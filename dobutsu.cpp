/*
  Solve Dōbutsu shōgi.
  GPL2
  (c) Kai Tomerius, 2017
 */

#include <fcntl.h>
#include <iostream>
#include <iomanip>
#include <signal.h>
#include <stdlib.h>
#include <string.h>
#include <sys/mman.h>
#include <sys/stat.h>
#include <sys/time.h>
#include <sys/types.h>
#include <unistd.h>

static int verbose = 0;

// helper macro
#define min(a, b) ((a)<(b)? (a) : (b))

// board dimensions
#define H 4
#define W 3
#define N (H*W)

// number of pieces that can be on hand
#define D 6

// number of legal, non-final positions for non-adjacent lions
#define L 39

// upper bound for the number of positions <2^35
// 1 bit for sente/gote
// 10*2 bits for 10 squares empty/chick/elephant/giraffe
// 6 bits for assigning chicks/elefants/giraffes to sente/gote
// 2 bits to promote chicks
// <6 bits for 39 legal, non-final positions for non-adjacent lions
#define S (L*(1ULL<<(2+D+2*(N-2)+1)))

// bitmasks for pieces
#define EMPTY                 ' '
#define CHICK                 ANIMAL('C')
#define HEN                   ANIMAL('D')
#define ELEPHANT              ANIMAL('E')
#define GIRAFFE               ANIMAL('G')
#define LION                  ANIMAL('L')
#define GOTE                  ('l'-'L')
#define ANIMAL(piece)         ((piece) & 0x0f)
#define PROMOTE(piece)        (++(piece))
#define SENTE(piece)          (!((piece) & GOTE))
#define FLIP(piece)           ((piece) ^= GOTE)
#define PIECE_SENTE(animal)   ('A'-1+(animal))
#define PIECE_GOTE(animal)    (PIECE_SENTE(animal) | GOTE)

// bitmasks for hashtable
#define ILLEGAL  0x00
#define LEGAL    0x01
#define WIN      0x02
#define LOSS     0x04
#define EOHT     0xff

typedef unsigned char uint8;
typedef unsigned int uint32;
typedef unsigned long long uint64;

// hashtable in memory or on disk
class Hashtable {
private:
    static Hashtable* instance;
    static uint64 won;
    static uint64 lost;
    static uint64 queried;
    static uint64 matched;

    uint64 size;
    int fd;
    uint8* map;

    void flush() {
        if (fd>0) {
            if (map) {
                munmap(map, S);
            }

            close(fd);
            sync();
        } else {
            if (map) {
                free(map);
            }
        }

        map = NULL;
    }

public:
    static uint8 enter(uint64 h, int depth, int result) {
        uint8 m = result>0 ? (won++, WIN) : result<0 ? (lost++, LOSS) : 0;

        return instance && instance->map && instance->size>h ?
            (*instance)[h] |= ((depth/2)<<3) | m : m;
    }

    static int query(uint64 h, int depth, int* result) {
        queried++;
        if (instance && instance->map && instance->size>h) {
            if ((*instance)[h] & (WIN | LOSS)) {
                *result = (*instance)[h] & WIN ? 1 : -1;
            } else if (((*instance)[h]>>3)*2>=depth) {
                *result = 0;
            } else {
                if (((*instance)[h]>>3)<depth/2) {
                    (*instance)[h] &= 0x07;
                    (*instance)[h] |= ((depth/2)<<3);
                }

                return 0;
            }

            if (++matched%1000==0) {
                std::cout << queried << " queries, " <<  matched << " matches\r" << std::flush;
            }

            return 1;
        }

        return 0;
    }

    static uint64 wins() {
        return won;
    }

    static uint64 losses() {
        return lost;
    }

    static uint64 queries() {
        return queried;
    }

    static uint64 matches() {
        return matched;
    }

    static void unmap() {
        if (instance) {
            instance->flush();
        }
    }

    Hashtable(uint64 size, const char* hashtablename=NULL)
        : size(size), fd(-1), map(NULL) {
        if (hashtablename &&
            (fd = open(hashtablename, O_CREAT | O_LARGEFILE | O_RDWR, 0664))>0 &&
             lseek(fd, size, SEEK_SET)==size) {
            write(fd, "\377", 1);
            map = (uint8*) mmap(NULL, size, PROT_READ | PROT_WRITE, MAP_SHARED | MAP_NORESERVE, fd, 0);
        } else {
            map = (uint8*) malloc(size);
        }

        instance = this;
    }

    ~Hashtable() {
        instance = NULL;
        flush();
    }

    operator void*() {
        return map;
    }

    uint8& operator[](uint64 n) {
        return map[n];
    }
};

Hashtable* Hashtable::instance = NULL;
uint64 Hashtable::won = 0;
uint64 Hashtable::lost = 0;
uint64 Hashtable::queried = 0;
uint64 Hashtable::matched = 0;

class Board {
private:
    // lookup tables
    static uint8 lionPosition[2*L];
    static uint8 lionGrid[N][N];
    static uint8 animal[4];

    // pieces on the board and on hand
    uint8 grid[N+D];
    int sente;
    int illegal;
    int deeper;
    int result;

    // iterate over a grid to find all pieces
    class PieceIterator {
    private:
        uint8* grid;
        uint32 i;

    public:
        PieceIterator(uint8* grid)
            : grid(grid), i(~0) {
        }

        operator void*() const {
            return i<N+D ? (void*) this : NULL;
        }

        uint32 operator()() const {
            return i;
        }

        uint8* operator&() const {
            return grid;
        }

        PieceIterator& operator++() {
            while (++i<N+D && (!ANIMAL(grid[i]) || !SENTE(grid[i]) || (i>N && ANIMAL(grid[i])==ANIMAL(grid[i-1])))) ;
            return *this;
        }
    };

    // iterate around a piece to find all possible moves
    class MoveIterator {
    private:
        uint8* grid;
        uint32 n;
        uint32 i;

    public:
        MoveIterator()
            : grid(NULL), n(N), i(N) {
        }

        MoveIterator& operator=(const MoveIterator& m) {
            grid = m.grid;
            n = m.n;
            i = m.i;
            return *this;
        }

        MoveIterator& reset(const PieceIterator& p) {
            grid = &p;
            n = p();
            i = p()<N ? p()<4 ? 4-p()-1 : ~0 : ~0;
            return *this;
        }

        MoveIterator(const PieceIterator& p) {
            reset(p);
        }

        operator void*() const {
            return
                n<N ? i<9 && n-4+i<N ? (void*) this : NULL :
                i<N ? (void*) this : NULL;
        }

        int operator==(uint32 l) {
            return n<N ? n-4+i==l : i==l;
        }

        uint32 from() const {
            return n;
        }

        uint32 to() const {
            return n<N ? n-4+i : i;
        }

        MoveIterator& operator++() {
            while ((n<N && ++i<9 &&
                    (i==4 ||
                     (n%3==0 && i%3==0) ||
                     (n%3==2 && i%3==2) ||
                     (ANIMAL(grid[n-4+i]) &&
                      !((grid[n]^grid[n-4+i]) & GOTE)) ||
                     (ANIMAL(grid[n])==CHICK    && i!=7) ||
                     (ANIMAL(grid[n])==HEN      && (i==0 || i==2)) ||
                     (ANIMAL(grid[n])==ELEPHANT && (i&1)) ||
                     (ANIMAL(grid[n])==GIRAFFE  && !(i&1)))) ||
                   (n>=N && ++i<N && ANIMAL(grid[i]))) ;

            return *this;
        }
    };

public:
    // iterate over all pieces and moves
    class PositionIterator {
    private:
        uint8* grid;
        int sente;
        PieceIterator piece;
        MoveIterator move;
        Board* board;

    public:
        PositionIterator(uint8* grid, int sente)
            : grid(grid), sente(sente), piece(grid), board(NULL) {
        }

        ~PositionIterator() {
            if (board) {
                delete board;
            }
        }

        operator void*() {
            if (!move) {
                delete this;
                return NULL;
            }

            return this;
        }

        PositionIterator& operator++() {
            if (board) {
                delete board;
                board = NULL;
            }

            while (!++move && ++piece) {
                move.reset(piece);
            }

            return *this;
        }

        Board& operator()() {
            if (!board) {
                board = new Board(grid, sente, move);
            }

            return *board;
        }

        const PieceIterator& getPiece() const {
            return piece;
        }

        const MoveIterator& getMove() const {
            return move;
        }
};

public:
    // initialize lookup tables
    static void initialize() {
        memset(lionGrid, ~0, sizeof(lionGrid));
        for (int i=0; i<L; i++) {
            lionGrid[lionPosition[2*i]][lionPosition[2*i+1]] = i;
        }
    }

private:
    // determine the order of pieces on hand
    static int reorder(uint8 p, uint8 q) {
        return !ANIMAL(p) || (ANIMAL(q) && ANIMAL(p)<ANIMAL(q));
    }

    // find a piece on the board
    int find(uint8 p, int start=0, int end=N) {
        for (int i=start; i<end; i++) {
            if (grid[i]==p) {
                return i;
            }
        }

        return end;
    }

    // flip the board for gote
    void flip() {
        if (!sente) {
            uint8 g[N];
            for (int i=0; i<N; i++) {
                g[i] = grid[N-1-i];
            }

            memcpy(grid, g, N);

            for (int i=0; i<N+D; i++) {
                if (ANIMAL(grid[i])) {
                    FLIP(grid[i]);
                }
            }
        }
    }

public:
    Board(const char* s="ELG C  c gle      ", int sente=1)
        : sente(sente), illegal(0), deeper(0), result(0) {
        memset(grid, EMPTY, sizeof(grid));
        memcpy(grid, s, min(sizeof(grid), strlen(s)));
    }

    Board(uint8* g, int s, const MoveIterator& move) : sente(0), illegal(0), deeper(0), result(0) {
        memcpy(grid, g, sizeof(grid));

        if (ANIMAL(grid[move.to()])) {
            if (ANIMAL(grid[move.to()])==LION) {
                // losing the lions loses the game
                result = -__LINE__;
            }

            grid[find(EMPTY, N, N+D)] = FLIP(grid[move.to()]);
        }

        grid[move.to()] = grid[move.from()];
        grid[move.from()] = EMPTY;

        if (move.to()>=N-W) {
            if (ANIMAL(grid[move.to()])==CHICK) {
                // promote chick
                PROMOTE(grid[move.to()]);
            }

            if (ANIMAL(grid[move.to()])==LION) {
                // lion on final rank
                deeper += 2;
            }
        }

        flip();
        sente = !s;

        for (int i=N-W; i<N; i++) {
            if (SENTE(grid[i]) && ANIMAL(grid[i])==LION) {
                // a lion surving on final rank wins
                result = __LINE__;
                break;
            }
        }
    }

    Board(uint64 h)
        : sente(0), illegal(h>=S), deeper(0), result(0) {
        if (illegal) {
            return;
        }

        memset(grid, EMPTY, sizeof(grid));

        // decode the position of both lions
        grid[lionPosition[2*(h>>29)]] = PIECE_SENTE(LION);
        grid[lionPosition[2*(h>>29)+1]] = PIECE_GOTE(LION);

        // board orientation
        sente = h & 0x01 ? 0 : 1;
        h >>= 1;

        // decode the pieces on the remaining 10 fields
        uint32 count[4] = { 0 };
        for (int i=0; i<N && h; i++) {
            if (!ANIMAL(grid[i])) {
                if (h & 0x03) {
                    grid[i] = animal[h & 0x03];
                    if (++count[h & 0x03]>2) {
                        illegal++;
                        return;
                    }
                }

                h >>= 2;
            }
        }

        // add the remaining pieces to be dropped
        int a = 3;
        for (int i=N; i<N+D; i++) {
            while (a && count[a]>=2) {
                a--;
            }

            grid[i] = animal[a];
            count[a]++;
        }

        // assign pieces to sente/gote
        for (int i=0; i<N+D; i++) {
            if (ANIMAL(grid[i]) && ANIMAL(grid[i])!=LION) {
                if (h & 0x01) {
                    grid[i] |= GOTE;
                }

                h >>= 1;
            }
        }

        // promote chicks
        for (int i=0; i<N+D; i++) {
            if (ANIMAL(grid[i])==CHICK) {
                if (h & 0x01) {
                    if (i<N) {
                        PROMOTE(grid[i]);
                    } else {
                        // chicks to drop can't be promoted
                        illegal++;
                        return;
                    }
                }

                h >>= 1;
            }
        }

        flip();
    }

    // check if the board position is legal
    operator void*() {
        return illegal ? NULL : this;
    }

    // calculate a hashvalue for the board
    uint64 operator()() {
        if (!illegal) {
            uint64 h = 0;
            flip();

            int l = find(PIECE_SENTE(LION));
            int n = find(PIECE_GOTE(LION));

            if (l>=N || n>=N || lionGrid[l][n]>L) {
                flip();
                return ~0;
            }

            h = lionGrid[l][n];

            // promote chicks
            for (int i=N+D; i--;) {
                if (ANIMAL(grid[i])==CHICK || ANIMAL(grid[i])==HEN) {
                    h <<= 1;
                    if (ANIMAL(grid[i])==HEN) {
                        h |= 0x01;
                    }
                }
            }

            // sort pieces on hand
            for (int i=N; i<N+D-1; i++) {
                for (int j=i+1; j<N+D; j++) {
                    if (reorder(grid[i], grid[j])) {
                        uint8 swap = grid[i];
                        grid[i] = grid[j];
                        grid[j] = swap;
                    }
                }
            }

            // assign pieces to sente/gote
            for (int i=N+D; i--;) {
                if (ANIMAL(grid[i]) && ANIMAL(grid[i])!=LION) {
                    h <<= 1;
                    if (grid[i] & GOTE) {
                        h |= 0x01;
                    }
                }
            }

            // encode the pieces on the remaining 10 fields
            for (int i=N; i--;) {
                if (ANIMAL(grid[i])!=LION) {
                    h <<=2;
                    if (ANIMAL(grid[i])) {
                        h |= (ANIMAL(grid[i])-CHICK)/2+1;
                    }
                }
            }

            // board orientation
            h <<= 1;
            if (!sente) {
                h |= 1;
            }

            flip();
            return h;
        }

        return ~0;
    }

    // print the position
    void print(const MoveIterator& move = MoveIterator()) {
        if (!illegal) {
            std::cout << (sente ? " 321" : " 123") << std::endl;
            for (int y=H; y--;) {
                std::cout << "|";
                for (int x=0; x<W; x++) {
                    std::cout << grid[y*W+x];
                }
                std::cout << "|" << (sente ? H-y : y+1) << std::endl;
            }

            int a = 0;
            for (int i=N; i<N+D; i++) {
                if (ANIMAL(grid[i])) {
                    std::cout << grid[i];
                    a++;
                }
            }

            if (a) {
                std::cout << std::endl;
            }

            if (move) {
                if (sente) {
                    std::cout << W-(N-1-move.from())%W << (N-1-move.from())/W+1 << "->" << W-(N-1-move.to())%W << (N-1-move.to())/W+1 << " wins" << std::endl << std::endl;
                } else {
                    std::cout << move.from()%W+1 << move.from()/W+1 << "->" << move.to()%W+1 << move.to()/W+1 << " wins" << std::endl << std::endl;
                }
            }

            if (result) {
                std::cout << (result>0 ? " is won #" : " is lost #") << result << std::endl;
            }
        }
    }

    // generate moves
    PositionIterator& children() {
        return *new PositionIterator(grid, sente);
    }

    // recursively search to a given depth
    int search(int depth) {
        Board& b = *this;
        uint64 h = b();
        if (!result &&
            !Hashtable::query(h, depth+deeper, &result) &&
            depth+deeper>0) {
            result = -__LINE__;
            for (Board::PositionIterator& child=b.children(); result<=0 && ++child;) {
                int rc = -child().search(depth-1+deeper);
                if (rc>result) {
                    if (verbose && rc>0) {
                        b.print(child.getMove());
                    }

                    result = rc;
                }
            }

            Hashtable::enter(h, depth+deeper, result);
            if (verbose) {
                std::cout << std::hex << "0x" << b() << std::dec << std::endl;
                b.print();
                std::cout << std::endl;
            }
        }

        return result;
    }
};

// lookup tables
uint8 Board::lionPosition[2*L] = { 0, 5, 0, 6, 0, 7, 0, 8, 0, 9, 0, 10, 0, 11, 1, 6, 1, 7, 1, 8, 1, 9, 1, 10, 1, 11, 2, 3, 2, 6, 2, 7, 2, 8, 2, 9, 2, 10, 2, 11, 3, 5, 3, 8, 3, 9, 3, 10, 3, 11, 4, 9, 4, 10, 4, 11, 5, 3, 5, 6, 5, 9, 5, 10, 5, 11, 6, 5, 6, 8, 6, 11, 8, 3, 8, 6, 8, 9 };

uint8 Board::lionGrid[N][N];

uint8 Board::animal[4] = { EMPTY, PIECE_SENTE(CHICK), PIECE_SENTE(ELEPHANT), PIECE_SENTE(GIRAFFE) }; // promote C->D

static void intHandler(int) {
    std::cout << std::endl << "got ^C, exiting ..." << std::endl;
    Hashtable::unmap();

    exit(1);
}

int main(int argc, const char** argv) {
    // command line options
    int check = 0;
    int empty = 0;
    int count = 0;
    int depth = 0;
    int print = argc==1;
    uint64 start = 0;
    uint64 stop = S;
    const char* pos = "ELG C  c gle      ";
    int gote = 0;
    const char* hashtablename = NULL;
    for (int i=1; i<argc; i++) {
        if (!strcmp(argv[i], "-b") && i+1<argc) {
            pos = argv[++i];
        } else if (!strcmp(argv[i], "-c")) {
            check = 1;
        } else if (!strcmp(argv[i], "-d") && i+1<argc) {
            depth = strtoll(argv[++i], NULL, 0);
        } else if (!strcmp(argv[i], "-e")) {
            empty = 1;
        } else if (!strcmp(argv[i], "-f") && i+1<argc) {
            hashtablename = argv[++i];
        } else if (!strcmp(argv[i], "-g")) {
            gote = 1;
        } else if (!strcmp(argv[i], "-n")) {
            count = 1;
        } else if (!strcmp(argv[i], "-p")) {
            print = 1;
        } else if (!strcmp(argv[i], "-s") && i+1<argc) {
            start = strtoll(argv[++i], NULL, 0) & ~1ULL;
        } else if (!strcmp(argv[i], "-t") && i+1<argc) {
            stop = strtoll(argv[++i], NULL, 0);
        } else if (!strcmp(argv[i], "-v")) {
            verbose = 1;
        } else {
            std::cout << "usage: " << argv[0] << " [-c] [-e] [-f hashtable] [-n] [-p] [-s <start>] [-t <stop>] [-v]" << std::endl
                      << "usage: " << argv[0] << " [-b <board>] [-d <depth>] [-g] [-f hashtable] [-v]" << std::endl
                      << "-e: empty hash table loss/win information" << std::endl
                      << "-n: count legal positions in hashtable" << std::endl
                      << "-p: print legal positions" << std::endl
                      << "defaults: start=0, stop=" << std::hex << S << std::dec << std::endl;
            return 0;
        }
    }

    Board::initialize();
    Hashtable hashtable(S, hashtablename);
    signal(SIGINT, intHandler);

    if (!hashtable) {
        if (check || empty || count) {
            std::cout << "no hashtable" << std::endl;
        }

        check = 0;
        empty = 0;
        count = 0;
    }

    struct timeval t0;
    gettimeofday(&t0, NULL);

    if (check || print) {
        // iterate over all possible hash values for sente (+=2)
        uint64 n = 0;
        for (uint64 h=start; h<stop; h+=2) {
            if ((h & ((1<<21)-1))==0) {
                // print progress every 1M moves
                std::cout << std::setprecision(3) << 100.0*h/(stop-start) << "%\r" << std::flush;
            }

            if (print || check) {
                Board b(h);

                // count legal positions
                if (b) {
                    n++;

                    if (print) {
                        std::cout << std::hex << "0x" << h << std::dec << std::endl;
                        b.print();
                        std::cout << std::endl;
                    }

                    if (check) {
                        if (b()==h) {
                            hashtable[h] |= LEGAL;
                        } else {
                            std::cout << std::hex << "0x" << h << "/" << "0x" << b() << std::dec << std::endl;

                            break;
                        }
                    }
                }
            }
        }

        // 336760432 positions
        std::cout << n << " positions (" << 100.0*n/((stop-start)/2) << "%)" << std::endl;
    }

    if (depth) {
        // search to the given depth
        for (int d=0; d++<depth;) {
            Board b(pos, !gote);
            std::cout << "depth " << d << "\r" << std::flush;
            b.search(d);
            std::cout << Hashtable::wins() << " wins, " << Hashtable::losses() << " losses, " << Hashtable::queries() << " queries, " << Hashtable::matches() << " matches" << std::endl;
        }
    }

    if (count || empty) {
        // count positions
        uint64 n = 0;
        uint64 w = 0;
        uint64 l = 0;
        for (uint64 h=start; h<stop; h+=2) {
            if ((h & ((1<<21)-1))==0) {
                // print progress every 1M moves
                std::cout << std::setprecision(3) << 100.0*h/(stop-start) << "%\r" << std::flush;
            }

            if (hashtable[h] & LEGAL) {
                n++;

                if (hashtable[h] & WIN) {
                    w++;
                }

                if (hashtable[h] & LOSS) {
                    l++;
                }

                if (empty) {
                    if (hashtable[h] & ~LEGAL) {
                        hashtable[h] &= LEGAL;
                    }
                }
            }
        }

        std::cout << n << " positions (" << 100.0*n/((stop-start)/2) << "%), " << w << " wins, " << l << " losses" << std::endl;
    }

    struct timeval t;
    gettimeofday(&t, NULL);
    std::cout << t.tv_sec - t0.tv_sec << "s" << std::endl;

    return 0;
}
