/*
  Solve Dōbutsu shōgi.
  GPL2
  (c) Kai Tomerius, 2017
 */

#include <fcntl.h>
#include <iostream>
#include <iomanip>
#include <stdlib.h>
#include <string.h>
#include <sys/mman.h>
#include <sys/stat.h>
#include <sys/time.h>
#include <sys/types.h>
#include <unistd.h>

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

#define min(a, b) ((a)<(b)? (a) : (b))

// bitmasks for hashtable scan
#define ILLEGAL  0x00
#define LEGAL    0x01
#define EOHT     0xff

typedef unsigned char uint8;
typedef unsigned int uint32;
typedef unsigned long long uint64;

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
    int win;
    int loss;

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
            while (++i<N+D && (grid[i]==' ' || (grid[i] & ('l'-'L')))) ;
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

        MoveIterator& reset(const PieceIterator& p) {
            grid = &p;
            n = p();
            i = p()<N ? p()<4 ? 4-p()-1 : ~0 : ~0;
            return *this;
        }

        MoveIterator(const PieceIterator& p) {
            reset(p);
        }

        operator void*() {
            return
                n<N ? i<9 && n-4+i<N ? this : NULL :
                i<N ? this : NULL;
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
                     (grid[n-4+i]!=' ' &&
                      !((grid[n]^grid[n-4+i]) & ('l'-'L'))) ||
                     ((grid[n] & 0x0f)==('C' & 0x0f) && i!=7) ||
                     ((grid[n] & 0x0f)==('D' & 0x0f) && (i==0 || i==2)) ||
                     ((grid[n] & 0x0f)==('E' & 0x0f) && (i&1)) ||
                     ((grid[n] & 0x0f)==('G' & 0x0f) && !(i&1)))) ||
                   (n>=N && ++i<N && grid[i]!=' ')) ;

            return *this;
        }
    };

public:
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
            board = new Board(grid, sente, move);
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
        return p!=q && (p==' ' || (q!=' ' && (p&0x1f)<(q&0x1f)));
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
                if (grid[i]!=' ') {
                    grid[i] ^= 'l'-'L';
                }
            }
        }
    }

public:
    Board(const char* s="ELG C  c gle      ", int sente=1)
        : sente(sente), illegal(0), deeper(0), win(0), loss(0) {
        memset(grid, ' ', sizeof(grid));
        memcpy(grid, s, min(sizeof(grid), strlen(s)));
    }

    Board(uint8* g, int s, const MoveIterator& move) : sente(0), illegal(0), deeper(0), win(0), loss(0) {
        memcpy(grid, g, sizeof(grid));

        if (grid[move.to()]!=' ') {
            if (grid[move.to()]=='l') {
                win++;
            }

            grid[find(' ', N, N+D)] = grid[move.to()]^('l'-'L');
        }

        grid[move.to()] = grid[move.from()];
        grid[move.from()] = ' ';

        if (move.to()>=N-W) {
            if (grid[move.to()]=='C') {
                // promote chick
                grid[move.to()]++;
            }

            if (grid[move.to()]=='L') {
                // lion on final rank
                deeper++;
            }
        }

        flip();
        sente = !s;
        if (win) {
            win = 0;
            loss++;
        } else if (loss) {
            win++;
            loss = 0;
        }

        for (int i=N-W; i<N; i++) {
            if (grid[i]=='L') {
                win++;
                break;
            }
        }
    }

    Board(uint64 h)
        : sente(0), illegal(h>=S), deeper(0), win(0), loss(0) {
        if (illegal) {
            return;
        }

        memset(grid, ' ', sizeof(grid));

        // decode the position of both lions
        grid[lionPosition[2*(h>>29)]] = 'L';
        grid[lionPosition[2*(h>>29)+1]] = 'l';

        // board orientation
        sente = h & 0x01 ? 0 : 1;
        h >>= 1;

        // decode the pieces on the remaining 10 fields
        uint32 count[4] = { 0 };
        for (int i=0; i<N && h; i++) {
            if (grid[i]==' ') {
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
            if (grid[i]!=' ' && grid[i]!='L' && grid[i]!='l') {
                if (h & 0x01) {
                    grid[i] |= 'l'-'L';
                }

                h >>= 1;
            }
        }

        // promote chicks
        for (int i=0; i<N+D; i++) {
            if (grid[i]=='C' || grid[i]=='c') {
                if (h & 0x01) {
                    if (i<N) {
                        grid[i]++;
                    } else {
                        // chicks to drop can't be promoted
                        illegal++;
                        return;
                    }
                } else if ((grid[i]=='C' && i<W) ||
                           (grid[i]=='c' && i>=N-W)) {
                    // chicks on the last line must be promoted
                    illegal++;
                    return;
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

            int l = find('L');
            int n = find('l');

            if (l>=N || n>=N || lionGrid[l][n]>L) {
                flip();
                return ~0;
            }

            h = lionGrid[l][n];

            // promote chicks
            for (int i=N+D; i--;) {
                if (grid[i]=='C' || grid[i]=='c' ||
                    grid[i]=='D' || grid[i]=='d') {
                    h <<= 1;
                    if (grid[i]=='D' || grid[i]=='d') {
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
                if (grid[i]!=' ' && grid[i]!='L' && grid[i]!='l') {
                    h <<= 1;
                    if (grid[i] & ('l'-'L')) {
                        h |= 0x01;
                    }
                }
            }

            // encode the pieces on the remaining 10 fields
            for (int i=N; i--;) {
                if (grid[i]!='L' && grid[i]!='l') {
                    h <<=2;
                    if (grid[i]!=' ') {
                        h |= ((grid[i] & ~('l'-'L'))-'C')/2+1;
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
    void print() {
        if (!illegal) {
            for (int y=H; y--;) {
                std::cout << "|";
                for (int x=0; x<W; x++) {
                    std::cout << grid[y*W+x];
                }
                std::cout << "|" << std::endl;
            }

            for (int i=N; i<N+D; i++) {
                if (grid[i]!=' ') {
                    std::cout << grid[i];
                }
            }

            std::cout << (win ? " won" : loss ? " lost" : "") << std::endl;
        }
    }

    // generate moves
    PositionIterator& children() {
        return *new PositionIterator(grid, sente);
    }

    // recursively search to a given depth
    Board& search(int depth) {
        if (!win && !loss && depth+deeper>0) {
            Board& b = *this;
            std::cout << std::hex << "0x" << b() << std::dec << std::endl;
            b.print();

            for (Board::PositionIterator& child=b.children(); ++child;) {
                std::cout << "move" << child.getMove().from() << "->" << child.getMove().to() << std::endl;
                child().search(depth+deeper-1);
            }
        } else {
            print();
        }
    }
};

// lookup tables
uint8 Board::lionPosition[2*L] = { 0, 5, 0, 6, 0, 7, 0, 8, 0, 9, 0, 10, 0, 11, 1, 6, 1, 7, 1, 8, 1, 9, 1, 10, 1, 11, 2, 3, 2, 6, 2, 7, 2, 8, 2, 9, 2, 10, 2, 11, 3, 5, 3, 8, 3, 9, 3, 10, 3, 11, 4, 9, 4, 10, 4, 11, 5, 3, 5, 6, 5, 9, 5, 10, 5, 11, 6, 5, 6, 8, 6, 11, 8, 3, 8, 6, 8, 9 };

uint8 Board::lionGrid[N][N];

uint8 Board::animal[4] = { ' ', 'C', 'E', 'G' }; // promote C->D

// hashtable on disk
class Hashtable {
private:
    int fd;
    uint8* map;
    static Hashtable* instance;

public:
    static Hashtable& get() {
        return *instance;
    }

    Hashtable(uint64 size, const char* hashtablename=NULL)
        : fd(-1), map(NULL) {
        if (hashtablename &&
            (fd = open(hashtablename, O_CREAT | O_LARGEFILE | O_RDWR, 0664)>0 &&
             lseek(fd, size, SEEK_SET)==size)) {
            write(fd, "\377", 1);
            map = (uint8*) mmap(NULL, size, PROT_READ|PROT_WRITE, MAP_PRIVATE | MAP_NORESERVE, fd, 0);
        } else {
            map = (uint8*) malloc(size);
        }

        instance = this;
    }

    ~Hashtable() {
        instance = NULL;

        if (fd>0) {
            if (map) {
                munmap(map, S);
            }

            close(fd);
        } else {
            if (map) {
                free(map);
            }
        }
    }

    uint8& operator[](uint64 n) {
        return map[n];
    }
};

Hashtable* Hashtable::instance = NULL;

int main(int argc, const char** argv) {
    // command line options
    int check = 0;
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
        } else if (!strcmp(argv[i], "-g")) {
            gote = 1;
        } else if (!strcmp(argv[i], "-h") && i+1<argc) {
            hashtablename = argv[++i];
        } else if (!strcmp(argv[i], "-n")) {
            count = 1;
        } else if (!strcmp(argv[i], "-p")) {
            print = 1;
        } else if (!strcmp(argv[i], "-s") && i+1<argc) {
            start = strtoll(argv[++i], NULL, 0) & ~1ULL;
        } else if (!strcmp(argv[i], "-t") && i+1<argc) {
            stop = strtoll(argv[++i], NULL, 0);
        } else {
            std::cout << "usage: " << argv[0] << " [-c] [-h hashtable] [-n] [-p] [-s <start>] [-t <stop>]" << std::endl
                      << "usage: " << argv[0] << " [-b <board>] [-d <depth>] [-g] [-h hashtable]" << std::endl
                      << "defaults: start=0, stop=" << std::hex << S << std::dec << std::endl;
            return 0;
        }
    }

    Hashtable hashtable(S, hashtablename);
    Board::initialize();

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

        // 336760432 positions
        std::cout << n << " positions (" << 100.0*n/((stop-start)/2) << "%)" << std::endl;
    }

    if (depth) {
        // search to the given depth
        Board b(pos, !gote);
        b.search(depth);
    }

    if (count) {
        // count positions
        uint64 n = 0;
        for (uint64 h=start; h<stop; h+=2) {
            if ((h & ((1<<21)-1))==0) {
                // print progress every 1M moves
                std::cout << std::setprecision(3) << 100.0*h/(stop-start) << "%\r" << std::flush;
            }

            if (hashtable[h] & LEGAL) {
                n++;
            }
        }

        std::cout << n << " positions (" << 100.0*n/((stop-start)/2) << "%)" << std::endl;
    }

    struct timeval t;
    gettimeofday(&t, NULL);
    std::cout << t.tv_sec - t0.tv_sec << "s" << std::endl;

    return 0;
}
