/*
  Solve Dōbutsu shōgi.
  GPL2
  (c) Kai Tomerius, 2017
 */

#include <iostream>
#include <iomanip>
#include <stdlib.h>
#include <string.h>
#include <sys/time.h>

// board dimensions
#define H 4
#define W 3
#define N (H*W)

// pieces that can be on hand
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

typedef unsigned char uint8;
typedef unsigned int uint32;
typedef unsigned long long uint64;

class Board {
private:
    // lookup tables
    static uint8 lionPositions[2*L];
    static uint8 lionGrid[N][N];
    static uint8 animal[4];

    // pieces on the board and on hand
    uint8 grid[N+D];
    int sente;
    int illegal;

    // iterate over a grid to find all pieces
    class PieceIterator {
    private:
        uint8* grid;
        uint32 i;

    public:
        PieceIterator(uint8* grid, uint32 i)
            : grid(grid), i(i) {
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
            while (++i<N+D && grid[i]==' ') ;
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
        MoveIterator(const PieceIterator& p)
            : grid(&p), n(p()), i(p()<4 ? 4-p() : 0) {
        }

        operator void*() {
            return
                n<N ? i<10 && n-5+i<N ? this : NULL :
                i<N ? this : NULL;
        }

        int operator==(uint32 l) {
            return n-5+i==l;
        }

        MoveIterator& operator++() {
            if (n<N) {
                ++i;
                switch (grid[n]) {
                case 'l':
                case 'L':
                    if (n%3==0 && i%3==1) ++i;
                    if (i==5) ++i;
                    if (n%3==2 && i%3==0) ++i;
                    break;
                }

                return *this;
            } else {
                while (++i<N && grid[i]!=' ') ;
            }
        }
    };

public:
    // initialize lookup tables
    static void initialize() {
        memset(lionGrid, ~0, sizeof(lionGrid));
        for (int i=0; i<L; i++) {
            lionGrid[lionPositions[2*i]][lionPositions[2*i+1]] = i;
        }
    }

private:
    // determine the order of pieces on hand
    static int reorder(uint8 p, uint8 q) {
        return p!=q && (p==' ' || (q!=' ' && (p&0x1f)<(q&0x1f)));
    }

    // find a piece on the board
    int find(uint8 p) {
        for (int i=0; i<N; i++) {
            if (grid[i]==p) {
                return i;
            }
        }

        return N;
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
    Board(uint64 h) : illegal(h>=S) {
        memset(grid, ' ', sizeof(grid));
        if (illegal) {
            return;
        }

        // decode the position of both lions
        grid[lionPositions[2*(h>>29)]] = 'L';
        grid[lionPositions[2*(h>>29)+1]] = 'l';

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
                        std::cout << "swap" << std::endl;
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
                std::cout << grid[i];
            }
            std::cout << std::endl;
        }
    }
};

// lookup tables
uint8 Board::lionPositions[2*L] = { 0, 5, 0, 6, 0, 7, 0, 8, 0, 9, 0, 10, 0, 11, 1, 6, 1, 7, 1, 8, 1, 9, 1, 10, 1, 11, 2, 3, 2, 6, 2, 7, 2, 8, 2, 9, 2, 10, 2, 11, 3, 5, 3, 8, 3, 9, 3, 10, 3, 11, 4, 9, 4, 10, 4, 11, 5, 3, 5, 6, 5, 9, 5, 10, 5, 11, 6, 5, 6, 8, 6, 11, 8, 3, 8, 6, 8, 9 };

uint8 Board::lionGrid[N][N];

uint8 Board::animal[4] = { ' ', 'C', 'E', 'G' }; // promote C->D

int main(int argc, const char** argv) {
    // command line options
    int check = 0;
    int print = argc==1;
    uint64 start = 0;
    uint64 stop = S;
    for (int i=1; i<argc; i++) {
        if (!strcmp(argv[i], "-c")) {
            check = 1;
        } else if (!strcmp(argv[i], "-p")) {
            print = 1;
        } else if (!strcmp(argv[i], "-s") && i+1<argc) {
            start = strtoll(argv[++i], NULL, 0) & ~1ULL;
        } else if (!strcmp(argv[i], "-t") && i+1<argc) {
            stop = strtoll(argv[++i], NULL, 0);
        } else {
            std::cout << "usage: " << argv[0] << "[-c] [-p] [-s <start>] [-t <stop>]" << std::endl
                      << "defaults: start=0, stop=" << std::hex << S << std::dec << std::endl;
            return 0;
        }
    }

    uint64 n = 0;
    Board::initialize();

    struct timeval t0;
    gettimeofday(&t0, NULL);

    // iterate over all possible hash values for sente (+=2)
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
                if (b()!=h) {
                    std::cout << std::hex << "0x" << h << "/" << "0x" << b() << std::dec << std::endl;

                    break;
                }
            }
        }
    }

    // 336760432 positions
    std::cout << n << " positions (" << 100.0*n/((stop-start)/2) << "%)" << std::endl;

    struct timeval t;
    gettimeofday(&t, NULL);
    std::cout << t.tv_sec - t0.tv_sec << "s" << std::endl;

    return 0;
}
