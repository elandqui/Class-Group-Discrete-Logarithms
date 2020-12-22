#include <NTL/ZZ.h>
#include <NTL/RR.h>
#include "time.h"
#include <NTL/tools.h>
#include <NTL/vec_ZZ.h>
#include <NTL/vec_ZZ_p.h>
#include <NTL/ZZX.h>
#include <NTL/ZZ_p.h>
#include <NTL/ZZ_pX.h>


#define FMAX 30          // The maximum number of factors we will use in factoring ideals.

#define BLOCK 131072     // The maximum block size for the sieving interval.

#define MAX_FB 65536     // The maximum size of the factor base. 
                         // This limits the size of the factor base to 512K.

#define MAX_SI 131072    // The maximum size of the sieving interval. This limits its size to 128K.

#define MAX_HT 65521     // Maximum size for the hash table

#define TOLERR 2         // An error in the tolerance.

#define LPFAC 256          // We will consider all large primes less than LPFC*PMAX.

//#define SKIP 10          // The number of small primes we skip in sieving.


struct Node {                   // A node for the hashtable.
  int factorization[FMAX][2];
  int prime;
};

typedef struct Node node;

ZZ D;                     // The almighty discriminant
ZZ N;                     // The all-powerful group order.

ZZ g1=to_ZZ(0);           // The values that we create the example with: 
ZZ g2=to_ZZ(0);           // Find x s.t. (g1, g2)^x = (h1, h2)
ZZ h1, h2;          

double begintime;         // To keep track of time.

char error;               // Expected bit contribution of small primes.

short S;                  // The actual size of the factor base.
int F[MAX_FB][2];         // The factor base.
short FT[MAX_FB];          // A test array that will count the number of times each prime is used.
unsigned char Fbits[MAX_FB]; // The number of bits for each prime.
int SKIP;               // The number of small primes we skip in sieving.

int rootD[MAX_FB];        // This will hold sqrt(D)%P for every P in F.
int ainv[MAX_FB];         // This will hold (2a)^(-1) mod P for every P in F.

int R[MAX_FB][2];         // This matrix will hold roots of the polynomials mod the primes in FB.

node* HT[MAX_HT];         // A hash table containing factorizations for almost smooth ideals.
int entries = 0;          // The number of entries in the hash table.


int K=0;                  // Number of relations found.
int KINT=500;             // Will tell us when we have another KINT relations.
char ER=20;               // Extra relations.

int M;                    // The size of the sieving interval cn be 2M+1. We may break it into chunks.
unsigned char SI[MAX_SI]; // The size of the sieving interval.

int TOL;                  // The tolerance, or threshold, in the SI to test for smoothness.

/* The following are variables used for polynomial generation.  */

int Q;                    // Location in FB of smallest prime used to form f. 
char t=4;                 // will have 2^(t-1) sieving polynomials
char t2=30;               // number of primes to choose from for the coefficient a.
int mark = 7;             // This mark will tell us which primes to put together for  the polynomial.

ZZX SP;                    // THE sieving polynomial.

int TDIV=0;  //The number of elements we trial divided.
int LPU=0;   // The number of large primes used. The number found is LPU+entries.

int reduce(ZZ& a, ZZ& b);
void multiply(ZZ a1, ZZ b1, ZZ a2, ZZ b2, ZZ& a3, ZZ& b3);
void square(ZZ a1, ZZ b1, ZZ& a3, ZZ& b3);
void power(ZZ a1, ZZ b1, ZZ n, ZZ& c1, ZZ& c2);
int create_example(ZZ p);
void create_factorbase();
void rels_siqs(int x_coord[], int y_coord[], char exponent[]);
void precomputation();
void new_polynomial(ZZ& a1, ZZ& a2, int e[], ZZ bin, int& j);
void sieve ();
void getSmooth(int x_coord[], int y_coord[], char exponent[], int e[]);
void combine(int f [][2], int e[]);
void get_rel(int x_coord[], int y_coord[], char exponent[], int factorization[][2]);
int trialdivide(ZZ w1, ZZ w2, int factorization[][2]);
int insert(int factorization[][2]);
vec_ZZ_p Matrix_Vector(int x_c[], int y_c[], char value[], vec_ZZ_p b);
vec_ZZ_p MatrixTrans_Vector(int x_c[], int y_c[], char value[], vec_ZZ_p b);
vec_ZZ_p Lanczos_Random(int x_c[], int y_c[], char value[]);
vec_ZZ_p Lanczos_Inner(int x_c[], int y_c[], char value[], vec_ZZ_p b);
