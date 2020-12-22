#include <NTL/ZZ.h>
#include <NTL/RR.h>
#include <time.h>
#include <NTL/mat_ZZ.h>
#include <NTL/vec_ZZ.h>
#include <NTL/vec_ZZ_p.h>
//#include "BinarySearchTree.h"

// NTL documentation at http://shoup.net/NTL

struct node
{
  struct node *left;
  struct node *right;
  ZZ factors[10][2];
  ZZ as;
  ZZ bs;
  // The element that does the comparing is factors[factors[0][0]][0].
  // The element factors[0][1] will act as a flag.
};

typedef struct node Node;

int reduce(ZZ& a, ZZ& b, ZZ D);
void multiply(ZZ a1, ZZ b1, ZZ a2, ZZ b2, ZZ& a3, ZZ& b3, ZZ D);
void square(ZZ a1, ZZ b1, ZZ& a3, ZZ& b3, ZZ D);
void power(ZZ a1, ZZ b1, ZZ n, ZZ& c1, ZZ& c2, ZZ D);
int create_example(ZZ p, ZZ& g1, ZZ& g2, ZZ D);
long create_factorbase(ZZ D, long S, ZZ F[][2]);
void create_multipliers(ZZ g1, ZZ g2, ZZ h1, ZZ h2, ZZ N, ZZ M[][2], ZZ E[][2], ZZ D);
void step(ZZ w1, ZZ w2, ZZ M[][2], ZZ E[][2], ZZ& G1, ZZ& G2, ZZ& a, ZZ& b, ZZ D);
ZZ dlog(ZZ& a, ZZ p);
int smooth(ZZ w1, ZZ w2, ZZ F[][2], long size_of_factbase, ZZ factorization[], ZZ D);
void walk(ZZ g1, ZZ g2, ZZ h1, ZZ h2, ZZ M[][2], ZZ E[][2], ZZ F[][2], long size_of_factbase, ZZ N, ZZ D);
Node *insert(Node **root, ZZ factorization[][2], ZZ as, ZZ bs);
vec_ZZ_p Matrix_Vector(long x_c[], long y_c[], int value[], vec_ZZ_p b, long value);
vec_ZZ_p MatrixTrans_Vector(long x_c[], long y_c[], int value[], vec_ZZ_p b, long length);
vec_ZZ_p Lanczos_Random(long x_c[], long y_c[], int value[], long length, ZZ N);
vec_ZZ_p Lanczos_Inner(long x_c[], long y_c[], int value[], vec_ZZ_p b, long length);

// Convert an ideal (a, b) to its equivalent reduced form.
// Uses the algorithm described in Cohen.
int reduce(ZZ& a, ZZ& b, ZZ D) {
  ZZ c, t, q, r, a0, a1;
  c = (b*b - D)/(4*a);
  if ((-a < b) && (b <= a)) {
    if (a > c) {
      b = -b; t = a; a = c; c = t;
    } 
    else {
      if ((a == c) && (b < 0)) {
	b = -b;
      }
      return 1;
    }
  }

  do {
    q = b/(2*a); r = b % (2*a);
    if (r > a) {
      r = r-2*a; q++;
    }
    c = c - (b+r)*q/2; b = r;
    a0 = a; a1 = c;
    if (a > c) {
      b = -b; t = a; a = c; c = t;
    }
  } while (a0 > a1);
  if ((a == c) && (b < 0)) { b= -b; }
  return 1;
}

// Multiply two ideals (a1, b1) and (a2, b2) in reduced form. Result
// (a3, b3) is in reduced form
void multiply(ZZ a1, ZZ b1, ZZ a2, ZZ b2, ZZ& a3, ZZ& b3, ZZ D) {
  ZZ d1, v, w;
  XGCD(d1, v, w, a1, a2);
  b3 = v*a1*(b2-b1);
  a3 = a1*a2;
  if (d1 != 1) {
    ZZ d;
    XGCD(d, v, w, d1, (b1+b2)/2);
    b3 = (b3*v + w*(D-b1*b1)/2)/d;
    a3 = a3/(d*d);
  }
  b3 = (b3+b1) % (2*a3);
  reduce(a3, b3, D);
}

// Squares the reduced ideal (a1, b1). The result (a3, b3) is in reduced
// form.
void square(ZZ a1, ZZ b1, ZZ& a3, ZZ& b3, ZZ D) {
  ZZ d, v, w;
  XGCD(d, v, w, a1, b1);
  b3 = b1 + w*(D - (b1*b1))/(2*d);
  a3 = sqr(a1/d); b3 = b3 % (2*a3);
  reduce(a3, b3, D);
}

// Computes (a1, b1)^n and stores the result in (c1, c2). The input should
// be reduced, and the output is reduced.
void power(ZZ a1, ZZ b1, ZZ n, ZZ& c1, ZZ& c2, ZZ D) {
  ZZ B1, B2, d1, d2;
  B1 = a1; B2 = b1; c1 = 1; c2 = 1; // c = id.
  while (n > 0) {
    if ((n % 2) == 1) {
      multiply(c1, c2, B1, B2, d1, d2, D);
      c1 = d1; c2 = d2;
    }
    n = n/2;                     
    if (n > 0) {
      square(B1, B2, d1, d2, D);
      B1 = d1; B2 = d2;
	}
  }
}

// Given a prime p and a discriminant D, tries to compute a prime ideal above
// p. If it succeeds, it stores the reduced ideal in (g1, g2) and returns 1,
// else g1, g2 contains garbage and 0 is returned.
int create_example(ZZ p, ZZ& g1, ZZ& g2, ZZ D) {
  ZZ d = (D % p);  
  if (Jacobi(d, p) == 1) {
    ZZ temp =  SqrRootMod(d, p);
    temp = p-temp;
    g2 = MulMod((d - temp), InvMod(to_ZZ(2), p), p);
    g2 = (D - 2*g2);
    g1 = p;
    reduce(g1, g2, D);
    return 1;
  } else { return 0; }
}

// D - disc, 2^S = max size of the factor base.
long create_factorbase(ZZ D, long S, ZZ F[][2]) {
  ZZ p, b; ZZ P = to_ZZ(3); ZZ max_size = power2_ZZ(S); long cur_index = 0;
  ZZ d, t; char i;
  int mark;
  // Throwing in the prime 2. 
  if((D%8)==1){
    F[0][0] = to_ZZ(2); F[0][1] = to_ZZ(1);
    F[1][0] = to_ZZ(2); F[1][1] = to_ZZ(-1);
    cur_index += 2;
    }
  // We don't handle this case in our big example.
  //else{
  
  //}
  // Now we make the rest of the factor base
  while (P <= max_size) {
    P = NextPrime(P);
    // We expect D to be prime, so we can ignore the case of (p, D)!=1.
      p = P;
      d = D % p;
     
      if (Jacobi(d, p) == 1) {
	t = InvMod(to_ZZ(2), p);
	b =  ((d - SqrRootMod(d, p))*t) % p;
	b = (D - 2*b);
	reduce(p, b, D);
	(b>0)?mark=0:mark=1;
	F[cur_index+mark][0] = p; F[cur_index+mark][1] = b;
	F[cur_index+1-mark][0] = p; F[cur_index+1-mark][1] = -b;
	cur_index += 2;
    }
    P++;
  }
  // This extension will store the square of the largest prime in the factor base.
  // It will be used to speed up the algorithm like the large prime QS.
  F[cur_index][0]=power(F[cur_index-1][0], 2);
  cout<<"\n";
  return (cur_index); // size of factor base array.
}

// creates 16 random multipliers, stores the multipliers in M and the corresp-
// onding exponents in E.
void create_multipliers(ZZ g1, ZZ g2, ZZ h1, ZZ h2, ZZ N, ZZ M[][2], ZZ E[][2], ZZ D) {
  ZZ a, b, w1, w2, z1, z2; 
  int i;  

  for (i = 0; i <= 15; i++) {
    a = RandomBnd(N-1); b = RandomBnd(N-1);
    power(g1, g2, a, w1, w2, D);
    power(h1, h2, b, z1, z2, D);
    multiply(w1, w2, z1, z2, M[i][0], M[i][1], D);
    E[i][0] = a; E[i][1] = b;
  }
}

// Does one step in the walk.
void step(ZZ w1, ZZ w2, ZZ M[][2], ZZ E[][2], ZZ& G1, ZZ& G2, ZZ& a, ZZ& b, ZZ D) {
  long i; ZZ M1, M2;
  i=w1%16;
  M1 = M[i][0]; M2 = M[i][1];
  a = E[i][0]; b = E[i][1];
  multiply(w1, w2, M1, M2, G1, G2, D);
}

// returns largest i s.t. p^i | a.
// Note: a is modified here. 
// This routine is only used to factor an ideal, and so there is no need to
// mess with a in the factorization routine.
ZZ dlog(ZZ& a, ZZ p) {
  ZZ i = to_ZZ(0);
  while ((a % p) == 0) {
   a/=p;
   i++;
  }
  return i;
}

// If (w1, w2) is smooth then compute its factorization and return 1, else return 0.
// This assumes that D is prime, so there are no elements in the factor base
// of the form (p, 0)

int smooth(ZZ w1, ZZ w2, ZZ F[][2], long size_of_factbase, ZZ factorization[][2], ZZ D) {
  long i = 0; int s = 0; ZZ p, y_p, e, v1, v2; long cur_index = 0;
  ZZ pmax2 = power(F[size_of_factbase-1][0], 2);

  while ((i < size_of_factbase) && (w1 > 1)) {
    p = F[i][0]; y_p = F[i][1];
    if ((w1 % p) == 0) {
      e = dlog(w1, p);     // in dlog w1 is modified and divided by p^e.
      cur_index++;
      if ((w2 % (2*p)) == y_p) {
	factorization[cur_index][0] = i; 
	factorization[cur_index][1] = e;
      }
      else {
	factorization[cur_index][0] = i+1; 
	factorization[cur_index][1] = e;
      }
    }
      i += 2;
  }
  // Output 1 (true) if the ideal is smooth, and set the 1st elt. in factorization[][] to the number of primes.
  if (w1 == 1) { 
    s= 1; 
    factorization[0][0]=cur_index; 
  } 
  // Here we wish to capture almost S-smooth numbers, that is, given an ideal a, 
  // all but one of its factors is in the factor base, and the non-smooth factor
  // is in the interval (p, p^2), where p is the largest prime in the factor base.
  // If we can get two identical prime IDEALS out of a, we can potentially use them.
  if((w1<pmax2) && (w1>1)){
    s=2;
    cur_index++;
    
    // Instead of storing the index of the prime and the exponent in factorization, 
    // we instead store the large-prime ideal itself in the next spot, since the large-
    // prime ideal is not stored in the factor base and we know the ideal has exponent 1.
    // We also note that we need two identical ideals in order to use this, not just 
    // two identical primes.
    factorization[cur_index][0]=w1; factorization[cur_index][1]= (w2%(2*w1));
    // This is a quick way to differentiate between the two ideals.
    if(factorization[cur_index][1]>w1/2)
      factorization[cur_index][0]++;
    factorization[0][0]=cur_index;
  }

  return s;
}

// Do the walk, yeah, do the walk o' life, do the walk o' life.

// N = size of group.
void walk(ZZ g1, ZZ g2, ZZ h1, ZZ h2, ZZ M[][2], ZZ E[][2], ZZ F[][2], long size_of_factbase, ZZ N, ZZ D) {
  const int WALK_SIZE_INC = 5; int s;
  ZZ a, b; ZZ prev_a = to_ZZ(0); ZZ prev_b = to_ZZ(0); ZZ G1, G2, H1, H2, w1, w2, x=to_ZZ(0), x2=to_ZZ(0); // Yes, the x is THE x.
  long k;
  long j; 
  long temp, num;
  ZZ factorization[10][2]; //The 0th entry will be the number of distinct prime factors of this smooth element.
  
  ZZ *alpha = new ZZ[2*size_of_factbase]; 
  ZZ *beta = new ZZ[2*size_of_factbase];

  //These three arrays represent our compressed row storage for our sparse matrix. (About) As optimized as you can get, BABY!
  int exponent[14*size_of_factbase]; 
  long y_coord[14*size_of_factbase];
  long x_coord[2*size_of_factbase];
  x_coord[0]=0;
  
  vec_ZZ_p kernel; // This will some day store an element of the kernel that we long for.

  int bigprimes=0; // Count the number of big primes added to the matrix.
  //int count2=0; // Number of almost-smooth ideals.
  // This is the root of the binary search tree. 
  Node *root=NULL;
  // The below will be a return value if we get a duplicate 
  Node *find;

  a = RandomBnd(N-1); b = RandomBnd(N-1);
  power(g1, g2, a, G1, G2, D);
  power(h1, h2, b, H1, H2, D);
  
  multiply(G1, G2, H1, H2, w1, w2, D); // step 0
  
  k = 1;
  while (k <= (size_of_factbase + WALK_SIZE_INC + bigprimes)) { 
    s = smooth(w1, w2, F, size_of_factbase, factorization, D);
    if (s) {
      // This if statement will run if we get an almost smooth ideal.
      if(s-1){
	// Store the factorization in a binary search tree.
	// If it's not very optimized, then we can always change it over to a red-black tree.
	find = insert(&root, factorization, (a + prev_a) % N, (b + prev_b) % N);
	// Then check if there is a duplicate.	
	if(find){
	  // We have found the second ideal in which the primes match, so add both of them in.
	  if(!to_long(find->factors[0][1])){
	    num = to_long(find->factors[0][0]);
	    temp = x_coord[k-1];
	    x_coord[k]=num+temp;
	    for(j=0; j<num-1; j++){
	      y_coord[temp+j] = to_long(find->factors[j+1][0]);
	      exponent[temp+j] = to_long(find->factors[j+1][1]);
	    }
	    // And now the large prime.
	    y_coord[temp+num-1] = size_of_factbase+bigprimes;
	    exponent[temp+num-1] = 1;

	    alpha[k-1] = find->as;
	    beta[k-1] = find->bs;

	    // And now the second one.
	    k++;
	    num = to_long(factorization[0][0]);
            temp = x_coord[k-1];
            x_coord[k]=num+temp;
            for(j=0; j<num-1; j++){
              y_coord[temp+j] = to_long(factorization[j+1][0]);
              exponent[temp+j] = to_long(factorization[j+1][1]);
            }
	    // And now the lare prime.
            y_coord[temp+num-1] = size_of_factbase+bigprimes;
            exponent[temp+num-1] = 1;

	    alpha[k-1] = ((a + prev_a) % N);
	    beta[k-1] = ((b + prev_b) % N);

	    if(k%25 == 0){
	      cout<<"We have found "<< k <<" smooth ideals.\n";
	    }

	    k++;

	    // Here we set the flag so that this ideal is not re-entered into the matrix.
	    bigprimes++;
	    find->factors[0][1] = bigprimes;

	  }
	  // We have now found three or more matching prime ideals, so just add one in.
	  else{
	    num = to_long(factorization[0][0]);
            temp = x_coord[k-1];
            x_coord[k]=num+temp;
            for(j=0; j<num-1; j++){
              y_coord[temp+j] = to_long(factorization[j+1][0]);
              exponent[temp+j] = to_long(factorization[j+1][1]);
            }
            // And now the lare prime.
            y_coord[temp+num-1] = size_of_factbase-1+to_long(find->factors[0][1]);
            exponent[temp+num-1] = 1;

	    alpha[k-1] = ((a + prev_a) % N);
	    beta[k-1] = ((b + prev_b) % N);
	    
	    if(k%25 == 0){
	      cout<<"We have found "<< k <<" smooth ideals.\n";
	    }
	    // In this case we don't need to increment bigprimes since this prime is one that has already been used.
	    // Instead we increment the ideal counter.
            k++;
	    
	  }
	}

      }
      // This will run for smooth ideals.
      else {
	if(k==1){
	  cout<<"We have our first smooth element.\n";
	}
	num = to_long(factorization[0][0]);
	temp = x_coord[k-1];
	x_coord[k]=num+temp;
	
	for(j=0 ; j<num ; j++){
	  y_coord[temp+j]=to_long(factorization[j+1][0]);
	  exponent[temp+j]=(int)to_long(factorization[j+1][1]);
	}
	alpha[k-1] = ((a + prev_a) % N);
	beta[k-1] = ((b + prev_b) % N);
	if(k%25 == 0){
	  cout<<"We have found "<< k <<" smooth ideals.\n";
	}
	k++;       
      }
    }
    prev_a = (a + prev_a) % N; 
    prev_b = (b + prev_b) % N;
    step(w1, w2, M, E, w1, w2, a, b, D);
  } // end while loop. Take the next step, if needed.
  
  cout<<bigprimes<<"\n";

  // Done walking. Get a drink of water.
  // We can now send the matrix (representation) and search for a nonzero element of the kernel.
  long i;
  cout << "We're done walking. Now we do Jonathan's Lanczos Linear Algebra black magic.\n";
  
  kernel=Lanczos_Random(x_coord, y_coord, exponent, size_of_factbase+WALK_SIZE_INC+bigprimes, N);
  cout<<"Linear Algebra Done.\n";
  for (i = 0; i < size_of_factbase+WALK_SIZE_INC+bigprimes; i++) {
    x+=MulMod(alpha[i], rep(kernel[i]), N);
    x%=N;
  }
  
  cout<<"alphas done\n";

  for (i = 0; i < size_of_factbase+WALK_SIZE_INC+bigprimes; i++) {
    x2+=MulMod(beta[i], rep(kernel[i]), N);
    x2%=N;
  }
  
  cout<<"betas done\n";

  // x marks the spot... where g^x=h. HA!
  x=MulMod(-x, InvMod(x2, N), N);
  
  cout << "\n"<< "X marks the spot: "<< x <<"\n\n"<<"Who's your daddy?"<<"\n\n";
  
  power(g1, g2, x, h1, h2, D);
  
  cout<<"("<<g1<<", "<<g2<<")^"<<x<<" = ("<<h1<<", "<<h2<<").\n\n";
  
  return;
}


// This will insert a node into our binary search tree. If there is a duplicate, return a pointer to
// the struct there. Otherwise, insert the node, and return NULL.
Node *insert(Node **root, ZZ fact[10][2], ZZ astep, ZZ bstep){
  Node *p = *root;
  Node *n;
  long prime = to_long(fact[0][0]);
  while(p != NULL){
    if(p->factors[to_long(p->factors[0][0])][0] > fact[prime][0]){
      if(p->left)
	p = p->left;
      else{
	n = new Node;
	p->left = n;
	n->left = NULL;
	n->right = NULL;
	// Copy the array over.
	for(long i=0; i<=prime; i++){
	  n->factors[i][0] = fact[i][0];
	  n->factors[i][1] = fact[i][1];
	}
	n->as = astep;
	n->bs = bstep;
	return(NULL);
      }
    }
    else if(p->factors[to_long(p->factors[0][0])][0] < fact[prime][0]){
      if(p->right)
	p=p->right;
      else{
	n = new Node;
	p->right = n;
	n->left = NULL;
	n->right = NULL;
	// Copy the array over.
	for(long i=0; i<=prime; i++){
	  n->factors[i][0] = fact[i][0];
	  n->factors[i][1] = fact[i][1];
	}
	n->as = astep;
	n->bs = bstep;
	return(NULL);
      }
    }
    else{
      //This is the case in which we have a duplicate, a very good thing.
      return(p);
    }
  }
  if(*root == NULL){
    *root = new Node; 
    (*root)->left = NULL;
    (*root)->right = NULL;
    // Copy the array over.
    for(long i=0; i<=prime; i++){
      (*root)->factors[i][0] = fact[i][0];
      (*root)->factors[i][1] = fact[i][1];
    }
    (*root)->as = astep;
    (*root)->bs = bstep;
  }
  return(NULL);
}



//calculates x such that x=bA'
// The matrix that is inputted from the walk. (length)x(length-5)

vec_ZZ_p Matrix_Vector(long x_c[], long y_c[], int value[], vec_ZZ_p b, long length)
{
  long i = 0, j=0;
  vec_ZZ_p out;
  out.SetLength(length);

  for(i=0; i<length; i++)
    {
      for( j = x_c[i]; j < x_c[i+1]; j++)
	{
	  out[i] += value[j]*b[y_c[j]];
	}
    }
  return out;
}

//Calculates x such that x = bA
//The transpose has more columns than rows.

vec_ZZ_p MatrixTrans_Vector(long x_c[], long y_c[], int value[], vec_ZZ_p b, long length)
{
  long i=0, j;
  vec_ZZ_p out;
  out.SetLength(length-5);

  for(j=0;j<length; j++)
    {
      for( i = x_c[j]; i < x_c[j+1]; i++)
	{
	  out[y_c[i]] += value[i]*b[j];
	}
    }
  return out;
}

// Use xprime as a dummy vector. Then actually solve system xA=bprime where bprime is an xpA.

vec_ZZ_p Lanczos_Random(long x_c[], long y_c[], int value[], long length, ZZ N)
{
  ZZ_p::init(N);

  vec_ZZ_p bprime;
  vec_ZZ_p x;
  vec_ZZ_p xprime;
  vec_ZZ_p out;

  bprime.SetLength(length);
  xprime.SetLength(length);
  x.SetLength(length);
  out.SetLength(length-5);
  
  for(long i = 0; i <length; i++)
    {
      xprime[i] = random_ZZ_p();
    }

  bprime = Matrix_Vector(x_c,y_c,value,MatrixTrans_Vector(x_c,y_c,value,xprime, length), length);

  x = Lanczos_Inner(x_c,y_c,value,bprime, length);

  //creating actual solution... assumes x-xprime != 0)
  return (x-xprime);
}

vec_ZZ_p Lanczos_Inner(long x_c[], long y_c[], int value[], vec_ZZ_p b, long length)
{
  vec_ZZ_p w_n, w_m, w_o, v_n, v_m, v_o, x; 
  ZZ_p t_n, t_m, t_o;

  w_o.SetLength(length);
  w_m.SetLength(length);
  v_m.SetLength(length);
  x.SetLength(length);
  
  t_n = 1;
  w_n = b;

  if( IsZero(w_n) )
    {
      return x ;
    }
  else
    {
      v_n = Matrix_Vector(x_c,y_c,value,MatrixTrans_Vector(x_c,y_c,value,w_n, length), length);
      t_m = t_n;
      t_n = inv(v_n*w_n);
      if( t_n == 0)
	cerr<< "I'm a big *&^$&^%\n";
      else
	x = (b*w_n)*t_n*w_n;
    }

  int i = 1;
  while( i < b.length() +10)
    {
      w_o = VectorCopy(w_m, length);
      w_m = w_n;
      w_n = v_n -(((v_n*v_n)*t_n)*w_m)-(((v_n*v_m)*t_m)*w_o);
      if( IsZero(w_n) )
	return x;
      else
	{
	  v_o = v_m;
	  v_m = v_n;
	  v_n = Matrix_Vector(x_c,y_c,value,MatrixTrans_Vector(x_c,y_c,value,w_n, length), length);
	  t_o = t_m;
	  t_m = t_n;
	  t_n = inv(w_n*v_n);
	  if( t_n == 0)
	    cerr<< "You %$#@$% stupid person.\n";
	  else
	    {
	      x = x +b*w_n*t_n*w_n;
	      i++;
	    }
	}
    }
}

int main() {
  ZZ g1 = to_ZZ(0); ZZ g2 = to_ZZ(0); ZZ p = to_ZZ(19); ZZ x, h1, h2; long S;
  ZZ c = to_ZZ(10);
  RR size;
  long s;

  //ZZ D=-to_ZZ(power(c, 10))-to_ZZ(343);
  //ZZ N=to_ZZ(64951);

  ZZ D = (- power(c, 25) - 3151); 
  ZZ N = (3*power(c, 12) + 7*power(c, 10) + 4*power(c, 8) + 7*power(c, 7) + 2*power(c, 6) + 2*power(c, 5) + to_ZZ(64887));

 // The group order is N=3070472264887, which is prime.
 
  cout <<"\n Discriminant= "<< D << "\n Size of the class group= " << N << "\n\n";

  int created = 0; 
  while (created == 0) {
    created = create_example(p, g1, g2, D);
    p = NextPrime(p+1);
  }
  SetSeed(to_ZZ(time(NULL))); // random # generator seed init.
  x = RandomBnd(N-1); // in the range 0..N-2

  cout << "x: " << x << "\n";
  cout << "g: " << g1 << "\t" << g2 << "\n";
  power(g1, g2, x, h1, h2, D);
  cout << "h: " << h1 << "\t" << h2 << "\n";

  S =9; 

  // Given S, this little routine will create a matrix for the factor base that is MUCH closer to the actual size of the factor base.
  // The numebrs are based on the Prime Numebr Theorem, plus a little fudge factor determined from experimental data.
  size = pow(2, S);
  size/=log(size);
  size*=1.3;
  ZZ F[to_long(TruncToZZ(size))][2];
  s = create_factorbase(D, S, F);
  cout << "Size of the factor base= " << s << "\n";

  ZZ M[16][2]; ZZ E[16][2];
  create_multipliers(g1, g2, h1, h2, N, M, E, D);
  walk(g1, g2, h1, h2, M, E, F, s, N, D);
  return 1;
}


