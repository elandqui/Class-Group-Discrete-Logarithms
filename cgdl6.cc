#include "cgdl.h"

// Convert an ideal (a, b) to its equivalent reduced form.
// Uses the algorithm described in Cohen.
int reduce(ZZ& a, ZZ& b) {
  ZZ c, u;
  c = (b*b - D)/(4*a);
  if ((-a < b) && (b <= a)) {
    if (a > c) {
      b = -b; u = a; a = c; c = u;
    } 
    else {
      if ((a == c) && (b < 0)) {
	b = -b;
      }
      return 1;
    }
  }

  ZZ q, r, a0, a1;

  do {
    q = b/(2*a); r = b % (2*a);
    if (r > a) {
      r = r-2*a; q++;
    }
    c = c - (b+r)*q/2; b = r;
    a0 = a; a1 = c;
    if (a > c) {
      b = -b; u = a; a = c; c = u;
    }
  } while (a0 > a1);
  if ((a == c) && (b < 0)) { b= -b; }
  return 1;
}

// Multiply two ideals (a1, b1) and (a2, b2) in reduced form. Result
// (a3, b3) is in reduced form
void multiply(ZZ a1, ZZ b1, ZZ a2, ZZ b2, ZZ& a3, ZZ& b3) {
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
  reduce(a3, b3);
}

// Squares the reduced ideal (a1, b1). The result (a3, b3) is in reduced
// form.
void square(ZZ a1, ZZ b1, ZZ& a3, ZZ& b3) {
  ZZ d, v, w;
  XGCD(d, v, w, a1, b1);
  b3 = b1 + w*(D - (b1*b1))/(2*d);
  a3 = sqr(a1/d); b3 = b3 % (2*a3);
  reduce(a3, b3);
}

// Computes (a1, b1)^n and stores the result in (c1, c2). The input should
// be reduced, and the output is reduced.
void power(ZZ a1, ZZ b1, ZZ n, ZZ& c1, ZZ& c2) {
  ZZ B1, B2, d1, d2;
  B1 = a1; B2 = b1; c1 = 1; c2 = 1; // c = id.
  while (n > 0) {
    if ((n % 2) == 1) {
      multiply(c1, c2, B1, B2, d1, d2);
      c1 = d1; c2 = d2;
    }
    n = n/2;                     
    if (n > 0) {
      square(B1, B2, d1, d2);
      B1 = d1; B2 = d2;
    }
  }
}

// Given a prime p and a discriminant D, tries to compute a prime ideal above
// p. If it succeeds, it stores the reduced ideal in (g1, g2) and returns 1,
// else g1, g2 contains garbage and 0 is returned.
int create_example(ZZ p) {
  ZZ d = (D % p);  
  if (Jacobi(d, p) == 1) {
    ZZ temp =  SqrRootMod(d, p);
    temp = p-temp;
    g2 = MulMod((d - temp), InvMod(to_ZZ(2), p), p);
    g2 = (D - 2*g2);
    g1 = p;
    reduce(g1, g2);
    return 1;
  } else { return 0; }
}

// D - disc, S = size of the factor base.
void create_factorbase() {
  ZZ p, b; ZZ P = to_ZZ(3);
  ZZ d, t0; 
  int i=0;
  float error2=0; // This will be an error for our tolerance.

  // Throwing in the prime 2. 
  if((D%8)==1){
    F[0][0] = 2; F[0][1] = 1;
    Fbits[i]=(char)NumBits(F[0][0]);
    i++;
  }
  // We don't handle this case in our big example.
  //else{
  
  //}
  // Now we make the rest of the factor base
  while (i<S) {
    P = NextPrime(P);
    // We expect D to be prime, so we can ignore the case of (p, D)!=1.
    p = P;
    d = D % p;
    
    if (Jacobi(d, p) == 1) {
      t0 = InvMod(to_ZZ(2), p);
      b =  ((d - SqrRootMod(d, p))*t0) % p;
      b = (D - 2*b);
      reduce(p, b);
      if(b>0){
	F[i][0] = (int)to_long(p); 
	F[i][1] = (int)to_long(b);
      }
      else{
	F[i][0] = (int)to_long(p); 
	F[i][1] = (int)to_long(-b);
      }
      Fbits[i]=NumBits(p);
      i++;
    }
    P++;
  }
  // This extension will store a factor times the largest prime in the factor base.
  // It will be used to speed up the algorithm like the large prime SIQS.
  F[S][0]=LPFAC*F[S-1][0];

  // Now we'll create an error for how many bits we can expect
  i=0;
  if(F[0][0]==2){
    error2=1;
    i=1;
  }
  else
    error2=0;

  while(i<SKIP){
    error2+=(float)(2*Fbits[i])/(float)F[i][0];
    i++;
  }
  error=(char)error2+1;
}

// Generate relations.

void rels_siqs(int x_coord[], int y_coord[], char exponent[]){

  short s2 = S+ER;
  int ihigh=S-1;
  int ilow = 0;
  int i=ihigh/2;

  ZZ bin;

  // The coefficient of x^2 for f(x).
  ZZ a=to_ZZ(1);

  ZZ condition = to_ZZ(F[S-1][0]/2);
  //cout<<to_long(to_ZZ(SqrRoot(to_RR(abs(D))/2))/power(condition, t))<<endl;

  ZZ bound = to_ZZ(SqrRoot(to_RR(abs(D))/2))/M;

  //ZZ condition = TruncToZZ(power(to_RR(SqrRoot(to_RR(abs(D))/2)/M), 1.0/t));
  
  // A tolerance constant. 
  // Any values of SI greater than this will be checked for smoothness.
  TOL = (int)to_long(NumBits(TruncToZZ(M*sqrt(abs(to_RR(D))/2))))-error-(int)to_long(NumBits(F[S-1][0]))+TOLERR;

  int j=0;

  // Will be the ideal such that a = FB^e.
  ZZ a1, a2;
  int e[t2];

  int ranout = 1;
  for(j=0; j<t; j++){
    ranout+=(int)pow(2, t2-j);
  }

  // Find the smallest prime ideal in the factor base whose norm is larger than the condition.
  while(!((F[i][0]>=condition)&&(F[i-1][0]<=condition))){
    if(F[i][0] < condition){
      ilow= i;
      i=(i+ihigh)/2;
    }
    else{
      ihigh = i;
      i = (i+ilow)/2;
    }
  }

  Q = i-t2/2;
  
  j=0;
  
  bin = power(to_ZZ(2), t-1);
  
  // Store some values ahead of time to make switching polynomials even faster.
  precomputation();

  // Set it up so that we have a good first set of sieving polynomials.
  while(weight(mark)!=t)
    mark++;

  while((K<s2)&&(mark<=ranout)){
    while((j<bin)&&(K<s2)){    
      // Get a new polynomial.
      new_polynomial(a1, a2, e, bin, j);

      // Now we sieve the interval [-M, M] with this polynomial.
      sieve();

      // Pick out the smoothies.
      getSmooth(x_coord, y_coord, exponent, e);
    }
    // Shifting mark twice should reduce the number of dependencies in the matrix.
    mark++;
    while(weight(mark)!=t)
      mark++;
    mark++;
    while(weight(mark)!=t)
      mark++;
    j=0;
  }
  if(mark>ranout){
    cout<<"More polynomials or a larger factor base needed.\n\n";
    exit(1);
  }
  else{
    //cout<<entries<<" of "<<MAX_HT<<" spots in the hash table were used.\n\n";
  }

  // Right now we can shrink the matrix size down considerably.
  gausselim(x_coord, y_coord, exponent);


  // Now we sieve to find smooth representations of g and h.

  // Flags to tell if we need to sieve for smooth values of g and h.
  char sieveg=1;
  char sieveh=1;
  int factorization[FMAX][2];
  ZZ c1, c2;
  int P;
  ZZ n;

  int num;

  int randome[25]; // A vector for randomly computing h times a product of primes.

  int ff, rr; //Counters
  int f2[FMAX][2]; // A temporary factorization array.

  // We could get lucky.
  if(trialdivide(g1, g2, factorization)==1){
    get_rel(x_coord, y_coord, exponent, factorization);
    sieveg=0;
  }

  // Now if g is not smooth initially, we will sieve to find a smooth value.
  // First we multiply it by a collection of small primes.
  while(sieveg){
    c1=g1;
    c2=g2;

    // Set the random vector array.
    for(i=0; i<25; i++){
      randome[i]=rand()%3-1;
    }
    
    // 1. Compute C=(c1, c2) = h*F^v where v is "random"
    for(i=0; i<25; i++){
      if(randome[i]==1)
	multiply(c1, c2, to_ZZ(F[i][0]), to_ZZ(F[i][1]), c1, c2);
      if(randome[i]==-1)
	multiply(c1, c2, to_ZZ(F[i][0]), to_ZZ(-F[i][1]), c1, c2);
    }
    // Get the roots mod p.
    SetCoeff(SP, 2, c1);
    SetCoeff(SP, 1, c2);
    SetCoeff(SP, 0, (c2*c2-D)/(4*c1));

    // Initializing ainv.
    for(i=1; i<S; i++){
      P = F[i][0];
      if(((2*c1)%P)!=0)
	ainv[i] = InvMod((2*c1)%P, P);
    }

    // Get the roots of the SP mod each prime in the factor base.
    for(i=0; i<S; i++){
      P = F[i][0];
      // If we have a single root.
      if (!(coeff(SP,2)%P)){
	R[i][0] = (-coeff(SP,0)*InvMod(c2%P, P))%P;
	R[i][1] = 0;
      }
      // We need to treat the case P==2 separately because of the formula below.
      else if(P==2){
	R[i][0]=0;
	R[i][1]=1;
      }
      // Otherwise we have two roots.
      else {
	R[i][0] = (((-c2+rootD[i])%P)*ainv[i])%P;
	R[i][1] = (((-c2-rootD[i])%P)*ainv[i])%P;
	// Making sure that any root that is 0 goes first.
	if(!(R[i][1])){
	  R[i][1]=R[i][0];
	  R[i][0]=0;
	}  
      }
    }

    // Now we sieve the interval [-M, M] with this polynomial.
    sieve();

    int max=2*M+1;

    for(i=0; i<max; i++){
    // Possible smooth number.
      if (SI[i] > TOL){
	// The trialdivide function returns 1 if the number is smooth.
	n = coeff(SP, 0)+(i-M)*coeff(SP, 1)+(i-M)*(i-M)*coeff(SP, 2);
	if(trialdivide(n, -2*(i-M)*coeff(SP, 2)-coeff(SP, 1), factorization)==1){
	  // Combine the random exponent vector with the factorization here.

	  num=factorization[0][0];
	  ff=1; // Counter for the new factorization array.
	  rr=0; // Counter for the random array.
	  j=1;  // Counter for the old factorization array.

	  while((j<=num)&&(rr<25)){
	    while((rr<factorization[j][0])&&(rr<25)){
	      if(randome[rr]){
		f2[ff][0]=rr;
		f2[ff][1]=-randome[rr];
		ff++;
	      }
	      rr++;
	    }
	    while((j<=num)&&(factorization[j][0]<rr)){
	      f2[ff][0]=factorization[j][0];
	      f2[ff][1]=-factorization[j][1];
	      ff++;
	      j++;
	    }
	    if((rr==factorization[j][0])&&(rr<25)&&(j<=num)){
	      if(randome[rr]){
		if(randome[rr]!=factorization[j][1]){
		  f2[ff][0]=rr;
		  f2[j][1]=factorization[j][1]-randome[rr];
		  ff++;
		}
		j++;
	      }
	      rr++;
	    }
	  }
	  if(rr==25){
	    while(j<=num){
	      f2[ff][0]=factorization[j][0];
	      f2[ff][1]=factorization[j][1];
	      ff++;
	      j++;
	    }
	  }
	  
	  f2[0][0]=ff-1;
	  get_rel(x_coord, y_coord, exponent, f2);
	  sieveg=0;
	  break;
	}
      }
    }
  }

  // We could get lucky with h.
  if(trialdivide(h1, h2, factorization)==1){
    get_rel(x_coord, y_coord, exponent, factorization);
    sieveh=0;
  }

  while(sieveh){
    
    c1=h1;
    c2=h2;

    // Set the random vector array.
    for(i=0; i<25; i++){
     randome[i]=rand()%3-1;
    }

    // 1. Comute C=(c1, c2) = h*F^v where v is "random"
    for(i=0; i<25; i++){
      if(randome[i]==1)
	multiply(c1, c2, to_ZZ(F[i][0]), to_ZZ(F[i][1]), c1, c2);
      if(randome[i]==-1)
	multiply(c1, c2, to_ZZ(F[i][0]), to_ZZ(-F[i][1]), c1, c2);
    }
    // Get the roots mod p.
    SetCoeff(SP, 2, c1);
    SetCoeff(SP, 1, c2);
    SetCoeff(SP, 0, (c2*c2-D)/(4*c1));

    // Initializing ainv.
    for(i=1; i<S; i++){
      P = F[i][0];
      if(((2*c1)%P)!=0)
	ainv[i] = InvMod((2*c1)%P, P);
    }

    // Get the roots of the SP mod each prime in the factor base.
    for(i=0; i<S; i++){
      P = F[i][0];
      // If we have a single root.
      if (!(coeff(SP,2)%P)){
	R[i][0] = (-coeff(SP,0)*InvMod(c2%P, P))%P;
	R[i][1] = 0;
      }
      // We need to treat the case P==2 separately because of the formula below.
      else if(P==2){
	R[i][0]=0;
	R[i][1]=1;
      }
      // Otherwise we have two roots.
      else {
	R[i][0] = (((-c2+rootD[i])%P)*ainv[i])%P;
	R[i][1] = (((-c2-rootD[i])%P)*ainv[i])%P;
	// Making sure that any root that is 0 goes first.
	if(!(R[i][1])){
	  R[i][1]=R[i][0];
	  R[i][0]=0;
	}  
      }
    }

    // Now we sieve the interval [-M, M] with this polynomial.
    sieve();

    int max=2*M+1;

    for(i=0; i<max; i++){
    // Possible smooth number.
      if (SI[i] > TOL){
	// The trialdivide function returns 1 if the number is smooth.
	n = coeff(SP, 0)+(i-M)*coeff(SP, 1)+(i-M)*(i-M)*coeff(SP, 2);
	if(trialdivide(n, -2*(i-M)*coeff(SP, 2)-coeff(SP, 1), factorization)==1){
	  // Combine the random exponent vector with the factorization here.

	  num=factorization[0][0];
	  
	  ff=1; // Counter for the new factorization array.
	  rr=0; // Counter for the random array.
	  j=1;  // Counter for the old factorization array.

	  while((j<=num)&&(rr<25)){
	    while((rr<factorization[j][0])&&(rr<25)){
	      if(randome[rr]){
		f2[ff][0]=rr;
		f2[ff][1]=-randome[rr];
		ff++;
	      }
	      rr++;
	    }
	    while((j<=num)&&(factorization[j][0]<rr)){
	      f2[ff][0]=factorization[j][0];
	      f2[ff][1]=factorization[j][1];
	      ff++;
	      j++;
	    }
	    if((rr==factorization[j][0])&&(rr<25)&&(j<=num)){
	      if(randome[rr]){
		if(randome[rr]!=factorization[j][1]){
		  f2[ff][0]=rr;
		  f2[ff][1]=factorization[j][1]-randome[rr];
		  ff++;
		}
		j++;
	      }
	      rr++;
	    }
	  }
	  if(rr==25){
	    while(j<=num){
	      f2[ff][0]=factorization[j][0];
	      f2[ff][1]=factorization[j][1];
	      ff++;
	      j++;
	    }
	  }
	  
	  f2[0][0]=ff-1;

	  // This will prevent h from being added to the matrix if it has a previously unused prime factor.
	  // If it's smooth except for an unused prime factor, keep looking.
	  sieveh=0;
	  for(int jj=1; jj<ff; jj++){
	    if(!FT[f2[jj][0]])
	      sieveh=1;
	  }
	  if(!sieveh){
	    get_rel(x_coord, y_coord, exponent, f2);
	    break;
	  }
	}
      }
    }
  }
}

// Pick out the smooth elements from the sieving interval.
// Then arrange to have the relation stored.
void getSmooth(int x_coord[], int y_coord[], char exponent[], int e[]){
  
  int i, j;
  int max = 2*M+1;
  ZZ n;
  ZZ a1, a2;
  int lp; // A flag for a large prime.
  ZZ b1, b2, q1, q2;
  int l;

  // A temporary storage for the factorization
  int factorization[FMAX][2];

  // The values of the polynomial are bounded above by ln(M*sqrt(D/2)), so we pick out 
  // those values in the sieving interval which are close to this.
  for(i=0; i<max; i++){
    // Possible smooth number.
    if (SI[i] > TOL){
      TDIV++;
      // The trialdivide function returns 1 if the number is smooth.
      n = coeff(SP, 0)+(i-M)*coeff(SP, 1)+(i-M)*(i-M)*coeff(SP, 2);
      lp = trialdivide(n, -2*(i-M)*coeff(SP, 2)-coeff(SP, 1), factorization);
      //if(lp==1)
      // 	cout<<i-M<<endl;
      if (lp){
	// If we have a large prime, insert it into the hash table.
	// If there is a duplicate in the hash table, then add in the two entries
	combine(factorization, e);

	if(lp-1){  
	  if(insert(factorization)) {
	    get_rel(x_coord, y_coord, exponent, factorization); 
	  }
	}
	else{
	  get_rel(x_coord, y_coord, exponent, factorization);
	}
      }
    }
  }
}

// This function will combine the factorization array with the exponent array and put the results 
// back in the factorization array.

void combine(int f[][2], int e[]){
  short i=0;
  int edge;    // The edge of the possible factorization array.
  int num = f[0][0];
  int j=1;
  int fend;  // Will be a mark for the factorization array.
  int m=mark;
  short total;

  // First figure out the location of largest index less than Q.
  while((f[j][0]<Q)&&(j<=num))
    j++;
  
  // This situation was causing trouble in the later loop.
  // This is the easy case in which all the primes dividing the smooth ideal
  // are less than the primes that divide the coefficient of f in the sieving polynomial.
  if(j==num+1){
    for(i=0; i<t2; i++){
      if(m&1){
	f[0][0]++;
	f[j][0]=Q+i;
	f[j][1]=e[i];
	j++;
      }
      m>>=1;
    }
    return;
  }

  // Shift the remaining spots over t spots to make room for the primes.
  for(i=0; i<=num-j; i++){
    f[num+t-i][0]=f[num-i][0];
    f[num+t-i][1]=f[num-i][1];
  }

  // Then just pop stuff in beginning in spot j:
  // If the first element of e[] is less than the first element of f[][], put it in that spot, etc.
  fend = j+t;
  edge = num+t;
  total= edge;
  i=0;
  while(num<total){
    // Keep shifting m until we get to one of the t 1's in it.
    while(!(m&1)){
      m>>=1;
      i++;
    }
    // m now indexes the prime Q+i.
    // Recall that j indexes the next open spot in the factorization array.
    if(Q+i < f[fend][0]){
      f[j][0]=Q+i;
      f[j][1]=e[i];
      j++;
      num++;
      m>>=1;
      i++;
    }
    else if(Q+i == f[fend][0]){
      if(e[i]+f[fend][1]){
	f[j][0]=Q+i;
	f[j][1]=e[i]+f[fend][1];
	j++;
      }
      total--;
      fend++;
      m>>=1;
      i++;
    }
    else{
      while((fend<=edge) && (f[fend][0] < Q+i)){
	f[j][0]=f[fend][0];
	f[j][1]=f[fend][1];
	j++;
	fend++;
      }
      if(fend==edge+1)
	f[fend][0]=S;
    }
  }
  // Now there will be edge-num spaces to fill in with the original primes.
  if(edge!=num){
    for(i=fend; i<=edge; i++){
      f[j][0]=f[i][0];
      f[j][1]=f[i][1];
      j++;
    }
  }
  // Update the number of factors.
  f[0][0]=num;
}

void get_rel(int x_coord[], int y_coord[], char exponent[], int factorization[][2]){
  
  int i;
  int num, temp;

  num = factorization[0][0];
  temp = x_coord[K];

  // Put the factorization array into the matrix.

  for(i=1; i<=num; i++){
    y_coord[temp+i-1]=factorization[i][0];
    exponent[temp+i-1]=factorization[i][1];

    // Counting the number of times each prime is used.

    FT[factorization[i][0]]++;
  }

  x_coord[K+1] = num+temp;

  K++;

  if(!(K%KINT))
    cout<<K<<" smooth elements in "<<GetTime()-begintime<<" CPU seconds.\n";

}

int trialdivide(ZZ w1, ZZ w2, int factorization[][2]){
  int i;
  ZZ P;
  int factors=1;
  int e;

  for(i=0; i<S; i++){
    P=F[i][0];
    if (IsZero(w1%P)){
      e=1;
      w1/=P;
      while(IsZero(w1%P)){
	e++;
	w1/=P;
      }
      factorization[factors][0] = i;
      if((w2 % (2*P)) == F[i][1]) 
	factorization[factors][1] = sign(w1)*e;
      else
	factorization[factors][1] = -sign(w1)*e;

      factors++;

    }
    // Early-exit strategy if we're done trial dividing this guy.
    if(IsOne(w1))
      break;
  }
  
  if (IsOne(abs(w1))){
    factorization[0][0]=factors-1;
    return(1);
  }
  if(abs(w1)<F[S][0]){
    factorization[factors][0]=to_long(abs(w1));
    // If the second element of the reduced ideal is less than w1, we'll call this the positive ideal.
    if((w2%(2*w1))<abs(w1))
      factorization[factors][1]=1;
    else
      factorization[factors][1]=-1;
    factorization[0][0]=factors;
    return(2);
  }
  return(0);

}

// Sieve the interval for smooth values of f(x).
// The sieving interval is [-M, M], so the location x=i is indexed by i+M.
void sieve (){
  int a, i;
  char bits;
  int P;
  int max = 2*M+1;

  // Initialize the sieve.
  for(i=0; i<max; i++)
    SI[i]=0;

  for(i=SKIP; i<S; i++){
    P = F[i][0];
    bits = Fbits[i];
    
    // Sieve to the left.
    a=M+R[i][0];
    if(a>=0){
      while(a<max){
	SI[a]+=bits;
	a+=P;
      }
    }
    // Sieve to the right.
    a=M+R[i][0]-P;
    if(a<max){
      while(a>=0){
	SI[a]+=bits;
	a-=P;
      }
    }

    // We could be in the situation that SP%P has only one root with the SIQS.
    if(R[i][1]){
      // Sieve left.
      a=M+R[i][1];
      if(a>=0){
	while(a<max){
	  SI[a]+=bits;
	  a+=P;
	}
      }
      // Sieve right.
      a=M+R[i][1]-P;
      if(a<max){
	while(a>=0){
	  SI[a]+=bits;
	  a-=P;
	}
      }
    }
  }
}

void precomputation(){
  ZZ P;
  int i;

  for(i=0; i<S; i++){
    P= to_ZZ(F[i][0]);
    rootD[i] = (int)to_long(SqrRootMod(D%P, P));
  }
}

//Generates a new polynomial using SIQS.
void new_polynomial(ZZ& a1, ZZ& a2, int e[], ZZ bin, int& j){
int i;
  int P;
  ZZ a= to_ZZ(1);
  ZZ b = to_ZZ(0);
  int v=0;
  int v2;
  int pow2 = 2;
  int m=mark;
  int off;

  ZZ w1=to_ZZ(1); 
  ZZ w2=to_ZZ(1);
  
  // We get the first polynomial.
  if(j==0){
    for(i=0; i<t2; i++){
      if(m&1){
	multiply(w1, w2, to_ZZ(F[Q+i][0]), to_ZZ(F[Q+i][1]), w1, w2);
	e[i]=-1;
      }
      else
	e[i]=0;
      m>>=1;
    }

    SetCoeff(SP, 2, w1);
    SetCoeff(SP, 1, w2);
    SetCoeff(SP, 0, (w2*w2-D)/(4*w1));

    // Initializing ainv.
    for(i=1; i<S; i++){
      P = F[i][0];
      if(((2*w1)%P)!=0)
	ainv[i] = InvMod((2*w1)%P, P);
    }

    // Get the roots of f mod each prime in the factor base.
    for(i=0; i<S; i++){
      P = F[i][0];
      // If we have a single root.
      if (!(coeff(SP,2)%P)){
	R[i][0] = (-coeff(SP,0)*InvMod(w2%P, P))%P;
	R[i][1] = 0;
      }
      // We need to treat the case P==2 separately because of the formula below.
      else if(P==2){
	R[i][0]=0;
	R[i][1]=1;
      }
      // Otherwise we have two roots.
      else {
	R[i][0] = (((-w2+rootD[i])%P)*ainv[i])%P;
	R[i][1] = (((-w2-rootD[i])%P)*ainv[i])%P;
	// Making sure that any root that is 0 goes first.
	if(!(R[i][1])){
	  R[i][1]=R[i][0];
	  R[i][0]=0;
	}  
      }
    }
  }
  else {
    // Find v s.t. 2^v || 2j
    while(!((2*j)%pow2)){
      v++;
      pow2*=2;
    }
    pow2/=2;

    //Change the exponent vector.
    off=0;
    v2=v;
    while(v2){
      (!(m&1)) ? off++ : v2--;
      m>>=1;
    }
    e[v+off-1]+=2*( ((j/pow2)%2) ? -1 : 1 );
    //e[v+off-1]+=2*(int)pow(-1, ceil(j/pow2));

    w1 = coeff(SP, 2);
    w2 = coeff(SP, 1);
    square(to_ZZ(F[Q+v+off-1][0]), to_ZZ(F[Q+v+off-1][1]), a, b);
    multiply(w1, w2, a, -b*pow(-1, ceil(j/pow2)), w1, w2);
    SetCoeff(SP, 2, w1);
    SetCoeff(SP, 1, w2);
    SetCoeff(SP, 0, (w2*w2-D)/(4*w1));
    
    // Get the roots of f mod each prime in the factor base.
    for(i=0; i<S; i++){
      P = F[i][0];
      // If we have a single root.
      if (!(w1%P)){
	R[i][0] = (-coeff(SP,0)*InvMod(w2%P, P))%P;
	R[i][1] = 0;
      }
      // We need to treat the case P==2 separately because of the formula below.
      else if(P==2){
	R[i][0]=0;
	R[i][1]=1;
      }
      // Otherwise we have two roots.
      else {
	R[i][0] = (((-w2+rootD[i])%P)*ainv[i])%P;
	R[i][1] = (((-w2-rootD[i])%P)*ainv[i])%P;	
	// Making sure that any root that is 0 goes first.
	if(!R[i][1]){
	  R[i][1]=R[i][0];
	  R[i][0]=0;
	}
      }
    }
  }
  j++;
}

// Will return 0 if either an element has been put into the hash table or there was an exact duplicate of two ideals.
// Will return 1 if we have a match in HT and will change the factorization for the relation function.
int insert(int factorization[][2]){
  
  int j;
  int num = factorization[0][0];
  int prime = factorization[num][0];
  int index = prime%MAX_HT; // The hash function.
  tailPtr=NULL; // The pointer such that tailPtr->next = currPtr.

  // In itialize the pointers.
  currPtr = HT[index];
 
  while(currPtr){
    // We have a match! Mix the two factorization arrays together.
    if((currPtr->prime)==prime){

      int j2, j0=0;
      int f[FMAX][2];
      int num2 = currPtr->factorization[0][0];
      int skip=0;

      // We have two possibilities: 
      // 1) the large prime in the hash table is the same as the large prime here, or
      // 2) the large primes are inverses.
      if(currPtr->factorization[num2][1] != factorization[num][1]){
        j=1;
        j2=1;
        while((j<num) || (j2<num2)){
          while(currPtr->factorization[j2][0] < factorization[j][0]){
	    j0++;
	    f[j0][0]=currPtr->factorization[j2][0];
	    f[j0][1]=currPtr->factorization[j2][1];
	    j2++;
          }
          while(currPtr->factorization[j2][0] > factorization[j][0]){
	    j0++;
	    f[j0][0]=factorization[j][0];
	    f[j0][1]=factorization[j][1];
	    j++;
          }
          if(currPtr->factorization[j2][0] == factorization[j][0]){
	    j0++;
	    f[j0][0]=factorization[j][0];
	    f[j0][1]=currPtr->factorization[j2][1]+factorization[j][1];
	    j++;
	    j2++;
          }
        }
        for(int i=1; i<=j0; i++){
          if(f[i][1]){
            factorization[i-skip][0] = f[i][0];
            factorization[i-skip][1] = f[i][1];
          }
          else
	    skip++;
        }
        if(j0==skip)
	  return(0);
	factorization[0][0]=j0-skip;
	return(1);
      }
      else {
        j=1;
        j2=1;
      
        while((j<num) || (j2<num2)){
          while(currPtr->factorization[j2][0] < factorization[j][0]){
	    j0++;
	    f[j0][0]=currPtr->factorization[j2][0];
	    f[j0][1]=-(currPtr->factorization[j2][1]);
	    j2++;
          }
          //if((j<num) || (j2<num2)
          while(currPtr->factorization[j2][0] > factorization[j][0]){
	    j0++;
	    f[j0][0]=factorization[j][0];
	    f[j0][1]=factorization[j][1];
	    j++;
          }
          if(currPtr->factorization[j2][0] == factorization[j][0]){
	    j0++;
            f[j0][0]=factorization[j][0];
	    f[j0][1]=factorization[j][1]-(currPtr->factorization[j2][1]);
	    j++;
	    j2++;
          }
        }
        for(int i=1; i<=j0; i++){
	  
          if(f[i][1]){
            factorization[i-skip][0] = f[i][0];
            factorization[i-skip][1] = f[i][1];
          }
          else
	    skip++;
        }
        if(j0==skip)
	  return(0);
        // j0--;
	factorization[0][0]=j0-skip;
        return(1);
      }
    }
    else {
      // If there is a collision, advance the pointer.
      if(!tailPtr)
	tailPtr=currPtr;

      currPtr=currPtr->next;
    }
  }

  // If the loop gets here, then this large prime is not in the hash table. Insert it.

  node *entryPtr;

  entries++;

  entryPtr = new node;
  (entryPtr->prime)=prime;
  for(j=0; j<=num; j++){
    (entryPtr->factorization[j][0])=factorization[j][0];
    (entryPtr->factorization[j][1])=factorization[j][1];
  }
  // Recall that we don't initialize tailPtr unless there is already an element 
  // in this spot of the hash table.
  if(!tailPtr)
    HT[index]=entryPtr;

  else 
    tailPtr->next = entryPtr;
  return(0);
}

// This will delete rows and columns from the matrix in order to speed up linear algebra.

void gausselim(int x_coord[], int y_coord[], char exponent[]){
  int i, j, jj, k, l, p1, p2;
  int killme=0;
  int smallest;
  int end = x_coord[K]; // The actual current length of the y_coord and exponent array.
  int shift;            // The number each element of the y_coord and exp array will be shifted.
  int deleted=0;
  int r1, r2;           // Place holders for two rows for stage 2 elimination.
  int fac[FMAX][2];     // Temporary factorization array for stage 2.

  // This will pin down the prime that is smallest given that it is represented once.
  for(i=S-1; i>=0; i--){
    //cout<<S-i-1<<" "<<FT[S-i-1]<<"   ";
    if(FT[i]==1){
      killme++;
      smallest=i;
    }
  }
  while(killme){
    // Stage 1.
    //cout<<"Beginning stage one.\n";
    while(killme){
      // Scan through the y_coord array looking for rows to kill.
      for(i=K; i>0; i--){
	j=x_coord[i]-1;
	while(y_coord[j]>=smallest){
	  // This is a situation in which we may kill a row.
	  if(FT[y_coord[j]]==1){
	    deleted++;
	    // We're getting rid of a bunch of primes.
	    // So we could be gearing up for a second or third pass.
	    for(k=x_coord[i-1]; k<x_coord[i]; k++)
	      FT[y_coord[k]]--;
	    shift = x_coord[i]-x_coord[i-1];
	    end-=shift;
	    // Shift the y_coord and exponent arrays.
	    
	    for(k=x_coord[i-1]; k<end; k++){
	      y_coord[k]=y_coord[k+shift];
	      exponent[k]=exponent[k+shift];
	    }
	    
	    // Now we shift the x_coord array.
	    K--;
	    
	    for(k=i; k<=K; k++)
	      x_coord[k]=x_coord[k-1]+(x_coord[k+1]-x_coord[k]);
	    break;
	  }
	  j--;
	} 
      }

      // Go for another Stage 1 pass.
      killme=0;
      for(i=S-1; i>=0; i--){
	if(FT[i]==1){
	  killme++;
	  smallest=i;
	}
      }
    }

    cout<<"Stage one done. Eliminated "<< deleted<<endl;
    

    // Now perform stage 2: 
    // If some prime is present in exactly two rows, we combine the two rows.
    
    killme=0;
    for(i=S-1; i>=0; i--){
      if(FT[i]==2){
	killme++;
	smallest = i;
      }
    }
    cout<<killme<<endl;
    
    if(killme){
      for(i=K; i>0; i--){
	j=x_coord[i]-1;
	while(y_coord[j]>=smallest){
	  // This is a situation in which we may combine two rows.
	  if(FT[y_coord[j]]==2){
	    // Look for the two rows with this same prime.
	    r2=i-1;
	    jj=j;
	    for(k=i-1; k>=0; k--){
	      l=x_coord[k]-1;
	      while(y_coord[l]>=smallest){
		// Found the other row.
		if(y_coord[l]==y_coord[jj]){
		  j=l;
		  r1=k-1;
		  break;
		}
		l--;
	      }
	      if(j==l)
		break;
	    }
	    if(j==jj){
	      j--;
	      continue;
	    }
	    //cout<<"Got rows "<<j<<" "<<jj<<endl;
	    //if(jj==13450){
	    //  for(k=12580; k<x_coord[K]; k++)
	    // 	cout<<y_coord[k]<<" ";
	    //  cout<<endl;
	    //}
	    // Put the first row into the factorization array.
	    l=x_coord[r1+1]-x_coord[r1];
	    for(k=0; k<l; k++){
	      fac[k][0]=y_coord[x_coord[r1]+k];
	      fac[k][1]=exponent[x_coord[r1]+k];
	      //if(jj==13450)
	      //	cout<<fac[k][0]<<" "<<fac[k][1]<<"  ";
	    }
	    //if(jj==13450)
	    //  cout<<endl;
	    j-=x_coord[r1];
	    // Now we shift the y_coord and exponent arrays to make room for the combining.
	    for(k=x_coord[r1]; k<x_coord[r2]-l; k++){
	      y_coord[k]=y_coord[k+l];
	      exponent[k]=exponent[k+l];
	    }

	    // Alter the x_coord array to account for the shift.
	    for(k=r1+1; k<r2; k++){
	      x_coord[k]-=(l+x_coord[k+1]-x_coord[k]);
	    }
	    // Now we go to position r2 and put the two rows in.
	    r1=x_coord[r2]-l;
	    // We have two possibilities:
	    // 1) The primes we're looking at are the same sign.
	    // 2) The primes have opposite signs.
	    // These two "pointers" point to the current location in the respective smooth factorizations.
	    p1=0;
	    p2=x_coord[r2];
	    //if(jj==13450){
	    //  for(k=p2; k<x_coord[r2+1];k++)
	    //	cout<<y_coord[k]<<" "<<(int)exponent[k]<<"  ";
	    //  cout<<endl;
	    // }

	    while((p1<l)||(p2<x_coord[r2+1])){
	      if((p1<l)&&((p2==x_coord[r2+1])||(fac[p1][0]<y_coord[p2]))){
		FT[fac[p1][0]]--;
		y_coord[r1]=fac[p1][0];
		exponent[r1]=fac[p1][1];
		//if(jj==13450)
		//  cout<<"1: "<<y_coord[r1]<<" "<<(int)exponent[r1]<<"  ";
		r1++;
		p1++;
	      }
	      else if((p2<x_coord[r2+1])&&((p1==l)||(fac[p1][0]>y_coord[p2]))){
		FT[y_coord[p2]]--;
		y_coord[r1]=y_coord[p2];
		if(fac[j][1]==exponent[jj])
		  exponent[r1]=-exponent[p2];
		else
		  exponent[r1]=exponent[p2];
		//if(jj==13450)
		//  cout<<"2: "<<y_coord[r1]<<" "<<(int)exponent[r1]<<"  ";
		r1++;
		p2++;
	      }
	      else{
		// In this case we combine two primes.
		if(fac[j][1]==exponent[jj]){
		  if(fac[p1][1]!=exponent[p2]){
		    y_coord[r1]=y_coord[p2];
		    exponent[r1]=fac[p1][0]-exponent[p2];
		    FT[y_coord[p2]]--;
		    r1++;
		    //if(jj==13450)
		    //  cout<<"3: "<<y_coord[r1]<<" "<<(int)exponent[r1]<<"  ";
		  }
		  else
		    FT[y_coord[p2]]-=2;
		}
		else{
		  if(fac[p1][1]==exponent[p2]){
		    y_coord[r1]=y_coord[p2];
		    exponent[r1]=fac[p1][0]+exponent[p2];
		    FT[y_coord[p2]]--;
		    r1++;
		  }
		  else
		    FT[y_coord[p2]]-=2;
		}
		p1++;
		p2++;
	      }
	    }
	    //if(jj==13450){
	    //  for(k=12580; k<x_coord[K]; k++)
	    //		cout<<y_coord[k]<<" ";
	    //  cout<<endl;
	    // }

	    // Done combining the two rows.
	    // Now shift the rest of the array back.
	    l=x_coord[r2+1]-r1;
	    for(k=r2; k<K; k++)
	      x_coord[k]=x_coord[k+1]-l;
	    for(k=r1; k<x_coord[K-1];k++){
	      y_coord[k]=y_coord[k+l];
	      exponent[k]=exponent[k+l];
	    }
	    //if(jj==13450){
	    //  for(k=12580; k<x_coord[K]; k++)
	    //		cout<<y_coord[k]<<" ";
	    //  cout<<endl;
	    //}

	    K--;
	    deleted++;
	  }
	  j--;
	}
      }
    }
    cout<<"Done with Stage2. Eliminated "<<deleted<<endl;
    // This completes a stage 2 pass. At this point killme != 0, so we'll go back up and check if combining stuff
    // eliminated some ideals. It's a big of a longshot, but it doesn't hurt to check.
    killme=0;
    for(i=S-1; i>=0; i--){
      if(FT[i]==1){
	killme++;
	smallest=i;
      }
    }
    cout<<killme<<endl;
  }
  cout<<"Deleted "<<deleted<<" rows and columns from the matrix.\n\n";
}


//calculates x such that x=bA'
// The matrix that is inputted from the sieving. (length)x(length-(ER+2))

vec_ZZ_p Matrix_Vector(int x_c[], int y_c[], char value[], vec_ZZ_p b)
{
  int i = 0, j=0;
  vec_ZZ_p out;
  out.SetLength(K);

  for(i=0; i<K; i++)
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

vec_ZZ_p MatrixTrans_Vector(int x_c[], int y_c[], char value[], vec_ZZ_p b)
{
  int i=0, j;
  vec_ZZ_p out;
  out.SetLength(K-(ER+2));

  for(j=0;j<K; j++)
    {
      for( i = x_c[j]; i < x_c[j+1]; i++)
	{
	  out[y_c[i]] += value[i]*b[j];
	}
    }
  return out;
}

// Use xprime as a dummy vector. Then actually solve system xA=bprime where bprime is an xpA.

vec_ZZ_p Lanczos_Random(int x_c[], int y_c[], char value[])
{

  ZZ_p::init(N/2); // formerly ZZ_p::init(N);

  vec_ZZ_p bprime;
  vec_ZZ_p x;
  vec_ZZ_p xprime;
  vec_ZZ_p out;

  bprime.SetLength(K);
  xprime.SetLength(K);
  x.SetLength(K);
  out.SetLength(K-(ER+2));

  for(int i = 0; i <K; i++)
    {
	xprime[i] = random_ZZ_p();
    }

  bprime = Matrix_Vector(x_c,y_c,value,MatrixTrans_Vector(x_c,y_c,value,xprime));

  x = Lanczos_Inner(x_c,y_c,value,bprime);

  //creating actual solution... assumes x-xprime != 0)
  return (x-xprime);
}

vec_ZZ_p Lanczos_Inner(int x_c[], int y_c[], char value[], vec_ZZ_p b)
{
  vec_ZZ_p w_n, w_m, w_o, v_n, v_m, v_o, x; 
  ZZ_p t_n, t_m, t_o;

  w_o.SetLength(K);
  w_m.SetLength(K);
  v_m.SetLength(K);
  x.SetLength(K);
  
  t_n = 1;
  w_n = b;

  if( IsZero(w_n) )
    {
      return x ;
    }
  else
    {
      v_n = Matrix_Vector(x_c,y_c,value,MatrixTrans_Vector(x_c,y_c,value,w_n));
      t_m = t_n;
      t_n = inv(v_n*w_n);
      if( t_n == 0)
	cerr<< "I'm a big *&^$&^%\n";
      else
	x = (b*w_n)*t_n*w_n;
    }

  int i = 1;
  while( i < K +10)
    {
      if(!(i%KINT))
	cout<<i<<" iterations of the Lanczos loop.\n";
      w_o = VectorCopy(w_m, K);
      w_m = w_n;
      w_n = v_n -(((v_n*v_n)*t_n)*w_m)-(((v_n*v_m)*t_m)*w_o);
      if( IsZero(w_n) )
	return x;
      else
	{
	  v_o = v_m;
	  v_m = v_n;
	  v_n = Matrix_Vector(x_c,y_c,value,MatrixTrans_Vector(x_c,y_c,value,w_n));
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

void getData(){
  FILE *fp;
  char name[6];
  char symbol;
  char symstr[5];
  char number[50];
  char letter;
  ZZ P, Q, H, h; // These guys are temp variables.


  if((fp = fopen("cgdl.ini", "r"))==NULL){
    cout<<"Could not open the initialization file. Quitting.\n\n";
    exit(0);
  }
  symbol=fgetc(fp);
  while(symbol!='P')
    symbol=fgetc(fp);

  while(!feof(fp)){
    fscanf(fp, "%s", name);
    fscanf(fp, "%s", symstr);
    fscanf(fp, "%s", number);
    letter=name[0];
    // Now we check out what we got.
    switch(letter){
    case 'P': 
      P=to_ZZ(number);
      break;
    case 'Q':
      Q=to_ZZ(number);
      D=-P*Q*Q;
      break;
    case 'H': 
      H=to_ZZ(number);
      break;
    case 'h':
      h=to_ZZ(number);
      N=2*H*h;
      break;
    case 'T':
      TOLERR=atoi(number);
      break;
    case 'M':
      M=atoi(number);
      break;
    case 'S':
      if(name[1]=='F')
	S=atoi(number);
      else if(name[1]=='K')
	SKIP=atoi(number);
      else 
	;
      break;
    case 'L':
      LPFAC=atoi(number);
      break;
    case 'E':
      ER=(char)atoi(number);
      break;
    case 'K':
      KINT=atoi(number);
      break;
    case 't':
      if(name[1]=='1')
	t=(char)atoi(number);
      else if(name[1]=='2')
	t2=(char)atoi(number);
      else
	;
      break;
    default:
      break;
    }
  }
  fclose(fp);
}


int main() {
  ZZ p = to_ZZ(19); 
  ZZ x;
  vec_ZZ_p kernel; 

  // Get the data from the cgdl.ini file.
  getData();

  cout <<"\n Discriminant= "<< D << "\n Size of the class group= " << N << "\n\n";

  while(!create_example(p)) 
    p = NextPrime(p+1);
  
  SetSeed(to_ZZ(time(0)));
  x = RandomBnd(N-1); // in the range 0..N-2

  cout << "x: " << x << "\n";
  cout << "g: " << g1 << "\t" << g2 << "\n";
  power(g1, g2, x, h1, h2);
  cout << "h: " << h1 << "\t" << h2 << "\n\n";
  
  for(int i=0; i<MAX_HT; i++)
    HT[i]=NULL;

  begintime = GetTime();

  create_factorbase();

  //These three arrays represent our compressed row storage for our sparse matrix. (About) As optimized as you can get, BABY!
  char exponent[FMAX*(S+2+ER)]; 
  int y_coord[FMAX*(S+2+ER)];
  int x_coord[S+3+ER+10];
  x_coord[0]=0;

  cout<<"Beginning Sieving.\n\n";

  rels_siqs(x_coord, y_coord, exponent);
  sievetime = GetTime()-begintime;
  cout<<"Sieving time: "<<sievetime<<" CPU seconds.\n";
  cout<<"Sieving complete. Solving the matrix.\n\n";

  // We just need to make sure that the last two entries in the vector are both nonzero.
  ER=K-S-2;
  int solution=0;
  while(!solution){
    kernel = Lanczos_Random(x_coord, y_coord, exponent);
    
    cout<<"\nLinear Algebra time: "<<GetTime()-sievetime<<" CPU seconds.\n\n";

    if((kernel[K-2]!=0)&&(kernel[K-1]!=0)){
      if(IsOne(GCD(rep(kernel[K-1]), N))){
	x = (-rep(kernel[K-2])*InvMod(rep(kernel[K-1]), N))%N;
	power(g1, g2, x, h1, h2);
	cout<<"X marks the spot: x= "<<x<<endl;
	cout<<"("<<g1<<", "<<g2<<")^"<<x<<" = ("<<h1<<", "<<h2<<").\n\nWho's your daddy?\n\n";
	
	x = (-rep(kernel[K-2])*InvMod(rep(kernel[K-1]), N/2))%N;
	power(g1, g2, x, h1, h2);
	cout<<"X marks the spot: x= "<<x<<endl;
	cout<<"("<<g1<<", "<<g2<<")^"<<x<<" = ("<<h1<<", "<<h2<<").\n\nWho's your daddy?\n\n";

	solution=1;
      }
      if(IsOne(GCD(rep(kernel[K-1]),N/2))){
	x = (-rep(kernel[K-2])*InvMod(rep(kernel[K-1]), N/2))%N;
        power(g1, g2, x, h1, h2);
        cout<<"X marks the spot: x= "<<x<<endl;
        cout<<"("<<g1<<", "<<g2<<")^"<<x<<" = ("<<h1<<", "<<h2<<").\n\nWho's your daddy?\n\n";

        x = (-rep(kernel[K-2])*InvMod(rep(kernel[K-1]), N/2))%(N/2);
        power(g1, g2, x, h1, h2);
        cout<<"X marks the spot: x= "<<x<<endl;
        cout<<"("<<g1<<", "<<g2<<")^"<<x<<" = ("<<h1<<", "<<h2<<").\n\nWho's your daddy?\n\n";

        solution=1;
      }
      if(!solution)
	cout<<"Could not find a solution: Bad GCD. Trying again.\n\n";
    }
    else{
      cout<<"Could not find a solution.\n\n";
      cout<<"Increase the number of extra relations and try again.\n\n";
      cout<<"Total time: "<<GetTime()-begintime<<" CPU seconds.\n\n";
      exit(0);
    }
  }
  cout<<"Total time: "<<GetTime()-begintime<<" CPU seconds.\n\n";
  return 1;
}
