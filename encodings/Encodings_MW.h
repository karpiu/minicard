#ifndef __Encodings_MW_h
#define __Encodings_MW_h

#include <assert.h>
#include <map>
#include <vector>
#include <iostream>
#include "core/SolverTypes.h"

using namespace std;

template <class Solver>
class Encoding_MW {
 private:
  bool make3wiseSel(vector<Lit>& invars, vector<Lit>& outvars, unsigned const k);
  void make3wiseMerge(vector<Lit> const& x, vector<Lit> const& y, vector<Lit> const& z, vector<Lit>& outvars, unsigned int k);
  void make3Comparator(Lit const& x1, Lit const& x2, Lit const& x3, Lit& y1, Lit& y2, Lit& y3);
  inline void make2Comparator(Lit const& a, Lit const& b, Lit& c1, Lit& c2);

  bool makeDirectNetwork(vector<Lit>& invars, vector<Lit>& outvars, unsigned k);
  void DirectCardClauses(vector<Lit>& invars, unsigned start, unsigned pos, unsigned j, vec<Lit>& args);

  Solver* S;

  inline unsigned pow2roundup (unsigned x) {
    if(x == 0) return 0;
    --x;
    x |= x >> 1;
    x |= x >> 2;
    x |= x >> 4;
    x |= x >> 8;
    x |= x >> 16;
    return x+1;
  }
  
 public:
  bool make3wiseSelConstr(const vector<Lit>& lits, unsigned const k, vector<Lit>* outvars);

  Encoding_MW(Solver* _S) : S(_S) { }
  ~Encoding_MW() { }
};

template<class Solver>
bool Encoding_MW<Solver>::make3wiseSelConstr(const vector<Lit>& lits, unsigned const k, vector<Lit>* p_outvars) {
  // input vars
  vector<Lit> invars;
  for (unsigned i = 0 ; i < lits.size() ; i++) {
    invars.push_back(lits[i]);
  }

  //output vars
  vector<Lit> outvars;

  make3wiseSel(invars, outvars, k);

  for (unsigned i = 0 ; i < outvars.size() ; i++) {
    if (outvars[i] == lit_Undef)  continue;
    if (p_outvars) {
      p_outvars->push_back(outvars[i]);
    }
  }

  for (unsigned i = k ; i < outvars.size() ; i++) {
    if(outvars[i] == lit_Undef) continue;
    S->addClause(~outvars[i]);
  }
    
  return true;
}

template<class Solver>
bool Encoding_MW<Solver>::make3wiseSel(vector<Lit>& invars, vector<Lit>& outvars, unsigned const k) {
  assert(outvars.empty());

  unsigned n = invars.size();

  assert(k <= n);
cerr<< "n = " << n << " k = " << k << endl;
for (unsigned i=0; i < n; i++) cerr << toInt(invars[i]) << " "; cerr << endl;

  if((k<=1) || (k==2 && n <= 9) || (k==3 && n <= 6) || (k==4 && n <= 5) || (k==5 && n==5)) {
    makeDirectNetwork(invars, outvars, k < n ? k+1 : k);
    if (k < n) S->addClause(~outvars[k]);

    cerr<< "outvars DIR:" << endl;
    for (unsigned i=0; i < outvars.size(); i++) cerr << toInt(outvars[i]) << " "; cerr << endl;
    
    return true;
  }

  unsigned n1, n2, n3;
  n1 = (n+2)/3;
  n2 = (n+1)/3;
  n3 = n/3;
  
  // split
  vector<Lit> x, y, z;
  for (unsigned i=0; i < n3; i++) {
    x.push_back(lit_Error);
    y.push_back(lit_Error);
    z.push_back(lit_Error);
    make3Comparator(invars[3*i], invars[3*i+1], invars[3*i+2], x[i], y[i], z[i]);
  }

  if (n % 3 == 1) {
    x.push_back(lit_Error);
    x[n1-1] = invars[n-1];
  } else if (n % 3 == 2) {
    x.push_back(lit_Error);
    y.push_back(lit_Error);
    make2Comparator(invars[n-2], invars[n-1], x[n1-1], y[n2-1]);
  }
  
  unsigned k1, k2, k3;
  k1 = min(k, n1);
  k2 = min(k/2, n2);
  k3 = k/3;

  // recursive calls
  vector<Lit> _x, _y, _z;
  make3wiseSel(x, _x, k1);
  make3wiseSel(y, _y, k2);
  make3wiseSel(z, _z, k3);

  // merging
  make3wiseMerge(_x, _y, _z, outvars, k);

cerr<< "outvars MERGE:" << endl;
 for (unsigned i=0; i < outvars.size(); i++) cerr << toInt(outvars[i]) << " "; cerr << endl;
 
  return true;
}

template<class Solver>
void Encoding_MW<Solver>::make3wiseMerge(vector<Lit> const& x, vector<Lit> const& y, vector<Lit> const& z, vector<Lit>& outvars, unsigned int k) {
  unsigned n1, n2, n3;
  n1 = x.size();
  n2 = y.size();
  n3 = z.size();

  vector<Lit> xi_1 (x);
  vector<Lit> yi_1 (y);
  vector<Lit> zi_1 (z);

  unsigned h = pow2roundup(k);
  
  while (h > 1) {
    h = h/2;

    cerr << "h = " << h << endl;
    cerr << "x: "; for (unsigned i=0; i < xi_1.size(); i++) cerr << toInt(xi_1[i]) << " "; cerr << endl;
    cerr << "y: "; for (unsigned i=0; i < yi_1.size(); i++) cerr << toInt(yi_1[i]) << " "; cerr << endl;
    cerr << "z: "; for (unsigned i=0; i < zi_1.size(); i++) cerr << toInt(zi_1[i]) << " "; cerr << endl;
    
    vector<Lit> xi (n1, lit_Error);
    vector<Lit> yi (n2, lit_Error);
    vector<Lit> zi (n3, lit_Error);

    for (unsigned j=0; j<n3; j++) {
      if ((j+h < n2) && (j + 2*h < n1)) {
        make3Comparator(xi_1[j+2*h], yi_1[j+h], zi_1[j], zi[j], yi[j+h], xi[j+2*h]);
      } else if (j + h < n2) {
        make2Comparator(yi_1[j+h], zi_1[j], zi[j], yi[j+h]);
      } else if (j + 2*h < n1) {
	cerr << "    " << toInt(xi_1[j+2*h]) << " " << toInt(zi_1[j]) << " " << toInt(zi[j]) << " " << toInt(xi[j+2*h]) << endl;
	make2Comparator(xi_1[j+2*h], zi_1[j], zi[j], xi[j+2*h]);
	cerr << "    " << toInt(xi_1[j+2*h]) << " " << toInt(zi_1[j]) << " " << toInt(zi[j]) << " " << toInt(xi[j+2*h]) << endl;
      } else {
        zi[j] = zi_1[j];
      }
    }
    for (unsigned j=0; j < min(n2,h); j++) {
      if (j + h < n1) {
	make2Comparator(xi_1[j+h], yi_1[j], yi[j], xi[j+h]);
      } else {
	yi[j] = yi_1[j];
      }
    }
    for (unsigned j=0; j<min(n1,h); j++) {
      xi[j] = xi_1[j];
    }
    for (unsigned j=0; j < min(n1,min(n2+h,n3+2*h)); j++) xi_1[j] = xi[j];
    for (unsigned j=0; j < min(n2,n3+h); j++) yi_1[j] = yi[j];
    for (unsigned j=0; j < n3; j++) zi_1[j] = zi[j];
  }

  cerr << "AFTER WHILE" <<  endl;
  cerr << "x: "; for (unsigned i=0; i < xi_1.size(); i++) cerr << toInt(xi_1[i]) << " "; cerr << endl;
  cerr << "y: "; for (unsigned i=0; i < yi_1.size(); i++) cerr << toInt(yi_1[i]) << " "; cerr << endl;
  cerr << "z: "; for (unsigned i=0; i < zi_1.size(); i++) cerr << toInt(zi_1[i]) << " "; cerr << endl;
    
  
  vector<Lit> xi (n1, lit_Error);
  vector<Lit> zi (n3, lit_Error);
  for (unsigned j=1; j<min(n1,n3+1); j++) {
    make2Comparator(xi_1[j], zi_1[j-1], zi[j-1], xi[j]);
  }
  for (unsigned j=1; j < min(n1,n3+1); j++) xi_1[j] = x[j];
  for (unsigned j=0; j < min(n1-1,n3); j++) zi_1[j] = zi[j];

  // copy k elements to outvars
  for (unsigned j=0; j<k; j++)
    outvars.push_back(j % 3 == 0 ? xi_1[j/3] : (j % 3 == 1 ? yi_1[j/3] : zi_1[j/3]));

  for (unsigned j=(k+2)/3; j < n1; j++) 
     if (xi_1[j] != lit_Undef) S->addClause(~xi_1[j]);
  for (unsigned j=(k+1)/3; j < n2; j++) 
     if (yi_1[j] != lit_Undef) S->addClause(~yi_1[j]);
}

template<class Solver>
void Encoding_MW<Solver>::make3Comparator(Lit const& x1, Lit const& x2, Lit const& x3, Lit& y1, Lit& y2, Lit& y3) {
  // if one of our inputs is a constant false, we use normal comparator on the other two
  if (x1 == lit_Undef) {
    y3 = x1;
    make2Comparator(x2, x3, y1, y2);
    return;
  }
  if (x2 == lit_Undef) {
    y3 = x2;
    make2Comparator(x1, x3, y1, y2);
    return;
  }
  if (x3 == lit_Undef) {
    y3 = x3;
    make2Comparator(x1, x2, y1, y2);
    return;
  }

  // otherwise we create new variables
  S->newVar();
  y1 = mkLit((unsigned int)S->nVars()-1);
  S->newVar();
  y2 = mkLit((unsigned int)S->nVars()-1);
  S->newVar();
  y3 = mkLit((unsigned int)S->nVars()-1);
  
  // 7-clause 3-comparator for AtMost constraint

  vec<Lit> args; // reused
  
  // x1 -> y1
  args.push(~x1);
  args.push(y1);
  S->addClause(args);
  
  // x2 -> y1
  args[0] = ~x2;
  // Already there: args[1] = y1;
  S->addClause(args);
  
  // x3 -> y1
  args[0] = ~x3;
  // Already there: args[1] = y1;
  S->addClause(args);
  
  // x1 ^ x2 -> y2
  args[0] = ~x1;
  args[1] = ~x2;
  args.push(y2);
  S->addClause(args);
  
  // x1 ^ x3 -> y2
  // Already there: args[0] = ~x1;
  args[1] = ~x3;
  // Already there: args[2] = y2;
  S->addClause(args);
  
  // x2 ^ x3 -> y2
  args[0] = ~x2;
  // Already there: args[1] = ~x3;
  // Already there: args[2] = y2;
  S->addClause(args);
  
  // x1 ^ x2 ^ x3 -> y3
  args[0] = ~x1;
  args[1] = ~x2;
  args[2] = ~x3;
  args.push(y3);
  S->addClause(args);
}

template<class Solver>
inline void Encoding_MW<Solver>::make2Comparator(Lit const& a, Lit const& b, Lit& c1, Lit& c2) {
  // if one of our inputs is a constant false, we can simplify greatly
  if (a == lit_Undef) {
    c1 = b;
    c2 = a;
    return;
  }
  if (b == lit_Undef) {
    c1 = a;
    c2 = b;
    return;
  } 

  // otherwise, we need new variables
  S->newVar();
  c1 = mkLit((unsigned int)S->nVars()-1);
  S->newVar();
  c2 = mkLit((unsigned int)S->nVars()-1);

  vec<Lit> args; // reused

  // 3-clause comparator,
  // because AtMosts only need implications from 0 on the outputs to 0 on the inputs

  // a -> c1
  args.push(~a);
  args.push(c1);
  S->addClause(args);
  
  // b -> c1
  args[0] = ~b;
  // Already there: args[1] = c1;
  S->addClause(args);

  // !c2 -> !a v !b'
  args[0] = ~a;
  args[1] = ~b;
  args.push(c2);
  S->addClause(args);
}

// Direct Sorting and Direct m-Cardinality Natwork
template<class Solver>
bool Encoding_MW<Solver>::makeDirectNetwork(vector<Lit>& invars, vector<Lit>& outvars, unsigned k) {
  // as described in CP'2013 paper: Abio, Nieuwenhuis, Oliveras and Rodriguez-Carbonell:
  // "A Parametric Approach for Smaller and Better Encodings of Cardinality Constraints", page 11
  // k is the desired size of sorted output

  // outvars should be created in this function
  assert(outvars.empty());
  unsigned n = invars.size();
  
  if (k == 0 || k > n) k = n;
cerr<< "DIR: n = " << n << " k = " << k << endl;

  for (unsigned i=0 ; i < k ; i++) {
    S->newVar();
    Lit ret = mkLit((unsigned)S->nVars()-1);
    outvars.push_back(ret);
  }
  for (unsigned j=1 ; j <= k ; j++) {
    vec<Lit> args;
    for (unsigned i=0 ; i < j; i++)
      args.push(lit_Error);
    args.push(outvars[j-1]);
    DirectCardClauses(invars, 0, 0, j, args);
  }
  return true;
}
  
template<class Solver>
void Encoding_MW<Solver>::DirectCardClauses(vector<Lit>& invars, unsigned start, unsigned pos, unsigned j, vec<Lit>& args) {
  unsigned n = invars.size();
  if (pos == j) {
    S->addClause(args);
  } else {
    for (unsigned i = start ; i <= n - (j - pos) ; i++) {
      args[pos] = ~invars[i];
      DirectCardClauses(invars, i+1, pos+1, j, args);
    }
  }  
}

#endif // __Encodings_MW_h
