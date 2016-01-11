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
    bool make3Comparator(Lit const& x1, Lit const& x2, Lit const& x3, Lit& y1, Lit& y2, Lit& y3);
    void _3wiseSplit(vector<Lit> const& in, vector<Lit>& out1, vector<Lit>& out2, vector<Lit>& out3);

    Solver* S;

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

    unsigned int n = invars.size();

    if((k==1) || (k==2 && n <= 9) || (k==3 && n <= 6) || (k==4 && n <= 5) || (k==5 && n==5)) {
      //ANORC13_DirectCard(invars, k, outvars, true);
      return true;
    }

    if (k >= n) {
      //makeSortNet(invars, outvars); // temporary use of existing odd-even sorting network
      return true;
    }

    // split
    vector<Lit> out1, out2, out3;
    _3wiseSplit(invars, out1, out2, out3);

    // recursive calls
    vector<Lit> sorted1, sorted2, sorted3;
    make3wiseSel(out1, sorted1, k);
    make3wiseSel(out2, sorted2, k>>1);
    make3wiseSel(out3, sorted3, k>>2);

    // merging

    return true;
  }

  // Pairwise Splitting
  template<class Solver>
  void Encoding_MW<Solver>::_3wiseSplit(vector<Lit> const& in, vector<Lit>& out1, vector<Lit>& out2, vector<Lit>& out3) {
    // out1/2/3 should be created in this function
    assert(out1.empty());
    assert(out2.empty());
    assert(out3.empty());
  }
  
  template<class Solver>
  bool Encoding_MW<Solver>::make3Comparator(Lit const& x1, Lit const& x2, Lit const& x3, Lit& y1, Lit& y2, Lit& y3) {
    return true;
  }

#endif // __Encodings_MW_h
