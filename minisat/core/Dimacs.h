/****************************************************************************************[Dimacs.h]
Copyright (c) 2003-2006, Niklas Een, Niklas Sorensson
Copyright (c) 2007-2010, Niklas Sorensson

Permission is hereby granted, free of charge, to any person obtaining a copy of this software and
associated documentation files (the "Software"), to deal in the Software without restriction,
including without limitation the rights to use, copy, modify, merge, publish, distribute,
sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all copies or
substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT
NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM,
DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT
OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
**************************************************************************************************/

#ifndef Minisat_Dimacs_h
#define Minisat_Dimacs_h

#include <stdio.h>

#include "minisat/utils/ParseUtils.h"
#include "minisat/core/SolverTypes.h"

namespace Minisat {

//=================================================================================================
// DIMACS Parser:

template<class B, class Solver>
static void readClause(B& in, Solver& S, vec<Lit>& lits) {
    int     parsed_lit, var;
    lits.clear();
    for (;;){
        parsed_lit = parseInt(in);
        if (parsed_lit == 0) break;
        var = abs(parsed_lit)-1;
        while (var >= S.nVars()) S.newVar();
        lits.push( (parsed_lit > 0) ? mkLit(var) : ~mkLit(var) );
    }
}

template<class B, class Solver>
static void parse_DIMACS_main(B& in, FILE* extra_file, Solver& S, bool strictp = false) {
    vec<Lit> lits;
    int vars    = 0;
    int clauses = 0;
    int cnt     = 0;
    int nguards;
    int clauses_remaining_in_this_guard;
    for (;;){
        skipWhitespace(in);
        if (*in == EOF) break;
        else if (*in == 'p'){
            if (eagerMatch(in, "p cnf")){
                vars    = parseInt(in);
                clauses = parseInt(in);
                if(extra_file){
                    fscanf(extra_file, "%d", &nguards);
                    // compute the guard tree
                    S.parent_guard.push(0); //true guard: no parent
                    vec<int> guard_idx; // stack with the guards that have undiscovered children
                    vec<int> remaining_children; // # undiscovered children for each element in the stack
                    int nch; // temp var for scanf
                    guard_idx.push(0);
                    fscanf(extra_file, "%d", &nch);
                    remaining_children.push(nch);
                    for(int i = 1; i<nguards; i++){
                        while (remaining_children.last() == 0) {
                            guard_idx.pop();
                            remaining_children.pop();
                        }
                        remaining_children.last()--;
                        S.parent_guard.push(guard_idx.last());
                        guard_idx.push(i);
                        fscanf(extra_file, "%d", &nch);
                        remaining_children.push(nch);
                    }
                    while (remaining_children.size()) {
                        assert(remaining_children.last() == 0);
                        guard_idx.pop();
                        remaining_children.pop();
                    }
                    int cur_last_var_guard = nguards-2; //first guard is TRUE -> no var for it; then nguards-1 guards; hence the last one has index (nguards-1)
                    int nvars; // temp var for scanf
                    for(int i = 0; i<nguards; i++){
                        fscanf(extra_file, "%d", &nvars); //number of vars protected directly by this guard
                        cur_last_var_guard += nvars;
                        S.last_var_guard.push(cur_last_var_guard);
                    }
                    assert(S.last_var_guard.last() == vars-1);
                    fscanf(extra_file, "%d", &clauses_remaining_in_this_guard);
                } else {
                    nguards = 1;
                    S.parent_guard.push(0); //true guard: no parent
                    S.last_var_guard.push(vars-1); //all vars under TRUE guard
                    clauses_remaining_in_this_guard = clauses;
                }
                // SATRACE'06 hack
                // if (clauses > 4000000)
                //     S.eliminate(true);
            }else{
                printf("PARSE ERROR! Unexpected char: %c\n", *in), exit(3);
            }
        } else if (*in == 'c' || *in == 'p')
            skipLine(in);
        else{
            cnt++;
            readClause(in, S, lits);
            S.addClause_(lits);
            clauses_remaining_in_this_guard--;
            while (clauses_remaining_in_this_guard == 0){
                S.last_cref_guard.push(S.clauses.last());
                if(S.last_cref_guard.size() < nguards)
                    fscanf(extra_file, "%d", &clauses_remaining_in_this_guard);
                else
                    clauses_remaining_in_this_guard = -1;
            }
        }
    }
    assert(clauses_remaining_in_this_guard == -1);
    assert(S.last_cref_guard.size() == nguards);
    if (strictp && cnt != clauses)
        printf("PARSE ERROR! DIMACS header mismatch: wrong number of clauses\n");
}

// Inserts problem into solver.
//
template<class Solver>
static void parse_DIMACS(gzFile input_stream, FILE* extra_file, Solver& S, bool strictp = false) {
    StreamBuffer in(input_stream);
    parse_DIMACS_main(in, extra_file, S, strictp); }

//=================================================================================================
}

#endif
