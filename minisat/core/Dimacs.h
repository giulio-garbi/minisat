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
static void parse_DIMACS_main(B& in, Solver& S, B& extra_in, bool strictp = false) {
    vec<Lit> lits;
    int vars    = 0;
    int clauses = 0;
    int cnt     = 0;
    if(extra_in.valid()){
        skipWhitespace(extra_in);
        S.nGuards = parseInt(extra_in);
        if(S.nGuards) {
            S.toVar = (Var *) malloc(S.nGuards * sizeof(Var));
            S.toCl = (CRef *) malloc(S.nGuards * sizeof(CRef));
            S.fromGuard = (int *) malloc(S.nGuards * sizeof(int));
            S.toGuard = (int *) malloc(S.nGuards * sizeof(int));

            vec<int> guard_open;
            vec<uint> nchild;
            skipWhitespace(extra_in);
            uint next_guard = 0;
            guard_open.push(next_guard);
            nchild.push(parseInt(extra_in));
            S.fromGuard[0] = 0;
            S.toGuard[0] = std::max(0u, S.nGuards-2);
            for(uint guard_cnt = 0; guard_cnt < S.nGuards-1; guard_cnt++){
                S.fromGuard[guard_cnt+1] = guard_cnt;
                nchild.last()--;
                guard_open.push(guard_cnt+1);
                skipWhitespace(extra_in);
                nchild.push(parseInt(extra_in));
                while (nchild.size() && nchild.last() == 0){
                    S.toGuard[guard_open.last()] = guard_cnt;
                    guard_open.pop();
                    nchild.pop();
                }
            }
            while (nchild.size() && nchild.last() == 0){
                S.toGuard[guard_open.last()] = std::max(0u, S.nGuards-2);
                guard_open.pop();
                nchild.pop();
            }
            assert(!nchild.size());
            skipWhitespace(extra_in);
            S.toVar[0] = S.nGuards + parseInt(extra_in) - 1;
            for(uint guard_cnt = 0; guard_cnt < S.nGuards-1; guard_cnt++){
                skipWhitespace(extra_in);
                S.toVar[guard_cnt+1] = S.toVar[guard_cnt] + parseInt(extra_in);
            }
        }
    }
    CRef cur_clause = 0;
    uint next_guard = 0;
    uint remaining_clauses = 0;
    for (;;){
        skipWhitespace(in);
        if (*in == EOF) {
            while(remaining_clauses == 0){
                {
                    skipWhitespace(extra_in);
                    if(*extra_in == EOF)
                        break;
                    remaining_clauses = parseInt(extra_in);
                    if (next_guard == 0) {
                    } else {
                        S.toCl[next_guard-1] = cur_clause;
                    }
                    next_guard++;
                }
            }
            assert(remaining_clauses == 0);
            assert(next_guard == S.nGuards);
            S.toCl[next_guard-1] = cur_clause;
            break; }
        else if (*in == 'p'){
            if (eagerMatch(in, "p cnf")){
                vars    = parseInt(in);
                clauses = parseInt(in);
                // SATRACE'06 hack
                // if (clauses > 4000000)
                //     S.eliminate(true);
            }else{
                printf("PARSE ERROR! Unexpected char: %c\n", *in), exit(3);
            }
        } else if (*in == 'c' || *in == 'p')
            skipLine(in);
        else {
            while(remaining_clauses == 0){
                if(next_guard == S.nGuards){
                    S.toCl[next_guard-1] = cur_clause;
                } else {
                    skipWhitespace(extra_in);
                    remaining_clauses = parseInt(extra_in);
                    if (next_guard == 0) {
                    } else {
                        S.toCl[next_guard-1] = cur_clause;
                    }
                    next_guard++;
                }
            }
            cnt++;
            readClause(in, S, lits);
            S.addClause_(lits);
            cur_clause = S.lastClause();
            printf("c clause # %d -> CRef %d\n", cnt, cur_clause);
            remaining_clauses--;
        }
    }
    printf("c final toCl array: ");
    for(int i=0; i<S.nGuards; i++) printf("%d%c", S.toCl[i], (i==S.nGuards-1?'\n':' '));
    printf("c final toVar array: ");
    for(int i=0; i<S.nGuards; i++) printf("%d%c", S.toVar[i], (i==S.nGuards-1?'\n':' '));
    if (strictp && cnt != clauses)
        printf("PARSE ERROR! DIMACS header mismatch: wrong number of clauses\n");
}

// Inserts problem into solver.
//
template<class Solver>
static void parse_DIMACS(gzFile input_stream, Solver& S, gzFile extra_stream, bool strictp = false) {
    StreamBuffer in(input_stream);
    StreamBuffer extra(extra_stream);
    parse_DIMACS_main(in, S, extra, strictp); }

//=================================================================================================
}

#endif
