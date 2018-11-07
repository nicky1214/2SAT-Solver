package com.nicholas.a2d.sat;

import com.nicholas.a2d.immutable.EmptyImList;
import com.nicholas.a2d.immutable.ImList;
import com.nicholas.a2d.sat.env.Environment;
import com.nicholas.a2d.sat.formula.*;

/**
 * A simple DPLL SAT solver. See http://en.wikipedia.org/wiki/DPLL_algorithm
 */
public class SATSolver {
    /**
     * Solve the problem using a simple version of DPLL with backtracking and
     * unit propagation. The returned environment binds literals of class
     * bool.Variable rather than the special literals used in clausification of
     * class clausal.Literal, so that clients can more readily use it.
     *
     * @return an environment for which the problem evaluates to Bool.TRUE, or
     * null if no such environment exists.
     */
    public static Environment solve(Formula formula) {
        ImList<Clause> clauses = formula.getClauses(); //get the clauses in the formula and put it in a ImList
        Environment env = new Environment();
        return solve(clauses, env); //recursion
    }

    /**
     * Takes a partial assignment of variables to values, and recursively
     * searches for a complete satisfying assignment.
     *
     * @param clauses formula in conjunctive normal form
     * @param env     assignment of some or all variables in clauses to true or
     *                false values.
     * @return an environment for which all the clauses evaluate to Bool.TRUE,
     * or null if no such environment exists.
     */
    private static Environment solve(ImList<Clause> clauses, Environment env) {
        //if no clauses, formula is trivially satisfiable.
        if (clauses.isEmpty()) {
            return env;
        }
        Clause smallestClause = clauses.first(); //set first clause as smallestclause first,
        for (Clause clause : clauses) { // for each clause in clauses,

            if (clause.isEmpty()) { //check for empty clause. if clause is empty, clause list is unsatisfiable
                return null;
            }

            if (clause.size() < smallestClause.size()) { //Iterate to find the smallest clause. Start from smallest most efficient.
                smallestClause = clause;
            }
        }

        Literal literal = smallestClause.chooseLiteral(); //start with one literal in the smallest clause
        Environment output_env = new Environment();
        Environment n_env = new Environment();
        if (smallestClause.size() == 1){ //if there is only one literal in the clause
            //Bind the variable in the environment
            if (literal instanceof PosLiteral) { //if literal is +ve
                n_env = env.putTrue(literal.getVariable()); //to make it true, put true variable in the environment
            } else {
                n_env = env.putFalse(literal.getVariable());// if -ve, put false variable in the environment
            }
            ImList<Clause> sub1 = new EmptyImList<>();
            sub1 = substitute(clauses, literal); //Substitute literal and reduce the clause
            output_env = solve(sub1, n_env); //recursion


        }
        else{// if smallestClause is >1.
            Environment n_env2 = new Environment();
            //Bind variable in environment
            if (literal instanceof PosLiteral) { //if literal is +ve
                n_env2 = env.putTrue(literal.getVariable());//to make it true, put true variable in the environment
            } else {
                n_env2 = env.putFalse(literal.getVariable());// if -ve, put false variable in the environment
            }
            ImList<Clause> sub2 = new EmptyImList<>();
            sub2 = substitute(clauses,literal); //Substitute literal and reduce the clause
            output_env = solve(sub2,n_env2);//recursion

            if (output_env == null){ //when u set true to all the literals and ur output is null, meaning not satisfiable,
                Environment n_env3 = new Environment();
                if (literal instanceof PosLiteral) { //check if setting the literals to false will satisfy the formula.
                    n_env3 = env.putFalse(literal.getVariable());// to make it false, put false variable in environment when literal is +ve
                } else {
                    n_env3 = env.putTrue(literal.getVariable());//if literal is negliteral, put true variable in environment.
                }
                Literal n_literal = literal.getNegation();//since we are putting the -ve of the literal as the variable in environment,
                ImList<Clause> sub3 = new EmptyImList<>();
                sub3 = substitute(clauses, n_literal); // substitute the negation of the literal and reduce the clause
                output_env = solve(sub3,n_env3); //recursion

            }
        }
        return output_env;
    }

    /**
     * given a clause list and literal, produce a new list resulting from
     * setting that literal to true
     *
     * @param clauses , a list of clauses
     * @param l       , a literal to set to true
     * @return a new list of clauses resulting from setting l to true
     */
    private static ImList<Clause> substitute(ImList<Clause> clauses,
                                             Literal l) {

        ImList<Clause> outputClauses = new EmptyImList<Clause>();

        if (clauses.isEmpty()) { //if theres no clauses
            return outputClauses; //return empty list
        }


        for (Clause clause : clauses) { //for clause in clauses
            if (clause.isEmpty()){ //if clause is empty
                return null;
            }
            else {
                //if clause is not empty and is not null, reduce the clause with literal l
                Clause n_Clause = clause.reduce(l);
                if (n_Clause == null) {//if it is null
                    continue; //move on.
                }
                outputClauses = outputClauses.add(n_Clause); //if the output clause is not null, add it into the outputClause
            }
        }
        return outputClauses;
    }
}