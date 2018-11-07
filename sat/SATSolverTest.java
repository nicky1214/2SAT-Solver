package com.nicholas.a2d.sat;

/*
import static org.junit.Assert.*;

import org.junit.Test;
*/

import com.nicholas.a2d.sat.env.Environment;
import com.nicholas.a2d.sat.formula.PosLiteral;
import com.nicholas.a2d.sat.formula.*;

import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileWriter;
import java.io.IOException;
import java.io.PrintWriter;
import java.util.ArrayList;
import java.util.Scanner;

public class SATSolverTest {
    Literal a = PosLiteral.make("a");
    Literal b = PosLiteral.make("b");
    Literal c = PosLiteral.make("c");
    Literal na = a.getNegation();
    Literal nb = b.getNegation();
    Literal nc = c.getNegation();

    public static String filePath = "C:\\Users\\Nicholas\\AndroidStudioProjects\\MyApp01\\2d\\src\\main\\java\\com\\nicholas\\a2d\\sampleCNF\\largeSat.cnf";
    public static String filePath2 = "C:\\Users\\Nicholas\\AndroidStudioProjects\\MyApp01\\2d\\src\\main\\java\\com\\nicholas\\a2d\\sampleCNF\\largeUnsat.cnf";
    public static String filePath3 = "C:\\Users\\Nicholas\\AndroidStudioProjects\\MyApp01\\2d\\src\\main\\java\\com\\nicholas\\a2d\\sampleCNF\\s8Sat.cnf";
    public static String filePath4 = "C:\\Users\\Nicholas\\AndroidStudioProjects\\MyApp01\\2d\\src\\main\\java\\com\\nicholas\\a2d\\sampleCNF\\2D_bit3.cnf";
    public static String text_save_location = "C:\\Users\\Nicholas\\AndroidStudioProjects\\MyApp01\\2d\\src\\main\\java\\com\\nicholas\\a2d\\BoolAssignment.txt";


    public static void main(String[] args) throws IOException{
        Formula formula = cnf_to_formula(filePath4); //convert cnf file to formula
        System.out.println("SAT solver starts!!!");
        long started = System.nanoTime();
        Environment e = SATSolver.solve(formula);
        System.out.println(e);
        long time = System.nanoTime();
        long timeTaken = time - started;
        System.out.println("Time:" + timeTaken / 1000000.0 + "ms");
        if (e == null){ //if the result is null, it means that the formula is unsatisfiable
            System.out.println("not satisfiable");
        }
        else { //if the result is not null, formula is satisfiable for some combination
            System.out.println("satisfiable");
            save_to_txt(e); //save results to a text file.
        }
    }
    // Method that converts cnf to formula for SATSolver to solve.
	public static Formula cnf_to_formula(String dir) throws FileNotFoundException{
        File cnf = new File(dir); //read the file
        Scanner scanner = new Scanner (cnf); //scan line by line
        ArrayList<Clause> clauseArrayList = new ArrayList<Clause>();
        while (scanner.hasNextLine()){ //if scanner has a next line, do these:
            String new_line = scanner.nextLine();

            //1st case: line is empty
            if (new_line.trim().equals("")){
                continue; //ignore this line, go to next line
            }

            //2nd case: line is a comment
            else if (new_line.charAt(0) == 'c'){
                continue; //ignore this line, go to next line
            }

            //3rd case: line is problem, check if it is a cnf file
            // p Format Variables Clauses
            else if(new_line.charAt(0)=='p'){
                String[] string_list = new_line.split("\\s+");//split at whitespaces, include any number of space.
                if (!(string_list[1].contains("cnf"))){ //check that it is a cnf file
                    System.out.println("Not cnf file!");
                    break;
                }
            }
            else{ //if it is not an empty line, not comment line, not problem line
                String[] literal_list = new_line.split("\\s+"); //remove spaces and put it into a list of literals
                // start making clause.
                // create array for makeCL
                ArrayList<Literal> literal_array = new ArrayList<Literal>(); //makeCl takes in array, change arraylist to array later.
                for (int i=0;i<literal_list.length;i++){ //iterate across the number of literals in the list
                    Literal currentLiteral=null;
                    //3 cases, negLiteral, PosLiteral, or "0" to end clause
                    if (!(literal_list[i].equals("0"))){ //if literal is not 0,
                        if(literal_list[i].charAt(0) == '-'){ //if literal is -ve
                            currentLiteral = NegLiteral.make(literal_list[i].substring(1)); //create negative literal
                        } else{ //literal is +ve
                            currentLiteral = PosLiteral.make(literal_list[i]); //create positive literal
                        }
                    }
                    //add created literal to the literal_array
                    if (currentLiteral != null){ //if literal is not null
                        literal_array.add(currentLiteral); //add the literal to literal array
                    }
                }

                Literal[] array_1 = literal_array.toArray(new Literal[literal_array.size()]); //convert the ArrayList to Array because makeCL takes in array of literals
                Clause current_Clause = makeCl(array_1); //make the clause from each literal array, returns clause c
                if (current_Clause != null){ //if clause is not null
                    clauseArrayList.add(current_Clause); //add the clause to clause arraylist
                }
            }
        }
        Clause[] array_2 = clauseArrayList.toArray(new Clause[clauseArrayList.size()]);//convert Arraylist to Array because makeFM takes in array
        return makeFm(array_2); //make the formula, returns formula f
    }

    public static void save_to_txt(Environment e) throws IOException{
        FileWriter fileWriter = new FileWriter(text_save_location);//instantiate filewriter
        PrintWriter printWriter = new PrintWriter(fileWriter); // instantiate printwriter

        //extract environment key and values
        String sub_str = e.toString().substring(e.toString().indexOf('[')+1, e.toString().indexOf(']'));
        String[] stringArray = sub_str.split(","+"\\s+");
        for (String string: stringArray){
            String[] s = string.split("->");
            printWriter.println(s[0] + ":"+ s[1]);//s[0] is key(Literal number), s[1] is value(TRUE or FALSE)
        }
        printWriter.close();
    }

    public void testSATSolver1(){
    	// (a v b)
    	Environment e = SATSolver.solve(makeFm(makeCl(a,b))	);
/*
    	assertTrue( "one of the literals should be set to true",
    			Bool.TRUE == e.get(a.getVariable())  
    			|| Bool.TRUE == e.get(b.getVariable())	);
    	
*/    	
    }
    
    
    public void testSATSolver2(){
    	// (~a)
    	Environment e = SATSolver.solve(makeFm(makeCl(na)));
/*
    	assertEquals( Bool.FALSE, e.get(na.getVariable()));
*/    	
    }
    
    private static Formula makeFm(Clause... e) { //Clause... is a Clause array
        Formula f = new Formula();
        for (Clause c : e) {
            f = f.addClause(c);
        }
        return f;
    }
    
    private static Clause makeCl(Literal... e) { //Literal... is a literal array
        Clause c = new Clause();
        for (Literal l : e) {
            c = c.add(l);

        }
        return c;
    }
    
    
    
}