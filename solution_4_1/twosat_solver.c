/*
(and
    (integerp
        variable_count
    )
    (<
        0
        variable_count
    )
    (integer-listp
        implication_graph_transitive_closure
    )
    (=
        (len
            implication_graph_transitive_closure
        )
        (*
            4
            (*
                variable_count
                variable_count
            )
        )
    )
)
*/
int twosat_solver(int variable_count, int implication_graph_transitive_closure[])
{
    int x = 0;
    int satisfiable = 1;
    /*
    (and
        (integerp variable_count)
        (< 0 variable_count)
        (integer-listp implication_graph_transitive_closure)
        (=
            (len implication_graph_transitive_closure)
            (* 4 (* variable_count variable_count))
        )
        (integerp x)
        (<= 0 x)
        (implies
            (= satisfiable 0)
            (and
                (< x variable_count)
                (=
                    (nth
                        (+ (* x (* variable_count 2)) (+ x variable_count))
                        implication_graph_transitive_closure
                    )
                    1
                )
                (=
                    (nth
                        (+ (* (+ x variable_count) (* variable_count 2)) x)
                        implication_graph_transitive_closure
                    )
                    1
                )
            )
        )
    )
    */
    while (x < variable_count && satisfiable == 1)
    {
        if (implication_graph_transitive_closure[x + variable_count + x * 2 * variable_count] == 1 &&
            implication_graph_transitive_closure[x * 2 * variable_count + x + variable_count * 2 * variable_count] == 1)
        {
            satisfiable = 0;
        }
        else
        {
            x++;
        }
    }
    return satisfiable;
}
/*
(implies
    (=
        satisfiable
        0
    )
    (not
        (twosat-solver
            (boolean-variable-values
                variable_count
                nil
            )
            variable_count
            implication_graph_transitive_closure
        )
    )
)
*/
