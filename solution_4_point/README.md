# Дедуктивная верификация программы, относящейся к задаче проверки выполнимости булевых формул (SAT)

## Команда
Егоров Анатолий Романович
Еремина Ксения Игоревна

## Построение инварианта цикла:
Инвариант цикла состоит из трех частей:
1. Ограничения на типы входных переменных. Данные ограничения позволяют обеспечить завершение цикла
  ```
 (integerp variable_count )
 (integer-listp implication_graph_transitive_closure )
 
 (< 0 variable_count )
 (= (len implication_graph_transitive_closure )
    (* 2
        (* 2
            (* variable_count variable_count )
        )
    )
)
```
2. Ограничения на переменную-счетчик и тип переменной-счетчика. Эти ограничения обеспечивают условия входа в цикл, продолжения итераций цикла и выхода из цикла. 
```
   (integerp x)
   (<= 0 x)
```
3. Ограничения на переменную-результат. Такие ограничения обеспечивают выполнение постусловия при завершении цикла.
```
   (implies
    (= satisfiable 0)
    (and
        (and
            (=
                (nth
                    (+
                        x
                        variable_count
                        (*
                            x
                            2
                            variable_count
                        )
                    )
                    implication_graph_transitive_closure
                )
                1
            )
            (=
                (nth
                    (+
                        (*
                            x
                            2
                            variable_count
                        )
                        x
                        (*
                            variable_count
                            2
                            variable_count
                        )
                    )
                    implication_graph_transitive_closure
                )
                1
            )
        )
        (< x variable_count )
    )
)
```
