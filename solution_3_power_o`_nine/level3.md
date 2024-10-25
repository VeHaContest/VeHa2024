## На третьем уровне нам требуется реализовать уровень 2 для приложения на PTX. 
Само работающее решение мы не успели сделать, однако, чтобы показать, что мы разобрались в теме, приведём ниже алгоритм работы для уровня 3. 

### Для начала рассмотрим поподробнее маски:
В архитектуре GPU с моделью исполнения SIMT все потоки внутри ворпа должны выполнять одну и ту же инструкцию одновременно. Однако при наличии условных операторов разные потоки могут следовать разным ветвям исполнения. Чтобы сохранить одновременное выполнение инструкций в варпе, используется механизм масок и предикатного исполнения.

**Что такое маски в PTX**

В PTX маски используются для управления исполнением инструкций на уровне потоков внутри варпы. Что можно выделить:

- **Предикатные регистры**: PTX предоставляет предикатные регистры `%p`, которые могут содержать булевы значения (`true` или `false`). Они используются для управления условным исполнением инструкций.

- **Маска активных потоков**: Ворп имеет маску активных потоков, где каждый бит соответствует потоку в ворпе. Если бит установлен, то соответствующий поток активен и будет выполнять текущую инструкцию.

- **Стек масок**: Для поддержки вложенных ветвлений используется стек масок. При входе в условное ветвление текущая маска сохраняется в стек, и создается новая маска, отражающая какие потоки должны выполнить ветвь. При выходе из ветвления маска восстанавливается из стека.

**Как работают маски при ветвлениях**

1. **Выставление предиката**: При выполнении условного оператора сначала вычисляется предикат для каждого потока.

   ```ptx
   setp.eq.s32 %p1, %r1, 0;
   ```

2. **Обновление маски**: На основе предиката обновляется маска активных потоков.

   - **Вход в ветвление**: Маска сохраняется в стек, и создается новая маска для ветви `if`.

     ```ptx
     @!%p1 bra ELSE_LABEL; // Если предикат ложен, перейти к ELSE
     ```

     Здесь символ `@` указывает, что инструкция выполняется только для потоков, у которых предикат истинен.

3. **Выполнение инструкций внутри ветви**: Инструкции внутри ветви выполняются только активными потоками согласно новой маске.

4. **Выход из ветвления**: Маска восстанавливается из стека, объединяя потоки для продолжения совместного исполнения.

_как выглядить маска:_
при инициализации - 11111111111111111111111111111111
если например половина варп исполняет инструкцию (ушла по if), а остальная простаивает: 1111111111111111000000000000000

## Теперь к моделированию:  

### Шаг 1:
- **Определение процессов**: каждый поток моделируем как отдельный процесс (`proctype`), исполняющий последовательность инструкций PTX.
- **Регистры и переменные**: регистры PTX (`%r`, `%p`) отображаются на переменные в Promela.
  
  Пример:
  ```promela
  int r20, r18, r15;
  ```

- **Инструкции PTX**: каждая инструкция PTX транслируется в соответствующее действие в Promela.

  Пример:
  ```ptx
  add.s32 %r20, %r18, %r15;
  ```
  Соответствует:
  ```promela
  r20 = r18 + r15;
  ```

### Шаг 2:  
- **Условные переходы и предикаты**: использование конструкций `if..fi` для моделирования условных инструкций и предикатных регистров.

  Пример:
  ```ptx
  setp.gt.s32 %p1, %r4, 0;
  @%p1 bra BB0_2;
  ```
  Соответствует:
  ```promela
  p1 = (r4 > 0);
  if
  :: p1 -> goto BB0_2;
  :: else -> skip;
  fi;
  ```

**Шаг 3: Реализация работы с масками**

Для моделирования управления ветвлениями с помощью масок и предикатного выполнения:

- **Маска варпы**: для каждой варпы определяем массив булевых значений `active[N]`, где `N` — размер варпы (32 потока). Этот массив отражает активность потоков.

  ```promela
  bool active[warp_size];
  ```

- **Стек масок**: для поддержки вложенных ветвлений используется стек масок.

  ```promela
  bool mask_stack[MAX_DEPTH][warp_size];
  int sp = 0; // это указатель стека
  ```

- **Обновление масок при ветвлениях**:
  - При входе в ветвление сохраняем текущую маску в стек и обновляем ее в соответствии с результатом предиката.
  - При завершении ветвления восстанавливаем маску из стека.

- **Выполнение инструкций с учетом маски**: при выполнении каждой инструкции проверяем, активен ли поток.
  ```promela
  for (i : 0 .. warp_size) {
    if
    :: active[i] -> 
        // выполнение инструкции потоком i
    :: else -> skip
    fi;
  }
  ```

## Рассмотрим пример моделирования инструкции с использованием маски в Promela.

PTX код:

```ptx
setp.eq.s32 %p2, %r35, 0;
selp.b32 %r36, %r34, 0, %p2;
```

```Promela
// Обновление предиката для каждого потока
i = 0;
do
:: i < warp_size -> 
    if
    :: active[i] -> p2[i] = (r35[i] == 0)
    :: else -> skip
    fi;
    i = i + 1;
:: else -> break
od;

// Выбор значения на основе предиката
i = 0;
do
:: i < warp_size -> 
    if
    :: active[i] ->
        if
        :: p2[i] -> r36[i] = r34[i]
        :: else -> r36[i] = 0
        fi
    :: else -> skip
    fi;
    i = i + 1;
:: else -> break
od;
```
