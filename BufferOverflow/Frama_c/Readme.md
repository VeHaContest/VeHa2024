# Решение задачи "Верификация функции проверки прав доступа на Frama-C"

## Команда BufferOverflow

- Данило Анатоли Меркадо Оудалова
- Роберто Юниор Домингес Молина
- Жоел Андрес Бонилья Тельес

## Решение
### Детали, которые следует учитывать
Поскольку проверка и тестирование этого кода было выполнено на mac m1, оно полностью выполняется с помощью терминала с помощью следующих команд
```
frama-c -wp -wp-rte -debug 1  with_sol.c -then -report
```
### Анализ проблемы

Первым этапом было создание различных предикатов, чтобы иметь возможность представлять поведение программы

```C
/*@ axiomatic Block {
        logic unsigned int integrityCategories(PDPL_T *l) = l->ilev;
        
        predicate currentIsFileSystemRoot =
            current->process->fsuid == 0;
        
        logic PDPL_T *getSecurityLabel(struct task *task) =
            task->l;

        predicate isPublicFile(struct file *f) =
            f->f_inode->i_flags & SHIFT;
        
        predicate isGTImportant(unsigned int cmd) =
            cmd > IMPORTANT;

        predicate isLTExotic(unsigned int cmd) =
            cmd < EXOTIC;

        predicate isMaxILev(struct task *task) =
            getSecurityLabel(task)->ilev == max_ilev;

        predicate valid_result_check_permission(int result) =
            result == 0 || result == -NO_PERM || result == -NO_ILEV || result == -NO_LABEL;

        predicate valid_cmd(unsigned int cmd) = 
            cmd >= 0 && cmd <= 0xFFFFFFFF;
                       
        predicate valid_mode(unsigned int mode) =
            mode >= 0 && mode <= 0xFFFFFFFF;

        predicate valid_flags(unsigned int flags) = 
            flags >= 0 && flags <= 0xFFFFFFFF;

        predicate valid_inode(struct inode *i) =
            \valid(i) && valid_mode(i->i_mode) && valid_flags(i->i_flags);

        predicate valid_file(struct file *f) =
            \valid(f) && \valid(f->f_inode) && valid_inode(f->f_inode) && f->f_mode >= 0;
    }
*/
```

Как только это было сделано, поведение первой функции начало структурироваться, но возникла проблема, эта функция должна была иметь возможность возвращать: MAY_READ || MAY_WRITE || (MAY_WRITE|MAY_READ)

Но функция также возвращала 0, когда файл был общедоступным, и это было неправильно;

Проявляются следующие типы поведения:
- Файл является общедоступным
- Команда важнее, чем важна
- команда меньше экзотической
- команда находится в списке команд
- общий

```
/*@ 
    requires valid_file(file);
    requires valid_cmd(cmd);
    assigns \nothing;
    behavior file_is_public:
        assumes isPublicFile(file);
        ensures \result == (MAY_WRITE | MAY_READ);
    behavior cmd_gt_important:
        assumes !isPublicFile(file);
        assumes isGTImportant(cmd);
        ensures \result == MAY_WRITE;
    behavior cmd_lt_exotic:
        assumes !isPublicFile(file);
        assumes isLTExotic(cmd);
        ensures \result == MAY_READ;
    behavior cmd_equal_event:
        assumes !isPublicFile(file);
        assumes !isGTImportant(cmd);
        assumes !isLTExotic(cmd);
        assumes (!\forall int i; 0 <= i < 3 ==> event_numbers[i][0] != cmd);
        ensures \exists int j; 0 <= j < 3 && event_numbers[j][0] == cmd ==> event_numbers[j][1] == \result;
    behavior Default:
        assumes !isPublicFile(file);
        assumes !isGTImportant(cmd);
        assumes !isLTExotic(cmd);
        assumes \forall int i; 0 <= i < 3 ==> event_numbers[i][0] != cmd;
        ensures \result == (MAY_WRITE | MAY_READ);
    complete behaviors;
    disjoint behaviors;
    
*/
```

В случае функции проверки разрешений возникают следующие проблемы:

Он не возвращает -NO_LABEL в случае, если не может найти метку.
вам нужно добавить этот фрагмент кода
```C
if (!(sl)) {
    return -NO_LABEL;
}
```
Наконец, чтобы получить более четкие результаты и, кроме того, избежать двусмысленностей, предлагается изменить этот код:
```C
if (current->process->fsuid == 0)
    if ((mask_final & MAY_WRITE)){
        return 0;
    }

if (!(current->process->fsuid == 0))
    if ((mask_final & MAY_READ)){
        return 0;
    }
////////////////////////////////////////////
// С Этим другим
// Суперпользователь по определению имеет полный доступ к системе.
if (current->process->fsuid == 0){
        return 0;
    }
    if (!(current->process->fsuid == 0))
        if ((mask_final & MAY_READ)){
            return 0;
        }
```

Таким образом, мы смогли собрать воедино различные варианты поведения, которые могут возникнуть в нашей функции, разделив их на простые для понимания названия

```
/*@
    requires valid_file(file);
    requires valid_cmd(cmd); 
    requires \valid(current);
    requires \valid(current->l) || current->l == \null;
    requires \valid(current->process);
    assigns \nothing;
    ensures valid_result_check_permission(\result);
    behavior no_label:
        assumes getSecurityLabel(current) == \null;
        ensures \result == -NO_LABEL;
    behavior no_max_integrity_level:
        assumes getSecurityLabel(current) != \null;
		assumes !isMaxILev(current);
		ensures \result == -NO_ILEV;
    behavior is_root_can_read_and_write:
        assumes getSecurityLabel(current) != \null;
        assumes isMaxILev(current);
        assumes currentIsFileSystemRoot;
        ensures \result == 0;
    behavior is_no_root_can_read_public:
        assumes getSecurityLabel(current) != \null;
        assumes isMaxILev(current);
        assumes !currentIsFileSystemRoot;
        assumes isPublicFile(file);
        ensures \result == 0;
    behavior is_no_root_can_read_exotic:
        assumes getSecurityLabel(current) != \null;
        assumes isMaxILev(current);
        assumes !currentIsFileSystemRoot;
        assumes !isPublicFile(file);
        assumes isLTExotic(cmd);
        assumes !isGTImportant(cmd);
        ensures \result == 0;
    behavior is_no_root_cant_read_important:
        assumes getSecurityLabel(current) != \null;
        assumes isMaxILev(current);
        assumes !currentIsFileSystemRoot;
        assumes !isPublicFile(file);
        assumes !isLTExotic(cmd);
        assumes isGTImportant(cmd);
        ensures \result == -NO_PERM;
    behavior is_no_root_cant_read_cmd_event:
        assumes getSecurityLabel(current) != \null;
        assumes isMaxILev(current);
        assumes !currentIsFileSystemRoot;
        assumes !isPublicFile(file);
        assumes !isLTExotic(cmd);
        assumes !isGTImportant(cmd);
        assumes (!\forall int i; 0 <= i < 3 ==> event_numbers[i][0] != cmd);
        ensures \exists int j; 0 <= j < 3 && event_numbers[j][0] == cmd ==> \result == -NO_PERM || \result == 0;
    behavior Default:
        assumes getSecurityLabel(current) != \null;
        assumes isMaxILev(current);
        assumes !currentIsFileSystemRoot;
        assumes !isPublicFile(file);
        assumes !isLTExotic(cmd);
        assumes !isGTImportant(cmd);
        assumes \forall int i; 0 <= i < 3 ==> event_numbers[i][0] != cmd;
        ensures \result == 0;
    complete behaviors;
    disjoint behaviors;
```

Наши неисправленные функции остались следующими:


```C
static int compute_mask(struct file *file, unsigned int cmd)
{
    struct inode *inode = file_inode(file);
    int mask = 0;
    int i = 0;
    // Количество событий в массиве event_numbers
    unsigned long size_array = (sizeof(event_numbers) / sizeof((event_numbers)[0]));

    // Проверяем, является ли файл публичным.
    // Если да, то доступ разрешен сразу
    if (inode->i_flags & SHIFT)
        return 0;

    if (cmd > IMPORTANT) {
        return MAY_WRITE;
    }

    if (cmd < EXOTIC) {
        return MAY_READ;
    }
    // Верифицируйте цикл внутри функции
    /*@ 
        loop invariant 0 <= i <= size_array;
        loop invariant mask == 0 || \exists int j; 0 <= j < i && cmd == event_numbers[j][0] && mask == event_numbers[j][1];
        loop assigns i, mask;
        loop variant size_array - i;
    */
    for (i = 0; i < size_array; ++i)
        if (cmd == event_numbers[i][0]) {
            mask = event_numbers[i][1];
            break;
        }

    if (!mask)
        mask = MAY_READ | MAY_WRITE;

   return mask;

}
```

```C
static int check_permission (struct file *file, unsigned int cmd)
{
    const PDPL_T *sl = getCurrentLabel();
    //@ assert sl == getSecurityLabel(current);

    // Вычисляем уровень целостности пользователя
    unsigned int ilev = slabel_ilev(sl);
    //@ assert ilev == integrityCategories(sl);

    // Если пользователь не максимального уровня целостности, возвращаем ошибку доступа
    if (ilev != max_ilev){
        return -NO_ILEV;
    }

    // Вычисляем маску 
    int mask_final = compute_mask(file, cmd);

    // Текущий процесс -- суперпользователь + у пользователя есть право на запись в файл -- доступ разрешен

    if (current->process->fsuid == 0)
        if ((mask_final & MAY_WRITE)){
            return 0;
        }

    // Текущий процесс -- не суперпользователь + у пользователя есть право на чтение из файла -- доступ разрешён

    if (!(current->process->fsuid == 0))
        if ((mask_final & MAY_READ)){
            return 0;
        }

    // В других случаях доступ запрещен
    return -NO_PERM;
}
```

В этой первой части эксперимента мы смогли получить следующие результаты:
[RESULTS_1](first_result.txt)

После изменения наши функции будут выглядеть следующим образом:

```C
static int compute_mask(struct file *file, unsigned int cmd)
{
    struct inode *inode = file_inode(file);
    int mask = 0;
    int i = 0;
    // Количество событий в массиве event_numbers
    unsigned long size_array = (sizeof(event_numbers) / sizeof((event_numbers)[0]));

    // Проверяем, является ли файл публичным.
    // Если да, то доступ разрешен сразу
    if (inode->i_flags & SHIFT)
        return MAY_READ | MAY_WRITE;

    if (cmd > IMPORTANT) {
        return MAY_WRITE;
    }

    if (cmd < EXOTIC) {
        return MAY_READ;
    }
    // Верифицируйте цикл внутри функции
    /*@ 
        loop invariant 0 <= i <= size_array;
        loop invariant mask == 0 || \exists int j; 0 <= j < i && cmd == event_numbers[j][0] && mask == event_numbers[j][1];
        loop assigns i, mask;
        loop variant size_array - i;
    */
    for (i = 0; i < size_array; ++i)
        if (cmd == event_numbers[i][0]) {
            mask = event_numbers[i][1];
            break;
        }

    if (!mask)
        mask = MAY_READ | MAY_WRITE;

   return mask;

}
```

```C
static int check_permission (struct file *file, unsigned int cmd)
{
    const PDPL_T *sl = getCurrentLabel();
    //@ assert sl == getSecurityLabel(current);

    if (!(sl)) {
        return -NO_LABEL;
    }
    // Вычисляем уровень целостности пользователя
    unsigned int ilev = slabel_ilev(sl);
    //@ assert ilev == integrityCategories(sl);

    // Если пользователь не максимального уровня целостности, возвращаем ошибку доступа
    if (ilev != max_ilev){
        return -NO_ILEV;
    }

    // Вычисляем маску 
    int mask_final = compute_mask(file, cmd);

    // Текущий процесс -- суперпользователь + у пользователя есть право на запись в файл -- доступ разрешен

    if (current->process->fsuid == 0){
        return 0;
    }
    // Текущий процесс -- не суперпользователь + у пользователя есть право на чтение из файла -- доступ разрешён
    if (!(current->process->fsuid == 0))
        if ((mask_final & MAY_READ)){
            return 0;
        }
    // В других случаях доступ запрещен
    return -NO_PERM;
}
```

В этой второй част эксперимента мы смогли получить следующие результаты:
[RESULTS_2](second_result.txt)

Таким образом, мы достигаем полной проверки наших функций