/*
* Функция compute_mask вычисляет маску (с битами MAY_WRITE и MAY_READ), которая в дальнейшем используется для
* принятия решения о доступе к заданному файлу. 
* Отметим, что доступы в маске означают наличие прав соответствующего доступа

* Функция check_permission проверяет доступ к заданному файлу с учетом прав пользователя на чтение/запись.
* Функция возвращает 3 значения:
* 0  – доступ к файлу разрешен;
* -13 – доступ к файлу запрещен (макрос NO_PERM); 
* -1 – недостаточно высокий уровень целостности пользователя, ошибка доступа (макрос NO_ILEV).

* Также используется выражение (MAY_READ | MAY_WRITE), разрешающее и чтение, и запись для указанного файла.

* ВНИМАНИЕ! 
* В коде одной из функций есть ошибка. Найдите её при помощи верификации, не изменяя уже написанные спецификации к коду.
* Исправьте код (обосновав своё решение) и полностью проверифицируйте получившиеся функции (все цели должны быть доказаны).

*/

// Определяем макросы
#define NO_PERM 13
#define NO_ILEV 1
#define NO_LABEL 12
#define MAY_WRITE 0x00000002
#define MAY_READ 0x00000004

#define IMPORTANT 50000
#define REGULAR 0x5414
#define ORDINARY 0x5413
#define RARE 0x541B
#define EXOTIC 2
#define SHIFT (1 << 9)

// Структура файла содержит 2 поля:
struct file {
    struct inode *f_inode; // поле индексного дескриптора и 
    int f_mode; // поле режима обработки
};

// Структура индексного дескриптора содержит 2 поля:
struct inode {
    unsigned int i_mode; // поле режима обработки и 
    unsigned int i_flags; // поле служебных флагов 
};

// Структура метки процесса,
// которая содержит следующие поля:
typedef struct {
    unsigned int lev; // поле иерархического уровня доступа;
    unsigned int ilev; // поле уровня целостности пользователя/процесса;
    unsigned int cat; // поле категорий целостности пользователя/процесса
} PDPL_T;

// Структура процесса содержит следующие поля:
struct process {
    unsigned int usage; // поле счетчика использования;
    unsigned int fsuid; // поле, определяющее, является ли процесс суперпользовательским (корневым);
    void *security; // поле структуры безопасности
};

// Структура текущей задачи содержит следующие поля:
struct task {
    unsigned int usage; // поле счетчика использования;
    const struct process *process; // поле структуры процесса;
    const PDPL_T *l; // поле метки процесса
};

// Глобальная переменная текущей задачи/процесса
struct task *current;

// Структура, сопоставляющая типу события определенное право доступа
static const unsigned int event_numbers[][2] = {
    { REGULAR, MAY_WRITE },
    { ORDINARY, MAY_READ },
    { RARE, MAY_READ },
};

// Глобальная переменная максимального уровня целостности
unsigned int max_ilev = 123400000;

// Аксиоматика; можете дополнять своими определениями 
/*@   axiomatic Block {
         logic unsigned int integrityCategories(PDPL_T *l) = l->ilev;
         predicate currentIsFileSystemRoot =
            current->process->fsuid == 0;
         logic PDPL_T *getSecurityLabel(struct task *task) =
            task->l;    
             // Файл f публичный?
         predicate isPublic(struct file *f) = f->f_inode->i_flags & SHIFT;
             // Событие важное?
         predicate isImportant(unsigned int cmd) = cmd > IMPORTANT;
             // Событие экзотическое?
         predicate isExotic(unsigned int cmd) = cmd < EXOTIC;
             // Маска доступа корректна?
         predicate isValidMask(int mask) =
             mask == 0 || mask == MAY_READ || mask == MAY_WRITE || mask == (MAY_READ | MAY_WRITE);
             // У текущего процесса задана метка доступа?
         predicate hasLabel = current->l;
             // У текущего процесса достаточный уровень целостности?
         predicate hasLevel = current->l->ilev == max_ilev;
}*/

// Функция-геттер, возвращает поле индексного дескриптора
/*@   requires \valid(f); 
          // Здесь было \nothing, но для анализа лучше указать,
          // на что может указывать результат.
      assigns \result \from f->f_inode;
      ensures \result == f->f_inode;
*/
static inline struct inode *file_inode(const struct file *f)
{
    return f->f_inode;
}

// Функция-геттер, возвращает поле уровня целостности пользователя/процесса;
/*@   requires \valid(sl);
      assigns \nothing;
      ensures \result == sl->ilev;
*/
unsigned int slabel_ilev(const PDPL_T *sl)
{ 
   return sl->ilev;
}

// Функция-геттер, возвращает метку безопасности пользователя/процесса;
/*@ requires \valid(current);
    requires \valid(current->l) || current->l == \null;
        // Здесь было \nothing, но для анализа лучше указать,
        // на что может указывать результат.
    assigns \result \from current->l;
    ensures \result == current->l;
*/
PDPL_T * getCurrentLabel() {
    return current->l;
}


// Напишите спецификации к функции; также верифицируйте цикл внутри функции
/*@
        // Файл и его структура должны быть корректными структурами в памяти.
    requires \valid(file);
    requires \valid(file->f_inode);
        // Функция является "чистой", т.е. ничего не изменяет.
    assigns \nothing;
        // Функция возвращает 0, MAY_READ, MAY_WRITE или их комбинацию.
    ensures isValidMask(\result);
        // Спецификации ниже описывают поведение более подробно.
        // Они могут быть удалены/проигнорированы, если подробности не нужны.
    behavior public:
        assumes isPublic(file);
        ensures \result == (MAY_READ | MAY_WRITE);
    behavior important:
        assumes !isPublic(file);
        assumes isImportant(cmd);
        ensures \result == MAY_WRITE;
    behavior exotic:
        assumes !isPublic(file);
        assumes isExotic(cmd);
        ensures \result == MAY_READ;
    behavior other:
        assumes !isPublic(file);
        assumes !isImportant(cmd);
        assumes !isExotic(cmd);
        ensures isValidMask(\result);
    complete behaviors;
    disjoint behaviors;
*/
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
            // Индекс не меньше 0.
        loop invariant 0 <= i;
            // Маска принимает одно из 3 значений: 0, MAY_READ, MAY_WRITE.
            // Но нам достаточно знать, что её значение корректно.
        loop invariant isValidMask(mask);
            // В цикле изменяются только эти переменные.
        loop assigns i, mask;
            // На каждом шаге индекс увеличивается на 1,
            // при этом его величина не превышает размер массива,
            // поэтому цикл завершается.
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

// Напишите спецификации к функции.
/*@
        // Файл и его структура должны быть корректными структурами в памяти.
    requires \valid(file);
    requires \valid(file->f_inode);
        // current указывает на корректную структуру.
    requires \valid(current);
        // Указатель на метку процесса должен быть корректным либо нулевым.
    requires \valid(current->l) || current->l == \null;
        // Описатель структуры процесса должен быть корректным.
    requires \valid_read(current->process);
        // Функция является "чистой", т.е. ничего не изменяет.
    assigns  \nothing;
        // Результат может принимать 4 значения.
        // Дополнительное значение -12 (макрос NO_LABEL) описывает ситуацию,
        // когда у процесса не установлена метка доступа.
    ensures  \result == 0 || \result == -NO_ILEV || \result == -NO_PERM || \result == -NO_LABEL;
        // Спецификации ниже описывают поведение более подробно.
        // Они помогают проанализировать поведение и сравнить его с ожидающимся.
        // Например, доступ суперпользователя по экзотическому событию
        // к непубличному файлу запрещён (поведение root_exotic), а доступ
        // не-суперпользователя при тех же условиях разрешён (поведение user_exotic).
        // Эти спецификации могут быть удалены/проигнорированы, если подробности не нужны.
    behavior no_label:
        assumes !hasLabel;
        ensures \result == -NO_LABEL;
    behavior no_level:
        assumes hasLabel;
        assumes !hasLevel;
        ensures \result == -NO_ILEV;
    behavior root_public:
        assumes hasLabel;
        assumes hasLevel;
        assumes currentIsFileSystemRoot;
        assumes isPublic(file);
        ensures \result == 0;
    behavior root_important:
        assumes hasLabel;
        assumes hasLevel;
        assumes currentIsFileSystemRoot;
        assumes !isPublic(file);
        assumes isImportant(cmd);
        ensures \result == 0;
    behavior root_exotic:
        assumes hasLabel;
        assumes hasLevel;
        assumes currentIsFileSystemRoot;
        assumes !isPublic(file);
        assumes isExotic(cmd);
        ensures \result == -NO_PERM;
    behavior user_public:
        assumes hasLabel;
        assumes hasLevel;
        assumes !currentIsFileSystemRoot;
        assumes isPublic(file);
        ensures \result == 0;
    behavior user_exotic:
        assumes hasLabel;
        assumes hasLevel;
        assumes !currentIsFileSystemRoot;
        assumes !isPublic(file);
        assumes isExotic(cmd);
        ensures \result == 0;
    behavior user_important:
        assumes hasLabel;
        assumes hasLevel;
        assumes !currentIsFileSystemRoot;
        assumes !isPublic(file);
        assumes isImportant(cmd);
        ensures \result == -NO_PERM;
    behavior other:
        assumes hasLabel;
        assumes hasLevel;
        assumes !isPublic(file);
        assumes !isImportant(cmd);
        assumes !isExotic(cmd);
        ensures \result == 0 || \result == -NO_PERM;
    disjoint behaviors;
    complete behaviors;
*/
static int check_permission (struct file *file, unsigned int cmd)
{
    const PDPL_T *sl = getCurrentLabel();

    // Если у пользователя не установлена метка процесса, сообщаем об её отсутствии
    if (!(current->l)) {
        return -NO_LABEL;
    }

    // Вычисляем уровень целостности пользователя
    unsigned int ilev = slabel_ilev(sl);

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
