Require Import List ZArith.

(** Наша задача - формальная верификация одной из функций модуля безопасности
    ядра Linux.

    Поведение системы можно описать переходами между её состояниями.
    Состояние нашей системы (ядра Linux):
    - множество субъектов (например, процессов);
    - множество объектов (например, файлов);
    - матрица доступов субъектов к объектам;
    - метки целостности субъектов;
    - метки целостности объектов.

    Формально:

    Record State := {
      subjects         : Subject -> Prop;
      objects          : Object -> Prop;
      subjectAccess    : Subject -> Object -> Access -> Prop;
      subjectIntegrity : Subject -> L;
      objectIntegrity  : Object -> L
    }.

    Переход из одного состояния в другое происходит при наступлении события.
    Например, рассмотрим событие получения доступа субъекта к объекту. Если в
    запросе есть доступ на запись, то метка целостности объекта не должна
    превышать метку целостности субъекта:

    Inductive transition : Event -> State -> State -> Prop :=
    | tTakeAccessWrite   : forall s o a st,
                           subjects st s -> objects st o -> a aWrite -> checkRight st s o arWrite ->
                           transition (eTakeAccess s o a) st (updateAccess s o a st)
    | tTakeAccessNoWrite : forall s o a st,
                           subjects st s -> objects st o ->
                           ~ a aWrite -> transition (eTakeAccess s o a) st (updateAccess s o a st).

    Задание 1

    Посмотрим на функцию vsm_inode_permission из модуля безопасности ядра.
    Эта функция принимает два аргумента: указатель на inode, запрашиваемые
    параметры доступа к этому inode. Функция возвращает 0, если процессу
    разрешен доступ к inode.

    #define MAY_EXEC		0x00000001
    #define MAY_WRITE		0x00000002
    #define MAY_READ		0x00000004

    #define EACCES		13

    int vsm_inode_permission(struct inode *inode, int mask)
    {
            mask &= MAY_WRITE;

            if (!mask)
                    return 0;

            const struct security *isec = inode_security(inode);
            const struct security *tsec = cred_security(current_cred());

            if (tsec->ilev >= isec->ilev)
                    return 0;

            return -EACCES;
    }

    Наша задача - написать спецификацию этой функции, т.е. закончить
    определение:

    Definition inode_permission (tsec_ilev : Z) (isec_ilev : Z) (mask : Z) : Z := ...

    Вам могут пригодиться функции Z.testbit и Z_lt_dec.

    Задание 2

    Метки целостности функциональной спецификации обладают типом Z. Метки
    целостности формальной модели системы - элементы решетки. Нужно доказать,
    что тип Z является решеткой. Для этого нужно определить
    'Instance ZLattice : Lattice Z' для класса:

    Class Lattice (A : Type) := {
        meet : A -> A -> A where "x ∧ y" := (meet x y);
        join : A -> A -> A where "x ∨ y" := (join x y);

        meetCommutative : forall a b, a ∧ b = b ∧ a;
        meetAssociative : forall a b c, a ∧ (b ∧ c) = (a ∧ b) ∧ c;
        meetAbsorptive  : forall a b, a ∧ (a ∨ b) = a;
        meetIdempotent  : forall a, a ∧ a = a;

        joinCommutative : forall a b, a ∨ b = b ∨ a;
        joinAssociative : forall a b c, a ∨ (b ∨ c) = (a ∨ b) ∨ c;
        joinAbsorptive  : forall a b, a ∨ (a ∧ b) = a;
        joinIdempotent  : forall a, a ∨ a = a
      }.

    Задание 3

    Чтобы показать корректность функциональной спецификации vsm_inode_permission,
    докажем утверждение: функция inode_permission возвращает 0 тогда и только
    тогда, когда функция checkRight разрешает доступ субъекта к объекту:

    ∀ (st : State nat nat Z) (mask : Z) s o,
      inode_permission (subjectIntegrity st s) (objectIntegrity st o) mask = 0%Z ↔
      fromMask mask ⊆ checkRight nat nat Z st s o.

    Чтобы выполнить задание, в лемме inode_permission_checkRight замените
    'Admitted' на доказательство.

    Задание 4

    Чтобы убедиться в корректности спецификации, докажем, что любой переход
    системы из одного состояния в другое сохраняет следующее свойство: у
    субъекта есть доступ на запись к объекту только в том случае, если метка
    целостности объекта не превышает метку целостности субъекта. Формально:

    ∀ (es : list Event) (st st' : State),
      transitions es st st' -> integrity st -> integrity st',

    где integrity имеет следующее определение:

    ∀ s o, subjectAccess st s o aWrite -> objectIntegrity st o ≤ subjectIntegrity st s.

    Чтобы выполнить задание, в лемме transitionsIntegrity замените 'Admitted' на
    доказательство.
 *)

(** * Functional specification *)

Definition eaccess : Z := 13.

(* Задание 1 *)

(* Здесь транслируем поведение функции на C: если не запрашивается
   доступ на запись, то возвращаем 0. Иначе проверяем метки целостности. 
   Вместо сравнения с результатом в bool используем [Z_lt_dec],
   чтобы упростить дальнейшие доказательства. *)

Definition inode_permission (tsec_ilev : Z) (isec_ilev : Z) (mask : Z) : Z :=
  match Z.testbit mask 1 with
  | false => 0
  | true => 
    match Z_lt_dec tsec_ilev isec_ilev with
    | right _ => 0
    | left _ => Z.opp eaccess
    end
  end.

(** * Subset and union *)

Section Sets.
  Context {X : Type}.

  Definition union (A B : X -> Prop) : X -> Prop := fun x => A x \/ B x.

  Definition subset (A B : X -> Prop) : Prop := forall x, A x -> B x.
End Sets.

Infix "∪" := union (at level 85).
Infix "⊆" := subset (at level 90).

(** * Decidable equality *)

Class EqDec (A : Type) : Type :=
  eq_dec : forall a b : A, {a = b} + {a <> b}.

Lemma eq_dec_refl {A B} {A_eq : EqDec A} (a : A) (x y : B) :
  (if eq_dec a a then x else y) = x.
Proof.
  destruct (eq_dec a a).
  - reflexivity.
  - contradiction.
Qed.

Lemma eq_dec_neq {A B} {A_eq : EqDec A} {a a' : A} (x y : B) :
  a <> a' -> (if eq_dec a a' then x else y) = y.
Proof.
  intro H. destruct (eq_dec a a').
  - contradiction.
  - reflexivity.
Qed.

Instance ZEqDec : EqDec Z := { eq_dec := Z.eq_dec }.

Instance NatEqDec : EqDec nat := { eq_dec := Nat.eq_dec }.

(** * Lattice *)

Reserved Infix "∧" (at level 50, left associativity).
Reserved Infix "∨" (at level 45, left associativity).

Class Lattice (A : Type) := {
    meet : A -> A -> A where "x ∧ y" := (meet x y);
    join : A -> A -> A where "x ∨ y" := (join x y);

    meetCommutative : forall a b, a ∧ b = b ∧ a;
    meetAssociative : forall a b c, a ∧ (b ∧ c) = (a ∧ b) ∧ c;
    meetAbsorptive  : forall a b, a ∧ (a ∨ b) = a;
    meetIdempotent  : forall a, a ∧ a = a;

    joinCommutative : forall a b, a ∨ b = b ∨ a;
    joinAssociative : forall a b c, a ∨ (b ∨ c) = (a ∨ b) ∨ c;
    joinAbsorptive  : forall a b, a ∨ (a ∧ b) = a;
    joinIdempotent  : forall a, a ∨ a = a
  }.

Infix "∧" := meet (at level 50, left associativity).
Infix "∨" := join (at level 45, left associativity).

Definition lel {L} `{Lattice L} (a : L) (b : L) : Prop :=
  a = (a ∧ b).

Infix "≤" := lel (at level 50).

(* Задание 2 *)

(* Определяем [meet] и [join] в решетке
   Через [Z_lt_dec], чтобы упростить доказательства. *)

Definition Zmeet (x y : Z) : Z :=
  match Z_lt_dec x y with
  | left _ => x
  | right _ => y
  end.

Definition Zjoin (x y : Z) : Z :=
  match Z_lt_dec x y with
  | left _ => y
  | right _ => x
  end.

(* Далее доказательства придерживаются общей схемы:
   разбираем случаи по значениям [Z_lt_dec] и используем
   автоматику, чтобы закончить доказательства. *)

Theorem ZmeetCommutative : forall a b, Zmeet a b = Zmeet b a.
Proof with (auto with *).
  intros a b. unfold Zmeet. 
  destruct (Z_lt_dec a b) as [l0 | l0];
  destruct (Z_lt_dec b a) as [l1 | l1]...
  Qed.

Theorem ZmeetAssociative : forall a b c, Zmeet a (Zmeet b c) = Zmeet (Zmeet a b) c.
Proof with (auto with *).
  intros a b c. unfold Zmeet.
  destruct (Z_lt_dec a b) eqn:Hab;
  destruct (Z_lt_dec b c) eqn: Hbc;
  destruct (Z_lt_dec a c) eqn:Hac;
  try rewrite Hab...
  Qed.


Theorem ZmeetAbsorbtive : forall a b, Zmeet a (Zjoin a b) = a.
Proof.
  intros a b. unfold Zmeet. unfold Zjoin.
  destruct (Z_lt_dec a b) eqn:Hab; try rewrite Hab.
  - reflexivity.
  - destruct (Z_lt_dec a a); reflexivity.
  Qed.

Theorem ZmeetIdempotent : forall a, Zmeet a a = a.
Proof.
  intros a. unfold Zmeet. destruct (Z_lt_dec a a); reflexivity.
  Qed.

(* Доказательства для [join] идентичны доказательствам для
   [meet], с небольшими изменениями. *)

Theorem ZjoinCommutative : forall a b, Zjoin a b = Zjoin b a.
Proof with (auto with *).
  intros a b. unfold Zjoin. 
  destruct (Z_lt_dec a b) as [l0 | l0];
  destruct (Z_lt_dec b a) as [l1 | l1]...
  Qed.

Theorem ZjoinAssociative : forall a b c, Zjoin a (Zjoin b c) = Zjoin (Zjoin a b) c.
Proof with (auto with *).
  intros a b c. unfold Zjoin.
  destruct (Z_lt_dec a b) eqn:Hab;
  destruct (Z_lt_dec b c) eqn: Hbc;
  destruct (Z_lt_dec a c) eqn:Hac;
  try rewrite Hab...
  Qed.

Theorem ZjoinAbsorbtive : forall a b, Zjoin a (Zmeet a b) = a.
Proof.
  intros a b. unfold Zmeet. unfold Zjoin.
  destruct (Z_lt_dec a b) eqn:Hab; try rewrite Hab.
  - destruct (Z_lt_dec a a); reflexivity.
  - reflexivity.
  Qed.

Theorem ZjoinIdempotent : forall a, Zmeet a a = a.
Proof.
  intros a. unfold Zmeet. destruct (Z_lt_dec a a); reflexivity.
  Qed.

(* Наконец, собираем инстанс класса. *)

Instance ZLattice : Lattice Z := {
  meet := Zmeet;
  join := Zjoin;

  meetCommutative := ZmeetCommutative;
  meetAssociative := ZmeetAssociative;
  meetAbsorptive := ZmeetAbsorbtive;
  meetIdempotent := ZmeetIdempotent;

  joinCommutative := ZjoinCommutative;
  joinAssociative := ZjoinAssociative;
  joinAbsorptive := ZjoinAbsorbtive;
  joinIdempotent := ZjoinIdempotent;
}.

(** * Model *)

Section Integrity.
  Context {Subject Object L : Type} (si : Subject -> L) (oi : Object -> L)
    `{EqDec Subject} `{EqDec Object} `{Lattice L} `{EqDec L}.

  Inductive AccessRight := arRead | arWrite | arExecute | arOwn.

  Inductive Access := aRead | aWrite.

  Record State := {
      subjects         : Subject -> Prop;
      objects          : Object -> Prop;
      subjectAccess    : Subject -> Object -> Access -> Prop;
      subjectIntegrity : Subject -> L;
      objectIntegrity  : Object -> L
    }.

  Definition updateSubjectAccess (s : Subject) (o : Object) (a : Access -> Prop) (subjectAccess : Subject -> Object -> Access -> Prop) :  Subject -> Object -> Access -> Prop :=
    fun s' o' => match eq_dec s s', eq_dec o o' with
              | left _, left _ => a
              | _, _ => subjectAccess s' o'
              end.

  (* В состоянии st субъекту s присвоить доступы a к объекту o. *)

  Definition updateAccess (s : Subject) (o : Object) (a : Access -> Prop) (st : State) : State := {|
      subjects         := subjects st;
      objects          := objects st;
      subjectAccess    := updateSubjectAccess s o a (subjectAccess st);
      subjectIntegrity := subjectIntegrity st;
      objectIntegrity  := objectIntegrity st
    |}.

  (* Функция checkRight возвращает права доступа субъекта s к объекту o в состоянии st. *)

  Definition checkRight (st : State) (s : Subject) (o : Object) (ar : AccessRight) : Prop :=
    match ar with
    | arWrite => objectIntegrity st o ≤ subjectIntegrity st s
    | _ => True
    end.

  (* События, которые переводят систему из одного состояния в другое. *)

  Inductive Event :=
  | eTakeAccess    : Subject -> Object -> (Access -> Prop) -> Event
  | eDeleteAccess  : Subject -> Object -> (Access -> Prop) -> Event
  | eCreateSubject : Subject -> Subject -> Event
  | eCreateObject  : Subject -> Object -> Event.

  (* Переход системы из состояния в состояние при наступлении события. *)

  Inductive transition : Event -> State -> State -> Prop :=
  | tTakeAccessWrite   : forall s o a st,
                         subjects st s -> objects st o -> a aWrite -> checkRight st s o arWrite ->
                         transition (eTakeAccess s o a) st (updateAccess s o a st)
  | tTakeAccessNoWrite : forall s o a st,
                         subjects st s -> objects st o ->
                         ~ a aWrite -> transition (eTakeAccess s o a) st (updateAccess s o a st).

  (* Переход системы из состояния в состояние при наступлении последовательности
     событий es. *)

  Inductive transitions : list Event -> State -> State -> Prop :=
  | transitions_refl : forall st, transitions nil st st
  | transitions_step : forall e es st st' st'', transition e st' st'' -> transitions es st st' ->
                       transitions (e :: es) st st''.

  (* Задание 4 *)

  Definition integrity (st : State) : Prop :=
    forall s o, subjectAccess st s o aWrite -> objectIntegrity st o ≤ subjectIntegrity st s.

  Lemma transitionsIntegrity : forall (es : list Event) (st st' : State),
    transitions es st st' -> integrity st -> integrity st'.
  Proof.
  Admitted.
End Integrity.

Arguments State : clear implicits.

(** * Verification *)

Definition fromMaskb (mask : Z) : AccessRight -> bool := fun a =>
  match a with
  | arRead    => Z.testbit mask 2
  | arWrite   => Z.testbit mask 1
  | arExecute => Z.testbit mask 0
  | _         => false
  end.

Definition fromMask (mask : Z) : AccessRight -> Prop :=
  fun ar => fromMaskb mask ar = true.

(* Задание 3 *)

Lemma inode_permission_checkRight : forall (st : State nat nat Z) (mask : Z) s o,
  inode_permission (subjectIntegrity st s) (objectIntegrity st o) mask = 0%Z <->
  fromMask mask ⊆ checkRight st s o.
Proof.
  (* Начнем с того, что ведем в контекст аргументы,
     и развернем часть определений. *)
  intros st mask s o.
  unfold inode_permission.
  unfold subset.
  unfold fromMask.
  unfold checkRight.
  remember (subjectIntegrity st s) as sint.
  remember (objectIntegrity st o) as oint.
  (* Далее доказываем две импликации *)
  split; intros H.
  {
    (* Первая половина -- если [inode_permissions] возвращает 0,
       то [checkRight] разрешает доступ субъекта к объекту. *)
    (* разбираем случаи с разными правами. Все, кроме [arWrite],
       тривиальные и решаются автоматикой. *)
    intros ar. destruct ar; try (auto with *).
    (* Разворачиваем определение [fromMaskb], из
       него получаем свидетельство того, что второй бит маски -- 1,
       то есть запрашиваются права на запись. *)
    unfold fromMaskb. intros Htestbit.
    (* Уточняем гипотезу о том, что функция вернула 0, этим свидетельством *)
    rewrite Htestbit in H. unfold lel.
    (* Развернем [meet] в доказываемом утверждении, чтобы матч на [Z_lt_dec] 
        имел одинаковую форму в [H] и в утверждении. *)
    rewrite meetCommutative.
    (* Разбираем случаи. *)
    destruct (Z_lt_dec sint oint) eqn:Hlt.
    - (* Противоречивый случай, ибо имеем доказательство 0 = -13 *) inversion H. 
    - (* Докажем равенство. *) simpl. unfold Zmeet. rewrite Hlt. reflexivity.
  }
  {
    (* Вторая половина -- если [checkRight] разрешает доступ,
       то функция вернет 0. *)
    (* Разбираем случаи по второму биту маски, т. е. по наличию
       прав на запись среди запрашиваемых. *)
    destruct (Z.testbit mask 1) eqn:Hmask.
    - (* Были запрошены права на запись. Специализируем гипотезу о том,
         что [checkRight] разрешил доступ. *)
      specialize H with (x := arWrite). unfold fromMaskb in H.
      specialize (H Hmask).
      (* Упростим гипотезу о выдаче прав, и приведем ее к if того же
         вида, что и в доказываемом утверждении. *)
      unfold lel in H.
      rewrite meetCommutative in H. simpl in H.
      unfold Zmeet in H.
      (* Разберем случаи результатов сравнения. *)
      destruct (Z_lt_dec sint oint) eqn:Hlt.
      + (* Противоречие в предположениях: [sint < oint] и [sint = oint].
           Решим автоматикой. *)
        auto with *.
      + (* Тривиальный случай. *)
        reflexivity.
    - (* Если права на запись не запрашиваются. то функция вернет 0,
         и доказательство тривиальное *) reflexivity.
  }
  Qed.

