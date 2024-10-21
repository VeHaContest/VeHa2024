Require Import List ZArith.

Set Warnings "-parsing".
From mathcomp Require Import ssreflect ssrbool eqtype.
Set Warnings "parsing".

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

Open Scope Z_scope.

(* Подробная спецификация: *)

Definition inode_permission' (tsec_ilev : Z) (isec_ilev : Z) (mask : Z) : Z :=
  let MAY_WRITE := 2 in                 (* #define MAY_WRITE		0x00000002 *)
  let mask' := Z.land mask MAY_WRITE in (* mask &= MAY_WRITE; *)
  if mask' =? 0                         (* if (!mask) *)
  then 0                                (*   return 0; *)
  else
  if tsec_ilev >=? isec_ilev            (* if (tsec->ilev >= isec->ilev) *)
  then 0                                (*   return 0; *)
  else -eaccess.                        (* return -EACCES; *)

(* Эквивалентная ей "удобная" спецификация. Доказательство эквивалентности - в конце файла. *)

Definition inode_permission (tsec_ilev : Z) (isec_ilev : Z) (mask : Z) : Z :=
  if ~~ Z.testbit mask 1 then 0 else
  if isec_ilev <=? tsec_ilev then 0 else -eaccess.

Close Scope Z_scope.

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


#[refine] Instance ZLattice : Lattice Z :=
{
  meet := Z.min;
  join := Z.max;

  meetCommutative := Z.min_comm;
  meetAssociative := Z.min_assoc;
  meetAbsorptive := Z.max_min_absorption;
  meetIdempotent := Z.min_id;

  joinCommutative := Z.max_comm;
  joinAssociative := Z.max_assoc;
  joinAbsorptive := Z.min_max_absorption;
  joinIdempotent := Z.max_id;
}.
Defined.

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
    move=> ???.
    elim=> // e ???? Ht Hts IH Hi0.
    move: (IH Hi0)=> Hi1; clear Hts IH Hi0.
    case: e Ht=> [???|???|? s1|??] Ht s2 o2; rewrite/integrity.

    - case: Ht Hi1=> [s3 o3 ????? cr|s3 o3 ?????] Hi;
      first rewrite/checkRight in cr;
      rewrite/=/updateSubjectAccess;
      case: (eq_dec s3 s2)=> [<-|?];
      case: (eq_dec o3 o2)=> [<-//|?];
      exact: Hi.

    - case: Ht Hi1=> [s3 o3 ????? cr|s3 o3 ?????] Hi;
      first rewrite/checkRight in cr;
      rewrite/=/updateSubjectAccess;
      case: (eq_dec s3 s2)=> [<-|?];
      case: (eq_dec o3 o2)=> [<-//|?];
      exact: Hi.

    - case: Ht Hi1=> [s3 o3 ????? cr|s3 o3 ?????] Hi;
      first rewrite/checkRight in cr;
      rewrite/=/updateSubjectAccess;
      case: (eq_dec s3 s1)=> [?|?];
      case: (eq_dec o3 o2)=> [<-|?];
      case: (eq_dec s3 s2)=> [<-//|?];
      exact: Hi.

    case: Ht Hi1=> [s3 o3 ????? cr|s3 o3 ?????] Hi;
    first rewrite/checkRight in cr;
    rewrite/=/updateSubjectAccess;
    case: (eq_dec o3 o2)=> [<-|?];
    case: (eq_dec s3 s2)=> [<-//|?];
    exact: Hi.
  Qed.

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

Open Scope Z_scope.

Lemma lelP x y: reflect (x ≤ y) (x <=? y).
Proof.
  apply/Bool.iff_reflect.
  rewrite/lel/meet/=.
  split.
  - by move=>->; apply/Z.leb_spec0/Z.le_min_r.
  by rewrite/Z.min; case E:(x ?= y)=>//; move:(Z.leb_compare x y)->; rewrite E.
Qed.

Lemma inode_permission_checkRight : forall (st : State nat nat Z) (mask : Z) s o,
  inode_permission (subjectIntegrity st s) (objectIntegrity st o) mask = 0%Z <->
  fromMask mask ⊆ checkRight st s o.
Proof.
  rewrite/inode_permission/fromMask/fromMaskb/subset/checkRight=> st mask s o.
  move: (objectIntegrity st o)=> oi.
  move: (subjectIntegrity st s)=> si.
  split.
  - move/[swap].
    case; case: (Z.testbit mask 1)=> //=.
    case Ele: (oi <=? si)=> // _ _.
    exact: lelP.
  case: (Z.testbit mask 1)=> //=.
  move/(_ arWrite)/(_ (Logic.eq_refl true)).
  case E: (oi <=? si)=> // ?.
  exfalso.
  move: E=> /Bool.eq_true_false_abs.
  apply.
  by apply/lelP.
Qed.


(* Доказательство эквивалентности подробной и "удобной" спецификаций: *)

Import Zbitwise.
Local Notation "x .[ n ]" := (Z.testbit x n) (at level 9).

Goal forall t i m, inode_permission' t i m = inode_permission t i m.
Proof.
  move=> t i mark.
  rewrite/inode_permission'/inode_permission Z.geb_leb.
  case: (i <=? t); first by rewrite !if_same.
  have L (x y : Z): forall a b, (a = b) -> (if a then x else y) = (if b then x else y) by case; case.
  apply/L; clear L t i.
  have-> x: Z.land x 2 = if x.[1] then 2 else 0.
    Z.bitwise.
    case E: (m =? 1).
    - move: E=> /Z.eqb_spec->.
      have->: 2.[1] = true by [].
      rewrite Bool.andb_true_r.
      case: (x.[1]).
      + by have->: 2.[1] = true by [].
      by have->: 0.[1] = false by [].
    move: E=> /Z.eqb_neq E.
    have->: 2.[m] = false by have->: 2 = 2 ^ 1 by []; move: E=> /ssrfun.nesym; exact: Z.pow2_bits_false.
    rewrite Bool.andb_false_r.
    case: (x.[1]); last by rewrite Z.bits_0.
    have->: 2 = 2 ^ 1 by [].
    move: E=> /ssrfun.nesym E.
    by apply/ssrfun.esym/Z.pow2_bits_false.
  by case: (mark.[1]).
Qed.

Close Scope Z_scope.
