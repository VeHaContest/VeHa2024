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

Definition inode_permission (tsec_ilev : Z) (isec_ilev : Z) (mask : Z) : Z := 
  if andb (Z.testbit mask 1) (tsec_ilev <? isec_ilev)%Z
  then -eaccess 
  else 0.

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

Instance ZLattice : Lattice Z := {
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

  Lemma transitionIntegrity: forall (e: Event) (st st': State),
    transition e st st' -> integrity st -> integrity st'.
  Proof.
    intros e st st'.
    intros T I1.
    inversion T; subst;
    unfold integrity, updateAccess, updateSubjectAccess; simpl;
    intros;
    destruct (eq_dec s s0);
    try (apply I1; assumption);
    subst;
    destruct (eq_dec o o0);
    try (apply I1; assumption);
    subst.
    - unfold checkRight in H6.
      assumption.
    - contradiction.
  Qed.

  Lemma transitionsIntegrity : forall (es : list Event) (st st' : State),
    transitions es st st' -> integrity st -> integrity st'.
  Proof.
    intros es st st' H_transitions.
    induction H_transitions.
    - tauto.
    - intros.
      apply transitionIntegrity with (e := e) (st := st').
      + assumption.
      + apply IHH_transitions.
        assumption.
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

Lemma Zlattice_le_iff_Zle: forall a b,
  a ≤ b <-> (a <= b)%Z.
Proof.
  intros.
  unfold "≤", "∧".
  unfold ZLattice.
  split.
  - intros.
    symmetry in H.
    apply Z.min_l_iff.
    assumption.
  - intros.
    symmetry.
    apply Z.min_l_iff.
    assumption.
Qed.

Lemma if_false_eq: forall (A: Type) (cond: bool) (a b c: A),
  (if cond then a else b) = c -> 
  a <> c -> 
  b = c /\ cond = false. 
Proof.
  intros.
  destruct cond eqn: E.
  - contradiction.
  - split.
    + assumption.
    + reflexivity.
Qed.

Lemma inode_permission_iff: forall tsec_ilev isec_ilev mask,
  inode_permission tsec_ilev isec_ilev mask = 0%Z
  <->
  Z.testbit mask 1 = false \/ (tsec_ilev <? isec_ilev)%Z = false.
Proof. 
  split; intros.
  - unfold inode_permission in H.
    apply if_false_eq in H.
    2: { unfold "<>". intros. discriminate. } 
    destruct H as [_ H].
    rewrite Bool.andb_false_iff in H.
    assumption.
  - unfold inode_permission.
    destruct H as [H_testbit | H_le].
    + replace (Z.testbit mask 1) with false.
      reflexivity.
    + replace (tsec_ilev <? isec_ilev)%Z with false.
      rewrite Bool.andb_false_r.
      reflexivity.
Qed.

Lemma checkRight_iff: forall (st : State nat nat Z) (mask : Z) s o,
  fromMask mask ⊆ checkRight st s o 
  <-> 
  Z.testbit mask 1 = false \/ (subjectIntegrity st s <? objectIntegrity st o)%Z = false.
Proof.
  Opaque Z.testbit.

  split.
  - intros. 
    unfold fromMask, fromMaskb, checkRight, "⊆" in H.
    specialize H with arWrite.
    simpl in H.
    rewrite Zlattice_le_iff_Zle in H.
    rewrite <- Z.ltb_ge in H.
    
    destruct (Z.testbit mask 1) eqn: E.
    2: { left. reflexivity. }
    right.
    apply H.
    reflexivity.

  - intros.
    unfold fromMask, checkRight, "⊆".
    intros accessRight H_accessRight.
    destruct accessRight; try (apply I).
    
    unfold fromMaskb in H_accessRight.
    destruct H as [H_testbit_false | H_le_false].
    + rewrite H_accessRight in H_testbit_false.
      discriminate.
    + apply Zlattice_le_iff_Zle.
      apply Z.ltb_ge in H_le_false.
      assumption.
Qed.

Lemma inode_permission_checkRight : forall (st : State nat nat Z) (mask : Z) s o,
  inode_permission (subjectIntegrity st s) (objectIntegrity st o) mask = 0%Z <->
  fromMask mask ⊆ checkRight st s o.
Proof.
  intros.
  eapply iff_trans.
  - apply inode_permission_iff.
  - symmetry.
    apply checkRight_iff.
Qed.

Print Assumptions inode_permission_checkRight.