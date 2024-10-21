### Задача 1
Тут, кажется, комментировать особо нечего. Просто нужно правильно переписать условие на Coq.

### Задача 2
Для определение решётки я использовал леммы из библиотеки ZArith. 
В основном просто делал `Search Z.max`, `Search Z.min`, проходился глазами и вытаскивал нужные леммы.

### Задача 3

Тут всё усложняется вложенностью `fromMask mask ⊆ checkRight st s o`, но если их раскрыть, получаем, следующее: 

```coq
forall x : AccessRight,
  match x with
  | arRead => Z.testbit mask 2
  | arWrite => Z.testbit mask 1
  | arExecute => Z.testbit mask 0
  | arOwn => false
  end = true ->
  match x with
  | arWrite => objectIntegrity st o ≤ subjectIntegrity st s
  | _ => True
  end
```

Далее замечаем, что при `x <> arWrite` утверждение тривиально и имеет вид: `_ -> True`.
Поэтому далее смотрим что происходит при `x = arWrite`. А тогда утверждение раскрывается как 

```coq
Z.testbit mask 1 = true -> objectIntegrity st o ≤ subjectIntegrity st s
```

--------

Теперь раскроем `inode_permission`: 
```coq
Definition inode_permission (tsec_ilev : Z) (isec_ilev : Z) (mask : Z) : Z := 
  if andb (Z.testbit mask 1) (tsec_ilev <? isec_ilev)%Z
  then -eaccess 
  else 0.
```

В формулировке теореме записано `inode_permission _ _ _ = 0%Z`. Так как `-eaccess <> 0`, утверждение можно упростить как: 
```coq
andb (Z.testbit mask 1) (tsec_ilev <? isec_ilev)%Z = false
```

Далее всё почти тривиально: 
- Превращаем `lel` в `ltb` с помощью леммы `Zlattice_le_iff_Zle`
- Превращаем `andb a b = false` в `a = false \/ b = false` с помощью `Bool.andb_false_iff`

Таким образом мы приводим обе теоремы к одному виду. Остаётся только соединить их, что я и делаю с помощью теоремы `iff_trans`

### Задача 4

Заметим, что если свойство сохраняется при каждом шаге, то оно, очевидно, сохраняется и если шагов много. Поэтому добавляем как предположение 

```coq
Lemma transitionIntegrity: forall (e: Event) (st st': State),
  transition e st st' -> integrity st -> integrity st'.
Proof.
Admitted.
```

С помощью него лемма легко доказывается по индукции:
```coq
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
```

Теперь сфокусируемся на `transitionIntegrity`. Посмотрим как мог произойти переход из `st` в `st'`, для этого используем `inversion T; subst.`. Получаем две цели, одна соответствует `tTakeAccessWrite`, другая - `tTakeAccessNoWrite`. Далее раскроем `integrity (updateAccess s o a st)` с помощью `unfold integrity, updateAccess, updateSubjectAccess; simpl;`. Получаем:

```coq
forall (s0 : Subject) (o0 : Object),
  (if eq_dec s s0 
   then if eq_dec o o0 
        then a 
        else subjectAccess st s0 o0
   else subjectAccess st s0 o0) aWrite -> objectIntegrity st o0 ≤ subjectIntegrity st s0
```

Теперь замечаем, что если `s <> s0` или `o <> o0`, то мы можем просто воспользоваться гипотезой `I1 : integrity st`. Упрощаем, подставляем, а дальше одна из целей решается по предположению, а у другой есть противоречие в условии.