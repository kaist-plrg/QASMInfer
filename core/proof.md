postulate를 보고 증명하면서 execution model 의 구현도 같이 진행

# postulate를 읽기 전
## 지금까지 진행 상황
* execution model
  * 없음
* proof.
  * 없음

## 구현
Execution model의 initial state를 정의하자.
initial state는 임의의 010101010..이 될 수 있다.
inductive 하게, empty 일 수 있고 0 일 수 있고 1 일 수 있고 tensor product로 두개 가져가 붙인 것일 수도 있다.

```coq
(* Density.v *)
Inductive InitialDensityMatrix: nat -> Matrix -> Prop :=
| DensityMatrix_empty: InitialDensityMatrix 0 (eye 0)
| DensityMatrix_0: InitialDensityMatrix 1 Den_0
| DensityMatrix_1: InitialDensityMatrix 1 Den_1
| DensityMatrix_TMproduct (n1 n2: nat) (den1 den2: Matrix):
  InitialDensityMatrix n1 den1 ->
  InitialDensityMatrix n2 den2 ->
  InitialDensityMatrix (n1 + n2) (TMproduct den1 den2).
```

별거 없지만 필요한 Operation 도 적자.

```coq
(* program.v *)
Inductive Instruction: Type :=
| NopInstr: Instruction
| SeqInstr: Instruction -> Instruction -> Instruction
| IfInstr: nat -> bool -> Instruction -> Instruction.  (* if cbit == 0 (false) or cbit == 1 (true) *)
```



# Postulate 1
## 지금까지 진행 상황
* execution model
  * state
    * Initial state만 정의되어 있음
  * operation
    * 별거없음
  * function
    * 없음
* proof.
  * 없음

## Postulate 내용
Postulate1이 의미하는 것: quantum state를 표현하는 density matrix가 가져야 하는 성질
1. Hermitian
1. Positive-semidefinite
1. Trace 1 (normalized)

## 증명
Execution model에 initial state가 있으므로 그 state가 postulate 1을 만족한다는 것을 증명해야한다.
### Hermitian
complex conjugate transpose가 자기 자신과 같다는 것을 보이면 된다.
```coq
(* density.v *)
Lemma InitialDensityMatrix_Hermitian: forall (n: nat) (den proj: Matrix),
  InitialDensityMatrix n den -> Projection proj -> Qop_Hermitian den.
Proof.
  ...
```
### Positive-definite
임의의 모든 벡터에 대해서, v^t * A * v 가 non-negative임을 보여야 하기 때문에 Hermitian보다는 증명이 까다롭다.
일단 우리가 정의한 initial density matrix들은 모두 특정 vector의 outer product로 나타내어질 수 있다는 점을 주목하자.
(물리학 용어로는 pure하다 라고 표현)
```coq
(* density.v *)
Lemma InitialDensityMatrix_pure: forall (n: nat) (den: Matrix),
  InitialDensityMatrix n den ->
  exists (qst: ColVec) (H: _),
  den = VVmult qst (CVconjtrans qst) H.
Proof.
  ...
```
density matrix가 pure하다는 것은, A = u * u^t 라고 할 수 있으므로
v^t * A * v = v^t * u * u^t * v =  (v^t * u) * (u^t * v) = 어떤 복소수와 켤레복소수의 곱 >= 0
이다.
```coq
(* operator.v *)
Lemma Qop_positive_pure: forall (m: Matrix),
  (exists (qst: ColVec) (H: _), m = VVmult qst (CVconjtrans qst) H) -> Qop_positive m.
Proof.
...
```
위에서 initial density matrix 가 pure하다는 것을 증명했으니까 positive-semidefinite도 증명이 가능하다.
```coq
(* density.v *)
Lemma InitialDensityMatrix_positive: forall (n: nat) (den: Matrix),
  InitialDensityMatrix n den -> Qop_positive den.
Proof.
  intros.
  apply Qop_positive_pure.
  eapply InitialDensityMatrix_pure.
  apply H.
Qed.
```

### Trace 1
Base case 에 대해서 증명하고, Inductive case (Tensor product case) 를 증명하면 된다.
Inductive case 에서는, Trace 1 인 두 matrix를 tensor product했을 때 걔도 trace 1 임을 증명해야 한다.

vector 끼리 tensor product를 해서 tensor product된 matrix 에 곱할 때 지들끼리 짝이 잘 맞는다는 것을 보여야 한다.

```coq
(* Density.v *)
Lemma TMproduct_normalized: forall (den1 den2: Matrix),
  Den_normalized den1 -> Den_normalized den2 -> Den_normalized (TMproduct den1 den2).
Proof.
...
```

이것만 증명하면 inductive 하게 증명된다:
```coq
(* Density.v *)
Lemma InitialDensityMatrix_normalized: forall (n: nat) (den: Matrix),
  InitialDensityMatrix n den -> Den_normalized den.
Proof.
  intros.
  induction H.
  + unfold Den_normalized, eye, Mtrace, func_sum, func_sum2, func_sum_suppl.
    lca.
  + apply Den_0_normalized.
  + apply Den_1_normalized.
  + apply TMproduct_normalized.
    apply IHInitialDensityMatrix1.
    apply IHInitialDensityMatrix2.
Qed.
```

# Postulate 2
## 지금까지 진행 상황
* execution model
  * state
    * Initial state만 정의되어 있음
  * operation
    * 없음
  * function
    * 없음
* proof.
  * Initial state 가 postulate 1 을 만족함

## Postulate 내용
어떤 물리량의 measurement 기댓값 계산하는 법
사실 quantum computing 용도에서는 postulate 3과 겹치는 느낌이 있다.

## 증명
Postulate에 적힌 대로 기댓값을 계산하는 것이 증명된 함수를 Execution model에 추가한다.
```coq
(* Density.v *)
Definition Den_expect (den observable: Matrix) (H: MMeqbits den observable) :=
  Mtrace (Mmult den observable H).
```
```coq
(* Physics.v *)
Theorem Observables_and_States: forall rho observable Hbits,
  Den_expect rho observable Hbits = Mtrace (Mmult rho observable Hbits).
Proof.
  reflexivity.
Qed.
```


# Postulate 3
## 지금까지 진행 상황
* execution model
  * state
    * Initial state만 정의되어 있음
  * operation
    * 없음
  * function
    * measurement 기댓값 계산하는 함수
* proof.
  * Initial state 가 postulate 1 을 만족함

## Postulate 내용
measurement 확률 계산하는 법

## 증명
Postulate에 적힌 대로 확률을 계산하는 것이 증명된 함수를 Execution model에 추가한다.

```coq
(* Density.v *)
Definition Den_prob (den: Matrix) (proj: Matrix) (H: MMeqbits den proj): C :=
  Mtrace (Mmult den proj H).
```
```coq
Theorem measurement_probability_postulate: forall rho projection Hbits,
  Den_prob rho projection Hbits = Mtrace (Mmult rho projection Hbits).
Proof.
  reflexivity.
Qed.
```

# Postulate 4
## 지금까지 진행 상황
* execution model
  * state
    * Initial state만 정의되어 있음
  * operation
    * 없음
  * function
    * measurement 기댓값 계산하는 함수
    * measurement 확률 계산하는 함수
* proof.
  * Initial state 가 postulate 1 을 만족함

## Postulate 내용
change of state by a measurement

## 증명
Postulate에 적힌 대로 density matrix를 변화시키는 것이 증명된 함수를 추가한다.
```coq
(* Density.v *)
Definition Den_measure (den proj: Matrix) (Hd: MMeqbits den proj): Matrix.
Proof.
  refine (
    Msmul
      (Cinv (Den_prob den proj Hd))
      ( Mmult (
          Mmult proj den _
        ) proj _)
  ).
  Unshelve.
  all: simpl_bits; simpl; lia.
Defined.
```
```coq
(* Physics.v *)
Theorem projection_postulate: forall rho proj Hbits Hp Hm1 Hm2,
  Den_measure rho proj Hbits =
    Msmul
      (Cinv (Den_prob rho proj Hp))
      ( Mmult (
          Mmult proj rho Hm1
        ) proj Hm2).
Proof.
  reflexivity.
Qed.
```
그리고 이 함수에 의해서 변화한 matrix는 역시 유효한 density matrix이어야 할것이다.
(여기서 projection matrix에 대한 설명을 추가해야 할까?)
```coq
Theorem projection_postulate_density: forall num_bits rho proj Hbits,
  DensityMatrix num_bits rho ->
  Projection proj ->
  Den_prob rho proj Hbits <> 0 ->
  DensityMatrix num_bits (Den_measure rho proj Hbits).
Proof.
  apply DensityMatrix_measure.
Qed.
```
이게 끝이 아니다. initial density matrix 외에 measurement때문에 변한 density matrix도
 postulate 1을 만족함을 또 보여야 한다 (일단 난해해서 생략).
```coq
(* Density.v *)
Inductive DensityMatrix: nat -> Matrix -> Prop :=
| DensityMatrix_init (n: nat) (den: Matrix): InitialDensityMatrix n den -> DensityMatrix n den
| DensityMatrix_measure (n: nat) (den proj: Matrix) (Hd: _):
    DensityMatrix n den ->
    Projection proj ->
    Den_prob den proj Hd <> 0 ->
    DensityMatrix n (Den_measure den proj Hd).
```
```coq
(* Density.v *)
Lemma DensityMatrix_Hermitian: forall (n: nat) (den: Matrix),
  DensityMatrix n den -> Qop_Hermitian den.
```


그리고 quantum computing에서, 적어도 Qasm에서는 0, 1로만 측정하기 때문에 general한 `Den_measure` 함수를 이용해
special한 `Den_measure_0` 과 `Den_measure_1`을 만든다
이를 이용해서 measurement operation을 execution model에 추가한다.
```coq
(* Program.v *)
Inductive Instruction: Type :=
| NopInstr: Instruction
| MeasureInstr: nat -> nat -> Instruction  (* 추가됨 *)
| SeqInstr: Instruction -> Instruction -> Instruction
| IfInstr: nat -> bool -> Instruction -> Instruction.
```
```coq
Fixpoint Execute_measure_instr (qbit cbit: nat) (worlds: ManyWorld): ManyWorld.
Proof.
  destruct worlds as [|[qstate cstate prob nq Hq] t].
  ...
```
# Postulate 5
## 지금까지 진행 상황
* execution model
  * state
    * Initial + Measurement
  * operation
    * Measurement
  * function
    * measurement 기댓값 계산하는 함수
    * measurement 확률 계산하는 함수
* proof.
  * Initial + Measurement state 가 postulate 1 을 만족함

## Postulate 내용
change of state by time evolution (Unitary Operation)

## 증명
Postulate에 적힌 대로 density matrix를 변화시키는 것이 증명된 함수를 추가한다.
```coq
(* Density.v *)
Definition Den_unitary (den uop: Matrix) (H1: _) (H2: _) :=
  (Mmult (Mmult uop den H1) (Mconjtrans uop) H2).
```
```coq
(* Physics.v *)
Theorem time_evoluation_postulate: forall rho uop H1 H2,
  Den_unitary rho uop H1 H2 = (Mmult (Mmult uop rho H1) (Mconjtrans uop) H2).
Proof.
  reflexivity.
Qed.
```
그리고 이 함수에 의해서 변화한 matrix는 역시 유효한 density matrix이어야 할것이다.
(여기서 unitary matrix에 대한 설명을 추가해야 할까?)
```coq
Theorem time_evolution_postulate_density: forall num_bits rho uop Hbits1 Hbits2,
  DensityMatrix num_bits rho ->
  Qop_unitary uop ->
  DensityMatrix num_bits (Mmult (Mmult uop rho Hbits1) (Mconjtrans uop) Hbits2).
Proof.
  apply DensityMatrix_unitary.
Qed.
```
이게 끝이 아니다. initial + measurement density matrix 외에 time evolution 때문에 변한 density matrix도
 postulate 1을 만족함을 또 보여야 한다 (일단 난해해서 생략).
```coq
(* Density.v *)
Inductive DensityMatrix: nat -> Matrix -> Prop :=
| DensityMatrix_init (n: nat) (den: Matrix): InitialDensityMatrix n den -> DensityMatrix n den
| DensityMatrix_unitary (n: nat) (den uop: Matrix) (H1: _) (H2: _):  (* 추가됨 *)
    DensityMatrix n den ->
    Qop_unitary uop ->
    DensityMatrix n (Den_unitary den uop H1 H2)
| DensityMatrix_measure (n: nat) (den proj: Matrix) (Hd: _):
    DensityMatrix n den ->
    Projection proj ->
    Den_prob den proj Hd <> 0 ->
    DensityMatrix n (Den_measure den proj Hd).
```
```coq
(* Density.v *)
Lemma DensityMatrix_Hermitian: forall (n: nat) (den: Matrix),
  DensityMatrix n den -> Qop_Hermitian den.
```


그리고 Qasm에서는 크게 두가지의 unitary operation을 지원한다.
general한 single-qubit rotation과 controlled-not 인데, 이를 postulate을 만족하며 사용하기 위해서는
일단 두 개의 operation이 unitary임을 증명해야 한다.
### General Rotation
single qubit operation in multi qubit state is unitary if
the same single qubit operation in single qubit state is uniatry
```coq
(* Operation.v *)
Lemma Qop_sq_general_unitary: forall (n t: nat) (op: Matrix) (Hop: _),
Qop_unitary op -> Qop_unitary (Qop_sq_general n t op Hop).
Proof.
...
```
general rotation of single qubit is uniatry
```coq
(* Operation.v *)
Lemma Qop_rot_unitary: forall (theta phi lambda: R), Qop_unitary (Qop_rot theta phi lambda).
Proof.
  intros.
```
### Cnot
general한 control - target qubit 쌍을 가지는 matrix를 생성하려면,
기본적인 2-bit (0:control, 1: target) 을 늘리고 swap operation matrix을 적절히 섞어주어야 한다.
이 과정에서 일어난 모든 연산에 대해서 unitary함이 변하지 않음을 보이면 된다.

```
(* Operator.v *)
Lemma Qop_cnot_unitary: forall (n qc qt: nat) (Hn: _) (Hc: _) (Ht: _),
  Qop_unitary (Qop_cnot n qc qt Hn Hc Ht).
Proof.
...
```

마지막으로 measurement operation을 execution model에 추가한다.
```coq
(* Program.v *)
Inductive Instruction: Type :=
| NopInstr: Instruction
| MeasureInstr: nat -> nat -> Instruction  (* 추가됨 *)
| SeqInstr: Instruction -> Instruction -> Instruction
| IfInstr: nat -> bool -> Instruction -> Instruction.
```
```coq
Fixpoint Execute_measure_instr (qbit cbit: nat) (worlds: ManyWorld): ManyWorld.
Proof.
  destruct worlds as [|[qstate cstate prob nq Hq] t].
  ...
```

# execution level로 확장
임의의 프로그램 input에 대해서 모든 many world를 구성하고 있는 world의 quantum state 는 항상 postulate 1 의 3가지 property를 만족한다.

```coq
Theorem Execute_quantum_state_density: forall (program: InlinedProgram),
  Forall (fun world => exists n, DensityMatrix n (W_qstate world)) (Execute program).
Proof.
...
```
