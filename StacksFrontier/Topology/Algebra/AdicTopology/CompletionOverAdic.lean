module

public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
public import Mathlib.RingTheory.AdicCompletion.Topology
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.RingHom.FaithfullyFlat
public import Mathlib.RingTheory.RingHom.Flat
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Topology.Algebra.AdicTopology.AdmissibleRings
public import StacksFrontier.Topology.Algebra.AdicTopology.CompletionOver

/-!
# The completion over an adic base is an adic completion

Let `f : B →+* A` be a ring homomorphism out of a topological ring `B`.  The completion
`CompletionOver f` of Tag 0AN6 is the inverse limit of the rings `A / JA`, taken over *all* weak
ideals of definition `J` of `B`.  When the topology of `B` is the `I`-adic topology of an ideal of
definition `I`, the powers `Iⁿ` with `n ≥ 1` are cofinal among the weak ideals of definition, so
the limit is already computed by the single chain `(Iⁿ)`: the completion over `B` is the
`IA`-adic completion of `A`.

Cofinality is the content of `isWeakIdealOfDefinition_pow` — a positive power of an ideal of
definition is a weak ideal of definition — and of
`exists_pow_le_of_isWeakIdealOfDefinition` — a weak ideal of definition contains a positive
power of an ideal of definition.  The comparison map reads off the `I ^ (n + 1)`-component, the
shift being forced by `I ^ 0 = ⊤`, which is not a weak ideal of definition.

## Main results

* `TopologicalRing.CompletionOver.toAdicCompletion`: the comparison ring homomorphism
  `CompletionOver f →+* AdicCompletion (I.map f) A`, with
  `TopologicalRing.CompletionOver.bijective_toAdicCompletion` and the resulting
  `TopologicalRing.CompletionOver.adicCompletionRingEquiv`.
* `TopologicalRing.CompletionOver.toAdicCompletion_comp_ofTarget`: the comparison map carries
  the natural map from `A` to the canonical map into the adic completion.
* `TopologicalRing.CompletionOver.flat_ofTarget`, `flat_canonicalMap` and
  `faithfullyFlat_canonicalMap`: over an adic base with Noetherian target, the vertical maps of
  a localization diagram are flat, and faithfully flat when the map being completed is.  The
  last is the algebraic content of Tag 0AN9.

## References

* [Stacks Project, Tag 0AN6](https://stacks.math.columbia.edu/tag/0AN6)
-/

@[expose] public section

namespace TopologicalRing

namespace CompletionOver

universe u v

section Factor

variable {A : Type v} [CommRing A]

/-- Factoring a quotient map through the same ideal is the identity. -/
public lemma factor_le_rfl {J : Ideal A} (z : A ⧸ J) :
    Ideal.Quotient.factor (le_refl J) z = z := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective z
  exact Ideal.Quotient.factor_mk (le_refl J) a

/-- Factoring twice is factoring once. -/
public lemma factor_factor {J K L : Ideal A} (h₁ : J ≤ K) (h₂ : K ≤ L) (z : A ⧸ J) :
    Ideal.Quotient.factor h₂ (Ideal.Quotient.factor h₁ z) =
      Ideal.Quotient.factor (h₁.trans h₂) z := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective z
  rw [Ideal.Quotient.factor_mk, Ideal.Quotient.factor_mk, Ideal.Quotient.factor_mk]

/-- Factoring along an equality of ideals is injective. -/
public lemma factor_injective_of_eq {J K : Ideal A} (h : J = K) :
    Function.Injective (Ideal.Quotient.factor (le_of_eq h)) := by
  subst h
  intro z w hzw
  rwa [factor_le_rfl, factor_le_rfl] at hzw

end Factor

section Cofinal

open Filter
open scoped Topology

variable {B : Type u} [CommRing B] [TopologicalSpace B]

/-- Every element of an ideal of definition is topologically nilpotent: its `k`-th power lies in
`I ^ k`, and the powers of `I` are cofinal among the neighbourhoods of zero. -/
@[ega "0 7.1.4" "(ii)"]
public lemma isTopologicallyNilpotent_of_mem_isIdealOfDefinition {I : Ideal B}
    (hdef : IsIdealOfDefinition I) {x : B} (hx : x ∈ I) : IsTopologicallyNilpotent x := by
  rw [IsTopologicallyNilpotent, Filter.tendsto_def]
  intro U hU
  obtain ⟨m, hm⟩ := hdef.2 U hU
  refine Filter.mem_of_superset (Filter.eventually_ge_atTop m) fun k hk ↦ hm ?_
  exact Ideal.pow_le_pow_right hk (Ideal.pow_mem_pow hx k)

/-- A positive power of an ideal of definition defining the topology is a weak ideal of
definition. -/
public lemma isWeakIdealOfDefinition_pow [IsTopologicalRing B] {I : Ideal B}
    (hdef : IsIdealOfDefinition I) (hadic : _root_.IsAdic I) {n : ℕ} (hn : n ≠ 0) :
    IsWeakIdealOfDefinition (I ^ n) :=
  ⟨(isAdic_iff.mp hadic).1 n, fun _ hx ↦
    isTopologicallyNilpotent_of_mem_isIdealOfDefinition hdef (Ideal.pow_le_self hn hx)⟩

/-- Every weak ideal of definition contains a positive power of an ideal of definition. -/
public lemma exists_pow_le_of_isWeakIdealOfDefinition {I : Ideal B}
    (hdef : IsIdealOfDefinition I) {J : Ideal B} (hJ : IsWeakIdealOfDefinition J) :
    ∃ n : ℕ, n ≠ 0 ∧ I ^ n ≤ J := by
  obtain ⟨m, hm⟩ := hdef.2 (J : Set B) (hJ.1.mem_nhds J.zero_mem)
  exact ⟨m + 1, Nat.succ_ne_zero m, fun _ hx ↦ hm (Ideal.pow_le_pow_right (Nat.le_succ m) hx)⟩

end Cofinal

section Compare

variable {B : Type u} {A : Type v} [CommRing B] [CommRing A]

/-- Extending the `n`-th power of an ideal along `f` gives the ideal cutting out the `n`-th
quotient of the `IA`-adic completion of `A`. -/
public lemma map_pow_eq_pow_smul_top (f : B →+* A) (I : Ideal B) (n : ℕ) :
    (I ^ n).map f = ((I.map f) ^ n • ⊤ : Ideal A) := by
  rw [Ideal.smul_eq_mul, Ideal.mul_top, Ideal.map_pow]

variable (f : B →+* A) {I : Ideal B}

/-- A lower component of an adic completion element is the class of the same representative. -/
private theorem val_eq_mk_of_le (y : AdicCompletion (I.map f) A) {m n : ℕ} (h : m ≤ n) {a : A}
    (ha : y.1 n = Ideal.Quotient.mk _ a) : y.1 m = Ideal.Quotient.mk _ a := by
  rw [← y.2 h, ha]
  exact AdicCompletion.transitionMap_ideal_mk (I.map f) h a

/-- The `n`-th component, in `A ⧸ Iⁿ A`, of an element of the `IA`-adic completion of `A`. -/
public def ofAdicVal (y : AdicCompletion (I.map f) A) (n : ℕ) : A ⧸ ((I ^ n).map f) :=
  Ideal.Quotient.factor (le_of_eq (map_pow_eq_pow_smul_top f I n).symm) (y.1 n)

/-- If the `n`-th component of `y` is the class of `a`, then so is `ofAdicVal f y n`. -/
public lemma ofAdicVal_eq_mk (y : AdicCompletion (I.map f) A) {n : ℕ} {a : A}
    (ha : y.1 n = Ideal.Quotient.mk _ a) :
    ofAdicVal f y n = Ideal.Quotient.mk _ a := by
  rw [ofAdicVal, ha, Ideal.Quotient.factor_mk]

/-- The components `ofAdicVal` form a compatible family along the chain of powers. -/
public lemma factor_ofAdicVal {m n : ℕ} (h : m ≤ n) (y : AdicCompletion (I.map f) A) :
    Ideal.Quotient.factor (Ideal.map_mono (Ideal.pow_le_pow_right h : I ^ n ≤ I ^ m))
        (ofAdicVal f y n) = ofAdicVal f y m := by
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (y.1 n)
  rw [ofAdicVal_eq_mk f y ha.symm, ofAdicVal_eq_mk f y (val_eq_mk_of_le f y h ha.symm),
    Ideal.Quotient.factor_mk]

/-- The value of `ofAdicVal` pushed into `A ⧸ LA` does not depend on the chosen power of `I`
contained in `L`. -/
public lemma factor_ofAdicVal_eq {L : Ideal B} {k m : ℕ} (hk : I ^ k ≤ L) (hm : I ^ m ≤ L)
    (y : AdicCompletion (I.map f) A) :
    Ideal.Quotient.factor (Ideal.map_mono hk) (ofAdicVal f y k) =
      Ideal.Quotient.factor (Ideal.map_mono hm) (ofAdicVal f y m) := by
  rcases le_total k m with hkm | hmk
  · rw [← factor_ofAdicVal f hkm y, factor_factor]
  · rw [← factor_ofAdicVal f hmk y, factor_factor]

end Compare

section Adic

variable {B : Type u} {A : Type v} [CommRing B] [CommRing A] [TopologicalSpace B]
  {I : Ideal B} (hdef : IsIdealOfDefinition I)

/-- A positive exponent with `I ^ n` contained in a given weak ideal of definition. -/
public noncomputable def chosenExp (J : WeakIdealOfDefinitionIndex B) : ℕ :=
  (exists_pow_le_of_isWeakIdealOfDefinition hdef J.2).choose

/-- The power of `I` with exponent `chosenExp hdef J` is contained in `J`. -/
public lemma pow_chosenExp_le (J : WeakIdealOfDefinitionIndex B) :
    I ^ chosenExp hdef J ≤ J.1 :=
  (exists_pow_le_of_isWeakIdealOfDefinition hdef J.2).choose_spec.2

/-- A coarser component of an element of the completion over `B` is the class of the same
representative. -/
private theorem val_eq_mk_of_le_index (f : B →+* A) (x : CompletionOver f)
    {J K : WeakIdealOfDefinitionIndex B} (h : J.1 ≤ K.1) {a : A}
    (ha : x.1 J = Ideal.Quotient.mk _ a) : x.1 K = Ideal.Quotient.mk _ a := by
  have hcomp := x.2 J K h
  rw [ha] at hcomp
  exact hcomp.symm.trans (Ideal.Quotient.factor_mk (Ideal.map_mono h) a)

variable [IsTopologicalRing B] (hadic : _root_.IsAdic I)

/-- The weak ideal of definition `I ^ (n + 1)`, as an index of the inverse system defining the
completion over `B`. -/
@[reducible] public def powIndex (n : ℕ) : WeakIdealOfDefinitionIndex B :=
  ⟨I ^ (n + 1), isWeakIdealOfDefinition_pow hdef hadic (Nat.succ_ne_zero n)⟩

/-- The chain of powers indexing the completion over an adic base is antitone. -/
public lemma powIndex_le {m n : ℕ} (h : m ≤ n) :
    (powIndex hdef hadic n).1 ≤ (powIndex hdef hadic m).1 :=
  Ideal.pow_le_pow_right (Nat.succ_le_succ h)

variable (f : B →+* A)

/-- The `n + 1`-st extended power is contained in the ideal cutting out the `n`-th quotient of
the adic completion. -/
public lemma extendedIdeal_powIndex_le (n : ℕ) :
    extendedIdeal f (powIndex hdef hadic n) ≤ ((I.map f) ^ n • ⊤ : Ideal A) := by
  rw [← map_pow_eq_pow_smul_top f I n]
  exact Ideal.map_mono (Ideal.pow_le_pow_right (Nat.le_succ n))

/-- The `n`-th component of the comparison map, read off the `I ^ (n + 1)`-component of the
element.  The chain is shifted by one because `I ^ 0 = ⊤` is not a weak ideal of definition. -/
public def toAdicValHom (n : ℕ) :
    CompletionOver f →+* A ⧸ ((I.map f) ^ n • ⊤ : Ideal A) :=
  (Ideal.Quotient.factor (extendedIdeal_powIndex_le hdef hadic f n)).comp
    (projection f (powIndex hdef hadic n))

/-- If the `I ^ (n + 1)`-component of `x` is the class of `a`, then so is the `n`-th component
`toAdicValHom hdef hadic f n x` of the comparison map. -/
public lemma toAdicValHom_eq_mk {n : ℕ} (x : CompletionOver f) {a : A}
    (ha : projection f (powIndex hdef hadic n) x = Ideal.Quotient.mk _ a) :
    toAdicValHom hdef hadic f n x = Ideal.Quotient.mk _ a := by
  rw [toAdicValHom, RingHom.coe_comp, Function.comp_apply, ha, Ideal.Quotient.factor_mk]

/-- The components of the comparison map are compatible with the transition maps of the adic
completion. -/
public lemma transitionMap_toAdicValHom {m n : ℕ} (h : m ≤ n) (x : CompletionOver f) :
    AdicCompletion.transitionMap (I.map f) A h (toAdicValHom hdef hadic f n x) =
      toAdicValHom hdef hadic f m x := by
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (projection f (powIndex hdef hadic n) x)
  have hn : projection f (powIndex hdef hadic n) x = Ideal.Quotient.mk _ a := ha.symm
  rw [toAdicValHom_eq_mk hdef hadic f x hn,
    toAdicValHom_eq_mk hdef hadic f x (val_eq_mk_of_le_index f x (powIndex_le hdef hadic h) hn)]
  exact AdicCompletion.transitionMap_ideal_mk (I.map f) h a

/-- The comparison map from the completion of `A` over an adic base `B` to the `IA`-adic
completion of `A`, as a function. -/
public def toAdicCompletionFun (x : CompletionOver f) : AdicCompletion (I.map f) A :=
  ⟨fun n ↦ toAdicValHom hdef hadic f n x, fun h ↦ transitionMap_toAdicValHom hdef hadic f h x⟩

/-- The `n`-th component of `toAdicCompletionFun` is `toAdicValHom`. -/
@[simp]
public lemma val_toAdicCompletionFun (x : CompletionOver f) (n : ℕ) :
    (toAdicCompletionFun hdef hadic f x).1 n = toAdicValHom hdef hadic f n x := rfl

/-- The comparison map from the completion of `A` over an adic base `B` to the `IA`-adic
completion of `A`. -/
public def toAdicCompletion : CompletionOver f →+* AdicCompletion (I.map f) A where
  toFun := toAdicCompletionFun hdef hadic f
  map_one' := AdicCompletion.ext fun n ↦ by
    rw [val_toAdicCompletionFun, AdicCompletion.val_one]
    exact map_one (toAdicValHom hdef hadic f n)
  map_mul' x y := AdicCompletion.ext fun n ↦ by
    rw [val_toAdicCompletionFun, AdicCompletion.val_mul, val_toAdicCompletionFun,
      val_toAdicCompletionFun]
    exact map_mul (toAdicValHom hdef hadic f n) x y
  map_zero' := AdicCompletion.ext fun n ↦ by
    rw [val_toAdicCompletionFun, AdicCompletion.val_zero_apply]
    exact map_zero (toAdicValHom hdef hadic f n)
  map_add' x y := AdicCompletion.ext fun n ↦ by
    rw [val_toAdicCompletionFun, AdicCompletion.val_add_apply, val_toAdicCompletionFun,
      val_toAdicCompletionFun]
    exact map_add (toAdicValHom hdef hadic f n) x y

/-- The `n`-th component of the comparison map `toAdicCompletion` is `toAdicValHom`. -/
@[simp]
public lemma val_toAdicCompletion (x : CompletionOver f) (n : ℕ) :
    (toAdicCompletion hdef hadic f x).1 n = toAdicValHom hdef hadic f n x := rfl

/-- The comparison map is compatible with the natural maps from `A`. -/
public lemma toAdicCompletion_comp_ofTarget :
    (toAdicCompletion hdef hadic f).comp (ofTarget f) =
      algebraMap A (AdicCompletion (I.map f) A) := by
  refine RingHom.ext fun a ↦ AdicCompletion.ext fun n ↦ ?_
  rw [RingHom.coe_comp, Function.comp_apply, val_toAdicCompletion,
    toAdicValHom_eq_mk hdef hadic f (ofTarget f a) (projection_ofTarget f _ a)]
  rfl

/-- At a shifted index the comparison map is the element's own component, transported along the
equality of the two descriptions of the cutting ideal. -/
public lemma toAdicValHom_succ (x : CompletionOver f) (n : ℕ) :
    toAdicValHom hdef hadic f (n + 1) x =
      Ideal.Quotient.factor (le_of_eq (map_pow_eq_pow_smul_top f I (n + 1)))
        (x.1 (powIndex hdef hadic n)) := by
  obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective (projection f (powIndex hdef hadic (n + 1)) x)
  have hb' : projection f (powIndex hdef hadic (n + 1)) x = Ideal.Quotient.mk _ b := hb.symm
  rw [toAdicValHom_eq_mk hdef hadic f x hb',
    val_eq_mk_of_le_index f x (powIndex_le hdef hadic (Nat.le_succ n)) hb',
    Ideal.Quotient.factor_mk]

/-- The comparison map to the adic completion is injective. -/
public lemma injective_toAdicCompletion :
    Function.Injective (toAdicCompletion hdef hadic f) := by
  intro x y hxy
  have hval : ∀ n : ℕ, x.1 (powIndex hdef hadic n) = y.1 (powIndex hdef hadic n) := by
    intro n
    refine factor_injective_of_eq (map_pow_eq_pow_smul_top f I (n + 1)) ?_
    rw [← toAdicValHom_succ hdef hadic f x n, ← toAdicValHom_succ hdef hadic f y n,
      ← val_toAdicCompletion hdef hadic f x (n + 1), hxy]
    rfl
  refine Subtype.ext (funext fun J ↦ ?_)
  obtain ⟨k, hk0, hk⟩ := exists_pow_le_of_isWeakIdealOfDefinition hdef J.2
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
  have hxJ := x.2 (powIndex hdef hadic n) J hk
  have hyJ := y.2 (powIndex hdef hadic n) J hk
  rw [← hxJ, ← hyJ, hval n]

/-- The inverse comparison map, from the `IA`-adic completion of `A` to the completion of `A`
over `B`. -/
public noncomputable def ofAdicCompletionFun (y : AdicCompletion (I.map f) A) :
    CompletionOver f :=
  ⟨fun J ↦ Ideal.Quotient.factor (Ideal.map_mono (pow_chosenExp_le hdef J))
      (ofAdicVal f y (chosenExp hdef J)), by
    intro J K h
    rw [transitionMap, factor_factor]
    exact factor_ofAdicVal_eq f ((pow_chosenExp_le hdef J).trans h)
      (pow_chosenExp_le hdef K) y⟩

/-- The comparison map to the adic completion is surjective. -/
public lemma surjective_toAdicCompletion :
    Function.Surjective (toAdicCompletion hdef hadic f) := by
  intro y
  refine ⟨ofAdicCompletionFun hdef f y, AdicCompletion.ext fun n ↦ ?_⟩
  have hstep : (ofAdicCompletionFun hdef f y).1 (powIndex hdef hadic n) =
      ofAdicVal f y (n + 1) :=
    (factor_ofAdicVal_eq f (pow_chosenExp_le hdef (powIndex hdef hadic n))
      (le_refl (I ^ (n + 1))) y).trans (factor_le_rfl _)
  obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective (y.1 (n + 1))
  have hb' : y.1 (n + 1) = Ideal.Quotient.mk _ b := hb.symm
  have ha : projection f (powIndex hdef hadic n) (ofAdicCompletionFun hdef f y) =
      Ideal.Quotient.mk _ b := hstep.trans (ofAdicVal_eq_mk f y hb')
  rw [val_toAdicCompletion, toAdicValHom_eq_mk hdef hadic f _ ha,
    val_eq_mk_of_le f y (Nat.le_succ n) hb']

/-- **The completion over an adic base is an adic completion.**  The comparison map is
bijective. -/
public lemma bijective_toAdicCompletion :
    Function.Bijective (toAdicCompletion hdef hadic f) :=
  ⟨injective_toAdicCompletion hdef hadic f, surjective_toAdicCompletion hdef hadic f⟩

/-- The completion of `A` over an adic base `B` is isomorphic, as a ring, to the `IA`-adic
completion of `A`. -/
public noncomputable def adicCompletionRingEquiv :
    CompletionOver f ≃+* AdicCompletion (I.map f) A :=
  RingEquiv.ofBijective _ (bijective_toAdicCompletion hdef hadic f)

end Adic

section Flat

variable {B : Type u} {A : Type v} [CommRing B] [CommRing A] [TopologicalSpace B]
  [IsTopologicalRing B] [IsNoetherianRing A]

/-- Over an adic base, the completion of a Noetherian ring `A` over `B` is flat over `A`: it is
the `IA`-adic completion of `A`, and adic completions of Noetherian rings are flat
(Tag 00MB). -/
public theorem flat_ofTarget {I : Ideal B} (hdef : IsIdealOfDefinition I)
    (hadic : _root_.IsAdic I) (f : B →+* A) : (ofTarget f).Flat := by
  have hflat : ((toAdicCompletion hdef hadic f).comp (ofTarget f)).Flat := by
    rw [toAdicCompletion_comp_ofTarget hdef hadic f]
    exact RingHom.flat_algebraMap_iff.mpr (AdicCompletion.flat_of_isNoetherian (I.map f))
  exact (RingHom.Flat.comp_iff_of_bijective_left
    (bijective_toAdicCompletion hdef hadic f)).mp hflat

/-- Over a pre-adic base, the completion of a Noetherian ring `A` over `B` is flat over `A`. -/
public theorem flat_ofTarget_of_isPreAdic (hB : IsPreAdic B) (f : B →+* A) :
    (ofTarget f).Flat := by
  obtain ⟨I, hdef, hadic⟩ := hB
  exact flat_ofTarget hdef hadic f

/-- Over a pre-adic base, if `f` is flat and `A` is Noetherian then the canonical map from the
base into the completion of `A` over `B` is flat. -/
public theorem flat_canonicalMap (hB : IsPreAdic B) {f : B →+* A} (hf : f.Flat) :
    (canonicalMap f).Flat := by
  rw [← ofTarget_comp]
  exact hf.comp (flat_ofTarget_of_isPreAdic hB f)

/-- Over an adic base, if `f` is faithfully flat and `A` is Noetherian then the canonical map
from the base into the completion of `A` over `B` is faithfully flat.

Flatness is `flat_canonicalMap`.  For faithfulness, let `I` be an ideal of definition of `B`.
It lies in the Jacobson radical, `B` being `I`-adically complete, so a proper ideal `J` of `B`
stays proper after adding `I`.  If `J` generated the unit ideal of the completion, then pushing
through the surjection onto `B / IB` would give `JA + IA = A`, contradicting faithful flatness
of `f` at the proper ideal `J ⊔ I`.  This is the algebraic content of Tag 0AN9. -/
public theorem faithfullyFlat_canonicalMap (hB : TopologicalRing.IsAdic B) {f : B →+* A}
    (hf : f.FaithfullyFlat) : (canonicalMap f).FaithfullyFlat := by
  obtain ⟨I, hdef, hadic⟩ := hB.1
  have hjac : I ≤ Ring.jacobson B := by
    let : UniformSpace B := IsTopologicalAddGroup.rightUniformSpace B
    let : IsUniformAddGroup B := isUniformAddGroup_of_addCommGroup
    have : IsAdicComplete I B := hadic.isAdicComplete_iff.mpr ⟨hB.2.2, hB.2.1⟩
    rw [← Ideal.jacobson_bot]
    exact IsAdicComplete.le_jacobson_bot I
  have hIweak : IsWeakIdealOfDefinition I :=
    ⟨hdef.1, fun _ hx ↦ isTopologicallyNilpotent_of_mem_isIdealOfDefinition hdef hx⟩
  let Jidx : WeakIdealOfDefinitionIndex B := ⟨I, hIweak⟩
  let instBA : Algebra B A := f.toAlgebra
  let instBM : Algebra B (CompletionOver f) := (canonicalMap f).toAlgebra
  have hffBA : Module.FaithfullyFlat B A := RingHom.faithfullyFlat_algebraMap_iff.mp hf
  have hflat : Module.Flat B (CompletionOver f) :=
    RingHom.flat_algebraMap_iff.mp (flat_canonicalMap hB.1 hf.flat)
  rw [show canonicalMap f = algebraMap B (CompletionOver f) from rfl,
    RingHom.faithfullyFlat_algebraMap_iff]
  refine (Module.FaithfullyFlat.iff_flat_and_proper_ideal B (CompletionOver f)).mpr
    ⟨hflat, fun J hJ hsmul ↦ ?_⟩
  rw [Ideal.smul_top_eq_map, Submodule.restrictScalars_eq_top_iff] at hsmul
  have hsmul' : J.map (canonicalMap f) = ⊤ := hsmul
  have h1 : J.map ((projection f Jidx).comp (canonicalMap f)) = ⊤ := by
    rw [← Ideal.map_map, hsmul', Ideal.map_top]
  rw [show (projection f Jidx).comp (canonicalMap f) =
    (Ideal.Quotient.mk (extendedIdeal f Jidx)).comp f from
      RingHom.ext fun b ↦ projection_canonicalMap f Jidx b, ← Ideal.map_map] at h1
  have h2 : (J.map f) ⊔ (extendedIdeal f Jidx) = ⊤ := by
    have h3 := congrArg (Ideal.comap (Ideal.Quotient.mk (extendedIdeal f Jidx))) h1
    rwa [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective,
      ← RingHom.ker_eq_comap_bot, Ideal.mk_ker, Ideal.comap_top] at h3
  rw [show extendedIdeal f Jidx = I.map f from rfl, ← Ideal.map_sup] at h2
  obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal J hJ
  refine ((Module.FaithfullyFlat.iff_flat_and_proper_ideal B A).mp hffBA).2 (J ⊔ I)
    (fun h ↦ hm.ne_top (top_le_iff.mp
      (h ▸ sup_le hle (hjac.trans (Ring.jacobson_le_of_isMaximal m))))) ?_
  rwa [Ideal.smul_top_eq_map, Submodule.restrictScalars_eq_top_iff]

end Flat

end CompletionOver

end TopologicalRing

end
