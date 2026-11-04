module

public import Mathlib
public import Mathlib.FieldTheory.PurelyInseparable.PerfectClosure
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.LocalProperties.Reduced
public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.RingTheory.Nilpotent.GeometricallyReduced
public import Mathlib.RingTheory.Unramified.Field
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.FieldTheory.SeparableAlgebraic.Localization
public import StacksFrontier.RingTheory.CohenMacaulay.Defs
public import StacksFrontier.RingTheory.CohenMacaulay.FieldExtension
public import StacksFrontier.RingTheory.CohenMacaulay.LocusBaseChange
public import StacksFrontier.RingTheory.FormalFibres.RingMapProperty
public import StacksFrontier.RingTheory.GeometricallyNormal.Defs
public import StacksFrontier.RingTheory.GeometricallyNormal.Localization
public import StacksFrontier.RingTheory.GeometricallyNormal.Separable
public import StacksFrontier.RingTheory.GeometricallyNormal.TFAE
public import StacksFrontier.RingTheory.GeometricallyReduced.Separable
public import StacksFrontier.RingTheory.GeometricallyReduced.TFAE
public import StacksFrontier.RingTheory.GeometricallyRegular.Defs
public import StacksFrontier.RingTheory.GeometricallyRegular.FieldExtension
public import StacksFrontier.RingTheory.GeometricallyRegular.Reduced
public import StacksFrontier.RingTheory.Regular.AscentAlongRegularRingHom
public import StacksFrontier.RingTheory.Regular.RegularRingHom
public import StacksFrontier.RingTheory.Serre.Defs
public import StacksFrontier.RingTheory.Serre.FaithfullyFlatDescent
public import StacksFrontier.RingTheory.Serre.FlatAscent
public import StacksFrontier.RingTheory.Smooth.RegularRing
public import StacksFrontier.RingTheory.Depth.AlgebraMap
public import StacksFrontier.RingTheory.CohenMacaulay.Support

@[expose] public section

/-!
# Formal fibre properties: Serre's condition `(Sₙ)` and Cohen–Macaulayness

Stacks Project, Chapter 15 "More on Algebra". The tags treated here are

0BIY, 0BJ9.

## Tag 0BIY — Serre's condition and properties of formal fibres

For `n ≥ 1`, Serre's condition `(Sₙ)` has the five permanence properties used in the theory of
formal fibres: finitely generated extension of the ground field, detection on localizations,
composition with a regular map, faithfully flat descent, and restriction of the ground field.

### Main definitions

* `HasSerreCondition`: Serre's condition `(Sₙ)` for a commutative ring.

### Main results

* `serreProperty_satisfies_formalFiberAxioms`: properties (A)--(E) hold for `(Sₙ)`, `n ≥ 1`.
* `HasSerreCondition.of_isRegularRing`: a regular ring satisfies every `(Sₙ)`.

### Implementation notes

The condition is expressed with `Module.depth` and `ringKrullDim`, as in Definition 031P.
The predicate `PropertySkRing` uses a different definition of depth; the two are not compared
here. The body of `HasSerreCondition` is exposed so that importing files can use the pointwise
inequalities directly, including the characterization of Cohen–Macaulay rings used in Tag 0BJ9.

### References

* [Stacks Project, Tag 0BIY](https://stacks.math.columbia.edu/tag/0BIY)

## Tag 0BJ9 — Cohen–Macaulayness and properties of formal fibres

The property of a map from a field to a Noetherian ring that its target is Cohen–Macaulay has
the five permanence properties used in the theory of formal fibres: finitely generated extension
of the ground field, detection on localizations, composition with a regular map, faithfully flat
descent, and restriction along a separable algebraic extension of ground fields.

### Main definitions

There are no new definitions.

### Main results

* `cohenMacaulayProperty_satisfies_formalFiberAxioms`: Cohen–Macaulayness satisfies
  properties (A), (B), (C), (D), and (E) for properties of maps from fields.

### Implementation notes

A property of ring maps is represented by `RingMapProperty`. A ring `R` is expressed as
Cohen–Macaulay by `Module.IsCohenMacaulay R R`. The hypothesis identifying the property with
Cohen–Macaulayness is restricted to its intended domain, namely maps from fields to Noetherian
rings. In property (C), regularity is written as flatness together with geometric regularity of
every fibre.

### References

* [Stacks Project, Tag 0BJ9](https://stacks.math.columbia.edu/tag/0BJ9)

-/

/-! ### Stacks Tag 0BIY -/

section

section

set_option maxRecDepth 4096

open scoped TensorProduct

universe u v w

/-- Serre's condition `(Sₙ)` for a commutative ring, expressed at every prime with
`Module.depth`. On a Noetherian ring this is the condition `depth(Rₚ) ≥ min(n, dim(Rₚ))` of
Stacks 031P. -/
@[ega "IV 5.7.2" "special case", ega "IV 5.7.3", ega "IV 7.5.3"]
public def HasSerreCondition (R : Type u) [CommRing R] (n : ℕ) : Prop :=
  ∀ (p : Ideal R) [p.IsPrime],
    min (n : WithBot ℕ∞) (ringKrullDim (Localization.AtPrime p)) ≤
      (Module.depth (Localization.AtPrime p)
        (IsLocalRing.maximalIdeal (Localization.AtPrime p))
        (Localization.AtPrime p) : WithBot ℕ∞)

end

section

set_option maxRecDepth 4096

open scoped TensorProduct

universe u v w

/-- The inequality `min (n, dim) ≤ depth` of a ring transports along a ring isomorphism. -/
private lemma min_le_depth_of_ringEquiv {A B : Type*} [CommRing A] [CommRing B]
    [IsLocalRing A] [IsLocalRing B] (e : A ≃+* B) {n : ℕ}
    (h : min (n : WithBot ℕ∞) (ringKrullDim A) ≤
      (Module.depth A (IsLocalRing.maximalIdeal A) A : WithBot ℕ∞)) :
    min (n : WithBot ℕ∞) (ringKrullDim B) ≤
      (Module.depth B (IsLocalRing.maximalIdeal B) B : WithBot ℕ∞) := by
  rwa [← ringKrullDim_eq_of_ringEquiv e, ← Module.depth_self_eq_of_ringEquiv e]

/-- Serre's condition `(Sₙ)` transports along a ring isomorphism: an isomorphism matches up the
primes and induces isomorphisms of the localizations, preserving both dimension and depth. -/
public theorem HasSerreCondition.of_ringEquiv {A B : Type*} [CommRing A] [CommRing B]
    (e : A ≃+* B) {n : ℕ} (h : HasSerreCondition A n) : HasSerreCondition B n := by
  intro q _
  let p := q.comap (e : A →+* B)
  let E : Localization.AtPrime p ≃+* Localization.AtPrime q :=
    Localization.localRingEquiv p q e rfl
  exact min_le_depth_of_ringEquiv E (h p)

private lemma serre_of_isCohenMacaulay {B : Type*} [CommRing B]
    (h : Module.IsCohenMacaulay B B) (n : ℕ) : HasSerreCondition B n := by
  intro P _
  rw [← Stacks.CohenMacaulay.FiniteTypeBaseChange.isMaximalCohenMacaulay_localization_atPrime
    h P]
  exact min_le_right _ _

private lemma serre_of_isRegularRing {B : Type*} [CommRing B] [IsRegularRing B] (n : ℕ) :
    HasSerreCondition B n := by
  intro P _
  have h :=
    (IsRegularLocalRing.isRegular_and_isRegularLocalRing_quotient_and_isMaximalCohenMacaulay
      (Localization.AtPrime P)).2
  rw [Module.IsMaximalCohenMacaulay] at h
  rw [← h]
  exact min_le_right _ _

/-- **A regular ring satisfies Serre's condition `(Sₙ)` for every `n`.** Each localization at a
prime is a regular local ring, hence maximal Cohen–Macaulay over itself, so its depth is its
dimension and in particular at least `min (n, dim)`. -/
@[ega "IV 7.3.9" "(i)"]
public alias HasSerreCondition.of_isRegularRing := serre_of_isRegularRing

private noncomputable def iteratedFiberRingEquiv
    {B E C : Type*} [CommRing B] [CommRing E] [CommRing C]
    [Algebra B E] [Algebra B C] (q : Ideal B) [q.IsPrime]
    (Q : Ideal E) [Q.IsPrime] [Q.LiesOver q]
    [Algebra q.ResidueField Q.ResidueField]
    [IsScalarTower B q.ResidueField Q.ResidueField] :
    Q.Fiber (E ⊗[B] C) ≃+*
      Q.ResidueField ⊗[q.ResidueField] q.Fiber C :=
  (Algebra.TensorProduct.cancelBaseChange B E Q.ResidueField
      Q.ResidueField C).toRingEquiv.trans
    (Algebra.TensorProduct.cancelBaseChange B q.ResidueField Q.ResidueField
      Q.ResidueField C).symm.toRingEquiv

private noncomputable def fiberBaseChangeRingEquiv (k R : Type*) [Field k] [CommRing R]
    [Algebra k R] (p : Ideal R) [p.IsPrime] (K : Type*) [Field K] [Algebra k K] :
    p.Fiber (R ⊗[k] K) ≃+* p.ResidueField ⊗[k] K :=
  (Algebra.TensorProduct.cancelBaseChange k R p.ResidueField p.ResidueField K).toRingEquiv

private lemma serre_localization {R : Type*} [CommRing R] [IsNoetherianRing R] (p : Ideal R)
    [p.IsPrime] {n : ℕ} (h : HasSerreCondition R n) :
    HasSerreCondition (Localization.AtPrime p) n := by
  intro q _
  let r := q.comap (algebraMap R (Localization.AtPrime p))
  let T := Localization.AtPrime q
  have : IsScalarTower R (Localization.AtPrime p) T := inferInstance
  have hi := IsLocalization.localization_localization_isLocalization p.primeCompl q.primeCompl T
  have heq : IsLocalization.localizationLocalizationSubmodule p.primeCompl q.primeCompl =
      r.primeCompl := by
    unfold IsLocalization.localizationLocalizationSubmodule
    rw [sup_eq_left.mpr]
    · rfl
    · rintro _ ⟨x, hx, rfl⟩ hq
      have hmax : algebraMap R (Localization.AtPrime p) x ∈
          IsLocalRing.maximalIdeal (Localization.AtPrime p) :=
        (IsLocalRing.le_maximalIdeal (Ideal.IsPrime.ne_top inferInstance)) hq
      exact hx ((IsLocalization.AtPrime.to_map_mem_maximal_iff
        (Localization.AtPrime p) p x).mp hmax)
  rw [heq] at hi
  let E : Localization.AtPrime r ≃ₐ[R] T :=
    IsLocalization.algEquiv r.primeCompl _ _
  exact min_le_depth_of_ringEquiv E.toRingEquiv (h r)

private lemma serre_of_localizations {R : Type*} [CommRing R] [IsNoetherianRing R] {n : ℕ}
    (h : ∀ p : PrimeSpectrum R, HasSerreCondition (Localization.AtPrime p.asIdeal) n) :
    HasSerreCondition R n := by
  intro p _
  let m := IsLocalRing.maximalIdeal (Localization.AtPrime p)
  have hm : m.IsPrime := Ideal.IsMaximal.isPrime
    (IsLocalRing.maximalIdeal.isMaximal (Localization.AtPrime p))
  let T := Localization.AtPrime m
  have : IsLocalization m.primeCompl (Localization.AtPrime p) :=
    IsLocalization.self (fun x hx => by
      change x ∉ IsLocalRing.maximalIdeal (Localization.AtPrime p) at hx
      show IsUnit x
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hx
      exact Classical.not_not.mp hx)
  let e : T ≃ₐ[Localization.AtPrime p] Localization.AtPrime p :=
    IsLocalization.algEquiv m.primeCompl T (Localization.AtPrime p)
  exact min_le_depth_of_ringEquiv e.toRingEquiv (h ⟨p, inferInstance⟩ m)

/-- **Stacks 0BIY.** For `n ≥ 1`, the property that the target of a map from a field to a
Noetherian ring satisfies `(Sₙ)` has properties (A)--(E). -/
@[stacks 0BIY "The source fixes `n ≥ 1`, so `_hn : 1 ≤ n` is carried for faithfulness even though
the proof does not use it — each of the five axioms holds for `(Sₙ)` at every `n`. Hence the
leading underscore on that binder."]
public theorem serreProperty_satisfies_formalFiberAxioms
    (n : ℕ) (_hn : 1 ≤ n) :
    (∀ (k : Type u) (K : Type v) (R : Type w)
      [Field k] [Field K] [CommRing R] [Algebra k K]
      [Algebra k R] [IsNoetherianRing R] [Algebra.EssFiniteType k K],
      HasSerreCondition R n → HasSerreCondition (R ⊗[k] K) n) ∧
    (∀ (k : Type u) (R : Type v) [Field k] [CommRing R]
      [Algebra k R] [IsNoetherianRing R],
      (∀ p : PrimeSpectrum R,
        HasSerreCondition (Localization.AtPrime p.asIdeal) n) ↔
        HasSerreCondition R n) ∧
    (∀ (A : Type u) (B : Type v) (C : Type w)
      [CommRing A] [CommRing B] [CommRing C]
      [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
      [IsNoetherianRing A] [IsNoetherianRing B] [IsNoetherianRing C]
      [Module.Flat A B] [Module.Flat B C],
      (∀ p : PrimeSpectrum A, HasSerreCondition (p.asIdeal.Fiber B) n) →
      (∀ q : PrimeSpectrum B,
        Algebra.IsGeometricallyRegular q.asIdeal.ResidueField (q.asIdeal.Fiber C)) →
      ∀ p : PrimeSpectrum A, HasSerreCondition (p.asIdeal.Fiber C) n) ∧
    (∀ (A : Type u) (B : Type v) (C : Type w)
      [CommRing A] [CommRing B] [CommRing C]
      [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
      [IsNoetherianRing A] [IsNoetherianRing B] [IsNoetherianRing C]
      [Module.Flat A B] [Module.FaithfullyFlat B C],
      (∀ p : PrimeSpectrum A, HasSerreCondition (p.asIdeal.Fiber C) n) →
      ∀ p : PrimeSpectrum A, HasSerreCondition (p.asIdeal.Fiber B) n) ∧
    (∀ (k : Type u) (K : Type v) (R : Type w)
      [Field k] [Field K] [CommRing R]
      [Algebra k K] [Algebra k R] [Algebra K R] [IsScalarTower k K R]
      [IsNoetherianRing R] [Algebra.IsAlgebraic k K] [Algebra.IsSeparable k K],
      HasSerreCondition R n → HasSerreCondition R n) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro k K R _ _ _ _ _ _ _ hR
    have : IsNoetherianRing (R ⊗[k] K) :=
      Algebra.EssFiniteType.isNoetherianRing R (R ⊗[k] K)
    have : Module.Flat R (R ⊗[k] K) := Module.Flat.baseChange k R K
    apply min_le_depth_atPrime_of_flat (R := R) (S := R ⊗[k] K) (k := n) _ hR
    intro p _ Q _
    have hcm := (Algebra.TensorProduct.isNoetherianRing_and_isCohenMacaulay_of_essFiniteType
      k p.ResidueField K (.inr ‹Algebra.EssFiniteType k K›)).2
    exact HasSerreCondition.of_ringEquiv (fiberBaseChangeRingEquiv k R p K).symm
      (serre_of_isCohenMacaulay hcm n) Q
  · intro k R _ _ _ _
    exact ⟨serre_of_localizations, fun h p => serre_localization p h⟩
  · intro A B C _ _ _ _ _ _ _ _ _ _ _ _ hAB hreg p
    let : Algebra B (p.asIdeal.Fiber B) := Algebra.TensorProduct.rightAlgebra
    have : IsNoetherianRing (p.asIdeal.Fiber B) :=
      Stacks.Flatness.NormalFibreAscent.isNoetherianRing_fiber p.asIdeal
    let D := (p.asIdeal.Fiber B) ⊗[B] C
    let e : D ≃ₐ[p.asIdeal.ResidueField] p.asIdeal.Fiber C :=
      Algebra.IsPushout.cancelBaseChangeAlg A p.asIdeal.ResidueField B (p.asIdeal.Fiber B) C
    have : IsNoetherianRing (p.asIdeal.Fiber C) :=
      Stacks.Flatness.NormalFibreAscent.isNoetherianRing_fiber p.asIdeal
    have : IsNoetherianRing D := isNoetherianRing_of_ringEquiv _ e.symm.toRingEquiv
    have : Module.Flat (p.asIdeal.Fiber B) D := inferInstance
    apply HasSerreCondition.of_ringEquiv (A := D) e.toRingEquiv
    apply min_le_depth_atPrime_of_flat (R := p.asIdeal.Fiber B) (S := D) (k := n) _ (hAB p)
    intro Q _ Q' _
    let q : Ideal B := Q.comap (algebraMap B (p.asIdeal.Fiber B))
    have : q.IsPrime := inferInstance
    have : Q.LiesOver q := ⟨rfl⟩
    -- The residue field extension `κ(q) → κ(Q)` and its scalar towers are the canonical
    -- ones. The `Module κ(q) κ(Q)` instance is not syntactically `Algebra.toModule`, so
    -- `IsScalarTower.left` does not apply and this instance is supplied by hand.
    have : IsScalarTower q.ResidueField q.ResidueField Q.ResidueField :=
      ⟨fun x y z => mul_smul x y z⟩
    have : Algebra.IsGeometricallyRegular q.ResidueField (q.Fiber C) := hreg ⟨q, inferInstance⟩
    have hκ : Function.Bijective (algebraMap q.ResidueField Q.ResidueField) :=
      p.asIdeal.surjectiveOnStalks_residueField.baseChange'.residueFieldMap_bijective q Q rfl
    let κe : q.ResidueField ≃ₐ[q.ResidueField] Q.ResidueField :=
      AlgEquiv.ofBijective (Algebra.ofId q.ResidueField Q.ResidueField) hκ
    let Ee : (Q.ResidueField ⊗[q.ResidueField] q.Fiber C) ≃+*
        (q.ResidueField ⊗[q.ResidueField] q.Fiber C) :=
      (Algebra.TensorProduct.congr κe.symm (AlgEquiv.refl : q.Fiber C ≃ₐ[q.ResidueField]
        q.Fiber C)).toRingEquiv
    have : IsRegularRing (q.ResidueField ⊗[q.ResidueField] q.Fiber C) := inferInstance
    have : IsRegularRing (Q.ResidueField ⊗[q.ResidueField] q.Fiber C) :=
      IsRegularRing.of_ringEquiv
        (R := q.ResidueField ⊗[q.ResidueField] q.Fiber C) Ee.symm
    have hS : HasSerreCondition
        (Q.ResidueField ⊗[q.ResidueField] q.Fiber C) n :=
      serre_of_isRegularRing n
    let Eiter : Q.Fiber D ≃+*
        (Q.ResidueField ⊗[q.ResidueField] q.Fiber C) :=
      iteratedFiberRingEquiv q Q
    let : CommRing (Q.Fiber D) := by
      show CommRing (Q.ResidueField ⊗[p.asIdeal.Fiber B] D)
      exact Algebra.TensorProduct.instCommRing
        (R := p.asIdeal.Fiber B) (A := Q.ResidueField) (B := D)
    have hD : HasSerreCondition (Q.Fiber D) n :=
      HasSerreCondition.of_ringEquiv (A := Q.ResidueField ⊗[q.ResidueField] q.Fiber C)
        (B := Q.Fiber D) Eiter.symm hS
    exact hD Q'
  · intro A B C _ _ _ _ _ _ _ _ _ _ _ _ hAC p
    let : Algebra B (p.asIdeal.Fiber B) := Algebra.TensorProduct.rightAlgebra
    let D := (p.asIdeal.Fiber B) ⊗[B] C
    let e : D ≃ₐ[p.asIdeal.ResidueField] p.asIdeal.Fiber C :=
      Algebra.IsPushout.cancelBaseChangeAlg A p.asIdeal.ResidueField B (p.asIdeal.Fiber B) C
    have : IsNoetherianRing (p.asIdeal.Fiber C) :=
      Stacks.Flatness.NormalFibreAscent.isNoetherianRing_fiber p.asIdeal
    have : IsNoetherianRing D := isNoetherianRing_of_ringEquiv _ e.symm.toRingEquiv
    have : Module.FaithfullyFlat (p.asIdeal.Fiber B) D := inferInstance
    exact (isNoetherianRing_and_min_le_depth_atPrime_of_faithfullyFlat
      (HasSerreCondition.of_ringEquiv (A := p.asIdeal.Fiber C) (B := D)
        e.symm.toRingEquiv (hAC p))).2
  · intros
    assumption

end

end

/-! ### Stacks Tag 0BJ9 -/

section

section

open scoped TensorProduct

attribute [local instance] Algebra.TensorProduct.rightAlgebra

universe u

private lemma depth_self_le_ringKrullDim (R : Type*) [CommRing R] [IsLocalRing R] :
    (Module.depth R (IsLocalRing.maximalIdeal R) R : WithBot ℕ∞) ≤ ringKrullDim R := by
  rw [← Module.supportDim_self_eq_ringKrullDim]
  exact Module.depth_le_supportDim R _ R (by
    simpa using (IsLocalRing.maximalIdeal.isMaximal R).ne_top)

private lemma eq_of_min_nat_le (d : WithBot ℕ∞) (x : ℕ∞) (hx : (x : WithBot ℕ∞) ≤ d)
    (hd : d ≠ ⊤) (h : ∀ n : ℕ, 1 ≤ n → min (n : WithBot ℕ∞) d ≤ x) :
    (x : WithBot ℕ∞) = d := by
  apply le_antisymm hx
  rcases eq_or_ne d ⊥ with rfl | hd_bot
  · exact bot_le
  lift d to ℕ∞ using (by simp [hd_bot]) with d
  induction d using ENat.recTopCoe with
  | top => exact (hd (by simp)).elim
  | coe d =>
    by_cases hzero : d = 0
    · subst d
      simp
    · simpa [min_eq_left] using h d (Nat.one_le_iff_ne_zero.mpr hzero)

private lemma isCohenMacaulay_iff_forall_serre (R : Type*) [CommRing R] [IsNoetherianRing R] :
    Module.IsCohenMacaulay R R ↔ ∀ n : ℕ, HasSerreCondition R n := by
  simp only [Module.IsCohenMacaulay, Module.support_self, Set.mem_univ, forall_const,
    HasSerreCondition, Module.supportDim_self_eq_ringKrullDim]
  constructor
  · intro h n p hp
    rw [h ⟨p, hp⟩]
    exact min_le_right _ _
  · intro h p
    apply eq_of_min_nat_le _ _ (depth_self_le_ringKrullDim _)
      (ringKrullDim_ne_top (R := Localization.AtPrime p.asIdeal))
    intro n hn
    exact h n p.asIdeal

/-- **Stacks 0BJ9.** The property of a map from a field to a Noetherian ring that its target is
Cohen–Macaulay satisfies properties (A)--(E): it is preserved by finitely generated field
extension, is local on the target, passes through a composition of flat maps when the second map
is regular, descends through a faithfully flat second map, and is unchanged upon replacing the
ground field by a separable algebraic extension. -/
@[stacks 0BJ9, ega "IV 7.5.3" "(iii) Cohen-Macaulay"]
public theorem cohenMacaulayProperty_satisfies_formalFiberAxioms
    (P : RingMapProperty.{u, u})
    (hP : ∀ (k R : Type u) [Field k] [CommRing R] [Algebra k R]
      [IsNoetherianRing R], P (algebraMap k R) ↔ Module.IsCohenMacaulay R R) :
    (∀ (k K R : Type u) [Field k] [Field K] [CommRing R] [Algebra k K]
      [Algebra k R] [IsNoetherianRing R] [Algebra.EssFiniteType k K],
      P (algebraMap k R) →
        P (Algebra.TensorProduct.includeRight (R := k) (A := R) (B := K)).toRingHom) ∧
    (∀ (k R : Type u) [Field k] [CommRing R] [Algebra k R] [IsNoetherianRing R],
      (∀ p : PrimeSpectrum R,
        P (algebraMap k (Localization.AtPrime p.asIdeal))) ↔ P (algebraMap k R)) ∧
    (∀ (A B C : Type u) [CommRing A] [CommRing B] [CommRing C]
      [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
      [IsNoetherianRing A] [IsNoetherianRing B] [IsNoetherianRing C]
      [Module.Flat A B] [Module.Flat B C],
      (∀ p : PrimeSpectrum A,
        P (algebraMap p.asIdeal.ResidueField (p.asIdeal.Fiber B))) →
      (∀ q : PrimeSpectrum B,
        Algebra.IsGeometricallyRegular q.asIdeal.ResidueField (q.asIdeal.Fiber C)) →
      ∀ p : PrimeSpectrum A,
        P (algebraMap p.asIdeal.ResidueField (p.asIdeal.Fiber C))) ∧
    (∀ (A B C : Type u) [CommRing A] [CommRing B] [CommRing C]
      [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
      [IsNoetherianRing A] [IsNoetherianRing B] [IsNoetherianRing C]
      [Module.Flat A B] [Module.FaithfullyFlat B C],
      (∀ p : PrimeSpectrum A,
        P (algebraMap p.asIdeal.ResidueField (p.asIdeal.Fiber C))) →
      ∀ p : PrimeSpectrum A,
        P (algebraMap p.asIdeal.ResidueField (p.asIdeal.Fiber B))) ∧
    (∀ (k K R : Type u) [Field k] [Field K] [CommRing R]
      [Algebra k K] [Algebra k R] [Algebra K R] [IsScalarTower k K R]
      [IsNoetherianRing R] [Algebra.IsAlgebraic k K] [Algebra.IsSeparable k K],
      P (algebraMap k R) → P (algebraMap K R)) := by
  have key (k R : Type u) [Field k] [CommRing R] [Algebra k R] [IsNoetherianRing R] :
      P (algebraMap k R) ↔ ∀ n, 1 ≤ n → HasSerreCondition R n := by
    rw [hP, isCohenMacaulay_iff_forall_serre]
    refine ⟨fun h n _ ↦ h n, fun h n ↦ ?_⟩
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · exact fun _ _ ↦ by simp
    · exact h n hn
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro k K R _ _ _ _ _ _ _ h
    have : Algebra.EssFiniteType R (R ⊗[k] K) :=
      Algebra.EssFiniteType.baseChange k K R
    have : IsNoetherianRing (R ⊗[k] K) :=
      Algebra.EssFiniteType.isNoetherianRing R (R ⊗[k] K)
    rw [key] at h
    show P (algebraMap K (R ⊗[k] K))
    rw [key]
    exact fun n hn ↦ (serreProperty_satisfies_formalFiberAxioms.{u, u, u} n hn).1 k K R (h n hn)
  · intro k R _ _ _ _
    simp_rw [key]
    exact ⟨fun h n hn ↦
        ((serreProperty_satisfies_formalFiberAxioms.{u, u, u} n hn).2.1 k R).mp fun p ↦ h p n hn,
      fun h p n hn ↦
        ((serreProperty_satisfies_formalFiberAxioms.{u, u, u} n hn).2.1 k R).mpr (h n hn) p⟩
  · intro A B C _ _ _ _ _ _ _ _ _ _ _ _ hAB hreg p
    have := Stacks.Flatness.NormalFibreAscent.isNoetherianRing_fiber (S := C) p.asIdeal
    rw [key]
    exact fun n hn ↦
      (serreProperty_satisfies_formalFiberAxioms.{u, u, u} n hn).2.2.1 A B C
        (fun q ↦ by
          have := Stacks.Flatness.NormalFibreAscent.isNoetherianRing_fiber (S := B) q.asIdeal
          exact (key _ _).mp (hAB q) n hn)
        hreg p
  · intro A B C _ _ _ _ _ _ _ _ _ _ _ _ hAC p
    have := Stacks.Flatness.NormalFibreAscent.isNoetherianRing_fiber (S := B) p.asIdeal
    rw [key]
    exact fun n hn ↦
      (serreProperty_satisfies_formalFiberAxioms.{u, u, u} n hn).2.2.2.1 A B C
        (fun q ↦ by
          have := Stacks.Flatness.NormalFibreAscent.isNoetherianRing_fiber (S := C) q.asIdeal
          exact (key _ _).mp (hAC q) n hn) p
  · intro k K R _ _ _ _ _ _ _ _ _ _ h
    exact (hP K R).mpr ((hP k R).mp h)

end

end

end
