module

public import Mathlib.Algebra.Homology.Homotopy
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.AdicCompletion.Topology
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.AdicCompletion.Basic
public import StacksFrontier.RingTheory.AdicCompletion.QuasiFinite
public import StacksFrontier.RingTheory.NaiveCotangent.Defs
public import StacksFrontier.RingTheory.Rig.NaiveCotangent
public import StacksFrontier.Topology.Algebra.AdicTopology.Continuous

/-!
# Independence of the completed naive cotangent complex from its presentation

Let `A` be a Noetherian ring, `I` an ideal of `A`, and `B` an `I`-adically complete `A`-algebra
of finite type modulo `I`. The two-term completed naive cotangent complexes obtained from any
two completed polynomial presentations of `B` are homotopy equivalent as complexes of
`B`-modules.

## Main definitions

* `Rig.completedSubstitution`: the continuous `A`-algebra map between the completed polynomial
  rings of two presentations, sending each variable of the first to a lift of its image in `B`.
* `Rig.completedPresentationChainMap`: the morphism of completed naive cotangent complexes it
  induces.

## Main results

* `Rig.completedNaiveCotangentComplex_homotopyEquiv`: the completed naive cotangent complex
  does not depend on the chosen completed polynomial presentation.

## References

* [Stacks Project, Tag 0GAE](https://stacks.math.columbia.edu/tag/0GAE)
-/

@[expose] public noncomputable section

open CategoryTheory
open Rig.CompletedPolynomialPresentation
open Rig.CompletedNaiveCotangentComplex

universe u v

namespace Rig

/- The following identifications hold at `implicit` transparency in this file:

* `P.extension.Ring` is `P.completedPolynomialRing`;
* `(Algebra.Extension.ofSurjective f h).Ring` is the source of `f`;
* `K.cochainComplex` is `HomologicalComplex.double (ModuleCat.ofHom K.liftedDifferential) _`. -/
attribute [local implicit_reducible] CompletedPolynomialPresentation.extension
  Algebra.Extension.ofSurjective CompletedNaiveCotangentComplex.cochainComplex

/-- The `P.completedPolynomialRing`-algebra structure on `B` given by the presentation `P`. -/
public noncomputable abbrev completedPolynomialPresentationAlgebra
    {A : Type u} [CommRing A] {I : Ideal A}
    {B : AdicFiniteTypeAlgebra.{u, v} A I}
    (P : CompletedPolynomialPresentation I B) :
    Algebra P.completedPolynomialRing B.carrier := P.extension.algebra₂

attribute [local instance] completedPolynomialPresentationAlgebra

/-- The actions of `A` and of `P.completedPolynomialRing` on `B` form a scalar tower. -/
public theorem completedPolynomialScalarTower
    {A : Type u} [CommRing A] {I : Ideal A}
    {B : AdicFiniteTypeAlgebra.{u, v} A I}
    (P : CompletedPolynomialPresentation I B) :
    IsScalarTower A P.completedPolynomialRing B.carrier := P.extension.isScalarTower

attribute [local instance] completedPolynomialScalarTower

/-- The `P.completedPolynomialRing`-module structure on the cotangent module
`P.extension.Cotangent`. -/
public noncomputable abbrev completedCotangentModule
    {A : Type u} [CommRing A] {I : Ideal A}
    {B : AdicFiniteTypeAlgebra.{u, v} A I}
    (P : CompletedPolynomialPresentation I B) :
    Module P.completedPolynomialRing P.extension.Cotangent :=
  inferInstanceAs (Module P.extension.Ring P.extension.Cotangent)

attribute [local instance] completedCotangentModule

/-- The actions of `A` and of `P.completedPolynomialRing` on `P.extension.Cotangent` form a scalar
tower. -/
public theorem completedCotangentScalarTower
    {A : Type u} [CommRing A] {I : Ideal A}
    {B : AdicFiniteTypeAlgebra.{u, v} A I}
    (P : CompletedPolynomialPresentation I B) :
    IsScalarTower A P.completedPolynomialRing P.extension.Cotangent :=
  inferInstanceAs (IsScalarTower A P.extension.Ring P.extension.Cotangent)

attribute [local instance] completedCotangentScalarTower

/-- The formal partial derivatives recorded by the completed naive cotangent complex of `P` are
`Rig.completedPartialDeriv P`. -/
private theorem completedNaiveCotangentComplex_partialDeriv
    {A : Type u} [CommRing A] [IsNoetherianRing A] {I : Ideal A}
    {B : AdicFiniteTypeAlgebra.{u, v} A I}
    (P : CompletedPolynomialPresentation I B) (i : Fin P.variableCount) :
    (Rig.completedNaiveCotangentComplex B P).partialDeriv i = completedPartialDeriv P i := rfl

/-- The cotangent module `P.extension.Cotangent` of a completed polynomial presentation is adically
complete for the ideal `B.adicIdeal`. -/
public theorem completedCotangent_isAdicComplete
    {A : Type u} [CommRing A] [IsNoetherianRing A] {I : Ideal A}
    {B : AdicFiniteTypeAlgebra.{u, v} A I}
    (P : CompletedPolynomialPresentation I B) :
    IsAdicComplete B.adicIdeal P.extension.Cotangent := by
  let : IsNoetherianRing P.completedPolynomialRing :=
    AdicCompletion.isNoetherianRing
      (I.map (MvPolynomial.C : A →+*
        MvPolynomial (Fin P.variableCount) A))
  let : IsAdicComplete B.adicIdeal B.carrier := B.isAdicallyComplete
  let : Module.Finite B.carrier P.extension.Cotangent :=
    Algebra.Extension.Cotangent.finite (P := P.extension) (by
      show P.ker.FG
      exact Ideal.fg_of_isNoetherianRing P.ker)
  have hsep : ⨅ n : ℕ, B.adicIdeal ^ n • (⊤ : Submodule B.carrier
      P.extension.Cotangent) = ⊥ :=
    Ideal.iInf_pow_smul_eq_bot_of_le_jacobson B.adicIdeal
      (IsAdicComplete.le_jacobson_bot B.adicIdeal)
  exact isAdicComplete_of_iInf_smul_eq_bot B.adicIdeal hsep

/-- Two `A`-derivations from `P.completedPolynomialRing` into a Hausdorff topological ring `S`
which are continuous for the limit topology and agree on polynomials are equal. -/
public theorem completedPolynomialDerivation_ext
    {A : Type u} [CommRing A] [IsNoetherianRing A] {I : Ideal A}
    {B : AdicFiniteTypeAlgebra.{u, v} A I}
    (P : CompletedPolynomialPresentation I B) {S : Type*} [CommRing S]
    [Algebra A S] [Algebra P.completedPolynomialRing S]
    [IsScalarTower A P.completedPolynomialRing S] [TopologicalSpace S] [T2Space S]
    (D E : Derivation A P.completedPolynomialRing S)
    (hD : @Continuous P.completedPolynomialRing S
      (RestrictedPowerSeries.polynomialCompletionLimitTopology I
        (Fin P.variableCount)) ‹TopologicalSpace S› D)
    (hE : @Continuous P.completedPolynomialRing S
      (RestrictedPowerSeries.polynomialCompletionLimitTopology I
        (Fin P.variableCount)) ‹TopologicalSpace S› E)
    (hpoly : ∀ f : MvPolynomial (Fin P.variableCount) A,
      D (algebraMap (MvPolynomial (Fin P.variableCount) A)
        P.completedPolynomialRing f) =
      E (algebraMap (MvPolynomial (Fin P.variableCount) A)
        P.completedPolynomialRing f)) : D = E := by
  let : TopologicalSpace P.completedPolynomialRing :=
    RestrictedPowerSeries.polynomialCompletionLimitTopology I
      (Fin P.variableCount)
  exact Derivation.ext (congrFun ((denseRange_completedPolynomials P).equalizer hD hE
    (funext hpoly)))

/-- Every element of the completed polynomial ring is congruent to a polynomial modulo the `n`-th
power of the extension of `I`. -/
private theorem exists_sub_algebraMap_mem_pow
    {A : Type u} [CommRing A] [IsNoetherianRing A] {I : Ideal A}
    {B : AdicFiniteTypeAlgebra.{u, v} A I}
    (P : CompletedPolynomialPresentation I B) (x : P.completedPolynomialRing) (n : ℕ) :
    ∃ f : MvPolynomial (Fin P.variableCount) A,
      x - algebraMap (MvPolynomial (Fin P.variableCount) A) P.completedPolynomialRing f ∈
        (I.map (algebraMap A P.completedPolynomialRing)) ^ n := by
  let R := MvPolynomial (Fin P.variableCount) A
  let J : Ideal R := I.map (MvPolynomial.C : A →+* R)
  let : IsNoetherianRing R := inferInstance
  obtain ⟨f, hf⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ J n x)
  refine ⟨f, ?_⟩
  have heval : AdicCompletion.evalₐ J n x =
      AdicCompletion.evalₐ J n (algebraMap R P.completedPolynomialRing f) := by
    rw [AdicCompletion.algebraMap_apply, AdicCompletion.evalₐ_of]
    exact hf.symm
  have hker : x - algebraMap R P.completedPolynomialRing f ∈
      (AdicCompletion.eval J R n).ker := by
    rw [LinearMap.mem_ker]
    have hzero : AdicCompletion.evalₐ J n
        (x - algebraMap R P.completedPolynomialRing f) = 0 := by
      rw [map_sub, heval, sub_self]
    have hfactor := congrArg
      (Ideal.Quotient.factor (show J ^ n ≤ J ^ n • (⊤ : Ideal R) by simp)) hzero
    simpa only [AdicCompletion.factor_evalₐ_eq_eval, map_zero] using hfactor
  have hpow : x - algebraMap R P.completedPolynomialRing f ∈
      J ^ n • (⊤ : Submodule R P.completedPolynomialRing) := by
    rwa [AdicCompletion.pow_smul_top_eq_ker_eval
      (I := J) (M := R) (n := n) (Ideal.fg_of_isNoetherianRing J)]
  have hK : Ideal.map (algebraMap R P.completedPolynomialRing) J =
      I.map (algebraMap A P.completedPolynomialRing) := by
    dsimp [J]
    rw [Ideal.map_map]
    congr 1
  rwa [Ideal.smul_top_eq_map, Ideal.map_pow, hK] at hpow

/-- Two `A`-derivations from `P.completedPolynomialRing` into an `I`-adically separated module `M`
which agree on polynomials, and which both carry the `n`-th power of the extension of `I`
into `I ^ n • M` for every `n`, are equal. -/
public theorem completedPolynomialDerivation_ext_adic
    {A : Type u} [CommRing A] [IsNoetherianRing A] {I : Ideal A}
    {B : AdicFiniteTypeAlgebra.{u, v} A I}
    (P : CompletedPolynomialPresentation I B)
    {M : Type*} [AddCommGroup M] [Module A M]
    [Module P.completedPolynomialRing M]
    [IsScalarTower A P.completedPolynomialRing M]
    (D E : Derivation A P.completedPolynomialRing M)
    (hD : ∀ n (x : P.completedPolynomialRing),
      x ∈ (I.map (algebraMap A P.completedPolynomialRing)) ^ n →
        D x ∈ I ^ n • (⊤ : Submodule A M))
    (hE : ∀ n (x : P.completedPolynomialRing),
      x ∈ (I.map (algebraMap A P.completedPolynomialRing)) ^ n →
        E x ∈ I ^ n • (⊤ : Submodule A M))
    (hpoly : ∀ f : MvPolynomial (Fin P.variableCount) A,
      D (algebraMap (MvPolynomial (Fin P.variableCount) A)
        P.completedPolynomialRing f) =
      E (algebraMap (MvPolynomial (Fin P.variableCount) A)
        P.completedPolynomialRing f))
    (hsep : ⨅ n : ℕ, I ^ n • (⊤ : Submodule A M) = ⊥) : D = E := by
  apply Derivation.ext
  intro x
  have hmem (n : ℕ) : D x - E x ∈ I ^ n • (⊤ : Submodule A M) := by
    obtain ⟨f, hf⟩ := exists_sub_algebraMap_mem_pow P x n
    have hEq : D x - E x =
        D (x - algebraMap _ P.completedPolynomialRing f) -
          E (x - algebraMap _ P.completedPolynomialRing f) := by
      rw [map_sub, map_sub, hpoly f]
      abel
    rw [hEq]
    exact sub_mem (hD n _ hf) (hE n _ hf)
  have hmem' : D x - E x ∈ ⨅ n : ℕ, I ^ n • (⊤ : Submodule A M) :=
    (Submodule.mem_iInf _).2 hmem
  rw [hsep] at hmem'
  have hzero : D x - E x = 0 := by simpa using hmem'
  exact sub_eq_zero.mp hzero

/-- **Chain rule.** For a derivation `D` of `S` and an `A`-algebra map `φ` out of a polynomial
ring, `D (φ f) = ∑ i, φ (∂f/∂Xᵢ) * D (φ Xᵢ)`. -/
public theorem mvPolynomial_derivation_chainRule
    {A : Type u} [CommRing A] {S : Type*} [CommRing S] [Algebra A S]
    {ι : Type*} [Fintype ι]
    (D : Derivation A S S) (φ : MvPolynomial ι A →ₐ[A] S)
    (f : MvPolynomial ι A) :
    D (φ f) = ∑ i, φ (MvPolynomial.pderiv i f) * D (φ (MvPolynomial.X i)) := by
  classical
  induction f using MvPolynomial.induction_on with
  | C a => simp
  | add f g hf hg =>
      rw [map_add, D.map_add, hf, hg]
      simp only [map_add]
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      ring
  | mul_X f i hf =>
      rw [map_mul, D.leibniz, hf]
      simp_rw [MvPolynomial.pderiv_mul]
      simp only [map_add, map_mul]
      have hsum :
          (∑ j, (φ (MvPolynomial.pderiv j f) * φ (MvPolynomial.X i) +
            φ f * φ (MvPolynomial.pderiv j (MvPolynomial.X i))) *
              D (φ (MvPolynomial.X j))) =
            (∑ j, φ (MvPolynomial.pderiv j f) * φ (MvPolynomial.X i) *
                D (φ (MvPolynomial.X j))) +
              ∑ j, φ f * φ (MvPolynomial.pderiv j (MvPolynomial.X i)) *
                D (φ (MvPolynomial.X j)) := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro j hj
        ring
      rw [hsum]
      simp only [smul_eq_mul]
      rw [Finset.mul_sum]
      simp [MvPolynomial.pderiv_X, Pi.single_apply,
        mul_left_comm, mul_comm]
      ac_rfl

/-- A chosen element of `Q.completedPolynomialRing` with the same image in `B` as the `i`-th
variable of `P`. -/
public noncomputable def completedSubstitutionCoordinate
    {A : Type u} [CommRing A] {I : Ideal A}
    {B : AdicFiniteTypeAlgebra.{u, v} A I}
    (P Q : CompletedPolynomialPresentation I B) (i : Fin P.variableCount) :
    Q.completedPolynomialRing :=
  Classical.choose (Q.toAlgHom_surjective
    (P.toAlgHom (algebraMap (MvPolynomial (Fin P.variableCount) A)
      P.completedPolynomialRing (MvPolynomial.X i))))

/-- The element `completedSubstitutionCoordinate P Q i` has the same image in `B` as the `i`-th
variable of `P`. -/
public theorem completedSubstitutionCoordinate_spec
    {A : Type u} [CommRing A] {I : Ideal A}
    {B : AdicFiniteTypeAlgebra.{u, v} A I}
    (P Q : CompletedPolynomialPresentation I B) (i : Fin P.variableCount) :
    Q.toAlgHom (completedSubstitutionCoordinate P Q i) =
      P.toAlgHom (algebraMap (MvPolynomial (Fin P.variableCount) A)
        P.completedPolynomialRing (MvPolynomial.X i)) :=
  Classical.choose_spec (Q.toAlgHom_surjective _)

/-- The `A`-algebra map from the polynomial ring of `P` to the quotient of the polynomial ring of
`Q` by the `n`-th power of the extension of `I`, sending the `i`-th variable to the image of
`completedSubstitutionCoordinate P Q i`. -/
public noncomputable def completedSubstitutionPolynomialLevel
    {A : Type u} [CommRing A] {I : Ideal A}
    {B : AdicFiniteTypeAlgebra.{u, v} A I}
    (P Q : CompletedPolynomialPresentation I B) (n : ℕ) :
    MvPolynomial (Fin P.variableCount) A →ₐ[A]
      MvPolynomial (Fin Q.variableCount) A ⧸
        (I.map (MvPolynomial.C : A →+* MvPolynomial (Fin Q.variableCount) A)) ^ n :=
  MvPolynomial.aeval (fun i => AdicCompletion.evalₐ
    (I.map (MvPolynomial.C : A →+* MvPolynomial (Fin Q.variableCount) A)) n
    (completedSubstitutionCoordinate P Q i))

/-- The maps `completedSubstitutionPolynomialLevel P Q n` are compatible with the projections
between the quotients by the powers of the extension of `I`. -/
public theorem completedSubstitutionPolynomialLevel_compatible
    {A : Type u} [CommRing A] {I : Ideal A}
    {B : AdicFiniteTypeAlgebra.{u, v} A I}
    (P Q : CompletedPolynomialPresentation I B) {m n : ℕ} (hmn : m ≤ n) :
    (Ideal.Quotient.factorₐ A (Ideal.pow_le_pow_right hmn)).comp
      (completedSubstitutionPolynomialLevel P Q n) =
        completedSubstitutionPolynomialLevel P Q m := by
  apply MvPolynomial.algHom_ext
  intro i
  simp only [AlgHom.comp_apply, completedSubstitutionPolynomialLevel,
    MvPolynomial.aeval_X]
  exact AdicCompletion.factor_evalₐ _ hmn _

/-- The `A`-algebra map between the quotients of the polynomial rings of `P` and `Q` by the `n`-th
powers of the extensions of `I` induced by `completedSubstitutionPolynomialLevel P Q n`. -/
public noncomputable def completedSubstitutionQuotientLift
    {A : Type u} [CommRing A] {I : Ideal A}
    {B : AdicFiniteTypeAlgebra.{u, v} A I}
    (P Q : CompletedPolynomialPresentation I B) (n : ℕ) :
    (MvPolynomial (Fin P.variableCount) A ⧸
      (I.map (MvPolynomial.C : A →+* MvPolynomial (Fin P.variableCount) A)) ^ n) →ₐ[A]
    MvPolynomial (Fin Q.variableCount) A ⧸
      (I.map (MvPolynomial.C : A →+* MvPolynomial (Fin Q.variableCount) A)) ^ n := by
  let φ := completedSubstitutionPolynomialLevel P Q n
  let KP := I.map (MvPolynomial.C : A →+* MvPolynomial (Fin P.variableCount) A)
  let KQ := I.map (MvPolynomial.C : A →+* MvPolynomial (Fin Q.variableCount) A)
  have hmap : Ideal.map φ.toRingHom KP ≤
      Ideal.map (Ideal.Quotient.mk (KQ ^ n)) KQ := by
    have hconst : φ.toRingHom.comp (MvPolynomial.C : A →+* MvPolynomial (Fin P.variableCount) A) =
        (Ideal.Quotient.mk (KQ ^ n)).comp
          (MvPolynomial.C : A →+* MvPolynomial (Fin Q.variableCount) A) := by
      ext a
      calc
        completedSubstitutionPolynomialLevel P Q n (MvPolynomial.C a) =
            algebraMap A _ a := by
              simp [completedSubstitutionPolynomialLevel]
        _ = Ideal.Quotient.mk (KQ ^ n)
              (algebraMap A (MvPolynomial (Fin Q.variableCount) A) a) :=
            (Ideal.Quotient.mk_algebraMap A (KQ ^ n) a).symm
        _ = Ideal.Quotient.mk (KQ ^ n) (MvPolynomial.C a) := by
            rfl
    change Ideal.map φ.toRingHom
        (I.map (MvPolynomial.C : A →+* MvPolynomial (Fin P.variableCount) A)) ≤
      Ideal.map (Ideal.Quotient.mk (KQ ^ n))
        (I.map (MvPolynomial.C : A →+* MvPolynomial (Fin Q.variableCount) A))
    rw [Ideal.map_map, Ideal.map_map, hconst]
  have hzero : Ideal.map φ.toRingHom (KP ^ n) = ⊥ := by
    rw [Ideal.map_pow]
    apply le_antisymm
    · calc
        (Ideal.map φ.toRingHom KP) ^ n ≤ (Ideal.map (Ideal.Quotient.mk (KQ ^ n)) KQ) ^ n :=
          pow_le_pow_left' hmap n
        _ = Ideal.map (Ideal.Quotient.mk (KQ ^ n)) (KQ ^ n) := (Ideal.map_pow _ _ _).symm
        _ = ⊥ := (Ideal.map_eq_bot_iff_le_ker _).2 (by simp)
    · exact bot_le
  exact Ideal.Quotient.liftₐ (KP ^ n) φ (fun x hx => by
    have hx' : φ x ∈ Ideal.map φ.toRingHom (KP ^ n) := Ideal.mem_map_of_mem _ hx
    rw [hzero] at hx'
    exact Ideal.mem_bot.mp hx')

/-- The map `completedSubstitutionQuotientLift P Q n` composed with the quotient map is
`completedSubstitutionPolynomialLevel P Q n`. -/
public theorem completedSubstitutionQuotientLift_comp_mk
    {A : Type u} [CommRing A] {I : Ideal A}
    {B : AdicFiniteTypeAlgebra.{u, v} A I}
    (P Q : CompletedPolynomialPresentation I B) (n : ℕ)
    :
    (completedSubstitutionQuotientLift P Q n).comp
        (Ideal.Quotient.mkₐ A
          ((I.map (MvPolynomial.C : A →+* MvPolynomial (Fin P.variableCount) A)) ^ n)) =
      completedSubstitutionPolynomialLevel P Q n := by
  unfold completedSubstitutionQuotientLift
  exact Ideal.Quotient.liftₐ_comp _ _ _

/-- The map `completedSubstitutionQuotientLift P Q n` sends the class of a polynomial `x` to
`completedSubstitutionPolynomialLevel P Q n x`. -/
public theorem completedSubstitutionQuotientLift_mk
    {A : Type u} [CommRing A] {I : Ideal A}
    {B : AdicFiniteTypeAlgebra.{u, v} A I}
    (P Q : CompletedPolynomialPresentation I B) (n : ℕ)
    (x : MvPolynomial (Fin P.variableCount) A) :
    completedSubstitutionQuotientLift P Q n (Ideal.Quotient.mk _ x) =
      completedSubstitutionPolynomialLevel P Q n x := by
  have h := completedSubstitutionQuotientLift_comp_mk P Q n
  simpa only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk] using
    DFunLike.congr_fun h x

/-- The maps `completedSubstitutionQuotientLift P Q n` commute with the projections between the
quotients by the powers of the extensions of `I`. -/
public theorem completedSubstitutionQuotientLift_compatible
    {A : Type u} [CommRing A] {I : Ideal A}
    {B : AdicFiniteTypeAlgebra.{u, v} A I}
    (P Q : CompletedPolynomialPresentation I B) {m n : ℕ} (hmn : m ≤ n) :
    (Ideal.Quotient.factorₐ A (Ideal.pow_le_pow_right hmn)).comp
      (completedSubstitutionQuotientLift P Q n) =
        (completedSubstitutionQuotientLift P Q m).comp
          (Ideal.Quotient.factorₐ A (Ideal.pow_le_pow_right hmn)) := by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  intro x
  show ((Ideal.Quotient.factorₐ A (Ideal.pow_le_pow_right hmn)).comp
      (completedSubstitutionQuotientLift P Q n)).comp
        (Ideal.Quotient.mkₐ A
          ((I.map (MvPolynomial.C : A →+* MvPolynomial (Fin P.variableCount) A)) ^ n))
        (MvPolynomial.X x) =
    ((completedSubstitutionQuotientLift P Q m).comp
      (Ideal.Quotient.factorₐ A (Ideal.pow_le_pow_right hmn))).comp
        (Ideal.Quotient.mkₐ A
          ((I.map (MvPolynomial.C : A →+* MvPolynomial (Fin P.variableCount) A)) ^ n))
        (MvPolynomial.X x)
  simp only [AlgHom.comp_assoc]
  rw [completedSubstitutionQuotientLift_comp_mk,
    Ideal.Quotient.factorₐ_comp_mk,
    completedSubstitutionQuotientLift_comp_mk]
  exact DFunLike.congr_fun (completedSubstitutionPolynomialLevel_compatible P Q hmn)
    (MvPolynomial.X x)

/-- The `n`-th level of the substitution: the projection of `P.completedPolynomialRing` to its
`n`-th quotient followed by `completedSubstitutionQuotientLift P Q n`. -/
public noncomputable def completedSubstitutionLevel
    {A : Type u} [CommRing A] {I : Ideal A}
    {B : AdicFiniteTypeAlgebra.{u, v} A I}
    (P Q : CompletedPolynomialPresentation I B) (n : ℕ) :
    P.completedPolynomialRing →ₐ[A]
      MvPolynomial (Fin Q.variableCount) A ⧸
        (I.map (MvPolynomial.C : A →+* MvPolynomial (Fin Q.variableCount) A)) ^ n :=
  (completedSubstitutionQuotientLift P Q n).comp
      ((AdicCompletion.evalₐ
        (I.map (MvPolynomial.C : A →+* MvPolynomial (Fin P.variableCount) A)) n).restrictScalars A)

/-- The maps `completedSubstitutionLevel P Q n` are compatible with the projections between the
quotients by the powers of the extension of `I`. -/
public theorem completedSubstitutionLevel_compatible
    {A : Type u} [CommRing A] {I : Ideal A}
    {B : AdicFiniteTypeAlgebra.{u, v} A I}
    (P Q : CompletedPolynomialPresentation I B) {m n : ℕ} (hmn : m ≤ n) :
    (Ideal.Quotient.factorₐ A (Ideal.pow_le_pow_right hmn)).comp
      (completedSubstitutionLevel P Q n) = completedSubstitutionLevel P Q m := by
  have hq := completedSubstitutionQuotientLift_compatible P Q hmn
  have hp : (Ideal.Quotient.factorₐ A (Ideal.pow_le_pow_right hmn)).comp
      ((AdicCompletion.evalₐ (I.map (MvPolynomial.C :
          A →+* MvPolynomial (Fin P.variableCount) A)) n).restrictScalars A) =
      (AdicCompletion.evalₐ (I.map (MvPolynomial.C :
          A →+* MvPolynomial (Fin P.variableCount) A)) m).restrictScalars A := by
    ext x
    exact AdicCompletion.factor_evalₐ _ hmn x
  apply AlgHom.ext
  intro x
  show Ideal.Quotient.factorₐ A (Ideal.pow_le_pow_right hmn)
      (completedSubstitutionQuotientLift P Q n
        (AdicCompletion.evalₐ
          (I.map (MvPolynomial.C : A →+* MvPolynomial (Fin P.variableCount) A)) n x)) =
    completedSubstitutionQuotientLift P Q m
      (AdicCompletion.evalₐ
        (I.map (MvPolynomial.C : A →+* MvPolynomial (Fin P.variableCount) A)) m x)
  calc
    _ = completedSubstitutionQuotientLift P Q m
        (Ideal.Quotient.factorₐ A (Ideal.pow_le_pow_right hmn)
          (AdicCompletion.evalₐ
            (I.map (MvPolynomial.C : A →+* MvPolynomial (Fin P.variableCount) A)) n x)) := by
          simpa only [AlgHom.comp_apply] using
            DFunLike.congr_fun hq (AdicCompletion.evalₐ
              (I.map (MvPolynomial.C : A →+* MvPolynomial (Fin P.variableCount) A)) n x)
    _ = completedSubstitutionQuotientLift P Q m
        (AdicCompletion.evalₐ
          (I.map (MvPolynomial.C : A →+* MvPolynomial (Fin P.variableCount) A)) m x) := by
          rw [Ideal.Quotient.factorₐ_apply, AdicCompletion.factor_evalₐ _ hmn x]

/-- The substitution `P.completedPolynomialRing →ₐ[A] Q.completedPolynomialRing`: the limit of the
compatible maps `completedSubstitutionLevel P Q n`. -/
public noncomputable def completedSubstitution
    {A : Type u} [CommRing A] {I : Ideal A}
    {B : AdicFiniteTypeAlgebra.{u, v} A I}
    (P Q : CompletedPolynomialPresentation I B) :
    P.completedPolynomialRing →ₐ[A] Q.completedPolynomialRing :=
  AdicCompletion.liftAlgHom _ (completedSubstitutionLevel P Q)
    (completedSubstitutionLevel_compatible P Q)

/-- The `n`-th component of `completedSubstitution P Q x` is
`completedSubstitutionLevel P Q n x`. -/
public theorem completedSubstitution_eval
    {A : Type u} [CommRing A] {I : Ideal A}
    {B : AdicFiniteTypeAlgebra.{u, v} A I}
    (P Q : CompletedPolynomialPresentation I B) (n : ℕ)
    (x : P.completedPolynomialRing) :
    AdicCompletion.evalₐ
        (I.map (MvPolynomial.C : A →+* MvPolynomial (Fin Q.variableCount) A)) n
        (completedSubstitution P Q x) = completedSubstitutionLevel P Q n x := by
  show AdicCompletion.evalₐ _ n
      (AdicCompletion.liftAlgHom _ (completedSubstitutionLevel P Q)
        (completedSubstitutionLevel_compatible P Q) x) = _
  exact AdicCompletion.evalₐ_liftAlgHom _ _ _ n x

/-- The substitution `completedSubstitution P Q` is continuous for the limit topologies. -/
public theorem continuous_completedSubstitution
    {A : Type u} [CommRing A] {I : Ideal A}
    {B : AdicFiniteTypeAlgebra.{u, v} A I}
    (P Q : CompletedPolynomialPresentation I B) :
    @Continuous P.completedPolynomialRing Q.completedPolynomialRing
      (RestrictedPowerSeries.polynomialCompletionLimitTopology I
        (Fin P.variableCount))
      (RestrictedPowerSeries.polynomialCompletionLimitTopology I
        (Fin Q.variableCount)) (completedSubstitution P Q) := by
  let : TopologicalSpace P.completedPolynomialRing :=
    RestrictedPowerSeries.polynomialCompletionLimitTopology I
      (Fin P.variableCount)
  let : TopologicalSpace Q.completedPolynomialRing :=
    RestrictedPowerSeries.polynomialCompletionLimitTopology I
      (Fin Q.variableCount)
  let : ∀ n : ℕ, TopologicalSpace
      (MvPolynomial (Fin P.variableCount) A ⧸
        (I.map (MvPolynomial.C : A →+* MvPolynomial (Fin P.variableCount) A)) ^ n) :=
    fun _ => ⊥
  let : ∀ n : ℕ, TopologicalSpace
      (MvPolynomial (Fin Q.variableCount) A ⧸
        (I.map (MvPolynomial.C : A →+* MvPolynomial (Fin Q.variableCount) A)) ^ n) :=
    fun _ => ⊥
  let : ∀ n : ℕ, DiscreteTopology
      (MvPolynomial (Fin P.variableCount) A ⧸
        (I.map (MvPolynomial.C : A →+* MvPolynomial (Fin P.variableCount) A)) ^ n) :=
    fun _ => ⟨rfl⟩
  let : ∀ n : ℕ, DiscreteTopology
      (MvPolynomial (Fin Q.variableCount) A ⧸
        (I.map (MvPolynomial.C : A →+* MvPolynomial (Fin Q.variableCount) A)) ^ n) :=
    fun _ => ⟨rfl⟩
  apply continuous_induced_rng.mpr
  apply continuous_pi
  intro n
  show Continuous (fun x => AdicCompletion.evalₐ
    (I.map (MvPolynomial.C : A →+* MvPolynomial (Fin Q.variableCount) A)) n
    (completedSubstitution P Q x))
  have hlevel : (fun x => AdicCompletion.evalₐ
      (I.map (MvPolynomial.C : A →+* MvPolynomial (Fin Q.variableCount) A)) n
      (completedSubstitution P Q x)) = completedSubstitutionLevel P Q n := by
    funext x
    exact completedSubstitution_eval P Q n x
  rw [hlevel]
  show Continuous (completedSubstitutionQuotientLift P Q n ∘
    AdicCompletion.evalₐ
      (I.map (MvPolynomial.C : A →+* MvPolynomial (Fin P.variableCount) A)) n)
  have hqeval : Continuous (fun x : P.completedPolynomialRing =>
      fun m : ℕ => AdicCompletion.evalₐ
        (I.map (MvPolynomial.C : A →+* MvPolynomial (Fin P.variableCount) A)) m x) :=
    continuous_induced_dom
  exact (continuous_of_discreteTopology :
    Continuous (completedSubstitutionQuotientLift P Q n)).comp
      ((continuous_apply n).comp hqeval)

/-- The substitution `completedSubstitution P Q` sends the `i`-th variable of `P` to
`completedSubstitutionCoordinate P Q i`. -/
public theorem completedSubstitution_X
    {A : Type u} [CommRing A] {I : Ideal A}
    {B : AdicFiniteTypeAlgebra.{u, v} A I}
    (P Q : CompletedPolynomialPresentation I B) (i : Fin P.variableCount) :
    completedSubstitution P Q
      (algebraMap (MvPolynomial (Fin P.variableCount) A) P.completedPolynomialRing
        (MvPolynomial.X i)) = completedSubstitutionCoordinate P Q i := by
  apply AdicCompletion.ext_evalₐ
  intro n
  rw [completedSubstitution_eval]
  simp only [
    AdicCompletion.algebraMap_apply,
    ]
  show completedSubstitutionQuotientLift P Q n
      (Ideal.Quotient.mk _ (MvPolynomial.X i)) = _
  rw [completedSubstitutionQuotientLift_mk]
  simp [completedSubstitutionPolynomialLevel]

private theorem denseRange_completedPolynomials_adic
    {A : Type u} [CommRing A] [IsNoetherianRing A] {I : Ideal A}
    {B : AdicFiniteTypeAlgebra.{u, v} A I}
    (P : CompletedPolynomialPresentation I B) :
    let _J := I.map (MvPolynomial.C : A →+* MvPolynomial (Fin P.variableCount) A)
    let K := I.map (algebraMap A P.completedPolynomialRing)
    @DenseRange P.completedPolynomialRing K.adicTopology
      (MvPolynomial (Fin P.variableCount) A)
      (algebraMap (MvPolynomial (Fin P.variableCount) A) P.completedPolynomialRing) := by
  dsimp
  let R := MvPolynomial (Fin P.variableCount) A
  let K : Ideal P.completedPolynomialRing := I.map (algebraMap A P.completedPolynomialRing)
  let : TopologicalSpace P.completedPolynomialRing := K.adicTopology
  rw [DenseRange]
  show Dense (Set.range (algebraMap R P.completedPolynomialRing))
  intro x
  apply (mem_closure_iff_nhds_basis (Ideal.hasBasis_nhds_adic K x)).2
  intro n hn
  obtain ⟨p, hideal⟩ := exists_sub_algebraMap_mem_pow P x n
  have hmem : algebraMap R P.completedPolynomialRing p ∈
      (fun y => x + y) ''
        ((K ^ n : Ideal P.completedPolynomialRing) : Set P.completedPolynomialRing) := by
    refine ⟨algebraMap R P.completedPolynomialRing p - x, ?_, by simp⟩
    rw [← neg_sub]
    exact neg_mem hideal
  exact ⟨algebraMap R P.completedPolynomialRing p, ⟨p, rfl⟩, hmem⟩

/-- Evaluating a polynomial at the images of the variables in an algebra over the polynomial ring
gives the image of the polynomial. -/
private theorem aeval_algebraMap_X_eq_algebraMap {A S σ : Type*} [CommRing A] [CommRing S]
    [Algebra A S] [Algebra (MvPolynomial σ A) S] [IsScalarTower A (MvPolynomial σ A) S]
    (f : MvPolynomial σ A) :
    MvPolynomial.aeval (fun i => algebraMap (MvPolynomial σ A) S (MvPolynomial.X i)) f =
      algebraMap (MvPolynomial σ A) S f :=
  DFunLike.congr_fun (MvPolynomial.algHom_ext (g := IsScalarTower.toAlgHom A _ S) fun i => by
    simp) f

/-- An `A`-algebra map is continuous for the topologies induced by the extensions of `I`. -/
private theorem continuous_adicTopology_algHom {A R S : Type*} [CommRing A] [CommRing R]
    [CommRing S] [Algebra A R] [Algebra A S] (I : Ideal A) (f : R →ₐ[A] S) :
    @Continuous R S (I.map (algebraMap A R)).adicTopology (I.map (algebraMap A S)).adicTopology
      f := by
  refine (RingHom.continuous_adic_iff f.toRingHom _ _).2 ⟨1, le_rfl, fun x hx => ?_⟩
  have hle : Ideal.map f.toRingHom (I.map (algebraMap A R)) ≤ I.map (algebraMap A S) := by
    rw [Ideal.map_map]
    exact (congrArg (Ideal.map · I) f.comp_algebraMap).le
  exact hle (Ideal.mem_map_of_mem _ (by simpa using hx))

/-- The substitution `completedSubstitution P Q` commutes with the projections of the two completed
polynomial rings onto `B`. -/
public theorem completedSubstitution_compatible
    {A : Type u} [CommRing A] [IsNoetherianRing A] {I : Ideal A}
    {B : AdicFiniteTypeAlgebra.{u, v} A I}
    (P Q : CompletedPolynomialPresentation I B) :
    Q.toAlgHom.comp (completedSubstitution P Q) = P.toAlgHom := by
  let KP : Ideal P.completedPolynomialRing :=
    I.map (algebraMap A P.completedPolynomialRing)
  let KQ : Ideal Q.completedPolynomialRing :=
    I.map (algebraMap A Q.completedPolynomialRing)
  let : TopologicalSpace P.completedPolynomialRing := KP.adicTopology
  let : TopologicalSpace Q.completedPolynomialRing := KQ.adicTopology
  let : TopologicalSpace B.carrier := B.adicIdeal.adicTopology
  let : T2Space B.carrier :=
    (IsAdic.isHausdorff_iff (I := B.adicIdeal) rfl).mp
      B.isAdicallyComplete.toIsHausdorff
  have hFcont : @Continuous P.completedPolynomialRing Q.completedPolynomialRing
      KP.adicTopology KQ.adicTopology (completedSubstitution P Q) :=
    continuous_adicTopology_algHom I _
  have hPcont : @Continuous P.completedPolynomialRing B.carrier
      KP.adicTopology B.adicIdeal.adicTopology P.toAlgHom :=
    continuous_adicTopology_algHom I _
  have hQcont : @Continuous Q.completedPolynomialRing B.carrier
      KQ.adicTopology B.adicIdeal.adicTopology Q.toAlgHom :=
    continuous_adicTopology_algHom I _
  let pAlg : MvPolynomial (Fin P.variableCount) A →ₐ[A] P.completedPolynomialRing :=
    MvPolynomial.aeval (fun i => algebraMap (MvPolynomial (Fin P.variableCount) A)
      P.completedPolynomialRing (MvPolynomial.X i))
  have hpAlg (f : MvPolynomial (Fin P.variableCount) A) :
      pAlg f = algebraMap (MvPolynomial (Fin P.variableCount) A)
        P.completedPolynomialRing f :=
    aeval_algebraMap_X_eq_algebraMap f
  have hmaps : (Q.toAlgHom.comp (completedSubstitution P Q)).comp pAlg =
      P.toAlgHom.comp pAlg := by
    apply MvPolynomial.algHom_ext
    intro i
    simp [pAlg, completedSubstitution_X, completedSubstitutionCoordinate_spec]
  have hpoly : (fun f : MvPolynomial (Fin P.variableCount) A =>
      Q.toAlgHom (completedSubstitution P Q
        (algebraMap (MvPolynomial (Fin P.variableCount) A) P.completedPolynomialRing f))) =
      (fun f => P.toAlgHom
        (algebraMap (MvPolynomial (Fin P.variableCount) A) P.completedPolynomialRing f)) := by
    funext f
    rw [← hpAlg f]
    exact DFunLike.congr_fun hmaps f
  exact AlgHom.ext (congrFun ((denseRange_completedPolynomials_adic P).equalizer
    (hQcont.comp hFcont) hPcont hpoly))

/-- The `B`-linear map given by the Jacobian matrix of `F`: the image of `x` has `j`-th coordinate
`∑ i, x i * ∂(F Xᵢ)/∂Xⱼ`, evaluated in `B`. -/
public noncomputable def completedSubstitutionCoordinateMap
    {A : Type u} [CommRing A] [IsNoetherianRing A] {I : Ideal A}
    {B : AdicFiniteTypeAlgebra.{u, v} A I}
    (P Q : CompletedPolynomialPresentation I B)
    (F : P.completedPolynomialRing →ₐ[A] Q.completedPolynomialRing) :
    (Fin P.variableCount → B.carrier) →ₗ[B.carrier]
      (Fin Q.variableCount → B.carrier) := by
  classical
  let KQ := Rig.completedNaiveCotangentComplex B Q
  refine
    { toFun := fun x j => ∑ i : Fin P.variableCount,
        x i * Q.toAlgHom (KQ.partialDeriv j (F
          (algebraMap (MvPolynomial (Fin P.variableCount) A) P.completedPolynomialRing
            (MvPolynomial.X i))))
      map_add' := ?_
      map_smul' := ?_ }
  · intro x y
    funext j
    simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
  · intro a x
    funext j
    simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    simp only [RingHom.id_apply]
    ring

/-- The substitution `completedSubstitution P Q` as a morphism of extensions from `P.extension` to
`Q.extension`. -/
public noncomputable def completedSubstitutionExtensionHom
    {A : Type u} [CommRing A] [IsNoetherianRing A] {I : Ideal A}
    {B : AdicFiniteTypeAlgebra.{u, v} A I}
    (P Q : CompletedPolynomialPresentation I B) : P.extension.Hom Q.extension :=
  Algebra.Extension.Hom.ofAlgHom (completedSubstitution P Q) (by
    change Q.toAlgHom.comp (completedSubstitution P Q) = P.toAlgHom
    exact completedSubstitution_compatible P Q)

/-- The map of lifted cotangent modules induced by `completedSubstitutionExtensionHom P Q`. -/
public noncomputable def completedSubstitutionMinusMap
    {A : Type u} [CommRing A] [IsNoetherianRing A] {I : Ideal A}
    {B : AdicFiniteTypeAlgebra.{u, v} A I}
    (P Q : CompletedPolynomialPresentation I B) :
    LiftedCotangent (P := P) →ₗ[B.carrier] LiftedCotangent (P := Q) :=
  ULift.moduleEquiv.symm.toLinearMap.comp
    ((Algebra.Extension.Cotangent.map (completedSubstitutionExtensionHom P Q)).comp
      ULift.moduleEquiv.toLinearMap)

/-- The map of lifted differentials given by the Jacobian map `completedSubstitutionCoordinateMap`
of `completedSubstitution P Q`. -/
public noncomputable def completedSubstitutionZeroMap
    {A : Type u} [CommRing A] [IsNoetherianRing A] {I : Ideal A}
    {B : AdicFiniteTypeAlgebra.{u, v} A I}
    (P Q : CompletedPolynomialPresentation I B) :
    LiftedDifferentials (P := P) →ₗ[B.carrier] LiftedDifferentials (P := Q) :=
  ULift.moduleEquiv.symm.toLinearMap.comp
    ((completedSubstitutionCoordinateMap P Q (completedSubstitution P Q)).comp
      ULift.moduleEquiv.toLinearMap)

/-- **Chain rule.** For a continuous `A`-algebra map `F` between completed polynomial rings,
`∂(F x)/∂Xⱼ = ∑ i, F (∂x/∂Xᵢ) * ∂(F Xᵢ)/∂Xⱼ`. -/
public theorem completedSubstitution_chainRule
    {A : Type u} [CommRing A] [IsNoetherianRing A] {I : Ideal A}
    {B : AdicFiniteTypeAlgebra.{u, v} A I}
    (P Q : CompletedPolynomialPresentation I B)
    (F : P.completedPolynomialRing →ₐ[A] Q.completedPolynomialRing)
    (hF : @Continuous P.completedPolynomialRing Q.completedPolynomialRing
      (RestrictedPowerSeries.polynomialCompletionLimitTopology I
        (Fin P.variableCount))
      (RestrictedPowerSeries.polynomialCompletionLimitTopology I
        (Fin Q.variableCount)) F)
    (j : Fin Q.variableCount) (x : P.completedPolynomialRing) :
    completedPartialDeriv Q j (F x) =
      ∑ i : Fin P.variableCount,
        F (completedPartialDeriv P i x) *
          completedPartialDeriv Q j (F
            (algebraMap (MvPolynomial (Fin P.variableCount) A)
              P.completedPolynomialRing (MvPolynomial.X i))) := by
  let : TopologicalSpace P.completedPolynomialRing :=
    RestrictedPowerSeries.polynomialCompletionLimitTopology I
      (Fin P.variableCount)
  let : TopologicalSpace Q.completedPolynomialRing :=
    RestrictedPowerSeries.polynomialCompletionLimitTopology I
      (Fin Q.variableCount)
  let : ∀ n : ℕ, TopologicalSpace
      (MvPolynomial (Fin Q.variableCount) (A ⧸ I ^ n)) := fun _ => ⊥
  let : ∀ n : ℕ, DiscreteTopology
      (MvPolynomial (Fin Q.variableCount) (A ⧸ I ^ n)) := fun _ => ⟨rfl⟩
  let : TopologicalSpace
      (RestrictedPowerSeries I (Fin Q.variableCount)) :=
    RestrictedPowerSeries.limitTopology I (Fin Q.variableCount)
  have : ContinuousAdd
      (RestrictedPowerSeries I (Fin Q.variableCount)) := by infer_instance
  have : ContinuousMul
      (RestrictedPowerSeries I (Fin Q.variableCount)) := by infer_instance
  have : T2Space (RestrictedPowerSeries I
      (Fin Q.variableCount)) := by infer_instance
  let hq := RestrictedPowerSeries.adicCompletionHomeomorph I
    (Fin Q.variableCount)
  let : T2Space Q.completedPolynomialRing := hq.t2Space
  let Qpoly := MvPolynomial (Fin Q.variableCount) A
  let Qideal := I.map (MvPolynomial.C : A →+* Qpoly)
  let : ∀ n : ℕ, TopologicalSpace (Qpoly ⧸ Qideal ^ n) := fun _ => ⊥
  let : ∀ n : ℕ, DiscreteTopology (Qpoly ⧸ Qideal ^ n) := fun _ => ⟨rfl⟩
  let qeval : Q.completedPolynomialRing →+*
      (n : ℕ) → Qpoly ⧸ Qideal ^ n := {
    toFun := fun x n => AdicCompletion.evalₐ Qideal n x
    map_one' := by funext n; simp
    map_mul' _ _ := by funext n; simp
    map_zero' := by funext n; simp
    map_add' _ _ := by funext n; simp
  }
  have : ContinuousAdd Q.completedPolynomialRing := continuousAdd_induced qeval
  have : ContinuousMul Q.completedPolynomialRing := continuousMul_induced qeval
  let D := completedPartialDeriv Q j
  let KP := Rig.completedNaiveCotangentComplex B P
  let H : P.completedPolynomialRing →ₗ[A] Q.completedPolynomialRing :=
    ∑ i : Fin P.variableCount,
      (LinearMap.mulRight (R := A) (D (F
        (algebraMap (MvPolynomial (Fin P.variableCount) A)
          P.completedPolynomialRing (MvPolynomial.X i))))).comp
        ((F.toLinearMap).comp (KP.partialDeriv i).toLinearMap)
  let : Algebra P.completedPolynomialRing Q.completedPolynomialRing := F.toAlgebra
  let : IsScalarTower A P.completedPolynomialRing Q.completedPolynomialRing :=
    IsScalarTower.of_algebraMap_eq fun _ => (F.commutes _).symm
  let Dcomp : Derivation A P.completedPolynomialRing Q.completedPolynomialRing := by
    refine Derivation.mk' (D.toLinearMap.comp F.toLinearMap) ?_
    intro y z
    show D (F (y * z)) = y • D (F z) + z • D (F y)
    rw [map_mul, D.leibniz]
    simp only [Algebra.smul_def]
    show F y * D (F z) + F z * D (F y) =
      F y * D (F z) + F z * D (F y)
    rfl
  have hH_apply (y : P.completedPolynomialRing) :
      H y = ∑ i : Fin P.variableCount,
        F (KP.partialDeriv i y) * D (F
          (algebraMap (MvPolynomial (Fin P.variableCount) A)
            P.completedPolynomialRing (MvPolynomial.X i))) := by
    simp [H, LinearMap.mulRight_apply]
  let E : Derivation A P.completedPolynomialRing Q.completedPolynomialRing := by
    refine Derivation.mk' H ?_
    intro y z
    rw [hH_apply (y * z), hH_apply y, hH_apply z]
    simp only [Algebra.smul_def]
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    have hderiv : KP.partialDeriv i (y * z) =
        y * KP.partialDeriv i z + z * KP.partialDeriv i y := by
      simpa only [smul_eq_mul] using (KP.partialDeriv i).leibniz y z
    rw [hderiv]
    simp only [map_add, map_mul]
    simp only [RingHom.algebraMap_toAlgebra]
    show (F y * F (KP.partialDeriv i z) + F z * F (KP.partialDeriv i y)) *
        D (F (algebraMap (MvPolynomial (Fin P.variableCount) A)
          P.completedPolynomialRing (MvPolynomial.X i))) =
      F y * (F (KP.partialDeriv i z) *
        D (F (algebraMap (MvPolynomial (Fin P.variableCount) A)
          P.completedPolynomialRing (MvPolynomial.X i)))) +
      F z * (F (KP.partialDeriv i y) *
        D (F (algebraMap (MvPolynomial (Fin P.variableCount) A)
          P.completedPolynomialRing (MvPolynomial.X i))))
    ring
  have hcontH : @Continuous P.completedPolynomialRing Q.completedPolynomialRing
      (RestrictedPowerSeries.polynomialCompletionLimitTopology I
        (Fin P.variableCount))
      (RestrictedPowerSeries.polynomialCompletionLimitTopology I
        (Fin Q.variableCount)) H := by
    have hcont : Continuous (fun x : P.completedPolynomialRing =>
        ∑ i : Fin P.variableCount,
          F (KP.partialDeriv i x) * D (F
            (algebraMap (MvPolynomial (Fin P.variableCount) A)
              P.completedPolynomialRing (MvPolynomial.X i)))) :=
      continuous_finsetSum _ fun i _ =>
        (hF.comp (continuous_completedPartialDeriv P i)).mul continuous_const
    exact hcont.congr fun x => (hH_apply x).symm
  let pAlg : MvPolynomial (Fin P.variableCount) A →ₐ[A] P.completedPolynomialRing :=
    MvPolynomial.aeval (fun i => algebraMap (MvPolynomial (Fin P.variableCount) A)
      P.completedPolynomialRing (MvPolynomial.X i))
  have hpAlg (f : MvPolynomial (Fin P.variableCount) A) :
      pAlg f = algebraMap (MvPolynomial (Fin P.variableCount) A)
        P.completedPolynomialRing f :=
    aeval_algebraMap_X_eq_algebraMap f
  let φ := F.comp pAlg
  have hpoly : ∀ f : MvPolynomial (Fin P.variableCount) A,
      Dcomp
        (algebraMap (MvPolynomial (Fin P.variableCount) A)
          P.completedPolynomialRing f) =
      E (algebraMap (MvPolynomial (Fin P.variableCount) A)
          P.completedPolynomialRing f) := by
    intro f
    have hc := mvPolynomial_derivation_chainRule D φ f
    rw [← hpAlg f]
    show D (F (pAlg f)) = H (pAlg f)
    rw [hH_apply]
    have hcoord (i : Fin P.variableCount) :
        KP.partialDeriv i (pAlg f) = algebraMap (MvPolynomial (Fin P.variableCount) A)
          P.completedPolynomialRing (MvPolynomial.pderiv i f) := by
      rw [hpAlg f]
      exact completedPartialDeriv_polynomial P i f
    simp_rw [hcoord]
    simpa [φ, pAlg, hpAlg] using hc
  have hEq := completedPolynomialDerivation_ext P Dcomp
    E (hD := by
      show Continuous (fun x => D (F x))
      exact (continuous_completedPartialDeriv Q j).comp hF)
    (hE := hcontH) hpoly
  have hx := congrArg (fun d : Derivation A P.completedPolynomialRing
      Q.completedPolynomialRing => d x) hEq
  simpa [Dcomp, E, H, LinearMap.comp_apply, LinearMap.mulRight_apply,
    KP, D, completedNaiveCotangentComplex_partialDeriv] using hx

/-- The maps `completedSubstitutionMinusMap P Q` and `completedSubstitutionZeroMap P Q` commute
with the differentials of the completed naive cotangent complexes. -/
public theorem completedSubstitution_chainCondition
    {A : Type u} [CommRing A] [IsNoetherianRing A] {I : Ideal A}
    {B : AdicFiniteTypeAlgebra.{u, v} A I}
    (P Q : CompletedPolynomialPresentation I B) :
    (Rig.completedNaiveCotangentComplex B Q).liftedDifferential.comp
        (completedSubstitutionMinusMap P Q) =
      (completedSubstitutionZeroMap P Q).comp
        (Rig.completedNaiveCotangentComplex B P).liftedDifferential := by
  classical
  let : Algebra P.completedPolynomialRing B.carrier := P.toAlgHom.toAlgebra
  let F := completedSubstitution P Q
  let KP := Rig.completedNaiveCotangentComplex B P
  let KQ := Rig.completedNaiveCotangentComplex B Q
  apply LinearMap.ext
  intro z
  cases z with
  | up x =>
    obtain ⟨g, rfl⟩ := Algebra.Extension.Cotangent.mk_surjective x
    apply ULift.ext
    funext j
    simp only [LinearMap.comp_apply]
    rw [KP.liftedDifferential_up, KQ.liftedDifferential_up]
    show KQ.differential
        (Algebra.Extension.Cotangent.map (completedSubstitutionExtensionHom P Q)
          (Algebra.Extension.Cotangent.mk g)) j =
      completedSubstitutionCoordinateMap P Q (completedSubstitution P Q)
        (KP.differential (Algebra.Extension.Cotangent.mk g)) j
    rw [Algebra.Extension.Cotangent.map_mk, KQ.differential_mk,
      KP.differential_mk]
    simp only [completedSubstitutionCoordinateMap, LinearMap.coe_mk, AddHom.coe_mk]
    let gval : P.completedPolynomialRing := g.val
    have hc := completedSubstitution_chainRule P Q F
      (continuous_completedSubstitution P Q) j gval
    have hc' := congrArg Q.toAlgHom hc
    simp only [map_sum, map_mul] at hc'
    have hF (x : P.completedPolynomialRing) : Q.toAlgHom (F x) = P.toAlgHom x :=
      DFunLike.congr_fun (completedSubstitution_compatible P Q) x
    have hFderiv (i : Fin P.variableCount) :
        Q.toAlgHom (F (completedPartialDeriv P i gval)) =
          P.toAlgHom (completedPartialDeriv P i gval) := hF _
    simp_rw [hFderiv] at hc'
    show Q.toAlgHom (completedPartialDeriv Q j (F gval)) =
      ∑ i : Fin P.variableCount,
        P.toAlgHom (completedPartialDeriv P i gval) *
          Q.toAlgHom (completedPartialDeriv Q j
            (F (algebraMap (MvPolynomial (Fin P.variableCount) A)
              P.completedPolynomialRing (MvPolynomial.X i))))
    exact hc'

/-- The morphism of completed naive cotangent complexes with component `f₁` in degree `-1` and `f₀`
in degree `0`, for maps commuting with the differentials. -/
public noncomputable def completedSubstitutionChainMap
    {A : Type u} [CommRing A] [IsNoetherianRing A] {I : Ideal A}
    {B : AdicFiniteTypeAlgebra.{u, v} A I}
    (P Q : CompletedPolynomialPresentation I B)
    (f₁ : LiftedCotangent (P := P) →ₗ[B.carrier] LiftedCotangent (P := Q))
    (f₀ : LiftedDifferentials (P := P) →ₗ[B.carrier] LiftedDifferentials (P := Q))
    (hcomm : (Rig.completedNaiveCotangentComplex B Q).liftedDifferential.comp f₁ =
      f₀.comp (Rig.completedNaiveCotangentComplex B P).liftedDifferential) :
    (Rig.completedNaiveCotangentComplex B P).cochainComplex ⟶
      (Rig.completedNaiveCotangentComplex B Q).cochainComplex := by
  let KP := Rig.completedNaiveCotangentComplex B P
  let KQ := Rig.completedNaiveCotangentComplex B Q
  let φ₀ : ModuleCat.of B.carrier (LiftedCotangent (P := P)) ⟶
      KQ.cochainComplex.X (-1) :=
    ModuleCat.ofHom f₁ ≫ KQ.degreeNegOneIso.inv
  let φ₁ : ModuleCat.of B.carrier (LiftedDifferentials (P := P)) ⟶
      KQ.cochainComplex.X 0 :=
    ModuleCat.ofHom f₀ ≫ KQ.degreeZeroIso.inv
  exact HomologicalComplex.mkHomFromDouble
    (show (ComplexShape.up ℤ).Rel (-1) 0 from rfl)
    (by norm_num : (-1 : ℤ) ≠ 0) φ₀ φ₁ (by
      rw [KQ.cochainComplex_d]
      dsimp [φ₀, φ₁]
      simp only [Category.assoc, Iso.inv_hom_id_assoc]
      have hcomp : ModuleCat.ofHom f₁ ≫ ModuleCat.ofHom KQ.liftedDifferential =
          ModuleCat.ofHom KP.liftedDifferential ≫ ModuleCat.ofHom f₀ := by
        rw [← ModuleCat.ofHom_comp, ← ModuleCat.ofHom_comp, hcomm]
      exact congrArg (fun f => f ≫ KQ.degreeZeroIso.inv) hcomp) (by
        intro k hk
        have hk1 : k = 1 := by
          have h : (0 : ℤ) + 1 = k := hk
          omega
        exact (HomologicalComplex.isZero_double_X
          (ModuleCat.ofHom KQ.liftedDifferential)
          (show (ComplexShape.up ℤ).Rel (-1) 0 from rfl) k (by omega) (by omega)).eq_of_tgt
          _ _)

/-- For an endomorphism `F` of `P.completedPolynomialRing` over `B`, the class in the cotangent
module of the element `Xᵢ - F Xᵢ` of the kernel. -/
public noncomputable def completedSubstitutionDifferenceGenerator
    {A : Type u} [CommRing A] [IsNoetherianRing A] {I : Ideal A}
    {B : AdicFiniteTypeAlgebra.{u, v} A I}
    (P : CompletedPolynomialPresentation I B)
    (F : P.completedPolynomialRing →ₐ[A] P.completedPolynomialRing)
    (hF : P.toAlgHom.comp F = P.toAlgHom) (i : Fin P.variableCount) :
    P.extension.Cotangent := by
  classical
  letI : Algebra P.completedPolynomialRing B.carrier := P.toAlgHom.toAlgebra
  refine Algebra.Extension.Cotangent.mk ⟨
    algebraMap (MvPolynomial (Fin P.variableCount) A) P.completedPolynomialRing
        (MvPolynomial.X i) -
      F (algebraMap (MvPolynomial (Fin P.variableCount) A) P.completedPolynomialRing
        (MvPolynomial.X i)), ?_⟩
  change P.toAlgHom
    (algebraMap (MvPolynomial (Fin P.variableCount) A) P.completedPolynomialRing
        (MvPolynomial.X i) -
      F (algebraMap (MvPolynomial (Fin P.variableCount) A) P.completedPolynomialRing
        (MvPolynomial.X i))) = 0
  have h := DFunLike.congr_fun hF
    (algebraMap (MvPolynomial (Fin P.variableCount) A) P.completedPolynomialRing
      (MvPolynomial.X i))
  rw [map_sub]
  exact sub_eq_zero.mpr (by simpa only [AlgHom.comp_apply] using h.symm)

/-- For an endomorphism `F` of `P.completedPolynomialRing` over `B`, the map from the lifted
differentials to the lifted cotangent module sending `x` to `∑ i, x i • [Xᵢ - F Xᵢ]`. -/
public noncomputable def completedSubstitutionDifferenceMap
    {A : Type u} [CommRing A] [IsNoetherianRing A] {I : Ideal A}
    {B : AdicFiniteTypeAlgebra.{u, v} A I}
    (P : CompletedPolynomialPresentation I B)
    (F : P.completedPolynomialRing →ₐ[A] P.completedPolynomialRing)
    (hF : P.toAlgHom.comp F = P.toAlgHom) :
    LiftedDifferentials (P := P) →ₗ[B.carrier] LiftedCotangent (P := P) := by
  classical
  letI : Algebra P.completedPolynomialRing B.carrier := P.toAlgHom.toAlgebra
  refine
    { toFun := fun x => ULift.up (∑ i : Fin P.variableCount,
        x.down i • completedSubstitutionDifferenceGenerator P F hF i)
      map_add' := ?_
      map_smul' := ?_ }
  · intro x y
    apply ULift.ext
    simp [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  · intro a x
    apply ULift.ext
    change (∑ i : Fin P.variableCount,
        (a * x.down i) • completedSubstitutionDifferenceGenerator P F hF i) =
      a • ∑ i : Fin P.variableCount,
        x.down i • completedSubstitutionDifferenceGenerator P F hF i
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    simp [mul_smul]

/-- The differential composed after `completedSubstitutionDifferenceMap P F hF` is the identity
minus the Jacobian map of `F`. -/
public theorem completedSubstitutionDifferenceMap_differential
    {A : Type u} [CommRing A] [IsNoetherianRing A] {I : Ideal A}
    {B : AdicFiniteTypeAlgebra.{u, v} A I}
    (P : CompletedPolynomialPresentation I B)
    (F : P.completedPolynomialRing →ₐ[A] P.completedPolynomialRing)
    (hF : P.toAlgHom.comp F = P.toAlgHom) :
    (Rig.completedNaiveCotangentComplex B P).liftedDifferential.comp
        (completedSubstitutionDifferenceMap P F hF) =
      (LinearMap.id : LiftedDifferentials (P := P) →ₗ[B.carrier] _) -
        (ULift.moduleEquiv.symm.toLinearMap.comp
          ((completedSubstitutionCoordinateMap P P F).comp
            ULift.moduleEquiv.toLinearMap)) := by
  classical
  let : Algebra P.completedPolynomialRing B.carrier := P.toAlgHom.toAlgebra
  let K := Rig.completedNaiveCotangentComplex B P
  let X : Fin P.variableCount → P.completedPolynomialRing := fun i =>
    algebraMap (MvPolynomial (Fin P.variableCount) A) P.completedPolynomialRing
      (MvPolynomial.X i)
  apply LinearMap.ext
  intro x
  apply ULift.ext
  funext j
  show K.differential
      (∑ i : Fin P.variableCount, x.down i •
        completedSubstitutionDifferenceGenerator P F hF i) j =
    x.down j - ∑ i : Fin P.variableCount, x.down i *
      P.toAlgHom (K.partialDeriv j (F (X i)))
  rw [map_sum]
  simp only [map_smul, K.differential_mk, completedSubstitutionDifferenceGenerator]
  rw [Finset.sum_apply]
  show (∑ i : Fin P.variableCount, x.down i *
      P.toAlgHom (K.partialDeriv j (X i - F (X i)))) =
    x.down j - ∑ i : Fin P.variableCount, x.down i *
      P.toAlgHom (K.partialDeriv j (F (X i)))
  have hderiv (i : Fin P.variableCount) :
      K.partialDeriv j (X i - F (X i)) =
        K.partialDeriv j (X i) - K.partialDeriv j (F (X i)) :=
    (K.partialDeriv j).map_sub _ _
  simp_rw [hderiv, map_sub]
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib]
  have hpart : K.partialDeriv j = completedPartialDeriv P j := rfl
  rw [hpart]
  have hXi (i : Fin P.variableCount) :
      completedPartialDeriv P j (X i) =
        algebraMap (MvPolynomial (Fin P.variableCount) A) P.completedPolynomialRing
          (MvPolynomial.pderiv j (MvPolynomial.X i)) := by
    dsimp only [X]
    exact completedPartialDeriv_polynomial P j (MvPolynomial.X i)
  simp_rw [hXi]
  simp [MvPolynomial.pderiv_X, Pi.single_apply, eq_comm]

/-- A derivation mapping an ideal `J` into itself maps every power `J ^ n` into itself. -/
public theorem derivation_mem_pow_of_mem_ideal
    {A R : Type u} [CommRing A] [CommRing R] [Algebra A R] {J : Ideal R}
    (D : Derivation A R R) (hJ : ∀ x ∈ J, D x ∈ J) :
    ∀ n x, x ∈ J ^ n → D x ∈ J ^ n := by
  intro n
  induction n with
  | zero =>
      intro x hx
      simp
  | succ n ih =>
      intro x hx
      rw [pow_succ] at hx ⊢
      induction hx using Submodule.mul_induction_on' with
      | mem_mul_mem a ha b hb =>
          have h1 : a * D b ∈ J ^ n * J := Ideal.mul_mem_mul ha (hJ b hb)
          have h2 : b * D a ∈ J ^ n * J := by
            simpa [mul_comm] using (Ideal.mul_mem_mul hb (ih a ha))
          rw [D.leibniz]
          simpa only [smul_eq_mul] using add_mem h1 h2
      | add a b ha hb hda hdb =>
          rw [D.map_add]
          exact add_mem hda hdb

/-- A linear map carries `J ^ n • ⊤` into `J ^ n • ⊤`. -/
public theorem linearMap_mem_smul_top_pow
    {A M N : Type*} [CommSemiring A] [AddCommMonoid M] [AddCommMonoid N]
    [Module A M] [Module A N] (J : Ideal A) (f : M →ₗ[A] N) :
    ∀ n x, x ∈ J ^ n • (⊤ : Submodule A M) →
      f x ∈ J ^ n • (⊤ : Submodule A N) := fun n x hx =>
  Submodule.smul_induction_on hx
    (fun a ha y _ => by rw [map_smul]; exact Submodule.smul_mem_smul ha (by simp))
    fun x y hx hy => by rw [map_add]; exact add_mem hx hy

/-- An endomorphism `F` of `P.completedPolynomialRing` over `B`, as an endomorphism of the
extension `P.extension`. -/
public noncomputable def completedSubstitutionEndomorphismHom
    {A : Type u} [CommRing A] {I : Ideal A}
    {B : AdicFiniteTypeAlgebra.{u, v} A I}
    (P : CompletedPolynomialPresentation I B)
    (F : P.completedPolynomialRing →ₐ[A] P.completedPolynomialRing)
    (hF : P.toAlgHom.comp F = P.toAlgHom) : P.extension.Hom P.extension := by
  have hF' : (IsScalarTower.toAlgHom A P.extension.Ring B.carrier).comp F =
      (IsScalarTower.toAlgHom A B.carrier B.carrier).comp
        (IsScalarTower.toAlgHom A P.extension.Ring B.carrier) :=
    AlgHom.ext fun x => congrArg (fun f => f x) hF
  exact Algebra.Extension.Hom.ofAlgHom F hF'

attribute [local instance] IsScalarTower.of_compHom SMulCommClass.of_commMonoid

/-- For an endomorphism `F` of `P.completedPolynomialRing` over `B`, the derivation `x ↦ [x - F x]`
into the cotangent module. -/
public noncomputable def completedSubstitutionDifferenceDerivation
    {A : Type u} [CommRing A] [IsNoetherianRing A] {I : Ideal A}
    {B : AdicFiniteTypeAlgebra.{u, v} A I}
    (P : CompletedPolynomialPresentation I B)
    (F : P.completedPolynomialRing →ₐ[A] P.completedPolynomialRing)
    (hF : P.toAlgHom.comp F = P.toAlgHom) :
    Derivation A P.completedPolynomialRing P.extension.Cotangent := by
  letI : Module P.completedPolynomialRing P.extension.ker :=
    inferInstanceAs (Module P.extension.Ring P.extension.ker)
  let f := completedSubstitutionEndomorphismHom P F hF
  let id : P.extension.Hom P.extension := Algebra.Extension.Hom.id P.extension
  let δ : P.completedPolynomialRing →ₗ[A] P.extension.ker := (id.subToKer f)
  let L : P.completedPolynomialRing →ₗ[A] P.extension.Cotangent :=
    (Algebra.Extension.Cotangent.mk.restrictScalars A).comp δ
  refine Derivation.mk' L ?_
  intro x y
  dsimp only [L]
  change Algebra.Extension.Cotangent.mk (δ (x * y)) =
    x • Algebra.Extension.Cotangent.mk (δ y) +
      y • Algebra.Extension.Cotangent.mk (δ x)
  have hsx : Algebra.Extension.Cotangent.mk (x • δ y) =
      x • Algebra.Extension.Cotangent.mk (δ y) :=
    (Algebra.Extension.Cotangent.mk (P := P.extension)).map_smul x (δ y)
  have hsy : Algebra.Extension.Cotangent.mk (y • δ x) =
      y • Algebra.Extension.Cotangent.mk (δ x) :=
    (Algebra.Extension.Cotangent.mk (P := P.extension)).map_smul y (δ x)
  have hadd : Algebra.Extension.Cotangent.mk (x • δ y + y • δ x) =
      Algebra.Extension.Cotangent.mk (x • δ y) + Algebra.Extension.Cotangent.mk (y • δ x) :=
    (Algebra.Extension.Cotangent.mk (P := P.extension)).map_add _ _
  rw [← hsx, ← hsy, ← hadd]
  apply (Algebra.Extension.Cotangent.mk_eq_mk_iff_sub_mem _ _).mpr
  have hx : x - F x ∈ P.extension.ker := by
    change P.toAlgHom (x - F x) = 0
    rw [map_sub]
    exact sub_eq_zero.mpr (congrArg (fun g => g x) hF).symm
  have hy : y - F y ∈ P.extension.ker := by
    change P.toAlgHom (y - F y) = 0
    rw [map_sub]
    exact sub_eq_zero.mpr (congrArg (fun g => g y) hF).symm
  have hmul : (x - F x) * (y - F y) ∈ P.extension.ker ^ 2 := by
    rw [pow_two]
    exact Ideal.mul_mem_mul hx hy
  have hδx : (δ x).val = x - F x := by
    rfl
  have hδy : (δ y).val = y - F y := by
    rfl
  have hδxy : (δ (x * y)).val = x * y - F x * F y := by
    change x * y - F (x * y) = _
    rw [map_mul]
  change (@HSub.hSub P.completedPolynomialRing P.completedPolynomialRing
      P.completedPolynomialRing instHSub (δ (x * y)).val
      (@HMul.hMul P.completedPolynomialRing P.completedPolynomialRing P.completedPolynomialRing
          instHMul x (δ y).val +
        @HMul.hMul P.completedPolynomialRing P.completedPolynomialRing P.completedPolynomialRing
          instHMul y (δ x).val)) ∈ P.extension.ker ^ 2
  rw [hδx, hδy, hδxy]
  have hiden : (x * y - F x * F y) -
      (x * (y - F y) + y * (x - F x)) = -((x - F x) * (y - F y)) := by
    ring
  rw [hiden]
  exact neg_mem hmul

/-- The derivation `completedSubstitutionDifferenceDerivation P F hF` sends the `i`-th variable to
the class of `Xᵢ - F Xᵢ`. -/
public theorem completedSubstitutionDifferenceDerivation_X
    {A : Type u} [CommRing A] [IsNoetherianRing A] {I : Ideal A}
    {B : AdicFiniteTypeAlgebra.{u, v} A I}
    (P : CompletedPolynomialPresentation I B)
    (F : P.completedPolynomialRing →ₐ[A] P.completedPolynomialRing)
    (hF : P.toAlgHom.comp F = P.toAlgHom) (i : Fin P.variableCount) :
    completedSubstitutionDifferenceDerivation P F hF
      (algebraMap (MvPolynomial (Fin P.variableCount) A) P.completedPolynomialRing
        (MvPolynomial.X i)) =
      Algebra.Extension.Cotangent.mk
        ((Algebra.Extension.Hom.id P.extension).subToKer
          (completedSubstitutionEndomorphismHom P F hF)
          (algebraMap (MvPolynomial (Fin P.variableCount) A) P.completedPolynomialRing
            (MvPolynomial.X i))) := by
  unfold completedSubstitutionDifferenceDerivation
  show Algebra.Extension.Cotangent.mk
      ((Algebra.Extension.Hom.id P.extension).subToKer
        (completedSubstitutionEndomorphismHom P F hF)
        (algebraMap (MvPolynomial (Fin P.variableCount) A) P.completedPolynomialRing
          (MvPolynomial.X i))) = _
  rfl

/-- The derivation `x ↦ ∑ i, (∂x/∂Xᵢ) • D Xᵢ` into the cotangent module, where `D` is
`completedSubstitutionDifferenceDerivation P F hF`. -/
public noncomputable def completedSubstitutionTaylorCoordinateDerivation
    {A : Type u} [CommRing A] [IsNoetherianRing A] {I : Ideal A}
    {B : AdicFiniteTypeAlgebra.{u, v} A I}
    (P : CompletedPolynomialPresentation I B)
    (F : P.completedPolynomialRing →ₐ[A] P.completedPolynomialRing)
    (hF : P.toAlgHom.comp F = P.toAlgHom) :
    Derivation A P.completedPolynomialRing P.extension.Cotangent := by
  let D := completedSubstitutionDifferenceDerivation P F hF
  let X : Fin P.variableCount → P.completedPolynomialRing := fun i =>
    algebraMap (MvPolynomial (Fin P.variableCount) A) P.completedPolynomialRing
      (MvPolynomial.X i)
  let L : P.completedPolynomialRing →ₗ[A] P.extension.Cotangent := {
    toFun := fun x => ∑ i : Fin P.variableCount,
      algebraMap P.completedPolynomialRing B.carrier
        (completedPartialDeriv P i x) • D (X i)
    map_add' := by
      intro x y
      simp only [map_add, Finset.sum_add_distrib, add_smul]
    map_smul' := by
      intro a x
      simp only [Finset.smul_sum]
      congr 1
      funext i
      calc
        algebraMap P.completedPolynomialRing B.carrier
            (completedPartialDeriv P i (a • x)) • D (X i) =
            (algebraMap A B.carrier a * algebraMap P.completedPolynomialRing
              B.carrier (completedPartialDeriv P i x)) •
              D (X i) := by
                rw [(completedPartialDeriv P i).map_smul, Algebra.smul_def,
                  map_mul, IsScalarTower.algebraMap_apply A
                    P.completedPolynomialRing B.carrier]
        _ = a • P.toAlgHom (completedPartialDeriv P i x) • D (X i) := by
              calc
                _ = algebraMap A B.carrier a •
                    (P.toAlgHom (completedPartialDeriv P i x) • D (X i)) := by
                      rw [mul_smul]
                      rfl
                _ = _ := IsScalarTower.algebraMap_smul
                  (R := A) (A := B.carrier) a _
  }
  exact Derivation.mk' L (by
    intro x y
    dsimp only [L]
    change (∑ i : Fin P.variableCount,
      algebraMap P.completedPolynomialRing B.carrier
        (completedPartialDeriv P i (x * y)) • D (X i)) =
      x • (∑ i : Fin P.variableCount,
        algebraMap P.completedPolynomialRing B.carrier
          (completedPartialDeriv P i y) • D (X i)) +
      y • (∑ i : Fin P.variableCount,
        algebraMap P.completedPolynomialRing B.carrier
          (completedPartialDeriv P i x) • D (X i))
    have hderiv (i : Fin P.variableCount) :
        completedPartialDeriv P i (x * y) =
          x * completedPartialDeriv P i y + y * completedPartialDeriv P i x := by
      simpa only [smul_eq_mul] using (completedPartialDeriv P i).leibniz x y
    simp_rw [hderiv, map_add, map_mul, add_smul, Finset.sum_add_distrib,
      Finset.smul_sum]
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    rw [← IsScalarTower.algebraMap_smul (R := P.completedPolynomialRing)
      (A := B.carrier) x, ← IsScalarTower.algebraMap_smul
        (R := P.completedPolynomialRing) (A := B.carrier) y]
    simp only [mul_smul]
    )

/-- The cotangent module `P.extension.Cotangent` is `I`-adically separated as an `A`-module. -/
public theorem completedCotangent_iInf_coefficient_pow
    {A : Type u} [CommRing A] [IsNoetherianRing A] {I : Ideal A}
    {B : AdicFiniteTypeAlgebra.{u, v} A I}
    (P : CompletedPolynomialPresentation I B)
    [Module A P.extension.Cotangent]
    [IsScalarTower A B.carrier P.extension.Cotangent] :
    ⨅ n : ℕ, I ^ n • (⊤ : Submodule A P.extension.Cotangent) = ⊥ := by
  let : IsNoetherianRing P.completedPolynomialRing :=
    AdicCompletion.isNoetherianRing
      (I.map (MvPolynomial.C : A →+* MvPolynomial (Fin P.variableCount) A))
  let : IsAdicComplete B.adicIdeal B.carrier := B.isAdicallyComplete
  let : Module.Finite B.carrier P.extension.Cotangent :=
    Algebra.Extension.Cotangent.finite (P := P.extension) (by
      show P.ker.FG
      exact Ideal.fg_of_isNoetherianRing P.ker)
  have hsepB : ⨅ n : ℕ, B.adicIdeal ^ n •
      (⊤ : Submodule B.carrier P.extension.Cotangent) = ⊥ :=
    Ideal.iInf_pow_smul_eq_bot_of_le_jacobson B.adicIdeal
      (IsAdicComplete.le_jacobson_bot B.adicIdeal)
  have hfil (n : ℕ) :
      (B.adicIdeal ^ n • (⊤ : Submodule B.carrier P.extension.Cotangent)).restrictScalars A =
        I ^ n • (⊤ : Submodule A P.extension.Cotangent) := by
    rw [show B.adicIdeal ^ n = (I ^ n).map (algebraMap A B.carrier) by
      rw [AdicFiniteTypeAlgebra.adicIdeal, Ideal.map_pow]]
    rw [Ideal.smul_restrictScalars]
    simp
  have hsepA : (⨅ n : ℕ, B.adicIdeal ^ n •
      (⊤ : Submodule B.carrier P.extension.Cotangent)).restrictScalars A = ⊥ := by
    rw [hsepB]
    rfl
  rw [Submodule.restrictScalars_iInf] at hsepA
  simpa only [hfil] using hsepA

/-- The difference derivation `x ↦ [x - F x]` equals `x ↦ ∑ i, (∂x/∂Xᵢ) • [Xᵢ - F Xᵢ]`. -/
public theorem completedSubstitution_taylor
    {A : Type u} [CommRing A] [IsNoetherianRing A] {I : Ideal A}
    {B : AdicFiniteTypeAlgebra.{u, v} A I}
    (P : CompletedPolynomialPresentation I B)
    (F : P.completedPolynomialRing →ₐ[A] P.completedPolynomialRing)
    (hF : P.toAlgHom.comp F = P.toAlgHom) :
    completedSubstitutionDifferenceDerivation P F hF =
      completedSubstitutionTaylorCoordinateDerivation P F hF := by
  let D := completedSubstitutionDifferenceDerivation P F hF
  let E := completedSubstitutionTaylorCoordinateDerivation P F hF
  have hX (i : Fin P.variableCount) : D
      (algebraMap (MvPolynomial (Fin P.variableCount) A) P.completedPolynomialRing
        (MvPolynomial.X i)) = E
      (algebraMap (MvPolynomial (Fin P.variableCount) A) P.completedPolynomialRing
        (MvPolynomial.X i)) := by
    rw [completedSubstitutionDifferenceDerivation_X P F hF i]
    simp [E, completedSubstitutionTaylorCoordinateDerivation,
      completedSubstitutionDifferenceDerivation_X, completedPartialDeriv_polynomial,
      MvPolynomial.pderiv_X, Pi.single_apply]
  have hpoly : ∀ f : MvPolynomial (Fin P.variableCount) A,
      D (algebraMap (MvPolynomial (Fin P.variableCount) A)
        P.completedPolynomialRing f) =
      E (algebraMap (MvPolynomial (Fin P.variableCount) A)
        P.completedPolynomialRing f) := by
    intro f
    induction f using MvPolynomial.induction_on with
    | C a =>
        have hc : algebraMap (MvPolynomial (Fin P.variableCount) A)
            P.completedPolynomialRing (MvPolynomial.C a) =
          algebraMap A P.completedPolynomialRing a := by
          calc
            algebraMap (MvPolynomial (Fin P.variableCount) A) P.completedPolynomialRing
                (MvPolynomial.C a) =
              algebraMap (MvPolynomial (Fin P.variableCount) A) P.completedPolynomialRing
                (algebraMap A (MvPolynomial (Fin P.variableCount) A) a) := by
                  rw [MvPolynomial.algebraMap_eq]
            _ = algebraMap A P.completedPolynomialRing a :=
              IsScalarTower.algebraMap_apply A (MvPolynomial (Fin P.variableCount) A)
                P.completedPolynomialRing a
        rw [hc, D.map_algebraMap, E.map_algebraMap]
    | add f g hf hg => rw [map_add, D.map_add, E.map_add, hf, hg]
    | mul_X f i hf =>
        rw [map_mul, D.leibniz, E.leibniz, hf, hX i]
  let K : Ideal P.completedPolynomialRing :=
    I.map (algebraMap A P.completedPolynomialRing)
  have hKmem (n : ℕ) {x : P.completedPolynomialRing} (hx : x ∈ K ^ n) :
      x ∈ I ^ n • (⊤ : Submodule A P.completedPolynomialRing) := by
    rw [Ideal.smul_top_eq_map, Ideal.map_pow]
    exact hx
  have hD (n : ℕ) (x : P.completedPolynomialRing)
      (hx : x ∈ K ^ n) : D x ∈ I ^ n • (⊤ : Submodule A P.extension.Cotangent) :=
    linearMap_mem_smul_top_pow I D.toLinearMap n x (hKmem n hx)
  have hE (n : ℕ) (x : P.completedPolynomialRing)
      (hx : x ∈ K ^ n) : E x ∈ I ^ n • (⊤ : Submodule A P.extension.Cotangent) :=
    linearMap_mem_smul_top_pow I E.toLinearMap n x (hKmem n hx)
  exact completedPolynomialDerivation_ext_adic P D E hD hE hpoly
    (completedCotangent_iInf_coefficient_pow P)

/-- The map `completedSubstitutionDifferenceMap P F hF` composed after the differential is the
identity minus the map induced by `F` on the lifted cotangent module. -/
public theorem completedSubstitutionDifferenceMap_comp_differential
    {A : Type u} [CommRing A] [IsNoetherianRing A] {I : Ideal A}
    {B : AdicFiniteTypeAlgebra.{u, v} A I}
    (P : CompletedPolynomialPresentation I B)
    (F : P.completedPolynomialRing →ₐ[A] P.completedPolynomialRing)
    (hF : P.toAlgHom.comp F = P.toAlgHom) :
    (completedSubstitutionDifferenceMap P F hF).comp
        (Rig.completedNaiveCotangentComplex B P).liftedDifferential =
      (LinearMap.id : LiftedCotangent (P := P) →ₗ[B.carrier] _) -
        (ULift.moduleEquiv.symm.toLinearMap.comp
          ((Algebra.Extension.Cotangent.map
            (completedSubstitutionEndomorphismHom P F hF)).comp
              ULift.moduleEquiv.toLinearMap)) := by
  classical
  apply LinearMap.ext
  intro element
  cases element with
  | up element =>
    obtain ⟨relation, rfl⟩ := Algebra.Extension.Cotangent.mk_surjective element
    apply ULift.ext
    let K := Rig.completedNaiveCotangentComplex B P
    show (∑ i : Fin P.variableCount,
        K.differential (Algebra.Extension.Cotangent.mk relation) i •
          completedSubstitutionDifferenceGenerator P F hF i) =
      Algebra.Extension.Cotangent.mk relation -
        Algebra.Extension.Cotangent.map (completedSubstitutionEndomorphismHom P F hF)
          (Algebra.Extension.Cotangent.mk relation)
    rw [K.differential_mk, Algebra.Extension.Cotangent.map_mk]
    have identity := congrArg (fun derivation => derivation relation.val)
      (completedSubstitution_taylor P F hF)
    dsimp [completedSubstitutionDifferenceDerivation,
      completedSubstitutionTaylorCoordinateDerivation] at identity
    change Algebra.Extension.Cotangent.mk
        ((Algebra.Extension.Hom.id P.extension).subToKer
          (completedSubstitutionEndomorphismHom P F hF) relation.val) =
      ∑ i : Fin P.variableCount, P.toAlgHom (completedPartialDeriv P i relation.val) •
        completedSubstitutionDifferenceGenerator P F hF i at identity
    show (∑ i : Fin P.variableCount,
        P.toAlgHom (completedPartialDeriv P i relation.val) •
          completedSubstitutionDifferenceGenerator P F hF i) = _
    rw [← identity, ← map_sub]
    congr 1

/-- The degree `-1` component of `completedSubstitutionChainMap P Q minusMap zeroMap comm` is
`minusMap`. -/
public theorem completedSubstitutionChainMap_f_negOne
    {A : Type u} [CommRing A] [IsNoetherianRing A] {I : Ideal A}
    {B : AdicFiniteTypeAlgebra.{u, v} A I}
    (P Q : CompletedPolynomialPresentation I B)
    (minusMap : LiftedCotangent (P := P) →ₗ[B.carrier] LiftedCotangent (P := Q))
    (zeroMap : LiftedDifferentials (P := P) →ₗ[B.carrier] LiftedDifferentials (P := Q))
    (comm : (Rig.completedNaiveCotangentComplex B Q).liftedDifferential.comp
      minusMap = zeroMap.comp
        (Rig.completedNaiveCotangentComplex B P).liftedDifferential) :
    (completedSubstitutionChainMap P Q minusMap zeroMap comm).f (-1) =
      (Rig.completedNaiveCotangentComplex B P).degreeNegOneIso.hom ≫
        ModuleCat.ofHom minusMap ≫
          (Rig.completedNaiveCotangentComplex B Q).degreeNegOneIso.inv := by
  dsimp only [completedSubstitutionChainMap]
  rw [HomologicalComplex.mkHomFromDouble_f₀]
  rfl

/-- The degree `0` component of `completedSubstitutionChainMap P Q minusMap zeroMap comm` is
`zeroMap`. -/
public theorem completedSubstitutionChainMap_f_zero
    {A : Type u} [CommRing A] [IsNoetherianRing A] {I : Ideal A}
    {B : AdicFiniteTypeAlgebra.{u, v} A I}
    (P Q : CompletedPolynomialPresentation I B)
    (minusMap : LiftedCotangent (P := P) →ₗ[B.carrier] LiftedCotangent (P := Q))
    (zeroMap : LiftedDifferentials (P := P) →ₗ[B.carrier] LiftedDifferentials (P := Q))
    (comm : (Rig.completedNaiveCotangentComplex B Q).liftedDifferential.comp
      minusMap = zeroMap.comp
        (Rig.completedNaiveCotangentComplex B P).liftedDifferential) :
    (completedSubstitutionChainMap P Q minusMap zeroMap comm).f 0 =
      (Rig.completedNaiveCotangentComplex B P).degreeZeroIso.hom ≫
        ModuleCat.ofHom zeroMap ≫
          (Rig.completedNaiveCotangentComplex B Q).degreeZeroIso.inv := by
  dsimp only [completedSubstitutionChainMap]
  rw [HomologicalComplex.mkHomFromDouble_f₁]
  rfl

/-- The Jacobian map of a composite `second.comp first` is the composite of the Jacobian maps, for
`second` continuous and commuting with the projections onto `B`. -/
public theorem completedSubstitutionCoordinateMap_comp
    {A : Type u} [CommRing A] [IsNoetherianRing A] {I : Ideal A}
    {B : AdicFiniteTypeAlgebra.{u, v} A I}
    (P Q R : CompletedPolynomialPresentation I B)
    (first : P.completedPolynomialRing →ₐ[A] Q.completedPolynomialRing)
    (second : Q.completedPolynomialRing →ₐ[A] R.completedPolynomialRing)
    (continuousSecond : @Continuous Q.completedPolynomialRing R.completedPolynomialRing
      (RestrictedPowerSeries.polynomialCompletionLimitTopology I
        (Fin Q.variableCount))
      (RestrictedPowerSeries.polynomialCompletionLimitTopology I
        (Fin R.variableCount)) second)
    (compatibleSecond : R.toAlgHom.comp second = Q.toAlgHom) :
    completedSubstitutionCoordinateMap P R (second.comp first) =
      (completedSubstitutionCoordinateMap Q R second).comp
        (completedSubstitutionCoordinateMap P Q first) := by
  classical
  apply LinearMap.ext
  intro vector
  funext coordinate
  show (∑ source, vector source * R.toAlgHom
      (completedPartialDeriv R coordinate (second (first
        (algebraMap (MvPolynomial (Fin P.variableCount) A)
          P.completedPolynomialRing (MvPolynomial.X source)))))) =
    ∑ middle, (∑ source, vector source * Q.toAlgHom
      (completedPartialDeriv Q middle (first
        (algebraMap (MvPolynomial (Fin P.variableCount) A)
          P.completedPolynomialRing (MvPolynomial.X source))))) *
      R.toAlgHom (completedPartialDeriv R coordinate (second
        (algebraMap (MvPolynomial (Fin Q.variableCount) A)
          Q.completedPolynomialRing (MvPolynomial.X middle))))
  have compatible (element : Q.completedPolynomialRing) :
      R.toAlgHom (second element) = Q.toAlgHom element :=
    DFunLike.congr_fun compatibleSecond element
  have chain (source : Fin P.variableCount) :
      R.toAlgHom (completedPartialDeriv R coordinate (second (first
        (algebraMap (MvPolynomial (Fin P.variableCount) A)
          P.completedPolynomialRing (MvPolynomial.X source))))) =
      ∑ middle, Q.toAlgHom (completedPartialDeriv Q middle (first
        (algebraMap (MvPolynomial (Fin P.variableCount) A)
          P.completedPolynomialRing (MvPolynomial.X source)))) *
        R.toAlgHom (completedPartialDeriv R coordinate (second
          (algebraMap (MvPolynomial (Fin Q.variableCount) A)
            Q.completedPolynomialRing (MvPolynomial.X middle)))) := by
    rw [completedSubstitution_chainRule Q R second continuousSecond, map_sum]
    apply Finset.sum_congr rfl
    intro middle middle_mem
    rw [map_mul, compatible]
  simp_rw [chain, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro middle middle_mem
  apply Finset.sum_congr rfl
  intro source source_mem
  ring

/-- The composite of `completedSubstitutionMinusMap P Q` and `completedSubstitutionMinusMap Q P` is
the map induced by the endomorphism `(completedSubstitution Q P).comp (completedSubstitution P Q)`
of `P.extension`. -/
public theorem completedSubstitutionMinusMap_comp
    {A : Type u} [CommRing A] [IsNoetherianRing A] {I : Ideal A}
    {B : AdicFiniteTypeAlgebra.{u, v} A I}
    (P Q : CompletedPolynomialPresentation I B) :
    (completedSubstitutionMinusMap Q P).comp (completedSubstitutionMinusMap P Q) =
      ULift.moduleEquiv.symm.toLinearMap.comp
        ((Algebra.Extension.Cotangent.map (completedSubstitutionEndomorphismHom P
          ((completedSubstitution Q P).comp (completedSubstitution P Q))
          (by rw [← AlgHom.comp_assoc, completedSubstitution_compatible,
            completedSubstitution_compatible]))).comp ULift.moduleEquiv.toLinearMap) := by
  apply LinearMap.ext
  intro element
  cases element with
  | up element =>
    obtain ⟨relation, rfl⟩ := Algebra.Extension.Cotangent.mk_surjective element
    apply ULift.ext
    simp only [completedSubstitutionMinusMap, LinearMap.comp_apply,
      LinearEquiv.coe_coe, ULift.moduleEquiv_apply, ULift.moduleEquiv_symm_apply,
      Algebra.Extension.Cotangent.map_mk]
    rfl

/-- The composite of `completedSubstitutionZeroMap P Q` and `completedSubstitutionZeroMap Q P` is
the Jacobian map of `(completedSubstitution Q P).comp (completedSubstitution P Q)`. -/
public theorem completedSubstitutionZeroMap_comp
    {A : Type u} [CommRing A] [IsNoetherianRing A] {I : Ideal A}
    {B : AdicFiniteTypeAlgebra.{u, v} A I}
    (P Q : CompletedPolynomialPresentation I B) :
    (completedSubstitutionZeroMap Q P).comp (completedSubstitutionZeroMap P Q) =
      ULift.moduleEquiv.symm.toLinearMap.comp
        ((completedSubstitutionCoordinateMap P P
          ((completedSubstitution Q P).comp (completedSubstitution P Q))).comp
            ULift.moduleEquiv.toLinearMap) := by
  apply LinearMap.ext
  intro element
  cases element
  apply ULift.ext
  show completedSubstitutionCoordinateMap Q P (completedSubstitution Q P)
      (completedSubstitutionCoordinateMap P Q (completedSubstitution P Q) _) = _
  rw [completedSubstitutionCoordinateMap_comp P Q P
    (completedSubstitution P Q) (completedSubstitution Q P)
    (continuous_completedSubstitution Q P) (completedSubstitution_compatible Q P)]
  rfl

/-- A homotopy from the identity to an endomorphism of the completed naive cotangent complex of `P`
with components `minusMap` and `zeroMap`, given by a map `homotopyMap` with
`homotopyMap ∘ d = 1 - minusMap` and `d ∘ homotopyMap = 1 - zeroMap`. -/
public noncomputable def completedComplexHomotopy
    {A : Type u} [CommRing A] [IsNoetherianRing A] {I : Ideal A}
    {B : AdicFiniteTypeAlgebra.{u, v} A I}
    (P : CompletedPolynomialPresentation I B)
    (endomorphism : (Rig.completedNaiveCotangentComplex B P).cochainComplex ⟶
      (Rig.completedNaiveCotangentComplex B P).cochainComplex)
    (minusMap : LiftedCotangent (P := P) →ₗ[B.carrier] LiftedCotangent (P := P))
    (zeroMap : LiftedDifferentials (P := P) →ₗ[B.carrier] LiftedDifferentials (P := P))
    (homotopyMap : LiftedDifferentials (P := P) →ₗ[B.carrier] LiftedCotangent (P := P))
    (minusComponent : endomorphism.f (-1) =
      (Rig.completedNaiveCotangentComplex B P).degreeNegOneIso.hom ≫
        ModuleCat.ofHom minusMap ≫
          (Rig.completedNaiveCotangentComplex B P).degreeNegOneIso.inv)
    (zeroComponent : endomorphism.f 0 =
      (Rig.completedNaiveCotangentComplex B P).degreeZeroIso.hom ≫
        ModuleCat.ofHom zeroMap ≫
          (Rig.completedNaiveCotangentComplex B P).degreeZeroIso.inv)
    (minusIdentity : homotopyMap.comp
      (Rig.completedNaiveCotangentComplex B P).liftedDifferential =
        LinearMap.id - minusMap)
    (zeroIdentity : (Rig.completedNaiveCotangentComplex B P).liftedDifferential.comp
      homotopyMap = LinearMap.id - zeroMap) :
    Homotopy (𝟙 _) endomorphism := by
  classical
  let K := Rig.completedNaiveCotangentComplex B P
  let homotopy : (source target : ℤ) → K.cochainComplex.X source ⟶
      K.cochainComplex.X target := fun source target =>
    if source_eq : source = 0 then
      if target_eq : target = -1 then
        eqToHom (congrArg K.cochainComplex.X source_eq) ≫ K.degreeZeroIso.hom ≫
          ModuleCat.ofHom homotopyMap ≫ K.degreeNegOneIso.inv ≫
            eqToHom (congrArg K.cochainComplex.X target_eq.symm)
      else 0
    else 0
  refine ⟨homotopy, ?_, ?_⟩
  · intro source target not_related
    dsimp [homotopy]
    split_ifs with source_eq target_eq
    · subst source
      subst target
      exact False.elim (not_related (by rfl))
    all_goals rfl
  · intro degree
    by_cases degree_minus : degree = -1
    · subst degree
      rw [dNext_eq homotopy (show (ComplexShape.up ℤ).Rel (-1) 0 from rfl),
        prevD_eq homotopy (show (ComplexShape.up ℤ).Rel (-2) (-1) from rfl),
        HomologicalComplex.id_f, minusComponent, K.cochainComplex_d]
      simp only [homotopy, show (-1 : ℤ) ≠ 0 by norm_num, ↓reduceDIte,
        eqToHom_refl, Category.id_comp,
        Category.comp_id, CategoryTheory.Limits.zero_comp, add_zero,
        Category.assoc, Iso.inv_hom_id_assoc]
      have identity : ModuleCat.ofHom K.liftedDifferential ≫
          ModuleCat.ofHom homotopyMap + ModuleCat.ofHom minusMap = 𝟙 _ := by
        rw [← ModuleCat.ofHom_comp, minusIdentity]
        ext element
        simp
      have liftedIdentity := congrArg (fun morphism =>
        K.degreeNegOneIso.hom ≫ morphism ≫ K.degreeNegOneIso.inv) identity
      simpa only [Preadditive.comp_add, Preadditive.add_comp, Category.assoc,
        Category.comp_id, Category.id_comp, Iso.hom_inv_id] using liftedIdentity.symm
    · by_cases degree_zero : degree = 0
      · subst degree
        rw [dNext_eq homotopy (show (ComplexShape.up ℤ).Rel 0 1 from rfl),
          prevD_eq homotopy (show (ComplexShape.up ℤ).Rel (-1) 0 from rfl),
          HomologicalComplex.id_f, zeroComponent, K.cochainComplex_d]
        simp only [homotopy, show (1 : ℤ) ≠ 0 by norm_num, ↓reduceDIte,
          eqToHom_refl, Category.id_comp,
          Category.comp_id, CategoryTheory.Limits.comp_zero, zero_add,
          Category.assoc, Iso.inv_hom_id_assoc]
        have identity : ModuleCat.ofHom homotopyMap ≫
            ModuleCat.ofHom K.liftedDifferential + ModuleCat.ofHom zeroMap = 𝟙 _ := by
          rw [← ModuleCat.ofHom_comp, zeroIdentity]
          ext element
          simp
        have liftedIdentity := congrArg (fun morphism =>
          K.degreeZeroIso.hom ≫ morphism ≫ K.degreeZeroIso.inv) identity
        simpa only [Preadditive.comp_add, Preadditive.add_comp, Category.assoc,
          Category.comp_id, Category.id_comp, Iso.hom_inv_id] using liftedIdentity.symm
      · exact (HomologicalComplex.isZero_double_X
          (ModuleCat.ofHom K.liftedDifferential)
          (show (ComplexShape.up ℤ).Rel (-1) 0 from rfl)
          degree degree_minus degree_zero).eq_of_src _ _

/-- The morphism from the completed naive cotangent complex of `P` to that of `Q` induced by
`completedSubstitution P Q`. -/
public noncomputable abbrev completedPresentationChainMap
    {A : Type u} [CommRing A] [IsNoetherianRing A] {I : Ideal A}
    {B : AdicFiniteTypeAlgebra.{u, v} A I}
    (P Q : CompletedPolynomialPresentation I B) :=
  completedSubstitutionChainMap P Q (completedSubstitutionMinusMap P Q)
    (completedSubstitutionZeroMap P Q) (completedSubstitution_chainCondition P Q)

/-- A homotopy from the identity to the composite of the morphisms
`completedPresentationChainMap P Q` and `completedPresentationChainMap Q P`. -/
public noncomputable def completedPresentationCompositionHomotopy
    {A : Type u} [CommRing A] [IsNoetherianRing A] {I : Ideal A}
    {B : AdicFiniteTypeAlgebra.{u, v} A I}
    (P Q : CompletedPolynomialPresentation I B) :
    Homotopy (𝟙 _) (completedPresentationChainMap P Q ≫
      completedPresentationChainMap Q P) := by
  let F := (completedSubstitution Q P).comp (completedSubstitution P Q)
  have compatible : P.toAlgHom.comp F = P.toAlgHom := by
    rw [← AlgHom.comp_assoc, completedSubstitution_compatible,
      completedSubstitution_compatible]
  refine completedComplexHomotopy P _
    ((completedSubstitutionMinusMap Q P).comp (completedSubstitutionMinusMap P Q))
    ((completedSubstitutionZeroMap Q P).comp (completedSubstitutionZeroMap P Q))
    (completedSubstitutionDifferenceMap P F compatible) ?_ ?_ ?_ ?_
  · rw [HomologicalComplex.comp_f,
      completedSubstitutionChainMap_f_negOne,
      completedSubstitutionChainMap_f_negOne]
    simp only [Category.assoc, Iso.inv_hom_id_assoc, ModuleCat.ofHom_comp]
  · rw [HomologicalComplex.comp_f,
      completedSubstitutionChainMap_f_zero,
      completedSubstitutionChainMap_f_zero]
    simp only [Category.assoc, Iso.inv_hom_id_assoc, ModuleCat.ofHom_comp]
  · rw [completedSubstitutionMinusMap_comp]
    exact completedSubstitutionDifferenceMap_comp_differential P F compatible
  · rw [completedSubstitutionZeroMap_comp]
    exact completedSubstitutionDifferenceMap_differential P F compatible

/-- The completed naive cotangent complexes associated to two completed polynomial
presentations of the same `I`-adically complete algebra are homotopy equivalent. -/
@[stacks 0GAE]
public theorem completedNaiveCotangentComplex_homotopyEquiv
    {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    (B : AdicFiniteTypeAlgebra.{u, v} A I)
    (P Q : CompletedPolynomialPresentation I B) :
    Nonempty (HomotopyEquiv
      (Rig.completedNaiveCotangentComplex B P).cochainComplex
      (Rig.completedNaiveCotangentComplex B Q).cochainComplex) :=
  ⟨{ hom := completedPresentationChainMap P Q
     inv := completedPresentationChainMap Q P
     homotopyHomInvId := (completedPresentationCompositionHomotopy P Q).symm
     homotopyInvHomId := (completedPresentationCompositionHomotopy Q P).symm }⟩

end Rig

end
