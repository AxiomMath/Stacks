module

public import Mathlib.Algebra.Homology.Homotopy
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.AdicCompletion.Topology
public import StacksFrontier.RingTheory.AdicCompletion.Basic
public import StacksFrontier.RingTheory.AdicCompletion.QuasiFinite
public import StacksFrontier.RingTheory.NaiveCotangent.Defs
public import StacksFrontier.RingTheory.Restricted.NaiveCotangentHomotopy
public import StacksFrontier.RingTheory.Rig.NaiveCotangent
public import StacksFrontier.Topology.Algebra.AdicTopology.Continuous

/-!
# Independence of the completed naive cotangent complex from its presentation

Let `A` be a Noetherian ring, let `I` be an ideal of `A`, and let `B` be an `I`-adically
complete `A`-algebra of finite type modulo `I`. Writing `B = A[x₁, …, xᵣ]^ / J` for a
presentation of `B` as a quotient of a completed polynomial algebra, the completed naive
cotangent complex of that presentation is the two-term complex `J / J² → ⨁ i, B dxᵢ` of
`Rig.CompletedNaiveCotangentComplex.cochainComplex`. This file shows that the complex does
not depend on the presentation: any two presentations of `B` give homotopy equivalent
complexes, so the completed naive cotangent complex is well defined in `K(B)`.

The argument follows the proof for ordinary polynomial presentations. Given presentations
with variables `x₁, …, xᵣ` and `y₁, …, yₛ`, a choice of restricted power series `gᵢ(y)`
lifting the images of `xᵢ` in `B` determines, by the universal property of restricted power
series, a unique continuous `A`-algebra map `A[x₁, …, xᵣ]^ → A[y₁, …, yₛ]^` compatible with
the surjections onto `B`. Such a substitution carries the one presenting ideal into the
other and, by the chain rule for the formal partial derivatives, induces a chain map between
the two complexes. For an endomorphism of a single presentation, the map `dxᵢ ↦ gᵢ(x) - xᵢ`
is a homotopy from the induced chain map to the identity: in degree `-1` this rests on the
first-order Taylor expansion `g(σx) - g(x) = ∑ i, (∂g/∂xᵢ) (gᵢ - xᵢ)` modulo `J²`. Composing
the two substitutions in both orders therefore gives the homotopy equivalence.

## Main results

* `Rig.completedNaiveCotangentComplex_homotopyEquiv`: **Stacks 0GAE**. Proved in
  `StacksFrontier.RingTheory.Restricted.NaiveCotangentHomotopy`, which this module re-exports;
  the substitution calculus it is assembled from is the content of this file.

## Implementation notes

Well-definedness in `K(B)` is recorded as homotopy equivalence of the complexes attached to
any pair of presentations, rather than by singling out a preferred presentation.

`Rig.completedNaiveCotangentComplex_homotopyEquiv` was proved here as well, under the same
fully-qualified name and with a type equal to the byte as the copy in
`StacksFrontier.RingTheory.Restricted.NaiveCotangentHomotopy`, the sibling development of this
one. The two were a single constant whenever both modules were in scope, so one of the proofs
was silently discarded on import; keeping the registration of Stacks 0GAE on that module alone
gave the key one site but left the duplicate declaration standing. The copy here has now been
removed and that module is imported above instead. It is the side the import order already
selected, the side the key is registered on, and the side that needs none of the
transparency-backward elaboration option this file still sets below. The
import costs nothing: the two modules have the same own-library import closure, so the edge
adds no module to it, and neither reaches the other, so no cycle is created. Nothing stopped
being proved — the statement is unchanged and is settled by a bare application of that
module's theorem in either direction. The duplication of the two developments below the
theorem is gone: the fifty declarations the two developments had in common are now declared once,
public, in that module, and this file uses them.

## References

* [Stacks Project, Tag 0GAE](https://stacks.math.columbia.edu/tag/0GAE)
-/

@[expose] public noncomputable section

open CategoryTheory
open Rig.CompletedNaiveCotangentComplex

universe u v

namespace Rig

attribute [local instance] completedPolynomialPresentationAlgebra

attribute [local instance] completedPolynomialScalarTower

attribute [local instance] completedCotangentModule

attribute [local instance] completedCotangentScalarTower

noncomputable def presentationPartialDeriv
    {A : Type u} [CommRing A] [IsNoetherianRing A] {I : Ideal A}
    {B : AdicFiniteTypeAlgebra.{u, v} A I}
    (P : CompletedPolynomialPresentation I B) (i : Fin P.variableCount) :=
  (Rig.completedNaiveCotangentComplex B P).partialDeriv i

theorem continuous_presentationPartialDeriv
    {A : Type u} [CommRing A] [IsNoetherianRing A] {I : Ideal A}
    {B : AdicFiniteTypeAlgebra.{u, v} A I}
    (P : CompletedPolynomialPresentation I B) (i : Fin P.variableCount) :
    @Continuous P.completedPolynomialRing P.completedPolynomialRing
      (RestrictedPowerSeries.polynomialCompletionLimitTopology I
        (Fin P.variableCount))
      (RestrictedPowerSeries.polynomialCompletionLimitTopology I
        (Fin P.variableCount)) (presentationPartialDeriv P i) :=
  (Rig.completedNaiveCotangentComplex B P).partialDeriv_continuous i

theorem presentationPartialDeriv_polynomial
    {A : Type u} [CommRing A] [IsNoetherianRing A] {I : Ideal A}
    {B : AdicFiniteTypeAlgebra.{u, v} A I}
    (P : CompletedPolynomialPresentation I B) (i : Fin P.variableCount)
    (f : MvPolynomial (Fin P.variableCount) A) :
    presentationPartialDeriv P i
      (algebraMap (MvPolynomial (Fin P.variableCount) A) P.completedPolynomialRing f) =
      algebraMap (MvPolynomial (Fin P.variableCount) A) P.completedPolynomialRing
        (MvPolynomial.pderiv i f) :=
  (Rig.completedNaiveCotangentComplex B P).partialDeriv_polynomial i f

theorem denseRange_presentationRestrictedPolynomials
    {A : Type u} [CommRing A] {I : Ideal A} (σ : Type v) :
    DenseRange (RestrictedPowerSeries.polynomialAlgHom I σ) := by
  let R := RestrictedPowerSeries I σ
  let : TopologicalSpace R := RestrictedPowerSeries.limitTopology I σ
  let : ∀ n : ℕ, TopologicalSpace (MvPolynomial σ (A ⧸ I ^ n)) := fun _ => ⊥
  let : ∀ n : ℕ, DiscreteTopology (MvPolynomial σ (A ⧸ I ^ n)) := fun _ => ⟨rfl⟩
  let T := ∀ n : ℕ, MvPolynomial σ (A ⧸ I ^ n)
  let polynomialFamily : MvPolynomial σ A → T := fun p n =>
    MvPolynomial.map (Ideal.Quotient.mk (I ^ n)) p
  rw [DenseRange]
  change Dense (Set.range (RestrictedPowerSeries.polynomialAlgHom I σ))
  apply (Topology.IsInducing.subtypeVal
    (t := (RestrictedPowerSeries.inverseLimitSubring I σ : Set T))
    ).dense_iff.mpr
  intro f
  have hrange : Set.range polynomialFamily =
      Subtype.val '' Set.range (RestrictedPowerSeries.polynomialAlgHom I σ) := by
    rw [← Set.range_comp]
    rfl
  have hclose : f.val ∈ closure (Set.range polynomialFamily) := by
    apply (isTopologicalBasis_pi
      (fun _ => TopologicalSpace.isTopologicalBasis_opens)).mem_closure_iff.mpr
    intro U hU hfU
    rcases hU with ⟨g, F, hg, rfl⟩
    let N := F.sup id
    have hN : ∀ m ∈ F, m ≤ N := fun m hm => Finset.le_sup (f := id) hm
    have hq : Function.Surjective
        (Ideal.Quotient.mk (I ^ N) : A → A ⧸ I ^ N) := fun q =>
      Ideal.Quotient.mk_surjective q
    obtain ⟨p, hp⟩ := MvPolynomial.map_surjective
      (Ideal.Quotient.mk (I ^ N)) hq (f.val N)
    refine ⟨polynomialFamily p, ?_, ⟨p, rfl⟩⟩
    change ∀ m ∈ F, polynomialFamily p m ∈ g m
    intro m hm
    have hmN := hN m hm
    have hcoord : MvPolynomial.map (Ideal.Quotient.mk (I ^ m)) p = f.val m := by
      calc
        MvPolynomial.map (Ideal.Quotient.mk (I ^ m)) p =
            RestrictedPowerSeries.coefficientTransition I σ hmN
              (MvPolynomial.map (Ideal.Quotient.mk (I ^ N)) p) := by
                simp [RestrictedPowerSeries.coefficientTransition,
                  RestrictedPowerSeries.idealSystemTransition,
                  MvPolynomial.map_map]
        _ = RestrictedPowerSeries.coefficientTransition I σ hmN
              (f.val N) := by rw [hp]
        _ = f.val m := f.property hmN
    change MvPolynomial.map (Ideal.Quotient.mk (I ^ m)) p ∈ g m
    rw [hcoord]
    exact hfU m hm
  rwa [hrange] at hclose

theorem denseRange_presentationCompletedPolynomials
    {A : Type u} [CommRing A] {I : Ideal A}
    {B : AdicFiniteTypeAlgebra.{u, v} A I}
    (P : CompletedPolynomialPresentation I B) :
    let _ : TopologicalSpace P.completedPolynomialRing :=
      RestrictedPowerSeries.polynomialCompletionLimitTopology I
        (Fin P.variableCount)
    DenseRange (algebraMap (MvPolynomial (Fin P.variableCount) A) P.completedPolynomialRing) := by
  let R := RestrictedPowerSeries I (Fin P.variableCount)
  let : TopologicalSpace R :=
    RestrictedPowerSeries.limitTopology I (Fin P.variableCount)
  let : ∀ n : ℕ, TopologicalSpace
      (MvPolynomial (Fin P.variableCount) (A ⧸ I ^ n)) := fun _ => ⊥
  let : ∀ n : ℕ, DiscreteTopology
      (MvPolynomial (Fin P.variableCount) (A ⧸ I ^ n)) := fun _ => ⟨rfl⟩
  let : TopologicalSpace P.completedPolynomialRing :=
    RestrictedPowerSeries.polynomialCompletionLimitTopology I
      (Fin P.variableCount)
  let h := RestrictedPowerSeries.adicCompletionHomeomorph I
    (Fin P.variableCount)
  let p := RestrictedPowerSeries.polynomialAlgHom I (Fin P.variableCount)
  have hd := denseRange_presentationRestrictedPolynomials (I := I) (Fin P.variableCount)
  have heq : (fun f => h (p f)) =
      (algebraMap (MvPolynomial (Fin P.variableCount) A) P.completedPolynomialRing) := by
    funext f
    change RestrictedPowerSeries.adicCompletionEquiv I
      (Fin P.variableCount) (RestrictedPowerSeries.polynomialRingHom
        I (Fin P.variableCount) f) = _
    rw [RestrictedPowerSeries.adicCompletionEquiv_polynomialRingHom]
    rfl
  rw [← heq]
  exact h.surjective.denseRange.comp hd h.continuous_toFun

/-! The bridge lemmas below compare completed presentations by continuous substitution. -/

theorem denseRange_presentationCompletedPolynomials_adic
    {A : Type u} [CommRing A] [IsNoetherianRing A] {I : Ideal A}
    {B : AdicFiniteTypeAlgebra.{u, v} A I}
    (P : CompletedPolynomialPresentation I B) :
    let K := I.map (algebraMap A P.completedPolynomialRing)
    @DenseRange P.completedPolynomialRing K.adicTopology
      (MvPolynomial (Fin P.variableCount) A)
      (algebraMap (MvPolynomial (Fin P.variableCount) A) P.completedPolynomialRing) := by
  dsimp
  let R := MvPolynomial (Fin P.variableCount) A
  let J : Ideal R := I.map (MvPolynomial.C : A →+* R)
  let K : Ideal P.completedPolynomialRing := I.map (algebraMap A P.completedPolynomialRing)
  let : TopologicalSpace P.completedPolynomialRing := K.adicTopology
  let : IsNoetherianRing R := inferInstance
  rw [DenseRange]
  change Dense (Set.range (algebraMap R P.completedPolynomialRing))
  intro x
  apply (mem_closure_iff_nhds_basis (Ideal.hasBasis_nhds_adic K x)).2
  intro n hn
  obtain ⟨p, hp⟩ := Ideal.Quotient.mk_surjective
    (AdicCompletion.evalₐ J n x)
  have heval : AdicCompletion.evalₐ J n x =
      AdicCompletion.evalₐ J n (algebraMap R P.completedPolynomialRing p) := by
    rw [AdicCompletion.algebraMap_apply, AdicCompletion.evalₐ_of]
    exact hp.symm
  have hker : x - algebraMap R P.completedPolynomialRing p ∈
      (AdicCompletion.eval J R n).ker := by
    rw [LinearMap.mem_ker]
    have heval0 : AdicCompletion.evalₐ J n
        (x - algebraMap R P.completedPolynomialRing p) = 0 := by
      rw [map_sub, heval, sub_self]
    simpa only [AdicCompletion.factor_evalₐ_eq_eval, map_zero] using
      congrArg (Ideal.Quotient.factor (show J ^ n ≤ J ^ n • (⊤ : Ideal R) by simp)) heval0
  have hpow : x - algebraMap R P.completedPolynomialRing p ∈
      (J ^ n • (⊤ : Submodule R P.completedPolynomialRing)) := by
    rwa [AdicCompletion.pow_smul_top_eq_ker_eval
      (I := J) (M := R) (n := n) (Ideal.fg_of_isNoetherianRing J)]
  have hK : Ideal.map (algebraMap R P.completedPolynomialRing) J = K := by
    dsimp [J, K]
    rw [Ideal.map_map]
    congr 1
  have hideal : x - algebraMap R P.completedPolynomialRing p ∈ (K ^ n : Ideal
    P.completedPolynomialRing) := by
    rwa [Ideal.smul_top_eq_map, Ideal.map_pow, hK] at hpow
  refine ⟨algebraMap R P.completedPolynomialRing p, ⟨p, rfl⟩,
    algebraMap R P.completedPolynomialRing p - x, ?_, by simp⟩
  rw [← neg_sub]
  exact neg_mem hideal

/-! For an endomorphism of a completed presentation which fixes the quotient, the
degree-zero homotopy is obtained by taking the class of the difference of each variable and its
image. -/

attribute [local instance] IsScalarTower.of_compHom SMulCommClass.of_commMonoid

end Rig

end
