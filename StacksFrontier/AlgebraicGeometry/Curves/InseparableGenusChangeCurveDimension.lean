module

public import StacksFrontier.AlgebraicGeometry.Curves.InseparableGenusChangeCurve
public import StacksFrontier.AlgebraicGeometry.Curves.PlaneCurveIdeal
public import StacksFrontier.AlgebraicGeometry.Properties.CohenMacaulay
public import StacksFrontier.RingTheory.MvPolynomial.HypersurfaceDimension
public import StacksFrontier.RingTheory.RegularLocalRing.Basic
public import StacksFrontier.Topology.Dimension.LocalKrullDim
public import StacksFrontier.Topology.Dimension.NowhereDense
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The plane cubic of [Stacks, Tag 0CD1] is one-dimensional with no embedded points

Let `Z = Proj (k[T₀, T₁, T₂] ⧸ (F))` be the plane cubic of [Stacks, Tag 0CD1], with ideal of
equations `(F)`. This file proves that every irreducible component of `Z` has dimension one and
that `Z` has no embedded points, so that the statements of [Stacks, Tag 0CD1] hold with no
hypothesis on `Z`.

## Main results

* `isCohenMacaulayRing_of_isRegularRing`: A regular ring is Cohen–Macaulay.
* `AlgebraicGeometry.isCohenMacaulay_of_isRegular`: A regular scheme is Cohen–Macaulay.
* `AlgebraicGeometry.irreducibleSpace_proj_of_isDomain`: `Proj` of a nonempty graded domain is
  irreducible.
* `Stacks.Curves.InseparableGenus.topologicalKrullDim_planeCubicCurve`: `Z` has dimension one.
* `Stacks.Curves.InseparableGenus.hasNoEmbeddedPoints_planeCubicCurve`: `Z` has no embedded
  points.
* `Stacks.Curves.InseparableGenus.planeCubicCurve_isRegular_and_genus_ne`: [Stacks, Tag 0CD1] for
  the curve `Z`.

## Implementation notes

`Z` is irreducible, because `k[T₀, T₁, T₂] ⧸ (F)` is a domain and the zero ideal is a generic
point of `Proj` of a graded domain. Its dimension is computed on the charts `Z ∩ D₊(T₀)` and
`Z ∩ D₊(T₁)`, which cover `Z`: the ring of sections of `Z ∩ D₊(Tⱼ)` is
`k[Y₀, Y₁] ⧸ (F(Tⱼ = 1))`, a hypersurface in the affine plane, of Krull dimension one.

In dimension one the absence of embedded points is Cohen–Macaulayness ([Stacks, Tag 0BXG],
[Stacks, Tag 0BYB]), and `Z` is Cohen–Macaulay because it is regular.

## References

* [Stacks Project, Tag 0CD1](https://stacks.math.columbia.edu/tag/0CD1)
* [Stacks Project, Tag 0BYB](https://stacks.math.columbia.edu/tag/0BYB)
* [Stacks Project, Tag 0BXG](https://stacks.math.columbia.edu/tag/0BXG)
* [Stacks Project, Tag 0B7I](https://stacks.math.columbia.edu/tag/0B7I)
* [Stacks Project, Tag 00NQ](https://stacks.math.columbia.edu/tag/00NQ)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace
open AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpectrum.Proj (idealOfClosedSubscheme)
open Stacks.RingTheory.HomogeneousQuotient (quotientGrading)
open Stacks.ProjectiveChart (dehomCoeff subschemeChart chartQuotientEquiv
  isAffineOpen_subschemeChart)
open Stacks.AlgebraicGeometry.ProjPolyChart (projToSpecCoeff)

universe u w

/-! ### A regular scheme is Cohen–Macaulay -/

/-- **A regular ring is Cohen–Macaulay.** Every localization at a prime is a regular local ring,
and the depth of a regular local ring at its maximal ideal is its Krull dimension, by
[Stacks, Tag 00NQ]. -/
theorem isCohenMacaulayRing_of_isRegularRing (B : Type*) [CommRing B] [IsRegularRing B] :
    IsCohenMacaulayRing B := by
  rw [isCohenMacaulayRing_iff]
  intro q _
  let R := Localization.AtPrime q
  have hne : IsLocalRing.maximalIdeal R • (⊤ : Submodule R R) ≠ ⊤ := by
    simpa using (IsLocalRing.maximalIdeal.isMaximal R).ne_top
  have hd : localRingDepth R =
      Module.depth R (IsLocalRing.maximalIdeal R) R := by
    rw [localRingDepth, Module.depth, ite_eq_right hne]
    exact le_antisymm (iSup_le fun s => le_iSup₂_of_le s.val s.property le_rfl)
      (iSup_le fun rs => iSup_le fun hrs => le_iSup_of_le ⟨rs, hrs⟩ le_rfl)
  change (localRingDepth R : WithBot ℕ∞) = ringKrullDim R
  rw [hd]
  exact_mod_cast
    (IsRegularLocalRing.isRegular_and_isRegularLocalRing_quotient_and_isMaximalCohenMacaulay R).2

/-- **A regular scheme is Cohen–Macaulay**, [Stacks, Tag 02IS] implies [Stacks, Tag 02IO]. Each
point has an affine open on which the ring of sections is regular, and a regular ring is
Cohen–Macaulay. -/
@[ega "IV 7.3.8", ega "IV 7.3.9" "(iv)"]
theorem AlgebraicGeometry.isCohenMacaulay_of_isRegular {X : Scheme.{u}} (hX : IsRegular X) :
    IsCohenMacaulay X := by
  rw [isCohenMacaulay_iff]
  intro x
  obtain ⟨U, hx, hreg⟩ := hX x
  exact ⟨U, hx, inferInstance, isCohenMacaulayRing_of_isRegularRing _⟩

/-! ### The dimension of an affine open, and `Proj` of a graded domain -/

/-- **The dimension of an affine open is the Krull dimension of its ring of sections.** The affine
open is homeomorphic to the spectrum of that ring. -/
@[ega "IV 5.1.1" "more general"]
theorem AlgebraicGeometry.topologicalKrullDim_coe_eq_ringKrullDim_of_isAffineOpen
    {X : Scheme.{u}} (U : X.Opens) (hU : IsAffineOpen U) :
    topologicalKrullDim (U : Set X) = ringKrullDim Γ(X, U) := by
  rw [← PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim]
  exact IsHomeomorph.topologicalKrullDim_eq _ hU.isoSpec.hom.homeomorph.isHomeomorph

/-- **The zero ideal as a point of `Proj` of a graded domain.** It is a homogeneous prime, and it
is a *relevant* one as soon as `Proj 𝒜` has any point at all, since the irrelevant ideal is then
not contained in the zero ideal. -/
def AlgebraicGeometry.projBot {A : Type u} {σ : Type w} [CommRing A] [SetLike σ A]
    [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [_root_.GradedRing 𝒜] [IsDomain A]
    [Nonempty (AlgebraicGeometry.Proj 𝒜)] : ProjectiveSpectrum 𝒜 :=
  ⟨⊥, by simpa using (inferInstance : (⊥ : Ideal A).IsPrime), by
    obtain ⟨x⟩ := ‹Nonempty (AlgebraicGeometry.Proj 𝒜)›
    exact fun h => x.not_irrelevant_le (h.trans bot_le)⟩

/-- The homogeneous ideal of `AlgebraicGeometry.projBot 𝒜` is the zero ideal. -/
@[simp] theorem AlgebraicGeometry.asHomogeneousIdeal_projBot {A : Type u} {σ : Type w}
    [CommRing A] [SetLike σ A] [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [_root_.GradedRing 𝒜]
    [IsDomain A] [Nonempty (AlgebraicGeometry.Proj 𝒜)] :
    (AlgebraicGeometry.projBot 𝒜).asHomogeneousIdeal = ⊥ := rfl

/-- **The zero ideal is the generic point of `Proj` of a graded domain**: every homogeneous prime
contains it, so every point lies in the closure of that one. -/
theorem AlgebraicGeometry.isGenericPoint_projBot {A : Type u} {σ : Type w} [CommRing A]
    [SetLike σ A] [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [_root_.GradedRing 𝒜] [IsDomain A]
    [Nonempty (AlgebraicGeometry.Proj 𝒜)] :
    closure ({AlgebraicGeometry.projBot 𝒜} : Set (ProjectiveSpectrum 𝒜)) = Set.univ :=
  Set.eq_univ_of_forall fun x =>
    (ProjectiveSpectrum.le_iff_mem_closure 𝒜 (AlgebraicGeometry.projBot 𝒜) x).mp
      (show (AlgebraicGeometry.projBot 𝒜).asHomogeneousIdeal ≤ x.asHomogeneousIdeal from bot_le)

/-- **`Proj` of a nonempty graded domain is irreducible.** The zero ideal is a relevant
homogeneous prime, hence a generic point by
`AlgebraicGeometry.isGenericPoint_projBot`, and a space with a generic point is irreducible. -/
theorem AlgebraicGeometry.irreducibleSpace_proj_of_isDomain {A : Type u} {σ : Type w} [CommRing A]
    [SetLike σ A] [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [_root_.GradedRing 𝒜] [IsDomain A]
    [Nonempty (AlgebraicGeometry.Proj 𝒜)] : IrreducibleSpace (AlgebraicGeometry.Proj 𝒜) := by
  refine (irreducibleSpace_def _).mpr ?_
  change IsIrreducible (Set.univ : Set (ProjectiveSpectrum 𝒜))
  rw [← AlgebraicGeometry.isGenericPoint_projBot 𝒜]
  exact isIrreducible_singleton.closure

namespace Stacks.Curves.InseparableGenus

attribute [local instance] MvPolynomial.gradedAlgebra

/-! ### The two dehomogenizations are nonzero non-units -/

/-- The substitution `Y₀ = 0`, `Y₁ = Y` of the affine plane into the affine line; it carries both
dehomogenizations of the cubic to a polynomial of degree three. -/
def chartCollapse (k : Type u) [Field k] :
    MvPolynomial (Fin 2) k →+* Polynomial k :=
  (MvPolynomial.aeval (R := k)
    (fun j : Fin 2 => if j = 0 then 0 else Polynomial.X)).toRingHom

/-- Under the substitution `Y₀ = 0`, `Y₁ = Y`, the dehomogenization of the cubic on `D₊(T₀)` is
`a - Y³`. -/
theorem chartCollapse_dehomCoeff_zero (k : Type u) [Field k] (a : k) :
    chartCollapse k (dehomCoeff k (0 : Fin 3) (planeCubic k a)) =
      Polynomial.C a - Polynomial.X ^ 3 := by
  rw [dehomCoeff_planeCubic_zero, chartCollapse]
  simp
  ring

/-- Under the substitution `Y₀ = 0`, `Y₁ = Y`, the dehomogenization of the cubic on `D₊(T₁)` is
`-Y³`. -/
theorem chartCollapse_dehomCoeff_one (k : Type u) [Field k] (a : k) :
    chartCollapse k (dehomCoeff k (1 : Fin 3) (planeCubic k a)) =
      -(Polynomial.X ^ 3) := by
  rw [dehomCoeff_planeCubic_one, chartCollapse]
  simp

/-- **Neither dehomogenization of the cubic is zero or a unit.** Substituting `Y₀ = 0`, `Y₁ = Y`
carries them to `a - Y³` and to `-Y³`, both of degree three in one variable; a ring homomorphism
carries zero to zero and a unit to a unit, and a unit of `k[Y]` has degree zero. -/
theorem dehomCoeff_planeCubic_ne_zero_and_not_isUnit (k : Type u) [Field k] (a : k) {j : Fin 3}
    (hj : j = 0 ∨ j = 1) :
    dehomCoeff k j (planeCubic k a) ≠ 0 ∧ ¬ IsUnit (dehomCoeff k j (planeCubic k a)) := by
  have key : ∀ g : MvPolynomial (Fin 2) k, (chartCollapse k g).natDegree = 3 →
      g ≠ 0 ∧ ¬ IsUnit g := fun g hg => by
    refine ⟨fun h => ?_, fun h => ?_⟩
    · rw [h, map_zero, Polynomial.natDegree_zero] at hg
      omega
    · rw [Polynomial.natDegree_eq_zero_of_isUnit (h.map (chartCollapse k))] at hg
      omega
  rcases hj with rfl | rfl
  · refine key _ ?_
    rw [chartCollapse_dehomCoeff_zero, show Polynomial.C a - Polynomial.X ^ 3 =
      -(Polynomial.X ^ 3 - Polynomial.C a) by ring, Polynomial.natDegree_neg,
      Polynomial.natDegree_X_pow_sub_C]
  · refine key _ ?_
    rw [chartCollapse_dehomCoeff_one, Polynomial.natDegree_neg, Polynomial.natDegree_X_pow]

/-! ### The dimension of the charts -/

/-- The cubic is homogeneous of degree `3 • 1`. -/
theorem planeCubic_mem_homogeneousSubmodule_smul (k : Type u) [Field k] (a : k) :
    planeCubic k a ∈ MvPolynomial.homogeneousSubmodule (Fin 3) k (3 • 1) := by
  simpa using (MvPolynomial.mem_homogeneousSubmodule 3 _).2 (planeCubic_isHomogeneous k a)

/-- **Each of the two charts of the curve has dimension one.** The chart is the affine open
`Z ∩ D₊(Tⱼ)`, whose ring of sections is `k[Y₀, Y₁] ⧸ (F(Tⱼ = 1))` by
`Stacks.ProjectiveChart.chartQuotientEquiv`; a hypersurface in the affine plane over a field has
Krull dimension one. -/
theorem topologicalKrullDim_subschemeChart_planeCubicEmbedding (k : Type u) [Field k] (a : k)
    {j : Fin 3} (hj : j = 0 ∨ j = 1) :
    topologicalKrullDim
        ((subschemeChart (planeCubicEmbedding k a) j : Set (planeCubicCurve k a))) = 1 := by
  obtain ⟨hne, hnu⟩ := dehomCoeff_planeCubic_ne_zero_and_not_isUnit k a hj
  rw [AlgebraicGeometry.topologicalKrullDim_coe_eq_ringKrullDim_of_isAffineOpen _
      (isAffineOpen_subschemeChart (planeCubicEmbedding k a) j),
    ← ringKrullDim_eq_of_ringEquiv
      (chartQuotientEquiv (planeCubicEmbedding k a) j (planeCubic k a)
        (planeCubic_mem_homogeneousSubmodule_smul k a)
        (idealOfClosedSubscheme_planeCubicEmbedding k a)),
    Stacks.MvPolynomial.ringKrullDim_quotient_span_singleton k (Fin 2) (n := 1)
      (by simp) _ hne hnu]
  rfl

/-- **Every point of the curve lies on one of the two charts.** A point of the cubic satisfies its
equation, and then `T₀` or `T₁` is invertible there. -/
theorem exists_mem_subschemeChart_planeCubicEmbedding (k : Type u) [Field k] (a : k)
    (x : planeCubicCurve k a) :
    ∃ j : Fin 3, (j = 0 ∨ j = 1) ∧ x ∈ subschemeChart (planeCubicEmbedding k a) j := by
  rcases X_zero_notMem_or_X_one_notMem a ((planeCubicEmbedding k a).base x)
    (planeCubic_mem_asHomogeneousIdeal a (planeCubicEmbedding k a)
      (idealOfClosedSubscheme_planeCubicEmbedding k a) x) with h | h
  · exact ⟨0, Or.inl rfl, h⟩
  · exact ⟨1, Or.inr rfl, h⟩

/-! ### The curve is irreducible of dimension one -/

/-- The quotient `k[T₀, T₁, T₂] ⧸ (F)` by the ideal of the cubic is a domain. -/
instance isDomain_planeCubicQuotient (k : Type u) [Field k] (a : k) :
    IsDomain (MvPolynomial (Fin 3) k ⧸ (planeCubicIdeal k a).toIdeal) :=
  haveI := isPrime_planeCubicIdeal k a
  Ideal.Quotient.isDomain _

/-- **The curve of [Stacks, Tag 0CD1] is irreducible**: it is `Proj` of a graded domain, the
quotient by the prime ideal generated by the irreducible cubic, and it is nonempty. -/
instance irreducibleSpace_planeCubicCurve (k : Type u) [Field k] (a : k) :
    IrreducibleSpace (planeCubicCurve k a) :=
  haveI := nonempty_planeCubicCurve k a
  AlgebraicGeometry.irreducibleSpace_proj_of_isDomain _

/-- **The curve of [Stacks, Tag 0CD1] has dimension one.** The dimension of a space is the
supremum of its local dimensions ([Stacks, Tag 0B7I]); each point has a chart of dimension one
for a neighbourhood, which bounds the dimension above, and one chart is a subspace, which bounds
it below. -/
theorem topologicalKrullDim_planeCubicCurve (k : Type u) [Field k] (a : k) :
    topologicalKrullDim (planeCubicCurve k a) = 1 := by
  refine le_antisymm ?_ ?_
  · rw [TopologicalSpace.topologicalKrullDim_eq_iSup_localKrullDim]
    refine iSup_le fun x => ?_
    obtain ⟨j, hj, hx⟩ := exists_mem_subschemeChart_planeCubicEmbedding k a x
    refine le_trans ?_ (topologicalKrullDim_subschemeChart_planeCubicEmbedding k a hj).le
    exact iInf_le_of_le ((subschemeChart (planeCubicEmbedding k a) j : Set (planeCubicCurve k a)))
      (iInf_le_of_le (subschemeChart (planeCubicEmbedding k a) j).2 (iInf_le _ hx))
  · rw [← topologicalKrullDim_subschemeChart_planeCubicEmbedding k a (j := 0) (Or.inl rfl)]
    exact topologicalKrullDim_subspace_le (planeCubicCurve k a) _

/-- **The curve of [Stacks, Tag 0CD1] is equidimensional of dimension one.** The curve is
irreducible, so its only irreducible component is the whole space. -/
theorem forall_mem_irreducibleComponents_topologicalKrullDim_planeCubicCurve
    (k : Type u) [Field k] (a : k) :
    ∀ W ∈ irreducibleComponents (planeCubicCurve k a), topologicalKrullDim W = 1 := by
  intro W hW
  rw [irreducibleComponents_eq_singleton, Set.mem_singleton_iff] at hW
  subst hW
  rw [topologicalKrullDim_univ]
  exact topologicalKrullDim_planeCubicCurve k a

/-! ### The curve has no embedded points -/

/-- **The curve of [Stacks, Tag 0CD1] has no embedded points.** In dimension one that is
Cohen–Macaulayness, by [Stacks, Tag 0BYB] for a closed subscheme of `𝐏²_k`, and the curve is
Cohen–Macaulay because it is regular. -/
theorem hasNoEmbeddedPoints_planeCubicCurve (k : Type u) [Field k] [ExpChar k 3] (a : k)
    (ha : ∀ b : k, b ^ 3 ≠ a) :
    HasNoEmbeddedPoints (planeCubicCurve k a) :=
  (AlgebraicGeometry.ProjectiveSpectrum.Proj.projectivePlane_isCohenMacaulay_iff_hasNoEmbeddedPoints
      k (planeCubicEmbedding k a)
      (forall_mem_irreducibleComponents_topologicalKrullDim_planeCubicCurve k a)).mp
    (AlgebraicGeometry.isCohenMacaulay_of_isRegular (isRegular_planeCubicCurve k a ha))

/-! ### The example of Tag 0CD1, with nothing assumed about the curve -/

/-- **[Stacks, Tag 0CD1] at the constructed curve, with the abstract function field.** Let `k`
be a field of characteristic three in which `a` is not a cube — such a pair exists by
`exists_charThree_notCube`. Then for the plane cubic `Z = Proj (k[T₀, T₁, T₂] ⧸ (F))`,
`F = T₁²T₀ - T₂³ + aT₀³`:

* `Z` is a curve over `k` and is **nonsingular**;
* the coordinate projection `f : Z ⟶ 𝐏¹_k`, `(T₀ : T₁ : T₂) ↦ (T₀ : T₁)`, exists and is pinned
  down by its inverse images of the standard opens;
* the extension `k(x) ⊆ k(x)(y)`, `y³ = x² + a`, is purely inseparable of degree three;
* the genus of `Z` is `1` while the genus of `𝐏¹_k` is `0`, so the two differ.

Here the purely inseparable extension is `RatFunc k ⊆ curveFunctionField k a`. -/
theorem planeCubicCurve_isRegular_and_genus_ne (k : Type u) [Field k] [ExpChar k 3] (a : k)
    (ha : ∀ b : k, b ^ 3 ≠ a) :
    IsCurve k (planeCubicEmbedding k a ≫ projToSpecCoeff k 2) ∧
      IsRegular (planeCubicCurve k a) ∧
      (∃ f : planeCubicCurve k a ⟶
          AlgebraicGeometry.Proj (MvPolynomial.homogeneousSubmodule (Fin 2) k),
        ∀ (G : MvPolynomial (Fin 2) k) (d : ℕ),
          G ∈ MvPolynomial.homogeneousSubmodule (Fin 2) k d → 0 < d →
          f ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen
              (MvPolynomial.homogeneousSubmodule (Fin 2) k) G =
            planeCubicEmbedding k a ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen
              (MvPolynomial.homogeneousSubmodule (Fin 3) k) (coordProjHom k G)) ∧
      IsPurelyInseparable (RatFunc k) (curveFunctionField k a) ∧
      Module.finrank (RatFunc k) (curveFunctionField k a) = 3 ∧
      genus (planeCubicEmbedding k a ≫ projToSpecCoeff k 2) = 1 ∧
      genus (projToSpecCoeff k 1) = 0 ∧
      genus (planeCubicEmbedding k a ≫ projToSpecCoeff k 2) ≠ genus (projToSpecCoeff k 1) :=
  have := nonempty_planeCubicCurve k a
  isRegular_and_exists_coordProj_and_genus_ne a ha (planeCubicEmbedding k a)
    (hasNoEmbeddedPoints_planeCubicCurve k a ha)
    (forall_mem_irreducibleComponents_topologicalKrullDim_planeCubicCurve k a)
    (idealOfClosedSubscheme_planeCubicEmbedding k a)

end Stacks.Curves.InseparableGenus

end
