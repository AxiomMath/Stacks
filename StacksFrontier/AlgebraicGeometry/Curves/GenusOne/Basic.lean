module

public import Mathlib.LinearAlgebra.Trace
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.SmoothSupportClopen
public import StacksFrontier.AlgebraicGeometry.CurveLocalRing.EffectiveCartier
public import StacksFrontier.AlgebraicGeometry.DivisorSum.Basic
public import StacksFrontier.AlgebraicGeometry.Curves.GenusCurve.CohomologyComparison
public import StacksFrontier.AlgebraicGeometry.EulerCharAdditivity.Basic
public import StacksFrontier.AlgebraicGeometry.Picard.SmoothCurveLocalDimension
public import StacksFrontier.AlgebraicGeometry.ProperGeomConnected.Basic
public import StacksFrontier.AlgebraicGeometry.RelativeProjSeparated.Basic
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.Defs
public import StacksFrontier.AlgebraicGeometry.Variety.Smooth.Regular
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Proper smooth curves with `H⁰(X, 𝒪_X) = k` and a rational point

Let `k` be a field and `f : X ⟶ Spec k` proper and smooth of relative dimension one, with
`dim_k H⁰(X, 𝒪_X) = 1`. This is the shape of each fibre of an elliptic curve. This file collects
the elementary consequences used to analyse such a curve through a `k`-rational point `p`: the
global functions are the constants, `X` is connected and integral, it is a curve over `k`, the
image of `p` is a closed point, its local ring is a discrete valuation ring, and the reduced point
and all its multiples are effective Cartier divisors.

## Main results

* `AlgebraicGeometry.GenusOne.bijective_globalSectionsHom`: `k ⟶ Γ(X, 𝒪_X)` is bijective.
* `AlgebraicGeometry.GenusOne.connectedSpace` and `AlgebraicGeometry.GenusOne.isIntegral`.
* `AlgebraicGeometry.GenusOne.isCurve`: `X` is a curve over `k`.
* `AlgebraicGeometry.GenusOne.isClosed_point`: the image of a section is a closed point.
* `AlgebraicGeometry.GenusOne.isDiscreteValuationRing_stalk`: its local ring is a discrete
  valuation ring.
* `AlgebraicGeometry.GenusOne.isEffectiveCartierDivisor_pow`: every multiple of the point is an
  effective Cartier divisor.

## Implementation notes

The point of `Spec k` is `IsLocalRing.closedPoint k`, and the closed point of `X` is its image
under the section. Closedness comes from the section being a closed immersion, which holds for
any section of a separated morphism.
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.GenusOne

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

/-- The structure morphism on global sections, `k ⟶ Γ(X, 𝒪_X)`. -/
abbrev globalSectionsHom : k →+* Γ(X, ⊤) := ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop).hom

/-- **The global functions are the constants**: if `dim_k H⁰(X, 𝒪_X) = 1` then
`k ⟶ Γ(X, 𝒪_X)` is bijective. -/
theorem bijective_globalSectionsHom
    (h0 : Module.finrank k (structureSheafCohomology f 0) = 1) :
    Function.Bijective (globalSectionsHom f) := by
  let : Algebra k Γ(X, ⊤) := (globalSectionsHom f).toAlgebra
  have h : Module.finrank k Γ(X, ⊤) = 1 := by
    rw [← finrank_cohomologyOverField_zero_unit_eq_finrank_globalSections k f,
      ← (structureSheafCohomologyIsoCohomologyOverField k f 0).toLinearEquiv.finrank_eq, h0]
  exact Module.Free.bijective_algebraMap_of_finrank_eq_one h

/-- The ring of global functions is nontrivial. -/
theorem nontrivial_globalSections
    (h0 : Module.finrank k (structureSheafCohomology f 0) = 1) : Nontrivial Γ(X, ⊤) :=
  (bijective_globalSectionsHom f h0).1.nontrivial

/-- **`X` is connected**: its ring of global functions is the field `k`, which has no idempotents
besides `0` and `1`. -/
theorem connectedSpace [IsProper f]
    (h0 : Module.finrank k (structureSheafCohomology f 0) = 1) : ConnectedSpace X := by
  have := nontrivial_globalSections f h0
  refine Stacks.AlgebraicGeometry.ProperGeomConnected.connectedSpace_of_isProper_of_isIdempotentElem
    f fun e he => ?_
  obtain ⟨c, rfl⟩ := (bijective_globalSectionsHom f h0).2 e
  have hc : IsIdempotentElem c :=
    (bijective_globalSectionsHom f h0).1 (by rwa [map_mul])
  rcases IsIdempotentElem.iff_eq_zero_or_one.mp hc with rfl | rfl
  · exact Or.inl (map_zero _)
  · exact Or.inr (map_one _)

/-- **`X` is integral**: it is connected and smooth over a field. -/
theorem isIntegral [IsProper f] [SmoothOfRelativeDimension 1 f]
    (h0 : Module.finrank k (structureSheafCohomology f 0) = 1) : IsIntegral X := by
  have := connectedSpace f h0
  have : Smooth f := SmoothOfRelativeDimension.smooth 1 f
  exact Stacks.Chow.isIntegral_of_connectedSpace_of_smooth f

/-- **`X` is a curve over `k`**: an integral separated scheme of finite type over `k`, of
dimension one. -/
theorem isCurve [IsProper f] [SmoothOfRelativeDimension 1 f]
    (h0 : Module.finrank k (structureSheafCohomology f 0) = 1) : IsCurve k f := by
  have := isIntegral f h0
  refine { topologicalKrullDim_eq_one := ?_ }
  rw [TopologicalSpace.topologicalKrullDim_eq_iSup_localKrullDim]
  simp_rw [← TopologicalSpace.topologicalKrullDimAt_eq_localKrullDim,
    topologicalKrullDimAt_eq_one_of_smoothOfRelativeDimension_one f]
  exact ciSup_const

/-- The point of `X` that a section `p` of `f` picks out. -/
abbrev point (p : Spec (.of k) ⟶ X) : X := p (IsLocalRing.closedPoint k)

/-- **The image of a section is a closed point**: a section of a separated morphism is a closed
immersion, and `Spec k` has one point. -/
theorem isClosed_point [IsSeparated f] (p : Spec (.of k) ⟶ X) (hp : p ≫ f = 𝟙 _) :
    IsClosed ({point p} : Set X) := by
  have := Stacks.AlgebraicGeometry.RelativeProjSeparated.isClosedImmersion_of_section f p hp
  have h : Set.range p = ({point p} : Set X) :=
    (Set.subsingleton_range p).eq_singleton_of_mem ⟨_, rfl⟩
  rw [← h]
  exact p.isClosedEmbedding.isClosed_range

/-- **The local ring at the point is a discrete valuation ring**: the stalks of a scheme smooth
over a field are regular, and a regular local ring of a curve at a closed point is a discrete
valuation ring ([Stacks, Tag 0B8Y]). -/
@[sga "7 IX 3.2.1" "special case"]
theorem isDiscreteValuationRing_stalk [IsProper f] [SmoothOfRelativeDimension 1 f] [IsIntegral X]
    (h0 : Module.finrank k (structureSheafCohomology f 0) = 1) (p : Spec (.of k) ⟶ X)
    (hp : p ≫ f = 𝟙 _) : IsDiscreteValuationRing (X.presheaf.stalk (point p)) := by
  have := isCurve f h0
  have : Smooth f := SmoothOfRelativeDimension.smooth 1 f
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have hreg := (isRegular_of_smooth_over_field f).isRegularLocalRing_stalk (point p)
  exact ((isEffectiveCartierDivisor_closedPoint_tfae_of_isCurve k f
    (isClosed_point f p hp)).out 1 3).mp hreg

/-- **The point is an effective Cartier divisor.** -/
theorem isEffectiveCartierDivisor [IsProper f] [SmoothOfRelativeDimension 1 f]
    (h0 : Module.finrank k (structureSheafCohomology f 0) = 1) (p : Spec (.of k) ⟶ X)
    (hp : p ≫ f = 𝟙 _) :
    Stacks.Divisors.IsEffectiveCartierDivisor
      (Scheme.IdealSheafData.vanishingIdeal (⟨{point p}, isClosed_point f p hp⟩ : Closeds X)) :=
  have := isIntegral f h0
  have := isCurve f h0
  have := isDiscreteValuationRing_stalk f h0 p hp
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  isEffectiveCartierDivisor_vanishingIdeal_of_isDiscreteValuationRing _

/-- **Every multiple of the point is an effective Cartier divisor.** -/
theorem isEffectiveCartierDivisor_pow [IsProper f] [SmoothOfRelativeDimension 1 f]
    (h0 : Module.finrank k (structureSheafCohomology f 0) = 1) (p : Spec (.of k) ⟶ X)
    (hp : p ≫ f = 𝟙 _) (n : ℕ) :
    Stacks.Divisors.IsEffectiveCartierDivisor
      (Scheme.IdealSheafData.vanishingIdeal (⟨{point p}, isClosed_point f p hp⟩ : Closeds X) ^ n) :=
  Stacks.Divisors.isEffectiveCartierDivisor_pow (isEffectiveCartierDivisor f h0 p hp) n

end AlgebraicGeometry.GenusOne

end
