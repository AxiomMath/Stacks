module

public import StacksFrontier.AlgebraicGeometry.ComponentDegrees.Basic
public import StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardClosedSubscheme
public import StacksFrontier.AlgebraicGeometry.Chow.FieldSituation.Base
public import StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardPrincipal.CurveDeltaDimension
public import StacksFrontier.AlgebraicGeometry.CoherentPushforwardCriteria.ClosureSubscheme

/-!
# The Chow 1-cycle of a scheme, presented by its one-dimensional components

Stacks Tag 02QU attaches to a closed immersion `i : Z ⟶ X` and an integer `k` a `k`-cycle
`cycleAssociatedToClosedSubscheme`, whose coefficient at the image of a generic point of `Z` is
the multiplicity `Stacks.Chow.componentMultiplicity i ξ` there, and which vanishes elsewhere. The
one-dimensional irreducible components of a scheme `X` are indexed by `genericPointsOne X`, each
with a multiplicity `Stacks.AlgebraicGeometry.ComponentDegrees.componentMultiplicity` computed at
the identity immersion. This file identifies the two, over the Chow situation whose base is the
spectrum of a field: a generic point of `X` lies in `genericPointsOne X` iff its relative dimension
is `1`, and the coefficients of the Chow 1-cycle of `X` are the multiplicities of its
one-dimensional components.

## Main results

* `Stacks.AlgebraicGeometry.ComponentDegrees.mem_genericPointsOne_iff_relativeDimension_eq_one`:
  a generic point of `X` is the generic point of a one-dimensional component iff its relative
  dimension (over `Stacks.Chow.fieldChowSituation k`) is `1`.
* `Stacks.AlgebraicGeometry.ComponentDegrees.cycleAssociatedToClosedSubscheme_id_apply`:
  the coefficient of the Chow 1-cycle of `X` (associated to the
  identity immersion) at a point `x` is the `ComponentDegrees` multiplicity of `x` when `x` is the
  generic point of a one-dimensional component, and zero otherwise.

## References

* [Stacks Project, Tag 02QU](https://stacks.math.columbia.edu/tag/02QU)
* [Stacks Project, Tag 02QO](https://stacks.math.columbia.edu/tag/02QO)
* [Stacks Project, Tag 0AYW](https://stacks.math.columbia.edu/tag/0AYW)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Stacks.Chow

universe u

namespace Stacks.AlgebraicGeometry.ComponentDegrees

variable (k : Type u) [Field k] {X : Scheme.{u}}

/-- The topological Krull dimension of the reduced closed subscheme on the closure of a point
agrees with the topological Krull dimension of that closure as a subspace of `X`. -/
theorem topologicalKrullDim_subscheme_vanishingIdeal_closure (x : X) :
    topologicalKrullDim
        (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({x} : Set X))).subscheme =
      topologicalKrullDim (closure ({x} : Set X)) := by
  set I : X.IdealSheafData :=
    Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({x} : Set X))
  have hrange : Set.range I.subschemeι.base = closure ({x} : Set X) := by
    rw [Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.coe_support_vanishingIdeal]
    rfl
  exact (IsHomeomorph.topologicalKrullDim_eq _
    (IsPreimmersion.isEmbedding I.subschemeι).toHomeomorph.isHomeomorph).trans
    (IsHomeomorph.topologicalKrullDim_eq _ (Homeomorph.setCongr hrange).isHomeomorph)

/-- A generic point of `X` is the generic point of a one-dimensional component iff its relative
dimension over `Stacks.Chow.fieldChowSituation k` is `1`. -/
theorem mem_genericPointsOne_iff_relativeDimension_eq_one {X : Scheme.{u}}
    (p : X ⟶ (fieldChowSituation k).S) [LocallyOfFiniteType p] {x : X}
    (hx : x ∈ genericPoints X) :
    x ∈ genericPointsOne X ↔
      relativeDimension (fieldChowSituation k).dimensionFunction p x = 1 := by
  have hZint : IsIntegral
      (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({x} : Set X))).subscheme :=
    Scheme.IdealSheafData.isIntegral_subscheme_vanishingIdeal_closure x
  have htop := Stacks.Chow.topologicalKrullDim_eq_relativeDimension_toNat (fieldChowSituation k)
    (fun _ _ ↦ rfl) p
    (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({x} : Set X))).subschemeι
    (genericPoint
      (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({x} : Set X))).subscheme)
    (genericPoint_spec _)
  rw [Scheme.IdealSheafData.subschemeι_genericPoint_vanishingIdeal_closure x,
    topologicalKrullDim_subscheme_vanishingIdeal_closure] at htop
  have hnonneg := Stacks.Chow.relativeDimension_nonneg (fieldChowSituation k) (fun _ _ ↦ rfl) p x
  rw [mem_genericPointsOne_iff]
  refine ⟨fun h => ?_, fun h => ⟨hx, ?_⟩⟩
  · have h2 := h.2
    rw [htop] at h2
    have h2' : (relativeDimension (fieldChowSituation k).dimensionFunction p x).toNat = 1 := by
      exact_mod_cast h2
    omega
  · rw [htop, h]
    rfl

/-- At the generic point of a one-dimensional component, the multiplicity
`Stacks.Chow.componentMultiplicity` of the identity immersion is the `ComponentDegrees`
multiplicity. -/
theorem componentMultiplicity_id_eq {X : Scheme.{u}} (ξ : genericPointsOne X) :
    Stacks.Chow.componentMultiplicity (𝟙 X) ⟨ξ.1, (mem_genericPointsOne_iff.mp ξ.2).1⟩ =
      (componentMultiplicity X ξ : ℤ) :=
  Stacks.Chow.componentMultiplicity_eq_length_stalk (𝟙 X)
    ⟨ξ.1, (mem_genericPointsOne_iff.mp ξ.2).1⟩

open Classical in
/-- The presentation of `[X]_1` by its one-dimensional components, with multiplicities: the
Chow `1`-cycle of `X` over `Stacks.Chow.fieldChowSituation k`, associated to the identity
closed immersion, has at every point `x` of `X` the `ComponentDegrees` multiplicity of `x` when
`x` is the generic point of a one-dimensional irreducible component, and coefficient zero
otherwise. -/
theorem cycleAssociatedToClosedSubscheme_id_apply {X : Scheme.{u}}
    (p : X ⟶ (fieldChowSituation k).S) [LocallyOfFiniteType p] (x : X) :
    (Stacks.Chow.cycleAssociatedToClosedSubscheme (fieldChowSituation k) p (𝟙 X) 1).1 x =
      if hx : x ∈ genericPointsOne X then (componentMultiplicity X ⟨x, hx⟩ : ℤ) else 0 := by
  split_ifs with hx
  · have hξ : x ∈ genericPoints X := (mem_genericPointsOne_iff.mp hx).1
    have hdim : relativeDimension (fieldChowSituation k).dimensionFunction p x = 1 :=
      (mem_genericPointsOne_iff_relativeDimension_eq_one k p hξ).mp hx
    exact (Stacks.Chow.cycleAssociatedToClosedSubscheme_apply (fieldChowSituation k) p
      (𝟙 X) 1 ⟨x, hξ⟩ hdim).trans (componentMultiplicity_id_eq ⟨x, hx⟩)
  · apply Stacks.Chow.cycleAssociatedToClosedSubscheme_apply_eq_zero (fieldChowSituation k) p
      (𝟙 X) 1 x
    rintro ⟨ξ, hξx, hξdim⟩
    obtain rfl : ξ.1 = x := hξx
    exact hx ((mem_genericPointsOne_iff_relativeDimension_eq_one k p ξ.2).mpr hξdim)

end Stacks.AlgebraicGeometry.ComponentDegrees

end
