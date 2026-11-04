module

public import StacksFrontier.Topology.Dimension.KrullSeparation
public import StacksFrontier.Topology.Dimension.SpecializingSurjection
import all
  StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.EmbeddedResolution.CurveFamilyResolution
public import
  StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.EmbeddedResolution.CurveFamilyResolution
public import
  StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.EmbeddedResolution.ExceptionalFibreGlobal
public import
  StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.EmbeddedResolution.StrictTransformSupport

/-!
# The dimension of a strict transform, backwards

The strict transform of a closed subscheme under a blowup at a closed point has the same
dimension as the subscheme, and `AlgebraicGeometry.transformIdeal_integral_curve` records the
direction that is needed to push a one-dimensional integral subscheme forward along a chain. This
file adds the other direction: a strict transform of dimension one comes from a subscheme of
dimension one.

## Main results

* `Stacks.ResolutionOfSurfaces.topologicalKrullDim_eq_one_of_transformIdeal` — a strict transform
  of dimension one comes from a subscheme of dimension one.

## Implementation notes

Away from the centre the strict transform is isomorphic to the subscheme
(`AlgebraicGeometry.nonempty_transformIdeal_subscheme_iso_self`), so the dimension transfers along
an isomorphism. At a point of the subscheme the strict transform is the blowup of the subscheme
there, by [Stacks, Tag 080E]
(`AlgebraicGeometry.nonempty_transformIdeal_subscheme_iso_blowUp`), and the two bounds are
separate:

* the blowup morphism is proper, hence closed, and surjective because the centre is a closed point
  whose closure is not the whole subscheme, so it cannot raise the dimension —
  [Stacks, Tag 02JF], as
  `Topology.topologicalKrullDim_le_of_surjective_of_specializingMap_or_generalizingMap`;
* the subscheme has dimension at least one because that same closed point is not its generic
  point, which is a strict chain of irreducible closed subsets.

That the centre's closure is not the whole subscheme is itself read off the hypothesis: were the
closure everything, the centre would be the vanishing ideal of the whole space, which on a reduced
scheme is the zero ideal sheaf, and the blowup in the zero ideal sheaf is empty
(`AlgebraicGeometry.isEmpty_blowUp_bot`) — whereas it has dimension one and so is nonempty.

## References

* [Stacks Project, Tag 0BI4](https://stacks.math.columbia.edu/tag/0BI4)
* [Stacks Project, Tag 080E](https://stacks.math.columbia.edu/tag/080E)
* [Stacks Project, Tag 02JF](https://stacks.math.columbia.edu/tag/02JF)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open Stacks.Divisors

universe u

namespace Stacks.ResolutionOfSurfaces

/-- **A strict transform of dimension one comes from a subscheme of dimension one.** This is the
converse of the dimension half of `AlgebraicGeometry.transformIdeal_integral_curve`.

Away from the centre the strict transform is isomorphic to the subscheme. At a point of the
subscheme it is the blowup of the subscheme there ([Stacks, Tag 080E]), which is proper and
surjective, so it cannot raise the dimension ([Stacks, Tag 02JF]); and the subscheme has
dimension at least one because the centre is a closed point whose closure is not everything —
were it everything, the centre would be the zero ideal sheaf and the blowup empty. -/
public theorem topologicalKrullDim_eq_one_of_transformIdeal {X : Scheme.{u}} [IsNoetherian X]
    (I : X.IdealSheafData) [IsIntegral I.subscheme] (p : X) (hp : IsClosed ({p} : Set X))
    (h : topologicalKrullDim (transformIdeal I p hp).subscheme = 1) :
    topologicalKrullDim I.subscheme = 1 := by
  have : IsNoetherian I.subscheme := isNoetherian_subscheme I
  have : IsLocallyNoetherian I.subscheme := IsNoetherian.toIsLocallyNoetherian
  have : IrreducibleSpace I.subscheme := irreducibleSpace_of_isIntegral I.subscheme
  by_cases hIp : p ∈ I.support
  · obtain ⟨y, rfl⟩ : ∃ y : I.subscheme, I.subschemeι y = p := ⟨⟨p, hIp⟩, rfl⟩
    have hy : IsClosed ({y} : Set I.subscheme) := isClosed_singleton_of_subschemeι_eq I hp y rfl
    obtain ⟨d⟩ := nonempty_transformIdeal_subscheme_iso_blowUp I y hy hp
    have hBl : topologicalKrullDim (blowUp (centerIdeal y hy)) = 1 :=
      (topologicalKrullDim_eq_of_iso d).symm.trans h
    have hNE : Nonempty (blowUp (centerIdeal y hy)) := by
      by_contra hcon
      rw [not_nonempty_iff] at hcon
      have hemp : IsEmpty (IrreducibleCloseds (blowUp (centerIdeal y hy))) :=
        ⟨fun Z => Z.isIrreducible'.nonempty.elim fun z _ => hcon.false z⟩
      rw [topologicalKrullDim, Order.krullDim_eq_bot_iff.mpr hemp] at hBl
      exact absurd hBl (by simp)
    have hyne : ({y} : Set I.subscheme) ≠ Set.univ := by
      intro hu
      have htop : (⟨{y}, hy⟩ : Closeds I.subscheme) = ⊤ := by
        apply SetLike.coe_injective
        simpa using hu
      have hbot : centerIdeal y hy = ⊥ := by
        rw [centerIdeal, htop, Scheme.IdealSheafData.vanishingIdeal_top, Scheme.nilradical_eq_bot]
      rw [hbot] at hNE
      exact (isEmpty_blowUp_bot _).false hNE.some
    have hgne : genericPoint I.subscheme ≠ y := by
      intro he
      refine hyne ?_
      rw [← hy.closure_eq, ← he, genericPoint_closure]
    have h1 : (1 : WithBot ℕ∞) ≤ topologicalKrullDim I.subscheme :=
      one_le_topologicalKrullDim_of_specializes_of_ne (genericPoint_specializes y) hgne
    have hsurj : Function.Surjective (blowUpToBase (centerIdeal y hy)).base :=
      surjective_blowUpToBase_of_support_ne_univ _ (by
        rw [centerIdeal, Scheme.IdealSheafData.coe_support_vanishingIdeal]
        exact hyne)
    have hle := Topology.topologicalKrullDim_le_of_surjective_of_specializingMap_or_generalizingMap
      (blowUpToBase (centerIdeal y hy)).base (blowUpToBase (centerIdeal y hy)).continuous hsurj
      (Or.inl (blowUpToBase (centerIdeal y hy)).isClosedMap.specializingMap)
    rw [hBl] at hle
    exact le_antisymm hle h1
  · obtain ⟨e⟩ := nonempty_transformIdeal_subscheme_iso_self I p hp
      (transformToCurve_isIso_of_notMem_support I p hp hIp)
    exact (topologicalKrullDim_eq_of_iso e).symm.trans h

end Stacks.ResolutionOfSurfaces

end
