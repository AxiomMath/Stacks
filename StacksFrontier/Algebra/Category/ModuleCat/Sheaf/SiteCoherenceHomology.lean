module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SiteCoherenceFiniteFamilies
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SiteCoherenceCokernels
public import StacksFrontier.AlgebraicGeometry.Topologies.CoherentKernelOnSite
public import Mathlib.CategoryTheory.ObjectProperty.FiniteProducts

/-!
# Retracts and finite sums of coherent sheaves of modules on a site

Coherent sheaves of modules on a ringed site are closed under kernels and cokernels
(Stacks 01BY, parts (2) and (3), on a site) and under finite direct sums.  This file draws two
consequences used by the local analysis of a derived tensor product with a perfect factor:

* a retract of a coherent sheaf of modules is coherent, being the cokernel of an endomorphism of
  a coherent sheaf;
* coherence, as a property of objects, is closed under isomorphisms and finite coproducts;

## Main results

* `Stacks.SheafOfModules.isCoherentOnSite_of_comp_eq_id`
* `Stacks.SheafOfModules.isClosedUnderFiniteCoproducts_isCoherentOnSite`

## References

* [Stacks Project, Tag 01BY](https://stacks.math.columbia.edu/tag/01BY)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v w

namespace Stacks.SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{w}}
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify J AddCommGrpCat.{w}]

/-- **A retract of a coherent sheaf of modules is coherent.**  If `i ≫ r = 𝟙 M` with `N`
coherent, then `M` is the cokernel of the endomorphism `𝟙 N - r ≫ i` of `N`, the cokernel of a
morphism of coherent sheaves of modules being coherent. -/
theorem isCoherentOnSite_of_comp_eq_id {M N : _root_.SheafOfModules.{w} R} (i : M ⟶ N) (r : N ⟶ M)
    (hir : i ≫ r = 𝟙 M) (hN : _root_.SheafOfModules.IsCoherentOnSite N) :
    _root_.SheafOfModules.IsCoherentOnSite M := by
  let φ : N ⟶ N := 𝟙 N - r ≫ i
  have hφ : φ ≫ r = 0 := by simp [φ, hir]
  let e : cokernel φ ≅ M :=
    { hom := cokernel.desc φ r hφ
      inv := i ≫ cokernel.π φ
      hom_inv_id := by
        refine coequalizer.hom_ext ?_
        rw [cokernel.π_desc_assoc, Category.comp_id, ← Category.assoc,
          show r ≫ i = 𝟙 N - φ by simp [φ], Preadditive.sub_comp, cokernel.condition, sub_zero,
          Category.id_comp]
      inv_hom_id := by
        rw [Category.assoc, cokernel.π_desc, hir] }
  exact isCoherentOnSite_of_iso e (isCoherentOnSite_cokernel φ hN hN)

/-- Coherence is a property of objects closed under isomorphisms. -/
instance isClosedUnderIsomorphisms_isCoherentOnSite :
    ObjectProperty.IsClosedUnderIsomorphisms
      (fun M : _root_.SheafOfModules.{w} R => _root_.SheafOfModules.IsCoherentOnSite M) where
  of_iso e h := isCoherentOnSite_of_iso e h

variable [HasWeakSheafify J AddCommGrpCat.{w}]

/-- **Coherence is closed under finite coproducts.** -/
instance isClosedUnderFiniteCoproducts_isCoherentOnSite :
    ObjectProperty.IsClosedUnderFiniteCoproducts
      (fun M : _root_.SheafOfModules.{w} R => _root_.SheafOfModules.IsCoherentOnSite M) where
  isClosedUnderColimitsOfShape I _ := by
    refine ⟨fun X ⟨h⟩ => ?_⟩
    let f : I → _root_.SheafOfModules.{w} R := fun j => h.diag.obj ⟨j⟩
    let e : X ≅ ∐ f :=
      h.isColimit.coconePointUniqueUpToIso (colimit.isColimit h.diag) ≪≫
        HasColimit.isoOfNatIso (Discrete.natIsoFunctor (F := h.diag))
    exact isCoherentOnSite_of_iso e.symm (isCoherentOnSite_sigma f fun j => h.prop_diag_obj ⟨j⟩)

end Stacks.SheafOfModules

end
