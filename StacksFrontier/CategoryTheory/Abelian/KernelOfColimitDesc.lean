module

public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
public import Mathlib.CategoryTheory.Filtered.Connected
public import Mathlib.CategoryTheory.Limits.Connected
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
public import Mathlib.CategoryTheory.Limits.Shapes.ConcreteCategory
public import Mathlib.CategoryTheory.Abelian.Basic

/-!
# The kernel of the map out of a filtered colimit

In an abelian category in which colimits of shape `J` are exact (Grothendieck's axiom AB5 for a
filtered `J`), the kernel of the map `colim Dⱼ ⟶ X` induced by a cocone `αⱼ : Dⱼ ⟶ X` is the
colimit of the kernels of the `αⱼ`.

## Main definitions

* `CategoryTheory.Limits.kernelDescIsoColimitKernel`
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Limits

/-- **The kernel of the map out of a filtered colimit is the colimit of the kernels.** -/
def kernelDescIsoColimitKernel {C : Type*} [Category C] [Abelian C]
    {J : Type*} [Category J] [IsFiltered J] [HasColimitsOfShape J C] [HasExactColimitsOfShape J C]
    {D : J ⥤ C} {c : Cocone D} (hc : IsColimit c) {X : C} (α : D ⟶ (Functor.const J).obj X) :
    kernel (hc.desc (Cocone.mk X α)) ≅ colimit (kernel α) := by
  have : IsConnected J := IsFiltered.isConnected J
  let e : colimit ((Functor.const J).obj X) ≅ X :=
    (colimit.isColimit ((Functor.const J).obj X)).coconePointUniqueUpToIso
      (isColimitConstCocone J X)
  have he : ∀ j, colimit.ι ((Functor.const J).obj X) j ≫ e.hom = 𝟙 X := fun j =>
    IsColimit.comp_coconePointUniqueUpToIso_hom _ (isColimitConstCocone J X) j
  let i : c.pt ≅ colimit D := hc.coconePointUniqueUpToIso (colimit.isColimit D)
  have hi : ∀ j, c.ι.app j ≫ i.hom = colimit.ι D j := fun j =>
    IsColimit.comp_coconePointUniqueUpToIso_hom hc (colimit.isColimit D) j
  have hfac : hc.desc (Cocone.mk X α) = i.hom ≫ colim.map α ≫ e.hom := by
    refine hc.hom_ext fun j => ?_
    rw [hc.fac, reassoc_of% (hi j), colim_map, ι_colimMap_assoc, he]
    exact (Category.comp_id _).symm
  rw [hfac]
  exact kernelIsIsoComp _ _ ≪≫ kernelCompMono _ _ ≪≫ (PreservesKernel.iso colim α).symm

/-- **A colimit of zero objects is zero.** -/
theorem isZero_colimit_of_forall_isZero {C : Type*} [Category C] [HasZeroMorphisms C]
    {J : Type*} [Category J] {K : J ⥤ C} [HasColimit K] (h : ∀ j, IsZero (K.obj j)) :
    IsZero (colimit K) :=
  (IsZero.iff_id_eq_zero _).2 (colimit.hom_ext fun j => (h j).eq_of_src _ _)

end CategoryTheory.Limits

end
