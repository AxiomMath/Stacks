module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.UniverseLift

/-!
# Coherence under restriction of scalars along an isomorphism of sheaves of rings

Two sheaves of rings on one site which are isomorphic, but not equal, carry categories of
modules which are not the same category, and a local condition proved for a module over one of
them says nothing *a priori* about the corresponding module over the other.
`StacksFrontier.AlgebraicGeometry.Topologies.QuasicoherentRestrictScalars` closes that gap for the
clauses 03DE (6) and 03DL (1), (2), (3) and (6); this file closes it for the remaining clause
03DL (8), coherence.

Coherence is not a colimit condition, so it does not travel by the route the other clauses take.
It is two sectionwise finite-type conditions, and restriction of scalars along an isomorphism
changes neither the sections of the module nor the sections of the presheaf of relations among a
finite family of them: only the ring acting on them changes, and it changes by a ring
isomorphism at every object.  Both conditions therefore travel by the sectionwise transport of
finite type, `Stacks.SheafOfModules.isFiniteType_of_sectionwiseEquiv` and
`Stacks.SheafOfModules.CoherentLift.relations_isFiniteType_of_sectionwiseEquiv`.

## Main definitions

* `Stacks.SheafOfModules.sectionsRingEquiv`: the sections of two isomorphic sheaves of rings at
  an object of the site, as a ring isomorphism.

## Main results

* `Stacks.SheafOfModules.isCoherentOnSite_restrictScalars_of_isIso`: **coherence is carried by
  restriction of scalars along an isomorphism of sheaves of rings**, which is the clause
  03DL (8).

## Implementation notes

A morphism of sheaves of rings is not itself a natural transformation of the underlying
presheaves — `CategoryTheory.Sheaf` is a full subcategory, so the component at an object is
reached through `CategoryTheory.sheafToPresheaf` — and `Stacks.SheafOfModules.sectionsRingEquiv`
records the resulting ring isomorphism once rather than at each use.  Its *inverse* is what the
two transports consume, since the module whose coherence is concluded is the one over the
smaller-looking ring `R'`; the semilinearity hypothesis is then the cancellation
`e ∘ e⁻¹ = id` read on sections, and the naturality hypothesis is the naturality of the inverse.

No `stacks` attribute appears here.  What is proved is the invariance of one of the eight clauses
of Stacks 03DL under a change of presentation of the sheaf of rings, which is a fragment of the
assertion of Stacks 03DM rather than that assertion; the file exists to be used by the clause
itself.

## References

* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
* [Stacks Project, Tag 03DM](https://stacks.math.columbia.edu/tag/03DM)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v r m

namespace Stacks.SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R R' : Sheaf J RingCat.{r}}

/-- **The sections of two isomorphic sheaves of rings at an object, as a ring isomorphism.**
A morphism of sheaves of rings has no components of its own, `CategoryTheory.Sheaf` being a full
subcategory of presheaves; the components are those of its image under
`CategoryTheory.sheafToPresheaf`. -/
noncomputable def sectionsRingEquiv (e : R' ⟶ R) [IsIso e] (V : Cᵒᵖ) :
    R'.obj.obj V ≃+* R.obj.obj V :=
  (((sheafToPresheaf J RingCat.{r}).mapIso (asIso e)).app V).ringCatIsoToRingEquiv

/-- The ring isomorphism of sections is the component of the morphism of sheaves of rings. -/
theorem sectionsRingEquiv_apply (e : R' ⟶ R) [IsIso e] (V : Cᵒᵖ) (a : R'.obj.obj V) :
    sectionsRingEquiv e V a = ((sheafToPresheaf J RingCat.{r}).map e).app V a := rfl

/-- The ring isomorphisms of sections commute with restriction along an arrow of the site. -/
theorem sectionsRingEquiv_naturality (e : R' ⟶ R) [IsIso e] {V W : Cᵒᵖ} (f : V ⟶ W)
    (a : R'.obj.obj V) :
    sectionsRingEquiv e W (R'.obj.map f a) = R.obj.map f (sectionsRingEquiv e V a) := by
  simp [sectionsRingEquiv_apply]

/-- The inverse ring isomorphisms of sections commute with restriction along an arrow of the
site. -/
theorem sectionsRingEquiv_symm_naturality (e : R' ⟶ R) [IsIso e] {V W : Cᵒᵖ} (f : V ⟶ W)
    (a : R.obj.obj V) :
    (sectionsRingEquiv e W).symm (R.obj.map f a) =
      R'.obj.map f ((sectionsRingEquiv e V).symm a) :=
  (sectionsRingEquiv e W).injective (by
    rw [RingEquiv.apply_symm_apply, sectionsRingEquiv_naturality, RingEquiv.apply_symm_apply])

/-- **Restriction of scalars along an isomorphism of sheaves of rings leaves the sections and
their scalar multiplication alone**, once the scalar is read through the inverse isomorphism. -/
theorem restrictScalars_symm_smul (e : R' ⟶ R) [IsIso e] (M : SheafOfModules.{m} R) (V : Cᵒᵖ)
    (a : R.obj.obj V) (x : M.val.obj V) :
    ((sectionsRingEquiv e V).symm a •
        (show ((SheafOfModules.restrictScalars.{m} e).obj M).val.obj V from x) :
        ((SheafOfModules.restrictScalars.{m} e).obj M).val.obj V) =
      (show M.val.obj V from a • x) := by
  change (show M.val.obj V from
    sectionsRingEquiv e V ((sectionsRingEquiv e V).symm a) • x) = _
  rw [RingEquiv.apply_symm_apply]

/-- **Coherence is carried by restriction of scalars along an isomorphism of sheaves of
rings.**  This is the invariance of Stacks 03DL (8) under a change of presentation of the sheaf
of rings: the two categories of modules are not the same category, but a module and its
restriction of scalars have the same sections, and so do the presheaves of relations among a
finite family of them, so both of the two finite-type conditions coherence asks for travel
sectionwise. -/
theorem isCoherentOnSite_restrictScalars_of_isIso (e : R' ⟶ R) [IsIso e]
    (M : SheafOfModules.{m} R) (hM : M.IsCoherentOnSite) :
    ((SheafOfModules.restrictScalars.{m} e).obj M).IsCoherentOnSite where
  isFiniteType :=
    isFiniteType_of_sectionwiseEquiv (fun V ↦ (sectionsRingEquiv e V).symm)
      (fun _ ↦ AddEquiv.refl _) (fun V a x ↦ (restrictScalars_symm_smul e M V a x).symm)
      (fun _ _ ↦ rfl) hM.isFiniteType
  kernel_isFiniteType U n s :=
    CoherentLift.relations_isFiniteType_of_sectionwiseEquiv
      (fun V ↦ (sectionsRingEquiv e V).symm) (fun f a ↦ sectionsRingEquiv_symm_naturality e f a)
      (fun _ ↦ AddEquiv.refl _) (fun V a x ↦ (restrictScalars_symm_smul e M V a x).symm)
      (fun _ _ ↦ rfl) s (hM.kernel_isFiniteType U n _)

end Stacks.SheafOfModules

end
