module

public import StacksFrontier.AlgebraicGeometry.ModulePullbackPseudofunctor.Basic
public import StacksFrontier.Topology.Sheaves.Functors.Module.PullbackComp
public import StacksFrontier.AlgebraicGeometry.Schemes.ClosedImmersions.IsomorphismOfClosedSubspaces

/-!
# A closed immersion is determined by its ideal sheaf

A morphism of locally ringed spaces factors through a closed immersion exactly when the ideal
sheaf of that closed immersion dies in its structure sheaf, and the factorization is then
unique. Consequently two closed immersions with the same target and the same ideal sheaf are
uniquely isomorphic over the target.

This is the form of Tags 01HO and 01HP that applies to an arbitrary closed immersion rather
than to the closed subspace `Stacks.ClosedImmersion.closedSubspace` constructed from an ideal
sheaf.

## Main results

* `Stacks.ClosedImmersion.existsUnique_factorization`: the factorization criterion for a closed
  immersion.
* `Stacks.ClosedImmersion.existsUnique_iso_of_idealSheaf_iso`: two closed immersions with
  isomorphic ideal sheaves are uniquely isomorphic over their common target.

## Implementation notes

Both statements are obtained from the closed subspace associated to the ideal sheaf. A closed
immersion is isomorphic over its target to that subspace
(`Stacks.ClosedImmersion.existsUnique_iso_closedSubspace`), and the subspace carries the
factorization criterion `Stacks.ClosedImmersion.factorsThrough_closedSubspace_iff`; transporting
the factorization along the isomorphism gives the criterion for the closed immersion itself.
Uniqueness is not separate work: a closed immersion of locally ringed spaces is a
monomorphism.

For the second statement the two factorizations obtained from the hypothesis are mutually
inverse, again because the two closed immersions are monomorphisms.

## References

* [Stacks Project, Tag 01HO](https://stacks.math.columbia.edu/tag/01HO)
* [Stacks Project, Tag 01HP](https://stacks.math.columbia.edu/tag/01HP)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open RingedSpaceModuleAdjunction

universe u

namespace Stacks.ClosedImmersion

variable {X A B : LocallyRingedSpace.{u}}

/-- **The factorization criterion for a closed immersion.** A morphism `f : A ⟶ X` factors
through a closed immersion `g : B ⟶ X`, uniquely, as soon as the ideal sheaf of `g` dies in the
structure sheaf of `A`. -/
theorem existsUnique_factorization (g : B ⟶ X) [hg : IsClosedImmersion g.toShHom] (f : A ⟶ X)
    (h : kernel.ι (SheafOfModules.unitToPushforwardObjUnit (structureSheafHom g.toShHom)) ≫
        SheafOfModules.unitToPushforwardObjUnit (structureSheafHom f.toShHom) = 0) :
    ∃! t : A ⟶ B, t ≫ g = f := by
  obtain ⟨e, he, -⟩ := existsUnique_iso_closedSubspace g
  obtain ⟨a, ha⟩ := (factorsThrough_closedSubspace_iff
    (closedSubspace X (idealSheaf g.toShHom) (kernel.ι _) hg.kernel_locallyGenerated) f).2
    ((pullbackIdealMap_eq_zero_iff f _ _).2 h)
  have key : (a ≫ e.inv) ≫ g = f := by
    rw [Category.assoc, (Iso.inv_comp_eq e).2 he.symm]; exact ha
  exact ⟨a ≫ e.inv, key, fun t ht ↦ (cancel_mono g).1 (ht.trans key.symm)⟩

/-- **Two closed immersions with the same ideal sheaf agree.** If the ideal sheaves of two
closed immersions `f : A ⟶ X` and `g : B ⟶ X` are isomorphic compatibly with their inclusions
into `𝒪_X`, then `A` and `B` are uniquely isomorphic over `X`. -/
theorem existsUnique_iso_of_idealSheaf_iso (f : A ⟶ X) (g : B ⟶ X)
    [IsClosedImmersion f.toShHom] [IsClosedImmersion g.toShHom]
    (e : idealSheaf f.toShHom ≅ idealSheaf g.toShHom)
    (he : e.hom ≫ kernel.ι (SheafOfModules.unitToPushforwardObjUnit
        (structureSheafHom g.toShHom)) =
      kernel.ι (SheafOfModules.unitToPushforwardObjUnit (structureSheafHom f.toShHom))) :
    ∃! t : A ≅ B, t.hom ≫ g = f := by
  obtain ⟨u, hu, hu'⟩ := existsUnique_factorization g f (by
    rw [(Iso.eq_inv_comp e).2 he, Category.assoc, kernel.condition, comp_zero])
  obtain ⟨v, hv, -⟩ := existsUnique_factorization f g (by
    rw [← he, Category.assoc, kernel.condition, comp_zero])
  refine ⟨⟨u, v, (cancel_mono f).1 (by rw [Category.assoc, hv, hu, Category.id_comp]),
    (cancel_mono g).1 (by rw [Category.assoc, hu, hv, Category.id_comp])⟩, hu,
    fun t ht ↦ Iso.ext (hu' _ ht)⟩

/-! ### Transport of the ideal sheaf along an isomorphism of the source -/

section Transport

/-- An isomorphism of locally ringed spaces is an isomorphism of the underlying ringed
spaces. -/
instance isIso_toShHom_of_isIso {P Q : LocallyRingedSpace.{u}} (f : P ⟶ Q) [IsIso f] :
    IsIso f.toShHom :=
  ⟨(inv f).toShHom, by rw [← LocallyRingedSpace.comp_toShHom, IsIso.hom_inv_id]; rfl,
    by rw [← LocallyRingedSpace.comp_toShHom, IsIso.inv_hom_id]; rfl⟩

/-- Pushforward of sheaves of modules along the structure-sheaf map of a composite. -/
def structureSheafPushforwardComp {A' B' C' : RingedSpace.{u, u}} (f : A' ⟶ B')
    (g : B' ⟶ C') :
    SheafOfModules.pushforward (structureSheafHom (f ≫ g)) ≅
      SheafOfModules.pushforward (structureSheafHom f) ⋙
        SheafOfModules.pushforward (structureSheafHom g) :=
  SheafOfModules.pushforwardCongr (RingedSpaceModuleAdjunction.structureSheafHom_comp f g) ≪≫
    (SheafOfModules.pushforwardComp (structureSheafHom g) (structureSheafHom f)).symm

/-- The map of structure sheaves of modules attached to a composite, factored through the two
maps attached to the factors. -/
theorem unitToPushforwardObjUnit_compose {A' B' C' : RingedSpace.{u, u}} (f : A' ⟶ B')
    (g : B' ⟶ C') :
    SheafOfModules.unitToPushforwardObjUnit (structureSheafHom (f ≫ g)) =
      SheafOfModules.unitToPushforwardObjUnit (structureSheafHom g) ≫
        (SheafOfModules.pushforward (structureSheafHom g)).map
          (SheafOfModules.unitToPushforwardObjUnit (structureSheafHom f)) ≫
        (structureSheafPushforwardComp f g).inv.app
          (SheafOfModules.unit (structureSheafRing A')) := by
  ext U
  rfl

/-- **The ideal sheaf of a morphism of ringed spaces depends only on that morphism.** -/
def idealSheafCongr {X' Z' : RingedSpace.{u, u}} {f g : Z' ⟶ X'} (h : f = g) :
    idealSheaf f ≅ idealSheaf g :=
  eqToIso (congrArg idealSheaf h)

/-- The identification `idealSheafCongr h` is compatible with the inclusions of the two ideal
sheaves into the structure sheaf. -/
theorem idealSheafCongr_hom_kernel_ι {X' Z' : RingedSpace.{u, u}} {f g : Z' ⟶ X'} (h : f = g) :
    (idealSheafCongr h).hom ≫
        kernel.ι (SheafOfModules.unitToPushforwardObjUnit (structureSheafHom g)) =
      kernel.ι (SheafOfModules.unitToPushforwardObjUnit (structureSheafHom f)) := by
  subst h
  rw [idealSheafCongr]
  simp

/-- **The ideal sheaf of a morphism of ringed spaces is unchanged by an isomorphism of its
source**, in the form where the composite is taken in ringed spaces. -/
def idealSheafShHomCompIso (e : A ≅ B) (j : B ⟶ X) :
    idealSheaf (e.hom.toShHom ≫ j.toShHom) ≅ idealSheaf j.toShHom := by
  have hη : IsIso (SheafOfModules.unitToPushforwardObjUnit
      (structureSheafHom e.hom.toShHom)) := inferInstance
  refine kernel.mapIso
    (f := SheafOfModules.unitToPushforwardObjUnit
      (structureSheafHom (e.hom.toShHom ≫ j.toShHom)))
    (f' := SheafOfModules.unitToPushforwardObjUnit (structureSheafHom j.toShHom))
    (p := Iso.refl _)
    (q := (structureSheafPushforwardComp e.hom.toShHom j.toShHom).app
        (SheafOfModules.unit (structureSheafRing A.toSheafedSpace)) ≪≫
      ((SheafOfModules.pushforward (structureSheafHom j.toShHom)).mapIso
        (@asIso _ _ _ _ _ hη)).symm) ?_
  rw [unitToPushforwardObjUnit_compose e.hom.toShHom j.toShHom]
  simp

/-- The isomorphism `idealSheafShHomCompIso e j` is compatible with the inclusions of the two
ideal sheaves into the structure sheaf. -/
theorem idealSheafShHomCompIso_hom_kernel_ι (e : A ≅ B) (j : B ⟶ X) :
    (idealSheafShHomCompIso e j).hom ≫
        kernel.ι (SheafOfModules.unitToPushforwardObjUnit (structureSheafHom j.toShHom)) =
      kernel.ι (SheafOfModules.unitToPushforwardObjUnit
        (structureSheafHom (e.hom.toShHom ≫ j.toShHom))) := by
  rw [idealSheafShHomCompIso]
  simp

/-- **The ideal sheaf of a morphism of locally ringed spaces is unchanged by an isomorphism of
its source.** -/
def idealSheafCompIso (e : A ≅ B) (j : B ⟶ X) :
    idealSheaf (e.hom ≫ j).toShHom ≅ idealSheaf j.toShHom :=
  idealSheafCongr (show (e.hom ≫ j).toShHom = e.hom.toShHom ≫ j.toShHom from by
    rw [LocallyRingedSpace.comp_toShHom]) ≪≫ idealSheafShHomCompIso e j

/-- The isomorphism `idealSheafCompIso e j` is compatible with the inclusions of the two ideal
sheaves into the structure sheaf. -/
theorem idealSheafCompIso_hom_kernel_ι (e : A ≅ B) (j : B ⟶ X) :
    (idealSheafCompIso e j).hom ≫
        kernel.ι (SheafOfModules.unitToPushforwardObjUnit (structureSheafHom j.toShHom)) =
      kernel.ι (SheafOfModules.unitToPushforwardObjUnit
        (structureSheafHom (e.hom ≫ j).toShHom)) :=
  (Category.assoc _ _ _).trans
    ((congrArg (fun z ↦ (idealSheafCongr _).hom ≫ z)
        (idealSheafShHomCompIso_hom_kernel_ι e j)).trans
      (idealSheafCongr_hom_kernel_ι _))

end Transport

end Stacks.ClosedImmersion

end
