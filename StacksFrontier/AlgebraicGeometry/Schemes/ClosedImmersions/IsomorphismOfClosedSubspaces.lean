module

public import StacksFrontier.AlgebraicGeometry.ClosedImmersion.ClosedSubspaceExistence
public import StacksFrontier.AlgebraicGeometry.Schemes.ClosedImmersions.FactorizationExistence
import StacksFrontier.Topology.Sheaves.Functors.Module.PullbackComp

/-!
# A closed immersion is the closed subspace cut out by its ideal sheaf

Let `f : X ⟶ Y` be a closed immersion of locally ringed spaces and let `Z` be the closed subspace
of `Y` associated to the ideal sheaf of `f`. Then `f` factors uniquely through the inclusion of
`Z`, and the factorization is an isomorphism: a closed immersion identifies its source with the
closed subspace cut out by its ideal sheaf.

## Main results

* `Stacks.ClosedImmersion.existsUnique_iso_closedSubspace`: there is a unique isomorphism from
  the source of a closed immersion to the associated closed subspace commuting with the maps to
  the ambient space.

## References

* [Stacks Project, Tag 01HO](https://stacks.math.columbia.edu/tag/01HO)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open RingedSpaceModuleAdjunction

universe u

namespace Stacks.ClosedImmersion

/-- An epimorphism in an abelian category exhibits its target as the cokernel of its kernel. -/
private noncomputable def cokernelKernelIso {C : Type*} [Category* C] [Abelian C] {A B : C}
    (q : A ⟶ B) [Epi q] : cokernel (kernel.ι q) ≅ B :=
  (cokernelIsCokernel (kernel.ι q)).coconePointUniqueUpToIso
    (Abelian.epiIsCokernelOfKernel (KernelFork.ofι (kernel.ι q) (kernel.condition q))
      (kernelIsKernel q))

/-- The identification of `cokernelKernelIso` is the one compatible with the quotient maps. -/
private theorem cokernelKernelIso_fac {C : Type*} [Category* C] [Abelian C] {A B : C}
    (q : A ⟶ B) [Epi q] :
    cokernel.π (kernel.ι q) ≫ (cokernelKernelIso q).hom = q :=
  (cokernelIsCokernel _).comp_coconePointUniqueUpToIso_hom _ WalkingParallelPair.one

/-- The structure-sheaf map of a composite of morphisms of ringed spaces is the structure-sheaf
map of the second followed by the pushforward of the structure-sheaf map of the first. -/
private alias structureSheafHom_comp := RingedSpaceModuleAdjunction.structureSheafHom_comp

/-- Pushing forward sheaves of modules along a composite `g ≫ i` of morphisms of locally ringed
spaces is pushing forward along `g` and then along `i`. -/
private noncomputable def pushforwardCompIso {X Y Z : LocallyRingedSpace.{u}} (g : X ⟶ Z)
    (i : Z ⟶ Y) :
    SheafOfModules.pushforward.{u} (structureSheafHom (g ≫ i).toShHom) ≅
      SheafOfModules.pushforward.{u} (structureSheafHom g.toShHom) ⋙
        SheafOfModules.pushforward.{u} (structureSheafHom i.toShHom) :=
  SheafOfModules.pushforwardCongr (structureSheafHom_comp g.toShHom i.toShHom) ≪≫
    (SheafOfModules.pushforwardComp (structureSheafHom i.toShHom)
      (structureSheafHom g.toShHom)).symm

/-- The structure-sheaf map of `g ≫ i`, read through `pushforwardCompIso`, is the structure-sheaf
map of `i` followed by `i_*` of the structure-sheaf map of `g`. -/
private theorem unitToPushforwardObjUnit_comp_pushforwardCompIso
    {X Y Z : LocallyRingedSpace.{u}} (g : X ⟶ Z) (i : Z ⟶ Y) :
    SheafOfModules.unitToPushforwardObjUnit (structureSheafHom (g ≫ i).toShHom) ≫
        (pushforwardCompIso g i).hom.app
          (SheafOfModules.unit (structureSheafRing X.toRingedSpace)) =
      SheafOfModules.unitToPushforwardObjUnit (structureSheafHom i.toShHom) ≫
        (SheafOfModules.pushforward.{u} (structureSheafHom i.toShHom)).map
          (SheafOfModules.unitToPushforwardObjUnit (structureSheafHom g.toShHom)) := by
  apply SheafOfModules.hom_ext
  ext U
  rfl

/-- Let `f = g ≫ i`, let the structure-sheaf map of `f` be an epimorphism, and let `eta` identify
`f_* 𝒪_X` with `i_* 𝒪_Z` compatibly with the two structure-sheaf maps. Then `i_*` of the
structure-sheaf map of `g` is an isomorphism. -/
private theorem isIso_pushforward_map_structureSheafMap {X Y Z : LocallyRingedSpace.{u}}
    (f : X ⟶ Y) (i : Z ⟶ Y) (g : X ⟶ Z) (hg : g ≫ i = f)
    [Epi (SheafOfModules.unitToPushforwardObjUnit (structureSheafHom f.toShHom))]
    (eta : (SheafOfModules.pushforward.{u} (structureSheafHom f.toShHom)).obj
             (SheafOfModules.unit (structureSheafRing X.toRingedSpace)) ≅
           (SheafOfModules.pushforward.{u} (structureSheafHom i.toShHom)).obj
             (SheafOfModules.unit (structureSheafRing Z.toRingedSpace)))
    (heta : SheafOfModules.unitToPushforwardObjUnit (structureSheafHom f.toShHom) ≫ eta.hom =
            SheafOfModules.unitToPushforwardObjUnit (structureSheafHom i.toShHom)) :
    IsIso ((SheafOfModules.pushforward.{u} (structureSheafHom i.toShHom)).map
      (SheafOfModules.unitToPushforwardObjUnit (structureSheafHom g.toShHom))) := by
  subst hg
  have hqi : Epi (SheafOfModules.unitToPushforwardObjUnit (structureSheafHom i.toShHom)) := by
    rw [← heta]; infer_instance
  have hr : (SheafOfModules.pushforward.{u} (structureSheafHom i.toShHom)).map
      (SheafOfModules.unitToPushforwardObjUnit (structureSheafHom g.toShHom)) =
      eta.inv ≫ (pushforwardCompIso g i).hom.app
        (SheafOfModules.unit (structureSheafRing X.toRingedSpace)) := by
    apply (cancel_epi (SheafOfModules.unitToPushforwardObjUnit
      (structureSheafHom i.toShHom))).1
    rw [← unitToPushforwardObjUnit_comp_pushforwardCompIso g i, ← heta, Category.assoc,
      Iso.hom_inv_id_assoc]
  rw [hr]
  infer_instance

/-- If `i` is inducing and `i_*` of the structure-sheaf map of `g` is an isomorphism, then the
structure-sheaf map of `g` is an isomorphism on sections over every open of `Z`. -/
private theorem isIso_val_app_of_isIso_pushforward_map {X Y Z : LocallyRingedSpace.{u}}
    (g : X ⟶ Z) (i : Z ⟶ Y) (hi : Topology.IsInducing i.base)
    (hr : IsIso ((SheafOfModules.pushforward.{u} (structureSheafHom i.toShHom)).map
      (SheafOfModules.unitToPushforwardObjUnit (structureSheafHom g.toShHom))))
    (U : Opens Z) :
    IsIso ((SheafOfModules.unitToPushforwardObjUnit
      (structureSheafHom g.toShHom)).val.app (op U)) := by
  set r := (SheafOfModules.pushforward.{u} (structureSheafHom i.toShHom)).map
    (SheafOfModules.unitToPushforwardObjUnit (structureSheafHom g.toShHom))
  have hV : IsIso (r.val.app (op (hi.functorObj U))) :=
    Functor.map_isIso (SheafOfModules.evaluation
      (structureSheafRing Y.toRingedSpace) (op (hi.functorObj U))) r
  have hVbij := (ConcreteCategory.isIso_iff_bijective _).mp hV
  refine (ConcreteCategory.isIso_iff_bijective _).mpr ?_
  rw [← hi.map_functorObj U]
  exact hVbij

/-- A morphism whose composite with a closed embedding is a closed embedding is itself a closed
embedding. -/
private theorem isClosedEmbedding_base_of_factorization {X Y Z : LocallyRingedSpace.{u}}
    (g : X ⟶ Z) (i : Z ⟶ Y) (hi : Topology.IsClosedEmbedding i.base)
    (hf : Topology.IsClosedEmbedding (g ≫ i).base) :
    Topology.IsClosedEmbedding g.base := by
  have hbase : ∀ x : X.toTopCat, i.base (g.base x) = (g ≫ i).base x := fun _ => rfl
  refine ⟨hi.isEmbedding.of_comp_iff.mp hf.isEmbedding, ?_⟩
  have hrange : Set.range g.base = i.base ⁻¹' Set.range (g ≫ i).base := by
    ext z
    exact ⟨fun ⟨x, hx⟩ ↦ ⟨x, hx ▸ hbase x⟩, fun ⟨x, hx⟩ ↦ ⟨x, hi.injective ((hbase x).trans hx)⟩⟩
  exact hrange ▸ hf.isClosed_range.preimage i.base.hom.continuous

/-- If the base map of `g` has closed range and the structure-sheaf map of `g` is an isomorphism
on sections over every open of `Z`, then the base map of `g` is surjective. -/
private theorem surjective_base_of_isIso_val_app {X Z : LocallyRingedSpace.{u}} (g : X ⟶ Z)
    (hclosed : IsClosed (Set.range g.base))
    (h : ∀ U : Opens Z, IsIso ((SheafOfModules.unitToPushforwardObjUnit
      (structureSheafHom g.toShHom)).val.app (op U))) :
    Function.Surjective g.base := by
  intro z
  by_contra hz
  let U : Opens Z.toTopCat := ⟨(Set.range g.base)ᶜ, hclosed.isOpen_compl⟩
  have hzU : z ∈ U := hz
  have hpre : (Opens.map g.base).obj U = ⊥ := eq_bot_iff.2 fun x hx ↦ hx (Set.mem_range_self x)
  have htarget : Subsingleton
      (((SheafOfModules.pushforward.{u} (structureSheafHom g.toShHom)).obj
        (SheafOfModules.unit (structureSheafRing X.toRingedSpace))).val.obj (op U)) := by
    show Subsingleton (X.presheaf.obj (op ((Opens.map g.base).obj U)))
    rw [hpre]
    exact CommRingCat.subsingleton_of_isTerminal (X.sheaf.isTerminalOfEqEmpty rfl)
  have hsource : Subsingleton
      ((SheafOfModules.unit (structureSheafRing Z.toRingedSpace)).val.obj (op U)) := by
    refine ⟨fun a b => ?_⟩
    have hab : (SheafOfModules.unitToPushforwardObjUnit
        (structureSheafHom g.toShHom)).val.app (op U) a =
      (SheafOfModules.unitToPushforwardObjUnit
        (structureSheafHom g.toShHom)).val.app (op U) b := htarget.elim _ _
    exact ((ConcreteCategory.isIso_iff_bijective _).mp (h U)).1 hab
  change Subsingleton (Z.presheaf.obj (op U)) at hsource
  have hstalk : (1 : Z.presheaf.stalk z) = 0 := by
    simpa only [map_one, map_zero] using
      congrArg (fun s ↦ Z.presheaf.germ U z hzU s) (hsource.elim 1 0)
  exact one_ne_zero hstalk

/-- A morphism of locally ringed spaces whose base map is a closed bijection and whose
structure-sheaf map is an isomorphism on sections over every open is an isomorphism. -/
private theorem isIso_of_isIso_val_app {X Z : LocallyRingedSpace.{u}} (g : X ⟶ Z)
    (hbij : Function.Bijective g.base) (hclosedMap : IsClosedMap g.base)
    (h : ∀ U : Opens Z, IsIso ((SheafOfModules.unitToPushforwardObjUnit
      (structureSheafHom g.toShHom)).val.app (op U))) :
    IsIso g := by
  have hgBaseIso : IsIso g.toShHom.hom.base :=
    TopCat.isIso_of_bijective_of_isClosedMap g.base hbij hclosedMap
  have hgc : IsIso g.toShHom.hom.c := by
    rw [NatTrans.isIso_iff_isIso_app]
    refine fun U ↦ (ConcreteCategory.isIso_iff_bijective _).2 ?_
    show Function.Bijective ((SheafOfModules.unitToPushforwardObjUnit
      (structureSheafHom g.toShHom)).val.app U)
    exact (ConcreteCategory.isIso_iff_bijective _).1 (h U.unop)
  have hgPresheafedIso : IsIso (SheafedSpace.forgetToPresheafedSpace.map
      (LocallyRingedSpace.forgetToSheafedSpace.map g)) :=
    PresheafedSpace.isIso_of_components g.toShHom.hom
  have hgSheafedIso : IsIso (LocallyRingedSpace.forgetToSheafedSpace.map g) :=
    isIso_of_reflects_iso (LocallyRingedSpace.forgetToSheafedSpace.map g)
      (SheafedSpace.forgetToPresheafedSpace (C := CommRingCat.{u}))
  exact isIso_of_reflects_iso g LocallyRingedSpace.forgetToSheafedSpace

section

variable {X Y : LocallyRingedSpace.{u}} (f : X ⟶ Y) [hf : IsClosedImmersion f.toShHom]
  (D : ClosedSubspaceData Y (idealSheaf f.toShHom)
    (kernel.ι (SheafOfModules.unitToPushforwardObjUnit (structureSheafHom f.toShHom))))

/-- The isomorphism `f_* 𝒪_X ≅ i_* 𝒪_D` identifying both sides with the cokernel of the inclusion
of the ideal sheaf. -/
private noncomputable def quotientComparisonIso :
    (SheafOfModules.pushforward.{u} (structureSheafHom f.toShHom)).obj
        (SheafOfModules.unit (structureSheafRing X.toRingedSpace)) ≅
      (SheafOfModules.pushforward.{u} (structureSheafHom D.inclusion.toShHom)).obj
        (SheafOfModules.unit (structureSheafRing D.space.toRingedSpace)) :=
  (cokernelKernelIso (SheafOfModules.unitToPushforwardObjUnit
    (structureSheafHom f.toShHom))).symm ≪≫ D.quotientIso

/-- The comparison `f_* 𝒪_X ≅ i_* 𝒪_D` commutes with the two structure-sheaf maps. -/
private theorem unitToPushforwardObjUnit_comp_quotientComparisonIso :
    SheafOfModules.unitToPushforwardObjUnit (structureSheafHom f.toShHom) ≫
        (quotientComparisonIso f D).hom =
      SheafOfModules.unitToPushforwardObjUnit (structureSheafHom D.inclusion.toShHom) := by
  have h1 : SheafOfModules.unitToPushforwardObjUnit (structureSheafHom f.toShHom) ≫
        (quotientComparisonIso f D).hom =
      SheafOfModules.unitToPushforwardObjUnit (structureSheafHom f.toShHom) ≫
        (cokernelKernelIso (SheafOfModules.unitToPushforwardObjUnit
          (structureSheafHom f.toShHom))).inv ≫ D.quotientIso.hom := rfl
  have h2 := (Iso.comp_inv_eq (cokernelKernelIso (SheafOfModules.unitToPushforwardObjUnit
    (structureSheafHom f.toShHom)))).2 (cokernelKernelIso_fac
      (SheafOfModules.unitToPushforwardObjUnit (structureSheafHom f.toShHom))).symm
  refine h1.trans (((Category.assoc _ _ _).symm.trans ?_).trans D.quotientIso_compat)
  exact congrArg (fun k => k ≫ D.quotientIso.hom) h2

/-- A factorization of a closed immersion through the closed subspace cut out by its ideal sheaf
is an isomorphism. -/
private theorem isIso_of_factorization (g : X ⟶ D.space) (hg : g ≫ D.inclusion = f) : IsIso g := by
  have hi := IsClosedImmersion.isClosedEmbedding (i := D.inclusion.toShHom)
  have hstage1 := isIso_pushforward_map_structureSheafMap f D.inclusion g hg
    (quotientComparisonIso f D) (unitToPushforwardObjUnit_comp_quotientComparisonIso f D)
  have hstage2 : ∀ U : Opens D.space, IsIso ((SheafOfModules.unitToPushforwardObjUnit
      (structureSheafHom g.toShHom)).val.app (op U)) :=
    isIso_val_app_of_isIso_pushforward_map g D.inclusion hi.isInducing hstage1
  have hemb : Topology.IsClosedEmbedding g.base :=
    isClosedEmbedding_base_of_factorization g D.inclusion hi
      (by rw [hg]; exact hf.isClosedEmbedding)
  exact isIso_of_isIso_val_app g
    ⟨hemb.injective, surjective_base_of_isIso_val_app g hemb.isClosed_range hstage2⟩
    hemb.isClosedMap hstage2

/-- A closed immersion is uniquely isomorphic over its target to any closed subspace realizing
its ideal sheaf. -/
private theorem existsUnique_iso_of_closedSubspaceData :
    ∃! e : X ≅ D.space, e.hom ≫ D.inclusion = f := by
  obtain ⟨g, hg⟩ := (factorsThrough_closedSubspace_iff D f).2 (by
    rw [pullbackIdealMap_eq_zero_iff]
    exact kernel.condition _)
  have : IsIso g := isIso_of_factorization f D g hg
  exact ⟨asIso g, hg, fun e' he' ↦ Iso.ext (congrArg Subtype.val
    ((subsingleton_factorizations_closedSubspace _ _ D f).elim ⟨e'.hom, he'⟩ ⟨g, hg⟩))⟩

end

/-- A closed immersion is uniquely isomorphic over its target to the closed subspace defined by
its ideal sheaf. -/
@[stacks 01HO]
theorem existsUnique_iso_closedSubspace {X Y : LocallyRingedSpace.{u}} (f : X ⟶ Y)
    [hf : IsClosedImmersion f.toShHom] :
    let Z := closedSubspace Y (idealSheaf f.toShHom) (kernel.ι _) hf.kernel_locallyGenerated
    ∃! e : X ≅ Z.space, e.hom ≫ Z.inclusion = f :=
  existsUnique_iso_of_closedSubspaceData f _

end Stacks.ClosedImmersion

end
