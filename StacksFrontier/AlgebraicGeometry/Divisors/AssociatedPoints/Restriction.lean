module

public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Images
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.Mono
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.Quasicoherent
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.StructureSheafStalk
public import StacksFrontier.Topology.Sheaves.Modules.Colimits
public import StacksCore.Tactic.StacksAttribute

/-!
# Restriction of sections to an open containing the weakly associated points

A global section of a quasi-coherent module on a scheme is determined by its restriction to any
open subset containing every weakly associated point of the module; on a locally Noetherian
scheme, containing every associated point suffices.

## Main results

* `AlgebraicGeometry.restriction_injective_of_weaklyAssociatedPoints_subset`: restriction of
  global sections to an open containing all weakly associated points is injective.
* `AlgebraicGeometry.restriction_injective_of_associatedPoints_subset`: the same on a locally
  Noetherian scheme, for an open containing all associated points.

## Implementation notes

The restriction map is the map of the underlying presheaf along the canonical inclusion of the
open subset into the maximal open. A global section `s` is turned into a morphism from the
structure sheaf; its image is a quasi-coherent subsheaf of `F`, the hypothesis forces that image
to have no weakly associated point, hence to vanish by Stacks tag 05AP, and therefore `s = 0`.

The stalk functor is taken with `AlgebraicGeometry.Scheme.Modules` as its source rather than the
unfolded `SheafOfModules X.ringCatSheaf`, because only the former carries the abelian structure
as an instance, and images and epimorphisms are needed in the same category.

## References

* [Stacks Project, Tag 0B3L](https://stacks.math.columbia.edu/tag/0B3L)
* [Stacks Project, Tag 0B3M](https://stacks.math.columbia.edu/tag/0B3M)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u

namespace AlgebraicGeometry

/-- Taking the stalk at `x` of an `𝒪_X`-module, as a functor out of `X.Modules`. -/
private noncomputable abbrev moduleStalkFunctor (X : Scheme.{u}) (x : X) :
    X.Modules ⥤ ModuleCat.{u} (TopCat.Presheaf.stalk (C := RingCat.{u}) X.ringCatSheaf.obj x) :=
  SheafOfModules.stalkFunctor X.ringCatSheaf x

/-- A global section of a sheaf of modules on a scheme, read as a compatible family of
sections. -/
private noncomputable def globalSectionFamily {X : Scheme.{u}} (F : X.Modules)
    (s : F.val.presheaf.obj (op ⊤)) : F.sections :=
  PresheafOfModules.sectionsMk (fun V => F.val.presheaf.map (homOfLE le_top).op s)
    (fun {V W} f => by
      change F.val.presheaf.map f (F.val.presheaf.map _ s) = F.val.presheaf.map _ s
      rw [← Functor.map_comp_apply]
      congr 2)

/-- A monomorphism of sheaves of modules on a scheme is a monomorphism on every stalk. -/
private lemma stalk_map_mono_of_mono {X : Scheme.{u}} {M N : X.Modules} (f : M ⟶ N) [Mono f]
    (x : X) : Mono ((moduleStalkFunctor X x).map f) :=
  ConcreteCategory.mono_of_injective _ (stalk_map_injective_of_mono f x)

/-- The morphism classifying a global section sends `1` on an open `V` to the restriction of the
section to `V`. -/
private lemma unitHom_app_one {X : Scheme.{u}} (F : X.Modules) (s : F.val.presheaf.obj (op ⊤))
    (f : structureSheafModule X ⟶ F) (hf : F.unitHomEquiv f = globalSectionFamily F s)
    (V : X.Opens) : (ConcreteCategory.hom (f.val.app (op V))) (1 : X.ringCatSheaf.obj.obj (op V)) =
      (F.val.presheaf.map (homOfLE le_top : V ⟶ ⊤).op) s := by
  have h : (F.unitHomEquiv f).val (op V) =
      (ConcreteCategory.hom (f.val.app (op V))) (1 : X.ringCatSheaf.obj.obj (op V)) := rfl
  rw [← h, hf]
  rfl

/-- The morphism classifying a global section vanishes on every open on which the section
restricts to zero. -/
private lemma unitHom_app_eq_zero {X : Scheme.{u}} (F : X.Modules) (U : X.Opens)
    (s : F.val.presheaf.obj (op ⊤)) (f : structureSheafModule X ⟶ F)
    (hf : F.unitHomEquiv f = globalSectionFamily F s)
    (hs : F.val.presheaf.map (homOfLE le_top : U ⟶ ⊤).op s = 0) (V : X.Opens) (hV : V ≤ U) :
    f.val.app (op V) = 0 := by
  have hval := unitHom_app_one F s f hf V
  apply ModuleCat.hom_ext
  have hcomp : (homOfLE (hV.trans le_top) : V ⟶ ⊤) =
      homOfLE hV ≫ (homOfLE le_top : U ⟶ ⊤) := Subsingleton.elim _ _
  have hres' := congrArg (fun z => F.val.presheaf.map (homOfLE hV).op z) hs
  rw [← Functor.map_comp_apply, ← op_comp, ← hcomp] at hres'
  have hres : (ConcreteCategory.hom
      (F.val.presheaf.map (homOfLE (hV.trans le_top)).op)) s = 0 :=
    hres'.trans (AddMonoidHom.map_zero _)
  rw [hres] at hval
  exact (LinearMap.ringLmapEquivSelf (X.ringCatSheaf.obj.obj (op V)) ℤ
    (F.val.obj (op V))).injective hval

/-- A morphism of sheaves of modules vanishing on every open contained in `U` vanishes on the
stalk at every point of `U`. -/
private lemma stalk_map_eq_zero_of_app_eq_zero {X : Scheme.{u}} {M N : X.Modules} (f : M ⟶ N)
    (U : X.Opens) (hf : ∀ V ≤ U, f.val.app (op V) = 0) (x : X) (hx : x ∈ U) :
    (moduleStalkFunctor X x).map f = 0 := by
  ext a
  let P := (PresheafOfModules.toPresheaf X.ringCatSheaf.obj).obj M.val
  obtain ⟨V, hxV, aV, haV⟩ := TopCat.Presheaf.exists_germ_eq P a
  have hxW : x ∈ V ⊓ U := ⟨hxV, hx⟩
  have haW : TopCat.Presheaf.germ P (V ⊓ U) x hxW
      (P.map (homOfLE (inf_le_left : V ⊓ U ≤ V)).op aV) = a := by
    rwa [TopCat.Presheaf.germ_res_apply]
  rw [← haW]
  change ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
    ((PresheafOfModules.toPresheaf X.ringCatSheaf.obj).map f.val)) _ = 0
  rw [TopCat.Presheaf.stalkFunctor_map_germ_apply (V ⊓ U) x hxW
    ((PresheafOfModules.toPresheaf X.ringCatSheaf.obj).map f.val)]
  have hzero : (((PresheafOfModules.toPresheaf X.ringCatSheaf.obj).map f.val).app
      (op (V ⊓ U))) ((P.map (homOfLE (inf_le_left : V ⊓ U ≤ V)).op) aV) = 0 := by
    change (ConcreteCategory.hom (f.val.app (op (V ⊓ U))))
      ((P.map (homOfLE (inf_le_left : V ⊓ U ≤ V)).op) aV) = 0
    rw [hf (V ⊓ U) inf_le_right]
    rfl
  rw [hzero]
  exact map_zero _

/-- If a morphism of sheaves of modules vanishes on the stalk at `x`, so does its image. -/
private lemma image_stalk_isZero_of_stalk_map_eq_zero {X : Scheme.{u}} {M N : X.Modules}
    (f : M ⟶ N) (x : X) (hfx : (moduleStalkFunctor X x).map f = 0) :
    IsZero ((moduleStalkFunctor X x).obj (image f)) := by
  have hpc : PreservesColimits (moduleStalkFunctor X x) :=
    SheafOfModules.stalkFunctor_preservesColimits X.ringCatSheaf x
  have hepi : Epi ((moduleStalkFunctor X x).map (factorThruImage f)) :=
    preserves_epi_of_preservesColimit (moduleStalkFunctor X x) (factorThruImage f)
  have hmono : Mono ((moduleStalkFunctor X x).map (image.ι f)) :=
    stalk_map_mono_of_mono (image.ι f) x
  have hcomp : (moduleStalkFunctor X x).map (factorThruImage f) ≫
      (moduleStalkFunctor X x).map (image.ι f) = 0 := by
    rw [← Functor.map_comp, image.fac f, hfx]
  refine IsZero.of_mono_eq_zero ((moduleStalkFunctor X x).map (image.ι f)) ?_
  apply (cancel_epi ((moduleStalkFunctor X x).map (factorThruImage f))).1
  simpa using hcomp

/-- If a global section restricts to zero on an open `U`, then at every point of `U` the stalk
of the image of the morphism it classifies vanishes. -/
private lemma section_image_stalk_isZero {X : Scheme.{u}} (F : X.Modules) (U : X.Opens)
    (s : F.val.presheaf.obj (op ⊤)) (f : structureSheafModule X ⟶ F)
    (hf : F.unitHomEquiv f = globalSectionFamily F s)
    (hs : F.val.presheaf.map (homOfLE le_top : U ⟶ ⊤).op s = 0) (x : X) (hx : x ∈ U) :
    IsZero ((moduleStalkFunctor X x).obj (image f)) :=
  image_stalk_isZero_of_stalk_map_eq_zero f x
    (stalk_map_eq_zero_of_app_eq_zero f U (unitHom_app_eq_zero F U s f hf hs) x hx)

/-- **Stacks Project, Tag 0B3M.** Restriction of sections of a quasi-coherent module to an open
containing all its weakly associated points is injective. -/
@[stacks 0B3M]
theorem restriction_injective_of_weaklyAssociatedPoints_subset {X : Scheme.{u}} (F : X.Modules)
    [F.IsQuasicoherent] (U : X.Opens)
    (hU : Stacks.Divisors.weaklyAssociatedPoints F ⊆ U) :
    Function.Injective (F.presheaf.map (homOfLE le_top : U ⟶ ⊤).op) := by
  intro s t hst
  rw [← sub_eq_zero]
  have hs : F.presheaf.map (homOfLE le_top : U ⟶ ⊤).op (s - t) = 0 := by
    rw [map_sub, hst, sub_self]
  let f : structureSheafModule X ⟶ F := F.unitHomEquiv.symm (globalSectionFamily F (s - t))
  have hf : F.unitHomEquiv f = globalSectionFamily F (s - t) := Equiv.apply_symm_apply _ _
  let I : X.Modules := image f
  let g : I ⟶ F := image.ι f
  let S : ShortComplex X.Modules := ShortComplex.mk g (cokernel.π g) (cokernel.condition g)
  have hI : I.IsQuasicoherent := isQuasicoherent_image f
  have hS : S.ShortExact :=
    ShortComplex.ShortExact.mk' (ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel _))
      (show Mono g from inferInstance) (show Epi (cokernel.π g) from inferInstance)
  have hW : Stacks.Divisors.weaklyAssociatedPoints I = ∅ := by
    ext x
    simp only [Set.mem_empty_iff_false, iff_false]
    intro hx
    have hzeroI := section_image_stalk_isZero F U (s - t) f hf hs x
      (hU (weaklyAssociatedPoints_subset_of_shortExact S hS hx))
    have hsub : Subsingleton
        (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) I.val.presheaf x) :=
      ModuleCat.isZero_iff_subsingleton.mp hzeroI
    rw [Stacks.Divisors.mem_weaklyAssociatedPoints_iff] at hx
    change IsWeaklyAssociatedPrime (X.presheaf.stalk x)
      (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) I.val.presheaf x)
      (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) at hx
    obtain ⟨m, hm⟩ := hx
    obtain rfl : m = 0 := hsub.elim _ _
    simp [Submodule.annihilator_bot, Ideal.minimalPrimes_top] at hm
  have hzeroF : f = 0 := by
    rw [← image.fac f, ((isZero_iff_weaklyAssociatedPoints_eq_empty I).2 hW).eq_of_tgt
      (factorThruImage f) 0, zero_comp]
  have htop : F.val.presheaf.map (homOfLE (le_refl (⊤ : X.Opens))).op (s - t) = 0 := by
    have h := unitHom_app_one F (s - t) f hf ⊤
    rw [hzeroF] at h
    exact h.symm.trans (by rfl)
  rwa [show (homOfLE (le_refl (⊤ : X.Opens))) = 𝟙 (⊤ : X.Opens) from Subsingleton.elim _ _,
    op_id, F.val.presheaf.map_id] at htop

/-- **Stacks Project, Tag 0B3L.** Restriction of sections of a quasi-coherent sheaf on a locally
Noetherian scheme to an open subset containing all associated points is injective. -/
@[stacks 0B3L]
theorem restriction_injective_of_associatedPoints_subset (X : Scheme.{u})
    [IsLocallyNoetherian X] (F : X.Modules) [F.IsQuasicoherent] (U : X.Opens)
    (hU : Stacks.Divisors.associatedPoints F ⊆ (U : Set X)) :
    Function.Injective (F.presheaf.map (homOfLE (show U ≤ (⊤ : X.Opens) from le_top)).op) :=
  restriction_injective_of_weaklyAssociatedPoints_subset F U
    ((associatedPoints_eq_weaklyAssociatedPoints X F) ▸ hU)

end AlgebraicGeometry
