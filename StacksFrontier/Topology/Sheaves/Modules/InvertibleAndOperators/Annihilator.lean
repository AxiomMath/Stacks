module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Submodule
public import Mathlib.Algebra.Category.ModuleCat.Stalk
public import Mathlib.RingTheory.Ideal.Maps
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafHomLeftExact
public import StacksFrontier.Topology.Sheaves.Functors.Module.RingedSpace
public import StacksFrontier.Topology.Sheaves.RingedSpace.Basic
public import StacksFrontier.Topology.Sheaves.Sheaf.Module

/-!
# The annihilator of a sheaf of modules

Let `F` be a sheaf of modules on a ringed space `X`. Its *annihilator* is the subsheaf of the
structure sheaf whose sections over an open `U` are those `r ∈ 𝒪_X(U)` all of whose
restrictions act as zero on all local sections of `F`. Equivalently it is the kernel of the
canonical map from `𝒪_X`, viewed as a module over itself, to the internal endomorphism sheaf
of `F`; both descriptions are proved here, and the germs of local sections of the annihilator
are shown to annihilate the stalk of `F`.

Quantifying over all restrictions is what makes the defining condition stable under
restriction, so the resulting subfunctor is a subpresheaf; it is a subsheaf because the
condition is local on the open, which is where the sheaf condition on `F` enters.

## Main definitions

* `Stacks.SheafOfModules.annihilatorPresheafSubmodule`: the annihilator as a submodule of the
  underlying presheaf of the structure sheaf.
* `Stacks.SheafOfModules.annihilatorSheaf`: the annihilator as a submodule sheaf of the
  structure sheaf, regarded as a module over itself.
* `Stacks.SheafOfModules.scalarAction`: the canonical morphism from the structure sheaf to the
  internal endomorphism sheaf of `F`, acting by multiplication on every smaller open.
* `Stacks.SheafOfModules.annihilatorSheafIsKernel`: the canonical inclusion of the annihilator
  exhibits it as the categorical kernel of `scalarAction`.

## Main results

* `Stacks.SheafOfModules.mem_annihilatorSheaf_iff`: a section lies in the annihilator exactly
  when each of its restrictions annihilates every local section of `F`.
* `Stacks.SheafOfModules.scalarAction_component`: the scalar action is multiplication on each
  local component.
* `Stacks.SheafOfModules.annihilatorSheaf_obj_eq_ker_scalarAction`: sectionwise, the
  annihilator is the kernel of the scalar action.
* `Stacks.SheafOfModules.stalk_annihilatorSheaf_le_annihilator_stalk`: the germs of local
  sections of the annihilator annihilate the stalk of `F`.

## Implementation notes

The structure sheaf is regarded as its rank-one module
`SheafOfModules.unit (structureSheafRing X)`, and the canonical inclusion
of the annihilator is `(annihilatorSheaf X F).ι`, which inherits its monomorphism instance.
The internal endomorphism sheaf is taken through the `SheafHom` interface of Stacks 01CO, with
its additive identification of sections, its restriction naturality and its compatibility with
scalars; `scalarAction_component` identifies the canonical map with local multiplication.

The stalk of the annihilator subsheaf is described directly as the set of germs of its local
sections inside the stalk of the structure sheaf. This avoids choosing a model for the stalk of
a submodule sheaf, and avoids choosing an isomorphism between the stalk of the rank-one module
and the stalk of the sheaf of rings.

The module universe is independent of the ring universe in `annihilatorSheaf` and its
membership API. The space and ring universes agree, as `structureSheafRing` requires; the kernel
comparison and the internal endomorphism sheaf use the common-universe `SheafHom` interface.

## References

* [Stacks Project, Tag 0H2H](https://stacks.math.columbia.edu/tag/0H2H)
* [Stacks Project, Tag 0H2I](https://stacks.math.columbia.edu/tag/0H2I)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open RingedSpaceModuleAdjunction

universe u v

namespace Stacks.SheafOfModules

attribute [local implicit_reducible] SheafOfModules.unit PresheafOfModules.unit
  PresheafOfModules.presheaf TopCat.Sheaf structureSheafRing ModuleCat.restrictScalars

-- `structureSheafRing X` reduces to `X.presheaf ⋙ forget₂ _ _`, while the `SheafHom` interface
-- and its `SheafOfModules` indices are stated at `structureSheaf X.sheaf`, that is at
-- `(sheafCompose _ (forget₂ _ _)).obj X.sheaf`; unfolding `sheafCompose` and `SheafedSpace.sheaf`
-- is what identifies the two.
attribute [local instance_reducible] CategoryTheory.sheafCompose
  AlgebraicGeometry.SheafedSpace.sheaf

variable (X : RingedSpace.{u, u})
variable (F : SheafOfModules.{v} (structureSheafRing X))

/-- The annihilator as a submodule of the underlying presheaf of the structure sheaf.
A section belongs when each of its restrictions kills every section of `F` on the
smaller open. -/
noncomputable def annihilatorPresheafSubmodule :
    (SheafOfModules.unit (structureSheafRing X)).val.Submodule where
  obj := fun U => ({
    carrier := { r : (structureSheafRing X).obj.obj U |
      ∀ (V : (Opens X.carrier)ᵒᵖ) (f : U ⟶ V) (m : F.val.obj V),
        ((structureSheafRing X).obj.map f r) • m = 0 }
    zero_mem' := by
      intro V f m
      simp
    add_mem' := by
      intro a b ha hb V f m
      change ((structureSheafRing X).obj.map f).hom (a + b) • m = 0
      rw [map_add, add_smul, ha V f m, hb V f m, zero_add]
    smul_mem' := by
      intro a b hb V f m
      change ((structureSheafRing X).obj.map f).hom (a * b) • m = 0
      rw [map_mul, mul_smul, hb V f m, smul_zero]
    } : _root_.Submodule ((structureSheafRing X).obj.obj U) ((structureSheafRing X).obj.obj U))
  map := by
    intro U V f r hr W g m
    change ((structureSheafRing X).obj.map g) ((structureSheafRing X).obj.map f r) • m = 0
    simpa only [Functor.map_comp_apply] using hr W (f ≫ g) m

/-- **Stacks Project, Tag 0H2H.** The annihilator of an `𝒪_X`-module `F` is the
subsheaf of `𝒪_X` consisting of the local functions that act as zero on `F`.  Equivalently,
it is the kernel of the canonical map from `𝒪_X` to the internal endomorphism sheaf of
`F`. -/
@[stacks 0H2H, ega "0 5.3.7" "annihilator def"]
noncomputable def annihilatorSheaf :
    (SheafOfModules.unit (structureSheafRing X)).Submodule where
  toSubmodule := annihilatorPresheafSubmodule X F
  isSheaf := by
    intro U r hr V f m
    have hF : Presheaf.IsSheaf (Opens.grothendieckTopology X.carrier)
        (F.val.presheaf ⋙ forget AddCommGrpCat.{v}) :=
      GrothendieckTopology.HasSheafCompose.isSheaf _ F.isSheaf
    apply (hF.isSheafFor _
      ((Opens.grothendieckTopology X.carrier).pullback_stable f.unop hr)).isSeparatedFor.ext
    intro W g hg
    change F.val.map g.op (((structureSheafRing X).obj.map f r) • m) = F.val.map g.op 0
    rw [F.val.map_smul, map_zero, ← Functor.map_comp_apply]
    dsimp [CategoryTheory.Subfunctor.sieveOfSection] at hg
    have hkill := hg (op W) (𝟙 _) (F.val.map g.op m)
    simp only [op_unop] at hkill
    have unitMapApply {A B : (Opens X.carrier)ᵒᵖ} (i : A ⟶ B)
        (s : (structureSheafRing X).obj.obj A) :
        (SheafOfModules.unit (structureSheafRing X)).val.map i s
          = (structureSheafRing X).obj.map i s := rfl
    have ringMapId (s : (structureSheafRing X).obj.obj (op W)) :
        (structureSheafRing X).obj.map (𝟙 _) s = s := by simp
    rw [ringMapId, PresheafOfModules.presheaf_map_apply_coe, unitMapApply] at hkill
    rw [show (f ≫ g.op) = (g ≫ f.unop).op by simp]
    exact hkill

/-- Membership in the annihilator sheaf, expressed by its canonical local action:
`r ∈ Ann(F)(U)` iff every restriction of `r` annihilates every corresponding local
section of `F`. -/
@[simp]
theorem mem_annihilatorSheaf_iff (U : (Opens X.carrier)ᵒᵖ)
    (r : (structureSheafRing X).obj.obj U) :
    r ∈ (annihilatorSheaf X F).toSubmodule.obj U ↔
      ∀ (V : (Opens X.carrier)ᵒᵖ) (f : U ⟶ V) (m : F.val.obj V),
        ((structureSheafRing X).obj.map f r) • m = 0 :=
  Iff.rfl

section ScalarAction

variable (F : SheafOfModules.{u} (structureSheafRing X)) (H : SheafHom X.sheaf F F)

/-- The canonical scalar-action morphism from the structure sheaf to the internal
endomorphism sheaf: a function acts by multiplication on every smaller open. -/
@[implicit_reducible, ega "0 5.4.3"]
noncomputable def scalarAction : SheafOfModules.unit (structureSheafRing X) ⟶ H.obj :=
  H.obj.unitHomEquiv.symm (PresheafOfModules.sectionsMk
    (fun U => (H.sectionsEquiv U.unop).symm (𝟙 (F.over U.unop))) (by
      intro U V f
      apply (H.sectionsEquiv V.unop).injective
      rw [AddEquiv.apply_symm_apply]
      ext W m
      change (H.sectionsEquiv V.unop
        (H.obj.val.map f ((H.sectionsEquiv U.unop).symm (𝟙 _)))).val.app
          (op (Over.mk W.unop.hom)) m = m
      have hn := H.restrict_natural f.unop.le
        ((H.sectionsEquiv U.unop).symm (𝟙 (F.over U.unop))) W.unop.hom.le m
      rw [AddEquiv.apply_symm_apply] at hn
      change m = _ at hn
      convert hn.symm using 1
      rfl))

/-- On sections, scalar action multiplies the identity endomorphism. -/
theorem scalarAction_app (U : (Opens X.carrier)ᵒᵖ) (r : (structureSheafRing X).obj.obj U) :
    (scalarAction X F H).val.app U r =
      r • (H.sectionsEquiv U.unop).symm (𝟙 (F.over U.unop)) := rfl

/-- The local component formula specifying the canonical scalar-action map. -/
@[simp]
theorem scalarAction_component (U V : Opens X.carrier) (hVU : V ≤ U)
    (r : (structureSheafRing X).obj.obj (op U)) (m : F.val.obj (op V)) :
    (H.sectionsEquiv U ((scalarAction X F H).val.app (op U) r)).val.app
        (op (Over.mk (homOfLE hVU))) m =
      (structureSheafRing X).obj.map (homOfLE hVU).op r • m := by
  rw [scalarAction_app, H.smul_natural, AddEquiv.apply_symm_apply]
  rfl

/-- The annihilator sections are exactly the kernel of the scalar-action map. -/
theorem annihilatorSheaf_obj_eq_ker_scalarAction (U : (Opens X.carrier)ᵒᵖ) :
    (annihilatorSheaf X F).toSubmodule.obj U =
      LinearMap.ker ((scalarAction X F H).val.app U).hom := by
  ext r
  rw [mem_annihilatorSheaf_iff, LinearMap.mem_ker]
  refine ⟨fun hr => ?_, fun hr V f m => ?_⟩
  · apply (H.sectionsEquiv U.unop).injective
    rw [map_zero]
    ext W m
    change (H.sectionsEquiv U.unop ((scalarAction X F H).val.app U r)).val.app
      (op (Over.mk W.unop.hom)) m = 0
    convert (scalarAction_component X F H U.unop W.unop.left W.unop.hom.le r m).trans
      (hr (op W.unop.left) W.unop.hom.op m) using 1
    rfl
  · change (scalarAction X F H).val.app U r = 0 at hr
    have h := scalarAction_component X F H U.unop V.unop f.unop.le r m
    rw [hr, map_zero] at h
    exact h.symm

/-- The canonical inclusion of the annihilator is killed by scalar action. -/
@[reassoc (attr := simp)]
theorem annihilatorSheaf_ι_scalarAction :
    (annihilatorSheaf X F).ι ≫ scalarAction X F H = 0 := by
  ext U r
  exact (annihilatorSheaf_obj_eq_ker_scalarAction X F H U).le r.property

/-- The canonical inclusion exhibits the annihilator sheaf as the categorical
kernel of scalar action into the internal endomorphism sheaf. -/
noncomputable def annihilatorSheafIsKernel :
    Limits.IsLimit (Limits.KernelFork.ofι (annihilatorSheaf X F).ι
      (annihilatorSheaf_ι_scalarAction X F H)) := by
  refine Limits.KernelFork.IsLimit.ofι' _ _ ?_
  intro A k hk
  refine ⟨⟨{
    app := fun U => ModuleCat.ofHom
      (((k.val.app U).hom).codRestrict ((annihilatorSheaf X F).toSubmodule.obj U)
        (fun s => ?_))
    naturality := ?_ }⟩, ?_⟩
  · rw [annihilatorSheaf_obj_eq_ker_scalarAction X F H U, LinearMap.mem_ker]
    exact congrArg (fun q => q.val.app U s) hk
  · intro U V f
    ext s
    exact Subtype.ext (PresheafOfModules.naturality_apply k.val f s)
  · ext U s
    rfl

end ScalarAction

section Stalk

variable (F : SheafOfModules.{u} (structureSheafRing X))

/-- **Stacks Project, Tag 0H2I.** The germs of local sections of the annihilator
sheaf at `x` annihilate the stalk `Fₓ`. -/
@[stacks 0H2I]
theorem stalk_annihilatorSheaf_le_annihilator_stalk (x : X) :
    { a : (show X.carrier.Presheaf RingCat from (structureSheafRing X).obj).stalk x |
      ∃ (U : Opens X.carrier) (hx : x ∈ U) (r : (structureSheafRing X).obj.obj (op U)),
        r ∈ (annihilatorSheaf X F).toSubmodule.obj (op U) ∧
          (show X.carrier.Presheaf RingCat from (structureSheafRing X).obj).germ U x hx r = a } ⊆
      Module.annihilator
        ((show X.carrier.Presheaf RingCat from (structureSheafRing X).obj).stalk x)
        ((show X.carrier.Presheaf Ab.{u} from F.val.presheaf).stalk x) := by
  rintro a ⟨U, hxU, r, hr, rfl⟩
  refine Module.mem_annihilator.mpr fun m => ?_
  obtain ⟨V, hxV, m, rfl⟩ := TopCat.Presheaf.exists_germ_eq (x := x) F.val.presheaf m
  let W := U ⊓ V
  have hxW : x ∈ W := ⟨hxU, hxV⟩
  have hr' := (mem_annihilatorSheaf_iff X F (op U) r).mp hr
    (op W) (homOfLE inf_le_left).op (F.val.presheaf.map (homOfLE inf_le_right).op m)
  rw [← TopCat.Presheaf.germ_res_apply (structureSheafRing X).obj (homOfLE inf_le_left) x hxW r,
    ← TopCat.Presheaf.germ_res_apply F.val.presheaf (homOfLE inf_le_right) x hxW m,
    ← PresheafOfModules.germ_ringCat_smul F.val x W hxW, hr', map_zero]

end Stalk

end Stacks.SheafOfModules
