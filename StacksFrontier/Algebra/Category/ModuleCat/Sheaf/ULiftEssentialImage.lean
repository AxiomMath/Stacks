module

public import Mathlib.Algebra.Module.Shrink
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExtensionByZeroUnitULift
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ULiftFiniteColimits
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ULiftUnit
public import StacksFrontier.AlgebraicGeometry.Topologies.GlobalPresentationComparison
public import StacksCore.CategoryTheory.Abelian.SerreClass.Weak
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DirectImage

/-!
# The essential image of the universe lift of sheaves of modules

Let `R` be a sheaf of rings on a site `C`. `Stacks.SheafOfModules.moduleULift` lifts the module
sections of a sheaf of `R`-modules from a universe `z` to `max z t`; it is fully faithful
(`Stacks.SheafOfModules.moduleULiftFullyFaithful`) and exact
(`Stacks.SheafOfModules.preservesFiniteLimits_moduleULift`,
`Stacks.SheafOfModules.preservesFiniteColimits_moduleULift`). This file identifies its essential
image: a sheaf of modules with sections in `max z t` is the lift of one with sections in `z`
exactly when all of its modules of sections are `z`-small. It follows that the essential image is
a weak Serre class — closed under kernels, cokernels and extensions — since a module of sections
of an extension of two sheaves with `z`-small sections is an extension of a submodule of a
`z`-small module by a `z`-small module.

This is what lets a construction made at a larger module universe — the direct image of
modules along a `1`-morphism of algebraic stacks, whose limits are indexed by sites with objects
in `Type (u + 1)` — be brought back to the module universe `u` of the schemes: once its values
are shown to have `u`-small sections, it factors through the lift.

## Main results

* `AddMonoidHom.small_of_ker_le_range`: the middle term of an exact sequence of abelian groups
  with small ends is small.
* `PresheafOfModules.shrinkObj` and `Stacks.SheafOfModules.shrinkObj`, with
  `Stacks.SheafOfModules.moduleULiftShrinkObjIso`: a (pre)sheaf of modules with `z`-small
  sections, shrunk to module universe `z`, whose lift is the original one.
* `Stacks.SheafOfModules.moduleULift_essImage_iff`: the essential image of the lift is the sheaves
  of modules with `z`-small sections.
* `Stacks.SheafOfModules.isWeakSerreClass_essImage_moduleULift`: that essential image is a weak
  Serre class of the sheaves of modules with sections in `max z t`.
* `CategoryTheory.Functor.small_sections_of_essentiallySmall` and
  `SheafOfModules.small_directImageOfEq_obj`: the direct image of a sheaf of modules with
  `z`-small sections, along a functor with essentially `z`-small comma categories, has `z`-small
  sections.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe v₁ u₁ w z t

/-- **The middle term of an exact sequence of abelian groups with small ends is small**: an
element `b` is determined by its image `g b` and by the difference between `b` and a chosen
preimage of `g b`, which lies in the image of `f`. -/
theorem AddMonoidHom.small_of_ker_le_range {A B C : Type*} [AddCommGroup A] [AddCommGroup B]
    [AddCommGroup C] (f : A →+ B) (g : B →+ C) (h : ∀ b, g b = 0 → ∃ a, f a = b)
    [Small.{z} A] [Small.{z} C] : Small.{z} B := by
  let s : C → B := Function.invFun g
  have hs : ∀ b, g (s (g b)) = g b := fun b ↦ Function.invFun_eq (f := ⇑g) ⟨b, rfl⟩
  let ψ : B → C × Set.range f := fun b ↦
    (g b, ⟨b - s (g b), h _ (by rw [map_sub, hs, sub_self])⟩)
  refine small_of_injective (f := ψ) fun b b' hbb ↦ ?_
  have h₁ : g b = g b' := congrArg Prod.fst hbb
  have h₂ : b - s (g b) = b' - s (g b') := congrArg (fun x ↦ (x.2 : B)) hbb
  rw [h₁] at h₂
  exact sub_left_injective h₂

/-- **The sections of a functor to types over an essentially `z`-small category, with `z`-small
values, form a `z`-small type**: a section is determined by its values at a set of
representatives of the isomorphism classes of objects. -/
theorem CategoryTheory.Functor.small_sections_of_essentiallySmall {K : Type*} [Category K]
    [EssentiallySmall.{z} K] (G : K ⥤ Type*) [∀ k, Small.{z} (G.obj k)] :
    Small.{z} G.sections := by
  let e := equivSmallModel.{z} K
  refine small_of_injective (f := fun s (k : SmallModel.{z} K) ↦ s.1 (e.inverse.obj k))
    fun s t h ↦ Subtype.ext (funext fun k ↦ ?_)
  have hk : s.1 (e.inverse.obj (e.functor.obj k)) = t.1 (e.inverse.obj (e.functor.obj k)) :=
    congrFun h (e.functor.obj k)
  have key (u : G.sections) :
      G.map (e.unitIso.inv.app k) (u.1 (e.inverse.obj (e.functor.obj k))) = u.1 k :=
    u.2 _
  rw [← key s, ← key t, hk]

namespace PresheafOfModules

variable {C : Type u₁} [Category.{v₁} C] {R : Cᵒᵖ ⥤ RingCat.{w}}

section Shrink

variable (M : PresheafOfModules.{max z t} R) [∀ U, Small.{z} (M.obj U)]

/-- A presheaf of modules all of whose sections are `z`-small, shrunk to module universe `z`:
the sections over `U` are `Shrink (M.obj U)`, with the module structure transported along
`Shrink.linearEquiv`, and the restriction maps are those of `M` conjugated by it. -/
noncomputable def shrinkObj : PresheafOfModules.{z} R where
  obj U := ModuleCat.of (R.obj U) (Shrink.{z} (M.obj U))
  map {U V} f := ModuleCat.ofHom
    (R := R.obj U)
    (X := ModuleCat.of (R.obj U) (Shrink.{z} (M.obj U)))
    (Y := (ModuleCat.restrictScalars (R.map f).hom).obj
      (ModuleCat.of (R.obj V) (Shrink.{z} (M.obj V))))
    { toFun := fun m ↦ (Shrink.linearEquiv.{z} (R.obj V) (M.obj V)).symm
        (M.map f (Shrink.linearEquiv.{z} (R.obj U) (M.obj U) m))
      map_add' := fun x y ↦
        (congrArg (Shrink.linearEquiv.{z} (R.obj V) (M.obj V)).symm
          ((congrArg (M.map f) ((Shrink.linearEquiv.{z} (R.obj U) (M.obj U)).map_add x y)).trans
            ((M.map f).hom.map_add _ _))).trans
          ((Shrink.linearEquiv.{z} (R.obj V) (M.obj V)).symm.map_add _ _)
      map_smul' := fun r m ↦
        (congrArg (Shrink.linearEquiv.{z} (R.obj V) (M.obj V)).symm
          ((congrArg (M.map f) ((Shrink.linearEquiv.{z} (R.obj U) (M.obj U)).map_smul r m)).trans
            (M.map_smul f r _))).trans
          ((Shrink.linearEquiv.{z} (R.obj V) (M.obj V)).symm.map_smul _ _) }
  map_id U := by
    ext m
    change (Shrink.linearEquiv.{z} (R.obj U) (M.obj U)).symm
      (M.map (𝟙 U) (Shrink.linearEquiv.{z} (R.obj U) (M.obj U) m)) = m
    rw [M.map_id]
    exact (Shrink.linearEquiv.{z} (R.obj U) (M.obj U)).symm_apply_apply m
  map_comp {U V W} f g := by
    ext m
    change (Shrink.linearEquiv.{z} (R.obj W) (M.obj W)).symm
        (M.map (f ≫ g) (Shrink.linearEquiv.{z} (R.obj U) (M.obj U) m)) =
      (Shrink.linearEquiv.{z} (R.obj W) (M.obj W)).symm (M.map g
        (Shrink.linearEquiv.{z} (R.obj V) (M.obj V)
          ((Shrink.linearEquiv.{z} (R.obj V) (M.obj V)).symm
            (M.map f (Shrink.linearEquiv.{z} (R.obj U) (M.obj U) m)))))
    exact congrArg (Shrink.linearEquiv.{z} (R.obj W) (M.obj W)).symm
      ((M.map_comp_apply f g _).trans (congrArg (M.map g)
        ((Shrink.linearEquiv.{z} (R.obj V) (M.obj V)).apply_symm_apply _).symm))

/-- The universe lift of the shrunk presheaf of modules is the presheaf of modules itself. -/
noncomputable def uliftShrinkObjIso :
    (Stacks.SheafOfModules.presheafULift.{t} R).obj (shrinkObj M) ≅ M :=
  isoMk (fun U ↦ (ULift.moduleEquiv.trans
      (Shrink.linearEquiv.{z} (R.obj U) (M.obj U))).toModuleIso)
    (fun {U V} f ↦ by
      ext m
      change Shrink.linearEquiv.{z} (R.obj V) (M.obj V)
        ((Shrink.linearEquiv.{z} (R.obj V) (M.obj V)).symm
          (M.map f (Shrink.linearEquiv.{z} (R.obj U) (M.obj U) m.down))) = _
      exact (Shrink.linearEquiv.{z} (R.obj V) (M.obj V)).apply_symm_apply _)

end Shrink

end PresheafOfModules

namespace Stacks.SheafOfModules

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C} (R : Sheaf J RingCat.{w})

/-- A sheaf of modules all of whose sections are `z`-small, shrunk to module universe `z`. -/
noncomputable def shrinkObj (M : _root_.SheafOfModules.{max z t} R)
    [∀ U, Small.{z} (M.val.obj U)] : _root_.SheafOfModules.{z} R where
  val := PresheafOfModules.shrinkObj.{_, _, _, z, t} M.val
  isSheaf := Presheaf.isSheaf_of_isSheaf_comp J _ AddCommGrpCat.uliftFunctor.{t}
    ((Presheaf.isSheaf_of_iso_iff ((PresheafOfModules.toPresheaf R.obj).mapIso
      (PresheafOfModules.uliftShrinkObjIso.{_, _, _, z, t} M.val))).2 M.isSheaf)

/-- The universe lift of the shrunk sheaf of modules is the sheaf of modules itself. -/
noncomputable def moduleULiftShrinkObjIso (M : _root_.SheafOfModules.{max z t} R)
    [∀ U, Small.{z} (M.val.obj U)] : (moduleULift.{t, z} R).obj (shrinkObj R M) ≅ M :=
  (_root_.SheafOfModules.fullyFaithfulForget R).preimageIso
    (PresheafOfModules.uliftShrinkObjIso.{_, _, _, z, t} M.val)

/-- **The essential image of the universe lift** of sheaves of modules consists of the sheaves of
modules all of whose sections are `z`-small. -/
theorem moduleULift_essImage_iff (M : _root_.SheafOfModules.{max z t} R) :
    (moduleULift.{t, z} R).essImage M ↔ ∀ U, Small.{z} (M.val.obj U) := by
  refine ⟨?_, fun _ ↦ ⟨shrinkObj R M, ⟨moduleULiftShrinkObjIso R M⟩⟩⟩
  rintro ⟨N, ⟨e⟩⟩ U
  have : Small.{z} ((_root_.SheafOfModules.evaluation R U).obj
      ((moduleULift.{t, z} R).obj N)) :=
    small_ulift (N.val.obj U)
  exact small_of_injective (f := fun x ↦ ((_root_.SheafOfModules.evaluation R U).mapIso e).inv x)
    ((_root_.SheafOfModules.evaluation R U).mapIso e).toLinearEquiv.symm.injective

section WeakSerre

variable [HasSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasSheafify J AddCommGrpCat.{max u₁ v₁ w}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u₁ v₁ w}]

/-- **The essential image of the universe lift is a weak Serre class**: it contains `0` and is
closed under kernels and cokernels, the lift being exact and fully faithful, and under
extensions, because the sections of an extension of two sheaves with `w`-small sections are an
extension of a submodule of a `w`-small module by a `w`-small module. -/
theorem isWeakSerreClass_essImage_moduleULift :
    (moduleULift.{max u₁ v₁ w, w} R).essImage.IsWeakSerreClass := by
  let F := moduleULift.{max u₁ v₁ w, w} R
  have : F.Full := (moduleULiftFullyFaithful R).full
  have : F.Faithful := (moduleULiftFullyFaithful R).faithful
  have : PreservesFiniteLimits F := preservesFiniteLimits_moduleULift (R := R)
  have := preservesFiniteColimits_moduleULift.{max u₁ v₁ w, w} (J := J) R
  have hlim : F.essImage.IsClosedUnderLimitsOfShape WalkingParallelPair := inferInstance
  have hcolim : F.essImage.IsClosedUnderColimitsOfShape WalkingParallelPair := inferInstance
  exact
    { exists_zero := ⟨_, F.map_isZero (isZero_zero _), F.obj_mem_essImage _⟩
      kernels_le := by
        rintro _ ⟨f, k, hk, hX, hY⟩
        exact F.essImage.prop_of_isLimit hk (by rintro (_ | _) <;> assumption)
      cokernels_le := by
        rintro _ ⟨f, k, hk, hX, hY⟩
        exact F.essImage.prop_of_isColimit hk (by rintro (_ | _) <;> assumption)
      prop_X₂_of_shortExact := by
        intro S hS h₁ h₃
        rw [moduleULift_essImage_iff] at h₁ h₃ ⊢
        intro U
        have := hS.mono_f
        have hex := hS.exact.map_of_mono_of_preservesKernel
          (_root_.SheafOfModules.evaluation R U) inferInstance inferInstance
        rw [ShortComplex.moduleCat_exact_iff] at hex
        exact AddMonoidHom.small_of_ker_le_range (S.f.val.app U).hom.toAddMonoidHom
          (S.g.val.app U).hom.toAddMonoidHom hex }

end WeakSerre

end Stacks.SheafOfModules

namespace SheafOfModules

variable {C : Type u₁} [Category.{v₁} C] {D : Type*} [Category D] (f : C ⥤ D)
  (J : GrothendieckTopology C) (K : GrothendieckTopology D) [f.IsContinuous J K]
  [f.IsCocontinuous J K] (O : Sheaf K RingCat.{w})

/-- **The direct image of a sheaf of modules with `z`-small sections has `z`-small sections**,
along a functor whose comma categories `StructuredArrow x f.op` are essentially `z`-small: its
sections over `x` are compatible families of sections indexed by that comma category. -/
theorem small_directImageOfEq_obj {T : Sheaf J RingCat.{w}}
    (hT : T = (f.sheafPushforwardContinuous RingCat.{w} J K).obj O)
    (N : SheafOfModules.{max u₁ _ t} T) [∀ X, Small.{z} (N.val.obj X)] (x : Dᵒᵖ)
    [EssentiallySmall.{z} (StructuredArrow x f.op)] :
    Small.{z} (((directImageOfEq.{w, t} f J K O hT).obj N).val.obj x) := by
  subst hT
  let G := StructuredArrow.proj x f.op ⋙ N.val.presheaf ⋙ CategoryTheory.forget AddCommGrpCat
  have : ∀ j, Small.{z} (G.obj j) := fun j ↦ inferInstanceAs (Small.{z} (N.val.obj j.right))
  have := G.small_sections_of_essentiallySmall
  exact small_of_injective (f := fun s ↦ (⟨fun j ↦ s.val j, fun {_ _} g ↦ s.property g⟩ :
      G.sections)) fun s s' h ↦ Subtype.ext (congrArg Subtype.val h)

end SheafOfModules
