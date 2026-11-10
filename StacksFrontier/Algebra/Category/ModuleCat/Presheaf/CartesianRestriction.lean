module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Colimits
public import Mathlib.CategoryTheory.Adjunction.Limits
public import StacksCore.Tactic.StacksAttribute

/-!
# Cartesian presheaves of modules: the base-change comparison of a restriction map

Let `R` be a presheaf of commutative rings on a category `C` and let `M` be a presheaf of
modules over the underlying presheaf of rings.  For a morphism `f : X ⟶ Y` of `Cᵒᵖ` the
restriction map `M X ⟶ M Y` is semilinear over `R X ⟶ R Y`, so it has an adjoint transpose

`R Y ⊗[R X] M X ⟶ M Y`,

the *base-change comparison* of the restriction map.  The presheaf `M` is *cartesian* over `f`
exactly when this comparison is an isomorphism; that condition is clause (1) of the
characterization of quasi-coherence on the affine étale site, Stacks 0H04.  This file sets up
the comparison, its elementary properties, and the two stability statements a presentation
argument needs: the comparison of a colimit of presheaves of modules is an isomorphism when each
comparison in the diagram is, and the comparison of the structure presheaf with its sections
raised to a larger universe is always an isomorphism.

## Main definitions

* `Stacks.PresheafOfModules.restrictionBaseChange`: the base-change comparison of a restriction
  map.
* `Stacks.PresheafOfModules.restrictionBaseChangeNatTrans`: the comparison as a natural
  transformation in the presheaf of modules.
* `Stacks.PresheafOfModules.restrictionTensorEquiv`: the comparison as an equivalence of types,
  when it is an isomorphism.
* `Stacks.PresheafOfModules.largeUnit`: the structure presheaf with its sections raised to a
  larger universe, as a presheaf of modules over itself, and
  `Stacks.PresheafOfModules.largeUnitBaseChangeEquiv` its base-change comparison, computed.

## Main results

* `Stacks.PresheafOfModules.restrictionBaseChange_tmul` and
  `Stacks.PresheafOfModules.restrictionBaseChange_one_tmul`: the comparison on a pure tensor.
* `Stacks.PresheafOfModules.restrictionBaseChange_naturality`: naturality in the presheaf of
  modules.
* `Stacks.PresheafOfModules.isIso_restrictionBaseChange_of_iso`: being cartesian over `f` is
  invariant under isomorphism of presheaves of modules.
* `Stacks.PresheafOfModules.isIso_restrictionBaseChange_colimit`: the comparison of a colimit.
* `Stacks.PresheafOfModules.isIso_restrictionBaseChange_largeUnit`: the structure presheaf with
  raised sections is cartesian over every morphism.

## Implementation notes

The comparison is the adjoint transpose under `ModuleCat.extendRestrictScalarsAdj`, so it is the
canonical tensor-product comparison and not an arbitrary map; `restrictionBaseChange_tmul` pins
it down on pure tensors, and everything else is deduced from that identity rather than by
unfolding the adjunction again.

The colimit statement is obtained by whiskering `restrictionBaseChangeNatTrans` along the
diagram and using that evaluation of presheaves of modules preserves colimits, so that an
objectwise isomorphism of natural transformations between colimit-preserving functors is an
isomorphism at the colimit.

## References

* [Stacks Project, Tag 0H04](https://stacks.math.columbia.edu/tag/0H04)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v r m t w

namespace Stacks.PresheafOfModules

variable {C : Type u} [Category.{v} C] {R : Cᵒᵖ ⥤ CommRingCat.{r}}

/-- The base-change comparison `R Y ⊗[R X] M X ⟶ M Y` of the restriction map of a presheaf of
modules along `f : X ⟶ Y`, that is, the adjoint transpose of the semilinear restriction map. -/
noncomputable abbrev restrictionBaseChange
    (M : PresheafOfModules.{max m r} (R ⋙ forget₂ CommRingCat RingCat))
    {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    (ModuleCat.extendScalars (R.map f).hom).obj (M.obj X) ⟶ M.obj Y :=
  ((ModuleCat.extendRestrictScalarsAdj (R.map f).hom).homEquiv _ _).symm (M.map f)

open scoped ChangeOfRings in
/-- The base-change comparison sends `1 ⊗ₜ x` to the restriction of `x`. -/
theorem restrictionBaseChange_one_tmul
    (M : PresheafOfModules.{max m r} (R ⋙ forget₂ CommRingCat RingCat))
    {X Y : Cᵒᵖ} (f : X ⟶ Y) (x : M.obj X) :
    (restrictionBaseChange M f)
      ((1 : R.obj Y) ⊗ₜ[R.obj X, (R.map f).hom] x) = M.map f x :=
  congrArg (fun a => a x)
    (((ModuleCat.extendRestrictScalarsAdj (R.map f).hom).homEquiv _ _).apply_symm_apply (M.map f))

open scoped ChangeOfRings in
/-- The base-change comparison sends `a ⊗ₜ x` to `a` acting on the restriction of `x`. -/
theorem restrictionBaseChange_tmul
    (M : PresheafOfModules.{max m r} (R ⋙ forget₂ CommRingCat RingCat))
    {X Y : Cᵒᵖ} (f : X ⟶ Y) (a : R.obj Y) (x : M.obj X) :
    restrictionBaseChange M f (a ⊗ₜ[R.obj X, (R.map f).hom] x) = a • M.map f x :=
  (congrArg (fun c => (restrictionBaseChange M f).hom
      (c ⊗ₜ[R.obj X, (R.map f).hom] x)) (mul_one a).symm).trans
    (((restrictionBaseChange M f).hom.map_smul a
        ((1 : R.obj Y) ⊗ₜ[R.obj X, (R.map f).hom] x)).trans
      (congrArg (fun z => a • z) (restrictionBaseChange_one_tmul M f x)))

/-- The base-change comparison is natural in the presheaf of modules. -/
theorem restrictionBaseChange_naturality
    {M N : PresheafOfModules.{max m r} (R ⋙ forget₂ CommRingCat RingCat)}
    (a : M ⟶ N) {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    (ModuleCat.extendScalars (R.map f).hom).map (a.app X) ≫
        restrictionBaseChange N f = restrictionBaseChange M f ≫ a.app Y := by
  let adj := ModuleCat.extendRestrictScalarsAdj (R.map f).hom
  exact (adj.homEquiv_naturality_left_symm (a.app X) (N.map f)).symm.trans
    ((congrArg ((adj.homEquiv _ _).symm) (a.naturality f).symm).trans
      (adj.homEquiv_naturality_right_symm (M.map f) (a.app Y)))

/-- Being cartesian over `f` transfers along an isomorphism of presheaves of modules. -/
theorem isIso_restrictionBaseChange_of_iso
    {M N : PresheafOfModules.{max m r} (R ⋙ forget₂ CommRingCat RingCat)}
    (e : M ≅ N) {X Y : Cᵒᵖ} (f : X ⟶ Y)
    [IsIso (restrictionBaseChange M f)] : IsIso (restrictionBaseChange N f) := by
  have : ∀ Z, IsIso (e.hom.app Z) := fun Z =>
    ((PresheafOfModules.evaluation _ Z).mapIso e).isIso_hom
  have : IsIso ((ModuleCat.extendScalars (R.map f).hom).map (e.hom.app X) ≫
      restrictionBaseChange N f) := by
    rw [restrictionBaseChange_naturality e.hom f]
    infer_instance
  exact IsIso.of_isIso_comp_left ((ModuleCat.extendScalars (R.map f).hom).map (e.hom.app X)) _

/-! ### The comparison as an equivalence of types -/

/-- When the base-change comparison along `f` is an isomorphism, it is an equivalence of types
`R Y ⊗[R X] M X ≃ M Y`.  The ring map is supplied explicitly so that the algebra structure on
the sections is the intended one. -/
noncomputable def restrictionTensorEquiv
    (M : PresheafOfModules.{max m r} (R ⋙ forget₂ CommRingCat RingCat))
    {X Y : Cᵒᵖ} (f : X ⟶ Y) [IsIso (restrictionBaseChange M f)]
    (a : R.obj X ⟶ R.obj Y) (ha : R.map f = a) :
    letI : Algebra (R.obj X) (R.obj Y) := a.hom.toAlgebra
    TensorProduct (R.obj X) (R.obj Y) (M.obj X) ≃ M.obj Y := by
  subst a
  exact (CategoryTheory.Iso.toLinearEquiv (asIso (restrictionBaseChange M f))).toEquiv

/-- `Stacks.PresheafOfModules.restrictionTensorEquiv` on a pure tensor. -/
theorem restrictionTensorEquiv_tmul
    (M : PresheafOfModules.{max m r} (R ⋙ forget₂ CommRingCat RingCat))
    {X Y : Cᵒᵖ} (f : X ⟶ Y) [IsIso (restrictionBaseChange M f)]
    (a : R.obj X ⟶ R.obj Y) (ha : R.map f = a) (c : R.obj Y) (x : M.obj X) :
    letI : Algebra (R.obj X) (R.obj Y) := a.hom.toAlgebra
    restrictionTensorEquiv M f a ha (TensorProduct.tmul (R.obj X) c x) = c • M.map f x := by
  subst a
  exact restrictionBaseChange_tmul M f c x

/-- `Stacks.PresheafOfModules.restrictionTensorEquiv` is additive. -/
theorem restrictionTensorEquiv_add
    (M : PresheafOfModules.{max m r} (R ⋙ forget₂ CommRingCat RingCat))
    {X Y : Cᵒᵖ} (f : X ⟶ Y) [IsIso (restrictionBaseChange M f)]
    (a : R.obj X ⟶ R.obj Y) (ha : R.map f = a) :
    letI : Algebra (R.obj X) (R.obj Y) := a.hom.toAlgebra
    ∀ x y, restrictionTensorEquiv M f a ha (x + y) =
      restrictionTensorEquiv M f a ha x + restrictionTensorEquiv M f a ha y := by
  subst a
  exact fun x y => map_add (restrictionBaseChange M f).hom x y

/-- `Stacks.PresheafOfModules.restrictionTensorEquiv` sends `0` to `0`. -/
theorem restrictionTensorEquiv_zero
    (M : PresheafOfModules.{max m r} (R ⋙ forget₂ CommRingCat RingCat))
    {X Y : Cᵒᵖ} (f : X ⟶ Y) [IsIso (restrictionBaseChange M f)]
    (a : R.obj X ⟶ R.obj Y) (ha : R.map f = a) :
    letI : Algebra (R.obj X) (R.obj Y) := a.hom.toAlgebra
    restrictionTensorEquiv M f a ha 0 = 0 := by
  subst a
  exact map_zero (restrictionBaseChange M f).hom

/-! ### Stability of the cartesian condition -/

/-- The base-change comparison along `f`, as a natural transformation of functors on presheaves
of modules. -/
noncomputable def restrictionBaseChangeNatTrans
    (R : Cᵒᵖ ⥤ CommRingCat.{r}) {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    (PresheafOfModules.evaluation (R ⋙ forget₂ CommRingCat RingCat) X :
      PresheafOfModules.{max r m} _ ⥤ _) ⋙
        ModuleCat.extendScalars (R := R.obj X) (S := R.obj Y) (R.map f).hom ⟶
      PresheafOfModules.evaluation (R ⋙ forget₂ CommRingCat RingCat) Y where
  app M := restrictionBaseChange (R := R) M f
  naturality _ _ a := restrictionBaseChange_naturality (R := R) a f

/-- **A colimit of cartesian presheaves of modules is cartesian.** -/
theorem isIso_restrictionBaseChange_colimit
    (R : Cᵒᵖ ⥤ CommRingCat.{r})
    {D : Type t} [Category.{w} D]
    (K : D ⥤ PresheafOfModules.{max m r} (R ⋙ forget₂ CommRingCat RingCat))
    (c : Cocone K) (hc : IsColimit c)
    [HasColimitsOfShape D AddCommGrpCat.{max m r}]
    {X Y : Cᵒᵖ} (f : X ⟶ Y)
    (h : ∀ i, IsIso (restrictionBaseChange (K.obj i) f)) :
    IsIso (restrictionBaseChange c.pt f) := by
  let a : (PresheafOfModules.evaluation (R ⋙ forget₂ CommRingCat RingCat) X :
      PresheafOfModules.{max m r} _ ⥤ _) ⋙
        ModuleCat.extendScalars (R := R.obj X) (S := R.obj Y) (R.map f).hom ⟶
      PresheafOfModules.evaluation (R ⋙ forget₂ CommRingCat RingCat) Y :=
    restrictionBaseChangeNatTrans.{u, v, r, m} R f
  have : ∀ i : D, IsIso ((Functor.whiskerLeft K a).app i) := h
  have : IsIso (Functor.whiskerLeft K a) := NatIso.isIso_of_isIso_app _
  have : ∀ Z, PreservesColimitsOfShape D
      (PresheafOfModules.evaluation (R ⋙ forget₂ CommRingCat RingCat) Z :
        PresheafOfModules.{max m r} _ ⥤ _) :=
    fun Z => PresheafOfModules.evaluation_preservesColimitsOfShape _ _ _
  have : PreservesColimitsOfSize.{w, t}
      (ModuleCat.extendScalars.{r, r, max m r} (R := R.obj X) (S := R.obj Y) (R.map f).hom) :=
    (ModuleCat.extendRestrictScalarsAdj (R.map f).hom).leftAdjoint_preservesColimits
  exact isIso_app_coconePt_of_preservesColimit K a c hc

/-- The structure presheaf of commutative rings, read as a presheaf of modules over itself with
its sections raised to a larger universe. -/
noncomputable def largeUnit (R : Cᵒᵖ ⥤ CommRingCat.{r}) :
    PresheafOfModules.{max r m} (R ⋙ forget₂ CommRingCat RingCat) where
  obj X := ModuleCat.of (R.obj X) (ULift.{m} (R.obj X))
  map {X Y} f := ModuleCat.ofHom (Y := (ModuleCat.restrictScalars (R.map f).hom).obj
    (ModuleCat.of (R.obj Y) (ULift.{m} (R.obj Y)))) {
    toFun := fun x => ULift.up ((R.map f).hom x.down)
    map_add' := fun x y => congrArg ULift.up (map_add _ _ _)
    map_smul' := fun a x => congrArg ULift.up (map_mul _ _ _) }
  map_id X := by
    ext x
    change ULift.up ((R.map (𝟙 X)).hom x.down) =
      (ModuleCat.restrictScalarsId'App _ (by simp) _).inv x
    rw [ModuleCat.restrictScalarsId'App_inv_apply]
    simp
  map_comp f g := by
    ext x
    simp
    rfl

open scoped ChangeOfRings in
/-- The base change of `Stacks.PresheafOfModules.largeUnit` along a restriction map, computed:
the base change of a free module of rank one is free of rank one, so
`R Y ⊗[R X] ULift (R X)` is `R Y`-linearly `ULift (R Y)`. -/
noncomputable def largeUnitBaseChangeEquiv (R : Cᵒᵖ ⥤ CommRingCat.{r}) {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    letI : Algebra (R.obj X) (R.obj Y) := (R.map f).hom.toAlgebra
    (TensorProduct (R.obj X) (R.obj Y) (ULift.{m} (R.obj X))) ≃ₗ[R.obj Y]
      ULift.{m} (R.obj Y) := by
  letI : Algebra (R.obj X) (R.obj Y) := (R.map f).hom.toAlgebra
  exact (TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl (R.obj Y) (R.obj Y))
      (ULift.moduleEquiv (R := R.obj X) (M := R.obj X))).trans
    ((TensorProduct.AlgebraTensorModule.rid (R.obj X) (R.obj Y) (R.obj Y)).trans
      (ULift.moduleEquiv).symm)

open scoped ChangeOfRings in
/-- `Stacks.PresheafOfModules.largeUnitBaseChangeEquiv` on a pure tensor. -/
theorem largeUnitBaseChangeEquiv_tmul (R : Cᵒᵖ ⥤ CommRingCat.{r}) {X Y : Cᵒᵖ} (f : X ⟶ Y)
    (s : R.obj Y) (x : ULift.{m} (R.obj X)) :
    letI : Algebra (R.obj X) (R.obj Y) := (R.map f).hom.toAlgebra
    largeUnitBaseChangeEquiv.{u, v, r, m} R f (s ⊗ₜ[R.obj X] x)
      = ULift.up (s * (R.map f).hom x.down) := by
  let : Algebra (R.obj X) (R.obj Y) := (R.map f).hom.toAlgebra
  simp only [largeUnitBaseChangeEquiv, LinearEquiv.trans_apply,
    TensorProduct.AlgebraTensorModule.congr_tmul, LinearEquiv.refl_apply,
    ULift.moduleEquiv_apply, TensorProduct.AlgebraTensorModule.rid_tmul, Algebra.smul_def,
    ULift.moduleEquiv_symm_apply, ULift.up.injEq]
  exact mul_comm _ _

open scoped ChangeOfRings in
/-- **The structure presheaf with raised sections is cartesian over every morphism.**  The
base-change comparison is `Stacks.PresheafOfModules.largeUnitBaseChangeEquiv`, which it agrees
with on pure tensors. -/
theorem isIso_restrictionBaseChange_largeUnit
    (R : Cᵒᵖ ⥤ CommRingCat.{r}) {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    IsIso (restrictionBaseChange (largeUnit.{u, v, r, m} R) f) := by
  let : Algebra (R.obj X) (R.obj Y) := (R.map f).hom.toAlgebra
  have h : restrictionBaseChange (largeUnit.{u, v, r, m} R) f =
      ModuleCat.ofHom (largeUnitBaseChangeEquiv.{u, v, r, m} R f).toLinearMap := by
    refine ModuleCat.hom_ext (LinearMap.ext fun z => ?_)
    induction z using TensorProduct.inductionOn with
    | add z w hz hw =>
      exact ((map_add _ z w).trans (congrArg₂ (· + ·) hz hw)).trans (map_add _ z w).symm
    | tmul s x =>
      exact (restrictionBaseChange_tmul (largeUnit.{u, v, r, m} R) f s x).trans
        (largeUnitBaseChangeEquiv_tmul.{u, v, r, m} R f s x).symm
  rw [h]
  exact (LinearEquiv.toModuleIso (largeUnitBaseChangeEquiv.{u, v, r, m} R f)).isIso_hom

end Stacks.PresheafOfModules

end
