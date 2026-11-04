module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.CategoryTheory.Sites.PreservesLocallyBijective
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafificationTensor
public import StacksCore.Tactic.StacksAttribute

/-!
# Restriction to a localization commutes with sheafification and with the tensor product

Let `(C, J)` be a site, let `O♯` be a sheaf of commutative rings on it and let `V` be an object
of `C`.  Restriction along `CategoryTheory.Over.forget V` carries a presheaf of `O♯`-modules on
`C` to a presheaf of modules on the localization `C/V`, and this file proves that it commutes
with the two constructions that the tensor product of sheaves of modules is built from:

* sheafification of presheaves of modules, and
* the objectwise tensor product.

Together these identify the restriction of a tensor product of two sheaves of modules with the
tensor product formed on the localized site.  That identification is the localization case of
Stacks 03EL, the statement that the inverse image of a morphism of ringed topoi commutes with
tensor products; it is what lets a local presentation of `F ⊗ G` be read off from local
presentations of `F` and of `G`, since quasi-coherence of a sheaf of modules on a site is a
statement about its restrictions to the members of a covering family.

## Main definitions

* `PresheafOfModules.overRestriction` is the restriction of a presheaf of modules to the
  localization of the site at an object.
* `PresheafOfModules.overRestrictionTensorObjIso` identifies the restriction of an objectwise
  tensor product with the objectwise tensor product of the restrictions.

## Main results

* `PresheafOfModules.sheafificationOverIso`: restriction to a localization commutes with
  sheafification of presheaves of modules.
* `PresheafOfModules.tensorSheafBifunctorOverIso`: the restriction of the tensor product of two
  sheaves of modules is the tensor product formed on the localized site.  This is the
  localization case of Stacks 03EL.

## Implementation notes

Both identifications are definitional objectwise and expensive as identifications of whole
structures: asking `rfl` for the equality of
`(overRestriction V).obj (tensorObj F G)` with
`tensorObj ((overRestriction V).obj F) ((overRestriction V).obj G)`
exhausts the default heartbeat budget at `whnf`, because the two sides reach the restriction maps
of the tensor product by different routes.  `overRestrictionTensorObjIso` performs the
identification pointwise instead, where over each object of `C/V` both sides are literally the
same `TensorProduct`, exactly as
`AlgebraicGeometry.tensorPresheafRestrictionIso` does for a ringed space.  No option overrides are
needed anywhere here.

`sheafificationOverIso` is proved by the universal property rather than by computing
sheafifications: the restriction of the sheafification unit is a morphism into a sheaf on `C/V`,
it is locally bijective because `CategoryTheory.Over.forget V` is cocontinuous
(`CategoryTheory.Presheaf.isLocallyInjective_whisker` and
`CategoryTheory.Presheaf.isLocallySurjective_whisker`), and a locally bijective morphism into a
sheaf exhibits its target as a sheafification.  The same argument appears, for the Zariski site
of a ringed space, inside `AlgebraicGeometry.tensorRestrictionIso`.

The sheafification hypotheses are asked for on every localization of `J`, which is how
`SheafOfModules.QuasicoherentData` asks for them as well.

## References

* [Stacks Project, Tag 03EL](https://stacks.math.columbia.edu/tag/03EL)
* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf

universe v u w z z₁

namespace PresheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  {Osharp : Sheaf J CommRingCat.{w}} (V : C)

/-- Restriction of a presheaf of modules to the localization of the site at an object: the
pushforward along `CategoryTheory.Over.forget V`, with the structure presheaf of the
localization as new coefficients.  On sections it forgets nothing — the value at an object
`T ⟶ V` of `C/V` is the value at `T`. -/
public noncomputable def overRestriction :
    PresheafOfModules.{z} (Osharp.obj ⋙ forget₂ CommRingCat RingCat) ⥤
      PresheafOfModules.{z} ((Osharp.over V).obj ⋙ forget₂ CommRingCat RingCat) :=
  PresheafOfModules.pushforward (F := Over.forget V)
    (𝟙 ((Osharp.over V).obj ⋙ forget₂ CommRingCat RingCat))

/-- The restriction of an objectwise tensor product of two presheaves of modules is the
objectwise tensor product of their restrictions. -/
public noncomputable def overRestrictionTensorObjIso
    (F : PresheafOfModules.{z} (Osharp.obj ⋙ forget₂ CommRingCat RingCat))
    (G : PresheafOfModules.{z₁} (Osharp.obj ⋙ forget₂ CommRingCat RingCat)) :
    (overRestriction (Osharp := Osharp) V).obj (tensorObj F G) ≅
      tensorObj ((overRestriction V).obj F) ((overRestriction V).obj G) :=
  isoMk (fun _ => Iso.refl _)

section Sheafification

variable [J.WEqualsLocallyBijective AddCommGrpCat.{z}] [HasWeakSheafify J AddCommGrpCat.{z}]
  [∀ X : C, HasWeakSheafify (J.over X) AddCommGrpCat.{z}]
  [∀ X : C, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{z}]

/-- **Restriction to a localization commutes with sheafification of presheaves of modules.**
The restriction to `C/V` of the sheaf of modules associated with a presheaf of modules on `C` is
the sheaf of modules associated with the restriction. -/
public noncomputable def sheafificationOverIso
    (P : PresheafOfModules.{z} (toRingCat J Osharp).obj) :
    ((sheafification (𝟙 (toRingCat J Osharp).obj)).obj P).over V ≅
      (sheafification (𝟙 ((toRingCat J Osharp).over V).obj)).obj
        ((overRestriction (Osharp := Osharp) V).obj P) := by
  let R := toRingCat J Osharp
  let JV := J.over V
  let RV := R.over V
  let Pv := (overRestriction (Osharp := Osharp) V).obj P
  let M := ((sheafification (𝟙 R.obj)).obj P).over V
  let unitP := (sheafificationAdjunction (𝟙 R.obj)).unit.app P
  let forgetMap := SheafOfModules.forget RV ⋙ restrictScalars (𝟙 RV.obj)
  let γ : Pv ⟶ forgetMap.obj M := (overRestriction V).map unitP
  let adj := sheafificationAdjunction (𝟙 RV.obj)
  let e : (sheafification (𝟙 RV.obj)).obj Pv ⟶ M := (adj.homEquiv Pv M).symm γ
  let η := adj.unit.app Pv
  let toAb := toPresheaf RV.obj
  let toAbJ := toPresheaf R.obj
  have hecomp : η ≫ forgetMap.map e = γ :=
    (adj.homEquiv_unit (f := e)).symm.trans ((adj.homEquiv Pv M).apply_symm_apply γ)
  have hwhisk : toAb.map γ = Functor.whiskerLeft (Over.forget V).op (toAbJ.map unitP) := rfl
  have hγI : Presheaf.IsLocallyInjective JV (toAb.map γ) := by
    rw [hwhisk]
    exact Presheaf.isLocallyInjective_whisker JV J (Over.forget V) _
  have hγS : Presheaf.IsLocallySurjective JV (toAb.map γ) := by
    rw [hwhisk]
    exact Presheaf.isLocallySurjective_whisker JV J (Over.forget V) _
  have hηW : JV.W (toAb.map η) := by
    change JV.W (CategoryTheory.toSheafify JV Pv.presheaf)
    exact JV.W_toSheafify Pv.presheaf
  have hηIso : IsIso ((presheafToSheaf JV AddCommGrpCat).map (toAb.map η)) := (JV.W_iff _).mp hηW
  have hγIso : IsIso ((presheafToSheaf JV AddCommGrpCat).map (toAb.map γ)) :=
    (JV.W_iff _).mp ((JV.W_iff_isLocallyBijective _).2 ⟨hγI, hγS⟩)
  have hcompAb : toAb.map η ≫ toAb.map e.val = toAb.map γ := by
    change toAb.map (η ≫ e.val) = toAb.map γ
    convert congrArg toAb.map hecomp using 1
    rfl
  have heMapIso : IsIso ((presheafToSheaf JV AddCommGrpCat).map (toAb.map e.val)) := by
    have : IsIso ((presheafToSheaf JV AddCommGrpCat).map (toAb.map η) ≫
        (presheafToSheaf JV AddCommGrpCat).map (toAb.map e.val)) := by
      rw [← Functor.map_comp, hcompAb]
      exact hγIso
    exact IsIso.of_isIso_comp_left ((presheafToSheaf JV AddCommGrpCat).map (toAb.map η))
      ((presheafToSheaf JV AddCommGrpCat).map (toAb.map e.val))
  have heIso : IsIso e :=
    (isIso_iff_of_reflects_iso e (SheafOfModules.toSheaf RV)).mp
      ((JV.W_sheafToPresheaf_map_iff_isIso _).1 ((JV.W_iff _).2 heMapIso))
  exact (asIso e).symm

end Sheafification

section Tensor

variable [J.WEqualsLocallyBijective AddCommGrpCat.{max z z₁}]
  [HasWeakSheafify J AddCommGrpCat.{max z z₁}]
  [∀ X : C, HasWeakSheafify (J.over X) AddCommGrpCat.{max z z₁}]
  [∀ X : C, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{max z z₁}]
  [∀ X : C, (J.over X).HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]

/-- **Stacks 03EL, for the localization of a site at an object.**  The restriction to `C/V` of
the tensor product of two sheaves of modules on `C` is the tensor product, formed on `C/V`, of
their restrictions. -/
public noncomputable def tensorSheafBifunctorOverIso
    (F : SheafOfModules.{z} (toRingCat J Osharp))
    (G : SheafOfModules.{z₁} (toRingCat J Osharp)) :
    (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, z, z₁} Osharp).obj F).obj G).over V ≅
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{max u v, v, w, z, z₁} (Osharp.over V)).obj (F.over
          V)).obj (G.over V) :=
  sheafificationOverIso V (tensorObj F.val G.val) ≪≫
    (sheafification (𝟙 ((toRingCat J Osharp).over V).obj)).mapIso
      (overRestrictionTensorObjIso V F.val G.val)

end Tensor

end PresheafOfModules

end
