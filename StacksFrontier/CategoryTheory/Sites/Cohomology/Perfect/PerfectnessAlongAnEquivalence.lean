module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InternalHomSiteEquivalenceAnyUniverse
public import StacksFrontier.Algebra.Homology.StrictlyPerfectApproximationLocal
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.PerfectnessAlongAnExactFunctor

/-!
# Perfectness along an equivalence of ringed sites

Let `e : C ≌ D` be an equivalence of sites between the underlying sites of two ringed sites
`(C, O_C)` and `(D, O_D)`, continuous in both directions, together with an isomorphism of sheaves
of rings `ρ : O_C ⟶ e_* O_D`. Pushforward along `ρ` is an equivalence
`Mod(O_D) ≌ Mod(O_C)`, and this file shows that the induced equivalence of derived categories
carries perfect objects (Stacks 08G5) to perfect objects. The object and morphism universes of the
two sites are independent; only the universe of the sections of the structure sheaves is shared.

## Main definitions

* `AlgebraicGeometry.RingedSite.pushforwardEquivalenceOfIsIso`: the equivalence
  `Mod(O_D) ≌ Mod(O_C)`.
* `AlgebraicGeometry.RingedSite.pushforwardEquivalenceOfIsIsoOver`: its localization at an object.

## Main results

* `AlgebraicGeometry.RingedSite.isPerfect_mapDerivedCategory_pushforwardEquivalenceOfIsIso`:
  perfectness is carried across the equivalence.

## Implementation notes

The transfer is `AlgebraicGeometry.RingedSite.isPerfect_mapDerivedCategory_of_hypotheses` along the
inverse `e⁻¹ : D ⥤ C`, whose images cover `C`; the slice factors are the localized equivalences of
module categories `Stacks.SheafOfModules.InternalHom.AnyUniverse.siteEquivModulesOver` for the
inverse equivalence of sites, and the localization squares commute on the nose.

## References

* [Stacks Project, Tag 08G5](https://stacks.math.columbia.edu/tag/08G5)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe uX vX uY vY w dX dY

namespace AlgebraicGeometry.RingedSite

open Stacks.SheafOfModules.InternalHom

variable {X : RingedSite.{uX, vX, w}} {Y : RingedSite.{uY, vY, w}}
  (eqv : X.C ≌ Y.C) [hfun : eqv.functor.IsContinuous X.J Y.J]
  [hinv : eqv.inverse.IsContinuous Y.J X.J]
  (ρ : (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ⟶
    (eqv.functor.sheafPushforwardContinuous RingCat.{w} X.J Y.J).obj
      (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
  [hρ : IsIso ρ]

/-- A presheaf of rings sends an isomorphism and its inverse to mutually inverse maps. -/
private theorem map_op_hom_map_op_inv_apply {C : Type*} [Category C] (F : Cᵒᵖ ⥤ RingCat)
    {a b : C} (e : a ≅ b) (x : F.obj (op a)) : F.map e.hom.op (F.map e.inv.op x) = x := by
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp]
  simp

/-- The first compatibility of `pushforwardPushforwardEquivalence` for the inverse equivalence of
sites, with structure maps `AnyUniverse.psiOfIso eqv ρ` and `ρ`. -/
theorem pushforward_symm_counit :
    Functor.whiskerRight (NatTrans.op eqv.symm.counit)
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj =
      ρ.hom ≫ eqv.symm.inverse.op.whiskerLeft (AnyUniverse.psiOfIso eqv ρ).hom := by
  ext W x
  have key : ∀ y, (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.map (eqv.unit.app W.unop).op
      ((AnyUniverse.psiOfIso eqv ρ).hom.app (op (eqv.functor.obj W.unop)) (ρ.hom.app W y)) = y :=
    fun y =>
    ConcreteCategory.congr_hom (NatTrans.congr_app (AnyUniverse.psiOfIso_unit eqv ρ) W) y
  have inj : Function.Injective
      ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.map (eqv.unit.app W.unop).op) :=
    (ConcreteCategory.bijective_of_isIso _).1
  apply inj
  refine Eq.trans ?_ (key x).symm
  exact map_op_hom_map_op_inv_apply _ (eqv.unitIso.app W.unop) x

/-- The second compatibility of `pushforwardPushforwardEquivalence` for the inverse equivalence of
sites, with structure maps `AnyUniverse.psiOfIso eqv ρ` and `ρ`. -/
theorem pushforward_symm_unit :
    (AnyUniverse.psiOfIso eqv ρ).hom ≫ eqv.symm.functor.op.whiskerLeft ρ.hom ≫
      Functor.whiskerRight (NatTrans.op eqv.symm.unit)
          (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj =
        𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj := by
  ext V x
  have key : ∀ y,
      (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj.map (eqv.counit.app V.unop).op y =
      ρ.hom.app (op (eqv.inverse.obj V.unop)) ((AnyUniverse.psiOfIso eqv ρ).hom.app V y) := fun y =>
    ConcreteCategory.congr_hom (NatTrans.congr_app (AnyUniverse.psiOfIso_counit eqv ρ) V) y
  change (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj.map (eqv.counitInv.app V.unop).op
    (ρ.hom.app (op (eqv.inverse.obj V.unop)) ((AnyUniverse.psiOfIso eqv ρ).hom.app V x)) = x
  rw [← key]
  exact map_op_hom_map_op_inv_apply _ (eqv.counitIso.app V.unop).symm x

/-- The pushforward along an equivalence of sites with an invertible structure map, as an
equivalence of the categories of sheaves of modules. -/
abbrev pushforwardEquivalenceOfIsIso :
    SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) ≌
      SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) :=
  SheafOfModules.pushforwardPushforwardEquivalence eqv ρ (AnyUniverse.psiOfIso eqv ρ)
    (AnyUniverse.psiOfIso_counit eqv ρ) (AnyUniverse.psiOfIso_unit eqv ρ)

/-- The pushforward along an equivalence of ringed sites is additive. -/
instance pushforwardEquivalenceOfIsIso_functor_additive :
    (pushforwardEquivalenceOfIsIso eqv ρ).functor.Additive :=
  Functor.additive_of_preserves_binary_products _

/-- The functor of the inverse equivalence of sites is continuous. -/
instance pushforwardEquivalenceOfIsIso_symm_functor_isContinuous :
    eqv.symm.functor.IsContinuous Y.J X.J :=
  inferInstanceAs (eqv.inverse.IsContinuous Y.J X.J)

/-- The inverse of the inverse equivalence of sites is continuous. -/
instance pushforwardEquivalenceOfIsIso_symm_inverse_isContinuous :
    eqv.symm.inverse.IsContinuous X.J Y.J :=
  inferInstanceAs (eqv.functor.IsContinuous X.J Y.J)

/-- The equivalence of slices `Mod(O_X|_{e⁻¹ W}) ≌ Mod(O_Y|_W)` localizing
`pushforwardEquivalenceOfIsIso` at an object `W` of `Y`. -/
abbrev pushforwardEquivalenceOfIsIsoOver (W : Y.C) :
    SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over (eqv.inverse.obj W)) ≌
      SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O).over W) :=
  AnyUniverse.siteEquivModulesOver (X := X) (Y := Y) eqv.symm (AnyUniverse.psiOfIso eqv ρ) ρ
    (pushforward_symm_counit eqv ρ) (pushforward_symm_unit eqv ρ) W

variable [∀ U : X.C, HasSheafify (X.J.over U) AddCommGrpCat.{w}]
  [∀ U : X.C, (X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{w}]
  [∀ W : Y.C, HasSheafify (Y.J.over W) AddCommGrpCat.{w}]
  [∀ W : Y.C, (Y.J.over W).WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasSheafify Y.J AddCommGrpCat.{w}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasDerivedCategory.{dY} (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))]
  [HasDerivedCategory.{dX} (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))]

/-- **Perfectness is invariant under an equivalence of ringed sites.** The derived functor of the
pushforward along an equivalence of sites with an invertible structure map carries a perfect
object of `D(O_D)` to a perfect object of `D(O_C)`. -/
theorem isPerfect_mapDerivedCategory_pushforwardEquivalenceOfIsIso
    (K : DerivedCategory (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)))
    (hK : Y.IsPerfect K) :
    X.IsPerfect ((pushforwardEquivalenceOfIsIso eqv ρ).functor.mapDerivedCategory.obj K) := by
  have hψ : ∀ W : Y.C,
      IsIso (AnyUniverse.siteEquivPsiOver (X := X) (Y := Y) eqv.symm ρ W) := fun W => by
    have : IsIso ((sheafToPresheaf _ _).map
        (AnyUniverse.siteEquivPsiOver (X := X) (Y := Y) eqv.symm ρ W)) :=
      inferInstanceAs (IsIso (Functor.whiskerLeft (Over.forget (eqv.symm.functor.obj W)).op ρ.hom))
    exact isIso_of_reflects_iso _ (sheafToPresheaf _ _)
  have hη : ∀ W : Y.C, IsIso (SheafOfModules.unitToPushforwardObjUnit
      (AnyUniverse.siteEquivPsiOver (X := X) (Y := Y) eqv.symm ρ W)) := fun W =>
    have := hψ W
    Stacks.SheafOfModules.isIso_unitToPushforwardObjUnit _
  have hTop : X.J.CoversTop eqv.inverse.obj := fun U =>
    X.J.superset_covering (fun V f _ => ⟨eqv.functor.obj U, ⟨f ≫ eqv.unit.app U⟩⟩) (X.J.top_mem U)
  exact isPerfect_mapDerivedCategory_of_hypotheses (X := X) (Y := Y) eqv.inverse
    (pushforwardEquivalenceOfIsIso eqv ρ).functor
    (fun W => (pushforwardEquivalenceOfIsIsoOver eqv ρ W).inverse)
    inferInstance inferInstance inferInstance
    (fun W => Functor.additive_of_preserves_binary_products _)
    (fun W => inferInstance) (fun W => inferInstance) inferInstance hTop
    (fun W => (@asIso _ _ _ _ _ (hη W)).symm)
    (fun W => Iso.refl _) K hK

end AlgebraicGeometry.RingedSite

end
