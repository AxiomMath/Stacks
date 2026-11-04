module

public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.RightAdjointHigherDirectImage
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.FlatBaseChangeSheafAffineSections
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleAffinePushforward
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.HigherDirectImageFlatBaseChangeSheafRule

/-!
# The direct image along a 1-morphism of affine schemes is cartesian between affine objects

Let `f : X ⟶ Y` be a 1-morphism between the algebraic stacks represented by objects `X`, `Y` of the
big fppf site lying over affine schemes. Its functor has the right adjoint `G = - ×_Y X`
(`AlgebraicGeometry.Stack.schemeStackAdjunction`), and the direct image of an étale sheaf of
modules `ℱ` is `(f_*ℱ)(y) = ℱ(G y)`
(`AlgebraicGeometry.Stack.moduleSheafPushforwardIsoOfRightAdjoint`).

## Main results

* `AlgebraicGeometry.Stack.isPullback_schemeStackAdjunction_counit`: for an arrow `φ : y' ⟶ y`,
  the square of `G y' ⟶ G y` over `φ` formed by the two counits is cartesian.
* `AlgebraicGeometry.Stack.bijective_restrictionBaseChange_pushforward_schemeStack`: for `φ`
  between objects lying over affine schemes, the base-change comparison of `f_*ℱ` along `φ` is
  bijective as soon as that of `ℱ` along `G φ` is.
* `AlgebraicGeometry.Stack.locallyQuasicoherentFlatBaseChangeSheafRule_pushforward_schemeStack`:
  `f_*ℱ` is in `LQCoh^fbc` when `ℱ` is.

## References

* [Stacks Project, Tag 0765](https://stacks.math.columbia.edu/tag/0765)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u t

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section SchemeStack

variable {X Y : BigFppfOver B S hS}

/-- **The counit square of the base-change adjunction is cartesian.** For an arrow `φ : y' ⟶ y`
of `Sch/Y`, the square formed by `f(G φ)`, the two counits and `φ` is a pullback square of the
underlying objects: it is the square of `y' ×_Y X ⟶ y ×_Y X` over `y' ⟶ y`, up to the
identification of the functor of `f` with postcomposition. -/
theorem isPullback_schemeStackAdjunction_counit
    (f : schemeStack.{u, t} B S hS X ⟶ schemeStack.{u, t} B S hS Y) {y' y : Over Y}
    (φ : y' ⟶ y) :
    IsPullback ((CatFiberedInGroupoids.homFunctor f.hom).map
        ((Over.pullback (schemeMapOfFunctor B S hS f.hom.hom)).map φ)).left
      ((schemeStackAdjunction B S hS f).counit.app y').left
      ((schemeStackAdjunction B S hS f).counit.app y).left φ.left := by
  let c := schemeMapOfFunctor B S hS f.hom.hom
  let β := basedFunctorIsoOverMap B S hS f.hom.hom
  have he : ∀ z : Over Y, β.inv.app ((Over.pullback c).obj z) ≫
      β.hom.app ((Over.pullback c).obj z) ≫ (Over.mapPullbackAdj c).counit.app z =
        (Over.mapPullbackAdj c).counit.app z := fun z =>
    Iso.inv_hom_id_app_assoc _ _ _
  have hbasic : IsPullback ((Over.map c).map ((Over.pullback c).map φ)).left
      ((Over.mapPullbackAdj c).counit.app y').left
      ((Over.mapPullbackAdj c).counit.app y).left φ.left := by
    change IsPullback (pullback.lift (pullback.fst y'.hom c ≫ φ.left) (pullback.snd y'.hom c)
        (by simp [pullback.condition]))
      (pullback.fst y'.hom c) (pullback.fst y.hom c) φ.left
    refine (IsPullback.of_bot ?_ (pullback.lift_fst _ _ _).symm
      (IsPullback.of_hasPullback y.hom c)).flip
    rw [pullback.lift_snd, Over.w φ]
    exact IsPullback.of_hasPullback y'.hom c
  refine hbasic.of_iso ((Over.forget Y).mapIso (β.app ((Over.pullback c).obj y'))).symm
    ((Over.forget Y).mapIso (β.app ((Over.pullback c).obj y))).symm (Iso.refl _) (Iso.refl _)
    ?_ ?_ ?_ ?_
  · exact congrArg CommaMorphism.left (β.inv.naturality ((Over.pullback c).map φ))
  · exact (Category.comp_id _).trans (congrArg CommaMorphism.left (he y')).symm
  · exact (Category.comp_id _).trans (congrArg CommaMorphism.left (he y)).symm
  · simp

/-- Base change along the 1-morphism preserves objects over affine schemes. -/
private theorem isAffine_toScheme_homFunctor_pullback
    (hX : IsAffine ((BigFppfOver.toScheme B S hS).obj X))
    (hY : IsAffine ((BigFppfOver.toScheme B S hS).obj Y))
    (f : schemeStack.{u, t} B S hS X ⟶ schemeStack.{u, t} B S hS Y) {y : Over Y}
    (hy : IsAffine ((BigFppfOver.toScheme B S hS).obj y.left)) :
    IsAffine ((BigFppfOver.toScheme B S hS).obj ((CatFiberedInGroupoids.homFunctor f.hom).obj
      ((Over.pullback (schemeMapOfFunctor B S hS f.hom.hom)).obj y)).left) := by
  have hw : (schemeStack.{u, t} B S hS Y).val.val.p.obj
      (f.hom.hom.obj ((Over.pullback (schemeMapOfFunctor B S hS f.hom.hom)).obj y)) =
        ((Over.pullback (schemeMapOfFunctor B S hS f.hom.hom)).obj y).left := f.hom.hom.w_obj _
  change IsAffine ((BigFppfOver.toScheme B S hS).obj ((schemeStack.{u, t} B S hS Y).val.val.p.obj
    (f.hom.hom.obj ((Over.pullback (schemeMapOfFunctor B S hS f.hom.hom)).obj y))))
  rw [hw]
  exact isAffine_toScheme_pullback B S hS _ _ hy hX hY

/-- The counit square of the base-change adjunction stays cartesian in schemes. -/
private theorem isPullback_toScheme_schemeStackAdjunction_counit
    (f : schemeStack.{u, t} B S hS X ⟶ schemeStack.{u, t} B S hS Y) {y' y : Over Y}
    (φ : y' ⟶ y) :
    IsPullback ((BigFppfOver.toScheme B S hS).map ((CatFiberedInGroupoids.homFunctor f.hom).map
        ((Over.pullback (schemeMapOfFunctor B S hS f.hom.hom)).map φ)).left)
      ((BigFppfOver.toScheme B S hS).map ((schemeStackAdjunction B S hS f).counit.app y').left)
      ((BigFppfOver.toScheme B S hS).map ((schemeStackAdjunction B S hS f).counit.app y).left)
      ((BigFppfOver.toScheme B S hS).map φ.left) := by
  have hP : PreservesLimitsOfShape WalkingCospan (BigFppfOver.toScheme B S hS) := by
    dsimp [BigFppfOver.toScheme]
    infer_instance
  exact (isPullback_schemeStackAdjunction_counit B S hS f φ).map (BigFppfOver.toScheme B S hS)

/-- **The direct image along a 1-morphism of affine schemes is cartesian over arrows between
affine objects whose base change is cartesian.** For `φ : y' ⟶ y` between objects lying over
affine schemes, the base-change comparison of `f_*ℱ = ℱ ∘ G` along `φ` is bijective as soon as the
one of `ℱ` along `G φ` is. -/
theorem bijective_restrictionBaseChange_pushforward_schemeStack
    (hX : IsAffine ((BigFppfOver.toScheme B S hS).obj X))
    (hY : IsAffine ((BigFppfOver.toScheme B S hS).obj Y))
    (f : schemeStack.{u, t} B S hS X ⟶ schemeStack.{u, t} B S hS Y)
    (F : SheafOfModules.{u + 1} (ringStructureSheafCore B S hS
      (CatFiberedInGroupoids.homFunctor f.hom ⋙ (schemeStack.{u, t} B S hS Y).val.val.p)
      (isFiberedInGroupoids_homFunctor_comp B S hS f.hom) (etaleTopology B)
      (etaleTopology_le_topology B)))
    {y' y : Over Y} (φ : y' ⟶ y)
    (hy' : IsAffine ((BigFppfOver.toScheme B S hS).obj y'.left))
    (hy : IsAffine ((BigFppfOver.toScheme B S hS).obj y.left))
    (hF : Function.Bijective (Stacks.PresheafOfModules.restrictionBaseChange.{u + 1, u, u, u + 1}
      (R := (structureSheaf B S hS
        (CatFiberedInGroupoids.homFunctor f.hom ⋙ (schemeStack.{u, t} B S hS Y).val.val.p)
        (isFiberedInGroupoids_homFunctor_comp B S hS f.hom) (etaleTopology B)
        (etaleTopology_le_topology B)).obj)
      F.val ((Over.pullback (schemeMapOfFunctor B S hS f.hom.hom)).map φ).op).hom) :
    letI := isContinuous_rightAdjoint_of_adjunction B S hS (schemeStack.{u, t} B S hS Y).val.val.p
      (CatFiberedInGroupoids.homFunctor f.hom) (isFiberedInGroupoids_homFunctor_comp B S hS f.hom)
      (schemeStack.{u, t} B S hS Y).val.isFiberedInGroupoids (schemeStackAdjunction B S hS f)
      (etaleTopology B)
    Function.Bijective (Stacks.PresheafOfModules.restrictionBaseChange.{u + 1, u, u, u + 1}
      (R := (structureSheaf B S hS (schemeStack.{u, t} B S hS Y).val.val.p
        (schemeStack.{u, t} B S hS Y).val.isFiberedInGroupoids (etaleTopology B)
        (etaleTopology_le_topology B)).obj)
      ((SheafOfModules.pushforward.{u + 1} (rightAdjointRingMap B S hS
        (schemeStack.{u, t} B S hS Y).val.val.p (CatFiberedInGroupoids.homFunctor f.hom)
        (isFiberedInGroupoids_homFunctor_comp B S hS f.hom)
        (schemeStack.{u, t} B S hS Y).val.isFiberedInGroupoids (schemeStackAdjunction B S hS f)
        (etaleTopology B) (etaleTopology_le_topology B))).obj F).val φ.op).hom := by
  let c := schemeMapOfFunctor B S hS f.hom.hom
  let RD := (structureSheaf B S hS (schemeStack.{u, t} B S hS Y).val.val.p
    (schemeStack.{u, t} B S hS Y).val.isFiberedInGroupoids (etaleTopology B)
    (etaleTopology_le_topology B)).obj
  let RC := (structureSheaf B S hS
    (CatFiberedInGroupoids.homFunctor f.hom ⋙ (schemeStack.{u, t} B S hS Y).val.val.p)
    (isFiberedInGroupoids_homFunctor_comp B S hS f.hom) (etaleTopology B)
    (etaleTopology_le_topology B)).obj
  let ψ : RD ⟶ (Over.pullback c).op ⋙ RC :=
    Functor.whiskerRight (NatTrans.op (schemeStackAdjunction B S hS f).counit) RD
  have hpb := isPullback_toScheme_schemeStackAdjunction_counit B S hS f φ
  have hGy := isAffine_toScheme_homFunctor_pullback B S hS hX hY f hy
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj
      (Over.left ((𝟭 (schemeStack.{u, t} B S hS Y).val.val.obj).obj y'))) := hy'
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj
      (Over.left ((𝟭 (schemeStack.{u, t} B S hS Y).val.val.obj).obj y))) := hy
  have h0 := AlgebraicGeometry.isPushout_appTop_of_isPullback hpb
  have hpo : IsPushout (ψ.app (op y)) (RD.map φ.op) (RC.map ((Over.pullback c).op.map φ.op))
      (ψ.app (op y')) := h0
  exact Stacks.PresheafOfModules.bijective_restrictionBaseChange_pushforward.{u, u, u + 1, u + 1,
    u, u + 1} ψ F.val φ.op hpo hF

/-- Let `P` be a property of morphisms of schemes stable under base change. If an arrow `φ` of
`Sch/Y` lies over a morphism with `P`, so does its image under `G`. -/
theorem of_schemeStackAdjunction_map {P : MorphismProperty Scheme.{u}} [P.IsStableUnderBaseChange]
    (f : schemeStack.{u, t} B S hS X ⟶ schemeStack.{u, t} B S hS Y) {y' y : Over Y}
    (φ : y' ⟶ y) (hφ : P ((BigFppfOver.toScheme B S hS).map φ.left)) :
    P ((BigFppfOver.toScheme B S hS).map ((CatFiberedInGroupoids.homFunctor f.hom).map
      ((Over.pullback (schemeMapOfFunctor B S hS f.hom.hom)).map φ)).left) := by
  exact MorphismProperty.of_isPullback
    (isPullback_toScheme_schemeStackAdjunction_counit B S hS f φ).flip hφ

/-- Base change along the 1-morphism carries objects over affine schemes to objects over affine
schemes, `X` and `Y` being affine. -/
theorem isAffine_schemeStackAdjunction_obj
    (hX : IsAffine ((BigFppfOver.toScheme B S hS).obj X))
    (hY : IsAffine ((BigFppfOver.toScheme B S hS).obj Y))
    (f : schemeStack.{u, t} B S hS X ⟶ schemeStack.{u, t} B S hS Y) {y : Over Y}
    (hy : IsAffine ((BigFppfOver.toScheme B S hS).obj y.left)) :
    IsAffine ((BigFppfOver.toScheme B S hS).obj ((CatFiberedInGroupoids.homFunctor f.hom).obj
      ((Over.pullback (schemeMapOfFunctor B S hS f.hom.hom)).obj y)).left) :=
  isAffine_toScheme_homFunctor_pullback B S hS hX hY f hy

/-- **Hypothesis (4) of Stacks 076Z for `LQCoh^fbc` in degree zero, for the direct image read as
the pushforward along the right adjoint.** For a 1-morphism `f` between the algebraic stacks
represented by objects lying over affine schemes and `ℱ ∈ LQCoh^fbc`, the module
`(f_*ℱ)(y) = ℱ(y ×_Y X)` is locally quasi-coherent and has the flat base change property. -/
theorem locallyQuasicoherentFlatBaseChangeSheafRule_pushforward_schemeStack
    (E : BigEtaleSite.{u}) (h : E.cutoff = B.cutoff)
    (hX : IsAffine ((BigFppfOver.toScheme B S hS).obj X))
    (hY : IsAffine ((BigFppfOver.toScheme B S hS).obj Y))
    (f : schemeStack.{u, t} B S hS X ⟶ schemeStack.{u, t} B S hS Y)
    (F : SheafOfModules.{u + 1} (ringStructureSheafCore B S hS
      (CatFiberedInGroupoids.homFunctor f.hom ⋙ (schemeStack.{u, t} B S hS Y).val.val.p)
      (isFiberedInGroupoids_homFunctor_comp B S hS f.hom) (etaleTopology B)
      (etaleTopology_le_topology B)))
    (hF : locallyQuasicoherentFlatBaseChangeSheafRule B E h S hS
      (CatFiberedInGroupoids.homFunctor f.hom ⋙ (schemeStack.{u, t} B S hS Y).val.val.p)
      (isFiberedInGroupoids_homFunctor_comp B S hS f.hom) F.val) :
    letI := isContinuous_rightAdjoint_of_adjunction B S hS (schemeStack.{u, t} B S hS Y).val.val.p
      (CatFiberedInGroupoids.homFunctor f.hom) (isFiberedInGroupoids_homFunctor_comp B S hS f.hom)
      (schemeStack.{u, t} B S hS Y).val.isFiberedInGroupoids (schemeStackAdjunction B S hS f)
      (etaleTopology B)
    locallyQuasicoherentFlatBaseChangeSheafRule B E h S hS (schemeStack.{u, t} B S hS Y).val.val.p
      (schemeStack.{u, t} B S hS Y).val.isFiberedInGroupoids
      ((SheafOfModules.pushforward.{u + 1} (rightAdjointRingMap B S hS
        (schemeStack.{u, t} B S hS Y).val.val.p (CatFiberedInGroupoids.homFunctor f.hom)
        (isFiberedInGroupoids_homFunctor_comp B S hS f.hom)
        (schemeStack.{u, t} B S hS Y).val.isFiberedInGroupoids (schemeStackAdjunction B S hS f)
        (etaleTopology B) (etaleTopology_le_topology B))).obj F).val := by
  let := isContinuous_rightAdjoint_of_adjunction B S hS (schemeStack.{u, t} B S hS Y).val.val.p
    (CatFiberedInGroupoids.homFunctor f.hom) (isFiberedInGroupoids_homFunctor_comp B S hS f.hom)
    (schemeStack.{u, t} B S hS Y).val.isFiberedInGroupoids (schemeStackAdjunction B S hS f)
    (etaleTopology B)
  let q := (schemeStack.{u, t} B S hS Y).val.val.p
  let hq := (schemeStack.{u, t} B S hS Y).val.isFiberedInGroupoids
  let fF := CatFiberedInGroupoids.homFunctor f.hom
  let hp := isFiberedInGroupoids_homFunctor_comp B S hS f.hom
  let c := schemeMapOfFunctor B S hS f.hom.hom
  let N := (SheafOfModules.pushforward.{u + 1} (rightAdjointRingMap B S hS q fF hp hq
    (schemeStackAdjunction B S hS f) (etaleTopology B) (etaleTopology_le_topology B))).obj F
  obtain ⟨hlqc, -, hfbc⟩ := hF
  have hfbc' : HasFlatBaseChangePropertySheafUnivLE.{u, u + 1, u, u + 1} B E h S hS (fF ⋙ q) hp F :=
    hfbc F.isSheaf
  have hrbcF : ∀ {x' x : (schemeStack.{u, t} B S hS X).val.val.obj} (g : x' ⟶ x),
      IsAffine ((fF ⋙ q).obj x').left.1 → IsAffine ((fF ⋙ q).obj x).left.1 →
      IsIso (restrictSheafPullbackComparison B E h S hS (fF ⋙ q) hp g F) →
      Function.Bijective (Stacks.PresheafOfModules.restrictionBaseChange.{u + 1, u, u, u + 1}
        (R := (structureSheaf B S hS (fF ⋙ q) hp (etaleTopology B)
          (etaleTopology_le_topology B)).obj) F.val g.op).hom := fun g hx' hx hc =>
    (isIso_restrictSheafPullbackComparison_iff_bijective_restrictionBaseChange B E h S hS
      (fF ⋙ q) hp g hx' hx F (hlqc.2 _).2 (hlqc.2 _).2).1 hc
  have hrbcN : ∀ {y' y : (schemeStack.{u, t} B S hS Y).val.val.obj} (φ : y' ⟶ y),
      IsAffine ((BigFppfOver.toScheme B S hS).obj (q.obj y')) →
      IsAffine ((BigFppfOver.toScheme B S hS).obj (q.obj y)) →
      IsIso (restrictSheafPullbackComparison B E h S hS (fF ⋙ q) hp
        ((Over.pullback c).map φ) F) →
      Function.Bijective (Stacks.PresheafOfModules.restrictionBaseChange.{u + 1, u, u, u + 1}
        (R := (structureSheaf B S hS q hq (etaleTopology B) (etaleTopology_le_topology B)).obj)
        N.val φ.op).hom := fun φ hy' hy hc =>
    bijective_restrictionBaseChange_pushforward_schemeStack B S hS hX hY f F φ hy' hy
      (hrbcF _ (isAffine_schemeStackAdjunction_obj B S hS hX hY f hy')
        (isAffine_schemeStackAdjunction_obj B S hS hX hY f hy) hc)
  have hlqcN : IsLocallyQuasicoherent B E h S hS q hq N.val := by
    refine isLocallyQuasicoherent_of_bijective_restrictionBaseChange_succ B E h S hS q hq N ?_
    intro y y' g hg hy hy'
    have hgG :
        Etale ((BigFppfOver.toScheme B S hS).map ((fF.map ((Over.pullback c).map g)).left)) :=
      of_schemeStackAdjunction_map B S hS (P := @Etale) f g hg
    exact hrbcN g hy' hy
      (isIso_restrictSheafPullbackComparison_of_etale B E h S hS (fF ⋙ q) hp _ hgG F)
  have hN : HasFlatBaseChangePropertySheafUnivLE.{u, u + 1, u, u + 1} B E h S hS q hq N := by
    refine hasFlatBaseChangePropertySheaf_of_affine.{u, u + 1, u, u + 1} B E h S hS q hq N ?_
    intro y' y φ hφ hy' hy
    refine (isIso_restrictSheafPullbackComparison_iff_bijective_restrictionBaseChange B E h S hS
      q hq φ hy' hy N (hlqcN.2 y').2 (hlqcN.2 y).2).2 (hrbcN φ hy' hy ?_)
    have hgG : Flat ((BigFppfOver.toScheme B S hS).map
        ((fF.map ((Over.pullback c).map φ)).left)) :=
      of_schemeStackAdjunction_map B S hS (P := @Flat) f φ hφ
    exact hfbc' _ hgG
  exact ⟨hlqcN, N.isSheaf, fun _ => hN⟩

end SchemeStack

end AlgebraicGeometry.Stack

end
