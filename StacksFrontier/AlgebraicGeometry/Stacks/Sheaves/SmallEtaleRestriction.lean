module

public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Pullbacks
public import Mathlib.CategoryTheory.Sites.DenseSubsite.InducedTopology
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Sites.Pullback
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.CategoryTheory.Sites.Localization.Relocalize
public import StacksFrontier.AlgebraicGeometry.Stacks.LocalizationPullback
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.BaseSites
public import StacksFrontier.AlgebraicGeometry.Topologies.ChangeOfSites.ChosenEtaleSite
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.Limits
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.SmallEtaleBaseChange
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.SmallEtaleProjection

/-!
# The comparison maps between small étale restrictions (Stacks 06W2, 06W3)

Let `p : 𝒳 ⥤ (Sch/S)_{fppf}` be a category fibred in groupoids and let `F` be a presheaf on
`𝒳`. Stacks 06W1 restricts `F` to the small étale site of the scheme `U` underlying an object
`x` of `𝒳`. An arrow `φ : x ⟶ y` of `𝒳` lies over a morphism `a : U ⟶ V` of schemes, and the
two restrictions are compared along it in two equivalent ways:

* **Stacks 06W2** is the map `c_φ : F|_{V_ét} ⟶ a_{small, *}(F|_{U_ét})` to the direct image,
  which on the small étale site is literal precomposition with base change along `a`;
* **Stacks 06W3** is its adjoint `c_φ : a_{small}^{-1}(F|_{V_ét}) ⟶ F|_{U_ét}`, defined when
  `F` is an étale sheaf, for which the restrictions are sheaves.

## Main definitions

* `AlgebraicGeometry.Stack.smallEtaleBaseMorphism`: the morphism of the big étale category of
  schemes below an arrow of `𝒳`.
* `AlgebraicGeometry.Stack.restrictionPushforwardComparison`: **Stacks 06W2**.
* `AlgebraicGeometry.Stack.restrictionInverseImageComparison`: **Stacks 06W3**.

## Main results

* `AlgebraicGeometry.Stack.restrictionPushforwardComparison_app`: each component of the
  direct-image comparison is restriction along the arrow between the cartesian lifts of the
  base-change square, which pins the map down rather than merely asserting one exists.
* `AlgebraicGeometry.Stack.restrictionPushforwardComparison_naturality`: the comparison is
  natural in the presheaf.
* `AlgebraicGeometry.Stack.restrictToSmallEtale_isSheaf`: the restriction of an étale sheaf
  on `𝒳` to a small étale site is a sheaf.

## Implementation notes

The big fppf site and the big étale site are assumed to have the same size cutoff, so they
have the same bounded category of schemes and an arrow of `𝒳` has an underlying arrow of the
étale site; that is `smallEtaleBaseMorphism`.

Both comparisons are built from the localization equivalence of Stacks 06W0: a small étale
object over `V` is transported to the slice of `𝒳` at `y`, pulled back along `a`, transported
to the slice at `x`, and the comparison is the restriction map of `F` along the resulting
arrow of `𝒳`. The arrow in question is obtained as a preimage under the fully faithful
localization functor, so the direct-image comparison is specified by its components rather
than chosen; `restrictionPushforwardComparison_app` records that specification.

The inverse-image comparison is the mate of the direct-image one under the pullback–pushforward
adjunction on sheaves. Its source and target are the actual restricted sheaves, not their
sheafifications, which is what `restrictToSmallEtale_isSheaf` is for: the restriction functor
is a composite of three continuous functors, so it carries sheaves to sheaves on the nose.

commutations of slice functors that the construction needs, and
`CategoryTheory.coverPreserving_toGrothendieck_of_generators` the criterion for a functor to be
cover-preserving. All three are general category theory and are stated here only because no
module of the library yet collects them.

## References

* [Stacks Project, Tag 06W2](https://stacks.math.columbia.edu/tag/06W2)
* [Stacks Project, Tag 06W3](https://stacks.math.columbia.edu/tag/06W3)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u v w t s

namespace CategoryTheory.Over

universe u₁ v₁ u₂ v₂

/-- Post-composition with a functor preserving fibre products commutes with the slice pullback
functor, by the comparison map of the preserved pullback. -/
noncomputable def pullbackCompPostIso
    {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    (I : C ⥤ D) {X Y : C} (f : X ⟶ Y)
    [Limits.HasPullbacksAlong f] [Limits.HasPullbacksAlong (I.map f)]
    [Limits.PreservesLimitsOfShape Limits.WalkingCospan I] :
    Over.pullback f ⋙ Over.post I ≅ Over.post I ⋙ Over.pullback (I.map f) :=
  NatIso.ofComponents
    (fun Z : Over Y => Over.isoMk (Limits.PreservesPullback.iso I Z.hom f)
      (Limits.PreservesPullback.iso_hom_snd I Z.hom f))
    (by
      intro Z Z' g
      apply Over.OverMorphism.ext
      apply Limits.pullback.hom_ext
      · simp [Over.pullback, Over.post, Category.assoc, ← Functor.map_comp,
          Limits.pullback.lift_fst]
      · simp [Over.pullback, Over.post, Category.assoc,
          Limits.pullbackComparison_comp_snd, Limits.pullback.lift_snd])

end CategoryTheory.Over

namespace AlgebraicGeometry.Stack

/-- The scheme an object of a category fibred in groupoids over the big fppf category of `S`
lies over is contained in any big étale site with the same size cutoff. -/
theorem contains_base (B : BigFppfSite.{u}) (E : BigEtaleSite.{u}) (h : E.cutoff = B.cutoff)
    (S : Scheme.{u}) (hS : B.Contains S) {𝒳 : Type v} [Category.{w} 𝒳]
    (p : 𝒳 ⥤ BigFppfOver B S hS) (x : 𝒳) :
    E.Contains (p.obj x).left.1 := by
  simpa [h] using (p.obj x).left.2

variable (B : BigFppfSite.{u}) (E : BigEtaleSite.{u}) (h : E.cutoff = B.cutoff)
  (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 06W2.** The morphism of the big étale category of schemes below an arrow of a
category fibred in groupoids: the fppf and étale cutoffs agree, so the scheme morphism
underlying the arrow is a morphism of the étale site's bounded category. -/
@[stacks 06W2 "the morphism of schemes below an arrow"]
def smallEtaleBaseMorphism {𝒳 : Type v} [Category.{w} 𝒳]
    (p : 𝒳 ⥤ BigFppfOver B S hS) {x y : 𝒳} (φ : x ⟶ y) :
    E.obj (p.obj x).left.1 (contains_base B E h S hS p x) ⟶
      E.obj (p.obj y).left.1 (contains_base B E h S hS p y) :=
  ObjectProperty.homMk (B.inclusion.map (p.map φ).left)

/-- **Stacks 06W2.** The comparison `c_φ : F|_{V_ét} ⟶ a_{small, *}(F|_{U_ét})` from the
restriction of a presheaf at the target of an arrow `φ : x ⟶ y` to the direct image, along the
underlying morphism of schemes, of its restriction at the source.

The direct image on small étale sites is precomposition with base change, so the target is
spelled as such. -/
@[stacks 06W2 "the comparison with the direct image"]
noncomputable def restrictionPushforwardComparison {𝒳 : Type v} [Category.{w} 𝒳]
    (p : 𝒳 ⥤ BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids) {x y : 𝒳} (φ : x ⟶ y)
    {A : Type t} [Category.{s} A] (F : 𝒳ᵒᵖ ⥤ A) :
    restrictToSmallEtale B E h S hS p hp y F ⟶
      (smallEtaleBaseChange E (smallEtaleBaseMorphism B E h S hS p φ)).op ⋙
        restrictToSmallEtale B E h S hS p hp x F := by
  classical
  let q := p ⋙ Over.forget (B.obj hS)
  let qx := Over.post (X := x) q
  let qy := Over.post (X := y) q
  letI : qx.IsEquivalence := isEquivalence_overPost B S hS p hp x
  letI : qy.IsEquivalence := isEquivalence_overPost B S hS p hp y
  let jx := smallEtaleInclusion B E h (p.obj x).left.1 (contains_base B E h S hS p x)
  let jy := smallEtaleInclusion B E h (p.obj y).left.1 (contains_base B E h S hS p y)
  let a := smallEtaleBaseMorphism B E h S hS p φ
  let bc := smallEtaleBaseChange E a
  let Xfun := bc ⋙ jx ⋙ qx.inv ⋙ Over.map φ
  let Yfun := jy ⋙ qy.inv
  let I := ObjectProperty.ιOfLE (P := schemeSizeBelow E.cutoff)
    (P' := schemeSizeBelow B.cutoff) (by intro Z hZ; simpa [h] using hZ)
  have hfa : I.map a = q.map φ := rfl
  cases hfa.symm
  letI : I.IsEquivalence := (ObjectProperty.isEquivalence_ιOfLE_iff _).2 fun Z hZ =>
    (schemeSizeBelow E.cutoff).le_isoClosure Z (by simpa [h] using hZ)
  letI : PreservesLimitsOfShape WalkingCospan I := inferInstance
  let f := I.map a
  letI : HasPullbacksAlong f := by
    intro W g
    infer_instance
  let hcomm := Over.mapCompPostIso q φ
  letI : HasPullbacksAlong a := by
    intro W g
    infer_instance
  let hbase : bc ⋙ jx ≅ jy ⋙ Over.pullback f := by
    dsimp [bc, jx, jy, f, q]
    calc
      smallEtaleBaseChange E a ⋙
          (SmallEtale.inclusion E (p.obj x).left.1 (contains_base B E h S hS p x) ⋙
            Over.post I) =
          (smallEtaleBaseChange E a ⋙
            SmallEtale.inclusion E (p.obj x).left.1 (contains_base B E h S hS p x)) ⋙
            Over.post I := rfl
      _ = (SmallEtale.inclusion E (p.obj y).left.1 (contains_base B E h S hS p y) ⋙
            Over.pullback a) ⋙ Over.post I := by
          rw [smallEtaleBaseChange_comp_inclusion]
      _ ≅ (SmallEtale.inclusion E (p.obj y).left.1 (contains_base B E h S hS p y) ⋙
            Over.post I) ⋙ Over.pullback (I.map a) :=
          Functor.associator
            (SmallEtale.inclusion E (p.obj y).left.1 (contains_base B E h S hS p y))
            (Over.pullback a) (Over.post I) ≪≫
            Functor.isoWhiskerLeft
              (SmallEtale.inclusion E (p.obj y).left.1 (contains_base B E h S hS p y))
              (Over.pullbackCompPostIso I a) ≪≫
            (Functor.associator
              (SmallEtale.inclusion E (p.obj y).left.1 (contains_base B E h S hS p y))
              (Over.post I) (Over.pullback (I.map a))).symm
      _ = jy ⋙ Over.pullback f := rfl
  let hbeta : Xfun ⋙ qy ⟶ Yfun ⋙ qy := by
    dsimp [Xfun, Yfun]
    exact
      (Functor.isoWhiskerLeft (bc ⋙ jx ⋙ qx.inv) hcomm).hom ≫
      (Functor.whiskerLeft (bc ⋙ jx)
        (Functor.isoWhiskerRight qx.asEquivalence.counitIso (Over.map f)).hom ≫
          Functor.whiskerLeft (bc ⋙ jx) (Functor.leftUnitor (Over.map f)).hom) ≫
      (Functor.isoWhiskerRight hbase (Over.map f)).hom ≫
      Functor.whiskerLeft jy (Over.mapPullbackAdj f).counit ≫
      Functor.whiskerLeft jy qy.asEquivalence.counitIso.inv
  let qyff := Functor.FullyFaithful.ofFullyFaithful qy
  let alpha : Xfun ⟶ Yfun :=
    { app := fun W => qyff.preimage (hbeta.app W)
      naturality := by
        intro W W' g
        apply qy.map_injective
        calc
          qy.map (Xfun.map g ≫ qyff.preimage (hbeta.app W')) =
              qy.map (Xfun.map g) ≫ hbeta.app W' := by
                rw [Functor.map_comp, qyff.map_preimage]
          _ = hbeta.app W ≫ qy.map (Yfun.map g) := hbeta.naturality g
          _ = qy.map (qyff.preimage (hbeta.app W) ≫ Yfun.map g) := by
                rw [Functor.map_comp, qyff.map_preimage] }
  change
    jy.op ⋙ qy.inv.op ⋙ (Over.forget y).op ⋙ F ⟶
      bc.op ⋙ jx.op ⋙ qx.inv.op ⋙ (Over.forget x).op ⋙ F
  refine ⟨fun W => F.map (((Over.forget y).map (alpha.app (Opposite.unop W))).op), ?_⟩
  intro W W' g
  have hg := alpha.naturality (Opposite.unop g)
  simp only [Functor.comp_obj, Functor.comp_map, Functor.op_map]
  rw [← F.map_comp, ← F.map_comp]
  apply congrArg F.map
  have hforg := congrArg (fun k => (Over.Hom.left k).op) hg.symm
  change
    (Over.Hom.left (qy.inv.map (jy.map g.unop))).op ≫
      (Over.Hom.left (alpha.app (Opposite.unop W'))).op =
    (Over.Hom.left (alpha.app (Opposite.unop W))).op ≫
      (Over.Hom.left (qx.inv.map (jx.map (bc.map g.unop)))).op
  exact hforg

/-- **Stacks 06W2.** On a small étale object `W` over `V`, the comparison with the direct image
is restriction of `F` along the arrow of `𝒳` between the cartesian lifts of `W` and of its base
change, characterized by lying over the projection of the base-change square.

This specifies the comparison map, rather than merely producing one. -/
@[stacks 06W2 "the component formula"]
theorem restrictionPushforwardComparison_app {𝒳 : Type v} [Category.{w} 𝒳]
    (p : 𝒳 ⥤ BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids) {x y : 𝒳} (φ : x ⟶ y)
    {A : Type t} [Category.{s} A] (F : 𝒳ᵒᵖ ⥤ A)
    (W : SmallEtale E (p.obj y).left.1 (contains_base B E h S hS p y)) :
    letI : (Over.post (X := x) (p ⋙ Over.forget (B.obj hS))).IsEquivalence :=
      isEquivalence_overPost B S hS p hp x
    letI : (Over.post (X := y) (p ⋙ Over.forget (B.obj hS))).IsEquivalence :=
      isEquivalence_overPost B S hS p hp y
    let f := smallEtaleBaseMorphism B E h S hS p φ
    let V' := (smallEtaleInclusion B E h (p.obj y).left.1 (contains_base B E h S hS p y)).obj W
    let U' := (smallEtaleInclusion B E h (p.obj x).left.1
      (contains_base B E h S hS p x)).obj ((smallEtaleBaseChange E f).obj W)
    let y' := (Over.post (X := y) (p ⋙ Over.forget (B.obj hS))).inv.obj V'
    let x' := (Over.post (X := x) (p ⋙ Over.forget (B.obj hS))).inv.obj U'
    let εy := (Over.post (X := y) (p ⋙ Over.forget (B.obj hS))).asEquivalence.counit.app V'
    let εx := (Over.post (X := x) (p ⋙ Over.forget (B.obj hS))).asEquivalence.counit.app U'
    ∀ φ' : x'.left ⟶ y'.left, φ' ≫ y'.hom = x'.hom ≫ φ →
      B.inclusion.map (p.map φ').left ≫ B.inclusion.map εy.left =
        B.inclusion.map εx.left ≫ E.inclusion.map (pullback.fst W.obj.hom f) →
      (restrictionPushforwardComparison B E h S hS p hp φ F).app (Opposite.op W) =
        F.map φ'.op := by
  classical
  intro _ _ _ y' x' εy εx f' hsq hproj
  let : IsIso εy := by
    dsimp [εy]
    infer_instance
  let : IsIso εy.left := by
    show IsIso ((Over.forget ((p ⋙ Over.forget (B.obj hS)).obj y)).map εy)
    infer_instance
  let q := p ⋙ Over.forget (B.obj hS)
  let qx := Over.post (X := x) q
  let qy := Over.post (X := y) q
  let : qx.IsEquivalence := isEquivalence_overPost B S hS p hp x
  let : qy.IsEquivalence := isEquivalence_overPost B S hS p hp y
  have hqxInv : qx.inv = qx.asEquivalence.inverse := rfl
  have hqyInv : qy.inv = qy.asEquivalence.inverse := rfl
  let jx := smallEtaleInclusion B E h (p.obj x).left.1 (contains_base B E h S hS p x)
  let jy := smallEtaleInclusion B E h (p.obj y).left.1 (contains_base B E h S hS p y)
  let a := smallEtaleBaseMorphism B E h S hS p φ
  let bc := smallEtaleBaseChange E a
  let Xfun := bc ⋙ jx ⋙ qx.inv ⋙ Over.map φ
  let Yfun := jy ⋙ qy.asEquivalence.inverse
  let I := ObjectProperty.ιOfLE (P := schemeSizeBelow E.cutoff)
    (P' := schemeSizeBelow B.cutoff) (by intro Z hZ; simpa [h] using hZ)
  have hfa : I.map a = q.map φ := rfl
  cases hfa.symm
  let : I.IsEquivalence := (ObjectProperty.isEquivalence_ιOfLE_iff _).2 fun Z hZ =>
    (schemeSizeBelow E.cutoff).le_isoClosure Z (by simpa [h] using hZ)
  let : PreservesLimitsOfShape WalkingCospan I := inferInstance
  let fpb := I.map a
  let : HasPullbacksAlong fpb := by
    intro Z g
    infer_instance
  let hcomm := Over.mapCompPostIso q φ
  have hcommLeft :
      (Over.Hom.left (hcomm.hom.app (qx.inv.obj (jx.obj (bc.obj W))))).hom = 𝟙 _ := rfl
  have hcommObjEq :
      B.inclusion.obj ((Over.map φ ⋙ Over.post q).obj
        (qx.inv.obj (jx.obj (bc.obj W)))).left =
      B.inclusion.obj ((Over.post q ⋙ Over.map (q.map φ)).obj
        (qx.inv.obj (jx.obj (bc.obj W)))).left := by
    simp [Functor.comp_obj, Over.map_obj_left]
  have hcommLeftMap' :
      B.inclusion.map (Over.Hom.left
        (hcomm.hom.app (qx.inv.obj (jx.obj (bc.obj W))))) = eqToHom hcommObjEq := by
    show (Over.Hom.left (hcomm.hom.app (qx.inv.obj (jx.obj (bc.obj W))))).hom =
      eqToHom hcommObjEq
    rw [hcommLeft]
    cases hcommObjEq
    rfl
  let : HasPullbacksAlong a := by
    intro Z g
    infer_instance
  let hbase : bc ⋙ jx ≅ jy ⋙ Over.pullback fpb := by
    dsimp [bc, jx, jy, fpb, q]
    calc
      smallEtaleBaseChange E a ⋙ _ ⋙ Over.post I = (smallEtaleBaseChange E a ⋙ _) ⋙ Over.post I :=
        rfl
      _ = (_ ⋙ Over.pullback a) ⋙ Over.post I := by rw [smallEtaleBaseChange_comp_inclusion]
      _ ≅ _ ⋙ Over.post I ⋙ Over.pullback (I.map a) :=
          Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _ (Over.pullbackCompPostIso I a) ≪≫
            (Functor.associator _ _ _).symm
      _ = jy ⋙ Over.pullback fpb := rfl
  have hpb := congrArg B.inclusion.map (PreservesPullback.iso_hom_fst I
    ((SmallEtale.inclusion E (p.obj y).left.1 (contains_base B E h S hS p y)).obj W).hom a)
  have hbaseProjection :
      B.inclusion.map (Over.Hom.left (hbase.hom.app W)) ≫
        B.inclusion.map (pullback.fst (jy.obj W).hom fpb) =
      E.inclusion.map (pullback.fst W.obj.hom a) := hpb
  have hbaseProjectionHom :
      (Over.Hom.left (hbase.hom.app W)).hom ≫ (pullback.fst (jy.obj W).hom fpb).hom =
      (pullback.fst W.obj.hom a).hom := by
    simpa using hbaseProjection
  let hbeta : Xfun ⋙ qy ⟶ Yfun ⋙ qy := by
    dsimp [Xfun, Yfun]
    exact
      (Functor.isoWhiskerLeft (bc ⋙ jx ⋙ qx.inv) hcomm).hom ≫
      (Functor.whiskerLeft (bc ⋙ jx)
        (Functor.isoWhiskerRight qx.asEquivalence.counitIso (Over.map fpb)).hom ≫
          Functor.whiskerLeft (bc ⋙ jx) (Functor.leftUnitor (Over.map fpb)).hom) ≫
      (Functor.isoWhiskerRight hbase (Over.map fpb)).hom ≫
      Functor.whiskerLeft jy (Over.mapPullbackAdj fpb).counit ≫
      Functor.whiskerLeft jy qy.asEquivalence.counitIso.inv
  have hbetaEq : hbeta =
      (Functor.isoWhiskerLeft (bc ⋙ jx ⋙ qx.inv) hcomm).hom ≫
        (Functor.whiskerLeft (bc ⋙ jx)
          (Functor.isoWhiskerRight qx.asEquivalence.counitIso (Over.map fpb)).hom ≫
            Functor.whiskerLeft (bc ⋙ jx) (Functor.leftUnitor (Over.map fpb)).hom) ≫
        (Functor.isoWhiskerRight hbase (Over.map fpb)).hom ≫
        Functor.whiskerLeft jy (Over.mapPullbackAdj fpb).counit ≫
        Functor.whiskerLeft jy qy.asEquivalence.counitIso.inv := rfl
  have hcounitApp (Z : Over (I.obj (E.obj (p.obj y).left.1 (contains_base B E h S hS p y)))) :
      (Over.mapPullbackAdj fpb).counit.app Z =
        Over.homMk (pullback.fst Z.hom fpb) pullback.condition := by
    apply Over.OverMorphism.ext
    simp
  have hcx : qx.asEquivalence.counitIso.hom.app (jx.obj (bc.obj W)) = εx := rfl
  have hcy : qy.asEquivalence.counitIso.hom.app (jy.obj W) = εy := rfl
  let ex := qx.asEquivalence.counitIso.hom.app (jx.obj (bc.obj W))
  let ey := qy.asEquivalence.counitIso.hom.app (jy.obj W)
  let ν := ((bc ⋙ jx).whiskerLeft
    (Functor.whiskerRight qx.asEquivalence.counitIso.hom (Over.map fpb)) ≫
    (bc ⋙ jx).whiskerLeft (Over.map fpb).leftUnitor.hom).app W
  have hqxStep : Over.Hom.left ν = ex.left := by
    simp [ν, Functor.whiskerLeft_app, Functor.whiskerRight_app, NatTrans.comp_app,
      Functor.leftUnitor_hom_app]
    rfl
  have hqxStepToMap :
      Over.Hom.left ν =
        Over.Hom.left ((Over.map fpb).map
          (qx.asEquivalence.counitIso.hom.app (jx.obj (bc.obj W)))) ≫
          Over.Hom.left (𝟙 ((Over.map fpb).obj (jx.obj (bc.obj W)))) := by
    rw [hqxStep, Over.map_map_left]
    simp
    rfl
  have hqyCancelLeft :
      Over.Hom.left (qy.asEquivalence.counitIso.inv.app (jy.obj W)) ≫ ey.left = 𝟙 _ :=
    congrArg Over.Hom.left (Iso.inv_hom_id_app qy.asEquivalence.counitIso (jy.obj W))
  have hqyCancelUnderlying :
      (Over.Hom.left (qy.asEquivalence.counitIso.inv.app (jy.obj W))).hom ≫
        (Over.Hom.left ey).hom = 𝟙 _ := by
    simpa using congrArg (fun g => g.hom) hqyCancelLeft
  have hqxStepMap := congrArg B.inclusion.map hqxStep
  have hYobj : (Yfun ⋙ qy).obj W =
      (qy.asEquivalence.inverse ⋙ qy.asEquivalence.functor).obj (jy.obj W) := rfl
  have hXobj : (Xfun ⋙ qy).obj W =
      (Over.map φ ⋙ Over.post q).obj (qx.inv.obj (jx.obj (bc.obj W))) := rfl
  cases hqxInv
  cases hqyInv
  cases hXobj
  cases hYobj
  have hbetaLeftDecomp :
      Over.Hom.left (hbeta.app W) =
        Over.Hom.left (hcomm.hom.app (qx.inv.obj (jx.obj (bc.obj W)))) ≫
          Over.Hom.left
            ν ≫
          Over.Hom.left ((Over.map fpb).map (hbase.hom.app W)) ≫
          Over.Hom.left (Over.homMk (pullback.fst (jy.obj W).hom fpb)
            (pullback.condition)) ≫
          Over.Hom.left (qy.asEquivalence.counitIso.inv.app (jy.obj W)) := by
    rw [hbetaEq]
    simp only [Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app,
      Functor.whiskerRight_app,
      NatTrans.comp_app, Over.comp_left, Functor.comp_obj, Over.map_obj_left, hcounitApp]
    have hstep := congrArg
      (fun k =>
        Over.Hom.left (hcomm.hom.app (qx.inv.obj (jx.obj (bc.obj W)))) ≫ k ≫
          Over.Hom.left (hbase.hom.app W) ≫
          pullback.fst (jy.obj W).hom fpb ≫
          Over.Hom.left (qy.asEquivalence.counitIso.inv.app (jy.obj W)))
      hqxStepToMap
    convert hstep using 1 <;> rfl
  have hbetaMapDecomp :
      B.inclusion.map (Over.Hom.left (hbeta.app W)) =
        B.inclusion.map (Over.Hom.left (hcomm.hom.app (qx.inv.obj (jx.obj (bc.obj W))))) ≫
        B.inclusion.map (Over.Hom.left
          ν) ≫
        B.inclusion.map (Over.Hom.left ((Over.map fpb).map (hbase.hom.app W))) ≫
        B.inclusion.map (pullback.fst (jy.obj W).hom fpb) ≫
        B.inclusion.map (Over.Hom.left
          (qy.asEquivalence.counitIso.inv.app (jy.obj W))) := by
    show (Over.Hom.left (hbeta.app W)).hom =
      (Over.Hom.left (hcomm.hom.app (qx.inv.obj (jx.obj (bc.obj W))))).hom ≫
        (Over.Hom.left ν).hom ≫
        (Over.Hom.left ((Over.map fpb).map (hbase.hom.app W))).hom ≫
        (pullback.fst (jy.obj W).hom fpb).hom ≫
        (Over.Hom.left (qy.asEquivalence.counitIso.inv.app (jy.obj W))).hom
    exact congrArg (fun k => k.hom) hbetaLeftDecomp
  have hbeta_factor :
      B.inclusion.map (Over.Hom.left (hbeta.app W)) ≫ B.inclusion.map ey.left =
        B.inclusion.map ex.left ≫
          (B.inclusion.map (Over.Hom.left (hbase.hom.app W)) ≫
            B.inclusion.map (pullback.fst (jy.obj W).hom fpb)) := by
    have hcommStep :
        eqToHom hcommObjEq ≫
          B.inclusion.map (Over.Hom.left
            ν) =
        B.inclusion.map (Over.Hom.left ex) :=
      eq_of_heq ((eqToHom_comp_heq
        (B.inclusion.map (Over.Hom.left
          ν))
        hcommObjEq).trans (heq_of_eq hqxStepMap))
    have hsuffix := congrArg (fun k => k ≫
      B.inclusion.map (Over.Hom.left (hbase.hom.app W)) ≫
      B.inclusion.map (pullback.fst (jy.obj W).hom fpb) ≫
      B.inclusion.map (Over.Hom.left (qy.asEquivalence.counitIso.inv.app (jy.obj W))) ≫
      B.inclusion.map ey.left) hcommStep
    let middle := B.inclusion.map ex.left ≫
      B.inclusion.map (Over.Hom.left (hbase.hom.app W)) ≫
      B.inclusion.map (pullback.fst (jy.obj W).hom fpb) ≫
      B.inclusion.map (Over.Hom.left (qy.asEquivalence.counitIso.inv.app (jy.obj W))) ≫
      B.inclusion.map ey.left
    have hfirst :
        B.inclusion.map (Over.Hom.left (hbeta.app W)) ≫ B.inclusion.map ey.left = middle := by
      rw [hbetaMapDecomp, hcommLeftMap', Over.map_map_left]
      convert hsuffix using 1 <;> (try simp only [Category.assoc]) <;> rfl
    have hsecond : middle =
        B.inclusion.map ex.left ≫
          (B.inclusion.map (Over.Hom.left (hbase.hom.app W)) ≫
            B.inclusion.map (pullback.fst (jy.obj W).hom fpb)) := by
      dsimp [middle]
      rw [hqyCancelUnderlying]
      simp
    exact hfirst.trans hsecond
  have hprojLocal := hproj
  rw [← hcx, ← hcy] at hprojLocal
  have hproj_factor :
      B.inclusion.map (Over.Hom.left (p.map f')) ≫ B.inclusion.map ey.left =
        B.inclusion.map ex.left ≫ E.inclusion.map (pullback.fst W.obj.hom a) := by
    show (Over.Hom.left (p.map f')).hom ≫ B.inclusion.map ey.left =
      (Over.Hom.left ex).hom ≫ (pullback.fst W.obj.hom a).hom
    exact hprojLocal
  let qyff := Functor.FullyFaithful.ofFullyFaithful qy
  let candidate : Xfun.obj W ⟶ Yfun.obj W := Over.homMk f' hsq
  have hcandidateMap :
      B.inclusion.map (Over.Hom.left (qy.map candidate)) =
        B.inclusion.map (Over.Hom.left (p.map f')) := rfl
  have hprojectionAfterEx :
      B.inclusion.map ex.left ≫
        (B.inclusion.map (Over.Hom.left (hbase.hom.app W)) ≫
          B.inclusion.map (pullback.fst (jy.obj W).hom fpb)) =
        B.inclusion.map ex.left ≫ E.inclusion.map (pullback.fst W.obj.hom a) := by
    show (Over.Hom.left ex).hom ≫
        ((Over.Hom.left (hbase.hom.app W)).hom ≫ (pullback.fst (jy.obj W).hom fpb).hom) =
      (Over.Hom.left ex).hom ≫ (pullback.fst W.obj.hom a).hom
    rw [hbaseProjectionHom]
  have hα : qyff.preimage (hbeta.app W) = candidate := by
    apply qy.map_injective
    rw [qyff.map_preimage]
    apply Over.OverMorphism.ext
    apply B.inclusion.map_injective
    apply (cancel_mono (B.inclusion.map ey.left)).mp
    exact hbeta_factor.trans hprojectionAfterEx |>.trans (by
      rw [← hproj_factor, hcandidateMap])
  show F.map (((Over.forget y).map (qyff.preimage (hbeta.app W))).op) = F.map f'.op
  rw [hα]
  rfl

/-- **Stacks 06W2.** The comparison with the direct image is natural in the presheaf. -/
@[stacks 06W2 "functoriality in the presheaf"]
theorem restrictionPushforwardComparison_naturality {𝒳 : Type v} [Category.{w} 𝒳]
    (p : 𝒳 ⥤ BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids) {x y : 𝒳} (φ : x ⟶ y)
    {A : Type t} [Category.{s} A] {F G : 𝒳ᵒᵖ ⥤ A} (η : F ⟶ G)
    (W : SmallEtale E (p.obj y).left.1 (contains_base B E h S hS p y)) :
    letI : (Over.post (X := x) (p ⋙ Over.forget (B.obj hS))).IsEquivalence :=
      isEquivalence_overPost B S hS p hp x
    letI : (Over.post (X := y) (p ⋙ Over.forget (B.obj hS))).IsEquivalence :=
      isEquivalence_overPost B S hS p hp y
    let y' := (Over.post (X := y) (p ⋙ Over.forget (B.obj hS))).inv.obj
      ((smallEtaleInclusion B E h (p.obj y).left.1 (contains_base B E h S hS p y)).obj W)
    let x' := (Over.post (X := x) (p ⋙ Over.forget (B.obj hS))).inv.obj
      ((smallEtaleInclusion B E h (p.obj x).left.1 (contains_base B E h S hS p x)).obj
        ((smallEtaleBaseChange E (smallEtaleBaseMorphism B E h S hS p φ)).obj W))
    (restrictionPushforwardComparison B E h S hS p hp φ F).app (Opposite.op W) ≫
        η.app (Opposite.op x'.left) =
      η.app (Opposite.op y'.left) ≫
        (restrictionPushforwardComparison B E h S hS p hp φ G).app (Opposite.op W) := by
  classical
  simp [restrictionPushforwardComparison]

end AlgebraicGeometry.Stack

namespace CategoryTheory

/-- A functor preserving fibre products is cover-preserving for a topology generated by a
precoverage as soon as it carries each generating family to a covering sieve.

This belongs with the general theory of cover-preserving functors; it is stated here because
no module of the library yet collects the generation criteria. -/
lemma coverPreserving_toGrothendieck_of_generators {C D : Type*} [Category C] [Category D]
    [HasPullbacks C] (G : C ⥤ D) [PreservesLimitsOfShape WalkingCospan G]
    (P : Precoverage C) (K : GrothendieckTopology D)
    (hgen : ∀ {X : C} {R : Presieve X}, R ∈ P X →
      (Sieve.generate R).functorPushforward G ∈ K (G.obj X)) :
    CoverPreserving P.toGrothendieck K G := by
  refine ⟨fun {X S} hS => ?_⟩
  induction hS with
  | of X R hR => exact hgen hR
  | top X => simp
  | pullback X S hS Y f ih =>
      exact K.superset_covering (by
        intro Z t ht
        obtain ⟨V, g, k, hg, e⟩ := ht
        let hpb := (IsPullback.of_hasPullback g f).map G
        let l := hpb.lift k t (by simpa using e.symm)
        refine ⟨pullback g f, pullback.snd g f, l, ?_, ?_⟩
        · show S (pullback.snd g f ≫ f)
          rw [← pullback.condition]
          exact S.downward_closed hg (pullback.fst g f)
        · exact (hpb.lift_snd _ _ _).symm) (K.pullback_stable (G.map f) ih)
  | transitive X S R hS hR ihS ihR =>
      apply K.transitive ihS
      intro Y t ht
      obtain ⟨Z, g, k, hg, e⟩ := ht
      have hk := K.pullback_stable k (ihR hg)
      refine K.superset_covering ?_ hk
      intro W q hq
      have hq' := (Sieve.functorPushforward_pullback_le G g R) (q ≫ k) hq
      change (R.functorPushforward G) ((q ≫ k) ≫ G.map g) at hq'
      show (R.functorPushforward G) (q ≫ t)
      rw [e]
      simpa only [Category.assoc] using hq'

end CategoryTheory

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (E : BigEtaleSite.{u}) (h : E.cutoff = B.cutoff)
  (S : Scheme.{u}) (hS : B.Contains S)

/-- The change of size cutoff from a big étale site to a big fppf site with the same cutoff is
continuous from the big étale topology over a scheme to the localized étale topology of the
fppf site: the two sites have the same selected étale covering families up to combinatorial
equivalence. -/
private theorem isContinuous_overPost_cutoff (U : Scheme.{u}) (hU : E.Contains U) :
    (Over.post (X := E.obj U hU) (ObjectProperty.ιOfLE (P := schemeSizeBelow E.cutoff)
      (P' := schemeSizeBelow B.cutoff) (by intro X hX; simpa [h] using hX))).IsContinuous
      (BigEtaleOver.topology E U hU)
      ((etaleTopology B).over (B.obj (show B.Contains U from by simpa [h] using hU))) := by
  let I := ObjectProperty.ιOfLE (P := schemeSizeBelow E.cutoff)
    (P' := schemeSizeBelow B.cutoff) (by intro X hX; simpa [h] using hX)
  let G := Over.post (X := E.obj U hU) I
  let K := (etaleTopology B).over (B.obj (show B.Contains U from by simpa [h] using hU))
  let P := BigEtaleOver.precoverage E U hU
  let : I.IsEquivalence := (ObjectProperty.isEquivalence_ιOfLE_iff _).2 fun X hX =>
    (schemeSizeBelow E.cutoff).le_isoClosure X (by simpa [schemeSizeBelow, h] using hX)
  let : G.IsEquivalence := by infer_instance
  let : PreservesLimitsOfShape WalkingCospan G := by infer_instance
  have hcp : CoverPreserving P.toGrothendieck K G := by
    apply coverPreserving_toGrothendieck_of_generators G P K
    intro X R hR
    obtain ⟨C, rfl, hC⟩ := (BigEtaleOver.mem_precoverage_iff E U hU).1 hR
    let C₀ : Covering E.Scheme := ⟨X.left, C.map (Over.forget (E.obj U hU))⟩
    have hC₀ : E.IsCovering C₀ := by
      simpa [C₀, BigEtaleOver.IsCovering] using hC
    let W : Covering B.Schemes := ⟨I.obj X.left, C₀.2.map I⟩
    have hmap : (C₀.2.map I).map (schemeBelowInclusion B.cutoff) =
        C₀.2.map (schemeBelowInclusion E.cutoff) := by
      ext <;> simp [C₀, I, schemeBelowInclusion, PreZeroHypercover.map]
    have hW : IsEtaleCovering W := by
      show ((C₀.2.map I).map (schemeBelowInclusion B.cutoff)).presieve₀ ∈
        Scheme.etalePrecoverage ((schemeBelowInclusion B.cutoff).obj (I.obj X.left))
      rw [hmap]
      show (C₀.2.map (schemeBelowInclusion E.cutoff)).presieve₀ ∈
        Scheme.etalePrecoverage ((schemeBelowInclusion E.cutoff).obj X.left)
      exact BigEtaleSite.IsCovering.etale hC₀
    obtain ⟨W', hW', hComb⟩ := etaleCovering_has_representative B W hW
    rcases W' with ⟨Wtarget, Wfam⟩
    have htarget : I.obj X.left = Wtarget := hComb.1
    cases htarget
    have hPres : (C₀.2.map I).presieve₀ = Wfam.presieve₀ :=
      PreZeroHypercover.presieve₀_eq_of_combinatoriallyEquivalent hComb.2
    have hbase : Sieve.generate Wfam.presieve₀ ∈ etaleTopology B (I.obj X.left) := by
      rw [etaleTopology]
      exact Precoverage.generate_mem_toGrothendieck ⟨Wfam, rfl, hW'⟩
    rw [← congrArg Sieve.generate hPres] at hbase
    dsimp [G, K]
    rw [GrothendieckTopology.mem_over_iff]
    erw [Sieve.overEquiv_functorPushforward_post]
    rw [Sieve.overEquiv_generate]
    have hsrc : Sieve.generate
        (Presieve.functorPushforward (Over.forget (E.obj U hU)) C.presieve₀) =
        Sieve.generate C₀.2.presieve₀ := by
      ext Y f
      simp [C₀, PreZeroHypercover.presieve₀_map,
        ← Sieve.arrows_generate_map_eq_functorPushforward]
    rw [hsrc]
    rw [PreZeroHypercover.presieve₀_map, Sieve.generate_map_eq_functorPushforward] at hbase
    show Sieve.functorPushforward I (Sieve.generate C₀.2.presieve₀) ∈
      etaleTopology B (I.obj X.left)
    exact hbase
  let : G.IsRightAdjoint := by infer_instance
  let : RepresentablyFlat G := inferInstance
  exact Functor.isContinuous_iff_coverPreserving.mpr hcp

/-- **Stacks 06W3.** The restriction of an étale sheaf on a category fibred in groupoids to the
small étale site of the scheme an object lies over is a sheaf, not merely a presheaf whose
sheafification is of interest. -/
@[stacks 06W3 "the restriction is a sheaf"]
theorem restrictToSmallEtale_isSheaf {𝒳 : Type v} [Category.{w} 𝒳]
    (p : 𝒳 ⥤ BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids) (x : 𝒳)
    (F : Sheaf (associatedTopology B S hS p (etaleTopology B)) (Type (max (u + 1) t))) :
    Presheaf.IsSheaf
      (SmallEtale.topology E (p.obj x).left.1 (contains_base B E h S hS p x))
      (restrictToSmallEtale B E h S hS p hp x F.obj) := by
  let U := (p.obj x).left.1
  let hU : E.Contains U := contains_base B E h S hS p x
  let J := SmallEtale.topology E U hU
  let Ubase := B.obj (show B.Contains U from by simpa [h] using hU)
  let K := (etaleTopology B).over Ubase
  let : (SmallEtale.inclusion E U hU).IsContinuous J (BigEtaleOver.topology E U hU) :=
    (smallEtaleInclusion_isMorphismOfSites E U hU).toIsContinuous
  let I := ObjectProperty.ιOfLE (P := schemeSizeBelow E.cutoff)
    (P' := schemeSizeBelow B.cutoff) (by intro X hX; simpa [h] using hX)
  let : (Over.post I).IsContinuous (BigEtaleOver.topology E U hU) K :=
    isContinuous_overPost_cutoff B E h U hU
  let : (smallEtaleInclusion B E h U hU).IsContinuous J K := by
    show (SmallEtale.inclusion E U hU ⋙ Over.post I).IsContinuous J K
    exact Functor.isContinuous_comp _ _ J (BigEtaleOver.topology E U hU) K
  let q := p ⋙ Over.forget (B.obj hS)
  let e := Over.post (X := x) q
  let L := (associatedTopology B S hS p (etaleTopology B)).over x
  let : e.IsEquivalence := isEquivalence_overPost B S hS p hp x
  let eEquiv := e.asEquivalence
  let : eEquiv.functor.IsEquivalence := Equivalence.isEquivalence_functor eEquiv
  let : eEquiv.inverse.IsEquivalence := Equivalence.isEquivalence_functor eEquiv.symm
  have hInd : e.inducedTopology K = L :=
    inducedTopology_overPost B S hS p hp (etaleTopology B) x
  let : eEquiv.inverse.IsDenseSubsite K L := by
    have htop2 : K = eEquiv.inverse.inducedTopology (eEquiv.functor.inducedTopology K) := by
      ext X T
      simp only [Functor.mem_inducedTopology_iff_of_isCoverDense]
      have hEq := Sieve.functorPushforward_equivalence_eq_pullback eEquiv.symm T
      have hEq' : Sieve.functorPushforward eEquiv.functor
          (Sieve.functorPushforward eEquiv.inverse T) =
          T.pullback (eEquiv.symm.unitInv.app X) := by
        simpa only [Equivalence.symm_inverse, Equivalence.symm_functor] using hEq
      rw [hEq']
      exact (K.pullback_mem_iff_of_isIso (i := eEquiv.symm.unitInv.app X) (S := T)).symm
    have hd : eEquiv.inverse.IsDenseSubsite K (eEquiv.functor.inducedTopology K) := by
      nth_rw 1 [htop2]
      infer_instance
    have hInd' : eEquiv.functor.inducedTopology K = L := by
      simpa [eEquiv, e] using hInd
    rw [← hInd']
    exact hd
  have hInvCont : eEquiv.inverse.IsContinuous K L := by
    have hEq : K = eEquiv.inverse.inducedTopology L :=
      eEquiv.eq_inducedTopology_of_isDenseSubsite L K
    rw [hEq]
    exact (Functor.le_inducedTopology_iff).1 le_rfl
  let : e.inv.IsContinuous K L := by
    show eEquiv.inverse.IsContinuous K L
    exact hInvCont
  let : (Over.forget x).IsContinuous L (associatedTopology B S hS p (etaleTopology B)) :=
    inferInstance
  let : (smallEtaleInclusion B E h U hU ⋙ e.inv ⋙ Over.forget x).IsContinuous J
      (associatedTopology B S hS p (etaleTopology B)) := by
    have h₁ := Functor.isContinuous_comp (smallEtaleInclusion B E h U hU) e.inv J K L
    exact Functor.isContinuous_comp (smallEtaleInclusion B E h U hU ⋙ e.inv)
      (Over.forget x) J L (associatedTopology B S hS p (etaleTopology B))
  show Presheaf.IsSheaf J
    ((smallEtaleInclusion B E h U hU).op ⋙
      (Over.post (X := x) (p ⋙ Over.forget (B.obj hS))).inv.op ⋙
      (Over.forget x).op ⋙ F.obj)
  exact (smallEtaleInclusion B E h U hU ⋙ e.inv ⋙ Over.forget x).op_comp_isSheaf_of_isSheaf
    (J := J) (K := associatedTopology B S hS p (etaleTopology B)) F.obj F.property

/-- **Stacks 06W1**, part (2), for an étale sheaf. The restriction of an étale sheaf on a
category fibred in groupoids to the small étale site of the scheme an object lies over, as a
sheaf on that site. -/
noncomputable def restrictToSmallEtaleSheaf {𝒳 : Type v} [Category.{w} 𝒳]
    (p : 𝒳 ⥤ BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids) (x : 𝒳)
    (F : Sheaf (associatedTopology B S hS p (etaleTopology B)) (Type (max (u + 1) t))) :
    Sheaf (SmallEtale.topology E (p.obj x).left.1 (contains_base B E h S hS p x))
      (Type (max (u + 1) t)) :=
  ⟨restrictToSmallEtale B E h S hS p hp x F.obj,
    restrictToSmallEtale_isSheaf B E h S hS p hp x F⟩

/-- **Stacks 06W3.** The comparison `c_φ : a_{small}^{-1}(F|_{V_ét}) ⟶ F|_{U_ét}` from the
inverse image of the restriction at the target of an arrow `φ : x ⟶ y` to the restriction at
its source, the mate of the direct-image comparison of Stacks 06W2 under the
pullback–pushforward adjunction on small étale sheaves. -/
@[stacks 06W3 "the comparison with the inverse image"]
noncomputable def restrictionInverseImageComparison {𝒳 : Type v} [Category.{w} 𝒳]
    (p : 𝒳 ⥤ BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids) {x y : 𝒳} (φ : x ⟶ y)
    (F : Sheaf (associatedTopology B S hS p (etaleTopology B)) (Type (max (u + 1) t))) :
    ((smallEtaleBaseChange E (smallEtaleBaseMorphism B E h S hS p φ)).sheafPullback
        (Type (max (u + 1) t))
        (SmallEtale.topology E (p.obj y).left.1 (contains_base B E h S hS p y))
        (SmallEtale.topology E (p.obj x).left.1 (contains_base B E h S hS p x))).obj
      (restrictToSmallEtaleSheaf B E h S hS p hp y F) ⟶
    restrictToSmallEtaleSheaf B E h S hS p hp x F :=
  letI Jy := SmallEtale.topology E (p.obj y).left.1 (contains_base B E h S hS p y)
  letI Jx := SmallEtale.topology E (p.obj x).left.1 (contains_base B E h S hS p x)
  letI G := smallEtaleBaseChange E (smallEtaleBaseMorphism B E h S hS p φ)
  letI Sy := restrictToSmallEtaleSheaf B E h S hS p hp y F
  letI Sx := restrictToSmallEtaleSheaf B E h S hS p hp x F
  ((G.sheafAdjunctionContinuous (Type (max (u + 1) t)) Jy Jx).homEquiv Sy Sx).symm
    (Sheaf.homEquiv.symm
      (restrictionPushforwardComparison B E h S hS p hp φ F.obj :
        Sy.obj ⟶ ((G.sheafPushforwardContinuous (Type (max (u + 1) t)) Jy Jx).obj Sx).obj))

end AlgebraicGeometry.Stack

end
