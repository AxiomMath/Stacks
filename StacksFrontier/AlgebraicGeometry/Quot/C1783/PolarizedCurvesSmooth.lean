module

public import StacksFrontier.AlgebraicGeometry.Quot.C1783.PolarizedCurvesSmoothLift
public import StacksFrontier.AlgebraicGeometry.Quot.PolarizedCurvesToCurvesAlgebraic
public import StacksFrontier.AlgebraicGeometry.Stacks.Criteria.FormallySmoothFaithfulTarget
public import StacksFrontier.AlgebraicGeometry.Stacks.FormallySmoothOnObjectsLifting
public import StacksFrontier.AlgebraicGeometry.Stacks.LimitPreservingObjectsFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparatedDiagonalTFAE
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothFormallySmooth
public import StacksFrontier.CategoryTheory.FiberedCategory.ShrinkHomsBasedCategory

/-!
# Smoothness of the base changes of `PolarizedCurves ⟶ 𝒞urves`

The second assertion of Stacks 0D5C left to prove is that `PolarizedCurves ⟶ 𝒞urves` is smooth:
its base change along every scheme point `z : (Sch/Z) ⟶ 𝒞urves` is smooth over `Z`. By the
infinitesimal lifting criterion (Stacks 0DP0) a 1-morphism of algebraic stacks is smooth once it
is locally of finite presentation and formally smooth on objects (Stacks 06D0), the source's route
through Stacks 0DQ0.

Formal smoothness on objects is proved here outright. The target `(Sch/Z)` of the base change has
a faithful structure functor, so it suffices to solve the first-order lifting problems of
`PolarizedCurves ⟶ 𝒞urves` itself, which is
`AlgebraicGeometry.C1783.hasFirstOrderObjectLifts_polarizedCurvesToCurves`
(Stacks 0DPJ: the polarization of a curve lifts along a first-order thickening of an affine base),
read on the small models of `AlgebraicGeometry.polarizedCurvesSmall`
and `AlgebraicGeometry.curvesSmall`.

Local finite presentation is reduced to limit preservation on objects (Stacks 06CU, through the
implication (2) `⇒` (3) of Stacks 0CMY) of the small model
`AlgebraicGeometry.polarizedCurvesSmallToCurvesSmall`, which is
inherited by its base changes; that limit preservation is the hypothesis `hlim` of the last result,
discharged in `StacksFrontier.AlgebraicGeometry.Quot.C1783.PolarizedCurvesSmoothLimit`.

## Main results

All names below are in the namespace `AlgebraicGeometry.C1783`.

* `hasFirstOrderObjectLifts_polarizedCurvesSmallToCurvesSmall`:
  the first-order lifting property of the small model of `PolarizedCurves ⟶ 𝒞urves`.
* `isFormallySmoothOnObjects_baseChange_polarizedCurvesSmall`:
  the base change along a scheme point is formally smooth on objects.
* `hasPropertyOnSomeSmoothDiagram_baseChange_polarizedCurvesSmall_of_isLimitPreservingOnObjects`:
  the base change along a scheme point is smooth, given that it is algebraic and that
  `PolarizedCurves ⟶ 𝒞urves` is limit preserving on objects.

## References

* [Stacks Project, Tag 0D5C](https://stacks.math.columbia.edu/tag/0D5C)
* [Stacks Project, Tag 0DQ0](https://stacks.math.columbia.edu/tag/0DQ0)
* [Stacks Project, Tag 0DP0](https://stacks.math.columbia.edu/tag/0DP0)
* [Stacks Project, Tag 06D0](https://stacks.math.columbia.edu/tag/06D0)
* [Stacks Project, Tag 06CU](https://stacks.math.columbia.edu/tag/06CU)
* [Stacks Project, Tag 0CMY](https://stacks.math.columbia.edu/tag/0CMY)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe w₀ u

namespace AlgebraicGeometry.C1783

variable (B : BigFppfSite.{u}) (hZ : B.Contains integerBase)
  (h3Z : (polarizedProjection B ⋙ schemeOverIntegers B).IsFiberedInGroupoids)

omit B hZ h3Z in
/-- Inverting the last arrow of a commutative square whose top is an isomorphism. -/
private theorem comp_inv_eq_of_comp_eq {C : Type*} [Category C] {a b d e : C} (f : a ⟶ b)
    (s : a ≅ d) (g : d ⟶ e) (k : e ⟶ b) [IsIso k] (h : g ≫ k = s.inv ≫ f) :
    f ≫ inv k = s.hom ≫ g := by
  rw [IsIso.comp_inv_eq, Category.assoc, h, Iso.hom_inv_id_assoc]

omit B hZ h3Z in
/-- A morphism of a shrunk category lies over `f` exactly when its image in the original category
does. -/
theorem isHomLift_shrinkHomsInverse_comp_iff.{w, v, v', t, t'} {C : Type t} [Category.{v} C]
    [LocallySmall.{w} C] {D : Type t'} [Category.{v'} D] (p : C ⥤ D) {R S : D}
    {X Y : ShrinkHoms.{t} C} (f : R ⟶ S) (φ : X ⟶ Y) :
    (ShrinkHoms.inverse.{w} C ⋙ p).IsHomLift f φ ↔
      p.IsHomLift f ((ShrinkHoms.inverse.{w} C).map φ) :=
  ⟨fun _ => IsHomLift.of_fac' _ _ _ (IsHomLift.domain_eq (ShrinkHoms.inverse.{w} C ⋙ p) f φ)
      (IsHomLift.codomain_eq (ShrinkHoms.inverse.{w} C ⋙ p) f φ)
      (IsHomLift.fac' (ShrinkHoms.inverse.{w} C ⋙ p) f φ),
    fun _ => IsHomLift.of_fac' _ _ _ (IsHomLift.domain_eq p f ((ShrinkHoms.inverse.{w} C).map φ))
      (IsHomLift.codomain_eq p f ((ShrinkHoms.inverse.{w} C).map φ))
      (IsHomLift.fac' p f ((ShrinkHoms.inverse.{w} C).map φ))⟩

omit B hZ h3Z in
/-- Shrinking the hom types and coming back is the identity on morphisms. -/
theorem shrinkHomsInverse_map_functor_map.{w, v, t} {C : Type t} [Category.{v} C]
    [LocallySmall.{w} C] {X Y : C} (g : X ⟶ Y) :
    (ShrinkHoms.inverse.{w} C).map ((ShrinkHoms.functor.{w} C).map g) = g :=
  (equivShrink _).symm_apply_apply g

omit B hZ h3Z in
/-- Coming back from the shrunk hom types and shrinking again is the identity on morphisms. -/
theorem shrinkHomsFunctor_map_inverse_map.{w, v, t} {C : Type t} [Category.{v} C]
    [LocallySmall.{w} C] {X Y : ShrinkHoms.{t} C} (g : X ⟶ Y) :
    (ShrinkHoms.functor.{w} C).map ((ShrinkHoms.inverse.{w} C).map g) = g :=
  (equivShrink _).apply_symm_apply g

omit B hZ h3Z in
/-- The shrunk image of a morphism lying over `f` lies over `f`. -/
theorem isHomLift_shrinkHomsFunctor_map.{w, v, v', t, t'} {C : Type t} [Category.{v} C]
    [LocallySmall.{w} C] {D : Type t'} [Category.{v'} D] (p : C ⥤ D) {R S : D} {X Y : C}
    (f : R ⟶ S) (g : X ⟶ Y) (h : p.IsHomLift f g) :
    (ShrinkHoms.inverse.{w} C ⋙ p).IsHomLift f ((ShrinkHoms.functor.{w} C).map g) := by
  refine (isHomLift_shrinkHomsInverse_comp_iff p f _).2 ?_
  rw [show (ShrinkHoms.inverse.{w} C).map ((ShrinkHoms.functor.{w} C).map g) = g from
    (equivShrink _).symm_apply_apply g]
  exact h

omit B hZ h3Z in
/-- A factorization `G b ≫ c = a` read through the shrunk hom types. -/
private theorem shrinkHoms_map_comp_eq.{w, v, v', t, t'} {C : Type t} [Category.{v} C]
    [LocallySmall.{w} C] {E : Type t'} [Category.{v'} E] [LocallySmall.{w} E] (G : C ⥤ E)
    {X X' : C} {Y : ShrinkHoms.{t'} E} (b : X ⟶ X') (c : G.obj X' ⟶ ShrinkHoms.fromShrinkHoms Y)
    (a : ShrinkHoms.toShrinkHoms (G.obj X) ⟶ Y)
    (h : G.map b ≫ c = (ShrinkHoms.inverse.{w} E).map a) :
    (ShrinkHoms.functor.{w} E).map
        (G.map ((ShrinkHoms.inverse.{w} C).map ((ShrinkHoms.functor.{w} C).map b))) ≫
      (ShrinkHoms.functor.{w} E).map c = a := by
  rw [show (ShrinkHoms.inverse.{w} C).map ((ShrinkHoms.functor.{w} C).map b) = b from
    (equivShrink _).symm_apply_apply b]
  exact ((ShrinkHoms.functor.{w} E).map_comp (G.map b) c).symm.trans
    ((congrArg (ShrinkHoms.functor.{w} E).map h).trans ((equivShrink _).apply_symm_apply a))

/-- **The small model of `PolarizedCurves ⟶ 𝒞urves` has the first-order lifting property**
(Stacks 06D0): `AlgebraicGeometry.C1783.hasFirstOrderObjectLifts_polarizedCurvesToCurves`
read through the shrinking of the hom types, which changes neither objects nor projections. -/
private theorem hasFirstOrderObjectLifts_polarizedCurvesSmallToCurvesSmall :
    Stack.HasFirstOrderObjectLifts B integerBase hZ
      (polarizedCurvesSmallToCurvesSmall B hZ h3Z) := by
  let := locallySmall_polarizedCurves B hZ h3Z
  let : LocallySmall.{u} (polarizedCurvesSquare B hZ h3Z).pt.val.obj :=
    locallySmall_polarizedCurves B hZ h3Z
  let := locallySmall_curveFamily B hZ
  let : LocallySmall.{u} (curvesFiberedCategory B hZ).val.obj := locallySmall_curveFamily B hZ
  intro U U' i hU hU' hi x y' a ha
  let PC := (polarizedCurvesFiberedCategory B hZ h3Z).val.obj
  let a' : (CatFiberedInGroupoids.homFunctor (polarizedCurvesSquare B hZ h3Z).snd).obj
      (ShrinkHoms.inverse.{u} PC |>.obj x.1) ⟶
        ShrinkHoms.inverse.{u} (CurveFamily B hZ) |>.obj y'.1 :=
    (ShrinkHoms.inverse.{u} (CurveFamily B hZ)).map a
  have ha' : (curvesFiberedCategory B hZ).val.p.IsHomLift i a' :=
    (isHomLift_shrinkHomsInverse_comp_iff (curvesProjectionOver B hZ) i a).1 ha
  obtain ⟨x'', b, c, hb, hc, hbc⟩ := hasFirstOrderObjectLifts_polarizedCurvesToCurves B hZ h3Z
    U U' i hU hU' hi ⟨ShrinkHoms.inverse.{u} PC |>.obj x.1, x.2⟩
    ⟨ShrinkHoms.inverse.{u} (CurveFamily B hZ) |>.obj y'.1, y'.2⟩ a' ha'
  refine ⟨⟨ShrinkHoms.toShrinkHoms x''.1, x''.2⟩, (ShrinkHoms.functor.{u} PC).map b,
    (ShrinkHoms.functor.{u} (CurveFamily B hZ)).map c, ?_, ?_, ?_⟩
  · exact isHomLift_shrinkHomsFunctor_map (polarizedCurvesFiberedCategory B hZ h3Z).val.p i b hb
  · exact isHomLift_shrinkHomsFunctor_map (curvesProjectionOver B hZ) _ c hc
  · exact shrinkHoms_map_comp_eq
      (CatFiberedInGroupoids.homFunctor (polarizedCurvesSquare B hZ h3Z).snd) b c a hbc

/-- **The base change of `PolarizedCurves ⟶ 𝒞urves` along a scheme point is formally smooth on
objects** (Stacks 06D0). The target `(Sch/Z)` has a faithful structure functor, so a lift of an
object over the thickening together with a morphism from the given one suffices
(`AlgebraicGeometry.Stack.isFormallySmoothOnObjects_of_faithful_of_exists_lift`); it is assembled
from the first-order lift of the polarized curve, the identification with the point being
transported along the vertical comparison, which is an isomorphism. -/
private theorem isFormallySmoothOnObjects_baseChange_polarizedCurvesSmall
    (Z : BigFppfOver B integerBase hZ)
    (z : BigFppfOver B Z.left.1 Z.left.2 ⥤ (curvesSmall B hZ).val.obj)
    (hz : z ⋙ (curvesSmall B hZ).val.p = Over.map Z.hom) :
    Stack.IsFormallySmoothOnObjects B integerBase hZ
      (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1}
        (Stack.schemeSliceMap B integerBase hZ Z z hz)
        (polarizedCurvesSmallToCurvesSmall B hZ h3Z)).pt
      (Stack.schemeSlice B integerBase hZ Z)
      (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1}
        (Stack.schemeSliceMap B integerBase hZ Z z hz)
        (polarizedCurvesSmallToCurvesSmall B hZ h3Z)).fst := by
  have : (Stack.schemeSlice B integerBase hZ Z).val.p.Faithful := by
    change (Over.map Z.hom).Faithful
    infer_instance
  refine Stack.isFormallySmoothOnObjects_of_faithful_of_exists_lift ?_
  intro U U' i hU hU' hi x hx y' hy' ψ hψ
  subst hx hy'
  let Fs := CatFiberedInGroupoids.homFunctor (polarizedCurvesSmallToCurvesSmall B hZ h3Z)
  have hCs := (curvesSmall B hZ).isFiberedInGroupoids
  have hzψ : (curvesSmall B hZ).val.p.IsHomLift i (z.map ψ) := by
    have h : (z ⋙ (curvesSmall B hZ).val.p).IsHomLift i ψ := by rwa [hz]
    exact IsHomLift.of_fac' _ _ _ (IsHomLift.domain_eq (z ⋙ (curvesSmall B hZ).val.p) i ψ)
      (IsHomLift.codomain_eq (z ⋙ (curvesSmall B hZ).val.p) i ψ)
      (IsHomLift.fac' (z ⋙ (curvesSmall B hZ).val.p) i ψ)
  have hiso : (curvesSmall B hZ).val.p.IsHomLift (𝟙 x.base) x.iso.inv := by
    have := x.vertical
    infer_instance
  have := hzψ
  have ha : (curvesSmall B hZ).val.p.IsHomLift i (x.iso.inv ≫ z.map ψ) :=
    @IsHomLift.comp_lift_id_left' _ _ _ _ (curvesSmall B hZ).val.p _ _ _ x.base x.iso.inv hiso
      _ _ i (z.map ψ) hzψ
  obtain ⟨x'', b, c, hb, hc, hbc⟩ :=
    hasFirstOrderObjectLifts_polarizedCurvesSmallToCurvesSmall B hZ h3Z x.base _ i hU hU' hi
      ⟨x.y, x.hy⟩ ⟨z.obj y', IsHomLift.codomain_eq (curvesSmall B hZ).val.p i (z.map ψ)⟩
      (x.iso.inv ≫ z.map ψ) ha
  have := hc
  have : IsIso c := by
    have := hCs.isStronglyCartesian_homLift
      (𝟙 ((Stack.schemeSlice B integerBase hZ Z).val.p.obj y')) c
    exact Functor.IsStronglyCartesian.isIso_of_base_isIso (p := (curvesSmall B hZ).val.p)
      (f := 𝟙 ((Stack.schemeSlice B integerBase hZ Z).val.p.obj y')) c
  let x' : (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1}
      (Stack.schemeSliceMap B integerBase hZ Z z hz)
      (polarizedCurvesSmallToCurvesSmall B hZ h3Z)).pt.val.obj :=
    { base := (Stack.schemeSlice B integerBase hZ Z).val.p.obj y'
      x := y'
      y := x''.1
      hx := rfl
      hy := x''.2
      iso := (asIso c).symm
      vertical := by
        change (curvesSmall B hZ).val.p.IsHomLift _ (inv c)
        have h := IsHomLift.inv (curvesSmall B hZ).val.p
          (𝟙 ((Stack.schemeSlice B integerBase hZ Z).val.p.obj y')) c
        rwa [IsIso.inv_id] at h }
  have hw : z.map ψ ≫ x'.iso.hom = x.iso.hom ≫ Fs.map b :=
    comp_inv_eq_of_comp_eq _ _ _ _ hbc
  let β : x ⟶ x' :=
    { hbase := i
      a := ψ
      b := b
      ha := hψ
      hb := hb
      w := hw }
  refine ⟨x', rfl, β, ?_, 𝟙 y', ?_⟩
  · exact IsHomLift.of_fac' _ _ _ rfl rfl (by simp; rfl)
  · exact IsHomLift.id rfl

/-- **The base changes of `PolarizedCurves ⟶ 𝒞urves` are smooth** (the second assertion of
Stacks 0D5C, in the form consumed by
`AlgebraicGeometry.polarizedCurvesToCurves_isAlgebraic_smooth_surjective`), given that the
base change is an algebraic stack (`halg`, the first assertion) and that the small model of
`PolarizedCurves ⟶ 𝒞urves` is limit preserving on objects (`hlim`, Stacks 06CU). By Stacks 0DP0
the base change is smooth once it is locally of finite presentation, which follows from `hlim`
by Stacks 06CV and 0CMY, and formally smooth on objects, which is
`AlgebraicGeometry.C1783.isFormallySmoothOnObjects_baseChange_polarizedCurvesSmall`. -/
theorem hasPropertyOnSomeSmoothDiagram_baseChange_polarizedCurvesSmall_of_isLimitPreservingOnObjects
    (hlim : BigFppfOver.IsLimitPreservingOnObjects.{u, u, u} B integerBase hZ
      (polarizedCurvesSmall B hZ h3Z) (curvesSmall B hZ)
      (polarizedCurvesSmallToCurvesSmall B hZ h3Z))
    (Z : BigFppfOver B integerBase hZ)
    (z : BigFppfOver B Z.left.1 Z.left.2 ⥤ (curvesSmall B hZ).val.obj)
    (hz : z ⋙ (curvesSmall B hZ).val.p = Over.map Z.hom)
    (halg : Stack.IsAlgebraicStack.{u, w₀} B integerBase hZ
      (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1}
        (Stack.schemeSliceMap B integerBase hZ Z z hz)
        (polarizedCurvesSmallToCurvesSmall B hZ h3Z)).pt.val) :
    Stack.HasPropertyOnSomeSmoothDiagram B integerBase hZ
      (fun _ _ h => Space.IsSmooth B integerBase hZ h)
      (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1}
        (Stack.schemeSliceMap B integerBase hZ Z z hz)
        (polarizedCurvesSmallToCurvesSmall B hZ h3Z)).fst := by
  let Q := CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1}
    (Stack.schemeSliceMap B integerBase hZ Z z hz) (polarizedCurvesSmallToCurvesSmall B hZ h3Z)
  let 𝒳 : Stack.AlgebraicStacks.{u, w₀} B integerBase hZ := ⟨Q.pt, halg⟩
  let 𝒴 : Stack.AlgebraicStacks.{u, w₀} B integerBase hZ :=
    ⟨Stack.schemeSlice B integerBase hZ Z, Stack.isAlgebraicStack_schemeSlice.{u, w₀} B _ hZ Z⟩
  let f : 𝒳 ⟶ 𝒴 := Bicategory.InducedBicategory.mkHom Q.fst
  exact
    (Stack.AlgebraicStacks.isSmooth_iff_isLocallyOfFinitePresentation_and_isFormallySmoothOnObjects
      B integerBase hZ f).2
    ⟨Stack.AlgebraicStacks.isLocallyOfFinitePresentation_of_isLimitPreservingOnObjects B integerBase
        hZ f (BigFppfOver.isLimitPreservingOnObjects_twoFibreProductSquareFst B integerBase hZ _ _
          hlim),
      isFormallySmoothOnObjects_baseChange_polarizedCurvesSmall B hZ h3Z Z z hz⟩

end AlgebraicGeometry.C1783
