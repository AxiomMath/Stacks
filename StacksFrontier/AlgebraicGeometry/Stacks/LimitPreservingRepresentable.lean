module

public import Mathlib.AlgebraicGeometry.AffineTransitionLimit
public import Mathlib.CategoryTheory.Groupoid.Discrete
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Pullbacks
public import Mathlib.CategoryTheory.Limits.Types.Pullbacks
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.ProEtale.IndEtale.StandardVCoveringLimits
public import StacksFrontier.AlgebraicGeometry.Stacks.Algebraic.RepresentableBySpace.Basic
public import StacksFrontier.AlgebraicGeometry.Stacks.Algebraic.RepresentableBySpace.Characterization
public import StacksFrontier.AlgebraicGeometry.Morphisms.FinitePresentationPoint
public import StacksFrontier.AlgebraicGeometry.Spaces.Basic
public import StacksFrontier.AlgebraicGeometry.Spaces.Category
public import StacksFrontier.AlgebraicGeometry.Spaces.Coverings
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.Points
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallerBase
public import StacksFrontier.AlgebraicGeometry.Stacks.BaseChangeAlgebraicSpace
public import StacksFrontier.AlgebraicGeometry.Stacks.DiagonalOverTerminal
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeProperty
public import StacksFrontier.AlgebraicGeometry.Stacks.Representability
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.LimitPreservingOnObjects
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf
public import StacksFrontier.CategoryTheory.FiberedCategory.ChoiceOfPullbacks
public import StacksFrontier.CategoryTheory.FiberedCategory.FiberedInSetoids
public import StacksFrontier.CategoryTheory.FiberedCategory.OfPresheaf
public import StacksFrontier.CategoryTheory.FiberedCategory.PresheafElements
public import StacksFrontier.CategoryTheory.FiberedCategory.PresheafElementsEquivalence
public import StacksFrontier.CategoryTheory.FiberedCategory.SliceFunctorComparison
public import StacksFrontier.CategoryTheory.TwoFibreProductOverReindex
public import StacksFrontier.CategoryTheory.TwoYoneda.Fibered
public import StacksFrontier.RingTheory.Algebra.DirectLimit.FinitePresentation
/-!
# Checking a relative property of a representable 1-morphism on finitely presented affine bases

Let `f : 𝒳 ⟶ 𝒴` be a 1-morphism of categories fibred in groupoids over the big fppf site of a
scheme `S` which is representable by algebraic spaces, and let `P` be a property of morphisms of
algebraic spaces as in Stacks 03YK, that is, stable under base change and fppf local on the base.
If the structure morphism `𝒴 ⟶ (Sch/S)_{fppf}` is limit preserving on objects and the morphism of
algebraic spaces `F_y ⟶ V` of Stacks 0402 has `P` for every *affine* `V` locally of finite
presentation over `S` and every `y` of `𝒴` over `V`, then `f` has `P`.

## Main results

* `AlgebraicGeometry.Stack.hasRelativeProperty_of_affine_locallyOfFinitePresentation`:
  **Stacks 07WI**.

## Implementation notes

The source argues: `P` being fppf local on the base, one may assume the test scheme `V` affine and
mapping into an affine open `Spec Λ` of `S`; such a `V` is a directed limit of affine schemes of
finite presentation over `Spec Λ` by Stacks 00QN; limit preservation on objects moves the given
object `y` of `𝒴` over `V` to a finite stage `V_i`; the hypothesis applies at `V_i`; and `P` is
stable under base change along `V ⟶ V_i`.

Each of those steps is carried out on presheaves rather than on chosen representatives. The
property is tested on *every* algebraic space representing the 2-fibre product, as in the library's
rendering of Stacks 03YK, so no choice of representative is recorded and the base-change step is a
pullback square of presheaves transported along an isomorphism of representatives.

The directed limit of Stacks 00QN is produced as a cone in the site of affine schemes over `S`
whose image in schemes is a limit cone: `Spec` of the direct limit of the finitely presented
subalgebras of the coordinate ring. Local finite presentation of each stage over `Spec Λ` is read
off the finitely generated presentation.

*Universes.* Stacks 06CU as stated in the library compares a 1-morphism's source and target at a single universe
quadruple, and the target here is the site itself, so `𝒳` and `𝒴` are at the site's own universes,
as they are for `AlgebraicGeometry.Stack.IsAlgebraicStack`. The index universes of the
limit-preservation hypothesis stay free: the hypothesis is used at the universe of the coordinate
ring, which the proof reaches by replacing an index category with an equivalent one at those
universes.

## References

* [Stacks Project, Tag 07WI](https://stacks.math.columbia.edu/tag/07WI)
* [Stacks Project, Tag 03YK](https://stacks.math.columbia.edu/tag/03YK)
* [Stacks Project, Tag 0402](https://stacks.math.columbia.edu/tag/0402)
* [Stacks Project, Tag 06CU](https://stacks.math.columbia.edu/tag/06CU)
* [Stacks Project, Tag 00QN](https://stacks.math.columbia.edu/tag/00QN)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Stack

universe u u₁ u₂ v₁ v₂ v w

universe vI wI

attribute [local implicit_reducible] Functor.Fiber Functor.Fiber.fiberInclusion
  Functor.ChoiceOfPullbacks.sliceFunctor

universe vC uC uS


universe uX uY uZ uD vX vY vZ vD

attribute [local implicit_reducible] TwoFibreProductOver.reindex
  TwoFibreProductOver.reindexSymm TwoFibreProductOver.fst
private def reindexEquivalenceOver
    {C : Type uC} [Category.{vC} C] {X : Type uX} [Category.{vX} X]
    {Y : Type uY} [Category.{vY} Y] {Z : Type uZ} [Category.{vZ} Z]
    {pX : X ⥤ C} {pY : Y ⥤ C} {pZ : Z ⥤ C}
    {F F' : X ⥤ Z} {G : Y ⥤ Z}
    (α : F ≅ F') (hα : ∀ x, pZ.IsHomLift (𝟙 (pX.obj x)) (α.hom.app x)) :
    StacksRepresentableCFG.EquivalenceOver
      (TwoFibreProductOver.fst pX pY pZ F G)
      (TwoFibreProductOver.fst pX pY pZ F' G) where
  hom := ⟨TwoFibreProductOver.reindex α hα, TwoFibreProductOver.reindex_comp_fst α hα⟩
  inv := ⟨TwoFibreProductOver.reindexSymm α hα, TwoFibreProductOver.reindexSymm_comp_fst α hα⟩
  unitIso := NatIso.ofComponents (fun P => {
    hom := {
      hbase := 𝟙 P.base
      a := 𝟙 P.x
      b := 𝟙 P.y
      ha := IsHomLift.of_fac' pX _ _ P.hx P.hx (by
          change pX.map (𝟙 P.x) = eqToHom P.hx ≫ 𝟙 P.base ≫ eqToHom P.hx.symm
          simp)
      hb := IsHomLift.of_fac' pY _ _ P.hy P.hy (by
          change pY.map (𝟙 P.y) = eqToHom P.hy ≫ 𝟙 P.base ≫ eqToHom P.hy.symm
          simp)
      w := by simp [TwoFibreProductOver.reindexSymm, TwoFibreProductOver.reindex] }
    inv := {
      hbase := 𝟙 P.base
      a := 𝟙 P.x
      b := 𝟙 P.y
      ha := IsHomLift.of_fac' pX _ _ P.hx P.hx (by
          change pX.map (𝟙 P.x) = eqToHom P.hx ≫ 𝟙 P.base ≫ eqToHom P.hx.symm
          simp)
      hb := IsHomLift.of_fac' pY _ _ P.hy P.hy (by
          change pY.map (𝟙 P.y) = eqToHom P.hy ≫ 𝟙 P.base ≫ eqToHom P.hy.symm
          simp)
      w := by simp [TwoFibreProductOver.reindexSymm, TwoFibreProductOver.reindex] }
    hom_inv_id := by
      apply TwoFibreProductOver.Hom.ext' <;>
        simp [TwoFibreProductOver.reindexSymm, TwoFibreProductOver.reindex]
    inv_hom_id := by
      apply TwoFibreProductOver.Hom.ext' <;>
        simp [TwoFibreProductOver.reindexSymm, TwoFibreProductOver.reindex] })
    (by
      intro P Q f
      apply TwoFibreProductOver.Hom.ext' <;>
        simp [TwoFibreProductOver.reindexSymm, TwoFibreProductOver.reindex])
  counitIso := NatIso.ofComponents (fun P => {
    hom := {
      hbase := 𝟙 P.base
      a := 𝟙 P.x
      b := 𝟙 P.y
      ha := IsHomLift.of_fac' pX _ _ P.hx P.hx (by
          change pX.map (𝟙 P.x) = eqToHom P.hx ≫ 𝟙 P.base ≫ eqToHom P.hx.symm
          simp)
      hb := IsHomLift.of_fac' pY _ _ P.hy P.hy (by
          change pY.map (𝟙 P.y) = eqToHom P.hy ≫ 𝟙 P.base ≫ eqToHom P.hy.symm
          simp)
      w := by simp [TwoFibreProductOver.reindexSymm, TwoFibreProductOver.reindex] }
    inv := {
      hbase := 𝟙 P.base
      a := 𝟙 P.x
      b := 𝟙 P.y
      ha := IsHomLift.of_fac' pX _ _ P.hx P.hx (by
          change pX.map (𝟙 P.x) = eqToHom P.hx ≫ 𝟙 P.base ≫ eqToHom P.hx.symm
          simp)
      hb := IsHomLift.of_fac' pY _ _ P.hy P.hy (by
          change pY.map (𝟙 P.y) = eqToHom P.hy ≫ 𝟙 P.base ≫ eqToHom P.hy.symm
          simp)
      w := by simp [TwoFibreProductOver.reindexSymm, TwoFibreProductOver.reindex] }
    hom_inv_id := by
      apply TwoFibreProductOver.Hom.ext' <;>
        simp [TwoFibreProductOver.reindexSymm, TwoFibreProductOver.reindex]
    inv_hom_id := by
      apply TwoFibreProductOver.Hom.ext' <;>
        simp [TwoFibreProductOver.reindexSymm, TwoFibreProductOver.reindex] })
    (by
      intro P Q f
      apply TwoFibreProductOver.Hom.ext' <;>
        simp [TwoFibreProductOver.reindexSymm, TwoFibreProductOver.reindex])
  unit_over := by ext P; simp [TwoFibreProductOver.fst]
  counit_over := by ext P; simp [TwoFibreProductOver.fst]
private def composeEquivalenceOver
    {C : Type uC} [Category.{vC} C] {X : Type uX} [Category.{vX} X]
    {Y : Type uY} [Category.{vY} Y] {Z : Type uZ} [Category.{vZ} Z]
    {pX : X ⥤ C} {pY : Y ⥤ C} {pZ : Z ⥤ C}
    (e : StacksRepresentableCFG.EquivalenceOver pX pY)
    (d : StacksRepresentableCFG.EquivalenceOver pY pZ) :
    StacksRepresentableCFG.EquivalenceOver pX pZ where
  hom := ⟨e.hom.functor ⋙ d.hom.functor, by rw [Functor.assoc, d.hom.w, e.hom.w]⟩
  inv := ⟨d.inv.functor ⋙ e.inv.functor, by rw [Functor.assoc, e.inv.w, d.inv.w]⟩
  unitIso := NatIso.ofComponents
    (fun x => e.unitIso.app x ≪≫ e.inv.functor.mapIso (d.unitIso.app (e.hom.functor.obj x)))
    (by
      intro x y f
      have h₁ := e.unitIso.hom.naturality f
      have h₂ := d.unitIso.hom.naturality (e.hom.functor.map f)
      dsimp at h₁ h₂ ⊢
      rw [← Category.assoc, h₁, Category.assoc, ← e.inv.functor.map_comp, h₂,
        e.inv.functor.map_comp, Category.assoc])
  counitIso := NatIso.ofComponents
    (fun z => d.hom.functor.mapIso (e.counitIso.app (d.inv.functor.obj z)) ≪≫ d.counitIso.app z)
    (by
      intro x y f
      have h₁ := e.counitIso.hom.naturality (d.inv.functor.map f)
      have h₂ := d.counitIso.hom.naturality f
      dsimp at h₁ h₂ ⊢
      rw [← Category.assoc, ← d.hom.functor.map_comp, h₁,
        d.hom.functor.map_comp, Category.assoc, h₂, Category.assoc])
  unit_over := by
    ext x
    simp only [Functor.whiskerRight_app, NatIso.ofComponents_hom_app, Iso.trans_hom,
      Functor.mapIso_hom, Functor.map_comp, eqToHom_app, Iso.app_hom]
    have h₁ := congrArg (fun t => t.app x) e.unit_over
    have h₂ := congrArg (fun t => t.app (e.hom.functor.obj x)) d.unit_over
    simp only [Functor.whiskerRight_app, eqToHom_app] at h₁ h₂
    rw [h₁]
    change _ ≫ (e.inv.functor ⋙ pX).map _ = _
    rw [Functor.congr_hom e.inv.w, h₂]
    simp only [eqToHom_trans]
  counit_over := by
    ext z
    simp only [Functor.whiskerRight_app, NatIso.ofComponents_hom_app, Iso.trans_hom,
      Functor.mapIso_hom, Functor.map_comp, eqToHom_app, Iso.app_hom]
    have h₁ := congrArg (fun t => t.app (d.inv.functor.obj z)) e.counit_over
    have h₂ := congrArg (fun t => t.app z) d.counit_over
    simp only [Functor.whiskerRight_app, eqToHom_app] at h₁ h₂
    rw [h₂]
    change (d.hom.functor ⋙ pZ).map _ ≫ _ = _
    rw [Functor.congr_hom d.hom.w, h₁]
    simp only [eqToHom_trans]

private theorem whiskerRight_eqToHom_of_vertical
    {C : Type uC} [Category.{vC} C] {X : Type uX} [Category.{vX} X]
    {Y : Type uY} [Category.{vY} Y] (p : Y ⥤ C)
    {F G : X ⥤ Y} (h : F ⋙ p = G ⋙ p) (α : F ⟶ G)
    (hα : ∀ x, p.IsHomLift (𝟙 (p.obj (F.obj x))) (α.app x)) :
    Functor.whiskerRight α p = eqToHom h := by
  ext x
  have := hα x
  have hf := IsHomLift.fac' p (𝟙 (p.obj (F.obj x))) (α.app x)
  simpa using hf

private def reverseEquivalenceOver
    {C : Type uC} [Category.{vC} C] {X : Type uX} [Category.{vX} X]
    {Y : Type uY} [Category.{vY} Y] {pX : X ⥤ C} {pY : Y ⥤ C}
    (e : StacksRepresentableCFG.EquivalenceOver pX pY) :
    StacksRepresentableCFG.EquivalenceOver pY pX where
  hom := e.inv
  inv := e.hom
  unitIso := e.counitIso.symm
  counitIso := e.unitIso.symm
  unit_over := by
    apply whiskerRight_eqToHom_of_vertical
    intro y
    have : pY.IsHomLift (𝟙 (pY.obj y)) (e.counitIso.app y).hom :=
      e.isHomLift_counitIso_hom_app y
    exact IsHomLift.lift_id_inv pY (pY.obj y) (e.counitIso.app y)
  counit_over := by
    apply whiskerRight_eqToHom_of_vertical
    intro x
    have h := e.isHomLift_unitIso_inv_app x
    have hx : pX.obj ((e.hom.functor ⋙ e.inv.functor).obj x) = pX.obj x :=
      Functor.congr_obj (show (e.hom.functor ⋙ e.inv.functor) ⋙ pX = pX by
        rw [Functor.assoc, e.inv.w, e.hom.w]) x
    change pX.IsHomLift (𝟙 (pX.obj ((e.hom.functor ⋙ e.inv.functor).obj x)))
      (e.unitIso.inv.app x)
    rw [hx]
    exact h

private def twoFibreProductPrecompose
    {C : Type uC} [Category.{vC} C] {X : Type uX} [Category.{vX} X]
    {Y : Type uY} [Category.{vY} Y] {Z : Type uZ} [Category.{vZ} Z]
    {D : Type uD} [Category.{vD} D]
    (pX : X ⥤ C) (pY : Y ⥤ C) (pZ : Z ⥤ C)
    (y : X ⥤ Z) (f : Y ⥤ Z) (H : D ⥤ X) :
    TwoFibreProductOver (H ⋙ pX) pY pZ (H ⋙ y) f ⥤
      TwoFibreProductOver pX pY pZ y f where
  obj P := {
    base := P.base
    x := H.obj P.x
    y := P.y
    hx := P.hx
    hy := P.hy
    iso := P.iso
    vertical := P.vertical }
  map a := {
    hbase := a.hbase
    a := H.map a.a
    b := a.b
    ha := by
      have := a.ha
      exact Functor.isHomLift_map_of_comp_eq rfl _ a.a
    hb := a.hb
    w := a.w }
  map_id P := by apply TwoFibreProductOver.Hom.ext' <;> simp
  map_comp a b := by apply TwoFibreProductOver.Hom.ext' <;> simp

private def fiberFunctorAlong
    {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
    {X : Type uX} [Category.{vX} X] {Y : Type uY} [Category.{vY} Y]
    {p : X ⥤ C} {q : Y ⥤ D} (H : C ⥤ D) (F : X ⥤ Y)
    (h : F ⋙ q = p ⋙ H) (U : C) : p.Fiber U ⥤ q.Fiber (H.obj U) where
  obj x := ⟨F.obj x.1, (Functor.congr_obj h x.1).trans (congrArg H.obj x.2)⟩
  map {x y} a := ⟨F.map a.1, by
    have := a.2
    apply IsHomLift.of_fac' q _ _
      ((Functor.congr_obj h x.1).trans (congrArg H.obj x.2))
      ((Functor.congr_obj h y.1).trans (congrArg H.obj y.2))
    change (F ⋙ q).map a.1 = _
    rw [Functor.congr_hom h]
    simp only [Functor.comp_map, IsHomLift.fac' p (𝟙 U) a.1, eqToHom_map,
      Category.id_comp, eqToHom_trans]⟩
  map_id x := by apply Functor.Fiber.hom_ext; exact F.map_id x.1
  map_comp a b := by apply Functor.Fiber.hom_ext; exact F.map_comp a.1 b.1

private def twoFibreProductPrecomposeFiberFunctor
    {C : Type uC} [Category.{vC} C] {X : Type uX} [Category.{vX} X]
    {Y : Type uY} [Category.{vY} Y] {Z : Type uZ} [Category.{vZ} Z]
    {D : Type uD} [Category.{vD} D]
    (pX : X ⥤ C) (pY : Y ⥤ C) (pZ : Z ⥤ C)
    (y : X ⥤ Z) (f : Y ⥤ Z) (H : D ⥤ X) (U : D) :
    (TwoFibreProductOver.fst (H ⋙ pX) pY pZ (H ⋙ y) f).Fiber U ⥤
      (TwoFibreProductOver.fst pX pY pZ y f).Fiber (H.obj U) :=
  fiberFunctorAlong H (twoFibreProductPrecompose pX pY pZ y f H) rfl U

private def twoFibreProductPrecomposeFiberEquiv
    {C : Type uC} [Category.{vC} C] {X : Type uX} [Category.{vX} X]
    {Y : Type uY} [Category.{vY} Y] {Z : Type uZ} [Category.{vZ} Z]
    {D : Type uD} [Category.{vD} D]
    (pX : X ⥤ C) (pY : Y ⥤ C) (pZ : Z ⥤ C)
    (y : X ⥤ Z) (f : Y ⥤ Z) (H : D ⥤ X) (U : D) :
    (TwoFibreProductOver.fst (H ⋙ pX) pY pZ (H ⋙ y) f).Fiber U ≃
      (TwoFibreProductOver.fst pX pY pZ y f).Fiber (H.obj U) where
  toFun P := ⟨(twoFibreProductPrecompose pX pY pZ y f H).obj P.1,
    congrArg H.obj P.2⟩
  invFun P := by
    rcases P with ⟨⟨base, x, z, hx, hz, i, hi⟩, hP⟩
    change x = H.obj U at hP
    subst x
    cases hx
    exact ⟨⟨pX.obj (H.obj U), U, z, rfl, hz, i, hi⟩, rfl⟩
  left_inv P := by
    rcases P with ⟨⟨base, x, z, hx, hz, i, hi⟩, hP⟩
    change x = U at hP
    subst x
    change pX.obj (H.obj U) = base at hx
    cases hx
    rfl
  right_inv P := by
    rcases P with ⟨⟨base, x, z, hx, hz, i, hi⟩, hP⟩
    change x = H.obj U at hP
    subst x
    cases hx
    rfl

private theorem twoFibreProduct_fiber_hom_a
    {C : Type uC} [Category.{vC} C] {X : Type uX} [Category.{vX} X]
    {Y : Type uY} [Category.{vY} Y] {Z : Type uZ} [Category.{vZ} Z]
    {pX : X ⥤ C} {pY : Y ⥤ C} {pZ : Z ⥤ C} {y : X ⥤ Z} {f : Y ⥤ Z}
    {U : X} {a b : (TwoFibreProductOver.fst pX pY pZ y f).Fiber U}
    (k : a ⟶ b) : k.1.a = eqToHom a.2 ≫ eqToHom b.2.symm := by
  have := k.2
  simpa using IsHomLift.fac' (TwoFibreProductOver.fst pX pY pZ y f) (𝟙 U) k.1

private theorem twoFibreProductPrecomposeFiberFunctor_faithful
    {C : Type uC} [Category.{vC} C] {X : Type uX} [Category.{vX} X]
    {Y : Type uY} [Category.{vY} Y] {Z : Type uZ} [Category.{vZ} Z]
    {D : Type uD} [Category.{vD} D]
    (pX : X ⥤ C) (pY : Y ⥤ C) (pZ : Z ⥤ C)
    (y : X ⥤ Z) (f : Y ⥤ Z) (H : D ⥤ X) (U : D) :
    (twoFibreProductPrecomposeFiberFunctor pX pY pZ y f H U).Faithful where
  map_injective {a b} k l h := by
    apply Functor.Fiber.hom_ext
    apply TwoFibreProductOver.Hom.ext'
    · exact (twoFibreProduct_fiber_hom_a k).trans (twoFibreProduct_fiber_hom_a l).symm
    · exact congrArg (fun m => m.1.b) h

-- The fibre of the reindexed 2-fibre product is given by a chain of definitions, and the
-- components of one of its morphisms are typed through that chain; unification has to see
-- through it to recognise the base component as an identity.
attribute [local implicit_reducible] twoFibreProductPrecomposeFiberFunctor fiberFunctorAlong
  twoFibreProductPrecompose in
private theorem twoFibreProductPrecomposeFiberFunctor_full
    {C : Type uC} [Category.{vC} C] {X : Type uX} [Category.{vX} X]
    {Y : Type uY} [Category.{vY} Y] {Z : Type uZ} [Category.{vZ} Z]
    {D : Type uD} [Category.{vD} D]
    (pX : X ⥤ C) (pY : Y ⥤ C) (pZ : Z ⥤ C)
    (y : X ⥤ Z) (f : Y ⥤ Z) (H : D ⥤ X) (U : D) :
    (twoFibreProductPrecomposeFiberFunctor pX pY pZ y f H U).Full := by
  constructor
  intro a b k
  rcases a with ⟨⟨baseA, a, zA, ha, hzA, iA, hiA⟩, hA⟩
  rcases b with ⟨⟨baseB, b, zB, hb, hzB, iB, hiB⟩, hB⟩
  change a = U at hA
  change b = U at hB
  subst a
  subst b
  change pX.obj (H.obj U) = baseA at ha
  change pX.obj (H.obj U) = baseB at hb
  cases ha
  cases hb
  have hk : k.1.a = 𝟙 (H.obj U) := by
    simpa [twoFibreProductPrecomposeFiberFunctor, fiberFunctorAlong,
      twoFibreProductPrecompose, TwoFibreProductOver.fst] using twoFibreProduct_fiber_hom_a k
  let l : TwoFibreProductOver.Hom
      (⟨pX.obj (H.obj U), U, zA, rfl, hzA, iA, hiA⟩ :
        TwoFibreProductOver (H ⋙ pX) pY pZ (H ⋙ y) f)
      ⟨pX.obj (H.obj U), U, zB, rfl, hzB, iB, hiB⟩ := {
    hbase := k.1.hbase
    a := 𝟙 U
    b := k.1.b
    ha := by
      have h := k.1.ha
      rw [hk] at h
      apply IsHomLift.of_fac' (H ⋙ pX) _ _ rfl rfl
      have := h
      simpa using IsHomLift.fac' pX k.1.hbase (𝟙 (H.obj U))
    hb := k.1.hb
    w := by simpa [hk, twoFibreProductPrecomposeFiberFunctor, fiberFunctorAlong,
      twoFibreProductPrecompose] using k.1.w }
  have hl : (TwoFibreProductOver.fst (H ⋙ pX) pY pZ (H ⋙ y) f).IsHomLift
      (𝟙 U) l := IsHomLift.of_fac' _ _ _ rfl rfl (by
        simp [l, TwoFibreProductOver.fst])
  refine ⟨⟨l, hl⟩, ?_⟩
  apply Functor.Fiber.hom_ext
  apply TwoFibreProductOver.Hom.ext'
  · show H.map (𝟙 U) = k.1.a
    simpa using hk.symm
  · rfl

private theorem twoFibreProductPrecomposeFiberFunctor_isEquivalence
    {C : Type uC} [Category.{vC} C] {X : Type uX} [Category.{vX} X]
    {Y : Type uY} [Category.{vY} Y] {Z : Type uZ} [Category.{vZ} Z]
    {D : Type uD} [Category.{vD} D]
    (pX : X ⥤ C) (pY : Y ⥤ C) (pZ : Z ⥤ C)
    (y : X ⥤ Z) (f : Y ⥤ Z) (H : D ⥤ X) (U : D) :
    (twoFibreProductPrecomposeFiberFunctor pX pY pZ y f H U).IsEquivalence := by
  let K := twoFibreProductPrecomposeFiberFunctor pX pY pZ y f H U
  have : K.Faithful := twoFibreProductPrecomposeFiberFunctor_faithful pX pY pZ y f H U
  have : K.Full := twoFibreProductPrecomposeFiberFunctor_full pX pY pZ y f H U
  have : K.EssSurj := ⟨fun a => by
    obtain ⟨b, hb⟩ := (twoFibreProductPrecomposeFiberEquiv pX pY pZ y f H U).surjective a
    exact ⟨b, ⟨eqToIso hb⟩⟩⟩
  exact ⟨inferInstance, inferInstance, inferInstance⟩

private def isoClassEquivOfEquivalence
    {A : Type uX} [Category.{vX} A] {D : Type uY} [Category.{vY} D]
    (E : A ≌ D) :
    Quotient (isIsomorphicSetoid A) ≃
      Quotient (isIsomorphicSetoid D) where
  toFun := Quotient.map E.functor.obj (by
    intro x y h
    obtain ⟨e⟩ := (Functor.isIsomorphicSetoid_r_iff x y).1 h
    exact (Functor.isIsomorphicSetoid_r_iff _ _).2 ⟨E.functor.mapIso e⟩)
  invFun := Quotient.map E.inverse.obj (by
    intro x y h
    obtain ⟨e⟩ := (Functor.isIsomorphicSetoid_r_iff x y).1 h
    exact (Functor.isIsomorphicSetoid_r_iff _ _).2 ⟨E.inverse.mapIso e⟩)
  left_inv := by
    intro x
    induction x using Quotient.ind with
    | _ x => exact Quotient.sound ((Functor.isIsomorphicSetoid_r_iff _ _).2
        ⟨(E.unitIso.app x).symm⟩)
  right_inv := by
    intro x
    induction x using Quotient.ind with
    | _ x => exact Quotient.sound ((Functor.isIsomorphicSetoid_r_iff _ _).2
        ⟨E.counitIso.app x⟩)

private theorem isHomLift_map_along
    {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
    {X : Type uX} [Category.{vX} X] {Y : Type uY} [Category.{vY} Y]
    {p : X ⥤ C} {q : Y ⥤ D} (H : C ⥤ D) (F : X ⥤ Y)
    (h : F ⋙ q = p ⋙ H) {U V : C} (g : U ⟶ V)
    {x y : X} (a : x ⟶ y) (ha : p.IsHomLift g a) :
    q.IsHomLift (H.map g) (F.map a) := by
  have := ha
  apply IsHomLift.of_fac' q _ _
    ((Functor.congr_obj h x).trans (congrArg H.obj (IsHomLift.domain_eq p g a)))
    ((Functor.congr_obj h y).trans (congrArg H.obj (IsHomLift.codomain_eq p g a)))
  show (F ⋙ q).map a = _
  rw [Functor.congr_hom h]
  simp [Functor.comp_map, IsHomLift.fac' p g a, eqToHom_map, Category.assoc]

/-- A 1-morphism over the base carries a morphism lying over `f` to a morphism lying over `f`.
This is `CategoryTheory.Functor.isHomLift_map_of_comp_eq` with the lift supplied as an argument
rather than by instance search, at unrestricted universes. -/
private theorem isHomLift_map_of_comp_eq_arg {C : Type uC} [Category.{vC} C]
    {X : Type uX} [Category.{vX} X] {Y : Type uY} [Category.{vY} Y]
    {p : X ⥤ C} {q : Y ⥤ C} {G : X ⥤ Y} (hG : G ⋙ q = p)
    {R T : C} (f : R ⟶ T) {a b : X} (φ : a ⟶ b) (h : p.IsHomLift f φ) :
    q.IsHomLift f (G.map φ) :=
  have := h
  Functor.isHomLift_map_of_comp_eq hG f φ

private noncomputable def representedPresheafRestrictionIso
    {C : Type uC} [Category.{vC} C] {X : Type uX} [Category.{vX} X]
    {Y : Type uY} [Category.{vY} Y] {Z : Type uZ} [Category.{vZ} Z]
    {D : Type uD} [Category.{vX} D]
    (pX : X ⥤ C) (pY : Y ⥤ C) (pZ : Z ⥤ C)
    (y : X ⥤ Z) (f : Y ⥤ Z) (H : D ⥤ X)
    (F : Xᵒᵖ ⥤ Type vX) (G : Dᵒᵖ ⥤ Type vX)
    (eF : StacksRepresentableCFG.EquivalenceOver
      (TwoFibreProductOver.fst pX pY pZ y f) (PresheafOfCategories.discreteProjection F))
    (eG : StacksRepresentableCFG.EquivalenceOver
      (TwoFibreProductOver.fst (H ⋙ pX) pY pZ (H ⋙ y) f)
      (PresheafOfCategories.discreteProjection G)) :
    G ≅ H.op ⋙ F := by
  let p := TwoFibreProductOver.fst (H ⋙ pX) pY pZ (H ⋙ y) f
  let q := TwoFibreProductOver.fst pX pY pZ y f
  let K := twoFibreProductPrecompose pX pY pZ y f H
  let k := twoFibreProductPrecomposeFiberFunctor pX pY pZ y f H
  have hp : p.IsFiberedInGroupoids :=
    StacksRepresentableCFG.isFiberedInGroupoids_of_equivalenceOver eG
      (AlgebraicGeometry.elementsProjection_isFiberedInSetoids G).isFiberedInGroupoids
  have hq : q.IsFiberedInGroupoids :=
    StacksRepresentableCFG.isFiberedInGroupoids_of_equivalenceOver eF
      (AlgebraicGeometry.elementsProjection_isFiberedInSetoids F).isFiberedInGroupoids
  have : p.IsFibered := hp.isFibered
  have : q.IsFibered := hq.isFibered
  have (U : D) : (k U).IsEquivalence :=
    twoFibreProductPrecomposeFiberFunctor_isEquivalence pX pY pZ y f H U
  let e := fun U => (PresheafOfCategories.elementsIsoClassEquiv G eG U).symm.trans
    ((isoClassEquivOfEquivalence (k U).asEquivalence).trans
      (PresheafOfCategories.elementsIsoClassEquiv F eF (H.obj U)))
  have he (U : D) (x : p.Fiber U) :
      e U (PresheafOfCategories.elementsIsoClassEquiv G eG U (Functor.isoClassMk p x)) =
        PresheafOfCategories.elementsIsoClassEquiv F eF (H.obj U)
          (Functor.isoClassMk q ((k U).obj x)) := by
    simp [e, isoClassEquivOfEquivalence, Functor.isoClassMk]
    rfl
  refine NatIso.ofComponents (fun U => Equiv.toIso (e U.unop)) ?_
  intro U V g
  ext a
  obtain ⟨c, rfl⟩ := (PresheafOfCategories.elementsIsoClassEquiv G eG U.unop).surjective a
  induction c using Quotient.ind with
  | _ x =>
    change e V.unop (G.map g (PresheafOfCategories.elementsIsoClassEquiv G eG U.unop
      (Functor.isoClassMk p x))) =
      F.map (H.map g.unop).op (e U.unop (PresheafOfCategories.elementsIsoClassEquiv G eG U.unop
        (Functor.isoClassMk p x)))
    have hn := PresheafOfCategories.elementsIsoClassEquiv_naturality hp G eG g.unop
      (Functor.isoClassMk p x)
    simp only [Quiver.Hom.op_unop] at hn
    have hm := Functor.isoClassPresheaf_map_isoClassMk (p := p) g.unop x
    simp only [Quiver.Hom.op_unop] at hm
    rw [← hn, hm, he, he]
    apply PresheafOfCategories.elementsFiberEquiv_map_of_isHomLift F (H.map g.unop)
      ((fiberFunctorAlong (𝟭 _) eF.hom.functor eF.hom.w (H.obj U.unop)).obj
        ((k U.unop).obj x))
      ((fiberFunctorAlong (𝟭 _) eF.hom.functor eF.hom.w (H.obj V.unop)).obj
        ((k V.unop).obj (p.pullbackFiber x g.unop)))
      (eF.hom.functor.map (K.map (Functor.IsPreFibered.pullbackMap x.2 g.unop)))
    have hk : q.IsHomLift (H.map g.unop)
        (K.map (Functor.IsPreFibered.pullbackMap x.2 g.unop)) :=
      isHomLift_map_along (p := p) (q := q) H K rfl g.unop _ inferInstance
    exact isHomLift_map_of_comp_eq_arg eF.hom.w (H.map g.unop) _ hk

private def identityEquivalenceOver {C : Type uC} [Category.{vC} C]
    {A : Type uX} [Category.{vX} A] (p : A ⥤ C) :
    StacksRepresentableCFG.EquivalenceOver p p where
  hom := ⟨𝟭 A, rfl⟩
  inv := ⟨𝟭 A, rfl⟩
  unitIso := Iso.refl _
  counitIso := Iso.refl _
  unit_over := by simp [Functor.assoc]
  counit_over := by simp [Functor.assoc]

private noncomputable def presheafIsoOfEquivalenceOverElements
    {C : Type uC} [Category.{vC} C]
    (F G : Cᵒᵖ ⥤ Type vC)
    (E : StacksRepresentableCFG.EquivalenceOver
      (presheafOfCategories (F ⋙ typeToCat)).p
      (presheafOfCategories (G ⋙ typeToCat)).p) : F ≅ G := by
  let pF := (presheafOfCategories (F ⋙ typeToCat)).p
  let pG := (presheafOfCategories (G ⋙ typeToCat)).p
  let eF := identityEquivalenceOver pF
  let : pF.IsFiberedInGroupoids :=
    (AlgebraicGeometry.elementsProjection_isFiberedInSetoids F).isFiberedInGroupoids
  let : pF.IsFibered := inferInstance
  let : pG.IsFiberedInGroupoids :=
    (AlgebraicGeometry.elementsProjection_isFiberedInSetoids G).isFiberedInGroupoids
  let : pG.IsFibered := inferInstance
  let e₁ := fun U => PresheafOfCategories.elementsIsoClassEquiv F eF U
  let e₂ := fun U => PresheafOfCategories.elementsIsoClassEquiv G E U
  let e := fun U => (e₁ U).symm.trans (e₂ U)
  have hnat {V U : C} (f : V ⟶ U) (a : F.obj (Opposite.op U)) :
      e V (F.map f.op a) = G.map f.op (e U a) := by
    let c := (e₁ U).symm a
    have h₁ := PresheafOfCategories.elementsIsoClassEquiv_naturality
      (p := pF) (AlgebraicGeometry.elementsProjection_isFiberedInSetoids F).isFiberedInGroupoids
      F eF f c
    have h₂ := PresheafOfCategories.elementsIsoClassEquiv_naturality
      (p := pF) (AlgebraicGeometry.elementsProjection_isFiberedInSetoids F).isFiberedInGroupoids
      G E f c
    have hc : (e₁ V).symm (F.map f.op a) =
        pF.isoClassPresheaf.map f.op c := by
      apply (e₁ V).injective
      calc
        (e₁ V) ((e₁ V).symm (F.map f.op a)) = F.map f.op a :=
          Equiv.apply_symm_apply (e₁ V) _
        _ = F.map f.op (e₁ U c) :=
          congrArg (F.map f.op) (Equiv.apply_symm_apply (e₁ U) a).symm
        _ = (e₁ V) (pF.isoClassPresheaf.map f.op c) := h₁.symm
    dsimp [e, e₁, e₂]
    rw [hc]
    exact h₂
  refine NatIso.ofComponents (fun U => Equiv.toIso (e U.unop)) ?_
  intro U V f
  ext a
  exact hnat f.unop a

private def relocalizedProjection
    {C : Type uC} [Category.{vC} C] {S U : C} (g : U ⟶ S)
    (F : (Over U)ᵒᵖ ⥤ Type vC) :
    (OverShriek.relocalizePresheafFunctor g).obj F ⟶ yoneda.obj (Over.mk g) where
  app W := ↾fun s => Over.homMk s.1.1 s.2
  naturality W W' k := by ext s; rfl

private def relocalizedRestrictionMap
    {C : Type uC} [Category.{vC} C] {S : C} {V U : Over S} (h : V ⟶ U)
    (F : (Over U.left)ᵒᵖ ⥤ Type vC) :
    (OverShriek.relocalizePresheafFunctor V.hom).obj ((Over.map h.left).op ⋙ F) ⟶
      (OverShriek.relocalizePresheafFunctor U.hom).obj F where
  app W := ↾fun s => ⟨⟨s.1.1 ≫ h.left, s.1.2⟩, by
    change (s.1.1 ≫ h.left) ≫ U.hom = W.unop.hom
    rw [Category.assoc, Over.w h]
    exact s.2⟩
  naturality W W' k := by
    ext s
    exact Subtype.ext (OverShriek.sigmaMk_eq F s.1.2 _ _ rfl)

private theorem relocalizedRestriction_isPullback
    {C : Type uC} [Category.{vC} C] {S : C} {V U : Over S} (h : V ⟶ U)
    (F : (Over U.left)ᵒᵖ ⥤ Type vC) :
    IsPullback (relocalizedRestrictionMap h F)
      (relocalizedProjection V.hom ((Over.map h.left).op ⋙ F))
      (relocalizedProjection U.hom F) (yoneda.map h) := by
  apply IsPullback.of_forall_isPullback_app
  intro W
  apply (Types.isPullback_iff _ _ _ _).2
  refine ⟨?_, ?_, ?_⟩
  · ext s; rfl
  · rintro ⟨⟨ψ, s⟩, hs⟩ ⟨⟨ψ', s'⟩, hs'⟩ ⟨ht, hl⟩
    have hψ : ψ = ψ' := congrArg Over.Hom.left hl
    subst ψ'
    have hv : s = s' := eq_of_heq (Sigma.mk.inj_iff.mp (congrArg Subtype.val ht)).2
    subst s'
    rfl
  · rintro ⟨⟨ψ, s⟩, hs⟩ t ht
    have hψ : ψ = t.left ≫ h.left := congrArg Over.Hom.left ht
    subst ψ
    refine ⟨⟨⟨t.left, s⟩, t.w⟩, ?_, ?_⟩
    · rfl
    · apply Over.OverMorphism.ext; rfl
private theorem relocalizedProjection_naturality
    {C : Type uC} [Category.{vC} C] {S U : C} (g : U ⟶ S)
    {F G : (Over U)ᵒᵖ ⥤ Type vC} (a : F ⟶ G) :
    (OverShriek.relocalizePresheafFunctor g).map a ≫ relocalizedProjection g G =
      relocalizedProjection g F := rfl

private theorem relocalizedRestriction_isPullback_of_iso
    {C : Type uC} [Category.{vC} C] {S : C} {V U : Over S} (h : V ⟶ U)
    (F : (Over U.left)ᵒᵖ ⥤ Type vC) (G : (Over V.left)ᵒᵖ ⥤ Type vC)
    (a : G ≅ (Over.map h.left).op ⋙ F) :
    IsPullback
      ((OverShriek.relocalizePresheafFunctor V.hom).map a.hom ≫
        relocalizedRestrictionMap h F)
      (relocalizedProjection V.hom G)
      (relocalizedProjection U.hom F) (yoneda.map h) :=
  (relocalizedRestriction_isPullback h F).of_iso'
    ((OverShriek.relocalizePresheafFunctor V.hom).mapIso a)
    (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (by simp) (by simpa using relocalizedProjection_naturality V.hom a.hom)
    (by simp) (by simp)

private theorem algebraicSpaceMap_eq_relocalizedProjection
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (U : BigFppfOver B S hS)
    (F : AlgebraicSpaces B U.left.1 U.left.2) :
    ((spacesOverSmallerBaseFunctorForgetIso
      B U.left.1 S U.left.2 hS U.hom).app F).hom ≫
      relocalizedProjection U.hom F.obj =
    (algebraicSpaceMap B S hS U
      ((spacesOverSmallerBaseFunctor
        B U.left.1 S U.left.2 hS U.hom).obj F)).hom := by
  ext W s
  let e := (spacesOverSmallerBaseFunctorForgetIso
    B U.left.1 S U.left.2 hS U.hom).app F
  have h := (spacesOverSmallerBaseFunctor_hom_app_forgetIso_inv_app
    B U.left.1 S U.left.2 hS U.hom) F W (e.hom.app W s)
  have he : e.inv.app W (e.hom.app W s) = s := by
    simp
  change ((spacesOverSmallerBaseFunctor
    B U.left.1 S U.left.2 hS U.hom).obj F).1.hom.app W
      (e.inv.app W (e.hom.app W s)) = _ at h
  rw [he] at h
  exact h.symm

private theorem algebraicSpaceMap_isPullback_of_restrictionIso
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {V U : BigFppfOver B S hS} (h : V ⟶ U)
    (F : AlgebraicSpaces B U.left.1 U.left.2)
    (G : AlgebraicSpaces B V.left.1 V.left.2)
    (a : G.obj ≅ (Over.map h.left).op ⋙ F.obj) :
    ∃ t, IsPullback t
      (algebraicSpaceMap B S hS V
        ((spacesOverSmallerBaseFunctor
          B V.left.1 S V.left.2 hS V.hom).obj G))
      (algebraicSpaceMap B S hS U
        ((spacesOverSmallerBaseFunctor
          B U.left.1 S U.left.2 hS U.hom).obj F))
      (ObjectProperty.homMk (yoneda.map h)) := by
  let eF := (spacesOverSmallerBaseFunctorForgetIso
    B U.left.1 S U.left.2 hS U.hom).app F
  let eG := (spacesOverSmallerBaseFunctorForgetIso
    B V.left.1 S V.left.2 hS V.hom).app G
  let t := eG.hom ≫ (OverShriek.relocalizePresheafFunctor V.hom).map a.hom ≫
    relocalizedRestrictionMap h F.obj ≫ eF.inv
  have ht : IsPullback t
      (algebraicSpaceMap B S hS V
        ((spacesOverSmallerBaseFunctor
          B V.left.1 S V.left.2 hS V.hom).obj G)).hom
      (algebraicSpaceMap B S hS U
        ((spacesOverSmallerBaseFunctor
          B U.left.1 S U.left.2 hS U.hom).obj F)).hom
      (yoneda.map h) := by
    apply (relocalizedRestriction_isPullback_of_iso h F.obj G.obj a).of_iso'
      eG eF (Iso.refl _) (Iso.refl _)
    · simp [t, Category.assoc]
    · simpa [eG] using algebraicSpaceMap_eq_relocalizedProjection B S hS V G
    · simpa [eF] using algebraicSpaceMap_eq_relocalizedProjection B S hS U F
    · simp
  refine ⟨ObjectProperty.homMk t, ?_⟩
  apply IsPullback.of_map (ObjectProperty.ι
    (fun F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u =>
      IsAlgebraicSpace B S hS F))
  · exact ObjectProperty.hom_ext _ ht.w
  · exact ht

private theorem algebraicSpaceMap_property_iff_of_iso
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (P : MorphismProperty (AlgebraicSpaces B S hS)) [P.RespectsIso]
    (U : BigFppfOver B S hS)
    (F G : AlgebraicSpaces B U.left.1 U.left.2) (e : F ≅ G) :
    P (algebraicSpaceMap B S hS U
      ((spacesOverSmallerBaseFunctor
        B U.left.1 S U.left.2 hS U.hom).obj F)) ↔
    P (algebraicSpaceMap B S hS U
      ((spacesOverSmallerBaseFunctor
        B U.left.1 S U.left.2 hS U.hom).obj G)) := by
  let E := (spacesOverSmallerBaseFunctor
    B U.left.1 S U.left.2 hS U.hom)
  let i := E.mapIso e
  let j : (⟨(E.obj F).1.left, (E.obj F).property⟩ :
      AlgebraicSpaces B S hS) ≅
    (⟨(E.obj G).1.left, (E.obj G).property⟩ :
      AlgebraicSpaces B S hS) :=
    ObjectProperty.isoMk _ ((Over.forget _).mapIso ((ObjectProperty.ι _).mapIso i))
  have h : j.hom ≫ algebraicSpaceMap B S hS U (E.obj G) =
      algebraicSpaceMap B S hS U (E.obj F) :=
    ObjectProperty.hom_ext _ (Over.w i.hom.hom)
  have : IsIso j.hom := j.isIso_hom
  rw [← h, P.cancel_left_of_respectsIso]

private noncomputable def representedPresheafIsoOfSectionIso
    {C : Type uC} [Category.{vC} C] {X : Type uX} [Category.{vX} X]
    {Y : Type uY} [Category.{vY} Y] {Z : Type uZ} [Category.{vZ} Z]
    {pX : X ⥤ C} {pY : Y ⥤ C} {pZ : Z ⥤ C}
    {y y' : X ⥤ Z} {f : Y ⥤ Z}
    (α : y ≅ y') (hα : ∀ x, pZ.IsHomLift (𝟙 (pX.obj x)) (α.hom.app x))
    (F G : Xᵒᵖ ⥤ Type vX)
    (eF : StacksRepresentableCFG.EquivalenceOver
      (TwoFibreProductOver.fst pX pY pZ y f) (PresheafOfCategories.discreteProjection F))
    (eG : StacksRepresentableCFG.EquivalenceOver
      (TwoFibreProductOver.fst pX pY pZ y' f)
      (PresheafOfCategories.discreteProjection G)) : F ≅ G :=
  presheafIsoOfEquivalenceOverElements F G
    (composeEquivalenceOver (reverseEquivalenceOver eF)
      (composeEquivalenceOver (reindexEquivalenceOver α hα) eG))

private theorem algebraicSpaceMap_property_iff_of_sectionIso
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (P : MorphismProperty (AlgebraicSpaces B S hS)) [P.RespectsIso]
    {𝒳 𝒴 : CatFiberedInGroupoids.{u, u, u + 1, u + 1}
      (BigFppfOver B S hS)} (f : 𝒳 ⟶ 𝒴)
    (U : BigFppfOver B S hS)
    (y y' : BigFppfOver B U.left.1 U.left.2 ⥤ 𝒴.val.obj)
    (α : y ≅ y')
    (hα : ∀ W, 𝒴.val.p.IsHomLift (𝟙 ((Over.map U.hom).obj W)) (α.hom.app W))
    (F G : AlgebraicSpaces B U.left.1 U.left.2)
    (eF : StacksRepresentableCFG.EquivalenceOver
      (TwoFibreProductOver.fst (Over.map U.hom) 𝒳.val.p 𝒴.val.p y
        (CatFiberedInGroupoids.homFunctor f)) (PresheafOfCategories.discreteProjection F.obj))
    (eG : StacksRepresentableCFG.EquivalenceOver
      (TwoFibreProductOver.fst (Over.map U.hom) 𝒳.val.p 𝒴.val.p y'
        (CatFiberedInGroupoids.homFunctor f)) (PresheafOfCategories.discreteProjection G.obj)) :
    P (algebraicSpaceMap B S hS U
      ((spacesOverSmallerBaseFunctor
        B U.left.1 S U.left.2 hS U.hom).obj F)) ↔
    P (algebraicSpaceMap B S hS U
      ((spacesOverSmallerBaseFunctor
        B U.left.1 S U.left.2 hS U.hom).obj G)) := by
  exact algebraicSpaceMap_property_iff_of_iso B S hS P U F G
    (ObjectProperty.isoMk _ (representedPresheafIsoOfSectionIso α hα F.obj G.obj eF eG))

private theorem representedAlgebraicSpace_isPullback_of_sectionIso
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {𝒳 𝒴 : CatFiberedInGroupoids.{u, u, u + 1, u + 1}
      (BigFppfOver B S hS)} (f : 𝒳 ⟶ 𝒴)
    {V U : BigFppfOver B S hS} (h : V ⟶ U)
    (yU : BigFppfOver B U.left.1 U.left.2 ⥤ 𝒴.val.obj)
    (yV : BigFppfOver B V.left.1 V.left.2 ⥤ 𝒴.val.obj)
    (a : yV ≅ Over.map h.left ⋙ yU)
    (ha : ∀ W, 𝒴.val.p.IsHomLift (𝟙 ((Over.map V.hom).obj W)) (a.hom.app W))
    (F : AlgebraicSpaces B U.left.1 U.left.2)
    (G : AlgebraicSpaces B V.left.1 V.left.2)
    (eF : StacksRepresentableCFG.EquivalenceOver
      (TwoFibreProductOver.fst (Over.map U.hom) 𝒳.val.p 𝒴.val.p yU
        (CatFiberedInGroupoids.homFunctor f)) (PresheafOfCategories.discreteProjection F.obj))
    (eG : StacksRepresentableCFG.EquivalenceOver
      (TwoFibreProductOver.fst (Over.map V.hom) 𝒳.val.p 𝒴.val.p yV
        (CatFiberedInGroupoids.homFunctor f)) (PresheafOfCategories.discreteProjection G.obj)) :
    ∃ t, IsPullback t
      (algebraicSpaceMap B S hS V
        ((spacesOverSmallerBaseFunctor
          B V.left.1 S V.left.2 hS V.hom).obj G))
      (algebraicSpaceMap B S hS U
        ((spacesOverSmallerBaseFunctor
          B U.left.1 S U.left.2 hS U.hom).obj F))
      (ObjectProperty.homMk (yoneda.map h)) := by
  let e := composeEquivalenceOver (reverseEquivalenceOver (reindexEquivalenceOver a ha)) eG
  have hm : Over.map h.left ⋙ Over.map U.hom = Over.map V.hom := by
    rw [← Over.mapComp_eq, Over.w h]
  let e' : StacksRepresentableCFG.EquivalenceOver
      (TwoFibreProductOver.fst (Over.map h.left ⋙ Over.map U.hom)
        𝒳.val.p 𝒴.val.p (Over.map h.left ⋙ yU) (CatFiberedInGroupoids.homFunctor f))
      (PresheafOfCategories.discreteProjection G.obj) := by
    rw [hm]
    exact e
  let i := representedPresheafRestrictionIso (Over.map U.hom) 𝒳.val.p 𝒴.val.p
    yU (CatFiberedInGroupoids.homFunctor f) (Over.map h.left) F.obj G.obj eF e'
  exact algebraicSpaceMap_isPullback_of_restrictionIso B S hS h F G i

private theorem algebraicSpaceMap_property_of_sectionIso
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (P : MorphismProperty (AlgebraicSpaces B S hS))
    [P.IsStableUnderBaseChange]
    {𝒳 𝒴 : CatFiberedInGroupoids.{u, u, u + 1, u + 1}
      (BigFppfOver B S hS)} (f : 𝒳 ⟶ 𝒴)
    {V U : BigFppfOver B S hS} (h : V ⟶ U)
    (yU : BigFppfOver B U.left.1 U.left.2 ⥤ 𝒴.val.obj)
    (yV : BigFppfOver B V.left.1 V.left.2 ⥤ 𝒴.val.obj)
    (a : yV ≅ Over.map h.left ⋙ yU)
    (ha : ∀ W, 𝒴.val.p.IsHomLift (𝟙 ((Over.map V.hom).obj W)) (a.hom.app W))
    (F : AlgebraicSpaces B U.left.1 U.left.2)
    (G : AlgebraicSpaces B V.left.1 V.left.2)
    (eF : StacksRepresentableCFG.EquivalenceOver
      (TwoFibreProductOver.fst (Over.map U.hom) 𝒳.val.p 𝒴.val.p yU
        (CatFiberedInGroupoids.homFunctor f)) (PresheafOfCategories.discreteProjection F.obj))
    (eG : StacksRepresentableCFG.EquivalenceOver
      (TwoFibreProductOver.fst (Over.map V.hom) 𝒳.val.p 𝒴.val.p yV
        (CatFiberedInGroupoids.homFunctor f)) (PresheafOfCategories.discreteProjection G.obj))
    (hF : P (algebraicSpaceMap B S hS U
      ((spacesOverSmallerBaseFunctor
        B U.left.1 S U.left.2 hS U.hom).obj F))) :
    P (algebraicSpaceMap B S hS V
      ((spacesOverSmallerBaseFunctor
        B V.left.1 S V.left.2 hS V.hom).obj G)) := by
  obtain ⟨t, ht⟩ := representedAlgebraicSpace_isPullback_of_sectionIso B S hS f h
    yU yV a ha F G eF eG
  exact P.of_isPullback ht hF

private theorem algebraicSpaceMap_property_of_cover
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (P : MorphismProperty (AlgebraicSpaces B S hS))
    [P.IsLocalAtTarget (Space.Topology.fppf.precoverage.{u, vI} B S hS)]
    {𝒳 𝒴 : CatFiberedInGroupoids.{u, u, u + 1, u + 1}
      (BigFppfOver B S hS)} (f : 𝒳 ⟶ 𝒴)
    (U : BigFppfOver B S hS)
    (y : BigFppfOver B U.left.1 U.left.2 ⥤ 𝒴.val.obj)
    (hy : y ⋙ 𝒴.val.p = Over.map U.hom)
    (F : AlgebraicSpaces B U.left.1 U.left.2)
    (eF : StacksRepresentableCFG.EquivalenceOver
      (TwoFibreProductOver.fst (Over.map U.hom) 𝒳.val.p 𝒴.val.p y
        (CatFiberedInGroupoids.homFunctor f)) (PresheafOfCategories.discreteProjection F.obj))
    (I : Type vI) (V : I → BigFppfOver B S hS) (g : ∀ i, V i ⟶ U)
    (hcover : Space.Topology.fppf.IsCovering B S hS
      (fun i => yoneda.obj (V i)) (fun i => yoneda.map (g i)))
    (htest : ∀ i, ∃ G : AlgebraicSpaces B (V i).left.1 (V i).left.2,
      Nonempty (StacksRepresentableCFG.EquivalenceOver
        (TwoFibreProductOver.fst (Over.map (V i).hom) 𝒳.val.p 𝒴.val.p
          (Over.map (g i).left ⋙ y) (CatFiberedInGroupoids.homFunctor f))
        (PresheafOfCategories.discreteProjection G.obj)) ∧
      P (algebraicSpaceMap B S hS (V i)
        ((spacesOverSmallerBaseFunctor
          B (V i).left.1 S (V i).left.2 hS (V i).hom).obj G))) :
    P (algebraicSpaceMap B S hS U
      ((spacesOverSmallerBaseFunctor
        B U.left.1 S U.left.2 hS U.hom).obj F)) := by
  let Vi : I → AlgebraicSpaces B S hS := fun i =>
    ⟨yoneda.obj (V i), isAlgebraicSpace_yoneda B S hS (V i)⟩
  let gi : ∀ i, Vi i ⟶
      (⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩ :
        AlgebraicSpaces B S hS) :=
    fun i => ObjectProperty.homMk (yoneda.map (g i))
  have hR : Presieve.ofArrows Vi gi ∈
      (Space.Topology.fppf.precoverage.{u, vI} B S hS).coverings
        (⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩ :
          AlgebraicSpaces B S hS) :=
    ⟨I, Vi, gi, rfl, hcover⟩
  apply MorphismProperty.IsLocalAtTarget.of_forall_pullbackSnd hR
  intro W h hh hmem
  obtain ⟨i⟩ := hmem
  obtain ⟨G, ⟨eG⟩, hG⟩ := htest i
  have ha : ∀ T, 𝒴.val.p.IsHomLift (𝟙 ((Over.map (V i).hom).obj T))
      ((Iso.refl (Over.map (g i).left ⋙ y)).hom.app T) := by
    intro T
    have ht : 𝒴.val.p.obj ((Over.map (g i).left ⋙ y).obj T) =
        (Over.map (V i).hom).obj T := by
      have hm : (Over.map (g i).left ⋙ y) ⋙ 𝒴.val.p = Over.map (V i).hom := by
        rw [Functor.assoc, hy, ← Over.mapComp_eq, Over.w (g i)]
      exact Functor.congr_obj hm T
    exact IsHomLift.of_fac' _ _ _ ht ht (by simp)
  obtain ⟨t, ht⟩ := representedAlgebraicSpace_isPullback_of_sectionIso B S hS f (g i)
    y (Over.map (g i).left ⋙ y) (Iso.refl _) ha F G eF eG
  rw [← ht.isoPullback_inv_snd, P.cancel_left_of_respectsIso]
  exact hG

private noncomputable def sliceFunctorIsoOfFibreIso
    {C : Type u₁} [Category.{v₁} C] {X : Type u₂} [Category.{v₂} X]
    (p : X ⥤ C) (c : Functor.ChoiceOfPullbacks p) {U : C}
    {x x' : p.Fiber U} (e : x ≅ x') :
    c.sliceFunctor x ≅ c.sliceFunctor x' := by
  refine NatIso.ofComponents
    (fun f => (Functor.Fiber.fiberInclusion).mapIso
      ((c.pullbackFunctor f.hom).mapIso e)) ?_
  intro f' f h
  let ψ₁ : (c.sliceFunctor x).obj f' ⟶ (c.sliceFunctor x').obj f :=
    (c.sliceFunctor x).map h ≫
      (Functor.Fiber.fiberInclusion).map (c.homMap f.hom e.hom)
  let ψ₂ : (c.sliceFunctor x).obj f' ⟶ (c.sliceFunctor x').obj f :=
    (Functor.Fiber.fiberInclusion).map (c.homMap f'.hom e.hom) ≫
      (c.sliceFunctor x').map h
  have hmapx : p.IsHomLift h.left ((c.sliceFunctor x).map h) :=
    c.sliceFunctor_map_isHomLift x h
  have hmapx' : p.IsHomLift h.left ((c.sliceFunctor x').map h) :=
    c.sliceFunctor_map_isHomLift x' h
  have hαf : p.IsHomLift (𝟙 f.left)
      (Functor.Fiber.fiberInclusion.map (c.homMap f.hom e.hom)) :=
    (c.homMap f.hom e.hom).2
  have hαf' : p.IsHomLift (𝟙 f'.left)
      (Functor.Fiber.fiberInclusion.map (c.homMap f'.hom e.hom)) :=
    (c.homMap f'.hom e.hom).2
  have hψ₁ : p.IsHomLift h.left ψ₁ :=
    IsHomLift.comp_lift_id_right p h.left _ _
  have hψ₂ : p.IsHomLift h.left ψ₂ :=
    IsHomLift.comp_lift_id_left p h.left _ _
  have hfac₁ : ψ₁ ≫ c.map f.hom x' =
      c.map f'.hom x ≫ Functor.Fiber.fiberInclusion.map e.hom := by
    dsimp [ψ₁]
    rw [Category.assoc, c.homMap_fac, ← Category.assoc, c.sliceFunctor_map_fac]
  have hfac₂ : ψ₂ ≫ c.map f.hom x' =
      c.map f'.hom x ≫ Functor.Fiber.fiberInclusion.map e.hom := by
    dsimp [ψ₂]
    calc
      _ = Functor.Fiber.fiberInclusion.map (c.homMap f'.hom e.hom) ≫
          ((c.sliceFunctor x').map h ≫ c.map f.hom x') := by simp [Category.assoc]
      _ = Functor.Fiber.fiberInclusion.map (c.homMap f'.hom e.hom) ≫
          c.map f'.hom x' := by rw [c.sliceFunctor_map_fac]
      _ = c.map f'.hom x ≫ Functor.Fiber.fiberInclusion.map e.hom :=
        c.homMap_fac f'.hom e.hom
  have h₁ := Functor.IsStronglyCartesian.map_uniq p f.hom (c.map f.hom x')
    (show f'.hom = h.left ≫ f.hom from (Over.w h).symm)
    (c.map f'.hom x ≫ Functor.Fiber.fiberInclusion.map e.hom) ψ₁ hfac₁
  have h₂ := Functor.IsStronglyCartesian.map_uniq p f.hom (c.map f.hom x')
    (show f'.hom = h.left ≫ f.hom from (Over.w h).symm)
    (c.map f'.hom x ≫ Functor.Fiber.fiberInclusion.map e.hom) ψ₂ hfac₂
  exact h₁.trans h₂.symm

private noncomputable def sectionIsoOfFibreIso
    {C : Type u₁} [Category.{v₁} C] {X : Type u₂} [Category.{v₂} X]
    (p : X ⥤ C) (hp : p.IsFiberedInGroupoids)
    (c : Functor.ChoiceOfPullbacks p) {U : C}
    (G H : Over U ⥤ X) (hG : G ⋙ p = Over.forget U)
    (hH : H ⋙ p = Over.forget U)
    (e : Functor.ChoiceOfPullbacks.sliceObj G hG ≅
      Functor.ChoiceOfPullbacks.sliceObj H hH) : G ≅ H :=
  (Functor.ChoiceOfPullbacks.sliceFunctorIso c G hG hp).trans <|
    (sliceFunctorIsoOfFibreIso p c e).trans
      (Functor.ChoiceOfPullbacks.sliceFunctorIso c H hH hp).symm

private theorem sectionIsoOfFibreIso_isHomLift
    {C : Type u₁} [Category.{v₁} C] {X : Type u₂} [Category.{v₂} X]
    (p : X ⥤ C) (hp : p.IsFiberedInGroupoids)
    (c : Functor.ChoiceOfPullbacks p) {U : C}
    (G H : Over U ⥤ X) (hG : G ⋙ p = Over.forget U)
    (hH : H ⋙ p = Over.forget U)
    (e : Functor.ChoiceOfPullbacks.sliceObj G hG ≅
      Functor.ChoiceOfPullbacks.sliceObj H hH) (W : Over U) :
    p.IsHomLift (𝟙 W.left) ((sectionIsoOfFibreIso p hp c G H hG hH e).hom.app W) := by
  have h₁ := Functor.ChoiceOfPullbacks.sliceFunctorIso_hom_app_isHomLift c G hG hp W
  have h₂ : p.IsHomLift (𝟙 W.left)
      ((sliceFunctorIsoOfFibreIso p c e).hom.app W) :=
    (c.homMap W.hom e.hom).2
  have h₃ := @IsHomLift.lift_id_inv _ _ _ _ p _ _ _
    ((Functor.ChoiceOfPullbacks.sliceFunctorIso c H hH hp).app W)
    (Functor.ChoiceOfPullbacks.sliceFunctorIso_hom_app_isHomLift c H hH hp W)
  exact Functor.isHomLift_comp_of_isHomLift_id p _ _ _
    h₁ (Functor.isHomLift_comp_of_isHomLift_id p _ _ _ h₂ h₃)

private theorem exists_sectionIso_of_fiberIso
    {C : Type u₁} [Category.{v₁} C] {X : Type u₂} [Category.{v₂} X]
    (p : X ⥤ C) (hp : p.IsFiberedInGroupoids)
    (c : Functor.ChoiceOfPullbacks p) {U V : C} (g : U ⟶ V)
    (G : Over U ⥤ X) (hG : G ⋙ p = Over.forget U) (x : p.Fiber V)
    (e : Functor.ChoiceOfPullbacks.sliceObj G hG ≅ c.obj g x) :
    ∃ a : G ≅ Over.map g ⋙ c.sliceFunctor x,
      ∀ W, p.IsHomLift (𝟙 W.left) (a.hom.app W) := by
  let H := Over.map g ⋙ c.sliceFunctor x
  have hH : H ⋙ p = Over.forget U := by
    rw [show H = Over.map g ⋙ c.sliceFunctor x from rfl,
      Functor.assoc, c.sliceFunctor_comp]
    rfl
  have hx : Functor.ChoiceOfPullbacks.sliceObj H hH = c.obj g x := by
    apply Subtype.ext
    simp [Functor.ChoiceOfPullbacks.sliceObj, H,
      Functor.ChoiceOfPullbacks.sliceFunctor_obj]
  let e' := e ≪≫ eqToIso hx.symm
  exact ⟨sectionIsoOfFibreIso p hp c G H hG hH e',
    sectionIsoOfFibreIso_isHomLift p hp c G H hG hH e'⟩

private noncomputable def sectionIsoOfValueIso
    {C : Type u₁} [Category.{v₁} C] {X : Type u₂} [Category.{v₂} X]
    (p : X ⥤ C) (hp : p.IsFiberedInGroupoids)
    (c : Functor.ChoiceOfPullbacks p) {U : C}
    (G H : Over U ⥤ X) (hG : G ⋙ p = Over.forget U)
    (hH : H ⋙ p = Over.forget U)
    (e : G.obj (Over.mk (𝟙 U)) ≅ H.obj (Over.mk (𝟙 U)))
    (he : p.IsHomLift (𝟙 U) e.hom) : G ≅ H := by
  let x : p.Fiber U := ⟨G.obj (Over.mk (𝟙 U)), by
    have h := congrArg (fun F : Over U ⥤ C => F.obj (Over.mk (𝟙 U))) hG
    simpa using h⟩
  let y : p.Fiber U := ⟨H.obj (Over.mk (𝟙 U)), by
    have h := congrArg (fun F : Over U ⥤ C => F.obj (Over.mk (𝟙 U))) hH
    simpa using h⟩
  have he' : p.IsHomLift (𝟙 U) e.hom := he
  have hei0 : p.IsHomLift (𝟙 U) (CategoryTheory.inv e.hom) :=
    IsHomLift.lift_id_inv_isIso p U e.hom
  have hei : p.IsHomLift (𝟙 U) e.inv := by simpa using hei0
  let : p.IsHomLift (𝟙 U) e.hom := he'
  let : p.IsHomLift (𝟙 U) e.inv := hei
  let e' : x ≅ y := {
    hom := Functor.Fiber.homMk p U e.hom
    inv := Functor.Fiber.homMk p U e.inv
    hom_inv_id := Functor.Fiber.hom_ext e.hom_inv_id
    inv_hom_id := Functor.Fiber.hom_ext e.inv_hom_id }
  exact sectionIsoOfFibreIso p hp c G H hG hH e'

private theorem sectionIsoOfValueIso_isHomLift
    {C : Type u₁} [Category.{v₁} C] {X : Type u₂} [Category.{v₂} X]
    (p : X ⥤ C) (hp : p.IsFiberedInGroupoids)
    (c : Functor.ChoiceOfPullbacks p) {U : C}
    (G H : Over U ⥤ X) (hG : G ⋙ p = Over.forget U)
    (hH : H ⋙ p = Over.forget U)
    (e : G.obj (Over.mk (𝟙 U)) ≅ H.obj (Over.mk (𝟙 U)))
    (he : p.IsHomLift (𝟙 U) e.hom) (W : Over U) :
    p.IsHomLift (𝟙 W.left)
      ((sectionIsoOfValueIso p hp c G H hG hH e he).hom.app W) := by
  unfold sectionIsoOfValueIso
  exact sectionIsoOfFibreIso_isHomLift p hp c G H hG hH _ W

private noncomputable def fibreIsoOfCartesianIso
    {C : Type u₁} [Category.{v₁} C] {X : Type u₂} [Category.{v₂} X]
    (p : X ⥤ C) (c : Functor.ChoiceOfPullbacks p)
    {U V : C} (f : U ⟶ V) {xU x : p.Fiber U} {xV : p.Fiber V}
    (β : xU.1 ⟶ x.1) (hβ : p.IsHomLift (𝟙 U) β) [IsIso β]
    (δ : xU.1 ⟶ xV.1) (hδ : p.IsStronglyCartesian f δ) :
    x ≅ c.obj f xV := by
  let βi : x.1 ⟶ xU.1 := (asIso β).symm.hom
  let : p.IsHomLift (𝟙 U) β := hβ
  have hβi : p.IsHomLift (𝟙 U) βi := IsHomLift.lift_id_inv_isIso p U β
  let := hβi
  have hβiSC : p.IsStronglyCartesian (𝟙 U) βi :=
    Functor.IsStronglyCartesian.of_iso p (𝟙 U) (asIso β).symm
  have hψSC : p.IsStronglyCartesian (𝟙 U ≫ f) (βi ≫ δ) :=
    Functor.IsStronglyCartesian.comp p
  have hψSC' : p.IsStronglyCartesian f (βi ≫ δ) := by
    simpa using hψSC
  let : p.IsStronglyCartesian f (βi ≫ δ) := hψSC'
  let : p.IsStronglyCartesian f (c.map f xV) := c.isStronglyCartesian f xV
  exact Functor.fiberIsoOfCartesian f (βi ≫ δ) (c.map f xV) inferInstance inferInstance

/-- `Spec` of two composable ring homomorphisms composes to `Spec` of their composite. -/
private theorem spec_map_comp_eq_of_comp_eq {A B C : Type u} [CommRing A] [CommRing B]
    [CommRing C] (f : A →+* B) (g : B →+* C) (h : A →+* C) (H : g.comp f = h) :
    Scheme.Spec.map (CommRingCat.ofHom g).op ≫ Scheme.Spec.map (CommRingCat.ofHom f).op =
      Scheme.Spec.map (CommRingCat.ofHom h).op := by
  rw [← Scheme.Spec.map_comp, ← op_comp, ← CommRingCat.ofHom_comp, H]

section AffineLimit

variable {R : Type u} [CommRing R] {Λ : Type u} [PartialOrder Λ]
    [Nonempty Λ] [IsDirectedOrder Λ]
    (G : Λ → Type u) [∀ i, CommRing (G i)] [∀ i, Algebra R (G i)]
    (q : ∀ i j, i ≤ j → G i →ₐ[R] G j)
    [DirectedSystem G fun i j h ↦ ⇑(q i j h)]

variable {A : Type u} [CommRing A] [Algebra R A]
    (g : ∀ i, G i →ₐ[R] A) (hg : ∀ i j h x, g j (q i j h x) = g i x)

private noncomputable def specLimitCone :
    Cone ((DirectedPresentation.ringDiagram G q).op ⋙ Scheme.Spec) :=
  Scheme.Spec.mapCone (DirectedPresentation.compatibleCocone G q g hg).op

private noncomputable def specLimitIsLimit
    (hbij : Function.Bijective (DirectLimit.Algebra.lift G q A g hg)) :
    IsLimit (specLimitCone (R := R) (Λ := Λ) G q g hg) :=
  isLimitOfPreserves Scheme.Spec (DirectedPresentation.compatibleIsColimit G q g hg hbij).op

private structure AffinePresentationData (R A : Type u) [CommRing R] [CommRing A]
    [Algebra R A] where
  Λ : Type u
  [partialOrder : PartialOrder Λ]
  [nonempty : Nonempty Λ]
  [directed : IsDirectedOrder Λ]
  G : Λ → Type u
  [commRing : ∀ i, CommRing (G i)]
  [algebra : ∀ i, Algebra R (G i)]
  q : ∀ i j, i ≤ j → G i →ₐ[R] G j
  [directedSystem : DirectedSystem G fun i j h ↦ ⇑(q i j h)]
  g : ∀ i, G i →ₐ[R] A
  hg : ∀ i j h x, g j (q i j h x) = g i x
  finitePresentation : ∀ i, Algebra.FinitePresentation R (G i)
  comparisonBijective : Function.Bijective (DirectLimit.Algebra.lift G q A g hg)

attribute [local instance] AffinePresentationData.partialOrder AffinePresentationData.nonempty
  AffinePresentationData.directed AffinePresentationData.commRing
  AffinePresentationData.algebra AffinePresentationData.directedSystem

private noncomputable def affinePresentationData (R A : Type u) [CommRing R]
    [CommRing A] [Algebra R A] : AffinePresentationData R A := by
  classical
  choose Λ hpo hne hdir G hG hAlg q hq g hg hfp htype hbij using
    Algebra.exists_directedSystem_finitePresentation_lift_bijective R A
  let := hpo
  let := hne
  let := hdir
  let : ∀ i, CommRing (G i) := hG
  let : ∀ i, Algebra R (G i) := hAlg
  let : DirectedSystem G fun i j h ↦ ⇑(q i j h) := hq
  exact ⟨Λ, G, q, g, hg, hfp, hbij⟩

private noncomputable def affinePresentationSpecIsLimit {R A : Type u}
    [CommRing R] [CommRing A] [Algebra R A]
    (D : AffinePresentationData R A) :
    IsLimit (specLimitCone (R := R) (Λ := D.Λ) D.G D.q D.g D.hg) := by
  exact specLimitIsLimit D.G D.q D.g D.hg D.comparisonBijective

private theorem affinePresentation_stage_isContained
    (B : BigFppfSite.{u}) {R A : Type u} [CommRing R] [CommRing A]
    [Algebra R A] (hR : B.Contains (Spec (.of R)))
    (D : AffinePresentationData R A) (i : D.Λ) :
    B.Contains (Spec (.of (D.G i))) := by
  let : Algebra.FinitePresentation R (D.G i) := D.finitePresentation i
  exact Scheme.size_Spec_lt_of_finiteType B.aleph0_lt_cutoff B.cutoff_isStrongPrelimit
    R (D.G i) hR

private noncomputable def affinePresentation_siteStage
    (B : BigFppfSite.{u}) {R A : Type u} [CommRing R] [CommRing A]
    [Algebra R A] (hR : B.Contains (Spec (.of R)))
    (D : AffinePresentationData R A) (i : D.Λ) :
    BigAffineFppf B (Spec (.of R)) hR := by
  let hGi := affinePresentation_stage_isContained B hR D i
  refine ⟨siteObject B (Spec (.of R)) hR hGi
      (Scheme.Spec.map (CommRingCat.ofHom (algebraMap R (D.G i))).op), ?_⟩
  change IsAffine (Spec (.of (D.G i)))
  infer_instance

private noncomputable def affinePresentation_siteTransition
    (B : BigFppfSite.{u}) {R A : Type u} [CommRing R] [CommRing A]
    [Algebra R A] (hR : B.Contains (Spec (.of R)))
    (D : AffinePresentationData R A) {i j : D.Λ} (h : j ≤ i) :
    affinePresentation_siteStage B hR D i ⟶ affinePresentation_siteStage B hR D j := by
  let Xi : B.Schemes := Over.left
    ((affinePresentation_siteStage B hR D i).1)
  let Xj : B.Schemes := Over.left
    ((affinePresentation_siteStage B hR D j).1)
  let f : B.inclusion.obj Xi ⟶ B.inclusion.obj Xj :=
    Scheme.Spec.map (CommRingCat.ofHom (D.q j i h).toRingHom).op
  let g : Xi ⟶ Xj := B.inclusion.preimage f
  have hg : B.inclusion.map g = f := by
    dsimp [g, Xi, Xj]
    exact B.inclusion.map_preimage f
  have hSpec :
      Scheme.Spec.map (CommRingCat.ofHom (D.q j i h).toRingHom).op ≫
        Scheme.Spec.map (CommRingCat.ofHom (algebraMap R (D.G j))).op =
      Scheme.Spec.map (CommRingCat.ofHom (algebraMap R (D.G i))).op :=
    spec_map_comp_eq_of_comp_eq _ _ _ (by ext r; simp)
  have hmap_j : B.inclusion.map (Over.hom
      ((BigAffineFppf.inclusion B (Spec (.of R)) hR).obj
        (affinePresentation_siteStage B hR D j))) =
      Scheme.Spec.map (CommRingCat.ofHom (algebraMap R (D.G j))).op := rfl
  have hmap_i : B.inclusion.map (Over.hom
      ((BigAffineFppf.inclusion B (Spec (.of R)) hR).obj
        (affinePresentation_siteStage B hR D i))) =
      Scheme.Spec.map (CommRingCat.ofHom (algebraMap R (D.G i))).op := rfl
  refine ⟨Over.homMk g ?_⟩
  apply B.inclusion.map_injective
  change B.inclusion.map g ≫
      B.inclusion.map (Over.hom
        ((BigAffineFppf.inclusion B (Spec (.of R)) hR).obj
          (affinePresentation_siteStage B hR D j))) =
    B.inclusion.map (Over.hom
      ((BigAffineFppf.inclusion B (Spec (.of R)) hR).obj
        (affinePresentation_siteStage B hR D i)))
  rw [hg, hmap_j, hmap_i]
  exact hSpec

private theorem affinePresentation_siteTransition_map
    (B : BigFppfSite.{u}) {R A : Type u} [CommRing R] [CommRing A]
    [Algebra R A] (hR : B.Contains (Spec (.of R)))
    (D : AffinePresentationData R A) {i j : D.Λ} (h : j ≤ i) :
    (BigAffineFppf.toScheme B (Spec (.of R)) hR).map
        (affinePresentation_siteTransition B hR D h) =
      Scheme.Spec.map (CommRingCat.ofHom (D.q j i h).toRingHom).op := by
  let Xi : B.Schemes := Over.left
    ((affinePresentation_siteStage B hR D i).1)
  let Xj : B.Schemes := Over.left
    ((affinePresentation_siteStage B hR D j).1)
  let f : B.inclusion.obj Xi ⟶ B.inclusion.obj Xj :=
    Scheme.Spec.map (CommRingCat.ofHom (D.q j i h).toRingHom).op
  let g : Xi ⟶ Xj := B.inclusion.preimage f
  have hg : B.inclusion.map g = f := B.inclusion.map_preimage f
  show B.inclusion.map g = f
  exact hg

private noncomputable def affinePresentation_siteDiagram
    (B : BigFppfSite.{u}) {R A : Type u} [CommRing R] [CommRing A]
    [Algebra R A] (hR : B.Contains (Spec (.of R)))
    (D : AffinePresentationData R A) :
    D.Λᵒᵖ ⥤ BigAffineFppf B (Spec (.of R)) hR := by
  refine {
    obj i := affinePresentation_siteStage B hR D i.unop
    map f := affinePresentation_siteTransition B hR D f.unop.le
    map_id := ?_
    map_comp := ?_ }
  · intro i
    apply (BigAffineFppf.toScheme B (Spec (.of R)) hR).map_injective
    rw [affinePresentation_siteTransition_map]
    have hq : D.q i.unop i.unop (le_refl i.unop) = AlgHom.id R (D.G i.unop) := by
      ext x
      exact DirectedSystem.map_self
        (f := fun i j h ↦ ⇑(D.q i j h)) x
    rw [hq]
    simp [affinePresentation_siteStage, siteObject, BigFppfSite.obj]
  · intro i j k f g
    apply (BigAffineFppf.toScheme B (Spec (.of R)) hR).map_injective
    rw [Functor.map_comp]
    rw [affinePresentation_siteTransition_map, affinePresentation_siteTransition_map,
      affinePresentation_siteTransition_map]
    have hki : k.unop ≤ i.unop := g.unop.le.trans f.unop.le
    have hcomp :
        Scheme.Spec.map (CommRingCat.ofHom
          (D.q k.unop i.unop hki).toRingHom).op =
          Scheme.Spec.map (CommRingCat.ofHom
            (D.q j.unop i.unop f.unop.le).toRingHom).op ≫
            Scheme.Spec.map (CommRingCat.ofHom
              (D.q k.unop j.unop g.unop.le).toRingHom).op :=
      (spec_map_comp_eq_of_comp_eq _ _ _ (by
        ext x
        exact DirectedSystem.map_map (f := fun i j h ↦ ⇑(D.q i j h))
          g.unop.le f.unop.le x)).symm
    simpa [affinePresentation_siteStage, siteObject,
      BigFppfSite.obj] using hcomp

private noncomputable def affinePresentation_sitePushforward
    (B : BigFppfSite.{u}) {R : Type u} [CommRing R]
    (hR : B.Contains (Spec (.of R))) (S : Scheme.{u}) (hS : B.Contains S)
    (f : Spec (.of R) ⟶ S) :
    BigAffineFppf B (Spec (.of R)) hR ⥤
      BigAffineFppf B S hS := by
  let f' : B.obj hR ⟶ B.obj hS := B.inclusion.preimage f
  let K := Over.map f'
  refine {
    obj i := ⟨K.obj ((BigAffineFppf.inclusion B (Spec (.of R)) hR).obj i), ?_⟩
    map g := (BigAffineFppf.inclusion B S hS).preimage
      (K.map ((BigAffineFppf.inclusion B (Spec (.of R)) hR).map g))
    map_id := ?_
    map_comp := ?_ }
  · change IsAffine ((BigFppfOver.toScheme B S hS).obj
      (K.obj ((BigAffineFppf.inclusion B (Spec (.of R)) hR).obj i)))
    simpa [K, Over.map, BigFppfOver.toScheme,
      BigFppfOver.forget, IsAffineOver] using i.property
  · intro i
    let e := BigAffineFppf.inclusion B S hS
    apply e.map_injective
    rw [e.map_preimage]
    simp [K, e]
  · intro i j k g h
    let e := BigAffineFppf.inclusion B S hS
    apply e.map_injective
    rw [e.map_preimage, e.map_comp, e.map_preimage, e.map_preimage]
    simp [K, e]

private theorem affinePresentation_sitePushforward_map
    (B : BigFppfSite.{u}) {R : Type u} [CommRing R]
    (hR : B.Contains (Spec (.of R))) (S : Scheme.{u}) (hS : B.Contains S)
    (f : Spec (.of R) ⟶ S)
    {X Y : BigAffineFppf B (Spec (.of R)) hR} (g : X ⟶ Y) :
    (BigAffineFppf.toScheme B S hS).map
        ((affinePresentation_sitePushforward B hR S hS f).map g) =
      (BigAffineFppf.toScheme B (Spec (.of R)) hR).map g := by
  let e := BigAffineFppf.inclusion B S hS
  let f' : B.obj hR ⟶ B.obj hS := B.inclusion.preimage f
  let K := Over.map f'
  have h : e.map ((affinePresentation_sitePushforward B hR S hS f).map g) =
      K.map ((BigAffineFppf.inclusion B (Spec (.of R)) hR).map g) := by
    show e.map (e.preimage _) = _
    exact e.map_preimage _
  have h := congrArg (fun z => z.left.hom) h
  rw [Over.map_map_left] at h
  simpa [affinePresentation_sitePushforward, BigAffineFppf.toScheme,
    BigFppfOver.toScheme, BigFppfOver.forget,
    K, e, Over.map] using h

private noncomputable def affinePresentation_siteDiagramOver
    (B : BigFppfSite.{u}) {R A : Type u} [CommRing R] [CommRing A]
    [Algebra R A] (hR : B.Contains (Spec (.of R))) (S : Scheme.{u})
    (hS : B.Contains S) (f : Spec (.of R) ⟶ S)
    (D : AffinePresentationData R A) :
    D.Λᵒᵖ ⥤ BigAffineFppf B S hS :=
  affinePresentation_siteDiagram B hR D ⋙
    affinePresentation_sitePushforward B hR S hS f

private noncomputable def affinePresentation_siteLimitPoint
    (B : BigFppfSite.{u}) {R A : Type u} [CommRing R] [CommRing A]
    [Algebra R A] (hR : B.Contains (Spec (.of R)))
    (hA : B.Contains (Spec (.of A))) :
    BigAffineFppf B (Spec (.of R)) hR := by
  refine ⟨siteObject B (Spec (.of R)) hR hA
    (Scheme.Spec.map (CommRingCat.ofHom (algebraMap R A)).op), ?_⟩
  change IsAffine (Spec (.of A))
  infer_instance

private noncomputable def affinePresentation_siteConeLeg
    (B : BigFppfSite.{u}) {R A : Type u} [CommRing R] [CommRing A]
    [Algebra R A] (hR : B.Contains (Spec (.of R)))
    (hA : B.Contains (Spec (.of A))) (D : AffinePresentationData R A) (i : D.Λ) :
    affinePresentation_siteLimitPoint B hR hA ⟶ affinePresentation_siteStage B hR D i := by
  let UL : B.Schemes := Over.left
    ((BigAffineFppf.inclusion B (Spec (.of R)) hR).obj
      (affinePresentation_siteLimitPoint B hR hA))
  let Xi : B.Schemes := Over.left
    ((BigAffineFppf.inclusion B (Spec (.of R)) hR).obj
      (affinePresentation_siteStage B hR D i))
  let f : B.inclusion.obj UL ⟶ B.inclusion.obj Xi :=
    Scheme.Spec.map (CommRingCat.ofHom (D.g i).toRingHom).op
  let g : UL ⟶ Xi := B.inclusion.preimage f
  have hg : B.inclusion.map g = f := B.inclusion.map_preimage f
  have hbase :
      Scheme.Spec.map (CommRingCat.ofHom (D.g i).toRingHom).op ≫
        Scheme.Spec.map (CommRingCat.ofHom (algebraMap R (D.G i))).op =
      Scheme.Spec.map (CommRingCat.ofHom (algebraMap R A)).op :=
    spec_map_comp_eq_of_comp_eq _ _ _ (by ext r; simp)
  have hmap_i : B.inclusion.map (Over.hom
      ((BigAffineFppf.inclusion B (Spec (.of R)) hR).obj
        (affinePresentation_siteStage B hR D i))) =
      Scheme.Spec.map (CommRingCat.ofHom (algebraMap R (D.G i))).op := rfl
  have hmap_A : B.inclusion.map (Over.hom
      ((BigAffineFppf.inclusion B (Spec (.of R)) hR).obj
        (affinePresentation_siteLimitPoint B hR hA))) =
      Scheme.Spec.map (CommRingCat.ofHom (algebraMap R A)).op := rfl
  refine ⟨Over.homMk g ?_⟩
  apply B.inclusion.map_injective
  change B.inclusion.map g ≫
      B.inclusion.map (Over.hom
        ((BigAffineFppf.inclusion B (Spec (.of R)) hR).obj
          (affinePresentation_siteStage B hR D i))) =
    B.inclusion.map (Over.hom
      ((BigAffineFppf.inclusion B (Spec (.of R)) hR).obj
        (affinePresentation_siteLimitPoint B hR hA)) )
  rw [hg, hmap_i, hmap_A]
  exact hbase

private theorem affinePresentation_siteConeLeg_map
    (B : BigFppfSite.{u}) {R A : Type u} [CommRing R] [CommRing A]
    [Algebra R A] (hR : B.Contains (Spec (.of R)))
    (hA : B.Contains (Spec (.of A))) (D : AffinePresentationData R A) (i : D.Λ) :
    (BigAffineFppf.toScheme B (Spec (.of R)) hR).map
        (affinePresentation_siteConeLeg B hR hA D i) =
      Scheme.Spec.map (CommRingCat.ofHom (D.g i).toRingHom).op := by
  let UL : B.Schemes := Over.left
    ((BigAffineFppf.inclusion B (Spec (.of R)) hR).obj
      (affinePresentation_siteLimitPoint B hR hA))
  let Xi : B.Schemes := Over.left
    ((BigAffineFppf.inclusion B (Spec (.of R)) hR).obj
      (affinePresentation_siteStage B hR D i))
  let f : B.inclusion.obj UL ⟶ B.inclusion.obj Xi :=
    Scheme.Spec.map (CommRingCat.ofHom (D.g i).toRingHom).op
  let g : UL ⟶ Xi := B.inclusion.preimage f
  show B.inclusion.map g = f
  exact B.inclusion.map_preimage f

private noncomputable def affinePresentation_siteCone
    (B : BigFppfSite.{u}) {R A : Type u} [CommRing R] [CommRing A]
    [Algebra R A] (hR : B.Contains (Spec (.of R)))
    (hA : B.Contains (Spec (.of A))) (D : AffinePresentationData R A) :
    Cone (affinePresentation_siteDiagram B hR D) := by
  refine {
    pt := affinePresentation_siteLimitPoint B hR hA
    π := {
      app i := affinePresentation_siteConeLeg B hR hA D i.unop
      naturality := ?_ } }
  intro i j f
  dsimp [affinePresentation_siteDiagram]
  simp only [Category.id_comp]
  apply (BigAffineFppf.toScheme B (Spec (.of R)) hR).map_injective
  rw [Functor.map_comp]
  rw [affinePresentation_siteConeLeg_map,
    affinePresentation_siteTransition_map,
    affinePresentation_siteConeLeg_map]
  have hcompat :
      Scheme.Spec.map (CommRingCat.ofHom
        (D.g i.unop).toRingHom).op ≫
        Scheme.Spec.map (CommRingCat.ofHom
          (D.q j.unop i.unop f.unop.le).toRingHom).op =
      Scheme.Spec.map (CommRingCat.ofHom (D.g j.unop).toRingHom).op :=
    spec_map_comp_eq_of_comp_eq _ _ _ (by ext x; exact D.hg j.unop i.unop f.unop.le x)
  simpa [affinePresentation_siteStage, affinePresentation_siteLimitPoint,
    siteObject,
    BigFppfSite.obj] using hcompat.symm

private noncomputable def affinePresentation_siteConeOver
    (B : BigFppfSite.{u}) {R A : Type u} [CommRing R] [CommRing A]
    [Algebra R A] (hR : B.Contains (Spec (.of R))) (S : Scheme.{u})
    (hS : B.Contains S) (f : Spec (.of R) ⟶ S)
    (hA : B.Contains (Spec (.of A))) (D : AffinePresentationData R A) :
    Cone (affinePresentation_siteDiagramOver B hR S hS f D) :=
  (affinePresentation_sitePushforward B hR S hS f).mapCone
    (affinePresentation_siteCone B hR hA D)

private noncomputable def affinePresentation_siteCone_isLimit
    (B : BigFppfSite.{u}) {R A : Type u} [CommRing R] [CommRing A]
    [Algebra R A] (hR : B.Contains (Spec (.of R)))
    (hA : B.Contains (Spec (.of A))) (D : AffinePresentationData R A) :
    IsLimit ((BigAffineFppf.toScheme B (Spec (.of R)) hR).mapCone
      (affinePresentation_siteCone B hR hA D)) := by
  let F := affinePresentation_siteDiagram B hR D ⋙
    BigAffineFppf.toScheme B (Spec (.of R)) hR
  let G := (DirectedPresentation.ringDiagram D.G D.q).op ⋙ Scheme.Spec
  let α : F ≅ G := NatIso.ofComponents (fun i => Iso.refl _) (by
    intro i j f
    change (BigAffineFppf.toScheme B (Spec (.of R)) hR).map
        (affinePresentation_siteTransition B hR D f.unop.le) =
      Scheme.Spec.map (CommRingCat.ofHom
        (D.q j.unop i.unop f.unop.le).toRingHom).op
    exact affinePresentation_siteTransition_map B hR D f.unop.le)
  let c := (BigAffineFppf.toScheme B (Spec (.of R)) hR).mapCone
    (affinePresentation_siteCone B hR hA D)
  let d := specLimitCone D.G D.q D.g D.hg
  have hw : (Cone.postcompose α.hom).obj c ≅ d := by
    refine Cone.ext (Iso.refl _) ?_
    intro i
    change (BigAffineFppf.toScheme B (Spec (.of R)) hR).map
        (affinePresentation_siteConeLeg B hR hA D i.unop) ≫ 𝟙 _ =
      Scheme.Spec.map (CommRingCat.ofHom (D.g i.unop).toRingHom).op
    rw [affinePresentation_siteConeLeg_map]
    exact Category.comp_id _
  exact (IsLimit.equivOfNatIsoOfIso α c d hw).symm
    (affinePresentationSpecIsLimit D)

private noncomputable def affinePresentation_siteConeOver_isLimit
    (B : BigFppfSite.{u}) {R A : Type u} [CommRing R] [CommRing A]
    [Algebra R A] (hR : B.Contains (Spec (.of R))) (S : Scheme.{u})
    (hS : B.Contains S) (f : Spec (.of R) ⟶ S)
    (hA : B.Contains (Spec (.of A))) (D : AffinePresentationData R A) :
    IsLimit ((BigAffineFppf.toScheme B S hS).mapCone
      (affinePresentation_siteConeOver B hR S hS f hA D)) := by
  let F := affinePresentation_siteDiagramOver B hR S hS f D ⋙
    BigAffineFppf.toScheme B S hS
  let G := affinePresentation_siteDiagram B hR D ⋙
    BigAffineFppf.toScheme B (Spec (.of R)) hR
  let α : F ≅ G := NatIso.ofComponents (fun _ ↦ Iso.refl _) (by
    intro i j f'
    exact affinePresentation_sitePushforward_map B hR S hS f
      ((affinePresentation_siteDiagram B hR D).map f'))
  let c := (BigAffineFppf.toScheme B S hS).mapCone
    (affinePresentation_siteConeOver B hR S hS f hA D)
  let d := (BigAffineFppf.toScheme B (Spec (.of R)) hR).mapCone
    (affinePresentation_siteCone B hR hA D)
  have hw : (Cone.postcompose α.hom).obj c ≅ d := by
    refine Cone.ext (Iso.refl _) ?_
    intro i
    change (BigAffineFppf.toScheme B S hS).map
        ((affinePresentation_sitePushforward B hR S hS f).map
          ((affinePresentation_siteCone B hR hA D).π.app i)) ≫ 𝟙 _ =
      𝟙 _ ≫ (BigAffineFppf.toScheme B (Spec (.of R)) hR).map
        ((affinePresentation_siteCone B hR hA D).π.app i)
    rw [affinePresentation_sitePushforward_map]
    exact Category.comp_id _
  exact (IsLimit.equivOfNatIsoOfIso α c d hw).symm
    (affinePresentation_siteCone_isLimit B hR hA D)

end AffineLimit

attribute [local instance] AffinePresentationData.partialOrder AffinePresentationData.nonempty
  AffinePresentationData.directed AffinePresentationData.commRing
  AffinePresentationData.algebra AffinePresentationData.directedSystem

private theorem exists_fiberIso_pullback_of_limitPreserving
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (𝒴 : CatFiberedInGroupoids.{u, u, u + 1, u + 1}
      (BigFppfOver B S hS))
    (hlimit : BigFppfOver.IsLimitPreservingOnObjects.{u, u, u, u, u + 1}
      B S hS 𝒴 (terminalCFG B S hS)
      (Bicategory.InducedBicategory.mkHom
        (toTerminalCFG B S hS 𝒴)))
    (I : Type u) [Category.{u} I] [IsCofiltered I]
    (D : I ⥤ BigAffineFppf B S hS) (c : Cone D)
    (hc : IsLimit ((BigAffineFppf.toScheme B S hS).mapCone c))
    (x : 𝒴.val.p.Fiber ((BigAffineFppf.inclusion B S hS).obj c.pt))
    (pullbacks : Functor.ChoiceOfPullbacks 𝒴.val.p) :
    ∃ (i : I) (xi : 𝒴.val.p.Fiber
        ((BigAffineFppf.inclusion B S hS).obj (D.obj i))),
      Nonempty (x ≅ pullbacks.obj
        ((BigAffineFppf.inclusion B S hS).map (c.π.app i)) xi) := by
  have : Nonempty I := IsCofiltered.nonempty
  let i : I := Classical.arbitrary I
  let inc := BigAffineFppf.inclusion B S hS
  let γ : 𝒴.val.p.obj x.1 ⟶ inc.obj (D.obj i) :=
    eqToHom x.2 ≫ inc.map (c.π.app i)
  have hγ : (𝟭 (BigFppfOver B S hS)).IsHomLift
      (inc.map (c.π.app i)) γ :=
    IsHomLift.of_fac' _ _ _ x.2 rfl (by simp [γ])
  have : (terminalCFG B S hS).val.p.IsHomLift
      (inc.map (c.π.app i)) γ := hγ
  have hγcart : (𝟭 (BigFppfOver B S hS)).IsStronglyCartesian
      (inc.map (c.π.app i)) γ :=
    (terminalCFG B S hS).2.isStronglyCartesian_homLift _ γ
  obtain ⟨i', j, xi, xU, δ, β, γ', hδ, hβ, hβiso, hγ', hcomm⟩ :=
    hlimit I D c hc i ⟨inc.obj (D.obj i), rfl⟩ x γ hγcart
  have := hβiso
  exact ⟨i', xi, ⟨fibreIsoOfCartesianIso 𝒴.val.p pullbacks _ β hβ δ hδ⟩⟩

private theorem exists_sectionIso_of_limitPreserving
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (𝒴 : CatFiberedInGroupoids.{u, u, u + 1, u + 1}
      (BigFppfOver B S hS))
    (hlimit : BigFppfOver.IsLimitPreservingOnObjects.{u, u, u, u, u + 1}
      B S hS 𝒴 (terminalCFG B S hS)
      (Bicategory.InducedBicategory.mkHom
        (toTerminalCFG B S hS 𝒴)))
    (I : Type u) [Category.{u} I] [IsCofiltered I]
    (D : I ⥤ BigAffineFppf B S hS) (c : Cone D)
    (hc : IsLimit ((BigAffineFppf.toScheme B S hS).mapCone c))
    (G : Over ((BigAffineFppf.inclusion B S hS).obj c.pt) ⥤ 𝒴.val.obj)
    (hG : G ⋙ 𝒴.val.p = Over.forget ((BigAffineFppf.inclusion B S hS).obj c.pt))
    (pullbacks : Functor.ChoiceOfPullbacks 𝒴.val.p) :
    ∃ (i : I) (x : 𝒴.val.p.Fiber
        ((BigAffineFppf.inclusion B S hS).obj (D.obj i)))
      (a : G ≅ Over.map
        ((BigAffineFppf.inclusion B S hS).map (c.π.app i)) ⋙
          pullbacks.sliceFunctor x),
      ∀ W, 𝒴.val.p.IsHomLift (𝟙 W.left) (a.hom.app W) := by
  obtain ⟨i, x, ⟨e⟩⟩ := exists_fiberIso_pullback_of_limitPreserving
    B S hS 𝒴 hlimit I D c hc (Functor.ChoiceOfPullbacks.sliceObj G hG) pullbacks
  obtain ⟨a, ha⟩ := exists_sectionIso_of_fiberIso 𝒴.val.p
    (CatFiberedInGroupoids.isFiberedInGroupoids 𝒴) pullbacks
    ((BigAffineFppf.inclusion B S hS).map (c.π.app i)) G hG x e
  exact ⟨i, x, a, ha⟩

private noncomputable def sectionIso_of_iteratedSlice
    {C : Type u₁} [Category.{v₁} C] {S : C}
    {U V : Over S} (q : U ⟶ V)
    {X : Type u₂} [Category.{v₂} X]
    (y : Over U.left ⥤ X) (z : Over V ⥤ X)
    (a : U.iteratedSliceForward ⋙ y ≅ Over.map q ⋙ z) :
    y ≅ Over.map q.left ⋙ V.iteratedSliceBackward ⋙ z := by
  calc
    y ≅ (𝟭 (Over U.left)) ⋙ y := (Functor.leftUnitor y).symm
    _ ≅ (U.iteratedSliceBackward ⋙ U.iteratedSliceForward) ⋙ y :=
      Functor.isoWhiskerRight U.iteratedSliceEquiv.counitIso.symm y
    _ ≅ U.iteratedSliceBackward ⋙ (U.iteratedSliceForward ⋙ y) :=
      Functor.associator _ _ _
    _ ≅ U.iteratedSliceBackward ⋙ (Over.map q ⋙ z) :=
      Functor.isoWhiskerLeft _ a
    _ ≅ (U.iteratedSliceBackward ⋙ Over.map q) ⋙ z :=
      (Functor.associator _ _ _).symm
    _ ≅ (Over.map q.left ⋙ V.iteratedSliceBackward) ⋙ z :=
      Functor.isoWhiskerRight (iteratedSliceBackward_mapIso q) z
    _ ≅ Over.map q.left ⋙ V.iteratedSliceBackward ⋙ z :=
      Functor.associator _ _ _

-- The comparison isomorphism is transported along the iterated-slice equivalence, so the
-- components to be identified are typed through it.
attribute [local implicit_reducible] sectionIso_of_iteratedSlice iteratedSliceBackward_mapIso
  Over.iteratedSliceBackward Over.iteratedSliceForward Over.iteratedSliceEquivOverMapIso in
private theorem sectionIso_of_iteratedSlice_isHomLift
    {C : Type u₁} [Category.{v₁} C] {S : C}
    {U V : Over S} (q : U ⟶ V)
    {X : Type u₂} [Category.{v₂} X] (p : X ⥤ Over S)
    (y : Over U.left ⥤ X) (z : Over V ⥤ X)
    (hy : y ⋙ p = Over.map U.hom)
    (hz : z ⋙ p = Over.forget V)
    (a : U.iteratedSliceForward ⋙ y ≅ Over.map q ⋙ z)
    (ha : ∀ W, p.IsHomLift (𝟙 W.left) (a.hom.app W))
    (W : Over U.left) :
    p.IsHomLift (𝟙 ((Over.map U.hom).obj W))
      ((sectionIso_of_iteratedSlice q y z a).hom.app W) := by
  have hsource : p.obj (y.obj W) = (Over.map U.hom).obj W :=
    Functor.congr_obj hy W
  have ht : (Over.map q.left ⋙ V.iteratedSliceBackward ⋙ z) ⋙ p =
      Over.map U.hom := by
    calc
      _ = Over.map q.left ⋙ V.iteratedSliceBackward ⋙ (z ⋙ p) := rfl
      _ = Over.map q.left ⋙ V.iteratedSliceBackward ⋙ Over.forget V := by rw [hz]
      _ = Over.map q.left ⋙ Over.map V.hom := by
        rw [Over.iteratedSliceBackward_forget]
      _ = Over.map U.hom := by rw [← Over.mapComp_eq, Over.w q]
  have htarget : p.obj
      ((Over.map q.left ⋙ V.iteratedSliceBackward ⋙ z).obj W) =
      (Over.map U.hom).obj W := Functor.congr_obj ht W
  apply IsHomLift.of_fac' p _ _ hsource htarget
  have haW := IsHomLift.fac' p (𝟙 (U.iteratedSliceBackward.obj W).left)
    (a.hom.app (U.iteratedSliceBackward.obj W))
  have hmapy {A B : Over U.left} (g : A ⟶ B) :
      p.map (y.map g) =
        eqToHom (Functor.congr_obj hy A) ≫ (Over.map U.hom).map g ≫
          eqToHom (Functor.congr_obj hy B).symm :=
    Functor.congr_hom hy g
  have hmapz {A B : Over V} (g : A ⟶ B) :
      p.map (z.map g) =
        eqToHom (Functor.congr_obj hz A) ≫ (Over.forget V).map g ≫
          eqToHom (Functor.congr_obj hz B).symm :=
    Functor.congr_hom hz g
  apply Over.OverMorphism.ext
  simp [sectionIso_of_iteratedSlice, iteratedSliceBackward_mapIso,
    hmapz, haW]
  simp [Over.iteratedSliceEquiv, Over.iteratedSliceForward,
    Over.iteratedSliceBackward, hmapy]
private theorem iteratedSliceForward_overMap_eq_forget
    (B : BigFppfSite.{u}) {S : Scheme.{u}} {hS : B.Contains S}
    (U : BigFppfOver B S hS) :
    Over.iteratedSliceForward U ⋙ Over.map U.hom = Over.forget U := by
  apply CategoryTheory.Functor.ext
  · intro A A' g
    cases A
    cases A'
    apply Over.OverMorphism.ext
    simp only [Functor.comp_map, Over.iteratedSliceForward_map]
    try simp only [Over.comp_left, Over.eqToHom_left]
    exact (conj_eqToHom_iff_heq' (Over.Hom.left (Over.Hom.left g))
      (Over.Hom.left (Over.Hom.left g)) rfl rfl).2 HEq.rfl
  · intro A
    cases A with
    | mk Aleft _ Ahom =>
      cases Aleft with
      | mk _ _ AtoS =>
        show Over.mk (Ahom.left ≫ U.hom) = Over.mk AtoS
        congr 1
        exact Ahom.w

private noncomputable def sectionFromFiberObject
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (𝒴 : CatFiberedInGroupoids.{u, v₁, u + 1, v₂}
      (BigFppfOver B S hS))
    (U : BigFppfOver B S hS)
    (x : 𝒴.val.p.Fiber U) :
    (BigFppfOver B U.left.1 U.left.2) ⥤ 𝒴.val.obj := by
  let : 𝒴.val.p.IsFibered :=
    (CatFiberedInGroupoids.isFiberedInGroupoids 𝒴).isFibered
  let G := Functor.FiberedMor.OfFiberObj.fiberedMor 𝒴.val.p U x.2
  exact Over.iteratedSliceBackward U ⋙ G.toFunctor

private theorem sectionFromFiberObject_eq_chosenPullbacks
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (𝒴 : CatFiberedInGroupoids.{u, v₁, u + 1, v₂}
      (BigFppfOver B S hS))
    [𝒴.val.p.IsFibered]
    (U : BigFppfOver B S hS)
    (x : 𝒴.val.p.Fiber U) :
    sectionFromFiberObject B S hS 𝒴 U x =
      Over.iteratedSliceBackward U ⋙ (Functor.chosenPullbacks 𝒴.val.p).sliceFunctor x := by
  rfl

private theorem sectionFromFiberObject_comp
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (𝒴 : CatFiberedInGroupoids.{u, v₁, u + 1, v₂}
      (BigFppfOver B S hS))
    (U : BigFppfOver B S hS)
    (x : 𝒴.val.p.Fiber U) :
    sectionFromFiberObject B S hS 𝒴 U x ⋙ 𝒴.val.p = Over.map U.hom := by
  let : 𝒴.val.p.IsFibered :=
    (CatFiberedInGroupoids.isFiberedInGroupoids 𝒴).isFibered
  let G := Functor.FiberedMor.OfFiberObj.fiberedMor 𝒴.val.p U x.2
  show (Over.iteratedSliceBackward U ⋙ G.toFunctor) ⋙ 𝒴.val.p = Over.map U.hom
  calc
    (Over.iteratedSliceBackward U ⋙ G.toFunctor) ⋙ 𝒴.val.p =
        Over.iteratedSliceBackward U ⋙ (G.toFunctor ⋙ 𝒴.val.p) := rfl
    _ = Over.iteratedSliceBackward U ⋙ Over.forget U := by
      have hG : G.toFunctor ⋙ 𝒴.val.p = Over.forget U := by
        show G.toFunctor ⋙ (BasedCategory.ofFunctor 𝒴.val.p).p = Over.forget U
        exact G.w
      exact congrArg (fun F => Over.iteratedSliceBackward U ⋙ F) hG
    _ = Over.map U.hom := Over.iteratedSliceBackward_forget U

private theorem exists_sectionIso_of_limitPreserving_smallerBase
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (𝒴 : CatFiberedInGroupoids.{u, u, u + 1, u + 1}
      (BigFppfOver B S hS))
    (hlimit : BigFppfOver.IsLimitPreservingOnObjects.{u, u, u, u, u + 1}
      B S hS 𝒴 (terminalCFG B S hS)
      (Bicategory.InducedBicategory.mkHom
        (toTerminalCFG B S hS 𝒴)))
    (I : Type u) [Category.{u} I] [IsCofiltered I]
    (D : I ⥤ BigAffineFppf B S hS) (c : Cone D)
    (hc : IsLimit ((BigAffineFppf.toScheme B S hS).mapCone c))
    (y : BigFppfOver B
      ((BigAffineFppf.inclusion B S hS).obj c.pt).left.1
      ((BigAffineFppf.inclusion B S hS).obj c.pt).left.2 ⥤ 𝒴.val.obj)
    (hy : y ⋙ 𝒴.val.p = Over.map
      ((BigAffineFppf.inclusion B S hS).obj c.pt).hom) :
    ∃ (i : I) (x : 𝒴.val.p.Fiber
        ((BigAffineFppf.inclusion B S hS).obj (D.obj i))),
      ∃ (a : y ≅ Over.map
        ((BigAffineFppf.inclusion B S hS).map (c.π.app i)).left ⋙
        sectionFromFiberObject B S hS 𝒴
          ((BigAffineFppf.inclusion B S hS).obj (D.obj i)) x),
        ∀ W, 𝒴.val.p.IsHomLift (𝟙 ((Over.map
          ((BigAffineFppf.inclusion B S hS).obj c.pt).hom).obj W))
          (a.hom.app W) := by
  let U := (BigAffineFppf.inclusion B S hS).obj c.pt
  let : 𝒴.val.p.IsFibered :=
    (CatFiberedInGroupoids.isFiberedInGroupoids 𝒴).isFibered
  let pullbacks := Functor.chosenPullbacks 𝒴.val.p
  have hG : (Over.iteratedSliceForward U ⋙ y) ⋙ 𝒴.val.p = Over.forget U := by
    rw [Functor.assoc, hy]
    exact iteratedSliceForward_overMap_eq_forget B U
  obtain ⟨i, x, a, ha⟩ := exists_sectionIso_of_limitPreserving B S hS 𝒴
    hlimit I D c hc (Over.iteratedSliceForward U ⋙ y) hG pullbacks
  let V := (BigAffineFppf.inclusion B S hS).obj (D.obj i)
  let q : U ⟶ V := (BigAffineFppf.inclusion B S hS).map (c.π.app i)
  let a' : y ≅ Over.map q.left ⋙ V.iteratedSliceBackward ⋙
      pullbacks.sliceFunctor x := sectionIso_of_iteratedSlice q y
        (pullbacks.sliceFunctor x) a
  refine ⟨i, x, a', ?_⟩
  intro W
  exact sectionIso_of_iteratedSlice_isHomLift q 𝒴.val.p y
    (pullbacks.sliceFunctor x) hy (pullbacks.sliceFunctor_comp x) a ha W

private theorem affinePresentation_stage_map_locallyOfFinitePresentation
    (B : BigFppfSite.{u}) {R A : Type u} [CommRing R] [CommRing A]
    [Algebra R A] (hR : B.Contains (Spec (.of R))) (D : AffinePresentationData R A)
    (i : D.Λᵒᵖ) :
    LocallyOfFinitePresentation (B.inclusion.map
      ((BigAffineFppf.inclusion B (Spec (.of R)) hR).obj
        ((affinePresentation_siteDiagram B hR D).obj i)).hom) := by
  let : Algebra.FinitePresentation R (D.G i.unop) := D.finitePresentation i.unop
  show LocallyOfFinitePresentation
    (Scheme.Spec.map (CommRingCat.ofHom (algebraMap R (D.G i.unop))).op)
  exact (LocallyOfFinitePresentation.SpecMap_iff
    (CommRingCat.ofHom (algebraMap R (D.G i.unop)))).2 (by
      show (algebraMap R (D.G i.unop)).FinitePresentation
      rw [RingHom.finitePresentation_algebraMap]
      exact D.finitePresentation i.unop)

private theorem affinePresentation_stageOver_map_locallyOfFinitePresentation
    (B : BigFppfSite.{u}) {R A : Type u} [CommRing R] [CommRing A]
    [Algebra R A] (hR : B.Contains (Spec (.of R))) (S : Scheme.{u})
    (hS : B.Contains S) (g : Spec (.of R) ⟶ S) [LocallyOfFinitePresentation g]
    (D : AffinePresentationData R A) (i : D.Λᵒᵖ) :
    LocallyOfFinitePresentation (B.inclusion.map
      ((BigAffineFppf.inclusion B S hS).obj
        ((affinePresentation_siteDiagramOver B hR S hS g D).obj i)).hom) := by
  have : LocallyOfFinitePresentation (B.inclusion.map
      ((BigAffineFppf.inclusion B (Spec (.of R)) hR).obj
        ((affinePresentation_siteDiagram B hR D).obj i)).hom) :=
    affinePresentation_stage_map_locallyOfFinitePresentation B hR D i
  show LocallyOfFinitePresentation
    (B.inclusion.map
      (((BigAffineFppf.inclusion B (Spec (.of R)) hR).obj
        ((affinePresentation_siteDiagram B hR D).obj i)).hom ≫
        B.inclusion.preimage (X := B.obj hR) (Y := B.obj hS) g))
  rw [Functor.map_comp, Functor.map_preimage]
  infer_instance

private theorem exists_representative_with_property_at_affine_finitePresentation
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (P : MorphismProperty (AlgebraicSpaces B S hS))
    [P.IsStableUnderBaseChange]
    [P.IsLocalAtTarget (Space.Topology.fppf.precoverage B S hS)]
    {𝒳 𝒴 : CatFiberedInGroupoids.{u, u, u + 1, u + 1}
      (BigFppfOver B S hS)}
    (f : 𝒳 ⟶ 𝒴)
    (hf : IsRepresentableByAlgebraicSpaces B S hS f.hom)
    (hlocal : ∀ (U : BigFppfOver B S hS),
      IsAffine U.left.1 →
      LocallyOfFinitePresentation (B.inclusion.map U.hom) →
      ∀ (y : BigFppfOver B U.left.1 U.left.2 ⥤ 𝒴.val.obj)
        (_hy : y ⋙ 𝒴.val.p = Over.map U.hom)
        (F : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u)
        (hF : IsAlgebraicSpace B U.left.1 U.left.2 F),
        Nonempty (StacksRepresentableCFG.EquivalenceOver
          (TwoFibreProductOver.fst (Over.map U.hom) 𝒳.val.p 𝒴.val.p y
            (CatFiberedInGroupoids.homFunctor f))
          (presheafOfCategories (F ⋙ typeToCat)).p) →
        P (algebraicSpaceMap B S hS U
          ((spacesOverSmallerBaseFunctor
            B U.left.1 S U.left.2 hS U.hom).obj ⟨F, hF⟩)))
    (U : BigFppfOver B S hS) (hU : IsAffine U.left.1)
    (hfp : LocallyOfFinitePresentation (B.inclusion.map U.hom))
    (y : BigFppfOver B U.left.1 U.left.2 ⥤ 𝒴.val.obj)
    (hy : y ⋙ 𝒴.val.p = Over.map U.hom) :
    ∃ (F : AlgebraicSpaces B U.left.1 U.left.2),
      Nonempty (StacksRepresentableCFG.EquivalenceOver
        (TwoFibreProductOver.fst (Over.map U.hom) 𝒳.val.p 𝒴.val.p y
          (CatFiberedInGroupoids.homFunctor f))
        (PresheafOfCategories.discreteProjection F.obj)) ∧
      P (algebraicSpaceMap B S hS U
        ((spacesOverSmallerBaseFunctor
          B U.left.1 S U.left.2 hS U.hom).obj F)) := by
  obtain ⟨F, hF, ⟨e⟩⟩ := hf U y hy
  exact ⟨⟨F, hF⟩, ⟨e⟩, hlocal U hU hfp y hy F hF ⟨e⟩⟩

private theorem represented_property_of_affine_stage
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (P : MorphismProperty (AlgebraicSpaces B S hS))
    [P.IsStableUnderBaseChange]
    [P.IsLocalAtTarget (Space.Topology.fppf.precoverage B S hS)]
    {𝒳 𝒴 : CatFiberedInGroupoids.{u, u, u + 1, u + 1}
      (BigFppfOver B S hS)}
    (f : 𝒳 ⟶ 𝒴)
    (hf : IsRepresentableByAlgebraicSpaces B S hS f.hom)
    (hlocal : ∀ (U : BigFppfOver B S hS),
      IsAffine U.left.1 →
      LocallyOfFinitePresentation (B.inclusion.map U.hom) →
      ∀ (y : BigFppfOver B U.left.1 U.left.2 ⥤ 𝒴.val.obj)
        (_hy : y ⋙ 𝒴.val.p = Over.map U.hom)
        (F : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u)
        (hF : IsAlgebraicSpace B U.left.1 U.left.2 F),
        Nonempty (StacksRepresentableCFG.EquivalenceOver
          (TwoFibreProductOver.fst (Over.map U.hom) 𝒳.val.p 𝒴.val.p y
            (CatFiberedInGroupoids.homFunctor f))
          (presheafOfCategories (F ⋙ typeToCat)).p) →
        P (algebraicSpaceMap B S hS U
          ((spacesOverSmallerBaseFunctor
            B U.left.1 S U.left.2 hS U.hom).obj ⟨F, hF⟩)))
    {U V : BigFppfOver B S hS} (q : U ⟶ V)
    (hV : IsAffine V.left.1)
    (hVfp : LocallyOfFinitePresentation (B.inclusion.map V.hom))
    (yV : BigFppfOver B V.left.1 V.left.2 ⥤ 𝒴.val.obj)
    (hyV : yV ⋙ 𝒴.val.p = Over.map V.hom)
    (yU : BigFppfOver B U.left.1 U.left.2 ⥤ 𝒴.val.obj)
    (a : yU ≅ Over.map q.left ⋙ yV)
    (ha : ∀ W, 𝒴.val.p.IsHomLift (𝟙 ((Over.map U.hom).obj W)) (a.hom.app W))
    (F : AlgebraicSpaces B U.left.1 U.left.2)
    (eF : StacksRepresentableCFG.EquivalenceOver
      (TwoFibreProductOver.fst (Over.map U.hom) 𝒳.val.p 𝒴.val.p yU
        (CatFiberedInGroupoids.homFunctor f)) (PresheafOfCategories.discreteProjection F.obj)) :
    P (algebraicSpaceMap B S hS U
      ((spacesOverSmallerBaseFunctor
        B U.left.1 S U.left.2 hS U.hom).obj F)) := by
  obtain ⟨G, ⟨eG⟩, hG⟩ :=
    exists_representative_with_property_at_affine_finitePresentation
      B S hS P f hf hlocal V hV hVfp yV hyV
  exact algebraicSpaceMap_property_of_sectionIso
    B S hS P f q yV yU a ha G F eG eF hG

private theorem represented_property_of_affine_presentation
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (P : MorphismProperty (AlgebraicSpaces B S hS))
    [P.IsStableUnderBaseChange]
    [P.IsLocalAtTarget (Space.Topology.fppf.precoverage B S hS)]
    {𝒳 𝒴 : CatFiberedInGroupoids.{u, u, u + 1, u + 1}
      (BigFppfOver B S hS)}
    (f : 𝒳 ⟶ 𝒴)
    (hf : IsRepresentableByAlgebraicSpaces B S hS f.hom)
    (hlimit : BigFppfOver.IsLimitPreservingOnObjects.{u, u, u, u, u + 1}
      B S hS 𝒴 (terminalCFG B S hS)
      (Bicategory.InducedBicategory.mkHom
        (toTerminalCFG B S hS 𝒴)))
    (hlocal : ∀ (U : BigFppfOver B S hS),
      IsAffine U.left.1 →
      LocallyOfFinitePresentation (B.inclusion.map U.hom) →
      ∀ (y : BigFppfOver B U.left.1 U.left.2 ⥤ 𝒴.val.obj)
        (_hy : y ⋙ 𝒴.val.p = Over.map U.hom)
        (F : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u)
        (hF : IsAlgebraicSpace B U.left.1 U.left.2 F),
        Nonempty (StacksRepresentableCFG.EquivalenceOver
          (TwoFibreProductOver.fst (Over.map U.hom) 𝒳.val.p 𝒴.val.p y
            (CatFiberedInGroupoids.homFunctor f))
          (presheafOfCategories (F ⋙ typeToCat)).p) →
        P (algebraicSpaceMap B S hS U
          ((spacesOverSmallerBaseFunctor
            B U.left.1 S U.left.2 hS U.hom).obj ⟨F, hF⟩)))
    {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    (hR : B.Contains (Spec (.of R)))
    (g : Spec (.of R) ⟶ S) [LocallyOfFinitePresentation g]
    (hA : B.Contains (Spec (.of A)))
    (D : AffinePresentationData R A)
    (y : BigFppfOver B
      ((BigAffineFppf.inclusion B S hS).obj
        (affinePresentation_siteConeOver B hR S hS g hA D).pt).left.1
      ((BigAffineFppf.inclusion B S hS).obj
        (affinePresentation_siteConeOver B hR S hS g hA D).pt).left.2 ⥤ 𝒴.val.obj)
    (hy : y ⋙ 𝒴.val.p = Over.map
      ((BigAffineFppf.inclusion B S hS).obj
        (affinePresentation_siteConeOver B hR S hS g hA D).pt).hom)
    (F : AlgebraicSpaces B
      ((BigAffineFppf.inclusion B S hS).obj
        (affinePresentation_siteConeOver B hR S hS g hA D).pt).left.1
      ((BigAffineFppf.inclusion B S hS).obj
        (affinePresentation_siteConeOver B hR S hS g hA D).pt).left.2)
    (eF : StacksRepresentableCFG.EquivalenceOver
      (TwoFibreProductOver.fst (Over.map
        ((BigAffineFppf.inclusion B S hS).obj
          (affinePresentation_siteConeOver B hR S hS g hA D).pt).hom)
        𝒳.val.p 𝒴.val.p y (CatFiberedInGroupoids.homFunctor f))
      (PresheafOfCategories.discreteProjection F.obj)) :
    P (algebraicSpaceMap B S hS
      ((BigAffineFppf.inclusion B S hS).obj
        (affinePresentation_siteConeOver B hR S hS g hA D).pt)
      ((spacesOverSmallerBaseFunctor B
        ((BigAffineFppf.inclusion B S hS).obj
          (affinePresentation_siteConeOver B hR S hS g hA D).pt).left.1
        S _ hS _).obj F)) := by
  let c := affinePresentation_siteConeOver B hR S hS g hA D
  let D' := affinePresentation_siteDiagramOver B hR S hS g D
  obtain ⟨i, x, a, ha⟩ := exists_sectionIso_of_limitPreserving_smallerBase
    B S hS 𝒴 hlimit _ D' c
      (affinePresentation_siteConeOver_isLimit B hR S hS g hA D) y hy
  let V := (BigAffineFppf.inclusion B S hS).obj (D'.obj i)
  let q := (BigAffineFppf.inclusion B S hS).map (c.π.app i)
  let yV := sectionFromFiberObject B S hS 𝒴 V x
  have hyV : yV ⋙ 𝒴.val.p = Over.map V.hom :=
    sectionFromFiberObject_comp B S hS 𝒴 V x
  have hV : IsAffine V.left.1 := (D'.obj i).property
  have hfp : LocallyOfFinitePresentation (B.inclusion.map V.hom) :=
    affinePresentation_stageOver_map_locallyOfFinitePresentation B hR S hS g D i
  exact represented_property_of_affine_stage B S hS P f hf hlocal q
    hV hfp yV hyV y a ha F eF

private theorem limitPreserving_small
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (𝒴 : CatFiberedInGroupoids.{u, u, u + 1, u + 1}
      (BigFppfOver B S hS))
    (h : BigFppfOver.IsLimitPreservingOnObjects.{u, max u vI, max u wI, u, u + 1}
      B S hS 𝒴 (terminalCFG B S hS)
      (Bicategory.InducedBicategory.mkHom
        (toTerminalCFG B S hS 𝒴))) :
    BigFppfOver.IsLimitPreservingOnObjects.{u, u, u, u, u + 1}
      B S hS 𝒴 (terminalCFG B S hS)
      (Bicategory.InducedBicategory.mkHom
        (toTerminalCFG B S hS 𝒴)) := by
  intro I _ _ D c hc i y x γ hγ
  let : Category.{u} (ULift.{max u vI} I) := uliftCategory I
  let : Category.{max u wI}
      (ULiftHom.{max u wI} (ULift.{max u vI} I)) := ULiftHom.category
  let E : I ≌ ULiftHom.{max u wI} (ULift.{max u vI} I) :=
    ULiftHomULiftCategory.equiv I
  let D' := E.inverse ⋙ D
  let c' := c.whisker E.inverse
  have hc' : IsLimit ((BigAffineFppf.toScheme B S hS).mapCone c') :=
    (hc.whiskerEquivalence E.symm).ofIsoLimit
      ((BigAffineFppf.toScheme B S hS).mapConeWhisker
        (c := c) (E := E.inverse)).symm
  obtain ⟨i', j, x', xU, δ, β, γ', hδ, hβ, hβiso, hγ', hcomm⟩ :=
    h _ D' c' hc' (E.functor.obj i) y x γ hγ
  exact ⟨E.inverse.obj i', E.inverse.map j, x', xU, δ, β, γ',
    hδ, hβ, hβiso, hγ', hcomm⟩

private theorem etale_chart_of_open_immersion
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : BigFppfOver B S hS} (g : X ⟶ Y)
    [IsOpenImmersion ((BigFppfOver.toScheme B S hS).map g)]
    (U V : BigFppfOver B S hS)
    (a : yoneda.obj U ⟶ yoneda.obj X) (b : yoneda.obj V ⟶ yoneda.obj Y)
    (h : U ⟶ V)
    (ha : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a)
    (hb : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf b)
    (hh : yoneda.map h ≫ b = a ≫ yoneda.map g) :
    Etale ((BigFppfOver.toScheme B S hS).map h) := by
  obtain ⟨a, rfl⟩ := yoneda.map_surjective a
  obtain ⟨b, rfl⟩ := yoneda.map_surjective b
  have ha' : Etale ((BigFppfOver.toScheme B S hS).map a) :=
    MorphismProperty.of_relative_map (P := (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))) ha
  have hb' : Etale ((BigFppfOver.toScheme B S hS).map b) :=
    MorphismProperty.of_relative_map (P := (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))) hb
  have hh' : h ≫ b = a ≫ g := yoneda.map_injective (by simpa using hh)
  have : Etale ((BigFppfOver.toScheme B S hS).map h ≫
      (BigFppfOver.toScheme B S hS).map b) := by
    rw [← Functor.map_comp, hh', Functor.map_comp]
    infer_instance
  exact Etale.of_comp ((BigFppfOver.toScheme B S hS).map h)
    ((BigFppfOver.toScheme B S hS).map b)

private theorem fppfCovering_yoneda_of_open_cover
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (U : BigFppfOver B S hS)
    (I : Type u) (V : I → BigFppfOver B S hS) (g : ∀ i, V i ⟶ U)
    (hopen : ∀ i, IsOpenImmersion (B.inclusion.map (g i).left))
    (hcover : ∀ x : U.left.1, ∃ i, ∃ z : (V i).left.1, (g i).left.hom z = x) :
    Space.Topology.fppf.IsCovering B S hS
      (fun i => yoneda.obj (V i)) (fun i => yoneda.map (g i)) := by
  refine ⟨isAlgebraicSpace_yoneda B S hS U,
    fun i => isAlgebraicSpace_yoneda B S hS (V i), ?_⟩
  refine ⟨isAlgebraicSpace_yoneda B S hS U,
    fun i => isAlgebraicSpace_yoneda B S hS (V i), ?_, ?_, ?_⟩
  rotate_left 2
  · apply Set.eq_univ_of_forall
    intro x
    refine Quot.inductionOn x ?_
    intro p
    let t : Spec (.of p.carrier) := Classical.choice inferInstance
    obtain ⟨i, z, hz⟩ := hcover (p.value.left.hom t)
    have : IsOpenImmersion (g i).left.hom := hopen i
    have : Subsingleton (Spec (.of p.carrier)) :=
      inferInstanceAs (Subsingleton (PrimeSpectrum p.carrier))
    have hr : Set.range p.value.left.hom ⊆ Set.range (g i).left.hom := by
      rintro _ ⟨q, rfl⟩
      have hqt : q = t := @Subsingleton.elim (Spec (.of p.carrier)) inferInstance q t
      exact ⟨z, by simpa [hqt] using hz⟩
    let l := IsOpenImmersion.lift (g i).left.hom p.value.left.hom hr
    have hl : l ≫ (g i).left.hom = p.value.left.hom :=
      IsOpenImmersion.lift_fac _ _ hr
    let q : p.siteObject ⟶ V i := Over.homMk (ObjectProperty.homMk l) (by
      apply B.inclusion.map_injective
      show l ≫ (V i).hom.hom = p.toBase
      calc
        l ≫ (V i).hom.hom = l ≫ ((g i).left.hom ≫ U.hom.hom) := by
          congr 1
          exact (congrArg (fun f => f.hom) (Over.w (g i))).symm
        _ = p.value.left.hom ≫ U.hom.hom := by rw [← Category.assoc, hl]
        _ = p.toBase := congrArg (fun f => f.hom) (Over.w p.value))
    have hq : q ≫ g i = p.value := Over.OverMorphism.ext (ObjectProperty.hom_ext _ hl)
    let p' : Space.FieldValuedPoint B S hS (yoneda.obj (V i)) :=
      { carrier := p.carrier
        contained := p.contained
        toBase := p.toBase
        value := q }
    refine Set.mem_iUnion.mpr ⟨i, p'.class B S hS _, ?_⟩
    show Quot.mk _ (Space.FieldValuedPoint.map B S hS _ (yoneda.map (g i)) p') =
      Quot.mk _ p
    apply congrArg (Quot.mk _)
    show (Space.FieldValuedPoint.mk p.carrier p.contained p.toBase (q ≫ g i)) = p
    rw [hq]
  all_goals
    intro i A C a b h ha hb hh
    have : IsOpenImmersion ((BigFppfOver.toScheme B S hS).map (g i)) := hopen i
    have := etale_chart_of_open_immersion B S hS (g i) A C a b h ha hb hh
    infer_instance

private theorem exists_affine_limit_presentation
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (U : BigFppfOver B S hS) (hU : IsAffine U.left.1)
    (V : Scheme.{u}) [IsAffine V] (hV : B.Contains V)
    (g : V ⟶ S) [LocallyOfFinitePresentation g]
    (k : U.left.1 ⟶ V) (hk : k ≫ g = B.inclusion.map U.hom) :
    ∃ (I : Type u) (_ : Category.{u} I) (_ : IsCofiltered I)
      (D : I ⥤ BigAffineFppf B S hS) (c : Cone D),
      Nonempty (IsLimit ((BigAffineFppf.toScheme B S hS).mapCone c)) ∧
      (∀ i, LocallyOfFinitePresentation (B.inclusion.map (D.obj i).obj.hom)) ∧
      c.pt = ⟨U, hU⟩ := by
  let := hU
  let R := Γ(V, ⊤)
  let A := Γ(U.left.1, ⊤)
  let : Algebra R A := k.appTop.hom.toAlgebra
  have hR : B.Contains (Spec (.of R)) := by
    show (Spec Γ(V, ⊤)).size < B.cutoff
    rw [← Scheme.size_congr V.isoSpec]
    exact hV
  have hA : B.Contains (Spec (.of A)) := by
    show (Spec Γ(U.left.1, ⊤)).size < B.cutoff
    rw [← Scheme.size_congr U.left.1.isoSpec]
    exact U.left.2
  let g' : Spec (.of R) ⟶ S := V.isoSpec.inv ≫ g
  let data := affinePresentationData R A
  let D := affinePresentation_siteDiagramOver B hR S hS g' data
  let c := affinePresentation_siteConeOver B hR S hS g' hA data
  let e₀ : U.left ≅ c.pt.obj.left := ObjectProperty.isoMk _ U.left.1.isoSpec
  have he₀ : e₀.hom ≫ c.pt.obj.hom = U.hom := by
    apply B.inclusion.map_injective
    rw [Functor.map_comp]
    show U.left.1.isoSpec.hom ≫ B.inclusion.map
      ((ObjectProperty.homMk (Scheme.Spec.map (CommRingCat.ofHom (algebraMap R A)).op) :
          B.obj hA ⟶ B.obj hR) ≫
        B.inclusion.preimage (X := B.obj hR) (Y := B.obj hS) g') = _
    rw [Functor.map_comp, Functor.map_preimage]
    show U.left.1.isoSpec.hom ≫ (Spec.map k.appTop ≫ (V.isoSpec.inv ≫ g)) = _
    rw [← Category.assoc, Scheme.isoSpec_hom_naturality, Category.assoc,
      Iso.hom_inv_id_assoc]
    exact hk
  let e₁ : U ≅ c.pt.obj := Over.isoMk e₀ he₀
  let e : (⟨U, hU⟩ : BigAffineFppf B S hS) ≅ c.pt := ObjectProperty.isoMk _ e₁
  refine ⟨data.Λᵒᵖ, inferInstance, inferInstance, D, c.extend e.hom, ?_, ?_, rfl⟩
  · exact ⟨(affinePresentation_siteConeOver_isLimit B hR S hS g' hA data).ofIsoLimit
      ((Cone.functoriality D (BigAffineFppf.toScheme B S hS)).mapIso
        (c.extendIso e.symm))⟩
  · intro i
    exact affinePresentation_stageOver_map_locallyOfFinitePresentation B hR S hS g' data i

private theorem represented_property_of_affine_chart
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (P : MorphismProperty (AlgebraicSpaces B S hS))
    [P.IsStableUnderBaseChange]
    [P.IsLocalAtTarget (Space.Topology.fppf.precoverage B S hS)]
    {𝒳 𝒴 : CatFiberedInGroupoids.{u, u, u + 1, u + 1}
      (BigFppfOver B S hS)}
    (f : 𝒳 ⟶ 𝒴)
    (hf : IsRepresentableByAlgebraicSpaces B S hS f.hom)
    (hlimit : BigFppfOver.IsLimitPreservingOnObjects.{u, u, u, u, u + 1}
      B S hS 𝒴 (terminalCFG B S hS)
      (Bicategory.InducedBicategory.mkHom
        (toTerminalCFG B S hS 𝒴)))
    (hlocal : ∀ (U : BigFppfOver B S hS),
      IsAffine U.left.1 →
      LocallyOfFinitePresentation (B.inclusion.map U.hom) →
      ∀ (y : BigFppfOver B U.left.1 U.left.2 ⥤ 𝒴.val.obj)
        (_hy : y ⋙ 𝒴.val.p = Over.map U.hom)
        (F : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u)
        (hF : IsAlgebraicSpace B U.left.1 U.left.2 F),
        Nonempty (StacksRepresentableCFG.EquivalenceOver
          (TwoFibreProductOver.fst (Over.map U.hom) 𝒳.val.p 𝒴.val.p y
            (CatFiberedInGroupoids.homFunctor f))
          (presheafOfCategories (F ⋙ typeToCat)).p) →
        P (algebraicSpaceMap B S hS U
          ((spacesOverSmallerBaseFunctor
            B U.left.1 S U.left.2 hS U.hom).obj ⟨F, hF⟩)))
    (U : BigFppfOver B S hS) (hU : IsAffine U.left.1)
    (V : Scheme.{u}) [IsAffine V] (hV : B.Contains V)
    (g : V ⟶ S) [LocallyOfFinitePresentation g]
    (k : U.left.1 ⟶ V) (hk : k ≫ g = B.inclusion.map U.hom)
    (y : BigFppfOver B U.left.1 U.left.2 ⥤ 𝒴.val.obj)
    (hy : y ⋙ 𝒴.val.p = Over.map U.hom)
    (F : AlgebraicSpaces B U.left.1 U.left.2)
    (eF : StacksRepresentableCFG.EquivalenceOver
      (TwoFibreProductOver.fst (Over.map U.hom) 𝒳.val.p 𝒴.val.p y
        (CatFiberedInGroupoids.homFunctor f)) (PresheafOfCategories.discreteProjection F.obj)) :
    P (algebraicSpaceMap B S hS U
      ((spacesOverSmallerBaseFunctor
        B U.left.1 S U.left.2 hS U.hom).obj F)) := by
  obtain ⟨I, hI, hcof, D, c, ⟨hc⟩, hfp, hpt⟩ :=
    exists_affine_limit_presentation B S hS U hU V hV g k hk
  let := hI
  let := hcof
  have hpt' : (BigAffineFppf.inclusion B S hS).obj c.pt = U :=
    congrArg (BigAffineFppf.inclusion B S hS).obj hpt
  subst U
  obtain ⟨i, x, a, ha⟩ := exists_sectionIso_of_limitPreserving_smallerBase
    B S hS 𝒴 hlimit I D c hc y hy
  exact represented_property_of_affine_stage B S hS P f hf hlocal
    ((BigAffineFppf.inclusion B S hS).map (c.π.app i))
    (D.obj i).property (hfp i) (sectionFromFiberObject B S hS 𝒴 _ x)
    (sectionFromFiberObject_comp B S hS 𝒴 _ x) y a ha F eF

-- The affine refinement of the chart cover is indexed by a dependent pair, which unification
-- sees only after unfolding the two layers of `bind`.
attribute [local implicit_reducible] PreZeroHypercover.bind
  Precoverage.ZeroHypercover.bind PreZeroHypercover.pullback₁
  Precoverage.ZeroHypercover.pullback₁ in
/-- A base-change-stable, fppf-local property of a representable morphism can
be checked on affine bases locally of finite presentation when the target is
limit preserving on objects. -/
@[stacks 07WI]
public theorem hasRelativeProperty_of_affine_locallyOfFinitePresentation
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (P : MorphismProperty (AlgebraicSpaces B S hS))
    [P.IsStableUnderBaseChange]
    [P.IsLocalAtTarget (Space.Topology.fppf.precoverage.{u, u} B S hS)]
    {𝒳 𝒴 : CatFiberedInGroupoids.{u, u, u + 1, u + 1}
      (BigFppfOver B S hS)}
    (f : 𝒳 ⟶ 𝒴)
    (hf : IsRepresentableByAlgebraicSpaces B S hS f.hom)
    (hlimit : BigFppfOver.IsLimitPreservingOnObjects.{u, max u vI, max u wI, u, u + 1}
      B S hS 𝒴 (terminalCFG B S hS)
      (Bicategory.InducedBicategory.mkHom
        (toTerminalCFG B S hS 𝒴)))
    (hlocal : ∀ (U : BigFppfOver B S hS),
      IsAffine U.left.1 →
      LocallyOfFinitePresentation (B.inclusion.map U.hom) →
      ∀ (y : BigFppfOver B U.left.1 U.left.2 ⥤ 𝒴.val.obj)
        (_hy : y ⋙ 𝒴.val.p = Over.map U.hom)
        (F : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u)
        (hF : IsAlgebraicSpace B U.left.1 U.left.2 F),
        Nonempty (StacksRepresentableCFG.EquivalenceOver
          (TwoFibreProductOver.fst (Over.map U.hom) 𝒳.val.p 𝒴.val.p y
            (CatFiberedInGroupoids.homFunctor f))
          (presheafOfCategories (F ⋙ typeToCat)).p) →
        P (algebraicSpaceMap B S hS U
          ((spacesOverSmallerBaseFunctor
            B U.left.1 S U.left.2 hS U.hom).obj ⟨F, hF⟩))) :
    HasRelativeProperty B S hS P f hf := by
  classical
  intro U y hy F hF ⟨eF⟩
  let p : U.left.1 ⟶ S := B.inclusion.map U.hom
  let C := S.affineCover.pullback₁ p
  let W := C.bind fun i => (C.X i).affineCover
  let hW (i : W.I₀) : B.Contains (W.X i) :=
    Scheme.size_lt_of_isOpenImmersion (W.f i) U.left.2
  let V (i : W.I₀) : BigFppfOver B S hS :=
    Over.mk (ObjectProperty.homMk (W.f i ≫ p) : B.obj (hW i) ⟶ B.obj hS)
  let g (i : W.I₀) : V i ⟶ U :=
    Over.homMk (ObjectProperty.homMk (W.f i)) rfl
  apply algebraicSpaceMap_property_of_cover B S hS P f U y hy ⟨F, hF⟩ eF
    W.I₀ V g
  · apply fppfCovering_yoneda_of_open_cover B S hS U W.I₀ V g
    · intro i
      exact inferInstanceAs (IsOpenImmersion (W.f i))
    · exact Scheme.Cover.exists_eq W
  · rintro ⟨i, j⟩
    let yV := Over.map (g ⟨i, j⟩).left ⋙ y
    have hyV : yV ⋙ 𝒴.val.p = Over.map (V ⟨i, j⟩).hom := by
      rw [Functor.assoc, hy, ← Over.mapComp_eq, Over.w (g ⟨i, j⟩)]
    obtain ⟨G, hG, ⟨eG⟩⟩ := hf (V ⟨i, j⟩) yV hyV
    refine ⟨⟨G, hG⟩, ⟨eG⟩, ?_⟩
    let k : (V ⟨i, j⟩).left.1 ⟶ S.affineCover.X i :=
      (C.X i).affineCover.f j ≫ S.affineCover.pullbackHom p i
    have hk : k ≫ S.affineCover.f i = B.inclusion.map (V ⟨i, j⟩).hom :=
      calc k ≫ S.affineCover.f i
          = (C.X i).affineCover.f j ≫
              S.affineCover.pullbackHom p i ≫ S.affineCover.f i := Category.assoc _ _ _
        _ = (C.X i).affineCover.f j ≫ C.f i ≫ p :=
              congrArg (fun m => (C.X i).affineCover.f j ≫ m)
                (pullback.condition : C.f i ≫ p =
                  S.affineCover.pullbackHom p i ≫ S.affineCover.f i).symm
        _ = ((C.X i).affineCover.f j ≫ C.f i) ≫ p := (Category.assoc _ _ _).symm
        _ = B.inclusion.map (V ⟨i, j⟩).hom := rfl
    exact represented_property_of_affine_chart B S hS P f hf
      (limitPreserving_small B S hS 𝒴 hlimit) hlocal (V ⟨i, j⟩)
      (inferInstanceAs (IsAffine ((C.X i).affineCover.X j)))
      (S.affineCover.X i)
      (Scheme.size_lt_of_isOpenImmersion (S.affineCover.f i) hS)
      (S.affineCover.f i) k hk yV hyV ⟨G, hG⟩ eG


end AlgebraicGeometry.Stack

end
