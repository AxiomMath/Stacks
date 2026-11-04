module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.AlgebraicStackEquivalenceInvariance
public import StacksFrontier.AlgebraicGeometry.Stacks.ChangeOfBaseAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.DiagonalCriteriaSchemePoints
public import StacksFrontier.AlgebraicGeometry.Stacks.SchemeStack
public import StacksFrontier.AlgebraicGeometry.Stacks.TwoFibreProductUniversalProperty
public import StacksFrontier.CategoryTheory.Sites.Stack.Functoriality.PullbackAdjunction
public import StacksFrontier.CategoryTheory.TwoFibreProduct.OverBase
public import StacksFrontier.CategoryTheory.Comma.SliceRebase
public import StacksFrontier.CategoryTheory.TwoFibreProduct.OverIso

/-!
# Change of base scheme for an algebraic stack (Stacks 04X7)

Let `g : S ⟶ S'` be a morphism of a big fppf site and let `𝒳'` be a category over the big fppf
site of `S'`. Its *change of base* to `S` is the strict pullback of its structure functor along
the relocalization functor `CategoryTheory.Over.map g`: an object is an object `U` of the big
fppf site of `S` together with an object of `𝒳'` lying over `U` viewed over `S'`.
**Stacks 04X7** is the definition of this construction *as an algebraic stack*, so its content is
that the change of base of an algebraic stack over `S'` is an algebraic stack over `S`, and that
Construction A of Stacks, Section 04WT carries it to the 2-fibre product `𝒳' ×_{S'} S` over `S'`.

## Main definitions

* `AlgebraicGeometry.Stack.baseChange`: **Stacks 04X7**, the change of base of a category over
  the big fppf site of `S'` to the big fppf site of `S`.
* `AlgebraicGeometry.Stack.baseChangeProduct`: the 2-fibre product of `𝒳'` and the stack
  represented by `S` over the stack represented by `S'`.
* `AlgebraicGeometry.Stack.baseChangeProductEquivalence`: the identification of the image of the
  change of base under Construction A with that 2-fibre product.

## Main results

* `AlgebraicGeometry.Stack.isAlgebraicStack_changeBase_baseChange`: the image of the change of
  base under Construction A is an algebraic stack over `S'`, being the 2-fibre product
  `𝒳' ×_{S'} S`.
* `AlgebraicGeometry.Stack.isAlgebraicStack_baseChange`: **Stacks 04X7**, the change of base of
  an algebraic stack over `S'` is an algebraic stack over `S`.

## Implementation notes

The source phrases Stacks 04X7 through the correspondence of Stacks 04X5 between algebraic stacks
over `S` and algebraic stacks over `S'` carrying a 1-morphism to the stack represented by `S`,
and defines the change of base as the object of the left-hand side matching `𝒳' ×_{S'} S`. This
library has no 2-categorical equivalence of algebraic stacks, so the statement is given
unbundled: the change of base is constructed directly, the identification of its image under
Construction A (`AlgebraicGeometry.Stack.changeBase`) with the 2-fibre product is
`AlgebraicGeometry.Stack.baseChangeProductEquivalence`, and the algebraicity of the change of
base is read back through `AlgebraicGeometry.Stack.isAlgebraicStack_of_changeBase`, the direction
of Stacks 04X5 that this library proves. Nothing of the source's content is lost: the bundled
equivalence's object map is `changeBase`, and the two conditions it would impose on the image —
that it is an algebraic stack and that its structural 1-morphism to the stack represented by `S`
is the second projection of the 2-fibre product — are
`AlgebraicGeometry.Stack.isAlgebraicStack_changeBase_baseChange` and
`AlgebraicGeometry.Stack.baseChangeSnd`, which is the second projection of
`AlgebraicGeometry.Stack.baseChangeProductEquivalence` by construction.

The stack represented by `S` over `S'` is `schemeFibredCategory B S' hS' (Over.mk g)`, whose total
category is the slice at `S/S'`, while the change of base is built from the big fppf site of `S`
itself; the two are identified by `CategoryTheory.Over.iteratedSliceEquiv`. Only one of its two
structural equations is an equality of functors on the nose
(`CategoryTheory.Over.iteratedSliceBackward_forget`); the other is
`CategoryTheory.Over.iteratedSliceForward_comp_map`, and the comparison in the opposite direction
is not an equality of functors at all, which is why
`AlgebraicGeometry.Stack.baseChangeProductEquivalence` has one strict composite and one genuine
natural isomorphism, the unit of `CategoryTheory.Over.iteratedSliceEquiv`.

## References

* [Stacks Project, Tag 04X5](https://stacks.math.columbia.edu/tag/04X5)
* [Stacks Project, Tag 04X7](https://stacks.math.columbia.edu/tag/04X7)
* [Stacks Project, Tag 04TF](https://stacks.math.columbia.edu/tag/04TF)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Functor

/-- **The image of an `eqToHom` under a functor is vertical.** For any two functors `F` and `p`
and any equality of objects of the source of `F`, the image of its `eqToHom` under `F` lies over
the identity of its image under `p`: after substituting the equality it is an identity. -/
theorem isHomLift_map_eqToHom {C : Type*} [Category C] {D : Type*} [Category D]
    {E : Type*} [Category E] (F : C ⥤ D) (p : D ⥤ E) {a b : C} (h : a = b) {U : E}
    (hU : p.obj (F.obj a) = U) : p.IsHomLift (𝟙 U) (F.map (eqToHom h)) := by
  subst h
  refine CategoryTheory.IsHomLift.of_fac' p (𝟙 U) _ hU hU ?_
  simp

/-- **A composite of vertical morphisms is vertical.** The two identities they lie over are
identities of the same object, since the middle object lies over both. -/
theorem isHomLift_comp_id {D : Type*} [Category D] {E : Type*} [Category E] {p : D ⥤ E}
    {U U' : E} {a b c : D} {φ : a ⟶ b} {ψ : b ⟶ c}
    (hφ : p.IsHomLift (𝟙 U) φ) (hψ : p.IsHomLift (𝟙 U') ψ) : p.IsHomLift (𝟙 U) (φ ≫ ψ) := by
  have := hφ
  have := hψ
  have hb : p.obj b = U := CategoryTheory.IsHomLift.codomain_eq p (𝟙 U) φ
  have hb' : p.obj b = U' := CategoryTheory.IsHomLift.domain_eq p (𝟙 U') ψ
  refine CategoryTheory.IsHomLift.of_fac' p (𝟙 U) (φ ≫ ψ)
    (CategoryTheory.IsHomLift.domain_eq p (𝟙 U) φ)
    ((CategoryTheory.IsHomLift.codomain_eq p (𝟙 U') ψ).trans (hb'.symm.trans hb)) ?_
  rw [p.map_comp, CategoryTheory.IsHomLift.fac' p (𝟙 U) φ,
    CategoryTheory.IsHomLift.fac' p (𝟙 U') ψ]
  simp

/-- **Over a faithful structure functor a vertical morphism is determined by its source and
target.** Two morphisms of the total category which lie over identities are equal, because a
faithful functor reflects the `eqToHom` composite that `CategoryTheory.IsHomLift.fac'` pins each
of them down to; the two identities need not be identities of the same object, since the common
source already forces that. -/
theorem eq_of_isHomLift_id {D : Type*} [Category D] {E : Type*} [Category E] (p : D ⥤ E)
    [p.Faithful] {U U' : E} {a b : D} {φ ψ : a ⟶ b}
    (hφ : p.IsHomLift (𝟙 U) φ) (hψ : p.IsHomLift (𝟙 U') ψ) : φ = ψ := by
  have := hφ
  have := hψ
  refine p.map_injective ?_
  rw [CategoryTheory.IsHomLift.fac' p (𝟙 U) φ, CategoryTheory.IsHomLift.fac' p (𝟙 U') ψ]
  simp

end CategoryTheory.Functor

namespace CategoryTheory.Over

/-- **A morphism of a twice-iterated slice whose underlying morphism of the ambient category is
an `eqToHom` is vertical for the forgetful functor of the first slice.** Its source and target
then have the same image in `𝒞/X`, by `CategoryTheory.Over.obj_ext`, and the morphism itself is
the `eqToHom` of that identification. -/
theorem isHomLift_of_left_left_eq_eqToHom {C : Type*} [Category C] {X : C} (f : Over X)
    {a b : Over f} (m : a ⟶ b) (hL : a.left.left = b.left.left)
    (hm : m.left.left = eqToHom hL) {U : Over X} (hU : b.left = U) :
    (Over.forget f).IsHomLift (𝟙 U) m := by
  subst hU
  have hab : a.left = b.left := Over.obj_ext hL (by rw [← Over.w m.left, hm])
  refine CategoryTheory.IsHomLift.of_fac' _ _ _ hab rfl ?_
  refine Over.OverMorphism.ext ?_
  rw [Category.id_comp, eqToHom_trans, Over.forget_map, hm, Over.eqToHom_left]

/-- **The unit of the iterated-slice equivalence is vertical.** Its component at an object `y` of
`𝒞/f` is an isomorphism whose underlying morphism of `𝒞` is the identity. -/
theorem isHomLift_iteratedSliceEquiv_unitIso_inv_app {C : Type*} [Category C] {X : C}
    (f : Over X) (y : Over f) {U : Over X} (hU : y.left = U) :
    (Over.forget f).IsHomLift (𝟙 U) ((Over.iteratedSliceEquiv f).unitIso.inv.app y) :=
  Over.isHomLift_of_left_left_eq_eqToHom f
    ((Over.iteratedSliceEquiv f).unitIso.inv.app y) rfl rfl hU

end CategoryTheory.Over

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S S' : Scheme.{u}) (hS : B.Contains S) (hS' : B.Contains S')
  (g : B.obj hS ⟶ B.obj hS')

/-- **The structural 1-morphism to the stack represented by the base.** Every category over the
big fppf site of `S'` maps to the category represented by the terminal object `S'/S'`, by its own
structure functor read through the iterated-slice identification of the slice at `S'/S'` with the
big fppf site of `S'`. -/
def toTerminalStack (𝒴 : BasedCategory.{u, u + 1} (BigFppfOver B S' hS')) :
    𝒴 ⥤ᵇ (schemeFibredCategory B S' hS' (Over.mk (𝟙 (B.obj hS')))).val where
  toFunctor := 𝒴.p ⋙ Over.iteratedSliceBackward (Over.mk (𝟙 (B.obj hS')))
  w := by
    change 𝒴.p ⋙ Over.map (𝟙 (B.obj hS')) = 𝒴.p
    rw [Over.mapId_eq, Functor.comp_id]

variable (𝒳' : BasedCategory.{u, u + 1} (BigFppfOver B S' hS'))

/-- **Stacks 04X7, the construction.** The *change of base* of a category `𝒳'` over the big fppf
site of `S'` along `g : S ⟶ S'`: the strict pullback of its structure functor along the
relocalization functor of `g`, as a category over the big fppf site of `S`. An object is an object
`U` of the big fppf site of `S` together with an object of `𝒳'` lying over `U/S'`, and the
structure functor is the first projection. -/
@[stacks 04X7 "the construction"]
def baseChange : BasedCategory.{u, u + 1} (BigFppfOver B S hS) :=
  BasedCategory.ofFunctor (StrictPullback.structureFunctor (Over.map g) 𝒳'.p)

/-- The first projection of the change of base: a 1-morphism to `𝒳'` over the big fppf site of
`S'`, defined on the image of the change of base under Construction A. -/
def baseChangeFst : changeBase B S S' hS hS' g (baseChange B S S' hS hS' g 𝒳') ⥤ᵇ 𝒳' where
  toFunctor := StrictPullback.pr (Over.map g) 𝒳'.p
  w := StrictPullback.pr_comp_eq _ _

/-- The second projection of the change of base: the 1-morphism to the stack represented by `S`
over `S'` which the correspondence of Stacks 04X5 attaches to the change of base. It is the
structure functor of the change of base, read through the iterated-slice identification. -/
def baseChangeSnd : changeBase B S S' hS hS' g (baseChange B S S' hS hS' g 𝒳') ⥤ᵇ
    (schemeFibredCategory B S' hS' (Over.mk g)).val where
  toFunctor := StrictPullback.structureFunctor (Over.map g) 𝒳'.p ⋙
    Over.iteratedSliceBackward (Over.mk g)
  w := rfl

/-- The 2-fibre product `𝒳' ×_{S'} S` of `𝒳'` and the stack represented by `S` over the stack
represented by `S'`, as a category over the big fppf site of `S'`. -/
abbrev baseChangeProduct : BasedCategory.{u, u + 1} (BigFppfOver B S' hS') :=
  BasedCategory.ofFunctor (TwoFibreProductOver.structureFunctor 𝒳'.p
    (schemeFibredCategory B S' hS' (Over.mk g)).val.p
    (schemeFibredCategory B S' hS' (Over.mk (𝟙 (B.obj hS')))).val.p
    (toTerminalStack B S' hS' 𝒳').toFunctor
    (toTerminalStack B S' hS' (schemeFibredCategory B S' hS' (Over.mk g)).val).toFunctor)

/-- The 2-cell filling the square of the two projections of the change of base over the stack
represented by `S'`: at an object of the change of base it is the identification, over `S'/S'`, of
the image of its object of `𝒳'` with the relocalization of its object of the big fppf site of
`S`. That identification is the defining equation of the strict pullback. -/
def baseChangeComparison :
    (baseChangeFst B S S' hS hS' g 𝒳').toFunctor ⋙ (toTerminalStack B S' hS' 𝒳').toFunctor ≅
      (baseChangeSnd B S S' hS hS' g 𝒳').toFunctor ⋙
        (toTerminalStack B S' hS'
          (schemeFibredCategory B S' hS' (Over.mk g)).val).toFunctor :=
  NatIso.ofComponents
    (fun X => (Over.iteratedSliceBackward (Over.mk (𝟙 (B.obj hS')))).mapIso (eqToIso X.over))
    (fun {X Y} φ => by
      have h : 𝒳'.p.map φ.fib ≫ eqToHom Y.over
          = eqToHom X.over ≫ (Over.map g).map φ.base := by
        rw [φ.over]; simp
      change (Over.iteratedSliceBackward (Over.mk (𝟙 (B.obj hS')))).map (𝒳'.p.map φ.fib) ≫
            (Over.iteratedSliceBackward (Over.mk (𝟙 (B.obj hS')))).map (eqToHom Y.over)
          = (Over.iteratedSliceBackward (Over.mk (𝟙 (B.obj hS')))).map (eqToHom X.over) ≫
            (Over.iteratedSliceBackward (Over.mk (𝟙 (B.obj hS')))).map
              ((Over.map g).map φ.base)
      rw [← Functor.map_comp, ← Functor.map_comp, h])

/-- The component of the comparison 2-cell at an object of the change of base is the image under
the iterated-slice identification of the `eqToHom` of the defining equation of that object. -/
@[simp]
theorem baseChangeComparison_hom_app
    (X : (changeBase B S S' hS hS' g (baseChange B S S' hS hS' g 𝒳')).obj) :
    (baseChangeComparison B S S' hS hS' g 𝒳').hom.app X =
      (Over.iteratedSliceBackward (Over.mk (𝟙 (B.obj hS')))).map (eqToHom X.over) :=
  rfl

/-- Every component of the comparison 2-cell is vertical over the big fppf site of `S'`: it is
the image under a functor of an `eqToHom`. -/
theorem baseChangeComparison_vertical
    (X : (changeBase B S S' hS hS' g (baseChange B S S' hS hS' g 𝒳')).obj) :
    (schemeFibredCategory B S' hS' (Over.mk (𝟙 (B.obj hS')))).val.p.IsHomLift
      (𝟙 ((changeBase B S S' hS hS' g (baseChange B S S' hS hS' g 𝒳')).p.obj X))
      ((baseChangeComparison B S S' hS hS' g 𝒳').hom.app X) :=
  Functor.isHomLift_map_eqToHom (Over.iteratedSliceBackward (Over.mk (𝟙 (B.obj hS'))))
    (schemeFibredCategory B S' hS' (Over.mk (𝟙 (B.obj hS')))).val.p X.over
    ((Functor.congr_obj (Over.mapId_eq (B.obj hS')) (𝒳'.p.obj X.fib)).trans X.over)

/-- The 1-morphism from the image of the change of base under Construction A to the 2-fibre
product `𝒳' ×_{S'} S`, given by the two projections and the comparison 2-cell. -/
def toBaseChangeProduct : changeBase B S S' hS hS' g (baseChange B S S' hS hS' g 𝒳') ⥤ᵇ
    baseChangeProduct B S S' hS hS' g 𝒳' where
  toFunctor := TwoFibreProductOver.lift _ _ _ _ _
    (changeBase B S S' hS hS' g (baseChange B S S' hS hS' g 𝒳')).p
    (baseChangeFst B S S' hS hS' g 𝒳').toFunctor (baseChangeSnd B S S' hS hS' g 𝒳').toFunctor
    (baseChangeFst B S S' hS hS' g 𝒳').w (baseChangeSnd B S S' hS hS' g 𝒳').w
    (baseChangeComparison B S S' hS hS' g 𝒳')
    (baseChangeComparison_vertical B S S' hS hS' g 𝒳')
  w := TwoFibreProductOver.lift_comp_structureFunctor ..

/-- The 1-morphism from the 2-fibre product `𝒳' ×_{S'} S` back to the image of the change of base
under Construction A: an object of the 2-fibre product has an object of `𝒳'` and an object of the
slice at `S/S'`, and the comparison 2-cell being vertical makes the pair a point of the strict
pullback. -/
def ofBaseChangeProduct : baseChangeProduct B S S' hS hS' g 𝒳' ⥤ᵇ
    changeBase B S S' hS hS' g (baseChange B S S' hS hS' g 𝒳') where
  toFunctor := StrictPullback.liftFib
    (TwoFibreProductOver.snd 𝒳'.p (schemeFibredCategory B S' hS' (Over.mk g)).val.p
        (schemeFibredCategory B S' hS' (Over.mk (𝟙 (B.obj hS')))).val.p _ _ ⋙
      Over.iteratedSliceForward (Over.mk g))
    (TwoFibreProductOver.fst 𝒳'.p (schemeFibredCategory B S' hS' (Over.mk g)).val.p
      (schemeFibredCategory B S' hS' (Over.mk (𝟙 (B.obj hS')))).val.p _ _)
    ((TwoFibreProductOver.fst_comp_eq ..).trans
      ((Functor.assoc _ _ _).trans
        ((congrArg (fun F => TwoFibreProductOver.snd 𝒳'.p
              (schemeFibredCategory B S' hS' (Over.mk g)).val.p
              (schemeFibredCategory B S' hS' (Over.mk (𝟙 (B.obj hS')))).val.p _ _ ⋙ F)
            (Over.iteratedSliceForward_comp_map (Over.mk g))).trans
          (TwoFibreProductOver.snd_comp_eq ..))).symm)
  w := (Functor.assoc _ _ _).symm.trans
    ((congrArg (fun F => F ⋙ Over.map g)
        (StrictPullback.liftFib_comp_structureFunctor _ _ _)).trans
      ((Functor.assoc _ _ _).trans
        ((congrArg (fun F => TwoFibreProductOver.snd 𝒳'.p
              (schemeFibredCategory B S' hS' (Over.mk g)).val.p
              (schemeFibredCategory B S' hS' (Over.mk (𝟙 (B.obj hS')))).val.p _ _ ⋙ F)
            (Over.iteratedSliceForward_comp_map (Over.mk g))).trans
          (TwoFibreProductOver.snd_comp_eq ..))))

/-- Going to the 2-fibre product and back is the identity on the nose: both projections and the
defining equation of the strict pullback are returned unchanged. -/
theorem toBaseChangeProduct_comp_ofBaseChangeProduct :
    (toBaseChangeProduct B S S' hS hS' g 𝒳').comp (ofBaseChangeProduct B S S' hS hS' g 𝒳') =
      BasedFunctor.id _ :=
  rfl


/-- Going from the 2-fibre product to the change of base and back is isomorphic to the identity:
the object of `𝒳'` and the comparison 2-cell are returned unchanged, and the object of the slice
at `S/S'` is returned up to the unit of `CategoryTheory.Over.iteratedSliceEquiv`. -/
noncomputable def ofBaseChangeProductCompIso :
    (ofBaseChangeProduct B S S' hS hS' g 𝒳').comp (toBaseChangeProduct B S S' hS hS' g 𝒳') ≅
      BasedFunctor.id (baseChangeProduct B S S' hS hS' g 𝒳') := by
  have hfaith : (schemeFibredCategory B S' hS' (Over.mk (𝟙 (B.obj hS')))).val.p.Faithful :=
    inferInstanceAs (Over.forget (Over.mk (𝟙 (B.obj hS')))).Faithful
  refine BasedNatIso.mkNatIso (TwoFibreProductOver.liftIso
    (pW := (baseChangeProduct B S S' hS hS' g 𝒳').p)
    (H := TwoFibreProductOver.fst 𝒳'.p (schemeFibredCategory B S' hS' (Over.mk g)).val.p
      (schemeFibredCategory B S' hS' (Over.mk (𝟙 (B.obj hS')))).val.p
      (toTerminalStack B S' hS' 𝒳').toFunctor
      (toTerminalStack B S' hS' (schemeFibredCategory B S' hS' (Over.mk g)).val).toFunctor)
    (K := TwoFibreProductOver.snd 𝒳'.p (schemeFibredCategory B S' hS' (Over.mk g)).val.p
      (schemeFibredCategory B S' hS' (Over.mk (𝟙 (B.obj hS')))).val.p
      (toTerminalStack B S' hS' 𝒳').toFunctor
      (toTerminalStack B S' hS' (schemeFibredCategory B S' hS' (Over.mk g)).val).toFunctor)
    (t := TwoFibreProductOver.psiIso 𝒳'.p (schemeFibredCategory B S' hS' (Over.mk g)).val.p
      (schemeFibredCategory B S' hS' (Over.mk (𝟙 (B.obj hS')))).val.p
      (toTerminalStack B S' hS' 𝒳').toFunctor
      (toTerminalStack B S' hS' (schemeFibredCategory B S' hS' (Over.mk g)).val).toFunctor)
    ((ofBaseChangeProduct B S S' hS hS' g 𝒳').toFunctor ⋙
      (toBaseChangeProduct B S S' hS hS' g 𝒳').toFunctor)
    (Iso.refl _)
    (Functor.isoWhiskerLeft
      (TwoFibreProductOver.snd 𝒳'.p (schemeFibredCategory B S' hS' (Over.mk g)).val.p
        (schemeFibredCategory B S' hS' (Over.mk (𝟙 (B.obj hS')))).val.p
        (toTerminalStack B S' hS' 𝒳').toFunctor
        (toTerminalStack B S' hS' (schemeFibredCategory B S' hS' (Over.mk g)).val).toFunctor)
      (Over.iteratedSliceEquiv (Over.mk g)).unitIso.symm)
    (fun P => CategoryTheory.IsHomLift.id P.hx)
    (fun P => Over.isHomLift_iteratedSliceEquiv_unitIso_inv_app (Over.mk g) P.y P.hy)
    ?_ (TwoFibreProductOver.fst_comp_eq ..) (TwoFibreProductOver.snd_comp_eq ..)
    (fun P => TwoFibreProductOver.psiIso_hom_vertical P)) ?_
  · ext P
    have hFid : (schemeFibredCategory B S' hS' (Over.mk (𝟙 (B.obj hS')))).val.p.IsHomLift
        (𝟙 P.base) ((toTerminalStack B S' hS' 𝒳').toFunctor.map (𝟙 P.x)) :=
      Functor.isHomLift_map_eqToHom (toTerminalStack B S' hS' 𝒳').toFunctor
        (schemeFibredCategory B S' hS' (Over.mk (𝟙 (B.obj hS')))).val.p (rfl : P.x = P.x)
        ((Functor.congr_obj (toTerminalStack B S' hS' 𝒳').w P.x).trans P.hx)
    have hunit : (schemeFibredCategory B S' hS' (Over.mk g)).val.p.IsHomLift (𝟙 P.base)
        ((Over.iteratedSliceEquiv (Over.mk g)).unitIso.inv.app P.y) :=
      Over.isHomLift_iteratedSliceEquiv_unitIso_inv_app (Over.mk g) P.y P.hy
    refine Functor.eq_of_isHomLift_id
      (schemeFibredCategory B S' hS' (Over.mk (𝟙 (B.obj hS')))).val.p
      (Functor.isHomLift_comp_id hFid P.vertical)
      (Functor.isHomLift_comp_id
        (TwoFibreProductOver.psiIso_hom_vertical
          (((ofBaseChangeProduct B S S' hS hS' g 𝒳').toFunctor ⋙
            (toBaseChangeProduct B S S' hS hS' g 𝒳').toFunctor).obj P))
        (Functor.isHomLift_map_of_comp_eq
          (toTerminalStack B S' hS' (schemeFibredCategory B S' hS' (Over.mk g)).val).w
          (𝟙 P.base) ((Over.iteratedSliceEquiv (Over.mk g)).unitIso.inv.app P.y)))
  · intro P
    exact TwoFibreProductOver.structureFunctor_isHomLift _ (𝟙 _)
      (CategoryTheory.IsHomLift.id P.hx)

/-- **The image of the change of base under Construction A is the 2-fibre product
`𝒳' ×_{S'} S`.** The identification is strict in one composite: an object of the strict pullback
is carried to the triple consisting of its object of `𝒳'`, its object of the big fppf site of `S`
read in the slice at `S/S'`, and the defining equation of the strict pullback as the comparison
2-cell, and recovering the strict pullback from that triple returns it unchanged. In the other
composite the object of the slice at `S/S'` is only recovered up to the unit of
`CategoryTheory.Over.iteratedSliceEquiv`. -/
@[stacks 04X7 "the change of base is the two-fibre product over the base"]
noncomputable def baseChangeProductEquivalence :
    BasedCategory.Equivalence (changeBase B S S' hS hS' g (baseChange B S S' hS hS' g 𝒳'))
      (baseChangeProduct B S S' hS hS' g 𝒳') where
  functor := toBaseChangeProduct B S S' hS hS' g 𝒳'
  inverse := ofBaseChangeProduct B S S' hS hS' g 𝒳'
  unitIso := Iso.refl _
  counitIso := ofBaseChangeProductCompIso B S S' hS hS' g 𝒳'

/-- **The image of the change of base under Construction A is an algebraic stack over `S'`.** It
is the 2-fibre product of `𝒳'` and the stack represented by `S` over the stack represented by
`S'`, and a 2-fibre product of algebraic stacks is an algebraic stack by Stacks 04TF. -/
theorem isAlgebraicStack_changeBase_baseChange
    (h𝒳' : IsAlgebraicStack.{u, w} B S' hS' 𝒳') :
    IsAlgebraicStack.{u, w} B S' hS'
      (changeBase B S S' hS hS' g (baseChange B S S' hS hS' g 𝒳')) := by
  obtain ⟨hZfib, hZstack, hZdiag, -⟩ :=
    isAlgebraicStack_schemeFibredCategory.{u, w} B S' hS' (Over.mk (𝟙 (B.obj hS')))
  refine (isAlgebraicStack_iff_of_equivalence'.{u, w} B S' hS' _ _
    (baseChangeProductEquivalence B S S' hS hS' g 𝒳')).2 ?_
  exact isAlgebraicStack_twoFibreProduct.{u, w} B S' hS' 𝒳'
    (schemeFibredCategory B S' hS' (Over.mk g)).val
    (schemeFibredCategory B S' hS' (Over.mk (𝟙 (B.obj hS')))).val
    (toTerminalStack B S' hS' 𝒳')
    (toTerminalStack B S' hS' (schemeFibredCategory B S' hS' (Over.mk g)).val)
    hZstack hZdiag h𝒳'
    (isAlgebraicStack_schemeFibredCategory.{u, w} B S' hS' (Over.mk g))

/-- **Stacks 04X7.** The change of base of an algebraic stack over `S'` along `g : S ⟶ S'` is an
algebraic stack over `S`.

Its image under Construction A is the 2-fibre product `𝒳' ×_{S'} S`, hence an algebraic stack
over `S'` by Stacks 04TF; algebraicity is then carried back along Construction A by the direction
of Stacks 04X5 proved in
`AlgebraicGeometry.Stack.isAlgebraicStack_of_changeBase`. -/
@[stacks 04X7 "the change of base is an algebraic stack"]
theorem isAlgebraicStack_baseChange (h𝒳' : IsAlgebraicStack.{u, u + 1} B S' hS' 𝒳') :
    IsAlgebraicStack.{u, w} B S hS (baseChange B S S' hS hS' g 𝒳') := by
  have h2 := isAlgebraicStack_changeBase_baseChange.{u, u + 1} B S S' hS hS' g 𝒳' h𝒳'
  have hfib : (baseChange B S S' hS hS' g 𝒳').p.IsFiberedInGroupoids :=
    (isFiberedInGroupoids_changeBase_iff B S S' hS hS' g
      (baseChange B S S' hS hS' g 𝒳')).1 h2.choose
  exact isAlgebraicStack_of_changeBase B S S' hS hS' g
    ⟨baseChange B S S' hS hS' g 𝒳', hfib⟩ h2

end AlgebraicGeometry.Stack

end
