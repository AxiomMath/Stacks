module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Category
public import StacksFrontier.AlgebraicGeometry.Stacks.Representability
public import StacksFrontier.CategoryTheory.FiberedCategory.ElementsSection

/-!
# The relative map to the algebraic space representing a fibre of a 1-morphism

Let `F : 𝒳 ⟶ 𝒴` be a 1-morphism of categories fibred in groupoids over the big fppf site of a
scheme `S`, let `y` be a scheme-valued point of `𝒴` over a scheme `U` over `S`, and let `X_y` be
an algebraic space over `U` representing the 2-fibre product `(Sch/U)_{fppf} ×_{y, 𝒴, F} 𝒳` — the
representation supplied, for a 1-morphism representable by algebraic spaces, by
`AlgebraicGeometry.Stack.IsRepresentableByAlgebraicSpaces`. A scheme `Z` over `U`, an object `x`
of `𝒳` over `Z` and a vertical isomorphism `α : y|_Z ⟶ F(x)` then assemble into an object
`ξ = (Z, Z → U, x, α)` of that 2-fibre product lying over `Z`, and `ξ` names a section of `X_y`
over `Z`, that is a morphism `x_α : Z ⟶ X_y` of algebraic spaces over `U`.

## Main definitions

* `AlgebraicGeometry.Stack.relativeObj`: the object `ξ = (Z, Z → U, x, α)` of the 2-fibre
  product.
* `AlgebraicGeometry.Stack.relativeObjHom`: a morphism `g : Z' ⟶ Z` of schemes over `U` together
  with a compatible morphism `x' ⟶ x` of `𝒳` as a morphism `ξ' ⟶ ξ`.
* `AlgebraicGeometry.Stack.relativeSection`: the section of the representing presheaf named by
  `ξ`.
* `AlgebraicGeometry.Stack.relativeMap`: the morphism `x_α : Z ⟶ X_y` of algebraic spaces over
  `U`.

## Main results

* `AlgebraicGeometry.Stack.psiIso_hom_app_relativeObj`: the 2-cell filling the 2-fibre product
  square has `α` for its component at `ξ`.
* `AlgebraicGeometry.Stack.relativeSection_map`: the section named by `ξ'` is the restriction
  of the section named by `ξ` along `g`.
* `AlgebraicGeometry.Stack.relativeSection_eq_of_vertical`: data isomorphic over `Z` name the
  same section, so `x_α` depends on `ξ` only through its isomorphism class in the fibre over `Z`.

## References

* [Stacks Project, Tag 0040](https://stacks.math.columbia.edu/tag/0040)
* [Stacks Project, Tag 025Z](https://stacks.math.columbia.edu/tag/025Z)
* [Stacks Project, Tag 02X2](https://stacks.math.columbia.edu/tag/02X2)
* [Stacks Project, Tag 02XV](https://stacks.math.columbia.edu/tag/02XV)
* [Stacks Project, Tag 02ZW](https://stacks.math.columbia.edu/tag/02ZW)
* [Stacks Project, Tag 06CJ](https://stacks.math.columbia.edu/tag/06CJ)
* [Stacks Project, Tag 06CK](https://stacks.math.columbia.edu/tag/06CK)
-/

@[expose] public section

open CategoryTheory Opposite

namespace AlgebraicGeometry.Stack

universe u v₁ v₂ w₁ w₂

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {𝒳 : BasedCategory.{v₁, w₁} (BigFppfOver B S hS)}
  {𝒴 : BasedCategory.{v₂, w₂} (BigFppfOver B S hS)}
  (F : 𝒳 ⥤ᵇ 𝒴) {U : BigFppfOver B S hS}
  (y : BigFppfOver B U.left.1 U.left.2 ⥤ 𝒴.obj)

/-! ### The object of the 2-fibre product -/

/-- The object `ξ = (Z, Z → U, x, α)` of the 2-fibre product
`(Sch/U)_{fppf} ×_{y, 𝒴, F} 𝒳` attached to a scheme `Z` over `U`, an object `x` of `𝒳` over `Z`
and an isomorphism `α : y|_Z ⟶ F(x)` vertical over `Z`. It lies over `Z` for the first
projection. -/
@[stacks 06CK "the object (Z, Z → U, x, α) of the 2-fibre product"]
def relativeObj (Z : BigFppfOver B U.left.1 U.left.2) (x : 𝒳.obj)
    (hx : 𝒳.p.obj x = (Over.map U.hom).obj Z) (α : y.obj Z ≅ F.toFunctor.obj x)
    (hα : 𝒴.p.IsHomLift (𝟙 ((Over.map U.hom).obj Z)) α.hom) :
    TwoFibreProductOver (Over.map U.hom) 𝒳.p 𝒴.p y F.toFunctor where
  base := (Over.map U.hom).obj Z
  x := Z
  y := x
  hx := rfl
  hy := hx
  iso := α
  vertical := hα

variable {F y}

/-- `ξ` lies over the scheme `Z` read as a scheme over `S`. -/
@[simp]
lemma relativeObj_base {Z : BigFppfOver B U.left.1 U.left.2} {x : 𝒳.obj}
    {hx : 𝒳.p.obj x = (Over.map U.hom).obj Z} {α : y.obj Z ≅ F.toFunctor.obj x}
    {hα : 𝒴.p.IsHomLift (𝟙 ((Over.map U.hom).obj Z)) α.hom} :
    (relativeObj F y Z x hx α hα).base = (Over.map U.hom).obj Z := rfl

/-- The first component of `ξ` is the scheme `Z` over `U`. -/
@[simp]
lemma relativeObj_x {Z : BigFppfOver B U.left.1 U.left.2} {x : 𝒳.obj}
    {hx : 𝒳.p.obj x = (Over.map U.hom).obj Z} {α : y.obj Z ≅ F.toFunctor.obj x}
    {hα : 𝒴.p.IsHomLift (𝟙 ((Over.map U.hom).obj Z)) α.hom} :
    (relativeObj F y Z x hx α hα).x = Z := rfl

/-- The second component of `ξ` is the object `x` of `𝒳`. -/
@[simp]
lemma relativeObj_y {Z : BigFppfOver B U.left.1 U.left.2} {x : 𝒳.obj}
    {hx : 𝒳.p.obj x = (Over.map U.hom).obj Z} {α : y.obj Z ≅ F.toFunctor.obj x}
    {hα : 𝒴.p.IsHomLift (𝟙 ((Over.map U.hom).obj Z)) α.hom} :
    (relativeObj F y Z x hx α hα).y = x := rfl

/-- The comparison isomorphism of `ξ` is `α`. -/
@[simp]
lemma relativeObj_iso {Z : BigFppfOver B U.left.1 U.left.2} {x : 𝒳.obj}
    {hx : 𝒳.p.obj x = (Over.map U.hom).obj Z} {α : y.obj Z ≅ F.toFunctor.obj x}
    {hα : 𝒴.p.IsHomLift (𝟙 ((Over.map U.hom).obj Z)) α.hom} :
    (relativeObj F y Z x hx α hα).iso = α := rfl

/-- The 2-cell filling the 2-fibre product square, which compares the composite to `𝒴` through
`y` with the composite through `F`, has the given isomorphism `α` for its component at `ξ`. -/
lemma psiIso_hom_app_relativeObj {Z : BigFppfOver B U.left.1 U.left.2} {x : 𝒳.obj}
    {hx : 𝒳.p.obj x = (Over.map U.hom).obj Z} {α : y.obj Z ≅ F.toFunctor.obj x}
    {hα : 𝒴.p.IsHomLift (𝟙 ((Over.map U.hom).obj Z)) α.hom} :
    (TwoFibreProductOver.psiIso (Over.map U.hom) 𝒳.p 𝒴.p y F.toFunctor).hom.app
      (relativeObj F y Z x hx α hα) = α.hom := rfl

/-- A morphism `g : Z' ⟶ Z` of schemes over `U` together with a morphism `a : x' ⟶ x` of `𝒳`
lying over `g` and compatible with the two comparison isomorphisms, read as a morphism
`ξ' ⟶ ξ` of the 2-fibre product. -/
def relativeObjHom {Z Z' : BigFppfOver B U.left.1 U.left.2} {x x' : 𝒳.obj}
    {hx : 𝒳.p.obj x = (Over.map U.hom).obj Z} {hx' : 𝒳.p.obj x' = (Over.map U.hom).obj Z'}
    {α : y.obj Z ≅ F.toFunctor.obj x} {α' : y.obj Z' ≅ F.toFunctor.obj x'}
    {hα : 𝒴.p.IsHomLift (𝟙 ((Over.map U.hom).obj Z)) α.hom}
    {hα' : 𝒴.p.IsHomLift (𝟙 ((Over.map U.hom).obj Z')) α'.hom}
    (g : Z' ⟶ Z) (a : x' ⟶ x) (ha : 𝒳.p.IsHomLift ((Over.map U.hom).map g) a)
    (w : y.map g ≫ α.hom = α'.hom ≫ F.toFunctor.map a) :
    relativeObj F y Z' x' hx' α' hα' ⟶ relativeObj F y Z x hx α hα where
  hbase := (Over.map U.hom).map g
  a := g
  b := a
  ha := .map g
  hb := ha
  w := w

/-- The first component of the induced morphism is `g`. -/
@[simp]
lemma relativeObjHom_a {Z Z' : BigFppfOver B U.left.1 U.left.2} {x x' : 𝒳.obj}
    {hx : 𝒳.p.obj x = (Over.map U.hom).obj Z} {hx' : 𝒳.p.obj x' = (Over.map U.hom).obj Z'}
    {α : y.obj Z ≅ F.toFunctor.obj x} {α' : y.obj Z' ≅ F.toFunctor.obj x'}
    {hα : 𝒴.p.IsHomLift (𝟙 ((Over.map U.hom).obj Z)) α.hom}
    {hα' : 𝒴.p.IsHomLift (𝟙 ((Over.map U.hom).obj Z')) α'.hom}
    (g : Z' ⟶ Z) (a : x' ⟶ x) (ha : 𝒳.p.IsHomLift ((Over.map U.hom).map g) a)
    (w : y.map g ≫ α.hom = α'.hom ≫ F.toFunctor.map a) :
    (relativeObjHom (hx := hx) (hx' := hx') (hα := hα) (hα' := hα') g a ha w).a = g := rfl

/-- The second component of the induced morphism is `a`. -/
@[simp]
lemma relativeObjHom_b {Z Z' : BigFppfOver B U.left.1 U.left.2} {x x' : 𝒳.obj}
    {hx : 𝒳.p.obj x = (Over.map U.hom).obj Z} {hx' : 𝒳.p.obj x' = (Over.map U.hom).obj Z'}
    {α : y.obj Z ≅ F.toFunctor.obj x} {α' : y.obj Z' ≅ F.toFunctor.obj x'}
    {hα : 𝒴.p.IsHomLift (𝟙 ((Over.map U.hom).obj Z)) α.hom}
    {hα' : 𝒴.p.IsHomLift (𝟙 ((Over.map U.hom).obj Z')) α'.hom}
    (g : Z' ⟶ Z) (a : x' ⟶ x) (ha : 𝒳.p.IsHomLift ((Over.map U.hom).map g) a)
    (w : y.map g ≫ α.hom = α'.hom ≫ F.toFunctor.map a) :
    (relativeObjHom (hx := hx) (hx' := hx') (hα := hα) (hα' := hα') g a ha w).b = a := rfl

/-! ### The relative map -/

variable (F y) {Xy : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u}

variable (e : StacksRepresentableCFG.EquivalenceOver
  (TwoFibreProductOver.fst (Over.map U.hom) 𝒳.p 𝒴.p y F.toFunctor)
  (presheafOfCategories (Xy ⋙ typeToCat)).p)

/-- The section of `X_y` over `Z` named by the object `ξ = (Z, Z → U, x, α)`: carry `ξ` through
the equivalence exhibiting `X_y` as representing the 2-fibre product and read off the element of
`X_y(Z)` that its image names. -/
def relativeSection (Z : BigFppfOver B U.left.1 U.left.2) (x : 𝒳.obj)
    (hx : 𝒳.p.obj x = (Over.map U.hom).obj Z) (α : y.obj Z ≅ F.toFunctor.obj x)
    (hα : 𝒴.p.IsHomLift (𝟙 ((Over.map U.hom).obj Z)) α.hom) : Xy.obj (op Z) :=
  PresheafOfCategories.sectionOfObj e (relativeObj F y Z x hx α hα) rfl

variable {F y e}

/-- **The section named by `ξ` is compatible with restriction.** A morphism
`g : Z' ⟶ Z` of schemes over `U` and a morphism `a : x' ⟶ x` of `𝒳` over it, compatible with the
two comparison isomorphisms, carry the section named by `ξ` to the section named by `ξ'`. -/
theorem relativeSection_map {Z Z' : BigFppfOver B U.left.1 U.left.2} {x x' : 𝒳.obj}
    {hx : 𝒳.p.obj x = (Over.map U.hom).obj Z} {hx' : 𝒳.p.obj x' = (Over.map U.hom).obj Z'}
    {α : y.obj Z ≅ F.toFunctor.obj x} {α' : y.obj Z' ≅ F.toFunctor.obj x'}
    {hα : 𝒴.p.IsHomLift (𝟙 ((Over.map U.hom).obj Z)) α.hom}
    {hα' : 𝒴.p.IsHomLift (𝟙 ((Over.map U.hom).obj Z')) α'.hom}
    (g : Z' ⟶ Z) (a : x' ⟶ x) (ha : 𝒳.p.IsHomLift ((Over.map U.hom).map g) a)
    (w : y.map g ≫ α.hom = α'.hom ≫ F.toFunctor.map a) :
    relativeSection F y e Z' x' hx' α' hα' =
      Xy.map g.op (relativeSection F y e Z x hx α hα) :=
  PresheafOfCategories.sectionOfObj_map (W := Z) (W' := Z') e rfl rfl g _
    (.map (relativeObjHom (hx := hx) (hx' := hx') (hα := hα) (hα' := hα') g a ha w))

/-- **The section named by `ξ` depends only on the isomorphism class of `ξ`.** Two sets of
data over the same `Z` related by a vertical morphism of `𝒳` compatible with the comparison
isomorphisms name the same section of `X_y`. -/
theorem relativeSection_eq_of_vertical {Z : BigFppfOver B U.left.1 U.left.2} {x x' : 𝒳.obj}
    {hx : 𝒳.p.obj x = (Over.map U.hom).obj Z} {hx' : 𝒳.p.obj x' = (Over.map U.hom).obj Z}
    {α : y.obj Z ≅ F.toFunctor.obj x} {α' : y.obj Z ≅ F.toFunctor.obj x'}
    {hα : 𝒴.p.IsHomLift (𝟙 ((Over.map U.hom).obj Z)) α.hom}
    {hα' : 𝒴.p.IsHomLift (𝟙 ((Over.map U.hom).obj Z)) α'.hom}
    (a : x' ⟶ x) (ha : 𝒳.p.IsHomLift (𝟙 ((Over.map U.hom).obj Z)) a)
    (w : α.hom = α'.hom ≫ F.toFunctor.map a) :
    relativeSection F y e Z x' hx' α' hα' = relativeSection F y e Z x hx α hα := by
  simpa using relativeSection_map (e := e) (hx := hx) (hx' := hx') (hα := hα) (hα' := hα')
    (𝟙 Z) a (by simpa using ha) (by simpa using w)

/-- The morphism `x_α : Z ⟶ X_y` of algebraic spaces over `U` attached to a
scheme `Z` over `U`, an object `x` of `𝒳` over `Z` and an isomorphism `α : y|_Z ⟶ F(x)` vertical
over `Z`: the morphism of presheaves on the big fppf site of `U` named, under the Yoneda lemma,
by the section of `X_y` over `Z` that `ξ = (Z, Z → U, x, α)` names. -/
@[stacks 06CK "the morphism x_α of the left-hand diagram"]
def relativeMap (F : 𝒳 ⥤ᵇ 𝒴) (y : BigFppfOver B U.left.1 U.left.2 ⥤ 𝒴.obj)
    (e : StacksRepresentableCFG.EquivalenceOver
      (TwoFibreProductOver.fst (Over.map U.hom) 𝒳.p 𝒴.p y F.toFunctor)
      (presheafOfCategories (Xy ⋙ typeToCat)).p)
    (hXy : IsAlgebraicSpace B U.left.1 U.left.2 Xy)
    (Z : BigFppfOver B U.left.1 U.left.2) (x : 𝒳.obj)
    (hx : 𝒳.p.obj x = (Over.map U.hom).obj Z) (α : y.obj Z ≅ F.toFunctor.obj x)
    (hα : 𝒴.p.IsHomLift (𝟙 ((Over.map U.hom).obj Z)) α.hom) :
    (⟨yoneda.obj Z, isAlgebraicSpace_yoneda B U.left.1 U.left.2 Z⟩ :
        AlgebraicSpaces B U.left.1 U.left.2) ⟶ ⟨Xy, hXy⟩ :=
  ObjectProperty.homMk (yonedaEquiv.symm (relativeSection F y e Z x hx α hα))

/-- The section of `X_y` over `Z` named by `x_α` under the Yoneda lemma is the section named by
`ξ = (Z, Z → U, x, α)`. -/
@[simp]
lemma yonedaEquiv_relativeMap_hom {hXy : IsAlgebraicSpace B U.left.1 U.left.2 Xy}
    {Z : BigFppfOver B U.left.1 U.left.2} {x : 𝒳.obj}
    {hx : 𝒳.p.obj x = (Over.map U.hom).obj Z} {α : y.obj Z ≅ F.toFunctor.obj x}
    {hα : 𝒴.p.IsHomLift (𝟙 ((Over.map U.hom).obj Z)) α.hom} :
    yonedaEquiv (relativeMap F y e hXy Z x hx α hα).hom =
      relativeSection F y e Z x hx α hα :=
  yonedaEquiv.apply_symm_apply _

end AlgebraicGeometry.Stack

end
