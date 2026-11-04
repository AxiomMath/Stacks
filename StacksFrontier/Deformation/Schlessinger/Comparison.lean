module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
public import StacksFrontier.CategoryTheory.TwoFibreProduct.SymmetricModel
public import StacksFrontier.Deformation.Basic
public import StacksFrontier.Deformation.Cofibered
public import StacksFrontier.Deformation.Smooth.Pushforward

/-!
# The comparison functor for a cofibered category

The comparison functor from a category cofibered in groupoids to the
category of elements of its functor of isomorphism classes.

## Main definitions

* `ComparisonFunctor` records the canonical 2-cell and the resulting
  functor to the categorical 2-fibre product.

## Main results

* `comparisonFunctor` constructs the comparison functor associated
  to a fibre square and choices of pushforwards.

## Implementation notes

The source first chooses pushforwards and then obtains a 2-commutative square
of fibre categories.  `ComparisonFunctor.squareIso` is its canonical 2-cell;
the compatibility field characterizes each component by the two composite
cocartesian arrows.  The actual functor is then defined from that natural
isomorphism, so its projection functors are definitionally the two chosen
pushforwards.

## References

* [Stacks Project, Tag 06SP](https://stacks.math.columbia.edu/tag/06SP)
-/

@[expose] public section

namespace Deformation

/-! ### The comparison functor for a cofibered category -/

section
open CategoryTheory CategoryTheory.Limits
universe u v w u₁ v₁


/-- Data of the comparison functor associated to a commutative square of the
base.  The compatibility equation says that the natural isomorphism between
the two composite pushforwards is the canonical one under the common source. -/
public structure SquareComparisonFunctor
    {F : Type u₁} [Category.{v₁} F] {C : Type u} [Category.{v} C]
    (p : F ⥤ C) {P A₁ A₂ A : C}
    (p₁ : P ⟶ A₁) (p₂ : P ⟶ A₂) (f₁ : A₁ ⟶ A) (f₂ : A₂ ⟶ A)
    (P₁ : PushforwardChoice p p₁) (P₂ : PushforwardChoice p p₂)
    (F₁ : PushforwardChoice p f₁) (F₂ : PushforwardChoice p f₂)
    (Qp₁ : PushforwardFunctor P₁) (Qp₂ : PushforwardFunctor P₂)
    (Qf₁ : PushforwardFunctor F₁) (Qf₂ : PushforwardFunctor F₂) where
  /-- The canonical natural isomorphism between the two composite
  pushforward functors. -/
  squareIso : Qp₁.toFunctor ⋙ Qf₁.toFunctor ≅ Qp₂.toFunctor ⋙ Qf₂.toFunctor
  /-- The canonical isomorphism is the unique comparison compatible with the
  chosen cocartesian arrows. -/
  compatibility : ∀ x,
    P₁.inclusion x ≫ F₁.inclusion (P₁.obj x) ≫
        Functor.Fiber.fiberInclusion.map (squareIso.hom.app x) =
      P₂.inclusion x ≫ F₂.inclusion (P₂.obj x)

/-- The functor from the fibre over `P` to the 2-fibre product of the fibres
over `A₁` and `A₂`. -/
public def SquareComparisonFunctor.toFunctor
    {F : Type u₁} [Category.{v₁} F] {C : Type u} [Category.{v} C]
    {p : F ⥤ C} {P A₁ A₂ A : C}
    {p₁ : P ⟶ A₁} {p₂ : P ⟶ A₂} {f₁ : A₁ ⟶ A} {f₂ : A₂ ⟶ A}
    {P₁ : PushforwardChoice p p₁} {P₂ : PushforwardChoice p p₂}
    {F₁ : PushforwardChoice p f₁} {F₂ : PushforwardChoice p f₂}
    {Qp₁ : PushforwardFunctor P₁} {Qp₂ : PushforwardFunctor P₂}
    {Qf₁ : PushforwardFunctor F₁} {Qf₂ : PushforwardFunctor F₂}
    (K : SquareComparisonFunctor p p₁ p₂ f₁ f₂ P₁ P₂ F₁ F₂ Qp₁ Qp₂ Qf₁ Qf₂) :
    p.Fiber P ⥤ CategoricalPullback Qf₁.toFunctor Qf₂.toFunctor :=
  (CategoricalPullback.CatCommSqOver.toFunctorToCategoricalPullback
    Qf₁.toFunctor Qf₂.toFunctor (p.Fiber P)).obj
      ⟨Qp₁.toFunctor, Qp₂.toFunctor, K.squareIso⟩

/-- **Stacks Project, Tag 06SP.** For a pullback square of Artinian local
`Λ`-algebras with `f₂` surjective, choices of pushforwards in a category
cofibered in groupoids determine the canonical comparison functor
`F(P) ⟶ F(A₁) ×_{F(A)} F(A₂)`. -/
@[stacks 06SP]
public noncomputable def squareComparisonFunctor
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    {F : Type u₁} [Category.{v₁} F]
    (p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k)
    (_hp : IsCofiberedInGroupoids p)
    {P A₁ A₂ A : ArtinianLocalAlgCat.{u, v, w} Λ k}
    (p₁ : P ⟶ A₁) (p₂ : P ⟶ A₂) (f₁ : A₁ ⟶ A) (f₂ : A₂ ⟶ A)
    (hP : IsPullback p₁ p₂ f₁ f₂) (_hf₂ : Function.Surjective f₂.hom)
    (P₁ : PushforwardChoice p p₁) (P₂ : PushforwardChoice p p₂)
    (F₁ : PushforwardChoice p f₁) (F₂ : PushforwardChoice p f₂)
    (Qp₁ : PushforwardFunctor P₁) (Qp₂ : PushforwardFunctor P₂)
    (Qf₁ : PushforwardFunctor F₁) (Qf₂ : PushforwardFunctor F₂) :
    SquareComparisonFunctor p p₁ p₂ f₁ f₂ P₁ P₂ F₁ F₂ Qp₁ Qp₂ Qf₁ Qf₂ := by
  classical
  let s := p₁ ≫ f₁
  have hbase : p₁ ≫ f₁ = p₂ ≫ f₂ := hP.w
  let T₁ := Qp₁.toFunctor ⋙ Qf₁.toFunctor
  let T₂ := Qp₂.toFunctor ⋙ Qf₂.toFunctor
  let iP := Functor.Fiber.fiberInclusion (p := p) (S := P)
  let iA := Functor.Fiber.fiberInclusion (p := p) (S := A)
  let e₁ (x : p.Fiber P) : (Functor.Fiber.fiberInclusion (p := p) (S := P)).obj x ⟶
      (Functor.Fiber.fiberInclusion (p := p) (S := A)).obj (T₁.obj x) :=
    P₁.inclusion x ≫ F₁.inclusion (P₁.obj x)
  let e₂ (x : p.Fiber P) : (Functor.Fiber.fiberInclusion (p := p) (S := P)).obj x ⟶
      (Functor.Fiber.fiberInclusion (p := p) (S := A)).obj (T₂.obj x) :=
    P₂.inclusion x ≫ F₂.inclusion (P₂.obj x)
  have sc₁ (x : p.Fiber P) : p.IsStronglyCocartesian s (e₁ x) := by
    dsimp [e₁, s]
    let : p.IsStronglyCocartesian p₁ (P₁.inclusion x) := P₁.cocartesian x
    let : p.IsStronglyCocartesian f₁ (F₁.inclusion (P₁.obj x)) :=
      F₁.cocartesian (P₁.obj x)
    exact CategoryTheory.Functor.IsStronglyCocartesian.comp
      (p := p) (f := p₁) (g := f₁) (φ := P₁.inclusion x)
      (ψ := F₁.inclusion (P₁.obj x))
  have sc₂ (x : p.Fiber P) : p.IsStronglyCocartesian s (e₂ x) := by
    dsimp [e₂, s]
    let : p.IsStronglyCocartesian p₂ (P₂.inclusion x) := P₂.cocartesian x
    let : p.IsStronglyCocartesian f₂ (F₂.inclusion (P₂.obj x)) :=
      F₂.cocartesian (P₂.obj x)
    exact hbase ▸ CategoryTheory.Functor.IsStronglyCocartesian.comp
      (p := p) (f := p₂) (g := f₂) (φ := P₂.inclusion x)
      (ψ := F₂.inclusion (P₂.obj x))
  let component (x : p.Fiber P) : T₁.obj x ≅ T₂.obj x := by
    let : p.IsStronglyCocartesian s (e₁ x) := sc₁ x
    let : p.IsStronglyCocartesian s (e₂ x) := sc₂ x
    let : p.IsCocartesian s (e₁ x) := inferInstance
    let : p.IsCocartesian s (e₂ x) := inferInstance
    let j := CategoryTheory.Functor.IsCocartesian.codomainUniqueUpToIso p s (e₁ x) (e₂ x)
    exact ⟨⟨j.hom, CategoryTheory.Functor.IsCocartesian.map_isHomLift p s (e₁ x) (e₂ x)⟩,
      ⟨j.inv, CategoryTheory.Functor.IsCocartesian.map_isHomLift p s (e₂ x) (e₁ x)⟩,
      Functor.Fiber.hom_ext j.hom_inv_id, Functor.Fiber.hom_ext j.inv_hom_id⟩
  have compFac (x : p.Fiber P) :
      e₁ x ≫ iA.map ((component x).hom) = e₂ x := by
    let : p.IsStronglyCocartesian s (e₁ x) := sc₁ x
    let : p.IsStronglyCocartesian s (e₂ x) := sc₂ x
    let : p.IsCocartesian s (e₁ x) := inferInstance
    let : p.IsCocartesian s (e₂ x) := inferInstance
    let j := CategoryTheory.Functor.IsCocartesian.codomainUniqueUpToIso p s (e₁ x) (e₂ x)
    change e₁ x ≫ j.hom = e₂ x
    exact CategoryTheory.Functor.IsCocartesian.fac p s _ _
  have path₁ {x y : p.Fiber P} (g : x ⟶ y) :
      (P₁.inclusion x ≫ F₁.inclusion (P₁.obj x)) ≫
          Functor.Fiber.fiberInclusion.map (Qf₁.toFunctor.map (Qp₁.toFunctor.map g)) =
        Functor.Fiber.fiberInclusion.map g ≫ P₁.inclusion y ≫ F₁.inclusion (P₁.obj y) := by
    have hF : F₁.inclusion (P₁.obj x) ≫
        Functor.Fiber.fiberInclusion.map (Qf₁.toFunctor.map (Qp₁.toFunctor.map g)) =
        Functor.Fiber.fiberInclusion.map (Qp₁.toFunctor.map g) ≫ F₁.inclusion (P₁.obj y) :=
      Qf₁.inclusion_naturality (Qp₁.toFunctor.map g)
    have hP : P₁.inclusion x ≫ Functor.Fiber.fiberInclusion.map (Qp₁.toFunctor.map g) =
        Functor.Fiber.fiberInclusion.map g ≫ P₁.inclusion y :=
      Qp₁.inclusion_naturality g
    exact (Category.assoc _ _ _).trans <| (congrArg (P₁.inclusion x ≫ ·) hF).trans <|
      ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ F₁.inclusion (P₁.obj y)) hP)).trans
        (Category.assoc _ _ _)
  have path₂ {x y : p.Fiber P} (g : x ⟶ y) :
      (P₂.inclusion x ≫ F₂.inclusion (P₂.obj x)) ≫
          Functor.Fiber.fiberInclusion.map (Qf₂.toFunctor.map (Qp₂.toFunctor.map g)) =
        Functor.Fiber.fiberInclusion.map g ≫ P₂.inclusion y ≫ F₂.inclusion (P₂.obj y) := by
    have hF : F₂.inclusion (P₂.obj x) ≫
        Functor.Fiber.fiberInclusion.map (Qf₂.toFunctor.map (Qp₂.toFunctor.map g)) =
        Functor.Fiber.fiberInclusion.map (Qp₂.toFunctor.map g) ≫ F₂.inclusion (P₂.obj y) :=
      Qf₂.inclusion_naturality (Qp₂.toFunctor.map g)
    have hP : P₂.inclusion x ≫ Functor.Fiber.fiberInclusion.map (Qp₂.toFunctor.map g) =
        Functor.Fiber.fiberInclusion.map g ≫ P₂.inclusion y :=
      Qp₂.inclusion_naturality g
    exact (Category.assoc _ _ _).trans <| (congrArg (P₂.inclusion x ≫ ·) hF).trans <|
      ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ F₂.inclusion (P₂.obj y)) hP)).trans
        (Category.assoc _ _ _)
  have nat : ∀ {x y : p.Fiber P} (g : x ⟶ y),
      T₁.map g ≫ (component y).hom = (component x).hom ≫ T₂.map g := by
    intro x y g
    apply Functor.Fiber.hom_ext
    let : p.IsStronglyCocartesian s (e₁ x) := sc₁ x
    apply CategoryTheory.Functor.IsStronglyCocartesian.ext p s (e₁ x) (𝟙 A)
    have hp1 : e₁ x ≫ iA.map (T₁.map g) = iP.map g ≫ e₁ y := path₁ g
    have hp2 : e₂ x ≫ iA.map (T₂.map g) = iP.map g ≫ e₂ y := path₂ g
    simp only [Functor.map_comp]
    rw [reassoc_of% hp1, compFac y, reassoc_of% (compFac x), hp2]
  exact ⟨NatIso.ofComponents component nat,
    fun x => (Category.assoc _ _ _).symm.trans (compFac x)⟩

end

end Deformation
