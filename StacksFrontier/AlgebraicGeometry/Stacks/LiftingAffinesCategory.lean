module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.SpacesEtaleSite
public import StacksFrontier.AlgebraicGeometry.Stacks.AlgebraicSpaceStackPresentation
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.Thickening
public import StacksFrontier.CategoryTheory.TwoFibreProduct.Defs

/-!
# Smooth lifts of étale opens along a thickening of algebraic stacks (Stacks 0CJP)

Fix a thickening `ι : 𝒳 ⟶ 𝒳'` of algebraic stacks over `S`, an algebraic space `W` over `S`
and a smooth 1-morphism `x : W ⟶ 𝒳`. Stacks 0CJP attaches to this data a category together with
a functor to the spaces-étale site of `W`.

An object is a system `(U, U', a, i, x', α)`: an algebraic space `U` étale over `W` through
`a : U ⟶ W`, an algebraic space `U'`, a morphism `i : U ⟶ U'`, a smooth 1-morphism
`x' : U' ⟶ 𝒳'`, and a 2-morphism `α` exhibiting the square with sides `a`, `x`, `ι`, `i`, `x'`
as 2-commutative, subject to the condition that the square so filled is a 2-fibre product, i.e.
that `U = 𝒳 ×_{𝒳'} U'`. The condition forces `i` to be a thickening, so no thickening hypothesis
is imposed on it.

A morphism `(U, U', a, i, x', α) ⟶ (V, V', b, j, y', β)` is a system `(f, f', γ)`: a morphism
`f : U ⟶ V` over `W`, a morphism `f' : U' ⟶ V'` whose restriction to `U` is `f`, and a
2-morphism `γ : x' ⟶ y' ∘ f'` filling the right-hand triangle, subject to the coherence
`i^*γ ∘ α = f^*β`. The functor to the spaces-étale site of `W` sends the object to `a : U ⟶ W`
and the morphism to `f`.

## Main definitions

* `AlgebraicGeometry.Stack.algebraicSpaceStackFunctor`: an algebraic space over `S`, regarded as
  an algebraic stack over `S`, functorially in the space.
* `AlgebraicGeometry.Stack.EtaleSmoothLift`: **Stacks 0CJP**, the objects.
* `AlgebraicGeometry.Stack.EtaleSmoothLift.Hom`: **Stacks 0CJP**, the morphisms.
* `AlgebraicGeometry.Stack.EtaleSmoothLift.instCategory`: **Stacks 0CJP**, the category they
  form.
* `AlgebraicGeometry.Stack.EtaleSmoothLift.proj`: **Stacks 0CJP**, the functor to the
  spaces-étale site of `W`.

## Main results

* `AlgebraicGeometry.Stack.EtaleSmoothLift.coherence_comp`: the coherence condition relating the
  two fillers of a morphism is stable under composition, which is what makes the composite of
  two morphisms a morphism.

## Implementation notes

**Direction convention.** A morphism of this category lies *covariantly* over its image in the
spaces-étale site: a morphism out of the object carrying `U` carries `f : U ⟶ V` and
`f' : U' ⟶ V'`, and the projection to the spaces-étale site of `W` sends it to `f`. This is the
labelling of the source for the objects and for `f`, and it is the one Stacks 0CJS and Stacks
0CJT use downstream, where a morphism of the category produces `f' : V' ⟶ U'` out of the object
named `V` there and pullbacks are formed along a morphism `f : V ⟶ U` of the site. The source's
displayed coherence `β = j^*γ ∘ f^*α` is written for the opposite labelling of source and target
— it whiskers `α` by `f` on the right, which presupposes `f` pointing into the space carrying
`α` — and reads here, after exchanging the names of source and target, as `i^*γ ∘ α = f^*β`.
Accordingly `γ` points from `x'` to `y' ∘ f'`, the direction in which the right-hand triangle of
the source commutes once `f'` goes from `U'` to `V'`.

**The filler `α` and the comparison `γ`.** The 2-morphism `α` is an isomorphism, as the
2-commutative squares of Stacks 003O require; `γ` is a plain 2-morphism, as in the 2-category
`Spaces/𝒳'` of Stacks 04ZQ. Nothing is lost: the ambient 2-category is a `(2,1)`-category, so
every 2-morphism of it is invertible.

**Route to the category structure.** The source justifies the category axioms by reading the
objects and the morphisms as commutative diagrams in the 2-category `Spaces/𝒳'` of Stacks 04ZQ
(`AlgebraicGeometry.Stack.SpacesOverStack`). That route is not taken, for two reasons. First,
`SpacesOverStack` carries a `CategoryTheory.Bicategory` structure and no `Category` structure —
its composition of 1-morphisms is associative only up to its associator — so inheriting
composition from it would leave the associativity axiom to be proved from that associator, which
is the whole difficulty. Second, its objects require the structure 1-morphism to be
representable by algebraic spaces, a condition Stacks 0CJP does not impose on `x'`. Instead
composition is written down directly and the axioms are discharged from strictness of the
ambient 2-category: `CategoryTheory.BasedCategory` is a strict bicategory, hence so is every
`CategoryTheory.Bicategory.InducedBicategory` over it, hence so is
`AlgebraicGeometry.Stack.AlgebraicStacks`, which therefore carries a `Category` instance whose
composition is associative and unital by `rfl`. With that, reassociating a composite of
1-morphisms or of whiskerings is definitional, and each of the three axioms reduces to the
equality of the comparison 2-morphism alone.

**Term mode.** The proofs below are written as terms rather than with `rw` and `simp`. Goals in
`AlgebraicGeometry.Stack.AlgebraicStacks` are not type-correct at `implicit` transparency —
`CategoryTheory.Bicategory.InducedBicategory` is a semireducible definition over a subtype, so
the coercion of an object needs unfolding — and the rewriting tactics fail on them. The purely
bicategorical and purely categorical steps are isolated as lemmas stated for an arbitrary
bicategory or category, where the tactics work.

**The passage from spaces to stacks.** `AlgebraicGeometry.Stack.algebraicSpaceStack` turns an
algebraic space into an algebraic stack and `AlgebraicGeometry.Stack.associatedMap`
(**Stacks 0458**) turns a morphism of presheaves into a 1-morphism of the attached categories
fibred in groupoids; `algebraicSpaceStackFunctor` packages the two into a functor, which is what
makes `CategoryTheory.Functor.map_id` and `CategoryTheory.Functor.map_comp` available. Its
`map_comp` holds by `rfl`, so a composite `f' ≫ g'` and the composite of the induced
1-morphisms are interchangeable with no transport; its `map_id` does not, which is why the
comparison 2-morphism of an identity morphism is a `CategoryTheory.eqToHom`.

**Inherited caveat.** Thickenings of algebraic stacks are
`AlgebraicGeometry.Stack.IsThickening` (**Stacks 0BPP**, part (1)), which omits the
homeomorphism-of-underlying-spaces clause of the source for want of a library site for the point
topology of Stacks 04XL. That omission is inherited here.

## References

* [Stacks Project, Tag 03G0](https://stacks.math.columbia.edu/tag/03G0)
* [Stacks Project, Tag 03YP](https://stacks.math.columbia.edu/tag/03YP)
* [Stacks Project, Tag 04ZQ](https://stacks.math.columbia.edu/tag/04ZQ)
* [Stacks Project, Tag 075U](https://stacks.math.columbia.edu/tag/075U)
* [Stacks Project, Tag 0BPP](https://stacks.math.columbia.edu/tag/0BPP)
* [Stacks Project, Tag 0CJP](https://stacks.math.columbia.edu/tag/0CJP)
* [Stacks Project, Tag 0CJS](https://stacks.math.columbia.edu/tag/0CJS)
* [Stacks Project, Tag 0CJT](https://stacks.math.columbia.edu/tag/0CJT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Bicategory

namespace CategoryTheory

/-- **A sandwich of transports collapses.** Composing a morphism with transports along equalities
of objects on either side, and then with two further transports, is composing it with the two
composite transports. -/
theorem eqToHom_sandwich_trans {𝒞 : Type*} [Category 𝒞] {a b c d e f : 𝒞}
    (h₁ : a = b) (h₂ : b = c) (θ : c ⟶ d) (h₃ : d = e) (h₄ : e = f) :
    eqToHom h₁ ≫ ((eqToHom h₂ ≫ θ ≫ eqToHom h₃) ≫ eqToHom h₄) =
      eqToHom (h₁.trans h₂) ≫ θ ≫ eqToHom (h₃.trans h₄) := by
  subst h₁
  subst h₂
  subst h₃
  subst h₄
  simp

namespace Bicategory

/-- **Left whiskering a transport along an equality of 1-morphisms.** For `h : p = q` and a
2-morphism `θ : v ⟶ v'`, whiskering `θ` by `p` and whiskering it by `q` agree after the
transports along the two instances of `h`. -/
theorem eqToHom_whiskerLeft_naturality {ℬ : Type*} [Bicategory ℬ] {A C D : ℬ} {p q : A ⟶ C}
    (h : p = q) {v v' : C ⟶ D} (θ : v ⟶ v') :
    eqToHom (congrArg (· ≫ v) h) ≫ q ◁ θ = p ◁ θ ≫ eqToHom (congrArg (· ≫ v') h) := by
  subst h
  simp

/-- **Left whiskering a 2-morphism flanked by transports.** Whiskering distributes over the
composite, turning the two transports into transports along the whiskered equalities. -/
theorem whiskerLeft_eqToHom_comp_eqToHom {ℬ : Type*} [Bicategory ℬ] {A C D : ℬ} (F : A ⟶ C)
    {Q R V V' : C ⟶ D} (h₁ : Q = R) (ε : R ⟶ V) (h₂ : V = V') :
    F ◁ (eqToHom h₁ ≫ ε ≫ eqToHom h₂) =
      eqToHom (congrArg (fun p => F ≫ p) h₁) ≫ (F ◁ ε) ≫
        eqToHom (congrArg (fun p => F ≫ p) h₂) := by
  subst h₁
  subst h₂
  simp

end Bicategory

end CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

/-- **An algebraic space over `S`, regarded as an algebraic stack over `S`, functorially.** On
objects this is `AlgebraicGeometry.Stack.algebraicSpaceStack`, the category fibred in groupoids
attached to the presheaf; on morphisms it is the 1-morphism attached to a morphism of presheaves
by **Stacks 0458**. -/
def algebraicSpaceStackFunctor (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) :
    AlgebraicSpaces B S hS ⥤ AlgebraicStacks.{u, w} B S hS where
  obj X := algebraicSpaceStack.{u, w} B S hS X.obj X.property
  map f := Bicategory.InducedBicategory.mkHom (associatedMap B S hS f.hom).1
  map_id X := by
    apply Bicategory.InducedBicategory.hom_ext
    refine hom_ext_of_obj B S hS fun z => ?_
    rw [associatedMap_obj]
    rfl
  map_comp _ _ := rfl

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **Stacks 0CJP, the objects.** For a thickening `ι : 𝒳 ⟶ 𝒳'` of algebraic stacks over `S` and
a smooth 1-morphism `x` from an algebraic space `W` to `𝒳`, a *smooth lift of an étale open of
`W`* consists of an algebraic space `U` étale over `W` through `a : U ⟶ W`, an algebraic space
`U'` containing it through `i : U ⟶ U'`, a smooth 1-morphism `x' : U' ⟶ 𝒳'`, and a 2-morphism
filling the square with sides `a`, `x`, `ι`, `i`, `x'` which exhibits it as the 2-fibre product
`U = 𝒳 ×_{𝒳'} U'`.

The last condition forces `i` to be a thickening, so no thickening hypothesis is imposed on
it. -/
@[stacks 0CJP "objects"]
structure EtaleSmoothLift (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {𝒳 𝒳' : AlgebraicStacks.{u, w} B S hS} (ι : 𝒳 ⟶ 𝒳') (_hι : IsThickening ι)
    (W : AlgebraicSpaces B S hS)
    (x : (algebraicSpaceStackFunctor B S hS).obj W ⟶ 𝒳)
    (_hx : AlgebraicStacks.IsSmooth B S hS x) where
  /-- The algebraic space `U` together with the étale morphism `a : U ⟶ W` it lies over. -/
  base : Space.SpacesEtale B S hS W
  /-- The algebraic space `U'` that `U` is lifted into. -/
  ambient : AlgebraicSpaces B S hS
  /-- The morphism `i : U ⟶ U'`; the 2-fibre product condition makes it a thickening. -/
  inclusion : base.obj.left ⟶ ambient
  /-- The 1-morphism `x' : U' ⟶ 𝒳'`. -/
  ambientMap : (algebraicSpaceStackFunctor B S hS).obj ambient ⟶ 𝒳'
  /-- The 1-morphism `x'` is smooth. -/
  isSmooth_ambientMap : AlgebraicStacks.IsSmooth B S hS ambientMap
  /-- The 2-morphism `α : ι ∘ x ∘ a ⟶ x' ∘ i` filling the square. -/
  comm : ((algebraicSpaceStackFunctor B S hS).map base.obj.hom ≫ x) ≫ ι ≅
      (algebraicSpaceStackFunctor B S hS).map inclusion ≫ ambientMap
  /-- The square filled by `α` is a 2-fibre product, i.e. `U = 𝒳 ×_{𝒳'} U'`. -/
  isTwoFibreProduct : IsTwoFibreProduct
    (⟨(algebraicSpaceStackFunctor B S hS).obj base.obj.left,
      (algebraicSpaceStackFunctor B S hS).map base.obj.hom ≫ x,
      (algebraicSpaceStackFunctor B S hS).map inclusion, comm⟩ : TwoCommSq ι ambientMap)

namespace EtaleSmoothLift

/-- Reassociating a composite of a 2-morphism and two whiskered 2-morphisms. -/
private theorem comp_whiskerLeft_comp_whiskerLeft {𝒰 𝒰' 𝒱' 𝒯' 𝒳' : AlgebraicStacks.{u, w} B S hS}
    {I : 𝒰 ⟶ 𝒰'} {F' : 𝒰' ⟶ 𝒱'} {G' : 𝒱' ⟶ 𝒯'} {X : 𝒰' ⟶ 𝒳'} {Y : 𝒱' ⟶ 𝒳'}
    {Z : 𝒯' ⟶ 𝒳'} {P : 𝒰 ⟶ 𝒳'} (α : P ⟶ I ≫ X) (γ : X ⟶ F' ≫ Y) (δ : Y ⟶ G' ≫ Z) :
    (α ≫ I ◁ γ) ≫ I ◁ (F' ◁ δ) = α ≫ I ◁ (γ ≫ F' ◁ δ) := by
  rw [Bicategory.whiskerLeft_comp, Category.assoc]

/-- **The coherence condition is stable under composition.** In the 2-category of algebraic
stacks, if `γ` relates the filler `α` to the filler `β` along `(F, F')` and `δ` relates `β` to
the filler `ε` along `(G, G')`, then `γ` followed by `δ` whiskered by `F'` relates `α` to `ε`
along the composite `(F ≫ G, F' ≫ G')`. -/
theorem coherence_comp {𝒳' 𝒰 𝒱 𝒯 𝒰' 𝒱' 𝒯' : AlgebraicStacks.{u, w} B S hS}
    {F : 𝒰 ⟶ 𝒱} {G : 𝒱 ⟶ 𝒯} {I : 𝒰 ⟶ 𝒰'} {J : 𝒱 ⟶ 𝒱'} {K : 𝒯 ⟶ 𝒯'}
    {F' : 𝒰' ⟶ 𝒱'} {G' : 𝒱' ⟶ 𝒯'}
    {X : 𝒰' ⟶ 𝒳'} {Y : 𝒱' ⟶ 𝒳'} {Z : 𝒯' ⟶ 𝒳'}
    {P : 𝒰 ⟶ 𝒳'} {Q : 𝒱 ⟶ 𝒳'} {R : 𝒯 ⟶ 𝒳'}
    (hP : P = F ≫ Q) (hQ : Q = G ≫ R) (hI : F ≫ J = I ≫ F') (hJ : G ≫ K = J ≫ G')
    (hL : P = (F ≫ G) ≫ R) (hR : (F ≫ G) ≫ K = I ≫ F' ≫ G')
    (α : P ⟶ I ≫ X) (β : Q ⟶ J ≫ Y) (ε : R ⟶ K ≫ Z)
    (γ : X ⟶ F' ≫ Y) (δ : Y ⟶ G' ≫ Z)
    (hm : α ≫ I ◁ γ = eqToHom hP ≫ (F ◁ β) ≫ eqToHom (congrArg (· ≫ Y) hI))
    (hn : β ≫ J ◁ δ = eqToHom hQ ≫ (G ◁ ε) ≫ eqToHom (congrArg (· ≫ Z) hJ)) :
    α ≫ I ◁ (γ ≫ F' ◁ δ) =
      eqToHom hL ≫ ((F ≫ G) ◁ ε) ≫ eqToHom (congrArg (· ≫ Z) hR) :=
  have e₁ := (comp_whiskerLeft_comp_whiskerLeft α γ δ).symm
  have e₂ : (α ≫ I ◁ γ) ≫ I ◁ (F' ◁ δ) =
      (eqToHom hP ≫ (F ◁ β) ≫ eqToHom (congrArg (· ≫ Y) hI)) ≫ I ◁ (F' ◁ δ) :=
    congrArg (fun t => t ≫ I ◁ (F' ◁ δ)) hm
  have e₃ : (eqToHom hP ≫ (F ◁ β) ≫ eqToHom (congrArg (· ≫ Y) hI)) ≫ I ◁ (F' ◁ δ) =
      eqToHom hP ≫ ((F ◁ β) ≫ (eqToHom (congrArg (· ≫ Y) hI) ≫ I ◁ (F' ◁ δ))) :=
    (Category.assoc (eqToHom hP) ((F ◁ β) ≫ eqToHom (congrArg (· ≫ Y) hI))
          (I ◁ (F' ◁ δ))).trans
      (congrArg (fun t => eqToHom hP ≫ t)
        (Category.assoc (F ◁ β) (eqToHom (congrArg (· ≫ Y) hI)) (I ◁ (F' ◁ δ))))
  have e₄ : eqToHom hP ≫ ((F ◁ β) ≫ (eqToHom (congrArg (· ≫ Y) hI) ≫ I ◁ (F' ◁ δ))) =
      eqToHom hP ≫ ((F ◁ β) ≫ (F ◁ (J ◁ δ) ≫ eqToHom (congrArg (· ≫ (G' ≫ Z)) hI))) :=
    congrArg (fun t => eqToHom hP ≫ ((F ◁ β) ≫ t))
      (Bicategory.eqToHom_whiskerLeft_naturality hI δ)
  have e₅ : eqToHom hP ≫ ((F ◁ β) ≫ (F ◁ (J ◁ δ) ≫ eqToHom (congrArg (· ≫ (G' ≫ Z)) hI))) =
      eqToHom hP ≫ ((F ◁ (β ≫ J ◁ δ)) ≫ eqToHom (congrArg (· ≫ (G' ≫ Z)) hI)) :=
    congrArg (fun t => eqToHom hP ≫ t)
      ((Category.assoc (F ◁ β) (F ◁ (J ◁ δ))
            (eqToHom (congrArg (· ≫ (G' ≫ Z)) hI))).symm.trans
        (congrArg (fun t => t ≫ eqToHom (congrArg (· ≫ (G' ≫ Z)) hI))
          (Bicategory.whiskerLeft_comp F β (J ◁ δ)).symm))
  have e₆ : eqToHom hP ≫ ((F ◁ (β ≫ J ◁ δ)) ≫ eqToHom (congrArg (· ≫ (G' ≫ Z)) hI)) =
      eqToHom hP ≫ ((F ◁ (eqToHom hQ ≫ (G ◁ ε) ≫ eqToHom (congrArg (· ≫ Z) hJ))) ≫
        eqToHom (congrArg (· ≫ (G' ≫ Z)) hI)) :=
    congrArg (fun t => eqToHom hP ≫ ((F ◁ t) ≫ eqToHom (congrArg (· ≫ (G' ≫ Z)) hI))) hn
  have e₇ : eqToHom hP ≫ ((F ◁ (eqToHom hQ ≫ (G ◁ ε) ≫ eqToHom (congrArg (· ≫ Z) hJ))) ≫
        eqToHom (congrArg (· ≫ (G' ≫ Z)) hI)) =
      eqToHom hP ≫ ((eqToHom (congrArg (fun p => F ≫ p) hQ) ≫ (F ◁ (G ◁ ε)) ≫
        eqToHom (congrArg (fun p => F ≫ p) (congrArg (· ≫ Z) hJ))) ≫
          eqToHom (congrArg (· ≫ (G' ≫ Z)) hI)) :=
    congrArg (fun t => eqToHom hP ≫ (t ≫ eqToHom (congrArg (· ≫ (G' ≫ Z)) hI)))
      (Bicategory.whiskerLeft_eqToHom_comp_eqToHom F hQ (G ◁ ε) (congrArg (· ≫ Z) hJ))
  have e₈ : eqToHom hP ≫ ((eqToHom (congrArg (fun p => F ≫ p) hQ) ≫ (F ◁ (G ◁ ε)) ≫
        eqToHom (congrArg (fun p => F ≫ p) (congrArg (· ≫ Z) hJ))) ≫
          eqToHom (congrArg (· ≫ (G' ≫ Z)) hI)) =
      eqToHom (hP.trans (congrArg (fun p => F ≫ p) hQ)) ≫ (F ◁ (G ◁ ε)) ≫
        eqToHom ((congrArg (fun p => F ≫ p) (congrArg (· ≫ Z) hJ)).trans
          (congrArg (· ≫ (G' ≫ Z)) hI)) :=
    eqToHom_sandwich_trans hP (congrArg (fun p => F ≫ p) hQ) (F ◁ (G ◁ ε))
      (congrArg (fun p => F ≫ p) (congrArg (· ≫ Z) hJ)) (congrArg (· ≫ (G' ≫ Z)) hI)
  have e₉ : eqToHom (hP.trans (congrArg (fun p => F ≫ p) hQ)) ≫ (F ◁ (G ◁ ε)) ≫
        eqToHom ((congrArg (fun p => F ≫ p) (congrArg (· ≫ Z) hJ)).trans
          (congrArg (· ≫ (G' ≫ Z)) hI)) =
      eqToHom hL ≫ ((F ≫ G) ◁ ε) ≫ eqToHom (congrArg (· ≫ Z) hR) :=
    rfl
  e₁.trans (e₂.trans (e₃.trans (e₄.trans (e₅.trans (e₆.trans (e₇.trans (e₈.trans e₉)))))))

variable {𝒳 𝒳' : AlgebraicStacks.{u, w} B S hS} {ι : 𝒳 ⟶ 𝒳'} {hι : IsThickening ι}
  {W : AlgebraicSpaces B S hS}
  {x : (algebraicSpaceStackFunctor B S hS).obj W ⟶ 𝒳}
  {hx : AlgebraicStacks.IsSmooth B S hS x}

/-- **The étale structure morphism of the source factors through that of the target.** For a
morphism `f : U ⟶ V` over `W` one has `a = b ∘ f`, read in the 2-category of algebraic
stacks. -/
theorem base_leg (ξ η : EtaleSmoothLift B S hS ι hι W x hx) (f : ξ.base ⟶ η.base) :
    (algebraicSpaceStackFunctor B S hS).map ξ.base.obj.hom =
      (algebraicSpaceStackFunctor B S hS).map f.hom.left ≫
        (algebraicSpaceStackFunctor B S hS).map η.base.obj.hom := by
  rw [← CategoryTheory.Functor.map_comp, Over.w f.hom]

/-- **The left-hand leg of the coherence condition.** For a morphism `f : U ⟶ V` over `W` the
1-morphism `ι ∘ x ∘ a` factors as `ι ∘ x ∘ b ∘ f`. -/
theorem left_leg (ξ η : EtaleSmoothLift B S hS ι hι W x hx) (f : ξ.base ⟶ η.base) :
    ((algebraicSpaceStackFunctor B S hS).map ξ.base.obj.hom ≫ x) ≫ ι =
      (algebraicSpaceStackFunctor B S hS).map f.hom.left ≫
        (((algebraicSpaceStackFunctor B S hS).map η.base.obj.hom ≫ x) ≫ ι) :=
  congrArg (fun p => (p ≫ x) ≫ ι) (base_leg ξ η f)

/-- **A morphism restricting to `f` gives a commuting square of inclusions.** When
`f' : U' ⟶ V'` restricts to `f : U ⟶ V` one has `j ∘ f = f' ∘ i`, read in the 2-category of
algebraic stacks. -/
theorem lift_leg (ξ η : EtaleSmoothLift B S hS ι hι W x hx) (f : ξ.base ⟶ η.base)
    (g : ξ.ambient ⟶ η.ambient) (hg : ξ.inclusion ≫ g = f.hom.left ≫ η.inclusion) :
    (algebraicSpaceStackFunctor B S hS).map f.hom.left ≫
        (algebraicSpaceStackFunctor B S hS).map η.inclusion =
      (algebraicSpaceStackFunctor B S hS).map ξ.inclusion ≫
        (algebraicSpaceStackFunctor B S hS).map g := by
  rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp, hg]

/-- **The right-hand leg of the coherence condition.** When `f' : U' ⟶ V'` restricts to
`f : U ⟶ V`, the 1-morphism `y' ∘ j ∘ f` agrees with `y' ∘ f' ∘ i`. -/
theorem right_leg (ξ η : EtaleSmoothLift B S hS ι hι W x hx) (f : ξ.base ⟶ η.base)
    (g : ξ.ambient ⟶ η.ambient) (hg : ξ.inclusion ≫ g = f.hom.left ≫ η.inclusion) :
    (algebraicSpaceStackFunctor B S hS).map f.hom.left ≫
        ((algebraicSpaceStackFunctor B S hS).map η.inclusion ≫ η.ambientMap) =
      (algebraicSpaceStackFunctor B S hS).map ξ.inclusion ≫
        ((algebraicSpaceStackFunctor B S hS).map g ≫ η.ambientMap) :=
  congrArg (fun p => p ≫ η.ambientMap) (lift_leg ξ η f g hg)

/-- **Stacks 0CJP, the morphisms.** A morphism of smooth lifts of étale opens of `W` from
`(U, U', a, i, x', α)` to `(V, V', b, j, y', β)` is a morphism `f : U ⟶ V` over `W`, a morphism
`f' : U' ⟶ V'` restricting to `f` on `U`, and a 2-morphism `γ : x' ⟶ y' ∘ f'` filling the
right-hand triangle, compatible with the two fillers in the sense that `i^*γ ∘ α = f^*β`. -/
@[stacks 0CJP "morphisms"]
structure Hom (ξ η : EtaleSmoothLift B S hS ι hι W x hx) where
  /-- The morphism `f : U ⟶ V` over `W`, i.e. a morphism of the spaces-étale site of `W`. -/
  base : ξ.base ⟶ η.base
  /-- The morphism `f' : U' ⟶ V'`. -/
  ambient : ξ.ambient ⟶ η.ambient
  /-- The morphism `f'` restricts to `f` on `U`, i.e. `f' ∘ i = j ∘ f`. -/
  inclusion_comp : ξ.inclusion ≫ ambient = base.hom.left ≫ η.inclusion
  /-- The 2-morphism `γ : x' ⟶ y' ∘ f'` filling the right-hand triangle. -/
  comm : ξ.ambientMap ⟶ (algebraicSpaceStackFunctor B S hS).map ambient ≫ η.ambientMap
  /-- The coherence `i^*γ ∘ α = f^*β` between the two fillers and `γ`. -/
  coherence : ξ.comm.hom ≫ ((algebraicSpaceStackFunctor B S hS).map ξ.inclusion ◁ comm) =
      eqToHom (left_leg ξ η base) ≫
        ((algebraicSpaceStackFunctor B S hS).map base.hom.left ◁ η.comm.hom) ≫
          eqToHom (right_leg ξ η base ambient inclusion_comp)

/-- **A morphism of smooth lifts is determined by its three components.** The restriction
equation and the coherence are propositions, so two morphisms with the same `f`, `f'` and `γ`
agree. -/
theorem hom_congr {ξ η : EtaleSmoothLift B S hS ι hι W x hx} (m n : Hom ξ η)
    (hb : m.base = n.base) (ha : m.ambient = n.ambient) (hc : HEq m.comm n.comm) : m = n := by
  obtain ⟨b₁, a₁, r₁, c₁, k₁⟩ := m
  obtain ⟨b₂, a₂, r₂, c₂, k₂⟩ := n
  dsimp only at hb ha hc
  subst hb
  subst ha
  obtain rfl := eq_of_heq hc
  rfl

/-- **The 1-morphism `x'` is unchanged by precomposing with the identity of `U'`.** This is
`CategoryTheory.Functor.map_id` for `AlgebraicGeometry.Stack.algebraicSpaceStackFunctor`, in the
shape the identity morphism of a smooth lift needs. -/
theorem ambientMap_eq_map_id_comp (ξ : EtaleSmoothLift B S hS ι hι W x hx) :
    ξ.ambientMap =
      (algebraicSpaceStackFunctor B S hS).map (𝟙 ξ.ambient) ≫ ξ.ambientMap := by
  rw [CategoryTheory.Functor.map_id, Category.id_comp]

/-- **The identity morphism of a smooth lift of an étale open.** Its two space components are
identities and its comparison 2-morphism is the transport along
`AlgebraicGeometry.Stack.EtaleSmoothLift.ambientMap_eq_map_id_comp`. -/
def Hom.id (ξ : EtaleSmoothLift B S hS ι hι W x hx) : Hom ξ ξ where
  base := 𝟙 ξ.base
  ambient := 𝟙 ξ.ambient
  inclusion_comp := by simp
  comm := eqToHom (ambientMap_eq_map_id_comp ξ)
  coherence :=
    have s₁ : ξ.comm.hom ≫ ((algebraicSpaceStackFunctor B S hS).map ξ.inclusion ◁
          eqToHom (ambientMap_eq_map_id_comp ξ)) = ξ.comm.hom :=
      (congrArg (fun t => ξ.comm.hom ≫ t)
        (Bicategory.whiskerLeft_eqToHom
          ((algebraicSpaceStackFunctor B S hS).map ξ.inclusion)
          (ambientMap_eq_map_id_comp ξ))).trans (Category.comp_id ξ.comm.hom)
    have s₂ : ξ.comm.hom =
        (algebraicSpaceStackFunctor B S hS).map (𝟙 ξ.base.obj.left) ◁ ξ.comm.hom :=
      ((Category.id_comp ξ.comm.hom).symm.trans
        (Bicategory.eqToHom_whiskerLeft_naturality
          (CategoryTheory.Functor.map_id (algebraicSpaceStackFunctor B S hS)
            ξ.base.obj.left) ξ.comm.hom)).trans (Category.comp_id _)
    s₁.trans (s₂.trans ((Category.comp_id _).symm.trans (Category.id_comp _).symm))

/-- **A composite of morphisms of smooth lifts restricts correctly.** The restriction equations
of the two factors compose to the restriction equation of the composite. -/
theorem inclusion_comp_comp {ξ η ζ : EtaleSmoothLift B S hS ι hι W x hx} (m : Hom ξ η)
    (n : Hom η ζ) :
    ξ.inclusion ≫ (m.ambient ≫ n.ambient) = (m.base ≫ n.base).hom.left ≫ ζ.inclusion := by
  have h : (m.base ≫ n.base).hom.left = m.base.hom.left ≫ n.base.hom.left := rfl
  rw [h, ← Category.assoc, m.inclusion_comp, Category.assoc, n.inclusion_comp, ← Category.assoc]

/-- **The composite of two morphisms of smooth lifts of étale opens.** The space components
compose, and the comparison 2-morphisms compose after whiskering the second by the first lifted
space component. -/
def Hom.comp {ξ η ζ : EtaleSmoothLift B S hS ι hι W x hx} (m : Hom ξ η) (n : Hom η ζ) :
    Hom ξ ζ where
  base := m.base ≫ n.base
  ambient := m.ambient ≫ n.ambient
  inclusion_comp := inclusion_comp_comp m n
  comm := m.comm ≫ ((algebraicSpaceStackFunctor B S hS).map m.ambient ◁ n.comm)
  coherence :=
    coherence_comp (left_leg ξ η m.base) (left_leg η ζ n.base)
      (lift_leg ξ η m.base m.ambient m.inclusion_comp)
      (lift_leg η ζ n.base n.ambient n.inclusion_comp)
      (left_leg ξ ζ (m.base ≫ n.base))
      (lift_leg ξ ζ (m.base ≫ n.base) (m.ambient ≫ n.ambient) (inclusion_comp_comp m n))
      ξ.comm.hom η.comm.hom ζ.comm.hom m.comm n.comm m.coherence n.coherence

/-- **The comparison 2-morphism of a composite with an identity on the left.** -/
theorem comm_id_comp {ξ η : EtaleSmoothLift B S hS ι hι W x hx} (m : Hom ξ η) :
    ((Hom.id ξ).comp m).comm = m.comm :=
  have hp := CategoryTheory.Functor.map_id (algebraicSpaceStackFunctor B S hS) ξ.ambient
  have s : (algebraicSpaceStackFunctor B S hS).map (𝟙 ξ.ambient) ◁ m.comm =
      eqToHom (congrArg (· ≫ ξ.ambientMap) hp) ≫ m.comm :=
    ((Bicategory.eqToHom_whiskerLeft_naturality hp m.comm).trans
      (Category.comp_id _)).symm
  (congrArg (fun t => eqToHom (ambientMap_eq_map_id_comp ξ) ≫ t) s).trans
    (((Category.assoc (eqToHom (ambientMap_eq_map_id_comp ξ))
          (eqToHom (congrArg (· ≫ ξ.ambientMap) hp)) m.comm).symm).trans
      ((congrArg (fun t => t ≫ m.comm)
          (eqToHom_trans (ambientMap_eq_map_id_comp ξ)
            (congrArg (· ≫ ξ.ambientMap) hp))).trans (Category.id_comp m.comm)))

/-- **The comparison 2-morphism of a composite with an identity on the right.** -/
theorem comm_comp_id {ξ η : EtaleSmoothLift B S hS ι hι W x hx} (m : Hom ξ η) :
    (m.comp (Hom.id η)).comm = m.comm :=
  (congrArg (fun t => m.comm ≫ t)
    (Bicategory.whiskerLeft_eqToHom ((algebraicSpaceStackFunctor B S hS).map m.ambient)
      (ambientMap_eq_map_id_comp η))).trans (Category.comp_id m.comm)

/-- **The comparison 2-morphisms of the two bracketings of a triple composite agree.** -/
theorem comm_assoc {ξ η ζ ϑ : EtaleSmoothLift B S hS ι hι W x hx} (m : Hom ξ η) (n : Hom η ζ)
    (o : Hom ζ ϑ) : ((m.comp n).comp o).comm = (m.comp (n.comp o)).comm :=
  comp_whiskerLeft_comp_whiskerLeft m.comm n.comm o.comm

/-- **Stacks 0CJP, the category.** The smooth lifts of the étale opens of `W` along the
thickening `ι`, with the morphisms above, their identities and their composition. -/
@[instance_reducible, stacks 0CJP "category"]
instance instCategory : Category (EtaleSmoothLift B S hS ι hι W x hx) where
  Hom ξ η := Hom ξ η
  id ξ := Hom.id ξ
  comp m n := Hom.comp m n
  id_comp m := hom_congr _ _ rfl rfl (heq_of_eq (comm_id_comp m))
  comp_id m := hom_congr _ _ rfl rfl (heq_of_eq (comm_comp_id m))
  assoc m n o := hom_congr _ _ rfl rfl (heq_of_eq (comm_assoc m n o))

/-- **Stacks 0CJP, the projection.** The functor sending a smooth lift to the étale open
`a : U ⟶ W` it lies over and a morphism of smooth lifts to its component `f : U ⟶ V`. -/
@[stacks 0CJP "projection"]
def proj : EtaleSmoothLift B S hS ι hι W x hx ⥤ Space.SpacesEtale B S hS W where
  obj ξ := ξ.base
  map m := Hom.base m
  map_id _ := rfl
  map_comp _ _ := rfl

end EtaleSmoothLift

end AlgebraicGeometry.Stack

end
