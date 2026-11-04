module

import StacksCore.CategoryTheory.FiberedInGroupoidsEquiv
public import StacksCore.CategoryTheory.FiberedInGroupoids
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.Tactic.NormNum.Parity
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Geometry.Euclidean.Altitude
import Mathlib.Data.NNRat.Floor
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.CategoryTheory.FiberedCategory.Cartesian
public import Mathlib.CategoryTheory.FiberedCategory.BasedCategory
public import Mathlib.CategoryTheory.Bicategory.InducedBicategory
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Sheaves.Init
import Mathlib.CategoryTheory.Monoidal.Mon
public import Mathlib.Algebra.Group.End


/-!
# The 2-category of categories fibred in groupoids

Let `𝒞` be a category. The *2-category of categories fibred in groupoids over `𝒞`*
(Stacks 02XS) has as objects the categories over `𝒞` whose structure functor is fibred in
groupoids, as 1-morphisms the functors `G` over `𝒞`, i.e. those with `p' ∘ G = p`, and as
2-morphisms the morphisms of functors `t` with `p'(t_x) = 𝟙 (p x)` for every object `x`.

## Main definitions

* `CategoryTheory.CatFiberedInGroupoids`: the 2-category of categories fibred in groupoids
  over `𝒞`.
* `CategoryTheory.CatFiberedInGroupoids.inclusion`: the inclusion of one full sub-2-category of
  the 2-category of categories over `𝒞` into another, along an implication between the predicates
  cutting them out.

## Main results

* `CategoryTheory.CatFiberedInGroupoids.homEquivBasedFunctor`,
  `CategoryTheory.CatFiberedInGroupoids.homFunctor_comp_p`,
  `CategoryTheory.CatFiberedInGroupoids.homEquivBasedNatTrans` and
  `CategoryTheory.CatFiberedInGroupoids.map_app`: the 1-morphisms are exactly the functors `G` with
  `p' ∘ G = p`, and the 2-morphisms exactly the morphisms of functors `t` with `p'(t_x) = 𝟙 (p x)`.
* `CategoryTheory.CatFiberedInGroupoids.isStronglyCartesian_map`: a 1-morphism automatically
  preserves strongly cartesian morphisms.
* `CategoryTheory.CatFiberedInGroupoids.inclusionFullyFaithful`: such an inclusion is fully
  faithful on 1-morphisms, both sub-2-categories being full.

## Implementation notes

The ambient 2-category of categories over `𝒞` (Stacks 003Y) is Mathlib's
`CategoryTheory.BasedCategory`, a strict bicategory whose 1-morphisms are the `BasedFunctor`s
(a functor together with `BasedFunctor.w : G ⋙ p' = p`) and whose 2-morphisms are the
`BasedNatTrans` (a natural transformation together with `BasedNatTrans.isHomLift'`, saying that
each component lies over an identity). The source's 1-morphisms and 2-morphisms are *all* of
these, so the 2-category below is a full sub-2-category, and it is obtained from Mathlib's full
sub-bicategory construction `CategoryTheory.Bicategory.InducedBicategory` applied to the subtype
of `BasedCategory 𝒞` cut out by `Functor.IsFiberedInGroupoids` (Stacks 003S).

It is spelled as a reducible definition rather than an opaque one so that the whole simp set of
`InducedBicategory`, describing composition, whiskering, the unitors and the associator, applies
to it unchanged.

`CatFiberedInGroupoids.based` is `𝒳.val` under a `@[reducible]` name, so that goals mentioning it
are type-correct at `implicit` transparency. `CatFiberedInGroupoids` is an `abbrev` for an
`InducedBicategory` over a subtype, and `InducedBicategory` is a semireducible `def`, so the raw
projection `𝒳.val` is *not* type-correct at that transparency; `Lean.Meta.kabstract` then declines
to abstract over any subterm of such a goal, and `rw` and `simp only` fail with "did not find an
occurrence" together with a note about the transparency level. Stating a clause with `𝒳.based`
instead of `𝒳.val` keeps the two definitionally equal while letting the ordinary rewriting tactics
work on it.
-/

@[expose] public section

namespace CategoryTheory

universe v₁ v₂ u₁ u₂

variable {𝒞 : Type u₁} [Category.{v₁} 𝒞]

set_option linter.checkUnivs false in
/-- The 2-category of categories fibred in groupoids over `𝒞`: the full sub-2-category of the
2-category `BasedCategory 𝒞` of categories over `𝒞` (Stacks 003Y) spanned by the categories fibred
in groupoids. Explicitly:

1. its objects are the categories `p : 𝒮 ⥤ 𝒞` over `𝒞` that are fibred in groupoids;
2. its 1-morphisms `(𝒮, p) ⟶ (𝒮', p')` are the functors `G : 𝒮 ⥤ 𝒮'` with `p' ∘ G = p`
   (no condition on strongly cartesian morphisms is needed: see
   `CatFiberedInGroupoids.isStronglyCartesian_map`);
3. its 2-morphisms `t : G ⟶ H` are the morphisms of functors with `p'(t_x) = 𝟙 (p x)` for every
   object `x` of `𝒮`. -/
@[stacks 02XS]
abbrev CatFiberedInGroupoids (𝒞 : Type u₁) [Category.{v₁} 𝒞] :=
  Bicategory.InducedBicategory (BasedCategory.{v₂, u₂} 𝒞)
    (Subtype.val (p := fun 𝒳 : BasedCategory.{v₂, u₂} 𝒞 ↦ 𝒳.p.IsFiberedInGroupoids))

namespace CatFiberedInGroupoids

/-- A category over `𝒞` whose structure functor is fibred in groupoids, viewed as an object of
the 2-category of categories fibred in groupoids over `𝒞`. -/
abbrev mk (𝒳 : BasedCategory.{v₂, u₂} 𝒞) (h : 𝒳.p.IsFiberedInGroupoids) :
    CatFiberedInGroupoids.{v₁, v₂, u₁, u₂} 𝒞 :=
  ⟨𝒳, h⟩

/-- The structure functor of an object of the 2-category of categories fibred in groupoids over `𝒞`
is fibred in groupoids. -/
lemma isFiberedInGroupoids (𝒳 : CatFiberedInGroupoids.{v₁, v₂, u₁, u₂} 𝒞) :
    𝒳.val.p.IsFiberedInGroupoids :=
  𝒳.2

/-- The underlying category over `𝒞` of an object of the 2-category of categories fibred in
groupoids. -/
@[reducible]
def based (𝒳 : CatFiberedInGroupoids.{v₁, v₂, u₁, u₂} 𝒞) : BasedCategory.{v₂, u₂} 𝒞 :=
  𝒳.val

section

variable {P : BasedCategory.{v₂, u₂} 𝒞 → Prop}
  {𝒳 𝒴 : Bicategory.InducedBicategory (BasedCategory.{v₂, u₂} 𝒞) (Subtype.val (p := P))}

/-- A 1-morphism `𝒳 ⟶ 𝒴` is precisely a functor `G` between the underlying categories with
`p' ∘ G = p`. -/
def homEquivBasedFunctor
    (𝒳 𝒴 : Bicategory.InducedBicategory (BasedCategory.{v₂, u₂} 𝒞) (Subtype.val (p := P))) :
    (𝒳 ⟶ 𝒴) ≃ (𝒳.val ⥤ᵇ 𝒴.val) where
  toFun G := G.hom
  invFun G := Bicategory.InducedBicategory.mkHom G
  left_inv _ := rfl
  right_inv _ := rfl

/-- The functor `𝒮 ⥤ 𝒮'` underlying a 1-morphism. -/
abbrev homFunctor (G : 𝒳 ⟶ 𝒴) : 𝒳.val.obj ⥤ 𝒴.val.obj :=
  G.hom.toFunctor

/-- The functor underlying a 1-morphism satisfies `p' ∘ G = p`. -/
lemma homFunctor_comp_p (G : 𝒳 ⟶ 𝒴) : homFunctor G ⋙ 𝒴.val.p = 𝒳.val.p :=
  G.hom.w

/-- A 2-morphism `G ⟶ H` is precisely a morphism of the underlying functors all of whose components
lie over an identity of `𝒞`. -/
def homEquivBasedNatTrans (G H : 𝒳 ⟶ 𝒴) : (G ⟶ H) ≃ BasedNatTrans G.hom H.hom where
  toFun t := t.hom
  invFun t := Bicategory.InducedBicategory.Hom₂.mk t
  left_inv _ := rfl
  right_inv _ := rfl

/-- The components of a 2-morphism lie over identities. -/
instance isHomLift_app {G H : 𝒳 ⟶ 𝒴} (t : G ⟶ H) (x : 𝒳.val.obj) :
    𝒴.val.p.IsHomLift (𝟙 (𝒳.val.p.obj x)) (t.hom.toNatTrans.app x) :=
  t.hom.isHomLift' x

/-- The image under `p'` of the component `t_x` of a 2-morphism is the identity of `p(x)`,
transported along the equalities `p'(G x) = p x` and `p'(H x) = p x`. -/
lemma map_app {G H : 𝒳 ⟶ 𝒴} (t : G ⟶ H) (x : 𝒳.val.obj) :
    𝒴.val.p.map (t.hom.toNatTrans.app x) =
      eqToHom (BasedFunctor.w_obj G.hom x) ≫ eqToHom (BasedFunctor.w_obj H.hom x).symm := by
  simpa using IsHomLift.fac' 𝒴.val.p (𝟙 (𝒳.val.p.obj x)) (t.hom.toNatTrans.app x)

end

section

variable {P Q : BasedCategory.{v₂, u₂} 𝒞 → Prop}

/-- The inclusion of one full sub-2-category of the 2-category `BasedCategory 𝒞` of categories over
`𝒞` (Stacks 003Y) into another, along an implication `h` between the two predicates cutting them
out, as a functor on the underlying 1-categories of the two strict bicategories. It is the identity
on the underlying categories over `𝒞` and on the underlying 1-morphisms. -/
@[simps]
def inclusion (h : ∀ 𝒳 : BasedCategory.{v₂, u₂} 𝒞, P 𝒳 → Q 𝒳) :
    Bicategory.InducedBicategory (BasedCategory.{v₂, u₂} 𝒞) (Subtype.val (p := P)) ⥤
      Bicategory.InducedBicategory (BasedCategory.{v₂, u₂} 𝒞) (Subtype.val (p := Q)) where
  obj 𝒳 := ⟨𝒳.val, h 𝒳.val 𝒳.2⟩
  map G := Bicategory.InducedBicategory.mkHom G.hom
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The inclusion of one full sub-2-category of the 2-category of categories over `𝒞` into another
is fully faithful on 1-morphisms. -/
def inclusionFullyFaithful (h : ∀ 𝒳 : BasedCategory.{v₂, u₂} 𝒞, P 𝒳 → Q 𝒳) :
    Functor.FullyFaithful (inclusion h) where
  preimage G := Bicategory.InducedBicategory.mkHom G.hom
  map_preimage _ := rfl
  preimage_map _ := rfl

end

section

variable {𝒳 𝒴 : CatFiberedInGroupoids.{v₁, v₂, u₁, u₂} 𝒞}

/-- The image under a 1-morphism of the 2-category of categories fibred in groupoids of a morphism
lying over `f` is strongly cartesian over `f`; in particular 1-morphisms take strongly cartesian
morphisms to strongly cartesian morphisms. -/
lemma isStronglyCartesian_map (G : 𝒳 ⟶ 𝒴) {R S : 𝒞} {a b : 𝒳.val.obj} (f : R ⟶ S) (φ : a ⟶ b)
    [𝒳.val.p.IsHomLift f φ] : 𝒴.val.p.IsStronglyCartesian f ((homFunctor G).map φ) :=
  have : 𝒴.val.p.IsHomLift f ((homFunctor G).map φ) :=
    BasedFunctor.preserves_isHomLift G.hom f φ
  𝒴.isFiberedInGroupoids.isStronglyCartesian_homLift f _

end

end CatFiberedInGroupoids

end CategoryTheory
