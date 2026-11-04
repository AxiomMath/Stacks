module

public import StacksFrontier.CategoryTheory.Adjunction.BaseChangeSquare
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.CompositionOfToposHom
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPushforward.DerivedAdjunctionOfToposHom
public import StacksCore.Tactic.StacksAttribute

/-!
# The derived base change map of a commutative square of morphisms of ringed topoi

Let

```
                g'
  (Sh(C'), 𝒪_{C'}) --→ (Sh(C), 𝒪_C)
        |  f'                |  f
        v                    v
  (Sh(D'), 𝒪_{D'}) --→ (Sh(D), 𝒪_D)
                g
```

be a commutative diagram of ringed topoi and let `K` be an object of the unbounded derived
category `D(𝒪_C)`. There is a canonical base change map

`Lg^* Rf_* K ⟶ Rf'_* L(g')^* K`

in `D(𝒪_{D'})`. It is adjoint, under the derived adjunction `L(f')^* ⊣ Rf'_*`, to a map
`L(f')^* Lg^* Rf_* K ⟶ L(g')^* K`, and since `L(f')^* ∘ Lg^* = L(g')^* ∘ Lf^*` — both being the
derived pullback along the common composite of the square — that is the same as a map
`L(g')^* Lf^* Rf_* K ⟶ L(g')^* K`, which is taken to be `L(g')^*` of the derived counit
`Lf^* Rf_* K ⟶ K`.

The four arrows of the square are morphisms of ringed topoi in the two-field sense of Stacks
01D3, part (2) — a morphism of the underlying *topoi* together with a map of structure sheaves,
with no continuous functor between the underlying sites — and there is no hypothesis on them
beyond those which make the four categories of modules and their derived categories exist. The
twelve universes of the four ringed topoi are free and unrelated.

## Main definitions

* `derivedPullbackCompIsoLeft` identifies the iterated derived pullback `Lg^* ⋙ L(f')^*`, down
  the left and along the bottom of the square, with the derived pullback along the common
  composite.
* `derivedPullbackCompIsoRight` does the same for `Lf^* ⋙ L(g')^*`, along the top and down the
  right.
* `derivedBaseChangeSquare` is the canonical base change morphism of functors
  `Rf_* ⋙ Lg^* ⟶ L(g')^* ⋙ Rf'_*`.
* `derivedBaseChangeMap` is its component at an object of `D(𝒪_C)`, the derived base change
  map.

## Main results

* `derivedBaseChangeMap_adjoint`: the adjunct of the base change map under `L(f')^* ⊣ Rf'_*` is
  `L(g')^*` of the derived counit.
* `derivedBaseChangeMap_eq`: the same equation read as a formula for the map.
* `derivedBaseChangeMap_naturality`: the base change map is natural in the object of `D(𝒪_C)`.

## References

* [Stacks Project, Tag 07A7](https://stacks.math.columbia.edu/tag/07A7)
* [Stacks Project, Tag 07A6](https://stacks.math.columbia.edu/tag/07A6)
* [Stacks Project, Tag 0D6D](https://stacks.math.columbia.edu/tag/0D6D)
* [Stacks Project, Tag 06YY](https://stacks.math.columbia.edu/tag/06YY)
* [Stacks Project, Tag 07A5](https://stacks.math.columbia.edu/tag/07A5)
* [Stacks Project, Tag 01D3](https://stacks.math.columbia.edu/tag/01D3)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.Cohomology.DerivedPushforward
open Stacks.Cohomology.DerivedPullbackOfToposHom
open Stacks.Cohomology.DerivedPullbackCompositionOfToposHom

namespace Stacks.Cohomology.DerivedBaseChangeOfToposHom

universe vC' uC' wC' vC uC wC vD' uD' wD' vD uD wD

attribute [local instance 10000] HasDerivedCategory.standard

attribute [local instance]
  Stacks.Cohomology.DerivedPullbackOfToposHom.hasLeftDerivedFunctor_pullbackOnHomotopy

noncomputable section

section Congr

variable {X' : RingedTopos.{vC', uC', wC'}} {Y : RingedTopos.{vD, uD, wD}}
  [X'.J.HasSheafCompose (forget RingCat.{wC'})] [Y.J.HasSheafCompose (forget RingCat.{wD})]
  [X'.J.HasSheafCompose (forget₂ CommRingCat.{wC'} RingCat.{wC'})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{wD} RingCat.{wD})]
  [X'.J.HasSheafCompose (forget AddCommGrpCat.{wC'})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{wD})]
  [HasSheafify X'.J AddCommGrpCat.{wC'}] [X'.J.WEqualsLocallyBijective AddCommGrpCat.{wC'}]
  [HasSheafify Y.J AddCommGrpCat.{wD}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{wD}]
  [HasSheafify X'.J (Type wC')] [HasSheafify Y.J (Type wD)]

/-- Equal morphisms of ringed topoi have isomorphic derived pullbacks. -/
def derivedPullbackCongr {m₁ m₂ : RingedToposHom X' Y} (h : m₁ = m₂) :
    derivedPullback m₁ ≅ derivedPullback m₂ := by
  subst h
  exact Iso.refl _

end Congr

section Square

variable {X' : RingedTopos.{vC', uC', wC'}} {X : RingedTopos.{vC, uC, wC}}
  {Y' : RingedTopos.{vD', uD', wD'}} {Y : RingedTopos.{vD, uD, wD}}
  [X'.J.HasSheafCompose (forget RingCat.{wC'})] [X.J.HasSheafCompose (forget RingCat.{wC})]
  [Y'.J.HasSheafCompose (forget RingCat.{wD'})] [Y.J.HasSheafCompose (forget RingCat.{wD})]
  [X'.J.HasSheafCompose (forget₂ CommRingCat.{wC'} RingCat.{wC'})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{wC} RingCat.{wC})]
  [Y'.J.HasSheafCompose (forget₂ CommRingCat.{wD'} RingCat.{wD'})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{wD} RingCat.{wD})]
  [X'.J.HasSheafCompose (forget AddCommGrpCat.{wC'})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{wC})]
  [Y'.J.HasSheafCompose (forget AddCommGrpCat.{wD'})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{wD})]
  [HasSheafify X'.J AddCommGrpCat.{wC'}] [X'.J.WEqualsLocallyBijective AddCommGrpCat.{wC'}]
  [HasSheafify X.J AddCommGrpCat.{wC}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{wC}]
  [HasSheafify Y'.J AddCommGrpCat.{wD'}] [Y'.J.WEqualsLocallyBijective AddCommGrpCat.{wD'}]
  [HasSheafify Y.J AddCommGrpCat.{wD}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{wD}]
  [HasSheafify X'.J (Type wC')] [HasSheafify X.J (Type wC)]
  [HasSheafify Y'.J (Type wD')] [HasSheafify Y.J (Type wD)]
  [IsGrothendieckAbelian.{wC}
    (SheafOfModules.{wC} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J)) X.O))]
  [IsGrothendieckAbelian.{wC'}
    (SheafOfModules.{wC'} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X'.J)) X'.O))]
  (f : RingedToposHom X Y) (g' : RingedToposHom X' X)
  (f' : RingedToposHom X' Y') (g : RingedToposHom Y' Y)

/-- The iterated derived pullback `Lg^* ⋙ L(f')^*`, down the left and along the bottom of the
square, identified with the derived pullback along the composite `g ∘ f'`. -/
def derivedPullbackCompIsoLeft :
    derivedPullback g ⋙ derivedPullback f' ≅ derivedPullback (g.comp f') :=
  derivedPullbackCompIso f' g

/-- The iterated derived pullback `Lf^* ⋙ L(g')^*`, along the top and down the right of the
square, identified with the derived pullback along the composite `g ∘ f'` using the
commutativity of the square. -/
def derivedPullbackCompIsoRight (h : g.comp f' = f.comp g') :
    derivedPullback f ⋙ derivedPullback g' ≅ derivedPullback (g.comp f') :=
  derivedPullbackCompIso g' f ≪≫ derivedPullbackCongr h.symm

/-- **The derived base change morphism of functors** `Rf_* ⋙ Lg^* ⟶ L(g')^* ⋙ Rf'_*` attached to
a commutative square of morphisms of ringed topoi: the mate, under the derived adjunctions, of
the comparison of the two iterated derived pullbacks around the square. -/
def derivedBaseChangeSquare (h : g.comp f' = f.comp g') :
    TwoSquare (derivedPushforward f) (derivedPullback g') (derivedPullback g)
      (derivedPushforward f') :=
  Stacks.CategoryTheory.BaseChange.twoSquare (derivedAdjunction f) (derivedAdjunction f')
    (derivedPullbackCompIsoLeft f' g) (derivedPullbackCompIsoRight f g' f' g h)

/-- For a commutative square of morphisms of ringed topoi

```
                g'
  (Sh(C'), 𝒪_{C'}) --→ (Sh(C), 𝒪_C)
        |  f'                |  f
        v                    v
  (Sh(D'), 𝒪_{D'}) --→ (Sh(D), 𝒪_D)
                g
```

and an object `K` of the unbounded derived category `D(𝒪_C)`, the canonical base change map

`Lg^* Rf_* K ⟶ Rf'_* L(g')^* K`

in `D(𝒪_{D'})`. -/
@[stacks 07A7 "the canonical derived base change map `Lg^* Rf_* K ⟶ Rf'_* L(g')^* K` of a
commutative square of morphisms of ringed topoi in the two-field sense of Tag 01D3, part (2) --
a morphism of the underlying topoi together with the map of structure sheaves, with no continuous
functor between the underlying sites -- at the twelve free universes of the four ringed topoi",
  sga "6 IV 3.1.0"]
def derivedBaseChangeMap (h : g.comp f' = f.comp g')
    (K : DerivedCategory
      (SheafOfModules.{wC} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J)) X.O))) :
    (derivedPullback g).obj ((derivedPushforward f).obj K) ⟶
      (derivedPushforward f').obj ((derivedPullback g').obj K) :=
  Stacks.CategoryTheory.BaseChange.map (derivedAdjunction f) (derivedAdjunction f')
    (derivedPullbackCompIsoLeft f' g) (derivedPullbackCompIsoRight f g' f' g h) K

/-- **The adjoint characterization of the base change map.** Under the derived adjunction
`L(f')^* ⊣ Rf'_*`, the base change map of a commutative square of morphisms of ringed topoi is
`L(g')^*` of the derived counit `Lf^* Rf_* K ⟶ K`, transported across the two composition
isomorphisms. -/
@[simp, stacks 07A7 "the adjoint characterization which the source gives of the base change map
of a commutative square of morphisms of ringed topoi in the two-field sense of Tag 01D3,
part (2), and which pins the map down: its adjunct under `L(f')^* ⊣ Rf'_*` is `L(g')^*` of the
derived counit, across the two composition isomorphisms of Tag 0D6D"]
theorem derivedBaseChangeMap_adjoint (h : g.comp f' = f.comp g')
    (K : DerivedCategory
      (SheafOfModules.{wC} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J)) X.O))) :
    ((derivedAdjunction f').homEquiv
        ((derivedPullback g).obj ((derivedPushforward f).obj K))
        ((derivedPullback g').obj K)).symm
        (derivedBaseChangeMap f g' f' g h K) =
      (derivedPullbackCompIsoLeft f' g).hom.app ((derivedPushforward f).obj K) ≫
        (derivedPullbackCompIsoRight f g' f' g h).inv.app ((derivedPushforward f).obj K) ≫
        (derivedPullback g').map ((derivedAdjunction f).counit.app K) :=
  Stacks.CategoryTheory.BaseChange.homEquiv_symm_map (derivedAdjunction f) (derivedAdjunction f')
    (derivedPullbackCompIsoLeft f' g) (derivedPullbackCompIsoRight f g' f' g h) K

/-- The base change map is the transpose, under `L(f')^* ⊣ Rf'_*`, of the derived pullback
along `g'` of the derived counit. -/
theorem derivedBaseChangeMap_eq (h : g.comp f' = f.comp g')
    (K : DerivedCategory
      (SheafOfModules.{wC} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J)) X.O))) :
    derivedBaseChangeMap f g' f' g h K =
      (derivedAdjunction f').homEquiv
        ((derivedPullback g).obj ((derivedPushforward f).obj K))
        ((derivedPullback g').obj K)
        ((derivedPullbackCompIsoLeft f' g).hom.app ((derivedPushforward f).obj K) ≫
          (derivedPullbackCompIsoRight f g' f' g h).inv.app ((derivedPushforward f).obj K) ≫
          (derivedPullback g').map ((derivedAdjunction f).counit.app K)) :=
  Stacks.CategoryTheory.BaseChange.map_eq (derivedAdjunction f) (derivedAdjunction f')
    (derivedPullbackCompIsoLeft f' g) (derivedPullbackCompIsoRight f g' f' g h) K

/-- The base change map is natural in the object of `D(𝒪_C)`. -/
theorem derivedBaseChangeMap_naturality (h : g.comp f' = f.comp g')
    {K L : DerivedCategory
      (SheafOfModules.{wC} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J)) X.O))}
    (e : K ⟶ L) :
    (derivedPullback g).map ((derivedPushforward f).map e) ≫
        derivedBaseChangeMap f g' f' g h L =
      derivedBaseChangeMap f g' f' g h K ≫
        (derivedPushforward f').map ((derivedPullback g').map e) :=
  Stacks.CategoryTheory.BaseChange.map_naturality (derivedAdjunction f) (derivedAdjunction f')
    (derivedPullbackCompIsoLeft f' g) (derivedPullbackCompIsoRight f g' f' g h) e

end Square

end

end Stacks.Cohomology.DerivedBaseChangeOfToposHom

end
