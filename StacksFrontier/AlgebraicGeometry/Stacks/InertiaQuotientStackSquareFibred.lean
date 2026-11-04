module

public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.Quotient.SmoothQuotientStackAlgebraic
public import StacksFrontier.AlgebraicGeometry.Stacks.InertiaPresentationSquare
public import StacksFrontier.AlgebraicGeometry.Stacks.InertiaQuotientStackComparison
public import StacksFrontier.AlgebraicGeometry.Stacks.QuotientStackProjectionRepresentable
public import StacksFrontier.CategoryTheory.TwoFibreProduct.StackInGroupoidsFibred

/-!
# Stacks 06PC: the inertia stack of a quotient stack as a base change

Let `B → S` and let `(U, R, s, t, c)` be a groupoid in algebraic spaces over `B` (Stacks 044Q
(1)), with stabilizer group algebraic space `G/U` (Stacks 0448) and inertia groupoid
`(G, R', s', t', c')` (Stacks 06PB). The canonical diagram

```
𝒮_G  ------>  𝒮_U
 |             |
 v             v
ℐ_{[U/R]} --> [U/R]
```

is 2-cartesian, both in the 2-category of categories fibred in groupoids over the big fppf site
(Stacks 02XS) and in the 2-category of stacks in groupoids over it (Stacks 02ZK). The square of
Stacks 04ZN, and the square with `[G/R']` in place of `ℐ_{[U/R]}`, are 2-cartesian in the
2-category of categories fibred in groupoids.

## Main definitions

* `AlgebraicGeometry.Stack.functorialitySquareFibred`: the square of Stacks 04ZN, read in the
  2-category of categories fibred in groupoids.
* `AlgebraicGeometry.Stack.inertiaQuotientStackSquareFibred`: the square of Stacks 06PC with
  `[G/R']` in the lower-left corner, read in that 2-category.
* `AlgebraicGeometry.Stack.quotientStackInertiaSquare` and
  `AlgebraicGeometry.Stack.quotientStackInertiaSquareInGroupoids`: the canonical diagram of
  Stacks 06PC, with `ℐ_{[U/R]}` in that corner, in the two 2-categories.

## Main results

* `AlgebraicGeometry.Stack.isEquivalence_functorialityComparison`: the comparison 1-morphism of
  Stacks 04ZN is an equivalence of the underlying categories when the source square of the
  morphism of groupoids is cartesian.
* `AlgebraicGeometry.Stack.isTwoFibreProduct_functorialitySquareFibred`: Stacks 04ZN in the
  2-category of categories fibred in groupoids.
* `AlgebraicGeometry.Stack.isTwoFibreProduct_inertiaQuotientStackSquareFibred`: the square of
  Stacks 06PC with `[G/R']` in the lower-left corner is 2-cartesian in that 2-category.
* `AlgebraicGeometry.Stack.isStackInGroupoids_inertiaQuotientStack`: the inertia `ℐ_{[U/R]}` is
  a stack in groupoids over the big fppf site.
* `AlgebraicGeometry.Stack.isTwoFibreProduct_quotientStackInertiaSquare` and
  `AlgebraicGeometry.Stack.isTwoFibreProduct_quotientStackInertiaSquareInGroupoids`:
  Stacks 06PC, the canonical diagram with corners `𝒮_G`, `𝒮_U`, `ℐ_{[U/R]}` and `[U/R]` is
  2-cartesian, in the two 2-categories.

## References

* [Stacks Project, Tag 003O](https://stacks.math.columbia.edu/tag/003O)
* [Stacks Project, Tag 003Q](https://stacks.math.columbia.edu/tag/003Q)
* [Stacks Project, Tag 02XS](https://stacks.math.columbia.edu/tag/02XS)
* [Stacks Project, Tag 02ZK](https://stacks.math.columbia.edu/tag/02ZK)
* [Stacks Project, Tag 0448](https://stacks.math.columbia.edu/tag/0448)
* [Stacks Project, Tag 044Q](https://stacks.math.columbia.edu/tag/044Q)
* [Stacks Project, Tag 04ZN](https://stacks.math.columbia.edu/tag/04ZN)
* [Stacks Project, Tag 06PB](https://stacks.math.columbia.edu/tag/06PB)
* [Stacks Project, Tag 06PC](https://stacks.math.columbia.edu/tag/06PC)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u

open AlgebraicGeometry.GroupoidInAlgebraicSpaces

variable {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
  {B : AlgebraicSpaces C S hS} {G G' : GroupoidInAlgebraicSpaces C S hS B}

/-- For a morphism `φ : (U, R, s, t, c) ⟶ (U', R', s', t', c')` of groupoids in algebraic spaces
whose source square is cartesian, the comparison 1-morphism
`AlgebraicGeometry.Stack.functorialityComparison` from `𝒮_U` to the 2-fibre product
`[U/R] ×_{[U'/R']} 𝒮_{U'}` of Stacks 0040 is an equivalence of the underlying categories. -/
theorem isEquivalence_functorialityComparison (φ : Hom G G')
    (hφ : IsPullback φ.toGroupoidHom.mapArrows G.source.hom G'.source.hom
      φ.toGroupoidHom.mapObjects) :
    (functorialityComparison φ).IsEquivalence := by
  have := functorialityComparison_full φ hφ
  have := functorialityComparison_faithful φ
  have : (liftedFibredCategory G.objects).p.IsFibered :=
    (liftedFibredCategory_isStack G.objects).isFibered
  obtain ⟨hequiv⟩ := isEquivalenceOver_functorialityTwoFibreProduct φ
    (liftedFibredCategory_isStack G.objects).hasEffectiveDescent
    (isFibredOneMorphism_functorialityComparison φ)
    (locallyEssSurjOnFibers_functorialityComparison φ hφ)
  exact (CategoryTheory.Equivalence.mk (functorialityComparison φ) hequiv.inv
    hequiv.unitIso.symm hequiv.counitIso).isEquivalence_functor

/-- For a morphism `φ : (U, R, s, t, c) ⟶ (U', R', s', t', c')` of groupoids in algebraic spaces
over `B`, the 2-commutative square

```
𝒮_U ----π----> [U/R]
 |              |
𝒮_f            [φ]
 v              v
𝒮_{U'} --π'--> [U'/R']
```

of the projections of Stacks 044R, the induced 1-morphism of Stacks 046Q and the 1-morphism of
Stacks 0458, with every corner read as a category fibred in groupoids over the big fppf site. -/
noncomputable def functorialitySquareFibred (φ : Hom G G') :
    Bicategory.TwoCommSq
      (Bicategory.InducedBicategory.mkHom (quotientStackMap φ) :
        quotientStackCFG C S hS G ⟶ quotientStackCFG C S hS G')
      (Bicategory.InducedBicategory.mkHom (liftedQuotientStackProjection G') :
        liftedSpaceStack G'.objects ⟶ quotientStackCFG C S hS G') where
  pt := liftedSpaceStack G.objects
  fst := Bicategory.InducedBicategory.mkHom (liftedQuotientStackProjection G)
  snd := Bicategory.InducedBicategory.mkHom (liftedAssociatedMap φ.objectsMap)
  iso := Bicategory.InducedBicategory.isoMk
    (BasedNatIso.mkNatIso (functorialityProjectionCellLifted φ)
      (functorialityProjectionCellLifted_isHomLift φ))

/-- If the square formed by the two source maps of a morphism `φ` of groupoids in algebraic spaces
is cartesian, then `AlgebraicGeometry.Stack.functorialitySquareFibred` is a 2-fibre product
(Stacks 003Q) in the 2-category of categories fibred in groupoids over the big fppf site. -/
noncomputable def isTwoFibreProduct_functorialitySquareFibred (φ : Hom G G')
    (hφ : IsPullback φ.toGroupoidHom.mapArrows G.source.hom G'.source.hom
      φ.toGroupoidHom.mapObjects) :
    Bicategory.IsTwoFibreProduct (functorialitySquareFibred φ) :=
  Bicategory.isTwoFibreProduct_of_isEquivalence_to
    (CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u + 1, u + 1, u + 1} _ _)
    (CatFiberedInGroupoids.preHomTwoFibreProductSquare.{u, u + 1, u + 1, u + 1} _ _
      (functorialitySquareFibred φ))
    (isEquivalence_functorialityComparison φ hφ)

/-- For a groupoid `(U, R, s, t, c)` in algebraic spaces over `B` with stabilizer group algebraic
space `G/U` (Stacks 0448) and inertia groupoid `(G, R', s', t', c')` (Stacks 06PB), the
2-commutative square of categories fibred in groupoids over the big fppf site

```
𝒮_G  ------>  𝒮_U
 |             |
 v             v
[G/R'] ----> [U/R]
```

read over the cospan `[G/R'] ⟶ [U/R] ⟵ 𝒮_U`, so that its first leg is `𝒮_G ⟶ [G/R']`. It is the
functoriality square of the forgetful morphism
`AlgebraicGeometry.GroupoidInAlgebraicSpaces.inertiaForgetful` of the inertia groupoid. -/
noncomputable abbrev inertiaQuotientStackSquareFibred
    (G : GroupoidInAlgebraicSpaces C S hS B) :
    Bicategory.TwoCommSq
      (Bicategory.InducedBicategory.mkHom (quotientStackMap (inertiaForgetful G)) :
        quotientStackCFG C S hS (inertiaGroupoid G) ⟶ quotientStackCFG C S hS G)
      (Bicategory.InducedBicategory.mkHom (liftedQuotientStackProjection G) :
        liftedSpaceStack G.objects ⟶ quotientStackCFG C S hS G) :=
  functorialitySquareFibred (inertiaForgetful G)

/-- The square

```
𝒮_G  ------>  𝒮_U
 |             |
 v             v
[G/R'] ----> [U/R]
```

of `AlgebraicGeometry.Stack.inertiaQuotientStackSquareFibred` is a 2-fibre product (Stacks 003Q)
of categories fibred in groupoids over the big fppf site. -/
noncomputable def isTwoFibreProduct_inertiaQuotientStackSquareFibred
    (G : GroupoidInAlgebraicSpaces C S hS B) :
    Bicategory.IsTwoFibreProduct (inertiaQuotientStackSquareFibred G) :=
  isTwoFibreProduct_functorialitySquareFibred (inertiaForgetful G)
    (isPullback_inertiaForgetful_source G)

/-! ### Stacks 06PC -/

/-- The inertia `ℐ_{[U/R]}` of the quotient stack `[U/R]` of a groupoid in algebraic spaces is a
stack in groupoids over the big fppf site (Stacks 02ZI). -/
theorem isStackInGroupoids_inertiaQuotientStack
    (G : GroupoidInAlgebraicSpaces C S hS B) :
    (RelativeInertia.toBase (quotientStack G).p).IsStackInGroupoids
      (BigFppfOver.topology C S hS) :=
  (inertiaQuotient_isStack G).isStackInGroupoids (inertiaQuotient_isFiberedInGroupoids G)

/-- For `B → S` and a groupoid `(U, R, s, t, c)` in algebraic spaces over `B` (Stacks 044Q (1))
with stabilizer group algebraic space `G/U` (Stacks 0448), the canonical 2-commutative square of
Stacks 06PC

```
𝒮_G  ------>  𝒮_U
 |             |
 v             v
ℐ_{[U/R]} --> [U/R]
```

over the cospan `ℐ_{[U/R]} ⟶ [U/R] ⟵ 𝒮_U`. Its bottom arrow is the forgetful 1-morphism
`ℐ_{[U/R]} ⟶ [U/R]`, `(x, α) ↦ x`; its right arrow is the projection of Stacks 044R; its top
arrow `𝒮_G ⟶ 𝒮_U` is the 1-morphism of Stacks 0458 induced by the structure morphism `G → U`
of the stabilizer; and its left arrow `𝒮_G ⟶ ℐ_{[U/R]}` is the projection of Stacks 044R for the
inertia groupoid `(G, R', s', t', c')` of Stacks 06PB followed by the comparison
`[G/R'] ⟶ ℐ_{[U/R]}` of the second assertion of Stacks 06PB. -/
noncomputable def quotientStackInertiaSquare (G : GroupoidInAlgebraicSpaces C S hS B) :
    Bicategory.TwoCommSq (inertiaCatProjection C S hS (quotientStackCFG C S hS G))
      (Bicategory.InducedBicategory.mkHom (liftedQuotientStackProjection G) :
        liftedSpaceStack G.objects ⟶ quotientStackCFG C S hS G) :=
  precomposeFstSquare C S hS _ _ (inertiaQuotientStackCompare G)
    ((inertiaQuotientStackSquareFibred G).reindexFst
      (inertiaQuotientStackCompareOver G).symm)

/-- The apex of the diagram of Stacks 06PC is the stack `𝒮_G` of the stabilizer group algebraic
space `G/U` of Stacks 0448. -/
theorem quotientStackInertiaSquare_pt (G : GroupoidInAlgebraicSpaces C S hS B) :
    (quotientStackInertiaSquare G).pt =
      liftedSpaceStack (GroupoidInAlgebraicSpaces.stabilizerOverBase G) := rfl

/-- The second leg of the diagram of Stacks 06PC is the top arrow `𝒮_G ⟶ 𝒮_U`, the 1-morphism of
Stacks 0458 induced by the structure morphism `G → U` of the stabilizer. -/
theorem quotientStackInertiaSquare_snd (G : GroupoidInAlgebraicSpaces C S hS B) :
    (quotientStackInertiaSquare G).snd =
      Bicategory.InducedBicategory.mkHom
        (liftedAssociatedMap (inertiaForgetful G).objectsMap) := rfl

/-- The first leg of the diagram of Stacks 06PC is the left arrow `𝒮_G ⟶ ℐ_{[U/R]}`, the
composite of the projection of Stacks 044R for the inertia groupoid of Stacks 06PB with the
comparison `[G/R'] ⟶ ℐ_{[U/R]}` of the second assertion of Stacks 06PB. -/
theorem quotientStackInertiaSquare_fst (G : GroupoidInAlgebraicSpaces C S hS B) :
    (quotientStackInertiaSquare G).fst =
      Bicategory.InducedBicategory.mkHom
          (liftedQuotientStackProjection (inertiaGroupoid G)) ≫
        inertiaQuotientStackCompare G := rfl

/-- Assume `B → S` and `(U, R, s, t, c)` as in Stacks 044Q (1). Let `G/U` be the stabilizer group
algebraic space of the groupoid `(U, R, s, t, c, e, i)` (Stacks 0448). Then the canonical diagram

```
𝒮_G  ------>  𝒮_U
 |             |
 v             v
ℐ_{[U/R]} --> [U/R]
```

of `AlgebraicGeometry.Stack.quotientStackInertiaSquare` is 2-cartesian, i.e. a 2-fibre product
in the sense of Stacks 003Q, in the 2-category of categories fibred in groupoids over the big fppf
site (Stacks 02XS). -/
@[stacks 06PC "the canonical square with corners S_G, S_U, I_[U/R], [U/R] is 2-cartesian"]
noncomputable def isTwoFibreProduct_quotientStackInertiaSquare
    (G : GroupoidInAlgebraicSpaces C S hS B) :
    Bicategory.IsTwoFibreProduct (quotientStackInertiaSquare G) :=
  isTwoFibreProduct_precomposeFstSquare C S hS _ _ (inertiaQuotientStackCompare G)
    (isEquivalence_inertiaQuotientStackCompare G) _
    (Bicategory.isTwoFibreProduct_reindexFst (inertiaQuotientStackCompareOver G).symm
      (isTwoFibreProduct_inertiaQuotientStackSquareFibred G))

/-! ### Stacks 06PC in the 2-category of stacks in groupoids -/

section StacksInGroupoids

attribute [local implicit_reducible] StackInGroupoids.bicategory
  Bicategory.InducedBicategory Bicategory.InducedBicategory.bicategory
  Bicategory.InducedBicategory.isoMk Bicategory.InducedBicategory.isoHom
  Bicategory.TwoCommSq.underlying

/-- The inertia stack `ℐ_{[U/R]}` of the quotient stack of a groupoid in algebraic spaces, as an
object of the 2-category of stacks in groupoids over the big fppf site (Stacks 02ZK). Its
underlying category over the site is `AlgebraicGeometry.Stack.inertia` of the quotient stack. -/
noncomputable abbrev quotientStackInertiaInGroupoids
    (G : GroupoidInAlgebraicSpaces C S hS B) :
    StackInGroupoids (BigFppfOver C S hS) (BigFppfOver.topology C S hS) :=
  ⟨(inertia C S hS (quotientStackCFG C S hS G)).val,
    isStackInGroupoids_inertiaQuotientStack G⟩

/-- The canonical diagram of Stacks 06PC in the 2-category of stacks in groupoids over the big
fppf site (Stacks 02ZK): the corners, legs and filler of
`AlgebraicGeometry.Stack.quotientStackInertiaSquare`, each read as a stack in groupoids or as a
1-morphism or 2-morphism of them. -/
noncomputable def quotientStackInertiaSquareInGroupoids
    (G : GroupoidInAlgebraicSpaces C S hS B) :
    Bicategory.TwoCommSq
      (Bicategory.InducedBicategory.mkHom
        (inertiaCatProjection C S hS (quotientStackCFG C S hS G)).hom :
          quotientStackInertiaInGroupoids G ⟶ quotientStackInGroupoids G)
      (Bicategory.InducedBicategory.mkHom (liftedQuotientStackProjection G) :
        liftedFibredCategoryInGroupoids G.objects ⟶ quotientStackInGroupoids G) where
  pt := liftedFibredCategoryInGroupoids (GroupoidInAlgebraicSpaces.stabilizerOverBase G)
  fst := Bicategory.InducedBicategory.mkHom (quotientStackInertiaSquare G).fst.hom
  snd := Bicategory.InducedBicategory.mkHom (quotientStackInertiaSquare G).snd.hom
  iso := Bicategory.InducedBicategory.isoMk
    (Bicategory.InducedBicategory.isoHom
      (f := (quotientStackInertiaSquare G).fst ≫
        inertiaCatProjection C S hS (quotientStackCFG C S hS G))
      (g := (quotientStackInertiaSquare G).snd ≫
        Bicategory.InducedBicategory.mkHom (liftedQuotientStackProjection G))
      (quotientStackInertiaSquare G).iso)

/-- Assume `B → S` and `(U, R, s, t, c)` as in Stacks 044Q (1) and let `G/U` be the stabilizer
group algebraic space of `(U, R, s, t, c, e, i)` (Stacks 0448). Then the canonical diagram

```
𝒮_G  ------>  𝒮_U
 |             |
 v             v
ℐ_{[U/R]} --> [U/R]
```

is 2-cartesian in the 2-category of stacks in groupoids over the big fppf site (Stacks 02ZK). -/
@[stacks 06PC "that square, in the 2-category of stacks in groupoids, is 2-cartesian"]
noncomputable def isTwoFibreProduct_quotientStackInertiaSquareInGroupoids
    (G : GroupoidInAlgebraicSpaces C S hS B) :
    Bicategory.IsTwoFibreProduct (quotientStackInertiaSquareInGroupoids G) :=
  StackInGroupoids.isTwoFibreProduct_of_toFibred
    (isTwoFibreProduct_quotientStackInertiaSquare G)

end StacksInGroupoids

end AlgebraicGeometry.Stack

end
