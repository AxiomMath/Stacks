module

public import StacksFrontier.CategoryTheory.Adjunction.BaseChangeSquare
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.CompositionOnRingedTopoi
public import StacksCore.Tactic.StacksAttribute

/-!
# The derived base change map for a commutative square of ringed topoi

Let

```
                g'
  (Sh(C'), 𝒪_{C'}) --→ (Sh(C), 𝒪_C)
        |  f'                |  f
        v                    v
  (Sh(D'), 𝒪_{D'}) --→ (Sh(D), 𝒪_D)
                g
```

be a commutative diagram of ringed topoi whose morphisms are induced by morphisms of sites, and
let `K` be an object of the unbounded derived category `D(𝒪_C)`. There is a canonical base
change map

`Lg^* Rf_* K ⟶ Rf'_* L(g')^* K`

in `D(𝒪_{D'})`. It is adjoint, under the derived adjunction `L(f')^* ⊣ Rf'_*`, to a map
`L(f')^* Lg^* Rf_* K ⟶ L(g')^* K`, and since `L(f')^* ∘ Lg^* = L(g')^* ∘ Lf^*` — both being the
derived pullback along the common composite of the square — that is the same as a map
`L(g')^* Lf^* Rf_* K ⟶ L(g')^* K`, which is taken to be `L(g')^*` of the derived counit
`Lf^* Rf_* K ⟶ K`.

## Main definitions

* `derivedPullbackCompIsoLeft` identifies the iterated derived pullback `Lg^* ⋙ L(f')^*`, down
  the left and along the bottom of the square, with the derived pullback along the common
  composite.
* `derivedBaseChangeSquare` is the canonical base change morphism of functors
  `Rf_* ⋙ Lg^* ⟶ L(g')^* ⋙ Rf'_*`.
* `derivedBaseChangeMap` is its component at an object of `D(𝒪_C)`, which is the derived base
  change map of the square.

## Main results

* `derivedBaseChangeMap_adjoint`: under `L(f')^* ⊣ Rf'_*`, the base change map corresponds to
  `L(g')^*` of the derived counit `Lf^* Rf_* K ⟶ K`.
* `derivedBaseChangeMap_eq`: the base change map is the transpose of that composite.
* `derivedBaseChangeMap_naturality`: the base change map is natural in the object of `D(𝒪_C)`.

## Implementation notes

The derived pullback along a morphism of ringed topoi takes a `HasLeftDerivedFunctor` instance
argument depending on the morphism, so equal morphisms have their derived pullbacks identified by
`derivedPullbackCongr` rather than by an `eqToIso`.

## References

* [Stacks Project, Tag 07A7](https://stacks.math.columbia.edu/tag/07A7)
* [Stacks Project, Tag 07A6](https://stacks.math.columbia.edu/tag/07A6)
* [Stacks Project, Tag 0D6D](https://stacks.math.columbia.edu/tag/0D6D)
* [Stacks Project, Tag 06YY](https://stacks.math.columbia.edu/tag/06YY)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open Stacks.Cohomology.DerivedPullbackPushforwardAdjunction
open Stacks.Cohomology.DerivedPullbackCompositionOnTopoi
open Stacks.Cohomology.DerivedPullbackOnRingedTopoi

namespace Stacks.Cohomology.DerivedBaseChangeOnTopoi

universe u

attribute [local instance] HasDerivedCategory.standard

noncomputable section

section Congr

variable {X Y : RingedTopos.{u, u, u}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify Y.J AddCommGrpCat.{u}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- Equal morphisms of ringed topoi have isomorphic derived pullbacks. -/
def derivedPullbackCongr {m₁ m₂ : RingedToposSiteHom X Y} (h : m₁ = m₂)
    [(pullbackOnHomotopy m₁).HasLeftDerivedFunctor
      (HomotopyCategory.quasiIso (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
        (ComplexShape.up ℤ))]
    [(pullbackOnHomotopy m₂).HasLeftDerivedFunctor
      (HomotopyCategory.quasiIso (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
        (ComplexShape.up ℤ))] :
    derivedPullback m₁ ≅ derivedPullback m₂ := by
  subst h
  exact Iso.refl _

end Congr

section Square

variable {X' X Y' Y : RingedTopos.{u, u, u}}
  [X'.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y'.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [HasSheafify X'.J AddCommGrpCat.{u}] [X'.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify Y'.J AddCommGrpCat.{u}] [Y'.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify Y.J AddCommGrpCat.{u}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  (f : RingedToposSiteHom X Y) (g' : RingedToposSiteHom X' X)
  (f' : RingedToposSiteHom X' Y') (g : RingedToposSiteHom Y' Y)
  [(pullbackOnHomotopy f).HasLeftDerivedFunctor
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
      (ComplexShape.up ℤ))]
  [(pullbackOnHomotopy g').HasLeftDerivedFunctor
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
      (ComplexShape.up ℤ))]
  [(pullbackOnHomotopy f').HasLeftDerivedFunctor
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y'.O))
      (ComplexShape.up ℤ))]
  [(pullbackOnHomotopy g).HasLeftDerivedFunctor
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
      (ComplexShape.up ℤ))]
  [(pullbackOnHomotopy (g.comp f')).HasLeftDerivedFunctor
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
      (ComplexShape.up ℤ))]
  [(pullbackOnHomotopy (f.comp g')).HasLeftDerivedFunctor
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
      (ComplexShape.up ℤ))]

/-- The iterated derived pullback `Lg^* ⋙ L(f')^*`, down the left and along the bottom of the
square, identified with the derived pullback along the composite `g ∘ f'`. -/
def derivedPullbackCompIsoLeft (hmosf' : f'.u.IsMorphismOfSites Y'.J X'.J)
    (hmosg : g.u.IsMorphismOfSites Y.J Y'.J) :
    derivedPullback g ⋙ derivedPullback f' ≅ derivedPullback (g.comp f') :=
  derivedPullbackCompIso f' g hmosf' hmosg

/-- The iterated derived pullback `Lf^* ⋙ L(g')^*`, along the top and down the right of the
square, identified with the derived pullback along the composite `g ∘ f'` through the
commutativity `g ∘ f' = f ∘ g'` of the square. -/
def derivedPullbackCompIsoRight (hmosf : f.u.IsMorphismOfSites Y.J X.J)
    (hmosg' : g'.u.IsMorphismOfSites X.J X'.J) (h : g.comp f' = f.comp g') :
    derivedPullback f ⋙ derivedPullback g' ≅ derivedPullback (g.comp f') :=
  derivedPullbackCompIso g' f hmosg' hmosf ≪≫ derivedPullbackCongr h.symm

/-- The derived base change morphism of functors `Rf_* ⋙ Lg^* ⟶ L(g')^* ⋙ Rf'_*` attached to a
commutative square of ringed topoi: the mate, under the derived adjunctions of Stacks 07A6, of
the comparison of the two iterated derived pullbacks around the square. -/
def derivedBaseChangeSquare (hmosf : f.u.IsMorphismOfSites Y.J X.J)
    (hmosg' : g'.u.IsMorphismOfSites X.J X'.J) (hmosf' : f'.u.IsMorphismOfSites Y'.J X'.J)
    (hmosg : g.u.IsMorphismOfSites Y.J Y'.J) (h : g.comp f' = f.comp g') :
    TwoSquare (derivedPushforward f) (derivedPullback g') (derivedPullback g)
      (derivedPushforward f') :=
  Stacks.CategoryTheory.BaseChange.twoSquare (derivedAdjunction f hmosf)
    (derivedAdjunction f' hmosf') (derivedPullbackCompIsoLeft f' g hmosf' hmosg)
    (derivedPullbackCompIsoRight f g' f' g hmosf hmosg' h)

/-- The canonical derived base change map `Lg^* Rf_* K ⟶ Rf'_* L(g')^* K` of a commutative
square of ringed topoi, at an object `K` of the unbounded derived category of `𝒪_C`-modules. -/
@[sga "4 XVII 4.1.5" "site-induced morphisms",
  sga "4 XVII 4.1.4"]
def derivedBaseChangeMap (hmosf : f.u.IsMorphismOfSites Y.J X.J)
    (hmosg' : g'.u.IsMorphismOfSites X.J X'.J) (hmosf' : f'.u.IsMorphismOfSites Y'.J X'.J)
    (hmosg : g.u.IsMorphismOfSites Y.J Y'.J) (h : g.comp f' = f.comp g')
    (K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    (derivedPullback g).obj ((derivedPushforward f).obj K) ⟶
      (derivedPushforward f').obj ((derivedPullback g').obj K) :=
  Stacks.CategoryTheory.BaseChange.map (derivedAdjunction f hmosf) (derivedAdjunction f' hmosf')
    (derivedPullbackCompIsoLeft f' g hmosf' hmosg)
    (derivedPullbackCompIsoRight f g' f' g hmosf hmosg' h) K

/-- Under the derived adjunction `L(f')^* ⊣ Rf'_*`, the base change map corresponds to `L(g')^*`
of the derived counit `Lf^* Rf_* K ⟶ K`, transported across the two composition isomorphisms of
Stacks 0D6D. -/
@[simp]
theorem derivedBaseChangeMap_adjoint (hmosf : f.u.IsMorphismOfSites Y.J X.J)
    (hmosg' : g'.u.IsMorphismOfSites X.J X'.J) (hmosf' : f'.u.IsMorphismOfSites Y'.J X'.J)
    (hmosg : g.u.IsMorphismOfSites Y.J Y'.J) (h : g.comp f' = f.comp g')
    (K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    ((derivedAdjunction f' hmosf').homEquiv
        ((derivedPullback g).obj ((derivedPushforward f).obj K))
        ((derivedPullback g').obj K)).symm
        (derivedBaseChangeMap f g' f' g hmosf hmosg' hmosf' hmosg h K) =
      (derivedPullbackCompIsoLeft f' g hmosf' hmosg).hom.app ((derivedPushforward f).obj K) ≫
        (derivedPullbackCompIsoRight f g' f' g hmosf hmosg' h).inv.app
          ((derivedPushforward f).obj K) ≫
        (derivedPullback g').map ((derivedAdjunction f hmosf).counit.app K) :=
  Stacks.CategoryTheory.BaseChange.homEquiv_symm_map (derivedAdjunction f hmosf)
    (derivedAdjunction f' hmosf') (derivedPullbackCompIsoLeft f' g hmosf' hmosg)
    (derivedPullbackCompIsoRight f g' f' g hmosf hmosg' h) K

/-- The base change map is the transpose, under `L(f')^* ⊣ Rf'_*`, of the derived pullback along
`g'` of the derived counit. -/
theorem derivedBaseChangeMap_eq (hmosf : f.u.IsMorphismOfSites Y.J X.J)
    (hmosg' : g'.u.IsMorphismOfSites X.J X'.J) (hmosf' : f'.u.IsMorphismOfSites Y'.J X'.J)
    (hmosg : g.u.IsMorphismOfSites Y.J Y'.J) (h : g.comp f' = f.comp g')
    (K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    derivedBaseChangeMap f g' f' g hmosf hmosg' hmosf' hmosg h K =
      (derivedAdjunction f' hmosf').homEquiv
        ((derivedPullback g).obj ((derivedPushforward f).obj K))
        ((derivedPullback g').obj K)
        ((derivedPullbackCompIsoLeft f' g hmosf' hmosg).hom.app
            ((derivedPushforward f).obj K) ≫
          (derivedPullbackCompIsoRight f g' f' g hmosf hmosg' h).inv.app
            ((derivedPushforward f).obj K) ≫
          (derivedPullback g').map ((derivedAdjunction f hmosf).counit.app K)) :=
  Stacks.CategoryTheory.BaseChange.map_eq (derivedAdjunction f hmosf)
    (derivedAdjunction f' hmosf') (derivedPullbackCompIsoLeft f' g hmosf' hmosg)
    (derivedPullbackCompIsoRight f g' f' g hmosf hmosg' h) K

/-- The derived base change map is natural in the object of `D(𝒪_C)`. -/
theorem derivedBaseChangeMap_naturality (hmosf : f.u.IsMorphismOfSites Y.J X.J)
    (hmosg' : g'.u.IsMorphismOfSites X.J X'.J) (hmosf' : f'.u.IsMorphismOfSites Y'.J X'.J)
    (hmosg : g.u.IsMorphismOfSites Y.J Y'.J) (h : g.comp f' = f.comp g')
    {K L : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    (e : K ⟶ L) :
    (derivedPullback g).map ((derivedPushforward f).map e) ≫
        derivedBaseChangeMap f g' f' g hmosf hmosg' hmosf' hmosg h L =
      derivedBaseChangeMap f g' f' g hmosf hmosg' hmosf' hmosg h K ≫
        (derivedPushforward f').map ((derivedPullback g').map e) :=
  Stacks.CategoryTheory.BaseChange.map_naturality (derivedAdjunction f hmosf)
    (derivedAdjunction f' hmosf') (derivedPullbackCompIsoLeft f' g hmosf' hmosg)
    (derivedPullbackCompIsoRight f g' f' g hmosf hmosg' h) e

end Square

end

end Stacks.Cohomology.DerivedBaseChangeOnTopoi

end
