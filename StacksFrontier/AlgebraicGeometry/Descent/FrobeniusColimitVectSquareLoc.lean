module

public import StacksFrontier.AlgebraicGeometry.Descent.FrobeniusColimitVectorBundlesCube

/-!
# Localising a morphism over a corner of a commutative square of schemes

Let `p` be a prime and let

```
W ⟶ V
↓     ↓
Z ⟶ X
```

be a commutative square of schemes in characteristic `p`, with vertical morphisms `zV : W ⟶ V`
and `z : Z ⟶ X` and horizontal ones `ιV : V ⟶ X` and `ιW : W ⟶ Z`. The transition functors of
[Stacks, Tag 0EXE] along the two composites agree up to the comparison
`AlgebraicGeometry.frobeniusColimitVectorBundlesSquareIso`, so a morphism of finite locally free
`colim_F 𝒪_Z`-modules between the transitions of two `colim_F 𝒪_X`-modules can be *localised*: it
is carried, by conjugation with that comparison, to a morphism between the transitions along the
other side of the square. This file constructs that localisation and records its two basic
properties.

This is the operation the trivialising-cover argument for [Stacks, Tag 0EXD] performs on the two
data `(g, k)` whose compatibility fullness has to lift to the base: the square above is a side
face of the cube, the initial corner `V` is a member of the cover and `W` is the corner of the
local square over it, and the localisation is how a datum given over the whole of `Z` becomes one
of the two local data of the local Hom-square.

## Main definitions

* `AlgebraicGeometry.frobeniusColimitVectorBundlesSquareLoc`: **the localisation of a morphism
  along a commutative square**, by conjugation with the square comparison.

## Main results

* `AlgebraicGeometry.frobeniusColimitVectorBundlesSquareLoc_map`: **the localisation of the
  transition of a global morphism is the transition of its restriction.** This is the naturality
  of the square comparison, and it is the property that makes the localisation the right operation:
  the local datum attached to a morphism that *comes from the base* is the one the base morphism
  induces locally.
* `AlgebraicGeometry.frobeniusColimitVectorBundlesSquareLoc_injective`: the localisation is
  injective, being conjugation by an isomorphism. Together with the previous result this gives
  `AlgebraicGeometry.frobeniusColimitVectorBundlesPullback_map_eq_of_square`, the equality-level
  statement that the faithfulness half of the trivialising-cover argument uses, as a two-line
  corollary; that lemma is kept where it is because it is what
  `AlgebraicGeometry.jointly_injective_frobeniusColimitVectorBundles_of_cover` consumes.

## Implementation notes

Everything is stated with the four morphisms of the square as variables subject to the single
equation `zV ≫ ιV = ιW ≫ z`, so no transport across opens occurs and the local corner `V` may be
an arbitrary scheme over `X` rather than an open subscheme of it — the same choice the cube
coherence `AlgebraicGeometry.frobeniusColimitVectorBundlesSquareIso_cube_app` makes, and what lets
the instantiation take `V` to be `Spec (A_g)` itself.

## References

* [Stacks Project, Tag 0EXD](https://stacks.math.columbia.edu/tag/0EXD)
* [Stacks Project, Tag 0EXE](https://stacks.math.columbia.edu/tag/0EXE)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Frobenius

universe u

namespace AlgebraicGeometry

variable (p : ℕ) [Fact p.Prime] {X Z V W : Scheme.{u}}
  (z : Z ⟶ X) (ιV : V ⟶ X) (zV : W ⟶ V) (ιW : W ⟶ Z)
  (hX : IsInCharacteristic X p) (hZ : IsInCharacteristic Z p)
  (hV : IsInCharacteristic V p) (hW : IsInCharacteristic W p)
  (sz : zV ≫ ιV = ιW ≫ z)

/-- **The localisation of a morphism along a commutative square of schemes.**

Given `zV ≫ ιV = ιW ≫ z` and a morphism `gg` between the transitions along `z` of two finite
locally free `colim_F 𝒪_X`-modules, this is the morphism between their transitions along
`ιV` and then `zV` obtained by transporting the transition of `gg` along `ιW` across
`AlgebraicGeometry.frobeniusColimitVectorBundlesSquareIso`. -/
noncomputable def frobeniusColimitVectorBundlesSquareLoc
    {M N : frobeniusColimitVectorBundles X p hX}
    (gg : (frobeniusColimitVectorBundlesPullback p z hZ hX).obj M ⟶
      (frobeniusColimitVectorBundlesPullback p z hZ hX).obj N) :
    (frobeniusColimitVectorBundlesPullback p zV hW hV).obj
        ((frobeniusColimitVectorBundlesPullback p ιV hV hX).obj M) ⟶
      (frobeniusColimitVectorBundlesPullback p zV hW hV).obj
        ((frobeniusColimitVectorBundlesPullback p ιV hV hX).obj N) :=
  (frobeniusColimitVectorBundlesSquareIso p ιV z zV ιW hX hV hZ hW sz).inv.app M ≫
    (frobeniusColimitVectorBundlesPullback p ιW hW hZ).map gg ≫
      (frobeniusColimitVectorBundlesSquareIso p ιV z zV ιW hX hV hZ hW sz).hom.app N

/-- **The localisation of the transition of a global morphism is the transition of its
restriction.**

This is the naturality of `AlgebraicGeometry.frobeniusColimitVectorBundlesSquareIso` at the
morphism, with the two comparisons cancelling. It says that the localisation of
`AlgebraicGeometry.frobeniusColimitVectorBundlesSquareLoc` is the right operation: a datum over
`Z` that comes from a morphism over `X` localises to the datum that morphism induces over `V`. -/
theorem frobeniusColimitVectorBundlesSquareLoc_map
    {M N : frobeniusColimitVectorBundles X p hX} (φ : M ⟶ N) :
    frobeniusColimitVectorBundlesSquareLoc p z ιV zV ιW hX hZ hV hW sz
        ((frobeniusColimitVectorBundlesPullback p z hZ hX).map φ) =
      (frobeniusColimitVectorBundlesPullback p zV hW hV).map
        ((frobeniusColimitVectorBundlesPullback p ιV hV hX).map φ) := by
  rw [frobeniusColimitVectorBundlesSquareLoc, ← Functor.comp_map, ← Category.assoc,
    ← (frobeniusColimitVectorBundlesSquareIso p ιV z zV ιW hX hV hZ hW sz).inv.naturality φ,
    Category.assoc, Iso.inv_hom_id_app, Category.comp_id, Functor.comp_map]

/-- **Localisation along a commutative square preserves composition.** -/
theorem frobeniusColimitVectorBundlesSquareLoc_comp
    {M N P : frobeniusColimitVectorBundles X p hX}
    (gg : (frobeniusColimitVectorBundlesPullback p z hZ hX).obj M ⟶
      (frobeniusColimitVectorBundlesPullback p z hZ hX).obj N)
    (kk : (frobeniusColimitVectorBundlesPullback p z hZ hX).obj N ⟶
      (frobeniusColimitVectorBundlesPullback p z hZ hX).obj P) :
    frobeniusColimitVectorBundlesSquareLoc p z ιV zV ιW hX hZ hV hW sz (gg ≫ kk) =
      frobeniusColimitVectorBundlesSquareLoc p z ιV zV ιW hX hZ hV hW sz gg ≫
        frobeniusColimitVectorBundlesSquareLoc p z ιV zV ιW hX hZ hV hW sz kk := by
  simp [frobeniusColimitVectorBundlesSquareLoc, Functor.map_comp]

end AlgebraicGeometry

end
