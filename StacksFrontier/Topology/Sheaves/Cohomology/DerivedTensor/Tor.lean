module

public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedTensor.OnARingedSpace
import StacksCore.Tactic.StacksAttribute

/-!
# Tor of two modules on a ringed space

Let `(X, O_X)` be a ringed space and let `F`, `G` be `O_X`-modules. Their `Tor` modules are

`Tor_p^{O_X}(F, G) = H^{-p}(F ⊗_{O_X}^{L} G)`,

the cohomology in degree `-p` of the derived tensor product of `F` and `G`, each placed in
degree `0` of `D(O_X)`.

## Main definitions

* `Stacks.Cohomology.torFunctor`: `Tor_p^{O_X}(-, -)` as a bifunctor on `O_X`-modules.
* `Stacks.Cohomology.tor`: the `O_X`-module `Tor_p^{O_X}(F, G)`.

## Main results

* `Stacks.Cohomology.tor_eq`: the defining formula, spelled out.

## Implementation notes

The derived tensor product used is the one carrying Tag 06YH,
`Stacks.Cohomology.TorAmplitude.derTensor`, whose `tensor` field is the derived tensor
bifunctor on `D(O_X)`; nothing here re-chooses it. An `O_X`-module is placed in degree `0` by
Mathlib's `CategoryTheory.DerivedCategory.singleFunctor` and the cohomology is taken by
`CategoryTheory.DerivedCategory.homologyFunctor`, so `Tor` is functorial in both arguments by
construction and `tor` is the value of the bifunctor rather than a separate definition.

Indexing follows the source: `tor X p` is homological indexing, so it is cohomology in degree
`-p`; in particular `Tor_0` is the ordinary tensor product and `Tor_p` vanishes for `p < 0`.

The universes of the space, its structure sheaf and its modules coincide, and the derived
category's own hom universe stays independent, exactly as for
`Stacks.Cohomology.TorAmplitude.derTensor`; the narrowing is inherited from the existence of
K-flat resolutions (Tag 06YS) and is not introduced here. `HasDerivedCategory` has to be
seated by hand at the `Stacks.DerivedTensor.RingedSite.Modules X.sheaf` spelling: that type is
`OXMod X` by `rfl`, but an instance proved at one spelling of a non-reducible definition does
not fire at the other.

## References

* [Stacks Project, Tag 08BP](https://stacks.math.columbia.edu/tag/08BP)
* [Stacks Project, Tag 06YH](https://stacks.math.columbia.edu/tag/06YH)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open StrictlyPerfect Stacks.Cohomology.TorAmplitude

namespace Stacks.Cohomology

universe u d

variable (X : RingedSpace.{u, u}) [HasDerivedCategory.{d} (OXMod.{u} X)]

-- `HasDerivedCategory` at the spelling of Stacks 06YU: the type is `OXMod X` by `rfl`, but
-- `structureSheafOfRings` is not reducible, so an instance proved at one spelling does not fire
-- at the other. Seated here, not restated.
attribute [local instance] _root_.Stacks.Cohomology.TorAmplitude.hasDerivedCategoryModules

/-- **Tag 08BP.** `Tor_p^{O_X}(-, -)` as a bifunctor on `O_X`-modules: place both arguments in
degree `0` of `D(O_X)`, take their derived tensor product, and read off cohomology in degree
`-p`. -/
def torFunctor (p : ℤ) : OXMod.{u} X ⥤ OXMod.{u} X ⥤ OXMod.{u} X :=
  DerivedCategory.singleFunctor (OXMod.{u} X) 0 ⋙ (derTensor X).tensor ⋙
    ((Functor.whiskeringLeft (OXMod.{u} X) (DerivedCategory (OXMod.{u} X))
          (DerivedCategory (OXMod.{u} X))).obj
        (DerivedCategory.singleFunctor (OXMod.{u} X) 0) ⋙
      (Functor.whiskeringRight (OXMod.{u} X) (DerivedCategory (OXMod.{u} X))
          (OXMod.{u} X)).obj
        (DerivedCategory.homologyFunctor (OXMod.{u} X) (-p)))

/-- **Tag 08BP.** The `O_X`-module `Tor_p^{O_X}(F, G) = H^{-p}(F ⊗_{O_X}^{L} G)`. -/
@[stacks 08BP,
  sga "4½ Etat_0 6.2" "Tor_i, ringed space",
  sga "4 XVII 4.1.8" "modules, not complexes"]
def tor (p : ℤ) (F G : OXMod.{u} X) : OXMod.{u} X := ((torFunctor X p).obj F).obj G

/-- The defining formula for `Tor_p^{O_X}(F, G)`: cohomology in degree `-p` of the derived
tensor product of `F` and `G`, each placed in degree `0`. -/
theorem tor_eq (p : ℤ) (F G : OXMod.{u} X) :
    tor X p F G =
      (DerivedCategory.homologyFunctor (OXMod.{u} X) (-p)).obj
        (((derTensor X).tensor.obj
            ((DerivedCategory.singleFunctor (OXMod.{u} X) 0).obj F)).obj
          ((DerivedCategory.singleFunctor (OXMod.{u} X) 0).obj G)) :=
  rfl

end Stacks.Cohomology
