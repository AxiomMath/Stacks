module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.AlgebraBundleStalk
public import StacksFrontier.AlgebraicGeometry.RegularSequence.KoszulExtDescent

/-!
# The exterior powers of the first Ext sheaf, over the quotient

Let `O♯` be a sheaf of commutative rings on a space, let `φ : (O♯)ʳ ⟶ O♯` generate a sheaf of
ideals `𝓘`, let `O_X = O♯/𝓘`, and let `K` be a Koszul complex resolving the quotient. The first
Ext sheaf `Ext^1_{O♯}(O_X, O_X)` is annihilated by `𝓘` and so is a sheaf of `O_X`-modules; this
file forms its exterior powers **over `O_X`**,

`⋀ⁱ_{O_X}(Ext^1_{O♯}(O_X, O_X))`,

which is the source of the map that Stacks 0BQY asserts to be an isomorphism.

The exterior powers are taken over `O_X` and not over `O♯`, because that is the ring the source
states them over. The two do agree for `i ≥ 1` — an exterior power of a module annihilated by an
ideal does not see the difference between the ring and its quotient — but they differ in degree
`0`, where one is `O♯` and the other is `O_X`, so the choice of ring is not a matter of
convenience.

## Main definitions

* `Stacks.RegularSequence.KoszulChainData.extExteriorAlgebra`: the tensor, exterior and symmetric
  algebras of the descended first Ext sheaf, as a package over `O_X`.
* `Stacks.RegularSequence.KoszulChainData.extExteriorPower`: the degree-`i` exterior power
  `⋀ⁱ_{O_X}(Ext^1)`.

## Implementation notes

**The package exists with no hypotheses on the base.** `SheafOfModules.algebras` produces a
`TensorExteriorSymmetricAlgebras` for an arbitrary sheaf of modules over an arbitrary sheaf of
commutative rings; the only instance arguments are properties of the site, and those are the ones
already carried here. In particular nothing has to be checked about `O_X` beyond its being a sheaf
of commutative rings, which is what the identification of the Koszul quotient with the quotient
ring sheaf provides. There is no precedent in this library for exterior powers over a quotient
structure sheaf, but there is also no obstruction: the base of the exterior-power API is
unconstrained.

**The generator and the universal property are fields of the package.** The morphism from the Ext
sheaf into degree one is `exteriorGenerator`, and the statement that the package is an exterior
algebra on it is `exterior_isExteriorAlgebra`; they are read off the datum rather than restated
here, so that the universal property used downstream is the one the package carries.

**The types are left to be inferred,** for the reason recorded in
`StacksFrontier/CategoryTheory/Sites/Modules/QuotientRingSheafEpi.lean`: writing them out would make
the elaborator compare a hand-written copy of the quotient ring sheaf with the inferred one, and
that unfolds to a sheafification.

## References

* [Stacks Project, Tag 0BQY](https://stacks.math.columbia.edu/tag/0BQY)
* [Stacks Project, Tag 01CF](https://stacks.math.columbia.edu/tag/01CF)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf Opposite TopologicalSpace
open AlgebraicGeometry

universe u

namespace Stacks.RegularSequence.KoszulChainData

open Stacks.Sites Stacks.SheafOfModules Stacks.RegularSequence

attribute [local instance] HasDerivedCategory.standard

variable {X : TopCat.{u}} (Rc : TopCat.Sheaf CommRingCat.{u} X)
  [HasSheafify (Opens.grothendieckTopology ↥X) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology ↥X).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasWeakSheafify (Opens.grothendieckTopology ↥X) CommRingCat.{u}]
  {r : ℕ}
  {A : SheafOfModules.TensorExteriorSymmetricAlgebras (Opens.grothendieckTopology ↥X)
    (koszulFreeSheaf Rc r)}
  {φ : koszulFreeSheaf Rc r ⟶
    SheafOfModules.unit (toRingCat (Opens.grothendieckTopology ↥X) Rc)}

/-- **The exterior algebra of the first Ext sheaf, over the quotient.** The tensor, exterior and
symmetric algebras of `Ext^1_{O♯}(O_X, O_X)` read as a sheaf of `O_X`-modules, as a chosen
package. Its `exteriorGenerator` is the morphism from the Ext sheaf into degree one, and
`exterior_isExteriorAlgebra` is the universal property of the exterior algebra on that
generator. -/
def extExteriorAlgebra (K : KoszulChainData.{u, u, u} A φ) [QuasiIso K.augmentation] :=
  SheafOfModules.algebras (Opens.grothendieckTopology ↥X) (extDescended Rc K 1)

/-- **The exterior powers of the first Ext sheaf, over the quotient**:
`⋀ⁱ_{O_X}(Ext^1_{O♯}(O_X, O_X))`. This is the source of the map of Stacks 0BQY. -/
def extExteriorPower (K : KoszulChainData.{u, u, u} A φ) [QuasiIso K.augmentation] (i : ℕ) :=
  (extExteriorAlgebra Rc K).exteriorPower i

end Stacks.RegularSequence.KoszulChainData

end
