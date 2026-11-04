module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DenseSubsiteModules
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedSite
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.EssentiallySmall

/-!
# A small model of an essentially small ringed site

Let `X` be a ringed site whose underlying category is essentially small, with morphisms and
structure rings in `Type u` but objects possibly in a larger universe, such as the small étale
ringed site of an algebraic space, an `AlgebraicGeometry.RingedSite.{u + 1, u, u}`. Its
underlying category is equivalent to a category `SmallModel.{u} X.C` in `Type u`; transporting the
topology and the structure sheaf along that equivalence produces a ringed site
`AlgebraicGeometry.RingedSite.smallModel X : RingedSite.{u, u, u}`, and restriction of sections
along the equivalence identifies the sheaves of modules on the two ringed sites.

## Main definitions

* `AlgebraicGeometry.RingedSite.smallModel` — the model, a `RingedSite.{u, u, u}`.
* `AlgebraicGeometry.RingedSite.smallModelModulesEquiv` — **the Comparison Lemma for sheaves of
  modules** along the comparison: `Mod(𝒪_X) ≌ Mod(𝒪_model)`.

## Implementation notes

This is `AlgebraicGeometry.SmallEtale.smallModelRingedTopos` and
`AlgebraicGeometry.SmallEtale.smallModelModulesEquiv` of
`StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/SmallEtaleSmallModelModules.lean`, which
are stated for the small étale site of a scheme, for an arbitrary essentially small ringed site.
The model category, its topology and its structure sheaf are the ones of that file: the topology
is the one induced by the comparison `SmallModel.{u} X.C ⥤ X.C`, and the structure sheaf is the
restriction of `𝒪_X` along it. The equivalence of sheaves of modules is
`Stacks.DenseSubsiteModules.moduleRestrictionEquivalence`, the comparison being a dense subsite
inclusion for the induced topology.

## References

* [Stacks Project, Tag 03A0](https://stacks.math.columbia.edu/tag/03A0)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.DenseSubsiteModules

universe c u

namespace AlgebraicGeometry.RingedSite

variable (X : RingedSite.{c, u, u}) [EssentiallySmall.{u} X.C]

/-- The comparison of the underlying category of `X` with a small model of it in `Type u`. -/
abbrev smallModelEquiv : X.C ≌ SmallModel.{u} X.C :=
  equivSmallModel.{u} X.C

/-- The topology of `X`, transported to the small model: the topology induced by the comparison
`SmallModel.{u} X.C ⥤ X.C`. -/
abbrev smallModelTopology : GrothendieckTopology (SmallModel.{u} X.C) :=
  (smallModelEquiv X).inverse.inducedTopology X.J

/-- The structure sheaf of the model: the restriction of `𝒪_X` along the comparison. -/
abbrev smallModelStructureSheaf : Sheaf (smallModelTopology X) CommRingCat.{u} :=
  ((smallModelEquiv X).inverse.sheafPushforwardContinuous CommRingCat.{u}
    (smallModelTopology X) X.J).obj X.O

/-- **The small model of `X`**, a ringed site whose objects, morphisms and structure rings all
lie in `Type u`. -/
abbrev smallModel : RingedSite.{u, u, u} where
  C := SmallModel.{u} X.C
  J := smallModelTopology X
  O := smallModelStructureSheaf X

/-- The comma categories indexing the right Kan extension along the comparison have the limits
of a complete category with morphisms in `Type u`: they are essentially small, the model being
small and `X.C` locally small. This is what makes restriction of sheaves along the comparison an
equivalence. -/
instance hasLimitsOfShape_structuredArrow_smallModelEquiv_inverse_op
    (W : X.Cᵒᵖ) (A : Type (u + 1)) [Category.{u} A] [HasLimits A] :
    HasLimitsOfShape (StructuredArrow W (smallModelEquiv X).inverse.op) A :=
  have : EssentiallySmall.{u} (StructuredArrow W (smallModelEquiv X).inverse.op) :=
    inferInstance
  hasLimitsOfShape_of_essentiallySmall _ _

/-- **The Comparison Lemma for sheaves of modules, for the small model.** Restriction of
sections along the comparison is an equivalence from sheaves of `𝒪_X`-modules to sheaves of
modules over the structure sheaf of the model. -/
def smallModelModulesEquiv :
    SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ≌
      SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (smallModel X).O) :=
  moduleRestrictionEquivalence.{u} (smallModelTopology X) X.J (smallModelEquiv X).inverse
    (Stacks.SheafOfModules.Tensor.ringSheaf X.O)

end AlgebraicGeometry.RingedSite

end
