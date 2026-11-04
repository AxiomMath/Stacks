module

public import StacksFrontier.AlgebraicGeometry.Stacks.DerivedSectionsOverSmoothAndFlatObjects
public import StacksFrontier.AlgebraicGeometry.Stacks.FlatFppfParasiticVanishing
public import StacksFrontier.CategoryTheory.Sites.Cohomology.LowerShriek.DerivedAbelianSectionsAdditive
import StacksCore.Tactic.StacksAttribute

/-!
# Stacks 0H13 with no carried hypothesis

Let `𝒳` be an algebraic stack and let `K` be an object of `D(𝒳_{fppf})` whose cohomology sheaves
are parasitic (**Stacks 0773**). **Stacks 0H13** says that `RΓ(x, K) = 0` for every object `x`
of `𝒳` lying over a scheme `U` such that `U → 𝒳` is flat.

The steps of the source's proof are in
`StacksFrontier/AlgebraicGeometry/Stacks/FlatFppfParasiticVanishing.lean`; its original form,
`AlgebraicGeometry.Stack.FlatFppf.isZero_derivedSections_of_parasitic_cohomology`, carried two
inputs. Both are discharged here:

* the half of **Stacks 0794** computing `Lg_!` on the generator `j_{x!} ℤ_x`, which is
  `AlgebraicGeometry.Stack.FlatFppf.derivedLowerShriekComputesFlatGenerator`;
* the instance saying that `RΓ(x, -)` on the flat-fppf site preserves zero morphisms, which is an
  instance of `Stacks.Cohomology.DerivedLowerShriek.BigSite.additive_derivedAbelianSections`.

Cohomology over an object is the right derived functor of sections over it, the convention of
the formalized forms of Stacks 0H10 (2)(b) and Stacks 0DD8; see the module docstring of
`StacksFrontier/AlgebraicGeometry/Stacks/FlatFppfDerivedSections.lean`. The parasitic condition is
written out on abelian sheaves, at the `flatObject` predicate of **Stacks 0787** that
`AlgebraicGeometry.Stack.IsParasitic` quantifies over; see the module docstring of
`StacksFrontier/AlgebraicGeometry/Stacks/FlatFppfParasiticVanishing.lean`.

## Main results

* `AlgebraicGeometry.Stack.FlatFppf.isZero_derivedSectionsFppf_of_parasitic_cohomology`:
  **Stacks 0H13**.

## References

* [Stacks Project, Tag 0773](https://stacks.math.columbia.edu/tag/0773)
* [Stacks Project, Tag 0794](https://stacks.math.columbia.edu/tag/0794)
* [Stacks Project, Tag 0H10](https://stacks.math.columbia.edu/tag/0H10)
* [Stacks Project, Tag 0H13](https://stacks.math.columbia.edu/tag/0H13)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Stack.FlatFppf

universe u w

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] isContinuous_inclusion' isCocontinuous_inclusion'

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (𝒳 : Stack.AlgebraicStacks.{u, w} B S hS)

/-- **Stacks 0H13.** Let `𝒳` be an algebraic stack and let `K` be an object of `D(𝒳_{fppf})`
whose cohomology sheaves are parasitic — the sections of every cohomology sheaf of `K` vanish at
every object of `𝒳` lying over a scheme `U` such that `U → 𝒳` is flat (**Stacks 0773**). Then
`RΓ(x, K) = 0` for every such object `x`.

Cohomology over an object is the right derived functor of sections over it. The proof is the
source's: by Stacks 0H10 (2)(b), `RΓ(x, K) = RΓ(x, g⁻¹K)`, and `g⁻¹K = 0` because its cohomology
sheaves are the restrictions of those of `K` to the flat objects. -/
@[stacks 0H13 "cohomology over an object taken as the derived functor of sections over it, and \
the parasitic condition of Stacks 0773 written out on abelian sheaves"]
theorem isZero_derivedSectionsFppf_of_parasitic_cohomology
    (K : DerivedCategory (Sheaf (fppfTopology B S hS 𝒳) AddCommGrpCat.{u + 1}))
    (hK : ∀ n : ℤ, ∀ y : 𝒳.val.val.obj, flatObject B S hS 𝒳.val y →
      Subsingleton (((DerivedCategory.homologyFunctor
        (Sheaf (fppfTopology B S hS 𝒳) AddCommGrpCat.{u + 1}) n).obj K).obj.obj (op y)))
    (x : 𝒳.val.val.obj) (hx : flatObject B S hS 𝒳.val x) :
    IsZero ((derivedSectionsFppf B S hS 𝒳 x).obj K) :=
  IsZero.of_iso ((derivedSections B S hS 𝒳 ⟨x, hx⟩).map_isZero
      ((isZero_derivedAbelianRestriction_iff B S hS 𝒳 K).mpr hK))
    ((derivedSectionsRestrictionIsoOfFlatObject B S hS 𝒳 ⟨x, hx⟩).app K).symm

end AlgebraicGeometry.Stack.FlatFppf
