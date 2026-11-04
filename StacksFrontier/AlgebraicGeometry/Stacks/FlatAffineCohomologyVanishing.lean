module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LocalAcyclicity.DerivedGlobalSectionsAdditive
public import StacksFrontier.AlgebraicGeometry.Stacks.DerivedGlobalSectionsOnSmoothAndFlatSites
public import StacksFrontier.AlgebraicGeometry.Stacks.DerivedSectionsOverSmoothAndFlatObjects
public import StacksFrontier.AlgebraicGeometry.Stacks.FlatFppfVanishingCriterion
public import StacksFrontier.Homology.Injectives.KInjective.RightDerivedCriterion
import StacksCore.Tactic.StacksAttribute

/-!
# Complexes on an algebraic stack with no cohomology over the flat affine objects

Let `𝒳` be an algebraic stack, let `g : Sh(𝒳_{flat,fppf}) ⟶ Sh(𝒳_{fppf})` be the comparison
morphism of topoi of Stacks 08MZ, and let `K` be an object of `D(𝒳_{fppf})` such that
`RΓ(x, K) = 0` for every object `x` of `𝒳` lying over an affine scheme `U` with `U → 𝒳` flat.
**Stacks 0H14** says that then `H^i(𝒳, K) = 0` for all `i`.

This file proves it with no hypothesis.
`StacksFrontier/AlgebraicGeometry/Stacks/FlatFppfVanishingCriterion.lean` carries the source's
argument with two inputs as hypotheses; both are proved here.

* `g⁻¹K = 0`. By Stacks 0H10 (2)(b) the hypothesis says that `g⁻¹K` has vanishing derived
  sections over the flat objects lying over affine schemes, which cover the flat-fppf site, so
  `g⁻¹K = 0`, by
  `FlatFppf.isZero_restriction_of_isZero_derivedSections_flatAffine`.
  The half of Stacks 0794 carried as `hgen` in `FlatFppfVanishingCriterion.lean` is
  `AlgebraicGeometry.Stack.FlatFppf.derivedLowerShriekComputesFlatGenerator`.
* From `g⁻¹K = 0` to `H^i(𝒳, K) = 0`. Then `RΓ(𝒳_{flat,fppf}, g⁻¹K) = 0`, and Stacks 0H10
  (2)(a), `AlgebraicGeometry.Stack.FlatFppf.derivedGlobalSectionsRestrictionIso`, identifies it
  with `RΓ(𝒳_{fppf}, K)`.

Cohomology over an object `x` is the right derived functor of sections over `x`, the convention
of Stacks 0DD8 and of Stacks 0H10 (2)(b) in this library; it agrees with cohomology of the slice
site by Stacks 03F3.

## Main results

* `AlgebraicGeometry.Stack.FlatFppf.additive_derivedGlobalSectionsOnFlatSite`:
  `RΓ(𝒳_{flat,fppf}, -)` is additive.
* `AlgebraicGeometry.Stack.FlatFppf.isZero_derivedGlobalSectionsOnFlatSite_restriction`:
  under the hypothesis of Stacks 0H14, `RΓ(𝒳_{flat,fppf}, g⁻¹K) = 0`.
* `AlgebraicGeometry.Stack.FlatFppf.isZero_cohomology_of_isZero_derivedSectionsFppf_flatAffine`:
  **Stacks 0H14**.

## References

* [Stacks Project, Tag 03F3](https://stacks.math.columbia.edu/tag/03F3)
* [Stacks Project, Tag 0794](https://stacks.math.columbia.edu/tag/0794)
* [Stacks Project, Tag 08MZ](https://stacks.math.columbia.edu/tag/08MZ)
* [Stacks Project, Tag 0DD8](https://stacks.math.columbia.edu/tag/0DD8)
* [Stacks Project, Tag 0H10](https://stacks.math.columbia.edu/tag/0H10)
* [Stacks Project, Tag 0H14](https://stacks.math.columbia.edu/tag/0H14)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Stack.FlatFppf

universe u w

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] isContinuous_inclusion' isCocontinuous_inclusion'

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (𝒳 : Stack.AlgebraicStacks.{u, w} B S hS)

/-- **Derived global sections on the flat-fppf site are additive.** Global sections are
additive, and the abelian sheaves on the flat-fppf site form a Grothendieck abelian category, so
every complex has a K-injective resolution, on which the derived functor is computed. -/
instance additive_derivedGlobalSectionsOnFlatSite :
    (derivedGlobalSectionsOnFlatSite B S hS 𝒳).Additive :=
  Stacks.SmallDerivedCategory.additive_of_exists_quasiIso_isKInjective _ _
    (((Sheaf.Γ (inclusionTopology B S hS 𝒳) AddCommGrpCat.{u + 1}).mapHomotopyCategory
      (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).totalRightDerivedUnit DerivedCategory.Qh
      (HomotopyCategory.quasiIso
        (Sheaf (inclusionTopology B S hS 𝒳) AddCommGrpCat.{u + 1}) (ComplexShape.up ℤ)))
    Stacks.Injectives.exists_kInjective_resolution_of_grothendieck

/-- **`RΓ(𝒳_{flat,fppf}, g⁻¹K) = 0`, with no hypothesis beyond that of Stacks 0H14.** If the
derived sections of a complex `K` of abelian fppf sheaves vanish over every object of `𝒳` that
lies over an affine scheme and is flat over `𝒳`, then `g⁻¹K = 0` (Stacks 0H10 (2)(b) and the
covering of the flat-fppf site by such objects), hence so are its derived global sections on the
flat-fppf site. -/
theorem isZero_derivedGlobalSectionsOnFlatSite_restriction
    (K : DerivedCategory (Sheaf (fppfTopology B S hS 𝒳) AddCommGrpCat.{u + 1}))
    (hK : ∀ x : 𝒳.val.val.obj, flatObject B S hS 𝒳.val x →
      IsAffine ((BigFppfOver.toScheme B S hS).obj (𝒳.val.val.p.obj x)) →
      IsZero ((derivedSectionsFppf B S hS 𝒳 x).obj K)) :
    IsZero ((derivedGlobalSectionsOnFlatSite B S hS 𝒳).obj
      ((Stacks.Cohomology.DerivedLowerShriek.derivedAbelianRestriction.{u + 1}
        (inclusionTopology B S hS 𝒳) (fppfTopology B S hS 𝒳)
        (objectProperty B S hS 𝒳).ι).obj K)) :=
  (derivedGlobalSectionsOnFlatSite B S hS 𝒳).map_isZero
    (isZero_restriction_of_isZero_derivedSections_flatAffine B S hS 𝒳 K
      (fun x _ => derivedLowerShriekComputesFlatGenerator B S hS 𝒳 x) hK)

/-- **Stacks 0H14.** Let `𝒳` be an algebraic stack and let `K` be an object of `D(𝒳_{fppf})` such
that `RΓ(x, K) = 0` for every object `x` of `𝒳` lying over an affine scheme `U` with `U → 𝒳`
flat. Then `H^i(𝒳, K) = 0` for all `i`.

Here `RΓ(x, -)` is the right derived functor of sections over `x` (the convention of Stacks 0DD8
and Stacks 0H10 (2)(b) in this library), and `H^i(𝒳, K)` is the `i`-th cohomology of the
unbounded derived global sections `RΓ(𝒳_{fppf}, K)`.

This is the source's proof: `g⁻¹K = 0` because its derived sections vanish on a family covering
the flat-fppf site (Stacks 0H10 (2)(b)), so `RΓ(𝒳_{flat,fppf}, g⁻¹K) = 0`, which is
`RΓ(𝒳_{fppf}, K)` by Stacks 0H10 (2)(a). -/
@[stacks 0H14 "unconditional. Cohomology over an object is the derived functor of sections \
over it (Tag 0DD8 convention, equal to cohomology of the slice site by Tag 03F3)"]
theorem isZero_cohomology_of_isZero_derivedSectionsFppf_flatAffine
    (K : DerivedCategory (Sheaf (fppfTopology B S hS 𝒳) AddCommGrpCat.{u + 1}))
    (hK : ∀ x : 𝒳.val.val.obj, flatObject B S hS 𝒳.val x →
      IsAffine ((BigFppfOver.toScheme B S hS).obj (𝒳.val.val.p.obj x)) →
      IsZero ((derivedSectionsFppf B S hS 𝒳 x).obj K))
    (i : ℤ) :
    IsZero ((DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} i).obj
      ((AlgebraicGeometry.Stack.derivedGlobalSections.{u, u + 1} B S hS 𝒳.val).obj K)) :=
  (DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} i).map_isZero
    ((isZero_derivedGlobalSectionsOnFlatSite_restriction B S hS 𝒳 K hK).of_iso
      ((derivedGlobalSectionsRestrictionIso B S hS 𝒳).app K).symm)

end AlgebraicGeometry.Stack.FlatFppf

end
