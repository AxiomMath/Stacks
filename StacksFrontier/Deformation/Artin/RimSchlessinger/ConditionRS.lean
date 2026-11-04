module

public import Mathlib.AlgebraicGeometry.Artinian
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteType.ArtinianLocalRing
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteTypePoint
public import StacksFrontier.AlgebraicGeometry.Pushout.SchemePushout
public import StacksFrontier.AlgebraicGeometry.Pushout.ThickeningPushout
public import StacksFrontier.AlgebraicGeometry.Smooth.FormallySmoothScheme
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf
public import StacksFrontier.CategoryTheory.Sites.Descent.IsStack.FiberIso
public import StacksFrontier.CategoryTheory.TwoFibreProduct.SquareComparisonPaste
public import StacksFrontier.CategoryTheory.TwoFibreProduct.SquareComparisonTransfer
public import StacksFrontier.Deformation.Artin.RimSchlessinger.Strong
public import StacksFrontier.Deformation.ArtinCriteria.Predeformation
public import StacksFrontier.Deformation.BaseCategory.FibreProduct
public import StacksFrontier.Deformation.RimSchlessinger.Basic
public import StacksFrontier.Deformation.RimSchlessingerCategory.SmallExtensionCriterion

/-!
# Condition (RS) for a category fibred in groupoids

A category fibred in groupoids over the big fppf site of a locally Noetherian scheme `S`
satisfies condition (RS) when, for every pushout square of finite-type local Artinian
objects of the site along a closed immersion, restriction from the fibre over the pushout
identifies that fibre with the two-fibre product of the fibres over the other three
corners.

This is the variant of the Rim–Schlessinger condition stated for pushouts of schemes,
rather than for fibre products of algebras as in `Deformation.Artin.SatisfiesRSStar`.

## Main definitions

* `Deformation.Artin.IsArtinianLocal` — an object of the site whose underlying scheme is
  the spectrum of a local Artinian ring.
* `Deformation.Artin.IsFiniteTypeOver` — an object of the site which is of finite type
  over the base scheme.
* `Deformation.Artin.SatisfiesRS` — condition (RS).

## Implementation notes

The two-fibre product is Mathlib's `CategoryTheory.Limits.CategoricalPullback`, and the
comparison is `Deformation.Artin.fiberSquareComparison`, built from the chosen cartesian
pullbacks and the canonical composition isomorphisms. It is the equivalence of *that*
comparison, rather than of an arbitrary equivalence of the underlying categories, which is
required. The definition uses the canonical choice of pullbacks; the condition does not
depend on this choice.

## References

* [Stacks Project, Tag 07WP](https://stacks.math.columbia.edu/tag/07WP)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u u₁ u₂ u₃ v₁

namespace Deformation.Artin

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The underlying scheme of an object of the big fppf site over `S` is the
spectrum of a local Artinian ring. -/
public abbrev IsArtinianLocal (X : BigFppfOver B S hS) : Prop :=
  IsAffine ((BigFppfOver.toScheme B S hS).obj X) ∧
    IsLocalRing Γ((BigFppfOver.toScheme B S hS).obj X, ⊤) ∧
    IsArtinianRing Γ((BigFppfOver.toScheme B S hS).obj X, ⊤)

/-- Finite type of an object of the big site over its base scheme. -/
public abbrev IsFiniteTypeOver (X : BigFppfOver B S hS) : Prop :=
  LocallyOfFiniteType (B.inclusion.map X.hom) ∧ QuasiCompact (B.inclusion.map X.hom)

variable {𝒵 : Type u₁} [Category.{v₁} 𝒵] (p : 𝒵 ⥤ BigFppfOver B S hS)

/-- Condition (RS): restriction across a finite-type local Artinian pushout
along a closed immersion is an equivalence onto the two-fibre product of fibres. -/
@[stacks 07WP]
public abbrev SatisfiesRS (hp : p.IsFiberedInGroupoids) : Prop :=
  let : p.IsFibered := hp.isFibered
  ∀ {X X' Y Y' : BigFppfOver B S hS} (i : X ⟶ X') (j : X ⟶ Y) (i' : X' ⟶ Y')
      (j' : Y ⟶ Y') (w : i ≫ i' = j ≫ j'),
    IsArtinianLocal B S hS X → IsArtinianLocal B S hS X' →
      IsArtinianLocal B S hS Y → IsArtinianLocal B S hS Y' →
      IsFiniteTypeOver B S hS X → IsFiniteTypeOver B S hS X' →
      IsFiniteTypeOver B S hS Y → IsFiniteTypeOver B S hS Y' →
    IsClosedImmersion ((BigFppfOver.toScheme B S hS).map i) →
      IsPushout ((BigFppfOver.toScheme B S hS).map i)
        ((BigFppfOver.toScheme B S hS).map j)
        ((BigFppfOver.toScheme B S hS).map i')
        ((BigFppfOver.toScheme B S hS).map j') →
    (fiberSquareComparison p (p.chosenPullbacks) j i j' i' w.symm).IsEquivalence

/-- Condition (RS) at the squares of Tag 07WP in which `X ⟶ Y` induces a surjection of residue
fields: every global section of `X` agrees with the image of a global section of `Y` up to a
non-unit. The squares coming from fibre products in `𝒞_Λ`, whose residue fields are all
identified with `k`, are of this kind, so this is the part of (RS) that makes a predeformation
category of Tag 07T2 a deformation category. -/
public abbrev SatisfiesRSOfResidue (hp : p.IsFiberedInGroupoids) : Prop :=
  let : p.IsFibered := hp.isFibered
  ∀ {X X' Y Y' : BigFppfOver B S hS} (i : X ⟶ X') (j : X ⟶ Y) (i' : X' ⟶ Y')
      (j' : Y ⟶ Y') (w : i ≫ i' = j ≫ j'),
    IsArtinianLocal B S hS X → IsArtinianLocal B S hS X' →
      IsArtinianLocal B S hS Y → IsArtinianLocal B S hS Y' →
      IsFiniteTypeOver B S hS X → IsFiniteTypeOver B S hS X' →
      IsFiniteTypeOver B S hS Y → IsFiniteTypeOver B S hS Y' →
    IsClosedImmersion ((BigFppfOver.toScheme B S hS).map i) →
      IsPushout ((BigFppfOver.toScheme B S hS).map i)
        ((BigFppfOver.toScheme B S hS).map j)
        ((BigFppfOver.toScheme B S hS).map i')
        ((BigFppfOver.toScheme B S hS).map j') →
      (∀ a : Γ((BigFppfOver.toScheme B S hS).obj X, ⊤),
        ∃ b : Γ((BigFppfOver.toScheme B S hS).obj Y, ⊤),
          a - ((BigFppfOver.toScheme B S hS).map j).appTop.hom b ∈
            nonunits Γ((BigFppfOver.toScheme B S hS).obj X, ⊤)) →
    (fiberSquareComparison p (p.chosenPullbacks) j i j' i' w.symm).IsEquivalence

/-- The fully faithful half of condition (RS): at every square of Tag 07WP the comparison functor
is full and faithful. -/
public abbrev SatisfiesRSFullyFaithful (hp : p.IsFiberedInGroupoids) : Prop :=
  let : p.IsFibered := hp.isFibered
  ∀ {X X' Y Y' : BigFppfOver B S hS} (i : X ⟶ X') (j : X ⟶ Y) (i' : X' ⟶ Y')
      (j' : Y ⟶ Y') (w : i ≫ i' = j ≫ j'),
    IsArtinianLocal B S hS X → IsArtinianLocal B S hS X' →
      IsArtinianLocal B S hS Y → IsArtinianLocal B S hS Y' →
      IsFiniteTypeOver B S hS X → IsFiniteTypeOver B S hS X' →
      IsFiniteTypeOver B S hS Y → IsFiniteTypeOver B S hS Y' →
    IsClosedImmersion ((BigFppfOver.toScheme B S hS).map i) →
      IsPushout ((BigFppfOver.toScheme B S hS).map i)
        ((BigFppfOver.toScheme B S hS).map j)
        ((BigFppfOver.toScheme B S hS).map i')
        ((BigFppfOver.toScheme B S hS).map j') →
    (fiberSquareComparison p (p.chosenPullbacks) j i j' i' w.symm).Full ∧
      (fiberSquareComparison p (p.chosenPullbacks) j i j' i' w.symm).Faithful

/-- Condition (RS) implies its fully faithful half. -/
public theorem satisfiesRSFullyFaithful_of_satisfiesRS (hp : p.IsFiberedInGroupoids)
    (hRS : SatisfiesRS B S hS p hp) : SatisfiesRSFullyFaithful B S hS p hp := by
  intro X X' Y Y' i j i' j' w hX hX' hY hY' hX₁ hX₁' hY₁ hY₁' hi hpo
  let : p.IsFibered := hp.isFibered
  have := hRS i j i' j' w hX hX' hY hY' hX₁ hX₁' hY₁ hY₁' hi hpo
  exact ⟨inferInstance, inferInstance⟩

/-- Condition (RS) implies condition (RS) at the squares inducing surjections of residue
fields. -/
public theorem satisfiesRSOfResidue_of_satisfiesRS (hp : p.IsFiberedInGroupoids)
    (hRS : SatisfiesRS B S hS p hp) : SatisfiesRSOfResidue B S hS p hp :=
  fun i j i' j' w hX hX' hY hY' hX₁ hX₁' hY₁ hY₁' hi hpo _ =>
    hRS i j i' j' w hX hX' hY hY' hX₁ hX₁' hY₁ hY₁' hi hpo

end Deformation.Artin
