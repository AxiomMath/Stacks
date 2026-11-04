module

public import StacksFrontier.AlgebraicGeometry.Chow.AffineBundle.AffineSpaceBundleSmooth
public import StacksFrontier.AlgebraicGeometry.Chow.AffineBundle.LineBundleAffineSpaceBundle
public import StacksFrontier.AlgebraicGeometry.Divisors.CanonicalSectionZeroScheme
public import StacksFrontier.AlgebraicGeometry.Flatness.FiniteOverSmooth
public import StacksFrontier.AlgebraicGeometry.Picard.DivisorsOnSmoothCurves

/-!
# The zero section of a line bundle is a relative effective Cartier divisor

Let `ℒ` be an invertible module on a scheme `X` and let `p : L = \underline{\Spec}(\Sym^*(ℒ))
⟶ X` be its total space, with zero section `o : X ⟶ L` cut out by the augmentation
`\Sym^*(ℒ) ⟶ 𝒪_X`. This file proves that the image `o(X)`, presented by the quasi-coherent ideal
sheaf `Stacks.LineBundle.Situation.zeroSection.ker`, is a **relative effective Cartier divisor on
`L/X`** in the sense of Definition 062T — both conjuncts at once, so in particular `o(X)` is an
effective Cartier divisor on `L`.

The argument is the implication (1) implies (2) of [Stacks, Tag 0B9D]: a closed subscheme of a
scheme smooth of relative dimension one over a base which is finite locally free over that base
is a relative effective Cartier divisor. Both hypotheses are available for `o(X)`:

* `p` is smooth of relative dimension one, because it is an affine-space bundle of rank one
  (`Stacks.LineBundle.Situation.isAffineSpaceBundle_totalSpaceToBase`) and affine `1`-space over
  any base is smooth of relative dimension one;
* `o(X) ⟶ X` is an isomorphism, hence finite locally free, because `o` splits `p` and `o(X)` is
  the closed subscheme cut out by the closed immersion `o`.

## Main results

The smoothness of `p` (`Stacks.LineBundle.Situation.smoothOfRelativeDimension_totalSpaceToBase`)
and the relative effective Cartier property of `o(X)`
(`Stacks.LineBundle.Situation.isRelativeEffectiveCartierDivisor_ker_zeroSection`, [Stacks,
Tag 062T]) are in `StacksFrontier.AlgebraicGeometry.Chow.AffineBundle.AffineSpaceBundleSmooth`.

* `Stacks.LineBundle.Situation.isIso_ker_zeroSection_subschemeι_comp_totalSpaceToBase`: the
  structure morphism of `o(X)` over `X` is an isomorphism.
* `Stacks.LineBundle.Situation.isEffectiveCartierDivisor_ker_zeroSection`: **`o(X)` is an
  effective Cartier divisor on `L`.**
* `Stacks.LineBundle.Situation.zeroScheme_divisorSheafGlobalSection_ker_zeroSection` and
  `Stacks.LineBundle.Situation.ker_zeroSection_eq_zeroScheme`: `o(X)` is the zero scheme of a
  global section of an invertible module on `L`, namely the canonical section of `𝒪_L(o(X))`.

## Implementation notes

The ring-theoretic input, that a polynomial ring in `r` variables is standard smooth of relative
dimension `r`, is `Stacks.Flatness.isStandardSmoothOfRelativeDimension_mvPolynomial`, and its
geometric form over an affine base is `Stacks.Flatness.smoothOfRelativeDimension_SpecMap_C`.
Those are stated for the index type `Fin r`, while `AlgebraicGeometry.AffineSpace` is indexed by
a type in the same universe as the schemes; the transport along
`MvPolynomial.renameEquiv _ Equiv.ulift.symm` is the only step that mediates between the two.

Passing from an affine base to an arbitrary one is not done by localizing the statement: the
integral model is used instead, exactly as Mathlib's own instances for `𝔸(n; S) ↘ S` do.
`𝔸(n; S) ↘ S` is by construction the first projection of the pullback of `S ⟶ \Spec ℤ` along
`\Spec ℤ[n] ⟶ \Spec ℤ`, the terminal morphism out of `\Spec ℤ` is an isomorphism, and smoothness
of a given relative dimension is stable under base change. The instance
`MorphismProperty.IsStableUnderBaseChangeAlong` has to be supplied by hand from
`AlgebraicGeometry.smoothOfRelativeDimension_isStableUnderBaseChange`, which is a lemma and not
an instance, and likewise `IsZariskiLocalAtTarget` from
`AlgebraicGeometry.HasRingHomProperty.instIsZariskiLocalAtTarget`: instance search does not find
the `HasRingHomProperty` of `SmoothOfRelativeDimension` on its own, the associated ring-hom
property not being an output parameter. The same discipline is used by
`Stacks.Chow.flat_of_isAffineSpaceBundle`.

That `o(X) ⟶ X` is an isomorphism is the computation already performed inside
`Stacks.Chow.flat_ker_zeroSection_subschemeι_comp_totalSpaceToBase`, which deduces only
flatness from it; it is isolated here because finite local freeness, not flatness, is what
[Stacks, Tag 0B9D] asks for.

## Which part of Tag 0F96 this file carries, and which it does not

Clause (1) of [Stacks, Tag 0F96] asserts that `o(X)` is the zero scheme of a regular global
section of `p^*ℒ^{⊗ -1}` — that specific invertible module, and the specific section of the
source's proof, which is the tautological section
`Stacks.LineBundle.Situation.tautologicalSectionBase`. The zero-scheme presentation proved here
presents `o(X)` as the zero scheme of the canonical section of `𝒪_L(o(X))` instead, a module
built out of `o(X)` itself; it identifies no external module and is therefore **not** clause (1)
in the source's form.

What this file *does* register of the tag is the relative-effective-Cartier half of clause (1):
`Stacks.LineBundle.Situation.isRelativeEffectiveCartierDivisor_ker_zeroSection` carries
`@[stacks 0F96 "(1), the zero section is a relative effective Cartier divisor"]`. That is one of
the two inputs the full clause consumes, as the next paragraph records.

Clause (1) itself is
`Stacks.LineBundle.Situation.zeroScheme_tautologicalSectionBase_eq_ker_zeroSection` together with
`Stacks.LineBundle.Situation.isRegularSection_tautologicalSectionBase`, in
`StacksFrontier.AlgebraicGeometry.DeRham.LineBundle.ZeroSectionZeroScheme` and
`StacksFrontier.AlgebraicGeometry.DeRham.LineBundle.TautologicalSectionBaseRegular`. It takes the
effective Cartier property proved here as one of its two inputs: regularity of the section is the
zero scheme being an effective Cartier divisor, by [Stacks, Tag 02OR] (4). The other input is the
**universal property of the total space**, an equivalence

`(Y ⟶ L) ≃ Σ g : Y ⟶ X, (ℒ ⟶ g_* 𝒪_Y)`,

natural in `Y` and sending `o` to the zero module map, which is
`Stacks.LineBundle.Situation.totalSpaceHomEquiv` of
`StacksFrontier.AlgebraicGeometry.DeRham.LineBundle.TotalSpaceUniversal`, assembled from the
representability of a relative spectrum (`Stacks.RelativeSpec.relativeSpecRepresentableBy`,
[Stacks, Tag 01LV]) and the ungraded universal property of the symmetric algebra sheaf
(`Stacks.RelativeSpec.ungradedAlgebraSheafModuleHomEquiv`). No description of the tautological
section over a chart of the relative spectrum is needed.

## References

* [Stacks Project, Tag 0B9D](https://stacks.math.columbia.edu/tag/0B9D)
* [Stacks Project, Tag 062T](https://stacks.math.columbia.edu/tag/062T)
* [Stacks Project, Tag 01WR](https://stacks.math.columbia.edu/tag/01WR)
* [Stacks Project, Tag 02OQ](https://stacks.math.columbia.edu/tag/02OQ)
* [Stacks Project, Tag 01M2](https://stacks.math.columbia.edu/tag/01M2)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.LineBundle

variable (D : Situation.{u})

/-- **The structure morphism of the image of the zero section over the base is an
isomorphism.** The zero section `o : X ⟶ L` is a closed immersion with the same kernel ideal
sheaf as the inclusion of the closed subscheme that ideal cuts out, so the comparison of the two
is an isomorphism; and it coincides with the structure morphism because `o` splits `p`. -/
theorem Situation.isIso_ker_zeroSection_subschemeι_comp_totalSpaceToBase :
    IsIso (D.zeroSection.ker.subschemeι ≫ D.totalSpaceToBase) := by
  have he := IsClosedImmersion.isIso_lift D.zeroSection D.zeroSection.ker.subschemeι
    (Scheme.IdealSheafData.ker_subschemeι D.zeroSection.ker).symm
  have hrw : D.zeroSection.ker.subschemeι ≫ D.totalSpaceToBase =
      IsClosedImmersion.lift D.zeroSection D.zeroSection.ker.subschemeι
        (Scheme.IdealSheafData.ker_subschemeι D.zeroSection.ker).ge :=
    calc D.zeroSection.ker.subschemeι ≫ D.totalSpaceToBase
        = (IsClosedImmersion.lift D.zeroSection D.zeroSection.ker.subschemeι
            (Scheme.IdealSheafData.ker_subschemeι D.zeroSection.ker).ge ≫ D.zeroSection) ≫
              D.totalSpaceToBase := by rw [IsClosedImmersion.lift_fac]
      _ = IsClosedImmersion.lift D.zeroSection D.zeroSection.ker.subschemeι
            (Scheme.IdealSheafData.ker_subschemeι D.zeroSection.ker).ge := by
          rw [Category.assoc, D.zeroSection_comp_totalSpaceToBase, Category.comp_id]
  rw [hrw]
  exact he

/-- **The image of the zero section of a line bundle is an effective Cartier divisor on the
total space** ([Stacks, Tag 01WR]): the first conjunct of Definition 062T for it. -/
theorem Situation.isEffectiveCartierDivisor_ker_zeroSection :
    Stacks.Divisors.IsEffectiveCartierDivisor D.zeroSection.ker :=
  D.isRelativeEffectiveCartierDivisor_ker_zeroSection.1

/-- **The image of the zero section of a line bundle is cut out by a global section of an
invertible module on the total space**: it is the zero scheme ([Stacks, Tag 02OQ]) of the
canonical section of the invertible module `𝒪_L(o(X))` attached to it.

The invertible module here is built from `o(X)` itself and is not the module
`p^*ℒ^{⊗ -1}` of clause (1) of [Stacks, Tag 0F96]; see the module documentation. -/
theorem Situation.zeroScheme_divisorSheafGlobalSection_ker_zeroSection :
    letI := D.isEffectiveCartierDivisor_ker_zeroSection
    AlgebraicGeometry.zeroScheme D.totalSpace
        (Stacks.Divisors.divisorSheaf D.zeroSection.ker)
        (Stacks.Divisors.divisorSheafGlobalSection D.zeroSection.ker) =
      D.zeroSection.ker :=
  let := D.isEffectiveCartierDivisor_ker_zeroSection
  Stacks.Divisors.zeroScheme_canonicalSection _

/-- **The image of the zero section of a line bundle is a zero scheme**, in the shape the
consumers of [Stacks, Tag 02TO] and [Stacks, Tag 02TR] on Chow groups take their divisor: the
triple `(𝒪_L(o(X)), 1_{o(X)}, o)` presents `o(X)`. This is
`Stacks.LineBundle.Situation.zeroScheme_divisorSheafGlobalSection_ker_zeroSection` read the
other way round. -/
theorem Situation.ker_zeroSection_eq_zeroScheme :
    letI := D.isEffectiveCartierDivisor_ker_zeroSection
    D.zeroSection.ker =
      Stacks.Divisors.zeroScheme D.totalSpace
        (Stacks.Divisors.divisorSheaf D.zeroSection.ker)
        (Stacks.Divisors.divisorSheafGlobalSection D.zeroSection.ker) :=
  D.zeroScheme_divisorSheafGlobalSection_ker_zeroSection.symm

end Stacks.LineBundle

end
