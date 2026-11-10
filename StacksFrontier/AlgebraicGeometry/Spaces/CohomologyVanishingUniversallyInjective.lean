module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.CohomologyVanishingBaseChangeGlobalFunctions
public import StacksFrontier.AlgebraicGeometry.Spaces.CohomologyVanishingClosedPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.CohomologyVanishingTensorStructureSheaf
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.ClosedPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.PointsOfFibresCardinality
public import StacksFrontier.AlgebraicGeometry.Spaces.DescendingProperties.SeparatedDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.ImageSystemProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.SeparationAxioms
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.UniversallyInjective
public import StacksFrontier.AlgebraicGeometry.Spaces.RightExactGlobalSectionsSeparated
public import StacksFrontier.AlgebraicGeometry.Spaces.SpectralPoints

/-!
# A space with vanishing first cohomology is universally injective over its spectrum

Let `X` be a quasi-compact, quasi-separated algebraic space over a scheme `S` all of whose
quasi-coherent modules have vanishing first cohomology — the data of Stacks 07UY — and write
`A = Γ(X, 𝒪_X)`.  **Stacks 07V4** says that the canonical morphism `p : X ⟶ Spec A` of
Stacks 05Z1 is universally injective.

The source reduces to two `K`-valued points `x, y` of `X` with the same image in `Spec A` and
base changes to `X_K = Spec K ×_{Spec A} X`, which is again in the situation of Stacks 07UY by
Stacks 07V0, with `Γ(X_K, 𝒪) = K`.  The two sections `(id, x)` and `(id, y)` of
`X_K ⟶ Spec K` are closed points of `|X_K|` by Stacks 07U5, and two distinct closed points would
be separated by a global function on `X_K`, by Stacks 07V1 — impossible for the elements of a
field.  So they coincide, and `x` and `y` agree after a common field extension.

## Main results

* `Space.CohomologyVanishingSituation.isAbsolutelyQuasiSeparated_spaceOverIntegers`:
  the view of `X` over `Spec ℤ` is quasi-separated.
* `Space.CohomologyVanishingSituation.universallyInjective_toSpecGlobalFunctionsOverIntegers`:
  **Stacks 07V4**, over an arbitrary base scheme.

## Implementation notes

*The view over `Spec ℤ`.*  As in the source, `p` is a morphism of algebraic spaces over `Spec ℤ`:
`Spec A` has no morphism to `S`, so Stacks forms `p` after regarding `X` as an algebraic space
over `ℤ`, and universal injectivity of `p` is universal injectivity over `Spec ℤ`, the notion of
Stacks 03MV for that base.  The view of `X` over `Spec ℤ`,
`AlgebraicGeometry.Space.CohomologyVanishingSituation.spaceOverIntegers`, has the same small
étale ringed site as `X` (`AlgebraicGeometry.Space.SmallEtale.relocalizeEquivalence`), so it has
the same global functions and right exact global sections on quasi-coherent modules
(`AlgebraicGeometry.Space.surjective_sectionsMap_relocalize`), and it is quasi-compact and
quasi-separated.  The statement is therefore deduced from the general
`AlgebraicGeometry.Space.universallyInjective_of_surjective_pullbackToGlobalFunctions`, which is
stated over an arbitrary base for any morphism to an affine object of the site inducing a
surjection on global functions, in
`StacksFrontier/AlgebraicGeometry/Spaces/RightExactGlobalSectionsSeparated.lean`.  Of the
computation
`Γ(X_K, 𝒪) = K` only the surjectivity of `K ⟶ Γ(X_K, 𝒪)` is used.

*How Stacks 07V0 enters.*  The cohomology hypothesis of Stacks 07UY is used through right
exactness of global sections on quasi-coherent modules, which it implies
(`Space.CohomologyVanishingSituation.surjective_sectionsMap_of_epi_of_isQuasicoherentOnSite`).
That property passes to `X_K`, which is affine over `X`
(`AlgebraicGeometry.Space.surjective_sectionsMap_of_isAffineHom`), and it is all that the
separation of closed sets of Stacks 07V1 needs
(`Space.exists_subset_compl_sectionSupport_of_disjoint_of_surjective_sectionsMap`).
The surjectivity of `K ⟶ Γ(X_K, 𝒪)` is
`AlgebraicGeometry.Space.surjective_pullbackToGlobalFunctions_of_isPullback`.

*The field-valued points.*  Universal injectivity is tested by Stacks 03MV in the form
`AlgebraicGeometry.Space.universallyInjective_of_fieldPoints`.  The source replaces `K` by an
algebraically closed field of large transcendence degree (Stacks 0488) in order to argue with the
`K`-points of `X_K`; this is not needed here, because the two points to be compared are already
`K`-rational sections of `X_K ⟶ Spec K`, and a common extension of two sections of
`X_K ⟶ Spec K` lies over a single morphism to `Spec K`.  For the same reason the closedness of
Stacks 07U5 is used in its form for a rational point of a space over the spectrum of a field,
`AlgebraicGeometry.Space.isClosed_singleton_class_of_comp_eq_id`; decency of `X_K` is its
quasi-separatedness, `X_K` being affine over the quasi-separated `X`.

*Presenting `Spec A`.*  `Spec A` is presented by an affine object `V` of the site over `Spec ℤ`
together with a ring isomorphism `Γ(V, 𝒪_V) ≅ A`, as in
`AlgebraicGeometry.Space.CohomologyVanishingSituation.toSpecGlobalFunctionsOverIntegers`; the
statement holds for every such presentation.  The situation is one at the module universe of the
structure sheaf, `CohomologyVanishingSituation.{u, u}`, the smallest module universe at which the
first cohomology of the small étale site exists.

## References

* [Stacks Project, Tag 07V4](https://stacks.math.columbia.edu/tag/07V4)
* [Stacks Project, Tag 07UY](https://stacks.math.columbia.edu/tag/07UY)
* [Stacks Project, Tag 07V0](https://stacks.math.columbia.edu/tag/07V0)
* [Stacks Project, Tag 07V1](https://stacks.math.columbia.edu/tag/07V1)
* [Stacks Project, Tag 07U5](https://stacks.math.columbia.edu/tag/07U5)
* [Stacks Project, Tag 05Z1](https://stacks.math.columbia.edu/tag/05Z1)
* [Stacks Project, Tag 03MV](https://stacks.math.columbia.edu/tag/03MV)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry

namespace Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

namespace CohomologyVanishingSituation

variable (T : CohomologyVanishingSituation.{u, u})

/-- `X` viewed over `Spec ℤ` is quasi-separated. -/
theorem isAbsolutelyQuasiSeparated_spaceOverIntegers :
    IsAbsolutelyQuasiSeparated T.site (⊤_ Scheme.{u}) T.containsTerminal T.containsTerminal
      T.spaceOverIntegers.1 :=
  isAbsolutelyQuasiSeparated_viewOverIntegers T.site T.base T.containsBase T.containsTerminal
    T.space.1 T.quasiSeparated

variable (V : BigFppfOver T.site (⊤_ Scheme.{u}) T.containsTerminal)
    [IsAffine ((BigFppfOver.toScheme T.site (⊤_ Scheme.{u}) T.containsTerminal).obj V)]
    (e : Γ((BigFppfOver.toScheme T.site (⊤_ Scheme.{u}) T.containsTerminal).obj V, ⊤) ≃+*
      T.globalFunctions)

/-- **Stacks 07V4.** In the situation of Stacks 07UY, over an arbitrary base scheme `S`, the
canonical morphism `p : X ⟶ Spec A` is universally injective.  As in the source, `p` is the
morphism of Stacks 05Z1 formed after regarding `X` as an algebraic space over `Spec ℤ`, and
`Spec A` is presented by an affine object `V` of the site through a ring isomorphism
`Γ(V, 𝒪_V) ≅ A = Γ(X, 𝒪_X)`.

The view of `X` over `Spec ℤ` has the same small étale ringed site, hence the same global
functions and right exact global sections, and it is quasi-compact and quasi-separated; the
statement is then
`AlgebraicGeometry.Space.universallyInjective_of_surjective_pullbackToGlobalFunctions`. -/
@[stacks 07V4]
theorem universallyInjective_toSpecGlobalFunctionsOverIntegers :
    _root_.AlgebraicGeometry.Space.UniversallyInjective T.site (⊤_ Scheme.{u}) T.containsTerminal
      (toSpecGlobalFunctionsOverIntegers T V e).hom :=
  universallyInjective_of_surjective_pullbackToGlobalFunctions T.containsTerminal
    T.surjective_sectionsMap_spaceOverIntegers T.isQuasiCompactSpace_spaceOverIntegers
    T.isAbsolutelyQuasiSeparated_spaceOverIntegers (toSpecGlobalFunctionsOverIntegers T V e)
    (surjective_pullbackToGlobalFunctions_toSpecGlobalFunctionsOverIntegers T V e)

end CohomologyVanishingSituation

end Space

end AlgebraicGeometry

end
