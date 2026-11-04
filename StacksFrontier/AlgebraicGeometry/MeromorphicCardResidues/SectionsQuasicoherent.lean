module

public import StacksFrontier.AlgebraicGeometry.MeromorphicQuasicoherent.Criteria
public import StacksFrontier.AlgebraicGeometry.QcohLimits.RestrictScalars
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Quasi-coherence of the sheaf of meromorphic sections, modulo one named input

Tag 02OW part (2) and Tag 0EMH assert that the sheaf `𝒦_X(F)` of meromorphic sections of a
quasi-coherent `𝒪_X`-module `F` is quasi-coherent as an `𝒪_X`-module. By definition (Tag 01X4)
`𝒦_X(F)` is the extension of scalars of `F` along `𝒪_X ⟶ 𝒦_X`, regarded as an `𝒪_X`-module
again by restriction of scalars, so Tag 0H88 applies: its hypothesis is exactly quasi-coherence
of `𝒦_X` as an `𝒪_X`-module, which is Tag 02OW part (1) and the corresponding clause of Tag
0EMH, both proved.

This file records the resulting reduction. Its content is that the *only* remaining input is

> extension of scalars along `𝒪_X ⟶ 𝒦_X` takes a quasi-coherent `𝒪_X`-module to a
> `𝒦_X`-module which is quasi-coherent over `𝒦_X`,

carried below as the hypothesis `hext`, and that Tag 0H88 is an *equivalence*, so for this
single instance `hext` is not weaker than the conclusion: what has to be proved is the general
statement that extension of scalars preserves quasi-coherence, not this instance of it.

## Main results

* `isQuasicoherent_meromorphicSections_iff`: Tag 0H88 at `𝒪_X ⟶ 𝒦_X`. The sheaf of meromorphic
  sections of `F` is quasi-coherent as an `𝒪_X`-module if and only if it is quasi-coherent over
  `𝒦_X`, given quasi-coherence of `𝒦_X`.
* `isQuasicoherent_meromorphicSections_of_noEmbeddedPoints` and
  `isQuasicoherent_meromorphicSections_of_isReduced`: the assertions of Tag 0EMH and of Tag
  02OW part (2), with `hext` as the single added hypothesis. Because `hext` is a hypothesis
  neither tag carries, there is no covering set and neither tag is attached here.

## Implementation notes

No tag is claimed. The added hypothesis `hext` is exactly what a covering set may not contain.

Two inputs to `hext` are already available and are recorded here only in prose, since neither
needs a new declaration. Extension of scalars for sheaves of modules is left adjoint to
restriction of scalars — `Stacks.Sheaves.ChangeOfRings.extensionRestrictionAdjunction`, which is
the same functor as `Stacks.Sheaves.ChangeOfRings.changeOfRings` used by
`AlgebraicGeometry.meromorphicSectionSheaf` — so it preserves all colimits, which is the half of
a `SheafOfModules.Presentation.map` argument concerning cokernels and coproducts of copies of
the structure sheaf. What is missing is the other half: the comparison of extension of scalars
with restriction to an open, that is an isomorphism
`(𝒦_X ⊗_{𝒪_X} F)|_U ≅ 𝒦_U ⊗_{𝒪_U} (F|_U)`, needed because `SheafOfModules.QuasicoherentData`
presents the module on each member of a covering. For *restriction* of scalars that comparison
is `rfl` (`Stacks.AlgebraicGeometry.QcohOverAlgebra.restrictScalars_comp_overFunctor`); for
extension of scalars it is not, because sheafification intervenes.

## References

* [The Stacks Project, Tag 02OW](https://stacks.math.columbia.edu/tag/02OW)
* [The Stacks Project, Tag 0EMH](https://stacks.math.columbia.edu/tag/0EMH)
* [The Stacks Project, Tag 0H88](https://stacks.math.columbia.edu/tag/0H88)
* [The Stacks Project, Tag 01X4](https://stacks.math.columbia.edu/tag/01X4)
-/

@[expose] public noncomputable section

open CategoryTheory Limits TopologicalSpace
open AlgebraicGeometry

open scoped AlgebraicGeometry

universe u

namespace Stacks.AlgebraicGeometry.MeromorphicCardResidues

open Stacks.AlgebraicGeometry.GenericPointDecomposition

variable (X : Scheme.{u})

/-- **Stacks Tag 0H88 at the canonical morphism `𝒪_X ⟶ 𝒦_X`.** Given that the sheaf of
meromorphic functions is quasi-coherent as an `𝒪_X`-module, the sheaf of meromorphic sections of
an `𝒪_X`-module `F` is quasi-coherent as an `𝒪_X`-module if and only if it is quasi-coherent as
a module over the sheaf of total quotient rings.

Both directions hold, so the extension-of-scalars statement on the right is not a weakening of
the one on the left. -/
theorem isQuasicoherent_meromorphicSections_iff
    (hK : (meromorphicFunctions X).IsQuasicoherent) (F : X.Modules) :
    (meromorphicSections X F).IsQuasicoherent ↔
      (meromorphicSectionSheaf X.sheaf F).IsQuasicoherent :=
  QcohLimits.isQuasicoherent_restrictScalars_iff (toTotalQuotientRingCatSheaf X) hK _

/-- **Stacks Tag 0EMH, quasi-coherence of meromorphic sections, modulo `hext`.** On a locally
Noetherian scheme without embedded points, the sheaf of meromorphic sections of an `𝒪_X`-module
`F` is quasi-coherent, provided the extension of scalars of `F` to the sheaf of total quotient
rings is quasi-coherent over that sheaf of rings.

`hext` is a hypothesis the tag does not carry, so this is not a covering set for the tag. -/
theorem isQuasicoherent_meromorphicSections_of_noEmbeddedPoints [IsLocallyNoetherian X]
    (hX : _root_.AlgebraicGeometry.HasNoEmbeddedPoints X) (F : X.Modules)
    (hext : (meromorphicSectionSheaf X.sheaf F).IsQuasicoherent) :
    (meromorphicSections X F).IsQuasicoherent :=
  (isQuasicoherent_meromorphicSections_iff X
    (MeromorphicQuasicoherent.meromorphicFunctions_isQuasicoherent_of_noEmbeddedPoints X hX)
    F).mpr hext

/-- **Stacks Tag 02OW part (2), quasi-coherence, modulo `hext`.** On a reduced scheme whose
quasi-compact opens have finitely many irreducible components, the sheaf of meromorphic sections
of an `𝒪_X`-module `F` is quasi-coherent, provided the extension of scalars of `F` to the sheaf
of total quotient rings is quasi-coherent over that sheaf of rings.

`hext` is a hypothesis the tag does not carry, so this is not a covering set for the tag. -/
@[ega "II 6.4.10" "partial"]
theorem isQuasicoherent_meromorphicSections_of_isReduced [IsReduced X]
    (hfinite : GenericPointProduct.FiniteComponentsOnCompactOpens X) (F : X.Modules)
    (hext : (meromorphicSectionSheaf X.sheaf F).IsQuasicoherent) :
    (meromorphicSections X F).IsQuasicoherent :=
  (isQuasicoherent_meromorphicSections_iff X
    (MeromorphicQuasicoherent.meromorphicFunctions_isQuasicoherent X hfinite) F).mpr hext

end Stacks.AlgebraicGeometry.MeromorphicCardResidues

end
