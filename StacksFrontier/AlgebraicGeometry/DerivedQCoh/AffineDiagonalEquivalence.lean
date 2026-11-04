module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.AffineOpenPushforward
public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.ComparisonEquivalence
public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.DerivedCoherator

/-!
# The derived category of quasi-coherent modules on a scheme with affine diagonal

Let `X` be a scheme. [Stacks, Tag 06VT] provides the comparison functor
`i_X : D(QCoh(𝒪_X)) ⥤ D_QCoh(𝒪_X)` from the derived category of the quasi-coherent modules to
the complexes of `𝒪_X`-modules with quasi-coherent cohomology. This file proves the two
assertions that make that functor useful:

* [Stacks, Tag 09T6]: if for every affine open `U ⊆ X` the derived direct image of quasi-coherent
  modules fits into the square `i_X ∘ Φ ≅ Rj_* ∘ i_U`, then `i_X` is an equivalence;
* [Stacks, Tag 08DB]: for a quasi-compact scheme with affine diagonal `i_X` is an equivalence,
  with quasi-inverse the derived coherator `RQ_X`.

The first is the dévissage of
`StacksFrontier/AlgebraicGeometry/DerivedQCoh/ComparisonEquivalence.lean` fed with the derived
coherator of `StacksFrontier/AlgebraicGeometry/DerivedQCoh/DerivedCoherator.lean`, after replacing
the arbitrary models `Rj_*` and `Φ` of derived direct image supplied by the hypothesis with the
chosen ones, which is legitimate because a total right derived functor is unique up to a unique
natural isomorphism. The second specialises it: a scheme with affine diagonal is quasi-separated,
and `Stacks.DerivedQCoh.affineOpenPushforwardCompatible` verifies the hypothesis of
[Stacks, Tag 09T6] there. The quasi-inverse is then read off from
`Stacks.DerivedQCoh.derivedCoherator_isoInv`, which identifies the inverse of the comparison
functor with any total right derived functor of the coherator.

## Main definitions

* `Stacks.DerivedQCoh.coheratorDerivedAdjunction` — the derived coherator of an arbitrary scheme
  presented as a right adjoint of `D(ι)`, which is the shape the dévissage consumes.

## Main results

* `Stacks.DerivedQCoh.quasiSeparatedSpace_of_affineDiagonal` — a scheme with affine diagonal is
  quasi-separated.
* `Stacks.DerivedQCoh.derivedQuasicoherentComparison_isEquivalence_of_compatible` —
  **[Stacks, Tag 09T6], equivalence clause.**
* `Stacks.DerivedQCoh.derivedQuasicoherentComparison_isEquivalence_of_affineDiagonal` —
  **[Stacks, Tag 08DB]**: the comparison functor is an equivalence on a quasi-compact scheme with
  affine diagonal.
* `Stacks.DerivedQCoh.derivedCoherator_isoInv_of_affineDiagonal` — **[Stacks, Tag 08DB]**, the
  quasi-inverse: it is the derived coherator restricted to the complexes with quasi-coherent
  cohomology.

## Implementation notes

The derived categories are the locally small ones; see the implementation notes of
`StacksFrontier/AlgebraicGeometry/DerivedQCoh/SupportedDevissage.lean`. In particular the free
`HasDerivedCategory.{w}` binders of
`Stacks.DerivedQCoh.AffineOpenPushforwardCompatible` are taken at `w := u`, by the global
instances `SheafOfModules.hasDerivedCategory` and
`Stacks.DerivedQCoh.hasDerivedCategoryQuasicoherent`. This is forced: the affine base case
`Stacks.DerivedQCoh.derivedQuasicoherentComparison_isEquivalence_of_isAffine` of the dévissage is
available at that model alone.

**The support hypothesis.** The dévissage triangle of
`Stacks.DerivedQCoh.exists_derivedRestriction_triangle` needs to know that derived direct image
along the inclusion of an open subscheme carries a complex supported on the preimage of a closed
`T ⊆ X` to a complex supported on `T` — the open-immersion case of [Stacks, Tag 08DF]. It is
discharged by `Stacks.DerivedQCoh.cohomologySupportedOn_derivedPushforward_scheme`, so the
theorems below have no hypothesis beyond their geometric ones.

## References

* [Stacks Project, Tag 08DB](https://stacks.math.columbia.edu/tag/08DB)
* [Stacks Project, Tag 09T6](https://stacks.math.columbia.edu/tag/09T6)
* [Stacks Project, Tag 06VT](https://stacks.math.columbia.edu/tag/06VT)
* [Stacks Project, Tag 077P](https://stacks.math.columbia.edu/tag/077P)
* [Stacks Project, Tag 08DF](https://stacks.math.columbia.edu/tag/08DF)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for `R`-modules.
-- `D(R)` for sheaves of modules on a small site.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] ModuleCat.hasDerivedCategory
attribute [local instance] SheafOfModules.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.AlgebraicGeometry.QuasicoherentDerived

universe u

namespace Stacks.DerivedQCoh

/-! ### The derived coherator as a right adjoint of the derived inclusion -/

/-- **The derived coherator of an arbitrary scheme as a right adjoint.** The functor
`D(ι) : D(QCoh(𝒪_X)) ⥤ D(𝒪_X)` induced by the exact inclusion of the quasi-coherent modules is
left adjoint to `Stacks.DerivedQCoh.derivedCoheratorOfScheme`.

This is `Stacks.DerivedQCoh.derivedCoheratorAdjunction` — [Stacks, Tag 09T5] for the coherator
adjunction of [Stacks, Tag 077P] — transported along
`Stacks.DerivedQCoh.derivedFunctorOfExactIsoMapDerivedCategory`, which identifies the
arbitrary-model induced functor of an exact functor with
`CategoryTheory.Functor.mapDerivedCategory`. -/
@[sga "6 II 3.3" "more general"]
def coheratorDerivedAdjunction (X : Scheme.{u}) :
    (SheafOfModules.isQuasicoherent X.ringCatSheaf).ι.mapDerivedCategory ⊣
      derivedCoheratorOfScheme X :=
  (derivedCoheratorAdjunction X (derivedCoheratorOfScheme X)
    (derivedCoheratorOfSchemeUnit X)).ofNatIsoLeft
    (derivedFunctorOfExactIsoMapDerivedCategory (SheafOfModules.isQuasicoherent X.ringCatSheaf).ι)

/-! ### Affine diagonal and quasi-separatedness -/

/-- **A scheme with affine diagonal is quasi-separated.** An affine morphism is quasi-compact, so
a scheme whose diagonal over the terminal scheme is affine has quasi-compact diagonal, which is
quasi-separatedness of its structure morphism and hence of its space. -/
theorem quasiSeparatedSpace_of_affineDiagonal (X : Scheme.{u})
    [IsAffineHom (pullback.diagonal (terminal.from X))] : QuasiSeparatedSpace X :=
  (quasiSeparatedSpace_iff_quasiSeparated X).2 ⟨inferInstance⟩

/-! ### The equivalence clause of Stacks 09T6 -/

/-- **[Stacks, Tag 09T6], equivalence clause.** Let `X` be a quasi-compact quasi-separated scheme
satisfying `Stacks.DerivedQCoh.AffineOpenPushforwardCompatible`: for every affine open `U ⊆ X`
the right derived functor `Φ` of `j_* : QCoh(𝒪_U) ⥤ QCoh(𝒪_X)` fits into the commutative square
`i_X ∘ Φ ≅ Rj_* ∘ i_U`. Then the comparison functor `i_X` of [Stacks, Tag 06VT] is an
equivalence.

The hypothesis names arbitrary models of the two derived functors; a total right derived functor
is unique up to a unique natural isomorphism, so
`Stacks.DerivedQCoh.derivedPushforwardIsoOfCochainUnit` and
`Stacks.DerivedQCoh.derivedQuasicoherentPushforwardIsoOfCochainUnit` move the square to the
chosen models, where `Stacks.DerivedQCoh.derivedQuasicoherentComparison_isEquivalence_of_square`
runs the dévissage of the source on the derived coherator
`Stacks.DerivedQCoh.coheratorDerivedAdjunction`. -/
@[stacks 09T6 "equivalence clause"]
theorem derivedQuasicoherentComparison_isEquivalence_of_compatible (X : Scheme.{u})
    [CompactSpace X] [QuasiSeparatedSpace X]
    (h : AffineOpenPushforwardCompatible.{u, u} X) :
    (derivedQuasicoherentComparison.{u} X).IsEquivalence := by
  refine derivedQuasicoherentComparison_isEquivalence_of_square X
    (fun Z => ⟨derivedCoheratorOfScheme Z, ⟨coheratorDerivedAdjunction Z⟩⟩) ?_
  intro U hU _ _
  obtain ⟨Rj, ηj, Φ, ηΦ, hRj, hΦ, ⟨e⟩⟩ := h U hU
  have eRj : Rj ≅ Stacks.Duality.derivedPushforward U.ι :=
    @derivedPushforwardIsoOfCochainUnit _ _ U.ι Rj ηj hRj
  have eΦ : Φ ≅ derivedQuasicoherentPushforward U.ι :=
    @derivedQuasicoherentPushforwardIsoOfCochainUnit _ _ U.ι _ _ Φ ηΦ hΦ
  exact ⟨Functor.isoWhiskerRight eΦ.symm _ ≪≫ e ≪≫
    Functor.isoWhiskerLeft _ (Functor.isoWhiskerLeft _ eRj)⟩

/-! ### Stacks 08DB -/

/-- **[Stacks, Tag 08DB].** Let `X` be a quasi-compact scheme with affine diagonal. Then the
comparison functor `i_X : D(QCoh(𝒪_X)) ⥤ D_QCoh(𝒪_X)` of [Stacks, Tag 06VT] is an equivalence.

A scheme with affine diagonal is quasi-separated, and the inclusion of one of its affine opens is
an affine morphism, so the square of [Stacks, Tag 09T6] is the square of [Stacks, Tag 08D7]; that
is `Stacks.DerivedQCoh.affineOpenPushforwardCompatible`, which discharges the hypothesis of
`Stacks.DerivedQCoh.derivedQuasicoherentComparison_isEquivalence_of_compatible`. -/
@[stacks 08DB "equivalence"]
theorem derivedQuasicoherentComparison_isEquivalence_of_affineDiagonal (X : Scheme.{u})
    [CompactSpace X] [IsAffineHom (pullback.diagonal (terminal.from X))] :
    (derivedQuasicoherentComparison.{u} X).IsEquivalence :=
  have := quasiSeparatedSpace_of_affineDiagonal X
  derivedQuasicoherentComparison_isEquivalence_of_compatible X
    (affineOpenPushforwardCompatible X)

/-- **[Stacks, Tag 08DB], the quasi-inverse.** On a quasi-compact scheme with affine diagonal the
quasi-inverse of the comparison functor of [Stacks, Tag 06VT] is the derived coherator `RQ_X`,
restricted to the complexes with quasi-coherent cohomology.

The comparison functor is an equivalence by
`Stacks.DerivedQCoh.derivedQuasicoherentComparison_isEquivalence_of_affineDiagonal`, and
`Stacks.DerivedQCoh.derivedCoherator_isoInv` — the quasi-inverse clause of [Stacks, Tag 09T6] —
identifies the inverse of an equivalent comparison functor with any total right derived functor
of the coherator, here `Stacks.DerivedQCoh.derivedCoheratorOfScheme`. -/
@[stacks 08DB "quasi-inverse"]
def derivedCoherator_isoInv_of_affineDiagonal (X : Scheme.{u})
    [CompactSpace X] [IsAffineHom (pullback.diagonal (terminal.from X))] :
    letI := derivedQuasicoherentComparison_isEquivalence_of_affineDiagonal X
    (DerivedCategoryB.derivedCategoryB
        (SheafOfModules.isQuasicoherent X.ringCatSheaf)).ι ⋙ derivedCoheratorOfScheme X ≅
      (derivedQuasicoherentComparison.{u} X).inv :=
  letI := derivedQuasicoherentComparison_isEquivalence_of_affineDiagonal X
  derivedCoherator_isoInv X (derivedCoheratorOfScheme X) (derivedCoheratorOfSchemeUnit X)

end Stacks.DerivedQCoh

end
