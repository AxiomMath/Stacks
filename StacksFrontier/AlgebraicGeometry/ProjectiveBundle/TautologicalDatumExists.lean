module

public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.BundleBaseChange
public import StacksFrontier.AlgebraicGeometry.Morphisms.Projective.BaseChange
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundle.Sections
public import StacksFrontier.AlgebraicGeometry.RelativeProjDegreeOne.Tautological
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The projective bundle of any quasi-coherent module carries a tautological datum

A tautological datum on `𝐏(F)`, `Stacks.RelativeProj.TautologicalDatum`, is an invertible module
on `𝐏(F)` together with a surjection onto it from `π^*F`. On `𝐏(F)` it is `𝒪_{𝐏(F)}(1)` with the
universal surjection of Tag 01O4, and it is the datum that the forward direction of Tag 0B3V's
bijection consumes.

**This file produces one for an arbitrary quasi-coherent `F` on an arbitrary scheme.** Both of
its ingredients are available, on the *other* of this repository's two projective-bundle substrates:
`Stacks.ProjectiveBundleSplitting.tautologicalTwist` is `𝒪(1)` on
`Stacks.SymGraded.schemeProjectiveBundle`, invertible by
`Stacks.ProjectiveBundleSplitting.isInvertible_tautologicalTwist`, and
`Stacks.ProjectiveBundleSplitting.tautologicalMap` is the surjection onto it, epi by
`Stacks.ProjectiveBundleSplitting.epi_tautologicalMap`. What this file adds is the transport of
that pair to `Stacks.RelativeProj.projectiveBundle` along
`Stacks.ProjectiveBundle.presentationIso`, the named comparison of the two substrates over the
base.

## Main definitions

* `Stacks.RelativeProj.bundlePresentationIso`: the comparison `𝐏_{SymGraded}(F) ≅ 𝐏(F)` over the
  base, named.
* `Stacks.RelativeProj.tautologicalDatumTwist`: `𝒪_{𝐏(F)}(1)`, the comparison's pullback of the
  existing twist.
* `Stacks.RelativeProj.tautologicalDatumUniv`: the surjection `π^*F ⟶ 𝒪_{𝐏(F)}(1)`.
* `Stacks.RelativeProj.tautologicalDatum`: **the tautological datum of `𝐏(F)`, for every
  quasi-coherent `F`, with no hypothesis on its rank.**

## Main results

* `Stacks.RelativeProj.bundlePresentationIso_inv_comp_toBase`: the comparison's inverse carries
  the one projection to the other, which is what makes the transported surjection a map out of
  `π^*F` for `π` the projection of `Stacks.RelativeProj.projectiveBundle`.
* `Stacks.RelativeProj.epi_tautologicalDatumUniv`: the transported surjection is surjective.

## What this settles, and what it does not

The implementation notes of `StacksFrontier/AlgebraicGeometry/ProjectiveBundle/Sections.lean` and of
`StacksFrontier/AlgebraicGeometry/ProjectiveBundle/TautologicalInvertible.lean` state that
`TautologicalDatum` is inhabited for an invertible `F` and for no other rank, and price the
general case at a twist of a relative `Proj` *situation*. That price is no longer owed: the twist
exists on the `SheafGradedAlgebra` substrate and the two substrates are now known to agree over
the base, so the datum transports. The notes are corrected in place.

Consequently the forward direction of Tag 0B3V's bijection —
`Stacks.RelativeProj.TautologicalDatum.pullbackQuotient`, the invertible quotient of `F` that a
section of `π` pulls back from `𝒪(1)` — is available for **every** quasi-coherent module on every
scheme, with no hypothesis.

**`Stacks.RelativeProj.TautologicalDatum.IsUniversal` remains a gap and is untouched here.** That
is the assertion that the forward map is bijective, which is the mapping-in half of the universal
property of relative `Proj` (Tag 01O4, Constructions Lemma 27.16.11); this file supplies the
datum the assertion is *about*, not the assertion. See the `Not done here` section.

## Implementation notes

**The comparison isomorphism is named, not chosen.**
`AlgebraicGeometry.projectiveBundlePresentationsAgree` is an existence statement with no
uniqueness clause, so a witness chosen from it is an opaque function of the module: two
witnesses differ by an automorphism of `𝐏(F)` over `X`, nothing pins which one
`Exists.choose` returns, and consequently *no* relation between the witness at `F` and the
witness at a pullback `g^*F` is provable. That is fatal for the base-change clause of Tag 0B3V,
because an automorphism of `𝐏(F)` over `X` does not in general carry the universal quotient to
the universal quotient, so the datum built from a chosen witness is not even isomorphic, as a
datum, to the one built at `g^*F`.

`Stacks.ProjectiveBundle.presentationIso` is used instead. It is a witness for the same
existential (its spec is `Stacks.ProjectiveBundle.presentationIso_hom_toBase`), so nothing below
changes, but it is *named* and it comes with its formula on charts,
`Stacks.ProjectiveBundle.chart_presentationIso_hom`. That formula is what makes the comparison
computable across a base change, and
`StacksFrontier/AlgebraicGeometry/ProjectiveBundle/TautologicalDatumBaseChange.lean` uses it to
identify the base change of the datum built here with the datum built here at `g^*F`.

**The transport is three comparison isomorphisms and one functor action**, in the same shape as
`Stacks.RelativeProj.TautologicalDatum.pullbackQuotientMap`: `pullbackCongr` moves
`π` to `b⁻¹ ≫ π'`, `pullbackComp` splits that pullback into the two, and the twist map is then
carried along by `Scheme.Modules.pullback b⁻¹`. Surjectivity survives because the two comparisons
are isomorphisms and `Scheme.Modules.pullback b⁻¹`, being a left adjoint, preserves epimorphisms.

**Quasi-coherence of the homogeneous pieces is discharged, not assumed.**
`Stacks.SymGraded.IsQuasicoherentPieces` is a `Prop`, so by proof irrelevance the bundle and the
twist built from `Stacks.SymGraded.isQuasicoherentPieces_of_isQuasicoherent F` are the same terms
as those built from any other proof, and no transport along a change of that argument appears.

## Not done here

**No `@[stacks]` attribute is attached.** Tag 01OB defines `𝒪_{𝐏(F)}(1)` and Tag 01O4 asserts its
universal surjection to be universal; this file transports an existing twist and surjection
from one presentation of `𝐏(F)` to another, which is neither tag's statement nor a covering part
of one. Tag 0B3V's bijection is not reached either: it needs `IsUniversal`.

## References

* [Stacks Project, Tag 0B3V](https://stacks.math.columbia.edu/tag/0B3V)
* [Stacks Project, Tag 01OB](https://stacks.math.columbia.edu/tag/01OB)
* [Stacks Project, Tag 01O4](https://stacks.math.columbia.edu/tag/01O4)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.SymGraded

universe u

namespace Stacks.RelativeProj

variable {X : Scheme.{u}} (F : X.Modules) [F.IsQuasicoherent]

/-- **The `SheafGradedAlgebra` presentation of the projective bundle of `F`**, with the
quasi-coherence of the homogeneous pieces discharged. This is
`Stacks.SymGraded.schemeProjectiveBundle` with its hypothesis filled in, written at the
`Stacks.AlgebraicGeometry.RelativeProj.relativeProj` spelling that the twist and
tautological map of `Stacks.ProjectiveBundleSplitting` are stated at, and reducible so that
instance search sees the two as one. -/
@[ega "II 4.1.1"]
abbrev symGradedBundle : Stacks.AlgebraicGeometry.RelativeProj.RelativeProjData
    (schemeSheafGradedAlgebra F (isQuasicoherentPieces_of_isQuasicoherent F)) :=
  Stacks.AlgebraicGeometry.RelativeProj.relativeProj
    (schemeSheafGradedAlgebra F (isQuasicoherentPieces_of_isQuasicoherent F))

/-- **The comparison of the two projective-bundle substrates of `F`.** This is
`Stacks.ProjectiveBundle.presentationIso`, the *named* isomorphism from
`Stacks.SymGraded.schemeProjectiveBundle` to `Stacks.RelativeProj.projectiveBundle` lying over
the base — not a witness chosen from
`AlgebraicGeometry.projectiveBundlePresentationsAgree`, of which it is one. See the
implementation notes: a chosen witness carries no formula on charts and therefore cannot be
compared with the chosen witness at another module, whereas this one can. -/
def bundlePresentationIso : (symGradedBundle F).scheme ≅ projectiveBundle X F :=
  Stacks.ProjectiveBundle.presentationIso F (isQuasicoherentPieces_of_isQuasicoherent F)

/-- The comparison lies over the base. -/
theorem bundlePresentationIso_hom_comp_toBase :
    (bundlePresentationIso F).hom ≫ projectiveBundleToBase X F = (symGradedBundle F).toBase :=
  Stacks.ProjectiveBundle.presentationIso_hom_toBase F
    (isQuasicoherentPieces_of_isQuasicoherent F)

/-- **The comparison's inverse carries the projection of the `SheafGradedAlgebra` presentation
to the projection of the `Situation` presentation.** -/
theorem bundlePresentationIso_inv_comp_toBase :
    (bundlePresentationIso F).inv ≫ (symGradedBundle F).toBase = projectiveBundleToBase X F := by
  rw [← bundlePresentationIso_hom_comp_toBase F, Iso.inv_hom_id_assoc]

/-- **The tautological invertible module `𝒪_{𝐏(F)}(1)` on the projective bundle**, the
comparison's pullback of the degree-one twist of the other presentation.

Reducible, so that instance search — which unfolds only reducible definitions — sees a morphism
into it as a morphism into the pullback it is, which is what
`Stacks.RelativeProj.epi_tautologicalDatumUniv` needs. -/
abbrev tautologicalDatumTwist : (projectiveBundle X F).Modules :=
  (Scheme.Modules.pullback (bundlePresentationIso F).inv).obj
    (Stacks.ProjectiveBundleSplitting.tautologicalTwist F
      (isQuasicoherentPieces_of_isQuasicoherent F))

/-- `𝒪_{𝐏(F)}(1)` is invertible. -/
theorem isInvertible_tautologicalDatumTwist :
    AlgebraicGeometry.SheafOfModules.IsInvertible (projectiveBundle X F).presheaf
      (projectiveBundle X F).ringCatSheaf.2 (tautologicalDatumTwist F) :=
  (Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry _ _ _).mp
    (@Stacks.Modules.isInvertible_pullback _ _ (bundlePresentationIso F).inv _
      ((Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry _ _ _).mpr
        (Stacks.ProjectiveBundleSplitting.isInvertible_tautologicalTwist F
          (isQuasicoherentPieces_of_isQuasicoherent F))))

/-- **The tautological surjection `π^*F ⟶ 𝒪_{𝐏(F)}(1)`**, the tautological map of the
other presentation carried along the comparison. The two comparison isomorphisms identify
`π^*F` with `(b⁻¹)^*(π')^*F`, using that `b⁻¹` lies over the base. -/
def tautologicalDatumUniv :
    (Scheme.Modules.pullback (projectiveBundleToBase X F)).obj F ⟶ tautologicalDatumTwist F :=
  (Scheme.Modules.pullbackCongr (bundlePresentationIso_inv_comp_toBase F)).inv.app F ≫
    (Scheme.Modules.pullbackComp (bundlePresentationIso F).inv
      (symGradedBundle F).toBase).inv.app F ≫
    (Scheme.Modules.pullback (bundlePresentationIso F).inv).map
      (Stacks.ProjectiveBundleSplitting.tautologicalMap F
        (isQuasicoherentPieces_of_isQuasicoherent F))

/-- **The tautological surjection is surjective.** The two comparisons are isomorphisms and
`Scheme.Modules.pullback (b⁻¹)`, being a left adjoint, preserves epimorphisms. -/
instance epi_tautologicalDatumUniv : Epi (tautologicalDatumUniv F) := by
  have : (Scheme.Modules.pullback (bundlePresentationIso F).inv).PreservesEpimorphisms :=
    Functor.preservesEpimorphisms_of_adjunction
      (Scheme.Modules.pullbackPushforwardAdjunction (bundlePresentationIso F).inv)
  have : Epi (Stacks.ProjectiveBundleSplitting.tautologicalMap F
      (isQuasicoherentPieces_of_isQuasicoherent F)) :=
    Stacks.ProjectiveBundleSplitting.epi_tautologicalMap F _
  unfold tautologicalDatumUniv
  infer_instance

/-- **The tautological datum of the projective bundle of an arbitrary quasi-coherent module**:
`𝒪_{𝐏(F)}(1)` together with its universal surjection from `π^*F`. No hypothesis is placed on the
rank of `F`. -/
def tautologicalDatum : TautologicalDatum X F where
  twist := tautologicalDatumTwist F
  invertible := isInvertible_tautologicalDatumTwist F
  univ := tautologicalDatumUniv F
  epi_univ := epi_tautologicalDatumUniv F

/-- The invertible module of `tautologicalDatum F` is `tautologicalDatumTwist F`. -/
@[simp]
theorem tautologicalDatum_twist : (tautologicalDatum F).twist = tautologicalDatumTwist F := rfl

/-- The surjection of `tautologicalDatum F` is `tautologicalDatumUniv F`. -/
@[simp]
theorem tautologicalDatum_univ : (tautologicalDatum F).univ = tautologicalDatumUniv F := rfl

end Stacks.RelativeProj

end
