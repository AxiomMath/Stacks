module

public import StacksFrontier.AlgebraicGeometry.Perfect.RelativeDescentAffineEssentialSurjectivity
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativeTorAmplitudeOpenImmersion

/-!
# The module avatar of a pseudo-coherent object on an affine scheme

Let `A` be a commutative ring and let `E` be a pseudo-coherent object of `D(𝒪_{Spec A})`. This
module produces an object `M` of `D(A)`, itself pseudo-coherent, whose complex of associated
sheaves is isomorphic to `E`.

This is the step *write `U_i = Spec(A)` … the restriction `E|_{U_i}` corresponds (by Derived
Categories of Schemes, Lemma 06Z0 and 08E7) to a pseudo-coherent object `K` of `D(A)`* of the
source's proof of Stacks 0DJZ, which is where the fibrewise criterion of Stacks 0DJH gets the
complex of modules it consumes.

Both halves are already available; what is added here is their composition at one model.
Pseudo-coherence makes the cohomology sheaves of `E` quasi-coherent, which is Stacks 08E5
(`AlgebraicGeometry.isQuasicoherentDerived_of_isPseudoCoherent`); an object of `D(𝒪_{Spec A})`
with quasi-coherent cohomology is a complex of associated sheaves, which is Stacks 06Z0 at the
standard model (`AlgebraicGeometry.StandardModel.exists_iso_mapDerivedCategory`); and
pseudo-coherence transfers back across `~` by Stacks 08E7
(`AlgebraicGeometry.RingedSpace.isPseudoCoherent_derivedTilde_iff`).

## Main results

* `AlgebraicGeometry.RingedSpace.exists_isPseudoCoherent_iso_mapDerivedCategory_tilde`: the
  avatar, with its pseudo-coherence.

## Implementation notes

The three inputs meet only at `CategoryTheory.HasDerivedCategory.standard`, and the attribute
seating it is written with priority `10000` as the implementation notes of
`StacksFrontier/AlgebraicGeometry/DerivedQCoh/AffineDerivedEquivalenceStandard.lean` require: that
file's import closure carries *global* `HasDerivedCategory` instances for `ModuleCat` and for
`X.Modules`, and a global instance beats a default-priority local attribute, so a plain
`attribute [local instance]` here would silently keep the locally small model and the two halves
would not compose.

Stacks 08E7 is used at its *object-level* form
`AlgebraicGeometry.RingedSpace.isPseudoCoherent_derivedTilde_iff`, which takes an arbitrary object
of `D(A)`, rather than the complex-level
`AlgebraicGeometry.RingedSpace.isPseudoCoherent_tilde_iff`, which takes a cochain complex and its
image under `DerivedCategory.Q`. The avatar Stacks 06Z0 produces is an arbitrary object, so the
object-level form applies directly and no representative has to be chosen.

No `stacks` attribute is placed. The statement is the composition of three tags, each already
registered where it is proved, and it asserts no clause of its own; in particular it is not a
clause of Stacks 0DJZ, whose conclusion is about relative perfectness.

## References

* [Stacks Project, Lemma 36.3.5 (06Z0)](https://stacks.math.columbia.edu/tag/06Z0)
* [Stacks Project, Lemma 36.10.2 (08E7)](https://stacks.math.columbia.edu/tag/08E7)
* [Stacks Project, Lemma 36.10.1 (08E5)](https://stacks.math.columbia.edu/tag/08E5)
* [Stacks Project, Lemma 37.71.3 (0DJZ)](https://stacks.math.columbia.edu/tag/0DJZ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits StrictlyPerfect

universe u

attribute [local instance 10000] HasDerivedCategory.standard

namespace AlgebraicGeometry.RingedSpace

/-- **A pseudo-coherent object on an affine scheme is a complex of associated sheaves.** Stacks
08E5 followed by Stacks 06Z0 at the standard model, with no pseudo-coherence claim about the
avatar yet.

This half is a declaration of its own because the two inputs are stated at the two definitionally
equal spellings of the category of `𝒪_{Spec A}`-modules — `StrictlyPerfect.OXMod` of the ringed
space for Stacks 08E5, `(Spec A).Modules` for Stacks 06Z0 — and the unifier crossing them is
expensive. Heartbeats are counted per declaration, so isolating the crossing here keeps it and the
pseudo-coherence step of the next declaration from sharing one budget. No elaboration option is
raised anywhere in this module; splitting the declarations is what makes it compile. -/
private theorem exists_iso_mapDerivedCategory_tilde_of_isPseudoCoherent (A : CommRingCat.{u})
    (E : DerivedCategory (OXMod.{u, u} (Spec A).toRingedSpace))
    (hE : IsPseudoCoherent (X := (Spec A).toRingedSpace) E) :
    ∃ M : DerivedCategory (ModuleCat.{u} A),
      Nonempty ((tilde.functor A).mapDerivedCategory.obj M ≅ E) := by
  have hqc : ∀ n : ℤ,
      ((DerivedCategory.homologyFunctor (Spec A).Modules n).obj E).IsQuasicoherent :=
    isQuasicoherentDerived_of_isPseudoCoherent (Spec A) E hE
  exact StandardModel.exists_iso_mapDerivedCategory A E hqc

/-- Pseudo-coherence transported from `E` onto the complex of associated sheaves of its avatar,
along the isomorphism the previous declaration supplies.

A declaration of its own for the same reason: the transport is
`AlgebraicGeometry.RingedSpace.IsPseudoCoherent.of_iso`, whose ringed space is implicit and so is
inferred by unifying the two spellings again, and it is kept off the budget of the
Stacks 08E7 application that consumes it. -/
private theorem isPseudoCoherent_mapDerivedCategory_tilde_of_iso (A : CommRingCat.{u})
    (E : DerivedCategory (OXMod.{u, u} (Spec A).toRingedSpace))
    (hE : IsPseudoCoherent (X := (Spec A).toRingedSpace) E)
    (M : DerivedCategory (ModuleCat.{u} A))
    (e : (tilde.functor A).mapDerivedCategory.obj M ≅ E) :
    IsPseudoCoherent (X := (Spec A).toRingedSpace)
      ((tilde.functor A).mapDerivedCategory.obj M) :=
  hE.of_iso e.symm

/-- **The module avatar of a pseudo-coherent object on an affine scheme.** A pseudo-coherent
object `E` of `D(𝒪_{Spec A})` is isomorphic to the complex of associated sheaves of a
pseudo-coherent object `M` of `D(A)`.

This is the source's *`E|_{U_i}` corresponds to a pseudo-coherent object `K` of `D(A)`*: Stacks
08E5 makes the cohomology of `E` quasi-coherent, Stacks 06Z0 produces `M`, and Stacks 08E7
returns its pseudo-coherence. -/
public theorem exists_isPseudoCoherent_iso_mapDerivedCategory_tilde (A : CommRingCat.{u})
    (E : DerivedCategory (OXMod.{u, u} (Spec A).toRingedSpace))
    (hE : IsPseudoCoherent (X := (Spec A).toRingedSpace) E) :
    ∃ M : DerivedCategory (ModuleCat.{u} A),
      StacksDraft.PseudoCoherence.IsPseudoCoherent M ∧
        Nonempty ((tilde.functor A).mapDerivedCategory.obj M ≅ E) := by
  obtain ⟨M, ⟨e⟩⟩ := exists_iso_mapDerivedCategory_tilde_of_isPseudoCoherent A E hE
  exact ⟨M, (isPseudoCoherent_derivedTilde_iff A M).mp
    (isPseudoCoherent_mapDerivedCategory_tilde_of_iso A E hE M e), ⟨e⟩⟩

end AlgebraicGeometry.RingedSpace

end
