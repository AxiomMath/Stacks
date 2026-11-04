module

public import StacksFrontier.AlgebraicGeometry.DerivedTildeTorAmplitude
public import StacksFrontier.AlgebraicGeometry.Perfect.PseudoCoherentFrom.Affine
public import StacksFrontier.AlgebraicGeometry.RelativeTorAmplitudeAffine
public import StacksFrontier.Homology.Perfect.Basic
public import StacksFrontier.Homology.Perfect.ModelIndependence
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.PseudoCoherentAndFiniteTorDimension
import StacksCore.Tactic.StacksAttribute

/-!
# Perfect objects on an affine scheme

Let `X = Spec R` and let `M` be an object of `D(R)`. Its image `M̃` under derived sheafification,
an object of `D(𝒪_X)`, is a perfect object of `D(𝒪_X)` exactly when `M` is a perfect object of
`D(R)`.

## Main results

* `AlgebraicGeometry.isPerfect_tilde_iff` is **Stacks 08EB**: perfectness agrees on the two sides.
* `AlgebraicGeometry.isPerfect_tildeComplex_iff` is the same statement read on a complex of
  `R`-modules, which is the form the source states.
* `AlgebraicGeometry.isPerfect_tilde_iff_of_model` is **Stacks 08EB again, at an arbitrary pair of
  chosen derived categories** rather than at the standard model.

## Implementation notes

The proof is the composite the source describes: perfectness on a ringed space is
pseudo-coherence together with locally finite Tor dimension (Stacks 08CQ,
`Stacks.Cohomology.TorAmplitude.isPerfect_iff_isPseudoCoherent_and_locallyHasFiniteTorDimension`),
perfectness over a ring is pseudo-coherence together with finite Tor dimension (Stacks 0658,
`StacksDraft.Perfect.isPerfect_iff_pseudoCoherent_and_finiteTorDimension`), and the two halves
match across derived sheafification by Stacks 08E7
(`AlgebraicGeometry.RingedSpace.isPseudoCoherent_tilde_iff`) and Stacks 08E9
(`AlgebraicGeometry.hasFiniteTorDimension_tilde_iff`).

One step is not in the source's list of citations and is needed because the two sides quantify
the Tor-amplitude interval differently. Stacks 08CQ asks for *locally* finite Tor dimension — a
cover of the space together with an interval on each member — while Stacks 08E9 compares *finite*
Tor dimension, one interval on the whole space. On `Spec R` the two agree, the space being
quasi-compact: that is `locallyHasFiniteTorDimension_iff_hasFiniteTorDimension` of the namespace
`AlgebraicGeometry.AffineRelativeTorAmplitude`.

Stacks 08E7 is stated on a complex of `R`-modules, so
`AlgebraicGeometry.isPseudoCoherent_mapDerivedCategory_tilde_iff` reads it on an object of `D(R)`
by choosing a representing complex; both pseudo-coherence predicates are the existence of a
representative of a prescribed shape, hence invariant under isomorphism, so nothing is lost.

The proof is written in term mode rather than with `rw`. The category of `𝒪_{Spec R}`-modules has
two spellings, `StrictlyPerfect.OXMod (Spec R).toRingedSpace` and `(Spec R).Modules`, which are
equal only by `rfl`; instance search returns the `HasDerivedCategory` instance at the second while
the statements of Stacks 08CQ and Stacks 08CI are at the first, and `rw` compares the two at
`implicit` transparency and fails. Term-mode application checks them at default transparency,
where they agree.

The derived categories of the first three statements are the standard ones, as they already are for
the Stacks 08E9 statements this composes; `HasDerivedCategory.standard` is seated as a local
instance for that reason.

**Why the tag is stated twice.** `HasDerivedCategory` carries the localization as data, so a
statement at the standard model says nothing at any other model, and the standard model's morphisms
live in `Type (u + 1)`. The direct sums that [Derived Categories, Tag 09SR] needs are indexed by
the category's own morphism universe, and in `𝒪_X`-modules those do not exist at `u + 1`; so the
compact-generation results of this chapter are stated at the locally small
`AlgebraicGeometry.Scheme.Modules.hasDerivedCategory` instead, and Stacks 08EB as proved above is
unusable there. `AlgebraicGeometry.isPerfect_tilde_iff_of_model` removes the pin by transport,
using that both perfectness predicates are a condition on a representing *complex* — which mentions
no derived category — together with an isomorphism, which is the only thing that has to travel
(`StacksFrontier.Homology.Perfect.ModelIndependence`). It is placed in a second `AlgebraicGeometry`
block so that the local attribute above does not capture it.

Its sheaf-side instance is written into the statement with `@` rather than left to instance
search. The two spellings `StrictlyPerfect.OXMod (Spec R).toRingedSpace` and `(Spec R).Modules` of
the category of `𝒪_{Spec R}`-modules are definitionally equal, but
`AlgebraicGeometry.Scheme.Modules` is a `def` rather than an abbreviation, so a single
`[HasDerivedCategory (Spec R).Modules]` binder is found for
`CategoryTheory.Functor.mapDerivedCategory` and *not* found for
`Stacks.Cohomology.PerfectComplexes.IsPerfect`, whose binder is at the first spelling. Supplying
the one binder to both uses makes a single model, rather than two unrelated ones, appear on the
two sides of the equivalence.

## References

* [Stacks Project, Lemma 36.10.7 (Tag 08EB)](https://stacks.math.columbia.edu/tag/08EB)
* [Stacks Project, Lemma 36.10.2 (Tag 08E7)](https://stacks.math.columbia.edu/tag/08E7)
* [Stacks Project, Lemma 36.10.4 (Tag 08E9)](https://stacks.math.columbia.edu/tag/08E9)
* [Stacks Project, Lemma 20.49.5 (Tag 08CQ)](https://stacks.math.columbia.edu/tag/08CQ)
* [Stacks Project, Lemma 15.76.2 (Tag 0658)](https://stacks.math.columbia.edu/tag/0658)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open StrictlyPerfect
open StacksDraft.TorAmplitude (hasFiniteTorDimensionCanonical_iff_exists_hasTorAmplitudeCanonical
  hasTorAmplitudeCanonical_iff_hasFlatRepresentative)

universe u

namespace AlgebraicGeometry

variable {R : CommRingCat.{u}}

attribute [local instance] HasDerivedCategory.standard

/-- Every object of a derived category of modules is isomorphic to a complex of modules. -/
private theorem exists_complex_iso [HasDerivedCategory.{_} (ModuleCat.{u} R)]
    (M : DerivedCategory (ModuleCat.{u} R)) :
    ∃ K : CochainComplex (ModuleCat.{u} R) ℤ, Nonempty (DerivedCategory.Q.obj K ≅ M) :=
  ⟨DerivedCategory.Q.objPreimage M, ⟨DerivedCategory.Q.objObjPreimageIso M⟩⟩

/-- **Stacks 08E7 read on an object of `D(R)`.** An object `M` of `D(R)` is pseudo-coherent if and
only if the object `M̃` of `D(𝒪_{Spec R})` is pseudo-coherent. -/
theorem isPseudoCoherent_mapDerivedCategory_tilde_iff (M : DerivedCategory (ModuleCat.{u} R)) :
    AlgebraicGeometry.RingedSpace.PseudoCoherence.IsPseudoCoherent
        (X := (Spec R).toRingedSpace) ((tilde.functor R).mapDerivedCategory.obj M) ↔
      StacksDraft.PseudoCoherence.IsPseudoCoherent M := by
  obtain ⟨K, ⟨eK⟩⟩ := exists_complex_iso M
  have eT : (tilde.functor R).mapDerivedCategory.obj M ≅
      DerivedCategory.Q.obj (tildeComplexMod K) :=
    (tilde.functor R).mapDerivedCategory.mapIso eK.symm ≪≫
      (tilde.functor R).mapDerivedCategoryFactors.app K
  refine Iff.trans (Stacks.Cohomology.TorAmplitude.isPseudoCoherent_iff_isPseudoCoherent'
      (X := (Spec R).toRingedSpace) ((tilde.functor R).mapDerivedCategory.obj M))
    (Iff.trans ⟨fun h => h.of_iso eT, fun h => h.of_iso eT.symm⟩
      (Iff.trans (AlgebraicGeometry.RingedSpace.isPseudoCoherent_tilde_iff (A := (R : Type u)) K)
        ?_))
  exact ⟨fun ⟨E, hE, ⟨e⟩⟩ => ⟨E, hE, ⟨e ≪≫ eK⟩⟩, fun ⟨E, hE, ⟨e⟩⟩ => ⟨E, hE, ⟨e ≪≫ eK.symm⟩⟩⟩

/-- **Stacks 08EB.** Let `X = Spec R` be an affine scheme and let `M` be an object of `D(R)`. Then
the associated object `M̃` of `D(𝒪_X)` is a perfect object of `D(𝒪_X)` if and only if `M` is a
perfect object of `D(R)`. -/
@[stacks 08EB]
theorem isPerfect_tilde_iff (M : DerivedCategory (ModuleCat.{u} R)) :
    Stacks.Cohomology.PerfectComplexes.IsPerfect
        ((tilde.functor R).mapDerivedCategory.obj M) ↔
      StacksDraft.Perfect.IsPerfect M :=
  Iff.trans
    (Stacks.Cohomology.TorAmplitude.isPerfect_iff_isPseudoCoherent_and_locallyHasFiniteTorDimension
      (X := (Spec R).toRingedSpace) ((tilde.functor R).mapDerivedCategory.obj M))
    (Iff.trans
      (and_congr (isPseudoCoherent_mapDerivedCategory_tilde_iff M)
        (Iff.trans
          (AffineRelativeTorAmplitude.locallyHasFiniteTorDimension_iff_hasFiniteTorDimension
            (X := (Spec R).toRingedSpace) ((tilde.functor R).mapDerivedCategory.obj M))
          (Iff.trans (hasFiniteTorDimension_tilde_iff M)
            (Iff.trans
              (hasFiniteTorDimensionCanonical_iff_exists_hasTorAmplitudeCanonical _ M)
              (exists_congr fun a => exists_congr fun b =>
                hasTorAmplitudeCanonical_iff_hasFlatRepresentative _ M a b)))))
      (StacksDraft.Perfect.isPerfect_iff_pseudoCoherent_and_finiteTorDimension M).1.symm)

/-- **Stacks 08EB on a complex of modules**, which is the form the source states: for a complex
`M^•` of `R`-modules, the complex `M̃^•` of `𝒪_{Spec R}`-modules is a perfect object of
`D(𝒪_{Spec R})` if and only if `M^•` is a perfect object of `D(R)`. -/
theorem isPerfect_tildeComplex_iff (M : CochainComplex (ModuleCat.{u} R) ℤ) :
    Stacks.Cohomology.PerfectComplexes.IsPerfect
        (X := (Spec R).toRingedSpace) (DerivedCategory.Q.obj (tildeComplexMod M)) ↔
      StacksDraft.Perfect.IsPerfect (DerivedCategory.Q.obj M) := by
  have e := (tilde.functor R).mapDerivedCategoryFactors.app M
  exact Iff.trans ⟨fun h => Stacks.Cohomology.PerfectComplexTriangles.isPerfect_of_iso
      (X := (Spec R).toRingedSpace) e.symm h,
    fun h => Stacks.Cohomology.PerfectComplexTriangles.isPerfect_of_iso
      (X := (Spec R).toRingedSpace) e h⟩ (isPerfect_tilde_iff (DerivedCategory.Q.obj M))

end AlgebraicGeometry

/-! ### Stacks 08EB at an arbitrary pair of chosen derived categories

The declarations above speak only about the standard model, whose morphisms live in
`Type (u + 1)`. The statement below takes both models as free binders instead. -/

namespace AlgebraicGeometry

universe w w'

variable {R : CommRingCat.{u}}

/-- **Stacks 08EB at an arbitrary pair of chosen derived categories.** Let `X = Spec R` be an
affine scheme and let `M` be an object of `D(R)`, for any chosen model of `D(R)` and any chosen
model of `D(𝒪_X)`, with the two morphism universes unrelated. Then the associated object `M̃` of
`D(𝒪_X)` is a perfect object of `D(𝒪_X)` if and only if `M` is a perfect object of `D(R)`. -/
@[stacks 08EB]
theorem isPerfect_tilde_iff_of_model [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    [hS : HasDerivedCategory.{w'} (Spec R).Modules] (M : DerivedCategory (ModuleCat.{u} R)) :
    @Stacks.Cohomology.PerfectComplexes.IsPerfect (Spec R).toRingedSpace hS
        ((tilde.functor R).mapDerivedCategory.obj M) ↔
      StacksDraft.Perfect.IsPerfect M := by
  obtain ⟨K, ⟨eK⟩⟩ := exists_complex_iso M
  have eT : (@DerivedCategory.Q (Spec R).Modules _ _ hS).obj (tildeComplexMod K) ≅
      (tilde.functor R).mapDerivedCategory.obj M :=
    ((tilde.functor R).mapDerivedCategoryFactors.app K).symm ≪≫
      (tilde.functor R).mapDerivedCategory.mapIso eK
  refine Iff.trans ?_ (Iff.trans (isPerfect_tildeComplex_iff K) ?_)
  · exact Stacks.Cohomology.PerfectComplexes.isPerfect_iff_of_model _ _ eT (Iso.refl _)
  · exact StacksDraft.Perfect.isPerfect_iff_of_model _ _ (Iso.refl _) eK

end AlgebraicGeometry

end
