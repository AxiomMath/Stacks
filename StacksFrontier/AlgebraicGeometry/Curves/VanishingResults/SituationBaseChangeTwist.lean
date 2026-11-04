module

public import StacksFrontier.AlgebraicGeometry.Curves.VanishingResults.SituationBaseChange
public import StacksFrontier.AlgebraicGeometry.FlatBaseChange.GlobalGeneration
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpaceBaseChange.VeryAmple
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.InvertibleDegreeFieldExtension

/-!
# A very ample sheaf on the curve of Situation [Stacks, Tag 0B5D] after a ground-field extension

Let `S` be a datum of Situation [Stacks, Tag 0B5D], let `K/S.k` be an extension of fields and let
`ℒ` be an invertible `𝒪_X`-module. This file transports the two hypotheses that
[Stacks, Tag 0B5H] places on `ℒ` — very ampleness and the lower bound on the degree — to the
base-changed situation `S.baseChange K` of
`StacksFrontier/AlgebraicGeometry/Curves/VanishingResults/SituationBaseChange.lean`.

It also transports the *conclusion* of that tag back down: global generation of a quasi-coherent
module on `X` is equivalent to global generation of its inverse image on `X_K`, which is
[Stacks, Tag 0B57]. Together with that file these are all the inputs of the source's reduction of
[Stacks, Tag 0B5H] to an algebraically closed base field *except one*: the identification of the
inverse image of `ω_X` with the dualizing sheaf of the base change ([Stacks, Tag 0E32]). See
"What is still missing" below.

## Main results

* `AlgebraicGeometry.CohenMacaulayCurveSituation.isInvertible_pullback_baseChangeProj`: the
  inverse image of an invertible module is invertible ([Stacks, Tag 0B8L]).
* `AlgebraicGeometry.CohenMacaulayCurveSituation.isRelativelyVeryAmple_baseChange`: the inverse
  image of a very ample invertible module is very ample for the base-changed situation. This is
  [Stacks, Tag 0B3F] at the affine bases `Spec S.k` and `Spec K`.
* `AlgebraicGeometry.CohenMacaulayCurveSituation.invertibleCurveDegree_baseChange`: the degree is
  unchanged, which is [Stacks, Tag 0B59].
* `AlgebraicGeometry.CohenMacaulayCurveSituation`
  `.nonempty_generatingSections_pullback_baseChangeProj_iff`: global generation is unchanged,
  which is [Stacks, Tag 0B57].

## What is still missing for the reduction

* **Part (2) of [Stacks, Tag 0E32].** The inverse image of
  `Stacks.Duality.dualizingSheafOverField S.f` along `X_K ⟶ X` has to be
  `Stacks.Duality.dualizingSheafOverField (S.baseChange K).f`. The dualizing complex is
  `f^×(𝒪_{Spec k})` for the right adjoint `f^×` of [Stacks, Tag 0A9E], and the source deduces the
  statement from base change for `f^×`, [Stacks, Tag 0AA8]. In this repository the comparison
  morphism of [Stacks, Tag 0AA6] is constructed
  (`Stacks.Duality.twistedInverseImageBaseChangeMap`) but it takes the invertibility of the
  pushforward comparison `ξ` of [Stacks, Tag 0A9K] as an instance argument. That
  invertibility is stated by
  `Stacks.Duality.isIso_twistedInverseImagePushforwardBaseChange_iff` of
  `Duality/TwistedInverseImage/BaseChangeConjugate.lean`, as an equivalence with
  invertibility of the derived base change map of [Stacks, Tag 08HY], so that at this model
  [Stacks, Tag 0A9K] is exactly [Stacks, Tag 08IB]. It is not proved, and even granted
  it the invertibility asserted by [Stacks, Tag 0AA8] is a further unproved theorem. So part (2)
  of [Stacks, Tag 0E32] is out of reach, and with it the general case of [Stacks, Tag 0B5H]; see
  the module documentation of `DualizingTwistGenerationGeneralField.lean` for the full chain and
  for the hypotheses of [Stacks, Tag 0AA8], which this situation does meet.

**Descent of global generation.** Concluding global generation of `ω_X ⊗ ℒ` on `X` from the same statement on `X_{k̄}` needs
`Γ(X, ℱ) ⊗_k k̄ = Γ(X_{k̄}, ℱ_{k̄})` together with descent of surjectivity along the faithfully
flat `X_{k̄} ⟶ X`. Both are available for
`AlgebraicGeometry.SheafOfModules.GeneratingSections`: [Stacks, Tag 0B57] is proved for
`GeneratingSections`, in both directions and over an
arbitrary faithfully flat ring map, as
`Stacks.AlgebraicGeometry.FlatBaseChange.nonempty_generatingSections_pullback_iff_specMap`, and
`nonempty_generatingSections_pullback_baseChangeProj_iff` below is its instance at this situation.

## Implementation notes

Both results are the general statements applied at the chosen categorical pullback, with the three
components of `AlgebraicGeometry.CohenMacaulayCurveSituation.baseChange` unfolded by `rfl`. The
finite-type and quasi-compactness hypotheses of
`AlgebraicGeometry.isRelativelyVeryAmple_baseChange` and the affineness of the two bases are
automatic here: `S.f` is proper and the bases are spectra of fields.

Invertibility of the inverse image is not registered as an instance, because its only hypothesis
is invertibility of a module on a *different* scheme and instance search cannot be expected to
guess the morphism; it is passed explicitly, which is also how
`AlgebraicGeometry.invertibleCurveDegree` receives it.

## References

* [Stacks Project, Tag 0B5D](https://stacks.math.columbia.edu/tag/0B5D)
* [Stacks Project, Tag 0B5H](https://stacks.math.columbia.edu/tag/0B5H)
* [Stacks Project, Tag 0B3F](https://stacks.math.columbia.edu/tag/0B3F)
* [Stacks Project, Tag 0B59](https://stacks.math.columbia.edu/tag/0B59)
* [Stacks Project, Tag 0B8L](https://stacks.math.columbia.edu/tag/0B8L)
* [Stacks Project, Tag 0B57](https://stacks.math.columbia.edu/tag/0B57)
* [Stacks Project, Tag 0E32](https://stacks.math.columbia.edu/tag/0E32)
* [Stacks Project, Tag 0AA6](https://stacks.math.columbia.edu/tag/0AA6)
* [Stacks Project, Tag 0AA8](https://stacks.math.columbia.edu/tag/0AA8)
* [Stacks Project, Tag 0A9K](https://stacks.math.columbia.edu/tag/0A9K)
* [Stacks Project, Tag 0A9E](https://stacks.math.columbia.edu/tag/0A9E)
* [Stacks Project, Tag 08HY](https://stacks.math.columbia.edu/tag/08HY)
* [Stacks Project, Tag 08IB](https://stacks.math.columbia.edu/tag/08IB)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

namespace CohenMacaulayCurveSituation

variable (S : CohenMacaulayCurveSituation.{u}) (K : Type u) [Field K] [Algebra S.k K]

/-- **The projection `X_K ⟶ X` of the base-changed situation**, along which the modules of `S`
are pulled back. -/
abbrev baseChangeProj : (S.baseChange K).X ⟶ S.X :=
  pullback.fst S.f (Spec.map (CommRingCat.ofHom (algebraMap S.k K)))

/-- **[Stacks, Tag 0B8L] on the base-changed situation**: the inverse image of an invertible
`𝒪_X`-module along `X_K ⟶ X` is an invertible `𝒪_{X_K}`-module. -/
theorem isInvertible_pullback_baseChangeProj (L : S.X.Modules)
    [hL : SheafOfModules.IsInvertible S.X.presheaf S.X.ringCatSheaf.2 L] :
    SheafOfModules.IsInvertible (S.baseChange K).X.presheaf (S.baseChange K).X.ringCatSheaf.2
      ((Scheme.Modules.pullback (S.baseChangeProj K)).obj L) :=
  Stacks.RingedSpace.modulePullback_isInvertible_algebraicGeometry
    (S.baseChangeProj K).toLRSHom.toShHom L hL

/-- **[Stacks, Tag 0B3F] on the base-changed situation**: the inverse image along `X_K ⟶ X` of a
very ample invertible `𝒪_X`-module is very ample relative to `X_K ⟶ Spec K`.

The two bases are spectra of fields, hence affine, and `S.f` is proper, hence of finite type, so
`AlgebraicGeometry.isRelativelyVeryAmple_baseChange` applies with nothing to supply. -/
theorem isRelativelyVeryAmple_baseChange (L : S.X.Modules)
    [hL : SheafOfModules.IsInvertible S.X.presheaf S.X.ringCatSheaf.2 L]
    (hva : Stacks.Tag01VMVeryAmple.IsRelativelyVeryAmple S.f L) :
    @Stacks.Tag01VMVeryAmple.IsRelativelyVeryAmple (Spec (.of K)) (S.baseChange K).X
      (S.baseChange K).f ((Scheme.Modules.pullback (S.baseChangeProj K)).obj L)
      (S.isInvertible_pullback_baseChangeProj K L) :=
  AlgebraicGeometry.isRelativelyVeryAmple_baseChange
    (IsPullback.of_hasPullback S.f
      (Spec.map (CommRingCat.ofHom (algebraMap S.k K)))) L hva

/-- **[Stacks, Tag 0B59] on the base-changed situation**: the degree of an invertible
`𝒪_X`-module is unchanged by the extension of the ground field. -/
theorem invertibleCurveDegree_baseChange (L : S.X.Modules)
    [hL : SheafOfModules.IsInvertible S.X.presheaf S.X.ringCatSheaf.2 L] :
    @invertibleCurveDegree K _ (S.baseChange K).X (S.baseChange K).f
        (S.baseChange K).proper (le_of_eq (S.baseChange K).dimension_one)
        ((Scheme.Modules.pullback (S.baseChangeProj K)).obj L)
        (S.isInvertible_pullback_baseChangeProj K L) =
      invertibleCurveDegree S.k S.f (le_of_eq S.dimension_one) L :=
  invertibleCurveDegree_baseChange_field_pullback S.k K S.f (le_of_eq S.dimension_one) L

/-- **[Stacks, Tag 0B57] on the base-changed situation**: a quasi-coherent `𝒪_X`-module is
generated by its global sections if and only if its inverse image along `X_K ⟶ X` is.

This is the descent step of the source's reduction of [Stacks, Tag 0B5H] to an algebraically
closed base field, and it is
`Stacks.AlgebraicGeometry.FlatBaseChange.nonempty_generatingSections_pullback_iff_specMap` at
`φ = algebraMap S.k K`: an extension of fields is faithfully flat because `K` is a nonzero free
`S.k`-module, and `S.f` is proper, hence quasi-compact and quasi-separated. -/
theorem nonempty_generatingSections_pullback_baseChangeProj_iff (F : S.X.Modules)
    [F.IsQuasicoherent] :
    Nonempty F.GeneratingSections ↔
      Nonempty (((Scheme.Modules.pullback (S.baseChangeProj K)).obj F).GeneratingSections) := by
  let : IsProper S.f := S.proper
  let : QuasiCompact S.f := inferInstance
  let : QuasiSeparated S.f := inferInstance
  exact Stacks.AlgebraicGeometry.FlatBaseChange.nonempty_generatingSections_pullback_iff_specMap
    (CommRingCat.ofHom (algebraMap S.k K))
    (RingHom.faithfullyFlat_algebraMap_iff.2 inferInstance) S.f F

end CohenMacaulayCurveSituation

end AlgebraicGeometry

end
