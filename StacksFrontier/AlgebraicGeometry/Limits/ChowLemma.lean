module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.AlgebraicGeometry.Noetherian
public import StacksFrontier.AlgebraicGeometry.Limits.ProjectiveSpace

/-!
# Chow's lemma: the statement, and the reduction to a finitely presented scheme

**Chow's lemma** (Stacks 0202) says that a separated finite-type morphism `f : X ⟶ S` over a
quasi-compact, quasi-separated base admits a proper surjective modification `π : X' ⟶ X` such
that `X'` immerses into a projective space over `S`, compatibly with the maps to `S`.

This file introduces `AlgebraicGeometry.HasChowModification f` for that conclusion and proves
the first step of the Stacks proof: the conclusion descends along a closed immersion. The
Stacks argument opens by replacing `X` with a scheme `Y` that is separated and of *finite
presentation* over `S` and into which `X` closed-immerses (Stacks 01ZJ), and then observes
"clearly, if we prove the assertion for `Y`, then the result follows for `X`". That observation
is `HasChowModification.of_isClosedImmersion` below; it is pure base change, so it needs none
of the limit machinery that the rest of the proof does.

Also proved here is the fact that a quasi-compact scheme locally of finite type over `Spec ℤ`
is Noetherian, which is what lets the Noetherian-approximation step of the Stacks proof
(Stacks 01ZA/07RN) feed into Chow's lemma over a Noetherian base (Stacks 0200).

## Main definitions

* `AlgebraicGeometry.HasChowModification` is the conclusion of Chow's lemma for a morphism.

## Main results

* `AlgebraicGeometry.HasChowModification.of_isImmersion`: a morphism that already factors as an
  immersion into a projective space over the base satisfies the conclusion of Chow's lemma.
* `AlgebraicGeometry.HasChowModification.of_isClosedImmersion`: if `X` closed-immerses into `Y`
  over `S` and Chow's lemma holds for `Y ⟶ S`, then it holds for `X ⟶ S`.
* `AlgebraicGeometry.HasChowModification.of_isPullback`: the conclusion of Chow's lemma is
  stable under base change of the whole diagram.
* `AlgebraicGeometry.isNoetherian_of_locallyOfFiniteType_terminal_from`: a quasi-compact scheme
  locally of finite type over the terminal scheme is Noetherian.
* `AlgebraicGeometry.locallyOfFiniteType_terminal_from_of_isEmpty`: an empty scheme is locally of
  finite type over the terminal scheme.
* `AlgebraicGeometry.quasiCompact_terminal_from_of_isEmpty`: an empty scheme is quasi-compact over
  the terminal scheme.

## Implementation notes

`HasChowModification` is stated with `AlgebraicGeometry.ProjectiveSpace` and its canonical
structure morphism, so that `AlgebraicGeometry.ProjectiveSpace.instIsProperOver` applies to it
directly.

Finite type is expressed, as elsewhere in this development, by `LocallyOfFiniteType` together
with `QuasiCompact`. The terminal scheme of `Scheme.{u}` is `Spec (ULift.{u} ℤ)`, so being of
finite type over the terminal scheme is being of finite type over the integers.

Chow's lemma itself is not proved here. What *is* available is the whole reduction layer of the
Stacks proof: both of the steps phrased there as "clearly, if we prove the assertion for `Y`,
then the result follows for `X`" are the two lemmas
`HasChowModification.of_isClosedImmersion` and `HasChowModification.of_isPullback`, and the
trivial case is `HasChowModification.of_isImmersion`.

Of the four inputs the Stacks proof needs beyond that reduction layer, three are now available:
the closed embedding into a separated scheme of finite presentation is
`AlgebraicGeometry.exists_isClosedImmersion_into_isSeparated_finitePresentation` (Stacks 01ZJ),
absolute Noetherian approximation is `AlgebraicGeometry.finiteTypeApproximationOfIsLimit`
(Stacks 07RN), and descending a scheme of finite presentation along a limit is
`AlgebraicGeometry.LimitDescent.exists_model_of_finitePresentation_of_essentiallySmall`
(part (1) of Stacks 01ZM), with
`AlgebraicGeometry.exists_isSeparated_baseChange_of_isLimit` (Stacks 01ZQ) descending
separatedness. The one outstanding input is Stacks 0200, Chow's lemma over a Noetherian base,
for which there is no declaration in this development. Its own inputs are all present except
the projective embedding of an affine chart: the Stacks proof obtains that from Stacks 01VS
(ample sheaves), but for an affine chart it also follows from
`AlgebraicGeometry.exists_immersion_affineSpace` (Stacks 04II) together with an open immersion
of `𝔸ⁿ_S` into `ℙⁿ_S` over `S`, which this development does not yet have — only the absolute
chart `AlgebraicGeometry.ProjectiveSpace.basicOpenXIsoAffineSpace` over the integers.

## References

* [Stacks Project, Tag 0202](https://stacks.math.columbia.edu/tag/0202)
* [Stacks Project, Tag 0200](https://stacks.math.columbia.edu/tag/0200)
-/

@[expose] public section

open CategoryTheory Limits

namespace AlgebraicGeometry

universe u

/-- The conclusion of **Chow's lemma** for a morphism `f : X ⟶ S`: there are an `n`, a scheme
`X'`, a proper surjective morphism `π : X' ⟶ X` and an immersion `i : X' ⟶ ℙⁿ_S` such that the
triangle over `S` commutes. -/
def HasChowModification {X S : Scheme.{u}} (f : X ⟶ S) : Prop :=
  ∃ (n : ℕ) (X' : Scheme.{u}) (π : X' ⟶ X) (i : X' ⟶ ProjectiveSpace n S),
    IsProper π ∧ Surjective π ∧ IsImmersion i ∧ π ≫ f = i ≫ (ProjectiveSpace n S ↘ S)

/-- **Chow's lemma is trivial for a morphism that is already projectively immersed.** If `f`
factors as an immersion `i : X ⟶ ℙⁿ_S` followed by the structure morphism of `ℙⁿ_S`, then `f`
admits a Chow modification, namely the identity of `X`. -/
theorem HasChowModification.of_isImmersion {X S : Scheme.{u}} {n : ℕ} {f : X ⟶ S}
    (i : X ⟶ ProjectiveSpace n S) [IsImmersion i] (h : i ≫ (ProjectiveSpace n S ↘ S) = f) :
    HasChowModification f :=
  ⟨n, X, 𝟙 X, i, inferInstance, inferInstance, inferInstance, by rw [Category.id_comp, h]⟩

/-- **Chow's lemma descends along a closed immersion.** If `j : X ⟶ Y` is a closed immersion of
schemes over `S` and Chow's lemma holds for `Y ⟶ S`, then it holds for `X ⟶ S`: pull the
modification of `Y` back along `j`.

This is the opening reduction in the Stacks proof of 0202, which replaces `X` by a scheme that
is separated and of finite presentation over `S`. -/
theorem HasChowModification.of_isClosedImmersion {X Y S : Scheme.{u}} {j : X ⟶ Y} {g : Y ⟶ S}
    {f : X ⟶ S} [IsClosedImmersion j] (hf : j ≫ g = f) (hg : HasChowModification g) :
    HasChowModification f := by
  obtain ⟨n, Y', πY, iY, _, _, _, hCommutesY⟩ := hg
  refine ⟨n, pullback j πY, pullback.fst j πY, pullback.snd j πY ≫ iY, ?_, ?_, ?_, ?_⟩
  · infer_instance
  · infer_instance
  · infer_instance
  · rw [← hf, pullback.condition_assoc, hCommutesY, Category.assoc]

/-- **Chow's lemma is stable under base change.** Let `f : X ⟶ S` and let `f' : X' ⟶ S'` be its
base change along `g : S' ⟶ S`, exhibited by a cartesian square. If Chow's lemma holds for `f`,
then it holds for `f'`.

Base changing a Chow modification `π : Y ⟶ X` gives `Y ×_X X' ⟶ X'`, still proper and
surjective, and the induced morphism `Y ×_X X' ⟶ ℙⁿ_S ×_S S' ≅ ℙⁿ_{S'}` is the base change of
the immersion `Y ⟶ ℙⁿ_S` along `ℙⁿ_{S'} ⟶ ℙⁿ_S`, hence an immersion.

This is the second of the two reductions in the Stacks proof of 0202: having written
`S = lim Sᵢ` and `X = S ×_{Sᵢ} Xᵢ`, the assertion for `Xᵢ ⟶ Sᵢ` gives the assertion for `f`. -/
theorem HasChowModification.of_isPullback {X S X' S' : Scheme.{u}} {f : X ⟶ S} {g : S' ⟶ S}
    {f' : X' ⟶ S'} {p : X' ⟶ X} (hsq : IsPullback p f' f g) (hf : HasChowModification f) :
    HasChowModification f' := by
  obtain ⟨n, Y, π, i, _, _, himm, hcomm⟩ := hf
  have hYsq : IsPullback (pullback.fst π p) (pullback.snd π p) π p :=
    IsPullback.of_hasPullback π p
  have hs : IsPullback (pullback.snd π p ≫ f') (pullback.fst π p) g (π ≫ f) :=
    hYsq.flip.paste_horiz hsq.flip
  rw [hcomm] at hs
  have t : IsPullback (pullback.snd (ProjectiveSpace n S ↘ S) g)
      (pullback.fst (ProjectiveSpace n S ↘ S) g) g (ProjectiveSpace n S ↘ S) :=
    (IsPullback.of_hasPullback (ProjectiveSpace n S ↘ S) g).flip
  refine ⟨n, pullback π p, pullback.snd π p,
    t.lift (pullback.snd π p ≫ f') (pullback.fst π p ≫ i) (by rw [hs.w, Category.assoc]) ≫
      (ProjectiveSpace.baseChangeIso n g).hom, ?_, ?_, ?_, ?_⟩
  · infer_instance
  · infer_instance
  · have : IsImmersion (t.lift (pullback.snd π p ≫ f') (pullback.fst π p ≫ i)
        (by rw [hs.w, Category.assoc])) :=
      MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @IsImmersion)
        (IsPullback.of_right' hs t).flip himm
    infer_instance
  · rw [Category.assoc, ProjectiveSpace.baseChangeIso_hom_over, t.lift_fst]

/-- A quasi-compact scheme that is locally of finite type over the terminal scheme is
Noetherian. The terminal scheme is `Spec (ULift ℤ)`, so this says that a scheme of finite type
over the integers is Noetherian. -/
theorem isNoetherian_of_locallyOfFiniteType_terminal_from (T : Scheme.{u})
    [LocallyOfFiniteType (terminal.from T)] [QuasiCompact (terminal.from T)] :
    IsNoetherian T := by
  let e : (⊤_ Scheme.{u}) ≅ Spec (CommRingCat.of (ULift.{u} ℤ)) :=
    (specULiftZIsTerminal.uniqueUpToIso terminalIsTerminal).symm
  have : IsNoetherianRing (ULift.{u} ℤ) := isNoetherianRing_of_ringEquiv ℤ ULift.ringEquiv.symm
  have : IsLocallyNoetherian (⊤_ Scheme.{u}) := LocallyOfFiniteType.isLocallyNoetherian e.hom
  have : IsLocallyNoetherian T := LocallyOfFiniteType.isLocallyNoetherian (terminal.from T)
  have : CompactSpace (⊤_ Scheme.{u}) := QuasiCompact.compactSpace_of_compactSpace e.hom
  have : CompactSpace T := QuasiCompact.compactSpace_of_compactSpace (terminal.from T)
  exact {}

/-- An empty scheme is locally of finite type over the integers: it is affine, and its ring of
global functions is the zero ring, which is a quotient of the integers. -/
lemma locallyOfFiniteType_terminal_from_of_isEmpty (Z : Scheme.{u}) [IsEmpty Z] :
    LocallyOfFiniteType (terminal.from Z) := by
  rw [HasRingHomProperty.iff_of_isAffine (P := @LocallyOfFiniteType)]
  exact RingHom.FiniteType.of_surjective _ fun _ ↦ ⟨0, Subsingleton.elim _ _⟩

/-- An empty scheme is quasi-compact over the integers. -/
lemma quasiCompact_terminal_from_of_isEmpty (Z : Scheme.{u}) [IsEmpty Z] :
    QuasiCompact (terminal.from Z) :=
  (compactSpace_iff_quasiCompact Z).mp inferInstance

end AlgebraicGeometry

end
