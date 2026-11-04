module

public import StacksFrontier.AlgebraicGeometry.Limits.ChowLemmaAffineBase
public import StacksFrontier.AlgebraicGeometry.Morphisms.Proper.Projective
public import StacksFrontier.AlgebraicGeometry.Topologies.Ph.ChowConsumption
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Chow's lemma produces an H-projective modification

The proof of [Stacks, Tag 02O5] applies Chow's lemma ([Stacks, Tag 0200]) to an integral closed
subscheme `Z` of the source of a proper morphism `f : X ⟶ S` over an affine Noetherian base, and
then feeds the resulting modification to the *projective* case of [Stacks, Tag 02O4]. The step
that turns one into the other is [Stacks, Tag 0201]: Chow's lemma delivers an **immersion** into
`ℙⁿ_S`, while [Stacks, Tag 02O4] wants an H-projective morphism, that is a **closed** immersion
into a projective space over the base.

This file performs that step, unconditionally and in both of the two forms the source's argument
needs — over `S` for the composite `Y ⟶ Z ⟶ S`, and over `Z` for the modification `Y ⟶ Z`
itself. It is the point at which `StacksFrontier/AlgebraicGeometry/ProperCoherentImage/` consumes
Chow's lemma; before it, nothing in that directory mentioned
`AlgebraicGeometry.HasChowModification` or
`AlgebraicGeometry.HasChowModificationIsoOnDenseOpen` at all.

## Main results

* `AlgebraicGeometry.isProjectiveMorphism_of_isImmersion_projectiveSpaceOver`: a **proper**
  scheme immersed in `ℙⁿ_S` over `S` is H-projective over `S`. This is [Stacks, Tag 0201] in the
  form the argument uses: the immersion is proper because `ℙⁿ_S ⟶ S` is separated, hence closed.
* `AlgebraicGeometry.exists_isProjectiveMorphism_of_hasChowModificationIsoOnDenseOpen`: from the
  conclusion of Chow's lemma over a Noetherian base for a **proper** `f : X ⟶ S`, the
  modification `π : Y ⟶ X` is H-projective **and** so is `π ≫ f`, with the dense open of
  [Stacks, Tag 0200] retained.
* `AlgebraicGeometry.exists_isProjectiveMorphism_chowModification_of_isAffine`: the same with no
  hypothesis beyond `IsAffine S`, `IsNoetherian S` and `IsProper f`, since Chow's lemma over an
  affine Noetherian base is unconditional.
* `AlgebraicGeometry.ProperCoherentImage.exists_isProjectiveMorphism_chowModification_subscheme`:
  the shape the dévissage of
  `StacksFrontier/AlgebraicGeometry/ProperCoherentImage/Devissage.lean` asks for — a closed
  subscheme `j : Z ⟶ X` of the source of a proper morphism to an affine locally Noetherian base
  admits a proper surjective modification `π : Y ⟶ Z`, an isomorphism over a dense open of `Z`,
  with both `π` and `π ≫ j ≫ f` H-projective.
* `AlgebraicGeometry.isNoetherian_of_isAffine_of_isLocallyNoetherian`: an affine locally
  Noetherian scheme is Noetherian, which is what lets the dévissage's hypotheses on the base
  (`IsAffine` and `IsLocallyNoetherian`) reach Chow's lemma (`IsNoetherian`).

## Implementation notes

**Why `π` and not only `π ≫ f`.** H-projectivity of the composite is immediate from the
immersion Chow's lemma already supplies, because the properness that upgrades the immersion to a
closed one is properness of `π ≫ f` itself. H-projectivity of `π` over `Z` is the one that costs
something: the closed immersion into `ℙⁿ_Z` has to be assembled as the lift of the pair
`(i, π)` through `ℙⁿ_Z ≅ ℙⁿ_S ×_S Z`, which is
`AlgebraicGeometry.projectiveSpaceOverBaseChangeIso`. Both are needed downstream: the source
chooses one tensor power of `i ^* 𝒪(1)` killing the higher direct images along `π` *and* along
`π ≫ f`, so the invertible sheaf has to be relatively ample for both morphisms, and relative
ampleness is read off an H-projective presentation of each.

**The lift is only known to be an immersion before properness is used.** `pullback.lift i π` is
an immersion by `AlgebraicGeometry.IsImmersion.of_comp` from `pullback.lift_fst`, which gives
back the immersion `i`; its closedness is then obtained exactly as for `i`, from properness of
`π` and separatedness of `ℙⁿ_Z ⟶ Z`. So
`AlgebraicGeometry.isClosedImmersion_of_isImmersion_of_isProper` is applied twice, and is reused
from `StacksFrontier/AlgebraicGeometry/Topologies/Ph/ChowConsumption.lean` rather than restated:
that file proves the same fact for the ph-topology consumer of Chow's lemma, at the same
`IsImmersion` hypothesis, and there is no second notion here to keep apart from it.

**Properness of projective space over its base is supplied by hand**, as
`AlgebraicGeometry.isProper_projectiveSpaceOver`, at each of the two bases. Instance search does
not find it: `AlgebraicGeometry.ProjectiveSpace.instIsProperOver` is stated for the
`AlgebraicGeometry.ProjectiveSpace` spelling, and `AlgebraicGeometry.projectiveSpaceOver` is a
separate abbreviation of the same scheme, so the two agree definitionally but not reducibly.
Once supplied, separatedness of the structure morphism follows from it by instance search and is
what `AlgebraicGeometry.IsProper.of_comp` consumes.

**No tag is attached.** [Stacks, Tag 0201] is a remark comprising several clauses about the
output of Chow's lemma, of which only the closed-immersion upgrade is proved here, and
[Stacks, Tag 02O5] is not reached: the projective case of [Stacks, Tag 02O4], and the
vanishing theorem [Stacks, Tag 02O1] that the source applies to the modification produced
below, have no declaration in this repository.

## References

* [Stacks Project, Tag 0200](https://stacks.math.columbia.edu/tag/0200)
* [Stacks Project, Tag 0201](https://stacks.math.columbia.edu/tag/0201)
* [Stacks Project, Tag 01W8](https://stacks.math.columbia.edu/tag/01W8)
* [Stacks Project, Tag 02O4](https://stacks.math.columbia.edu/tag/02O4)
* [Stacks Project, Tag 02O5](https://stacks.math.columbia.edu/tag/02O5)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

universe u

/-- **An affine locally Noetherian scheme is Noetherian.** An affine scheme is compact by
`AlgebraicGeometry.Scheme.compactSpace_of_isAffine`, and `AlgebraicGeometry.IsNoetherian` is
local Noetherianness together with compactness.

This is the bridge between the hypotheses the dévissage of [Stacks, Tag 02O5] carries on its
base — `IsAffine` and `IsLocallyNoetherian`, which is what the locality reduction of
`AlgebraicGeometry.ProperCoherentImage.higherDirectImageIsCoherent_iff_overAffineBase`
delivers — and the hypothesis Chow's lemma asks for, which is `IsNoetherian`. -/
theorem isNoetherian_of_isAffine_of_isLocallyNoetherian (S : Scheme.{u}) [IsAffine S]
    [IsLocallyNoetherian S] : IsNoetherian S :=
  ⟨⟩

/-- **A proper scheme immersed in a projective space over the base is H-projective**
([Stacks, Tag 0201]). If `i : Y ⟶ ℙⁿ_S` is an immersion with `i ≫ (ℙⁿ_S ⟶ S) = g` and `g` is
proper, then `i` is proper — because `ℙⁿ_S ⟶ S` is separated — hence a closed immersion, so `g`
is H-projective in the sense of `AlgebraicGeometry.IsProjectiveMorphism`.

This is the upgrade that the conclusion of Chow's lemma needs before the projective case of
[Stacks, Tag 02O4] can be applied to it: Chow's lemma produces an immersion, and
[Stacks, Tag 02O4] is about H-projective morphisms. -/
@[ega "II 5.5.3" "(ii), special case"]
theorem isProjectiveMorphism_of_isImmersion_projectiveSpaceOver {Y S : Scheme.{u}} {n : ℕ}
    (i : Y ⟶ projectiveSpaceOver n S) [IsImmersion i] {g : Y ⟶ S} [IsProper g]
    (hi : i ≫ (projectiveSpaceOver n S ↘ S) = g) : IsProjectiveMorphism g := by
  have hproj : IsProper (projectiveSpaceOver n S ↘ S) := isProper_projectiveSpaceOver n S
  have hcomp : IsProper (i ≫ (projectiveSpaceOver n S ↘ S)) := by rw [hi]; infer_instance
  have : IsProper i := IsProper.of_comp i (projectiveSpaceOver n S ↘ S)
  exact ⟨n, i, isClosedImmersion_of_isImmersion_of_isProper i, hi⟩

/-- **Chow's lemma for a proper morphism yields an H-projective modification.** Let `f : X ⟶ S`
be proper and suppose the conclusion of Chow's lemma over a Noetherian base
(`AlgebraicGeometry.HasChowModificationIsoOnDenseOpen`, [Stacks, Tag 0200]) holds for it. Then
there are a proper surjective `π : Y ⟶ X`, an isomorphism above a dense open `U ⊆ X`, such that
**both** `π` and `π ≫ f` are H-projective.

For `π ≫ f` this is `isProjectiveMorphism_of_isImmersion_projectiveSpaceOver` at the immersion
`i : Y ⟶ ℙⁿ_S` that Chow's lemma supplies. For `π` it is the same statement over the base `X`,
at the immersion `Y ⟶ ℙⁿ_X` obtained by lifting the pair `(i, π)` through
`AlgebraicGeometry.projectiveSpaceOverBaseChangeIso`; see the implementation notes. -/
theorem exists_isProjectiveMorphism_of_hasChowModificationIsoOnDenseOpen {X S : Scheme.{u}}
    (f : X ⟶ S) [IsProper f] (h : HasChowModificationIsoOnDenseOpen f) :
    ∃ (Y : Scheme.{u}) (π : Y ⟶ X) (U : X.Opens), IsProper π ∧ Surjective π ∧
      IsProjectiveMorphism π ∧ IsProjectiveMorphism (π ≫ f) ∧ Dense (U : Set X) ∧
        IsIso (π ∣_ U) := by
  obtain ⟨n, Y, π, i, U, hπ, hπs, hi, hcomm, hdense, hiso⟩ := h
  have : IsProper π := hπ
  have : IsImmersion i := hi
  have hcompProper : IsProper (π ≫ f) := inferInstance
  refine ⟨Y, π, U, hπ, hπs, ?_, ?_, hdense, hiso⟩
  · have hlift : IsImmersion (pullback.lift i π hcomm.symm ≫
        (projectiveSpaceOverBaseChangeIso n f).hom) := by
      have hfst : IsImmersion (pullback.lift i π hcomm.symm ≫
          pullback.fst (projectiveSpaceOver n S ↘ S) f) := by
        rw [pullback.lift_fst]; exact hi
      have hmid : IsImmersion (pullback.lift i π hcomm.symm) :=
        IsImmersion.of_comp _ (pullback.fst (projectiveSpaceOver n S ↘ S) f)
      infer_instance
    have hover : (pullback.lift i π hcomm.symm ≫ (projectiveSpaceOverBaseChangeIso n f).hom) ≫
        (projectiveSpaceOver n X ↘ X) = π := by
      rw [Category.assoc, projectiveSpaceOverBaseChangeIso_hom_over, pullback.lift_snd]
    exact isProjectiveMorphism_of_isImmersion_projectiveSpaceOver _ hover
  · exact isProjectiveMorphism_of_isImmersion_projectiveSpaceOver i hcomm.symm

/-- **Chow's lemma over an affine Noetherian base yields an H-projective modification**, with no
hypothesis beyond properness of `f` and the base being affine and Noetherian.

This is `exists_isProjectiveMorphism_of_hasChowModificationIsoOnDenseOpen` with its hypothesis
discharged by `AlgebraicGeometry.hasChowModificationIsoOnDenseOpen_of_isAffine`, which is
unconditional. -/
theorem exists_isProjectiveMorphism_chowModification_of_isAffine {X S : Scheme.{u}} (f : X ⟶ S)
    [IsAffine S] [IsNoetherian S] [IsProper f] :
    ∃ (Y : Scheme.{u}) (π : Y ⟶ X) (U : X.Opens), IsProper π ∧ Surjective π ∧
      IsProjectiveMorphism π ∧ IsProjectiveMorphism (π ≫ f) ∧ Dense (U : Set X) ∧
        IsIso (π ∣_ U) :=
  exists_isProjectiveMorphism_of_hasChowModificationIsoOnDenseOpen f
    (hasChowModificationIsoOnDenseOpen_of_isAffine f)

namespace ProperCoherentImage

/-- **The H-projective Chow modification of a closed subscheme, in the shape the dévissage of
[Stacks, Tag 02O5] asks for.** Let `f : X ⟶ S` be proper with `S` affine and locally Noetherian
— the configuration
`AlgebraicGeometry.ProperCoherentImage.HigherDirectImageIsCoherentOnIntegralIdeals` quantifies
over — and let `j : Z ⟶ X` be a closed immersion. Then `Z` admits a proper surjective
modification `π : Y ⟶ Z`, an isomorphism above a dense open of `Z`, with both `π` and
`π ≫ j ≫ f` H-projective.

Integrality of `Z` is **not** used, and is therefore not assumed: the source uses it only later,
to speak of the generic point of `Z` and of the rank there of the sheaf it constructs.

This is the input to step 4 of the source's proof. What it does not supply, and what has no
declaration in this repository, is the rest of that step: the vanishing theorem
[Stacks, Tag 02O1] choosing a tensor power of `i ^* 𝒪(1)` that kills the higher direct images
along `π` and along `π ≫ j ≫ f`, the projective case of [Stacks, Tag 02O4] for coherence of
`(π ≫ j ≫ f)_*` of that power, and the relative Leray spectral sequence [Stacks, Tag 01F6]
transporting both down to `Z`. -/
@[sga "4½ Arcata 3.4.3" "special case"]
theorem exists_isProjectiveMorphism_chowModification_subscheme {X S Z : Scheme.{u}} (f : X ⟶ S)
    [IsAffine S] [IsLocallyNoetherian S] [IsProper f] (j : Z ⟶ X) [IsClosedImmersion j] :
    ∃ (Y : Scheme.{u}) (π : Y ⟶ Z) (U : Z.Opens), IsProper π ∧ Surjective π ∧
      IsProjectiveMorphism π ∧ IsProjectiveMorphism (π ≫ j ≫ f) ∧ Dense (U : Set Z) ∧
        IsIso (π ∣_ U) := by
  have : IsNoetherian S := isNoetherian_of_isAffine_of_isLocallyNoetherian S
  have : IsProper (j ≫ f) := inferInstance
  exact exists_isProjectiveMorphism_chowModification_of_isAffine (j ≫ f)

end ProperCoherentImage

end AlgebraicGeometry

end
