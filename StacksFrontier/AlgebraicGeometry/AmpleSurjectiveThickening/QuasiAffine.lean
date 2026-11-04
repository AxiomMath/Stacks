module

public import StacksFrontier.AlgebraicGeometry.AmpleSurjectiveThickening.Basic
public import StacksFrontier.AlgebraicGeometry.AmplePullback.QuasiAffineUnitIso
public import StacksFrontier.AlgebraicGeometry.AmpleWire.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.IsIso
public import Mathlib.Data.ZMod.Basic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Stacks Tag 0B7K: quasi-affineness across a surjective closed immersion

Let `i : Z ⟶ X` be a closed immersion of Noetherian schemes inducing a homeomorphism of
underlying topological spaces — equivalently, a surjective closed immersion. [Stacks, Tag 0B7K]
asserts

> `X` is quasi-affine if and only if `Z` is quasi-affine.

The source proves it by reading [Stacks, Tag 01QE] — a scheme is quasi-affine exactly when its
structure sheaf is ample — through [Stacks, Tag 09MS], and remarks that the implication `X`
quasi-affine `⟹` `Z` quasi-affine "can also be seen in an elementary way".

## Main results

* `Stacks.AmpleSurjectiveThickening.isQuasiAffine_iff_isAmple_modulePullback_unitModule`:
  `Z` is quasi-affine exactly when `i^* 𝒪_X` is ample on `Z`, for an arbitrary morphism `i`.
  This is [Stacks, Tag 01QE] transported along `i^* 𝒪_X ≅ 𝒪_Z`.
* `Stacks.AmpleSurjectiveThickening.isQuasiAffine_of_isQuasiAffine`: `X` quasi-affine `⟹` `Z`
  quasi-affine, since a closed immersion is affine.
* `Stacks.AmpleSurjectiveThickening.isQuasiAffine_of_isQuasiAffine_source`: `Z` quasi-affine
  `⟹` `X` quasi-affine, from [Stacks, Tag 09MS] and [Stacks, Tag 01QE].
* `Stacks.AmpleSurjectiveThickening.isQuasiAffine_iff_isQuasiAffine`: **[Stacks, Tag 0B7K]**.
* `Stacks.AmpleSurjectiveThickening.isQuasiAffine_of_sectionsLiftAfterPower` and
  `isQuasiAffine_iff_of_sectionsLiftAfterPower`: the same implications through
  `Stacks.AmpleClosedImmersion.SectionsLiftAfterPower`.
* `Stacks.AmpleSurjectiveThickening.dualNumberThickening`,
  `not_isIso_dualNumberThickening` and `dualNumberThickening_hypotheses`:
  `Spec(ℤ/4 ⧸ (2)) ⟶ Spec(ℤ/4)`, a surjective closed immersion of Noetherian schemes that is
  not an isomorphism.

## The route

`X` quasi-affine `⟹` `Z` quasi-affine: a closed immersion is affine, and Mathlib's
`AlgebraicGeometry.Scheme.IsQuasiAffine.of_isAffineHom` says the source of an affine morphism
into a quasi-affine scheme is quasi-affine. Neither surjectivity of `i` nor Noetherianness of `X`
enters; both are carried in the statement because the other half of the source's biconditional
needs them, so that what is proved is literally one half of the source statement.

The source's own route is recorded alongside, because it is what the source's dependency on
[Stacks, Tag 09MS] refers to: `𝒪_X` ample gives `i^* 𝒪_X` ample by the unconditional half of
Tag 09MS (`Stacks.AmpleSurjectiveThickening.isAmple_modulePullback`), and `i^* 𝒪_X ≅ 𝒪_Z` carries
Tag 01QE back down to `Z`. The two agree, which is a check on both.

## What is not done here, and what is proved elsewhere

**No declaration in this file carries the bare tag** — only the scoped clause for the implication
`X` quasi-affine `⟹` `Z` quasi-affine. The two statements below give the biconditional granted
`Stacks.AmpleClosedImmersion.SectionsLiftAfterPower`, the hypothesis the converse half of
Tag 09MS still carries in this repository, and for a general invertible `L` that hypothesis is
still not discharged; the module documentation of
`StacksFrontier/AlgebraicGeometry/AmpleSurjectiveThickening/Basic.lean` names the Stacks tags whose
assembly would discharge it.

[Stacks, Tag 0B7K] itself, however, **is proved**, by a route that does not pass through ampleness
at all: `Stacks.Thickenings.isQuasiAffine_iff_of_isNoetherian`, in
`StacksFrontier/AlgebraicGeometry/MoreMorphisms/ThickeningMorphism/QuasiAffineAscent.lean`, carries
the bare tag. At `L = 𝒪_X` the graded sequence the source differentiates is the sequence of
sheaves of commutative rings `0 → 𝓘 → 𝒪_X → i_* 𝒪_Z → 0` itself, and the affine opens of `Z` and
`X` correspond, so the transport of ampleness is free and what is left is the lifting of the
nonvanishing locus of a global function. Over a Noetherian scheme `𝓘` has a vanishing power, so
that lifting reduces along the filtration by its powers to the square-zero case, and the
square-zero case is an elementary Čech computation on a finite affine cover, using only the two
localization statements over an affine open. No cohomology group is formed, so neither
[Stacks, Tag 01XR] in degree one nor [Stacks, Tag 09MR] is needed.

What that route does **not** give is Tag 09MS for an arbitrary invertible `L`, which is what the
statements below need, nor [Stacks, Tag 0B7L] — the same biconditional with no Noetherian
hypothesis — for which the source uses the limit argument of [Stacks, Tag 09MW].

## References

* [Stacks Project, Tag 0B7K](https://stacks.math.columbia.edu/tag/0B7K)
* [Stacks Project, Tag 0B7L](https://stacks.math.columbia.edu/tag/0B7L)
* [Stacks Project, Tag 09MS](https://stacks.math.columbia.edu/tag/09MS)
* [Stacks Project, Tag 09MW](https://stacks.math.columbia.edu/tag/09MW)
* [Stacks Project, Tag 01QE](https://stacks.math.columbia.edu/tag/01QE)
* [Stacks Project, Tag 01XR](https://stacks.math.columbia.edu/tag/01XR)
* [Stacks Project, Tag 0B8S](https://stacks.math.columbia.edu/tag/0B8S)
* [Stacks Project, Tag 01Y9](https://stacks.math.columbia.edu/tag/01Y9)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory
open RingedSpaceModuleAdjunction
open Stacks.Ample

universe u

namespace Stacks.AmpleSurjectiveThickening

variable {Z X : Scheme.{u}} (i : Z ⟶ X)

/-! ### Quasi-affineness of the source as ampleness of the pulled-back structure sheaf -/

/-- **[Stacks, Tag 01QE] on the source of an arbitrary morphism, read at `i^* 𝒪_X`.** A scheme `Z`
receiving `i : Z ⟶ X` is quasi-affine exactly when the pullback of `𝒪_X` is ample on it.

No hypothesis on `i`: the pullback of the structure sheaf is isomorphic to the structure sheaf by
`Stacks.AmplePullback.modulePullbackIsoUnitModule`, and
`Stacks.RelativeAmple.isQuasiAffine_iff_isAmple_of_iso_unitModule` is Tag 01QE for any invertible
module isomorphic to `𝒪_Z`. -/
@[ega "II 5.1.2" "more general", ega "II 5.1.4" "special case", ega "II 6.6.13" "more general"]
theorem isQuasiAffine_iff_isAmple_modulePullback_unitModule :
    Z.IsQuasiAffine ↔ IsAmple Z ((modulePullback i.toLRSHom.toShHom).obj (unitModule X)) :=
  Stacks.RelativeAmple.isQuasiAffine_iff_isAmple_of_iso_unitModule Z _
    (Stacks.AmplePullback.modulePullbackIsoUnitModule i (unitModule X) (Iso.refl _))

/-! ### The implication `X` quasi-affine ⟹ `Z` quasi-affine -/

/-- **`X` quasi-affine `⟹` `Z` quasi-affine.** For a closed immersion `i : Z ⟶ X` of Noetherian
schemes inducing a homeomorphism of underlying spaces, quasi-affineness of `X` gives
quasi-affineness of `Z`: a closed immersion is an affine morphism, so
`AlgebraicGeometry.Scheme.IsQuasiAffine.of_isAffineHom` applies. -/
theorem isQuasiAffine_of_isQuasiAffine [IsClosedImmersion i] [Surjective i] [IsNoetherian X]
    (hX : X.IsQuasiAffine) : Z.IsQuasiAffine :=
  have := hX
  Scheme.IsQuasiAffine.of_isAffineHom i

/-! ### The converse, and Stacks Tag 0B7K -/

/-- **`Z` quasi-affine `⟹` `X` quasi-affine.** For a closed immersion `i : Z ⟶ X` surjective on
points onto a locally Noetherian scheme, quasi-affineness of `Z` gives quasi-affineness of `X`:
`i^* 𝒪_X ≅ 𝒪_Z` is ample ([Stacks, Tag 01QE]), so `𝒪_X` is ample ([Stacks, Tag 09MS]). -/
theorem isQuasiAffine_of_isQuasiAffine_source [IsClosedImmersion i] [Surjective i]
    [IsLocallyNoetherian X] (hZ : Z.IsQuasiAffine) : X.IsQuasiAffine :=
  (isQuasiAffine_iff_isAmple X).mpr
    (isAmple_of_isAmple_modulePullback_of_surjective i (unitModule X)
      ((isQuasiAffine_iff_isAmple_modulePullback_unitModule i).mp hZ))

/-- **[Stacks, Tag 0B7K].** Let `i : Z ⟶ X` be a closed immersion of Noetherian schemes inducing a
homeomorphism of underlying topological spaces — that is, a closed immersion surjective on
points. Then `X` is quasi-affine if and only if `Z` is quasi-affine. -/
@[stacks 0B7K]
theorem isQuasiAffine_iff_isQuasiAffine [IsClosedImmersion i] [Surjective i] [IsNoetherian X] :
    X.IsQuasiAffine ↔ Z.IsQuasiAffine :=
  ⟨isQuasiAffine_of_isQuasiAffine i, isQuasiAffine_of_isQuasiAffine_source i⟩

/-! ### The same implications through the cohomological lift -/

/-- **`Z` quasi-affine `⟹` `X` quasi-affine, through
`Stacks.AmpleClosedImmersion.SectionsLiftAfterPower` for `𝒪_X`.** -/
theorem isQuasiAffine_of_sectionsLiftAfterPower [IsClosedImmersion i] [Surjective i]
    [IsLocallyNoetherian X]
    (hlift : Stacks.AmpleClosedImmersion.SectionsLiftAfterPower i (unitModule X))
    (hZ : Z.IsQuasiAffine) : X.IsQuasiAffine :=
  (isQuasiAffine_iff_isAmple X).mpr
    (isAmple_of_isAmple_modulePullback i (unitModule X) hlift
      ((isQuasiAffine_iff_isAmple_modulePullback_unitModule i).mp hZ))

/-- **`X` quasi-affine `⟺` `Z` quasi-affine, through
`Stacks.AmpleClosedImmersion.SectionsLiftAfterPower` for `𝒪_X`.** -/
theorem isQuasiAffine_iff_of_sectionsLiftAfterPower [IsClosedImmersion i] [Surjective i]
    [IsNoetherian X]
    (hlift : Stacks.AmpleClosedImmersion.SectionsLiftAfterPower i (unitModule X)) :
    X.IsQuasiAffine ↔ Z.IsQuasiAffine :=
  ⟨isQuasiAffine_of_isQuasiAffine i, isQuasiAffine_of_sectionsLiftAfterPower i hlift⟩

/-! ### The hypotheses are satisfiable, and not only by an isomorphism -/

/-- The square-zero ideal `(2)` of `ℤ/4`. -/
abbrev squareZeroIdeal : Ideal (ZMod 4) := Ideal.span {(2 : ZMod 4)}

/-- `(2)` consists of nilpotents in `ℤ/4`, since `2 ^ 2 = 0`. -/
theorem squareZeroIdeal_le_nilradical : squareZeroIdeal ≤ nilradical (ZMod 4) := by
  rw [Ideal.span_le]
  intro x hx
  simp only [Set.mem_singleton_iff] at hx
  subst hx
  exact mem_nilradical.mpr ⟨2, by decide⟩

/-- **A genuine nilpotent thickening**: the closed immersion `Spec(ℤ/4 ⧸ (2)) ⟶ Spec(ℤ/4)` cut out
by the square-zero ideal `(2)`. Its source is `Spec(ℤ/2)`. -/
noncomputable def dualNumberThickening :
    Spec (CommRingCat.of (ZMod 4 ⧸ squareZeroIdeal)) ⟶ Spec (CommRingCat.of (ZMod 4)) :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk squareZeroIdeal))

/-- The thickening is a closed immersion: it is `Spec` of a surjective ring map. -/
instance isClosedImmersion_dualNumberThickening : IsClosedImmersion dualNumberThickening :=
  IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective

/-- The thickening is surjective on points, hence a homeomorphism of underlying spaces: the
ideal it is cut out by consists of nilpotents, so it is contained in every prime. -/
instance surjective_dualNumberThickening : Surjective dualNumberThickening :=
  ⟨(PrimeSpectrum.comap_quotientMk_bijective_of_le_nilradical
    squareZeroIdeal_le_nilradical).surjective⟩

/-- **The thickening is not an isomorphism.** Its source has two points' worth of global
sections fewer than its target: `2` is a nonzero element of `ℤ/4` killed by the quotient map, so
that map is not injective, and `AlgebraicGeometry.isIso_SpecMap_iff` turns that into the claim.

This is what makes `Stacks.AmpleSurjectiveThickening.dualNumberThickening` a non-degenerate
witness for the hypotheses above: for `i = 𝟙 X` the source and target coincide and
[Stacks, Tag 0B7K] says nothing, whereas here `Z` and `X` are genuinely different schemes with
the same underlying space. -/
theorem not_isIso_dualNumberThickening : ¬ IsIso dualNumberThickening := by
  rw [dualNumberThickening, isIso_SpecMap_iff]
  intro h
  have h2 : (Ideal.Quotient.mk squareZeroIdeal) (2 : ZMod 4) =
      (Ideal.Quotient.mk squareZeroIdeal) (0 : ZMod 4) := by
    rw [map_zero]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)
  exact absurd (h.injective h2) (by decide)

/-- **The hypotheses of [Stacks, Tag 0B7K] are satisfiable by a morphism that is not an
isomorphism.** `Spec(ℤ/4)` is Noetherian, `Stacks.AmpleSurjectiveThickening.dualNumberThickening`
is a surjective closed immersion onto it, and it is not an isomorphism. -/
theorem dualNumberThickening_hypotheses :
    IsNoetherian (Spec (CommRingCat.of (ZMod 4))) ∧
      IsClosedImmersion dualNumberThickening ∧ Surjective dualNumberThickening ∧
      ¬ IsIso dualNumberThickening :=
  ⟨inferInstance, inferInstance, inferInstance, not_isIso_dualNumberThickening⟩

/-- [Stacks, Tag 0B7K] applied to that witness: the source of the thickening is quasi-affine
because `Spec(ℤ/4)` is. -/
theorem isQuasiAffine_source_dualNumberThickening :
    (Spec (CommRingCat.of (ZMod 4 ⧸ squareZeroIdeal))).IsQuasiAffine :=
  (isQuasiAffine_iff_isQuasiAffine dualNumberThickening).mp inferInstance

end Stacks.AmpleSurjectiveThickening

end
