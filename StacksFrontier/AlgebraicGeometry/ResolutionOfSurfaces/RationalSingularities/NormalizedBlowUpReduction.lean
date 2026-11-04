module

public import Mathlib.RingTheory.KrullDimension.Basic
public import StacksFrontier.AlgebraicGeometry.Blowup.Transform.Birational
public import StacksFrontier.AlgebraicGeometry.Morphisms.Proper.Projective
public import StacksFrontier.AlgebraicGeometry.Morphisms.Birational.Stability
public import StacksFrontier.AlgebraicGeometry.NagataNormalization.IntegralClosureBaseChange
public import StacksFrontier.AlgebraicGeometry.Normalization.NormalizedBlowUpSequence
public import StacksFrontier.AlgebraicGeometry.NormalizationBaseChangeBirational.Basic
public import StacksFrontier.AlgebraicGeometry.NormalizationBirational.Basic
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Boundedness.RationalSingularity
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Boundedness.Reduction
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.DominateByNormalizedBlowUps.Basic
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.ModifyingLocalRings.NormalizedPointBlowupSequence
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Resolution.NormalizedBlowUps
public import StacksFrontier.RingTheory.IntegrallyClosed.Defs
public import StacksFrontier.RingTheory.Nagata.Defs
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Reduction to rational singularities by normalized blowups at closed points

Let `(A, 𝔪, κ)` be a local normal Nagata domain of dimension two for which reduction to rational
singularities is possible. [Stacks, Tag 0B4P] produces a finite sequence of normalized blowups at
closed points `X = Xₙ → ⋯ → X₁ → X₀ = Spec A` whose total space is normal and projective over `A`,
whose structure morphism is a modification, and all of whose closed-point local rings define
rational singularities.

## Main definitions

There are no new definitions: the sequence is `AlgebraicGeometry.NormalizedBlowUpSeq`, normality is
`AlgebraicGeometry.IsNormal`, being a modification is `AlgebraicGeometry.IsModification`, and the
rational-singularity condition on a local ring is
`AlgebraicGeometry.DefinesRationalSingularity`.

## Main results

* `AlgebraicGeometry.exists_maximal_length_normal_modification`: when reduction to rational
  singularities is possible, a normal modification of `Spec A` of maximal first-cohomology length
  exists.
* `AlgebraicGeometry.NormalizedBlowUpSeq.isModification`: over an integral, normal, Nagata,
  two-dimensional base the structure morphism of a sequence of normalized blowups at closed points
  is a modification.
* `AlgebraicGeometry.exists_normalizedBlowUpSeq_dominating`: [Stacks, Tag 0BBT] restated for
  sequences of normalized blowups over a normal base itself rather than over its normalization.
* `AlgebraicGeometry.exists_normalizedBlowUpSeq_isModification_dominating`: the part of the
  conclusion of [Stacks, Tag 0B4P] available here — every modification of `Spec A` is dominated by
  a sequence of normalized blowups at closed points with normal total space whose structure
  morphism is again a modification.

## Implementation notes

The sequence of blowups is the inductive predicate `AlgebraicGeometry.NormalizedBlowUpSeq`, whose
base case is the identity of the base and whose step is the normalized blowup at a closed point of
the current stage. Tag 0BBT is stated for `AlgebraicGeometry.NormalizedBlowUpChain`, whose base
case is the *normalization* of the base; over a normal base that normalization is an isomorphism,
and `factorsAsNormalizedPointBlowups_of_normalizedBlowUpChain` transports such a chain across it,
using the isomorphism-robust `Stacks.ResolutionOfSurfaces.FactorsAsNormalizedPointBlowups`. The two
inductive predicates `NormalizedBlowUpSeq S` and
`Stacks.ResolutionOfSurfaces.NormalizedPointBlowupChain S Set.univ` have the same constructors.

Birationality of a normalized blowup is the composite of birationality of the blowup of a nonzero
ideal sheaf on an integral scheme with birationality of a normalization, so it needs a point
other than the centre; that is where two-dimensionality of the base enters, propagated along the
sequence by surjectivity of proper birational morphisms.

### What Stacks 0B4P still needs, and what is *not* missing

No attribute for this tag is carried in this file.  (That sentence deliberately avoids spelling the
attribute out: a bare tag grep matches prose, so denials written with the literal attribute syntax
read as coverage to any scanner that does not skip comments.  Use `tag_grep`, and read its
citations rather than its summary flag.)  The conclusion of the tag has two parts this file does
not reach — that the local ring at every closed point defines a rational singularity, and that the
structure morphism is projective — and each is blocked upstream.  What follows was checked
declaration by declaration, because a tag being *present* is not the clause being *proved*: several
of these tags are carried, but only for a narrower clause or over an undischarged hypothesis.

* `H²(X, 𝒪_X) = 0`, hence the **first** conclusion of [Stacks, Tag 0AXF] (the Leray short exact
  sequence), is absent in the half that is needed.
  `SemistableReduction/HigherDirectImageBoundedness.lean` declines it in
  its own prose: surjectivity onto `H⁰(X, R¹g_*𝒪_{X'})` is what is missing, so no part of the
  first conclusion is asserted there; only conclusions (2) and (3) are tagged.  The injectivity
  half of the first conclusion *is* proved, elsewhere — as
  `AlgebraicGeometry.firstStructureSheafCohomologyVanishes_of_isModification` of
  `…/ResolutionOfSurfaces/Boundedness/FirstCohomologyModificationTransfer.lean` — so what is
  absent is the surjectivity alone.  It reduces to
  [Stacks, Tag 02V7] at fibre dimension one, which is carried only at fibre dimension *zero*, and
  that in turn to [Stacks, Tags 02OD and 02O5].  Of those, 02OD is carried on definitions only —
  its clause string says the conclusion is not asserted — and 02O5 is carried in
  `…/ProperCoherenceWitness/ChowStalk.lean`.  This is the input the maximality step of the
  source's proof needs.
* [Stacks, Tag 02KH], flat base change for cohomology, is carried only in degree zero or as a
  vanishing criterion for projective space, so it does not give injectivity of `H¹` under flat
  pullback.  `PullbackSections/Qcqs.lean` records the two names that would and says neither is
  proved here.
* Projectivity of a blowup, [Stacks, Tag 02NS] part (1), is absent;
  `Blowup/ReesAlgebra/TwistAmple.lean` carries part (2) only, over a `TwistTransition` datum that
  is [Stacks, Tag 01NO] (3)+(4) and is not constructed here.
* [Stacks, Tag 0B3I] is carried over the named hypothesis `PushforwardIsRelativeProj`, and no
  declaration in the library concludes it; it occurs only in binder position. [Stacks, Tags
  087S (1) and 0C4P] are proved, as `AlgebraicGeometry.isProjectiveMorphism_of_isProjective` and
  `AlgebraicGeometry.IsProjective.comp`.
* [Stacks, Tag 0E8Q] is carried on the canonical functor and comparison; its full faithfulness
  is proved and its essential surjectivity is not, so the `IsEquivalence` assertion of its third
  label is not earned. [Stacks, Tag 0BFV] does not wait on it: the local-model step takes full
  faithfulness from Tag 0E8Q and essential surjectivity from [Stacks, Tag 0B3X].

Two notes for whoever closes this.  The projectivity half has an H-form route:
`isProjectiveMorphism_iff_isHQuasiProjective_and_isProper`
([Stacks, Tag 0BCL] clause (2)) and `IsProjectiveMorphism.comp` are unconditional, and
`NormalizedBlowUpSeq.properties` supplies properness, so the H-form route reduces the whole clause
to [Stacks, Tag 01NO] for the blowup step and `PushforwardIsRelativeProj` for the normalization
step.  And the `H²` vanishing must not be routed through
`RationalSingularities/QuasicoherentCohomology.lean`, which derives it *from* a
rational-singularity hypothesis — the conclusion 0B4P is trying to establish.

## References

* [Stacks Project, Tag 0B4P](https://stacks.math.columbia.edu/tag/0B4P)
* [Stacks Project, Tag 0BBT](https://stacks.math.columbia.edu/tag/0BBT)
* [Stacks Project, Tag 0BGL](https://stacks.math.columbia.edu/tag/0BGL)
* [Stacks Project, Tag 0AXF](https://stacks.math.columbia.edu/tag/0AXF)
* [Stacks Project, Tag 02KH](https://stacks.math.columbia.edu/tag/02KH)
* [Stacks Project, Tag 02NS](https://stacks.math.columbia.edu/tag/02NS)
* [Stacks Project, Tag 0BCL](https://stacks.math.columbia.edu/tag/0BCL)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

/-! ### Elementary closure properties of modifications -/

/-- A composite of modifications is a modification. -/
theorem IsModification.comp {X Y Z : Scheme.{u}} [IsIntegral Y] [IsIntegral Z]
    {f : X ⟶ Y} {g : Y ⟶ Z} (hf : IsModification f) (hg : IsModification g) :
    IsModification (f ≫ g) := by
  let : IsProper f := hf.isProper
  let : IsProper g := hg.isProper
  exact ⟨hf.isBirational.comp hg.isBirational, inferInstance, hf.source_isIntegral⟩

/-! ### A normal modification of maximal first-cohomology length -/

/-- If reduction to rational singularities is possible for a normal local domain `A`, then among
the normal modifications of `Spec A` there is one whose first structure-sheaf cohomology has
maximal `A`-length. The lengths are bounded by a natural number and hence finite, so the set of
attained lengths is a finite set of natural numbers. -/
theorem exists_maximal_length_normal_modification
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNormalDomain A]
    (hReduction : IsReductionToRationalSingularitiesPossible A) :
    ∃ (X : Scheme.{u}) (_ : IsNormal X) (f : X ⟶ Spec (.of A)),
      IsModification f ∧
        ∀ (Y : Scheme.{u}) (_ : IsNormal Y) (g : Y ⟶ Spec (.of A)), IsModification g →
          Module.length A (firstCohomologyAsBaseModule Y g) ≤
            Module.length A (firstCohomologyAsBaseModule X f) := by
  obtain ⟨bound, hBound⟩ := hReduction
  have hlen_nat : ∀ (Y : Scheme.{u}), IsNormal Y → ∀ (g : Y ⟶ Spec (.of A)), IsModification g →
      ∃ n : ℕ, Module.length A (firstCohomologyAsBaseModule Y g) = n := by
    intro Y hY g hg
    let := hY
    obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp
      (ne_of_lt (lt_of_le_of_lt (hBound Y g hg) (ENat.natCast_lt_top bound)))
    exact ⟨n, hn.symm⟩
  set lengthSet : Set ℕ := {n | ∃ (Y : Scheme.{u}) (_ : IsNormal Y) (g : Y ⟶ Spec (.of A)),
    IsModification g ∧
      Module.length A (firstCohomologyAsBaseModule Y g) = (n : ℕ∞)}
  have hsub : lengthSet ⊆ Set.Iic bound := by
    rintro n ⟨Y, hY, g, hg, hlen⟩
    let := hY
    have h := hBound Y g hg
    rw [hlen] at h
    exact_mod_cast h
  have hnonempty : lengthSet.Nonempty := by
    let : IsNormal (Spec (.of A)) :=
      isNormal_spec_of_isNormalRing (IsNormalRing.of_isIntegrallyClosed A)
    have hid : IsModification (𝟙 (Spec (.of A))) := isModification_id _
    obtain ⟨n, hn⟩ := hlen_nat _ inferInstance _ hid
    exact ⟨n, _, inferInstance, _, hid, hn⟩
  obtain ⟨_, ⟨X, hX, f, hf, hlen⟩, hmax⟩ :=
    Set.exists_max_image lengthSet id ((Set.finite_Iic bound).subset hsub) hnonempty
  refine ⟨X, hX, f, hf, fun Y hY g hg => ?_⟩
  obtain ⟨m, hm⟩ := hlen_nat Y hY g hg
  rw [hm, hlen]
  exact_mod_cast hmax m ⟨Y, hY, g, hg, hm⟩

/-! ### Modifications obtained from sequences of normalized blowups -/

/-- The reduced closed subscheme supported at a closed point of a reduced scheme with another
point is a nonzero ideal sheaf: its support is the single point, not the whole space. -/
theorem vanishingIdeal_singleton_ne_bot {X : Scheme.{u}} [IsReduced X] (x : X)
    (hx : IsClosed ({x} : Set X)) {y : X} (hy : y ≠ x) :
    Scheme.IdealSheafData.vanishingIdeal (⟨{x}, hx⟩ : Closeds X) ≠ ⊥ := by
  intro hbot
  have htop : (Scheme.IdealSheafData.vanishingIdeal (⟨{x}, hx⟩ : Closeds X)).support = ⊤ :=
    Scheme.IdealSheafData.support_eq_top_iff.mpr hbot
  have hsupp : ((Scheme.IdealSheafData.vanishingIdeal
      (⟨{x}, hx⟩ : Closeds X)).support : Set X) = {x} :=
    Scheme.IdealSheafData.coe_support_vanishingIdeal _
  have hyx : y ∈ ({x} : Set X) := by
    rw [← hsupp, htop]
    trivial
  exact hy (Set.mem_singleton_iff.mp hyx)

/-- The normalized blowup of an integral scheme at a closed point which is not the whole space
is birational: the blowup of a nonzero ideal is birational and so is a normalization. -/
theorem isBirational_normalizedBlowUp {X : Scheme.{u}} [IsIntegral X]
    (hX : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite)
    (x : X) (hx : IsClosed ({x} : Set X)) {y : X} (hy : y ≠ x) :
    IsBirational (Stacks.Blowup.normalizedBlowUp X hX x hx) := by
  set I := Scheme.IdealSheafData.vanishingIdeal (⟨{x}, hx⟩ : Closeds X) with hI
  have hIne : I ≠ ⊥ := vanishingIdeal_singleton_ne_bot x hx hy
  let : IsIntegral (blowUp I) := isIntegral_blowUp I hIne
  exact (Scheme.isBirational_normalization (blowUp I)
    (Stacks.Blowup.finite_irreducibleComponents_blowUp I hX)).comp
    (isBirational_blowUpToBase I hIne)

/-- The normalized blowup of an integral scheme at a closed point which is not its only point is
again integral: it is normal, hence reduced, and birational over the integral base. -/
theorem isIntegral_normalizedBlowUpScheme {X : Scheme.{u}} [IsIntegral X]
    (hX : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite)
    (x : X) (hx : IsClosed ({x} : Set X)) {y : X} (hy : y ≠ x) :
    IsIntegral (Stacks.Blowup.normalizedBlowUpScheme X hX x hx) :=
  integral_of_reduced_birational_to_integral (Stacks.Blowup.normalizedBlowUp X hX x hx)
    (isBirational_normalizedBlowUp hX x hx hy)

/-- The normalized blowup of a Nagata integral scheme at a closed point which is not its only
point is a modification. -/
theorem isModification_normalizedBlowUp {X : Scheme.{u}} [IsIntegral X]
    (hNagata : IsNagataScheme X)
    (hX : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite)
    (x : X) (hx : IsClosed ({x} : Set X)) {y : X} (hy : y ≠ x) :
    IsModification (Stacks.Blowup.normalizedBlowUp X hX x hx) :=
  ⟨isBirational_normalizedBlowUp hX x hx hy,
    (isNormal_isNagataScheme_and_isProper_normalizedBlowUp hX x hx hNagata).2.2,
    isIntegral_normalizedBlowUpScheme hX x hx hy⟩

/-- A proper birational morphism onto an integral scheme is surjective: its image is closed and
contains the generic point. -/
@[ega "I 2.2.9" "special case"]
theorem surjective_of_isProper_of_isBirational {X Y : Scheme.{u}} [IsIntegral Y] (f : X ⟶ Y)
    [IsProper f] (hf : IsBirational f) : Function.Surjective f := by
  have hη : genericPoint Y ∈ genericPoints Y := by simp [genericPoints_eq_singleton]
  obtain ⟨x, -, hmap⟩ := hf.bijOn.surjOn hη
  intro y
  refine (?_ : (Set.univ : Set Y) ⊆ Set.range f) (Set.mem_univ y)
  calc (Set.univ : Set Y) = closure ({genericPoint Y} : Set Y) := (genericPoint_spec Y).symm
    _ ⊆ closure (Set.range f) := closure_mono (Set.singleton_subset_iff.mpr ⟨x, hmap⟩)
    _ = Set.range f := f.isClosedMap.isClosed_range.closure_eq

/-- A two-dimensional scheme has at least two points: a one-point space is discrete, hence of
dimension at most zero. -/
theorem exists_ne_of_topologicalKrullDim_eq_two {X : Scheme.{u}}
    (hdim : topologicalKrullDim X = 2) (x : X) : ∃ y : X, y ≠ x := by
  by_contra h
  simp only [not_exists, ne_eq] at h
  have : Subsingleton X :=
    ⟨fun a b => (not_not.mp (h a)).trans (not_not.mp (h b)).symm⟩
  have : DiscreteTopology X := inferInstance
  have hzero : topologicalKrullDim X ≤ 0 := topologicalKrullDim_zero_of_discreteTopology X
  rw [hdim] at hzero
  norm_num at hzero

/-- The structure morphism of a sequence of normalized blowups at closed points over an
integral, normal, Nagata, two-dimensional base is a modification, and no stage of the sequence
is a one-point space. -/
theorem NormalizedBlowUpSeq.isModification {S X : Scheme.{u}} {f : X ⟶ S}
    (hseq : NormalizedBlowUpSeq S X f) (hS : IsNagataScheme S) [IsLocallyNoetherian S]
    [IsNormal S] [IsIntegral S] (hdim : topologicalKrullDim S = 2) :
    IsModification f ∧ ∀ x : X, ∃ y : X, y ≠ x := by
  induction hseq with
  | refl => exact ⟨isModification_id S, exists_ne_of_topologicalKrullDim_eq_two hdim⟩
  | blowUp prev hX x hx ih =>
    obtain ⟨hmod, hmany⟩ := ih
    let : IsIntegral _ := hmod.source_isIntegral
    obtain ⟨y, hy⟩ := hmany x
    have hstep := isModification_normalizedBlowUp (prev.properties hS).1 hX x hx hy
    let : IsProper (Stacks.Blowup.normalizedBlowUp _ hX x hx) := hstep.isProper
    have hsurj := surjective_of_isProper_of_isBirational
      (Stacks.Blowup.normalizedBlowUp _ hX x hx) hstep.isBirational
    refine ⟨hstep.comp hmod, fun w => ?_⟩
    obtain ⟨v₁, hv₁⟩ := hsurj x
    obtain ⟨v₂, hv₂⟩ := hsurj y
    by_cases hw : w = v₁
    · exact ⟨v₂, fun he => hy (by simp [← hv₁, ← hv₂, hw, he])⟩
    · exact ⟨v₁, Ne.symm hw⟩

/-! ### Domination of a modification by a sequence of normalized blowups -/

/-- A chain of normalized blowups at closed points over all of `X` is a sequence of normalized
blowups in the sense of `AlgebraicGeometry.NormalizedBlowUpSeq`: the two inductive predicates
have the same constructors. -/
theorem normalizedBlowUpSeq_of_normalizedPointBlowupChain {X Z : Scheme.{u}} {p : Z ⟶ X}
    (h : Stacks.ResolutionOfSurfaces.NormalizedPointBlowupChain X Set.univ Z p) :
    NormalizedBlowUpSeq X Z p := by
  induction h with
  | refl => exact NormalizedBlowUpSeq.refl
  | step _ hW w hw _ ih => exact ih.blowUp hW w hw

/-- Over a normal base the normalization step of a chain of Tag 0BGL is an isomorphism, so such
a chain factors as a sequence of normalized blowups at closed points of the base itself. -/
theorem factorsAsNormalizedPointBlowups_of_normalizedBlowUpChain {Y Z : Scheme.{u}} [IsNormal Y]
    {hY : ∀ U : Y.Opens, IsCompact (U : Set Y) → (irreducibleComponents U).Finite} {g : Z ⟶ Y}
    (h : NormalizedBlowUpChain Y hY Z g) :
    Stacks.ResolutionOfSurfaces.FactorsAsNormalizedPointBlowups Y Set.univ Z g := by
  induction h with
  | normalization _ =>
    have : IsIso (Scheme.normalization Y hY) :=
      (Scheme.isIso_normalization_iff_isNormal Y hY).2 inferInstance
    exact ((Stacks.ResolutionOfSurfaces.FactorsAsNormalizedPointBlowups.refl
      (Set.univ : Set Y)).of_iso (asIso (Scheme.normalization Y hY))).congr
      (Category.comp_id _)
  | blowUp _ hX x hx _ ih => exact ih.step hX x hx (Set.mem_univ _)

/-- **Tag 0BBT, restated for sequences of normalized blowups over the base itself.** A proper
birational morphism onto a normal Noetherian Nagata scheme of dimension two is dominated by a
finite sequence of normalized blowups at closed points of that scheme. -/
theorem exists_normalizedBlowUpSeq_dominating {X Y : Scheme.{u}} [IsNoetherian X] [IsNormal X]
    (hNagata : IsNagataScheme X) (hdim : topologicalKrullDim X = 2) (f : Y ⟶ X) [IsProper f]
    (hf : IsBirational f) :
    ∃ (Z W : Scheme.{u}) (g : Z ⟶ X) (gW : W ⟶ X) (h : Z ⟶ Y) (e : Z ≅ W),
      NormalizedBlowUpSeq X W gW ∧ e.hom ≫ gW = g ∧ h ≫ f = g := by
  obtain ⟨Z, g, h, hchain, hcomm⟩ :=
    Stacks.ResolutionOfSurfaces.exists_normalizedBlowUpChain_dominating hNagata hdim f hf
  obtain ⟨W, gW, hpc, e, he⟩ := factorsAsNormalizedPointBlowups_of_normalizedBlowUpChain hchain
  exact ⟨Z, W, g, gW, h, e, normalizedBlowUpSeq_of_normalizedPointBlowupChain hpc, he, hcomm⟩

/-- **Tag 0B4P, the part of the conclusion available here.** For a local normal Nagata domain
`A` of dimension two, every modification of `Spec A` is dominated by a finite sequence of
normalized blowups at closed points `W = Wₙ → ⋯ → W₀ = Spec A`, whose total space is normal and
whose structure morphism is again a modification. -/
theorem exists_normalizedBlowUpSeq_isModification_dominating
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNormalDomain A]
    (hNagata : IsNagataRing A) (hdim : ringKrullDim A = 2)
    {Y : Scheme.{u}} (f : Y ⟶ Spec (.of A)) (hf : IsModification f) :
    ∃ (W : Scheme.{u}) (g : W ⟶ Spec (.of A)) (h : W ⟶ Y),
      NormalizedBlowUpSeq (Spec (.of A)) W g ∧ IsNormal W ∧ IsModification g ∧ h ≫ f = g := by
  let : IsNoetherianRing A := hNagata.1
  let : IsNormal (Spec (.of A)) :=
    isNormal_spec_of_isNormalRing (IsNormalRing.of_isIntegrallyClosed A)
  have hNagataSpec : IsNagataScheme (Spec (.of A)) :=
    isNagataScheme_spec_of_isNagataRing A hNagata
  have hdimSpec : topologicalKrullDim (Spec (.of A)) = 2 :=
    (PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim A).trans hdim
  let : IsProper f := hf.isProper
  obtain ⟨Z, W, g, gW, h, e, hseq, he, hcomm⟩ :=
    exists_normalizedBlowUpSeq_dominating hNagataSpec hdimSpec f hf.isBirational
  obtain ⟨hmod, -⟩ := hseq.isModification hNagataSpec hdimSpec
  refine ⟨W, gW, e.inv ≫ h, hseq, (hseq.properties hNagataSpec).2.2.1, hmod, ?_⟩
  rw [Category.assoc, hcomm, ← he, Iso.inv_hom_id_assoc]

end AlgebraicGeometry

end
