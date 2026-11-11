module

public import StacksFrontier.AlgebraicGeometry.Blowup.FiniteOverLocalDimensionOne
public import StacksFrontier.AlgebraicGeometry.Divisors.Reflexive.AffineColimitReflexivePower
public import StacksFrontier.AlgebraicGeometry.Blowup.NormalizedBlowUpNagataExtra
public import StacksFrontier.AlgebraicGeometry.Blowup.RegularSurfaceBlowup
public import StacksFrontier.AlgebraicGeometry.Blowup.Transform.Birational
public import StacksFrontier.AlgebraicGeometry.F6Rank89.IdealSheafStalk
public import StacksFrontier.AlgebraicGeometry.Morphisms.Birational.IrreducibleCriterion
public import StacksFrontier.AlgebraicGeometry.Morphisms.Birational.Stability
public import StacksFrontier.AlgebraicGeometry.NagataNormalization.IntegralClosureBaseChange
public import StacksFrontier.AlgebraicGeometry.NormalizationBaseChange.Normal
public import StacksFrontier.AlgebraicGeometry.Pullback.StalkFromSpecStalk
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Boundedness.BlowUpFirstCohomology
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Boundedness.RegularLocalRingTransfer
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.DominateByNormalizedBlowUps.Basic
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalDoublePoints.StageSituation
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalSingularities.BlowUpClosedPointDimension
import StacksCore.Tactic.EgaSgaAttribute

/-!
# A Nagata regular local ring of dimension two defines a rational singularity

Let `A` be a Nagata regular local ring of dimension two and `X ⟶ Spec(A)` a modification with
`X` normal. By [Stacks, Tag 0BBT] the modification is dominated by a scheme `Z` obtained from the
normalization of `Spec(A)` by finitely many normalized blowups at closed points. Along that chain
every scheme is regular, its local rings at closed points have dimension two, and
`H¹(Z, 𝒪_Z) = 0`:

* the normalization of `Spec(A)` is `Spec(A)` itself, which is affine;
* blowing up a closed point of a regular scheme at which the local ring has dimension two gives a
  regular scheme ([Stacks, Tag 0AGR] after the flat base change of [Stacks, Tag 0805]), whose local
  rings at closed points again have dimension two; so the blowup is normal and the normalized
  blowup is the blowup;
* the vanishing of `H¹(𝒪)` survives such a blowup
  (`AlgebraicGeometry.isZeroFirstStructureSheafCohomology_blowUp_of_isRegularLocalRing`, which is
  [Stacks, Tag 0AGS] with [Stacks, Tag 0AXF] in the form needed here).

Finally `H¹(X, 𝒪_X)` embeds into `H¹(Z, 𝒪_Z)` ([Stacks, Tag 0AXF]), which is
`AlgebraicGeometry.firstStructureSheafCohomologyVanishes_of_dominates`.

The source's proof dominates `X` by a sequence of blowups in closed points through
[Stacks, Tag 0AHI]; here [Stacks, Tag 0BBT] plays that role, which is where the Nagata hypothesis
of the statement is used.

## Main results

* `AlgebraicGeometry.definesRationalSingularity_of_isRegularLocalRing_of_isNagataRing`:
  [Stacks, Tag 0B4Q].

## Implementation notes

This is the complete statement of [Stacks, Tag 0B4Q] under exactly the source's hypotheses — `A`
is a Nagata regular local ring with `ringKrullDim A = 2` — with no cited input assumed, and it
carries the tag (as does its `letI` restatement
`AlgebraicGeometry.definesRationalSingularity_of_isRegularLocalRing_of_ringKrullDim_eq_two`).
It supersedes the earlier conditional forms of the source's argument, which are no longer
registered:

* `AlgebraicGeometry.definesRationalSingularity_of_isRegularLocalRing`
  (`Boundedness.RegularLocalRing`) assumes `dominate` ([Stacks, Tag 0AHI] with Tags 0AGR and
  0567), `transfer` (the injectivity half of [Stacks, Tag 0AXF]) and `blowUpStep`
  ([Stacks, Tag 0AGS] with Tag 0AXF);
* `AlgebraicGeometry.definesRationalSingularity_of_isRegularLocalRing_of_dominate`
  (`Boundedness.RegularLocalRingTransfer`) and
  `AlgebraicGeometry.definesRationalSingularity_of_isRegularLocalRing_unconditional`
  (`Boundedness.RegularLocalRingRationalSingularity`) assume `dominate` and `blowUpStep`.

Here `transfer` is `AlgebraicGeometry.firstStructureSheafCohomologyVanishes_of_dominates`,
`blowUpStep` is
`AlgebraicGeometry.isZeroFirstStructureSheafCohomology_blowUp_of_isRegularLocalRing`, and
`dominate` is replaced by the domination of [Stacks, Tag 0BBT].

## References

* [Stacks Project, Tag 0B4Q](https://stacks.math.columbia.edu/tag/0B4Q)
* [Stacks Project, Tag 0BBT](https://stacks.math.columbia.edu/tag/0BBT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Stacks.ResolutionOfSurfaces

universe u

namespace AlgebraicGeometry

/-- Away from the centre of a blowup at a closed point, the blowup is a local isomorphism. -/
theorem isIso_stalkMap_blowUpToBase_vanishingIdeal_of_ne {W : Scheme.{u}} (w : W)
    (hw : IsClosed ({w} : Set W)) (M : W.IdealSheafData)
    (hM : M = Scheme.IdealSheafData.vanishingIdeal ⟨{w}, hw⟩) (q : blowUp M)
    (hq : blowUpToBase M q ≠ w) : IsIso ((blowUpToBase M).stalkMap q) := by
  let U : W.Opens := ⟨M.supportᶜ, M.support.isClosed.isOpen_compl⟩
  have hqU : q ∈ blowUpToBase M ⁻¹ᵁ U := by
    change blowUpToBase M q ∉ (M.support : Set W)
    simpa [hM] using hq
  exact isIso_stalkMap_of_isIso_morphismRestrict (blowUpToBase M)
    (isIso_blowUp_restrict_compl_support M) hqU

/-- A closed map sends closed points to closed points. -/
private theorem isClosed_singleton_apply {α β : Type*} [TopologicalSpace α] [TopologicalSpace β]
    {f : α → β} (hf : IsClosedMap f) {a : α} (ha : IsClosed ({a} : Set α)) :
    IsClosed ({f a} : Set β) := by
  rw [← Set.image_singleton]
  exact hf _ ha

/-- If a morphism is an isomorphism on stalks at `x`, the local ring at `x` is regular as soon as
the local ring at the image is. -/
private theorem isRegularLocalRing_stalk_of_isIso_stalkMap {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X)
    [IsIso (f.stalkMap x)] (h : IsRegularLocalRing (Y.presheaf.stalk (f x))) :
    IsRegularLocalRing (X.presheaf.stalk x) :=
  IsRegularLocalRing.of_ringEquiv (asIso (f.stalkMap x)).commRingCatIsoToRingEquiv

/-- If a morphism is an isomorphism on stalks at `x`, the local rings at `x` and at its image have
the same Krull dimension. -/
private theorem ringKrullDim_stalk_eq_of_isIso_stalkMap {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X)
    [IsIso (f.stalkMap x)] :
    ringKrullDim (X.presheaf.stalk x) = ringKrullDim (Y.presheaf.stalk (f x)) :=
  (ringKrullDim_eq_of_ringEquiv (asIso (f.stalkMap x)).commRingCatIsoToRingEquiv).symm

/-- **The local rings of the blowup of a regular scheme at a closed point of dimension two are
regular.** Over the centre the blowup is, after the flat base change `Spec 𝒪_{W, w} ⟶ W`, the
blowup of a regular local ring of dimension two in its maximal ideal, which is regular
([Stacks, Tag 0AGR]); away from the centre the blowup is an isomorphism. -/
@[ega "IV 19.4.4" "special case"]
theorem isRegularLocalRing_stalk_blowUp {W : Scheme.{u}} (w : W) (hw : IsClosed ({w} : Set W))
    (hreg : ∀ y : W, IsRegularLocalRing (W.presheaf.stalk y))
    (hdim : ringKrullDim (W.presheaf.stalk w) = 2) (M : W.IdealSheafData)
    (hM : M = Scheme.IdealSheafData.vanishingIdeal ⟨{w}, hw⟩) (q : blowUp M) :
    IsRegularLocalRing ((blowUp M).presheaf.stalk q) := by
  by_cases hq : blowUpToBase M q = w
  · have := hreg w
    have : Flat (W.fromSpecStalk w) := flat_fromSpecStalk W w
    obtain ⟨h, hpb⟩ := exists_isPullback_blowUpToBase_comap (W.fromSpecStalk w) M
    have : Flat h := MorphismProperty.of_isPullback (P := @Flat) hpb inferInstance
    have : IsPreimmersion h :=
      MorphismProperty.of_isPullback (P := @IsPreimmersion) hpb inferInstance
    have hregBlow : IsRegular (blowUp (M.comap (W.fromSpecStalk w))) := by
      rw [hM, comap_fromSpecStalk_vanishingIdeal_singleton W w hw]
      exact isRegular_blowUp_maximalIdeal _ hdim
    obtain ⟨v, -, rfl⟩ := Scheme.exists_preimage_of_isPullback hpb
      (IsLocalRing.closedPoint (W.presheaf.stalk w)) q
      (Scheme.fromSpecStalk_closedPoint.trans hq.symm)
    have : IsIso (h.stalkMap v) := isIso_stalkMap_of_flat_preimmersion h v
    have := AlgebraicGeometry.IsRegular.isRegularLocalRing_stalk hregBlow v
    exact IsRegularLocalRing.of_ringEquiv (asIso (h.stalkMap v)).commRingCatIsoToRingEquiv.symm
  · have := isIso_stalkMap_blowUpToBase_vanishingIdeal_of_ne w hw M hM q hq
    exact isRegularLocalRing_stalk_of_isIso_stalkMap (blowUpToBase M) q (hreg _)

/-- **The local rings of the blowup at its closed points have dimension two**, if those of the
scheme being blown up do and the centre is a regular closed point. Over the centre this is the
two-dimensionality of the local rings at the closed points of the blowup of a two-dimensional
local ring in its maximal ideal; away from the centre the blowup is an isomorphism and, being
proper, carries closed points to closed points. -/
theorem ringKrullDim_stalk_blowUp_of_isClosed {W : Scheme.{u}} [IsLocallyNoetherian W] (w : W)
    (hw : IsClosed ({w} : Set W)) (hreg : IsRegularLocalRing (W.presheaf.stalk w))
    (hdim : ∀ y : W, IsClosed ({y} : Set W) → ringKrullDim (W.presheaf.stalk y) = 2)
    (M : W.IdealSheafData) (hM : M = Scheme.IdealSheafData.vanishingIdeal ⟨{w}, hw⟩)
    (q : blowUp M) (hqc : IsClosed ({q} : Set (blowUp M))) :
    ringKrullDim ((blowUp M).presheaf.stalk q) = 2 := by
  by_cases hq : blowUpToBase M q = w
  · have : IsNormalDomain (W.presheaf.stalk w) := isNormalDomain_of_isRegularLocalRing _
    subst hM
    obtain ⟨x, hxc, ⟨e⟩⟩ := exists_isClosed_ringEquiv_stalk_blowUp_maximalIdealSheaf
      (W.presheaf.stalk w) w hw (RingEquiv.refl _) q hq hqc
    rw [← ringKrullDim_eq_of_ringEquiv e]
    exact ringKrullDim_stalk_blowUp_maximalIdeal_eq_two_of_isClosed _ (hdim w hw) x hxc
  · have := isIso_stalkMap_blowUpToBase_vanishingIdeal_of_ne w hw M hM q hq
    rw [ringKrullDim_stalk_eq_of_isIso_stalkMap (blowUpToBase M) q]
    exact hdim _ (isClosed_singleton_apply (blowUpToBase M).isClosedMap hqc)

/-- A scheme all of whose local rings are regular is normal. -/
theorem isNormal_of_forall_isRegularLocalRing {X : Scheme.{u}}
    (h : ∀ x : X, IsRegularLocalRing (X.presheaf.stalk x)) : IsNormal X where
  stalk_isDomain x := by
    have := h x
    exact (isNormalDomain_of_isRegularLocalRing (X.presheaf.stalk x)).1
  stalk_normal x := by
    have := h x
    exact (isNormalDomain_of_isRegularLocalRing (X.presheaf.stalk x)).2

/-- The stalks of the spectrum of a regular local ring are regular, and the stalk at the closed
point has the dimension of the ring. -/
theorem isRegularLocalRing_stalk_spec (A : Type u) [CommRing A] [IsRegularLocalRing A]
    (p : Spec (.of A)) : IsRegularLocalRing ((Spec (.of A)).presheaf.stalk p) := by
  have : IsRegularRing A := ((IsLocalRing.isRegularRing_tfae (R := A)).out 1 3).mp ‹_›
  have : p.asIdeal.IsPrime := p.2
  have : IsRegularLocalRing (Localization.AtPrime p.asIdeal) :=
    IsRegularRing.isRegularLocalRing_of_isLocalization p.asIdeal _
  exact IsRegularLocalRing.of_ringEquiv
    (Spec.stalkIso (CommRingCat.of A) p).commRingCatIsoToRingEquiv.symm

/-- The generic point of an integral scheme is not a point whose local ring has nonzero
dimension. -/
theorem genericPoint_ne_of_ringKrullDim_stalk_ne_zero {X : Scheme.{u}} [IsIntegral X] {z : X}
    (h : ringKrullDim (X.presheaf.stalk z) ≠ 0) : genericPoint X ≠ z := by
  rintro rfl
  exact h (ringKrullDim_eq_zero_of_field X.functionField)

/-- The normalization of the spectrum of a regular local ring `A` of dimension two is integral,
birational and proper over `Spec(A)`, has regular local rings, has two-dimensional local rings at
its closed points, and has `H¹(𝒪) = 0`. -/
theorem normalization_spec_invariant (A : Type u) [CommRing A] [IsRegularLocalRing A]
    (hdim : ringKrullDim A = 2)
    (hS : ∀ U : (Spec (.of A)).Opens, IsCompact (U : Set (Spec (.of A))) →
      (irreducibleComponents U).Finite)
    (hproper : IsProper (Scheme.normalization (Spec (.of A)) hS)) :
    IsIntegral (Scheme.normalizationScheme (Spec (.of A)) hS) ∧
      IsBirational (Scheme.normalization (Spec (.of A)) hS) ∧
      IsProper (Scheme.normalization (Spec (.of A)) hS) ∧
      (∀ z : Scheme.normalizationScheme (Spec (.of A)) hS,
        IsRegularLocalRing ((Scheme.normalizationScheme (Spec (.of A)) hS).presheaf.stalk z)) ∧
      (∀ z : Scheme.normalizationScheme (Spec (.of A)) hS,
        IsClosed ({z} : Set (Scheme.normalizationScheme (Spec (.of A)) hS)) →
        ringKrullDim ((Scheme.normalizationScheme (Spec (.of A)) hS).presheaf.stalk z) = 2) ∧
      IsZeroFirstStructureSheafCohomology (Scheme.normalizationScheme (Spec (.of A)) hS) := by
  have : IsDomain A := IsRegularLocalRing.isDomain A
  have : IsIntegrallyClosed A := isIntegrallyClosed_of_isRegularLocalRing A
  have : IsNormal (Spec (.of A)) := isNormal_spec (.of A)
  have := Scheme.isIso_normalization_of_isNormal (Spec (.of A)) hS
  set g := Scheme.normalization (Spec (.of A)) hS
  have : Nonempty (Scheme.normalizationScheme (Spec (.of A)) hS) :=
    ⟨inv g (IsLocalRing.closedPoint A)⟩
  have : IsIntegral (Scheme.normalizationScheme (Spec (.of A)) hS) :=
    isIntegral_of_isOpenImmersion g
  have : IsAffine (Scheme.normalizationScheme (Spec (.of A)) hS) := IsAffine.of_isIso g
  refine ⟨inferInstance, isBirational_of_isIso_stalkMap_genericPoint g, hproper, fun z => ?_,
    fun z hz => ?_, firstStructureSheafCohomologyVanishes_of_isAffine _⟩
  · exact isRegularLocalRing_stalk_of_isIso_stalkMap g z (isRegularLocalRing_stalk_spec A (g z))
  · have hgz : IsClosed ({g z} : Set (Spec (.of A))) :=
      isClosed_singleton_apply g.homeomorph.isClosedMap hz
    have hcl : g z = IsLocalRing.closedPoint A := by
      have hmax := (PrimeSpectrum.isClosed_singleton_iff_isMaximal _).mp hgz
      exact PrimeSpectrum.ext (IsLocalRing.eq_maximalIdeal hmax)
    rw [ringKrullDim_stalk_eq_of_isIso_stalkMap g z, hcl, ringKrullDim_stalk_closedPoint, hdim]

/-- The invariant of `AlgebraicGeometry.normalizedBlowUpChain_invariant` passes from a scheme `X`
over the spectrum of a regular local ring to its normalized blowup at a closed point. -/
theorem normalizedBlowUp_invariant (A : Type u) [CommRing A] [IsRegularLocalRing A]
    {X : Scheme.{u}} {f : X ⟶ Spec (.of A)}
    (hX : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite)
    (z : X) (hz : IsClosed ({z} : Set X))
    (hproper : IsProper (Stacks.Blowup.normalizedBlowUp X hX z hz ≫ f))
    [IsIntegral X] (hbir : IsBirational f) [IsProper f]
    (hreg : ∀ x : X, IsRegularLocalRing (X.presheaf.stalk x))
    (hdim2 : ∀ x : X, IsClosed ({x} : Set X) → ringKrullDim (X.presheaf.stalk x) = 2)
    (hH1 : IsZeroFirstStructureSheafCohomology X) :
    IsIntegral (Stacks.Blowup.normalizedBlowUpScheme X hX z hz) ∧
      IsBirational (Stacks.Blowup.normalizedBlowUp X hX z hz ≫ f) ∧
      IsProper (Stacks.Blowup.normalizedBlowUp X hX z hz ≫ f) ∧
      (∀ q : Stacks.Blowup.normalizedBlowUpScheme X hX z hz,
        IsRegularLocalRing ((Stacks.Blowup.normalizedBlowUpScheme X hX z hz).presheaf.stalk q)) ∧
      (∀ q : Stacks.Blowup.normalizedBlowUpScheme X hX z hz,
        IsClosed ({q} : Set (Stacks.Blowup.normalizedBlowUpScheme X hX z hz)) →
        ringKrullDim ((Stacks.Blowup.normalizedBlowUpScheme X hX z hz).presheaf.stalk q) = 2) ∧
      IsZeroFirstStructureSheafCohomology (Stacks.Blowup.normalizedBlowUpScheme X hX z hz) := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  set M := Scheme.IdealSheafData.vanishingIdeal (⟨{z}, hz⟩ : Closeds X) with hM
  have hregB := isRegularLocalRing_stalk_blowUp z hz hreg (hdim2 z hz) M hM
  have : IsNormal (blowUp M) := isNormal_of_forall_isRegularLocalRing hregB
  have hMne : M ≠ ⊥ := vanishingIdeal_singleton_ne_bot z hz
    (genericPoint_ne_of_ringKrullDim_stalk_ne_zero
      fun h => absurd ((hdim2 z hz).symm.trans h) (by decide))
  have : IsIntegral (blowUp M) := isIntegral_blowUp M hMne
  let e := Stacks.Blowup.normalizedBlowUpSchemeIsoBlowUp hX z hz
  have : Nonempty (Stacks.Blowup.normalizedBlowUpScheme X hX z hz) :=
    ⟨e.inv (Nonempty.some inferInstance)⟩
  have : IsIntegral (Stacks.Blowup.normalizedBlowUpScheme X hX z hz) :=
    isIntegral_of_isOpenImmersion e.hom
  refine ⟨inferInstance, ?_, hproper, fun q => ?_, fun q hq => ?_, ?_⟩
  · rw [← Stacks.Blowup.normalizedBlowUpSchemeIsoBlowUp_hom_blowUpToBase hX z hz, Category.assoc]
    exact (isBirational_of_isIso_stalkMap_genericPoint e.hom).comp
      ((isBirational_blowUpToBase M hMne).comp hbir)
  · exact isRegularLocalRing_stalk_of_isIso_stalkMap e.hom q (hregB _)
  · rw [ringKrullDim_stalk_eq_of_isIso_stalkMap e.hom q]
    exact ringKrullDim_stalk_blowUp_of_isClosed z hz (hreg z) hdim2 M hM (e.hom q)
      (isClosed_singleton_apply e.hom.homeomorph.isClosedMap hq)
  · exact isZeroFirstStructureSheafCohomology_of_isIso_c e.inv
      (isZeroFirstStructureSheafCohomology_blowUp_of_isRegularLocalRing z hz (hreg z)
        (hdim2 z hz) hH1)

/-- **The invariant along a chain of normalized blowups of the spectrum of a regular local ring
of dimension two.** Every member of the chain is integral, birational and proper over `Spec(A)`,
has regular local rings, has two-dimensional local rings at its closed points, and has
`H¹(𝒪) = 0`. -/
theorem normalizedBlowUpChain_invariant (A : Type u) [CommRing A] [IsRegularLocalRing A]
    (hdim : ringKrullDim A = 2)
    (hS : ∀ U : (Spec (.of A)).Opens, IsCompact (U : Set (Spec (.of A))) →
      (irreducibleComponents U).Finite)
    {Z : Scheme.{u}} {g : Z ⟶ Spec (.of A)} (hchain : NormalizedBlowUpChain (Spec (.of A)) hS Z g) :
    IsIntegral Z ∧ IsBirational g ∧ IsProper g ∧
      (∀ z : Z, IsRegularLocalRing (Z.presheaf.stalk z)) ∧
      (∀ z : Z, IsClosed ({z} : Set Z) → ringKrullDim (Z.presheaf.stalk z) = 2) ∧
      IsZeroFirstStructureSheafCohomology Z := by
  induction hchain with
  | normalization hproper => exact normalization_spec_invariant A hdim hS hproper
  | blowUp previous hX z hz hproper ih =>
    obtain ⟨hint, hbir, hfproper, hreg, hdim2, hH1⟩ := ih
    exact normalizedBlowUp_invariant A hX z hz hproper hbir hreg hdim2 hH1

/-- **Stacks Project, Tag 0B4Q.** A Nagata regular local ring `A` of dimension two defines a
rational singularity: `H¹(X, 𝒪_X) = 0` for every modification `X ⟶ Spec(A)` with `X` normal.
(A regular local ring is a domain, which `DefinesRationalSingularity` needs as an instance; it is
supplied by `IsRegularLocalRing.isDomain`.)

The modification is dominated by a chain of normalized blowups at closed points
([Stacks, Tag 0BBT], which uses the Nagata hypothesis); along the chain every scheme is regular
with two-dimensional local rings at its closed points and has `H¹(𝒪) = 0`
(`AlgebraicGeometry.normalizedBlowUpChain_invariant`), and `H¹(X, 𝒪_X)` embeds into the
cohomology of the dominating scheme ([Stacks, Tag 0AXF]). Nothing beyond the source's
hypotheses is assumed; the conditional forms of the argument, which carry Tags 0AHI, 0AXF and
0AGS as hypotheses, are listed in the module docstring. -/
@[stacks 0B4Q]
theorem definesRationalSingularity_of_isRegularLocalRing_of_isNagataRing (A : Type u)
    [CommRing A] [IsRegularLocalRing A] [IsNagataRing A] (hdim : ringKrullDim A = 2) :
    @DefinesRationalSingularity A _ (IsRegularLocalRing.isDomain A) := by
  have : IsDomain A := IsRegularLocalRing.isDomain A
  intro X _ f hf
  have : IsProper f := hf.isProper
  obtain ⟨Z, g, h, hchain, hhf⟩ := exists_normalizedBlowUpChain_dominating
    (isNagataScheme_spec_of_isNagataRing A ‹_›)
    ((PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim A).trans hdim) f hf.isBirational
  obtain ⟨hint, hbir, hprop, -, -, hH1⟩ := normalizedBlowUpChain_invariant A hdim _ hchain
  exact firstStructureSheafCohomologyVanishes_of_dominates A f g h ‹_› hf ⟨hbir, hprop, hint⟩
    hhf hH1

end AlgebraicGeometry

end
