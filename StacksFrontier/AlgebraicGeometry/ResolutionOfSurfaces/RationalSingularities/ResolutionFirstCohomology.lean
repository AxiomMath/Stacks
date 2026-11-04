module

public import
  StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Boundedness.NormalizedBlowUpSeqRegular
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Boundedness.SeparableGoUpAssembly
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Resolution.Basic
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Vanishing.DominatingBlowup
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Vanishing.OfModification

/-!
# A resolution with `H¹(X, 𝒪_X) = 0` makes the base a rational singularity

Let `A` be a Noetherian normal local Nagata domain of dimension two and let `f : X ⟶ Spec(A)` be
a resolution of singularities with `H¹(X, 𝒪_X) = 0`. Then `A` defines a rational singularity
([Stacks, Tag 0B4N]). This is the observation of the discussion in [Stacks, Section 0AXE] which
the proof of [Stacks, Tag 0EA2] invokes: every normal modification `X'` of `Spec(A)` is dominated
by a sequence `Z` of normalized blowups of `X` at closed points ([Stacks, Tag 0C5I], applied to
the rational map `X ⇢ X'` which is the identity over the punctured spectrum). Blowing up a closed
point with regular local ring of a normal surface is normal with regular local rings over the
centre, and it preserves `H¹(𝒪) = 0` (the computation behind [Stacks, Tag 0B4Q]); so
`H¹(Z, 𝒪_Z) = 0`, and `H¹(X', 𝒪_{X'})` injects into it ([Stacks, Tag 0AXF]).

## Main results

* `AlgebraicGeometry.isRegularLocalRing_and_isZero_of_normalizedBlowUpSeq_of_isModification`:
  along a sequence of normalized blowups at closed points of a normal modification `S` of
  `Spec(A)` whose closed points have regular local rings and with `H¹(S, 𝒪_S) = 0`, both
  properties persist.
* `AlgebraicGeometry.definesRationalSingularity_of_isResolution_of_isZero_structureSheafH1`:
  a resolution with `H¹(X, 𝒪_X) = 0` makes `A` a rational singularity.

## References

* [Stacks Project, Tag 0B4N](https://stacks.math.columbia.edu/tag/0B4N)
* [Stacks Project, Tag 0B4Q](https://stacks.math.columbia.edu/tag/0B4Q)
* [Stacks Project, Tag 0C5I](https://stacks.math.columbia.edu/tag/0C5I)
* [Stacks Project, Tag 0AXF](https://stacks.math.columbia.edu/tag/0AXF)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- A modification of `Spec(A)` has topological Krull dimension two when `A` has dimension two. -/
private theorem topologicalKrullDim_eq_two_of_isModification {A : Type u} [CommRing A]
    [IsLocalRing A] [IsDomain A] [IsNoetherianRing A] (hdim : ringKrullDim A = 2)
    {S : Scheme.{u}} {p : S ⟶ Spec (.of A)} (hp : IsModification p) :
    topologicalKrullDim S = 2 := by
  have := hp.isProper
  have := hp.source_isIntegral
  rw [IsBirational.topologicalKrullDim_eq_of_isClosedMap hp.isBirational p.isClosedMap]
  exact (PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim A).trans hdim

/-- **`H¹(𝒪) = 0` along normalized point blowups of a regular surface over `Spec(A)`.** Let `S`
be a normal modification of `Spec(A)`, `A` a Noetherian normal local Nagata domain of dimension
two, whose closed points have regular local rings, and with `H¹(S, 𝒪_S) = 0`. Every scheme in a
sequence of normalized blowups of `S` at closed points has the same two properties. At each step
the centre is a closed point with a regular local ring, two-dimensional because the stage is a
modification of `Spec(A)`; the blowup is normal with regular local rings over the centre and an
isomorphism elsewhere, so its normalization is an isomorphism, and `H¹(𝒪) = 0` survives. -/
theorem isRegularLocalRing_and_isZero_of_normalizedBlowUpSeq_of_isModification (A : Type u)
    [CommRing A] [IsLocalRing A] [IsNormalDomain A] (hNagata : IsNagataRing A)
    (hdim : ringKrullDim A = 2) {S : Scheme.{u}} [IsNormal S] (p : S ⟶ Spec (.of A))
    (hp : IsModification p)
    (hregS : ∀ s : S, IsClosed ({s} : Set S) → IsRegularLocalRing (S.presheaf.stalk s))
    (hHS : IsZero (structureSheafH1 S)) {W : Scheme.{u}} {g : W ⟶ S}
    (hseq : NormalizedBlowUpSeq S W g) :
    (∀ w : W, IsClosed ({w} : Set W) → IsRegularLocalRing (W.presheaf.stalk w)) ∧
      IsZero (structureSheafH1 W) := by
  have : IsNoetherianRing A := hNagata.1
  have : IsIntegral S := hp.source_isIntegral
  have : IsProper p := hp.isProper
  have : IsLocallyNoetherian (Spec (.of A)) := isLocallyNoetherian_Spec.mpr inferInstance
  have : IsLocallyNoetherian S := LocallyOfFiniteType.isLocallyNoetherian p
  have hS : IsNagataScheme S := isNagataScheme_of_isNagataRing p hNagata
  have hdimS := topologicalKrullDim_eq_two_of_isModification hdim hp
  induction hseq with
  | refl => exact ⟨hregS, hHS⟩
  | @blowUp X f prev hX x hx ih =>
    obtain ⟨hreg, hH⟩ := ih
    obtain ⟨-, hLN, hN, -⟩ := prev.properties hS
    obtain ⟨hmod, -⟩ := prev.isModification hS hdimS
    have : IsIntegral X := hmod.source_isIntegral
    have hd2 := ringKrullDim_stalk_eq_two_of_isModification A hdim (f ≫ p) (hmod.comp hp) x hx
    have := hreg x hx
    set M := Scheme.IdealSheafData.vanishingIdeal (⟨{x}, hx⟩ : Closeds X)
    obtain ⟨hregB, hBN⟩ := isRegularLocalRing_stalk_blowUp_and_isNormal x hx hd2
    let ν := Scheme.normalization (blowUp M)
      (Stacks.Blowup.finite_irreducibleComponents_blowUp M hX)
    have hν : IsIso ν := Scheme.isIso_normalization_of_isNormal _ _
    refine ⟨fun w hw => ?_, ?_⟩
    · have hνw : IsClosed ({ν w} : Set (blowUp M)) := by
        simpa using ν.isClosedMap _ hw
      have hregν : IsRegularLocalRing ((blowUp M).presheaf.stalk (ν w)) := by
        by_cases hy : blowUpToBase M (ν w) = x
        · exact hregB _ hy
        · have := isIso_stalkMap_blowUpToBase_of_ne x hx (ν w) hy
          have hcl : IsClosed ({blowUpToBase M (ν w)} : Set X) := by
            simpa using (blowUpToBase M).isClosedMap _ hνw
          have := hreg _ hcl
          exact IsRegularLocalRing.of_ringEquiv
            (asIso ((blowUpToBase M).stalkMap (ν w))).commRingCatIsoToRingEquiv
      exact IsRegularLocalRing.of_ringEquiv (asIso (ν.stalkMap w)).commRingCatIsoToRingEquiv
    · exact isZero_structureSheafH1_of_isIso (inv ν)
        (isZero_rightDerived_evaluation_one_blowUp_pointIdeal x hx hd2 hH)

/-- **A resolution with `H¹(X, 𝒪_X) = 0` makes the base a rational singularity** (the
discussion of [Stacks, Section 0AXE] invoked in the proof of [Stacks, Tag 0EA2]). Let `A` be a
Noetherian normal local Nagata domain of dimension two and `f : X ⟶ Spec(A)` a resolution of
singularities with `H¹(X, 𝒪_X) = 0`. For a normal modification `f' : X' ⟶ Spec(A)` the rational
map `X ⇢ X'` over `Spec(A)` which is `f'⁻¹ ∘ f` over the punctured spectrum is resolved by a
sequence of normalized blowups `W ⟶ X` at closed points ([Stacks, Tag 0C5I]); `H¹(W, 𝒪_W) = 0`
by `isRegularLocalRing_and_isZero_of_normalizedBlowUpSeq_of_isModification`, and the morphism
`W ⟶ X'` is a modification of the normal scheme `X'`, so `H¹(X', 𝒪_{X'})` injects into
`H¹(W, 𝒪_W)` ([Stacks, Tag 0AXF]). -/
theorem definesRationalSingularity_of_isResolution_of_isZero_structureSheafH1 (A : Type u)
    [CommRing A] [IsLocalRing A] [IsNormalDomain A] (hNagata : IsNagataRing A)
    (hdim : ringKrullDim A = 2) {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) (hf : IsResolution f)
    (hH : IsZero (structureSheafH1 X)) : DefinesRationalSingularity A := by
  have : IsNoetherianRing A := hNagata.1
  intro X' hX' f' hf'
  have : IsIntegral X := hf.1.source_isIntegral
  have : IsIntegral X' := hf'.source_isIntegral
  have : IsProper f := hf.1.isProper
  have : IsProper f' := hf'.isProper
  have : IsNormal X := isNormal_of_isRegular X hf.2
  have : IsLocallyNoetherian (Spec (.of A)) := isLocallyNoetherian_Spec.mpr inferInstance
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : IsNoetherian X := AlgebraicGeometry.IsNoetherian.mk
  have hNX : IsNagataScheme X := isNagataScheme_of_isNagataRing f hNagata
  have hdimSpec : topologicalKrullDim (Spec (.of A)) = 2 :=
    (PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim A).trans hdim
  have hdimX := topologicalKrullDim_eq_two_of_isModification hdim hf.1
  let V := VanishingSituation.ofModification A hdim f hf.1
  let V' := VanishingSituation.ofModification A hdim f' hf'
  let U : (Spec (.of A)).Opens := V.puncturedSpectrumOpen
  have : IsIso (f ∣_ U) := V.isIso_morphismRestrict_puncturedSpectrumOpen
  have : IsIso (f' ∣_ U) := V'.isIso_morphismRestrict_puncturedSpectrumOpen
  let : X.Over (Spec (.of A)) := ⟨f⟩
  let : X'.Over (Spec (.of A)) := ⟨f'⟩
  have : IsProper (X' ↘ Spec (.of A)) := hf'.isProper
  have hne : ((f ⁻¹ᵁ U : X.Opens) : Set X).Nonempty := by
    obtain ⟨y, hy⟩ := exists_ne_of_topologicalKrullDim_eq_two hdimSpec
      (IsLocalRing.closedPoint A)
    obtain ⟨x, hx⟩ := surjective_of_isProper_of_isBirational f hf.1.isBirational y
    refine ⟨x, ?_⟩
    change f x ∈ ({IsLocalRing.closedPoint A}ᶜ : Set (Spec (.of A)))
    rw [hx]
    exact hy
  let φ : X.PartialMap X' :=
    { domain := f ⁻¹ᵁ U
      dense_domain := (f ⁻¹ᵁ U).isOpen.dense hne
      hom := (f ∣_ U) ≫ inv (f' ∣_ U) ≫ (f' ⁻¹ᵁ U).ι }
  have : φ.IsOver (Spec (.of A)) := by
    change Scheme.Hom.IsOver φ.hom (Spec (.of A))
    rw [Scheme.Hom.isOver_iff]
    change ((f ∣_ U) ≫ inv (f' ∣_ U) ≫ (f' ⁻¹ᵁ U).ι) ≫ f' = (f ⁻¹ᵁ U).ι ≫ f
    rw [Category.assoc, Category.assoc, ← morphismRestrict_ι, IsIso.inv_hom_id_assoc,
      morphismRestrict_ι]
  obtain ⟨Z, g, h, hchain, hover, -⟩ :=
    Stacks.ResolutionOfSurfaces.exists_normalizedBlowUpChain_resolving_partialMap
      (S := Spec (.of A)) hNX hdimX φ
  change h ≫ f' = g ≫ f at hover
  obtain ⟨W, gW, hpc, e, he⟩ := factorsAsNormalizedPointBlowups_of_normalizedBlowUpChain hchain
  have hseq := normalizedBlowUpSeq_of_normalizedPointBlowupChain hpc
  have hW := (isRegularLocalRing_and_isZero_of_normalizedBlowUpSeq_of_isModification A hNagata
    hdim f hf.1 (fun s _ => hf.2.isRegularLocalRing_stalk s) hH hseq).2
  obtain ⟨hgW, -⟩ := hseq.isModification hNX hdimX
  have hcomp : (e.inv ≫ h) ≫ f' = gW ≫ f := by
    rw [Category.assoc, hover, ← he, Category.assoc, Iso.inv_hom_id_assoc]
  have hmod : IsModification (e.inv ≫ h) :=
    SeparableGoUp.isModification_of_comp hf' (hcomp ▸ hgW.comp hf.1)
  have hc : IsIso (e.inv ≫ h).c := hmod.isIso_c_of_isNormal_target
  have : Subsingleton (structureSheafH1 W) := ModuleCat.isZero_iff_subsingleton.mp hW
  have : Subsingleton ((forget₂ (ModuleCat.{u} (W.ringCatSheaf.obj.obj (op ⊤)))
      AddCommGrpCat.{u}).obj (structureSheafH1 W)) := this
  have hsub := (leraySmulEdge_injective (e.inv ≫ h) hc).subsingleton
  exact (isZeroFirstStructureSheafCohomology_iff_isZero_rightDerived X').2
    (ModuleCat.isZero_iff_subsingleton.mpr hsub)

end AlgebraicGeometry

end
