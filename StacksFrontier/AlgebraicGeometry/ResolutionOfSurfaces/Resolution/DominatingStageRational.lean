module

public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalSingularities.RationalStalk
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Resolution.Basic
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Resolution.LipmanEquivalencePort
public import StacksFrontier.AlgebraicGeometry.Properties.RegularCharacterization
public import StacksFrontier.AlgebraicGeometry.NormalizationBaseChangeBirational.Basic
import all StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalSingularities.NormalizedBlowUpRationalSingularity

/-!
# The singular points of a normal modification dominating a resolution are rational

Let `A` be a two-dimensional Noetherian local normal domain, `f : X ⟶ Spec(A)` a resolution of
singularities, and `Z ⟶ Spec(A)` a normal modification which factors through `f`. Step 4 of the
proof of [Stacks, Tag 0BGM] shows that the local ring of `Z` at each singular point `z`
defines a rational singularity. Let `x ∈ X` be the image of `z`. The local ring `𝒪_{X, x}` is
regular, so it defines a rational singularity ([Stacks, Tag 0B4Q]). Then
[Stacks, Tag 0BG0] applies to `𝒪_{X, x} ⟶ 𝒪_{Z, z}`.

Here [Stacks, Tag 0BG0] is applied to the base change `W = Z ×_X Spec 𝒪_{X, x}`. This is a
normal modification of `Spec 𝒪_{X, x}`, and it has a closed point with local ring `𝒪_{Z, z}`.

## Main results

* `AlgebraicGeometry.definesRationalSingularity_of_iso`: being a rational singularity transports
  along an isomorphism of rings.
* `AlgebraicGeometry.definesRationalSingularity_stalk_of_mem_singularLocus`: Step 4 of
  [Stacks, Tag 0BGM].

## Implementation notes

[Stacks, Tag 0B4Q] enters as the hypothesis `h0B4Q`; it is
`AlgebraicGeometry.definesRationalSingularity_of_isRegularLocalRing_of_isNagataRing`.
[Stacks, Tag 0BG0] in its local-ring form is
`AlgebraicGeometry.definesRationalSingularity_stalk_of_isModification`.

## References

* [Stacks Project, Tag 0BGM](https://stacks.math.columbia.edu/tag/0BGM)
* [Stacks Project, Tag 0B4Q](https://stacks.math.columbia.edu/tag/0B4Q)
* [Stacks Project, Tag 0BG0](https://stacks.math.columbia.edu/tag/0BG0)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- **Being a rational singularity transports along an isomorphism of rings.** A modification of
`Spec R` composed with the isomorphism `Spec R ≅ Spec S` is a modification of `Spec S`. -/
theorem definesRationalSingularity_of_iso {R S : CommRingCat.{u}} [IsDomain R] [IsDomain S]
    (e : R ≅ S) (h : DefinesRationalSingularity S) : DefinesRationalSingularity R := by
  intro Y _ p hp
  have := hp.isProper
  exact h Y (p ≫ Spec.map e.inv) ⟨hp.isBirational.comp (isBirational_of_iso (asIso
    (Spec.map e.inv))), inferInstance, hp.source_isIntegral⟩

/-- A scheme whose local rings are, through a morphism, local rings of a normal scheme is
normal. -/
theorem isNormal_of_isIso_stalkMap {W Z : Scheme.{u}} [IsNormal Z] (q : W ⟶ Z)
    (hq : ∀ w, IsIso (q.stalkMap w)) : IsNormal W := by
  rw [isNormal_iff_stalk_normal]
  intro w
  have := hq w
  have := IsNormal.stalk_normal (X := Z) (q w)
  let e : (Z.presheaf.stalk (q w)) ≃+* (W.presheaf.stalk w) :=
    (asIso (q.stalkMap w)).commRingCatIsoToRingEquiv
  let : IsDomain (W.presheaf.stalk w) := Function.Injective.isDomain e.symm e.symm.injective
  exact ⟨inferInstance, IsIntegrallyClosed.of_equiv e⟩

/-- A closed birational morphism of integral schemes to the spectrum of a Noetherian domain
preserves dimension. -/
private theorem topologicalKrullDim_eq_ringKrullDim_of_isBirational {R : CommRingCat.{u}}
    [IsDomain R] [IsNoetherianRing R] {X : Scheme.{u}} [IsIntegral X] (f : X ⟶ Spec R)
    [IsProper f] (hf : IsBirational f) : topologicalKrullDim X = ringKrullDim R := by
  have : IsLocallyNoetherian (Spec R) := isLocallyNoetherian_Spec.mpr inferInstance
  rw [← PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim]
  exact hf.topologicalKrullDim_eq_of_isClosedMap f.isClosedMap

/-- **Step 4 of [Stacks, Tag 0BGM].** Let `A` be a two-dimensional Noetherian local normal domain,
`f : X ⟶ Spec(A)` a resolution of singularities, and `g : Z ⟶ Spec(A)` a modification with `Z`
normal which factors as `h ≫ f`. Then the local ring of `Z` at every singular point defines a
rational singularity.

The hypothesis `h0B4Q` stands for [Stacks, Tag 0B4Q], which the source states for Nagata rings;
it is applied at the local rings of `X`, which are Nagata by `hN`. -/
theorem definesRationalSingularity_stalk_of_mem_singularLocus (A : Type u) [CommRing A]
    [IsNoetherianRing A] [IsLocalRing A] [IsNormalDomain A] (hdim : ringKrullDim A = 2)
    (h0B4Q : ∀ (B : Type u) [CommRing B] [IsDomain B] [IsRegularLocalRing B] [IsNagataRing B],
      ringKrullDim B = 2 → DefinesRationalSingularity B)
    {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) (hf : IsResolution f)
    (hN : ∀ x : X, IsNagataRing (X.presheaf.stalk x))
    {Z : Scheme.{u}} [IsNormal Z] (g : Z ⟶ Spec (.of A)) (h : Z ⟶ X) (hg : IsModification g)
    (hhg : h ≫ f = g) (z : Z) (hz : z ∈ singularLocus Z) :
    DefinesRationalSingularity (Z.presheaf.stalk z) := by
  have : IsIntegral X := hf.1.source_isIntegral
  have : IsIntegral Z := hg.source_isIntegral
  have := hg.isProper
  have := hf.1.isProper
  have : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian g
  have hXnormal : IsNormal X := isNormal_of_isRegular X hf.2
  obtain ⟨-, hXreg⟩ := ((isRegular_tfae X).out 1 2).mp hf.2
  have hdimX : topologicalKrullDim X = 2 :=
    (topologicalKrullDim_eq_ringKrullDim_of_isBirational f hf.1.isBirational).trans hdim
  have hdimZ : topologicalKrullDim Z = 2 :=
    (topologicalKrullDim_eq_ringKrullDim_of_isBirational g hg.isBirational).trans hdim
  have hz2 : ringKrullDim (Z.presheaf.stalk z) = 2 :=
    ringKrullDim_stalk_eq_two_of_mem_singularLocus Z hdimZ.le z hz
  have hzclosed : IsClosed ({z} : Set Z) :=
    isClosed_singleton_of_mem_singularLocus Z hdimZ.le z hz
  set x := h z
  let B := X.presheaf.stalk x
  have : IsRegularLocalRing B := hXreg x
  have : IsNormalDomain B := ⟨inferInstance, IsNormal.stalk_normal x⟩
  have : IsNagataRing B := hN x
  let W := pullback h (X.fromSpecStalk x)
  let q : W ⟶ Z := pullback.fst h (X.fromSpecStalk x)
  let p : W ⟶ Spec B := pullback.snd h (X.fromSpecStalk x)
  have hsq : IsPullback p q (X.fromSpecStalk x) h := (IsPullback.of_hasPullback h _).flip
  have : Flat (X.fromSpecStalk x) := flat_fromSpecStalk X x
  have : Flat q := MorphismProperty.IsStableUnderBaseChange.of_isPullback hsq inferInstance
  have : IsPreimmersion q := MorphismProperty.IsStableUnderBaseChange.of_isPullback hsq
    inferInstance
  have hqstalk : ∀ w, IsIso (q.stalkMap w) := fun w => isIso_stalkMap_of_flat_isPreimmersion q w
  have : IsNormal W := isNormal_of_isIso_stalkMap q hqstalk
  obtain ⟨w, hw, -⟩ := exists_point_pullback_fromSpecStalk_isIso_stalkMap h x z rfl
  have hηmem : h (genericPoint Z) ∈ Set.range (X.fromSpecStalk x) := by
    rw [Scheme.range_fromSpecStalk]
    exact ((genericPoint_spec Z).specializes (Set.mem_univ z)).map h.continuous
  obtain ⟨t, ht⟩ := hηmem
  obtain ⟨wη, hwη, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := h)
    (g := X.fromSpecStalk x) (genericPoint Z) t ht.symm
  have hspec : ∀ w' : W, wη ⤳ w' := by
    intro w'
    refine (IsPreimmersion.isEmbedding q).isInducing.specializes_iff.mp ?_
    rw [hwη]
    exact (genericPoint_spec Z).specializes (Set.mem_univ _)
  have hirr : IrreducibleSpace W := by
    have hcl : closure ({wη} : Set W) = Set.univ :=
      Set.eq_univ_of_forall fun w' => specializes_iff_mem_closure.mp (hspec w')
    have hi := (isIrreducible_singleton (x := wη)).closure
    rw [hcl] at hi
    exact (irreducibleSpace_def W).mpr hi
  have hWint : IsIntegral W := isIntegral_of_irreducibleSpace_of_isReduced W
  have hgenW : genericPoint W = wη :=
    (((genericPoint_spec W).specializes (Set.mem_univ wη)).antisymm (hspec _)).eq
  let T : SemistableReduction.TwoModifications.{u} :=
    { situation := vanishingSituationOfModification A hdim f hf.1
      X' := Z
      g := h
      modification' := by change IsModification (h ≫ f); rw [hhg]; exact hg
      normal := hXnormal }
  have hhbir : IsBirational h := T.isBirational_g
  have hpη : p wη = genericPoint (Spec B) := by
    have h1 : X.fromSpecStalk x (p wη) = genericPoint X := by
      rw [← Scheme.Hom.comp_apply, ← pullback.condition, Scheme.Hom.comp_apply]
      change h (q wη) = _
      rw [hwη, IsBirational.genericPoint_eq h hhbir]
    refine (((genericPoint_spec _).specializes (Set.mem_univ _)).antisymm ?_).eq.symm
    refine (IsPreimmersion.isEmbedding (X.fromSpecStalk x)).isInducing.specializes_iff.mp ?_
    rw [h1, fromSpecStalk_genericPoint]
  have hpbir : IsBirational p := by
    refine ⟨?_, ?_⟩
    · rw [genericPoints_eq_singleton, genericPoints_eq_singleton, hgenW]
      exact Set.bijOn_singleton.mpr hpη
    · intro w' hw'
      rw [genericPoints_eq_singleton, Set.mem_singleton_iff, hgenW] at hw'
      rw [hw']
      have hη : IsIso (h.stalkMap (q wη)) := by
        have := hhbir.isIso_stalkMap (genericPoint Z) (by simp [genericPoints_eq_singleton])
        rwa [← hwη] at this
      have h1 : IsIso ((q ≫ h).stalkMap wη) := by
        rw [Scheme.Hom.stalkMap_comp]
        exact IsIso.comp_isIso' hη (hqstalk wη)
      rw [Scheme.Hom.stalkMap_congr_hom _ _ (pullback.condition : q ≫ h = p ≫ X.fromSpecStalk x),
        Scheme.Hom.stalkMap_comp] at h1
      have : IsIso ((X.fromSpecStalk x).stalkMap (p wη)) :=
        isIso_stalkMap_of_flat_isPreimmersion _ _
      have h2 : IsIso ((X.fromSpecStalk x).stalkMap (p wη) ≫ p.stalkMap wη) :=
        @IsIso.of_isIso_comp_left _ _ _ _ _ _ _ (Iso.isIso_hom _) h1
      exact IsIso.of_isIso_comp_left ((X.fromSpecStalk x).stalkMap (p wη)) _
  have : IsProper h := by
    have : IsProper (h ≫ f) := by rw [hhg]; infer_instance
    exact IsProper.of_comp h f
  have : IsProper p := MorphismProperty.IsStableUnderBaseChange.of_isPullback hsq.flip
    inferInstance
  have hdimW : topologicalKrullDim W = ringKrullDim B :=
    topologicalKrullDim_eq_ringKrullDim_of_isBirational p hpbir
  have hw2 : ringKrullDim (W.presheaf.stalk w) = 2 := by
    rw [← hz2, ← hw]
    exact (ringKrullDim_eq_of_ringEquiv (asIso (q.stalkMap w)).commRingCatIsoToRingEquiv).symm
  have hdimB : ringKrullDim B = 2 := by
    refine le_antisymm ?_ ?_
    · refine le_trans ?_ hdimX.le
      rw [topologicalKrullDim_eq_iSup_krullDimOfRing_stalk]
      exact le_iSup_of_le x le_rfl
    · rw [← hw2, ← hdimW, topologicalKrullDim_eq_iSup_krullDimOfRing_stalk]
      exact le_iSup_of_le w le_rfl
  have hwclosed : IsClosed ({w} : Set W) := by
    rw [← (IsPreimmersion.isEmbedding q).injective.preimage_image {w}, Set.image_singleton, hw]
    exact hzclosed.preimage q.continuous
  have hwη' : w ≠ genericPoint W := by
    intro hwg
    have hzη : z = genericPoint Z := by rw [← hw, hwg, hgenW, hwη]
    have h0 : ringKrullDim (Z.presheaf.stalk z) = 0 := by
      rw [hzη]
      exact ringKrullDim_eq_zero_of_field Z.functionField
    rw [hz2] at h0
    exact absurd h0 (by norm_num)
  have := hqstalk w
  exact definesRationalSingularity_of_iso
    ((Z.presheaf.stalkCongr (.of_eq hw)).symm ≪≫ asIso (q.stalkMap w))
    (definesRationalSingularity_stalk_of_isModification B hdimB (h0B4Q B hdimB) p
      ⟨hpbir, inferInstance, hWint⟩ w hwclosed hwη')

end AlgebraicGeometry

end
