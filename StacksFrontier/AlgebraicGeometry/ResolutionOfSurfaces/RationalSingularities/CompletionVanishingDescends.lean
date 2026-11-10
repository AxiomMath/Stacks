module

public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalSingularities.CohomologyModelBridge
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalSingularities.CompletionDefinesRationalSingularity
public import StacksFrontier.Topology.Sheaves.Cohomology.Leray.LowDegreeSequence
public import StacksFrontier.Topology.Sheaves.Cohomology.AbelianFilteredColimits.NativeCohomologyAndColimits
public import StacksFrontier.CategoryTheory.Sites.GlobalSections.CohomologyAtTheTerminalObject
public import StacksFrontier.AlgebraicGeometry.FlatBaseChangeCohomology.AffinePositiveDegree
public import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.StrictTransformOpenImmersion
public import StacksFrontier.AlgebraicGeometry.Morphisms.Dominant.ModificationGlobalSections
public import StacksFrontier.AlgebraicGeometry.NormalizationBaseChangeBirational.Basic
public import StacksFrontier.AlgebraicGeometry.Surfaces.BlowUpNormality

/-!
# Vanishing of `H¹(𝒪)` descends from a modification over `A` to one over `A^`

Let `A` be a two-dimensional Noetherian normal local domain whose completion `A^` is a normal
domain. Given a normal modification `X ⟶ Spec(A)` with `H¹(X, 𝒪_X) = 0` and a normal
modification `Y ⟶ Spec(A^)` dominated by `Z = X ×_{Spec(A)} Spec(A^)`, also `H¹(Y, 𝒪_Y) = 0`.
This is the statement `AlgebraicGeometry.CompletionVanishingDescends`, a step of the proof of
[Stacks, Tag 0BG7], clause (1).

## Main results

* `AlgebraicGeometry.isZeroFirstStructureSheafCohomology_of_isIso_c`: the injective half of the
  first conclusion of [Stacks, Tag 0AXF], for any morphism with `g_*𝒪_Z = 𝒪_Y`.
* `AlgebraicGeometry.isZeroFirstStructureSheafCohomology_of_isPullback`: flat base change,
  [Stacks, Tag 02KH], for the vanishing of `H¹(𝒪)` over affine bases.
* `AlgebraicGeometry.isIso_c_of_isBirational_of_isNormal`: `g_*𝒪_Z = 𝒪_Y` for a proper birational
  morphism of integral schemes with normal target, [Stacks, Tag 0AY8].
* `AlgebraicGeometry.strictTransformOpenImmersion_of_isModification`: [Stacks, Tag 081S] at a
  modification of the spectrum of a two-dimensional Noetherian normal local domain.
* `AlgebraicGeometry.completionVanishingDescends`: `CompletionVanishingDescends` holds.

## Implementation notes

The base change `Z` is not known to be normal, `A` being Nagata rather than excellent, which is
why the full Leray sequence of `AlgebraicGeometry.LerayFirstCohomologyExact` is not used: only
the injectivity of the edge map `H¹(Y, g_*𝒪_Z) ⟶ H¹(Z, 𝒪_Z)` is needed, and it holds for any
continuous map. What is needed of `Z` is that it be integral, so that `Z ⟶ Y` is proper and
birational onto the normal `Y`; this comes from the scheme-theoretic density of the inverse image
of the punctured spectrum, which flat base change preserves.

## References

* [Stacks Project, Tag 0BG7](https://stacks.math.columbia.edu/tag/0BG7)
* [Stacks Project, Tag 0AXF](https://stacks.math.columbia.edu/tag/0AXF)
* [Stacks Project, Tag 02KH](https://stacks.math.columbia.edu/tag/02KH)
* [Stacks Project, Tag 0AY8](https://stacks.math.columbia.edu/tag/0AY8)
* [Stacks Project, Tag 081S](https://stacks.math.columbia.edu/tag/081S)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace IsLocalRing

universe u

namespace AlgebraicGeometry

open Stacks.Cohomology.LerayLowDegree (abelianCohomology abelianPushforward abelianEdgeMap
  abelianEdgeMap_injective abelianSheafHasSheafify)
open Stacks.Cohomology.AbelianColimit (abSections H'functor nonempty_H'functor_iso_rightDerived)

attribute [local instance] abelianSheafHasSheafify

/-- The abelian sheaf underlying the structure sheaf of a scheme. -/
abbrev structureAbelianSheaf (X : Scheme.{u}) :
    Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} :=
  (sheafCompose (Opens.grothendieckTopology X)
    (forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat)).obj X.sheaf

/-- `H¹(X, 𝒪_X) = 0` in the `Sheaf.H` spelling is the vanishing of first right-derived global
sections of the abelian structure sheaf, in which the Leray edge maps are stated. -/
theorem isZeroFirstStructureSheafCohomology_iff_subsingleton_abelianCohomology
    (X : Scheme.{u}) :
    IsZeroFirstStructureSheafCohomology X ↔
      Subsingleton ((abelianCohomology.{u, u} X ⊤ 1).obj (structureAbelianSheaf X)) := by
  let : EnoughInjectives (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) :=
    IsGrothendieckAbelian.enoughInjectives
  let : HasExt.{u} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) :=
    hasExt_of_enoughInjectives _
  refine (Stacks.Cohomology.TerminalCohomology.subsingleton_H_iff_subsingleton_H'_top
    (structureAbelianSheaf X) 1).trans ?_
  let e := ((nonempty_H'functor_iso_rightDerived (X := (X : Type u)) ⊤ 1).some).app
    (structureAbelianSheaf X)
  exact ⟨fun h => @Equiv.subsingleton _ _ e.symm.addCommGroupIsoToAddEquiv.toEquiv h,
    fun h => @Equiv.subsingleton _ _ e.addCommGroupIsoToAddEquiv.toEquiv h⟩

/-- The comparison map `𝒪_Y ⟶ g_*𝒪_Z` of a morphism of schemes, as a morphism of abelian
sheaves. -/
def structureAbelianSheafPushforwardMap {Z Y : Scheme.{u}} (g : Z ⟶ Y) :
    structureAbelianSheaf Y ⟶ (abelianPushforward.{u, u} g.base).obj (structureAbelianSheaf Z) :=
  ⟨Functor.whiskerRight g.c (forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat)⟩

/-- If the comparison map `𝒪_Y ⟶ g_*𝒪_Z` of `g : Z ⟶ Y` is an isomorphism of sheaves of rings,
then it is an isomorphism of abelian sheaves. -/
instance isIso_structureAbelianSheafPushforwardMap {Z Y : Scheme.{u}} (g : Z ⟶ Y)
    [IsIso g.c] : IsIso (structureAbelianSheafPushforwardMap g) := by
  have : IsIso ((sheafToPresheaf _ _).map (structureAbelianSheafPushforwardMap g)) := by
    change IsIso (Functor.whiskerRight g.c _)
    infer_instance
  exact isIso_of_reflects_iso _ (sheafToPresheaf _ _)

/-- **The first conclusion of [Stacks, Tag 0AXF], its injective half, under `g_*𝒪_Z = 𝒪_Y`.**
If the comparison map `𝒪_Y ⟶ g_*𝒪_Z` is an isomorphism then the Leray edge map embeds
`H¹(Y, 𝒪_Y)` into `H¹(Z, 𝒪_Z)`, so the vanishing of the latter forces that of the former. -/
theorem isZeroFirstStructureSheafCohomology_of_isIso_c {Z Y : Scheme.{u}} (g : Z ⟶ Y)
    [IsIso g.c] (hZ : IsZeroFirstStructureSheafCohomology Z) :
    IsZeroFirstStructureSheafCohomology Y := by
  rw [isZeroFirstStructureSheafCohomology_iff_subsingleton_abelianCohomology] at hZ ⊢
  let e := (abelianCohomology.{u, u} Y ⊤ 1).mapIso
    (asIso (structureAbelianSheafPushforwardMap g))
  exact ((abelianEdgeMap_injective.{u, u} g.base (structureAbelianSheaf Z)).comp
    e.addCommGroupIsoToAddEquiv.injective).subsingleton

/-- **Flat base change for the vanishing of `H¹(𝒪)` over affine bases**, [Stacks, Tag 02KH]
part (2) at the structure sheaf in degree one: if `S' ⟶ S` is a flat morphism of affine schemes
and `X ⟶ S` is quasi-compact and separated, then `H¹(X, 𝒪_X) = 0` forces
`H¹(X ×_S S', 𝒪) = 0`, the latter being `H¹(X, 𝒪_X) ⊗_{Γ(S)} Γ(S')`. -/
theorem isZeroFirstStructureSheafCohomology_of_isPullback {X Z S S' : Scheme.{u}}
    {f : X ⟶ S} {b : Z ⟶ S'} {g : S' ⟶ S} {c : Z ⟶ X} (H : IsPullback c b f g)
    [IsAffine S] [IsAffine S'] [Flat g] [QuasiCompact f] [IsSeparated f]
    (hX : IsZeroFirstStructureSheafCohomology X) :
    IsZeroFirstStructureSheafCohomology Z := by
  rw [isZeroFirstStructureSheafCohomology_iff_isZero_rightDerived] at hX ⊢
  obtain ⟨e⟩ := nonempty_cohomologyBaseChangeIso H (SheafOfModules.unit X.ringCatSheaf) 1
  have : (Stacks.AlgebraicGeometry.SectionsBaseChange.baseExtendScalars g).IsLeftAdjoint :=
    (ModuleCat.extendRestrictScalarsAdj _).isLeftAdjoint
  have h₂ := ((Stacks.AlgebraicGeometry.SectionsBaseChange.baseExtendScalars g).map_isZero
    ((Stacks.AlgebraicGeometry.SectionsBaseChange.baseRestrictScalars f).map_isZero hX)).of_iso
    e.symm
  have h₃ : IsZero (((SheafOfModules.evaluation Z.ringCatSheaf (op (⊤ : Z.Opens))).rightDerived
      1).obj ((Scheme.Modules.pullback c).obj (SheafOfModules.unit X.ringCatSheaf))) := by
    rw [ModuleCat.isZero_iff_subsingleton] at h₂ ⊢
    exact h₂
  exact h₃.of_iso (((SheafOfModules.evaluation Z.ringCatSheaf (op (⊤ : Z.Opens))).rightDerived
    1).mapIso (Scheme.Modules.pullbackUnitIso c)).symm


/-! ### Proper birational morphisms onto a normal integral scheme -/

/-- **[Stacks, Tag 0AY8] for a proper birational morphism of integral schemes with normal
target**: the comparison map `𝒪_Y ⟶ g_*𝒪_Z` is an isomorphism. -/
theorem isIso_c_of_isBirational_of_isNormal {Z Y : Scheme.{u}} [IsIntegral Z] [IsIntegral Y]
    [IsNormal Y] (g : Z ⟶ Y) [IsProper g] (hg : IsBirational g) : IsIso g.c := by
  have hfib : IsIso (g.fiberToSpecResidueField (genericPoint Y)) :=
    isIso_fiberToSpecResidueField_genericPoint_of_isBirational g hg
  have hfibΓ : IsIso (g.fiberToSpecResidueField (genericPoint Y)).appTop := by
    have hc0 : IsIso (g.fiberToSpecResidueField (genericPoint Y)).c :=
      PresheafedSpace.c_isIso_of_iso (g.fiberToSpecResidueField (genericPoint Y)).toPshHom
    exact NatIso.isIso_app_of_isIso _ (Opposite.op ⊤)
  have hΓ : IsIso ((Scheme.ΓSpecIso (Y.residueField (genericPoint Y))).inv ≫
      (g.fiberToSpecResidueField (genericPoint Y)).appTop) := inferInstance
  have hgen : ∀ x : Z, x ∈ genericPoints Z → g x = genericPoint Y := by
    intro x hx
    have hmem := hg.bijOn.mapsTo hx
    rwa [genericPoints_eq_singleton, Set.mem_singleton_iff] at hmem
  exact Stacks.SteinFactorization.isIso_c_of_isNormal g hgen hΓ

/-! ### Modifications of the spectrum of a two-dimensional normal local ring -/

/-- **A modification of the spectrum of a two-dimensional Noetherian normal local domain is an
isomorphism over the punctured spectrum.** -/
theorem isIso_morphismRestrict_puncturedSpectrum_of_isModification (B : Type u) [CommRing B]
    [IsLocalRing B] [IsNoetherianRing B] [IsNormalDomain B] (hdim : ringKrullDim B = 2)
    {Y : Scheme.{u}} (q : Y ⟶ Spec (.of B)) (hq : IsModification q) :
    IsIso (q ∣_ Stacks.puncturedSpectrum B) := by
  have : IsProper q := hq.isProper
  have := finite_irreducibleComponents_fiber_closedPoint B q
  exact VanishingSituation.isIso_morphismRestrict_puncturedSpectrumOpen
    { A := B
      dimension_two := hdim
      X := Y
      f := q
      modification := hq
      numberOfComponents := Nat.card {Z : Set (q.fiber (IsLocalRing.closedPoint B)) //
        Z ∈ irreducibleComponents (q.fiber (IsLocalRing.closedPoint B))}
      components := (Finite.equivFin _).symm }

/-- **[Stacks, Tag 081S] at a modification of the spectrum of a two-dimensional Noetherian normal
local domain**: the strict transform of the modification along some admissible blowup of the
punctured spectrum is an open subscheme of that blowup. -/
theorem strictTransformOpenImmersion_of_isModification (B : Type u) [CommRing B]
    [IsLocalRing B] [IsNoetherianRing B] [IsNormalDomain B] (hdim : ringKrullDim B = 2)
    {Y : Scheme.{u}} (q : Y ⟶ Spec (.of B)) (hq : IsModification q) :
    StrictTransformOpenImmersion q (Stacks.puncturedSpectrum B) := by
  have := isIso_morphismRestrict_puncturedSpectrum_of_isModification B hdim q hq
  have : IsProper q := hq.isProper
  have : NoetherianSpace (Spec (.of B)) := inferInstanceAs (NoetherianSpace (PrimeSpectrum B))
  exact strictTransformOpenImmersion_of_isIso_morphismRestrict q (Stacks.puncturedSpectrum B)
    (NoetherianSpace.isCompact _)

/-! ### The punctured spectrum of the completion -/

/-- **The punctured spectrum of `A^` is the inverse image of the punctured spectrum of `A`**: a
prime of `A^` lies over the maximal ideal of `A` exactly when it contains `𝔪A^`, which is the
maximal ideal of `A^`. -/
theorem specMapAdicCompletion_preimage_puncturedSpectrum (A : Type u) [CommRing A]
    [IsLocalRing A] [IsNoetherianRing A] :
    specMapAdicCompletion A ⁻¹ᵁ Stacks.puncturedSpectrum A =
      Stacks.puncturedSpectrum (AdicCompletion (maximalIdeal A) A) := by
  ext p
  change specMapAdicCompletion A p ≠ closedPoint A ↔ p ≠ closedPoint _
  refine not_congr ⟨fun h => PrimeSpectrum.ext ?_, fun h => ?_⟩
  · have hcomap : Ideal.comap (algebraMap A (AdicCompletion (maximalIdeal A) A)) p.asIdeal =
        maximalIdeal A := congrArg PrimeSpectrum.asIdeal h
    refine le_antisymm (IsLocalRing.le_maximalIdeal p.isPrime.ne_top) ?_
    change maximalIdeal (AdicCompletion (maximalIdeal A) A) ≤ p.asIdeal
    rw [AdicCompletion.maximalIdeal_eq_map]
    exact Ideal.map_le_iff_le_comap.mpr hcomap.ge
  · rw [h]
    exact PrimeSpectrum.ext
      (IsLocalRing.maximalIdeal_comap (algebraMap A (AdicCompletion (maximalIdeal A) A)))

/-! ### Flat base change followed by the Leray injection -/

/-- **`AlgebraicGeometry.CompletionVanishingDescends` holds for a two-dimensional Noetherian
normal local domain with normal completion.** This is the step of the proof of
[Stacks, Tag 0BG7], clause (1), that combines flat base change, [Stacks, Tag 02KH], with the
injectivity in the first conclusion of [Stacks, Tag 0AXF]: for a normal modification
`X ⟶ Spec(A)` with `H¹(X, 𝒪_X) = 0` and a normal modification `Y ⟶ Spec(A^)` dominated by
`X ×_{Spec(A)} Spec(A^)`, also `H¹(Y, 𝒪_Y) = 0`. -/
theorem completionVanishingDescends (A : Type u) [CommRing A] [IsLocalRing A]
    [IsNoetherianRing A] [IsNormalDomain A] [IsNormalDomain (AdicCompletion (maximalIdeal A) A)]
    (hdim : ringKrullDim A = 2) : CompletionVanishingDescends.{u} A := by
  intro X Y Z f q c b g hXn hf hYn hq H hgq hX
  have hdim' : ringKrullDim (AdicCompletion (maximalIdeal A) A) = 2 :=
    IsLocalRing.ringKrullDim_adicCompletion_maximalIdeal.trans hdim
  have : IsProper f := hf.isProper
  have : IsProper q := hq.isProper
  have : IsIntegral X := hf.source_isIntegral
  have : IsIntegral Y := hq.source_isIntegral
  have : IsNormal Y := hYn
  have : Module.FaithfullyFlat A (AdicCompletion (maximalIdeal A) A) :=
    AdicCompletion.faithfullyFlat_of_le_ringJacobson _
      (by rw [← Ideal.jacobson_bot]; exact IsLocalRing.maximalIdeal_le_jacobson ⊥)
  have : Flat (specMapAdicCompletion A) :=
    Flat.SpecMap_iff.mpr (RingHom.flat_algebraMap_iff.mpr inferInstance)
  have hZ : IsZeroFirstStructureSheafCohomology Z :=
    isZeroFirstStructureSheafCohomology_of_isPullback H hX
  have : IsProper b := MorphismProperty.of_isPullback H inferInstance
  have : Flat c := MorphismProperty.of_isPullback H.flip inferInstance
  have hfU := isIso_morphismRestrict_puncturedSpectrum_of_isModification A hdim f hf
  have hqU := isIso_morphismRestrict_puncturedSpectrum_of_isModification _ hdim' q hq
  have hpre := specMapAdicCompletion_preimage_puncturedSpectrum A
  set U := Stacks.puncturedSpectrum A with hUdef
  set U' := Stacks.puncturedSpectrum (AdicCompletion (maximalIdeal A) A) with hU'def
  set W := f ⁻¹ᵁ U with hWdef
  have hVeq : b ⁻¹ᵁ U' = c ⁻¹ᵁ W := by
    rw [← hpre, ← Scheme.Hom.comp_preimage, ← H.w, Scheme.Hom.comp_preimage]
  have hbU : IsIso (b ∣_ U') := by
    have h := Scheme.Hom.isPullback_resLE H (US := U) (UT := U') (UX := W) hpre.ge le_rfl
      (UY := b ⁻¹ᵁ U') (by rw [hVeq, inf_idem])
    have hfU' : IsIso (f.resLE U W le_rfl) := by
      rw [Scheme.Hom.resLE_eq_morphismRestrict]
      exact hfU
    simpa only [Scheme.Hom.resLE_eq_morphismRestrict] using
      (MorphismProperty.isomorphisms Scheme).of_isPullback h hfU'
  have hUne : (U : Set (Spec (.of A))).Nonempty :=
    nonempty_coe_puncturedSpectrum A (by rw [hdim]; exact one_le_two)
  have hU'ne : (U' : Set (Spec (.of (AdicCompletion (maximalIdeal A) A)))).Nonempty :=
    nonempty_coe_puncturedSpectrum _ (by rw [hdim']; exact one_le_two)
  have : Nonempty U'.toScheme := hU'ne.to_subtype
  have : IsIntegral U'.toScheme := isIntegral_of_isOpenImmersion U'.ι
  have : Nonempty (b ⁻¹ᵁ U').toScheme := ⟨(inv (b ∣_ U')) (Classical.arbitrary _)⟩
  have hVint : IsIntegral (b ⁻¹ᵁ U').toScheme := isIntegral_of_isOpenImmersion (b ∣_ U')
  have hVint' : IsIntegral (c ⁻¹ᵁ W).toScheme := hVeq ▸ hVint
  have : Nonempty U.toScheme := hUne.to_subtype
  have hWne : (W : Set X).Nonempty := ⟨((inv (f ∣_ U)) (Classical.arbitrary _)).1,
    ((inv (f ∣_ U)) (Classical.arbitrary _)).2⟩
  have : IsDominant W.ι := AlgebraicGeometry.Opens.isDominant_ι (W.isOpen.dense hWne)
  have : IsSchemeTheoreticallyDominant W.ι := .of_isDominant W.ι
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have hsq := isPullback_morphismRestrict c W
  have : QuasiCompact (c ⁻¹ᵁ W).ι := MorphismProperty.of_isPullback hsq inferInstance
  have : IsSchemeTheoreticallyDominant (c ⁻¹ᵁ W).ι := .of_isPullback hsq
  have : IsReduced Z := IsSchemeTheoreticallyDominant.isReduced (c ⁻¹ᵁ W).ι
  have hirr : IsIrreducible (Set.range (c ⁻¹ᵁ W).ι.base) := by
    rw [← Set.image_univ]
    exact (IrreducibleSpace.isIrreducible_univ _).image _ (c ⁻¹ᵁ W).ι.continuous.continuousOn
  have : IrreducibleSpace Z := (irreducibleSpace_def Z).mpr (by
    change IsIrreducible (Set.univ : Set Z)
    rw [← (inferInstance : IsDominant (c ⁻¹ᵁ W).ι).denseRange.closure_range]
    exact hirr.closure)
  have : IsIntegral Z := isIntegral_of_irreducibleSpace_of_isReduced Z
  have hgenU' : genericPoint (Spec (.of (AdicCompletion (maximalIdeal A) A))) ∈ U' := by
    change _ ∈ (U' : Set (Spec (.of (AdicCompletion (maximalIdeal A) A))))
    rw [(genericPoint_spec _).mem_open_set_iff U'.isOpen, Set.univ_inter]
    exact hU'ne
  have hbbir : IsBirational b := by
    refine isBirational_of_isIso_morphismRestrict b U' hbU (fun z hz => ?_) (fun y hy => ?_)
    · rw [genericPoints_eq_singleton, Set.mem_singleton_iff] at hz
      subst hz
      change genericPoint Z ∈ ((b ⁻¹ᵁ U' : Z.Opens) : Set Z)
      rw [(genericPoint_spec Z).mem_open_set_iff (b ⁻¹ᵁ U').isOpen, Set.univ_inter]
      obtain ⟨v⟩ := (inferInstance : Nonempty (b ⁻¹ᵁ U').toScheme)
      exact ⟨v.1, v.2⟩
    · rw [genericPoints_eq_singleton, Set.mem_singleton_iff] at hy
      subst hy
      exact hgenU'
  have hqgen : q (genericPoint Y) = genericPoint _ := IsBirational.genericPoint_eq q hq.isBirational
  have hgbir : IsBirational g := by
    refine isBirational_of_comp_of_isBirational g q (hgq ▸ hbbir) hq.isBirational ?_
    rw [genericPoints_eq_singleton, genericPoints_eq_singleton]
    ext y
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    refine ⟨fun hy => ?_, fun hy => hy ▸ hqgen⟩
    have hmem : ∀ y, q y = genericPoint _ → y ∈ q ⁻¹ᵁ U' := fun y hy => by
      change q y ∈ U'
      rwa [hy]
    have hy' := hmem y hy
    have hη := hmem _ hqgen
    have hz : (q ∣_ U') (⟨y, hy'⟩ : (q ⁻¹ᵁ U').toScheme) =
        (q ∣_ U') (⟨genericPoint Y, hη⟩ : (q ⁻¹ᵁ U').toScheme) :=
      Subtype.ext ((morphismRestrict_base_coe q U' ⟨y, hy'⟩).trans
        (hy.trans (hqgen.symm.trans
          (morphismRestrict_base_coe q U' ⟨genericPoint Y, hη⟩).symm)))
    exact congrArg Subtype.val ((q ∣_ U').homeomorph.injective hz)
  have : IsProper (g ≫ q) := hgq ▸ inferInstance
  have : IsProper g := IsProper.of_comp g q
  have : IsIso g.c := isIso_c_of_isBirational_of_isNormal g hgbir
  exact isZeroFirstStructureSheafCohomology_of_isIso_c g hZ

end AlgebraicGeometry
