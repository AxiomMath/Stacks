module

public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import StacksFrontier.AlgebraicGeometry.RelativeAmple.ProjIso
public import StacksFrontier.AlgebraicGeometry.RelativeAmple.RestrictBase
public import StacksFrontier.AlgebraicGeometry.SectionRingProjImmersion.Basic
public import StacksFrontier.AlgebraicGeometry.RelativeVeryAmple.TensorPower
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Stacks Tag 01VJ: relative ampleness through the relative `Proj`

Let `f : X ⟶ S` be a quasi-compact morphism of schemes and `L` an invertible `𝒪_X`-module.
[Stacks, Tag 01VJ] says that the following are equivalent:

1. `L` is ample relative to `f` ([Stacks, Tag 01VH]);
2. there is an open covering `S = ⋃ V_i` with `L|_{f⁻¹V_i}` ample relative to `f⁻¹V_i ⟶ V_i`;
3. there is an affine open covering `S = ⋃ V_i` with every `L|_{f⁻¹V_i}` ample;
4. there are a quasi-coherent graded `𝒪_S`-algebra `𝒜` and a graded map
   `ψ : f^*𝒜 ⟶ ⨁_{d ≥ 0} L^{⊗ d}` with `U(ψ) = X` and `r_{L, ψ} : X ⟶ Proj_S(𝒜)` an open
   immersion;
5. `f` is quasi-separated and (4) holds for `𝒜 = f_*(⨁_{d ≥ 0} L^{⊗ d})` and `ψ` the adjunction
   map;
6. as (4), with `r_{L, ψ}` only an immersion.

The equivalence of (1), (2) and (3) is proved in
`StacksFrontier/AlgebraicGeometry/RelativeAmple/LocalOnBase.lean` and
`StacksFrontier/AlgebraicGeometry/RelativeAmple/RestrictBase.lean`; this file proves the clauses
about the relative `Proj` and assembles the whole equivalence.

## Main results

* `Stacks.RelativeAmple.isAmple_of_isImmersion_glued`: on a quasi-compact scheme `T`, if a graded
  map `ψ : A → Γ_*(T, L)` has `U(ψ) = T` and the morphism `r_{L, ψ} : T ⟶ Proj A` of
  [Stacks, Tag 01NK] is an immersion, then `L` is ample.
* `Stacks.RelativeAmple.globalMorphism_iff`: a property of morphisms local on the target holds
  for `r_{L, ψ} : U(ψ) ⟶ Proj_S(𝒜)` if and only if it holds for the morphism of
  [Stacks, Tag 01NK] induced over every affine open of `S`.
* `Stacks.RelativeAmple.IsRelativelyAmple.isOpenImmersion_globalMorphism`: **(1) implies the
  open-immersion assertion of (5).**
* `Stacks.RelativeAmple.isRelativelyAmple_of_isImmersion_globalMorphism`: **(6) implies (1)**,
  and `isRelativelyAmple_of_isOpenImmersion_globalMorphism`, **(4) implies (1)**.
* `Stacks.RelativeAmple.isRelativelyAmple_tfae`: **[Stacks, Tag 01VJ]**, all six clauses.

## The route for (6) implies (1)

Over an affine open `V` of `S` the morphism `r_{L, ψ}` is, up to isomorphisms on both sides, the
morphism `f⁻¹V ⟶ Proj 𝒜(V)` of [Stacks, Tag 01NK] for the graded map
`𝒜(V) → Γ_*(f⁻¹V, L|_{f⁻¹V})` induced by `ψ` (clause (3) of [Stacks, Tag 01O9]); so it is an
immersion as soon as `r_{L, ψ}` is. An immersion `j` factors as a closed immersion into the open
`W` of `Proj 𝒜(V)` in which its image is closed. Through each point of the image there is a basic
open `D₊(a) ⊆ W` with `a` homogeneous of positive degree; it is affine, so its preimage under the
closed immersion is affine, and that preimage is the nonvanishing open of the section `ψ(a)` of a
positive tensor power of `L` (clause (1) of [Stacks, Tag 01NK]). This is ampleness of
`L|_{f⁻¹V}` in the form of [Stacks, Tag 01PS], `f⁻¹V` being quasi-compact because `f` is.

This replaces the source's appeal to [Stacks, Tags 01Q2, 01PT, 01MW, 01PU] by the affineness of
the basic opens of `Proj` and of closed subschemes of affine schemes; no twisting sheaf is used.
The same argument with an open immersion is clause (2) implies clause (1) of
[Stacks, Tag 01Q3] (`Stacks.AmpleCharacterization.isAmple_of_isOpenImmersion_projHomOfCovers`).

## The route for (1) implies (5)

Quasi-separatedness and `U(ψ) = X` are
`Stacks.RelativeAmple.IsRelativelyAmple.quasiSeparated` and
`Stacks.RelativeAmple.coveringOpen_directImagePowerMap`. Being an open immersion is local on
the target, and over an affine open `V` of `S` the morphism is the morphism of
[Stacks, Tag 01NK] for the graded ring `𝒜(V)`, which is isomorphic to `Γ_*(f⁻¹V, L|_{f⁻¹V})`
(`Stacks.RelativeAmple.sectionRingEquiv`). For the full section ring that morphism is the
morphism of [Stacks, Tag 01PZ], an open immersion by [Stacks, Tag 01Q1] because `L|_{f⁻¹V}` is
ample.

## Implementation notes

The graded map `ψ` of clauses (4) and (6) is the datum
`Stacks.AlgebraicGeometry.RelativeProjInvertibleMorphism.GradedPowerMap` of [Stacks, Tag 01O8]:
an invertible module together with multiplicative components `𝒜_d ⟶ f_*(L^{⊗ d})`, the adjoint
form of the components of `f^*𝒜 ⟶ ⨁_{d ≥ 0} L^{⊗ d}`. Its module is only required to be
isomorphic to `L`. The morphism `r_{L, ψ}` is
`Stacks.AlgebraicGeometry.RelativeProjInvertibleMorphism.GradedPowerMap.globalMorphism`, with
source `U(ψ)`; the clauses state `U(ψ) = X` and the property of that morphism.

The open coverings of clauses (2) and (3) are written pointwise: every point of `S` lies in a
member.

## References

* [Stacks Project, Tag 01VJ](https://stacks.math.columbia.edu/tag/01VJ)
* [Stacks Project, Tag 01VH](https://stacks.math.columbia.edu/tag/01VH)
* [Stacks Project, Tag 01NK](https://stacks.math.columbia.edu/tag/01NK)
* [Stacks Project, Tag 01O8](https://stacks.math.columbia.edu/tag/01O8)
* [Stacks Project, Tag 01O9](https://stacks.math.columbia.edu/tag/01O9)
* [Stacks Project, Tag 01PS](https://stacks.math.columbia.edu/tag/01PS)
* [Stacks Project, Tag 01PZ](https://stacks.math.columbia.edu/tag/01PZ)
* [Stacks Project, Tag 01Q1](https://stacks.math.columbia.edu/tag/01Q1)
* [Stacks Project, Tag 01Q3](https://stacks.math.columbia.edu/tag/01Q3)
* [EGA II, Proposition 4.6.3]
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProjInvertibleMorphism
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.ProjChartFullGraded (GradedSections)
open Stacks.TensorPowers (natTensorPow)
open Stacks.NonvanishingOpen (nonvanishingOpen)

universe u

namespace Stacks.RelativeAmple

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory
  Stacks.SectionRingGeometric.schemePreadditive
  Stacks.SectionRingGeometric.schemeTensorRightAdditive

section Absolute

variable {σ : Type u} {R : Type u} [CommRing R] [SetLike σ R] [AddSubgroupClass σ R]
  {𝒜 : ℕ → σ} [GradedRing 𝒜] {T : Scheme.{u}} {L : T.Modules}
  [Stacks.Ample.IsInvertibleModule T L]

/-- **A graded map whose morphism to `Proj` is an immersion makes `L` ample.** Let `T` be a
quasi-compact scheme, `L` an invertible `𝒪_T`-module and `ψ : A → Γ_*(T, L)` a graded map from a
graded ring, in the form of [Stacks, Tag 01NK]. If `U(ψ) = T` and `r_{L, ψ} : U(ψ) ⟶ Proj A` is an
immersion, then `L` is ample.

Through the image of a point there is a basic open `D₊(a)`, `a` homogeneous of positive degree,
inside the open in which the image is closed; its preimage is affine, being a closed subscheme of
an affine scheme, and is the nonvanishing open of `ψ(a)`. -/
@[ega "II 4.5.2" "partial"]
theorem isAmple_of_isImmersion_glued [CompactSpace T] (ψ : GradedSections 𝒜 L)
    (hU : ψ.coveringOpen = ⊤) [IsImmersion ψ.glued] : Stacks.Ample.IsAmple T L := by
  refine (Stacks.NonvanishingOpen.isAmple_iff_nonvanishingOpen T L).mpr ⟨‹_›, fun x => ?_⟩
  set j := ψ.glued
  let x' : ψ.coveringOpen.toScheme := ⟨x, hU ▸ trivial⟩
  have hx : j.base x' ∈ j.coborderRange := by
    have h1 : (j.liftCoborder ≫ j.coborderRange.ι).base x' = j.base x' := by
      rw [j.liftCoborder_ι]
    exact h1 ▸ (j.liftCoborder.base x').2
  obtain ⟨d, g, hd, hg, hmem, hle⟩ :=
    Stacks.AlgebraicGeometry.ProjBasis.exists_pos_basicOpen_le 𝒜 j.coborderRange hx
  have hD : IsAffineOpen (Proj.basicOpen 𝒜 g) := Proj.isAffineOpen_basicOpen 𝒜 g hg hd
  have hD' : IsAffineOpen (j.coborderRange.ι ⁻¹ᵁ Proj.basicOpen 𝒜 g) :=
    hD.preimage_of_isOpenImmersion _ (by rwa [Scheme.Opens.opensRange_ι])
  have hpre : j ⁻¹ᵁ Proj.basicOpen 𝒜 g
      = j.liftCoborder ⁻¹ᵁ (j.coborderRange.ι ⁻¹ᵁ Proj.basicOpen 𝒜 g) := by
    rw [← Scheme.Hom.comp_preimage, j.liftCoborder_ι]
  have haff : IsAffineOpen (j ⁻¹ᵁ Proj.basicOpen 𝒜 g) := by
    rw [hpre]; exact hD'.preimage _
  have himg := ψ.image_preimage_basicOpen_glued hg hd
  have haff' : IsAffineOpen (nonvanishingOpen T (natTensorPow L d) (ψ.toFun d ⟨g, hg⟩)) := by
    rw [← himg]; exact haff.image_of_isOpenImmersion _
  have hxmem : x ∈ nonvanishingOpen T (natTensorPow L d) (ψ.toFun d ⟨g, hg⟩) := by
    rw [← himg]; exact ⟨x', hmem, rfl⟩
  have heq : (natTensorPow L d : T.Modules) = Stacks.Ample.tensorPowModule T L (d : ℤ) :=
    Stacks.SectionRingGeometric.natTensorPow_eq_tensorPow
      (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf T) L d
  let e : (natTensorPow L d : T.Modules) ≅ Stacks.Ample.tensorPowModule T L (d : ℤ) :=
    eqToIso (C := T.Modules) heq
  have hopen : nonvanishingOpen T (Stacks.Ample.tensorPowModule T L (d : ℤ))
        (e.hom.app ⊤ (ψ.toFun d ⟨g, hg⟩))
      = nonvanishingOpen T (natTensorPow L d) (ψ.toFun d ⟨g, hg⟩) :=
    Opens.ext (Stacks.Ample.nonvanishingLocus_congr e _)
  exact ⟨d, hd, e.hom.app ⊤ (ψ.toFun d ⟨g, hg⟩), hopen ▸ hxmem, hopen ▸ haff'⟩

end Absolute

section OpenImmersion

open Stacks.AlgebraicGeometry.ProjChartGradedRingFunctoriality

/-- **For `M` ample, the morphism of [Stacks, Tag 01NK] for the full section ring
`Γ_*(Y, M)` is an open immersion.** It is the morphism of [Stacks, Tag 01PZ]
(`Stacks.SectionRingGluedComparison.ι_comp_projHomOfIsAmple_eq_glued`), an open immersion by
[Stacks, Tag 01Q1]. -/
theorem isOpenImmersion_glued_canonicalSections {Y : Scheme.{u}} (M : Y.Modules)
    [Stacks.Ample.IsInvertibleModule Y M] (hM : Stacks.Ample.IsAmple Y M) :
    IsOpenImmersion (Stacks.SectionRingGluedComparison.canonicalSections M).glued := by
  rw [← Stacks.SectionRingGluedComparison.ι_comp_projHomOfIsAmple_eq_glued M hM]
  have : IsIso (Stacks.SectionRingGluedComparison.canonicalSections M).coveringOpen.ι := by
    rw [Stacks.SectionRingGluedComparison.coveringOpen_canonicalSections_eq_top M hM]
    exact (inferInstance : IsIso (Scheme.topIso Y).hom)
  have := Stacks.SectionRingProjImmersion.isOpenImmersion_projHomOfIsAmple M hM
  infer_instance

variable {A B σ τ : Type u} [CommRing A] [CommRing B]
  [SetLike σ A] [AddSubgroupClass σ A] [SetLike τ B] [AddSubgroupClass τ B]
  {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ]
  {T : Scheme.{u}} {L : T.Modules} [Stacks.Ample.IsInvertibleModule T L]

/-- **Pulling a datum back along a graded ring isomorphism preserves open immersions**: the
pulled-back morphism is the original one followed by `Proj` of the isomorphism, on the same
covering open. -/
theorem isOpenImmersion_glued_comap (φ : 𝒜 →+*ᵍ ℬ) (φ' : ℬ →+*ᵍ 𝒜)
    (h₁ : φ'.comp φ = GradedRingHom.id 𝒜) (h₂ : φ.comp φ' = GradedRingHom.id ℬ)
    (ψ : GradedSections ℬ L) [IsOpenImmersion ψ.glued] : IsOpenImmersion (comap φ ψ).glued := by
  rw [← homOfLE_glued_comp_projMap φ (Stacks.GradedRegrading.irrelevant_le_map_of_comp_eq_id h₂) ψ]
  have : IsIso (T.homOfLE (coveringOpen_le φ ψ)) :=
    (inferInstance : IsIso (T.isoOfEq
      (Stacks.SectionRingGluedComparison.coveringOpen_comap_of_comp_eq_id φ φ' h₂ ψ)).hom)
  have := AlgebraicGeometry.Proj.isIso_map
    (Stacks.GradedRegrading.irrelevant_le_map_of_comp_eq_id h₂)
    (Stacks.GradedRegrading.irrelevant_le_map_of_comp_eq_id h₁) h₁ h₂
  infer_instance

end OpenImmersion

section Restriction

variable {S : Scheme.{u}} {A : SheafGradedAlgebra.{u} S} {T : Scheme.{u}} {f : T ⟶ S}
  (P : GradedPowerMap A f) (rp : RelativeProjData A)

/-- The preimages of the affine opens of the base cover a relative `Proj`. -/
theorem iSup_preimage_toBase_affineOpens :
    (⨆ V : S.affineOpens, rp.toBase ⁻¹ᵁ (V : S.Opens)) = ⊤ := by
  rw [← Scheme.Hom.preimage_iSup, AlgebraicGeometry.iSup_affineOpens_eq_top S,
    Scheme.Hom.preimage_top]

/-- **Over an affine open `V` of the base, `r_{L, ψ}` is the morphism of [Stacks, Tag 01NK]
induced over `V`**, up to an isomorphism of sources and the chart
`Proj 𝒜(V) ≅ π⁻¹(V)` of [Stacks, Tag 01NQ]. This is clause (3) of [Stacks, Tag 01O9]. -/
theorem exists_globalMorphism_restrict_eq (V : S.affineOpens) :
    ∃ (e₁ : (P.globalMorphism rp ⁻¹ᵁ (rp.toBase ⁻¹ᵁ V.1)).toScheme
          ≅ ((P.affineDatum V.1).coveringOpen).toScheme)
      (e₂ : AlgebraicGeometry.Proj (A.grading V.1) ≅ (rp.toBase ⁻¹ᵁ V.1).toScheme),
      P.globalMorphism rp ∣_ (rp.toBase ⁻¹ᵁ V.1)
        = e₁.hom ≫ (P.affineDatum V.1).glued ≫ e₂.hom := by
  have hRW : P.globalMorphism rp ⁻¹ᵁ (rp.toBase ⁻¹ᵁ V.1) = P.toBase ⁻¹ᵁ V.1 := by
    rw [← Scheme.Hom.comp_preimage, P.globalMorphism_comp_toBase rp]
  let c : AlgebraicGeometry.Proj (A.grading V.1) ≅ (rp.toBase ⁻¹ᵁ V.1).toScheme :=
    (rp.chart_isPullback V.1 V.2).isoPullback ≪≫ pullbackRestrictIsoRestrict rp.toBase V.1
  have hc : c.hom ≫ (rp.toBase ⁻¹ᵁ V.1).ι = rp.chart V.1 V.2 := by
    simp only [c, Iso.trans_hom, Category.assoc, pullbackRestrictIsoRestrict_hom_ι,
      IsPullback.isoPullback_hom_fst]
  refine ⟨(Scheme.isoOfEq _ hRW) ≪≫ P.toBaseIso V.1 V.2 ≪≫ (P.datumIso V.1).symm, c, ?_⟩
  rw [← cancel_mono (rp.toBase ⁻¹ᵁ V.1).ι, morphismRestrict_ι]
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, hc]
  change _ = (Scheme.isoOfEq _ hRW).hom ≫ P.piece rp V
  rw [← P.ι_globalMorphism rp V, ← Category.assoc, Scheme.isoOfEq_hom_ι]

/-- **Properties local on the target are checked on the induced morphisms of
[Stacks, Tag 01NK].** A property of morphisms of schemes that is local on the target holds for
`r_{L, ψ} : U(ψ) ⟶ Proj_S(𝒜)` if and only if it holds for the morphism `U(ψ_V) ⟶ Proj 𝒜(V)` of the
graded map induced by `ψ` over every affine open `V` of `S`. -/
theorem globalMorphism_iff (Q : MorphismProperty Scheme.{u}) [IsZariskiLocalAtTarget Q] :
    Q (P.globalMorphism rp) ↔ ∀ V : S.affineOpens, Q (P.affineDatum V.1).glued := by
  rw [IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := Q) _ (iSup_preimage_toBase_affineOpens rp)]
  refine forall_congr' fun V => ?_
  obtain ⟨e₁, e₂, h⟩ := exists_globalMorphism_restrict_eq P rp V
  rw [h, MorphismProperty.cancel_left_of_respectsIso Q,
    MorphismProperty.cancel_right_of_respectsIso Q]

end Restriction

section Main

variable {X S : Scheme.{u}} {f : X ⟶ S} {L : X.Modules} [Stacks.Ample.IsInvertibleModule X L]

/-- **[Stacks, Tag 01VJ], (1) implies the open-immersion assertion of (5).** For `L` ample relative
to `f`, with `𝒜 = f_*(⨁_{d ≥ 0} L^{⊗ d})` and `ψ` the adjunction map, the morphism
`r_{L, ψ} : U(ψ) ⟶ Proj_S(𝒜)` is an open immersion. -/
@[stacks 01VJ "(1) implies (5), the assertion that r_{L,psi} is an open immersion"]
theorem IsRelativelyAmple.isOpenImmersion_globalMorphism (hL : IsRelativelyAmple f L) :
    haveI := hL.quasiCompact
    haveI := hL.quasiSeparated
    IsOpenImmersion
      ((directImagePowerMap f L).globalMorphism (relativeProj (directImageAlgebra f L))) := by
  have := hL.quasiCompact
  have := hL.quasiSeparated
  refine (globalMorphism_iff _ _ @IsOpenImmersion).mpr fun V => ?_
  have := isOpenImmersion_glued_canonicalSections _ (isAmple_restrictedModule hL V.2)
  have h := isOpenImmersion_glued_comap _ _ (sectionGradedHomInv_comp f L V.1)
    (sectionGradedHom_comp f L V.1)
    (Stacks.SectionRingGluedComparison.canonicalSections (restrictedModule f L V.1))
  exact (affineDatum_eq_comap f L V.1) ▸ h

/-- **The canonical morphism `r : X ⟶ Proj_S(f_*(⨁_{d ≥ 0} L^{⊗ d}))` is an open immersion**
for `L` ample relative to `f`: `IsRelativelyAmple.isOpenImmersion_globalMorphism` read on `X`
through `U(ψ) = X`. -/
theorem isOpenImmersion_relativeAmpleProjHom (hL : IsRelativelyAmple f L) :
    haveI := hL.quasiCompact
    haveI := hL.quasiSeparated
    IsOpenImmersion (relativeAmpleProjHom f L hL) := by
  have := hL.quasiCompact
  have := hL.quasiSeparated
  have := hL.isOpenImmersion_globalMorphism
  rw [relativeAmpleProjHom]
  infer_instance

/-- **[Stacks, Tag 01VJ], (6) implies (1).** Let `f` be quasi-compact, `𝒜` a quasi-coherent
graded `𝒪_S`-algebra and `ψ : f^*𝒜 ⟶ ⨁_{d ≥ 0} L^{⊗ d}` a graded map with `U(ψ) = X` such that
`r_{L, ψ} : X ⟶ Proj_S(𝒜)` is an immersion. Then `L` is ample relative to `f`.

Over an affine open `V` of `S` the morphism is an immersion `f⁻¹V ⟶ Proj 𝒜(V)` by
`globalMorphism_iff`, and `isAmple_of_isImmersion_glued` gives ampleness of `L|_{f⁻¹V}`. -/
@[stacks 01VJ "(6) implies (1)"]
theorem isRelativelyAmple_of_isImmersion_globalMorphism (hf : QuasiCompact f)
    {A : SheafGradedAlgebra.{u} S} (P : GradedPowerMap A f) (e : P.L ≅ L)
    (hU : P.coveringOpen = ⊤) (hP : IsImmersion (P.globalMorphism (relativeProj A))) :
    IsRelativelyAmple f L := by
  refine ⟨hf, fun V hV => ?_⟩
  have himm := (globalMorphism_iff P (relativeProj A) @IsImmersion).mp hP ⟨V, hV⟩
  have hle : f ⁻¹ᵁ V ≤ P.coveringOpenOver V := by
    have := P.inf_le_coveringOpenOver hV
    rwa [hU, top_inf_eq] at this
  have hcov : (P.affineDatum V).coveringOpen = ⊤ := by
    rw [P.coveringOpen_affineDatum V]
    exact eq_top_iff.mpr fun y _ => hle y.2
  have : CompactSpace (f ⁻¹ᵁ V).toScheme :=
    Stacks.RelativeAmpleComposition.compactSpace_preimage_of_isCompact f V hV.isCompact
  have hA := isAmple_of_isImmersion_glued (P.affineDatum V) hcov
  exact (Stacks.RelativeVeryAmple.isAmple_congr _ _
    ((Scheme.Modules.pullback (f ⁻¹ᵁ V).ι).mapIso e)).mp hA

/-- **[Stacks, Tag 01VJ], (4) implies (1)**: an open immersion is an immersion. -/
@[stacks 01VJ "(4) implies (1)"]
theorem isRelativelyAmple_of_isOpenImmersion_globalMorphism (hf : QuasiCompact f)
    {A : SheafGradedAlgebra.{u} S} (P : GradedPowerMap A f) (e : P.L ≅ L)
    (hU : P.coveringOpen = ⊤) (hP : IsOpenImmersion (P.globalMorphism (relativeProj A))) :
    IsRelativelyAmple f L :=
  isRelativelyAmple_of_isImmersion_globalMorphism hf P e hU inferInstance

/-- **[Stacks, Tag 01VJ].** For a quasi-compact morphism of schemes `f : X ⟶ S` and an invertible
`𝒪_X`-module `L` the following are equivalent:

1. `L` is ample relative to `f`;
2. every point of `S` has an open neighbourhood `V` with `L|_{f⁻¹V}` ample relative to
   `f ∣_ V : f⁻¹V ⟶ V`;
3. every point of `S` has an affine open neighbourhood `V` with `L|_{f⁻¹V}` ample;
4. there are a quasi-coherent graded `𝒪_S`-algebra `𝒜` and a graded map
   `ψ : f^*𝒜 ⟶ ⨁_{d ≥ 0} L^{⊗ d}` with `U(ψ) = X` and `r_{L, ψ} : U(ψ) ⟶ Proj_S(𝒜)` an open
   immersion;
5. `f` is quasi-separated and, for `𝒜 = f_*(⨁_{d ≥ 0} L^{⊗ d})` and `ψ` the adjunction map,
   `U(ψ) = X` and `r_{L, ψ}` is an open immersion;
6. as (4), with `r_{L, ψ}` an immersion. -/
@[stacks 01VJ]
theorem isRelativelyAmple_tfae (f : X ⟶ S) (L : X.Modules)
    [Stacks.Ample.IsInvertibleModule X L] [QuasiCompact f] :
    List.TFAE [
      IsRelativelyAmple f L,
      ∀ x : S, ∃ V : S.Opens, x ∈ V ∧
        IsRelativelyAmple (f ∣_ V) (Stacks.AmpleLocallyClosed.pullbackModule (f ⁻¹ᵁ V).ι L),
      ∀ x : S, ∃ V : S.Opens, IsAffineOpen V ∧ x ∈ V ∧
        Stacks.Ample.IsAmple (f ⁻¹ᵁ V).toScheme
          (Stacks.AmpleLocallyClosed.pullbackModule (f ⁻¹ᵁ V).ι L),
      ∃ (A : SheafGradedAlgebra.{u} S) (P : GradedPowerMap A f), Nonempty (P.L ≅ L) ∧
        P.coveringOpen = ⊤ ∧ IsOpenImmersion (P.globalMorphism (relativeProj A)),
      ∃ h : QuasiSeparated f,
        haveI := h
        (directImagePowerMap f L).coveringOpen = ⊤ ∧ IsOpenImmersion
          ((directImagePowerMap f L).globalMorphism (relativeProj (directImageAlgebra f L))),
      ∃ (A : SheafGradedAlgebra.{u} S) (P : GradedPowerMap A f), Nonempty (P.L ≅ L) ∧
        P.coveringOpen = ⊤ ∧ IsImmersion (P.globalMorphism (relativeProj A))] := by
  tfae_have 1 ↔ 2 :=
    Stacks.RelativeAmpleRestrictBase.isRelativelyAmple_iff_exists_isRelativelyAmple_cover f L
      inferInstance
  tfae_have 1 ↔ 3 :=
    Stacks.RelativeAmpleLocalOnBase.isRelativelyAmple_iff_exists_affine_isAmple_cover f L
      inferInstance
  tfae_have 1 → 5 := fun hL =>
    haveI := hL.quasiSeparated
    ⟨hL.quasiSeparated, coveringOpen_directImagePowerMap hL, hL.isOpenImmersion_globalMorphism⟩
  tfae_have 5 → 4 := fun ⟨h, hU, hP⟩ =>
    haveI := h
    ⟨directImageAlgebra f L, directImagePowerMap f L, ⟨Iso.refl _⟩, hU, hP⟩
  tfae_have 4 → 6 := fun ⟨A, P, e, hU, hP⟩ => ⟨A, P, e, hU, inferInstance⟩
  tfae_have 6 → 1 := fun ⟨_, P, ⟨e⟩, hU, hP⟩ =>
    isRelativelyAmple_of_isImmersion_globalMorphism inferInstance P e hU hP
  tfae_finish

end Main

end Stacks.RelativeAmple

end
