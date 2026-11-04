module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.AffineRigEtaleAlgebraization
public import StacksFrontier.AlgebraicGeometry.FormalSpace.SpectrumFullyFaithful
public import StacksFrontier.AlgebraicGeometry.FormalSpace.SpectrumOfAdicCompletion
public import StacksFrontier.AlgebraicGeometry.FormalSpace.AffineCompletionEssentialSurjectivity
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionMorphismsAffine
public import StacksFrontier.AlgebraicGeometry.Artin.ContractionClosedImmersionChartAdic
public import StacksFrontier.AlgebraicGeometry.Artin.ContractionSolutionCompletion
public import StacksFrontier.AlgebraicGeometry.Artin.ContractionLimitFormalRingHom
public import StacksFrontier.AlgebraicGeometry.FormalSpace.FormalSpectrumCompletedTensorProduct

/-!
# Morphisms from the completion of an affine scheme into a formal spectrum

Let `V` be an affine object of the big fppf site of `S` with Noetherian ring of global sections
`A`, let `I ⊆ A` be an ideal and `Z = V(I)`. In the algebra part of the proof of Stacks 0GI5 a
morphism `x̂ : V_{/Z} ⟶ Spf B` into the formal spectrum of a weakly admissible topological ring
`B` over `S` "determines and is determined by a continuous ring map `B → A^∧`", `A^∧` the
`I`-adic completion of `A`. This file records that dictionary.

The completion `V_{/Z}` is identified with `Spf A^∧` by Stacks 0GBA (2)
(`AlgebraicGeometry.FormalSpace.isIso_completionComparison`) after transporting `V` to the affine
object `Spec A` of the site, and morphisms of formal spectra are continuous ring maps over `S` by
Stacks 0AN0 (`AlgebraicGeometry.FormalSpace.existsUnique_continuousHom_formalSpectrumMap_eq`).

## Main definitions

* `AlgebraicGeometry.Artin.FormalDictionary.completionQuotientSystem`: the quotient system
  presenting `A^∧`, with the `I`-adic topology, as a topological ring over `S`.
* `AlgebraicGeometry.Artin.FormalDictionary.completionIsoFormalSpectrum`: `V_{/Z} ≅ Spf A^∧`.
* `AlgebraicGeometry.Artin.FormalDictionary.continuousHomEquiv`: the dictionary, a bijection
  between continuous ring maps `B → A^∧` over `S` and morphisms `V_{/Z} ⟶ Spf B`.

## Main results

* `FormalDictionary.sectionEquiv_symm_presheafSection_comp_completionIsoFormalSpectrum_hom`: the
  value of `V_{/Z} ≅ Spf A^∧` on a section factoring through a quotient stage.
* `AlgebraicGeometry.Artin.FormalDictionary.completionSheaf_hom_ext_powStage`: morphisms out of
  `V_{/Z}` are determined on the quotient stages `Spec (A ⧸ I^{n+1})`.
* `AlgebraicGeometry.Artin.FormalDictionary.completionSheafRestrict_comp_continuousHomEquiv`: the
  dictionary is natural in `V`.

## References

* [Stacks Project, Tag 0GI5](https://stacks.math.columbia.edu/tag/0GI5)
* [Stacks Project, Tag 0GBA](https://stacks.math.columbia.edu/tag/0GBA)
* [Stacks Project, Tag 0AN0](https://stacks.math.columbia.edu/tag/0AN0)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Artin.FormalDictionary

attribute [local instance] Space.pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- The `I`-adic topology on the `I`-adic completion `AdicCompletion I A`. -/
local instance instTopologicalSpaceAdicCompletion {A : Type u} [CommRing A] (I : Ideal A) :
    TopologicalSpace (AdicCompletion I A) :=
  I.adicModuleTopology (AdicCompletion I A)

variable (V : BigFppfOver B S hS) [IsAffine ((BigFppfOver.toScheme B S hS).obj V)]

/-- The structure morphism `Spec Γ(V) ≅ V ⟶ S` of the spectrum of the ring of global sections of
an affine object `V` of the site. -/
noncomputable abbrev specStructure : Spec (.of Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)) ⟶ S :=
  ((BigFppfOver.toScheme B S hS).obj V).isoSpec.inv ≫ V.hom.hom

/-- The spectrum `Spec Γ(V)` of an affine object `V`, as the object
`AlgebraicGeometry.FormalSpace.affineOver` of the site. -/
noncomputable abbrev affineModel : BigFppfOver B S hS :=
  FormalSpace.affineOver B S hS (Space.contains_spec_globalSections B S hS V) (specStructure V)

/-- The isomorphism `Spec Γ(V) ⟶ V` of objects of the site. -/
noncomputable def affineModelHom : affineModel V ⟶ V :=
  FormalSpace.siteHom B S hS ((BigFppfOver.toScheme B S hS).obj V).isoSpec.inv rfl

/-- The underlying morphism of schemes of `Spec Γ(V) ⟶ V` is the inverse of `V ≅ Spec Γ(V)`. -/
theorem toScheme_map_affineModelHom :
    (BigFppfOver.toScheme B S hS).map (affineModelHom V) =
      ((BigFppfOver.toScheme B S hS).obj V).isoSpec.inv := rfl

/-- The morphism `Spec Γ(V) ⟶ V` of the site is an isomorphism. -/
instance isIso_affineModelHom : IsIso (affineModelHom V) := by
  have : IsIso ((BigFppfOver.toScheme B S hS).map (affineModelHom V)) := by
    rw [toScheme_map_affineModelHom]
    exact ⟨⟨_, Iso.inv_hom_id _, Iso.hom_inv_id _⟩⟩
  exact isIso_of_reflects_iso _ (BigFppfOver.toScheme B S hS)

variable [IsNoetherianRing Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)]
  (I : Ideal Γ((BigFppfOver.toScheme B S hS).obj V, ⊤))

/-- The quotient system presenting the `I`-adic completion `A^∧` of `A = Γ(V)`, with its `I`-adic
topology, as a topological ring over `S`: the structure morphism of `Spec (A^∧ ⧸ J)` is the one
induced by `A → A^∧ ⧸ J` and `Spec A ≅ V ⟶ S`. -/
noncomputable abbrev completionQuotientSystem : FormalSpace.AdicQuotientSystem B S hS I :=
  FormalSpace.adicQuotientSystem B S hS (Space.contains_spec_globalSections B S hS V)
    (specStructure V) I I.fg_of_isNoetherianRing

variable {V I} {Z : Set (Space.points B S hS (yoneda.obj V))}
  (hZI : ∀ x, x ∈ Z ↔ Space.pointsToScheme B S hS V x ∈
    ((BigFppfOver.toScheme B S hS).obj V).zeroLocus
      (I : Set Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)))

omit [IsNoetherianRing Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)] in
include hZI in
/-- Along `Spec A ≅ V` the zero locus of `I` in `V` pulls back to the zero locus of `I` in
`Spec A`. -/
theorem preimage_eq_zeroLocusPoints :
    Space.pointsMap B S hS _ (yoneda.map (affineModelHom V)) ⁻¹' Z =
      FormalSpace.zeroLocusPoints B S hS (Space.contains_spec_globalSections B S hS V)
        (specStructure V) I := by
  rw [← FormalSpace.supportedPoints_zeroLocus]
  ext x
  show Space.pointsMap B S hS _ (yoneda.map (affineModelHom V)) x ∈ Z ↔
    Space.pointsToScheme B S hS (affineModel V) x ∈ PrimeSpectrum.zeroLocus _
  rw [hZI, Space.pointsToScheme_pointsMap_yoneda, toScheme_map_affineModelHom,
    ← Scheme.isoSpec_inv_preimage_zeroLocus]
  rfl

/-- The comparison `Spf A^∧ ⟶ Spec A_{/V(I)} ⟶ V_{/Z}` of Stacks 0GBA (2). -/
noncomputable def completionIsoFormalSpectrumInv :
    FormalSpace.formalSpectrum (completionQuotientSystem V I) ⟶
      Space.completionSheaf B S hS (yoneda.obj V) Z :=
  FormalSpace.completionComparison B S hS (Space.contains_spec_globalSections B S hS V)
      (specStructure V) I (completionQuotientSystem V I)
      (FormalSpace.quotientSystemCompatible_adicQuotientSystem B S hS
        (Space.contains_spec_globalSections B S hS V) (specStructure V) I
        I.fg_of_isNoetherianRing) ≫
    Space.completionSheafRestrict B S hS (yoneda.map (affineModelHom V))
      (FormalSpace.zeroLocusPoints B S hS (Space.contains_spec_globalSections B S hS V)
        (specStructure V) I) Z (preimage_eq_zeroLocusPoints hZI).symm.subset

include hZI in
/-- The comparison `Spf A^∧ ⟶ V_{/Z}` is an isomorphism. -/
theorem isIso_completionIsoFormalSpectrumInv : IsIso (completionIsoFormalSpectrumInv hZI) := by
  have := FormalSpace.isIso_completionSheafMap_of_isIso (yoneda.map (affineModelHom V)) Z
  have := FormalSpace.isIso_completionComparison_adicQuotientSystem B S hS
    (Space.contains_spec_globalSections B S hS V) (specStructure V) I I.fg_of_isNoetherianRing
  rw [completionIsoFormalSpectrumInv, Space.completionSheafRestrict_eq_eqToHom_comp B S hS _ _ _ _
    (preimage_eq_zeroLocusPoints hZI).symm]
  infer_instance

/-- **Stacks 0GBA (2) for an affine object of the site**: `V_{/V(I)} ≅ Spf A^∧`. -/
noncomputable def completionIsoFormalSpectrum :
    Space.completionSheaf B S hS (yoneda.obj V) Z ≅
      FormalSpace.formalSpectrum (completionQuotientSystem V I) :=
  haveI := isIso_completionIsoFormalSpectrumInv hZI
  (asIso (completionIsoFormalSpectrumInv hZI)).symm

/-- The inverse of `V_{/Z} ≅ Spf A^∧` is the comparison `completionIsoFormalSpectrumInv`. -/
theorem completionIsoFormalSpectrum_inv :
    (completionIsoFormalSpectrum hZI).inv = completionIsoFormalSpectrumInv hZI := rfl

variable {Bt : Type u} [CommRing Bt] [TopologicalSpace Bt] [IsTopologicalRing Bt]
  [IsLinearTopology Bt Bt] (hB : TopologicalRing.IsWeaklyAdmissible Bt)
  {DB : FormalSpace.QuotientSystem B S hS Bt}

/-- **The dictionary of the proof of Stacks 0GI5**: a morphism `V_{/Z} ⟶ Spf B`, `Z = V(I)`,
"determines and is determined by" a continuous ring map `B → A^∧` over `S`. The bijection sends
`φ` to `V_{/Z} ≅ Spf A^∧ ⟶ Spf B`, the second map being `Spf φ`. -/
noncomputable def continuousHomEquiv :
    FormalSpace.ContinuousHom DB (completionQuotientSystem V I) ≃
      (Space.completionSheaf B S hS (yoneda.obj V) Z ⟶ FormalSpace.formalSpectrum DB) :=
  Equiv.ofBijective (fun φ => (completionIsoFormalSpectrum hZI).hom ≫
      FormalSpace.formalSpectrumMap hB φ) (by
    obtain ⟨hTR, hLT, -, -, hAw⟩ :=
      FormalSpace.adicCompletion_isAdic_of_fg I I.fg_of_isNoetherianRing
    refine ⟨fun φ ψ h => ?_, fun x => ?_⟩
    · have h' : FormalSpace.formalSpectrumMap hB φ = FormalSpace.formalSpectrumMap hB ψ := by
        simpa using congrArg ((completionIsoFormalSpectrum hZI).inv ≫ ·) h
      obtain ⟨g, -, hg⟩ := FormalSpace.existsUnique_continuousHom_formalSpectrumMap_eq hB hAw
        (FormalSpace.formalSpectrumMap hB φ)
      exact (hg φ rfl).trans (hg ψ h'.symm).symm
    · obtain ⟨g, hg, -⟩ := FormalSpace.existsUnique_continuousHom_formalSpectrumMap_eq hB hAw
        ((completionIsoFormalSpectrum hZI).inv ≫ x)
      exact ⟨g, by simp only [hg, Iso.hom_inv_id_assoc]⟩)

/-- The dictionary sends `φ` to `V_{/Z} ≅ Spf A^∧ ⟶ Spf B`, the second map being `Spf φ`. -/
theorem continuousHomEquiv_apply (φ : FormalSpace.ContinuousHom DB (completionQuotientSystem V I)) :
    continuousHomEquiv hZI hB φ =
      (completionIsoFormalSpectrum hZI).hom ≫ FormalSpace.formalSpectrumMap hB φ := rfl

variable (V I) in
/-- The quotient stage `Spec (A^∧ ⧸ I ^ (n + 1) A^∧)` of the completion. -/
noncomputable def powStage (n : ℕ) : BigFppfOver B S hS :=
  (BigAffineFppf.inclusion B S hS).obj ((completionQuotientSystem V I).stage
    (FormalSpace.adicCompletionPowStageIdeal I I.fg_of_isNoetherianRing n))

variable (V I) in
/-- The morphism `Spec (A^∧ ⧸ I ^ (n + 1) A^∧) ⟶ Spec A`. -/
noncomputable def powStageToAffine (n : ℕ) : powStage V I n ⟶ affineModel V :=
  FormalSpace.quotientStageToAffine B S hS (Space.contains_spec_globalSections B S hS V)
      (specStructure V) I (completionQuotientSystem V I)
      (FormalSpace.quotientSystemCompatible_adicQuotientSystem B S hS
        (Space.contains_spec_globalSections B S hS V) (specStructure V) I
        I.fg_of_isNoetherianRing)
      (FormalSpace.adicCompletionPowStageIdeal I I.fg_of_isNoetherianRing n)

variable (V I) in
/-- The morphism `Spec (A^∧ ⧸ I ^ (n + 1) A^∧) ⟶ V`. -/
noncomputable def powStageToV (n : ℕ) : powStage V I n ⟶ V :=
  powStageToAffine V I n ≫ affineModelHom V

variable (V I) in
/-- The inclusion of the quotient stage `Spec (A^∧ ⧸ I ^ (n + 1) A^∧)` into `Spf A^∧`. -/
noncomputable def powStageIncl (n : ℕ) :
    (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj (powStage V I n) ⟶
      FormalSpace.formalSpectrum (completionQuotientSystem V I) :=
  FormalSpace.formalSpectrumInclusion (completionQuotientSystem V I)
    (OrderDual.toDual (FormalSpace.adicCompletionPowStageIdeal I I.fg_of_isNoetherianRing n))

/-- Transporting a section of a completion along an equality of sets of points. -/
theorem eqToHom_app_presheafSection {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {T₁ T₂ : Set (Space.points B S hS F)} (e : T₁ = T₂) {U : BigFppfOver B S hS}
    (x : F.obj (op U)) (h₁ : Space.HasImageIn B S hS F T₁ U x)
    (h₂ : Space.HasImageIn B S hS F T₂ U x) :
    (eqToHom (congrArg (Space.completionSheaf B S hS F) e)).hom.app (op U)
        (FormalSpace.presheafSection B S hS x h₁) = FormalSpace.presheafSection B S hS x h₂ := by
  subst e
  rfl

/-- The presheaf morphism `yonedaEquiv.symm s` attached to `s : M ⟶ M'` is `yoneda.map s`. -/
private theorem yonedaEquiv_symm_eq_yoneda_map {M M' : BigFppfOver B S hS} (s : M ⟶ M') :
    yonedaEquiv.symm s = yoneda.map s := by
  ext
  rfl

omit [IsAffine ((BigFppfOver.toScheme B S hS).obj V)]
  [IsNoetherianRing Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)] in
/-- A morphism `t : N ⟶ V` with image in `Z` precomposed with `g : N' ⟶ N` has image in `Z`. -/
theorem hasImageIn_comp {N N' : BigFppfOver B S hS} (t : N ⟶ V)
    (ht : Space.HasImageIn B S hS (yoneda.obj V) Z N t) (g : N' ⟶ N) :
    Space.HasImageIn B S hS (yoneda.obj V) Z N' (g ≫ t) := by
  rw [Space.hasImageIn_iff_range_subset] at ht ⊢
  rw [yonedaEquiv_symm_eq_yoneda_map] at ht ⊢
  rintro _ ⟨w, rfl⟩
  rw [Functor.map_comp, Space.pointsMap_comp, Function.comp_apply]
  exact ht ⟨_, rfl⟩

include hZI in
/-- The quotient stage `Spec (A^∧ ⧸ I ^ (n + 1) A^∧) ⟶ V` has image in `Z`. -/
theorem hasImageIn_powStageToV (n : ℕ) :
    Space.HasImageIn B S hS (yoneda.obj V) Z (powStage V I n) (powStageToV V I n) := by
  have h : Space.HasImageIn B S hS (yoneda.obj (affineModel V))
      (Space.pointsMap B S hS _ (yoneda.map (affineModelHom V)) ⁻¹' Z) (powStage V I n)
      (powStageToAffine V I n) := by
    rw [preimage_eq_zeroLocusPoints hZI]
    exact FormalSpace.quotientStage_hasImageIn B S hS
      (Space.contains_spec_globalSections B S hS V) (specStructure V) I
      (completionQuotientSystem V I)
      (FormalSpace.quotientSystemCompatible_adicQuotientSystem B S hS
        (Space.contains_spec_globalSections B S hS V) (specStructure V) I I.fg_of_isNoetherianRing)
      (FormalSpace.adicCompletionPowStageIdeal I I.fg_of_isNoetherianRing n)
  rw [Space.hasImageIn_iff_range_subset] at h ⊢
  rw [yonedaEquiv_symm_eq_yoneda_map] at h ⊢
  rintro _ ⟨w, rfl⟩
  rw [powStageToV, Functor.map_comp, Space.pointsMap_comp, Function.comp_apply]
  exact h ⟨w, rfl⟩

omit [IsNoetherianRing Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)] in
include hZI in
/-- Restriction along `Spec A ≅ V` sends the section of `Spec A_{/V(I)}` given by
`x : U ⟶ Spec A` to the section of `V_{/Z}` given by `x ≫ (Spec A ⟶ V)`. -/
theorem completionSheafRestrict_affineModelHom_presheafSection {U : BigFppfOver B S hS}
    (x : U ⟶ affineModel V)
    (h₁ : Space.HasImageIn B S hS (yoneda.obj (affineModel V))
      (FormalSpace.zeroLocusPoints B S hS (Space.contains_spec_globalSections B S hS V)
        (specStructure V) I) U x)
    (h₂ : Space.HasImageIn B S hS (yoneda.obj V) Z U (x ≫ affineModelHom V)) :
    (Space.completionSheafRestrict B S hS (yoneda.map (affineModelHom V))
      (FormalSpace.zeroLocusPoints B S hS (Space.contains_spec_globalSections B S hS V)
        (specStructure V) I) Z (preimage_eq_zeroLocusPoints hZI).symm.subset).hom.app (op U)
        (FormalSpace.presheafSection B S hS x h₁) =
      FormalSpace.presheafSection B S hS (F := yoneda.obj V) (x ≫ affineModelHom V) h₂ :=
  FormalSpace.completionSheafRestrict_presheafSection B S hS (yoneda.map (affineModelHom V)) _ Z
    _ x h₁ h₂

include hZI in
/-- **The inverse of `V_{/Z} ≅ Spf A^∧` on a quotient stage** is the section of `V_{/Z}` given by
`Spec (A^∧ ⧸ I ^ (n + 1) A^∧) ⟶ V`. -/
theorem completionIsoFormalSpectrum_inv_app_powStageIncl (n : ℕ) :
    (completionIsoFormalSpectrum hZI).inv.hom.app (op (powStage V I n))
        (Sheaf.sectionEquiv (BigFppfOver.topology B S hS)
          (X := powStage V I n) (F := FormalSpace.formalSpectrum (completionQuotientSystem V I))
          (powStageIncl V I n)) =
      FormalSpace.presheafSection B S hS (F := yoneda.obj V) (T := Z) (U := powStage V I n)
        (powStageToV V I n) (hasImageIn_powStageToV hZI n) := by
  let hA := Space.contains_spec_globalSections B S hS V
  let hD := FormalSpace.quotientSystemCompatible_adicQuotientSystem B S hS hA (specStructure V) I
    I.fg_of_isNoetherianRing
  let K := FormalSpace.adicCompletionPowStageIdeal I I.fg_of_isNoetherianRing n
  let c := FormalSpace.completionComparison B S hS hA (specStructure V) I
    (completionQuotientSystem V I) hD
  let r := Space.completionSheafRestrict B S hS (yoneda.map (affineModelHom V))
    (FormalSpace.zeroLocusPoints B S hS hA (specStructure V) I) Z
    (preimage_eq_zeroLocusPoints hZI).symm.subset
  have hQ : Space.HasImageIn B S hS (yoneda.obj (affineModel V))
      (FormalSpace.zeroLocusPoints B S hS hA (specStructure V) I) (powStage V I n)
      (powStageToAffine V I n) :=
    FormalSpace.quotientStage_hasImageIn B S hS hA (specStructure V) I
      (completionQuotientSystem V I) hD K
  let x₀ : (Space.completionSheaf B S hS (yoneda.obj (affineModel V))
      (FormalSpace.zeroLocusPoints B S hS hA (specStructure V) I)).obj.obj (op (powStage V I n)) :=
    FormalSpace.presheafSection B S hS (U := powStage V I n) (powStageToAffine V I n) hQ
  let qs : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj (powStage V I n) ⟶
      Space.completionSheaf B S hS (yoneda.obj (affineModel V))
        (FormalSpace.zeroLocusPoints B S hS hA (specStructure V) I) :=
    (Sheaf.sectionEquiv (BigFppfOver.topology B S hS)).symm x₀
  have hstage : powStageIncl V I n ≫ c = qs :=
    FormalSpace.completionComparison_stage B S hS hA (specStructure V) I
      (completionQuotientSystem V I) hD K
  have hinv : (completionIsoFormalSpectrum hZI).inv = c ≫ r := rfl
  rw [← Sheaf.sectionEquiv_comp, hinv, ← Category.assoc, hstage, Sheaf.sectionEquiv_comp]
  have hqs : Sheaf.sectionEquiv (BigFppfOver.topology B S hS) qs = x₀ :=
    Equiv.apply_symm_apply _ _
  refine (congrArg (fun z => r.hom.app (op (powStage V I n)) z) hqs).trans ?_
  exact completionSheafRestrict_affineModelHom_presheafSection hZI (powStageToAffine V I n) hQ
    (hasImageIn_powStageToV hZI n)

include hZI in
/-- **The value of `V_{/Z} ≅ Spf A^∧` on a section factoring through a quotient stage.** A
morphism `t : N ⟶ V` with image in `Z` which factors as `v' ≫ (Spec (A^∧ ⧸ I^{n+1}) ⟶ V)` is
sent to the section of `Spf A^∧` given by `v'`. -/
theorem sectionEquiv_symm_presheafSection_comp_completionIsoFormalSpectrum_hom
    {N : BigFppfOver B S hS} (t : N ⟶ V) (ht : Space.HasImageIn B S hS (yoneda.obj V) Z N t)
    (n : ℕ) (v' : N ⟶ powStage V I n) (hv' : v' ≫ powStageToV V I n = t) :
    (Sheaf.sectionEquiv (BigFppfOver.topology B S hS)).symm
        (FormalSpace.presheafSection B S hS t ht) ≫ (completionIsoFormalSpectrum hZI).hom =
      (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map v' ≫ powStageIncl V I n := by
  subst hv'
  refine (Iso.eq_comp_inv _).1 ?_
  apply (Sheaf.sectionEquiv (BigFppfOver.topology B S hS)).injective
  rw [Equiv.apply_symm_apply, Sheaf.sectionEquiv_comp, Sheaf.sectionEquiv_map_comp,
    NatTrans.naturality_apply, completionIsoFormalSpectrum_inv_app_powStageIncl,
    FormalSpace.presheafSection_map B S hS v' _ _ ht]
  rfl

include hZI in
/-- The inverse of `V_{/Z} ≅ Spf A^∧` on a quotient stage, in morphism form. -/
theorem powStageIncl_comp_completionIsoFormalSpectrum_inv (n : ℕ) :
    powStageIncl V I n ≫ (completionIsoFormalSpectrum hZI).inv =
      (Sheaf.sectionEquiv (BigFppfOver.topology B S hS)).symm
        (FormalSpace.presheafSection B S hS (F := yoneda.obj V) (T := Z) (U := powStage V I n)
          (powStageToV V I n) (hasImageIn_powStageToV hZI n)) := by
  apply (Sheaf.sectionEquiv (BigFppfOver.topology B S hS)).injective
  rw [Equiv.apply_symm_apply, Sheaf.sectionEquiv_comp]
  exact completionIsoFormalSpectrum_inv_app_powStageIncl hZI n

omit [IsAffine ((BigFppfOver.toScheme B S hS).obj V)] in
/-- Every weak ideal of definition of the `I`-adic completion contains some `I ^ (n + 1) A^∧`. -/
theorem exists_adicCompletionPowStageIdeal_le
    (J : { K : Ideal (AdicCompletion I Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)) //
      TopologicalRing.IsWeakIdealOfDefinition K }) :
    ∃ n : ℕ, (FormalSpace.adicCompletionPowStageIdeal I I.fg_of_isNoetherianRing n).1 ≤ J.1 := by
  let : TopologicalSpace Γ((BigFppfOver.toScheme B S hS).obj V, ⊤) := I.adicTopology
  obtain ⟨-, ⟨n, rfl⟩, hn⟩ :=
    ((I.ringFilterBasis.moduleFilterBasis (I.adic_module_basis
      (AdicCompletion I Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)))).toAddGroupFilterBasis
        |>.nhds_zero_hasBasis).mem_iff.mp (J.2.1.mem_nhds J.1.zero_mem)
  refine ⟨n, fun x hx => hn ?_⟩
  show x ∈ (I ^ n • ⊤ : Submodule Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)
    (AdicCompletion I Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)))
  rw [Ideal.smul_top_eq_map]
  exact Ideal.map_mono (Ideal.pow_le_pow_right (Nat.le_succ n)) hx

include hZI in
/-- **Morphisms out of `V_{/Z}` are determined on the quotient stages**
`Spec (A^∧ ⧸ I^{n+1} A^∧) ⟶ V`. -/
theorem completionSheaf_hom_ext_powStage {G : Sheaf (BigFppfOver.topology B S hS) (Type (u + 1))}
    {φ ψ : Space.completionSheaf B S hS (yoneda.obj V) Z ⟶ G}
    (h : ∀ n : ℕ, (Sheaf.sectionEquiv (BigFppfOver.topology B S hS)).symm
        (FormalSpace.presheafSection B S hS (F := yoneda.obj V) (T := Z) (U := powStage V I n)
          (powStageToV V I n) (hasImageIn_powStageToV hZI n)) ≫ φ =
      (Sheaf.sectionEquiv (BigFppfOver.topology B S hS)).symm
        (FormalSpace.presheafSection B S hS (F := yoneda.obj V) (T := Z) (U := powStage V I n)
          (powStageToV V I n) (hasImageIn_powStageToV hZI n)) ≫ ψ) :
    φ = ψ := by
  rw [← cancel_epi (completionIsoFormalSpectrum hZI).inv]
  apply FormalSpace.formalSpectrum_hom_ext
  intro J
  obtain ⟨n, hn⟩ := exists_adicCompletionPowStageIdeal_le (V := V) (I := I) J
  let K := FormalSpace.adicCompletionPowStageIdeal I I.fg_of_isNoetherianRing n
  have hle : OrderDual.toDual J ≤ OrderDual.toDual K :=
    OrderDual.toDual_le_toDual.mpr (Subtype.coe_le_coe.mp hn)
  have hw := colimit.w (FormalSpace.formalSpectrumDiagram (completionQuotientSystem V I))
    (homOfLE hle)
  have key : powStageIncl V I n ≫ (completionIsoFormalSpectrum hZI).inv ≫ φ =
      powStageIncl V I n ≫ (completionIsoFormalSpectrum hZI).inv ≫ ψ := by
    rw [← Category.assoc, ← Category.assoc, powStageIncl_comp_completionIsoFormalSpectrum_inv]
    exact h n
  refine (congrArg (· ≫ (completionIsoFormalSpectrum hZI).inv ≫ φ) hw.symm).trans ?_
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg (_ ≫ ·) key).trans ?_
  refine (Category.assoc _ _ _).symm.trans ?_
  exact congrArg (· ≫ (completionIsoFormalSpectrum hZI).inv ≫ ψ) hw

omit [IsAffine ((BigFppfOver.toScheme B S hS).obj V)]
  [IsNoetherianRing Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)] in
/-- Restriction along `g : V ⟶ V''` sends the section of `V_{/Z}` given by `x : U ⟶ V` to the
section of `V''_{/Z''}` given by `x ≫ g`. -/
theorem completionSheafRestrict_yoneda_presheafSection {V'' : BigFppfOver B S hS}
    {Z'' : Set (Space.points B S hS (yoneda.obj V''))} (g : V ⟶ V'')
    (hZZ : Z ⊆ Space.pointsMap B S hS _ (yoneda.map g) ⁻¹' Z'') {U : BigFppfOver B S hS}
    (x : U ⟶ V) (h₁ : Space.HasImageIn B S hS (yoneda.obj V) Z U x)
    (h₂ : Space.HasImageIn B S hS (yoneda.obj V'') Z'' U (x ≫ g)) :
    (Space.completionSheafRestrict B S hS (yoneda.map g) Z Z'' hZZ).hom.app (op U)
        (FormalSpace.presheafSection B S hS x h₁) =
      FormalSpace.presheafSection B S hS (F := yoneda.obj V'') (x ≫ g) h₂ :=
  FormalSpace.completionSheafRestrict_presheafSection B S hS (yoneda.map g) Z Z'' hZZ x h₁ h₂

/-! ### Naturality of the dictionary -/

section Naturality

variable {V' : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj V')]
  [IsNoetherianRing Γ((BigFppfOver.toScheme B S hS).obj V', ⊤)]
  {I' : Ideal Γ((BigFppfOver.toScheme B S hS).obj V', ⊤)}
  {Z' : Set (Space.points B S hS (yoneda.obj V'))}
  (hZ'I' : ∀ x, x ∈ Z' ↔ Space.pointsToScheme B S hS V' x ∈
    ((BigFppfOver.toScheme B S hS).obj V').zeroLocus
      (I' : Set Γ((BigFppfOver.toScheme B S hS).obj V', ⊤)))
  (f : V ⟶ V')
  (hII : I'.map ((BigFppfOver.toScheme B S hS).map f).appTop.hom ≤ I)

omit [IsAffine ((BigFppfOver.toScheme B S hS).obj V)]
  [IsAffine ((BigFppfOver.toScheme B S hS).obj V')] in
include hII in
/-- The map `A'^∧ ⟶ A^∧` induced by `f` sends `I'^{n+1} A'^∧` into `I^{n+1} A^∧`. -/
theorem map_adicCompletionPowStageIdeal_le (n : ℕ) :
    (FormalSpace.adicCompletionPowStageIdeal I' I'.fg_of_isNoetherianRing n).1.map
        (completionRingHom ((BigFppfOver.toScheme B S hS).map f).appTop.hom hII) ≤
      (FormalSpace.adicCompletionPowStageIdeal I I.fg_of_isNoetherianRing n).1 := by
  show ((I' ^ (n + 1)).map (algebraMap _ _)).map _ ≤ (I ^ (n + 1)).map (algebraMap _ _)
  rw [Ideal.map_map]
  have h : (completionRingHom ((BigFppfOver.toScheme B S hS).map f).appTop.hom hII).comp
      (algebraMap Γ((BigFppfOver.toScheme B S hS).obj V', ⊤)
        (AdicCompletion I' Γ((BigFppfOver.toScheme B S hS).obj V', ⊤))) =
      (algebraMap Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)
        (AdicCompletion I Γ((BigFppfOver.toScheme B S hS).obj V, ⊤))).comp
        ((BigFppfOver.toScheme B S hS).map f).appTop.hom :=
    RingHom.ext fun a => completionRingHom_of _ hII a
  rw [h, ← Ideal.map_map]
  exact Ideal.map_mono ((Ideal.map_pow _ _ _).trans_le (Ideal.pow_right_mono hII _))

/-- The ring map `A'^∧ ⧸ I'^{n+1} ⟶ A^∧ ⧸ I^{n+1}` induced by `f`. -/
noncomputable def powStageRingHom (n : ℕ) :
    AdicCompletion I' Γ((BigFppfOver.toScheme B S hS).obj V', ⊤) ⧸
        (FormalSpace.adicCompletionPowStageIdeal I' I'.fg_of_isNoetherianRing n).1 →+*
      AdicCompletion I Γ((BigFppfOver.toScheme B S hS).obj V, ⊤) ⧸
        (FormalSpace.adicCompletionPowStageIdeal I I.fg_of_isNoetherianRing n).1 :=
  Ideal.quotientMap _ (completionRingHom ((BigFppfOver.toScheme B S hS).map f).appTop.hom hII)
    (Ideal.map_le_iff_le_comap.mp (map_adicCompletionPowStageIdeal_le f hII n))

omit [IsAffine ((BigFppfOver.toScheme B S hS).obj V)]
  [IsAffine ((BigFppfOver.toScheme B S hS).obj V')] in
/-- The ring map `A'^∧ ⧸ I'^{n+1} ⟶ A^∧ ⧸ I^{n+1}` is compatible with `f^♯ : A' ⟶ A`. -/
theorem powStageRingHom_comp (n : ℕ) :
    (powStageRingHom f hII n).comp ((Ideal.Quotient.mk _).comp
      (algebraMap Γ((BigFppfOver.toScheme B S hS).obj V', ⊤)
        (AdicCompletion I' Γ((BigFppfOver.toScheme B S hS).obj V', ⊤)))) =
      ((Ideal.Quotient.mk _).comp (algebraMap Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)
        (AdicCompletion I Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)))).comp
        ((BigFppfOver.toScheme B S hS).map f).appTop.hom := by
  ext a
  simp only [RingHom.comp_apply, powStageRingHom, Ideal.quotientMap_mk]
  rw [AdicCompletion.algebraMap_apply, completionRingHom_of]
  rfl

/-- The morphism `Spec (A^∧ ⧸ I^{n+1}) ⟶ Spec (A'^∧ ⧸ I'^{n+1})` is compatible with `f`, as
morphisms of schemes into `V'`. -/
theorem spec_powStageRingHom_comp (n : ℕ) :
    Spec.map (CommRingCat.ofHom (powStageRingHom f hII n)) ≫
        Spec.map (CommRingCat.ofHom ((Ideal.Quotient.mk _).comp
          (algebraMap Γ((BigFppfOver.toScheme B S hS).obj V', ⊤)
            (AdicCompletion I' Γ((BigFppfOver.toScheme B S hS).obj V', ⊤))))) ≫
          ((BigFppfOver.toScheme B S hS).obj V').isoSpec.inv =
      Spec.map (CommRingCat.ofHom ((Ideal.Quotient.mk _).comp
          (algebraMap Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)
            (AdicCompletion I Γ((BigFppfOver.toScheme B S hS).obj V, ⊤))))) ≫
        ((BigFppfOver.toScheme B S hS).obj V).isoSpec.inv ≫
          (BigFppfOver.toScheme B S hS).map f := by
  rw [← Scheme.isoSpec_inv_naturality, ← Category.assoc, ← Spec.map_comp, ← Category.assoc,
    ← Spec.map_comp]
  congr 2

/-- The morphism `Spec (A^∧ ⧸ I^{n+1}) ⟶ Spec (A'^∧ ⧸ I'^{n+1})` of quotient stages induced by
`f`. -/
noncomputable def powStageMap (n : ℕ) : powStage V I n ⟶ powStage V' I' n :=
  FormalSpace.siteHom B S hS (Spec.map (CommRingCat.ofHom (powStageRingHom f hII n))) (by
    change Spec.map (CommRingCat.ofHom (powStageRingHom f hII n)) ≫
        Spec.map (CommRingCat.ofHom ((Ideal.Quotient.mk _).comp
          (algebraMap Γ((BigFppfOver.toScheme B S hS).obj V', ⊤)
            (AdicCompletion I' Γ((BigFppfOver.toScheme B S hS).obj V', ⊤))))) ≫
          ((BigFppfOver.toScheme B S hS).obj V').isoSpec.inv ≫ V'.hom.hom =
      Spec.map (CommRingCat.ofHom ((Ideal.Quotient.mk _).comp
          (algebraMap Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)
            (AdicCompletion I Γ((BigFppfOver.toScheme B S hS).obj V, ⊤))))) ≫
        ((BigFppfOver.toScheme B S hS).obj V).isoSpec.inv ≫ V.hom.hom
    have hf : (BigFppfOver.toScheme B S hS).map f ≫ V'.hom.hom = V.hom.hom :=
      congrArg (fun k => k.hom) (Over.w f)
    rw [← hf]
    simp only [← Category.assoc]
    congr 1
    simp only [Category.assoc]
    exact spec_powStageRingHom_comp f hII n)

/-- The morphism of quotient stages induced by `f` is compatible with the morphisms to `V` and
`V'`. -/
theorem powStageMap_comp_powStageToV (n : ℕ) :
    powStageMap f hII n ≫ powStageToV V' I' n = powStageToV V I n ≫ f :=
  BigFppfOver.map_toScheme_injective B S hS (by
    simp only [Functor.map_comp]
    exact spec_powStageRingHom_comp f hII n)

variable {Bt : Type u} [CommRing Bt] [TopologicalSpace Bt] [IsTopologicalRing Bt]
  [IsLinearTopology Bt Bt] (hB : TopologicalRing.IsWeaklyAdmissible Bt)
  {DB : FormalSpace.QuotientSystem B S hS Bt}

include hZI hZ'I' in
/-- **Naturality of the dictionary.** For `f : V ⟶ V'` with `f^♯(I') ⊆ I` and `Z ⊆ f⁻¹ Z'`, the
restriction along `f_{/Z}` of the morphism given by `φ' : B → A'^∧` is the morphism given by the
composite `B → A'^∧ → A^∧`. -/
theorem completionSheafRestrict_comp_continuousHomEquiv
    (hZZ : Z ⊆ Space.pointsMap B S hS _ (yoneda.map f) ⁻¹' Z')
    (φ' : FormalSpace.ContinuousHom DB (completionQuotientSystem V' I'))
    (φ : FormalSpace.ContinuousHom DB (completionQuotientSystem V I))
    (hφ : φ.toRingHom = (completionRingHom ((BigFppfOver.toScheme B S hS).map f).appTop.hom
      hII).comp φ'.toRingHom) :
    Space.completionSheafRestrict B S hS (yoneda.map f) Z Z' hZZ ≫
        continuousHomEquiv hZ'I' hB φ' = continuousHomEquiv hZI hB φ := by
  obtain ⟨hTR, hLT, -, -, hAw⟩ :=
    FormalSpace.adicCompletion_isAdic_of_fg I I.fg_of_isNoetherianRing
  obtain ⟨hTR', hLT', -, -, hAw'⟩ :=
    FormalSpace.adicCompletion_isAdic_of_fg I' I'.fg_of_isNoetherianRing
  apply completionSheaf_hom_ext_powStage hZI
  intro n
  let Y := Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)
  let K := FormalSpace.adicCompletionPowStageIdeal I I.fg_of_isNoetherianRing n
  let K' := FormalSpace.adicCompletionPowStageIdeal I' I'.fg_of_isNoetherianRing n
  have ht : Space.HasImageIn B S hS (yoneda.obj V') Z' (powStage V I n)
      (powStageToV V I n ≫ f) := by
    rw [← powStageMap_comp_powStageToV f hII n]
    exact hasImageIn_comp (powStageToV V' I' n) (hasImageIn_powStageToV hZ'I' n)
      (powStageMap f hII n)
  have h1 : (Sheaf.sectionEquiv (BigFppfOver.topology B S hS)).symm
      (FormalSpace.presheafSection B S hS (F := yoneda.obj V) (T := Z) (U := powStage V I n)
        (powStageToV V I n) (hasImageIn_powStageToV hZI n)) ≫
        Space.completionSheafRestrict B S hS (yoneda.map f) Z Z' hZZ =
      (Sheaf.sectionEquiv (BigFppfOver.topology B S hS)).symm
        (FormalSpace.presheafSection B S hS (F := yoneda.obj V') (T := Z') (U := powStage V I n)
          (powStageToV V I n ≫ f) ht) := by
    rw [← Sheaf.sectionEquiv_symm_comp]
    congr 1
    exact completionSheafRestrict_yoneda_presheafSection f hZZ (powStageToV V I n) _ ht
  have h2 := sectionEquiv_symm_presheafSection_comp_completionIsoFormalSpectrum_hom hZ'I'
    (powStageToV V I n ≫ f) ht n (powStageMap f hII n) (powStageMap_comp_powStageToV f hII n)
  have h3 := sectionEquiv_symm_presheafSection_comp_completionIsoFormalSpectrum_hom hZI
    (powStageToV V I n) (hasImageIn_powStageToV hZI n) n (𝟙 _) (Category.id_comp _)
  rw [CategoryTheory.Functor.map_id, Category.id_comp] at h3
  obtain ⟨J, hJ', hJ⟩ := FormalSpace.exists_isWeakIdealOfDefinition_le_comap_of_isOpen hB
    φ'.continuous φ.continuous K'.2.1 K.2.1
  let inclB : Y.obj ((BigAffineFppf.inclusion B S hS).obj (DB.stage J)) ⟶
      FormalSpace.formalSpectrum DB :=
    FormalSpace.formalSpectrumInclusion DB (OrderDual.toDual J)
  let a' : powStage V' I' n ⟶ (BigAffineFppf.inclusion B S hS).obj (DB.stage J) :=
    (BigAffineFppf.inclusion B S hS).map (φ'.stageMap J K' hJ')
  let a : powStage V I n ⟶ (BigAffineFppf.inclusion B S hS).obj (DB.stage J) :=
    (BigAffineFppf.inclusion B S hS).map (φ.stageMap J K hJ)
  have hs' : powStageIncl V' I' n ≫ FormalSpace.formalSpectrumMap hB φ' = Y.map a' ≫ inclB :=
    FormalSpace.formalSpectrumMap_spec hB φ' J K' hJ'
  have hs : powStageIncl V I n ≫ FormalSpace.formalSpectrumMap hB φ = Y.map a ≫ inclB :=
    FormalSpace.formalSpectrumMap_spec hB φ J K hJ
  have hst : powStageMap f hII n ≫ a' = a :=
    BigFppfOver.map_toScheme_injective B S hS (by
      show Spec.map (CommRingCat.ofHom (powStageRingHom f hII n)) ≫
          Spec.map (CommRingCat.ofHom (Ideal.quotientMap K'.1 φ'.toRingHom hJ')) =
        Spec.map (CommRingCat.ofHom (Ideal.quotientMap K.1 φ.toRingHom hJ))
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
      congr 2
      ext x
      simp only [RingHom.comp_apply, Ideal.quotientMap_mk, powStageRingHom, hφ]
      rfl)
  simp only [continuousHomEquiv_apply]
  rw [← Category.assoc, h1, ← Category.assoc, h2, ← Category.assoc, h3, Category.assoc, hs',
    hs, ← Category.assoc, ← Functor.map_comp, hst]

end Naturality

omit [IsAffine ((BigFppfOver.toScheme B S hS).obj V)]
  [IsNoetherianRing Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)] in
/-- A Noetherian affine formal algebraic space is the formal spectrum of a Noetherian adic
weakly admissible topological ring over `S` (Stacks 0AIC). -/
theorem exists_iso_formalSpectrum_of_isNoetherian {W₀ : FormalSpace.FppfSheaf B S hS}
    (hW₀ : FormalSpace.IsNoetherian B S hS W₀) :
    ∃ (Bt : Type u) (_ : CommRing Bt) (_ : TopologicalSpace Bt) (_ : IsTopologicalRing Bt)
      (_ : IsLinearTopology Bt Bt) (DB : FormalSpace.QuotientSystem B S hS Bt),
      TopologicalRing.IsWeaklyAdmissible Bt ∧ IsNoetherianRing Bt ∧ TopologicalRing.IsAdic Bt ∧
        Nonempty (W₀ ≅ FormalSpace.formalSpectrum DB) := by
  obtain ⟨-, Bt, _, _, _, _, hpres, hnoeth, hadic⟩ := hW₀
  obtain ⟨DB, he⟩ := FormalSpace.exists_quotientSystem_iso_formalSpectrum_of_isPresentingRing hpres
  exact ⟨Bt, _, _, _, _, DB, hpres.1, hnoeth, hadic, he⟩

end AlgebraicGeometry.Artin.FormalDictionary

end
