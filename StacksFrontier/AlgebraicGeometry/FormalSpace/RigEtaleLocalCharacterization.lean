module

public import Mathlib.Data.List.TFAE
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.AdicMorphismConverse
public import StacksFrontier.AlgebraicGeometry.FormalSpace.AffineCompletionTypes
public import StacksFrontier.AlgebraicGeometry.FormalSpace.EtaleCompletionCover
public import StacksFrontier.AlgebraicGeometry.FormalSpace.EtaleCompletionFiniteCover
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RepresentableEtaleCancellationGeneral
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RigEtaleChartLocality
public import StacksFrontier.AlgebraicGeometry.FormalSpace.TautMorphismRepresentability

/-!
# Rig-étale morphisms of locally Noetherian formal algebraic spaces are étale local

Let `S` be a scheme contained in a big fppf site `B` and let `f : X ⟶ Y` be a morphism of
locally Noetherian formal algebraic spaces over `S`. **Stacks 0GCZ** says that the following
are equivalent:

1. `f` is rig-étale;
2. for every commutative square with affine formal algebraic spaces `U`, `V` and representable
   étale maps `U ⟶ X`, `V ⟶ Y`, the upper map `U ⟶ V` corresponds to a rig-étale map in
   `WAdm^{Noeth}`;
3. there is a covering `{Yⱼ ⟶ Y}` as in Definition 0AIM and for each `j` a covering
   `{Xⱼᵢ ⟶ Yⱼ ×_Y X}` as in Definition 0AIM such that each `Xⱼᵢ ⟶ Yⱼ` corresponds to a
   rig-étale map in `WAdm^{Noeth}`;
4. there is a covering `{Xᵢ ⟶ X}` as in Definition 0AIM and for each `i` a factorization
   `Xᵢ ⟶ Yᵢ ⟶ Y` with `Yᵢ` an affine formal algebraic space, `Yᵢ ⟶ Y` representable étale,
   and `Xᵢ ⟶ Yᵢ` corresponding to a rig-étale map in `WAdm^{Noeth}`.

## Main definitions

* `AlgebraicGeometry.FormalSpace.CorrespondsToRigEtaleMap`: a morphism of fppf sheaves
  corresponds to a rig-étale map in `WAdm^{Noeth}`.

## Main results

* `AlgebraicGeometry.FormalSpace.hasPropertyOnAffineChartMap_of_correspondsToRigEtaleMap`:
  whether a morphism corresponds to a rig-étale map does not depend on the presentation.
* `AlgebraicGeometry.FormalSpace.hasPropertyOnAffineChartMap_comp_of_isRepresentableEtale`: a
  rig-étale chart map followed by a representable étale map to a Noetherian chart is rig-étale.
* `AlgebraicGeometry.FormalSpace.isRigEtale_tfae_of_isLocallyNoetherian`: **Stacks 0GCZ** with
  condition (2) read through Definition 0AQM; the registered statement, with the source's
  condition (2), is `AlgebraicGeometry.FormalSpace.isRigEtale_tfae_of_isLocallyNoetherian'` in
  `StacksFrontier.AlgebraicGeometry.FormalSpace.RigEtaleLocalCharacterizationCharts`.

## Implementation notes

Condition (2) is, as the source's proof says, Definition 0AQM itself, and is read as the
library reads that definition (`AlgebraicGeometry.FormalSpace.IsRigEtale`): for every
presentation of `U ⟶ V` by Noetherian adic rings the presenting homomorphism is rig-étale.
Every affine formal algebraic space representable étale over a locally Noetherian formal
algebraic space is Noetherian (Stacks 0AKX), so these charts always have such presentations,
and this reading agrees with the source's; the statement with the source's reading is in
`StacksFrontier.AlgebraicGeometry.FormalSpace.RigEtaleLocalCharacterizationCharts`. Conditions (3)
and (4) are read literally through `CorrespondsToRigEtaleMap`: the charts are formal spectra of
Noetherian adic rings and the map between them is the formal spectrum of a rig-étale
homomorphism. By Stacks 0AN0 and the invariance of rig-étaleness under isomorphisms of
topological rings, a map corresponding to a rig-étale map has every Noetherian presentation
rig-étale (`hasPropertyOnAffineChartMap_of_correspondsToRigEtaleMap`), and conversely a map
between Noetherian charts all of whose presentations are rig-étale corresponds to a rig-étale map
(`correspondsToRigEtaleMap_of_hasPropertyOnAffineChartMap`).

The proof follows the source: Definition 0AQM is condition (2), and the other equivalences are
the argument of Stacks 0ANG for the property of Stacks 0AQL. For (4) ⟹ (2), a square
`U₀ ⟶ V₀` over `f` is refined by the fibre products `Vᵢ ×_Y V₀` and `Uᵢ ×_X U₀`, which are
covered by formal spectra of completed étale algebras
(`exists_completion_cover_of_isRepresentableEtale`), a finite subfamily of which covers `U₀`
(`exists_finite_faithfullyFlat_of_isLocallySurjective`); rig-étaleness ascends from the given
charts to the refinement (axiom (1) of Situation 0CBA), passes to the composite with the
representable étale map to `V₀`, and descends to `U₀ ⟶ V₀` (axioms (2) and (3)).

## References

* [Stacks Project, Tag 0AN0](https://stacks.math.columbia.edu/tag/0AN0)
* [Stacks Project, Tag 0AN8](https://stacks.math.columbia.edu/tag/0AN8)
* [Stacks Project, Tag 0ANG](https://stacks.math.columbia.edu/tag/0ANG)
* [Stacks Project, Tag 0AQL](https://stacks.math.columbia.edu/tag/0AQL)
* [Stacks Project, Tag 0AQM](https://stacks.math.columbia.edu/tag/0AQM)
* [Stacks Project, Tag 0GCZ](https://stacks.math.columbia.edu/tag/0GCZ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalRing

universe u

namespace AlgebraicGeometry.FormalSpace

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- A morphism `t : U ⟶ V` of fppf sheaves *corresponds to a rig-étale map in `WAdm^{Noeth}`*:
`V` and `U` are formal spectra of Noetherian adic rings `A` and `R`, and `t` is the formal
spectrum of a rig-étale continuous homomorphism `A → R`. -/
abbrev CorrespondsToRigEtaleMap {U V : FppfSheaf B S hS} (t : U ⟶ V) : Prop :=
  ∃ (A R : Type u) (_ : CommRing A) (_ : TopologicalSpace A) (_ : IsTopologicalRing A)
    (_ : IsLinearTopology A A) (_ : CommRing R) (_ : TopologicalSpace R) (_ : IsTopologicalRing R)
    (_ : IsLinearTopology R R), IsNoetherianAdic A ∧ IsNoetherianAdic R ∧
    ∃ (hA : IsWeaklyAdmissible A) (D : QuotientSystem B S hS A) (E : QuotientSystem B S hS R)
      (eU : U ≅ formalSpectrum E) (eV : V ≅ formalSpectrum D) (g : ContinuousHom D E),
      t = eU.hom ≫ formalSpectrumMap hA g ≫ eV.inv ∧ IsRigEtaleHom g.toRingHom

/-- The formal spectrum of a Noetherian adic ring is an affine formal algebraic space. -/
theorem isAffineFormalAlgebraicSpace_of_iso_formalSpectrum_of_isAdic {U : FppfSheaf B S hS}
    {A : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A]
    (hA : TopologicalRing.IsAdic A) (D : QuotientSystem B S hS A) (e : U ≅ formalSpectrum D) :
    IsAffineFormalAlgebraicSpace B S hS U :=
  isAffineFormalAlgebraicSpace_of_iso B S hS e.symm
    (isAffineFormalAlgebraicSpace_formalSpectrum hA.isWeaklyAdmissible D
      (hasLargeSite_of_mk_lt_cutoff D (mk_lt_cutoff_of_quotientSystem_of_isAdic B S hS hA D)))

/-- **Presentation independence.** A morphism corresponding to a rig-étale map in
`WAdm^{Noeth}` has every presentation by Noetherian adic rings rig-étale: two presentations
differ by isomorphisms of topological rings (Stacks 0AN0), along which rig-étaleness is
transported. -/
theorem hasPropertyOnAffineChartMap_of_correspondsToRigEtaleMap {U V : FppfSheaf B S hS}
    {t : U ⟶ V} (ht : CorrespondsToRigEtaleMap B S hS t) :
    HasPropertyOnAffineChartMap B S hS IsNoetherianAdic IsRigEtaleHom t := by
  obtain ⟨A, R, _, _, _, _, _, _, _, _, hCA, hCR, hA, D, E, eU, eV, g, hg, hP⟩ := ht
  exact hasPropertyOnAffineChartMap_of_isRepresentableEtale B S hS t t (𝟙 U) (𝟙 V)
    (isAffineFormalAlgebraicSpace_of_iso_formalSpectrum_of_isAdic B S hS hCR.1 E eU)
    (isAffineFormalAlgebraicSpace_of_iso_formalSpectrum_of_isAdic B S hS hCA.1 D eV)
    (isRepresentableEtale_of_isIso B S hS _) (isRepresentableEtale_of_isIso B S hS _)
    (by simp) A R hCA hCR hA D E eU eV g hg hP

/-- A morphism between formal spectra of Noetherian adic rings all of whose Noetherian
presentations are rig-étale corresponds to a rig-étale map in `WAdm^{Noeth}`: the presenting
homomorphism exists by Stacks 0AN0. -/
theorem correspondsToRigEtaleMap_of_hasPropertyOnAffineChartMap {U V : FppfSheaf B S hS}
    {t : U ⟶ V} (ht : HasPropertyOnAffineChartMap B S hS IsNoetherianAdic IsRigEtaleHom t)
    {A R : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A]
    [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [IsLinearTopology R R]
    (hCA : IsNoetherianAdic A) (hCR : IsNoetherianAdic R) (D : QuotientSystem B S hS A)
    (E : QuotientSystem B S hS R) (eU : U ≅ formalSpectrum E) (eV : V ≅ formalSpectrum D) :
    CorrespondsToRigEtaleMap B S hS t := by
  have hA := hCA.1.isWeaklyAdmissible
  obtain ⟨g, hg, -⟩ := existsUnique_continuousHom_formalSpectrumMap_eq hA
    hCR.1.isWeaklyAdmissible (eU.inv ≫ t ≫ eV.hom)
  have htg : t = eU.hom ≫ formalSpectrumMap hA g ≫ eV.inv := by simp [hg]
  exact ⟨A, R, _, _, _, _, _, _, _, _, hCA, hCR, hA, D, E, eU, eV, g, htg,
    ht A R hCA hCR hA D E eU eV g htg⟩

/-- **A rig-étale chart map followed by a representable étale map.** Let `m : W ⟶ Z` be a
morphism of affine formal algebraic spaces all of whose Noetherian presentations are rig-étale
and let `c : Z ⟶ V` be representable étale. Then every Noetherian presentation of `m ≫ c` is
rig-étale.

For a presentation `A → R` of `m ≫ c`, Stacks 0AN8 presents `c` by the canonical map
`A → A₁^` to the completion of an étale `A`-algebra, which is rig-étale; by Stacks 0AN0 the
presentation of `m ≫ c` factors as `A → A₁^ → R` with `A₁^ → R` a presentation of `m`, and
rig-étaleness is stable under composition (Stacks 0GCX). -/
theorem hasPropertyOnAffineChartMap_comp_of_isRepresentableEtale {W Z V : FppfSheaf B S hS}
    (m : W ⟶ Z) (c : Z ⟶ V) (hZ : IsAffineFormalAlgebraicSpace B S hS Z)
    (hc : IsRepresentableEtale B S hS c)
    (hm : HasPropertyOnAffineChartMap B S hS IsNoetherianAdic IsRigEtaleHom m) :
    HasPropertyOnAffineChartMap B S hS IsNoetherianAdic IsRigEtaleHom (m ≫ c) := by
  intro A R _ _ _ _ _ _ _ _ hCA hCR hA D E eW eV g hg
  have : IsNoetherianRing A := hCA.2
  have : IsNoetherianRing R := hCR.2
  have hRw := hCR.1.isWeaklyAdmissible
  obtain ⟨A₁, _, _, _, D₁, cV, εZ, hcV, hεZ⟩ :=
    exists_etale_completion_of_isRepresentableEtale B S hS c hZ hc A hCA.1 D eV
  have hA₁ : IsNoetherianAdic (CompletionOver (algebraMap A A₁)) :=
    completionOver_isNoetherianAdic _ hCA (Algebra.FiniteType.isNoetherianRing A A₁)
  have hA₁w := hA₁.1.isWeaklyAdmissible
  have : IsNoetherianRing (CompletionOver (algebraMap A A₁)) := hA₁.2
  obtain ⟨h, hh, -⟩ := existsUnique_continuousHom_formalSpectrumMap_eq hA₁w hRw
    (eW.inv ≫ m ≫ εZ.hom)
  have hmh : m = eW.hom ≫ formalSpectrumMap hA₁w h ≫ εZ.inv := by simp [hh]
  have hrig : IsRigEtaleHom h.toRingHom := hm _ _ hA₁ hCR hA₁w D₁ E eW εZ h hmh
  have hspf : formalSpectrumMap hA g = formalSpectrumMap hA (ContinuousHom.comp hA₁w hA h cV) := by
    rw [← formalSpectrumMap_comp_eq hA₁w hA, hh,
      show formalSpectrumMap hA g = eW.inv ≫ (m ≫ c) ≫ eV.hom by simp [hg], Category.assoc,
      Category.assoc, Category.assoc, hεZ]
  have hring : g.toRingHom = h.toRingHom.comp cV.toRingHom := by
    rw [toRingHom_eq_of_formalSpectrumMap_eq B S hS hA hRw hspf]
    rfl
  intro _ _ _ _
  obtain ⟨hhc, hhr⟩ := hrig
  obtain ⟨hcc, hcr⟩ := Rig.isRigEtale_canonicalMap (algebraMap A A₁)
    (RingHom.etale_algebraMap.mpr inferInstance) hCA.1 hA₁.1
  rw [hring, hcV]
  exact ⟨hhc.comp hcc, Rig.rigEtale_comp hCR.1 hA₁.1 hCA.1 _ _ hhc hcc hhr hcr⟩

/-- **Charts of a sheaf representable étale over a Noetherian chart.** A sheaf `E'` with a
representable étale morphism `φ` to `Spf A`, for `A` a Noetherian adic ring, is covered jointly
surjectively by the formal spectra of the completions of étale `A`-algebras, mapping to `E'`
representably and étale over `Spf A`; these completions are Noetherian adic rings. -/
theorem exists_noetherian_completion_cover_of_isRepresentableEtale {A : Type u} [CommRing A]
    [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A] (hCA : IsNoetherianAdic A)
    (D : QuotientSystem B S hS A) {E' : FppfSheaf B S hS} (φ : E' ⟶ formalSpectrum D)
    (hφ : IsRepresentableEtale B S hS φ) :
    letI : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
    ∃ (K : Type (u + 1)) (C : K → Type u) (_ : ∀ k, CommRing (C k)) (f : ∀ k, A →+* C k)
      (_ : ∀ k, (f k).Etale) (Q : ∀ k, QuotientSystem B S hS (CompletionOver (f k)))
      (g : ∀ k, ContinuousHom D (Q k))
      (_ : ∀ k, (g k).toRingHom = CompletionOver.canonicalMap (f k))
      (w : ∀ k, formalSpectrum (Q k) ⟶ E'),
      (∀ k, w k ≫ φ = formalSpectrumMap hCA.1.isWeaklyAdmissible (g k)) ∧
      (∀ k, IsRepresentableEtale B S hS (w k)) ∧
      (∀ k, IsAffineFormalAlgebraicSpace B S hS (formalSpectrum (Q k))) ∧
      (∀ k, IsNoetherianAdic (CompletionOver (f k))) ∧
      Sheaf.IsLocallySurjective (Sigma.desc w) := by
  let : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
  have : IsNoetherianRing A := hCA.2
  have hAw := hCA.1.isWeaklyAdmissible
  obtain ⟨I, -, hIadic⟩ := hCA.1.1
  have hD : D.HasLargeSite :=
    hasLargeSite_of_mk_lt_cutoff D (mk_lt_cutoff_of_quotientSystem_of_isAdic B S hS hCA.1 D)
  obtain ⟨K, C, _, f, hf, Q, g, hg, w, hw, hsurj⟩ :=
    exists_completion_cover_of_isRepresentableEtale B S hS hAw (IsNoetherian.noetherian I)
      hIadic D hD φ hφ
  have hft : ∀ k, let : Algebra A (C k) := (f k).toAlgebra; Algebra.FiniteType A (C k) :=
    fun k ↦ by
      let : Algebra A (C k) := (f k).toAlgebra
      have : Algebra.Etale A (C k) := hf k
      infer_instance
  refine ⟨K, C, inferInstance, f, hf, Q, g, hg, w, hw, fun k ↦ ?_, fun k ↦ ?_, fun k ↦ ?_, hsurj⟩
  · exact isRepresentableEtale_of_comp' B S hS (w k) φ hφ (hw k ▸
      isRepresentableEtale_formalSpectrumMap_of_etale B S hS hAw D hD (f k) (hf k) (Q k) (g k)
        (hg k))
  · exact isAffineFormalAlgebraicSpace_formalSpectrum
      (TopologicalRing.completionOver_isWeaklyAdmissible (f k) hAw) (Q k)
      (hasLargeSite_completionOver_of_finiteType B S hS (f k) (hft k) hD (Q k))
  · let : Algebra A (C k) := (f k).toAlgebra
    exact completionOver_isNoetherianAdic _ hCA (Algebra.FiniteType.isNoetherianRing A (C k))

/-- The first projection of a fibre product along a representable étale morphism is
representable étale. -/
theorem isRepresentableEtale_pullback_fst {X Y V : FppfSheaf B S hS} (v : V ⟶ Y) (f : X ⟶ Y)
    (hf : IsRepresentableEtale B S hS f) : IsRepresentableEtale B S hS (pullback.fst v f) := by
  rw [← pullbackSymmetry_hom_comp_snd]
  exact (isRepresentableEtale_of_isIso B S hS _).comp B S hS
    (isRepresentableEtale_pullback_snd B S hS f v hf)

/-- **Stacks 0GCZ, condition (3).** There is a covering `{Yⱼ ⟶ Y}` as in Definition 0AIM and
for each `j` a covering `{Xⱼᵢ ⟶ Yⱼ ×_Y X}` as in Definition 0AIM such that each `Xⱼᵢ ⟶ Yⱼ`
corresponds to a rig-étale map in `WAdm^{Noeth}`. -/
abbrev CorrespondsToRigEtaleMapAfterTargetCover {X Y : FppfSheaf B S hS} (f : X ⟶ Y) : Prop :=
  ∃ (J : Type (u + 1)) (V : J → FppfSheaf B S hS) (v : ∀ j, V j ⟶ Y),
    IsAffineEtaleCover B S hS V v ∧
      ∀ j, ∃ (I : Type (u + 1)) (U : I → FppfSheaf B S hS)
        (w : ∀ i, U i ⟶ pullback (v j) f),
        IsAffineEtaleCover B S hS U w ∧
          ∀ i, CorrespondsToRigEtaleMap B S hS (w i ≫ pullback.fst (v j) f)

/-- **Stacks 0GCZ, condition (4).** There is a covering `{Xᵢ ⟶ X}` as in Definition 0AIM and for
each `i` a factorization `Xᵢ ⟶ Yᵢ ⟶ Y` with `Yᵢ` an affine formal algebraic space, `Yᵢ ⟶ Y`
representable étale and `Xᵢ ⟶ Yᵢ` corresponding to a rig-étale map in `WAdm^{Noeth}`. -/
abbrev CorrespondsToRigEtaleMapAfterSourceCover {X Y : FppfSheaf B S hS} (f : X ⟶ Y) : Prop :=
  ∃ (I : Type (u + 1)) (U : I → FppfSheaf B S hS) (u : ∀ i, U i ⟶ X),
    IsAffineEtaleCover B S hS U u ∧
      ∀ i, ∃ (V : FppfSheaf B S hS) (v : V ⟶ Y) (t : U i ⟶ V),
        IsAffineFormalAlgebraicSpace B S hS V ∧ IsRepresentableEtale B S hS v ∧
          u i ≫ f = t ≫ v ∧ CorrespondsToRigEtaleMap B S hS t

/-- Composing the coverings of the fibre products `Vⱼ ×_Y X` with the projections to `X` gives
a covering of `X`. -/
private theorem isLocallySurjective_sigmaDesc_comp_pullback_snd {X Y : FppfSheaf B S hS}
    (f : X ⟶ Y) {J : Type (u + 1)} {V : J → FppfSheaf B S hS} (v : ∀ j, V j ⟶ Y)
    (hv : letI : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) :=
      Sheaf.instHasColimitsOfSize; Sheaf.IsLocallySurjective (Sigma.desc v))
    {K : J → Type (u + 1)} {U : (j : J) → K j → FppfSheaf B S hS}
    (w : ∀ j k, U j k ⟶ pullback (v j) f)
    (hw : letI : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) :=
      Sheaf.instHasColimitsOfSize; ∀ j, Sheaf.IsLocallySurjective (Sigma.desc (w j))) :
    letI : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
    Sheaf.IsLocallySurjective
      (Sigma.desc fun x : Σ j, K j ↦ w x.1 x.2 ≫ pullback.snd (v x.1) f) :=
  isLocallySurjective_sigmaDesc_comp_sigma B S hS (fun j ↦ pullback.snd (v j) f)
    (Sheaf.isLocallySurjective_sigmaDesc_pullback_snd f v hv) (fun x ↦ w x.1 x.2) hw

attribute [-instance] CategoryTheory.catToReflQuiver in
/-- **Stacks 0GCZ, (4) ⟹ (2).** If the members of an affine étale covering of `X` factor through
affine representable étale charts of `Y` by maps corresponding to rig-étale maps in
`WAdm^{Noeth}`, then every affine étale square over `f` has every Noetherian presentation of its
upper map rig-étale.

Given a square `U₀ ⟶ V₀` over `f` and a presentation `g : A → R` of it, the fibre products
`Qᵢ = Vᵢ ×_Y V₀` are covered by formal spectra `Z` of completed étale `A`-algebras, and the
fibre products `Zᵢ ×_{Qᵢ} (Uᵢ ×_X U₀)` by formal spectra `W` of completed étale `R`-algebras;
the `W` cover `U₀` and finitely many of them make `R` faithfully flat over their product
(`exists_finite_faithfullyFlat_of_isLocallySurjective`). Each `W ⟶ Z` is rig-étale by the
ascent from `Uᵢ ⟶ Vᵢ`, hence so is `W ⟶ Z ⟶ V₀`, which is `W ⟶ U₀ ⟶ V₀`, and rig-étaleness
descends to `g` (`Rig.isRigEtaleArrow_of_finite_etale_family`). -/
theorem hasPropertyOnEveryAffineEtaleDiagram_of_correspondsToRigEtaleMapAfterSourceCover
    {X Y : FppfSheaf B S hS} (f : X ⟶ Y)
    (hf : CorrespondsToRigEtaleMapAfterSourceCover B S hS f) :
    HasPropertyOnEveryAffineEtaleDiagram B S hS IsNoetherianAdic IsRigEtaleHom f := by
  classical
  let : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
  obtain ⟨I, U, u, hUcover, hfac⟩ := hf
  choose V v t hVaff hVet hsq hcorr using hfac
  intro U₀ V₀ a b τ hU₀ hV₀ ha hb hτ A R _ _ _ _ _ _ _ _ hCA hCR hA D E eU eV g hg
  have : IsNoetherianRing A := hCA.2
  have : IsNoetherianRing R := hCR.2
  have hRw := hCR.1.isWeaklyAdmissible
  -- the charts `Z` of `Vᵢ ×_Y V₀`
  have hφ : ∀ i, IsRepresentableEtale B S hS (pullback.snd (v i) b ≫ eV.hom) := fun i ↦
    (isRepresentableEtale_pullback_snd B S hS (v i) b (hVet i)).comp B S hS
      (isRepresentableEtale_of_isIso B S hS _)
  choose Kz Cz instCz fz hfz Qz gz hgz wz hwz hwzet hZaff hZnoeth hZsurj using fun i ↦
    exists_noetherian_completion_cover_of_isRepresentableEtale B S hS hCA D _ (hφ i)
  -- the map `Uᵢ ×_X U₀ ⟶ Vᵢ ×_Y V₀`
  let π : ∀ i, pullback (u i) a ⟶ pullback (v i) b := fun i ↦
    pullback.lift (pullback.fst (u i) a ≫ t i) (pullback.snd (u i) a ≫ τ) (by
      rw [Category.assoc, Category.assoc, ← hsq i, ← hτ, ← Category.assoc, ← Category.assoc,
        pullback.condition])
  have hπfst : ∀ i, π i ≫ pullback.fst (v i) b = pullback.fst (u i) a ≫ t i := fun i ↦
    pullback.lift_fst _ _ _
  have hπsnd : ∀ i, π i ≫ pullback.snd (v i) b = pullback.snd (u i) a ≫ τ := fun i ↦
    pullback.lift_snd _ _ _
  -- the charts `W` of `Z ×_{Qᵢ} (Uᵢ ×_X U₀)`
  have hψ : ∀ i (k : Kz i), IsRepresentableEtale B S hS
      (pullback.snd (wz i k) (π i) ≫ pullback.snd (u i) a ≫ eU.hom) := fun i k ↦
    (isRepresentableEtale_pullback_snd B S hS (wz i k) (π i) (hwzet i k)).comp B S hS
      ((isRepresentableEtale_pullback_snd B S hS (u i) a (hUcover.2.1 i)).comp B S hS
        (isRepresentableEtale_of_isIso B S hS _))
  choose Kw Cw instCw fw hfw Qw gw hgw ww hww hwwet hWaff hWnoeth hWsurj using fun i k ↦
    exists_noetherian_completion_cover_of_isRepresentableEtale B S hS hCR E _ (hψ i k)
  -- the refined family, indexed by `x = ⟨i, k, l⟩`
  let Ix := Σ i, Σ k : Kz i, Kw i k
  let p : ∀ x : Ix, formalSpectrum (Qw x.1 x.2.1 x.2.2) ⟶ U₀ := fun x ↦
    ww x.1 x.2.1 x.2.2 ≫ pullback.snd (wz x.1 x.2.1) (π x.1) ≫ pullback.snd (u x.1) a
  have hpE : ∀ x : Ix, p x ≫ eU.hom = formalSpectrumMap hRw (gw x.1 x.2.1 x.2.2) := fun x ↦ by
    simp only [p, Category.assoc]
    exact hww x.1 x.2.1 x.2.2
  -- joint surjectivity
  have hsurjP : Sheaf.IsLocallySurjective (Sigma.desc p) := by
    have hstage : ∀ i, Sheaf.IsLocallySurjective (Sigma.desc fun y : Σ k : Kz i, Kw i k ↦
        ww i y.1 y.2 ≫ pullback.snd (wz i y.1) (π i)) := fun i ↦
      isLocallySurjective_sigmaDesc_comp_pullback_snd B S hS (π i) (wz i) (hZsurj i)
        (fun k l ↦ ww i k l) (hWsurj i)
    have h := isLocallySurjective_sigmaDesc_comp_pullback_snd B S hS a u hUcover.2.2
      (K := fun i ↦ Σ k : Kz i, Kw i k)
      (fun i y ↦ ww i y.1 y.2 ≫ pullback.snd (wz i y.1) (π i)) hstage
    simpa only [p, Category.assoc] using h
  have hsurjE : Sheaf.IsLocallySurjective
      (Sigma.desc fun x : Ix ↦ formalSpectrumMap hRw (gw x.1 x.2.1 x.2.2)) := by
    have hfac : Sigma.desc p ≫ eU.hom =
        Sigma.desc fun x : Ix ↦ formalSpectrumMap hRw (gw x.1 x.2.1 x.2.2) :=
      Sigma.hom_ext _ _ fun x ↦ by rw [Sigma.ι_comp_desc_assoc, Sigma.ι_comp_desc, hpE]
    rw [← hfac]
    have := (Sheaf.isLocallySurjective_iff_epi _).1 hsurjP
    exact (Sheaf.isLocallySurjective_iff_epi _).2 (epi_comp _ _)
  obtain ⟨σ, _, kx, hff⟩ := exists_finite_faithfullyFlat_of_isLocallySurjective hRw E
    (fun x : Ix ↦ fw x.1 x.2.1 x.2.2) (fun x ↦ hfw x.1 x.2.1 x.2.2)
    (fun x ↦ Qw x.1 x.2.1 x.2.2) (fun x ↦ gw x.1 x.2.1 x.2.2) (fun x ↦ hgw x.1 x.2.1 x.2.2)
    hsurjE
  -- rig-étaleness of each composite `W ⟶ U₀ ⟶ V₀`
  have hcomp : ∀ x : Ix, HasPropertyOnAffineChartMap B S hS IsNoetherianAdic IsRigEtaleHom
      (p x ≫ τ) := by
    rintro ⟨i, k, l⟩
    let m : formalSpectrum (Qw i k l) ⟶ formalSpectrum (Qz i k) :=
      ww i k l ≫ pullback.fst (wz i k) (π i)
    let r : formalSpectrum (Qz i k) ⟶ V i := wz i k ≫ pullback.fst (v i) b
    let c : formalSpectrum (Qz i k) ⟶ V₀ := wz i k ≫ pullback.snd (v i) b
    let q : formalSpectrum (Qw i k l) ⟶ U i :=
      ww i k l ≫ pullback.snd (wz i k) (π i) ≫ pullback.fst (u i) a
    have hq : IsRepresentableEtale B S hS q :=
      (hwwet i k l).comp B S hS ((isRepresentableEtale_pullback_snd B S hS (wz i k) (π i)
        (hwzet i k)).comp B S hS (isRepresentableEtale_pullback_fst B S hS (u i) a ha))
    have hr : IsRepresentableEtale B S hS r :=
      (hwzet i k).comp B S hS (isRepresentableEtale_pullback_fst B S hS (v i) b hb)
    have hc : IsRepresentableEtale B S hS c :=
      (hwzet i k).comp B S hS (isRepresentableEtale_pullback_snd B S hS (v i) b (hVet i))
    have hqr : q ≫ t i = m ≫ r := by
      simp only [q, m, r, Category.assoc]
      rw [← hπfst, ← reassoc_of% (pullback.condition (f := wz i k) (g := π i))]
    have hpc : p ⟨i, k, l⟩ ≫ τ = m ≫ c := by
      simp only [p, m, c, Category.assoc]
      rw [← hπsnd, ← reassoc_of% (pullback.condition (f := wz i k) (g := π i))]
    obtain ⟨Ai, Ri, _, _, _, _, _, _, _, _, hCAi, hCRi, hAi, Di, Ei, eUi, eVi, gi, hgi, hPi⟩ :=
      hcorr i
    have hm : HasPropertyOnAffineChartMap B S hS IsNoetherianAdic IsRigEtaleHom m :=
      hasPropertyOnAffineChartMap_of_isRepresentableEtale B S hS (t i) m q r (hWaff i k l)
        (hZaff i k) hq hr hqr Ai Ri hCAi hCRi hAi Di Ei eUi eVi gi hgi hPi
    rw [hpc]
    exact hasPropertyOnAffineChartMap_comp_of_isRepresentableEtale B S hS m c (hZaff i k) hc hm
  -- descent along the finite faithfully flat family
  let : ∀ j, Algebra R (Cw (kx j).1 (kx j).2.1 (kx j).2.2) := fun j ↦
    (fw (kx j).1 (kx j).2.1 (kx j).2.2).toAlgebra
  have : ∀ j, Algebra.Etale R (Cw (kx j).1 (kx j).2.1 (kx j).2.2) := fun j ↦
    hfw (kx j).1 (kx j).2.1 (kx j).2.2
  change RingHom.IsRigEtaleArrow g.toRingHom
  refine Rig.isRigEtaleArrow_of_finite_etale_family (σ := σ) hCA hCR g.toRingHom
    g.continuous (fun j : σ ↦ Cw (kx j).1 (kx j).2.1 (kx j).2.2) hff fun j ↦ ?_
  have hsqW : p (kx j) ≫ τ = (Iso.refl _).hom ≫ formalSpectrumMap hA
      (ContinuousHom.comp hRw hA (gw (kx j).1 (kx j).2.1 (kx j).2.2) g) ≫ eV.inv := by
    rw [← formalSpectrumMap_comp_eq hRw hA, Iso.refl_hom, Category.id_comp, ← hpE (kx j), hg]
    simp
  have h : IsRigEtaleHom
      (ContinuousHom.comp hRw hA (gw (kx j).1 (kx j).2.1 (kx j).2.2) g).toRingHom :=
    hcomp (kx j) A _ hCA (hWnoeth (kx j).1 (kx j).2.1 (kx j).2.2) hA D
    (Qw (kx j).1 (kx j).2.1 (kx j).2.2) (Iso.refl _) eV
    (ContinuousHom.comp hRw hA (gw (kx j).1 (kx j).2.1 (kx j).2.2) g) hsqW
  rw [ContinuousHom.comp_toRingHom, hgw] at h
  intro i₁ i₂ i₃ i₄
  exact @h i₁ i₂ i₃ i₄

/-- **Stacks 0GCZ, (3) ⟹ (4).** Composing the coverings of the fibre products `Yⱼ ×_Y X` with
their projections to `X` gives a covering of `X` whose members factor through the charts `Yⱼ`
by the same maps. -/
theorem correspondsToRigEtaleMapAfterSourceCover_of_afterTargetCover {X Y : FppfSheaf B S hS}
    (f : X ⟶ Y) (hf : CorrespondsToRigEtaleMapAfterTargetCover B S hS f) :
    CorrespondsToRigEtaleMapAfterSourceCover B S hS f := by
  let : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
  obtain ⟨J, V, v, ⟨hVaffine, hVetale, hVsurj⟩, hcharts⟩ := hf
  choose I U w hUcover hUproperty using hcharts
  refine ⟨(j : J) × I j, fun p ↦ U p.1 p.2, fun p ↦ w p.1 p.2 ≫ pullback.snd (v p.1) f,
    ⟨fun p ↦ (hUcover p.1).1 p.2, fun p ↦ IsRepresentableEtale.comp B S hS
      ((hUcover p.1).2.1 p.2)
      (isRepresentableEtale_pullback_snd B S hS (v p.1) f (hVetale p.1)), ?_⟩,
    fun p ↦ ⟨V p.1, v p.1, w p.1 p.2 ≫ pullback.fst (v p.1) f, hVaffine p.1, hVetale p.1,
      by rw [Category.assoc, Category.assoc, ← pullback.condition], hUproperty p.1 p.2⟩⟩
  exact isLocallySurjective_sigmaDesc_comp_pullback_snd B S hS f v hVsurj w
    fun j ↦ (hUcover j).2.2

/-- **Stacks 0GCZ, (2) ⟹ (3).** For a morphism of locally Noetherian formal algebraic spaces
satisfying the chart condition, the Noetherian atlas of `Y`, together with, for each of its
members `Yⱼ`, the covering of `Yⱼ ×_Y X` by formal spectra of completed étale algebras over the
members `Xᵢ` of the Noetherian atlas of `X` (charts of `Xᵢ ×_X (Yⱼ ×_Y X)`, Stacks 0AN8), is as
in condition (3): each chart map is a map of formal spectra of Noetherian adic rings, which the
chart condition makes rig-étale. -/
theorem correspondsToRigEtaleMapAfterTargetCover_of_hasPropertyOnEveryAffineEtaleDiagram
    {X Y : FppfSheaf B S hS} (f : X ⟶ Y) (hX : IsLocallyNoetherian B S hS X)
    (hY : IsLocallyNoetherian B S hS Y)
    (hf : HasPropertyOnEveryAffineEtaleDiagram B S hS IsNoetherianAdic IsRigEtaleHom f) :
    CorrespondsToRigEtaleMapAfterTargetCover B S hS f := by
  let : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
  obtain ⟨-, IX, Xi, ui, -, hXet, hXsurj, hXnoeth⟩ := hX
  obtain ⟨-, JY, Yj, vj, hYaff, hYet, hYsurj, hYnoeth⟩ := hY
  refine ⟨JY, Yj, vj, ⟨hYaff, hYet, hYsurj⟩, fun j ↦ ?_⟩
  obtain ⟨-, Aj, _, _, _, _, hApres, hAnoeth, hAadic⟩ := hYnoeth j
  have hPsnd : IsRepresentableEtale B S hS (pullback.snd (vj j) f) :=
    isRepresentableEtale_pullback_snd B S hS (vj j) f (hYet j)
  have hcharts : ∀ i : IX, ∃ (K : Type (u + 1)) (W : K → FppfSheaf B S hS)
      (w : ∀ k, W k ⟶ pullback (ui i) (pullback.snd (vj j) f)),
      (∀ k, IsAffineFormalAlgebraicSpace B S hS (W k)) ∧
      (∀ k, IsRepresentableEtale B S hS (w k)) ∧
      Sheaf.IsLocallySurjective (Sigma.desc w) ∧
      ∀ k, CorrespondsToRigEtaleMap B S hS
        (w k ≫ pullback.snd (ui i) (pullback.snd (vj j) f) ≫ pullback.fst (vj j) f) := by
    intro i
    obtain ⟨-, Ri, _, _, _, _, hRpres, hRnoeth, hRadic⟩ := hXnoeth i
    have hφ : IsRepresentableEtale B S hS
        (pullback.fst (ui i) (pullback.snd (vj j) f) ≫ hRpres.2.some.formalSpectrumIso.hom) :=
      (isRepresentableEtale_pullback_fst B S hS (ui i) _ hPsnd).comp B S hS
        (isRepresentableEtale_of_isIso B S hS _)
    obtain ⟨K, C, _, fk, -, Q, g, -, w, -, hwet, hWaff, hWnoeth, hsurj⟩ :=
      exists_noetherian_completion_cover_of_isRepresentableEtale B S hS ⟨hRadic, hRnoeth⟩
        hRpres.2.some.quotientSystem _ hφ
    refine ⟨K, fun k ↦ formalSpectrum (Q k), w, hWaff, hwet, hsurj, fun k ↦ ?_⟩
    have hsq : (w k ≫ pullback.snd (ui i) (pullback.snd (vj j) f) ≫ pullback.snd (vj j) f) ≫ f =
        (w k ≫ pullback.snd (ui i) (pullback.snd (vj j) f) ≫ pullback.fst (vj j) f) ≫ vj j := by
      simp only [Category.assoc, pullback.condition]
    exact correspondsToRigEtaleMap_of_hasPropertyOnAffineChartMap B S hS
      (hf _ _ _ (vj j) _ (hWaff k) (hYaff j) ((hwet k).comp B S hS
        ((isRepresentableEtale_pullback_snd B S hS (ui i) _ (hXet i)).comp B S hS hPsnd))
        (hYet j) hsq) ⟨hAadic, hAnoeth⟩ (hWnoeth k) hApres.2.some.quotientSystem (Q k)
      (Iso.refl _) hApres.2.some.formalSpectrumIso
  choose K W w hWaff hWet hWsurj hWcorr using hcharts
  refine ⟨(i : IX) × K i, fun x ↦ W x.1 x.2,
    fun x ↦ w x.1 x.2 ≫ pullback.snd (ui x.1) (pullback.snd (vj j) f),
    ⟨fun x ↦ hWaff x.1 x.2, fun x ↦ (hWet x.1 x.2).comp B S hS
      (isRepresentableEtale_pullback_snd B S hS (ui x.1) _ (hXet x.1)), ?_⟩,
    fun x ↦ by simpa only [Category.assoc] using hWcorr x.1 x.2⟩
  exact isLocallySurjective_sigmaDesc_comp_pullback_snd B S hS _ ui hXsurj w hWsurj

/-- **Stacks 0GCZ, with condition (2) read through Definition 0AQM.** Let `f : X ⟶ Y` be a
morphism of locally Noetherian formal algebraic spaces over `S`. The following are equivalent:

1. `f` is rig-étale (Definition 0AQM);
2. for every commutative square with `U`, `V` affine formal algebraic spaces and `U ⟶ X`,
   `V ⟶ Y` representable by algebraic spaces and étale, every presentation of `U ⟶ V` by
   Noetherian adic rings is rig-étale;
3. there exist a covering `{Yⱼ ⟶ Y}` as in Definition 0AIM and for each `j` a covering
   `{Xⱼᵢ ⟶ Yⱼ ×_Y X}` as in Definition 0AIM such that each `Xⱼᵢ ⟶ Yⱼ` corresponds to a
   rig-étale map in `WAdm^{Noeth}`;
4. there exist a covering `{Xᵢ ⟶ X}` as in Definition 0AIM and for each `i` a factorization
   `Xᵢ ⟶ Yᵢ ⟶ Y` where `Yᵢ` is an affine formal algebraic space, `Yᵢ ⟶ Y` is representable by
   algebraic spaces and étale, and `Xᵢ ⟶ Yᵢ` corresponds to a rig-étale map in
   `WAdm^{Noeth}`.

Condition (2) here is the library's reading; the source's, in which `U ⟶ V` corresponds to a
rig-étale map in `WAdm^{Noeth}`, is equivalent to it by Stacks 0AKX, and Stacks 0GCZ with the
source's condition (2) is `AlgebraicGeometry.FormalSpace.isRigEtale_tfae_of_isLocallyNoetherian'`
in `StacksFrontier.AlgebraicGeometry.FormalSpace.RigEtaleLocalCharacterizationCharts`. -/
theorem isRigEtale_tfae_of_isLocallyNoetherian {X Y : FppfSheaf B S hS} (f : X ⟶ Y)
    (hX : IsLocallyNoetherian B S hS X) (hY : IsLocallyNoetherian B S hS Y) :
    List.TFAE
      [IsRigEtale B S hS f,
        HasPropertyOnEveryAffineEtaleDiagram B S hS IsNoetherianAdic IsRigEtaleHom f,
        CorrespondsToRigEtaleMapAfterTargetCover B S hS f,
        CorrespondsToRigEtaleMapAfterSourceCover B S hS f] := by
  tfae_have 1 ↔ 2 := isRigEtale_iff_hasPropertyOnEveryAffineEtaleDiagram B S hS f
  tfae_have 2 → 3 :=
    correspondsToRigEtaleMapAfterTargetCover_of_hasPropertyOnEveryAffineEtaleDiagram B S hS f hX hY
  tfae_have 3 → 4 := correspondsToRigEtaleMapAfterSourceCover_of_afterTargetCover B S hS f
  tfae_have 4 → 2 :=
    hasPropertyOnEveryAffineEtaleDiagram_of_correspondsToRigEtaleMapAfterSourceCover B S hS f
  tfae_finish

end AlgebraicGeometry.FormalSpace

end
