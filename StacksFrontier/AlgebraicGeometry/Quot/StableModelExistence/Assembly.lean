module

public import StacksFrontier.AlgebraicGeometry.Quot.UniqueStableModelsReduction
public import StacksFrontier.AlgebraicGeometry.Quot.StableModelUniqueness
public import StacksFrontier.AlgebraicGeometry.Quot.StableCurveFamilies
public import StacksFrontier.AlgebraicGeometry.Curves.Models.ModelSituation
public import StacksFrontier.AlgebraicGeometry.Curves.Models.MinimalModelMappingProperty
public import StacksFrontier.AlgebraicGeometry.Curves.Models.StableModel.SpecialFibre
public import
  StacksFrontier.AlgebraicGeometry.Curves.Models.StableModel.SpecialFibreIso.BaseChangeSquares
public import StacksFrontier.AlgebraicGeometry.Curves.StableContraction.StableModelUniqueness
public import StacksFrontier.AlgebraicGeometry.Curves.ContractingRationalBridges.Terminal
public import StacksFrontier.AlgebraicGeometry.SemistableReduction.NodalResolution
public import
  StacksFrontier.AlgebraicGeometry.Quot.StableModelExistence.ExceptionalContractionSpecialFibre
public import StacksFrontier.AlgebraicGeometry.Quot.StableModelExistence.StableFibres
public import StacksFrontier.AlgebraicGeometry.Quot.StableModelExistence.CurveFacts
public import StacksFrontier.AlgebraicGeometry.Quot.StableModelExistence.NodalResolutionModel
public import StacksFrontier.AlgebraicGeometry.Quot.StableModelExistence.SpecialFibreDescent

/-!
# Existence of the isomorphism of stable models (Stacks 0E97), assembled from its steps

Let `R` be a discrete valuation ring with fraction field `K`, `C` a smooth curve over `K` and `X`,
`X'` models of `C` which are stable families of curves of genus `g` over `R`. The proof of
[Stacks, Tag 0E97] produces an isomorphism of models `X ≅ X'` through the minimal model `Y` of
`C` and its contraction `Y ⟶ Z` onto a stable family: every stable model `X` is isomorphic to `Z`
as a model. For this, `X` is resolved by blowups `X_m ⟶ X` (Stacks 0CDE), `X_m` maps to `Y` by
contractions of exceptional curves (Stacks 0C9Z), and both `X_{m,s} ⟶ X_s` and
`X_{m,s} ⟶ Y_s ⟶ Z_s` are the stable contraction of the special fibre `X_{m,s}`
(Stacks 0E7Q), so that Stacks 0E89 identifies `X` with `Z`.

This file proves `AlgebraicGeometry.ExistsIsoOfStableModels` from seven statements, each a step
of that proof, named `Stacks.Models.StableModelExistence.Input1` to `Input7` (the fourth in two
parts), and proves all of them except `Input2` and `Input5` from the modules of this directory.
It is UNREGISTERED: it carries no `stacks` attribute.

## Main definitions

* `Stacks.Models.StableModelExistence.Input1`: Stacks 0E89 over a discrete valuation ring.
* `Stacks.Models.StableModelExistence.Input2`: `𝒪 = h_*𝒪` and `R¹h_*𝒪 = 0` on the special fibre
  of a chain of blowups at singular points.
* `Stacks.Models.StableModelExistence.Input3`: `𝒪 = g_*𝒪` and `Rⁱg_*𝒪 = 0` on the special fibre
  of a sequence of contractions of exceptional curves.
* `Stacks.Models.StableModelExistence.Input4a`, `Input4b`: the special fibre of a stable family,
  and of a proper at-worst-nodal family.
* `Stacks.Models.StableModelExistence.Input5`: the contraction of a minimal at-worst-nodal model
  onto a stable model.
* `Stacks.Models.StableModelExistence.Input6`: the curve facts for the generic fibre of a stable
  model.
* `Stacks.Models.StableModelExistence.Input7`: the regular resolution of a nodal proper model.

## Main results

* `Stacks.Models.StableModelExistence.exists_iso_isModelHom_of_isStableFamily`: every stable
  model of `C` is isomorphic as a model to the contraction `Z` of the minimal model.
* `AlgebraicGeometry.existsIsoOfStableModels_of`: `ExistsIsoOfStableModels` from the inputs.
* `Stacks.Models.StableModelExistence.input1`, `input3`, `input4a`, `input4b`, `input6`,
  `input7`: those inputs hold.
* `AlgebraicGeometry.existsIsoOfStableModels_of_input2_input5`: `ExistsIsoOfStableModels` from
  `Input2` and `Input5`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.Models.StableModelExistence

/-! ### The inputs -/

/-- **Input 1: Stacks 0E89 over a discrete valuation ring.** Let `W`, `X`, `X'` be proper models
of `V` and `c : W ⟶ X`, `c' : W ⟶ X'` morphisms of models. If the special fibres `Xₛ`, `X'ₛ` are
identified over `κ` by an isomorphism `φ` with `cₛ ≫ φ = c'ₛ`, `𝒪_{Xₛ} ⟶ cₛ,* 𝒪_{Wₛ}` is an
isomorphism, `R¹cₛ,* 𝒪_{Wₛ} = 0` and `Wₛ` has dimension at most one, then there is a unique
isomorphism of models `X ≅ X'`. -/
def Input1 : Prop :=
  ∀ (R K : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K]
    [IsFractionRing R K] {V W X X' : Scheme.{u}} {v : V ⟶ Spec (.of K)}
    {pW : W ⟶ Spec (.of R)} {p : X ⟶ Spec (.of R)} {p' : X' ⟶ Spec (.of R)}
    {eW : V ≅ pullback pW (genericPointInclusion R K)}
    {e : V ≅ pullback p (genericPointInclusion R K)}
    {e' : V ≅ pullback p' (genericPointInclusion R K)},
    IsModel v pW eW → IsModel v p e → IsModel v p' e' →
    ∀ [IsProper pW] [IsProper p] [IsProper p'] {c : W ⟶ X} {c' : W ⟶ X'}
      (hcX : IsModelHom pW p eW e c) (hcX' : IsModelHom pW p' eW e' c')
      (φ : pullback p (ContractionUniquenessComplete.closedPoint R) ≅
        pullback p' (ContractionUniquenessComplete.closedPoint R)),
      φ.hom ≫ pullback.snd _ _ = pullback.snd _ _ →
      ContractionUniquenessComplete.specialMap pW p c hcX.1 ≫ φ.hom =
        ContractionUniquenessComplete.specialMap pW p' c' hcX'.1 →
      IsIso (C := (pullback p (ContractionUniquenessComplete.closedPoint R)).Modules)
        (Scheme.Modules.unitToPushforwardUnit
          (ContractionUniquenessComplete.specialMap pW p c hcX.1)) →
      IsZero (((Scheme.Modules.pushforward
          (ContractionUniquenessComplete.specialMap pW p c hcX.1)).rightDerived 1).obj
        (SheafOfModules.unit
          (pullback pW (ContractionUniquenessComplete.closedPoint R)).ringCatSheaf)) →
      topologicalKrullDim ↥(pullback pW (ContractionUniquenessComplete.closedPoint R)) ≤ 1 →
      ∃! f : X ≅ X', IsModelHom p p' e e' f.hom

/-- **Input 2: the special fibre of a chain of blowups at singular points.** For a proper
at-worst-nodal `f : X ⟶ Spec R` with smooth generic fibre and a chain of blowups `h : Y ⟶ X` at
singular closed points (Stacks 0CDE), the special fibre `hₛ` satisfies `𝒪 = hₛ,*𝒪` and
`R¹hₛ,*𝒪 = 0`. -/
def Input2 : Prop :=
  ∀ (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of R)) [IsProper f], IsAtWorstNodalOfRelativeDimensionOne f →
    Smooth (f.fiberToSpecResidueField (⊥ : PrimeSpectrum R)) →
    ∀ {Y : Scheme.{u}} {h : Y ⟶ X}, Stacks.SemistableReduction.NodalBlowupChain f Y h →
      IsIso (SheafOfModules.unitToPushforwardObjUnit
        (ContractionUniquenessComplete.specialMap (h ≫ f) f h rfl).toRingCatSheafHom) ∧
      IsZero (((Scheme.Modules.pushforward
          (ContractionUniquenessComplete.specialMap (h ≫ f) f h rfl)).rightDerived 1).obj
        (SheafOfModules.unit
          (pullback (h ≫ f) (ContractionUniquenessComplete.closedPoint R)).ringCatSheaf))

/-- **Input 3: the special fibre of a sequence of contractions of exceptional curves.** For a
sequence `g : Y ⟶ X` of contractions of exceptional curves of the first kind (Stacks 0CD9) whose
source is a regular proper model of `C`, at-worst-nodal over `R`, the special fibre `gₛ` satisfies
`𝒪 = gₛ,*𝒪` and `Rⁱgₛ,*𝒪 = 0` for `i > 0`. This is proved as
`Stacks.Models.StableModelExistence.input3`. -/
def Input3 : Prop :=
  ∀ (R K : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K]
    [IsFractionRing R K] {C X Y : Scheme.{u}} {c : C ⟶ Spec (.of K)} [IsCurve K c] [Smooth c]
    {q : Y ⟶ Spec (.of R)} {p : X ⟶ Spec (.of R)} {g : Y ⟶ X}
    (hs : ExceptionalContractionSequence c q p g) [IsProper q],
    IsAtWorstNodalOfRelativeDimensionOne q → Stacks.HProjective.IsHProjective c →
    ∀ [IsIso ((Scheme.ΓSpecIso (.of K)).inv ≫ c.appTop)]
      (eY : C ≅ pullback q (Spec.map (CommRingCat.ofHom (algebraMap R K)))),
    IsModel c q eY → IsRegular Y →
    (ContractionUniquenessComplete.specialMap q p g
      (comp_eq_of_exceptionalContractionSequence hs)).IsStructurallyAcyclic

/-- **Input 4 (a): the special fibre of a stable family.** The special fibre of a stable family
of curves of genus `g` over `R` has genus at least two, no rational tails and no rational
bridges, and `H⁰(Xₛ, 𝒪) = κ`. -/
def Input4a : Prop :=
  ∀ (B : BigFppfSite.{u}) (hZ : B.Contains integerBase) (g : ℕ) (R : Type u) [CommRing R]
    [IsDomain R] [IsDiscreteValuationRing R] (hR : B.Contains (Spec (.of R))) {X : Scheme.{u}}
    {p : X ⟶ Spec (.of R)}, IsStableFamilyOfSchemesOfGenus B hZ g p hR →
    HasGenusTwoNoRationalTailNoRationalBridge (IsLocalRing.ResidueField R)
        (pullback.snd p (ContractionUniquenessComplete.closedPoint R)) ∧
      IsIso ((Scheme.ΓSpecIso (.of (IsLocalRing.ResidueField R))).inv ≫
        (pullback.snd p (ContractionUniquenessComplete.closedPoint R)).appTop)

/-- **Input 4 (b): the special fibre of a proper at-worst-nodal family.** If `p : X ⟶ Spec R` is
proper and at-worst-nodal of relative dimension one and its special fibre is nonempty, the
special fibre is proper of dimension one over `κ` with at-worst-nodal singularities, and `X` is
quasi-compact. -/
def Input4b : Prop :=
  ∀ (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] {X : Scheme.{u}}
    (p : X ⟶ Spec (.of R)) [IsProper p], IsAtWorstNodalOfRelativeDimensionOne p →
    Nonempty ↥(pullback p (ContractionUniquenessComplete.closedPoint R)) →
    IsProper (pullback.snd p (ContractionUniquenessComplete.closedPoint R)) ∧
      topologicalKrullDim ↥(pullback p (ContractionUniquenessComplete.closedPoint R)) = 1 ∧
      (letI : (pullback p (ContractionUniquenessComplete.closedPoint R)).Over
          (Spec (.of (IsLocalRing.ResidueField R))) :=
          ⟨pullback.snd p (ContractionUniquenessComplete.closedPoint R)⟩;
        Stacks.Curves.HasAtWorstNodalSingularities (IsLocalRing.ResidueField R)
          (pullback p (ContractionUniquenessComplete.closedPoint R))) ∧
      CompactSpace X

/-- **Input 5: the contraction of a minimal model onto a stable model** (Stacks 0E8A over a
discrete valuation ring). A minimal model `Y` of `C`, at-worst-nodal of relative dimension one,
maps by a morphism of models `cZ : Y ⟶ Z` to a proper model `Z` such that `cZ,ₛ` is a stable
contraction of `Yₛ` (Stacks 0E7Q). -/
def Input5 : Prop :=
  ∀ (R K : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K]
    [IsFractionRing R K] {C Y : Scheme.{u}} (c : C ⟶ Spec (.of K)) [IsCurve K c] [Smooth c]
    (_hc : IsProjective c) [IsIso ((Scheme.ΓSpecIso (.of K)).inv ≫ c.appTop)],
    2 ≤ genus c → ∀ (p : Y ⟶ Spec (.of R))
      (e : C ≅ pullback p (Spec.map (CommRingCat.ofHom (algebraMap R K)))),
    IsMinimalModel c p e → IsAtWorstNodalOfRelativeDimensionOne p →
    ∃ (Z : Scheme.{u}) (pZ : Z ⟶ Spec (.of R))
      (eZ : C ≅ pullback pZ (Spec.map (CommRingCat.ofHom (algebraMap R K))))
      (cZ : Y ⟶ Z) (hcZ : cZ ≫ pZ = p),
      IsModel c pZ eZ ∧ IsProper pZ ∧ IsModelHom p pZ e eZ cZ ∧
        Stacks.Curves.StableModel.IsStableContraction
          (pullback.snd p (ContractionUniquenessComplete.closedPoint R))
          (pullback.snd pZ (ContractionUniquenessComplete.closedPoint R))
          (ContractionUniquenessComplete.specialMap p pZ cZ hcZ)

/-- **Input 6: the generic fibre of a stable model.** If a smooth `K`-scheme `C` is the generic
fibre of a model `X` which is a stable family of curves of genus `g`, then `C` is a proper
projective curve with `H⁰(C, 𝒪_C) = K` and genus at least two, and the generic fibre of `X` is
smooth. -/
def Input6 : Prop :=
  ∀ (B : BigFppfSite.{u}) (hZ : B.Contains integerBase) (g : ℕ) (R K : Type u) [CommRing R]
    [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K]
    (hR : B.Contains (Spec (.of R))) {C : Scheme.{u}} (C_to_K : C ⟶ Spec (.of K))
    [Smooth C_to_K] {X : Scheme.{u}} {p : X ⟶ Spec (.of R)}
    {e : C ≅ pullback p (Spec.map (CommRingCat.ofHom (algebraMap R K)))},
    IsModel C_to_K p e → IsStableFamilyOfSchemesOfGenus B hZ g p hR →
    IsCurve K C_to_K ∧ IsProper C_to_K ∧ IsIso ((Scheme.ΓSpecIso (.of K)).inv ≫ C_to_K.appTop) ∧
      IsProjective C_to_K ∧ Stacks.HProjective.IsHProjective C_to_K ∧ 2 ≤ genus C_to_K ∧
      Smooth (p.fiberToSpecResidueField (⊥ : PrimeSpectrum R))

/-- **Input 7: the regular resolution of a nodal proper model** (Stacks 0CDE). A proper model
`X` of `C`, at-worst-nodal of relative dimension one with smooth generic fibre, receives a chain
of blowups at singular points `h : Y ⟶ X` with `Y` regular and proper over `R`, which is a
morphism of models. -/
def Input7 : Prop :=
  ∀ (R K : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K]
    [IsFractionRing R K] {C X : Scheme.{u}} (c : C ⟶ Spec (.of K)) [Smooth c]
    (f : X ⟶ Spec (.of R)) [IsProper f], IsAtWorstNodalOfRelativeDimensionOne f →
    ∀ (e : C ≅ pullback f (Spec.map (CommRingCat.ofHom (algebraMap R K)))), IsModel c f e →
    ∀ [CompactSpace X], Smooth (f.fiberToSpecResidueField (⊥ : PrimeSpectrum R)) →
    ∃ (Y : Scheme.{u}) (h : Y ⟶ X), Stacks.SemistableReduction.NodalBlowupChain f Y h ∧
      IsRegular Y ∧ IsProper (h ≫ f) ∧
      ∃ eY : C ≅ pullback (h ≫ f) (Spec.map (CommRingCat.ofHom (algebraMap R K))),
        IsModel c (h ≫ f) eY ∧ IsModelHom (h ≫ f) f eY e h

/-! ### General lemmas -/

section Lemmas

variable {R K : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field K] [Algebra R K] [IsFractionRing R K]

omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K] in
/-- **The inverse of an isomorphism of models is a morphism of models.** -/
theorem isModelHom_inv {V X X' : Scheme.{u}} {p : X ⟶ Spec (.of R)} {p' : X' ⟶ Spec (.of R)}
    {e : V ≅ pullback p (genericPointInclusion R K)}
    {e' : V ≅ pullback p' (genericPointInclusion R K)} {f : X ≅ X'}
    (hf : IsModelHom p p' e e' f.hom) : IsModelHom p' p e' e f.inv :=
  IsModelHom.of_comp_eq hf (isModelHom_id p e) (by rw [← hf.1, Iso.inv_hom_id_assoc])
    f.hom_inv_id

omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K] in
/-- **A morphism over `R` between models compatible with the first projections of the generic
fibres is a morphism of models**: the second projections agree since both identifications are
over `K`. -/
theorem isModelHom_of_comp_fst {V X X' : Scheme.{u}} {v : V ⟶ Spec (.of K)}
    {p : X ⟶ Spec (.of R)} {p' : X' ⟶ Spec (.of R)}
    {e : V ≅ pullback p (genericPointInclusion R K)}
    {e' : V ≅ pullback p' (genericPointInclusion R K)} (hX : IsModel v p e)
    (hX' : IsModel v p' e') {φ : X ⟶ X'} (hφ : φ ≫ p' = p)
    (hfst : e.hom ≫ pullback.fst p (genericPointInclusion R K) ≫ φ =
      e'.hom ≫ pullback.fst p' (genericPointInclusion R K)) :
    IsModelHom p p' e e' φ := by
  refine ⟨hφ, ?_⟩
  apply pullback.hom_ext
  · simp only [genericFiberMapOfHomOver, Category.assoc, pullback.lift_fst]
    exact hfst
  · simp only [genericFiberMapOfHomOver, Category.assoc, pullback.lift_snd, Category.comp_id]
    exact hX.2.2.2.trans hX'.2.2.2.symm

end Lemmas

/-! ### Every stable model is isomorphic to the contraction of the minimal model -/

/-- **Every stable model is isomorphic to the contraction of the minimal model** (the claim in
the proof of Stacks 0E97). Let `Y` be a minimal model of `C` and `cZ : Y ⟶ Z` a morphism of models
onto a proper model `Z` whose special fibre is a stable contraction. Then every model `X` of `C`
which is a stable family of curves is isomorphic to `Z` as a model. -/
theorem exists_iso_isModelHom_of_isStableFamily (h1 : Input1.{u}) (h2 : Input2.{u})
    (h3 : Input3.{u}) (h4a : Input4a.{u}) (h4b : Input4b.{u}) (h7 : Input7.{u})
    (B : BigFppfSite.{u}) (hZ : B.Contains integerBase) (g : ℕ)
    (R K : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K]
    [IsFractionRing R K] (hR : B.Contains (Spec (.of R))) {C : Scheme.{u}}
    (C_to_K : C ⟶ Spec (.of K)) [IsCurve K C_to_K] [Smooth C_to_K]
    [IsIso ((Scheme.ΓSpecIso (.of K)).inv ≫ C_to_K.appTop)]
    (hproj : Stacks.HProjective.IsHProjective C_to_K) (hg2 : 2 ≤ genus C_to_K)
    {Y : Scheme.{u}} {pY : Y ⟶ Spec (.of R)}
    {eY : C ≅ pullback pY (Spec.map (CommRingCat.ofHom (algebraMap R K)))}
    (hmin : IsMinimalModel C_to_K pY eY)
    {Z : Scheme.{u}} {pZ : Z ⟶ Spec (.of R)}
    {eZ : C ≅ pullback pZ (Spec.map (CommRingCat.ofHom (algebraMap R K)))} {cZ : Y ⟶ Z}
    (hcZ : cZ ≫ pZ = pY) (hZmod : IsModel C_to_K pZ eZ) [IsProper pZ]
    (hcZm : IsModelHom pY pZ eY eZ cZ)
    (hcZs : Stacks.Curves.StableModel.IsStableContraction
      (pullback.snd pY (ContractionUniquenessComplete.closedPoint R))
      (pullback.snd pZ (ContractionUniquenessComplete.closedPoint R))
      (ContractionUniquenessComplete.specialMap pY pZ cZ hcZ))
    {X : Scheme.{u}} {p : X ⟶ Spec (.of R)}
    {e : C ≅ pullback p (Spec.map (CommRingCat.ofHom (algebraMap R K)))}
    (hmod : IsModel C_to_K p e) (hst : IsStableFamilyOfSchemesOfGenus B hZ g p hR)
    (hsm : Smooth (p.fiberToSpecResidueField (⊥ : PrimeSpectrum R))) :
    ∃ f : X ≅ Z, IsModelHom p pZ e eZ f.hom := by
  have : IsProper p := hst.isProper
  have hnod : IsAtWorstNodalOfRelativeDimensionOne p :=
    hst.isStableFamilyOfSchemes.isAtWorstNodalOfRelativeDimensionOne fun _ hF => hF.1
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace p
  -- the regular resolution `h : X_m ⟶ X` (Stacks 0CDE)
  obtain ⟨Xm, h, hchain, hreg, hqprop, eXm, hXmmod, hhm⟩ := h7 R K C_to_K p hnod e hmod hsm
  have := hqprop
  have hqnod := hchain.isAtWorstNodalOfRelativeDimensionOne hnod
  -- the morphism `X_m ⟶ Y` to the minimal model (Stacks 0C9Z)
  have := hmin.isProper
  obtain ⟨φY, ⟨hφYp, hφYc⟩, X₀, p₀, g₀, ψ, hseq, hψp, hgψ⟩ :=
    (existsUnique_exceptionalContractionSequence_of_isMinimalModel C_to_K (by omega) pY eY hmin
      (h ≫ p) eXm hXmmod hreg).exists
  have hφYm : IsModelHom (h ≫ p) pY eXm eY φY :=
    isModelHom_of_comp_fst hXmmod hmin.isModel hφYp hφYc
  have hc'm : IsModelHom (h ≫ p) pZ eXm eZ (φY ≫ cZ) := hφYm.comp hcZm
  have hg₀p : g₀ ≫ p₀ = h ≫ p := comp_eq_of_exceptionalContractionSequence hseq
  have : IsProper p₀ := by rw [← hψp]; infer_instance
  -- the special fibre of `X_m`
  let S := regularProperModelSituation C_to_K hproj (h ≫ p) eXm hXmmod hreg
  have hneM : Nonempty ↥(pullback (h ≫ p) (ContractionUniquenessComplete.closedPoint R)) :=
    S.nonempty_specialFiber
  have hdimM : topologicalKrullDim
      ↥(pullback (h ≫ p) (ContractionUniquenessComplete.closedPoint R)) = 1 :=
    S.topologicalKrullDim_specialFiber S.nonempty_specialFiber
  have hglobM : IsIso ((Scheme.ΓSpecIso (.of (IsLocalRing.ResidueField R))).inv ≫
      (pullback.snd (h ≫ p) (ContractionUniquenessComplete.closedPoint R)).appTop) :=
    S.isIso_globalSections_specialFiber_of_isAtWorstNodal hqnod
  have hnodalM :=
    S.hasAtWorstNodalSingularities_specialFiber_of_isAtWorstNodal hqnod
  have := S.isIso_globalSections_specialFiber_of_isAtWorstNodal hqnod
  have hgenM : genus (pullback.snd (h ≫ p) (ContractionUniquenessComplete.closedPoint R)) =
      genus C_to_K :=
    S.genus_specialFiber_eq_of_eulerCharacteristic_eq S.eulerCharacteristic_C_eq_specialFiber
  -- the special fibre of `X`
  have hneX : Nonempty ↥(pullback p (ContractionUniquenessComplete.closedPoint R)) :=
    ⟨ContractionUniquenessComplete.specialMap (h ≫ p) p h rfl hneM.some⟩
  obtain ⟨hXsprop, hXsdim, hXsnodal, -⟩ := h4b R p hnod hneX
  obtain ⟨⟨hXsg, hXstail, hXsprop', hXsbridge⟩, hXsglob⟩ := h4a B hZ g R hR hst
  have := hXsprop
  have := hXsglob
  -- `hₛ` is a stable contraction of `X_{m,s}` onto `Xₛ`
  obtain ⟨hA0, hA1⟩ := h2 R p hnod hsm hchain
  have hid := (IsIteratedContractionOfRationalBridges.identity
    (k := IsLocalRing.ResidueField R) _
    (pullback.snd p (ContractionUniquenessComplete.closedPoint R))).isStableContraction
    hXsdim hXsnodal hXstail hXsg (fun C _ => hXsbridge C)
  have hXs : Stacks.Curves.StableModel.IsStableContraction
      (pullback.snd (h ≫ p) (ContractionUniquenessComplete.closedPoint R))
      (pullback.snd p (ContractionUniquenessComplete.closedPoint R))
      (ContractionUniquenessComplete.specialMap (h ≫ p) p h rfl) :=
    { comp_eq := ContractionUniquenessComplete.specialMap_snd _ _ _ _
      isProper := hXsprop
      topologicalKrullDim_eq := hXsdim
      hasAtWorstNodalSingularities := hXsnodal
      isIso_unitToPushforwardObjUnit := hA0
      isZero_rightDerived_one := hA1
      isAmple := hid.isAmple }
  -- `(X_m ⟶ Y ⟶ Z)ₛ` is a stable contraction of `X_{m,s}` onto `Zₛ`
  obtain ⟨hB0, hB⟩ := h3 R K hseq hqnod hproj eXm hXmmod hreg
  have hψa := Scheme.Hom.isStructurallyAcyclic_of_isIso
    (ContractionUniquenessComplete.specialMap p₀ pY ψ.hom hψp)
  have hψs := Stacks.Curves.StableModel.IsStableContraction.comp
    (ContractionUniquenessComplete.specialMap p₀ pY ψ.hom hψp) _
    (ContractionUniquenessComplete.specialMap_snd _ _ _ _) hψa.1 hψa.2 hcZs
  have : IsProper (ContractionUniquenessComplete.specialMap (h ≫ p) p₀ g₀ hg₀p) := by
    have : ContractionUniquenessComplete.specialMap (h ≫ p) p₀ g₀ hg₀p ≫
        pullback.snd p₀ (ContractionUniquenessComplete.closedPoint R) =
        pullback.snd (h ≫ p) (ContractionUniquenessComplete.closedPoint R) :=
      ContractionUniquenessComplete.specialMap_snd _ _ _ _
    have : IsProper (ContractionUniquenessComplete.specialMap (h ≫ p) p₀ g₀ hg₀p ≫
        pullback.snd p₀ (ContractionUniquenessComplete.closedPoint R)) := by
      rw [this]; infer_instance
    exact IsProper.of_comp _ (pullback.snd p₀ (ContractionUniquenessComplete.closedPoint R))
  have hc's := Stacks.Curves.StableModel.IsStableContraction.comp
    (ContractionUniquenessComplete.specialMap (h ≫ p) p₀ g₀ hg₀p) _
    (ContractionUniquenessComplete.specialMap_snd _ _ _ _) hB0 hB hψs
  subst hgψ
  have hgψp : (g₀ ≫ ψ.hom) ≫ pY = h ≫ p := by rw [Category.assoc, hψp, hg₀p]
  have hc'eq : ContractionUniquenessComplete.specialMap (h ≫ p) pZ ((g₀ ≫ ψ.hom) ≫ cZ) hc'm.1 =
      ContractionUniquenessComplete.specialMap (h ≫ p) p₀ g₀ hg₀p ≫
        ContractionUniquenessComplete.specialMap p₀ pY ψ.hom hψp ≫
          ContractionUniquenessComplete.specialMap pY pZ cZ hcZ := by
    rw [ContractionUniquenessComplete.specialMap_comp (h ≫ p) pY pZ (g₀ ≫ ψ.hom) cZ hgψp hcZ,
      ContractionUniquenessComplete.specialMap_comp (h ≫ p) p₀ pY g₀ ψ.hom hg₀p hψp,
      Category.assoc]
  rw [← hc'eq] at hc's
  -- the two stable contractions of `X_{m,s}` are isomorphic (Stacks 0E7Q)
  obtain ⟨φ, hφc, -⟩ := Stacks.Curves.StableModel.existsUnique_iso_of_isStableContraction
    (pullback.snd (h ≫ p) (ContractionUniquenessComplete.closedPoint R)) hdimM
    (hgenM ▸ hg2) hnodalM hXs hc's
  have hφ : φ.hom ≫ pullback.snd pZ (ContractionUniquenessComplete.closedPoint R) =
      pullback.snd p (ContractionUniquenessComplete.closedPoint R) := by
    refine hXs.ext (gY' := 𝟙 _) ?_
    rw [reassoc_of% hφc, ContractionUniquenessComplete.specialMap_snd,
      ContractionUniquenessComplete.specialMap_snd]
  -- Stacks 0E89
  obtain ⟨f, hf, -⟩ := h1 R K hXmmod hmod hZmod hhm hc'm φ hφ hφc hA0 hA1 hdimM.le
  exact ⟨f, hf⟩

/-! ### The inputs that hold -/

/-- `Input1` holds: `Stacks.Models.existsUnique_isModelHom_iso_of_specialFibre`. -/
theorem input1 : Input1.{u} := by
  intro R K _ _ _ _ _ _ V W X X' v pW p p' eW e e' hW hX hX' _ _ _ c c' hcX hcX' φ hφ hφc h0 hR
    hdim
  exact existsUnique_isModelHom_iso_of_specialFibre hW hX hX' hcX hcX' φ hφ hφc h0 hR hdim

/-- `Input3` holds: `Stacks.Models.ExceptionalContractionSequence.acyc_specialMap`. -/
theorem input3 : Input3.{u} := by
  intro R K _ _ _ _ _ _ C X Y c _ _ q p g hs _ hnod hproj _ eY hmod hreg
  exact hs.acyc_specialMap hnod hproj eY hmod hreg

/-- `Input4a` holds: `AlgebraicGeometry.IsStableFamilyOfSchemesOfGenus.specialFibre`. -/
theorem input4a : Input4a.{u} := by
  intro B hZ g R _ _ _ hR X p hst
  exact hst.specialFibre

/-- `Input4b` holds: `Stacks.Models.specialFibre_standing_of_isAtWorstNodal`. -/
theorem input4b : Input4b.{u} := by
  intro R _ _ _ X p _ hnod hne
  exact specialFibre_standing_of_isAtWorstNodal p hnod

/-- `Input6` holds: `Stacks.Models.curveFacts_of_isStableFamilyOfSchemesOfGenus`. -/
theorem input6 : Input6.{u} := by
  intro B hZ g R K _ _ _ _ _ _ hR C C_to_K _ X p e hmod hst
  exact curveFacts_of_isStableFamilyOfSchemesOfGenus C_to_K hmod hst

/-- `Input7` holds: `Stacks.SemistableReduction.exists_nodalBlowupChain_isRegular_isModelHom`. -/
theorem input7 : Input7.{u} := by
  intro R K _ _ _ _ _ _ C X c _ f _ hf e hmod _ hsm
  exact Stacks.SemistableReduction.exists_nodalBlowupChain_isRegular_isModelHom c f hf e hmod hsm

end Stacks.Models.StableModelExistence

open Stacks.Models.StableModelExistence in
/-- **The existence half of Stacks 0E97, from its steps.** `ExistsIsoOfStableModels` follows from
`Input1` to `Input7`: both stable models are isomorphic as models to the contraction `Z` of the
minimal model of `C`. -/
theorem AlgebraicGeometry.existsIsoOfStableModels_of (B : BigFppfSite.{u})
    (hZ : B.Contains integerBase) (g : ℕ) (h1 : Input1.{u}) (h2 : Input2.{u}) (h3 : Input3.{u})
    (h4a : Input4a.{u}) (h4b : Input4b.{u}) (h5 : Input5.{u}) (h6 : Input6.{u})
    (h7 : Input7.{u}) : ExistsIsoOfStableModels B hZ g := by
  intro R _ _ _ K _ _ _ hR C C_to_K _ X X' p p' e e' hX hX' hst hst'
  obtain ⟨hcurve, -, hH0, hprojC, hhproj, hg2, hsm⟩ := h6 B hZ g R K hR C_to_K hX hst
  have hsm' := (h6 B hZ g R K hR C_to_K hX' hst').2.2.2.2.2.2
  have := hcurve
  have := hH0
  -- the minimal model, at-worst-nodal (Stacks 0C2W, 0CDG)
  have hss : Stacks.Models.HasSemistableReduction R C_to_K hprojC :=
    ⟨X, p, e, hX, hst.isProper,
      hst.isStableFamilyOfSchemes.isAtWorstNodalOfRelativeDimensionOne fun _ hF => hF.1⟩
  obtain ⟨Y, pY, eY, hmin, hnodY⟩ :=
    ((Stacks.Models.tfae_hasSemistableReduction (R := R) C_to_K hprojC).out 1 2).mp hss
  -- its contraction onto a stable model (Stacks 0E8A)
  obtain ⟨Z, pZ, eZ, cZ, hcZ, hZmod, hZprop, hcZm, hcZs⟩ :=
    h5 R K C_to_K hprojC hg2 pY eY hmin hnodY
  have := hZprop
  obtain ⟨f, hf⟩ := exists_iso_isModelHom_of_isStableFamily h1 h2 h3 h4a h4b h7 B hZ g R K hR
    C_to_K hhproj hg2 hmin hcZ hZmod hcZm hcZs hX hst hsm
  obtain ⟨f', hf'⟩ := exists_iso_isModelHom_of_isStableFamily h1 h2 h3 h4a h4b h7 B hZ g R K hR
    C_to_K hhproj hg2 hmin hcZ hZmod hcZm hcZs hX' hst' hsm'
  exact ⟨f ≪≫ f'.symm, hf.comp (isModelHom_inv hf')⟩


open Stacks.Models.StableModelExistence in
/-- **The existence half of Stacks 0E97, from the special fibre of the regular resolution and
the contraction onto a stable model.** `ExistsIsoOfStableModels` follows from `Input2` and
`Input5`, the other inputs being proved. -/
theorem AlgebraicGeometry.existsIsoOfStableModels_of_input2_input5 (B : BigFppfSite.{u})
    (hZ : B.Contains integerBase) (g : ℕ) (h2 : Input2.{u}) (h5 : Input5.{u}) :
    ExistsIsoOfStableModels B hZ g :=
  existsIsoOfStableModels_of B hZ g input1 h2 input3 input4a input4b h5 input6 input7

end
