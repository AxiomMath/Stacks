module

public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedFunctorInjective
public import StacksFrontier.Algebra.Homology.Resolution.NatIntBridge
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.AmbientRestrictionDerived
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.AmbientTensorFormsIso
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.Proposition07LM
public import StacksCore.Tactic.StacksAttribute

/-!
# [Stacks, Equation 07LP]: `RΓ(Cris(X/S), F) ⟶ RΓ(T, F_T ⊗_{𝒪_T} Ω^*_{T/S,δ})`

In Situation 07MF, let `F` be a crystal in quasi-coherent modules on `Cris(X/S)` and let
`(U, T, δ)` be an object of `Cris(X/S)`.  [Stacks, Tag 07LM] allows one to construct a canonical
map

`RΓ(Cris(X/S), F) ⟶ RΓ(T, F_T ⊗_{𝒪_T} Ω^*_{T/S,δ})`.

Namely `RΓ(Cris(X/S), F) = RΓ(Cris(X/S), F ⊗ Ω^*_{X/S})`, one can restrict global cohomology
classes to `T`, and `Ω_{X/S}` restricts to `Ω_{T/S,δ}` by [Stacks, Tag 07IZ].  This file carries
out that construction.

## The three steps

1. `RΓ(Cris(X/S), F) ≅ RΓ(Cris(X/S), F ⊗ Ω^*_{X/S})`: the truncation map
   `F ⊗ Ω^*_{X/S} ⟶ F[0]` becomes an isomorphism after `Ru_{X/S, *}` by [Stacks, Tag 07LM], hence
   after `RΓ(Cris(X/S), -) = RΓ(X_Zar, -) ∘ Ru_{X/S, *}`; the identification is the inverse of its
   image (`CrystalDeRhamSheafData.derivedGlobalSectionsIsoDeRham`).
2. The restriction of global cohomology classes to `T`,
   `RΓ(Cris(X/S), K) ⟶ RΓ(T, K_T)` for the complex `K = F ⊗ Ω^*_{X/S}`
   (`...SmallSite.CrystallineThickening.derivedGlobalSectionsToAmbient`).
3. The identification `(F ⊗ Ω^*_{X/S})_T ≅ F_T ⊗_{𝒪_T} Ω^*_{T/S,δ}` of complexes of abelian
   sheaves on `T_Zar` (`restrictCrystalDeRhamComplexIso`): in each degree it is
   `...SmallSite.restrictTensorDifferentialFormsSheafIso`, [Stacks, Tag 07IZ] for the terms, and
   the differentials of `F_T ⊗ Ω^*_{T/S,δ}` are those of `F ⊗ Ω^*_{X/S}` restricted to `T`, the
   extensions `m ⊗ ω ↦ ∇(m) ∧ ω + m ⊗ d ω` of the canonical connection of [Stacks, Tag 07J6].

## Main definitions

Everything lives in the namespace `Crystalline.GlobalCrystallineSituation.SmallSite`.

* `CrystalDeRhamSheafData.ambientComplex` — for the de Rham complex of a
  `CrystalDeRhamSheafData`, the complex `F_T ⊗_{𝒪_T} Ω^*_{T/S,δ}` on `T_Zar`, and
  `CrystalDeRhamSheafData.restrictComplexIso` its identification with the restriction to `T`.
* `CrystalDeRhamSheafData.comparison07LP` — the composite of the three steps.
* `ambientDeRhamComplex` — `F_T ⊗_{𝒪_T} Ω^*_{T/S,δ}` for a crystal in quasi-coherent modules,
  whose differentials are those of `...SmallSite.crystalDeRhamSheafData`.
* `crystallineToAmbientDeRham` — **[Stacks, Equation 07LP]**.

## Main results

* `truncation_comp_crystallineToAmbientDeRham` — the map of the equation, precomposed with the
  (invertible) image of the truncation map, is the restriction of global cohomology classes of
  `F ⊗ Ω^*_{X/S}` to `T` followed by the identification of step 3.
* `ambientDeRhamComplex_d`, `tensorFormsAmbientComparison_comp_ambientD_hom` and
  `restrictPresheafDeRhamDifferential_app_apply` — the differentials of
  `F_T ⊗_{𝒪_T} Ω^*_{T/S,δ}`: they are the restrictions to `T` of the differentials
  `...SmallSite.crystalDeRhamDifferential` of [Stacks, Tag 07LM]; read on the restricted presheaf
  tensor product they are the restriction of the presheaf de Rham differential, which over the
  opens `W` of `T` with `(U ∩ W, W, δ|_W)` affine over an affine open of `S` is the extension
  `m ⊗ ω ↦ ∇(m) ∧ ω + m ⊗ d ω` of the canonical connection `∇` of [Stacks, Tag 07J6].  That
  connection is the one of the sheaf-level `...SmallSite.crystalConnection` of 07J6, by
  `...SmallSite.AffineConnection.firstOrderTensorInclusion_crystalConnection_top`.

## References

* [Stacks Project, Tag 07LP](https://stacks.math.columbia.edu/tag/07LP)
* [Stacks Project, Tag 07LM](https://stacks.math.columbia.edu/tag/07LM)
* [Stacks Project, Tag 07IZ](https://stacks.math.columbia.edu/tag/07IZ)
* [Stacks Project, Tag 07J6](https://stacks.math.columbia.edu/tag/07J6)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace

universe w w' w'' w₃ u

noncomputable section

namespace Crystalline.GlobalCrystallineSituation.SmallSite

attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso
  instHasSheafifyOpensSpaceAddCommGrpCat

namespace CrystalDeRhamSheafData

variable {S : GlobalCrystallineSituation.{u}} {F : SheafOfModules.{u} (structureSheaf S)}
  (data : CrystalDeRhamSheafData S F) (A : CrystallineThickening S)

/-! ### The de Rham complex `F_T ⊗_{𝒪_T} Ω^*_{T/S,δ}` -/

/-- The degree-`i` differential `F_T ⊗ Ω^i_{T/S,δ} ⟶ F_T ⊗ Ω^{i+1}_{T/S,δ}` of the de Rham complex
of `F_T`: the restriction to `T` of the differential of `F ⊗ Ω^*_{X/S}`, read through the
identifications `(F ⊗ Ω^i_{X/S})_T ≅ F_T ⊗ Ω^i_{T/S,δ}` of
`...SmallSite.restrictTensorDifferentialFormsSheafIso`. -/
def ambientD (i : ℕ) : ambientTensorFormsAbelian F A i ⟶ ambientTensorFormsAbelian F A (i + 1) :=
  (restrictTensorDifferentialFormsSheafIso F A i).inv ≫
    (CrystallineThickening.abelianAmbientRestriction A).map (data.d i) ≫
      (restrictTensorDifferentialFormsSheafIso F A (i + 1)).hom

/-- Consecutive differentials of `F_T ⊗ Ω^*_{T/S,δ}` compose to zero, those of `F ⊗ Ω^*_{X/S}`
doing so. -/
theorem ambientD_comp (i : ℕ) : data.ambientD A i ≫ data.ambientD A (i + 1) = 0 := by
  simp only [ambientD, Category.assoc, Iso.hom_inv_id_assoc]
  rw [← Functor.map_comp_assoc, data.d_comp, Functor.map_zero, zero_comp, comp_zero]

/-- **`ambientD` on the underlying presheaves**: through the identifications of the terms, it is
the restriction to `T` of the differential of `F ⊗ Ω^*_{X/S}`. -/
theorem restrictTensorDifferentialFormsPresheafIso_hom_comp_ambientD_hom (i : ℕ) :
    (restrictTensorDifferentialFormsPresheafIso F A i).hom ≫ (data.ambientD A i).hom =
      Functor.whiskerLeft (CrystallineThickening.restrictOpenFunctor A).op (data.d i).hom ≫
        (restrictTensorDifferentialFormsPresheafIso F A (i + 1)).hom := by
  show (restrictTensorDifferentialFormsPresheafIso F A i).hom ≫
      (restrictTensorDifferentialFormsPresheafIso F A i).inv ≫
        Functor.whiskerLeft (CrystallineThickening.restrictOpenFunctor A).op (data.d i).hom ≫
          (restrictTensorDifferentialFormsPresheafIso F A (i + 1)).hom = _
  rw [Iso.hom_inv_id_assoc]
  rfl

/-- **The differential of `F_T ⊗_{𝒪_T} Ω^*_{T/S,δ}`, read on the restricted presheaf tensor
product**: composed with the comparison `F(A|_W) ⊗ Ω^i_{X/S}(A|_W) ⟶ (F_T ⊗ Ω^i_{T/S,δ})(W)`, the
differential `ambientD` is the restriction to `T` of the differential of `F ⊗ Ω^*_{X/S}`
precomposed with the crystalline sheafification unit. -/
theorem tensorFormsAmbientComparison_comp_ambientD_hom (i : ℕ) :
    tensorFormsAmbientComparison F A i ≫ (data.ambientD A i).hom =
      Functor.whiskerLeft (CrystallineThickening.restrictOpenFunctor A).op
          (toSheafify (smallTopology S) (tensorDifferentialFormsPresheaf F i) ≫ (data.d i).hom) ≫
        (restrictTensorDifferentialFormsPresheafIso F A (i + 1)).hom := by
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg (Functor.whiskerLeft (CrystallineThickening.restrictOpenFunctor A).op
    (toSheafify (smallTopology S) (tensorDifferentialFormsPresheaf F i)) ≫ ·)
    (data.restrictTensorDifferentialFormsPresheafIso_hom_comp_ambientD_hom A i)).trans ?_
  exact (Category.assoc (Functor.whiskerLeft (CrystallineThickening.restrictOpenFunctor A).op
      (toSheafify (smallTopology S) (tensorDifferentialFormsPresheaf F i)))
    (Functor.whiskerLeft (CrystallineThickening.restrictOpenFunctor A).op (data.d i).hom)
    (restrictTensorDifferentialFormsPresheafIso F A (i + 1)).hom).symm

/-- **The de Rham complex `F_T ⊗_{𝒪_T} Ω^*_{T/S,δ}` of `F_T`, `ℕ`-indexed.** -/
def ambientNatComplex :
    CochainComplex (Sheaf (Opens.grothendieckTopology A.obj.thickening.target.scheme)
      AddCommGrpCat.{u + 1}) ℕ :=
  CochainComplex.of (fun i ↦ ambientTensorFormsAbelian F A i) (data.ambientD A)
    (data.ambientD_comp A)

/-- **The de Rham complex `F_T ⊗_{𝒪_T} Ω^*_{T/S,δ}` of `F_T`**, extended from `ℕ` to `ℤ` by
zero. -/
def ambientComplex :
    CochainComplex (Sheaf (Opens.grothendieckTopology A.obj.thickening.target.scheme)
      AddCommGrpCat.{u + 1}) ℤ :=
  (data.ambientNatComplex A).extend ComplexShape.embeddingUpNat

/-- `F_T ⊗ Ω^*_{T/S,δ}` is concentrated in degrees `≥ 0`. -/
instance ambientComplex_isStrictlyGE : (data.ambientComplex A).IsStrictlyGE 0 :=
  inferInstanceAs (CochainComplex.IsStrictlyGE
    ((data.ambientNatComplex A).extend ComplexShape.embeddingUpNat) 0)

/-- **The restriction to `T` of the de Rham complex of `F` is the de Rham complex of `F_T`**,
`ℕ`-indexed: termwise it is `...SmallSite.restrictTensorDifferentialFormsSheafIso`. -/
def restrictNatComplexIso :
    ((CrystallineThickening.abelianAmbientRestriction A).mapHomologicalComplex _).obj
        data.natComplex ≅ data.ambientNatComplex A :=
  HomologicalComplex.Hom.isoOfComponents
    (fun i ↦ restrictTensorDifferentialFormsSheafIso F A i) (by
      rintro i j (rfl : i + 1 = j)
      simp only [Functor.mapHomologicalComplex_obj_d, natComplex, ambientNatComplex,
        CochainComplex.of_d, ambientD, Iso.hom_inv_id_assoc])

/-- **The restriction to `T` of the de Rham complex `F ⊗ Ω^*_{X/S}` is `F_T ⊗ Ω^*_{T/S,δ}`.** -/
def restrictComplexIso :
    ((CrystallineThickening.abelianAmbientRestriction A).mapHomologicalComplex _).obj
        data.complex ≅ data.ambientComplex A :=
  (CrystallineThickening.abelianAmbientRestriction A).mapExtendIso data.natComplex
      ComplexShape.embeddingUpNat ≪≫
    (ComplexShape.embeddingUpNat.extendFunctor _).mapIso (data.restrictNatComplexIso A)

/-! ### The comparison map of Equation 07LP -/

/-- The de Rham complex `F ⊗ Ω^*_{X/S}` of `F`, read as a bounded below complex. -/
abbrev complexPlus : CochainComplex.Plus (Sheaf (smallTopology S) AddCommGrpCat.{u + 1}) :=
  sheafPlusComplex S data.complex

/-- The de Rham complex `F_T ⊗ Ω^*_{T/S,δ}` of `F_T`, read as a bounded below complex. -/
def ambientComplexPlus :
    CochainComplex.Plus (Sheaf (Opens.grothendieckTopology A.obj.thickening.target.scheme)
      AddCommGrpCat.{u + 1}) :=
  ⟨data.ambientComplex A, ⟨0, inferInstance⟩⟩

section Derived

variable [HasDerivedCategory.{w} (Sheaf (smallTopology S) AddCommGrpCat.{u + 1})]
  [HasDerivedCategory.{w'} (Sheaf (opensTopology S) AddCommGrpCat.{u + 1})]
  [HasDerivedCategory.{w''} AddCommGrpCat.{u + 1}]

/-- `F[0]` in the bounded below derived category is the complex `singleComplex`. -/
def singleFunctorIsoSingleComplex :
    (DerivedCategory.Plus.singleFunctor (Sheaf (smallTopology S) AddCommGrpCat.{u + 1}) 0).obj
        (abelianSheaf F) ≅
      DerivedCategory.Plus.Qh.obj ((HomotopyCategory.Plus.quotient _).obj
        (sheafPlusComplex S (singleComplex (F := F)))) :=
  (Functor.singleFunctorPlusIsoCompQh 0).app _ ≪≫
    DerivedCategory.Plus.Qh.mapIso (ObjectProperty.isoMk _
      ((HomotopyCategory.quotient _ _).mapIso
        (HomologicalComplex.extendSingleIso ComplexShape.embeddingUpNat
          (abelianSheaf F) 0 0 rfl).symm))

/-- **The truncation map becomes an isomorphism after `RΓ(Cris(X/S), -)`**, under conditions (1)
and (2) of [Stacks, Tag 07JN].  `RΓ(Cris(X/S), -)` is `Ru_{X/S, *}` followed by `RΓ(X_Zar, -)`
(`...SmallSite.derivedGlobalSectionsIsoDerivedZariskiDirectImage`), and `Ru_{X/S, *}` of the
truncation map is an isomorphism (`isIso_derivedZariskiDirectImage_map_truncation`, the leading
assertion of [Stacks, Tag 07LM]). -/
theorem isIso_derivedGlobalSections_map_truncation (hqc : IsLocallyQuasiCoherent F)
    (hsurj : CohomologyRestriction.IsSurjectiveComparison F.val) :
    IsIso ((derivedGlobalSectionsFunctor S).map
      (DerivedCategory.Plus.Qh.map
        ((HomotopyCategory.Plus.quotient _).map
          (sheafPlusTruncation S data.complex (singleComplex (F := F)) data.truncation)))) := by
  have := data.isIso_derivedZariskiDirectImage_map_truncation hqc hsurj
  exact (NatIso.isIso_map_iff (derivedGlobalSectionsIsoDerivedZariskiDirectImage S) _).2
    (inferInstanceAs (IsIso ((derivedZariskiGlobalSectionsFunctor S).map
      ((derivedZariskiDirectImageFunctor S).map _))))

/-- **`RΓ(Cris(X/S), F) ≅ RΓ(Cris(X/S), F ⊗ Ω^*_{X/S})`**, the first step of the construction of
[Stacks, Equation 07LP]: the inverse of the image under `RΓ(Cris(X/S), -)` of the truncation map
`F ⊗ Ω^*_{X/S} ⟶ F[0]`, which [Stacks, Tag 07LM] makes invertible. -/
def derivedGlobalSectionsIsoDeRham (hqc : IsLocallyQuasiCoherent F)
    (hsurj : CohomologyRestriction.IsSurjectiveComparison F.val) :
    (derivedGlobalSectionsFunctor S).obj
        ((DerivedCategory.Plus.singleFunctor _ 0).obj (abelianSheaf F)) ≅
      (derivedGlobalSectionsFunctor S).obj
        (DerivedCategory.Plus.Qh.obj ((HomotopyCategory.Plus.quotient _).obj data.complexPlus)) :=
  haveI := data.isIso_derivedGlobalSections_map_truncation hqc hsurj
  (derivedGlobalSectionsFunctor S).mapIso (singleFunctorIsoSingleComplex (F := F)) ≪≫
    (asIso ((derivedGlobalSectionsFunctor S).map
      (DerivedCategory.Plus.Qh.map
        ((HomotopyCategory.Plus.quotient _).map
          (sheafPlusTruncation S data.complex (singleComplex (F := F)) data.truncation))))).symm

/-- The forward direction of `derivedGlobalSectionsIsoDeRham`: the identification of `F[0]` with
`singleComplex`, then the inverse of the image of the truncation map. -/
theorem derivedGlobalSectionsIsoDeRham_hom (hqc : IsLocallyQuasiCoherent F)
    (hsurj : CohomologyRestriction.IsSurjectiveComparison F.val) :
    haveI := data.isIso_derivedGlobalSections_map_truncation hqc hsurj
    (data.derivedGlobalSectionsIsoDeRham hqc hsurj).hom =
      (derivedGlobalSectionsFunctor S).map (singleFunctorIsoSingleComplex (F := F)).hom ≫
        inv ((derivedGlobalSectionsFunctor S).map
          (DerivedCategory.Plus.Qh.map
            ((HomotopyCategory.Plus.quotient _).map
              (sheafPlusTruncation S data.complex (singleComplex (F := F)) data.truncation)))) :=
  rfl

variable [HasDerivedCategory.{w₃}
  (Sheaf (Opens.grothendieckTopology A.obj.thickening.target.scheme) AddCommGrpCat.{u + 1})]

/-- **The restriction to `T` of `F ⊗ Ω^*_{X/S}`, in the derived category, is
`F_T ⊗ Ω^*_{T/S,δ}`**: termwise restriction of complexes, followed by `restrictComplexIso`. -/
def derivedRestrictComplexIso :
    (CrystallineThickening.derivedAmbientRestriction A).obj
        (DerivedCategory.Plus.Qh.obj ((HomotopyCategory.Plus.quotient _).obj data.complexPlus)) ≅
      DerivedCategory.Plus.Qh.obj ((HomotopyCategory.Plus.quotient _).obj
        (data.ambientComplexPlus A)) :=
  (CrystallineThickening.derivedAmbientRestrictionFactorsh A).app _ ≪≫
    DerivedCategory.Plus.Qh.mapIso (ObjectProperty.isoMk _
      (((CrystallineThickening.abelianAmbientRestriction A).mapHomotopyCategoryFactors _).app
          data.complex ≪≫
        (HomotopyCategory.quotient _ _).mapIso (data.restrictComplexIso A)))

/-- **The comparison map of [Stacks, Equation 07LP] for the de Rham complex of a
`CrystalDeRhamSheafData`**:

`RΓ(Cris(X/S), F) ⟶ RΓ(T, F_T ⊗_{𝒪_T} Ω^*_{T/S,δ})`,

the composite of `RΓ(Cris(X/S), F) ≅ RΓ(Cris(X/S), F ⊗ Ω^*_{X/S})`
(`derivedGlobalSectionsIsoDeRham`, from [Stacks, Tag 07LM]), of the restriction of global
cohomology classes to `T` (`...CrystallineThickening.derivedGlobalSectionsToAmbient`), and of the
identification `(F ⊗ Ω^*_{X/S})_T ≅ F_T ⊗ Ω^*_{T/S,δ}` of [Stacks, Tag 07IZ]
(`derivedRestrictComplexIso`). -/
def comparison07LP (hqc : IsLocallyQuasiCoherent F)
    (hsurj : CohomologyRestriction.IsSurjectiveComparison F.val) :
    (derivedGlobalSectionsFunctor S).obj
        ((DerivedCategory.Plus.singleFunctor _ 0).obj (abelianSheaf F)) ⟶
      (CrystallineThickening.derivedAmbientGlobalSectionsFunctor A).obj
        (DerivedCategory.Plus.Qh.obj ((HomotopyCategory.Plus.quotient _).obj
          (data.ambientComplexPlus A))) :=
  (data.derivedGlobalSectionsIsoDeRham hqc hsurj).hom ≫
    (CrystallineThickening.derivedGlobalSectionsToAmbient A).app _ ≫
      (CrystallineThickening.derivedAmbientGlobalSectionsFunctor A).map
        (data.derivedRestrictComplexIso A).hom

/-- **The comparison map is constructed from the three steps of the source.**  Precomposed with
the image under `RΓ(Cris(X/S), -)` of the truncation map `F ⊗ Ω^*_{X/S} ⟶ F[0]` (and the
identification of `F[0]` with `singleComplex`), it is the restriction of global cohomology classes
of `F ⊗ Ω^*_{X/S}` to `T` followed by the identification of `(F ⊗ Ω^*_{X/S})_T` with
`F_T ⊗ Ω^*_{T/S,δ}`.  Since the image of the truncation map is invertible, this determines the
comparison map. -/
@[reassoc]
theorem truncation_comp_comparison07LP (hqc : IsLocallyQuasiCoherent F)
    (hsurj : CohomologyRestriction.IsSurjectiveComparison F.val) :
    (derivedGlobalSectionsFunctor S).map
        (DerivedCategory.Plus.Qh.map
          ((HomotopyCategory.Plus.quotient _).map
            (sheafPlusTruncation S data.complex (singleComplex (F := F)) data.truncation))) ≫
      (derivedGlobalSectionsFunctor S).map (singleFunctorIsoSingleComplex (F := F)).inv ≫
        data.comparison07LP A hqc hsurj =
      (CrystallineThickening.derivedGlobalSectionsToAmbient A).app _ ≫
        (CrystallineThickening.derivedAmbientGlobalSectionsFunctor A).map
          (data.derivedRestrictComplexIso A).hom := by
  have := data.isIso_derivedGlobalSections_map_truncation hqc hsurj
  show _ ≫ _ ≫ (data.derivedGlobalSectionsIsoDeRham hqc hsurj).hom ≫ _ = _
  rw [derivedGlobalSectionsIsoDeRham_hom]
  simp only [Category.assoc]
  rw [← Functor.map_comp_assoc (derivedGlobalSectionsFunctor S)
      (singleFunctorIsoSingleComplex (F := F)).inv, Iso.inv_hom_id,
    CategoryTheory.Functor.map_id, Category.id_comp, IsIso.hom_inv_id_assoc]

end Derived

end CrystalDeRhamSheafData

/-! ### [Stacks, Equation 07LP] -/

variable {S : GlobalCrystallineSituation.{u}} {F : SheafOfModules.{u} (structureSheaf S)}
  (hF : F.IsQuasicoherentOnSite) (A : CrystallineThickening S)

/-- **The de Rham complex `F_T ⊗_{𝒪_T} Ω^*_{T/S,δ}`** of the restriction `F_T` of a crystal in
quasi-coherent modules `F` to the ambient scheme `T` of an object `(U, T, δ)` of `Cris(X/S)`, as
a complex of abelian sheaves on `T_Zar`.  Its degree-`i` term is `F_T ⊗_{𝒪_T} Ω^i_{T/S,δ}`
(`ambientDeRhamComplexXIso`), and its differentials are those of the de Rham complex
`F ⊗ Ω^*_{X/S}` of [Stacks, Tag 07LM] restricted to `T`, which are the extensions of the canonical
connection of [Stacks, Tag 07J6] (`restrictCrystalDeRhamComplexIso`). -/
def ambientDeRhamComplex :
    CochainComplex (Sheaf (Opens.grothendieckTopology A.obj.thickening.target.scheme)
      AddCommGrpCat.{u + 1}) ℤ :=
  (crystalDeRhamSheafData hF).ambientComplex A

/-- In degree `i ≥ 0` the term of `F_T ⊗_{𝒪_T} Ω^*_{T/S,δ}` is `F_T ⊗_{𝒪_T} Ω^i_{T/S,δ}`. -/
def ambientDeRhamComplexXIso (i : ℕ) :
    (ambientDeRhamComplex hF A).X (i : ℤ) ≅ ambientTensorFormsAbelian F A i :=
  HomologicalComplex.extendXIso _ ComplexShape.embeddingUpNat (i := i) (by simp)

/-- **[Stacks, Tag 07IZ] for the de Rham complex: `(F ⊗ Ω^*_{X/S})_T ≅ F_T ⊗_{𝒪_T} Ω^*_{T/S,δ}`
as complexes**, for a crystal in quasi-coherent modules `F`.  In each degree it is
`...SmallSite.restrictTensorDifferentialFormsSheafIso`. -/
def restrictCrystalDeRhamComplexIso :
    ((CrystallineThickening.abelianAmbientRestriction A).mapHomologicalComplex _).obj
        (crystalDeRhamSheafData hF).complex ≅ ambientDeRhamComplex hF A :=
  (crystalDeRhamSheafData hF).restrictComplexIso A

/-- **The differential of `F_T ⊗_{𝒪_T} Ω^*_{T/S,δ}` in degree `i`** is the restriction to `T` of
the differential `crystalDeRhamDifferential hF i` of `F ⊗ Ω^*_{X/S}`, read through the
identifications of [Stacks, Tag 07IZ] for the terms. -/
theorem ambientDeRhamComplex_d (i : ℕ) :
    (ambientDeRhamComplex hF A).d i (i + 1) =
      (ambientDeRhamComplexXIso hF A i).hom ≫
        (restrictTensorDifferentialFormsSheafIso F A i).inv ≫
          (CrystallineThickening.abelianAmbientRestriction A).map
            (crystalDeRhamDifferential hF i) ≫
            (restrictTensorDifferentialFormsSheafIso F A (i + 1)).hom ≫
              (ambientDeRhamComplexXIso hF A (i + 1)).inv := by
  have h := HomologicalComplex.extend_d_eq ((crystalDeRhamSheafData hF).ambientNatComplex A)
    ComplexShape.embeddingUpNat (i := i) (j := i + 1) (i' := (i : ℤ)) (j' := ((i + 1 : ℕ) : ℤ))
    (by simp) (by simp)
  refine (Eq.trans (by congr 1) h).trans ?_
  simp only [CrystalDeRhamSheafData.ambientNatComplex, CochainComplex.of_d,
    CrystalDeRhamSheafData.ambientD, Category.assoc]
  rfl

/-- **The differential of `F_T ⊗_{𝒪_T} Ω^*_{T/S,δ}` is the restriction of the de Rham differential
of `F ⊗ Ω^*_{X/S}` on the presheaf tensor product.**  Composed with the comparison
`F(A|_W) ⊗ Ω^i_{X/S}(A|_W) ⟶ (F_T ⊗ Ω^i_{T/S,δ})(W)`, the differential in degree `i` is the
restriction to `T` of `presheafDeRhamDifferential hF i`, the de Rham differential of the presheaf
`F ⊗ Ω^*_{X/S}`, followed by the identification of [Stacks, Tag 07IZ] in degree `i + 1`. -/
theorem tensorFormsAmbientComparison_comp_ambientD_hom (i : ℕ) :
    tensorFormsAmbientComparison F A i ≫ ((crystalDeRhamSheafData hF).ambientD A i).hom =
      Functor.whiskerLeft (CrystallineThickening.restrictOpenFunctor A).op
          (presheafDeRhamDifferential hF i) ≫
        (restrictTensorDifferentialFormsPresheafIso F A (i + 1)).hom := by
  rw [(crystalDeRhamSheafData hF).tensorFormsAmbientComparison_comp_ambientD_hom]
  exact congrArg (· ≫ (restrictTensorDifferentialFormsPresheafIso F A (i + 1)).hom)
    (congrArg (Functor.whiskerLeft (CrystallineThickening.restrictOpenFunctor A).op)
      (toSheafify_crystalDeRhamDifferential hF i))

/-- **On the opens of `T` over which the object is affine over an affine open of `S`, the
restriction of the presheaf de Rham differential is the extension of the canonical connection.**
Over such an open `W` — they cover `T` — the restriction to `T` of
`presheafDeRhamDifferential hF i` carries `x ∈ F(A|_W) ⊗ Ω^i_{X/S}(A|_W)` to the image in
`F ⊗ Ω^{i+1}_{X/S}` of `affineDeRhamDifferential hF i x`, which on `m ⊗ ω` is
`∇(m) ∧ ω + m ⊗ d ω` with `∇(m) = p₁^* m - p₀^* m` the canonical connection of [Stacks, Tag 07J6]
(`...SmallSite.tensorFormsSectionsEquiv_affineDeRhamDifferential`,
`...SmallSite.AffineConnection.extDiff_tmul`).  With
`tensorFormsAmbientComparison_comp_ambientD_hom` this computes the differential of
`F_T ⊗_{𝒪_T} Ω^*_{T/S,δ}`. -/
theorem restrictPresheafDeRhamDifferential_app_apply (i : ℕ)
    (W : A.obj.thickening.target.scheme.Opens)
    (hW : IsAffineOverAffineObject S (A.restrictOpen W))
    (x : ((CrystallineThickening.restrictOpenFunctor A).op ⋙
      tensorDifferentialFormsPresheaf F i).obj (op W)) :
    (Functor.whiskerLeft (CrystallineThickening.restrictOpenFunctor A).op
          (presheafDeRhamDifferential hF i)).app (op W) x =
      (Functor.whiskerLeft (CrystallineThickening.restrictOpenFunctor A).op
          (toSheafify (smallTopology S) (tensorDifferentialFormsPresheaf F (i + 1)))).app (op W)
        (ULift.up (affineDeRhamDifferential hF i ⟨A.restrictOpen W, hW⟩ x.down)) :=
  presheafDeRhamDifferential_app hF i ⟨A.restrictOpen W, hW⟩ x.down

section Derived

variable [HasDerivedCategory.{w} (Sheaf (smallTopology S) AddCommGrpCat.{u + 1})]
  [HasDerivedCategory.{w'} (Sheaf (opensTopology S) AddCommGrpCat.{u + 1})]
  [HasDerivedCategory.{w''} AddCommGrpCat.{u + 1}]
  [HasDerivedCategory.{w₃}
    (Sheaf (Opens.grothendieckTopology A.obj.thickening.target.scheme) AddCommGrpCat.{u + 1})]

/-- **Stacks Project, Equation 07LP.**  In Situation 07MF, let `F` be a crystal in quasi-coherent
modules on `Cris(X/S)` and let `(U, T, δ)` be an object of `Cris(X/S)`.  The canonical map

`RΓ(Cris(X/S), F) ⟶ RΓ(T, F_T ⊗_{𝒪_T} Ω^*_{T/S,δ})`

in `D⁺(Ab)`, constructed as in the source: `RΓ(Cris(X/S), F) = RΓ(Cris(X/S), F ⊗ Ω^*_{X/S})` by
[Stacks, Tag 07LM] (`CrystalDeRhamSheafData.derivedGlobalSectionsIsoDeRham`, the inverse of the
image of the truncation map, invertible after `Ru_{X/S, *}` and hence after `RΓ(Cris(X/S), -)`);
then the restriction of global cohomology classes to `T`
(`...CrystallineThickening.derivedGlobalSectionsToAmbient`); then the identification of the
restriction of `F ⊗ Ω^*_{X/S}` to `T` with `F_T ⊗_{𝒪_T} Ω^*_{T/S,δ}` by [Stacks, Tag 07IZ]
(`restrictCrystalDeRhamComplexIso`).  `truncation_comp_crystallineToAmbientDeRham` records that
it is this composite.  The target is `RΓ(T, -)` of `ambientDeRhamComplex hF A`, read as a bounded
below complex (`CrystalDeRhamSheafData.ambientComplexPlus`). -/
@[stacks 07LP "the canonical map RΓ(Cris(X/S), F) ⟶ RΓ(T, F_T ⊗ Ω*_{T/S,δ}) for a crystal in \
quasi-coherent modules F and an object (U, T, δ), built from 07LM, restriction to T and 07IZ"]
def crystallineToAmbientDeRham :
    (derivedGlobalSections S).obj (abelianSheaf F) ⟶
      (CrystallineThickening.derivedAmbientGlobalSectionsFunctor A).obj
        (DerivedCategory.Plus.Qh.obj ((HomotopyCategory.Plus.quotient _).obj
          ((crystalDeRhamSheafData hF).ambientComplexPlus A))) :=
  (crystalDeRhamSheafData hF).comparison07LP A
    (satisfiesVanishingHypotheses_of_isQuasicoherentOnSite F hF).1
    (satisfiesVanishingHypotheses_of_isQuasicoherentOnSite F hF).2

/-- **The map of [Stacks, Equation 07LP] is the composite of the source.**  Precomposed with the
image under `RΓ(Cris(X/S), -)` of the truncation map `F ⊗ Ω^*_{X/S} ⟶ F[0]` of
[Stacks, Tag 07LM] — an isomorphism — it is the restriction to `T` of the global cohomology
classes of `F ⊗ Ω^*_{X/S}`, followed by `RΓ(T, -)` of the identification
`(F ⊗ Ω^*_{X/S})_T ≅ F_T ⊗_{𝒪_T} Ω^*_{T/S,δ}` of [Stacks, Tag 07IZ]. -/
@[stacks 07LP "the canonical map is the composite of the source: 07LM, restriction of global \
cohomology classes to T, and 07IZ"]
theorem truncation_comp_crystallineToAmbientDeRham :
    (derivedGlobalSectionsFunctor S).map
        (DerivedCategory.Plus.Qh.map
          ((HomotopyCategory.Plus.quotient _).map
            (sheafPlusTruncation S (crystalDeRhamSheafData hF).complex
              (CrystalDeRhamSheafData.singleComplex (F := F))
              (crystalDeRhamSheafData hF).truncation))) ≫
      (derivedGlobalSectionsFunctor S).map
          (CrystalDeRhamSheafData.singleFunctorIsoSingleComplex (F := F)).inv ≫
        crystallineToAmbientDeRham hF A =
      (CrystallineThickening.derivedGlobalSectionsToAmbient A).app _ ≫
        (CrystallineThickening.derivedAmbientGlobalSectionsFunctor A).map
          ((crystalDeRhamSheafData hF).derivedRestrictComplexIso A).hom :=
  (crystalDeRhamSheafData hF).truncation_comp_comparison07LP A
    (satisfiesVanishingHypotheses_of_isQuasicoherentOnSite F hF).1
    (satisfiesVanishingHypotheses_of_isQuasicoherentOnSite F hF).2

end Derived

end Crystalline.GlobalCrystallineSituation.SmallSite
