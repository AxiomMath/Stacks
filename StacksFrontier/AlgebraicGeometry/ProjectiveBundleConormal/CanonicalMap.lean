module

public import StacksFrontier.AlgebraicGeometry.ProjectiveBundleSplitting.TautologicalMap
public import StacksFrontier.AlgebraicGeometry.InvertibleQuotient.Basic
public import StacksFrontier.AlgebraicGeometry.ProjBundleInverseBaseChange.Basic
public import StacksFrontier.AlgebraicGeometry.CartierConormal.Basic
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundle.SectionClosedImmersion
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackSheafTensorMonoidal
public import StacksFrontier.AlgebraicGeometry.PicardBaseChange.MulIsomorphism

/-!
# The canonical map of a section of a projective bundle into its conormal sheaf

Let `ℰ` be a quasi-coherent module on a scheme `X`, let `π : 𝐏(ℰ) ⟶ X` be its projective
bundle and let `u : π^*ℰ ⟶ 𝒪(1)` be the tautological map. Tag 0B3V's third clause says that a
section `σ` of `π` classifying an invertible quotient `q : ℰ ⟶ L` is a closed immersion whose
conormal sheaf receives a canonical map

  `ker(q) ⊗ L^{⊗ -1} ⟶ 𝒞_{σ(X)/𝐏(ℰ)}`.

This file constructs that map. The route is the one the clause describes, with no local
computation anywhere:

1. `u` restricted to `π^*ker(q)` is a map `v : π^*ker(q) ⟶ 𝒪(1)`; untwisting it by the
   evaluation `𝒪(1) ⊗ 𝒪(-1) ≅ 𝒪_{𝐏(ℰ)}` gives `ṽ : (π^*ker q) ⊗ 𝒪(-1) ⟶ 𝒪_{𝐏(ℰ)}`.
2. Because `σ` classifies `q`, `σ^*v` is the transport of `ker(q) ⟶ ℰ ⟶ L`, which is zero;
   untwisting is additive and commutes with `σ^*` by Tag 01CD, so `σ^*ṽ = 0` too.
3. A map into `𝒪_{𝐏(ℰ)}` whose pullback along `σ` vanishes is killed by the unit
   `𝒪_{𝐏(ℰ)} ⟶ σ_*𝒪_X`, its transpose under `σ^* ⊣ σ_*` being `σ^*ṽ` up to the counit. So `ṽ`
   lifts through the ideal sheaf `ℐ(σ) = ker(𝒪_{𝐏(ℰ)} ⟶ σ_*𝒪_X)`.
4. Pulling that lift back along `σ` and reading the result through
   `Stacks.CartierConormal.conormalSheafIsoPullbackSelf`, which says `𝒞_σ ≅ σ^*ℐ(σ)`, gives the
   canonical map.

## Main definitions

* `Stacks.ProjectiveBundleConormal.kernelTautologicalMap`: the map `v`.
* `Stacks.ProjectiveBundleConormal.kernelTautologicalMapTwisted`: the map `ṽ`.
* `Stacks.ProjectiveBundleConormal.idealSheafLift`: the lift of `ṽ` through `ℐ(σ)`.
* `Stacks.ProjectiveBundleConormal.pullbackSourceIso`: the identification
  `σ^*((π^*ker q) ⊗ 𝒪(-1)) ≅ ker(q) ⊗ L^{⊗ -1}`.
* `Stacks.ProjectiveBundleConormal.conormalCanonicalMap`: **the canonical map of Tag 0B3V
  clause 3.**

## Main results

* `Stacks.ProjectiveBundleConormal.pullback_kernelTautologicalMap_eq_zero` and
  `pullback_kernelTautologicalMapTwisted_eq_zero`: step 2 above.
* `Stacks.ProjectiveBundleConormal.kernelTautologicalMapTwisted_comp_structureSheafUnit`:
  step 3 above.
* `Stacks.ProjectiveBundleConormal.idealSheafLift_comp_ι`,
  `pullbackSourceIso_hom_comp_conormalCanonicalMap` and `conormalCanonicalMap_comp_ι`: the
  normalisations that pin the canonical map down.

## Implementation notes

**Which tensor spelling.** This repository carries two monoidal structures on sheaves of
modules — the localized one, `Stacks.SheafInternalHom.monoidalCategory`, which
`Stacks.ProjBundleInverseBaseChange.negOneMulIso'` is stated over, and the re-seated one,
`SheafOfModules.monoidalCategorySheafTensor`, whose tensor product is **definitionally**
`Stacks.SheafOfModules.TensorSheafification.tensorSheaf` (equivalently
`Stacks.SheafOfModules.Invertible.tensorProduct`, by
`Stacks.ProjectiveBundleConormal.tensorProduct_eq_tensorObj`) and whose unit is
**definitionally** `SheafOfModules.unit`. Everything below uses the second one, installed on
`AlgebraicGeometry.Scheme.Modules` as the local instance
`Stacks.ProjectiveBundleConormal.monoidalSheafTensor`. Three things decided the choice, and all
three are what make the file short:

* `Stacks.PullbackSheafTensor.sheafTensorComparison_naturality_left` is Tag 01CD's comparison in
  whiskered form for exactly this structure, which is the one step of the construction that is
  not formal;
* `SheafOfModules.monoidalPreadditiveSheafTensor` gives `(0 : A ⟶ B) ▷ T = 0` for it, which is
  the additivity step 2 needs — the localized structure has no `MonoidalPreadditive` instance.
  Step 2 is its only use, so it is introduced by `have` in that one proof rather than as a
  file-level instance; the library already carries several identical re-seatings of it;
* the unit being `SheafOfModules.unit` on the nose means the target of the untwisted map is
  literally the source of `SheafOfModules.unitToPushforwardObjUnit`, whose kernel is the ideal
  sheaf, so step 3 needs no comparison of units.

The evaluation pairing `𝒪(1) ⊗ 𝒪(-1) ≅ 𝒪_{𝐏(ℰ)}` is therefore built here out of Tag 01CU's
successor comparison and the braiding of the tensor product sheaf rather than taken from
`Stacks.ProjBundleInverseBaseChange.negOneMulIso'`, which is the same isomorphism in the
localized spelling and would have to be crossed back twice.

**Ascription.** `Stacks.PullbackSheafTensor` states Tag 01CD over the sheaves of modules of the
underlying *ringed space*, which is definitionally `AlgebraicGeometry.Scheme.Modules` but not
syntactically; a composite mixing the two spellings is not type-correct at `implicit`
transparency, so `rw` refuses a goal containing one. `pullbackTensorComparison`,
`pullbackTensorComparisonIso` and `structureSheafUnit` are the comparison, its inverse and the
unit `𝒪_Y ⟶ f_*𝒪_X` with their types ascribed at the scheme spelling, so that the crossing
happens once per definition and every statement below stays in one category.

**Surjectivity of the tautological map is not used.** Neither `u` nor `v` is assumed
epimorphic, and nothing below would follow from it; Tag 0B3V's clause 3 asserts the existence of
the map, not that it is an isomorphism, and the latter is not proved here.

## References

* [Stacks Project, Tag 0B3V](https://stacks.math.columbia.edu/tag/0B3V)
* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
* [Stacks Project, Tag 01OD](https://stacks.math.columbia.edu/tag/01OD)
* [Stacks Project, Tag 01R2](https://stacks.math.columbia.edu/tag/01R2)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
open RingedSpaceModuleAdjunction
open Stacks.SheafInternalHom (isSheaf_structureRingPresheaf)
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.ProjectiveBundleSplitting
open Stacks.SymGraded

universe u

namespace Stacks.ProjectiveBundleConormal

/-- The monoidal structure on the sheaves of modules of a scheme whose tensor product is the
tensor product sheaf of Tag 01CA and whose unit is the structure sheaf, both definitionally.
Deliberately local: `AlgebraicGeometry.Scheme.Modules` carries more than one. -/
@[instance_reducible] local instance monoidalSheafTensor (X : Scheme.{u}) :
    MonoidalCategory X.Modules :=
  _root_.SheafOfModules.monoidalCategorySheafTensor X.toRingedSpace.sheaf

/-! ### Tag 01CD and the structure-sheaf unit, ascribed at the scheme spelling -/

section Comparison

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- **The comparison of [Stacks, Tag 01CD]** `f^*(A ⊗ B) ⟶ f^*A ⊗ f^*B`, with its source and
target ascribed at `AlgebraicGeometry.Scheme.Modules`. This is
`Stacks.PullbackSheafTensor.sheafTensorComparison`, whose statement spells the modules over the
underlying ringed space; the two spellings are definitionally equal, but a composite mixing
them is not type-correct at `implicit` transparency, so `rw` refuses a goal containing one.
Ascribing here makes the crossing happen once. -/
def pullbackTensorComparison (A B : Y.Modules) :
    (Scheme.Modules.pullback f).obj (A ⊗ B) ⟶
      (Scheme.Modules.pullback f).obj A ⊗ (Scheme.Modules.pullback f).obj B :=
  Stacks.PullbackSheafTensor.sheafTensorComparison f.toLRSHom.toShHom A B

/-- The comparison of Tag 01CD is invertible. -/
instance isIso_pullbackTensorComparison (A B : Y.Modules) :
    IsIso (pullbackTensorComparison f A B) :=
  Stacks.PullbackSheafTensor.isIso_sheafTensorComparison f.toLRSHom.toShHom A B

/-- **Tag 01CD as an isomorphism** `f^*(A ⊗ B) ≅ f^*A ⊗ f^*B`. -/
def pullbackTensorComparisonIso (A B : Y.Modules) :
    (Scheme.Modules.pullback f).obj (A ⊗ B) ≅
      (Scheme.Modules.pullback f).obj A ⊗ (Scheme.Modules.pullback f).obj B :=
  asIso (pullbackTensorComparison f A B)

/-- Naturality of the comparison of Tag 01CD in the first variable, in whiskered form. -/
theorem pullbackTensorComparison_naturality_left {A A' : Y.Modules} (v : A ⟶ A')
    (B : Y.Modules) :
    pullbackTensorComparison f A B ≫
        ((Scheme.Modules.pullback f).map v ▷ (Scheme.Modules.pullback f).obj B) =
      (Scheme.Modules.pullback f).map (v ▷ B) ≫ pullbackTensorComparison f A' B :=
  Stacks.PullbackSheafTensor.sheafTensorComparison_naturality_left f.toLRSHom.toShHom v B

/-- **The unit `𝒪_Y ⟶ f_*𝒪_X` of a morphism of schemes**, ascribed at
`AlgebraicGeometry.Scheme.Modules` and at the monoidal unit. This is the map whose kernel is
`Stacks.ClosedImmersion.idealSheaf`. -/
def structureSheafUnit :
    𝟙_ (Y.Modules) ⟶ (Scheme.Modules.pushforward f).obj (𝟙_ (X.Modules)) :=
  _root_.SheafOfModules.unitToPushforwardObjUnit (structureSheafHom f.toLRSHom.toShHom)

/-- The ideal sheaf of `f` is the kernel of `structureSheafUnit f`, by definition. -/
theorem idealSheaf_eq_kernel :
    Stacks.ClosedImmersion.idealSheaf f.toLRSHom.toShHom = kernel (structureSheafUnit f) :=
  rfl

end Comparison

/-! ### The evaluation pairing of an invertible module with its inverse -/

section Evaluation

variable {X : Scheme.{u}} (L : X.Modules)
  [AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L]

/-- **The evaluation pairing `L ⊗ L^{⊗ -1} ≅ 𝒪_X`**, with source and target ascribed at the
monoidal product and unit used here. This is
`Stacks.SheafOfModules.Invertible.mulNegOneIso`, whose statement spells the tensor product as
`Stacks.SheafOfModules.TensorSheafification.tensorSheaf` and the structure sheaf as
`SheafOfModules.unit`; both agree with `⊗` and `𝟙_` definitionally, and ascribing here makes the
crossing happen once for every use below. -/
def invertibleEvaluation :
    L ⊗ Stacks.SheafOfModules.Invertible.tensorPower X.presheaf X.ringCatSheaf.2 L (-1) ≅
      𝟙_ X.Modules :=
  Stacks.SheafOfModules.Invertible.mulNegOneIso X.presheaf X.ringCatSheaf.2 L

end Evaluation

/-! ### The projective bundle, its sections and its twists -/

variable {X : Scheme.{u}} (E : X.Modules) [E.IsQuasicoherent]

/-- Quasi-coherence of the graded pieces of `Sym(ℰ)`, the hypothesis the projective bundle is
built from, discharged for a quasi-coherent `ℰ`. -/
abbrev symPieces : IsQuasicoherentPieces E := isQuasicoherentPieces_of_isQuasicoherent E

/-- The projective bundle `𝐏(ℰ) = Proj_X(Sym(ℰ))` together with its projection `π` to `X`. -/
abbrev bundle : RelativeProjData (schemeSheafGradedAlgebra E (symPieces E)) :=
  relativeProj (schemeSheafGradedAlgebra E (symPieces E))

/-- `𝒪(1)` is invertible: `Stacks.ProjectiveBundleSplitting.isInvertible_tautologicalTwist`. -/
instance isInvertible_tautologicalTwist_algebraicGeometry :
    AlgebraicGeometry.SheafOfModules.IsInvertible (bundle E).scheme.presheaf
      (bundle E).scheme.ringCatSheaf.2 (tautologicalTwist E (symPieces E)) :=
  isInvertible_tautologicalTwist E (symPieces E)

/-- `𝒪(1)` is invertible in this repository's predicate. The two predicates are related by
`Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry`, and instance search does not cross
between them on its own. -/
instance isInvertible_tautologicalTwist_stacks :
    Stacks.SheafOfModules.IsInvertible (bundle E).scheme.presheaf
      (bundle E).scheme.ringCatSheaf.2 (tautologicalTwist E (symPieces E)) :=
  (Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry _ _ _).mpr
    (isInvertible_tautologicalTwist_algebraicGeometry E)

/-- The same instance at the sheaf-condition spelling
`Stacks.ProjBundleInverseBaseChange.inverseQuotientBaseChangeIso` is stated in. The two
spellings are equal by proof irrelevance but instance search does not cross between them. -/
instance isInvertible_tautologicalTwist_stacks' :
    Stacks.SheafOfModules.IsInvertible (bundle E).scheme.presheaf
      (isSheaf_structureRingPresheaf (bundle E).scheme) (tautologicalTwist E (symPieces E)) :=
  isInvertible_tautologicalTwist_stacks E

/-- **`𝒪(-1) = 𝒪(1)^{⊗ -1}`**, the inverse of the tautological twist, as Tag 01CU's `(-1)`st
tensor power. -/
abbrev inverseTautologicalTwist : (bundle E).scheme.Modules :=
  Stacks.SheafOfModules.Invertible.tensorPower (bundle E).scheme.presheaf
    (bundle E).scheme.ringCatSheaf.2 (tautologicalTwist E (symPieces E)) (-1)

/-! ### The twisted tautological map on the kernel of an invertible quotient -/

variable (Q : Stacks.Divisors.InvertibleQuotient X E)

/-- `Q.L` is invertible in this repository's predicate, at the sheaf-condition spelling
`Stacks.ProjBundleInverseBaseChange.inverseQuotientBaseChangeIso` is stated in. -/
instance isInvertible_quotient :
    Stacks.SheafOfModules.IsInvertible X.presheaf (isSheaf_structureRingPresheaf X) Q.L :=
  (Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry _ _ _).mpr Q.invertible

/-- **The tautological map restricted to the kernel of `q`**, `v : π^*ker(q) ⟶ 𝒪(1)`. -/
def kernelTautologicalMap :
    (Scheme.Modules.pullback (bundle E).toBase).obj (kernel Q.q) ⟶
      tautologicalTwist E (symPieces E) :=
  (Scheme.Modules.pullback (bundle E).toBase).map (kernel.ι Q.q) ≫
    tautologicalMap E (symPieces E)

/-- **The untwisting of `kernelTautologicalMap`**, `ṽ : (π^*ker q) ⊗ 𝒪(-1) ⟶ 𝒪_{𝐏(ℰ)}`: the
map `v` tensored with the identity of `𝒪(-1)`, followed by the evaluation pairing. -/
def kernelTautologicalMapTwisted :
    (Scheme.Modules.pullback (bundle E).toBase).obj (kernel Q.q) ⊗
        inverseTautologicalTwist E ⟶
      𝟙_ ((bundle E).scheme.Modules) :=
  kernelTautologicalMap E Q ▷ inverseTautologicalTwist E ≫
    (invertibleEvaluation (tautologicalTwist E (symPieces E))).hom

/-! ### A section classifying the quotient kills the twisted map -/

variable {σ : X ⟶ (bundle E).scheme} (hσ : σ ≫ (bundle E).toBase = 𝟙 X)

/-- **The collapse `F ≅ σ^*π^*F` supplied by `σ ≫ π = 𝟙 X`**, as a natural isomorphism. Its
components are the three comparison maps that
`Stacks.RelativeProj.TautologicalDatum.pullbackQuotientMap` composes. -/
def pullbackSectionNatIso :
    𝟭 X.Modules ≅
      Scheme.Modules.pullback (bundle E).toBase ⋙ Scheme.Modules.pullback σ :=
  (Scheme.Modules.pullbackId X).symm ≪≫ (Scheme.Modules.pullbackCongr hσ).symm ≪≫
    (Scheme.Modules.pullbackComp σ (bundle E).toBase).symm

/-- The components of `pullbackSectionNatIso`, spelled out. -/
theorem pullbackSectionNatIso_hom_app (F : X.Modules) :
    (pullbackSectionNatIso E hσ).hom.app F =
      (Scheme.Modules.pullbackId X).inv.app F ≫
        (Scheme.Modules.pullbackCongr hσ).inv.app F ≫
          (Scheme.Modules.pullbackComp σ (bundle E).toBase).inv.app F :=
  rfl

variable (e : (Scheme.Modules.pullback σ).obj (tautologicalTwist E (symPieces E)) ≅ Q.L)
  (hqe : (Scheme.Modules.pullbackId X).inv.app E ≫
    (Scheme.Modules.pullbackCongr hσ).inv.app E ≫
      (Scheme.Modules.pullbackComp σ (bundle E).toBase).inv.app E ≫
        (Scheme.Modules.pullback σ).map (tautologicalMap E (symPieces E)) ≫ e.hom = Q.q)

include hqe in
/-- **`σ^*` kills the tautological map on the kernel.** Naturality of the collapse
`F ≅ σ^*π^*F` turns `σ^*v`, read through that collapse and through `e`, into
`ker(q) ⟶ ℰ ⟶ L`, which is zero. -/
theorem pullback_kernelTautologicalMap_eq_zero :
    (Scheme.Modules.pullback σ).map (kernelTautologicalMap E Q) = 0 := by
  have hnat : (pullbackSectionNatIso E hσ).hom.app (kernel Q.q) ≫
      (Scheme.Modules.pullback σ).map
        ((Scheme.Modules.pullback (bundle E).toBase).map (kernel.ι Q.q)) =
      kernel.ι Q.q ≫ (pullbackSectionNatIso E hσ).hom.app E :=
    ((pullbackSectionNatIso E hσ).hom.naturality (kernel.ι Q.q)).symm
  have hqe' : (pullbackSectionNatIso E hσ).hom.app E ≫
      (Scheme.Modules.pullback σ).map (tautologicalMap E (symPieces E)) ≫ e.hom = Q.q := hqe
  rw [← cancel_mono e.hom, zero_comp,
    ← cancel_epi ((pullbackSectionNatIso E hσ).hom.app (kernel Q.q)), comp_zero]
  calc (pullbackSectionNatIso E hσ).hom.app (kernel Q.q) ≫
        (Scheme.Modules.pullback σ).map (kernelTautologicalMap E Q) ≫ e.hom
      = ((pullbackSectionNatIso E hσ).hom.app (kernel Q.q) ≫
          (Scheme.Modules.pullback σ).map
            ((Scheme.Modules.pullback (bundle E).toBase).map (kernel.ι Q.q))) ≫
          ((Scheme.Modules.pullback σ).map (tautologicalMap E (symPieces E)) ≫ e.hom) := by
        rw [kernelTautologicalMap, Functor.map_comp]; simp only [Category.assoc]
    _ = kernel.ι Q.q ≫ ((pullbackSectionNatIso E hσ).hom.app E ≫
          (Scheme.Modules.pullback σ).map (tautologicalMap E (symPieces E)) ≫ e.hom) := by
        rw [hnat]; simp only [Category.assoc]
    _ = kernel.ι Q.q ≫ Q.q := by rw [hqe']
    _ = 0 := kernel.condition Q.q

include hqe in
/-- **`σ^*` kills the untwisted map as well.** Tensoring with `𝒪(-1)` is additive, and by Tag
01CD it commutes with `σ^*`, so the vanishing of `σ^*v` is inherited by `σ^*ṽ`. -/
theorem pullback_kernelTautologicalMapTwisted_eq_zero :
    (Scheme.Modules.pullback σ).map (kernelTautologicalMapTwisted E Q) = 0 := by
  have hv := pullback_kernelTautologicalMap_eq_zero E Q hσ e hqe
  have hnat := pullbackTensorComparison_naturality_left σ (kernelTautologicalMap E Q)
    (inverseTautologicalTwist E)
  have hwhisker : (Scheme.Modules.pullback σ).map
      (kernelTautologicalMap E Q ▷ inverseTautologicalTwist E) = 0 := by
    have h2 : (Scheme.Modules.pullback σ).map
          (kernelTautologicalMap E Q ▷ inverseTautologicalTwist E) ≫
        pullbackTensorComparison σ (tautologicalTwist E (symPieces E))
          (inverseTautologicalTwist E) = 0 := by
      have : MonoidalPreadditive X.Modules :=
        _root_.SheafOfModules.monoidalPreadditiveSheafTensor X.toRingedSpace.sheaf
      rw [← hnat, hv, MonoidalPreadditive.zero_whiskerRight, comp_zero]
    simpa using (cancel_mono (pullbackTensorComparison σ (tautologicalTwist E (symPieces E))
      (inverseTautologicalTwist E))).mp (h2.trans zero_comp.symm)
  rw [kernelTautologicalMapTwisted, Functor.map_comp, hwhisker, zero_comp]

/-! ### Factoring the twisted map through the ideal sheaf of the section -/

include hqe in
/-- **The untwisted map vanishes against the unit `𝒪_{𝐏(ℰ)} ⟶ σ_*𝒪_X`.** Its transpose under
`σ^* ⊣ σ_*` is `σ^*ṽ` followed by the counit, and `σ^*ṽ` is zero; the transpose is a
bijection, so the map itself is zero. -/
theorem kernelTautologicalMapTwisted_comp_structureSheafUnit :
    kernelTautologicalMapTwisted E Q ≫ structureSheafUnit σ = 0 := by
  have hM2 := pullback_kernelTautologicalMapTwisted_eq_zero E Q hσ e hqe
  refine ((Scheme.Modules.pullbackPushforwardAdjunction σ).homEquiv _ _).symm.injective ?_
  simp only [Adjunction.homEquiv_counit, Functor.map_comp, Functor.map_zero, hM2, zero_comp]

include hqe in
/-- **The untwisted map factors through the ideal sheaf `ℐ(σ)`**, which is Tag 0B3V's clause 3
before pulling back to the section. -/
def idealSheafLift :
    (Scheme.Modules.pullback (bundle E).toBase).obj (kernel Q.q) ⊗
        inverseTautologicalTwist E ⟶
      kernel (structureSheafUnit σ) :=
  kernel.lift (structureSheafUnit σ) (kernelTautologicalMapTwisted E Q)
    (kernelTautologicalMapTwisted_comp_structureSheafUnit E Q hσ e hqe)

include hqe in
/-- **The normalisation of `idealSheafLift`**: composed with the inclusion of the ideal sheaf
into `𝒪_{𝐏(ℰ)}` it is the untwisted map itself. -/
theorem idealSheafLift_comp_ι :
    idealSheafLift E Q hσ e hqe ≫ kernel.ι (structureSheafUnit σ) =
      kernelTautologicalMapTwisted E Q :=
  kernel.lift_ι _ _ _

/-! ### The canonical map into the conormal sheaf -/

include e in
/-- **`σ^*𝒪(-1) ≅ (Q.L)^{⊗ -1}`**: the base change of the inverse of an invertible sheaf, Tag
0B3V's `inverseQuotientBaseChangeIso`, at the comparison `e` saying that `σ` classifies `Q`. -/
def inverseTwistBaseChangeIso :
    (Scheme.Modules.pullback σ).obj (inverseTautologicalTwist E) ≅
      Stacks.SheafOfModules.Invertible.tensorPower X.presheaf X.ringCatSheaf.2 Q.L (-1) :=
  Stacks.ProjBundleInverseBaseChange.inverseQuotientBaseChangeIso σ
    (tautologicalTwist E (symPieces E)) Q.L e.symm

include hσ e in
/-- **The identification of the source**: `σ^*((π^*ker q) ⊗ 𝒪(-1)) ≅ ker(q) ⊗ (Q.L)^{⊗ -1}`.
Tag 01CD splits the pullback over the tensor product, `σ ≫ π = 𝟙 X` collapses the first factor,
and Tag 0B3V's base change of the inverse identifies the second. -/
def pullbackSourceIso :
    (Scheme.Modules.pullback σ).obj
        ((Scheme.Modules.pullback (bundle E).toBase).obj (kernel Q.q) ⊗
          inverseTautologicalTwist E) ≅
      kernel Q.q ⊗
        Stacks.SheafOfModules.Invertible.tensorPower X.presheaf X.ringCatSheaf.2 Q.L (-1) :=
  pullbackTensorComparisonIso σ
      ((Scheme.Modules.pullback (bundle E).toBase).obj (kernel Q.q))
      (inverseTautologicalTwist E) ≪≫
    MonoidalCategory.tensorIso ((pullbackSectionNatIso E hσ).app (kernel Q.q)).symm
      (inverseTwistBaseChangeIso E Q e)

/-- The source of the canonical map is the tensor product sheaf on the nose: the monoidal
product of `monoidalSheafTensor` is `Stacks.SheafOfModules.Invertible.tensorProduct` by
definition. -/
theorem tensorProduct_eq_tensorObj (M N : X.Modules) :
    Stacks.SheafOfModules.Invertible.tensorProduct X.presheaf X.ringCatSheaf.2 M N = M ⊗ N :=
  rfl

variable [IsImmersion σ]

include hσ e hqe in
/-- **The canonical map of Stacks Tag 0B3V clause 3**: `ker(q) ⊗ L^{⊗ -1} ⟶ 𝒞_{σ(X)/𝐏(ℰ)}`. -/
def conormalCanonicalMap :
    kernel Q.q ⊗
        Stacks.SheafOfModules.Invertible.tensorPower X.presheaf X.ringCatSheaf.2 Q.L (-1) ⟶
      Stacks.Conormal.conormalSheaf σ :=
  (pullbackSourceIso E Q hσ e).inv ≫
    (Scheme.Modules.pullback σ).map (idealSheafLift E Q hσ e hqe) ≫
      (Stacks.CartierConormal.conormalSheafIsoPullbackSelf σ).inv

include hσ e hqe in
/-- **The canonical map is `σ^*` of the ideal-sheaf lift**, read through the identification of
its source with `σ^*((π^*ker q) ⊗ 𝒪(-1))` and the identification `𝒞_σ ≅ σ^*ℐ(σ)`. -/
theorem pullbackSourceIso_hom_comp_conormalCanonicalMap :
    (pullbackSourceIso E Q hσ e).hom ≫ conormalCanonicalMap E Q hσ e hqe =
      (Scheme.Modules.pullback σ).map (idealSheafLift E Q hσ e hqe) ≫
        (Stacks.CartierConormal.conormalSheafIsoPullbackSelf σ).inv :=
  Iso.hom_inv_id_assoc (pullbackSourceIso E Q hσ e) _

include hσ e hqe in
/-- **The canonical map composed with the inclusion of the conormal sheaf into `σ^*𝒪_{𝐏(ℰ)}`**
is `σ^*` of the untwisted tautological map. Together with `idealSheafLift_comp_ι` this pins the
canonical map down: it is the factorization of `σ^*ṽ` through `σ^*ℐ(σ)`. -/
theorem conormalCanonicalMap_comp_ι :
    (pullbackSourceIso E Q hσ e).hom ≫ conormalCanonicalMap E Q hσ e hqe ≫
        (Stacks.CartierConormal.conormalSheafIsoPullbackSelf σ).hom ≫
          (Scheme.Modules.pullback σ).map (kernel.ι (structureSheafUnit σ)) =
      (Scheme.Modules.pullback σ).map (kernelTautologicalMapTwisted E Q) :=
  calc (pullbackSourceIso E Q hσ e).hom ≫ conormalCanonicalMap E Q hσ e hqe ≫
        (Stacks.CartierConormal.conormalSheafIsoPullbackSelf σ).hom ≫
          (Scheme.Modules.pullback σ).map (kernel.ι (structureSheafUnit σ))
      = ((pullbackSourceIso E Q hσ e).hom ≫ conormalCanonicalMap E Q hσ e hqe) ≫
          ((Stacks.CartierConormal.conormalSheafIsoPullbackSelf σ).hom ≫
            (Scheme.Modules.pullback σ).map (kernel.ι (structureSheafUnit σ))) :=
        (Category.assoc _ _ _).symm
    _ = ((Scheme.Modules.pullback σ).map (idealSheafLift E Q hσ e hqe) ≫
          (Stacks.CartierConormal.conormalSheafIsoPullbackSelf σ).inv) ≫
          ((Stacks.CartierConormal.conormalSheafIsoPullbackSelf σ).hom ≫
            (Scheme.Modules.pullback σ).map (kernel.ι (structureSheafUnit σ))) :=
        congrArg (fun g => g ≫ ((Stacks.CartierConormal.conormalSheafIsoPullbackSelf σ).hom ≫
            (Scheme.Modules.pullback σ).map (kernel.ι (structureSheafUnit σ))))
          (pullbackSourceIso_hom_comp_conormalCanonicalMap E Q hσ e hqe)
    _ = (Scheme.Modules.pullback σ).map (idealSheafLift E Q hσ e hqe) ≫
          ((Stacks.CartierConormal.conormalSheafIsoPullbackSelf σ).inv ≫
            (Stacks.CartierConormal.conormalSheafIsoPullbackSelf σ).hom ≫
              (Scheme.Modules.pullback σ).map (kernel.ι (structureSheafUnit σ))) :=
        Category.assoc _ _ _
    _ = (Scheme.Modules.pullback σ).map (idealSheafLift E Q hσ e hqe) ≫
          (Scheme.Modules.pullback σ).map (kernel.ι (structureSheafUnit σ)) :=
        congrArg (fun g => (Scheme.Modules.pullback σ).map (idealSheafLift E Q hσ e hqe) ≫ g)
          (Iso.inv_hom_id_assoc (Stacks.CartierConormal.conormalSheafIsoPullbackSelf σ) _)
    _ = (Scheme.Modules.pullback σ).map (idealSheafLift E Q hσ e hqe ≫
          kernel.ι (structureSheafUnit σ)) :=
        ((Scheme.Modules.pullback σ).map_comp _ _).symm
    _ = (Scheme.Modules.pullback σ).map (kernelTautologicalMapTwisted E Q) :=
        congrArg (Scheme.Modules.pullback σ).map (idealSheafLift_comp_ι E Q hσ e hqe)

end Stacks.ProjectiveBundleConormal

end
