module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.CompletedTensorProductFibreProduct
public import StacksFrontier.AlgebraicGeometry.FormalSpace.LocalProperty
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CountablyIndexedSpectrum
public import StacksFrontier.AlgebraicGeometry.FormalSpace.PresentingRingUniqueness
public import StacksFrontier.AlgebraicGeometry.FormalSpace.SeparationAxioms
public import StacksFrontier.AlgebraicGeometry.FormalSpace.SeparatedMorphism
public import StacksFrontier.AlgebraicGeometry.Spaces.MapDescent
public import StacksFrontier.AlgebraicGeometry.FormalSpace.AffineFibreProductRefined
public import Mathlib.CategoryTheory.Sites.PreservesLimits
public import StacksFrontier.AlgebraicGeometry.FormalSpace.FormalSpectrumRefined
public import StacksFrontier.Topology.Algebra.AdicTopology.CompletionOverNoetherian
public import StacksFrontier.Topology.Algebra.AdicTopology.LocalProperties
public import StacksFrontier.Topology.Algebra.AdicTopology.NoetherianAdic
public import StacksFrontier.Topology.Algebra.AdicTopology.CompletedTensorProduct.UniversalProperty
import all StacksFrontier.AlgebraicGeometry.FormalSpace.FormalSpectrum

/-!
# The fibre product `Spf A ×_{Spf R} Spf C` as `Spf (A ⊗̂_R C)`, with its projections

Clause (3) of Stacks 0AN3 says that a fibre product `Spf A ×_{Spf R} Spf C` of McQuillan affine
formal algebraic spaces over a separated one is the formal spectrum of the completed tensor
product `A ⊗̂_R C`. The proof of Stacks 0GBD needs more: under this identification the second
projection is `Spf` of the canonical map `C → A ⊗̂_R C`, so that the morphism of
`WAdm` corresponding to `X_{ji} ×_{Y_j} Z_{jk} ⟶ Z_{jk}` is `C_{jk} → A_{ji} ⊗̂_{B_j} C_{jk}`.
This file proves that refinement.

## Main definitions

* `AlgebraicGeometry.FormalSpace.QuotientSystem.induced`: the quotient system that a continuous
  ring map `A → T` out of a ring over `S` induces on `T`, the structure morphism of
  `Spec (T ⧸ K)` being the one of a quotient spectrum of `A` mapping to it.

## Main results

* `AlgebraicGeometry.FormalSpace.exists_formalSpectrum_completedTensorProduct_iso_snd`:
  **Stacks 0AN3, clause (3)**, with the second projection of the fibre product identified with
  `Spf (C → A ⊗̂_R C)`.

## Implementation notes

Clause (3) of Stacks 0AN3 as the library states it,
`AlgebraicGeometry.FormalSpace.exists_formalSpectrum_completedTensorProduct`, gives some
isomorphism `e` of the fibre product with `Spf (A ⊗̂_R C)`, for some structure of ring over `S`
on `A ⊗̂_R C`. The two canonical maps `A → A ⊗̂_R C ← C` are made maps over `S` for the quotient
system induced from `A`; they define a morphism `κ` from `Spf (A ⊗̂_R C)` to the fibre product.
By Stacks 0AN0 the two projections of `e⁻¹` are `Spf` of maps `γ_A`, `γ_C`, and `κ ≫ e` is
`Spf τ`. The universal property of the completed tensor product gives `σ` with
`σ ∘ ι_A = γ_A` and `σ ∘ ι_C = γ_C`; then `τ ∘ σ` fixes `ι_A` and `ι_C`, so is the identity, and
`Spf σ ≫ κ = e⁻¹`, so `σ ∘ τ` is the identity by Stacks 0AN0. Hence `κ` is an isomorphism, and
its second projection is `Spf ι_C` by construction.

## References

* [Stacks Project, Tag 0AMU](https://stacks.math.columbia.edu/tag/0AMU)
* [Stacks Project, Tag 0AN0](https://stacks.math.columbia.edu/tag/0AN0)
* [Stacks Project, Tag 0AN3](https://stacks.math.columbia.edu/tag/0AN3)
* [Stacks Project, Tag 0GBD](https://stacks.math.columbia.edu/tag/0GBD)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace AlgebraicGeometry.FormalSpace

universe u

variable {𝔅 : BigFppfSite.{u}} {S : Scheme.{u}} {hS : 𝔅.Contains S}

/-- Two continuous homomorphisms over `S` with the same underlying ring map are equal. -/
theorem ContinuousHom.ext_toRingHom {A C : Type u} [CommRing A] [TopologicalSpace A]
    [CommRing C] [TopologicalSpace C] {D : QuotientSystem 𝔅 S hS A}
    {E : QuotientSystem 𝔅 S hS C} {g g' : ContinuousHom D E} (h : g.toRingHom = g'.toRingHom) :
    g = g' := by
  cases g
  cases g'
  cases h
  rfl

section Induced

variable {A T : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [IsLinearTopology A A] [CommRing T] [TopologicalSpace T]
  (hA : TopologicalRing.IsWeaklyAdmissible A) (DA : QuotientSystem 𝔅 S hS A) (ι : A →+* T)
  (hι : Continuous ι)

omit [IsTopologicalRing A] [IsLinearTopology A A] in
/-- Two weak ideals of definition of `A` below the preimage of a weak ideal of definition `K` of
`T` induce the same structure morphism `Spec (T ⧸ K) ⟶ S`. -/
theorem quotientMap_comp_overS_eq
    (K : { I : Ideal T // TopologicalRing.IsWeakIdealOfDefinition I })
    (J J' : { I : Ideal A // TopologicalRing.IsWeakIdealOfDefinition I })
    (hJ : J.1 ≤ Ideal.comap ι K.1) (hJ' : J'.1 ≤ Ideal.comap ι K.1) :
    Spec.map (CommRingCat.ofHom (Ideal.quotientMap K.1 ι hJ)) ≫ DA.overS J =
      Spec.map (CommRingCat.ofHom (Ideal.quotientMap K.1 ι hJ')) ≫ DA.overS J' := by
  let M : { I : Ideal A // TopologicalRing.IsWeakIdealOfDefinition I } :=
    ⟨J.1 ⊓ J'.1, TopologicalRing.isWeakIdealOfDefinition_inf_of_isOpen_right J.2 J'.2.1⟩
  have hM : M.1 ≤ Ideal.comap ι K.1 := inf_le_left.trans hJ
  have key : ∀ (L : { I : Ideal A // TopologicalRing.IsWeakIdealOfDefinition I })
      (hL : L.1 ≤ Ideal.comap ι K.1) (hML : M.1 ≤ L.1),
      Spec.map (CommRingCat.ofHom (Ideal.quotientMap K.1 ι hL)) ≫ DA.overS L =
        Spec.map (CommRingCat.ofHom (Ideal.quotientMap K.1 ι hM)) ≫ DA.overS M := by
    intro L hL hML
    rw [← DA.compatible M L hML, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 3
    apply Ideal.Quotient.ringHom_ext
    ext a
    rfl
  rw [key J hJ inf_le_left, key J' hJ' inf_le_right]

include hA hι in
/-- Every weak ideal of definition of `T` contains the image of one of `A`. -/
theorem exists_weakIdeal_le_comap
    (K : { I : Ideal T // TopologicalRing.IsWeakIdealOfDefinition I }) :
    ∃ J : { I : Ideal A // TopologicalRing.IsWeakIdealOfDefinition I }, J.1 ≤ Ideal.comap ι K.1 :=
  exists_weakIdeal_below_comap hA ι hι K

/-- **The quotient system induced along a continuous ring map.** Given a ring `A` over `S` and a
continuous ring map `ι : A → T`, the spectrum of a quotient `T ⧸ K` by a weak ideal of
definition maps to `S` through the spectrum of any quotient of `A` mapping to it. Membership of
the site is taken from a given quotient system `D₀` on `T`. -/
def QuotientSystem.induced (D₀ : QuotientSystem 𝔅 S hS T) : QuotientSystem 𝔅 S hS T where
  inSite := D₀.inSite
  overS K := Spec.map (CommRingCat.ofHom (Ideal.quotientMap K.1 ι
      (exists_weakIdeal_le_comap hA ι hι K).choose_spec)) ≫
    DA.overS (exists_weakIdeal_le_comap hA ι hι K).choose
  compatible K L h := by
    rw [quotientMap_comp_overS_eq DA ι L _ (exists_weakIdeal_le_comap hA ι hι K).choose _
      ((exists_weakIdeal_le_comap hA ι hι K).choose_spec.trans (Ideal.comap_mono h)),
      ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 3
    apply Ideal.Quotient.ringHom_ext
    ext a
    rfl

/-- For any weak ideal of definition `J` of `A` with `J ≤ ι⁻¹ K`, the structure map of
`Spec (T ⧸ K)` in the induced quotient system is the spectrum of `A ⧸ J → T ⧸ K` followed by the
structure map of `Spec (A ⧸ J)`. -/
theorem QuotientSystem.induced_overS (D₀ : QuotientSystem 𝔅 S hS T)
    (K : { I : Ideal T // TopologicalRing.IsWeakIdealOfDefinition I })
    (J : { I : Ideal A // TopologicalRing.IsWeakIdealOfDefinition I })
    (hJ : J.1 ≤ Ideal.comap ι K.1) :
    (QuotientSystem.induced hA DA ι hι D₀).overS K =
      Spec.map (CommRingCat.ofHom (Ideal.quotientMap K.1 ι hJ)) ≫ DA.overS J :=
  quotientMap_comp_overS_eq DA ι K _ J _ hJ

/-- The map along which a quotient system is induced is a continuous homomorphism over `S`. -/
def QuotientSystem.inducedHom (D₀ : QuotientSystem 𝔅 S hS T) :
    ContinuousHom DA (QuotientSystem.induced hA DA ι hι D₀) where
  toRingHom := ι
  continuous := hι
  overS J K h := (QuotientSystem.induced_overS hA DA ι hι D₀ K J h).symm

end Induced

section InducedComp

variable {R A C T : Type u} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
  [IsLinearTopology R R] [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [IsLinearTopology A A] [CommRing C] [TopologicalSpace C] [CommRing T] [TopologicalSpace T]
  (hR : TopologicalRing.IsWeaklyAdmissible R) (hA : TopologicalRing.IsWeaklyAdmissible A)
  {DR : QuotientSystem 𝔅 S hS R} {DA : QuotientSystem 𝔅 S hS A} {DC : QuotientSystem 𝔅 S hS C}
  (φA : ContinuousHom DR DA) (φC : ContinuousHom DR DC) (ιA : A →+* T) (hιA : Continuous ιA)
  (ιC : C →+* T) (hιC : Continuous ιC)
  (hcomp : ιA.comp φA.toRingHom = ιC.comp φC.toRingHom) (D₀ : QuotientSystem 𝔅 S hS T)

/-- A continuous ring map `C → T` agreeing over `R` with the map along which the quotient system
of `T` is induced is a homomorphism over `S`. -/
def QuotientSystem.inducedHomOfComp :
    ContinuousHom DC (QuotientSystem.induced hA DA ιA hιA D₀) where
  toRingHom := ιC
  continuous := hιC
  overS J K h := by
    obtain ⟨JA, hJA⟩ := exists_weakIdeal_le_comap hA ιA hιA K
    obtain ⟨L₁, hL₁⟩ := exists_weakIdeal_below_comap hR φA.toRingHom φA.continuous JA
    obtain ⟨L₂, hL₂⟩ := exists_weakIdeal_below_comap hR φC.toRingHom φC.continuous J
    let L : { I : Ideal R // TopologicalRing.IsWeakIdealOfDefinition I } :=
      ⟨L₁.1 ⊓ L₂.1, TopologicalRing.isWeakIdealOfDefinition_inf_of_isOpen_right L₁.2 L₂.2.1⟩
    have hLA : L.1 ≤ Ideal.comap φA.toRingHom JA.1 := inf_le_left.trans hL₁
    have hLC : L.1 ≤ Ideal.comap φC.toRingHom J.1 := inf_le_right.trans hL₂
    rw [QuotientSystem.induced_overS hA DA ιA hιA D₀ K JA hJA, ← φA.overS L JA hLA,
      ← φC.overS L J hLC, ← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp,
      ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
    congr 3
    apply Ideal.Quotient.ringHom_ext
    ext r
    exact congrArg (Ideal.Quotient.mk K.1) (RingHom.congr_fun hcomp r).symm

/-- The underlying ring map of `QuotientSystem.inducedHomOfComp` is `ιC`. -/
theorem QuotientSystem.inducedHomOfComp_toRingHom :
    (QuotientSystem.inducedHomOfComp hR hA φA φC ιA hιA ιC hιC hcomp D₀).toRingHom = ιC := rfl

end InducedComp

section FibreProduct

attribute [local instance] sheaf_hasColimits

/-- Continuous homomorphisms of weakly admissible rings with the same map on formal spectra are
equal (Stacks 0AN0). -/
private theorem continuousHom_eq_of_formalSpectrumMap_eq {R A : Type u} [CommRing R]
    [TopologicalSpace R] [IsTopologicalRing R] [IsLinearTopology R R] [CommRing A]
    [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A]
    (hR : TopologicalRing.IsWeaklyAdmissible R) (hA : TopologicalRing.IsWeaklyAdmissible A)
    {D : QuotientSystem 𝔅 S hS R} {E : QuotientSystem 𝔅 S hS A} {y₁ y₂ : ContinuousHom D E}
    (h : formalSpectrumMap hR y₁ = formalSpectrumMap hR y₂) : y₁ = y₂ :=
  (existsUnique_continuousHom_formalSpectrumMap_eq hR hA (formalSpectrumMap hR y₂)).unique h rfl

variable {R A C : Type u} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
  [IsLinearTopology R R] [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [IsLinearTopology A A] [CommRing C] [TopologicalSpace C] [IsTopologicalRing C]
  [IsLinearTopology C C]

/-- **Stacks 0AN3, clause (3), with the second projection.** Let `X ⟶ Z` and `Y ⟶ Z` be
morphisms of fppf sheaves over `S` with `Z` separated, which are, through identifications of
`X`, `Y`, `Z` with the formal spectra of weakly admissible topological rings `A`, `C`, `R` over
`S`, the formal spectra of continuous homomorphisms `R → A` and `R → C` over `S`. Then the fibre
product `X ×_Z Y` is the formal spectrum of the completed tensor product `A ⊗̂_R C`, which is
weakly admissible, by an identification under which the second projection is the formal
spectrum of the canonical map `C → A ⊗̂_R C`, a continuous homomorphism over `S`. -/
theorem exists_formalSpectrum_completedTensorProduct_iso_snd
    (hA : TopologicalRing.IsWeaklyAdmissible A) (hC : TopologicalRing.IsWeaklyAdmissible C)
    (hR : TopologicalRing.IsWeaklyAdmissible R) (DA : QuotientSystem 𝔅 S hS A)
    (DC : QuotientSystem 𝔅 S hS C) (DR : QuotientSystem 𝔅 S hS R)
    {X Y Z : FppfSheaf 𝔅 S hS} (f : X ⟶ Z) (g : Y ⟶ Z) (eX : X ≅ formalSpectrum DA)
    (eY : Y ≅ formalSpectrum DC) (eZ : Z ≅ formalSpectrum DR)
    (hZsep : IsSeparated 𝔅 S hS Z) (φA : ContinuousHom DR DA) (φC : ContinuousHom DR DC)
    (hf : formalSpectrumMap hR φA = eX.inv ≫ f ≫ eZ.hom)
    (hg : formalSpectrumMap hR φC = eY.inv ≫ g ≫ eZ.hom) :
    letI : Algebra R A := φA.toRingHom.toAlgebra
    letI : Algebra R C := φC.toRingHom.toAlgebra
    ∃ (DT : QuotientSystem 𝔅 S hS
        (TopologicalRing.CompletedTensorProduct (R := R) (M := A) (N := C)))
      (ιC : ContinuousHom DC DT) (E : pullback f g ≅ formalSpectrum DT),
      TopologicalRing.IsWeaklyAdmissible
          (TopologicalRing.CompletedTensorProduct (R := R) (M := A) (N := C)) ∧
        ιC.toRingHom = TopologicalRing.completedTensorProductInr ∧
          E.hom ≫ formalSpectrumMap hC ιC = pullback.snd f g ≫ eY.hom := by
  let : Algebra R A := φA.toRingHom.toAlgebra
  let : Algebra R C := φC.toRingHom.toAlgebra
  obtain ⟨D₀, hT, ⟨e₀⟩⟩ := exists_formalSpectrum_completedTensorProduct 𝔅 S hS hA hC hR DA DC DR
    f g eX eY eZ hZsep φA φC hf hg
  set T := TopologicalRing.CompletedTensorProduct (R := R) (M := A) (N := C)
  let ιA : A →+* T := TopologicalRing.completedTensorProductInl
  let ιC : C →+* T := TopologicalRing.completedTensorProductInr
  have hιA : Continuous ιA := TopologicalRing.continuous_completedTensorProductInl
  have hιC : Continuous ιC := TopologicalRing.continuous_completedTensorProductInr
  have hcomp : ιA.comp φA.toRingHom = ιC.comp φC.toRingHom :=
    TopologicalRing.completedTensorProductInl_comp_algebraMap
  let DT := QuotientSystem.induced hA DA ιA hιA D₀
  let iA : ContinuousHom DA DT := QuotientSystem.inducedHom hA DA ιA hιA D₀
  let iC : ContinuousHom DC DT :=
    QuotientSystem.inducedHomOfComp hR hA φA φC ιA hιA ιC hιC hcomp D₀
  -- the two composites to `Spf R` agree
  have hfX : eX.inv ≫ f = formalSpectrumMap hR φA ≫ eZ.inv := by
    rw [hf]; simp
  have hgY : eY.inv ≫ g = formalSpectrumMap hR φC ≫ eZ.inv := by
    rw [hg]; simp
  have hiAC : ContinuousHom.comp hA hR iA φA = ContinuousHom.comp hC hR iC φC :=
    ContinuousHom.ext_toRingHom hcomp
  let κ : formalSpectrum DT ⟶ pullback f g :=
    pullback.lift (formalSpectrumMap hA iA ≫ eX.inv) (formalSpectrumMap hC iC ≫ eY.inv) (by
      rw [Category.assoc, Category.assoc, hfX, hgY, ← Category.assoc, ← Category.assoc,
        formalSpectrumMap_comp_eq, formalSpectrumMap_comp_eq, hiAC])
  -- the projections of `e₀⁻¹`
  obtain ⟨γA, hγA, -⟩ := existsUnique_continuousHom_formalSpectrumMap_eq hA hT
    (e₀.inv ≫ pullback.fst f g ≫ eX.hom)
  obtain ⟨γC, hγC, -⟩ := existsUnique_continuousHom_formalSpectrumMap_eq hC hT
    (e₀.inv ≫ pullback.snd f g ≫ eY.hom)
  obtain ⟨τ, hτ, -⟩ := existsUnique_continuousHom_formalSpectrumMap_eq hT hT (κ ≫ e₀.hom)
  have hτA : τ.toRingHom.comp γA.toRingHom = ιA :=
    congrArg ContinuousHom.toRingHom (continuousHom_eq_of_formalSpectrumMap_eq hA hT
      (y₁ := ContinuousHom.comp hT hA τ γA) (y₂ := iA)
      (by rw [← formalSpectrumMap_comp_eq, hτ, hγA]; simp [κ, pullback.lift_fst_assoc]))
  have hτC : τ.toRingHom.comp γC.toRingHom = ιC :=
    congrArg ContinuousHom.toRingHom (continuousHom_eq_of_formalSpectrumMap_eq hC hT
      (y₁ := ContinuousHom.comp hT hC τ γC) (y₂ := iC)
      (by rw [← formalSpectrumMap_comp_eq, hτ, hγC]; simp [κ, pullback.lift_snd_assoc]))
  have hγR : γA.toRingHom.comp (algebraMap R A) = γC.toRingHom.comp (algebraMap R C) :=
    congrArg ContinuousHom.toRingHom (continuousHom_eq_of_formalSpectrumMap_eq hR hT
      (y₁ := ContinuousHom.comp hA hR γA φA) (y₂ := ContinuousHom.comp hC hR γC φC)
      (by
        rw [← formalSpectrumMap_comp_eq, ← formalSpectrumMap_comp_eq, hγA, hγC, hf, hg]
        simp [pullback.condition_assoc]))
  let σ : T →+* T := TopologicalRing.completedTensorProductLift γA.toRingHom γC.toRingHom
    γA.continuous γC.continuous hγR
  have hσ : Continuous σ := TopologicalRing.continuous_completedTensorProductLift _ _ _ _ _
  have hσA : σ.comp ιA = γA.toRingHom :=
    TopologicalRing.completedTensorProductLift_comp_inl _ _ _ _ _
  have hσC : σ.comp ιC = γC.toRingHom :=
    TopologicalRing.completedTensorProductLift_comp_inr _ _ _ _ _
  let sS : ContinuousHom DT D₀ :=
    { toRingHom := σ
      continuous := hσ
      overS := fun K' K h ↦ by
        obtain ⟨J, hJ⟩ := exists_weakIdeal_le_comap hA ιA hιA K'
        have hJK : J.1 ≤ Ideal.comap γA.toRingHom K.1 := fun x hx ↦ by
          rw [Ideal.mem_comap, ← hσA]
          exact h (hJ hx)
        show _ ≫ (QuotientSystem.induced hA DA ιA hιA D₀).overS K' = _
        rw [QuotientSystem.induced_overS hA DA ιA hιA D₀ K' J hJ, ← γA.overS J K hJK,
          ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
        congr 3
        apply Ideal.Quotient.ringHom_ext
        ext a
        exact congrArg (Ideal.Quotient.mk K.1) (RingHom.congr_fun hσA a) }
  have hsκ : formalSpectrumMap hT sS ≫ κ = e₀.inv := by
    refine pullback.hom_ext ?_ ?_
    · have h : ContinuousHom.comp hT hA sS iA = γA := ContinuousHom.ext_toRingHom hσA
      simp only [κ, Category.assoc, pullback.lift_fst]
      rw [← Category.assoc, formalSpectrumMap_comp_eq, h, hγA]
      simp
    · have h : ContinuousHom.comp hT hC sS iC = γC := ContinuousHom.ext_toRingHom hσC
      simp only [κ, Category.assoc, pullback.lift_snd]
      rw [← Category.assoc, formalSpectrumMap_comp_eq, h, hγC]
      simp
  have hτσ : τ.toRingHom.comp σ = RingHom.id T := by
    refine TopologicalRing.completedTensorProduct_ringHom_ext (τ.continuous.comp hσ)
      continuous_id ?_ ?_
    · rw [RingHom.comp_assoc, hσA, hτA]; rfl
    · rw [RingHom.comp_assoc, hσC, hτC]; rfl
  have hτs : formalSpectrumMap hT τ ≫ formalSpectrumMap hT sS = 𝟙 _ := by
    rw [formalSpectrumMap_comp_eq]
    exact formalSpectrumMap_id hT _ hτσ
  let E : pullback f g ≅ formalSpectrum DT :=
    { hom := e₀.hom ≫ formalSpectrumMap hT sS
      inv := κ
      hom_inv_id := by rw [Category.assoc, hsκ, Iso.hom_inv_id]
      inv_hom_id := by rw [← Category.assoc, ← hτ, hτs] }
  refine ⟨DT, iC, E, hT, rfl, ?_⟩
  have hκC : formalSpectrumMap hC iC = E.inv ≫ pullback.snd f g ≫ eY.hom := by
    show _ = κ ≫ pullback.snd f g ≫ eY.hom
    simp [κ, pullback.lift_snd_assoc]
  rw [hκC, Iso.hom_inv_id_assoc]

end FibreProduct

section ChartMap

attribute [local instance] Algebra.TensorProduct.rightAlgebra

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The chart map of a fibre product of charts, for a property stable under base change.**
Let `P` be stable under base change by `Q` for Noetherian adic topological rings, invariant
under isomorphism of source and target as Situation 0CBA assumes. Let `t : U ⟶ V` and
`s : W ⟶ V` be morphisms of affine formal algebraic spaces, `U` and `V` being formal spectra of
Noetherian adic rings, with `P` on the chart map of `t` and `Q` on the chart map of `s`. Then
`P` holds on the chart map of the second projection `U ×_V W ⟶ W`.

This is the step of the proof of Stacks 0GBD that reads `U ×_V W ⟶ W` as
`C → A ⊗̂_R C` (Stacks 0AN3, through
`AlgebraicGeometry.FormalSpace.exists_formalSpectrum_completedTensorProduct_iso_snd`) and
applies stability under base change. A presentation of the chart map by other rings differs
from this one by isomorphisms of topological rings (Stacks 0AN0), which `P` does not see. -/
theorem hasPropertyOnAffineChartMap_pullback_snd
    (P Q : ∀ {R₁ R₂ : Type u} [CommRing R₁] [TopologicalSpace R₁] [IsTopologicalRing R₁]
      [CommRing R₂] [TopologicalSpace R₂] [IsTopologicalRing R₂], (R₁ →+* R₂) → Prop)
    (hPQ : TopologicalRing.IsStableUnderBaseChangeBy.{u} P Q)
    (hPiso : ∀ {B A B' A' : Type u}
      [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] [IsLinearTopology B B]
      [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A]
      [CommRing B'] [TopologicalSpace B'] [IsTopologicalRing B'] [IsLinearTopology B' B']
      [CommRing A'] [TopologicalSpace A'] [IsTopologicalRing A'] [IsLinearTopology A' A']
      (eB : B ≃+* B') (eA : A ≃+* A'), Continuous eB → Continuous eB.symm →
      Continuous eA → Continuous eA.symm → ∀ (f : B →+* A), Continuous f →
      TopologicalRing.IsNoetherianAdic B → TopologicalRing.IsNoetherianAdic A →
      TopologicalRing.IsNoetherianAdic B' → TopologicalRing.IsNoetherianAdic A' →
      (P f ↔ P ((eA.toRingHom.comp f).comp eB.symm.toRingHom)))
    {U V W : FppfSheaf B S hS} (t : U ⟶ V) (s : W ⟶ V) (hV : IsAffineFormalAlgebraicSpace B S hS V)
    (PU : SpfPresentation B S hS U) (hPU : TopologicalRing.IsNoetherianAdic PU.ring)
    (PV : SpfPresentation B S hS V) (hPV : TopologicalRing.IsNoetherianAdic PV.ring)
    (ht : HasPropertyOnAffineChartMap B S hS TopologicalRing.IsNoetherianAdic P t)
    (hs : HasPropertyOnAffineChartMap B S hS TopologicalRing.IsNoetherianAdic Q s) :
    HasPropertyOnAffineChartMap B S hS TopologicalRing.IsNoetherianAdic P (pullback.snd t s) := by
  intro C' R' _ _ _ _ _ _ _ _ hC' hR' hwC' D' E' eP eW φ' hφ'
  obtain ⟨eU⟩ := PU.iso
  obtain ⟨eV⟩ := PV.iso
  have hwA : TopologicalRing.IsWeaklyAdmissible PU.ring := hPU.1.isWeaklyAdmissible
  have hwR : TopologicalRing.IsWeaklyAdmissible PV.ring := hPV.1.isWeaklyAdmissible
  have hwR' : TopologicalRing.IsWeaklyAdmissible R' := hR'.1.isWeaklyAdmissible
  obtain ⟨φA, hφA, -⟩ := existsUnique_continuousHom_formalSpectrumMap_eq hwR hwA
    (eU.inv ≫ t ≫ eV.hom)
  obtain ⟨φC, hφC, -⟩ := existsUnique_continuousHom_formalSpectrumMap_eq hwR hwC'
    (eW.inv ≫ s ≫ eV.hom)
  have hPA : P φA.toRingHom := ht PV.ring PU.ring hPV hPU hwR PV.system PU.system eU eV φA
    (by rw [hφA]; simp)
  have hQC : Q φC.toRingHom := hs PV.ring C' hPV hC' hwR PV.system D' eW eV φC
    (by rw [hφC]; simp)
  let : Algebra PV.ring PU.ring := φA.toRingHom.toAlgebra
  let : Algebra PV.ring C' := φC.toRingHom.toAlgebra
  have : IsNoetherianRing PV.ring := hPV.2
  have : IsNoetherianRing PU.ring := hPU.2
  have : IsNoetherianRing C' := hC'.2
  obtain ⟨hTadic, hTnoeth, hPT⟩ := hPQ.baseChange hPV.1 hPU.1 hC'.1 φA.continuous φC.continuous
    hPA hQC
  obtain ⟨DT, ιC, E, hwT, hιC, hE⟩ := exists_formalSpectrum_completedTensorProduct_iso_snd
    hwA hwC' hwR PU.system D' PV.system t s eU eW eV
    (IsAffineFormalAlgebraicSpace.isSeparated B S hS hV) φA φC hφA hφC
  obtain ⟨g, -, ρ, hg, -, hρ, -, hρc, hρc'⟩ :=
    exists_continuous_ringEquiv_of_formalSpectrum_iso hwR' hwT (E.symm ≪≫ eP)
  have hgφ : ContinuousHom.comp hwR' hwC' g φ' = ιC := by
    refine continuousHom_eq_of_formalSpectrumMap_eq hwC' hwT ?_
    rw [← formalSpectrumMap_comp_eq, hg]
    have h1 : eP.hom ≫ formalSpectrumMap hwC' φ' = pullback.snd t s ≫ eW.hom := by
      rw [hφ']; simp
    have h2 : formalSpectrumMap hwC' ιC = E.inv ≫ pullback.snd t s ≫ eW.hom := by
      rw [← hE]; simp
    simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, h1, h2]
  have hρφ : ∀ x, ρ (φ'.toRingHom x) = TopologicalRing.completedTensorProductInr x := by
    intro x
    rw [hρ, ← hιC, ← hgφ]
    rfl
  have key := (hPiso (RingEquiv.refl C') ρ.symm continuous_id continuous_id hρc' hρc
    (TopologicalRing.completedTensorProductInr) TopologicalRing.continuous_completedTensorProductInr
    hC' ⟨hTadic, hTnoeth⟩ hC' hR').mp hPT
  convert key using 1
  ext x
  simp only [RingHom.coe_comp, Function.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe,
    RingEquiv.symm_refl, RingEquiv.refl_apply]
  rw [← hρφ, RingEquiv.symm_apply_apply]

end ChartMap

end AlgebraicGeometry.FormalSpace

end
