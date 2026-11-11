module

public import StacksFrontier.Deformation.ToposThickening.CurvatureCorrection
import StacksCore.Tactic.StacksAttribute

/-!
# A bounded above complex lifts across a square-zero thickening iff its obstruction vanishes

Let `C` be a site, `f : O ⟶ O₀` a surjection of sheaves of commutative rings whose kernel is an
ideal sheaf `I` of square zero, and `K₀ ∈ D⁻(O₀)`. Stacks 0DIW: the canonical class
`ω(K₀) ∈ Ext²_{O₀}(K₀, K₀ ⊗^L_{O₀} I)` of Tag 0DIU vanishes if and only if there is
`K ∈ D⁻(O)` with `K ⊗^L_O O₀ ≅ K₀` in `D(O₀)`.

The implication `(2) ⇒ (1)` is `Deformation.ComplexLift.omega_eq_zero_of_nonempty_derivedLift`.
For `(1) ⇒ (2)` we follow the source. Choose a bounded above flat lift `F` of `K₀` with
reduction `F₀` and curvature `c : F₀ ⟶ (F₀ ⊗ I)[2]`. That `ω(K₀) = 0` says `c` is zero in
`D(O₀)`, so by the calculus of fractions there is a quasi-isomorphism `α : G₀ ⟶ F₀` with
`α ∘ c` null-homotopic, `α ∘ c = d ∘ h + h ∘ d`; and `G₀` may be taken bounded above. The
corrected complex `H = F ×_{F₀} G₀` of `Deformation.ComplexLift.correctedComplex` is an extension
`0 ⟶ (F₀ ⊗ I)|_O ⟶ H ⟶ G₀|_O ⟶ 0`. A bounded above flat resolution `E ⟶ H` reduces to
`δ : E₀ ⟶ G₀`, which is a quasi-isomorphism by the descending induction of
`Deformation.ComplexLift.quasiIso_of_shortExact_comparison`; so `K = E` satisfies
`K ⊗^L_O O₀ ≅ E₀ ≅ G₀ ≅ F₀ ≅ K₀`.

## Main results

* `Deformation.ComplexLift.Q_map_curvatureMap_eq_zero`: `ω(K₀) = 0` makes the curvature of any
  flat lift vanish in `D(O₀)`.
* `Deformation.ComplexLift.exists_quasiIso_homotopy_of_Q_map_eq_zero`: a map of complexes that
  vanishes in the derived category becomes null-homotopic after precomposition with a
  quasi-isomorphism.
* `Deformation.ComplexLift.exists_correction_of_homotopy`: the homotopy, read as the maps
  `h^n : G₀^n ⟶ F₀^{n + 1} ⊗ I`.
* `Deformation.ComplexLift.exists_correction_of_omega_eq_zero`: the data `(F, α, h)` of the
  source, from `ω(K₀) = 0`.
* `Deformation.ComplexLift.flatComplexEmb_comparison` and
  `Deformation.ComplexLift.quasiIso_correctedTranspose`: the reduction `δ : E₀ ⟶ G₀` of a flat
  resolution `E` of the corrected complex is a quasi-isomorphism.
* `Deformation.ComplexLift.nonempty_derivedLift_of_flatComplex`: a bounded above complex of flat
  `O`-modules whose reduction represents `K₀` is a lift of `K₀`.
* `Deformation.ComplexLift.nonempty_derivedLift_of_omega_eq_zero` and
  `Deformation.ComplexLift.omega_eq_zero_iff_nonempty_derivedLift`: the criterion for the class
  `omega` stated against a supplied `Deformation.ComplexLift.DerivedIdealTensor`, a datum that
  exists only when `I` is flat over `O₀`.

## Implementation notes

The tagged statement of Tag 0DIW, in
`StacksFrontier.Deformation.ToposThickening.ObstructionLiftCriterionDerivedTensor`, is
`Deformation.ComplexLift.tensorOmegaMinus_eq_zero_iff_nonempty_derivedLift`:
there `ω(K₀)` is `Deformation.ComplexLift.tensorOmegaMinus`, with values in the derived tensor
product `Deformation.ComplexLift.derivedTensorRight I` constructed from flat resolutions, `K₀` is
an arbitrary object of `D⁻(O₀)`, and `- ⊗^L_O O₀` is the constructed derived base change
`Deformation.ComplexLift.derivedExtensionOfScalarsData`; nothing is assumed of `I` beyond being a
square-zero kernel.

The older form below, `Deformation.ComplexLift.omega_eq_zero_iff_nonempty_derivedLift`, states
`ω` against a supplied `Deformation.ComplexLift.DerivedIdealTensor`, whose comparison is natural
on all complexes; such a datum exists only when `I` is flat over `O₀` (see the implementation
notes of `StacksFrontier.Deformation.ToposThickening.CurvatureClassDerivedTensor`), so that form is
the lemma for flat `I` only. An object of `D⁻(O₀)` is given as `E : DerivedCategory.Minus`
together with a complex `K₀` and an
isomorphism `Q(K₀) ≅ E`: the canonical class `ω` of Tag 0DIU is defined on complexes
(`Deformation.ComplexLift.omega`), every object of `D(O₀)` is of the form `Q(K₀)`, and `ω` is
natural along isomorphisms of `D(O₀)` (`Deformation.ComplexLift.omega_natural_derived`), so its
vanishing does not depend on the representative. Clause (2) is a
`Deformation.ComplexLift.DerivedLift`, an object `K` of `D⁻(O)` with an isomorphism
`K ⊗^L_O O₀ ≅ K₀` in `D(O₀)`, for an arbitrary derived base change `T` along `f`; any two are
canonically isomorphic. The derived tensor product with `I` is the datum
`Deformation.ComplexLift.DerivedIdealTensor` against which the base states `ω`. The surjection
is `Sheaf.IsLocallySurjective f`, and the square-zero kernel is
`Deformation.ComplexLift.SquareZeroIdeal`.

## References

* [Stacks Project, Tag 0DIW](https://stacks.math.columbia.edu/tag/0DIW)
* [Stacks Project, Tag 0DIU](https://stacks.math.columbia.edu/tag/0DIU)
* [Stacks Project, Tag 0DIV](https://stacks.math.columbia.edu/tag/0DIV)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.SheafOfModules.ComplexLifting (GradedDifferential BaseChangeTo
  IsExtensionOfScalars)

universe v u w d d₀

namespace Deformation.ComplexLift

attribute [-instance] CategoryTheory.catToReflQuiver

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{max u v w} RingCat.{max u v w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v w}]
  [HasSheafify J AddCommGrpCat.{max u v w}]
  {O O₀ : Sheaf J CommRingCat.{max u v w}} {f : O ⟶ O₀}
  {I : SheafMod O₀} [((Stacks.SheafOfModules.Tensor.sheafTensor O₀).flip.obj I).Additive]
  {S : SquareZeroIdeal f I}

section Homotopy

variable [HasDerivedCategory.{d₀} (SheafMod O₀)]

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat)] in
/-- **A map of complexes vanishing in the derived category is null-homotopic after precomposing
with a quasi-isomorphism**: the quasi-isomorphisms of the homotopy category admit a right
calculus of fractions, and the derived category is its localization. -/
theorem exists_quasiIso_homotopy_of_Q_map_eq_zero {A B : CochainComplex (SheafMod O₀) ℤ}
    (c : A ⟶ B) (hc : DerivedCategory.Q.map c = 0) :
    ∃ (G : CochainComplex (SheafMod O₀) ℤ) (α : G ⟶ A), QuasiIso α ∧
      Nonempty (Homotopy (α ≫ c) 0) := by
  let Qu := HomotopyCategory.quotient (SheafMod O₀) (ComplexShape.up ℤ)
  have h1 : DerivedCategory.Qh.map (Qu.map c) = DerivedCategory.Qh.map (Qu.map 0) := by
    have e := (DerivedCategory.quotientCompQhIso (SheafMod O₀)).hom.naturality c
    rw [hc, comp_zero] at e
    rw [CategoryTheory.Functor.map_zero, CategoryTheory.Functor.map_zero]
    rw [← cancel_mono ((DerivedCategory.quotientCompQhIso (SheafMod O₀)).hom.app B), zero_comp]
    exact e
  obtain ⟨X, s, hs, hfac⟩ := (MorphismProperty.map_eq_iff_precomp DerivedCategory.Qh
    (W := HomotopyCategory.quasiIso (SheafMod O₀) (ComplexShape.up ℤ)) _ _).1 h1
  obtain ⟨G, rfl⟩ := HomotopyCategory.quotient_obj_surjective X
  obtain ⟨α, rfl⟩ := Qu.map_surjective s
  refine ⟨G, α, (HomotopyCategory.quotient_map_mem_quasiIso_iff α).1 hs,
    ⟨HomotopyCategory.homotopyOfEq _ _ ?_⟩⟩
  rw [CategoryTheory.Functor.map_comp, hfac, CategoryTheory.Functor.map_zero, comp_zero,
    CategoryTheory.Functor.map_zero]

/-- The quasi-isomorphism may moreover be taken from a complex vanishing above any bound of the
target's source. -/
theorem exists_bounded_quasiIso_homotopy_of_Q_map_eq_zero {A B : CochainComplex (SheafMod O₀) ℤ}
    (b : ℤ) [A.IsStrictlyLE b] (c : A ⟶ B) (hc : DerivedCategory.Q.map c = 0) :
    ∃ (G : CochainComplex (SheafMod O₀) ℤ) (_ : G.IsStrictlyLE b) (α : G ⟶ A), QuasiIso α ∧
      Nonempty (Homotopy (α ≫ c) 0) := by
  obtain ⟨G, α, hα, ⟨h⟩⟩ := exists_quasiIso_homotopy_of_Q_map_eq_zero c hc
  have : G.IsLE b := by
    rw [CochainComplex.isLE_iff]
    intro i hi
    rw [exactAt_iff_of_quasiIsoAt α i]
    exact (HomologicalComplex.exactAt_iff _ i).2
      (ShortComplex.exact_of_isZero_X₂ _ (A.isZero_of_isStrictlyLE b i hi))
  obtain ⟨P, p, hp, -, hP⟩ := exists_isFlat_quasiIso_isStrictlyLE_of_isLE O₀ b G
  refine ⟨P, hP, p ≫ α, inferInstance, ⟨?_⟩⟩
  exact (Homotopy.ofEq (Category.assoc _ _ _)).trans ((h.compLeft p).trans (Homotopy.ofEq
    comp_zero))

end Homotopy

section Correction

variable {K₀ : CochainComplex (SheafMod O₀) ℤ} {L : FlatLift f K₀} (T : IdealKernel S L)

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat)] [HasSheafify J AddCommGrpCat]
  [J.WEqualsLocallyBijective AddCommGrpCat] in
/-- For a family `φ i j : A^i ⟶ Y^{j + 2}` and `j = j'`, the composites of `φ i j` and `φ i j'`
with the identifications `Y^{j + 2} ≅ Y^m` and `Y^{j' + 2} ≅ Y^m` agree. -/
theorem homotopy_hom_comp_XIsoOfEq {A Y : CochainComplex (SheafMod O₀) ℤ}
    (φ : ∀ i j : ℤ, A.X i ⟶ Y.X (j + 2)) (i j j' m : ℤ) (h : j = j') (h1 : j + 2 = m)
    (h2 : j' + 2 = m) : φ i j ≫ (Y.XIsoOfEq h1).hom = φ i j' ≫ (Y.XIsoOfEq h2).hom := by
  subst h
  rfl

/-- **The homotopy, read degreewise.** A null-homotopy of `α ∘ c`, with `c` the curvature class
of a flat lift, is a family `h^n : G₀^n ⟶ F₀^{n + 1} ⊗ I` with `α ∘ c = d ∘ h + h ∘ d`. -/
theorem exists_correction_of_homotopy {G₀ : CochainComplex (SheafMod O₀) ℤ}
    (α : G₀ ⟶ L.baseChange.complex) (h : Homotopy (α ≫ curvatureMap T) 0) :
    ∃ k : ∀ n : ℤ, G₀.X n ⟶ (L.idealTensor (I := I)).X (n + 1), ∀ n : ℤ,
      α.f n ≫ curvature T n =
        k n ≫ (L.idealTensor (I := I)).d (n + 1) (n + 1 + 1) + G₀.d n (n + 1) ≫ k (n + 1) := by
  refine ⟨fun n => h.hom n (n - 1) ≫
    ((L.idealTensor (I := I)).XIsoOfEq (by omega : n - 1 + 2 = n + 1)).hom, fun n => ?_⟩
  have hc := h.comm n
  rw [dNext_eq _ (show (ComplexShape.up ℤ).Rel n (n + 1) by simp),
    prevD_eq _ (show (ComplexShape.up ℤ).Rel (n - 1) n by simp)] at hc
  simp only [HomologicalComplex.comp_f, curvatureMap_f, HomologicalComplex.zero_f, add_zero,
    CochainComplex.shiftFunctor_obj_d'] at hc
  have h2 : ((2 : ℤ)).negOnePow = 1 := by decide
  simp only [h2, one_smul] at hc
  rw [← cancel_mono ((L.idealTensor (I := I)).XIsoOfEq (show n + 1 + 1 = n + 2 by omega)).hom,
    Category.assoc, hc]
  simp only [Preadditive.add_comp, Category.assoc, HomologicalComplex.XIsoOfEq_hom_comp_d,
    HomologicalComplex.d_comp_XIsoOfEq_hom, HomologicalComplex.XIsoOfEq_hom_comp_XIsoOfEq_hom]
  have key := homotopy_hom_comp_XIsoOfEq (A := G₀) (Y := L.idealTensor (I := I))
    (fun i j => h.hom i j) (n + 1) n (n + 1 - 1) (n + 2)
    (by omega) rfl (by omega)
  beta_reduce at key
  rw [HomologicalComplex.XIsoOfEq_rfl, Iso.refl_hom, Category.comp_id] at key
  rw [← key]
  exact add_comm _ _

/-- The reduction sequence of a resolution `γ : E ⟶ H` of the corrected complex maps to
`0 ⟶ (F₀ ⊗ I)|_O ⟶ H ⟶ G₀|_O ⟶ 0` on the ideal parts by `(δ ≫ α) ⊗ I`, where `δ : E₀ ⟶ G₀` is the
transpose of `γ` followed by the projection. -/
theorem flatComplexEmb_comparison (hf : Sheaf.IsLocallySurjective f)
    {K₀ : CochainComplex (SheafMod O₀) ℤ} {L : FlatLift f K₀} (TL : IdealKernel S L)
    {G₀ : CochainComplex (SheafMod O₀) ℤ} (α : G₀ ⟶ L.baseChange.complex)
    (k : ∀ n : ℤ, G₀.X n ⟶ (L.idealTensor (I := I)).X (n + 1))
    (hk : ∀ n : ℤ, α.f n ≫ curvature TL n =
      k n ≫ (L.idealTensor (I := I)).d (n + 1) (n + 1 + 1) + G₀.d n (n + 1) ≫ k (n + 1))
    {E' : CochainComplex (SheafMod O) ℤ}
    (hflat : ∀ n, AlgebraicGeometry.SheafOfModules.IsFlat (O := O) (E'.X n))
    (hbdd : ∃ N : ℤ, ∀ n : ℤ, N ≤ n → IsZero (E'.X n)) (γ : E' ⟶ correctedComplex TL α k hk)
    (n : ℤ) :
    (restrict f).map (((Stacks.SheafOfModules.Tensor.sheafTensor O₀).flip.obj I).map
      ((flatComplexTranspose (γ ≫ correctedProj TL α k hk)).f n ≫ α.f n)) ≫
        (correctedIncl TL α k hk).f n = (flatComplexEmb S hf hflat hbdd).f n ≫ γ.f n := by
  have hg := flatComplexTranspose_spec hflat hbdd (γ ≫ correctedProj TL α k hk) n
  rw [HomologicalComplex.comp_f] at hg
  rw [flatComplexEmb_f]
  exact emb_comp_correctedIncl TL α k hk hf (flatComplexKernel S hf hflat hbdd) n (γ.f n)
    ((flatComplexTranspose (γ ≫ correctedProj TL α k hk)).f n) hg.symm

end Correction

section Criterion

variable [HasDerivedCategory.{d₀} (SheafMod O₀)]

omit [HasDerivedCategory (SheafMod O₀)] in
/-- The reduction of a flat lift is a bounded above complex of flat modules. -/
theorem FlatLift.reduction_boundedAbove {K₀ : CochainComplex (SheafMod O₀) ℤ} (L : FlatLift f K₀) :
    ∃ N : ℤ, ∀ n : ℤ, N ≤ n → IsZero (L.baseChange.complex.X n) := by
  obtain ⟨N, hN⟩ := L.boundedAbove
  exact ⟨N, fun n hn => L.isZero_reduction (hN n hn)⟩

/-- **If `ω(K₀)` is zero, the curvature class of any flat lift of `K₀` is zero in `D(O₀)`**: the
two differ by isomorphisms of the derived category, the comparison of the derived tensor product
with the ordinary one being invertible on the reduction, a bounded above complex of flat
modules. -/
theorem Q_map_curvatureMap_eq_zero (D : DerivedIdealTensor I) {K₀ : CochainComplex (SheafMod O₀) ℤ}
    {L : FlatLift f K₀} (T : IdealKernel S L) (h : obstructionMap D T = 0) :
    (DerivedCategory.Q (C := SheafMod O₀)).map (curvatureMap T) = 0 := by
  have := D.isIso_comparison L.baseChange.complex L.isFlat_reduction L.reduction_boundedAbove
  have h' : derivedCurvature D T = 0 := by
    simp only [obstructionMap] at h
    rw [← cancel_epi (inv (DerivedCategory.Q.map L.baseChange.map)),
      ← cancel_mono ((CategoryTheory.shiftFunctor (DerivedCategory (SheafMod O₀)) (2 : ℤ)).map
        (D.functor.map (DerivedCategory.Q.map L.baseChange.map)))]
    simpa using h
  simp only [derivedCurvature] at h'
  exact (Preadditive.IsIso.comp_right_eq_zero _ _).1 h'

/-- **The data of the source from a vanishing obstruction**: a bounded above flat lift `F` of
`K₀`, a quasi-isomorphism `α : G₀ ⟶ F₀` from a bounded above complex, and maps
`h^n : G₀^n ⟶ F₀^{n + 1} ⊗ I` with `α ∘ c = d ∘ h + h ∘ d`, `c` the curvature of `F`. -/
theorem exists_correction_of_omega_eq_zero (hf : Sheaf.IsLocallySurjective f)
    (S : SquareZeroIdeal f I) (D : DerivedIdealTensor I) (K₀ : CochainComplex (SheafMod O₀) ℤ)
    (hK : ∃ N : ℤ, ∀ n : ℤ, N ≤ n → IsZero (K₀.homology n))
    (h0 : omega hf S D K₀ hK = 0) :
    ∃ (L : FlatLift f K₀) (N : ℤ) (_ : ∀ n, N < n → IsZero (L.F.X n))
      (G₀ : CochainComplex (SheafMod O₀) ℤ) (_ : G₀.IsStrictlyLE N)
      (α : G₀ ⟶ L.baseChange.complex) (_ : QuasiIso α)
      (k : ∀ n : ℤ, G₀.X n ⟶ (L.idealTensor (I := I)).X (n + 1)),
      ∀ n : ℤ, α.f n ≫ curvature (idealKernel hf S L) n =
        k n ≫ (L.idealTensor (I := I)).d (n + 1) (n + 1 + 1) + G₀.d n (n + 1) ≫ k (n + 1) := by
  obtain ⟨L⟩ := exists_flatLift hf K₀ hK
  have hQ := Q_map_curvatureMap_eq_zero D (idealKernel hf S L)
    ((omega_eq hf S D hK (idealKernel hf S L)).symm.trans h0)
  obtain ⟨N, hN⟩ := L.boundedAbove
  have hFz : ∀ n, N < n → IsZero (L.F.X n) := fun n hn => hN n hn.le
  have : L.baseChange.complex.IsStrictlyLE N := by
    rw [CochainComplex.isStrictlyLE_iff]
    exact fun n hn => L.isZero_reduction (hFz n hn)
  obtain ⟨G₀, hG, α, hα, ⟨h⟩⟩ :=
    exists_bounded_quasiIso_homotopy_of_Q_map_eq_zero N (curvatureMap (idealKernel hf S L)) hQ
  obtain ⟨k, hk⟩ := exists_correction_of_homotopy (idealKernel hf S L) α h
  exact ⟨L, N, hFz, G₀, hG, α, hα, k, hk⟩

/-- **The reduction of a resolution of the corrected complex is a quasi-isomorphism onto `G₀`.**
For a bounded above flat resolution `γ : E ⟶ H` of the corrected complex, the transpose
`δ : E₀ ⟶ G₀` of `γ` followed by the projection is a quasi-isomorphism: this is the descending
induction of the source, applied to the reduction sequence of `E` and the sequence
`0 ⟶ (F₀ ⊗ I)|_O ⟶ H ⟶ G₀|_O ⟶ 0`. -/
theorem quasiIso_correctedTranspose (hf : Sheaf.IsLocallySurjective f)
    {K₀ : CochainComplex (SheafMod O₀) ℤ} {L : FlatLift f K₀} (TL : IdealKernel S L)
    {G₀ : CochainComplex (SheafMod O₀) ℤ} (α : G₀ ⟶ L.baseChange.complex) [QuasiIso α]
    (k : ∀ n : ℤ, G₀.X n ⟶ (L.idealTensor (I := I)).X (n + 1))
    (hk : ∀ n : ℤ, α.f n ≫ curvature TL n =
      k n ≫ (L.idealTensor (I := I)).d (n + 1) (n + 1 + 1) + G₀.d n (n + 1) ≫ k (n + 1))
    (N : ℤ) [L.baseChange.complex.IsStrictlyLE N] {E' : CochainComplex (SheafMod O) ℤ}
    (γ : E' ⟶ correctedComplex TL α k hk) [QuasiIso γ]
    (hflat : ∀ n, AlgebraicGeometry.SheafOfModules.IsFlat (O := O) (E'.X n))
    (hE' : E'.IsStrictlyLE N) :
    QuasiIso (flatComplexTranspose (γ ≫ correctedProj TL α k hk)) := by
  have hbdd : ∃ M : ℤ, ∀ n : ℤ, M ≤ n → IsZero (E'.X n) :=
    ⟨N + 1, fun n hn => E'.isZero_of_isStrictlyLE N n (by omega)⟩
  have : CochainComplex.IsStrictlyLE ((extensionOfScalarsCochainComplex J f).obj E') N :=
    isStrictlyLE_map_extensionOfScalars f N E' hE'
  exact quasiIso_of_shortExact_comparison (flatComplexEmb S hf hflat hbdd)
    (flatComplexUnitMap E') (flatComplexSequence S hf hflat hbdd).zero
    (shortExact_flatComplexSequence S hf hflat hbdd)
    (correctedIncl TL α k hk) (correctedProj TL α k hk) (correctedSequence TL α k hk).zero
    (shortExact_correctedSequence TL α k hk hf) γ
    (flatComplexTranspose (γ ≫ correctedProj TL α k hk)) α
    (flatComplexEmb_comparison hf TL α k hk hflat hbdd γ)
    (flatComplexUnitMap_comp_transpose _).symm N
    (fun i => flatObjects_extensionOfScalars f (hflat i)) L.isFlat_reduction

variable [HasDerivedCategory.{d} (SheafMod O)]

/-- **A bounded above complex of flat `O`-modules whose reduction represents `K₀` is a lift of
`K₀`**: its derived base change is computed by the degreewise reduction. -/
theorem nonempty_derivedLift_of_flatComplex (T : DerivedExtensionOfScalars f)
    (E : DerivedCategory.Minus (SheafMod O₀)) {E' : CochainComplex (SheafMod O) ℤ} (N : ℤ)
    (hflat : ∀ n, AlgebraicGeometry.SheafOfModules.IsFlat (O := O) (E'.X n))
    (hE' : E'.IsStrictlyLE N)
    (e : DerivedCategory.Q.obj ((extensionOfScalarsCochainComplex J f).obj E') ≅ E.obj) :
    Nonempty (DerivedLift T E) := by
  have hiso : IsIso ((derivedExtensionOfScalarsCounit.{d, d₀} f).app E') :=
    isIso_derivedExtensionOfScalarsCounit_app.{d, d₀} f E'
      (isFlatCellular_of_isStrictlyLE O E' N hflat)
  let L' : DerivedLift (derivedExtensionOfScalarsData.{d, d₀} f) E :=
    { K := ⟨DerivedCategory.Q.obj E', ⟨N, E', Iso.refl _, hE'⟩⟩
      identification := @asIso _ _ _ _ ((derivedExtensionOfScalarsCounit.{d, d₀} f).app E') hiso ≪≫
        e }
  exact ⟨L'.transport⟩

/-- **`(1) ⇒ (2)` of Stacks 0DIW, at a supplied derived ideal tensor datum.** Let `K₀ ∈ D⁻(O₀)`,
represented by a complex `K₀'` of
`O₀`-modules. If the canonical class `ω(K₀')` of Tag 0DIU vanishes, there is `K ∈ D⁻(O)` with
`K ⊗^L_O O₀ ≅ K₀` in `D(O₀)`, for any derived base change `T` along `f`.

The construction is the one of the source: the curvature of a bounded above flat lift `F` of
`K₀'` is null-homotopic after a quasi-isomorphism `α : G₀ ⟶ F₀`; the homotopy corrects the
differential of `F ×_{F₀} G₀`; and a bounded above flat resolution `E` of the corrected complex
has reduction quasi-isomorphic to `G₀`, by the descending induction using Tag 0DIV.

The class is stated against `D : DerivedIdealTensor I`, which exists only when `I` is flat over
`O₀`; the implication for every square-zero `I` is
`Deformation.ComplexLift.nonempty_derivedLift_of_tensorOmegaMinus_eq_zero`. -/
theorem nonempty_derivedLift_of_omega_eq_zero (hf : Sheaf.IsLocallySurjective f)
    (S : SquareZeroIdeal f I) (D : DerivedIdealTensor I) (T : DerivedExtensionOfScalars f)
    (E : DerivedCategory.Minus (SheafMod O₀)) (K₀ : CochainComplex (SheafMod O₀) ℤ)
    (e : DerivedCategory.Q.obj K₀ ≅ E.obj)
    (hK : ∃ N : ℤ, ∀ n : ℤ, N ≤ n → IsZero (K₀.homology n))
    (h0 : omega hf S D K₀ hK = 0) : Nonempty (DerivedLift T E) := by
  obtain ⟨L, N, hFz, G₀, hG, α, hα, k, hk⟩ :=
    exists_correction_of_omega_eq_zero hf S D K₀ hK h0
  have : L.baseChange.complex.IsStrictlyLE N := by
    rw [CochainComplex.isStrictlyLE_iff]
    exact fun n hn => L.isZero_reduction (hFz n hn)
  have := isStrictlyLE_correctedComplex (idealKernel hf S L) α k hk N hFz
  obtain ⟨E', γ, -, hγ, hflat, hE'⟩ :=
    exists_isFlat_quasiIso_isStrictlyLE O N (correctedComplex (idealKernel hf S L) α k hk)
  have hδ := quasiIso_correctedTranspose hf (idealKernel hf S L) α k hk N γ hflat hE'
  exact nonempty_derivedLift_of_flatComplex T E N hflat hE'
    (asIso (DerivedCategory.Q.map
        (flatComplexTranspose (γ ≫ correctedProj (idealKernel hf S L) α k hk))) ≪≫
      asIso (DerivedCategory.Q.map α) ≪≫ asIso (DerivedCategory.Q.map L.baseChange.map) ≪≫ e)

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat)] in
/-- A complex representing an object of `D⁻(O₀)` has cohomology vanishing in high degrees. -/
theorem homology_boundedAbove_of_iso (E : DerivedCategory.Minus (SheafMod O₀))
    {K₀ : CochainComplex (SheafMod O₀) ℤ} (e : DerivedCategory.Q.obj K₀ ≅ E.obj) :
    ∃ N : ℤ, ∀ n : ℤ, N ≤ n → IsZero (K₀.homology n) := by
  obtain ⟨b, hb⟩ := E.property
  have hE : E.obj.IsLE b := hb
  have h1 : (DerivedCategory.Q.obj K₀).IsLE b := by
    rw [DerivedCategory.isLE_iff] at hE ⊢
    exact fun i hi => (hE i hi).of_iso ((DerivedCategory.homologyFunctor _ i).mapIso e)
  have h2 : K₀.IsLE b := (DerivedCategory.isLE_Q_obj_iff K₀ b).1 h1
  exact ⟨b + 1, fun n hn => (K₀.exactAt_of_isLE b n (by omega)).isZero_homology⟩

/-- **Stacks 0DIW for a flat ideal, at a supplied derived ideal tensor datum.** Let `C` be a site
and `f : O ⟶ O₀` a surjection of sheaves of commutative rings whose kernel is an ideal sheaf `I`
of square zero. For every object `K₀` of `D⁻(O₀)`, represented by a complex `K₀'` of `O₀`-modules,
the following are equivalent:

1. the canonical class `ω(K₀) : K₀ ⟶ (K₀ ⊗^L_{O₀} I)[2]` of Tag 0DIU, computed on `K₀'`, is
   zero;
2. there exists `K ∈ D⁻(O)` with `K ⊗^L_O O₀ ≅ K₀` in `D(O₀)`.

Here `T` is any derived base change `- ⊗^L_O O₀` (all are canonically isomorphic) and `D` the
derived tensor product with `I` against which the base states `ω`. The bound on the cohomology
of `K₀'` that `ω` is stated with is the one `K₀ ∈ D⁻(O₀)` provides,
`Deformation.ComplexLift.homology_boundedAbove_of_iso`.

A datum `D : DerivedIdealTensor I` exists only when `I` is flat over `O₀`: its comparison
`K ⊗_{O₀} I ⟶ K ⊗^L_{O₀} I` is natural on all complexes, which forces `Tor₁(-, I) = 0`. So this
is Tag 0DIW for flat `I` only. The lemma for every square-zero ideal `I`, with `ω` the class
`Deformation.ComplexLift.tensorOmegaMinus` with values in the derived tensor product, is
`Deformation.ComplexLift.tensorOmegaMinus_eq_zero_iff_nonempty_derivedLift`. -/
theorem omega_eq_zero_iff_nonempty_derivedLift (hf : Sheaf.IsLocallySurjective f)
    (S : SquareZeroIdeal f I) (D : DerivedIdealTensor I) (T : DerivedExtensionOfScalars f)
    (E : DerivedCategory.Minus (SheafMod O₀)) (K₀ : CochainComplex (SheafMod O₀) ℤ)
    (e : DerivedCategory.Q.obj K₀ ≅ E.obj) :
    omega hf S D K₀ (homology_boundedAbove_of_iso E e) = 0 ↔ Nonempty (DerivedLift T E) :=
  ⟨nonempty_derivedLift_of_omega_eq_zero hf S D T E K₀ e _,
    omega_eq_zero_of_nonempty_derivedLift hf S D T E K₀ e _⟩

end Criterion

end Deformation.ComplexLift

end
