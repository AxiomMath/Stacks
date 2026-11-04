module

public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Products
public import StacksFrontier.Homology.DerivedComplete.AdicKoszulCompletion

/-!
# Derived completeness via Koszul complexes

An object of the derived category is derived complete for a finitely generated ideal exactly
when its canonical map to the derived limit of its tensor--Koszul tower is an isomorphism.

## Main definitions

* `AdicKoszul.coefficientKoszulGradedDerivedMilnorIso` identifies the localized Milnor fiber of
  a graded tower of the Koszul filtration with the finite product of its scalar factors.

## Main results

* `AdicKoszul.isDerivedComplete_iff_isIso_to_rlim_derivedTensor_koszulPowers` characterizes
  derived completeness by the canonical map to the derived limit of the tensor--Koszul tower.
* `AdicKoszul.coefficientKoszulFiltrationMilnor_shortExact`: two adjacent steps of the Koszul
  filtration and their graded quotient give a short exact sequence of Milnor fibers.
* `AdicKoszul.coefficientKoszulFiltrationStep_milnor_quasiIso`: for derived-complete
  coefficients, the negative filtration inclusions induce quasi-isomorphisms of Milnor fibers.
* `canonicalCompletion_criterion`: an object is derived complete if and only if the completion
  unit at it is an isomorphism.

## References

* [Stacks Project, Tag 091Z](https://stacks.math.columbia.edu/tag/091Z)
* [Bhatt--Scholze, *Projectivity of the Witt vector affine Grassmannian*][BS]
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe u v

namespace AdicKoszul

variable {A : Type u} [CommRing A]

attribute [local instance] HasDerivedCategory.standard derivedCountableProducts

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CountableMilnorTower KoszulCoefficientTower

private abbrev scalarDifference (K : DerivedCategory (ModuleCat.{v} A)) (a : A) :
    (∏ᶜ fun _ : ℕ ↦ K) ⟶ ∏ᶜ fun _ : ℕ ↦ K :=
  Pi.lift fun n : ℕ ↦ Pi.π (fun _ : ℕ ↦ K) n -
    Pi.π (fun _ : ℕ ↦ K) (n + 1) ≫ (a • 𝟙 K)
private theorem scalarDifference_isIso (K : DerivedCategory (ModuleCat.{v} A)) (a : A)
    (h : ∃ L, IsDerivedLimit (Functor.ofOpSequence (X := fun _ : ℕ ↦ K)
      (fun _ ↦ a • 𝟙 K)) L ∧ IsZero L) : IsIso (scalarDifference K a) := by
  obtain ⟨L, ⟨p, δ, hT⟩, hL⟩ := h
  simpa only [scalarDifference, Triangle.mk_mor₂, Functor.ofOpSequence_obj,
    Functor.ofOpSequence_map_homOfLE_succ] using! (Triangle.isZero₁_iff_isIso₂ _ hT).mp hL
/-- An endomorphism intertwined with an isomorphism-conjugate of an invertible one is invertible. -/
private theorem isIso_of_comp_hom_eq_hom_comp {C : Type*} [Category C] {X Y : C} (e : X ≅ Y)
    {g : X ⟶ X} {g' : Y ⟶ Y} [IsIso g] (h : g ≫ e.hom = e.hom ≫ g') : IsIso g' := by
  rw [show g' = e.inv ≫ g ≫ e.hom by rw [h, e.inv_hom_id_assoc]]
  infer_instance
private theorem scalarDifference_iso {K L : DerivedCategory (ModuleCat.{v} A)}
    (e : K ≅ L) (a : A) [IsIso (scalarDifference K a)] : IsIso (scalarDifference L a) := by
  let E := Pi.mapIso (fun _ : ℕ ↦ e)
  refine isIso_of_comp_hom_eq_hom_comp E (g := scalarDifference K a) ?_
  apply Pi.hom_ext
  intro n
  simp [scalarDifference, E, Preadditive.comp_sub, Preadditive.sub_comp,
    Category.assoc]
private theorem scalarDifference_shift (K : DerivedCategory (ModuleCat.{v} A))
    (a : A) (d : ℤ) [IsIso (scalarDifference K a)] :
    IsIso (scalarDifference (K⟦d⟧) a) := by
  let F := shiftFunctor (DerivedCategory (ModuleCat.{v} A)) d
  let e := PreservesProduct.iso F (fun _ : ℕ ↦ K)
  refine isIso_of_comp_hom_eq_hom_comp e (g := F.map (scalarDifference K a)) ?_
  apply Pi.hom_ext
  intro n
  dsimp only [e, scalarDifference]
  rw [Category.assoc, PreservesProduct.iso_hom, piComparison_comp_π,
    ← F.map_comp, Pi.lift_π, F.map_sub, F.map_comp,
    Category.assoc, Pi.lift_π, Preadditive.comp_sub, piComparison_comp_π,
    ← Category.assoc, piComparison_comp_π]
  simp [F]
/-- A scalar Milnor fiber vanishes on every shift of a derived-complete coefficient complex. -/
public theorem scalarMilnor_shift_isZero (K : CochainComplex (ModuleCat.{v} A) ℤ)
    (a : A) (d : ℤ)
    (ha : ∃ L, IsDerivedLimit (Functor.ofOpSequence
      (X := fun _ : ℕ ↦ DerivedCategory.Q.obj K) (fun _ ↦ a • 𝟙 _)) L ∧ IsZero L) :
    IsZero (DerivedCategory.Q.obj (countableMilnorFunctor.obj
      (Functor.ofOpSequence (X := fun _ : ℕ ↦ K⟦d⟧)
        (fun _ ↦ (shiftFunctor _ d).map (a • 𝟙 K))))) := by
  have h0 := scalarDifference_isIso (DerivedCategory.Q.obj K) a ha
  have hs := scalarDifference_shift (DerivedCategory.Q.obj K) a d
  let e : DerivedCategory.Q.obj (K⟦d⟧) ≅ (DerivedCategory.Q.obj K)⟦d⟧ :=
    (DerivedCategory.Q.commShiftIso d).app K
  have ht := scalarDifference_iso e.symm a
  obtain ⟨δ, hδ⟩ := map_quasiIso_and_milnor_triangle.2
    (Functor.ofOpSequence (X := fun _ : ℕ ↦ K⟦d⟧)
      (fun _ ↦ (shiftFunctor _ d).map (a • 𝟙 K)))
  apply (Triangle.isZero₁_iff_isIso₂ _ hδ).mpr
  simpa [Functor.map_smul, Functor.map_id, scalarDifference] using
    (inferInstance : IsIso (scalarDifference (DerivedCategory.Q.obj (K⟦d⟧)) a))

/-- The tower of graded pieces of the Koszul filtration in degree `p`, with the diagonal scalar
transition maps. -/
public def coefficientKoszulGradedTower {r : ℕ} (f : Fin r → A) (p : ℤ)
    (K : CochainComplex (ModuleCat.{v} A) ℤ) : Tower.{u, v} (A := A) :=
  Functor.ofOpSequence (X := fun _ : ℕ ↦ (coefficientKoszulGradedPiece (A := A) r p).obj K)
    (fun _ ↦ coefficientKoszulGradedTransition f p K)
/-- The scalar tower corresponding to one exterior basis component, including its shift. -/
public def coefficientKoszulScalarTower {r : ℕ} (f : Fin r → A) (p : ℤ)
    (K : CochainComplex (ModuleCat.{v} A) ℤ) (S : KoszulBasis r p.natAbs) : Tower.{u, v} (A := A) :=
  Functor.ofOpSequence (X := fun _ : ℕ ↦ K⟦-p⟧) (fun _ ↦
    (shiftFunctor _ (-p)).map ((∏ i ∈ S.1, f i) • 𝟙 K))
/-- The canonical projection from the graded tower to a scalar factor. -/
public def coefficientKoszulGradedTowerπ {r : ℕ} (f : Fin r → A) (p : ℤ)
    (K : CochainComplex (ModuleCat.{v} A) ℤ) (S : KoszulBasis r p.natAbs) :
    coefficientKoszulGradedTower f p K ⟶ coefficientKoszulScalarTower f p K S :=
  NatTrans.ofOpSequence
    (fun _ ↦ Pi.π (fun _ : KoszulBasis r p.natAbs ↦ K⟦-p⟧) S)
    (fun n ↦ by
      simp [coefficientKoszulGradedTower, coefficientKoszulScalarTower,
        coefficientKoszulGradedTransition])
/-- A coefficient chain map acts naturally on each scalar tower. -/
public def coefficientKoszulScalarTowerMap {r : ℕ} (f : Fin r → A) (p : ℤ)
    {K L : CochainComplex (ModuleCat.{v} A) ℤ} (g : K ⟶ L) (S : KoszulBasis r p.natAbs) :
    coefficientKoszulScalarTower f p K S ⟶ coefficientKoszulScalarTower f p L S :=
  NatTrans.ofOpSequence (fun _ ↦ g⟦-p⟧') (fun n ↦ by
    simp only [coefficientKoszulScalarTower, Functor.ofOpSequence_map_homOfLE_succ,
      ← Functor.map_comp]
    congr 1
    simp)
/-- A coefficient chain map acts on the diagonal graded tower. -/
public def coefficientKoszulGradedTowerMap {r : ℕ} (f : Fin r → A) (p : ℤ)
    {K L : CochainComplex (ModuleCat.{v} A) ℤ} (g : K ⟶ L) :
    coefficientKoszulGradedTower f p K ⟶ coefficientKoszulGradedTower f p L :=
  NatTrans.ofOpSequence (fun _ ↦ (coefficientKoszulGradedPiece (A := A) r p).map g)
    (fun n ↦ by
      simp only [coefficientKoszulGradedTower, Functor.ofOpSequence_map_homOfLE_succ]
      apply Pi.hom_ext
      intro S
      change coefficientKoszulGradedTransition f p K ≫
          Limits.Pi.map (fun _ : KoszulBasis r p.natAbs ↦ g⟦-p⟧') ≫ _ = _
      simp only [coefficientKoszulGradedTransition, Category.assoc, Pi.map_π,
        Pi.map_π_assoc]
      change _ = Limits.Pi.map (fun _ : KoszulBasis r p.natAbs ↦ g⟦-p⟧') ≫ _
      simp only [Pi.map_π_assoc, ← Functor.map_comp]
      simp)
/-- The scalar projections commute with coefficient maps. -/
@[reassoc] public theorem coefficientKoszulGradedTowerπ_naturality {r : ℕ}
    (f : Fin r → A) (p : ℤ) {K L : CochainComplex (ModuleCat.{v} A) ℤ}
    (g : K ⟶ L) (S : KoszulBasis r p.natAbs) :
    coefficientKoszulGradedTowerMap f p g ≫ coefficientKoszulGradedTowerπ f p L S =
      coefficientKoszulGradedTowerπ f p K S ≫ coefficientKoszulScalarTowerMap f p g S := by
  apply NatTrans.ext
  funext n
  show Limits.Pi.map (fun _ : KoszulBasis r p.natAbs ↦ g⟦-p⟧') ≫ _ = _
  exact Pi.map_π _ _

/-- The projection of the Koszul filtration step in degree `p` onto its graded tower. -/
public def coefficientKoszulGradedProjection {r : ℕ} (f : Fin r → A)
    (p : ℤ) (hp : p ≤ 0) (K : CochainComplex (ModuleCat.{v} A) ℤ) :
    (coefficientKoszulFiltration f p).obj K ⟶ coefficientKoszulGradedTower f p K :=
  NatTrans.ofOpSequence (fun n ↦ (canonicalFormulaLaws f).1.gradedProjection p hp n K)
    (fun n ↦ by
      simpa only [coefficientKoszulGradedTower, Functor.ofOpSequence_map_homOfLE_succ,
        coefficientKoszulFiltration, FormulaLaws.tower] using!
        ((canonicalFormulaLaws f).2 (canonicalFormulaLaws f).1).graded_transition p hp n K)
/-- Naturality of the quotient projection in the coefficient complex. -/
@[reassoc] public theorem coefficientKoszulGradedProjection_naturality {r : ℕ}
    (f : Fin r → A) (p : ℤ) (hp : p ≤ 0)
    {K L : CochainComplex (ModuleCat.{v} A) ℤ} (g : K ⟶ L) :
    (coefficientKoszulFiltration f p).map g ≫ coefficientKoszulGradedProjection f p hp L =
      coefficientKoszulGradedProjection f p hp K ≫ coefficientKoszulGradedTowerMap f p g := by
  apply NatTrans.ext
  funext n
  exact ((canonicalFormulaLaws f).2 (canonicalFormulaLaws f).1).graded_naturality p hp n.unop g

/-- The short complex of towers for two adjacent filtration steps. -/
public def coefficientKoszulFiltrationSequence {r : ℕ} (f : Fin r → A)
    (p : ℤ) (hp : p ≤ 0) (K : CochainComplex (ModuleCat.{v} A) ℤ) :
    ShortComplex (Tower.{u, v} (A := A)) :=
  ShortComplex.mk ((coefficientKoszulFiltrationStep f p).app K)
    (coefficientKoszulGradedProjection f p hp K) (by
      apply NatTrans.ext
      funext n
      apply Pi.hom_ext
      intro S
      change _ ≫ (canonicalFormulaLaws f).1.gradedProjection p hp n.unop K ≫ _ = _
      rw [FormulaLaws.gradedProjection, Pi.lift_π]
      simp only [NatTrans.app_zero, zero_comp]
      apply HomologicalComplex.hom_ext
      intro t
      exact (canonicalFormulaLaws f).1.graded_vanish p hp K S t)
/-- The filtration is short exact as a sequence of strict towers. -/
public theorem coefficientKoszulFiltrationSequence_shortExact {r : ℕ} (f : Fin r → A)
    (p : ℤ) (hp : p ≤ 0) (K : CochainComplex (ModuleCat.{v} A) ℤ) :
    (coefficientKoszulFiltrationSequence f p hp K).ShortExact := by
  let S := coefficientKoszulFiltrationSequence f p hp K
  have hn (n : ℕᵒᵖ) : (S.map ((evaluation _ _).obj n)).ShortExact := by
    let j := ((coefficientKoszulFiltrationStep f p).app K).app n
    have : Mono j := coefficientKoszulFiltrationStep_mono f p n.unop K
    have hj : (ShortComplex.cokernelSequence j).ShortExact :=
      { exact := ShortComplex.cokernelSequence_exact j
        mono_f := by change Mono j; infer_instance }
    let e : ShortComplex.cokernelSequence j ≅ S.map ((evaluation _ _).obj n) :=
      ShortComplex.isoMk (Iso.refl _) (Iso.refl _)
        (coefficientKoszulGradedPieceIso f p hp n.unop K)
        (by simp [S, coefficientKoszulFiltrationSequence, j]) (by
          dsimp [S, coefficientKoszulFiltrationSequence, coefficientKoszulGradedProjection,
            coefficientKoszulGradedPieceIso, FormulaLaws.gradedMap, j]
          show _ = cokernel.π j ≫ cokernel.desc j _ _
          rw [cokernel.π_desc]
          exact Category.id_comp _)
    exact ShortComplex.shortExact_of_iso e hj
  have hmono : ∀ n, Mono (S.f.app n) := fun n ↦ (hn n).mono_f
  have hepi : ∀ n, Epi (S.g.app n) := fun n ↦ (hn n).epi_g
  have : Mono S.f := NatTrans.mono_of_mono_app S.f
  have : Epi S.g := NatTrans.epi_of_epi_app S.g
  refine { exact := ?_ }
  rw [ShortComplex.exact_iff_isZero_homology, IsZero.iff_id_eq_zero]
  apply NatTrans.ext
  funext n
  exact (IsZero.of_iso ((ShortComplex.exact_iff_isZero_homology _).mp (hn n).exact)
    (S.mapHomologyIso ((evaluation _ _).obj n)).symm).eq_of_src _ _
/-- The short complex of two adjacent filtration steps stays short exact after taking Milnor
fibers. -/
public theorem coefficientKoszulFiltrationMilnor_shortExact {r : ℕ} (f : Fin r → A)
    (p : ℤ) (hp : p ≤ 0) (K : CochainComplex (ModuleCat.{v} A) ℤ) :
    ((coefficientKoszulFiltrationSequence f p hp K).map countableMilnorFunctor).ShortExact :=
  countableMilnorFunctor_map_shortExact _
    (coefficientKoszulFiltrationSequence_shortExact f p hp K)

/-- The graded tower is the product of its scalar towers, with the canonical projections. -/
public def coefficientKoszulGradedTowerIso {r : ℕ} (f : Fin r → A) (p : ℤ)
    (K : CochainComplex (ModuleCat.{v} A) ℤ) :
    coefficientKoszulGradedTower f p K ≅ ∏ᶜ coefficientKoszulScalarTower f p K := by
  let a : coefficientKoszulGradedTower f p K ⟶ ∏ᶜ coefficientKoszulScalarTower f p K :=
    Pi.lift (coefficientKoszulGradedTowerπ f p K)
  have (n : ℕᵒᵖ) : IsIso (a.app n) := by
    let e : (∏ᶜ coefficientKoszulScalarTower f p K).obj n ≅
        (coefficientKoszulGradedTower f p K).obj n :=
      PreservesProduct.iso ((evaluation ℕᵒᵖ (CochainComplex (ModuleCat.{v} A) ℤ)).obj n)
        (coefficientKoszulScalarTower f p K)
    have h : a.app n ≫ e.hom = 𝟙 _ := by
      apply Pi.hom_ext
      intro S
      rw [Category.assoc, Category.id_comp]
      change a.app n ≫ piComparison
        ((evaluation ℕᵒᵖ (CochainComplex (ModuleCat.{v} A) ℤ)).obj n)
        (coefficientKoszulScalarTower f p K) ≫ _ = _
      erw [piComparison_comp_π]
      change (a ≫ Pi.π (coefficientKoszulScalarTower f p K) S).app n = _
      dsimp only [a]
      rw [Pi.lift_π]
      rfl
    have h' : a.app n = e.inv := by
      rw [← Category.comp_id (a.app n), ← e.hom_inv_id, ← Category.assoc, h,
        Category.id_comp]
    rw [h']
    infer_instance
  have : IsIso a := NatIso.isIso_of_isIso_app a
  exact asIso a
/-- The Milnor fiber of the graded tower is the finite product of the scalar Milnor fibers. -/
public def coefficientKoszulGradedMilnorIso {r : ℕ} (f : Fin r → A) (p : ℤ)
    (K : CochainComplex (ModuleCat.{v} A) ℤ) :
    countableMilnorFunctor.obj (coefficientKoszulGradedTower f p K) ≅
      ∏ᶜ fun S : KoszulBasis r p.natAbs ↦
        countableMilnorFunctor.obj (coefficientKoszulScalarTower f p K S) :=
  countableMilnorFunctor.mapIso (coefficientKoszulGradedTowerIso f p K) ≪≫
    PreservesProduct.iso countableMilnorFunctor (coefficientKoszulScalarTower f p K)
/-- `coefficientKoszulGradedTowerIso` is compatible with the projections to the scalar
towers. -/
@[reassoc] public theorem coefficientKoszulGradedTowerIso_hom_π {r : ℕ} (f : Fin r → A) (p : ℤ)
    (K : CochainComplex (ModuleCat.{v} A) ℤ) (S : KoszulBasis r p.natAbs) :
    (coefficientKoszulGradedTowerIso f p K).hom ≫
      Pi.π (coefficientKoszulScalarTower f p K) S = coefficientKoszulGradedTowerπ f p K S := by
  show Pi.lift _ ≫ _ = _
  exact Pi.lift_π _ _
/-- `coefficientKoszulGradedMilnorIso` is compatible with the projections to the scalar
factors. -/
@[reassoc] public theorem coefficientKoszulGradedMilnorIso_hom_π {r : ℕ} (f : Fin r → A) (p : ℤ)
    (K : CochainComplex (ModuleCat.{v} A) ℤ) (S : KoszulBasis r p.natAbs) :
    (coefficientKoszulGradedMilnorIso f p K).hom ≫
      Pi.π (fun S ↦ countableMilnorFunctor.obj (coefficientKoszulScalarTower f p K S)) S =
        countableMilnorFunctor.map (coefficientKoszulGradedTowerπ f p K S) := by
  dsimp only [coefficientKoszulGradedMilnorIso, Iso.trans_hom, Functor.mapIso_hom]
  rw [Category.assoc, PreservesProduct.iso_hom, piComparison_comp_π,
    ← Functor.map_comp, coefficientKoszulGradedTowerIso_hom_π]

/-- `coefficientKoszulGradedMilnorIso` is natural in the coefficient chain map. -/
@[reassoc] public theorem coefficientKoszulGradedMilnorIso_naturality {r : ℕ}
    (f : Fin r → A) (p : ℤ) {K L : CochainComplex (ModuleCat.{v} A) ℤ} (g : K ⟶ L) :
    countableMilnorFunctor.map (coefficientKoszulGradedTowerMap f p g) ≫
        (coefficientKoszulGradedMilnorIso f p L).hom =
      (coefficientKoszulGradedMilnorIso f p K).hom ≫
        Limits.Pi.map (fun S ↦
          countableMilnorFunctor.map (coefficientKoszulScalarTowerMap f p g S)) := by
  apply Pi.hom_ext
  intro S
  simp only [Category.assoc, Pi.map_π, coefficientKoszulGradedMilnorIso_hom_π,
    coefficientKoszulGradedMilnorIso_hom_π_assoc, ← Functor.map_comp,
    coefficientKoszulGradedTowerπ_naturality]

/-- The localized Milnor fiber of the graded tower is the finite product of the localized
scalar Milnor fibers. -/
public def coefficientKoszulGradedDerivedMilnorIso {r : ℕ} (f : Fin r → A) (p : ℤ)
    (K : CochainComplex (ModuleCat.{v} A) ℤ) :
    DerivedCategory.Q.obj (countableMilnorFunctor.obj (coefficientKoszulGradedTower f p K)) ≅
      ∏ᶜ fun S : KoszulBasis r p.natAbs ↦ DerivedCategory.Q.obj
        (countableMilnorFunctor.obj (coefficientKoszulScalarTower f p K S)) :=
  DerivedCategory.Q.mapIso (coefficientKoszulGradedMilnorIso f p K) ≪≫
    PreservesProduct.iso DerivedCategory.Q _
/-- The localized Milnor fiber of a scalar tower is a derived limit of that tower. -/
public theorem coefficientKoszulScalarMilnor_isDerivedLimit {r : ℕ} (f : Fin r → A) (p : ℤ)
    (K : CochainComplex (ModuleCat.{v} A) ℤ) (S : KoszulBasis r p.natAbs) :
    IsDerivedLimit (coefficientKoszulScalarTower f p K S ⋙ DerivedCategory.Q)
      (DerivedCategory.Q.obj (countableMilnorFunctor.obj
        (coefficientKoszulScalarTower f p K S))) := by
  obtain ⟨δ, hδ⟩ := map_quasiIso_and_milnor_triangle.2 (coefficientKoszulScalarTower f p K S)
  exact ⟨_, δ, hδ⟩
/-- Each factor is a derived limit of repeated scalar multiplication on the shifted coefficient. -/
public theorem coefficientKoszulScalarMilnor_isScalarDerivedLimit {r : ℕ}
    (f : Fin r → A) (p : ℤ) (K : CochainComplex (ModuleCat.{v} A) ℤ)
    (S : KoszulBasis r p.natAbs) :
    IsDerivedLimit (Functor.ofOpSequence
      (X := fun _ : ℕ ↦ DerivedCategory.Q.obj (K⟦-p⟧))
      (fun _ ↦ (∏ i ∈ S.1, f i) • 𝟙 _))
      (DerivedCategory.Q.obj
        (countableMilnorFunctor.obj (coefficientKoszulScalarTower f p K S))) := by
  simpa [IsDerivedLimit, coefficientKoszulScalarTower, CoefficientComplex,
    Functor.map_smul, Functor.map_id] using!
      coefficientKoszulScalarMilnor_isDerivedLimit f p K S

/-- The negative graded Milnor fibers vanish for derived-complete coefficients. -/
public theorem coefficientKoszulGradedMilnor_isZero {r : ℕ} (f : Fin r → A)
    (p : ℤ) (hp : p < 0) (K : CochainComplex (ModuleCat.{v} A) ℤ)
    (hK : IsDerivedComplete (Ideal.span (Set.range f)) (DerivedCategory.Q.obj K)) :
    IsZero (DerivedCategory.Q.obj (countableMilnorFunctor.obj
      (coefficientKoszulGradedTower f p K))) := by
  have hS (S : KoszulBasis r p.natAbs) :
      IsZero (DerivedCategory.Q.obj (countableMilnorFunctor.obj
        (coefficientKoszulScalarTower f p K S))) := by
    apply scalarMilnor_shift_isZero
    rw [← isDerivedCompleteAt_iff_exists_isDerivedLimit_isZero]
    apply hK
    have hnonempty : S.1.Nonempty := Finset.card_pos.mp (by
      rw [S.2]; exact Int.natAbs_pos.mpr (ne_of_lt hp))
    obtain ⟨i, hi⟩ := hnonempty
    rw [← Finset.mul_prod_erase S.1 f hi]
    exact Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨i, rfl⟩)
  apply IsZero.of_iso _ (coefficientKoszulGradedDerivedMilnorIso f p K)
  rw [IsZero.iff_id_eq_zero]
  apply Pi.hom_ext
  intro S
  exact (hS S).eq_of_tgt _ _
/-- For derived-complete coefficients, the negative filtration inclusions induce
quasi-isomorphisms of Milnor fibers. -/
public theorem coefficientKoszulFiltrationStep_milnor_quasiIso {r : ℕ} (f : Fin r → A)
    (p : ℤ) (hp : p < 0) (K : CochainComplex (ModuleCat.{v} A) ℤ)
    (hK : IsDerivedComplete (Ideal.span (Set.range f)) (DerivedCategory.Q.obj K)) :
    QuasiIso (countableMilnorFunctor.map ((coefficientKoszulFiltrationStep f p).app K)) := by
  let h := coefficientKoszulFiltrationMilnor_shortExact f p hp.le K
  rw [← DerivedCategory.isIso_Q_map_iff_quasiIso]
  exact (Triangle.isZero₃_iff_isIso₁ _ (DerivedCategory.triangleOfSES_distinguished h)).mp
    (coefficientKoszulGradedMilnor_isZero f p hp K hK)

end AdicKoszul
end

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open CountableMilnorTower

attribute [local instance 2000] HasDerivedCategory.standard

universe ringLevel moduleLevel

variable {ring : Type ringLevel} [CommRing ring]

/-- The derived category of modules over a commutative ring has countable products. -/
public instance derivedCountableProducts (baseRing : Type*) [CommRing baseRing] :
    HasProductsOfShape ℕ (DerivedCategory (ModuleCat.{moduleLevel} baseRing)) :=
  Stacks.DerivedProducts.hasProductsOfShape_derivedCategory

/-- Let `inclusion : source ⟶ middle` and `difference : middle ⟶ target` compose to zero, and
let `retraction` and `sectionMap` satisfy `inclusion ≫ retraction = 𝟙`,
`sectionMap ≫ difference = 𝟙` and `retraction ≫ inclusion + difference ≫ sectionMap = 𝟙`. Then
the lift of `inclusion` to the mapping cocone of `difference` is a quasi-isomorphism. -/
public theorem mappingCoconeLift_quasiIso_of_split
    {source middle target : CochainComplex (ModuleCat.{moduleLevel} ring) ℤ}
    (inclusion : source ⟶ middle) (difference : middle ⟶ target)
    (retraction : middle ⟶ source) (sectionMap : target ⟶ middle)
    (zeroComposite : inclusion ≫ difference = 0)
    (retractIdentity : inclusion ≫ retraction = 𝟙 source)
    (sectionIdentity : sectionMap ≫ difference = 𝟙 target)
    (decomposition : retraction ≫ inclusion + difference ≫ sectionMap = 𝟙 middle) :
    QuasiIso (CochainComplex.mappingCocone.lift difference inclusion 0
      (by simp [zeroComposite])) := by
  let lift := CochainComplex.mappingCocone.lift difference inclusion 0 (by simp [zeroComposite])
  let projection := CochainComplex.mappingCocone.fst difference
  have liftProjection : lift ≫ projection = inclusion :=
    CochainComplex.mappingCocone.lift_fst difference inclusion 0 _
  have mappedSection :
      DerivedCategory.Q.map sectionMap ≫ DerivedCategory.Q.map difference = 𝟙 _ := by
    rw [← Functor.map_comp, sectionIdentity, CategoryTheory.Functor.map_id]
  have : IsSplitEpi (DerivedCategory.Q.map difference) := ⟨⟨_, mappedSection⟩⟩
  have epiDifference : Epi (DerivedCategory.Q.map difference) := inferInstance
  let triangle := DerivedCategory.Q.mapTriangle.obj (CochainComplex.mappingCocone.triangle
    difference)
  have distinguished := DerivedCategory.mappingCocone_triangle_distinguished difference
  have : Mono (DerivedCategory.Q.map projection) :=
    Triangle.mono₁ triangle distinguished
      (Triangle.mor₃_eq_zero_of_epi₂ triangle distinguished epiDifference)
  have projectionDifference :
      DerivedCategory.Q.map projection ≫ DerivedCategory.Q.map difference = 0 :=
    comp_distTriang_mor_zero₁₂ triangle distinguished
  have decomposed : retraction ≫ inclusion = 𝟙 middle - difference ≫ sectionMap :=
    eq_sub_iff_add_eq.mpr decomposition
  rw [← DerivedCategory.isIso_Q_map_iff_quasiIso]
  show IsIso (DerivedCategory.Q.map lift)
  refine ⟨⟨DerivedCategory.Q.map (projection ≫ retraction), ?_, ?_⟩⟩
  · rw [← Functor.map_comp, ← Category.assoc, liftProjection, retractIdentity,
      CategoryTheory.Functor.map_id]
  · apply (cancel_mono (DerivedCategory.Q.map projection)).mp
    simp only [Category.assoc, ← Functor.map_comp]
    simp only [liftProjection]
    rw [decomposed]
    simp only [Preadditive.comp_sub, Category.comp_id, Functor.map_sub, Functor.map_comp,
      ← Category.assoc, projectionDifference, zero_comp, sub_zero, Category.id_comp]

/-- The augmentation of the constant tower on a complex by that complex, with identity
components. -/
public def constantTowerAugmentation
    (complex : CochainComplex (ModuleCat.{moduleLevel} ring) ℤ) :
    TowerAugmentation ((Functor.const ℕᵒᵖ).obj complex) where
  source := complex
  app _ := 𝟙 complex
  naturality _ := by simp

/-- The augmentation map of the constant tower on a complex is a quasi-isomorphism. -/
public theorem constantTower_augmentation_quasiIso
    (complex : CochainComplex (ModuleCat.{moduleLevel} ring) ℤ) :
    QuasiIso (constantTowerAugmentation complex).augmentationMap := by
  let tower := (Functor.const ℕᵒᵖ).obj complex
  let inclusion := (constantTowerAugmentation complex).productLift
  let retraction : towerProductObj tower ⟶ complex := Pi.π (fun _ : ℕ => complex) 0
  let sectionMap : towerProductObj tower ⟶ towerProductObj tower :=
    Pi.lift fun stage : ℕ => - ∑ index ∈ Finset.range stage, Pi.π (fun _ : ℕ => complex) index
  have retractIdentity : inclusion ≫ retraction = 𝟙 complex := by
    simp [inclusion, retraction, TowerAugmentation.productLift, constantTowerAugmentation]
  have sectionIdentity : sectionMap ≫ oneMinusShift tower = 𝟙 _ := by
    apply Pi.hom_ext
    intro stage
    simp [sectionMap, oneMinusShift, tower, Preadditive.comp_sub,
      Finset.sum_range_succ, Category.assoc]
  have telescoping (stage : ℕ) :
      ∑ index ∈ Finset.range stage,
        (Pi.π (fun _ : ℕ => complex) index - Pi.π (fun _ : ℕ => complex) (index + 1)) =
      Pi.π (fun _ : ℕ => complex) 0 - Pi.π (fun _ : ℕ => complex) stage := by
    induction stage with
    | zero => simp
    | succ stage inductionHypothesis =>
      rw [Finset.sum_range_succ, inductionHypothesis]
      abel
  have decomposition : retraction ≫ inclusion + oneMinusShift tower ≫ sectionMap = 𝟙 _ := by
    apply Pi.hom_ext
    intro stage
    simp only [Preadditive.add_comp, Category.assoc, Category.id_comp]
    simp only [inclusion, TowerAugmentation.productLift, Pi.lift_π,
      constantTowerAugmentation, Category.comp_id]
    simp only [sectionMap]
    simp only [oneMinusShift, Pi.lift_π, tower, Functor.const_obj_obj,
      Functor.const_obj_map, Category.comp_id]
    simp only [Preadditive.comp_neg, Preadditive.comp_sum, Pi.lift_π]
    rw [telescoping]
    dsimp [retraction]
    abel
  exact mappingCoconeLift_quasiIso_of_split inclusion (oneMinusShift tower) retraction sectionMap
    (TowerAugmentation.productLift_oneMinusShift (constantTowerAugmentation complex))
    retractIdentity sectionIdentity decomposition

open KoszulCoefficientTower KoszulCompletion

/-- The morphism from the constant tower on a complex to the degree-zero step of its Koszul
filtration. -/
public def constantToZeroFiltration {rank : ℕ} (family : Fin rank → ring)
    (complex : CochainComplex (ModuleCat.{moduleLevel} ring) ℤ) :
    (Functor.const ℕᵒᵖ).obj complex ⟶ (coefficientKoszulFiltration family 0).obj complex where
  app index := (coefficientKoszulFiltrationZeroIso family index.unop).hom.app complex
  naturality source target morphism := by
    apply HomologicalComplex.hom_ext
    intro degree
    exact ((canonicalFormulaLaws family).1.unit_transition (some 0) _ _
      (leOfHom morphism.unop) complex degree).symm

/-- The constant tower on a complex is isomorphic to the degree-zero step of its Koszul
filtration, by `constantToZeroFiltration`. -/
public instance constantToZeroFiltration_isIso {rank : ℕ} (family : Fin rank → ring)
    (complex : CochainComplex (ModuleCat.{moduleLevel} ring) ℤ) :
    IsIso (constantToZeroFiltration family complex) := by
  apply (NatTrans.isIso_iff_isIso_app _).mpr
  intro index
  change IsIso ((coefficientKoszulFiltrationZeroIso family index.unop).hom.app complex)
  infer_instance

/-- For derived-complete coefficients, the inclusion of the degree-zero step of the Koszul
filtration induces a quasi-isomorphism of Milnor fibers. -/
public theorem filtrationZero_milnor_quasiIso {rank : ℕ} (family : Fin rank → ring)
    (complex : CochainComplex (ModuleCat.{moduleLevel} ring) ℤ)
    (complete : IsDerivedComplete (Ideal.span (Set.range family))
      (DerivedCategory.Q.obj complex)) :
    QuasiIso (countableMilnorFunctor.map
      ((coefficientKoszulFiltrationι family 0).app complex)) := by
  have descend (depth : ℕ) :
      QuasiIso (countableMilnorFunctor.map
        ((coefficientKoszulFiltrationι family (-(depth : ℤ))).app complex)) →
      QuasiIso (countableMilnorFunctor.map
        ((coefficientKoszulFiltrationι family 0).app complex)) := by
    induction depth with
    | zero => simp
    | succ depth inductionHypothesis =>
      intro bottomQuasiIso
      have stepQuasiIso := AdicKoszul.coefficientKoszulFiltrationStep_milnor_quasiIso
        family (-((depth + 1 : ℕ) : ℤ)) (by omega) complex complete
      have composite : QuasiIso
          (countableMilnorFunctor.map ((coefficientKoszulFiltrationStep family
            (-((depth + 1 : ℕ) : ℤ))).app complex) ≫
          countableMilnorFunctor.map ((coefficientKoszulFiltrationι family
            (-((depth + 1 : ℕ) : ℤ))).app complex)) := inferInstance
      rw [← Functor.map_comp, ← NatTrans.comp_app, coefficientKoszulFiltrationStep_ι,
        show -((depth + 1 : ℕ) : ℤ) + 1 = -(depth : ℤ) by omega] at composite
      exact inductionHypothesis composite
  apply descend rank
  apply map_quasiIso_and_milnor_triangle.1
  intro stage
  infer_instance

/-- For derived-complete coefficients, the unit of the Koszul coefficient tower induces a
quasi-isomorphism of Milnor fibers. -/
public theorem coefficientUnit_milnor_quasiIso {rank : ℕ} (family : Fin rank → ring)
    (complex : CochainComplex (ModuleCat.{moduleLevel} ring) ℤ)
    (complete : IsDerivedComplete (Ideal.span (Set.range family))
      (DerivedCategory.Q.obj complex)) :
    QuasiIso (countableMilnorFunctor.map ((coefficientKoszulUnit family).app complex)) := by
  have factorization : constantToZeroFiltration family complex ≫
      (coefficientKoszulFiltrationι family 0).app complex =
      (coefficientKoszulUnit family).app complex := by
    apply NatTrans.ext
    funext index
    exact coefficientKoszulFiltrationZeroIso_ι family index.unop complex
  rw [← factorization, Functor.map_comp]
  have := filtrationZero_milnor_quasiIso family complex complete
  infer_instance

/-- The coefficient completion unit of a complex that is derived complete for the ideal generated
by `family` is a quasi-isomorphism. -/
public theorem coefficientCompletionUnit_quasiIso_of_complete
    {rank : ℕ} (family : Fin rank → ring)
    (complex : CochainComplex (ModuleCat.{moduleLevel} ring) ℤ)
    (complete : IsDerivedComplete (Ideal.span (Set.range family))
      (DerivedCategory.Q.obj complex)) :
    QuasiIso ((coefficientCompletionUnit family).app complex) := by
  let augmented : TowerAugmentation ((coefficientKoszulTower family).obj complex) :=
    { source := complex
      app stage := (coefficientKoszulAugmentation family stage).app complex
      naturality stage := coefficientKoszulAugmentation_transition family complex
        (stage + 1) stage (Nat.le_succ stage) }
  have naturality := (constantTowerAugmentation complex).augmentationMap_naturality
    augmented (𝟙 complex) ((coefficientKoszulUnit family).app complex) (fun stage => by
      simp only [constantTowerAugmentation, augmented, Category.id_comp]
      rfl)
  have factorization : (coefficientCompletionUnit family).app complex =
      (constantTowerAugmentation complex).augmentationMap ≫
        countableMilnorFunctor.map ((coefficientKoszulUnit family).app complex) := by
    change 𝟙 complex ≫ (coefficientCompletionUnit family).app complex = _ at naturality
    rwa [Category.id_comp] at naturality
  rw [factorization]
  have := constantTower_augmentation_quasiIso complex
  have := coefficientUnit_milnor_quasiIso family complex complete
  infer_instance

/-- The coefficient completion unit of a complex that is derived complete for the ideal generated
by `family` is a quasi-isomorphism. -/
public theorem AdicKoszul.coefficientCompletionUnit_quasiIso_of_isDerivedComplete
    {rank : ℕ} (family : Fin rank → ring)
    (complex : CochainComplex (ModuleCat.{moduleLevel} ring) ℤ)
    [HasProduct fun _ : ℕ => DerivedCategory.Q.obj complex]
    (complete : IsDerivedComplete (Ideal.span (Set.range family))
      (DerivedCategory.Q.obj complex)) :
    QuasiIso ((KoszulCompletion.coefficientCompletionUnit family).app complex) :=
  coefficientCompletionUnit_quasiIso_of_complete family complex complete

/-- The difference map `∏ₙ K ⟶ ∏ₙ K` of the tower of multiplications by `scalar` on `K`, with
components `π n - π (n + 1) ≫ scalar • 𝟙 K`. -/
public def scalarDifference (object : DerivedCategory (ModuleCat.{moduleLevel} ring)) (scalar :
  ring) :
    (∏ᶜ fun _ : ℕ => object) ⟶ ∏ᶜ fun _ : ℕ => object :=
  Pi.lift fun stage : ℕ => Pi.π (fun _ : ℕ => object) stage -
    Pi.π (fun _ : ℕ => object) (stage + 1) ≫ (scalar • 𝟙 object)

/-- An object is derived complete for an ideal if and only if `scalarDifference object scalar`
is an isomorphism for every `scalar` in the ideal. -/
public theorem complete_iff_scalarDifference_isIso
    (ideal : Ideal ring) (object : DerivedCategory (ModuleCat.{moduleLevel} ring)) :
    IsDerivedComplete ideal object ↔
      ∀ scalar ∈ ideal, IsIso (scalarDifference object scalar) := by
  rw [isDerivedComplete_iff_forall_exists_isDerivedLimit_isZero]
  constructor
  · intro complete scalar membership
    obtain ⟨limitObject, ⟨projection, boundary, distinguished⟩, zero⟩ := complete scalar membership
    simpa only [scalarDifference, Triangle.mk_mor₂, Functor.ofOpSequence_obj,
      Functor.ofOpSequence_map_homOfLE_succ] using!
      (Triangle.isZero₁_iff_isIso₂ _ distinguished).mp zero
  · intro invertible scalar membership
    let diagram := Functor.ofOpSequence (X := fun _ : ℕ => object) (fun _ => scalar • 𝟙 object)
    obtain ⟨limitObject, projection, boundary, distinguished⟩ := exists_isDerivedLimit diagram
    refine ⟨limitObject, ⟨projection, boundary, distinguished⟩,
      (Triangle.isZero₁_iff_isIso₂ _ distinguished).mpr ?_⟩
    simpa only [scalarDifference, Triangle.mk_mor₂, diagram, Functor.ofOpSequence_obj,
      Functor.ofOpSequence_map_homOfLE_succ] using! invertible scalar membership

/-- Derived completeness for an ideal is invariant under isomorphism. -/
public theorem complete_of_iso (ideal : Ideal ring)
    {source target : DerivedCategory (ModuleCat.{moduleLevel} ring)} (comparison : source ≅ target)
    (complete : IsDerivedComplete ideal source) :
    IsDerivedComplete ideal target := by
  rw [complete_iff_scalarDifference_isIso] at complete ⊢
  intro scalar membership
  have := complete scalar membership
  let productIso := Pi.mapIso (fun _ : ℕ => comparison)
  refine AdicKoszul.isIso_of_comp_hom_eq_hom_comp productIso
    (g := scalarDifference source scalar) ?_
  apply Pi.hom_ext
  intro stage
  simp [scalarDifference, productIso, Preadditive.comp_sub, Preadditive.sub_comp,
    Linear.smul_comp, Linear.comp_smul, Category.assoc]

variable {rank : ℕ}

/-- An object is derived complete for an ideal as soon as its universe lift is derived complete
for the image of the ideal in `ULift ring`. -/
public theorem isDerivedComplete_of_universeLift
    (ring : Type ringLevel) [CommRing ring] (ideal : Ideal ring)
    (object : DerivedCategory (ModuleCat.{moduleLevel} ring))
    (complete : IsDerivedComplete
      (ideal.map (ULift.ringEquiv.symm : ring ≃+* ULift.{moduleLevel} ring).toRingHom)
      ((AdicKoszul.derivedUniverseLift ring).obj object)) :
    IsDerivedComplete ideal object := by
  intro scalar membership
  rw [isDerivedCompleteAt_iff_exists_isDerivedLimit_isZero]
  refine (KoszulCompletion.derivedUniverseLift_scalarTower_zero_iff scalar object).mp ?_
  rw [← isDerivedCompleteAt_iff_exists_isDerivedLimit_isZero]
  exact complete (ULift.up scalar) (Ideal.mem_map_of_mem
    (ULift.ringEquiv.symm : ring ≃+* ULift.{moduleLevel} ring).toRingHom membership)

/-- The Koszul power completion of an object is derived complete for the ideal generated by
`family`. -/
public theorem koszulPowerCompletion_complete
    (ring : Type ringLevel) [CommRing ring] {rank : ℕ} (family : Fin rank → ring)
    (tensor : CochainComplex.DerivedTensor.DerivedTensorProduct (ULift.{moduleLevel} ring))
    (completion : AdicKoszul.KoszulPowerCompletion family tensor)
    (object : DerivedCategory (ModuleCat.{moduleLevel} ring)) :
    IsDerivedComplete (Ideal.span (Set.range family))
      (completion.functor.obj object) := by
  apply isDerivedComplete_of_universeLift
  have complete := AdicKoszul.rlim_derivedTensor_koszulPowers_isDerivedComplete
    (fun index => (ULift.up (family index) : ULift.{moduleLevel} ring))
    (fun stage => AdicKoszul.koszulPowerTransition _ (stage + 1) stage (Nat.le_succ stage))
    tensor ((AdicKoszul.derivedUniverseLift ring).obj object)
    ((AdicKoszul.derivedUniverseLift ring).obj (completion.functor.obj object))
    (completion.isDerivedLimit object)
  have spanEquality :
      (Ideal.span (Set.range family)).map
        (ULift.ringEquiv.symm : ring ≃+* ULift.{moduleLevel} ring).toRingHom =
      Ideal.span (Set.range fun index => (ULift.up (family index) : ULift.{moduleLevel} ring)) := by
    rw [Ideal.map_span, ← Set.range_comp]
    rfl
  rwa [spanEquality]

/-- The completion functor precomposed with the localization functor is the coefficient completion
complex followed by the localization functor. -/
public def completionLocalIso (family : Fin rank → ring) :
    DerivedCategory.Q (C := ModuleCat.{moduleLevel} ring) ⋙ completionFunctor family ≅
      coefficientCompletionComplex family ⋙ DerivedCategory.Q :=
  Localization.fac _ (coefficientCompletion_isInvertedBy family) _

/-- On the image of a complex, the completion unit is the localization of the coefficient
completion unit followed by `completionLocalIso`. -/
public theorem completionUnit_representative (family : Fin rank → ring)
    (complex : CochainComplex (ModuleCat.{moduleLevel} ring) ℤ) :
    (completionUnit family).app (DerivedCategory.Q.obj complex) =
      DerivedCategory.Q.map ((coefficientCompletionUnit family).app complex) ≫
        (completionLocalIso family).inv.app complex := by
  simp only [completionUnit, Localization.liftNatTrans_app, Functor.whiskerRight_app,
    completionLocalIso, Localization.fac, Localization.Lifting.iso,
    Functor.rightUnitor_hom_app]
  erw [Category.id_comp]

/-- An object is derived complete for the ideal generated by `family` if and only if the
completion unit at it is an isomorphism. -/
public theorem canonicalCompletion_criterion
    (family : Fin rank → ring)
    (tensor : CochainComplex.DerivedTensor.DerivedTensorProduct (ULift.{moduleLevel} ring))
    (object : DerivedCategory (ModuleCat.{moduleLevel} ring)) :
    IsDerivedComplete (Ideal.span (Set.range family)) object ↔
      IsIso ((completionUnit family).app object) := by
  constructor
  · intro complete
    let representative := (DerivedCategory.Q (C := ModuleCat.{moduleLevel} ring)).objPreimage object
    let representativeIso := (DerivedCategory.Q (C := ModuleCat.{moduleLevel}
      ring)).objObjPreimageIso object
    have representativeComplete := complete_of_iso (Ideal.span (Set.range family))
      representativeIso.symm complete
    have quasiIso := coefficientCompletionUnit_quasiIso_of_complete family representative
      representativeComplete
    have unitIso : IsIso ((completionUnit family).app (DerivedCategory.Q.obj representative)) := by
      rw [completionUnit_representative]
      infer_instance
    exact (NatTrans.isIso_app_iff_of_iso (completionUnit family) representativeIso).mp unitIso
  · intro unitIso
    have complete := koszulPowerCompletion_complete ring family tensor (completionData family
      tensor) object
    exact complete_of_iso (Ideal.span (Set.range family))
      (asIso ((completionUnit family).app object)).symm complete

namespace AdicKoszul

attribute [local instance 2000] HasDerivedCategory.standard
attribute [local instance] derivedCountableProducts

/-- The Koszul derived-completion functor, its unit, and the criterion for derived
completeness in terms of that unit. -/
public theorem koszulCompletionSolution
    (family : Fin rank → ring)
    (tensor : CochainComplex.DerivedTensor.DerivedTensorProduct (ULift.{moduleLevel} ring)) :
    ∃ completion : KoszulPowerCompletion.{ringLevel, moduleLevel} family tensor,
      ∀ object : DerivedCategory (ModuleCat.{moduleLevel} ring),
        IsDerivedComplete (Ideal.span (Set.range family)) object ↔
          IsIso (completion.unit.app object) :=
  ⟨completionData.{ringLevel, moduleLevel} family tensor,
    canonicalCompletion_criterion family tensor⟩

end AdicKoszul

end

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe u v

namespace AdicKoszul

variable {A : Type u} [CommRing A]

attribute [local instance] HasDerivedCategory.standard derivedCountableProducts
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CountableMilnorTower KoszulCoefficientTower

/-- The Koszul derived limit and its canonical natural map exist for every complex. A complex is
derived complete for the ideal generated by `f` if and only if the component of this map is an
isomorphism. The ring and module universes are independent; only the tensor calculation is
enlarged using `ULift`. -/
@[stacks 091Z]
public theorem isDerivedComplete_iff_isIso_to_rlim_derivedTensor_koszulPowers
    {r : ℕ} (f : Fin r → A)
    (T : CochainComplex.DerivedTensor.DerivedTensorProduct (ULift.{v} A)) :
    ∃ C : KoszulPowerCompletion f T, ∀ K : DerivedCategory (ModuleCat.{v} A),
      IsDerivedComplete (Ideal.span (Set.range f)) K ↔
        IsIso (C.unit.app K) :=
  koszulCompletionSolution f T

end AdicKoszul

end
