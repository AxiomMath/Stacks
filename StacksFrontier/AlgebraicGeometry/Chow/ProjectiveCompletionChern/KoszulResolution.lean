module

public import StacksFrontier.AlgebraicGeometry.Chow.ProjectiveCompletionChern.ZeroSectionStalk
public import StacksFrontier.AlgebraicGeometry.Chow.ProjectiveCompletionChern.KoszulExactness
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorPowerLineSubsheaf

/-!
# The Koszul complex of the projective completion resolves `i_* 𝒪_X`

Let `E = Proj_X(Sym^*(𝒞)[T])`, `𝒦 = Ker(π^*(𝒞 ⊕ 𝒪_X) ⟶ 𝒪_E(1))` with `φ : 𝒦 ⟶ 𝒪_E`, and
`i : X ⟶ E` the zero section. The Koszul complex `⋯ ⟶ ⋀² 𝒦 ⟶ 𝒦 ⟶ 𝒪_E` of `φ` is exact in
positive homological degrees, and its cokernel in degree zero is `i_* 𝒪_X`: the sequence
`⋀¹ 𝒦 ⟶ ⋀⁰ 𝒦 ⟶ i_* 𝒪_X ⟶ 0` is exact. It is checked at the stalks: on the chart `W = D₊(T)`
both the image of `φ_ξ` and the kernel of `𝒪_{E, ξ} ⟶ (i_* 𝒪_X)_ξ` are the ideal of the
coordinates, and off `C = {T ≠ 0}` the functional `φ_ξ` is onto and `(i_* 𝒪_X)_ξ = 0`.

## Main definitions

* `koszulAug`: the augmentation `⋀⁰ 𝒦 ≅ 𝒪_E ⟶ i_* 𝒪_X`.

## Main results

* `exteriorPower.contraction_zero_eq`: the contraction `⋀¹ M ⟶ ⋀⁰ M = R` is the functional.
* `koszulContraction_zero_comp_koszulAug`: the composite `⋀¹ 𝒦 ⟶ ⋀⁰ 𝒦 ⟶ i_* 𝒪_X` is zero.
* `exact_koszulAug`: the sequence `⋀¹ 𝒦 ⟶ ⋀⁰ 𝒦 ⟶ i_* 𝒪_X` is exact.
* `epi_koszulAug`: the augmentation `⋀⁰ 𝒦 ⟶ i_* 𝒪_X` is an epimorphism.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u

/-- An element of `⋀⁰ M` is its coordinate times the generator. -/
theorem exteriorPower.eq_zeroEquiv_smul_symm_one {R M : Type*} [CommRing R] [AddCommGroup M]
    [Module R M] (v : ⋀[R]^0 M) :
    v = exteriorPower.zeroEquiv R M v • (exteriorPower.zeroEquiv R M).symm 1 := by
  rw [← map_smul, smul_eq_mul, mul_one, LinearEquiv.symm_apply_apply]

/-- **The contraction in degree zero is the functional**: `ι(m) ↦ ψ(m) · 1`. -/
theorem exteriorPower.contraction_zero_eq {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (ψ : M →ₗ[R] R) (v : ⋀[R]^1 M) :
    exteriorPower.contraction ψ 0 v =
      ψ (exteriorPower.oneEquiv R M v) • (exteriorPower.zeroEquiv R M).symm 1 := by
  have hv : v = exteriorPower.ιMulti R 1 (fun _ => exteriorPower.oneEquiv R M v) := by
    rw [← exteriorPower.oneEquiv_symm_apply, LinearEquiv.symm_apply_apply]
  conv_lhs => rw [hv]
  rw [exteriorPower.contraction_ιMulti, Fin.sum_univ_one, exteriorPower.zeroEquiv_symm_apply,
    one_smul]
  simp only [pow_zero, one_smul, Fin.val_zero]
  congr 2
  funext i
  exact i.elim0

namespace Stacks.Chow.ProjectiveCompletion

variable {X : Scheme.{u}} (𝒞 : X.Modules)
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} 𝒞]

attribute [local implicit_reducible] TopCat.Sheaf sheafCompose

/-- The comparison `(⋀ⁿ 𝒦)_ξ ≅ ⋀ⁿ(𝒦_ξ)` of Tag 01CH. -/
abbrev wedgeStalk (n : ℕ) (ξ : space 𝒞) :=
  SheafOfModules.exteriorPowerStalkEquiv (Osharp := (space 𝒞).sheaf)
    (Scheme.Modules.exteriorAlgebra (kernelModule 𝒞))
    (Scheme.Modules.exteriorGenerator (kernelModule 𝒞))
    (Scheme.Modules.isExteriorAlgebra_exteriorAlgebra (kernelModule 𝒞)) n ξ

/-- The generator of the stalk of `⋀⁰ 𝒦`. -/
def wedgeZeroGen (ξ : space 𝒞) :
    ↑(TopCat.Presheaf.stalk (Scheme.Modules.exteriorPower (kernelModule 𝒞)
      ((0 : ℕ) : ℤ)).val.presheaf ξ) :=
  (wedgeStalk 𝒞 0 ξ).symm ((exteriorPower.zeroEquiv _ _).symm 1)

/-- The coordinate of `a • wedgeZeroGen 𝒞 ξ` in `⋀⁰(𝒦_ξ)` is `a` times the generator. -/
private theorem wedgeStalk_zero_smul_wedgeZeroGen (ξ : space 𝒞)
    (a : ↑(TopCat.Presheaf.stalk (space 𝒞).sheaf.obj ξ)) :
    wedgeStalk 𝒞 0 ξ (a • wedgeZeroGen 𝒞 ξ) =
      a • (exteriorPower.zeroEquiv _ _).symm 1 := by
  refine (wedgeStalk 𝒞 0 ξ).map_smul a _ |>.trans (congrArg (a • ·) ?_)
  exact LinearEquiv.apply_symm_apply _ _

/-- **The stalk of the Koszul differential `⋀¹ 𝒦 ⟶ ⋀⁰ 𝒦` is `φ_ξ`**, in the basis of the
stalk of `⋀⁰ 𝒦`. -/
theorem stalkMapL_koszulContraction_zero (ξ : space 𝒞)
    (w : ↑(TopCat.Presheaf.stalk (Scheme.Modules.exteriorPower (kernelModule 𝒞)
      ((0 + 1 : ℕ) : ℤ)).val.presheaf ξ)) :
    PresheafOfModules.stalkMapL ξ
        (Scheme.Modules.koszulContraction (kernelModule 𝒞) (koszulMap 𝒞) 0).val w =
      Stacks.KoszulStalk.stalkDual (Osharp := (space 𝒞).sheaf) (M := kernelModule 𝒞)
          (koszulMap 𝒞) ξ (exteriorPower.oneEquiv _ _ (wedgeStalk 𝒞 (0 + 1) ξ w)) •
        wedgeZeroGen 𝒞 ξ := by
  apply (wedgeStalk 𝒞 0 ξ).injective
  refine (SheafOfModules.exteriorPowerStalkEquiv_stalkMapL_exteriorContraction
    (Osharp := (space 𝒞).sheaf) (Scheme.Modules.exteriorAlgebra (kernelModule 𝒞))
    (Scheme.Modules.exteriorGenerator (kernelModule 𝒞))
    (Scheme.Modules.isExteriorAlgebra_exteriorAlgebra (kernelModule 𝒞)) (koszulMap 𝒞) 0 ξ
    (Stacks.KoszulStalk.stalkDual (Osharp := (space 𝒞).sheaf) (M := kernelModule 𝒞)
      (koszulMap 𝒞) ξ)
    (Stacks.KoszulStalk.stalkDual_germ (Osharp := (space 𝒞).sheaf) (koszulMap 𝒞) ξ) w).trans ?_
  exact (exteriorPower.contraction_zero_eq _ _).trans
    (wedgeStalk_zero_smul_wedgeZeroGen 𝒞 ξ _).symm

omit [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} 𝒞] in
/-- The stalk map of the identity morphism is the identity. -/
theorem stalkMapL_id {Y : Scheme.{u}} (A : SheafOfModules.{u} Y.ringCatSheaf) (y : Y)
    (k : ↑(TopCat.Presheaf.stalk A.val.presheaf y)) :
    PresheafOfModules.stalkMapL y (𝟙 A : A ⟶ A).val k = k := by
  change ConcreteCategory.hom ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} y).map
      ((PresheafOfModules.toPresheaf _).map (𝟙 A.val))) k = _
  rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]
  rfl

omit [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} 𝒞] in
/-- For an isomorphism `e : A ≅ B`, the stalk map of `e.inv` is left inverse to that of `e.hom`. -/
theorem stalkMapL_inv_hom {Y : Scheme.{u}} {A B : SheafOfModules.{u} Y.ringCatSheaf} (e : A ≅ B)
    (y : Y) (k : ↑(TopCat.Presheaf.stalk A.val.presheaf y)) :
    PresheafOfModules.stalkMapL y e.inv.val (PresheafOfModules.stalkMapL y e.hom.val k) = k := by
  rw [← stalkMapL_comp, e.hom_inv_id, stalkMapL_id]

omit [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} 𝒞] in
/-- For an isomorphism `e : A ≅ B`, the stalk map of `e.hom` is left inverse to that of `e.inv`. -/
theorem stalkMapL_hom_inv {Y : Scheme.{u}} {A B : SheafOfModules.{u} Y.ringCatSheaf} (e : A ≅ B)
    (y : Y) (k : ↑(TopCat.Presheaf.stalk B.val.presheaf y)) :
    PresheafOfModules.stalkMapL y e.hom.val (PresheafOfModules.stalkMapL y e.inv.val k) = k := by
  rw [← stalkMapL_comp, e.inv_hom_id, stalkMapL_id]

/-- The identification `⋀⁰ 𝒦 ≅ 𝒪_E`. -/
def wedgeZeroIso : Scheme.Modules.exteriorPower (kernelModule 𝒞) ((0 : ℕ) : ℤ) ≅
    SheafOfModules.unit (space 𝒞).ringCatSheaf :=
  (SheafOfModules.algebras _ (kernelModule 𝒞)).exteriorPieceIso_zero

/-- The stalk of `⋀⁰ 𝒦 ≅ 𝒪_E`, read on the stalk ring. -/
abbrev wedgeZeroStalk (ξ : space 𝒞) :=
  Stacks.KoszulStalk.stalkDual (Osharp := (space 𝒞).sheaf) (wedgeZeroIso 𝒞).hom ξ

/-- The map `wedgeZeroStalk 𝒞 ξ` from the stalk of `⋀⁰ 𝒦` to the stalk ring `𝒪_{E, ξ}` is
bijective. -/
theorem bijective_wedgeZeroStalk (ξ : space 𝒞) :
    Function.Bijective (wedgeZeroStalk 𝒞 ξ) :=
  (Stacks.AlgebraicGeometry.ProjEulerSequence.unitStalkCommEquiv (space 𝒞).sheaf
    ξ).bijective.comp ⟨Function.LeftInverse.injective (stalkMapL_inv_hom (wedgeZeroIso 𝒞) ξ),
      Function.RightInverse.surjective (stalkMapL_hom_inv (wedgeZeroIso 𝒞) ξ)⟩

/-- Every element of the stalk of `⋀⁰ 𝒦` is its coordinate in `⋀⁰(𝒦_ξ)` times
`wedgeZeroGen 𝒞 ξ`. -/
theorem eq_smul_wedgeZeroGen (ξ : space 𝒞)
    (y : ↑(TopCat.Presheaf.stalk (Scheme.Modules.exteriorPower (kernelModule 𝒞)
      ((0 : ℕ) : ℤ)).val.presheaf ξ)) :
    y = exteriorPower.zeroEquiv ↑(TopCat.Presheaf.stalk (space 𝒞).sheaf.obj ξ)
      ↑(TopCat.Presheaf.stalk (kernelModule 𝒞).val.presheaf ξ) (wedgeStalk 𝒞 0 ξ y) •
        wedgeZeroGen 𝒞 ξ := by
  apply (wedgeStalk 𝒞 0 ξ).injective
  exact (exteriorPower.eq_zeroEquiv_smul_symm_one _).trans
    (wedgeStalk_zero_smul_wedgeZeroGen 𝒞 ξ _).symm

/-- The image of the generator `wedgeZeroGen 𝒞 ξ` in `𝒪_{E, ξ}` is a unit. -/
theorem isUnit_wedgeZeroStalk_gen (ξ : space 𝒞) :
    IsUnit (wedgeZeroStalk 𝒞 ξ (wedgeZeroGen 𝒞 ξ)) := by
  obtain ⟨y, hy⟩ := (bijective_wedgeZeroStalk 𝒞 ξ).2 1
  rw [eq_smul_wedgeZeroGen 𝒞 ξ y, map_smul, smul_eq_mul] at hy
  exact IsUnit.of_mul_eq_one_right _ hy

variable (r : ℕ) [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} 𝒞 r]

/-- **The augmentation `⋀⁰ 𝒦 ≅ 𝒪_E ⟶ i_* 𝒪_X`.** -/
def koszulAug : Scheme.Modules.exteriorPower (kernelModule 𝒞) ((0 : ℕ) : ℤ) ⟶
    (Scheme.Modules.pushforward (zeroSec 𝒞 r)).obj (SheafOfModules.unit X.ringCatSheaf) :=
  (wedgeZeroIso 𝒞).hom ≫ unitToZeroSec 𝒞 r

/-- The stalk of `koszulAug` sends `a • wedgeZeroGen 𝒞 ξ` to the image under `epsStalk` of
`a` times the image of the generator in `𝒪_{E, ξ}`. -/
theorem stalkMapL_koszulAug (ξ : space 𝒞) (a : ↑(TopCat.Presheaf.stalk (space 𝒞).sheaf.obj ξ)) :
    PresheafOfModules.stalkMapL ξ (koszulAug 𝒞 r).val (a • wedgeZeroGen 𝒞 ξ) =
      epsStalk 𝒞 r ξ (a * wedgeZeroStalk 𝒞 ξ (wedgeZeroGen 𝒞 ξ)) := by
  refine (stalkMapL_comp (wedgeZeroIso 𝒞).hom (unitToZeroSec 𝒞 r) ξ _).trans ?_
  change _ = PresheafOfModules.stalkMapL ξ (unitToZeroSec 𝒞 r).val
    ((Stacks.AlgebraicGeometry.ProjEulerSequence.unitStalkCommEquiv (space 𝒞).sheaf ξ).symm
      (a * wedgeZeroStalk 𝒞 ξ (wedgeZeroGen 𝒞 ξ)))
  refine congrArg (PresheafOfModules.stalkMapL ξ (unitToZeroSec 𝒞 r).val) ?_
  refine Eq.trans ?_ (congrArg (Stacks.AlgebraicGeometry.ProjEulerSequence.unitStalkCommEquiv
    (space 𝒞).sheaf ξ).symm ((wedgeZeroStalk 𝒞 ξ).map_smul a (wedgeZeroGen 𝒞 ξ)))
  exact ((Stacks.AlgebraicGeometry.ProjEulerSequence.unitStalkCommEquiv (space 𝒞).sheaf
    ξ).symm_apply_apply _).symm

/-- For a functional `ψ` and a basis `e` with `ψ (e j) = g j`, the image of `ψ` is the ideal
spanned by the `g j`. -/
theorem exists_apply_eq_iff_mem_span_of_basis {R M ι : Type*} [Fintype ι] [CommRing R]
    [AddCommGroup M] [Module R M] (ψ : M →ₗ[R] R) (e : Module.Basis ι R M) {g : ι → R}
    (he : ∀ j, ψ (e j) = g j) (f : R) : (∃ k, ψ k = f) ↔ f ∈ Ideal.span (Set.range g) := by
  refine ⟨?_, fun hg => (Ideal.span_le (I := LinearMap.range ψ)).2
    (Set.range_subset_iff.2 fun j => ⟨e j, he j⟩) hg⟩
  rintro ⟨k, rfl⟩
  rw [← e.sum_repr k, map_sum]
  refine Ideal.sum_mem _ fun j _ => ?_
  rw [map_smul, he j]
  exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨j, rfl⟩)

/-- **The kernel of `𝒪_{E, ξ} ⟶ (i_* 𝒪_X)_ξ` is the image of `φ_ξ`**, at every point of `E`. -/
theorem epsStalk_eq_zero_iff (ξ : space 𝒞) (f : ↑(TopCat.Presheaf.stalk (space 𝒞).sheaf.obj ξ)) :
    epsStalk 𝒞 r ξ f = 0 ↔ ∃ k, Stacks.KoszulStalk.stalkDual (Osharp := (space 𝒞).sheaf)
      (M := kernelModule 𝒞) (koszulMap 𝒞) ξ k = f := by
  obtain ⟨V, hV, hξV, ⟨b⟩⟩ := exists_isAffineOpen_basis_sections 𝒞 r ((proj 𝒞).base ξ)
  by_cases hW : ξ ∈ openW 𝒞 hV
  · obtain ⟨e, he⟩ := exists_basis_stalkDual 𝒞 hV b ξ hW
    have h := exists_apply_eq_iff_mem_span_of_basis _ e he f
    exact ⟨fun hf => h.2 (mem_span_of_epsStalk_eq_zero 𝒞 r hV b ξ hW f hf),
      fun hf => epsStalk_eq_zero_of_mem_span 𝒞 r hV b ξ hW f (h.1 hf)⟩
  · have hT : ξ ∉ openT 𝒞 := fun h => hW (by rw [openW_eq]; exact ⟨h, hξV⟩)
    obtain ⟨ζ, hζ⟩ : ξ ∈ Set.range (chart 𝒞 V hV) := by
      rw [← Scheme.Hom.coe_opensRange, ← Scheme.Hom.image_top_eq_opensRange, chart_image_top_eq]
      exact hξV
    rcases mem_chartD_or_exists_mem_basicOpen 𝒞 b ζ hV with h | ⟨k, hk⟩
    · exact absurd (by rw [← hζ]; exact (Scheme.Hom.apply_mem_image_iff _).2 h) hW
    · have hk' : ξ ∈ chartOpen 𝒞 hV (chartE 𝒞 (b k)) := by
        rw [← hζ]
        exact (Scheme.Hom.apply_mem_image_iff _).2 hk
      obtain ⟨v, hv⟩ := exists_stalkDual_eq_one 𝒞 hV (b k) ξ hk'
      exact ⟨fun _ => ⟨f • v, (Stacks.KoszulStalk.stalkDual (Osharp := (space 𝒞).sheaf)
        (M := kernelModule 𝒞) (koszulMap 𝒞) ξ).map_smul f v |>.trans
          (by rw [hv, smul_eq_mul, mul_one])⟩,
        fun _ => eq_zero_of_notMem_openT 𝒞 r ξ hT _⟩

/-- At every stalk, the Koszul differential `⋀¹ 𝒦 ⟶ ⋀⁰ 𝒦` followed by `koszulAug` is zero. -/
theorem stalkMapL_koszulContraction_zero_koszulAug (ξ : space 𝒞)
    (w : ↑(TopCat.Presheaf.stalk (Scheme.Modules.exteriorPower (kernelModule 𝒞)
      ((0 + 1 : ℕ) : ℤ)).val.presheaf ξ)) :
    PresheafOfModules.stalkMapL ξ (koszulAug 𝒞 r).val (PresheafOfModules.stalkMapL ξ
        (Scheme.Modules.koszulContraction (kernelModule 𝒞) (koszulMap 𝒞) 0).val w) = 0 := by
  rw [stalkMapL_koszulContraction_zero, stalkMapL_koszulAug]
  refine (epsStalk_eq_zero_iff 𝒞 r ξ _).2 ⟨wedgeZeroStalk 𝒞 ξ (wedgeZeroGen 𝒞 ξ) •
    exteriorPower.oneEquiv _ _ (wedgeStalk 𝒞 (0 + 1) ξ w), ?_⟩
  exact ((Stacks.KoszulStalk.stalkDual (Osharp := (space 𝒞).sheaf) (M := kernelModule 𝒞)
    (koszulMap 𝒞) ξ).map_smul _ _).trans (mul_comm _ _)

/-- **The augmented Koszul complex is a complex in degree zero.** -/
theorem koszulContraction_zero_comp_koszulAug :
    Scheme.Modules.koszulContraction (kernelModule 𝒞) (koszulMap 𝒞) 0 ≫ koszulAug 𝒞 r = 0 :=
  Stacks.SheafOfModules.TopWedge.eq_zero_of_stalkMapL_eq_zero (Osharp := (space 𝒞).sheaf) _
    fun ξ z => (stalkMapL_comp _ _ ξ z).trans (stalkMapL_koszulContraction_zero_koszulAug 𝒞 r ξ z)

/-- If an element `y` of the stalk of `⋀⁰ 𝒦` lies in the kernel of the stalk of `koszulAug`,
then its coordinate in `⋀⁰(𝒦_ξ)` is in the image of `φ_ξ`. -/
theorem exists_stalkDual_eq_coord (ξ : space 𝒞)
    (y : ↑(TopCat.Presheaf.stalk (Scheme.Modules.exteriorPower (kernelModule 𝒞)
      ((0 : ℕ) : ℤ)).val.presheaf ξ))
    (hy : PresheafOfModules.stalkMapL ξ (koszulAug 𝒞 r).val y = 0) :
    ∃ k, Stacks.KoszulStalk.stalkDual (Osharp := (space 𝒞).sheaf) (M := kernelModule 𝒞)
      (koszulMap 𝒞) ξ k = exteriorPower.zeroEquiv ↑(TopCat.Presheaf.stalk (space 𝒞).sheaf.obj ξ)
        ↑(TopCat.Presheaf.stalk (kernelModule 𝒞).val.presheaf ξ) (wedgeStalk 𝒞 0 ξ y) := by
  set a := exteriorPower.zeroEquiv ↑(TopCat.Presheaf.stalk (space 𝒞).sheaf.obj ξ)
    ↑(TopCat.Presheaf.stalk (kernelModule 𝒞).val.presheaf ξ) (wedgeStalk 𝒞 0 ξ y)
  have hy' := (congrArg (PresheafOfModules.stalkMapL ξ (koszulAug 𝒞 r).val)
    (eq_smul_wedgeZeroGen 𝒞 ξ y)).symm.trans hy
  rw [stalkMapL_koszulAug] at hy'
  obtain ⟨k, hk⟩ := (epsStalk_eq_zero_iff 𝒞 r ξ _).1 hy'
  obtain ⟨c, hc⟩ := (isUnit_wedgeZeroStalk_gen 𝒞 ξ).exists_left_inv
  refine ⟨c • k, ((Stacks.KoszulStalk.stalkDual (Osharp := (space 𝒞).sheaf)
    (M := kernelModule 𝒞) (koszulMap 𝒞) ξ).map_smul c k).trans ?_⟩
  rw [smul_eq_mul, hk, mul_comm a, ← mul_assoc, hc, one_mul]

/-- **`⋀¹ 𝒦 ⟶ ⋀⁰ 𝒦 ⟶ i_* 𝒪_X` is exact.** -/
theorem exact_koszulAug :
    (ShortComplex.mk _ _ (koszulContraction_zero_comp_koszulAug 𝒞 r)).Exact := by
  refine (AlgebraicGeometry.SheafOfModules.exact_iff_stalkFunctor_map_exact _).2 fun ξ => ?_
  refine (ShortComplex.moduleCat_exact_iff _).2 fun y hy => ?_
  obtain ⟨k, hk⟩ := exists_stalkDual_eq_coord 𝒞 r ξ y hy
  refine ⟨(wedgeStalk 𝒞 (0 + 1) ξ).symm ((exteriorPower.oneEquiv _ _).symm k), ?_⟩
  refine (stalkMapL_koszulContraction_zero 𝒞 ξ _).trans ?_
  have h1 : exteriorPower.oneEquiv ↑(TopCat.Presheaf.stalk (space 𝒞).sheaf.obj ξ)
      ↑(TopCat.Presheaf.stalk (kernelModule 𝒞).val.presheaf ξ) (wedgeStalk 𝒞 (0 + 1) ξ
      ((wedgeStalk 𝒞 (0 + 1) ξ).symm ((exteriorPower.oneEquiv _ _).symm k))) = k := by
    simp
  refine (congrArg (fun z => Stacks.KoszulStalk.stalkDual (Osharp := (space 𝒞).sheaf)
    (M := kernelModule 𝒞) (koszulMap 𝒞) ξ z • wedgeZeroGen 𝒞 ξ) h1).trans ?_
  refine (congrArg (fun z => z • wedgeZeroGen 𝒞 ξ) hk).trans ?_
  exact (eq_smul_wedgeZeroGen 𝒞 ξ y).symm

/-- The augmentation `⋀⁰ 𝒦 ⟶ i_* 𝒪_X` is an epimorphism. -/
theorem epi_koszulAug : Epi (koszulAug 𝒞 r) := by
  have h1 : Epi (unitToZeroSec 𝒞 r) :=
    ClosedImmersionCoherentImage.epi_unitToPushforwardUnit (zeroSec 𝒞 r)
  have h2 : Epi (wedgeZeroIso 𝒞).hom := ⟨fun g h hgh =>
    (Iso.inv_hom_id_assoc (wedgeZeroIso 𝒞) g).symm.trans
      ((congrArg (fun t => (wedgeZeroIso 𝒞).inv ≫ t) hgh).trans
        (Iso.inv_hom_id_assoc (wedgeZeroIso 𝒞) h))⟩
  exact @epi_comp _ _ _ _ _ _ h2 _ h1

end Stacks.Chow.ProjectiveCompletion

end
