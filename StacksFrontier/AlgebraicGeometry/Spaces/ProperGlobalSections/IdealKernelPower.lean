module

public import StacksFrontier.AlgebraicGeometry.Spaces.ProperGlobalSections.FibreThickening
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentCompletionFunctor
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineChartBaseChangePresieve

/-!
# The powers of the sheaf of ideals `J 𝒪_X` and the multiples `Jⁿ F`

Let `X` be an algebraic space, `φ : A →+* Γ(X, 𝒪_X)` a ring map and `J ⊆ A` an ideal, and write
`𝓘 = J 𝒪_X` for the kernel of `𝒪_X ⟶ 𝒪_X / J 𝒪_X` (`AlgebraicGeometry.Space.idealKernel`).  Two
spellings of `Jⁿ F` for an `𝒪_X`-module `F` are in use: the image `Jⁿ F` of multiplication by the
elements of `Jⁿ` (`AlgebraicGeometry.Space.idealMultiple`), out of which the theorem on formal
functions is built, and the least sheaf submodule `𝓘ⁿ F` containing `𝓘(U)ⁿ F(U)` over every étale
chart (`AlgebraicGeometry.Space.idealPowerMultiple`), out of which the category `Coh(X, 𝓘)` and the
completion functor of Stacks 08B4 are built.  This file identifies them.

## Main results

* `AlgebraicGeometry.Space.idealPowerMultiple_idealKernel_eq_ker`: `𝓘ⁿ F` is the kernel of
  `F ⟶ F / Jⁿ F`.
* `AlgebraicGeometry.Space.idealPowerQuotientIsoIdealQuotient`: `F / 𝓘ⁿ F ≅ F / Jⁿ F`, compatibly
  with the two projections from `F`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Cohomology.SiteModules

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {X : AlgebraicSpaces B S hS} {A : Type u} [CommRing A]
  (φ : A →+* ↥(GlobalSectionRing ((Stacks.SheafOfModules.Tensor.ringSheaf
    (smallEtaleRingedSite B S hS X.1 X.2).O)))) (J : Ideal A)

/-- The functions `φ a`, `a ∈ J`, are sections of `J 𝒪_X` over every étale chart. -/
theorem idealChartEval_mem_idealKernel {a : A} (ha : a ∈ J) (U : SmallEtale B S hS X.1) :
    idealChartEval φ U a ∈ (idealKernel φ J).obj (op U) := by
  refine (SheafOfModules.Submodule.mem_ker _ (op U) _).2 ?_
  have h : (globalSmul _ (φ a) (structureSheafModule B S hS X) ≫
      idealQuotientπ φ (structureSheafModule B S hS X) J).val.app (op U)
        (1 : ToType ((structureRingSheaf B S hS X).obj.obj (op U))) = 0 := by
    rw [← comp_globalSmul, globalSmul_idealQuotient_eq_zero φ _ J ha, comp_zero]
    rfl
  have h2 : (globalSmul _ (φ a) (structureSheafModule B S hS X)).val.app (op U)
      (1 : ToType ((structureRingSheaf B S hS X).obj.obj (op U))) = (φ a).1 (op U) :=
    (globalSmul_app _ _ _ _ _).trans
      (mul_one (show ToType ((structureRingSheaf B S hS X).obj.obj (op U)) from (φ a).1 (op U)))
  exact (congrArg (fun y => (idealQuotientπ φ (structureSheafModule B S hS X) J).val.app (op U) y)
    h2.symm).trans h

/-- The functions `φ a`, `a ∈ Jⁿ`, are sections of `(J 𝒪_X)ⁿ` over every étale chart. -/
theorem idealChartEval_mem_chartIdeal_pow (n : ℕ) {a : A} (ha : a ∈ J ^ n)
    (U : SmallEtale B S hS X.1) :
    idealChartEval φ U a ∈ chartIdeal B S hS ⟨X.1, X.2⟩ (idealKernel φ J) U ^ n := by
  have h : Ideal.map (idealChartEval φ U) J ≤ chartIdeal B S hS ⟨X.1, X.2⟩ (idealKernel φ J) U :=
    Ideal.map_le_iff_le_comap.2 fun b hb => idealChartEval_mem_idealKernel φ J hb U
  have hm : idealChartEval φ U a ∈ Ideal.map (idealChartEval φ U) J ^ n :=
    (Ideal.map_pow (S := chartRing B S hS X.1 X.2 U) (idealChartEval φ U) J n).le
      (Ideal.mem_map_of_mem _ ha)
  exact Ideal.pow_right_mono h n hm

/-- Over an affine étale chart, `(J 𝒪_X)ⁿ` is the extension of `Jⁿ`. -/
theorem chartIdeal_idealKernel_pow_le_of_isAffine (n : ℕ) (U : SmallEtale B S hS X.1)
    (hU : IsAffine ((SmallEtale.toOver B S hS X.1 ⋙ BigFppfOver.toScheme B S hS).obj U)) :
    chartIdeal B S hS ⟨X.1, X.2⟩ (idealKernel φ J) U ^ n ≤
      Ideal.map (S := chartRing B S hS X.1 X.2 U) (idealChartEval φ U) (J ^ n) := by
  have h : chartIdeal B S hS ⟨X.1, X.2⟩ (idealKernel φ J) U ≤
      Ideal.map (S := chartRing B S hS X.1 X.2 U) (idealChartEval φ U) J :=
    fun x hx => (mem_idealKernel_iff_of_isAffine φ J U hU x).1 hx
  exact (Ideal.pow_right_mono h n).trans
    (Ideal.map_pow (S := chartRing B S hS X.1 X.2 U) (idealChartEval φ U) J n).ge

variable (M : Modules.{u, u} B S hS X.1 X.2)

/-- The extension of `Jⁿ` to an étale chart annihilates the sections of `M / Jⁿ M` there. -/
theorem smul_idealQuotient_eq_zero_of_mem_map (n : ℕ) (U : SmallEtale B S hS X.1)
    {r : chartRing B S hS X.1 X.2 U}
    (hr : r ∈ Ideal.map (S := chartRing B S hS X.1 X.2 U) (idealChartEval φ U) (J ^ n))
    (q : (idealQuotient φ M (J ^ n)).val.obj (op U)) : r • q = 0 := by
  refine Submodule.span_induction (p := fun r _ => r • q = 0) ?_ ?_ ?_ ?_ hr
  · rintro _ ⟨a, ha, rfl⟩
    exact congrArg (fun g : idealQuotient φ M (J ^ n) ⟶ idealQuotient φ M (J ^ n) =>
      g.val.app (op U) q) (globalSmul_idealQuotient_eq_zero φ M (J ^ n) ha)
  · exact zero_smul _ q
  · intro x y _ _ hx hy
    rw [add_smul, hx, hy, add_zero]
  · intro c x _ hx
    rw [smul_eq_mul, mul_smul, hx, smul_zero]

/-- **`(J 𝒪_X)ⁿ` annihilates `M / Jⁿ M`.** -/
theorem isPowAnnihilated_idealQuotient_idealKernel (n : ℕ) :
    IsPowAnnihilated B S hS X.1 X.2 (idealKernel φ J) n (idealQuotient φ M (J ^ n)) := by
  intro U r hr q
  refine (idealQuotient φ M (J ^ n)).isSheaf.isSeparated U _
    (SmallEtale.generate_affineChartPresieve_mem B S hS X.1 U) _ 0 fun W i hi => ?_
  obtain ⟨W', h, g, hW', rfl⟩ := hi
  show (idealQuotient φ M (J ^ n)).val.restrictₛₗ (h ≫ g).op (r • q) =
    (idealQuotient φ M (J ^ n)).val.restrictₛₗ (h ≫ g).op 0
  rw [map_zero]
  refine (restrictₛₗ_restrictₛₗ B S hS X.1 X.2 _ g.op h.op (r • q)).symm.trans ?_
  have key : (idealQuotient φ M (J ^ n)).val.restrictₛₗ g.op (r • q) = 0 := by
    refine (((idealQuotient φ M (J ^ n)).val.map g.op).hom.map_smul r q).trans ?_
    exact smul_idealQuotient_eq_zero_of_mem_map φ J M n W'
      (chartIdeal_idealKernel_pow_le_of_isAffine φ J n W' hW'
        (chartRestrict_mem_chartIdeal_pow B S hS X.1 X.2 (idealKernel φ J) g n hr)) _
  exact (congrArg _ key).trans (map_zero _)

/-- `(J 𝒪_X)ⁿ M` lies in the kernel of `M ⟶ M / Jⁿ M`. -/
theorem idealPowerMultiple_ι_comp_idealQuotientπ (n : ℕ) :
    (idealPowerMultiple B S hS X.1 X.2 (idealKernel φ J) n M).ι ≫
      idealQuotientπ φ M (J ^ n) = 0 := by
  rw [idealPowerMultiple_ι_comp_eq_zero_iff]
  intro U r hr x
  rw [((idealQuotientπ φ M (J ^ n)).val.app (op U)).hom.map_smul r x]
  exact isPowAnnihilated_idealQuotient_idealKernel φ J M n U r hr _

/-- `Jⁿ M` lies in `(J 𝒪_X)ⁿ M`. -/
theorem idealMultipleι_comp_cokernelπ_idealPowerMultiple (n : ℕ) :
    idealMultipleι φ M (J ^ n) ≫
      cokernel.π (idealPowerMultiple B S hS X.1 X.2 (idealKernel φ J) n M).ι = 0 := by
  refine (cancel_epi (Abelian.factorThruImage (idealMultipleHom φ M (J ^ n)))).1 ?_
  rw [comp_zero, ← Category.assoc, Abelian.image.fac]
  refine Sigma.hom_ext _ _ fun a => ?_
  rw [comp_zero, ← Category.assoc, ι_idealMultipleHom]
  ext U x
  obtain ⟨U⟩ := U
  refine (cokernel_π_app_eq_zero_iff B S hS X.1 X.2 _ (op U) _).2 ?_
  exact le_idealPowerMultiple_obj B S hS X.1 X.2 (idealKernel φ J) n M U
    (Submodule.smul_mem_smul (idealChartEval_mem_chartIdeal_pow φ J n a.2 U) Submodule.mem_top)

/-- **`(J 𝒪_X)ⁿ M` is the kernel of `M ⟶ M / Jⁿ M`.** -/
theorem idealPowerMultiple_idealKernel_eq_ker (n : ℕ) :
    idealPowerMultiple B S hS X.1 X.2 (idealKernel φ J) n M =
      SheafOfModules.Submodule.ker (idealQuotientπ φ M (J ^ n)) := by
  refine le_antisymm ((submodule_ι_comp_eq_zero_iff B S hS X.1 X.2 _ _).1
    (idealPowerMultiple_ι_comp_idealQuotientπ φ J M n)) ?_
  intro U x hx
  have := (idealShortComplex_shortExact φ M (J ^ n)).mono_f
  let K := SheafOfModules.Submodule.ker (idealQuotientπ φ M (J ^ n))
  let l : K.toSheafOfModules ⟶ idealMultiple φ M (J ^ n) :=
    (idealShortComplex_shortExact φ M (J ^ n)).exact.fIsKernel.lift
      (KernelFork.ofι K.ι (SheafOfModules.Submodule.ker_ι_comp _))
  have hl : l ≫ idealMultipleι φ M (J ^ n) = K.ι :=
    (idealShortComplex_shortExact φ M (J ^ n)).exact.fIsKernel.fac _ WalkingParallelPair.zero
  have h0 := congrArg (fun g : K.toSheafOfModules ⟶ cokernel
      (idealPowerMultiple B S hS X.1 X.2 (idealKernel φ J) n M).ι => g.val.app U ⟨x, hx⟩)
    (show K.ι ≫ cokernel.π (idealPowerMultiple B S hS X.1 X.2 (idealKernel φ J) n M).ι = 0 by
      rw [← hl, Category.assoc, idealMultipleι_comp_cokernelπ_idealPowerMultiple φ J M n,
        comp_zero])
  exact (cokernel_π_app_eq_zero_iff B S hS X.1 X.2 _ U x).1 h0

/-- **`M / (J 𝒪_X)ⁿ M ≅ M / Jⁿ M`**: the quotient out of which the completion functor of Stacks
08B4 is built is the quotient of the theorem on formal functions. -/
def idealPowerQuotientIsoIdealQuotient (n : ℕ) :
    idealPowerQuotient B S hS X.1 X.2 (idealKernel φ J) n M ≅ idealQuotient φ M (J ^ n) where
  hom := cokernel.desc _ (idealQuotientπ φ M (J ^ n))
    (idealPowerMultiple_ι_comp_idealQuotientπ φ J M n)
  inv := cokernel.desc _ (cokernel.π _) (idealMultipleι_comp_cokernelπ_idealPowerMultiple φ J M n)
  hom_inv_id := (cancel_epi (cokernel.π _)).1 (by
    rw [← Category.assoc, cokernel.π_desc, cokernel.π_desc, Category.comp_id])
  inv_hom_id := (cancel_epi (idealQuotientπ φ M (J ^ n))).1 (by
    rw [← Category.assoc, cokernel.π_desc, cokernel.π_desc, Category.comp_id])

/-- The projection `M ⟶ M / (J 𝒪_X)ⁿ M` followed by `M / (J 𝒪_X)ⁿ M ≅ M / Jⁿ M` is the projection
`M ⟶ M / Jⁿ M`. -/
@[reassoc (attr := simp)]
theorem cokernelπ_comp_idealPowerQuotientIsoIdealQuotient_hom (n : ℕ) :
    cokernel.π (idealPowerMultiple B S hS X.1 X.2 (idealKernel φ J) n M).ι ≫
      (idealPowerQuotientIsoIdealQuotient φ J M n).hom = idealQuotientπ φ M (J ^ n) :=
  cokernel.π_desc _ _ _

/-- The projection `M ⟶ M / Jⁿ M` followed by `M / Jⁿ M ≅ M / (J 𝒪_X)ⁿ M` is the projection
`M ⟶ M / (J 𝒪_X)ⁿ M`. -/
@[reassoc (attr := simp)]
theorem idealQuotientπ_comp_idealPowerQuotientIsoIdealQuotient_inv (n : ℕ) :
    idealQuotientπ φ M (J ^ n) ≫ (idealPowerQuotientIsoIdealQuotient φ J M n).inv =
      cokernel.π (idealPowerMultiple B S hS X.1 X.2 (idealKernel φ J) n M).ι :=
  cokernel.π_desc _ _ _

/-- The identification `M / (J 𝒪_X)ⁿ M ≅ M / Jⁿ M` is compatible with the transition maps. -/
@[reassoc]
theorem idealPowerQuotientMapOfLE_comp_idealPowerQuotientIsoIdealQuotient_hom {k l : ℕ}
    (h : k ≤ l) :
    idealPowerQuotientMapOfLE B S hS X.1 X.2 (idealKernel φ J) h M ≫
        (idealPowerQuotientIsoIdealQuotient φ J M k).hom =
      (idealPowerQuotientIsoIdealQuotient φ J M l).hom ≫
        idealQuotientMap φ M (Ideal.pow_le_pow_right h : J ^ l ≤ J ^ k) := by
  refine (cancel_epi (cokernel.π _)).1 ?_
  rw [← Category.assoc, π_comp_idealPowerQuotientMapOfLE,
    cokernelπ_comp_idealPowerQuotientIsoIdealQuotient_hom,
    cokernelπ_comp_idealPowerQuotientIsoIdealQuotient_hom_assoc, idealQuotientπ_idealQuotientMap]

/-- The identification `M / (J 𝒪_X)ⁿ M ≅ M / Jⁿ M` is natural in `M`. -/
@[reassoc]
theorem idealQuotientπ_comp_idealPowerQuotientMapOfHom_conj (n : ℕ)
    {M' : Modules.{u, u} B S hS X.1 X.2} (g : M ⟶ M') :
    idealQuotientπ φ M (J ^ n) ≫ (idealPowerQuotientIsoIdealQuotient φ J M n).inv ≫
        idealPowerQuotientMapOfHom B S hS X.1 X.2 (idealKernel φ J) n g ≫
          (idealPowerQuotientIsoIdealQuotient φ J M' n).hom =
      g ≫ idealQuotientπ φ M' (J ^ n) := by
  rw [idealQuotientπ_comp_idealPowerQuotientIsoIdealQuotient_inv_assoc, ← Category.assoc,
    π_comp_idealPowerQuotientMapOfHom, Category.assoc,
    cokernelπ_comp_idealPowerQuotientIsoIdealQuotient_hom]

end AlgebraicGeometry.Space

end
