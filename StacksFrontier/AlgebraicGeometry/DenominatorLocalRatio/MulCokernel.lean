module

public import StacksFrontier.AlgebraicGeometry.DenominatorLocalRatio.Cokernels
public import StacksFrontier.AlgebraicGeometry.DenominatorColonIdeal.Basic

/-!
# The cokernel of multiplication by a regular meromorphic section

## References

* [Stacks Project, Tag 02P0](https://stacks.math.columbia.edu/tag/02P0)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open Stacks.DenominatorIdeal Stacks.DenominatorIdealResidue

universe u

namespace Stacks.DenominatorCokernel

variable (X : Scheme.{u}) (L : SheafOfModules.{u} (O X))
  (s : MeromorphicSection.{u, u} X.sheaf L)

/-- **The numerator of a local ratio is a nonzerodivisor**, for a *regular* meromorphic section.
If `c · a = 0`, where `a` is the image of the numerator `t` under a trivialization, then `c · t`
vanishes, hence so does `c · b · s`; regularity of `s` and injectivity of `𝒪_X ⟶ K_X` on sections
then force `c · b = 0`, and `b` is a nonzerodivisor. -/
lemma mem_nonZeroDivisors_of_trivialization
    (hs : IsRegularMeromorphicSection X.sheaf L s) {V : Opens X}
    (e : (L.val.obj (op V) : Type u) ≃ₗ[Stacks.DenominatorLocalRatio.oScalar X V]
      (Stacks.DenominatorLocalRatio.oScalar X V))
    (b : Stacks.DenominatorLocalRatio.oScalar X V) (hb : b ∈ nonZeroDivisors Γ(X, V))
    (t : (L.val.obj (op V) : Type u))
    (hbt : (toK X L).val.app (op V) t = (sectionMap X L s).val.app (op V) b)
    (a : Γ(X, V)) (ha : e t = a) :
    a ∈ nonZeroDivisors Γ(X, V) := by
  have key : ∀ c : Γ(X, V), c * a = 0 → c = 0 := by
    intro c hc
    obtain ⟨c', hc'⟩ : ∃ c' : Stacks.DenominatorLocalRatio.oScalar X V, c = c' := ⟨c, rfl⟩
    have hct : c' • t = 0 := by
      refine e.injective ?_
      have h1 : e (c' • t) = c' * (e t) := by
        rw [map_smul]
        rfl
      rw [h1, map_zero, ha, ← hc']
      exact hc
    have h2 : (sectionMap X L s).val.app (op V) (c' * b) =
        c' • (sectionMap X L s).val.app (op V) b :=
      map_smul ((sectionMap X L s).val.app (op V)).hom c' b
    have h5 : c' • (toK X L).val.app (op V) t = (toK X L).val.app (op V) (c' • t) :=
      (map_smul ((toK X L).val.app (op V)).hom c' t).symm
    have h3 : (sectionMap X L s).val.app (op V) (c' * b) = 0 := by
      rw [h2, ← hbt, h5, hct, map_zero]
    have h6 : ((K X L).unitHomEquiv.symm s).val.app (op V)
        ((toTotalQuotientSheaf X.sheaf).hom.app (op V) (c' * b)) =
        ((K X L).unitHomEquiv.symm s).val.app (op V)
          ((toTotalQuotientSheaf X.sheaf).hom.app (op V) (0 : Γ(X, V))) := by
      rw [← sectionMap_app_apply X L s (op V) (c' * b),
        ← sectionMap_app_apply X L s (op V) (0 : Γ(X, V)), h3]
      exact (map_zero ((sectionMap X L s).val.app (op V)).hom).symm
    have h4 : (c' * b : Γ(X, V)) = 0 :=
      toTotalQuotientSheaf_app_injective X V (injective_regularSection_app X L s hs (op V) h6)
    rw [hc']
    exact (mem_nonZeroDivisors_iff.mp hb).2 c' h4
  exact mem_nonZeroDivisors_iff.mpr
    ⟨fun x hx => key x (by rw [mul_comm]; exact hx), fun x hx => key x hx⟩

/-- The second projection of the denominator ideal hits the numerator of a local ratio: if
`toK t = b · s` then the denominator `d` with `ι d = b` has `mul d = t`. -/
lemma exists_denominatorIdealMul_eq
    (hL : AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf (O X).property L)
    {V : Opens X} (b : (((SheafOfModules.unit (O X)).val.obj (op V)) : Type u))
    (t : (L.val.obj (op V) : Type u))
    (hbt : (toK X L).val.app (op V) t = (sectionMap X L s).val.app (op V) b) :
    ∃ d : (denominatorIdeal X L s).val.obj (op V),
      (denominatorIdealMul X L s).val.app (op V) d = t := by
  obtain ⟨d, hd⟩ := (denominatorIdeal_sections X L s V b).mpr ⟨t, hbt.symm⟩
  refine ⟨d, Stacks.DenominatorColonIdeal.injective_toK_app X L hL (op V) ?_⟩
  rw [← app_condition X L s V d, hd, ← hbt]

/-- **Where the numerator of a local ratio is invertible, multiplication by the section is
surjective on sections.**  If `mul d₁ = tW` and the trivialization sends `tW` to a unit, then
every section `v` of `L` is `mul` of the corresponding multiple of `d₁`. -/
lemma exists_eq_denominatorIdealMul_app {W : Opens X}
    (eW : (L.val.obj (op W) : Type u) ≃ₗ[Stacks.DenominatorLocalRatio.oScalar X W]
      (Stacks.DenominatorLocalRatio.oScalar X W))
    (d₁ : (denominatorIdeal X L s).val.obj (op W)) (tW : (L.val.obj (op W) : Type u))
    (hd₁ : (denominatorIdealMul X L s).val.app (op W) d₁ = tW)
    (aW : Stacks.DenominatorLocalRatio.oScalar X W) (haW : eW tW = aW) (hu : IsUnit aW)
    (v : (L.val.obj (op W) : Type u)) :
    ∃ d : (denominatorIdeal X L s).val.obj (op W),
      (denominatorIdealMul X L s).val.app (op W) d = v := by
  obtain ⟨u, hu'⟩ := hu
  have hms : (denominatorIdealMul X L s).val.app (op W)
      ((eW v * (↑u⁻¹ : Stacks.DenominatorLocalRatio.oScalar X W)) • d₁) =
      (eW v * (↑u⁻¹ : Stacks.DenominatorLocalRatio.oScalar X W)) • tW := by
    rw [← hd₁]
    exact map_smul ((denominatorIdealMul X L s).val.app (op W)).hom _ d₁
  refine ⟨(eW v * (↑u⁻¹ : Stacks.DenominatorLocalRatio.oScalar X W)) • d₁,
    eW.injective ?_⟩
  rw [hms, map_smul, haW, ← hu']
  change (eW v * (↑u⁻¹ : Stacks.DenominatorLocalRatio.oScalar X W)) *
    (↑u : Stacks.DenominatorLocalRatio.oScalar X W) = eW v
  rw [mul_assoc, Units.inv_mul, mul_one]

/-- **The cokernel of multiplication by a regular meromorphic section of an invertible sheaf is
supported on a closed nowhere dense subset.**  Stacks Tag 02P0, "support of the second
cokernel". -/
@[stacks 02P0 "support of the second cokernel"]
theorem denominatorIdeal_section_support
    (hL : AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf (O X).property L)
    (hs : IsRegularMeromorphicSection X.sheaf L s) :
    ∃ T : Set X, IsClosed T ∧ IsNowhereDense T ∧
      (asModuleSheaf X (cokernel (denominatorIdealMul X L s))).supp ⊆ T := by
  choose V _ hxV hVaff htriv b hb t hbt using fun x : X =>
    Stacks.DenominatorLocalRatio.exists_affineOpen_denominator X L s hL ⊤ x (Opens.mem_top x)
  have hanzd : ∀ x : X, ((htriv x).some.θ (V x) (𝟙 (V x)) (t x) : Γ(X, V x)) ∈
      nonZeroDivisors Γ(X, V x) := fun x =>
    mem_nonZeroDivisors_of_trivialization X L s hs ((htriv x).some.θ (V x) (𝟙 (V x)))
      (b x) (hb x) (t x) (hbt x) _ rfl
  obtain ⟨hTclosed, hTnd⟩ := isClosed_isNowhereDense_compl_iSup_basicOpen X V hxV hVaff
    (fun x => ((htriv x).some.θ (V x) (𝟙 (V x)) (t x) : Γ(X, V x))) hanzd
  refine ⟨_, hTclosed, hTnd, fun y hy => ?_⟩
  intro hyW
  obtain ⟨x, hx⟩ := Opens.mem_iSup.mp hyW
  refine notMem_supp_cokernel X (denominatorIdealMul X L s) y (fun U hyU => ?_) hy
  have hWV : U ⊓ X.basicOpen ((htriv x).some.θ (V x) (𝟙 (V x)) (t x) : Γ(X, V x)) ≤ V x :=
    inf_le_right.trans (X.basicOpen_le _)
  obtain ⟨d, hd⟩ := exists_denominatorIdealMul_eq X L s hL (b x) (t x) (hbt x)
  refine ⟨U ⊓ X.basicOpen ((htriv x).some.θ (V x) (𝟙 (V x)) (t x) : Γ(X, V x)),
    inf_le_left, ⟨hyU, hx⟩, fun v => ?_⟩
  refine exists_eq_denominatorIdealMul_app X L s ((htriv x).some.θ _ (homOfLE hWV))
    ((denominatorIdeal X L s).val.map (homOfLE hWV).op d)
    (L.val.map (homOfLE hWV).op (t x)) ?_
    (X.presheaf.map (homOfLE hWV).op ((htriv x).some.θ (V x) (𝟙 (V x)) (t x))) ?_
    (isUnit_res_of_le_basicOpen X _ inf_le_right hWV) v
  · exact (PresheafOfModules.naturality_apply (denominatorIdealMul X L s).val
      (homOfLE hWV).op d).trans (congrArg (fun z => L.val.map (homOfLE hWV).op z) hd)
  · exact (htriv x).some.θ_naturality (𝟙 (V x)) (homOfLE hWV) (t x)

end Stacks.DenominatorCokernel

end
