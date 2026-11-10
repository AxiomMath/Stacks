module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.LaurentAlgebraChartSections
public import StacksFrontier.AlgebraicGeometry.Spaces.SymmetricAlgebraSheafQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Stacks.InvertibleCoherent

/-!
# The Laurent algebra of an invertible sheaf has few sections

In Situation 0EDT let `X/B` be good and let `ℒ` be an invertible `𝒪_X`-module.  This file proves
that the Laurent algebra `𝒜 = ⨁_{n ∈ ℤ} ℒ^{⊗ n}` satisfies the size condition
`AlgebraicGeometry.Space.AlgebraSheaf.SectionsBelowCutoff` of the bounded relative spectrum: over
every étale chart `V` of `X` the ring `𝒜(V)` has fewer than `B.cutoff` elements.  So the
multiplicative torsor `\underline{Spec}_X(𝒜)` is formed inside the big fppf site of `X`, with no
hypothesis on `ℒ` beyond invertibility.

## Main results

* `Cardinal.mk_directSum_le`: a countable direct sum of types of size at most an infinite `κ`
  has size at most `κ`.
* `AlgebraicGeometry.Space.mk_sections_laurentAlgebraSheaf_le_of_isAffine`: over an affine chart
  `W`, `#𝒜(W) ≤ #𝒪(W) ⊔ ℵ₀`.
* `AlgebraicGeometry.Space.sectionsBelowCutoff_laurentAlgebraSheaf`: the size condition.

## References

* [Stacks Project, Tag 0EQG](https://stacks.math.columbia.edu/tag/0EQG)
* [Stacks Project, Tag 081W](https://stacks.math.columbia.edu/tag/081W)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Cardinal

universe u

namespace Cardinal

/-- A countable direct sum of types of size at most an infinite cardinal `κ` has size at most
`κ`. -/
theorem mk_directSum_le {ι : Type} [Countable ι] (M : ι → Type u)
    [∀ i, AddCommMonoid (M i)] {κ : Cardinal.{u}} (hκ : ℵ₀ ≤ κ) (hM : ∀ i, #(M i) ≤ κ) :
    #(DirectSum ι M) ≤ κ := by
  classical
  let f : List (Σ i, M i) → DirectSum ι M := fun l => (l.map fun x => DirectSum.of M x.1 x.2).sum
  have hf : Function.Surjective f := by
    intro z
    induction z using DirectSum.induction_on with
    | zero => exact ⟨[], rfl⟩
    | of i m => exact ⟨[⟨i, m⟩], by simp [f]⟩
    | add a b ha hb =>
      obtain ⟨la, rfl⟩ := ha
      obtain ⟨lb, rfl⟩ := hb
      exact ⟨la ++ lb, by simp [f]⟩
  refine (mk_le_of_surjective hf).trans ((mk_list_le_max _).trans (max_le hκ ?_))
  rw [mk_sigma]
  refine (sum_le_sum _ (fun _ => κ) hM).trans ?_
  rw [sum_const, lift_uzero]
  exact (mul_le_mul' (lift_le_aleph0.2 mk_le_aleph0 |>.trans hκ) le_rfl).trans (mul_eq_self hκ).le

end Cardinal

namespace AlgebraicGeometry.Space

variable (D : BaseSpaceDimensionSituation.{u})
    {X : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (p : X ⟶ D.space) (hp : D.IsGood p)
    (L : Modules.{u, u} D.site D.base D.base_mem X hp.1)
    (hL : IsInvertibleSheaf D p hp L)

/-- The sections of the Laurent algebra over an affine étale chart `W` number at most
`#𝒪(W) ⊔ ℵ₀`. -/
theorem mk_sections_laurentAlgebraSheaf_le_of_isAffine
    (W : SmallEtale D.site D.base D.base_mem X)
    (hW : IsAffine ((SmallEtale.toOver D.site D.base D.base_mem X ⋙
      BigFppfOver.toScheme D.site D.base D.base_mem).obj W)) :
    #((laurentAlgebraSheaf D p hp L hL).right.obj.obj (op W)) ≤
      #(chartRing D.site D.base D.base_mem X hp.1 W) ⊔ ℵ₀ := by
  have hbij := bijective_laurentDirectSumHom_app_of_isAffine D p hp L hL W hW
  have : Stacks.SheafOfModules.IsInvertible (tensorStructureRingPresheaf D p hp)
      (isSheaf_tensorStructureRingPresheaf D p hp) L :=
    Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ L hL
  refine (mk_le_of_surjective hbij.2).trans ?_
  refine Cardinal.mk_directSum_le
    (fun n : ℤ => ((laurentGradedAlgebra D p hp L hL).piece n).val.obj (op W))
    le_sup_right fun n => ?_
  let G : Modules.{u, u} D.site D.base D.base_mem X hp.1 :=
    (laurentGradedAlgebra D p hp L hL).piece n
  have hfp : SheafOfModules.IsFinitePresentationOnSite G :=
    Stacks.SheafOfModules.isFinitePresentationOnSite_of_isInvertible _ _
      (Stacks.SheafOfModules.TensorPower.isInvertible_tensorPower
        (tensorStructureRingPresheaf D p hp) (isSheaf_tensorStructureRingPresheaf D p hp) L n)
  have hfin := module_finitePresentation_sections_of_isFinitePresentationOnSite
    (B := D.site) (S := D.base) (hS := D.base_mem) (F := X) (hF := hp.1) G
    (SheafOfModules.isQuasicoherentOnSite_of_isFinitePresentationOnSite G) hfp W hW
  change #(G.val.obj (op W)) ≤ _
  exact mk_le_of_module_finite

/-- The Laurent algebra `⨁_{n ∈ ℤ} ℒ^{⊗ n}` of an invertible `𝒪_X`-module has fewer than
`B.cutoff` sections over every étale chart of `X`: the size condition of the bounded relative
spectrum. -/
theorem sectionsBelowCutoff_laurentAlgebraSheaf :
    AlgebraSheaf.SectionsBelowCutoff D.site D.base D.base_mem (X := ⟨X, hp.1⟩)
      (laurentAlgebraSheaf D p hp L hL) := by
  intro V
  have hV : D.site.Contains (chartScheme V) := V.obj.left.left.property
  set κ : Cardinal.{u} := 2 ^ (chartScheme V).size ⊔ ℵ₀ with hκ
  have hκlt : κ < D.site.cutoff :=
    max_lt (D.site.cutoff_isStrongPrelimit hV) D.site.aleph0_lt_cutoff
  have hκ0 : ℵ₀ ≤ κ := le_sup_right
  have hbound : ∀ W' : (chartScheme V).affineOpens,
      #((laurentAlgebraSheaf D p hp L hL).right.obj.obj
        (op ((chartOpens D.site D.base D.base_mem V).obj (W' : (chartScheme V).Opens)))) ≤ κ := by
    intro W'
    have hW' : IsAffine ((SmallEtale.toOver D.site D.base D.base_mem X ⋙
        BigFppfOver.toScheme D.site D.base D.base_mem).obj
          ((chartOpens D.site D.base D.base_mem V).obj (W' : (chartScheme V).Opens))) := W'.2
    have hR : #(chartRing D.site D.base D.base_mem X hp.1
        ((chartOpens D.site D.base D.base_mem V).obj (W' : (chartScheme V).Opens))) ≤
          2 ^ (chartScheme V).size :=
      (Scheme.mk_sections_le_two_pow_size _ ⊤).trans
        (Cardinal.power_le_power_left two_ne_zero
          (Scheme.size_coe_opens_le (chartScheme V) (W' : (chartScheme V).Opens)))
    exact (mk_sections_laurentAlgebraSheaf_le_of_isAffine D p hp L hL _ hW').trans
      (max_le (hR.trans le_sup_left) hκ0)
  refine (AlgebraSheaf.mk_sections_le_mk_pi_affineOpens D.site D.base D.base_mem ⟨X, hp.1⟩ _
    V).trans_lt ?_
  rw [Cardinal.mk_pi]
  refine (Cardinal.prod_le_prod _ _ hbound).trans_lt ?_
  rw [Cardinal.prod_const']
  calc κ ^ #(chartScheme V).affineOpens ≤ κ ^ κ :=
        Cardinal.power_le_power_left (ne_of_gt (lt_of_lt_of_le Cardinal.aleph0_pos hκ0))
          ((chartScheme V).mk_affineOpens_le_size.trans ((Cardinal.cantor _).le.trans le_sup_left))
    _ = 2 ^ κ := Cardinal.power_self_eq hκ0
    _ < D.site.cutoff := D.site.cutoff_isStrongPrelimit hκlt

end AlgebraicGeometry.Space

end
