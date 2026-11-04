module

public import StacksFrontier.AlgebraicGeometry.Chow.TensorZeroScheme.BranchProjection

/-!
# A diagram of Tag 0F97 whose branches are literally zero schemes

Condition (3) of [Stacks, Tag 0F97] says that the closed subscheme `Dᵢ` of a diagram
`R : Stacks.Chow.TensorZeroScheme.Decomposition Y L₁ L₂ s` is the zero scheme of the section
`sᵢ` of `p^*Lᵢ`. In `Decomposition` this is an equality of ideal sheaves, the field `zeroScheme₁`
(resp. `zeroScheme₂`).

This file replaces `D₁` and `D₂` by the two zero schemes themselves, transporting the remaining
data along the isomorphisms `Z(sᵢ) ≅ Dᵢ` given by the inclusions of equal ideal sheaves. The
result `R.normalize` is again a diagram as in the tag, with the same total space, projection and
sections, and its `Dᵢ` is `Z(sᵢ)` by definition.

## Main definitions

* `Stacks.Chow.TensorZeroScheme.Decomposition.intersectionProj`: the isomorphism `D₁ ∩ D₂ ⟶ D`
  through the first branch.
* `Stacks.Chow.TensorZeroScheme.Decomposition.normalize`: the diagram with `Dᵢ := Z(sᵢ)`.

## References

* [Stacks Project, Tag 0F97](https://stacks.math.columbia.edu/tag/0F97)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Chow.TensorZeroScheme

/-- The inclusion of two equal ideal sheaves is an isomorphism. -/
theorem isIso_inclusion_of_eq {X : Scheme.{u}} {I J : X.IdealSheafData} (h : I = J) :
    IsIso (Scheme.IdealSheafData.inclusion h.le) := by
  subst h
  rw [Scheme.IdealSheafData.inclusion_id]
  infer_instance

namespace Decomposition

variable {Y : Scheme.{u}} {L₁ L₂ : Y.Modules}
  [h₁ : AlgebraicGeometry.SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property L₁]
  [h₂ : AlgebraicGeometry.SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property L₂]
  {s : Γ(Stacks.Divisors.tensorModules L₁ L₂, ⊤)} (R : Decomposition Y L₁ L₂ s)

include h₁ h₂ in
/-- The projection `p : L ⟶ Y` of a diagram of Tag 0F97 is locally of finite type. -/
instance : LocallyOfFiniteType R.p := R.p_locallyOfFiniteType

include h₁ h₂ in
/-- The projection `p : L ⟶ Y` of a diagram of Tag 0F97 is quasi-compact. -/
instance : QuasiCompact R.p := R.p_quasiCompact

include h₁ h₂ in
/-- The projection `p : L ⟶ Y` of a diagram of Tag 0F97 is flat. -/
instance : AlgebraicGeometry.Flat R.p := R.p_flat

include h₁ h₂ in
/-- The branch projection `p₁ : D₁ ⟶ D` is locally of finite type. -/
instance : LocallyOfFiniteType R.p₁ := Decomposition.locallyOfFiniteType_p₁ Y L₁ L₂ s R

include h₁ h₂ in
/-- The branch projection `p₁ : D₁ ⟶ D` is flat. -/
instance : AlgebraicGeometry.Flat R.p₁ := Decomposition.flat_p₁ Y L₁ L₂ s R

include h₁ h₂ in
/-- The branch projection `p₂ : D₂ ⟶ D` is locally of finite type. -/
instance : LocallyOfFiniteType R.p₂ := Decomposition.locallyOfFiniteType_p₂ Y L₁ L₂ s R

include h₁ h₂ in
/-- The branch projection `p₂ : D₂ ⟶ D` is flat. -/
instance : AlgebraicGeometry.Flat R.p₂ := Decomposition.flat_p₂ Y L₁ L₂ s R

include h₁ h₂ in
/-- The morphism `D₁ ∩ D₂ ⟶ D` of a diagram of Tag 0F97, through the first branch. It is an
isomorphism by condition (6). -/
def intersectionProj : (R.D₁ ⊔ R.D₂).subscheme ⟶ (zeroIdeal Y L₁ L₂ s).subscheme :=
  Scheme.IdealSheafData.inclusion (le_sup_left : R.D₁ ≤ R.D₁ ⊔ R.D₂) ≫ R.p₁

include h₁ h₂ in
/-- The morphism `D₁ ∩ D₂ ⟶ D` is an isomorphism, by condition (6) of Tag 0F97. -/
instance : IsIso R.intersectionProj := R.intersection_isIso

include h₁ h₂ in
/-- `D₁ ∩ D₂ ⟶ L ⟶ Y` factors through `D ⟶ Y` by the morphism `D₁ ∩ D₂ ⟶ D`. -/
theorem sup_subschemeι_comp_p :
    (R.D₁ ⊔ R.D₂).subschemeι ≫ R.p = R.intersectionProj ≫ (zeroIdeal Y L₁ L₂ s).subschemeι := by
  rw [intersectionProj, Category.assoc, ← R.comm₁, ← Category.assoc,
    Scheme.IdealSheafData.inclusion_subschemeι]

include h₁ h₂ in
/-- Condition (6) of Tag 0F97 survives replacing the two branches by equal ideal sheaves. -/
theorem isIso_inclusion_comp_of_eq {E₁ E₂ : R.total.IdealSheafData} (e₁ : R.D₁ = E₁)
    (e₂ : R.D₂ = E₂) :
    IsIso (Scheme.IdealSheafData.inclusion (le_sup_left : E₁ ≤ E₁ ⊔ E₂) ≫
      Scheme.IdealSheafData.inclusion e₁.le ≫ R.p₁) := by
  subst e₁ e₂
  simpa using R.intersection_isIso

include h₁ h₂ in
/-- Condition (7) of Tag 0F97 for the first branch survives replacing the two branches by equal
ideal sheaves. -/
theorem inclusion_comp_zeroSection₁_of_eq {E₁ E₂ : R.total.IdealSheafData} (e₁ : R.D₁ = E₁)
    (e₂ : R.D₂ = E₂) :
    Scheme.IdealSheafData.inclusion (le_sup_left : E₁ ≤ E₁ ⊔ E₂) ≫
        Scheme.IdealSheafData.inclusion e₁.le ≫ R.branch₁.hom =
      (Scheme.IdealSheafData.inclusion (le_sup_left : E₁ ≤ E₁ ⊔ E₂) ≫
          Scheme.IdealSheafData.inclusion e₁.le ≫ R.p₁) ≫
        (branchSituation Y L₁ L₂ s L₂).zeroSection := by
  subst e₁ e₂
  rw [Scheme.IdealSheafData.inclusion_id, Category.id_comp, Category.id_comp]
  exact R.intersection_zeroSection₁

include h₁ h₂ in
/-- Condition (7) of Tag 0F97 for the second branch survives replacing the two branches by equal
ideal sheaves. -/
theorem inclusion_comp_zeroSection₂_of_eq {E₁ E₂ : R.total.IdealSheafData} (e₁ : R.D₁ = E₁)
    (e₂ : R.D₂ = E₂) :
    Scheme.IdealSheafData.inclusion (le_sup_right : E₂ ≤ E₁ ⊔ E₂) ≫
        Scheme.IdealSheafData.inclusion e₂.le ≫ R.branch₂.hom =
      (Scheme.IdealSheafData.inclusion (le_sup_right : E₂ ≤ E₁ ⊔ E₂) ≫
          Scheme.IdealSheafData.inclusion e₂.le ≫ R.p₂) ≫
        (branchSituation Y L₁ L₂ s L₁).zeroSection := by
  subst e₁ e₂
  rw [Scheme.IdealSheafData.inclusion_id, Category.id_comp, Category.id_comp]
  exact R.intersection_zeroSection₂

include h₁ h₂ in
/-- **A diagram of [Stacks, Tag 0F97] whose two branches are literally the zero schemes of the
two sections.** The total space, the projection and the sections are those of `R`; `Dᵢ` is the
zero scheme of `sᵢ`, which is `R.Dᵢ` by condition (3), and the maps `pᵢ` and the identifications
of condition (4) are those of `R` precomposed with the inclusion of equal ideal sheaves. -/
def normalize : Decomposition Y L₁ L₂ s where
  total := R.total
  p := R.p
  D₁ := Stacks.Divisors.zeroScheme R.total ((Scheme.Modules.pullback R.p).obj L₁) R.s₁
  D₂ := Stacks.Divisors.zeroScheme R.total ((Scheme.Modules.pullback R.p).obj L₂) R.s₂
  p₁ := Scheme.IdealSheafData.inclusion R.zeroScheme₁.le ≫ R.p₁
  p₂ := Scheme.IdealSheafData.inclusion R.zeroScheme₂.le ≫ R.p₂
  comm₁ := by
    rw [Category.assoc, ← R.comm₁, ← Category.assoc, Scheme.IdealSheafData.inclusion_subschemeι]
  comm₂ := by
    rw [Category.assoc, ← R.comm₂, ← Category.assoc, Scheme.IdealSheafData.inclusion_subschemeι]
  s₁ := R.s₁
  s₂ := R.s₂
  pullback_section_eq := R.pullback_section_eq
  p_locallyOfFiniteType := R.p_locallyOfFiniteType
  p_quasiCompact := R.p_quasiCompact
  p_flat := R.p_flat
  p_relativeDimension := R.p_relativeDimension
  zeroScheme₁ := rfl
  zeroScheme₂ := rfl
  branch₁ :=
    haveI := isIso_inclusion_of_eq R.zeroScheme₁
    asIso (Scheme.IdealSheafData.inclusion R.zeroScheme₁.le) ≪≫ R.branch₁
  branch₁_toBase := by
    simp only [Iso.trans_hom, asIso_hom, Category.assoc, R.branch₁_toBase]
    rfl
  branch₂ :=
    haveI := isIso_inclusion_of_eq R.zeroScheme₂
    asIso (Scheme.IdealSheafData.inclusion R.zeroScheme₂.le) ≪≫ R.branch₂
  branch₂_toBase := by
    simp only [Iso.trans_hom, asIso_hom, Category.assoc, R.branch₂_toBase]
    rfl
  preimage_eq_union := by
    rw [← R.zeroScheme₁, ← R.zeroScheme₂]
    exact R.preimage_eq_union
  intersection_isIso := R.isIso_inclusion_comp_of_eq R.zeroScheme₁ R.zeroScheme₂
  intersection_zeroSection₁ := R.inclusion_comp_zeroSection₁_of_eq R.zeroScheme₁ R.zeroScheme₂
  intersection_zeroSection₂ := R.inclusion_comp_zeroSection₂_of_eq R.zeroScheme₁ R.zeroScheme₂

end Decomposition

end Stacks.Chow.TensorZeroScheme

end
