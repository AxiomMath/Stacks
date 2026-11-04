module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CanonicalCompactSupportFrobenius
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.DirectImageSystemIdentity
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.UnderivedExtensionByZeroPasting

/-!
# Composites of base change twists

Let `g : Y' ⟶ Y` be a morphism of schemes and let `a : Y' ⟶ Y'`, `b : Y ⟶ Y` with
`a ≫ g = g ≫ b`.  A transformation `ψ : 𝟭 ⟶ b_*` induces the base change twist
`Stacks.EtaleCohomology.etaleModuleBaseChangeTwist Λ g a b w ψ : g⁻¹ ⟶ g⁻¹ ⋙ a_*` of sheaves of
`Λ`-modules; for `g` the projection of the geometric fibre, `a` the base change of the geometric
Frobenius and `ψ` the Frobenius descent isomorphism this is the twist from which the canonical
action `π_X^*` on `RΓ_c(X_k̄, -)` is built.

This file proves that base change twists compose: the twist attached to `a₁ ≫ a₂`, `b₁ ≫ b₂` and
the composite `ψ₂ ≫ (b₂)_* ψ₁` of two transformations is the twist attached to `a₂` followed by
`(a₂)_*` of the twist attached to `a₁`.  Applied to the powers of the Frobenius this identifies
the twist of `π̄ ^ m` with the `m`-fold composite of the twist of `π̄`, as needed in the proof of
[Stacks, Tag 03V0].

## Main results

* `Stacks.EtaleCohomology.unit_comp_map_etaleModuleBaseChangeTwist`: the twist is characterised
  by its adjoint.
* `Stacks.EtaleCohomology.etaleModuleBaseChangeTwist_comp`: the composition law.

## References

* [Stacks Project, Tag 03V0](https://stacks.math.columbia.edu/tag/03V0)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u r

namespace Stacks.EtaleCohomology

section Adjoint

variable (Λ : Type r) [Ring Λ] {Y' Y : Scheme.{u}} (g : Y' ⟶ Y) (a : Y' ⟶ Y') (b : Y ⟶ Y)
  (w : a ≫ g = g ≫ b)
  (ψ : 𝟭 (EtaleModules.{u, r} Λ Y) ⟶ etaleModuleDirectImage.{u, r} Λ b)

/-- **The base change twist is characterised by its adjoint**: the unit of `g⁻¹ ⊣ g_*` followed
by `g_*` of the twist is `ψ`, then `b_*` of the unit, then the identification
`b_* g_* = (a ≫ g)_* = g_* a_*`. -/
lemma unit_comp_map_etaleModuleBaseChangeTwist (L : EtaleModules.{u, r} Λ Y) :
    (etaleModuleInverseImageAdj.{u, r} Λ g).unit.app L ≫
        (etaleModuleDirectImage.{u, r} Λ g).map
          ((etaleModuleBaseChangeTwist.{u, r} Λ g a b w ψ).app L) =
      ψ.app L ≫ (etaleModuleDirectImage.{u, r} Λ b).map
          ((etaleModuleInverseImageAdj.{u, r} Λ g).unit.app L) ≫
        (etaleModuleDirectImageComp.{u, r} Λ g b (a ≫ g) w).hom.app
          ((etaleModuleInverseImage.{u, r} Λ g).obj L) ≫
        (etaleModuleDirectImageComp.{u, r} Λ a g (a ≫ g) rfl).inv.app
          ((etaleModuleInverseImage.{u, r} Λ g).obj L) := by
  rw [etaleModuleBaseChangeTwist_app]
  have h := (etaleModuleInverseImageAdj.{u, r} Λ g).homEquiv_unit (X := L)
    (f := ((etaleModuleInverseImageAdj.{u, r} Λ g).homEquiv _ _).symm
      ((etaleModuleBaseChangeTwistAdj.{u, r} Λ g a b w ψ).app L))
  rw [Equiv.apply_symm_apply] at h
  refine h.symm.trans ?_
  simp [etaleModuleBaseChangeTwistAdj]

end Adjoint

/-! ### Sections of the comparison isomorphisms -/

section Sections

/-- The sections of the inverse of the comparison for a composite direct image: restriction along
the inverse of the base change comparison. -/
lemma smallEtalePushforwardComp'_inv_app_hom_app {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (fg : X ⟶ Z) (hfg : fg = f ≫ g) (A : Type*) [Category* A]
    (F : Sheaf (smallEtaleTopology X) A) (U : (Z.Etale)ᵒᵖ) :
    ((smallEtalePushforwardComp' f g fg hfg A).inv.app F).hom.app U =
      F.obj.map (op ((smallEtaleBaseChangeComp' f g fg hfg).inv.app U.unop)) :=
  Category.comp_id _

/-- A composite of five restriction maps is the restriction along the composite. -/
lemma map_op_comp_five {C A : Type*} [Category* C] [Category* A] (F : Cᵒᵖ ⥤ A)
    {X₀ X₁ X₂ X₃ X₄ X₅ : C} (x₅ : X₄ ⟶ X₅) (x₄ : X₃ ⟶ X₄) (x₃ : X₂ ⟶ X₃) (x₂ : X₁ ⟶ X₂)
    (x₁ : X₀ ⟶ X₁) :
    F.map x₅.op ≫ F.map x₄.op ≫ F.map x₃.op ≫ F.map x₂.op ≫ F.map x₁.op =
      F.map (x₁ ≫ x₂ ≫ x₃ ≫ x₄ ≫ x₅).op := by
  simp only [op_comp, F.map_comp, Category.assoc]

/-- A composite of three restriction maps is the restriction along the composite. -/
lemma map_op_comp_three {C A : Type*} [Category* C] [Category* A] (F : Cᵒᵖ ⥤ A)
    {X₀ X₁ X₂ X₃ : C} (x₃ : X₂ ⟶ X₃) (x₂ : X₁ ⟶ X₂) (x₁ : X₀ ⟶ X₁) :
    F.map x₃.op ≫ F.map x₂.op ≫ F.map x₁.op = F.map (x₁ ≫ x₂ ≫ x₃).op := by
  simp only [op_comp, F.map_comp, Category.assoc]

end Sections

/-! ### The coherence of the comparison isomorphisms -/

section Coherence

/-- Rearranging the projection formulas of the five-fold side of the coherence; stated on
variables. -/
private lemma chainFive {D : Type*} [Category* D]
    {O₀ O₁ O₂ O₃ O₄ O₅ E₁ E₂ U H₂ H₁ H₀ G : D} (x₁ : O₀ ⟶ O₁) (x₂ : O₁ ⟶ O₂) (x₃ : O₂ ⟶ O₃)
    (x₄ : O₃ ⟶ O₄) (x₅ : O₄ ⟶ O₅) (P₁ : O₅ ⟶ E₁) (P₂ : E₁ ⟶ E₂) (P₃ : E₂ ⟶ U) (Q₄ : O₄ ⟶ E₂)
    (A₁ : O₃ ⟶ H₂) (G₁ : H₂ ⟶ E₂) (A₁' : O₂ ⟶ H₁) (B₃ : H₁ ⟶ H₂) (Q₃ : H₁ ⟶ U)
    (A₁'' : O₁ ⟶ H₀) (B₂ : H₀ ⟶ H₁) (A₂ : H₀ ⟶ G) (G₀ : G ⟶ U) (Q₁ : O₀ ⟶ G)
    (F₅ : x₅ ≫ P₁ ≫ P₂ = Q₄) (F₄ : x₄ ≫ Q₄ = A₁ ≫ G₁) (F₃ : x₃ ≫ A₁ = A₁' ≫ B₃)
    (F₃' : B₃ ≫ G₁ ≫ P₃ = Q₃) (F₂ : x₂ ≫ A₁' = A₁'' ≫ B₂) (F₂' : B₂ ≫ Q₃ = A₂ ≫ G₀)
    (F₁ : x₁ ≫ A₁'' ≫ A₂ = Q₁) :
    (x₁ ≫ x₂ ≫ x₃ ≫ x₄ ≫ x₅) ≫ P₁ ≫ P₂ ≫ P₃ = Q₁ ≫ G₀ := by
  simp only [Category.assoc]
  rw [reassoc_of% F₅, reassoc_of% F₄, reassoc_of% F₃, F₃', reassoc_of% F₂, F₂', ← F₁]
  simp only [Category.assoc]

/-- Rearranging the projection formulas of the threefold side of the coherence; stated on
variables. -/
private lemma chainThree {D : Type*} [Category* D]
    {O₀ O₁ O₂ O₃ E₁ E₂ U K G : D} (y₁ : O₀ ⟶ O₁) (y₂ : O₁ ⟶ O₂) (y₃ : O₂ ⟶ O₃)
    (P₁ : O₃ ⟶ E₁) (P₂ : E₁ ⟶ E₂) (P₃ : E₂ ⟶ U) (Gf : O₂ ⟶ K) (B' : K ⟶ E₁) (Qb : K ⟶ U)
    (Qc : O₁ ⟶ U) (Q₁ : O₀ ⟶ G) (G₀ : G ⟶ U)
    (R₃ : y₃ ≫ P₁ = Gf ≫ B') (R₃' : B' ≫ P₂ ≫ P₃ = Qb) (R₂ : y₂ ≫ Gf ≫ Qb = Qc)
    (R₁ : y₁ ≫ Qc = Q₁ ≫ G₀) :
    (y₁ ≫ y₂ ≫ y₃) ≫ P₁ ≫ P₂ ≫ P₃ = Q₁ ≫ G₀ := by
  simp only [Category.assoc]
  rw [reassoc_of% R₃, R₃', R₂, R₁]

variable {Y' Y : Scheme.{u}} (g : Y' ⟶ Y) (a₁ a₂ : Y' ⟶ Y') (b₁ b₂ : Y ⟶ Y)
  (w₁ : a₁ ≫ g = g ≫ b₁) (w₂ : a₂ ≫ g = g ≫ b₂) (w₁₂ : (a₁ ≫ a₂) ≫ g = g ≫ (b₁ ≫ b₂))

/-- **The site-level coherence of the composite of two base change squares.** -/
lemma smallEtaleBaseChange_twistSquare_coherence (U : Y.Etale) :
    (smallEtaleBaseChangeComp' a₁ a₂ (a₁ ≫ a₂) rfl).hom.app ((smallEtaleBaseChange g).obj U) ≫
        (smallEtaleBaseChange a₁).map ((smallEtaleBaseChangeComp' a₂ g (a₂ ≫ g) rfl).inv.app U) ≫
        (smallEtaleBaseChange a₁).map ((smallEtaleBaseChangeComp' g b₂ (a₂ ≫ g) w₂).hom.app U) ≫
        (smallEtaleBaseChangeComp' a₁ g (a₁ ≫ g) rfl).inv.app ((smallEtaleBaseChange b₂).obj U) ≫
        (smallEtaleBaseChangeComp' g b₁ (a₁ ≫ g) w₁).hom.app ((smallEtaleBaseChange b₂).obj U) =
      (smallEtaleBaseChangeComp' (a₁ ≫ a₂) g ((a₁ ≫ a₂) ≫ g) rfl).inv.app U ≫
        (smallEtaleBaseChangeComp' g (b₁ ≫ b₂) ((a₁ ≫ a₂) ≫ g) w₁₂).hom.app U ≫
        (smallEtaleBaseChange g).map
          ((smallEtaleBaseChangeComp' b₁ b₂ (b₁ ≫ b₂) rfl).hom.app U) := by
  refine ExtensionByZeroPasting.smallEtaleBaseChange_baseChange_baseChange_hom_ext g b₁ b₂ ?_
  refine (chainFive _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (smallEtaleBaseChangeComp'_fst_fst g b₁ (a₁ ≫ g) w₁ ((smallEtaleBaseChange b₂).obj U))
    (smallEtaleBaseChangeComp'_inv_fst a₁ g (a₁ ≫ g) rfl ((smallEtaleBaseChange b₂).obj U))
    (smallEtaleBaseChange_map_left_fst a₁ ((smallEtaleBaseChangeComp' g b₂ (a₂ ≫ g) w₂).hom.app U))
    (smallEtaleBaseChangeComp'_fst_fst g b₂ (a₂ ≫ g) w₂ U)
    (smallEtaleBaseChange_map_left_fst a₁ ((smallEtaleBaseChangeComp' a₂ g (a₂ ≫ g) rfl).inv.app U))
    (smallEtaleBaseChangeComp'_inv_fst a₂ g (a₂ ≫ g) rfl U)
    (smallEtaleBaseChangeComp'_fst_fst a₁ a₂ (a₁ ≫ a₂) rfl ((smallEtaleBaseChange g).obj U))).trans
    (chainThree _ _ _ _ _ _ _ _ _ _ _ _
      (smallEtaleBaseChange_map_left_fst g
        ((smallEtaleBaseChangeComp' b₁ b₂ (b₁ ≫ b₂) rfl).hom.app U))
      (smallEtaleBaseChangeComp'_fst_fst b₁ b₂ (b₁ ≫ b₂) rfl U)
      (smallEtaleBaseChangeComp'_fst_fst g (b₁ ≫ b₂) ((a₁ ≫ a₂) ≫ g) w₁₂ U)
      (smallEtaleBaseChangeComp'_inv_fst (a₁ ≫ a₂) g ((a₁ ≫ a₂) ≫ g) rfl U)).symm

/-- The direct image of a morphism of sheaves is the morphism on sections over the base
change. -/
private lemma pushforward_map_hom_app {W Z : Scheme.{u}} (i : W ⟶ Z) (A : Type*) [Category* A]
    {G H : Sheaf (smallEtaleTopology W) A} (ψ : G ⟶ H) (U : (Z.Etale)ᵒᵖ) :
    ((smallEtalePushforward i A).map ψ).hom.app U =
      ψ.hom.app (op ((smallEtaleBaseChange i).obj U.unop)) := rfl

/-- **The coherence of the comparison isomorphisms for a composite of two base change squares**:
the identification `(b₂)_* (b₁)_* g_* ≅ g_* (a₂)_* (a₁)_*` obtained by moving `g_*` past `b₁` and
then past `b₂` is the one obtained by moving it past `b₁ ≫ b₂` at once. -/
theorem smallEtalePushforward_twistSquare_coherence (A : Type*) [Category* A]
    (X : Sheaf (smallEtaleTopology Y') A) :
    (smallEtalePushforward b₂ A).map
        ((smallEtalePushforwardComp' g b₁ (a₁ ≫ g) w₁ A).hom.app X ≫
          (smallEtalePushforwardComp' a₁ g (a₁ ≫ g) rfl A).inv.app X) ≫
      (smallEtalePushforwardComp' g b₂ (a₂ ≫ g) w₂ A).hom.app
        ((smallEtalePushforward a₁ A).obj X) ≫
      (smallEtalePushforwardComp' a₂ g (a₂ ≫ g) rfl A).inv.app
        ((smallEtalePushforward a₁ A).obj X) ≫
      (smallEtalePushforward g A).map
        ((smallEtalePushforwardComp' a₁ a₂ (a₁ ≫ a₂) rfl A).hom.app X) =
    (smallEtalePushforwardComp' b₁ b₂ (b₁ ≫ b₂) rfl A).hom.app ((smallEtalePushforward g A).obj X) ≫
      (smallEtalePushforwardComp' g (b₁ ≫ b₂) ((a₁ ≫ a₂) ≫ g) w₁₂ A).hom.app X ≫
      (smallEtalePushforwardComp' (a₁ ≫ a₂) g ((a₁ ≫ a₂) ≫ g) rfl A).inv.app X := by
  ext U
  simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app, pushforward_map_hom_app,
    smallEtalePushforwardComp'_hom_app_hom_app, smallEtalePushforwardComp'_inv_app_hom_app]
  exact (Category.assoc _ _ _).trans <| (map_op_comp_five X.obj _ _ _ _ _).trans
    ((congrArg (fun φ => X.obj.map φ.op)
      (smallEtaleBaseChange_twistSquare_coherence g a₁ a₂ b₁ b₂ w₁ w₂ w₁₂ U.unop)).trans
    (map_op_comp_three X.obj _ _ _).symm)

end Coherence

/-! ### The composition law -/

/-- The final rearrangement of the composition law; stated on variables. -/
private lemma twist_comp_final {D : Type*} [Category* D] {O₀ O₁ O₂ O₃ O₄ O₅ O₆ O₇ O₈ O₉ O₁₀ O₁₁ : D}
    {ψ₁₂ : O₀ ⟶ O₁} {x : O₁ ⟶ O₂} {hh : O₂ ⟶ O₃} {ii : O₃ ⟶ O₄} {ψ₂ : O₀ ⟶ O₅} {y : O₅ ⟶ O₆}
    {z : O₆ ⟶ O₇} {cb : O₆ ⟶ O₁} {cb' : O₇ ⟶ O₂} {c₁ : O₇ ⟶ O₈} {c₂ : O₈ ⟶ O₉} {c₃ : O₉ ⟶ O₁₀}
    {c₄ : O₁₀ ⟶ O₁₁} {c₅ : O₁₁ ⟶ O₄}
    (hψ : ψ₂ ≫ y ≫ cb = ψ₁₂) (n₃ : z ≫ cb' = cb ≫ x)
    (hco : (c₁ ≫ c₂) ≫ c₃ ≫ c₄ ≫ c₅ = cb' ≫ hh ≫ ii) :
    ψ₁₂ ≫ x ≫ hh ≫ ii = ψ₂ ≫ y ≫ z ≫ c₁ ≫ c₂ ≫ c₃ ≫ c₄ ≫ c₅ := by
  rw [← hψ, Category.assoc, Category.assoc, ← reassoc_of% n₃, ← hco]
  simp only [Category.assoc]

section Composition

variable (Λ : Type r) [Ring Λ] {Y' Y : Scheme.{u}} (g : Y' ⟶ Y) (a₁ a₂ : Y' ⟶ Y') (b₁ b₂ : Y ⟶ Y)
  (w₁ : a₁ ≫ g = g ≫ b₁) (w₂ : a₂ ≫ g = g ≫ b₂) (w₁₂ : (a₁ ≫ a₂) ≫ g = g ≫ (b₁ ≫ b₂))
  (ψ₁ : 𝟭 (EtaleModules.{u, r} Λ Y) ⟶ etaleModuleDirectImage.{u, r} Λ b₁)
  (ψ₂ : 𝟭 (EtaleModules.{u, r} Λ Y) ⟶ etaleModuleDirectImage.{u, r} Λ b₂)
  (ψ₁₂ : 𝟭 (EtaleModules.{u, r} Λ Y) ⟶ etaleModuleDirectImage.{u, r} Λ (b₁ ≫ b₂))

/-- **Base change twists compose.**  If `ψ₁₂` is `ψ₂` followed by `(b₂)_*` of `ψ₁`, then the twist
attached to `a₁ ≫ a₂` and `ψ₁₂` is the twist attached to `a₂` and `ψ₂` followed by `(a₂)_*` of the
twist attached to `a₁` and `ψ₁`. -/
theorem etaleModuleBaseChangeTwist_comp
    (hψ : ∀ L, ψ₂.app L ≫ (etaleModuleDirectImage.{u, r} Λ b₂).map (ψ₁.app L) ≫
      (etaleModuleDirectImageComp.{u, r} Λ b₁ b₂ (b₁ ≫ b₂) rfl).hom.app L = ψ₁₂.app L)
    (L : EtaleModules.{u, r} Λ Y) :
    (etaleModuleBaseChangeTwist.{u, r} Λ g (a₁ ≫ a₂) (b₁ ≫ b₂) w₁₂ ψ₁₂).app L =
      (etaleModuleBaseChangeTwist.{u, r} Λ g a₂ b₂ w₂ ψ₂).app L ≫
        (etaleModuleDirectImage.{u, r} Λ a₂).map
          ((etaleModuleBaseChangeTwist.{u, r} Λ g a₁ b₁ w₁ ψ₁).app L) ≫
        (etaleModuleDirectImageComp.{u, r} Λ a₁ a₂ (a₁ ≫ a₂) rfl).hom.app
          ((etaleModuleInverseImage.{u, r} Λ g).obj L) := by
  apply ((etaleModuleInverseImageAdj.{u, r} Λ g).homEquiv _ _).injective
  simp only [Adjunction.homEquiv_unit]
  rw [unit_comp_map_etaleModuleBaseChangeTwist, Functor.map_comp, Functor.map_comp,
    reassoc_of% (unit_comp_map_etaleModuleBaseChangeTwist Λ g a₂ b₂ w₂ ψ₂ L)]
  have n₁ := (etaleModuleDirectImageComp.{u, r} Λ g b₂ (a₂ ≫ g) w₂).hom.naturality
    ((etaleModuleBaseChangeTwist.{u, r} Λ g a₁ b₁ w₁ ψ₁).app L)
  have n₂ := (etaleModuleDirectImageComp.{u, r} Λ a₂ g (a₂ ≫ g) rfl).inv.naturality
    ((etaleModuleBaseChangeTwist.{u, r} Λ g a₁ b₁ w₁ ψ₁).app L)
  have n₃ := (etaleModuleDirectImageComp.{u, r} Λ b₁ b₂ (b₁ ≫ b₂) rfl).hom.naturality
    ((etaleModuleInverseImageAdj.{u, r} Λ g).unit.app L)
  have hτ₁ := congrArg (etaleModuleDirectImage.{u, r} Λ b₂).map
    (unit_comp_map_etaleModuleBaseChangeTwist Λ g a₁ b₁ w₁ ψ₁ L)
  have hco := smallEtalePushforward_twistSquare_coherence g a₁ a₂ b₁ b₂ w₁ w₂ w₁₂
    (ModuleCat.{max (u + 1) r} Λ) ((etaleModuleInverseImage.{u, r} Λ g).obj L)
  dsimp only [Functor.comp_map] at n₁ n₂ n₃
  rw [← reassoc_of% n₂, ← reassoc_of% n₁, ← Functor.map_comp_assoc, hτ₁]
  simp only [Functor.map_comp, Category.assoc]
  exact twist_comp_final (hψ L) n₃ hco

end Composition

/-! ### Transport of a base change twist along a cartesian square -/

section TransportCoherence

/-- A base change map commutes with the projections. -/
private lemma comb_map {D : Type*} [Category* D] {O O' E E' U : D} {x : O ⟶ O'} {f₁ : O' ⟶ E'}
    {g : O ⟶ E} {y : E ⟶ E'} {R : E' ⟶ U} {Q : E ⟶ U} (hx : x ≫ f₁ = g ≫ y) (hy : y ≫ R = Q) :
    x ≫ f₁ ≫ R = g ≫ Q := by
  rw [reassoc_of% hx, hy]

/-- A comparison morphism commutes with the projections. -/
private lemma comb_hom {D : Type*} [Category* D] {O O' E E' U : D} {x : O ⟶ O'} {a : O' ⟶ E}
    {b : E ⟶ E'} {c : O ⟶ E'} (d : E' ⟶ U) (h : x ≫ a ≫ b = c) : x ≫ a ≫ b ≫ d = c ≫ d := by
  rw [reassoc_of% h]

/-- The inverse of a comparison morphism commutes with the projections. -/
private lemma comb_inv {D : Type*} [Category* D] {O O' E E' U : D} {x : O ⟶ O'} {a : O' ⟶ E'}
    {b : O ⟶ E} {c : E ⟶ E'} (d : E' ⟶ U) (h : x ≫ a = b ≫ c) : x ≫ a ≫ d = b ≫ c ≫ d := by
  rw [reassoc_of% h]

/-- Telescoping projections along a composite of ten morphisms. -/
private lemma telescope₁₀ {D : Type*} [Category* D] {O₀ O₁ O₂ O₃ O₄ O₅ O₆ O₇ O₈ O₉ O₁₀ U : D}
    {x₁ : O₀ ⟶ O₁} {x₂ : O₁ ⟶ O₂} {x₃ : O₂ ⟶ O₃} {x₄ : O₃ ⟶ O₄} {x₅ : O₄ ⟶ O₅} {x₆ : O₅ ⟶ O₆}
    {x₇ : O₆ ⟶ O₇} {x₈ : O₇ ⟶ O₈} {x₉ : O₈ ⟶ O₉} {x₁₀ : O₉ ⟶ O₁₀} {P₀ : O₀ ⟶ U} {P₁ : O₁ ⟶ U}
    {P₂ : O₂ ⟶ U} {P₃ : O₃ ⟶ U} {P₄ : O₄ ⟶ U} {P₅ : O₅ ⟶ U} {P₆ : O₆ ⟶ U} {P₇ : O₇ ⟶ U}
    {P₈ : O₈ ⟶ U} {P₉ : O₉ ⟶ U} {P₁₀ : O₁₀ ⟶ U}
    (h₁₀ : x₁₀ ≫ P₁₀ = P₉) (h₉ : x₉ ≫ P₉ = P₈) (h₈ : x₈ ≫ P₈ = P₇) (h₇ : x₇ ≫ P₇ = P₆)
    (h₆ : x₆ ≫ P₆ = P₅) (h₅ : x₅ ≫ P₅ = P₄) (h₄ : x₄ ≫ P₄ = P₃) (h₃ : x₃ ≫ P₃ = P₂)
    (h₂ : x₂ ≫ P₂ = P₁) (h₁ : x₁ ≫ P₁ = P₀) :
    (x₁ ≫ x₂ ≫ x₃ ≫ x₄ ≫ x₅ ≫ x₆ ≫ x₇ ≫ x₈ ≫ x₉ ≫ x₁₀) ≫ P₁₀ = P₀ := by
  simp only [Category.assoc, h₁₀, h₉, h₈, h₇, h₆, h₅, h₄, h₃, h₂, h₁]

/-- Telescoping projections along a composite of two morphisms. -/
private lemma telescope₂ {D : Type*} [Category* D] {O₀ O₁ O₂ U : D}
    {x₁ : O₀ ⟶ O₁} {x₂ : O₁ ⟶ O₂} {P₀ : O₀ ⟶ U} {P₁ : O₁ ⟶ U} {P₂ : O₂ ⟶ U}
    (h₂ : x₂ ≫ P₂ = P₁) (h₁ : x₁ ≫ P₁ = P₀) : (x₁ ≫ x₂) ≫ P₂ = P₀ := by
  simp only [Category.assoc, h₂, h₁]

variable {Yb Yb' Yl Yl' : Scheme.{u}} (pr : Yb ⟶ Yl) (pr' : Yb' ⟶ Yl') (gl : Yl' ⟶ Yl)
  (e : Yb' ⟶ Yb) (n : Yb' ⟶ Yl) (hn : n = pr' ≫ gl) (hn' : n = e ≫ pr)
  (A : Yb ⟶ Yb) (B : Yl ⟶ Yl) (w : A ≫ pr = pr ≫ B) (A' : Yb' ⟶ Yb') (B' : Yl' ⟶ Yl')
  (w' : A' ≫ pr' = pr' ≫ B') (eA : Yb' ⟶ Yb) (heA : eA = A' ≫ e) (heA' : eA = e ≫ A)
  (m : Yl' ⟶ Yl) (hm : m = B' ≫ gl) (hm' : m = gl ≫ B)

/-- **The site-level coherence of the transport of a base change twist** along the square
`pr' ≫ gl = e ≫ pr`. -/
lemma smallEtaleBaseChange_twistTransport_coherence (U : Yl.Etale) :
    (smallEtaleBaseChangeComp' e A eA heA').inv.app ((smallEtaleBaseChange pr).obj U) ≫
        (smallEtaleBaseChangeComp' A' e eA heA).hom.app ((smallEtaleBaseChange pr).obj U) ≫
        (smallEtaleBaseChange A').map ((smallEtaleBaseChangeComp' e pr n hn').inv.app U) ≫
        (smallEtaleBaseChange A').map ((smallEtaleBaseChangeComp' pr' gl n hn).hom.app U) ≫
        (smallEtaleBaseChangeComp' A' pr' (A' ≫ pr') rfl).inv.app
          ((smallEtaleBaseChange gl).obj U) ≫
        (smallEtaleBaseChangeComp' pr' B' (A' ≫ pr') w').hom.app ((smallEtaleBaseChange gl).obj U) ≫
        (smallEtaleBaseChange pr').map ((smallEtaleBaseChangeComp' B' gl m hm).inv.app U) ≫
        (smallEtaleBaseChange pr').map ((smallEtaleBaseChangeComp' gl B m hm').hom.app U) ≫
        (smallEtaleBaseChangeComp' pr' gl n hn).inv.app ((smallEtaleBaseChange B).obj U) ≫
        (smallEtaleBaseChangeComp' e pr n hn').hom.app ((smallEtaleBaseChange B).obj U) =
      (smallEtaleBaseChange e).map ((smallEtaleBaseChangeComp' A pr (A ≫ pr) rfl).inv.app U) ≫
        (smallEtaleBaseChange e).map ((smallEtaleBaseChangeComp' pr B (A ≫ pr) w).hom.app U) := by
  refine ExtensionByZeroPasting.smallEtaleBaseChange_baseChange_baseChange_hom_ext e pr B ?_
  refine (telescope₁₀
    (comb_hom (pullback.fst U.hom B)
      (smallEtaleBaseChangeComp'_fst_fst e pr n hn' ((smallEtaleBaseChange B).obj U)))
    (comb_inv (pullback.fst U.hom B)
      (smallEtaleBaseChangeComp'_inv_fst pr' gl n hn ((smallEtaleBaseChange B).obj U)))
    (comb_map (smallEtaleBaseChange_map_left_fst pr'
      ((smallEtaleBaseChangeComp' gl B m hm').hom.app U))
      (smallEtaleBaseChangeComp'_fst_fst gl B m hm' U))
    (comb_map (smallEtaleBaseChange_map_left_fst pr'
      ((smallEtaleBaseChangeComp' B' gl m hm).inv.app U))
      (smallEtaleBaseChangeComp'_inv_fst B' gl m hm U))
    (comb_hom (pullback.fst U.hom gl)
      (smallEtaleBaseChangeComp'_fst_fst pr' B' (A' ≫ pr') w' ((smallEtaleBaseChange gl).obj U)))
    (comb_inv (pullback.fst U.hom gl)
      (smallEtaleBaseChangeComp'_inv_fst A' pr' (A' ≫ pr') rfl ((smallEtaleBaseChange gl).obj U)))
    (comb_map (smallEtaleBaseChange_map_left_fst A'
      ((smallEtaleBaseChangeComp' pr' gl n hn).hom.app U))
      (smallEtaleBaseChangeComp'_fst_fst pr' gl n hn U))
    (comb_map (smallEtaleBaseChange_map_left_fst A'
      ((smallEtaleBaseChangeComp' e pr n hn').inv.app U))
      (smallEtaleBaseChangeComp'_inv_fst e pr n hn' U))
    (comb_hom (pullback.fst U.hom pr)
      (smallEtaleBaseChangeComp'_fst_fst A' e eA heA ((smallEtaleBaseChange pr).obj U)))
    (comb_inv (pullback.fst U.hom pr)
      (smallEtaleBaseChangeComp'_inv_fst e A eA heA' ((smallEtaleBaseChange pr).obj U)))).trans
    (telescope₂
      (comb_map (smallEtaleBaseChange_map_left_fst e
        ((smallEtaleBaseChangeComp' pr B (A ≫ pr) w).hom.app U))
        (smallEtaleBaseChangeComp'_fst_fst pr B (A ≫ pr) w U))
      (comb_map (smallEtaleBaseChange_map_left_fst e
        ((smallEtaleBaseChangeComp' A pr (A ≫ pr) rfl).inv.app U))
        (smallEtaleBaseChangeComp'_inv_fst A pr (A ≫ pr) rfl U))).symm

/-- A composite of ten restriction maps is the restriction along the composite. -/
private lemma map_op_comp_ten {C A : Type*} [Category* C] [Category* A] (F : Cᵒᵖ ⥤ A)
    {X₀ X₁ X₂ X₃ X₄ X₅ X₆ X₇ X₈ X₉ X₁₀ : C} (x₁₀ : X₉ ⟶ X₁₀) (x₉ : X₈ ⟶ X₉) (x₈ : X₇ ⟶ X₈)
    (x₇ : X₆ ⟶ X₇) (x₆ : X₅ ⟶ X₆) (x₅ : X₄ ⟶ X₅) (x₄ : X₃ ⟶ X₄) (x₃ : X₂ ⟶ X₃) (x₂ : X₁ ⟶ X₂)
    (x₁ : X₀ ⟶ X₁) :
    (F.map x₁₀.op ≫ F.map x₉.op) ≫ F.map x₈.op ≫ F.map x₇.op ≫ (F.map x₆.op ≫ F.map x₅.op) ≫
        F.map x₄.op ≫ F.map x₃.op ≫ F.map x₂.op ≫ F.map x₁.op =
      F.map (x₁ ≫ x₂ ≫ x₃ ≫ x₄ ≫ x₅ ≫ x₆ ≫ x₇ ≫ x₈ ≫ x₉ ≫ x₁₀).op := by
  simp only [op_comp, F.map_comp, Category.assoc]

/-- A composite of two restriction maps is the restriction along the composite. -/
private lemma map_op_comp_two {C A : Type*} [Category* C] [Category* A] (F : Cᵒᵖ ⥤ A)
    {X₀ X₁ X₂ : C} (x₂ : X₁ ⟶ X₂) (x₁ : X₀ ⟶ X₁) :
    F.map x₂.op ≫ F.map x₁.op = F.map (x₁ ≫ x₂).op :=
  (F.map_comp _ _).symm

/-- **The coherence of the comparison isomorphisms for transporting a base change twist** along
the square `pr' ≫ gl = e ≫ pr`, on sheaves with arbitrary coefficients. -/
theorem smallEtalePushforward_twistTransport_coherence (C : Type*) [Category* C]
    (X : Sheaf (smallEtaleTopology Yb') C) :
    (smallEtalePushforward B C).map
        ((smallEtalePushforwardComp' e pr n hn' C).hom.app X ≫
          (smallEtalePushforwardComp' pr' gl n hn C).inv.app X) ≫
      (smallEtalePushforwardComp' gl B m hm' C).hom.app ((smallEtalePushforward pr' C).obj X) ≫
      (smallEtalePushforwardComp' B' gl m hm C).inv.app ((smallEtalePushforward pr' C).obj X) ≫
      (smallEtalePushforward gl C).map
        ((smallEtalePushforwardComp' pr' B' (A' ≫ pr') w' C).hom.app X ≫
          (smallEtalePushforwardComp' A' pr' (A' ≫ pr') rfl C).inv.app X) ≫
      (smallEtalePushforwardComp' pr' gl n hn C).hom.app ((smallEtalePushforward A' C).obj X) ≫
      (smallEtalePushforwardComp' e pr n hn' C).inv.app ((smallEtalePushforward A' C).obj X) ≫
      (smallEtalePushforward pr C).map
        ((smallEtalePushforwardComp' A' e eA heA C).hom.app X ≫
          (smallEtalePushforwardComp' e A eA heA' C).inv.app X) =
    (smallEtalePushforwardComp' pr B (A ≫ pr) w C).hom.app ((smallEtalePushforward e C).obj X) ≫
      (smallEtalePushforwardComp' A pr (A ≫ pr) rfl C).inv.app
        ((smallEtalePushforward e C).obj X) := by
  ext U
  simp only [Functor.map_comp, ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
    pushforward_map_hom_app, smallEtalePushforwardComp'_hom_app_hom_app,
    smallEtalePushforwardComp'_inv_app_hom_app]
  exact (map_op_comp_ten X.obj _ _ _ _ _ _ _ _ _ _).trans
    ((congrArg (fun φ => X.obj.map φ.op)
      (smallEtaleBaseChange_twistTransport_coherence pr pr' gl e n hn hn' A B w A' B' w' eA heA heA'
        m hm hm' U.unop)).trans
    (map_op_comp_two X.obj _ _).symm)

/-- **The rearrangement behind the transport of a base change twist**, on variables: the adjoint
of the transported twist is computed from the adjoint characterisation of the two twists, the
naturality of the descent isomorphisms against direct images, the naturality of the comparison
isomorphisms, and their coherence. -/
lemma twistTransport_rearrange {D : Type*} [Category* D]
    {L X₁ X₂ X₃ X₄ G₁ G₂ G₃ G₄ G₅ M₁ M₂ M₃ M₄ M₅ M₆ M₇ M₈ M₉ N₁ N₂ N₃ : D}
    (u : L ⟶ X₁) (v : X₁ ⟶ X₂) (t : X₂ ⟶ X₃) (r : X₃ ⟶ X₄) (pτ : X₁ ⟶ M₉) (pAv : M₉ ⟶ X₄)
    (ηg : L ⟶ G₁) (gη : G₁ ⟶ G₂) (c1 : G₂ ⟶ G₃) (c2 : G₃ ⟶ X₂) (gt : G₂ ⟶ G₄) (c1' : G₄ ⟶ G₅)
    (c2' : G₅ ⟶ X₃) (gψ' : G₁ ⟶ M₁) (gBη : M₁ ⟶ M₂) (gc34 : M₂ ⟶ G₄) (ψ : L ⟶ M₃)
    (Bηg : M₃ ⟶ M₄) (c5 : M₄ ⟶ M₅) (c6 : M₅ ⟶ M₁) (Bgη : M₄ ⟶ M₆) (c5' : M₆ ⟶ M₇)
    (c6' : M₇ ⟶ M₂) (Bci : N₂ ⟶ M₆) (c7 : N₂ ⟶ M₈) (c8 : M₈ ⟶ X₄) (Bc1 : M₆ ⟶ N₁)
    (Bc2 : N₁ ⟶ N₂) (Bu : M₃ ⟶ N₃) (Bv : N₃ ⟶ N₂) (c78₀ : N₃ ⟶ M₉)
    (Psi : u ≫ v = ηg ≫ gη ≫ c1 ≫ c2) (N1 : c1 ≫ c2 ≫ t = gt ≫ c1' ≫ c2')
    (Tw' : gη ≫ gt = gψ' ≫ gBη ≫ gc34) (G2' : ηg ≫ gψ' = ψ ≫ Bηg ≫ c5 ≫ c6)
    (N2 : c5 ≫ c6 ≫ gBη = Bgη ≫ c5' ≫ c6')
    (CohT : Bci ≫ c5' ≫ c6' ≫ gc34 ≫ c1' ≫ c2' ≫ r = c7 ≫ c8) (hinv : Bc1 ≫ Bc2 ≫ Bci = 𝟙 _)
    (Tw : u ≫ pτ = ψ ≫ Bu ≫ c78₀) (N3 : c78₀ ≫ pAv = Bv ≫ c7 ≫ c8)
    (BPsi : Bu ≫ Bv = Bηg ≫ Bgη ≫ Bc1 ≫ Bc2) :
    u ≫ v ≫ t ≫ r = u ≫ pτ ≫ pAv := by
  have e₁ : u ≫ v ≫ t ≫ r = ψ ≫ Bηg ≫ Bgη ≫ c5' ≫ c6' ≫ gc34 ≫ c1' ≫ c2' ≫ r := by
    rw [reassoc_of% Psi, reassoc_of% N1, reassoc_of% Tw', reassoc_of% G2', reassoc_of% N2]
  have e₂ : c5' ≫ c6' ≫ gc34 ≫ c1' ≫ c2' ≫ r = Bc1 ≫ Bc2 ≫ c7 ≫ c8 := by
    rw [← CohT, ← Category.assoc Bc2, ← Category.assoc Bc1, hinv, Category.id_comp]
  rw [e₁, e₂, reassoc_of% Tw, N3, ← reassoc_of% BPsi]

end TransportCoherence

end Stacks.EtaleCohomology

end
