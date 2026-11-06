module

public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleQuotientFlatDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.ProjectiveBundleSpaceBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.ProjectiveBundleTwistCharts
import StacksFrontier.AlgebraicGeometry.Spaces.EtaleMorphisms
import StacksFrontier.AlgebraicGeometry.Spaces.EtalePermanence
import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.SurjectivePoints
import StacksFrontier.AlgebraicGeometry.Spaces.SmoothAtlas

/-!
# The morphism `θ : 𝐏(g^*ℰ) ⟶ 𝐏(ℰ)` and comparisons of iterated inverse images

The coherence of the comparisons of iterated inverse images around a commutative square
(`AlgebraicGeometry.Space.pullbackComparison_coherence_of_square`), the morphism
`AlgebraicGeometry.Space.projectiveBundlePullbackMap` over `g`, and the étale surjective chart
`AlgebraicGeometry.Space.presentingFiberChartAtlas` of `𝐏(g^*ℰ)` and its composite with `θ`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

-- `CategoryTheory.catToReflQuiver` offers a second route from `Category` to `Quiver`, by which an
-- arrow `M ⟶ N` of modules written in a statement would not match the arrows of the inverse-image
-- functors without unfolding them.
attribute [-instance] CategoryTheory.catToReflQuiver

/-! ### Comparisons of iterated inverse images -/

section Comparison

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- The inverse image of a morphism along a composite `x = w ≫ p`, through a factorization
`p^*τ ≫ e = q` of its inverse image along `p`. -/
theorem modulePullback_map_eq_of_comp_eq {A P T : AlgebraicSpaces B S hS} (w : T ⟶ P) (p : P ⟶ A)
    (x : T ⟶ A) (hx : w ≫ p = x) {M O : Modules.{u, u} B S hS A.1 A.2} (τ : M ⟶ O)
    {L : Modules.{u, u} B S hS P.1 P.2} (e : (modulePullback B S hS p).obj O ≅ L)
    (q : (modulePullback B S hS p).obj M ⟶ L)
    (hq : (modulePullback B S hS p).map τ ≫ e.hom = q) :
    (modulePullback B S hS x).map τ =
      (QuasiCoherentDescent.pullbackComparison B S hS w p x hx M).hom ≫
        (modulePullback B S hS w).map q ≫
        ((modulePullback B S hS w).mapIso e.symm ≪≫
          (QuasiCoherentDescent.pullbackComparison B S hS w p x hx O).symm).hom := by
  have hq' : (modulePullback B S hS p).map τ = q ≫ e.inv := by
    rw [← hq, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rw [← Category.comp_id ((modulePullback B S hS x).map τ),
    ← (QuasiCoherentDescent.pullbackComparison B S hS w p x hx O).hom_inv_id,
    ← Category.assoc, QuasiCoherentDescent.pullbackComparison_naturality B S hS w p x hx τ, hq']
  simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, Functor.map_comp, Category.assoc]

/-- The inverse image of a morphism along a factorization `w ≫ p = x`, through its inverse image
along `x`. -/
theorem modulePullback_map_modulePullback_map_eq {A P T : AlgebraicSpaces B S hS} (w : T ⟶ P)
    (p : P ⟶ A) (x : T ⟶ A) (hx : w ≫ p = x) {M O : Modules.{u, u} B S hS A.1 A.2}
    (τ : M ⟶ O) :
    (modulePullback B S hS w).map ((modulePullback B S hS p).map τ) =
      (QuasiCoherentDescent.pullbackComparison B S hS w p x hx M).inv ≫
        (modulePullback B S hS x).map τ ≫
        (QuasiCoherentDescent.pullbackComparison B S hS w p x hx O).hom := by
  rw [QuasiCoherentDescent.pullbackComparison_naturality B S hS w p x hx τ, Iso.inv_hom_id_assoc]

/-- The final chase: two quotients written through two factorizations, whose sources are
identified compatibly, are isomorphic as quotients. -/
private theorem quotient_chase_shape {C₀ : Type*} [Category C₀]
    {m₀ x₁ x₂ x₃ n₁ l₁ o₁ n₂ l₂ o₂ k : C₀} (s₁ : m₀ ≅ x₁) (s₂ : x₁ ≅ x₂) (s₃ : x₂ ≅ x₃)
    (s₄ : x₃ ≅ n₁) (q₁ : n₁ ⟶ l₁) (τ₁ : l₁ ≅ o₁) (σ₂ : m₀ ≅ n₂)
    (q₂ : n₂ ⟶ l₂) (τ₂ : l₂ ≅ o₂) (κ₁ : n₁ ≅ k) (κ₂ : n₂ ≅ k) (γ : l₁ ≅ l₂)
    (hγ : q₁ ≫ γ.hom = (κ₁ ≪≫ κ₂.symm).hom ≫ q₂)
    (hcoh : s₁ ≪≫ s₂ ≪≫ s₃ ≪≫ s₄ ≪≫ κ₁ = σ₂ ≪≫ κ₂)
    (χ₁ : m₀ ⟶ o₁) (χ₂ : m₀ ⟶ o₂) (h₁ : χ₁ = (s₁ ≪≫ s₂ ≪≫ s₃ ≪≫ s₄).hom ≫ q₁ ≫ τ₁.hom)
    (h₂ : χ₂ = σ₂.hom ≫ q₂ ≫ τ₂.hom) :
    χ₁ ≫ (τ₁.symm ≪≫ γ ≪≫ τ₂).hom = χ₂ := by
  have hc := congrArg Iso.hom hcoh
  simp only [Iso.trans_hom] at hc
  subst h₁ h₂
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.hom_inv_id_assoc]
  rw [reassoc_of% hγ]
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc]
  rw [reassoc_of% hc, Iso.hom_inv_id_assoc]

/-- The inverse image along `a` of `c ≫ θ^*τ`, through a factorization `a ≫ θ = r₁ ≫ φ` and a
factorization `φ^*τ ≫ e = q`. -/
theorem modulePullback_map_comp_modulePullback_map_eq {P Q Pu T : AlgebraicSpaces B S hS}
    (θ : Q ⟶ P) (a : T ⟶ Q) (r₁ : T ⟶ Pu) (φ : Pu ⟶ P) (ha : a ≫ θ = r₁ ≫ φ)
    {M O : Modules.{u, u} B S hS P.1 P.2} {M₀ : Modules.{u, u} B S hS Q.1 Q.2}
    {M₁ : Modules.{u, u} B S hS Q.1 Q.2} (c₁ : M₀ ≅ M₁) (c₂ : M₁ ≅ (modulePullback B S hS θ).obj M)
    (τ : M ⟶ O)
    {L : Modules.{u, u} B S hS Pu.1 Pu.2} (e : (modulePullback B S hS φ).obj O ≅ L)
    (q : (modulePullback B S hS φ).obj M ⟶ L)
    (hq : (modulePullback B S hS φ).map τ ≫ e.hom = q) :
    (modulePullback B S hS a).map ((c₁ ≪≫ c₂).hom ≫ (modulePullback B S hS θ).map τ) =
      ((modulePullback B S hS a).mapIso c₁ ≪≫ (modulePullback B S hS a).mapIso c₂ ≪≫
          (QuasiCoherentDescent.pullbackComparison B S hS a θ (r₁ ≫ φ) ha M).symm ≪≫
          QuasiCoherentDescent.pullbackComparison B S hS r₁ φ (r₁ ≫ φ) rfl M).hom ≫
        (modulePullback B S hS r₁).map q ≫
        (((modulePullback B S hS r₁).mapIso e.symm ≪≫
          (QuasiCoherentDescent.pullbackComparison B S hS r₁ φ (r₁ ≫ φ) rfl O).symm) ≪≫
          QuasiCoherentDescent.pullbackComparison B S hS a θ (r₁ ≫ φ) ha O).hom := by
  rw [Functor.map_comp, modulePullback_map_modulePullback_map_eq a θ (r₁ ≫ φ) ha τ,
    modulePullback_map_eq_of_comp_eq r₁ φ (r₁ ≫ φ) rfl τ e q hq]
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Functor.map_comp, Category.assoc]

/-- **The coherence of the comparisons of iterated inverse images around the base change of a
projective bundle.**  For a square `θ ≫ π = π' ≫ g` and two factorizations
`a ≫ θ = r₁ ≫ φ` and `r₂ ≫ φ' = a`, the two identifications of `a^*π'^*g^*ℰ` with
`(a ≫ π')^*g^*ℰ`, through `θ^*π^*ℰ` and `φ^*π^*ℰ` on the one hand and through `φ'^*π'^*g^*ℰ` on
the other, agree. -/
theorem pullbackComparison_coherence_of_square
    {X X' P Q Pu Pu' T : AlgebraicSpaces B S hS} (g : X' ⟶ X) (θ : Q ⟶ P) (π : P ⟶ X)
    (π' : Q ⟶ X') (hθ : θ ≫ π = π' ≫ g) (a : T ⟶ Q) (r₁ : T ⟶ Pu) (φ : Pu ⟶ P)
    (ha : a ≫ θ = r₁ ≫ φ) (r₂ : T ⟶ Pu') (φ' : Pu' ⟶ Q) (hb : r₂ ≫ φ' = a)
    (wk₁ : r₁ ≫ (φ ≫ π) = (a ≫ π') ≫ g) (wk₂ : r₂ ≫ (φ' ≫ π') = a ≫ π')
    (E : Modules.{u, u} B S hS X.1 X.2) :
    ((modulePullback B S hS a).map
          (QuasiCoherentDescent.pullbackComparison B S hS π' g (π' ≫ g) rfl E).inv ≫
        (modulePullback B S hS a).map
          (QuasiCoherentDescent.pullbackComparison B S hS θ π (π' ≫ g) hθ E).hom ≫
        (QuasiCoherentDescent.pullbackComparison B S hS a θ (r₁ ≫ φ) ha
          ((modulePullback B S hS π).obj E)).inv ≫
        (QuasiCoherentDescent.pullbackComparison B S hS r₁ φ (r₁ ≫ φ) rfl
          ((modulePullback B S hS π).obj E)).hom) ≫
      (modulePullback B S hS r₁).map
          (QuasiCoherentDescent.pullbackComparison B S hS φ π (φ ≫ π) rfl E).inv ≫
        (QuasiCoherentDescent.pullbackComparison B S hS r₁ (φ ≫ π) ((a ≫ π') ≫ g) wk₁ E).inv ≫
        (QuasiCoherentDescent.pullbackComparison B S hS (a ≫ π') g ((a ≫ π') ≫ g) rfl E).hom =
    (QuasiCoherentDescent.pullbackComparison B S hS r₂ φ' a hb
        ((modulePullback B S hS π').obj ((modulePullback B S hS g).obj E))).hom ≫
      (modulePullback B S hS r₂).map
        (QuasiCoherentDescent.pullbackComparison B S hS φ' π' (φ' ≫ π') rfl
          ((modulePullback B S hS g).obj E)).inv ≫
      (QuasiCoherentDescent.pullbackComparison B S hS r₂ (φ' ≫ π') (a ≫ π') wk₂
        ((modulePullback B S hS g).obj E)).inv := by
  have hst₁ : (r₁ ≫ φ) ≫ π = (a ≫ π') ≫ g := by rw [Category.assoc, wk₁]
  have ht : a ≫ (π' ≫ g) = (a ≫ π') ≫ g := (Category.assoc _ _ _).symm
  have sA := QuasiCoherentDescent.pullbackComparison_trans_inv B S hS r₁ φ π (φ ≫ π) rfl
    (r₁ ≫ φ) rfl ((a ≫ π') ≫ g) wk₁ hst₁ E
  have sB := QuasiCoherentDescent.pullbackComparison_trans_inv B S hS a θ π (π' ≫ g) hθ
    (r₁ ≫ φ) ha ((a ≫ π') ≫ g) ht hst₁ E
  have sC := QuasiCoherentDescent.pullbackComparison_trans_inv B S hS a π' g (π' ≫ g) rfl
    (a ≫ π') rfl ((a ≫ π') ≫ g) ht rfl E
  have sD := QuasiCoherentDescent.pullbackComparison_trans_inv B S hS r₂ φ' π' (φ' ≫ π') rfl
    a hb (a ≫ π') wk₂ rfl ((modulePullback B S hS g).obj E)
  simp only [Category.assoc]
  rw [reassoc_of% sA, Iso.hom_inv_id_assoc, ← reassoc_of% sB, Iso.map_hom_inv_id_assoc,
    reassoc_of% sC, Iso.inv_hom_id, Category.comp_id, sD, Iso.hom_inv_id_assoc]


/-- `AlgebraicGeometry.Space.pullbackComparison_coherence_of_square`, as an equation of
isomorphisms. -/
theorem pullbackComparison_coherence_of_square_iso
    {X X' P Q Pu Pu' T : AlgebraicSpaces B S hS} (g : X' ⟶ X) (θ : Q ⟶ P) (π : P ⟶ X)
    (π' : Q ⟶ X') (hθ : θ ≫ π = π' ≫ g) (a : T ⟶ Q) (r₁ : T ⟶ Pu) (φ : Pu ⟶ P)
    (ha : a ≫ θ = r₁ ≫ φ) (r₂ : T ⟶ Pu') (φ' : Pu' ⟶ Q) (hb : r₂ ≫ φ' = a)
    (wk₁ : r₁ ≫ (φ ≫ π) = (a ≫ π') ≫ g) (wk₂ : r₂ ≫ (φ' ≫ π') = a ≫ π')
    (E : Modules.{u, u} B S hS X.1 X.2) :
    (modulePullback B S hS a).mapIso
        (QuasiCoherentDescent.pullbackComparison B S hS π' g (π' ≫ g) rfl E).symm ≪≫
      (modulePullback B S hS a).mapIso
        (QuasiCoherentDescent.pullbackComparison B S hS θ π (π' ≫ g) hθ E) ≪≫
      (QuasiCoherentDescent.pullbackComparison B S hS a θ (r₁ ≫ φ) ha
        ((modulePullback B S hS π).obj E)).symm ≪≫
      QuasiCoherentDescent.pullbackComparison B S hS r₁ φ (r₁ ≫ φ) rfl
        ((modulePullback B S hS π).obj E) ≪≫
      ((modulePullback B S hS r₁).mapIso
          (QuasiCoherentDescent.pullbackComparison B S hS φ π (φ ≫ π) rfl E).symm ≪≫
        (QuasiCoherentDescent.pullbackComparison B S hS r₁ (φ ≫ π) ((a ≫ π') ≫ g) wk₁ E).symm) ≪≫
      QuasiCoherentDescent.pullbackComparison B S hS (a ≫ π') g ((a ≫ π') ≫ g) rfl E =
    QuasiCoherentDescent.pullbackComparison B S hS r₂ φ' a hb
        ((modulePullback B S hS π').obj ((modulePullback B S hS g).obj E)) ≪≫
      (modulePullback B S hS r₂).mapIso
        (QuasiCoherentDescent.pullbackComparison B S hS φ' π' (φ' ≫ π') rfl
          ((modulePullback B S hS g).obj E)).symm ≪≫
      (QuasiCoherentDescent.pullbackComparison B S hS r₂ (φ' ≫ π') (a ≫ π') wk₂
        ((modulePullback B S hS g).obj E)).symm := by
  refine Iso.ext ?_
  have key := pullbackComparison_coherence_of_square g θ π π' hθ a r₁ φ ha r₂ φ' hb wk₁ wk₂ E
  simp only [Category.assoc] at key
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Category.assoc]
  exact key

/-- **`φ^*τ` followed by `e` is `q`**: the statement that a morphism `τ` becomes `q` after the
inverse image along `φ` and the identification `e` of the targets.  It is a definition so that
two instances of it whose spaces are spelled differently are compared argument by argument,
without unfolding the inverse-image functor. -/
def ModulePullbackFactor {A P : AlgebraicSpaces B S hS} (φ : P ⟶ A)
    {M O : Modules.{u, u} B S hS A.1 A.2} (τ : M ⟶ O) {L : Modules.{u, u} B S hS P.1 P.2}
    (e : (modulePullback B S hS φ).obj O ≅ L) (q : (modulePullback B S hS φ).obj M ⟶ L) : Prop :=
  (modulePullback B S hS φ).map τ ≫ e.hom = q

/-- **`q₁` and `q₂` are isomorphic quotients through `κ` and `γ`**: `q₁ ≫ γ = κ ≫ q₂`.  It is a
definition for the same reason as `AlgebraicGeometry.Space.ModulePullbackFactor`. -/
def QuotientIsoComp {C₀ : Type*} [Category C₀] {N₁ L₁ N₂ L₂ : C₀} (q₁ : N₁ ⟶ L₁) (γ : L₁ ≅ L₂)
    (κ : N₁ ≅ N₂) (q₂ : N₂ ⟶ L₂) : Prop :=
  q₁ ≫ γ.hom = κ.hom ≫ q₂

/-- **Two quotients over a square of inverse images, compared on a chart.**  For a square
`θ ≫ π = π' ≫ g` and factorizations `a ≫ θ = r₁ ≫ φ` and `r₂ ≫ φ' = a`, let `τ` be a quotient of
`π^*ℰ` and `τ'` a quotient of `π'^*g^*ℰ`, written as `q₁` after `φ^*` and as `q₂` after `φ'^*`.
If `r₁^*q₁` and `r₂^*q₂` are isomorphic quotients through the identification of their sources
with `ψ^*g^*ℰ`, then `a^*θ^*τ` and `a^*τ'` are isomorphic quotients of `a^*π'^*g^*ℰ`. -/
theorem exists_iso_modulePullback_comp_of_square
    {X X' P Q Pu Pu' T : AlgebraicSpaces B S hS} (g : X' ⟶ X) (θ : Q ⟶ P) (π : P ⟶ X)
    (π' : Q ⟶ X') (hθ : θ ≫ π = π' ≫ g) (a : T ⟶ Q) (r₁ : T ⟶ Pu) (φ : Pu ⟶ P)
    (ha : a ≫ θ = r₁ ≫ φ) (r₂ : T ⟶ Pu') (φ' : Pu' ⟶ Q) (hb : r₂ ≫ φ' = a)
    (ψ : T ⟶ X') (hψ : a ≫ π' = ψ) (wk₁ : r₁ ≫ (φ ≫ π) = ψ ≫ g) (wk₂ : r₂ ≫ (φ' ≫ π') = ψ)
    (E : Modules.{u, u} B S hS X.1 X.2) {O : Modules.{u, u} B S hS P.1 P.2}
    (τ : (modulePullback B S hS π).obj E ⟶ O) {O' : Modules.{u, u} B S hS Q.1 Q.2}
    (τ' : (modulePullback B S hS π').obj ((modulePullback B S hS g).obj E) ⟶ O')
    {L₁ : Modules.{u, u} B S hS Pu.1 Pu.2} (e₁ : (modulePullback B S hS φ).obj O ≅ L₁)
    (q₁ : (modulePullback B S hS φ).obj ((modulePullback B S hS π).obj E) ⟶ L₁)
    (hq₁ : ModulePullbackFactor φ τ e₁ q₁)
    {L₂ : Modules.{u, u} B S hS Pu'.1 Pu'.2} (e₂ : (modulePullback B S hS φ').obj O' ≅ L₂)
    (q₂ : (modulePullback B S hS φ').obj
      ((modulePullback B S hS π').obj ((modulePullback B S hS g).obj E)) ⟶ L₂)
    (hq₂ : ModulePullbackFactor φ' τ' e₂ q₂)
    (γ : (modulePullback B S hS r₁).obj L₁ ≅ (modulePullback B S hS r₂).obj L₂)
    (hγ : QuotientIsoComp ((modulePullback B S hS r₁).map q₁) γ
      ((((modulePullback B S hS r₁).mapIso
          (QuasiCoherentDescent.pullbackComparison B S hS φ π _ rfl E).symm ≪≫
          (QuasiCoherentDescent.pullbackComparison B S hS r₁ (φ ≫ π) (ψ ≫ g) wk₁ E).symm) ≪≫
          QuasiCoherentDescent.pullbackComparison B S hS ψ g _ rfl E) ≪≫
        ((modulePullback B S hS r₂).mapIso
          (QuasiCoherentDescent.pullbackComparison B S hS φ' π' _ rfl
            ((modulePullback B S hS g).obj E)).symm ≪≫
          (QuasiCoherentDescent.pullbackComparison B S hS r₂ (φ' ≫ π') ψ wk₂
            ((modulePullback B S hS g).obj E)).symm).symm)
      ((modulePullback B S hS r₂).map q₂)) :
    ∃ β : (modulePullback B S hS a).obj ((modulePullback B S hS θ).obj O) ≅
        (modulePullback B S hS a).obj O',
      (modulePullback B S hS a).map
          (((QuasiCoherentDescent.pullbackComparison B S hS π' g _ rfl E).symm ≪≫
            QuasiCoherentDescent.pullbackComparison B S hS θ π _ hθ E).hom ≫
            (modulePullback B S hS θ).map τ) ≫ β.hom =
        (modulePullback B S hS a).map τ' := by
  subst hψ
  exact ⟨_, quotient_chase_shape _ _ _ _ ((modulePullback B S hS r₁).map q₁) _ _
    ((modulePullback B S hS r₂).map q₂)
    ((modulePullback B S hS r₂).mapIso e₂.symm ≪≫
      (QuasiCoherentDescent.pullbackComparison B S hS r₂ φ' a hb O').symm)
    _ _ γ hγ
    (pullbackComparison_coherence_of_square_iso g θ π π' hθ a r₁ φ ha r₂ φ' hb wk₁ wk₂ E) _ _
    (modulePullback_map_comp_modulePullback_map_eq θ a r₁ φ ha _ _ τ e₁ q₁ hq₁)
    (modulePullback_map_eq_of_comp_eq r₂ φ' a hb τ' e₂ q₂ hq₂)⟩

/-- **Two quotients, the first an inverse image `c ≫ θ^*τ`, which are isomorphic after a flat
surjective pullback are isomorphic**:
`AlgebraicGeometry.Space.quotientIsoOfModulePullbackIsFlatOfSurjective` with the epimorphism
`c ≫ θ^*τ` of the inverse image of an epimorphism `τ`. -/
def quotientIsoOfModulePullbackIsFlatOfSurjectiveOfComp {P Q Z' : AlgebraicSpaces B S hS}
    (θ : Q ⟶ P) {N O : Modules.{u, u} B S hS P.1 P.2} (τ : N ⟶ O) (hτ : Epi τ)
    {M F₂ : Modules.{u, u} B S hS Q.1 Q.2} (c : M ≅ (modulePullback B S hS θ).obj N)
    (χ₂ : M ⟶ F₂) (hχ₂ : Epi χ₂) (φ : Z' ⟶ Q) (hφ : IsFlat B S hS φ.hom)
    (hsurj : IsSurjective B S hS φ.hom)
    (h : ∃ β : (modulePullback B S hS φ).obj ((modulePullback B S hS θ).obj O) ≅
        (modulePullback B S hS φ).obj F₂,
      (modulePullback B S hS φ).map (c.hom ≫ (modulePullback B S hS θ).map τ) ≫ β.hom =
        (modulePullback B S hS φ).map χ₂) :
    (modulePullback B S hS θ).obj O ≅ F₂ :=
  quotientIsoOfModulePullbackIsFlatOfSurjective B S hS φ hφ hsurj _
    (by
      have := Functor.preservesEpimorphisms_of_adjunction (modulePullbackAdjunction B S hS θ)
      exact @epi_comp _ _ _ _ _ _ (@IsIso.epi_of_iso _ _ _ _ _ (Iso.isIso_hom _)) _
        (@Functor.map_epi _ _ _ _ _ _ _ _ _ hτ)) χ₂ hχ₂ h

/-- The isomorphism of
`AlgebraicGeometry.Space.quotientIsoOfModulePullbackIsFlatOfSurjectiveOfComp` carries the first
quotient map to the second. -/
theorem comp_quotientIsoOfModulePullbackIsFlatOfSurjectiveOfComp_hom
    {P Q Z' : AlgebraicSpaces B S hS}
    (θ : Q ⟶ P) {N O : Modules.{u, u} B S hS P.1 P.2} (τ : N ⟶ O) (hτ : Epi τ)
    {M F₂ : Modules.{u, u} B S hS Q.1 Q.2} (c : M ≅ (modulePullback B S hS θ).obj N)
    (χ₂ : M ⟶ F₂) (hχ₂ : Epi χ₂) (φ : Z' ⟶ Q) (hφ : IsFlat B S hS φ.hom)
    (hsurj : IsSurjective B S hS φ.hom)
    (h : ∃ β : (modulePullback B S hS φ).obj ((modulePullback B S hS θ).obj O) ≅
        (modulePullback B S hS φ).obj F₂,
      (modulePullback B S hS φ).map (c.hom ≫ (modulePullback B S hS θ).map τ) ≫ β.hom =
        (modulePullback B S hS φ).map χ₂) :
    (c.hom ≫ (modulePullback B S hS θ).map τ) ≫
        (quotientIsoOfModulePullbackIsFlatOfSurjectiveOfComp θ τ hτ c χ₂ hχ₂ φ hφ hsurj h).hom =
      χ₂ :=
  comp_quotientIsoOfModulePullbackIsFlatOfSurjective_hom B S hS φ hφ hsurj _ _ χ₂ hχ₂ h

end Comparison


/-! ### The morphism `θ : 𝐏(g^*ℰ) ⟶ 𝐏(ℰ)` and the chart over `W` -/

section Geometry

set_option synthInstance.maxHeartbeats 400000 in
/-- Pullbacks of presheaves on the big fppf site (instance search times out without this
shortcut). -/
local instance hasPullbacks_presheaf_PullbackMap {B : BigFppfSite.{u}} {S : Scheme.{u}}
    {hS : B.Contains S} : HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) := inferInstance

local instance (priority := high) hasPullback_presheaf_PullbackMap {B : BigFppfSite.{u}}
    {S : Scheme.{u}} {hS : B.Contains S} {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (f : X ⟶ Z) (g : Y ⟶ Z) : HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {X X' : AlgebraicSpaces B S hS}
  (g : X' ⟶ X) (E : Modules.{u, u} B S hS X.1 X.2) [hE : E.IsQuasicoherentOnSite]
  (hfree : SheafOfModules.IsFiniteLocallyFreeOnSite E)

/-- **The morphism `θ : 𝐏(g^*ℰ) ⟶ 𝐏(ℰ)`**: the identification `𝐏(g^*ℰ) ≅ 𝐏(ℰ) ×_X X'`
followed by the first projection. -/
abbrev projectiveBundlePullbackMap :
    projectiveBundle ((modulePullback B S hS g).obj E)
        (isFiniteLocallyFreeOnSite_modulePullback_obj g E hfree) ⟶ projectiveBundle E hfree :=
  (projectiveBundlePullbackIso g E hfree).hom ≫ projectiveBundleFiberProductFst g E hfree

/-- **`θ` lies over `g`**: `θ ≫ π = π' ≫ g`. -/
theorem projectiveBundlePullbackMap_comp_proj :
    projectiveBundlePullbackMap g E hfree ≫ projectiveBundleProj E hfree =
      projectiveBundleProj ((modulePullback B S hS g).obj E)
          (isFiniteLocallyFreeOnSite_modulePullback_obj g E hfree) ≫ g := by
  have h : projectiveBundleFiberProductFst g E hfree ≫ projectiveBundleProj E hfree =
      projectiveBundleFiberProductProj g E hfree ≫ g :=
    ObjectProperty.hom_ext _ pullback.condition
  rw [Category.assoc, h, ← Category.assoc, projectiveBundlePullbackIso_hom_comp_proj]

/-- The chart `𝐏(g^*ℰ|_W) ⟶ 𝐏(g^*ℰ)` over the chart `W = U' ×_X U` of `X'`, through the
presenting chart bundle `𝐏(g^*ℰ|_{U'})`. -/
abbrev presentingFiberChartAtlas :
    representedAlgebraicSpace B S hS
      ((pullbackChartFamily g E hfree).site (presentingFiberChart g)) ⟶
      projectiveBundle ((modulePullback B S hS g).obj E)
        (isFiniteLocallyFreeOnSite_modulePullback_obj g E hfree) :=
  projectiveBundleChartOfHom ((modulePullback B S hS g).obj E)
    (isFiniteLocallyFreeOnSite_modulePullback_obj g E hfree) (presentingFiberChartHom g)

/-- The morphism `𝐏(g^*ℰ|_W) ⟶ 𝐏(ℰ|_U) ⟶ 𝐏(ℰ)`, through the presenting chart bundle of
`𝐏(ℰ)`. -/
abbrev presentingFiberChartBundleAtlas :
    representedAlgebraicSpace B S hS
      ((pullbackChartFamily g E hfree).site (presentingFiberChart g)) ⟶
      projectiveBundle E hfree :=
  representedSpaceMap B S hS (chartBundlePullbackSiteMap g E hfree (presentingFiberChartFstOver g)
    (presentingFiberChartFst_w g)) ≫ projectiveBundleAtlas E hfree

/-- The chart `𝐏(g^*ℰ|_W) ⟶ 𝐏(g^*ℰ)` factors through the bundle glued over the kernel pair of
`W`, by an isomorphism. -/
theorem quotientChart_comp_projectiveBundleOverChartToProjectiveBundle :
    (pullbackChartFamily g E hfree).quotientChart _ _
        (isPullback_chartKernelPairHom (presentingFiberChart g)) ≫
        (projectiveBundleOverChartToProjectiveBundle g E hfree).hom =
      (presentingFiberChartAtlas g E hfree).hom :=
  (pullbackChartFamily g E hfree).quotientChart_comp_quotientDesc _ _ _ _ _ _

/-- **`a ≫ θ = 𝐏(g^*ℰ|_W) ⟶ 𝐏(ℰ|_U) ⟶ 𝐏(ℰ)`.** -/
theorem presentingFiberChartAtlas_comp_projectiveBundlePullbackMap :
    presentingFiberChartAtlas g E hfree ≫ projectiveBundlePullbackMap g E hfree =
      presentingFiberChartBundleAtlas g E hfree := by
  refine ObjectProperty.hom_ext _ ?_
  have h₂ : (pullbackChartFamily g E hfree).quotientChart _ _
        (isPullback_chartKernelPairHom (presentingFiberChart g)) ≫
        (projectiveBundleOverChartToFiberProduct g E hfree).hom =
      presentingFiberChartToFiberProduct g E hfree :=
    (pullbackChartFamily g E hfree).quotientChart_comp_quotientDesc _ _ _ _ _ _
  have h₃ : (projectiveBundleOverChartToProjectiveBundle g E hfree).hom ≫
      (inv (projectiveBundleOverChartToProjectiveBundle g E hfree)).hom = 𝟙 _ :=
    congrArg (fun f => f.hom)
      (IsIso.hom_inv_id (projectiveBundleOverChartToProjectiveBundle g E hfree))
  have e : (presentingFiberChartAtlas g E hfree ≫ projectiveBundlePullbackMap g E hfree).hom =
      (presentingFiberChartAtlas g E hfree).hom ≫
        (inv (projectiveBundleOverChartToProjectiveBundle g E hfree)).hom ≫
          (projectiveBundleOverChartToFiberProduct g E hfree).hom ≫
            pullback.fst (projectiveBundleProj E hfree).hom g.hom := rfl
  rw [e, ← quotientChart_comp_projectiveBundleOverChartToProjectiveBundle, Category.assoc,
    reassoc_of% h₃]
  exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) h₂).trans
    (presentingFiberChartToFiberProduct_fst g E hfree))

/-- **The chart `𝐏(g^*ℰ|_W) ⟶ 𝐏(g^*ℰ)` is étale.** -/
theorem isEtale_presentingFiberChartAtlas :
    IsEtale B S hS (presentingFiberChartAtlas g E hfree).hom := by
  rw [← quotientChart_comp_projectiveBundleOverChartToProjectiveBundle]
  exact isEtale_comp B S hS ((isEtale_iff_presheaf_of_yoneda B S hS _).2
    ((pullbackChartFamily g E hfree).etale_quotientChart _ _ _)) (isEtale_of_isIso B S hS _)

/-- **The chart `𝐏(g^*ℰ|_W) ⟶ 𝐏(g^*ℰ)` is surjective.** -/
theorem surjective_pointsMap_presentingFiberChartAtlas :
    IsSurjective B S hS (presentingFiberChartAtlas g E hfree).hom := by
  rw [← quotientChart_comp_projectiveBundleOverChartToProjectiveBundle, IsSurjective,
    pointsMap_comp]
  refine Function.Surjective.comp (fun y => ⟨pointsMap B S hS _
    (inv (projectiveBundleOverChartToProjectiveBundle g E hfree).hom) y, ?_⟩)
    (surjective_pointsMap_of_presheaf_surjective B S hS _
      ((pullbackChartFamily g E hfree).surjective_quotientChart _ _ _))
  rw [← Function.comp_apply (f := pointsMap B S hS _ _), ← pointsMap_comp, IsIso.inv_hom_id,
    pointsMap_id, id_eq]

/-- The square `𝐏(g^*ℰ|_W) ⟶ W ⟶ X'` equals `𝐏(g^*ℰ|_W) ⟶ 𝐏(g^*ℰ) ⟶ X'`. -/
theorem representedSpaceMap_siteToChart_comp_chartToSpace_presentingFiberChart :
    representedSpaceMap B S hS
      ((pullbackChartFamily g E hfree).siteToChart (presentingFiberChart g)) ≫
        chartToSpace B S hS X' (presentingFiberChart g) =
      presentingFiberChartAtlas g E hfree ≫
        projectiveBundleProj ((modulePullback B S hS g).obj E)
          (isFiniteLocallyFreeOnSite_modulePullback_obj g E hfree) :=
  ObjectProperty.hom_ext _ (isPullback_projectiveBundleChartOfHom ((modulePullback B S hS g).obj E)
    (isFiniteLocallyFreeOnSite_modulePullback_obj g E hfree) (presentingFiberChartHom g)).w.symm

end Geometry

end AlgebraicGeometry.Space

end
