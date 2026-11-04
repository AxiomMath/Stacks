module

public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.QuasiCoherent.CanonicalDatum
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.QuasiCoherent.FpqcChartFullness

/-!
# Descent data for a one-member family from an isomorphism on a chart of the pair

Let `s₀ : Y₀ ⟶ X` be a morphism of algebraic spaces and `M₀` a quasi-coherent module on `Y₀`.
Suppose the fibre product `Y₀ ×_X Y₀` maps to an algebraic space `Y_c` carrying two morphisms
`g₁ g₂ : Y_c ⟶ Y₀` through which the two projections factor, and that
`θ : g₁^* M₀ ≅ g₂^* M₀` is given. Reading `θ` along a morphism `w : T ⟶ Y_c` gives an isomorphism
`(w ≫ g₁)^* M₀ ≅ (w ≫ g₂)^* M₀` (`AlgebraicGeometry.Space.QuasiCoherentDescent.readAlong`), and
reading along `ρ : Y₀ ×_X Y₀ ⟶ Y_c` gives the pairwise isomorphism of a descent datum for the
one-member family `{s₀}` (Stacks 04W3). Its cocycle condition, which Stacks 04W3 states on the
triple fibre product, holds as soon as `θ` satisfies it on an algebraic space `Y₃` with three
morphisms to `Y_c` through which every triple of compatible morphisms factors.

This is the shape of the descent of the polarization in Stacks 0E94, where `Y_c` and `Y₃` are the
base changes along the product points `U₀ ×_T U₀` and `U₀ ×_T U₀ ×_T U₀` of an atlas `U₀` of `T`
and `θ` comes from a functor on the points of `T`.

## Main definitions

* `AlgebraicGeometry.Space.QuasiCoherentDescent.readAlong`: `θ` read along a morphism into `Y_c`.
* `AlgebraicGeometry.Space.QuasiCoherentDescent.unitDescentDatum`: the descent datum.

## Main results

* `AlgebraicGeometry.Space.QuasiCoherentDescent.readAlong_comp`: reading is compatible with
  inverse images.
* `AlgebraicGeometry.Space.QuasiCoherentDescent.readAlong_eq_of_comp_law`: `θ = κ₁⁻¹ ≫ κ₂` read
  along `h` is `μ₁⁻¹ ≫ μ₂` when the `μᵢ` are the composites of the inverse image of `κᵢ` with a
  given `κ : M₃ ≅ h^* M_c`.
* `AlgebraicGeometry.Space.QuasiCoherentDescent.readAlong_cocycle_of_triple`: the cocycle
  condition everywhere from the cocycle condition on `Y₃`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space.QuasiCoherentDescent

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
variable {Yc Y₀ : AlgebraicSpaces B S hS} (g₁ g₂ : Yc ⟶ Y₀) {M : Modules.{u, u} B S hS Y₀.1 Y₀.2}
  (θ : (modulePullback B S hS g₁).obj M ≅ (modulePullback B S hS g₂).obj M)

/-- The inverse of the comparison of an inverse image with an iterated inverse image, written
out. -/
theorem pullbackComparison_inv {A P T : AlgebraicSpaces B S hS} (g : T ⟶ P) (p : P ⟶ A)
    (v : T ⟶ A) (hv : g ≫ p = v) (N : Modules.{u, u} B S hS A.1 A.2) :
    (pullbackComparison B S hS g p v hv N).inv =
      (modulePullbackCompIso B S hS g p).hom.app N ≫
        eqToHom (congrArg (fun q : T ⟶ A => (modulePullback B S hS q).obj N) hv) := by
  subst hv
  rw [pullbackComparison_rfl]
  simp only [Iso.symm_inv, Iso.app_hom, eqToHom_refl, Category.comp_id]

/-- **An isomorphism `θ : g₁^* M ≅ g₂^* M` read along a morphism `w` into its base**, as an
isomorphism of the inverse images of `M` along the two composites. -/
def readAlong {T : AlgebraicSpaces B S hS} (w : T ⟶ Yc) (a b : T ⟶ Y₀) (ha : w ≫ g₁ = a)
    (hb : w ≫ g₂ = b) :
    (modulePullback B S hS a).obj M ≅ (modulePullback B S hS b).obj M :=
  pullbackComparison B S hS w g₁ a ha M ≪≫ (modulePullback B S hS w).mapIso θ ≪≫
    (pullbackComparison B S hS w g₂ b hb M).symm

/-- Reading along equal morphisms gives the same isomorphism. -/
theorem readAlong_congr {T : AlgebraicSpaces B S hS} {w w' : T ⟶ Yc} (h : w = w') (a b : T ⟶ Y₀)
    (ha : w ≫ g₁ = a) (hb : w ≫ g₂ = b) :
    readAlong g₁ g₂ θ w a b ha hb = readAlong g₁ g₂ θ w' a b (h ▸ ha) (h ▸ hb) := by
  subst h
  rfl

/-- **Reading along a composite is the inverse image of the reading**, through the comparisons
of iterated inverse images. -/
theorem readAlong_comp {T T' : AlgebraicSpaces B S hS} (v : T' ⟶ T) (w : T ⟶ Yc) (a b : T ⟶ Y₀)
    (ha : w ≫ g₁ = a) (hb : w ≫ g₂ = b) (a' b' : T' ⟶ Y₀) (ha' : v ≫ a = a') (hb' : v ≫ b = b') :
    pullbackComparison B S hS v a a' ha' M ≪≫
        (modulePullback B S hS v).mapIso (readAlong g₁ g₂ θ w a b ha hb) ≪≫
        (pullbackComparison B S hS v b b' hb' M).symm =
      readAlong g₁ g₂ θ (v ≫ w) a' b' (by rw [Category.assoc, ha, ha'])
        (by rw [Category.assoc, hb, hb']) := by
  subst ha hb ha' hb'
  rw [readAlong, readAlong]
  simp only [Functor.mapIso_trans, Functor.mapIso_symm, mapIso_pullbackComparison B S hS v w,
    Iso.trans_symm, Iso.symm_symm_eq, Iso.trans_assoc]
  rw [pullbackComparison_rfl v (w ≫ g₁) M, pullbackComparison_rfl v (w ≫ g₂) M,
    Iso.symm_symm_eq, Iso.symm_self_id_assoc]
  rw [Iso.subst_trans₂ (modulePullbackCompIso_mapIso B S hS v w θ)]
  simp only [Iso.trans_assoc, Iso.symm_self_id_assoc, Iso.symm_self_id, Iso.trans_refl]
  rfl

/-- **`κ₁⁻¹ ≫ κ₂` read along `h` is `μ₁⁻¹ ≫ μ₂`**, where `μᵢ` is the composite of
`κ : M₃ ≅ h^* M_c`, the inverse image of `κᵢ : M_c ≅ gᵢ^* M` and the comparison of iterated
inverse images. -/
theorem readAlong_eq_of_comp_law {Mc : Modules.{u, u} B S hS Yc.1 Yc.2}
    (κ₁ : Mc ≅ (modulePullback B S hS g₁).obj M) (κ₂ : Mc ≅ (modulePullback B S hS g₂).obj M)
    {Y₃ : AlgebraicSpaces B S hS} {M₃ : Modules.{u, u} B S hS Y₃.1 Y₃.2} (h : Y₃ ⟶ Yc)
    (κ : M₃ ≅ (modulePullback B S hS h).obj Mc) (a b : Y₃ ⟶ Y₀) (ha : h ≫ g₁ = a)
    (hb : h ≫ g₂ = b) (μa : M₃ ≅ (modulePullback B S hS a).obj M)
    (μb : M₃ ≅ (modulePullback B S hS b).obj M)
    (la : κ ≪≫ (modulePullback B S hS h).mapIso κ₁ ≪≫ (pullbackComparison B S hS h g₁ a ha M).symm =
      μa)
    (lb : κ ≪≫ (modulePullback B S hS h).mapIso κ₂ ≪≫ (pullbackComparison B S hS h g₂ b hb M).symm =
      μb) :
    readAlong g₁ g₂ (κ₁.symm ≪≫ κ₂) h a b ha hb = μa.symm ≪≫ μb := by
  subst la lb
  apply Iso.ext
  simp [readAlong]

/-- **The cocycle condition on `Y₃` gives the cocycle condition on every algebraic space mapping
through `Y₃`.** -/
theorem readAlong_cocycle_of_triple {Y₃ : AlgebraicSpaces B S hS} (p₁₂ p₂₃ p₁₃ : Y₃ ⟶ Yc)
    (π₁ π₂ π₃ : Y₃ ⟶ Y₀) (h₁₂ : p₁₂ ≫ g₁ = π₁) (h₁₂' : p₁₂ ≫ g₂ = π₂) (h₂₃ : p₂₃ ≫ g₁ = π₂)
    (h₂₃' : p₂₃ ≫ g₂ = π₃) (h₁₃ : p₁₃ ≫ g₁ = π₁) (h₁₃' : p₁₃ ≫ g₂ = π₃)
    (H : readAlong g₁ g₂ θ p₁₂ π₁ π₂ h₁₂ h₁₂' ≪≫ readAlong g₁ g₂ θ p₂₃ π₂ π₃ h₂₃ h₂₃' =
      readAlong g₁ g₂ θ p₁₃ π₁ π₃ h₁₃ h₁₃')
    {T : AlgebraicSpaces B S hS} (t : T ⟶ Y₃) (w₁₂ w₂₃ w₁₃ : T ⟶ Yc) (v₁ v₂ v₃ : T ⟶ Y₀)
    (hw₁₂ : t ≫ p₁₂ = w₁₂) (hw₂₃ : t ≫ p₂₃ = w₂₃) (hw₁₃ : t ≫ p₁₃ = w₁₃)
    (hv₁ : t ≫ π₁ = v₁) (hv₂ : t ≫ π₂ = v₂) (hv₃ : t ≫ π₃ = v₃)
    (e₁₂ : w₁₂ ≫ g₁ = v₁) (e₁₂' : w₁₂ ≫ g₂ = v₂) (e₂₃ : w₂₃ ≫ g₁ = v₂) (e₂₃' : w₂₃ ≫ g₂ = v₃)
    (e₁₃ : w₁₃ ≫ g₁ = v₁) (e₁₃' : w₁₃ ≫ g₂ = v₃) :
    readAlong g₁ g₂ θ w₁₂ v₁ v₂ e₁₂ e₁₂' ≪≫ readAlong g₁ g₂ θ w₂₃ v₂ v₃ e₂₃ e₂₃' =
      readAlong g₁ g₂ θ w₁₃ v₁ v₃ e₁₃ e₁₃' := by
  subst hw₁₂ hw₂₃ hw₁₃
  rw [← readAlong_comp g₁ g₂ θ t p₁₂ π₁ π₂ h₁₂ h₁₂' v₁ v₂ hv₁ hv₂,
    ← readAlong_comp g₁ g₂ θ t p₂₃ π₂ π₃ h₂₃ h₂₃' v₂ v₃ hv₂ hv₃,
    ← readAlong_comp g₁ g₂ θ t p₁₃ π₁ π₃ h₁₃ h₁₃' v₁ v₃ hv₁ hv₃, ← H]
  simp only [Functor.mapIso_trans, Iso.trans_assoc, Iso.symm_self_id_assoc]


/-- **A reading of `M₀ ≅ s₀^* L` through two morphisms `A`, `B'` to `Y₀` does not depend on the
morphism**, as soon as the canonical comparison of the two inverse images of `L` is, through
`τ`, the comparison `fα⁻¹ ≫ fβ` of the two inverse images of `M₀`. -/
theorem reading_eq_of_compat {X Yx : AlgebraicSpaces B S hS} {s₀ : Y₀ ⟶ X}
    {L : Modules.{u, u} B S hS X.1 X.2} (τ : M ≅ (modulePullback B S hS s₀).obj L)
    {Mx : Modules.{u, u} B S hS Yx.1 Yx.2} (A B' : Yx ⟶ Y₀) (sx : Yx ⟶ X) (hA : A ≫ s₀ = sx)
    (hB : B' ≫ s₀ = sx) (fα : Mx ≅ (modulePullback B S hS A).obj M)
    (fβ : Mx ≅ (modulePullback B S hS B').obj M)
    (K : (modulePullback B S hS A).mapIso τ ≪≫ canonicalComparison A B' s₀ s₀ (hA.trans hB.symm) L =
      (fα.symm ≪≫ fβ) ≪≫ (modulePullback B S hS B').mapIso τ) :
    fα ≪≫ (modulePullback B S hS A).mapIso τ ≪≫ (pullbackComparison B S hS A s₀ sx hA L).symm =
      fβ ≪≫ (modulePullback B S hS B').mapIso τ ≪≫
        (pullbackComparison B S hS B' s₀ sx hB L).symm := by
  rw [canonicalComparison_eq_pullbackComparison B S hS A B' s₀ s₀ _ sx hA hB L] at K
  have K' := congrArg (fun e => fα ≪≫ e ≪≫ (pullbackComparison B S hS B' s₀ sx hB L).symm) K
  simp only [Iso.trans_assoc, Iso.self_symm_id, Iso.trans_refl, Iso.self_symm_id_assoc] at K'
  exact K'


/-- **The descent datum for the one-member family `{s₀}` whose pairwise isomorphism is `θ` read
along `ρ : Y₀ ×_X Y₀ ⟶ Y_c`** (Stacks 04W3), given the cocycle condition for the readings of
`θ` on every algebraic space. -/
def unitDescentDatum {X : AlgebraicSpaces B S hS} (s₀ : Y₀ ⟶ X) (hM : M.IsQuasicoherentOnSite)
    (ρ : pair B S hS (fun _ : Unit => Y₀) (fun _ => s₀) () () ⟶ Yc)
    (hρ₁ : ρ ≫ g₁ = pairFst B S hS (fun _ : Unit => Y₀) (fun _ => s₀) () ())
    (hρ₂ : ρ ≫ g₂ = pairSnd B S hS (fun _ : Unit => Y₀) (fun _ => s₀) () ())
    (hcoc : ∀ (T : AlgebraicSpaces B S hS) (w₁₂ w₂₃ w₁₃ : T ⟶ Yc) (v₁ v₂ v₃ : T ⟶ Y₀)
      (e₁₂ : w₁₂ ≫ g₁ = v₁) (e₁₂' : w₁₂ ≫ g₂ = v₂) (e₂₃ : w₂₃ ≫ g₁ = v₂)
      (e₂₃' : w₂₃ ≫ g₂ = v₃) (e₁₃ : w₁₃ ≫ g₁ = v₁) (e₁₃' : w₁₃ ≫ g₂ = v₃),
      readAlong g₁ g₂ θ w₁₂ v₁ v₂ e₁₂ e₁₂' ≪≫ readAlong g₁ g₂ θ w₂₃ v₂ v₃ e₂₃ e₂₃' =
        readAlong g₁ g₂ θ w₁₃ v₁ v₃ e₁₃ e₁₃') :
    DescentDatum B S hS (fun _ : Unit => Y₀) (fun _ => s₀) where
  F _ := M
  quasicoherent _ := hM
  transition _ _ := readAlong g₁ g₂ θ ρ _ _ hρ₁ hρ₂
  cocycle _ _ _ T vi vj vk vij vjk vik hij₀ hij₁ hjk₀ hjk₁ hik₀ hik₁ := by
    simp only [transitionOn]
    rw [readAlong_comp g₁ g₂ θ vij ρ _ _ hρ₁ hρ₂ vi vj hij₀ hij₁,
      readAlong_comp g₁ g₂ θ vjk ρ _ _ hρ₁ hρ₂ vj vk hjk₀ hjk₁,
      readAlong_comp g₁ g₂ θ vik ρ _ _ hρ₁ hρ₂ vi vk hik₀ hik₁]
    exact hcoc T _ _ _ vi vj vk _ _ _ _ _ _

end AlgebraicGeometry.Space.QuasiCoherentDescent

end
