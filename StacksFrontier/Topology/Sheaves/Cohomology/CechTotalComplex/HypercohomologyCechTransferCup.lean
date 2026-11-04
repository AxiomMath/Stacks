module

public import StacksFrontier.Topology.Sheaves.Cohomology.CechTotalComplex.HypercohomologyCechTransfer

/-!
# Transfer of cup products between shifted sheaves with the same Čech cochains

Let `X` be a topological space with sheaves `𝒪₁`, `𝒪₂` of commutative rings, and let
`β₁ : ℱ₁ × 𝒢₁ ⟶ ℋ₁` and `β₂ : ℱ₂ × 𝒢₂ ⟶ ℋ₂` be bilinear maps of sheaves of `𝒪₁`- and
`𝒪₂`-modules. Let `e_ℱ`, `e_𝒢`, `e_ℋ` be morphisms of the underlying presheaves of abelian groups
compatible with the bilinear maps: `e_ℋ(β₁(x, y)) = β₂(e_ℱ(x), e_𝒢(y))` on local sections. Then the
transfer maps `Stacks.Cech.Hypercohomology.cechTransfer` along the `e`'s carry the cup product
of Cohomology, Section 01FP along `β₁` of `ℱ₁[-a₁]` and `𝒢₁[-b₁]` to the cup product along `β₂`
of `ℱ₂[-a₂]` and `𝒢₂[-b₂]`, up to the sign `(-1)^{(a₁ + a₂)q}`. Both cup products are computed by
the Alexander–Whitney product of representing Čech cocycles
(`Stacks.Cech.Hypercohomology.cup_cechCocycleClassAt`), and pushing along the `e`'s commutes with
it.

## Main results

* `Stacks.Cech.Hypercohomology.push_cechAWCochain`: pushing commutes with the Alexander–Whitney
  product of explicit Čech cochains.
* `Stacks.Cech.Hypercohomology.cechTransfer_cup`: **the transfer maps carry cup products to cup
  products.**

## References

* [Stacks Project, Section 01FP](https://stacks.math.columbia.edu/tag/01FP)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.SheafOfModules.Tensor (ringSheaf)
open Stacks.Cohomology.CechSheaf (abSections SectionRing)
open Stacks.Cohomology.CechOne (push push_cechD cechD_push push_refinementMap)
open CechCochains (Cochain cechD refinementMap)

universe u

namespace Stacks.Cech.Hypercohomology

variable {X : TopCat.{u}} {O₁ O₂ : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u}}
  {F₁ G₁ H₁ : SheafOfModules.{u} (ringSheaf O₁)} {F₂ G₂ H₂ : SheafOfModules.{u} (ringSheaf O₂)}
  (eF : abSections F₁ ⟶ abSections F₂) (eG : abSections G₁ ⟶ abSections G₂)
  (eH : abSections H₁ ⟶ abSections H₂)
  (β₁ : Stacks.BilinearMap F₁.val G₁.val H₁.val) (β₂ : Stacks.BilinearMap F₂.val G₂.val H₂.val)
  (hβ : ∀ (V : Opens X) (x : F₁.val.obj (op V)) (y : G₁.val.obj (op V)),
    eH.app (op V) (β₁.app (op V) x y) = β₂.app (op V) (eF.app (op V) x) (eG.app (op V) y))

include hβ in
/-- **Pushing along morphisms compatible with the bilinear maps commutes with the
Alexander–Whitney product** of explicit Čech cochains. -/
theorem push_cechAWCochain {I : Type u} (U : I → Opens X) {r s : ℕ}
    (c : Cochain U (abSections F₁) r) (d : Cochain U (abSections G₁) s) :
    push U eH (r + s) (cechAWCochain U β₁ c d) =
      cechAWCochain U β₂ (push U eF r c) (push U eG s d) := by
  funext x
  exact (hβ _ _ _).trans <| congrArg₂ (fun (a : F₂.val.obj (op (CechCochains.inter U x)))
      (b : G₂.val.obj (op (CechCochains.inter U x))) => β₂.app (op (CechCochains.inter U x)) a b)
    (NatTrans.naturality_apply eF _ _) (NatTrans.naturality_apply eG _ _)

include hβ in
/-- **The transfer maps carry cup products to cup products.** For `x ∈ H^{p+a₁}(X, ℱ₁[-a₁])` and
`y ∈ H^{q+b₁}(X, 𝒢₁[-b₁])`, the transfer along `e_ℋ` of the cup product along `β₁` is
`(-1)^{a₁q}(-1)^{a₂q}` times the cup product along `β₂` of the transfers along `e_ℱ` and `e_𝒢`. -/
theorem cechTransfer_cup (a₁ b₁ a₂ b₂ : ℤ) (hF₁ : CechComputes O₁ (singlePlus O₁ F₁ a₁))
    (hG₁ : CechComputes O₁ (singlePlus O₁ G₁ b₁))
    (hH₁ : CechComputes O₁ (singlePlus O₁ H₁ (a₁ + b₁)))
    (hF₂ : CechComputes O₂ (singlePlus O₂ F₂ a₂)) (hG₂ : CechComputes O₂ (singlePlus O₂ G₂ b₂))
    (p q : ℕ) (x : hypercohomology O₁ (singlePlus O₁ F₁ a₁) ((p : ℤ) + a₁))
    (y : hypercohomology O₁ (singlePlus O₁ G₁ b₁) ((q : ℤ) + b₁)) :
    cechTransfer eH (a₁ + b₁) (a₂ + b₂) hH₁ (p + q)
        (cup O₁ hF₁ hG₁ (singlePairingAt a₁ b₁ (bilinearPairing β₁)) ((p : ℤ) + a₁)
          ((q : ℤ) + b₁) (((p + q : ℕ) : ℤ) + (a₁ + b₁)) (by push_cast; ring) x y) =
      ((a₁ * q).negOnePow : ℤ) • ((a₂ * q).negOnePow : ℤ) •
        cup O₂ hF₂ hG₂ (singlePairingAt a₂ b₂ (bilinearPairing β₂)) ((p : ℤ) + a₂)
          ((q : ℤ) + b₂) (((p + q : ℕ) : ℤ) + (a₂ + b₂)) (by push_cast; ring)
          (cechTransfer eF a₁ a₂ hF₁ p x) (cechTransfer eG b₁ b₂ hG₁ q y) := by
  obtain ⟨J, V, hV, c, hc, rfl⟩ := exists_cechCocycleClassAt_eq _ a₁ hF₁ p x
  obtain ⟨J', V', hV', d, hd, rfl⟩ := exists_cechCocycleClassAt_eq _ b₁ hG₁ q y
  let W : J × J' → Opens X := fun ij => V ij.1 ⊓ V' ij.2
  have hW : ⊤ = ⨆ ij, W ij := iSup_inf_eq_top V hV V' hV'
  rw [← cechCocycleClassAt_refinement V hV _ a₁ W hW Prod.fst (fun _ => inf_le_left) c hc,
    ← cechCocycleClassAt_refinement V' hV' _ b₁ W hW Prod.snd (fun _ => inf_le_right) d hd,
    cup_cechCocycleClassAt W hW a₁ b₁ hF₁ hG₁ β₁, map_zsmul, cechTransfer_cechCocycleClassAt,
    cechTransfer_cechCocycleClassAt, cechTransfer_cechCocycleClassAt,
    cup_cechCocycleClassAt W hW a₂ b₂ hF₂ hG₂ β₂, smul_smul, smul_smul, mul_assoc,
    ← Units.val_mul, Int.units_mul_self, Units.val_one, mul_one]
  exact congrArg _ (cechCocycleClassAt_congr W hW H₂ (a₂ + b₂)
    (push_cechAWCochain eF eG eH β₁ β₂ hβ W _ _) _ _)

/-! ### Pairings into an arbitrary degree -/

section To

variable {O : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u}}
  {F G H : SheafOfModules.{u} (ringSheaf O)}

variable (O) in
/-- **The pairing of sheaves placed in degrees `a`, `b` and `c = a + b` attached to a pairing on
sections**, for a target degree given by an equation. -/
def singlePairingAtTo (a b c : ℤ) (h : a + b = c)
    (μ₀ : Stacks.Cech.LinearCupProduct.Pairing (SectionRing (ringSheaf O) ⊤) (sectionsP O F)
      (sectionsP O G) (sectionsP O H)) :
    Pairing O (singlePlus O F a) (singlePlus O G b) (singlePlus O H c) := by
  subst h
  exact singlePairingAt a b μ₀

/-- For the target degree `a + b`, `singlePairingAtTo` is `singlePairingAt`. -/
theorem singlePairingAtTo_rfl (a b : ℤ)
    (μ₀ : Stacks.Cech.LinearCupProduct.Pairing (SectionRing (ringSheaf O) ⊤) (sectionsP O F)
      (sectionsP O G) (sectionsP O H)) :
    singlePairingAtTo O a b (a + b) rfl μ₀ = singlePairingAt a b μ₀ :=
  rfl

/-- **The cup product of the classes of two explicit Čech cocycles** along the pairing attached
to a bilinear map, into a target degree given by an equation. -/
theorem cup_cechCocycleClassAtTo {I : Type u} (U : I → Opens X) (hU : ⊤ = ⨆ i, U i)
    (a b c : ℤ) (h : a + b = c) (hF : CechComputes O (singlePlus O F a))
    (hG : CechComputes O (singlePlus O G b)) (β : Stacks.BilinearMap F.val G.val H.val)
    {r s : ℕ} (x : Cochain U (abSections F) r) (hx : cechD U (abSections F) r x = 0)
    (y : Cochain U (abSections G) s) (hy : cechD U (abSections G) s y = 0) :
    cup O hF hG (singlePairingAtTo O a b c h (bilinearPairing β)) ((r : ℤ) + a) ((s : ℤ) + b)
        (((r + s : ℕ) : ℤ) + c) (by push_cast; omega) (cechCocycleClassAt U hU F a x hx)
        (cechCocycleClassAt U hU G b y hy) =
      ((a * s).negOnePow : ℤ) • cechCocycleClassAt U hU H c (cechAWCochain U β x y)
        (cechD_cechAWCochain U hU β x y hx hy) := by
  subst h
  exact cup_cechCocycleClassAt U hU a b hF hG β x hx y hy

include hβ in
/-- **The transfer maps carry cup products to cup products**, for pairings into target degrees
given by equations. -/
theorem cechTransfer_cupTo (a₁ b₁ c₁ a₂ b₂ c₂ : ℤ) (h₁ : a₁ + b₁ = c₁) (h₂ : a₂ + b₂ = c₂)
    (hF₁ : CechComputes O₁ (singlePlus O₁ F₁ a₁)) (hG₁ : CechComputes O₁ (singlePlus O₁ G₁ b₁))
    (hH₁ : CechComputes O₁ (singlePlus O₁ H₁ c₁))
    (hF₂ : CechComputes O₂ (singlePlus O₂ F₂ a₂)) (hG₂ : CechComputes O₂ (singlePlus O₂ G₂ b₂))
    (p q : ℕ) (x : hypercohomology O₁ (singlePlus O₁ F₁ a₁) ((p : ℤ) + a₁))
    (y : hypercohomology O₁ (singlePlus O₁ G₁ b₁) ((q : ℤ) + b₁)) :
    cechTransfer eH c₁ c₂ hH₁ (p + q)
        (cup O₁ hF₁ hG₁ (singlePairingAtTo O₁ a₁ b₁ c₁ h₁ (bilinearPairing β₁)) ((p : ℤ) + a₁)
          ((q : ℤ) + b₁) (((p + q : ℕ) : ℤ) + c₁) (by push_cast; omega) x y) =
      ((a₁ * q).negOnePow : ℤ) • ((a₂ * q).negOnePow : ℤ) •
        cup O₂ hF₂ hG₂ (singlePairingAtTo O₂ a₂ b₂ c₂ h₂ (bilinearPairing β₂)) ((p : ℤ) + a₂)
          ((q : ℤ) + b₂) (((p + q : ℕ) : ℤ) + c₂) (by push_cast; omega)
          (cechTransfer eF a₁ a₂ hF₁ p x) (cechTransfer eG b₁ b₂ hG₁ q y) := by
  subst h₁ h₂
  exact cechTransfer_cup eF eG eH β₁ β₂ hβ a₁ b₁ a₂ b₂ hF₁ hG₁ hH₁ hF₂ hG₂ p q x y

end To

end Stacks.Cech.Hypercohomology

end
