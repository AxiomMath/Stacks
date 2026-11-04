module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.BilinearMapRestrictScalars
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.CoextendScalarsKInjective
public import StacksFrontier.Topology.Sheaves.Cohomology.CechToCohomology.BoundaryCocycle
public import StacksFrontier.Topology.Sheaves.Cohomology.CechTotalComplex.HypercohomologyShiftedSingleCochains

/-!
# Shifted sheaves with the same Čech cochains

Let `X` be a topological space with sheaves `𝒪₁` and `𝒪₂` of commutative rings, `ℱ₁` a sheaf of
`𝒪₁`-modules, `ℱ₂` a sheaf of `𝒪₂`-modules, and `e` a morphism of their underlying presheaves of
abelian groups. When Čech cohomology computes the hypercohomology of `ℱ₁[-a₁]`, every class of
`H^{p+a₁}(X, ℱ₁[-a₁])` is the class of an explicit Čech `p`-cocycle `c`, and the class of `e(c)` in
`H^{p+a₂}(X, ℱ₂[-a₂])` depends only on the class of `c`: this is a homomorphism, natural in
morphisms compatible with `e`. When `e` is an isomorphism and Čech cohomology also computes the
hypercohomology of `ℱ₂[-a₂]`, it is an isomorphism.

The main instance is restriction of scalars along a morphism `𝒪' ⟶ 𝒪` of sheaves of rings, which
does not change the underlying abelian sheaf: it identifies `H^{p+a}(X, ℱ[-a])`, computed in
sheaves of `𝒪'`-modules, with `H^p(X, ℱ)`, computed in sheaves of `𝒪`-modules.

## Main definitions

* `Stacks.Cech.Hypercohomology.cechTransfer`: the homomorphism induced by `e`.
* `Stacks.Cech.Hypercohomology.cechTransferEquiv`: the isomorphism induced by an isomorphism `e`.
* `Stacks.Cech.Hypercohomology.restrictScalarsCechEquiv`: the identification
  `H^{p+a}(X, ℱ[-a]) ≅ H^p(X, ℱ)` across restriction of scalars.

## Main results

* `Stacks.Cech.Hypercohomology.cechTransfer_cechCocycleClassAt`: the value on the class of an
  explicit Čech cocycle.
* `Stacks.Cech.Hypercohomology.cechTransfer_hypercohomologyMap`: naturality.
* `Stacks.Cech.Hypercohomology.restrictScalarsCechEquiv_cechCocycleClassAt`,
  `Stacks.Cech.Hypercohomology.restrictScalarsCechEquiv_hypercohomologyMap`: the same for the
  identification across restriction of scalars.
* `Stacks.Cech.Hypercohomology.restrictScalarsCechEquiv_sectionClass`: in degree zero it carries
  the class of a global section to the class of the same section.
* `Stacks.Cech.Hypercohomology.restrictScalarsCechEquiv_cup`: the identification across
  restriction of scalars carries cup products to cup products, up to the sign `(-1)^{aq}`.

## References

* [Stacks Project, Tag 01FJ](https://stacks.math.columbia.edu/tag/01FJ)
* [Stacks Project, Section 01FP](https://stacks.math.columbia.edu/tag/01FP)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.SheafOfModules.Tensor (ringSheaf)
open Stacks.Cohomology.CechSheaf (abSections)
open Stacks.Cohomology.CechOne (push push_cechD cechD_push push_refinementMap)
open CechCochains (Cochain cechD refinementMap)

universe u

namespace Stacks.Cech.Hypercohomology

variable {X : TopCat.{u}} {O₁ O₂ : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u}}
  {F₁ : SheafOfModules.{u} (ringSheaf O₁)} {F₂ : SheafOfModules.{u} (ringSheaf O₂)}
  (e : abSections F₁ ⟶ abSections F₂) (a₁ a₂ : ℤ)

section Cocycles

variable {O : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u}}
  {F : SheafOfModules.{u} (ringSheaf O)} {I : Type u} (U : I → Opens X) (hU : ⊤ = ⨆ i, U i)
  (a : ℤ)

/-- The class of the zero cocycle is zero. -/
theorem cechCocycleClassAt_eq_zero_of_eq_zero {p : ℕ} (c : Cochain U (abSections F) p)
    (hc : cechD U (abSections F) p c = 0) (h : c = 0) :
    cechCocycleClassAt U hU F a c hc = 0 := by
  have h2 := cechCocycleClassAt_add U hU F a c c hc hc
  rw [cechCocycleClassAt_congr U hU F a (show c + c = c by rw [h, add_zero]) _ hc] at h2
  exact left_eq_add.1 h2

end Cocycles

variable {I : Type u} (U : I → Opens X) (hU : ⊤ = ⨆ i, U i)

/-- Refining a Čech cocycle gives a Čech cocycle. -/
private theorem cechD_refinementMap_eq_zero {J : Type u} (V : J → Opens X) (r : J → I)
    (hr : ∀ j, V j ≤ U (r j)) {ℱ : TopCat.Presheaf AddCommGrpCat.{u} X} {p : ℕ}
    {c : Cochain U ℱ p} (hc : cechD U ℱ p c = 0) :
    cechD V ℱ p (refinementMap U V r hr ℱ p c) = 0 := by
  rw [← CechCochains.refinementMap_cechD, hc, map_zero]

/-- Pushing a cocycle along `e` and refining the covering give the same class. -/
theorem cechCocycleClassAt_push_refinementMap {J : Type u} (V : J → Opens X)
    (hV : ⊤ = ⨆ j, V j) (r : J → I) (hr : ∀ j, V j ≤ U (r j)) {p : ℕ}
    (c : Cochain U (abSections F₁) p) (hc : cechD U (abSections F₁) p c = 0) :
    cechCocycleClassAt V hV F₂ a₂ (push V e p (refinementMap U V r hr (abSections F₁) p c))
        (cechD_push V e p _ (by rw [← CechCochains.refinementMap_cechD, hc, map_zero])) =
      cechCocycleClassAt U hU F₂ a₂ (push U e p c) (cechD_push U e p c hc) := by
  rw [cechCocycleClassAt_congr V hV F₂ a₂ (push_refinementMap U V r hr e p c) _
    (cechD_refinementMap_eq_zero U V r hr (cechD_push U e p c hc))]
  exact cechCocycleClassAt_refinement U hU F₂ a₂ V hV r hr _ _

/-- **A cocycle with vanishing class still has vanishing class after pushing along `e`**, when
Čech cohomology computes the hypercohomology of `ℱ₁[-a₁]`. -/
theorem cechCocycleClassAt_push_eq_zero (h₁ : CechComputes O₁ (singlePlus O₁ F₁ a₁)) {p : ℕ}
    (c : Cochain U (abSections F₁) p) (hc : cechD U (abSections F₁) p c = 0)
    (h0 : cechCocycleClassAt U hU F₁ a₁ c hc = 0) :
    cechCocycleClassAt U hU F₂ a₂ (push U e p c) (cechD_push U e p c hc) = 0 := by
  cases p with
  | zero =>
    obtain ⟨J, V, hV, r, hr, hρ⟩ :=
      exists_refinement_eq_zero_of_cechCocycleClassAt_eq_zero U hU F₁ a₁ h₁ c hc h0
    rw [← cechCocycleClassAt_push_refinementMap e a₂ U hU V hV r hr c hc]
    exact cechCocycleClassAt_eq_zero_of_eq_zero V hV a₂ _ _ (by rw [hρ, map_zero])
  | succ q =>
    obtain ⟨J, V, hV, r, hr, t, ht⟩ :=
      exists_refinement_cechD_eq_of_cechCocycleClassAt_eq_zero U hU F₁ a₁ h₁ c hc h0
    rw [← cechCocycleClassAt_push_refinementMap e a₂ U hU V hV r hr c hc]
    exact cechCocycleClassAt_eq_zero V hV F₂ a₂ (push V e q t) _ _ (by rw [← push_cechD, ht])

/-- **Cocycles with the same class have the same class after pushing along `e`**, when Čech
cohomology computes the hypercohomology of `ℱ₁[-a₁]`. -/
theorem cechCocycleClassAt_push_eq_of_eq (h₁ : CechComputes O₁ (singlePlus O₁ F₁ a₁)) {p : ℕ}
    (c : Cochain U (abSections F₁) p) (hc : cechD U (abSections F₁) p c = 0) {I' : Type u}
    (U' : I' → Opens X) (hU' : ⊤ = ⨆ i, U' i) (c' : Cochain U' (abSections F₁) p)
    (hc' : cechD U' (abSections F₁) p c' = 0)
    (h : cechCocycleClassAt U hU F₁ a₁ c hc = cechCocycleClassAt U' hU' F₁ a₁ c' hc') :
    cechCocycleClassAt U hU F₂ a₂ (push U e p c) (cechD_push U e p c hc) =
      cechCocycleClassAt U' hU' F₂ a₂ (push U' e p c') (cechD_push U' e p c' hc') := by
  let W : I × I' → Opens X := fun ij => U ij.1 ⊓ U' ij.2
  have hW : ⊤ = ⨆ ij, W ij := iSup_inf_eq_top U hU U' hU'
  have hl : ∀ ij, W ij ≤ U ij.1 := fun _ => inf_le_left
  have hr : ∀ ij, W ij ≤ U' ij.2 := fun _ => inf_le_right
  set d := refinementMap U W Prod.fst hl (abSections F₁) p c
  set d' := refinementMap U' W Prod.snd hr (abSections F₁) p c'
  have hd := cechD_refinementMap_eq_zero U W Prod.fst hl hc
  have hd' := cechD_refinementMap_eq_zero U' W Prod.snd hr hc'
  have hs : cechD W (abSections F₁) p (d - d') = 0 := by rw [map_sub, hd, hd', sub_zero]
  have h0 : cechCocycleClassAt W hW F₁ a₁ (d - d') hs = 0 := by
    have e₁ := cechCocycleClassAt_add W hW F₁ a₁ (d - d') d' hs hd'
    rw [cechCocycleClassAt_congr W hW F₁ a₁ (sub_add_cancel d d') _ hd,
      cechCocycleClassAt_refinement U hU F₁ a₁ W hW Prod.fst hl c hc, h,
      ← cechCocycleClassAt_refinement U' hU' F₁ a₁ W hW Prod.snd hr c' hc'] at e₁
    exact right_eq_add.1 e₁
  have e₂ := cechCocycleClassAt_add W hW F₂ a₂ (push W e p (d - d')) (push W e p d')
    (cechD_push W e p _ hs) (cechD_push W e p _ hd')
  rw [cechCocycleClassAt_push_eq_zero e a₁ a₂ W hW h₁ (d - d') hs h0, zero_add,
    cechCocycleClassAt_congr W hW F₂ a₂ (by rw [← map_add, sub_add_cancel]) _
      (cechD_push W e p _ hd)] at e₂
  rw [← cechCocycleClassAt_push_refinementMap e a₂ U hU W hW Prod.fst hl c hc,
    ← cechCocycleClassAt_push_refinementMap e a₂ U' hU' W hW Prod.snd hr c' hc']
  exact e₂

/-- The value of `cechTransfer` on a class: the class of the pushforward of any representing
cocycle. -/
theorem exists_cechTransfer_value (h₁ : CechComputes O₁ (singlePlus O₁ F₁ a₁)) (p : ℕ)
    (x : hypercohomology O₁ (singlePlus O₁ F₁ a₁) ((p : ℤ) + a₁)) :
    ∃ y : hypercohomology O₂ (singlePlus O₂ F₂ a₂) ((p : ℤ) + a₂),
      ∀ (J : Type u) (V : J → Opens X) (hV : ⊤ = ⨆ j, V j) (c : Cochain V (abSections F₁) p)
        (hc : cechD V (abSections F₁) p c = 0), cechCocycleClassAt V hV F₁ a₁ c hc = x →
        cechCocycleClassAt V hV F₂ a₂ (push V e p c) (cechD_push V e p c hc) = y := by
  obtain ⟨J, V, hV, c, hc, hx⟩ := exists_cechCocycleClassAt_eq F₁ a₁ h₁ p x
  exact ⟨_, fun J' V' hV' c' hc' hx' =>
    cechCocycleClassAt_push_eq_of_eq e a₁ a₂ V' hV' h₁ c' hc' V hV c hc (hx'.trans hx.symm)⟩

/-- **The map on hypercohomology induced by a morphism `e` of the underlying abelian presheaves**,
`H^{p+a₁}(X, ℱ₁[-a₁]) ⟶ H^{p+a₂}(X, ℱ₂[-a₂])`, when Čech cohomology computes the hypercohomology
of `ℱ₁[-a₁]`: the class of an explicit Čech cocycle `c` goes to the class of `e(c)`. -/
def cechTransfer (h₁ : CechComputes O₁ (singlePlus O₁ F₁ a₁)) (p : ℕ) :
    hypercohomology O₁ (singlePlus O₁ F₁ a₁) ((p : ℤ) + a₁) →+
      hypercohomology O₂ (singlePlus O₂ F₂ a₂) ((p : ℤ) + a₂) where
  toFun x := (exists_cechTransfer_value e a₁ a₂ h₁ p x).choose
  map_zero' := by
    obtain ⟨J, V, hV, c, hc, hx⟩ := exists_cechCocycleClassAt_eq F₁ a₁ h₁ p 0
    rw [← (exists_cechTransfer_value e a₁ a₂ h₁ p 0).choose_spec J V hV c hc hx]
    exact cechCocycleClassAt_push_eq_zero e a₁ a₂ V hV h₁ c hc hx
  map_add' x y := by
    obtain ⟨J, V, hV, c, hc, rfl⟩ := exists_cechCocycleClassAt_eq F₁ a₁ h₁ p x
    obtain ⟨J', V', hV', c', hc', rfl⟩ := exists_cechCocycleClassAt_eq F₁ a₁ h₁ p y
    let W : J × J' → Opens X := fun ij => V ij.1 ⊓ V' ij.2
    have hW : ⊤ = ⨆ ij, W ij := iSup_inf_eq_top V hV V' hV'
    have hl : ∀ ij, W ij ≤ V ij.1 := fun _ => inf_le_left
    have hr : ∀ ij, W ij ≤ V' ij.2 := fun _ => inf_le_right
    set d := refinementMap V W Prod.fst hl (abSections F₁) p c
    set d' := refinementMap V' W Prod.snd hr (abSections F₁) p c'
    have hd : cechD W (abSections F₁) p d = 0 := by
      rw [← CechCochains.refinementMap_cechD, hc, map_zero]
    have hd' : cechD W (abSections F₁) p d' = 0 := by
      rw [← CechCochains.refinementMap_cechD, hc', map_zero]
    have hsum : cechCocycleClassAt V hV F₁ a₁ c hc + cechCocycleClassAt V' hV' F₁ a₁ c' hc' =
        cechCocycleClassAt W hW F₁ a₁ (d + d') (by rw [map_add, hd, hd', add_zero]) := by
      rw [cechCocycleClassAt_add W hW F₁ a₁ d d' hd hd',
        cechCocycleClassAt_refinement V hV F₁ a₁ W hW Prod.fst hl c hc,
        cechCocycleClassAt_refinement V' hV' F₁ a₁ W hW Prod.snd hr c' hc']
    rw [← (exists_cechTransfer_value e a₁ a₂ h₁ p _).choose_spec J V hV c hc rfl,
      ← (exists_cechTransfer_value e a₁ a₂ h₁ p _).choose_spec J' V' hV' c' hc' rfl,
      ← (exists_cechTransfer_value e a₁ a₂ h₁ p _).choose_spec _ W hW (d + d') _ hsum.symm,
      cechCocycleClassAt_congr W hW F₂ a₂ (map_add (push W e p) d d') _
        (by rw [map_add, cechD_push W e p d hd, cechD_push W e p d' hd', add_zero]),
      cechCocycleClassAt_add W hW F₂ a₂ _ _ (cechD_push W e p d hd) (cechD_push W e p d' hd'),
      cechCocycleClassAt_push_refinementMap e a₂ V hV W hW Prod.fst hl c hc,
      cechCocycleClassAt_push_refinementMap e a₂ V' hV' W hW Prod.snd hr c' hc']

/-- **`cechTransfer` on the class of an explicit Čech cocycle `c` is the class of `e(c)`.** -/
theorem cechTransfer_cechCocycleClassAt (h₁ : CechComputes O₁ (singlePlus O₁ F₁ a₁)) {p : ℕ}
    (c : Cochain U (abSections F₁) p) (hc : cechD U (abSections F₁) p c = 0) :
    cechTransfer e a₁ a₂ h₁ p (cechCocycleClassAt U hU F₁ a₁ c hc) =
      cechCocycleClassAt U hU F₂ a₂ (push U e p c) (cechD_push U e p c hc) :=
  ((exists_cechTransfer_value e a₁ a₂ h₁ p _).choose_spec _ U hU c hc rfl).symm

/-- **`cechTransfer` is natural** in morphisms `f₁ : ℱ₁ ⟶ 𝒢₁` and `f₂ : ℱ₂ ⟶ 𝒢₂` compatible with
the morphisms of the underlying abelian presheaves. -/
theorem cechTransfer_hypercohomologyMap {G₁ : SheafOfModules.{u} (ringSheaf O₁)}
    {G₂ : SheafOfModules.{u} (ringSheaf O₂)} (e' : abSections G₁ ⟶ abSections G₂) (f₁ : F₁ ⟶ G₁)
    (f₂ : F₂ ⟶ G₂)
    (hf : ((SheafOfModules.toSheaf _).map f₁).hom ≫ e' =
      e ≫ ((SheafOfModules.toSheaf _).map f₂).hom)
    (h₁ : CechComputes O₁ (singlePlus O₁ F₁ a₁)) (h₁' : CechComputes O₁ (singlePlus O₁ G₁ a₁))
    (p : ℕ) (x : hypercohomology O₁ (singlePlus O₁ F₁ a₁) ((p : ℤ) + a₁)) :
    cechTransfer e' a₁ a₂ h₁' p (hypercohomologyMap O₁ (singlePlusMapAt O₁ f₁ a₁) _ x) =
      hypercohomologyMap O₂ (singlePlusMapAt O₂ f₂ a₂) _ (cechTransfer e a₁ a₂ h₁ p x) := by
  obtain ⟨J, V, hV, c, hc, rfl⟩ := exists_cechCocycleClassAt_eq F₁ a₁ h₁ p x
  rw [hypercohomologyMap_cechCocycleClassAt, cechTransfer_cechCocycleClassAt,
    cechTransfer_cechCocycleClassAt, hypercohomologyMap_cechCocycleClassAt]
  refine cechCocycleClassAt_congr V hV G₂ a₂ ?_ _ _
  rw [← Stacks.Cohomology.CechOne.push_comp, hf, Stacks.Cohomology.CechOne.push_comp]

/-- **`cechTransfer` is compatible with composition.** -/
theorem cechTransfer_comp {O₃ : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u}}
    {F₃ : SheafOfModules.{u} (ringSheaf O₃)} (e' : abSections F₂ ⟶ abSections F₃) (a₃ : ℤ)
    (h₁ : CechComputes O₁ (singlePlus O₁ F₁ a₁)) (h₂ : CechComputes O₂ (singlePlus O₂ F₂ a₂))
    (p : ℕ) (x : hypercohomology O₁ (singlePlus O₁ F₁ a₁) ((p : ℤ) + a₁)) :
    cechTransfer e' a₂ a₃ h₂ p (cechTransfer e a₁ a₂ h₁ p x) =
      cechTransfer (e ≫ e') a₁ a₃ h₁ p x := by
  obtain ⟨J, V, hV, c, hc, rfl⟩ := exists_cechCocycleClassAt_eq F₁ a₁ h₁ p x
  rw [cechTransfer_cechCocycleClassAt, cechTransfer_cechCocycleClassAt,
    cechTransfer_cechCocycleClassAt]
  exact cechCocycleClassAt_congr V hV F₃ a₃
    (Stacks.Cohomology.CechOne.push_comp V e e' p c).symm _ _

/-- **`cechTransfer` along the identity is the identity.** -/
theorem cechTransfer_id (h₁ : CechComputes O₁ (singlePlus O₁ F₁ a₁)) (p : ℕ)
    (x : hypercohomology O₁ (singlePlus O₁ F₁ a₁) ((p : ℤ) + a₁)) :
    cechTransfer (𝟙 (abSections F₁)) a₁ a₁ h₁ p x = x := by
  obtain ⟨J, V, hV, c, hc, rfl⟩ := exists_cechCocycleClassAt_eq F₁ a₁ h₁ p x
  rw [cechTransfer_cechCocycleClassAt]
  exact cechCocycleClassAt_congr V hV F₁ a₁ (funext fun _ => rfl) _ _

/-- **The isomorphism `H^{p+a₁}(X, ℱ₁[-a₁]) ≅ H^{p+a₂}(X, ℱ₂[-a₂])` induced by an isomorphism `e`
of the underlying abelian presheaves**, when Čech cohomology computes both hypercohomologies: the
class of an explicit Čech cocycle `c` goes to the class of `e(c)`. -/
def cechTransferEquiv (e : abSections F₁ ≅ abSections F₂)
    (h₁ : CechComputes O₁ (singlePlus O₁ F₁ a₁)) (h₂ : CechComputes O₂ (singlePlus O₂ F₂ a₂))
    (p : ℕ) :
    hypercohomology O₁ (singlePlus O₁ F₁ a₁) ((p : ℤ) + a₁) ≃+
      hypercohomology O₂ (singlePlus O₂ F₂ a₂) ((p : ℤ) + a₂) where
  toFun := cechTransfer e.hom a₁ a₂ h₁ p
  invFun := cechTransfer e.inv a₂ a₁ h₂ p
  left_inv x := by
    rw [cechTransfer_comp, e.hom_inv_id, cechTransfer_id]
  right_inv x := by
    rw [cechTransfer_comp, e.inv_hom_id, cechTransfer_id]
  map_add' := map_add _

/-- **`cechTransferEquiv` on the class of an explicit Čech cocycle `c` is the class of `e(c)`.** -/
theorem cechTransferEquiv_cechCocycleClassAt (e : abSections F₁ ≅ abSections F₂)
    (h₁ : CechComputes O₁ (singlePlus O₁ F₁ a₁)) (h₂ : CechComputes O₂ (singlePlus O₂ F₂ a₂))
    {p : ℕ} (c : Cochain U (abSections F₁) p) (hc : cechD U (abSections F₁) p c = 0) :
    cechTransferEquiv a₁ a₂ e h₁ h₂ p (cechCocycleClassAt U hU F₁ a₁ c hc) =
      cechCocycleClassAt U hU F₂ a₂ (push U e.hom p c) (cechD_push U e.hom p c hc) :=
  cechTransfer_cechCocycleClassAt e.hom a₁ a₂ U hU h₁ c hc

/-! ### Restriction of scalars -/

section RestrictScalars

variable {O O' : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u}}
  (ψ : ringSheaf O' ⟶ ringSheaf O) (F : SheafOfModules.{u} (ringSheaf O)) (a : ℤ)

/-- **The identification `H^{p+a}(X, ℱ[-a]) ≅ H^p(X, ℱ)` across restriction of scalars** along
`ψ : 𝒪' ⟶ 𝒪`, the left side computed in sheaves of `𝒪'`-modules and the right side in sheaves of
`𝒪`-modules, when Čech cohomology computes both: restriction of scalars does not change the
underlying abelian sheaf, and the class of an explicit Čech cocycle goes to the class of the same
cocycle. -/
def restrictScalarsCechEquiv
    (hF' : CechComputes O' (singlePlus O' ((SheafOfModules.restrictScalars ψ).obj F) a))
    (hF : CechComputes O (singlePlus O F 0)) (p : ℕ) :
    hypercohomology O' (singlePlus O' ((SheafOfModules.restrictScalars ψ).obj F) a)
        ((p : ℤ) + a) ≃+
      hypercohomology O (singlePlus O F 0) p :=
  cechTransferEquiv a 0 ((sheafToPresheaf _ _).mapIso
    ((Stacks.SheafOfModules.CoextendScalars.restrictScalarsCompToSheafIso ψ).app F)) hF' hF p

/-- **The identification across restriction of scalars on the class of an explicit Čech cocycle**
is the class of the same cocycle. -/
theorem restrictScalarsCechEquiv_cechCocycleClassAt
    (hF' : CechComputes O' (singlePlus O' ((SheafOfModules.restrictScalars ψ).obj F) a))
    (hF : CechComputes O (singlePlus O F 0)) {p : ℕ}
    (c : Cochain U (abSections ((SheafOfModules.restrictScalars ψ).obj F)) p)
    (hc : cechD U (abSections ((SheafOfModules.restrictScalars ψ).obj F)) p c = 0) :
    restrictScalarsCechEquiv ψ F a hF' hF p
        (cechCocycleClassAt U hU ((SheafOfModules.restrictScalars ψ).obj F) a c hc) =
      cechCocycleClass U hU F c hc :=
  cechTransferEquiv_cechCocycleClassAt a 0 U hU _ hF' hF c hc

/-- **The identification across restriction of scalars in degree zero on the class of a global
section** is the class of the same section. -/
theorem restrictScalarsCechEquiv_sectionClass
    (hF' : CechComputes O' (singlePlus O' ((SheafOfModules.restrictScalars ψ).obj F) 0))
    (hF : CechComputes O (singlePlus O F 0)) (t : F.val.obj (op ⊤)) :
    restrictScalarsCechEquiv ψ F 0 hF' hF 0
        (sectionClass ((SheafOfModules.restrictScalars ψ).obj F) t) = sectionClass F t := by
  have h := restrictScalarsCechEquiv_cechCocycleClassAt (fun _ : PUnit.{u + 1} => (⊤ : Opens X))
    top_eq_iSup_top ψ F 0 hF' hF
    (restrictionCochain _ ((SheafOfModules.restrictScalars ψ).obj F) t)
    (cechD_restrictionCochain _ _ t)
  exact (congrArg (restrictScalarsCechEquiv ψ F 0 hF' hF 0)
    (cechCocycleClass_restrictionCochain _ top_eq_iSup_top
      ((SheafOfModules.restrictScalars ψ).obj F) t)).symm.trans
      (h.trans (cechCocycleClass_restrictionCochain _ top_eq_iSup_top F t))

/-- **The identification across restriction of scalars is natural** in morphisms of sheaves of
`𝒪`-modules. -/
theorem restrictScalarsCechEquiv_hypercohomologyMap {G : SheafOfModules.{u} (ringSheaf O)}
    (f : F ⟶ G)
    (hF' : CechComputes O' (singlePlus O' ((SheafOfModules.restrictScalars ψ).obj F) a))
    (hF : CechComputes O (singlePlus O F 0))
    (hG' : CechComputes O' (singlePlus O' ((SheafOfModules.restrictScalars ψ).obj G) a))
    (hG : CechComputes O (singlePlus O G 0)) (p : ℕ)
    (x : hypercohomology O' (singlePlus O' ((SheafOfModules.restrictScalars ψ).obj F) a)
      ((p : ℤ) + a)) :
    restrictScalarsCechEquiv ψ G a hG' hG p
        (hypercohomologyMap O' (singlePlusMapAt O' ((SheafOfModules.restrictScalars ψ).map f) a)
          _ x) =
      hypercohomologyMap O (singlePlusMap O f) p (restrictScalarsCechEquiv ψ F a hF' hF p x) :=
  cechTransfer_hypercohomologyMap ((sheafToPresheaf _ _).map
      ((Stacks.SheafOfModules.CoextendScalars.restrictScalarsCompToSheafIso ψ).hom.app F)) a 0
    ((sheafToPresheaf _ _).map
      ((Stacks.SheafOfModules.CoextendScalars.restrictScalarsCompToSheafIso ψ).hom.app G))
    ((SheafOfModules.restrictScalars ψ).map f) f rfl hF' hG' p x

/-- **The identification across restriction of scalars carries cup products to cup products**, up
to the sign `(-1)^{aq}`: for a bilinear map `β : ℱ × 𝒢 ⟶ ℋ` of sheaves of `𝒪`-modules, the cup
product along the pairing of `ℱ[-a]` and `𝒢[-b]` attached to `β` read over `𝒪'` goes to `(-1)^{aq}`
times the cup product along the pairing attached to `β` of sheaves in degree zero. -/
theorem restrictScalarsCechEquiv_cup {G H : SheafOfModules.{u} (ringSheaf O)} (b : ℤ)
    (β : Stacks.BilinearMap F.val G.val H.val)
    (hF' : CechComputes O' (singlePlus O' ((SheafOfModules.restrictScalars ψ).obj F) a))
    (hG' : CechComputes O' (singlePlus O' ((SheafOfModules.restrictScalars ψ).obj G) b))
    (hH' : CechComputes O' (singlePlus O' ((SheafOfModules.restrictScalars ψ).obj H) (a + b)))
    (hF : CechComputes O (singlePlus O F 0)) (hG : CechComputes O (singlePlus O G 0))
    (hH : CechComputes O (singlePlus O H 0)) (p q : ℕ)
    (x : hypercohomology O' (singlePlus O' ((SheafOfModules.restrictScalars ψ).obj F) a)
      ((p : ℤ) + a))
    (y : hypercohomology O' (singlePlus O' ((SheafOfModules.restrictScalars ψ).obj G) b)
      ((q : ℤ) + b)) :
    restrictScalarsCechEquiv ψ H (a + b) hH' hH (p + q)
        (cup O' hF' hG' (singlePairingAt a b (bilinearPairing
            (F := (SheafOfModules.restrictScalars ψ).obj F)
            (G := (SheafOfModules.restrictScalars ψ).obj G)
            (H := (SheafOfModules.restrictScalars ψ).obj H) (β.restrictScalars ψ.hom)))
          ((p : ℤ) + a) ((q : ℤ) + b) (((p + q : ℕ) : ℤ) + (a + b)) (by push_cast; ring) x y) =
      ((a * q).negOnePow : ℤ) • cup O hF hG (singlePairing (bilinearPairing β)) p q
        ((p + q : ℕ) : ℤ) (by push_cast; rfl) (restrictScalarsCechEquiv ψ F a hF' hF p x)
        (restrictScalarsCechEquiv ψ G b hG' hG q y) := by
  obtain ⟨J, V, hV, c, hc, rfl⟩ := exists_cechCocycleClassAt_eq _ a hF' p x
  obtain ⟨J', V', hV', d, hd, rfl⟩ := exists_cechCocycleClassAt_eq _ b hG' q y
  let W : J × J' → Opens X := fun ij => V ij.1 ⊓ V' ij.2
  have hW : ⊤ = ⨆ ij, W ij := iSup_inf_eq_top V hV V' hV'
  have hl : ∀ ij, W ij ≤ V ij.1 := fun _ => inf_le_left
  have hr : ∀ ij, W ij ≤ V' ij.2 := fun _ => inf_le_right
  rw [← cechCocycleClassAt_refinement V hV _ a W hW Prod.fst hl c hc,
    ← cechCocycleClassAt_refinement V' hV' _ b W hW Prod.snd hr d hd,
    cup_cechCocycleClassAt W hW a b hF' hG' (H := (SheafOfModules.restrictScalars ψ).obj H)
      (β.restrictScalars ψ.hom), map_zsmul, restrictScalarsCechEquiv_cechCocycleClassAt,
    restrictScalarsCechEquiv_cechCocycleClassAt, restrictScalarsCechEquiv_cechCocycleClassAt]
  exact congrArg _ (cup_cechCocycleClass W hW hF hG β _ _ _ _).symm

end RestrictScalars

end Stacks.Cech.Hypercohomology

end
