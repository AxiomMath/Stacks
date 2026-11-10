module

public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.TameMultiplicativeGroup.FiberAction

/-!
# The tame fundamental group of `𝐆_m` over a finite field

Let `k` be a finite field with `q` elements. The homomorphism `Γ → π₁ᵗ(𝐆_{m,k}, η̄)`,
`Γ = Ẑ^{(q)} ⋊ Ẑ` with `F x F⁻¹ = q⁻¹ x`, of the action on the fibres of tame covers through the
Kummer tower is an isomorphism of topological groups:

* it is injective, since `γ` acting trivially on the base points of all layers acts trivially on
  every layer of the tower;
* it is surjective: for `σ ∈ π₁ᵗ`, the sets of `γ` agreeing with `σ` at the base point of the layer
  `K_m` are closed, nonempty (the deck group acts transitively on the fibre of `K_m`) and
  decreasing, so they meet since `Γ` is compact, and an element of `π₁ᵗ` is determined by its
  values at these base points;
* it is continuous, since its value at a point of a fibre depends only on the action at one layer;
* `Γ` is compact and `π₁ᵗ` is Hausdorff.

## Main results

* `AlgebraicGeometry.TameMultiplicativeGroup.tameFundamentalGroupEquiv`:
  `Ẑ^{(q)} ⋊ Ẑ ≃ₜ* π₁ᵗ(𝐆_{m,k}, η̄)`.
-/

@[expose] public noncomputable section

open CategoryTheory Polynomial Stacks.TraceFormula Topology

universe u

namespace AlgebraicGeometry.TameMultiplicativeGroup

variable {k : Type u} [Field k] [Fintype k]

/-- The ring map at the base point of the layer `K_m` takes values in the range of `towerPoint`. -/
theorem fiberRingHom_basePoint_mem (m : ℕ) (c : Γ((towerCover k m).obj.left, ⊤)) :
    fiberRingHom (basePoint k m) c ∈ (towerPoint k m).range := by
  rw [fiberRingHom_basePoint]
  exact ⟨_, rfl⟩

/-- The ring map at the base point of the layer `K_m`, composed with the inverse of
`Scheme.ΓSpecIso`, is `towerPoint k m`. -/
theorem fiberRingHom_basePoint_inv (m : ℕ) (z : Ring (towerField k m)) :
    fiberRingHom (basePoint k m)
        ((Scheme.ΓSpecIso (CommRingCat.of (Ring (towerField k m)))).inv.hom z) =
      towerPoint k m z := by
  have hinv : (Scheme.ΓSpecIso (CommRingCat.of (Ring (towerField k m)))).hom.hom
      ((Scheme.ΓSpecIso (CommRingCat.of (Ring (towerField k m)))).inv.hom z) = z :=
    ConcreteCategory.congr_hom (Scheme.ΓSpecIso (CommRingCat.of (Ring (towerField k m)))).inv_hom_id
      (show CommRingCat.of (Ring (towerField k m)) from z)
  exact (RingHom.congr_fun (fiberRingHom_basePoint m) _).trans (congrArg (towerPoint k m) hinv)

/-- If a point `y` of a fibre is valued in the layer `K_m`, then elements of `Γ` with the same
image in the deck group of `K_m` act on `y` in the same way. -/
theorem fiberAct_eq_of_deck_eq {Y : TameCover k} {y : (tameFiberFunctor k).obj Y} {m : ℕ}
    (hm : ∀ c, fiberRingHom y c ∈ (towerPoint k m).range)
    {γ γ' : Gamma (inverseCharacter (Fintype.card k))} (h : deck k m γ = deck k m γ') :
    fiberAct γ Y y = fiberAct γ' Y y :=
  fiber_ext (by
    rw [fiberRingHom_fiberAct, fiberRingHom_fiberAct]
    exact towerAct_congr h _ _ hm)

/-- **The action on a point of a fibre is locally constant.** -/
theorem isOpen_setOf_fiberAct_mem (Y : TameCover k) (y : (tameFiberFunctor k).obj Y)
    (S : Set ((tameFiberFunctor k).obj Y)) :
    IsOpen {γ : Gamma (inverseCharacter (Fintype.card k)) | fiberAct γ Y y ∈ S} := by
  obtain ⟨m, hm⟩ := isTowerValued_fiberRingHom y
  rw [isOpen_iff_forall_mem_open]
  intro γ hγ
  refine ⟨{γ' | deck k m γ' = deck k m γ}, fun γ' hγ' ↦ ?_, isOpen_setOf_deck_eq k m γ, rfl⟩
  change fiberAct γ' Y y ∈ S
  rw [fiberAct_eq_of_deck_eq hm hγ']
  exact hγ

/-- **`Γ → π₁ᵗ` is injective.** -/
theorem tameAutHom_injective : Function.Injective (tameAutHom (k := k)) := by
  rw [injective_iff_map_eq_one]
  intro γ hγ
  refine eq_one_of_forall_deck_eq_one k γ fun m ↦ RingEquiv.ext fun z ↦ ?_
  have h : fiberAct γ _ (basePoint k m) = basePoint k m :=
    congrArg (fun σ ↦ autApply σ _ (basePoint k m)) hγ
  have hr := congrArg fiberRingHom h
  rw [fiberRingHom_fiberAct, towerAct_eq _ _ _ (fiberRingHom_basePoint_mem m)] at hr
  have h1 := RingHom.congr_fun hr
    ((Scheme.ΓSpecIso (CommRingCat.of (Ring (towerField k m)))).inv.hom z)
  have h2 : tau k m γ ⟨_, fiberRingHom_basePoint_mem m
      ((Scheme.ΓSpecIso (CommRingCat.of (Ring (towerField k m)))).inv.hom z)⟩ =
      fiberRingHom (basePoint k m)
        ((Scheme.ΓSpecIso (CommRingCat.of (Ring (towerField k m)))).inv.hom z) := h1
  rw [tau_eq k γ _ (fiberRingHom_basePoint_inv m z).symm, fiberRingHom_basePoint_inv] at h2
  exact towerPoint_injective k m h2

/-- The elements of `Γ` acting on the base point of `K_m` as `σ` does. -/
def agreeSet (σ : tameFundamentalGroup k) (m : ℕ) :
    Set (Gamma (inverseCharacter (Fintype.card k))) :=
  {γ | fiberAct γ _ (basePoint k m) = autApply σ _ (basePoint k m)}

/-- The set `agreeSet σ m` is closed in `Γ`. -/
theorem isClosed_agreeSet (σ : tameFundamentalGroup k) (m : ℕ) : IsClosed (agreeSet σ m) := by
  rw [← isOpen_compl_iff]
  exact isOpen_setOf_fiberAct_mem _ _ {autApply σ _ (basePoint k m)}ᶜ

/-- The sets `agreeSet σ m` are decreasing in `m`. -/
theorem agreeSet_succ_subset (σ : tameFundamentalGroup k) (m : ℕ) :
    agreeSet σ (m + 1) ⊆ agreeSet σ m :=
  fun γ hγ ↦ autApply_basePoint_of_succ (σ := tameAutHom γ) m hγ

/-- **The deck group acts transitively on the fibre of `K_m`.** -/
theorem agreeSet_nonempty (σ : tameFundamentalGroup k) (m : ℕ) : (agreeSet σ m).Nonempty := by
  set y' := autApply σ _ (basePoint k m)
  let χ : Ring (towerField k m) →+* Omega k :=
    ((Scheme.ΓSpecIso (CommRingCat.of (Ring (towerField k m)))).inv ≫ pointRingHom y'.1).hom
  have hs : ∀ z, (strHom (towerCover k m).obj).hom z =
      (Scheme.ΓSpecIso (CommRingCat.of (Ring (towerField k m)))).inv.hom
        (kummerMap k (towerField k m) (towerN k m) z) :=
    fun z ↦ RingHom.congr_fun (congrArg CommRingCat.Hom.hom (strHom_towerCover m)) z
  have hχ : ∀ z, χ (kummerMap k (towerField k m) (towerN k m) z) = baseHom k z := fun z ↦
    (congrArg (fiberRingHom y') (hs z).symm).trans
      (RingHom.congr_fun (fiberRingHom_comp_strHom y') z)
  obtain ⟨γ, hγ⟩ := exists_eq_towerPoint_comp_deck k m χ hχ
  refine ⟨γ, fiber_ext (RingHom.ext fun c ↦ ?_)⟩
  rw [fiberRingHom_fiberAct, towerAct_eq _ _ _ (fiberRingHom_basePoint_mem m), actAt_apply,
    tau_eq k γ _ (RingHom.congr_fun (fiberRingHom_basePoint m) c).symm]
  have h1 := RingHom.congr_fun hγ
    ((Scheme.ΓSpecIso (CommRingCat.of (Ring (towerField k m)))).hom.hom c)
  have hinv : (Scheme.ΓSpecIso (CommRingCat.of (Ring (towerField k m)))).inv.hom
      ((Scheme.ΓSpecIso (CommRingCat.of (Ring (towerField k m)))).hom.hom c) = c :=
    ConcreteCategory.congr_hom (Scheme.ΓSpecIso _).hom_inv_id c
  exact h1.symm.trans (congrArg (fiberRingHom y') hinv)

attribute [local instance] compactSpace_gamma

/-- **`Γ → π₁ᵗ` is surjective.** -/
theorem tameAutHom_surjective : Function.Surjective (tameAutHom (k := k)) := by
  intro σ
  obtain ⟨γ, hγ⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
    (agreeSet σ) (agreeSet_succ_subset σ) (agreeSet_nonempty σ) (isClosed_agreeSet σ 0).isCompact
    (isClosed_agreeSet σ)
  exact ⟨γ, eq_of_forall_basePoint fun m ↦ Set.mem_iInter.mp hγ m⟩

/-- **`Γ → π₁ᵗ` is continuous.** -/
theorem continuous_tameAutHom : Continuous (tameAutHom (k := k)) := by
  let (Y : TameCover k) : TopologicalSpace ((tameFiberFunctor k).obj Y) := ⊥
  have (Y : TameCover k) : DiscreteTopology ((tameFiberFunctor k).obj Y) := ⟨rfl⟩
  refine continuous_induced_rng.mpr (continuous_pi fun Y ↦ ?_)
  refine continuous_induced_rng.mpr (continuous_pi fun y ↦ ?_)
  exact continuous_discrete_rng.mpr fun y' ↦ isOpen_setOf_fiberAct_mem Y y {y'}

/-- **`π₁ᵗ(𝐆_{m,k}, η̄)` is Hausdorff.** -/
instance : T2Space (tameFundamentalGroup k) := by
  let (Y : TameCover k) : TopologicalSpace ((tameFiberFunctor k).obj Y) := ⊥
  have (Y : TameCover k) : DiscreteTopology ((tameFiberFunctor k).obj Y) := ⟨rfl⟩
  let (Y : TameCover k) : TopologicalSpace (Equiv.Perm ((tameFiberFunctor k).obj Y)) := autTopology
  have (Y : TameCover k) : T2Space (Equiv.Perm ((tameFiberFunctor k).obj Y)) :=
    (⟨IsInducing.induced _, Equiv.coe_fn_injective⟩ :
      IsEmbedding (fun e : Equiv.Perm ((tameFiberFunctor k).obj Y) ↦
        (e : (tameFiberFunctor k).obj Y → (tameFiberFunctor k).obj Y))).t2Space
  let : TopologicalSpace (Aut (tameFiberFunctor k)) := functorAutomorphismTopology _
  let : TopologicalSpace (∀ Y, Equiv.Perm ((tameFiberFunctor k).obj Y)) :=
    automorphismProductTopology _
  exact (isClosedEmbedding_componentEmbedding (tameFiberFunctor k)).isEmbedding.t2Space

variable (k) in
/-- **The tame fundamental group of `𝐆_m` over a finite field.** For `k` finite with `q`
elements, the action on the fibres of tame covers through the Kummer tower is an isomorphism of
topological groups `Ẑ^{(q)} ⋊ Ẑ ≃ₜ* π₁ᵗ(𝐆_{m,k}, η̄)`, where `F x F⁻¹ = q⁻¹ x`. -/
def tameFundamentalGroupEquiv :
    Gamma (inverseCharacter (Fintype.card k)) ≃ₜ* tameFundamentalGroup k :=
  let e := MulEquiv.ofBijective (tameAutHom (k := k)) ⟨tameAutHom_injective, tameAutHom_surjective⟩
  { e with
    continuous_toFun := continuous_tameAutHom
    continuous_invFun :=
      (continuous_tameAutHom.homeoOfEquivCompactToT2 (f := e.toEquiv)).symm.continuous }

/-- The isomorphism `tameFundamentalGroupEquiv k` is given by `tameAutHom`. -/
theorem tameFundamentalGroupEquiv_apply (γ : Gamma (inverseCharacter (Fintype.card k))) :
    tameFundamentalGroupEquiv k γ = tameAutHom γ := rfl

omit [Fintype k] in
/-- `π₁ᵗ(𝐆_{m,k}, η̄)` is compact. -/
instance [Finite k] : CompactSpace (tameFundamentalGroup k) :=
  letI := Fintype.ofFinite k
  (tameFundamentalGroupEquiv k).toHomeomorph.compactSpace

omit [Fintype k] in
/-- `π₁ᵗ(𝐆_{m,k}, η̄)` is totally disconnected. -/
instance [Finite k] : TotallyDisconnectedSpace (tameFundamentalGroup k) :=
  letI := Fintype.ofFinite k
  haveI := totallyDisconnectedSpace_gamma (inverseCharacter (Fintype.card k))
  (tameFundamentalGroupEquiv k).toHomeomorph.totallyDisconnectedSpace

end AlgebraicGeometry.TameMultiplicativeGroup

end
