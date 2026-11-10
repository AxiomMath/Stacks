module

public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassDerived.CommonRankRefinement
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassDerived.Independence
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassDerived.MappingConeComplex
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassDerived.TotalChernWhitney

/-!
# The total Chern class is multiplicative on a mapping cone

Let `Y` be locally of finite type over the base of chapter 42 of the Stacks Project and let
`α : 𝓔₁^• ⟶ 𝓔₂^•` be a map of locally bounded complexes of finite locally free `𝒪_Y`-modules.
Since `C(α)^n = 𝓔₁^{n + 1} ⊕ 𝓔₂^n`, the Whitney sum formula and the alternating signs give

  `c(𝓔₂^•) = c(𝓔₁^•) c(C(α)^•)`,

the displayed identity in the third paragraph of the proof of [Stacks, Tag 0F9F].

## Main results

* `Stacks.Chow.complexChernFactor_eq_of_biprod` — the factor of degree `n` of a complex whose
  terms are the biproducts `𝓔₁^{n + 1} ⊕ 𝓔₂^n` is `c(𝓔₁^{n + 1})^{-(-1)^{n+1}} c(𝓔₂^n)^{(-1)^n}`.
* `Stacks.Chow.complexChernBounded_eq_mul_of_biprod_terms` — the identity for bounded complexes
  of constant ranks, stated for any complex whose terms are those biproducts.
* `Stacks.Chow.complexChern_mappingCone` — the identity `c(𝓔₂^•) = c(𝓔₁^•) c(C(α)^•)` for
  locally bounded complexes.

## Implementation notes

The ring of total Chow cohomology classes is not claimed to be commutative, so the products
defining `Stacks.Chow.complexChernBounded` are taken over a sorted list of degrees. Two generic
list lemmas in a monoid resp. a group with pairwise-commuting entries,
`Stacks.Chow.list_prod_map_mul_of_commute` and `Stacks.Chow.list_prod_map_inv_of_commute`, replace
the commutativity that `List.prod_map_mul` would need; the commutation they are fed with is
`Stacks.Chow.commute_totalChern`.

The bounded identity is stated for an arbitrary complex `R` whose terms are *isomorphic to* the
biproducts `𝓔₁^{n + 1} ⊕ 𝓔₂^n`, not for the cone itself. That is what makes the descent step go
through: the restriction of `c(C(α)^•)` is read on the *termwise pullback* of the cone, and a
termwise pullback of the cone is not the cone of a map of termwise pullbacks — the pullback
functor on sheaves of modules is additive but is not known here to preserve binary biproducts.
Its terms are nevertheless biproducts, by
`Stacks.Chow.pullbackMappingConeXIsoBiprod`, which splits `g^*(A ⊕ B)` using the
pullback of the split short exact sequence `0 ⟶ A ⟶ A ⊕ B ⟶ B ⟶ 0`.

## References

* [Stacks Project, Tag 0F9F](https://stacks.math.columbia.edu/tag/0F9F)
* [Stacks Project, Tag 02UI](https://stacks.math.columbia.edu/tag/02UI)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

/-! ### Products of pairwise-commuting entries -/

section ListCommute

/-- The head of a list of pairwise-commuting entries commutes with the product of the tail. -/
private theorem commute_list_prod_map_of_cons {M α : Type*} [Monoid M] (a : α) (t : List α)
    (f g : α → M) (h : ∀ x ∈ a :: t, ∀ y ∈ a :: t, Commute (g x) (f y)) :
    Commute (g a) ((t.map f).prod) :=
  Commute.list_prod_right _ _ fun y hy ↦ by
    obtain ⟨m, hm, rfl⟩ := List.mem_map.1 hy
    exact h a List.mem_cons_self m (List.mem_cons_of_mem a hm)

/-- **Splitting a product of pointwise products**, in a monoid where the entries of the two
families commute: `∏ (f n * g n) = (∏ f n) (∏ g n)` along a list. This is `List.prod_map_mul`
with commutativity of the ambient monoid weakened to commutativity of the entries. -/
theorem list_prod_map_mul_of_commute {M α : Type*} [Monoid M] (l : List α) (f g : α → M)
    (h : ∀ x ∈ l, ∀ y ∈ l, Commute (g x) (f y)) :
    (l.map fun n ↦ f n * g n).prod = (l.map f).prod * (l.map g).prod := by
  induction l with
  | nil => simp
  | cons a t ih =>
    have ht : ∀ x ∈ t, ∀ y ∈ t, Commute (g x) (f y) := fun x hx y hy ↦
      h x (List.mem_cons_of_mem a hx) y (List.mem_cons_of_mem a hy)
    rw [List.map_cons, List.map_cons, List.map_cons, List.prod_cons, List.prod_cons,
      List.prod_cons, ih ht, mul_assoc, mul_assoc, ← mul_assoc (g a),
      (commute_list_prod_map_of_cons a t f g h).eq, mul_assoc]

/-- **Inverting a product of pairwise-commuting entries**, in a group: `∏ (f n)⁻¹ = (∏ f n)⁻¹`
along a list. Without the commutation the right-hand side would be the product over the reversed
list (`List.prod_inv_reverse`). -/
theorem list_prod_map_inv_of_commute {G α : Type*} [Group G] (l : List α) (f : α → G)
    (h : ∀ x ∈ l, ∀ y ∈ l, Commute (f x) (f y)) :
    (l.map fun n ↦ (f n)⁻¹).prod = ((l.map f).prod)⁻¹ := by
  induction l with
  | nil => simp
  | cons a t ih =>
    have ht : ∀ x ∈ t, ∀ y ∈ t, Commute (f x) (f y) := fun x hx y hy ↦
      h x (List.mem_cons_of_mem a hx) y (List.mem_cons_of_mem a hy)
    rw [List.map_cons, List.map_cons, List.prod_cons, List.prod_cons, ih ht, mul_inv_rev,
      (commute_list_prod_map_of_cons a t f f h).inv_inv.eq]

end ListCommute

/-! ### Commutation of the factors of two complexes -/

/-- **Two factors of the total Chern classes of two complexes commute.** Each is a power of a
total Chern class, and total Chern classes commute (`Stacks.Chow.commute_totalChern`). -/
theorem commute_complexChernFactor (C : ChowSituation.{u}) {W : Scheme.{u}} (sW : W ⟶ C.S)
    [LocallyOfFiniteType sW] (P₁ P₂ : CochainComplex W.Modules ℤ) (ρ σ : ℤ → ℕ)
    (h₁ : ∀ n, AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (P₁.X n) (ρ n))
    (h₂ : ∀ n, AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (P₂.X n) (σ n)) (m n : ℤ) :
    Commute (complexChernFactor C sW P₁ ρ h₁ m) (complexChernFactor C sW P₂ σ h₂ n) := by
  have _ := h₁ m
  have _ := h₂ n
  have h : Commute (totalChernUnit C sW (P₁.X m) (ρ m)) (totalChernUnit C sW (P₂.X n) (σ n)) :=
    .units_of_val (commute_totalChern C sW (P₁.X m) (P₂.X n) (ρ m) (σ n))
  change Commute (totalChernUnit C sW (P₁.X m) (ρ m) ^ ((m.negOnePow : ℤˣ) : ℤ))
    (totalChernUnit C sW (P₂.X n) (σ n) ^ ((n.negOnePow : ℤˣ) : ℤ))
  exact h.zpow_zpow _ _

/-! ### The total Chern class of a complex of biproducts -/

section Factor

variable (C : ChowSituation.{u}) {W : Scheme.{u}} (sW : W ⟶ C.S) [LocallyOfFiniteType sW]
  (Q₁ Q₂ R : CochainComplex W.Modules ℤ) (ρ σ : ℤ →₀ ℕ)
  (hρ : ∀ n, AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (Q₁.X n) (ρ n))
  (hσ : ∀ n, AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (Q₂.X n) (σ n))
  (hR : ∀ n, AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (R.X n)
    (coneRank ρ σ n))

/-- **The factor of degree `n` of a complex whose terms are biproducts splits.** If
`R^n ≅ 𝓔₁^{n + 1} ⊕ 𝓔₂^n` then

  `c(R^n)^{(-1)^n} = (c(𝓔₁^{n+1})^{(-1)^{n+1}})^{-1} c(𝓔₂^n)^{(-1)^n}`,

by the Whitney sum formula `Stacks.Chow.totalChern_biprod` for the biproduct and
`Int.negOnePow_succ` for the sign. The two total Chern classes commute
(`Stacks.Chow.commute_totalChern`), which is what lets the exponent be distributed over the
product. -/
theorem complexChernFactor_eq_of_biprod (e : ∀ n, R.X n ≅ Q₁.X (n + 1) ⊞ Q₂.X n) (n : ℤ) :
    complexChernFactor C sW R (coneRank ρ σ) hR n =
      (complexChernFactor C sW Q₁ ρ hρ (n + 1))⁻¹ * complexChernFactor C sW Q₂ σ hσ n := by
  have _ := hρ (n + 1)
  have _ := hσ n
  have _ := hR n
  have _ := GenuineChern.isFiniteLocallyFreeOfRank_of_shortExact
    (ShortComplex.mk (biprod.inl : Q₁.X (n + 1) ⟶ Q₁.X (n + 1) ⊞ Q₂.X n)
      (biprod.snd : Q₁.X (n + 1) ⊞ Q₂.X n ⟶ Q₂.X n) (by simp))
    (ShortComplex.Splitting.ofHasBinaryBiproduct (Q₁.X (n + 1)) (Q₂.X n)).shortExact
    (ρ (n + 1)) (σ n) (hρ (n + 1)) (hσ n)
  have hcomm : Commute (totalChernUnit C sW (Q₁.X (n + 1)) (ρ (n + 1)))
      (totalChernUnit C sW (Q₂.X n) (σ n)) :=
    .units_of_val (commute_totalChern C sW (Q₁.X (n + 1)) (Q₂.X n) (ρ (n + 1)) (σ n))
  have ha : totalChernUnit C sW (R.X n) (coneRank ρ σ n) =
      totalChernUnit C sW (Q₁.X (n + 1)) (ρ (n + 1)) * totalChernUnit C sW (Q₂.X n) (σ n) :=
    Units.ext <| (totalChern_congr C sW (e n) (coneRank_apply ρ σ n)).trans
      (totalChern_biprod C sW (Q₁.X (n + 1)) (Q₂.X n) (ρ (n + 1)) (σ n))
  have hsign : ((n.negOnePow : ℤˣ) : ℤ) = -(((n + 1).negOnePow : ℤˣ) : ℤ) := by
    rw [Int.negOnePow_succ]
    simp
  change totalChernUnit C sW (R.X n) (coneRank ρ σ n) ^ ((n.negOnePow : ℤˣ) : ℤ) =
    (totalChernUnit C sW (Q₁.X (n + 1)) (ρ (n + 1)) ^ (((n + 1).negOnePow : ℤˣ) : ℤ))⁻¹ *
      totalChernUnit C sW (Q₂.X n) (σ n) ^ ((n.negOnePow : ℤˣ) : ℤ)
  rw [ha, hcomm.mul_zpow, hsign]
  simp only [zpow_neg]

/-- **The ordered alternating product of a complex of biproducts over a window splits.** If
`R^n ≅ 𝓔₁^{n + 1} ⊕ 𝓔₂^n` then, over any interval of degrees `[A, b]`,

  `∏_{n ∈ [A, b]} c(R^n)^{(-1)^n}
     = (∏_{n ∈ [A + 1, b + 1]} c(𝓔₁^n)^{(-1)^n})^{-1} ∏_{n ∈ [A, b]} c(𝓔₂^n)^{(-1)^n}`,

the shift of the interval on the right coming from `Stacks.Chow.map_sort_Icc_add_one`. No
vanishing of the ranks is needed: the identity is the termwise splitting
`Stacks.Chow.complexChernFactor_eq_of_biprod` followed by the two product manipulations, each of
which only needs the factors to commute. -/
theorem complexChernProd_eq_of_biprod_terms (e : ∀ n, R.X n ≅ Q₁.X (n + 1) ⊞ Q₂.X n) (A b : ℤ) :
    complexChernProd C sW R (coneRank ρ σ) hR (Finset.Icc A b) =
      (complexChernProd C sW Q₁ ρ hρ (Finset.Icc (A + 1) (b + 1)))⁻¹ *
        complexChernProd C sW Q₂ σ hσ (Finset.Icc A b) := by
  have hmapR : ((Finset.Icc A b).sort (· ≤ ·)).map
        (complexChernFactor C sW R (coneRank ρ σ) hR) =
      ((Finset.Icc A b).sort (· ≤ ·)).map fun n ↦
        (complexChernFactor C sW Q₁ ρ hρ (n + 1))⁻¹ *
          complexChernFactor C sW Q₂ σ hσ n :=
    List.map_congr_left fun n _ ↦
      complexChernFactor_eq_of_biprod C sW Q₁ Q₂ R ρ σ hρ hσ hR e n
  have hsplit : (((Finset.Icc A b).sort (· ≤ ·)).map fun n ↦
        (complexChernFactor C sW Q₁ ρ hρ (n + 1))⁻¹ *
          complexChernFactor C sW Q₂ σ hσ n).prod =
      (((Finset.Icc A b).sort (· ≤ ·)).map fun n ↦
          (complexChernFactor C sW Q₁ ρ hρ (n + 1))⁻¹).prod *
        (((Finset.Icc A b).sort (· ≤ ·)).map (complexChernFactor C sW Q₂ σ hσ)).prod :=
    list_prod_map_mul_of_commute _ _ _ fun x _ y _ ↦
      (commute_complexChernFactor C sW Q₂ Q₁ σ ρ hσ hρ x (y + 1)).inv_right
  have hinv : (((Finset.Icc A b).sort (· ≤ ·)).map fun n ↦
        (complexChernFactor C sW Q₁ ρ hρ (n + 1))⁻¹).prod =
      ((((Finset.Icc A b).sort (· ≤ ·)).map fun n ↦
        complexChernFactor C sW Q₁ ρ hρ (n + 1)).prod)⁻¹ :=
    list_prod_map_inv_of_commute _ _ fun x _ y _ ↦
      commute_complexChernFactor C sW Q₁ Q₁ ρ ρ hρ hρ (x + 1) (y + 1)
  have hidx : (((Finset.Icc A b).sort (· ≤ ·)).map fun n ↦
        complexChernFactor C sW Q₁ ρ hρ (n + 1)) =
      ((Finset.Icc (A + 1) (b + 1)).sort (· ≤ ·)).map (complexChernFactor C sW Q₁ ρ hρ) := by
    rw [← map_sort_Icc_add_one A b, List.map_map]
    rfl
  rw [complexChernProd, complexChernProd, complexChernProd, hmapR, hsplit, hinv, hidx]

/-- **The total Chern class is multiplicative on a complex of biproducts**, for bounded complexes
of constant ranks: if `R^n ≅ 𝓔₁^{n + 1} ⊕ 𝓔₂^n` for every `n`, then

  `c(𝓔₂^•) = c(𝓔₁^•) c(R^•)`.

The three classes are read as ordered products over a common window
(`Stacks.Chow.complexChernBounded_eq_prod`), chosen from
`Stacks.Chow.exists_window_of_finsupp` and widened by one on each side so that it contains the
supports of `ρ`, of `σ` and of `n ↦ ρ(n + 1) + σ(n)`; there
`Stacks.Chow.complexChernProd_eq_of_biprod_terms` says that `c(R^•) = c(𝓔₁^•)^{-1} c(𝓔₂^•)`. -/
theorem complexChernBounded_eq_mul_of_biprod_terms
    (e : ∀ n, R.X n ≅ Q₁.X (n + 1) ⊞ Q₂.X n) :
    complexChernBounded C sW Q₂ σ hσ =
      complexChernBounded C sW Q₁ ρ hρ * complexChernBounded C sW R (coneRank ρ σ) hR := by
  obtain ⟨a, k, hρ0, hσ0⟩ := exists_window_of_finsupp ρ σ
  have hc₂ := complexChernBounded_eq_prod C sW Q₂ σ hσ (Finset.Icc (a - 1) (a + (k : ℤ)))
    fun n hn ↦ hσ0 n (by rw [Finset.mem_Icc] at hn; omega)
  have hc₁ := complexChernBounded_eq_prod C sW Q₁ ρ hρ (Finset.Icc (a - 1 + 1) (a + (k : ℤ) + 1))
    fun n hn ↦ hρ0 n (by rw [Finset.mem_Icc] at hn; omega)
  have hcR := complexChernBounded_eq_prod C sW R (coneRank ρ σ) hR
    (Finset.Icc (a - 1) (a + (k : ℤ))) fun n hn ↦ by
      rw [Finset.mem_Icc] at hn
      rw [coneRank_apply, hρ0 (n + 1) (by omega), hσ0 n (by omega)]
  have hu : complexChernProd C sW Q₂ σ hσ (Finset.Icc (a - 1) (a + (k : ℤ))) =
      complexChernProd C sW Q₁ ρ hρ (Finset.Icc (a - 1 + 1) (a + (k : ℤ) + 1)) *
        complexChernProd C sW R (coneRank ρ σ) hR (Finset.Icc (a - 1) (a + (k : ℤ))) := by
    rw [complexChernProd_eq_of_biprod_terms C sW Q₁ Q₂ R ρ σ hρ hσ hR e (a - 1) (a + (k : ℤ)),
      mul_inv_cancel_left]
  rw [hc₂, hc₁, hcR, ← Units.val_mul, hu]

end Factor

/-! ### The total Chern class of the cone -/

section Cone

/-- **The terms of the termwise pullback of a cone are biproducts.** For `g : Z ⟶ Y` and
`α : 𝓔₁^• ⟶ 𝓔₂^•`,

  `g^*(C(α)^n) ≅ g^*(𝓔₁^{n + 1}) ⊕ g^*(𝓔₂^n)`,

obtained from `Stacks.Chow.mappingConeXIsoBiprod` by pulling back and then splitting
`g^*(A ⊕ B)`: the pullback functor is additive, so it carries the split short exact sequence
`0 ⟶ A ⟶ A ⊕ B ⟶ B ⟶ 0` to a split one, and a splitting identifies its middle term with the
biproduct of its outer terms (`CategoryTheory.ShortComplex.Splitting.isoBinaryBiproduct`).

This is weaker than `g^*` preserving binary biproducts, which is not available here, and it is
exactly what `Stacks.Chow.complexChernBounded_eq_mul_of_biprod_terms` asks for. -/
def pullbackMappingConeXIsoBiprod {Y Z : Scheme.{u}} {P₁ P₂ : CochainComplex Y.Modules ℤ}
    (g : Z ⟶ Y) (α : P₁ ⟶ P₂) (n : ℤ) :
    (pullbackComplex g (CochainComplex.mappingCone α : CochainComplex Y.Modules ℤ)).X n ≅
      (pullbackComplex g P₁).X (n + 1) ⊞ (pullbackComplex g P₂).X n :=
  (Scheme.Modules.pullback g).mapIso (mappingConeXIsoBiprod α n) ≪≫
    ((ShortComplex.Splitting.ofHasBinaryBiproduct (P₁.X (n + 1)) (P₂.X n)).map
      (Scheme.Modules.pullback g)).isoBinaryBiproduct

/-- **The total Chern class is multiplicative on a mapping cone** (the displayed identity in the
third paragraph of the proof of [Stacks, Tag 0F9F]). For a map `α : 𝓔₁^• ⟶ 𝓔₂^•` of locally
bounded complexes of finite locally free `𝒪_Y`-modules,

  `c(𝓔₂^•) = c(𝓔₁^•) c(C(α)^•)`.

The identity is read on the common refinement of the two rank decompositions
(`Stacks.Chow.eq_of_res_eq_of_constantRanks`): over a scheme `g : Z ⟶ Y` where both termwise
pullbacks have constant ranks `ρ` and `σ`, the three restrictions are the total Chern classes of
the bounded complexes `g^*𝓔₁^•`, `g^*𝓔₂^•` and `g^*C(α)^•`
(`Stacks.Chow.res_complexChern_eq_complexChernBounded`, the ranks of the last being
`n ↦ ρ(n + 1) + σ(n)` by
`Stacks.Chow.isFiniteLocallyFreeOfRank_pullbackComplex_mappingCone_X`), and there the identity is
`Stacks.Chow.complexChernBounded_eq_mul_of_biprod_terms`. -/
theorem complexChern_mappingCone (C : ChowSituation.{u}) {Y : Scheme.{u}} (sY : Y ⟶ C.S)
    [LocallyOfFiniteType sY] {P₁ P₂ : CochainComplex Y.Modules ℤ} (α : P₁ ⟶ P₂)
    (h₁ : IsLocallyBoundedFiniteLocallyFree P₁) (h₂ : IsLocallyBoundedFiniteLocallyFree P₂) :
    complexChern C sY h₂ =
      complexChern C sY h₁ *
        complexChern C sY (isLocallyBoundedFiniteLocallyFree_mappingCone α h₁ h₂) := by
  refine eq_of_res_eq_of_constantRanks C sY h₁ h₂ fun Z g _ ρ σ hρg hσg ↦ ?_
  rw [map_mul, res_complexChern_eq_complexChernBounded C sY h₂ g rfl σ hσg,
    res_complexChern_eq_complexChernBounded C sY h₁ g rfl ρ hρg,
    res_complexChern_eq_complexChernBounded C sY
      (isLocallyBoundedFiniteLocallyFree_mappingCone α h₁ h₂) g rfl (coneRank ρ σ)
      (isFiniteLocallyFreeOfRank_pullbackComplex_mappingCone_X g α ρ σ hρg hσg)]
  exact complexChernBounded_eq_mul_of_biprod_terms C (g ≫ sY) (pullbackComplex g P₁)
    (pullbackComplex g P₂) _ ρ σ hρg hσg _ (pullbackMappingConeXIsoBiprod g α)

end Cone

end Stacks.Chow

end
