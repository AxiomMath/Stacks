module

public import StacksFrontier.AlgebraicGeometry.Scheme.FunctorialityQuasiCoherent.Basic

/-!
# Sections of a quasi-coherent module over a union of basic opens

Let `M` be a quasi-coherent module on an affine scheme `X` and `y_j ∈ Γ(X, 𝒪_X)` a family of
functions, at least two of them. If each `y_j` acts injectively on `Γ(M, X)` and a pair of
denominators at distinct indices can always be cleared by a common cofactor, then restriction
`Γ(M, X) ⟶ Γ(M, ⋃_j D(y_j))` is bijective. For the free module of `a`-forms on affine space and
the last coordinates `y_1, …, y_n`, with `n ≥ 2`, this is the extension of forms across the
coordinate subspace of codimension `n`, the "small detail omitted" in the source's proof of
clause (1) of [Stacks, Tag 0FUR].

## Main results

* `Stacks.AlgebraicGeometry.BasicOpenUnion.bijective_res_iSup_basicOpen`: under these
  hypotheses, restriction `Γ(M, X) ⟶ Γ(M, ⋃_j D(y_j))` is bijective.

## References

* [Stacks Project, Tag 0FUR](https://stacks.math.columbia.edu/tag/0FUR)
* [Stacks Project, Tag 01P7](https://stacks.math.columbia.edu/tag/01P7)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace Stacks.AlgebraicGeometry.BasicOpenUnion

variable {X : Scheme.{u}} (M : X.Modules)

/-- Restriction of sections is functorial. -/
theorem res_res {U V W : X.Opens} (h₁ : V ≤ U) (h₂ : W ≤ V) (x : Γ(M, U)) :
    M.presheaf.map (homOfLE h₂).op (M.presheaf.map (homOfLE h₁).op x) =
      M.presheaf.map (homOfLE (h₂.trans h₁)).op x := by
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp]
  rfl

/-- Restriction of functions is functorial. -/
theorem resO_resO {U V W : X.Opens} (h₁ : V ≤ U) (h₂ : W ≤ V) (x : Γ(X, U)) :
    X.presheaf.map (homOfLE h₂).op (X.presheaf.map (homOfLE h₁).op x) =
      X.presheaf.map (homOfLE (h₂.trans h₁)).op x := by
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp]
  rfl

/-- Restriction of functions to the same open is the identity. -/
theorem resO_refl {U : X.Opens} (x : Γ(X, U)) :
    X.presheaf.map (homOfLE (le_refl U)).op x = x := by simp

variable [IsAffine X]

omit [IsAffine X] in
/-- `g` becomes a unit on `D(g)`. -/
theorem isUnit_res_top_inf_basicOpen (g : Γ(X, ⊤)) :
    IsUnit (X.presheaf.map (homOfLE (inf_le_left : ⊤ ⊓ X.basicOpen g ≤ ⊤)).op g) := by
  have h := X.toLocallyRingedSpace.toRingedSpace.isUnit_res_basicOpen g
  have h2 := h.map
    (X.presheaf.map (homOfLE (inf_le_right : ⊤ ⊓ X.basicOpen g ≤ X.basicOpen g)).op).hom
  exact (resO_resO (homOfLE (X.basicOpen_le g)).le inf_le_right g) ▸ h2

variable [M.IsQuasicoherent]

/-- A global section vanishing on `D(g)` is killed by a power of `g`. -/
theorem exists_pow_smul_eq_zero_of_res_eq_zero (g : Γ(X, ⊤)) (x : Γ(M, ⊤))
    (h : M.presheaf.map (homOfLE (inf_le_left : ⊤ ⊓ X.basicOpen g ≤ ⊤)).op x = 0) :
    ∃ k : ℕ, g ^ k • x = 0 := by
  obtain ⟨k, hk⟩ := Scheme.Modules.exists_pow_smul_res_eq_zero_of_isCompact M g ⊤
    isCompact_univ le_rfl x h
  exact ⟨k, by rwa [resO_refl] at hk⟩

/-- A power of `g` times a section over `D(g)` extends to a global section. -/
theorem exists_res_eq_pow_smul (g : Γ(X, ⊤)) (y : Γ(M, ⊤ ⊓ X.basicOpen g)) :
    ∃ (x : Γ(M, ⊤)) (k : ℕ),
      M.presheaf.map (homOfLE (inf_le_left : ⊤ ⊓ X.basicOpen g ≤ ⊤)).op x =
        X.presheaf.map (homOfLE (inf_le_left : ⊤ ⊓ X.basicOpen g ≤ ⊤)).op g ^ k • y :=
  Scheme.Modules.exists_res_eq_pow_smul_of_isCompact M g isQuasiSeparated_univ ⊤
    isCompact_univ le_rfl y

omit [IsAffine X] [M.IsQuasicoherent] in
/-- Restriction of sections is semilinear over restriction of functions. -/
theorem res_smul {U V : X.Opens} (h : V ≤ U) (r : Γ(X, U)) (x : Γ(M, U)) :
    M.presheaf.map (homOfLE h).op (r • x) =
      X.presheaf.map (homOfLE h).op r • M.presheaf.map (homOfLE h).op x :=
  Scheme.Modules.map_smul M (homOfLE h) r x

omit [IsAffine X] [M.IsQuasicoherent] in
/-- `res_smul` for a power. -/
theorem res_pow_smul {U V : X.Opens} (h : V ≤ U) (r : Γ(X, U)) (k : ℕ) (x : Γ(M, U)) :
    M.presheaf.map (homOfLE h).op (r ^ k • x) =
      X.presheaf.map (homOfLE h).op r ^ k • M.presheaf.map (homOfLE h).op x := by
  rw [res_smul, map_pow]

/-- A global section vanishing on `D(g)` is zero if `g` acts injectively. -/
private theorem eq_zero_of_res_eq_zero {g : Γ(X, ⊤)} (hg : IsSMulRegular Γ(M, ⊤) g)
    {x : Γ(M, ⊤)}
    (h : M.presheaf.map (homOfLE (inf_le_left : ⊤ ⊓ X.basicOpen g ≤ ⊤)).op x = 0) : x = 0 := by
  obtain ⟨k, hk⟩ := exists_pow_smul_eq_zero_of_res_eq_zero M g x h
  exact (hg.pow k) (hk.trans (smul_zero _).symm)

/-- **Sections over a union of basic opens: a Hartogs-type extension.** Let `M` be a
quasi-coherent module on an affine scheme `X` and `y : ι → Γ(X, 𝒪_X)` a family of functions, at
least two of them, each acting injectively on `Γ(M, X)`, such that a pair of denominators at
distinct indices can be cleared by a common cofactor: `y_j^l u = y_i^k v` with `i ≠ j` forces
`u = y_i^k w` and `v = y_j^l w`. Then restriction `Γ(M, X) ⟶ Γ(M, ⋃_j D(y_j))` is bijective. -/
theorem bijective_res_iSup_basicOpen {ι : Type*} (y : ι → Γ(X, ⊤))
    (h1 : ∀ j, IsSMulRegular Γ(M, ⊤) (y j))
    (h2 : ∀ i j, i ≠ j → ∀ (u v : Γ(M, ⊤)) (k l : ℕ), y j ^ l • u = y i ^ k • v →
      ∃ w, u = y i ^ k • w ∧ v = y j ^ l • w)
    (i₀ j₀ : ι) (hij : i₀ ≠ j₀) :
    Function.Bijective
      (M.presheaf.map (homOfLE (le_top : (⨆ j, X.basicOpen (y j)) ≤ ⊤)).op) := by
  have hDU : ∀ j, ⊤ ⊓ X.basicOpen (y j) ≤ ⨆ j, X.basicOpen (y j) := fun j =>
    inf_le_right.trans (le_iSup (fun j => X.basicOpen (y j)) j)
  have hD : ∀ j, ⊤ ⊓ X.basicOpen (y j) ≤ (⊤ : X.Opens) := fun _ => inf_le_left
  refine ⟨?_, fun t => ?_⟩
  · intro s t hst
    rw [← sub_eq_zero]
    have h0 : M.presheaf.map (homOfLE (hD i₀)).op (s - t) = 0 := by
      rw [← res_res M le_top (hDU i₀), map_sub, hst, sub_self, map_zero]
    exact eq_zero_of_res_eq_zero M (h1 i₀) h0
  choose ω k hω using fun j =>
    exists_res_eq_pow_smul M (y j) (M.presheaf.map (homOfLE (hDU j)).op t)
  have hδ : ∀ j, y j ^ k j • ω i₀ = y i₀ ^ k i₀ • ω j := by
    intro j
    rw [← sub_eq_zero]
    have hE₁ : ⊤ ⊓ X.basicOpen (y i₀ * y j) ≤ ⊤ ⊓ X.basicOpen (y i₀) := by
      rw [Scheme.basicOpen_mul]; exact inf_le_inf_left _ inf_le_left
    have hE₂ : ⊤ ⊓ X.basicOpen (y i₀ * y j) ≤ ⊤ ⊓ X.basicOpen (y j) := by
      rw [Scheme.basicOpen_mul]; exact inf_le_inf_left _ inf_le_right
    have hr : ∀ (i : ι) (hE : ⊤ ⊓ X.basicOpen (y i₀ * y j) ≤ ⊤ ⊓ X.basicOpen (y i)),
        M.presheaf.map (homOfLE (inf_le_left : ⊤ ⊓ X.basicOpen (y i₀ * y j) ≤ ⊤)).op (ω i) =
          X.presheaf.map (homOfLE (inf_le_left : ⊤ ⊓ X.basicOpen (y i₀ * y j) ≤ ⊤)).op (y i) ^ k i
            • M.presheaf.map (homOfLE (hE.trans (hDU i))).op t := by
      intro i hE
      rw [← res_res M (hD i) hE, hω i, res_pow_smul, res_res, resO_resO]
    have h0 : M.presheaf.map (homOfLE (inf_le_left : ⊤ ⊓ X.basicOpen (y i₀ * y j) ≤ ⊤)).op
        (y j ^ k j • ω i₀ - y i₀ ^ k i₀ • ω j) = 0 := by
      rw [map_sub, res_pow_smul, res_pow_smul, hr i₀ hE₁, hr j hE₂, smul_smul, smul_smul]
      exact sub_eq_zero.mpr (congrArg (· • _) (mul_comm _ _))
    exact eq_zero_of_res_eq_zero M ((h1 i₀).mul (h1 j)) h0
  obtain ⟨ζ, hζ0, -⟩ := h2 i₀ j₀ hij (ω i₀) (ω j₀) (k i₀) (k j₀) (hδ j₀)
  have hall : ∀ j, ω j = y j ^ k j • ζ := by
    intro j
    by_cases hj : j = i₀
    · subst hj; exact hζ0
    obtain ⟨w, hw0, hwj⟩ := h2 i₀ j (Ne.symm hj) (ω i₀) (ω j) (k i₀) (k j) (hδ j)
    have hw : w = ζ := ((h1 i₀).pow (k i₀)) (hw0.symm.trans hζ0)
    rw [hwj, hw]
  refine ⟨ζ, (Scheme.Modules.isSheaf M).section_ext
    (U := op (⨆ j, X.basicOpen (y j))) fun x hx => ?_⟩
  obtain ⟨j, hxj⟩ := Opens.mem_iSup.mp hx
  refine ⟨⊤ ⊓ X.basicOpen (y j), hDU j, ⟨trivial, hxj⟩, ?_⟩
  rw [res_res]
  refine ((isUnit_res_top_inf_basicOpen (y j)).pow (k j)).smul_left_cancel.mp ?_
  rw [← hω j, ← res_pow_smul, ← hall j]

end Stacks.AlgebraicGeometry.BasicOpenUnion
