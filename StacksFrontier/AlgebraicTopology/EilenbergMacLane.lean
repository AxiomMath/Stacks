module

public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.AlgebraicTopology.SimplicialObject.Basic
public import Mathlib.CategoryTheory.Abelian.FunctorCategory

/-!
# Eilenberg–MacLane objects `K(A, k)`

The Eilenberg–MacLane objects `K(A, k)` of an abelian category, and the short exact sequence
relating `K(A, k)` and `K(A, k + 1)`.
-/

/-!
## Eilenberg-MacLane objects

Let `C` be a category with a zero object and zero morphisms, let `A` be an object of `C` and let
`k : ℕ`. Write `U` for the `k`-truncated simplicial object of `C` concentrated in the top degree,
`U_i = 0` for `i < k` and `U_k = A`, all of whose operators vanish except `U(id_⦋k⦌) = id_A`; this
is the object `U` of [Stacks, Tag 0190]. The *Eilenberg-MacLane object* `K(A, k)` is the simplicial
object `i_{k!}U` obtained from `U` by left Kan extension along the inclusion of the `k`-truncated
simplex category, i.e. by the left adjoint of `k`-truncation.

By [Stacks, Tag 0190](2) its `n`-th term is `⊕_α A`, the sum over the surjections `α : ⦋n⦌ → ⦋k⦌`,
and for `φ : ⦋m⦌ → ⦋n⦌` the operator `K(A, k)(φ)` sends the summand `α` by the identity to the
summand `α ∘ φ` when the latter is surjective and to zero otherwise.

### Main definitions

* `CategoryTheory.SimplicialObject.eilenbergMacLane`: the Eilenberg-MacLane object `K(A, k)` of
  an object `A` and an integer `k ≥ 0`.

### References

* [Stacks, Tag 0191](https://stacks.math.columbia.edu/tag/0191)
-/

section

@[expose] public section

open CategoryTheory Limits Opposite Simplicial ZeroObject
open scoped SimplexCategory.Truncated

universe v u

namespace CategoryTheory.SimplicialObject

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C] [HasZeroObject C]

/-- An epimorphism out of `n` in the `k`-truncated simplex category cannot lower the dimension, so
a surjection `φ : n → m` with `m` of top dimension `k` forces `n` to have dimension `k` as well. -/
private lemma len_eq_of_surjective {k : ℕ} {m n : (SimplexCategory.Truncated k)ᵒᵖ} (φ : m ⟶ n)
    (hs : Function.Surjective φ.unop.hom.toOrderHom) (hm : m.unop.obj.len = k) :
    n.unop.obj.len = k :=
  have : Epi φ.unop.hom := SimplexCategory.epi_iff_surjective.mpr hs
  le_antisymm n.unop.property (hm.symm.trans_le (SimplexCategory.len_le_of_epi φ.unop.hom))

/-- **Stacks 0191**.
For an object `A` of `C` and an integer `k ≥ 0`, the *Eilenberg-MacLane object* `K(A, k)` is
`K(A, k) = i_{k!}U`, the left Kan extension along the inclusion of the `k`-truncated simplex
category (equivalently, the image under the left adjoint of `k`-truncation) of the `k`-truncated
simplicial object `U` of [Stacks, Tag 0190] with `U_i = 0` for `i < k`, `U_k = A` and all
operators `U(φ)` zero except `U(id_⦋k⦌) = id_A`. -/
@[stacks 0191]
public noncomputable def eilenbergMacLane (A : C) (k : ℕ)
    [∀ F : (SimplexCategory.Truncated k)ᵒᵖ ⥤ C,
      (SimplexCategory.Truncated.inclusion k).op.HasLeftKanExtension F] :
    SimplicialObject C :=
  (SimplicialObject.Truncated.sk k).obj
    { obj := fun m => if m.unop.obj.len = k then A else 0
      map := fun {m n} φ =>
        if h : Function.Surjective φ.unop.hom.toOrderHom ∧ m.unop.obj.len = k then
          eqToHom (by
            obtain ⟨hs, hm⟩ := h
            rw [ite_eq_left hm, ite_eq_left (len_eq_of_surjective φ hs hm)])
        else 0
      map_id := fun m => by
        by_cases hm : m.unop.obj.len = k
        · rw [dite_eq_left (⟨fun x => ⟨x, rfl⟩, hm⟩ :
            Function.Surjective (𝟙 m).unop.hom.toOrderHom ∧ m.unop.obj.len = k)]
          simp
        · rw [dite_eq_right (fun h => hm h.2)]
          refine (IsZero.eq_of_src ?_ _ _).symm
          rw [ite_eq_right hm]
          exact isZero_zero C
      map_comp := fun {m n p} φ ψ => by
        have hiff : (Function.Surjective (φ ≫ ψ).unop.hom.toOrderHom ∧ m.unop.obj.len = k) ↔
            ((Function.Surjective φ.unop.hom.toOrderHom ∧ m.unop.obj.len = k) ∧
              (Function.Surjective ψ.unop.hom.toOrderHom ∧ n.unop.obj.len = k)) := by
          have hcomp : Function.Surjective (φ ≫ ψ).unop.hom.toOrderHom ↔
              Function.Surjective (φ.unop.hom.toOrderHom ∘ ψ.unop.hom.toOrderHom) := by
            simp
          constructor
          · rintro ⟨hs, hm⟩
            have hsφ : Function.Surjective φ.unop.hom.toOrderHom := (hcomp.mp hs).of_comp
            have hn : n.unop.obj.len = k := len_eq_of_surjective φ hsφ hm
            have : Epi φ.unop.hom := SimplexCategory.epi_iff_surjective.mpr hsφ
            have : IsIso φ.unop.hom :=
              (SimplexCategory.isIso_iff_of_epi φ.unop.hom).mpr (hn.trans hm.symm)
            exact ⟨⟨hsφ, hm⟩, (hcomp.mp hs).of_comp_left
              (SimplexCategory.mono_iff_injective.mp inferInstance), hn⟩
          · rintro ⟨⟨hsφ, hm⟩, hsψ, -⟩
            exact ⟨hcomp.mpr (hsφ.comp hsψ), hm⟩
        by_cases h : Function.Surjective φ.unop.hom.toOrderHom ∧ m.unop.obj.len = k
        · by_cases h' : Function.Surjective ψ.unop.hom.toOrderHom ∧ n.unop.obj.len = k
          · rw [dite_eq_left (hiff.mpr ⟨h, h'⟩), dite_eq_left h, dite_eq_left h']
            simp
          · rw [dite_eq_right h', dite_eq_right (fun hc => h' (hiff.mp hc).2), comp_zero]
        · rw [dite_eq_right h, dite_eq_right (fun hc => h (hiff.mp hc).1), zero_comp] }

attribute [implicit_reducible] eilenbergMacLane

end CategoryTheory.SimplicialObject

end

end

/-!
## The extension relating `K(A, k)` and `K(A, k + 1)`

Let `𝒜` be an abelian category, let `A` be an object of `𝒜` and let `k` be an integer `≥ 0`. By
[Stacks, Tag 0190](2)-(3) the Eilenberg–MacLane simplicial object `K(A, k)` has
`K(A, k)_n = ⨁_α A`, the sum over the surjective monotone maps `α : [n] → [k]`, and the
structure map attached to a monotone `φ : [m] → [n]` carries the summand indexed by `α` via `id_A`
into the summand indexed by `α ∘ φ` when `α ∘ φ` is again surjective, and by `0` otherwise. The
simplicial object `E` is built by the same rule from the monotone maps `α : [n] → [k + 1]` whose
image is `[k]` or `[k + 1]`. This module takes these rules as the definition of an explicit model
`emKAk A k` of `K(A, k)`, constructs the sequence `0 → emKAk A k → E → emKAk A (k + 1) → 0`,
where the first map includes the summands of `(emKAk A k)_n` along the bottom inclusion
`[k] ↪ [k + 1]` and the second projects onto the summands indexed by the surjective maps, and
shows that it is short exact and split in each degree. The identification of `emKAk A k` with
`eilenbergMacLane A k`, and the resulting statement of [Stacks, Tag 0192] for the
Eilenberg–MacLane objects themselves, are in
`StacksFrontier.AlgebraicTopology.EilenbergMacLaneExplicit`.

Both index sets are cut out by a single predicate: `coversBelow s α` says that `α` attains every
value `≤ s` of its codomain. A monotone `α : [n] → [k]` is surjective iff `coversBelow k α`; a
monotone `α : [n] → [k + 1]` has image `[k]` or `[k + 1]` iff `coversBelow k α`, since `k + 1` is
the only value it may miss below the top; and it is surjective iff `coversBelow (k + 1) α`.

The declarations of this section live in the namespace
`CategoryTheory.SimplicialObject.EilenbergMacLane`.

### Main definitions

* `emObject`: the simplicial object with `n`-th term `⨁_α A` over the monotone maps
  `α : [n] → T` satisfying an admissibility predicate closed downwards under precomposition.
* `emRelabel`: the morphism of two such objects induced by postcomposition with a fixed
  `ρ : T₁ ⟶ T₂`.
* `emKAk`, `emEobj`: the explicit model of `K(A, k)` given by [Stacks, Tag 0190](2)-(3), and the
  simplicial object `E`, as `emObject`s for `coversBelow`. The isomorphism of `emKAk A k` with
  `eilenbergMacLane A k` and the statement of [Stacks, Tag 0192] for `eilenbergMacLane` are in
  `StacksFrontier.AlgebraicTopology.EilenbergMacLaneExplicit`.
* `emIota`, `emPi`: the morphisms `ι : K(A, k) ⟶ E` and `π : E ⟶ K(A, k + 1)`.
* `emShortComplex`: the short complex `K(A, k) ⟶ E ⟶ K(A, k + 1)` of simplicial objects.
* `emSplittingApp`: a splitting of `emShortComplex A k` evaluated in a degree `n`.

### Main results

* `emSplit`: the sequence is term by term split, i.e. evaluating `emShortComplex A k` in any
  degree `n` gives a short complex of `𝒜` that admits a splitting.
* `emShortComplex_shortExact`: `0 → K(A, k) → E → K(A, k + 1) → 0` is a short exact sequence
  of simplicial objects.

### References

* [Stacks, Tag 0192](https://stacks.math.columbia.edu/tag/0192)
-/

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.SimplicialObject.EilenbergMacLane

/-- The morphisms `m ⟶ n` of `SimplexCategory` form a finite type, being the monotone
functions `Fin (m.len + 1) → Fin (n.len + 1)`. -/
noncomputable instance simplexHomFintype (m n : SimplexCategory) : Fintype (m ⟶ n) :=
  Fintype.ofEquiv {f : Fin (m.len + 1) → Fin (n.len + 1) // Monotone f}
    { toFun := fun f => SimplexCategory.Hom.mk ⟨f.1, f.2⟩
      invFun := fun g => ⟨g.toOrderHom, g.toOrderHom.monotone⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => SimplexCategory.Hom.ext _ _ (OrderHom.ext _ _ rfl) }

/-- The matrix with `𝟙` on the diagonal and `0` off the diagonal is the identity morphism. -/
theorem biproduct_matrix_id {J : Type} [Finite J] [DecidableEq J]
    {C : Type*} [Category C] [Preadditive C] [HasFiniteBiproducts C] (A : C) :
    biproduct.matrix (fun a b : J => if b = a then 𝟙 A else (0 : A ⟶ A))
      = 𝟙 (⨁ (fun _ : J => A)) := by
  ext a b
  simp only [biproduct.matrix_π, biproduct.ι_desc, Category.id_comp]
  by_cases h : a = b
  · subst h
    simp
  · rw [ite_eq_right h, biproduct.ι_π_ne _ (Ne.symm h)]

/-- Composition of biproduct matrices is matrix multiplication. -/
theorem biproduct_matrix_comp {J K L : Type} [Finite J] [Fintype K] [Finite L]
    {C : Type*} [Category C] [Preadditive C] [HasFiniteBiproducts C]
    {f : J → C} {g : K → C} {h : L → C}
    (M : (j : J) → (k : K) → f j ⟶ g k) (N : (k : K) → (l : L) → g k ⟶ h l) :
    biproduct.matrix M ≫ biproduct.matrix N
      = biproduct.matrix (fun j l => ∑ k, M j k ≫ N k l) := by
  ext j l
  simp only [biproduct.matrix_π, Category.assoc, biproduct.ι_desc, biproduct.ι_matrix_assoc]
  rw [biproduct.lift_desc]

/-- A sum over a subtype where the summands carry an indicator on the underlying value
collapses to a single term (or zero, when no admissible index matches). -/
theorem subtype_indicator_sum {b : Type} [Fintype b] [DecidableEq b]
    (P : b → Prop) [DecidablePred P]
    {C : Type*} [Category C] [Preadditive C] (A B : C)
    (x : b) (mor : {β : b // P β} → (A ⟶ B)) :
    (∑ β : {β : b // P β}, (if (β:b) = x then (𝟙 A) else 0) ≫ mor β)
      = if h : P x then mor ⟨x, h⟩ else 0 := by
  by_cases hx : P x
  · rw [dite_eq_left hx, Finset.sum_eq_single (⟨x, hx⟩ : {β : b // P β})]
    · simp
    · intro β _ hβ
      have : (β : b) ≠ x := fun hbx => hβ (Subtype.ext hbx)
      rw [ite_eq_right this, zero_comp]
    · simp
  · rw [dite_eq_right hx]
    refine Finset.sum_eq_zero fun β _ => ?_
    have : (β : b) ≠ x := fun hbx => hx (hbx ▸ β.2)
    rw [ite_eq_right this, zero_comp]

variable {𝒜 : Type*} [Category 𝒜] [Abelian 𝒜] [HasFiniteBiproducts 𝒜]

/-- The image of a simplicial morphism, as a `Finset` of its codomain. -/
def imageFinset {m n : SimplexCategory} (α : m ⟶ n) : Finset (Fin (n.len + 1)) :=
  Finset.univ.image α.toOrderHom

/-- `coversBelow s α` holds when the monotone map `α` attains every value `≤ s` of its codomain. -/
@[implicit_reducible]
def coversBelow {n T : SimplexCategory} (s : ℕ) (α : n ⟶ T) : Prop :=
  ∀ i : Fin (T.len + 1), (i : ℕ) ≤ s → i ∈ imageFinset α

/-- `coversBelow s` is a decidable predicate on the morphisms `n ⟶ T` of `SimplexCategory`. -/
instance instCoversBelowDec {n T : SimplexCategory} (s : ℕ) :
    DecidablePred (coversBelow s (n := n) (T := T)) := by
  intro α
  unfold coversBelow
  infer_instance

/-- Precomposition can only shrink the image, so `coversBelow` of a composite implies
`coversBelow` of the right-hand factor. -/
theorem coversBelow_of_precomp {a b T : SimplexCategory} (s : ℕ) (g : b ⟶ a) (δ : a ⟶ T)
    (h : coversBelow s (g ≫ δ)) : coversBelow s δ := by
  intro i hi
  have hmem := h i hi
  simp only [imageFinset, Finset.mem_image, Finset.mem_univ, true_and] at hmem ⊢
  obtain ⟨x, hx⟩ := hmem
  exact ⟨g.toOrderHom x, by simpa using hx⟩

/-- `coversBelow s` is closed downwards under precomposition: if `g ≫ h ≫ α` covers below `s`
then so does `h ≫ α`. -/
theorem coversBelow_hP {T : SimplexCategory} (s : ℕ) :
    ∀ {a b c : SimplexCategory} (g : a ⟶ b) (h : b ⟶ c) (α : c ⟶ T),
      coversBelow s α → coversBelow s (g ≫ h ≫ α) → coversBelow s (h ≫ α) :=
  fun g h α _ hgha => coversBelow_of_precomp s g (h ≫ α) hgha

/-- The Eilenberg–MacLane-style simplicial object with target `T` and admissibility predicate
`P n` on the monotone maps `[n] → T`: in degree `n` it is the biproduct `⨁_α A` over the
admissible `α : [n] → T`, and the structure map attached to a monotone `φ : [m] → [n]` sends
the summand indexed by an admissible `α` by the identity into the summand indexed by `φ ≫ α`
when that is admissible, and by zero otherwise. The hypothesis `hP` says that admissibility is
closed downwards under precomposition. -/
@[implicit_reducible]
noncomputable def emObject (A : 𝒜) (T : SimplexCategory)
    (P : (n : SimplexCategory) → (n ⟶ T) → Prop) [∀ n, DecidablePred (P n)]
    (hP : ∀ {a b c : SimplexCategory} (g : a ⟶ b) (h : b ⟶ c) (α : c ⟶ T),
      P c α → P a (g ≫ h ≫ α) → P b (h ≫ α)) :
    SimplicialObject 𝒜 where
  obj n := ⨁ (fun _ : {α : n.unop ⟶ T // P n.unop α} => A)
  map {a b} φ :=
    biproduct.matrix
      (fun (α : {α : a.unop ⟶ T // P a.unop α})
           (β : {α : b.unop ⟶ T // P b.unop α}) =>
        if β.1 = φ.unop ≫ α.1 then (𝟙 A) else (0 : A ⟶ A))
  map_id X := by
    rw [← biproduct_matrix_id A]
    congr 1
    ext α β
    simp only [unop_id, Category.id_comp]
    congr 1
    exact propext ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩
  map_comp {X Y Z} f g := by
    rw [biproduct_matrix_comp]
    congr 1
    ext α γ
    rw [subtype_indicator_sum (P Y.unop) A A (f.unop ≫ α.1)
      (fun β => if (γ:Z.unop⟶T) = g.unop ≫ (β:Y.unop⟶T) then (𝟙 A) else (0:A⟶A))]
    have hassoc : (f ≫ g).unop ≫ α.1 = g.unop ≫ f.unop ≫ α.1 := by simp
    by_cases hβ : P Y.unop (f.unop ≫ α.1)
    · rw [dite_eq_left hβ, hassoc]
    · rw [dite_eq_right hβ]
      have hne : (γ:Z.unop⟶T) ≠ (f ≫ g).unop ≫ α.1 := by
        intro heq
        rw [hassoc] at heq
        refine hβ (hP g.unop f.unop α.1 α.2 ?_)
        rw [← heq]; exact γ.2
      rw [ite_eq_right hne]

/-- The structure map of `emObject` attached to `φ`, as a biproduct matrix. -/
theorem emObject_map (A : 𝒜) (T : SimplexCategory)
    (P : (n : SimplexCategory) → (n ⟶ T) → Prop) [∀ n, DecidablePred (P n)]
    (hP : ∀ {a b c : SimplexCategory} (g : a ⟶ b) (h : b ⟶ c) (α : c ⟶ T),
      P c α → P a (g ≫ h ≫ α) → P b (h ≫ α)) {a b : SimplexCategoryᵒᵖ} (φ : a ⟶ b) :
    (emObject A T P hP).map φ = biproduct.matrix
      (fun (α : {α : a.unop ⟶ T // P a.unop α}) (β : {α : b.unop ⟶ T // P b.unop α}) =>
        if β.1 = φ.unop ≫ α.1 then (𝟙 A) else (0 : A ⟶ A)) :=
  rfl

/-- The relabeling morphism of two `emObject`s induced by postcomposition with a fixed
`ρ : T₁ ⟶ T₂`: in degree `n` it sends the summand indexed by a `P`-admissible `α : [n] → T₁` by
the identity into the summand indexed by `α ≫ ρ`, and by zero otherwise. Here `hL` says that
`Q`-admissibility of `α ≫ ρ` implies `P`-admissibility of `α`, and `hR` says that `Q` is closed
under cancelling a precomposition. -/
noncomputable def emRelabel (A : 𝒜) (T₁ T₂ : SimplexCategory)
    (P : (n : SimplexCategory) → (n ⟶ T₁) → Prop) [∀ n, DecidablePred (P n)]
    (Q : (n : SimplexCategory) → (n ⟶ T₂) → Prop) [∀ n, DecidablePred (Q n)]
    (hP : ∀ {a b c : SimplexCategory} (g : a ⟶ b) (h : b ⟶ c) (α : c ⟶ T₁),
      P c α → P a (g ≫ h ≫ α) → P b (h ≫ α))
    (hQ : ∀ {a b c : SimplexCategory} (g : a ⟶ b) (h : b ⟶ c) (α : c ⟶ T₂),
      Q c α → Q a (g ≫ h ≫ α) → Q b (h ≫ α))
    (ρ : T₁ ⟶ T₂)
    (hL : ∀ {n : SimplexCategory} (δ : n ⟶ T₁), Q n (δ ≫ ρ) → P n δ)
    (hR : ∀ {a b : SimplexCategory} (g : b ⟶ a) (δ : a ⟶ T₂), Q b (g ≫ δ) → Q a δ) :
    emObject A T₁ P hP ⟶ emObject A T₂ Q hQ where
  app n :=
    biproduct.matrix
      (fun (α : {α : n.unop ⟶ T₁ // P n.unop α})
           (β : {α : n.unop ⟶ T₂ // Q n.unop α}) =>
        if β.1 = α.1 ≫ ρ then (𝟙 A) else (0 : A ⟶ A))
  naturality {a b} φ := by
    rw [emObject_map, emObject_map, biproduct_matrix_comp, biproduct_matrix_comp]
    congr 1
    ext α β
    rw [subtype_indicator_sum (P b.unop) A A (φ.unop ≫ α.1)
      (fun α' => if (β:b.unop⟶T₂) = (α':b.unop⟶T₁) ≫ ρ then (𝟙 A) else (0:A⟶A))]
    rw [subtype_indicator_sum (Q a.unop) A A (α.1 ≫ ρ)
      (fun β' => if (β:b.unop⟶T₂) = φ.unop ≫ (β':a.unop⟶T₂) then (𝟙 A) else (0:A⟶A))]
    by_cases hcase : (β:b.unop⟶T₂) = φ.unop ≫ α.1 ≫ ρ
    · have hPg : P b.unop (φ.unop ≫ α.1) := by
        apply hL
        have : (φ.unop ≫ α.1) ≫ ρ = β.1 := by rw [Category.assoc, hcase]
        rw [this]; exact β.2
      have hQg : Q a.unop (α.1 ≫ ρ) := by
        apply hR φ.unop
        have : φ.unop ≫ (α.1 ≫ ρ) = β.1 := by rw [hcase]
        rw [this]; exact β.2
      rw [dite_eq_left hPg, dite_eq_left hQg]
      have e1 : (β:b.unop⟶T₂) = (φ.unop ≫ α.1) ≫ ρ := by rw [Category.assoc]; exact hcase
      have e2 : (β:b.unop⟶T₂) = φ.unop ≫ (α.1 ≫ ρ) := hcase
      rw [ite_eq_left e1, ite_eq_left e2]
    · have h1 : (∀ _ : P b.unop (φ.unop ≫ α.1),
          (if (β:b.unop⟶T₂) = (φ.unop ≫ α.1) ≫ ρ then (𝟙 A) else (0:A⟶A)) = 0) := by
        intro _
        rw [ite_eq_right]; intro h; exact hcase (by rw [h, Category.assoc])
      have h2 : (∀ _ : Q a.unop (α.1 ≫ ρ),
          (if (β:b.unop⟶T₂) = φ.unop ≫ (α.1 ≫ ρ) then (𝟙 A) else (0:A⟶A)) = 0) := by
        intro _
        rw [ite_eq_right]; intro h; exact hcase h
      by_cases hPg : P b.unop (φ.unop ≫ α.1)
      · rw [dite_eq_left hPg, h1 hPg]
        by_cases hQg : Q a.unop (α.1 ≫ ρ)
        · rw [dite_eq_left hQg, h2 hQg]
        · rw [dite_eq_right hQg]
      · rw [dite_eq_right hPg]
        by_cases hQg : Q a.unop (α.1 ≫ ρ)
        · rw [dite_eq_left hQg, h2 hQg]
        · rw [dite_eq_right hQg]

/-- The explicit model of the Eilenberg–MacLane object `K(A,k)` given by the rules of
[Stacks, Tag 0190](2)-(3): summands indexed by surjective monotone maps `[n] → [k]`, encoded as
`coversBelow k`. It is identified with `K(A, k) = i_{k!}U` (`eilenbergMacLane A k`) by
`CategoryTheory.SimplicialObject.EilenbergMacLane.eilenbergMacLaneIsoEmKAk`. -/
noncomputable abbrev emKAk (A : 𝒜) (k : ℕ) : SimplicialObject 𝒜 :=
  emObject A (SimplexCategory.mk k) (fun _ => coversBelow k) (coversBelow_hP k)

/-- The simplicial object `E` from Stacks 0192: summands indexed by monotone maps
`[n] → [k+1]` whose image is `[k]` or `[k+1]`, encoded as `coversBelow k`. -/
noncomputable abbrev emEobj (A : 𝒜) (k : ℕ) : SimplicialObject 𝒜 :=
  emObject A (SimplexCategory.mk (k + 1)) (fun _ => coversBelow k) (coversBelow_hP k)

/-- The standard order-preserving inclusion `[k] ↪ [k+1]` of the bottom `k+1` elements. -/
def bottomIncl (k : ℕ) : (SimplexCategory.mk k) ⟶ (SimplexCategory.mk (k + 1)) :=
  SimplexCategory.Hom.mk ⟨Fin.castSucc, fun _ _ h => by simpa using h⟩

/-- The bottom inclusion `[k] ↪ [k+1]` acts as `Fin.castSucc`. -/
@[simp]
theorem bottomIncl_toOrderHom_apply (k : ℕ) (i : Fin (k + 1)) :
    (bottomIncl k).toOrderHom i = i.castSucc := by
  rw [bottomIncl, SimplexCategory.Hom.toOrderHom_mk]
  rfl

/-- A map into `[k]` covers below `k` iff its composite with the bottom inclusion does. -/
private theorem coversBelow_comp_bottomIncl_iff {n : SimplexCategory} (k : ℕ) (α : n ⟶ .mk k) :
    coversBelow k (α ≫ bottomIncl k) ↔ coversBelow k α := by
  constructor
  · intro hα i hi
    have hmem := hα (Fin.castSucc i) (by simpa using hi)
    simp only [imageFinset, Finset.mem_image, Finset.mem_univ, true_and] at hmem ⊢
    obtain ⟨x, hx⟩ := hmem
    exact ⟨x, Fin.castSucc_inj.mp (by simpa using hx)⟩
  · intro hα i hi
    have hmem := hα ⟨i, by simpa [Nat.lt_succ_iff] using hi⟩ (by simpa using hi)
    simp only [imageFinset, Finset.mem_image, Finset.mem_univ, true_and] at hmem ⊢
    obtain ⟨x, hx⟩ := hmem
    exact ⟨x, by simp [hx]⟩

/-- A map into `[k + 1]` factoring through the bottom inclusion misses the top value. -/
private theorem not_coversBelow_comp_bottomIncl {n : SimplexCategory} (k : ℕ) (γ : n ⟶ .mk k) :
    ¬ coversBelow (k + 1) (γ ≫ bottomIncl k) := by
  intro h
  have hmem := h (Fin.last (k + 1)) (by simp)
  simp only [imageFinset, Finset.mem_image, Finset.mem_univ, true_and] at hmem
  obtain ⟨x, hx⟩ := hmem
  have hle : ((γ ≫ bottomIncl k).toOrderHom x : ℕ) ≤ k := by simpa using Fin.is_le _
  rw [hx] at hle
  simp at hle

/-- Postcomposition with the bottom inclusion is injective. -/
private theorem eq_of_comp_bottomIncl_eq {n : SimplexCategory} {k : ℕ} {α α' : n ⟶ .mk k}
    (h : α ≫ bottomIncl k = α' ≫ bottomIncl k) : α = α' := by
  have : Mono (bottomIncl k) :=
    SimplexCategory.mono_iff_injective.mpr (Fin.castSucc_injective _)
  exact (cancel_mono _).mp h

/-- The inclusion morphism `ι : K(A,k) → E`. Its `n`-th component embeds the summand of
`K(A,k)_n` indexed by a surjective `α : [n] → [k]` into the summand of `E_n` indexed by the
composite `α ≫ (bottom inclusion [k] ↪ [k+1])`, which has image `[k]`. -/
noncomputable def emIota (A : 𝒜) (k : ℕ) : emKAk A k ⟶ emEobj A k :=
  emRelabel A (SimplexCategory.mk k) (SimplexCategory.mk (k + 1))
    (fun _ => coversBelow k) (fun _ => coversBelow k)
    (coversBelow_hP k) (coversBelow_hP k) (bottomIncl k)
    (by
      intro n δ hδ i _
      have hi2 : (Fin.castSucc i : ℕ) ≤ k := by simp only [Fin.val_castSucc]; omega
      have hmem := hδ (Fin.castSucc i) hi2
      simp only [imageFinset, Finset.mem_image, Finset.mem_univ, true_and] at hmem ⊢
      obtain ⟨x, hx⟩ := hmem
      exact ⟨x, Fin.castSucc_inj.mp (by simpa using hx)⟩)
    (fun g δ h => coversBelow_of_precomp k g δ h)

/-- The `n`-th component of `ι`, as a biproduct matrix. -/
theorem emIota_app (A : 𝒜) (k : ℕ) (n : SimplexCategoryᵒᵖ) :
    (emIota A k).app n = biproduct.matrix
      (fun (α : {α : n.unop ⟶ SimplexCategory.mk k // coversBelow k α})
           (β : {α : n.unop ⟶ SimplexCategory.mk (k + 1) // coversBelow k α}) =>
        if β.1 = α.1 ≫ bottomIncl k then (𝟙 A) else (0 : A ⟶ A)) := by
  unfold emIota emRelabel
  rfl

/-- The projection morphism `π : E → K(A,k+1)`. Its `n`-th component projects `E_n` onto the
summands indexed by surjective `α : [n] → [k+1]` (the index set of `K(A,k+1)_n`), sending such
a summand by the identity and the summands of image `[k]` to zero. -/
noncomputable def emPi (A : 𝒜) (k : ℕ) : emEobj A k ⟶ emKAk A (k + 1) :=
  emRelabel A (SimplexCategory.mk (k + 1)) (SimplexCategory.mk (k + 1))
    (fun _ => coversBelow k) (fun _ => coversBelow (k + 1))
    (coversBelow_hP k) (coversBelow_hP (k + 1)) (𝟙 _)
    (by
      intro n δ hδ i hi
      rw [Category.comp_id] at hδ
      exact hδ i (by omega))
    (fun g δ h => coversBelow_of_precomp (k + 1) g δ h)

/-- The `n`-th component of `π`, as a biproduct matrix. -/
theorem emPi_app (A : 𝒜) (k : ℕ) (n : SimplexCategoryᵒᵖ) :
    (emPi A k).app n = biproduct.matrix
      (fun (β : {α : n.unop ⟶ SimplexCategory.mk (k + 1) // coversBelow k α})
           (γ : {α : n.unop ⟶ SimplexCategory.mk (k + 1) // coversBelow (k + 1) α}) =>
        if γ.1 = β.1 ≫ 𝟙 _ then (𝟙 A) else (0 : A ⟶ A)) := by
  unfold emPi emRelabel
  rfl

/-- In each degree `n` the composite `ι_n ≫ π_n : K(A,k)_n ⟶ K(A,k+1)_n` is zero. -/
theorem emIota_emPi_app_zero (A : 𝒜) (k : ℕ) (n : SimplexCategoryᵒᵖ) :
    (emIota A k).app n ≫ (emPi A k).app n = 0 := by
  rw [emIota_app, emPi_app, biproduct_matrix_comp]
  refine biproduct.hom_ext _ _ fun β => biproduct.hom_ext' _ _ fun γ => ?_
  simp only [biproduct.matrix_π, biproduct.ι_desc, Limits.comp_zero, Limits.zero_comp]
  rw [subtype_indicator_sum (coversBelow k) A A (γ.1 ≫ bottomIncl k)
    (fun x => if (β:n.unop ⟶ SimplexCategory.mk (k+1)) = (x:n.unop ⟶ SimplexCategory.mk (k+1)) ≫ 𝟙 _
      then (𝟙 A) else (0:A⟶A))]
  have hfalse : (β:n.unop ⟶ SimplexCategory.mk (k+1)) ≠ (γ.1 ≫ bottomIncl k) ≫ 𝟙 _ := by
    rw [Category.comp_id]
    exact fun heq => not_coversBelow_comp_bottomIncl k γ.1 (heq ▸ β.2)
  by_cases hc : coversBelow k (γ.1 ≫ bottomIncl k)
  · rw [dite_eq_left hc, ite_eq_right hfalse]
  · rw [dite_eq_right hc]

/-- The short complex `K(A,k) → E → K(A,k+1)` in the category of simplicial objects. The
composite `π ∘ ι` is zero. -/
@[implicit_reducible]
noncomputable def emShortComplex (A : 𝒜) (k : ℕ) : ShortComplex (SimplicialObject 𝒜) :=
  { X₁ := emKAk A k
    X₂ := emEobj A k
    X₃ := emKAk A (k + 1)
    f := emIota A k
    g := emPi A k
    zero := by
      ext n
      simp only [CategoryTheory.NatTrans.comp_app, Limits.zero_app]
      exact emIota_emPi_app_zero A k n }

/-- Degreewise retraction matrix `E_n ⟶ K(A,k)_n`: the transpose of the inclusion matrix of
`ι_n`. Sends the summand of `E_n` indexed by `β` by `𝟙` into the summand of `K(A,k)_n` indexed
by `α` precisely when `β = α ≫ bottomIncl k` (i.e. `β` factors through the bottom inclusion),
and by `0` otherwise. -/
noncomputable def retractionApp (A : 𝒜) (k : ℕ) (n : SimplexCategoryᵒᵖ) :
    (emEobj A k).obj n ⟶ (emKAk A k).obj n :=
  biproduct.matrix
    (fun (β : {α : n.unop ⟶ SimplexCategory.mk (k + 1) // coversBelow k α})
         (α : {α : n.unop ⟶ SimplexCategory.mk k // coversBelow k α}) =>
      if β.1 = α.1 ≫ bottomIncl k then (𝟙 A) else (0 : A ⟶ A))

/-- Degreewise section matrix `K(A,k+1)_n ⟶ E_n`: sends the summand of `K(A,k+1)_n` indexed by
a surjective `γ : [n] → [k+1]` by `𝟙` into the same-underlying summand `β = γ` of `E_n` (which
is admissible since `coversBelow (k+1) γ ⟹ coversBelow k γ`), and by `0` otherwise. -/
noncomputable def sectionApp (A : 𝒜) (k : ℕ) (n : SimplexCategoryᵒᵖ) :
    (emKAk A (k + 1)).obj n ⟶ (emEobj A k).obj n :=
  biproduct.matrix
    (fun (γ : {α : n.unop ⟶ SimplexCategory.mk (k + 1) // coversBelow (k + 1) α})
         (β : {α : n.unop ⟶ SimplexCategory.mk (k + 1) // coversBelow k α}) =>
      if β.1 = γ.1 then (𝟙 A) else (0 : A ⟶ A))

/-- The sum of two biproduct matrices is the biproduct matrix of the entrywise sum. -/
theorem biproduct_matrix_add {J K : Type} [Finite J] [Finite K]
    {C : Type*} [Category C] [Preadditive C] [HasFiniteBiproducts C] {A : C}
    (M N : (j : J) → (l : K) → A ⟶ A) :
    biproduct.matrix M + biproduct.matrix N
      = biproduct.matrix (fun j l => M j l + N j l) := by
  classical
  ext j l
  simp [Preadditive.comp_add]

/-- Degreewise partition identity `retractionApp ≫ ι_n + π_n ≫ sectionApp = 𝟙` on `E_n`. -/
theorem retractionApp_add_sectionApp_id (A : 𝒜) (k : ℕ) (n : SimplexCategoryᵒᵖ) :
    retractionApp A k n ≫ (emIota A k).app n + (emPi A k).app n ≫ sectionApp A k n
      = 𝟙 ((emEobj A k).obj n) := by
  rw [emIota_app, emPi_app, retractionApp, sectionApp, biproduct_matrix_comp,
    biproduct_matrix_comp, biproduct_matrix_add]
  have key : (biproduct.matrix fun
      (β : {α : n.unop ⟶ SimplexCategory.mk (k+1) // coversBelow k α})
      (β' : {α : n.unop ⟶ SimplexCategory.mk (k+1) // coversBelow k α}) =>
      (∑ x : {α : n.unop ⟶ SimplexCategory.mk k // coversBelow k α},
        (if β.1 = x.1 ≫ bottomIncl k then (𝟙 A) else (0:A⟶A)) ≫
          (if β'.1 = x.1 ≫ bottomIncl k then (𝟙 A) else (0:A⟶A))) +
      (∑ y : {α : n.unop ⟶ SimplexCategory.mk (k+1) // coversBelow (k+1) α},
        (if y.1 = β.1 ≫ 𝟙 _ then (𝟙 A) else (0:A⟶A)) ≫
          (if β'.1 = y.1 then (𝟙 A) else (0:A⟶A))))
      = biproduct.matrix
          (fun a b : {α : n.unop ⟶ SimplexCategory.mk (k+1) // coversBelow k α} =>
            if b = a then 𝟙 A else (0 : A ⟶ A)) := by
    congr 1
    ext β β'
    have hsum2 : (∑ y : {α : n.unop ⟶ SimplexCategory.mk (k+1) // coversBelow (k+1) α},
        (if y.1 = β.1 ≫ 𝟙 _ then (𝟙 A) else (0:A⟶A)) ≫
          (if β'.1 = y.1 then (𝟙 A) else (0:A⟶A)))
        = if h : coversBelow (k+1) β.1 then
            (if β'.1 = β.1 then (𝟙 A) else (0:A⟶A)) else 0 := by
      have := subtype_indicator_sum (coversBelow (k+1)) A A β.1
        (fun y => if β'.1 = (y:n.unop ⟶ SimplexCategory.mk (k+1)) then (𝟙 A) else (0:A⟶A))
      simp only [Category.comp_id] at this ⊢
      rw [← this]
    rw [hsum2]
    by_cases hβ : coversBelow (k+1) β.1
    · rw [dite_eq_left hβ]
      have hsum1 : (∑ x : {α : n.unop ⟶ SimplexCategory.mk k // coversBelow k α},
          (if β.1 = x.1 ≫ bottomIncl k then (𝟙 A) else (0:A⟶A)) ≫
            (if β'.1 = x.1 ≫ bottomIncl k then (𝟙 A) else (0:A⟶A))) = 0 := by
        apply Finset.sum_eq_zero
        intro x _
        rw [ite_eq_right, zero_comp]
        exact fun heq => not_coversBelow_comp_bottomIncl k x.1 (heq ▸ hβ)
      rw [hsum1, zero_add]
      by_cases h : β' = β
      · subst h; rw [ite_eq_left rfl, ite_eq_left rfl]
      · rw [ite_eq_right h, ite_eq_right]
        intro heq; exact h (Subtype.ext heq)
    · rw [dite_eq_right hβ, add_zero]
      have hlast : Fin.last (k+1) ∉ imageFinset β.1 := by
        intro hmem
        apply hβ
        intro i hi
        rcases Nat.lt_or_ge (i:ℕ) (k+1) with hik | hik
        · exact β.2 i (by omega)
        · have : i = Fin.last (k+1) := by
            apply Fin.ext; rw [Fin.val_last]; omega
          rw [this]; exact hmem
      have hne : ∀ i, β.1.toOrderHom i ≠ Fin.last (k+1) := by
        intro i hcon
        apply hlast
        simp only [imageFinset, Finset.mem_image, Finset.mem_univ, true_and]
        exact ⟨i, hcon⟩
      set α₀fun : Fin (n.unop.len + 1) → Fin (k + 1) :=
        fun i => (β.1.toOrderHom i).castPred (hne i) with hα₀fun
      have hα₀mono : Monotone α₀fun := by
        intro i j hij
        simp only [hα₀fun]
        rw [Fin.castPred_le_castPred_iff]
        exact β.1.toOrderHom.monotone.imp hij
      set α₀ : n.unop ⟶ SimplexCategory.mk k :=
        SimplexCategory.Hom.mk ⟨α₀fun, hα₀mono⟩ with hα₀
      have hfact : α₀ ≫ bottomIncl k = β.1 := by
        apply SimplexCategory.Hom.ext
        apply OrderHom.ext
        funext i
        simp [hα₀, hα₀fun]
      have hα₀adm : coversBelow k α₀ :=
        (coversBelow_comp_bottomIncl_iff k α₀).1 (hfact ▸ β.2)
      rw [Finset.sum_eq_single (⟨α₀, hα₀adm⟩ : {α : n.unop ⟶ SimplexCategory.mk k // coversBelow k
          α})]
      · rw [ite_eq_left (by rw [hfact]), Category.id_comp]
        by_cases h : β' = β
        · subst h
          rw [ite_eq_left (by rw [hfact]), ite_eq_left rfl]
        · rw [ite_eq_right h, ite_eq_right]
          intro heq
          exact h (Subtype.ext (by rw [heq, hfact]))
      · intro x _ hx
        rw [ite_eq_right, zero_comp]
        intro heq
        exact hx (Subtype.ext (eq_of_comp_bottomIncl_eq (by rw [← heq, hfact])))
      · simp
  rw [key]
  exact biproduct_matrix_id A

/-- Degreewise splitting axiom `ι_n ≫ retractionApp_n = 𝟙` on `K(A,k)_n`. -/
theorem emIota_retractionApp_id (A : 𝒜) (k : ℕ) (n : SimplexCategoryᵒᵖ) :
    (emIota A k).app n ≫ retractionApp A k n = 𝟙 ((emKAk A k).obj n) := by
  rw [emIota_app, retractionApp, biproduct_matrix_comp]
  have key : (biproduct.matrix fun (α : {α : n.unop ⟶ SimplexCategory.mk k // coversBelow k α})
      (α' : {α : n.unop ⟶ SimplexCategory.mk k // coversBelow k α}) =>
      ∑ x : {α : n.unop ⟶ SimplexCategory.mk (k + 1) // coversBelow k α},
        (if (x:n.unop ⟶ SimplexCategory.mk (k+1)) = α.1 ≫ bottomIncl k then (𝟙 A) else (0:A⟶A)) ≫
          (if (x:n.unop ⟶ SimplexCategory.mk (k+1)) = α'.1 ≫ bottomIncl k then (𝟙 A) else (0:A⟶A)))
      = biproduct.matrix (fun a b : {α : n.unop ⟶ SimplexCategory.mk k // coversBelow k α} =>
          if b = a then 𝟙 A else (0 : A ⟶ A)) := by
    congr 1
    ext α α'
    have hadm : coversBelow k (α.1 ≫ bottomIncl k) :=
      (coversBelow_comp_bottomIncl_iff k α.1).2 α.2
    rw [subtype_indicator_sum (coversBelow k) A A (α.1 ≫ bottomIncl k)
      (fun β => if (β:n.unop ⟶ SimplexCategory.mk (k+1)) = α'.1 ≫ bottomIncl k
        then (𝟙 A) else (0:A⟶A))]
    rw [dite_eq_left hadm]
    by_cases h : α' = α
    · subst h; rw [ite_eq_left rfl, ite_eq_left rfl]
    · rw [ite_eq_right h, ite_eq_right]
      intro heq
      exact h (Subtype.ext (eq_of_comp_bottomIncl_eq heq).symm)
  rw [key]
  exact biproduct_matrix_id A

/-- Degreewise splitting axiom `sectionApp_n ≫ π_n = 𝟙` on `K(A,k+1)_n`. -/
theorem sectionApp_emPi_id (A : 𝒜) (k : ℕ) (n : SimplexCategoryᵒᵖ) :
    sectionApp A k n ≫ (emPi A k).app n = 𝟙 ((emKAk A (k + 1)).obj n) := by
  rw [sectionApp, emPi_app, biproduct_matrix_comp]
  have key : (biproduct.matrix fun
      (γ : {α : n.unop ⟶ SimplexCategory.mk (k + 1) // coversBelow (k + 1) α})
      (γ' : {α : n.unop ⟶ SimplexCategory.mk (k + 1) // coversBelow (k + 1) α}) =>
      ∑ x : {α : n.unop ⟶ SimplexCategory.mk (k + 1) // coversBelow k α},
        (if (x:n.unop ⟶ SimplexCategory.mk (k+1)) = γ.1 then (𝟙 A) else (0:A⟶A)) ≫
          (if γ'.1 = (x:n.unop ⟶ SimplexCategory.mk (k+1)) ≫ 𝟙 _ then (𝟙 A) else (0:A⟶A)))
      = biproduct.matrix
          (fun a b : {α : n.unop ⟶ SimplexCategory.mk (k + 1) // coversBelow (k + 1) α} =>
            if b = a then 𝟙 A else (0 : A ⟶ A)) := by
    congr 1
    ext γ γ'
    have hadm : coversBelow k γ.1 := by
      intro i hi
      exact γ.2 i (by omega)
    rw [subtype_indicator_sum (coversBelow k) A A γ.1
      (fun β => if γ'.1 = (β:n.unop ⟶ SimplexCategory.mk (k+1)) ≫ 𝟙 _
        then (𝟙 A) else (0:A⟶A))]
    rw [dite_eq_left hadm]
    rw [Category.comp_id]
    by_cases h : γ' = γ
    · subst h; rw [ite_eq_left rfl, ite_eq_left rfl]
    · rw [ite_eq_right h, ite_eq_right]
      intro heq
      exact h (Subtype.ext heq)
  rw [key]
  exact biproduct_matrix_id A

/-- The splitting of the short complex obtained by evaluating `emShortComplex A k` in degree
`n`, with retraction `retractionApp A k n` and section `sectionApp A k n`. -/
noncomputable def emSplittingApp (A : 𝒜) (k : ℕ) (n : SimplexCategoryᵒᵖ) :
    ((emShortComplex A k).map ((CategoryTheory.evaluation _ _).obj n)).Splitting where
  r := retractionApp A k n
  s := sectionApp A k n
  f_r := emIota_retractionApp_id A k n
  s_g := sectionApp_emPi_id A k n
  id := retractionApp_add_sectionApp_id A k n

/-- The sequence `0 → emKAk A k → E → emKAk A (k + 1) → 0` of explicit models is term by term
split: for each degree `n` the short complex obtained by evaluating it at `[n]` admits a splitting
in `𝒜`. For [Stacks, Tag 0192] itself, about the Eilenberg–MacLane objects `eilenbergMacLane A k`
and `eilenbergMacLane A (k + 1)`, see
`eilenbergMacLaneShortComplex_shortExact_and_splitting`. -/
theorem emSplit (A : 𝒜) (k : ℕ) (n : SimplexCategoryᵒᵖ) :
    Nonempty
      (((emShortComplex A k).map ((CategoryTheory.evaluation _ _).obj n)).Splitting) :=
  ⟨emSplittingApp A k n⟩

/-- The map `ι : K(A,k) ⟶ E` is a monomorphism in each degree. -/
theorem emIota_app_mono (A : 𝒜) (k : ℕ) (n : SimplexCategoryᵒᵖ) :
    Mono ((emIota A k).app n) :=
  ((emSplit A k n).some).shortExact.mono_f

/-- The map `π : E ⟶ K(A,k+1)` is an epimorphism in each degree. -/
theorem emPi_app_epi (A : 𝒜) (k : ℕ) (n : SimplexCategoryᵒᵖ) :
    Epi ((emPi A k).app n) :=
  ((emSplit A k n).some).shortExact.epi_g

/-- The sequence `0 → emKAk A k → E → emKAk A (k + 1) → 0` of explicit models is a short exact
sequence of simplicial objects of `𝒜`. For [Stacks, Tag 0192] itself, about the Eilenberg–MacLane
objects `eilenbergMacLane A k` and `eilenbergMacLane A (k + 1)`, see
`eilenbergMacLaneShortComplex_shortExact_and_splitting`. -/
theorem emShortComplex_shortExact (A : 𝒜) (k : ℕ) :
    (emShortComplex A k).ShortExact := by
  have hmono : Mono (emIota A k) := by
    have := emIota_app_mono A k
    exact NatTrans.mono_of_mono_app _
  have hepi : Epi (emPi A k) := by
    have := emPi_app_epi A k
    exact NatTrans.epi_of_epi_app _
  have hexact : (emShortComplex A k).Exact := by
    rw [ShortComplex.exact_iff_isZero_homology, IsZero.iff_id_eq_zero]
    ext n
    have hzero : IsZero ((emShortComplex A k).map ((evaluation _ _).obj n)).homology := by
      rw [← ShortComplex.exact_iff_isZero_homology]
      exact ((emSplit A k n).some).shortExact.exact
    have hz : IsZero ((emShortComplex A k).homology.obj n) :=
      hzero.of_iso ((emShortComplex A k).mapHomologyIso ((evaluation _ _).obj n)).symm
    exact hz.eq_of_src _ _
  exact { exact := hexact, mono_f := hmono, epi_g := hepi }

end CategoryTheory.SimplicialObject.EilenbergMacLane

end

end
