module

public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.AlgebraicTopology.SimplicialSet.CategoryWithFibrations
public import Mathlib.AlgebraicTopology.SimplicialSet.KanComplex
public import StacksFrontier.AlgebraicTopology.SimplicialSet.TrivialKanFibration

/-!
# Kan fibrations

Kan fibrations of simplicial sets: composition, products, inverse limits of towers, and termwise
surjective morphisms of simplicial groups.
-/

/-!
## Kan fibrations

A morphism of simplicial sets `f : X ⟶ Y` is a *Kan fibration* when for every `n ≥ 1` and every
`0 ≤ k ≤ n` it has the right lifting property with respect to the horn inclusion
`Λ_k[n] ⊆ Δ[n]`: every commutative square

```
Λ_k[n]  ------→  X
  |              |
  |              |  f
  ↓              ↓
Δ[n]    ------→  Y
```

admits a diagonal filler `Δ[n] ⟶ X`. This file collects the closure properties of the class of
Kan fibrations and its first source of examples.

Kan fibrations are closed under composition: a square over `f ≫ g` is filled first through `g`,
and then, against the resulting lift, through `f`. They are stable under products, a lifting
problem against a product cone being solved componentwise. And a homomorphism of simplicial
groups all of whose components `X_n → Y_n` are surjective is a Kan fibration of underlying
simplicial sets. Concretely, in that last statement a square as displayed is a family
`x_i ∈ X_{n - 1}` (`i ≠ k`) with `d_i x_j = d_{j - 1} x_i` for `i < j`, `i, j ≠ k`, together with
`y ∈ Y_n` such that `d_i y = f(x_i)` for `i ≠ k`, and the filler is an `x ∈ X_n` with
`d_i x = x_i` for `i ≠ k` and `f(x) = y`. Translating the data by a preimage of `y` reduces the
problem to the case `Y = 0`, where it is the statement that a simplicial group is a Kan complex
(Moore's theorem).

### Main results

* `SSet.hasLiftingProperty_horn_ι_comp`: the composition of two Kan fibrations of
  simplicial sets is a Kan fibration.
* `SSet.modelCategoryQuillen.isStableUnderProductsOfShape_fibrations`: the class of Kan
  fibrations of simplicial sets is stable under products indexed by any type.
* `CategoryTheory.SimplicialObject.fibration_whiskerRight_forget_of_surjective`: a termwise
  surjective homomorphism of simplicial groups is a Kan fibration of underlying simplicial sets.

### References

* [Stacks, Tag 08NU](https://stacks.math.columbia.edu/tag/08NU)
* [Stacks, Tag 08NW](https://stacks.math.columbia.edu/tag/08NW)
* [Stacks, Tag 08NY](https://stacks.math.columbia.edu/tag/08NY)
* [Stacks, Tag 08NZ](https://stacks.math.columbia.edu/tag/08NZ)
* [Stacks, Tag 08P0](https://stacks.math.columbia.edu/tag/08P0)
-/

section

open CategoryTheory HomotopicalAlgebra Limits MorphismProperty SSet
  SSet.modelCategoryQuillen Simplicial

universe w u

namespace SSet

/-- **Stacks 08NW**.
The composition of two Kan fibrations is a Kan fibration: if `f : X ⟶ Y` and `g : Y ⟶ Z` are
morphisms of simplicial sets each having the right lifting property with respect to all horn
inclusions, then so does `f ≫ g`. -/
@[stacks 08NW "the source's lifting condition, one horn inclusion `Λ[n + 1, i].ι` of Tag 08NU at \
  a time; the same statement for the bundled predicate `HomotopicalAlgebra.Fibration` of the \
  Quillen model structure on `SSet` is upstream's multiplicativity of `fibrations SSet`"]
public theorem hasLiftingProperty_horn_ι_comp {X Y Z : SSet.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    (hf : ∀ (n : ℕ) (i : Fin (n + 2)), HasLiftingProperty Λ[n + 1, i].ι f)
    (hg : ∀ (n : ℕ) (i : Fin (n + 2)), HasLiftingProperty Λ[n + 1, i].ι g) :
    ∀ (n : ℕ) (i : Fin (n + 2)), HasLiftingProperty Λ[n + 1, i].ι (f ≫ g) :=
  fun n i => have := hf n i; have := hg n i; .of_comp_right g f _

end SSet

namespace SSet.modelCategoryQuillen

/-- **Stacks 08NV**.
Kan fibrations of simplicial sets are stable under arbitrary base change. Under
`fibrations_eq`, they are a right lifting class, and every right lifting class has this closure
property. -/
@[stacks 08NV]
public theorem isStableUnderBaseChange_fibrations :
    (fibrations SSet.{u}).IsStableUnderBaseChange := by
  rw [fibrations_eq]
  infer_instance

/-- **Stacks 08NY**.
A product of Kan fibrations is a Kan fibration: if `f i : X i ⟶ Y i` is a family of morphisms of
simplicial sets each having the right lifting property with respect to all horn inclusions, then so
does the induced morphism `∏ X i ⟶ ∏ Y i` between any products of the `X i` and the `Y i`. -/
@[stacks 08NY "Kan fibrations are Mathlib's fibrations for the Quillen model structure on \
  `SSet`, whose generating family `J` is the horn inclusions of Tag 08NU; stability under \
  products is stated for arbitrary product cones, the source's `∏ X_i → ∏ Y_i` being the case \
  of `Limits.Pi.map`"]
public instance isStableUnderProductsOfShape_fibrations (J : Type w) :
    (fibrations SSet.{u}).IsStableUnderProductsOfShape J := by
  rw [SSet.modelCategoryQuillen.fibrations_eq]
  infer_instance

end SSet.modelCategoryQuillen

namespace CategoryTheory.SimplicialObject

/-! ### The Yoneda correspondence, with values in the simplicial object -/

section Yoneda

variable {C : Type*} [Category C] {FC : C → C → Type*} {CC : C → Type u}
  [∀ X Y, FunLike (FC X Y) (CC X) (CC Y)] [ConcreteCategory C FC]

/-- The Yoneda correspondence for the underlying simplicial set `X ⋙ forget C` of a simplicial
object `X` in a concrete category `C`, taking values in the object `X _⦋n⦌` of `n`-simplices
itself rather than in the underlying type of the simplicial set: a map `Δ[n] ⟶ X ⋙ forget C` is
the same thing as an element of `X _⦋n⦌`. -/
public def yonedaEquivObj (X : SimplicialObject C) (n : ℕ) :
    (Δ[n] ⟶ X ⋙ forget C) ≃ ToType (X _⦋n⦌) :=
  SSet.yonedaEquiv

/-- Precomposing with the `j`-th coface map corresponds to applying the `j`-th face map. -/
public lemma δ_yonedaEquivObj {X : SimplicialObject C} {n : ℕ} (g : Δ[n + 1] ⟶ X ⋙ forget C)
    (j : Fin (n + 2)) :
    ConcreteCategory.hom (X.δ j) (yonedaEquivObj X (n + 1) g)
      = yonedaEquivObj X n (stdSimplex.δ j ≫ g) :=
  (stdSimplex.yonedaEquiv_δ_comp g j).symm

/-- Postcomposing with `f` corresponds to applying `f`. -/
public lemma app_yonedaEquivObj {X Y : SimplicialObject C} (f : X ⟶ Y) {n : ℕ}
    (g : Δ[n] ⟶ X ⋙ forget C) :
    ConcreteCategory.hom (f.app _) (yonedaEquivObj X n g)
      = yonedaEquivObj Y n (g ≫ Functor.whiskerRight f (forget C)) :=
  (SSet.yonedaEquiv_comp g (Functor.whiskerRight f (forget C))).symm

end Yoneda

section MooreHornFilling

variable {X Y : SimplicialObject AddGrpCat.{u}}

/-! ### The simplicial identities, applied to elements and indexed by natural numbers -/

/-- Elementwise form of an equality of two composites of morphisms of abelian groups. -/
private lemma comp_apply_congr {A B C D : AddGrpCat.{u}} {f₁ : A ⟶ B} {g₁ : B ⟶ D} {f₂ : A ⟶ C}
    {g₂ : C ⟶ D} (h : f₁ ≫ g₁ = f₂ ≫ g₂) (z : A) : g₁.hom (f₁.hom z) = g₂.hom (f₂.hom z) :=
  ConcreteCategory.congr_hom h z

/-- Elementwise form of the identity `f ≫ g = 𝟙 A` of morphisms of abelian groups. -/
private lemma comp_apply_of_comp_eq_id {A B : AddGrpCat.{u}} {f : A ⟶ B} {g : B ⟶ A}
    (h : f ≫ g = 𝟙 A) (z : A) : g.hom (f.hom z) = z :=
  ConcreteCategory.congr_hom h z

private lemma δ_δ_apply {m a b : ℕ} (hab : a < b) (hb : b < m + 3) (z : X _⦋m + 2⦌) :
    (X.δ (⟨a, by omega⟩ : Fin (m + 2))).hom ((X.δ ⟨b, hb⟩).hom z)
      = (X.δ (⟨b - 1, by omega⟩ : Fin (m + 2))).hom
          ((X.δ (⟨a, by omega⟩ : Fin (m + 3))).hom z) := by
  have h := comp_apply_congr
    (X.δ_comp_δ (i := (⟨a, by omega⟩ : Fin (m + 2))) (j := (⟨b - 1, by omega⟩ : Fin (m + 2)))
      (by grind)) z
  rw [show (⟨b, hb⟩ : Fin (m + 3)) = (⟨b - 1, by omega⟩ : Fin (m + 2)).succ from by
        ext; grind,
    show (⟨a, by omega⟩ : Fin (m + 3)) = (⟨a, by omega⟩ : Fin (m + 2)).castSucc from by ext; simp]
  exact h

private lemma δ_σ_apply_of_lt {m a p : ℕ} (hap : a < p) (hp : p < m + 2) (v : X _⦋m + 1⦌) :
    (X.δ (⟨a, by omega⟩ : Fin (m + 3))).hom ((X.σ ⟨p, hp⟩).hom v)
      = (X.σ (⟨p - 1, by omega⟩ : Fin (m + 1))).hom
          ((X.δ (⟨a, by omega⟩ : Fin (m + 2))).hom v) := by
  have h := comp_apply_congr
    (X.δ_comp_σ_of_le (i := (⟨a, by omega⟩ : Fin (m + 2))) (j := (⟨p - 1, by omega⟩ : Fin (m + 1)))
      (by grind)) v
  rw [show (⟨p, hp⟩ : Fin (m + 2)) = (⟨p - 1, by omega⟩ : Fin (m + 1)).succ from by
        ext; grind,
    show (⟨a, by omega⟩ : Fin (m + 3)) = (⟨a, by omega⟩ : Fin (m + 2)).castSucc from by ext; simp]
  exact h

private lemma δ_σ_apply_self {m p : ℕ} (hp : p < m + 2) (v : X _⦋m + 1⦌) :
    (X.δ (⟨p, by omega⟩ : Fin (m + 3))).hom ((X.σ ⟨p, hp⟩).hom v) = v := by
  rw [show (⟨p, by omega⟩ : Fin (m + 3)) = (⟨p, hp⟩ : Fin (m + 2)).castSucc from by ext; simp]
  exact comp_apply_of_comp_eq_id (X.δ_comp_σ_self (i := (⟨p, hp⟩ : Fin (m + 2)))) v

private lemma δ_σ_apply_succ {m p : ℕ} (hp : p < m + 2) (v : X _⦋m + 1⦌) :
    (X.δ (⟨p + 1, by omega⟩ : Fin (m + 3))).hom ((X.σ ⟨p, hp⟩).hom v) = v := by
  rw [show (⟨p + 1, by omega⟩ : Fin (m + 3)) = (⟨p, hp⟩ : Fin (m + 2)).succ from by ext; simp]
  exact comp_apply_of_comp_eq_id (X.δ_comp_σ_succ (i := (⟨p, hp⟩ : Fin (m + 2)))) v

private lemma δ_σ_apply_of_gt {m a p : ℕ} (hap : p + 1 < a) (ha : a < m + 3) (v : X _⦋m + 1⦌) :
    (X.δ (⟨a, ha⟩ : Fin (m + 3))).hom ((X.σ (⟨p, by omega⟩ : Fin (m + 2))).hom v)
      = (X.σ (⟨p, by omega⟩ : Fin (m + 1))).hom
          ((X.δ (⟨a - 1, by omega⟩ : Fin (m + 2))).hom v) := by
  have h := comp_apply_congr
    (X.δ_comp_σ_of_gt (i := (⟨a - 1, by omega⟩ : Fin (m + 2))) (j := (⟨p, by omega⟩ : Fin (m + 1)))
      (by grind)) v
  rw [show (⟨a, ha⟩ : Fin (m + 3)) = (⟨a - 1, by omega⟩ : Fin (m + 2)).succ from by
        ext; grind,
    show (⟨p, by omega⟩ : Fin (m + 2)) = (⟨p, by omega⟩ : Fin (m + 1)).castSucc from by ext; simp]
  exact h

/-- Both faces of a degenerate `1`-simplex are the vertex it is degenerate at. -/
private lemma δ_σ_zero_apply (X : SimplicialObject AddGrpCat.{u}) (j : Fin 2) (v : X _⦋0⦌) :
    (X.δ j).hom ((X.σ 0).hom v) = v := by
  fin_cases j
  · exact comp_apply_of_comp_eq_id (X.δ_comp_σ_self (i := (0 : Fin 1))) v
  · exact comp_apply_of_comp_eq_id (X.δ_comp_σ_succ (i := (0 : Fin 1))) v

/-! ### Simplicial subgroups -/

/-- A family of subgroups `K m ⊆ X_m` of the terms of a simplicial group, closed under all the
simplicial operators: a simplicial subgroup of `X`. -/
private structure IsSimplicialSubgroup (K : ∀ m : ℕ, AddSubgroup (X _⦋m⦌)) : Prop where
  /-- `K` is closed under every simplicial operator. -/
  map_mem : ∀ {m m' : ℕ} (g : (⦋m⦌ : SimplexCategory) ⟶ ⦋m'⦌) {a : X _⦋m'⦌},
    a ∈ K m' → (X.map g.op).hom a ∈ K m

private lemma IsSimplicialSubgroup.δ_mem {K : ∀ m : ℕ, AddSubgroup (X _⦋m⦌)}
    (hK : IsSimplicialSubgroup K) {m : ℕ} (j : Fin (m + 2)) {a : X _⦋m + 1⦌}
    (ha : a ∈ K (m + 1)) : (X.δ j).hom a ∈ K m :=
  hK.map_mem _ ha

private lemma IsSimplicialSubgroup.σ_mem {K : ∀ m : ℕ, AddSubgroup (X _⦋m⦌)}
    (hK : IsSimplicialSubgroup K) {m : ℕ} (j : Fin (m + 1)) {a : X _⦋m⦌} (ha : a ∈ K m) :
    (X.σ j).hom a ∈ K (m + 1) :=
  hK.map_mem _ ha

/-- The kernel of a homomorphism of simplicial groups is a simplicial subgroup. -/
private lemma isSimplicialSubgroup_ker (f : X ⟶ Y) :
    IsSimplicialSubgroup fun m => (f.app (Opposite.op ⦋m⦌)).hom.ker := by
  constructor
  intro m m' g a ha
  simp only [AddMonoidHom.mem_ker] at ha ⊢
  rw [NatTrans.naturality_apply f g.op, ha, map_zero]

/-! ### Horn data -/

/-- The compatibility relations of the faces of the horn `Λ[n + 2, k]`: the family
`x : ℕ → X _⦋n + 1⦌` satisfies `d_a x_b = d_{b - 1} x_a` for `a < b < n + 3` avoiding `k`. -/
private def IsHornFamily {n : ℕ} (k : ℕ) (x : ℕ → X _⦋n + 1⦌) : Prop :=
  ∀ (a b : ℕ) (hab : a < b) (hb : b < n + 3), a ≠ k → b ≠ k →
    (X.δ (⟨a, by omega⟩ : Fin (n + 2))).hom (x b)
      = (X.δ (⟨b - 1, by omega⟩ : Fin (n + 2))).hom (x a)

/-! ### Moore's horn filling -/

/-- Let `u` be an element of a simplicial subgroup `K` whose `j`-th faces are the prescribed `x_j`
for the indices `j` of `S`, all of which avoid `p` and `p + 1`, and let `a` be `p` or `p + 1`. Then
`u + s_p(-(d_a u) + x_a)` lies in `K`, its `a`-th face is `x_a`, and its faces at the indices of
`S` are again the `x_j`. -/
private lemma exists_correction {K : ∀ m : ℕ, AddSubgroup (X _⦋m⦌)}
    (hK : IsSimplicialSubgroup K) {n k : ℕ} {x : ℕ → X _⦋n + 1⦌}
    (hxK : ∀ j : ℕ, j < n + 3 → j ≠ k → x j ∈ K (n + 1)) (hx : IsHornFamily k x)
    {p a : ℕ} (hp : p < n + 2) (ha : a < n + 3) (hpa : a = p ∨ a = p + 1) (hak : a ≠ k)
    {S : ℕ → Prop} (hSk : ∀ j, S j → j ≠ k) (hS : ∀ j, S j → j < p ∨ p + 1 < j)
    {u : X _⦋n + 2⦌} (huK : u ∈ K (n + 2))
    (hu : ∀ (j : ℕ) (hj : j < n + 3), S j → (X.δ ⟨j, hj⟩).hom u = x j) :
    ∃ u' ∈ K (n + 2), (X.δ ⟨a, ha⟩).hom u' = x a ∧
      ∀ (j : ℕ) (hj : j < n + 3), S j → (X.δ ⟨j, hj⟩).hom u' = x j := by
  set v : X _⦋n + 1⦌ := -((X.δ ⟨a, ha⟩).hom u) + x a with hv
  refine ⟨u + (X.σ (⟨p, hp⟩ : Fin (n + 2))).hom v,
    add_mem huK (hK.σ_mem _ (add_mem (neg_mem (hK.δ_mem _ huK)) (hxK a ha hak))), ?_, ?_⟩
  · rw [map_add, show (X.δ ⟨a, ha⟩).hom ((X.σ ⟨p, hp⟩).hom v) = v from ?_]
    · exact add_neg_cancel_left _ _
    · rcases hpa with rfl | rfl
      · exact δ_σ_apply_self hp v
      · exact δ_σ_apply_succ hp v
  · intro j hj hjS
    rcases hS j hjS with hjp | hjp
    · have h0 : (X.δ (⟨j, by omega⟩ : Fin (n + 2))).hom v = 0 := by
        rw [hv, map_add, map_neg, δ_δ_apply (show j < a by omega) ha u, hu j (by omega) hjS,
          hx j a (by omega) ha (hSk j hjS) hak]
        simp
      rw [map_add, δ_σ_apply_of_lt hjp hp, h0, map_zero, add_zero]
      exact hu j hj hjS
    · have h0 : (X.δ (⟨j - 1, by omega⟩ : Fin (n + 2))).hom v = 0 := by
        rw [hv, map_add, map_neg, ← δ_δ_apply (show a < j by omega) hj u, hu j hj hjS,
          hx a j (by omega) hj hak (hSk j hjS)]
        simp
      rw [map_add, δ_σ_apply_of_gt hjp hj, h0, map_zero, add_zero]
      exact hu j hj hjS

/-- **Moore's theorem**, relative to a simplicial subgroup: horn data with values in a
simplicial subgroup `K` of `X` can be filled inside `K`. The absolute statement, that the
underlying simplicial set of a simplicial group is a Kan complex, is the case `K = ⊤`. -/
private lemma exists_filler_mem {K : ∀ m : ℕ, AddSubgroup (X _⦋m⦌)}
    (hK : IsSimplicialSubgroup K) {n k : ℕ} (hk : k < n + 3) {x : ℕ → X _⦋n + 1⦌}
    (hxK : ∀ j : ℕ, j < n + 3 → j ≠ k → x j ∈ K (n + 1)) (hx : IsHornFamily k x) :
    ∃ z ∈ K (n + 2), ∀ (j : ℕ) (hj : j < n + 3), j ≠ k → (X.δ ⟨j, hj⟩).hom z = x j := by
  have phase1 : ∀ r ≤ k, ∃ u ∈ K (n + 2),
      ∀ (j : ℕ) (hj : j < n + 3), j < r → (X.δ ⟨j, hj⟩).hom u = x j := by
    intro r
    induction r with
    | zero => exact fun _ => ⟨0, zero_mem _, fun j hj h => absurd h (by omega)⟩
    | succ r ih =>
      intro hr
      obtain ⟨u, huK, hu⟩ := ih (by omega)
      obtain ⟨u', hu'K, hu'r, hu'⟩ := exists_correction hK hxK hx (p := r) (a := r) (by omega)
        (by omega) (Or.inl rfl) (by omega) (S := (· < r)) (fun j hj => by omega)
        (fun j hj => Or.inl hj) huK hu
      exact ⟨u', hu'K, fun j hj hjr => by
        rcases Nat.lt_succ_iff_lt_or_eq.mp hjr with h | rfl
        · exact hu' j hj h
        · exact hu'r⟩
  have phase2 : ∀ s ≤ n + 2 - k, ∃ z ∈ K (n + 2),
      ∀ (j : ℕ) (hj : j < n + 3), j < k ∨ n + 2 - s < j → (X.δ ⟨j, hj⟩).hom z = x j := by
    intro s
    induction s with
    | zero =>
      intro _
      obtain ⟨u, huK, hu⟩ := phase1 k le_rfl
      exact ⟨u, huK, fun j hj h => hu j hj (by omega)⟩
    | succ s ih =>
      intro hs
      obtain ⟨z, hzK, hz⟩ := ih (by omega)
      obtain ⟨z', hz'K, hz'a, hz'⟩ := exists_correction hK hxK hx (p := n + 1 - s)
        (a := n + 2 - s) (by omega) (by omega) (Or.inr (by omega)) (by omega)
        (S := fun j => j < k ∨ n + 2 - s < j) (fun j hj => by omega) (fun j hj => by omega)
        hzK hz
      exact ⟨z', hz'K, fun j hj h => by
        rcases h with h | h
        · exact hz' j hj (Or.inl h)
        · rcases Nat.lt_or_ge j (n + 2 - s) with h' | h'
          · exact absurd h (by omega)
          · rcases Nat.eq_or_lt_of_le h' with rfl | h''
            · exact hz'a
            · exact hz' j hj (Or.inr h'')⟩
  obtain ⟨z, hzK, hz⟩ := phase2 (n + 2 - k) le_rfl
  exact ⟨z, hzK, fun j hj hjk => hz j hj (by omega)⟩

/-! ### Reduction of the lifting problem to the kernel -/

/-- The lifting problem for a horn `Λ[n + 2, k]`, solved at the level of elements: horn data `x_j`
(`j ≠ k`) in `X` and a `y` in `Y` with `d_j y = f(x_j)` admit a filler mapping to `y`. -/
private lemma exists_filler (f : X ⟶ Y) {n k : ℕ}
    (hf : Function.Surjective (f.app (Opposite.op ⦋n + 2⦌)).hom) (hk : k < n + 3)
    (x : ℕ → X _⦋n + 1⦌) (y : Y _⦋n + 2⦌) (hx : IsHornFamily k x)
    (hy : ∀ (j : ℕ) (hj : j < n + 3), j ≠ k → (f.app _).hom (x j) = (Y.δ ⟨j, hj⟩).hom y) :
    ∃ z : X _⦋n + 2⦌, (f.app _).hom z = y ∧
      ∀ (j : ℕ) (hj : j < n + 3), j ≠ k → (X.δ ⟨j, hj⟩).hom z = x j := by
  obtain ⟨w, hw⟩ := hf y
  set x' : ℕ → X _⦋n + 1⦌ :=
    Function.extend Fin.val (fun j : Fin (n + 3) => x j.val - (X.δ j).hom w) 0
  have hx'eq : ∀ (j : ℕ) (hj : j < n + 3), x' j = x j - (X.δ ⟨j, hj⟩).hom w := fun j hj =>
    Function.Injective.extend_apply Fin.val_injective _ 0 ⟨j, hj⟩
  obtain ⟨z, hzK, hz⟩ := exists_filler_mem (isSimplicialSubgroup_ker f) hk (x := x')
    (fun j hj hjk => by
      have hδ : (f.app _).hom ((X.δ ⟨j, hj⟩).hom w) = (Y.δ ⟨j, hj⟩).hom ((f.app _).hom w) :=
        NatTrans.naturality_apply f _ w
      simp [hx'eq j hj, hδ, hw, hy j hj hjk])
    (fun a b hab hb ha' hb' => by
      rw [hx'eq b hb, hx'eq a (by omega), map_sub, map_sub, hx a b hab hb ha' hb',
        δ_δ_apply hab hb w])
  simp only [AddMonoidHom.mem_ker] at hzK
  refine ⟨z + w, by rw [map_add, hw, hzK, zero_add], fun j hj hjk => ?_⟩
  rw [map_add, hz j hj hjk, hx'eq j hj, sub_add_cancel]

/-- The lifting problem for a horn `Λ[1, j]`, which is a single vertex, solved at the level of
elements: a vertex `x` of `X` and an edge `y` of `Y` with `d_j y = f(x)` admit an edge `z` of `X`
with `f(z) = y` and `d_j z = x`. -/
private lemma exists_filler_one (f : X ⟶ Y)
    (hf : Function.Surjective (f.app (Opposite.op ⦋1⦌)).hom) (j : Fin 2) (x : X _⦋0⦌)
    (y : Y _⦋1⦌) (hxy : (f.app _).hom x = (Y.δ j).hom y) :
    ∃ z : X _⦋1⦌, (f.app _).hom z = y ∧ (X.δ j).hom z = x := by
  obtain ⟨w, hw⟩ := hf y
  refine ⟨(X.σ 0).hom (x - (X.δ j).hom w) + w, ?_, ?_⟩
  · have hσ : ∀ a : X _⦋0⦌,
        (f.app _).hom ((X.σ (0 : Fin 1)).hom a) = (Y.σ 0).hom ((f.app _).hom a) :=
      fun a => NatTrans.naturality_apply f _ a
    have hδ : (f.app _).hom ((X.δ j).hom w) = (Y.δ j).hom ((f.app _).hom w) :=
      NatTrans.naturality_apply f _ w
    rw [map_add, hw, hσ, map_sub, hxy, hδ, hw, sub_self, map_zero, zero_add]
  · rw [map_add, δ_σ_zero_apply]
    exact sub_add_cancel _ _

/-- The horn data of a map out of `Λ[n + 1, i]`: the family of its faces, extended by zero to
an index in `ℕ`. -/
private noncomputable def hornData {n : ℕ} {i : Fin (n + 2)}
    (t : (Λ[n + 1, i] : SSet.{u}) ⟶ X ⋙ forget AddGrpCat.{u}) : ℕ → X _⦋n⦌ :=
  Function.extend Fin.val
    (fun j => if hji : j = i then 0 else yonedaEquivObj X n (horn.ι i j hji ≫ t)) 0

private lemma hornData_apply {n : ℕ} {i : Fin (n + 2)}
    (t : (Λ[n + 1, i] : SSet.{u}) ⟶ X ⋙ forget AddGrpCat.{u}) {j : Fin (n + 2)} (hj : j ≠ i) :
    hornData t j.val = yonedaEquivObj X n (horn.ι i j hj ≫ t) := by
  rw [hornData, Function.Injective.extend_apply Fin.val_injective _ 0 j]
  simp [hj]

/-- The faces of a map out of a horn satisfy the horn compatibility relations. -/
private lemma isHornFamily_hornData {n : ℕ} {i : Fin (n + 3)}
    (t : (Λ[n + 2, i] : SSet.{u}) ⟶ X ⋙ forget AddGrpCat.{u}) :
    IsHornFamily i.val (hornData t) := by
  intro a b hab hb ha' hb'
  have hA : (⟨a, by omega⟩ : Fin (n + 3)) ≠ i := fun h => ha' (by rw [← h])
  have hB : (⟨b, hb⟩ : Fin (n + 3)) ≠ i := fun h => hb' (by rw [← h])
  have h2 := (SSet.horn.IsCompatible.of_hom t).δ_pred_comp ⟨a, by omega⟩ ⟨b, hb⟩ hA hB
    (by grind)
  rw [show (⟨b, hb⟩ : Fin (n + 3)).pred (by grind)
        = (⟨b - 1, by omega⟩ : Fin (n + 2)) from by ext; simp,
    show (⟨a, by omega⟩ : Fin (n + 3)).castPred (by grind)
        = (⟨a, by omega⟩ : Fin (n + 2)) from by ext; simp] at h2
  rw [hornData_apply t hB, hornData_apply t hA, δ_yonedaEquivObj, δ_yonedaEquivObj, h2]

end MooreHornFilling

/-- **Stacks 08P0**.
A termwise surjective homomorphism of simplicial groups is a Kan fibration: if `f : X ⟶ Y` is a
morphism of simplicial groups such that `X_n → Y_n` is surjective for every `n`, then the induced
morphism of underlying simplicial sets has the right lifting property with respect to all horn
inclusions. -/
@[stacks 08P0 "stated for simplicial groups written additively, commutativity being unused by \
  the source's argument (which reduces to Tag 08NZ, a statement about simplicial groups); the \
  source's simplicial abelian groups are the case of \
  `Functor.whiskerRight f (forget₂ AddCommGrpCat AddGrpCat)`, whose conclusion is the same term \
  by `rfl`. Kan fibrations are Mathlib's fibrations for the Quillen model structure on `SSet`, \
  whose generating family `J` is the horn inclusions of Tag 08NU"]
public theorem fibration_whiskerRight_forget_of_surjective
    {X Y : SimplicialObject AddGrpCat.{u}} (f : X ⟶ Y)
    (hf : ∀ n : SimplexCategoryᵒᵖ, Function.Surjective (f.app n).hom) :
    Fibration (Functor.whiskerRight f (forget AddGrpCat.{u})) := by
  rw [SSet.modelCategoryQuillen.fibration_iff]
  intro A B g hg
  simp only [J, MorphismProperty.iSup_iff] at hg
  obtain ⟨n, ⟨i⟩⟩ := hg
  -- `X` and `Y` also name the source and target of the horn inclusion; discarding them restores
  -- the two simplicial groups as the meaning of `X` and `Y`
  clear X Y
  refine ⟨fun {t u} sq ↦ ?_⟩
  have hcomm : ∀ (j : Fin (n + 2)) (hj : j ≠ i),
      (f.app _).hom (hornData t j.val) = (Y.δ j).hom (yonedaEquivObj Y (n + 1) u) := by
    intro j hj
    rw [hornData_apply t hj, app_yonedaEquivObj, δ_yonedaEquivObj]
    congr 1
    rw [Category.assoc, sq.w, ← Category.assoc, horn.ι_ι]
  have main : ∃ z : X _⦋n + 1⦌, (f.app _).hom z = yonedaEquivObj Y (n + 1) u ∧
      ∀ (j : Fin (n + 2)) (hj : j ≠ i), (X.δ j).hom z = hornData t j.val := by
    obtain _ | m := n
    · have hrev : i.rev ≠ i := by fin_cases i <;> decide
      obtain ⟨z, hz, hzδ⟩ := exists_filler_one f (hf _) i.rev _ _ (hcomm i.rev hrev)
      refine ⟨z, hz, fun j hj => ?_⟩
      obtain rfl : j = i.rev := by revert hj; fin_cases i <;> fin_cases j <;> decide
      exact hzδ
    · obtain ⟨z, hz, hzδ⟩ := exists_filler f (hf _) i.isLt (hornData t) _
        (isHornFamily_hornData t) (fun j hj hjk => hcomm ⟨j, hj⟩ fun h => hjk (by rw [← h]))
      exact ⟨z, hz, fun j hj => hzδ j.val j.isLt fun h => hj (by ext; exact h)⟩
  obtain ⟨z, hz, hzδ⟩ := main
  refine ⟨⟨{ l := (yonedaEquivObj X (n + 1)).symm z, fac_left := ?_, fac_right := ?_ }⟩⟩
  · refine horn.hom_ext' (fun j hj ↦ ?_)
    rw [← Category.assoc, horn.ι_ι]
    apply (yonedaEquivObj X n).injective
    rw [← δ_yonedaEquivObj, Equiv.apply_symm_apply, hzδ j hj, hornData_apply]
  · apply (yonedaEquivObj Y (n + 1)).injective
    rwa [← app_yonedaEquivObj, Equiv.apply_symm_apply]

end CategoryTheory.SimplicialObject

end

/-!
## Inverse limits of towers of Kan fibrations

A morphism `f : X ⟶ Y` of simplicial sets is a *Kan fibration* if it has the right lifting property
against every horn inclusion `Λ[n + 1, i].ι : Λ[n + 1, i] ⟶ Δ[n + 1]`, that is, if every
commutative square whose left edge is such an inclusion and whose right edge is `f` admits a
diagonal filler `Δ[n + 1] ⟶ X` making both triangles commute. The indices `n + 1 ≥ 1` and
`i : Fin (n + 2)` range over all horns.

A tower `⋯ → U² → U¹ → U⁰` of simplicial sets is a functor `F : ℕᵒᵖ ⥤ SSet`, with
`Uᵗ = F.obj (op t)` and transition maps the images of the arrows of `ℕᵒᵖ`; its inverse limit
`U = limₜ Uᵗ` is `limit F`, computed levelwise, and the canonical projection `U ⟶ U⁰` is
`limit.π F (op 0)`. If every transition map `Uᵗ⁺¹ ⟶ Uᵗ` is a Kan fibration, then so is that
projection.

### Main results

* `SSet.fibration_limit_π_zero`: if every transition map of a tower `F : ℕᵒᵖ ⥤ SSet` is a Kan
  fibration, then the projection `limit F ⟶ F.obj (op 0)` from the inverse limit is a Kan
  fibration.

### Implementation notes

Kan fibrations are Mathlib's fibrations `HomotopicalAlgebra.Fibration` for the Quillen model
structure on `SSet`, that is, the right lifting class of the family `J` of horn inclusions, and
the statement is the case `W = J` of `CategoryTheory.MorphismProperty.rlp_limit_π_zero`.

### References

* [Stacks, Tag 08NU](https://stacks.math.columbia.edu/tag/08NU)
* [Stacks, Tag 08NX](https://stacks.math.columbia.edu/tag/08NX)
-/

section

@[expose] public section

open CategoryTheory Limits HomotopicalAlgebra SSet.modelCategoryQuillen

namespace SSet

/-- **Stacks 08NX**.
Let `F : ℕᵒᵖ ⥤ SSet` be a tower `⋯ → U² → U¹ → U⁰` of simplicial sets each of whose transition
morphisms `Uᵗ⁺¹ ⟶ Uᵗ` is a Kan fibration. Then the canonical projection
`limit F ⟶ U⁰ = F.obj (op 0)` from the inverse limit to the bottom term is a Kan fibration. -/
@[stacks 08NX "Kan fibrations are Mathlib's fibrations for the Quillen model structure on \
  `SSet`, whose generating family `J` is the horn inclusions of Tag 08NU"]
theorem fibration_limit_π_zero (F : ℕᵒᵖ ⥤ SSet)
    (hF : ∀ t : ℕ, Fibration (F.map (homOfLE (Nat.le_succ t)).op)) :
    Fibration (limit.π F (Opposite.op 0)) :=
  (fibration_iff _).2 (J.rlp_limit_π_zero F fun t ↦ (fibration_iff _).1 (hF t))

end SSet

end

end
