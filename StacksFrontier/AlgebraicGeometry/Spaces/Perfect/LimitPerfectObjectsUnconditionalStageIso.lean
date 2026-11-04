module

public import StacksFrontier.CategoryTheory.PullbackData.LimitHomSystem

/-!
# Descending an isomorphism from the vertex to a stage, for a system over a base

Let `P` be a pullback pseudofunctor datum and let `S` be a
`CategoryTheory.PullbackData.LimitSystem` over a base `b`: stages `T_j` with structure morphisms
`k_j : T_j ⟶ b`, transition morphisms over `b` that compose, and a vertex `T` with projections
`p_j : T ⟶ T_j` over `b`.  For two objects `X`, `Y` of `D b` the datum gives the system of
morphism sets `Hom(k_j^*X, k_j^*Y)` with its maps `CategoryTheory.PullbackData.LimitSystem.trans`
between stages and `…LimitSystem.projHom` to `Hom(k^*X, k^*Y)`, and
`…LimitSystem.IsColim` is the assertion that the latter is the filtered colimit of the former.

Given that assertion in the four orders `(X, Y)`, `(Y, X)`, `(X, X)` and `(Y, Y)`, every
isomorphism `k^*X ≅ k^*Y` at the vertex is the image of an isomorphism `k_j^*X ≅ k_j^*Y` at some
stage.

## Main results

* `CategoryTheory.PullbackData.LimitSystem.exists_stageIso_of_projHom_eq`: a morphism at a stage
  whose image at the vertex is invertible, presented together with a candidate inverse at the
  same stage, becomes invertible at a later stage.
* `CategoryTheory.PullbackData.LimitSystem.exists_stageIso_of_isColim`: an isomorphism at the
  vertex descends to an isomorphism at a stage.
* `CategoryTheory.PullbackData.LimitSystem.exists_stageIso_of_limitIso`: the same with the
  isomorphism presented as a pair of isomorphisms `k^*X ≅ E` and `k^*Y ≅ E` with a common target.
* `CategoryTheory.PullbackData.LimitSystem.exists_le_stageIso_of_isColim`: the same at a stage
  beyond two prescribed ones.
* `CategoryTheory.PullbackData.factorHom_morphism_id`, `…factorHom_morphism_comp`: the map
  attached to a factorisation is compatible with identities and with composition of morphism
  sets, hence so are `…LimitSystem.trans` and `…LimitSystem.projHom`.

## Implementation notes

The datum is not assumed coherent, so the transition maps of a system are not known to be
functorial in the index: the composite of the transitions `k ≤ l` and `l ≤ n` need not be the
transition `k ≤ n` (that is `CategoryTheory.PullbackData.LimitSystem.trans_trans`, which takes
`CategoryTheory.PullbackData.IsCoherent`).  The arguments never compare a composite of two
transitions with a single one.

## References

* [Stacks Project, Lemma 75.24.3 (Tag 09RJ)](https://stacks.math.columbia.edu/tag/09RJ)
* [Stacks Project, Situation 75.24.1 (Tag 09RH)](https://stacks.math.columbia.edu/tag/09RH)
* [Stacks Project, Lemma 75.24.2 (Tag 09RI)](https://stacks.math.columbia.edu/tag/09RI)
* [Stacks Project, Lemma 75.10.8 (Tag 08HB)](https://stacks.math.columbia.edu/tag/08HB)
-/


@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe w v₁ u₁ v₂ u₂

namespace CategoryTheory.PullbackData

variable {A : Type u₁} [Category.{v₁} A] {D : A → Type u₂} [∀ a, Category.{v₂} (D a)]
  {P : PullbackData A D}

/-! ### The map attached to a factorisation respects composition and identities -/

section Factor

variable {a b c : A}

/-- **The map attached to a factorisation sends an identity to an identity.** -/
theorem factorHom_morphism_id {f : a ⟶ b} {g : b ⟶ c} {k : a ⟶ c} (h : f ≫ g = k) (X : D c) :
    P.factorHom h (𝟙 ((P.pull g).obj X)) = 𝟙 ((P.pull k).obj X) := by
  have hid : (P.pull f).map (𝟙 ((P.pull g).obj X)) = 𝟙 ((P.pull g ⋙ P.pull f).obj X) :=
    (P.pull f).map_id _
  simp only [factorHom, Functor.conjHom, hid, Category.id_comp, Iso.hom_inv_id_app]

/-- **The map attached to a factorisation respects composition.** -/
theorem factorHom_morphism_comp {f : a ⟶ b} {g : b ⟶ c} {k : a ⟶ c} (h : f ≫ g = k)
    {X Y Z : D c} (φ : (P.pull g).obj X ⟶ (P.pull g).obj Y)
    (ψ : (P.pull g).obj Y ⟶ (P.pull g).obj Z) :
    P.factorHom h (φ ≫ ψ) = P.factorHom h φ ≫ P.factorHom h ψ := by
  simp only [factorHom, Functor.conjHom, Functor.map_comp, Category.assoc,
    Iso.inv_hom_id_app_assoc]

end Factor

namespace LimitSystem

variable {b : A} {J : Type w} [Preorder J] {S : LimitSystem (A := A) b J}

/-- **The transition map of the system of morphism sets sends an identity to an identity.** -/
theorem trans_morphism_id (X : D b) {i j : J} (h : i ≤ j) :
    S.trans P X X i j h (𝟙 ((P.pull (S.toBase i)).obj X)) = 𝟙 ((P.pull (S.toBase j)).obj X) :=
  factorHom_morphism_id _ X

/-- **The transition map of the system of morphism sets respects composition.** -/
theorem trans_morphism_comp {X Y Z : D b} {i j : J} (h : i ≤ j)
    (φ : (P.pull (S.toBase i)).obj X ⟶ (P.pull (S.toBase i)).obj Y)
    (ψ : (P.pull (S.toBase i)).obj Y ⟶ (P.pull (S.toBase i)).obj Z) :
    S.trans P X Z i j h (φ ≫ ψ) = S.trans P X Y i j h φ ≫ S.trans P Y Z i j h ψ :=
  factorHom_morphism_comp _ φ ψ

/-- **The map to the vertex sends an identity to an identity.** -/
theorem projHom_morphism_id (X : D b) (j : J) :
    S.projHom P X X j (𝟙 ((P.pull (S.toBase j)).obj X)) =
      𝟙 ((P.pull S.limitToBase).obj X) :=
  factorHom_morphism_id _ X

/-- **The map to the vertex respects composition.** -/
theorem projHom_morphism_comp {X Y Z : D b} (j : J)
    (φ : (P.pull (S.toBase j)).obj X ⟶ (P.pull (S.toBase j)).obj Y)
    (ψ : (P.pull (S.toBase j)).obj Y ⟶ (P.pull (S.toBase j)).obj Z) :
    S.projHom P X Z j (φ ≫ ψ) = S.projHom P X Y j φ ≫ S.projHom P Y Z j ψ :=
  factorHom_morphism_comp _ φ ψ

/-! ### Descending an isomorphism to a stage -/

/-- **A morphism at a stage whose image at the vertex is invertible, presented with a candidate
inverse at the same stage, becomes invertible at a later stage.**  Let `a : k_j^*X ⟶ k_j^*Y` and
`b : k_j^*Y ⟶ k_j^*X` be morphisms at a stage `j` whose images in `Hom(k^*X, k^*Y)` and
`Hom(k^*Y, k^*X)` are `e` and `e⁻¹`.  Then `a` and `b` become mutually inverse at some stage
`m ≥ j`, and the resulting isomorphism still has image `e`. -/
theorem exists_stageIso_of_projHom_eq {X Y : D b}
    (hXY : S.IsColim P X Y) (hYX : S.IsColim P Y X)
    (hXX : S.IsColim P X X) (hYY : S.IsColim P Y Y)
    (e : (P.pull S.limitToBase).obj X ≅ (P.pull S.limitToBase).obj Y) (k : J)
    (a : (P.pull (S.toBase k)).obj X ⟶ (P.pull (S.toBase k)).obj Y)
    (c : (P.pull (S.toBase k)).obj Y ⟶ (P.pull (S.toBase k)).obj X)
    (ha : S.projHom P X Y k a = e.hom) (hc : S.projHom P Y X k c = e.inv) :
    ∃ (m : J) (φ : (P.pull (S.toBase m)).obj X ≅ (P.pull (S.toBase m)).obj Y),
      S.projHom P X Y m φ.hom = e.hom := by
  obtain ⟨l, hkl, hl⟩ := Stacks.IsStagesColimit.exists_trans_eq hXX k (a ≫ c) (𝟙 _) (by
    rw [projHom_morphism_comp, projHom_morphism_id, ha, hc, e.hom_inv_id])
  rw [trans_morphism_comp, trans_morphism_id] at hl
  obtain ⟨m, hlm, hm⟩ := Stacks.IsStagesColimit.exists_trans_eq hYY l
    (S.trans P Y X k l hkl c ≫ S.trans P X Y k l hkl a) (𝟙 _) (by
      rw [projHom_morphism_comp, projHom_morphism_id,
        Stacks.IsStagesColimit.ι_trans hYX k l hkl c, hc,
        Stacks.IsStagesColimit.ι_trans hXY k l hkl a, ha, e.inv_hom_id])
  rw [trans_morphism_comp, trans_morphism_id] at hm
  have h1 := congrArg (S.trans P X X l m hlm) hl
  rw [trans_morphism_comp, trans_morphism_id] at h1
  refine ⟨m, ⟨_, _, h1, hm⟩, ?_⟩
  rw [Stacks.IsStagesColimit.ι_trans hXY l m hlm _,
    Stacks.IsStagesColimit.ι_trans hXY k l hkl a, ha]

/-- **An isomorphism at the vertex descends to an isomorphism at a stage.**  Let `X` and `Y` be
objects of `D b` whose systems of morphism sets along `S` have the colimit property in the four
orders `(X, Y)`, `(Y, X)`, `(X, X)` and `(Y, Y)`.  Then every isomorphism `e : k^*X ≅ k^*Y` at
the vertex is the image, under `CategoryTheory.PullbackData.LimitSystem.projHom`, of an
isomorphism `k_j^*X ≅ k_j^*Y` at some stage `j`. -/
theorem exists_stageIso_of_isColim [IsDirected J (· ≤ ·)] {X Y : D b}
    (hXY : S.IsColim P X Y) (hYX : S.IsColim P Y X)
    (hXX : S.IsColim P X X) (hYY : S.IsColim P Y Y)
    (e : (P.pull S.limitToBase).obj X ≅ (P.pull S.limitToBase).obj Y) :
    ∃ (j : J) (φ : (P.pull (S.toBase j)).obj X ≅ (P.pull (S.toBase j)).obj Y),
      S.projHom P X Y j φ.hom = e.hom := by
  obtain ⟨i, g, hg⟩ := Stacks.IsStagesColimit.exists_stage hXY e.hom
  obtain ⟨i', g', hg'⟩ := Stacks.IsStagesColimit.exists_stage hYX e.inv
  obtain ⟨k, hik, hik'⟩ := directed_of (· ≤ ·) i i'
  exact exists_stageIso_of_projHom_eq hXY hYX hXX hYY e k
    (S.trans P X Y i k hik g) (S.trans P Y X i' k hik' g')
    (by rw [Stacks.IsStagesColimit.ι_trans hXY i k hik g, hg])
    (by rw [Stacks.IsStagesColimit.ι_trans hYX i' k hik' g', hg'])

/-- **The comparison isomorphism at a stage, from two isomorphisms with a common target.**  Let
`X` and `Y` be objects of `D b` satisfying the colimit assertion in the four orders, and let
`α : k^*X ≅ E` and `β : k^*Y ≅ E` be isomorphisms with a common object `E` of `D S.limit`.  Then
at some stage `j` there is an isomorphism `k_j^*X ≅ k_j^*Y` whose image at the vertex is
`β⁻¹ ∘ α`. -/
theorem exists_stageIso_of_limitIso [IsDirected J (· ≤ ·)] {X Y : D b}
    (hXY : S.IsColim P X Y) (hYX : S.IsColim P Y X)
    (hXX : S.IsColim P X X) (hYY : S.IsColim P Y Y)
    (E : D S.limit) (α : (P.pull S.limitToBase).obj X ≅ E)
    (β : (P.pull S.limitToBase).obj Y ≅ E) :
    ∃ (j : J) (φ : (P.pull (S.toBase j)).obj X ≅ (P.pull (S.toBase j)).obj Y),
      S.projHom P X Y j φ.hom = α.hom ≫ β.inv :=
  exists_stageIso_of_isColim hXY hYX hXX hYY (α ≪≫ β.symm)

/-- **An isomorphism at the vertex descends to an isomorphism at a stage beyond two prescribed
ones.**  Under the hypotheses of
`CategoryTheory.PullbackData.LimitSystem.exists_stageIso_of_isColim`, for any two stages `i` and
`i'` every isomorphism `e : k^*X ≅ k^*Y` at the vertex is the image of an isomorphism
`k_j^*X ≅ k_j^*Y` at some stage `j ≥ i, i'`. -/
theorem exists_le_stageIso_of_isColim [IsDirected J (· ≤ ·)] {X Y : D b}
    (hXY : S.IsColim P X Y) (hYX : S.IsColim P Y X)
    (hXX : S.IsColim P X X) (hYY : S.IsColim P Y Y)
    (e : (P.pull S.limitToBase).obj X ≅ (P.pull S.limitToBase).obj Y) (i i' : J) :
    ∃ (j : J) (_ : i ≤ j) (_ : i' ≤ j)
      (φ : (P.pull (S.toBase j)).obj X ≅ (P.pull (S.toBase j)).obj Y),
      S.projHom P X Y j φ.hom = e.hom := by
  obtain ⟨k, hik, hik'⟩ := directed_of (· ≤ ·) i i'
  obtain ⟨m, φ, hφ⟩ := exists_stageIso_of_isColim hXY hYX hXX hYY e
  obtain ⟨n, hkn, hmn⟩ := directed_of (· ≤ ·) k m
  refine ⟨n, hik.trans hkn, hik'.trans hkn, ⟨S.trans P X Y m n hmn φ.hom,
    S.trans P Y X m n hmn φ.inv, ?_, ?_⟩, ?_⟩
  · rw [← trans_morphism_comp, φ.hom_inv_id, trans_morphism_id]
  · rw [← trans_morphism_comp, φ.inv_hom_id, trans_morphism_id]
  · rw [Stacks.IsStagesColimit.ι_trans hXY m n hmn φ.hom, hφ]

end LimitSystem

end CategoryTheory.PullbackData

end
