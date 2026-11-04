module

public import StacksFrontier.RingTheory.LocalCohomology.StrictProRepresentatives
public import StacksFrontier.RingTheory.Module.AdicSystem.Homology

/-!
# A strict pro-isomorphism is a pro-isomorphism

The strict pro-category of [Stacks, Tag 0GA5] has fewer morphisms than the category of
pro-objects: a morphism is represented by maps `X_{n+c} ⟶ Y_n` with a shift `c` independent of
`n`.  This file records that an isomorphism of the strict pro-category gives a pro-isomorphism in
the explicit form `_root_.InverseSequence.ProIso` used elsewhere in the library.

## Main results

* `Stacks.LocalCohomology.nonempty_proIso_of_nonempty_iso_proObj`: two inverse sequences that
  are isomorphic in the strict pro-category are pro-isomorphic.

## References

* [Stacks Project, Tag 0GA5](https://stacks.math.columbia.edu/tag/0GA5)
-/

@[expose] public section

open CategoryTheory Opposite

namespace Stacks.LocalCohomology

universe v u

variable {C : Type u} [Category.{v} C]

/-- A strict pro-morphism `f` with shift `a`, followed by a strict pro-morphism `g` with shift
`b`, which is equivalent to the identity at the shift `d` from the level `N`: the round trip of
the components is a structural map from the level `n + d`, for `n ≥ N`. -/
theorem map_comp_hom_app_eq_of_equivalent_id {X Y : Functor ℕᵒᵖ C} (f : StrictProHomRep X Y)
    (g : StrictProHomRep Y X) {d N : ℕ} (hd : g.shift + f.shift ≤ d)
    (H : ∀ n, N ≤ n → X.map (opHomOfLE (Nat.add_le_add_left hd n)) ≫ (f.comp g).hom.app (op n) =
      X.map (opHomOfLE (Nat.add_le_add_left (Nat.zero_le d) n)) ≫
        (StrictProHomRep.id X).hom.app (op n))
    (n : ℕ) (hn : N ≤ n) :
    X.map (opHomOfLE (show n + g.shift + f.shift ≤ n + d by omega)) ≫
        f.hom.app (op (n + g.shift)) ≫ g.hom.app (op n) =
      X.map (opHomOfLE (show n ≤ n + d by omega)) := by
  have h := H n hn
  have e : X.map (opHomOfLE (le_refl (n + g.shift + f.shift))) = 𝟙 _ := by
    rw [inverseSequence_map_eq X _ (𝟙 _), X.map_id]
  rw [StrictProHomRep.map_comp_hom_app f g n (n + d) f.shift _ le_rfl
    (show n + g.shift + f.shift ≤ n + d by omega), StrictProHomRep.id_hom_app,
    e, Category.id_comp] at h
  exact h.trans (Category.comp_id _)

/-- The naturality of a strict pro-morphism, written with the structural maps. -/
theorem StrictProHomRep.app_comp_map {X Y : Functor ℕᵒᵖ C} (f : StrictProHomRep X Y) {i j : ℕ}
    (h : i ≤ j) :
    f.hom.app (op j) ≫ Y.map (opHomOfLE h) =
      X.map (opHomOfLE (Nat.add_le_add_right h f.shift)) ≫ f.hom.app (op i) := by
  have hnat := f.hom.naturality (opHomOfLE h)
  rw [shiftedInverseSequence_map X f.shift h (Nat.add_le_add_right h f.shift)] at hnat
  exact hnat.symm

/-- The round trip of two strict pro-morphisms inverse to each other from the level `K` on. -/
theorem StrictProHomRep.round_trip {X Y : Functor ℕᵒᵖ C} (f : StrictProHomRep X Y)
    (g : StrictProHomRep Y X) (K : ℕ) (hK : g.shift + f.shift ≤ K)
    (hX : ∀ n, K ≤ n → X.map (opHomOfLE (show n + g.shift + f.shift ≤ n + K by omega)) ≫
        f.hom.app (op (n + g.shift)) ≫ g.hom.app (op n) =
      X.map (opHomOfLE (show n ≤ n + K by omega))) (m : ℕ) :
    (f.hom.app (op (m + K + g.shift + K)) ≫
        Y.map (opHomOfLE (show m + K + g.shift ≤ m + K + g.shift + K by omega))) ≫
      g.hom.app (op (m + K)) ≫ X.map (opHomOfLE (show m ≤ m + K by omega)) =
    X.map (opHomOfLE (show m ≤ m + K + g.shift + K + f.shift by omega)) := by
  rw [f.app_comp_map, Category.assoc,
    ← map_opHomOfLE_comp X (show m + K + K ≤ m + K + g.shift + K + f.shift by omega)
      (show m + K + g.shift + f.shift ≤ m + K + K by omega),
    reassoc_of% (hX (m + K) (by omega)), map_opHomOfLE_comp' X, map_opHomOfLE_comp' X]
  all_goals omega

/-- The pro-isomorphism built from two strict pro-morphisms inverse to each other from the level
`K` on. -/
noncomputable def proIsoOfStrictProHomRep {X Y : Functor ℕᵒᵖ C} (f : StrictProHomRep X Y)
    (g : StrictProHomRep Y X) (K : ℕ) (hK : g.shift + f.shift ≤ K)
    (hK' : f.shift + g.shift ≤ K)
    (hX : ∀ n, K ≤ n → X.map (opHomOfLE (show n + g.shift + f.shift ≤ n + K by omega)) ≫
        f.hom.app (op (n + g.shift)) ≫ g.hom.app (op n) =
      X.map (opHomOfLE (show n ≤ n + K by omega)))
    (hY : ∀ n, K ≤ n → Y.map (opHomOfLE (show n + f.shift + g.shift ≤ n + K by omega)) ≫
        g.hom.app (op (n + f.shift)) ≫ f.hom.app (op n) =
      Y.map (opHomOfLE (show n ≤ n + K by omega))) :
    _root_.InverseSequence.ProIso X Y where
  α m := m + K + f.shift
  β m := m + K + g.shift
  αmono a b h := Nat.add_le_add_right (Nat.add_le_add_right h K) f.shift
  βmono a b h := Nat.add_le_add_right (Nat.add_le_add_right h K) g.shift
  αle m := by omega
  βle m := by omega
  φ m := f.hom.app (op (m + K)) ≫ Y.map (opHomOfLE (show m ≤ m + K by omega))
  ψ m := g.hom.app (op (m + K)) ≫ X.map (opHomOfLE (show m ≤ m + K by omega))
  φnat {m m'} h := by
    simp only [_root_.InverseSequence.tr]
    rw [inverseSequence_map_eq X (homOfLE _).op
      (opHomOfLE (show m + K + f.shift ≤ m' + K + f.shift by omega)), ← Category.assoc,
      ← f.app_comp_map (show m + K ≤ m' + K by omega), Category.assoc, Category.assoc]
    congr 1
    rw [← Y.map_comp, ← Y.map_comp]
    exact inverseSequence_map_eq Y _ _
  ψnat {m m'} h := by
    simp only [_root_.InverseSequence.tr]
    rw [inverseSequence_map_eq Y (homOfLE _).op
      (opHomOfLE (show m + K + g.shift ≤ m' + K + g.shift by omega)), ← Category.assoc,
      ← g.app_comp_map (show m + K ≤ m' + K by omega), Category.assoc, Category.assoc]
    congr 1
    rw [← X.map_comp, ← X.map_comp]
    exact inverseSequence_map_eq X _ _
  ψφ m := by
    simp only [_root_.InverseSequence.tr]
    rw [f.round_trip g K hK hX m]
    exact inverseSequence_map_eq X _ _
  φψ m := by
    simp only [_root_.InverseSequence.tr]
    rw [g.round_trip f K hK' hY m]
    exact inverseSequence_map_eq Y _ _

/-- If the composite of `f` and `g` is equivalent to the identity, the round trip of the
components is a structural map from the level `n + K`, for all `n ≥ K` and large enough `K`. -/
private theorem exists_round_trip_of_equivalent_id {X Y : Functor ℕᵒᵖ C} (f : StrictProHomRep X Y)
    (g : StrictProHomRep Y X) (h : (f.comp g).Equivalent (StrictProHomRep.id X)) :
    ∃ (K₀ : ℕ) (hK₀ : g.shift + f.shift ≤ K₀), ∀ (K : ℕ) (hK : K₀ ≤ K) (n : ℕ) (_ : K ≤ n),
      X.map (opHomOfLE (show n + g.shift + f.shift ≤ n + K by omega)) ≫
          f.hom.app (op (n + g.shift)) ≫ g.hom.app (op n) =
        X.map (opHomOfLE (show n ≤ n + K by omega)) := by
  obtain ⟨d, N, hf, hg, H⟩ := (StrictProHomRep.equivalent_iff _ _).1 h
  have hf' : g.shift + f.shift ≤ d := hf
  refine ⟨d + N, by omega, fun K hK n hn => ?_⟩
  have H := StrictProHomRep.agree_of_le (hf := hf) (hg := hg) H (show d ≤ K by omega)
    (show (f.comp g).shift ≤ K by simp only [StrictProHomRep.comp_shift]; omega)
    (show (StrictProHomRep.id X).shift ≤ K by simp)
  exact map_comp_hom_app_eq_of_equivalent_id f g (show g.shift + f.shift ≤ K by omega) H n
    (by omega)

/-- **A strict pro-isomorphism is a pro-isomorphism.**  Two inverse sequences which are
isomorphic in the strict pro-category of [Stacks, Tag 0GA5] are pro-isomorphic. -/
theorem nonempty_proIso_of_nonempty_iso_proObj {X Y : Functor ℕᵒᵖ C}
    (h : Nonempty (proObj X ≅ proObj Y)) :
    Nonempty (_root_.InverseSequence.ProIso X Y) := by
  obtain ⟨f, g, h₁, h₂⟩ := nonempty_iso_iff_exists_rep.1 h
  obtain ⟨K₁, hK₁, H₁⟩ := exists_round_trip_of_equivalent_id f g h₁
  obtain ⟨K₂, hK₂, H₂⟩ := exists_round_trip_of_equivalent_id g f h₂
  exact ⟨proIsoOfStrictProHomRep f g (K₁ + K₂) (by omega) (by omega) (H₁ _ (by omega))
    (H₂ _ (by omega))⟩

end Stacks.LocalCohomology

end
