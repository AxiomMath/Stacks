module

public import StacksFrontier.CategoryTheory.Abelian.InverseSystemModuleCat

/-!
# Mittag-Leffler from domination by a system with surjective transition maps

An inverse system of modules which is *pro-dominated* by an inverse system whose transition
maps are surjective satisfies the Mittag-Leffler condition of Stacks Tag 02N0.

Pro-domination is the following data, with index shifts `a, b : ℕ → ℕ` of which only `b` need
be monotone: maps `β n : G_{b n} → F_n` compatible with the transition maps of the two systems,
and maps `α n : F_{a n} → G_n` such that `α (b n) ≫ β n` is the transition map
`F_{a (b n)} → F_n`. A pro-isomorphism `F → G` of inverse systems provides such data.

## Main results

* `surjective_transition_of_le`: surjectivity of the one-step transition maps of an inverse
  system of modules propagates to all transition maps.
* `isMittagLefflerCategorical_of_proDominated_of_monotone`: an inverse system of modules
  pro-dominated by one with surjective transition maps is Mittag-Leffler.
* `isMittagLefflerCategorical_of_proDominated`: the same, for the uniform shifts `n ↦ n + c`.

## References

* [Stacks Project, Tag 02N0](https://stacks.math.columbia.edu/tag/02N0)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v

/-- The transition map `F.obj (op j) ⟶ F.obj (op i)` of an inverse system indexed by `ℕᵒᵖ`
factors through any intermediate stage. -/
theorem inverseSystem_transition_comp {C : Type*} [Category C] (F : ℕᵒᵖ ⥤ C)
    {i j k : ℕ} (hij : i ≤ j) (hjk : j ≤ k) :
    F.map (homOfLE (hij.trans hjk)).op =
      F.map (homOfLE hjk).op ≫ F.map (homOfLE hij).op := by
  rw [← F.map_comp]
  rfl

/-- If every one-step transition map of an inverse system of modules is surjective, then so is
every transition map. -/
theorem surjective_transition_of_le {A : Type u} [Ring A] (F : ℕᵒᵖ ⥤ ModuleCat.{v} A)
    (hsurj : ∀ n : ℕ, Function.Surjective (F.map (homOfLE (Nat.le_succ n)).op).hom)
    {i j : ℕ} (h : i ≤ j) : Function.Surjective (F.map (homOfLE h).op).hom := by
  induction j, h using Nat.le_induction with
  | base => simpa using Function.surjective_id
  | succ j hij ih =>
    rw [inverseSystem_transition_comp F hij (Nat.le_succ j), ModuleCat.hom_comp]
    exact ih.comp (hsurj j)

/-- Mittag-Leffler from pro-domination. Let `F` and `G` be inverse systems of `A`-modules
indexed by `ℕᵒᵖ` and suppose the one-step transition maps of `G` are surjective. Suppose given
index shifts `a, b : ℕ → ℕ` with `b` monotone and `n ≤ a (b n)`, maps `β n : G_{b n} ⟶ F_n`
compatible with the transition maps of `F` and `G`, and maps `α n : F_{a n} ⟶ G_n` with
`α (b n) ≫ β n` the transition map `F_{a (b n)} ⟶ F_n`. Then `F` satisfies the Mittag-Leffler
condition. -/
theorem isMittagLefflerCategorical_of_proDominated_of_monotone {A : Type u} [Ring A]
    (F G : ℕᵒᵖ ⥤ ModuleCat.{v} A) (a b : ℕ → ℕ) (hb : Monotone b)
    (hab : ∀ n : ℕ, n ≤ a (b n))
    (hG : ∀ n : ℕ, Function.Surjective (G.map (homOfLE (Nat.le_succ n)).op).hom)
    (β : ∀ n : ℕ, G.obj (op (b n)) ⟶ F.obj (op n))
    (hβ : ∀ (i j : ℕ) (h : i ≤ j),
      G.map (homOfLE (hb h)).op ≫ β i = β j ≫ F.map (homOfLE h).op)
    (α : ∀ n : ℕ, F.obj (op (a n)) ⟶ G.obj (op n))
    (hαβ : ∀ n : ℕ, α (b n) ≫ β n = F.map (homOfLE (hab n)).op) :
    IsMittagLefflerCategorical F := by
  apply isMittagLefflerCategorical_of_forall_exists_range_eq
  intro i
  refine ⟨a (b i), hab i, fun k hk => le_antisymm ?_ ?_⟩
  · rw [inverseSystem_transition_comp F (hab i) hk, ModuleCat.hom_comp]
    exact LinearMap.range_comp_le_range _ _
  · have hrange : LinearMap.range (F.map (homOfLE (hab i)).op).hom ≤
        LinearMap.range (β i).hom := by
      rw [← hαβ i, ModuleCat.hom_comp]
      exact LinearMap.range_comp_le_range _ _
    refine hrange.trans ?_
    rintro _ ⟨g, rfl⟩
    have hik : i ≤ k := (hab i).trans hk
    obtain ⟨g', rfl⟩ := surjective_transition_of_le G hG (hb hik) g
    exact ⟨(β k).hom g', (congrArg (fun φ => φ.hom g') (hβ i k hik)).symm⟩

/-- Mittag-Leffler from pro-domination, with a uniform shift. Let `F` and `G` be inverse
systems of `A`-modules indexed by `ℕᵒᵖ` and suppose the one-step transition maps of `G` are
surjective. Suppose given a shift `c`, maps `β n : G_{n+c} ⟶ F_n` compatible with the transition
maps of `F` and `G`, and maps `α n : F_{n+c} ⟶ G_n` with `α (n + c) ≫ β n` the transition map
`F_{n+c+c} ⟶ F_n`. Then `F` satisfies the Mittag-Leffler condition. -/
theorem isMittagLefflerCategorical_of_proDominated {A : Type u} [Ring A]
    (F G : ℕᵒᵖ ⥤ ModuleCat.{v} A) (c : ℕ)
    (hG : ∀ n : ℕ, Function.Surjective (G.map (homOfLE (Nat.le_succ n)).op).hom)
    (β : ∀ n : ℕ, G.obj (op (n + c)) ⟶ F.obj (op n))
    (hβ : ∀ (i j : ℕ) (h : i ≤ j),
      G.map (homOfLE (Nat.add_le_add_right h c)).op ≫ β i = β j ≫ F.map (homOfLE h).op)
    (α : ∀ n : ℕ, F.obj (op (n + c)) ⟶ G.obj (op n))
    (hαβ : ∀ n : ℕ, α (n + c) ≫ β n = F.map (homOfLE (show n ≤ n + c + c by omega)).op) :
    IsMittagLefflerCategorical F :=
  isMittagLefflerCategorical_of_proDominated_of_monotone F G (· + c) (· + c)
    (fun _ _ h => Nat.add_le_add_right h c) (fun n => by omega) hG β hβ α hαβ

end
