module

public import Mathlib.Algebra.Homology.HomotopyCategory
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Data.Int.ConditionallyCompleteOrder

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-!
# Right adjoints of exact functors preserve K-injective complexes

Let `A` and `B` be abelian categories and let `u : A ⥤ B`, `v : B ⥤ A` be additive functors
with `v ⊣ u` and `v` exact. Then `u`, applied degreewise to cochain complexes, sends
K-injective complexes to K-injective complexes. Applied to the adjunction between pullback and
pushforward of modules along a flat morphism of ringed topoi, this says that pushforward along
a flat morphism preserves K-injective complexes.

## Main definitions

* `IsKInjectiveHomotopyCategory`: a cochain complex `I` is K-injective if every morphism from
  an acyclic complex to `I` in the homotopy category is zero.
* `mapHomologicalComplexAdjunction`: an adjunction `v ⊣ u` induces an adjunction between the
  degreewise functors on cochain complexes.

## Main results

* `rightAdjoint_preserves_isKInjective`: if `v ⊣ u` and `v` is exact, then `u` preserves
  K-injective complexes.

## References

* [Stacks Project, Tag 070G and Tag 093Y][stacks-project]
-/

open CategoryTheory CategoryTheory.Limits

universe v u

variable {A : Type u} [Category.{v} A] [Abelian A]

/-- A cochain complex `I` indexed by `ℤ` is K-injective if for every acyclic complex `M`, every
morphism from `M` to `I` in the homotopy category is zero. -/
def IsKInjectiveHomotopyCategory (I : CochainComplex A ℤ) : Prop :=
  ∀ (M : CochainComplex A ℤ), M.Acyclic →
    ∀ (f : (HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj M ⟶
           (HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj I), f = 0

variable {B : Type u} [Category.{v} B] [Abelian B]

/-- The adjunction `v ⊣ u` lifts degreewise to an adjunction between the induced functors on
cochain complexes. -/
noncomputable def mapHomologicalComplexAdjunction
    (u : A ⥤ B) (v : B ⥤ A) [u.Additive] [v.Additive] (adj : v ⊣ u) :
    (v.mapHomologicalComplex (ComplexShape.up ℤ)) ⊣
      (u.mapHomologicalComplex (ComplexShape.up ℤ)) :=
  Adjunction.mkOfHomEquiv
  { homEquiv := fun Y X =>
      { toFun := fun g =>
          { f := fun i => (adj.homEquiv (Y.X i) (X.X i)) (g.f i)
            comm' := by
              intro i j hij
              simp only [Functor.mapHomologicalComplex_obj_d]
              rw [← adj.homEquiv_naturality_right, ← adj.homEquiv_naturality_left]
              congr 1
              exact g.comm i j }
        invFun := fun h =>
          { f := fun i => (adj.homEquiv (Y.X i) (X.X i)).symm (h.f i)
            comm' := by
              intro i j hij
              simp only [Functor.mapHomologicalComplex_obj_d]
              rw [← adj.homEquiv_naturality_right_symm, ← adj.homEquiv_naturality_left_symm]
              congr 1
              exact h.comm i j }
        left_inv := by intro g; ext i; simp
        right_inv := by intro h; ext i; simp }
    homEquiv_naturality_left_symm := by
      intro X' X Y f g
      ext i
      dsimp
      simp [adj.homEquiv_naturality_left_symm]
    homEquiv_naturality_right := by
      intro X Y Y' f g
      ext i
      dsimp
      simp [adj.homEquiv_naturality_right] }

/-- If `v ⊣ u` with `v` additive and exact (preserving finite limits and finite colimits), then
the degreewise functor `u.mapHomologicalComplex (ComplexShape.up ℤ)` sends K-injective cochain
complexes to K-injective cochain complexes. -/
theorem rightAdjoint_preserves_isKInjective
    (u : A ⥤ B) (v : B ⥤ A) [u.Additive] [v.Additive]
    (adj : v ⊣ u)
    [PreservesFiniteLimits v] [PreservesFiniteColimits v]
    (I : CochainComplex A ℤ) (hI : IsKInjectiveHomotopyCategory I) :
    IsKInjectiveHomotopyCategory ((u.mapHomologicalComplex (ComplexShape.up ℤ)).obj I) := by
  set Qa := HomotopyCategory.quotient A (ComplexShape.up ℤ)
  set Qb := HomotopyCategory.quotient B (ComplexShape.up ℤ)
  set uHC := u.mapHomologicalComplex (ComplexShape.up ℤ)
  set vHC := v.mapHomologicalComplex (ComplexShape.up ℤ)
  have madj : vHC ⊣ uHC := mapHomologicalComplexAdjunction u v adj
  intro M hM f
  obtain ⟨g, hg⟩ := Qb.map_surjective f
  set g' := (madj.homEquiv M I).symm g
  have hvM : (vHC.obj M).Acyclic := fun n => by
    rw [HomologicalComplex.exactAt_iff]
    exact ((HomologicalComplex.exactAt_iff _ _).mp (hM n)).map v
  have hg'zero : Qa.map g' = 0 := hI (vHC.obj M) hvM (Qa.map g')
  have hhtpy : Homotopy g' 0 :=
    HomotopyCategory.homotopyOfEq g' 0 (by rw [hg'zero, Qa.map_zero])
  have hgeq : g = madj.unit.app M ≫ uHC.map g' := by
    have : (madj.homEquiv M I) g' = g := (madj.homEquiv M I).apply_symm_apply g
    rw [← this, madj.homEquiv_unit]
  have huzero : Qb.map (uHC.map g') = 0 := by
    have hh : Homotopy (uHC.map g') (uHC.map 0) := u.mapHomotopy hhtpy
    rw [uHC.map_zero] at hh
    rw [HomotopyCategory.quotient_map_eq_zero_iff]
    exact ⟨hh⟩
  rw [← hg, hgeq, Qb.map_comp, huzero, comp_zero]
