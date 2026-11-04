module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionProjectiveEquivalence
public import StacksFrontier.AlgebraicGeometry.Variety.Bertini.AmbientImmersion
public import StacksFrontier.AlgebraicGeometry.Variety.Bertini.ReducedFiniteSections
public import StacksFrontier.AlgebraicGeometry.Variety.Bertini.VanishingDivisorOneStepReduction
public import StacksFrontier.AlgebraicGeometry.Variety.Bertini.VanishingSystemTwoPointsSections
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.MatrixTwoTransitive

/-!
# The Bertini step of [Stacks, Tag 0FH7] for a projective variety

Let `X` be a projective, smooth and geometrically irreducible scheme over an algebraically closed
field `k`, of dimension `d + 1 ≥ 2`, and let `x, x'` be two `k`-rational points of `X`. Then there
is a closed subscheme `H ⊆ X`, again projective, smooth and geometrically irreducible over `k`, of
dimension exactly `d`, through which both points factor.

This is the divisor `H_v` of the proof of [Stacks, Tag 0FH7] for a general section `v` of a high
power of an ample invertible module that vanishes at `x` and `x'`. The general-position argument
is `exists_bound_forall_exists_smooth_geometricallyIrreducible_divisorOnX_pair`, which takes the
linear system as input. Every input is supplied here from projectivity:

* the ample invertible module is the pullback of `𝒪(1)` along the defining closed immersion
  (`Stacks.Algebraization.exists_isRelativelyAmple_of_isProjective`);
* a basis of `V_n` exists, because `V_n` generates `ℒ ^⊗ n` off the two points
  ([Stacks, Tag 0FD5]) and the open complement of two closed points of a positive-dimensional
  irreducible scheme is nonempty, so `V_n ≠ 0`;
* the bound `dim_k Γ(Z, ℒ ^⊗ n|_Z) ≤ 2` is
  `AlgebraicGeometry.finrank_globalSections_le_natCard_of_isReduced` on the reduced subscheme on
  the two points;
* the ambient immersion of [Stacks, Tag 0FD6] is
  `Stacks.SectionsVanishingOnSubscheme.exists_bound_isImmersive_ambientFamilyDivisors`.

Projectivity of `H` comes from composing `H ↪ X` with the closed immersion of `X` into projective
space. It is part of the conclusion, so the step can be iterated, as both the induction of
[Stacks, Tag 0FH7] and the curve reduction of [Stacks, Tag 0FH9] do.

## Main results

* `exists_projective_smooth_geometricallyIrreducible_divisor_pair`: a projective, smooth and
  geometrically irreducible variety of dimension `d + 1 ≥ 2` over an algebraically closed field
  has a projective, smooth and geometrically irreducible closed subscheme of dimension `d`
  through any two given `k`-rational points.

## References

* [Stacks Project, Tag 0FD5](https://stacks.math.columbia.edu/tag/0FD5)
* [Stacks Project, Tag 0FD6](https://stacks.math.columbia.edu/tag/0FD6)
* [Stacks Project, Tag 0FH7](https://stacks.math.columbia.edu/tag/0FH7)
* [Stacks Project, Tag 0FH9](https://stacks.math.columbia.edu/tag/0FH9)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace
open Stacks.Ample Stacks.ProjectiveFromSections

universe u

namespace Stacks.SectionsVanishingOnSubscheme

/-- A closed subscheme of an H-projective scheme is H-projective. -/
theorem isProjectiveMorphism_comp_of_isClosedImmersion {H X S : Scheme.{u}} (ι : H ⟶ X)
    [IsClosedImmersion ι] {f : X ⟶ S} (hf : IsProjectiveMorphism f) :
    IsProjectiveMorphism (ι ≫ f) := by
  obtain ⟨n, j, hj, rfl⟩ := hf
  have := hj
  exact ⟨n, ι ≫ j, inferInstance, Category.assoc _ _ _⟩

/-- **A positive-dimensional scheme is not covered by two closed points.** -/
theorem exists_ne_ne_of_topologicalKrullDim {X : Type*} [TopologicalSpace X] {z z' : X}
    (hz : IsClosed ({z} : Set X)) (hz' : IsClosed ({z'} : Set X)) {d : ℕ}
    (hdim : topologicalKrullDim X = ((d + 1 : ℕ) : WithBot ℕ∞)) :
    ∃ y : X, y ≠ z ∧ y ≠ z' := by
  by_contra! h
  have : T1Space X := ⟨fun y => by
    rcases eq_or_ne y z with rfl | hyz
    · exact hz
    · rw [h y hyz]; exact hz'⟩
  have : Finite X := by
    refine Finite.of_injective (β := ({z, z'} : Set X)) (fun y => ⟨y, ?_⟩) ?_
    · rcases eq_or_ne y z with rfl | hyz
      · exact Set.mem_insert _ _
      · exact Set.mem_insert_of_mem _ (h y hyz)
    · intro a b hab
      exact congrArg Subtype.val hab
  have : DiscreteTopology X := inferInstance
  have hle := topologicalKrullDim_zero_of_discreteTopology X
  rw [hdim] at hle
  exact absurd hle (by norm_cast)

variable (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

/-- **The Bertini step of [Stacks, Tag 0FH7] for a projective variety.** Let `k` be algebraically
closed and let `X` be H-projective, smooth and geometrically irreducible over `k` with
`dim X = d + 1` and `1 ≤ d`. Let `x, x'` be `k`-rational points of `X`. Then there is a closed
immersion `ι : H ⟶ X` with `H` H-projective, smooth and geometrically irreducible over `k`, of
dimension exactly `d`, and `k`-rational points of `H` mapping to `x` and `x'`. -/
theorem exists_projective_smooth_geometricallyIrreducible_divisor_pair [IsAlgClosed k]
    [Smooth f] [GeometricallyIrreducible f] (hproj : IsProjectiveMorphism f)
    {d : ℕ} (hd : 1 ≤ d) (hdim : topologicalKrullDim X = ((d + 1 : ℕ) : WithBot ℕ∞))
    (x x' : Spec (.of k) ⟶ X) (hx : x ≫ f = 𝟙 _) (hx' : x' ≫ f = 𝟙 _) :
    ∃ (H : Scheme.{u}) (ι : H ⟶ X) (_ : IsClosedImmersion ι) (_ : Smooth (ι ≫ f))
      (_ : GeometricallyIrreducible (ι ≫ f)),
      IsProjectiveMorphism (ι ≫ f) ∧ topologicalKrullDim H = (d : WithBot ℕ∞) ∧
        ∃ x_H x'_H : Spec (.of k) ⟶ H, x_H ≫ ι = x ∧ x'_H ≫ ι = x' := by
  have : IsProper f := isProper_of_isProjectiveMorphism f hproj
  obtain ⟨L, hLinv, -, hL⟩ :=
    Stacks.Algebraization.exists_isRelativelyAmple_of_isProjective k f hproj.isProjective
  let : IsInvertibleModule X L := hLinv
  have : Nonempty X := ⟨x (IsLocalRing.closedPoint k)⟩
  set z := x (IsLocalRing.closedPoint k)
  set z' := x' (IsLocalRing.closedPoint k)
  have hz : IsClosed ({z} : Set X) := isClosed_singleton_apply_closedPoint k f x hx
  have hz' : IsClosed ({z'} : Set X) := isClosed_singleton_apply_closedPoint k f x' hx'
  set I := Scheme.IdealSheafData.vanishingIdeal (⟨{z, z'}, hz.union hz'⟩ : Closeds X)
  have hsupp : (I.support : Set X) = {z, z'} :=
    Scheme.IdealSheafData.coe_support_vanishingIdeal _
  obtain ⟨n₀, -, hstep⟩ :=
    exists_bound_forall_exists_smooth_geometricallyIrreducible_divisorOnX_pair k f hL hd hdim
      hz hz' x x' hx hx' rfl rfl
  obtain ⟨m₁, hm₁⟩ := exists_bound_isImmersive_ambientFamilyDivisors k f hL
  obtain ⟨m₂, hm₂⟩ := exists_bound_generatesOffSupport k f I L hL
  set n : ℕ := max n₀ (max m₁.toNat m₂.toNat)
  have hn₀ : n₀ ≤ n := le_max_left _ _
  have hn₁ : m₁ ≤ (n : ℤ) := (Int.self_le_toNat m₁).trans (by
    exact_mod_cast (le_max_left _ _).trans (le_max_right _ _))
  have hn₂ : m₂ ≤ (n : ℤ) := (Int.self_le_toNat m₂).trans (by
    exact_mod_cast (le_max_right _ _).trans (le_max_right _ _))
  -- a basis of `V_n`
  have hnt : Nontrivial (vanishingSections k f I L (n : ℤ)) := by
    obtain ⟨y, hyz, hyz'⟩ := exists_ne_ne_of_topologicalKrullDim hz hz' hdim
    have hy : y ∈ I.support.compl := by
      change y ∉ (I.support : Set X)
      rw [hsupp]
      rintro (h | h) <;> contradiction
    obtain ⟨t, ht⟩ := Stacks.StalkwiseGeneration.exists_mem_nvOpen_of_span_eq_top
      (tensorPowModule X L (n : ℤ)) _ y (hm₂ n hn₂ y hy)
    refine ⟨⟨t, 0, fun h0 => ne_zero_of_mem_nvOpen _ ht ?_⟩⟩
    rw [h0]; rfl
  obtain ⟨N, hN⟩ : ∃ N : ℕ, Module.finrank k (vanishingSections k f I L (n : ℤ)) = N + 1 :=
    Nat.exists_eq_succ_of_ne_zero Module.finrank_pos.ne'
  -- the dimension bound on the two points
  have hcond : Module.finrank k (subschemeSections k f I (L := L) (n : ℤ)) ≤ 2 := by
    rw [finrank_subschemeSections_eq_finrank_globalSections_of_coe_support_eq_pair k f I hz hz'
      hsupp]
    have : IsFinite (I.subschemeι ≫ f) :=
      isFinite_subschemeι_comp_of_coe_support_eq_pair k f I hz hz' hsupp
    let g : I.subscheme → ({z, z'} : Set X) := fun w => ⟨I.subschemeι w, by
      rw [← hsupp, ← I.range_subschemeι]; exact ⟨w, rfl⟩⟩
    have hg : Function.Injective g := fun a b hab =>
      I.subschemeι.isClosedEmbedding.injective (congrArg Subtype.val hab)
    have : Finite I.subscheme := Finite.of_injective g hg
    refine (finrank_globalSections_le_natCard_of_isReduced k (I.subschemeι ≫ f)).trans ?_
    calc Nat.card I.subscheme ≤ Nat.card ({z, z'} : Set X) :=
          Nat.card_le_card_of_injective g hg
      _ ≤ 2 := by
          rw [Nat.card_coe_set_eq]
          exact (Set.ncard_insert_le _ _).trans (by simp)
  obtain ⟨p, b', hb', himm⟩ := hm₁ n hn₁
  obtain ⟨H, ι, hι, hsm, hgi, hdimH, x_H, x'_H, hxH, hxH'⟩ :=
    hstep n hn₀ N (Module.finBasisOfFinrankEq k _ hN) hcond himm
  exact ⟨H, ι, hι, hsm, hgi, isProjectiveMorphism_comp_of_isClosedImmersion ι hproj, hdimH,
    x_H, x'_H, hxH, hxH'⟩

/-- **A smooth projective curve through two rational points.** Let `k` be algebraically closed
and let `X` be H-projective, smooth and geometrically irreducible over `k` with `dim X = d` and
`1 ≤ d`. Let `x, x'` be `k`-rational points of `X`. Then there is a closed immersion `ι : C ⟶ X`
with `C` H-projective, smooth and geometrically irreducible over `k`, of dimension one, and
`k`-rational points of `C` mapping to `x` and `x'`.

This is the reduction to a curve in the proofs of [Stacks, Tag 0FH7] and [Stacks, Tag 0FH9]:
`exists_projective_smooth_geometricallyIrreducible_divisor_pair` applied `d - 1` times. -/
theorem exists_projective_smooth_geometricallyIrreducible_curve_pair [IsAlgClosed k] (d : ℕ)
    (hd : 1 ≤ d) :
    ∀ {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [Smooth f] [GeometricallyIrreducible f],
      IsProjectiveMorphism f → topologicalKrullDim X = (d : WithBot ℕ∞) →
      ∀ (x x' : Spec (.of k) ⟶ X), x ≫ f = 𝟙 _ → x' ≫ f = 𝟙 _ →
      ∃ (C : Scheme.{u}) (ι : C ⟶ X) (_ : IsClosedImmersion ι) (_ : Smooth (ι ≫ f))
        (_ : GeometricallyIrreducible (ι ≫ f)),
        IsProjectiveMorphism (ι ≫ f) ∧ topologicalKrullDim C = (1 : WithBot ℕ∞) ∧
          ∃ x_C x'_C : Spec (.of k) ⟶ C, x_C ≫ ι = x ∧ x'_C ≫ ι = x' := by
  induction d, hd using Nat.le_induction with
  | base =>
    intro X f _ _ hproj hdim x x' _ _
    refine ⟨X, 𝟙 X, inferInstance, ?_, ?_, ?_, by exact_mod_cast hdim, x, x', by simp, by simp⟩ <;>
      simpa using ‹_›
  | succ d hd ih =>
    intro X f _ _ hproj hdim x x' hx hx'
    obtain ⟨H, ι, hι, hsm, hgi, hprojH, hdimH, x_H, x'_H, hxH, hxH'⟩ :=
      exists_projective_smooth_geometricallyIrreducible_divisor_pair k f hproj hd hdim x x' hx hx'
    have hxH₁ : x_H ≫ ι ≫ f = 𝟙 _ := by rw [← Category.assoc, hxH, hx]
    have hxH₁' : x'_H ≫ ι ≫ f = 𝟙 _ := by rw [← Category.assoc, hxH', hx']
    obtain ⟨C, ι', hι', hsm', hgi', hprojC, hdimC, x_C, x'_C, hxC, hxC'⟩ :=
      ih (ι ≫ f) hprojH hdimH x_H x'_H hxH₁ hxH₁'
    refine ⟨C, ι' ≫ ι, inferInstance, ?_, ?_, ?_, hdimC, x_C, x'_C, ?_, ?_⟩
    · rw [Category.assoc]; exact hsm'
    · rw [Category.assoc]; exact hgi'
    · rw [Category.assoc]; exact hprojC
    · rw [← Category.assoc, hxC, hxH]
    · rw [← Category.assoc, hxC', hxH']

end Stacks.SectionsVanishingOnSubscheme

end
