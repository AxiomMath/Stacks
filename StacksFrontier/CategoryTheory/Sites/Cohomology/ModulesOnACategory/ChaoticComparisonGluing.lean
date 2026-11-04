module

public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.LocallyQuasiIso
public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryHomology
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ModulesOnACategory.ChaoticComparisonOnCartesianObjects

/-!
# Gluing the condition of Stacks 0GZS from a covering family

Let `C` carry a Grothendieck topology `τ`, let `O` be a `τ`-sheaf of rings with commuting sections
and `ε : (C_τ, O_τ) ⟶ (C_τ', O_τ')` the comparison with the chaotic topology.

* Derived sheafification `ε^*` inverts a morphism of `D(O)` (on the chaotic site) whose derived
  sections over the members of a covering sieve of every object are isomorphisms:
  `isIso_epsilonPullback_map_of_exists_mem_sieve`. Its cohomology presheaves are then locally
  isomorphic, and sheafification is exact.
* If `C` has a terminal object `t`, `L` is an object of `D(C_τ, O_τ)` and `x i` is a family of
  objects such that the comparisons of `Rε_*L` along the arrows `t ← x i` are isomorphisms, every
  object is covered by objects admitting an arrow to some `x i` along which the comparison of
  `Rε_*L` is an isomorphism, and the `ε`-unit is invertible at the derived base change
  `Lp^*RΓ(t, Rε_*L) = RΓ(t, Rε_*L) ⊗^L_{O(t)} O`, then `Rε_*L` has cartesian derived sections:
  `isCartesianPushforward_of_comparison_of_exists_mem_sieve`. Indeed the counit
  `Lp^*RΓ(t, Rε_*L) ⟶ Rε_*L` is invertible on derived sections over those objects, by two
  naturality squares of comparison maps, so it is invertible after `ε^*`, hence invertible, the
  `ε`-units at both ends being invertible.

This is the gluing step of the proof that the objects of Stacks 0H0K's subcategory are
determined étale-locally.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.ModulesOnACategory.QuasiCoherentEquivalence
open Stacks.ModulesOnACategory.PullbackQuasiCoherentBaseChange (baseChangeDataOfComm)
open Stacks.ModulesOnACategory.TerminalMorphismOfSites (morphismOfSites)

namespace Stacks.ModulesOnACategory.ChaoticComparison

universe w u v r

attribute [local instance] HasDerivedCategory.standard

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} (R : Sheaf J RingCat.{r})
  [HasSheafify J AddCommGrpCat.{max u v r w}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v r w}]

/-- **Derived sheafification inverts a morphism which is invertible on derived sections over a
covering sieve of every object.** -/
theorem isIso_epsilonPullback_map_of_exists_mem_sieve {M N : DMod.{w} R.obj} (c : M ⟶ N)
    (h : ∀ V : C, ∃ S : Sieve V, S ∈ J V ∧ ∀ ⦃Y : C⦄ (a : Y ⟶ V), S a →
      IsIso ((RGamma.{w} R.obj (op Y)).map c)) :
    IsIso ((epsilonPullback.{w} R).mapDerivedCategory.map c) := by
  rw [DerivedCategory.isIso_iff]
  intro n
  rw [← Functor.comp_map, NatIso.isIso_map_iff
    ((epsilonPullback.{w} R).mapDerivedCategoryHomologyIso n) c]
  dsimp only [Functor.comp_map]
  refine PresheafOfModules.isIso_sheafification_map_of_exists_mem_sieve (𝟙 R.obj) _
    fun V ↦ ?_
  obtain ⟨S, hS, hc⟩ := h V
  refine ⟨S, hS, fun {Y} a ha ↦ ?_⟩
  have h1 := hc a ha
  have h2 : IsIso ((DerivedCategory.homologyFunctor _ n).map
      ((RGamma.{w} R.obj (op Y)).map c)) := inferInstance
  rw [← Functor.comp_map, NatIso.isIso_map_iff
    ((PresheafOfModules.evaluation.{max u v r w} R.obj (op Y)).mapDerivedCategoryHomologyIso n)
    c] at h2
  exact h2

variable (hO : ∀ (V : Cᵒᵖ) (x y : R.obj.obj V), x * y = y * x)

/-- **The condition of Stacks 0GZS glued from a covering family.** Let `t` be a terminal object
of `C` and `x : ι → C` a family of objects. Suppose that the comparisons of `Rε_*L` along the
arrows `t ← x i` are isomorphisms, that every object `V` has a covering sieve all of whose members
`z` admit an arrow `z ⟶ x i` along which the comparison of `Rε_*L` is an isomorphism, and that the
`ε`-unit is invertible at the derived base change `RΓ(t, Rε_*L) ⊗^L_{O(t)} O`. Then `Rε_*L` has
cartesian derived sections. -/
theorem isCartesianPushforward_of_comparison_of_exists_mem_sieve {t : C} (ht : IsTerminal t)
    (L : DerivedCategory (SheafOfModules.{max u v r w} R)) {ι : Type*} (x : ι → C)
    (hcomp₀ : ∀ i, IsIso (comparison.{w} (baseChangeDataOfComm.{r, v, u, w} R.obj hO)
      (ht.from (x i)).op ((derivedEpsilonPushforward.{w} R).obj L)))
    (hP : ∀ V : C, ∃ S : Sieve V, S ∈ J V ∧ ∀ ⦃Y : C⦄ (a : Y ⟶ V), S a → ∃ (i : ι)
      (b : Y ⟶ x i), IsIso (comparison.{w} (baseChangeDataOfComm.{r, v, u, w} R.obj hO)
        b.op ((derivedEpsilonPushforward.{w} R).obj L)))
    (hunit : IsIso ((derivedEpsilonAdjunction.{w} R).unit.app
      ((morphismOfSites.{w} R.obj hO ht).Lpullback.obj
        ((RGamma.{w} R.obj (op t)).obj ((derivedEpsilonPushforward.{w} R).obj L))))) :
    IsCartesianPushforward.{w} R (baseChangeDataOfComm.{r, v, u, w} R.obj hO) L := by
  set bc := baseChangeDataOfComm.{r, v, u, w} R.obj hO
  set mos := morphismOfSites.{w} R.obj hO ht
  set N := (derivedEpsilonPushforward.{w} R).obj L
  set c := mos.adj.counit.app N
  -- the counit is invertible on derived sections over `z` as soon as it is over `y` and the
  -- comparisons of `N` and of its base change along `y ← z` are invertible
  have hstep : ∀ {y z : C} (b : z ⟶ y), IsIso ((RGamma.{w} R.obj (op y)).map c) →
      IsIso (comparison.{w} bc b.op N) → IsIso ((RGamma.{w} R.obj (op z)).map c) := by
    intro y z b hy hb
    have hsq := comparison_naturality.{w} bc b.op c
    have h1 : IsIso (comparison.{w} bc b.op ((𝟭 (DMod.{w} R.obj)).obj N)) := hb
    have h2 : IsIso (comparison.{w} bc b.op ((RGamma.{w} R.obj (op t) ⋙ mos.Lpullback).obj N)) :=
      main_Lpullback_isQC.{w} bc mos ((RGamma.{w} R.obj (op t)).obj N) b.op
    have hL : IsIso ((bc.baseChange b.op).map ((RGamma.{w} R.obj (op y)).map c) ≫
        comparison.{w} bc b.op ((𝟭 (DMod.{w} R.obj)).obj N)) := IsIso.comp_isIso
    rw [hsq] at hL
    exact IsIso.of_isIso_comp_left
      (comparison.{w} bc b.op ((RGamma.{w} R.obj (op t) ⋙ mos.Lpullback).obj N))
      ((RGamma.{w} R.obj (op z)).map c)
  have ht' : IsIso ((RGamma.{w} R.obj (op t)).map c) := RGamma_counit_isIso.{w} bc mos N
  have hx : ∀ i, IsIso ((RGamma.{w} R.obj (op (x i))).map c) := fun i ↦
    hstep (ht.from (x i)) ht' (hcomp₀ i)
  -- hence it is invertible after sheafification
  have hε : IsIso ((epsilonPullback.{w} R).mapDerivedCategory.map c) := by
    refine isIso_epsilonPullback_map_of_exists_mem_sieve.{w} R c fun V ↦ ?_
    obtain ⟨S, hS, hSP⟩ := hP V
    refine ⟨S, hS, fun {Y} a ha ↦ ?_⟩
    obtain ⟨i, b, hb⟩ := hSP a ha
    exact hstep b (hx i) hb
  -- and the two units at its ends are invertible
  have hunitN : IsIso ((derivedEpsilonAdjunction.{w} R).unit.app N) := by
    have htri := (derivedEpsilonAdjunction.{w} R).right_triangle_components L
    have : IsIso ((derivedEpsilonPushforward.{w} R).map
        ((derivedEpsilonAdjunction.{w} R).counit.app L)) := inferInstance
    have h1 : IsIso ((derivedEpsilonAdjunction.{w} R).unit.app
        ((derivedEpsilonPushforward.{w} R).obj L) ≫ (derivedEpsilonPushforward.{w} R).map
          ((derivedEpsilonAdjunction.{w} R).counit.app L)) := by
      rw [htri]; exact IsIso.id _
    exact IsIso.of_isIso_comp_right _ ((derivedEpsilonPushforward.{w} R).map
      ((derivedEpsilonAdjunction.{w} R).counit.app L))
  have hc : IsIso c := by
    have : IsIso (c ≫ (derivedEpsilonAdjunction.{w} R).unit.app N) := by
      have e : c ≫ (derivedEpsilonAdjunction.{w} R).unit.app N =
          (derivedEpsilonAdjunction.{w} R).unit.app
            ((RGamma.{w} R.obj (op t) ⋙ mos.Lpullback).obj N) ≫
            (derivedEpsilonPushforward.{w} R).map
              ((epsilonPullback.{w} R).mapDerivedCategory.map c) := by
        simp
      rw [e]
      have : IsIso ((derivedEpsilonPushforward.{w} R).map
          ((epsilonPullback.{w} R).mapDerivedCategory.map c)) := inferInstance
      exact IsIso.comp_isIso' hunit this
    exact IsIso.of_isIso_comp_right c ((derivedEpsilonAdjunction.{w} R).unit.app N)
  have hQC : IsQC.{w} bc (mos.Lpullback.obj ((RGamma.{w} R.obj (op t)).obj N)) :=
    main_Lpullback_isQC.{w} bc mos ((RGamma.{w} R.obj (op t)).obj N)
  have hN : IsQC.{w} bc N :=
    (isQC_isClosedUnderIsomorphisms.{w} bc).of_iso (asIso c) hQC
  intro U V a
  exact hN a

end Stacks.ModulesOnACategory.ChaoticComparison

end
