module

public import StacksFrontier.AlgebraicGeometry.FormalFunctions.CohomologyIdealPowerSystem
public import StacksFrontier.RingTheory.Module.AdicSystem.Homology
public import StacksFrontier.AlgebraicGeometry.FormalFunctions.CohomologyIdealPowerSystemSupplement

/-!
# The two ideal-power cohomology systems are pro-isomorphic

[Stacks, Tag 02OA] part (5) asserts that the inverse systems `(Hᵖ(X, Iⁿℱ))` and
`(IⁿHᵖ(X, ℱ))` are pro-isomorphic, and the source deduces it from part (4) "and the definition
of morphisms of pro-objects". This file carries out that deduction.

Both inverse systems are functors on `ℕᵒᵖ`, built from their successor transition maps by
`CategoryTheory.Functor.ofOpSequence`; pro-isomorphism is `InverseSequence.ProIso`, the explicit
up-to-refinement form. The two reindexings are both `m ↦ m + c`; the forward maps are the
projections `Hᵖ(X, Iᵐ⁺ᶜℱ) → IᵐHᵖ(X, ℱ)` of part (2) at degree `0`, the backward maps are the
comparison maps `Iᵐ⁺ᶜHᵖ(X, ℱ) → Hᵖ(X, Iᵐℱ)` of part (4), and the two round trips are exactly
the two composites that part (4) identifies with the canonical maps.

## Main definitions

* `Stacks.RingTheory.powSmulFunctor` is the inverse system `n ↦ Iⁿ M₀` of the ideal-power
  filtration of a module, with the inclusions as transition maps.
* `Stacks.RingTheory.ReesSystem.systemFunctor` is the inverse system `n ↦ M n` of an ideal-power
  system.
* `Stacks.RingTheory.ReesSystem.projCorestrict` is the projection `M n → M₀` corestricted to
  `Iʳ M₀`, which part (2) of the source at degree `0` makes possible.

## Main results

* `Stacks.RingTheory.ReesSystem.proIso_powSmulFunctor`: the two systems are pro-isomorphic, in
  the abstract, given the clauses of [Stacks, Tag 02OA] that
  `Stacks.RingTheory.ReesSystem.exists_uniform_bound_mul` produces.
* `Stacks.Cohomology.FormalFunctions.proIso_cohomologyIdealPower`: **[Stacks, Tag 02OA]
  part (5)** for `n ↦ Hᵖ(X, Iⁿℱ)` over `Hᵖ(X, ℱ)`, granted [Stacks, Tag 02O8] in the same
  general form as the rest of the tag.

## Implementation notes

The transition map of a `Functor.ofOpSequence` along a general `n ≤ m` is a composite of
successor maps, so each system needs one induction (`tr_systemFunctor`, `tr_powSmulFunctor`)
identifying it with the map it should be. Both are the induction of
`CategoryTheory.Functor.ofOpSequence_map_homOfLE_succ` along `Nat.le_induction`, exactly as
`StacksFrontier/RingTheory/Module/AdicSystem/Ext.lean` does for its quotient system.

The four conditions of `InverseSequence.ProIso` beyond the reindexings are each proved first as
a statement about the underlying linear maps and only then transported to the categorical
form; stated directly on the functors, the bound variable carries the type
`↑(F.obj (op n))` rather than `↥(Iⁿ M₀)` and the subtype extensionality lemma no longer
applies. Each one goes through `Stacks.RingTheory.ReesSystem.comparison_apply`: the comparison
map is computed by *any* preimage under the projection, and in each case a preimage is produced
by a transition map applied to a preimage one level up.

## References

* [Stacks Project, Tag 02OA](https://stacks.math.columbia.edu/tag/02OA)
* [Stacks Project, Tag 02O8](https://stacks.math.columbia.edu/tag/02O8)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Opposite InverseSequence
open Stacks.Cohomology.AffineBase
open scoped ModuleCat.Algebra

universe u v

namespace Stacks.RingTheory

variable {A : Type u} [CommRing A] {I : Ideal A}
  {M : ℕ → Type v} [∀ n, AddCommGroup (M n)] [∀ n, Module A (M n)]
  {M₀ : Type v} [AddCommGroup M₀] [Module A M₀]

/-- The inverse system `n ↦ Iⁿ M₀` of the ideal-power filtration of `M₀`, with the inclusions
as transition maps. -/
def powSmulFunctor (I : Ideal A) (M₀ : Type v) [AddCommGroup M₀] [Module A M₀] :
    ℕᵒᵖ ⥤ ModuleCat.{v} A :=
  Functor.ofOpSequence (X := fun n ↦ ModuleCat.of A ↥(I ^ n • (⊤ : Submodule A M₀)))
    (fun n ↦ ModuleCat.ofHom
      (Submodule.inclusion (Submodule.pow_smul_top_le I M₀ (Nat.le_succ n))))

/-- The transition map of `powSmulFunctor I M₀` along `n ≤ m` is the inclusion
`Iᵐ M₀ ⊆ Iⁿ M₀`. -/
theorem tr_powSmulFunctor {n m : ℕ} (h : n ≤ m) :
    tr (powSmulFunctor I M₀) h =
      ModuleCat.ofHom (Submodule.inclusion (Submodule.pow_smul_top_le I M₀ h)) := by
  induction m, h using Nat.le_induction with
  | base =>
      rw [ProIso.tr_refl]
      ext
      rfl
  | succ m h ih =>
      rw [← ProIso.tr_trans _ h (Nat.le_succ m), ih]
      simp only [tr, powSmulFunctor, Functor.ofOpSequence_map_homOfLE_succ]
      ext
      rfl

namespace ReesSystem

variable (S : ReesSystem (RingHom.id A) I M M₀)

/-- The projection `M n → M₀` corestricted to `Iʳ M₀`. Part (2) of [Stacks, Tag 02OA] at
degree `0` is what makes the corestriction possible. -/
def projCorestrict {n r : ℕ}
    (hb : LinearMap.range (S.proj n) ≤ I ^ r • (⊤ : Submodule A M₀)) :
    M n →ₗ[A] ↥(I ^ r • (⊤ : Submodule A M₀)) :=
  (S.proj n).codRestrict _ fun z ↦ hb ⟨z, rfl⟩

/-- The corestricted projection `projCorestrict` agrees with `proj` after coercion to `M₀`. -/
@[simp]
theorem coe_projCorestrict {n r : ℕ}
    (hb : LinearMap.range (S.proj n) ≤ I ^ r • (⊤ : Submodule A M₀)) (z : M n) :
    (S.projCorestrict hb z : M₀) = S.proj n z := rfl

/-- The inverse system `n ↦ M n` of an ideal-power system, with its transition maps. -/
def systemFunctor : ℕᵒᵖ ⥤ ModuleCat.{v} A :=
  Functor.ofOpSequence (X := fun n ↦ ModuleCat.of A (M n))
    (fun n ↦ ModuleCat.ofHom (S.tr (Nat.le_succ n)))

/-- The transition map of `systemFunctor` along `n ≤ m` is the transition map `S.tr` of the
ideal-power system. -/
theorem tr_systemFunctor {n m : ℕ} (h : n ≤ m) :
    tr S.systemFunctor h = ModuleCat.ofHom (S.tr h) := by
  induction m, h using Nat.le_induction with
  | base =>
      rw [ProIso.tr_refl]
      ext x
      exact (S.tr_eq_self _ x).symm
  | succ m h ih =>
      rw [← ProIso.tr_trans _ h (Nat.le_succ m), ih]
      simp only [tr, systemFunctor, Functor.ofOpSequence_map_homOfLE_succ]
      ext x
      exact S.tr_tr h (Nat.le_succ m) x

section ProIsoData

variable {c : ℕ}
  (hb : ∀ r : ℕ, LinearMap.range (S.proj (r + c)) ≤ I ^ r • (⊤ : Submodule A M₀))
  (hrange : ∀ n : ℕ, I ^ n • (⊤ : Submodule A M₀) ≤ LinearMap.range (S.proj n))
  (hker : ∀ r : ℕ, LinearMap.ker (S.proj (r + c)) =
    LinearMap.ker (S.tr (Nat.le_add_right r c)))

/-- The corestricted projections are compatible with the transition maps of the two systems. -/
theorem inclusion_projCorestrict {m m' : ℕ} (h : m ≤ m') (z : M (m' + c)) :
    Submodule.inclusion (Submodule.pow_smul_top_le I M₀ h) (S.projCorestrict (hb m') z) =
      S.projCorestrict (hb m) (S.tr (Nat.add_le_add_right h c) z) :=
  Subtype.ext (S.proj_tr (Nat.add_le_add_right h c) z).symm

/-- The comparison maps are compatible with the transition maps of the two systems. -/
theorem comparison_inclusion {m m' : ℕ} (h : m ≤ m')
    (η : ↥(I ^ (m' + c) • (⊤ : Submodule A M₀))) :
    S.comparison (hrange (m + c)) (hker m)
        (Submodule.inclusion (Submodule.pow_smul_top_le I M₀ (Nat.add_le_add_right h c)) η) =
      S.tr h (S.comparison (hrange (m' + c)) (hker m') η) := by
  obtain ⟨z, hz⟩ := hrange (m' + c) η.2
  have hw : S.proj (m + c) (S.tr (Nat.add_le_add_right h c) z) = (η : M₀) :=
    (S.proj_tr _ z).trans hz
  rw [S.comparison_apply (hrange (m + c)) (hker m) _ _ hw,
    S.comparison_apply (hrange (m' + c)) (hker m') η z hz, S.tr_tr, S.tr_tr]

/-- The comparison map after the corestricted projection is a transition map: this is the first
composite of [Stacks, Tag 02OA] part (4). -/
theorem comparison_projCorestrict {m : ℕ} (z : M (m + c + c)) :
    S.comparison (hrange (m + c)) (hker m) (S.projCorestrict (hb (m + c)) z) =
      S.tr ((Nat.le_add_right m c).trans (Nat.le_add_right (m + c) c)) z :=
  S.comparison_proj (hrange (m + c)) (hker m) z _

/-- The corestricted projection after the comparison map is an inclusion: this is the second
composite of [Stacks, Tag 02OA] part (4). -/
theorem projCorestrict_comparison {m : ℕ}
    (η : ↥(I ^ (m + c + c) • (⊤ : Submodule A M₀))) :
    S.projCorestrict (hb m) (S.comparison (hrange (m + c + c)) (hker (m + c)) η) =
      Submodule.inclusion (Submodule.pow_smul_top_le I M₀
        ((Nat.le_add_right m c).trans (Nat.le_add_right (m + c) c))) η :=
  Subtype.ext (S.proj_comparison (hrange (m + c + c)) (hker (m + c)) η)

include hb hrange hker in
/-- **[Stacks, Tag 02OA] part (5)** in the abstract: the inverse systems `n ↦ M n` and
`n ↦ Iⁿ M₀` are pro-isomorphic.

The data are those the other clauses of the tag produce with one constant `c`: `hb` is part (2)
at degree `0`, `hrange` is the surjectivity of `Iⁿ ⊗ M₀ → Iⁿ M₀` read as a statement about the
image of `proj`, and `hker` is part (3). The reindexings are both `m ↦ m + c`, the forward maps
are the corestricted projections and the backward maps the comparison maps of part (4). -/
theorem proIso_powSmulFunctor :
    Nonempty (ProIso S.systemFunctor (powSmulFunctor I M₀)) := by
  refine ⟨{
    α := fun m ↦ m + c
    β := fun m ↦ m + c
    αmono := fun _ _ h ↦ Nat.add_le_add_right h c
    βmono := fun _ _ h ↦ Nat.add_le_add_right h c
    αle := fun m ↦ Nat.le_add_right m c
    βle := fun m ↦ Nat.le_add_right m c
    φ := fun m ↦ ModuleCat.ofHom (S.projCorestrict (hb m))
    ψ := fun m ↦ ModuleCat.ofHom (S.comparison (hrange (m + c)) (hker m))
    φnat := ?_
    ψnat := ?_
    ψφ := ?_
    φψ := ?_ }⟩
  · intro m m' h
    rw [tr_systemFunctor, tr_powSmulFunctor]
    ext z
    exact (S.inclusion_projCorestrict hb h z).symm
  · intro m m' h
    rw [tr_systemFunctor, tr_powSmulFunctor]
    ext η
    exact S.comparison_inclusion hrange hker h η
  · intro m
    rw [tr_systemFunctor]
    ext z
    exact S.comparison_projCorestrict hb hrange hker z
  · intro m
    rw [tr_powSmulFunctor]
    ext η
    exact S.projCorestrict_comparison hb hrange hker η

end ProIsoData

end ReesSystem

end Stacks.RingTheory

namespace Stacks.Cohomology.FormalFunctions

attribute [local instance] AlgebraicGeometry.modulesLinear baseSectionsAlgebra

variable {A : Type u} [CommRing A] (I : Ideal A) (X : Over (Spec (.of A)))
  (F : X.left.Modules) (p : ℕ)

/-- **[Stacks, Tag 02OA], part (5).**

For `A` Noetherian, `f : X → Spec A` proper and `ℱ` coherent, the inverse system
`n ↦ Hᵖ(X, Iⁿℱ)` and the ideal-power filtration `n ↦ IⁿHᵖ(X, ℱ)` of `Hᵖ(X, ℱ)` are
pro-isomorphic.

The hypothesis `h02O8` is [Stacks, Tag 02O8], carried in the same general form as in
`exists_uniform_bound_cohomology_surjective_range_le`: quantified over every Noetherian base
ring, every ideal of it, every proper scheme over it, every coherent module and every degree. -/
theorem proIso_cohomologyIdealPower [IsNoetherianRing A]
    (hX : AlgebraicGeometry.IsProper X.hom) (hF : SheafOfModules.IsCoherent F)
    (h02O8 : ∀ (A' : Type u) [CommRing A'] [IsNoetherianRing A'] (I' : Ideal A')
      (X' : Over (Spec (.of A'))) (_ : AlgebraicGeometry.IsProper X'.hom)
      (F' : X'.left.Modules) (_ : SheafOfModules.IsCoherent F') (p' : ℕ),
      (cohomologyIdealPowerSystem I' X' F' p').IsReesFinite) :
    Nonempty (InverseSequence.ProIso
      (cohomologyIdealPowerSystem I X F p).systemFunctor
      (Stacks.RingTheory.powSmulFunctor I (cohomology X F p))) := by
  obtain ⟨c, hproj, hker, -, -, -⟩ :=
    exists_uniform_bound_cohomology_surjective_range_le I X F hX hF p h02O8
  have hb : ∀ r : ℕ, LinearMap.range ((cohomologyIdealPowerSystem I X F p).proj (r + c)) ≤
      I ^ r • (⊤ : Submodule A (cohomology X F p)) := by
    intro r
    have h : LinearMap.range ((cohomologyIdealPowerSystem I X F p).proj (r + c)) ≤
        I ^ (r + c - c) • (⊤ : Submodule A (cohomology X F p)) :=
      hproj (r + c) (Nat.le_add_left c r)
    simpa using h
  have hk : ∀ r : ℕ, LinearMap.ker ((cohomologyIdealPowerSystem I X F p).proj (r + c)) =
      LinearMap.ker ((cohomologyIdealPowerSystem I X F p).tr (Nat.le_add_right r c)) :=
    fun r ↦ hker r (r + c) (le_refl (r + c))
  have hr : ∀ n : ℕ, I ^ n • (⊤ : Submodule A (cohomology X F p)) ≤
      LinearMap.range ((cohomologyIdealPowerSystem I X F p).proj n) :=
    pow_smul_le_range_cohomologyProj I X F p
  exact (cohomologyIdealPowerSystem I X F p).proIso_powSmulFunctor hb hr hk

end Stacks.Cohomology.FormalFunctions

end
