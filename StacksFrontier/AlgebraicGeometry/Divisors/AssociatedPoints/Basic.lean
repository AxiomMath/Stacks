module

public import Mathlib.CategoryTheory.Abelian.ShortExact
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints
public import StacksFrontier.AlgebraicGeometry.Morphisms.Support.Defs
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FlatShortExactSequence
public import StacksFrontier.Topology.Sheaves.Cohomology.KFlat.FlatModuleSheavesAndStalks
public import StacksCore.Tactic.StacksAttribute

/-!
# Associated points, the support, and short exact sequences

The associated points of a sheaf of modules on a scheme lie in its support, a monomorphism of
sheaves of modules induces an inclusion of associated points, and the associated points of the
middle term of a short exact sequence lie in the union of those of the outer terms.

## Main results

* `AlgebraicGeometry.associatedPoints_subset_support`: `Ass(F)` is contained in the support
  of `F`.
* `AlgebraicGeometry.associatedPoints_subset_of_mono`: the associated points of a subsheaf are
  associated points of the ambient sheaf.
* `AlgebraicGeometry.associatedPoints_subset_union_of_shortExact`: the associated points of the
  middle term of a short exact sequence lie in the union of those of the outer terms.

## Implementation notes

The source states these for quasi-coherent sheaves, but none of the three arguments uses
quasi-coherence: they all take place in the stalks, where exactness of the stalk functor and
the corresponding statements for modules over the local ring suffice. They are therefore stated
for every sheaf of modules.

A short exact sequence is represented by a `CategoryTheory.ShortComplex` together with its
`ShortExact` property; the induced short exact sequence of stalks is
`Stacks.SheafOfModules.FlatShortExact.stalkShortExact`.

## References

* [Stacks Project, Tag 05AD](https://stacks.math.columbia.edu/tag/05AD)
* [Stacks Project, Tag 05AE](https://stacks.math.columbia.edu/tag/05AE)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- **Stacks Project, Tag 05AD.** Every associated point of a sheaf of modules lies in its
support. -/
@[stacks 05AD]
lemma associatedPoints_subset_support {X : Scheme.{u}} (F : X.Modules) :
    Stacks.Divisors.associatedPoints F ⊆ SheafOfModules.supp F := fun x hx =>
  (SheafOfModules.mem_supp_iff_nontrivial_stalk
    (show SheafOfModules X.ringCatSheaf from F) x).mpr hx.nontrivial

/-- An injective linear map preserves the annihilator ideal of an element. -/
private theorem colon_span_singleton_map_eq {R M N : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] (g : M →ₗ[R] N)
    (hg : Function.Injective g) (m : M) :
    (⊥ : Submodule R N).colon (Submodule.span R {g m}) =
      (⊥ : Submodule R M).colon (Submodule.span R {m}) := by
  ext r
  rw [Submodule.mem_colon_span_singleton, Submodule.mem_bot, ← map_smul, map_eq_zero_iff g hg,
    Submodule.mem_colon_span_singleton, Submodule.mem_bot]

/-- An injective map of modules carries exact-annihilator associated primes to
exact-annihilator associated primes. -/
private theorem associatedPrimeStacks_subset_of_injective {R M N : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] (g : M →ₗ[R] N)
    (hg : Function.Injective g) :
    {p : Ideal R | IsAssociatedPrimeStacks R M p} ⊆
      {p : Ideal R | IsAssociatedPrimeStacks R N p} := by
  rintro p ⟨hp, m, hm⟩
  exact ⟨hp, g m, (colon_span_singleton_map_eq g hg m).trans hm⟩

/-- **Stacks Project, Tag 05AE.** The associated points of a subsheaf are associated points of
the ambient sheaf. -/
@[stacks 05AE "associated_points_subsheaf_subset"]
theorem associatedPoints_subset_of_mono {X : Scheme.{u}} {F₁ F₂ : X.Modules} (f : F₁ ⟶ F₂)
    [Mono f] :
    Stacks.Divisors.associatedPoints F₁ ⊆ Stacks.Divisors.associatedPoints F₂ := by
  intro x hx
  simp only [Stacks.Divisors.mem_associatedPoints_iff,
    Stacks.Divisors.IsAssociatedPoint] at hx ⊢
  have hmg : Mono ((PresheafOfModules.toPresheaf _).map f.val) := by
    have hval : Mono f.val := by
      let M₁ : SheafOfModules X.ringCatSheaf := F₁
      let M₂ : SheafOfModules X.ringCatSheaf := F₂
      let ff : M₁ ⟶ M₂ := f
      have : Mono ff := ‹Mono f›
      change Mono ((SheafOfModules.forget X.ringCatSheaf).map ff)
      exact Functor.map_mono _ ff
    exact Functor.map_mono _ f.val
  change IsAssociatedPrimeStacks _ (OXModule.stalk F₁ x) _ at hx
  exact associatedPrimeStacks_subset_of_injective (OXModule.stalkLinearMap F₁ F₂ f x)
    (OXModule.inj_of_mono_val F₁ F₂ f hmg x) hx

/-- Over a local ring, the maximal ideal is an exact-annihilator associated prime of the middle
term of a short exact sequence only if it is one for an outer term. -/
private lemma associatedPrimeStacks_maximal_subset_union_of_shortExact {R M₁ M₂ M₃ : Type*}
    [CommRing R] [IsLocalRing R] [AddCommGroup M₁] [Module R M₁] [AddCommGroup M₂]
    [Module R M₂] [AddCommGroup M₃] [Module R M₃] (f : M₁ →ₗ[R] M₂) (g : M₂ →ₗ[R] M₃)
    (hf : Function.Injective f) (hfg : Function.Exact f g) :
    IsAssociatedPrimeStacks R M₂ (IsLocalRing.maximalIdeal R) →
      IsAssociatedPrimeStacks R M₁ (IsLocalRing.maximalIdeal R) ∨
        IsAssociatedPrimeStacks R M₃ (IsLocalRing.maximalIdeal R) := by
  rintro ⟨hprime, m, hm⟩
  by_cases hgm : g m = 0
  · obtain ⟨n, hn⟩ := (hfg m).mp hgm
    exact Or.inl ⟨hprime, n, by rw [← colon_span_singleton_map_eq f hf, hn, hm]⟩
  · let J : Ideal R := (⊥ : Submodule R M₃).colon (Submodule.span R {g m})
    have hpJ : IsLocalRing.maximalIdeal R ≤ J := by
      intro r hr
      rw [← hm] at hr
      apply Submodule.mem_colon_span_singleton.mpr
      have hrm : r • m = 0 := by simpa using (Submodule.mem_colon_span_singleton.mp hr)
      change r • g m = 0
      rw [← map_smul, hrm, map_zero]
    have hJne : J ≠ ⊤ := by
      intro htop
      have h1 : (1 : R) ∈ J := by rw [htop]; simp
      have hy0 : g m = 0 := by
        have hmem : (1 : R) • g m ∈ (⊥ : Submodule R M₃) :=
          Submodule.mem_colon_span_singleton.mp h1
        simpa using hmem
      exact hgm hy0
    exact Or.inr ⟨hprime, g m, le_antisymm (IsLocalRing.le_maximalIdeal hJne) hpJ⟩

/-- **Stacks Project, Tag 05AE.** The associated points of the middle term of a short exact
sequence lie in the union of those of its outer terms. -/
@[stacks 05AE "associated_points_middle_subset_union"]
theorem associatedPoints_subset_union_of_shortExact {X : Scheme.{u}}
    (S : ShortComplex X.Modules) (hS : S.ShortExact) :
    Stacks.Divisors.associatedPoints S.X₂ ⊆
      Stacks.Divisors.associatedPoints S.X₁ ∪ Stacks.Divisors.associatedPoints S.X₃ := by
  intro x hx
  let : Module (X.presheaf.stalk x) (Stacks.SheafOfModules.FlatShortExact.abStalk S.X₁ x) :=
    Stacks.SheafOfModules.FlatShortExact.stalkModule S.X₁ x
  let : Module (X.presheaf.stalk x) (Stacks.SheafOfModules.FlatShortExact.abStalk S.X₂ x) :=
    Stacks.SheafOfModules.FlatShortExact.stalkModule S.X₂ x
  let : Module (X.presheaf.stalk x) (Stacks.SheafOfModules.FlatShortExact.abStalk S.X₃ x) :=
    Stacks.SheafOfModules.FlatShortExact.stalkModule S.X₃ x
  obtain ⟨f, g, hf, hfg, -⟩ := Stacks.SheafOfModules.FlatShortExact.stalkShortExact S hS x
  exact associatedPrimeStacks_maximal_subset_union_of_shortExact f g hf hfg hx

end AlgebraicGeometry
