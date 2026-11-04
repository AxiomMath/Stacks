module

public import Mathlib.Algebra.Module.CharacterModule
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Module.CharacterModule.Duality
public import StacksFrontier.Algebra.Module.Pure.Defs
public import StacksFrontier.Homology.TorAmplitude.Termwise
public import StacksFrontier.RingTheory.Flat.UniversallyExact
public import StacksFrontier.RingTheory.Flat.UniversallyInjective

/-!
# Pure injective modules

The character module `Hom_ℤ(M, ℚ/ℤ)` is pure injective, a module is pure injective exactly when
the evaluation map into its double character module splits, and every module embeds into a pure
injective one by a universally exact injection.

## References

* [Stacks Project, Tag 0700](https://stacks.math.columbia.edu/tag/0700)
* [Stacks Project, Tag 0701](https://stacks.math.columbia.edu/tag/0701)
-/

@[expose] public section

namespace CharacterModule

section

universe u v


/-- Evaluation into the double character module is universally injective. -/
public theorem universallyInjective_evalₗ (R : Type u) [CommRing R]
    (M : Type v) [AddCommGroup M] [Module R M] :
    UniversallyInjective (evalₗ R M) := by
  intro Q _ _
  rw [← LinearMap.lTensor_inj_iff_rTensor_inj, ← CharacterModule.dual_surjective_iff_injective]
  intro χ
  let ξ : Q →ₗ[R] CharacterModule M := CharacterModule.homEquiv.symm χ
  let s : CharacterModule M →ₗ[R]
      CharacterModule (CharacterModule (CharacterModule M)) :=
    { toFun := fun c ↦
        { toFun := fun d ↦ d c
          map_zero' := rfl
          map_add' := fun _ _ ↦ rfl }
      map_add' := by
        intro c d
        ext e
        exact e.map_add c d
      map_smul' := by
        intro r c
        ext e
        rfl }
  refine ⟨CharacterModule.homEquiv (s.comp ξ), ?_⟩
  apply CharacterModule.ext
  intro x
  induction x using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | tmul q m => rfl
  | add x y hx hy => rw [map_add, map_add, hx, hy]

end

end CharacterModule

namespace Module

section

universe u v

/-- The character module `Hom_ℤ(M, ℚ/ℤ)` of any module `M` over a commutative ring is pure
injective. -/
@[stacks 0700 "character_module_pure_injective"]
public theorem characterModule_pureInjective (A : Type u) [CommRing A]
    (M : Type v) [AddCommGroup M] [Module A M] :
    Module.PureInjective A (CharacterModule M) := by
  intro K X N _ _ _ _ _ _ f g hf hg hfg hfu
  exact ⟨LinearMap.lcomp_injective_of_surjective g hg,
    rTensor_injective_iff_lcomp_surjective.mp (hfu M),
    (LinearMap.exact_lcomp_of_exact_of_surjective (CharacterModule M)
      (LinearMap.exact_iff.mpr hfg.symm) hg).linearMap_ker_eq.symm⟩

end

section

universe u v

private theorem pureInjective_of_retract (A : Type u) [CommRing A]
    (I J : Type v) [AddCommGroup I] [Module A I] [AddCommGroup J] [Module A J]
    (hJ : Module.PureInjective A J)
    (i : I →ₗ[A] J) (r : J →ₗ[A] I) (hri : r.comp i = LinearMap.id) :
    Module.PureInjective A I := by
  intro K M N _ _ _ _ _ _ f g hf hg hfg hui
  obtain ⟨hinj, hsurj, hex⟩ := hJ K M N f g hf hg hfg hui
  have hl (P : Type v) [AddCommGroup P] [Module A P] :
      Function.LeftInverse (LinearMap.compRight A r : (P →ₗ[A] J) →ₗ[A] (P →ₗ[A] I))
        (LinearMap.compRight A i) := fun φ ↦ by
    ext p
    exact congrArg (fun q : I →ₗ[A] I => q (φ p)) hri
  refine ⟨?_, ?_, ?_⟩
  · intro φ ψ hφψ
    exact (hl N).injective (hinj (congrArg (LinearMap.compRight A i) hφψ))
  · intro φ
    obtain ⟨ψ, hψ⟩ := hsurj ((LinearMap.compRight A i) φ)
    exact ⟨(LinearMap.compRight A r) ψ, (congrArg (LinearMap.compRight A r) hψ).trans (hl K φ)⟩
  · apply le_antisymm
    · intro φ hφ
      rcases hφ with ⟨ψ, rfl⟩
      ext k
      have hk : g (f k) = 0 := LinearMap.mem_ker.mp (hfg ▸ ⟨k, rfl⟩)
      simp [LinearMap.lcomp_apply, hk]
    · intro φ hφ
      have hφJker : (LinearMap.lcomp A J f) ((LinearMap.compRight A i) φ) = 0 := by
        ext k
        have hk : φ (f k) = 0 := by
          simpa only [LinearMap.lcomp_apply, LinearMap.zero_apply] using
            congrArg (fun q : K →ₗ[A] I => q k) (LinearMap.mem_ker.mp hφ)
        simp [LinearMap.lcomp_apply, hk]
      obtain ⟨ψ, hψ⟩ : (LinearMap.compRight A i) φ ∈
          LinearMap.range (LinearMap.lcomp A J g) := by
        rw [hex]
        exact LinearMap.mem_ker.mpr hφJker
      exact ⟨(LinearMap.compRight A r) ψ, (congrArg (LinearMap.compRight A r) hψ).trans (hl M φ)⟩

/-- A module is pure injective if and only if evaluation into its double character
module has a linear retraction. -/
@[stacks 0700 "pure_injective_iff_double_dual_splits"]
public theorem pureInjective_iff_evalₗ_splits (A : Type u) [CommRing A]
    (I : Type v) [AddCommGroup I] [Module A I] :
    Module.PureInjective A I ↔
      ∃ r : CharacterModule (CharacterModule I) →ₗ[A] I,
        r.comp (CharacterModule.evalₗ A I) = LinearMap.id := by
  refine ⟨fun hI ↦ ?_, fun ⟨r, hr⟩ ↦ pureInjective_of_retract A I _
    (characterModule_pureInjective A (CharacterModule I)) (CharacterModule.evalₗ A I) r hr⟩
  obtain ⟨r, hr⟩ := (hI I (CharacterModule (CharacterModule I))
    (CharacterModule (CharacterModule I) ⧸ LinearMap.range (CharacterModule.evalₗ A I))
    (CharacterModule.evalₗ A I) (LinearMap.range (CharacterModule.evalₗ A I)).mkQ
    (CharacterModule.evalₗ_injective A I) (Submodule.mkQ_surjective _)
    (Submodule.ker_mkQ _).symm (CharacterModule.universallyInjective_evalₗ A I)).2.1 LinearMap.id
  exact ⟨r, hr⟩

end

section

universe u v

/-- Every module embeds universally injectively into a pure injective module, with a
surjective cokernel map making the resulting sequence exact. -/
@[stacks 0700 "exists_pure_injective_universally_exact_extension"]
public theorem exists_pureInjective_universallyExact_extension
    (A : Type u) [CommRing A] (M : Type v) [AddCommGroup M] [Module A M] :
    ∃ (I N : Type v)
      (_ : AddCommGroup I) (_ : Module A I)
      (_ : AddCommGroup N) (_ : Module A N)
      (f : M →ₗ[A] I) (g : I →ₗ[A] N),
      Function.Injective f ∧
        Function.Surjective g ∧
          LinearMap.range f = LinearMap.ker g ∧
            UniversallyInjective f ∧ Module.PureInjective A I := by
  let f := CharacterModule.evalₗ A M
  refine ⟨CharacterModule (CharacterModule M), _ ⧸ LinearMap.range f,
    inferInstance, inferInstance, inferInstance, inferInstance, f,
    Submodule.mkQ (LinearMap.range f), CharacterModule.evalₗ_injective A M,
    Submodule.mkQ_surjective _, by simp, CharacterModule.universallyInjective_evalₗ A M,
    characterModule_pureInjective A (CharacterModule M)⟩

end

section

universe u v


variable {A : Type u} [CommRing A]

/-- A cochain complex is universally exact if it is exact in every degree and stays exact
after tensoring with every module. -/
structure UniversallyExactComplex (M : ℤ → Type u)
    [∀ i, AddCommGroup (M i)] [∀ i, Module A (M i)]
    (d : ∀ i, M i →ₗ[A] M (i + 1)) : Prop where
  /-- The original complex is exact in every degree. -/
  exact : ∀ i, Function.Exact (d i) (d (i + 1))
  /-- Tensoring the complex with any module preserves exactness in every degree. -/
  baseChange_exact : ∀ (Q : Type u) [AddCommGroup Q] [Module A Q] (i : ℤ),
    Function.Exact ((d i).rTensor Q) ((d (i + 1)).rTensor Q)

/-- The differential of a complex, corestricted to the kernel of the following differential. -/
def toNextKernel {M : ℤ → Type u} [∀ i, AddCommGroup (M i)] [∀ i, Module A (M i)]
    (d : ∀ i, M i →ₗ[A] M (i + 1)) (h : UniversallyExactComplex M d) (i : ℤ) :
    M i →ₗ[A] LinearMap.ker (d (i + 1)) :=
  (d i).codRestrict (LinearMap.ker (d (i + 1))) fun x =>
    Function.Exact.apply_apply_eq_zero (h.exact i) x

/-- If `L → M → N` is exact and remains exact after every tensor product, then the
inclusion of the image of `M → N` in `N` is universally injective. -/
@[stacks 0701 "part (1)"]
theorem universallyInjective_range_subtype
    {L M N : Type v} [AddCommGroup L] [AddCommGroup M] [AddCommGroup N]
    [Module A L] [Module A M] [Module A N]
    (f : L →ₗ[A] M) (g : M →ₗ[A] N)
    (hexact : Function.Exact f g)
    (h : ∀ (Q : Type v) [AddCommGroup Q] [Module A Q],
      Function.Exact (f.rTensor Q) (g.rTensor Q)) :
    UniversallyInjective (LinearMap.range g).subtype := by
  intro Q _ _
  exact StacksDraft.TorAmplitude.Termwise.rTensor_range_subtype_injective_of_exact f g
    (Function.Exact.linearMap_comp_eq_zero hexact) Q (h Q)

/-- The kernel-to-term-to-next-kernel sequences of a universally exact complex are
universally exact short exact sequences. -/
@[stacks 0701 "part (2)"]
theorem kernel_universallyExact
    {M : ℤ → Type u} [∀ i, AddCommGroup (M i)] [∀ i, Module A (M i)]
    (d : ∀ i, M i →ₗ[A] M (i + 1)) (h : UniversallyExactComplex M d) (i : ℤ) :
    UniversallyExact (LinearMap.ker (d i)).subtype (toNextKernel d h i) := by
  obtain ⟨i, rfl⟩ : ∃ j : ℤ, j + 1 + 1 = i := ⟨i - 2, by omega⟩
  refine ⟨Subtype.val_injective, ?_, ?_, ?_⟩
  · intro x
    obtain ⟨y, hy⟩ := (h.exact (i + 1 + 1) x.1).mp x.2
    exact ⟨y, Subtype.ext hy⟩
  · rw [LinearMap.exact_iff, show LinearMap.ker (toNextKernel d h (i + 1 + 1)) =
        LinearMap.ker (d (i + 1 + 1)) from LinearMap.ker_codRestrict _ _ _]
    exact (Submodule.range_subtype _).symm
  · rw [LinearMap.exact_iff.mp (h.exact (i + 1))]
    exact universallyInjective_range_subtype (d i) (d (i + 1)) (h.exact i) fun Q =>
      h.baseChange_exact Q i

end

end Module

end
