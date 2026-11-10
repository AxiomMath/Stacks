module

public import StacksCore.CategoryTheory.Abelian.DeltaFunctor.Basic
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-!
# Dimension shifting for a `δ`-functor precomposed with an exact functor out of modules

Let `E` be a `δ`-functor from an abelian category `𝒜`, and let `Φ : ModuleCat R ⥤ 𝒜` be an exact
functor. If `Eᑫ⁺¹ ∘ Φ` vanishes on every module and `Eᑫ ∘ Φ` vanishes on every free module, then
`Eᑫ ∘ Φ` vanishes on every module: present a module as a quotient of a free one and read off the
long exact sequence.

## Main results

* `Stacks.Duality.ProjCoeff.isZero_of_isZero_free_of_isZero_succ`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v w

namespace Stacks.Duality.ProjCoeff

variable {R : Type u} [CommRing R]

/-- The free module on the underlying set of `L`, surjecting onto `L`. -/
noncomputable def freeCover (L : ModuleCat.{u} R) : ModuleCat.{u} R := ModuleCat.of R (L →₀ R)

/-- The canonical surjection from `freeCover L` onto `L`. -/
noncomputable def freeCoverπ (L : ModuleCat.{u} R) : freeCover L ⟶ L :=
  ModuleCat.ofHom (Finsupp.linearCombination R id)

/-- The canonical surjection `freeCoverπ L` is an epimorphism: the basis vector
`Finsupp.single x 1` is a preimage of `x`. -/
theorem epi_freeCoverπ (L : ModuleCat.{u} R) : Epi (freeCoverπ L) := by
  rw [ModuleCat.epi_iff_surjective]
  intro x
  refine ⟨Finsupp.single x 1, ?_⟩
  change Finsupp.linearCombination R id (Finsupp.single x 1) = x
  simp

/-- The short exact sequence `0 ⟶ ker ⟶ freeCover L ⟶ L ⟶ 0`. -/
noncomputable def freeCoverShortComplex (L : ModuleCat.{u} R) : ShortComplex (ModuleCat.{u} R) :=
  ShortComplex.mk (kernel.ι (freeCoverπ L)) (freeCoverπ L) (kernel.condition _)

/-- The presentation `0 ⟶ ker (freeCoverπ L) ⟶ freeCover L ⟶ L ⟶ 0` of a module by a free one is
short exact. -/
theorem freeCoverShortComplex_shortExact (L : ModuleCat.{u} R) :
    (freeCoverShortComplex L).ShortExact := by
  have he := epi_freeCoverπ L
  have : Mono (freeCoverShortComplex L).f := by dsimp [freeCoverShortComplex]; infer_instance
  exact ShortComplex.ShortExact.mk'
    (ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel (freeCoverπ L))) this he

variable {𝒜 : Type v} [Category.{w} 𝒜] [Abelian 𝒜] {ℬ : Type*} [Category ℬ] [Abelian ℬ]

/-- **Dimension shifting.** -/
theorem isZero_of_isZero_free_of_isZero_succ (E : CategoryTheory.DeltaFunctor 𝒜 ℬ)
    (Φ : ModuleCat.{u} R ⥤ 𝒜) [PreservesFiniteLimits Φ] [PreservesFiniteColimits Φ] (q : ℕ)
    (hfree : ∀ L : ModuleCat.{u} R, IsZero ((E.functor q).obj (Φ.obj (freeCover L))))
    (hsucc : ∀ L : ModuleCat.{u} R, IsZero ((E.functor (q + 1)).obj (Φ.obj L)))
    (L : ModuleCat.{u} R) : IsZero ((E.functor q).obj (Φ.obj L)) := by
  have hS : ((freeCoverShortComplex L).map Φ).ShortExact :=
    (freeCoverShortComplex_shortExact L).map_of_exact Φ
  have hex := E.exact_δ₁ hS q
  exact hex.isZero_X₂ ((hfree L).eq_of_src _ _) ((hsucc _).eq_of_tgt _ _)

end Stacks.Duality.ProjCoeff
