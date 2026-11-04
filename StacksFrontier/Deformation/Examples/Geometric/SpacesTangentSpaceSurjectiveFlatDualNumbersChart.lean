module

public import StacksFrontier.RingTheory.Flat.DualNumbersSquareZeroChart

/-!
# Flatness over the dual numbers from the affine charts of a thickening

Let `i : U₀ ⟶ U'` and `j : S ⟶ S'` be closed immersions of schemes and `α : U' ⟶ S'` a morphism
over `f₀ : U₀ ⟶ S`, where `S'` has a single point and `Γ(S', 𝒪) ≅ k[ε]` with `j` cutting out
`ε = 0`. Suppose that on every affine open `O ⊆ U'` the ring `Γ(U', O)` is an extension of
`Γ(U₀, i⁻¹O)` whose ideal is `Γ(U₀, i⁻¹O)` itself, multiplication by the pullback of `ε` being
the inclusion of the reduction. Then `α` is flat and `U₀ = S ×_{S'} U'`. This is the scheme form
of `Stacks.Thickenings.flat_and_ker_eq_of_dualNumbers`, glued by
`Stacks.Thickenings.flat_and_isPullback_of_affine` ((2) ⟹ (1) of Stacks 063Y).

## Main results

* `AlgebraicGeometry.flat_and_isPullback_of_dualNumbers_chart`.

## References

* [Stacks Project, Tag 063Y](https://stacks.math.columbia.edu/tag/063Y)
* [Stacks Project, Tag 0E41](https://stacks.math.columbia.edu/tag/0E41)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry

variable {k : Type u} [Field k] {U₀ U' S S' : Scheme.{u}}

/-- **Flatness over the dual numbers from the affine charts.** For closed immersions
`i : U₀ ⟶ U'`, `j : S ⟶ S'` and `α : U' ⟶ S'` over `f₀ : U₀ ⟶ S`, with `S'` a single point,
`Γ(S', 𝒪) ≅ k[ε]` and `j` cutting out `ε = 0`: if on every affine open `O ⊆ U'` the kernel of
`Γ(U', O) ⟶ Γ(U₀, i⁻¹O)` is a copy of `Γ(U₀, i⁻¹O)` on which `ε` acts as the reduction, then
`α` is flat and the square is cartesian. -/
theorem flat_and_isPullback_of_dualNumbers_chart (i : U₀ ⟶ U') (j : S ⟶ S')
    [IsClosedImmersion i] [IsClosedImmersion j] (f₀ : U₀ ⟶ S) (α : U' ⟶ S')
    (comm : i ≫ α = f₀ ≫ j) [Subsingleton S']
    (e : TrivSqZeroExt k k ≃+* Γ(S', ⊤))
    (he : ∀ a : TrivSqZeroExt k k, (j.appTop).hom (e a) = 0 ↔ a.fst = 0)
    (hchart : ∀ (O : U'.Opens), IsAffineOpen O → ∀ hO : O ≤ α ⁻¹ᵁ ⊤,
      Function.Surjective (i.app O).hom ∧
      ∃ incl : Γ(U₀, i ⁻¹ᵁ O) →+ Γ(U', O), Function.Injective incl ∧
        (∀ c, (α.appLE ⊤ O hO).hom (e (TrivSqZeroExt.inr 1)) * c = incl ((i.app O).hom c)) ∧
        (∀ c, (i.app O).hom c = 0 → ∃ d, incl d = c) ∧
        (∀ d, (i.app O).hom (incl d) = 0) ∧
        ∀ d d', incl d * incl d' = 0) :
    Flat α ∧ IsPullback i f₀ α j := by
  refine Stacks.Thickenings.flat_and_isPullback_of_affine f₀ α comm
    fun V hV O hO hOV => ?_
  by_cases hVe : (V : Set S') = ∅
  · have hV0 : V = ⊥ := TopologicalSpace.Opens.ext (by rw [hVe]; rfl)
    subst hV0
    have hO0 : O = ⊥ := le_bot_iff.mp (hOV.trans (by
      intro x hx
      exact absurd hx (by simp)))
    subst hO0
    refine ⟨Subsingleton.elim _ _, ?_⟩
    let := (α.appLE ⊥ ⊥ hOV).hom.toAlgebra
    exact Module.Flat.of_free
  · obtain ⟨y, hy⟩ := Set.nonempty_iff_ne_empty.mpr hVe
    have hVt : V = ⊤ := TopologicalSpace.Opens.ext (Set.eq_univ_of_forall fun z =>
      (Subsingleton.elim z y) ▸ hy)
    subst hVt
    obtain ⟨hsurj, incl, hinj, hmul, hexact, hπincl, hsq⟩ := hchart O hO hOV
    let ψ : TrivSqZeroExt k k →+* Γ(U', O) := (α.appLE ⊤ O hOV).hom.comp e.toRingHom
    obtain ⟨hflat, hker⟩ := Stacks.Thickenings.flat_and_ker_eq_of_dualNumbers ψ (i.app O).hom
      hsurj incl hinj hmul hexact hπincl hsq
    have hjker : j.ker.ideal ⟨⊤, hV⟩ =
        Ideal.map e.toRingHom (RingHom.ker (TrivSqZeroExt.fstHom k k k).toRingHom) := by
      rw [Scheme.Hom.ker_apply]
      ext x
      obtain ⟨a, rfl⟩ := e.surjective x
      have hm : e a ∈ Ideal.map e.toRingHom
          (RingHom.ker (TrivSqZeroExt.fstHom k k k).toRingHom) ↔
          a ∈ RingHom.ker (TrivSqZeroExt.fstHom k k k).toRingHom := by
        refine ⟨fun h => ?_, Ideal.mem_map_of_mem _⟩
        simpa only [Ideal.comap_map_of_bijective e.toRingHom e.bijective] using
          (Ideal.mem_comap (f := e.toRingHom)).mpr h
      rw [RingHom.mem_ker, hm, RingHom.mem_ker]
      exact he a
    refine ⟨?_, ?_⟩
    · rwa [Scheme.Hom.ker_apply, hjker, Ideal.map_map]
    · have h : (α.appLE ⊤ O hOV).hom = ψ.comp e.symm.toRingHom := by
        ext x
        simp [ψ]
      rw [h]
      exact RingHom.Flat.comp (RingHom.Flat.of_bijective e.symm.bijective) hflat

end AlgebraicGeometry
