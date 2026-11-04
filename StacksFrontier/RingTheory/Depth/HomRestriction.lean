module

public import Mathlib.Algebra.Category.ModuleCat.Ext.Baer
public import Mathlib.RingTheory.Depth.Rees
public import StacksFrontier.RingTheory.Depth.Defs.Defs
public import StacksFrontier.RingTheory.Depth.Nakayama

/-!
# Depth at least two from homomorphisms off the maximal ideal

Let `(R, 𝔪)` be a Noetherian local ring and `M` a nonzero finite `R`-module. Restriction along
the inclusion `𝔪 ⊆ R` is a map

`Hom_R(R, M) ⟶ Hom_R(𝔪, M)`,

and `M` has depth at least two as soon as that map is bijective. Injectivity says that no nonzero
element of `M` is killed by `𝔪`, which is the vanishing of `Hom_R(R/𝔪, M)`; surjectivity is
Baer's extension property for `𝔪`, which is the vanishing of `Ext^1_R(R/𝔪, M)`. By the Rees
theorem the vanishing of `Ext^i_R(R/𝔪, M)` for `i < 2` produces an `M`-regular sequence of
length two in `𝔪`, and the depth is by definition the supremum of the lengths of such sequences.

## Main results

* `Module.two_le_depth_of_bijective_restrict_maximalIdeal`: the criterion above.

## Implementation notes

The two `Ext` vanishings are read off Mathlib: `ModuleCat.ext_quotient_one_subsingleton_iff` is
Baer's criterion, and `CategoryTheory.Abelian.Ext.homEquiv₀` identifies `Ext^0` with the
homomorphism group. Mathlib states both for `R ⧸ 𝔪` shrunk into the module universe, so the two
transports between `Shrink (R ⧸ 𝔪)` and `R ⧸ 𝔪` are carried explicitly;
`ModuleCat.exists_isRegular_tfae` is the Rees theorem in the same spelling.

The second branch of `Module.depth` is a supremum over regular sequences, so the sequence the
Rees theorem produces bounds it below directly.

## References

* [Stacks Project, Tag 00LW](https://stacks.math.columbia.edu/tag/00LW)
* [Stacks Project, Tag 0EY0](https://stacks.math.columbia.edu/tag/0EY0)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Abelian Pointwise

universe u

namespace Module

/-- Let `(R, 𝔪)` be a Noetherian local ring and `M` a nonzero finite `R`-module. If every
`R`-linear map `𝔪 → M` extends uniquely to `R`, that is, if restriction along `𝔪 ⊆ R` is a
bijection `Hom_R(R, M) → Hom_R(𝔪, M)`, then `depth_𝔪(M) ≥ 2`. -/
public theorem two_le_depth_of_bijective_restrict_maximalIdeal {R : Type u} [CommRing R]
    [IsNoetherianRing R] [IsLocalRing R] (M : Type u) [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Nontrivial M]
    (h : Function.Bijective fun g : R →ₗ[R] M =>
      g.comp (IsLocalRing.maximalIdeal R).subtype) :
    (2 : ℕ∞) ≤ Module.depth R (IsLocalRing.maximalIdeal R) M := by
  classical
  set I : Ideal R := IsLocalRing.maximalIdeal R
  have hne : I • (⊤ : Submodule R M) ≠ ⊤ := Module.maximalIdeal_smul_top_ne_top M
  have hlt : I • (⊤ : Submodule R M) < ⊤ := lt_of_le_of_ne le_top hne
  have hhom : Subsingleton ((R ⧸ I) →ₗ[R] M) := by
    refine ⟨fun φ ψ => ?_⟩
    have hcomp : (φ.comp I.mkQ).comp I.subtype = (ψ.comp I.mkQ).comp I.subtype := by
      ext x
      have hx : I.mkQ (x : R) = 0 := by
        show Submodule.Quotient.mk (x : R) = 0
        rw [Submodule.Quotient.mk_eq_zero]
        exact x.property
      show φ (I.mkQ (x : R)) = ψ (I.mkQ (x : R))
      rw [hx, map_zero, map_zero]
    have hmaps : φ.comp I.mkQ = ψ.comp I.mkQ := h.1 hcomp
    refine LinearMap.ext fun q => ?_
    obtain ⟨r, rfl⟩ := I.mkQ_surjective q
    exact congrArg (fun g : R →ₗ[R] M => g r) hmaps
  have hsub : Subsingleton (ModuleCat.of R (Shrink.{u} (R ⧸ I)) ⟶ ModuleCat.of R M) :=
    (ModuleCat.homEquiv.trans
      ((Shrink.linearEquiv R (R ⧸ I)).arrowCongr (LinearEquiv.refl R M)).toEquiv).subsingleton
  have h0 : Subsingleton (Ext (ModuleCat.of R (Shrink.{u} (R ⧸ I))) (ModuleCat.of R M) 0) :=
    Ext.homEquiv₀.subsingleton
  have h1 : Subsingleton (Ext (ModuleCat.of R (Shrink.{u} (R ⧸ I))) (ModuleCat.of R M) 1) :=
    (ModuleCat.ext_quotient_one_subsingleton_iff (ModuleCat.of R M) I).mpr fun g => by
      obtain ⟨g', hg'⟩ := h.2 g
      exact ⟨g', fun x hx => LinearMap.congr_fun hg' ⟨x, hx⟩⟩
  obtain ⟨rs, hlen, hmem, hreg⟩ :=
    ((ModuleCat.exists_isRegular_tfae I 2 (ModuleCat.of R M) hlt).out 2 4).mp (by
      intro i hi
      interval_cases i
      · exact h0
      · exact h1)
  rw [Module.depth, ite_eq_right hne]
  exact le_iSup₂_of_le rs ⟨hmem, hreg⟩ (by exact_mod_cast hlen.ge)

end Module

end
