module

public import StacksFrontier.AlgebraicGeometry.ImmersionEvaluationSurjective.JetQuotient

/-!
# The local equation of a section, read against the square of the maximal ideal

Let `ℒ` be an invertible module on a scheme `X` and let `s` be a section of `ℒ`. A
trivialization of `ℒ` over an open `V` through a point `x` turns `s` into a function on `V`, its
*local equation*, and the question whether `s` vanishes to second order at `x` — whether its
germ lies in `𝔪_x²ℒ_x` — becomes the question whether the germ of that function lies in `𝔪_x²`.

This equivalence is the bridge between the two halves of the Jacobian criterion in the proof of
[Stacks, Tag 0FD6]. On one side the evaluation `ev_x` of a linear system is a map into
`ℒ_x/𝔪_x²ℒ_x`, so `ev_x(v) = 0` says exactly that the germ of `ψ(v)` lies in `𝔪_x²ℒ_x`. On the
other side the regularity criterion
`AlgebraicGeometry.isRegularLocalRing_stalk_of_ker_stalkMap_eq_span_singleton` asks for a
generator of the kernel of a stalk map avoiding `𝔪_x²`, and that generator is a local equation.

## Main results

* `Stacks.LocalEquationJet.mem_maximalSqSmul_iff_germ_triv_mem`: **a section lies in `𝔪_x²ℒ_x`
  exactly when its local equation lies in `𝔪_x²`**, for a section over the trivializing open.
* `Stacks.LocalEquationJet.Γgerm_mem_maximalSqSmul_iff`: the same for a global section, whose
  local equation is `Stacks.NonvanishingOpen.trivTop`.
* `Stacks.LocalEquationJet.mem_maximalIdealSq_iff_of_span_eq`: two generators of one ideal of
  the local ring lie in `𝔪_x²` together, which is how a local equation produced by one
  trivialization formalism is compared with one produced by another.

## Implementation notes

The trivialization formalism here is `Stacks.SheafDescent.Trivialization`, the sectionwise one,
because that is the formalism in which the stalk of an invertible module is known to be free of
rank one (`Stacks.StalkJet.stalkEquiv`). The isomorphism `𝒪_{X,x} ≃ ℒ_x` it supplies carries
the ideal `𝔪_x²`, read as the submodule `𝔪_x²·𝒪_{X,x}`, onto `𝔪_x²ℒ_x`
(`Stacks.StalkJet.map_stalkEquiv_smul_top`), and the local equation is by construction the
element of `𝒪_{X,x}` that it sends to the germ of the section.

The other formalism, a trivialization written as an isomorphism `ℒ|_U ≅ 𝒪_U` of sheaves of
modules over the restricted structure sheaf, produces its local equation through
`Stacks.Divisors.frameSections`. The two are reconciled by
`Stacks.LocalEquationJet.mem_maximalIdealSq_iff_of_span_eq`: `𝔪_x²` is an ideal, so whether a
generator of a principal ideal belongs to it depends only on the ideal, not on the generator.

No `@[stacks]` attribute is attached: this is a step inside the proof of Tag 0FD6.

## References

* [Stacks Project, Tag 0FD6](https://stacks.math.columbia.edu/tag/0FD6)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory IsLocalRing TopologicalSpace Opposite

universe u

namespace Stacks.LocalEquationJet

open Stacks.ModuleStalk Stacks.NonvanishingOpen Stacks.SectionProduct Stacks.StalkJet
open Stacks.ImmersionEvaluationSurjective

variable {X : Scheme.{u}} {M : X.Modules} {V : X.Opens}
  (t : Stacks.SheafDescent.Trivialization X.presheaf M.val V) {x : X} (hx : x ∈ V)

/-- **The germ of a section is the image of the germ of its local equation** under the
isomorphism `𝒪_{X,x} ≃ ℒ_x` of the trivialization. -/
theorem stalkEquiv_germ_triv (u : Γ(M, V)) :
    stalkEquiv t hx ((X.presheaf.germ V x hx).hom (triv t (𝟙 V) u)) =
      (M.presheaf.germ V x hx).hom u := by
  rw [stalkEquiv_apply, ← germ_smul]
  exact congrArg (M.presheaf.germ V x hx).hom (eq_triv_smul_basis t u).symm

/-- **A section lies in `𝔪_x²ℒ_x` exactly when its local equation lies in `𝔪_x²`.** The
trivialization identifies `ℒ_x` with `𝒪_{X,x}` carrying `𝔪_x²ℒ_x` onto `𝔪_x²`, and the local
equation is the element corresponding to the germ of the section. -/
theorem mem_maximalSqSmul_iff_germ_triv_mem (u : Γ(M, V)) :
    (M.presheaf.germ V x hx).hom u ∈ maximalSqSmul M x ↔
      (X.presheaf.germ V x hx).hom (triv t (𝟙 V) u) ∈ maximalIdeal (X.presheaf.stalk x) ^ 2 := by
  have key : maximalSqSmul M x =
      Submodule.map (stalkEquiv t hx).toLinearMap
        (maximalIdeal (X.presheaf.stalk x) ^ 2 •
          (⊤ : Submodule (X.presheaf.stalk x) (X.presheaf.stalk x))) :=
    (map_stalkEquiv_smul_top t hx _).symm
  have hsmul : (maximalIdeal (X.presheaf.stalk x) ^ 2 •
      (⊤ : Submodule (X.presheaf.stalk x) (X.presheaf.stalk x))) =
      maximalIdeal (X.presheaf.stalk x) ^ 2 := by simp
  rw [← stalkEquiv_germ_triv t hx u, key, Submodule.mem_map_equiv, LinearEquiv.symm_apply_apply,
    hsmul]

/-- **A global section lies in `𝔪_x²ℒ_x` exactly when its local equation lies in `𝔪_x²`.** -/
theorem Γgerm_mem_maximalSqSmul_iff (s : Γ(M, ⊤)) :
    (M.presheaf.Γgerm x).hom s ∈ maximalSqSmul M x ↔
      (X.presheaf.germ V x hx).hom (trivTop t s) ∈ maximalIdeal (X.presheaf.stalk x) ^ 2 := by
  rw [← TopCat.Presheaf.Γgerm_res_apply (i := homOfLE (le_top : V ≤ ⊤)) M.presheaf x hx s]
  exact mem_maximalSqSmul_iff_germ_triv_mem t hx _

/-- **Two generators of one principal ideal of the local ring lie in `𝔪_x²` together.** The
square of the maximal ideal is an ideal, so `a ∈ 𝔪²` says no more than `(a) ⊆ 𝔪²`.

This is how a local equation computed in one trivialization formalism is compared with one
computed in another: both generate the ideal of the zero scheme in the local ring, so neither
the choice of trivializing open nor the shape of the trivialization matters. -/
theorem mem_maximalIdealSq_iff_of_span_eq {R : Type u} [CommRing R] [IsLocalRing R] {a b : R}
    (hab : Ideal.span ({a} : Set R) = Ideal.span ({b} : Set R)) :
    a ∈ maximalIdeal R ^ 2 ↔ b ∈ maximalIdeal R ^ 2 := by
  rw [← Ideal.span_singleton_le_iff_mem, ← Ideal.span_singleton_le_iff_mem, hab]

end Stacks.LocalEquationJet

end
