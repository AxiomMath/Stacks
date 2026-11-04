module

public import StacksFrontier.AlgebraicGeometry.Quot.NumericalTensorPowerProductsAbsoluteApproximation
public import StacksFrontier.AlgebraicGeometry.Quot.NumericalTensorPowerProductsRebase

/-!
# `Coh^P_{X/B}` is an open and closed substack of `Coh_{X/B}`

Let `f : X ⟶ B` be a separated morphism of finite presentation of algebraic spaces over a scheme
`S`, let `E_1, …, E_r` be perfect objects of `D(𝒪_X)`, and let `P : ℤ^{⊕ r} ⟶ ℤ`.  For
`n ∈ ℤ^{⊕ r}` put `E_n = E_1^{⊗ n_1} ⊗ ⋯ ⊗ E_r^{⊗ n_r}`.  Stacks 0DNE asserts that the
subcategory `Coh^P_{X/B} ⊆ Coh_{X/B}` of the objects `(T, 𝓕)` with
`χ(X_t, (E_n)_t ⊗^𝐋 𝓕_t) = P(n)` for all `n` and all `t ∈ T` is an open and closed substack.

The question is étale local on `B`, so `B` may be taken affine; the base scheme `S` may be
replaced by `Spec ℤ`, the numerical invariants being unchanged; and then absolute Noetherian
approximation (Stacks 07SK, 0851 and 09RJ) presents the data as the base change of data over a
Noetherian affine scheme. Over a Noetherian base every object of `Coh` is locally pulled back
from one over a Noetherian test scheme, whose connected components are open.

## Main results

* `Space.NumericalSituation.isOpenAndClosedCondition_ofDerivedTensorPowerProducts`:
  `Coh^P_{X/B}` is an open and closed substack of `Coh_{X/B}`.

## Implementation notes

"Open and closed substack" is `AlgebraicGeometry.Space.CoherentSituation.IsOpenAndClosedCondition`:
for every object `(T, 𝓕)` of `Coh_{X/B}` there is an open and closed subscheme `U ⊆ T` such that
a morphism `(T', 𝓕') ⟶ (T, 𝓕)` lies in `Coh^P_{X/B}` exactly when `T' ⟶ T` factors through `U`;
this is the representability of the inclusion by open and closed immersions, written out on the
objects and morphisms of Stacks 08KB.  The invariants `χ` are the derived-fibre Euler
characteristics of `K_n = Rf_{T,*}((E_n)_T ⊗^𝐋 𝓕)`, which is perfect (Stacks 0A1P).

## References

* [Stacks Project, Tag 0DNE](https://stacks.math.columbia.edu/tag/0DNE)
* [Stacks Project, Tag 0DNC](https://stacks.math.columbia.edu/tag/0DNC)
* [Stacks Project, Tag 0DND](https://stacks.math.columbia.edu/tag/0DND)
* [Stacks Project, Tag 09RJ](https://stacks.math.columbia.edu/tag/09RJ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {D : CoherentSituation B S hS}

namespace NumericalSituation

open CoherentSituation

/-- Let `f : X ⟶ B` be a separated morphism of finite presentation of algebraic spaces,
`E_1, …, E_r` perfect objects of `D(𝒪_X)` and `P : ℤ^{⊕ r} ⟶ ℤ`.  Then the subcategory
`Coh^P_{X/B} ⊆ Coh_{X/B}` of the objects `(T, 𝓕)` with
`χ(X_t, (E_1^{⊗ n_1} ⊗ ⋯ ⊗ E_r^{⊗ n_r})_t ⊗^𝐋 𝓕_t) = P(n)` for all `n ∈ ℤ^{⊕ r}` and all
`t ∈ T` is an open and closed substack. -/
@[stacks 0DNE]
theorem isOpenAndClosedCondition_ofDerivedTensorPowerProducts (hf : IsSeparated B S hS D.f.hom)
    {r : ℕ}
    (E : Fin r → @DerivedCategory (Modules.{u, u} B S hS D.X.1 D.X.2) _ _
      (HasDerivedCategory.standard _))
    (hE : ∀ j, letI := HasDerivedCategory.standard (Modules.{u, u} B S hS D.X.1 D.X.2)
      (smallEtaleRingedSite B S hS D.X.1 D.X.2).IsPerfect (E j))
    (P : (Fin r → ℤ) → ℤ) :
    IsOpenAndClosedCondition D (ofDerivedTensorPowerProducts hf E hE P).HasNumericalInvariants := by
  let hZ := B.contains_terminal
  let h : B.obj hS ⟶ B.obj hZ := ObjectProperty.homMk (terminal.from S)
  refine isOpenAndClosedCondition_of_rebase h D hf E hE P ?_
  refine isOpenAndClosedCondition_of_isLocallyNoetherianPullbackAt _ ?_
  refine isLocallyNoetherianPullbackAt_of_affine_baseChange _ _ (isPerfect_rebaseObjects h D E hE)
    P fun W hW g A t => ?_
  exact isLocallyNoetherianPullbackAt_of_isAffine (T := ⟨W, hW⟩) _ (Iso.refl _) _ _ _ P A t

end NumericalSituation

end AlgebraicGeometry.Space

end
