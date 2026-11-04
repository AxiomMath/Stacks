module

public import Mathlib.Algebra.Algebra.Pi
public import StacksFrontier.RingTheory.DiscreteValuationRing.EppSolution
public import StacksFrontier.RingTheory.DiscreteValuationRing.Solution

/-!
# Descending a weak solution from the completed situation

This file formalises the third step of the Stacks Project proof of Epp's theorem
(Tag 09F9): the reduction of the existence of a weak solution *from* the completed
situation back down to the original one.

The geometry of the step is a commutative square of extensions of discrete valuation
rings
$$
\begin{matrix} B & \to & B^\wedge \\ \uparrow & & \uparrow \\ A & \to & A^\wedge \end{matrix}
$$
with fraction fields `K → K^`, `L → L^`.  Given a finite extension `M/K^` which is a
weak solution for `A^ → B^`, Tag 09EJ produces a finite extension `K₁/K` with
`K^ ⊗_K K₁ = M`.  Tags 09E7, 09EQ and 09EM then say that the integral closures `A₁`
of `A` in `K₁` and `A₁^` of `A^` in `M` are discrete valuation rings with
`A₁ → A₁^` formally smooth in the adic topology, i.e. that `K₁/K` is a *solution*, in
particular a weak solution, for `A → A^`.  Feeding these two weak solutions into the
composition half of Tag 09ES gives that `K₁/K` is a weak solution for `A → B^`, and the
descent half of Tag 09ES then gives that `K₁/K` is a weak solution for `A → B`.

## Main results

* `IsDiscreteValuationRing.isWeakSolution_of_isWeakSolution_completion`: the two
  applications of Tag 09ES which turn a weak solution for `A^ → B^` along `M/K^` into a
  weak solution for `A → B` along `K₁/K`.

## Implementation notes

A "weak solution" is not a bare predicate on the field `K₁`; it is
`IsDiscreteValuationRing.IntegralClosureBaseChange.IsWeakSolution` applied to a
base-change *data package* recording the reduced compositum and the two integral
closures (Tag 09EM).  There is no general constructor for such a package in this
development, so the four packages appearing in the square — for `A → B`, `A → A^`,
`A → B^` and `A^ → B^` — are hypotheses of the statement below, as is the
identification of the reduced compositum `(K^ ⊗_K K₁)_{red}` with `M` supplied by
Tag 09EJ.  The theorem is therefore the *transport* content of the step: everything
special to completions is isolated into the single hypothesis that `K₁/K` is a weak
solution for `A → A^`, which is what Tags 09E7, 09EQ and 09EM provide and which is the
only place completeness of `A^` is used.  No completeness hypothesis is imposed here:
the square is taken abstractly, and the statement is correspondingly more general than
the source paragraph.

Since `M/K^` is a field — the compositum of the source's step (b) — the product
decomposition demanded by the composition half of Tag 09ES is the one-factor product,
which is why the equivalence hypothesis is stated as an equivalence with `M` itself and
transported along `AlgEquiv.funUnique`.

All ten carrier types and all twelve presentation universes of the four packages are
independent.

## References

* [The Stacks Project, Tag 09F9](https://stacks.math.columbia.edu/tag/09F9)
* [The Stacks Project, Tag 09ES](https://stacks.math.columbia.edu/tag/09ES)
-/

@[expose] public section

open scoped TensorProduct

namespace IsDiscreteValuationRing

universe uA uAc uB uBc uK uKc uL uLc uK₁ uM w₁ w₂ w₃ x₁ x₂ x₃ y₁ y₂ y₃ z₁ z₂ z₃

namespace IntegralClosureBaseChange

/-- The reduced compositum `L₁` recorded by a base-change package is `L`-isomorphic to any
*field* that the unreduced tensor product `L ⊗[K] K₁` is `L`-isomorphic to.

Tag 09EJ delivers its finite extension in the form of an isomorphism `K^ ⊗_K K₁ ≅ M` with
the unreduced tensor product, whereas the base-change package of Tag 09EM records the
reduced compositum `(L ⊗[K] K₁) / √0`.  When the target is a field the tensor product is
already reduced, so the nilradical is zero and the two descriptions agree.  This lemma is
the translation between them. -/
theorem nonempty_algEquiv_l₁_of_tensorProduct_algEquiv
    {A : Type uA} {B : Type uB} {K : Type uK} {L : Type uL} {K₁ : Type uK₁} {M : Type uM}
    [CommRing A] [CommRing B] [Field K] [Field L] [Field K₁] [Field M]
    [IsDomain A] [IsDomain B] [IsDiscreteValuationRing A] [IsDiscreteValuationRing B]
    [Algebra A B] [Algebra A K] [Algebra A L] [Algebra B L]
    [Algebra K L] [Algebra K K₁] [Algebra A K₁] [Algebra L M]
    [IsExtension A B] [IsFractionRing A K] [IsFractionRing B L]
    [IsScalarTower A B L] [IsScalarTower A K L] [IsScalarTower A K K₁]
    [Module.Finite K K₁]
    (D : IntegralClosureBaseChange.{uA, uB, uK, uL, uK₁, w₁, w₂, w₃} A B K L K₁)
    (e : (L ⊗[K] K₁) ≃ₐ[L] M) :
    letI := D.commRingL₁
    letI := D.algebraLL₁
    Nonempty (D.L₁ ≃ₐ[L] M) := by
  let _ := D.commRingL₁
  let _ := D.algebraLL₁
  let _ := D.algebraKL₁
  -- Being isomorphic to a field, the tensor product is reduced, so its nilradical is zero.
  have hker : nilradical (L ⊗[K] K₁) =
      RingHom.ker (e.toAlgHom : (L ⊗[K] K₁) →ₐ[L] M) := by
    rw [nilradical_eq_bot_iff.mpr (isReduced_of_injective e.toRingHom e.injective)]
    exact ((RingHom.injective_iff_ker_eq_bot
      (e.toAlgHom : (L ⊗[K] K₁) →ₐ[L] M).toRingHom).mp e.injective).symm
  -- `D.eL₁` is only recorded as a `K`-algebra equivalence; `D.eL₁_left` upgrades it to `L`.
  have hcomm : ∀ x : L, D.eL₁.toRingEquiv (algebraMap L D.L₁ x) =
      algebraMap L ((L ⊗[K] K₁) ⧸ nilradical (L ⊗[K] K₁)) x := by
    intro x
    have h1 : algebraMap L ((L ⊗[K] K₁) ⧸ nilradical (L ⊗[K] K₁)) x =
        Ideal.Quotient.mk _ (x ⊗ₜ[K] (1 : K₁)) := rfl
    simpa [Algebra.TensorProduct.includeLeft_apply, h1] using D.eL₁_left x
  exact ⟨(AlgEquiv.ofRingEquiv (R := L) hcomm).trans
    ((Ideal.quotientEquivAlgOfEq L hker).trans
      (Ideal.quotientKerAlgEquivOfSurjective e.surjective))⟩

end IntegralClosureBaseChange

/-- **Step 3 of Stacks 09F9.**  Let
`A → B`, `A → A^`, `A^ → B^` and `B → B^` be extensions of discrete valuation rings
forming a commutative square, with fraction fields `K`, `L`, `K^`, `L^` (the intended
case is that `A^` and `B^` are the completions of `A` and `B`, but completeness is not
used).  Let `K₁/K` and `M/K^` be finite extensions, and let `D_AB`, `D_AAc`, `D_ABc`,
`D_AcBc` be the base-change packages of Tag 09EM for `A → B` along `K₁`, for `A → A^`
along `K₁`, for `A → B^` along `K₁`, and for `A^ → B^` along `M`.

If `M/K^` is a weak solution for `A^ → B^`, if `K₁/K` is a weak solution for `A → A^`
(this is what Tags 09E7, 09EQ and 09EM supply when `A^` is the completion of `A`), and
if the reduced compositum `(K^ ⊗_K K₁)_{red}` recorded by `D_AAc` is `K^`-isomorphic to
`M` (this is what Tag 09EJ supplies), then `K₁/K` is a weak solution for `A → B`.

The proof is the composition half of Tag 09ES applied to the tower `A → A^ → B^`,
followed by the descent half of Tag 09ES applied to the tower `A → B → B^`. -/
theorem isWeakSolution_of_isWeakSolution_completion
    (A : Type uA) (Ac : Type uAc) (B : Type uB) (Bc : Type uBc)
    (K : Type uK) (Kc : Type uKc) (L : Type uL) (Lc : Type uLc)
    (K₁ : Type uK₁) (M : Type uM)
    [CommRing A] [CommRing Ac] [CommRing B] [CommRing Bc]
    [IsDomain A] [IsDomain Ac] [IsDomain B] [IsDomain Bc]
    [IsDiscreteValuationRing A] [IsDiscreteValuationRing Ac]
    [IsDiscreteValuationRing B] [IsDiscreteValuationRing Bc]
    [Field K] [Field Kc] [Field L] [Field Lc] [Field K₁] [Field M]
    [Algebra A Ac] [Algebra A B] [Algebra A Bc] [Algebra Ac Bc] [Algebra B Bc]
    [Algebra A K] [Algebra A Kc] [Algebra A L] [Algebra A Lc] [Algebra A K₁]
    [Algebra Ac Kc] [Algebra Ac Lc] [Algebra Ac M]
    [Algebra B L] [Algebra B Lc] [Algebra Bc Lc]
    [Algebra K Kc] [Algebra K L] [Algebra K Lc] [Algebra K K₁]
    [Algebra Kc Lc] [Algebra Kc M] [Algebra L Lc]
    [IsExtension A Ac] [IsExtension A B] [IsExtension A Bc]
    [IsExtension Ac Bc] [IsExtension B Bc]
    [IsFractionRing A K] [IsFractionRing Ac Kc]
    [IsFractionRing B L] [IsFractionRing Bc Lc]
    [Module.Finite K K₁] [Module.Finite Kc M]
    [IsScalarTower A Ac Bc] [IsScalarTower A Ac Kc] [IsScalarTower A Ac Lc]
    [IsScalarTower Ac Bc Lc] [IsScalarTower A Bc Lc] [IsScalarTower Ac Kc Lc]
    [IsScalarTower Ac Kc M]
    [IsScalarTower A B Bc] [IsScalarTower A B L] [IsScalarTower A B Lc]
    [IsScalarTower B Bc Lc] [IsScalarTower B L Lc]
    [IsScalarTower A K Kc] [IsScalarTower A K L] [IsScalarTower A K Lc]
    [IsScalarTower K Kc Lc] [IsScalarTower K L Lc] [IsScalarTower A K K₁]
    (D_AB : IntegralClosureBaseChange.{uA, uB, uK, uL, uK₁, y₁, y₂, y₃} A B K L K₁)
    (D_AAc : IntegralClosureBaseChange.{uA, uAc, uK, uKc, uK₁, w₁, w₂, w₃} A Ac K Kc K₁)
    (D_ABc : IntegralClosureBaseChange.{uA, uBc, uK, uLc, uK₁, x₁, x₂, x₃} A Bc K Lc K₁)
    (D_AcBc : IntegralClosureBaseChange.{uAc, uBc, uKc, uLc, uM, z₁, z₂, z₃} Ac Bc Kc Lc M)
    (hAAc : D_AAc.IsWeakSolution) (hAcBc : D_AcBc.IsWeakSolution) :
    letI := D_AAc.commRingL₁
    letI := D_AAc.algebraLL₁
    Nonempty (D_AAc.L₁ ≃ₐ[Kc] M) → D_AB.IsWeakSolution := by
  let _ := D_AAc.commRingL₁
  let _ := D_AAc.algebraLL₁
  rintro ⟨eM⟩
  -- Composition along the tower `A → A^ → B^`: `K₁/K` is a weak solution for `A → B^`.
  have hABc : D_ABc.IsWeakSolution :=
    ((weakSolutions_and_solutions_go_down_and_compose A Ac Bc K Kc Lc K₁ D_AAc D_ABc).2
      1 (fun _ => M) Nat.one_pos ⟨eM.trans (AlgEquiv.funUnique Kc (Fin 1) M).symm⟩
      (fun _ => D_AcBc)).1 ⟨hAAc, fun _ => hAcBc⟩
  -- Descent along the tower `A → B → B^`: `K₁/K` is a weak solution for `A → B`.
  exact (weakSolutions_and_solutions_go_down_and_compose.{uA, uB, uBc, uK, uL, uLc, uK₁,
    uM, y₁, y₂, y₃, x₁, x₂, x₃, z₁, z₂, z₃} A B Bc K L Lc K₁ D_AB D_ABc).1.1 hABc

/-- **Step 3 of Stacks 09F9**, with the output of Tag 09EJ in its literal form.

This is `isWeakSolution_of_isWeakSolution_completion` with the hypothesis about the reduced
compositum replaced by a `K^`-isomorphism `K^ ⊗_K K₁ ≅ M` of the *unreduced* tensor product,
which is exactly what Tag 09EJ produces.  The translation is
`IntegralClosureBaseChange.nonempty_algEquiv_l₁_of_tensorProduct_algEquiv`. -/
theorem isWeakSolution_of_isWeakSolution_completion_of_tensorProduct_algEquiv
    (A : Type uA) (Ac : Type uAc) (B : Type uB) (Bc : Type uBc)
    (K : Type uK) (Kc : Type uKc) (L : Type uL) (Lc : Type uLc)
    (K₁ : Type uK₁) (M : Type uM)
    [CommRing A] [CommRing Ac] [CommRing B] [CommRing Bc]
    [IsDomain A] [IsDomain Ac] [IsDomain B] [IsDomain Bc]
    [IsDiscreteValuationRing A] [IsDiscreteValuationRing Ac]
    [IsDiscreteValuationRing B] [IsDiscreteValuationRing Bc]
    [Field K] [Field Kc] [Field L] [Field Lc] [Field K₁] [Field M]
    [Algebra A Ac] [Algebra A B] [Algebra A Bc] [Algebra Ac Bc] [Algebra B Bc]
    [Algebra A K] [Algebra A Kc] [Algebra A L] [Algebra A Lc] [Algebra A K₁]
    [Algebra Ac Kc] [Algebra Ac Lc] [Algebra Ac M]
    [Algebra B L] [Algebra B Lc] [Algebra Bc Lc]
    [Algebra K Kc] [Algebra K L] [Algebra K Lc] [Algebra K K₁]
    [Algebra Kc Lc] [Algebra Kc M] [Algebra L Lc]
    [IsExtension A Ac] [IsExtension A B] [IsExtension A Bc]
    [IsExtension Ac Bc] [IsExtension B Bc]
    [IsFractionRing A K] [IsFractionRing Ac Kc]
    [IsFractionRing B L] [IsFractionRing Bc Lc]
    [Module.Finite K K₁] [Module.Finite Kc M]
    [IsScalarTower A Ac Bc] [IsScalarTower A Ac Kc] [IsScalarTower A Ac Lc]
    [IsScalarTower Ac Bc Lc] [IsScalarTower A Bc Lc] [IsScalarTower Ac Kc Lc]
    [IsScalarTower Ac Kc M]
    [IsScalarTower A B Bc] [IsScalarTower A B L] [IsScalarTower A B Lc]
    [IsScalarTower B Bc Lc] [IsScalarTower B L Lc]
    [IsScalarTower A K Kc] [IsScalarTower A K L] [IsScalarTower A K Lc]
    [IsScalarTower K Kc Lc] [IsScalarTower K L Lc] [IsScalarTower A K K₁]
    (D_AB : IntegralClosureBaseChange.{uA, uB, uK, uL, uK₁, y₁, y₂, y₃} A B K L K₁)
    (D_AAc : IntegralClosureBaseChange.{uA, uAc, uK, uKc, uK₁, w₁, w₂, w₃} A Ac K Kc K₁)
    (D_ABc : IntegralClosureBaseChange.{uA, uBc, uK, uLc, uK₁, x₁, x₂, x₃} A Bc K Lc K₁)
    (D_AcBc : IntegralClosureBaseChange.{uAc, uBc, uKc, uLc, uM, z₁, z₂, z₃} Ac Bc Kc Lc M)
    (hAAc : D_AAc.IsWeakSolution) (hAcBc : D_AcBc.IsWeakSolution)
    (e : (Kc ⊗[K] K₁) ≃ₐ[Kc] M) :
    D_AB.IsWeakSolution :=
  isWeakSolution_of_isWeakSolution_completion A Ac B Bc K Kc L Lc K₁ M
    D_AB D_AAc D_ABc D_AcBc hAAc hAcBc
    (IntegralClosureBaseChange.nonempty_algEquiv_l₁_of_tensorProduct_algEquiv D_AAc e)

end IsDiscreteValuationRing
