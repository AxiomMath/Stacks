module

public import StacksFrontier.AlgebraicGeometry.Blowup.ReesAlgebra.BlowupTwist
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.DenseOpenAdmissibleBlowup.Basic

/-!
# The ample family on a dense open admissible blowup

A quasi-compact and quasi-separated scheme with finitely many irreducible components has a
quasi-compact dense open `U` and a `U`-admissible blowup carrying an ample family of invertible
modules. The construction of `U`, of the centre and of the effective Cartier divisors on the
blowup is
`Stacks.DenseOpenAdmissibleBlowup.exists_admissibleBlowup_effectiveCartierCover`; the invertible
module ample on the complement of each divisor is the degree-one twist of the blowup, which is
relatively ample by [Stacks, Tag 02NS] part (2); and the ample family is then
[Stacks, Tag 0GTS] (`Stacks.AmpleFamilyCartier.exists_isAmpleFamily_of_isAmpleOnComplement_cover`).

## Main results

* `Stacks.DenseOpenAdmissibleBlowup.exists_isCompact_dense_admissibleBlowup_isAmpleFamily`:
  [Stacks, Tag 0GTT].

## References

* [Stacks Project, Tag 0GTT](https://stacks.math.columbia.edu/tag/0GTT)
* [Stacks Project, Tag 0GTS](https://stacks.math.columbia.edu/tag/0GTS)
* [Stacks Project, Tag 02NS](https://stacks.math.columbia.edu/tag/02NS)
-/

@[expose] public section

open CategoryTheory TopologicalSpace AlgebraicGeometry

universe u

namespace Stacks.DenseOpenAdmissibleBlowup

/-- **[Stacks, Tag 0GTT].** Let `X` be a quasi-compact and quasi-separated scheme with finitely
many irreducible components. There exist a quasi-compact dense open `U ⊆ X` and a `U`-admissible
blowup `X' ⟶ X` such that `X'` has an ample family of invertible modules. -/
@[stacks 0GTT]
public theorem exists_isCompact_dense_admissibleBlowup_isAmpleFamily
    (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X]
    [Finite (irreducibleComponents X)] :
    ∃ U : X.Opens, IsCompact (U : Set X) ∧ Dense (U : Set X) ∧
      ∃ (X' : Scheme.{u}) (f : X' ⟶ X), Stacks.Blowup.IsAdmissibleBlowup U f ∧
        ∃ (J : Type u) (N : J → X'.Modules), X'.IsAmpleFamily N :=
  exists_isCompact_dense_isAdmissibleBlowup_isAmpleFamily X
    fun K => (reesSituation K).twistTransition 1

/-- **[Stacks, Tag 0GTT] at prescribed generic points.** Let `X` be a quasi-compact and
quasi-separated scheme and let `η 0, …, η (n-1)` be the generic points of finitely many distinct
irreducible components of `X`. There are a quasi-compact open `U` containing every `η i` and a
finite type ideal `I` such that the blowup `blowUp I ⟶ X` is a `U`-admissible blowup and
`blowUp I` has an ample family of invertible modules. For all the irreducible components of a
scheme with finitely many of them this is
`Stacks.DenseOpenAdmissibleBlowup.exists_isCompact_dense_admissibleBlowup_isAmpleFamily`. -/
public theorem exists_isCompact_admissibleBlowup_isAmpleFamily_of_genericPoints
    (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X] {n : ℕ} (Z : Fin n → Set X)
    (hZ : ∀ i, Z i ∈ irreducibleComponents X) (hinj : Function.Injective Z) (η : Fin n → X)
    (hη : ∀ i, IsGenericPoint (η i) (Z i)) :
    ∃ (U : X.Opens) (I : X.IdealSheafData), IsCompact (U : Set X) ∧ (∀ i, η i ∈ U) ∧
      I.IsFiniteType ∧ Stacks.Blowup.IsAdmissibleBlowup U (blowUpToBase I) ∧
        ∃ (J : Type u) (N : J → (blowUp I).Modules), (blowUp I).IsAmpleFamily N :=
  exists_isCompact_isAdmissibleBlowup_isAmpleFamily_of_genericPoints X Z hZ hinj η hη
    fun K => (reesSituation K).twistTransition 1

end Stacks.DenseOpenAdmissibleBlowup

end
