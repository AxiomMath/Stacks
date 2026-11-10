module

public import StacksFrontier.AlgebraicGeometry.DeRham.CoordinateBlowupFormsKernelCech
public import StacksFrontier.AlgebraicGeometry.DeRham.CoordinateBlowupHigherDirectImageVanishing
public import StacksFrontier.AlgebraicGeometry.DeRham.BlowupFormsKernelReduction
public import StacksFrontier.AlgebraicGeometry.DeRham.BlowupFormsDerivedReduction
import StacksCore.Tactic.StacksAttribute

/-!
# Clause (3) of Stacks 0FUR: the derived comparison on the coordinate blowup

Fix a ring `R`, `S = Spec R`, integers `m ≥ 0`, `n ≥ 1`, the coordinate blowup `b : L ⟶ X` of
`X = 𝐀^{m+n}_S` along `Z = 𝐀^m_S`, its exceptional divisor `j : E ⟶ L` and `a ≥ 0`. Clause (3)
of [Stacks, Tag 0FUR] says that `Rb_*Ω^a_{L/S} ⟶ i_*Rp_*Ω^a_{E/S}` is an isomorphism on
cohomology sheaves in degrees `≥ 1`. The comparison is `Rb_*` of the restriction
`Ω^a_{L/S} ⟶ j_*Ω^a_{E/S}` followed by the identification `Rb_*j_* = i_*Rp_*`, so the clause is
`Stacks.DeRham.isIso_coordinateFormsRestrictionHomology`: `H^q(Rb_*)` of the restriction is an
isomorphism for `q ≥ 1`; `Stacks.DeRham.isIso_homology_coordinateBlowupFormsDerivedComparison`
states it for the comparison map `Stacks.DeRham.blowupFormsDerivedComparison` itself.

## The proof

The restriction is surjective with kernel the sheaf `K` of forms vanishing on `E`, so the clause
follows once `H^q(Rb_*K) = 0` for `q ≥ 1`
(`Stacks.DeRham.isIso_formsRestrictionHomology_of_kernel`). Over the affine `X` this is the
vanishing of `H^q(L, K)`
(`Stacks.DeRham.isZero_homology_schemeDerivedPushforward_of_isZero_rightDerived`), which is the
Čech computation `Stacks.DeRham.CoordinateCech.isZero_rightDerived_formsKer`: in Laurent frame
coordinates the sections of `K` over the intersections of the standard charts are the coordinates
of positive weight, and the Čech complex of those is contractible in positive degrees. This is the
source's proof — the positive-weight pieces `Ω^a_{L/S,k}`, `k ≥ 1`, of `π_*Ω^a_{L/S}` have no
higher cohomology — read on the Čech complex of the charts, where the weights are the Laurent
degrees in the `y`'s.

## References

* [Stacks Project, Tag 0FUR](https://stacks.math.columbia.edu/tag/0FUR)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

attribute [local instance 10000] HasDerivedCategory.standard

namespace Stacks.DeRham

variable (R : Type u) [CommRing R] (m n : ℕ)

/-- **`H^q(Rb_*K) = 0` for `q ≥ 1`**, `K` the forms vanishing on the exceptional divisor. -/
theorem isZero_homology_derivedPushforward_coordinateFormsKer (hn : 0 < n) (a : ℕ) (q : ℤ)
    (hq : 1 ≤ q) :
    IsZero ((DerivedCategory.homologyFunctor _ q).obj
      ((schemeDerivedPushforward (coordinateBlowupToAmbient R m n)).obj
        ((DerivedCategory.singleFunctor _ 0).obj
          (kernel (Scheme.Hom.formsDirectImageComparison (coordinateExceptionalι R m n)
            (coordinateBlowupToBase R m n) (a : ℤ)))))) := by
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, q = k := ⟨q.toNat, by omega⟩
  exact isZero_homology_schemeDerivedPushforward_of_isZero_rightDerived _
    (CoordinateCech.formsKer R m n a) k
    (CoordinateCech.isZero_rightDerived_formsKer R m n hn a k (by omega))

/-- **[Stacks, Tag 0FUR], clause (3).** For `n ≥ 1`, every `a ≥ 0` and every `q ≥ 1`, the map
`H^q(Rb_*Ω^a_{L/S}) ⟶ H^q(Rb_*j_*Ω^a_{E/S})` induced by restricting forms to the exceptional
divisor is an isomorphism; `Rb_*j_*Ω^a_{E/S} = i_*Rp_*Ω^a_{E/S}`, see
`Stacks.DeRham.isIso_homology_coordinateBlowupFormsDerivedComparison` for the comparison map
itself. -/
@[stacks 0FUR "clause (3), in the setting of Section 0FUB, \
which fixes a ring R and sets S = Spec(R), Z = A^m_S ⊂ X = A^{m+n}_S with n ≥ 1"]
theorem isIso_coordinateFormsRestrictionHomology (hn : 1 ≤ n) (a : ℕ) (q : ℤ) (hq : 1 ≤ q) :
    IsIso (formsRestrictionHomology (coordinateBlowupToAmbient R m n) (coordinateExceptionalι R m n)
      (coordinateBlowupToAmbient R m n ≫ coordinateAmbientToBase R m n) a q) :=
  isIso_formsRestrictionHomology_of_kernel _ _ _ a
    (fun q hq => isZero_homology_derivedPushforward_coordinateFormsKer R m n (by omega) a q hq) hq

attribute [local instance] Stacks.MoreMorphisms.coordinateEmbedding_isClosedImmersion in
/-- **[Stacks, Tag 0FUR], clause (3), for the comparison map** `Rb_*Ω^a_{L/S} ⟶ i_*Rp_*Ω^a_{E/S}`
(`Stacks.DeRham.blowupFormsDerivedComparison` of the coordinate closed immersion
`i : Z = 𝐀^m_S ⟶ X`): for `n ≥ 1`, every `a ≥ 0` and every `q ≥ 1` it is an isomorphism on
`H^q`. -/
@[stacks 0FUR "clause (3), for the comparison map Rb_*Ω^a ⟶ i_*Rp_*Ω^a, \
in the setting of Section 0FUB, \
which fixes a ring R and sets S = Spec(R), Z = A^m_S ⊂ X = A^{m+n}_S with n ≥ 1"]
theorem isIso_homology_coordinateBlowupFormsDerivedComparison (hn : 1 ≤ n) (a : ℕ) (q : ℤ)
    (hq : 1 ≤ q) :
    IsIso ((DerivedCategory.homologyFunctor _ q).map
      (blowupFormsDerivedComparison (coordinateAmbientToBase R m n)
        (Stacks.MoreMorphisms.coordinateEmbedding R m n) (a : ℤ))) :=
  (isIso_homology_formsDerivedSquareComparison_iff _ _ a q).2
    (isIso_coordinateFormsRestrictionHomology R m n hn a q hq)

end Stacks.DeRham
