module

public import StacksFrontier.AlgebraicGeometry.ProjectiveBundleCohomology.LocalModel
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundleCohomology.ProjectiveSpacePairing

/-!
# Monomial bases of symmetric powers over an affine open

Given a quasicoherent module `E` on a scheme `S` and an affine open `V` such that `Γ(E, V)` is
free with a basis indexed by `Fin (m + 2)`, the symmetric powers `Sym^k_{Γ(S, V)}(Γ(E, V))` and
the sections `Γ(Sym^k(E), V)` have bases indexed by the monomials of degree `k`.

## Main definitions

* `pieceSectionsLinearEquiv`: The linear equivalence `Sym^k_{Γ(S, V)}(Γ(E, V)) ≃ Γ(Sym^k(E), V)`.
* `symPowMonomialBasis`: The monomial basis of `Sym^k_{Γ(S, V)}(Γ(E, V))`.
* `sectionMonomialBasis`: The monomial basis of `Γ(Sym^k(E), V)`.

## Main results

* `coe_symPowMonomialBasis`: The basis elements correspond to monomials in the symmetric algebra.
* `of_sectionMonomialBasis`: The basis elements of `Γ(Sym^k(E), V)` correspond to monomials under
  the identification of `Γ(V, Sym(E))` with the polynomial ring.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite AlgebraicGeometry

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

namespace Stacks.AlgebraicGeometry.ProjectiveBundleCohomology

open ProjectiveSpacePairing

variable {S : Scheme.{u}} (E : S.Modules) [E.IsQuasicoherent]
  (hqc : Stacks.SymGraded.IsQuasicoherentPieces E) {V : S.Opens} (hV : IsAffineOpen V)

/-- The sheafification unit `Sym^k_{Γ(S, V)}(Γ(E, V)) ≅ Γ(Sym^k(E), V)` over an affine open, as
a linear equivalence. -/
def pieceSectionsLinearEquiv (k : ℕ) :
    SymPow.symmetricPower k Γ(S, V) Γ(E, V) ≃ₗ[Γ(S, V)]
      Γ((Stacks.SymGraded.schemeSheafGradedAlgebra E hqc).piece (k : ℤ), V) where
  __ := Stacks.SymGraded.AffinePieces.pieceSectionsEquiv E hV (k : ℤ)
  map_smul' r x :=
    (PresheafOfModules.Hom.app (PresheafOfModules.sheafifyUnit (𝟙 S.ringCatSheaf.obj)
      (Stacks.SymGraded.siteGradedPiece E.val (k : ℤ))) (op V)).hom.map_smul
        (r : S.ringCatSheaf.obj.obj (op V)) x

variable {m : ℕ} (b : Module.Basis (Fin (m + 1 + 1)) Γ(S, V) Γ(E, V))

/-- The monomial basis of `Sym^k_{Γ(S, V)}(Γ(E, V))` attached to a basis of `Γ(E, V)`. -/
def symPowMonomialBasis (k : ℕ) :
    Module.Basis (Monomials m k) Γ(S, V) (SymPow.symmetricPower k Γ(S, V) Γ(E, V)) :=
  (MvPolynomial.basisRestrictSupport Γ(S, V) {d : Fin (m + 1 + 1) →₀ ℕ | d.degree = k}).map
    ((LinearEquiv.ofEq _ _
      (MvPolynomial.homogeneousSubmodule_eq_finsupp_supported _ Γ(S, V) k).symm).trans
      (SymPow.symmetricPowerEquivHomogeneousSubmodule b k).symm)

include hV in
/-- **The monomial basis of `Γ(Sym^k(E), V)`** over an affine open `V` with a basis of `Γ(E, V)`
indexed by `Fin (m + 2)`. -/
def sectionMonomialBasis (k : ℕ) :
    Module.Basis (Monomials m k) Γ(S, V)
      Γ((Stacks.SymGraded.schemeSheafGradedAlgebra E hqc).piece (k : ℤ), V) :=
  (symPowMonomialBasis E b k).map (pieceSectionsLinearEquiv E hqc hV k)

omit [E.IsQuasicoherent] in
/-- The element of `symPowMonomialBasis` indexed by a monomial `α` is the preimage of the
monomial `X^α` under the identification of `Sym^k_{Γ(S, V)}(Γ(E, V))` with the homogeneous
polynomials of degree `k`. -/
theorem symPowMonomialBasis_apply {k : ℕ} (α : Monomials m k) :
    symPowMonomialBasis E b k α = (SymPow.symmetricPowerEquivHomogeneousSubmodule b k).symm
      ⟨MvPolynomial.monomial α.1 1, (MvPolynomial.mem_homogeneousSubmodule _ _).2
        (MvPolynomial.isHomogeneous_monomial 1 α.2)⟩ := by
  apply (SymPow.symmetricPowerEquivHomogeneousSubmodule b k).injective
  rw [LinearEquiv.apply_symm_apply]
  apply Subtype.ext
  change ((SymPow.symmetricPowerEquivHomogeneousSubmodule b k
      ((SymPow.symmetricPowerEquivHomogeneousSubmodule b k).symm
        (LinearEquiv.ofEq _ _ (MvPolynomial.homogeneousSubmodule_eq_finsupp_supported _ Γ(S, V)
          k).symm ((AddMonoidAlgebra.supportedEquivFinsupp
            {d : Fin (m + 1 + 1) →₀ ℕ | d.degree = k}).symm (Finsupp.single α 1)))) :
      MvPolynomial (Fin (m + 1 + 1)) Γ(S, V)) = _)
  rw [LinearEquiv.apply_symm_apply]
  exact (congrArg AddMonoidAlgebra.ofCoeff (Finsupp.supportedEquivFinsupp_symm_single
    (R := Γ(S, V)) {d : Fin (m + 1 + 1) →₀ ℕ | d.degree = k} α (1 : Γ(S, V)))).trans
    (AddMonoidAlgebra.ofCoeff_single _ _)

omit [E.IsQuasicoherent] in
/-- In the symmetric algebra, the element of `symPowMonomialBasis` indexed by `α` is the preimage
of the monomial `X^α` under `SymmetricAlgebra.equivMvPolynomial`. -/
theorem coe_symPowMonomialBasis {k : ℕ} (α : Monomials m k) :
    (symPowMonomialBasis E b k α : SymmetricAlgebra Γ(S, V) Γ(E, V)) =
      (SymmetricAlgebra.equivMvPolynomial b).symm (MvPolynomial.monomial α.1 1) := by
  apply (SymmetricAlgebra.equivMvPolynomial b).injective
  rw [AlgEquiv.apply_symm_apply, symPowMonomialBasis_apply]
  exact congrArg Subtype.val
    ((SymPow.symmetricPowerEquivHomogeneousSubmodule b k).apply_symm_apply _)

/-- **The monomial basis is carried to the monomials by the identification of `Γ(V, Sym(E))`
with the polynomial ring.** -/
theorem of_sectionMonomialBasis {k : ℕ} (α : Monomials m k) :
    DirectSum.of ((Stacks.SymGraded.schemeSheafGradedAlgebra E hqc).sectionPieces V) k
        (sectionMonomialBasis E hqc hV b k α) =
      ofPolyGrading E hqc hV b (MvPolynomial.monomial α.1 1) := by
  apply (Stacks.SymGraded.AffinePieces.symSectionRingEquiv E hV hqc).injective
  refine (Stacks.SymGraded.AffinePieces.symSectionRingEquiv_of E hV hqc k _).trans ?_
  change ((Stacks.SymGraded.AffinePieces.pieceSectionsEquiv E hV (k : ℤ)).symm
      (Stacks.SymGraded.AffinePieces.pieceSectionsEquiv E hV (k : ℤ)
        (symPowMonomialBasis E b k α)) : SymmetricAlgebra Γ(S, V) Γ(E, V)) =
    Stacks.SymGraded.AffinePieces.symSectionRingEquiv E hV hqc
      ((Stacks.SymGraded.AffinePieces.symSectionRingEquiv E hV hqc).symm
        ((SymmetricAlgebra.equivMvPolynomial b).symm (MvPolynomial.monomial α.1 1)))
  exact (congrArg Subtype.val ((Stacks.SymGraded.AffinePieces.pieceSectionsEquiv E hV
    (k : ℤ)).symm_apply_apply _)).trans ((coe_symPowMonomialBasis E b α).trans
      (RingEquiv.apply_symm_apply _ _).symm)

end Stacks.AlgebraicGeometry.ProjectiveBundleCohomology

end
