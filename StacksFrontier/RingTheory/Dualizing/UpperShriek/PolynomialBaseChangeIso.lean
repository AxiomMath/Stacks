module

public import StacksFrontier.RingTheory.Dualizing.DerivedHomBaseChange.DiagonalLargeUniverse
public import StacksFrontier.RingTheory.Dualizing.UpperShriek.FlatAlgebraBaseChange
public import StacksFrontier.RingTheory.Dualizing.UpperShriek.FlatBaseChange
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Base change of trivial duality along a field extension of a polynomial algebra

Let `k ⊆ K` be an extension of fields, let `P = k[x_1, …, x_n]` and `P_K = K[x_1, …, x_n]`, and
let `A` be a `P`-algebra which is perfect as a `P`-module.  Writing `A_K = A ⊗_P P_K`, the
canonical base-change morphism of [stacks 0E29],
`RHom_P(A, -) ⊗_A^L A_K ⟶ RHom_{P_K}(A_K, - ⊗_P^L P_K)`,
is an isomorphism; at the unit `P` of `D(P)` it is the comparison
`RHom_P(A, P) ⊗_A^L A_K ⟶ RHom_{P_K}(A_K, P_K)`.

## Main results

* `RingTheory.TorIndependence.torIndependent_of_flat_right` — an `R`-algebra which is flat is Tor
  independent over `R` from every `R`-algebra.
* `Dualizing.flat_mvPolynomial_of_flat` — adjoining variables preserves flatness of a base change:
  `R[x_1, …, x_n] → R'[x_1, …, x_n]` is flat whenever `R → R'` is.
* `Dualizing.mvPolynomialBaseChangeTensorRingEquiv` — the identification `A ⊗_P P_K ≃ A ⊗_k K`.
* `Dualizing.isIso_derivedTensorHomDiagonal_mvPolynomial` — the tensor--Hom diagonal of
  [stacks 0BYN] at `P_K`, `P` and `A` is invertible; this is the unconditional half of the
  criterion of [stacks 0E2A].
* `Dualizing.isIso_derivedHomBaseChange_mvPolynomial` — the base-change morphism of [stacks 0E29]
  is invertible, as a natural transformation.
* `Dualizing.isIso_derivedHomBaseChange_mvPolynomial_app_unit` — the displayed comparison at the
  unit of `D(P)`.

## Implementation notes

The two derived extensions of scalars enter as arguments together with the comparison morphisms
exhibiting their universal properties, as they do throughout the base change of [stacks 0E29]:
unbounded derived extension of scalars is not packaged, and taking arbitrary models makes the
conclusion stronger than it would be at a fixed one.  The pushout corner is `A ⊗_P P_K` with its
two canonical inclusions, and `Dualizing.mvPolynomialBaseChangeTensorRingEquiv` identifies it with
the base change `A ⊗_k K` of `A` along the field extension.

`P_K` is the base change of `P` along `k → K`, hence flat over `P`; this is what makes `A` and
`P_K` Tor independent over `P` whatever `A` is, so the Tor-independence hypothesis of
[stacks 0E29] costs nothing here.  The target of the comparison at the unit is
`RHom_{P_K}(A ⊗_P P_K, P ⊗_P^L P_K)`, the second argument being the unit `P_K` of `D(P_K)` read
through the chosen model of derived extension of scalars rather than identified with it.

Perfectness of `A` over `P` is the finiteness hypothesis of
[stacks 0BZP]; it is available for a flat algebra of finite type through
`Dualizing.PolynomialPresentation.isPerfectModule_of_flat`.

### The projection-formula compatibility is carried, not discharged

`Dualizing.isIso_derivedHomBaseChange_mvPolynomial` carries the hypothesis
`Dualizing.KFlatAlgebraActionEq`, the projection-formula compatibility of [stacks 0E2A] in the
reduced form of `Dualizing.projectionFormulaCompatibilityCanonical_of_kFlatAlgebraAction`.  It is
not discharged here, and the special features of this square do not help to discharge it: the
compatibility mentions neither the object at which invertibility is asserted nor any finiteness
hypothesis, so neither perfectness of `A` over `P` nor freeness of `P_K` over `P` enters its
statement.  It is the same hypothesis that the library's [stacks 0BZM] and [stacks 0BZP] carry
beyond those of their sources.

What *is* unconditional in this situation is the other half of the criterion of [stacks 0E2A],
namely invertibility of the tensor--Hom diagonal of [stacks 0BYN]; that is
`Dualizing.isIso_derivedTensorHomDiagonal_mvPolynomial`, and it follows from perfectness of `A`
alone by [stacks 0ATK].  So the two halves of the criterion are in opposite states: the diagonal
closes from the finiteness hypothesis, and the compatibility remains open.

## References

* [Stacks Project, Tag 0E29](https://stacks.math.columbia.edu/tag/0E29)
* [Stacks Project, Tag 0E2A](https://stacks.math.columbia.edu/tag/0E2A)
* [Stacks Project, Tag 0BZP](https://stacks.math.columbia.edu/tag/0BZP)
* [Stacks Project, Tag 0ATK](https://stacks.math.columbia.edu/tag/0ATK)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

attribute [local instance] HasDerivedCategory.standard

universe u

namespace RingTheory.TorIndependence

/-- An `R`-algebra `B` which is flat is Tor independent over `R` from every `R`-algebra `A`: by
the symmetry of Tor the vanishing of `Torᵢ^R(A, B)` in positive degrees is that of
`Torᵢ^R(B, A)`, and tensoring with a flat module preserves exactness of a projective
resolution.  This is the right-hand companion of
`RingTheory.TorIndependence.torIndependent_of_flat_left`. -/
@[sga "6 VIII 1.4" "partial", sga "6 X 7.10" "special case"]
theorem torIndependent_of_flat_right {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] [Module.Flat R B] :
    TorIndependent R A B := by
  rw [torIndependent_iff_isZero_tor]
  intro i hi
  obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
  obtain ⟨e⟩ := tor_symm_canonically_iso R (j + 1)
  refine IsZero.of_iso (isZero_Tor_succ_of_flat (ModuleCat.of R B) (ModuleCat.of R A) j) ?_
  simpa [Functor.flip] using (e.app (ModuleCat.of R A)).app (ModuleCat.of R B)

end RingTheory.TorIndependence

namespace Dualizing

attribute [local instance] MvPolynomial.algebraMvPolynomial
attribute [local instance] Algebra.TensorProduct.rightAlgebra
attribute [local implicit_reducible]
  CochainComplex.DerivedExtensionScalars.extensionOfScalarsComplexGeneral
  CochainComplex.DerivedExtensionScalars.extensionOfScalarsComplex

/-- Adjoining variables preserves flatness of a base change: the polynomial algebra over `R'` is
the base change along `R → R'` of the polynomial algebra over `R`, so it is flat over the
latter whenever `R'` is flat over `R`. -/
theorem flat_mvPolynomial_of_flat {R R' : Type u} [CommRing R] [CommRing R'] [Algebra R R']
    (σ : Type*) [Module.Flat R R'] :
    Module.Flat (MvPolynomial σ R) (MvPolynomial σ R') :=
  Module.Flat.of_linearEquiv
    (Algebra.IsPushout.out (R := R) (S := MvPolynomial σ R) (R' := R')
      (S' := MvPolynomial σ R')).equiv.symm

section

variable {k K : Type u} [Field k] [Field K] [Algebra k K] {n : ℕ}
  {A : Type u} [CommRing A] [Algebra (MvPolynomial (Fin n) k) A]

/-- `K[x_1, …, x_n]` is flat over `k[x_1, …, x_n]` for every extension of fields `k ⊆ K`. -/
instance flat_mvPolynomial_fieldExtension :
    Module.Flat (MvPolynomial (Fin n) k) (MvPolynomial (Fin n) K) :=
  flat_mvPolynomial_of_flat _

/-- A `k[x_1, …, x_n]`-algebra `A` is Tor independent from `K[x_1, …, x_n]` over
`k[x_1, …, x_n]`, the latter being flat over the former. -/
theorem torIndependent_mvPolynomial_fieldExtension :
    RingTheory.TorIndependence.TorIndependent
      (MvPolynomial (Fin n) k) A (MvPolynomial (Fin n) K) :=
  RingTheory.TorIndependence.torIndependent_of_flat_right

/-- The pushout corner `A ⊗_P P_K` of the square `P → A`, `P → P_K` is the base change
`A ⊗_k K` of `A` along the field extension, for `P = k[x_1, …, x_n]` and
`P_K = K[x_1, …, x_n]`. -/
def mvPolynomialBaseChangeTensorRingEquiv [Algebra k A]
    [IsScalarTower k (MvPolynomial (Fin n) k) A] :
    TensorProduct (MvPolynomial (Fin n) k) A (MvPolynomial (Fin n) K) ≃+* A ⊗[k] K :=
  ((Algebra.TensorProduct.commRight (MvPolynomial (Fin n) k) (MvPolynomial (Fin n) K)
        A).toRingEquiv.symm.trans
      (Algebra.IsPushout.cancelBaseChangeAlg k K (MvPolynomial (Fin n) k)
        (MvPolynomial (Fin n) K) A).toRingEquiv).trans
    (Algebra.TensorProduct.comm k K A).toRingEquiv

/-- **The unconditional half of the criterion of [stacks 0E2A] in this situation.**  For `A`
perfect as a `P`-module the tensor--Hom diagonal of [stacks 0BYN],
`P_K ⊗_P^L RHom_P(A, P) ⟶ RHom_P(A, P_K)`, is invertible; this is [stacks 0ATK] at a perfect
internal-Hom source. -/
theorem isIso_derivedTensorHomDiagonal_mvPolynomial
    (hA : StacksDraft.Perfect.IsPerfectModule (R := MvPolynomial (Fin n) k) A) :
    IsIso (derivedTensorHomDiagonalModel.{u, u, u + 1}
      (derivedAlgebraSingle.{u, u, u}
        (algebraMap (MvPolynomial (Fin n) k) (MvPolynomial (Fin n) K)))
      ((DerivedCategory.singleFunctor (ModuleCat.{u} (MvPolynomial (Fin n) k)) 0).obj
        (ModuleCat.of (MvPolynomial (Fin n) k) (MvPolynomial (Fin n) k)))
      (derivedAlgebraSingle.{u, u, u} (algebraMap (MvPolynomial (Fin n) k) A))) :=
  isIso_derivedTensorHomDiagonalModel _ _ _ (Or.inl (isPerfect_singleULiftAlgebra.{u, u, u} hA))

variable
  (bcP : DerivedCategory (ModuleCat.{u} (MvPolynomial (Fin n) k)) ⥤
    DerivedCategory (ModuleCat.{u} (MvPolynomial (Fin n) K)))
  (cmpP : DerivedCategory.Q ⋙ bcP ⟶
    (ModuleCat.extendScalars.{u, u, u}
        (algebraMap (MvPolynomial (Fin n) k)
          (MvPolynomial (Fin n) K))).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
      DerivedCategory.Q)
  (ldP : bcP.IsLeftDerivedFunctor cmpP
    (HomologicalComplex.quasiIso (ModuleCat.{u} (MvPolynomial (Fin n) k)) (ComplexShape.up ℤ)))
  (bcA : DerivedCategory (ModuleCat.{u} A) ⥤
    DerivedCategory (ModuleCat.{u}
      (TensorProduct (MvPolynomial (Fin n) k) A (MvPolynomial (Fin n) K))))
  (cmpA : DerivedCategory.Q ⋙ bcA ⟶
    (ModuleCat.extendScalars.{u, u, u}
        (algebraMap A (TensorProduct (MvPolynomial (Fin n) k) A
          (MvPolynomial (Fin n) K)))).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
      DerivedCategory.Q)
  (ldA : bcA.IsLeftDerivedFunctor cmpA
    (HomologicalComplex.quasiIso (ModuleCat.{u} A) (ComplexShape.up ℤ)))

/-- **Base change of trivial duality for a polynomial algebra over a field extension.**  Let
`k ⊆ K` be an extension of fields, `P = k[x_1, …, x_n]`, `P_K = K[x_1, …, x_n]`, and let `A` be a
`P`-algebra which is perfect as a `P`-module.  Then the base-change morphism of [stacks 0E29],
`RHom_P(A, -) ⊗_A^L (A ⊗_P P_K) ⟶ RHom_{P_K}(A ⊗_P P_K, - ⊗_P^L P_K)`,
is invertible as a natural transformation, hence at every object of `D(P)`.

Tor independence of `A` and `P_K` over `P` is automatic, `P_K` being flat over `P`.  The
hypothesis `hAct` is the projection-formula compatibility of [stacks 0E2A], which this square
does not discharge; see the module documentation. -/
theorem isIso_derivedHomBaseChange_mvPolynomial (hAct : KFlatAlgebraActionEq.{u})
    (hA : StacksDraft.Perfect.IsPerfectModule (R := MvPolynomial (Fin n) k) A) :
    IsIso (derivedHomBaseChange.{u, u, u, 0}
      (torIndependent_mvPolynomial_fieldExtension (K := K) (A := A))
      bcP cmpP ldP bcA cmpA ldA) :=
  isIso_derivedHomBaseChange_of_isPerfect_of_kFlatAlgebraActionEq _ bcP cmpP ldP bcA cmpA ldA
    (hAct _ bcP cmpP ldP bcA cmpA ldA) hA

/-- **The comparison `RHom_P(A, P) ⊗_A^L (A ⊗_P P_K) ⟶ RHom_{P_K}(A ⊗_P P_K, P ⊗_P^L P_K)`** is
invertible: the base-change morphism of [stacks 0E29] read at the unit `P` of `D(P)`.  The
hypotheses are those of `Dualizing.isIso_derivedHomBaseChange_mvPolynomial`. -/
theorem isIso_derivedHomBaseChange_mvPolynomial_app_unit (hAct : KFlatAlgebraActionEq.{u})
    (hA : StacksDraft.Perfect.IsPerfectModule (R := MvPolynomial (Fin n) k) A) :
    IsIso ((derivedHomBaseChange.{u, u, u, 0}
      (torIndependent_mvPolynomial_fieldExtension (K := K) (A := A))
      bcP cmpP ldP bcA cmpA ldA).app
        ((DerivedCategory.singleFunctor (ModuleCat.{u} (MvPolynomial (Fin n) k)) 0).obj
          (ModuleCat.of (MvPolynomial (Fin n) k) (MvPolynomial (Fin n) k)))) :=
  have := isIso_derivedHomBaseChange_mvPolynomial bcP cmpP ldP bcA cmpA ldA hAct hA
  inferInstance

end

end Dualizing

end
