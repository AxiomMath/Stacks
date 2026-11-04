module

public import StacksFrontier.AlgebraicGeometry.Quot.NumericalSubstackLocus
public import StacksFrontier.AlgebraicGeometry.Quot.NumericalTensorPowerProducts
public import StacksFrontier.CategoryTheory.Monoidal.BifunctorIntegerPowersCongr

/-!
# The numerical invariants of Stacks 0DNE depend only on the isomorphism classes of the `E_j`

Let `f : X ⟶ B` be a separated morphism of algebraic spaces of finite presentation and let
`E_1, …, E_r` and `E_1', …, E_r'` be perfect objects of `D(𝒪_X)` with `E_j ≅ E_j'` for every `j`.
Then for every `n ∈ ℤ^{⊕ r}` the objects `E_1^{⊗ n_1} ⊗ ⋯ ⊗ E_r^{⊗ n_r}` and
`E_1'^{⊗ n_1} ⊗ ⋯ ⊗ E_r'^{⊗ n_r}` are isomorphic, hence so are the objects
`K_n = Rf_{T,*}((E_1^{⊗ n_1} ⊗ ⋯ ⊗ E_r^{⊗ n_r})_T ⊗^𝐋 𝓕)` attached to an object `(T, 𝓕)` of
`Coh_{X/B}`, and the numerical invariants `χ_n` of the two families agree.  So the substack
`Coh^P_{X/B} ⊆ Coh_{X/B}` of Stacks 0DNE is the same for the two families, and one is open and
closed exactly when the other is.

This is how the proof of Stacks 0DNE uses Stacks 09RJ: the perfect objects `E_j` are only
isomorphic to the derived pullbacks of the perfect objects `E_{j,i}` on the Noetherian model.

## Main definitions

* `AlgebraicGeometry.Space.derivedDualCongrIso`: `E ≅ E'` gives `E^∨ ≅ E'^∨`.
* `AlgebraicGeometry.Space.derivedTensorPowerProductCongrIso`:
  `E_1^{⊗ n_1} ⊗ ⋯ ⊗ E_r^{⊗ n_r} ≅ E_1'^{⊗ n_1} ⊗ ⋯ ⊗ E_r'^{⊗ n_r}`.
* `AlgebraicGeometry.Space.NumericalSituation.numericalDirectImageCongrIso`: `K_n ≅ K_n'`.

## Main results

* `AlgebraicGeometry.Space.NumericalSituation.numericalEuler_congr`: the invariants agree.
* `AlgebraicGeometry.Space.NumericalSituation.hasNumericalInvariants_congr`: the two substacks
  `Coh^P_{X/B}` have the same objects.
* `AlgebraicGeometry.Space.NumericalSituation.isOpenAndClosedCondition_congr`: one is open and
  closed exactly when the other is.

## References

* [Stacks Project, Tag 0DNE](https://stacks.math.columbia.edu/tag/0DNE)
* [Stacks Project, Tag 0DNC](https://stacks.math.columbia.edu/tag/0DNC)
* [Stacks Project, Tag 09RJ](https://stacks.math.columbia.edu/tag/09RJ)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Space

section Congr

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {hF : IsAlgebraicSpace B S hS F}

/-- **The derived dual is invariant under isomorphism**: `E ≅ E'` gives `E^∨ ≅ E'^∨`. -/
def derivedDualCongrIso
    {E E' : @DerivedCategory (Modules.{u, u} B S hS F hF) _ _ (HasDerivedCategory.standard _)}
    (e : letI := HasDerivedCategory.standard (Modules.{u, u} B S hS F hF); E ≅ E') :
    letI := HasDerivedCategory.standard (Modules.{u, u} B S hS F hF)
    derivedDual B S hS F hF E ≅ derivedDual B S hS F hF E' :=
  letI := HasDerivedCategory.standard (Modules.{u, u} B S hS F hF)
  letI := HasDerivedCategory.standard (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
    (Stacks.Cohomology.Torsors.Generators.smallModelRingedSite
      (smallEtaleRingedSite B S hS F hF)).O))
  (RingedSite.smallModelDerivedEquivalence (smallEtaleRingedSite B S hS F hF)).inverse.mapIso
    (((RingedSite.derivedSheafHomBifunctor _).mapIso
      ((RingedSite.smallModelDerivedEquivalence
        (smallEtaleRingedSite B S hS F hF)).functor.mapIso e).op.symm).app _)

/-- **The products of integer tensor powers are invariant under isomorphisms of the factors**:
`E_j ≅ E_j'` for every `j` gives
`E_1^{⊗ n_1} ⊗ ⋯ ⊗ E_r^{⊗ n_r} ≅ E_1'^{⊗ n_1} ⊗ ⋯ ⊗ E_r'^{⊗ n_r}`. -/
def derivedTensorPowerProductCongrIso {r : ℕ}
    {E E' : Fin r → @DerivedCategory (Modules.{u, u} B S hS F hF) _ _
      (HasDerivedCategory.standard _)}
    (e : letI := HasDerivedCategory.standard (Modules.{u, u} B S hS F hF); ∀ j, E j ≅ E' j)
    (n : Fin r → ℤ) :
    letI := HasDerivedCategory.standard (Modules.{u, u} B S hS F hF)
    derivedTensorPowerProduct B S hS F hF E n ≅ derivedTensorPowerProduct B S hS F hF E' n :=
  letI := HasDerivedCategory.standard (Modules.{u, u} B S hS F hF)
  Functor.multiTensorPowCongrIso _ _ e (fun j => derivedDualCongrIso (e j)) n

end Congr

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [local instance 5000] CategoryTheory.IsGrothendieckAbelian.enoughInjectives
attribute [local instance] isGrothendieckAbelian_modules

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {D : CoherentSituation B S hS}

namespace NumericalSituation

variable (hf : IsSeparated B S hS D.f.hom) {r : ℕ}
    {E E' : Fin r → @DerivedCategory (Modules.{u, u} B S hS D.X.1 D.X.2) _ _
      (HasDerivedCategory.standard _)}
    (hE : ∀ j, letI := HasDerivedCategory.standard (Modules.{u, u} B S hS D.X.1 D.X.2)
      (smallEtaleRingedSite B S hS D.X.1 D.X.2).IsPerfect (E j))
    (hE' : ∀ j, letI := HasDerivedCategory.standard (Modules.{u, u} B S hS D.X.1 D.X.2)
      (smallEtaleRingedSite B S hS D.X.1 D.X.2).IsPerfect (E' j))
    (e : letI := HasDerivedCategory.standard (Modules.{u, u} B S hS D.X.1 D.X.2)
      ∀ j, E j ≅ E' j) (P : (Fin r → ℤ) → ℤ)

/-- **`K_n ≅ K_n'`**: for an object `(T, 𝓕)` of `Coh_{X/B}`, isomorphisms `E_j ≅ E_j'` give an
isomorphism of the objects `Rf_{T,*}((E_1^{⊗ n_1} ⊗ ⋯ ⊗ E_r^{⊗ n_r})_T ⊗^𝐋 𝓕)` and
`Rf_{T,*}((E_1'^{⊗ n_1} ⊗ ⋯ ⊗ E_r'^{⊗ n_r})_T ⊗^𝐋 𝓕)` of `D(𝒪_T)`. -/
def numericalDirectImageCongrIso (A : CoherentObject D) (n : Fin r → ℤ) :
    letI := HasDerivedCategory.standard (Modules.{u, u} B S hS D.X.1 D.X.2)
    letI := HasDerivedCategory.standard (Modules.{u, u} B S hS (D.space A.T).1 (D.space A.T).2)
    letI := HasDerivedCategory.standard (Modules.{u, u} B S hS (testSpace A).1 (testSpace A).2)
    (ofDerivedTensorPowerProducts hf E hE P).numericalDirectImage A n ≅
      (ofDerivedTensorPowerProducts hf E' hE' P).numericalDirectImage A n :=
  letI := HasDerivedCategory.standard (Modules.{u, u} B S hS D.X.1 D.X.2)
  letI := HasDerivedCategory.standard (Modules.{u, u} B S hS (D.space A.T).1 (D.space A.T).2)
  letI := HasDerivedCategory.standard (Modules.{u, u} B S hS (testSpace A).1 (testSpace A).2)
  (Stacks.DerivedFunctor.totalRightDerived (modulePushforward B S hS (D.projection A.T))).mapIso
    (((Stacks.SheafOfModules.derivedTensorProductFunctor
      (smallEtaleRingedSite B S hS (D.space A.T).1 (D.space A.T).2)).mapIso
        ((smallEtaleDerivedModulePullback B S hS (baseChangeProjection D.f A.T)).mapIso
          (derivedTensorPowerProductCongrIso e n))).app _)

include e in
/-- **The numerical invariants depend only on the isomorphism classes of the `E_j`.** -/
theorem numericalEuler_congr (A : CoherentObject D) (n : Fin r → ℤ) :
    (ofDerivedTensorPowerProducts hf E hE P).numericalEuler A n =
      (ofDerivedTensorPowerProducts hf E' hE' P).numericalEuler A n :=
  derivedFibreEuler_congr _ (numericalDirectImageCongrIso hf hE hE' e P A n)

include e in
/-- **`Coh^P_{X/B}` depends only on the isomorphism classes of the `E_j`**: an object of
`Coh_{X/B}` has the numerical invariants `P` for the family `E` exactly when it has them for the
family `E'`. -/
theorem hasNumericalInvariants_congr (A : CoherentObject D) :
    (ofDerivedTensorPowerProducts hf E hE P).HasNumericalInvariants A ↔
      (ofDerivedTensorPowerProducts hf E' hE' P).HasNumericalInvariants A := by
  refine forall_congr' fun n => forall_congr' fun t => ?_
  rw [numericalEuler_congr hf hE hE' e P A n]
  rfl

include e in
/-- **One of the two substacks `Coh^P_{X/B}` is open and closed exactly when the other is.** -/
theorem isOpenAndClosedCondition_congr :
    CoherentSituation.IsOpenAndClosedCondition D
        (ofDerivedTensorPowerProducts hf E hE P).HasNumericalInvariants ↔
      CoherentSituation.IsOpenAndClosedCondition D
        (ofDerivedTensorPowerProducts hf E' hE' P).HasNumericalInvariants :=
  iff_of_eq <| congrArg (CoherentSituation.IsOpenAndClosedCondition D) <|
    funext fun A => propext (hasNumericalInvariants_congr hf hE hE' e P A)

end NumericalSituation

end AlgebraicGeometry.Space

end
