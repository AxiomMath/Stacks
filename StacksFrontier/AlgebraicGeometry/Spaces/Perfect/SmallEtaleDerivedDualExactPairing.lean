module

public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.DerivedSheafHomQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.DerivedTensorHomDiagonal
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.PerfectRetract
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentDerivedMonoidal
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleLeftTensorHomDiagonal
public import StacksFrontier.CategoryTheory.Monoidal.ExactPairingOfTensorHomDiagonal
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedTensorHomDiagonalLeftTensor

/-!
# A perfect object on an algebraic space is dualizable

Let `X` be an algebraic space and `E` a perfect object of `D(𝒪_X)`, with dual
`E^∨ = R𝓗om(E, 𝒪_X)`. The tensor–Hom diagonal `P ⊗^L R𝓗om(E, K) ⟶ R𝓗om(E, P ⊗^L K)` is an
isomorphism (Stacks 0E4Q), so `E^∨` is a left dual of `E` in the monoidal category `D(𝒪_X)`,
with evaluation the counit `E^∨ ⊗^L E ⟶ 𝒪_X` of `- ⊗^L E ⊣ R𝓗om(E, -)` (Stacks 0FPV). Both
objects lie in `D_QCoh(𝒪_X)`, so the pairing is one in `D_QCoh(𝒪_X)`.

## Main results

* `AlgebraicGeometry.Space.isIso_smallEtaleLeftTensorHomDiagonal_of_isPerfect`: the tensor–Hom
  diagonal `P ⊗^L R𝓗om(M, K) ⟶ R𝓗om(M, P ⊗^L K)` is an isomorphism for perfect `M`.
* `AlgebraicGeometry.Space.smallEtaleDerivedDualExactPairing`: the exact pairing in `D(𝒪_X)`.
* `AlgebraicGeometry.Space.quasicoherentDerivedDualExactPairing`: the exact pairing in
  `D_QCoh(𝒪_X)`.

## References

* [Stacks Project, Tag 0FPV](https://stacks.math.columbia.edu/tag/0FPV)
* [Stacks Project, Tag 0E4Q](https://stacks.math.columbia.edu/tag/0E4Q)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite

universe u

namespace AlgebraicGeometry.Space

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

attribute [local instance 10000] HasDerivedCategory.standard

attribute [local instance 20000] AddCommGrpCat.FilteredColimits.forget_preservesFilteredColimits

attribute [local instance 5000] SmallEtale.instHasSheafify SmallEtale.instWEqualsLocallyBijective

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **The tensor–Hom diagonal of an algebraic space is invertible when the internal Hom source is
perfect** (Stacks 0E4Q case (1)), for the diagonal built from the associator of `⊗^L`. -/
theorem isIso_smallEtaleLeftTensorHomDiagonal_of_isPerfect (X : AlgebraicSpaces B S hS)
    (P M K : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)))
    (hM : RingedSite.IsPerfect (smallEtaleRingedSite B S hS X.1 X.2) M) :
    IsIso (CategoryTheory.PullbackInternalHom.leftTensorHomDiagonal
      (smallEtaleDerivedTensor B S hS X) (smallEtaleDerivedSheafHom B S hS X)
      (smallEtaleDerivedTensorSheafHomAdjunction B S hS X) (smallEtaleDerivedTensorAssociator X)
      P M K) := by
  refine isIso_leftTensorHomDiagonal_of_model X P M K ?_
  rw [← RingedSite.derivedTensorHomDiagonal_eq_leftTensorHomDiagonal]
  exact isIso_derivedTensorHomDiagonal_of_isPerfect B S hS X.1 X.2 _ _ _
    (isPerfect_smallEtaleModelDerivedEquivalence_functor_obj B S hS X M hM)

/-- **A perfect object of `D(𝒪_X)` has its derived dual as a left dual** (Stacks 0FPV), in the
monoidal structure of `D(𝒪_X)` with tensor product `⊗^L`: the evaluation is the counit
`R𝓗om(E, 𝒪_X) ⊗^L E ⟶ 𝒪_X` and the coevaluation is the section adjoint to `λ_E` read through
the inverse of the tensor–Hom diagonal. -/
@[instance_reducible]
def smallEtaleDerivedDualExactPairing (X : AlgebraicSpaces B S hS)
    (E : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)))
    (hE : RingedSite.IsPerfect (smallEtaleRingedSite B S hS X.1 X.2) E) :
    @ExactPairing (DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)))
      _ (smallEtaleDerivedMonoidal X) E
      (((smallEtaleDerivedSheafHom B S hS X).obj (op E)).obj
        (@MonoidalCategoryStruct.tensorUnit _ _
          (smallEtaleDerivedMonoidal X).toMonoidalCategoryStruct)) :=
  @CategoryTheory.PullbackInternalHom.exactPairingOfIsIsoLeftTensorHomDiagonal _ _
    (smallEtaleDerivedMonoidal X) (smallEtaleDerivedSheafHom B S hS X)
    (smallEtaleDerivedTensorSheafHomAdjunction B S hS X) E
    (isIso_smallEtaleLeftTensorHomDiagonal_of_isPerfect X E E _ hE)

/-- The dual of a perfect object, as an object of `D_QCoh(𝒪_X)`. -/
def quasicoherentDerivedDual (X : AlgebraicSpaces B S hS)
    (E : QuasicoherentDerivedCategory.{u, u} B S hS X.1 X.2)
    (hE : RingedSite.IsPerfect (smallEtaleRingedSite B S hS X.1 X.2) E.obj) :
    QuasicoherentDerivedCategory.{u, u} B S hS X.1 X.2 :=
  ⟨((smallEtaleDerivedSheafHom B S hS X).obj (op E.obj)).obj
      (derivedStructureSheaf B S hS X.1 X.2).obj,
    qcohDerived_smallEtaleDerivedSheafHom_of_isPerfect X _ _ hE
      (derivedStructureSheaf B S hS X.1 X.2).property⟩

/-- **A perfect object of `D_QCoh(𝒪_X)` has its derived dual as a left dual** (Stacks 0FPV), in
the monoidal structure `quasicoherentDerivedMonoidal` of `D_QCoh(𝒪_X)`. -/
@[instance_reducible]
def quasicoherentDerivedDualExactPairing (X : AlgebraicSpaces B S hS)
    (E : QuasicoherentDerivedCategory.{u, u} B S hS X.1 X.2)
    (hE : RingedSite.IsPerfect (smallEtaleRingedSite B S hS X.1 X.2) E.obj) :
    @ExactPairing _ _ (quasicoherentDerivedMonoidal X) E (quasicoherentDerivedDual X E hE) :=
  quasicoherentDerivedExactPairing X E (quasicoherentDerivedDual X E hE)
    (smallEtaleDerivedDualExactPairing X E.obj hE)

end AlgebraicGeometry.Space

end
