module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Variety.Tangent.Cotangent
public import StacksFrontier.Deformation.Basic
public import StacksFrontier.RingTheory.Kaehler.LocalCotangentSpace

/-!
# The cotangent and tangent spaces at a point with separable residue field extension

Let `f : X ⟶ S` be a morphism of schemes, let `x` be a point of `X` and let `s = f x`.  When the
residue field extension `κ(s) → κ(x)` is separable — in particular when `κ(x) = κ(s)` — the
relative cotangent space of the local homomorphism `𝒪_{S,s} → 𝒪_{X,x}`,

`𝔪_x / (𝔪_x² + 𝔪_s 𝒪_{X,x})`,

is canonically the residue-field fibre `κ(x) ⊗_{𝒪_{X,x}} Ω_{X/S,x}` of the stalk of the sheaf of
relative differentials, and the relative tangent space at `x` is canonically its `κ(x)`-linear
dual.

## Main definitions

* `AlgebraicGeometry.relativeCotangentSpaceEquivDifferentialFiber`: the first canonical
  isomorphism.
* `AlgebraicGeometry.dottedTangentArrowEquivDualRelativeCotangentSpace`: the second one.

## Main results

* `AlgebraicGeometry.relativeCotangentSpaceEquivDifferentialFiber_apply_germ`: the first
  isomorphism sends the class of the germ of a local section vanishing at `x` to the germ of its
  universal relative differential, which is what makes it canonical.
* `AlgebraicGeometry.dottedTangentArrowEquivDualRelativeCotangentSpace_apply_germ`: the second
  one evaluates a dual-number arrow on such a class by the coefficient of `ε` in the pullback of
  the section along the arrow.
* `AlgebraicGeometry.algebraMap_residueFieldMapAlgebra`: the algebra structure the separability
  hypothesis is stated over is the one of `AlgebraicGeometry.Scheme.Hom.residueFieldMap`.

## References

* [Stacks Project, Tag 0B2E](https://stacks.math.columbia.edu/tag/0B2E)
* [Stacks Project, Tag 0B2D](https://stacks.math.columbia.edu/tag/0B2D)
* [Stacks Project, Tag 06GY](https://stacks.math.columbia.edu/tag/06GY)
-/

@[expose] public section

open CategoryTheory TopologicalSpace Opposite IsLocalRing
open AlgebraicGeometry.SheafOfModules
open Stacks.RelativeDifferentialStalkMap
open Stacks.SmoothAtJacobian (relativeDifferentialStalk relativeDifferentialStalkModule)
open scoped TensorProduct

universe u

namespace Deformation

/-- The relative cotangent space of a local homomorphism is a scalar tower over the residue
field of its target: the residue field acts through the local ring. -/
noncomputable abbrev relativeCotangentSpace.isScalarTower {R A : Type*} [CommRing R] [CommRing A]
    [IsLocalRing R] [IsLocalRing A] (g : R →+* A) [IsLocalHom g] :
    IsScalarTower A (ResidueField A) (relativeCotangentSpace g) :=
  IsScalarTower.of_algebraMap_smul fun _ _ => rfl

end Deformation

namespace AlgebraicGeometry

variable {X S : Scheme.{u}} (f : X ⟶ S) (x : X)

/-! ### The scalar structures at a point -/

/-- `κ(x)` as an algebra over the local ring `𝒪_{X,x}`, through the residue map. -/
noncomputable abbrev stalkResidueAlgebra : Algebra (X.presheaf.stalk x) (X.residueField x) :=
  inferInstanceAs (Algebra (ToType (X.presheaf.stalk x))
    (ResidueField (ToType (X.presheaf.stalk x))))

attribute [local instance] stalkResidueAlgebra stalkMapAlgebra openNhdsDecidableEq
attribute [local instance] relativeDifferentialStalkModule
attribute [local instance] Deformation.relativeCotangentSpace.isScalarTower

/-- The stalk map of `f` at `x` is a local homomorphism, named as a statement about the
structural map of the algebra `𝒪_{S,f x} → 𝒪_{X,x}`. -/
noncomputable abbrev stalkMapIsLocalHom :
    IsLocalHom (algebraMap (ToType (S.presheaf.stalk (f.base x)))
      (ToType (X.presheaf.stalk x))) :=
  show IsLocalHom (f.stalkMap x).hom from inferInstance

attribute [local instance] stalkMapIsLocalHom

/-- `κ(x)` as an algebra over `κ(f x)`, the residue field extension of the stalk map of `f`. -/
noncomputable abbrev residueFieldMapAlgebra :
    Algebra (S.residueField (f.base x)) (X.residueField x) :=
  inferInstanceAs (Algebra (ResidueField (ToType (S.presheaf.stalk (f.base x))))
    (ResidueField (ToType (X.presheaf.stalk x))))

/-- The relative cotangent space `𝔪_x / (𝔪_x² + 𝔪_s 𝒪_{X,x})` as a `κ(x)`-vector space. -/
noncomputable abbrev relativeCotangentSpaceResidueModule :
    Module (X.residueField x) (Deformation.relativeCotangentSpace (f.stalkMap x).hom) :=
  inferInstanceAs (Module (ResidueField (ToType (X.presheaf.stalk x)))
    (Deformation.relativeCotangentSpace (f.stalkMap x).hom))

/-- Scalars from the local ring at `x` act on `κ(x)` through the residue field. -/
noncomputable abbrev residueAlgebraTower :
    IsScalarTower (X.presheaf.stalk x) (X.residueField x) (X.residueField x) :=
  inferInstanceAs (IsScalarTower (ToType (X.presheaf.stalk x))
    (ResidueField (ToType (X.presheaf.stalk x))) (ResidueField (ToType (X.presheaf.stalk x))))

attribute [local instance] residueFieldMapAlgebra relativeCotangentSpaceResidueModule
attribute [local instance] residueAlgebraTower

/-- The structural map of `AlgebraicGeometry.residueFieldMapAlgebra` is the homomorphism of
residue fields induced by `f`, so the separability hypothesis below is the separability of the
residue field extension `κ(f x) → κ(x)` of `f` at `x`. -/
theorem algebraMap_residueFieldMapAlgebra :
    algebraMap (S.residueField (f.base x)) (X.residueField x) = (f.residueFieldMap x).hom := by
  refine RingHom.ext fun z => ?_
  obtain ⟨y, rfl⟩ := IsLocalRing.residue_surjective z
  exact (congrArg (fun h => CommRingCat.Hom.hom h y)
    (Scheme.residue_residueFieldMap f x)).symm

/-! ### The cotangent space as a quotient of the maximal ideal -/

/-- Let `f : X ⟶ S` be a morphism of schemes and let `x` be a point of `X` whose residue field
extension `κ(f x) → κ(x)` is separable.  The relative cotangent space
`𝔪_x / (𝔪_x² + 𝔪_{f x} 𝒪_{X,x})` of the stalk map of `f` is canonically the residue-field fibre
`κ(x) ⊗_{𝒪_{X,x}} Ω_{X/S,x}` of the stalk of the sheaf of relative differentials. -/
@[stacks 0B2E "cotangent space", ega "IV 16.5.13" "partial"]
noncomputable def relativeCotangentSpaceEquivDifferentialFiber
    (hsep : Algebra.IsSeparable (S.residueField (f.base x)) (X.residueField x)) :
    Deformation.relativeCotangentSpace (f.stalkMap x).hom ≃ₗ[X.residueField x]
      X.residueField x ⊗[X.presheaf.stalk x] relativeDifferentialStalk f x :=
  letI : Algebra.IsSeparable (ResidueField (ToType (S.presheaf.stalk (f.base x))))
      (ResidueField (ToType (X.presheaf.stalk x))) := hsep
  let E : relativeDifferentialStalk f x ≃ₗ[ToType (X.presheaf.stalk x)]
      KaehlerDifferential (ToType (S.presheaf.stalk (f.base x)))
        (ToType (X.presheaf.stalk x)) :=
    relativeDifferentialsStalkKaehlerEquiv f x
  let e : Deformation.relativeCotangentSpace (f.stalkMap x).hom
      ≃ₗ[ResidueField (ToType (X.presheaf.stalk x))]
      (ResidueField (ToType (X.presheaf.stalk x)) ⊗[ToType (X.presheaf.stalk x)]
        relativeDifferentialStalk f x) :=
    ((LinearEquiv.ofBijective _
        (KaehlerDifferential.bijective_relativeCotangentSpaceToTensorKaehler
          (ToType (S.presheaf.stalk (f.base x)))
          (ToType (X.presheaf.stalk x)))).extendScalarsOfSurjective
            IsLocalRing.residue_surjective).trans
      (LinearEquiv.baseChange _ _ _ _ E.symm)
  e

/-- The identification of the relative cotangent space with the residue-field fibre of the
relative differentials carries the class of the germ at `x` of a local section of `𝒪_X` vanishing
at `x` to the germ of the universal relative differential of that section.  This is what makes it
canonical. -/
@[stacks 0B2E "canonical map on differentials"]
theorem relativeCotangentSpaceEquivDifferentialFiber_apply_germ
    (hsep : Algebra.IsSeparable (S.residueField (f.base x)) (X.residueField x))
    (U : X.Opens) (hx : x ∈ U) (a : X.presheaf.obj (op U))
    (ha : (X.presheaf.germ U x hx).hom a ∈
      maximalIdeal (ToType (X.presheaf.stalk x))) :
    relativeCotangentSpaceEquivDifferentialFiber f x hsep
        (Submodule.Quotient.mk ⟨(X.presheaf.germ U x hx).hom a, ha⟩) =
      (1 : X.residueField x) ⊗ₜ[X.presheaf.stalk x]
        (show relativeDifferentialStalk f x from
          TopCat.Presheaf.germ (C := AddCommGrpCat.{u})
            (Scheme.Hom.relativeDifferentials f).val.presheaf U x hx
            ((Scheme.Hom.universalRelativeDerivation f).d a)) := by
  have hE : relativeDifferentialsStalkKaehlerEquiv f x
      (TopCat.Presheaf.germ (C := AddCommGrpCat.{u})
        (Scheme.Hom.relativeDifferentials f).val.presheaf U x hx
        ((Scheme.Hom.universalRelativeDerivation f).d a)) =
      KaehlerDifferential.D (ToType (S.presheaf.stalk (f.base x)))
        (ToType (X.presheaf.stalk x)) ((X.presheaf.germ U x hx).hom a) :=
    relativeDifferentialsStalkKaehlerEquiv_germ_d f x
      (OrderDual.toDual (⟨U, hx⟩ : TopologicalSpace.OpenNhds x)) a
  have hcomp : relativeCotangentSpaceEquivDifferentialFiber f x hsep
      (Submodule.Quotient.mk ⟨(X.presheaf.germ U x hx).hom a, ha⟩) =
      (1 : X.residueField x) ⊗ₜ[X.presheaf.stalk x]
        (show relativeDifferentialStalk f x from
          (relativeDifferentialsStalkKaehlerEquiv f x).symm
            (KaehlerDifferential.D (ToType (S.presheaf.stalk (f.base x)))
              (ToType (X.presheaf.stalk x)) ((X.presheaf.germ U x hx).hom a))) := rfl
  rw [hcomp, ← hE, LinearEquiv.symm_apply_apply]

/-! ### The tangent space as the dual of the cotangent space -/

/-- If the residue field extension `κ(f x) → κ(x)` is separable, the relative tangent space at
`x` — the space of dual-number arrows into `X` over `S` extending the residue-field point `x` — is
canonically the `κ(x)`-linear dual of the relative cotangent space
`𝔪_x / (𝔪_x² + 𝔪_{f x} 𝒪_{X,x})`. -/
@[stacks 0B2E "tangent space"]
noncomputable def dottedTangentArrowEquivDualRelativeCotangentSpace
    (hsep : Algebra.IsSeparable (S.residueField (f.base x)) (X.residueField x)) :
    DottedTangentArrow f x ≃ₗ[X.residueField x]
      (Deformation.relativeCotangentSpace (f.stalkMap x).hom →ₗ[X.residueField x]
        X.residueField x) :=
  (show DottedTangentArrow f x ≃ₗ[X.residueField x]
      (relativeDifferentialStalk f x →ₗ[X.presheaf.stalk x] X.residueField x) from
    tangentSpaceEquivCotangentSpace f x).trans
    ((LinearMap.liftBaseChangeEquiv (R := X.presheaf.stalk x) (X.residueField x)).trans
      (relativeCotangentSpaceEquivDifferentialFiber f x hsep).dualMap)

/-- The identification of the relative tangent space with the dual of the relative cotangent space
evaluates a dual-number arrow on the class of the germ of a local section vanishing at `x` by the
coefficient of `ε` in the pullback of that section along the arrow. -/
@[stacks 0B2E "canonical map on tangent vectors"]
theorem dottedTangentArrowEquivDualRelativeCotangentSpace_apply_germ
    (hsep : Algebra.IsSeparable (S.residueField (f.base x)) (X.residueField x))
    (θ : DottedTangentArrow f x) (U : X.Opens) (hx : x ∈ U) (hU : ⊤ ≤ θ.val ⁻¹ᵁ U)
    (a : X.presheaf.obj (op U))
    (ha : (X.presheaf.germ U x hx).hom a ∈
      maximalIdeal (ToType (X.presheaf.stalk x))) :
    dottedTangentArrowEquivDualRelativeCotangentSpace f x hsep θ
        (Submodule.Quotient.mk ⟨(X.presheaf.germ U x hx).hom a, ha⟩) =
      pullbackInfinitesimalCoefficient θ U hU a := by
  have hdual : dottedTangentArrowEquivDualRelativeCotangentSpace f x hsep θ
      (Submodule.Quotient.mk ⟨(X.presheaf.germ U x hx).hom a, ha⟩) =
      LinearMap.liftBaseChangeEquiv (R := X.presheaf.stalk x) (X.residueField x)
        (show relativeDifferentialStalk f x →ₗ[X.presheaf.stalk x] X.residueField x from
          tangentSpaceEquivCotangentSpace f x θ)
        (relativeCotangentSpaceEquivDifferentialFiber f x hsep
          (Submodule.Quotient.mk ⟨(X.presheaf.germ U x hx).hom a, ha⟩)) := rfl
  rw [hdual, relativeCotangentSpaceEquivDifferentialFiber_apply_germ f x hsep U hx a ha]
  change (1 : X.residueField x) • tangentSpaceEquivCotangentSpace f x θ
    (TopCat.Presheaf.germ (C := AddCommGrpCat.{u})
      (Scheme.Hom.relativeDifferentials f).val.presheaf U x hx
      ((Scheme.Hom.universalRelativeDerivation f).d a)) = _
  rw [one_smul]
  exact tangentSpaceEquivCotangentSpace_apply_germ f x θ U hx hU a

end AlgebraicGeometry

end
