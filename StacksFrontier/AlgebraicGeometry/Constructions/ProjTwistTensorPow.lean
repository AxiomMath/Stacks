module

public import StacksFrontier.AlgebraicGeometry.PicardGroup.Basic
public import StacksFrontier.AlgebraicGeometry.ProjRepresentsF1.TwistPowers
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.AmpleTwistingSheaf
public import StacksFrontier.AlgebraicGeometry.RelativeVeryAmple.TensorPower

/-!
# The tensor powers of the hyperplane sheaf are the twists: `𝒪(1)^{⊗ d} ≅ 𝒪(d)`

On projective `n`-space over a scheme `S` the hyperplane sheaf `𝒪(1)` is the pullback of the
degree-one twisting sheaf of the integral model `ℙⁿ_ℤ = Proj ℤ[T₀, …, Tₙ]` along the projection,
and the degree-`d` twist `𝒪(d)` is the pullback of the degree-`d` twisting sheaf. This file
proves that the two agree with the tensor powers of Stacks Tag 01CU:

`𝒪(1)^{⊗ d} ≅ 𝒪(d)` for every integer `d`.

## Main definitions

* `Stacks.AlgebraicGeometry.ProjTwistTensorPow.twistOver`: the degree-`d` twist of the structure
  sheaf of `ℙⁿ_S`, as the pullback of `𝒪(d)` on the integral model. `twistOver n S 1` is
  `Stacks.AmpleProjectiveImmersion.projectiveSpaceTwistingSheaf n S` on the nose.
* `Stacks.AlgebraicGeometry.ProjTwistTensorPow.twistOverMulIso`: the multiplication isomorphism
  `𝒪(a) ⊗ 𝒪(b) ≅ 𝒪(a + b)` on `ℙⁿ_S`, in every pair of integer degrees.
* `Stacks.AlgebraicGeometry.ProjTwistTensorPow.tensorPowModuleProjectiveTwistIso`:
  **`𝒪(1)^{⊗ d} ≅ 𝒪(d)`**, for every `d : ℤ`.

## Main results

* `Stacks.AlgebraicGeometry.ProjTwistTensorPow.isIso_twistMultiplicationMap_integralModel`:
  **Stacks Tag 01MU on `ℙⁿ_ℤ`.** The multiplication map `𝒪(a) ⊗ 𝒪(b) ⟶ 𝒪(a + b)` on the integral
  model of projective space is an isomorphism in all integer degrees, a polynomial ring being
  generated in degree one.
* `Stacks.AlgebraicGeometry.ProjTwistTensorPow.isoUnitModuleOfTensorSelfIso`: an invertible
  `𝒪_X`-module isomorphic to its own tensor square is isomorphic to `𝒪_X`.
* `Stacks.AlgebraicGeometry.ProjTwistTensorPow.isoOfTensorUnitIso`: two invertible modules with a
  common tensor inverse are isomorphic.
* `Stacks.AlgebraicGeometry.ProjTwistTensorPow.twistZeroIsoUnit`: **`𝒪(0) ≅ 𝒪`** on `ℙⁿ_S`.
* `Stacks.AlgebraicGeometry.ProjTwistTensorPow.twistOverNegIsoUnit`:
  `𝒪(d) ⊗ 𝒪(-d) ≅ 𝒪`, so `𝒪(-d)` is the tensor inverse of `𝒪(d)`.

## Implementation notes

`Stacks.AlgebraicGeometry.ProjTwistTensorPow.tensorPowModuleProjectiveTwistIso` is a match on the
constructors of `ℤ`. For `d ≥ 1` it is an induction on `d` that splits `𝒪(1)^{⊗ (k+1)}` as
`𝒪(1)^{⊗ k} ⊗ 𝒪(1)` and multiplies the two twists. For `d = 0` it is
`Stacks.AlgebraicGeometry.ProjTwistTensorPow.twistZeroIsoUnit`, obtained from
`𝒪(0) ⊗ 𝒪(0) ≅ 𝒪(0)` and the invertibility of `𝒪(0)`. For `d < 0` both `𝒪(1)^{⊗ d}` and `𝒪(d)`
are tensor inverses of `𝒪(1)^{⊗ (-d)} ≅ 𝒪(-d)`, and a tensor inverse is unique up to isomorphism
(`Stacks.SheafOfModules.tensorInverseUniqueIso`).

## References

* [Stacks Project, Tag 01MN](https://stacks.math.columbia.edu/tag/01MN)
* [Stacks Project, Tag 01MU](https://stacks.math.columbia.edu/tag/01MU)
* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
* [Stacks Project, Tag 01CT](https://stacks.math.columbia.edu/tag/01CT)
* [Stacks Project, Tag 01YS](https://stacks.math.columbia.edu/tag/01YS)
-/

@[expose] public noncomputable section

open CategoryTheory
open AlgebraicGeometry AlgebraicGeometry.ProjectiveSpectrum.Proj
open RingedSpaceModuleAdjunction
open Stacks.Ample Stacks.AmpleProjectiveImmersion Stacks.RelativeVeryAmple
open Stacks.AlgebraicGeometry.ProjInvertibleLocus

universe u

namespace Stacks.AlgebraicGeometry.ProjTwistTensorPow

/-! ### Two facts about invertible modules on an arbitrary scheme -/

/-- **An invertible `𝒪_X`-module isomorphic to its own tensor square is the structure sheaf.**
Tensoring `M ⊗ M ≅ M` with a tensor inverse `M⁻¹` of `M` turns the inverse law
`M ⊗ M⁻¹ ≅ 𝒪_X` into `𝒪_X ≅ M ⊗ M ⊗ M⁻¹ ≅ M ⊗ 𝒪_X ≅ M`, computed in the full subcategory
`Stacks.SheafOfModules.InvertibleModules` of invertible modules. -/
def isoUnitModuleOfTensorSelfIso (X : Scheme.{u}) (M : X.Modules) [IsInvertibleModule X M]
    (m : tensorModules X M M ≅ M) : M ≅ unitModule X :=
  letI hM : Stacks.SheafOfModules.IsInvertible X.presheaf
      (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X) M := stacksIsInvertible X M
  letI O := X.presheaf
  letI hO := Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X
  let A : Stacks.SheafOfModules.InvertibleModules O hO := ⟨M, hM⟩
  let Ainv := Stacks.SheafOfModules.picardInvObj O hO A
  let i : Stacks.SheafOfModules.picardTensorObj O hO A Ainv ≅
      Stacks.SheafOfModules.picardUnitObj O hO :=
    Stacks.SheafOfModules.picardTensorComm O hO A Ainv ≪≫
      Stacks.SheafOfModules.picardInvTensorIso O hO A
  let m' : Stacks.SheafOfModules.picardTensorObj O hO A A ≅ A := ObjectProperty.isoMk _ m
  let e : Stacks.SheafOfModules.picardUnitObj O hO ≅ A :=
    i.symm ≪≫
      Stacks.SheafOfModules.picardTensorIso O hO m'.symm (Iso.refl Ainv) ≪≫
      Stacks.SheafOfModules.picardTensorAssoc O hO A A Ainv ≪≫
      Stacks.SheafOfModules.picardTensorIso O hO (Iso.refl A) i ≪≫
      Stacks.SheafOfModules.picardTensorUnitIso O hO A
  ((ObjectProperty.ι _).mapIso e).symm

/-- **A tensor inverse is unique up to isomorphism**, on a scheme and in the
`Stacks.RelativeVeryAmple.tensorModules` spelling: if `A ⊗ B ≅ 𝒪_X` and `A' ⊗ B ≅ 𝒪_X` with
`A`, `A'` and `B` invertible, then `A ≅ A'`. This is
`Stacks.SheafOfModules.tensorInverseUniqueIso`, with the three modules packaged into the full
subcategory of invertible sheaves and the conclusion unpackaged again. -/
def isoOfTensorUnitIso (X : Scheme.{u}) (A A' B : X.Modules) [IsInvertibleModule X A]
    [IsInvertibleModule X A'] [IsInvertibleModule X B]
    (e : tensorModules X A B ≅ unitModule X) (e' : tensorModules X A' B ≅ unitModule X) :
    A ≅ A' :=
  letI O := X.presheaf
  letI hO := Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X
  let a : Stacks.SheafOfModules.InvertibleModules O hO := ⟨A, stacksIsInvertible X A⟩
  let a' : Stacks.SheafOfModules.InvertibleModules O hO := ⟨A', stacksIsInvertible X A'⟩
  let b : Stacks.SheafOfModules.InvertibleModules O hO := ⟨B, stacksIsInvertible X B⟩
  (ObjectProperty.ι _).mapIso
    (Stacks.SheafOfModules.tensorInverseUniqueIso O hO (X := a) (Y := a') (L := b)
      (ObjectProperty.isoMk _ e) (ObjectProperty.isoMk _ e'))

/-! ### The twists on projective space over a base -/

attribute [local instance] MvPolynomial.gradedAlgebra

variable (n : ℕ) (S : Scheme.{u})

/-- **The degree-`d` twist of the structure sheaf of `ℙⁿ_S`**: the pullback along the projection
`ℙⁿ_S ⟶ ℙⁿ_ℤ` of the degree-`d` twisting sheaf of Stacks Tag 01MN on the integral model. At
`d = 1` this is `Stacks.AmpleProjectiveImmersion.projectiveSpaceTwistingSheaf n S` on the nose. -/
abbrev twistOver (d : ℤ) : (projectiveSpaceOver n S).Modules :=
  (Scheme.Modules.pullback (projectiveSpaceOver.toIntegralAtUniverse n S)).obj
    (twistingSheaf (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ)) d)

/-- The hyperplane sheaf on `ℙⁿ_S` is the degree-one twist. -/
theorem twistOver_one : twistOver n S 1 = projectiveSpaceTwistingSheaf n S := rfl

/-- **A polynomial ring is generated in degree one.** The degree-one homogeneous elements of
`ℤ[T₀, …, Tₙ]` generate it as an algebra over the degree-zero part. -/
theorem adjoin_degreeOne_integralModel :
    Algebra.adjoin (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ) 0)
      ((MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ) 1 :
          Submodule _ (MvPolynomial (Fin (n + 1)) (ULift.{u} ℤ))) :
        Set (MvPolynomial (Fin (n + 1)) (ULift.{u} ℤ))) = ⊤ := by
  rw [← Stacks.AlgebraicGeometry.ProjTwistMono.range_coe_degree_one
    (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ))]
  exact Stacks.AlgebraicGeometry.TwistFlatness.adjoin_degree_one_homogeneousSubmodule
    (Fin (n + 1)) (ULift.{u} ℤ)

/-- **Stacks Tag 01MU on the integral model of projective space.** The multiplication map
`𝒪(a) ⊗ 𝒪(b) ⟶ 𝒪(a + b)` on `ℙⁿ_ℤ` is an isomorphism for all integer `a` and `b`. -/
theorem isIso_twistMultiplicationMap_integralModel (a b : ℤ) :
    IsIso (twistMultiplicationMap
      (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ)) a b) :=
  Stacks.AlgebraicGeometry.ProjRepresentsF1.isIso_twistMultiplicationMap_of_adjoin _
    (adjoin_degreeOne_integralModel n) a b

/-- **Every twist on the integral model of projective space is invertible.** This is
`Stacks.ProjectiveSpace.isInvertibleModule_twistingSheaf_homogeneousSubmodule`, restated at the
spelling `AlgebraicGeometry.projectiveSpaceAtUniverse`, which is a `def` that instance search
does not unfold. -/
instance isInvertibleModule_twistingSheaf_integralModel (d : ℤ) :
    IsInvertibleModule (projectiveSpaceAtUniverse.{u} n)
      (twistingSheaf (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ)) d) :=
  Stacks.ProjectiveSpace.isInvertibleModule_twistingSheaf_homogeneousSubmodule
    (ULift.{u} ℤ) n d

/-- **Every twist on `ℙⁿ_S` is invertible**, with no hypothesis on `S`: it is a pullback, and
invertibility is stable under pullback (Stacks Tag 0B8L). At `d = 1` this is
`Stacks.AmpleProjectiveImmersion.isInvertibleModule_projectiveSpaceTwistingSheaf`. -/
instance isInvertibleModule_twistOver (d : ℤ) :
    IsInvertibleModule (projectiveSpaceOver n S) (twistOver n S d) :=
  Stacks.InvertiblePullback.isInvertibleModule_pullback
    (projectiveSpaceOver.toIntegralAtUniverse n S) _

/-- **The multiplication isomorphism `𝒪(a) ⊗ 𝒪(b) ≅ 𝒪(a + b)` on `ℙⁿ_S`**, in all integer
degrees. Stacks Tag 01CD commutes the pullback past the tensor product, and the multiplication map
on the integral model is an isomorphism by Stacks Tag 01MU, so its image under the pullback functor
is one too. -/
def twistOverMulIso (a b : ℤ) :
    tensorModules (projectiveSpaceOver n S) (twistOver n S a) (twistOver n S b) ≅
      twistOver n S (a + b) :=
  (pullbackTensorModulesIso (projectiveSpaceOver.toIntegralAtUniverse n S)
      (twistingSheaf (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ)) a)
      (twistingSheaf
        (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ)) b)).symm ≪≫
    (modulePullback
        (projectiveSpaceOver.toIntegralAtUniverse n S).toLRSHom.toShHom).mapIso
      (@asIso _ _ _ _ _ (isIso_twistMultiplicationMap_integralModel.{u} n a b))

/-! ### The degree-zero twist is the structure sheaf -/

/-- **`𝒪(0) ≅ 𝒪` on `ℙⁿ_S`.** The multiplication isomorphism at `(0, 0)` says that `𝒪(0)` is
isomorphic to its own tensor square, and an invertible module with that property is the structure
sheaf.

The canonical map `𝒪(0) ⟶ 𝒪` on `Proj` of a graded ring is invertible too,
`Stacks.AlgebraicGeometry.ProjEulerSequence.isIso_twistUnitMap`. -/
def twistZeroIsoUnit : twistOver n S 0 ≅ unitModule (projectiveSpaceOver n S) :=
  isoUnitModuleOfTensorSelfIso (projectiveSpaceOver n S) (twistOver n S 0)
    (twistOverMulIso n S 0 0 ≪≫
      eqToIso (congrArg (twistOver n S) (add_zero (0 : ℤ))))

/-- **`𝒪(d) ⊗ 𝒪(-d) ≅ 𝒪` on `ℙⁿ_S`**: the twist in the opposite degree is a tensor inverse. -/
def twistOverNegIsoUnit (d : ℤ) :
    tensorModules (projectiveSpaceOver n S) (twistOver n S d) (twistOver n S (-d)) ≅
      unitModule (projectiveSpaceOver n S) :=
  twistOverMulIso n S d (-d) ≪≫
    eqToIso (congrArg (twistOver n S) (add_neg_cancel d)) ≪≫
    twistZeroIsoUnit n S

/-! ### The tensor powers of the hyperplane sheaf -/

/-- **`𝒪(1)^{⊗ (k+1)} ≅ 𝒪(k+1)` on `ℙⁿ_S`**, by induction on `k`. The step splits the power as
`𝒪(1)^{⊗ k} ⊗ 𝒪(1)` with `Stacks.Ample.tensorPowModuleAddIso` and multiplies the two twists with
`Stacks.AlgebraicGeometry.ProjTwistTensorPow.twistOverMulIso`. -/
def tensorPowSuccIso : (k : ℕ) →
    tensorPowModule (projectiveSpaceOver n S) (twistOver n S 1) ((k + 1 : ℕ) : ℤ) ≅
      twistOver n S ((k + 1 : ℕ) : ℤ)
  | 0 =>
      tensorPowModuleCongr (projectiveSpaceOver n S) (twistOver n S 1)
          (show ((0 + 1 : ℕ) : ℤ) = 1 from by norm_num) ≪≫
        tensorPowModuleOneIso (projectiveSpaceOver n S) (twistOver n S 1) ≪≫
        eqToIso (congrArg (twistOver n S)
          (show (1 : ℤ) = ((0 + 1 : ℕ) : ℤ) from by norm_num))
  | (k + 1) =>
      tensorPowModuleCongr (projectiveSpaceOver n S) (twistOver n S 1)
          (show ((k + 1 + 1 : ℕ) : ℤ) = ((k + 1 : ℕ) : ℤ) + 1 from by push_cast; ring) ≪≫
        (tensorPowModuleAddIso (projectiveSpaceOver n S) (twistOver n S 1)
          ((k + 1 : ℕ) : ℤ) 1).symm ≪≫
        tensorModulesMapIso (projectiveSpaceOver n S) (tensorPowSuccIso k)
          (tensorPowModuleOneIso (projectiveSpaceOver n S) (twistOver n S 1)) ≪≫
        twistOverMulIso n S ((k + 1 : ℕ) : ℤ) 1 ≪≫
        eqToIso (congrArg (twistOver n S)
          (show ((k + 1 : ℕ) : ℤ) + 1 = ((k + 1 + 1 : ℕ) : ℤ) from by push_cast; ring))

/-- **`𝒪(1)^{⊗ (-(k+1))} ≅ 𝒪(-(k+1))` on `ℙⁿ_S`.** Both sides are tensor inverses of the already
identified pair `𝒪(1)^{⊗ (k+1)} ≅ 𝒪(k+1)` — the first by the addition law for the tensor powers,
the second by the multiplication isomorphism of the twists — and a tensor inverse is unique up to
isomorphism. -/
def tensorPowNegSuccIso (k : ℕ) :
    tensorPowModule (projectiveSpaceOver n S) (twistOver n S 1) (-((k + 1 : ℕ) : ℤ)) ≅
      twistOver n S (-((k + 1 : ℕ) : ℤ)) :=
  isoOfTensorUnitIso (projectiveSpaceOver n S)
    (tensorPowModule (projectiveSpaceOver n S) (twistOver n S 1) (-((k + 1 : ℕ) : ℤ)))
    (twistOver n S (-((k + 1 : ℕ) : ℤ)))
    (tensorPowModule (projectiveSpaceOver n S) (twistOver n S 1) ((k + 1 : ℕ) : ℤ))
    (tensorPowModuleAddIso (projectiveSpaceOver n S) (twistOver n S 1)
        (-((k + 1 : ℕ) : ℤ)) ((k + 1 : ℕ) : ℤ) ≪≫
      tensorPowModuleCongr (projectiveSpaceOver n S) (twistOver n S 1)
        (neg_add_cancel _) ≪≫
      tensorPowModuleZeroIso (projectiveSpaceOver n S) (twistOver n S 1))
    (tensorModulesMapIso (projectiveSpaceOver n S)
        (Iso.refl (twistOver n S (-((k + 1 : ℕ) : ℤ))))
        (tensorPowSuccIso n S k) ≪≫
      twistOverNegIsoUnit n S (-((k + 1 : ℕ) : ℤ)))

/-- **`𝒪(1)^{⊗ d} ≅ 𝒪(d)` on projective `n`-space over an arbitrary base scheme**, for every
integer `d`: the `d`-th tensor power of Stacks Tag 01CU of the hyperplane sheaf is the degree-`d`
twist of Stacks Tag 01MN, pulled back from the integral model. -/
def tensorPowModuleProjectiveTwistIso : (d : ℤ) →
    tensorPowModule (projectiveSpaceOver n S) (projectiveSpaceTwistingSheaf n S) d ≅
      (Scheme.Modules.pullback (projectiveSpaceOver.toIntegralAtUniverse n S)).obj
        (twistingSheaf (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ)) d)
  | .ofNat 0 =>
      tensorPowModuleZeroIso (projectiveSpaceOver n S) (twistOver n S 1) ≪≫
        (twistZeroIsoUnit n S).symm
  | .ofNat (k + 1) => tensorPowSuccIso n S k
  | .negSucc k =>
      tensorPowModuleCongr (projectiveSpaceOver n S) (twistOver n S 1)
          (show (Int.negSucc k) = -((k + 1 : ℕ) : ℤ) from by push_cast; rfl) ≪≫
        tensorPowNegSuccIso n S k ≪≫
        eqToIso (congrArg (twistOver n S)
          (show -((k + 1 : ℕ) : ℤ) = (Int.negSucc k) from by push_cast; rfl))

end Stacks.AlgebraicGeometry.ProjTwistTensorPow

end
