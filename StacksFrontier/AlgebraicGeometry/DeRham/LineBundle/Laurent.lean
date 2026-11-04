module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedAlgebraBridge
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InvertibleCompare
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InvertibleRankOne.Converse
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LaurentAlgebra
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorPower
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorPowerQuasicoherent
public import StacksFrontier.AlgebraicGeometry.DeRham.LineBundle.Punctured
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The Laurent algebra of a line bundle

Let `f : X ⟶ S` be a morphism of schemes and `L` an invertible `𝒪_X`-module. The total space of
`L` is the relative spectrum of `Sym(L) = ⨁_{n ≥ 0} L^{⊗ n}`, and its punctured version is
expected to be the relative spectrum of the **Laurent algebra** `⨁_{n ∈ ℤ} L^{⊗ n}`, which
inverts the degree-one generator. This file constructs that algebra for a line bundle, as a
sheaf of graded algebras and as a sheaf of commutative `𝒪_X`-algebras, and identifies the module
underlying the latter with the direct sum of the integer tensor powers.

The symmetric algebra vanishes in negative degrees, and the degree-zero augmentation and the
identification of the underlying module with the coproduct over the *nonnegative* degrees both
rest on that vanishing. Neither applies to the Laurent algebra, so the identification of the
underlying module is redone here over all of `ℤ`, where it is in fact shorter: the passage
through `Stacks.directSumNatToInt` disappears.

## Main definitions

* `Stacks.RelativeSpec.coprodIntIsoUnderlyingModule`: **the module underlying the ungraded
  algebra sheaf of a sheaf of graded algebras is the coproduct of its homogeneous pieces over
  all of `ℤ`.**
* `Stacks.LineBundle.Situation.laurentAlgebra`: **the Laurent algebra `⨁_{n ∈ ℤ} L^{⊗ n}` of the
  line bundle**, as a sheaf of graded algebras over the structure sheaf.
* `Stacks.LineBundle.Situation.laurentAlgebraSheaf`: **its ungraded realization, as a sheaf of
  commutative `𝒪_X`-algebras.**
* `Stacks.LineBundle.Situation.laurentAlgebraSheafIncl`: a homogeneous local section of
  `L^{⊗ n}`, viewed in the sections of that algebra sheaf. This is the `ℤ`-grading of the
  sections.
* `Stacks.LineBundle.Situation.laurentCoprodIsoUnderlyingModule`: the module underlying the
  Laurent algebra sheaf of the line bundle is `⨁_{n ∈ ℤ} L^{⊗ n}`.
* `Stacks.LineBundle.Situation.laurentPieceZeroIso`: **degree zero of the Laurent algebra is the
  structure sheaf of the scheme on which `L` lives.**
* `Stacks.LineBundle.Situation.laurentGen`: the degree-one generator `L ⟶ L^{⊗ 1}`.
* `Stacks.LineBundle.Situation.symmetricToLaurent`: **the comparison
  `Sym(L) ⟶ ⨁_{n ∈ ℤ} L^{⊗ n}`**, the unique unital homomorphism of sheaves of graded algebras
  extending that generator, and `symmetricToLaurentHom` the same as a morphism of the category
  of sheaves of graded algebras.

## Main results

* `Stacks.RelativeSpec.isQuasicoherent_ungradedAlgebraSheaf_of_coprodInt`: an ungraded algebra
  sheaf whose coproduct over all of `ℤ` is quasi-coherent is quasi-coherent. This is the
  hypothesis-free counterpart, for algebras with sections in negative degrees, of
  `Stacks.RelativeSpec.isQuasicoherent_ungradedAlgebraSheaf`.
* `Stacks.LineBundle.Situation.laurentAlgebra_mul_comm`: homogeneous multiplication in the
  Laurent algebra of the line bundle commutes, which is what makes its ungraded realization a
  sheaf of commutative rings.
* `Stacks.LineBundle.Situation.isQuasicoherent_laurentAlgebra_piece`: **every integer tensor
  power of the line bundle is quasi-coherent**, being invertible.
* `Stacks.LineBundle.Situation.laurentAlgebraSheafIncl_mul` and
  `laurentAlgebraSheafIncl_one`: the grading is multiplicative and unital.
* `Stacks.LineBundle.Situation.symmetricToLaurent_app_eq_zero`: the comparison of the symmetric
  algebra with the Laurent algebra vanishes in negative degrees, where `Sym(L)` is zero.

## Implementation notes

Two invertibility predicates for a sheaf of modules are in use, and a `Situation` carries the
`AlgebraicGeometry` one while the tensor powers of Tag 01CU are indexed by the `Stacks` one. The
transfer `Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry` is registered here as an
instance *for the line bundle of a situation only*: a general instance in that direction would
pair with the converse one and make instance search cycle between the two classes, which is why
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InvertibleCompare` registers neither.

`Stacks.SheafOfModules.Invertible.tensorRightFunctor_isEquivalence` is an instance that
instance search does not find: the functor it concludes about is the native tensor bifunctor
`Stacks.SheafOfModules.Tensor.sheafTensor`, flipped and evaluated at the module, and the sheaf
condition packed into its structure-sheaf argument is not recoverable from the goal by
unification. It is applied by hand to produce the instance the tensor powers are indexed by.

The comparison with the symmetric algebra is obtained from the universal property
`SheafOfModules.GradedAlgebra.IsSymmetricAlgebra`, so no degreewise formula is needed: the
degree-one generator is the inverse of the comparison of the first tensor power with `L`, and
the side condition is the commutativity of the coherent multiplication in degrees `(1, 1)`,
where the two sides already lie in the same homogeneous piece.

## References

* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
* [Stacks Project, Tag 0FQW](https://stacks.math.columbia.edu/tag/0FQW)
* [Stacks Project, Tag 01CL](https://stacks.math.columbia.edu/tag/01CL)
* [Stacks Project, Tag 0FUH](https://stacks.math.columbia.edu/tag/0FUH)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace AlgebraicGeometry

universe u

namespace Stacks.RelativeSpec

variable (X : Scheme.{u}) (A : SheafOfModules.GradedAlgebra.{u, u} X.ringCatSheaf)
  (hA : ∀ (i j : ℤ) (U : (Opens X)ᵒᵖ) (x : (A.piece i).val.obj U) (y : (A.piece j).val.obj U),
    HEq ((A.mul i j).app U x y) ((A.mul j i).app U y x))

/-- **The module underlying the ungraded algebra sheaf of a sheaf of graded algebras is the
coproduct of its homogeneous pieces over all of `ℤ`.** No vanishing in negative degrees is
assumed, so this applies to a Laurent algebra. -/
def coprodIntIsoUnderlyingModule :
    (∐ fun n : ℤ => A.piece n) ≅
      AlgebraSheaf.underlyingModule (ungradedAlgebraSheaf X A hA) :=
  (Stacks.sheafifyDirectSumIso (fun n : ℤ => A.piece n)).symm ≪≫
    directSumIsoUnderlyingModule X A hA

/-- **An ungraded algebra sheaf whose coproduct over all of `ℤ` is quasi-coherent is
quasi-coherent.** This is the datum a relative spectrum requires, for an algebra with sections
in negative degrees. -/
theorem isQuasicoherent_ungradedAlgebraSheaf_of_coprodInt
    (hqc : (∐ fun n : ℤ => A.piece n).IsQuasicoherent) :
    AlgebraSheaf.IsQuasicoherent (ungradedAlgebraSheaf X A hA) :=
  (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
    (coprodIntIsoUnderlyingModule X A hA) hqc

end Stacks.RelativeSpec

namespace Stacks.LineBundle

open Stacks.SheafOfModules Stacks.SheafOfModules.TensorPower

variable (D : Situation.{u})

/-- The line bundle of a situation is invertible in the spelling the tensor powers of Tag 01CU
are indexed by. -/
instance Situation.isInvertible_stacks :
    Stacks.SheafOfModules.IsInvertible D.X.sheaf.obj D.X.ringCatSheaf.property D.L :=
  Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ _ D.invertible

/-- Tensoring by the line bundle of a situation is an autoequivalence of its sheaves of modules,
which is the datum the integer tensor powers are indexed by. -/
instance Situation.isEquivalence_tensorRightFunctor :
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ⟨D.X.sheaf.obj, Presheaf.isSheaf_of_isSheaf_comp _ D.X.sheaf.obj
        (forget₂ CommRingCat RingCat) D.X.ringCatSheaf.property⟩).flip.obj D.L).IsEquivalence :=
  Stacks.SheafOfModules.Invertible.tensorRightFunctor_isEquivalence _ _ _

/-- **The `n`th integer tensor power `L^{⊗ n}` of the line bundle of a situation**, for
`n : ℤ`. -/
def Situation.tensorPower (n : ℤ) : D.X.Modules :=
  Stacks.SheafOfModules.TensorPower.tensorPower D.X.sheaf.obj D.X.ringCatSheaf.property D.L n

/-- **Every integer tensor power of the line bundle of a situation is invertible.** -/
instance Situation.isInvertible_tensorPower (n : ℤ) :
    AlgebraicGeometry.SheafOfModules.IsInvertible D.X.sheaf.obj D.X.ringCatSheaf.property
      (D.tensorPower n) :=
  Stacks.SheafOfModules.IsInvertible.toAlgebraicGeometry _ _ _
    (Stacks.SheafOfModules.TensorPower.isInvertible_tensorPower D.X.sheaf.obj
      D.X.ringCatSheaf.property D.L n)

/-- **Every integer tensor power of the line bundle of a situation is quasi-coherent**, being
invertible. -/
instance Situation.isQuasicoherent_tensorPower (n : ℤ) : (D.tensorPower n).IsQuasicoherent :=
  Stacks.Divisors.isQuasicoherent_of_isInvertible (X := D.X) (D.tensorPower n)

/-- **The Laurent algebra `⨁_{n ∈ ℤ} L^{⊗ n}` of the line bundle**, as a sheaf of graded algebras
over the structure sheaf. Its homogeneous piece in degree `n` is the `n`th integer tensor power
of `L`, and its multiplication is the coherent multiplication of Tag 01CU. -/
def Situation.laurentAlgebra : SheafOfModules.GradedAlgebra.{u, u} D.X.ringCatSheaf :=
  Stacks.SheafOfModules.TensorPower.laurentAlgebra D.X.sheaf.obj D.X.ringCatSheaf.property D.L

@[simp]
theorem Situation.laurentAlgebra_piece (n : ℤ) :
    D.laurentAlgebra.piece n = D.tensorPower n :=
  rfl

/-- **Homogeneous multiplication in the Laurent algebra of the line bundle commutes**, in every
pair of degrees. This is what makes its ungraded realization a sheaf of commutative rings. -/
theorem Situation.laurentAlgebra_mul_comm (i j : ℤ) (U : (Opens D.X)ᵒᵖ)
    (x : (D.laurentAlgebra.piece i).val.obj U) (y : (D.laurentAlgebra.piece j).val.obj U) :
    HEq ((D.laurentAlgebra.mul i j).app U x y) ((D.laurentAlgebra.mul j i).app U y x) :=
  Stacks.SheafOfModules.TensorPower.laurentAlgebra_mul_comm D.X.sheaf.obj
    D.X.ringCatSheaf.property D.L i j U x y

/-- **The Laurent algebra sheaf of the line bundle**: the ungraded realization of
`⨁_{n ∈ ℤ} L^{⊗ n}`, as a sheaf of commutative `𝒪_X`-algebras. -/
@[sga "6 IX 2.2" "partial"]
def Situation.laurentAlgebraSheaf : Stacks.RelativeSpec.AlgebraSheaf D.X :=
  Stacks.RelativeSpec.ungradedAlgebraSheaf D.X D.laurentAlgebra D.laurentAlgebra_mul_comm

/-- **A homogeneous local section of `L^{⊗ n}`, viewed in the sections of the Laurent algebra
sheaf of the line bundle.** This is the `ℤ`-grading of those sections. -/
def Situation.laurentAlgebraSheafIncl (n : ℤ) (U : D.X.Opens)
    (x : (D.tensorPower n).val.obj (.op U)) :
    Stacks.RelativeSpec.AlgebraSheaf.sections D.laurentAlgebraSheaf U :=
  Stacks.RelativeSpec.ungradedAlgebraSheafIncl D.X D.laurentAlgebra D.laurentAlgebra_mul_comm
    n U x

/-- The product of two homogeneous local sections in the Laurent algebra sheaf of the line
bundle is the image of their graded product, so the grading is multiplicative. -/
theorem Situation.laurentAlgebraSheafIncl_mul (n m : ℤ) (U : D.X.Opens)
    (x : (D.tensorPower n).val.obj (.op U)) (y : (D.tensorPower m).val.obj (.op U)) :
    D.laurentAlgebraSheafIncl n U x * D.laurentAlgebraSheafIncl m U y =
      D.laurentAlgebraSheafIncl (n + m) U ((D.laurentAlgebra.mul n m).app (.op U) x y) :=
  Stacks.RelativeSpec.ungradedAlgebraSheafIncl_mul D.X D.laurentAlgebra
    D.laurentAlgebra_mul_comm n m U x y

/-- The image of the unit of the Laurent algebra in its algebra sheaf is the unit. -/
theorem Situation.laurentAlgebraSheafIncl_one (U : D.X.Opens) :
    D.laurentAlgebraSheafIncl 0 U (D.laurentAlgebra.one.eval (.op U)) = 1 :=
  Stacks.RelativeSpec.ungradedAlgebraSheafIncl_one D.X D.laurentAlgebra
    D.laurentAlgebra_mul_comm U

/-- **The module underlying the Laurent algebra sheaf of the line bundle is
`⨁_{n ∈ ℤ} L^{⊗ n}`.** -/
def Situation.laurentCoprodIsoUnderlyingModule :
    (∐ fun n : ℤ => D.tensorPower n) ≅
      Stacks.RelativeSpec.AlgebraSheaf.underlyingModule D.laurentAlgebraSheaf :=
  Stacks.RelativeSpec.coprodIntIsoUnderlyingModule D.X D.laurentAlgebra
    D.laurentAlgebra_mul_comm

/-- **The line bundle of a situation is locally trivial**: its stalks are local rings, so the
opens on which a nonvanishing section generates it cover the scheme. -/
@[ega "IV 21.13.16" "partial"]
instance Situation.isLocallyTrivial : Stacks.SheafOfModules.Invertible.IsLocallyTrivial D.L := by
  have : Stacks.SheafOfModules.IsInvertible D.X.toRingedSpace.presheaf
      (structureSheafRing
        D.X.toRingedSpace).property D.L :=
    D.isInvertible_stacks
  exact Stacks.SheafOfModules.Invertible.isLocallyTrivial_of_isInvertible
    (X := D.X.toRingedSpace) D.L

/-- **The direct sum `⨁_{n ∈ ℤ} L^{⊗ n}` of the integer tensor powers of the line bundle is
quasi-coherent**: an open trivializing `L` trivializes every tensor power of `L` at once, which
is the uniformity of the covering family that Tag 01CL requires. -/
instance Situation.isQuasicoherent_coprod_tensorPower :
    (∐ fun n : ℤ => D.tensorPower n).IsQuasicoherent := by
  have : Stacks.SheafOfModules.Invertible.IsLocallyTrivial
      (R := Stacks.SheafOfModules.TensorSheafification.structureSheaf D.X.sheaf.obj
        D.X.ringCatSheaf.property) D.L :=
    D.isLocallyTrivial
  exact Stacks.SheafOfModules.TensorPower.isQuasicoherent_coprod_tensorPower D.X.sheaf.obj
    D.X.ringCatSheaf.property D.L

/-- **The Laurent algebra sheaf of the line bundle is quasi-coherent**, its underlying module
being the direct sum of the integer tensor powers of `L`. This is the datum a relative spectrum
requires. -/
instance Situation.isQuasicoherent_laurentAlgebraSheaf :
    Stacks.RelativeSpec.AlgebraSheaf.IsQuasicoherent D.laurentAlgebraSheaf :=
  Stacks.RelativeSpec.isQuasicoherent_ungradedAlgebraSheaf_of_coprodInt D.X D.laurentAlgebra
    D.laurentAlgebra_mul_comm D.isQuasicoherent_coprod_tensorPower

/-- The scheme on which the line bundle lives, together with the quasi-coherent sheaf of
algebras `⨁_{n ∈ ℤ} L^{⊗ n}`, as a relative-spectrum situation. -/
@[sga "3 VIII 4.3" "partial"]
def Situation.laurentRelativeSpecSituation : Stacks.RelativeSpec.RelativeSpecSituation.{u} where
  base := D.X
  algebra := D.laurentAlgebraSheaf

/-- **The relative spectrum of the Laurent algebra `⨁_{n ∈ ℤ} L^{⊗ n}` of the line bundle**, over
the scheme on which `L` lives. -/
@[sga "3 VIII 4.3" "partial", sga "6 IX 2.2" "partial"]
def Situation.laurentSpectrum : Scheme.{u} :=
  (Stacks.RelativeSpec.gluedSpectrum D.laurentRelativeSpecSituation).scheme

/-- The structure morphism of the relative spectrum of the Laurent algebra of the line
bundle. -/
@[sga "3 VIII 4.3" "partial", sga "6 IX 2.2" "partial"]
def Situation.laurentSpectrumToBase : D.laurentSpectrum ⟶ D.X :=
  (Stacks.RelativeSpec.gluedSpectrum D.laurentRelativeSpecSituation).toBase

/-! ### Degree zero, and the comparison with the symmetric algebra -/

/-- **Degree zero of the Laurent algebra of the line bundle is the structure sheaf of the scheme
on which `L` lives**, the zeroth tensor power of `L` being the structure sheaf. -/
def Situation.laurentPieceZeroIso :
    D.laurentAlgebra.piece 0 ≅ SheafOfModules.unit D.X.ringCatSheaf :=
  Iso.refl _

/-- The degree-zero identification of the Laurent algebra carries the algebra unit to `1`. -/
theorem Situation.laurentPieceZeroIso_hom_one (U : (Opens D.X)ᵒᵖ) :
    D.laurentPieceZeroIso.hom.val.app U (D.laurentAlgebra.one.eval U) =
      (1 : D.X.ringCatSheaf.obj.obj U) :=
  rfl

/-- **The degree-one generator `L ⟶ L^{⊗ 1}` of the Laurent algebra of the line bundle.** -/
def Situation.laurentGen : D.L ⟶ D.laurentAlgebra.piece 1 :=
  (Stacks.SheafOfModules.TensorPower.tensorPowerOneIso D.X.sheaf.obj
    D.X.ringCatSheaf.property D.L).inv

/-- The degree-one generator of the Laurent algebra is an isomorphism: the first tensor power of
`L` is `L`. -/
instance Situation.isIso_laurentGen : IsIso D.laurentGen :=
  Iso.isIso_inv _

/-- Local sections of `L` have commuting images under the degree-one generator, the coherent
multiplication of Tag 01CU being commutative. -/
theorem Situation.pairwiseCommutes_laurentGen :
    SheafOfModules.GradedAlgebra.PairwiseCommutes D.laurentGen := fun U _ _ =>
  eq_of_heq (D.laurentAlgebra_mul_comm 1 1 U _ _)

/-- **The comparison `Sym(L) ⟶ ⨁_{n ∈ ℤ} L^{⊗ n}` of the symmetric algebra of the line bundle
with its Laurent algebra**: the unique unital homomorphism of sheaves of graded algebras
extending the degree-one generator `L ⟶ L^{⊗ 1}`. -/
def Situation.symmetricToLaurent :
    SheafOfModules.GradedAlgebra.UnitalHom D.symmetricAlgebra D.laurentAlgebra :=
  D.isSymmetricAlgebra_symmetricAlgebra.isUniversal.desc D.laurentAlgebra D.laurentGen
    D.pairwiseCommutes_laurentGen

/-- The comparison of the symmetric algebra with the Laurent algebra extends the degree-one
generator. -/
theorem Situation.symmetricAlgebraGen_comp_symmetricToLaurent :
    D.symmetricAlgebraGen ≫ D.symmetricToLaurent.app 1 = D.laurentGen :=
  D.isSymmetricAlgebra_symmetricAlgebra.isUniversal.desc_extends _ _ _

/-- The comparison of the symmetric algebra with the Laurent algebra is the only unital
homomorphism extending the degree-one generator. -/
theorem Situation.symmetricToLaurent_unique
    {g : SheafOfModules.GradedAlgebra.UnitalHom D.symmetricAlgebra D.laurentAlgebra}
    (hg : D.symmetricAlgebraGen ≫ g.app 1 = D.laurentGen) : g = D.symmetricToLaurent :=
  D.isSymmetricAlgebra_symmetricAlgebra.isUniversal.desc_unique _ _ _ hg

/-- **The comparison of the symmetric algebra with the Laurent algebra vanishes in negative
degrees**, where `Sym(L)` is zero while the Laurent algebra is not. -/
theorem Situation.symmetricToLaurent_app_eq_zero (n : ℤ) (hn : n < 0) :
    D.symmetricToLaurent.app n = 0 :=
  (D.isZero_symmetricAlgebra_piece n hn).eq_of_src _ _

/-- **The comparison of the symmetric algebra of the line bundle with its Laurent algebra**, as
a morphism in the category of sheaves of graded algebras. -/
def Situation.symmetricToLaurentHom : D.symmetricAlgebra ⟶ D.laurentAlgebra :=
  D.symmetricToLaurent.toHom

@[simp]
theorem Situation.symmetricToLaurentHom_app (n : ℤ) :
    D.symmetricToLaurentHom.app n = D.symmetricToLaurent.app n :=
  rfl

end Stacks.LineBundle

end
