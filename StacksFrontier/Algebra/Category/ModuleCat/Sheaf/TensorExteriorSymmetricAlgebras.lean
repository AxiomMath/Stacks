module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafificationTensor

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SymmetricPowerSheafification
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The tensor, exterior and symmetric algebras of a sheaf of modules

Let `O` be a sheaf of commutative rings on a site `(C, J)` and let `F` be a sheaf of
`O`-modules. Stacks Section 17.21 attaches to `F` three sheaves of graded `O`-algebras: the
tensor algebra `T(F)`, its exterior quotient `⋀(F)` and its symmetric quotient `Sym(F)`, whose
homogeneous pieces are the tensor, exterior and symmetric powers of `F`. This file fixes the
tensor powers of `F` and bundles that whole package — the three algebras, their three universal
properties, the identification of the pieces of `T(F)` with the tensor powers, and the two
quotient maps — as a single structure
`SheafOfModules.TensorExteriorSymmetricAlgebras`, together with everything about it that
follows from the three universal properties alone.

Taking that structure as a hypothesis is how a statement about *the* tensor, exterior or
symmetric algebra of `F` is made without naming one: `tensorAlgebraIso`,
`exteriorAlgebraIso` and `symmetricAlgebraIso` show that two such bundles over the same `F`
have canonically isomorphic algebras in every degree, compatibly with the generators and with
multiplication, so a statement quantified over bundles is a statement about the canonical
objects and is strictly stronger than one about a single chosen bundle.

## Main definitions

* `SheafOfModules.tensorPower`: the `n`-fold tensor power of a sheaf of modules, with the
  zeroth power the structure sheaf, the first power the sheaf itself, and the higher powers
  obtained by tensoring on the left with `Stacks.SheafOfModules.Tensor.sheafTensor`.
* `SheafOfModules.TensorExteriorSymmetricAlgebras`: the bundle described above.
* `TensorExteriorSymmetricAlgebras.exteriorPower` and `symmetricPower`: the homogeneous pieces
  `⋀ⁿ F` and `Symⁿ F`, and `tensorAlgebraSheaf`, `exteriorAlgebraSheaf`,
  `symmetricAlgebraSheaf`: the underlying sheaves of modules, as direct sums of the
  homogeneous pieces.
* `TensorExteriorSymmetricAlgebras.tensorPieceZeroIsoUnit` and `exteriorPieceZeroIsoUnit`: the
  degree-zero identifications, with the zeroth tensor power spelled as the structure sheaf.
* `TensorExteriorSymmetricAlgebras.symPowComparison`: the comparison morphism from the presheaf
  of sectionwise symmetric powers of `F` into `Symⁿ F`, i.e. the morphism Stacks 01CG asserts
  becomes an isomorphism after sheafification.
* `TensorExteriorSymmetricAlgebras.tensorAlgebraIso`, `exteriorAlgebraIso` and
  `symmetricAlgebraIso`: the canonical comparisons between two bundles over the same `F`.

## Main results

* `TensorExteriorSymmetricAlgebras.tensorToExterior_eq` and `tensorToSymmetric_eq`: the two
  quotient maps are not extra data — each is the homomorphism the tensor algebra's universal
  property produces from the corresponding generator.
* `TensorExteriorSymmetricAlgebras.tensorGenerator_eq` and `isIso_tensorGenerator`: the
  degree-one generator of `T(F)` is inverse to the degree-one identification, hence an
  isomorphism: the degree-one piece of the tensor algebra *is* `F`.
* `TensorExteriorSymmetricAlgebras.tensorPieceZeroIsoUnit_smul_one` and
  `exteriorPieceZeroIsoUnit_smul_one`: a degree-zero local section of `T(F)` or of `⋀(F)` is
  its own image under the degree-zero identification times the unit, so degree zero is free of
  rank one on the unit.
* `TensorExteriorSymmetricAlgebras.tensorDirectSumIso_unique`: the direct-sum comparison is the
  only isomorphism induced by the homogeneous identifications, so that field of the bundle is
  determined by the field above it.
* `TensorExteriorSymmetricAlgebras.tensorAlgebraIso_generator`, `tensorAlgebraIso_mul` and
  their exterior and symmetric analogues: the comparisons between two bundles respect the
  generators and multiplication.
* `SheafOfModules.ringSheaf_eq`: for a ringed space the base used here is the sheaf of rings
  `structureSheafRing` on the nose, which is the repoint for the
  ringed-space statements of Section 17.21.

## Implementation notes

**What is here and what is not.** This file states the bundle and develops its consequences; it
does **not** construct one. Constructing it means building the tensor algebra of a sheaf of
modules together with the identification of its degree-`n` piece with the `n`-fold sheafified
tensor power, and then its two quotients, each with its full universal property. The route is
to realize each of the three graded algebras as the sheafification of its sectionwise
counterpart and transfer the universal property through the sheafification unit, for which the
pieces already present are `Stacks.BilinearMap.extend` and `existsUnique_extend`
(extension of a sectionwise bilinear map along a locally surjective morphism into a separated
presheaf), `Stacks.GradedAlgebra.totalPresheaf` (the ungraded realization, which is what turns
a sectionwise universal property of `TensorAlgebra`, `ExteriorAlgebra` or `SymmetricAlgebra`
into a degreewise statement), `SymmetricAlgebra.gradedAlgebra` and
`PresheafOfModules.symPow`. What is missing is the assembly of a sheafified graded presheaf
algebra into a `SheafOfModules.GradedAlgebra` and the comparison of the sheafified sectionwise
tensor powers with the iterated sheafified tensor products. Nothing below is specialized in
anticipation of that construction, and nothing below depends on it.

**Universes.** The site universes `u`, `v` are independent of the ring universe `w`, but the
module universe is `w` as well, and that is forced rather than chosen in two places. The tensor
product of sheaves of modules used for the tensor powers is Mathlib's objectwise tensor product
of presheaves of modules, sheafified, which exists only over a presheaf of commutative rings in
the module universe; and the degree-zero identifications land in the structure sheaf, whose
sections are the ring's. The source works over a ringed space, where all of these universes
coincide anyway; the site here is arbitrary, which is a generalization of the source and not a
narrowing.

**The scalar of a degree-zero section is a separate argument.** In
`tensorPieceZeroIsoUnit_smul_one` the scalar is taken as `r` together with
`hr : …hom.val.app U x = r`, rather than written out in the conclusion. This is the idiom of
`SheafOfModules.GradedAlgebra.eq_smul_one_of_isoUnit`, forced for the reason documented there:
written the other way the left-hand factor has type `(SheafOfModules.unit R).val.obj U`, which
is the ring of sections only up to unfolding `SheafOfModules.unit`, and instance search for the
scalar action does not unfold it. `exists_tensor_eq_smul_one` and
`exists_exterior_eq_smul_one` are the forms with the scalar existentially quantified.

**Negative degrees.** All three algebras are concentrated in nonnegative degrees, and the
bundle records that as the vanishing of every local section in a negative degree rather than as
`IsZero` of the piece. `subsingleton_tensorPiece` and `hom_ext_tensorPiece_of_neg` are the two
forms that vanishing is used in.

## References

* [Stacks Project, Section 17.21](https://stacks.math.columbia.edu/tag/01CF)
* [Stacks Project, Tag 0FQW](https://stacks.math.columbia.edu/tag/0FQW)
* [Stacks Project, Tag 01CG](https://stacks.math.columbia.edu/tag/01CG)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf

open scoped TensorProduct

universe v u w

namespace SheafOfModules

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  {Osharp : Sheaf J CommRingCat.{w}}
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]

/-- The `n`-fold tensor power of a sheaf of modules. -/
noncomputable def tensorPower (F : SheafOfModules.{w} (toRingCat J Osharp)) :
    ℕ → SheafOfModules.{w} (toRingCat J Osharp)
  | 0 => SheafOfModules.unit (toRingCat J Osharp)
  | 1 => F
  | n + 2 => ((Stacks.SheafOfModules.Tensor.sheafTensor Osharp).obj F).obj (tensorPower F (n + 1))

variable (F : SheafOfModules.{w} (toRingCat J Osharp))

/-- Countable coproducts of sheaves of modules, stated directly: instance search for
`HasColimit (Discrete.functor _)` in `SheafOfModules` times out under Lean v4.35.0. -/
local instance : HasColimitsOfShape (Discrete ℕ) (SheafOfModules.{w} (toRingCat J Osharp)) :=
  haveI := PresheafOfModules.hasColimitsOfShape (toRingCat J Osharp).obj (Discrete ℕ)
  SheafOfModules.instHasColimitsOfShapeOfPresheafOfModulesObjFunctorOppositeRingCatIsSheaf
    (toRingCat J Osharp) (Discrete ℕ)

/-- The zeroth tensor power is the structure sheaf. -/
theorem tensorPower_zero : tensorPower J F 0 = SheafOfModules.unit (toRingCat J Osharp) := rfl

/-- The first tensor power is the sheaf itself. -/
theorem tensorPower_one : tensorPower J F 1 = F := rfl

/-- Tensor powers of degree at least two are obtained by tensoring on the left. -/
theorem tensorPower_add_two (n : ℕ) :
    tensorPower J F (n + 2) =
      ((Stacks.SheafOfModules.Tensor.sheafTensor Osharp).obj F).obj (tensorPower J F (n + 1)) := rfl

/-- The tensor algebra of a sheaf of modules together with its exterior and symmetric
quotients. -/
structure TensorExteriorSymmetricAlgebras where
  /-- The tensor algebra. -/
  tensor : GradedAlgebra.{w, w} (toRingCat J Osharp)
  /-- Its canonical degree-one generator. -/
  tensorGenerator : F ⟶ tensor.piece 1
  /-- The tensor algebra universal property. -/
  tensor_isTensorAlgebra : GradedAlgebra.IsTensorAlgebra tensor tensorGenerator
  /-- Identification of its degree `n` piece with the `n`-fold tensor power. -/
  tensorPieceIso (n : ℕ) : tensor.piece (n : ℤ) ≅ tensorPower J F n
  /-- Under the degree-one identification, the generator is the identity. -/
  tensorPieceIso_one : tensorGenerator ≫ (tensorPieceIso 1).hom = 𝟙 F
  /-- The degree-zero identification takes the algebra unit to the structure-sheaf unit. -/
  tensorPieceIso_zero (U : Cᵒᵖ) :
    (tensorPieceIso 0).hom.val.app U (tensor.one.eval U) =
      (1 : (toRingCat J Osharp).obj.obj U)
  /-- Multiplication by a degree-one generator is tensor concatenation under the canonical
  homogeneous identifications. -/
  tensorPieceIso_mul_left (n : ℕ) (U : Cᵒᵖ) (s : F.val.obj U)
      (x : (tensorPower J F (n + 1)).val.obj U) :
    (tensorPieceIso (n + 2)).hom.val.app U
        (Eq.mp (congrArg (fun k : ℤ => ((tensor.piece k).val.obj U : Type w))
            (show 1 + ((n + 1 : ℕ) : ℤ) = ((n + 2 : ℕ) : ℤ) by omega))
          ((tensor.mul 1 ((n + 1 : ℕ) : ℤ)).app U (tensorGenerator.val.app U s)
            ((tensorPieceIso (n + 1)).inv.val.app U x))) =
      ((PresheafOfModules.sheafificationAdjunction (R := Stacks.SheafOfModules.Tensor.ringSheaf
          Osharp)
        (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf Osharp).obj)).unit.app
      (PresheafOfModules.tensorObj F.val (tensorPower J F (n + 1)).val)).app U
        (s ⊗ₜ[Osharp.obj.obj U] x)
  /-- The underlying graded direct sum is canonically the direct sum of tensor powers. -/
  tensorDirectSumIso :
    (∐ fun n : ℕ => tensorPower J F n) ≅ (∐ fun n : ℕ => tensor.piece (n : ℤ))
  /-- The direct-sum comparison is induced by the homogeneous identifications. -/
  tensorDirectSumIso_ι (n : ℕ) :
    Sigma.ι (fun m : ℕ => tensorPower J F m) n ≫ tensorDirectSumIso.hom =
      (tensorPieceIso n).inv ≫ Sigma.ι (fun m : ℕ => tensor.piece (m : ℤ)) n
  /-- The tensor algebra has no negative-degree sections. -/
  tensorPiece_eq_zero_of_neg (n : ℤ) (hn : n < 0) (U : Cᵒᵖ)
      (x : (tensor.piece n).val.obj U) : x = 0
  /-- The exterior algebra. -/
  exterior : GradedAlgebra.{w, w} (toRingCat J Osharp)
  /-- Its degree-one generator. -/
  exteriorGenerator : F ⟶ exterior.piece 1
  /-- Its universal quotient property. -/
  exterior_isExteriorAlgebra : GradedAlgebra.IsExteriorAlgebra exterior exteriorGenerator
  /-- The exterior quotient has the same degree-zero piece as the tensor algebra. -/
  exteriorPieceIso_zero : exterior.piece 0 ≅ tensorPower J F 0
  /-- The degree-zero identification takes the exterior unit to the structure-sheaf unit. -/
  exteriorPieceIso_zero_one (U : Cᵒᵖ) :
    exteriorPieceIso_zero.hom.val.app U (exterior.one.eval U) =
      (1 : (toRingCat J Osharp).obj.obj U)
  /-- The exterior algebra has no negative-degree sections. -/
  exteriorPiece_eq_zero_of_neg (n : ℤ) (hn : n < 0) (U : Cᵒᵖ)
      (x : (exterior.piece n).val.obj U) : x = 0
  /-- The symmetric algebra. -/
  symmetric : GradedAlgebra.{w, w} (toRingCat J Osharp)
  /-- Its degree-one generator. -/
  symmetricGenerator : F ⟶ symmetric.piece 1
  /-- Its universal quotient property. -/
  symmetric_isSymmetricAlgebra : GradedAlgebra.IsSymmetricAlgebra symmetric symmetricGenerator
  /-- The symmetric algebra has no negative-degree sections. -/
  symmetricPiece_eq_zero_of_neg (n : ℤ) (hn : n < 0) (U : Cᵒᵖ)
      (x : (symmetric.piece n).val.obj U) : x = 0
  /-- The canonical quotient from the tensor algebra to the exterior algebra. -/
  tensorToExterior : GradedAlgebra.UnitalHom tensor exterior
  /-- The exterior quotient map sends the tensor generator to the exterior generator. -/
  tensorToExterior_extends : tensorGenerator ≫ tensorToExterior.app 1 = exteriorGenerator
  /-- The canonical quotient from the tensor algebra to the symmetric algebra. -/
  tensorToSymmetric : GradedAlgebra.UnitalHom tensor symmetric
  /-- The symmetric quotient map sends the tensor generator to the symmetric generator. -/
  tensorToSymmetric_extends : tensorGenerator ≫ tensorToSymmetric.app 1 = symmetricGenerator

namespace TensorExteriorSymmetricAlgebras

variable {J F}

/-! ### The three algebras and their underlying sheaves -/

section Sheaves

variable (A : TensorExteriorSymmetricAlgebras J F)

/-- The degree-`n` exterior power `⋀ⁿ F`. -/
noncomputable abbrev exteriorPower (n : ℕ) : SheafOfModules.{w} (toRingCat J Osharp) :=
  A.exterior.piece (n : ℤ)

/-- The degree-`n` symmetric power `Symⁿ F`. -/
@[sga "3 VIIA 4.3.3" "S^p(A)"]
noncomputable abbrev symmetricPower (n : ℕ) : SheafOfModules.{w} (toRingCat J Osharp) :=
  A.symmetric.piece (n : ℤ)

/-- The sheaf of modules underlying the tensor algebra `T(F)`, as the direct sum of its
homogeneous pieces. -/
noncomputable abbrev tensorAlgebraSheaf : SheafOfModules.{w} (toRingCat J Osharp) :=
  ∐ fun n : ℕ => A.tensor.piece (n : ℤ)

/-- The sheaf of modules underlying the exterior algebra `⋀(F)`. -/
noncomputable abbrev exteriorAlgebraSheaf : SheafOfModules.{w} (toRingCat J Osharp) :=
  ∐ fun n : ℕ => A.exteriorPower n

/-- The sheaf of modules underlying the symmetric algebra `Sym(F)`. -/
noncomputable abbrev symmetricAlgebraSheaf : SheafOfModules.{w} (toRingCat J Osharp) :=
  ∐ fun n : ℕ => A.symmetricPower n

/-- The sheaf of modules underlying `T(F)` is the direct sum of the tensor powers. -/
noncomputable def tensorAlgebraSheafIso :
    A.tensorAlgebraSheaf ≅ ∐ fun n : ℕ => tensorPower J F n :=
  A.tensorDirectSumIso.symm

/-- **The comparison with the sectionwise symmetric powers.** The presheaf
`U ↦ Symⁿ_{O(U)}(F(U))` maps to the degree-`n` piece of `Sym(F)` by multiplying out the
generators. Stacks 01CG asserts that this morphism becomes an isomorphism after
sheafification; `Stacks.GradedAlgebra.cmpSections_prod_ι` and
`SheafOfModules.GradedAlgebra.incl_symPowCmp_prod_ι` are the equations on products of
degree-one generators that determine it. -/
noncomputable def symPowComparison (n : ℕ) :
    PresheafOfModules.symPow n F.val ⟶ (A.symmetricPower n).val :=
  A.symmetric.symPowCmp A.symmetricGenerator A.symmetric_isSymmetricAlgebra.1 n

end Sheaves

/-! ### Elementary consequences of the three universal properties -/

section Generators

variable (A : TensorExteriorSymmetricAlgebras J F)

/-- The exterior generator has square zero. -/
theorem squareZero_exteriorGenerator :
    GradedAlgebra.SquareZero A.exteriorGenerator :=
  A.exterior_isExteriorAlgebra.1

/-- Degree-one sections of the symmetric algebra commute. -/
theorem pairwiseCommutes_symmetricGenerator :
    GradedAlgebra.PairwiseCommutes A.symmetricGenerator :=
  A.symmetric_isSymmetricAlgebra.1

/-- The exterior quotient map is the one the tensor algebra's universal property produces: it
is not extra data, but is determined by the fact that it extends the generator. -/
theorem tensorToExterior_eq :
    A.tensorToExterior =
      A.tensor_isTensorAlgebra.descAny A.exterior A.exteriorGenerator :=
  A.tensor_isTensorAlgebra.descAny_unique _ _ A.tensorToExterior_extends

/-- The symmetric quotient map is likewise determined. -/
theorem tensorToSymmetric_eq :
    A.tensorToSymmetric =
      A.tensor_isTensorAlgebra.descAny A.symmetric A.symmetricGenerator :=
  A.tensor_isTensorAlgebra.descAny_unique _ _ A.tensorToSymmetric_extends

/-- A unital homomorphism out of the tensor algebra is determined by its value on the
degree-one generator. -/
theorem tensorHom_ext {B : GradedAlgebra.{w, w} (toRingCat J Osharp)}
    {g h : GradedAlgebra.UnitalHom A.tensor B}
    (hgh : A.tensorGenerator ≫ g.app 1 = A.tensorGenerator ≫ h.app 1) : g = h :=
  A.tensor_isTensorAlgebra.hom_ext (κ := A.tensorGenerator ≫ h.app 1) trivial hgh rfl

/-- The degree-one identification of the tensor algebra, with the identity spelled at the first
tensor power rather than at `F`. The two are the same morphism — the first tensor power *is*
`F` — but only the former unifies with the identity of the codomain of `tensorPieceIso 1`. -/
theorem tensorPieceIso_one' :
    A.tensorGenerator ≫ (A.tensorPieceIso 1).hom = 𝟙 (tensorPower J F 1) :=
  A.tensorPieceIso_one

/-- The degree-one generator of the tensor algebra is the inverse of the degree-one
identification: the degree-one piece of `T(F)` *is* `F`. -/
theorem tensorGenerator_eq : A.tensorGenerator = (A.tensorPieceIso 1).inv :=
  ((Iso.eq_comp_inv _).2 A.tensorPieceIso_one').trans (Category.id_comp _)

/-- The degree-one generator of the tensor algebra is an isomorphism. -/
theorem isIso_tensorGenerator : IsIso A.tensorGenerator :=
  ⟨(A.tensorPieceIso 1).hom, A.tensorPieceIso_one, by
    rw [A.tensorGenerator_eq]; exact (A.tensorPieceIso 1).hom_inv_id⟩

end Generators

/-! ### Degree zero -/

section DegreeZero

variable (A : TensorExteriorSymmetricAlgebras J F)

/-- The degree-zero identification of the tensor algebra, with the zeroth tensor power spelled
as the structure sheaf. -/
noncomputable def tensorPieceZeroIsoUnit :
    A.tensor.piece 0 ≅ SheafOfModules.unit (toRingCat J Osharp) :=
  A.tensorPieceIso 0

/-- The degree-zero identification of the exterior algebra, with the zeroth tensor power
spelled as the structure sheaf. -/
noncomputable def exteriorPieceZeroIsoUnit :
    A.exterior.piece 0 ≅ SheafOfModules.unit (toRingCat J Osharp) :=
  A.exteriorPieceIso_zero

/-- The degree-zero identification of the tensor algebra takes the unit to `1`. -/
theorem tensorPieceZeroIsoUnit_one (U : Cᵒᵖ) :
    A.tensorPieceZeroIsoUnit.hom.val.app U (A.tensor.one.eval U) =
      (1 : (toRingCat J Osharp).obj.obj U) :=
  A.tensorPieceIso_zero U

/-- The degree-zero identification of the exterior algebra takes the unit to `1`. -/
theorem exteriorPieceZeroIsoUnit_one (U : Cᵒᵖ) :
    A.exteriorPieceZeroIsoUnit.hom.val.app U (A.exterior.one.eval U) =
      (1 : (toRingCat J Osharp).obj.obj U) :=
  A.exteriorPieceIso_zero_one U

/-- A degree-zero section of the tensor algebra is its corresponding scalar times the unit. -/
theorem tensorPieceZeroIsoUnit_smul_one (U : Cᵒᵖ) (x : (A.tensor.piece 0).val.obj U)
    (r : (toRingCat J Osharp).obj.obj U)
    (hr : A.tensorPieceZeroIsoUnit.hom.val.app U x = r) :
    r • A.tensor.one.eval U = x :=
  GradedAlgebra.eq_smul_one_of_isoUnit A.tensor A.tensorPieceZeroIsoUnit
    A.tensorPieceZeroIsoUnit_one U x r hr

/-- Degree zero of the tensor algebra is generated by the unit. -/
theorem exists_tensor_eq_smul_one (U : Cᵒᵖ) (x : (A.tensor.piece 0).val.obj U) :
    ∃ r : (toRingCat J Osharp).obj.obj U, r • A.tensor.one.eval U = x :=
  GradedAlgebra.exists_smul_one_of_isoUnit A.tensor A.tensorPieceZeroIsoUnit
    A.tensorPieceZeroIsoUnit_one U x

/-- A degree-zero exterior section is its corresponding scalar times the unit. -/
theorem exteriorPieceZeroIsoUnit_smul_one (U : Cᵒᵖ) (x : (A.exterior.piece 0).val.obj U)
    (r : (toRingCat J Osharp).obj.obj U)
    (hr : A.exteriorPieceZeroIsoUnit.hom.val.app U x = r) :
    r • A.exterior.one.eval U = x :=
  GradedAlgebra.eq_smul_one_of_isoUnit A.exterior A.exteriorPieceZeroIsoUnit
    A.exteriorPieceZeroIsoUnit_one U x r hr

/-- Degree zero of the exterior algebra is generated by the unit. -/
theorem exists_exterior_eq_smul_one (U : Cᵒᵖ) (x : (A.exterior.piece 0).val.obj U) :
    ∃ r : (toRingCat J Osharp).obj.obj U, r • A.exterior.one.eval U = x :=
  GradedAlgebra.exists_smul_one_of_isoUnit A.exterior A.exteriorPieceZeroIsoUnit
    A.exteriorPieceZeroIsoUnit_one U x

end DegreeZero

/-! ### Negative degrees -/

section Negative

variable (A : TensorExteriorSymmetricAlgebras J F)

/-- In a negative degree the tensor algebra has a single section over every object. -/
theorem subsingleton_tensorPiece {n : ℤ} (hn : n < 0) (U : Cᵒᵖ) :
    Subsingleton ((A.tensor.piece n).val.obj U) :=
  subsingleton_of_forall_eq 0 (A.tensorPiece_eq_zero_of_neg n hn U)

/-- In a negative degree the exterior algebra has a single section over every object. -/
theorem subsingleton_exteriorPiece {n : ℤ} (hn : n < 0) (U : Cᵒᵖ) :
    Subsingleton ((A.exterior.piece n).val.obj U) :=
  subsingleton_of_forall_eq 0 (A.exteriorPiece_eq_zero_of_neg n hn U)

/-- In a negative degree the symmetric algebra has a single section over every object. -/
theorem subsingleton_symmetricPiece {n : ℤ} (hn : n < 0) (U : Cᵒᵖ) :
    Subsingleton ((A.symmetric.piece n).val.obj U) :=
  subsingleton_of_forall_eq 0 (A.symmetricPiece_eq_zero_of_neg n hn U)

/-- Any two morphisms into a negative-degree piece of the tensor algebra agree. -/
theorem hom_ext_tensorPiece_of_neg {n : ℤ} (hn : n < 0)
    {M : SheafOfModules.{w} (toRingCat J Osharp)} (f g : M ⟶ A.tensor.piece n) : f = g :=
  (SheafOfModules.forget _).map_injective
    (PresheafOfModules.hom_ext fun U => ModuleCat.hom_ext (LinearMap.ext fun _x =>
      (A.subsingleton_tensorPiece hn U).elim _ _))

end Negative

/-! ### The direct-sum presentation -/

section DirectSum

variable (A : TensorExteriorSymmetricAlgebras J F)

/-- The inverse direct-sum comparison, read on the summands. -/
theorem ι_tensorDirectSumIso_inv (n : ℕ) :
    Sigma.ι (fun m : ℕ => A.tensor.piece (m : ℤ)) n ≫ A.tensorDirectSumIso.inv =
      (A.tensorPieceIso n).hom ≫ Sigma.ι (fun m : ℕ => tensorPower J F m) n := by
  rw [Iso.comp_inv_eq, Category.assoc, A.tensorDirectSumIso_ι n, Iso.hom_inv_id_assoc]

/-- The direct-sum comparison is the only isomorphism induced by the homogeneous
identifications: the field `tensorDirectSumIso` is determined by `tensorDirectSumIso_ι`. -/
theorem tensorDirectSumIso_unique
    (e : (∐ fun n : ℕ => tensorPower J F n) ≅ (∐ fun n : ℕ => A.tensor.piece (n : ℤ)))
    (he : ∀ n : ℕ, Sigma.ι (fun m : ℕ => tensorPower J F m) n ≫ e.hom =
      (A.tensorPieceIso n).inv ≫ Sigma.ι (fun m : ℕ => A.tensor.piece (m : ℤ)) n) :
    e = A.tensorDirectSumIso :=
  Iso.ext (colimit.hom_ext fun n => by
    simpa only [colimit.ι_desc] using (he n.as).trans (A.tensorDirectSumIso_ι n.as).symm)

end DirectSum

/-! ### Independence of the choices -/

section Uniqueness

variable (A B : TensorExteriorSymmetricAlgebras J F)

/-- The canonical comparison between the tensor algebras of two such bundles. -/
noncomputable def tensorAlgebraIso (n : ℤ) : A.tensor.piece n ≅ B.tensor.piece n :=
  A.tensor_isTensorAlgebra.pieceIso B.tensor_isTensorAlgebra n

/-- The canonical comparison between the exterior algebras of two such bundles: the exterior
powers of `F` are well defined up to canonical isomorphism. -/
noncomputable def exteriorAlgebraIso (n : ℤ) : A.exterior.piece n ≅ B.exterior.piece n :=
  A.exterior_isExteriorAlgebra.isUniversal.pieceIso
    B.exterior_isExteriorAlgebra.isUniversal n

/-- The comparison of exterior algebras is the one `IsExteriorAlgebra.pieceIso` produces. -/
theorem exteriorAlgebraIso_eq (n : ℤ) :
    exteriorAlgebraIso A B n =
      A.exterior_isExteriorAlgebra.pieceIso B.exterior_isExteriorAlgebra n := rfl

/-- The canonical comparison between the symmetric algebras of two such bundles: the symmetric
powers of `F` are well defined up to canonical isomorphism. -/
noncomputable def symmetricAlgebraIso (n : ℤ) : A.symmetric.piece n ≅ B.symmetric.piece n :=
  A.symmetric_isSymmetricAlgebra.pieceIso B.symmetric_isSymmetricAlgebra n

/-- The comparison of tensor algebras carries one generator to the other. -/
theorem tensorAlgebraIso_generator :
    A.tensorGenerator ≫ (tensorAlgebraIso A B 1).hom = B.tensorGenerator :=
  GradedAlgebra.IsUniversal.pieceIso_generator _ _

/-- The comparison of exterior algebras carries one generator to the other. -/
theorem exteriorAlgebraIso_generator :
    A.exteriorGenerator ≫ (exteriorAlgebraIso A B 1).hom = B.exteriorGenerator :=
  GradedAlgebra.IsUniversal.pieceIso_generator _ _

/-- The comparison of symmetric algebras carries one generator to the other. -/
theorem symmetricAlgebraIso_generator :
    A.symmetricGenerator ≫ (symmetricAlgebraIso A B 1).hom = B.symmetricGenerator :=
  GradedAlgebra.IsUniversal.pieceIso_generator _ _

/-- The comparison of tensor algebras is multiplicative on homogeneous local sections. -/
theorem tensorAlgebraIso_mul (i j : ℤ) (U : Cᵒᵖ) (x : (A.tensor.piece i).val.obj U)
    (y : (A.tensor.piece j).val.obj U) :
    (tensorAlgebraIso A B (i + j)).hom.val.app U ((A.tensor.mul i j).app U x y) =
      (B.tensor.mul i j).app U ((tensorAlgebraIso A B i).hom.val.app U x)
        ((tensorAlgebraIso A B j).hom.val.app U y) :=
  GradedAlgebra.IsUniversal.pieceIso_mul _ _ i j U x y

/-- The comparison of exterior algebras is multiplicative on homogeneous local sections. -/
theorem exteriorAlgebraIso_mul (i j : ℤ) (U : Cᵒᵖ) (x : (A.exterior.piece i).val.obj U)
    (y : (A.exterior.piece j).val.obj U) :
    (exteriorAlgebraIso A B (i + j)).hom.val.app U ((A.exterior.mul i j).app U x y) =
      (B.exterior.mul i j).app U ((exteriorAlgebraIso A B i).hom.val.app U x)
        ((exteriorAlgebraIso A B j).hom.val.app U y) :=
  GradedAlgebra.IsUniversal.pieceIso_mul _ _ i j U x y

/-- The comparison of symmetric algebras is multiplicative on homogeneous local sections. -/
theorem symmetricAlgebraIso_mul (i j : ℤ) (U : Cᵒᵖ) (x : (A.symmetric.piece i).val.obj U)
    (y : (A.symmetric.piece j).val.obj U) :
    (symmetricAlgebraIso A B (i + j)).hom.val.app U ((A.symmetric.mul i j).app U x y) =
      (B.symmetric.mul i j).app U ((symmetricAlgebraIso A B i).hom.val.app U x)
        ((symmetricAlgebraIso A B j).hom.val.app U y) :=
  GradedAlgebra.IsUniversal.pieceIso_mul _ _ i j U x y

end Uniqueness

end TensorExteriorSymmetricAlgebras

/-! ### The ringed-space case -/

section RingedSpace

open AlgebraicGeometry TopologicalSpace RingedSpaceModuleAdjunction

/-- For a ringed space the sheaf of rings over which Section 17.21 works is
`CategoryTheory.Sheaf.toRingCat` of the structure sheaf on the nose, so `tensorPower` and
`TensorExteriorSymmetricAlgebras` apply verbatim to a sheaf of modules on a ringed space, at
the site of its open subsets. This is the verified repoint for the ringed-space statements. -/
theorem ringSheaf_eq (X : RingedSpace.{w, w}) :
    structureSheafRing X = toRingCat (Opens.grothendieckTopology X.carrier) X.sheaf := rfl

end RingedSpace

end SheafOfModules
