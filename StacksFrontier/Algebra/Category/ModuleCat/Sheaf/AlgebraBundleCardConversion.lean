module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafificationTensor

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.AlgebraBundleStalk
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedAlgebraBridge
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The generator-packaged form of the tensor/exterior/symmetric algebra bundle

`SheafOfModules.TensorExteriorSymmetricAlgebras J F` records the tensor algebra of a sheaf
of modules `F`, its exterior and symmetric quotients, their three universal properties, the
identification of the homogeneous pieces of `T(F)` with the tensor powers of `F`, and the
two quotient maps. It states a degree-one generator as a bare morphism `F ⟶ A.piece 1`, and
it states the tensor algebra's universal property through the generic
`SheafOfModules.GradedAlgebra.IsUniversal` with the trivial side condition.

There is a second, equally natural packaging of exactly the same data, in which a degree-one
generator is a one-field record `GradedAlgebra.Generator F A`, the universal properties
quantify over such records, and "the quotient map carries one generator to the other" is a
named predicate `UnitalHom.Extends` rather than a composition written out. This file
introduces that packaging as `TensorExteriorSymmetricAlgebras.GeneratorForm` and proves the
two forms carry the same information, field for field, by exhibiting an explicit
`Equiv` whose round trips are `rfl`.

## Main definitions

* `SheafOfModules.GradedAlgebra.Generator`: a degree-one generator of a sheaf of graded
  algebras, as a one-field record wrapping a morphism `M ⟶ A.piece 1`.
* `SheafOfModules.GradedAlgebra.generatorEquiv`: that record is the morphism.
* `SheafOfModules.GradedAlgebra.UnitalHom.Extends`: a unital homomorphism carries a given
  degree-one generator of its source to a given degree-one generator of its target.
* `SheafOfModules.GradedAlgebra.Generator.SquareZero`, `Generator.PairwiseCommutes`,
  `Generator.IsTensorAlgebra`, `Generator.IsExteriorAlgebra`,
  `Generator.IsSymmetricAlgebra`: the generator-packaged forms of the four predicates.
* `SheafOfModules.TensorExteriorSymmetricAlgebras.GeneratorForm`: the generator-packaged
  bundle, with the same twenty-four fields under the same names.
* `SheafOfModules.TensorExteriorSymmetricAlgebras.toGeneratorForm` and
  `ofGeneratorForm`, assembled into
  `SheafOfModules.TensorExteriorSymmetricAlgebras.generatorFormEquiv`.
* `SheafOfModules.ringedSpaceAlgebrasGeneratorForm`: the inhabitant of the
  generator-packaged bundle for a sheaf of modules on a ringed space.

## Main results

* `SheafOfModules.GradedAlgebra.Generator.isTensorAlgebra_iff`,
  `isExteriorAlgebra_iff`, `isSymmetricAlgebra_iff`: each generator-packaged universal
  property holds exactly when the bare-morphism one does. The tensor case is the only one
  that is not a reshuffling of conjuncts: the generator-packaged form is the bare
  `∃!` statement with no side condition, and the bare-morphism form is
  `IsUniversal (fun _ _ => True)`, so the trivial conjunct has to be supplied and discarded.
* `SheafOfModules.TensorExteriorSymmetricAlgebras.generatorFormEquiv`: the two packagings
  are in bijection, with both round trips `rfl`. This is the field-for-field statement that
  neither packaging asks for anything the other does not provide, and that neither is the
  weaker of the two.
* `SheafOfModules.TensorExteriorSymmetricAlgebras.tensorPieceIso_mul_left_of_eq`: the one
  field of the bundle whose transport along an equality of tensor-power families is not
  mechanical, proved by abstracting the tensor power to a variable.
* `SheafOfModules.nonempty_ringedSpaceAlgebrasGeneratorForm`: the generator-packaged bundle
  over a sheaf of modules on a ringed space is inhabited.

## Implementation notes

What is forced and what is chosen:

* The universes are those of `SheafOfModules.TensorExteriorSymmetricAlgebras`: a site
  `C : Type u` with morphisms in `Type v`, and a single universe `w` carrying the sections
  of the structure sheaf and of every module. The collapse of the ring and module universes
  to one `w` is forced upstream, by `SheafOfModules.unit` (used for the zeroth tensor power)
  and by the monoidal structure on presheaves of modules, not chosen here; `u` and `v` stay
  independent of `w`.
* `GradedAlgebra.Generator` is deliberately a structure rather than an abbreviation for the
  morphism type, because that is the shape the consumers of the bundle are written against;
  `generatorEquiv` is what makes it harmless. Its single field is named `map`.
* The round trips of `generatorFormEquiv` are `rfl` only because `Generator` is a
  single-field structure (so structure eta applies) and because the differing universal
  property fields are propositions (so proof irrelevance applies). Nothing about the data
  fields is reassociated.
* `Generator.SquareZero` and `Generator.PairwiseCommutes` are *defined* as the bare-morphism
  predicates applied to the underlying morphism, rather than restated, because they are
  already stated sectionwise in exactly the shape the generator-packaged consumers use. Only
  the three `Is*Algebra` predicates genuinely change shape.

## References

* [Stacks Project, Section 17.21](https://stacks.math.columbia.edu/tag/01CF)
* [Stacks Project, Tag 0FQW](https://stacks.math.columbia.edu/tag/0FQW)
-/

@[expose] public section

universe t a v u w

attribute [local implicit_reducible] Stacks.SheafOfModules.Tensor.ringSheaf

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf

open scoped TensorProduct

namespace SheafOfModules

/-! ## Degree-one generators as a one-field record -/

namespace GradedAlgebra

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t}}

/-- A degree-one generator of a sheaf of graded algebras `A`: a morphism from `M` into the
degree-one piece of `A`, packaged as a one-field record. -/
@[ext]
structure Generator (M : SheafOfModules.{a} R) (A : GradedAlgebra.{t, a} R) where
  /-- The inclusion of `M` in degree one. -/
  map : M ⟶ A.piece 1

variable {M : SheafOfModules.{a} R}

/-- A degree-one generator is exactly a morphism into the degree-one piece. -/
def generatorEquiv (A : GradedAlgebra.{t, a} R) :
    Generator M A ≃ (M ⟶ A.piece 1) where
  toFun ι := ι.map
  invFun f := ⟨f⟩
  left_inv _ := rfl
  right_inv _ := rfl

variable {A B : GradedAlgebra.{t, a} R}

/-- A unital homomorphism carries a given degree-one generator of its source to a given
degree-one generator of its target. -/
def UnitalHom.Extends (g : UnitalHom A B) (ι : Generator M A) (f : Generator M B) : Prop :=
  ι.map ≫ g.app 1 = f.map

/-- Every local degree-one section coming from the generator has square zero. -/
def Generator.SquareZero (ι : Generator M A) : Prop :=
  _root_.SheafOfModules.GradedAlgebra.SquareZero ι.map

/-- Local degree-one sections coming from the generator commute pairwise. -/
def Generator.PairwiseCommutes (ι : Generator M A) : Prop :=
  _root_.SheafOfModules.GradedAlgebra.PairwiseCommutes ι.map

/-- The universal property of the tensor algebra, over generator records. Note that there is
no side condition: every degree-one generator of every target is extended. -/
def Generator.IsTensorAlgebra (ι : Generator M A) : Prop :=
  ∀ (B : GradedAlgebra.{t, a} R) (f : Generator M B), ∃! g : UnitalHom A B, g.Extends ι f

/-- The universal property of the quotient of the tensor algebra by the two-sided ideal
generated by the squares of local degree-one sections, over generator records. -/
def Generator.IsExteriorAlgebra (ι : Generator M A) : Prop :=
  ι.SquareZero ∧
    ∀ (B : GradedAlgebra.{t, a} R) (f : Generator M B),
      f.SquareZero → ∃! g : UnitalHom A B, g.Extends ι f

/-- The universal property of the quotient of the tensor algebra by the two-sided ideal
generated by the commutators of local degree-one sections, over generator records. -/
@[sga "6 VI 2.2"]
def Generator.IsSymmetricAlgebra (ι : Generator M A) : Prop :=
  ι.PairwiseCommutes ∧
    ∀ (B : GradedAlgebra.{t, a} R) (f : Generator M B),
      f.PairwiseCommutes → ∃! g : UnitalHom A B, g.Extends ι f

/-- The generator-packaged tensor algebra property holds exactly when the bare-morphism one
does. This is the one of the three that is not a reshuffling of conjuncts: the
generator-packaged form carries no side condition, while
`SheafOfModules.GradedAlgebra.IsTensorAlgebra` is `IsUniversal (fun _ _ => True)`. -/
theorem Generator.isTensorAlgebra_iff (ι : Generator M A) :
    ι.IsTensorAlgebra ↔ _root_.SheafOfModules.GradedAlgebra.IsTensorAlgebra A ι.map :=
  ⟨fun h => (_root_.SheafOfModules.GradedAlgebra.isTensorAlgebra_iff ι.map).2 fun B κ => h B ⟨κ⟩,
    fun h B f => (_root_.SheafOfModules.GradedAlgebra.isTensorAlgebra_iff ι.map).1 h B f.map⟩

/-- The generator-packaged exterior algebra property holds exactly when the bare-morphism one
does. -/
theorem Generator.isExteriorAlgebra_iff (ι : Generator M A) :
    ι.IsExteriorAlgebra ↔ _root_.SheafOfModules.GradedAlgebra.IsExteriorAlgebra A ι.map :=
  ⟨fun h => ⟨h.1, fun B κ => h.2 B ⟨κ⟩⟩,
    fun h => ⟨h.1, fun B f => h.2 B f.map⟩⟩

/-- The generator-packaged symmetric algebra property holds exactly when the bare-morphism
one does. -/
theorem Generator.isSymmetricAlgebra_iff (ι : Generator M A) :
    ι.IsSymmetricAlgebra ↔ _root_.SheafOfModules.GradedAlgebra.IsSymmetricAlgebra A ι.map :=
  ⟨fun h => ⟨h.1, fun B κ => h.2 B ⟨κ⟩⟩,
    fun h => ⟨h.1, fun B f => h.2 B f.map⟩⟩

end GradedAlgebra

/-! ## The generator-packaged bundle -/

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  {Osharp : Sheaf J CommRingCat.{w}}
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]
  (F : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Osharp))

/-- The generator-packaged form of `SheafOfModules.TensorExteriorSymmetricAlgebras`: the same
twenty-four fields under the same names, with the three degree-one generators packaged as
`SheafOfModules.GradedAlgebra.Generator` records, the three universal properties taken in
their generator-packaged form, and the two "the quotient map carries the generator across"
fields stated through `SheafOfModules.GradedAlgebra.UnitalHom.Extends`. -/
structure TensorExteriorSymmetricAlgebras.GeneratorForm where
  /-- The tensor algebra. -/
  tensor : GradedAlgebra.{w, w} (Stacks.SheafOfModules.Tensor.ringSheaf Osharp)
  /-- Its canonical degree-one generator. -/
  tensorGenerator : GradedAlgebra.Generator F tensor
  /-- The tensor algebra universal property. -/
  tensor_isTensorAlgebra : tensorGenerator.IsTensorAlgebra
  /-- Identification of its degree `n` piece with the `n`-fold tensor power. -/
  tensorPieceIso (n : ℕ) : tensor.piece (n : ℤ) ≅ tensorPower J F n
  /-- Under the degree-one identification, the generator is the identity. -/
  tensorPieceIso_one : tensorGenerator.map ≫ (tensorPieceIso 1).hom = 𝟙 F
  /-- The degree-zero identification takes the algebra unit to the structure-sheaf unit. -/
  tensorPieceIso_zero (U : Cᵒᵖ) :
    (tensorPieceIso 0).hom.val.app U (tensor.one.eval U) =
      (1 : (Stacks.SheafOfModules.Tensor.ringSheaf Osharp).obj.obj U)
  /-- Multiplication by a degree-one generator is tensor concatenation under the canonical
  homogeneous identifications. -/
  tensorPieceIso_mul_left (n : ℕ) (U : Cᵒᵖ) (s : F.val.obj U)
      (x : (tensorPower J F (n + 1)).val.obj U) :
    (tensorPieceIso (n + 2)).hom.val.app U
        (Eq.mp (congrArg (fun k : ℤ => ((tensor.piece k).val.obj U : Type w))
            (show 1 + ((n + 1 : ℕ) : ℤ) = ((n + 2 : ℕ) : ℤ) by omega))
          ((tensor.mul 1 ((n + 1 : ℕ) : ℤ)).app U (tensorGenerator.map.val.app U s)
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
  exterior : GradedAlgebra.{w, w} (Stacks.SheafOfModules.Tensor.ringSheaf Osharp)
  /-- Its degree-one generator. -/
  exteriorGenerator : GradedAlgebra.Generator F exterior
  /-- Its universal quotient property. -/
  exterior_isExteriorAlgebra : exteriorGenerator.IsExteriorAlgebra
  /-- The exterior quotient has the same degree-zero piece as the tensor algebra. -/
  exteriorPieceIso_zero : exterior.piece 0 ≅ tensorPower J F 0
  /-- The degree-zero identification takes the exterior unit to the structure-sheaf unit. -/
  exteriorPieceIso_zero_one (U : Cᵒᵖ) :
    exteriorPieceIso_zero.hom.val.app U (exterior.one.eval U) =
      (1 : (Stacks.SheafOfModules.Tensor.ringSheaf Osharp).obj.obj U)
  /-- The exterior algebra has no negative-degree sections. -/
  exteriorPiece_eq_zero_of_neg (n : ℤ) (hn : n < 0) (U : Cᵒᵖ)
      (x : (exterior.piece n).val.obj U) : x = 0
  /-- The symmetric algebra. -/
  symmetric : GradedAlgebra.{w, w} (Stacks.SheafOfModules.Tensor.ringSheaf Osharp)
  /-- Its degree-one generator. -/
  symmetricGenerator : GradedAlgebra.Generator F symmetric
  /-- Its universal quotient property. -/
  symmetric_isSymmetricAlgebra : symmetricGenerator.IsSymmetricAlgebra
  /-- The symmetric algebra has no negative-degree sections. -/
  symmetricPiece_eq_zero_of_neg (n : ℤ) (hn : n < 0) (U : Cᵒᵖ)
      (x : (symmetric.piece n).val.obj U) : x = 0
  /-- The canonical quotient from the tensor algebra to the exterior algebra. -/
  tensorToExterior : GradedAlgebra.UnitalHom tensor exterior
  /-- The exterior quotient map sends the tensor generator to the exterior generator. -/
  tensorToExterior_extends : tensorToExterior.Extends tensorGenerator exteriorGenerator
  /-- The canonical quotient from the tensor algebra to the symmetric algebra. -/
  tensorToSymmetric : GradedAlgebra.UnitalHom tensor symmetric
  /-- The symmetric quotient map sends the tensor generator to the symmetric generator. -/
  tensorToSymmetric_extends : tensorToSymmetric.Extends tensorGenerator symmetricGenerator

namespace TensorExteriorSymmetricAlgebras

variable {J F}

/-- The generator-packaged form of a bundle: field for field, the only changes are that the
three generators are wrapped, the three universal properties are transported along
`SheafOfModules.GradedAlgebra.Generator.is*Algebra_iff`, and the two `*_extends` fields are
read as `UnitalHom.Extends`, which is definitionally the composition they already are. -/
def toGeneratorForm (A : TensorExteriorSymmetricAlgebras J F) : GeneratorForm J F where
  tensor := A.tensor
  tensorGenerator := ⟨A.tensorGenerator⟩
  tensor_isTensorAlgebra :=
    (GradedAlgebra.Generator.isTensorAlgebra_iff _).2 A.tensor_isTensorAlgebra
  tensorPieceIso := A.tensorPieceIso
  tensorPieceIso_one := A.tensorPieceIso_one
  tensorPieceIso_zero := A.tensorPieceIso_zero
  tensorPieceIso_mul_left := A.tensorPieceIso_mul_left
  tensorDirectSumIso := A.tensorDirectSumIso
  tensorDirectSumIso_ι := A.tensorDirectSumIso_ι
  tensorPiece_eq_zero_of_neg := A.tensorPiece_eq_zero_of_neg
  exterior := A.exterior
  exteriorGenerator := ⟨A.exteriorGenerator⟩
  exterior_isExteriorAlgebra :=
    (GradedAlgebra.Generator.isExteriorAlgebra_iff _).2 A.exterior_isExteriorAlgebra
  exteriorPieceIso_zero := A.exteriorPieceIso_zero
  exteriorPieceIso_zero_one := A.exteriorPieceIso_zero_one
  exteriorPiece_eq_zero_of_neg := A.exteriorPiece_eq_zero_of_neg
  symmetric := A.symmetric
  symmetricGenerator := ⟨A.symmetricGenerator⟩
  symmetric_isSymmetricAlgebra :=
    (GradedAlgebra.Generator.isSymmetricAlgebra_iff _).2 A.symmetric_isSymmetricAlgebra
  symmetricPiece_eq_zero_of_neg := A.symmetricPiece_eq_zero_of_neg
  tensorToExterior := A.tensorToExterior
  tensorToExterior_extends := A.tensorToExterior_extends
  tensorToSymmetric := A.tensorToSymmetric
  tensorToSymmetric_extends := A.tensorToSymmetric_extends

/-- The inverse of `toGeneratorForm`: a generator-packaged bundle gives back a bundle. -/
def ofGeneratorForm (A : GeneratorForm J F) : TensorExteriorSymmetricAlgebras J F where
  tensor := A.tensor
  tensorGenerator := A.tensorGenerator.map
  tensor_isTensorAlgebra :=
    (GradedAlgebra.Generator.isTensorAlgebra_iff _).1 A.tensor_isTensorAlgebra
  tensorPieceIso := A.tensorPieceIso
  tensorPieceIso_one := A.tensorPieceIso_one
  tensorPieceIso_zero := A.tensorPieceIso_zero
  tensorPieceIso_mul_left := A.tensorPieceIso_mul_left
  tensorDirectSumIso := A.tensorDirectSumIso
  tensorDirectSumIso_ι := A.tensorDirectSumIso_ι
  tensorPiece_eq_zero_of_neg := A.tensorPiece_eq_zero_of_neg
  exterior := A.exterior
  exteriorGenerator := A.exteriorGenerator.map
  exterior_isExteriorAlgebra :=
    (GradedAlgebra.Generator.isExteriorAlgebra_iff _).1 A.exterior_isExteriorAlgebra
  exteriorPieceIso_zero := A.exteriorPieceIso_zero
  exteriorPieceIso_zero_one := A.exteriorPieceIso_zero_one
  exteriorPiece_eq_zero_of_neg := A.exteriorPiece_eq_zero_of_neg
  symmetric := A.symmetric
  symmetricGenerator := A.symmetricGenerator.map
  symmetric_isSymmetricAlgebra :=
    (GradedAlgebra.Generator.isSymmetricAlgebra_iff _).1 A.symmetric_isSymmetricAlgebra
  symmetricPiece_eq_zero_of_neg := A.symmetricPiece_eq_zero_of_neg
  tensorToExterior := A.tensorToExterior
  tensorToExterior_extends := A.tensorToExterior_extends
  tensorToSymmetric := A.tensorToSymmetric
  tensorToSymmetric_extends := A.tensorToSymmetric_extends

/-- The field `tensorPieceIso_mul_left` with the degree-`n+1` tensor power abstracted to a
variable `Y` that is merely *equal* to it.

This is the lemma a consumer needs when it carries its own copy of the tensor-power recursion.
Two definitions of the same recursion are equal but not definitionally equal at a variable
degree, so every field of the bundle mentioning a tensor power then needs a transport along
that equality; all of them except this one are either an `Iso` that `eqToIso` moves directly or
an identity that holds elementwise, and this one hides the tensor power inside the
`Eq.mp (congrArg ...)` degree coercion as well as in the type of `x`, which puts it out of
reach of `rw`, `simp` and `kabstract` (they report the target as not type-correct under
`implicit` transparency). Abstracting the tensor power to a variable is what makes it
reachable: `subst` then turns every `eqToHom` into an identity and the statement becomes the
field itself. -/
theorem tensorPieceIso_mul_left_of_eq (A : TensorExteriorSymmetricAlgebras J F) (n : ℕ)
    (Y : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Osharp))
    (hY : Y = tensorPower J F (n + 1))
    (U : Cᵒᵖ) (s : F.val.obj U) (x : Y.val.obj U) :
    ((A.tensorPieceIso (n + 2) ≪≫
        (eqToIso (congrArg
            (fun G : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Osharp) =>
          ((Stacks.SheafOfModules.Tensor.sheafTensor Osharp).obj F).obj G)
            hY)).symm).hom.val.app U)
      (Eq.mp (congrArg (fun k : ℤ => ((A.tensor.piece k).val.obj U : Type w))
          (show 1 + ((n + 1 : ℕ) : ℤ) = ((n + 2 : ℕ) : ℤ) by omega))
        ((A.tensor.mul 1 ((n + 1 : ℕ) : ℤ)).app U (A.tensorGenerator.val.app U s)
          ((A.tensorPieceIso (n + 1) ≪≫ (eqToIso hY).symm).inv.val.app U x))) =
      ((PresheafOfModules.sheafificationAdjunction (R := Stacks.SheafOfModules.Tensor.ringSheaf
          Osharp)
        (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf Osharp).obj)).unit.app
      (PresheafOfModules.tensorObj F.val Y.val)).app U
        (s ⊗ₜ[Osharp.obj.obj U] x) := by
  subst hY
  exact A.tensorPieceIso_mul_left n U s x

/-- **The two packagings carry the same data, field for field.** Both round trips are `rfl`:
no field of either form has to be rebuilt, reassociated or weakened to produce the other. -/
def generatorFormEquiv :
    TensorExteriorSymmetricAlgebras J F ≃ GeneratorForm J F where
  toFun := toGeneratorForm
  invFun := ofGeneratorForm
  left_inv _ := rfl
  right_inv _ := rfl

end TensorExteriorSymmetricAlgebras

/-! ## The inhabitant over a ringed space -/

section RingedSpace

open AlgebraicGeometry TopologicalSpace RingedSpaceModuleAdjunction

variable (X : RingedSpace.{w, w})

/-- The generator-packaged bundle of a sheaf of modules on a ringed space. -/
noncomputable def ringedSpaceAlgebrasGeneratorForm (F : SheafOfModules.{w} (structureSheafRing X)) :
    TensorExteriorSymmetricAlgebras.GeneratorForm
      (Opens.grothendieckTopology X.carrier) F :=
  (ringedSpaceAlgebras X F).toGeneratorForm

/-- The generator-packaged bundle of a sheaf of modules on a ringed space is inhabited. -/
theorem nonempty_ringedSpaceAlgebrasGeneratorForm (F : SheafOfModules.{w} (structureSheafRing X)) :
    Nonempty (TensorExteriorSymmetricAlgebras.GeneratorForm
      (Opens.grothendieckTopology X.carrier) F) :=
  ⟨ringedSpaceAlgebrasGeneratorForm X F⟩

end RingedSpace

end SheafOfModules
