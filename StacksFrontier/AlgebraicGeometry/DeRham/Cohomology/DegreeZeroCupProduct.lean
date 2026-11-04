module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.Algebras
public import StacksFrontier.Topology.Sheaves.Cohomology.Locality.CohomologyVanishesLocally

/-!
# Cupping a cohomology class with a degree-zero class

Let `X` be a topological space, let `𝒪_X` be a sheaf of rings on it and let
`μ : 𝒜 × ℬ ⟶ 𝒞` be a pairing of sheaves of `𝒪_X`-modules, given on sections as a
`Stacks.BilinearMap`. A *degree-zero class* in `H^0(X, ℬ)` is a global section `u` of `ℬ`, and
cupping with it is the map

`H^q(X, 𝒜) ⟶ H^q(X, 𝒞)`

induced by the morphism of sheaves `a ↦ μ(a, u)`. This file constructs that morphism and the
induced map on cohomology, and proves the properties that make it a cup product with a
degree-zero class rather than an arbitrary map: it is functorial in both coefficient sheaves,
and in degree `q = 0` it is the pairing itself on global sections.

This is the shape in which the cup product of [Stacks, Tag 0FKU] enters the projection formula
of [Stacks, Tag 0G88]: there the second factor is the degree-zero Gysin class `γ^0(1)`, which is
a global section of `ℋ^c_Z(Ω^c_{X/S})`, so only cupping with a degree-zero class is needed, and
for a degree-zero class the cup product *is* functoriality along the multiplication map. That
last sentence is `cupDegreeZero` together with `cupDegreeZero_zero_toRightDerivedZero`: the
definition is the functoriality, and the degree-zero normalization identifies it with the
pairing, so nothing is left implicit about which map is meant.

## Main definitions

* `Stacks.Cohomology.rightMulHom`: the morphism of sheaves `𝒜 ⟶ 𝒞`, `a ↦ μ(a, u)`, attached to
  a pairing `μ` and a global section `u` of its second argument. This is the mirror of
  `SheafOfModules.GradedAlgebra.rightMul`, read for an arbitrary pairing rather than for the
  multiplication of a sheaf of graded algebras.
* `Stacks.Cohomology.cupDegreeZero`: **cupping with a degree-zero class**, the map
  `H^q(X, 𝒜) ⟶ H^q(X, 𝒞)` it induces on cohomology.

## Main results

* `Stacks.Cohomology.comp_rightMulHom` and `rightMulHom_compRight`: it is functorial in the first
  and in the second coefficient sheaf, which become `cupDegreeZero_naturality_left` and
  `cupDegreeZero_compRight` on cohomology.
* `Stacks.Cohomology.cupDegreeZero_zero_toRightDerivedZero`: **the degree-zero normalization.**
  On the degree-zero class of a global section `a` of `𝒜`, cupping with `u` is the degree-zero
  class of `μ(a, u)`. In particular the construction extends the pairing on global sections,
  which is what identifies it with the cup product rather than with some other natural map.

## Implementation notes

**Why a `Stacks.BilinearMap` and not a morphism out of a tensor product.** The pairing is taken
in the sectionwise form `Stacks.BilinearMap`, whose three module universes are independent and
which needs no sheafification hypotheses; see the implementation notes of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/Algebras.lean`. A morphism
`𝒜 ⊗_{𝒪_X} ℬ ⟶ 𝒞` gives such a pairing, by `Stacks.tensorHomEquiv` at the objectwise tensor
product, so nothing is lost; what is gained is that the two consumers of this file — the
multiplication of the sheaf of graded algebras `Ω^•_{X/S}` and the wedge pairing with a local
cohomology sheaf — are already given sectionwise.

**Only a degree-zero second argument.** No pairing `H^q × H^{q'} ⟶ H^{q+q'}` is constructed
here, and none is needed for [Stacks, Tag 0G88], whose right-hand side cups with the class of a
global section. Constructing the general cup product means resolving both factors, and that is
Cohomology, Section [Stacks, Tag 0FKU]; the degree-zero case is the one where the cup product
collapses to functoriality and therefore needs no resolution of the second factor at all.

**The hypotheses.** `HasSheafify`, `WEqualsLocallyBijective` and `EnoughInjectives` are the
standing hypotheses of `Stacks.Cohomology.Hfunctor`, the right derived functors of
`Γ(U, -)`; they are the ones under which `H^q(U, -)` is defined at all, and this file adds none.

## References

* [Stacks Project, Tag 0FKU](https://stacks.math.columbia.edu/tag/0FKU)
* [Stacks Project, Tag 0G88](https://stacks.math.columbia.edu/tag/0G88)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TopologicalSpace

universe u

namespace Stacks.Cohomology

variable {X : Type u} [TopologicalSpace X]
variable {R : Sheaf (Opens.grothendieckTopology X) RingCat}

/-! ### Right multiplication by a global section of the second factor -/

section RightMul

variable {A A' B C C' : SheafOfModules R}

/-- **Right multiplication by a global section.** For a pairing `μ : 𝒜 × ℬ ⟶ 𝒞` of sheaves of
modules and a global section `u` of `ℬ`, this is the morphism of sheaves `𝒜 ⟶ 𝒞` carrying a
local section `a` to `μ(a, u|_V)`.

For the multiplication of a sheaf of graded algebras this is
`SheafOfModules.GradedAlgebra.rightMul`; the mirror construction fixing the *first* argument is
`SheafOfModules.GradedAlgebra.leftMul` of
`StacksFrontier/AlgebraicGeometry/DeRham/Gysin/GysinProjection.lean`. The two are different
morphisms and no graded commutativity relates them. -/
def rightMulHom (β : Stacks.BilinearMap A.val B.val C.val) (u : B.val.sections) : A ⟶ C where
  val :=
    { app := fun V => ModuleCat.ofHom
        { toFun := fun a => β.app V a (u.eval V)
          map_add' := fun a a' => β.map_add_left V a a' (u.eval V)
          map_smul' := fun r a => β.map_smul_left V r a (u.eval V) }
      naturality := by
        intro U V h
        ext a
        change β.app V (A.val.map h a) (u.eval V) = C.val.map h (β.app U a (u.eval U))
        rw [β.naturality h, PresheafOfModules.sections_property u h] }

/-- **The characterising equation of `rightMulHom`.** -/
@[simp]
theorem rightMulHom_app_apply (β : Stacks.BilinearMap A.val B.val C.val) (u : B.val.sections)
    (V : (Opens X)ᵒᵖ) (a : A.val.obj V) :
    (rightMulHom β u).val.app V a = β.app V a (u.eval V) := rfl

/-- **Right multiplication is functorial in the first coefficient sheaf**: restricting the
pairing along `φ : 𝒜' ⟶ 𝒜` is precomposition with `φ`. -/
theorem comp_rightMulHom (β : Stacks.BilinearMap A.val B.val C.val) (u : B.val.sections)
    (φ : A' ⟶ A) :
    rightMulHom (β.compLeft φ.val) u = φ ≫ rightMulHom β u := by
  ext V a
  rfl

/-- **Right multiplication along a morphism of the second factor.** Restricting the pairing
along `χ : ℬ' ⟶ ℬ` and multiplying by a global section `u'` of `ℬ'` is the same as multiplying
by its image in `ℬ`. -/
theorem rightMulHom_compRight (β : Stacks.BilinearMap A.val B.val C.val)
    {B' : SheafOfModules R} (χ : B' ⟶ B) (u' : B'.val.sections) :
    rightMulHom (β.compRight χ.val) u' =
      rightMulHom β (PresheafOfModules.sectionsMap χ.val u') := by
  ext V a
  rfl

end RightMul

/-! ### Cupping with a degree-zero class -/

section Cup

variable (R)
variable [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat]
variable [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat]
variable [EnoughInjectives (SheafOfModules R)]
variable {A A' B C C' : SheafOfModules R}

/-- **Cupping with a degree-zero class.** For a pairing `μ : 𝒜 × ℬ ⟶ 𝒞` of sheaves of modules
and a global section `u` of `ℬ` — that is, a class in `H^0(X, ℬ)` — this is the induced map
`H^q(X, 𝒜) ⟶ H^q(X, 𝒞)`.

It is `H^q` of the morphism `a ↦ μ(a, u)`: **for a degree-zero class the cup product is
functoriality along the multiplication map**, which is the normalization that the general cup
product of [Stacks, Tag 0FKU] satisfies and which is all that the projection formula of
[Stacks, Tag 0G88] uses. That this is the pairing and not some other natural map is
`cupDegreeZero_zero_toRightDerivedZero`, the case `q = 0`. -/
def cupDegreeZero (β : Stacks.BilinearMap A.val B.val C.val) (u : B.val.sections) (q : ℕ) :
    Hgroup R ⊤ q A ⟶ Hgroup R ⊤ q C :=
  (Hfunctor R ⊤ q).map (rightMulHom β u)

/-- **Naturality in the first coefficient sheaf.** -/
theorem cupDegreeZero_naturality_left (β : Stacks.BilinearMap A.val B.val C.val)
    (u : B.val.sections) (φ : A' ⟶ A) (q : ℕ) :
    cupDegreeZero R (β.compLeft φ.val) u q =
      (Hfunctor R ⊤ q).map φ ≫ cupDegreeZero R β u q := by
  rw [cupDegreeZero, cupDegreeZero, comp_rightMulHom, Functor.map_comp]

/-- **Cupping with a degree-zero class is compatible with a morphism of the second factor**:
cupping with `u'` for the restricted pairing is cupping with the image of `u'`. -/
theorem cupDegreeZero_compRight (β : Stacks.BilinearMap A.val B.val C.val)
    {B' : SheafOfModules R} (χ : B' ⟶ B) (u' : B'.val.sections) (q : ℕ) :
    cupDegreeZero R (β.compRight χ.val) u' q =
      cupDegreeZero R β (PresheafOfModules.sectionsMap χ.val u') q := by
  rw [cupDegreeZero, cupDegreeZero, rightMulHom_compRight]

/-- **The degree-zero normalization: cupping with a degree-zero class extends the pairing on
global sections.** The passage from a global section to a degree-zero cohomology class is
Mathlib's `CategoryTheory.Functor.toRightDerivedZero`, and this says that the square it makes
with the pairing commutes: the class of `a` cupped with `u` is the class of `μ(a, u)`.

Together with the definition of `cupDegreeZero` — which *is* the statement that cupping with a
degree-zero class is functoriality along the multiplication map — this pins the construction
down: in degree zero it is the pairing, and in higher degree it is the unique extension of it by
functoriality. -/
theorem cupDegreeZero_zero_toRightDerivedZero (β : Stacks.BilinearMap A.val B.val C.val)
    (u : B.val.sections) (a : (secF R (⊤ : Opens X)).obj A) :
    (cupDegreeZero R β u 0).hom (((secF R (⊤ : Opens X)).toRightDerivedZero.app A).hom a) =
      ((secF R (⊤ : Opens X)).toRightDerivedZero.app C).hom
        (((secF R (⊤ : Opens X)).map (rightMulHom β u)).hom a) :=
  congrArg (fun m => (ConcreteCategory.hom m) a)
    ((secF R (⊤ : Opens X)).toRightDerivedZero.naturality (rightMulHom β u)).symm

end Cup

end Stacks.Cohomology

end
