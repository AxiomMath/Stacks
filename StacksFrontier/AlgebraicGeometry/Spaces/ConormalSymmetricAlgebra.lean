module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedAlgebraBridge
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedAlgebraPullbackCommutative
public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalAlgebra

/-!
# The canonical map from the symmetric algebra on the conormal module

Let `i : Z ⟶ X` be a morphism of algebraic spaces over a scheme `S` contained in a big fppf
site `B`, with conormal algebra `𝒞_{Z/X,*}` of Stacks 09RN and conormal module
`𝒞_{Z/X} = (𝒞_{Z/X,*})_1` of Stacks 04CN.  Equation 76.6.1.2 of Stacks 09RQ is the canonical
map of graded `𝒪_Z`-algebras

`Sym^*(𝒞_{Z/X}) ⟶ 𝒞_{Z/X,*}`

which is the identity in degree one.  This file constructs it.

The symmetric algebra on a sheaf of modules is presented by its universal property rather than
by a construction: a consumer supplies a sheaf of graded algebras `A` together with a degree-one
generator `ι : 𝒞_{Z/X} ⟶ A_1` universal for
`SheafOfModules.GradedAlgebra.PairwiseCommutes`, which is what
`SheafOfModules.GradedAlgebra.IsSymmetricAlgebra` says, and the map out of it is the unique
unital homomorphism extending the identity of `𝒞_{Z/X}`.  That is strictly stronger than a
statement about one chosen symmetric algebra, and
`SheafOfModules.GradedAlgebra.IsUniversal.pieceIso` records that the hypotheses pin `A` down up
to a unique isomorphism of graded algebras.

What has to be proved for the universal property to apply is that the degree-`(1,1)`
multiplication of `𝒞_{Z/X,*}` is commutative.  It is, because the conormal algebra is the
inverse image of the graded algebra `⨁_{n ≥ 0} 𝓘ⁿ` of the powers of the kernel ideal sheaf,
whose multiplication is the multiplication of sections of `𝒪_X` and therefore commutative, and
because commutativity in two equal degrees survives a pullback of sheaves of graded algebras by
`Stacks.Sheaves.GradedAlgebraPullback.toposPullbackGradedAlgebra_mul_one_one_comm`.

## Main definitions

* `AlgebraicGeometry.Space.symmetricAlgebraToConormalAlgebra`: **Stacks 09RQ**, Equation
  76.6.1.2, the canonical map `Sym^*(𝒞_{Z/X}) ⟶ 𝒞_{Z/X,*}`.
* `AlgebraicGeometry.Space.symmetricAlgebraToConormalAlgebraOfImmersion`: the same for an
  immersion, through the closed factorisation of Stacks 04CE.

## Main results

* `SheafOfModules.reesGradedAlgebra_mul_comm`: the multiplication of the graded algebra of the
  powers of a sheaf of ideals is commutative between two equal degrees.
* `AlgebraicGeometry.Space.conormalAlgebra_mul_one_one_comm`: the degree-`(1,1)` multiplication
  of the conormal algebra is commutative.
* `AlgebraicGeometry.Space.symmetricAlgebraToConormalAlgebra_app_one` and
  `AlgebraicGeometry.Space.symmetricAlgebraToConormalAlgebra_unique`: the canonical map is the
  identity in degree one, and is the only unital homomorphism which is.

## Implementation notes

The commutativity hypothesis is read as
`SheafOfModules.GradedAlgebra.PairwiseCommutes (𝟙 ((𝒞_{Z/X,*}).piece 1))`: taking the generator
to be the identity of the degree-one piece turns the condition "any two degree-one local sections
in the image of the generator commute" into plain commutativity of the degree-`(1,1)`
multiplication, which is the form in which it is proved.

Commutativity of the multiplication of `⨁_{n ≥ 0} 𝓘ⁿ` is stated between two *equal* degrees.
Between different degrees the two sides of the equation lie in the homogeneous pieces of degrees
`i + j` and `j + i`, which are propositionally but not definitionally equal, so the statement
would have to be a heterogeneous equality; the symmetric-algebra universal property only
constrains degree `(1,1)`, so nothing is lost.

## References

* [Stacks Project, Tag 09RQ](https://stacks.math.columbia.edu/tag/09RQ)
* [Stacks Project, Tag 09RN](https://stacks.math.columbia.edu/tag/09RN)
* [Stacks Project, Tag 04CN](https://stacks.math.columbia.edu/tag/04CN)
* [Stacks Project, Tag 0FQW](https://stacks.math.columbia.edu/tag/0FQW)
* [Stacks Project, Tag 0FQX](https://stacks.math.columbia.edu/tag/0FQX)
* [Stacks Project, Section 17.21](https://stacks.math.columbia.edu/tag/01CF)
-/

@[expose] public section

open CategoryTheory Opposite

/-! ### Commutativity of the graded algebra of the powers of a sheaf of ideals -/

namespace SheafOfModules

universe t v u

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t}}
  (I : (unit R).Submodule)
  (hcomm : ∀ (X : Cᵒᵖ) (a b : ToType (R.obj.obj X)), a * b = b * a)

/-- **The multiplication of the graded algebra of the powers of a sheaf of ideals is commutative
between two equal degrees**, because it is the multiplication of sections of the structure
sheaf. -/
theorem reesMul_comm (i : ℤ) (X : Cᵒᵖ) (x y : (reesPiece I i).val.obj X) :
    (reesMul I hcomm i i).app X x y = (reesMul I hcomm i i).app X y x :=
  reesPiece_ext I (by
    rw [reesVal_reesMul_app, reesVal_reesMul_app, hcomm X])

/-- **The graded algebra of the powers of a sheaf of ideals has commutative multiplication
between two equal degrees.** -/
theorem reesGradedAlgebra_mul_comm (i : ℤ) (X : Cᵒᵖ)
    (x y : ((reesGradedAlgebra I hcomm).piece i).val.obj X) :
    ((reesGradedAlgebra I hcomm).mul i i).app X x y =
      ((reesGradedAlgebra I hcomm).mul i i).app X y x :=
  reesMul_comm I hcomm i X x y

end SheafOfModules

/-! ### Commutativity of the degree-one multiplication of the conormal algebra -/

namespace AlgebraicGeometry.Space

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y Z : AlgebraicSpaces B S hS}

/-- **The multiplication of the graded algebra of the powers of the kernel ideal sheaf is
commutative between two equal degrees.** -/
theorem kernelIdealGradedAlgebra_mul_comm (f : X ⟶ Y) (i : ℤ)
    (V : (SmallEtale B S hS Y.1)ᵒᵖ)
    (x y : ((kernelIdealGradedAlgebra B S hS f).piece i).val.obj V) :
    ((kernelIdealGradedAlgebra B S hS f).mul i i).app V x y =
      ((kernelIdealGradedAlgebra B S hS f).mul i i).app V y x :=
  SheafOfModules.reesGradedAlgebra_mul_comm (kernelIdealSheaf B S hS f)
    (structureRingSheaf_mul_comm B S hS Y) i V x y

/-- **The degree-`(1,1)` multiplication of the conormal algebra is commutative.**  The conormal
algebra is the inverse image of the graded algebra of the powers of the kernel ideal sheaf, whose
multiplication is the commutative multiplication of sections of `𝒪_X`, and commutativity in two
equal degrees survives a pullback of sheaves of graded algebras. -/
theorem conormalAlgebra_mul_one_one_comm (i : Z ⟶ X) (U : (SmallEtale B S hS Z.1)ᵒᵖ)
    (s u : ((conormalAlgebra B S hS i).piece 1).val.obj U) :
    ((conormalAlgebra B S hS i).mul 1 1).app U s u =
      ((conormalAlgebra B S hS i).mul 1 1).app U u s :=
  Stacks.Sheaves.GradedAlgebraPullback.toposPullbackGradedAlgebra_mul_one_one_comm
    (X := smallEtaleRingedTopos B S hS Z) (Y := smallEtaleRingedTopos B S hS X)
    (smallEtaleRingedToposModulesHom B S hS i) (kernelIdealGradedAlgebra B S hS i)
    (fun V x y ↦ kernelIdealGradedAlgebra_mul_comm B S hS i 1 V x y) U s u

/-- **Any two degree-one local sections of the conormal algebra commute.**  This is
`AlgebraicGeometry.Space.conormalAlgebra_mul_one_one_comm` read as the hypothesis that the
universal property of the symmetric algebra imposes on a degree-one generator, for the generator
being the identity of the degree-one piece. -/
theorem pairwiseCommutes_id_conormalAlgebra (i : Z ⟶ X) :
    SheafOfModules.GradedAlgebra.PairwiseCommutes (A := conormalAlgebra B S hS i)
      (𝟙 ((conormalAlgebra B S hS i).piece 1)) :=
  fun U s u ↦ conormalAlgebra_mul_one_one_comm B S hS i U s u

/-! ### The canonical map of Equation 76.6.1.2 -/

/-- **Stacks Project, Tag 09RQ, Equation 76.6.1.2.**  Let `i : Z ⟶ X` be a morphism of algebraic
spaces and let `A` be a sheaf of graded `𝒪_Z`-algebras which is the symmetric algebra on the
conormal module `𝒞_{Z/X} = (𝒞_{Z/X,*})_1`, with degree-one generator `ι`.  Then there is a
canonical unital homomorphism of sheaves of graded `𝒪_Z`-algebras

`Sym^*(𝒞_{Z/X}) ⟶ 𝒞_{Z/X,*}`,

the unique one extending the identity of the conormal module.

It exists because the degree-`(1,1)` multiplication of the conormal algebra is commutative, by
`AlgebraicGeometry.Space.conormalAlgebra_mul_one_one_comm`, which is exactly the condition the
universal property of the symmetric algebra tests a degree-one generator against. -/
@[stacks 09RQ "the canonical map from the symmetric algebra on the conormal module"]
noncomputable def symmetricAlgebraToConormalAlgebra (i : Z ⟶ X)
    (A : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf B S hS Z))
    (ι : (conormalAlgebra B S hS i).piece 1 ⟶ A.piece 1)
    (hA : SheafOfModules.GradedAlgebra.IsSymmetricAlgebra A ι) :
    SheafOfModules.GradedAlgebra.UnitalHom A (conormalAlgebra B S hS i) :=
  hA.isUniversal.desc (conormalAlgebra B S hS i)
    (𝟙 ((conormalAlgebra B S hS i).piece 1))
    (pairwiseCommutes_id_conormalAlgebra B S hS i)

/-- **The canonical map of Equation 76.6.1.2 is the identity in degree one.** -/
theorem symmetricAlgebraToConormalAlgebra_app_one (i : Z ⟶ X)
    (A : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf B S hS Z))
    (ι : (conormalAlgebra B S hS i).piece 1 ⟶ A.piece 1)
    (hA : SheafOfModules.GradedAlgebra.IsSymmetricAlgebra A ι) :
    ι ≫ (symmetricAlgebraToConormalAlgebra B S hS i A ι hA).app 1 =
      𝟙 ((conormalAlgebra B S hS i).piece 1) :=
  hA.isUniversal.desc_extends (conormalAlgebra B S hS i)
    (𝟙 ((conormalAlgebra B S hS i).piece 1))
    (pairwiseCommutes_id_conormalAlgebra B S hS i)

/-- **The canonical map of Equation 76.6.1.2 is the only unital homomorphism which is the
identity in degree one.** -/
theorem symmetricAlgebraToConormalAlgebra_unique (i : Z ⟶ X)
    (A : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf B S hS Z))
    (ι : (conormalAlgebra B S hS i).piece 1 ⟶ A.piece 1)
    (hA : SheafOfModules.GradedAlgebra.IsSymmetricAlgebra A ι)
    (g : SheafOfModules.GradedAlgebra.UnitalHom A (conormalAlgebra B S hS i))
    (hg : ι ≫ g.app 1 = 𝟙 ((conormalAlgebra B S hS i).piece 1)) :
    g = symmetricAlgebraToConormalAlgebra B S hS i A ι hA :=
  hA.isUniversal.desc_unique (conormalAlgebra B S hS i)
    (𝟙 ((conormalAlgebra B S hS i).piece 1))
    (pairwiseCommutes_id_conormalAlgebra B S hS i) hg

/-! ### The case of an immersion -/

section Immersion

attribute [local instance] pointTopology

variable {Z₀ X₀ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- **Stacks Project, Tag 09RQ for an immersion.**  The canonical map
`Sym^*(𝒞_{Z/X}) ⟶ 𝒞_{Z/X,*}` of Equation 76.6.1.2 for an immersion `i : Z ⟶ X`, taken through
the closed factorisation of Stacks 04CE which defines
`AlgebraicGeometry.Space.conormalAlgebraOfImmersion`. -/
@[stacks 09RQ "the canonical map from the symmetric algebra, for an immersion"]
noncomputable def symmetricAlgebraToConormalAlgebraOfImmersion
    (hX : IsAlgebraicSpace B S hS X₀) (hZ : IsAlgebraicSpace B S hS Z₀) (i : Z₀ ⟶ X₀)
    (hi : IsImmersion B S hS i)
    (A : SheafOfModules.GradedAlgebra.{u, u}
      (structureRingSheaf B S hS (⟨Z₀, hZ⟩ : AlgebraicSpaces B S hS)))
    (ι : (conormalAlgebraOfImmersion B S hS hX hZ i hi).piece 1 ⟶ A.piece 1)
    (hA : SheafOfModules.GradedAlgebra.IsSymmetricAlgebra A ι) :
    SheafOfModules.GradedAlgebra.UnitalHom A
      (conormalAlgebraOfImmersion B S hS hX hZ i hi) :=
  symmetricAlgebraToConormalAlgebra B S hS
    (immersionClosedFactorization B S hS hX hZ i hi) A ι hA

end Immersion

end AlgebraicGeometry.Space

end
