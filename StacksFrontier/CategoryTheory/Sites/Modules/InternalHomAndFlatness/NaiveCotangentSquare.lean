module

public import StacksFrontier.CategoryTheory.CommutingSquares
public import Mathlib.Algebra.Homology.Additive
public import StacksFrontier.CategoryTheory.Sites.Modules.ConormalSequenceSquare
public import StacksFrontier.CategoryTheory.Sites.Modules.InternalHomAndFlatness.NaiveCotangent

/-!
# Functoriality of the naive cotangent complex in a square of sheaves of rings

A commutative square
```
B ──β──▸ B'
▲         ▲
a         a'
│         │
A ──f──▸ A'
```
of sheaves of commutative rings on a site induces a canonical `B`-linear map of complexes
`NL_{B/A} ⟶ NL_{B'/A'}`.  Indeed the square gives a morphism `A[B] ⟶ A'[B']` of the two
canonical polynomial presentations which carries the kernel `I` of `A[B] ⟶ B` into the kernel
`I'` of `A'[B'] ⟶ B'`, hence a map `I/I² ⟶ I'/(I')²` in degree `-1` and a map
`B ⊗_{A[B]} Ω_{A[B]/A} ⟶ B' ⊗_{A'[B']} Ω_{A'[B']/A'}` in degree `0`.

## Main definitions

* `Stacks.SheafOfModules.freeAlgebraMapOfSquare`: the morphism `A[E] ⟶ A'[E']` of free
  algebra sheaves induced by `f : A ⟶ A'` and a morphism `E ⟶ E'` of presheaves of sets.
* `Stacks.SheafOfModules.underlyingPresheafMap`: a morphism of sheaves of commutative rings,
  read as a morphism of the underlying presheaves of sets.
* `Stacks.SheafOfModules.naiveCotangentConormalMapOfSquare` and
  `Stacks.SheafOfModules.naiveCotangentTensorMapOfSquare`: the maps induced on the two terms
  of the naive cotangent complexes.
* `Stacks.SheafOfModules.naiveCotangentComplexMapOfSquare`: the chain map
  `NL_{B/A} ⟶ NL_{B'/A'}`.
* `Stacks.SheafOfModules.naiveCotangentComplexMapOfBase`: the case `β = 𝟙 B` of that chain map,
  attached to a factorisation `a = f ≫ a'` of the structure morphism of `B`; both its source and
  its target are complexes of sheaves of `B`-modules.

## Main results

* `Stacks.SheafOfModules.freeAlgebraMapOfSquare_comp_canonicalPresentation`: the induced
  morphism of free algebra sheaves is compatible with the two canonical presentations.
* `Stacks.SheafOfModules.naiveCotangentComplexMapOfSquare_f_negOne` and
  `Stacks.SheafOfModules.naiveCotangentComplexMapOfSquare_f_zero`: the two nonzero components
  of the chain map are the maps of conormal sheaves and of the scalar extensions of the
  differentials.
* `SheafOfModules.restrictScalars_id`: restriction of scalars along the identity of a sheaf of
  rings is the identity functor.
* `Stacks.SheafOfModules.naiveCotangentComplexMapOfSquare_comp`: the chain map is compatible with
  compositions, that is, for two squares side by side the composite
  `NL_{B/A} ⟶ NL_{B'/A'} ⟶ NL_{B''/A''}` is the chain map of the outer rectangle.

## Implementation notes

The target of the chain map is the image of `NL_{B'/A'}` under termwise restriction of scalars
along `β`, so that both complexes consist of sheaves of `B`-modules; this is the Lean reading of
the source's assertion that the map is `B`-linear.  `Stacks.SheafOfModules.freeAlgebraMapOfSquare`
is the case of a varying coefficient sheaf of `Stacks.SheafOfModules.freeAlgebraMap`, and the two
maps on the terms come from
`StacksFrontier/CategoryTheory/Sites/Modules/ConormalSequenceSquare.lean`, whose `…OfSquare` family
is the corresponding generalisation of the `…OfFac` family used for a change of presentation of
a fixed morphism.

## References

* [Stacks Project, Tag 08TX](https://stacks.math.columbia.edu/tag/08TX)
* [Stacks Project, Tag 08TW](https://stacks.math.columbia.edu/tag/08TW), the naive cotangent
  complex of a homomorphism of sheaves of rings on a site.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v u w z

namespace SheafOfModules

/-- Restriction of scalars along the identity of a sheaf of rings is the identity functor: it
changes neither the sections of a sheaf of modules nor its module structure. -/
theorem restrictScalars_id {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{w}) :
    restrictScalars.{max w u v z} (𝟙 R) = 𝟭 (SheafOfModules.{max w u v z} R) :=
  rfl

end SheafOfModules

namespace Stacks.SheafOfModules

open AlgebraicGeometry.SheafOfModules (underlyingRingHomOfSite)
open Stacks.Sites.Conormal (conormalSheafMapOfSquare tensorSheafMapOfSquare
  conormalSequence_f_naturality_square hom_of_square)

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [HasWeakSheafify J CommRingCat.{w}]
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]

/-! ### Free algebra sheaves along a square -/

section FreeAlgebra

variable (A A' : Sheaf J CommRingCat.{w}) (E E' : Functor Cᵒᵖ (Type w))
  (f : A ⟶ A') (h : E ⟶ E')

/-- The morphism `A[E] ⟶ A'[E']` induced by a morphism `f : A ⟶ A'` of coefficients and a
morphism `h : E ⟶ E'` of families of variables: it is `f` on coefficients and sends the
variable `[x]` to the variable `[h x]`. -/
noncomputable abbrev freeAlgebraMapOfSquare :
    Stacks.Sites.FreeAlgebra.freeAlgebraSheaf J A E ⟶
      Stacks.Sites.FreeAlgebra.freeAlgebraSheaf J A' E' :=
  Stacks.Sites.FreeAlgebra.freeAlgebraSheafDesc J A
    (Stacks.Sites.FreeAlgebra.freeAlgebraSheaf J A' E') E
    (f ≫ Stacks.Sites.FreeAlgebra.freeAlgebraSheafCoefficientMap J A' E')
    (h ≫ Stacks.Sites.FreeAlgebra.freeAlgebraSheafVariable J A' E')

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- On coefficients the morphism `A[E] ⟶ A'[E']` is `f`. -/
theorem freeAlgebraSheafCoefficientMap_comp_freeAlgebraMapOfSquare :
    Stacks.Sites.FreeAlgebra.freeAlgebraSheafCoefficientMap J A E ≫
        freeAlgebraMapOfSquare J A A' E E' f h =
      f ≫ Stacks.Sites.FreeAlgebra.freeAlgebraSheafCoefficientMap J A' E' :=
  Stacks.Sites.FreeAlgebra.freeAlgebraSheafCoefficientMap_comp_desc J A _ E _ _

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- The morphism `A[E] ⟶ A'[E']` sends the variable `[x]` to the variable `[h x]`. -/
theorem freeAlgebraSheafVariable_comp_freeAlgebraMapOfSquare :
    Stacks.Sites.FreeAlgebra.freeAlgebraSheafVariable J A E ≫ Functor.whiskerRight
        ((sheafToPresheaf J CommRingCat.{w}).map (freeAlgebraMapOfSquare J A A' E E' f h))
        (forget CommRingCat.{w}) =
      h ≫ Stacks.Sites.FreeAlgebra.freeAlgebraSheafVariable J A' E' :=
  Stacks.Sites.FreeAlgebra.freeAlgebraSheafVariable_comp_desc J A _ E _ _

end FreeAlgebra

/-! ### The canonical presentations along a square -/

section Presentation

variable (A A' B B' : Sheaf J CommRingCat.{w}) (a : A ⟶ B) (a' : A' ⟶ B')
  (f : A ⟶ A') (β : B ⟶ B')

/-- A morphism of sheaves of commutative rings, read as a morphism of the underlying presheaves
of sets. -/
abbrev underlyingPresheafMap :
    Stacks.Sites.FreeAlgebra.underlyingPresheaf J B ⟶
      Stacks.Sites.FreeAlgebra.underlyingPresheaf J B' :=
  Functor.whiskerRight ((sheafToPresheaf J CommRingCat.{w}).map β) (forget CommRingCat.{w})

/-- The morphism `A[B] ⟶ A'[B']` attached to a commutative square. -/
noncomputable abbrev canonicalFreeAlgebraMapOfSquare :
    Stacks.Sites.FreeAlgebra.freeAlgebraSheaf J A
        (Stacks.Sites.FreeAlgebra.underlyingPresheaf J B) ⟶
      Stacks.Sites.FreeAlgebra.freeAlgebraSheaf J A'
        (Stacks.Sites.FreeAlgebra.underlyingPresheaf J B') :=
  freeAlgebraMapOfSquare J A A' _ _ f (underlyingPresheafMap J B B' β)

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- The canonical presentation `A[B] ⟶ B` sends the variable `[b]` to `b`. -/
theorem freeAlgebraSheafVariable_comp_canonicalPresentation :
    Stacks.Sites.FreeAlgebra.freeAlgebraSheafVariable J A
        (Stacks.Sites.FreeAlgebra.underlyingPresheaf J B) ≫
        Functor.whiskerRight ((sheafToPresheaf J CommRingCat.{w}).map
          (Stacks.Sites.FreeAlgebra.canonicalPresentation J A B a)) (forget CommRingCat.{w}) =
      𝟙 (Stacks.Sites.FreeAlgebra.underlyingPresheaf J B) := by
  rw [Stacks.Sites.FreeAlgebra.canonicalPresentation_eq_desc]
  exact Stacks.Sites.FreeAlgebra.freeAlgebraSheafVariable_comp_desc J A B _ a (𝟙 _)

variable (hsq : a ≫ β = f ≫ a')

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
include hsq in
/-- The morphism `A[B] ⟶ A'[B']` attached to a commutative square is compatible with the two
canonical presentations. -/
@[stacks 08TX "the canonical map A[B] ⟶ A'[B'] attached to the square"]
theorem freeAlgebraMapOfSquare_comp_canonicalPresentation :
    canonicalFreeAlgebraMapOfSquare J A A' B B' f β ≫
        Stacks.Sites.FreeAlgebra.canonicalPresentation J A' B' a' =
      Stacks.Sites.FreeAlgebra.canonicalPresentation J A B a ≫ β := by
  refine Stacks.Sites.FreeAlgebra.freeAlgebraSheaf_hom_ext J A B' _ ?_ ?_
  · rw [← Category.assoc, freeAlgebraSheafCoefficientMap_comp_freeAlgebraMapOfSquare,
      Category.assoc, Stacks.Sites.FreeAlgebra.canonicalPresentation_comp_coefficientMap,
      ← Category.assoc, Stacks.Sites.FreeAlgebra.canonicalPresentation_comp_coefficientMap,
      hsq]
  · rw [Functor.map_comp, Functor.map_comp, Functor.whiskerRight_comp, Functor.whiskerRight_comp,
      ← Category.assoc, ← Category.assoc,
      freeAlgebraSheafVariable_comp_freeAlgebraMapOfSquare,
      freeAlgebraSheafVariable_comp_canonicalPresentation J A B a, Category.assoc,
      freeAlgebraSheafVariable_comp_canonicalPresentation J A' B' a',
      Category.comp_id, Category.id_comp]

end Presentation

/-! ### The chain map -/

section ComplexMap

variable (A B : Sheaf J CommRingCat.{w}) (a : A ⟶ B)

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- The naive cotangent complex `NL_{B/A}` is concentrated in degrees `-1` and `0`, so it has no
differential out of degree `0`. -/
private theorem naiveCotangentComplex_d_zero (k : ℤ) :
    (naiveCotangentComplex.{v, u, w, z} J A B a).d 0 k = 0 := by
  have : HasZeroObject
      (_root_.SheafOfModules.{max w u v z} (Stacks.SheafOfModules.Tensor.ringSheaf B)) :=
    hasZeroObject_of_hasTerminal_object
  show (HomologicalComplex.double
    (canonicalConormalSequence.{v, u, w, z} J A B a).f
    (show (ComplexShape.up ℤ).Rel (-1) 0 from by decide)).d 0 k = 0
  exact HomologicalComplex.double_d_eq_zero₀ _ _ 0 k (by decide)

variable (A' B' : Sheaf J CommRingCat.{w}) (a' : A' ⟶ B') (f : A ⟶ A') (β : B ⟶ B')
  (hsq : a ≫ β = f ≫ a')

include hsq in
/-- The map `I/I² ⟶ I'/(I')²` of conormal sheaves attached to a commutative square. -/
noncomputable def naiveCotangentConormalMapOfSquare :
    (canonicalConormalSequence.{v, u, w, z} J A B a).X₁ ⟶
      (_root_.SheafOfModules.restrictScalars.{max w u v z} (underlyingRingHomOfSite β)).obj
        (canonicalConormalSequence.{v, u, w, z} J A' B' a').X₁ :=
  conormalSheafMapOfSquare.{v, u, w, z} J _ _ B B'
    (Stacks.Sites.FreeAlgebra.canonicalPresentation J A B a)
    (Stacks.Sites.FreeAlgebra.canonicalPresentation J A' B' a')
    (canonicalFreeAlgebraMapOfSquare J A A' B B' f β) β
    (freeAlgebraMapOfSquare_comp_canonicalPresentation J A A' B B' a a' f β hsq)

include hsq in
/-- The map `B ⊗_{A[B]} Ω_{A[B]/A} ⟶ B' ⊗_{A'[B']} Ω_{A'[B']/A'}` attached to a commutative
square. -/
noncomputable def naiveCotangentTensorMapOfSquare :
    (canonicalConormalSequence.{v, u, w, z} J A B a).X₂ ⟶
      (_root_.SheafOfModules.restrictScalars.{max w u v z} (underlyingRingHomOfSite β)).obj
        (canonicalConormalSequence.{v, u, w, z} J A' B' a').X₂ :=
  tensorSheafMapOfSquare.{v, u, w, z} J A A' _ _ B B'
    (Stacks.Sites.FreeAlgebra.freeAlgebraSheafCoefficientMap J A _)
    (Stacks.Sites.FreeAlgebra.freeAlgebraSheafCoefficientMap J A' _)
    (Stacks.Sites.FreeAlgebra.canonicalPresentation J A B a)
    (Stacks.Sites.FreeAlgebra.canonicalPresentation J A' B' a')
    (canonicalFreeAlgebraMapOfSquare J A A' B B' f β) β f
    (freeAlgebraMapOfSquare_comp_canonicalPresentation J A A' B B' a a' f β hsq)
    (freeAlgebraSheafCoefficientMap_comp_freeAlgebraMapOfSquare J A A' _ _ f
      (underlyingPresheafMap J B B' β)).symm

include hsq in
/-- The two maps attached to a commutative square commute with the differentials of the two
naive cotangent complexes. -/
theorem naiveCotangentConormalMapOfSquare_comm :
    (naiveCotangentConormalMapOfSquare.{v, u, w, z} J A B a A' B' a' f β hsq ≫
        (_root_.SheafOfModules.restrictScalars.{max w u v z}
          (underlyingRingHomOfSite β)).map
          (eqToHom (naiveCotangentComplex_X_negOne.{v, u, w, z} J A' B' a').symm)) ≫
      (((_root_.SheafOfModules.restrictScalars.{max w u v z}
          (underlyingRingHomOfSite β)).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (naiveCotangentComplex.{v, u, w, z} J A' B' a')).d (-1) 0 =
    (canonicalConormalSequence.{v, u, w, z} J A B a).f ≫
      (naiveCotangentTensorMapOfSquare.{v, u, w, z} J A B a A' B' a' f β hsq ≫
        (_root_.SheafOfModules.restrictScalars.{max w u v z}
          (underlyingRingHomOfSite β)).map
          (eqToHom (naiveCotangentComplex_X_zero.{v, u, w, z} J A' B' a').symm)) := by
  have key : (_root_.SheafOfModules.restrictScalars.{max w u v z}
          (underlyingRingHomOfSite β)).map
          (eqToHom (naiveCotangentComplex_X_negOne.{v, u, w, z} J A' B' a').symm) ≫
        (((_root_.SheafOfModules.restrictScalars.{max w u v z}
            (underlyingRingHomOfSite β)).mapHomologicalComplex (ComplexShape.up ℤ)).obj
          (naiveCotangentComplex.{v, u, w, z} J A' B' a')).d (-1) 0 =
      (_root_.SheafOfModules.restrictScalars.{max w u v z} (underlyingRingHomOfSite β)).map
          (canonicalConormalSequence.{v, u, w, z} J A' B' a').f ≫
        (_root_.SheafOfModules.restrictScalars.{max w u v z} (underlyingRingHomOfSite β)).map
          (eqToHom (naiveCotangentComplex_X_zero.{v, u, w, z} J A' B' a').symm) := by
    show _ ≫ (_root_.SheafOfModules.restrictScalars.{max w u v z}
        (underlyingRingHomOfSite β)).map
          ((naiveCotangentComplex.{v, u, w, z} J A' B' a').d (-1) 0) = _
    rw [naiveCotangentComplex_d_negOne_zero, Functor.map_comp, Functor.map_comp,
      ← Category.assoc, ← Functor.map_comp, eqToHom_trans, eqToHom_refl,
      CategoryTheory.Functor.map_id, Category.id_comp]
  rw [Category.assoc, key, ← Category.assoc, ← Category.assoc]
  exact congrArg (fun t ↦ t ≫ (_root_.SheafOfModules.restrictScalars.{max w u v z}
      (underlyingRingHomOfSite β)).map
      (eqToHom (naiveCotangentComplex_X_zero.{v, u, w, z} J A' B' a').symm))
    (conormalSequence_f_naturality_square.{v, u, w, z} J A A' _ _ B B'
      (Stacks.Sites.FreeAlgebra.freeAlgebraSheafCoefficientMap J A _)
      (Stacks.Sites.FreeAlgebra.freeAlgebraSheafCoefficientMap J A' _)
      (Stacks.Sites.FreeAlgebra.canonicalPresentation J A B a)
      (Stacks.Sites.FreeAlgebra.canonicalPresentation J A' B' a')
      (canonicalFreeAlgebraMapOfSquare J A A' B B' f β) β f
      (freeAlgebraMapOfSquare_comp_canonicalPresentation J A A' B B' a a' f β hsq)
      (freeAlgebraSheafCoefficientMap_comp_freeAlgebraMapOfSquare J A A' _ _ f
        (underlyingPresheafMap J B B' β)).symm).symm

include hsq in
/-- The degree `0` component is killed by every differential out of degree `0`, since
`NL_{B'/A'}` has none. -/
theorem naiveCotangentTensorMapOfSquare_comp_d (k : ℤ) :
    (naiveCotangentTensorMapOfSquare.{v, u, w, z} J A B a A' B' a' f β hsq ≫
        (_root_.SheafOfModules.restrictScalars.{max w u v z}
          (underlyingRingHomOfSite β)).map
          (eqToHom (naiveCotangentComplex_X_zero.{v, u, w, z} J A' B' a').symm)) ≫
      (((_root_.SheafOfModules.restrictScalars.{max w u v z}
          (underlyingRingHomOfSite β)).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (naiveCotangentComplex.{v, u, w, z} J A' B' a')).d 0 k = 0 := by
  show _ ≫ (_root_.SheafOfModules.restrictScalars.{max w u v z}
      (underlyingRingHomOfSite β)).map
        ((naiveCotangentComplex.{v, u, w, z} J A' B' a').d 0 k) = _
  rw [naiveCotangentComplex_d_zero, Functor.map_zero, Limits.comp_zero]

include hsq in
/-- **Stacks 08TX.** The canonical `B`-linear chain map `NL_{B/A} ⟶ NL_{B'/A'}` attached to a
commutative square of sheaves of rings: it is the map of conormal sheaves in degree `-1` and the
map of the scalar extensions of the differentials in degree `0`. -/
@[stacks 08TX "the canonical B-linear map of complexes NL_{B/A} ⟶ NL_{B'/A'}"]
noncomputable def naiveCotangentComplexMapOfSquare :
    naiveCotangentComplex.{v, u, w, z} J A B a ⟶
      ((_root_.SheafOfModules.restrictScalars.{max w u v z}
          (underlyingRingHomOfSite β)).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (naiveCotangentComplex.{v, u, w, z} J A' B' a') := by
  have : HasZeroObject
      (_root_.SheafOfModules.{max w u v z} (Stacks.SheafOfModules.Tensor.ringSheaf B)) :=
    hasZeroObject_of_hasTerminal_object
  exact HomologicalComplex.mkHomFromDouble
    (show (ComplexShape.up ℤ).Rel (-1) 0 from by decide) (by decide)
    (naiveCotangentConormalMapOfSquare.{v, u, w, z} J A B a A' B' a' f β hsq ≫
      (_root_.SheafOfModules.restrictScalars.{max w u v z} (underlyingRingHomOfSite β)).map
        (eqToHom (naiveCotangentComplex_X_negOne.{v, u, w, z} J A' B' a').symm))
    (naiveCotangentTensorMapOfSquare.{v, u, w, z} J A B a A' B' a' f β hsq ≫
      (_root_.SheafOfModules.restrictScalars.{max w u v z} (underlyingRingHomOfSite β)).map
        (eqToHom (naiveCotangentComplex_X_zero.{v, u, w, z} J A' B' a').symm))
    (naiveCotangentConormalMapOfSquare_comm.{v, u, w, z} J A B a A' B' a' f β hsq)
    (fun k _ ↦ naiveCotangentTensorMapOfSquare_comp_d.{v, u, w, z} J A B a A' B' a' f β hsq k)

include hsq in
/-- In degree `-1` the chain map is the map of conormal sheaves. -/
theorem naiveCotangentComplexMapOfSquare_f_negOne :
    (naiveCotangentComplexMapOfSquare.{v, u, w, z} J A B a A' B' a' f β hsq).f (-1) =
      eqToHom (naiveCotangentComplex_X_negOne.{v, u, w, z} J A B a) ≫
        naiveCotangentConormalMapOfSquare.{v, u, w, z} J A B a A' B' a' f β hsq ≫
        (_root_.SheafOfModules.restrictScalars.{max w u v z} (underlyingRingHomOfSite β)).map
          (eqToHom (naiveCotangentComplex_X_negOne.{v, u, w, z} J A' B' a').symm) := by
  have : HasZeroObject
      (_root_.SheafOfModules.{max w u v z} (Stacks.SheafOfModules.Tensor.ringSheaf B)) :=
    hasZeroObject_of_hasTerminal_object
  have h₀ : (HomologicalComplex.doubleXIso₀
      (canonicalConormalSequence.{v, u, w, z} J A B a).f
      (show (ComplexShape.up ℤ).Rel (-1) 0 from by decide)).hom =
      eqToHom (naiveCotangentComplex_X_negOne.{v, u, w, z} J A B a) := by
    simp only [HomologicalComplex.doubleXIso₀]
    congr 1
  rw [← h₀]
  exact HomologicalComplex.mkHomFromDouble_f₀
    (show (ComplexShape.up ℤ).Rel (-1) 0 from by decide) (by decide) _ _
    (naiveCotangentConormalMapOfSquare_comm.{v, u, w, z} J A B a A' B' a' f β hsq)
    (fun k _ ↦ naiveCotangentTensorMapOfSquare_comp_d.{v, u, w, z} J A B a A' B' a' f β hsq k)

include hsq in
/-- In degree `0` the chain map is the map on the scalar extensions of the differentials. -/
theorem naiveCotangentComplexMapOfSquare_f_zero :
    (naiveCotangentComplexMapOfSquare.{v, u, w, z} J A B a A' B' a' f β hsq).f 0 =
      eqToHom (naiveCotangentComplex_X_zero.{v, u, w, z} J A B a) ≫
        naiveCotangentTensorMapOfSquare.{v, u, w, z} J A B a A' B' a' f β hsq ≫
        (_root_.SheafOfModules.restrictScalars.{max w u v z} (underlyingRingHomOfSite β)).map
          (eqToHom (naiveCotangentComplex_X_zero.{v, u, w, z} J A' B' a').symm) := by
  have : HasZeroObject
      (_root_.SheafOfModules.{max w u v z} (Stacks.SheafOfModules.Tensor.ringSheaf B)) :=
    hasZeroObject_of_hasTerminal_object
  have h₁ : (HomologicalComplex.doubleXIso₁
      (canonicalConormalSequence.{v, u, w, z} J A B a).f
      (show (ComplexShape.up ℤ).Rel (-1) 0 from by decide) (by decide)).hom =
      eqToHom (naiveCotangentComplex_X_zero.{v, u, w, z} J A B a) := by
    simp only [HomologicalComplex.doubleXIso₁]
    congr 1
  rw [← h₁]
  exact HomologicalComplex.mkHomFromDouble_f₁
    (show (ComplexShape.up ℤ).Rel (-1) 0 from by decide) (by decide) _ _
    (naiveCotangentConormalMapOfSquare_comm.{v, u, w, z} J A B a A' B' a' f β hsq)
    (fun k _ ↦ naiveCotangentTensorMapOfSquare_comp_d.{v, u, w, z} J A B a A' B' a' f β hsq k)

end ComplexMap

/-! ### The change of base ring -/

section Base

variable (A B : Sheaf J CommRingCat.{w}) (a : A ⟶ B) (A' : Sheaf J CommRingCat.{w})
  (a' : A' ⟶ B) (f : A ⟶ A') (hf : a = f ≫ a')

omit [HasWeakSheafify J CommRingCat.{w}] in
/-- Restriction of scalars along the identity of `B` is the identity functor on sheaves of
`B`-modules. -/
theorem restrictScalars_underlyingRingHomOfSite_id :
    _root_.SheafOfModules.restrictScalars.{max w u v z} (underlyingRingHomOfSite (𝟙 B)) =
      𝟭 (_root_.SheafOfModules.{max w u v z} (Stacks.SheafOfModules.Tensor.ringSheaf B)) :=
  rfl

omit [HasWeakSheafify J CommRingCat.{w}]
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
include hf in
/-- A factorisation `a = f ≫ a'` of `a : A ⟶ B` through `a' : A' ⟶ B` is a commutative square
of sheaves of rings whose right-hand vertical morphism is the identity of `B`. -/
theorem comp_id_eq_comp_of_fac : a ≫ 𝟙 B = f ≫ a' :=
  (Category.comp_id a).trans hf

include hf in
/-- The map `I/I² ⟶ I'/(I')²` of the conormal sheaves of the canonical presentations
`A[B] ⟶ B` and `A'[B] ⟶ B`, attached to a factorisation `a = f ≫ a'`. -/
noncomputable abbrev naiveCotangentConormalMapOfBase :
    (canonicalConormalSequence.{v, u, w, z} J A B a).X₁ ⟶
      (canonicalConormalSequence.{v, u, w, z} J A' B a').X₁ :=
  naiveCotangentConormalMapOfSquare.{v, u, w, z} J A B a A' B a' f (𝟙 B)
    (comp_id_eq_comp_of_fac J A B a A' a' f hf)

include hf in
/-- The map `B ⊗_{A[B]} Ω_{A[B]/A} ⟶ B ⊗_{A'[B]} Ω_{A'[B]/A'}` attached to a factorisation
`a = f ≫ a'`. -/
noncomputable abbrev naiveCotangentTensorMapOfBase :
    (canonicalConormalSequence.{v, u, w, z} J A B a).X₂ ⟶
      (canonicalConormalSequence.{v, u, w, z} J A' B a').X₂ :=
  naiveCotangentTensorMapOfSquare.{v, u, w, z} J A B a A' B a' f (𝟙 B)
    (comp_id_eq_comp_of_fac J A B a A' a' f hf)

include hf in
/-- The canonical `B`-linear chain map `NL_{B/A} ⟶ NL_{B/A'}` attached to a factorisation
`a = f ≫ a'` of the structure morphism of `B`: the change of base ring of the naive cotangent
complex. Both source and target are complexes of sheaves of `B`-modules. -/
noncomputable def naiveCotangentComplexMapOfBase :
    naiveCotangentComplex.{v, u, w, z} J A B a ⟶
      naiveCotangentComplex.{v, u, w, z} J A' B a' :=
  naiveCotangentComplexMapOfSquare.{v, u, w, z} J A B a A' B a' f (𝟙 B)
    (comp_id_eq_comp_of_fac J A B a A' a' f hf)

include hf in
/-- In degree `-1` the change of base ring is the map of conormal sheaves. -/
theorem naiveCotangentComplexMapOfBase_f_negOne :
    (naiveCotangentComplexMapOfBase.{v, u, w, z} J A B a A' a' f hf).f (-1) =
      eqToHom (naiveCotangentComplex_X_negOne.{v, u, w, z} J A B a) ≫
        naiveCotangentConormalMapOfBase.{v, u, w, z} J A B a A' a' f hf ≫
        eqToHom (naiveCotangentComplex_X_negOne.{v, u, w, z} J A' B a').symm :=
  naiveCotangentComplexMapOfSquare_f_negOne.{v, u, w, z} J A B a A' B a' f (𝟙 B)
    (comp_id_eq_comp_of_fac J A B a A' a' f hf)

include hf in
/-- In degree `0` the change of base ring is the map on the scalar extensions of the
differentials. -/
theorem naiveCotangentComplexMapOfBase_f_zero :
    (naiveCotangentComplexMapOfBase.{v, u, w, z} J A B a A' a' f hf).f 0 =
      eqToHom (naiveCotangentComplex_X_zero.{v, u, w, z} J A B a) ≫
        naiveCotangentTensorMapOfBase.{v, u, w, z} J A B a A' a' f hf ≫
        eqToHom (naiveCotangentComplex_X_zero.{v, u, w, z} J A' B a').symm :=
  naiveCotangentComplexMapOfSquare_f_zero.{v, u, w, z} J A B a A' B a' f (𝟙 B)
    (comp_id_eq_comp_of_fac J A B a A' a' f hf)

end Base

/-! ### Composition of the morphisms of free algebra sheaves -/

section FreeAlgebraComp

variable (A A' A'' : Sheaf J CommRingCat.{w}) (E E' E'' : Functor Cᵒᵖ (Type w))
  (f : A ⟶ A') (f' : A' ⟶ A'') (h : E ⟶ E') (h' : E' ⟶ E'')

omit [HasWeakSheafify J CommRingCat.{w}]
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- Whiskering turns a composite of morphisms of sheaves of commutative rings into the composite
of the underlying morphisms of presheaves of sets. -/
private theorem whiskerRight_map_comp {S T U : Sheaf J CommRingCat.{w}} (g₁ : S ⟶ T)
    (g₂ : T ⟶ U) :
    Functor.whiskerRight ((sheafToPresheaf J CommRingCat.{w}).map (g₁ ≫ g₂))
        (forget CommRingCat.{w}) =
      Functor.whiskerRight ((sheafToPresheaf J CommRingCat.{w}).map g₁)
          (forget CommRingCat.{w}) ≫
        Functor.whiskerRight ((sheafToPresheaf J CommRingCat.{w}).map g₂)
          (forget CommRingCat.{w}) := by
  rw [Functor.map_comp, Functor.whiskerRight_comp]

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- The morphisms `A[E] ⟶ A'[E'] ⟶ A''[E'']` of free algebra sheaves attached to two squares of
coefficients and variables compose to the one attached to the outer rectangle. -/
theorem freeAlgebraMapOfSquare_comp :
    freeAlgebraMapOfSquare J A A' E E' f h ≫ freeAlgebraMapOfSquare J A' A'' E' E'' f' h' =
      freeAlgebraMapOfSquare J A A'' E E'' (f ≫ f') (h ≫ h') := by
  refine Stacks.Sites.FreeAlgebra.freeAlgebraSheaf_hom_ext J A _ E ?_ ?_
  · rw [← Category.assoc, freeAlgebraSheafCoefficientMap_comp_freeAlgebraMapOfSquare,
      Category.assoc, freeAlgebraSheafCoefficientMap_comp_freeAlgebraMapOfSquare,
      freeAlgebraSheafCoefficientMap_comp_freeAlgebraMapOfSquare, Category.assoc]
  · rw [whiskerRight_map_comp, ← Category.assoc,
      freeAlgebraSheafVariable_comp_freeAlgebraMapOfSquare, Category.assoc,
      freeAlgebraSheafVariable_comp_freeAlgebraMapOfSquare,
      freeAlgebraSheafVariable_comp_freeAlgebraMapOfSquare, Category.assoc]

end FreeAlgebraComp

section PresentationComp

variable (A A' A'' B B' B'' : Sheaf J CommRingCat.{w}) (f : A ⟶ A') (f' : A' ⟶ A'')
  (β : B ⟶ B') (β' : B' ⟶ B'')

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- The morphisms `A[B] ⟶ A'[B'] ⟶ A''[B'']` attached to two commutative squares compose to the
one attached to the outer rectangle. -/
theorem canonicalFreeAlgebraMapOfSquare_comp :
    canonicalFreeAlgebraMapOfSquare J A A' B B' f β ≫
        canonicalFreeAlgebraMapOfSquare J A' A'' B' B'' f' β' =
      canonicalFreeAlgebraMapOfSquare J A A'' B B'' (f ≫ f') (β ≫ β') := by
  refine (freeAlgebraMapOfSquare_comp J A A' A'' _ _ _ f f'
    (underlyingPresheafMap J B B' β) (underlyingPresheafMap J B' B'' β')).trans ?_
  exact congrArg
    (fun t : Stacks.Sites.FreeAlgebra.underlyingPresheaf J B ⟶
        Stacks.Sites.FreeAlgebra.underlyingPresheaf J B'' ↦
      freeAlgebraMapOfSquare J A A'' _ _ (f ≫ f') t)
    (whiskerRight_map_comp J β β').symm

end PresentationComp

/-! ### Composition of the chain maps -/

section ComplexMapComp

variable (A B : Sheaf J CommRingCat.{w}) (a : A ⟶ B)
  (A' B' : Sheaf J CommRingCat.{w}) (a' : A' ⟶ B') (f : A ⟶ A') (β : B ⟶ B')
  (hsq : a ≫ β = f ≫ a')
  (A'' B'' : Sheaf J CommRingCat.{w}) (a'' : A'' ⟶ B'') (f' : A' ⟶ A'') (β' : B' ⟶ B'')
  (hsq' : a' ≫ β' = f' ≫ a'')

include hsq hsq' in
/-- The maps of conormal sheaves attached to two commutative squares compose to the one attached
to the outer rectangle. -/
theorem naiveCotangentConormalMapOfSquare_comp :
    naiveCotangentConormalMapOfSquare.{v, u, w, z} J A B a A' B' a' f β hsq ≫
        (_root_.SheafOfModules.restrictScalars.{max w u v z}
          (underlyingRingHomOfSite β)).map
          (naiveCotangentConormalMapOfSquare.{v, u, w, z} J A' B' a' A'' B'' a'' f' β' hsq') =
      naiveCotangentConormalMapOfSquare.{v, u, w, z} J A B a A'' B'' a'' (f ≫ f') (β ≫ β')
        (square_comp hsq hsq') := by
  refine Eq.trans (Stacks.Sites.Conormal.conormalSheafMapOfSquare_comp.{v, u, w, z} J _ _ _
    B B' B''
    (Stacks.Sites.FreeAlgebra.canonicalPresentation J A B a)
    (Stacks.Sites.FreeAlgebra.canonicalPresentation J A' B' a')
    (Stacks.Sites.FreeAlgebra.canonicalPresentation J A'' B'' a'')
    (canonicalFreeAlgebraMapOfSquare J A A' B B' f β)
    (canonicalFreeAlgebraMapOfSquare J A' A'' B' B'' f' β') β β'
    (freeAlgebraMapOfSquare_comp_canonicalPresentation J A A' B B' a a' f β hsq)
    (freeAlgebraMapOfSquare_comp_canonicalPresentation J A' A'' B' B'' a' a'' f' β' hsq')) ?_
  exact Stacks.Sites.Conormal.conormalSheafMapOfSquare_congr.{v, u, w, z} J _ _ B B''
    (Stacks.Sites.FreeAlgebra.canonicalPresentation J A B a)
    (Stacks.Sites.FreeAlgebra.canonicalPresentation J A'' B'' a'') (β ≫ β') _ _
    (canonicalFreeAlgebraMapOfSquare_comp J A A' A'' B B' B'' f f' β β')

include hsq hsq' in
/-- The maps on the scalar extensions of the differentials attached to two commutative squares
compose to the one attached to the outer rectangle. -/
theorem naiveCotangentTensorMapOfSquare_comp :
    naiveCotangentTensorMapOfSquare.{v, u, w, z} J A B a A' B' a' f β hsq ≫
        (_root_.SheafOfModules.restrictScalars.{max w u v z}
          (underlyingRingHomOfSite β)).map
          (naiveCotangentTensorMapOfSquare.{v, u, w, z} J A' B' a' A'' B'' a'' f' β' hsq') =
      naiveCotangentTensorMapOfSquare.{v, u, w, z} J A B a A'' B'' a'' (f ≫ f') (β ≫ β')
        (square_comp hsq hsq') := by
  refine Eq.trans (Stacks.Sites.Conormal.tensorSheafMapOfSquare_comp.{v, u, w, z} J A A' A''
    _ _ _ B B' B''
    (Stacks.Sites.FreeAlgebra.freeAlgebraSheafCoefficientMap J A _)
    (Stacks.Sites.FreeAlgebra.freeAlgebraSheafCoefficientMap J A' _)
    (Stacks.Sites.FreeAlgebra.freeAlgebraSheafCoefficientMap J A'' _)
    (Stacks.Sites.FreeAlgebra.canonicalPresentation J A B a)
    (Stacks.Sites.FreeAlgebra.canonicalPresentation J A' B' a')
    (Stacks.Sites.FreeAlgebra.canonicalPresentation J A'' B'' a'')
    (canonicalFreeAlgebraMapOfSquare J A A' B B' f β)
    (canonicalFreeAlgebraMapOfSquare J A' A'' B' B'' f' β') β β' f f'
    (freeAlgebraMapOfSquare_comp_canonicalPresentation J A A' B B' a a' f β hsq)
    (freeAlgebraMapOfSquare_comp_canonicalPresentation J A' A'' B' B'' a' a'' f' β' hsq')
    (freeAlgebraSheafCoefficientMap_comp_freeAlgebraMapOfSquare J A A' _ _ f
      (underlyingPresheafMap J B B' β)).symm
    (freeAlgebraSheafCoefficientMap_comp_freeAlgebraMapOfSquare J A' A'' _ _ f'
      (underlyingPresheafMap J B' B'' β')).symm) ?_
  exact Stacks.Sites.Conormal.tensorSheafMapOfSquare_congr.{v, u, w, z} J A A'' _ _ B B''
    (Stacks.Sites.FreeAlgebra.freeAlgebraSheafCoefficientMap J A _)
    (Stacks.Sites.FreeAlgebra.freeAlgebraSheafCoefficientMap J A'' _)
    (Stacks.Sites.FreeAlgebra.canonicalPresentation J A B a)
    (Stacks.Sites.FreeAlgebra.canonicalPresentation J A'' B'' a'') (β ≫ β') _ _ _ _
    (canonicalFreeAlgebraMapOfSquare_comp J A A' A'' B B' B'' f f' β β') rfl

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- A morphism out of the naive cotangent complex is determined by its components in degrees
`-1` and `0`, the only degrees where `NL_{B/A}` is nonzero. -/
private theorem naiveCotangentComplex_from_hom_ext
    {K : CochainComplex
      (_root_.SheafOfModules.{max w u v z} (Stacks.SheafOfModules.Tensor.ringSheaf B)) ℤ}
    {u₁ u₂ : naiveCotangentComplex.{v, u, w, z} J A B a ⟶ K}
    (h₀ : u₁.f (-1) = u₂.f (-1)) (h₁ : u₁.f 0 = u₂.f 0) : u₁ = u₂ := by
  have : HasZeroObject
      (_root_.SheafOfModules.{max w u v z} (Stacks.SheafOfModules.Tensor.ringSheaf B)) :=
    hasZeroObject_of_hasTerminal_object
  exact HomologicalComplex.from_double_hom_ext
    (hi₀₁ := show (ComplexShape.up ℤ).Rel (-1) 0 from by decide) h₀ h₁

include hsq hsq' in
/-- **Stacks 08TX.** The canonical chain map attached to a commutative square of sheaves of
rings is compatible with compositions: given a commutative diagram
```
B ──β──▸ B' ──β'──▸ B''
▲         ▲          ▲
a         a'         a''
│         │          │
A ──f──▸ A' ──f'──▸ A''
```
the composition `NL_{B/A} ⟶ NL_{B'/A'} ⟶ NL_{B''/A''}` is the map attached to the outer
rectangle.  The target of the composite is the iterated restriction of scalars along `β` and
`β'`, which is the restriction of scalars along `β ≫ β'`. -/
@[stacks 08TX "compatibility of the canonical map of complexes with compositions"]
theorem naiveCotangentComplexMapOfSquare_comp :
    naiveCotangentComplexMapOfSquare.{v, u, w, z} J A B a A' B' a' f β hsq ≫
        ((_root_.SheafOfModules.restrictScalars.{max w u v z}
            (underlyingRingHomOfSite β)).mapHomologicalComplex (ComplexShape.up ℤ)).map
          (naiveCotangentComplexMapOfSquare.{v, u, w, z} J A' B' a' A'' B'' a'' f' β' hsq') =
      naiveCotangentComplexMapOfSquare.{v, u, w, z} J A B a A'' B'' a'' (f ≫ f') (β ≫ β')
        (square_comp hsq hsq') := by
  refine naiveCotangentComplex_from_hom_ext.{v, u, w, z} J A B a ?_ ?_
  · simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
      naiveCotangentComplexMapOfSquare_f_negOne, Functor.map_comp, Category.assoc,
      eqToHom_map_comp_assoc, eqToHom_refl, CategoryTheory.Functor.map_id, Category.id_comp]
    rw [← Category.assoc
        (naiveCotangentConormalMapOfSquare.{v, u, w, z} J A B a A' B' a' f β hsq),
      naiveCotangentConormalMapOfSquare_comp.{v, u, w, z} J A B a A' B' a' f β hsq
        A'' B'' a'' f' β' hsq']
    rfl
  · simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
      naiveCotangentComplexMapOfSquare_f_zero, Functor.map_comp, Category.assoc,
      eqToHom_map_comp_assoc, eqToHom_refl, CategoryTheory.Functor.map_id, Category.id_comp]
    rw [← Category.assoc
        (naiveCotangentTensorMapOfSquare.{v, u, w, z} J A B a A' B' a' f β hsq),
      naiveCotangentTensorMapOfSquare_comp.{v, u, w, z} J A B a A' B' a' f β hsq
        A'' B'' a'' f' β' hsq']
    rfl

end ComplexMapComp

end Stacks.SheafOfModules
