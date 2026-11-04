module

public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalAlgebraSquareMapCartesian
public import StacksFrontier.AlgebraicGeometry.Spaces.KernelIdealSheafCartesianSquare
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothAtlas
public import StacksFrontier.AlgebraicGeometry.ProjTwistGradedAlgebra.Basic

/-!
# The canonical map of conormal algebras of a square of immersions

Let
```
Z --i--→ X
|        |
f        g
↓        ↓
Z' -i'-→ X'
```
be a commutative square of algebraic spaces over a scheme `S` contained in a big fppf site `B`
with `i` and `i'` immersions.  [Stacks Project, Tag 09RS] asserts a canonical homomorphism of
sheaves of graded `𝒪_Z`-algebras

`f^*𝒞_{Z'/X',*} ⟶ 𝒞_{Z/X,*}`,

where, as in [Stacks Project, Tag 09RN], the conormal algebra of an immersion `i : Z ⟶ X` is the
conormal algebra of the closed immersion `i₀ : Z ⟶ X ∖ ∂Z` through which it factors,
`AlgebraicGeometry.Space.conormalAlgebraOfImmersion`.

`AlgebraicGeometry.Space.conormalAlgebraSquareMap` is the canonical map for the conormal algebra
`AlgebraicGeometry.Space.conormalAlgebra` of the morphisms `i` and `i'` themselves, that is with
the ambient spaces `X` and `X'` rather than `X ∖ ∂Z` and `X' ∖ ∂Z'`.  The two conormal algebras
of an immersion are canonically isomorphic, and this file proves it and carries the canonical
map over.

## The comparison of the two conormal algebras of an immersion

For an immersion `i'` with closed factorisation `i'₀ : Z' ⟶ X' ∖ ∂Z'` and open inclusion
`ι' : X' ∖ ∂Z' ⟶ X'`, the square

```
Z' --i'₀--→ X' ∖ ∂Z'
|𝟙           |ι'
↓            ↓
Z' ---i'---→ X'
```

commutes and is cartesian, because `ι'` is a monomorphism; `i'` is an immersion and `ι'` is an
open immersion, hence étale, hence flat.  So the canonical map of Stacks 09RS for this square,
`𝟙^*𝒞_{Z'/X',*} ⟶ 𝒞_{Z'/(X' ∖ ∂Z'),*}`, is an isomorphism in every degree by the flat clause of
[Stacks Project, Tag 09RT],
`AlgebraicGeometry.Space.isIso_conormalAlgebraSquareMap_app_of_isPullback_of_isFlat`, and being
a homomorphism of sheaves of graded algebras it is an isomorphism of sheaves of graded algebras
(`AlgebraicGeometry.Space.conormalAlgebraOfImmersionIso`).

## The canonical map

For a square of immersions the canonical map of Stacks 09RS on the conormal algebras of Stacks
09RN is then

`f^*𝒞_{Z'/(X' ∖ ∂Z'),*} ≅ f^*𝟙^*𝒞_{Z'/X',*} ≅ f^*𝒞_{Z'/X',*} ⟶ 𝒞_{Z/(X ∖ ∂Z),*}`,

the inverse image along `f` of the comparison above, the composition comparison `f^*𝟙^* ≅ f^*`,
and the canonical map `AlgebraicGeometry.Space.conormalAlgebraSquareMap` of the square

```
Z --i₀--→ X ∖ ∂Z
|f          |ι ≫ g
↓           ↓
Z' --i'--→ X'
```

which commutes because `i₀ ≫ ι = i`.

## Main definitions

* `AlgebraicGeometry.Space.conormalAlgebraOfImmersionIso`: the isomorphism
  `𝟙^*𝒞_{Z/X,*} ≅ 𝒞_{Z/(X ∖ ∂Z),*}` of sheaves of graded algebras, for an immersion.
* `AlgebraicGeometry.Space.conormalAlgebraOfImmersionSquareMap`: **the canonical map
  `f^*𝒞_{Z'/X',*} ⟶ 𝒞_{Z/X,*}` of [Stacks Project, Tag 09RS] for a square of immersions, on
  the conormal algebras of immersions of [Stacks Project, Tag 09RN].**

* `AlgebraicGeometry.Space.conormalAlgebraOfImmersionSquareUnitalHom`: the same map as a unital
  homomorphism of sheaves of graded algebras.

## Main results

* `AlgebraicGeometry.Space.isIso_conormalAlgebraOfImmersionComparison_app`: the comparison of the
  two conormal algebras of an immersion is an isomorphism in every degree.
* `AlgebraicGeometry.Space.conormalAlgebraOfImmersionSquareMap_map_one`: the canonical map
  preserves the unit.

## References

* [Stacks Project, Tag 09RS](https://stacks.math.columbia.edu/tag/09RS)
* [Stacks Project, Tag 09RN](https://stacks.math.columbia.edu/tag/09RN)
* [Stacks Project, Tag 09RT](https://stacks.math.columbia.edu/tag/09RT)
* [Stacks Project, Tag 04CE](https://stacks.math.columbia.edu/tag/04CE)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open Stacks.Sheaves.GradedAlgebraEssentiallySmall (gradedPull)

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section Immersion

variable {Z₀ X₀ Z₀' X₀' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
  (hZ : IsAlgebraicSpace B S hS Z₀) (hX : IsAlgebraicSpace B S hS X₀)
  (hZ' : IsAlgebraicSpace B S hS Z₀') (hX' : IsAlgebraicSpace B S hS X₀')

/-- The algebraic space `Z = (Z₀, hZ)`. -/
local notation "𝒵" => (ObjectProperty.FullSubcategory.mk
  (P := fun F => IsAlgebraicSpace B S hS F) Z₀ hZ : AlgebraicSpaces B S hS)
/-- The algebraic space `X = (X₀, hX)`. -/
local notation "𝒳" => (ObjectProperty.FullSubcategory.mk
  (P := fun F => IsAlgebraicSpace B S hS F) X₀ hX : AlgebraicSpaces B S hS)
/-- The algebraic space `Z' = (Z₀', hZ')`. -/
local notation "𝒵'" => (ObjectProperty.FullSubcategory.mk
  (P := fun F => IsAlgebraicSpace B S hS F) Z₀' hZ' : AlgebraicSpaces B S hS)
/-- The algebraic space `X' = (X₀', hX')`. -/
local notation "𝒳'" => (ObjectProperty.FullSubcategory.mk
  (P := fun F => IsAlgebraicSpace B S hS F) X₀' hX' : AlgebraicSpaces B S hS)

/-- The closed factorisation of an immersion followed by the inclusion of the complement of the
boundary is a cartesian square over the immersion, with the identity on the left: the inclusion
is a monomorphism. -/
theorem isPullback_immersionClosedFactorization (i : 𝒵 ⟶ 𝒳)
    (hi : IsImmersion B S hS i.hom) :
    IsPullback (immersionClosedFactorization B S hS hX hZ i.hom hi) (𝟙 𝒵)
      (immersionAmbientι B S hS i hi) i :=
  IsPullback.of_vert_isIso_mono
    ⟨(immersionClosedFactorization_comp_immersionAmbientι B S hS i hi).trans
      (Category.id_comp i).symm⟩

/-- **The comparison `𝟙^*𝒞_{Z/X,*} ⟶ 𝒞_{Z/(X ∖ ∂Z),*}` of the two conormal algebras of an
immersion**: the canonical map of Stacks 09RS of the cartesian square of
`AlgebraicGeometry.Space.isPullback_immersionClosedFactorization`.  Its target is the conormal
algebra `AlgebraicGeometry.Space.conormalAlgebraOfImmersion` of the immersion of
[Stacks Project, Tag 09RN]. -/
noncomputable def conormalAlgebraOfImmersionComparison (i : 𝒵 ⟶ 𝒳)
    (hi : IsImmersion B S hS i.hom) :
    (gradedPull (X := smallEtaleRingedTopos B S hS 𝒵) (Y := smallEtaleRingedTopos B S hS 𝒵)
        (smallEtaleRingedToposHom B S hS (𝟙 𝒵))).obj (conormalAlgebra B S hS i) ⟶
      conormalAlgebraOfImmersion B S hS hX hZ i.hom hi :=
  conormalAlgebraSquareMap B S hS (immersionClosedFactorization B S hS hX hZ i.hom hi) i
    (𝟙 𝒵) (immersionAmbientι B S hS i hi)
    (isPullback_immersionClosedFactorization B S hS hZ hX i hi).w

/-- **The comparison of the two conormal algebras of an immersion is an isomorphism in every
degree**, by the flat clause of [Stacks Project, Tag 09RT] for the cartesian square of
`AlgebraicGeometry.Space.isPullback_immersionClosedFactorization`, whose right edge is an open
immersion, hence étale, hence flat. -/
theorem isIso_conormalAlgebraOfImmersionComparison_app (i : 𝒵 ⟶ 𝒳)
    (hi : IsImmersion B S hS i.hom) (n : ℤ) :
    IsIso ((conormalAlgebraOfImmersionComparison B S hS hZ hX i hi).app n) :=
  isIso_conormalAlgebraSquareMap_app_of_isPullback_of_isFlat B S hS
    (isPullback_immersionClosedFactorization B S hS hZ hX i hi) hi
    (isFlat_of_isEtale B S hS (isEtale_immersionAmbientι B S hS i hi)) n

/-- **The two conormal algebras of an immersion are isomorphic.**  For an immersion `i : Z ⟶ X`
with closed factorisation `i₀ : Z ⟶ X ∖ ∂Z`, the comparison
`AlgebraicGeometry.Space.conormalAlgebraOfImmersionComparison` is an isomorphism

`𝟙^*𝒞_{Z/X,*} ≅ 𝒞_{Z/(X ∖ ∂Z),*}`

of sheaves of graded `𝒪_Z`-algebras between the conormal algebra
`AlgebraicGeometry.Space.conormalAlgebra` of the morphism `i` and the conormal algebra
`AlgebraicGeometry.Space.conormalAlgebraOfImmersion` of the immersion `i` of
[Stacks Project, Tag 09RN]: it is a homomorphism of sheaves of graded algebras which is an
isomorphism in every degree, by
`AlgebraicGeometry.Space.isIso_conormalAlgebraOfImmersionComparison_app`. -/
noncomputable def conormalAlgebraOfImmersionIso (i : 𝒵 ⟶ 𝒳)
    (hi : IsImmersion B S hS i.hom) :
    (gradedPull (X := smallEtaleRingedTopos B S hS 𝒵) (Y := smallEtaleRingedTopos B S hS 𝒵)
        (smallEtaleRingedToposHom B S hS (𝟙 𝒵))).obj (conormalAlgebra B S hS i) ≅
      conormalAlgebraOfImmersion B S hS hX hZ i.hom hi :=
  SheafOfModules.GradedAlgebra.isoOfIsIsoApp
    (conormalAlgebraOfImmersionComparison B S hS hZ hX i hi)
    (isIso_conormalAlgebraOfImmersionComparison_app B S hS hZ hX i hi)

/-- The forward map of `AlgebraicGeometry.Space.conormalAlgebraOfImmersionIso` is the comparison
`AlgebraicGeometry.Space.conormalAlgebraOfImmersionComparison`. -/
theorem conormalAlgebraOfImmersionIso_hom (i : 𝒵 ⟶ 𝒳) (hi : IsImmersion B S hS i.hom) :
    (conormalAlgebraOfImmersionIso B S hS hZ hX i hi).hom =
      conormalAlgebraOfImmersionComparison B S hS hZ hX i hi :=
  SheafOfModules.GradedAlgebra.Hom.ext fun _ => rfl

/-- The square of `AlgebraicGeometry.Space.conormalAlgebraOfImmersionSquareMap`: the closed
factorisation of `i` followed by the inclusion of `X ∖ ∂Z` and `g` is `f ≫ i'`. -/
theorem immersionClosedFactorization_comp_comp (i : 𝒵 ⟶ 𝒳) (i' : 𝒵' ⟶ 𝒳')
    (f : 𝒵 ⟶ 𝒵') (g : 𝒳 ⟶ 𝒳') (hsq : i ≫ g = f ≫ i') (hi : IsImmersion B S hS i.hom) :
    immersionClosedFactorization B S hS hX hZ i.hom hi ≫ immersionAmbientι B S hS i hi ≫ g =
      f ≫ i' := by
  rw [← Category.assoc, immersionClosedFactorization_comp_immersionAmbientι, hsq]

/-- **[Stacks Project, Tag 09RS] for a square of immersions, on the conormal algebras of
[Stacks Project, Tag 09RN].**  Let

```
Z --i--→ X
|        |
f        g
↓        ↓
Z' -i'-→ X'
```

be a commutative square of algebraic spaces over `S` with `i` and `i'` immersions.  There is a
canonical homomorphism of sheaves of graded `𝒪_Z`-algebras

`f^*𝒞_{Z'/X',*} ⟶ 𝒞_{Z/X,*}`,

where `𝒞_{Z/X,*}` is the conormal algebra of the immersion `i`, that is of its closed
factorisation `i₀ : Z ⟶ X ∖ ∂Z` (`AlgebraicGeometry.Space.conormalAlgebraOfImmersion`), and
likewise for `i'`.

It is the inverse image along `f` of the inverse of the isomorphism
`AlgebraicGeometry.Space.conormalAlgebraOfImmersionIso` for `i'`, then the composition
comparison `f^*𝟙^* ≅ f^*`, then the canonical map
`AlgebraicGeometry.Space.conormalAlgebraSquareMap` of the commutative square with edges `i₀`,
`ι ≫ g`, `f` and `i'`; the last is built from `g^♯` exactly as in the source's proof. -/
@[stacks 09RS "the canonical map f^*𝒞_{Z'/X',*} ⟶ 𝒞_{Z/X,*} for immersions i, i', on the \
conormal algebras of immersions of Tag 09RN"]
noncomputable def conormalAlgebraOfImmersionSquareMap (i : 𝒵 ⟶ 𝒳) (i' : 𝒵' ⟶ 𝒳')
    (f : 𝒵 ⟶ 𝒵') (g : 𝒳 ⟶ 𝒳') (hsq : i ≫ g = f ≫ i') (hi : IsImmersion B S hS i.hom)
    (hi' : IsImmersion B S hS i'.hom) :
    (gradedPull (X := smallEtaleRingedTopos B S hS 𝒵) (Y := smallEtaleRingedTopos B S hS 𝒵')
        (smallEtaleRingedToposHom B S hS f)).obj
        (conormalAlgebraOfImmersion B S hS hX' hZ' i'.hom hi') ⟶
      conormalAlgebraOfImmersion B S hS hX hZ i.hom hi :=
  (gradedPull (X := smallEtaleRingedTopos B S hS 𝒵) (Y := smallEtaleRingedTopos B S hS 𝒵')
      (smallEtaleRingedToposHom B S hS f)).map
      (conormalAlgebraOfImmersionIso B S hS hZ' hX' i' hi').inv ≫
    ((gradedAlgebraPullbackCompIsoOfEq B S hS f (𝟙 𝒵') f (Category.comp_id f).symm).app
      (conormalAlgebra B S hS i')).inv ≫
    conormalAlgebraSquareMap B S hS (immersionClosedFactorization B S hS hX hZ i.hom hi) i' f
      (immersionAmbientι B S hS i hi ≫ g)
      (immersionClosedFactorization_comp_comp B S hS hZ hX hZ' hX' i i' f g hsq hi)

/-- The canonical map of Stacks 09RS for a square of immersions, as a composite of its three
factors. -/
theorem conormalAlgebraOfImmersionSquareMap_eq (i : 𝒵 ⟶ 𝒳) (i' : 𝒵' ⟶ 𝒳')
    (f : 𝒵 ⟶ 𝒵') (g : 𝒳 ⟶ 𝒳') (hsq : i ≫ g = f ≫ i') (hi : IsImmersion B S hS i.hom)
    (hi' : IsImmersion B S hS i'.hom) :
    conormalAlgebraOfImmersionSquareMap B S hS hZ hX hZ' hX' i i' f g hsq hi hi' =
      (gradedPull (X := smallEtaleRingedTopos B S hS 𝒵) (Y := smallEtaleRingedTopos B S hS 𝒵')
          (smallEtaleRingedToposHom B S hS f)).map
          (conormalAlgebraOfImmersionIso B S hS hZ' hX' i' hi').inv ≫
        ((gradedAlgebraPullbackCompIsoOfEq B S hS f (𝟙 𝒵') f (Category.comp_id f).symm).app
          (conormalAlgebra B S hS i')).inv ≫
        conormalAlgebraSquareMap B S hS (immersionClosedFactorization B S hS hX hZ i.hom hi) i' f
          (immersionAmbientι B S hS i hi ≫ g)
          (immersionClosedFactorization_comp_comp B S hS hZ hX hZ' hX' i i' f g hsq hi) :=
  rfl

/-- The first factor of `AlgebraicGeometry.Space.conormalAlgebraOfImmersionSquareMap`, the
inverse image along `f` of the inverse of `AlgebraicGeometry.Space.conormalAlgebraOfImmersionIso`,
preserves the unit. -/
theorem gradedPull_map_conormalAlgebraOfImmersionIso_inv_map_one (i' : 𝒵' ⟶ 𝒳') (f : 𝒵 ⟶ 𝒵')
    (hi' : IsImmersion B S hS i'.hom) (U : (SmallEtale B S hS Z₀)ᵒᵖ) :
    (((gradedPull (X := smallEtaleRingedTopos B S hS 𝒵)
          (Y := smallEtaleRingedTopos B S hS 𝒵') (smallEtaleRingedToposHom B S hS f)).map
        (conormalAlgebraOfImmersionIso B S hS hZ' hX' i' hi').inv).app 0).val.app U
        (((gradedPull (X := smallEtaleRingedTopos B S hS 𝒵)
          (Y := smallEtaleRingedTopos B S hS 𝒵') (smallEtaleRingedToposHom B S hS f)).obj
            (conormalAlgebraOfImmersion B S hS hX' hZ' i'.hom hi')).one.eval U) =
      ((gradedPull (X := smallEtaleRingedTopos B S hS 𝒵)
          (Y := smallEtaleRingedTopos B S hS 𝒵') (smallEtaleRingedToposHom B S hS f)).obj
          ((gradedPull (X := smallEtaleRingedTopos B S hS 𝒵')
            (Y := smallEtaleRingedTopos B S hS 𝒵') (smallEtaleRingedToposHom B S hS (𝟙 𝒵'))).obj
              (conormalAlgebra B S hS i'))).one.eval U :=
  Stacks.Sheaves.GradedAlgebraPullback.toposPullbackGradedAlgebraFunctor_map_one
    (smallEtaleRingedToposHom B S hS f).toRingedToposModulesHom
    (conormalAlgebraOfImmersionIso B S hS hZ' hX' i' hi').inv
    (SheafOfModules.GradedAlgebra.iso_hom_map_one
      (conormalAlgebraOfImmersionIso B S hS hZ' hX' i' hi').symm) U

/-- The canonical map of the square of the closed factorisation of `i`, which is the last factor
of `AlgebraicGeometry.Space.conormalAlgebraOfImmersionSquareMap`, preserves the unit: this is
`AlgebraicGeometry.Space.conormalAlgebraSquareMap_map_one` at that square. -/
theorem conormalAlgebraSquareMap_immersionClosedFactorization_map_one (i : 𝒵 ⟶ 𝒳) (i' : 𝒵' ⟶ 𝒳')
    (f : 𝒵 ⟶ 𝒵') (g : 𝒳 ⟶ 𝒳') (hsq : i ≫ g = f ≫ i') (hi : IsImmersion B S hS i.hom)
    (U : (SmallEtale B S hS Z₀)ᵒᵖ) :
    ((conormalAlgebraSquareMap B S hS (immersionClosedFactorization B S hS hX hZ i.hom hi) i' f
          (immersionAmbientι B S hS i hi ≫ g)
          (immersionClosedFactorization_comp_comp B S hS hZ hX hZ' hX' i i' f g hsq hi)).app
          0).val.app U
        (((gradedPull (X := smallEtaleRingedTopos B S hS 𝒵)
          (Y := smallEtaleRingedTopos B S hS 𝒵') (smallEtaleRingedToposHom B S hS f)).obj
            (conormalAlgebra B S hS i')).one.eval U) =
      (conormalAlgebra B S hS (immersionClosedFactorization B S hS hX hZ i.hom hi)).one.eval U :=
  conormalAlgebraSquareMap_map_one B S hS
      (immersionClosedFactorization B S hS hX hZ i.hom hi) i' f
      (immersionAmbientι B S hS i hi ≫ g)
      (immersionClosedFactorization_comp_comp B S hS hZ hX hZ' hX' i i' f g hsq hi) U

/-- The composition comparison `f^*𝟙^* ≅ f^*`, the middle factor of
`AlgebraicGeometry.Space.conormalAlgebraOfImmersionSquareMap`, preserves the unit, being an
isomorphism. -/
theorem gradedAlgebraPullbackCompIsoOfEq_comp_id_inv_map_one (i' : 𝒵' ⟶ 𝒳') (f : 𝒵 ⟶ 𝒵')
    (U : (SmallEtale B S hS Z₀)ᵒᵖ) :
    ((((gradedAlgebraPullbackCompIsoOfEq B S hS f (𝟙 𝒵') f (Category.comp_id f).symm).app
          (conormalAlgebra B S hS i')).inv).app 0).val.app U
        (((gradedPull (X := smallEtaleRingedTopos B S hS 𝒵)
          (Y := smallEtaleRingedTopos B S hS 𝒵') (smallEtaleRingedToposHom B S hS f)).obj
            ((gradedPull (X := smallEtaleRingedTopos B S hS 𝒵')
              (Y := smallEtaleRingedTopos B S hS 𝒵') (smallEtaleRingedToposHom B S hS (𝟙 𝒵'))).obj
                (conormalAlgebra B S hS i'))).one.eval U) =
      ((gradedPull (X := smallEtaleRingedTopos B S hS 𝒵)
          (Y := smallEtaleRingedTopos B S hS 𝒵') (smallEtaleRingedToposHom B S hS f)).obj
            (conormalAlgebra B S hS i')).one.eval U :=
  SheafOfModules.GradedAlgebra.iso_hom_map_one
      ((gradedAlgebraPullbackCompIsoOfEq B S hS f (𝟙 𝒵') f (Category.comp_id f).symm).app
        (conormalAlgebra B S hS i')).symm U

/-- **The canonical map of Stacks 09RS for a square of immersions preserves the unit**, so it is
a homomorphism of sheaves of graded `𝒪_Z`-algebras in the unital sense of the source.  Each of
its three factors does: the inverse image along `f` of the inverse of an isomorphism
(`AlgebraicGeometry.Space.gradedPull_map_conormalAlgebraOfImmersionIso_inv_map_one`), the
composition comparison
(`AlgebraicGeometry.Space.gradedAlgebraPullbackCompIsoOfEq_comp_id_inv_map_one`), and the
canonical map of the square of the closed factorisation
(`AlgebraicGeometry.Space.conormalAlgebraSquareMap_immersionClosedFactorization_map_one`). -/
theorem conormalAlgebraOfImmersionSquareMap_map_one (i : 𝒵 ⟶ 𝒳) (i' : 𝒵' ⟶ 𝒳')
    (f : 𝒵 ⟶ 𝒵') (g : 𝒳 ⟶ 𝒳') (hsq : i ≫ g = f ≫ i') (hi : IsImmersion B S hS i.hom)
    (hi' : IsImmersion B S hS i'.hom) (U : (SmallEtale B S hS Z₀)ᵒᵖ) :
    ((conormalAlgebraOfImmersionSquareMap B S hS hZ hX hZ' hX' i i' f g hsq hi hi').app 0).val.app
        U (((gradedPull (X := smallEtaleRingedTopos B S hS 𝒵)
          (Y := smallEtaleRingedTopos B S hS 𝒵') (smallEtaleRingedToposHom B S hS f)).obj
            (conormalAlgebraOfImmersion B S hS hX' hZ' i'.hom hi')).one.eval U) =
      (conormalAlgebraOfImmersion B S hS hX hZ i.hom hi).one.eval U := by
  refine (congrArg (fun m => (m.app 0).val.app U
    (((gradedPull (X := smallEtaleRingedTopos B S hS 𝒵)
          (Y := smallEtaleRingedTopos B S hS 𝒵') (smallEtaleRingedToposHom B S hS f)).obj
            (conormalAlgebraOfImmersion B S hS hX' hZ' i'.hom hi')).one.eval U))
    (conormalAlgebraOfImmersionSquareMap_eq B S hS hZ hX hZ' hX' i i' f g hsq hi hi')).trans ?_
  refine (SheafOfModules.GradedAlgebra.comp_app_zero_apply
    ((gradedPull (X := smallEtaleRingedTopos B S hS 𝒵)
          (Y := smallEtaleRingedTopos B S hS 𝒵') (smallEtaleRingedToposHom B S hS f)).map
      (conormalAlgebraOfImmersionIso B S hS hZ' hX' i' hi').inv) _ U _).trans ?_
  refine (SheafOfModules.GradedAlgebra.comp_app_zero_apply
    ((gradedAlgebraPullbackCompIsoOfEq B S hS f (𝟙 𝒵') f (Category.comp_id f).symm).app
          (conormalAlgebra B S hS i')).inv _ U _).trans ?_
  refine (congrArg (fun t => ((conormalAlgebraSquareMap B S hS
      (immersionClosedFactorization B S hS hX hZ i.hom hi) i' f
      (immersionAmbientι B S hS i hi ≫ g)
      (immersionClosedFactorization_comp_comp B S hS hZ hX hZ' hX' i i' f g hsq hi)).app
        0).val.app U (((((gradedAlgebraPullbackCompIsoOfEq B S hS f (𝟙 𝒵') f
          (Category.comp_id f).symm).app (conormalAlgebra B S hS i')).inv).app 0).val.app U t))
    (gradedPull_map_conormalAlgebraOfImmersionIso_inv_map_one B S hS hZ hZ' hX' i' f hi' U)).trans
    ?_
  refine (congrArg (fun t => ((conormalAlgebraSquareMap B S hS
      (immersionClosedFactorization B S hS hX hZ i.hom hi) i' f
      (immersionAmbientι B S hS i hi ≫ g)
      (immersionClosedFactorization_comp_comp B S hS hZ hX hZ' hX' i i' f g hsq hi)).app
        0).val.app U t)
    (gradedAlgebraPullbackCompIsoOfEq_comp_id_inv_map_one B S hS hZ hZ' hX' i' f U)).trans ?_
  exact conormalAlgebraSquareMap_immersionClosedFactorization_map_one B S hS hZ hX hZ' hX' i i' f
    g hsq hi U

/-- **[Stacks Project, Tag 09RS] for a square of immersions, as a unital homomorphism**: the
canonical map `AlgebraicGeometry.Space.conormalAlgebraOfImmersionSquareMap` together with its
unit law `AlgebraicGeometry.Space.conormalAlgebraOfImmersionSquareMap_map_one`. -/
noncomputable def conormalAlgebraOfImmersionSquareUnitalHom (i : 𝒵 ⟶ 𝒳) (i' : 𝒵' ⟶ 𝒳')
    (f : 𝒵 ⟶ 𝒵') (g : 𝒳 ⟶ 𝒳') (hsq : i ≫ g = f ≫ i') (hi : IsImmersion B S hS i.hom)
    (hi' : IsImmersion B S hS i'.hom) :
    SheafOfModules.GradedAlgebra.UnitalHom
      ((gradedPull (X := smallEtaleRingedTopos B S hS 𝒵) (Y := smallEtaleRingedTopos B S hS 𝒵')
        (smallEtaleRingedToposHom B S hS f)).obj
          (conormalAlgebraOfImmersion B S hS hX' hZ' i'.hom hi'))
      (conormalAlgebraOfImmersion B S hS hX hZ i.hom hi) where
  app := (conormalAlgebraOfImmersionSquareMap B S hS hZ hX hZ' hX' i i' f g hsq hi hi').app
  map_mul := (conormalAlgebraOfImmersionSquareMap B S hS hZ hX hZ' hX' i i' f g hsq hi hi').map_mul
  map_one := conormalAlgebraOfImmersionSquareMap_map_one B S hS hZ hX hZ' hX' i i' f g hsq hi hi'

end Immersion

end AlgebraicGeometry.Space

end
