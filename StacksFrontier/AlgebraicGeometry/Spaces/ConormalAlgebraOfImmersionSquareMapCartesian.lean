module

public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalAlgebraOfImmersionSquareMap
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatComposition

/-!
# The canonical map of conormal algebras of immersions for a cartesian square

Let
```
Z --i--→ X
|        |
f        g
↓        ↓
Z' -i'-→ X'
```
be a cartesian square of algebraic spaces over a scheme `S` contained in a big fppf site `B`,
with `i` and `i'` immersions.  [Stacks Project, Tag 09RT] asserts that the canonical map

`f^*𝒞_{Z'/X',*} ⟶ 𝒞_{Z/X,*}`

of [Stacks Project, Tag 09RS] between the conormal algebras of the immersions of
[Stacks Project, Tag 09RN] (`AlgebraicGeometry.Space.conormalAlgebraOfImmersionSquareMap`) is
surjective, and that it is an isomorphism if `g` is flat.  Both assertions are proved here.

## The proof

By construction `AlgebraicGeometry.Space.conormalAlgebraOfImmersionSquareMap` is the composite
of two isomorphisms (the inverse image along `f` of the inverse of
`AlgebraicGeometry.Space.conormalAlgebraOfImmersionIso` for `i'`, and the composition comparison
`f^*𝟙^* ≅ f^*`) with the canonical map `AlgebraicGeometry.Space.conormalAlgebraSquareMap` of the
square
```
Z --i₀--→ X ∖ ∂Z
|f          |ι ≫ g
↓           ↓
Z' --i'--→ X'
```
where `i₀` is the closed factorisation of `i` and `ι : X ∖ ∂Z ⟶ X` the open inclusion.  This
square is cartesian: it is the vertical pasting of the cartesian square
`AlgebraicGeometry.Space.isPullback_immersionClosedFactorization` (with the identity on the left)
on top of the given cartesian square.  And `ι ≫ g` is flat when `g` is, since `ι` is an open
immersion, hence étale, hence flat.  So both clauses follow from the corresponding clauses of
Stacks 09RT for `AlgebraicGeometry.Space.conormalAlgebraSquareMap`,
`AlgebraicGeometry.Space.epi_conormalAlgebraSquareMap_app_of_isPullback` and
`AlgebraicGeometry.Space.isIso_conormalAlgebraSquareMap_of_isPullback_of_isFlat`.

## Main results

* `AlgebraicGeometry.Space.isPullback_immersionClosedFactorization_comp`: the square of the
  closed factorisation of `i` over `i'` is cartesian.
* `AlgebraicGeometry.Space.epi_conormalAlgebraSquareMap_app_of_isPullback_of_comm`: the
  surjectivity clause for `AlgebraicGeometry.Space.conormalAlgebraSquareMap` built on an arbitrary
  proof of commutativity of the square.
* `AlgebraicGeometry.Space.epi_conormalAlgebraOfImmersionSquareMap_app_of_isPullback`: **the
  surjectivity assertion of [Stacks Project, Tag 09RT]** on the conormal algebras of immersions.
* `AlgebraicGeometry.Space.isIso_conormalAlgebraOfImmersionSquareMap_of_isPullback_of_isFlat`:
  **the flat assertion of [Stacks Project, Tag 09RT]** on the conormal algebras of immersions.

## References

* [Stacks Project, Tag 09RT](https://stacks.math.columbia.edu/tag/09RT)
* [Stacks Project, Tag 09RS](https://stacks.math.columbia.edu/tag/09RS)
* [Stacks Project, Tag 09RN](https://stacks.math.columbia.edu/tag/09RN)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open Stacks.Sheaves.GradedAlgebraEssentiallySmall (gradedPull)

universe t a v u

namespace SheafOfModules.GradedAlgebra

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t}}

/-- Precomposing a homomorphism of sheaves of graded algebras which is an epimorphism in degree
`n` with an isomorphism gives an epimorphism in degree `n`. -/
theorem epi_comp_app_of_isIso {A D E : GradedAlgebra.{t, a} R} (φ : A ⟶ D) (hφ : IsIso φ)
    (ψ : D ⟶ E) (n : ℤ) (hψ : Epi (ψ.app n)) : Epi ((φ ≫ ψ).app n) := by
  rw [categoryStruct_comp_app]
  have := isIso_app_of_isIso φ hφ n
  exact epi_comp _ _

end SheafOfModules.GradedAlgebra

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- `AlgebraicGeometry.Space.epi_conormalAlgebraSquareMap_app_of_isPullback` for the canonical
map of Stacks 09RS built on any proof `hsq` of commutativity of the cartesian square, rather than
on the commutativity `sq.w` carried by the pullback square.  The two maps agree by proof
irrelevance; stating the epimorphism for an arbitrary `hsq` lets it be applied to a map whose
commutativity proof is not `sq.w` without the kernel unfolding the map to compare the two. -/
theorem epi_conormalAlgebraSquareMap_app_of_isPullback_of_comm
    {Z X Z' X' : AlgebraicSpaces B S hS} {i : Z ⟶ X} {i' : Z' ⟶ X'} {f : Z ⟶ Z'} {g : X ⟶ X'}
    (sq : IsPullback i f g i') (hsq : i ≫ g = f ≫ i') (hi' : IsImmersion B S hS i'.hom)
    (n : ℤ) : Epi ((conormalAlgebraSquareMap B S hS i i' f g hsq).app n) := by
  have e : conormalAlgebraSquareMap B S hS i i' f g hsq =
      conormalAlgebraSquareMap B S hS i i' f g sq.w := rfl
  rw [e]
  exact epi_conormalAlgebraSquareMap_app_of_isPullback B S hS sq hi' n

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

/-- **The square of the closed factorisation of an immersion over a cartesian square is
cartesian.**  If `Z = X ×_{X'} Z'` with `i` an immersion, then `Z = (X ∖ ∂Z) ×_{X'} Z'` along
the closed factorisation `i₀ : Z ⟶ X ∖ ∂Z` and `f`: paste the cartesian square
`AlgebraicGeometry.Space.isPullback_immersionClosedFactorization` on top of the given one. -/
theorem isPullback_immersionClosedFactorization_comp {i : 𝒵 ⟶ 𝒳} {i' : 𝒵' ⟶ 𝒳'}
    {f : 𝒵 ⟶ 𝒵'} {g : 𝒳 ⟶ 𝒳'} (sq : IsPullback i f g i') (hi : IsImmersion B S hS i.hom) :
    IsPullback (immersionClosedFactorization B S hS hX hZ i.hom hi) f
      (immersionAmbientι B S hS i hi ≫ g) i' := by
  have h := (isPullback_immersionClosedFactorization B S hS hZ hX i hi).paste_vert sq
  rwa [Category.id_comp] at h

/-- **[Stacks Project, Tag 09RT], surjectivity, on the conormal algebras of immersions.**  Let

```
Z --i--→ X
|        |
f        g
↓        ↓
Z' -i'-→ X'
```

be a cartesian square of algebraic spaces with `i` and `i'` immersions.  Then the canonical map
`f^*𝒞_{Z'/X',*} ⟶ 𝒞_{Z/X,*}` of [Stacks Project, Tag 09RS] between the conormal algebras of the
immersions of [Stacks Project, Tag 09RN]
(`AlgebraicGeometry.Space.conormalAlgebraOfImmersionSquareMap`) is surjective: it is an
epimorphism of `𝒪_Z`-modules in every degree.

The map is two isomorphisms followed by the canonical map of the square of the closed
factorisation of `i`, which is cartesian
(`AlgebraicGeometry.Space.isPullback_immersionClosedFactorization_comp`), so that
`AlgebraicGeometry.Space.epi_conormalAlgebraSquareMap_app_of_isPullback` applies. -/
@[stacks 09RT "surjectivity: for a cartesian square with i, i' immersions, the canonical map \
f^*𝒞_{Z'/X',*} ⟶ 𝒞_{Z/X,*} of Tag 09RS on the conormal algebras of immersions of Tag 09RN is \
surjective in every degree"]
theorem epi_conormalAlgebraOfImmersionSquareMap_app_of_isPullback {i : 𝒵 ⟶ 𝒳} {i' : 𝒵' ⟶ 𝒳'}
    {f : 𝒵 ⟶ 𝒵'} {g : 𝒳 ⟶ 𝒳'} (sq : IsPullback i f g i') (hi : IsImmersion B S hS i.hom)
    (hi' : IsImmersion B S hS i'.hom) (n : ℤ) :
    Epi ((conormalAlgebraOfImmersionSquareMap B S hS hZ hX hZ' hX' i i' f g sq.w hi hi').app
      n) := by
  rw [conormalAlgebraOfImmersionSquareMap_eq]
  refine SheafOfModules.GradedAlgebra.epi_comp_app_of_isIso _
    ((gradedPull (X := smallEtaleRingedTopos B S hS 𝒵) (Y := smallEtaleRingedTopos B S hS 𝒵')
      (smallEtaleRingedToposHom B S hS f)).mapIso
      (conormalAlgebraOfImmersionIso B S hS hZ' hX' i' hi').symm).isIso_hom _ n ?_
  refine SheafOfModules.GradedAlgebra.epi_comp_app_of_isIso _
    ((gradedAlgebraPullbackCompIsoOfEq B S hS f (𝟙 𝒵') f (Category.comp_id f).symm).app
      (conormalAlgebra B S hS i')).symm.isIso_hom _ n ?_
  refine epi_conormalAlgebraSquareMap_app_of_isPullback_of_comm B S hS ?_ _ hi' n
  exact isPullback_immersionClosedFactorization_comp B S hS hZ hX hZ' hX' sq hi

/-- **[Stacks Project, Tag 09RT], the flat case, on the conormal algebras of immersions.**  Let

```
Z --i--→ X
|        |
f        g
↓        ↓
Z' -i'-→ X'
```

be a cartesian square of algebraic spaces with `i` and `i'` immersions.  If `g` is flat, the
canonical map `f^*𝒞_{Z'/X',*} ⟶ 𝒞_{Z/X,*}` of [Stacks Project, Tag 09RS] between the conormal
algebras of the immersions of [Stacks Project, Tag 09RN]
(`AlgebraicGeometry.Space.conormalAlgebraOfImmersionSquareMap`) is an isomorphism of sheaves of
graded `𝒪_Z`-algebras.

The map is two isomorphisms followed by the canonical map of the square of the closed
factorisation of `i`, which is cartesian
(`AlgebraicGeometry.Space.isPullback_immersionClosedFactorization_comp`) with flat right edge
`ι ≫ g` (an open immersion is étale, hence flat, and flatness composes), so that
`AlgebraicGeometry.Space.isIso_conormalAlgebraSquareMap_of_isPullback_of_isFlat` applies. -/
@[stacks 09RT "flat case: for a cartesian square with i, i' immersions and g flat, the \
canonical map f^*𝒞_{Z'/X',*} ⟶ 𝒞_{Z/X,*} of Tag 09RS on the conormal algebras of immersions of \
Tag 09RN is an isomorphism of graded algebras"]
theorem isIso_conormalAlgebraOfImmersionSquareMap_of_isPullback_of_isFlat {i : 𝒵 ⟶ 𝒳}
    {i' : 𝒵' ⟶ 𝒳'} {f : 𝒵 ⟶ 𝒵'} {g : 𝒳 ⟶ 𝒳'} (sq : IsPullback i f g i')
    (hi : IsImmersion B S hS i.hom) (hi' : IsImmersion B S hS i'.hom)
    (hg : IsFlat B S hS g.hom) :
    IsIso (conormalAlgebraOfImmersionSquareMap B S hS hZ hX hZ' hX' i i' f g sq.w hi hi') := by
  have hflat : IsFlat B S hS (immersionAmbientι B S hS i hi ≫ g).hom :=
    isFlat_comp B S hS (immersionAmbient B S hS hX hZ i.hom hi).2 hX hX' _ _
      (isFlat_of_isEtale B S hS (isEtale_immersionAmbientι B S hS i hi)) hg
  have h₃ := isIso_conormalAlgebraSquareMap_of_isPullback_of_isFlat B S hS
    (isPullback_immersionClosedFactorization_comp B S hS hZ hX hZ' hX' sq hi) hi' hflat
  have h₁ := ((gradedPull (X := smallEtaleRingedTopos B S hS 𝒵)
    (Y := smallEtaleRingedTopos B S hS 𝒵') (smallEtaleRingedToposHom B S hS f)).mapIso
      (conormalAlgebraOfImmersionIso B S hS hZ' hX' i' hi').symm).isIso_hom
  rw [conormalAlgebraOfImmersionSquareMap_eq]
  exact @IsIso.comp_isIso _ _ _ _ _ _ _ h₁ (@IsIso.comp_isIso _ _ _ _ _ _ _ inferInstance h₃)

end Immersion

end AlgebraicGeometry.Space

end
