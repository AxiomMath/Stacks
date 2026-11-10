module

public import Mathlib.CategoryTheory.Comma.StructuredArrow.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Quot.CartesianFamilies
public import StacksFrontier.CategoryTheory.TwoFibreProduct.OverBase
public import StacksFrontier.CategoryTheory.TwoFibreProductOver

/-!
# Families of algebraic spaces over a fixed base algebraic space (Stacks 0D1H)

Fix an algebraic space `Z` over the base scheme `S` of a big fppf site. A *finite-type family of
algebraic spaces over* `Z` is an object `X ⟶ T` of the category `Spaces'_{ft}` of Stacks 0D1D
together with a morphism `h : T ⟶ Z` from its base scheme, read as an algebraic space; a morphism
of such is a cartesian morphism `(f, g)` of families with `h ∘ g = h'`. Stacks 0D1H is the remark
that the resulting square

```text
  Z-Spaces'_{ft}  ----->  Spaces'_{ft}
        |                      |
        v                      v
  (Sch/Z)_{fppf}  ----->  (Sch/S)_{fppf}
```

is a 2-fibre product square, and likewise with the finitely presented, flat and proper families
of Stacks 0D1D in place of the finite-type ones. It is what transfers statements about the
absolute category of families to families over a fixed base algebraic space.

Both squares are instances of one categorical fact: for a functor `p : 𝒳 ⥤ 𝒞`, a functor
`L : 𝒞 ⥤ 𝒟` and an object `D` of `𝒟`, the costructured-arrow category of `p ⋙ L` at `D` is the
2-fibre product, over `𝒞`, of `𝒳` with the costructured-arrow category of `L` at `D`.

## Main definitions

* `CategoryTheory.CostructuredArrow.toTwoFibreProductOver`: the canonical comparison from
  `CostructuredArrow (p ⋙ L) D` to the 2-fibre product of `p` with `CostructuredArrow L D`
  over `𝒞`.
* `AlgebraicGeometry.BigFppfOverSpace` is the category `(Sch/Z)_{fppf}` of schemes of the big
  fppf site of `S` carrying a morphism to `Z`, and
  `AlgebraicGeometry.bigFppfOverSpaceProjection` its projection to `(Sch/S)_{fppf}`.
* `AlgebraicGeometry.CartesianFiniteTypeSpacesOver`: **Stacks 0D1H**, the category
  `Z-Spaces'_{ft}` of finite-type families of algebraic spaces over `Z`, with
  `AlgebraicGeometry.cartesianFiniteTypeSpacesOverForget` and
  `AlgebraicGeometry.cartesianFiniteTypeSpacesOverProjection` the two legs of the square out of
  it.
* `AlgebraicGeometry.CartesianProperFlatSpacesOver`: **Stacks 0D1H**, the category
  `Z-Spaces'_{fp, flat, proper}`, with the analogous two legs.

## Main results

* `CategoryTheory.CostructuredArrow.isEquivalence_toTwoFibreProductOver`: the categorical fact
  above, together with
  `CategoryTheory.CostructuredArrow.toTwoFibreProductOver_comp_fst`,
  `toTwoFibreProductOver_comp_snd` and `toTwoFibreProductOver_comp_structureFunctor`, which say
  that the comparison respects the two projections and the structure functor to `𝒞` *on the
  nose*, so that it is an equivalence of categories over `𝒞` and not merely an abstract
  equivalence of categories.
* `AlgebraicGeometry.isEquivalence_cartesianFiniteTypeSpacesOverToTwoFibreProduct`:
  **Stacks 0D1H** for finite-type families, the 2-fibre product square.
* `AlgebraicGeometry.isEquivalence_cartesianProperFlatSpacesOverToTwoFibreProduct`:
  **Stacks 0D1H** for finitely presented, flat and proper families.

## Implementation notes

The 2-fibre product used is `CategoryTheory.TwoFibreProductOver`, the 2-fibre product of
categories *over* a base of Stacks 0040, whose comparison isomorphism is required to be vertical.
That is the correct notion here, since the square is a square of categories over the big fppf
site, and not Mathlib's absolute `CategoryTheory.Limits.CategoricalPullback` of Stacks 003R: the
two are inequivalent. Because the bottom functor of the square is the identity, a vertical
comparison isomorphism over a base object is forced to be the identity, which is why the
comparison functor is built with `CategoryTheory.Iso.refl` as its 2-cell and why essential
surjectivity can transport an object of the 2-fibre product without choosing a base change.

The source states the remark for an algebraic space over `Spec(ℤ)`, so that the bottom right
corner of the square is `Sch_{fppf}`; here the whole chapter is relativised over the base scheme
`S` of the big fppf site, as in Stacks 0D1E, and the bottom right corner is `(Sch/S)_{fppf}`.
Taking `S = Spec(ℤ)` recovers the statement of the source.

A morphism from a scheme `T` of the site to the algebraic space `Z` is a morphism
`schemeSpaceFunctor T ⟶ Z` of algebraic spaces, and `AlgebraicGeometry.schemeSpaceFunctor` is a
functor, so both `(Sch/Z)_{fppf}` and `Z-Spaces'_{ft}` are costructured-arrow categories; that is
what puts them in the scope of the categorical fact above.

## References

* [Stacks Project, Tag 0D1H](https://stacks.math.columbia.edu/tag/0D1H)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.CostructuredArrow

universe v₁ v₂ v₃ u₁ u₂ u₃

variable {𝒞 : Type u₁} [Category.{v₁} 𝒞] {𝒳 : Type u₂} [Category.{v₂} 𝒳]
  {𝒟 : Type u₃} [Category.{v₃} 𝒟]
variable (p : 𝒳 ⥤ 𝒞) (L : 𝒞 ⥤ 𝒟) (D : 𝒟)

/-- The canonical comparison from `CostructuredArrow (p ⋙ L) D` to the 2-fibre product, over `𝒞`,
of `p : 𝒳 ⥤ 𝒞` with the projection `CostructuredArrow L D ⥤ 𝒞`. The comparison 2-cell is the
identity, which is the only vertical one because the bottom functor of the square is the
identity. -/
def toTwoFibreProductOver :
    CostructuredArrow (p ⋙ L) D ⥤
      TwoFibreProductOver p (proj L D) (𝟭 𝒞) p (proj L D) :=
  TwoFibreProductOver.lift p (proj L D) (𝟭 𝒞) p (proj L D) (proj (p ⋙ L) D ⋙ p)
    (proj (p ⋙ L) D) (pre p L D) rfl rfl (Iso.refl _) fun _ => IsHomLift.id rfl

/-- The comparison respects the first projection on the nose: the object of `𝒳` underlying the
image of `(x, h)` is `x`. -/
theorem toTwoFibreProductOver_comp_fst :
    toTwoFibreProductOver p L D ⋙ TwoFibreProductOver.fst p (proj L D) (𝟭 𝒞) p (proj L D) =
      proj (p ⋙ L) D := by
  apply CategoryTheory.Functor.hext <;> intros <;> rfl

/-- The comparison respects the second projection on the nose: the costructured arrow on `L`
underlying the image of `(x, h)` is `(p x, h)`. -/
theorem toTwoFibreProductOver_comp_snd :
    toTwoFibreProductOver p L D ⋙ TwoFibreProductOver.snd p (proj L D) (𝟭 𝒞) p (proj L D) =
      pre p L D := by
  apply CategoryTheory.Functor.hext <;> intros <;> rfl

/-- The comparison is a functor over `𝒞`, on the nose. -/
theorem toTwoFibreProductOver_comp_structureFunctor :
    toTwoFibreProductOver p L D ⋙
        TwoFibreProductOver.structureFunctor p (proj L D) (𝟭 𝒞) p (proj L D) =
      proj (p ⋙ L) D ⋙ p := by
  apply CategoryTheory.Functor.hext <;> intros <;> rfl

/-- The canonical comparison is faithful: a morphism of the 2-fibre product is determined by its
`𝒳`-component. -/
theorem faithful_toTwoFibreProductOver : (toTwoFibreProductOver p L D).Faithful :=
  ⟨fun h => hom_ext _ _ (congrArg TwoFibreProductOver.Hom.a h)⟩

/-- The canonical comparison is full: the two components of a morphism of the 2-fibre product
agree, so the `𝒳`-component is already a morphism of costructured arrows on `p ⋙ L`. -/
theorem full_toTwoFibreProductOver : (toTwoFibreProductOver p L D).Full where
  map_surjective {X Y} m := by
    have hleft : p.map m.a = m.b.left := by
      have hw : p.map m.a ≫ 𝟙 _ = 𝟙 _ ≫ m.b.left := m.w
      simpa only [Category.comp_id, Category.id_comp] using hw
    refine ⟨homMk m.a ?_, ?_⟩
    · change L.map (p.map m.a) ≫ Y.hom = X.hom
      rw [hleft]
      exact CostructuredArrow.w m.b
    · exact TwoFibreProductOver.Hom.ext' rfl (hom_ext _ _ hleft)

/-- The canonical comparison is essentially surjective: the comparison isomorphism of an object
of the 2-fibre product is vertical over the identity, hence is the identity, so the object is
hit on the nose. -/
theorem essSurj_toTwoFibreProductOver : (toTwoFibreProductOver p L D).EssSurj where
  mem_essImage := by
    rintro ⟨base, x, y, hx, hy, iso, vertical⟩
    cases hx
    obtain ⟨yleft, yright, yhom⟩ := y
    change yleft = p.obj x at hy
    cases hy
    have : (𝟭 𝒞).IsHomLift (𝟙 (p.obj x)) iso.hom := vertical
    cases (Iso.ext (IsHomLift.eq_of_isHomLift (𝟭 𝒞) (𝟙 (p.obj x)) iso.hom).symm :
      iso = Iso.refl (p.obj x))
    exact ⟨mk yhom, ⟨Iso.refl _⟩⟩

/-- Costructured arrows on a composite `p ⋙ L` at `D` are the 2-fibre product over `𝒞` of `p`
with the costructured arrows on `L` at `D`: the canonical comparison is an equivalence. -/
theorem isEquivalence_toTwoFibreProductOver :
    (toTwoFibreProductOver p L D).IsEquivalence :=
  have := faithful_toTwoFibreProductOver p L D
  have := full_toTwoFibreProductOver p L D
  have := essSurj_toTwoFibreProductOver p L D
  { }

end CategoryTheory.CostructuredArrow

namespace AlgebraicGeometry

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (Z : AlgebraicSpaces B S hS)

/-- The category `(Sch/Z)_{fppf}` of schemes of the big fppf site of `S` carrying a morphism to a
fixed algebraic space `Z` over `S`. -/
abbrev BigFppfOverSpace := CostructuredArrow (schemeSpaceFunctor B S hS) Z

/-- The projection from schemes carrying a morphism to `Z` to the big fppf site of `S`. -/
abbrev bigFppfOverSpaceProjection : BigFppfOverSpace B S hS Z ⥤ BigFppfOver B S hS :=
  CostructuredArrow.proj (schemeSpaceFunctor B S hS) Z

/-- **Stacks 0D1H.** The category `Z-Spaces'_{ft}` of finite-type families of algebraic spaces
over a fixed algebraic space `Z`: an object is a finite-type family `X ⟶ T` of algebraic spaces
together with a morphism from its base scheme to `Z`, and a morphism is a cartesian morphism of
families commuting with those morphisms. -/
@[stacks 0D1H "the category of finite-type families over a base algebraic space"]
abbrev CartesianFiniteTypeSpacesOver :=
  CostructuredArrow (cartesianFiniteTypeProjection B S hS ⋙ schemeSpaceFunctor B S hS) Z

/-- The top leg of the square of Stacks 0D1H for finite-type families: forgetting the morphism to
`Z`. -/
abbrev cartesianFiniteTypeSpacesOverForget :
    CartesianFiniteTypeSpacesOver B S hS Z ⥤ CartesianFiniteTypeSpaces B S hS :=
  CostructuredArrow.proj (cartesianFiniteTypeProjection B S hS ⋙ schemeSpaceFunctor B S hS) Z

/-- The left leg of the square of Stacks 0D1H for finite-type families: taking a finite-type
family over `Z` to its base scheme with its morphism to `Z`. -/
abbrev cartesianFiniteTypeSpacesOverProjection :
    CartesianFiniteTypeSpacesOver B S hS Z ⥤ BigFppfOverSpace B S hS Z :=
  CostructuredArrow.pre (cartesianFiniteTypeProjection B S hS) (schemeSpaceFunctor B S hS) Z

/-- The canonical comparison of Stacks 0D1H for finite-type families: from finite-type families
over `Z` to the 2-fibre product, over the big fppf site of `S`, of the finite-type families of
Stacks 0D1D with the schemes over `Z`. -/
abbrev cartesianFiniteTypeSpacesOverToTwoFibreProduct :
    CartesianFiniteTypeSpacesOver B S hS Z ⥤
      TwoFibreProductOver (cartesianFiniteTypeProjection B S hS)
        (bigFppfOverSpaceProjection B S hS Z) (𝟭 (BigFppfOver B S hS))
        (cartesianFiniteTypeProjection B S hS) (bigFppfOverSpaceProjection B S hS Z) :=
  CostructuredArrow.toTwoFibreProductOver (cartesianFiniteTypeProjection B S hS)
    (schemeSpaceFunctor B S hS) Z

/-- **Stacks 0D1H** for finite-type families. The absolute and the relative categories of
finite-type families of algebraic spaces form a 2-fibre product square over the big fppf site of
`S`: the canonical comparison from the finite-type families over `Z` to the 2-fibre product of
the finite-type families with the schemes over `Z` is an equivalence. -/
@[stacks 0D1H "the 2-fibre product square for finite-type families"]
theorem isEquivalence_cartesianFiniteTypeSpacesOverToTwoFibreProduct :
    (cartesianFiniteTypeSpacesOverToTwoFibreProduct B S hS Z).IsEquivalence :=
  CostructuredArrow.isEquivalence_toTwoFibreProductOver
    (cartesianFiniteTypeProjection B S hS) (schemeSpaceFunctor B S hS) Z

/-- **Stacks 0D1H.** The category `Z-Spaces'_{fp, flat, proper}` of finitely presented, flat and
proper families of algebraic spaces over a fixed algebraic space `Z`: an object is such a family
`X ⟶ T` together with a morphism from its base scheme to `Z`, and a morphism is a cartesian
morphism of families commuting with those morphisms. -/
@[stacks 0D1H "the category of finitely presented, flat and proper families over a base space"]
abbrev CartesianProperFlatSpacesOver :=
  CostructuredArrow (cartesianProperFlatProjection B S hS ⋙ schemeSpaceFunctor B S hS) Z

/-- The top leg of the square of Stacks 0D1H for finitely presented, flat and proper families:
forgetting the morphism to `Z`. -/
abbrev cartesianProperFlatSpacesOverForget :
    CartesianProperFlatSpacesOver B S hS Z ⥤ CartesianProperFlatSpaces B S hS :=
  CostructuredArrow.proj (cartesianProperFlatProjection B S hS ⋙ schemeSpaceFunctor B S hS) Z

/-- The left leg of the square of Stacks 0D1H for finitely presented, flat and proper families:
taking such a family over `Z` to its base scheme with its morphism to `Z`. -/
abbrev cartesianProperFlatSpacesOverProjection :
    CartesianProperFlatSpacesOver B S hS Z ⥤ BigFppfOverSpace B S hS Z :=
  CostructuredArrow.pre (cartesianProperFlatProjection B S hS) (schemeSpaceFunctor B S hS) Z

/-- The canonical comparison of Stacks 0D1H for finitely presented, flat and proper families:
from such families over `Z` to the 2-fibre product, over the big fppf site of `S`, of the
finitely presented, flat and proper families of Stacks 0D1D with the schemes over `Z`. -/
abbrev cartesianProperFlatSpacesOverToTwoFibreProduct :
    CartesianProperFlatSpacesOver B S hS Z ⥤
      TwoFibreProductOver (cartesianProperFlatProjection B S hS)
        (bigFppfOverSpaceProjection B S hS Z) (𝟭 (BigFppfOver B S hS))
        (cartesianProperFlatProjection B S hS) (bigFppfOverSpaceProjection B S hS Z) :=
  CostructuredArrow.toTwoFibreProductOver (cartesianProperFlatProjection B S hS)
    (schemeSpaceFunctor B S hS) Z

/-- **Stacks 0D1H** for finitely presented, flat and proper families. The absolute and the
relative categories of finitely presented, flat and proper families of algebraic spaces form a
2-fibre product square over the big fppf site of `S`: the canonical comparison from such families
over `Z` to the 2-fibre product of such families with the schemes over `Z` is an equivalence. -/
@[stacks 0D1H "the 2-fibre product square for finitely presented, flat and proper families"]
theorem isEquivalence_cartesianProperFlatSpacesOverToTwoFibreProduct :
    (cartesianProperFlatSpacesOverToTwoFibreProduct B S hS Z).IsEquivalence :=
  CostructuredArrow.isEquivalence_toTwoFibreProductOver
    (cartesianProperFlatProjection B S hS) (schemeSpaceFunctor B S hS) Z

end AlgebraicGeometry

end
