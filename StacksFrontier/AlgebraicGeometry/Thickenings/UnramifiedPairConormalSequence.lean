module

public import StacksFrontier.AlgebraicGeometry.Conormal.QuotientFactorization
public import StacksFrontier.AlgebraicGeometry.Morphisms.Differentials.Triangle
public import StacksFrontier.AlgebraicGeometry.Morphisms.Differentials.TwoImmersionsConormalSequence
public import StacksFrontier.AlgebraicGeometry.Morphisms.Unramified.Differentials
public import StacksFrontier.AlgebraicGeometry.Thickenings.UniversalConormalSheaf
public import StacksFrontier.AlgebraicGeometry.Thickenings.UniversalDifferentials
import StacksCore.Tactic.StacksAttribute

/-!
# The conormal sequence of two formally unramified morphisms

Let `i : Z ⟶ X` and `j : Z ⟶ Y` be formally unramified morphisms of schemes fitting into a
commutative triangle `i ≫ p = j` over `p : X ⟶ Y`. [Stacks, Tag 067V] asserts that there is a
canonical exact sequence of `𝒪_Z`-modules

`𝒞_{Z/Y} ⟶ 𝒞_{Z/X} ⟶ i^*Ω_{X/Y} ⟶ 0`,

whose first arrow is the morphism of conormal sheaves of [Stacks, Tag 04F7] and whose second
arrow is the conormal differential of [Stacks, Tag 04FC].

This file constructs the first arrow, characterizes it, and identifies the third term.

## Main definitions

* `Stacks.ConormalSequenceUnramifiedPair.universalConormalTransitivityMap`: the first arrow
  `𝒞_{Z/Y} ⟶ 𝒞_{Z/X}` of the sequence.
* `Stacks.ConormalSequenceUnramifiedPair.thickeningComparison`: the canonical morphism
  `Z' ⟶ Z''` between the ambient schemes of the universal first-order thickenings of `Z` over
  `X` and over `Y`.
* `Stacks.ConormalSequenceUnramifiedPair.ambientDifferentialsIso`: the identification
  `Ω_{Z'/Y} ≅ Ω_{Z'/Z''}` of relative differentials of the ambient scheme `Z'`.
* `Stacks.ConormalSequenceUnramifiedPair.thirdTermIso`: the identification
  `i^*Ω_{X/Y} ≅ (i')^*Ω_{Z'/Z''}` of the third term of the sequence with the third term of the
  sequence of [Stacks, Tag 067L] for the two closed immersions `i' : Z ⟶ Z'`, `j' : Z ⟶ Z''`.

## Main results

* `Stacks.ConormalSequenceUnramifiedPair.universalConormalSheafMap_eq` and
  `Stacks.ConormalSequenceUnramifiedPair.universalConormalTransitivityMap_unique`: the first
  arrow is the morphism of [Stacks, Tag 04F7] read through three canonical identifications, and
  it is the only morphism that is.
* `Stacks.ConormalSequenceUnramifiedPair.isIso_toRelativeDifferentials_of_formallyUnramified`:
  for a composable pair whose second morphism is formally unramified, the canonical map
  `Ω_{A/C} ⟶ Ω_{A/B}` of [Stacks, Tag 01UX] is an isomorphism.
* `Stacks.ConormalSequenceUnramifiedPair.inclusion_comp_thickeningComparison` and
  `Stacks.ConormalSequenceUnramifiedPair.thickeningComparison_comp_toBase`: the canonical
  morphism `Z' ⟶ Z''` restricts to `𝟙 Z` and is compatible with the structure morphisms.

## Implementation notes

Write `Z ⊂ Z'` for the universal first-order thickening of `Z` over `X` chosen by
`Stacks.Thickenings.universalFirstOrderThickening`, and `Z ⊂ Z''` for the one of `Z` over `Y`,
so that `𝒞_{Z/X} = 𝒞_{Z/Z'}` and `𝒞_{Z/Y} = 𝒞_{Z/Z''}` by [Stacks, Tag 04F4] part (2), which
is `Stacks.Thickenings.universalConormalSheaf`. The triangle `i ≫ p = j` is the commutative
square whose top morphism is `𝟙 Z` and whose bottom morphism is `p`; the morphism of conormal
sheaves of [Stacks, Tag 04F7], `Stacks.Thickenings.universalConormalSheafMap`, for that square
is a morphism `(𝟙 Z)^* 𝒞_{Z/Z''} ⟶ 𝒞_{Z/Z'}` whose two sides are spelled with the conormal
sheaf `Stacks.Thickenings.schemeConormalSheaf` of the inclusions themselves. Three canonical
identifications move it onto the spelling of [Stacks, Tag 04F4]: pullback along an identity is
the identity functor, by `Stacks.ConormalSequenceTwoImmersions.pullbackIdIso`, and the conormal
sheaf of an immersion is the conormal sheaf of its closed-immersion factorization, by
`Stacks.Immersion.conormalSheafSelfIso`, on each of the two sides.

## References

* [Stacks Project, Tag 067V](https://stacks.math.columbia.edu/tag/067V)
* [Stacks Project, Tag 067L](https://stacks.math.columbia.edu/tag/067L)
* [Stacks Project, Tag 04F4](https://stacks.math.columbia.edu/tag/04F4)
* [Stacks Project, Tag 04F6](https://stacks.math.columbia.edu/tag/04F6)
* [Stacks Project, Tag 04F7](https://stacks.math.columbia.edu/tag/04F7)
* [Stacks Project, Tag 04FB](https://stacks.math.columbia.edu/tag/04FB)
* [Stacks Project, Tag 04FC](https://stacks.math.columbia.edu/tag/04FC)
* [Stacks Project, Tag 01UX](https://stacks.math.columbia.edu/tag/01UX)
* [Stacks Project, Tag 02H9](https://stacks.math.columbia.edu/tag/02H9)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open RingedSpaceModuleAdjunction
open Stacks.Thickenings Stacks.Immersion

universe u

namespace Stacks.ConormalSequenceUnramifiedPair

variable {Z X Y : Scheme.{u}}

/-! ### Relative differentials over a formally unramified base morphism -/

/-- **The relative differentials of `A` do not see a formally unramified base change of base.**
For a composable pair `f : A ⟶ B`, `g : B ⟶ C` with `g` formally unramified, the canonical map
`Ω_{A/C} ⟶ Ω_{A/B}` of [Stacks, Tag 01UX] is an isomorphism. -/
theorem isIso_toRelativeDifferentials_of_formallyUnramified {A B C : Scheme.{u}} (f : A ⟶ B)
    (g : B ⟶ C) [FormallyUnramified g] : IsIso (Scheme.Hom.toRelativeDifferentials f g) := by
  obtain ⟨hzero, hexact⟩ := Scheme.Hom.toRelativeDifferentials_exact f g
  have hΩ : IsZero (Scheme.Hom.relativeDifferentials g) :=
    (Scheme.Hom.formallyUnramified_iff_isZero_relativeDifferentials g).mp inferInstance
  have hp : IsZero ((Scheme.Modules.pullback f).obj (Scheme.Hom.relativeDifferentials g)) :=
    Functor.map_isZero (Scheme.Modules.pullback f) hΩ
  have hmono : Mono (Scheme.Hom.toRelativeDifferentials f g) :=
    (ShortComplex.exact_iff_mono _ (hp.eq_of_src _ _)).mp hexact
  have hepi : Epi (Scheme.Hom.toRelativeDifferentials f g) :=
    Scheme.Hom.toRelativeDifferentials_epi f g
  exact isIso_of_mono_of_epi _

/-! ### The triangle, read on universal first-order thickenings -/

variable (i : Z ⟶ X) (j : Z ⟶ Y) (p : X ⟶ Y)

/-- The triangle `i ≫ p = j`, written as the commutative square whose top morphism is `𝟙 Z`. -/
theorem comp_eq_id_comp_of_triangle (h : i ≫ p = j) : i ≫ p = 𝟙 Z ≫ j := by simpa using h

variable [FormallyUnramified i] [FormallyUnramified j]

/-- **The canonical morphism `q : Z' ⟶ Z''`** from the ambient scheme of the universal
first-order thickening of `Z` over `X` to that of the universal first-order thickening of `Z`
over `Y`, for the square of `Stacks.ConormalSequenceUnramifiedPair.comp_eq_id_comp_of_triangle`:
the morphism `Stacks.Thickenings.universalFirstOrderThickeningMap` given by the universal
property of `Z''`. -/
def thickeningComparison (h : i ≫ p = j) :
    (universalFirstOrderThickening i).ambient ⟶ (universalFirstOrderThickening j).ambient :=
  universalFirstOrderThickeningMap (universalFirstOrderThickening i)
    (universalFirstOrderThickening j) (𝟙 Z) p (comp_eq_id_comp_of_triangle i j p h)

/-- The canonical morphism `q : Z' ⟶ Z''` restricts to the identity of `Z`: `Z ⟶ Z'`, `Z ⟶ Z''`
and `q` form a commutative triangle. -/
theorem inclusion_comp_thickeningComparison (h : i ≫ p = j) :
    (universalFirstOrderThickening i).inclusion ≫ thickeningComparison i j p h =
      (universalFirstOrderThickening j).inclusion := by
  rw [thickeningComparison, universalFirstOrderThickeningMap_inclusion, Category.id_comp]

/-- The canonical morphism `q : Z' ⟶ Z''` is compatible with the structure morphisms to `X` and
to `Y`. -/
theorem thickeningComparison_comp_toBase (h : i ≫ p = j) :
    thickeningComparison i j p h ≫ (universalFirstOrderThickening j).toBase =
      (universalFirstOrderThickening i).toBase ≫ p :=
  universalFirstOrderThickeningMap_toBase _ _ _ _ _

/-! ### The first arrow -/

/-- **[Stacks, Tag 067V], the first arrow.** For formally unramified `i : Z ⟶ X` and
`j : Z ⟶ Y` in a commutative triangle `i ≫ p = j`, the canonical map `𝒞_{Z/Y} ⟶ 𝒞_{Z/X}` of
conormal sheaves in the sense of [Stacks, Tag 04F4] part (2).

It is the morphism of conormal sheaves of [Stacks, Tag 04F7] for the square whose top morphism
is `𝟙 Z` and whose bottom morphism is `p`, transported along the identification of pullback
along an identity with the identity functor and along the identifications of the conormal
sheaves of the two inclusions with those of their closed-immersion factorizations. -/
@[stacks 067V "the first arrow"]
def universalConormalTransitivityMap (h : i ≫ p = j) :
    universalConormalSheaf j ⟶ universalConormalSheaf i :=
  (conormalSheafSelfIso (universalFirstOrderThickening j).inclusion).inv ≫
    (Stacks.ConormalSequenceTwoImmersions.pullbackIdIso Z).inv.app
        (schemeConormalSheaf (universalFirstOrderThickening j).inclusion) ≫
      universalConormalSheafMap (universalFirstOrderThickening i)
          (universalFirstOrderThickening j) (𝟙 Z) p (comp_eq_id_comp_of_triangle i j p h) ≫
        (conormalSheafSelfIso (universalFirstOrderThickening i).inclusion).hom

/-- **The first arrow is the morphism of conormal sheaves of [Stacks, Tag 04F7].** Read through
the identification of pullback along `𝟙 Z` with the identity functor and the identifications of
the conormal sheaves of the two inclusions with the conormal sheaves of their closed-immersion
factorizations, it is `Stacks.Thickenings.universalConormalSheafMap`. -/
theorem universalConormalSheafMap_eq (h : i ≫ p = j) :
    universalConormalSheafMap (universalFirstOrderThickening i)
        (universalFirstOrderThickening j) (𝟙 Z) p (comp_eq_id_comp_of_triangle i j p h) =
      (Stacks.ConormalSequenceTwoImmersions.pullbackIdIso Z).hom.app
          (schemeConormalSheaf (universalFirstOrderThickening j).inclusion) ≫
        (conormalSheafSelfIso (universalFirstOrderThickening j).inclusion).hom ≫
          universalConormalTransitivityMap i j p h ≫
            (conormalSheafSelfIso (universalFirstOrderThickening i).inclusion).inv := by
  rw [universalConormalTransitivityMap]
  simp

/-- **The first arrow is determined by that description**, so it is canonical: a morphism
`𝒞_{Z/Y} ⟶ 𝒞_{Z/X}` whose conjugate by those three identifications is the morphism of
[Stacks, Tag 04F7] is `universalConormalTransitivityMap`. -/
theorem universalConormalTransitivityMap_unique (h : i ≫ p = j)
    (φ : universalConormalSheaf j ⟶ universalConormalSheaf i)
    (hφ : universalConormalSheafMap (universalFirstOrderThickening i)
        (universalFirstOrderThickening j) (𝟙 Z) p (comp_eq_id_comp_of_triangle i j p h) =
      (Stacks.ConormalSequenceTwoImmersions.pullbackIdIso Z).hom.app
          (schemeConormalSheaf (universalFirstOrderThickening j).inclusion) ≫
        (conormalSheafSelfIso (universalFirstOrderThickening j).inclusion).hom ≫ φ ≫
          (conormalSheafSelfIso (universalFirstOrderThickening i).inclusion).inv) :
    φ = universalConormalTransitivityMap i j p h := by
  have key := hφ.symm.trans (universalConormalSheafMap_eq i j p h)
  have h1 := (cancel_epi ((Stacks.ConormalSequenceTwoImmersions.pullbackIdIso Z).hom.app
    (schemeConormalSheaf (universalFirstOrderThickening j).inclusion))).mp key
  have h2 := (cancel_epi
    ((conormalSheafSelfIso (universalFirstOrderThickening j).inclusion).hom)).mp h1
  exact (cancel_mono
    ((conormalSheafSelfIso (universalFirstOrderThickening i).inclusion).inv)).mp h2

/-! ### The third term -/

/-- **`Ω_{Z'/Y} ≅ Ω_{Z'/Z''}`.** The relative differentials of the ambient scheme of the
universal first-order thickening of `Z` over `X`, taken over `Y`, agree with those taken over
the ambient scheme of the universal first-order thickening of `Z` over `Y`. -/
def ambientDifferentialsIso (h : i ≫ p = j) :
    Scheme.Hom.relativeDifferentials ((universalFirstOrderThickening i).toBase ≫ p) ≅
      Scheme.Hom.relativeDifferentials (thickeningComparison i j p h) :=
  haveI := isIso_toRelativeDifferentials_of_formallyUnramified (thickeningComparison i j p h)
    (universalFirstOrderThickening j).toBase
  eqToIso (congrArg (fun t : (universalFirstOrderThickening i).ambient ⟶ Y =>
      Scheme.Hom.relativeDifferentials t) (thickeningComparison_comp_toBase i j p h).symm) ≪≫
    asIso (Scheme.Hom.toRelativeDifferentials (thickeningComparison i j p h)
      (universalFirstOrderThickening j).toBase)

/-- **`i^*Ω_{X/Y} ≅ (i')^*Ω_{Z'/Z''}`.** The third term of the sequence of [Stacks, Tag 067V]
is canonically the third term of the sequence of [Stacks, Tag 067L] for the two closed
immersions `i' : Z ⟶ Z'` and `j' : Z ⟶ Z''` of `Z` into the ambient schemes of the two
universal first-order thickenings, over the canonical morphism `thickeningComparison`. -/
def thirdTermIso (h : i ≫ p = j) :
    (Scheme.Modules.pullback i).obj (Scheme.Hom.relativeDifferentials p) ≅
      (Scheme.Modules.pullback (universalFirstOrderThickening i).inclusion).obj
        (Scheme.Hom.relativeDifferentials (thickeningComparison i j p h)) :=
  haveI := Stacks.Thickenings.isIso_thickeningRelativeDifferentialsMap
    (universalFirstOrderThickening i).isUniversal p
  ((Scheme.Modules.pullbackCongr
          (universalFirstOrderThickening i).isUniversal.inclusion_toBase).app
        (Scheme.Hom.relativeDifferentials p)).symm ≪≫
    ((Scheme.Modules.pullbackComp (universalFirstOrderThickening i).inclusion
          (universalFirstOrderThickening i).toBase).app
        (Scheme.Hom.relativeDifferentials p)).symm ≪≫
      asIso (Scheme.Hom.thickeningRelativeDifferentialsMap
          (universalFirstOrderThickening i).inclusion
          (universalFirstOrderThickening i).toBase p) ≪≫
        (Scheme.Modules.pullback (universalFirstOrderThickening i).inclusion).mapIso
          (ambientDifferentialsIso i j p h)

end Stacks.ConormalSequenceUnramifiedPair

end
