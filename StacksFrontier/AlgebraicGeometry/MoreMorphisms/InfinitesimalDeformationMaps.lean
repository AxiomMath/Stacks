module

public import StacksFrontier.AlgebraicGeometry.Conormal.AmbientAffine
public import StacksFrontier.AlgebraicGeometry.Thickenings
public import StacksFrontier.AlgebraicGeometry.Thickenings.UniversalConormalGenerators

/-!
# Infinitesimal deformations of maps: the constrained lifts of a morphism

Let `S` be a scheme, let `i : X ⟶ X'` and `j : Y ⟶ Y'` be first-order thickenings over `S`, let
`a : X ⟶ Y` be a morphism and let `A : a^* 𝒞_{Y/Y'} ⟶ 𝒞_{X/X'}` be a map of `𝒪_X`-modules.
[Stacks Project, Tag 04FI] attaches to an open `V` of `X'`, with `U = X ∩ V` its intersection
with `X`, the set of morphisms `b : V ⟶ Y'` such that

1. `b` is a morphism over `S`;
2. `b` restricts to `a` on `U`, that is `(i ∣_ V) ≫ b = ι_U ≫ a ≫ j`; and
3. the map `(ι_U ≫ a)^* 𝒞_{Y/Y'} ⟶ 𝒞_{U/V}` of [Stacks Project, Tag 01R4] induced by the square
   of (2) is the restriction of `A` to `U`.

This file names that set and the restriction of `A` appearing in condition (3), and shows that
conditions (1) and (2) are stable under shrinking `V`. The conditions are stated for immersions
`i` and `j`, and neither `i`, `j` nor `a` is required to be a morphism over `S`: only the
structure morphisms `X' ⟶ S` and `Y' ⟶ S` enter, through condition (1).

## Main definitions

* `Stacks.Thickenings.restrictConormalSheafMap`: the restriction of a map
  `A : a^* 𝒞_{Y/Y'} ⟶ 𝒞_{X/X'}` to the open `U = i⁻¹V` of `X`, read as a map
  `(ι_U ≫ a)^* 𝒞_{Y/Y'} ⟶ 𝒞_{U/V}`. This is the `A|_U` of condition (3).
* `Stacks.Thickenings.IsCompatibleLift`: conditions (1), (2) and (3) on a morphism
  `b : V ⟶ Y'`.
* `Stacks.Thickenings.compatibleLifts`: the set of [Stacks Project, Tag 04FI], as the subtype of
  morphisms `V ⟶ Y'` satisfying `IsCompatibleLift`, and
  `Stacks.Thickenings.firstOrderCompatibleLifts`, the same set in the first-order-thickening
  setting in which [Stacks Project, Tag 04FH] states it; `compatibleLifts` is the same
  assignment for arbitrary immersions.

## Main results

* `Stacks.Thickenings.IsCompatibleLift.restrict_fst` and
  `Stacks.Thickenings.IsCompatibleLift.restrict_snd`: conditions (1) and (2) are stable under
  restriction along `V' ≤ V`.

## References

* [Stacks Project, Tag 01R2](https://stacks.math.columbia.edu/tag/01R2)
* [Stacks Project, Tag 01R4](https://stacks.math.columbia.edu/tag/01R4)
* [Stacks Project, Tag 04EX](https://stacks.math.columbia.edu/tag/04EX)
* [Stacks Project, Tag 04FH](https://stacks.math.columbia.edu/tag/04FH)
* [Stacks Project, Tag 04FI](https://stacks.math.columbia.edu/tag/04FI)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry RingedSpaceModuleAdjunction
open Stacks.Immersion RingedSpaceModuleAdjunction

universe u

namespace Stacks.Thickenings

variable {S X X' Y Y' : Scheme.{u}} {i : X ⟶ X'} {j : Y ⟶ Y'}

/-- **The restriction of a map of conormal sheaves to an open of the ambient scheme.** For
immersions `i : X ⟶ X'` and `j : Y ⟶ Y'`, a morphism `a : X ⟶ Y` and a map
`A : a^* 𝒞_{Y/Y'} ⟶ 𝒞_{X/X'}`, this is `A` read over the open `U = i⁻¹V` of `X` cut out by an
open `V` of `X'`, as a map `(ι_U ≫ a)^* 𝒞_{Y/Y'} ⟶ 𝒞_{U/V}`. It is the `A|_U` of condition (3)
of [Stacks Project, Tag 04FI]. -/
def restrictConormalSheafMap [IsImmersion i] [IsImmersion j] (a : X ⟶ Y)
    (A : (modulePullback a.toLRSHom.toShHom).obj (immersionConormalSheaf j) ⟶
      immersionConormalSheaf i) (V : X'.Opens) :
    (modulePullback ((i ⁻¹ᵁ V).ι ≫ a).toLRSHom.toShHom).obj (immersionConormalSheaf j) ⟶
      immersionConormalSheaf (i ∣_ V) :=
  (modulePullbackComp (i ⁻¹ᵁ V).ι.toLRSHom.toShHom a.toLRSHom.toShHom).hom.app
      (immersionConormalSheaf j) ≫
    (modulePullback (i ⁻¹ᵁ V).ι.toLRSHom.toShHom).map A ≫
    (RingedSpace.modulePullbackRestrictIso X.toSheafedSpace (i ⁻¹ᵁ V)).hom.app
      (immersionConormalSheaf i) ≫
    (conormalSheafSelfRestrictIso i V).hom ≫ (conormalSheafSelfIso (i ∣_ V)).hom

section

variable [IsImmersion i] [IsImmersion j]

/-- **The three conditions of [Stacks Project, Tag 04FI] on a lift of `a` over an open of `X'`.**
For a morphism `b : V ⟶ Y'` out of an open `V` of `X'`, with `U = i⁻¹V`: `b` is a morphism over
`S`; `b` restricts to `a` on `U`; and the map of conormal sheaves of [Stacks Project, Tag 01R4]
induced by the resulting square is the restriction of `A` to `U`. -/
def IsCompatibleLift (pX' : X' ⟶ S) (pY' : Y' ⟶ S) (a : X ⟶ Y)
    (A : (modulePullback a.toLRSHom.toShHom).obj (immersionConormalSheaf j) ⟶
      immersionConormalSheaf i) (V : X'.Opens) (b : V.toScheme ⟶ Y') : Prop :=
  b ≫ pY' = V.ι ≫ pX' ∧
    ∃ h : i ∣_ V ≫ b = ((i ⁻¹ᵁ V).ι ≫ a) ≫ j,
      immersionConormalSheafMap (i ∣_ V) j ((i ⁻¹ᵁ V).ι ≫ a) b (toShHom_square h) =
        restrictConormalSheafMap a A V

/-- **The set of [Stacks Project, Tag 04FI].** The morphisms `V ⟶ Y'` out of an open `V` of `X'`
satisfying the three conditions of `Stacks.Thickenings.IsCompatibleLift`. -/
def compatibleLifts (pX' : X' ⟶ S) (pY' : Y' ⟶ S) (a : X ⟶ Y)
    (A : (modulePullback a.toLRSHom.toShHom).obj (immersionConormalSheaf j) ⟶
      immersionConormalSheaf i) (V : X'.Opens) : Type u :=
  { b : V.toScheme ⟶ Y' // IsCompatibleLift pX' pY' a A V b }

variable {pX' : X' ⟶ S} {pY' : Y' ⟶ S} {a : X ⟶ Y}
  {A : (modulePullback a.toLRSHom.toShHom).obj (immersionConormalSheaf j) ⟶
    immersionConormalSheaf i} {V : X'.Opens} {b : V.toScheme ⟶ Y'}

/-- **Condition (1) of [Stacks Project, Tag 04FI] is stable under restriction.** If `b` is a
morphism over `S` then so is its restriction to a smaller open `V'` of `X'`. -/
theorem IsCompatibleLift.restrict_fst (hb : IsCompatibleLift pX' pY' a A V b) {V' : X'.Opens}
    (hV : V' ≤ V) : (X'.homOfLE hV ≫ b) ≫ pY' = V'.ι ≫ pX' := by
  rw [Category.assoc, hb.1, ← Category.assoc, Scheme.homOfLE_ι]

/-- **Condition (2) of [Stacks Project, Tag 04FI] is stable under restriction.** If `b` restricts
to `a` on `i⁻¹V` then its restriction to a smaller open `V'` of `X'` restricts to `a` on
`i⁻¹V'`. -/
theorem IsCompatibleLift.restrict_snd (hb : IsCompatibleLift pX' pY' a A V b) {V' : X'.Opens}
    (hV : V' ≤ V) : i ∣_ V' ≫ X'.homOfLE hV ≫ b = ((i ⁻¹ᵁ V').ι ≫ a) ≫ j := by
  obtain ⟨h, -⟩ := hb.2
  rw [← Category.assoc, morphismRestrict_homOfLE, Category.assoc, h, ← Category.assoc,
    ← Category.assoc, Scheme.homOfLE_ι]

end

/-- **The set of compatible lifts for first-order thickenings.** The set
`Stacks.Thickenings.compatibleLifts` when `i` and `j` are first-order thickenings in the sense of
[Stacks Project, Tag 04EX]. -/
@[stacks 04FI]
abbrev firstOrderCompatibleLifts (hi : IsFirstOrderThickening i)
    (hj : IsFirstOrderThickening j) (pX' : X' ⟶ S) (pY' : Y' ⟶ S) (a : X ⟶ Y)
    (A : letI := hi.1; letI := hj.1;
      (modulePullback a.toLRSHom.toShHom).obj (immersionConormalSheaf j) ⟶
        immersionConormalSheaf i)
    (V : X'.Opens) : Type u :=
  letI := hi.1
  letI := hj.1
  compatibleLifts pX' pY' a A V

end Stacks.Thickenings

end
