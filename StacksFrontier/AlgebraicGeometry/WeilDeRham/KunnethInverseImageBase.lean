module

public import StacksFrontier.AlgebraicGeometry.DeRham.InverseImageBaseChange
public import StacksFrontier.AlgebraicGeometry.DeRham.BoxTotalComparison
public import StacksFrontier.AlgebraicGeometry.DeRham.SmoothPulledBackFormsToTarget

/-!
# The projections of a fibre product, read over the base

A morphism of ringed spaces into an inverse-image ringed space `(Z, i^{-1}𝒪_X)` lying over `X` is
determined by its underlying continuous map (`AlgebraicGeometry.RingedSpace.inverseImage_hom_ext`).

The library writes the morphism of ringed spaces `(X ×_S Y, f^{-1}𝒪_S) ⟶ (X, a^{-1}𝒪_S)` over the
first projection in two ways: as `Stacks.Cohomology.BoxKunneth.fstProjection`, the one the box
product and the Künneth maps of [Stacks, Tag 0FLR] are formed along, and as
`Stacks.DeRhamBaseChange.inverseImageBaseMap` of the commutative square of the projection over the
identity of `S`, the one the pullback of de Rham cohomology is read along. Both lie over `S`, so
they agree.

## Main results

* `Stacks.WeilDeRham.inverseImageBaseMap_eq_relativeInverseImageProjection`: the morphism of
  inverse-image ringed spaces attached to the square of `g ≫ c` over the identity is the canonical
  one.
* `Stacks.WeilDeRham.inverseImageBaseMap_eq_fstProjection` and
  `Stacks.WeilDeRham.inverseImageBaseMap_eq_sndProjection`: the two projections of the fibre
  product, read over the base.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Stacks.DeRhamDirectImage

universe u

namespace Stacks.WeilDeRham

open Stacks.DeRhamBaseChange

variable {X W S : Scheme.{u}} (g : W ⟶ X) (c : X ⟶ S)

/-- A morphism of inverse-image ringed spaces over `g'` and over `S` is the one attached to the
square of `g'` over the identity of `S`. -/
private theorem inverseImageBaseMap_eq_of_base_of_comp {W' X' : Scheme.{u}} (g' : W' ⟶ X')
    (f' : W' ⟶ S) (c' : X' ⟶ S) (w : g' ≫ c' = f' ≫ 𝟙 S)
    (h : inverseImageBase f' ⟶ inverseImageBase c') (hb : h.hom.base = g'.base)
    (hc : h ≫ inverseImageBaseProjection c' = inverseImageBaseProjection f') :
    inverseImageBaseMap g' f' c' (𝟙 S) w = h := by
  refine RingedSpace.inverseImage_hom_ext S.toRingedSpace c'.base _ _ ?_ ?_
  · change 𝟙 _ ≫ g'.base = h.hom.base
    exact (Category.id_comp _).trans hb.symm
  · refine (inverseImageBaseMap_comp_inverseImageBaseProjection g' f' c' (𝟙 S) w).trans ?_
    exact (Category.comp_id _).trans hc.symm

/-- **The morphism of inverse-image ringed spaces attached to the square of `g ≫ c` over the
identity of `S` is the canonical morphism** `(W, (g ≫ c)^{-1}𝒪_S) ⟶ (X, c^{-1}𝒪_S)` over `g`.
Both have underlying map that of `g` and lie over `S`. -/
theorem inverseImageBaseMap_eq_relativeInverseImageProjection
    (w : g ≫ c = (g ≫ c) ≫ 𝟙 S) :
    inverseImageBaseMap g (g ≫ c) c (𝟙 S) w = relativeInverseImageProjection g c :=
  inverseImageBaseMap_eq_of_base_of_comp g _ c w _ rfl (relativeInverseImageProjection_comp g c)

/-- **A morphism of inverse-image ringed spaces over `g` and over `S` is the one attached to the
square of `g` over the identity of `S`.** -/
theorem inverseImageBaseMap_eq_of_comp {W' : Scheme.{u}} (g' : W' ⟶ X) (f' : W' ⟶ S)
    (w : g' ≫ c = f' ≫ 𝟙 S) (h : inverseImageBase f' ⟶ inverseImageBase c)
    (hb : h.hom.base = g'.base)
    (hc : h ≫ inverseImageBaseProjection c = inverseImageBaseProjection f') :
    inverseImageBaseMap g' f' c (𝟙 S) w = h :=
  inverseImageBaseMap_eq_of_base_of_comp g' f' c w h hb hc

/-- The transported canonical morphism has underlying map that of `p`. -/
theorem relativeInverseImageProjectionOfFactors_base {W' X' S' : Scheme.{u}} (p : W' ⟶ X')
    (c' : X' ⟶ S') (g'' : W' ⟶ S') (hg : p ≫ c' = g'') :
    (FiniteOrderDifferentialOperatorCategory.relativeInverseImageProjectionOfFactors
        p c' g'' hg).hom.base = p.base := by
  subst hg
  rfl

variable {Y : Scheme.{u}} (a : X ⟶ S) (b : Y ⟶ S)

/-- **The first projection of the fibre product, read over the base**, is the morphism of
inverse-image ringed spaces attached to the square of the first projection over the identity. -/
theorem inverseImageBaseMap_eq_fstProjection
    (w : pullback.fst a b ≫ a = (pullback.fst a b ≫ a) ≫ 𝟙 S) :
    inverseImageBaseMap (pullback.fst a b) (pullback.fst a b ≫ a) a (𝟙 S) w =
      Stacks.Cohomology.BoxKunneth.fstProjection a b :=
  inverseImageBaseMap_eq_of_comp a (pullback.fst a b) (pullback.fst a b ≫ a) w _ rfl
    (Stacks.Cohomology.BoxKunneth.fstProjection_comp a b)

/-- **The second projection of the fibre product, read over the base**, is the morphism of
inverse-image ringed spaces attached to the square of the second projection over the
identity. -/
theorem inverseImageBaseMap_eq_sndProjection
    (w : pullback.snd a b ≫ b = (pullback.fst a b ≫ a) ≫ 𝟙 S) :
    inverseImageBaseMap (pullback.snd a b) (pullback.fst a b ≫ a) b (𝟙 S) w =
      Stacks.Cohomology.BoxKunneth.sndProjection a b :=
  inverseImageBaseMap_eq_of_comp b (pullback.snd a b) (pullback.fst a b ≫ a) w _
    (relativeInverseImageProjectionOfFactors_base _ _ _ _)
    (Stacks.Cohomology.BoxKunneth.sndProjection_comp a b)

end Stacks.WeilDeRham

end
