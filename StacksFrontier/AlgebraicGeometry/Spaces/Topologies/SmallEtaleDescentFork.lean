module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleBaseChange

/-!
# Restricting the direct image of a small étale pullback along a further morphism (Stacks 0DFX)

Let `f : Y ⟶ X` be a morphism of algebraic spaces over a scheme `S` and let `F` be a sheaf on
the small étale site of `X`. The unit of the adjunction `f⁻¹ ⊣ f_*` of Stacks 03G2, part (3),
is a map `F ⟶ f_*f⁻¹F`. For a further morphism `p : P ⟶ Y` there is a canonical restriction
map `f_*f⁻¹F ⟶ (p ≫ f)_*(p ≫ f)⁻¹F`, obtained by applying `f_*` to the unit of `p`, and the
unit of `p ≫ f` factors through it.

Stacks 0DFX asserts, for `f` surjective and proper, that `F ⟶ f_*f⁻¹F` is injective and
exhibits `F` as the equalizer of the two restrictions to `Y ×_X Y`. This module supplies the
restriction map and the clause that the unit equalizes those two restrictions. Injectivity and
the equalizer property are *not* proved here; see the implementation notes.

## Main definitions

* `AlgebraicGeometry.Space.smallToposDescentMap`: the restriction map
  `f_*f⁻¹F ⟶ (p ≫ f)_*(p ≫ f)⁻¹F`.

## Main results

* `AlgebraicGeometry.Space.unit_comp_smallToposDescentMap`: **Stacks 0DFX**, the unit of `f`
  followed by the restriction along `p` is the unit of `p ≫ f`. This is the clause that the
  unit equalizes the two restrictions to a self-intersection.
* `AlgebraicGeometry.Space.homEquiv_symm_comp_smallToposDescentMap`: the adjoint transpose of
  a map composed with the restriction is the transpose of the map, pushed along `p⁻¹` and
  conjugated by the inverse-image comparison of Stacks 03G2, part (3).

## Implementation notes

The source phrases the equalizer clause as equality of the two composites
`F ⟶ f_*f⁻¹F ⟶ (pᵢ ≫ f)_*(pᵢ ≫ f)⁻¹F` for the two projections `p₁, p₂ : Y ×_X Y ⟶ Y`. Those
two composites do not literally have the same type: `p₁ ≫ f` and `p₂ ≫ f` agree only
propositionally, by the cartesian square, so the two targets are equal objects of the topos of
`X` but not definitionally equal ones, and the equality as stated carries a transport along
that square. `AlgebraicGeometry.Space.unit_comp_smallToposDescentMap` avoids the transport and
is stronger: it identifies *each* composite with the unit of the corresponding composite
morphism, for an arbitrary `p`, so the two agree as soon as `p₁ ≫ f = p₂ ≫ f`, which is the
content of the clause and is exactly what the cartesian square gives.

Neither injectivity of the unit nor the equalizer property is proved here, and neither can be
on this branch. Injectivity is checked on stalks at geometric points and needs the
characterization of surjectivity by geometric points, Stacks 0487. The equalizer property
needs the descent equivalence for the pullback system of small étale sheaves along a
surjective proper morphism, Stacks 0GFW. Neither statement is available in this repository.

## References

* [Stacks Project, Tag 0DFX](https://stacks.math.columbia.edu/tag/0DFX)
* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The canonical restriction map from `f_*f⁻¹F` to `(p ≫ f)_*(p ≫ f)⁻¹F`: apply `f_*` to the
adjunction unit of `p`, then compare the direct and inverse images of the composite `p ≫ f`
with those of `p` and `f` by the coherences of Stacks 03G2, part (3). -/
public noncomputable def smallToposDescentMap {P Y X : AlgebraicSpaces B S hS}
    (p : P ⟶ Y) (f : Y ⟶ X)
    (F : Sheaf (SmallEtale.topology B S hS X.1) (Type (u + 1))) :
    (smallToposMorphism B S hS f).pushforward.obj
        ((smallToposMorphism B S hS f).inverseImage.obj F) ⟶
      (smallToposMorphism B S hS (p ≫ f)).pushforward.obj
        ((smallToposMorphism B S hS (p ≫ f)).inverseImage.obj F) :=
  let mp := smallToposMorphism B S hS p
  let mf := smallToposMorphism B S hS f
  let mg := smallToposMorphism B S hS (p ≫ f)
  mf.pushforward.map (mp.adj.unit.app (mf.inverseImage.obj F)) ≫
    (smallToposMorphism_comp B S hS p f).hom.app
      (mp.inverseImage.obj (mf.inverseImage.obj F)) ≫
    mg.pushforward.map ((smallToposMorphism_comp_inverseImage B S hS p f).inv.app F)

/-- **Stacks 0DFX.** The unit of `f` followed by the restriction along `p` is the unit of
`p ≫ f`.

Applied to the two projections `p₁, p₂ : Y ×_X Y ⟶ Y` of a self-intersection, where
`p₁ ≫ f = p₂ ≫ f`, this says that the unit equalizes the two restrictions to `Y ×_X Y`. -/
@[stacks 0DFX "the unit equalizes the two restrictions"]
theorem unit_comp_smallToposDescentMap {P Y X : AlgebraicSpaces B S hS}
    (p : P ⟶ Y) (f : Y ⟶ X)
    (F : Sheaf (SmallEtale.topology B S hS X.1) (Type (u + 1))) :
    (smallToposMorphism B S hS f).adj.unit.app F ≫ smallToposDescentMap B S hS p f F =
      (smallToposMorphism B S hS (p ≫ f)).adj.unit.app F := by
  let mp := smallToposMorphism B S hS p
  let mf := smallToposMorphism B S hS f
  let mg := smallToposMorphism B S hS (p ≫ f)
  let c := smallToposMorphism_comp_inverseImage B S hS p f
  let d := smallToposMorphism_comp B S hS p f
  let K := mf.inverseImage ⋙ mp.inverseImage
  let G := mg.inverseImage.obj F
  have hm := smallToposMorphism_comp_mate B S hS p f F G (c.inv.app F)
  have hcmap : mg.pushforward.map (c.hom.app F ≫ c.inv.app F) =
      𝟙 (mg.pushforward.obj G) := by
    rw [c.hom_inv_id_app, mg.pushforward.map_id]
  have hnat' : (mp.pushforward ⋙ mf.pushforward).map (c.inv.app F) ≫
      d.hom.app G = d.hom.app (K.obj F) ≫ mg.pushforward.map (c.inv.app F) := by
    simpa [MorphismOfTopoi.comp, Functor.comp_obj, G, K] using d.hom.naturality (c.inv.app F)
  have hηid : mg.adj.unit.app F ≫ 𝟙 (mg.pushforward.obj G) =
      mg.adj.unit.app F :=
    Category.comp_id _
  have hm' : mg.adj.unit.app F =
      mf.adj.unit.app F ≫
        mf.pushforward.map (mp.adj.unit.app (mf.inverseImage.obj F)) ≫
        d.hom.app (K.obj F) ≫ mg.pushforward.map (c.inv.app F) := by
    rw [Adjunction.homEquiv_unit] at hm
    change mg.adj.unit.app F ≫ mg.pushforward.map (c.hom.app F ≫ c.inv.app F) =
      ((mf.adj.comp mp.adj).homEquiv F G (c.inv.app F)) ≫ d.hom.app G at hm
    rw [hcmap, hηid, Adjunction.homEquiv_unit, Adjunction.comp_unit_app] at hm
    calc
      mg.adj.unit.app F =
          (((mf.adj.unit.app F ≫
            mf.pushforward.map (mp.adj.unit.app (mf.inverseImage.obj F))) ≫
            (mp.pushforward ⋙ mf.pushforward).map (c.inv.app F)) ≫ d.hom.app G) := by
              simpa only [Functor.comp_obj] using hm
      _ = (mf.adj.unit.app F ≫
            mf.pushforward.map (mp.adj.unit.app (mf.inverseImage.obj F))) ≫
            ((mp.pushforward ⋙ mf.pushforward).map (c.inv.app F) ≫ d.hom.app G) :=
              Category.assoc _ _ _
      _ = (mf.adj.unit.app F ≫
            mf.pushforward.map (mp.adj.unit.app (mf.inverseImage.obj F))) ≫
            (d.hom.app (K.obj F) ≫ mg.pushforward.map (c.inv.app F)) := by
              rw [hnat']
              exact Category.assoc _ _ _
      _ = mf.adj.unit.app F ≫
            (mf.pushforward.map (mp.adj.unit.app (mf.inverseImage.obj F)) ≫
              (d.hom.app (K.obj F) ≫ mg.pushforward.map (c.inv.app F))) :=
              Category.assoc _ _ _
  simpa [smallToposDescentMap, MorphismOfTopoi.comp, K] using hm'.symm

/-- The adjoint transpose of a map into `f_*f⁻¹F` composed with the restriction along `p` is
the transpose of the map, pushed along `p⁻¹` and conjugated by the inverse-image comparison of
Stacks 03G2, part (3). -/
theorem homEquiv_symm_comp_smallToposDescentMap {P Y X : AlgebraicSpaces B S hS}
    (p : P ⟶ Y) (f : Y ⟶ X)
    (F G : Sheaf (SmallEtale.topology B S hS X.1) (Type (u + 1)))
    (k : G ⟶ (smallToposMorphism B S hS f).pushforward.obj
      ((smallToposMorphism B S hS f).inverseImage.obj F)) :
    ((smallToposMorphism B S hS (p ≫ f)).adj.homEquiv G
          ((smallToposMorphism B S hS (p ≫ f)).inverseImage.obj F)).symm
        (k ≫ smallToposDescentMap B S hS p f F) =
      (smallToposMorphism_comp_inverseImage B S hS p f).hom.app G ≫
        (smallToposMorphism B S hS p).inverseImage.map
          (((smallToposMorphism B S hS f).adj.homEquiv G
            ((smallToposMorphism B S hS f).inverseImage.obj F)).symm k) ≫
        (smallToposMorphism_comp_inverseImage B S hS p f).inv.app F := by
  let mp := smallToposMorphism B S hS p
  let mf := smallToposMorphism B S hS f
  let mg := smallToposMorphism B S hS (p ≫ f)
  let c := smallToposMorphism_comp_inverseImage B S hS p f
  let d := smallToposMorphism_comp B S hS p f
  let B₀ := mp.inverseImage.obj (mf.inverseImage.obj F)
  let δ := (mf.adj.homEquiv G (mf.inverseImage.obj F)).symm k
  let base := k ≫ mf.pushforward.map (mp.adj.unit.app (mf.inverseImage.obj F))
  have hmf : (mf.adj.homEquiv G (mp.pushforward.obj B₀)).symm base =
      δ ≫ mp.adj.unit.app (mf.inverseImage.obj F) :=
    mf.adj.homEquiv_naturality_right_symm k (mp.adj.unit.app (mf.inverseImage.obj F))
  have htranspose : ((mf.adj.comp mp.adj).homEquiv G B₀).symm base =
      mp.inverseImage.map δ := by
    dsimp [base, B₀, δ]
    rw [Adjunction.comp_homEquiv]
    change (mp.adj.homEquiv _ _).symm ((mf.adj.homEquiv _ _).symm base) = _
    rw [hmf, Adjunction.homEquiv_naturality_left_symm, Adjunction.homEquiv_symm_unit,
      Category.comp_id]
  have hmateComp : (mf.adj.comp mp.adj).homEquiv G B₀ (mp.inverseImage.map δ) = base :=
    (Equiv.eq_symm_apply _).1 htranspose.symm
  have hmate' : (mg.adj.homEquiv G B₀) (c.hom.app G ≫ mp.inverseImage.map δ) =
      base ≫ d.hom.app B₀ := by
    simpa [MorphismOfTopoi.comp] using
      (smallToposMorphism_comp_mate B S hS p f G B₀ (mp.inverseImage.map δ)).trans
        (congrArg (· ≫ d.hom.app B₀) hmateComp)
  calc
    (mg.adj.homEquiv G (mg.inverseImage.obj F)).symm
        (k ≫ smallToposDescentMap B S hS p f F) =
      (mg.adj.homEquiv G B₀).symm (base ≫ d.hom.app B₀) ≫ c.inv.app F := by
        dsimp [smallToposDescentMap, base, B₀, c, d, mg, mf, mp]
        exact mg.adj.homEquiv_naturality_right_symm
          (base ≫ d.hom.app B₀) (c.inv.app F)
    _ = c.hom.app G ≫ mp.inverseImage.map δ ≫ c.inv.app F := by
      rw [← hmate', Equiv.symm_apply_apply, Category.assoc]

end AlgebraicGeometry.Space

end
