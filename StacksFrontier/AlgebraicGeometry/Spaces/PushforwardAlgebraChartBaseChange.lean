module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineAlgebraAntiEquivalence
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePushforwardChartComparison

/-!
# The direct image of the structure sheaf along a representable morphism, as an algebra sheaf

Let `g : Y ⟶ X` be a *representable* morphism of algebraic spaces over a scheme `S`.  Two
`𝒪_X`-algebras are attached to it:

* `AlgebraicGeometry.Space.pushforwardAlgebra`, the direct image `g_* 𝒪_Y`, whose structure map
  is the `fSharp` field of the morphism of small étale ringed topoi of Stacks 03G8;
* the *explicit* chart-base-change algebra, whose sheaf of rings is the restriction of `𝒪_Y`
  along `AlgebraicGeometry.Space.smallBaseChange` and whose structure map is
  `AlgebraicGeometry.Space.smallBaseChangeSharpCommRingCat`, pullback of regular functions along
  the cartesian projection `V ×_X Y ⟶ V`.

This file identifies them, as objects of `AlgebraicGeometry.Space.AlgebraSheaf`:
`AlgebraicGeometry.Space.chartSharpAlgebraIso`.

## Main definitions

* `AlgebraicGeometry.Space.chartSharpRingHom`: the comparison of `g_* 𝒪_Y` with restriction
  along chart base change as sheaves of rings.
* `AlgebraicGeometry.Space.chartSharpCommRingHom` and
  `AlgebraicGeometry.Space.chartSharpCommRingIso`: the same comparison on sheaves of commutative
  rings, as a morphism and as an isomorphism.
* `AlgebraicGeometry.Space.chartSharpAlgebraIso`: `g_* 𝒪_Y` is the explicit chart-base-change
  algebra, for every representable `g`.

## Main results

* `AlgebraicGeometry.Space.structureSharp_comp_chartSharpRingHom`: the structure map of
  Stacks 03G8, read through the comparison, is
  `AlgebraicGeometry.Space.smallBaseChangeSharp`.
* `AlgebraicGeometry.Space.hom_comp_chartSharpCommRingHom`: the same on sheaves of commutative
  rings.

## References

* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2)
* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8)
* [Stacks Project, Tag 081V](https://stacks.math.columbia.edu/tag/081V)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Sheaves.ToposPullback

universe u

attribute [local instance] AlgebraicGeometry.Space.isContinuous_smallBaseChange

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X : AlgebraicSpaces B S hS}

set_option synthInstance.maxHeartbeats 400000 in
-- `inferInstance` for `PreservesFiniteProducts` of the sheaf pushforward along the chart
/-- Restriction of sheaves of sets along chart base change preserves finite products (instance
search times out finding this at its use sites). -/
instance preservesFiniteProducts_smallBaseChange_pushforwardAlgebraChartBaseChange
    (g : Over X) (hg : yoneda.relativelyRepresentable g.hom.hom) :
    PreservesFiniteProducts ((smallBaseChange B S hS g.hom hg).sheafPushforwardContinuous
      (Type u) (SmallEtale.topology B S hS X.1) (SmallEtale.topology B S hS g.left.1)) :=
  inferInstance

/-! ### The comparison on sheaves of rings -/

/-- **The direct image `g_* 𝒪_Y` of sheaves of rings is restriction along chart base change**,
for a representable `g`. -/
def chartSharpRingHom (g : Over X) (hg : yoneda.relativelyRepresentable g.hom.hom) :
    structureRingSheafDirectImage B S hS g.hom ⟶
      ((smallBaseChange B S hS g.hom hg).sheafPushforwardContinuous RingCat.{u}
        (SmallEtale.topology B S hS X.1) (SmallEtale.topology B S hS g.left.1)).obj
        (structureRingSheaf B S hS g.left) :=
  pullbackRingSheafMapOfNatTrans (SmallEtale.topology B S hS X.1)
      (structureRingSheaf B S hS g.left)
      (smallEtaleDirectImageRanIso B S hS g.hom ≪≫ chartRanIso B S hS g.hom hg).hom ≫
    (restrictionRingIso (SmallEtale.topology B S hS X.1)
      (SmallEtale.topology B S hS g.left.1) (smallBaseChange B S hS g.hom hg)
      (structureRingSheaf B S hS g.left)).hom

/-- **The structure map of Stacks 03G8, read through the comparison, is pullback of regular
functions along the cartesian projection.** -/
theorem structureSharp_comp_chartSharpRingHom (g : Over X)
    (hg : yoneda.relativelyRepresentable g.hom.hom) :
    structureSharp B S hS g.hom ≫ chartSharpRingHom B S hS g hg =
      smallBaseChangeSharp B S hS g.hom hg := by
  rw [chartSharpRingHom, ← Category.assoc]
  exact structureSharp_comp_chartRanIso B S hS g.hom hg

/-- The comparison of sheaves of rings is an isomorphism. -/
instance isIso_chartSharpRingHom (g : Over X)
    (hg : yoneda.relativelyRepresentable g.hom.hom) :
    IsIso (chartSharpRingHom B S hS g hg) := by
  rw [chartSharpRingHom]
  have : IsIso (pullbackRingSheafMapOfNatTrans (SmallEtale.topology B S hS X.1)
      (structureRingSheaf B S hS g.left)
      (smallEtaleDirectImageRanIso B S hS g.hom ≪≫ chartRanIso B S hS g.hom hg).hom) := by
    refine ⟨pullbackRingSheafMapOfNatTrans (SmallEtale.topology B S hS X.1)
      (structureRingSheaf B S hS g.left)
      (smallEtaleDirectImageRanIso B S hS g.hom ≪≫ chartRanIso B S hS g.hom hg).inv, ?_, ?_⟩
    · rw [pullbackRingSheafMapOfNatTrans_comp, Iso.hom_inv_id]; rfl
    · rw [pullbackRingSheafMapOfNatTrans_comp, Iso.inv_hom_id]; rfl
  infer_instance

/-! ### The comparison on sheaves of commutative rings -/

/-- **The direct image `g_* 𝒪_Y` of sheaves of *commutative* rings is restriction along chart
base change.** -/
def chartSharpCommRingHom (g : Over X) (hg : yoneda.relativelyRepresentable g.hom.hom) :
    (pushforwardAlgebra B S hS g).right ⟶
      ((smallBaseChange B S hS g.hom hg).sheafPushforwardContinuous CommRingCat.{u}
        (SmallEtale.topology B S hS X.1) (SmallEtale.topology B S hS g.left.1)).obj
        (structureSheaf B S hS g.left.1 g.left.2) :=
  (fullyFaithfulForgetCommRingSheaf.{u, u, u + 1}
    (SmallEtale.topology B S hS X.1)).preimage (chartSharpRingHom B S hS g hg)

/-- Forgetting commutativity in the comparison returns the comparison of sheaves of rings. -/
theorem map_chartSharpCommRingHom (g : Over X)
    (hg : yoneda.relativelyRepresentable g.hom.hom) :
    (sheafCompose (SmallEtale.topology B S hS X.1)
          (forget₂ CommRingCat.{u} RingCat.{u})).map (chartSharpCommRingHom B S hS g hg) =
      chartSharpRingHom B S hS g hg :=
  (fullyFaithfulForgetCommRingSheaf.{u, u, u + 1}
    (SmallEtale.topology B S hS X.1)).map_preimage _

/-- The comparison of sheaves of commutative rings is an isomorphism. -/
instance isIso_chartSharpCommRingHom (g : Over X)
    (hg : yoneda.relativelyRepresentable g.hom.hom) :
    IsIso (chartSharpCommRingHom B S hS g hg) := by
  have h : IsIso ((sheafCompose (SmallEtale.topology B S hS X.1)
      (forget₂ CommRingCat.{u} RingCat.{u})).map (chartSharpCommRingHom B S hS g hg)) := by
    rw [map_chartSharpCommRingHom]
    exact isIso_chartSharpRingHom B S hS g hg
  exact (fullyFaithfulForgetCommRingSheaf.{u, u, u + 1}
    (SmallEtale.topology B S hS X.1)).isIso_of_isIso_map _

/-- `AlgebraicGeometry.Space.chartSharpCommRingHom` as an isomorphism. -/
def chartSharpCommRingIso (g : Over X) (hg : yoneda.relativelyRepresentable g.hom.hom) :
    (pushforwardAlgebra B S hS g).right ≅
      ((smallBaseChange B S hS g.hom hg).sheafPushforwardContinuous CommRingCat.{u}
        (SmallEtale.topology B S hS X.1) (SmallEtale.topology B S hS g.left.1)).obj
        (structureSheaf B S hS g.left.1 g.left.2) :=
  @asIso _ _ _ _ (chartSharpCommRingHom B S hS g hg) (isIso_chartSharpCommRingHom B S hS g hg)

/-! ### Compatibility with the structure-algebra map -/

/-- **The structure-algebra map of `g_* 𝒪_Y`, read through the comparison, is
`AlgebraicGeometry.Space.smallBaseChangeSharpCommRingCat`**: pullback of regular functions along
the cartesian projection of chart base change. -/
theorem hom_comp_chartSharpCommRingHom (g : Over X)
    (hg : yoneda.relativelyRepresentable g.hom.hom) :
    (pushforwardAlgebra B S hS g).hom ≫ chartSharpCommRingHom B S hS g hg =
      smallBaseChangeSharpCommRingCat B S hS g.hom hg := by
  refine (fullyFaithfulForgetCommRingSheaf.{u, u, u + 1}
    (SmallEtale.topology B S hS X.1)).map_injective ?_
  rw [Functor.map_comp, map_chartSharpCommRingHom]
  exact (congrArg (fun t => t ≫ chartSharpRingHom B S hS g hg)
    (forgetCommRingSheaf_map_fSharp B S hS g.hom)).trans
      (structureSharp_comp_chartSharpRingHom B S hS g hg)

/-- The comparison carries the structure-algebra map of `g_* 𝒪_Y` to that of the explicit
chart-base-change algebra, on sections over every étale chart. -/
theorem chartSharpCommRingHom_comm (g : Over X)
    (hg : yoneda.relativelyRepresentable g.hom.hom) (U : (SmallEtale B S hS X.1)ᵒᵖ)
    (r : (structureSheaf B S hS X.1 X.2).obj.obj U) :
    (chartSharpCommRingHom B S hS g hg).hom.app U
        ((pushforwardAlgebra B S hS g).algebraMap U r) =
      (AlgebraSheaf.ofHom (smallBaseChangeSharpCommRingCat B S hS g.hom hg)).algebraMap U r :=
  ConcreteCategory.congr_hom
    (congrArg (fun t : structureSheaf B S hS X.1 X.2 ⟶ _ => t.hom.app U)
      (hom_comp_chartSharpCommRingHom B S hS g hg)) r

/-- For a representable `g : Y ⟶ X` the direct image `g_* 𝒪_Y` is the explicit algebra whose
sections over an étale chart `V` of `X` are the regular functions on the base-changed chart
`V ×_X Y` and whose structure map is pullback along the cartesian projection. -/
def chartSharpAlgebraIso (g : Over X) (hg : yoneda.relativelyRepresentable g.hom.hom) :
    pushforwardAlgebra B S hS g ≅
      AlgebraSheaf.ofHom (smallBaseChangeSharpCommRingCat B S hS g.hom hg) where
  hom := ⟨(chartSharpCommRingIso B S hS g hg).hom, chartSharpCommRingHom_comm B S hS g hg⟩
  inv := ⟨(chartSharpCommRingIso B S hS g hg).inv, fun U r =>
    (congrArg _ (chartSharpCommRingHom_comm B S hS g hg U r).symm).trans <|
      ConcreteCategory.congr_hom
        (congrArg (fun t : (pushforwardAlgebra B S hS g).right ⟶ _ => t.hom.app U)
          (chartSharpCommRingIso B S hS g hg).hom_inv_id) _⟩
  hom_inv_id := AlgebraSheaf.Hom.ext (chartSharpCommRingIso B S hS g hg).hom_inv_id
  inv_hom_id := AlgebraSheaf.Hom.ext (chartSharpCommRingIso B S hS g hg).inv_hom_id

end AlgebraicGeometry.Space

end
