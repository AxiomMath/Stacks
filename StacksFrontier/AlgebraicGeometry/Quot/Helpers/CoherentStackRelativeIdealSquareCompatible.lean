module

public import StacksFrontier.AlgebraicGeometry.Quot.Helpers.CoherentStackRelativeIdealSquareReduction
public import StacksFrontier.AlgebraicGeometry.Quot.Helpers.CoherentStackTestRelativeIdealSquare
public import StacksFrontier.AlgebraicGeometry.Quot.Helpers.RelativeThickeningTargetBridge
public import StacksFrontier.AlgebraicGeometry.Quot.Helpers.RelativeSquareIdealTransposeUnitStructureMap
public import StacksFrontier.AlgebraicGeometry.Quot.Helpers.SmallEtaleThickeningTargetJBridge

/-!
# The ideal-square compatibility of the relative squares of `Coh_{X/B}` from the ideal maps

For morphisms `h₁ : T ⟶ T'₁`, `h₂ : T ⟶ T'₂`, `g : T'₂ ⟶ T'₁` of affine first order thickenings
with `h₂ ≫ g = h₁`, the map `λ` of the pulled-back ideals of the relative squares
(`AlgebraicGeometry.Space.CoherentSituation.relativeSquareIdealMap`) satisfies the ideal-square
compatibility as soon as the map `f'₁^*𝒥₁ ⟶ j_*f'₂^*𝒥₂` of `κ_g` is `j^♯` on the ideals
(`AlgebraicGeometry.Space.CoherentSituation.relativeIdealSquareCompatible_of_comp_idealMap`), and
so for all affine first order thickenings
(`AlgebraicGeometry.Space.CoherentSituation.relativeIdealSquareCompatible_of_idealMaps`). The
reduction hypothesis is the cube comparison
`AlgebraicGeometry.Space.CoherentSituation.relativeSquareIdealMap_reduction`, read along `j = X_g`
by `Deformation.ToposThickening.ThickeningTargetMorphism.idealSquareCompatible_of_cube`.

## Implementation notes

The pieces of this proof reach it in different spellings, built through different definitions:
- objects through the abbrev `relativeSquareBasePullbackIdeal`, whose instance arguments are its
  auxiliary `_proof_i` lemmas, or through `basePullbackIdeal` with synthesized instances;
- adjunctions through the abbrev `spaceModuleAdj` or directly as
  `RingedToposHom.pullbackAdjPushforwardModules`;
- isomorphisms through `relativeSquareBasePullbackIdealIsoPullback` or
  `basePullbackIdealIsoPullback`;
- one `Quiver` instance through `catToReflQuiver`.

The two spellings of each piece are definitionally equal. But the kernel compares arguments first
only for definitions with regular reducibility hints; under projections such as `≫`, `Functor.map`
and `DFunLike.coe` it unfolds instead. An earlier proof identified these pieces inside composites
by `rfl`; its module check took 24 minutes on one fleet machine, most of it in the kernel.
`idealSquareCompatible_of_cube` therefore takes the cube equation with its left adjoints,
adjunctions, objects, isomorphisms and maps as variables, so that
`relativeSquareIdealMap_reduction` matches it syntactically, and identifies each piece on its
own. The direct images `i_*` and `φ_*` reach this proof in one spelling, so the lemma writes them
out.

The two spellings `f : X ⟶ Y` and `f' : X' ⟶ Y'` of a morphism have types that agree only up to
unfolding, so they are compared in the arrow category: `Arrow.mk f = Arrow.mk f'` is an equation
in one type, and `CategoryTheory.Arrow.mk` has regular reducibility hints, so the kernel checks
`rfl` at it by comparing `X`, `Y` and `f` with `X'`, `Y'` and `f'`, each at the top level. An
equation of arrows also identifies their ends, so of the objects of the cube only `A₂` needs an
equation of its own. Composites and images under functors are compared factor by factor
(`CategoryTheory.Arrow.mk_comp_eq_mk_comp`, `CategoryTheory.Arrow.mk_map_eq_mk_map_of_eq`); an
adjunction is identified by its unit, and an isomorphism by its forward map.

The ends of `Arrow.mk f` are implicit arguments, which unification fixes from the goal before it
reaches `f`. In `ν`, the ends of the arrow in the goal, from the type of
`relativeSquareIdealTranspose`, differ in instance proofs from the objects of the composite that
`relativeSquareIdealTranspose_eq` gives, so an instantiated `Arrow.mk_comp_eq_mk_comp` would
differ from the goal inside a composite, and the kernel would compare the two composites by
unfolding them and run out of heartbeats. The comparison of `ν` therefore starts by reading both
arrows through the identity functor (`Arrow.mk_map_eq_mk_map (𝟭 _)`), which gives each arrow the
ends of its own composite.

## References

* [Stacks Project, Tag 08WA](https://stacks.math.columbia.edu/tag/08WA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Sheaves.ToposPushforward (pushforwardCommRingFunctor pushforwardModuleFunctor)
open Deformation.ToposThickening
open Stacks.Sheaves.RingedToposModules.RingedToposHom (pullbackModules)

/-! The three lemmas below are general facts about the arrow category; they belong next to
`CategoryTheory.Arrow.mk_eq_mk_iff` in Mathlib's `Mathlib/CategoryTheory/Comma/Arrow.lean`. -/

namespace CategoryTheory.Arrow

variable {C : Type*} [Category C]

/-- Composites of morphisms that are equal in the arrow category are equal in the arrow category.
The objects of the two composites are separate implicit arguments, so that the conclusion unifies
with composites written in different spellings. -/
theorem mk_comp_eq_mk_comp {X Y Z X' Y' Z' : C} {f : X ⟶ Y} {g : Y ⟶ Z} {f' : X' ⟶ Y'}
    {g' : Y' ⟶ Z'} (hf : Arrow.mk f = Arrow.mk f') (hg : Arrow.mk g = Arrow.mk g') :
    Arrow.mk (f ≫ g) = Arrow.mk (f' ≫ g') := by
  obtain ⟨rfl, rfl, rfl⟩ := (Arrow.mk_eq_mk_iff f f').1 hf
  obtain ⟨-, rfl, rfl⟩ := (Arrow.mk_eq_mk_iff g g').1 hg
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]

variable {D : Type*} [Category D]

/-- A functor carries morphisms that are equal in the arrow category to morphisms that are equal in
the arrow category: `Functor.mapArrow` applied to the equation. -/
theorem mk_map_eq_mk_map (F : C ⥤ D) {X Y X' Y' : C} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    (h : Arrow.mk f = Arrow.mk f') : Arrow.mk (F.map f) = Arrow.mk (F.map f') :=
  congrArg F.mapArrow.obj h

/-- Equal functors carry morphisms that are equal in the arrow category to morphisms that are
equal in the arrow category. The functors are separate implicit arguments, so that the conclusion
unifies with images under functors written in different spellings, which `hF` then compares. -/
theorem mk_map_eq_mk_map_of_eq {F F' : C ⥤ D} {X Y X' Y' : C} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    (hF : F = F') (h : Arrow.mk f = Arrow.mk f') : Arrow.mk (F.map f) = Arrow.mk (F'.map f') := by
  subst hF
  exact mk_map_eq_mk_map F h

end CategoryTheory.Arrow

universe u

namespace AlgebraicGeometry.Space.CoherentSituation

/-! Instance search on the small étale sites finds the generic sheafification instances at the
universe `max (u + 1) ?u` and gets stuck on the universe constraint, so the first two shortcuts are
needed. The three `HasSheafCompose` shortcuts are there for speed: without them
`relativeIdealSquareCompatible_of_comp_idealMap` costs about four times as many heartbeats
(212,000 against 55,000). -/
attribute [local instance 10000] smallEtaleRingedTopos_hasSheafify_addCommGrpCat
  smallEtaleRingedTopos_wEqualsLocallyBijective_addCommGrpCat
  smallEtaleRingedTopos_hasSheafCompose_forget_ringCat
  smallEtaleRingedTopos_hasSheafCompose_forget₂_commRingCat
  smallEtaleRingedTopos_hasSheafCompose_forget_addCommGrpCat

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {D : CoherentSituation B S hS}
  {ξ : CoherentObject D} {T'₁ T'₂ : SchemesOver D.Y} (h₁ : ξ.T ⟶ T'₁) (h₂ : ξ.T ⟶ T'₂)
  (g : T'₂ ⟶ T'₁) (hg : h₂ ≫ g = h₁)
  (hh₁ : Stacks.Thickenings.IsFirstOrderThickening ((BigFppfOver.toScheme B S hS).map h₁.left))
  (hh₂ : Stacks.Thickenings.IsFirstOrderThickening ((BigFppfOver.toScheme B S hS).map h₂.left))
  [IsAffine ((BigFppfOver.toScheme B S hS).obj ξ.T.left)]
  [IsAffine ((BigFppfOver.toScheme B S hS).obj T'₁.left)]
  [IsAffine ((BigFppfOver.toScheme B S hS).obj T'₂.left)]

variable (hfl₁ : IsFlat B S hS (D.projection T'₁).hom) (hfl₂ : IsFlat B S hS (D.projection T'₂).hom)

/-- **The ideal-square compatibility of `λ` from the ideal maps.** If the map
`f'₁^*𝒥₁ ⟶ j_*f'₂^*𝒥₂` of `κ_g` is `j^♯` on the ideals
(`AlgebraicGeometry.Space.CoherentSituation.RelativeSquareIdealTransposeIdealMaps`), then
`AlgebraicGeometry.Space.CoherentSituation.relativeSquareIdealMap` satisfies the ideal-square
compatibility of the relative squares of `h₁` and `h₂`. -/
theorem relativeIdealSquareCompatible_of_comp_idealMap
    (H₁ : RelativeSquareIdealTransposeIdealMaps h₁ h₂ g hg hh₁ hh₂) :
    RelativeIdealSquareCompatible h₁ h₂ g hg hh₁ hh₂ hfl₁ hfl₂
      (relativeSquareIdealMap h₁ h₂ g hg hh₁ hh₂) := by
  refine ThickeningTargetMorphism.idealSquareCompatible_of_cube
    (relativeThickeningTarget h₁ h₂ g hg)
    (D.relativeSquareSituation.relativeMapFirstOrderThickening h₁ hh₁)
    (D.relativeSquareSituation.relativeMapFirstOrderThickening h₂ hh₂)
    (D.relativeSquareSituation.relativeSquareThickening h₁)
    (D.relativeSquareSituation.relativeSquareLeft h₁)
    (relBaseRight (smallEtaleRingedToposHom B S hS (D.relativeSquareSituation.projection T'₁)))
    (D.relativeSquareSituation.relativeSquareThickeningFirstOrderThickening h₁ hh₁)
    -- `comm`, `hf'` and `hstrict` are filled from the goal: written out, the six of them add
    -- about 55 seconds to the elaboration of this `refine` (each `hf'` about 10 seconds, its
    -- `RingedToposHom.IsFlat` statement being compared by unfolding).
    _ _ _
    (D.relativeSquareSituation.relativeSquareThickening h₂)
    (D.relativeSquareSituation.relativeSquareLeft h₂)
    (relBaseRight (smallEtaleRingedToposHom B S hS (D.relativeSquareSituation.projection T'₂)))
    (D.relativeSquareSituation.relativeSquareThickeningFirstOrderThickening h₂ hh₂)
    _ _ _
    (smallEtaleThickenedModulesCompIso (D.relativeSquareSituation.relativeMap h₂)
      (D.relativeSquareSituation.relativeMap g) (D.relativeSquareSituation.relativeMap h₁)
      (relativeMap_comp_of_comp_eq g hg))
    (smallEtaleRingedToposHom B S hS (D.relativeSquareSituation.relativeMap g))
    (relativeThickeningTarget_j h₁ h₂ g hg)
    (relativeSquareIdealMap h₁ h₂ g hg hh₁ hh₂) ?ν ?c ?hc ?H₁
    (relativeSquareIdealMap_reduction h₁ h₂ g hg hh₁ hh₂)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?hm ?hν ?hc'
  case ν => exact relativeSquareIdealTranspose h₁ h₂ g hg hh₁ hh₂
  case c =>
    exact (modulePushforwardCompIsoOfEq (D.relativeSquareSituation.relativeMap h₂)
      (D.relativeSquareSituation.relativeMap g) (D.relativeSquareSituation.relativeMap h₁)
      (relativeMap_comp_of_comp_eq g hg)).hom.app _
  case hc =>
    exact restrictIso_hom_comp_map_smallEtaleThickenedModulesCompIso_hom_app_eq_eqToHom_comp
      (D.relativeSquareSituation.relativeMap h₂) (D.relativeSquareSituation.relativeMap g)
      (D.relativeSquareSituation.relativeMap h₁) (relativeMap_comp_of_comp_eq g hg) _
  case H₁ =>
    exact relativeSquareIdealTranspose_comp_map_eq_comp_unitStructureMap h₁ h₂ g hg hh₁ hh₂ H₁
  case hm =>
    refine Eq.trans ?_ (congrArg Arrow.mk (relativeSquareIdealMap_eq h₁ h₂ g hg hh₁ hh₂).symm)
    refine Arrow.mk_comp_eq_mk_comp rfl (Arrow.mk_comp_eq_mk_comp ?_ rfl)
    exact Arrow.mk_map_eq_mk_map_of_eq rfl rfl
  case hν =>
    refine Eq.trans ?_ (congrArg Arrow.mk (relativeSquareIdealTranspose_eq h₁ h₂ g hg hh₁ hh₂).symm)
    unfold cubeIdealTranspose isoConjugateMap
    -- Each arrow takes the ends of its own composite. Without this step the kernel compares the
    -- two composites by unfolding them and runs out of heartbeats: about 1,960,000 for this
    -- theorem, against 55,000 with it (see the implementation notes).
    apply Arrow.mk_map_eq_mk_map (𝟭 _)
    refine Arrow.mk_comp_eq_mk_comp rfl ?_
    refine Arrow.mk_comp_eq_mk_comp rfl ?_
    refine Arrow.mk_comp_eq_mk_comp rfl ?_
    refine Arrow.mk_comp_eq_mk_comp rfl ?_
    refine Arrow.mk_map_eq_mk_map_of_eq rfl ?_
    exact Arrow.mk_comp_eq_mk_comp rfl (Arrow.mk_comp_eq_mk_comp rfl rfl)
  case hc' =>
    -- `c'` and `c` are components of one transformation at two spellings of one object; through
    -- `congrArg`, only the two spellings of the object are compared.
    exact congrArg (fun N => Arrow.mk ((modulePushforwardCompIsoOfEq
      (D.relativeSquareSituation.relativeMap h₂) (D.relativeSquareSituation.relativeMap g)
      (D.relativeSquareSituation.relativeMap h₁) (relativeMap_comp_of_comp_eq g hg)).hom.app N))
      rfl
  -- The seven identifications of the pieces, `hL₁` to `hBi₂`, by `rfl`.
  all_goals rfl

omit [IsAffine ((BigFppfOver.toScheme B S hS).obj ξ.T.left)]
  [IsAffine ((BigFppfOver.toScheme B S hS).obj T'₁.left)]
  [IsAffine ((BigFppfOver.toScheme B S hS).obj T'₂.left)] in
/-- **The ideal-square compatibility of `λ` from the ideal maps, for all affine first order
thickenings.** The property
`AlgebraicGeometry.Space.CoherentSituation.RelativeIdealSquareCompatibleOfIdealMaps` holds for `D`:
`AlgebraicGeometry.Space.CoherentSituation.relativeIdealSquareCompatible_of_comp_idealMap` holds at
each morphism of affine first order thickenings. -/
theorem relativeIdealSquareCompatible_of_idealMaps (D : CoherentSituation B S hS) :
    RelativeIdealSquareCompatibleOfIdealMaps D :=
  fun h₁ h₂ g hg hh₁ hh₂ _ _ _ hfl₁ hfl₂ H =>
    relativeIdealSquareCompatible_of_comp_idealMap h₁ h₂ g hg hh₁ hh₂ hfl₁ hfl₂ H

end AlgebraicGeometry.Space.CoherentSituation
