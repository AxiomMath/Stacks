module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalModuleBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalModuleBaseChangeFlat
public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalModuleComposition
public import StacksFrontier.AlgebraicGeometry.Spaces.CoveringComparisonTopologies
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.QuasiCoherent.HomDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.FibreProduct
public import StacksFrontier.AlgebraicGeometry.Spaces.FpqcMorphismDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleFlatTopos
public import StacksFrontier.AlgebraicGeometry.Spaces.SpacesEtaleBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.LiftingSheaf
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.SpacesEtaleCovering
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.SpacesEtaleSliceSite
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.SpacesEtaleStructureSheaf

/-!
# The sheaf of lifts cut out by conditions (1) and (2)

This file proves that the morphisms into a fixed algebraic space form a sheaf on the
spaces-étale site, defines the thickening `X ×_{X'} U'` of an algebraic space `U'` étale over
`X'`, the conditions (1) and (2) of [Stacks, Tag 061A] and the subfunctor of lifts they cut out,
proves that this subfunctor is a sheaf, and reconciles the two readings of `U = X ×_{X'} U'`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Thickenings

universe u v

namespace AlgebraicGeometry.Space

variable (C : BigFppfSite.{u}) (S : Scheme.{u}) (hS : C.Contains S)

/-! ### Morphisms into a fixed algebraic space form a sheaf on the spaces-étale site -/

section HomSheaf

/-- The presheaf on the spaces-étale site of `X` whose sections over an algebraic space `U`
étale over `X` are the morphisms `U ⟶ Z` into a fixed algebraic space `Z`, with restriction
given by precomposition. -/
noncomputable abbrev spacesEtaleHomPresheaf (X Z : AlgebraicSpaces C S hS) :
    (SpacesEtale C S hS X)ᵒᵖ ⥤ Type (u + 1) :=
  (SpacesEtale.toSpaces C S hS X).op ⋙ yoneda.obj Z

variable {X : AlgebraicSpaces C S hS}

/-- Pullbacks of presheaves on the big fppf site of `S` (instance search times out without this
shortcut). -/
local instance (priority := high) hasPullback_presheaf_LiftSubfunctor
    {F G H : (BigFppfOver C S hS)ᵒᵖ ⥤ Type u} (f : F ⟶ H) (g : G ⟶ H) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

/-- The chosen fibre product of the two underlying algebraic spaces of a pair of morphisms of
the spaces-étale site of `X` with common target. -/
private noncomputable abbrev sitePbSpace {V A A' : SpacesEtale C S hS X} (f : A ⟶ V)
    (g : A' ⟶ V) : AlgebraicSpaces C S hS :=
  AlgebraicSpaces.fiberProduct C S hS ((SpacesEtale.toSpaces C S hS X).map f)
    ((SpacesEtale.toSpaces C S hS X).map g)

/-- The first projection of `AlgebraicGeometry.Space.sitePbSpace`. -/
private noncomputable abbrev sitePbP₁ {V A A' : SpacesEtale C S hS X} (f : A ⟶ V) (g : A' ⟶ V) :
    sitePbSpace C S hS f g ⟶ (SpacesEtale.toSpaces C S hS X).obj A :=
  ObjectProperty.homMk (pullback.fst _ _)

/-- The second projection of `AlgebraicGeometry.Space.sitePbSpace`. -/
private noncomputable abbrev sitePbP₂ {V A A' : SpacesEtale C S hS X} (f : A ⟶ V) (g : A' ⟶ V) :
    sitePbSpace C S hS f g ⟶ (SpacesEtale.toSpaces C S hS X).obj A' :=
  ObjectProperty.homMk (pullback.snd _ _)

/-- The two projections of `AlgebraicGeometry.Space.sitePbSpace` exhibit it as a fibre product
in the category of algebraic spaces. -/
private theorem sitePb_isPullback {V A A' : SpacesEtale C S hS X} (f : A ⟶ V) (g : A' ⟶ V) :
    IsPullback (sitePbP₁ C S hS f g) (sitePbP₂ C S hS f g)
      ((SpacesEtale.toSpaces C S hS X).map f) ((SpacesEtale.toSpaces C S hS X).map g) :=
  AlgebraicSpaces.isPullback_fiberProduct C S hS _ _

/-- The fibre product of two morphisms of the spaces-étale site of `X`, as an object of that
site. -/
private noncomputable def sitePb {V A A' : SpacesEtale C S hS X} (f : A ⟶ V) (g : A' ⟶ V) :
    SpacesEtale C S hS X :=
  ⟨Over.mk (sitePbP₁ C S hS f g ≫ ((SpacesEtale.inclusion C S hS X).obj A).hom),
    isEtale_comp C S hS
      (isEtale_of_isPullback C S hS _ _ _ _ (sitePb_isPullback C S hS f g).flip
        (SpacesEtale.isEtale_toSpaces_map C S hS X g))
      A.property⟩

/-- The first projection of `AlgebraicGeometry.Space.sitePb`, as a morphism of the spaces-étale
site. -/
private noncomputable def sitePbFst {V A A' : SpacesEtale C S hS X} (f : A ⟶ V) (g : A' ⟶ V) :
    sitePb C S hS f g ⟶ A :=
  ObjectProperty.homMk (Over.homMk (sitePbP₁ C S hS f g) rfl)

/-- The second projection of `AlgebraicGeometry.Space.sitePb`, as a morphism of the spaces-étale
site. -/
private noncomputable def sitePbSnd {V A A' : SpacesEtale C S hS X} (f : A ⟶ V) (g : A' ⟶ V) :
    sitePb C S hS f g ⟶ A' :=
  ObjectProperty.homMk (Over.homMk (sitePbP₂ C S hS f g)
    (by
      change sitePbP₂ C S hS f g ≫ ((SpacesEtale.inclusion C S hS X).obj A').hom =
        sitePbP₁ C S hS f g ≫ ((SpacesEtale.inclusion C S hS X).obj A).hom
      rw [← SpacesEtale.toSpaces_map_comp_structure C S hS X f,
        ← SpacesEtale.toSpaces_map_comp_structure C S hS X g, ← Category.assoc,
        ← Category.assoc, (sitePb_isPullback C S hS f g).w]))

/-- The square formed by the two projections of `AlgebraicGeometry.Space.sitePb` commutes in the
spaces-étale site. -/
private theorem sitePb_w {V A A' : SpacesEtale C S hS X} (f : A ⟶ V) (g : A' ⟶ V) :
    sitePbFst C S hS f g ≫ f = sitePbSnd C S hS f g ≫ g :=
  (SpacesEtale.inclusion C S hS X).map_injective
    (Over.OverMorphism.ext (sitePb_isPullback C S hS f g).w)

/-- The presheaf of morphisms into a fixed algebraic space satisfies the sheaf condition for a
covering family of the spaces-étale site. -/
private theorem isSheafFor_spacesEtaleHomPresheaf (Z : AlgebraicSpaces C S hS)
    {V : SpacesEtale C S hS X} {I : Type (u + 1)} (Xi : I → SpacesEtale C S hS X)
    (f : ∀ i, Xi i ⟶ V)
    (hf : IsEtaleCovering C S hS
      (fun i => ((SpacesEtale.toSpaces C S hS X).obj (Xi i)).obj)
      (fun i => ((SpacesEtale.toSpaces C S hS X).map (f i)).hom)) :
    Presieve.IsSheafFor (spacesEtaleHomPresheaf C S hS X Z) (Presieve.ofArrows Xi f) := by
  rw [Presieve.isSheafFor_arrows_iff]
  intro x hx
  exact existsUnique_desc_of_fpqcCovering C S hS
    (fun i => (SpacesEtale.toSpaces C S hS X).map (f i))
    (isFpqcCovering_of_isEtaleCovering C S hS _ _ hf) Z x
    (fun i j => hx i j (sitePb C S hS (f i) (f j)) (sitePbFst C S hS (f i) (f j))
      (sitePbSnd C S hS (f i) (f j)) (sitePb_w C S hS (f i) (f j)))

/-- **Stacks 04P2 on the spaces-étale site.** The presheaf of morphisms into a fixed algebraic
space `Z` is a sheaf on the spaces-étale site of an algebraic space `X`. -/
theorem isSheaf_spacesEtaleHomPresheaf (X Z : AlgebraicSpaces C S hS) :
    Presieve.IsSheaf (SpacesEtale.topology C S hS X) (spacesEtaleHomPresheaf C S hS X Z) := by
  rw [Precoverage.isSheaf_toGrothendieck_iff_of_isStableUnderBaseChange]
  intro V R hR
  obtain ⟨E, rfl, hE⟩ := hR
  exact isSheafFor_spacesEtaleHomPresheaf C S hS Z E.X E.f
    (SpacesEtale.isEtaleCovering_of_isCovering C S hS X E.X E.f hE)

end HomSheaf

/-! ### The sheaf of lifts -/

section Lifts

variable {X' Y' T : AlgebraicSpaces C S hS} {G : Subfunctor X'.obj} {H : Subfunctor Y'.obj}

/-- The thickening `U = X ×_{X'} U'` of an algebraic space `U'` étale over `X'`, as an algebraic
space étale over `X`: the base change of `U'` along the inclusion `X ⟶ X'`. -/
noncomputable abbrev thickeningBaseChange (hG : IsThickening C S hS X' G) :
    SpacesEtale C S hS X' ⥤ SpacesEtale C S hS (IsThickening.space C S hS hG) :=
  (spacesBaseChange C S hS (IsThickening.inclusion C S hS hG)).functor

/-- The cartesian projection `X ×_{X'} U' ⟶ U'`. -/
noncomputable abbrev thickeningProjection (hG : IsThickening C S hS X' G) :
    thickeningBaseChange C S hS hG ⋙
        SpacesEtale.toSpaces C S hS (IsThickening.space C S hS hG) ⟶
      SpacesEtale.toSpaces C S hS X' :=
  (spacesBaseChange C S hS (IsThickening.inclusion C S hS hG)).projection

/-- The presheaf on the spaces-étale site of `X'` whose sections over `U'` are the morphisms
`X ×_{X'} U' ⟶ Z`. It is the presheaf of morphisms into `Z` on the spaces-étale site of `X`,
restricted along base change. -/
noncomputable abbrev thickeningHomPresheaf (hG : IsThickening C S hS X' G)
    (Z : AlgebraicSpaces C S hS) : (SpacesEtale C S hS X')ᵒᵖ ⥤ Type (u + 1) :=
  (thickeningBaseChange C S hS hG).op ⋙
    spacesEtaleHomPresheaf C S hS (IsThickening.space C S hS hG) Z

/-- The presheaf of morphisms `X ×_{X'} U' ⟶ Z` is a sheaf on the spaces-étale site of `X'`. -/
theorem isSheaf_thickeningHomPresheaf (hG : IsThickening C S hS X' G)
    (Z : AlgebraicSpaces C S hS) :
    Presieve.IsSheaf (SpacesEtale.topology C S hS X') (thickeningHomPresheaf C S hS hG Z) :=
  (isSheaf_iff_isSheaf_of_type _ _).1
    ((thickeningBaseChange C S hS hG).op_comp_isSheaf_of_isSheaf
      (SpacesEtale.topology C S hS X')
      (SpacesEtale.topology C S hS (IsThickening.space C S hS hG)) _
      ((isSheaf_iff_isSheaf_of_type _ _).2
        (isSheaf_spacesEtaleHomPresheaf C S hS (IsThickening.space C S hS hG) Z)))

variable (hG : IsThickening C S hS X' G) (hH : IsThickening C S hS Y' H)
  (pX' : X' ⟶ T) (pY' : Y' ⟶ T)
  (a : IsThickening.space C S hS hG ⟶ IsThickening.space C S hS hH)

/-- The condition on `a' : U' ⟶ Y'` of being a *lift of `a` over `T`*: it is a morphism over
`T`, and its restriction to the thickening `U = X ×_{X'} U'` of `U'` is the restriction of `a`,
read through the inclusion `Y ⟶ Y'`. These are the conditions (1) and (2) of Stacks 061A. -/
def IsLiftOver (U' : SpacesEtale C S hS X')
    (a' : (SpacesEtale.toSpaces C S hS X').obj U' ⟶ Y') : Prop :=
  a' ≫ pY' = ((SpacesEtale.inclusion C S hS X').obj U').hom ≫ pX' ∧
    (thickeningProjection C S hS hG).app U' ≫ a' =
      ((SpacesEtale.inclusion C S hS (IsThickening.space C S hS hG)).obj
          ((thickeningBaseChange C S hS hG).obj U')).hom ≫
        a ≫ IsThickening.inclusion C S hS hH

/-- The rule sending an algebraic space `U'` étale over `X'` to the set of lifts of `a` over
`U'` in the sense of conditions (1) and (2) of [Stacks, Tag 061A], as a subfunctor of the
presheaf of morphisms into `Y'`.

The rule of Equation [Stacks, Tag 061B] imposes condition (3) as well; it is
`AlgebraicGeometry.Space.conormalLiftSubfunctor`, a subfunctor of this one in each section. -/
def liftSubfunctor : Subfunctor (spacesEtaleHomPresheaf C S hS X' Y') where
  obj U' := {a' | IsLiftOver C S hS hG hH pX' pY' a (unop U') a'}
  map {U' V'} k a' ha' := by
    refine ⟨?_, ?_⟩
    · change ((SpacesEtale.toSpaces C S hS X').map k.unop ≫ a') ≫ pY' = _
      rw [Category.assoc, ha'.1, ← Category.assoc,
        SpacesEtale.toSpaces_map_comp_structure C S hS X' k.unop]
    · change (thickeningProjection C S hS hG).app (unop V') ≫
        (SpacesEtale.toSpaces C S hS X').map k.unop ≫ a' = _
      rw [← Category.assoc, ← (thickeningProjection C S hS hG).naturality k.unop,
        Functor.comp_map, Category.assoc, ha'.2, ← Category.assoc,
        SpacesEtale.toSpaces_map_comp_structure C S hS (IsThickening.space C S hS hG)
          ((thickeningBaseChange C S hS hG).map k.unop)]

/-- **The rule of conditions (1) and (2) is a sheaf.**  The rule sending an algebraic space `U'`
étale over `X'` to the set of morphisms `a' : U' ⟶ Y'` over `T` whose restriction to
`U = X ×_{X'} U'` is the restriction of `a` is a sheaf of sets on the spaces-étale site of `X'`.

The conormal condition (3) of the source is not imposed. For `Y = Y'` it holds for every `a'`,
and the rule is then the rule of the source (Remark 061D). -/
@[stacks 061A "the sheaf property of the rule of lifts, for conditions (1) and (2); \
the conormal condition (3) is not imposed"]
theorem isSheaf_liftSubfunctor :
    Presieve.IsSheaf (SpacesEtale.topology C S hS X')
      (liftSubfunctor C S hS hG hH pX' pY' a).toFunctor := by
  rw [Subfunctor.isSheaf_iff _ (isSheaf_spacesEtaleHomPresheaf C S hS X' Y')]
  intro U' a' hmem
  refine ⟨?_, ?_⟩
  · refine ((isSheaf_spacesEtaleHomPresheaf C S hS X' T).isSeparated _ hmem).ext ?_
    intro V' k hk
    have hk1 : ((SpacesEtale.toSpaces C S hS X').map k ≫ a') ≫ pY' =
      ((SpacesEtale.inclusion C S hS X').obj V').hom ≫ pX' := hk.1
    have hstr := SpacesEtale.toSpaces_map_comp_structure C S hS X' k
    change (SpacesEtale.toSpaces C S hS X').map k ≫ a' ≫ pY' =
      (SpacesEtale.toSpaces C S hS X').map k ≫
        ((SpacesEtale.inclusion C S hS X').obj (unop U')).hom ≫ pX'
    rw [← Category.assoc, ← Category.assoc, hstr]
    exact hk1
  · refine ((isSheaf_thickeningHomPresheaf C S hS hG Y').isSeparated _ hmem).ext ?_
    intro V' k hk
    have hk2 : (thickeningProjection C S hS hG).app V' ≫
          ((SpacesEtale.toSpaces C S hS X').map k ≫ a') =
        ((SpacesEtale.inclusion C S hS (IsThickening.space C S hS hG)).obj
            ((thickeningBaseChange C S hS hG).obj V')).hom ≫
          a ≫ IsThickening.inclusion C S hS hH := hk.2
    have hnat : (SpacesEtale.toSpaces C S hS (IsThickening.space C S hS hG)).map
          ((thickeningBaseChange C S hS hG).map k) ≫
          (thickeningProjection C S hS hG).app (unop U') =
        (thickeningProjection C S hS hG).app V' ≫ (SpacesEtale.toSpaces C S hS X').map k :=
      (thickeningProjection C S hS hG).naturality k
    have hstr := SpacesEtale.toSpaces_map_comp_structure C S hS (IsThickening.space C S hS hG)
      ((thickeningBaseChange C S hS hG).map k)
    change (SpacesEtale.toSpaces C S hS (IsThickening.space C S hS hG)).map
        ((thickeningBaseChange C S hS hG).map k) ≫
          (thickeningProjection C S hS hG).app (unop U') ≫ a' =
      (SpacesEtale.toSpaces C S hS (IsThickening.space C S hS hG)).map
        ((thickeningBaseChange C S hS hG).map k) ≫
          ((SpacesEtale.inclusion C S hS (IsThickening.space C S hS hG)).obj
              ((thickeningBaseChange C S hS hG).obj (unop U'))).hom ≫
            a ≫ IsThickening.inclusion C S hS hH
    rw [← Category.assoc, hnat, Category.assoc, hk2, ← hstr, Category.assoc]

/-! ### The two readings of `U = X ×_{X'} U'` -/

/-- **A lift makes the square of inclusions over it commute.** For a lift `a'` in the sense of
conditions (1) and (2), the inclusion of the preimage `U ⊆ U'` followed by `a'` is its projection
to `X` followed by `a` and the inclusion `Y ⟶ Y'`. This is the `square` field of
`AlgebraicGeometry.Space.IsConormalLiftAtSubspace` at the two thickenings of this file. -/
theorem preimageSquare_of_isLiftOver (U' : SpacesEtale C S hS X')
    (a' : (SpacesEtale.toSpaces C S hS X').obj U' ⟶ Y')
    (h : IsLiftOver C S hS hG hH pX' pY' a U' a') :
    subspaceInclusion C S hS ((SpacesEtale.toSpaces C S hS X').obj U')
          (preimageSubspace C S hS ((SpacesEtale.inclusion C S hS X').obj U').hom
            ⟨G, hG.1⟩) ≫ a' =
      (preimageProjection C S hS ((SpacesEtale.inclusion C S hS X').obj U').hom ⟨G, hG.1⟩ ≫
          a) ≫ subspaceInclusion C S hS Y' ⟨H, hH.1⟩ := by
  have hpb := (spacesBaseChange C S hS (IsThickening.inclusion C S hS hG)).isPullback U'
  have hw := conormalEtaleRestrictionSquare C S hS
    ((SpacesEtale.inclusion C S hS X').obj U').hom (⟨G, hG.1⟩ : ClosedSubspaces C S hS X'.1)
  have hc := congrArg (hpb.lift _ _ hw ≫ ·) h.2
  simp only [← Category.assoc] at hc
  erw [hpb.lift_fst _ _ hw, hpb.lift_snd _ _ hw] at hc
  exact hc

end Lifts

end AlgebraicGeometry.Space

end
