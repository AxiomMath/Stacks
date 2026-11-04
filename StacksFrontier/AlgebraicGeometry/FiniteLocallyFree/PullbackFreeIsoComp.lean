module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackFreeComp
public import StacksFrontier.AlgebraicGeometry.Descent.ModuleRestrictChart
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.RestrictFreeIsoPullback

/-!
# The free comparison of an inverse image is pseudo-functorial, and agrees with the restriction one

`AlgebraicGeometry.Scheme.Modules.pullbackFreeIso` identifies the inverse image of the free module
on `I` with the free module on `I`.  For a composite of two morphisms of schemes there are two such
identifications of the inverse image along the composite -- the one for the composite, and the
iterated one read through `AlgebraicGeometry.pullbackCompIsoOfEq`.  This file proves they agree,
and then combines that with
`Stacks.Modules.restrictFreeIso_eq` to say what the inverse image of the *restriction* free
comparison is.

The second statement is what shrinks a chart comparison built from a trivialisation on inverse
images.  `AlgebraicGeometry.restrictChartIso_pullback_trans` shrinks such a comparison provided
its two halves satisfy the cocycle condition *on the inverse images*; a chart comparison of the
blow-up descent ends in `Stacks.Modules.restrictFreeIso`, which lives on restrictions, and the
cocycle condition therefore asks precisely for the inverse image of that comparison in terms of
the inverse-image ones.

## Main results

* `AlgebraicGeometry.Scheme.Modules.pullbackComp_hom_app_free_comp_pullbackFreeIso_hom`: **the
  free comparison of an inverse image is pseudo-functorial.**
* `Stacks.Modules.pullback_map_restrictFreeIso_hom_comp_pullbackFreeIso_hom`: **the inverse image
  of the free comparison of a restriction, followed by the free comparison of the inverse image,
  is the inverse image of the identification of restriction with the inverse image, followed by
  the contraction of the iterated inverse image and the free comparison of the composite.**

## Implementation notes

The pseudo-functoriality is `Stacks.SheafOfModules.free_comp_pullbackObjFreeIso_hom_of_unit` and
not the specialised
`Stacks.SheafOfModules.pullbackComp_hom_app_free_comp_pullbackObjFreeIso_hom`:  the morphism of
sheaves of rings underlying a composite of morphisms of schemes is pushed forward along the inverse
image of opens along the composite, which is only definitionally the composite of the two inverse
images, and instance resolution for its extension of scalars does not succeed in the composite
spelling.

The adjointness and finality instances of the three morphisms of sheaves of rings are not found by
instance search in the spelling `SheafOfModules` asks for -- the same miss as in
`AlgebraicGeometry.Scheme.Modules.pullbackFreeIso` itself -- and are supplied as local `have`s.

## References

* [Stacks Project, Tag 01C6](https://stacks.math.columbia.edu/tag/01C6)
* [Stacks Project, Tag 0EXD](https://stacks.math.columbia.edu/tag/0EXD)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)

/-- **The free comparison of an inverse image is pseudo-functorial.**  Taking the inverse image
along `f` of the free comparison of `g` and then comparing again is contracting the iterated
inverse image and comparing once, for the composite `f ≫ g`. -/
theorem pullbackComp_hom_app_free_comp_pullbackFreeIso_hom (I : Type u) :
    (Scheme.Modules.pullbackComp f g).hom.app
          (_root_.SheafOfModules.free (R := Z.ringCatSheaf) I) ≫
        (Scheme.Modules.pullbackFreeIso (f ≫ g) I).hom =
      (Scheme.Modules.pullback f).map (Scheme.Modules.pullbackFreeIso g I).hom ≫
        (Scheme.Modules.pullbackFreeIso f I).hom := by
  have : (_root_.SheafOfModules.pushforward.{u} f.toRingCatSheafHom).IsRightAdjoint :=
    inferInstanceAs ((Scheme.Modules.pushforward f).IsRightAdjoint)
  have : (_root_.SheafOfModules.pushforward.{u} g.toRingCatSheafHom).IsRightAdjoint :=
    inferInstanceAs ((Scheme.Modules.pushforward g).IsRightAdjoint)
  have : (_root_.SheafOfModules.pushforward.{u} (f ≫ g).toRingCatSheafHom).IsRightAdjoint :=
    inferInstanceAs ((Scheme.Modules.pushforward (f ≫ g)).IsRightAdjoint)
  have : (Opens.map f.base).Final := final_of_representablyFlat _
  have : (Opens.map g.base).Final := final_of_representablyFlat _
  have : (Opens.map (f ≫ g).base).Final := final_of_representablyFlat _
  exact Stacks.SheafOfModules.free_comp_pullbackObjFreeIso_hom_of_unit
    g.toRingCatSheafHom f.toRingCatSheafHom (f ≫ g).toRingCatSheafHom
    (Scheme.Modules.pullbackComp f g).hom
    (Stacks.SheafOfModules.pullbackComp_hom_app_unit_comp_pullbackObjUnitToUnit
      g.toRingCatSheafHom f.toRingCatSheafHom) I

end AlgebraicGeometry.Scheme.Modules

namespace Stacks.Modules

variable {X' P P' : Scheme.{u}} (c : P' ⟶ P) (p : P ⟶ X') [IsOpenImmersion p]
  {k : P' ⟶ X'} (hk : c ≫ p = k)

include hk in
/-- **The inverse image of the free comparison of a restriction, followed by the free comparison
of the inverse image.**  The restriction of the free `𝒪_{X'}`-module on `I` along `p` is the free
module on `I`, by `Stacks.Modules.restrictFreeIso`; its inverse image along `c` is then free in two
ways, and this says they agree:  the one going through the restriction comparison equals the one
that first identifies the restriction along `p` with the inverse image along `p`, then contracts
the iterated inverse image, then compares once for the composite `k`.

`Stacks.Modules.restrictFreeIso_eq` replaces the restriction comparison by the identification of
the two functors followed by the inverse-image comparison, and
`AlgebraicGeometry.Scheme.Modules.pullbackComp_hom_app_free_comp_pullbackFreeIso_hom` contracts
the two inverse-image comparisons that are left. -/
theorem pullback_map_restrictFreeIso_hom_comp_pullbackFreeIso_hom (I : Type u) :
    (Scheme.Modules.pullback c).map (restrictFreeIso p I).hom ≫
          (Scheme.Modules.pullbackFreeIso c I).hom =
      (Scheme.Modules.pullback c).map ((Scheme.Modules.restrictFunctorIsoPullback p).hom.app
            (_root_.SheafOfModules.free (R := X'.ringCatSheaf) I)) ≫
        (pullbackCompIsoOfEq c p hk
            (_root_.SheafOfModules.free (R := X'.ringCatSheaf) I)).hom ≫
          (Scheme.Modules.pullbackFreeIso k I).hom := by
  subst hk
  have h0 : (restrictFreeIso p I).hom =
      (Scheme.Modules.restrictFunctorIsoPullback p).hom.app
          (_root_.SheafOfModules.free (R := X'.ringCatSheaf) I) ≫
        (Scheme.Modules.pullbackFreeIso p I).hom :=
    congrArg Iso.hom (restrictFreeIso_eq p I)
  have h1 : (Scheme.Modules.pullback c).map (restrictFreeIso p I).hom =
      (Scheme.Modules.pullback c).map
          ((Scheme.Modules.restrictFunctorIsoPullback p).hom.app
            (_root_.SheafOfModules.free (R := X'.ringCatSheaf) I)) ≫
        (Scheme.Modules.pullback c).map (Scheme.Modules.pullbackFreeIso p I).hom :=
    (congrArg (Scheme.Modules.pullback c).map h0).trans
      ((Scheme.Modules.pullback c).map_comp _ _)
  refine (congrArg (· ≫ (Scheme.Modules.pullbackFreeIso c I).hom) h1).trans ?_
  refine (Category.assoc _ _ _).trans ?_
  refine congrArg ((Scheme.Modules.pullback c).map
      ((Scheme.Modules.restrictFunctorIsoPullback p).hom.app
        (_root_.SheafOfModules.free (R := X'.ringCatSheaf) I)) ≫ ·) ?_
  refine Eq.trans
    (Scheme.Modules.pullbackComp_hom_app_free_comp_pullbackFreeIso_hom c p I).symm ?_
  exact congrArg (· ≫ (Scheme.Modules.pullbackFreeIso (c ≫ p) I).hom)
    (Category.comp_id ((Scheme.Modules.pullbackComp c p).hom.app
      (_root_.SheafOfModules.free (R := X'.ringCatSheaf) I))).symm

end Stacks.Modules

end
