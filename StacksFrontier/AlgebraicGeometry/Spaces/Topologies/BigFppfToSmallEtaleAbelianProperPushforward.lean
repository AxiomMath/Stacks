module

public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.BigFppfToSmallEtaleProperPushforward
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.BigFppfToSmallEtaleProperDerivedPushforward
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.ProperBaseChangeUnconditional

/-!
# Proper direct image and the big fppf topos, for sheaves of sets and abelian sheaves

Let `T` be a big fppf site of algebraic spaces over a scheme `S`, `E` a big étale site of
algebraic spaces over the same big fppf site of schemes, and `f : Y ⟶ X` a morphism of algebraic
spaces of `T`. Write `a_X = π_X ∘ ε_X` for the comparison morphism of Stacks 0DGI. For sheaves of
sets the canonical base change map `f_{small,*} ⋙ a_X⁻¹ ⟶ a_Y⁻¹ ⋙ f_{big,fppf,*}`,
`AlgebraicGeometry.BigFppfSpaceSite.fppfToSmallEtaleBaseChange`, is invertible for `f` proper
(`AlgebraicGeometry.BigFppfSpaceSite.isIso_fppfToSmallEtaleBaseChange_of_isProper`). This file
proves the same for abelian sheaves. It then states Stacks 0DGJ (1) as a pair of natural
isomorphisms, one for sheaves of sets and one for abelian sheaves.

## Main definitions

* `AlgebraicGeometry.BigFppfSpaceSite.fppfToSmallEtaleAbelianBaseChange`: the canonical base change
  map on abelian sheaves, the mate of the square of Stacks 0DGI across `a⁻¹ ⊣ a_*`.
* `AlgebraicGeometry.BigFppfSpaceSite.fppfToSmallEtalePushforwardIsosOfIsProper`: for `f` proper,
  `a_X⁻¹ ∘ f_{small,*} ≅ f_{big,fppf,*} ∘ a_Y⁻¹` on sheaves of sets and on abelian sheaves.

## Main results

* `AlgebraicGeometry.BigFppfSpaceSite.isIso_fppfToSmallEtaleAbelianBaseChange_of_isProper`: the
  abelian base change map is invertible for `f` proper.

## Implementation notes

The units of `a⁻¹ ⊣ a_*` on abelian sheaves are invertible (`a_{X,*}a_X⁻¹F = F`, Stacks 0DGF (1)),
and the square of direct images is invertible. So the mate is invertible at `F` once
`f_{big,fppf,*}a_Y⁻¹F` is of the form `a_X⁻¹G`
(`Stacks.ComparingTopologies.isIso_mateEquiv_symm_app`). It is, for `G = f_{small,*}F`:
`f_{big,fppf,*}a_Y⁻¹F = ε_X⁻¹ε_{X,*}f_{big,fppf,*}a_Y⁻¹F` (`ε_{X,*}` is fully faithful),
`ε_{X,*}f_{big,fppf,*} = f_{big,étale,*}ε_{Y,*}` (Stacks 0DGI), `ε_{Y,*}a_Y⁻¹F = π_Y⁻¹F`
(Stacks 0DGF (1)), `f_{big,étale,*}π_Y⁻¹F = π_X⁻¹f_{small,*}F` (Stacks 0DGD (1)) and
`ε_X⁻¹π_X⁻¹ = a_X⁻¹`.

## References

* [Stacks Project, Tag 0DGJ](https://stacks.math.columbia.edu/tag/0DGJ)
* [Stacks Project, Tag 0DGI](https://stacks.math.columbia.edu/tag/0DGI)
* [Stacks Project, Tag 0DGD](https://stacks.math.columbia.edu/tag/0DGD)
* [Stacks Project, Tag 0DGF](https://stacks.math.columbia.edu/tag/0DGF)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.BigFppfSpaceSite

-- `BigEtaleSpaceSite.bigToSmallAbelianInverseImage_additive` is a `local instance` of
-- `BigSmallEtaleCohomology.lean`, so the attribute is re-enabled here.
attribute [local instance] BigEtaleSpaceSite.bigToSmallAbelianInverseImage_additive

variable {S : Scheme.{u}} (T : BigFppfSpaceSite S) (E : BigEtaleSpaceSite S)
  (h : T.schemeSite = E.fppfSite) {X Y : T.Spaces} (f : Y ⟶ X)

/-- The canonical base change map `f_{small,*} ⋙ a_X⁻¹ ⟶ a_Y⁻¹ ⋙ f_{big,fppf,*}` on abelian
sheaves: the mate, across `a_Y⁻¹ ⊣ a_{Y,*}` and `a_X⁻¹ ⊣ a_{X,*}`, of the square of direct images
`a_{Y,*} ⋙ f_{small,*} = f_{big,fppf,*} ⋙ a_{X,*}` of Stacks 0DGI. -/
def fppfToSmallEtaleAbelianBaseChange :
    E.smallEtalePushforward (etaleMap T E h f) ⋙
        CategoryTheory.Sites.abelianInverseImage (fppfToSmallEtaleMorphism T E h X) ⟶
      CategoryTheory.Sites.abelianInverseImage (fppfToSmallEtaleMorphism T E h Y) ⋙
        fppfAbelianPushforward T f :=
  ((mateEquiv (fppfToSmallEtaleAbelianAdjunction T E h Y)
    (fppfToSmallEtaleAbelianAdjunction T E h X)).symm
    (TwoSquare.mk _ _ _ _ (fppfToSmallEtale_comp_fppfAbelianPushforwardIso T E h f).inv))

/-- For `f` proper, `f_{big,fppf,*}a_Y⁻¹F ≅ a_X⁻¹f_{small,*}F` for an abelian sheaf `F` on
`Y_étale`. -/
def fppfToSmallEtaleAbelianPushforwardObjIsoOfIsProper
    (hf : Space.IsProper T.schemeSite S T.scheme_mem f.hom)
    (F : Sheaf (Space.SpacesEtale.topology E.fppfSite S E.fppf_mem (etaleSpace T E h Y))
      AddCommGrpCat.{u + 1}) :
    (CategoryTheory.Sites.abelianInverseImage (fppfToSmallEtaleMorphism T E h X)).obj
        ((E.smallEtalePushforward (etaleMap T E h f)).obj F) ≅
      (fppfAbelianPushforward T f).obj
        ((CategoryTheory.Sites.abelianInverseImage (fppfToSmallEtaleMorphism T E h Y)).obj F) :=
  let εX := CategoryTheory.Sites.abelianInverseImage (fppfToBigEtaleMorphism T E h X)
  ((fppfToSmallEtale_abelianInverseImageCompIso T E h X).app _).symm ≪≫
    εX.mapIso ((BigEtaleSpaceSite.bigToSmallEtaleAbelianPushforwardIsoOfIsProper E
      (etaleMap T E h f) (isProper_etaleMap T E h f hf)).app F) ≪≫
    εX.mapIso ((E.bigEtalePushforward (etaleMap T E h f)).mapIso
      ((fppfToSmallEtale_abelianInverseImage_comp_pushforwardIso T E h Y).app F).symm) ≪≫
    εX.mapIso ((fppfToBigEtale_comp_fppfAbelianPushforwardIso T E h f).app _).symm ≪≫
    asIso ((fppfToBigEtaleAbelianAdjunction T E h X).counit.app _)

/-- For `f` proper, the abelian base change map `f_{small,*} ⋙ a_X⁻¹ ⟶ a_Y⁻¹ ⋙ f_{big,fppf,*}` is
invertible. -/
theorem isIso_fppfToSmallEtaleAbelianBaseChange_of_isProper
    (hf : Space.IsProper T.schemeSite S T.scheme_mem f.hom) :
    IsIso (fppfToSmallEtaleAbelianBaseChange T E h f) := by
  have : IsIso (TwoSquare.mk _ _ _ _
      (fppfToSmallEtale_comp_fppfAbelianPushforwardIso T E h f).inv) :=
    inferInstanceAs (IsIso (fppfToSmallEtale_comp_fppfAbelianPushforwardIso T E h f).inv)
  have := Stacks.Adjunction.isIso_unit_of_comp_iso_id (fppfToSmallEtaleAbelianAdjunction T E h Y)
    (fppfToSmallEtale_abelianInverseImage_comp_restrictionIso T E h Y)
  have := Stacks.Adjunction.isIso_unit_of_comp_iso_id (fppfToSmallEtaleAbelianAdjunction T E h X)
    (fppfToSmallEtale_abelianInverseImage_comp_restrictionIso T E h X)
  rw [NatTrans.isIso_iff_isIso_app]
  intro F
  exact Stacks.ComparingTopologies.isIso_mateEquiv_symm_app _ _ _ (fun _ ↦ inferInstance)
    (fun _ ↦ inferInstance) F (fppfToSmallEtaleAbelianPushforwardObjIsoOfIsProper T E h f hf F)

/-- Let `f : Y ⟶ X` be a proper morphism of algebraic spaces over `S`, and `a = π ∘ ε` the
comparison morphisms from the big fppf topoi to the small étale topoi of Stacks 0DGI. Then
`a_X⁻¹ ∘ f_{small,*} = f_{big,fppf,*} ∘ a_Y⁻¹`, as functors from sheaves of sets on the small étale
site of `Y` to sheaves of sets on the big fppf site of `X`, and likewise for abelian sheaves. Both
isomorphisms are the canonical base change maps, the mates of the commutative square of Stacks
0DGI: `AlgebraicGeometry.BigFppfSpaceSite.fppfToSmallEtaleBaseChange` and
`AlgebraicGeometry.BigFppfSpaceSite.fppfToSmallEtaleAbelianBaseChange`. -/
@[stacks 0DGJ "(1)"]
def fppfToSmallEtalePushforwardIsosOfIsProper
    (hf : Space.IsProper T.schemeSite S T.scheme_mem f.hom) :
    ((E.smallEtaleMorphism (etaleMap T E h f)).pushforward ⋙
        (fppfToSmallEtaleMorphism T E h X).inverseImage ≅
      (fppfToSmallEtaleMorphism T E h Y).inverseImage ⋙ (bigFppfMorphism T f).pushforward) ×
    (E.smallEtalePushforward (etaleMap T E h f) ⋙
        CategoryTheory.Sites.abelianInverseImage (fppfToSmallEtaleMorphism T E h X) ≅
      CategoryTheory.Sites.abelianInverseImage (fppfToSmallEtaleMorphism T E h Y) ⋙
        fppfAbelianPushforward T f) :=
  haveI := isIso_fppfToSmallEtaleBaseChange_of_isProper T E h f hf
  haveI := isIso_fppfToSmallEtaleAbelianBaseChange_of_isProper T E h f hf
  (asIso (fppfToSmallEtaleBaseChange T E h f), asIso (fppfToSmallEtaleAbelianBaseChange T E h f))

end AlgebraicGeometry.BigFppfSpaceSite

end
