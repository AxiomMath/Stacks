module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposEquivalence
public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.Basic
public import StacksFrontier.AlgebraicGeometry.Spaces.SimplicialSmallEtaleMorphism
public import StacksFrontier.AlgebraicGeometry.Spaces.SimplicialSmallEtaleStrictTotal
public import StacksFrontier.CategoryTheory.Sites.MorphismOfSites.DenseSubsiteMorphism

/-!
# The ringed topos of a simplicial algebraic space through its strict components

Let `X` be a simplicial algebraic space. The strict components form a simplicial site
(Stacks 09WC), whose total site is equivalent, as a site, to `X_{spaces,étale}` (Stacks 0DE7)
through `strictTotalComparison`. Restricting the structure sheaf `𝒪_X` along the comparison
makes the total site a ringed site, and the comparison an equivalence of ringed topoi
`(Sh(X_{spaces,étale}), 𝒪_X) ≃ (Sh(total), 𝒪)`. In each degree the component ringed topos is
likewise equivalent to the spaces-étale ringed topos of `X_n`. This puts
`(Sh(X_{spaces,étale}), 𝒪_X)` in the simplicial-site situation of Stacks 09WE, case (A).

## Main definitions

* `AlgebraicGeometry.Space.SimplicialSpacesEtaleSite.strictSituation`: the simplicial-site
  situation of the strict components.
* `AlgebraicGeometry.Space.SimplicialSpacesEtaleSite.strictStructureSheaf`: the structure sheaf
  of its total site, the restriction of `𝒪_X`.
* `AlgebraicGeometry.Space.SimplicialSpacesEtaleSite.strictRingedToposHom`: the equivalence of
  ringed topoi from `(Sh(X_{spaces,étale}), 𝒪_X)` to the total ringed topos, with
  `strictRingedToposHomInverse` its inverse.
* `AlgebraicGeometry.Space.SimplicialSpacesEtaleSite.strictComponentRingedToposHom`: in each
  degree `n`, the equivalence of ringed topoi from `(Sh((X_n)_{spaces,étale}), 𝒪_{X_n})` to the
  component ringed topos `(Sh(C_n), 𝒪_n)` (Stacks 0D72), through the realization
  `componentRealize`, with `strictComponentStructureIso` identifying the structure sheaves and
  `strictComponentRingedToposHomInverse` its inverse.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space.SimplicialSpacesEtaleSite

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  (X : SimplicialObject (AlgebraicSpaces B S hS))

/-- The simplicial-site situation of the strict components of `X`, case (A) of Stacks 09WE. -/
abbrev strictSituation : SimplicialSiteSituation.{u + 1} := (strictSimplicialSite X).situation

/-- The structure sheaf of the total site of the strict components: the restriction of `𝒪_X`
along the comparison with `X_{spaces,étale}`. -/
def strictStructureSheaf : Sheaf (strictSituation X).totalTopology CommRingCat.{u + 1} :=
  ((strictTotalComparison X).sheafPushforwardContinuous CommRingCat.{u + 1}
    (strictSimplicialSite X).totalTopology (topology X)).obj (structureSheaf X)

/-- The total ringed topos of the strict components of `X`. -/
abbrev strictRingedTopos : RingedTopos.{u + 1, u + 1, u + 1} :=
  (strictSituation X).totalRingedTopos (strictStructureSheaf X)

/-- The comparison with `X_{spaces,étale}` is a morphism of sites, being a dense subsite. -/
theorem strictTotalComparison_isMorphismOfSites :
    IsMorphismOfSites.{u + 1} (strictTotalComparison X) (strictSimplicialSite X).totalTopology
      (topology X) :=
  IsMorphismOfSites.ofIsDenseSubsite _

/-- **The comparison of ringed topoi** `(Sh(X_{spaces,étale}), 𝒪_X) ⟶ (Sh(total), 𝒪)`: the
morphism of topoi of the comparison of sites, whose direct image is restriction along the
comparison, with structure map the identification of `𝒪` with the restriction of `𝒪_X`. -/
def strictRingedToposHom : RingedToposHom (ringedTopos X) (strictRingedTopos X) where
  toToposHom := (strictTotalComparison_isMorphismOfSites X).morphismOfTopoi
  fSharp := (Stacks.Sheaves.ToposPullback.restrictionCommRingIso
    (strictSimplicialSite X).totalTopology (topology X) (strictTotalComparison X)
      (structureSheaf X)).inv

/-- The structure map of `strictRingedToposHom X` is an isomorphism. -/
instance strictRingedToposHom_isIso_fSharp : IsIso (strictRingedToposHom X).fSharp :=
  ⟨⟨(Stacks.Sheaves.ToposPullback.restrictionCommRingIso (strictSimplicialSite X).totalTopology
    (topology X) (strictTotalComparison X) (structureSheaf X)).hom, Iso.inv_hom_id _,
      Iso.hom_inv_id _⟩⟩

/-- The direct image of `strictRingedToposHom X` is an equivalence of sheaf categories. -/
instance strictRingedToposHom_pushforward_isEquivalence :
    (strictRingedToposHom X).toToposHom.pushforward.IsEquivalence :=
  inferInstanceAs ((strictTotalComparison X).sheafPushforwardContinuous (Type (u + 1))
    (strictSimplicialSite X).totalTopology (topology X)).IsEquivalence

/-- The inverse equivalence of ringed topoi `(Sh(total), 𝒪) ⟶ (Sh(X_{spaces,étale}), 𝒪_X)`. -/
def strictRingedToposHomInverse : RingedToposHom (strictRingedTopos X) (ringedTopos X) :=
  (strictRingedToposHom X).inverse

/-! ### The component ringed topoi -/

/-- The realization of the degree-`n` strict component, with source the degree-`n` component of
the simplicial-site situation. -/
def componentRealize (n : SimplexCategory) :
    (strictSituation X).component n ⥤ SpacesEtale B S hS (X.obj (op n)) :=
  strictRealize X n

/-- The realization of a strict component is an equivalence of categories. -/
instance componentRealize_isEquivalence (n : SimplexCategory) :
    (componentRealize X n).IsEquivalence :=
  inferInstanceAs (strictRealize X n).IsEquivalence

/-- The realization of a strict component is continuous for the component topology of the
simplicial-site situation and the étale topology of `X_n`. -/
instance componentRealize_isContinuous (n : SimplexCategory) :
    (componentRealize X n).IsContinuous ((strictSituation X).componentTopology n)
      (SpacesEtale.topology B S hS (X.obj (op n))) := by
  change (strictRealize X n).IsContinuous (strictTopology X n).toPrecoverage.toGrothendieck _
  rw [strictTopology_toPrecoverage_toGrothendieck]
  infer_instance

/-- The realization of a strict component is a dense subsite for the component topology of the
simplicial-site situation. -/
instance componentRealize_isDenseSubsite (n : SimplexCategory) :
    (componentRealize X n).IsDenseSubsite ((strictSituation X).componentTopology n)
      (SpacesEtale.topology B S hS (X.obj (op n))) := by
  change (strictRealize X n).IsDenseSubsite (strictTopology X n).toPrecoverage.toGrothendieck _
  rw [strictTopology_toPrecoverage_toGrothendieck]
  infer_instance

set_option synthInstance.maxHeartbeats 80000 in
/-- The realization of a strict component is a morphism of sites, being a dense subsite. -/
theorem componentRealize_isMorphismOfSites (n : SimplexCategory) :
    IsMorphismOfSites.{u + 1} (componentRealize X n) ((strictSituation X).componentTopology n)
      (SpacesEtale.topology B S hS (X.obj (op n))) :=
  IsMorphismOfSites.ofIsDenseSubsite _

/-- The comparison restricted to the degree-`n` component is the realization followed by the
inclusion of the degree, on morphisms. -/
theorem strictTotalComparison_map_componentFunctor (n : SimplexCategory)
    {y z : (strictSituation X).component n} (g : y ⟶ z) :
    (strictTotalComparison X).map ((SimplicialSiteSituation.componentFunctor
        (strictSituation X) n).map g) =
      (degreeInclusion X n).map ((componentRealize X n).map g) :=
  strictTotalComparison_map_ι (b := op n) g

/-- On presheaves, the structure sheaf of `X_n` restricted along the realization is the total
structure sheaf restricted along the component inclusion; the components are identities. -/
def strictComponentStructurePresheafIso (n : SimplexCategory) :
    (componentRealize X n).op ⋙ SpacesEtale.structurePresheaf B S hS (X.obj (op n)) ≅
      (SimplicialSiteSituation.componentFunctor (strictSituation X) n).op ⋙
        (strictTotalComparison X).op ⋙ structurePresheaf X :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun g ↦
    (Category.comp_id _).trans ((congrArg (fun k ↦ (structurePresheaf X).map (Quiver.Hom.op k))
      (strictTotalComparison_map_componentFunctor X n g.unop)).symm.trans
        (Category.id_comp _).symm))

/-- **The structure sheaf of a strict component is that of `X_n`**: the total structure sheaf
restricted to the degree-`n` component is the restriction of `𝒪_{X_n}` along the realization. -/
def strictComponentStructureIso (n : SimplexCategory) :
    ((componentRealize X n).sheafPushforwardContinuous CommRingCat.{u + 1}
        ((strictSituation X).componentTopology n)
        (SpacesEtale.topology B S hS (X.obj (op n)))).obj
        (SpacesEtale.structureSheaf B S hS (X.obj (op n))) ≅
      ((strictSituation X).componentRingedTopos (strictStructureSheaf X) n).O :=
  (fullyFaithfulSheafToPresheaf _ _).preimageIso (strictComponentStructurePresheafIso X n)

/-- **The degree-`n` comparison of ringed topoi**
`(Sh((X_n)_{spaces,étale}), 𝒪_{X_n}) ⟶ (Sh(C_n), 𝒪_n)` from the spaces-étale ringed topos of
`X_n` to the component ringed topos of the strict components: the morphism of topoi of the
realization, with structure map the identification of the structure sheaves. -/
def strictComponentRingedToposHom (n : SimplexCategory) :
    RingedToposHom (spacesEtaleRingedTopos B S hS (X.obj (op n)))
      ((strictSituation X).componentRingedTopos (strictStructureSheaf X) n) where
  toToposHom := (componentRealize_isMorphismOfSites X n).morphismOfTopoi
  fSharp := (strictComponentStructureIso X n).inv ≫
    (Stacks.Sheaves.ToposPullback.restrictionCommRingIso
      ((strictSituation X).componentTopology n) (SpacesEtale.topology B S hS (X.obj (op n)))
      (componentRealize X n) (SpacesEtale.structureSheaf B S hS (X.obj (op n)))).inv

/-- The structure map of `strictComponentRingedToposHom X n` is an isomorphism. -/
instance strictComponentRingedToposHom_isIso_fSharp (n : SimplexCategory) :
    IsIso (strictComponentRingedToposHom X n).fSharp :=
  Iso.isIso_hom ((strictComponentStructureIso X n).symm ≪≫
    (Stacks.Sheaves.ToposPullback.restrictionCommRingIso
      ((strictSituation X).componentTopology n) (SpacesEtale.topology B S hS (X.obj (op n)))
      (componentRealize X n) (SpacesEtale.structureSheaf B S hS (X.obj (op n)))).symm)

set_option synthInstance.maxHeartbeats 80000 in
/-- The direct image of `strictComponentRingedToposHom X n` is an equivalence of sheaf
categories. -/
instance strictComponentRingedToposHom_pushforward_isEquivalence (n : SimplexCategory) :
    (strictComponentRingedToposHom X n).toToposHom.pushforward.IsEquivalence :=
  inferInstanceAs ((componentRealize X n).sheafPushforwardContinuous (Type (u + 1))
    ((strictSituation X).componentTopology n)
    (SpacesEtale.topology B S hS (X.obj (op n)))).IsEquivalence

/-- The inverse degree-`n` comparison `(Sh(C_n), 𝒪_n) ⟶ (Sh((X_n)_{spaces,étale}), 𝒪_{X_n})`. -/
def strictComponentRingedToposHomInverse (n : SimplexCategory) :
    RingedToposHom ((strictSituation X).componentRingedTopos (strictStructureSheaf X) n)
      (spacesEtaleRingedTopos B S hS (X.obj (op n))) :=
  (strictComponentRingedToposHom X n).inverse

end AlgebraicGeometry.Space.SimplicialSpacesEtaleSite

end
