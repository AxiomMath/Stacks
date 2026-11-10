module

public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryComparisons
public import StacksFrontier.Algebra.Homology.HomotopyCategory.ExactFunctorHomology
public import StacksFrontier.AlgebraicGeometry.Spaces.SpacesEtaleModelHomComp
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.SpacesEtaleAffineGlobalPointDerived

/-!
# The morphism of models of an identity

For an algebraic space `X`, the morphism of ringed topoi that the identity of `X` induces on the
small model of the spaces-étale site (`AlgebraicGeometry.Space.spacesEtaleModelHom (𝟙 X)`) has
identity inverse image, both underived and derived: `(𝟙_X)^* ≅ 𝟭` and `L(𝟙_X)^* ≅ 𝟭`. With the
composition isomorphisms `AlgebraicGeometry.Space.spacesEtaleModelDerivedPullbackCompIso`, this
makes `Lσ^*` an equivalence for every isomorphism `σ` of algebraic spaces.

The base change along `𝟙 X` is the identity functor of the spaces-étale site, through its
cartesian projections (`AlgebraicGeometry.Space.spacesBaseChangeIdProjectionIso`); on the
models the structure map is then the identity
(`AlgebraicGeometry.Space.fSharpRing_spacesEtaleModelHom_id`), so the direct image is the
identity, and so is its left adjoint.

## Main definitions

* `AlgebraicGeometry.Space.spacesEtaleModelPullbackIdIso`: `(𝟙_X)^* ≅ 𝟭`.
* `AlgebraicGeometry.Space.spacesEtaleModelDerivedPullbackIdIso`: `L(𝟙_X)^* ≅ 𝟭`.

## References

* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (X : AlgebraicSpaces B S hS)

/-- **Base change along the identity is the identity functor of the spaces-étale site**, through
the cartesian projections, which are invertible since they are base changes of an
isomorphism. -/
def spacesBaseChangeIdProjectionIso :
    (spacesBaseChange B S hS (𝟙 X)).functor ≅ 𝟭 (SpacesEtale B S hS X) := by
  let b := spacesBaseChange B S hS (𝟙 X)
  refine NatIso.ofComponents (fun V => ?_) (fun {V W} g => ?_)
  · have hpb := b.isPullback V
    have hproj : IsIso (b.projection.app V) := hpb.isIso_fst_of_isIso
    exact (IsEtaleOver B S hS X).isoMk
      (Over.isoMk (asIso (b.projection.app V)) (by simpa using hpb.w))
  · exact (IsEtaleOver B S hS X).ι.map_injective (Over.OverMorphism.ext (b.projection.naturality g))

/-- The components of `AlgebraicGeometry.Space.spacesBaseChangeIdProjectionIso` are the
cartesian projections. -/
theorem toSpaces_map_spacesBaseChangeIdProjectionIso_hom_app (V : SpacesEtale B S hS X) :
    (SpacesEtale.toSpaces B S hS X).map ((spacesBaseChangeIdProjectionIso B S hS X).hom.app V) =
      (spacesBaseChange B S hS (𝟙 X)).projection.app V :=
  rfl

/-- **Base change along the identity on the small model** is the identity functor. -/
def smallModelBaseChangeIdIso : smallModelBaseChange B S hS (𝟙 X) ≅ 𝟭 _ :=
  Functor.isoWhiskerLeft (equivSmallModel.{u} (SpacesEtale B S hS X)).inverse
      (Functor.isoWhiskerRight (spacesBaseChangeIdProjectionIso B S hS X)
        (equivSmallModel.{u} (SpacesEtale B S hS X)).functor) ≪≫
    (equivSmallModel.{u} (SpacesEtale B S hS X)).counitIso

/-- The morphism along which the structure map of the model of `𝟙 X` pulls back regular
functions, read through `AlgebraicGeometry.Space.smallModelBaseChangeIdIso`, is the identity. -/
theorem spacesEtaleModelSharpMap_id (V : SmallModel.{u} (SpacesEtale B S hS X)) :
    (SpacesEtale.toSpaces B S hS X).map ((equivSmallModel.{u} (SpacesEtale B S hS X)).inverse.map
        ((smallModelBaseChangeIdIso B S hS X).inv.app V)) ≫
      spacesEtaleModelSharpMap B S hS (𝟙 X) V = 𝟙 _ := by
  let E := equivSmallModel.{u} (SpacesEtale B S hS X)
  let ε := spacesBaseChangeIdProjectionIso B S hS X
  let T := SpacesEtale.toSpaces B S hS X
  have hinv : (smallModelBaseChangeIdIso B S hS X).inv.app V =
      E.counitInv.app V ≫ E.functor.map (ε.inv.app (E.inverse.obj V)) := by
    simp [smallModelBaseChangeIdIso, E, ε]
  have hnat := E.unitIso.inv.naturality (ε.inv.app (E.inverse.obj V))
  have hε : T.map (ε.inv.app (E.inverse.obj V)) ≫
      (spacesBaseChange B S hS (𝟙 X)).projection.app (E.inverse.obj V) = 𝟙 _ := by
    rw [← toSpaces_map_spacesBaseChangeIdProjectionIso_hom_app, ← T.map_comp,
      Iso.inv_hom_id_app, T.map_id]
  simp only [Functor.comp_map, Functor.id_map, Functor.comp_obj, Functor.id_obj] at hnat
  rw [hinv, spacesEtaleModelSharpMap, Functor.map_comp, Functor.map_comp, Category.assoc,
    ← Functor.map_comp_assoc T (E.inverse.map (E.functor.map _)), ← Equivalence.unitInv,
    hnat]
  change T.map (E.inverse.map (E.counitInv.app V)) ≫
      T.map (E.unitInv.app (E.inverse.obj V) ≫ ε.inv.app (E.inverse.obj V)) ≫
        (spacesBaseChange B S hS (𝟙 X)).projection.app (E.inverse.obj V) = 𝟙 _
  rw [T.map_comp, Category.assoc, hε, Category.comp_id, ← T.map_comp, E.inverse_counitInv_comp V]
  exact T.map_id _

/-- **The structure map of the model of `𝟙 X` is the identity**, read through
`AlgebraicGeometry.Space.smallModelBaseChangeIdIso`. -/
theorem fSharpRing_spacesEtaleModelHom_id :
    (spacesEtaleModelHom B S hS (𝟙 X)).fSharpRing ≫
      (Functor.sheafPushforwardContinuousNatTrans (smallModelBaseChangeIdIso B S hS X).inv
        RingCat.{u} (smallModelTopology B S hS X) (smallModelTopology B S hS X)).app _ = 𝟙 _ := by
  ext V s
  apply (Shrink.ringEquiv ((SpacesEtale.structurePresheaf B S hS X).obj
    (op ((equivSmallModel.{u} (SpacesEtale B S hS X)).inverse.obj V.unop)))).injective
  have h1 := spacesEtaleModelStructureSheaf_map_apply B S hS X
    ((smallModelBaseChangeIdIso B S hS X).inv.app V.unop).op
    (((spacesEtaleModelHom B S hS (𝟙 X)).fSharp.hom.app V).hom s)
  have h2 := spacesEtaleModelHom_fSharp_apply B S hS (𝟙 X) V s
  have h5 := congrArg (fun m => ((globalFunctionsPresheaf B S hS).map m.op).hom
    (Shrink.ringEquiv ((SpacesEtale.structurePresheaf B S hS X).obj
      (op ((equivSmallModel.{u} (SpacesEtale B S hS X)).inverse.obj V.unop))) s))
    (spacesEtaleModelSharpMap_id B S hS X V.unop)
  simp only [op_comp, Functor.map_comp, CommRingCat.hom_comp, RingHom.comp_apply] at h5
  refine h1.trans ?_
  rw [h2]
  refine Eq.trans (b := ((globalFunctionsPresheaf B S hS).map (𝟙 _)).hom
    (Shrink.ringEquiv ((SpacesEtale.structurePresheaf B S hS X).obj
      (op ((equivSmallModel.{u} (SpacesEtale B S hS X)).inverse.obj V.unop))) s)) h5 ?_
  rw [CategoryTheory.Functor.map_id]
  rfl

/-- **The direct image along the model of `𝟙 X` is the identity.** -/
def spacesEtaleModelPushforwardIdIso :
    (spacesEtaleModelHom B S hS (𝟙 X)).pushforwardTopos ≅ 𝟭 _ :=
  @SheafOfModules.pushforwardCongr₂ _ _ _ _ _ _ _ _ _ _ (Functor.isContinuous_id _) _ _ _
      (smallModelBaseChangeIdIso B S hS X).symm (fSharpRing_spacesEtaleModelHom_id B S hS X) ≪≫
    SheafOfModules.pushforwardId _

/-- **The inverse image along the model of `𝟙 X` is the identity**, by uniqueness of left
adjoints. -/
def spacesEtaleModelPullbackIdIso :
    (spacesEtaleModelHom B S hS (𝟙 X)).pullbackTopos ≅ 𝟭 _ :=
  (spacesEtaleModelHom B S hS (𝟙 X)).pullbackPushforwardAdjunctionTopos.leftAdjointUniq
    (Adjunction.id.ofNatIsoRight (spacesEtaleModelPushforwardIdIso B S hS X).symm)

open Stacks.Cohomology.DerivedPullbackPushforwardAdjunction

attribute [local instance high] HasDerivedCategory.standard

attribute [local instance] RingedSite.hasSheafCompose_forget₂_ringCat

/-- **The derived pullback along the model of `𝟙 X` is the identity**: the inverse image is the
identity, hence exact, so the derived pullback is the functor it induces on derived categories. -/
def spacesEtaleModelDerivedPullbackIdIso :
    derivedPullback.{u} (spacesEtaleModelHom B S hS (𝟙 X)) ≅ 𝟭 _ :=
  haveI : PreservesFiniteLimits (spacesEtaleModelHom B S hS (𝟙 X)).pullbackTopos :=
    preservesFiniteLimits_of_natIso (spacesEtaleModelPullbackIdIso B S hS X).symm
  haveI : PreservesFiniteColimits (spacesEtaleModelHom B S hS (𝟙 X)).pullbackTopos :=
    preservesFiniteColimits_of_natIso (spacesEtaleModelPullbackIdIso B S hS X).symm
  derivedPullbackIsoMapDerivedCategoryOfExact (spacesEtaleModelHom B S hS (𝟙 X)) ≪≫
    Stacks.DerivedCategoryComparisons.mapDerivedCategoryIsoOfNatIso _ _
      (spacesEtaleModelPullbackIdIso B S hS X) ≪≫
    Stacks.Homology.mapDerivedCategoryIdIso

end AlgebraicGeometry.Space

end
