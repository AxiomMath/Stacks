module

public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.RepresentableBridgePseudofunctor
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.BigSmallEtaleSquare
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SurjectiveInverseImageFaithful
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BoundedSiteBaseChangeRestriction
public import StacksFrontier.CategoryTheory.Sites.Modules.InverseImage.AbelianSheaf

/-!
# Inverse image along a surjection of schemes is faithful on spaces-étale sheaves

Let `m : W ⟶ V` be a morphism of the big fppf site of `S` whose underlying morphism of schemes is
surjective. Inverse image along `m` is faithful on bounded small étale sheaves of sets, and so is
inverse image along `h_m : h_W ⟶ h_V` on the spaces-étale sites of the represented algebraic
spaces. Inverse image of abelian spaces-étale sheaves along `h_m` reflects zero objects.

## Main definitions

* `AlgebraicGeometry.BigEtaleSpaceSite.RepresentableSurjectiveReflectsZero`: the statement that
  inverse image of abelian sheaves along `h_m` reflects zero objects for every surjective `m`.

## Main results

* `AlgebraicGeometry.Space.faithful_representedSchemesInverseImage_of_surjective`: inverse image
  of bounded small étale sheaves along a surjection is faithful.
* `AlgebraicGeometry.Space.faithful_representedSpacesInverseImage_of_surjective`: the same on the
  spaces-étale sites of represented algebraic spaces.
* `AlgebraicGeometry.BigEtaleSpaceSite.representableSurjectiveReflectsZero`: that statement
  holds.

## References

* [Stacks Project, Tag 09Z3](https://stacks.math.columbia.edu/tag/09Z3)
* [Stacks Project, Tag 03G1](https://stacks.math.columbia.edu/tag/03G1)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **Inverse image of bounded small étale sheaves of sets along a surjection is faithful.** -/
theorem faithful_representedSchemesInverseImage_of_surjective {V W : BigFppfOver B S hS}
    (m : W ⟶ V) (hm : Surjective ((BigFppfOver.toScheme B S hS).map m)) :
    ((representedSchemesPseudofunctor B S hS).map m.op.toLoc).toFunctor.Faithful := by
  let B' := associatedBigEtaleSite B
  have e := SmallEtale.restrictionPullbackBaseChangeIso B' (Type (u + 1))
    (S := V.left) (T := W.left) m.left
    (Stacks.EtaleCohomology.smallEtaleInverseImageAdjunction.{u, 0}
      ((BigFppfOver.toScheme B S hS).map m))
    (representedSchemesAdjunction m)
  have hU : (Stacks.EtaleCohomology.smallEtaleInverseImage.{u, 0}
      ((BigFppfOver.toScheme B S hS).map m)).Faithful :=
    Stacks.EtaleCohomology.faithful_smallEtaleInverseImage_of_surjective _
  let ρV := (_root_.AlgebraicGeometry.SmallEtale.toEtaleSite B' V.left.obj
    V.left.property).sheafPushforwardContinuous (Type (u + 1))
      (_root_.AlgebraicGeometry.SmallEtale.topology B' V.left.obj V.left.property)
      V.left.obj.smallEtaleTopology
  let ρW := (_root_.AlgebraicGeometry.SmallEtale.toEtaleSite B' W.left.obj
    W.left.property).sheafPushforwardContinuous (Type (u + 1))
      (_root_.AlgebraicGeometry.SmallEtale.topology B' W.left.obj W.left.property)
      W.left.obj.smallEtaleTopology
  have hV : ρV.IsEquivalence := (_root_.AlgebraicGeometry.SmallEtale.sheafEquiv B' V.left.obj
    V.left.property (Type (u + 1))).isEquivalence_inverse
  have hW : ρW.IsEquivalence := (_root_.AlgebraicGeometry.SmallEtale.sheafEquiv B' W.left.obj
    W.left.property (Type (u + 1))).isEquivalence_inverse
  have hc := @Functor.Faithful.comp _ _ _ _ _ _ _ ρW hU hW.faithful
  have hρL := @Functor.Faithful.of_iso _ _ _ _ _ _ hc e.symm
  have h2 := @Functor.Faithful.comp _ _ _ _ _ _ ρV.asEquivalence.inverse _ inferInstance hρL
  exact @Functor.Faithful.of_iso _ _ _ _ _ _ h2 (ρV.asEquivalence.invFunIdAssoc _)

/-- **Inverse image of spaces-étale sheaves of sets along `h_m` is faithful** when the morphism of
schemes underlying `m` is surjective. -/
theorem faithful_representedSpacesInverseImage_of_surjective {V W : BigFppfOver B S hS}
    (m : W ⟶ V) (hm : Surjective ((BigFppfOver.toScheme B S hS).map m)) :
    ((representedSpacesPseudofunctor B S hS).map m.op.toLoc).toFunctor.Faithful := by
  have hS' := faithful_representedSchemesInverseImage_of_surjective m hm
  have e := Cat.Hom.toNatIso
    ((representedComparison (B := B) (S := S) (hS := hS)).naturality m.op.toLoc)
  have h1 := @Functor.Faithful.comp _ _ _ _ _ _ (representedRestriction V
      (Type (u + 1))) _ inferInstance hS'
  have : (((representedSpacesPseudofunctor B S hS).map m.op.toLoc).toFunctor ⋙
      representedRestriction W (Type (u + 1))).Faithful :=
    @Functor.Faithful.of_iso _ _ _ _ _ _ h1 e.symm
  exact Functor.Faithful.of_comp _ (representedRestriction W (Type (u + 1)))

end AlgebraicGeometry.Space

namespace AlgebraicGeometry.BigEtaleSpaceSite

variable {S : Scheme.{u}} (T : BigEtaleSpaceSite S)

/-- **Inverse image along a surjection of schemes reflects zero objects**, read on the
spaces-étale sites: for a morphism `m : W ⟶ V` of the big fppf site of `S` whose underlying
morphism of schemes is surjective, an abelian sheaf on the spaces-étale site of `h_V` whose
inverse image along `h_m` is zero is zero. -/
def RepresentableSurjectiveReflectsZero : Prop :=
  ∀ ⦃V W : BigFppfOver T.fppfSite S T.fppf_mem⦄ (m : W ⟶ V),
    _root_.AlgebraicGeometry.Surjective ((BigFppfOver.toScheme T.fppfSite S T.fppf_mem).map m) →
    ∀ G : Sheaf (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem
        (Space.yonedaSpace T.fppfSite S T.fppf_mem V)) Ab.{u + 1},
      IsZero ((CategoryTheory.Sites.abelianInverseImage
        (smallEtaleMorphism T (Space.yonedaSpaceHom m))).obj G) → IsZero G

/-- **Inverse image of abelian spaces-étale sheaves along a surjection of schemes reflects zero
objects**: `AlgebraicGeometry.BigEtaleSpaceSite.RepresentableSurjectiveReflectsZero` holds. -/
theorem representableSurjectiveReflectsZero : RepresentableSurjectiveReflectsZero T := by
  intro V W m hm G hG
  let L := CategoryTheory.Sites.abelianInverseImage
    (smallEtaleMorphism T (Space.yonedaSpaceHom m))
  have : L.Additive := Functor.additive_of_preserves_binary_products _
  have hset := Space.faithful_representedSpacesInverseImage_of_surjective m hm
  have : (sheafCompose (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem
      (Space.yonedaSpace T.fppfSite S T.fppf_mem V)) (forget Ab.{u + 1}) ⋙
        (smallEtaleMorphism T (Space.yonedaSpaceHom m)).inverseImage).Faithful :=
    @Functor.Faithful.comp _ _ _ _ _ _ _ _ _ hset
  have : (L ⋙ sheafCompose (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem
      (Space.yonedaSpace T.fppfSite S T.fppf_mem W)) (forget Ab.{u + 1})).Faithful :=
    Functor.Faithful.of_iso (CategoryTheory.Sites.abelianInverseImage_forgetIso _).symm
  have : L.Faithful := Functor.Faithful.of_comp _
    (sheafCompose (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem
      (Space.yonedaSpace T.fppfSite S T.fppf_mem W)) (forget Ab.{u + 1}))
  rw [IsZero.iff_id_eq_zero] at hG ⊢
  exact L.map_injective (by rwa [L.map_id, L.map_zero])

end AlgebraicGeometry.BigEtaleSpaceSite

end
