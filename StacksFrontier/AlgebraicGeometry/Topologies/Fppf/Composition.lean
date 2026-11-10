module

public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.MorphismOfTopoi
public import StacksCore.Tactic.StacksAttribute

/-!
# Composition of morphisms of big fppf topoi

For composable morphisms of schemes in a big fppf site, the morphism of topoi attached to
their composite agrees with the composite of their morphisms of topoi.  The comparison is
given by a pair of natural isomorphisms, one on direct images and one on inverse images,
which together respect the units of the two adjunctions.

## Main definitions

* `AlgebraicGeometry.ranCompIso`: right Kan extension along a composite is the composite of
  the right Kan extensions.
* `AlgebraicGeometry.sheafPushforwardCocontinuousCompIso`: the direct-image compositor for
  cocontinuous site functors, with no smallness assumption on the sites.

## Main results

* `AlgebraicGeometry.bigFppfMorphism_comp_pushforwardIso`: the comparison of direct images.
* `AlgebraicGeometry.bigFppfMorphism_comp_inverseImageIso`: the comparison of inverse
  images.
* `AlgebraicGeometry.bigFppfMorphism_comp_adjunction`: the two comparisons are compatible
  with the adjunction units.

## Implementation notes

The big fppf topos over a scheme is the sheaf category of the corresponding slice site, and
composition of the slice functors is identified by `CategoryTheory.Over.mapComp_eq`.  The
direct-image comparison is induced by composition of cocontinuous site functors and is
obtained from the uniqueness of right Kan extensions, a form which allows the object and
morphism universes of the slice sites to differ.  The inverse-image comparison is its mate
under the two adjunctions; the unit equation is what says the pair is an isomorphism of
geometric morphisms rather than two unrelated isomorphisms of functors.  The statement is
made for schemes in the big site without fixing a base, since the structure morphisms play
no role in composition.

## References

* [Stacks Project, Tag 021X](https://stacks.math.columbia.edu/tag/021X)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry

/-- Right Kan extension along a composite is the composite of right Kan extensions. -/
public noncomputable def ranCompIso {C : Type*} [Category* C]
    {D : Type*} [Category* D] {E : Type*} [Category* E]
    (A : Type*) [Category* A] (F : C ⥤ D) (G : D ⥤ E)
    [∀ P : C ⥤ A, F.HasRightKanExtension P]
    [∀ P : D ⥤ A, G.HasRightKanExtension P]
    [∀ P : C ⥤ A, (F ⋙ G).HasRightKanExtension P] :
    (F ⋙ G).ran (H := A) ≅ F.ran (H := A) ⋙ G.ran (H := A) :=
  ((F ⋙ G).ranAdjunction A).rightAdjointUniq
    (((G.ranAdjunction A).comp (F.ranAdjunction A)).ofNatIsoLeft
      (eqToIso
        (rfl :
          (Functor.whiskeringLeft D E A).obj G ⋙
              (Functor.whiskeringLeft C D A).obj F =
            (Functor.whiskeringLeft C E A).obj (F ⋙ G))))

/-- The canonical direct-image compositor for cocontinuous site functors, stated without a
small-category assumption on the sites. -/
public noncomputable def sheafPushforwardCocontinuousCompIso
    {C : Type*} [Category* C] {D : Type*} [Category* D]
    {E : Type*} [Category* E] (A : Type*) [Category* A]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (L : GrothendieckTopology E) (F : C ⥤ D) (G : D ⥤ E)
    [F.IsCocontinuous J K] [G.IsCocontinuous K L]
    [∀ P : Cᵒᵖ ⥤ A, F.op.HasPointwiseRightKanExtension P]
    [∀ P : Dᵒᵖ ⥤ A, G.op.HasPointwiseRightKanExtension P]
    [∀ P : Cᵒᵖ ⥤ A, (F ⋙ G).op.HasPointwiseRightKanExtension P] :
    letI := isCocontinuous_comp F G J K (L := L)
    (F ⋙ G).sheafPushforwardCocontinuous A J L ≅
      F.sheafPushforwardCocontinuous A J K ⋙
        G.sheafPushforwardCocontinuous A K L :=
  letI := isCocontinuous_comp F G J K (L := L)
  haveI : ∀ P : Cᵒᵖ ⥤ A, (F.op ⋙ G.op).HasPointwiseRightKanExtension P :=
    fun P => inferInstanceAs ((F ⋙ G).op.HasPointwiseRightKanExtension P)
  Functor.fullyFaithfulCancelRight (sheafToPresheaf L A)
    (Functor.isoWhiskerLeft (sheafToPresheaf J A) (ranCompIso A F.op G.op))

/-- **Stacks 021X.** Composition of the morphisms of big fppf topoi agrees, naturally on
sheaves, with the morphism attached to the composite map of schemes. -/
@[stacks 021X "canonical direct-image comparison"]
public noncomputable def bigFppfMorphism_comp_pushforwardIso
    (B : AlgebraicGeometry.BigFppfSite.{u}) {X Y Z : B.Schemes}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    (bigFppfMorphism B X Z (f ≫ g)).pushforward ≅
      ((bigFppfMorphism B Y Z g).comp
        (bigFppfMorphism B X Y f)).pushforward := by
  change (Over.map (f ≫ g)).sheafPushforwardCocontinuous
      (Type (u + 1)) (B.topology.over X) (B.topology.over Z) ≅
    (Over.map f).sheafPushforwardCocontinuous
      (Type (u + 1)) (B.topology.over X) (B.topology.over Y) ⋙
    (Over.map g).sheafPushforwardCocontinuous
      (Type (u + 1)) (B.topology.over Y) (B.topology.over Z)
  simpa only [Over.mapComp_eq] using
    (sheafPushforwardCocontinuousCompIso (Type (u + 1)) (B.topology.over X)
      (B.topology.over Y) (B.topology.over Z) (Over.map f) (Over.map g))

/-- **Stacks 021X.** The inverse-image comparison is the mate of the direct-image
comparison. -/
@[stacks 021X "canonical inverse-image comparison"]
public noncomputable def bigFppfMorphism_comp_inverseImageIso
    (B : AlgebraicGeometry.BigFppfSite.{u}) {X Y Z : B.Schemes}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    (bigFppfMorphism B X Z (f ≫ g)).inverseImage ≅
      ((bigFppfMorphism B Y Z g).comp
        (bigFppfMorphism B X Y f)).inverseImage :=
  (bigFppfMorphism B X Z (f ≫ g)).adj.leftAdjointUniq
    (((bigFppfMorphism B Y Z g).comp
      (bigFppfMorphism B X Y f)).adj.ofNatIsoRight
        (bigFppfMorphism_comp_pushforwardIso B f g).symm)

/-- **Stacks 021X.** The two canonical comparisons respect the units of the geometric
morphisms. -/
@[stacks 021X "compatibility with the adjunction"]
public theorem bigFppfMorphism_comp_adjunction
    (B : AlgebraicGeometry.BigFppfSite.{u}) {X Y Z : B.Schemes}
    (f : X ⟶ Y) (g : Y ⟶ Z)
    (V : Sheaf (B.topology.over Z) (Type (u + 1))) :
    let h := bigFppfMorphism B X Z (f ≫ g)
    let k := (bigFppfMorphism B Y Z g).comp
      (bigFppfMorphism B X Y f)
    h.adj.unit.app V ≫
        h.pushforward.map ((bigFppfMorphism_comp_inverseImageIso B f g).hom.app V) ≫
        (bigFppfMorphism_comp_pushforwardIso B f g).hom.app
          (k.inverseImage.obj V) = k.adj.unit.app V := by
  dsimp only
  let β := bigFppfMorphism_comp_pushforwardIso B f g
  let h := bigFppfMorphism B X Z (f ≫ g)
  let k := (bigFppfMorphism B Y Z g).comp (bigFppfMorphism B X Y f)
  let b := k.adj.ofNatIsoRight β.symm
  let α := h.adj.leftAdjointUniq b
  change h.adj.unit.app V ≫ h.pushforward.map (α.hom.app V) ≫
      β.hom.app (k.inverseImage.obj V) = k.adj.unit.app V
  rw [← Category.assoc, Adjunction.unit_leftAdjointUniq_hom_app h.adj b V]
  simp [b, Adjunction.ofNatIsoRight_unit]

end AlgebraicGeometry
