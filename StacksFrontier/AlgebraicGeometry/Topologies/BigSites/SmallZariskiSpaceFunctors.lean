module

public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.Topology.Sheaves.Functors
public import StacksFrontier.AlgebraicGeometry.Topologies.BigSites.SmallZariskiBaseChange
public import StacksFrontier.AlgebraicGeometry.Topologies.BigSites.SmallZariskiOpens
public import StacksFrontier.CategoryTheory.Sites.MorphismOfSites.TopologicalComparison

/-!
# Small Zariski inverse and direct image are the usual ones

Under the identification of sheaves on the small Zariski site of a scheme with sheaves on its
underlying topological space (Stacks 020X), the inverse-image and direct-image functors
induced by small-site base change along `f : T ⟶ S` are the usual inverse and direct image of
sheaves along the continuous map underlying `f`.

## Main results

* `AlgebraicGeometry.smallZariskiToOpens_baseChange_eq` — the open-image functor intertwines
  small-site base change with the induced map of opens.
* `AlgebraicGeometry.smallZariskiPullbackIso` — the two inverse-image functors agree.
* `AlgebraicGeometry.smallZariskiPushforwardIso` — the two direct-image functors agree.

## Implementation notes

The underlying statement is `smallZariskiToOpens_baseChange_eq`: the open image of the fibre
product `U ×_S T` is the preimage of the open image of `U`, so the open-image functor
intertwines small-site base change with the map of opens. That is an equality of functors, not
merely an isomorphism, because both sides are computed by taking the range of an open
immersion.

Both conclusions are isomorphisms of functors, hence natural in the sheaf. The direct-image
comparison is obtained from the equality of functors by composing the two
`sheafPushforwardContinuous` comparisons, and the inverse-image comparison is its mate under
the two adjunctions.

## References

* [Stacks Project, Tag 0211](https://stacks.math.columbia.edu/tag/0211)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

variable (B : BigZariskiSite.{u}) {S T : B.Schemes} (f : T ⟶ S)

/-- Base change on the small Zariski site sends an object to the inverse image
of its open subset under the underlying continuous map. -/
public theorem smallZariskiToOpens_baseChange_obj
    (X : SmallZariski B S.1 S.property) :
    (smallZariskiToOpens B T.1 T.property).obj
        ((smallZariskiBaseChange B f).obj X) =
      (Opens.map (B.inclusion.map f).base).obj
        ((smallZariskiToOpens B S.1 S.property).obj X) := by
  let e := smallZariskiBaseChangeIso B f
  let j := (smallSiteInSchemesOver B S).obj X |>.hom
  let Yover := (Over.pullback (B.inclusion.map f)).obj
    ((smallSiteInSchemesOver B S).obj X)
  have : IsOpenImmersion j := by
    change IsOpenImmersion (B.inclusion.map X.obj.hom)
    exact X.property
  have htri :
      (e.hom.app X).left ≫ Yover.hom =
        B.inclusion.map ((smallZariskiBaseChange B f).obj X).obj.hom :=
    (e.hom.app X).w
  have : IsIso (e.hom.app X) := (e.app X).isIso_hom
  have : IsIso (e.hom.app X).left :=
    (Over.forget T.1).map_isIso (e.hom.app X)
  change (B.inclusion.map
      ((smallZariskiBaseChange B f).obj X).obj.hom).opensRange = _
  apply Opens.ext
  change Set.range (B.inclusion.map
      ((smallZariskiBaseChange B f).obj X).obj.hom) = _
  have hsurj : Function.Surjective (e.hom.app X).left := by
    have : IsIso ((e.hom.app X).left.base) :=
      (Scheme.forgetToTop).map_isIso (e.hom.app X).left
    exact ((TopCat.isIso_iff_isHomeomorph _).mp inferInstance).bijective.2
  calc
    _ = Set.range ((e.hom.app X).left ≫ Yover.hom) := by
      rw [htri]
    _ = Set.range Yover.hom := by
      change Set.range (Yover.hom ∘ (e.hom.app X).left) = _
      rw [Set.range_comp, Set.range_eq_univ.mpr hsurj, Set.image_univ]
    _ = (B.inclusion.map f) ⁻¹ᵁ j.opensRange := by
      simpa only [Yover, Over.pullback_obj_hom, Over.pullback_obj_left] using
        (IsOpenImmersion.range_pullbackSnd j (B.inclusion.map f))
    _ = (B.inclusion.map f) ⁻¹ᵁ (B.inclusion.map X.obj.hom).opensRange := by
      rfl

/-- The small-site base-change functor commutes with the canonical functors to
the lattices of open subsets. -/
public theorem smallZariskiToOpens_baseChange_eq :
    smallZariskiBaseChange B f ⋙
        smallZariskiToOpens B T.1 T.property =
      smallZariskiToOpens B S.1 S.property ⋙
        Opens.map (B.inclusion.map f).base :=
  CategoryTheory.Functor.ext (smallZariskiToOpens_baseChange_obj B f)
    (fun _ _ _ => Subsingleton.elim _ _)

/-- Under the identification of sheaves on the small Zariski site with sheaves on opens, the
direct image along small-site base change is the direct image along the map of opens. -/
public noncomputable def smallSitePushforwardAdjointIso :
    (smallZariskiSheafEquiv B T.1 T.property).inverse ⋙
        (smallZariskiBaseChange B f).sheafPushforwardContinuous
          (Type (u + 1))
          (SmallZariski.topology B S.1 S.property)
          (SmallZariski.topology B T.1 T.property) ≅
      (Opens.map (B.inclusion.map f).base).sheafPushforwardContinuous (Type (u + 1))
          (Opens.grothendieckTopology
            ((B.inclusion.obj S).toPresheafedSpace : TopCat))
          (Opens.grothendieckTopology
            ((B.inclusion.obj T).toPresheafedSpace : TopCat)) ⋙
        (smallZariskiSheafEquiv B S.1 S.property).inverse := by
  let uS := smallZariskiToOpens B S.1 S.property
  let uT := smallZariskiToOpens B T.1 T.property
  let F := smallZariskiBaseChange B f
  let g := Opens.map (B.inclusion.map f).base
  let JS := SmallZariski.topology B S.1 S.property
  let JT := SmallZariski.topology B T.1 T.property
  let KS := Opens.grothendieckTopology S.1.carrier
  let KT := Opens.grothendieckTopology T.1.carrier
  have : F.IsContinuous JS JT :=
    (smallZariskiBaseChange_isMorphismOfSites B f).toIsContinuous
  have : g.IsContinuous KS KT :=
    (StacksZariskiSite.isMorphismOfSites_opensMap (B.inclusion.map f).base).isContinuous
  have : (F ⋙ uT).IsContinuous JS KT := Functor.isContinuous_comp F uT JS JT KT
  have : (uS ⋙ g).IsContinuous JS KT := Functor.isContinuous_comp uS g JS KS KT
  change uT.sheafPushforwardContinuous (Type (u + 1)) JT KT ⋙
      F.sheafPushforwardContinuous (Type (u + 1)) JS JT ≅
    g.sheafPushforwardContinuous (Type (u + 1)) KS KT ⋙
      uS.sheafPushforwardContinuous (Type (u + 1)) JS KS
  exact (Functor.sheafPushforwardContinuousComp F uT (Type (u + 1)) JS JT KT).trans <|
    (Functor.sheafPushforwardContinuousIso
      (eqToIso (smallZariskiToOpens_baseChange_eq B f))
      (Type (u + 1)) JS KT).trans <|
      (Functor.sheafPushforwardContinuousComp uS g (Type (u + 1)) JS KS KT).symm

/-- Under the small-site equivalences, inverse image is the usual inverse image
of sheaves on the underlying topological spaces. -/
@[stacks 0211 "usual_small_functors"]
public noncomputable def smallZariskiPullbackIso :
    (smallZariskiSheafEquiv B S.1 S.property).functor ⋙
      (Opens.map (B.inclusion.map f).base).sheafPullback (Type (u + 1))
        (Opens.grothendieckTopology ((B.inclusion.obj S).toPresheafedSpace : TopCat))
        (Opens.grothendieckTopology ((B.inclusion.obj T).toPresheafedSpace : TopCat)) ≅
      (smallZariskiBaseChange B f).sheafPullback (Type (u + 1))
      (SmallZariski.topology B S.1 S.property)
      (SmallZariski.topology B T.1 T.property) ⋙
      (smallZariskiSheafEquiv B T.1 T.property).functor := by
  let eS := smallZariskiSheafEquiv B S.1 S.property
  let eT := smallZariskiSheafEquiv B T.1 T.property
  let g := Opens.map (B.inclusion.map f).base
  let F := smallZariskiBaseChange B f
  let JS := SmallZariski.topology B S.1 S.property
  let JT := SmallZariski.topology B T.1 T.property
  let KS := Opens.grothendieckTopology
    ((B.inclusion.obj S).toPresheafedSpace : TopCat)
  let KT := Opens.grothendieckTopology
    ((B.inclusion.obj T).toPresheafedSpace : TopCat)
  have : F.IsContinuous JS JT :=
    (smallZariskiBaseChange_isMorphismOfSites B f).toIsContinuous
  have : g.IsContinuous KS KT :=
    (StacksZariskiSite.isMorphismOfSites_opensMap (B.inclusion.map f).base).isContinuous
  let adjL := eS.toAdjunction.comp
    (g.sheafAdjunctionContinuous (Type (u + 1)) KS KT)
  let adjR := (F.sheafAdjunctionContinuous (Type (u + 1)) JS JT).comp eT.toAdjunction
  exact adjL.leftAdjointUniq (adjR.ofNatIsoRight (smallSitePushforwardAdjointIso B f))

/-- Under the small-site equivalences, direct image is the usual direct image
of sheaves on the underlying topological spaces. -/
@[stacks 0211 "usual_small_functors"]
public noncomputable def smallZariskiPushforwardIso :
    (smallZariskiSheafEquiv B T.1 T.property).functor ⋙
      (Opens.map (B.inclusion.map f).base).sheafPushforwardContinuous (Type (u + 1))
        (Opens.grothendieckTopology ((B.inclusion.obj S).toPresheafedSpace : TopCat))
        (Opens.grothendieckTopology ((B.inclusion.obj T).toPresheafedSpace : TopCat)) ≅
      (smallZariskiBaseChange B f).sheafPushforwardContinuous
      (Type (u + 1))
      (SmallZariski.topology B S.1 S.property)
      (SmallZariski.topology B T.1 T.property) ⋙
      (smallZariskiSheafEquiv B S.1 S.property).functor := by
  let eS := smallZariskiSheafEquiv B S.1 S.property
  let eT := smallZariskiSheafEquiv B T.1 T.property
  let g := (Opens.map (B.inclusion.map f).base).sheafPushforwardContinuous
    (Type (u + 1))
    (Opens.grothendieckTopology
      ((B.inclusion.obj S).toPresheafedSpace : TopCat))
    (Opens.grothendieckTopology
      ((B.inclusion.obj T).toPresheafedSpace : TopCat))
  let p := (smallZariskiBaseChange B f).sheafPushforwardContinuous
    (Type (u + 1))
    (SmallZariski.topology B S.1 S.property)
    (SmallZariski.topology B T.1 T.property)
  exact
    (Functor.rightUnitor (eT.functor ⋙ g)).symm ≪≫
      Functor.isoWhiskerLeft (eT.functor ⋙ g) eS.counitIso.symm ≪≫
      Functor.associator eT.functor g (eS.inverse ⋙ eS.functor) ≪≫
      Functor.isoWhiskerLeft eT.functor
        (Functor.associator g eS.inverse eS.functor).symm ≪≫
      Functor.isoWhiskerLeft eT.functor
        (Functor.isoWhiskerRight (smallSitePushforwardAdjointIso B f).symm eS.functor) ≪≫
      Functor.isoWhiskerLeft eT.functor
        (Functor.associator eT.inverse p eS.functor) ≪≫
      (Functor.associator eT.functor eT.inverse (p ⋙ eS.functor)).symm ≪≫
      Functor.isoWhiskerRight eT.unitIso.symm (p ⋙ eS.functor) ≪≫
      Functor.leftUnitor (p ⋙ eS.functor)

end AlgebraicGeometry
