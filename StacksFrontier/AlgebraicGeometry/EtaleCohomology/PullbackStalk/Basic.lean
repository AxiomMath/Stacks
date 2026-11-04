module

public import StacksCore.Tactic.StacksAttribute
public import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
public import Mathlib.CategoryTheory.Sites.Point.Comap
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.PullbackStalk.ElementsColimit
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Sweep.EtaleStalkFunctor
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.PullbackStalk.BaseChangeFiber
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.PullbackStalk.SitePoint

/-!
# Stalks of inverse images on small étale sites

For a morphism `f : T ⟶ S` in a big étale site and a geometric point `x` of `T`, the stalk at
`x` of the inverse image of a sheaf on the small étale site of `S` is canonically the stalk of
the original sheaf at the image geometric point `f ∘ x`. The identification is natural in the
sheaf, and is pinned down by its effect on germs: a section over an étale neighborhood of the
image point, pulled back along the adjunction unit and restricted to a pointed étale
neighborhood of `x`, has the same germ as the original section.

The construction goes through points of sites. A geometric point of `S` is a point of the small
étale site of `S` (`AlgebraicGeometry.geometricPointSitePoint`) whose stalk functor is
`AlgebraicGeometry.etaleStalkFunctor`, base change is a representably flat continuous
cover-preserving functor, and the fibre functor of the image point is the fibre functor of `x`
precomposed with base change
(`AlgebraicGeometry.geometricPointFiberBaseChangeIso`). The comparison is therefore the
composite of Mathlib's isomorphism for the inverse image of a point along a morphism of sites
with the invariance of the elements-colimit under an isomorphism of fibre functors.

## Main definitions

* `AlgebraicGeometry.pullbackSectionAlong` — a section over an étale neighborhood of the image
  point, pulled back to an étale neighborhood of `x` over its base change.
* `AlgebraicGeometry.smallEtalePullbackStalkIso` — the comparison of stalk functors.

## Main results

* `AlgebraicGeometry.smallEtalePullbackStalkIso_germ` — the comparison on germs.

## References

* [Stacks Project, Tag 03Q1](https://stacks.math.columbia.edu/tag/03Q1)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.GrothendieckTopology

universe u v w r

namespace CategoryTheory.GrothendieckTopology.Point

open Opposite

section

variable {C : Type*} [Category* C] {J : GrothendieckTopology C}
  {A : Type*} [Category.{v} A] [HasColimitsOfSize.{w, w} A]

/-- The canonical map from the sections of a sheaf over `X` into its stalk at an element `x`
of the fibre of a point over `X`. -/
public def toSheafFiber (Φ : Point.{w} J) (F : Sheaf J A) (X : C) (x : Φ.fiber.obj X) :
    F.obj.obj (op X) ⟶ Φ.sheafFiber.obj F :=
  Φ.toPresheafFiber X x F.obj

/-- Taking the stalk at `x` is natural in the sheaf. -/
@[reassoc]
public lemma toSheafFiber_naturality (Φ : Point.{w} J) {F G : Sheaf J A} (φ : F ⟶ G)
    (X : C) (x : Φ.fiber.obj X) :
    Φ.toSheafFiber F X x ≫ Φ.sheafFiber.map φ =
      φ.hom.app (op X) ≫ Φ.toSheafFiber G X x :=
  Φ.toPresheafFiber_naturality φ.hom X x

end

section

variable {C : Type*} [Category* C] {J : GrothendieckTopology C}
  {A : Type*} [Category.{v} A] [HasProducts.{w} A] [HasColimitsOfSize.{w, w} A]

/-- On a skyscraper sheaf, the canonical map into the stalk followed by the counit of the
skyscraper adjunction is the projection to the factor indexed by `x`. -/
public lemma toSheafFiber_skyscraper (Φ : Point.{w} J) (M : A) (X : C) (x : Φ.fiber.obj X) :
    Φ.toSheafFiber (Φ.skyscraperSheafFunctor.obj M) X x ≫
      Φ.skyscraperSheafAdjunction.counit.app M = Pi.π _ x := by
  rw [← Adjunction.homEquiv_symm_id]
  simp only [Point.skyscraperSheafAdjunction, Functor.FullyFaithful.homEquiv, toSheafFiber,
    Adjunction.mkOfHomEquiv_homEquiv, Functor.id_obj, Functor.op_obj]
  exact (Φ.toPresheafFiber_skyscraperPresheafHomEquiv_symm
    (𝟙 (Φ.skyscraperPresheaf M)) X x).trans (Category.id_comp _)

/-- The unit of the skyscraper adjunction, followed by the projection to the factor indexed by
`x`, is the canonical map into the stalk at `x`. -/
public lemma unit_app_app_π (Φ : Point.{w} J) (F : Sheaf J A) (X : C) (x : Φ.fiber.obj X) :
    (Φ.skyscraperSheafAdjunction.unit.app F).hom.app (op X) ≫ Pi.π _ x =
      Φ.toSheafFiber F X x := by
  rw [← Adjunction.homEquiv_id]
  simp only [Point.skyscraperSheafAdjunction, Functor.FullyFaithful.homEquiv, toSheafFiber,
    Adjunction.mkOfHomEquiv_homEquiv, Functor.id_obj, Functor.comp_obj, Functor.op_obj]
  exact (Φ.skyscraperPresheafHomEquiv_app_π
    (𝟙 (Φ.presheafFiber.obj F.obj)) X x).trans (Category.comp_id _)

end

variable {C D : Type*} [Category* C] [Category* D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  (q : Point.{w} K) (u : C ⥤ D) [RepresentablyFlat u]
  [u.IsContinuous J K] (hu : CoverPreserving J K u)
  [InitiallySmall.{w} (u ⋙ q.fiber).Elements]
  {A : Type*} [Category.{v} A] [HasProducts.{w} A]
  [(u.sheafPushforwardContinuous A J K).IsRightAdjoint]
  [HasColimitsOfSize.{w, w} A]

/-- Mathlib's identification of the stalk at an inverse-image point with the stalk of the
inverse image is compatible with the canonical maps from the sections: the map from the
sections over `V` into the stalk at the comap point, followed by the identification, is the
adjunction unit followed by the map into the stalk of the inverse image. -/
public lemma toSheafFiber_sheafFiberComapIso_hom (F : Sheaf J A) (V : C)
    (x : (q.comap u hu).fiber.obj V) :
    (q.comap u hu).toSheafFiber F V x ≫ (q.sheafFiberComapIso u hu A).hom.app F =
      ((u.sheafAdjunctionContinuous A J K).unit.app F).hom.app (op V) ≫
        q.toSheafFiber ((u.sheafPullback A J K).obj F) (u.obj V) x := by
  rw [Point.sheafFiberComapIso_hom_app]
  simp only [toSheafFiber_naturality_assoc]
  rw [toSheafFiber_skyscraper]
  exact congrArg
    (fun k => ((u.sheafAdjunctionContinuous A J K).unit.app F).hom.app (op V) ≫ k)
    ((congrArg (fun k => ((u.sheafPushforwardContinuous A J K).map
        (q.skyscraperSheafAdjunction.unit.app ((u.sheafPullback A J K).obj F))).hom.app (op V) ≫ k)
      (Category.id_comp (Pi.π (fun _ : (q.comap u hu).fiber.obj V =>
        q.sheafFiber.obj ((u.sheafPullback A J K).obj F)) x))).trans
      (unit_app_app_π q ((u.sheafPullback A J K).obj F) (u.obj V) x))

end CategoryTheory.GrothendieckTopology.Point

namespace AlgebraicGeometry

/-- Pull a section over `V` back to an étale neighborhood `U` mapping to the base change
of `V`. -/
public def pullbackSectionAlong (B : BigEtaleSite.{u})
    {S T : B.Scheme} (f : T ⟶ S)
    (F : Sheaf (SmallEtale.topology B S.1 S.property) (Type (u + 1)))
    (V : SmallEtale B S.1 S.property) (U : SmallEtale B T.1 T.property)
    (a : U ⟶ (smallEtaleBaseChange B f).obj V) :
    F.obj.obj (Opposite.op V) →
      (((smallEtaleBaseChange B f).sheafPullback (Type (u + 1))
        (SmallEtale.topology B S.1 S.property)
        (SmallEtale.topology B T.1 T.property)).obj F).obj.obj (Opposite.op U) :=
  fun t =>
    let η := (((smallEtaleBaseChange B f).sheafAdjunctionContinuous (Type (u + 1))
      (SmallEtale.topology B S.1 S.property)
      (SmallEtale.topology B T.1 T.property)).unit.app F).hom.app (Opposite.op V)
    let ρ := (((smallEtaleBaseChange B f).sheafPullback (Type (u + 1))
      (SmallEtale.topology B S.1 S.property)
      (SmallEtale.topology B T.1 T.property)).obj F).obj.map a.op
    ρ (η t)

/-- **Stacks 03Q1.** Pullback of an étale sheaf commutes naturally with taking stalks at a
geometric point. -/
@[stacks 03Q1 "pullback_stalk", sga "4½ Arcata 2.3.3" "(f^*F)_x̄ = F_f(x̄)"]
public def smallEtalePullbackStalkIso (B : BigEtaleSite.{u})
    {S T : B.Scheme} (f : T ⟶ S) (x : GeometricPoint T.1) :
    (smallEtaleBaseChange B f).sheafPullback (Type (u + 1))
        (SmallEtale.topology B S.1 S.property)
        (SmallEtale.topology B T.1 T.property) ⋙
      etaleStalkFunctor.{u, u + 1} B T.1 T.property x ≅
    etaleStalkFunctor.{u, u + 1} B S.1 S.property (x.map (B.inclusion.map f)) := by
  let J := SmallEtale.topology B S.1 S.property
  let K := SmallEtale.topology B T.1 T.property
  let u := smallEtaleBaseChange B f
  let p := geometricPointSitePoint B S.1 S.property (x.map (B.inclusion.map f))
  let q := geometricPointSitePoint B T.1 T.property x
  haveI : PreservesLimitsOfShape (Discrete PEmpty.{1}) u :=
    Functor.preservesLimitsOfShape_pempty_of_isTerminal u
      (SmallEtale.finalIsTerminal B S.1 S.property)
      ((SmallEtale.finalIsTerminal B S.1 S.property).isTerminalObj u)
  letI : HasFiniteLimits (SmallEtale B S.1 S.property) :=
    hasFiniteLimits_of_hasTerminal_and_pullbacks
  letI : PreservesFiniteLimits u := preservesFiniteLimits_of_preservesTerminal_and_pullbacks u
  letI : RepresentablyFlat u := flat_of_preservesFiniteLimits u
  let hcover : CoverPreserving J K u := CoverPreserving.of_isContinuous u J K
  let eFiber : geometricPointFiber B S.1 S.property (x.map (B.inclusion.map f)) ≅
      u ⋙ geometricPointFiber B T.1 T.property x :=
    geometricPointFiberBaseChangeIso B f x
  let eElements := CategoryOfElements.equivalenceOfNatIso
    (C := SmallEtale B S.1 S.property)
    (P := geometricPointFiber B S.1 S.property (x.map (B.inclusion.map f)))
    (Q := u ⋙ geometricPointFiber B T.1 T.property x) eFiber
  haveI : InitiallySmall.{u}
      (u ⋙ geometricPointFiber B T.1 T.property x).Elements := by
    have hModel : Functor.Initial (fromInitialModel.{u} p.fiber.Elements) := inferInstance
    have hEquiv : eElements.functor.IsEquivalence := eElements.isEquivalence_functor
    exact ⟨_, inferInstance, fromInitialModel.{u} p.fiber.Elements ⋙ eElements.functor,
      @Functor.initial_comp_equivalence _ _ _ _ _ _
        (fromInitialModel.{u} p.fiber.Elements) eElements.functor hModel hEquiv⟩
  haveI : InitiallySmall.{u} (u ⋙ q.fiber).Elements := by
    change InitiallySmall.{u} (u ⋙ geometricPointFiber B T.1 T.property x).Elements
    infer_instance
  letI : HasColimitsOfShape p.fiber.Elementsᵒᵖ (Type (u + 1)) :=
    hasColimitsOfShape_geometricPointFiber B S.1 S.property (x.map (B.inclusion.map f))
  letI : HasColimitsOfShape
      (u ⋙ geometricPointFiber B T.1 T.property x).Elementsᵒᵖ (Type (u + 1)) :=
    hasColimitsOfShape_of_finallySmall _ _
  let eStalk := CategoryOfElements.sheafColimIsoOfNatIso J eFiber
  let eComap := q.sheafFiberComapIso u hcover (Type (u + 1))
  change (u.sheafPullback (Type (u + 1)) J K ⋙ q.sheafFiber) ≅ p.sheafFiber
  exact eComap.symm ≪≫ eStalk.symm

/-- **Stacks 03Q1.** The comparison sends the germ of a section pulled back to a pointed
étale neighborhood to the germ of the original section. -/
@[stacks 03Q1 "pullback_stalk"]
public theorem smallEtalePullbackStalkIso_germ (B : BigEtaleSite.{u})
    {S T : B.Scheme} (f : T ⟶ S) (x : GeometricPoint T.1)
    (F : Sheaf (SmallEtale.topology B S.1 S.property) (Type (u + 1)))
    (U : (geometricPointFiber B T.1 T.property x).Elements)
    (V : (geometricPointFiber B S.1 S.property
      (x.map (B.inclusion.map f))).Elements)
    (a : U.1 ⟶ (smallEtaleBaseChange B f).obj V.1)
    (ha : U.2.1 ≫ (SmallEtale.toScheme B T.1 T.property).map a ≫
        B.inclusion.map (pullback.fst V.1.obj.hom f) = V.2.1)
    (t : F.obj.obj (Opposite.op V.1)) :
    ((smallEtalePullbackStalkIso B f x).hom.app F)
      ((colimit.ι
        ((CategoryOfElements.π (geometricPointFiber B T.1 T.property x)).op ⋙
          (((smallEtaleBaseChange B f).sheafPullback (Type (u + 1))
            (SmallEtale.topology B S.1 S.property)
            (SmallEtale.topology B T.1 T.property)).obj F).obj)
        (Opposite.op U)) (pullbackSectionAlong B f F V.1 U.1 a t)) =
      (colimit.ι
        ((CategoryOfElements.π (geometricPointFiber B S.1 S.property
          (x.map (B.inclusion.map f)))).op ⋙ F.obj)
        (Opposite.op V)) t := by
  let J := SmallEtale.topology B S.1 S.property
  let K := SmallEtale.topology B T.1 T.property
  let u := smallEtaleBaseChange B f
  let p := geometricPointSitePoint B S.1 S.property (x.map (B.inclusion.map f))
  let q := geometricPointSitePoint B T.1 T.property x
  have : RepresentablyFlat u := representablyFlat_smallEtaleBaseChange B f
  let hcover : CoverPreserving J K u := CoverPreserving.of_isContinuous u J K
  let eFiber : p.fiber ≅ u ⋙ q.fiber := geometricPointFiberBaseChangeIso B f x
  let eElements := CategoryOfElements.equivalenceOfNatIso eFiber
  have : InitiallySmall.{u} (u ⋙ q.fiber).Elements := by
    have hModel : Functor.Initial (fromInitialModel.{u} p.fiber.Elements) := inferInstance
    have hEquiv : eElements.functor.IsEquivalence := eElements.isEquivalence_functor
    exact ⟨_, inferInstance, fromInitialModel.{u} p.fiber.Elements ⋙ eElements.functor,
      @Functor.initial_comp_equivalence _ _ _ _ _ _ _ eElements.functor hModel hEquiv⟩
  have : HasColimitsOfShape p.fiber.Elementsᵒᵖ (Type (u + 1)) :=
    hasColimitsOfShape_geometricPointFiber B S.1 S.property (x.map (B.inclusion.map f))
  have : HasColimitsOfShape (u ⋙ q.fiber).Elementsᵒᵖ (Type (u + 1)) :=
    hasColimitsOfShape_of_finallySmall _ _
  let eComap := q.sheafFiberComapIso u hcover (Type (u + 1))
  let eStalk := CategoryOfElements.sheafColimIsoOfNatIso J eFiber
  show ((eComap.symm ≪≫ eStalk.symm).hom.app F)
      (colimit.ι ((CategoryOfElements.π q.fiber).op ⋙
        ((u.sheafPullback (Type (u + 1)) J K).obj F).obj)
        (Opposite.op U) (pullbackSectionAlong B f F V.1 U.1 a t)) =
    colimit.ι ((CategoryOfElements.π p.fiber).op ⋙ F.obj) (Opposite.op V) t
  have hpoint : q.fiber.map a U.2 = eFiber.hom.app V.1 V.2 := by
    apply (geometricPointFiberBaseChangeEquiv B f x V.1).symm.injective
    show (geometricPointFiberBaseChangeEquiv B f x V.1).symm (q.fiber.map a U.2) =
      (geometricPointFiberBaseChangeEquiv B f x V.1).symm
        (geometricPointFiberBaseChangeEquiv B f x V.1 V.2)
    rw [Equiv.symm_apply_apply]
    apply Subtype.ext
    show (U.2.1 ≫ (SmallEtale.toScheme B T.1 T.property).map a) ≫
      eqToHom (smallEtaleBaseChange_toScheme_obj_eq B f V.1) ≫
        B.inclusion.map (pullback.fst V.1.obj.hom f) = V.2.1
    simpa using ha
  let G := (u.sheafPullback (Type (u + 1)) J K).obj F
  let η := ((u.sheafAdjunctionContinuous (Type (u + 1)) J K).unit.app F).hom.app
    (Opposite.op V.1)
  have hstalk := CategoryOfElements.ι_sheafColimIsoOfNatIso_hom J eFiber F V
  have hcomap := Point.toSheafFiber_sheafFiberComapIso_hom q u hcover F V.1
    (eFiber.hom.app V.1 V.2)
  have hw := q.toPresheafFiber_w a U.2 G.obj
  rw [hpoint] at hw
  let E := eStalk ≪≫ eComap
  have h : η ≫ G.obj.map a.op ≫ q.toPresheafFiber U.1 U.2 G.obj =
      p.toPresheafFiber V.1 V.2 F.obj ≫ E.hom.app F :=
    (congrArg (fun k => η ≫ k) hw).trans
      (hcomap.symm.trans
        (((congrArg (fun k => k ≫ eComap.hom.app F) hstalk).symm).trans
          (Category.assoc _ _ _)))
  exact congrArg (fun k => k t) ((Iso.comp_inv_eq (E.app F)).2 h)

/-! ### Filtered colimits of modules -/

/-- The forgetful functor of `Λ`-modules preserves the size-`u` filtered colimits over which the
stalks of a presheaf on the small étale site are formed. -/
public instance preservesFilteredColimitsOfSize_forget_moduleCat (Λ : Type (u + 1)) [CommRing Λ] :
    PreservesFilteredColimitsOfSize.{u, u} (forget (ModuleCat.{u + 1} Λ)) :=
  preservesFilteredColimitsOfSize_of_univLE.{u + 1, u + 1, u, u} (forget (ModuleCat.{u + 1} Λ))

/-- The forgetful functor of `Λ`-modules preserves filtered colimits of every size at the
coefficient universe `max (u + 1) r`, for a ring `Λ` in a universe `r` of its own.

The standard instance ties the module universe to the ring universe, so the preservation is
routed through abelian groups: `ModuleCat.forget₂PreservesColimitsOfSize` leaves the two
universes independent, and the forgetful functor of abelian groups preserves filtered colimits
unconditionally. This is not an instance, instance synthesis being unable to solve the
coefficient universe `max (u + 1) ?r` against a given one. -/
public theorem preservesFilteredColimits_forget_moduleCatMax (Λ : Type r) [CommRing Λ] :
    PreservesFilteredColimits (forget (ModuleCat.{max (u + 1) r} Λ)) :=
  let : PreservesColimitsOfSize.{max (u + 1) r, max (u + 1) r}
      (forget₂ (ModuleCat.{max (u + 1) r} Λ) AddCommGrpCat.{max (u + 1) r}) :=
    ModuleCat.forget₂PreservesColimitsOfSize.{max (u + 1) r, r,
      max (u + 1) r, max (u + 1) r} Λ
  comp_preservesFilteredColimits
    (forget₂ (ModuleCat.{max (u + 1) r} Λ) AddCommGrpCat.{max (u + 1) r})
    (forget AddCommGrpCat.{max (u + 1) r})

/-- The forgetful functor of `Λ`-modules preserves the size-`u` filtered colimits over which the
stalks of a presheaf on the small étale site are formed, at the coefficient universe
`max (u + 1) r` for a ring `Λ` in a universe `r` of its own. This is
`AlgebraicGeometry.preservesFilteredColimitsOfSize_forget_moduleCat` with the ring universe
freed. -/
public theorem preservesFilteredColimitsOfSize_forget_moduleCatMax (Λ : Type r) [CommRing Λ] :
    PreservesFilteredColimitsOfSize.{u, u} (forget (ModuleCat.{max (u + 1) r} Λ)) :=
  let := preservesFilteredColimits_forget_moduleCatMax.{u, r} Λ
  preservesFilteredColimitsOfSize_of_univLE.{max (u + 1) r, max (u + 1) r, u, u}
    (forget (ModuleCat.{max (u + 1) r} Λ))

end AlgebraicGeometry

end
