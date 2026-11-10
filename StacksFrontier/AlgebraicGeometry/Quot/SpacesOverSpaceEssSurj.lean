module

public import StacksFrontier.AlgebraicGeometry.Quot.SpacesOverSpaceGlue
public import StacksFrontier.AlgebraicGeometry.Spaces.Immersions
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentableByAlgebraicSpaces
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothAtlas
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothLocalityCriterion

/-!
# Essential surjectivity of base change along the points of an algebraic space

Let `T` be an algebraic space over the base scheme `S` of a big fppf site, and let `P` be a
property of morphisms of algebraic spaces which is stable under base change and local on the target
for the fpqc topology. Every functor `G` over the site from the category `𝒮_T` of points of `T` to
the families with property `P` (with cartesian squares as morphisms) is isomorphic to the
base-change functor of an algebraic space over `T` with property `P`: namely of the glued presheaf
`AlgebraicGeometry.SpacesOverSpace.glue`.

The glued presheaf is an algebraic space because its base change along every scheme-valued point of
`T` is one of the families of `G` (Stacks 02YS), and its projection to `T` has the property `P`
because its base change along a scheme atlas of `T` does, and `P` is local on the target for the
smooth topology, which is coarser than the fpqc one.

## Main results

* `AlgebraicGeometry.SpacesOverSpace.isAlgebraicSpace_glue`: the glued presheaf is an algebraic
  space.
* `AlgebraicGeometry.SpacesOverSpace.prop_glueSpaceMap`: its projection to `T` has the property
  `P`.
* `AlgebraicGeometry.SpacesOverSpace.baseChangeGlueIso`: its base-change functor is isomorphic to
  `G`.
* `AlgebraicGeometry.SpacesOverSpace.baseChangeFunctor_essSurj`: the base-change functor is
  essentially surjective.

## References

* [Stacks Project, Tag 0E93](https://stacks.math.columbia.edu/tag/0E93)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.SpacesOverSpace

universe u

attribute [local implicit_reducible] Stack.fibredCategory BasedCategory.ofFunctor
  AlgebraicSpaces.fiberProduct schemeSpace Functor.toPseudofunctor'
  pseudofunctorOfIsLocallyDiscrete typeToGrpd Grpd.forgetToCat MorphismProperty

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {P : MorphismProperty (AlgebraicSpaces B S hS)} {T : AlgebraicSpaces B S hS}

set_option synthInstance.maxHeartbeats 400000 in
-- instance search for limits of presheaves on the big fppf site needs more heartbeats
/-- Pullbacks of presheaves on the big fppf site (instance search times out without this
shortcut). -/
private instance hasPullbacks_presheaf_spacesOverSpaceEssSurj :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) := inferInstance

private instance (priority := high) hasPullback_presheaf_spacesOverSpaceEssSurj
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

/-- The morphism of algebraic spaces induced by an equality of schemes is an isomorphism. -/
theorem isIso_schemeSpaceMap_eqToHom {U V : BigFppfOver B S hS} (h : U = V) :
    IsIso (schemeSpaceMap (eqToHom h)) := by
  subst h
  rw [show schemeSpaceMap (eqToHom (rfl : U = U)) = 𝟙 _ from
    ObjectProperty.hom_ext _ (yoneda.map_id U)]
  infer_instance

/-- Transport of a morphism along equalities of its source and target, in the shape it takes for
the bases of the cartesian squares of a functor over the site. -/
theorem comp_eqToHom_eq_eqToHom_comp {C : Type*} [Category* C] {X Y X₁ Y₁ : C} (f : X ⟶ Y)
    (e₁ : Y = Y₁) (e₂ : X = X₁) (d : X₁ = X) (c : Y = Y₁) :
    f ≫ eqToHom e₁ = eqToHom e₂ ≫ eqToHom d ≫ f ≫ eqToHom c := by
  subst e₁ e₂
  simp

variable (G : pointsCategory B S hS T ⥤ᵇ BasedCategory.ofFunctor (cartesianProjection B S hS P))

/-- The point of `T` named by a morphism from a representable presheaf names that morphism. -/
theorem pointMap_pt_yonedaEquiv {U : BigFppfOver B S hS} (ξ : yoneda.obj U ⟶ T.obj) :
    (pointMap (pt U (yonedaEquiv ξ))).hom = ξ :=
  yonedaEquiv.symm_apply_apply ξ

/-- The cartesian square of `AlgebraicGeometry.SpacesOverSpace.isPullback_famToGlue`, along an
arbitrary morphism from a representable presheaf to `T`. -/
theorem isPullback_famToGlue_yoneda {U : BigFppfOver B S hS} (ξ : yoneda.obj U ⟶ T.obj) :
    IsPullback (famHom G (pt U (yonedaEquiv ξ))) (famToGlue G (pt U (yonedaEquiv ξ))) ξ
      (glueToBase G) := by
  have h := isPullback_famToGlue G (pt U (yonedaEquiv ξ))
  rwa [pointMap_pt_yonedaEquiv] at h

/-- The glued presheaf is an algebraic space: its projection to `T` is representable by algebraic
spaces, its base changes being the families of `G` (Stacks 02YS). -/
theorem isAlgebraicSpace_glue : IsAlgebraicSpace B S hS (glue G) :=
  isAlgebraicSpace_of_isRepresentableByAlgebraicSpaces B S hS (glueToBase G)
    (fun U ξ => (fam G (pt U (yonedaEquiv ξ))).left.property.of_iso
      (isPullback_famToGlue_yoneda G ξ).isoPullback)
    T.property

/-- The glued algebraic space. -/
abbrev glueSpace : AlgebraicSpaces B S hS :=
  ⟨glue G, isAlgebraicSpace_glue G⟩

/-- The projection of the glued algebraic space to `T`. -/
abbrev glueSpaceMap : glueSpace G ⟶ T :=
  ObjectProperty.homMk (glueToBase G)

/-- The structure morphism of the family at a point, to the base of the point, has `P`. -/
theorem prop_famHom [P.RespectsIso] (a : (pointsCategory B S hS T).obj) :
    P (ObjectProperty.homMk (famHom G a) : (fam G a).left ⟶ schemeSpace a.base) := by
  have := isIso_schemeSpaceMap_eqToHom (fam_right G a)
  exact (P.cancel_right_of_respectsIso (ObjectProperty.homMk (fam G a).hom)
    (schemeSpaceMap (eqToHom (fam_right G a)))).mpr (G.obj a).obj.property

/-- **The projection of the glued space has the property `P`.** Its base change along a scheme
atlas of `T` is one of the families of `G`, and `P` is local on the target. -/
theorem prop_glueSpaceMap [P.IsLocalAtTarget (Space.Topology.precoverage.{u, 0} .fpqc B S hS)] :
    P (glueSpaceMap G) := by
  have : P.IsLocalAtTarget (Space.Topology.precoverage.{u, 0} .smooth B S hS) :=
    MorphismProperty.IsLocalAtTarget.of_le (Space.smooth_precoverage_le_fpqc B S hS)
  obtain ⟨U, ξ, hsurj, hetale⟩ := T.property.exists_atlas
  rw [Space.prop_iff_pullbackSnd_of_atlas_covering.{u, 0} B S hS .smooth P (glueSpaceMap G)
    (Space.smooth_isCovering_atlas B S hS T.property hsurj hetale)]
  have sq : IsPullback
      (ObjectProperty.homMk (famToGlue G (pt U (yonedaEquiv ξ))) :
        (fam G (pt U (yonedaEquiv ξ))).left ⟶ glueSpace G)
      (ObjectProperty.homMk (famHom G (pt U (yonedaEquiv ξ))) :
        (fam G (pt U (yonedaEquiv ξ))).left ⟶ schemeSpace U)
      (glueSpaceMap G) (ObjectProperty.homMk ξ) :=
    IsPullback.of_map (ObjectProperty.ι _)
      (ObjectProperty.hom_ext _ (isPullback_famToGlue_yoneda G ξ).w.symm)
      (isPullback_famToGlue_yoneda G ξ).flip
  refine (P.cancel_left_of_respectsIso sq.isoPullback.hom _).mp ?_
  rw [sq.isoPullback_hom_snd]
  exact prop_famHom G _

/-- The map from the family at a point to the glued presheaf is compatible with the cartesian
squares of `G`. -/
theorem famMap_comp_famToGlue {a' a : (pointsCategory B S hS T).obj} (u : a' ⟶ a) :
    famMap G u ≫ famToGlue G a = famToGlue G a' := by
  ext ⟨W⟩ y'
  change famToGlueApp G a ((famMap G u).app (op W) y') = famToGlueApp G a' y'
  have hg : (famHom G a).app (op W) ((famMap G u).app (op W) y') =
      (famHom G a').app (op W) y' ≫ u.base :=
    famHom_famMap_apply G u y'
  have h : T.obj.map ((famHom G a).app (op W) ((famMap G u).app (op W) y')).op a.fiber.as =
      T.obj.map (𝟙 W).op (T.obj.map ((famHom G a').app (op W) y').op a'.fiber.as) := by
    rw [hg, op_id, Functor.map_id_apply, fiber_as_eq u, ← Functor.map_comp_apply,
      op_comp]
  set p := toPoint ((famHom G a').app (op W) y') rfl
  refine glue_ext G (ptHom (𝟙 W) h) rfl _ _ ?_
  apply ext_famMap G p
  · rw [← famMap_comp_apply G (ptHom (𝟙 W) h) p,
      famMap_famToGlueApp G a' y' (famToGlueApp G a' y') rfl p rfl]
    apply ext_famMap G u
    · rw [← famMap_comp_apply G (ptHom (𝟙 W) h ≫ p) u]
      exact famMap_famToGlueApp G a _ _ rfl _ (by
        change (𝟙 _ ≫ _) ≫ u.base = _
        rw [Category.id_comp, hg])
    · refine (famHom_famMap_apply G _ _).trans ?_
      rw [famHom_lift]
      change 𝟙 _ ≫ (𝟙 _ ≫ (famHom G a').app (op W) y') = (famHom G a').app (op W) y'
      rw [Category.id_comp, Category.id_comp]
  · refine (famHom_famMap_apply G _ _).trans ?_
    rw [famHom_lift]
    exact (Category.id_comp _).trans (famHom_lift G p y' (𝟙 W) (Category.id_comp _).symm).symm

/-- The normalized structure morphism of a family, followed back to the base of the family, is
its structure morphism. -/
theorem famHom_comp_eqToHom (a : (pointsCategory B S hS T).obj) :
    famHom G a ≫ yoneda.map (eqToHom (fam_right G a).symm) = (fam G a).hom := by
  simp only [famHom, Category.assoc, ← CategoryTheory.Functor.map_comp, eqToHom_trans,
    eqToHom_refl, CategoryTheory.Functor.map_id, Category.comp_id]

section EssSurj

variable [P.IsStableUnderBaseChange]
  [P.IsLocalAtTarget (Space.Topology.precoverage.{u, 0} .fpqc B S hS)]

/-- The glued algebraic space, as an algebraic space over `T` with the property `P`. -/
abbrev glueObject : SpacesOver B S hS P T :=
  ⟨⟨Over.mk (glueSpaceMap G)⟩, prop_glueSpaceMap G⟩

set_option synthInstance.maxHeartbeats 400000 in
-- `HasPullback` instance synthesis for `isoPullback` of algebraic spaces over the big fppf site
/-- The total space of the base change of the glued space along a point of `T` is the total space
of the family of `G` at the point. -/
def glueLeftIso (a : (pointsCategory B S hS T).obj) :
    (baseChangeComma (glueObject G).1.of a).left ≅ (fam G a).left :=
  ObjectProperty.isoMk _ (isPullback_famToGlue G a).isoPullback.symm

/-- The base change of the glued space along a point of `T` is the family of `G` at the point, as
families over the base of the point. -/
def glueCommaIso (a : (pointsCategory B S hS T).obj) :
    baseChangeComma (glueObject G).1.of a ≅ fam G a :=
  Comma.isoMk (glueLeftIso G a) (eqToIso (fam_right G a).symm) (by
      change (isPullback_famToGlue G a).isoPullback.inv ≫ (fam G a).hom =
        pullback.fst (pointMap a).hom (glueToBase G) ≫ yoneda.map (eqToHom (fam_right G a).symm)
      rw [← famHom_comp_eqToHom G a, ← Category.assoc, IsPullback.isoPullback_inv_fst])

/-- The base change of the glued space along a point of `T` is the family of `G` at the point. -/
def baseChangeGlueIsoApp (a : (pointsCategory B S hS T).obj) :
    baseChangeObj (glueObject G) a ≅ G.obj a :=
  WideSubcategory.isoMk (X := baseChangeObj (glueObject G) a) (Y := G.obj a)
    (ObjectProperty.isoMk _ (X := (baseChangeObj (glueObject G) a).obj) (Y := (G.obj a).obj)
      (glueCommaIso G a))
    (Functor.IsStronglyCartesian.of_isIso (p := spacesProjection B S hS)
      (f := (spacesProjection B S hS).map (glueCommaIso G a).hom) (glueCommaIso G a).hom)
    (Functor.IsStronglyCartesian.of_isIso (p := spacesProjection B S hS)
      (f := (spacesProjection B S hS).map (glueCommaIso G a).inv) (glueCommaIso G a).inv)

/-- **The base-change functor of the glued space is `G`.** -/
def baseChangeGlueIso : (baseChangeFunctor (P := P) (T := T)).obj (glueObject G) ≅ G :=
  BasedNatIso.mkNatIso (NatIso.ofComponents (baseChangeGlueIsoApp G) (by
    intro a' a u
    apply WideSubcategory.hom_ext
    apply ObjectProperty.hom_ext
    apply Comma.hom_ext
    · apply ObjectProperty.hom_ext
      change (baseChangeCommaMap (glueObject G).1.of u).left.hom ≫
          (isPullback_famToGlue G a).isoPullback.inv =
        (isPullback_famToGlue G a').isoPullback.inv ≫ famMap G u
      apply (isPullback_famToGlue G a).hom_ext
      · rw [Category.assoc, IsPullback.isoPullback_inv_fst]
        refine (baseChangeCommaMap_left_fst _ u).trans ?_
        rw [Category.assoc, (isPullback_famMap G u).w, ← Category.assoc,
          IsPullback.isoPullback_inv_fst]
        rfl
      · rw [Category.assoc, IsPullback.isoPullback_inv_snd]
        refine (baseChangeCommaMap_left_snd _ u).trans ?_
        rw [Category.assoc, famMap_comp_famToGlue, IsPullback.isoPullback_inv_snd]
        rfl
    · change u.base ≫ eqToHom (fam_right G a).symm =
        eqToHom (fam_right G a').symm ≫ (G.map u).hom.hom.right
      have h1 : (pointsCategory B S hS T).p.IsHomLift u.base u :=
        IsHomLift.map (pointsCategory B S hS T).p u
      have h2 : (cartesianProjection B S hS P).IsHomLift u.base (G.map u) :=
        BasedFunctor.preserves_isHomLift G u.base u
      have h := IsHomLift.fac' (cartesianProjection B S hS P) u.base (G.map u)
      change (G.map u).hom.hom.right = _ at h
      rw [h]
      exact comp_eqToHom_eq_eqToHom_comp u.base _ _ _ _))
    (fun a => IsHomLift.of_fac' (p := cartesianProjection B S hS P) (𝟙 a.base) _ rfl
      (fam_right G a) (by
        change eqToHom (fam_right G a).symm =
          eqToHom (rfl : a.base = a.base) ≫ 𝟙 a.base ≫ eqToHom (fam_right G a).symm
        simp))

/-- **Essential surjectivity in Stacks 0E93.** Every functor over the site from the category of
points of `T` to the families with property `P` is isomorphic to the base-change functor of an
algebraic space over `T` with property `P`. -/
instance baseChangeFunctor_essSurj : (baseChangeFunctor (B := B) (S := S) (hS := hS) (P := P)
    (T := T)).EssSurj :=
  ⟨fun G => ⟨glueObject G, ⟨baseChangeGlueIso G⟩⟩⟩

end EssSurj

end AlgebraicGeometry.SpacesOverSpace

end
