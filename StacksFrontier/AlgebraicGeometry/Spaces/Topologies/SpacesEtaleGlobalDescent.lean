module

public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.SmallEtaleSheafDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.SpacesEtaleRestrictionId
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.SpacesEtaleSliceInverseImage
public import StacksFrontier.CategoryTheory.Sites.Descent.RestrictedBaseDescentData

/-!
# Descent for spaces-étale sheaves over the category of all algebraic spaces

Let `X` be an algebraic space over a scheme `S` contained in a big fppf site `B`. Effective
descent for étale sheaves along a covering of `X` was proved in
`StacksFrontier.AlgebraicGeometry.Spaces.Topologies.SmallEtaleSheafDescent` for the pseudofunctor
`AlgebraicGeometry.Space.SpacesEtale.spacesEtaleSheafSystem` on the spaces-étale site of `X`,
whose fibre over an object `U` of that site is the category of sheaves on the spaces-étale site
of the algebraic space underlying `U`. The same fibres are those of
`AlgebraicGeometry.Space.spacesEtalePseudofunctor`, the pseudofunctor of spaces-étale inverse
images on the category of *all* algebraic spaces over `S`, restricted along the forgetful
functor from the spaces-étale site of `X`. This file identifies the two pseudofunctors and
deduces effective descent for the unrestricted one, where the base of a descent problem may be
an arbitrary morphism of algebraic spaces rather than an étale one.

## Main definitions

* `AlgebraicGeometry.Space.SpacesEtale.spacesEtaleSheafSystemStrongTrans`: the strong
  transformation with identity components from
  `AlgebraicGeometry.Space.SpacesEtale.spacesEtaleSheafSystem` to the restriction of
  `AlgebraicGeometry.Space.spacesEtalePseudofunctor` along
  `AlgebraicGeometry.Space.SpacesEtale.toSpaces`.

## Main results

* `isEquivalence_toDescentData_spacesEtalePseudofunctor_of_jointlySurjective`, in the namespace
  `AlgebraicGeometry.Space.SpacesEtale`: effective descent for spaces-étale sheaves along a
  family of algebraic spaces étale over `X` whose structure morphisms are jointly surjective on
  points;
* `isEquivalence_toDescentData_spacesEtalePseudofunctor_of_isEtaleCovering`, in the same
  namespace: **Stacks 0GFS** for that pseudofunctor.

## Implementation notes

The strong transformation has identity components, because the two pseudofunctors have the same
fibres on the nose; its strong naturality constraint is
`AlgebraicGeometry.Space.SpacesEtale.sheafOverEquivSmall_overMapPullback_iso`, which says that
the slice pullback is the spaces-étale inverse image. What has to be checked is that this
identification is compatible with the identity and the composition constraints of the two
pseudofunctors, and that is what the bulk of this file does.

The two checks have the same shape. Each reduces, by cancelling the comparison equivalence of
`AlgebraicGeometry.Space.SpacesEtale.sheafOverEquivSmall` against its own unit and counit, to
an identity between the comparison constraints themselves; there the identification of
Stacks 03LQ cancels against the one hidden inside the strong naturality constraint, by its
compatibility with identities and with composition, and what is left is an identity between
restriction functors along functors of sites, which holds because the underlying functors of
sites agree on the nose.

The cancellation of the equivalence is isolated in the three statements
`CategoryTheory.glueCounit`, `CategoryTheory.unitCounit` and `CategoryTheory.glueComp`, which
are facts about an arbitrary equivalence of categories.

Stacks 0GFS is registered twice: on
`isEquivalence_toDescentData_smallEtaleSheafSystem_of_isEtaleCovering`, for descent data in the
small étale sheaf categories of the members of the covering, and here, for the pseudofunctor of
spaces-étale inverse images over all algebraic spaces. The second form is what an étale-local
criterion for descent needs, since there the morphism whose descent problem is studied is
arbitrary.

## References

* [Stacks Project, Tag 0GFS](https://stacks.math.columbia.edu/tag/0GFS)
* [Stacks Project, Tag 03LQ](https://stacks.math.columbia.edu/tag/03LQ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Bicategory Opposite

universe t u

namespace CategoryTheory

/-! ### Cancelling an equivalence against its unit and counit -/

/-- Transposing a morphism through the counit of an equivalence: postcomposing the image of a
morphism followed by the counit with a morphism of the target is the image of the composite
read through the inverse. -/
theorem glueCounit {Dw : Type*} [Category Dw] {Cw : Type*} [Category Cw]
    (E : Dw ≌ Cw) {A : Dw} {P M : Cw} (α : A ⟶ E.inverse.obj P) (ν : P ⟶ M)
    (μ : A ⟶ E.inverse.obj M) (h : α ≫ E.inverse.map ν = μ) :
    (E.functor.map α ≫ E.counitIso.hom.app P) ≫ ν =
      E.functor.map μ ≫ E.counitIso.hom.app M := by
  subst h
  rw [CategoryTheory.Functor.map_comp, Category.assoc, Category.assoc]
  exact congrArg (E.functor.map α ≫ ·) (E.counitIso.hom.naturality ν).symm

/-- The unit of an equivalence cancels the transpose through its counit. -/
theorem unitCounit {Dv : Type*} [Category Dv] {Cv : Type*} [Category Cv]
    (E : Dv ≌ Cv) {A : Dv} {Z : Cv} (h : A ⟶ E.inverse.obj Z) :
    E.unitIso.hom.app A ≫ E.inverse.map (E.functor.map h ≫ E.counitIso.hom.app Z) = h := by
  simp

/-- Two equivalences cancel against a natural isomorphism conjugated by them: the composite
appearing in the composition coherence of a transported pseudofunctor is the image of a single
composite of the untransported data. -/
theorem glueComp {Dv : Type*} [Category Dv] {Cv : Type*} [Category Cv]
    {Dw : Type*} [Category Dw] {Cw : Type*} [Category Cw]
    (Ev : Dv ≌ Cv) (Ew : Dw ≌ Cw) (pg : Dv ⥤ Dw) (Iq : Cv ⥤ Cw)
    (Psi : Ev.inverse ⋙ pg ≅ Iq ⋙ Ew.inverse)
    {A : Dv} {Z : Cv} (h : A ⟶ Ev.inverse.obj Z) {P : Dw} (l : P ⟶ pg.obj A) :
    Ew.functor.map l ≫ Ew.functor.map (pg.map (Ev.unitIso.hom.app A)) ≫
        (Ew.functor.map (Psi.hom.app (Ev.functor.obj A)) ≫
            Ew.counitIso.hom.app (Iq.obj (Ev.functor.obj A))) ≫
          Iq.map (Ev.functor.map h ≫ Ev.counitIso.hom.app Z) =
      Ew.functor.map (l ≫ pg.map h ≫ Psi.hom.app Z) ≫ Ew.counitIso.hom.app (Iq.obj Z) := by
  have hnat : pg.map (Ev.inverse.map (Ev.functor.map h ≫ Ev.counitIso.hom.app Z)) ≫
        Psi.hom.app Z =
      Psi.hom.app (Ev.functor.obj A) ≫
        Ew.inverse.map (Iq.map (Ev.functor.map h ≫ Ev.counitIso.hom.app Z)) :=
    Psi.hom.naturality _
  have key : l ≫ pg.map (Ev.unitIso.hom.app A) ≫ (Psi.hom.app (Ev.functor.obj A) ≫
        Ew.inverse.map (Iq.map (Ev.functor.map h ≫ Ev.counitIso.hom.app Z))) =
      l ≫ pg.map h ≫ Psi.hom.app Z := by
    refine congrArg (l ≫ ·) ?_
    rw [← hnat, ← Category.assoc, ← Functor.map_comp, unitCounit]
  rw [glueCounit Ew (Psi.hom.app (Ev.functor.obj A))
      (Iq.map (Ev.functor.map h ≫ Ev.counitIso.hom.app Z)) _ rfl, ← key]
  simp only [CategoryTheory.Functor.map_comp, Category.assoc, Functor.id_obj]

end CategoryTheory

namespace AlgebraicGeometry.Space.SpacesEtale

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X : AlgebraicSpaces B S hS}

/-! ### The two halves of the strong naturality constraint -/

/-- The first half of
`AlgebraicGeometry.Space.SpacesEtale.overMapPullback_spacesEtaleInverseImageIso`: the slice
pullback along `φ`, read through the comparison equivalence at the target, is restriction along
`AlgebraicGeometry.Space.SpacesEtale.slicePostcomp`. -/
noncomputable def sliceOverMapIso {V U : SpacesEtale B S hS X} (φ : V ⟶ U) :
    (sheafOverEquivSmall B S hS U (Type (u + 1))).inverse ⋙
        (topology B S hS X).overMapPullback (Type (u + 1)) φ ≅
      (slicePostcomp B S hS φ).sheafPushforwardContinuous (Type (u + 1))
        ((topology B S hS X).over V) (topology B S hS U.obj.left) :=
  @Functor.sheafPushforwardContinuousComp' _ _ _ _ _ _ _ _ _
    (Iso.refl _ : Over.map φ ⋙ sliceToSmall B S hS U ≅ slicePostcomp B S hS φ)
    (Type (u + 1)) _
    ((topology B S hS X).over V) ((topology B S hS X).over U)
    (topology B S hS U.obj.left) _ _ (isContinuous_slicePostcomp B S hS φ)

/-- The second half of
`AlgebraicGeometry.Space.SpacesEtale.overMapPullback_spacesEtaleInverseImageIso`: restriction
along postcomposition, read through the comparison equivalence at the source, is restriction
along `AlgebraicGeometry.Space.SpacesEtale.slicePostcomp`. -/
noncomputable def slicePostcompIso {V U : SpacesEtale B S hS X} (φ : V ⟶ U) :
    (spacesEtalePostcomp B S hS ((toSpaces B S hS X).map φ)
          (isEtale_toSpaces_map B S hS X φ)).sheafPushforwardContinuous (Type (u + 1))
        (topology B S hS V.obj.left) (topology B S hS U.obj.left) ⋙
        (sheafOverEquivSmall B S hS V (Type (u + 1))).inverse ≅
      (slicePostcomp B S hS φ).sheafPushforwardContinuous (Type (u + 1))
        ((topology B S hS X).over V) (topology B S hS U.obj.left) :=
  @Functor.sheafPushforwardContinuousComp' _ _ _ _ _ _ _ _ _
    (Iso.refl _ : sliceToSmall B S hS V ⋙ spacesEtalePostcomp B S hS
        ((toSpaces B S hS X).map φ) (isEtale_toSpaces_map B S hS X φ) ≅
      slicePostcomp B S hS φ)
    (Type (u + 1)) _
    ((topology B S hS X).over V) (topology B S hS V.obj.left)
    (topology B S hS U.obj.left) _
    (isContinuous_spacesEtalePostcomp_toSpaces_map B S hS φ)
    (isContinuous_slicePostcomp B S hS φ)

/-- The comparison of the slice pullback with restriction along postcomposition, with the
identification of Stacks 03LQ removed: the composite of the two halves above. -/
noncomputable abbrev sliceMate {V U : SpacesEtale B S hS X} (φ : V ⟶ U) :
    (sheafOverEquivSmall B S hS U (Type (u + 1))).inverse ⋙
        (topology B S hS X).overMapPullback (Type (u + 1)) φ ⟶
      (spacesEtalePostcomp B S hS ((toSpaces B S hS X).map φ)
          (isEtale_toSpaces_map B S hS X φ)).sheafPushforwardContinuous (Type (u + 1))
        (topology B S hS V.obj.left) (topology B S hS U.obj.left) ⋙
        (sheafOverEquivSmall B S hS V (Type (u + 1))).inverse :=
  (sliceOverMapIso B S hS φ).hom ≫ (slicePostcompIso B S hS φ).inv

/-- The comparison of the slice pullback with the spaces-étale inverse image is the composite
of its two halves and the identification of Stacks 03LQ. -/
theorem overMapPullback_spacesEtaleInverseImageIso_eq {V U : SpacesEtale B S hS X}
    (φ : V ⟶ U) :
    overMapPullback_spacesEtaleInverseImageIso B S hS φ =
      sliceOverMapIso B S hS φ ≪≫
        (Functor.isoWhiskerRight (spacesToposMorphism_inverseImageIso B S hS
            ((toSpaces B S hS X).map φ) (isEtale_toSpaces_map B S hS X φ))
            (sheafOverEquivSmall B S hS V (Type (u + 1))).inverse ≪≫
          slicePostcompIso B S hS φ).symm := rfl

/-- The same decomposition, evaluated at a sheaf. -/
theorem overMapPullback_spacesEtaleInverseImageIso_hom_app {V U : SpacesEtale B S hS X}
    (φ : V ⟶ U) (M : Sheaf (topology B S hS U.obj.left) (Type (u + 1))) :
    (overMapPullback_spacesEtaleInverseImageIso B S hS φ).hom.app M =
      (sliceMate B S hS φ).app M ≫
        (sheafOverEquivSmall B S hS V (Type (u + 1))).inverse.map
          ((spacesToposMorphism_inverseImageIso B S hS ((toSpaces B S hS X).map φ)
            (isEtale_toSpaces_map B S hS X φ)).inv.app M) := rfl

private lemma auxIdComp {C₀ : Type*} [Category C₀] {A Bb : C₀} (e : A ⟶ A) (f : A ⟶ Bb)
    (he : e = 𝟙 A) : e ≫ f = f := by subst he; simp

private lemma auxCompId {C₀ : Type*} [Category C₀] {A Bb : C₀} (f : A ⟶ Bb) (v w : Bb ⟶ Bb)
    (hv : v = 𝟙 Bb) (hw : w = 𝟙 Bb) : f ≫ v ≫ w = f := by subst hv; subst hw; simp

/-- `AlgebraicGeometry.Space.SpacesEtale.sliceMate` is the identity on sections: the two
functors of sites it compares are equal on the nose. -/
theorem sliceMate_app_hom_app {V U : SpacesEtale B S hS X} (φ : V ⟶ U)
    (M : Sheaf (topology B S hS U.obj.left) (Type (u + 1))) (T : (Over V)ᵒᵖ) :
    ((sliceMate B S hS φ).app M).hom.app T = 𝟙 _ := by
  change M.obj.map (𝟙 _) ≫ M.obj.map (𝟙 _) = 𝟙 _
  simp only [CategoryTheory.Functor.map_id, Category.comp_id]

/-! ### The identity coherence -/

/-- **The comparison with restriction along postcomposition is compatible with identities.**
At the identity of an object of the spaces-étale site of `X`, the composite of
`AlgebraicGeometry.Space.SpacesEtale.sliceMate` with the strict identity comparison of the
restriction functor is the identity comparison of the slice pullback. -/
theorem sliceMate_id (U : SpacesEtale B S hS X) :
    (sliceOverMapIso B S hS (𝟙 U)).hom ≫ (slicePostcompIso B S hS (𝟙 U)).inv ≫
        Functor.whiskerRight
          (spacesEtalePostcompSheafId B S hS (isEtale_toSpaces_map B S hS X (𝟙 U))).hom
          (sheafOverEquivSmall B S hS U (Type (u + 1))).inverse =
      Functor.whiskerLeft (sheafOverEquivSmall B S hS U (Type (u + 1))).inverse
        ((topology B S hS X).overMapPullbackId (Type (u + 1)) U).hom := by
  refine NatTrans.ext (funext fun M ↦ Sheaf.hom_ext (NatTrans.ext (funext fun T ↦ ?_)))
  have h1 : ((sliceMate B S hS (𝟙 U)).app M).hom.app T = 𝟙 _ :=
    sliceMate_app_hom_app B S hS _ M T
  have h3 : (((sheafOverEquivSmall B S hS U (Type (u + 1))).inverse.map
        ((spacesEtalePostcompSheafId B S hS
          (isEtale_toSpaces_map B S hS X (𝟙 U))).hom.app M)).hom.app T) =
      M.obj.map ((spacesEtalePostcompId B S hS
        (isEtale_toSpaces_map B S hS X (𝟙 U))).inv.app
          ((sliceToSmall B S hS U).obj (unop T))).op ≫ 𝟙 _ := rfl
  have hsite : (spacesEtalePostcompId B S hS
        (isEtale_toSpaces_map B S hS X (𝟙 U))).inv.app
          ((sliceToSmall B S hS U).obj (unop T))
      = (sliceToSmall B S hS U).map ((Over.mapId U).inv.app (unop T)) :=
    ObjectProperty.hom_ext _ (Over.OverMorphism.ext rfl)
  rw [← Category.assoc]
  simp only [NatTrans.comp_app, ObjectProperty.FullSubcategory.comp_hom,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, h3,
    Category.comp_id, GrothendieckTopology.overMapPullbackId_hom_app_hom_app]
  exact ((congrArg (· ≫ _) h1).trans (Category.id_comp _)).trans
    (congrArg (fun z ↦ M.obj.map (Quiver.Hom.op z)) hsite)

/-- **The strong naturality constraint is compatible with identities.** -/
theorem overMapPullback_spacesEtaleInverseImageIso_id (U : SpacesEtale B S hS X) :
    (overMapPullback_spacesEtaleInverseImageIso B S hS (𝟙 U)).hom ≫
        Functor.whiskerRight
          (spacesEtaleInverseImage_id B S hS ((toSpaces B S hS X).obj U)).hom
          (sheafOverEquivSmall B S hS U (Type (u + 1))).inverse =
      Functor.whiskerLeft (sheafOverEquivSmall B S hS U (Type (u + 1))).inverse
        ((topology B S hS X).overMapPullbackId (Type (u + 1)) U).hom := by
  have hid : (spacesEtaleInverseImage_id B S hS ((toSpaces B S hS X).obj U)).hom =
      (spacesToposMorphism_inverseImageIso B S hS ((toSpaces B S hS X).map (𝟙 U))
          (isEtale_toSpaces_map B S hS X (𝟙 U))).hom ≫
        (spacesEtalePostcompSheafId B S hS
          (isEtale_toSpaces_map B S hS X (𝟙 U))).hom :=
    spacesToposMorphism_inverseImageIso_id B S hS _
  rw [hid, overMapPullback_spacesEtaleInverseImageIso_eq B S hS (𝟙 U)]
  have hw : Functor.whiskerRight
        ((spacesToposMorphism_inverseImageIso B S hS ((toSpaces B S hS X).map (𝟙 U))
            (isEtale_toSpaces_map B S hS X (𝟙 U))).hom ≫
          (spacesEtalePostcompSheafId B S hS
            (isEtale_toSpaces_map B S hS X (𝟙 U))).hom)
        (sheafOverEquivSmall B S hS U (Type (u + 1))).inverse =
      (Functor.isoWhiskerRight (spacesToposMorphism_inverseImageIso B S hS
          ((toSpaces B S hS X).map (𝟙 U)) (isEtale_toSpaces_map B S hS X (𝟙 U)))
          (sheafOverEquivSmall B S hS U (Type (u + 1))).inverse).hom ≫
        Functor.whiskerRight (spacesEtalePostcompSheafId B S hS
          (isEtale_toSpaces_map B S hS X (𝟙 U))).hom
          (sheafOverEquivSmall B S hS U (Type (u + 1))).inverse :=
    Functor.whiskerRight_comp _ _ _
  rw [hw]
  simp only [Iso.trans_hom, Iso.symm_hom, Iso.trans_inv, Category.assoc,
    Iso.inv_hom_id_assoc]
  exact sliceMate_id B S hS U

/-! ### The composition coherence -/

/-- **The comparison with restriction along postcomposition is compatible with composition.**
This is the composition coherence with the identification of Stacks 03LQ removed; it holds
because the underlying functors of sites agree on the nose. -/
theorem sliceMate_comp {W V U : SpacesEtale B S hS X} (φ : V ⟶ U) (ψ : W ⟶ V)
    (M : Sheaf (topology B S hS U.obj.left) (Type (u + 1))) :
    (sliceMate B S hS (ψ ≫ φ)).app M ≫
        (sheafOverEquivSmall B S hS W (Type (u + 1))).inverse.map
          ((spacesEtalePostcompSheafComp B S hS ((toSpaces B S hS X).map ψ)
            (isEtale_toSpaces_map B S hS X ψ) ((toSpaces B S hS X).map φ)
            (isEtale_toSpaces_map B S hS X φ)).inv.app M) =
      ((topology B S hS X).overMapPullbackComp (Type (u + 1)) ψ φ).inv.app
          ((sheafOverEquivSmall B S hS U (Type (u + 1))).inverse.obj M) ≫
        ((topology B S hS X).overMapPullback (Type (u + 1)) ψ).map
            ((sliceMate B S hS φ).app M) ≫
          (sliceMate B S hS ψ).app
            ((spacesEtalePostcomp B S hS ((toSpaces B S hS X).map φ)
                (isEtale_toSpaces_map B S hS X φ)).sheafPushforwardContinuous (Type (u + 1))
              (topology B S hS V.obj.left) (topology B S hS U.obj.left) |>.obj M) := by
  refine Sheaf.hom_ext (NatTrans.ext (funext fun T ↦ ?_))
  simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app]
  have hL1 : ((sliceMate B S hS (ψ ≫ φ)).app M).hom.app T = 𝟙 _ :=
    sliceMate_app_hom_app B S hS _ M T
  have hL2 : (((sheafOverEquivSmall B S hS W (Type (u + 1))).inverse.map
        ((spacesEtalePostcompSheafComp B S hS ((toSpaces B S hS X).map ψ)
          (isEtale_toSpaces_map B S hS X ψ) ((toSpaces B S hS X).map φ)
          (isEtale_toSpaces_map B S hS X φ)).inv.app M)).hom.app T) =
      M.obj.map ((spacesEtalePostcompComp B S hS ((toSpaces B S hS X).map ψ)
        (isEtale_toSpaces_map B S hS X ψ) ((toSpaces B S hS X).map φ)
        (isEtale_toSpaces_map B S hS X φ)).hom.app
          ((sliceToSmall B S hS W).obj (unop T))).op := rfl
  have hR1 : ((((topology B S hS X).overMapPullbackComp (Type (u + 1)) ψ φ).inv.app
        ((sheafOverEquivSmall B S hS U (Type (u + 1))).inverse.obj M)).hom.app T) =
      M.obj.map ((sliceToSmall B S hS U).map
        ((Over.mapComp ψ φ).inv.app (unop T))).op := rfl
  have hR2 : ((((topology B S hS X).overMapPullback (Type (u + 1)) ψ).map
        ((sliceMate B S hS φ).app M)).hom.app T) = 𝟙 _ :=
    sliceMate_app_hom_app B S hS φ M _
  have hR3 : ((sliceMate B S hS ψ).app
        ((spacesEtalePostcomp B S hS ((toSpaces B S hS X).map φ)
            (isEtale_toSpaces_map B S hS X φ)).sheafPushforwardContinuous (Type (u + 1))
          (topology B S hS V.obj.left) (topology B S hS U.obj.left) |>.obj M)).hom.app T
      = 𝟙 _ := sliceMate_app_hom_app B S hS ψ _ T
  have hsite : (spacesEtalePostcompComp B S hS ((toSpaces B S hS X).map ψ)
        (isEtale_toSpaces_map B S hS X ψ) ((toSpaces B S hS X).map φ)
        (isEtale_toSpaces_map B S hS X φ)).hom.app
          ((sliceToSmall B S hS W).obj (unop T))
      = (sliceToSmall B S hS U).map ((Over.mapComp ψ φ).inv.app (unop T)) :=
    ObjectProperty.hom_ext _ (Over.OverMorphism.ext rfl)
  rw [hL2, hR1]
  exact (auxIdComp _ _ hL1).trans
    ((congrArg (fun z ↦ M.obj.map (Quiver.Hom.op z)) hsite).trans
      (auxCompId _ _ _ hR2 hR3).symm)

/-- **Stacks 03LQ is compatible with composition**, in the form needed for the composition
coherence: the identification of the inverse image with restriction along postcomposition,
inverted and composed with the composition comparison of the inverse images, is the
composition comparison of the restriction functors followed by the two inverted
identifications. -/
theorem spacesToposMorphism_inverseImageIso_inv_comp {W V U : SpacesEtale B S hS X}
    (φ : V ⟶ U) (ψ : W ⟶ V)
    (M : Sheaf (topology B S hS U.obj.left) (Type (u + 1))) :
    (spacesToposMorphism_inverseImageIso B S hS ((toSpaces B S hS X).map (ψ ≫ φ))
          (isEtale_toSpaces_map B S hS X (ψ ≫ φ))).inv.app M ≫
        (spacesEtaleInverseImage_comp B S hS ((toSpaces B S hS X).map ψ)
          ((toSpaces B S hS X).map φ)).hom.app M =
      (spacesEtalePostcompSheafComp B S hS ((toSpaces B S hS X).map ψ)
            (isEtale_toSpaces_map B S hS X ψ) ((toSpaces B S hS X).map φ)
            (isEtale_toSpaces_map B S hS X φ)).inv.app M ≫
        (spacesToposMorphism_inverseImageIso B S hS ((toSpaces B S hS X).map ψ)
            (isEtale_toSpaces_map B S hS X ψ)).inv.app
          ((spacesEtalePostcomp B S hS ((toSpaces B S hS X).map φ)
              (isEtale_toSpaces_map B S hS X φ)).sheafPushforwardContinuous (Type (u + 1))
            (topology B S hS V.obj.left) (topology B S hS U.obj.left) |>.obj M) ≫
          (spacesEtaleInverseImage B S hS ((toSpaces B S hS X).map ψ)).map
            ((spacesToposMorphism_inverseImageIso B S hS ((toSpaces B S hS X).map φ)
              (isEtale_toSpaces_map B S hS X φ)).inv.app M) := by
  have hSB : (spacesEtaleInverseImage_comp B S hS ((toSpaces B S hS X).map ψ)
          ((toSpaces B S hS X).map φ)).hom.app M ≫
        ((spacesEtaleInverseImage B S hS ((toSpaces B S hS X).map ψ)).map
            ((spacesToposMorphism_inverseImageIso B S hS ((toSpaces B S hS X).map φ)
              (isEtale_toSpaces_map B S hS X φ)).hom.app M) ≫
          (spacesToposMorphism_inverseImageIso B S hS ((toSpaces B S hS X).map ψ)
              (isEtale_toSpaces_map B S hS X ψ)).hom.app
            ((spacesEtalePostcomp B S hS ((toSpaces B S hS X).map φ)
                (isEtale_toSpaces_map B S hS X φ)).sheafPushforwardContinuous (Type (u + 1))
              (topology B S hS V.obj.left) (topology B S hS U.obj.left) |>.obj M)) =
      (spacesToposMorphism_inverseImageIso B S hS ((toSpaces B S hS X).map (ψ ≫ φ))
            (isEtale_toSpaces_map B S hS X (ψ ≫ φ))).hom.app M ≫
        (spacesEtalePostcompSheafComp B S hS ((toSpaces B S hS X).map ψ)
          (isEtale_toSpaces_map B S hS X ψ) ((toSpaces B S hS X).map φ)
          (isEtale_toSpaces_map B S hS X φ)).inv.app M :=
    NatTrans.congr_app (spacesToposMorphism_inverseImageIso_comp B S hS
      ((toSpaces B S hS X).map ψ) (isEtale_toSpaces_map B S hS X ψ)
      ((toSpaces B S hS X).map φ) (isEtale_toSpaces_map B S hS X φ)) M
  have hcancel : (spacesEtaleInverseImage_comp B S hS ((toSpaces B S hS X).map ψ)
        ((toSpaces B S hS X).map φ)).hom.app M =
      ((spacesToposMorphism_inverseImageIso B S hS ((toSpaces B S hS X).map (ψ ≫ φ))
            (isEtale_toSpaces_map B S hS X (ψ ≫ φ))).hom.app M ≫
        (spacesEtalePostcompSheafComp B S hS ((toSpaces B S hS X).map ψ)
          (isEtale_toSpaces_map B S hS X ψ) ((toSpaces B S hS X).map φ)
          (isEtale_toSpaces_map B S hS X φ)).inv.app M) ≫
        (spacesToposMorphism_inverseImageIso B S hS ((toSpaces B S hS X).map ψ)
            (isEtale_toSpaces_map B S hS X ψ)).inv.app
          ((spacesEtalePostcomp B S hS ((toSpaces B S hS X).map φ)
              (isEtale_toSpaces_map B S hS X φ)).sheafPushforwardContinuous (Type (u + 1))
            (topology B S hS V.obj.left) (topology B S hS U.obj.left) |>.obj M) ≫
          (spacesEtaleInverseImage B S hS ((toSpaces B S hS X).map ψ)).map
            ((spacesToposMorphism_inverseImageIso B S hS ((toSpaces B S hS X).map φ)
              (isEtale_toSpaces_map B S hS X φ)).inv.app M) := by
    rw [← hSB]
    simp
  rw [hcancel]
  simp only [Category.assoc]
  rw [Iso.inv_hom_id_app_assoc]

/-- **The strong naturality constraint is compatible with composition.** -/
theorem overMapPullback_spacesEtaleInverseImageIso_comp {W V U : SpacesEtale B S hS X}
    (φ : V ⟶ U) (ψ : W ⟶ V)
    (M : Sheaf (topology B S hS U.obj.left) (Type (u + 1))) :
    (overMapPullback_spacesEtaleInverseImageIso B S hS (ψ ≫ φ)).hom.app M ≫
        (sheafOverEquivSmall B S hS W (Type (u + 1))).inverse.map
          ((spacesEtaleInverseImage_comp B S hS ((toSpaces B S hS X).map ψ)
            ((toSpaces B S hS X).map φ)).hom.app M) =
      ((topology B S hS X).overMapPullbackComp (Type (u + 1)) ψ φ).inv.app
          ((sheafOverEquivSmall B S hS U (Type (u + 1))).inverse.obj M) ≫
        ((topology B S hS X).overMapPullback (Type (u + 1)) ψ).map
            ((overMapPullback_spacesEtaleInverseImageIso B S hS φ).hom.app M) ≫
          (overMapPullback_spacesEtaleInverseImageIso B S hS ψ).hom.app
            ((spacesEtaleInverseImage B S hS ((toSpaces B S hS X).map φ)).obj M) := by
  have hnat1 : ((topology B S hS X).overMapPullback (Type (u + 1)) ψ).map
        ((sheafOverEquivSmall B S hS V (Type (u + 1))).inverse.map
          ((spacesToposMorphism_inverseImageIso B S hS ((toSpaces B S hS X).map φ)
            (isEtale_toSpaces_map B S hS X φ)).inv.app M)) ≫
        (sliceMate B S hS ψ).app
          ((spacesEtaleInverseImage B S hS ((toSpaces B S hS X).map φ)).obj M) =
      (sliceMate B S hS ψ).app
          ((spacesEtalePostcomp B S hS ((toSpaces B S hS X).map φ)
              (isEtale_toSpaces_map B S hS X φ)).sheafPushforwardContinuous (Type (u + 1))
            (topology B S hS V.obj.left) (topology B S hS U.obj.left) |>.obj M) ≫
        (sheafOverEquivSmall B S hS W (Type (u + 1))).inverse.map
          (((spacesEtalePostcomp B S hS ((toSpaces B S hS X).map ψ)
              (isEtale_toSpaces_map B S hS X ψ)).sheafPushforwardContinuous (Type (u + 1))
            (topology B S hS W.obj.left) (topology B S hS V.obj.left)).map
              ((spacesToposMorphism_inverseImageIso B S hS ((toSpaces B S hS X).map φ)
                (isEtale_toSpaces_map B S hS X φ)).inv.app M)) :=
    (sliceMate B S hS ψ).naturality _
  have hnat2 : ((spacesEtalePostcomp B S hS ((toSpaces B S hS X).map ψ)
          (isEtale_toSpaces_map B S hS X ψ)).sheafPushforwardContinuous (Type (u + 1))
        (topology B S hS W.obj.left) (topology B S hS V.obj.left)).map
          ((spacesToposMorphism_inverseImageIso B S hS ((toSpaces B S hS X).map φ)
            (isEtale_toSpaces_map B S hS X φ)).inv.app M) ≫
        (spacesToposMorphism_inverseImageIso B S hS ((toSpaces B S hS X).map ψ)
            (isEtale_toSpaces_map B S hS X ψ)).inv.app
          ((spacesEtaleInverseImage B S hS ((toSpaces B S hS X).map φ)).obj M) =
      (spacesToposMorphism_inverseImageIso B S hS ((toSpaces B S hS X).map ψ)
            (isEtale_toSpaces_map B S hS X ψ)).inv.app
          ((spacesEtalePostcomp B S hS ((toSpaces B S hS X).map φ)
              (isEtale_toSpaces_map B S hS X φ)).sheafPushforwardContinuous (Type (u + 1))
            (topology B S hS V.obj.left) (topology B S hS U.obj.left) |>.obj M) ≫
        (spacesEtaleInverseImage B S hS ((toSpaces B S hS X).map ψ)).map
          ((spacesToposMorphism_inverseImageIso B S hS ((toSpaces B S hS X).map φ)
            (isEtale_toSpaces_map B S hS X φ)).inv.app M) :=
    (spacesToposMorphism_inverseImageIso B S hS ((toSpaces B S hS X).map ψ)
      (isEtale_toSpaces_map B S hS X ψ)).inv.naturality _
  rw [overMapPullback_spacesEtaleInverseImageIso_hom_app B S hS (ψ ≫ φ) M,
    overMapPullback_spacesEtaleInverseImageIso_hom_app B S hS φ M,
    overMapPullback_spacesEtaleInverseImageIso_hom_app B S hS ψ
      ((spacesEtaleInverseImage B S hS ((toSpaces B S hS X).map φ)).obj M),
    Category.assoc, ← Functor.map_comp,
    spacesToposMorphism_inverseImageIso_inv_comp B S hS φ ψ M]
  simp only [CategoryTheory.Functor.map_comp, Category.assoc]
  slice_rhs 3 4 => rw [hnat1]
  slice_rhs 4 5 => rw [← Functor.map_comp, hnat2, CategoryTheory.Functor.map_comp]
  slice_rhs 1 3 => rw [← sliceMate_comp B S hS φ ψ M]
  simp only [Category.assoc]

/-! ### The strong transformation and effective descent -/

/-- **The slice-based sheaf system is the restriction of the pseudofunctor of spaces-étale
inverse images.** The two pseudofunctors on the spaces-étale site of `X` have the same fibres,
and the strong naturality constraint identifying their inverse images is the comparison of the
slice pullback with the spaces-étale inverse image. -/
noncomputable def spacesEtaleSheafSystemStrongTrans :
    Pseudofunctor.StrongTrans (spacesEtaleSheafSystem B S hS (X := X))
      ((spacesEtalePseudofunctor B S hS).restrict (toSpaces B S hS X)) where
  app a := 𝟙 _
  naturality {a b} φ := Cat.Hom.isoMk (sheafOverEquivSmall_overMapPullback_iso B S hS φ.as.unop)
  naturality_naturality := by
    intro a b f g η
    obtain rfl := LocallyDiscrete.eq_of_hom η
    obtain rfl : η = 𝟙 _ := Subsingleton.elim _ _
    rw [Pseudofunctor.map₂_eq_eqToHom (spacesEtaleSheafSystem B S hS (X := X)),
      Pseudofunctor.map₂_eq_eqToHom ((spacesEtalePseudofunctor B S hS).restrict
        (toSpaces B S hS X))]
    exact (Category.id_comp _).trans (Category.comp_id _).symm
  naturality_id := by
    intro a
    ext M
    exact glueCounit (sheafOverEquivSmall B S hS (unop a.as) (Type (u + 1)))
      ((overMapPullback_spacesEtaleInverseImageIso B S hS (𝟙 (unop a.as))).hom.app M)
      ((spacesEtaleInverseImage_id B S hS ((toSpaces B S hS X).obj (unop a.as))).hom.app M)
      (((topology B S hS X).overMapPullbackId (Type (u + 1)) (unop a.as)).hom.app
        ((sheafOverEquivSmall B S hS (unop a.as) (Type (u + 1))).inverse.obj M))
      (NatTrans.congr_app
        (overMapPullback_spacesEtaleInverseImageIso_id B S hS (unop a.as)) M)
  naturality_comp := by
    intro a b c f g
    ext M
    exact (glueCounit (sheafOverEquivSmall B S hS (unop c.as) (Type (u + 1)))
        ((overMapPullback_spacesEtaleInverseImageIso B S hS
          (g.as.unop ≫ f.as.unop)).hom.app M)
        ((spacesEtaleInverseImage_comp B S hS ((toSpaces B S hS X).map g.as.unop)
          ((toSpaces B S hS X).map f.as.unop)).hom.app M) _
        (overMapPullback_spacesEtaleInverseImageIso_comp B S hS f.as.unop g.as.unop M)).trans
      (glueComp (sheafOverEquivSmall B S hS (unop b.as) (Type (u + 1)))
        (sheafOverEquivSmall B S hS (unop c.as) (Type (u + 1)))
        ((topology B S hS X).overMapPullback (Type (u + 1)) g.as.unop)
        (spacesEtaleInverseImage B S hS ((toSpaces B S hS X).map g.as.unop))
        (overMapPullback_spacesEtaleInverseImageIso B S hS g.as.unop)
        ((overMapPullback_spacesEtaleInverseImageIso B S hS f.as.unop).hom.app M)
        (((topology B S hS X).overMapPullbackComp (Type (u + 1)) g.as.unop
          f.as.unop).inv.app
            ((sheafOverEquivSmall B S hS (unop a.as) (Type (u + 1))).inverse.obj M))).symm

/-- The components of
`AlgebraicGeometry.Space.SpacesEtale.spacesEtaleSheafSystemStrongTrans` are equivalences,
being identities. -/
instance isEquivalence_spacesEtaleSheafSystemStrongTrans_app
    (a : LocallyDiscrete (SpacesEtale B S hS X)ᵒᵖ) :
    ((spacesEtaleSheafSystemStrongTrans B S hS (X := X)).app a).toFunctor.IsEquivalence :=
  Functor.isEquivalence_refl

/-- **Effective descent for spaces-étale sheaves over the category of all algebraic spaces.**
For a family of objects of the spaces-étale site of `X` whose structure morphisms are jointly
surjective on points, sheaves of sets on the spaces-étale site of `X` are equivalent to descent
data for the family in the pseudofunctor of spaces-étale inverse images. -/
theorem isEquivalence_toDescentData_spacesEtalePseudofunctor_of_jointlySurjective
    {I : Type t} (U : I → SpacesEtale B S hS X)
    (hsurj : (⋃ i, Set.range (pointsMap B S hS ((U i).obj.left).1 ((U i).obj.hom).hom))
      = Set.univ) :
    ((spacesEtalePseudofunctor B S hS).toDescentData
      (fun i => (U i).obj.hom)).IsEquivalence := by
  have h0 : (((topology B S hS X).pseudofunctorOver (Type (u + 1))).toDescentData
      (fun i => toFinal B S hS (U i))).IsEquivalence :=
    GrothendieckTopology.isEquivalence_toDescentData_pseudofunctorOver
      (topology B S hS X) (Type (u + 1)) _
      (ofArrows_toFinal_mem_topology_of_jointlySurjective B S hS U hsurj)
  have h1 : ((spacesEtaleSheafSystem B S hS (X := X)).toDescentData
      (fun i => toFinal B S hS (U i))).IsEquivalence :=
    (Pseudofunctor.isEquivalence_toDescentData_transport_iff _ _ _ _).mp h0
  have h2 : (((spacesEtalePseudofunctor B S hS).restrict
      (toSpaces B S hS X)).toDescentData
        (fun i => toFinal B S hS (U i))).IsEquivalence :=
    ((spacesEtaleSheafSystemStrongTrans B S hS (X := X)).isEquivalence_toDescentData_iff
      (fun i => toFinal B S hS (U i))
      (isEquivalence_spacesEtaleSheafSystemStrongTrans_app B S hS)).mp h1
  exact (Pseudofunctor.isEquivalence_toDescentData_restrict_iff_of_preserves
    (spacesEtalePseudofunctor B S hS) (toSpaces B S hS X)
    (fun i => toFinal B S hS (U i))).mp h2

/-- **Stacks 0GFS for the pseudofunctor of spaces-étale inverse images.** Let `X` be an
algebraic space over a scheme `S` and let `{g i : Y i ⟶ X}` be an étale covering of algebraic
spaces. Then sheaves of sets on the spaces-étale site of `X` are equivalent, via the functor
taking a sheaf to its canonical descent datum, to descent data for that covering: a
spaces-étale sheaf on each `Y i`, together with transition isomorphisms over the overlaps
satisfying the cocycle condition. -/
@[stacks 0GFS "for the pseudofunctor of spaces-étale inverse images"]
theorem isEquivalence_toDescentData_spacesEtalePseudofunctor_of_isEtaleCovering
    {I : Type t} (Y : I → AlgebraicSpaces B S hS) (g : ∀ i, Y i ⟶ X)
    (hg : IsEtaleCovering B S hS (fun i => (Y i).1) (fun i => (g i).hom)) :
    ((spacesEtalePseudofunctor B S hS).toDescentData g).IsEquivalence :=
  isEquivalence_toDescentData_spacesEtalePseudofunctor_of_jointlySurjective B S hS
    (fun i => etaleObject B S hS (g i) (hg.etale i)) hg.jointly_surjective

end AlgebraicGeometry.Space.SpacesEtale

end
