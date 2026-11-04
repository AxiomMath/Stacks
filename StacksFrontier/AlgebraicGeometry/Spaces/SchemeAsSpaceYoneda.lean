module

public import StacksFrontier.AlgebraicGeometry.Spaces.SchemeAsSpace

/-!
# The algebraic space of a scheme, through the Yoneda embedding

`AlgebraicGeometry.schemeSpace U` is the algebraic space of a scheme `U` over `S`, its presheaf of
points (Stacks 025Z), and `AlgebraicGeometry.schemeSpaceMap` the morphism induced by a morphism of
schemes. This file is the interface through which consumers use them without unfolding their
definitions: it identifies the underlying presheaf with the representable one by a natural
isomorphism, and describes the morphisms out of and into the algebraic space of a scheme and its
points.

## Main definitions

* `AlgebraicGeometry.schemeSpaceFunctorCompιIso`: the corestricted Yoneda embedding followed by
  the inclusion into presheaves is the Yoneda embedding; its components are
  `AlgebraicGeometry.schemeSpaceIso U : (schemeSpace U).obj ≅ yoneda.obj U`.
* `AlgebraicGeometry.fromSchemeSpace` and `AlgebraicGeometry.fromSchemeSpaceEquiv`: morphisms out
  of the algebraic space of `U` are morphisms of presheaves out of `yoneda.obj U`.
* `AlgebraicGeometry.toSchemeSpace` and `AlgebraicGeometry.toSchemeSpaceEquiv`: the same for
  morphisms into it.
* `AlgebraicGeometry.schemeSpacePointEquiv`: morphisms out of the algebraic space of `U` are the
  `U`-valued points.
* `AlgebraicGeometry.schemeSpaceMap_inj` and `AlgebraicGeometry.schemeSpaceMap_surjective`:
  schemes form a full subcategory of algebraic spaces (the instances `Full` and `Faithful`; the
  bundled `Functor.FullyFaithful` is `AlgebraicGeometry.schemeSpaceFunctorFullyFaithful`, in
  `StacksFrontier/AlgebraicGeometry/Spaces/Topologies/BigPhEtaleSchemeSlices.lean`).

## Main results

* `AlgebraicGeometry.isPullback_schemeSpaceMap_iff`: a square of schemes is cartesian exactly when
  the square of their algebraic spaces is.

## Implementation notes

`AlgebraicGeometry.schemeSpaceFunctorCompιIso` is sealed by `irreducible_def`, so a consumer
of this interface cannot rely on the isomorphism being the identity; the definitions of
`AlgebraicGeometry.schemeSpace` and `AlgebraicGeometry.schemeSpaceMap` are not sealed, since some
consumers still use their definitional form. `AlgebraicGeometry.schemeSpace_eq`, `AlgebraicGeometry.schemeSpace_obj`
and `AlgebraicGeometry.schemeSpaceMap_hom` record the definitional description, and
`AlgebraicGeometry.schemeSpaceIso_hom_eq_eqToHom` relates the isomorphism to it.

The functoriality lemmas `schemeSpaceMap_comp` and `schemeSpaceMap_injective` live in
`StacksFrontier/AlgebraicGeometry/Quot/CurveFamilies.lean` and
`StacksFrontier/Deformation/Examples/Geometric/CurvesDeformationComparison.lean`; here
`AlgebraicGeometry.schemeSpaceFunctor_map` reduces them to `CategoryTheory.Functor.map_comp` and
`AlgebraicGeometry.schemeSpaceMap_inj`.

## References

* [Stacks Project, Tag 025Z](https://stacks.math.columbia.edu/tag/025Z)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- The corestricted Yoneda embedding takes a scheme to its algebraic space. -/
@[simp]
theorem schemeSpaceFunctor_obj (U : BigFppfOver B S hS) :
    (schemeSpaceFunctor B S hS).obj U = schemeSpace U :=
  rfl

/-- The corestricted Yoneda embedding takes a morphism of schemes to the induced morphism of
algebraic spaces. -/
@[simp]
theorem schemeSpaceFunctor_map {U V : BigFppfOver B S hS} (g : U ⟶ V) :
    (schemeSpaceFunctor B S hS).map g = schemeSpaceMap g :=
  rfl

/-- The algebraic space of a scheme is the anonymous object built from its representable
presheaf. Prefer `AlgebraicGeometry.schemeSpaceIso`. -/
theorem schemeSpace_eq (U : BigFppfOver B S hS) :
    schemeSpace U = ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩ :=
  rfl

/-- The algebraic space of `AlgebraicGeometry.Space.representedAlgebraicSpace` is
`AlgebraicGeometry.schemeSpace`. -/
theorem representedAlgebraicSpace_eq_schemeSpace (U : BigFppfOver B S hS) :
    Space.representedAlgebraicSpace B S hS U = schemeSpace U :=
  rfl

/-- The algebraic space of `AlgebraicGeometry.yonedaSpace` is `AlgebraicGeometry.schemeSpace`. -/
theorem yonedaSpace_eq_schemeSpace (U : BigFppfOver B S hS) :
    yonedaSpace B S hS U = schemeSpace U :=
  rfl

variable (B S hS) in
/-- The corestricted Yoneda embedding followed by the inclusion of algebraic spaces into
presheaves is the Yoneda embedding. Sealed: consumers use it through
`AlgebraicGeometry.schemeSpaceIso` and the naturality lemmas below. -/
irreducible_def schemeSpaceFunctorCompιIso :
    schemeSpaceFunctor B S hS ⋙ ObjectProperty.ι _ ≅ yoneda :=
  NatIso.ofComponents (fun U => Iso.refl (yoneda.obj U)) (fun _ => rfl)

/-- The presheaf underlying the algebraic space of a scheme is the representable presheaf. -/
def schemeSpaceIso (U : BigFppfOver B S hS) : (schemeSpace U).obj ≅ yoneda.obj U :=
  (schemeSpaceFunctorCompιIso B S hS).app U

/-- The component at `U` of `AlgebraicGeometry.schemeSpaceFunctorCompιIso` is
`AlgebraicGeometry.schemeSpaceIso U`. -/
@[simp]
theorem schemeSpaceFunctorCompιIso_hom_app (U : BigFppfOver B S hS) :
    (schemeSpaceFunctorCompιIso B S hS).hom.app U = (schemeSpaceIso U).hom :=
  rfl

/-- The inverse of `AlgebraicGeometry.schemeSpaceFunctorCompιIso` at `U` is the inverse of
`AlgebraicGeometry.schemeSpaceIso U`. -/
@[simp]
theorem schemeSpaceFunctorCompιIso_inv_app (U : BigFppfOver B S hS) :
    (schemeSpaceFunctorCompιIso B S hS).inv.app U = (schemeSpaceIso U).inv :=
  rfl

/-- `AlgebraicGeometry.schemeSpaceIso` is the identification
`AlgebraicGeometry.schemeSpace_obj`. -/
theorem schemeSpaceIso_hom_eq_eqToHom (U : BigFppfOver B S hS) :
    (schemeSpaceIso U).hom = eqToHom (schemeSpace_obj U) := by
  rw [schemeSpaceIso, schemeSpaceFunctorCompιIso_def]
  rfl

/-- The inverse of `AlgebraicGeometry.schemeSpaceIso` is the inverse of the identification
`AlgebraicGeometry.schemeSpace_obj`. -/
theorem schemeSpaceIso_inv_eq_eqToHom (U : BigFppfOver B S hS) :
    (schemeSpaceIso U).inv = eqToHom (schemeSpace_obj U).symm := by
  rw [← cancel_epi (schemeSpaceIso U).hom, Iso.hom_inv_id, schemeSpaceIso_hom_eq_eqToHom,
    eqToHom_trans, eqToHom_refl]

/-- The algebraic space of a scheme is isomorphic to the anonymous object built from its
representable presheaf. -/
def schemeSpaceIsoMk (U : BigFppfOver B S hS) :
    schemeSpace U ≅ ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩ :=
  ObjectProperty.isoMk _ (schemeSpaceIso U)

/-- The morphism underlying `AlgebraicGeometry.schemeSpaceIsoMk` is that of
`AlgebraicGeometry.schemeSpaceIso`. -/
@[simp]
theorem schemeSpaceIsoMk_hom_hom (U : BigFppfOver B S hS) :
    (schemeSpaceIsoMk U).hom.hom = (schemeSpaceIso U).hom :=
  rfl

/-- The morphism underlying the inverse of `AlgebraicGeometry.schemeSpaceIsoMk` is the inverse of
`AlgebraicGeometry.schemeSpaceIso`. -/
@[simp]
theorem schemeSpaceIsoMk_inv_hom (U : BigFppfOver B S hS) :
    (schemeSpaceIsoMk U).inv.hom = (schemeSpaceIso U).inv :=
  rfl

/-! #### The induced morphism -/

/-- `AlgebraicGeometry.schemeSpaceIso` is natural. -/
@[reassoc (attr := simp)]
theorem schemeSpaceMap_hom_comp_schemeSpaceIso_hom {U V : BigFppfOver B S hS} (g : U ⟶ V) :
    (schemeSpaceMap g).hom ≫ (schemeSpaceIso V).hom = (schemeSpaceIso U).hom ≫ yoneda.map g :=
  (schemeSpaceFunctorCompιIso B S hS).hom.naturality g

/-- `AlgebraicGeometry.schemeSpaceIso` is natural. -/
@[reassoc (attr := simp)]
theorem schemeSpaceIso_inv_comp_schemeSpaceMap_hom {U V : BigFppfOver B S hS} (g : U ⟶ V) :
    (schemeSpaceIso U).inv ≫ (schemeSpaceMap g).hom = yoneda.map g ≫ (schemeSpaceIso V).inv :=
  ((schemeSpaceFunctorCompιIso B S hS).inv.naturality g).symm

/-- The morphism underlying `AlgebraicGeometry.schemeSpaceMap` is the Yoneda image of the
morphism, read through `AlgebraicGeometry.schemeSpaceIso`. -/
theorem schemeSpaceMap_hom_eq {U V : BigFppfOver B S hS} (g : U ⟶ V) :
    (schemeSpaceMap g).hom = (schemeSpaceIso U).hom ≫ yoneda.map g ≫ (schemeSpaceIso V).inv := by
  rw [← schemeSpaceMap_hom_comp_schemeSpaceIso_hom_assoc, Iso.hom_inv_id, Category.comp_id]

/-- The morphism of algebraic spaces induced by a morphism of schemes determines it. -/
@[simp]
theorem schemeSpaceMap_inj {U V : BigFppfOver B S hS} {g g' : U ⟶ V} :
    schemeSpaceMap g = schemeSpaceMap g' ↔ g = g' := by
  refine ⟨fun h => yoneda.map_injective ?_, fun h => h ▸ rfl⟩
  rw [← cancel_mono (schemeSpaceIso V).inv, ← schemeSpaceIso_inv_comp_schemeSpaceMap_hom,
    ← schemeSpaceIso_inv_comp_schemeSpaceMap_hom, h]

/-- Every morphism between the algebraic spaces of two schemes is induced by a morphism of
schemes. -/
theorem schemeSpaceMap_surjective {U V : BigFppfOver B S hS} :
    Function.Surjective (schemeSpaceMap : (U ⟶ V) → (schemeSpace U ⟶ schemeSpace V)) := by
  intro f
  refine ⟨yoneda.preimage ((schemeSpaceIso U).inv ≫ f.hom ≫ (schemeSpaceIso V).hom),
    ObjectProperty.hom_ext _ ?_⟩
  simp [schemeSpaceMap_hom_eq]

/-- Every morphism between the algebraic spaces of two schemes comes from a morphism of schemes. -/
instance : (schemeSpaceFunctor B S hS).Full :=
  ⟨fun f => schemeSpaceMap_surjective f⟩

/-- A morphism of schemes is determined by the induced morphism of algebraic spaces. -/
instance : (schemeSpaceFunctor B S hS).Faithful :=
  ⟨fun h => schemeSpaceMap_inj.mp h⟩

/-- The morphism of algebraic spaces induced by a morphism of schemes is an isomorphism exactly
when the morphism of schemes is. -/
theorem isIso_schemeSpaceMap_iff {U V : BigFppfOver B S hS} (g : U ⟶ V) :
    IsIso (schemeSpaceMap g) ↔ IsIso g :=
  ⟨fun h =>
    have : IsIso ((schemeSpaceFunctor B S hS).map g) := h
    isIso_of_fully_faithful (schemeSpaceFunctor B S hS) g,
    fun _ => inferInstanceAs (IsIso ((schemeSpaceFunctor B S hS).map g))⟩

/-! #### Morphisms out of and into the algebraic space of a scheme -/

/-- A morphism of algebraic spaces out of the algebraic space of a scheme `U`, from a morphism of
presheaves out of the representable presheaf of `U`. -/
def fromSchemeSpace {U : BigFppfOver B S hS} {X : AlgebraicSpaces B S hS}
    (y : yoneda.obj U ⟶ X.obj) : schemeSpace U ⟶ X :=
  ObjectProperty.homMk ((schemeSpaceIso U).hom ≫ y)

/-- The morphism of presheaves underlying `AlgebraicGeometry.fromSchemeSpace y`. -/
@[simp]
theorem fromSchemeSpace_hom {U : BigFppfOver B S hS} {X : AlgebraicSpaces B S hS}
    (y : yoneda.obj U ⟶ X.obj) : (fromSchemeSpace y).hom = (schemeSpaceIso U).hom ≫ y :=
  rfl

/-- Read through `AlgebraicGeometry.schemeSpaceIso`, `AlgebraicGeometry.fromSchemeSpace y` is
`y`. -/
@[reassoc (attr := simp)]
theorem schemeSpaceIso_inv_comp_fromSchemeSpace_hom {U : BigFppfOver B S hS}
    {X : AlgebraicSpaces B S hS} (y : yoneda.obj U ⟶ X.obj) :
    (schemeSpaceIso U).inv ≫ (fromSchemeSpace y).hom = y := by
  simp

variable (U : BigFppfOver B S hS) (X : AlgebraicSpaces B S hS) in
/-- Morphisms of algebraic spaces out of the algebraic space of a scheme `U` are the morphisms of
presheaves out of the representable presheaf of `U`. -/
def fromSchemeSpaceEquiv : (yoneda.obj U ⟶ X.obj) ≃ (schemeSpace U ⟶ X) where
  toFun y := fromSchemeSpace y
  invFun f := (schemeSpaceIso U).inv ≫ f.hom
  left_inv y := by simp
  right_inv f := ObjectProperty.hom_ext _ (by simp)

/-- `AlgebraicGeometry.fromSchemeSpaceEquiv` is `AlgebraicGeometry.fromSchemeSpace`. -/
@[simp]
theorem fromSchemeSpaceEquiv_apply {U : BigFppfOver B S hS} {X : AlgebraicSpaces B S hS}
    (y : yoneda.obj U ⟶ X.obj) : fromSchemeSpaceEquiv U X y = fromSchemeSpace y :=
  rfl

/-- The inverse of `AlgebraicGeometry.fromSchemeSpaceEquiv` reads a morphism through
`AlgebraicGeometry.schemeSpaceIso`. -/
@[simp]
theorem fromSchemeSpaceEquiv_symm_apply {U : BigFppfOver B S hS} {X : AlgebraicSpaces B S hS}
    (f : schemeSpace U ⟶ X) :
    (fromSchemeSpaceEquiv U X).symm f = (schemeSpaceIso U).inv ≫ f.hom :=
  rfl

/-- Every morphism out of the algebraic space of a scheme is `AlgebraicGeometry.fromSchemeSpace` of
its restriction to the representable presheaf. -/
@[simp]
theorem fromSchemeSpace_schemeSpaceIso_inv_comp {U : BigFppfOver B S hS}
    {X : AlgebraicSpaces B S hS} (f : schemeSpace U ⟶ X) :
    fromSchemeSpace ((schemeSpaceIso U).inv ≫ f.hom) = f :=
  (fromSchemeSpaceEquiv U X).right_inv f

/-- `AlgebraicGeometry.fromSchemeSpace` is compatible with composition on the right. -/
@[simp]
theorem fromSchemeSpace_comp {U : BigFppfOver B S hS} {X Y : AlgebraicSpaces B S hS}
    (y : yoneda.obj U ⟶ X.obj) (h : X ⟶ Y) :
    fromSchemeSpace y ≫ h = fromSchemeSpace (y ≫ h.hom) :=
  ObjectProperty.hom_ext _ (by simp)

/-- `AlgebraicGeometry.fromSchemeSpace` is compatible with precomposition by
`AlgebraicGeometry.schemeSpaceMap`. -/
@[simp]
theorem schemeSpaceMap_comp_fromSchemeSpace {U V : BigFppfOver B S hS}
    {X : AlgebraicSpaces B S hS} (g : U ⟶ V) (y : yoneda.obj V ⟶ X.obj) :
    schemeSpaceMap g ≫ fromSchemeSpace y = fromSchemeSpace (yoneda.map g ≫ y) :=
  ObjectProperty.hom_ext _ (by simp [schemeSpaceMap_hom_eq])

/-- A morphism of algebraic spaces into the algebraic space of a scheme `U`, from a morphism of
presheaves into the representable presheaf of `U`. -/
def toSchemeSpace {X : AlgebraicSpaces B S hS} {U : BigFppfOver B S hS}
    (z : X.obj ⟶ yoneda.obj U) : X ⟶ schemeSpace U :=
  ObjectProperty.homMk (z ≫ (schemeSpaceIso U).inv)

/-- The morphism of presheaves underlying `AlgebraicGeometry.toSchemeSpace z`. -/
@[simp]
theorem toSchemeSpace_hom {X : AlgebraicSpaces B S hS} {U : BigFppfOver B S hS}
    (z : X.obj ⟶ yoneda.obj U) : (toSchemeSpace z).hom = z ≫ (schemeSpaceIso U).inv :=
  rfl

/-- Read through `AlgebraicGeometry.schemeSpaceIso`, `AlgebraicGeometry.toSchemeSpace z` is `z`. -/
@[reassoc (attr := simp)]
theorem toSchemeSpace_hom_comp_schemeSpaceIso_hom {X : AlgebraicSpaces B S hS}
    {U : BigFppfOver B S hS} (z : X.obj ⟶ yoneda.obj U) :
    (toSchemeSpace z).hom ≫ (schemeSpaceIso U).hom = z := by
  simp

variable (X : AlgebraicSpaces B S hS) (U : BigFppfOver B S hS) in
/-- Morphisms of algebraic spaces into the algebraic space of a scheme `U` are the morphisms of
presheaves into the representable presheaf of `U`. -/
def toSchemeSpaceEquiv : (X.obj ⟶ yoneda.obj U) ≃ (X ⟶ schemeSpace U) where
  toFun z := toSchemeSpace z
  invFun f := f.hom ≫ (schemeSpaceIso U).hom
  left_inv z := by simp
  right_inv f := ObjectProperty.hom_ext _ (by simp)

/-- `AlgebraicGeometry.toSchemeSpaceEquiv` is `AlgebraicGeometry.toSchemeSpace`. -/
@[simp]
theorem toSchemeSpaceEquiv_apply {X : AlgebraicSpaces B S hS} {U : BigFppfOver B S hS}
    (z : X.obj ⟶ yoneda.obj U) : toSchemeSpaceEquiv X U z = toSchemeSpace z :=
  rfl

/-- The inverse of `AlgebraicGeometry.toSchemeSpaceEquiv` reads a morphism through
`AlgebraicGeometry.schemeSpaceIso`. -/
@[simp]
theorem toSchemeSpaceEquiv_symm_apply {X : AlgebraicSpaces B S hS} {U : BigFppfOver B S hS}
    (f : X ⟶ schemeSpace U) :
    (toSchemeSpaceEquiv X U).symm f = f.hom ≫ (schemeSpaceIso U).hom :=
  rfl

/-- Every morphism into the algebraic space of a scheme is `AlgebraicGeometry.toSchemeSpace` of its
composite with `AlgebraicGeometry.schemeSpaceIso`. -/
@[simp]
theorem toSchemeSpace_hom_comp_schemeSpaceIso {X : AlgebraicSpaces B S hS}
    {U : BigFppfOver B S hS} (f : X ⟶ schemeSpace U) :
    toSchemeSpace (f.hom ≫ (schemeSpaceIso U).hom) = f :=
  (toSchemeSpaceEquiv X U).right_inv f

/-- `AlgebraicGeometry.toSchemeSpace` is compatible with composition on the left. -/
@[simp]
theorem comp_toSchemeSpace {X Y : AlgebraicSpaces B S hS} {U : BigFppfOver B S hS}
    (h : Y ⟶ X) (z : X.obj ⟶ yoneda.obj U) :
    h ≫ toSchemeSpace z = toSchemeSpace (h.hom ≫ z) :=
  ObjectProperty.hom_ext _ (by simp)

/-- `AlgebraicGeometry.toSchemeSpace` is compatible with postcomposition by
`AlgebraicGeometry.schemeSpaceMap`. -/
@[simp]
theorem toSchemeSpace_comp_schemeSpaceMap {X : AlgebraicSpaces B S hS}
    {U V : BigFppfOver B S hS} (z : X.obj ⟶ yoneda.obj U) (g : U ⟶ V) :
    toSchemeSpace z ≫ schemeSpaceMap g = toSchemeSpace (z ≫ yoneda.map g) :=
  ObjectProperty.hom_ext _ (by simp [schemeSpaceMap_hom_eq])

/-- Two morphisms out of the algebraic space of a scheme agree once they agree on the
representable presheaf. -/
theorem schemeSpace_yoneda_ext {U : BigFppfOver B S hS} {X : AlgebraicSpaces B S hS}
    {f f' : schemeSpace U ⟶ X}
    (h : (schemeSpaceIso U).inv ≫ f.hom = (schemeSpaceIso U).inv ≫ f'.hom) : f = f' :=
  (fromSchemeSpaceEquiv U X).symm.injective h

/-- Two morphisms into the algebraic space of a scheme agree once they agree as morphisms into
the representable presheaf. -/
theorem hom_ext_schemeSpace {X : AlgebraicSpaces B S hS} {U : BigFppfOver B S hS}
    {f f' : X ⟶ schemeSpace U}
    (h : f.hom ≫ (schemeSpaceIso U).hom = f'.hom ≫ (schemeSpaceIso U).hom) : f = f' :=
  (toSchemeSpaceEquiv X U).symm.injective h

/-! #### Points -/

variable (U : BigFppfOver B S hS) (X : AlgebraicSpaces B S hS) in
/-- **The Yoneda lemma for the algebraic space of a scheme**: a morphism of algebraic spaces out of
the algebraic space of `U` is a `U`-valued point. -/
def schemeSpacePointEquiv : (schemeSpace U ⟶ X) ≃ X.obj.obj (Opposite.op U) :=
  (fromSchemeSpaceEquiv U X).symm.trans yonedaEquiv

/-- `AlgebraicGeometry.schemeSpacePointEquiv` is the Yoneda point of the morphism read through
`AlgebraicGeometry.schemeSpaceIso`. -/
theorem schemeSpacePointEquiv_apply {U : BigFppfOver B S hS} {X : AlgebraicSpaces B S hS}
    (f : schemeSpace U ⟶ X) :
    schemeSpacePointEquiv U X f = yonedaEquiv ((schemeSpaceIso U).inv ≫ f.hom) :=
  rfl

/-- The point of `AlgebraicGeometry.fromSchemeSpace y` is the Yoneda point of `y`. -/
@[simp]
theorem schemeSpacePointEquiv_fromSchemeSpace {U : BigFppfOver B S hS}
    {X : AlgebraicSpaces B S hS} (y : yoneda.obj U ⟶ X.obj) :
    schemeSpacePointEquiv U X (fromSchemeSpace y) = yonedaEquiv y := by
  simp [schemeSpacePointEquiv_apply]

/-- The morphism with a given point is `AlgebraicGeometry.fromSchemeSpace` of its Yoneda
morphism. -/
@[simp]
theorem schemeSpacePointEquiv_symm {U : BigFppfOver B S hS} {X : AlgebraicSpaces B S hS}
    (x : X.obj.obj (Opposite.op U)) :
    (schemeSpacePointEquiv U X).symm x = fromSchemeSpace (yonedaEquiv.symm x) :=
  rfl

/-- The point of a composite `f ≫ h` is the image under `h` of the point of `f`. -/
@[simp]
theorem schemeSpacePointEquiv_comp {U : BigFppfOver B S hS} {X Y : AlgebraicSpaces B S hS}
    (f : schemeSpace U ⟶ X) (h : X ⟶ Y) :
    schemeSpacePointEquiv U Y (f ≫ h) = h.hom.app (Opposite.op U) (schemeSpacePointEquiv U X f) :=
  rfl

/-- The point of `schemeSpaceMap g ≫ f` is the pullback along `g` of the point of `f`. -/
@[simp]
theorem schemeSpacePointEquiv_schemeSpaceMap_comp {U V : BigFppfOver B S hS}
    {X : AlgebraicSpaces B S hS} (g : U ⟶ V) (f : schemeSpace V ⟶ X) :
    schemeSpacePointEquiv U X (schemeSpaceMap g ≫ f) =
      X.obj.map g.op (schemeSpacePointEquiv V X f) := by
  rw [schemeSpacePointEquiv_apply, schemeSpacePointEquiv_apply, yonedaEquiv_naturality,
    ObjectProperty.FullSubcategory.comp_hom, schemeSpaceIso_inv_comp_schemeSpaceMap_hom_assoc]

/-- The point of `AlgebraicGeometry.schemeSpaceMap g` is `g`, read through
`AlgebraicGeometry.schemeSpaceIso`. -/
theorem schemeSpacePointEquiv_schemeSpaceMap {U V : BigFppfOver B S hS} (g : U ⟶ V) :
    schemeSpacePointEquiv U (schemeSpace V) (schemeSpaceMap g) =
      (schemeSpaceIso V).inv.app (Opposite.op U) g := by
  rw [schemeSpacePointEquiv_apply, schemeSpaceIso_inv_comp_schemeSpaceMap_hom, yonedaEquiv_comp,
    yonedaEquiv_yoneda_map]

/-- Two morphisms out of the algebraic space of a scheme agree once their points agree. -/
theorem schemeSpace_point_ext {U : BigFppfOver B S hS} {X : AlgebraicSpaces B S hS}
    {f f' : schemeSpace U ⟶ X}
    (h : schemeSpacePointEquiv U X f = schemeSpacePointEquiv U X f') : f = f' :=
  (schemeSpacePointEquiv U X).injective h

/-! ### Fibre products -/

/-- A square of schemes over `S` is cartesian exactly when the square of their algebraic spaces
is cartesian as a square of presheaves. -/
theorem isPullback_schemeSpaceMap_hom_iff {P U V W : BigFppfOver B S hS} {fst : P ⟶ U}
    {snd : P ⟶ V} {f : U ⟶ W} {g : V ⟶ W} :
    IsPullback (schemeSpaceMap fst).hom (schemeSpaceMap snd).hom (schemeSpaceMap f).hom
      (schemeSpaceMap g).hom ↔ IsPullback fst snd f g := by
  refine ⟨fun h => ?_, fun h => (h.map yoneda).of_iso (schemeSpaceIso P).symm
    (schemeSpaceIso U).symm (schemeSpaceIso V).symm (schemeSpaceIso W).symm
    (schemeSpaceIso_inv_comp_schemeSpaceMap_hom fst).symm
    (schemeSpaceIso_inv_comp_schemeSpaceMap_hom snd).symm
    (schemeSpaceIso_inv_comp_schemeSpaceMap_hom f).symm
    (schemeSpaceIso_inv_comp_schemeSpaceMap_hom g).symm⟩
  exact (h.of_iso (schemeSpaceIso P) (schemeSpaceIso U) (schemeSpaceIso V) (schemeSpaceIso W)
    (schemeSpaceMap_hom_comp_schemeSpaceIso_hom fst)
    (schemeSpaceMap_hom_comp_schemeSpaceIso_hom snd)
    (schemeSpaceMap_hom_comp_schemeSpaceIso_hom f)
    (schemeSpaceMap_hom_comp_schemeSpaceIso_hom g)).of_map_of_faithful yoneda

/-- A square of schemes over `S` is cartesian exactly when the square of their algebraic spaces
is cartesian. -/
theorem isPullback_schemeSpaceMap_iff {P U V W : BigFppfOver B S hS} {fst : P ⟶ U}
    {snd : P ⟶ V} {f : U ⟶ W} {g : V ⟶ W} :
    IsPullback (schemeSpaceMap fst) (schemeSpaceMap snd) (schemeSpaceMap f) (schemeSpaceMap g) ↔
      IsPullback fst snd f g := by
  rw [← isPullback_schemeSpaceMap_hom_iff]
  exact ⟨fun h => AlgebraicSpaces.isPullback_hom B S hS h,
    fun h => IsPullback.of_map_of_faithful (ObjectProperty.ι _) (f := schemeSpaceMap fst)
      (g := schemeSpaceMap snd) (h := schemeSpaceMap f) (i := schemeSpaceMap g) h⟩

end AlgebraicGeometry

end
