module

public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.StrongSplittingEtaleScheme

/-!
# De-realizing a residue field point, a separated morphism and a restriction

Let `G` be a groupoid scheme over `S` whose object scheme a big fppf site contains, let `u` be a
point of its object scheme, and let `U'` be an algebraic space over `S` with a morphism to the
object space of the realization of `G` and with representable underlying presheaf, so that `U'`
is the space represented by a scheme `Y` over `S` with a morphism `q : Y ⟶ U`.  A section of
`U'` over `Spec κ(u)` lying over the canonical morphism `Spec κ(u) ⟶ U` is then a point `y` of
`Y` above `u` with `κ(u) = κ(y)`; `q` is separated as soon as the morphism of spaces is; and the
restriction of the realization along the morphism represented by `q` has the same arrow space as
the restriction along the morphism out of `U'`.

## Main definitions

* `Stacks.Groupoids.GroupoidScheme.derealizeResiduePoint`: the morphism of schemes over `S` from
  the spectrum of the residue field at `u` underlying a section over that spectrum.
* `Stacks.Groupoids.GroupoidScheme.derealizeSpaceIso`: the de-realizing identification, read as
  an isomorphism of algebraic spaces.
* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.Restriction.arrowsCompIso`: the identification of
  the arrow spaces of two realizations of the restrictions along `g` and along `E.hom ≫ g`,
  with `_hom_comp_mapArrows`, `_hom_comp_source` and `_hom_comp_target` carrying the projection
  to the ambient arrow space and the two endpoint lifts across — the latter two up to `E`, since
  the lifts live in the two different spaces.

## Main results

* `AlgebraicGeometry.Scheme.Hom.isIso_residueFieldMap_base_closedPoint`: a section of a morphism
  of schemes over the spectrum of the residue field at a point `y` carries the closed point to a
  point above `y` whose residue field is `κ(y)`; its existential form is
  `AlgebraicGeometry.Scheme.Hom.exists_isIso_residueFieldMap_of_specResidueField`.
* `Stacks.Groupoids.GroupoidScheme.isIso_residueFieldMap_derealizeResiduePoint`: the point of the
  de-realized scheme determined by a residue field point of the space, with its residue field
  condition; its existential form is
  `Stacks.Groupoids.GroupoidScheme.exists_isIso_residueFieldMap_of_derealize`.
* `Stacks.Groupoids.GroupoidScheme.isSeparated_derealize`: a de-realized morphism is separated
  when the morphism of algebraic spaces it comes from is.
* `Stacks.Groupoids.GroupoidScheme.derealizeSpaceIso_hom_comp`: the de-realizing identification
  carries the morphism represented by `q` to the given morphism to the object space, which is
  what presents the latter as a morphism precomposed with an isomorphism.

## References

* [Stacks Project, Tag 04RX](https://stacks.math.columbia.edu/tag/04RX)
* [Stacks Project, Tag 04RZ](https://stacks.math.columbia.edu/tag/04RZ)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- **The point determined by a morphism from the spectrum of a residue field.**  A morphism
`Spec κ(y) ⟶ X` over the canonical morphism `Spec κ(y) ⟶ Y` carries the closed point to a point
of `X` above `y` with `κ(y) = κ(x)`.

Such a morphism is a point `x` of `X` together with an embedding `κ(x) ⟶ κ(y)`, by
`AlgebraicGeometry.Scheme.SpecToEquivOfField`, and that point is the image of the closed point;
lying over the canonical morphism makes the embedding a retraction of the residue field map of
`f` at `x`, which forces it to be an isomorphism. -/
theorem isIso_residueFieldMap_base_closedPoint {X Y : Scheme.{u}} (f : X ⟶ Y) (y : Y)
    (w : Spec (Y.residueField y) ⟶ X) (hw : w ≫ f = Y.fromSpecResidueField y) :
    f.base (w.base (IsLocalRing.closedPoint (Y.residueField y))) = y ∧
      IsIso (f.residueFieldMap (w.base (IsLocalRing.closedPoint (Y.residueField y)))) := by
  have hspec : Scheme.SpecToEquivOfField (Y.residueField y) Y (Y.fromSpecResidueField y) =
      ⟨y, CommRingCat.ofHom (RingHom.id (Y.residueField y))⟩ := by
    apply (Scheme.SpecToEquivOfField (Y.residueField y) Y).symm.injective
    rw [(Scheme.SpecToEquivOfField (Y.residueField y) Y).symm_apply_apply]
    show Y.fromSpecResidueField y =
      Spec.map (𝟙 (.of (Y.residueField y))) ≫ Y.fromSpecResidueField y
    rw [Spec.map_id, Category.id_comp]
  have hcomp := congrArg (Scheme.SpecToEquivOfField (Y.residueField y) Y) hw
  rw [hspec] at hcomp
  obtain ⟨e₀, hσ⟩ := Scheme.SpecToEquivOfField_eq_iff.1 hcomp
  have hdec := Scheme.descResidueField_stalkClosedPointTo_comp f w
  refine ⟨e₀, isIso_residueFieldMap_of_retraction f _
      ((Scheme.SpecToEquivOfField (Y.residueField y) X w).2 ≫
        (Y.residueFieldCongr e₀).inv) ?_⟩
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (fun k => k ≫ (Y.residueFieldCongr e₀).inv)
    (hdec.symm.trans hσ)).trans ?_
  exact (congrArg (fun k => k ≫ (Y.residueFieldCongr e₀).inv)
    (Category.comp_id (Y.residueFieldCongr e₀).hom)).trans
    (Y.residueFieldCongr e₀).hom_inv_id

/-- A morphism of schemes which admits a section over the spectrum of the residue field at a
point `y` has a point above `y` whose residue field is `κ(y)`. -/
theorem exists_isIso_residueFieldMap_of_specResidueField {X Y : Scheme.{u}} (f : X ⟶ Y) (y : Y)
    (w : Spec (Y.residueField y) ⟶ X) (hw : w ≫ f = Y.fromSpecResidueField y) :
    ∃ x : X, f.base x = y ∧ IsIso (f.residueFieldMap x) :=
  ⟨_, (isIso_residueFieldMap_base_closedPoint f y w hw).1,
    (isIso_residueFieldMap_base_closedPoint f y w hw).2⟩

end AlgebraicGeometry.Scheme.Hom

namespace Stacks.Groupoids.GroupoidScheme

open AlgebraicGeometry.Space

variable {S : Scheme.{u}} (G : GroupoidScheme S) (C : BigFppfSite.{u}) (hS : C.Contains S)
  (hU : C.Contains G.objects.left) {F : (BigFppfOver C S hS)ᵒᵖ ⥤ Type u} {Y : Over S}
  (hY : C.Contains Y.left) (q : Y ⟶ G.objects)
  (e : yoneda.obj (schemeSiteObject C hS hY) ≅ F)
  (φ : F ⟶ yoneda.obj (schemeSiteObject C hS hU))
  (he : e.hom ≫ φ = yoneda.map (schemeSiteMap C hS hY hU q))

/-! ### The point of the de-realized scheme -/

/-- The morphism of schemes over `S` from the spectrum of the residue field at `u` underlying a
section of a representable presheaf over that spectrum. -/
def derealizeResiduePoint (u : G.objects.left)
    (hK : C.Contains (Spec (G.objects.left.residueField u)))
    (v : F.obj (Opposite.op (schemeSiteObject C hS (X := residueOver G u) hK))) :
    residueOver G u ⟶ Y :=
  yonedaSchemePointEquiv C hS hY
    (Opposite.op (schemeSiteObject C hS (X := residueOver G u) hK))
    (e.inv.app (Opposite.op (schemeSiteObject C hS (X := residueOver G u) hK)) v)

include he in
/-- The de-realized morphism of a section, composed with `q`, is the morphism of schemes
underlying the image of that section in the object space. -/
theorem derealizeResiduePoint_comp (u : G.objects.left)
    (hK : C.Contains (Spec (G.objects.left.residueField u)))
    (v : F.obj (Opposite.op (schemeSiteObject C hS (X := residueOver G u) hK))) :
    derealizeResiduePoint G C hS hY e u hK v ≫ q =
      yonedaSchemePointEquiv C hS hU
        (Opposite.op (schemeSiteObject C hS (X := residueOver G u) hK)) (φ.app _ v) := by
  refine (yonedaSchemePointEquiv_map C hS hY hU q
    (Opposite.op (schemeSiteObject C hS (X := residueOver G u) hK))
    (e.inv.app (Opposite.op (schemeSiteObject C hS (X := residueOver G u) hK)) v)).symm.trans ?_
  refine congrArg (yonedaSchemePointEquiv C hS hU
    (Opposite.op (schemeSiteObject C hS (X := residueOver G u) hK))) ?_
  refine Eq.trans (congrArg
    (fun k => k (e.inv.app (Opposite.op
      (schemeSiteObject C hS (X := residueOver G u) hK)) v))
    (NatTrans.congr_app he.symm
      (Opposite.op (schemeSiteObject C hS (X := residueOver G u) hK)))) ?_
  exact congrArg
    (fun z => φ.app (Opposite.op (schemeSiteObject C hS (X := residueOver G u) hK)) z)
    (congrArg (fun k => k v) (NatTrans.congr_app e.inv_hom_id
      (Opposite.op (schemeSiteObject C hS (X := residueOver G u) hK))))

include he in
/-- A section lying over the canonical morphism `Spec κ(u) ⟶ U` de-realizes to a morphism of
schemes over that canonical morphism. -/
theorem derealizeResiduePoint_left_comp (u : G.objects.left)
    (hK : C.Contains (Spec (G.objects.left.residueField u)))
    (v : F.obj (Opposite.op (schemeSiteObject C hS (X := residueOver G u) hK)))
    (hv : (yonedaSchemePointEquiv C hS hU
        (Opposite.op (schemeSiteObject C hS (X := residueOver G u) hK)) (φ.app _ v)).left =
      G.objects.left.fromSpecResidueField u) :
    (derealizeResiduePoint G C hS hY e u hK v).left ≫ q.left =
      G.objects.left.fromSpecResidueField u :=
  (congrArg (fun m : residueOver G u ⟶ G.objects => m.left)
    (derealizeResiduePoint_comp G C hS hU hY q e φ he u hK v)).trans hv

include he in
/-- **The point of the de-realized scheme above `u` with residue field `κ(u)`.**  A section over
the spectrum of the residue field at `u` of a presheaf represented by a scheme `Y` over `S`,
lying over the canonical morphism `Spec κ(u) ⟶ U`, de-realizes to a morphism `Spec κ(u) ⟶ Y`
carrying the closed point to a point of `Y` above `u` at which the residue field map of `q` is an
isomorphism. -/
theorem isIso_residueFieldMap_derealizeResiduePoint (u : G.objects.left)
    (hK : C.Contains (Spec (G.objects.left.residueField u)))
    (v : F.obj (Opposite.op (schemeSiteObject C hS (X := residueOver G u) hK)))
    (hv : (yonedaSchemePointEquiv C hS hU
        (Opposite.op (schemeSiteObject C hS (X := residueOver G u) hK)) (φ.app _ v)).left =
      G.objects.left.fromSpecResidueField u) :
    q.left.base ((derealizeResiduePoint G C hS hY e u hK v).left.base
        (IsLocalRing.closedPoint (G.objects.left.residueField u))) = u ∧
      IsIso (q.left.residueFieldMap
        ((derealizeResiduePoint G C hS hY e u hK v).left.base
          (IsLocalRing.closedPoint (G.objects.left.residueField u)))) :=
  AlgebraicGeometry.Scheme.Hom.isIso_residueFieldMap_base_closedPoint q.left u
    (derealizeResiduePoint G C hS hY e u hK v).left
    (derealizeResiduePoint_left_comp G C hS hU hY q e φ he u hK v hv)

include he in
/-- The point of the de-realized scheme determined by a residue field point of the presheaf,
with its residue field condition. -/
theorem exists_isIso_residueFieldMap_of_derealize (u : G.objects.left)
    (hK : C.Contains (Spec (G.objects.left.residueField u)))
    (v : F.obj (Opposite.op (schemeSiteObject C hS (X := residueOver G u) hK)))
    (hv : (yonedaSchemePointEquiv C hS hU
        (Opposite.op (schemeSiteObject C hS (X := residueOver G u) hK)) (φ.app _ v)).left =
      G.objects.left.fromSpecResidueField u) :
    ∃ y : Y.left, q.left.base y = u ∧ IsIso (q.left.residueFieldMap y) :=
  ⟨_, (isIso_residueFieldMap_derealizeResiduePoint G C hS hU hY q e φ he u hK v hv).1,
    (isIso_residueFieldMap_derealizeResiduePoint G C hS hU hY q e φ he u hK v hv).2⟩

/-! ### Separatedness of the de-realized morphism -/

include he in
/-- **Separatedness of a de-realized morphism.**  A morphism of schemes over `S` whose Yoneda
image is, up to an isomorphism of the source, a separated morphism of algebraic spaces is
separated. -/
theorem isSeparated_derealize (hφ : IsSeparated C S hS φ) :
    AlgebraicGeometry.IsSeparated q.left := by
  refine (isSeparated_schemeSpaceMap_iff C hS hY hU q).1 ?_
  show IsSeparated C S hS (yoneda.map (schemeSiteMap C hS hY hU q))
  rw [← he]
  exact isSeparated_comp C S hS e.hom φ (isSeparated_of_isIso C S hS e.hom) hφ

end Stacks.Groupoids.GroupoidScheme

namespace AlgebraicGeometry.GroupoidInAlgebraicSpaces

variable {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
  {B : AlgebraicSpaces C S hS} {G : GroupoidInAlgebraicSpaces C S hS B}

/-! ### Comparing the two restrictions -/

/-- A realization of the restriction along a morphism is a realization of the restriction along
an equal morphism. -/
def Restriction.ofEq {U' : AlgebraicSpaces C S hS} {g g' : U' ⟶ G.objects} (h : g = g')
    (R : Restriction G g) : Restriction G g' := by
  cases h
  exact R

/-- Transporting a realization of a restriction along an equality of restricting morphisms does
not change the groupoid it realizes. -/
theorem Restriction.ofEq_groupoid {U' : AlgebraicSpaces C S hS} {g g' : U' ⟶ G.objects}
    (h : g = g') (R : Restriction G g) :
    (Restriction.ofEq h R).groupoid = R.groupoid := by
  cases h
  rfl

variable {U₁ U₂ : AlgebraicSpaces C S hS} (E : U₁ ≅ U₂) {g : U₂ ⟶ G.objects}
  (R : Restriction G g) (R' : Restriction G (E.hom ≫ g))

/-- **The arrow spaces of the two restrictions.**  The arrow space of a realization of the
restriction along `E.hom ≫ g` is canonically isomorphic to that of a realization of the
restriction along `g`. -/
noncomputable def Restriction.arrowsCompIso : R'.groupoid.arrows ≅ R.groupoid.arrows :=
  eqToIso R'.arrows_eq ≪≫ restrictionArrowsCompIso G E g ≪≫ eqToIso R.arrows_eq.symm

/-- The identification is the transport of
`AlgebraicGeometry.GroupoidInAlgebraicSpaces.restrictionArrowsCompIso` along the two equalities
of arrow spaces. -/
theorem Restriction.arrowsCompIso_hom :
    (Restriction.arrowsCompIso E R R').hom =
      eqToHom R'.arrows_eq ≫
        (restrictionArrowsCompIso G E g).hom ≫ eqToHom R.arrows_eq.symm :=
  rfl

/-- The identification carries the projection to the ambient arrow space of the restriction
along `g` to that of the restriction along `E.hom ≫ g`. -/
theorem Restriction.arrowsCompIso_hom_comp_arrowsToArrows :
    (Restriction.arrowsCompIso E R R').hom ≫
        eqToHom R.arrows_eq ≫ restrictionArrowsToArrows G g =
      eqToHom R'.arrows_eq ≫ restrictionArrowsToArrows G (E.hom ≫ g) := by
  rw [Restriction.arrowsCompIso_hom]
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  exact congrArg (fun k => eqToHom R'.arrows_eq ≫ k)
    (restrictionArrowsCompIso_hom_comp_arrowsToArrows G E g)

/-- The identification carries the morphism to the ambient arrow space across. -/
theorem Restriction.arrowsCompIso_hom_comp_mapArrows :
    (Restriction.arrowsCompIso E R R').hom.hom ≫ R.hom.toGroupoidHom.mapArrows =
      R'.hom.toGroupoidHom.mapArrows := by
  rw [R.mapArrows_eq, R'.mapArrows_eq]
  exact congrArg (fun m : R'.groupoid.arrows ⟶ G.arrows => m.hom)
    (Restriction.arrowsCompIso_hom_comp_arrowsToArrows E R R')

/-- The identification carries a lift of an endpoint across, up to the isomorphism, once the
corresponding lifts of the two restrictions are the transports of those of the ambient
restrictions. -/
private theorem Restriction.arrowsCompIso_hom_comp_lift
    {s : R.groupoid.arrows ⟶ R.groupoid.objects} {s' : R'.groupoid.arrows ⟶ R'.groupoid.objects}
    {r : restrictionArrows G g ⟶ U₂} {r' : restrictionArrows G (E.hom ≫ g) ⟶ U₁}
    (hs : s = eqToHom R.arrows_eq ≫ r ≫ eqToHom R.objects_eq.symm)
    (hs' : s' = eqToHom R'.arrows_eq ≫ r' ≫ eqToHom R'.objects_eq.symm)
    (h : (restrictionArrowsCompIso G E g).hom ≫ r = r' ≫ E.hom) :
    (Restriction.arrowsCompIso E R R').hom ≫ s =
      s' ≫ eqToHom R'.objects_eq ≫ E.hom ≫ eqToHom R.objects_eq.symm := by
  rw [Restriction.arrowsCompIso_hom, hs, hs']
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  rw [reassoc_of% h]

/-- The identification carries the source across, up to the isomorphism: the two lifts live in
the two different spaces. -/
theorem Restriction.arrowsCompIso_hom_comp_source :
    (Restriction.arrowsCompIso E R R').hom ≫ R.groupoid.source =
      R'.groupoid.source ≫ eqToHom R'.objects_eq ≫ E.hom ≫ eqToHom R.objects_eq.symm :=
  Restriction.arrowsCompIso_hom_comp_lift E R R' R.source_eq R'.source_eq
    (restrictionArrowsCompIso_hom_comp_source G E g)

/-- The identification carries the target across, up to the isomorphism. -/
theorem Restriction.arrowsCompIso_hom_comp_target :
    (Restriction.arrowsCompIso E R R').hom ≫ R.groupoid.target =
      R'.groupoid.target ≫ eqToHom R'.objects_eq ≫ E.hom ≫ eqToHom R.objects_eq.symm :=
  Restriction.arrowsCompIso_hom_comp_lift E R R' R.target_eq R'.target_eq
    (restrictionArrowsCompIso_hom_comp_target G E g)

end AlgebraicGeometry.GroupoidInAlgebraicSpaces

namespace Stacks.Groupoids.GroupoidScheme

open AlgebraicGeometry.Space

/-! ### The de-realized restricting morphism -/

variable {S : Scheme.{u}} (G : GroupoidScheme S) (C : BigFppfSite.{u}) (hS : C.Contains S)
  (hU : C.Contains G.objects.left) (hR : C.Contains G.arrows.left)
  (hP : C.Contains (pullback G.source G.target).left) {Y : Over S} (hY : C.Contains Y.left)
  (q : Y ⟶ G.objects) {U' : AlgebraicSpaces C S hS}
  (e : yoneda.obj (schemeSiteObject C hS hY) ≅ U'.obj)
  (g : U' ⟶ (G.realization C hS hU hR hP).objects)

/-- The identification of algebraic spaces underlying a de-realization: the space represented by
the de-realized scheme is the given one. -/
def derealizeSpaceIso : siteSchemeSpace C hS hY ≅ U' where
  hom := ObjectProperty.homMk e.hom
  inv := ObjectProperty.homMk e.inv
  hom_inv_id := by
    apply ObjectProperty.hom_ext
    exact e.hom_inv_id
  inv_hom_id := by
    apply ObjectProperty.hom_ext
    exact e.inv_hom_id

/-- The de-realization identifies the given morphism to the object space with the morphism
represented by the de-realized morphism of schemes. -/
theorem derealizeSpaceIso_hom_comp
    (he : e.hom ≫ g.hom = yoneda.map (schemeSiteMap C hS hY hU q)) :
    (derealizeSpaceIso C hS hY e).hom ≫ g = realizationMap G C hS hU hR hP hY q := by
  apply ObjectProperty.hom_ext
  exact he

end Stacks.Groupoids.GroupoidScheme

end

end
