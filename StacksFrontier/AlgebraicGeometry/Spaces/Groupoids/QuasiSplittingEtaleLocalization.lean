module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.EtaleLocalizationStabilizerMembership
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupoidSchemeDerealization
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupoidSchemeEtaleLocalization

/-!
# Quasi-splitting on an étale neighbourhood of a point

Let `(U, R, s, t, c)` be a groupoid scheme over `S` with `s` and `t` separated and locally of
finite type, let `u ∈ U`, and let `s` be quasi-finite at the identity arrow `e(u)`; this is
Situation 04RV.  Then there are an algebraic space `U'`, an étale morphism `g : U' ⟶ U` and a
point `u' : Spec κ(u) ⟶ U'` over `u` such that `R' = R|_{U'}` is quasi-split over `u'`.  This is
**Stacks 04RW**.

The neighbourhood is the finite part `U' = (R_s/U, e)_{fin}` of Stacks 04RU with its étale
projection, the point is the pair `(u, Z_u)` with `Z_u` the open and closed piece of the fibre
`F_u = R ×_{s, U} Spec κ(u)` supported on `e(u)`, and the quasi-splitting is the universal open
`Z_univ` read inside `R|_{U'}`.

## Main results

* `Stacks.Groupoids.GroupoidScheme.realization_identity_yonedaMap`: the identity arrow of the
  realization of a groupoid scheme at a generalized object is the identity of the groupoid scheme
  composed with that object.
* `AlgebraicGeometry.Space.QuasiSplittingSituation.exists_fiberOpens_identity`: the summand
  `Z_u` of `F_u` supported on `e(u)`.
* `AlgebraicGeometry.Space.etaleLocalFibrePointOfMem` and
  `AlgebraicGeometry.Space.lies_over_fibrePointOfMem`: the point `u'` of `U'` over `u` attached
  to any open of `F_u`, finite over `κ(u)`, containing the point the unit section carries.
* `Stacks.Groupoids.GroupoidScheme.exists_quasiSplit_of_quasiSplittingSituation`:
  **Stacks 04RW**.

## Implementation notes

Situation 04RV asks quasi-finiteness of the source only at `e(u)`, so the summand `Z_u` is the
singleton `{e(u)}`, and the point `u' = (u, Z_u)` exists only because the unit of the finite
part is the identity arrow of the groupoid scheme there.  That identification is
`AlgebraicGeometry.Space.unitArrowSite_eq`, proved from
`Stacks.Groupoids.GroupoidScheme.realization_identity_yonedaMap`: the identity arrow of a groupoid
in functors is characterized as the arrow with both endpoints at the object which composes with
itself to itself, and `e(u)` has that property by the unit axioms of a groupoid scheme.

The chain which turns an open of the fibre into a section of `(R_s/U, e)_{fin}` is carried out
here under the hypothesis that the open contains the point the unit section carries, which is
weaker than the description of the open used in Situation 04RL
(`AlgebraicGeometry.Space.etaleLocalFibrePoint`) and in Situation 0DTB
(`AlgebraicGeometry.Space.etaleLocalStabilizerFibrePoint`), and holds for the singleton
`{e(u)}`.

The quasi-splitting is weaker than the splitting conditions of Stacks 04RK parts (1) and (2):
it asks only that the open finite subgroupoid contain the identity arrow at the point, which
`AlgebraicGeometry.GroupoidInAlgebraicSpaces.isQuasiSplitAt_of_openFiniteSubgroupoid` supplies
for every point from `Z_univ` alone.  So no containment of arrows over `u'` is needed, and the
hypotheses of Situation 04RV are consumed only in producing `Z_u`.

## References

* [Stacks Project, Tag 04RK](https://stacks.math.columbia.edu/tag/04RK)
* [Stacks Project, Tag 04RU](https://stacks.math.columbia.edu/tag/04RU)
* [Stacks Project, Tag 04RV](https://stacks.math.columbia.edu/tag/04RV)
* [Stacks Project, Tag 04RW](https://stacks.math.columbia.edu/tag/04RW)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Groupoids.GroupoidScheme

variable {S : Scheme.{u}} (G : GroupoidScheme S)

/-- The identity arrow at a generalized object composes with itself to itself. -/
theorem compose_identity_self {T : Over S} (f : T ⟶ G.objects)
    (w : (f ≫ G.identity) ≫ G.source = (f ≫ G.identity) ≫ G.target) :
    G.compose (f ≫ G.identity) (f ≫ G.identity) w = f ≫ G.identity := by
  have hb : (f ≫ G.identity) ≫ G.target ≫ G.identity = f ≫ G.identity := by
    rw [← Category.assoc, Category.assoc f, G.target_identity, Category.comp_id]
  have hw : ((f ≫ G.identity) ≫ G.target ≫ G.identity) ≫ G.source =
      (f ≫ G.identity) ≫ G.target := by
    rw [hb, w]
  have hli := G.left_identity T (f ≫ G.identity) hw
  have hlift : pullback.lift ((f ≫ G.identity) ≫ G.target ≫ G.identity)
        (f ≫ G.identity) hw =
      pullback.lift (f ≫ G.identity) (f ≫ G.identity) w := by
    refine pullback.hom_ext ?_ ?_
    · rw [pullback.lift_fst, pullback.lift_fst, hb]
    · rw [pullback.lift_snd, pullback.lift_snd]
  rwa [hlift] at hli

/-- An arrow which is the identity at a generalized object composes with itself to itself. -/
theorem compose_self_of_eq_identity {T : Over S} (b : T ⟶ G.arrows) (f : T ⟶ G.objects)
    (hb : b = f ≫ G.identity) (w : b ≫ G.source = b ≫ G.target) :
    G.compose b b w = b := by
  subst hb
  exact G.compose_identity_self f w

variable (C : BigFppfSite.{u}) (hS : C.Contains S) (hU : C.Contains G.objects.left)
  (hR : C.Contains G.arrows.left) (hP : C.Contains (pullback G.source G.target).left)

open AlgebraicGeometry.Space in
/-- The identity arrow of the realization of a groupoid scheme at a generalized object is the
Yoneda image of the identity of the groupoid scheme, composed with that object. -/
theorem realization_identity_yonedaMap (T : (BigFppfOver C S hS)ᵒᵖ)
    (x : (realization G C hS hU hR hP).objects.obj.obj T) :
    (realization G C hS hU hR hP).toGroupoidInFunctors.identity T x =
      (yoneda.map (schemeSiteMap C hS hU hR G.identity)).app T x := by
  set a : (realization G C hS hU hR hP).arrows.obj.obj T :=
    (yoneda.map (schemeSiteMap C hS hU hR G.identity)).app T x
  have hxa : yonedaSchemePointEquiv C hS hR T a =
      yonedaSchemePointEquiv C hS hU T x ≫ G.identity :=
    yonedaSchemePointEquiv_map C hS hU hR G.identity T x
  have hst : ∀ m : G.arrows ⟶ G.objects, G.identity ≫ m = 𝟙 _ →
      (yoneda.map (schemeSiteMap C hS hR hU m)).app T a = x := fun m hm => by
    refine (yonedaSchemePointEquiv C hS hU T).injective ?_
    rw [yonedaSchemePointEquiv_map, hxa, Category.assoc, hm, Category.comp_id]
  have hs : (realization G C hS hU hR hP).source.hom.app T a = x := hst _ G.source_identity
  have ht : (realization G C hS hU hR hP).target.hom.app T a = x := hst _ G.target_identity
  refine Deformation.GroupoidInFunctors.identity_eq_of_idempotent
    (realization G C hS hU hR hP).toGroupoidInFunctors T x a hs ht ?_
  have hw : yonedaSchemePointEquiv C hS hR T a ≫ G.source =
      yonedaSchemePointEquiv C hS hR T a ≫ G.target := by
    rw [hxa, Category.assoc, Category.assoc, G.source_identity, G.target_identity]
  refine (yonedaSchemePointEquiv C hS hR T).injective ?_
  exact (realizationComp_app G C hS hU hR hP T ⟨(a, a), hs.trans ht.symm⟩ hw).trans
    (G.compose_self_of_eq_identity (yonedaSchemePointEquiv C hS hR T a)
      (yonedaSchemePointEquiv C hS hU T x) hxa hw)

end Stacks.Groupoids.GroupoidScheme

namespace AlgebraicGeometry.Space

open Stacks.Groupoids.GroupoidScheme

/-- Pullbacks of presheaves on the big fppf site over `S`, given directly: instance search for
them times out under Lean v4.35.0. -/
local instance (priority := high) hasPullbacks_presheaf_quasiSplittingEtaleLocalization
    {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S} :
    HasPullbacks ((BigFppfOver C S hS)ᵒᵖ ⥤ Type u) :=
  Limits.functorCategoryHasLimitsOfShape

local instance (priority := high) hasPullback_presheaf_quasiSplittingEtaleLocalization
    {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
    {X Y Z : (BigFppfOver C S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  hasPullbacks_presheaf_quasiSplittingEtaleLocalization.has_limit _

variable {S : Scheme.{u}} (G : Stacks.Groupoids.GroupoidScheme S)
  (C : BigFppfSite.{u}) (hS : C.Contains S) (hU : C.Contains G.objects.left)
  (hR : C.Contains G.arrows.left) (u : G.objects.left)
  (hK : C.Contains (Spec (G.objects.left.residueField u)))
  (hP : C.Contains (pullback G.source G.target).left)
  (F : FinitePartUniversalOpen (G.realization C hS hU hR hP))

/-- The unit arrow of the finite part at the residue field point of `u` is the identity arrow
`e(u)` of the groupoid scheme there. -/
theorem unitArrowSite_eq :
    unitArrowSite G C hS hU hR u hK hP F =
      residueSiteMap G C hS hU u hK ≫ schemeSiteMap C hS hU hR G.identity := by
  have h := congrArg yonedaEquiv (yoneda_map_unitArrowSite G C hS hU hR u hK hP F)
  rw [yonedaEquiv_yoneda_map] at h
  refine h.trans ((congrArg (fun z => F.unit.hom.app
      (Opposite.op (schemeSiteObject C hS (X := residueOver G u) hK)) z)
    (Category.id_comp (residueSiteMap G C hS hU u hK))).trans ?_)
  exact (F.unit_identity _ (residueSiteMap G C hS hU u hK)).trans
    (realization_identity_yonedaMap G C hS hU hR hP _ (residueSiteMap G C hS hU u hK))

/-- On underlying schemes, the unit arrow of the finite part at the residue field point of `u`
is the identity arrow of the groupoid scheme, precomposed with `Spec κ(u) ⟶ U`. -/
theorem toScheme_map_unitArrowSite_eq :
    (BigFppfOver.toScheme C S hS).map (unitArrowSite G C hS hU hR u hK hP F) =
      G.objects.left.fromSpecResidueField u ≫ G.identity.left := by
  rw [unitArrowSite_eq, Functor.map_comp, toScheme_map_schemeSiteMap_eq,
    toScheme_map_schemeSiteMap_eq]
  rfl

/-- Every point of `Spec κ(u)` is carried by the unit arrow of the finite part to the identity
arrow `e(u)` of the groupoid scheme. -/
theorem toScheme_map_unitArrowSite_apply (y : (BigFppfOver.toScheme C S hS).obj
    (schemeSiteObject C hS (X := residueOver G u) hK)) :
    (BigFppfOver.toScheme C S hS).map (unitArrowSite G C hS hU hR u hK hP F) y =
      G.identity.left u := by
  have hr : (G.objects.left.fromSpecResidueField u) y = u := by
    have hmem : (G.objects.left.fromSpecResidueField u) y ∈
        Set.range (G.objects.left.fromSpecResidueField u) := ⟨y, rfl⟩
    rwa [Scheme.range_fromSpecResidueField] at hmem
  rw [toScheme_map_unitArrowSite_eq]
  exact congrArg G.identity.left hr

/-! ### The point of the finite part attached to an open containing the unit -/

section Mem

variable (W : (G.source.left.fiber u).Opens)
  (hmem : ∀ y : (BigFppfOver.toScheme C S hS).obj
      (schemeSiteObject C hS (X := residueOver G u) hK),
    (etaleLocalFibreIso G C hS hU hR u hK).hom
      ((BigFppfOver.toScheme C S hS).map (unitFibreSection G C hS hU hR u hK hP F) y) ∈ W)
  (hWfin : AlgebraicGeometry.IsFinite (W.ι ≫ G.source.left.fiberToSpecResidueField u))

include hmem in
/-- The unit section factors set-theoretically through an open of the fibre containing the point
it carries. -/
theorem unitFibreSection_range_le_of_mem :
    Set.range ((BigFppfOver.toScheme C S hS).map
        (unitFibreSection G C hS hU hR u hK hP F)) ⊆
      Set.range (fibreOpenImmersion G C hS hU hR u hK W) := by
  rintro _ ⟨y, rfl⟩
  refine ⟨⟨(etaleLocalFibreIso G C hS hU hR u hK).hom
      ((BigFppfOver.toScheme C S hS).map (unitFibreSection G C hS hU hR u hK hP F) y),
    hmem y⟩, ?_⟩
  show (etaleLocalFibreIso G C hS hU hR u hK).inv
      ((etaleLocalFibreIso G C hS hU hR u hK).hom
        ((BigFppfOver.toScheme C S hS).map (unitFibreSection G C hS hU hR u hK hP F) y)) =
    (BigFppfOver.toScheme C S hS).map (unitFibreSection G C hS hU hR u hK hP F) y
  rw [← Scheme.Hom.comp_apply, Iso.hom_inv_id]
  rfl

include hmem in
/-- The factorization of the unit section through such an open, by the universal property of an
open immersion. -/
def unitOpenLiftOfMem :
    (BigFppfOver.toScheme C S hS).obj (schemeSiteObject C hS (X := residueOver G u) hK) ⟶
      (BigFppfOver.toScheme C S hS).obj (fibreOpenSite G C hS hU hR u hK W) :=
  AlgebraicGeometry.IsOpenImmersion.lift
    (H := isOpenImmersion_fibreOpenImmersion G C hS hU hR u hK W)
    (fibreOpenImmersion G C hS hU hR u hK W)
    ((BigFppfOver.toScheme C S hS).map (unitFibreSection G C hS hU hR u hK hP F))
    (unitFibreSection_range_le_of_mem G C hS hU hR u hK hP F W hmem)

include hmem in
/-- That morphism is a factorization of the unit section. -/
theorem unitOpenLiftOfMem_fac :
    unitOpenLiftOfMem G C hS hU hR u hK hP F W hmem ≫
        fibreOpenImmersion G C hS hU hR u hK W =
      (BigFppfOver.toScheme C S hS).map (unitFibreSection G C hS hU hR u hK hP F) :=
  AlgebraicGeometry.IsOpenImmersion.lift_fac
    (H := isOpenImmersion_fibreOpenImmersion G C hS hU hR u hK W) _ _ _

include hmem in
/-- The factorization of the unit section through the open, as a morphism of the site. -/
def unitOpenSectionOfMem :
    schemeSiteObject C hS (X := residueOver G u) hK ⟶ fibreOpenSite G C hS hU hR u hK W :=
  Over.homMk (ObjectProperty.homMk (unitOpenLiftOfMem G C hS hU hR u hK hP F W hmem)) (by
    apply ObjectProperty.hom_ext
    change unitOpenLiftOfMem G C hS hU hR u hK hP F W hmem ≫
      (fibreOpenImmersion G C hS hU hR u hK W ≫
        (fibreSiteObject G C hS hU hR u hK).hom.hom) = _
    exact ((Category.assoc _ _ _).symm.trans
      (congrArg (fun k => k ≫ (fibreSiteObject G C hS hU hR u hK).hom.hom)
        (unitOpenLiftOfMem_fac G C hS hU hR u hK hP F W hmem))).trans
      (congrArg (fun k => k.hom) (Over.w (unitFibreSection G C hS hU hR u hK hP F))))

include hmem in
/-- That morphism of the site is a factorization of the unit section. -/
theorem unitOpenSectionOfMem_comp :
    unitOpenSectionOfMem G C hS hU hR u hK hP F W hmem ≫
        fibreOpenSiteMap G C hS hU hR u hK W =
      unitFibreSection G C hS hU hR u hK hP F :=
  (BigFppfOver.toScheme C S hS).map_injective
    (((BigFppfOver.toScheme C S hS).map_comp _ _).trans
      ((congrArg (fun k => (BigFppfOver.toScheme C S hS).map
            (unitOpenSectionOfMem G C hS hU hR u hK hP F W hmem) ≫ k)
          (toScheme_map_siteOpenMap C S hS (fibreSiteObject G C hS hU hR u hK)
            (fibreOpenImmersion G C hS hU hR u hK W)
            (isOpenImmersion_fibreOpenImmersion G C hS hU hR u hK W))).trans
        (unitOpenLiftOfMem_fac G C hS hU hR u hK hP F W hmem)))

include hmem in
/-- Composing it with the inclusion of the open and the projection to `Spec κ(u)` is the
identity. -/
theorem unitOpenSectionOfMem_comp_fst :
    unitOpenSectionOfMem G C hS hU hR u hK hP F W hmem ≫
        (fibreOpenSiteMap G C hS hU hR u hK W ≫
          pullback.fst (residueSiteMap G C hS hU u hK) (sourceSiteMap G C hS hU hR)) = 𝟙 _ :=
  (Category.assoc _ _ _).symm.trans
    ((congrArg (fun k => k ≫ pullback.fst (residueSiteMap G C hS hU u hK)
        (sourceSiteMap G C hS hU hR))
      (unitOpenSectionOfMem_comp G C hS hU hR u hK hP F W hmem)).trans
      (unitFibreSection_comp_fst G C hS hU hR u hK hP F))

include hmem in
/-- Composing it with the inclusion of the open and the projection to `R` is the unit arrow. -/
theorem unitOpenSectionOfMem_comp_snd :
    unitOpenSectionOfMem G C hS hU hR u hK hP F W hmem ≫
        (fibreOpenSiteMap G C hS hU hR u hK W ≫
          pullback.snd (residueSiteMap G C hS hU u hK) (sourceSiteMap G C hS hU hR)) =
      unitArrowSite G C hS hU hR u hK hP F :=
  (Category.assoc _ _ _).symm.trans
    ((congrArg (fun k => k ≫ pullback.snd (residueSiteMap G C hS hU u hK)
        (sourceSiteMap G C hS hU hR))
      (unitOpenSectionOfMem_comp G C hS hU hR u hK hP F W hmem)).trans
      (unitFibreSection_comp_snd G C hS hU hR u hK hP F))

include hmem in
/-- The pair `(u, Z_u)` attached to such an open contains the unit, which is the condition
placing it in the finite part with section `(R_s/U, e)_fin`. -/
theorem containsSection_fibreFiniteOpenSubspace_of_memOpen :
    ContainsSection C S hS (G.realization C hS hU hR hP).source F.unit F.unit_source
      (fibreFiniteOpenSubspace G C hS hU hR u hK hP W hWfin) := by
  refine ⟨yoneda.map (unitOpenSectionOfMem G C hS hU hR u hK hP F W hmem) ≫
    Subfunctor.toRange (fibreOpenPresheafMap G C hS hU hR u hK W), ?_⟩
  refine ((Category.assoc _ _ _).trans
    (congrArg (fun k =>
      yoneda.map (unitOpenSectionOfMem G C hS hU hR u hK hP F W hmem) ≫ k)
      (Subfunctor.toRange_ι (fibreOpenPresheafMap G C hS hU hR u hK W)))).trans
    (pullback.hom_ext ?_ ?_)
  · exact ((Category.assoc _ _ _).trans
      ((congrArg (fun k =>
            yoneda.map (unitOpenSectionOfMem G C hS hU hR u hK hP F W hmem) ≫ k)
          (fibreOpenPresheafMap_comp_fst G C hS hU hR u hK W)).trans
        (((yoneda.map_comp _ _).symm.trans
            (congrArg yoneda.map
              (unitOpenSectionOfMem_comp_fst G C hS hU hR u hK hP F W hmem))).trans
          (yoneda.map_id _)))).trans (pullback.lift_fst _ _ _).symm
  · exact ((Category.assoc _ _ _).trans
      ((congrArg (fun k =>
            yoneda.map (unitOpenSectionOfMem G C hS hU hR u hK hP F W hmem) ≫ k)
          (fibreOpenPresheafMap_comp_snd G C hS hU hR u hK W)).trans
        (((yoneda.map_comp _ _).symm.trans
            (congrArg yoneda.map
              (unitOpenSectionOfMem_comp_snd G C hS hU hR u hK hP F W hmem))).trans
          (yoneda_map_unitArrowSite G C hS hU hR u hK hP F)))).trans
      (pullback.lift_snd _ _ _).symm

include hmem in
/-- The section of the finite part which that pair names lies in the open subspace
`(R_s/U, e)_fin` cut out by containing the unit. -/
theorem mem_finitePartWithSection_of_mem :
    fibrePresheafSection G C hS hU hR u hK hP W hWfin ∈
      (finitePartWithSection C S hS (G.realization C hS hU hR hP).source F.unit
        F.unit_source).toSubfunctor.obj
        (Opposite.op (schemeSiteObject C hS (X := residueOver G u) hK)) := by
  rw [(finitePartWithSection C S hS (G.realization C hS hU hR hP).source F.unit
    F.unit_source).mem_iff]
  refine containsSection_restrict (G.realization C hS hU hR hP).source F.unit F.unit_source
    ((finiteOpenSubspaceEquiv C S hS (G.realization C hS hU hR hP).source
      (schemeSpace (schemeSiteObject C hS (X := residueOver G u) hK))).1.symm
      (fibreFiniteOpenSubspace G C hS hU hR u hK hP W hWfin))
    ?_ (schemeSiteObject C hS (X := residueOver G u) hK)
    (𝟙 (schemeSiteObject C hS (X := residueOver G u) hK))
  rw [Equiv.apply_symm_apply]
  exact containsSection_fibreFiniteOpenSubspace_of_memOpen G C hS hU hR u hK hP F W hmem hWfin

include hmem in
/-- The `Spec κ(u)`-valued point of the object space of the finite part named by the pair
`(u, Z_u)` for such an open. -/
def etaleLocalFibrePointOfMem :
    F.objects.obj.obj (Opposite.op (schemeSiteObject C hS (X := residueOver G u) hK)) :=
  F.objectsEquiv.inv.app _
    ⟨fibrePresheafSection G C hS hU hR u hK hP W hWfin,
      mem_finitePartWithSection_of_mem G C hS hU hR u hK hP F W hmem hWfin⟩

include hmem in
/-- The image of that point under the projection `g : U' ⟶ U` is the canonical morphism
`Spec κ(u) ⟶ U`, read in the site. -/
theorem objectProjection_fibrePointOfMem :
    F.objectProjection.hom.app
        (Opposite.op (schemeSiteObject C hS (X := residueOver G u) hK))
        (etaleLocalFibrePointOfMem G C hS hU hR u hK hP F W hmem hWfin) =
      residueSiteMap G C hS hU u hK := by
  have h1 := congrArg (fun k : F.objects.obj ⟶ (G.realization C hS hU hR hP).objects.obj =>
      k.app (Opposite.op (schemeSiteObject C hS (X := residueOver G u) hK))
        (etaleLocalFibrePointOfMem G C hS hU hR u hK hP F W hmem hWfin))
    F.objectProjection_spec
  have h2 : F.objectsEquiv.hom.app
      (Opposite.op (schemeSiteObject C hS (X := residueOver G u) hK))
      (etaleLocalFibrePointOfMem G C hS hU hR u hK hP F W hmem hWfin) =
      ⟨fibrePresheafSection G C hS hU hR u hK hP W hWfin,
        mem_finitePartWithSection_of_mem G C hS hU hR u hK hP F W hmem hWfin⟩ :=
    congrArg (fun k => k.app
      (Opposite.op (schemeSiteObject C hS (X := residueOver G u) hK))
      ⟨fibrePresheafSection G C hS hU hR u hK hP W hWfin,
        mem_finitePartWithSection_of_mem G C hS hU hR u hK hP F W hmem hWfin⟩)
      F.objectsEquiv.inv_hom_id
  refine h1.trans ((congrArg (fun z =>
    (finiteOpenSubspacePresheaf C S hS (G.realization C hS hU hR hP).source).baseMap.app
      (Opposite.op (schemeSiteObject C hS (X := residueOver G u) hK))
      ((finitePartWithSection C S hS (G.realization C hS hU hR hP).source F.unit
        F.unit_source).toSubfunctor.ι.app
        (Opposite.op (schemeSiteObject C hS (X := residueOver G u) hK)) z)) h2).trans ?_)
  exact baseMap_fibrePresheafSection G C hS hU hR u hK hP W hWfin

include hmem in
/-- That point lies over `u`: its composition with the étale projection `g : U' ⟶ U` is the
canonical morphism `Spec κ(u) ⟶ U`. -/
theorem lies_over_fibrePointOfMem :
    (yonedaSchemePointEquiv C hS hU
        (Opposite.op (schemeSiteObject C hS (X := residueOver G u) hK))
        (F.objectProjection.hom.app _
          (etaleLocalFibrePointOfMem G C hS hU hR u hK hP F W hmem hWfin))).left =
      G.objects.left.fromSpecResidueField u := by
  rw [objectProjection_fibrePointOfMem G C hS hU hR u hK hP F W hmem hWfin]
  exact congrArg Over.Hom.left (siteToOver_map_schemeSiteMap C hS
    (X := residueOver G u) (Y := G.objects) hK hU (residuePoint G u))

end Mem

/-! ### The open of the fibre supported on the identity arrow -/

/-- In the quasi-splitting situation of Stacks 04RV the identity arrow `e(u)` cuts out an open
and closed subscheme of the fibre `F_u = R ×_{s, U} Spec κ(u)` of the source over `u` which is
finite over the residue field `κ(u)`.

This is the summand `Z_u` of `F_u` from which the étale neighbourhood is built; it comes from
the quasi-finiteness of the source at `e(u)`. -/
theorem QuasiSplittingSituation.exists_fiberOpens_identity (D : QuasiSplittingSituation.{u}) :
    ∃ W : (D.groupoid.source.left.fiber D.u).Opens,
      (∀ x : D.groupoid.source.left.fiber D.u,
        x ∈ W ↔
          D.groupoid.source.left.fiberι D.u x = D.groupoid.identity.left D.u) ∧
      _root_.AlgebraicGeometry.IsFinite
        (W.ι ≫ D.groupoid.source.left.fiberToSpecResidueField D.u) := by
  classical
  have hsrc : D.groupoid.source.left (D.groupoid.identity.left D.u) = D.u := by
    simpa using congrArg
      (fun m : D.groupoid.objects.left ⟶ D.groupoid.objects.left => m.base D.u)
      (Stacks.Groupoids.identity_left_comp_source_left D.groupoid)
  obtain ⟨W, hW, -, hfin⟩ := exists_fiberOpens_of_finite_of_quasiFiniteAt
    D.groupoid.source.left D.u
    {(D.groupoid.source.left.fiberHomeo D.u).symm ⟨D.groupoid.identity.left D.u, hsrc⟩}
    (Set.finite_singleton _) (fun x hx => by
      rw [Set.mem_singleton_iff] at hx
      subst hx
      rw [Scheme.Hom.fiberι_fiberHomeo_symm]
      exact D.sourceQuasiFiniteAtIdentity.2)
  refine ⟨W, fun x => ?_, hfin⟩
  have hWx : (x ∈ W) = (x ∈ ({(D.groupoid.source.left.fiberHomeo D.u).symm
                                ⟨D.groupoid.identity.left D.u, hsrc⟩} :
      Set (D.groupoid.source.left.fiber D.u))) := congrArg (x ∈ ·) hW
  have hfib : D.groupoid.source.left.fiberι D.u
      ((D.groupoid.source.left.fiberHomeo D.u).symm
        ⟨D.groupoid.identity.left D.u, hsrc⟩) = D.groupoid.identity.left D.u :=
    Scheme.Hom.fiberι_fiberHomeo_symm D.groupoid.source.left D.u _
  rw [hWx, Set.mem_singleton_iff]
  exact ⟨fun h => h ▸ hfib,
    fun h => injective_fiberι D.groupoid D.u (h.trans hfib.symm)⟩

/-- **The point of the fibre carried by the unit section is the identity arrow `e(u)`**, so it
lies in any open of the fibre supported there. -/
theorem unitFibrePoint_mem_identity (W : (G.source.left.fiber u).Opens)
    (hWid : ∀ x : G.source.left.fiber u,
      x ∈ W ↔ G.source.left.fiberι u x = G.identity.left u)
    (y : (BigFppfOver.toScheme C S hS).obj
      (schemeSiteObject C hS (X := residueOver G u) hK)) :
    (etaleLocalFibreIso G C hS hU hR u hK).hom
      ((BigFppfOver.toScheme C S hS).map
        (unitFibreSection G C hS hU hR u hK hP F) y) ∈ W := by
  rw [hWid]
  have h := congrArg (fun k => k y) (unitFibrePoint_comp_fiberι G C hS hU hR u hK hP F)
  simp only [Scheme.Hom.comp_apply] at h
  rw [h]
  exact toScheme_map_unitArrowSite_apply G C hS hU hR u hK hP F y

end AlgebraicGeometry.Space

/-! ### Stacks 04RW -/

namespace Stacks.Groupoids.GroupoidScheme

open AlgebraicGeometry AlgebraicGeometry.Space

/-- **Stacks Project, Tag 04RW.**  In the quasi-splitting situation of Stacks 04RV there are an
algebraic space `U'`, an étale morphism `g : U' ⟶ U` of algebraic spaces and a point
`u' : Spec κ(u) ⟶ U'` lying over `u : Spec κ(u) ⟶ U` such that the restriction `R' = R|_{U'}`
of `R` to `U'` is quasi-split over `u'`.

`U'` is the object space of the finite part `(R_s/U, e)_fin`, `g` its étale projection, `u'` the
pair `(u, Z_u)` with `Z_u` the open and closed piece of the fibre `F_u = R ×_{s, U} Spec κ(u)`
supported on the identity arrow `e(u)`, and the quasi-splitting is the universal open `Z_univ`
read inside `R|_{U'}`. -/
@[stacks 04RW "ALL FOUR ASSERTIONS, in Situation 04RV: the algebraic space U', the etale \
morphism g : U' -> U, the point u' : Spec k(u) -> U' lying over u, and that the restriction \
R|_{U'} is QUASI-SPLIT over u' -- all four PRODUCED, none assumed. The situation hypothesis is \
AlgebraicGeometry.Space.QuasiSplittingSituation, which carries the 04RV attribute. The open \
Z_u of the fibre is the one supported on the identity arrow e(u), which is open and closed and \
finite over k(u) because s is quasi-finite at e(u), the one geometric hypothesis of Tag 04RV \
beyond separatedness and local finiteness of type. Beyond Situation 04RV the only hypotheses \
are that the big fppf site contains the base, object, arrow and composable-pair schemes and \
Spec k(u), which is this library's standing ambient requirement"]
theorem exists_quasiSplit_of_quasiSplittingSituation
    (D : AlgebraicGeometry.Space.QuasiSplittingSituation.{u})
    (C : BigFppfSite.{u}) (hS : C.Contains D.S)
    (hU : C.Contains D.groupoid.objects.left)
    (hR : C.Contains D.groupoid.arrows.left)
    (hP : C.Contains (pullback D.groupoid.source D.groupoid.target).left)
    (hK : C.Contains (Spec (D.groupoid.objects.left.residueField D.u))) :
    ∃ (U' : AlgebraicSpaces C D.S hS)
      (g : U' ⟶ (D.groupoid.realization C hS hU hR hP).objects),
      IsEtale C D.S hS g.hom ∧
      ∃ v : U'.obj.obj (Opposite.op
          (schemeSiteObject C hS (X := residueOver D.groupoid D.u) hK)),
        (yonedaSchemePointEquiv C hS hU (Opposite.op
            (schemeSiteObject C hS (X := residueOver D.groupoid D.u) hK))
            (g.hom.app _ v)).left =
          D.groupoid.objects.left.fromSpecResidueField D.u ∧
        GroupoidInAlgebraicSpaces.IsQuasiSplitAt
          (GroupoidInAlgebraicSpaces.restrict (D.groupoid.realization C hS hU hR hP)
            g).groupoid
          ((residueSectionValuedPoint D.groupoid C hS D.u hK U' v).class C D.S hS U'.obj) := by
  obtain ⟨W, hWid, hWfin⟩ := D.exists_fiberOpens_identity
  exact ⟨(realizationFinitePart D.groupoid C hS hU hR hP).objects,
    (realizationFinitePart D.groupoid C hS hU hR hP).objectProjection,
    (realizationFinitePart D.groupoid C hS hU hR hP).objectProjection_etale,
    etaleLocalFibrePointOfMem D.groupoid C hS hU hR D.u hK hP
      (realizationFinitePart D.groupoid C hS hU hR hP) W
      (unitFibrePoint_mem_identity D.groupoid C hS hU hR D.u hK hP
        (realizationFinitePart D.groupoid C hS hU hR hP) W hWid) hWfin,
    lies_over_fibrePointOfMem D.groupoid C hS hU hR D.u hK hP
      (realizationFinitePart D.groupoid C hS hU hR hP) W
      (unitFibrePoint_mem_identity D.groupoid C hS hU hR D.u hK hP
        (realizationFinitePart D.groupoid C hS hU hR hP) W hWid) hWfin,
    GroupoidInAlgebraicSpaces.isQuasiSplitAt_of_openFiniteSubgroupoid _
      (realizationFinitePart D.groupoid C hS hU hR hP).restrictedSubgroupoid _⟩

end Stacks.Groupoids.GroupoidScheme

end
