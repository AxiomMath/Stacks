module

public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.EtaleLocalizationFinitePartConstruction
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.EtaleLocalizationStabilizerMembership
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupoidSchemeDerealization
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.QuasiSplittingEtaleLocalization

/-!
# Stacks 04RW: the étale neighbourhood, the point over `u`, and the quasi-splitting

Work in the quasi-splitting situation of Stacks 04RV: a groupoid scheme `(U, R, s, t, c)` over
`S` whose source and target are separated and locally of finite type, together with a point `u`
of `U` at which the source is quasi-finite along the identity arrow `e(u)`.  Stacks 04RW asserts
the existence of an algebraic space `U'`, an étale morphism `g : U' ⟶ U` and a point
`u' : Spec κ(u) ⟶ U'` over `u` for which the restriction `R|_{U'}` is quasi-split over `u'`.

This file proves all four assertions.  `U'` is the finite part `(R_s/U, e)_fin` of Stacks 04RU
and `g` its étale projection; the quasi-splitting is the universal open `Z_univ` of Stacks 04RU
read inside `R|_{U'}`, which
`AlgebraicGeometry.GroupoidInAlgebraicSpaces.isQuasiSplitAt_of_openFiniteSubgroupoid` makes a
quasi-splitting at *every* point of `U'`.  What was missing was the point `u'`, and with it the
one place where the hypothesis of Situation 04RV is consumed.

A point of `U'` over `u` is a pair `(u, Z_u)` with `Z_u` an open of the fibre
`F_u = R ×_{s, U} Spec κ(u)` which is finite over `κ(u)` and contains the unit arrow at `u`
(Stacks 04PC, 04PE, 04RR).  In Situation 04RV the open is the smallest one possible,
`Z_u = {e(u)}`: it is open, closed and finite over `κ(u)` because `s` is quasi-finite at `e(u)`,
by `AlgebraicGeometry.exists_fiberOpens_of_finite_of_quasiFiniteAt`.

## Main definitions

* `AlgebraicGeometry.Space.etaleLocalFibrePointOfContainsSection`: **the point `u'`** of `U'`
  attached to a pair `(u, Z_u)` which contains the unit.

## Main results

* `Stacks.Groupoids.GroupoidScheme.realization_identity` and
  `Stacks.Groupoids.GroupoidScheme.unit_hom_eq_yoneda_map_identity`: **the pointwise identity of
  the realization of a groupoid scheme, and hence the unit of any finite part of it, is the
  Yoneda image of the identity `e : U ⟶ R`.**
* `AlgebraicGeometry.Space.unitArrowSite_eq` and
  `AlgebraicGeometry.Space.toScheme_map_unitArrowSite_eq`: consequently the unit arrow at `u` is
  `e(u)`.
* `AlgebraicGeometry.Space.containsSection_fibreFiniteOpenSubspace_of_mem`: a pair `(u, Z_u)`
  contains the unit as soon as the unit lands in `Z_u` pointwise.
* `AlgebraicGeometry.Space.lies_over_fibrePointOfContainsSection`: the point `u'` lies over `u`.
* `Stacks.Groupoids.GroupoidScheme.exists_etale_quasiSplitting_of_quasiSplittingSituation`:
  **Stacks 04RW**, all four assertions, in Situation 04RV.

## Implementation notes

`AlgebraicGeometry.Space.etaleLocalFibrePoint` and the chain leading to it in
`StacksFrontier/AlgebraicGeometry/Spaces/Groupoids/EtaleLocalizationSplittingExistence.lean` take
the support hypothesis `∀ x, x ∈ W ↔ t (ι x) = u` of Situation 04RL as an argument, and
`Z_u = {e(u)}` does not satisfy it: an arrow from `u` to `u` other than the identity has target
`u` and is not in `Z_u`.  A hypothesis cannot be substituted into a declaration that names it in
its type, so the last three steps of that chain are repeated here, with the support hypothesis
replaced by the containment of the unit which it is used to produce and the proofs transcribed
unchanged.  The steps before them are *not* repeated: the membership criterion
`AlgebraicGeometry.Space.exists_lift_fibreOpenPair_iff` of
`StacksFrontier/AlgebraicGeometry/Spaces/Groupoids/EtaleLocalizationStabilizerMembership.lean`
carries no hypothesis on the support of the open and gives the containment of the unit directly.

That the unit of a finite part is the Yoneda image of `e` is what Situation 04RV needs and the
other two situations do not: they characterize `Z_u` by a condition on the endpoints of an
arrow, which `AlgebraicGeometry.Space.FinitePartUniversalOpen.unit_source` and `unit_comp_target`
already give, whereas `Z_u = {e(u)}` names the identity arrow itself.  It is proved from the
uniqueness of the pointwise identity of a groupoid in functors (Stacks 06K5) together with
`Deformation.GroupoidInFunctors.identity_eq_of_idempotent`: `x ≫ e` has source and target `x`
and composes with itself to itself, by the unit axiom of the groupoid scheme.

## References

* [Stacks Project, Tag 04PC](https://stacks.math.columbia.edu/tag/04PC)
* [Stacks Project, Tag 04PE](https://stacks.math.columbia.edu/tag/04PE)
* [Stacks Project, Tag 04RK](https://stacks.math.columbia.edu/tag/04RK)
* [Stacks Project, Tag 04RR](https://stacks.math.columbia.edu/tag/04RR)
* [Stacks Project, Tag 04RU](https://stacks.math.columbia.edu/tag/04RU)
* [Stacks Project, Tag 04RV](https://stacks.math.columbia.edu/tag/04RV)
* [Stacks Project, Tag 04RW](https://stacks.math.columbia.edu/tag/04RW)
* [Stacks Project, Tag 06K5](https://stacks.math.columbia.edu/tag/06K5)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Groupoids.GroupoidScheme

open AlgebraicGeometry.Space

variable {S : Scheme.{u}} (G : GroupoidScheme S) (C : BigFppfSite.{u}) (hS : C.Contains S)
  (hU : C.Contains G.objects.left) (hR : C.Contains G.arrows.left)
  (hP : C.Contains (pullback G.source G.target).left)

/-- Regarding the identity of a scheme over `S` in the site gives the identity. -/
theorem schemeSiteMap_id {X : Over S} (hX : C.Contains X.left) :
    schemeSiteMap C hS hX hX (𝟙 X) = 𝟙 (schemeSiteObject C hS hX) := by
  apply Over.OverMorphism.ext
  rfl

/-- **The pointwise identity of the realization of a groupoid scheme is the Yoneda image of the
identity `e : U ⟶ R`.**

The arrow `x ≫ e` has source and target `x` and composes with itself to itself, by the unit
axioms of the groupoid scheme, and an idempotent arrow of a groupoid in functors with equal
source and target is the identity arrow there. -/
theorem realization_identity (T : (BigFppfOver C S hS)ᵒᵖ)
    (x : (G.realization C hS hU hR hP).toGroupoidInFunctors.Evaluation T) :
    (G.realization C hS hU hR hP).toGroupoidInFunctors.identity T x =
      (show T.unop ⟶ schemeSiteObject C hS hU from x) ≫ schemeSiteMap C hS hU hR G.identity := by
  set a : (G.realization C hS hU hR hP).toGroupoidInFunctors.arrows.obj T :=
    (show T.unop ⟶ schemeSiteObject C hS hU from x) ≫ schemeSiteMap C hS hU hR G.identity with ha
  have key : ∀ p : G.arrows ⟶ G.objects, G.identity ≫ p = 𝟙 G.objects →
      a ≫ schemeSiteMap C hS hR hU p = x := fun p hp => by
    rw [ha, Category.assoc, ← schemeSiteMap_comp, hp, schemeSiteMap_id, Category.comp_id]
  have hsrc : (G.realization C hS hU hR hP).toGroupoidInFunctors.source.app T a = x :=
    key _ G.source_identity
  have htgt : (G.realization C hS hU hR hP).toGroupoidInFunctors.target.app T a = x :=
    key _ G.target_identity
  refine Deformation.GroupoidInFunctors.identity_eq_of_idempotent _ T x a hsrc htgt ?_
  set T₀ := (siteToOver C hS).obj T.unop with hT₀
  set f : T₀ ⟶ G.arrows := yonedaSchemePointEquiv C hS hR T a with hf
  have hfa : f = yonedaSchemePointEquiv C hS hU T x ≫ G.identity := by
    rw [hf, ha]
    exact yonedaSchemePointEquiv_map C hS hU hR G.identity T x
  have key₂ : ∀ p : G.arrows ⟶ G.objects, G.identity ≫ p = 𝟙 G.objects →
      f ≫ p = yonedaSchemePointEquiv C hS hU T x := fun p hp => by
    rw [hfa, Category.assoc, hp, Category.comp_id]
  have hfs := key₂ _ G.source_identity
  have hft := key₂ _ G.target_identity
  have hfid : f ≫ G.source ≫ G.identity = f := by
    rw [← Category.assoc, hfs, ← hfa]
  have hw : f ≫ G.source = f ≫ G.target := hfs.trans hft.symm
  have hcompose : G.compose f f hw = f := by
    have key : ∀ (g : T₀ ⟶ G.arrows) (_ : g = f ≫ G.source ≫ G.identity)
        (w : f ≫ G.source = g ≫ G.target), pullback.lift f g w ≫ G.comp = f := by
      rintro g rfl w
      exact G.right_identity T₀ f w
    exact key f hfid.symm hw
  apply (yonedaSchemePointEquiv C hS hR T).injective
  refine (realizationComp_app G C hS hU hR hP T ⟨(a, a), hsrc.trans htgt.symm⟩ hw).trans ?_
  exact hcompose

variable (u : G.objects.left) (hK : C.Contains (Spec (G.objects.left.residueField u)))
  (F : FinitePartUniversalOpen (G.realization C hS hU hR hP))

/-- **The unit of a finite part of the realization is the Yoneda image of the identity
`e : U ⟶ R` of the groupoid scheme.**

The unit of a finite part is the pointwise identity of the groupoid by
`AlgebraicGeometry.Space.FinitePartUniversalOpen.unit_identity`, the Yoneda image of `e` is it
too by `Stacks.Groupoids.GroupoidScheme.realization_identity`, and the natural transformation
with that pointwise description is unique by Stacks 06K5. -/
theorem unit_hom_eq_yoneda_map_identity :
    F.unit.hom = yoneda.map (schemeSiteMap C hS hU hR G.identity) :=
  (Deformation.existsUnique_identity
      (G.realization C hS hU hR hP).toGroupoidInFunctors).unique
    (fun T x => F.unit_identity T x)
    (fun T x => (realization_identity G C hS hU hR hP T x).symm)

alias unitArrowSite_eq_identity := AlgebraicGeometry.Space.unitArrowSite_eq

alias toScheme_map_unitArrowSite_eq_identity :=
  AlgebraicGeometry.Space.toScheme_map_unitArrowSite_eq

end Stacks.Groupoids.GroupoidScheme

namespace AlgebraicGeometry.Space

open Stacks.Groupoids

variable {S : Scheme.{u}} (G : GroupoidScheme S)
  (C : BigFppfSite.{u}) (hS : C.Contains S) (hU : C.Contains G.objects.left)
  (hR : C.Contains G.arrows.left) (u : G.objects.left)
  (hK : C.Contains (Spec (G.objects.left.residueField u)))
  (hP : C.Contains (pullback G.source G.target).left)
  (F : FinitePartUniversalOpen (G.realization C hS hU hR hP))
  (W : (G.source.left.fiber u).Opens)
  (hWfin : AlgebraicGeometry.IsFinite (W.ι ≫ G.source.left.fiberToSpecResidueField u))

/-- The fibre point of the unit section, read in the fibre of the source, is the unit arrow. -/
private theorem fiberι_unitFibreSection_apply
    (y : (BigFppfOver.toScheme C S hS).obj
      (schemeSiteObject C hS (X := residueOver G u) hK)) :
    G.source.left.fiberι u ((etaleLocalFibreIso G C hS hU hR u hK).hom
      ((BigFppfOver.toScheme C S hS).map (unitFibreSection G C hS hU hR u hK hP F) y)) =
      (BigFppfOver.toScheme C S hS).map (unitArrowSite G C hS hU hR u hK hP F) y := by
  have h := congrArg (fun k => k y) (unitFibrePoint_comp_fiberι G C hS hU hR u hK hP F)
  simp only [Scheme.Hom.comp_apply] at h
  exact h

/-- **The pair `(u, Z_u)` contains the unit as soon as the unit lands in `Z_u` pointwise.**

This is `AlgebraicGeometry.Space.containsSection_fibreFiniteOpenSubspace` with the support
hypothesis of Situation 04RL replaced by the pointwise condition it is used to produce; the
membership criterion with no hypothesis on the support is
`AlgebraicGeometry.Space.exists_lift_fibreOpenPair_iff`. -/
theorem containsSection_fibreFiniteOpenSubspace_of_mem
    (hmem : ∀ y : (BigFppfOver.toScheme C S hS).obj
        (schemeSiteObject C hS (X := residueOver G u) hK),
      (etaleLocalFibreIso G C hS hU hR u hK).hom
        ((BigFppfOver.toScheme C S hS).map (unitFibreSection G C hS hU hR u hK hP F) y) ∈ W) :
    ContainsSection C S hS (G.realization C hS hU hR hP).source F.unit F.unit_source
      (fibreFiniteOpenSubspace G C hS hU hR u hK hP W hWfin) := by
  have hc : yoneda.map (𝟙 (schemeSiteObject C hS (X := residueOver G u) hK)) ≫
        (fibreFiniteOpenSubspace G C hS hU hR u hK hP W hWfin).toBase.hom =
      yoneda.map (unitArrowSite G C hS hU hR u hK hP F) ≫
        (G.realization C hS hU hR hP).source.hom :=
    (congrArg (fun z => z ≫ (fibreFiniteOpenSubspace G C hS hU hR u hK hP W hWfin).toBase.hom)
        (yoneda.map_id (schemeSiteObject C hS (X := residueOver G u) hK))).trans
      ((Category.id_comp _).trans
        ((congrArg yoneda.map
            (unitArrowSite_comp_source G C hS hU hR u hK hP F).symm).trans
          (yoneda.map_comp _ _)))
  have hpt : ∀ y : (BigFppfOver.toScheme C S hS).obj
        (schemeSiteObject C hS (X := residueOver G u) hK),
      ∃ x : G.source.left.fiber u, x ∈ W ∧
        G.source.left.fiberι u x =
          (BigFppfOver.toScheme C S hS).map (unitArrowSite G C hS hU hR u hK hP F) y := by
    intro y
    exact ⟨_, hmem y, fiberι_unitFibreSection_apply G C hS hU hR u hK hP F y⟩
  obtain ⟨n, hn⟩ :=
    (exists_lift_fibreOpenPair_iff G C hS hU hR u hK hP W hWfin
      (schemeSiteObject C hS (X := residueOver G u) hK)
      (𝟙 (schemeSiteObject C hS (X := residueOver G u) hK))
      (unitArrowSite G C hS hU hR u hK hP F) hc).2 hpt
  exact ⟨n, hn.trans (pullback_lift_congr _ _ _ _ _ _
    (yoneda.map_id (schemeSiteObject C hS (X := residueOver G u) hK))
    (yoneda_map_unitArrowSite G C hS hU hR u hK hP F))⟩

/-! ### The point of the finite part attached to a pair which contains the unit -/

variable (hcs : ContainsSection C S hS (G.realization C hS hU hR hP).source F.unit F.unit_source
  (fibreFiniteOpenSubspace G C hS hU hR u hK hP W hWfin))

include hcs in
/-- The pair `(u, Z_u)` lies in the open subspace `(R_s/U, e)_fin` cut out by containing the
unit, by Stacks 04RR.

This is `AlgebraicGeometry.Space.mem_finitePartWithSection` with the support hypothesis of
Situation 04RL replaced by the containment of the unit which that hypothesis is used to
produce. -/
theorem mem_finitePartWithSection_of_containsSection :
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
  exact hcs

include hcs in
/-- **The point `u' : Spec κ(u) ⟶ U'`.** The pair `(u, Z_u)`, read as a `Spec κ(u)`-valued point
of the object space of the finite part of the groupoid.

This is `AlgebraicGeometry.Space.etaleLocalFibrePoint` with the support hypothesis of Situation
04RL replaced by the containment of the unit. -/
def etaleLocalFibrePointOfContainsSection :
    F.objects.obj.obj (Opposite.op (schemeSiteObject C hS (X := residueOver G u) hK)) :=
  F.objectsEquiv.inv.app _
    ⟨fibrePresheafSection G C hS hU hR u hK hP W hWfin,
      mem_finitePartWithSection_of_containsSection G C hS hU hR u hK hP F W hWfin hcs⟩

include hcs in
/-- The image of that point under the projection `g : U' ⟶ U` is the canonical morphism
`Spec κ(u) ⟶ U`, read in the site. -/
theorem objectProjection_fibrePointOfContainsSection :
    F.objectProjection.hom.app
        (Opposite.op (schemeSiteObject C hS (X := residueOver G u) hK))
        (etaleLocalFibrePointOfContainsSection G C hS hU hR u hK hP F W hWfin hcs) =
      residueSiteMap G C hS hU u hK := by
  have h1 := congrArg (fun k : F.objects.obj ⟶ (G.realization C hS hU hR hP).objects.obj =>
      k.app (Opposite.op (schemeSiteObject C hS (X := residueOver G u) hK))
        (etaleLocalFibrePointOfContainsSection G C hS hU hR u hK hP F W hWfin hcs))
    F.objectProjection_spec
  have h2 : F.objectsEquiv.hom.app
      (Opposite.op (schemeSiteObject C hS (X := residueOver G u) hK))
      (etaleLocalFibrePointOfContainsSection G C hS hU hR u hK hP F W hWfin hcs) =
      ⟨fibrePresheafSection G C hS hU hR u hK hP W hWfin,
        mem_finitePartWithSection_of_containsSection G C hS hU hR u hK hP F W hWfin hcs⟩ :=
    congrArg (fun k => k.app
      (Opposite.op (schemeSiteObject C hS (X := residueOver G u) hK))
      ⟨fibrePresheafSection G C hS hU hR u hK hP W hWfin,
        mem_finitePartWithSection_of_containsSection G C hS hU hR u hK hP F W hWfin hcs⟩)
      F.objectsEquiv.inv_hom_id
  refine h1.trans ((congrArg (fun z =>
    (finiteOpenSubspacePresheaf C S hS (G.realization C hS hU hR hP).source).baseMap.app
      (Opposite.op (schemeSiteObject C hS (X := residueOver G u) hK))
      ((finitePartWithSection C S hS (G.realization C hS hU hR hP).source F.unit
        F.unit_source).toSubfunctor.ι.app
        (Opposite.op (schemeSiteObject C hS (X := residueOver G u) hK)) z)) h2).trans ?_)
  exact baseMap_fibrePresheafSection G C hS hU hR u hK hP W hWfin

include hcs in
/-- **The point `u'` lies over `u`**: its composition with the étale projection `g : U' ⟶ U` is
the canonical morphism `Spec κ(u) ⟶ U`. -/
theorem lies_over_fibrePointOfContainsSection :
    (yonedaSchemePointEquiv C hS hU
        (Opposite.op (schemeSiteObject C hS (X := residueOver G u) hK))
        (F.objectProjection.hom.app _
          (etaleLocalFibrePointOfContainsSection G C hS hU hR u hK hP F W hWfin hcs))).left =
      G.objects.left.fromSpecResidueField u := by
  rw [objectProjection_fibrePointOfContainsSection G C hS hU hR u hK hP F W hWfin hcs]
  exact congrArg Over.Hom.left (siteToOver_map_schemeSiteMap C hS
    (X := residueOver G u) (Y := G.objects) hK hU (residuePoint G u))

end AlgebraicGeometry.Space

/-! ### Stacks 04RW -/

namespace Stacks.Groupoids.GroupoidScheme

open AlgebraicGeometry.Space AlgebraicGeometry.GroupoidInAlgebraicSpaces

/-- **Stacks Project, Tag 04RW.**

In the quasi-splitting situation of Stacks 04RV there are an algebraic space `U'`, an étale
morphism `g : U' ⟶ U` of algebraic spaces and a point `u' : Spec κ(u) ⟶ U'` lying over `u` such
that the restriction `R|_{U'}` is quasi-split over `u'`.

`U'` is the finite part `(R_s/U, e)_fin` of Stacks 04RU and `g` its étale projection; `u'` is
the pair `(u, Z_u)` with `Z_u = {e(u)}`, which is an open and closed piece of the fibre
`F_u = R ×_{s, U} Spec κ(u)` finite over `κ(u)` because the source is quasi-finite at `e(u)`;
and the quasi-splitting is the universal open `Z_univ` of Stacks 04RU read inside `R|_{U'}`,
which is a quasi-splitting at every point of `U'`. -/
@[stacks 04RW]
theorem exists_etale_quasiSplitting_of_quasiSplittingSituation
    (D : AlgebraicGeometry.Space.QuasiSplittingSituation.{u})
    (C : BigFppfSite.{u}) (hS : C.Contains D.S)
    (hU : C.Contains D.groupoid.objects.left)
    (hR : C.Contains D.groupoid.arrows.left)
    (hP : C.Contains (pullback D.groupoid.source D.groupoid.target).left)
    (hK : C.Contains (Spec (D.groupoid.objects.left.residueField D.u))) :
    ∃ (U' : AlgebraicSpaces C D.S hS)
      (g : U' ⟶ (D.groupoid.realization C hS hU hR hP).objects),
      AlgebraicGeometry.Space.IsEtale C D.S hS g.hom ∧
      ∃ v : U'.obj.obj (Opposite.op
          (AlgebraicGeometry.Space.residueFieldSiteObject C hS
            (X := D.groupoid.objects) D.u hK)),
        (AlgebraicGeometry.Space.yonedaSchemePointEquiv C hS hU
            (Opposite.op (AlgebraicGeometry.Space.residueFieldSiteObject C hS
              (X := D.groupoid.objects) D.u hK))
            (g.hom.app _ v)).left =
              D.groupoid.objects.left.fromSpecResidueField D.u ∧
        IsQuasiSplitAt (restrict (D.groupoid.realization C hS hU hR hP) g).groupoid
          (AlgebraicGeometry.Space.pointsMap C D.S hS U'.obj
            (eqToHom (restrict (D.groupoid.realization C hS hU hR hP) g).objects_eq.symm).hom
            (AlgebraicGeometry.Space.FieldValuedPoint.class C D.S hS U'.obj
              { carrier := D.groupoid.objects.left.residueField D.u
                contained := hK
                toBase := D.groupoid.objects.left.fromSpecResidueField D.u ≫
                  D.groupoid.objects.hom
                value := v })) := by
  classical
  have hsrc : D.groupoid.source.left (D.groupoid.identity.left D.u) = D.u := by
    have h := congrArg (fun k : D.groupoid.objects.left ⟶ D.groupoid.objects.left => k D.u)
      (identity_left_comp_source_left D.groupoid)
    simpa using h
  obtain ⟨p₀, hp₀⟩ := exists_fiber_eq_of_source_eq D.groupoid D.u
    (D.groupoid.identity.left D.u) hsrc
  obtain ⟨W, hWset, -, hWfin⟩ :=
    AlgebraicGeometry.exists_fiberOpens_of_finite_of_quasiFiniteAt D.groupoid.source.left D.u
      {p₀} (Set.finite_singleton p₀) (fun x hx => by
        rw [Set.mem_singleton_iff] at hx
        rw [hx, hp₀]
        exact D.sourceQuasiFiniteAtIdentity.2)
  set F := realizationFinitePart D.groupoid C hS hU hR hP with hF
  have hmem : ∀ y : (BigFppfOver.toScheme C D.S hS).obj
        (schemeSiteObject C hS (X := residueOver D.groupoid D.u) hK),
      (etaleLocalFibreIso D.groupoid C hS hU hR D.u hK).hom
        ((BigFppfOver.toScheme C D.S hS).map
          (unitFibreSection D.groupoid C hS hU hR D.u hK hP F) y) ∈ W := by
    intro y
    have h := fiberι_unitFibreSection_apply D.groupoid C hS hU hR D.u hK hP F y
    have hid := congrArg (fun k => k y)
      (toScheme_map_unitArrowSite_eq D.groupoid C hS hU hR D.u hK hP F)
    simp only at hid
    have hy : D.groupoid.objects.left.fromSpecResidueField D.u y = D.u := by
      have hr : D.groupoid.objects.left.fromSpecResidueField D.u y ∈
          Set.range (D.groupoid.objects.left.fromSpecResidueField D.u) := ⟨y, rfl⟩
      rwa [Scheme.range_fromSpecResidueField, Set.mem_singleton_iff] at hr
    have hfib : D.groupoid.source.left.fiberι D.u
        ((etaleLocalFibreIso D.groupoid C hS hU hR D.u hK).hom
          ((BigFppfOver.toScheme C D.S hS).map
            (unitFibreSection D.groupoid C hS hU hR D.u hK hP F) y)) =
        D.groupoid.source.left.fiberι D.u p₀ :=
      h.trans (hid.trans
        ((congrArg (fun z => D.groupoid.identity.left z) hy).trans hp₀.symm))
    rw [← SetLike.mem_coe, hWset]
    exact Set.mem_singleton_iff.2 (injective_fiberι D.groupoid D.u hfib)
  have hcs := containsSection_fibreFiniteOpenSubspace_of_mem D.groupoid C hS hU hR D.u hK hP
    F W hWfin hmem
  refine ⟨F.objects, F.objectProjection, F.objectProjection_etale,
    etaleLocalFibrePointOfContainsSection D.groupoid C hS hU hR D.u hK hP F W hWfin hcs,
    lies_over_fibrePointOfContainsSection D.groupoid C hS hU hR D.u hK hP F W hWfin hcs, ?_⟩
  rw [pointsMap_eqToHom_restrict_objects]
  exact isQuasiSplitAt_of_openFiniteSubgroupoid _ F.restrictedSubgroupoid _

end Stacks.Groupoids.GroupoidScheme

end
