module

public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedCategory.TwoOpenGlueingObjectTransport

/-!
# The two-open glueing problem of Situation 0D67 depends only on the ringed space

Let `(X, 𝒪_X)` be a ringed space and `S` a system of locally given derived objects on it, as in
Situation 0D67.  `Stacks.DerivedGlueing.TwoOpenGlueingOver` — the two-open glueing problem of
[Stacks, Tag 08DG] stated in the vocabulary of that situation — mentions only the restriction
functors of `S` and their comparisons in two steps.  This file shows that both are determined by
`X`: the comparison `restrictionComp` of *any* system is the canonical one induced by the counit
of extension by zero, so the problem for `S` reduces to the problem for the restriction datum of
`X` alone.

It also records the shape of the overlap comparison in which the glueing lemma is stated: at two
opens of a space the comparison `Stacks.Cohomology.GlueingComplexes.overlapIso` of the two
iterated derived restrictions to the intersection factors through the derived restriction to the
intersection itself.

## Main results

* `Stacks.DerivedGlueing.overlapIso_eq_restrictInclDerivedIso`: the overlap comparison of
  [Stacks, Tag 08DG] at two opens of a space is the comparison of [Stacks, Tag 0D5S] for the
  inclusion of `U ∩ V` into `U`, inverted, followed by the one for its inclusion into `V`.
* `Stacks.DerivedGlueing.restrictionIsoMapDerivedCategory_hom_app_Q`: the identification of the
  displayed restriction with the degreewise one, read at the class of a complex.
* `Stacks.DerivedGlueing.restrictionComp_eq_mapDerivedCategoryComp`: **the comparison of
  restriction in two steps of any system is the canonical one.**
* `Stacks.DerivedGlueing.twoOpenGlueingOver_of_restrictionIso`: the two-open glueing problem
  transports along an isomorphism of restriction data.
* `Stacks.DerivedGlueing.twoOpenGlueingOver_of_restrictionDatum`: **the two-open glueing problem
  of Situation 0D67 for an arbitrary system follows from the same problem for the restriction
  datum of the space.**

## References

* [Stacks Project, Tag 08DG](https://stacks.math.columbia.edu/tag/08DG)
* [Stacks Project, Tag 0D5S](https://stacks.math.columbia.edu/tag/0D5S)
* [Stacks Project, Tag 0D67](https://stacks.math.columbia.edu/tag/0D67)
* [Stacks Project, Tag 0D6A](https://stacks.math.columbia.edu/tag/0D6A)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open ExtensionByZeroModules RingedSpaceModuleAdjunction

namespace Stacks.DerivedGlueing

universe u

attribute [local instance 10000] HasDerivedCategory.standard

variable {X : RingedSpace.{u, u}}

open Stacks.Cohomology.GlueingComplexes in
/-- Transport of derived restriction along an equality of morphisms, composed on both sides. -/
theorem restrictEqIso_trans {W : RingedSpace.{u, u}} {f g k : W ⟶ X}
    (hf : f = k) (hg : g = k) :
    restrictEqIso (hf.trans hg.symm) = restrictEqIso hf ≪≫ (restrictEqIso hg).symm := by
  cases hg
  cases hf
  rfl

open Stacks.Cohomology.GlueingComplexes in
/-- **The overlap comparison of [Stacks, Tag 08DG] at two opens of a space factors through the
derived restriction to the intersection.** -/
theorem overlapIso_eq_restrictInclDerivedIso (U V : Opens X.carrier) :
    overlapIso (X.ofRestrict U.isOpenEmbedding) (X.ofRestrict V.isOpenEmbedding)
        (restrictIncl (X := X) (inf_le_left : U ⊓ V ≤ U))
        (restrictIncl (X := X) (inf_le_right : U ⊓ V ≤ V))
        (isPullback_restrictIncl U V).w =
      (restrictInclDerivedIso (X := X) (inf_le_left : U ⊓ V ≤ U)).symm ≪≫
        restrictInclDerivedIso (X := X) (inf_le_right : U ⊓ V ≤ V) := by
  have key := restrictEqIso_trans (X := X)
    (restrictIncl_comp (X := X) (inf_le_left : U ⊓ V ≤ U))
    (restrictIncl_comp (X := X) (inf_le_right : U ⊓ V ≤ V))
  refine Iso.ext ?_
  simp only [overlapIso, restrictInclDerivedIso, Iso.trans_hom, Iso.symm_hom, Iso.trans_inv,
    Iso.symm_inv, key, Category.assoc]



/-- **The identification of the displayed restriction with the degreewise one, at the class of a
complex.**  `Stacks.DerivedGlueing.restrictionIsoMapDerivedCategory` is the lift through
`DerivedCategory.Q` of the identity comparison, so on the image of `Q` it is the factorization
`restrictionFactors` of the system followed by the inverse of the factorization of the functor
induced by restriction of complexes. -/
theorem restrictionIsoMapDerivedCategory_hom_app_Q (S : LocallyGiven X) (V U : Opens X.carrier)
    (hVU : V ≤ U)
    (C : HomologicalComplex (SheafOfModules.{u} (restrictedRingSheaf X U))
      (ComplexShape.up ℤ)) :
    (restrictionIsoMapDerivedCategory S V U hVU).hom.app (DerivedCategory.Q.obj C) =
      (S.restrictionFactors V U hVU).hom.app C ≫
        (openModuleRestriction X V U hVU).mapDerivedCategoryFactors.inv.app C := by
  simp [restrictionIsoMapDerivedCategory]

/-- The cancellation used in `Stacks.DerivedGlueing.restrictionComp_eq_mapDerivedCategoryComp`:
the inverse and the hom of the factorization of the degreewise restriction functor cancel inside
the functor induced by restriction to a smaller open.  It is stated separately, and proved by
`rw` rather than by `simp`, because the two routes to the category structure of
`Stacks.DerivedGlueing.OpenDerivedCategory X V` — the ambient one and the one bound by the `let`
in the type of `Stacks.DerivedGlueing.LocallyGiven.restrictionFactors` — are definitionally equal
but not equal at the transparency at which `simp` matches, so `Category.comp_id` does not fire on
the goal. -/
private theorem mapDerivedCategory_map_factors_cancel (S : LocallyGiven X) (W V U : Opens X.carrier)
    (hWV : W ≤ V) (hVU : V ≤ U)
    (C : HomologicalComplex (SheafOfModules.{u} (restrictedRingSheaf X U))
      (ComplexShape.up ℤ)) :
    (openModuleRestriction X W V hWV).mapDerivedCategory.map
        ((S.restrictionFactors V U hVU).hom.app C ≫
          (openModuleRestriction X V U hVU).mapDerivedCategoryFactors.inv.app C) ≫
      (openModuleRestriction X W V hWV).mapDerivedCategory.map
        ((openModuleRestriction X V U hVU).mapDerivedCategoryFactors.hom.app C) =
    (openModuleRestriction X W V hWV).mapDerivedCategory.map
      ((S.restrictionFactors V U hVU).hom.app C) := by
  rw [← CategoryTheory.Functor.map_comp, Category.assoc, Iso.inv_hom_id_app, Category.comp_id]

/-- **The comparison of restriction in one and in two steps of any system of locally given
derived objects is the canonical one.**  Transported along
`Stacks.DerivedGlueing.restrictionIsoMapDerivedCategory`, the field `restrictionComp` of a
`Stacks.DerivedGlueing.LocallyGiven` becomes
`Stacks.DerivedGlueing.mapDerivedCategoryComp` at the comparison
`Stacks.DerivedGlueing.openModuleRestrictionComparison` — the counit of extension by zero on the
middle open.  So that field carries no information beyond what the ringed space already
determines.

Both sides are natural transformations out of a functor on
`Stacks.DerivedGlueing.OpenDerivedCategory X U`, so `CategoryTheory.Localization.natTrans_ext`
reduces the equality to the class of a complex, where it is the defining equation
`restrictionCompFactors` of the system against the defining equation
`Stacks.DerivedGlueing.mapDerivedCategoryComp_factors` of the canonical comparison. -/
theorem restrictionComp_eq_mapDerivedCategoryComp (S : LocallyGiven X) (W V U : Opens X.carrier)
    (hWV : W ≤ V) (hVU : V ≤ U) :
    (restrictionIsoMapDerivedCategory S W U (hWV.trans hVU)).hom ≫
        (mapDerivedCategoryComp (openModuleRestriction X V U hVU)
          (openModuleRestriction X W V hWV) (openModuleRestriction X W U (hWV.trans hVU))
          (asIso (openModuleRestrictionComparison X W V U hWV hVU))).hom =
      (S.restrictionComp W V U hWV hVU).hom ≫
        Functor.whiskerLeft (S.restriction V U hVU)
          (restrictionIsoMapDerivedCategory S W V hWV).hom ≫
        Functor.whiskerRight (restrictionIsoMapDerivedCategory S V U hVU).hom
          (openModuleRestriction X W V hWV).mapDerivedCategory := by
  refine Localization.natTrans_ext DerivedCategory.Q
    (HomologicalComplex.quasiIso (SheafOfModules.{u} (restrictedRingSheaf X U))
      (ComplexShape.up ℤ)) fun C => ?_
  have hA := mapDerivedCategoryComp_factors (openModuleRestriction X V U hVU)
    (openModuleRestriction X W V hWV) (openModuleRestriction X W U (hWV.trans hVU))
    (asIso (openModuleRestrictionComparison X W V U hWV hVU)) C
  have hB := S.restrictionCompFactors W V U hWV hVU C
  have hnat := (restrictionIsoMapDerivedCategory S W V hWV).hom.naturality
    ((S.restrictionFactors V U hVU).hom.app C)
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    restrictionIsoMapDerivedCategory_hom_app_Q, Functor.comp_obj]
  refine eq_of_comp_right_eq_of_isIso
    ((openModuleRestriction X W V hWV).mapDerivedCategory.map
        ((openModuleRestriction X V U hVU).mapDerivedCategoryFactors.hom.app C) ≫
      (openModuleRestriction X W V hWV).mapDerivedCategoryFactors.hom.app
        (((openModuleRestriction X V U hVU).mapHomologicalComplex (ComplexShape.up ℤ)).obj C) ≫
      DerivedCategory.Q.map
        ((Functor.mapHomologicalComplexCompIso
          (Iso.refl (openModuleRestriction X V U hVU ⋙ openModuleRestriction X W V hWV))
          (ComplexShape.up ℤ)).hom.app C) ≫
      DerivedCategory.Q.map
        ((NatTrans.mapHomologicalComplex
          (asIso (openModuleRestrictionComparison X W V U hWV hVU)).hom
          (ComplexShape.up ℤ)).app C))
    ((S.restrictionFactors W U (hWV.trans hVU)).hom.app C) ?_ ?_
  · simp only [Category.assoc]
    rw [hA]
    simp
  · simp only [Category.assoc]
    rw [reassoc_of% mapDerivedCategory_map_factors_cancel S W V U hWV hVU C, ← reassoc_of% hnat,
      restrictionIsoMapDerivedCategory_hom_app_Q]
    simp only [Category.assoc]
    rw [Iso.inv_hom_id_app_assoc]
    exact hB


/-- **The two-open glueing problem transports along an isomorphism of restriction data.**  If the
restriction functors of two systems are isomorphic, compatibly with their comparisons of
restriction in two steps, then a solution of the two-open glueing problem for the second is one
for the first.  Neither system's collection of opens, prescribed objects or transition
isomorphisms enter: `Stacks.DerivedGlueing.TwoOpenGlueingOver` mentions only `restriction` and
`restrictionComp`. -/
theorem twoOpenGlueingOver_of_restrictionIso (S T : LocallyGiven X)
    (t : ∀ (W O : Opens X.carrier) (hWO : W ≤ O), S.restriction W O hWO ≅ T.restriction W O hWO)
    (ht : ∀ (W V' O : Opens X.carrier) (hWV : W ≤ V') (hVO : V' ≤ O),
      (t W O (hWV.trans hVO)).hom ≫ (T.restrictionComp W V' O hWV hVO).hom =
        (S.restrictionComp W V' O hWV hVO).hom ≫
          Functor.whiskerLeft (S.restriction V' O hVO) (t W V' hWV).hom ≫
          Functor.whiskerRight (t V' O hVO).hom (T.restriction W V' hWV))
    (U V P : Opens X.carrier) (hUP : U ≤ P) (hVP : V ≤ P)
    (h : TwoOpenGlueingOver T U V P hUP hVP) :
    TwoOpenGlueingOver S U V P hUP hVP := by
  intro A B c
  obtain ⟨F, f, g, hfg⟩ := h A B
    (((t (U ⊓ V) U inf_le_left).app A).symm ≪≫ c ≪≫ ((t (U ⊓ V) V inf_le_right).app B))
  refine ⟨F, ((t U P hUP).app F) ≪≫ f, ((t V P hVP).app F) ≪≫ g, ?_⟩
  have core : ∀ (O : Opens X.carrier) (hO : U ⊓ V ≤ O) (hOP : O ≤ P)
      {Y : OpenDerivedCategory X O} (a : (T.restriction O P hOP).obj F ⟶ Y),
      ((t (U ⊓ V) P (hO.trans hOP)).app F).hom ≫
        (T.restrictionComp (U ⊓ V) O P hO hOP).hom.app F ≫ (T.restriction (U ⊓ V) O hO).map a =
      (S.restrictionComp (U ⊓ V) O P hO hOP).hom.app F ≫
        (S.restriction (U ⊓ V) O hO).map (((t O P hOP).app F).hom ≫ a) ≫
        ((t (U ⊓ V) O hO).app Y).hom := by
    intro O hO hOP Y a
    have happ := NatTrans.congr_app (ht (U ⊓ V) O P hO hOP) F
    have hn := (t (U ⊓ V) O hO).hom.naturality (((t O P hOP).app F).hom ≫ a)
    simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Functor.comp_obj, Iso.app_hom] at happ hn ⊢
    rw [← Category.assoc, happ, Category.assoc, Category.assoc, hn, Functor.map_comp]
  apply (cancel_mono (((t (U ⊓ V) V inf_le_right).app B).hom)).mp
  have hL := core U inf_le_left hUP f.hom
  have hR := core V inf_le_right hVP g.hom
  have hfg' := congrArg (((t (U ⊓ V) P (inf_le_left.trans hUP)).app F).hom ≫ ·) hfg
  simp only [Iso.trans_hom, Iso.symm_hom, Iso.app_hom, Category.assoc, Functor.map_comp]
    at hL hR hfg' ⊢
  rw [← hR, ← hfg', reassoc_of% hL]
  simp

/-- **The two-open glueing problem of Situation 0D67 does not depend on the system.**  For every
system of locally given derived objects on `X` it follows from the same problem for the
restriction datum of `X` alone — the system with no prescribed objects whose restriction functors
are those induced by restriction of complexes of sheaves of modules.

Together with `Stacks.DerivedGlueing.exists_glueing_two_opens_of_top` this says that the
compatibility clause still owed by the transport of [Stacks, Tag 08DG] into Situation 0D67 is a
statement about the ringed space `X` alone. -/
theorem twoOpenGlueingOver_of_restrictionDatum (S : LocallyGiven X) (U V P : Opens X.carrier)
    (hUP : U ≤ P) (hVP : V ≤ P)
    (h : TwoOpenGlueingOver (restrictionDatum X) U V P hUP hVP) :
    TwoOpenGlueingOver S U V P hUP hVP :=
  twoOpenGlueingOver_of_restrictionIso S (restrictionDatum X)
    (fun W O hWO => restrictionIsoMapDerivedCategory S W O hWO)
    (fun W V' O hWV hVO => restrictionComp_eq_mapDerivedCategoryComp S W V' O hWV hVO)
    U V P hUP hVP h

end Stacks.DerivedGlueing

end
