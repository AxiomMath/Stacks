module

public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedCategory.CompareIsoCanonicalSide
public import
  StacksFrontier.Topology.Sheaves.Cohomology.DerivedCategory.DerivedRestrictionDictionaryCoherence

/-!
# The coherence of the two comparisons of restriction, reduced to one counit identity

Let `(X, 𝒪_X)` be a ringed space.  The uniqueness clause of [Stacks, Tag 0D68] was reduced, in
`StacksFrontier.Topology.Sheaves.Cohomology.DerivedCategory.CompareIsoCoherence`, to the single
equation

`canonicalCompareIso K hTW hWO = overMapCompareIso K hTW`

between `Stacks.DerivedGlueing.canonicalCompareIso` and `Stacks.DerivedGlueing.overMapCompareIso`,
two comparisons of the restriction of an extension by zero: the one assembled from the
canonical comparison of restriction in two steps, and the one read off the transitivity of
restriction to a slice on the ringed site.  This file proves that equation, first granted one
identity that mentions neither the object `K` nor the open `O` —
`Stacks.DerivedGlueing.SliceCounitCoherence`, the triangle identity for
`ExtensionByZeroModules.jShriekAdjunction` read in the slice model — and then **unconditionally**,
by proving that identity.

The identity is proved in two halves.  On sheaves of modules it is
`Stacks.DerivedGlueing.sliceExtendOverIso_hom_app_over`: the comparison
`Stacks.DerivedGlueing.sliceExtendOverIso`, evaluated at the restriction to the slice over `W` of a
module on the whole space, is the restriction of the counit of extension by zero — the
right-triangle identity of the adjunction, read through the faithful passage between the two
models of modules on `W`.  Lifting it to unbounded derived categories is pure
pseudofunctoriality of `CategoryTheory.Functor.mapDerivedCategory`, proved once for arbitrary
exact functors in `Stacks.DerivedGlueing.sliceCounit_generic`.

Nothing here is a clause of a tag; everything is a step of a proof.

## Main results

* `Stacks.DerivedGlueing.sliceCompJStarIso` — the comparison identifying restriction to the slice
  over `U` followed by the open-subspace model with restriction to the open subspace, on
  unbounded derived categories.
* `Stacks.DerivedGlueing.compIso_congr_whiskerLeft` — the composition comparison of induced
  functors is natural in the second functor; stated for arbitrary exact functors.
* `Stacks.DerivedGlueing.bridge_hcan` — `Stacks.DerivedGlueing.openModuleRestrictionIsoOfExtension`
  is `Stacks.DerivedGlueing.sliceCompJStarIso` followed by the composition comparison for
  extension by zero.
* `Stacks.DerivedGlueing.star_eq` — the canonical comparison of restriction in two steps, read at
  an object, is the composition comparison once one factor of the derived counit is supplied.
* `Stacks.DerivedGlueing.SliceCounitCoherence` and
  `Stacks.DerivedGlueing.canonicalCompareIso_eq_overMapCompareIso_of_sliceCounitCoherence` — the
  remaining identity, and the equation it yields.
* `Stacks.DerivedGlueing.compIso_assoc`, `Stacks.DerivedGlueing.compIso_congr_whiskerRight`,
  `Stacks.DerivedGlueing.whiskerRight_derivedCompToId`,
  `Stacks.DerivedGlueing.mapDerivedCategoryCongr_hom_eq_derivedNatTrans` and their companions —
  the pseudofunctoriality of the passage to unbounded derived categories, for arbitrary exact
  functors.
* `Stacks.DerivedGlueing.sliceCounit_generic` — the coherence for arbitrary exact functors,
  granted the module-level identity.
* `Stacks.DerivedGlueing.sliceExtendOverIso_hom_app_over` — **the triangle identity in the slice
  model**, the only non-formal ingredient of the whole chain.
* `Stacks.DerivedGlueing.sliceCounitCoherence` — `Stacks.DerivedGlueing.SliceCounitCoherence`,
  proved.
* `Stacks.DerivedGlueing.canonicalCompareIso_eq_overMapCompareIso` — the equation the uniqueness
  clause of [Stacks, Tag 0D68] owed, with nothing granted.
* `Stacks.DerivedGlueing.restrictHomBelow_eq_restrictDerivedHom` — the coherence between the two
  restrictions of morphisms, unconditional.

## Implementation notes

The two spellings of restriction to an open — `jStar U 𝒪_X` and
`SheafOfModules.overFunctor 𝒪_X U ⋙ sliceToSubspace 𝒪_X U` — are definitionally equal, but
identifying them is affordable only at the level of *modules*.  Every identification below is
therefore carried as a `CategoryTheory.eqToIso` and never asked of the unifier at the level of
functors on derived categories; `Stacks.DerivedGlueing.eqToIso_openModuleRestriction_eq` is where
the identification is paid, componentwise.

Each step of the chase is a lemma with every category, functor, object and morphism a variable,
applied by `exact`, so that each crossing is one definitional unification at `default`
transparency.  The comparisons are taken as morphisms with their cancellations as hypotheses
rather than as `CategoryTheory.Iso`s, because instance search does not find `CategoryTheory.IsIso`
for the components of these natural isomorphisms.

## References

* [Stacks Project, Tag 0D66](https://stacks.math.columbia.edu/tag/0D66)
* [Stacks Project, Tag 0D67](https://stacks.math.columbia.edu/tag/0D67)
* [Stacks Project, Tag 0D68](https://stacks.math.columbia.edu/tag/0D68)
* [Stacks Project, Tag 00AB](https://stacks.math.columbia.edu/tag/00AB)

Tags covered: none.  Everything here is a step of a proof, not a clause of a tag statement.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open ExtensionByZeroModules RingedSpaceModuleAdjunction

namespace Stacks.DerivedGlueing

universe w₁ w₂ w₃ w₄ w₅ v₁ v₂ v₃ v₄ v₅ u₁ u₂ u₃ u₄ u₅ u

/-! ### The category algebra of the cancellation -/

/-- A functor carries a one-sided cancellation to a one-sided cancellation. -/
theorem map_comp_id {C D : Type*} [Category C] [Category D] (H : C ⥤ D) {x y : C} (p : x ⟶ y)
    (q : y ⟶ x) (h : p ≫ q = 𝟙 x) : H.map p ≫ H.map q = 𝟙 (H.obj x) := by
  rw [← H.map_comp, h, H.map_id]

/-- **The cancellation that proves the coherence, with every object and morphism a variable.**
Four invertible legs `u`, `w`, `t1` and `c` and two morphisms `v`, `s'`; the hypothesis `hstar`
says that `v` followed by the three invertible legs is `c`, and `hIII` says that `c` followed by
the tail is `v` followed by `s'` and the target.  Since `u ≫ w ≫ t1` is invertible, `hstar`
makes `v` invertible too, and the two occurrences of `v` cancel.

Stated with every object and morphism a variable, and with the inverses given as morphisms with
their cancellations rather than as `CategoryTheory.IsIso` instances, so that it applies by
`exact` at one definitional unification. -/
theorem hcan_pure {𝒞 : Type*} [Category 𝒞] {A E R1 R2 R3 R4 B V : 𝒞}
    (a1 : A ⟶ R1) (s : A ⟶ E) (s' : E ⟶ A) (hss : s ≫ s' = 𝟙 A)
    (u : E ⟶ R1) (ui : R1 ⟶ E) (hu : u ≫ ui = 𝟙 E) (ha1 : a1 = s ≫ u)
    (w : R1 ⟶ R2) (wi : R2 ⟶ R1) (hw : w ≫ wi = 𝟙 R1)
    (c3 : R2 ⟶ R4) (t1 : R2 ⟶ R3) (t1i : R3 ⟶ R2) (ht1 : t1 ≫ t1i = 𝟙 R2)
    (t2 : R3 ⟶ R4) (hc3 : c3 = t1 ≫ t2)
    (c : V ⟶ R3) (ci : R3 ⟶ V) (hc' : ci ≫ c = 𝟙 R3)
    (v : V ⟶ E) (f : R4 ⟶ B) (r : A ⟶ B)
    (hstar : (v ≫ u ≫ w) ≫ t1 = c)
    (hIII : c ≫ t2 ≫ f = v ≫ s' ≫ r) :
    a1 ≫ w ≫ c3 ≫ f = r := by
  subst ha1
  subst hc3
  have hPPi : (u ≫ w ≫ t1) ≫ t1i ≫ wi ≫ ui = 𝟙 E := by
    simp only [Category.assoc, reassoc_of% ht1, reassoc_of% hw, hu]
  have hv : v = c ≫ t1i ≫ wi ≫ ui := by
    rw [← hstar]
    simp only [Category.assoc, reassoc_of% ht1, reassoc_of% hw, hu, Category.comp_id]
  have key : (u ≫ w ≫ t1) ≫ t2 ≫ f = s' ≫ r := by
    have e1 : (u ≫ w ≫ t1) ≫ t2 ≫ f = (u ≫ w ≫ t1) ≫ (ci ≫ c) ≫ t2 ≫ f := by
      rw [hc', Category.id_comp]
    rw [e1, Category.assoc ci c (t2 ≫ f), hIII, hv]
    simp only [Category.assoc]
    rw [reassoc_of% hc']
    exact (reassoc_of% hPPi) _
  calc (s ≫ u) ≫ w ≫ (t1 ≫ t2) ≫ f = s ≫ (u ≫ w ≫ t1) ≫ t2 ≫ f := by
        simp only [Category.assoc]
    _ = s ≫ s' ≫ r := by rw [key]
    _ = r := by rw [← Category.assoc, hss, Category.id_comp]

section GenericC3

variable {C₁ : Type*} [Category C₁] [Abelian C₁] [HasDerivedCategory.{0} C₁]

/-- **The composition comparison is natural in the second functor.** -/
theorem compIso_congr_whiskerLeft {D₁ : Type*} [Category D₁] [Abelian D₁]
    [HasDerivedCategory D₁] {D₂ : Type*} [Category D₂] [Abelian D₂] [HasDerivedCategory D₂]
    {D₃ : Type*} [Category D₃] [Abelian D₃] [HasDerivedCategory D₃]
    (F : D₁ ⥤ D₂) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    {G G' : D₂ ⥤ D₃} [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [G'.Additive] [PreservesFiniteLimits G'] [PreservesFiniteColimits G']
    [(F ⋙ G).Additive] [PreservesFiniteLimits (F ⋙ G)] [PreservesFiniteColimits (F ⋙ G)]
    [(F ⋙ G').Additive] [PreservesFiniteLimits (F ⋙ G')] [PreservesFiniteColimits (F ⋙ G')]
    (α : G ≅ G') :
    mapDerivedCategoryCompIso F G ≪≫ mapDerivedCategoryCongr (Functor.isoWhiskerLeft F α) =
      Functor.isoWhiskerLeft F.mapDerivedCategory (mapDerivedCategoryCongr α) ≪≫
        mapDerivedCategoryCompIso F G' := by
  refine Iso.ext (Localization.natTrans_ext DerivedCategory.Q
    (HomologicalComplex.quasiIso D₁ (ComplexShape.up ℤ)) fun P => ?_)
  have hw : (NatIso.mapHomologicalComplex (Functor.isoWhiskerLeft F α)
        (ComplexShape.up ℤ)).hom.app P =
      (NatIso.mapHomologicalComplex α (ComplexShape.up ℤ)).hom.app
        ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj P) := by
    ext n
    simp
  have hconj := natTrans_app_eq_conj (mapDerivedCategoryCongr α).hom
    (F.mapDerivedCategoryFactors.app P)
  simp only [Iso.app_hom, Iso.app_inv, Functor.comp_obj] at hconj
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.whiskerLeft_app]
  rw [mapDerivedCategoryCompIso_hom_app_Q, mapDerivedCategoryCongr_hom_app_Q, hw, hconj,
    mapDerivedCategoryCongr_hom_app_Q, mapDerivedCategoryCompIso_hom_app_Q]
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc]
  simp

end GenericC3

section Concrete

variable {X : RingedSpace.{u, u}}

attribute [local instance 10000] HasDerivedCategory.standard

attribute [local instance] Stacks.DerivedGlueing.preservesFiniteLimitsOverMap
  Stacks.DerivedGlueing.preservesFiniteColimitsOverMap

/-- **The two spellings of restriction to `U`, on unbounded derived categories.**  Restricting a
complex to the opens contained in `U` and reading the result in the open-subspace model, each on
derived categories, is restriction to the open subspace `U` on derived categories.

The identification of the two spellings on sheaves of modules,
`Stacks.DerivedGlueing.overFunctor_comp_sliceToSubspace`, is carried as a
`CategoryTheory.eqToIso` and lifted, rather than asked of the unifier: comparing the two
spellings at the level of functors on derived categories is above the per-declaration heartbeat
ceiling. -/
def sliceCompJStarIso (U : Opens X.carrier) :
    (SheafOfModules.overFunctor.{u} (underlyingRingSheaf X) U).mapDerivedCategory ⋙
        (sliceToSubspace (underlyingRingSheaf X) U).mapDerivedCategory ≅
      (jStar U (underlyingRingSheaf X)).mapDerivedCategory :=
  mapDerivedCategoryCompIso (SheafOfModules.overFunctor.{u} (underlyingRingSheaf X) U)
      (sliceToSubspace (underlyingRingSheaf X) U) ≪≫
    mapDerivedCategoryCongr
      (eqToIso (overFunctor_comp_sliceToSubspace (underlyingRingSheaf X) U))

/-- **The chase behind `Stacks.DerivedGlueing.star_eq`**, with two arbitrary functors and every
object and morphism a variable: a coherence whose left-hand side begins with the image of an
invertible `gi`, composed with the image of its inverse `g`, is the remaining factor. -/
theorem star_pure {𝒲 𝒱 𝒯 : Type*} [Category 𝒲] [Category 𝒱] [Category 𝒯]
    (Dm : 𝒲 ⥤ 𝒱) (Em : 𝒱 ⥤ 𝒯) (DE : 𝒲 ⥤ 𝒯) {x y : 𝒲} (gi : y ⟶ x) (g : x ⟶ y)
    (hgg : gi ≫ g = 𝟙 y) (X2 : Em.obj (Dm.obj x) ⟶ DE.obj x)
    (c : Em.obj (Dm.obj y) ⟶ DE.obj y)
    (hnat : Em.map (Dm.map g) ≫ c = X2 ≫ DE.map g)
    (V : Em.obj (Dm.obj y) ⟶ DE.obj x)
    (hcoh : Em.map (Dm.map gi) ≫ X2 = V) :
    V ≫ DE.map g = c := by
  rw [← hcoh, Category.assoc, ← hnat, ← Category.assoc, ← Em.map_comp, ← Dm.map_comp, hgg,
    Dm.map_id, Em.map_id, Category.id_comp]

/-- **The canonical comparison of restriction in two steps is the composition comparison, once a
factor of the derived counit is supplied.**  For `T ≤ W ≤ O` and an object `K` over `O`, the
derived counit of extension by zero on `W`, followed by the composition comparison for
`j_{O!}` and `j_T^*`, the canonical comparison of restriction in two steps, and the inverse of
the composition comparison for `j_{O!}` and `j_W^*`, is the composition comparison for `j_{W!}`
and `j_T^*`.

This is `Stacks.DerivedGlueing.compIso_comp_coherence` for the four functors `j_{O!}`, `j_W^*`,
`j_{W!}`, `j_T^*` and the counit of `ExtensionByZeroModules.jShriekAdjunction` on `W`, read at
`K` and with one naturality square of the composition comparison. -/
theorem star_eq {O : Opens X.carrier} (K : OpenDerivedCategory X O) {T W : Opens X.carrier}
    (hTW : T ≤ W) (hWO : W ≤ O) :
    ((jStar T (underlyingRingSheaf X)).mapDerivedCategory.map
          ((derivedCompToId (jStar W (underlyingRingSheaf X))
              (jShriek W (underlyingRingSheaf X))
              (jShriekAdjunction W (underlyingRingSheaf X)).counit).app
            ((jShriek O (underlyingRingSheaf X)).mapDerivedCategory.obj K)) ≫
        (mapDerivedCategoryCompIso (jShriek O (underlyingRingSheaf X))
          (jStar T (underlyingRingSheaf X))).hom.app K ≫
        (mapDerivedCategoryComp (openModuleRestriction X W O hWO)
            (openModuleRestriction X T W hTW) (openModuleRestriction X T O (hTW.trans hWO))
            (asIso (openModuleRestrictionComparison X T W O hTW hWO))).hom.app K) ≫
        (openModuleRestriction X T W hTW).mapDerivedCategory.map
          ((mapDerivedCategoryCompIso (jShriek O (underlyingRingSheaf X))
            (jStar W (underlyingRingSheaf X))).inv.app K) =
      (mapDerivedCategoryCompIso (jShriek W (underlyingRingSheaf X))
          (jStar T (underlyingRingSheaf X))).hom.app
        ((jStar W (underlyingRingSheaf X)).mapDerivedCategory.obj
          ((jShriek O (underlyingRingSheaf X)).mapDerivedCategory.obj K)) := by
  have hcoh := NatTrans.congr_app (compIso_comp_coherence
      (jShriek O (underlyingRingSheaf X)) (jStar W (underlyingRingSheaf X))
      (jShriek W (underlyingRingSheaf X)) (jStar T (underlyingRingSheaf X))
      (jShriekAdjunction W (underlyingRingSheaf X)).counit
      (asIso (openModuleRestrictionComparison X T W O hTW hWO) :
        openModuleRestriction X W O hWO ⋙ openModuleRestriction X T W hTW ≅
          openModuleRestriction X T O (hTW.trans hWO)) rfl) K
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.comp_map, Functor.comp_obj] at hcoh
  exact star_pure (jShriek W (underlyingRingSheaf X)).mapDerivedCategory
    (jStar T (underlyingRingSheaf X)).mapDerivedCategory
    (openModuleRestriction X T W hTW).mapDerivedCategory
    ((mapDerivedCategoryCompIso (jShriek O (underlyingRingSheaf X))
      (jStar W (underlyingRingSheaf X))).hom.app K)
    ((mapDerivedCategoryCompIso (jShriek O (underlyingRingSheaf X))
      (jStar W (underlyingRingSheaf X))).inv.app K)
    ((mapDerivedCategoryCompIso (jShriek O (underlyingRingSheaf X))
      (jStar W (underlyingRingSheaf X))).hom_inv_id_app K) _ _
    ((mapDerivedCategoryCompIso (jShriek W (underlyingRingSheaf X))
      (jStar T (underlyingRingSheaf X))).hom.naturality
      ((mapDerivedCategoryCompIso (jShriek O (underlyingRingSheaf X))
        (jStar W (underlyingRingSheaf X))).inv.app K)) _ hcoh

/-- **The coherence that the comparison of the two models of restriction still owes**, with no
system of locally given derived objects and no extension by zero along the ambient open: for
every object `Y` of `D(𝒪_X)`, the comparison `Stacks.DerivedGlueing.sliceRestrictOverDerivedIso`
read at the restriction of `Y` to the slice over `W` is the derived counit of extension by zero
on `W`, transported along the two identifications of the spellings of restriction and along the
transitivity of restriction to a slice.

This is the *triangle identity for* `ExtensionByZeroModules.jShriekAdjunction` *in the slice
model*: on sheaves of modules it is the statement that
`Stacks.DerivedGlueing.sliceExtendOverIso`, evaluated at the restriction to the slice over `W` of
a module on the whole space, is the restriction of the counit, which is the right-triangle
identity of the adjunction.  It is stated here as a `Prop`, on no tagged declaration, so that the
equation it yields can be recorded before it is proved; it is proved below, as
`Stacks.DerivedGlueing.sliceCounitCoherence`, and with it
`Stacks.DerivedGlueing.canonicalCompareIso_eq_overMapCompareIso` is unconditional. -/
def SliceCounitCoherence (X : RingedSpace.{u, u}) {T W : Opens X.carrier} (hTW : T ≤ W) : Prop :=
  ∀ Y : DerivedCategory (SheafOfModules.{u} (underlyingRingSheaf X)),
    (mapDerivedCategoryCompIso (jShriek W (underlyingRingSheaf X))
              (jStar T (underlyingRingSheaf X))).hom.app
            ((jStar W (underlyingRingSheaf X)).mapDerivedCategory.obj Y) ≫
            (openModuleRestriction X T W hTW).mapDerivedCategory.map
              ((sliceCompJStarIso W).inv.app Y) ≫
            (sliceRestrictOverDerivedIso hTW).hom.app
              ((SheafOfModules.overFunctor.{u} (underlyingRingSheaf X) W).mapDerivedCategory.obj
                Y) =
          (jStar T (underlyingRingSheaf X)).mapDerivedCategory.map
              ((derivedCompToId (jStar W (underlyingRingSheaf X))
                  (jShriek W (underlyingRingSheaf X))
                  (jShriekAdjunction W (underlyingRingSheaf X)).counit).app Y) ≫
            (sliceCompJStarIso T).inv.app Y ≫
              (sliceToSubspace (underlyingRingSheaf X) T).mapDerivedCategory.map
                ((RingedSite.overMapDerivedCategoryRestrictIso
                  (Stacks.SheafOfModules.ringedSite X.sheaf) hTW.hom).inv.app Y)

/-- The transport identifying the two spellings of restriction from `O` to `U` is the one
induced by the identification of the two spellings of restriction to `U`. -/
theorem eqToIso_openModuleRestriction_eq (O U : Opens X.carrier) (hUO : U ≤ O) :
    eqToIso (openModuleRestriction_eq O U hUO) =
      Functor.isoWhiskerLeft (jShriek O (underlyingRingSheaf X))
        (eqToIso (overFunctor_comp_sliceToSubspace (underlyingRingSheaf X) U)) := by
  refine Iso.ext (NatTrans.ext (funext fun M => ?_))
  simp only [eqToIso.hom, Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, eqToHom_app]
  rfl

/-- **The restriction of an extension by zero, read through the two spellings.**  The comparison
`Stacks.DerivedGlueing.openModuleRestrictionIsoOfExtension` is
`Stacks.DerivedGlueing.sliceCompJStarIso` at the extension by zero of `K`, followed by the
composition comparison for `j_{O!}` and `j_U^*`.

This is what removes the spelling `SheafOfModules.overFunctor 𝒪_X U ⋙ sliceToSubspace 𝒪_X U`
from the left-hand side of the coherence, so that
`Stacks.DerivedGlueing.compIso_comp_coherence` — which is stated for `j_U^*` — applies. -/
theorem bridge_hcan {O U : Opens X.carrier} (hUO : U ≤ O) (K : OpenDerivedCategory X O) :
    openModuleRestrictionIsoOfExtension O U hUO K =
      (sliceCompJStarIso U).app
          ((jShriek O (underlyingRingSheaf X)).mapDerivedCategory.obj K) ≪≫
        (mapDerivedCategoryCompIso (jShriek O (underlyingRingSheaf X))
          (jStar U (underlyingRingSheaf X))).app K := by
  have key := NatTrans.congr_app (congrArg Iso.hom
    (compIso_congr_whiskerLeft (jShriek O (underlyingRingSheaf X))
      (eqToIso (overFunctor_comp_sliceToSubspace (underlyingRingSheaf X) U)))) K
  rw [← eqToIso_openModuleRestriction_eq O U hUO] at key
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.whiskerLeft_app] at key
  exact Iso.ext ((congrArg (fun x =>
      (mapDerivedCategoryCompIso (SheafOfModules.overFunctor.{u} (underlyingRingSheaf X) U)
        (sliceToSubspace (underlyingRingSheaf X) U)).hom.app
          ((jShriek O (underlyingRingSheaf X)).mapDerivedCategory.obj K) ≫ x) key).trans
    (Category.assoc _ _ _).symm)

/-- **The two comparisons of restriction agree, granted the slice-model triangle identity.**
This is the equation that the uniqueness clause of [Stacks, Tag 0D68] still owes, in the form
`Stacks.DerivedGlueing.canonicalCompareIso_eq_of_forall_Q` reduces it to; the hypothesis
`Stacks.DerivedGlueing.SliceCounitCoherence` mentions no system, no object over `O` and no
extension by zero along `O`.

The proof is three steps.  `Stacks.DerivedGlueing.bridge_hcan` rewrites both occurrences of
`Stacks.DerivedGlueing.openModuleRestrictionIsoOfExtension` as the comparison of the two
spellings of restriction followed by the composition comparison for `j_{O!}`.
`Stacks.DerivedGlueing.star_eq` — the coherence
`Stacks.DerivedGlueing.compIso_comp_coherence` for the four functors
`j_{O!}`, `j_W^*`, `j_{W!}`, `j_T^*` — identifies the canonical comparison of restriction in two
steps with the composition comparison, at the price of one factor of the derived counit.  That
factor is exactly what the hypothesis cancels, and the cancellation itself is the pure category
algebra of `Stacks.DerivedGlueing.hcan_pure`. -/
theorem canonicalCompareIso_eq_overMapCompareIso_of_sliceCounitCoherence
    {O : Opens X.carrier} (K : OpenDerivedCategory X O)
    {T W : Opens X.carrier} (hTW : T ≤ W) (hWO : W ≤ O)
    (hcoh : SliceCounitCoherence X hTW) :
    canonicalCompareIso K hTW hWO = overMapCompareIso K hTW := by
  refine Iso.ext ?_
  have hcan : (canonicalCompareIso K hTW hWO).hom =
      (openModuleRestrictionIsoOfExtension O T (hTW.trans hWO) K).hom ≫
        (mapDerivedCategoryComp (openModuleRestriction X W O hWO)
            (openModuleRestriction X T W hTW) (openModuleRestriction X T O (hTW.trans hWO))
            (asIso (openModuleRestrictionComparison X T W O hTW hWO))).hom.app K ≫
          (openModuleRestriction X T W hTW).mapDerivedCategory.map
              ((openModuleRestrictionIsoOfExtension O W hWO K).inv) ≫
            (sliceRestrictOverDerivedIso hTW).hom.app
              ((SheafOfModules.overFunctor.{u} (underlyingRingSheaf X) W).mapDerivedCategory.obj
                ((jShriek O (underlyingRingSheaf X)).mapDerivedCategory.obj K)) := rfl
  have h1 : (openModuleRestrictionIsoOfExtension O T (hTW.trans hWO) K).hom =
      (sliceCompJStarIso T).hom.app
          ((jShriek O (underlyingRingSheaf X)).mapDerivedCategory.obj K) ≫
        (mapDerivedCategoryCompIso (jShriek O (underlyingRingSheaf X))
          (jStar T (underlyingRingSheaf X))).hom.app K :=
    congrArg Iso.hom (bridge_hcan (hTW.trans hWO) K)
  have h3 : (openModuleRestrictionIsoOfExtension O W hWO K).inv =
      (mapDerivedCategoryCompIso (jShriek O (underlyingRingSheaf X))
          (jStar W (underlyingRingSheaf X))).inv.app K ≫
        (sliceCompJStarIso W).inv.app
          ((jShriek O (underlyingRingSheaf X)).mapDerivedCategory.obj K) :=
    congrArg Iso.inv (bridge_hcan hWO K)
  have e3 : (openModuleRestriction X T W hTW).mapDerivedCategory.map
        ((openModuleRestrictionIsoOfExtension O W hWO K).inv) =
      (openModuleRestriction X T W hTW).mapDerivedCategory.map
          ((mapDerivedCategoryCompIso (jShriek O (underlyingRingSheaf X))
            (jStar W (underlyingRingSheaf X))).inv.app K) ≫
        (openModuleRestriction X T W hTW).mapDerivedCategory.map
          ((sliceCompJStarIso W).inv.app
            ((jShriek O (underlyingRingSheaf X)).mapDerivedCategory.obj K)) :=
    (congrArg (openModuleRestriction X T W hTW).mapDerivedCategory.map h3).trans
      ((openModuleRestriction X T W hTW).mapDerivedCategory.map_comp _ _)
  exact hcan.trans (hcan_pure _ _ _ ((sliceCompJStarIso T).hom_inv_id_app _) _ _
    ((mapDerivedCategoryCompIso (jShriek O (underlyingRingSheaf X))
      (jStar T (underlyingRingSheaf X))).hom_inv_id_app K) h1 _ _
    ((mapDerivedCategoryComp (openModuleRestriction X W O hWO)
        (openModuleRestriction X T W hTW) (openModuleRestriction X T O (hTW.trans hWO))
        (asIso (openModuleRestrictionComparison X T W O hTW hWO))).hom_inv_id_app K)
    _ _ _ (map_comp_id (openModuleRestriction X T W hTW).mapDerivedCategory _ _
      ((mapDerivedCategoryCompIso (jShriek O (underlyingRingSheaf X))
        (jStar W (underlyingRingSheaf X))).inv_hom_id_app K)) _ e3
    _ _ ((mapDerivedCategoryCompIso (jShriek W (underlyingRingSheaf X))
      (jStar T (underlyingRingSheaf X))).inv_hom_id_app _)
    _ _ _ (star_eq K hTW hWO)
    (hcoh ((jShriek O (underlyingRingSheaf X)).mapDerivedCategory.obj K)))

end Concrete

/-! ### Pseudofunctoriality of the passage to unbounded derived categories -/

section Gen

variable {C₁ : Type u₁} [Category.{v₁} C₁] [Abelian C₁] [HasDerivedCategory.{w₁} C₁]
  {C₂ : Type u₂} [Category.{v₂} C₂] [Abelian C₂] [HasDerivedCategory.{w₂} C₂]
  {C₃ : Type u₃} [Category.{v₃} C₃] [Abelian C₃] [HasDerivedCategory.{w₃} C₃]
  {C₄ : Type u₄} [Category.{v₄} C₄] [Abelian C₄] [HasDerivedCategory.{w₄} C₄]

/-- The derived comparison induced by a natural isomorphism `e` has, as its forward morphism, the
derived transformation of `e.hom`. -/
theorem mapDerivedCategoryCongr_hom_eq_derivedNatTrans {F F' : C₁ ⥤ C₂} [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] [F'.Additive]
    [PreservesFiniteLimits F'] [PreservesFiniteColimits F'] (e : F ≅ F') :
    (mapDerivedCategoryCongr e).hom = derivedNatTrans e.hom := by
  refine Localization.natTrans_ext DerivedCategory.Q
    (HomologicalComplex.quasiIso C₁ (ComplexShape.up ℤ)) fun P => ?_
  rw [mapDerivedCategoryCongr_hom_app_Q, derivedNatTrans_app_Q]
  rfl

/-- The derived comparison induced by a composite of natural isomorphisms is the composite of the
derived comparisons. -/
theorem mapDerivedCategoryCongr_trans {F F' F'' : C₁ ⥤ C₂} [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] [F'.Additive]
    [PreservesFiniteLimits F'] [PreservesFiniteColimits F'] [F''.Additive]
    [PreservesFiniteLimits F''] [PreservesFiniteColimits F''] (e : F ≅ F') (e' : F' ≅ F'') :
    mapDerivedCategoryCongr (e ≪≫ e') =
      mapDerivedCategoryCongr e ≪≫ mapDerivedCategoryCongr e' := by
  refine Iso.ext (Localization.natTrans_ext DerivedCategory.Q
    (HomologicalComplex.quasiIso C₁ (ComplexShape.up ℤ)) fun P => ?_)
  have h : (NatIso.mapHomologicalComplex (e ≪≫ e') (ComplexShape.up ℤ)).hom.app P =
      (NatIso.mapHomologicalComplex e (ComplexShape.up ℤ)).hom.app P ≫
        (NatIso.mapHomologicalComplex e' (ComplexShape.up ℤ)).hom.app P := by
    ext n; simp
  rw [mapDerivedCategoryCongr_hom_app_Q, h, Iso.trans_hom, NatTrans.comp_app,
    mapDerivedCategoryCongr_hom_app_Q, mapDerivedCategoryCongr_hom_app_Q]
  simp

/-- The composition comparison of induced functors is natural in the first functor: for
`α : F ≅ F'` and `H`, it commutes with the derived comparisons of `α` and of `α` whiskered by
`H`. -/
theorem compIso_congr_whiskerRight {F F' : C₁ ⥤ C₂} [F.Additive] [PreservesFiniteLimits F]
    [PreservesFiniteColimits F] [F'.Additive] [PreservesFiniteLimits F']
    [PreservesFiniteColimits F'] (α : F ≅ F') (H : C₂ ⥤ C₃) [H.Additive]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H] [(F ⋙ H).Additive]
    [PreservesFiniteLimits (F ⋙ H)] [PreservesFiniteColimits (F ⋙ H)] [(F' ⋙ H).Additive]
    [PreservesFiniteLimits (F' ⋙ H)] [PreservesFiniteColimits (F' ⋙ H)] :
    mapDerivedCategoryCompIso F H ≪≫
        mapDerivedCategoryCongr (Functor.isoWhiskerRight α H) =
      Functor.isoWhiskerRight (mapDerivedCategoryCongr α) H.mapDerivedCategory ≪≫
        mapDerivedCategoryCompIso F' H := by
  refine Iso.ext (Localization.natTrans_ext DerivedCategory.Q
    (HomologicalComplex.quasiIso C₁ (ComplexShape.up ℤ)) fun P => ?_)
  have hw : (NatIso.mapHomologicalComplex (Functor.isoWhiskerRight α H)
        (ComplexShape.up ℤ)).hom.app P =
      (H.mapHomologicalComplex (ComplexShape.up ℤ)).map
        ((NatIso.mapHomologicalComplex α (ComplexShape.up ℤ)).hom.app P) := by
    ext n; simp
  have hnat := H.mapDerivedCategoryFactors.hom.naturality
    ((NatIso.mapHomologicalComplex α (ComplexShape.up ℤ)).hom.app P)
  simp only [Functor.comp_map] at hnat
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app]
  rw [← cancel_mono ((F' ⋙ H).mapDerivedCategoryFactors.hom.app P)]
  simp only [Category.assoc]
  rw [mapDerivedCategoryCongr_hom_app_Q_comp, hw,
    reassoc_of% (mapDerivedCategoryCompIso_hom_app_Q_comp F H P),
    mapDerivedCategoryCompIso_hom_app_Q_comp, ← Functor.map_comp_assoc,
    mapDerivedCategoryCongr_hom_app_Q_comp, Functor.map_comp_assoc, hnat]

/-- The composition comparisons of induced functors are associative: the two ways of comparing
`(F ⋙ G ⋙ H).mapDerivedCategory` with the composite of the three induced functors agree. -/
theorem compIso_assoc (F : C₁ ⥤ C₂) [F.Additive] [PreservesFiniteLimits F]
    [PreservesFiniteColimits F] (G : C₂ ⥤ C₃) [G.Additive] [PreservesFiniteLimits G]
    [PreservesFiniteColimits G] (H : C₃ ⥤ C₄) [H.Additive] [PreservesFiniteLimits H]
    [PreservesFiniteColimits H] [(G ⋙ H).Additive] [PreservesFiniteLimits (G ⋙ H)]
    [PreservesFiniteColimits (G ⋙ H)] [(F ⋙ G).Additive] [PreservesFiniteLimits (F ⋙ G)]
    [PreservesFiniteColimits (F ⋙ G)] [(F ⋙ G ⋙ H).Additive]
    [PreservesFiniteLimits (F ⋙ G ⋙ H)] [PreservesFiniteColimits (F ⋙ G ⋙ H)] :
    Functor.isoWhiskerLeft F.mapDerivedCategory (mapDerivedCategoryCompIso G H) ≪≫
        mapDerivedCategoryCompIso F (G ⋙ H) =
      Functor.isoWhiskerRight (mapDerivedCategoryCompIso F G) H.mapDerivedCategory ≪≫
        mapDerivedCategoryCompIso (F ⋙ G) H := by
  refine Iso.ext (Localization.natTrans_ext DerivedCategory.Q
    (HomologicalComplex.quasiIso C₁ (ComplexShape.up ℤ)) fun P => ?_)
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.whiskerLeft_app, Functor.isoWhiskerRight_hom, Functor.whiskerRight_app]
  rw [← cancel_mono ((F ⋙ G ⋙ H).mapDerivedCategoryFactors.hom.app P)]
  simp only [Category.assoc]
  have hR : H.mapDerivedCategory.map
        ((mapDerivedCategoryCompIso F G).hom.app (DerivedCategory.Q.obj P)) ≫
      (mapDerivedCategoryCompIso (F ⋙ G) H).hom.app (DerivedCategory.Q.obj P) ≫
        ((F ⋙ G) ⋙ H).mapDerivedCategoryFactors.hom.app P =
      H.mapDerivedCategory.map
          (G.mapDerivedCategory.map (F.mapDerivedCategoryFactors.hom.app P)) ≫
        H.mapDerivedCategory.map (G.mapDerivedCategoryFactors.hom.app
            ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)) ≫
          H.mapDerivedCategoryFactors.hom.app
            ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj
              ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)) := by
    rw [mapDerivedCategoryCompIso_hom_app_Q_comp, ← Functor.map_comp_assoc,
      mapDerivedCategoryCompIso_hom_app_Q_comp, Functor.map_comp_assoc]
    exact rfl
  rw [mapDerivedCategoryCompIso_chain F G H P]
  exact hR.symm

/-- The derived form of `η : b ⋙ d ⟶ 𝟭 C₁`, whiskered on the right by the induced functor of `e`,
is the derived transformation of `θ = Functor.whiskerRight η e`, conjugated by the composition
comparisons. -/
theorem whiskerRight_derivedCompToId (b : C₁ ⥤ C₂) [b.Additive] [PreservesFiniteLimits b]
    [PreservesFiniteColimits b] (d : C₂ ⥤ C₁) [d.Additive] [PreservesFiniteLimits d]
    [PreservesFiniteColimits d] (e : C₁ ⥤ C₃) [e.Additive] [PreservesFiniteLimits e]
    [PreservesFiniteColimits e] [(b ⋙ d).Additive] [PreservesFiniteLimits (b ⋙ d)]
    [PreservesFiniteColimits (b ⋙ d)] [(d ⋙ e).Additive] [PreservesFiniteLimits (d ⋙ e)]
    [PreservesFiniteColimits (d ⋙ e)] [(b ⋙ d ⋙ e).Additive]
    [PreservesFiniteLimits (b ⋙ d ⋙ e)] [PreservesFiniteColimits (b ⋙ d ⋙ e)]
    (η : b ⋙ d ⟶ 𝟭 C₁) (θ : b ⋙ d ⋙ e ⟶ e)
    (hθ : θ = Functor.whiskerRight η e) :
    Functor.whiskerRight (derivedCompToId b d η) e.mapDerivedCategory =
      Functor.whiskerLeft b.mapDerivedCategory (mapDerivedCategoryCompIso d e).hom ≫
        (mapDerivedCategoryCompIso b (d ⋙ e)).hom ≫ derivedNatTrans θ := by
  refine Localization.natTrans_ext DerivedCategory.Q
    (HomologicalComplex.quasiIso C₁ (ComplexShape.up ℤ)) fun P => ?_
  have hdg : (e.mapHomologicalComplex (ComplexShape.up ℤ)).map
        ((NatTrans.mapHomologicalComplex η (ComplexShape.up ℤ)).app P ≫
          (Functor.mapHomologicalComplexIdIso C₁ (ComplexShape.up ℤ)).hom.app P) =
      (NatTrans.mapHomologicalComplex θ (ComplexShape.up ℤ)).app P := by
    ext n; simp [hθ]
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app]
  rw [derivedCompToId_app_Q, Functor.map_comp, Functor.map_comp,
    mapDerivedCategoryFactors_conj e
      ((NatTrans.mapHomologicalComplex η (ComplexShape.up ℤ)).app P ≫
        (Functor.mapHomologicalComplexIdIso C₁ (ComplexShape.up ℤ)).hom.app P),
    hdg, derivedNatTrans_app_Q,
    reassoc_of% (mapDerivedCategoryCompIso_chain b d e P)]
  exact rfl

/-- `Stacks.DerivedCategoryComparisons.mapDerivedCategoryCompIso` is the inverse of the
composition comparison `mapDerivedCategoryCompIso`. -/
theorem dcc_compIso_eq (F : C₁ ⥤ C₂) [F.Additive] [PreservesFiniteLimits F]
    [PreservesFiniteColimits F] (G : C₂ ⥤ C₃) [G.Additive] [PreservesFiniteLimits G]
    [PreservesFiniteColimits G] [(F ⋙ G).Additive] [PreservesFiniteLimits (F ⋙ G)]
    [PreservesFiniteColimits (F ⋙ G)] :
    Stacks.DerivedCategoryComparisons.mapDerivedCategoryCompIso F G =
      (mapDerivedCategoryCompIso F G).symm := by
  refine Iso.ext (Localization.natTrans_ext DerivedCategory.Q
    (HomologicalComplex.quasiIso C₁ (ComplexShape.up ℤ)) fun P => ?_)
  rw [Stacks.DerivedCategoryComparisons.mapDerivedCategoryCompIso_hom_app_Q,
    Iso.symm_hom, mapDerivedCategoryCompIso_inv_app_Q]

/-- `Stacks.DerivedCategoryComparisons.mapDerivedCategoryIsoOfNatIso` is the comparison
`mapDerivedCategoryCongr`. -/
theorem dcc_congr_eq {F F' : C₁ ⥤ C₂} [F.Additive] [PreservesFiniteLimits F]
    [PreservesFiniteColimits F] [F'.Additive] [PreservesFiniteLimits F']
    [PreservesFiniteColimits F'] (e : F ≅ F') :
    Stacks.DerivedCategoryComparisons.mapDerivedCategoryIsoOfNatIso F F' e =
      mapDerivedCategoryCongr e :=
  rfl

/-! ### Rearrangements of an equality of composite isomorphisms -/

/-- If `X ≪≫ Y = Z ≪≫ W`, then `Z.inv ≫ X.hom = W.hom ≫ Y.inv`. -/
theorem iso_rearrange {C : Type*} [Category C] {a b c d : C} {X : a ≅ b} {Y : b ≅ d} {Z : a ≅ c}
    {W : c ≅ d} (h : X ≪≫ Y = Z ≪≫ W) : Z.inv ≫ X.hom = W.hom ≫ Y.inv := by
  rw [Iso.inv_comp_eq, ← Category.assoc, Iso.eq_comp_inv]
  exact congrArg Iso.hom h

/-- If `X ≪≫ Y = Z ≪≫ W`, then `X.inv = Y.hom ≫ W.inv ≫ Z.inv`. -/
theorem iso_rearrange_inv {C : Type*} [Category C] {a b c d : C} {X : a ≅ b} {Y : b ≅ d}
    {Z : a ≅ c} {W : c ≅ d} (h : X ≪≫ Y = Z ≪≫ W) : X.inv = Y.hom ≫ W.inv ≫ Z.inv := by
  rw [← Iso.inv_comp_eq]
  exact congrArg Iso.inv h

/-- If `X ≪≫ Y = Z ≪≫ W`, then `Z.hom = X.hom ≫ Y.hom ≫ W.inv`. -/
theorem iso_rearrange_hom {C : Type*} [Category C] {a b c d : C} {X : a ≅ b} {Y : b ≅ d}
    {Z : a ≅ c} {W : c ≅ d} (h : X ≪≫ Y = Z ≪≫ W) : Z.hom = X.hom ≫ Y.hom ≫ W.inv := by
  rw [← Category.assoc, Iso.eq_comp_inv]
  exact (congrArg Iso.hom h).symm

/-- If `X ≪≫ Y = Z ≪≫ W`, then `W.inv ≫ Z.inv = Y.inv ≫ X.inv`. -/
theorem iso_rearrange_inv_inv {C : Type*} [Category C] {a b c d : C} {X : a ≅ b} {Y : b ≅ d}
    {Z : a ≅ c} {W : c ≅ d} (h : X ≪≫ Y = Z ≪≫ W) : W.inv ≫ Z.inv = Y.inv ≫ X.inv :=
  (congrArg Iso.inv h).symm

/-- The derived comparison induced by a natural isomorphism `e` has, as its inverse, the derived
transformation of `e.inv`. -/
theorem mapDerivedCategoryCongr_inv_eq_derivedNatTrans {F F' : C₁ ⥤ C₂} [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] [F'.Additive]
    [PreservesFiniteLimits F'] [PreservesFiniteColimits F'] (e : F ≅ F') :
    (mapDerivedCategoryCongr e).inv = derivedNatTrans e.inv := by
  refine Localization.natTrans_ext DerivedCategory.Q
    (HomologicalComplex.quasiIso C₁ (ComplexShape.up ℤ)) fun P => ?_
  rw [mapDerivedCategoryCongr_inv_app_Q, derivedNatTrans_app_Q]
  rfl

/-- The derived form of a composite of natural transformations is the composite of the derived
forms. -/
theorem derivedNatTrans_comp {F F' F'' : C₁ ⥤ C₂} [F.Additive] [PreservesFiniteLimits F]
    [PreservesFiniteColimits F] [F'.Additive] [PreservesFiniteLimits F']
    [PreservesFiniteColimits F'] [F''.Additive] [PreservesFiniteLimits F'']
    [PreservesFiniteColimits F''] (ν : F ⟶ F') (ν' : F' ⟶ F'') :
    derivedNatTrans (ν ≫ ν') = derivedNatTrans ν ≫ derivedNatTrans ν' := by
  refine Localization.natTrans_ext DerivedCategory.Q
    (HomologicalComplex.quasiIso C₁ (ComplexShape.up ℤ)) fun P => ?_
  have h : (NatTrans.mapHomologicalComplex (ν ≫ ν') (ComplexShape.up ℤ)).app P =
      (NatTrans.mapHomologicalComplex ν (ComplexShape.up ℤ)).app P ≫
        (NatTrans.mapHomologicalComplex ν' (ComplexShape.up ℤ)).app P := by
    ext n; simp
  rw [derivedNatTrans_app_Q, h, NatTrans.comp_app, derivedNatTrans_app_Q, derivedNatTrans_app_Q]
  simp


/-- A transport cancelled against its inverse, with the intermediate object spelled
differently. -/
theorem eqToHom_comp_cancel {C : Type*} [Category C] {a b d : C} (h₁ : a = b) (h₂ : b = a)
    (g : a ⟶ d) : eqToHom h₁ ≫ eqToHom h₂ ≫ g = g := by
  subst h₁; simp

/-- The inverse of a transport of functors, at an object. -/
theorem eqToIso_inv_app {C : Type*} [Category C] {D : Type*} [Category D] {F G : C ⥤ D}
    (h : F = G) (M : C) :
    (eqToIso h).inv.app M = eqToHom (Functor.congr_obj h M).symm := by
  subst h; simp

/-- A transport of functors followed by a comparison, at an object, once the comparison's value
there is known.  Stated with every object and morphism a variable, so that it applies by `exact`
at one definitional unification. -/
theorem eqToIso_trans_hom_app_eq {C : Type*} [Category C] {D : Type*} [Category D]
    {F G H : C ⥤ D} (h : F = G) (β : G ≅ H) (M : C) {Zt : D} {f : Zt ⟶ H.obj M}
    {p : G.obj M = Zt} (hβ : β.hom.app M = eqToHom p ≫ f) (q : F.obj M = Zt) :
    (eqToIso h ≪≫ β).hom.app M = eqToHom q ≫ f := by
  subst h
  rw [Iso.trans_hom, NatTrans.comp_app, eqToIso.hom, eqToHom_app, hβ, ← Category.assoc,
    eqToHom_trans]

end Gen

section Main

attribute [local instance] CategoryTheory.Limits.comp_preservesFiniteLimits
  CategoryTheory.Limits.comp_preservesFiniteColimits

/-- **The slice counit coherence for arbitrary exact functors.**  Given exact functors with
`oW ⋙ sW = jsW` and `oT ⋙ sT = jsT`, natural isomorphisms `rho` and `phi`, and a transformation
`eta : jsW ⋙ jshW ⟶ 𝟭 A` whose whiskering `theta` satisfies the module-level identity `hM`, the
corresponding identity holds between the induced functors on unbounded derived categories, with
`eta` replaced by its derived form `Stacks.DerivedGlueing.derivedCompToId`. -/
theorem sliceCounit_generic
    {A : Type u₁} [Category.{v₁} A] [Abelian A] [HasDerivedCategory.{w₁} A]
    {SL : Type u₂} [Category.{v₂} SL] [Abelian SL] [HasDerivedCategory.{w₂} SL]
    {SB : Type u₃} [Category.{v₃} SB] [Abelian SB] [HasDerivedCategory.{w₃} SB]
    {TL : Type u₄} [Category.{v₄} TL] [Abelian TL] [HasDerivedCategory.{w₄} TL]
    {TB : Type u₅} [Category.{v₅} TB] [Abelian TB] [HasDerivedCategory.{w₅} TB]
    (oW : A ⥤ SL) [oW.Additive] [PreservesFiniteLimits oW] [PreservesFiniteColimits oW]
    (sW : SL ⥤ SB) [sW.Additive] [PreservesFiniteLimits sW] [PreservesFiniteColimits sW]
    (jsW : A ⥤ SB) [jsW.Additive] [PreservesFiniteLimits jsW] [PreservesFiniteColimits jsW]
    (jshW : SB ⥤ A) [jshW.Additive] [PreservesFiniteLimits jshW] [PreservesFiniteColimits jshW]
    (m : SL ⥤ TL) [m.Additive] [PreservesFiniteLimits m] [PreservesFiniteColimits m]
    (sT : TL ⥤ TB) [sT.Additive] [PreservesFiniteLimits sT] [PreservesFiniteColimits sT]
    (oT : A ⥤ TL) [oT.Additive] [PreservesFiniteLimits oT] [PreservesFiniteColimits oT]
    (jsT : A ⥤ TB) [jsT.Additive] [PreservesFiniteLimits jsT] [PreservesFiniteColimits jsT]
    (hW : oW ⋙ sW = jsW) (hT : oT ⋙ sT = jsT)
    (rho : sW ⋙ jshW ⋙ jsT ≅ m ⋙ sT) (phi : oW ⋙ m ≅ oT)
    (eta : jsW ⋙ jshW ⟶ 𝟭 A) (theta : jsW ⋙ jshW ⋙ jsT ⟶ jsT)
    (htheta : theta = Functor.whiskerRight eta jsT)
    (hM : Functor.whiskerRight (eqToIso hW).inv (jshW ⋙ jsT) ≫ Functor.whiskerLeft oW rho.hom =
      theta ≫ (eqToIso hT).inv ≫ Functor.whiskerRight phi.inv sT) :
    Functor.whiskerLeft jsW.mapDerivedCategory (mapDerivedCategoryCompIso jshW jsT).hom ≫
        Functor.whiskerRight
            (mapDerivedCategoryCompIso oW sW ≪≫ mapDerivedCategoryCongr (eqToIso hW)).inv
            (jshW ⋙ jsT).mapDerivedCategory ≫
          Functor.whiskerLeft oW.mapDerivedCategory
            (mapDerivedCategoryCompIso sW (jshW ⋙ jsT) ≪≫ mapDerivedCategoryCongr rho ≪≫
              (mapDerivedCategoryCompIso m sT).symm).hom =
      Functor.whiskerRight (derivedCompToId jsW jshW eta) jsT.mapDerivedCategory ≫
        (mapDerivedCategoryCompIso oT sT ≪≫ mapDerivedCategoryCongr (eqToIso hT)).inv ≫
          Functor.whiskerRight
            ((Stacks.DerivedCategoryComparisons.mapDerivedCategoryCompIso oW m).symm ≪≫
              Stacks.DerivedCategoryComparisons.mapDerivedCategoryIsoOfNatIso (oW ⋙ m) oT
                phi).inv
            sT.mapDerivedCategory := by
  rw [dcc_compIso_eq, dcc_congr_eq, Iso.symm_symm_eq]
  have hA := iso_rearrange (compIso_assoc oW sW (jshW ⋙ jsT))
  have hB := iso_rearrange_hom (compIso_congr_whiskerLeft oW rho)
  have hC := iso_rearrange_inv (compIso_assoc oW m sT)
  have hD := iso_rearrange (compIso_congr_whiskerRight (eqToIso hW) (jshW ⋙ jsT))
  have hE := iso_rearrange_inv_inv (compIso_congr_whiskerRight phi sT)
  have hF := whiskerRight_derivedCompToId jsW jshW jsT eta theta htheta
  have hFin : (mapDerivedCategoryCongr
          (Functor.isoWhiskerRight (eqToIso hW) (jshW ⋙ jsT))).inv ≫
        (mapDerivedCategoryCongr (Functor.isoWhiskerLeft oW rho)).hom =
      derivedNatTrans theta ≫ (mapDerivedCategoryCongr (eqToIso hT)).inv ≫
        (mapDerivedCategoryCongr (Functor.isoWhiskerRight phi sT)).inv := by
    rw [mapDerivedCategoryCongr_inv_eq_derivedNatTrans,
      mapDerivedCategoryCongr_hom_eq_derivedNatTrans,
      mapDerivedCategoryCongr_inv_eq_derivedNatTrans,
      mapDerivedCategoryCongr_inv_eq_derivedNatTrans,
      ← derivedNatTrans_comp, ← derivedNatTrans_comp, ← derivedNatTrans_comp]
    exact congrArg derivedNatTrans hM
  simp only [Functor.isoWhiskerLeft_hom, Functor.isoWhiskerLeft_inv,
    Functor.isoWhiskerRight_inv] at hA hB hC hD hE
  simp only [Iso.trans_inv, Iso.trans_hom, Iso.symm_hom, Functor.whiskerRight_comp,
    Functor.whiskerLeft_comp, Category.assoc]
  rw [hB, hC, reassoc_of% hA, reassoc_of% hD, hF, reassoc_of% hE]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [reassoc_of% hFin]

end Main


/-! ### The triangle identity for extension by zero, read in the slice model -/

section SliceTriangle

variable {Z : TopCat.{u}} (O : Sheaf (Opens.grothendieckTopology Z) RingCat.{u})

/-- **The restriction of the counit is a two-sided inverse of the unit.**  The unit of
`ExtensionByZeroModules.jShriekAdjunction` is invertible, so the right-triangle identity, which
exhibits the restriction of the counit as a right inverse of the unit at a restricted module,
exhibits it as a left inverse too. -/
theorem map_counit_comp_unit (U : Opens Z) (A : SheafOfModules.{u} O) :
    (jStar U O).map ((jShriekAdjunction U O).counit.app A) ≫
        (jShriekAdjunction U O).unit.app ((jStar U O).obj A) =
      𝟙 ((jStar U O ⋙ jShriek U O ⋙ jStar U O).obj A) := by
  have := isIso_jShriekAdjunction_unit U O
  rw [← IsIso.inv_eq_of_hom_inv_id
    ((jShriekAdjunction U O).right_triangle_components (Y := A))]
  exact IsIso.inv_hom_id _

/-- The two spellings of the restriction of a module to `U`, carried under extension by zero and
restriction to the opens contained in `U`.  This is
`Stacks.DerivedGlueing.overFunctor_comp_sliceToSubspace` read at an object, never the composite
`rfl`. -/
theorem overFunctor_jShriek_obj_eq (U : Opens Z) (A : SheafOfModules.{u} O) :
    (SheafOfModules.overFunctor.{u} O U).obj
        ((jShriek U O).obj ((SheafOfModules.overFunctor.{u} O U ⋙ sliceToSubspace O U).obj A)) =
      (SheafOfModules.overFunctor.{u} O U).obj ((jShriek U O).obj ((jStar U O).obj A)) :=
  congrArg (fun M => (SheafOfModules.overFunctor.{u} O U).obj ((jShriek U O).obj M))
    (Functor.congr_obj (overFunctor_comp_sliceToSubspace O U) A)

/-- **The triangle identity for `ExtensionByZeroModules.jShriekAdjunction` in the slice model.**
The comparison `Stacks.DerivedGlueing.sliceExtendOverIso`, evaluated at the restriction to the
slice over `U` of a module on the whole space, is the restriction of the counit of extension by
zero.

The passage between the two models of modules on `U` is faithful, so it is enough to check the
identity after applying it; there
`Stacks.DerivedGlueing.sliceToSubspace_map_sliceExtendOverIso_hom_app` turns the left-hand side
into the inverse of the unit, and `Stacks.DerivedGlueing.map_counit_comp_unit` is the
right-triangle identity. -/
theorem sliceExtendOverIso_hom_app_over (U : Opens Z) (A : SheafOfModules.{u} O) :
    (sliceExtendOverIso O U).hom.app ((SheafOfModules.overFunctor.{u} O U).obj A) =
      eqToHom (overFunctor_jShriek_obj_eq O U A) ≫
        (SheafOfModules.overFunctor.{u} O U).map ((jShriekAdjunction U O).counit.app A) := by
  have := sliceToSubspace_faithful O U
  refine (sliceToSubspace O U).map_injective ?_
  rw [sliceToSubspace_map_sliceExtendOverIso_hom_app]
  simp only [sliceExtendOverCompIso, Iso.trans_hom, NatTrans.comp_app, eqToIso.hom, eqToHom_app,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, Iso.symm_hom, asIso_inv,
    Functor.map_comp, eqToHom_map]
  rw [← Functor.comp_map (SheafOfModules.overFunctor.{u} O U) (sliceToSubspace O U),
    Functor.congr_hom (overFunctor_comp_sliceToSubspace O U)
      ((jShriekAdjunction U O).counit.app A), NatIso.isIso_inv_app, IsIso.comp_inv_eq]
  simp only [Category.assoc]
  have hnat := (jShriekAdjunction U O).unit.naturality
      (eqToHom (Functor.congr_obj (overFunctor_comp_sliceToSubspace O U) A).symm)
  simp only [Functor.id_map, eqToHom_map, Functor.comp_obj] at hnat
  rw [hnat, ← Category.assoc ((jStar U O).map _), map_counit_comp_unit]
  simp

end SliceTriangle

/-! ### The coherence, proved -/

section Closing

variable {X : RingedSpace.{u, u}}

attribute [local instance 10000] HasDerivedCategory.standard

attribute [local instance] CategoryTheory.Limits.comp_preservesFiniteLimits
  CategoryTheory.Limits.comp_preservesFiniteColimits

attribute [local instance] Stacks.DerivedGlueing.preservesFiniteLimitsOverMap
  Stacks.DerivedGlueing.preservesFiniteColimitsOverMap

/-- **The source of the slice comparison at a restricted module, spelled through `jStar`.**  This
is `Stacks.DerivedGlueing.sliceRestrict_source_eq` with the composite `j_{W!} ⋙ j_T^*` in place of
`Stacks.DerivedGlueing.openModuleRestriction`: the spelling in which the identification is carried
below, so that no statement mixes the two names for restriction in two steps. -/
theorem slice_jShriek_jStar_source_eq {T W : Opens X.carrier}
    (N : SheafOfModules.{u} (underlyingRingSheaf X)) :
    (sliceToSubspace (underlyingRingSheaf X) W ⋙
        jShriek W (underlyingRingSheaf X) ⋙ jStar T (underlyingRingSheaf X)).obj
          ((SheafOfModules.overFunctor.{u} (underlyingRingSheaf X) W).obj N) =
      (jStar T (underlyingRingSheaf X)).obj
        ((jShriek W (underlyingRingSheaf X)).obj ((jStar W (underlyingRingSheaf X)).obj N)) :=
  congrArg (fun M => (jStar T (underlyingRingSheaf X)).obj
      ((jShriek W (underlyingRingSheaf X)).obj M))
    (Functor.congr_obj (overFunctor_comp_sliceToSubspace (underlyingRingSheaf X) W) N)

/-- **The module-level identity the coherence rests on.**  The comparison of the two models of
restriction from `W` to `T`, whiskered by restriction to the opens below `W`, is the counit of
extension by zero on `W` restricted to `T`, carried between the two spellings of restriction.

This is `Stacks.DerivedGlueing.sliceExtendOverIso_hom_app_over` — the triangle identity — together
with the identifications of the two spellings recorded in
`StacksFrontier/Topology/Sheaves/Cohomology/DerivedCategory/CompareIsoCanonicalSide.lean`.  Nothing
about derived categories is involved. -/
theorem whiskerLeft_sliceRestrictOverIso {T W : Opens X.carrier} (hTW : T ≤ W) :
    Functor.whiskerRight
          (eqToIso (overFunctor_comp_sliceToSubspace (underlyingRingSheaf X) W)).inv
          (jShriek W (underlyingRingSheaf X) ⋙ jStar T (underlyingRingSheaf X)) ≫
        Functor.whiskerLeft (SheafOfModules.overFunctor.{u} (underlyingRingSheaf X) W)
          (eqToIso (slice_comp_jShriek_jStar_eq (underlyingRingSheaf X) hTW).symm ≪≫
            sliceRestrictOverIso (underlyingRingSheaf X) hTW).hom =
      Functor.whiskerRight (jShriekAdjunction W (underlyingRingSheaf X)).counit
          (jStar T (underlyingRingSheaf X)) ≫
        (eqToIso (overFunctor_comp_sliceToSubspace (underlyingRingSheaf X) T)).inv ≫
          Functor.whiskerRight
            (SheafOfModules.overFunctorMap.{u} (underlyingRingSheaf X) hTW.hom).inv
            (sliceToSubspace (underlyingRingSheaf X) T) := by
  refine NatTrans.ext (funext fun N => ?_)
  have hβ : (sliceRestrictOverIso (underlyingRingSheaf X) hTW).hom.app
        ((SheafOfModules.overFunctor.{u} (underlyingRingSheaf X) W).obj N) =
      eqToHom ((Functor.congr_obj
            (slice_comp_jShriek_jStar_eq (underlyingRingSheaf X) hTW).symm
            ((SheafOfModules.overFunctor.{u} (underlyingRingSheaf X) W).obj N)).symm.trans
          (slice_jShriek_jStar_source_eq (T := T) (W := W) N)) ≫
        (jStar T (underlyingRingSheaf X)).map
            ((jShriekAdjunction W (underlyingRingSheaf X)).counit.app N) ≫
          eqToHom (jStar_obj_eq_overMap_obj hTW N) := by
    rw [sliceRestrictOverIso_hom_app, sliceExtendOverIso_hom_app_over, Functor.map_comp,
      eqToHom_map, overMap_sliceToSubspace_map_overFunctor_map]
    simp
  have key := eqToIso_trans_hom_app_eq
    (slice_comp_jShriek_jStar_eq (underlyingRingSheaf X) hTW).symm
    (sliceRestrictOverIso (underlyingRingSheaf X) hTW)
    ((SheafOfModules.overFunctor.{u} (underlyingRingSheaf X) W).obj N) hβ
    (slice_jShriek_jStar_source_eq (T := T) (W := W) N)
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    eqToIso_inv_app, eqToHom_map]
  rw [key, show (sliceToSubspace (underlyingRingSheaf X) T).map
        ((SheafOfModules.overFunctorMap.{u} (underlyingRingSheaf X) hTW.hom).inv.app N) =
      eqToHom (congrArg (sliceToSubspace (underlyingRingSheaf X) T).obj
        (Functor.congr_obj (overFunctor_comp_overMap (underlyingRingSheaf X) hTW) N).symm)
      from rfl, eqToHom_comp_cancel]
  simp

/-- The left-hand side of `Stacks.DerivedGlueing.SliceCounitCoherence`, as a natural
transformation and in the spelling `Stacks.DerivedGlueing.sliceCounit_generic` consumes. -/
def sliceCounitLeft (X : RingedSpace.{u, u}) {T W : Opens X.carrier} (hTW : T ≤ W) :
    (jStar W (underlyingRingSheaf X)).mapDerivedCategory ⋙
        ((jShriek W (underlyingRingSheaf X)).mapDerivedCategory ⋙
          (jStar T (underlyingRingSheaf X)).mapDerivedCategory) ⟶
      (SheafOfModules.overFunctor.{u} (underlyingRingSheaf X) W).mapDerivedCategory ⋙
        ((SheafOfModules.overMap.{u} (underlyingRingSheaf X) hTW.hom).mapDerivedCategory ⋙
          (sliceToSubspace (underlyingRingSheaf X) T).mapDerivedCategory) :=
  Functor.whiskerLeft (jStar W (underlyingRingSheaf X)).mapDerivedCategory
      (mapDerivedCategoryCompIso (jShriek W (underlyingRingSheaf X))
        (jStar T (underlyingRingSheaf X))).hom ≫
    Functor.whiskerRight
        (mapDerivedCategoryCompIso (SheafOfModules.overFunctor.{u} (underlyingRingSheaf X) W)
            (sliceToSubspace (underlyingRingSheaf X) W) ≪≫
          mapDerivedCategoryCongr
            (eqToIso (overFunctor_comp_sliceToSubspace (underlyingRingSheaf X) W))).inv
        (jShriek W (underlyingRingSheaf X) ⋙
          jStar T (underlyingRingSheaf X)).mapDerivedCategory ≫
      Functor.whiskerLeft
        (SheafOfModules.overFunctor.{u} (underlyingRingSheaf X) W).mapDerivedCategory
        (mapDerivedCategoryCompIso (sliceToSubspace (underlyingRingSheaf X) W)
              (jShriek W (underlyingRingSheaf X) ⋙ jStar T (underlyingRingSheaf X)) ≪≫
            mapDerivedCategoryCongr
                (eqToIso (slice_comp_jShriek_jStar_eq (underlyingRingSheaf X) hTW).symm ≪≫
                  sliceRestrictOverIso (underlyingRingSheaf X) hTW) ≪≫
              (mapDerivedCategoryCompIso
                (SheafOfModules.overMap.{u} (underlyingRingSheaf X) hTW.hom)
                (sliceToSubspace (underlyingRingSheaf X) T)).symm).hom

/-- The right-hand side of `Stacks.DerivedGlueing.SliceCounitCoherence`, as a natural
transformation and in the spelling `Stacks.DerivedGlueing.sliceCounit_generic` consumes. -/
def sliceCounitRight (X : RingedSpace.{u, u}) {T W : Opens X.carrier} (hTW : T ≤ W) :
    (jStar W (underlyingRingSheaf X)).mapDerivedCategory ⋙
        ((jShriek W (underlyingRingSheaf X)).mapDerivedCategory ⋙
          (jStar T (underlyingRingSheaf X)).mapDerivedCategory) ⟶
      (SheafOfModules.overFunctor.{u} (underlyingRingSheaf X) W).mapDerivedCategory ⋙
        ((SheafOfModules.overMap.{u} (underlyingRingSheaf X) hTW.hom).mapDerivedCategory ⋙
          (sliceToSubspace (underlyingRingSheaf X) T).mapDerivedCategory) :=
  Functor.whiskerRight
      (derivedCompToId (jStar W (underlyingRingSheaf X)) (jShriek W (underlyingRingSheaf X))
        (jShriekAdjunction W (underlyingRingSheaf X)).counit)
      (jStar T (underlyingRingSheaf X)).mapDerivedCategory ≫
    (mapDerivedCategoryCompIso (SheafOfModules.overFunctor.{u} (underlyingRingSheaf X) T)
          (sliceToSubspace (underlyingRingSheaf X) T) ≪≫
        mapDerivedCategoryCongr
          (eqToIso (overFunctor_comp_sliceToSubspace (underlyingRingSheaf X) T))).inv ≫
      Functor.whiskerRight
        ((Stacks.DerivedCategoryComparisons.mapDerivedCategoryCompIso
              (SheafOfModules.overFunctor.{u} (underlyingRingSheaf X) W)
              (SheafOfModules.overMap.{u} (underlyingRingSheaf X) hTW.hom)).symm ≪≫
          Stacks.DerivedCategoryComparisons.mapDerivedCategoryIsoOfNatIso
            (SheafOfModules.overFunctor.{u} (underlyingRingSheaf X) W ⋙
              SheafOfModules.overMap.{u} (underlyingRingSheaf X) hTW.hom)
            (SheafOfModules.overFunctor.{u} (underlyingRingSheaf X) T)
            (SheafOfModules.overFunctorMap.{u} (underlyingRingSheaf X) hTW.hom)).inv
        (sliceToSubspace (underlyingRingSheaf X) T).mapDerivedCategory

/-- `Stacks.DerivedGlueing.sliceCounitLeft` at an object is the left-hand side of the
coherence. -/
theorem sliceCounitLeft_app (X : RingedSpace.{u, u}) {T W : Opens X.carrier} (hTW : T ≤ W)
    (Y : DerivedCategory (SheafOfModules.{u} (underlyingRingSheaf X))) :
    (sliceCounitLeft X hTW).app Y =
      (mapDerivedCategoryCompIso (jShriek W (underlyingRingSheaf X))
              (jStar T (underlyingRingSheaf X))).hom.app
            ((jStar W (underlyingRingSheaf X)).mapDerivedCategory.obj Y) ≫
          (openModuleRestriction X T W hTW).mapDerivedCategory.map
            ((sliceCompJStarIso W).inv.app Y) ≫
          (sliceRestrictOverDerivedIso hTW).hom.app
            ((SheafOfModules.overFunctor.{u} (underlyingRingSheaf X) W).mapDerivedCategory.obj
              Y) :=
  rfl

/-- `Stacks.DerivedGlueing.sliceCounitRight` at an object is the right-hand side of the
coherence. -/
theorem sliceCounitRight_app (X : RingedSpace.{u, u}) {T W : Opens X.carrier} (hTW : T ≤ W)
    (Y : DerivedCategory (SheafOfModules.{u} (underlyingRingSheaf X))) :
    (sliceCounitRight X hTW).app Y =
      (jStar T (underlyingRingSheaf X)).mapDerivedCategory.map
            ((derivedCompToId (jStar W (underlyingRingSheaf X))
                (jShriek W (underlyingRingSheaf X))
                (jShriekAdjunction W (underlyingRingSheaf X)).counit).app Y) ≫
          (sliceCompJStarIso T).inv.app Y ≫
            (sliceToSubspace (underlyingRingSheaf X) T).mapDerivedCategory.map
              ((RingedSite.overMapDerivedCategoryRestrictIso
                (Stacks.SheafOfModules.ringedSite X.sheaf) hTW.hom).inv.app Y) :=
  rfl

/-- **The two sides of the coherence agree as natural transformations.**  This is
`Stacks.DerivedGlueing.sliceCounit_generic` for the eight functors at hand, whose module-level
hypothesis is `Stacks.DerivedGlueing.whiskerLeft_sliceRestrictOverIso`. -/
theorem sliceCounitLeft_eq_sliceCounitRight (X : RingedSpace.{u, u}) {T W : Opens X.carrier}
    (hTW : T ≤ W) : sliceCounitLeft X hTW = sliceCounitRight X hTW :=
  sliceCounit_generic (SheafOfModules.overFunctor.{u} (underlyingRingSheaf X) W)
    (sliceToSubspace (underlyingRingSheaf X) W) (jStar W (underlyingRingSheaf X))
    (jShriek W (underlyingRingSheaf X))
    (SheafOfModules.overMap.{u} (underlyingRingSheaf X) hTW.hom)
    (sliceToSubspace (underlyingRingSheaf X) T)
    (SheafOfModules.overFunctor.{u} (underlyingRingSheaf X) T)
    (jStar T (underlyingRingSheaf X))
    (overFunctor_comp_sliceToSubspace (underlyingRingSheaf X) W)
    (overFunctor_comp_sliceToSubspace (underlyingRingSheaf X) T)
    (eqToIso (slice_comp_jShriek_jStar_eq (underlyingRingSheaf X) hTW).symm ≪≫
      sliceRestrictOverIso (underlyingRingSheaf X) hTW)
    (SheafOfModules.overFunctorMap.{u} (underlyingRingSheaf X) hTW.hom)
    (jShriekAdjunction W (underlyingRingSheaf X)).counit
    (Functor.whiskerRight (jShriekAdjunction W (underlyingRingSheaf X)).counit
      (jStar T (underlyingRingSheaf X))) rfl
    (whiskerLeft_sliceRestrictOverIso hTW)

/-- **`Stacks.DerivedGlueing.SliceCounitCoherence` holds.**  Both sides are natural in the object,
so the identity is an equality of two natural transformations; that equality is the
pseudofunctoriality of the passage to unbounded derived categories applied to the triangle
identity for `ExtensionByZeroModules.jShriekAdjunction` read in the slice model. -/
theorem sliceCounitCoherence (X : RingedSpace.{u, u}) {T W : Opens X.carrier} (hTW : T ≤ W) :
    SliceCounitCoherence X hTW := fun Y =>
  (sliceCounitLeft_app X hTW Y).symm.trans
    ((NatTrans.congr_app (sliceCounitLeft_eq_sliceCounitRight X hTW) Y).trans
      (sliceCounitRight_app X hTW Y))

/-- **The two comparisons of restriction agree**, with nothing granted.  This is
`Stacks.DerivedGlueing.canonicalCompareIso_eq_overMapCompareIso_of_sliceCounitCoherence` with its
hypothesis discharged. -/
theorem canonicalCompareIso_eq_overMapCompareIso {O : Opens X.carrier}
    (K : OpenDerivedCategory X O) {T W : Opens X.carrier} (hTW : T ≤ W) (hWO : W ≤ O) :
    canonicalCompareIso K hTW hWO = overMapCompareIso K hTW :=
  canonicalCompareIso_eq_overMapCompareIso_of_sliceCounitCoherence K hTW hWO
    (sliceCounitCoherence X hTW)

/-- **The coherence between the restriction of morphisms of Situation 0D67 and the restriction of
morphisms on the ringed site, with nothing granted.**  This is
`Stacks.DerivedGlueing.restrictHomBelow_eq_restrictDerivedHom_of_compareIso` with both of its
hypotheses discharged: `Stacks.DerivedGlueing.restrictionCompareIso_trans_eq_canonical` removes the
system from each, and `Stacks.DerivedGlueing.canonicalCompareIso_eq_overMapCompareIso` is what
remains.

It is the one statement the chain from [Stacks, Tag 0D66] part (2) to the uniqueness clause of
[Stacks, Tag 0D68] was owed. -/
theorem restrictHomBelow_eq_restrictDerivedHom (S : LocallyGiven X) {O : Opens X.carrier}
    (K L : OpenDerivedCategory X O) {T W : Opens X.carrier} (hTW : T ≤ W) (hWO : W ≤ O)
    (phi : (S.restriction W O hWO).obj K ⟶ (S.restriction W O hWO).obj L) :
    homEquivSlice S K L (hTW.trans hWO) (restrictHomBelow S hTW hWO phi) =
      RingedSite.restrictDerivedHom (Stacks.SheafOfModules.ringedSite X.sheaf) hTW.hom
        ((jShriek O (underlyingRingSheaf X)).mapDerivedCategory.obj K)
        ((jShriek O (underlyingRingSheaf X)).mapDerivedCategory.obj L)
        (homEquivSlice S K L hWO phi) :=
  restrictHomBelow_eq_restrictDerivedHom_of_compareIso S K L hTW hWO
    ((restrictionCompareIso_trans_eq_canonical S K hTW hWO).trans
      (canonicalCompareIso_eq_overMapCompareIso K hTW hWO))
    ((restrictionCompareIso_trans_eq_canonical S L hTW hWO).trans
      (canonicalCompareIso_eq_overMapCompareIso L hTW hWO)) phi

end Closing


end Stacks.DerivedGlueing

end
