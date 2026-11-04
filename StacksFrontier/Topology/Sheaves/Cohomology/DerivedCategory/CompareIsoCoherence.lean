module

public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedCategory.HomRestrictionInSituation0D67
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedCategory.RestrictionCompCanonical

/-!
# The two comparisons of restriction, with the system eliminated

Let `(X, 𝒪_X)` be a ringed space and `S` a system of locally given derived objects on it
(Situation 0D67).  The coherence that the uniqueness clause of [Stacks, Tag 0D68] needs —
that the restriction of morphisms of Situation 0D67 is the restriction of morphisms on the
ringed site — was reduced in
`StacksFrontier.Topology.Sheaves.Cohomology.DerivedCategory.HomRestrictionInSituation0D67` to an
equation between two *isomorphisms*,

`restrictionCompareIso S K hTW hWO ≪≫ (sliceRestrictOverRestrictionIso S hTW).app _ =`
`  overMapCompareIso K hTW`,

by `Stacks.DerivedGlueing.restrictHomBelow_eq_restrictDerivedHom_of_compareIso`.

This file removes the system from the left-hand side.  Every occurrence of `S` there enters
through `Stacks.DerivedGlueing.restrictionIsoMapDerivedCategory` and through
`S.restrictionComp`, and the second is the canonical comparison conjugated by the first
(`Stacks.DerivedGlueing.LocallyGiven.restrictionComp_eq_app`).  So the conjugating
isomorphisms cancel in pairs, and what is left is
`Stacks.DerivedGlueing.canonicalCompareIso`, built only from
`Stacks.DerivedGlueing.openModuleRestrictionIsoOfExtension`, the canonical comparison induced by
`Stacks.DerivedGlueing.openModuleRestrictionComparison` — the **counit** of extension by zero on
the middle open — and `Stacks.DerivedGlueing.sliceRestrictOverDerivedIso`.

## Main results

* `Stacks.DerivedGlueing.extensionRestrictionNatIso` — the comparison
  `Stacks.DerivedGlueing.openModuleRestrictionIsoOfExtension` as a natural isomorphism, with
  `Stacks.DerivedGlueing.extensionRestrictionNatIso_app` identifying its components.
* `Stacks.DerivedGlueing.canonicalCompareIso` — the comparison of the two readings of the
  restriction of an extension by zero, with no system involved.
* `Stacks.DerivedGlueing.conj_cancel_restriction` — the cancellation of conjugating isomorphisms
  that eliminates the system, stated with every object and morphism a variable.
* `Stacks.DerivedGlueing.restrictionCompareIso_trans_eq_canonical` — the left-hand side of the
  coherence is that canonical comparison, for *every* system.

## The remaining equation

What is left is one equation, and it mentions no system:

`Stacks.DerivedGlueing.canonicalCompareIso K hTW hWO =`
`  Stacks.DerivedGlueing.overMapCompareIso K hTW`.

Its two sides are recorded as natural isomorphisms between one pair of functors
(`Stacks.DerivedGlueing.canonicalCompareNatIso` and `Stacks.DerivedGlueing.overMapCompareNatIso`)
in `StacksFrontier.Topology.Sheaves.Cohomology.DerivedCategory.CompareIsoCoherenceClosed`, and the
equation is proved as `Stacks.DerivedGlueing.canonicalCompareIso_eq_overMapCompareIso` in
`StacksFrontier.Topology.Sheaves.Cohomology.DerivedCategory.CompareIsoCounitReduction`. Its only
non-formal ingredient is the triangle identity for `ExtensionByZeroModules.jShriekAdjunction`,
discharged on sheaves of modules as `Stacks.DerivedGlueing.sliceExtendOverIso_hom_app_over`. With
it, `Stacks.DerivedGlueing.restrictHomBelow_eq_restrictDerivedHom_of_compareIso` becomes
unconditional, and with that
`Stacks.DerivedGlueing.exists_unique_solutionIso_of_covers_of_coherence` is clause (a) of
[Stacks, Tag 0D68] with nothing granted.

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

universe u

variable {X : RingedSpace.{u, u}}

attribute [local instance 10000] HasDerivedCategory.standard

attribute [local instance] Stacks.DerivedGlueing.preservesFiniteLimitsOverMap
  Stacks.DerivedGlueing.preservesFiniteColimitsOverMap

/-- **`Stacks.DerivedGlueing.openModuleRestrictionIsoOfExtension` as a natural isomorphism.**
Extending an object over `O` by zero and restricting it to `U ≤ O` in the open-subspace model is
restricting it from `O` to `U`, naturally in the object.  The three comparisons are the ones the
pointwise definition composes. -/
def extensionRestrictionNatIso (O U : Opens X.carrier) (hUO : U ≤ O) :
    (jShriek O (underlyingRingSheaf X)).mapDerivedCategory ⋙
        ((SheafOfModules.overFunctor.{u} (underlyingRingSheaf X) U).mapDerivedCategory ⋙
          (sliceToSubspace (underlyingRingSheaf X) U).mapDerivedCategory) ≅
      (openModuleRestriction X U O hUO).mapDerivedCategory :=
  Functor.isoWhiskerLeft (jShriek O (underlyingRingSheaf X)).mapDerivedCategory
      (mapDerivedCategoryCompIso (SheafOfModules.overFunctor.{u} (underlyingRingSheaf X) U)
        (sliceToSubspace (underlyingRingSheaf X) U)) ≪≫
    mapDerivedCategoryCompIso (jShriek O (underlyingRingSheaf X))
        (SheafOfModules.overFunctor.{u} (underlyingRingSheaf X) U ⋙
          sliceToSubspace (underlyingRingSheaf X) U) ≪≫
      mapDerivedCategoryCongr (eqToIso (openModuleRestriction_eq O U hUO))

/-- The natural isomorphism agrees pointwise with the comparison it is assembled from. -/
theorem extensionRestrictionNatIso_app (O U : Opens X.carrier) (hUO : U ≤ O)
    (K : OpenDerivedCategory X O) :
    (extensionRestrictionNatIso O U hUO).app K = openModuleRestrictionIsoOfExtension O U hUO K :=
  Iso.ext rfl

/-- **The comparison of the two readings of the restriction of an extension by zero, with no
system involved.**  The slice-model restriction to `T` of the extension by zero of `K` along `O`
is identified with its restriction along the arrow `T ⟶ W` of the site: first with the
restriction from `O` to `T` of complexes, then with its reading through `W` by the canonical
comparison induced by `Stacks.DerivedGlueing.openModuleRestrictionComparison` — the counit of
extension by zero on `W` — and finally by
`Stacks.DerivedGlueing.sliceRestrictOverDerivedIso`.

This is what the left-hand side of the coherence becomes once the system is eliminated. -/
def canonicalCompareIso {O : Opens X.carrier} (K : OpenDerivedCategory X O)
    {T W : Opens X.carrier} (hTW : T ≤ W) (hWO : W ≤ O) :
    (sliceToSubspace (underlyingRingSheaf X) T).mapDerivedCategory.obj
        ((SheafOfModules.overFunctor.{u} (underlyingRingSheaf X) T).mapDerivedCategory.obj
          ((jShriek O (underlyingRingSheaf X)).mapDerivedCategory.obj K)) ≅
      (sliceToSubspace (underlyingRingSheaf X) T).mapDerivedCategory.obj
        ((SheafOfModules.overMap.{u} (underlyingRingSheaf X) hTW.hom).mapDerivedCategory.obj
          ((SheafOfModules.overFunctor.{u} (underlyingRingSheaf X) W).mapDerivedCategory.obj
            ((jShriek O (underlyingRingSheaf X)).mapDerivedCategory.obj K))) :=
  openModuleRestrictionIsoOfExtension O T (hTW.trans hWO) K ≪≫
    (mapDerivedCategoryComp (openModuleRestriction X W O hWO)
          (openModuleRestriction X T W hTW) (openModuleRestriction X T O (hTW.trans hWO))
          (asIso (openModuleRestrictionComparison X T W O hTW hWO))).app K ≪≫
      (openModuleRestriction X T W hTW).mapDerivedCategory.mapIso
          (openModuleRestrictionIsoOfExtension O W hWO K).symm ≪≫
        (sliceRestrictOverDerivedIso hTW).app
          ((SheafOfModules.overFunctor.{u} (underlyingRingSheaf X) W).mapDerivedCategory.obj
            ((jShriek O (underlyingRingSheaf X)).mapDerivedCategory.obj K))

/-- **The cancellation that eliminates the system.**  Two inverse pairs of conjugating
isomorphisms and one naturality square collapse a conjugated comparison onto the comparison
itself.  Every object and morphism is a variable, so this applies by `exact` at one definitional
unification; stated with the spellings of the concrete situation it would need a rewrite across
the slice/open-subspace crossing, which is a heartbeat timeout. -/
theorem conj_cancel_restriction {A : Type*} [Category A] {B : Type*} [Category B]
    {Rst Gf : A ⥤ B} (r : Rst ≅ Gf) {a b d : B} (eT : a ⟶ b) (p : b ⟶ d) (q : d ⟶ b)
    (hpq : p ≫ q = 𝟙 b) {P' P Q : A} (can : b ⟶ Gf.obj P') (w : P' ⟶ P) (wv : P ⟶ P')
    (hw : w ≫ wv = 𝟙 P') (eW : P' ⟶ Q) {Y : B} (s : Gf.obj Q ⟶ Y) (Bm : d ⟶ Rst.obj P)
    (hB : Bm = q ≫ can ≫ Gf.map w ≫ r.inv.app P) :
    ((eT ≫ p) ≫ Bm ≫ Rst.map (wv ≫ eW)) ≫ r.hom.app Q ≫ s =
      eT ≫ can ≫ Gf.map eW ≫ s := by
  subst hB
  have hnat : r.inv.app P ≫ Rst.map (wv ≫ eW) = Gf.map (wv ≫ eW) ≫ r.inv.app Q :=
    (r.inv.naturality (wv ≫ eW)).symm
  have hmap : Gf.map w ≫ Gf.map (wv ≫ eW) = Gf.map eW := by
    rw [← Functor.map_comp, ← Category.assoc, hw, Category.id_comp]
  simp only [Category.assoc]
  rw [reassoc_of% hpq, reassoc_of% hnat, Iso.inv_hom_id_app_assoc, reassoc_of% hmap]

/-- **The left-hand side of the 0D68 coherence is the canonical comparison, for every system.**
Every occurrence of the system in
`Stacks.DerivedGlueing.restrictionCompareIso S K hTW hWO ≪≫`
`(Stacks.DerivedGlueing.sliceRestrictOverRestrictionIso S hTW).app _`
enters through `Stacks.DerivedGlueing.restrictionIsoMapDerivedCategory`, because the system's
comparison of restriction in two steps is the canonical one conjugated by it
(`Stacks.DerivedGlueing.LocallyGiven.restrictionComp_eq_app`).  Those conjugations cancel in
pairs, leaving `Stacks.DerivedGlueing.canonicalCompareIso`.

So the coherence owed by the uniqueness clause of [Stacks, Tag 0D68] is a statement about the
canonical comparisons alone: see the section *The remaining equation* of the module
documentation. -/
theorem restrictionCompareIso_trans_eq_canonical (S : LocallyGiven X)
    {O : Opens X.carrier} (K : OpenDerivedCategory X O) {T W : Opens X.carrier}
    (hTW : T ≤ W) (hWO : W ≤ O) :
    restrictionCompareIso S K hTW hWO ≪≫ (sliceRestrictOverRestrictionIso S hTW).app
        ((SheafOfModules.overFunctor.{u} (underlyingRingSheaf X) W).mapDerivedCategory.obj
          ((jShriek O (underlyingRingSheaf X)).mapDerivedCategory.obj K)) =
      canonicalCompareIso K hTW hWO :=
  Iso.ext <| conj_cancel_restriction (restrictionIsoMapDerivedCategory S T W hTW)
    (openModuleRestrictionIsoOfExtension O T (hTW.trans hWO) K).hom
    ((restrictionIsoMapDerivedCategory S T O (hTW.trans hWO)).inv.app K)
    ((restrictionIsoMapDerivedCategory S T O (hTW.trans hWO)).hom.app K)
    ((restrictionIsoMapDerivedCategory S T O (hTW.trans hWO)).inv_hom_id_app K)
    ((mapDerivedCategoryComp (openModuleRestriction X W O hWO)
      (openModuleRestriction X T W hTW) (openModuleRestriction X T O (hTW.trans hWO))
      (asIso (openModuleRestrictionComparison X T W O hTW hWO))).hom.app K)
    ((restrictionIsoMapDerivedCategory S W O hWO).inv.app K)
    ((restrictionIsoMapDerivedCategory S W O hWO).hom.app K)
    ((restrictionIsoMapDerivedCategory S W O hWO).inv_hom_id_app K)
    (openModuleRestrictionIsoOfExtension O W hWO K).inv _
    ((S.restrictionComp T W O hTW hWO).hom.app K)
    (S.restrictionComp_hom_app_eq T W O hTW hWO K)

end Stacks.DerivedGlueing

end
