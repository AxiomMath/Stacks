module

public import StacksFrontier.AlgebraicGeometry.Morphisms.Birational.GenericPointMapComponents
public import StacksFrontier.AlgebraicGeometry.Morphisms.Birational.GenericPointMapInjective
public import StacksFrontier.AlgebraicGeometry.Morphisms.Valuative.LocalExtension
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Rational maps out of a reduced scheme are their generic-point data

Let `X` and `Y` be schemes over `S`, where `X` has finitely many irreducible components with
chosen generic points. If `Y` is locally of finite type over `S` and `X` is reduced, then
rational maps from `X` to `Y` over `S` are in bijection with the families consisting of, for
every chosen generic point, a point of the target and a compatible local map on stalks.

## Main results

* `AlgebraicGeometry.GenericPointMapContext.bijective_genericPointMapForRationalMaps_of_isReduced`:
  evaluation of rational maps at the generic points is bijective when the target is locally of
  finite type over the base and the source is reduced.

## Implementation notes

The map is the generic-point map constructed in
`AlgebraicGeometry.GenericPointMapContext.genericPointMapForRationalMaps`; its codomain records,
for every chosen generic point, a point of the target and a compatible local map on stalks.

Injectivity is Tag 0BX8's first part. Surjectivity is reduced to the components one at a time by
`AlgebraicGeometry.GenericPointMapContext.surjective_genericPointMap_iff_components`, and on a
single component the required rational map is produced by
`AlgebraicGeometry.exists_open_morphism_inducing_localHom_of_isReduced`: the chart
`A` is an open piece of one irreducible component inside the disjoint-component locus, so it is
irreducible and reduced, and the prescribed local map on its generic stalk extends to a morphism
on an open neighbourhood, which is dense because the generic point specializes to every point.

## References

* [Stacks Project, Lemma 29.49.2 (Tag 0BX8)](https://stacks.math.columbia.edu/tag/0BX8)
-/

@[expose] public section

universe u

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry

namespace GenericPointMapContext

variable (C : GenericPointMapContext.{u})

private theorem genericPointLocalMap_ext {i : Fin C.numberOfComponents}
    {a b : C.GenericPointLocalMap i} (hp : a.point = b.point)
    (hs : HEq a.stalkMap b.stalkMap) : a = b := by
  cases a with
  | mk ap am ast al ac =>
    cases b with
    | mk bp bm bst bl bc =>
      dsimp at hp hs
      cases hp
      cases hs
      rfl

private lemma hom_comp_five {A B C D E F : CommRingCat}
    (f : A ⟶ B) (g : B ⟶ C) (h : C ⟶ D) (j : D ⟶ E) (k : E ⟶ F) :
    (k.hom.comp (j.hom.comp h.hom)).comp (g.hom.comp f.hom) =
      (((f ≫ g) ≫ h) ≫ j ≫ k).hom := by
  simp only [CommRingCat.hom_comp, RingHom.comp_assoc]

/-- The local map of generic-point data is compatible with the structure maps on stalks. -/
private theorem GenericPointLocalMap.eqToHom_comp_stalkMap {i : Fin C.numberOfComponents}
    (yi : C.GenericPointLocalMap i) :
    eqToHom (congrArg (fun z ↦ C.S.presheaf.stalk z) yi.mapsTo).symm ≫
        C.toBaseTarget.stalkMap yi.point ≫ yi.stalkMap =
      C.toBaseSource.stalkMap (C.genericPoint i) := by
  rw [yi.commutes]
  simp

/-- The chosen generic point of a component is a generic point of its piece of the dense
open. -/
private theorem isGenericPoint_componentOpen (R : IrreducibleComponentReduction C)
    (i : Fin C.numberOfComponents) (hD : C.genericPoint i ∈ R.denseOpen)
    (hA : (⟨C.genericPoint i, hD⟩ : R.denseOpen.toScheme) ∈
      (R.componentOpen i : Set R.denseOpen.toScheme)) :
    IsGenericPoint (⟨⟨C.genericPoint i, hD⟩, hA⟩ : (R.componentOpen i).toScheme) Set.univ := by
  refine isGenericPoint_iff_specializes.2 fun z ↦ iff_of_true ?_ (Set.mem_univ z)
  apply (R.componentOpen i).ι.isOpenEmbedding.isInducing.specializes_iff.mp
  apply R.denseOpen.ι.isOpenEmbedding.isInducing.specializes_iff.mp
  apply (C.isGenericPoint i).specializes
  have hz : ((R.componentOpen i).ι z : R.denseOpen.toScheme) ∈
      (R.componentOpen i : Set R.denseOpen.toScheme) := z.2
  rwa [R.componentOpen_carrier] at hz

/-- A stalk equation for a morphism out of an iterated open subscheme, in the form produced by
local extension, identifies its stalk map transported to the ambient scheme. -/
private theorem heq_stalkMap_comp_stalkIso_of_comp_eq {X Y : Scheme.{u}} {U : X.Opens}
    {V : U.toScheme.Opens} {W : V.toScheme.Opens} (f : W.toScheme ⟶ Y) (x : W) {y : Y}
    (φ : Y.presheaf.stalk y ⟶ X.presheaf.stalk x.1.1.1) (hfy : f x = y)
    (h : (W.stalkIso x).hom.hom.comp ((f.stalkMap x).hom.comp
        (eqToHom (congrArg (fun z ↦ Y.presheaf.stalk z) hfy).symm).hom) =
      (V.stalkIso x.1).inv.hom.comp ((U.stalkIso x.1.1).inv.hom.comp φ.hom)) :
    HEq (f.stalkMap x ≫ (W.stalkIso x).hom ≫ (V.stalkIso x.1).hom ≫ (U.stalkIso x.1.1).hom)
      φ := by
  subst hfy
  have h' : f.stalkMap x ≫ (W.stalkIso x).hom =
      φ ≫ (U.stalkIso x.1.1).inv ≫ (V.stalkIso x.1).inv := by
    apply CommRingCat.hom_ext
    simpa only [CommRingCat.hom_comp, RingHom.comp_assoc, eqToHom_refl, CommRingCat.hom_id,
      RingHom.comp_id] using h
  apply heq_of_eq
  rw [← Category.assoc (f.stalkMap x), h']
  simp

/-- A representative on a component piece, over the base and realizing the prescribed point and
stalk map at the generic point, yields a rational map with the prescribed generic-point data. -/
private theorem exists_componentGenericPointMap_eq_of_partialMap
    (R : IrreducibleComponentReduction C) {i : Fin C.numberOfComponents}
    (yi : C.GenericPointLocalMap i)
    (g : (R.componentOpen i).toScheme.PartialMap C.Y)
    (hg : g.hom ≫ C.toBaseTarget =
      g.domain.ι ≫ (R.componentOpen i).ι ≫ R.denseOpen.ι ≫ C.toBaseSource)
    (x : g.domain) (hx : x.1.1.1 = C.genericPoint i) (hpoint : g.hom x = yi.point)
    (hstalk : HEq (g.hom.stalkMap x ≫ (g.domain.stalkIso x).hom ≫
      ((R.componentOpen i).stalkIso x.1).hom ≫ (R.denseOpen.stalkIso x.1.1).hom) yi.stalkMap) :
    ∃ c, R.componentGenericPointMap i c = yi := by
  let c : ComponentRationalMapsOver C R.denseOpen (R.componentOpen i) :=
    ⟨g.toRationalMap, by
      rw [← Scheme.RationalMap.compHom_toRationalMap]
      apply Scheme.PartialMap.toRationalMap_eq_iff.mpr
      refine ⟨g.domain, g.dense_domain, le_rfl, le_top, ?_⟩
      have htop : (R.componentOpen i).toScheme.topIso.hom =
          (⊤ : (R.componentOpen i).toScheme.Opens).ι := rfl
      simp only [Scheme.PartialMap.restrict, Scheme.PartialMap.compHom,
        Scheme.Hom.toPartialMap]
      rw [Scheme.homOfLE_rfl, Category.id_comp, htop]
      simpa only [← Category.assoc, Scheme.homOfLE_ι] using hg⟩
  exact ⟨c, genericPointLocalMap_ext C
    ((R.componentGenericPointMap_point i c g rfl hg x hx).trans hpoint)
    ((R.componentGenericPointMap_stalk i c g rfl hg x hx).trans hstalk)⟩

/-- On a reduced source, with target locally of finite type over the base, every compatible
local datum at the generic point of a component is realized by a rational map on its piece. -/
private theorem exists_componentGenericPointMap_eq_of_isReduced
    [LocallyOfFiniteType C.toBaseTarget] [IsReduced C.X] (R : IrreducibleComponentReduction C)
    (i : Fin C.numberOfComponents) (yi : C.GenericPointLocalMap i) :
    ∃ c, R.componentGenericPointMap i c = yi := by
  let x := C.genericPoint i
  let y := yi.point
  have hxD : x ∈ R.denseOpen := genericPoint_mem_dense_open C R.denseOpen R.dense_denseOpen i
  let A : R.denseOpen.toScheme.Opens := R.componentOpen i
  let xD : R.denseOpen.toScheme := (⟨x, hxD⟩ : R.denseOpen)
  have hxA : xD ∈ (R.componentOpen i : Set R.denseOpen.toScheme) := by
    rw [R.componentOpen_carrier]
    exact (C.isGenericPoint i).mem
  let q : A.toScheme := ⟨xD, hxA⟩
  have hgenA : IsGenericPoint q Set.univ := isGenericPoint_componentOpen C R i hxD hxA
  have : IrreducibleSpace A.toScheme := (irreducibleSpace_def A.toScheme).2 hgenA.isIrreducible
  have hcompA : (irreducibleComponents A.toScheme).Finite := by
    simp [irreducibleComponents_eq_singleton]
  have : IsReduced R.denseOpen.toScheme := isReduced_of_isOpenImmersion R.denseOpen.ι
  have : IsReduced A.toScheme := isReduced_of_isOpenImmersion A.ι
  let pA : A.toScheme ⟶ C.S := A.ι ≫ R.denseOpen.ι ≫ C.toBaseSource
  let xDpoint : R.denseOpen := A.ι q
  let phiA : C.Y.presheaf.stalk y →+* A.toScheme.presheaf.stalk q :=
    (A.stalkIso q).inv.hom.comp ((R.denseOpen.stalkIso xDpoint).inv.hom.comp yi.stalkMap.hom)
  have hphiA : IsLocalHom phiA := by
    dsimp [phiA]
    exact @RingHom.isLocalHom_comp _ _ _ _ _ _ _ _ (isLocalHom_of_isIso (A.stalkIso q).inv)
      (@RingHom.isLocalHom_comp _ _ _ _ _ _ _ _ (isLocalHom_of_isIso _) yi.isLocalHom)
  have hphiAS : phiA.comp ((C.toBaseTarget.stalkMap y).hom.comp
      (eqToHom (congrArg (fun z ↦ C.S.presheaf.stalk z) yi.mapsTo).symm).hom) =
      (pA.stalkMap q).hom := by
    have hloc : (eqToHom (congrArg (fun z ↦ C.S.presheaf.stalk z) yi.mapsTo).symm ≫
        C.toBaseTarget.stalkMap y) ≫ yi.stalkMap = C.toBaseSource.stalkMap x := by
      simpa only [← Category.assoc] using GenericPointLocalMap.eqToHom_comp_stalkMap C yi
    have hcat : ((eqToHom (congrArg (fun z ↦ C.S.presheaf.stalk z) yi.mapsTo).symm ≫
        C.toBaseTarget.stalkMap y) ≫ yi.stalkMap) ≫
          (R.denseOpen.stalkIso xDpoint).inv ≫ (A.stalkIso q).inv = pA.stalkMap q := by
      rw [hloc, Scheme.Opens.stalkIso_inv, Scheme.Opens.stalkIso_inv]
      simp only [pA, Scheme.Hom.stalkMap_comp]
      rfl
    exact (hom_comp_five (eqToHom (congrArg (fun z ↦ C.S.presheaf.stalk z) yi.mapsTo).symm)
      (C.toBaseTarget.stalkMap y) yi.stalkMap (R.denseOpen.stalkIso xDpoint).inv
      (A.stalkIso q).inv).trans (congrArg CommRingCat.Hom.hom hcat)
  obtain ⟨W, hqW, fA, hfA, hfyA, hstalkA⟩ := exists_open_morphism_inducing_localHom_of_isReduced
    pA C.toBaseTarget (C.toBaseSource x) q y rfl yi.mapsTo phiA hphiA hphiAS inferInstance
    ‹IsReduced A.toScheme› hcompA
  have hWdense : Dense (W : Set A.toScheme) := dense_iff_closure_eq.2 <| Set.eq_univ_of_forall
    fun z ↦ closure_mono (Set.singleton_subset_iff.mpr hqW) (hgenA.specializes trivial).mem_closure
  let g : A.toScheme.PartialMap C.Y := ⟨W, hWdense, fA⟩
  have hgOver : g.hom ≫ C.toBaseTarget = g.domain.ι ≫ A.ι ≫ R.denseOpen.ι ≫ C.toBaseSource := by
    simpa [g, pA, Category.assoc] using hfA
  exact exists_componentGenericPointMap_eq_of_partialMap C R yi g hgOver ⟨q, hqW⟩ rfl hfyA
    (heq_stalkMap_comp_stalkIso_of_comp_eq fA ⟨q, hqW⟩ yi.stalkMap hfyA hstalkA)

/-- For a reduced source and a target locally of finite type over the base,
rational maps over the base are determined by, and realize, arbitrary
compatible local data at the generic points of the source. -/
@[stacks 0BX8 "reduced_source_bijectivity",
  ega "IV 20.2.11" "(ii) reduced case",
  ega "I 7.1.11" "bijectivity, X reduced"]
public theorem bijective_genericPointMapForRationalMaps_of_isReduced
    [LocallyOfFiniteType C.toBaseTarget] [IsReduced C.X] :
    Function.Bijective C.genericPointMapForRationalMaps := by
  refine ⟨genericPointMapForRationalMaps_injective C, ?_⟩
  obtain ⟨R⟩ := nonempty_irreducibleComponentReduction C
  rw [surjective_genericPointMap_iff_components C R]
  exact Or.inr fun i yi ↦ exists_componentGenericPointMap_eq_of_isReduced C R i yi

end GenericPointMapContext


end AlgebraicGeometry

end
