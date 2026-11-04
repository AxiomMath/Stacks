module

public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedFunctors.CompositeComparisonTransitivity
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedFunctors.CompositeRightDerivedTransitivity

/-!
# Transitivity of the two right-derived comparison engines

Two different comparison isomorphisms are used to identify the right derived functors of a
composite:

* `Stacks.Cohomology.CompositeRightDerived.compRightDerivedNatIso L G n :
  (L ⋙ G).rightDerived n ≅ L ⋙ G.rightDerived n`, for `L` exact and preserving injective
  objects, which moves an exact functor out of a derived functor on the **left**, and
* `Stacks.Cohomology.ModuleComparison.rightDerivedCompIso F G H e n :
  F.rightDerived n ⋙ G ≅ H.rightDerived n`, for `G` exact and `e : F ⋙ G ≅ H`, which moves an
  exact functor out of a derived functor on the **right**.

Each has a composition law of its own
(`Stacks.Cohomology.DerivedCompTransport.compRightDerivedNatIso_comp` and
`Stacks.Cohomology.DerivedCompTransport.rightDerivedCompIso_comp`), but nothing related the two
to each other, so a comparison assembled from one engine could not be identified with a
comparison assembled from the other.  That identification is what this file supplies.

The configuration is a square of functors: `L : C ⥤ D` and `L' : C ⥤ D'` exact and preserving
injective objects, `S : D ⥤ D'` likewise, `G : D ⥤ E` and `G' : D' ⥤ E'` additive, `R : E ⥤ E'`
additive and exact, together with `e : G ⋙ R ≅ S ⋙ G'` and `ι : L ⋙ S ≅ L'`.  Then
`(L ⋙ G) ⋙ R ≅ L' ⋙ G'` in a canonical way, and there are two routes from
`((L ⋙ G).rightDerived p) ⋙ R` to `L' ⋙ G'.rightDerived p`: peel `L` off first with
`compRightDerivedNatIso` and then use `rightDerivedCompIso` for `R` against `G` alone, or use
`rightDerivedCompIso` for `R` against the composite `L ⋙ G` and peel `L'` off at the end.  The
main result says the two agree.

## Main results

* `mapHomologicalComplexCompIso_hom_app_whiskerLeft`: the degreewise content — applying a
  comparison built by whiskering is applying the inner comparison and then the degreewise image
  of `ι`.
* `mapComplexHomologyIso_hom_app_whiskerLeft`: the same statement one level up, for
  `Stacks.Cohomology.ModuleComparison.mapComplexHomologyIso`.
* `rightDerivedCompIso_comp_compRightDerivedNatIso_app` and
  `rightDerivedCompIso_comp_compRightDerivedNatIso`: **the two-engine transitivity law**,
  pointwise and as an equality of natural transformations.

## Implementation notes

Both engines compute on injective resolutions, and the proof is the observation that one triple
of resolutions serves all four comparisons: the chosen resolution `I` of `M`, its image
`J = mapInjRes L I` under `L`, and the image `mapInjRes S J` of that under `S`, which is also
the image of `I` under `L ⋙ S`.  Each occurrence of
`CategoryTheory.InjectiveResolution.isoRightDerivedObj` then cancels against its own inverse,
and what is left is the complex-level comparison, whose two sides differ by the degreewise
image of `ι` — the content of `mapHomologicalComplexCompIso_hom_app_whiskerLeft`.  Transporting
along `ι` on the derived side is
`CategoryTheory.InjectiveResolution.isoRightDerivedObj_inv_naturality` for the descent of
`ι.hom.app M` given by applying `ι.hom` degreewise.

`((L ⋙ S).mapHomologicalComplex c).obj K` and
`(S.mapHomologicalComplex c).obj ((L.mapHomologicalComplex c).obj K)` are definitionally equal
but are not syntactically interchangeable for `rw`, so the reassociations below are terms built
from `Category.assoc` and `congrArg` elaborated against a goal stated in the desired spelling,
exactly as in
`StacksFrontier/Topology/Sheaves/Cohomology/DerivedFunctors/CompositeComparisonOnResolutions.lean`.

## References

* [The Stacks Project, Tag 015Z](https://stacks.math.columbia.edu/tag/015Z)
* [The Stacks Project, Tag 01E5](https://stacks.math.columbia.edu/tag/01E5)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace Stacks.Cohomology.DerivedCompTransport

open Stacks.Cohomology.CompositeRightDerived Stacks.Cohomology.ModuleComparison

/-! ### Reassociation lemmas -/

section Glue

variable {O : Type*} [Category* O]

end Glue

section TwoEngines

variable {C : Type*} {D : Type*} {D' : Type*} {E : Type*} {E' : Type*}
  [Category* C] [Category* D] [Category* D'] [Category* E] [Category* E']
  [Abelian C] [HasInjectiveResolutions C] [Abelian D] [HasInjectiveResolutions D]
  [Abelian D'] [HasInjectiveResolutions D'] [Abelian E] [Abelian E']
  (L : C ⥤ D) (G : D ⥤ E) (R : E ⥤ E') (S : D ⥤ D') (G' : D' ⥤ E') (L' : C ⥤ D')
  [L.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]
  [L.PreservesInjectiveObjects]
  [S.Additive] [PreservesFiniteLimits S] [PreservesFiniteColimits S]
  [S.PreservesInjectiveObjects]
  [L'.Additive] [PreservesFiniteLimits L'] [PreservesFiniteColimits L']
  [L'.PreservesInjectiveObjects]
  [G.Additive] [G'.Additive] [R.Additive] [R.PreservesHomology]

omit [HasInjectiveResolutions C] [HasInjectiveResolutions D] [HasInjectiveResolutions D']
  [PreservesFiniteLimits L] [PreservesFiniteColimits L] [L.PreservesInjectiveObjects]
  [PreservesFiniteLimits S] [PreservesFiniteColimits S] [S.PreservesInjectiveObjects]
  [PreservesFiniteLimits L'] [PreservesFiniteColimits L'] [L'.PreservesInjectiveObjects]
  [R.PreservesHomology] in
/-- The degreewise content of the two-engine law: if `P` is the comparison
`(L ⋙ G) ⋙ R ≅ L' ⋙ G'` assembled from `e : G ⋙ R ≅ S ⋙ G'` and `ι : L ⋙ S ≅ L'`, then
applying `P` degreewise to a complex is applying `e` degreewise to the image of the complex
under `L`, followed by the image under `G'` of `ι` applied degreewise. -/
theorem mapHomologicalComplexCompIso_hom_app_whiskerLeft
    (e : G ⋙ R ≅ S ⋙ G') (ι : L ⋙ S ≅ L') (P : (L ⋙ G) ⋙ R ≅ L' ⋙ G')
    (hP : ∀ Z : C, P.hom.app Z = e.hom.app (L.obj Z) ≫ G'.map (ι.hom.app Z))
    (K : HomologicalComplex C (ComplexShape.up ℕ)) :
    (Functor.mapHomologicalComplexCompIso P (ComplexShape.up ℕ)).hom.app K =
      (Functor.mapHomologicalComplexCompIso e (ComplexShape.up ℕ)).hom.app
          ((L.mapHomologicalComplex (ComplexShape.up ℕ)).obj K) ≫
        (G'.mapHomologicalComplex (ComplexShape.up ℕ)).map
          ((NatTrans.mapHomologicalComplex ι.hom (ComplexShape.up ℕ)).app K) := by
  ext n
  simpa using hP (K.X n)

omit [HasInjectiveResolutions C] [HasInjectiveResolutions D] [HasInjectiveResolutions D']
  [PreservesFiniteLimits L] [PreservesFiniteColimits L] [L.PreservesInjectiveObjects]
  [PreservesFiniteLimits S] [PreservesFiniteColimits S] [S.PreservesInjectiveObjects]
  [PreservesFiniteLimits L'] [PreservesFiniteColimits L'] [L'.PreservesInjectiveObjects] in
/-- The two-engine law at the level of complexes: the comparison
`Stacks.Cohomology.ModuleComparison.mapComplexHomologyIso` for the composite `L ⋙ G` is the
comparison for `G` on the image complex, followed by the map induced on homology by `ι` applied
degreewise. -/
theorem mapComplexHomologyIso_hom_app_whiskerLeft
    (e : G ⋙ R ≅ S ⋙ G') (ι : L ⋙ S ≅ L') (P : (L ⋙ G) ⋙ R ≅ L' ⋙ G')
    (hP : ∀ Z : C, P.hom.app Z = e.hom.app (L.obj Z) ≫ G'.map (ι.hom.app Z))
    (p : ℕ) (K : HomologicalComplex C (ComplexShape.up ℕ)) :
    (mapComplexHomologyIso (L ⋙ G) R (L' ⋙ G') P p).hom.app K =
      (mapComplexHomologyIso G R (S ⋙ G') e p).hom.app
          ((L.mapHomologicalComplex (ComplexShape.up ℕ)).obj K) ≫
        (G'.mapHomologicalComplex (ComplexShape.up ℕ) ⋙
            HomologicalComplex.homologyFunctor E' (ComplexShape.up ℕ) p).map
          ((NatTrans.mapHomologicalComplex ι.hom (ComplexShape.up ℕ)).app K) := by
  refine Eq.trans (congrArg
    (fun φ => (homologyMapFunctorIso R p).inv.app
        ((G.mapHomologicalComplex (ComplexShape.up ℕ)).obj
          ((L.mapHomologicalComplex (ComplexShape.up ℕ)).obj K)) ≫
      HomologicalComplex.homologyMap φ p)
    (mapHomologicalComplexCompIso_hom_app_whiskerLeft L G R S G' L' e ι P hP K)) ?_
  refine Eq.trans (congrArg
    (fun ψ => (homologyMapFunctorIso R p).inv.app
        ((G.mapHomologicalComplex (ComplexShape.up ℕ)).obj
          ((L.mapHomologicalComplex (ComplexShape.up ℕ)).obj K)) ≫ ψ)
    (HomologicalComplex.homologyMap_comp
      ((Functor.mapHomologicalComplexCompIso e (ComplexShape.up ℕ)).hom.app
        ((L.mapHomologicalComplex (ComplexShape.up ℕ)).obj K))
      ((G'.mapHomologicalComplex (ComplexShape.up ℕ)).map
        ((NatTrans.mapHomologicalComplex ι.hom (ComplexShape.up ℕ)).app K)) p)) ?_
  exact (Category.assoc _ _ _).symm

/-- **The two-engine transitivity law, pointwise.**  Peeling the exact functor `L` off the
derived functor of `L ⋙ G` first and comparing `R` against `G` alone agrees with comparing `R`
against the composite `L ⋙ G` and peeling `L'` off at the end.

The hypothesis `hP` says that `P` is the comparison assembled from `e` and `ι`; it is stated
pointwise so that any spelling of that composite may be supplied. -/
theorem rightDerivedCompIso_comp_compRightDerivedNatIso_app
    (e : G ⋙ R ≅ S ⋙ G') (ι : L ⋙ S ≅ L') (P : (L ⋙ G) ⋙ R ≅ L' ⋙ G')
    (hP : ∀ Z : C, P.hom.app Z = e.hom.app (L.obj Z) ≫ G'.map (ι.hom.app Z))
    (p : ℕ) (M : C) :
    (rightDerivedCompIso (L ⋙ G) R (L' ⋙ G') P p).hom.app M ≫
        (compRightDerivedNatIso L' G' p).hom.app M =
      R.map ((compRightDerivedNatIso L G p).hom.app M) ≫
        (rightDerivedCompIso G R (S ⋙ G') e p).hom.app (L.obj M) ≫
          (compRightDerivedNatIso S G' p).hom.app (L.obj M) ≫
            (G'.rightDerived p).map (ι.hom.app M) := by
  have hχ : (mapInjRes S (mapInjRes L (injectiveResolution M))).ι.f 0 ≫
      ((NatTrans.mapHomologicalComplex ι.hom (ComplexShape.up ℕ)).app
        (injectiveResolution M).cocomplex).f 0 =
      ι.hom.app M ≫ (mapInjRes L' (injectiveResolution M)).ι.f 0 := by
    rw [mapInjRes_mapInjRes_ι_f_zero L S (injectiveResolution M),
      mapInjRes_ι_f_zero L' (injectiveResolution M)]
    exact ι.hom.naturality ((injectiveResolution M).ι.f 0)
  set I := injectiveResolution M with hI
  set J := mapInjRes L I with hJ
  set J' := mapInjRes L' I with hJ'
  set K := mapInjRes S J with hK
  set χ : K.cocomplex ⟶ J'.cocomplex :=
    (NatTrans.mapHomologicalComplex ι.hom (ComplexShape.up ℕ)).app I.cocomplex with hχdef
  have h1 : (rightDerivedCompIso (L ⋙ G) R (L' ⋙ G') P p).hom.app M =
      R.map (I.isoRightDerivedObj (L ⋙ G) p).hom ≫
        (mapComplexHomologyIso (L ⋙ G) R (L' ⋙ G') P p).hom.app I.cocomplex ≫
          (I.isoRightDerivedObj (L' ⋙ G') p).inv :=
    rightDerivedCompIso_hom_app_eq (L ⋙ G) R (L' ⋙ G') P p I
  have h2 : (compRightDerivedNatIso L' G' p).hom.app M =
      (I.isoRightDerivedObj (L' ⋙ G') p).hom ≫ (J'.isoRightDerivedObj G' p).inv :=
    compRightDerivedNatIso_hom_app_mapInjRes L' G' p I
  have h3 : R.map ((compRightDerivedNatIso L G p).hom.app M) =
      R.map (I.isoRightDerivedObj (L ⋙ G) p).hom ≫ R.map (J.isoRightDerivedObj G p).inv :=
    (congrArg R.map (compRightDerivedNatIso_hom_app_mapInjRes L G p I)).trans
      (R.map_comp _ _)
  have h4 : (rightDerivedCompIso G R (S ⋙ G') e p).hom.app (L.obj M) =
      R.map (J.isoRightDerivedObj G p).hom ≫
        (mapComplexHomologyIso G R (S ⋙ G') e p).hom.app J.cocomplex ≫
          (J.isoRightDerivedObj (S ⋙ G') p).inv :=
    rightDerivedCompIso_hom_app_eq G R (S ⋙ G') e p J
  have h5 : (compRightDerivedNatIso S G' p).hom.app (L.obj M) =
      (J.isoRightDerivedObj (S ⋙ G') p).hom ≫ (K.isoRightDerivedObj G' p).inv :=
    compRightDerivedNatIso_hom_app_mapInjRes S G' p J
  have h6 : (K.isoRightDerivedObj G' p).inv ≫ (G'.rightDerived p).map (ι.hom.app M) =
      (G'.mapHomologicalComplex (ComplexShape.up ℕ) ⋙
          HomologicalComplex.homologyFunctor E' (ComplexShape.up ℕ) p).map χ ≫
        (J'.isoRightDerivedObj G' p).inv :=
    InjectiveResolution.isoRightDerivedObj_inv_naturality (ι.hom.app M) K J' χ hχ G' p
  have h7 : (mapComplexHomologyIso G R (S ⋙ G') e p).hom.app J.cocomplex ≫
      (G'.mapHomologicalComplex (ComplexShape.up ℕ) ⋙
        HomologicalComplex.homologyFunctor E' (ComplexShape.up ℕ) p).map χ =
      (mapComplexHomologyIso (L ⋙ G) R (L' ⋙ G') P p).hom.app I.cocomplex :=
    (mapComplexHomologyIso_hom_app_whiskerLeft L G R S G' L' e ι P hP p I.cocomplex).symm
  have hmid : (compRightDerivedNatIso S G' p).hom.app (L.obj M) ≫
      (G'.rightDerived p).map (ι.hom.app M) =
      (J.isoRightDerivedObj (S ⋙ G') p).hom ≫
        (G'.mapHomologicalComplex (ComplexShape.up ℕ) ⋙
            HomologicalComplex.homologyFunctor E' (ComplexShape.up ℕ) p).map χ ≫
          (J'.isoRightDerivedObj G' p).inv :=
    (congrArg (· ≫ (G'.rightDerived p).map (ι.hom.app M)) h5).trans
      ((Category.assoc _ _ _).trans (congrArg _ h6))
  rw [h1, h2, h3, h4]
  simp only [Category.assoc, hmid]
  erw [Iso.inv_hom_id_assoc, Iso.inv_hom_id_assoc, Iso.map_inv_hom_id_assoc, ← h7,
    Category.assoc]
  rfl

/-- **The two-engine transitivity law.**  `Stacks.Cohomology.ModuleComparison.rightDerivedCompIso`
for the exact functor `R` against the composite `L ⋙ G`, followed by
`Stacks.Cohomology.CompositeRightDerived.compRightDerivedNatIso` peeling `L'` off, agrees with
`compRightDerivedNatIso` peeling `L` off first, then `rightDerivedCompIso` for `R` against `G`,
then `compRightDerivedNatIso` for `S`, read along `ι`.

This is what lets a comparison assembled by one engine be identified with a comparison
assembled by the other. -/
theorem rightDerivedCompIso_comp_compRightDerivedNatIso
    (e : G ⋙ R ≅ S ⋙ G') (ι : L ⋙ S ≅ L') (P : (L ⋙ G) ⋙ R ≅ L' ⋙ G')
    (hP : ∀ Z : C, P.hom.app Z = e.hom.app (L.obj Z) ≫ G'.map (ι.hom.app Z)) (p : ℕ) :
    (rightDerivedCompIso (L ⋙ G) R (L' ⋙ G') P p).hom ≫
        (compRightDerivedNatIso L' G' p).hom =
      Functor.whiskerRight (compRightDerivedNatIso L G p).hom R ≫
        Functor.whiskerLeft L (rightDerivedCompIso G R (S ⋙ G') e p).hom ≫
          Functor.whiskerLeft L (compRightDerivedNatIso S G' p).hom ≫
            Functor.whiskerRight ι.hom (G'.rightDerived p) :=
  NatTrans.ext (funext fun M =>
    rightDerivedCompIso_comp_compRightDerivedNatIso_app L G R S G' L' e ι P hP p M)

end TwoEngines

end Stacks.Cohomology.DerivedCompTransport

end
