module

public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.RepresentativeSingle
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.TopDegreePullbackCycles

/-!
# The top-degree pullback comparison on cycle classes

Let `f : X ⟶ Y` be a morphism of ringed spaces and `K` an object of the derived category of
`𝒪_Y`-modules with no cohomology above degree `d`. The isomorphism `Hᵈ(Lf^* K) ≅ f^* Hᵈ(K)` is
`Hᵈ` of `Lf^*` applied to the canonical map `κ : K ⟶ Hᵈ(K)[-d]`, followed by the degree-`d`
counit at the single complex `Hᵈ(K)[-d]`. For a representative `P` of `K` with no terms above
`d`, the pullback of the cohomology class of `P`, carried through this isomorphism and the
derived-pullback comparison at `P`, is the canonical map `f^* Hᵈ(P) ⟶ Hᵈ(f^* P)`.

In the situation of [Stacks, Tag 0EX3] this gives the description of
`topDirectImagePullbackIso` on cycle classes, for every representative of
`Rf'_*(F'[0])`.

## Main results

* `Stacks.AlgebraicGeometry.TopDegreeBaseChange.homologyDerivedPullbackSingleMap_eq`: the
  degree-`d` counit at a single complex, written in terms of the derived-pullback comparison and
  the identifications of the single functors.
* `Stacks.AlgebraicGeometry.TopDegreeBaseChange.derivedPullbackTopDegreeIsoPullback_hom`:
  `Hᵈ(Lf^* K) ≅ f^* Hᵈ(K)` is `Hᵈ(Lf^* κ)` followed by that counit.
* `Stacks.AlgebraicGeometry.TopDegreeBaseChange.representativeClass_comp_eq_mapHomology`: the
  cycle-free identity at a complex with no terms above `d`, for any morphism of ringed spaces.
* `Stacks.AlgebraicGeometry.TopDegreeBaseChange.topDirectImagePullbackIso_cycles`: the
  description of `topDirectImagePullbackIso` on cycle classes, for every representative.

## Implementation notes

`Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullbackComparison f` is a natural
transformation `Qh ⋙ Lf^* ⟶ f^*(-) ⋙ Qh`, so its component at `quot P` has target
`(f^*(-) ⋙ Qh).obj (quot P)`, which is only definitionally equal to `Qh.obj (quot (f^* P))`. A
goal mixing the two spellings is not type-correct at `implicit` transparency, and `rw`,
`simp only` and `Category.assoc` all fail on it. The geometry-free theorem
`Stacks.RepresentativeSingle.classOfRepresentative_comp_eq_mapHomology` therefore takes the two
components and the naturality square between them as hypotheses, and the naturality square is
passed in argument position, where the definitional equality is checked at default transparency.

`CochainComplex.IsStrictlyLE` is an explicit argument of `representativeClass_comp_eq_mapHomology`:
at the two definitionally equal spellings of the category of modules on a ringed space it is not
found by instance search.

`homologyDerivedPullbackSingleMap_eq` keeps the composite under one `Hᵈ`: distributing `Hᵈ` over
it by `Functor.map_comp` at the `SheafOfModules (structureSheafRing _)` spelling times out, while
distributing inside the geometry-free theorem, where the categories are abstract, is cheap.

## References

* [Stacks Project, Tag 0EX3](https://stacks.math.columbia.edu/tag/0EX3)
* [Stacks Project, Tag 0BDL](https://stacks.math.columbia.edu/tag/0BDL)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Category AlgebraicGeometry
open RingedSpaceModuleAdjunction HomologicalComplex
open Stacks.TopSingleProjection Stacks.RepresentativeHomology Stacks.RepresentativeSingle

namespace Stacks.AlgebraicGeometry.TopDegreeBaseChange

open DerivedCategory

universe u

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] RingedSpaceModuleAdjunction.preservesFiniteColimits_modulePullback

section Generic

variable {C₁ C₂ : Type*} [Category C₁] [Category C₂] [Abelian C₁] [Abelian C₂]
  (T : C₁ ⥤ C₂) [T.Additive]

/-- In every degree `n`, the component at `M` of
`CategoryTheory.Functor.mapHomotopyCategorySingleFunctor` is the image in the homotopy category
of the component of `HomologicalComplex.singleMapHomologicalComplex`. -/
theorem mapHomotopyCategorySingleFunctor_hom_app_eq (n : ℤ) (M : C₁) :
    (T.mapHomotopyCategorySingleFunctor n).hom.app M =
      (HomotopyCategory.quotient C₂ (ComplexShape.up ℤ)).map
        ((singleMapHomologicalComplex T (ComplexShape.up ℤ) n).hom.app M) := by
  have h1 : (HomotopyCategory.singleFunctorPostcompQuotientIso C₁ n).hom.app M = 𝟙 _ := rfl
  have h2 : (T.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).hom.app
      ((CochainComplex.singleFunctor C₁ n).obj M) = 𝟙 _ := rfl
  have h3 : (HomotopyCategory.singleFunctorPostcompQuotientIso C₂ n).inv.app (T.obj M)
      = 𝟙 _ := rfl
  dsimp only [Functor.mapHomotopyCategorySingleFunctor]
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app, Functor.associator_hom_app, Functor.isoWhiskerLeft_hom,
    Functor.whiskerLeft_app, Functor.associator_inv_app, Iso.symm_hom, h1, h2, h3]
  change (T.mapHomotopyCategory (ComplexShape.up ℤ)).map (𝟙 _) ≫ 𝟙 _ ≫ 𝟙 _ ≫ 𝟙 _ ≫
      (HomotopyCategory.quotient C₂ (ComplexShape.up ℤ)).map
        ((singleMapHomologicalComplex T (ComplexShape.up ℤ) n).hom.app M) ≫ 𝟙 _ ≫ 𝟙 _ = _
  refine Eq.trans (congrArg (fun g => g ≫ 𝟙 _ ≫ 𝟙 _ ≫ 𝟙 _ ≫
    (HomotopyCategory.quotient C₂ (ComplexShape.up ℤ)).map
      ((singleMapHomologicalComplex T (ComplexShape.up ℤ) n).hom.app M) ≫ 𝟙 _ ≫ 𝟙 _)
    ((T.mapHomotopyCategory (ComplexShape.up ℤ)).map_id _)) ?_
  simp only [Category.comp_id, Category.id_comp]

end Generic

section Single

variable {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]

/-- The identification `homologySingleIso N d` of `Hᵈ` of the single object `N[-d]` of the
derived category is the component at `N` of `DerivedCategory.singleFunctorCompHomologyFunctorIso`.
-/
theorem homologySingleIso_hom (N : C) (d : ℤ) :
    (homologySingleIso N d).hom =
      (singleFunctorCompHomologyFunctorIso C d).hom.app N :=
  (singleFunctorCompHomologyFunctorIso_hom_app N d).symm

end Single

section Geometry

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)

/-- The degree-`d` counit `homologyDerivedPullbackSingleMap f M d` at the single complex `M[-d]`
is `Hᵈ` of the composite of `Lf^*` applied to the identification of single functors, the
derived-pullback comparison
`Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullbackComparison f` at `M[-d]`, the
degreewise comparison of single complexes, and the inverse identification of single functors,
followed by the identification of `Hᵈ` of a single complex. -/
theorem homologyDerivedPullbackSingleMap_eq (M : SheafOfModules.{u} (structureSheafRing Y))
    (d : ℤ) :
    homologyDerivedPullbackSingleMap f M d =
      (homologyFunctor (SheafOfModules.{u} (structureSheafRing X)) d).map
          ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback f).map
              ((singleFunctorIsoCompQh (SheafOfModules.{u} (structureSheafRing Y)) d).hom.app M) ≫
            (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullbackComparison f).app
              ((HomotopyCategory.singleFunctor (SheafOfModules.{u} (structureSheafRing Y)) d).obj
                M) ≫
            DerivedCategory.Qh.map
              ((HomotopyCategory.quotient (SheafOfModules.{u} (structureSheafRing X))
                (ComplexShape.up ℤ)).map
                ((singleMapHomologicalComplex (modulePullback f)
                  (ComplexShape.up ℤ) d).hom.app M)) ≫
            (singleFunctorIsoCompQh (SheafOfModules.{u} (structureSheafRing X)) d).inv.app
              ((modulePullback f).obj M)) ≫
        (singleFunctorCompHomologyFunctorIso (SheafOfModules.{u} (structureSheafRing X)) d).hom.app
          ((modulePullback f).obj M) := by
  rw [homologyDerivedPullbackSingleMap, derivedToOrdinaryPullbackSingle,
    mapHomotopyCategorySingleFunctor_hom_app_eq, homologySingleIso_hom]
  rfl

/-- The isomorphism `Hᵈ(Lf^* K) ≅ f^* Hᵈ(K)` of `derivedPullbackTopDegreeIsoPullback` is `Hᵈ`
of `Lf^*` applied to the canonical map `κ : K ⟶ Hᵈ(K)[-d]`, followed by the degree-`d` counit at
that single complex. This is the step displayed in [Stacks, Tag 0EX3]. -/
theorem derivedPullbackTopDegreeIsoPullback_hom
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing Y))) (d : ℤ)
    (hK : TStructure.t.IsLE K d) :
    (derivedPullbackTopDegreeIsoPullback f K d hK).hom =
      (homologyFunctor (SheafOfModules.{u} (structureSheafRing X)) d).map
          ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback f).map
            ((TStructure.t.truncGEπ d).app K ≫ (truncGEIsoSingleHomology K d hK).hom)) ≫
        homologyDerivedPullbackSingleMap f
          ((homologyFunctor (SheafOfModules.{u} (structureSheafRing Y)) d).obj K) d := by
  have h0 : (derivedPullbackTopDegreeIsoPullback f K d hK).hom =
      ((homologyFunctor (SheafOfModules.{u} (structureSheafRing X)) d).map
            ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback f).map
              ((TStructure.t.truncGEπ d).app K)) ≫
          (homologyFunctor (SheafOfModules.{u} (structureSheafRing X)) d).map
            ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback f).map
              (truncGEIsoSingleHomology K d hK).hom)) ≫
        homologyDerivedPullbackSingleMap f
          ((homologyFunctor (SheafOfModules.{u} (structureSheafRing Y)) d).obj K) d := rfl
  rw [h0]
  exact congrArg (fun z => z ≫ homologyDerivedPullbackSingleMap f
      ((homologyFunctor (SheafOfModules.{u} (structureSheafRing Y)) d).obj K) d)
    ((congrArg ((homologyFunctor (SheafOfModules.{u} (structureSheafRing X)) d).map)
        ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback f).map_comp _ _)).trans
      ((homologyFunctor (SheafOfModules.{u} (structureSheafRing X)) d).map_comp _ _)).symm

/-- For a representative `P` of `K` with no terms above `d`, the pullback of the cohomology
class of `P`, carried through the inverse of the top-degree comparison and the derived-pullback
comparison at `P`, is the canonical comparison `Stacks.MapHomologyCycles.mapHomology`. -/
theorem representativeClass_comp_eq_mapHomology
    (P : CochainComplex (SheafOfModules.{u} (structureSheafRing Y)) ℤ) (d : ℤ)
    (hP : P.IsStrictlyLE d)
    {K : DerivedCategory (SheafOfModules.{u} (structureSheafRing Y))}
    (e : DerivedCategory.Qh.obj
      ((HomotopyCategory.quotient (SheafOfModules.{u} (structureSheafRing Y))
        (ComplexShape.up ℤ)).obj P) ≅ K)
    (hK : TStructure.t.IsLE K d) :
    (modulePullback f).map (classOfRepresentative P e d) ≫
        (derivedPullbackTopDegreeIsoPullback f K d hK).inv ≫
        comparisonOfRepresentative (modulePullback f)
          (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback f)
          (fun P => (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullbackComparison
            f).app
            ((HomotopyCategory.quotient (SheafOfModules.{u} (structureSheafRing Y))
              (ComplexShape.up ℤ)).obj P)) P e d =
      Stacks.MapHomologyCycles.mapHomology (modulePullback f) P d :=
  have := hP
  classOfRepresentative_comp_eq_mapHomology (modulePullback f)
    (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback f) P d e
    (toSingleTop P d ≫ (HomologicalComplex.single (SheafOfModules.{u} (structureSheafRing Y))
      (ComplexShape.up ℤ) d).map (classOfRepresentative P e d)) rfl
    ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullbackComparison f).app
      ((HomotopyCategory.quotient (SheafOfModules.{u} (structureSheafRing Y))
        (ComplexShape.up ℤ)).obj P))
    ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullbackComparison f).app
      ((HomotopyCategory.singleFunctor (SheafOfModules.{u} (structureSheafRing Y)) d).obj
        ((homologyFunctor (SheafOfModules.{u} (structureSheafRing Y)) d).obj K)))
    ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullbackComparison f).naturality _)
    (homologyDerivedPullbackSingleMap f
      ((homologyFunctor (SheafOfModules.{u} (structureSheafRing Y)) d).obj K) d)
    (homologyDerivedPullbackSingleMap_eq f _ d)
    ((TStructure.t.truncGEπ d).app K ≫ (truncGEIsoSingleHomology K d hK).hom)
    (eq_truncGEπ_comp P d e (truncGEIsoSingleHomology K d hK)
      (Stacks.TruncGESingleHomology.homologyMap_truncGEπ_truncGELTIso K d
        ((TStructure.t.isLE_iff_isIso_truncLTι_app d (d + 1) rfl K).1 hK)))
    (derivedPullbackTopDegreeIsoPullback f K d hK).symm
    (derivedPullbackTopDegreeIsoPullback_hom f K d hK)
    (comparisonOfRepresentative (modulePullback f)
      (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback f)
      (fun P => (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullbackComparison f).app
        ((HomotopyCategory.quotient (SheafOfModules.{u} (structureSheafRing Y))
          (ComplexShape.up ℤ)).obj P)) P e d) rfl

end Geometry

section Card

variable (S : Stacks.AlgebraicGeometry.TopDegreeBaseChangeSituation.{u})
  (F' : S.X'.Modules) [F'.IsQuasicoherent] {Y'' : Scheme.{u}} (h : Y'' ⟶ S.Y')

/-- In the base-change situation, for a representative `P` of `Rf'_*(F'[0])` with no terms above
`d`, the pullback of the cohomology class of `P` in degree `d`, carried through
`topDirectImagePullbackIso` and the comparison at `P`, is the canonical comparison
`Stacks.MapHomologyCycles.mapHomology`. The bound on the cohomology of `Rf'_*(F'[0])` is
conclusion (a) of [Stacks, Tag 0EX3], `isLE_derivedPushforward_baseChange`. -/
theorem representativeClass_comp_eq_mapHomology_baseChange
    (P : CochainComplex S.Y'.Modules ℤ) (hP : P.IsStrictlyLE (S.d : ℤ))
    (e : (DerivedCategory.Qh.obj ((HomotopyCategory.quotient S.Y'.Modules
        (ComplexShape.up ℤ)).obj P) : DerivedCategory S.Y'.Modules) ≅
      (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforward
        S.f'.toLRSHom.toShHom).obj
        ((singleFunctor S.X'.Modules 0).obj F')) :
    (modulePullback h.toLRSHom.toShHom).map (representativeClass P e (S.d : ℤ)) ≫
        (topDirectImagePullbackIso S F' h).hom ≫
        homologyPullbackRepresentativeComparison h P e (S.d : ℤ) =
      Stacks.MapHomologyCycles.mapHomology (modulePullback h.toLRSHom.toShHom) P (S.d : ℤ) :=
  representativeClass_comp_eq_mapHomology h.toLRSHom.toShHom P (S.d : ℤ) hP e
    (isLE_derivedPushforward_baseChange S F')

/-- In the base-change situation, for every representative `P` of `Rf'_*(F'[0])`, the pullback
of the cycle class of `P` in degree `d`, carried through `topDirectImagePullbackIso` and the
comparison at `P`, is the class in `Hᵈ(h^* P)` of the pullback of the cycles of `P`.

Not tagged: by the covering-set rule this is not a conclusion of [Stacks, Tag 0EX3]. The
comparison and its description on cycle classes are introduced by the source while explaining
what conclusion (c) means, and are not among the tag's conclusions (a), (b), (c). -/
theorem topDirectImagePullbackIso_cycles (P : CochainComplex S.Y'.Modules ℤ)
    (e : (DerivedCategory.Qh.obj ((HomotopyCategory.quotient S.Y'.Modules
        (ComplexShape.up ℤ)).obj P) : DerivedCategory S.Y'.Modules) ≅
      (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforward
        S.f'.toLRSHom.toShHom).obj
        ((singleFunctor S.X'.Modules 0).obj F')) :
    (modulePullback h.toLRSHom.toShHom).map
          (P.homologyπ (S.d : ℤ) ≫ representativeClass P e (S.d : ℤ)) ≫
        (topDirectImagePullbackIso S F' h).hom ≫
        homologyPullbackRepresentativeComparison h P e (S.d : ℤ) =
      Stacks.MapHomologyCycles.mapCycles (modulePullback h.toLRSHom.toShHom) P (S.d : ℤ) ≫
        (((modulePullback h.toLRSHom.toShHom).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj P).homologyπ (S.d : ℤ) := by
  have hPLE : CochainComplex.IsLE P (S.d : ℤ) :=
    Stacks.RepresentativeSingle.isLE_of_representative P (S.d : ℤ) e
      (isLE_derivedPushforward_baseChange S F')
  have hT : CochainComplex.IsStrictlyLE (P.truncLE (S.d : ℤ)) (S.d : ℤ) := inferInstance
  exact (topDirectImagePullbackIso_cycles_iff S F' h P e).2
    (representativeClass_comp_eq_mapHomology_of_truncLE
      h P e (S.d : ℤ) (topDirectImagePullbackIso S F' h).hom
      (representativeClass_comp_eq_mapHomology_baseChange S F' h (P.truncLE (S.d : ℤ)) hT
        (truncLERepresentative P e (S.d : ℤ))))

end Card

end Stacks.AlgebraicGeometry.TopDegreeBaseChange

end
