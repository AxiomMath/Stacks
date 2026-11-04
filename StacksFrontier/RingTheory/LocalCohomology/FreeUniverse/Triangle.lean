module

public import StacksFrontier.RingTheory.LocalCohomology.FreeUniverse.Comparison
public import StacksFrontier.RingTheory.LocalCohomology.LocalizationTriangle

/-!
# The affine localization triangle in a free module universe

Let `I = (f₁, …, f_r)` be a finitely generated ideal of a commutative ring `R` in `Type u` and let
`M` be an `R`-module in `Type v`, with `v` *independent* of `u`. This file assembles the
localization triangle
`RΓ_{V(I)}(M) ⟶ M ⟶ RΓ(U, M̃|U) ⟶ RΓ_{V(I)}(M)[1]`
of `U = Spec R \ V(I)` out of the small model of the Čech complex: derived sections on `U` are
the cone of the small Čech augmentation, the second map is the inclusion of `M` into that cone,
the third is the connecting map transported through the natural comparison
`Stacks.LocalCohomology.localCohomologyIsoCechShrink`, and the triangle is distinguished with the
counit of Stacks 0A6Q as its first map, functorially in `M`.

This is `StacksFrontier/RingTheory/LocalCohomology/LocalizationTriangle.lean` with the constraint
`ModuleCat.{max u v}` removed, and it supplies **four of the seven fields** of
`Stacks.LocalCohomology.LocalizationTriangleData.{u, v}`. The remaining three —
`sectionsIso`, `sectionsIso_naturality` and `restriction_eq` — are the degree-zero comparison of
the cohomology of derived sections with the sections of the associated sheaf on `U`, and they are
taken as hypotheses by
`Stacks.LocalCohomology.localizationTriangleDataOfSectionsIsoShrink` below, exactly as
`Stacks.LocalCohomology.localizationTriangleDataOfSectionsIso` takes them at the pinned
universe. Their proofs at the pinned universe are the eight files of
`StacksFrontier/RingTheory/LocalCohomology/SectionsIso/`, which are *not* transported here.

## Main definitions

* `Stacks.LocalCohomology.cechConeFunctorShrink`,
  `Stacks.LocalCohomology.cechComplementFunctorShrink` — **derived sections on
  `U = Spec R \ V(I)` as a functor of the module**, at a free module universe: the cone of the
  small Čech augmentation.
* `Stacks.LocalCohomology.cechRestrictionShrink`,
  `Stacks.LocalCohomology.cechBoundaryShrink` — the second and third maps of the triangle, as
  natural transformations.

## Main results

* `Stacks.LocalCohomology.cechLocalizationTriangleShrink_distinguished` — **the localization
  triangle is distinguished at a module universe independent of the ring universe**, with the
  counit of Stacks 0A6Q as its first map, for every module simultaneously.
* `Stacks.LocalCohomology.localizationTriangleDataOfSectionsIsoShrink` — what remains of
  Stacks 0DWR at a free module universe: given the degree-zero sections comparison, its
  naturality and the formula `m ↦ m/1`, a term of
  `Stacks.LocalCohomology.LocalizationTriangleData.{u, v}` exists.

## References

* [Stacks Project, Tag 0DWR](https://stacks.math.columbia.edu/tag/0DWR)
* [Stacks Project, Tag 0A6Q](https://stacks.math.columbia.edu/tag/0A6Q)
* [Stacks Project, Tag 0A6R](https://stacks.math.columbia.edu/tag/0A6R)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite
open AlgebraicGeometry

attribute [local instance] HasDerivedCategory.standard

universe v u

namespace Stacks.LocalCohomology

variable {R : Type u} [CommRing R] {r : ℕ} (f : Fin r → R) (I : Ideal R) (hI : I.FG)

/-! ### Derived sections on the complement -/

/-- The cone of the small Čech augmentation `C^•(f₁, …, f_r; M) ⟶ M⟦0⟧`, as a functor of the
module. -/
def cechConeFunctorShrink : ModuleCat.{v} R ⥤ CochainComplex (ModuleCat.{v} R) ℤ where
  obj M := CochainComplex.mappingCone (extendedCechAugmentationShrink.{v} f M)
  map {M N} g := CochainComplex.mappingCone.map _ _ (Cech.extendedCechComplexShrinkMap.{v} f g)
    ((CochainComplex.singleFunctor (ModuleCat.{v} R) 0).map g)
    (extendedCechAugmentationShrink_naturality.{v} f g).symm
  map_id M :=
    (mappingCone_map_congr _ _ (Cech.extendedCechComplexShrinkMap_id.{v} f)
      ((CochainComplex.singleFunctor (ModuleCat.{v} R) 0).map_id M) _ _).trans
      (CochainComplex.mappingCone.map_id _)
  map_comp {M N P} g h := by
    refine Eq.trans ?_ (CochainComplex.mappingCone.map_comp
      (extendedCechAugmentationShrink.{v} f M) (extendedCechAugmentationShrink.{v} f N)
      (extendedCechAugmentationShrink.{v} f P)
      (Cech.extendedCechComplexShrinkMap.{v} f g)
      ((CochainComplex.singleFunctor (ModuleCat.{v} R) 0).map g)
      (extendedCechAugmentationShrink_naturality.{v} f g).symm
      (Cech.extendedCechComplexShrinkMap.{v} f h)
      ((CochainComplex.singleFunctor (ModuleCat.{v} R) 0).map h)
      (extendedCechAugmentationShrink_naturality.{v} f h).symm)
    exact mappingCone_map_congr _ _ (Cech.extendedCechComplexShrinkMap_comp.{v} f g h)
      ((CochainComplex.singleFunctor (ModuleCat.{v} R) 0).map_comp g h) _ _

/-- The cone functor at a module is the mapping cone of the small augmentation. -/
@[simp] theorem cechConeFunctorShrink_obj (M : ModuleCat.{v} R) :
    (cechConeFunctorShrink.{v} f).obj M =
      CochainComplex.mappingCone (extendedCechAugmentationShrink.{v} f M) :=
  rfl

/-- The cone functor on a module map is the map of cones induced by the naturality square. -/
@[simp] theorem cechConeFunctorShrink_map {M N : ModuleCat.{v} R} (g : M ⟶ N) :
    (cechConeFunctorShrink.{v} f).map g = CochainComplex.mappingCone.map _ _
      (Cech.extendedCechComplexShrinkMap.{v} f g)
      ((CochainComplex.singleFunctor (ModuleCat.{v} R) 0).map g)
      (extendedCechAugmentationShrink_naturality.{v} f g).symm :=
  rfl

/-- **Derived sections on `U = Spec R \ V(I)` at a free module universe**, as a functor of the
module: the cone of the small Čech augmentation, viewed in the derived category. This is the
third term of the localization triangle. -/
def cechComplementFunctorShrink :
    ModuleCat.{v} R ⥤ DerivedCategory (ModuleCat.{v} R) :=
  cechConeFunctorShrink.{v} f ⋙ DerivedCategory.Q

/-- The inclusion of the module, placed in degree zero, into the cone of the small
augmentation. -/
def cechConeInrShrink (M : ModuleCat.{v} R) :
    (CochainComplex.singleFunctor (ModuleCat.{v} R) 0).obj M ⟶
      (cechConeFunctorShrink.{v} f).obj M :=
  CochainComplex.mappingCone.inr (extendedCechAugmentationShrink.{v} f M)

/-- The connecting map of the cone of the small augmentation. -/
def cechConeDeltaShrink (M : ModuleCat.{v} R) :
    (cechConeFunctorShrink.{v} f).obj M ⟶
      (Cech.extendedCechComplexShrink.{v} f (M : Type v))⟦(1 : ℤ)⟧ :=
  (CochainComplex.mappingCone.triangle (extendedCechAugmentationShrink.{v} f M)).mor₃

/-- The map of cone triangles induced by a module map. -/
private def cechConeTriangleMapShrink {M N : ModuleCat.{v} R} (g : M ⟶ N) :
    CochainComplex.mappingCone.triangle (extendedCechAugmentationShrink.{v} f M) ⟶
      CochainComplex.mappingCone.triangle (extendedCechAugmentationShrink.{v} f N) :=
  CochainComplex.mappingCone.triangleMap (extendedCechAugmentationShrink.{v} f M)
    (extendedCechAugmentationShrink.{v} f N) (Cech.extendedCechComplexShrinkMap.{v} f g)
    ((CochainComplex.singleFunctor (ModuleCat.{v} R) 0).map g)
    (extendedCechAugmentationShrink_naturality.{v} f g).symm

/-- The inclusion into the cone is natural in the module. -/
theorem cechConeInrShrink_naturality {M N : ModuleCat.{v} R} (g : M ⟶ N) :
    (CochainComplex.singleFunctor (ModuleCat.{v} R) 0).map g ≫ cechConeInrShrink.{v} f N =
      cechConeInrShrink.{v} f M ≫ (cechConeFunctorShrink.{v} f).map g :=
  (cechConeTriangleMapShrink.{v} f g).comm₂.symm

/-- The connecting map of the cone is natural in the module. -/
theorem cechConeDeltaShrink_naturality {M N : ModuleCat.{v} R} (g : M ⟶ N) :
    (cechConeFunctorShrink.{v} f).map g ≫ cechConeDeltaShrink.{v} f N =
      cechConeDeltaShrink.{v} f M ≫ (Cech.extendedCechComplexShrinkMap.{v} f g)⟦(1 : ℤ)⟧' :=
  (cechConeTriangleMapShrink.{v} f g).comm₃.symm

/-- The comparison of the two descriptions of a module placed in degree zero: the object of the
derived category, and the single cochain complex. -/
def singleIsoQShrink (M : ModuleCat.{v} R) :
    (DerivedCategory.singleFunctor (ModuleCat.{v} R) 0).obj M ≅
      DerivedCategory.Q.obj ((CochainComplex.singleFunctor (ModuleCat.{v} R) 0).obj M) :=
  (DerivedCategory.singleFunctorIsoCompQ (ModuleCat.{v} R) 0).app M

/-- The comparison of the two descriptions of a module in degree zero is natural. -/
theorem singleIsoQShrink_naturality {M N : ModuleCat.{v} R} (g : M ⟶ N) :
    (DerivedCategory.singleFunctor (ModuleCat.{v} R) 0).map g ≫
        (singleIsoQShrink.{v} (R := R) N).hom =
      (singleIsoQShrink.{v} (R := R) M).hom ≫ DerivedCategory.Q.map
        ((CochainComplex.singleFunctor (ModuleCat.{v} R) 0).map g) :=
  (DerivedCategory.singleFunctorIsoCompQ (ModuleCat.{v} R) 0).hom.naturality g

/-! ### The maps of the triangle -/

/-- The second map of the localization triangle at a free module universe: the inclusion of
`M⟦0⟧` into the cone of the small augmentation. It is the map inducing restriction of sections
to `U`. -/
def cechRestrictionShrink :
    DerivedCategory.singleFunctor (ModuleCat.{v} R) 0 ⟶ cechComplementFunctorShrink.{v} f where
  app M := (singleIsoQShrink.{v} (R := R) M).hom ≫
    DerivedCategory.Q.map (cechConeInrShrink.{v} f M)
  naturality M N g := by
    have h := cechConeInrShrink_naturality.{v} f g
    dsimp only [cechComplementFunctorShrink, Functor.comp_map]
    rw [← Category.assoc, singleIsoQShrink_naturality, Category.assoc, Category.assoc,
      ← DerivedCategory.Q.map_comp, ← DerivedCategory.Q.map_comp, h]

/-- The small augmentation in the derived category, written through the comparison with the
single complex. -/
theorem Q_map_extendedCechAugmentationShrink (M : ModuleCat.{v} R) :
    DerivedCategory.Q.map (extendedCechAugmentationShrink.{v} f M) =
      (cechAugmentationHomShrink.{v} f).app M ≫ (singleIsoQShrink.{v} (R := R) M).hom := by
  rw [cechAugmentationHomShrink_app, extendedCechAugmentationHomShrink]
  simp [singleIsoQShrink]

variable (hIf : Ideal.span (Set.range f) = I)

/-- The comparison of local cohomology with the small Čech object, at a module. -/
def cechComparisonIsoShrink (M : ModuleCat.{v} R) :
    (localCohomologyOnModules.{u, v} R I hI).obj M ≅
      DerivedCategory.Q.obj (Cech.extendedCechComplexShrink.{v} f (M : Type v)) :=
  (localCohomologyIsoCechShrink.{v} f I hI hIf).app M

/-- The comparison of the small Čech object with local cohomology is natural in the module. -/
theorem cechComparisonIsoShrink_inv_naturality {M N : ModuleCat.{v} R} (g : M ⟶ N) :
    DerivedCategory.Q.map (Cech.extendedCechComplexShrinkMap.{v} f g) ≫
        (cechComparisonIsoShrink.{v} f I hI hIf N).inv =
      (cechComparisonIsoShrink.{v} f I hI hIf M).inv ≫
        (localCohomologyOnModules.{u, v} R I hI).map g :=
  (localCohomologyIsoCechShrink.{v} f I hI hIf).inv.naturality g

/-- The comparison carries the counit of Stacks 0A6Q to the small Čech augmentation. -/
theorem cechComparisonIsoShrink_hom_comp_augmentation (M : ModuleCat.{v} R) :
    (cechComparisonIsoShrink.{v} f I hI hIf M).hom ≫ (cechAugmentationHomShrink.{v} f).app M =
      (Dualizing.localCohomologyAdjunction R I hI).counit.app
        ((DerivedCategory.singleFunctor (ModuleCat.{v} R) 0).obj M) :=
  cechComparisonHomShrink_comp_augmentation.{v} f I hI hIf M

/-- The third map of the localization triangle at a free module universe: the connecting map from
derived sections on `U` to `RΓ_{V(I)}(M)[1]`, transported through the comparison of local
cohomology with the small Čech object. -/
def cechBoundaryShrink :
    cechComplementFunctorShrink.{v} f ⟶ localCohomologyOnModules.{u, v} R I hI ⋙
      shiftFunctor (DerivedCategory (ModuleCat.{v} R)) (1 : ℤ) where
  app M := DerivedCategory.Q.map (cechConeDeltaShrink.{v} f M) ≫
    (DerivedCategory.Q.commShiftIso (1 : ℤ)).hom.app
        (Cech.extendedCechComplexShrink.{v} f (M : Type v)) ≫
      ((cechComparisonIsoShrink.{v} f I hI hIf M).inv)⟦(1 : ℤ)⟧'
  naturality M N g := by
    have h := cechConeDeltaShrink_naturality.{v} f g
    have hcs : DerivedCategory.Q.map ((shiftFunctor (CochainComplex (ModuleCat.{v} R) ℤ)
            (1 : ℤ)).map (Cech.extendedCechComplexShrinkMap.{v} f g)) ≫
          (DerivedCategory.Q.commShiftIso (1 : ℤ)).hom.app
            (Cech.extendedCechComplexShrink.{v} f (N : Type v)) =
        (DerivedCategory.Q.commShiftIso (1 : ℤ)).hom.app
            (Cech.extendedCechComplexShrink.{v} f (M : Type v)) ≫
          (DerivedCategory.Q.map (Cech.extendedCechComplexShrinkMap.{v} f g))⟦(1 : ℤ)⟧' :=
      (DerivedCategory.Q.commShiftIso (1 : ℤ)).hom.naturality
        (Cech.extendedCechComplexShrinkMap.{v} f g)
    have hshift := congrArg
      (fun φ => (shiftFunctor (DerivedCategory (ModuleCat.{v} R)) (1 : ℤ)).map φ)
      (cechComparisonIsoShrink_inv_naturality.{v} f I hI hIf g)
    simp only [Functor.map_comp] at hshift
    dsimp only [cechComplementFunctorShrink, Functor.comp_map]
    rw [← DerivedCategory.Q.map_comp_assoc, h, DerivedCategory.Q.map_comp]
    simp only [Category.assoc]
    rw [reassoc_of% hcs, hshift]
    rfl

/-! ### The triangle -/

/-- **Stacks 0DWR, the localization triangle, at a module universe independent of the ring
universe.** For a finitely generated ideal `I = (f₁, …, f_r)` of `R` and an `R`-module `M` in
`Type v`, the triangle
`RΓ_{V(I)}(M) ⟶ M ⟶ RΓ(U, M̃|U) ⟶ RΓ_{V(I)}(M)[1]`
is distinguished in `D(ModuleCat.{v} R)`, where the first map is the counit of the
local-cohomology adjunction of Stacks 0A6Q, the second is
`Stacks.LocalCohomology.cechRestrictionShrink` and the third is
`Stacks.LocalCohomology.cechBoundaryShrink`. All three terms and both maps are functorial
in `M`.

This carries no `@[stacks 0DWR]` attribute: tag 0DWR is the five-term exact sequence, whose
remaining ingredient — the identification of `H⁰` of the third term with the sections of the
associated sheaf on `U` — is not proved here. -/
theorem cechLocalizationTriangleShrink_distinguished (M : ModuleCat.{v} R) :
    Triangle.mk ((Dualizing.localCohomologyAdjunction R I hI).counit.app
        ((DerivedCategory.singleFunctor (ModuleCat.{v} R) 0).obj M))
      ((cechRestrictionShrink.{v} f).app M)
      ((cechBoundaryShrink.{v} f I hI hIf).app M) ∈ distTriang _ := by
  refine isomorphic_distinguished _
    (DerivedCategory.mappingCone_triangle_distinguished
      (extendedCechAugmentationShrink.{v} f M)) _ ?_
  refine Triangle.isoMk _ _ (cechComparisonIsoShrink.{v} f I hI hIf M)
    (singleIsoQShrink.{v} (R := R) M) (Iso.refl _) ?_ ?_ ?_
  · show (Dualizing.localCohomologyAdjunction R I hI).counit.app
        ((DerivedCategory.singleFunctor (ModuleCat.{v} R) 0).obj M) ≫
        (singleIsoQShrink.{v} (R := R) M).hom =
      (cechComparisonIsoShrink.{v} f I hI hIf M).hom ≫
        DerivedCategory.Q.map (extendedCechAugmentationShrink.{v} f M)
    rw [Q_map_extendedCechAugmentationShrink]
    exact (congrArg (fun x => x ≫ (singleIsoQShrink.{v} (R := R) M).hom)
      (cechComparisonIsoShrink_hom_comp_augmentation.{v} f I hI hIf M)).symm.trans
      (Category.assoc _ _ _)
  · show (cechRestrictionShrink.{v} f).app M ≫ (Iso.refl _).hom =
      (singleIsoQShrink.{v} (R := R) M).hom ≫
        DerivedCategory.Q.map (cechConeInrShrink.{v} f M)
    rw [Iso.refl_hom, Category.comp_id]
    rfl
  · show (cechBoundaryShrink.{v} f I hI hIf).app M ≫
        ((cechComparisonIsoShrink.{v} f I hI hIf M).hom)⟦(1 : ℤ)⟧' =
      (Iso.refl _).hom ≫ DerivedCategory.Q.map (cechConeDeltaShrink.{v} f M) ≫
        (DerivedCategory.Q.commShiftIso (1 : ℤ)).hom.app
          (Cech.extendedCechComplexShrink.{v} f (M : Type v))
    rw [Iso.refl_hom, Category.id_comp]
    show (DerivedCategory.Q.map (cechConeDeltaShrink.{v} f M) ≫
        (DerivedCategory.Q.commShiftIso (1 : ℤ)).hom.app
            (Cech.extendedCechComplexShrink.{v} f (M : Type v)) ≫
          ((cechComparisonIsoShrink.{v} f I hI hIf M).inv)⟦(1 : ℤ)⟧') ≫
        ((cechComparisonIsoShrink.{v} f I hI hIf M).hom)⟦(1 : ℤ)⟧' = _
    simp only [Category.assoc, ← Functor.map_comp, Iso.inv_hom_id]
    rw [CategoryTheory.Functor.map_id]
    exact congrArg (DerivedCategory.Q.map (cechConeDeltaShrink.{v} f M) ≫ ·)
      (Category.comp_id _)

/-! ### Reduction of the localization triangle data to the sections comparison -/

/-- **What remains of Stacks 0DWR at a free module universe.** Given the degree-zero comparison
of the cohomology of derived sections on `U` with the sections of the associated sheaf — its
existence, its naturality, and the formula `m ↦ m/1` — the full
`Stacks.LocalCohomology.LocalizationTriangleData.{u, v}` follows for a module universe `v`
independent of the ring universe: the functor of derived sections, the two natural
transformations and the distinguished triangle are supplied by this file.

Together with `Stacks.LocalCohomology.cechLocalizationTriangleShrink_distinguished` this says
exactly what is left to prove for the low-degree exact sequence at an independent module
universe: the three hypotheses below. They are the hypotheses of
`Stacks.LocalCohomology.localizationTriangleDataOfSectionsIso`, with the small model of the Čech
complex in place of the pinned one; the sheaf side of each statement is unchanged, since the
sections of the associated sheaf live in `Type (max u v)` in either case. -/
def localizationTriangleDataOfSectionsIsoShrink
    (sectionsIso : ∀ M : ModuleCat.{v} R,
      (DerivedCategory.homologyFunctor (ModuleCat.{v} R) 0).obj
          ((cechComplementFunctorShrink.{v} f).obj M) ≃ₗ[R]
        complementGlobalSections R I (complementTilde R I M))
    (sectionsIso_naturality : ∀ {M N : ModuleCat.{v} R} (g : M ⟶ N)
      (x : (DerivedCategory.homologyFunctor (ModuleCat.{v} R) 0).obj
        ((cechComplementFunctorShrink.{v} f).obj M)),
      sectionsIso N ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) 0).map
          ((cechComplementFunctorShrink.{v} f).map g) x) =
        (associatedAbPresheafMap g).app
          (op ((complementZeroLocus R I).ι ''ᵁ ⊤)) (sectionsIso M x))
    (restriction_eq : ∀ (M : ModuleCat.{v} R) (m : M),
      sectionsIso M ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) 0).map
        ((cechRestrictionShrink.{v} f).app M)
          ((DerivedCategory.singleFunctorCompHomologyFunctorIso
            (ModuleCat.{v} R) 0).inv.app M m)) =
        ⟨fun x ↦ LocalizedModule.mk m (1 : x.1.asIdeal.primeCompl),
          fun x ↦ ⟨_, x.2, 𝟙 _, m, 1, fun y ↦ ⟨by simp [Ideal.IsPrime.one_notMem], rfl⟩⟩⟩) :
    LocalizationTriangleData.{u, v} R I hI where
  complement := cechComplementFunctorShrink.{v} f
  restriction := cechRestrictionShrink.{v} f
  boundary := cechBoundaryShrink.{v} f I hI hIf
  distinguished M := cechLocalizationTriangleShrink_distinguished.{v} f I hI hIf M
  sectionsIso := sectionsIso
  sectionsIso_naturality := sectionsIso_naturality
  restriction_eq := restriction_eq

end Stacks.LocalCohomology

end
