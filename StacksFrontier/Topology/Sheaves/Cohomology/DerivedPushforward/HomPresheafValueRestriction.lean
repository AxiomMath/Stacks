module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.SectionsIsoOpenNaturalityDerived
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.ConnectivityOnABasis
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.PreimageSectionsKInjectiveRestrict

/-!
# `Ext` on an open in degree zero is compatible with restriction

Let `(X, 𝒪_X)` be a ringed space and let `K`, `L` be objects of the derived category `D(𝒪_X)`.
`Stacks.SheafOfModules.homSheafComplexSectionHomologyEquiv` identifies the degree-`n` cohomology
of the sections over an open `U` of the internal Hom complex of `K` and `L` with
`Ext^n(K|_U, L|_U)`; this is [Stacks, Tag 08DK] in every degree.  This file proves that in degree
zero, with the degree-zero shift of the target normalised away, that identification is compatible
with restriction along an inclusion `g : W ⟶ V` of opens, the restriction of a morphism of
derived categories being `AlgebraicGeometry.RingedSite.restrictDerivedHom`.

## Main results

* `Stacks.SheafOfModules.homSheafComplexSectionHomologyEquiv_zero_restrict`: **the square.**
* `Stacks.SheafOfModules.sheafHomComplexSectionHomologyEquivShiftedHom_zero_restrict`: the same
  square at the chosen complexes themselves, before the comparison of a representative with the
  object it represents is put in.
* `Stacks.SheafOfModules.sheafHomComplexSectionHomologyEquivShiftedHom_zero`: the degree-zero
  case of Tag 08DK at a K-injective target, with the shift normalised, **is** the identification
  of [Stacks, Tag 0A94].  This is what makes the naturality in the object of the site already
  proved for 0A94 —
  `AlgebraicGeometry.RingedSite.sheafHomSectionHomologyEquivDerivedCategoryHom_restrict` —
  available to the degree-`n` identification that Tag 0D66(2) is written with.
* `AlgebraicGeometry.RingedSite.homotopyHomDerivedCategoryEquiv_shiftFunctorZero`: the identity
  behind the previous item — normalising a degree-zero shift commutes with the bijectivity of the
  localisation functor on morphisms into a K-injective complex.
* `Stacks.DerivedCategoryComparisons.Q_map_shiftFunctorZero_hom_app`: the localisation functor
  carries the degree-zero shift normalisation of complexes to the one of the derived category.
* `Stacks.DerivedCategoryComparisons.homCongr_shiftFunctorZero_restrict`: the restriction square
  for degree-zero shifted morphisms conjugated by isomorphisms, with every object and every map a
  variable.

## Implementation notes

The identification of Tag 08DK in degree `n` and the identification of Tag 0A94 are built from
the same Tag 0A8Y comparison, but they normalise the shift at different places: 0A94 normalises
it on the K-injective complex, inside the homotopy category, whereas the degree-`n` statement
carries it to the derived category by `DerivedCategory.Q.commShiftIso` and normalises it there.
At `n = 0` the two agree, and that is
`Stacks.SheafOfModules.sheafHomComplexSectionHomologyEquivShiftedHom_zero`; its content is the
degree-zero compatibility of a `CategoryTheory.Functor.CommShift`, which is
`Stacks.DerivedCategoryComparisons.Q_map_shiftFunctorZero_hom_app`.  Without it the naturality
already available for 0A94 cannot be quoted at all, since the two identifications are different
constants.

*Why the two bookkeeping lemmas have every object a variable.*  The statements of this file cross
the two spellings `Stacks.SheafOfModules.sectionComplex` and
`AlgebraicGeometry.RingedSite.sectionComplex` of the complex of sections, which are definitionally
equal but expensive to unify.  The budget allows about one such crossing per declaration: a
`rw` whose pattern has to be matched up to that crossing exhausts the heartbeats, while an
`exact` or a `refine Eq.trans _ ?_`, which pays a single definitional unification at `default`
transparency, succeeds in seconds.  So every step is stated as its own lemma with the objects and
morphisms variables and applied by `exact` — in particular
`Stacks.DerivedCategoryComparisons.homCongr_shiftFunctorZero_restrict`, which is the whole shape
of the square with no sheaf, no site and no derived category in it, so that its consumer pays the
crossing once.

## References

* [Stacks Project, Tag 08DK](https://stacks.math.columbia.edu/tag/08DK)
* [Stacks Project, Tag 0A94](https://stacks.math.columbia.edu/tag/0A94)
* [Stacks Project, Tag 0A8Y](https://stacks.math.columbia.edu/tag/0A8Y)
* [Stacks Project, Tag 0D66](https://stacks.math.columbia.edu/tag/0D66)
* [Stacks Project, Tag 0D68](https://stacks.math.columbia.edu/tag/0D68)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe v u v' u'

namespace Stacks.DerivedCategoryComparisons

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory C]

/-- **The localisation functor carries the degree-zero shift normalisation to the one of the
derived category.** -/
theorem Q_map_shiftFunctorZero_hom_app (I : CochainComplex C ℤ) :
    DerivedCategory.Q.map ((shiftFunctorZero (CochainComplex C ℤ) ℤ).hom.app I) =
      (DerivedCategory.Q.commShiftIso (0 : ℤ)).hom.app I ≫
        (shiftFunctorZero (DerivedCategory C) ℤ).hom.app (DerivedCategory.Q.obj I) := by
  rw [DerivedCategory.Q.commShiftIso_zero (A := ℤ), Functor.CommShift.isoZero_hom_app,
    Category.assoc, Iso.inv_hom_id_app]
  exact (Category.comp_id _).symm

/-- **A restriction square for degree-zero shifted morphisms conjugated by isomorphisms.**
Let `R` carry morphisms `A ⟶ C` to `A' ⟶ C'` and let `S` carry morphisms `B ⟶ E` to `B' ⟶ E'`,
compatibly with the conjugations by `e₁, e₂` and by `e₁', e₂'`.  If `R` carries the degree-zero
normalisation of a shifted morphism `ψ` to that of `ψ'`, then `S` carries the degree-zero
normalisation of the conjugate of `ψ` to that of the conjugate of `ψ'`.

Every object and every map is a variable, so the only definitional unification paid by a
consumer is the one instantiating this statement; the proof is two applications of
`Stacks.DerivedCategoryComparisons.homCongr_shiftFunctorZero` and the two hypotheses. -/
theorem homCongr_shiftFunctorZero_restrict
    {D : Type u} [Category.{v} D] [Preadditive D] [HasShift D ℤ]
    [∀ n : ℤ, (CategoryTheory.shiftFunctor D n).Additive]
    {D' : Type u'} [Category.{v'} D'] [Preadditive D'] [HasShift D' ℤ]
    [∀ n : ℤ, (CategoryTheory.shiftFunctor D' n).Additive]
    {A C B E : D} {A' C' B' E' : D'}
    (e₁ : A ≅ B) (e₂ : C ≅ E) (e₁' : A' ≅ B') (e₂' : C' ≅ E')
    (R : (A ⟶ C) → (A' ⟶ C')) (S : (B ⟶ E) → (B' ⟶ E'))
    (hRS : ∀ φ : A ⟶ C, S (Linear.homCongr ℤ e₁ e₂ φ) = Linear.homCongr ℤ e₁' e₂' (R φ))
    (ψ : ShiftedHom A C (0 : ℤ)) (ψ' : ShiftedHom A' C' (0 : ℤ))
    (hψ : Linear.homCongr ℤ (Iso.refl A') ((shiftFunctorZero D' ℤ).app C') ψ' =
      R (Linear.homCongr ℤ (Iso.refl A) ((shiftFunctorZero D ℤ).app C) ψ)) :
    Linear.homCongr ℤ (Iso.refl B') ((shiftFunctorZero D' ℤ).app E')
        (Linear.homCongr ℤ e₁' ((CategoryTheory.shiftFunctor D' (0 : ℤ)).mapIso e₂') ψ') =
      S (Linear.homCongr ℤ (Iso.refl B) ((shiftFunctorZero D ℤ).app E)
        (Linear.homCongr ℤ e₁ ((CategoryTheory.shiftFunctor D (0 : ℤ)).mapIso e₂) ψ)) := by
  rw [homCongr_shiftFunctorZero, homCongr_shiftFunctorZero, hRS, hψ]

end Stacks.DerivedCategoryComparisons

namespace AlgebraicGeometry.RingedSite

attribute [local instance 10000] HasDerivedCategory.standard

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory C]

/-- **Normalising the degree-zero shift commutes with the K-injective identification.** -/
theorem homotopyHomDerivedCategoryEquiv_shiftFunctorZero (K I : CochainComplex C ℤ)
    [I.IsKInjective] [(I⟦(0 : ℤ)⟧).IsKInjective]
    (θ : (HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj K ⟶
      (HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj (I⟦(0 : ℤ)⟧)) :
    homotopyHomDerivedCategoryEquiv K I
        (Linear.homCongr ℤ (Iso.refl _)
          ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).mapIso
            ((shiftFunctorZero (CochainComplex C ℤ) ℤ).app I)) θ) =
      Linear.homCongr ℤ (Iso.refl _)
          ((shiftFunctorZero (DerivedCategory C) ℤ).app (DerivedCategory.Q.obj I))
        (Linear.homCongr ℤ (Iso.refl _) ((DerivedCategory.Q.commShiftIso (0 : ℤ)).app I)
          (homotopyHomDerivedCategoryEquiv K (I⟦(0 : ℤ)⟧) θ)) := by
  simp only [Linear.homCongr_apply, Iso.refl_inv, Category.id_comp, Functor.mapIso_hom,
    Iso.app_hom, Category.assoc]
  have h := homotopyHomDerivedCategoryEquiv_naturality (I := I⟦(0 : ℤ)⟧) (I' := I) (𝟙 K)
    ((shiftFunctorZero (CochainComplex C ℤ) ℤ).hom.app I) θ
  simp only [CategoryTheory.Functor.map_id, Category.id_comp,
    Stacks.DerivedCategoryComparisons.Q_map_shiftFunctorZero_hom_app] at h
  rw [h]


end AlgebraicGeometry.RingedSite

namespace Stacks.SheafOfModules

open TopologicalSpace AlgebraicGeometry

attribute [local instance 10000] HasDerivedCategory.standard

-- The declarations below are stated over `StructureSheafModules Rc`, i.e. modules over
-- `(sheafCompose _ (forget₂ CommRingCat RingCat)).obj Rc`, while the Tag 08DK and Tag 0A94
-- machinery they are built from is stated over
-- `SheafOfModules (Stacks.SheafOfModules.Tensor.ringSheaf Rc)`.  The two sheaves of rings are
-- equal, but only after unfolding `Tensor.ringSheaf` and `sheafCompose`, which instance search
-- will not do at reducible transparency: without this the K-injectivity hypothesis on `I` and
-- the `isKInjective_kInjectiveRepresentative` instance are carried at the first spelling and
-- never retrieved at the second.  Both names are made `implicit_reducible` for this section
-- only, as in `StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedExtOnAnOpen`.
attribute [local implicit_reducible] Stacks.SheafOfModules.Tensor.ringSheaf
  CategoryTheory.sheafCompose

variable {X : TopCat.{u}} (Rc : TopCat.Sheaf CommRingCat.{u} X)

/-- **The degree-zero case of Stacks 08DK at a K-injective target is Stacks 0A94.** -/
theorem sheafHomComplexSectionHomologyEquivShiftedHom_zero
    (L I : CochainComplex (StructureSheafModules Rc) ℤ) [I.IsKInjective] (U : Opens X)
    (η : ((sectionComplex Rc (sheafHomComplex Rc L I).obj U).homology 0 : Type u)) :
    Linear.homCongr ℤ (Iso.refl _)
        ((shiftFunctorZero (DerivedCategory (SheafOfModules.{u} ((structureSheaf Rc).over U)))
          ℤ).app (DerivedCategory.Q.obj (restrictComplex Rc I U)))
        (sheafHomComplexSectionHomologyEquivShiftedHom Rc L I U 0 η) =
      @AlgebraicGeometry.RingedSite.sheafHomSectionHomologyEquivDerivedCategoryHom
        (ringedSite Rc) L I ‹I.IsKInjective› U η := by
  letI : (restrictComplex Rc I U).IsKInjective :=
    Stacks.Cohomology.Localization.isKInjective_over (Opens.grothendieckTopology X)
      (structureSheaf Rc) U I
  letI : ((restrictComplex Rc I U)⟦(0 : ℤ)⟧).IsKInjective :=
    (CochainComplex.isKInjective_shift_iff _ _).2 inferInstance
  exact (AlgebraicGeometry.RingedSite.homotopyHomDerivedCategoryEquiv_shiftFunctorZero
    (restrictComplex Rc L U) (restrictComplex Rc I U)
    (AlgebraicGeometry.RingedSite.sheafHomComplexSectionHomologyEquivHomotopyCategory
      (ringedSite Rc) L I U 0 η)).symm

variable [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Tensor.sheafTensor.{u, u, u, u, u} Rc).Additive]
  [∀ A, ((Tensor.sheafTensor.{u, u, u, u, u} Rc).obj A).Additive]
  [∀ (K₁ K₂ : HomologicalComplex (SheafOfModules.{u} (Tensor.ringSheaf.{u, u, u} Rc))
      (ComplexShape.up ℤ)),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Tensor.sheafTensor Rc) (ComplexShape.up ℤ)]

/-- **The `Ext` identification on an open, written out.** -/
theorem homSheafComplexSectionHomologyEquiv_apply
    (K L : DerivedCategory (StructureSheafModules Rc)) (U : Opens X)
    [PreservesFiniteLimits (SheafOfModules.overFunctor.{u} (structureSheaf Rc) U)]
    [PreservesFiniteColimits (SheafOfModules.overFunctor.{u} (structureSheaf Rc) U)]
    (n : ℤ) (η : ((sectionComplex Rc (homSheafComplex Rc K L) U).homology n : Type u)) :
    homSheafComplexSectionHomologyEquiv Rc K L U n η =
      Linear.homCongr ℤ
          (AlgebraicGeometry.RingedSite.restrictModelIso (ringedSite Rc) U
            (AlgebraicGeometry.RingedSite.kFlatModelIso (ringedSite Rc) K))
          ((shiftFunctor (DerivedCategory (SheafOfModules.{u} ((structureSheaf Rc).over U)))
              n).mapIso
            (AlgebraicGeometry.RingedSite.restrictModelIso (ringedSite Rc) U
              (AlgebraicGeometry.RingedSite.kInjectiveModelIso (ringedSite Rc) L)))
        (sheafHomComplexSectionHomologyEquivShiftedHom Rc (kFlatRepresentative Rc K)
          (kInjectiveRepresentative Rc L) U n η) := rfl

/-- **The chain-level restriction square at degree zero**: the restriction square for the
degree-`0` identification of Stacks 08DK at a K-injective target, with the shift normalised. -/
theorem sheafHomComplexSectionHomologyEquivShiftedHom_zero_restrict
    (L I : CochainComplex (StructureSheafModules Rc) ℤ) [I.IsKInjective] {V W : Opens X}
    (g : W ⟶ V)
    (η : ((sectionComplex Rc (sheafHomComplex Rc L I).obj V).homology 0 : Type u)) :
    Linear.homCongr ℤ (Iso.refl _)
        ((shiftFunctorZero _ ℤ).app
          (DerivedCategory.Q.obj (restrictComplex Rc I W)))
        (sheafHomComplexSectionHomologyEquivShiftedHom Rc L I W 0
          (HomologicalComplex.homologyMap
            (AlgebraicGeometry.RingedSite.sectionComplexRestrict (ringedSite Rc)
              (sheafHomComplex Rc L I).obj g) 0 η)) =
      AlgebraicGeometry.RingedSite.restrictDerivedSectionHom (ringedSite Rc) g L I
        (Linear.homCongr ℤ (Iso.refl _)
          ((shiftFunctorZero _ ℤ).app
            (DerivedCategory.Q.obj (restrictComplex Rc I V)))
          (sheafHomComplexSectionHomologyEquivShiftedHom Rc L I V 0 η)) := by
  refine Eq.trans (sheafHomComplexSectionHomologyEquivShiftedHom_zero Rc L I W _) ?_
  refine Eq.trans
    (@AlgebraicGeometry.RingedSite.sheafHomSectionHomologyEquivDerivedCategoryHom_restrict
      (ringedSite Rc) L I ‹I.IsKInjective› V W g η) ?_
  exact congrArg (AlgebraicGeometry.RingedSite.restrictDerivedSectionHom (ringedSite Rc) g L I)
    (sheafHomComplexSectionHomologyEquivShiftedHom_zero Rc L I V η).symm

/-- **The degree-zero `Ext` identification on an open is compatible with restriction.** -/
theorem homSheafComplexSectionHomologyEquiv_zero_restrict
    (K L : DerivedCategory (StructureSheafModules Rc)) {V W : Opens X} (g : W ⟶ V)
    [PreservesFiniteLimits (SheafOfModules.overFunctor.{u} (structureSheaf Rc) V)]
    [PreservesFiniteColimits (SheafOfModules.overFunctor.{u} (structureSheaf Rc) V)]
    [PreservesFiniteLimits (SheafOfModules.overFunctor.{u} (structureSheaf Rc) W)]
    [PreservesFiniteColimits (SheafOfModules.overFunctor.{u} (structureSheaf Rc) W)]
    (η : ((sectionComplex Rc (homSheafComplex Rc K L) V).homology 0 : Type u)) :
    Linear.homCongr ℤ (Iso.refl _)
        ((shiftFunctorZero _ ℤ).app
          ((SheafOfModules.overFunctor.{u} (structureSheaf Rc) W).mapDerivedCategory.obj L))
        (homSheafComplexSectionHomologyEquiv Rc K L W 0
          (HomologicalComplex.homologyMap
            (AlgebraicGeometry.RingedSite.sectionComplexRestrict (ringedSite Rc)
              (homSheafComplex Rc K L) g) 0 η)) =
      AlgebraicGeometry.RingedSite.restrictDerivedHom (ringedSite Rc) g K L
        (Linear.homCongr ℤ (Iso.refl _)
          ((shiftFunctorZero _ ℤ).app
            ((SheafOfModules.overFunctor.{u} (structureSheaf Rc) V).mapDerivedCategory.obj L))
          (homSheafComplexSectionHomologyEquiv Rc K L V 0 η)) :=
  -- `sheafHomComplexSectionHomologyEquivShiftedHom_zero_restrict` binds its K-injective complex
  -- over `StructureSheafModules Rc`, whereas `isKInjective_kInjectiveRepresentative` is stated
  -- over `SheafOfModules (Tensor.ringSheaf Rc)`.  The ambient instance is introduced at the
  -- spelling the binder asks for -- it is that instance, not a second one.
  letI : CochainComplex.IsKInjective (C := StructureSheafModules Rc)
      (kInjectiveRepresentative Rc L) := isKInjective_kInjectiveRepresentative Rc L
  Stacks.DerivedCategoryComparisons.homCongr_shiftFunctorZero_restrict
    (AlgebraicGeometry.RingedSite.restrictModelIso (ringedSite Rc) V
      (AlgebraicGeometry.RingedSite.kFlatModelIso (ringedSite Rc) K))
    (AlgebraicGeometry.RingedSite.restrictModelIso (ringedSite Rc) V
      (AlgebraicGeometry.RingedSite.kInjectiveModelIso (ringedSite Rc) L))
    (AlgebraicGeometry.RingedSite.restrictModelIso (ringedSite Rc) W
      (AlgebraicGeometry.RingedSite.kFlatModelIso (ringedSite Rc) K))
    (AlgebraicGeometry.RingedSite.restrictModelIso (ringedSite Rc) W
      (AlgebraicGeometry.RingedSite.kInjectiveModelIso (ringedSite Rc) L))
    (AlgebraicGeometry.RingedSite.restrictDerivedSectionHom (ringedSite Rc) g
      (kFlatRepresentative Rc K) (kInjectiveRepresentative Rc L))
    (AlgebraicGeometry.RingedSite.restrictDerivedHom (ringedSite Rc) g K L)
    (AlgebraicGeometry.RingedSite.restrictDerivedHom_homCongr_restrictModelIso (ringedSite Rc) g
      (AlgebraicGeometry.RingedSite.kFlatModelIso (ringedSite Rc) K)
      (AlgebraicGeometry.RingedSite.kInjectiveModelIso (ringedSite Rc) L))
    (sheafHomComplexSectionHomologyEquivShiftedHom Rc (kFlatRepresentative Rc K)
      (kInjectiveRepresentative Rc L) V 0 η)
    (sheafHomComplexSectionHomologyEquivShiftedHom Rc (kFlatRepresentative Rc K)
      (kInjectiveRepresentative Rc L) W 0
      (HomologicalComplex.homologyMap
        (AlgebraicGeometry.RingedSite.sectionComplexRestrict (ringedSite Rc)
          (homSheafComplex Rc K L) g) 0 η))
    (sheafHomComplexSectionHomologyEquivShiftedHom_zero_restrict Rc
      (kFlatRepresentative Rc K) (kInjectiveRepresentative Rc L) g η)

end Stacks.SheafOfModules

end
