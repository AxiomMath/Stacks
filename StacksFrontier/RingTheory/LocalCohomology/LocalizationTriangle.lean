module

public import StacksFrontier.RingTheory.LocalCohomology.LocalizationTriangle.Comparison

/-!
# The affine localization triangle

Let `I = (f₁, …, f_r)` be a finitely generated ideal of a commutative ring `R` and let
`U = Spec R \ V(I)`. The localization triangle of Stacks 0DWR is
`RΓ_{V(I)}(M) ⟶ M ⟶ RΓ(U, M̃|U) ⟶ RΓ_{V(I)}(M)[1]`,
whose first map is the counit of the local-cohomology adjunction of Stacks 0A6Q. This file
constructs it, *functorially in the module* and with the counit as its first map.

The obstacle the construction has to clear is that a cone in a triangulated category is not
functorial. It is made functorial here by the Čech model: local cohomology of a module is
naturally the extended alternating Čech complex `C^•(f₁, …, f_r; M)`
(`Stacks.LocalCohomology.localCohomologyIsoCech`), the counit becomes the Čech augmentation onto
`M` in degree zero, and the augmentation is a natural transformation of functors into *cochain
complexes*, where the mapping cone is functorial for a commutative square. Transporting the
standard distinguished triangle of that mapping cone along the comparison gives a distinguished
triangle whose first map is the counit itself.

What is built here is four of the seven pieces of data of
`Stacks.LocalCohomology.LocalizationTriangleData`: the functor of derived sections on the
complement, the restriction and boundary transformations, and the distinguished triangle. The
remaining three — the identification of the degree-zero cohomology of the cone with the sections
`Γ(U, M̃|U)`, its naturality, and the formula `m ↦ m/1` — are the sheaf-theoretic half of
Stacks 0DWR and are not proved here; see the implementation notes.

## Main definitions

* `Stacks.LocalCohomology.cechConeFunctor` — the cone of the Čech augmentation, as a functor of
  the module into cochain complexes.
* `Stacks.LocalCohomology.cechComplementFunctor` — derived sections on `U`, as a functor into
  `D(R)`: the third term of the localization triangle.
* `Stacks.LocalCohomology.cechRestriction`, `Stacks.LocalCohomology.cechBoundary` — the second
  and third maps of the triangle, as natural transformations.
* `Stacks.LocalCohomology.localizationTriangleDataOfSectionsIso` — the reduction of
  `Stacks.LocalCohomology.LocalizationTriangleData` to its three remaining fields: given the
  degree-zero sections comparison, its naturality and the formula `m ↦ m/1`, the data exists.

## Main results

* `Stacks.LocalCohomology.cechLocalizationTriangle_distinguished` — **the localization triangle**
  `RΓ_{V(I)}(M) ⟶ M ⟶ RΓ(U, M̃|U) ⟶ RΓ_{V(I)}(M)[1]` is distinguished, with the counit of
  Stacks 0A6Q as its first map, for every module simultaneously.

## Implementation notes

The three fields of `Stacks.LocalCohomology.LocalizationTriangleData` that are missing are
`sectionsIso`, `sectionsIso_naturality` and `restriction_eq`, all three about the degree-zero
cohomology of `cechComplementFunctor`. By construction that cohomology is the kernel of
`⨁_i M_{f_i} ⟶ ⨁_{i < j} M_{f_i f_j}`, so what is needed is the sheaf axiom for the cover of `U`
by the standard opens `D(f_i)` together with the identification of the sections of the associated
sheaf on `D(f)` with `M_f`. Mathlib has the latter only when the module and the ring share a
universe (`AlgebraicGeometry.Modules.Tilde`, the instance
`IsLocalizedModule.Away f (tilde.toOpen M (basicOpen f)).hom`), whereas the locally fractional
sections of `StacksFrontier/RingTheory/LocalCohomology/LowDegree.lean` keep the two universes
independent, so that identification has to be redone in that generality.

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

/-! ### Functoriality of the mapping cone -/

section MappingCone

variable {C : Type*} [Category C] [Preadditive C] [HasBinaryBiproducts C]

/-- The morphism induced on mapping cones by a commutative square depends only on the square. -/
theorem mappingCone_map_congr {K₁ L₁ K₂ L₂ : CochainComplex C ℤ} (φ₁ : K₁ ⟶ L₁) (φ₂ : K₂ ⟶ L₂)
    {a a' : K₁ ⟶ K₂} {b b' : L₁ ⟶ L₂} (ha : a = a') (hb : b = b')
    (comm : φ₁ ≫ b = a ≫ φ₂) (comm' : φ₁ ≫ b' = a' ≫ φ₂) :
    CochainComplex.mappingCone.map φ₁ φ₂ a b comm =
      CochainComplex.mappingCone.map φ₁ φ₂ a' b' comm' := by
  subst ha
  subst hb
  rfl

end MappingCone

variable {R : Type u} [CommRing R] {r : ℕ} (f : Fin r → R) (I : Ideal R) (hI : I.FG)

/-! ### Derived sections on the complement -/

/-- The cone of the Čech augmentation `C^•(f₁, …, f_r; M) ⟶ M⟦0⟧`, as a functor of the module:
the mapping cone is functorial for a commutative square of cochain complexes, and the
augmentation is a natural transformation. -/
def cechConeFunctor : ModuleCat.{max u v} R ⥤ CochainComplex (ModuleCat.{max u v} R) ℤ where
  obj M := CochainComplex.mappingCone (extendedCechAugmentation f M)
  map {M N} g := CochainComplex.mappingCone.map _ _ (extendedCechComplexMap f g)
    ((CochainComplex.singleFunctor (ModuleCat.{max u v} R) 0).map g)
    (extendedCechAugmentation_naturality f g).symm
  map_id M :=
    (mappingCone_map_congr _ _ (extendedCechComplexMap_id f)
      ((CochainComplex.singleFunctor (ModuleCat.{max u v} R) 0).map_id M) _ _).trans
      (CochainComplex.mappingCone.map_id _)
  map_comp {M N P} g h := by
    refine Eq.trans ?_ (CochainComplex.mappingCone.map_comp
      (extendedCechAugmentation f M) (extendedCechAugmentation f N) (extendedCechAugmentation f P)
      (extendedCechComplexMap f g)
      ((CochainComplex.singleFunctor (ModuleCat.{max u v} R) 0).map g)
      (extendedCechAugmentation_naturality f g).symm
      (extendedCechComplexMap f h)
      ((CochainComplex.singleFunctor (ModuleCat.{max u v} R) 0).map h)
      (extendedCechAugmentation_naturality f h).symm)
    exact mappingCone_map_congr _ _ (extendedCechComplexMap_comp f g h)
      ((CochainComplex.singleFunctor (ModuleCat.{max u v} R) 0).map_comp g h) _ _

/-- The cone functor at a module is the mapping cone of the augmentation. -/
@[simp] theorem cechConeFunctor_obj (M : ModuleCat.{max u v} R) :
    (cechConeFunctor.{v} f).obj M = CochainComplex.mappingCone (extendedCechAugmentation f M) :=
  rfl

/-- The cone functor on a module map is the map of cones induced by the naturality square. -/
@[simp] theorem cechConeFunctor_map {M N : ModuleCat.{max u v} R} (g : M ⟶ N) :
    (cechConeFunctor.{v} f).map g = CochainComplex.mappingCone.map _ _
      (extendedCechComplexMap f g)
      ((CochainComplex.singleFunctor (ModuleCat.{max u v} R) 0).map g)
      (extendedCechAugmentation_naturality f g).symm :=
  rfl

/-- **Derived sections on `U = Spec R \ V(I)`**, as a functor of the module: the cone of the Čech
augmentation, viewed in the derived category. This is the third term of the localization
triangle. -/
def cechComplementFunctor :
    ModuleCat.{max u v} R ⥤ DerivedCategory (ModuleCat.{max u v} R) :=
  cechConeFunctor.{v} f ⋙ DerivedCategory.Q

/-- The inclusion of the module, placed in degree zero, into the cone of the augmentation. -/
def cechConeInr (M : ModuleCat.{max u v} R) :
    (CochainComplex.singleFunctor (ModuleCat.{max u v} R) 0).obj M ⟶
      (cechConeFunctor.{v} f).obj M :=
  CochainComplex.mappingCone.inr (extendedCechAugmentation f M)

/-- The connecting map of the cone of the augmentation. -/
def cechConeDelta (M : ModuleCat.{max u v} R) :
    (cechConeFunctor.{v} f).obj M ⟶ (extendedCechComplex f M)⟦(1 : ℤ)⟧ :=
  (CochainComplex.mappingCone.triangle (extendedCechAugmentation f M)).mor₃

/-- The map of cone triangles induced by a map of modules. -/
private abbrev cechConeTriangleMap {M N : ModuleCat.{max u v} R} (g : M ⟶ N) :=
  CochainComplex.mappingCone.triangleMap (extendedCechAugmentation f M)
    (extendedCechAugmentation f N) (extendedCechComplexMap f g)
    ((CochainComplex.singleFunctor (ModuleCat.{max u v} R) 0).map g)
    (extendedCechAugmentation_naturality f g).symm

/-- The inclusion into the cone is natural in the module. -/
theorem cechConeInr_naturality {M N : ModuleCat.{max u v} R} (g : M ⟶ N) :
    (CochainComplex.singleFunctor (ModuleCat.{max u v} R) 0).map g ≫ cechConeInr.{v} f N =
      cechConeInr.{v} f M ≫ (cechConeFunctor.{v} f).map g :=
  (cechConeTriangleMap.{v} f g).comm₂.symm

/-- The connecting map of the cone is natural in the module. -/
theorem cechConeDelta_naturality {M N : ModuleCat.{max u v} R} (g : M ⟶ N) :
    (cechConeFunctor.{v} f).map g ≫ cechConeDelta.{v} f N =
      cechConeDelta.{v} f M ≫ (extendedCechComplexMap f g)⟦(1 : ℤ)⟧' :=
  (cechConeTriangleMap.{v} f g).comm₃.symm

/-- The comparison of the two descriptions of a module placed in degree zero: the object of the
derived category, and the single cochain complex. -/
def singleIsoQ (M : ModuleCat.{max u v} R) :
    (DerivedCategory.singleFunctor (ModuleCat.{max u v} R) 0).obj M ≅
      DerivedCategory.Q.obj ((CochainComplex.singleFunctor (ModuleCat.{max u v} R) 0).obj M) :=
  (DerivedCategory.singleFunctorIsoCompQ (ModuleCat.{max u v} R) 0).app M

/-- The comparison of the two descriptions of a module in degree zero is natural. -/
theorem singleIsoQ_naturality {M N : ModuleCat.{max u v} R} (g : M ⟶ N) :
    (DerivedCategory.singleFunctor (ModuleCat.{max u v} R) 0).map g ≫
        (singleIsoQ.{v} (R := R) N).hom =
      (singleIsoQ.{v} (R := R) M).hom ≫ DerivedCategory.Q.map
        ((CochainComplex.singleFunctor (ModuleCat.{max u v} R) 0).map g) :=
  (DerivedCategory.singleFunctorIsoCompQ (ModuleCat.{max u v} R) 0).hom.naturality g

/-! ### The maps of the triangle -/

/-- The second map of the localization triangle: the inclusion of `M⟦0⟧` into the cone of the
augmentation. It is the map inducing restriction of sections to `U`. -/
def cechRestriction :
    DerivedCategory.singleFunctor (ModuleCat.{max u v} R) 0 ⟶ cechComplementFunctor.{v} f where
  app M := (singleIsoQ.{v} (R := R) M).hom ≫ DerivedCategory.Q.map (cechConeInr.{v} f M)
  naturality M N g := by
    have h := cechConeInr_naturality.{v} f g
    dsimp only [cechComplementFunctor, Functor.comp_map]
    rw [← Category.assoc, singleIsoQ_naturality, Category.assoc, Category.assoc,
      ← DerivedCategory.Q.map_comp, ← DerivedCategory.Q.map_comp, h]

/-- The augmentation in the derived category, written through the comparison with the single
complex. -/
theorem Q_map_extendedCechAugmentation (M : ModuleCat.{max u v} R) :
    DerivedCategory.Q.map (extendedCechAugmentation f M) =
      (cechAugmentationHom.{v} f).app M ≫ (singleIsoQ.{v} (R := R) M).hom := by
  rw [cechAugmentationHom_app, extendedCechAugmentationHom]
  simp [singleIsoQ]

variable (hIf : Ideal.span (Set.range f) = I)

/-- The comparison of local cohomology with the Čech object, at a module. -/
def cechComparisonIso (M : ModuleCat.{max u v} R) :
    (localCohomologyOnModules R I hI).obj M ≅
      DerivedCategory.Q.obj (extendedCechComplex f M) :=
  (localCohomologyIsoCech.{v} f I hI hIf).app M

/-- The comparison of the Čech object with local cohomology is natural in the module. -/
theorem cechComparisonIso_inv_naturality {M N : ModuleCat.{max u v} R} (g : M ⟶ N) :
    DerivedCategory.Q.map (extendedCechComplexMap f g) ≫
        (cechComparisonIso.{v} f I hI hIf N).inv =
      (cechComparisonIso.{v} f I hI hIf M).inv ≫ (localCohomologyOnModules R I hI).map g :=
  (localCohomologyIsoCech.{v} f I hI hIf).inv.naturality g

/-- The comparison carries the counit of Stacks 0A6Q to the Čech augmentation. -/
theorem cechComparisonIso_hom_comp_augmentation (M : ModuleCat.{max u v} R) :
    (cechComparisonIso.{v} f I hI hIf M).hom ≫ (cechAugmentationHom.{v} f).app M =
      (Dualizing.localCohomologyAdjunction R I hI).counit.app
        ((DerivedCategory.singleFunctor (ModuleCat.{max u v} R) 0).obj M) :=
  cechComparisonHom_comp_augmentation f I hI hIf M

/-- The third map of the localization triangle: the connecting map from derived sections on `U`
to `RΓ_{V(I)}(M)[1]`, transported through the comparison of local cohomology with the Čech
object. -/
def cechBoundary :
    cechComplementFunctor.{v} f ⟶ localCohomologyOnModules.{u, max u v} R I hI ⋙
      shiftFunctor (DerivedCategory (ModuleCat.{max u v} R)) (1 : ℤ) where
  app M := DerivedCategory.Q.map (cechConeDelta.{v} f M) ≫
    (DerivedCategory.Q.commShiftIso (1 : ℤ)).hom.app (extendedCechComplex f M) ≫
      ((cechComparisonIso.{v} f I hI hIf M).inv)⟦(1 : ℤ)⟧'
  naturality M N g := by
    have h := cechConeDelta_naturality.{v} f g
    have hcs : DerivedCategory.Q.map ((shiftFunctor (CochainComplex (ModuleCat.{max u v} R) ℤ)
            (1 : ℤ)).map (extendedCechComplexMap f g)) ≫
          (DerivedCategory.Q.commShiftIso (1 : ℤ)).hom.app (extendedCechComplex f N) =
        (DerivedCategory.Q.commShiftIso (1 : ℤ)).hom.app (extendedCechComplex f M) ≫
          (DerivedCategory.Q.map (extendedCechComplexMap f g))⟦(1 : ℤ)⟧' :=
      (DerivedCategory.Q.commShiftIso (1 : ℤ)).hom.naturality (extendedCechComplexMap f g)
    have hshift := congrArg
      (fun φ => (shiftFunctor (DerivedCategory (ModuleCat.{max u v} R)) (1 : ℤ)).map φ)
      (cechComparisonIso_inv_naturality.{v} f I hI hIf g)
    simp only [Functor.map_comp] at hshift
    dsimp only [cechComplementFunctor, Functor.comp_map]
    rw [← DerivedCategory.Q.map_comp_assoc, h, DerivedCategory.Q.map_comp]
    simp only [Category.assoc]
    rw [reassoc_of% hcs, hshift]
    rfl

/-! ### The triangle -/

/-- **Stacks 0DWR, the localization triangle.** For a finitely generated ideal
`I = (f₁, …, f_r)` of `R` and an `R`-module `M`, the triangle
`RΓ_{V(I)}(M) ⟶ M ⟶ RΓ(U, M̃|U) ⟶ RΓ_{V(I)}(M)[1]`
is distinguished in `D(R)`, where the first map is the counit of the local-cohomology adjunction
of Stacks 0A6Q, the second is `Stacks.LocalCohomology.cechRestriction` and the third is
`Stacks.LocalCohomology.cechBoundary`. All three terms and both maps are functorial in `M`.

This carries no `@[stacks 0DWR]` attribute: tag 0DWR is the five-term exact sequence, whose
remaining ingredient — the identification of `H⁰` of the third term with the sections of the
associated sheaf on `U` — is not proved here. -/
theorem cechLocalizationTriangle_distinguished (M : ModuleCat.{max u v} R) :
    Triangle.mk ((Dualizing.localCohomologyAdjunction R I hI).counit.app
        ((DerivedCategory.singleFunctor (ModuleCat.{max u v} R) 0).obj M))
      ((cechRestriction.{v} f).app M)
      ((cechBoundary.{v} f I hI hIf).app M) ∈ distTriang _ := by
  refine isomorphic_distinguished _
    (DerivedCategory.mappingCone_triangle_distinguished (extendedCechAugmentation f M)) _ ?_
  refine Triangle.isoMk _ _ (cechComparisonIso.{v} f I hI hIf M) (singleIsoQ.{v} (R := R) M)
    (Iso.refl _) ?_ ?_ ?_
  · change (Dualizing.localCohomologyAdjunction R I hI).counit.app
        ((DerivedCategory.singleFunctor (ModuleCat.{max u v} R) 0).obj M) ≫
        (singleIsoQ.{v} (R := R) M).hom =
      (cechComparisonIso.{v} f I hI hIf M).hom ≫
        DerivedCategory.Q.map (extendedCechAugmentation f M)
    rw [Q_map_extendedCechAugmentation]
    exact (congrArg (fun x => x ≫ (singleIsoQ.{v} (R := R) M).hom)
      (cechComparisonIso_hom_comp_augmentation f I hI hIf M)).symm.trans
      (Category.assoc _ _ _)
  · change (cechRestriction.{v} f).app M ≫ (Iso.refl _).hom =
      (singleIsoQ.{v} (R := R) M).hom ≫ DerivedCategory.Q.map (cechConeInr.{v} f M)
    rw [Iso.refl_hom, Category.comp_id]
    rfl
  · change (cechBoundary.{v} f I hI hIf).app M ≫
        ((cechComparisonIso.{v} f I hI hIf M).hom)⟦(1 : ℤ)⟧' =
      (Iso.refl _).hom ≫ DerivedCategory.Q.map (cechConeDelta.{v} f M) ≫
        (DerivedCategory.Q.commShiftIso (1 : ℤ)).hom.app (extendedCechComplex f M)
    rw [Iso.refl_hom, Category.id_comp]
    change (DerivedCategory.Q.map (cechConeDelta.{v} f M) ≫
        (DerivedCategory.Q.commShiftIso (1 : ℤ)).hom.app (extendedCechComplex f M) ≫
          ((cechComparisonIso.{v} f I hI hIf M).inv)⟦(1 : ℤ)⟧') ≫
        ((cechComparisonIso.{v} f I hI hIf M).hom)⟦(1 : ℤ)⟧' = _
    simp only [Category.assoc, ← Functor.map_comp, Iso.inv_hom_id]
    rw [CategoryTheory.Functor.map_id]
    exact congrArg (DerivedCategory.Q.map (cechConeDelta.{v} f M) ≫ ·) (Category.comp_id _)

/-! ### Reduction of the localization triangle data to the sections comparison -/

/-- **What remains of Stacks 0DWR.** Given the degree-zero comparison of the cohomology of
derived sections on `U` with the sections of the associated sheaf — its existence, its naturality,
and the formula `m ↦ m/1` — the full `Stacks.LocalCohomology.LocalizationTriangleData` follows: the
functor of derived sections, the two natural transformations and the distinguished triangle are
supplied by this file.

Together with `Stacks.LocalCohomology.cechLocalizationTriangle_distinguished` this says exactly
what is left to prove for the low-degree exact sequence: the three hypotheses below, which are
sheaf-theoretic statements about `Γ(U, M̃|U)` and involve local cohomology no further. -/
def localizationTriangleDataOfSectionsIso
    (sectionsIso : ∀ M : ModuleCat.{max u v} R,
      (DerivedCategory.homologyFunctor (ModuleCat.{max u v} R) 0).obj
          ((cechComplementFunctor.{v} f).obj M) ≃ₗ[R]
        complementGlobalSections R I (complementTilde R I M))
    (sectionsIso_naturality : ∀ {M N : ModuleCat.{max u v} R} (g : M ⟶ N)
      (x : (DerivedCategory.homologyFunctor (ModuleCat.{max u v} R) 0).obj
        ((cechComplementFunctor.{v} f).obj M)),
      sectionsIso N ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} R) 0).map
          ((cechComplementFunctor.{v} f).map g) x) =
        (associatedAbPresheafMap g).app
          (op ((complementZeroLocus R I).ι ''ᵁ ⊤)) (sectionsIso M x))
    (restriction_eq : ∀ (M : ModuleCat.{max u v} R) (m : M),
      sectionsIso M ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} R) 0).map
        ((cechRestriction.{v} f).app M)
          ((DerivedCategory.singleFunctorCompHomologyFunctorIso
            (ModuleCat.{max u v} R) 0).inv.app M m)) =
        ⟨fun x ↦ LocalizedModule.mk m (1 : x.1.asIdeal.primeCompl),
          fun x ↦ ⟨_, x.2, 𝟙 _, m, 1, fun y ↦ ⟨by simp [Ideal.IsPrime.one_notMem], rfl⟩⟩⟩) :
    LocalizationTriangleData.{u, max u v} R I hI where
  complement := cechComplementFunctor.{v} f
  restriction := cechRestriction.{v} f
  boundary := cechBoundary.{v} f I hI hIf
  distinguished M := cechLocalizationTriangle_distinguished.{v} f I hI hIf M
  sectionsIso := sectionsIso
  sectionsIso_naturality := sectionsIso_naturality
  restriction_eq := restriction_eq

end Stacks.LocalCohomology

end
