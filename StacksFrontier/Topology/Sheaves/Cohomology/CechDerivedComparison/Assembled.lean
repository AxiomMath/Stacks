module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Topology.Sheaves.Cohomology.CechDerivedComparison.ConnectingMorphism
public import StacksFrontier.Topology.Sheaves.Cohomology.CechDerivedEffaceability.GodementAtFourUniverses
public import StacksFrontier.Topology.Sheaves.Cohomology.CechDerivedComparison.CompatibleInjectiveResolutions

/-!
# The Čech-to-derived comparison of Stacks 01EN, assembled

`Stacks.Cohomology.CechComparison.CechDerivedComparison` bundles the whole first assertion of
Stacks 01EN: that presheaves of `O`-modules have enough injectives, that degree-zero Čech
cohomology of a covering `𝒰` is left exact, that the Čech complex functor of Stacks 01EJ is
exact, that every short exact sequence admits a compatible short exact sequence of injective
resolutions, and that there is a δ-functor whose components are the right derived functors of
degree-zero Čech cohomology, whose connecting morphisms are the ones computed on those
resolutions, and which is uniquely isomorphic to the Čech δ-functor of Stacks 01EK over
`CategoryTheory.Functor.toRightDerivedZero`.

All ten of its fields are now proved. This file assembles them, and then states and proves the
same assertion with the space, ring, module and covering index universes independent —
`Stacks.Cohomology.CechComparisonU.CechDerivedComparison`, which is the generality the
Čech-to-cohomology spectral sequence of Stacks 01ES and its consumers need.

## Main definitions

* `Stacks.Cohomology.CechComparisonU.cechDerivedComparison`: the comparison data of Stacks
  01EN, first assertion, at four independent universes. This is the one that carries the tag.
* `Stacks.Cohomology.CechComparison.cechDerivedComparison`: the same with the four universes
  identified, transported along `CechComparisonU.cechDerivedComparisonEquiv`.

## Implementation notes

`Stacks.Cohomology.CechComparisonU.cechDerivedComparisonOfDerivedδ` reduces the four-universe
statement to its `derivedδ_eq` field alone, every other field being proved at the four
universes already. The reduction chain proving that field was stated over the monomorphic API
of `Stacks.Cohomology.CechComparison`, and the second half of this file re-runs it
over the four-universe API. That costs nothing but the universe annotations: every abstract
input the chain calls — everything it takes from
`Stacks.Cohomology.HigherDirectImagePresheaf`, and in particular
`Stacks.Cohomology.HigherDirectImagePresheaf.comm₃_resolutionDerivedComparison`, which is the
whole mathematical content of `derivedδ_eq` — is already polymorphic in an arbitrary additive
functor between abelian categories with enough injectives in the source. Not one tactic script
changed; universe arguments must be written at the call sites, since unification will not read
the components of a `max` off its value.

## References

* [Stacks Project, Tag 01EN](https://stacks.math.columbia.edu/tag/01EN)
* [Stacks Project, Tag 01EK](https://stacks.math.columbia.edu/tag/01EK)
* [Stacks Project, Tag 01EJ](https://stacks.math.columbia.edu/tag/01EJ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits ComplexShape Opposite TopologicalSpace
open Stacks.Cohomology.HigherDirectImagePresheaf

universe u r v w


/-! ## The same, at four independent universes

`Stacks.Cohomology.CechComparisonU.cechDerivedComparisonOfDerivedδ` reduces the four-universe
comparison to its `derivedδ_eq` field alone. That field's reduction chain is stated over the
monomorphic API of `Stacks.Cohomology.CechComparison`; what follows re-runs it over the
four-universe API, which it fits without a single change to any tactic script, since every
abstract input it
calls — through
`Stacks.Cohomology.HigherDirectImagePresheaf.comm₃_resolutionDerivedComparison` and
`Stacks.Cohomology.HigherDirectImagePresheaf.mapδ_rightDerivedFunctorPlus_comp_ι_singlePlusδ` —
is already universe-polymorphic in an arbitrary additive functor between abelian categories.
-/

namespace Stacks.Cohomology.CechComparisonU

attribute [local instance] HasDerivedCategory.standard
-- The same instances the connecting morphism of `rightDerivedPlusδ` is built from: a second copy
-- would be definitionally equal but not syntactically so, and the commutation of `RF` with the
-- shift appears explicitly in that morphism.
attribute [local instance] CategoryTheory.Functor.commShiftRightDerivedFunctorPlus
  CategoryTheory.Functor.natTransCommShiftRightDerivedFunctorPlusUnit
  CategoryTheory.Functor.isTriangulated_rightDerivedFunctorPlus

variable {X : Type u} [TopologicalSpace X]
  (O : Sheaf (Opens.grothendieckTopology X) RingCat.{r})
  (𝒰 : CechExactFunctor.CechOpenCover.{u, w} (TopCat.of X))
  [EnoughInjectives (Modules.{u, r, max u r v w} O)]

/-- **The `derivedδ_eq` field of `CechDerivedComparison`, with its transport discharged.**  The
field conjugates the connecting morphism of `derivedDeltaFunctor` by the `eqToHom`s of
`derivedDeltaFunctor_functor`; since that equality of functors holds by `rfl` both `eqToHom`s
are identities, and since `CategoryTheory.DeltaFunctor.ofIso_δ` also holds by `rfl` the
connecting morphism is on the nose the conjugate of
`Stacks.Cohomology.CechDelta.rightDerivedPlusδ` by
`Stacks.Cohomology.HigherDirectImagePresheaf.derivedPlusToStandard`.  So the field reduces to
the displayed equality of morphisms, with no transport left in it. -/
theorem derivedδ_eq_of_rightDerivedPlusδ_eq {S : ShortComplex (Modules.{u, r, max u r v w} O)}
    (hS : S.ShortExact) (J : ResolutionShortComplex.{u, r, v, w} O 𝒰 S) (n : ℕ)
    (h : (derivedPlusToStandard (cechCohomologyZeroFunctor.{u, r, v, w} O 𝒰) n).inv.app S.X₃ ≫
          CechDelta.rightDerivedPlusδ (cechCohomologyZeroFunctor.{u, r, v, w} O 𝒰) hS n ≫
          (derivedPlusToStandard (cechCohomologyZeroFunctor.{u, r, v, w} O 𝒰)
            (n + 1)).hom.app S.X₁ =
        rightDerivedConnecting.{u, r, v, w} O 𝒰 J n) :
    (eqToHom (derivedDeltaFunctor_functor.{u, r, v, w} O 𝒰 n).symm).app S.X₃ ≫
        (derivedDeltaFunctor.{u, r, v, w} O 𝒰).δ hS n ≫
        (eqToHom (derivedDeltaFunctor_functor.{u, r, v, w} O 𝒰 (n + 1))).app S.X₁ =
      rightDerivedConnecting.{u, r, v, w} O 𝒰 J n :=
  (Category.id_comp _).trans ((Category.comp_id _).trans h)

/-- **The `derivedδ_eq` field of `CechDerivedComparison`, read through the resolutions of `J`.**
The comparison of the derived-category and injective-resolution conventions for `Rⁿ F` does not
depend on which injective resolution computes it
(`Stacks.Cohomology.HigherDirectImagePresheaf.derivedPlusToStandard_app_eq`), so the field may
be stated through the resolutions `J.J₃` and `J.J₁` carried by the sequence of resolutions
itself.  That is the form to work in: by
`Stacks.Cohomology.HigherDirectImagePresheaf.derivedPlusToStandardObjOfResolution_eq_trans`
each side then carries `J.J₃.isoRightDerivedObj` and `J.J₁.isoRightDerivedObj` as outer
factors, exactly as `rightDerivedConnecting` does, so those isomorphisms cancel instead of
having to be moved across the junction between `(homologyFunctor _ _ n).obj K` and
`K.homology n`. -/
theorem derivedδ_eq_of_resolution_rightDerivedPlusδ_eq
    {S : ShortComplex (Modules.{u, r, max u r v w} O)}
    (hS : S.ShortExact) (J : ResolutionShortComplex.{u, r, v, w} O 𝒰 S) (n : ℕ)
    (h : (derivedPlusToStandardObjOfResolution
            (cechCohomologyZeroFunctor.{u, r, v, w} O 𝒰) J.J₃ n).inv ≫
          CechDelta.rightDerivedPlusδ (cechCohomologyZeroFunctor.{u, r, v, w} O 𝒰) hS n ≫
          (derivedPlusToStandardObjOfResolution
            (cechCohomologyZeroFunctor.{u, r, v, w} O 𝒰) J.J₁ (n + 1)).hom =
        rightDerivedConnecting.{u, r, v, w} O 𝒰 J n) :
    (eqToHom (derivedDeltaFunctor_functor.{u, r, v, w} O 𝒰 n).symm).app S.X₃ ≫
        (derivedDeltaFunctor.{u, r, v, w} O 𝒰).δ hS n ≫
        (eqToHom (derivedDeltaFunctor_functor.{u, r, v, w} O 𝒰 (n + 1))).app S.X₁ =
      rightDerivedConnecting.{u, r, v, w} O 𝒰 J n := by
  refine derivedδ_eq_of_rightDerivedPlusδ_eq.{u, r, v, w} O 𝒰 hS J n ?_
  have h₃ : (derivedPlusToStandard (cechCohomologyZeroFunctor.{u, r, v, w} O 𝒰) n).inv.app S.X₃ =
      (derivedPlusToStandardObjOfResolution
        (cechCohomologyZeroFunctor.{u, r, v, w} O 𝒰) J.J₃ n).inv :=
    congrArg Iso.inv
      (derivedPlusToStandard_app_eq (cechCohomologyZeroFunctor.{u, r, v, w} O 𝒰) J.J₃ n)
  have h₁ : (derivedPlusToStandard
        (cechCohomologyZeroFunctor.{u, r, v, w} O 𝒰) (n + 1)).hom.app S.X₁ =
      (derivedPlusToStandardObjOfResolution
        (cechCohomologyZeroFunctor.{u, r, v, w} O 𝒰) J.J₁ (n + 1)).hom :=
    congrArg Iso.hom
      (derivedPlusToStandard_app_eq (cechCohomologyZeroFunctor.{u, r, v, w} O 𝒰) J.J₁ (n + 1))
  rw [h₃, h₁]
  exact h

/-- **The connecting morphism of the derived-category triangle attached to the sequence of
resolutions carried by `J`.**  Take the sequence `J.J₁.cocomplex ⟶ J.J₂.cocomplex ⟶
J.J₃.cocomplex` of injective resolutions, extend it by zero to a sequence of `ℤ`-indexed
complexes, apply degree-zero Čech cohomology in each degree — this is still short exact, which
is `J.mappedShortExact` — and take the connecting morphism in cohomology of
`DerivedCategory.triangleOfSES` of the result, read in the `Qh ∘ quotient` spelling that
`Stacks.Cohomology.HigherDirectImagePresheaf.extendedHomologyIso` presents.

This is the target of the one remaining obligation,
`rightDerivedPlusδ_eq_mappedShortExactδ`. -/
def resolutionTriangleδ {S : ShortComplex (Modules.{u, r, max u r v w} O)}
    (J : ResolutionShortComplex.{u, r, v, w} O 𝒰 S) (n : ℕ) :
    (DerivedCategory.homologyFunctor (SectionModules.{u, r, max u r v w} O 𝒰) (n : ℤ)).obj
        (DerivedCategory.Qh.obj
          ((HomotopyCategory.quotient (SectionModules.{u, r, max u r v w} O 𝒰) (up ℤ)).obj
            (((cechCohomologyZeroFunctor.{u, r, v, w} O 𝒰).mapHomologicalComplex (up ℤ)).obj
              (J.J₃.cocomplex.extend ComplexShape.embeddingUpNat)))) ⟶
      (DerivedCategory.homologyFunctor (SectionModules.{u, r, max u r v w} O 𝒰)
          ((n + 1 : ℕ) : ℤ)).obj
        (DerivedCategory.Qh.obj
          ((HomotopyCategory.quotient (SectionModules.{u, r, max u r v w} O 𝒰) (up ℤ)).obj
            (((cechCohomologyZeroFunctor.{u, r, v, w} O 𝒰).mapHomologicalComplex (up ℤ)).obj
              (J.J₁.cocomplex.extend ComplexShape.embeddingUpNat)))) :=
  (DerivedCategory.homologyFunctor (SectionModules.{u, r, max u r v w} O 𝒰) (n : ℤ)).map
      ((DerivedCategory.quotientCompQhIso (SectionModules.{u, r, max u r v w} O 𝒰)).hom.app _) ≫
    mapExtendTriangleδ (cechCohomologyZeroFunctor.{u, r, v, w} O 𝒰) J.mappedShortExact n ≫
    (DerivedCategory.homologyFunctor (SectionModules.{u, r, max u r v w} O 𝒰) ((n + 1 : ℕ) : ℤ)).map
      ((DerivedCategory.quotientCompQhIso (SectionModules.{u, r, max u r v w} O 𝒰)).inv.app _)

/-- **The remaining content of `derivedδ_eq`, with pieces 1 and 2 discharged.**  Granted the
single hypothesis that `Stacks.Cohomology.CechDelta.rightDerivedPlusδ`, conjugated by
`Stacks.Cohomology.HigherDirectImagePresheaf.derivedPlusResolutionHomologyIso`, is
`resolutionTriangleδ` — that is, granted that the connecting morphism of the total right derived
functor on `D⁺` is the connecting morphism of the derived-category triangle of the degreewise
image of the resolutions — the displayed equality of `derivedδ_eq` follows, by
`Stacks.Cohomology.HigherDirectImagePresheaf.extendedHomologyIso_conj_mapExtendTriangleδ`.

The hypothesis is the whole of the third piece described in the module docstring; everything
else in the field is now proved. -/
theorem rightDerivedPlusδ_eq_mappedShortExactδ {S : ShortComplex (Modules.{u, r, max u r v w} O)}
    (hS : S.ShortExact) (J : ResolutionShortComplex.{u, r, v, w} O 𝒰 S) (n : ℕ)
    (h : (derivedPlusResolutionHomologyIso
            (cechCohomologyZeroFunctor.{u, r, v, w} O 𝒰) J.J₃ n).inv ≫
          CechDelta.rightDerivedPlusδ (cechCohomologyZeroFunctor.{u, r, v, w} O 𝒰) hS n ≫
          (derivedPlusResolutionHomologyIso
            (cechCohomologyZeroFunctor.{u, r, v, w} O 𝒰) J.J₁ (n + 1)).hom =
        resolutionTriangleδ.{u, r, v, w} O 𝒰 J n) :
    (extendedHomologyIso (cechCohomologyZeroFunctor.{u, r, v, w} O 𝒰) J.J₃.cocomplex n).inv ≫
        (derivedPlusResolutionHomologyIso (cechCohomologyZeroFunctor.{u, r, v, w} O 𝒰) J.J₃ n).inv ≫
        CechDelta.rightDerivedPlusδ (cechCohomologyZeroFunctor.{u, r, v, w} O 𝒰) hS n ≫
        (derivedPlusResolutionHomologyIso
          (cechCohomologyZeroFunctor.{u, r, v, w} O 𝒰) J.J₁ (n + 1)).hom ≫
        (extendedHomologyIso (cechCohomologyZeroFunctor.{u, r, v, w} O 𝒰)
          J.J₁.cocomplex (n + 1)).hom =
      J.mappedShortExact.δ n (n + 1) rfl := by
  have hα := extendedHomologyIso_conj_mapExtendTriangleδ
    (cechCohomologyZeroFunctor.{u, r, v, w} O 𝒰) J.mappedShortExact n
  dsimp only at hα
  refine Eq.trans ?_ hα
  rw [resolutionTriangleδ] at h
  rw [← h]
  exact (whisker_eq _
    ((Category.assoc _ _ _).trans (whisker_eq _ (Category.assoc _ _ _)))).symm

/-- **The `derivedδ_eq` field of `CechDerivedComparison`, reduced to a single obligation.**
Granted that `Stacks.Cohomology.CechDelta.rightDerivedPlusδ`, conjugated by
`Stacks.Cohomology.HigherDirectImagePresheaf.derivedPlusResolutionHomologyIso`, is
`resolutionTriangleδ`, the field holds.

The two occurrences of `CategoryTheory.InjectiveResolution.isoRightDerivedObj` — the outer
factors of
`Stacks.Cohomology.HigherDirectImagePresheaf.derivedPlusToStandardObjOfResolution` and the
outer factors of `rightDerivedConnecting` — cancel, so what is left is exactly
`rightDerivedPlusδ_eq_mappedShortExactδ`.  The reassociation that performs the cancellation
crosses the junction between the two presentations of the cohomology of `F(I)` — as
`K.homology n` and as `(F.mapHomologicalComplex _ ⋙ homologyFunctor _ _ n).obj K` — across
which neither `rw` nor `simp` fires on `CategoryTheory.Category.assoc`, so it is built as a
chain of explicit `Category.assoc` terms. -/
theorem derivedδ_eq_of_resolutionTriangleδ {S : ShortComplex (Modules.{u, r, max u r v w} O)}
    (hS : S.ShortExact) (J : ResolutionShortComplex.{u, r, v, w} O 𝒰 S) (n : ℕ)
    (h : (derivedPlusResolutionHomologyIso
            (cechCohomologyZeroFunctor.{u, r, v, w} O 𝒰) J.J₃ n).inv ≫
          CechDelta.rightDerivedPlusδ (cechCohomologyZeroFunctor.{u, r, v, w} O 𝒰) hS n ≫
          (derivedPlusResolutionHomologyIso
            (cechCohomologyZeroFunctor.{u, r, v, w} O 𝒰) J.J₁ (n + 1)).hom =
        resolutionTriangleδ.{u, r, v, w} O 𝒰 J n) :
    (eqToHom (derivedDeltaFunctor_functor.{u, r, v, w} O 𝒰 n).symm).app S.X₃ ≫
        (derivedDeltaFunctor.{u, r, v, w} O 𝒰).δ hS n ≫
        (eqToHom (derivedDeltaFunctor_functor.{u, r, v, w} O 𝒰 (n + 1))).app S.X₁ =
      rightDerivedConnecting.{u, r, v, w} O 𝒰 J n := by
  refine derivedδ_eq_of_resolution_rightDerivedPlusδ_eq.{u, r, v, w} O 𝒰 hS J n ?_
  have hβ := rightDerivedPlusδ_eq_mappedShortExactδ.{u, r, v, w} O 𝒰 hS J n h
  rw [derivedPlusToStandardObjOfResolution_eq_trans,
    derivedPlusToStandardObjOfResolution_eq_trans, rightDerivedConnecting]
  have u₃ : (derivedPlusResolutionHomologyIso (cechCohomologyZeroFunctor.{u, r, v, w} O 𝒰) J.J₃ n ≪≫
        extendedHomologyIso (cechCohomologyZeroFunctor.{u, r, v, w} O 𝒰) J.J₃.cocomplex n ≪≫
        (J.J₃.isoRightDerivedObj (cechCohomologyZeroFunctor.{u, r, v, w} O 𝒰) n).symm).inv =
      ((J.J₃.isoRightDerivedObj (cechCohomologyZeroFunctor.{u, r, v, w} O 𝒰) n).hom ≫
          (extendedHomologyIso (cechCohomologyZeroFunctor.{u, r, v, w} O 𝒰) J.J₃.cocomplex n).inv) ≫
        (derivedPlusResolutionHomologyIso
          (cechCohomologyZeroFunctor.{u, r, v, w} O 𝒰) J.J₃ n).inv := rfl
  have v₁ : (derivedPlusResolutionHomologyIso
          (cechCohomologyZeroFunctor.{u, r, v, w} O 𝒰) J.J₁ (n + 1) ≪≫
        extendedHomologyIso (cechCohomologyZeroFunctor.{u, r, v, w} O 𝒰) J.J₁.cocomplex (n + 1) ≪≫
        (J.J₁.isoRightDerivedObj (cechCohomologyZeroFunctor.{u, r, v, w} O 𝒰) (n + 1)).symm).hom =
      (derivedPlusResolutionHomologyIso
          (cechCohomologyZeroFunctor.{u, r, v, w} O 𝒰) J.J₁ (n + 1)).hom ≫
        ((extendedHomologyIso (cechCohomologyZeroFunctor.{u, r, v, w} O 𝒰)
            J.J₁.cocomplex (n + 1)).hom ≫
          (J.J₁.isoRightDerivedObj
            (cechCohomologyZeroFunctor.{u, r, v, w} O 𝒰) (n + 1)).inv) := rfl
  rw [u₃, v₁]
  refine (Category.assoc _ _ _).trans ((Category.assoc _ _ _).trans (whisker_eq _ ?_))
  exact ((Category.assoc _ _ _).trans (whisker_eq _ ((Category.assoc _ _ _).trans
    (whisker_eq _ ((Category.assoc _ _ _).trans
      (whisker_eq _ (Category.assoc _ _ _))))))).symm.trans (hβ =≫ _)

/-- **The one remaining obligation of `derivedδ_eq`, as a single commuting square.**  The
hypothesis is the third square of the morphism of triangles of `D(ℬ)` from the image under
`DerivedCategory.Plus.ι` of the triangle of `Stacks.Cohomology.CechDelta.rightDerivedPlusδ` — the
image under `RF` of the triangle of `S[0]` in `D⁺(𝒜)` — to
`DerivedCategory.triangleOfSES` of the degreewise image under `Ȟ⁰(𝒰, -)` of the extended
sequence of resolutions, along `resolutionDerivedComparison`.

Granted it, the hypothesis of `rightDerivedPlusδ_eq_mappedShortExactδ` holds, so with
`derivedδ_eq_of_resolutionTriangleδ` the field `derivedδ_eq` follows
(`derivedδ_eq_of_comm₃`).

No morphism of triangles and no isomorphism of triangles is needed, only this one square:
`CategoryTheory.Functor.homologySequenceδ` of a triangle is `CategoryTheory.Functor.shiftMap` of
its third morphism, `DerivedCategory.Plus.homologyFunctor` is by definition
`DerivedCategory.Plus.ι ⋙ DerivedCategory.homologyFunctor` — so
`CategoryTheory.Functor.comp_shiftMap` reads the `D⁺(ℬ)` connecting morphism off `D(ℬ)` — and
`CategoryTheory.Functor.shiftMap_comp` and `….shiftMap_comp'` absorb the two comparison
isomorphisms into the argument of `shiftMap`.  Everything else in the proof is the cancellation
of `DerivedCategory.quotientCompQhIso`, done in term mode because the two presentations of the
image of a resolution in `D(ℬ)` are definitionally but not syntactically equal. -/
theorem rightDerivedPlusδ_eq_of_comm₃ {S : ShortComplex (Modules.{u, r, max u r v w} O)}
    (hS : S.ShortExact) (J : ResolutionShortComplex.{u, r, v, w} O 𝒰 S) (n : ℕ)
    (hsq : (resolutionDerivedComparison (cechCohomologyZeroFunctor.{u, r, v, w} O 𝒰) J.J₃).hom ≫
        mapExtendSESδ (cechCohomologyZeroFunctor.{u, r, v, w} O 𝒰)
          (R := ShortComplex.mk J.f J.g J.zero) J.mappedShortExact =
      (DerivedCategory.Plus.ι.map
            ((CechDelta.derivedDeltaFunctorStructure
              (cechCohomologyZeroFunctor.{u, r, v, w} O 𝒰)).δ hS) ≫
          (DerivedCategory.Plus.ι.commShiftIso (1 : ℤ)).hom.app
            ((cechCohomologyZeroFunctor.{u, r, v, w} O 𝒰).rightDerivedFunctorPlus.obj
              ((DerivedCategory.Plus.singleFunctor (Modules.{u, r, max u r v w} O) 0).obj S.X₁))) ≫
        ((resolutionDerivedComparison
          (cechCohomologyZeroFunctor.{u, r, v, w} O 𝒰) J.J₁).hom)⟦(1 : ℤ)⟧') :
    (derivedPlusResolutionHomologyIso (cechCohomologyZeroFunctor.{u, r, v, w} O 𝒰) J.J₃ n).inv ≫
        CechDelta.rightDerivedPlusδ (cechCohomologyZeroFunctor.{u, r, v, w} O 𝒰) hS n ≫
        (derivedPlusResolutionHomologyIso
          (cechCohomologyZeroFunctor.{u, r, v, w} O 𝒰) J.J₁ (n + 1)).hom =
      resolutionTriangleδ.{u, r, v, w} O 𝒰 J n := by
  have hA : CechDelta.rightDerivedPlusδ (cechCohomologyZeroFunctor.{u, r, v, w} O 𝒰) hS n =
      (DerivedCategory.homologyFunctor (SectionModules.{u, r, max u r v w} O 𝒰) 0).shiftMap
        (DerivedCategory.Plus.ι.map
            ((CechDelta.derivedDeltaFunctorStructure
              (cechCohomologyZeroFunctor.{u, r, v, w} O 𝒰)).δ hS) ≫
          (DerivedCategory.Plus.ι.commShiftIso (1 : ℤ)).hom.app
            ((cechCohomologyZeroFunctor.{u, r, v, w} O 𝒰).rightDerivedFunctorPlus.obj
              ((DerivedCategory.Plus.singleFunctor (Modules.{u, r, max u r v w} O) 0).obj S.X₁)))
        (n : ℤ) ((n + 1 : ℕ) : ℤ) (by push_cast; ring) :=
    Functor.comp_shiftMap DerivedCategory.Plus.ι _ _ _ _ _
  have key : (resolutionDerivedComparison (cechCohomologyZeroFunctor.{u, r, v, w} O 𝒰) J.J₃).inv ≫
      (DerivedCategory.Plus.ι.map
            ((CechDelta.derivedDeltaFunctorStructure
              (cechCohomologyZeroFunctor.{u, r, v, w} O 𝒰)).δ hS) ≫
          (DerivedCategory.Plus.ι.commShiftIso (1 : ℤ)).hom.app
            ((cechCohomologyZeroFunctor.{u, r, v, w} O 𝒰).rightDerivedFunctorPlus.obj
              ((DerivedCategory.Plus.singleFunctor (Modules.{u, r, max u r v w} O) 0).obj S.X₁))) ≫
        ((resolutionDerivedComparison
          (cechCohomologyZeroFunctor.{u, r, v, w} O 𝒰) J.J₁).hom)⟦(1 : ℤ)⟧' =
      mapExtendSESδ (cechCohomologyZeroFunctor.{u, r, v, w} O 𝒰)
          (R := ShortComplex.mk J.f J.g J.zero) J.mappedShortExact := by
    rw [Iso.inv_comp_eq]
    exact hsq.symm
  have hkey : (DerivedCategory.homologyFunctor (SectionModules.{u, r, max u r v w} O 𝒰) (n : ℤ)).map
          (resolutionDerivedComparison (cechCohomologyZeroFunctor.{u, r, v, w} O 𝒰) J.J₃).inv ≫
        (DerivedCategory.homologyFunctor (SectionModules.{u, r, max u r v w} O 𝒰) 0).shiftMap
          (DerivedCategory.Plus.ι.map
              ((CechDelta.derivedDeltaFunctorStructure
                (cechCohomologyZeroFunctor.{u, r, v, w} O 𝒰)).δ hS) ≫
            (DerivedCategory.Plus.ι.commShiftIso (1 : ℤ)).hom.app
              ((cechCohomologyZeroFunctor.{u, r, v, w} O 𝒰).rightDerivedFunctorPlus.obj
                ((DerivedCategory.Plus.singleFunctor (Modules.{u, r, max u r v w} O) 0).obj S.X₁)))
          (n : ℤ) ((n + 1 : ℕ) : ℤ) (by push_cast; ring) ≫
        (DerivedCategory.homologyFunctor (SectionModules.{u, r, max u r v w} O 𝒰)
            ((n + 1 : ℕ) : ℤ)).map
          (resolutionDerivedComparison (cechCohomologyZeroFunctor.{u, r, v, w} O 𝒰) J.J₁).hom =
      mapExtendTriangleδ (cechCohomologyZeroFunctor.{u, r, v, w} O 𝒰) J.mappedShortExact n := by
    rw [mapExtendTriangleδ_eq, ← key]
    conv_rhs => rw [Functor.shiftMap_comp', Functor.shiftMap_comp]
    rfl
  have e₃ : ((DerivedCategory.quotientCompQhIso (SectionModules.{u, r, max u r v w} O 𝒰)).app
          (((cechCohomologyZeroFunctor.{u, r, v, w} O 𝒰).mapHomologicalComplex (up ℤ)).obj
            (J.J₃.cocomplex.extend ComplexShape.embeddingUpNat))).hom ≫
        (resolutionDerivedComparison (cechCohomologyZeroFunctor.{u, r, v, w} O 𝒰) J.J₃).inv =
      DerivedCategory.Plus.ι.map
        (derivedPlusResolutionIso (cechCohomologyZeroFunctor.{u, r, v, w} O 𝒰) J.J₃).inv :=
    (Category.assoc _ _ _).symm.trans
      ((eq_whisker (Iso.hom_inv_id _) _).trans (Category.id_comp _))
  have e₁ : (resolutionDerivedComparison (cechCohomologyZeroFunctor.{u, r, v, w} O 𝒰) J.J₁).hom ≫
        ((DerivedCategory.quotientCompQhIso (SectionModules.{u, r, max u r v w} O 𝒰)).app
          (((cechCohomologyZeroFunctor.{u, r, v, w} O 𝒰).mapHomologicalComplex (up ℤ)).obj
            (J.J₁.cocomplex.extend ComplexShape.embeddingUpNat))).inv =
      DerivedCategory.Plus.ι.map
        (derivedPlusResolutionIso (cechCohomologyZeroFunctor.{u, r, v, w} O 𝒰) J.J₁).hom :=
    (Category.assoc _ _ _).trans
      ((whisker_eq _ (Iso.hom_inv_id _)).trans (Category.comp_id _))
  have hc₃ := (CategoryTheory.Functor.map_comp
      (DerivedCategory.homologyFunctor (SectionModules.{u, r, max u r v w} O 𝒰) (n : ℤ))
      (((DerivedCategory.quotientCompQhIso (SectionModules.{u, r, max u r v w} O 𝒰)).app
        (((cechCohomologyZeroFunctor.{u, r, v, w} O 𝒰).mapHomologicalComplex (up ℤ)).obj
          (J.J₃.cocomplex.extend ComplexShape.embeddingUpNat))).hom)
      (resolutionDerivedComparison
        (cechCohomologyZeroFunctor.{u, r, v, w} O 𝒰) J.J₃).inv).symm.trans
    (congrArg (fun f => (DerivedCategory.homologyFunctor
        (SectionModules.{u, r, max u r v w} O 𝒰) (n : ℤ)).map f)
      e₃)
  have hc₁ := (CategoryTheory.Functor.map_comp
      (DerivedCategory.homologyFunctor (SectionModules.{u, r, max u r v w} O 𝒰) ((n + 1 : ℕ) : ℤ))
      (resolutionDerivedComparison (cechCohomologyZeroFunctor.{u, r, v, w} O 𝒰) J.J₁).hom
      (((DerivedCategory.quotientCompQhIso (SectionModules.{u, r, max u r v w} O 𝒰)).app
        (((cechCohomologyZeroFunctor.{u, r, v, w} O 𝒰).mapHomologicalComplex (up ℤ)).obj
          (J.J₁.cocomplex.extend ComplexShape.embeddingUpNat))).inv)).symm.trans
    (congrArg (fun f =>
      (DerivedCategory.homologyFunctor (SectionModules.{u, r, max u r v w} O 𝒰)
        ((n + 1 : ℕ) : ℤ)).map f) e₁)
  rw [hA, derivedPlusResolutionHomologyIso_inv, derivedPlusResolutionHomologyIso_hom,
    resolutionTriangleδ]
  refine Eq.symm ((whisker_eq _ (eq_whisker hkey.symm _)).trans ?_)
  refine (whisker_eq _ ((Category.assoc _ _ _).trans
    (whisker_eq _ (Category.assoc _ _ _)))).trans ?_
  refine (Category.assoc _ _ _).symm.trans ?_
  exact (eq_whisker hc₃ _).trans (whisker_eq _ (whisker_eq _ hc₁))

/-- **The `derivedδ_eq` field of `CechDerivedComparison`, reduced to one commuting square of the
full derived category `D(ℬ)`.**  This is `derivedδ_eq_of_resolutionTriangleδ` with its
hypothesis replaced, through `rightDerivedPlusδ_eq_of_comm₃`, by the third square of the
morphism of triangles described there.  It is the whole of what is left of Stacks 01EN's
comparison of connecting morphisms. -/
theorem derivedδ_eq_of_comm₃ {S : ShortComplex (Modules.{u, r, max u r v w} O)}
    (hS : S.ShortExact) (J : ResolutionShortComplex.{u, r, v, w} O 𝒰 S) (n : ℕ)
    (hsq : (resolutionDerivedComparison (cechCohomologyZeroFunctor.{u, r, v, w} O 𝒰) J.J₃).hom ≫
        mapExtendSESδ (cechCohomologyZeroFunctor.{u, r, v, w} O 𝒰)
          (R := ShortComplex.mk J.f J.g J.zero) J.mappedShortExact =
      (DerivedCategory.Plus.ι.map
            ((CechDelta.derivedDeltaFunctorStructure
              (cechCohomologyZeroFunctor.{u, r, v, w} O 𝒰)).δ hS) ≫
          (DerivedCategory.Plus.ι.commShiftIso (1 : ℤ)).hom.app
            ((cechCohomologyZeroFunctor.{u, r, v, w} O 𝒰).rightDerivedFunctorPlus.obj
              ((DerivedCategory.Plus.singleFunctor (Modules.{u, r, max u r v w} O) 0).obj S.X₁))) ≫
        ((resolutionDerivedComparison
          (cechCohomologyZeroFunctor.{u, r, v, w} O 𝒰) J.J₁).hom)⟦(1 : ℤ)⟧') :
    (eqToHom (derivedDeltaFunctor_functor.{u, r, v, w} O 𝒰 n).symm).app S.X₃ ≫
        (derivedDeltaFunctor.{u, r, v, w} O 𝒰).δ hS n ≫
        (eqToHom (derivedDeltaFunctor_functor.{u, r, v, w} O 𝒰 (n + 1))).app S.X₁ =
      rightDerivedConnecting.{u, r, v, w} O 𝒰 J n :=
  derivedδ_eq_of_resolutionTriangleδ.{u, r, v, w} O 𝒰 hS J n
    (rightDerivedPlusδ_eq_of_comm₃.{u, r, v, w} O 𝒰 hS J n hsq)

/-- **The one commuting square that `derivedδ_eq_of_comm₃` asks for.** -/
theorem comm₃_cech {S : ShortComplex (Modules.{u, r, max u r v w} O)} (hS : S.ShortExact)
    (J : ResolutionShortComplex.{u, r, v, w} O 𝒰 S) :
    (resolutionDerivedComparison (cechCohomologyZeroFunctor.{u, r, v, w} O 𝒰) J.J₃).hom ≫
        mapExtendSESδ (cechCohomologyZeroFunctor.{u, r, v, w} O 𝒰)
          (R := ShortComplex.mk J.f J.g J.zero) J.mappedShortExact =
      (DerivedCategory.Plus.ι.map
            ((CechDelta.derivedDeltaFunctorStructure
              (cechCohomologyZeroFunctor.{u, r, v, w} O 𝒰)).δ hS) ≫
          (DerivedCategory.Plus.ι.commShiftIso (1 : ℤ)).hom.app
            ((cechCohomologyZeroFunctor.{u, r, v, w} O 𝒰).rightDerivedFunctorPlus.obj
              ((DerivedCategory.Plus.singleFunctor (Modules.{u, r, max u r v w} O) 0).obj S.X₁))) ≫
        ((resolutionDerivedComparison
          (cechCohomologyZeroFunctor.{u, r, v, w} O 𝒰) J.J₁).hom)⟦(1 : ℤ)⟧' :=
  (comm₃_resolutionDerivedComparison (cechCohomologyZeroFunctor.{u, r, v, w} O 𝒰) hS J.J₁ J.J₂ J.J₃
    J.f J.g J.zero J.comm_f J.comm_g J.shortExact J.mappedShortExact).trans
    (eq_whisker (mapδ_rightDerivedFunctorPlus_comp_ι_singlePlusδ
      (cechCohomologyZeroFunctor.{u, r, v, w} O 𝒰) hS) _)

/-- **The `derivedδ_eq` field of `CechDerivedComparison`.** -/
theorem derivedδ_eq {S : ShortComplex (Modules.{u, r, max u r v w} O)}
    (hS : S.ShortExact) (J : ResolutionShortComplex.{u, r, v, w} O 𝒰 S) (n : ℕ) :
    (eqToHom (derivedDeltaFunctor_functor.{u, r, v, w} O 𝒰 n).symm).app S.X₃ ≫
        (derivedDeltaFunctor.{u, r, v, w} O 𝒰).δ hS n ≫
        (eqToHom (derivedDeltaFunctor_functor.{u, r, v, w} O 𝒰 (n + 1))).app S.X₁ =
      rightDerivedConnecting.{u, r, v, w} O 𝒰 J n :=
  derivedδ_eq_of_comm₃.{u, r, v, w} O 𝒰 hS J n (comm₃_cech.{u, r, v, w} O 𝒰 hS J)


/-- **Stacks Project, Tag 01EN, first assertion (construction), at four independent
universes.** The space, the structure ring, the coefficient modules and the covering index are
independent; the module universe is `max u r v w`, as the indexed products and injective
resolutions need. Every field is the four-universe one of
`Stacks.Cohomology.CechComparisonU`, over the Godement effacement of
`Stacks.Cohomology.CechComparisonU.effaceable_cechDeltaFunctor` and the `derivedδ_eq` field
proved above.

This construction carries the first assertion's proof obligation. -/
@[stacks 01EN "construction of the canonical delta-functor isomorphism"]
def cechDerivedComparison : CechDerivedComparison.{u, r, v, w} O 𝒰 :=
  letI := enoughInjectives_modules.{u, r, v, w} O 𝒰
  -- `cechDerivedComparisonOfDerivedδ` binds its universes in the order `u, r, w, v`.
  cechDerivedComparisonOfDerivedδ.{u, r, w, v} O 𝒰 (derivedδ_eq.{u, r, v, w} O 𝒰)

end Stacks.Cohomology.CechComparisonU

namespace Stacks.Cohomology.CechComparison

attribute [local instance] HasDerivedCategory.standard

variable {X : Type u} [TopologicalSpace X]
  (O : Sheaf (Opens.grothendieckTopology X) RingCat.{u})
  (𝒰 : CechExactFunctor.CechOpenCover.{u, u} (TopCat.of X))

/-- **Stacks Project, Tag 01EN, first assertion (construction), with the four universes
identified.** The four-universe construction transported along
`Stacks.Cohomology.CechComparisonU.cechDerivedComparisonEquiv`, whose two round trips are `rfl`. -/
def cechDerivedComparison : CechDerivedComparison.{u} O 𝒰 :=
  CechComparisonU.cechDerivedComparisonEquiv O 𝒰
    (CechComparisonU.cechDerivedComparison.{u, u, u, u} O 𝒰)

end Stacks.Cohomology.CechComparison


end
