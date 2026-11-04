module

public import StacksFrontier.AlgebraicGeometry.Perfect.PerfectApproximation.Comparison
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedPushforward.AffineConservative

/-!
# Approximation by perfect complexes at the locally small model

The condition of [Stacks, Tag 08EM] on a triple `(T, E, m)` and the property of
[Stacks, Tag 08EN] of a scheme are stated at `CategoryTheory.HasDerivedCategory.standard`. This
file reads them at the locally small model `AlgebraicGeometry.Scheme.Modules.hasDerivedCategory`
of `D(𝒪_X)`, where compact generation and the lifting of compact objects are available.

## Main results

* `AlgebraicGeometry.PerfectApproximation.isPerfect_standard_iff`,
  `AlgebraicGeometry.PerfectApproximation.isPseudoCoherentFrom_standard_iff`: perfectness and
  `m`-pseudo-coherence of an object do not depend on the model.
* `AlgebraicGeometry.PerfectApproximation.isQuasicoherent_homology_standard_iff` and
  `AlgebraicGeometry.PerfectApproximation.isZero_stalk_homology_standard_iff`: nor do
  quasi-coherence of a cohomology sheaf and vanishing of its stalks.
* `AlgebraicGeometry.PerfectApproximation.approximationHolds_iff_locallySmall`: the condition of
  Tag 08EM at the locally small model.
* `AlgebraicGeometry.PerfectApproximation.hasApproximationByPerfectComplexes_iff_locallySmall`:
  the property of Tag 08EN at the locally small model.

## Implementation notes

The two models have the same objects (`StacksDraft.DerivedModel.derivedCategory_eq_standard`),
and the comparison `Stacks.Injectives.grothendieckModelEquiv` is the identity on objects and
carries the standard localization functor to the locally small one by definition. A perfect or
pseudo-coherent object is one isomorphic to the image of a complex with a property, so these
transport along the comparison; cohomology sheaves are compared by
`Stacks.Duality.homologyFunctorModelIso`.
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for sheaves of modules on a small site.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] SheafOfModules.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry.PerfectApproximation

variable {X : Scheme.{u}}

/-- The standard model of `D(𝒪_X)`, named so that it can be passed explicitly. -/
abbrev standardModel (X : Scheme.{u}) : HasDerivedCategory.{u + 1} X.Modules :=
  HasDerivedCategory.standard X.Modules

/-- The cohomology sheaves of an object of `D(𝒪_X)` at the two models. -/
def homologyStandardIso (E : DerivedCategory X.Modules) (i : ℤ) :
    (DerivedCategory.homologyFunctor X.Modules i).obj E ≅
      (@DerivedCategory.homologyFunctor X.Modules _ _ (standardModel X) i).obj E :=
  (Stacks.Duality.homologyFunctorModelIso X.Modules i).app E

/-- The comparison of cohomology sheaves at the two models is natural: it intertwines the action
on cohomology of a morphism of the standard model and of its image at the locally small model. -/
theorem homologyStandardIso_naturality {P E : DerivedCategory X.Modules}
    (α : @Quiver.Hom (@DerivedCategory X.Modules _ _ (standardModel X)) _ P E) (i : ℤ) :
    (DerivedCategory.homologyFunctor X.Modules i).map
        ((Stacks.Injectives.grothendieckModelEquiv X.Modules).functor.map α) ≫
      (homologyStandardIso E i).hom =
      (homologyStandardIso P i).hom ≫
        (@DerivedCategory.homologyFunctor X.Modules _ _ (standardModel X) i).map α :=
  (Stacks.Duality.homologyFunctorModelIso X.Modules i).hom.naturality α

/-- The action on a cohomology sheaf of a morphism of the standard model and of its image at the
locally small model are isomorphic arrows. -/
def homologyMapStandardArrowIso {P E : DerivedCategory X.Modules}
    (α : @Quiver.Hom (@DerivedCategory X.Modules _ _ (standardModel X)) _ P E) (i : ℤ) :
    Arrow.mk ((DerivedCategory.homologyFunctor X.Modules i).map
        ((Stacks.Injectives.grothendieckModelEquiv X.Modules).functor.map α)) ≅
      Arrow.mk ((@DerivedCategory.homologyFunctor X.Modules _ _ (standardModel X) i).map α) :=
  Arrow.isoMk (homologyStandardIso P i) (homologyStandardIso E i)
    (homologyStandardIso_naturality α i).symm

/-- Invertibility on a cohomology sheaf does not depend on the model. -/
theorem isIso_homology_map_standard_iff {P E : DerivedCategory X.Modules}
    (α : @Quiver.Hom (@DerivedCategory X.Modules _ _ (standardModel X)) _ P E) (i : ℤ) :
    IsIso ((DerivedCategory.homologyFunctor X.Modules i).map
        ((Stacks.Injectives.grothendieckModelEquiv X.Modules).functor.map α)) ↔
      IsIso ((@DerivedCategory.homologyFunctor X.Modules _ _ (standardModel X) i).map α) :=
  (MorphismProperty.isomorphisms _).arrow_mk_iso_iff (homologyMapStandardArrowIso α i)

/-- Surjectivity on a cohomology sheaf does not depend on the model. -/
theorem epi_homology_map_standard_iff {P E : DerivedCategory X.Modules}
    (α : @Quiver.Hom (@DerivedCategory X.Modules _ _ (standardModel X)) _ P E) (i : ℤ) :
    Epi ((DerivedCategory.homologyFunctor X.Modules i).map
        ((Stacks.Injectives.grothendieckModelEquiv X.Modules).functor.map α)) ↔
      Epi ((@DerivedCategory.homologyFunctor X.Modules _ _ (standardModel X) i).map α) :=
  (MorphismProperty.epimorphisms _).arrow_mk_iso_iff (homologyMapStandardArrowIso α i)

/-- Being isomorphic to the image of a complex with a property does not depend on the model. -/
private theorem exists_complex_standard_iff (p : CochainComplex X.Modules ℤ → Prop)
    (K : DerivedCategory X.Modules) :
    (∃ E, p E ∧ Nonempty ((@DerivedCategory.Q X.Modules _ _ (standardModel X)).obj E ≅ K)) ↔
      ∃ E, p E ∧ Nonempty (DerivedCategory.Q.obj E ≅ K) := by
  constructor
  · rintro ⟨E, hE, ⟨e⟩⟩
    exact ⟨E, hE, ⟨(Stacks.Injectives.grothendieckModelEquiv X.Modules).functor.mapIso e⟩⟩
  · rintro ⟨E, hE, ⟨e⟩⟩
    exact ⟨E, hE, ⟨(Stacks.Injectives.grothendieckModelEquiv X.Modules).inverse.mapIso e⟩⟩

/-- **Perfectness does not depend on the model.** -/
theorem isPerfect_standard_iff (K : DerivedCategory X.Modules) :
    @Stacks.Cohomology.PerfectComplexes.IsPerfect X.toRingedSpace (standardModel X) K ↔
      Stacks.Cohomology.PerfectComplexes.IsPerfect (X := X.toRingedSpace) K := by
  exact exists_complex_standard_iff _ K

/-- **`m`-pseudo-coherence does not depend on the model.** -/
theorem isPseudoCoherentFrom_standard_iff (K : DerivedCategory X.Modules) (m : ℤ) :
    @RingedSpace.IsPseudoCoherentFrom X.toRingedSpace (standardModel X) K m ↔
      RingedSpace.IsPseudoCoherentFrom (X := X.toRingedSpace) K m := by
  exact exists_complex_standard_iff _ K

/-- **Pseudo-coherence does not depend on the model.** -/
theorem isPseudoCoherent_standard_iff (K : DerivedCategory X.Modules) :
    @RingedSpace.IsPseudoCoherent X.toRingedSpace (standardModel X) K ↔
      RingedSpace.IsPseudoCoherent (X := X.toRingedSpace) K := by
  exact exists_complex_standard_iff _ K

/-- **Vanishing of a cohomology sheaf does not depend on the model.** -/
theorem isZero_homology_standard_iff (K : DerivedCategory X.Modules) (i : ℤ) :
    IsZero ((@DerivedCategory.homologyFunctor X.Modules _ _ (standardModel X) i).obj K) ↔
      IsZero ((DerivedCategory.homologyFunctor X.Modules i).obj K) :=
  ⟨fun h => h.of_iso (homologyStandardIso K i), fun h => h.of_iso (homologyStandardIso K i).symm⟩

/-- **Quasi-coherence of a cohomology sheaf does not depend on the model.** -/
theorem isQuasicoherent_homology_standard_iff (K : DerivedCategory X.Modules) (i : ℤ) :
    ((@DerivedCategory.homologyFunctor X.Modules _ _ (standardModel X) i).obj K).IsQuasicoherent ↔
      ((DerivedCategory.homologyFunctor X.Modules i).obj K).IsQuasicoherent :=
  ⟨fun h => (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
      (homologyStandardIso K i).symm h,
    fun h => (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
      (homologyStandardIso K i) h⟩

/-- **Vanishing of a stalk of a cohomology sheaf does not depend on the model.** -/
theorem isZero_stalk_homology_standard_iff (K : DerivedCategory X.Modules) (i : ℤ) (x : X) :
    IsZero (TopCat.Presheaf.stalk (X := X)
        (((@DerivedCategory.homologyFunctor X.Modules _ _ (standardModel X) i).obj
          K).val.presheaf) x) ↔
      IsZero (TopCat.Presheaf.stalk (X := X)
        (((DerivedCategory.homologyFunctor X.Modules i).obj K).val.presheaf) x) := by
  have e := (Scheme.Modules.toPresheaf X ⋙
    TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).mapIso (homologyStandardIso K i)
  exact ⟨fun h => h.of_iso e, fun h => h.of_iso e.symm⟩

/-- **The condition of [Stacks, Tag 08EM] at the locally small model.** Approximation holds for
`(T, E, m)` exactly when there is a perfect object `P` of the locally small `D(𝒪_X)` whose
cohomology sheaves vanish at every point off `T`, together with a morphism `P ⟶ E` approximating
`E` from `m`. -/
theorem approximationHolds_iff_locallySmall (T : Set X) (E : DerivedCategory X.Modules) (m : ℤ) :
    ApproximationHolds X T E m ↔
      ∃ P : DerivedCategory X.Modules,
        Stacks.Cohomology.PerfectComplexes.IsPerfect (X := X.toRingedSpace) P ∧
          (∀ (i : ℤ) (x : X), x ∉ T → IsZero (TopCat.Presheaf.stalk (X := X)
            (((DerivedCategory.homologyFunctor X.Modules i).obj P).val.presheaf) x)) ∧
          ∃ α : P ⟶ E, DerivedCategory.ApproximatesFrom α m := by
  let F := (Stacks.Injectives.grothendieckModelEquiv X.Modules).functor
  let G := (Stacks.Injectives.grothendieckModelEquiv X.Modules).inverse
  have hFG : ∀ {P : DerivedCategory X.Modules} (α : P ⟶ E), F.map (G.map α) = α := fun α =>
    Equiv.apply_symm_apply _ α
  constructor
  · rintro ⟨P, hP, hsupp, β, hiso, hepi⟩
    refine ⟨P, (isPerfect_standard_iff P).1 hP,
      fun i x hx => (isZero_stalk_homology_standard_iff P i x).1 (hsupp i x hx),
      F.map β, fun i hi => (isIso_homology_map_standard_iff β i).2 (hiso i hi),
      (epi_homology_map_standard_iff β m).2 hepi⟩
  · rintro ⟨P, hP, hsupp, α, hiso, hepi⟩
    refine ⟨P, (isPerfect_standard_iff P).2 hP,
      fun i x hx => (isZero_stalk_homology_standard_iff P i x).2 (hsupp i x hx),
      G.map α, fun i hi => (isIso_homology_map_standard_iff (G.map α) i).1 ?_,
      (epi_homology_map_standard_iff (G.map α) m).1 ?_⟩
    · rw [hFG α]
      exact hiso i hi
    · rw [hFG α]
      exact hepi

/-- **The property of [Stacks, Tag 08EN] at the locally small model.** -/
theorem hasApproximationByPerfectComplexes_iff_locallySmall (X : Scheme.{u}) :
    HasApproximationByPerfectComplexes X ↔
      ∀ T : Set X, IsClosed T → IsRetrocompact Tᶜ → ∃ r : ℤ,
        ∀ (E : DerivedCategory X.Modules) (m : ℤ),
          (∀ i : ℤ, ((DerivedCategory.homologyFunctor X.Modules i).obj E).IsQuasicoherent) →
          RingedSpace.IsPseudoCoherentFrom (X := X.toRingedSpace) E (m - r) →
          (∀ (i : ℤ) (x : X), m - r ≤ i → x ∉ T →
            IsZero (TopCat.Presheaf.stalk (X := X)
              (((DerivedCategory.homologyFunctor X.Modules i).obj E).val.presheaf) x)) →
          ∃ P : DerivedCategory X.Modules,
            Stacks.Cohomology.PerfectComplexes.IsPerfect (X := X.toRingedSpace) P ∧
              (∀ (i : ℤ) (x : X), x ∉ T → IsZero (TopCat.Presheaf.stalk (X := X)
                (((DerivedCategory.homologyFunctor X.Modules i).obj P).val.presheaf) x)) ∧
              ∃ α : P ⟶ E, DerivedCategory.ApproximatesFrom α m := by
  rw [← approximationByPerfectComplexes_iff]
  constructor
  · intro h T hT hTc
    obtain ⟨r, hr⟩ := h T hT hTc
    exact ⟨r, fun E m hqc hpc hsupp => (approximationHolds_iff_locallySmall T E m).1
      (hr E m (fun i => (isQuasicoherent_homology_standard_iff E i).2 (hqc i))
        ((isPseudoCoherentFrom_standard_iff E (m - r)).2 hpc)
        fun i x hi hx => (isZero_stalk_homology_standard_iff E i x).2 (hsupp i x hi hx))⟩
  · intro h T hT hTc
    obtain ⟨r, hr⟩ := h T hT hTc
    exact ⟨r, fun E m hqc hpc hsupp => (approximationHolds_iff_locallySmall T E m).2
      (hr E m (fun i => (isQuasicoherent_homology_standard_iff E i).1 (hqc i))
        ((isPseudoCoherentFrom_standard_iff E (m - r)).1 hpc)
        fun i x hi hx => (isZero_stalk_homology_standard_iff E i x).1 (hsupp i x hi hx))⟩

end AlgebraicGeometry.PerfectApproximation

end
