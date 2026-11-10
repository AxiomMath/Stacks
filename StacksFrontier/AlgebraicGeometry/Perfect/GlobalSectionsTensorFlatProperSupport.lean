module

public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryComparisons
public import StacksFrontier.AlgebraicGeometry.DerivedGlobalSectionsOverLeray
public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.AffineDerivedEquivalence
public import StacksFrontier.AlgebraicGeometry.DerivedTildePerfect
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.Support
public import StacksFrontier.AlgebraicGeometry.Flatness.BlowingUp.GrothendieckExistenceProperSupport
public import StacksFrontier.AlgebraicGeometry.Perfect.PerfectApproximation.Affine
public import StacksFrontier.AlgebraicGeometry.Perfect.TensorFinitelyPresentedPerfect
public import StacksFrontier.AlgebraicGeometry.Perfect.TensorFinitelyPresentedPerfectPushforward
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Monoidal.DerivedTensorReseat
public import StacksFrontier.Homology.Perfect.LargeUniverse

/-!
# `RΓ_R(X, ℱ ⊗^𝐋 E)` is perfect for a flat module with proper support

Let `R` be a ring, `f : X ⟶ Spec R` a morphism of finite presentation, `E` a perfect object of
`D(𝒪_X)` and `ℱ` an `𝒪_X`-module of finite presentation, flat over `R`, whose support is proper
over `R`. Then `RΓ_R(X, ℱ ⊗^𝐋 E)` is a perfect object of `D(R)`.

This is the step of the proof of [Stacks, Tag 0CTE] that reads "by Derived Categories of
Schemes, Lemma 36.30.4" ([Stacks, Tag 0A1H]) at each level `Xₙ ⟶ Spec Aₙ` of Situation
[Stacks, Tag 0CTC]: Tag 0A1H is a statement about `Rf_*(E ⊗^𝐋 ℱ)` in `D(𝒪_{Spec R})`, and the
source passes silently to `RΓ(Xₙ, -)` in `D(Aₙ)`. Here that passage is made explicit.

## Main results

* `AlgebraicGeometry.isPerfect_derivedGlobalSectionsOver_tensor_single`: the perfectness
  statement, with the proper-support hypothesis in the shape of Situation [Stacks, Tag 0CTC].
* `AlgebraicGeometry.exists_closeds_isProperOver_supp_of_isClosedImmersion`: that hypothesis
  gives a closed subset proper over the base containing the support, the form
  [Stacks, Tag 0A1H] consumes.
* `AlgebraicGeometry.flatProperSupportFinitelyPresented_single_of_properSupport`: so `ℱ[0]`
  satisfies the hypothesis `AlgebraicGeometry.FlatProperSupportFinitelyPresented` of
  [Stacks, Tag 0A1H].

## Implementation notes

The proof is three identifications:

1. `ℱ[0] ⊗^𝐋 E ≅ E ⊗^𝐋 ℱ[0]` (the symmetry of [Stacks, Tag 0FPB]), after which
   [Stacks, Tag 0A1H] (`AlgebraicGeometry.isPerfect_derivedPushforward_tensor`) says that
   `Rf_*(E ⊗^𝐋 ℱ[0])` is perfect on `Spec R`.
2. A perfect object of `D(𝒪_{Spec R})` is `M̃` for a perfect `M ∈ D(R)`
   ([Stacks, Tag 06Z0], [Stacks, Tag 08EB];
   `AlgebraicGeometry.Scheme.Modules.exists_isPerfect_iso_mapDerivedCategory_tilde`), and
   `RΓ(Spec R, M̃) ≅ M` by the invertibility of the unit of the derived Spec–Γ adjunction
   (`AlgebraicGeometry.isIso_derivedTildeGlobalSectionsAdjunction_unit`).
3. `RΓ(Spec R, Rf_* K) ≅ RΓ_R(X, K)`, the Leray identification
   (`AlgebraicGeometry.derivedGlobalSectionsOverDerivedPushforwardRestrictScalarsIso`) for the
   square `f ≫ 𝟙 = f ≫ Spec(𝟙)`, followed by `(restrict scalars along 𝟙_R) ≅ 𝟭`.

**The model.** [Stacks, Tag 0A1H], the derived pushforward of ringed spaces it is
stated with, and `exists_isPerfect_iso_mapDerivedCategory_tilde` exist only at
`CategoryTheory.HasDerivedCategory.standard`. The main declaration is therefore scoped to that
model by `attribute [local instance 10000] HasDerivedCategory.standard in`, on that declaration
alone; the priority is needed because the import closure carries the locally small model's global
instances. Moving the statement to a free `[HasDerivedCategory]` binder needs a comparison
between the models of the derived category.

## References

* [Stacks Project, Tag 0CTE](https://stacks.math.columbia.edu/tag/0CTE)
* [Stacks Project, Tag 0A1H](https://stacks.math.columbia.edu/tag/0A1H)
* [Stacks Project, Tag 06Z0](https://stacks.math.columbia.edu/tag/06Z0)
* [Stacks Project, Tag 08EB](https://stacks.math.columbia.edu/tag/08EB)
* [Stacks Project, Tag 0D5W](https://stacks.math.columbia.edu/tag/0D5W)
* [Stacks Project, Tag 0FPB](https://stacks.math.columbia.edu/tag/0FPB)
* [Stacks Project, Tag 0CYL](https://stacks.math.columbia.edu/tag/0CYL)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPushforward)
open Stacks.DerivedTensor.RingedSite (derivedTensorProductFunctor)

universe w u

namespace AlgebraicGeometry

/-- **A closed subscheme proper over the base carrying the support gives a closed subset proper
over the base containing it.** If `i : Z ⟶ X` is a closed immersion whose range is the support
of `ℱ` and `Z` is proper over `S`, then the closed subset `i(Z)` of `X` is proper over `S`
([Stacks, Tag 0CYL]) and contains the support of `ℱ`. This converts the proper-support condition
of Situation [Stacks, Tag 0CTC] into the one of [Stacks, Tag 0A1H]. -/
theorem exists_closeds_isProperOver_supp_of_isClosedImmersion {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] (F : X.Modules)
    (hsupp : ∃ (Z : Scheme.{u}) (i : Z ⟶ X), IsClosedImmersion i ∧
      Set.range i = RingedSpace.ModuleSheaf.supp (SheafOfModules.moduleSheafOfModules F) ∧
      IsProper (i ≫ f)) :
    ∃ Z : Closeds X, IsProperOver f Z ∧ SheafOfModules.supp F ⊆ (Z : Set X) := by
  obtain ⟨Z, i, hi, hrange, hprop⟩ := hsupp
  refine ⟨⟨Set.range i, i.isClosedEmbedding.isClosed_range⟩,
    (GrothendieckExistence.isProper_comp_iff_isProperOver_range i f).1 hprop, ?_⟩
  change SheafOfModules.supp F ⊆ Set.range i
  rw [hrange]
  exact (SheafOfModules.supp_eq_moduleSheaf_supp F).ge

/-- **The hypothesis of [Stacks, Tag 0A1H] for a single module with the proper support of
Situation [Stacks, Tag 0CTC].** If `ℱ` is of finite presentation, flat over `S`, and its support
is the range of a closed immersion `Z ⟶ X` with `Z` proper over `S`, then `ℱ` placed in degree
`0` is a bounded complex of finitely presented modules, flat over `S`, with support proper over
`S` (`AlgebraicGeometry.FlatProperSupportFinitelyPresented`). -/
theorem flatProperSupportFinitelyPresented_single_of_properSupport {X S : Scheme.{u}}
    (f : X ⟶ S) [LocallyOfFinitePresentation f] (F : X.Modules) [F.IsFinitePresentation]
    (hflat : IsFlatOver f.toLRSHom.toShHom F)
    (hsupp : ∃ (Z : Scheme.{u}) (i : Z ⟶ X), IsClosedImmersion i ∧
      Set.range i = RingedSpace.ModuleSheaf.supp (SheafOfModules.moduleSheafOfModules F) ∧
      IsProper (i ≫ f)) :
    FlatProperSupportFinitelyPresented f ((CochainComplex.singleFunctor X.Modules 0).obj F) :=
  flatProperSupportFinitelyPresented_singleDegreeComplex' f F inferInstance hflat
    (exists_closeds_isProperOver_supp_of_isClosedImmersion f F hsupp)

attribute [local instance 10000] HasDerivedCategory.standard in
/-- **`RΓ_R(X, ℱ ⊗^𝐋 E)` is perfect.** Let `f : X ⟶ Spec R` be of finite presentation, let `E`
be a perfect object of `D(𝒪_X)` and let `ℱ` be an `𝒪_X`-module of finite presentation, flat over
`R`, whose support is the underlying set of a closed subscheme proper over `R`. Then
`RΓ_R(X, ℱ[0] ⊗^𝐋 E)` is a perfect object of `D(R)`.

This is [Stacks, Tag 0A1H] read in `D(R)` rather than in `D(𝒪_{Spec R})`, the form in which the
proof of [Stacks, Tag 0CTE] uses it at each level of Situation [Stacks, Tag 0CTC]; see the module
documentation for the three identifications involved.

All derived categories are taken at `CategoryTheory.HasDerivedCategory.standard`, scoped to this
declaration: [Stacks, Tag 0A1H] and the derived pushforward of ringed spaces exist only at that
model (see the module documentation). -/
theorem isPerfect_derivedGlobalSectionsOver_tensor_single {R : Type u} [CommRing R]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) (hf : FinitePresentation f)
    (F : X.Modules) [F.IsFinitePresentation] (hflat : IsFlatOver f.toLRSHom.toShHom F)
    (hsupp : ∃ (Z : Scheme.{u}) (i : Z ⟶ X), IsClosedImmersion i ∧
      Set.range i = RingedSpace.ModuleSheaf.supp (SheafOfModules.moduleSheafOfModules F) ∧
      IsProper (i ≫ f))
    [HasDerivedCategory.{w} (ModuleCat.{u} R)] (E : DerivedCategory X.Modules)
    (hE : RingedSpace.IsPerfect (X := X.toRingedSpace) E) :
    StacksDraft.Perfect.IsPerfect ((derivedGlobalSectionsOver f).obj
      (((derivedTensorProductFunctor X.toRingedSpace.sheaf).obj
        ((DerivedCategory.singleFunctor X.Modules 0).obj F)).obj E)) := by
  let : LocallyOfFinitePresentation f := hf.locallyOfFinitePresentation
  have hG : FlatProperSupportFinitelyPresented f (ProperFlatBaseChange.singleDegreeComplex F) :=
    flatProperSupportFinitelyPresented_single_of_properSupport f F hflat hsupp
  let K : DerivedCategory X.Modules := ((derivedTensorProductFunctor X.sheaf).obj E).obj
    (DerivedCategory.Q.obj (ProperFlatBaseChange.singleDegreeComplex F))
  have h1 := isPerfect_derivedPushforward_tensor f hf E hE _ hG
  -- `ℱ[0] ⊗^𝐋 E ≅ K`
  let eK : ((derivedTensorProductFunctor X.toRingedSpace.sheaf).obj
      ((DerivedCategory.singleFunctor X.Modules 0).obj F)).obj E ≅ K :=
    (@BraidedCategory.braiding _ _
        (Stacks.SheafOfModules.DerivedMonoidal.canonicalDerivedMonoidal X.sheaf)
        (Stacks.SheafOfModules.DerivedMonoidal.canonicalDerivedSymmetric X.sheaf).toBraidedCategory
        ((DerivedCategory.singleFunctor X.Modules 0).obj F) E :
      ((derivedTensorProductFunctor X.sheaf).obj
          ((DerivedCategory.singleFunctor X.Modules 0).obj F)).obj E ≅
        ((derivedTensorProductFunctor X.sheaf).obj E).obj
          ((DerivedCategory.singleFunctor X.Modules 0).obj F)) ≪≫
      ((derivedTensorProductFunctor X.sheaf).obj E).mapIso
        ((DerivedCategory.singleFunctorIsoCompQ X.Modules 0).app F)
  -- `RΓ(Spec R, Rf_* K)` is perfect: `Rf_* K` has quasi-coherent cohomology, so it is the
  -- sheafification of its derived global sections, and Tag 08EB applies
  let Ri : DerivedCategory X.Modules ⥤ DerivedCategory (Spec (.of R)).Modules :=
    derivedPushforward f.toLRSHom.toShHom
  let Gq : (DerivedCategoryB.derivedCategoryB (A := (Spec (.of R)).Modules)
      (SheafOfModules.isQuasicoherent (Spec (.of R)).ringCatSheaf)).FullSubcategory :=
    ⟨Ri.obj K, fun n => PerfectApproximation.isQuasicoherent_homology_of_isPerfect _ _ h1 n⟩
  have : IsIso ((derivedTildeGlobalSectionsAdjunction (CommRingCat.of R)).val.counit.app
      (Ri.obj K)) :=
    isIso_derivedTildeGlobalSectionsAdjunction_counit_app (CommRingCat.of R) Gq
  let N := (derivedGlobalSectionsOver (𝟙 (Spec (.of R)))).obj (Ri.obj K)
  have hN : StacksDraft.Perfect.IsPerfect N :=
    (isPerfect_tilde_iff_of_model N).1
      (Stacks.Cohomology.PerfectComplexTriangles.isPerfect_of_iso
        (X := (Spec (.of R)).toRingedSpace)
        (((derivedTildeCompι (CommRingCat.of R)).app N).symm ≪≫
          asIso ((derivedTildeGlobalSectionsAdjunction (CommRingCat.of R)).val.counit.app
            (Ri.obj K))).symm h1)
  -- `RΓ_R(X, K) ≅ RΓ(Spec R, Rf_* K)`, the Leray identification for `f ≫ 𝟙 = f ≫ Spec(𝟙)`
  have hsq : f ≫ 𝟙 (Spec (.of R)) = f ≫ Spec.map (CommRingCat.ofHom (RingHom.id R)) := by
    rw [show CommRingCat.ofHom (RingHom.id R) = 𝟙 (CommRingCat.of R) from rfl, Spec.map_id]
  let αi : (Scheme.Modules.pushforward f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ Ri :=
    Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforwardUnit f.toLRSHom.toShHom
  have : Ri.IsRightDerivedFunctor αi (HomotopyCategory.quasiIso X.Modules (ComplexShape.up ℤ)) :=
    open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces in
    isRightDerivedFunctor_of_isIso_app_isKInjective
      _ (Scheme.Modules.exists_quasiIso_isKInjective X) DerivedCategory.Qh _ _ fun I hI =>
        isIso_derivedPushforwardUnit_app_of_isKInjective f.toLRSHom.toShHom I hI
  let eL : (derivedGlobalSectionsOver f).obj K ≅ N :=
    ((Stacks.Homology.mapDerivedCategoryIdIso.app _).symm ≪≫
      (Stacks.DerivedCategoryComparisons.mapDerivedCategoryIsoOfNatIso _ _
        (ModuleCat.restrictScalarsId R).symm).app _) ≪≫
      ((derivedGlobalSectionsOverPushforwardRestrictScalarsIso f (𝟙 (Spec (.of R))) f
        (RingHom.id R) Ri αi hsq).app K).symm
  exact StacksDraft.Perfect.isPerfect_of_iso ((derivedGlobalSectionsOver f).mapIso eK ≪≫ eL) hN

end AlgebraicGeometry

end
