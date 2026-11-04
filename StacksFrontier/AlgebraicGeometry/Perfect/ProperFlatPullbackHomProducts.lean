module

public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.AffineDerivedEquivalenceStandard
public import StacksFrontier.Algebra.Homology.DerivedCategory.Products
public import StacksFrontier.CategoryTheory.Limits.HomEquivPiBijective
public import StacksFrontier.CategoryTheory.Monoidal.DualizableHomCorepresentation
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.PerfectDualLeftDual
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.PerfectDualAtTheSpaceHypothesis
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.ProjectionFormulaOverAffineBase
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.UnitComparison
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.FlatDegreewise
public import StacksFrontier.AlgebraicGeometry.Perfect.TensorFinitelyPresentedPerfect
public import StacksFrontier.AlgebraicGeometry.Perfect.ProperFlatPushforwardBaseChangeCanonical
public import StacksFrontier.AlgebraicGeometry.Perfect.ProperFlatPushforwardBaseChange
public import StacksFrontier.AlgebraicGeometry.Perfect.TensorFinitelyPresentedPerfectPushforward
public import StacksFrontier.AlgebraicGeometry.Perfect.PerfectApproximation.Affine

/-!
# Morphisms out of a perfect complex into `O_X ⊗_R ∏ Nₙ`

Let `f : X ⟶ Spec R` be proper, flat and of finite presentation, and let `E` be a perfect object
of `D(𝒪_X)`. For every family `(Nₙ)` of `R`-modules, composing with the projections
`O_X ⊗_R ∏ Nₙ ⟶ O_X ⊗_R Nₙ` is a bijection

`Hom(E, O_X ⊗_R ∏ Nₙ) ≃ ∏ₙ Hom(E, O_X ⊗_R Nₙ)`.

This is the step of the source's proof of [Stacks, Tag 0D2Q] that uses the hypotheses on `f`.
Writing `E^∨` for the dual of `E` and `Q = Rf_*E^∨`, which is perfect by [Stacks, Tag 0A1H],
morphisms `E ⟶ f^*N^~` are morphisms `Q^∨ ⟶ N^~` naturally in `N`
(`CategoryTheory.MonoidalCategory.dualHomEquiv`, fed with the duality of [Stacks, Tag 08DQ] in
the symmetric monoidal `D(𝒪_X)` of [Stacks, Tag 0FPT], the adjunction `Lf^* ⊣ Rf_*`, the unit
comparison `Lf^*𝒪_{Spec R} ≅ 𝒪_X` and the projection formula of [Stacks, Tag 08EU]). On
`Spec R` the equivalence `D(R) ≃ D_QCoh(𝒪_{Spec R})` of [Stacks, Tag 06Z0] turns morphisms
`Q^∨ ⟶ N^~` into morphisms in `D(R)` into `N`, which commute with products because products of
modules are products in `D(R)`.

## Main results

* `Stacks.ProperFlatPullbackLimit.bijective_comp_singleFunctor_tilde_map_π`: on `Spec R`, for an
  object of `D_QCoh`.
* `Stacks.ProperFlatPullbackLimit.bijective_comp_singleFunctor_pullback_map_π`: on `X`, for a
  perfect object.

## Implementation notes

The inputs are stated at the standard model of the derived category, in several spellings of
the category of `𝒪_X`-modules; the model is named explicitly, by `letI` in the statements and
the abbreviation `Stacks.ProperFlatPullbackLimit.StdDerived`.

## References

* [Stacks Project, Tag 0D2Q](https://stacks.math.columbia.edu/tag/0D2Q)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for `R`-modules.
-- `D(R)` for sheaves of modules on a small site.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] ModuleCat.hasDerivedCategory
attribute [local instance] SheafOfModules.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
open scoped Stacks.Topology.SheafTensorAdditiveOnOpens

universe u

namespace Stacks.ProperFlatPullbackLimit

/-- The single functor `Mod(R) ⥤ D(R)` preserves countable products, at any model. -/
lemma preservesLimitsOfShape_singleFunctor_moduleCat (R : CommRingCat.{u})
    [HasDerivedCategory (ModuleCat.{u} R)] :
    PreservesLimitsOfShape (Discrete ℕ) (DerivedCategory.singleFunctor (ModuleCat.{u} R) 0) := by
  have := Stacks.DerivedProducts.preservesLimitsOfShape_Q (A := ModuleCat.{u} R) (I := ℕ)
  have : PreservesLimitsOfShape (Discrete ℕ)
      (CochainComplex.singleFunctor (ModuleCat.{u} R) 0) :=
    inferInstanceAs (PreservesLimitsOfShape (Discrete ℕ)
      (HomologicalComplex.single (ModuleCat.{u} R) (ComplexShape.up ℤ) 0))
  exact preservesLimitsOfShape_of_natIso (DerivedCategory.singleFunctorIsoCompQ _ 0).symm

/-- On `Spec R`, morphisms out of an object of `D_QCoh` into `(∏ Nₙ)^~` are families of morphisms
into the `Ñₙ`. -/
theorem bijective_comp_singleFunctor_tilde_map_π (R : CommRingCat.{u}) (N : ℕ → ModuleCat.{u} R) :
    letI := HasDerivedCategory.standard (Spec R).Modules
    ∀ (Q : DerivedCategory (Spec R).Modules), StandardModel.derivedQuasicoherent R Q →
    Function.Bijective (fun φ : Q ⟶ (DerivedCategory.singleFunctor (Spec R).Modules 0).obj
        ((tilde.functor R).obj (∏ᶜ N)) =>
      fun n => φ ≫ (DerivedCategory.singleFunctor (Spec R).Modules 0).map
        ((tilde.functor R).map (Pi.π N n))) := by
  let := HasDerivedCategory.standard (Spec R).Modules
  let := HasDerivedCategory.standard (ModuleCat.{u} R)
  intro Q hQ
  have := preservesLimitsOfShape_singleFunctor_moduleCat R
  obtain ⟨L, ⟨e⟩⟩ := Functor.EssSurj.mem_essImage (F := derivedTilde R)
    (⟨Q, hQ⟩ : (StandardModel.derivedQuasicoherent R).FullSubcategory)
  let ι' := (StandardModel.derivedQuasicoherent R).ι
  let FF := StandardModel.derivedTildeCompιFullyFaithful R
  let α : DerivedCategory.singleFunctor (ModuleCat.{u} R) 0 ⋙ (derivedTilde R ⋙ ι') ≅
      tilde.functor R ⋙ DerivedCategory.singleFunctor (Spec R).Modules 0 :=
    Functor.isoWhiskerLeft _ (derivedTildeCompι R) ≪≫
      (tilde.functor R).mapDerivedCategorySingleFunctor 0
  let β : ∀ M : ModuleCat.{u} R,
      (Q ⟶ (tilde.functor R ⋙ DerivedCategory.singleFunctor (Spec R).Modules 0).obj M) ≃
        (L ⟶ (DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj M) := fun M =>
    ((ι'.mapIso e).homCongr (α.app M)).symm.trans FF.homEquiv.symm
  refine bijective_comp_map_π_of_equiv (A := tilde.functor R ⋙
      DerivedCategory.singleFunctor (Spec R).Modules 0) β ?_ N
    (bijective_comp_map_π_of_preservesLimit _ N L)
  intro M M' g φ
  apply FF.map_injective
  simp only [β, Equiv.trans_apply, Iso.homCongr_symm, Iso.homCongr_apply, Iso.symm_inv,
    Iso.symm_hom, Functor.FullyFaithful.homEquiv_symm_apply, Functor.FullyFaithful.map_preimage,
    Functor.map_comp, Category.assoc]
  congr 2
  exact α.inv.naturality g

section Pullback

/-- The derived category of `𝒪_X`-modules at the standard model, in the spelling over which the
monoidal structure of [Stacks, Tag 0FPT] and the duals of perfect objects are stated. -/
abbrev StdDerived (X : Scheme.{u}) : Type (u + 1) :=
  @DerivedCategory (Stacks.SheafOfModules.StructureSheafModules X.toRingedSpace.sheaf) _ _
    (HasDerivedCategory.standard _)

variable {R : CommRingCat.{u}} {X : Scheme.{u}} (f : X ⟶ Spec R)

/-- **Core of [Stacks, Tag 0D2Q] for products.** -/
theorem bijective_comp_singleFunctor_pullback_map_π [IsProper f] [Flat f]
    [LocallyOfFinitePresentation f] (N : ℕ → ModuleCat.{u} R) :
    letI := HasDerivedCategory.standard X.Modules
    letI := HasDerivedCategory.standard (StrictlyPerfect.OXMod X.toRingedSpace)
    ∀ (E : DerivedCategory X.Modules),
      Stacks.Cohomology.PerfectComplexes.IsPerfect (X := X.toRingedSpace) E →
    Function.Bijective (fun φ : E ⟶ (DerivedCategory.singleFunctor X.Modules 0).obj
        ((tilde.functor R ⋙ Scheme.Modules.pullback f).obj (∏ᶜ N)) =>
      fun n => φ ≫ (DerivedCategory.singleFunctor X.Modules 0).map
        ((tilde.functor R ⋙ Scheme.Modules.pullback f).map (Pi.π N n))) := by
  let : ∀ Y : Scheme.{u}, HasDerivedCategory Y.Modules := fun _ => HasDerivedCategory.standard _
  let : ∀ Y : Scheme.{u}, HasDerivedCategory (StrictlyPerfect.OXMod Y.toRingedSpace) :=
    fun _ => HasDerivedCategory.standard _
  let : ∀ Y : Scheme.{u},
      HasDerivedCategory (SheafOfModules (structureSheafRing Y.toRingedSpace)) :=
    fun _ => HasDerivedCategory.standard _
  let : ∀ Y : Scheme.{u}, HasDerivedCategory
      (Stacks.SheafOfModules.StructureSheafModules Y.toRingedSpace.sheaf) :=
    fun _ => HasDerivedCategory.standard _
  let : ∀ Y : Scheme.{u}, HasDerivedCategory
      (Stacks.DerivedTensor.RingedSite.Modules Y.toRingedSpace.sheaf) :=
    fun _ => HasDerivedCategory.standard _
  let : ∀ (Y : Scheme.{u}) V, HasDerivedCategory
      (SheafOfModules ((StrictlyPerfect.structureSheafOfRings Y.toRingedSpace).over V)) :=
    fun _ _ => HasDerivedCategory.standard _
  intro E hE
  let mC : MonoidalCategory (StdDerived (Spec R)) :=
    Stacks.SheafOfModules.derivedMonoidalStructure (Spec R).toRingedSpace.sheaf
  let mD : MonoidalCategory (StdDerived X) :=
    Stacks.SheafOfModules.derivedMonoidalStructure X.toRingedSpace.sheaf
  let sD : SymmetricCategory (StdDerived X) :=
    Stacks.SheafOfModules.derivedSymmetricStructure X.toRingedSpace.sheaf
  let F : StdDerived (Spec R) ⥤ StdDerived X :=
    Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback f.toLRSHom.toShHom
  let G : StdDerived X ⥤ StdDerived (Spec R) :=
    Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforward f.toLRSHom.toShHom
  let adj : F ⊣ G :=
    Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedAdjunction f.toLRSHom.toShHom
  let eF : F.obj (𝟙_ (StdDerived (Spec R))) ≅ 𝟙_ (StdDerived X) :=
    Stacks.Cohomology.DerivedPullbackUnit.derivedPullbackUnitIso f.toLRSHom.toShHom
  -- the dual of `E` and its exact pairing
  let E₀ : StdDerived X := E
  let E' : StdDerived X := Stacks.SheafOfModules.derivedDual X.toRingedSpace.sheaf E
  let : ExactPairing E₀ E' := Stacks.SheafOfModules.exactPairingDerivedDual _ E
    (Stacks.Cohomology.PerfectComplexes.isPerfect_ringedSite_of_isPerfect X.toRingedSpace E hE)
  have hE' : Stacks.Cohomology.PerfectComplexes.IsPerfect (X := X.toRingedSpace) E' :=
    Stacks.SheafOfModules.isPerfect_derivedDual_of_isPerfectSpace X.toRingedSpace E hE
  -- `Q = Rf_*E^∨` is perfect, and so is its dual `Q'`
  let Q : StdDerived (Spec R) := G.obj E'
  have hQ : Stacks.Cohomology.PerfectComplexes.IsPerfect (X := (Spec R).toRingedSpace) Q :=
    (Stacks.Cohomology.PerfectComplexes.isPerfect_iff_ringedSpace _).2 <| isPerfect_of_iso_scheme
      ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforward
        f.toLRSHom.toShHom).mapIso (ProperFlatBaseChange.tensorStructureDegreeComplexIso E'))
      (isPerfect_derivedPushforward_tensor_of_isAffine f E'
        ((Stacks.Cohomology.PerfectComplexes.isPerfect_iff_ringedSpace _).1 hE')
        (ProperFlatBaseChange.structureDegreeComplex X)
        (ProperFlatBaseChange.flatProperSupportFinitelyPresented_structure f))
  let Q' : StdDerived (Spec R) := Stacks.SheafOfModules.derivedDual (Spec R).toRingedSpace.sheaf Q
  let : ExactPairing Q Q' := Stacks.SheafOfModules.exactPairingDerivedDual _ Q
    (Stacks.Cohomology.PerfectComplexes.isPerfect_ringedSite_of_isPerfect _ Q hQ)
  have hQ' : StandardModel.derivedQuasicoherent R Q' := fun n =>
    PerfectApproximation.isQuasicoherent_homology_of_isPerfect (Spec R) Q'
      (Stacks.SheafOfModules.isPerfect_derivedDual_of_isPerfectSpace _ Q hQ) n
  -- the projection formula along `H = (-)^~[0]`
  let H : ModuleCat.{u} R ⥤ StdDerived (Spec R) :=
    tilde.functor R ⋙ DerivedCategory.singleFunctor (Spec R).Modules 0
  have hE'qc : Stacks.Cohomology.SupportedComplexes.quasicoherentDerivedProperty X E' := fun n =>
    ProperFlatBaseChange.isQuasicoherent_homology_of_isPerfect E' hE' n
  have hHqc : ∀ M : ModuleCat.{u} R,
      Stacks.Cohomology.SupportedComplexes.quasicoherentDerivedProperty (Spec R) (H.obj M) :=
    fun M n =>
      (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf).prop_of_iso
        ((DerivedCategory.homologyFunctor (Spec R).Modules n).mapIso
          (((tilde.functor R).mapDerivedCategorySingleFunctor 0).app M))
        (isQuasicoherent_homology_mapDerivedCategory_obj R _ n)
  have hPf : ∀ M : ModuleCat.{u} R, IsIso
      (Stacks.Cohomology.DerivedProjectionFormula.projectionFormulaMap
        f.toLRSHom.toShHom E' (H.obj M)) := fun M =>
    Stacks.Cohomology.ProjectionFormulaOverAffineBase.isIso_projectionFormulaMap_of_isQuasicoherent
      f E' hE'qc (H.obj M) (hHqc M)
  let T : ∀ Y : Scheme.{u}, Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor
      Y.toRingedSpace.sheaf ≅ Stacks.SheafOfModules.derivedTensor Y.toRingedSpace.sheaf :=
    fun Y => (Stacks.SheafOfModules.DerivedMonoidal.monoidalTensorCanonicalIso _).symm ≪≫
      Stacks.SheafOfModules.derivedTensorMonoidalIso Y.toRingedSpace.sheaf
  let Pf : H ⋙ F ⋙ (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor
        X.toRingedSpace.sheaf).obj E' ⋙ G ≅
      H ⋙ (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor
        (Spec R).toRingedSpace.sheaf).obj Q :=
    (NatIso.ofComponents (fun M => @asIso _ _ _ _
      (Stacks.Cohomology.DerivedProjectionFormula.projectionFormulaMap
        f.toLRSHom.toShHom E' (H.obj M)) (hPf M)) (fun g =>
        Stacks.Cohomology.DerivedProjectionFormula.projectionFormulaMap_natural_right
          f.toLRSHom.toShHom E' (H.map g))).symm
  let p : H ⋙ F ⋙ MonoidalCategory.tensorRight E' ⋙ G ≅ H ⋙ MonoidalCategory.tensorLeft Q :=
    Functor.isoWhiskerLeft (H ⋙ F)
      (Functor.isoWhiskerRight (BraidedCategory.tensorLeftIsoTensorRight E').symm G) ≪≫
      Functor.isoWhiskerLeft (H ⋙ F) (Functor.isoWhiskerRight ((T X).app E').symm G) ≪≫ Pf ≪≫
      Functor.isoWhiskerLeft H ((T (Spec R)).app Q)
  -- the pullback of `M^~` is the derived pullback of `M^~[0]`
  have hφ : AlgebraicGeometry.IsFlat f.toLRSHom.toShHom := fun x => Flat.stalkMap f x
  let : PreservesFiniteLimits (RingedSpaceModuleAdjunction.modulePullback f.toLRSHom.toShHom) :=
    RingedSpaceModuleAdjunction.preservesFiniteLimits_modulePullback_of_isFlat _ hφ
  let γ : (tilde.functor R ⋙ Scheme.Modules.pullback f) ⋙
      DerivedCategory.singleFunctor X.Modules 0 ≅ H ⋙ F :=
    Functor.isoWhiskerLeft (tilde.functor R)
      ((RingedSpaceModuleAdjunction.modulePullback
          f.toLRSHom.toShHom).mapDerivedCategorySingleFunctor 0).symm ≪≫
      Functor.isoWhiskerLeft (tilde.functor R)
        (Functor.isoWhiskerLeft (DerivedCategory.singleFunctor (Spec R).Modules 0)
          (Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackIsoMapDerivedCategory
            f.toLRSHom.toShHom hφ).symm)
  let A := (tilde.functor R ⋙ Scheme.Modules.pullback f) ⋙ DerivedCategory.singleFunctor X.Modules 0
  let e₁ : ∀ M : ModuleCat.{u} R, (E ⟶ A.obj M) ≃ (E₀ ⟶ F.obj (H.obj M)) := fun M =>
    (γ.app M).homToEquiv
  let β : ∀ M : ModuleCat.{u} R, (E ⟶ A.obj M) ≃ (Q' ⟶ H.obj M) := fun M =>
    (e₁ M).trans (MonoidalCategory.dualHomEquiv adj eF H E₀ E' Q Q' p M)
  refine bijective_comp_map_π_of_equiv β ?_ N
    (bijective_comp_singleFunctor_tilde_map_π R N Q' hQ')
  intro M M' g ψ
  have h₁ : β M' (ψ ≫ A.map g) =
      MonoidalCategory.dualHomEquiv adj eF H E₀ E' Q Q' p M' ((ψ ≫ A.map g) ≫ (γ.app M').hom) :=
    rfl
  have h₂ : β M ψ = MonoidalCategory.dualHomEquiv adj eF H E₀ E' Q Q' p M (ψ ≫ (γ.app M).hom) :=
    rfl
  rw [h₁, h₂, ← MonoidalCategory.dualHomEquiv_naturality]
  congr 1
  exact (Category.assoc _ _ _).trans
    ((congrArg (ψ ≫ ·) (γ.hom.naturality g)).trans (Category.assoc _ _ _).symm)

end Pullback

end Stacks.ProperFlatPullbackLimit
