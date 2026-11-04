module

public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.DerivedStalk
public import StacksFrontier.AlgebraicGeometry.Duality.ClosedImmersionTwistedInverseImageLocallySmall
public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizing.ClosedImmersionDualizingModel
public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizing.DerivedStalkModel
public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizing.DualizingComplexModel
public import StacksFrontier.AlgebraicGeometry.Perfect.DerivedStalk.StalkSpellingBridge
public import StacksFrontier.RingTheory.Dualizing.DimensionFunctionSurjective
public import StacksFrontier.RingTheory.Dualizing.NormalizedShift
public import StacksFrontier.RingTheory.LocalCohomology.TopLocalCohomology

/-!
# Normalization of `R ℰom(𝒪_Y, K)` at a point of a closed subscheme

Let `i : Y ⟶ X` be a closed immersion into a locally Noetherian scheme and let `K` be a dualizing
complex on `X`. For `y ∈ Y`, if the derived stalk `K_{i(y)}` is a normalized dualizing complex
over `𝒪_{X,i(y)}`, then the derived stalk at `y` of `R ℰom(𝒪_Y, K)` is a normalized dualizing
complex over `𝒪_{Y,y}`. This is the normalization step in the proof that the restriction of a
dualizing complex along a closed immersion is a dualizing complex normalized at the closed points
of `Y` (the setting of [Stacks, Tag 0E34]).

The argument is the one of [Stacks, Tag 0AWF] and [Stacks, Tag 0A7Y]. Over an affine open
`U = Spec A` of `X` with preimage `i⁻¹U = Spec B`, the complex `K` is the sheaf associated to a
dualizing complex `ω` over `A`, and `R ℰom(𝒪_Y, K)` is the sheaf associated to `RHom_A(B, ω)`
([Stacks, Tag 0A78]). Normalization of a derived stalk is the vanishing at the corresponding prime
of the dimension function of a dualizing model
(`Stacks.Duality.isNormalizedDualizingComplex_derivedStalkFunctor_iff`), and along the surjection
`A → B` the dimension function of `RHom_A(B, ω)` is that of `ω` restricted
(`Dualizing.dualizingDimension_derivedHom_of_surjective`, [Stacks, Tag 0A7Y]). No closedness of
the point is needed.

## Main results

* `isNormalizedDualizingComplex_derivedStalkFunctor_iff`: the derived stalk of `K` at `x` is
  normalized exactly when the dimension function of a dualizing model of `K` over an affine open
  neighbourhood of `x` vanishes at `x`.
* `isNormalizedDualizingComplex_derivedStalkFunctor_iff_of_isDualizingModelOn_derivedHom`:
  normalization at `y` and at `i(y)` agree once `RHom_A(B, ω)` is a dualizing model over `i⁻¹U`
  of a complex on `Y`.
* `isNormalizedDualizingComplex_derivedStalk_derivedSheafHomExactSupport`: the derived stalk of
  `R ℰom(𝒪_Y, K)` at `y` is normalized when that of `K` at `i(y)` is.

## Implementation notes

All derived categories are read at `CategoryTheory.HasDerivedCategory.standard`, the model at which
`Dualizing.IsNormalizedDualizingComplex` and its consumers
(`AlgebraicGeometry.isInvertible_homology_neg_one_of_isGorenstein`) are stated. The functor
`Stacks.Duality.LocallySmall.derivedSheafHomExactSupport` is the locally small model's
`R ℰom(𝒪_Y, -)`; the objects of the two models coincide
(`StacksDraft.DerivedModel.derivedCategory_eq_standard`), so its values are objects of the standard
model. Normalization is `Dualizing.IsNormalizedDualizingComplex.{u, 0}`, the reading at which
`AlgebraicGeometry.derivedStalkFunctor` is consumed; the dimension-function criterion of
[Stacks, Tag 0AWF] is at index `u`, and the two are exchanged by
`Stacks.LocalCohomology.isNormalizedDualizingComplex_of_ulift_zero` and
`Stacks.Duality.isNormalizedDualizingComplex_ulift_zero_of_isNormalizedDualizingComplex`.

## References

* [Stacks Project, Tag 0AWF](https://stacks.math.columbia.edu/tag/0AWF)
* [Stacks Project, Tag 0A7Y](https://stacks.math.columbia.edu/tag/0A7Y)
* [Stacks Project, Tag 0A7W](https://stacks.math.columbia.edu/tag/0A7W)
* [Stacks Project, Tag 0A78](https://stacks.math.columbia.edu/tag/0A78)
* [Stacks Project, Tag 0E34](https://stacks.math.columbia.edu/tag/0E34)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for sheaves of modules on a small site.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] SheafOfModules.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Duality

/-- **Being a dualizing model does not depend on the model of `D(𝒪_X)`.** The derived restriction
to `U` computed at the standard model and at the locally small model agree at every object
(`Stacks.Injectives.mapDerivedCategoryObjIso`), and an object of the standard model is an object
of the locally small one. This is `Stacks.Duality.hasDualizingModelOn_standard_iff` with the
model exposed. -/
theorem isDualizingModelOn_standard_iff {X : Scheme.{u}} [IsLocallyNoetherian X]
    (K : @DerivedCategory X.Modules _ _ (HasDerivedCategory.standard _)) {U : X.Opens}
    (hU : IsAffineOpen U) (ω : DerivedCategory (ModuleCat.{u} Γ(X, U))) :
    @IsDualizingModelOn X _ (HasDerivedCategory.standard _) K U hU ω ↔
      IsDualizingModelOn ((Stacks.Injectives.grothendieckModelEquiv.{u} X.Modules).functor.obj K)
        hU ω := by
  let := HasDerivedCategory.standard U.toScheme.Modules
  have e := Stacks.Injectives.mapDerivedCategoryObjIso.{u} X.Modules
    (Scheme.Modules.restrictFunctor U.ι) K
  exact and_congr_right fun _ => ⟨fun ⟨i⟩ => ⟨e.symm ≪≫ i⟩, fun ⟨i⟩ => ⟨e ≪≫ i⟩⟩

section Standard

attribute [local instance 10000] HasDerivedCategory.standard

/-- A normalized dualizing complex at residue-lift index `u` is one at index `0`: the two
propositions differ only in the universe into which the residue field on the right of the
normalization is lifted, and a universe lift of a module is linearly equivalent to it. This is
the converse of `Stacks.LocalCohomology.isNormalizedDualizingComplex_of_ulift_zero`. -/
theorem isNormalizedDualizingComplex_ulift_zero_of_isNormalizedDualizingComplex
    {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    {ω : DerivedCategory (ModuleCat.{u} A)}
    (h : Dualizing.IsNormalizedDualizingComplex.{u, u} ω) :
    Dualizing.IsNormalizedDualizingComplex.{u, 0} ω :=
  ⟨h.1, h.2.map fun e => e.trans
    ((DerivedCategory.singleFunctor (ModuleCat.{u} (IsLocalRing.ResidueField A)) 0).mapIso
      (LinearEquiv.toModuleIso
        (ULift.moduleEquiv.trans ULift.moduleEquiv.symm)))⟩

/-- The derived stalk functor `AlgebraicGeometry.derivedStalkFunctor`, applied to the class of a
cochain complex `E` of `𝒪_X`-modules, is the degreewise stalk of `E` read in
`D(𝒪_{X,x})`, `Stacks.Duality.derivedStalkOfComplex`. The two stalk functors of sheaves of
modules involved agree up to `AlgebraicGeometry.restrictScalarsStalkFunctorIso`. -/
def derivedStalkFunctorObjIsoDerivedStalkOfComplex {X : Scheme.{u}} (x : X)
    (E : CochainComplex X.Modules ℤ) :
    (derivedStalkFunctor x).obj (DerivedCategory.Q.obj E) ≅ derivedStalkOfComplex x E :=
  (Stacks.ModuleSkyscraper.modulesStalkFunctor X x).mapDerivedCategoryFactors.app E ≪≫
    DerivedCategory.Q.mapIso
      ((NatIso.mapHomologicalComplex
        (show Stacks.ModuleSkyscraper.modulesStalkFunctor X x ≅ modulesStalkFunctor x from
          (restrictScalarsStalkFunctorIso x).symm) (ComplexShape.up ℤ)).app E)

/-- **Normalization of a derived stalk is read off a dualizing model.** Let `ω` be a dualizing
model of `K` over an affine open `U ∋ x`. Then the derived stalk of `K` at `x` is a normalized
dualizing complex over `𝒪_{X,x}` exactly when the dimension function of `ω`
([Stacks, Tag 0A7W]) vanishes at the prime of `x`. -/
theorem isNormalizedDualizingComplex_derivedStalkFunctor_iff {X : Scheme.{u}}
    [IsLocallyNoetherian X] (K : DerivedCategory X.Modules) {U : X.Opens} (hU : IsAffineOpen U)
    (ω : DerivedCategory (ModuleCat.{u} Γ(X, U))) (hω : IsDualizingModelOn K hU ω)
    (x : X) (hx : x ∈ U) :
    letI : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
    Dualizing.IsNormalizedDualizingComplex.{u, 0} ((derivedStalkFunctor x).obj K) ↔
      Dualizing.dualizingDimension.{u, u} ω (hU.primeIdealOf ⟨x, hx⟩) = 0 := by
  let : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  let E := DerivedCategory.Q.objPreimage K
  let e : DerivedCategory.Q.obj E ≅ K := DerivedCategory.Q.objObjPreimageIso K
  have key := isNormalizedDualizingComplex_derivedStalkOfComplex_shift_iff E ⟨e⟩ hU x hx ω hω 0
  let iso : (derivedStalkFunctor x).obj K ≅ (derivedStalkOfComplex x E)⟦-(0 : ℤ)⟧ :=
    (derivedStalkFunctor x).mapIso e.symm ≪≫ derivedStalkFunctorObjIsoDerivedStalkOfComplex x E ≪≫
      ((shiftFunctorZero' (DerivedCategory (ModuleCat.{u} (X.presheaf.stalk x))) (-(0 : ℤ))
        neg_zero).app _).symm
  exact ⟨fun h => (key.1 ((Dualizing.isNormalizedDualizingComplex_congr.{u, u} iso).1
      (Stacks.LocalCohomology.isNormalizedDualizingComplex_of_ulift_zero h))).symm,
    fun h => isNormalizedDualizingComplex_ulift_zero_of_isNormalizedDualizingComplex
      ((Dualizing.isNormalizedDualizingComplex_congr.{u, u} iso).2 (key.2 h.symm))⟩

/-- **Normalization at a point of a closed subscheme, given compatible dualizing models.** Let
`i : Y ⟶ X` be a closed immersion of locally Noetherian schemes, `U ⊆ X` an affine open and `ω`
a dualizing model of `K` over `U`. If `RHom_{Γ(X, U)}(Γ(Y, i⁻¹U), ω)` is a dualizing model of
`E` over the affine open `i⁻¹U`, then at every `y ∈ i⁻¹U` the derived stalk of `E` at `y` is
normalized exactly when the derived stalk of `K` at `i y` is.

Both conditions say that a dimension function vanishes
(`Stacks.Duality.isNormalizedDualizingComplex_derivedStalkFunctor_iff`), and along the
surjection `Γ(X, U) → Γ(Y, i⁻¹U)` the dimension function of `RHom(Γ(Y, i⁻¹U), ω)` is that of
`ω` restricted ([Stacks, Tag 0A7Y]). -/
theorem isNormalizedDualizingComplex_derivedStalkFunctor_iff_of_isDualizingModelOn_derivedHom
    {X Y : Scheme.{u}} [IsLocallyNoetherian X] [IsLocallyNoetherian Y] (i : Y ⟶ X)
    [IsClosedImmersion i] (K : DerivedCategory X.Modules) (E : DerivedCategory Y.Modules)
    {U : X.Opens} (hU : IsAffineOpen U) (ω : DerivedCategory (ModuleCat.{u} Γ(X, U)))
    (hω : IsDualizingModelOn K hU ω)
    (hE : IsDualizingModelOn E (hU.preimage i) ((Dualizing.derivedHom.{u, u} (i.app U).hom).obj ω))
    (y : Y) (hy : i y ∈ U) :
    Dualizing.IsNormalizedDualizingComplex.{u, 0} ((derivedStalkFunctor y).obj E) ↔
      Dualizing.IsNormalizedDualizingComplex.{u, 0} ((derivedStalkFunctor (i y)).obj K) := by
  let : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  let : IsNoetherianRing Γ(Y, i ⁻¹ᵁ U) :=
    IsLocallyNoetherian.component_noetherian ⟨i ⁻¹ᵁ U, hU.preimage i⟩
  have hp : PrimeSpectrum.comap (i.app U).hom ((hU.preimage i).primeIdealOf ⟨y, hy⟩) =
      hU.primeIdealOf ⟨i y, hy⟩ := by
    rw [Scheme.Hom.app_eq_appLE]
    exact IsAffineOpen.comap_primeIdealOf_appLE U hU (i ⁻¹ᵁ U) (hU.preimage i) le_rfl hy
  rw [isNormalizedDualizingComplex_derivedStalkFunctor_iff E (hU.preimage i) _ hE y hy,
    isNormalizedDualizingComplex_derivedStalkFunctor_iff K hU ω hω (i y) hy,
    Dualizing.dualizingDimension_derivedHom_of_surjective (i.app U).hom
      (i.app_surjective U hU) ω hω.1, hp]

end Standard

/-- **`R ℰom(𝒪_Y, -)` preserves normalization of derived stalks.** Let `i : Y ⟶ X` be a closed
immersion into a locally Noetherian scheme, `K` a dualizing complex on `X` and `y ∈ Y`. If the
derived stalk `K_{i(y)}` is a normalized dualizing complex over `𝒪_{X,i(y)}`, then the derived
stalk at `y` of `R ℰom(𝒪_Y, K)` is a normalized dualizing complex over `𝒪_{Y,y}`.

`K` and `R ℰom(𝒪_Y, K)` are objects of the locally small derived categories, at which
`Stacks.Duality.LocallySmall.derivedSheafHomExactSupport` is defined; their derived stalks are
read at the standard model, as `Dualizing.IsNormalizedDualizingComplex` is. Over an affine open
`U ∋ i(y)` with a dualizing model `ω` of `K`, `RHom_{Γ(X, U)}(Γ(Y, i⁻¹U), ω)` is a dualizing model
of `R ℰom(𝒪_Y, K)` over `i⁻¹U` ([Stacks, Tag 0A78],
`Stacks.Duality.isDualizingModelOn_derivedSheafHomExactSupport`), and normalization at `y` and
at `i(y)` then agree by [Stacks, Tag 0A7Y]. -/
theorem isNormalizedDualizingComplex_derivedStalk_derivedSheafHomExactSupport
    {X Y : Scheme.{u}} [IsLocallyNoetherian X] (i : Y ⟶ X) [IsClosedImmersion i]
    (K : DerivedCategory X.Modules) (hK : IsDualizingComplex K) (y : Y)
    (hnorm : letI := HasDerivedCategory.standard X.Modules
      letI := HasDerivedCategory.standard (ModuleCat.{u} (X.presheaf.stalk (i y)))
      Dualizing.IsNormalizedDualizingComplex.{u, 0} ((derivedStalkFunctor (i y)).obj K)) :
    letI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian i
    letI := HasDerivedCategory.standard Y.Modules
    letI := HasDerivedCategory.standard (ModuleCat.{u} (Y.presheaf.stalk y))
    Dualizing.IsNormalizedDualizingComplex.{u, 0}
      ((derivedStalkFunctor y).obj ((LocallySmall.derivedSheafHomExactSupport i).obj K)) := by
  let : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian i
  obtain ⟨-, ⟨U, hU, rfl⟩, hyU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (i y)) isOpen_univ
  obtain ⟨ω, hω⟩ := hK U hU
  exact (isNormalizedDualizingComplex_derivedStalkFunctor_iff_of_isDualizingModelOn_derivedHom
    i K _ hU ω ((isDualizingModelOn_standard_iff K hU ω).2 hω)
    ((isDualizingModelOn_standard_iff _ (hU.preimage i) _).2
      (isDualizingModelOn_derivedSheafHomExactSupport i K hU ω hω)) y hyU).2 hnorm

end Stacks.Duality

end
