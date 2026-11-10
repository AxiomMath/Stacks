module

public import StacksFrontier.AlgebraicGeometry.Duality.ProperOverField.StructureSheafHom
public import StacksFrontier.AlgebraicGeometry.Duality.ProperOverField.DualizingComplex
public import StacksFrontier.AlgebraicGeometry.Duality.GorensteinSchemes.DualizingInvertible
public import
  StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizing.DualizingComplexModelIndependence
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.QuasiCoherentPerfectDual
public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.TransformedDiagonal.ModelTransport
public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.SerreFunctors.InvertibleTwist
public import StacksFrontier.AlgebraicGeometry.Modules.DerivedMonoidalModelComparison
public import StacksFrontier.AlgebraicGeometry.Perfect.PerfectApproximation.LocallySmall
public import StacksFrontier.Homology.DerivedCategory.Bridge.Basic
public import StacksFrontier.CategoryTheory.Monoidal.InvertibleTransport
public import StacksFrontier.CategoryTheory.Monoidal.InvertibleObjectFunctor
public import StacksFrontier.CategoryTheory.Monoidal.InvertibleObjectDual
public import StacksFrontier.CategoryTheory.Monoidal.ReseatExactPairing
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Monoidal.DerivedCategoryModelComparison
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.LeftDualIsPerfect
public import StacksFrontier.AlgebraicGeometry.ProperSupportCoherent.ExtFinitenessUnconditional
public import StacksFrontier.AlgebraicGeometry.ProperSupportCoherent.TotalExtDimensionOverAField
public import StacksFrontier.AlgebraicGeometry.Perfect.PseudoCoherentComplex.PerfectBoundedCoherent
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.QuasicoherentCohomology
public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.TransformedDiagonal.Basic
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.TensorSymmetry
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafTensorAdditiveOnOpens

/-!
# The Serre functor of a proper Gorenstein scheme over a field

Let `X` be a proper scheme over a field `k` which is Gorenstein, and let `ω_X^•` be the
dualizing complex of [Stacks, Tag 0FVV]. Then `S(K) = K ⊗^𝐋 ω_X^•` is a Serre functor on
`D_perf(𝒪_X)` ([Stacks, Tag 0FY8]).

The proof is the source's. `ω_X^•` is a dualizing complex ([Stacks, Tag 0FVV]) and `X` is
Gorenstein, so `ω_X^•` is an invertible object of `D(𝒪_X)` ([Stacks, Tag 0BFQ]); hence it is
perfect and `S` is a self-equivalence of `D_perf(𝒪_X)`. The Serre pairing comes from
`Hom_X(K, L) = Hom_X(𝒪_X, K^∨ ⊗ L)` and `Hom_X(L, K ⊗ ω_X^•) = Hom_X(K^∨ ⊗ L, ω_X^•)`, both by the
exact pairing of a perfect object with its dual ([Stacks, Tags 0FPC, 08DQ]), together with the
duality `Hom_X(E, ω_X^•) = H⁰(X, E)^∨ = Hom_X(𝒪_X, E)^∨` ([Stacks, Tag 0FVV]) and the finiteness of
`Hom_X(𝒪_X, E)` ([Stacks, Tag 0D0D]). The bifunctoriality, which the source omits, is
`CategoryTheory.SerreEquivalence.ofTensorInvertible`.

## Main results

* `Stacks.Duality.isInvertible_dualizingComplexOverField` — `ω_X^•` is invertible for `X`
  Gorenstein.
* `Stacks.Duality.finiteDimensional_hom_unit` — `Hom_X(𝒪_X, E)` is finite dimensional for `E`
  perfect.
* `Stacks.Duality.monoidalPreadditive_canonicalDerivedMonoidal`,
  `Stacks.Duality.monoidalLinear_canonicalDerivedMonoidal` — the derived tensor product is
  additive, and `k`-linear, in each variable.
* `Stacks.Duality.serreEquivalenceOfIsGorenstein` — [Stacks, Tag 0FY8].

## Implementation notes

`D(𝒪_X)` is the locally small model, at which [Stacks, Tag 0FVV] is stated, with the monoidal
structure `AlgebraicGeometry.Scheme.Modules.canonicalDerivedMonoidal`, whose tensor product is the
derived tensor product of [Stacks, Tag 06YU] on the nose; `k` acts through
`AlgebraicGeometry.modulesLinear`. Results proved at the standard model ([Stacks, Tags 0BFQ, 0D0D])
are carried across the comparison of the two models.

## References

* [Stacks Project, Tag 0FY8](https://stacks.math.columbia.edu/tag/0FY8)
* [Stacks Project, Tag 0FVV](https://stacks.math.columbia.edu/tag/0FVV)
* [Stacks Project, Tag 0BFQ](https://stacks.math.columbia.edu/tag/0BFQ)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for sheaves of modules on a small site.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] SheafOfModules.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry

universe u

namespace Stacks.Duality

section Perfect

variable {X : Scheme.{u}}

/-- **An object with a left dual for the re-seated derived tensor product is perfect**:
[Stacks, Tag 0FPD] for the monoidal structure of [Stacks, Tag 0FPT], of which
`AlgebraicGeometry.Scheme.Modules.canonicalDerivedMonoidal` is a re-seating. -/
theorem isPerfect_of_exactPairing_canonical (M N : DerivedCategory X.Modules)
    (p : letI := Scheme.Modules.canonicalDerivedMonoidal X; ExactPairing M N) :
    Stacks.Cohomology.PerfectComplexes.IsPerfect (X := X.toRingedSpace) M := by
  let := Stacks.SheafOfModules.DerivedMonoidal.derivedMonoidal X.sheaf
  exact Stacks.Cohomology.LeftDualPerfect.isPerfect_of_exactPairing X.toRingedSpace M N
    (exactPairingOfReseat (Stacks.SheafOfModules.DerivedMonoidal.monoidalTensorCanonicalIso X.sheaf)
      (Stacks.SheafOfModules.DerivedMonoidal.canonicalUnitIso X.sheaf) M N p)

/-- **A perfect object has a right dual** for the re-seated derived tensor product: its derived
dual ([Stacks, Tag 0FPC]), carried from the standard model. -/
@[instance_reducible]
def hasRightDualOfIsPerfect (A : DerivedCategory X.Modules)
    (hA : Stacks.Cohomology.PerfectComplexes.IsPerfect (X := X.toRingedSpace) A) :
    letI := Scheme.Modules.canonicalDerivedMonoidal X
    HasRightDual A :=
  let := Scheme.Modules.canonicalDerivedMonoidal X
  @HasRightDual.mk _ _ _ A (Stacks.SheafOfModules.derivedDual X.sheaf A)
    (Scheme.Modules.exactPairingOfStandard X A _
      (exactPairingDerivedDualStandard A
        ((AlgebraicGeometry.PerfectApproximation.isPerfect_standard_iff A).2 hA)))

/-- **The derived tensor product of two perfect objects is perfect**: the tensor product of their
exact pairings is one. -/
theorem isPerfect_tensorObj_canonical {A B : DerivedCategory X.Modules}
    (hA : Stacks.Cohomology.PerfectComplexes.IsPerfect (X := X.toRingedSpace) A)
    (hB : Stacks.Cohomology.PerfectComplexes.IsPerfect (X := X.toRingedSpace) B) :
    letI := Scheme.Modules.canonicalDerivedMonoidal X
    Stacks.Cohomology.PerfectComplexes.IsPerfect (X := X.toRingedSpace)
      (show DerivedCategory X.Modules from A ⊗ B) := by
  let := Scheme.Modules.canonicalDerivedMonoidal X
  let : HasRightDual A := hasRightDualOfIsPerfect A hA
  let : HasRightDual B := hasRightDualOfIsPerfect B hB
  exact isPerfect_of_exactPairing_canonical _ _ (ExactPairing.tensor (Y₁ := Aᘁ) (Y₂ := Bᘁ))

/-- **The dual of a perfect object is perfect**: in the symmetric monoidal derived category the
exact pairing of `A` with `Aᘁ` swaps to one of `Aᘁ` with `A`. -/
theorem isPerfect_rightDual_canonical (A : DerivedCategory X.Modules)
    (hA : Stacks.Cohomology.PerfectComplexes.IsPerfect (X := X.toRingedSpace) A) :
    letI := Scheme.Modules.canonicalDerivedMonoidal X
    letI : HasRightDual A := hasRightDualOfIsPerfect A hA
    Stacks.Cohomology.PerfectComplexes.IsPerfect (X := X.toRingedSpace)
      (show DerivedCategory X.Modules from Aᘁ) := by
  let := Scheme.Modules.canonicalDerivedMonoidal X
  let : BraidedCategory (DerivedCategory X.Modules) :=
    (Stacks.SheafOfModules.DerivedMonoidal.canonicalDerivedSymmetric X.sheaf).toBraidedCategory
  let : HasRightDual A := hasRightDualOfIsPerfect A hA
  exact isPerfect_of_exactPairing_canonical _ _ (BraidedCategory.exactPairing_swap A Aᘁ)

/-- **Twisting by an invertible object preserves and reflects perfectness.** An invertible object
and its inverse are perfect, having exact pairings with each other, and `A ≅ (A ⊗ Z) ⊗ Z⁻¹`. -/
theorem inverseImage_tensorRight_isPerfect (Z : DerivedCategory X.Modules)
    (hZ : letI := Scheme.Modules.canonicalDerivedMonoidal X; HasInverse Z) :
    letI := Scheme.Modules.canonicalDerivedMonoidal X
    (show ObjectProperty (DerivedCategory X.Modules) from
      fun K => Stacks.Cohomology.PerfectComplexes.IsPerfect (X := X.toRingedSpace) K).inverseImage
        (MonoidalCategory.tensorRight Z) =
      fun K : DerivedCategory X.Modules =>
        Stacks.Cohomology.PerfectComplexes.IsPerfect (X := X.toRingedSpace) K := by
  let := Scheme.Modules.canonicalDerivedMonoidal X
  let : BraidedCategory (DerivedCategory X.Modules) :=
    (Stacks.SheafOfModules.DerivedMonoidal.canonicalDerivedSymmetric X.sheaf).toBraidedCategory
  let p : ExactPairing Z hZ.inv := hZ.exactPairing
  have hZp := isPerfect_of_exactPairing_canonical Z hZ.inv p
  have hZi :=
    isPerfect_of_exactPairing_canonical hZ.inv Z (BraidedCategory.exactPairing_swap Z hZ.inv)
  funext A
  change Stacks.Cohomology.PerfectComplexes.IsPerfect (X := X.toRingedSpace)
      (show DerivedCategory X.Modules from A ⊗ Z) = _
  refine propext ⟨fun h => ?_, fun h => isPerfect_tensorObj_canonical h hZp⟩
  have h' := isPerfect_tensorObj_canonical h hZi
  let e : (show DerivedCategory X.Modules from (A ⊗ Z) ⊗ hZ.inv) ≅ A :=
    α_ A Z hZ.inv ≪≫ whiskerLeftIso A hZ.isoLeft ≪≫ ρ_ A
  exact (@Stacks.Cohomology.PerfectComplexes.isClosedUnderIsomorphisms_isPerfect.{u, u, u}
    X.toRingedSpace inferInstance).of_iso e h'

/-- **The re-seated derived tensor product is additive in each variable**: fixing either argument
gives a triangulated functor ([Stacks, Tag 06YU]). -/
theorem monoidalPreadditive_canonicalDerivedMonoidal :
    letI := Scheme.Modules.canonicalDerivedMonoidal X
    MonoidalPreadditive (DerivedCategory X.Modules) := by
  let := Scheme.Modules.canonicalDerivedMonoidal X
  let T := Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct X.sheaf
  have hl : ∀ K, (T.tensor.flip.obj K).Additive := fun K => by
    let := T.commShift_left K
    have := T.exact_left K
    infer_instance
  have hr : ∀ K, (T.tensor.obj K).Additive := fun K => by
    let := T.commShift_right K
    have := T.exact_right K
    infer_instance
  refine ⟨fun {A _ _} => ?_, fun {B _ _} => ?_, fun {A _ _} f g => ?_, fun {B _ _} f g => ?_⟩
  · have := hr A
    exact (T.tensor.obj A).map_zero _ _
  · have := hl B
    exact (T.tensor.flip.obj B).map_zero _ _
  · exact (hr A).map_add (f := f) (g := g)
  · exact (hl B).map_add (f := f) (g := g)

end Perfect

variable {k : Type u} [Field k] (Y : Over (Spec (CommRingCat.of k))) [IsProper Y.hom]

/-- **`ω_X^•` is a dualizing complex at the standard model** of `D(𝒪_X)`: [Stacks, Tag 0FVV] at
the locally small model, carried along the comparison of the two models. -/
theorem isDualizingComplex_standard_dualizingComplexOverField :
    haveI : IsLocallyNoetherian Y.left := LocallyOfFiniteType.isLocallyNoetherian Y.hom
    @IsDualizingComplex Y.left _ (HasDerivedCategory.standard _)
      (dualizingComplexOverField Y.hom).obj := by
  have : IsLocallyNoetherian Y.left := LocallyOfFiniteType.isLocallyNoetherian Y.hom
  refine (isDualizingComplex_modelEquiv_iff (HasDerivedCategory.standard _)
    (Scheme.Modules.hasDerivedCategory Y.left) _).1 ?_
  exact isDualizingComplex_of_iso
    ((Scheme.Modules.schemeModulesComparisonFunctorIso Y.left).app _)
    (isDualizingComplex_relativeDualizingComplex_of_isProper Y.hom)

/-- **`ω_X^•` is invertible**, for the re-seated derived tensor product, when `X` is
Gorenstein: [Stacks, Tag 0BFQ] at the standard model, carried to the locally small model along the
monoidal comparison of the two models and then to the re-seating. -/
theorem isInvertible_dualizingComplexOverField [AlgebraicGeometry.IsGorenstein Y.left] :
    letI := Scheme.Modules.canonicalDerivedMonoidal Y.left
    IsInvertible (dualizingComplexOverField Y.hom).obj := by
  have : IsLocallyNoetherian Y.left := LocallyOfFiniteType.isLocallyNoetherian Y.hom
  have h₀ := (isGorenstein_iff_isInvertible_dualizingComplex (X := Y.left) _
    (isDualizingComplex_standard_dualizingComplexOverField Y)).1 inferInstance
  let G := (StacksDraft.DerivedModel.schemeModulesComparison Y.left).functor
  let hstd : MonoidalCategory (@DerivedCategory Y.left.Modules _ _
      (HasDerivedCategory.standard _)) :=
    @Scheme.Modules.derivedMonoidal Y.left (HasDerivedCategory.standard _)
  let hls : MonoidalCategory (DerivedCategory Y.left.Modules) :=
    Scheme.Modules.derivedMonoidal Y.left
  let : G.Monoidal :=
    Stacks.SheafOfModules.DerivedMonoidal.derivedMonoidalModelComparison Y.left.sheaf
      (HasDerivedCategory.standard _) inferInstance G
      (StacksDraft.DerivedModel.shrinkComparisonQhIso Y.left.Modules).symm
  have h₁ : IsInvertible (G.obj (dualizingComplexOverField Y.hom).obj) :=
    IsInvertible.mapOfTensorIsos G h₀ (Functor.Monoidal.εIso G)
      (fun A B => Functor.Monoidal.μIso G A B)
  exact @MonoidalCategory.isInvertible_of_tensorComparison_of_braided _ _
    (Scheme.Modules.derivedMonoidal Y.left) _ _ (Scheme.Modules.canonicalDerivedMonoidal Y.left)
    (Stacks.SheafOfModules.DerivedMonoidal.canonicalDerivedSymmetric Y.left.sheaf).toBraidedCategory
    (𝟭 _) (fun A B => ((Stacks.SheafOfModules.DerivedMonoidal.monoidalTensorCanonicalIso
      Y.left.sheaf).app A).app B)
    (Stacks.SheafOfModules.DerivedMonoidal.canonicalUnitIso Y.left.sheaf) _ h₁

/-- **The trace pairing is perfect**, read for the re-seated derived tensor product, whose unit is
`𝒪_X[0]`: `Stacks.Duality.bijective_structureSheafTrace_comp`. -/
theorem bijective_traceDual_structureSheafTrace (E : quasiCoherentDerivedCategory Y.left) :
    letI := modulesLinear k Y
    letI := Scheme.Modules.canonicalDerivedMonoidal Y.left
    Function.Bijective (SerreTrace.traceDual (dualizingComplexOverField Y.hom).obj
      (structureSheafTrace Y) E.obj) :=
  bijective_structureSheafTrace_comp Y E

/-- **`Hom(𝒪_X, E)` is finite dimensional** for a perfect `E` on `X` proper over `k`: this is
[Stacks, Tag 0D0D] at the standard model, `𝒪_X` and `E` lying in `D^b_Coh(𝒪_X)`
([Stacks, Tag 0FXU]). -/
theorem finiteDimensional_hom_unit (E : DerivedCategory Y.left.Modules)
    (hE : Stacks.Cohomology.PerfectComplexes.IsPerfect (X := Y.left.toRingedSpace) E) :
    letI := modulesLinear k Y
    letI := Scheme.Modules.canonicalDerivedMonoidal Y.left
    FiniteDimensional k (𝟙_ (DerivedCategory Y.left.Modules) ⟶ E) := by
  let := modulesLinear k Y
  let := Scheme.Modules.canonicalDerivedMonoidal Y.left
  have : IsNoetherian Y.left :=
    Stacks.AlgebraicGeometry.ProperSupportCoherent.isNoetherian_of_isProper_over_field Y
  have hO : Stacks.Cohomology.PerfectComplexes.IsPerfect (X := Y.left.toRingedSpace)
      (𝟙_ (DerivedCategory Y.left.Modules)) :=
    isPerfect_of_exactPairing_canonical _ (𝟙_ _) exactPairingUnit
  have hb := fun F
      (hF : Stacks.Cohomology.PerfectComplexes.IsPerfect (X := Y.left.toRingedSpace) F) =>
    @Stacks.AlgebraicGeometry.PerfectCohomology.isBoundedCoherent_of_isPerfect Y.left _
      (HasDerivedCategory.standard _) _ ((PerfectApproximation.isPerfect_standard_iff _).2 hF)
  have bO := hb _ hO
  have bE := hb _ hE
  let G := StacksDraft.DerivedModel.schemeModulesComparison Y.left
  have hstd : Module.Finite k (G.inverse.obj (𝟙_ (DerivedCategory Y.left.Modules)) ⟶
      G.inverse.obj E) := by
    have hfin := Stacks.AlgebraicGeometry.ProperSupportCoherent.moduleFinite_ext_of_proper
      (A := k) Y (G.inverse.obj (𝟙_ (DerivedCategory Y.left.Modules))) (G.inverse.obj E)
      ⟨bO.1.2, bO.2⟩ ⟨bE.1.1, bE.2⟩ 0
    exact Module.Finite.equiv (Linear.homCongr k (Iso.refl _)
      ((shiftFunctorZero (@DerivedCategory Y.left.Modules _ _ (HasDerivedCategory.standard _))
        ℤ).app (G.inverse.obj E)))
  exact Module.Finite.equiv (StacksDraft.DerivedModel.modelHomLinearEquiv Y.left k _ E).symm

section Linear

attribute [local instance] Stacks.Topology.SheafTensorAdditiveOnOpens.sheafTensorAdditive
  Stacks.Topology.SheafTensorAdditiveOnOpens.sheafTensorObjAdditive
  Stacks.Topology.SheafTensorAdditiveOnOpens.hasMapBifunctorSheafTensor

/-- **The re-seated derived tensor product is `k`-linear in each variable**, for a scheme over a
field `k` and any model of `D(𝒪_X)`. Tensoring sheaves of modules is `k`-linear
(`AlgebraicGeometry.tensorLeft_linear`), hence so is the total tensor complex in each variable;
on a K-flat right factor the derived tensor product is the functor that total complex induces on
the derived category (the K-flat comparison of [Stacks, Tag 06YU]), and a functor induced along a
linear localization is linear (`CategoryTheory.Localization.functor_linear_iff`). The other
variable follows by the symmetry. -/
theorem monoidalLinear_canonicalDerivedMonoidal (Z : Over (Spec (CommRingCat.of k))) :
    letI : Linear k Z.left.Modules := modulesLinear k Z
    letI := Scheme.Modules.canonicalDerivedMonoidal Z.left
    haveI := monoidalPreadditive_canonicalDerivedMonoidal (X := Z.left)
    MonoidalLinear k (DerivedCategory Z.left.Modules) := by
  let : Linear k Z.left.Modules := modulesLinear k Z
  let : Linear k (Stacks.DerivedTensor.RingedSite.Modules Z.left.sheaf) := modulesLinear k Z
  let := Scheme.Modules.canonicalDerivedMonoidal Z.left
  let : BraidedCategory (DerivedCategory Z.left.Modules) :=
    (Stacks.SheafOfModules.DerivedMonoidal.canonicalDerivedSymmetric Z.left.sheaf).toBraidedCategory
  have := monoidalPreadditive_canonicalDerivedMonoidal (X := Z.left)
  let T := Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct Z.left.sheaf
  let F := Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Z.left.sheaf
  let Q : CochainComplex Z.left.Modules ℤ ⥤ DerivedCategory Z.left.Modules := DerivedCategory.Q
  -- tensoring sheaves of modules on the right is `k`-linear
  have hmod : ∀ M, (F.flip.obj M).Linear k := fun M => by
    have : (F.obj M).Linear k := tensorLeft_linear k Z M
    exact Functor.linear_of_iso _
      ((Stacks.SheafOfModules.Tensor.sheafTensorBraiding Z.left.sheaf).app M)
  -- every object is the class of a K-flat complex
  have hres : ∀ K : DerivedCategory Z.left.Modules, ∃ L : CochainComplex
      (Stacks.DerivedTensor.RingedSite.Modules Z.left.sheaf) ℤ,
      Stacks.SheafOfModules.KFlat Z.left.sheaf L ∧ Nonempty (Q.obj L ≅ K) := by
    intro K
    have : Q.EssSurj := Localization.essSurj _ (HomologicalComplex.quasiIso _ (ComplexShape.up ℤ))
    obtain ⟨L, p, hL, -, hp, -⟩ :=
      Stacks.SheafOfModules.KFlatResolution.exists_kFlatResolution Z.left.sheaf (Q.objPreimage K)
    have : IsIso (Q.map p) := (DerivedCategory.isIso_Q_map_iff_quasiIso _ p).2 hp
    exact ⟨L, hL, ⟨asIso (Q.map p) ≪≫ Q.objObjPreimageIso K⟩⟩
  -- the derived tensor product is `k`-linear in its first variable
  have hflip : ∀ K : DerivedCategory Z.left.Modules, (T.tensor.flip.obj K).Linear k := by
    intro K
    obtain ⟨L, hL, ⟨e⟩⟩ := hres K
    have : ((F.map₂HomologicalComplex (ComplexShape.up ℤ) (ComplexShape.up ℤ)
        (ComplexShape.up ℤ)).flip.obj L).Linear k := ⟨fun {K₁ L₁} f r => by
      change HomologicalComplex.mapBifunctorMap (r • f) (𝟙 L) F (ComplexShape.up ℤ) =
        r • HomologicalComplex.mapBifunctorMap f (𝟙 L) F (ComplexShape.up ℤ)
      refine HomologicalComplex.hom_ext _ _ fun j =>
        HomologicalComplex.mapBifunctor.hom_ext fun i₁ i₂ h => ?_
      have hlin : (F.map (r • f.f i₁)).app (L.X i₂) = r • (F.map (f.f i₁)).app (L.X i₂) :=
        (F.flip.obj (L.X i₂)).map_smul r (f.f i₁)
      rw [HomologicalComplex.smul_f_apply, Linear.comp_smul,
        HomologicalComplex.ι_mapBifunctorMap, HomologicalComplex.ι_mapBifunctorMap,
        HomologicalComplex.smul_f_apply, hlin, Linear.smul_comp]⟩
    let : Localization.Lifting DerivedCategory.Q
        (HomologicalComplex.quasiIso _ (ComplexShape.up ℤ))
        ((F.map₂HomologicalComplex (ComplexShape.up ℤ) (ComplexShape.up ℤ)
          (ComplexShape.up ℤ)).flip.obj L ⋙ DerivedCategory.Q)
        (T.tensor.flip.obj (DerivedCategory.Q.obj L)) :=
      ⟨NatIso.ofComponents (fun K' => T.comparisonRight K' L hL) (fun {K' K''} f => by
        have h := T.comparisonRight_naturality f (𝟙 L) hL hL
        simp only [CategoryTheory.Functor.map_id, Category.id_comp] at h
        exact h)⟩
    have : (T.tensor.flip.obj (Q.obj L)).Linear k :=
      (Localization.functor_linear_iff DerivedCategory.Q
        (HomologicalComplex.quasiIso _ (ComplexShape.up ℤ)) k
        ((F.map₂HomologicalComplex (ComplexShape.up ℤ) (ComplexShape.up ℤ)
          (ComplexShape.up ℤ)).flip.obj L ⋙ DerivedCategory.Q)
        (T.tensor.flip.obj (DerivedCategory.Q.obj L))).1 inferInstance
    exact Functor.linear_of_iso _ (T.tensor.flip.mapIso e)
  -- and, by the symmetry, in its second variable
  have hR : ∀ (r : k) {A B : DerivedCategory Z.left.Modules} (f : A ⟶ B)
      (X : DerivedCategory Z.left.Modules), (r • f) ▷ X = r • (f ▷ X) :=
    fun r {_ _} f X => (hflip X).map_smul f r
  refine ⟨fun X {A B} r f => ?_, hR⟩
  have h1 := BraidedCategory.braiding_naturality_right X (r • f)
  have h2 := BraidedCategory.braiding_naturality_right X f
  rw [← cancel_mono (β_ X B).hom, h1, hR, Linear.comp_smul, Linear.smul_comp, h2]

end Linear

/-- **Stacks Project, Tag 0FY8.** Let `X` be a proper Gorenstein scheme over a field `k`, and let
`ω_X^•` be its dualizing complex ([Stacks, Tag 0FVV]). Then `S(K) = K ⊗^𝐋 ω_X^•` is a Serre functor
on `D_perf(𝒪_X)`: there is a Serre equivalence of `D_perf(𝒪_X)` (`CategoryTheory.SerreEquivalence`)
whose functor is derived tensoring with `ω_X^•`. -/
@[stacks 0FY8]
def serreEquivalenceOfIsGorenstein [AlgebraicGeometry.IsGorenstein Y.left] :
    letI : Linear k Y.left.Modules := modulesLinear k Y
    { E : SerreEquivalence k (C := perfectDerived Y.left) //
      Nonempty (E.equivalence.functor ⋙ ObjectProperty.ι _ ≅ ObjectProperty.ι _ ⋙
        (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor
          Y.left.toRingedSpace.sheaf).flip.obj (dualizingComplexOverField Y.hom).obj) } := by
  let : Linear k Y.left.Modules := modulesLinear k Y
  let := Scheme.Modules.canonicalDerivedMonoidal Y.left
  let : BraidedCategory (DerivedCategory Y.left.Modules) :=
    (Stacks.SheafOfModules.DerivedMonoidal.canonicalDerivedSymmetric Y.left.sheaf).toBraidedCategory
  have : MonoidalPreadditive (DerivedCategory Y.left.Modules) :=
    monoidalPreadditive_canonicalDerivedMonoidal
  have : MonoidalLinear k (DerivedCategory Y.left.Modules) :=
    monoidalLinear_canonicalDerivedMonoidal Y
  have : ObjectProperty.IsClosedUnderIsomorphisms (fun K : DerivedCategory Y.left.Modules =>
      Stacks.Cohomology.PerfectComplexes.IsPerfect (X := Y.left.toRingedSpace) K) :=
    @Stacks.Cohomology.PerfectComplexes.isClosedUnderIsomorphisms_isPerfect.{u, u, u}
      Y.left.toRingedSpace inferInstance
  refine ⟨SerreEquivalence.ofTensorInvertible
    (fun K : DerivedCategory Y.left.Modules =>
      Stacks.Cohomology.PerfectComplexes.IsPerfect (X := Y.left.toRingedSpace) K)
    (fun A hA => hasRightDualOfIsPerfect A hA) (dualizingComplexOverField Y.hom).obj
    (isInvertible_dualizingComplexOverField Y).some
    (inverseImage_tensorRight_isPerfect _ (isInvertible_dualizingComplexOverField Y).some)
    (structureSheafTrace Y)
    (fun K : DerivedCategory Y.left.Modules =>
      Stacks.Cohomology.PerfectComplexes.IsPerfect (X := Y.left.toRingedSpace) K)
    (fun A B hA hB => isPerfect_tensorObj_canonical (isPerfect_rightDual_canonical A hA) hB)
    (fun E hE => finiteDimensional_hom_unit Y E hE)
    (fun E hE => bijective_traceDual_structureSheafTrace Y
      ⟨E, isQuasicoherentDerived_of_isPseudoCoherent Y.left E
        (AlgebraicGeometry.RingedSpace.IsPerfect.isPseudoCoherent hE)⟩),
    ⟨eqToIso ?_⟩⟩
  change ObjectProperty.ι _ ⋙ (curriedTensor (DerivedCategory Y.left.Modules)).flip.obj _ = _
  rw [Scheme.Modules.curriedTensor_canonicalDerivedMonoidal]
  rfl

end Stacks.Duality
