module

public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.BundleBaseChangeTwist
public import StacksFrontier.AlgebraicGeometry.DerivedAffineMorphism.PullbackPushforwardDerivedTensor
public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.FourierMukai.FlatSingleTensorHomology
public import StacksFrontier.AlgebraicGeometry.Modules.FiniteLocallyFreeDescent.FlatFinitePresentation
public import StacksFrontier.AlgebraicGeometry.ProperSupportCoherent.BoundedBelowDerivedDirectImage
public import StacksFrontier.AlgebraicGeometry.QuasiCoherent.Coherator.QcqsPushforwardBounds

/-!
# A window for the direct image of a quasi-coherent module twisted by a vector bundle

Let `f : X ⟶ S` be a quasi-compact quasi-separated morphism of schemes with `S` quasi-compact,
and let `ℰ` be a finite locally free `𝒪_X`-module. There is an integer `t ≥ 0`, depending on `f`
alone, such that for every quasi-coherent `𝒪_X`-module `ℱ` the object

`Rf_*(ℱ[0] ⊗^𝐋 ℰ[0])`

of `D(𝒪_S)` has cohomology sheaves only in degrees `[0, t]`.

This is the step of the proof of [Stacks, Tag 0FZ7] that replaces the cohomological range of an
arbitrary perfect complex by one range depending on `X` alone: for `S = Spec k` the cohomology
sheaves of `Rf_*(ℱ ⊗ ℰ)` are the groups `H^i(X, ℱ ⊗ ℰ)`, and the source takes the range
`[0, dim X]`. Any range depending on `X` alone serves the source's argument, and the one here is
the uniform vanishing degree of [Stacks, Tag 08D5].

## The argument

`ℰ` is flat ([Stacks, Tag 05P2]), so `H^i(ℱ[0] ⊗^𝐋 ℰ[0]) ≅ H^i(ℱ[0]) ⊗ ℰ` for every `i`
(`AlgebraicGeometry.homologyTensorSingleFlatIso`): the tensor product is concentrated in degree
zero, where it is the quasi-coherent module `ℱ ⊗ ℰ` ([Stacks, Tag 01CE]). The derived direct image
of an object with quasi-coherent cohomology in degrees `[0, 0]` lies in degrees `≥ 0` (left
`t`-exactness, [Stacks, Tag 05TC]) and in degrees `≤ t` with `t` the uniform bound of
[Stacks, Tag 08D5] part (2).

## Main results

* `AlgebraicGeometry.isGE_tensorSingle_singleFlat`,
  `AlgebraicGeometry.isLE_tensorSingle_singleFlat` and
  `AlgebraicGeometry.isQuasicoherent_homology_tensorSingle_singleFlat`: `ℱ[0] ⊗^𝐋 ℰ[0]` is
  concentrated in degree zero and has quasi-coherent cohomology.
* `AlgebraicGeometry.exists_isZero_homology_dpush_tensorSingle_of_isFiniteLocallyFree`: the
  uniform window `[0, t]`, and
  `AlgebraicGeometry.exists_isZero_homology_dpush_singleTensor_of_isFiniteLocallyFree` the same
  for `ℰ[0] ⊗^𝐋 ℱ[0]`.

## Implementation notes

The tensor product is spelled `(dtenR X (ℰ[0])).obj (ℱ[0])` and the direct image `dpush f`, the
spellings of `StacksFrontier/AlgebraicGeometry/DerivedVarieties/FourierMukai/Composition.lean`, at
`CategoryTheory.HasDerivedCategory.standard`. `dtenR X A` is `- ⊗^𝐋 A`, so this is `ℱ[0] ⊗^𝐋 ℰ[0]`
and agrees definitionally with `(dtenLeft X (ℱ[0])).obj (ℰ[0])`, the spelling of
`AlgebraicGeometry.homologyTensorSingleFlatIso`.

## References

* [Stacks Project, Tag 0FZ7](https://stacks.math.columbia.edu/tag/0FZ7)
* [Stacks Project, Tag 08D5](https://stacks.math.columbia.edu/tag/08D5)
* [Stacks Project, Tag 05TC](https://stacks.math.columbia.edu/tag/05TC)
* [Stacks Project, Tag 05P2](https://stacks.math.columbia.edu/tag/05P2)
* [Stacks Project, Tag 01CE](https://stacks.math.columbia.edu/tag/01CE)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

attribute [local instance 100000] HasDerivedCategory.standard

section Tensor

variable {X : Scheme.{u}} (F E : X.Modules)
  (hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree (R := X.ringCatSheaf) E)

include hE in
/-- `ℱ[0] ⊗^𝐋 ℰ[0]` has no cohomology below degree zero, `ℰ` being flat. -/
theorem isGE_tensorSingle_singleFlat :
    ((dtenR X ((DerivedCategory.singleFunctor X.Modules 0).obj E)).obj
      ((DerivedCategory.singleFunctor X.Modules 0).obj F)).IsGE 0 :=
  isGE_tensorSingleFlat X ((DerivedCategory.singleFunctor X.Modules 0).obj F) E
    (AlgebraicGeometry.SheafOfModules.isFlat_of_isFiniteLocallyFree E hE) 0

/-- The cohomology of `ℱ[0] ⊗^𝐋 ℰ[0]` in degree `j` is `H^j(ℱ[0]) ⊗ ℰ`, `ℰ` being flat. -/
private def homologyTensorSingleIso (j : ℤ) :
    (DerivedCategory.homologyFunctor X.Modules j).obj
        ((dtenR X ((DerivedCategory.singleFunctor X.Modules 0).obj E)).obj
          ((DerivedCategory.singleFunctor X.Modules 0).obj F)) ≅
      Scheme.Modules.tensorObjRingedSpace X
        ((DerivedCategory.homologyFunctor X.Modules j).obj
          ((DerivedCategory.singleFunctor X.Modules 0).obj F)) E :=
  homologyTensorSingleFlatIso X ((DerivedCategory.singleFunctor X.Modules 0).obj F) E
    (AlgebraicGeometry.SheafOfModules.isFlat_of_isFiniteLocallyFree E hE) j

include hE in
/-- `ℱ[0] ⊗^𝐋 ℰ[0]` has no cohomology above degree zero: in degree `j` its cohomology is
`H^j(ℱ[0]) ⊗ ℰ`, `ℰ` being flat, and `H^j(ℱ[0])` vanishes for `j > 0`. -/
theorem isLE_tensorSingle_singleFlat :
    ((dtenR X ((DerivedCategory.singleFunctor X.Modules 0).obj E)).obj
      ((DerivedCategory.singleFunctor X.Modules 0).obj F)).IsLE 0 :=
  (DerivedCategory.isLE_iff _ 0).2 fun j hj =>
    IsZero.of_iso
      (isZero_tensorObjRingedSpace_of_isZero X _ E
        (DerivedCategory.isZero_of_isLE ((DerivedCategory.singleFunctor X.Modules 0).obj F)
          0 j hj))
      (homologyTensorSingleIso F E hE j)

include hE in
/-- The cohomology sheaves of `ℱ[0] ⊗^𝐋 ℰ[0]` are quasi-coherent for `ℱ` quasi-coherent: in
degree `j` such a sheaf is `H^j(ℱ[0]) ⊗ ℰ`, a tensor product of quasi-coherent modules. -/
theorem isQuasicoherent_homology_tensorSingle_singleFlat (hF : F.IsQuasicoherent) (j : ℤ) :
    ((DerivedCategory.homologyFunctor X.Modules j).obj
      ((dtenR X ((DerivedCategory.singleFunctor X.Modules 0).obj E)).obj
        ((DerivedCategory.singleFunctor X.Modules 0).obj F))).IsQuasicoherent := by
  have hEq : E.IsQuasicoherent :=
    @Stacks.Chow.isQuasicoherent_of_isFiniteLocallyFree X E hE
  have hH : ((DerivedCategory.homologyFunctor X.Modules j).obj
      ((DerivedCategory.singleFunctor X.Modules 0).obj F)).IsQuasicoherent :=
    Stacks.AlgebraicGeometry.AffinePushforwardTExactness.isQuasicoherent_homology_singleFunctor_obj
      0 F hF j
  exact (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
    (homologyTensorSingleIso F E hE j).symm
    (@AlgebraicGeometry.tensorSheaf_isQuasicoherent X.toRingedSpace _ E hH hEq)

end Tensor

/-- **A uniform window for `Rf_*(ℱ[0] ⊗^𝐋 ℰ[0])`.** Let `f : X ⟶ S` be quasi-compact and
quasi-separated with `S` quasi-compact, and let `ℰ` be a finite locally free `𝒪_X`-module. There
is a `t`, depending on `f` alone, such that for every quasi-coherent `𝒪_X`-module `ℱ` the
cohomology sheaves of `Rf_*(ℱ[0] ⊗^𝐋 ℰ[0])` vanish outside the degrees `[0, t]`.

The tensor product lies in degrees `[0, 0]` with quasi-coherent cohomology; the lower bound is
left `t`-exactness of `Rf_*` and the upper bound is the uniform bound of
[Stacks, Tag 08D5] part (2). -/
theorem exists_isZero_homology_dpush_tensorSingle_of_isFiniteLocallyFree {X S : Scheme.{u}}
    (f : X ⟶ S) [QuasiCompact f] [QuasiSeparated f] [CompactSpace S] (E : X.Modules)
    (hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree (R := X.ringCatSheaf) E) :
    ∃ t : ℕ, ∀ F : X.Modules, F.IsQuasicoherent → ∀ i : ℤ, i < 0 ∨ (t : ℤ) < i →
      IsZero ((DerivedCategory.homologyFunctor S.Modules i).obj
        ((dpush f).obj ((dtenR X ((DerivedCategory.singleFunctor X.Modules 0).obj E)).obj
          ((DerivedCategory.singleFunctor X.Modules 0).obj F)))) := by
  obtain ⟨N, hN⟩ := exists_isLE_derivedPushforward_obj f
  refine ⟨N, fun F hF i hi => ?_⟩
  set T := (dtenR X ((DerivedCategory.singleFunctor X.Modules 0).obj E)).obj
    ((DerivedCategory.singleFunctor X.Modules 0).obj F)
  rcases hi with hi | hi
  · have hGE : ((derivedPushforwardModules f).obj T).IsGE 0 :=
      Stacks.AlgebraicGeometry.ProperSupportCoherent.isGE_derivedPushforward f T 0
        (isGE_tensorSingle_singleFlat F E hE)
    exact DerivedCategory.isZero_of_isGE ((derivedPushforwardModules f).obj T) 0 i hi
  · have hLE := hN T (isQuasicoherent_homology_tensorSingle_singleFlat F E hE hF) 0
      (isLE_tensorSingle_singleFlat F E hE)
    exact @DerivedCategory.isZero_of_isLE _ _ _ _ ((dpush f).obj T) (0 + (N : ℤ)) i (by omega) hLE

/-- **A uniform window for `Rf_*(ℰ[0] ⊗^𝐋 ℱ[0])`**, the same statement as
`exists_isZero_homology_dpush_tensorSingle_of_isFiniteLocallyFree` with the two factors of the
tensor product in the other order: the commutativity isomorphism of the derived tensor product,
`AlgebraicGeometry.dtenRSwapIso`, identifies the two objects. -/
theorem exists_isZero_homology_dpush_singleTensor_of_isFiniteLocallyFree {X S : Scheme.{u}}
    (f : X ⟶ S) [QuasiCompact f] [QuasiSeparated f] [CompactSpace S] (E : X.Modules)
    (hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree (R := X.ringCatSheaf) E) :
    ∃ t : ℕ, ∀ F : X.Modules, F.IsQuasicoherent → ∀ i : ℤ, i < 0 ∨ (t : ℤ) < i →
      IsZero ((DerivedCategory.homologyFunctor S.Modules i).obj
        ((dpush f).obj ((dtenR X ((DerivedCategory.singleFunctor X.Modules 0).obj F)).obj
          ((DerivedCategory.singleFunctor X.Modules 0).obj E)))) := by
  obtain ⟨t, ht⟩ := exists_isZero_homology_dpush_tensorSingle_of_isFiniteLocallyFree f E hE
  exact ⟨t, fun F hF i hi => (ht F hF i hi).of_iso
    ((DerivedCategory.homologyFunctor S.Modules i).mapIso ((dpush f).mapIso
      ((dtenRSwapIso X ((DerivedCategory.singleFunctor X.Modules 0).obj F)).app
        ((DerivedCategory.singleFunctor X.Modules 0).obj E))))⟩

end AlgebraicGeometry

end
