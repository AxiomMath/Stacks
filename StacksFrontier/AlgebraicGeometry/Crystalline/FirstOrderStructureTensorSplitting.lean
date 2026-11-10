module

public import StacksFrontier.AlgebraicGeometry.Crystalline.FirstOrderStructureSplitting
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.MonoidalSheafTensorUnitors

/-!
# Tensoring the split square-zero extension with a sheaf of modules

Let `(T, J, δ)` be a divided power scheme over a scheme `Y`, let `T'` be the first-order
universal thickening of [Stacks, Tag 07J2] and let `M` be a sheaf of `𝒪_T`-modules.
`Crystalline.firstOrderThickeningStructureSplitting` splits the square-zero extension

`0 ⟶ Ω_{T/Y,δ} ⟶ p₀_* 𝒪_{T'} ⟶ 𝒪_T ⟶ 0`

in the category of sheaves of `𝒪_T`-modules.  Tensoring by `M` over `𝒪_T` is an additive
functor, so it carries that splitting to a splitting of

`0 ⟶ M ⊗_{𝒪_T} Ω_{T/Y,δ} ⟶ M ⊗_{𝒪_T} p₀_* 𝒪_{T'} ⟶ M ⊗_{𝒪_T} 𝒪_T ⟶ 0`,

and the right unitor identifies the third term with `M`.  In particular `M ⊗_{𝒪_T} Ω_{T/Y,δ}` is
the kernel of `M` tensored with the comorphism of the diagonal `i : T ⟶ T'`.

## Main definitions

* `Crystalline.firstOrderThickeningTensorUnitRestriction` — `M ⊗_{𝒪_T} p₀_* 𝒪_{T'}`.
* `Crystalline.firstOrderThickeningTensorDifferentials` — `M ⊗_{𝒪_T} Ω_{T/Y,δ}`.
* `Crystalline.firstOrderThickeningStructureTensorShortComplex` — the short complex above.
* `Crystalline.firstOrderThickeningStructureTensorSplitting` — its splitting.

## Main results

* `Crystalline.firstOrderThickeningTensorBiprodIso` — `M ⊗ p₀_* 𝒪_{T'} ≅ (M ⊗ Ω_{T/Y,δ}) ⊞ M`.
* `Crystalline.exact_firstOrderThickeningStructureTensorShortComplex` — the tensored complex is
  exact.
* `Crystalline.isLimitKernelFork_firstOrderThickeningTensorInr` — `M ⊗ Ω_{T/Y,δ}` is a kernel of
  `M` tensored with the comorphism of the diagonal.

## Implementation notes

The tensor product of `Mod(𝒪_T)` is `SheafOfModules.monoidalCategorySheafTensor`, the tensor
product sheaf of [Stacks, Tag 01CA] with unit `SheafOfModules.unit`, provided at the spelling
`T.scheme.Modules` by the local instance `Crystalline.monoidalCategorySchemeModules`.

## References

* [Stacks Project, Tag 07J2](https://stacks.math.columbia.edu/tag/07J2)
* [Stacks Project, Tag 07J6](https://stacks.math.columbia.edu/tag/07J6)
* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory

universe u

noncomputable section

namespace Crystalline

/-- The tensor product sheaf as the monoidal product of `Mod(𝒪_X)`, for `X` a scheme:
`SheafOfModules.monoidalCategorySheafTensor` with its type ascribed at
`AlgebraicGeometry.Scheme.Modules`. -/
@[instance_reducible] local instance monoidalCategorySchemeModules (X : Scheme.{u}) :
    MonoidalCategory X.Modules :=
  SheafOfModules.monoidalCategorySheafTensor X.sheaf

/-- The monoidal product of `Mod(𝒪_X)` is bilinear on morphisms. -/
local instance monoidalPreadditiveSchemeModules (X : Scheme.{u}) :
    MonoidalPreadditive X.Modules :=
  SheafOfModules.monoidalPreadditiveSheafTensor X.sheaf

variable (T : DividedPowerScheme.{u}) (Y : Scheme.{u}) (f : T.scheme ⟶ Y) (M : T.scheme.Modules)

/-! ### The two tensor products -/

/-- `M ⊗_{𝒪_T} p₀_* 𝒪_{T'}`, the structure sheaf of the first-order universal thickening,
read as a sheaf of `𝒪_T`-modules through `p₀` and tensored with `M`. -/
def firstOrderThickeningTensorUnitRestriction : T.scheme.Modules :=
  M ⊗ firstOrderThickeningUnitRestriction T Y f

/-- `M ⊗_{𝒪_T} Ω_{T/Y,δ}`, the second summand of [Stacks, Tag 07J6]. -/
def firstOrderThickeningTensorDifferentials : T.scheme.Modules :=
  M ⊗ dpDifferentialsSheaf T Y f

/-- `M` tensored with the inclusion `ω ↦ (0, ω)` of the ideal of the diagonal. -/
def firstOrderThickeningTensorInr :
    firstOrderThickeningTensorDifferentials T Y f M ⟶
      firstOrderThickeningTensorUnitRestriction T Y f M :=
  M ◁ firstOrderThickeningInrSheaf T Y f

/-- `M` tensored with the comorphism `(g, ω) ↦ g` of the diagonal `i : T ⟶ T'`. -/
def firstOrderThickeningTensorProj :
    firstOrderThickeningTensorUnitRestriction T Y f M ⟶ M ⊗ schemeUnitModule T.scheme :=
  M ◁ firstOrderThickeningProjSheaf T Y f

/-! ### The splitting -/

/-- The short complex `0 ⟶ M ⊗ Ω_{T/Y,δ} ⟶ M ⊗ p₀_* 𝒪_{T'} ⟶ M ⊗ 𝒪_T ⟶ 0`, the square-zero
extension of [Stacks, Tag 07J2] tensored with `M`. -/
def firstOrderThickeningStructureTensorShortComplex : ShortComplex T.scheme.Modules :=
  (firstOrderThickeningStructureShortComplex T Y f).map (tensorLeft M)

/-- The splitting of the tensored complex: the image under tensoring by `M` of the splitting
`Crystalline.firstOrderThickeningStructureSplitting` of the square-zero extension. -/
def firstOrderThickeningStructureTensorSplitting :
    (firstOrderThickeningStructureTensorShortComplex T Y f M).Splitting :=
  (firstOrderThickeningStructureSplitting T Y f).map (tensorLeft M)

/-- `M ⊗ p₀_* 𝒪_{T'}` is the direct sum of `M ⊗ Ω_{T/Y,δ}` and `M`, by the splitting of the
square-zero extension of [Stacks, Tag 07J2] tensored with `M`, the third term being identified
with `M` by the right unitor. -/
def firstOrderThickeningTensorBiprodIso :
    firstOrderThickeningTensorUnitRestriction T Y f M ≅
      firstOrderThickeningTensorDifferentials T Y f M ⊞ M :=
  (firstOrderThickeningStructureTensorSplitting T Y f M).isoBinaryBiproduct ≪≫
    biprod.mapIso (Iso.refl _) (ρ_ M)

/-- The tensored complex is exact. -/
theorem exact_firstOrderThickeningStructureTensorShortComplex :
    (firstOrderThickeningStructureTensorShortComplex T Y f M).Exact :=
  (firstOrderThickeningStructureTensorSplitting T Y f M).exact

/-- `M ⊗ Ω_{T/Y,δ}` is a kernel of `M` tensored with the comorphism of the diagonal
`i : T ⟶ T'`. -/
def isLimitKernelFork_firstOrderThickeningTensorInr :
    IsLimit (KernelFork.ofι (firstOrderThickeningTensorInr T Y f M)
      (firstOrderThickeningStructureTensorShortComplex T Y f M).zero) :=
  (firstOrderThickeningStructureTensorSplitting T Y f M).fIsKernel

/-- `M` tensored with the comorphism of `p₀` is a split monomorphism. -/
theorem isSplitMono_firstOrderThickeningTensorInl :
    IsSplitMono (M ◁ firstOrderThickeningInlSheaf T Y f) :=
  ⟨⟨⟨firstOrderThickeningTensorProj T Y f M, by
    change (tensorLeft M).map (firstOrderThickeningInlSheaf T Y f) ≫
      (tensorLeft M).map (firstOrderThickeningProjSheaf T Y f) = _
    have h : firstOrderThickeningInlSheaf T Y f ≫ firstOrderThickeningProjSheaf T Y f = 𝟙 _ :=
      (firstOrderThickeningStructureSplitting T Y f).s_g
    rw [← (tensorLeft M).map_comp, h]
    exact (tensorLeft M).map_id _⟩⟩⟩

/-- `M` tensored with the comorphism of the diagonal is a split epimorphism. -/
theorem isSplitEpi_firstOrderThickeningTensorProj :
    IsSplitEpi (firstOrderThickeningTensorProj T Y f M) :=
  ⟨⟨⟨M ◁ firstOrderThickeningInlSheaf T Y f, by
    change (tensorLeft M).map (firstOrderThickeningInlSheaf T Y f) ≫
      (tensorLeft M).map (firstOrderThickeningProjSheaf T Y f) = _
    have h : firstOrderThickeningInlSheaf T Y f ≫ firstOrderThickeningProjSheaf T Y f = 𝟙 _ :=
      (firstOrderThickeningStructureSplitting T Y f).s_g
    rw [← (tensorLeft M).map_comp, h]
    exact (tensorLeft M).map_id _⟩⟩⟩

end Crystalline

end

end
