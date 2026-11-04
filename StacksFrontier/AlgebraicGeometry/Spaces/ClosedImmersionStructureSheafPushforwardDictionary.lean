module

public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionStructureSheafCoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionStructureSheafDirectImage
public import StacksFrontier.AlgebraicGeometry.Spaces.DefiningIdealFiniteTypeOfQuotient
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatModuleIso
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePushforwardChartComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.ClosedImmersionFinitePresentation

/-!
# Flatness and finite presentation read off `i_*𝒪_Z` for a closed immersion

Let `i : Z ⟶ X` be a closed immersion of algebraic spaces over a scheme `S` and let
`p : X ⟶ T` be a morphism of algebraic spaces.  The canonical map `𝒪_X ⟶ i_*𝒪_Z` is surjective
with kernel the kernel ideal sheaf `𝓘 = ker(i♯)`, so the sequence

`0 ⟶ 𝓘 ⟶ 𝒪_X ⟶ i_*𝒪_Z ⟶ 0`

is short exact.  This file reads two properties of the morphism `Z ⟶ T` off the module
`i_*𝒪_Z`:

* if `i_*𝒪_Z` is an `𝒪_X`-module of finite presentation, then `𝓘` is of finite type (Modules on
  Sites, Lemma 082T), so `i` is of finite presentation (Stacks 084Q), and `Z ⟶ T` is locally of
  finite presentation as soon as `p` is;
* if `i_*𝒪_Z` is flat over `T` in the sense of Stacks 05VV, then `Z ⟶ T` is flat.

These are the finite-presentation and flatness entries of the dictionary of Stacks 0D00,
`AlgebraicGeometry.Space.isFlat_of_isFlatOver_pushforwardStructureSheaf` and its neighbours,
for an arbitrary closed immersion in place of the inclusion of a closed subspace presented as a
subfunctor.  They are the last step of the proof of Stacks 087E, where the closed immersion is
the composite of a strict transform with the base change of a closed immersion and so is not an
inclusion of subfunctors on the nose.

## Main definitions

* `Space.pushforwardStructureShortComplex`: the sequence `𝓘 ⟶ 𝒪_X ⟶ i_*𝒪_Z`.

## Main results

* `Space.pushforwardStructureShortComplex_shortExact`: it is short exact for a closed immersion.
* `Space.isFinitePresentation_of_isFinitePresentationOnSite_structureSheafPushforward`: `i` is
  of finite presentation when `i_*𝒪_Z` is.
* `Space.isFlat_comp_of_isFlatOver_structureSheafPushforward`: `Z ⟶ T` is flat when `i_*𝒪_Z`
  is flat over `T`.

## References

* [Stacks Project, Tag 0D00](https://stacks.math.columbia.edu/tag/0D00)
* [Stacks Project, Tag 082T](https://stacks.math.columbia.edu/tag/082T)
* [Stacks Project, Tag 084Q](https://stacks.math.columbia.edu/tag/084Q)
* [Stacks Project, Tag 05VV](https://stacks.math.columbia.edu/tag/05VV)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Z T : AlgebraicSpaces B S hS}

/-- The sequence `𝓘 ⟶ 𝒪_X ⟶ i_*𝒪_Z` of a morphism `i : Z ⟶ X` of algebraic spaces, with the
kernel of the canonical map in the left-hand spot. -/
def pushforwardStructureShortComplex (i : Z ⟶ X) : ShortComplex (Modules.{u, u} B S hS X.1 X.2) :=
  ShortComplex.mk (SheafOfModules.Submodule.ker (pushforwardStructureProjection B S hS i)).ι
    (pushforwardStructureProjection B S hS i)
    (SheafOfModules.Submodule.ker_ι_comp (pushforwardStructureProjection B S hS i))

/-- **`0 ⟶ 𝓘 ⟶ 𝒪_X ⟶ i_*𝒪_Z ⟶ 0` is short exact for a closed immersion `i`.**  The left map is a
kernel of the canonical map, and the canonical map is an epimorphism by the surjectivity clause of
Stacks 03MB. -/
theorem pushforwardStructureShortComplex_shortExact (i : Z ⟶ X)
    (hi : IsClosedImmersion B S hS i.hom) :
    (pushforwardStructureShortComplex B S hS i).ShortExact :=
  { exact := ShortComplex.exact_of_f_is_kernel _
      (SheafOfModules.Submodule.isLimitKernelFork (pushforwardStructureProjection B S hS i))
    mono_f := mono_of_isLimit_fork
      (SheafOfModules.Submodule.isLimitKernelFork (pushforwardStructureProjection B S hS i))
    epi_g := epi_pushforwardStructureProjection B S hS i hi }

/-- **A closed immersion `i` is of finite presentation as soon as `i_*𝒪_Z` is an `𝒪_X`-module of
finite presentation.**  The kernel of the surjection `𝒪_X ⟶ i_*𝒪_Z` from a module of finite type
onto a module of finite presentation is of finite type (Modules on Sites, Lemma 082T), and that
kernel is the kernel ideal sheaf of `i`, whose finite type is finite presentation of `i`
(Stacks 084Q). -/
theorem isFinitePresentation_of_isFinitePresentationOnSite_structureSheafPushforward
    (i : Z ⟶ X) (hi : IsClosedImmersion B S hS i.hom)
    (h : (structureSheafPushforward B S hS i).IsFinitePresentationOnSite) :
    IsFinitePresentation B S hS i.hom := by
  have : ∀ (U : (smallEtaleRingedSite B S hS X.1 X.2).C)
      (N : _root_.SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS X.1 X.2).O).over U)),
      Small.{u, u + 1} N.sections :=
    fun _ N => _root_.SheafOfModules.small_sections_of_isTerminal Over.mkIdTerminal N
  have hker : SheafOfModules.IsFiniteTypeOnSite
      (SheafOfModules.Submodule.ker (pushforwardStructureProjection B S hS i)).toSheafOfModules :=
    Stacks.SheafOfModules.isFiniteTypeOnSite_X₁_of_shortExact_of_small
      (S := pushforwardStructureShortComplex B S hS i)
      (pushforwardStructureShortComplex_shortExact B S hS i hi)
      (isFiniteTypeOnSite_unit_structureRingSheaf B S hS X) h
  rw [ker_pushforwardStructureProjection] at hker
  exact (isFinitePresentation_iff_isFiniteTypeOnSite_kernelIdealSheaf B S hS i hi).2 hker

/-- **`Z ⟶ T` is flat as soon as `i_*𝒪_Z` is flat over `T`**, for a closed immersion
`i : Z ⟶ X` and a morphism `p : X ⟶ T`.  This is
`AlgebraicGeometry.Space.isFlat_comp_of_isFlatOver_chartDirectImage` read through the
identification `AlgebraicGeometry.Space.modulePushforwardIsoChartDirectImage` of the two
spellings of the direct image. -/
theorem isFlat_comp_of_isFlatOver_structureSheafPushforward (i : Z ⟶ X)
    (hi : IsClosedImmersion B S hS i.hom) (p : X ⟶ T)
    (h : IsFlatOver B S hS X.2 p.hom (structureSheafPushforward B S hS i)) :
    IsFlat B S hS (i ≫ p).hom := by
  have : (chartDirectImage.{u, u} B S hS i hi
      (structureSheafModule B S hS Z)).IsQuasicoherentOnSite :=
    SheafOfModules.IsQuasicoherentOnSite.of_iso
      (modulePushforwardIsoChartDirectImage B S hS i hi _)
      (isQuasicoherentOnSite_structureSheafPushforward B S hS i hi)
  exact isFlat_comp_of_isFlatOver_chartDirectImage B S hS i hi p
    (IsFlatOver.of_iso B S hS X.2 (modulePushforwardIsoChartDirectImage B S hS i hi _) h)

end AlgebraicGeometry.Space

end
