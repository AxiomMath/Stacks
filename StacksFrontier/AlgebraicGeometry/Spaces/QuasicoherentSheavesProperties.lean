module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartModuleSliceComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartRestrictionQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentCoherator
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentCokernelsUnconditional
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentDirectSums
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentKernelsUnconditional
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentTensorProduct
public import StacksFrontier.AlgebraicGeometry.Spaces.ShortExactQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.SliceAssociatedModuleEssSurjFromChart
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleBinaryProducts
public import StacksFrontier.AlgebraicGeometry.Topologies.GlobalPresentationComparison
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.EssentiallySmallInternalHom
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.FinitePresentationKernel
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The category of quasi-coherent modules on an algebraic space

Let `S` be a scheme and `X` an algebraic space over `S`.  Stacks 03M1 lists six properties of
the category `QCoh(𝒪_X)` of quasi-coherent modules on the small étale ringed site of `X`, inside
the category `Mod(𝒪_X)` of all `𝒪_X`-modules: it is closed under direct sums, under colimits,
under kernels and cokernels, under the two-out-of-three property for short exact sequences, under
tensor products, and under the internal Hom out of a module of finite presentation.  This file
states and proves each of the six, one theorem per clause, for the `𝒪_X`-modules whose sections
lie in the universe of the schemes.

## Main results

* `AlgebraicGeometry.Space.isQuasicoherentOnSite_of_isColimit_cofan`: **03M1 (1)**, direct sums.
* `AlgebraicGeometry.Space.isClosedUnderColimitsOfShape_quasicoherentSheaves_of_essentiallySmall`:
  **03M1 (2)**, colimits of small diagrams.
* `AlgebraicGeometry.Space.isQuasicoherentOnSite_kernel_and_cokernel`: **03M1 (3)**, kernels and
  cokernels.
* `AlgebraicGeometry.Space.isQuasicoherentOnSite_shortExact_twoOutOfThree`: **03M1 (4)**, two out
  of three for a short exact sequence of `𝒪_X`-modules.
* `AlgebraicGeometry.Space.isQuasicoherentOnSite_tensorModule_schemeUniverse`: **03M1 (5)**,
  tensor products.
* `AlgebraicGeometry.Space.isQuasicoherentOnSite_internalHomSheafSmall`: **03M1 (6)**, the internal
  Hom out of a quasi-coherent module of finite presentation.

## Implementation notes

`QCoh(𝒪_X)` is `AlgebraicGeometry.Space.QuasicoherentSheaves` (Stacks 03G9): the
`𝒪_X`-modules on the small étale ringed site `AlgebraicGeometry.Space.smallEtaleRingedSite`
which are quasi-coherent in the sense of Stacks 03DL(6), `SheafOfModules.IsQuasicoherentOnSite`.
The module universe is the universe `u` of the schemes, the one in which `Mod(𝒪_X)` is abelian
with no further input (the sheafification instances of
`StacksFrontier.AlgebraicGeometry.Spaces.ModulesAbelian`).

Clauses (1) to (4) assemble results of this development: Descent, Proposition 03DX(2) on the
small étale site of `X`
(`AlgebraicGeometry.Space.isQuasicoherentOnSite_iff_isCartesianOnAffineCharts`), the cokernel
and kernel clauses, and Descent, Proposition 03DW in the uniform form
`AlgebraicGeometry.Space.surjective_val_app_of_epi_of_kernel_isCartesian_unconditional`, which
makes the right-hand map of a short exact sequence with quasi-coherent kernel surjective over the
affine étale charts.  Clause (5) is
`AlgebraicGeometry.Space.isQuasicoherentOnSite_tensorModule` with its two sheafification
conditions supplied at `u`.

The internal Hom of clause (6) is the internal Hom of Stacks 03EM in `Mod(𝒪_X)`,
`AlgebraicGeometry.RingedSite.internalHomSheafSmall`: its sections over an étale chart `U` are
the morphisms `F|_U ⟶ G|_U`, read in the universe `u` because the small étale site is
essentially `u`-small.  Its universe lift is `AlgebraicGeometry.RingedSite.internalHomSheaf`, of
which `AlgebraicGeometry.Space.smallEtaleInternalHom` is the bundled form.  The proof is the
source's: quasi-coherence is local (Stacks 03DN), the restriction of the internal Hom to a slice
is the internal Hom of the restrictions (Stacks 0E8H), on a slice over which `F` has a finite
presentation the internal Hom is a kernel of a map between finite products of copies of `G`, and
the slice of the small étale site of `X` at a chart is the small étale site of the chart, on
which kernels of quasi-coherent modules are quasi-coherent by clause (3).

## References

* [Stacks Project, Tag 03M1](https://stacks.math.columbia.edu/tag/03M1)
* [Stacks Project, Tag 03G9](https://stacks.math.columbia.edu/tag/03G9)
* [Stacks Project, Tag 03DN](https://stacks.math.columbia.edu/tag/03DN)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 03DW](https://stacks.math.columbia.edu/tag/03DW)
* [Stacks Project, Tag 03EM](https://stacks.math.columbia.edu/tag/03EM)
* [Stacks Project, Tag 0E8H](https://stacks.math.columbia.edu/tag/0E8H)
* [Stacks Project, Tag 04M0](https://stacks.math.columbia.edu/tag/04M0)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u w w'

/- The global instance `Abelian (SheafOfModules.{max u v r w} O)` of the cohomology of modules
leaves a stuck universe constraint against the `𝒪_X`-modules at the universe of the schemes; the
abelian structure used here is the one at the pinned universe. -/
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

namespace AlgebraicGeometry.Space

/-! ### Kernels and finite products on the slice at a chart -/

section Slice

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : AlgebraicSpaces B S hS) (W : SmallEtale B S hS X.1)

/-- A module on the slice of the small étale site of `X` at an étale chart `W` is quasi-coherent
exactly when its reading on the small étale site of the chart is
(`AlgebraicGeometry.Space.chartModuleSliceReindex`, Stacks 04M0).  This is
`Stacks.SheafOfModules.isQuasicoherentOnSite_reindex_iff` at the comparison equivalence. -/
theorem isQuasicoherentOnSite_chartModuleSliceReindex_obj_iff
    (K : SheafOfModules.{u} ((structureRingSheaf B S hS X).over W)) :
    ((chartModuleSliceReindex B S hS X W).obj K).IsQuasicoherentOnSite ↔
      K.IsQuasicoherentOnSite :=
  @Stacks.SheafOfModules.isQuasicoherentOnSite_reindex_iff _ _ _ _
    ((SmallEtale.topology B S hS X.1).over W)
    (SmallEtale.topology B S hS (chartSpace B S hS X W).1)
    (SmallEtale.chartLocalizationEquivalence B S hS X.1 W)
    (isContinuous_chartLocalization_chartSpace B S hS X W)
    ((structureRingSheaf B S hS X).over W)
    (isDenseSubsite_chartLocalizationEquivalence_inverse B S hS X W) K

/-- **A kernel of a morphism of quasi-coherent modules on the slice of the small étale site of an
algebraic space at an étale chart is quasi-coherent.**  The slice is the small étale site of the
chart (Stacks 04M0, `AlgebraicGeometry.Space.chartModuleSliceEquiv`), an equivalence which
preserves kernels and quasi-coherence, and on the chart the kernel clause holds. -/
theorem isQuasicoherentOnSite_of_isLimit_kernelFork_over_chart
    {K₁ K₂ : SheafOfModules.{u} ((structureRingSheaf B S hS X).over W)} {f : K₁ ⟶ K₂}
    (k : KernelFork f) (hk : IsLimit k)
    (h₁ : K₁.IsQuasicoherentOnSite) (h₂ : K₂.IsQuasicoherentOnSite) :
    k.pt.IsQuasicoherentOnSite := by
  let E := chartModuleSliceReindex B S hS X W
  have := isClosedUnderKernels_quasicoherentSheaves_schemeUniverse B S hS
    (chartSpace B S hS X W).1 (chartSpace B S hS X W).2
  have h := isQuasicoherentOnSite_chartModuleSliceReindex_obj_iff B S hS X W
  refine (h _).1 ?_
  exact (SheafOfModules.isQuasicoherentOnSite _).prop_of_isLimit_kernelFork
    (KernelFork.mapIsLimit k hk E) ((h _).2 h₁) ((h _).2 h₂)

end Slice

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)

/-! ### Clause (1): direct sums -/

/-- **Stacks 03M1 (1).**  Any direct sum of quasi-coherent `𝒪_X`-modules on an algebraic space
`X` is quasi-coherent: the vertex of a colimiting cofan on a family of quasi-coherent
`𝒪_X`-modules, indexed by an arbitrary type, is quasi-coherent.

This is `AlgebraicGeometry.Space.isQuasicoherentOnSite_of_isColimit_cofan_of_h03DX` with Descent,
Proposition 03DX(2) supplied by
`AlgebraicGeometry.Space.isQuasicoherentOnSite_iff_isCartesianOnAffineCharts`. -/
@[stacks 03M1 "(1) any direct sum of quasi-coherent 𝒪_X-modules is quasi-coherent"]
theorem isQuasicoherentOnSite_of_isColimit_cofan {ι : Type w}
    {G : ι → Modules.{u, u} B S hS F hF} (c : Cofan G) (hc : IsColimit c)
    (hG : ∀ i, (G i).IsQuasicoherentOnSite) :
    c.pt.IsQuasicoherentOnSite :=
  isQuasicoherentOnSite_of_isColimit_cofan_of_h03DX B S hS F hF
    (isQuasicoherentOnSite_iff_isCartesianOnAffineCharts B S hS F hF) c hc hG

/-! ### Clause (2): colimits -/

/-- **Stacks 03M1 (2).**  Any colimit of quasi-coherent `𝒪_X`-modules on an algebraic space `X`
is quasi-coherent: quasi-coherence is closed under colimits of every small shape `K`.

The shape `K` is replaced by its small model, for which this is
`AlgebraicGeometry.Space.isClosedUnderColimitsOfShape_quasicoherentSheaves_schemeUniverse`: a
colimit is the cokernel of a map between two direct sums, and clauses (1) and (3) apply. -/
@[stacks 03M1 "(2) any colimit of quasi-coherent 𝒪_X-modules is quasi-coherent"]
theorem isClosedUnderColimitsOfShape_quasicoherentSheaves_of_essentiallySmall (K : Type w)
    [Category.{w'} K] [EssentiallySmall.{u} K] :
    (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
      ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS F hF).O))).IsClosedUnderColimitsOfShape K :=
  have := isClosedUnderColimitsOfShape_quasicoherentSheaves_schemeUniverse B S hS F hF
    (SmallModel.{u} K)
  ObjectProperty.IsClosedUnderColimitsOfShape.of_equivalence (equivSmallModel.{u} K).symm

/-! ### Clause (3): kernels and cokernels -/

/-- **Stacks 03M1 (3).**  The kernel and the cokernel of a morphism of quasi-coherent
`𝒪_X`-modules on an algebraic space `X` are quasi-coherent. -/
@[stacks 03M1 "(3) the kernel and the cokernel of a morphism of quasi-coherent 𝒪_X-modules are \
quasi-coherent"]
theorem isQuasicoherentOnSite_kernel_and_cokernel {M N : Modules.{u, u} B S hS F hF}
    (f : M ⟶ N) (hM : M.IsQuasicoherentOnSite) (hN : N.IsQuasicoherentOnSite) :
    (kernel f).IsQuasicoherentOnSite ∧ (cokernel f).IsQuasicoherentOnSite := by
  have := isClosedUnderKernels_quasicoherentSheaves_schemeUniverse B S hS F hF
  exact ⟨(SheafOfModules.isQuasicoherentOnSite _).prop_kernel f hM hN,
    isQuasicoherentOnSite_cokernel_unconditional B S hS F hF f⟩

/-! ### Clause (4): short exact sequences -/

/-- The right-hand map of a short exact sequence of `𝒪_X`-modules with quasi-coherent left term
is surjective on the sections over every affine étale chart: its kernel is the left term, hence
cartesian on affine charts, and Descent, Proposition 03DW applies. -/
theorem surjective_g_val_app_of_shortExact {T : ShortComplex (Modules.{u, u} B S hS F hF)}
    (hT : T.ShortExact) (h₁ : T.X₁.IsQuasicoherentOnSite) (U : SmallEtale B S hS F)
    (hU : IsAffine ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj U)) :
    Function.Surjective (T.g.val.app (op U)) := by
  have := hT.mono_f
  have hk : (kernel T.g).IsQuasicoherentOnSite :=
    SheafOfModules.IsQuasicoherentOnSite.of_iso
      (IsLimit.conePointUniqueUpToIso hT.exact.fIsKernel (limit.isLimit _)) h₁
  exact surjective_val_app_of_epi_of_kernel_isCartesian_unconditional B S hS ⟨F, hF⟩ T.g
    hT.epi_g ((isQuasicoherentOnSite_iff_isCartesianOnAffineCharts B S hS F hF _).1 hk) U hU

/-- **Stacks 03M1 (4).**  Given a short exact sequence `0 → 𝓕₁ → 𝓕₂ → 𝓕₃ → 0` of `𝒪_X`-modules
on an algebraic space `X`, if two out of the three terms are quasi-coherent then so is the
third. -/
@[stacks 03M1 "(4) in a short exact sequence of 𝒪_X-modules, if two of the three terms are \
quasi-coherent so is the third"]
theorem isQuasicoherentOnSite_shortExact_twoOutOfThree
    {T : ShortComplex (Modules.{u, u} B S hS F hF)} (hT : T.ShortExact) :
    (T.X₂.IsQuasicoherentOnSite → T.X₃.IsQuasicoherentOnSite → T.X₁.IsQuasicoherentOnSite) ∧
      (T.X₁.IsQuasicoherentOnSite → T.X₃.IsQuasicoherentOnSite →
        T.X₂.IsQuasicoherentOnSite) ∧
      (T.X₁.IsQuasicoherentOnSite → T.X₂.IsQuasicoherentOnSite →
        T.X₃.IsQuasicoherentOnSite) := by
  have h03DX := fun G => (isQuasicoherentOnSite_iff_isCartesianOnAffineCharts B S hS F hF G).1
  refine ⟨fun h₂ h₃ => isQuasicoherent_left_of_shortExact T hT h03DX,
    fun h₁ h₃ => isQuasicoherent_middle_of_shortExact T hT h03DX
      (surjective_g_val_app_of_shortExact B S hS F hF hT h₁),
    fun h₁ h₂ => isQuasicoherent_right_of_shortExact T hT h03DX
      (surjective_g_val_app_of_shortExact B S hS F hF hT h₁)⟩

/-! ### Clause (5): tensor products -/

/-- **Stacks 03M1 (5).**  The tensor product of two quasi-coherent `𝒪_X`-modules on an algebraic
space `X` is quasi-coherent.

The tensor product is `AlgebraicGeometry.Space.tensorModule`, the sheafified objectwise tensor
product on the small étale ringed site; the two sheafification conditions it uses hold at the
universe of the schemes. -/
@[stacks 03M1 "(5) the tensor product of two quasi-coherent 𝒪_X-modules is quasi-coherent"]
theorem isQuasicoherentOnSite_tensorModule_schemeUniverse (M N : Modules.{u, u} B S hS F hF)
    (hM : M.IsQuasicoherentOnSite) (hN : N.IsQuasicoherentOnSite) :
    (tensorModule.{u, u, u} B S hS F hF M N).IsQuasicoherentOnSite :=
  isQuasicoherentOnSite_tensorModule B S hS F hF M N hM hN

/-! ### Clause (6): internal Hom -/

/-- Over an étale chart `W` on which `M` has a finite presentation, the restriction of the
internal Hom `𝓗om_{𝒪_X}(M, N)` to the slice at `W` is quasi-coherent as soon as `N` is: it is a
kernel of a map between finite products of copies of `N|_W`. -/
theorem isQuasicoherentOnSite_over_internalHomSheafSmall (M N : Modules.{u, u} B S hS F hF)
    (hN : N.IsQuasicoherentOnSite) (W : (smallEtaleRingedSite B S hS F hF).C)
    (hW : SheafOfModules.HasFiniteGlobalPresentation (M.over W)) :
    letI := smallEtaleRingedSite_essentiallySmall B S hS F hF
    ((RingedSite.internalHomSheafSmall (smallEtaleRingedSite B S hS F hF) M N).over
      W).IsQuasicoherentOnSite := by
  classical
  let := smallEtaleRingedSite_essentiallySmall B S hS F hF
  let X := smallEtaleRingedSite B S hS F hF
  let Rs := (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
  let H := RingedSite.internalHomSheafSmall X M N
  obtain ⟨n, k, P, Q, ι, κ, ⟨hP⟩, ⟨hQ⟩, a, b, hab, ⟨hb⟩⟩ := hW
  have : HasFiniteLimits (SheafOfModules.{u} (Rs.over W)) :=
    SheafOfModules.Finite.hasFiniteLimits _
  have : HasFiniteLimits (SheafOfModules.{u + 1} (Rs.over W)) :=
    SheafOfModules.Finite.hasFiniteLimits _
  let L := Stacks.SheafOfModules.moduleULift.{u + 1, u} (Rs.over W)
  have hL : L.FullyFaithful := Stacks.SheafOfModules.moduleULiftFullyFaithful _
  have : PreservesFiniteLimits L := Stacks.SheafOfModules.preservesFiniteLimits_moduleULift
  let IH : SheafOfModules.{u + 1} (Rs.over W) :=
    (X.over W).internalHomSheaf
      (SheafOfModules.uliftForPresentation.{u + 1, u, u, u, u + 1} (M.over W)) (L.obj (N.over W))
  obtain ⟨f', ⟨e'⟩⟩ : ∃ f' : (∏ᶜ fun _ : Fin n => L.obj (N.over W)) ⟶
      ∏ᶜ fun _ : Fin k => L.obj (N.over W), Nonempty (IH ≅ kernel f') :=
    RingedSite.exists_internalHomSheaf_iso_kernel (X.over W) ι hP κ hQ a b hab hb
      (L.obj (N.over W))
  let eH : L.obj (H.over W) ≅ kernel f' :=
    (SheafOfModules.overFunctor Rs W).mapIso (RingedSite.internalHomSheafSmallIso X M N) ≪≫
      RingedSite.internalHomSheafOverIso X W M N ≪≫
      (RingedSite.internalHomSheafULiftIso (X.over W) (M.over W) (N.over W)).symm ≪≫ e'
  let eP (m : ℕ) : L.obj (∏ᶜ fun _ : Fin m => N.over W) ≅ ∏ᶜ fun _ : Fin m => L.obj (N.over W) :=
    PreservesProduct.iso L _
  let f : (∏ᶜ fun _ : Fin n => N.over W) ⟶ ∏ᶜ fun _ : Fin k => N.over W :=
    hL.preimage ((eP n).hom ≫ f' ≫ (eP k).inv)
  let eK : L.obj (kernel f) ≅ kernel f' :=
    PreservesKernel.iso L f ≪≫ kernel.mapIso _ _ (eP n) (eP k) (by simp [f])
  let eHW : H.over W ≅ kernel f := hL.preimageIso (eH ≪≫ eK.symm)
  have hNW : (N.over W).IsQuasicoherentOnSite := Stacks.SheafOfModules.isQuasicoherent_over N hN W
  have hprod : ∀ m : ℕ, (∏ᶜ fun _ : Fin m => N.over W).IsQuasicoherentOnSite := fun m =>
    (SheafOfModules.isQuasicoherentOnSite _).prop_limit _ (fun _ => hNW)
  exact SheafOfModules.IsQuasicoherentOnSite.of_iso eHW.symm
    (isQuasicoherentOnSite_of_isLimit_kernelFork_over_chart B S hS ⟨F, hF⟩ W _
      (limit.isLimit _) (hprod n) (hprod k))

/-- **Stacks 03M1 (6).**  Let `𝓕`, `𝓖` be quasi-coherent `𝒪_X`-modules on an algebraic space `X`
with `𝓕` of finite presentation (Stacks 03DL(7)).  Then the internal Hom
`𝓗om_{𝒪_X}(𝓕, 𝓖)` is quasi-coherent.

The internal Hom is the one of Stacks 03EM in `Mod(𝒪_X)`,
`AlgebraicGeometry.RingedSite.internalHomSheafSmall`; see the module documentation.  The
quasi-coherence of `𝓕` is part of the source's statement; the argument does not use it, a module
of finite presentation being quasi-coherent.  Quasi-coherence is local on the members of a
covering family (Stacks 03DN), the charts over which `𝓕` has a finite presentation cover `X`, and
over each of them
`AlgebraicGeometry.Space.isQuasicoherentOnSite_over_internalHomSheafSmall` applies. -/
@[stacks 03M1 "(6) the internal Hom 𝓗om(𝓕, 𝓖) of two quasi-coherent 𝒪_X-modules with 𝓕 of \
finite presentation is quasi-coherent", sga "3 III 0.6" "more general"]
theorem isQuasicoherentOnSite_internalHomSheafSmall (M N : Modules.{u, u} B S hS F hF)
    (_hM : M.IsQuasicoherentOnSite) (hN : N.IsQuasicoherentOnSite)
    (hfp : M.IsFinitePresentationOnSite) :
    letI := smallEtaleRingedSite_essentiallySmall B S hS F hF
    (RingedSite.internalHomSheafSmall (smallEtaleRingedSite B S hS F hF) M
      N).IsQuasicoherentOnSite := by
  let := smallEtaleRingedSite_essentiallySmall B S hS F hF
  refine (Stacks.SheafOfModules.isQuasicoherentOnSite_iff_exists_cover_isQuasicoherentOnSite
    _).2 ⟨{W : (smallEtaleRingedSite B S hS F hF).C //
        SheafOfModules.HasFiniteGlobalPresentation (M.over W)}, fun W => W.1, fun U => ?_, fun W =>
        isQuasicoherentOnSite_over_internalHomSheafSmall B S hS F hF M N hN W.1 W.2⟩
  obtain ⟨I, V, f, hV, hpres⟩ := hfp.locally_hasFiniteGlobalPresentation U
  refine GrothendieckTopology.superset_covering _
    ((Sieve.ofArrows_le_ofObjects V f).trans (Sieve.ofObjects_mono ?_)) hV
  rintro x ⟨i, rfl⟩
  exact ⟨⟨V i, hpres i⟩, rfl⟩

end AlgebraicGeometry.Space

end
