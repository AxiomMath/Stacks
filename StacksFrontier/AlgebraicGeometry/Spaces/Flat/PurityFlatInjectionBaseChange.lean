module

public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.FlatLocalAtSource
public import StacksFrontier.AlgebraicGeometry.Divisors.MorphismWeaklyAssociated.ChartDiagramRelativeAssassin
public import StacksFrontier.AlgebraicGeometry.Divisors.MorphismWeaklyAssociated.SpaceBaseChange
public import StacksFrontier.AlgebraicGeometry.Divisors.MorphismWeaklyAssociated.SpaceTensorPullbackLocallyNoetherian
public import StacksFrontier.AlgebraicGeometry.Flatness.WeaklyAssociatedTensorPullbackFibre
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartRestrictionFromSite
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartRestrictionSections
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.Flat.BourbakiFiniteTypeGeneralBase
public import StacksFrontier.AlgebraicGeometry.Spaces.Flat.PurityFlatInjection
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatModuleBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackQuasicoherentFromChartDiagrams
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.PushforwardPresentationExact
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentPushforwardExactSequence
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentPushforwardQcqs
public import StacksFrontier.AlgebraicGeometry.Spaces.WeaklyAssociatedInjective
public import StacksFrontier.AlgebraicGeometry.Spaces.WeaklyAssociatedVanishingQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Topologies.FiniteTypeFromGlobalGenerators
public import StacksFrontier.AlgebraicGeometry.Topologies.FiniteTypeOnSiteKernel
public import StacksCore.Tactic.StacksAttribute

/-!
# The injection of a flat morphism meeting the relative assassin survives base change

Let `Y` be an algebraic space over a scheme `S`, let `g : X' ⟶ X` be a flat morphism of
algebraic spaces over `Y` with `X` locally of finite type over `Y`, and let `ℱ` be a finite type
quasi-coherent `𝒪_X`-module which is flat over `Y`. If the relative assassin `Ass_{X/Y}(ℱ)` is
contained in the image of `|X'|`, then `ℱ ⟶ g_*g^*ℱ` is injective and remains injective after any
base change (Stacks 0CW6). This file gives forms of the base-change half in which a morphism
`h : Z ⟶ Y` gives `X_Z = X ×_Y Z` with projections `p_Z : X_Z ⟶ X` and `q_Z : X_Z ⟶ Z`, and
`X'_Z = X_Z ×_X X'` with `g_Z : X'_Z ⟶ X_Z`, both presented by cartesian squares.

## Main results

* `AlgebraicGeometry.Space.modulePullback_map_eq_zero_iff_of_mono_unit`: a map of modules
  vanishes exactly when its inverse image along `g` does, as soon as `𝒩 ⟶ g_*g^*𝒩` is a
  monomorphism.
* `AlgebraicGeometry.Space.isFiniteType_modulePullback`: the inverse image of a module of finite
  type is of finite type.
* `AlgebraicGeometry.Space.isQuasicoherentOnSite_kernel_unit_of_qcqs`: along a quasi-compact,
  quasi-separated `φ` the kernel of `𝒩 ⟶ φ_*φ^*𝒩` is quasi-coherent for quasi-coherent `𝒩`.
* `AlgebraicGeometry.Space.weaklyAssociatedVanishingInput`: a quasi-coherent module with no
  weakly associated point vanishes.
* `weaklyAssociatedPoints_subset_relativeWeaklyAssociatedPoints_of_isFiniteTypeOnSite`: for a
  morphism `f : X ⟶ Y` locally of finite type and a quasi-coherent module `𝓕` of finite type flat
  over `Y`, every weakly associated point of `𝓕` is a relative weakly associated point.
* `mono_unit_baseChange_of_relativeWeaklyAssociatedPoints_subset_range_of_kernel`,
  `mono_unit_baseChange_of_relativeWeaklyAssociatedPoints_subset_range'` and
  `mono_unit_baseChange_of_relativeWeaklyAssociatedPoints_subset_range_of_qcqs`: if
  `Ass_{X/Y}(ℱ) ⊆ g(|X'|)`, then `p_Z^*ℱ ⟶ g_{Z*}g_Z^*p_Z^*ℱ` is a monomorphism.

## References

* [Stacks Project, Tag 0CW6](https://stacks.math.columbia.edu/tag/0CW6)
* [Stacks Project, Tag 0CW2](https://stacks.math.columbia.edu/tag/0CW2)
* [Stacks Project, Tag 0CU0](https://stacks.math.columbia.edu/tag/0CU0)
* [Stacks Project, Tag 0CVL](https://stacks.math.columbia.edu/tag/0CVL)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 03MO](https://stacks.math.columbia.edu/tag/03MO)
* [Stacks Project, Tag 03XH](https://stacks.math.columbia.edu/tag/03XH)
* [Stacks Project, Tag 03GA](https://stacks.math.columbia.edu/tag/03GA)
* [Stacks Project, Tag 03DO](https://stacks.math.columbia.edu/tag/03DO)
* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
* [Stacks Project, Tag 05VW](https://stacks.math.columbia.edu/tag/05VW)
* [Stacks Project, Tag 03M1](https://stacks.math.columbia.edu/tag/03M1)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance 10000] smallEtaleModulesAbelian

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Maps killed by the inverse image -/

/-- **A map of modules vanishes exactly when its inverse image along `g` does, as soon as the
canonical map `𝒩 ⟶ g_*g^*𝒩` is a monomorphism.** -/
theorem modulePullback_map_eq_zero_iff_of_mono_unit {X' X : AlgebraicSpaces B S hS} (g : X' ⟶ X)
    {M N : Modules.{u, u} B S hS X.1 X.2}
    (hmono : Mono ((modulePullbackAdjunction B S hS g).unit.app N)) (v : M ⟶ N) :
    (modulePullback B S hS g).map v = 0 ↔ v = 0 := by
  have := (modulePullbackAdjunction B S hS g).isLeftAdjoint
  have : (modulePullback B S hS g).PreservesZeroMorphisms := inferInstance
  refine ⟨fun h => ?_, fun h => by rw [h, Functor.map_zero]⟩
  have hnat := (modulePullbackAdjunction B S hS g).unit_naturality v
  rw [h, Functor.map_zero, comp_zero] at hnat
  exact (Preadditive.mono_iff_cancel_zero _).1 hmono _ v hnat.symm

/-! ### Finite type under inverse image -/

/-- The inverse image of a module of finite type, in the sense of `SheafOfModules.IsFiniteType`,
is of finite type. -/
theorem isFiniteType_modulePullback {X' X : AlgebraicSpaces B S hS} (g : X' ⟶ X)
    (F : Modules.{u, u} B S hS X.1 X.2) (hF : SheafOfModules.IsFiniteType F) :
    SheafOfModules.IsFiniteType ((modulePullback B S hS g).obj F) :=
  Stacks.SheafOfModules.isFiniteType_of_isFiniteTypeOnSite _
    (isFiniteTypeOnSite_modulePullback B S hS g F
      (Stacks.SheafOfModules.isFiniteTypeOnSite_of_isFiniteType _ hF))

/-! ### Hypotheses of the base-change half -/

/-- The assertion that along every flat morphism `φ : W' ⟶ W` every quasi-coherent
`𝒪_W`-module `𝒩` has a quasi-coherent kernel of the unit `𝒩 ⟶ φ_*φ^*𝒩` of Stacks 03LU.

This assertion is false. Take any nonzero ring `R`, put `A = R[x, y₁, y₂, …]`, let `J` be the
monomial ideal `(xⁱyᵢⁱ : i ≥ 1)` and `M = A/J`, let `W = Spec A` and let `φ : U ⟶ W` be the open
immersion of `U = ⋃_{i ≥ 1} D(yᵢ)`. It is étale, hence flat, and it is not quasi-compact: the
prime `(y₁, …, yₙ)` lies in `U` but in no `D(yᵢ)` with `i ≤ n`. Let `𝒩` be the quasi-coherent
module of `M`. The kernel of the unit is the subsheaf of sections dying on `U`, so
`K(W) = {t ∈ M : ∀ i, yᵢᵖ t = 0 for some p}` and
`K(D(x)) = {s ∈ M_x : ∀ i, yᵢᵖ s = 0 in M_x for some p}`, and the class of `1` lies in `K(D(x))`,
since `xⁱyᵢⁱ ∈ J` kills it after inverting `x`, while being nonzero there, since no power of `x`
lies in `J`. It does not lie in `K(W)_x`: from `xᴺ t = x^{N+n}` in `M` with `yᵢᵖ t = 0` one gets
`x^{N+n} yᵢᵖ ∈ J`, and a monomial lies in a monomial ideal only if one of the generators divides
it, which forces `i ≤ N + n` — false at `i = N + n + 1`. So `K(W) ⊗_A A_x ⟶ K(D(x))` is not
surjective, `K` is not cartesian on the affine étale charts `Spec A_x ⟶ Spec A`, and by
Stacks 03DX(2), `AlgebraicGeometry.Space.isQuasicoherentOnSite_iff_isCartesianOnAffineCharts`,
`K` is not quasi-coherent. -/
abbrev UnitKernelQuasicoherentInput : Prop :=
  ∀ (W' W : AlgebraicSpaces B S hS) (φ : W' ⟶ W), IsFlat B S hS φ.hom →
    ∀ N : Modules.{u, u} B S hS W.1 W.2, N.IsQuasicoherentOnSite →
      ∃ (K : Modules.{u, u} B S hS W.1 W.2) (ι : K ⟶ N)
        (hι : ι ≫ (modulePullbackAdjunction B S hS φ).unit.app N = 0),
        K.IsQuasicoherentOnSite ∧ Nonempty (IsLimit (KernelFork.ofι ι hι))

/-! ### The kernel of the unit along a quasi-compact quasi-separated morphism -/

/-- **The kernel of the unit `𝒩 ⟶ φ_*φ^*𝒩` of Stacks 03LU is quasi-coherent as soon as `φ` is
quasi-compact and quasi-separated and `𝒩` is quasi-coherent.** -/
theorem isQuasicoherentOnSite_kernel_unit_of_qcqs {W' W : AlgebraicSpaces B S hS} (φ : W' ⟶ W)
    (hqc : IsQuasiCompact B S hS φ.hom) (hqs : IsQuasiSeparated B S hS φ.hom)
    (N : Modules.{u, u} B S hS W.1 W.2) [N.IsQuasicoherentOnSite] :
    (kernel ((modulePullbackAdjunction B S hS φ).unit.app N)).IsQuasicoherentOnSite := by
  have : ((modulePullback B S hS φ).obj N).IsQuasicoherentOnSite :=
    isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS φ N inferInstance
  have : ((modulePullback B S hS φ ⋙ modulePushforward B S hS φ).obj
      N).IsQuasicoherentOnSite :=
    isQuasicoherentOnSite_modulePushforward_of_qcqs B S hS φ hqc hqs _ inferInstance
  exact isQuasicoherentOnSite_kernel_of_quasicoherent B S hS W.1 W.2 (M := N) _

/-- `AlgebraicGeometry.Space.UnitKernelQuasicoherentInput` restricted to quasi-compact and
quasi-separated morphisms: along every flat, quasi-compact and quasi-separated morphism
`φ : W' ⟶ W` every quasi-coherent `𝒪_W`-module `𝒩` has a quasi-coherent kernel of the unit
`𝒩 ⟶ φ_*φ^*𝒩`. -/
abbrev UnitKernelQuasicoherentQcqsInput : Prop :=
  ∀ (W' W : AlgebraicSpaces B S hS) (φ : W' ⟶ W), IsFlat B S hS φ.hom →
    IsQuasiCompact B S hS φ.hom → IsQuasiSeparated B S hS φ.hom →
    ∀ N : Modules.{u, u} B S hS W.1 W.2, N.IsQuasicoherentOnSite →
      ∃ (K : Modules.{u, u} B S hS W.1 W.2) (ι : K ⟶ N)
        (hι : ι ≫ (modulePullbackAdjunction B S hS φ).unit.app N = 0),
        K.IsQuasicoherentOnSite ∧ Nonempty (IsLimit (KernelFork.ofι ι hι))

/-- **`AlgebraicGeometry.Space.UnitKernelQuasicoherentQcqsInput` holds.** -/
theorem unitKernelQuasicoherentQcqsInput : UnitKernelQuasicoherentQcqsInput B S hS :=
  fun _W' _ φ _hflat hqc hqs N _ =>
    ⟨kernel ((modulePullbackAdjunction B S hS φ).unit.app N), kernel.ι _, kernel.condition _,
      isQuasicoherentOnSite_kernel_unit_of_qcqs B S hS φ hqc hqs N, ⟨kernelIsKernel _⟩⟩

/-- The assertion that a quasi-coherent module on an algebraic space with no weakly associated
point vanishes, the substantive direction of Stacks 0CU0. -/
abbrev WeaklyAssociatedVanishingInput : Prop :=
  ∀ (W : AlgebraicSpaces B S hS) (K : Modules.{u, u} B S hS W.1 W.2),
    K.IsQuasicoherentOnSite → weaklyAssociatedPoints B S hS W K = ∅ → IsZero K

/-- **`AlgebraicGeometry.Space.WeaklyAssociatedVanishingInput` holds.** -/
theorem weaklyAssociatedVanishingInput : WeaklyAssociatedVanishingInput B S hS :=
  fun W K _ h => isZero_of_weaklyAssociatedPoints_eq_empty B S hS W K h

/-- The assertion that for a morphism `φ : W ⟶ V` locally of finite type and a finite type
quasi-coherent module on `W` flat over `V`, every weakly associated point of the module is a
relative weakly associated point: Stacks 0CVL at `𝒢 = 𝒪_V`. -/
abbrev WeaklyAssociatedSubsetRelativeInput : Prop :=
  ∀ (W V : AlgebraicSpaces B S hS) (φ : W ⟶ V) (M : Modules.{u, u} B S hS W.1 W.2),
    M.IsQuasicoherentOnSite → SheafOfModules.IsFiniteType M →
    IsLocallyOfFiniteType B S hS φ.hom → IsFlatOver B S hS W.2 φ.hom M →
    weaklyAssociatedPoints B S hS W M ⊆ relativeWeaklyAssociatedPoints B S hS φ M

/-- **Every weakly associated point is a relative weakly associated point.** Let `f : X ⟶ Y` be a
morphism of algebraic spaces locally of finite type and let `𝓕` be a quasi-coherent
`𝒪_X`-module of finite type on the small étale site which is flat over `Y`. Then every weakly
associated point of `𝓕` lies in the relative weak assassin `WeakAss_{X/Y}(𝓕)` of Stacks 0CV0 —
which, the fibres of `f` being locally Noetherian by Stacks 0CUY, is the set the source writes
`Ass_{X/Y}(𝓕)`. -/
theorem weaklyAssociatedPoints_subset_relativeWeaklyAssociatedPoints_of_isFiniteTypeOnSite
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) (hf : IsLocallyOfFiniteType B S hS f.hom)
    (F : Modules.{u, u} B S hS X.1 X.2) [F.IsQuasicoherentOnSite]
    (hft : SheafOfModules.IsFiniteTypeOnSite F)
    (hF : IsFlatOver B S hS X.2 f.hom F) :
    weaklyAssociatedPoints B S hS X F ⊆ relativeWeaklyAssociatedPoints B S hS f F := by
  intro x hx
  obtain ⟨d, w, rfl⟩ := exists_chartDiagram_chartSchemeToPoints_eq B S hS f x
  have hflat := isFlatOverAt_chartDiagram_of_mem_flatLocus B S hS f F d w
    ⟨d, w, (chartSchemeToPoints_eq_pointsMap_pointsEquivScheme_symm B S hS X.1 d.U w).symm,
      hF d w⟩
  have hw : Stacks.Divisors.IsWeaklyAssociatedPoint
      (chartDiagramRestrictSource B S hS f F d) w :=
    (isWeaklyAssociatedPoint_restrictToChart_iff_isWeaklyAssociatedPoint B S hS X F d.U w).2 hx
  have : LocallyOfFiniteType (chartDiagramSchemeMap B S hS f d) :=
    locallyOfFiniteType_chartDiagramSchemeMap B S hS f hf d
  have : (chartDiagramRestrictSource B S hS f F d).IsQuasicoherent :=
    isQuasicoherent_restrictToChart B S hS X F inferInstance d.U
  have : (chartDiagramRestrictSource B S hS f F d).IsFiniteType :=
    isFiniteType_restrictToChart B S hS X F inferInstance hft d.U
  exact isRelativeWeaklyAssociatedPoint_of_mem_relativeAssassin_chartDiagram B S hS f F
    inferInstance d w
    (Stacks.Divisors.mem_relativeAssassin_of_isWeaklyAssociatedPoint_of_finiteType
      (chartDiagramSchemeMap B S hS f d) (chartDiagramRestrictSource B S hS f F d) w hflat hw)

/-- **`AlgebraicGeometry.Space.WeaklyAssociatedSubsetRelativeInput` holds.** -/
theorem weaklyAssociatedSubsetRelativeInput : WeaklyAssociatedSubsetRelativeInput B S hS :=
  fun _ _ φ M _ hft hφ hM =>
    weaklyAssociatedPoints_subset_relativeWeaklyAssociatedPoints_of_isFiniteTypeOnSite B S hS φ hφ
      M (Stacks.SheafOfModules.isFiniteTypeOnSite_of_isFiniteType M hft) hM

/-! ### Stacks 0CW6, the base-change half -/

/-- **The base-change half of Stacks 0CW6, with a kernel of the base-changed unit as data.** Let
`X_Z` be the base change of `X` along `h` by the cartesian square `sq`, and `X'_Z = X_Z ×_X X'`
by the cartesian square `sq'`. If `Ass_{X/Y}(ℱ)` is contained in the image of `|X'|`, then
`p_Z^*ℱ ⟶ g_{Z*}g_Z^*p_Z^*ℱ` is a monomorphism. -/
theorem mono_unit_baseChange_of_relativeWeaklyAssociatedPoints_subset_range_of_kernel
    {X' X Y Z XZ X'Z : AlgebraicSpaces B S hS} {f : X ⟶ Y} {g : X' ⟶ X} {h : Z ⟶ Y}
    {pZ : XZ ⟶ X} {qZ : XZ ⟶ Z} {gZ : X'Z ⟶ XZ} {rZ : X'Z ⟶ X'}
    (sq : IsPullback pZ qZ f h) (sq' : IsPullback gZ rZ pZ g)
    (hf : IsLocallyOfFiniteType B S hS f.hom) (hg : IsFlat B S hS g.hom)
    (F : Modules.{u, u} B S hS X.1 X.2) [F.IsQuasicoherentOnSite] [F.IsFiniteType]
    (hF : IsFlatOver B S hS X.2 f.hom F)
    {KZ : Modules.{u, u} B S hS XZ.1 XZ.2} [KZ.IsQuasicoherentOnSite]
    (ιZ : KZ ⟶ (modulePullback B S hS pZ).obj F)
    (hιZ : ιZ ≫ (modulePullbackAdjunction B S hS gZ).unit.app
      ((modulePullback B S hS pZ).obj F) = 0)
    (_hKZ : IsLimit (KernelFork.ofι ιZ hιZ))
    (_h0CU0 : weaklyAssociatedPoints B S hS XZ KZ = ∅ → IsZero KZ)
    (_h0CVL : IsLocallyOfFiniteType B S hS qZ.hom →
      IsFlatOver B S hS XZ.2 qZ.hom ((modulePullback B S hS pZ).obj F) →
      weaklyAssociatedPoints B S hS XZ ((modulePullback B S hS pZ).obj F) ⊆
        relativeWeaklyAssociatedPoints B S hS qZ ((modulePullback B S hS pZ).obj F))
    (hass : relativeWeaklyAssociatedPoints B S hS f F ⊆
      Set.range (pointsMap B S hS X'.1 g.hom)) :
    Mono ((modulePullbackAdjunction B S hS gZ).unit.app ((modulePullback B S hS pZ).obj F)) := by
  exact mono_unit_baseChange_of_relativeWeaklyAssociatedPoints_subset_range B S hS f g h pZ qZ
    rZ gZ sq sq'.flip hf hg F hF hass

/-- The relative weakly associated points input of `h0CVL` for the inverse image `p_Z^*ℱ`. -/
private theorem weaklyAssociatedSubsetRelative_modulePullback
    (h0CVL : WeaklyAssociatedSubsetRelativeInput B S hS)
    {X Z XZ : AlgebraicSpaces B S hS} (pZ : XZ ⟶ X) (qZ : XZ ⟶ Z)
    (F : Modules.{u, u} B S hS X.1 X.2) [F.IsQuasicoherentOnSite] [F.IsFiniteType]
    (hq : IsLocallyOfFiniteType B S hS qZ.hom)
    (hfl : IsFlatOver B S hS XZ.2 qZ.hom ((modulePullback B S hS pZ).obj F)) :
    weaklyAssociatedPoints B S hS XZ ((modulePullback B S hS pZ).obj F) ⊆
      relativeWeaklyAssociatedPoints B S hS qZ ((modulePullback B S hS pZ).obj F) :=
  h0CVL XZ Z qZ _
    (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS pZ F inferInstance)
    (isFiniteType_modulePullback B S hS pZ F inferInstance) hq hfl

/-- **The base-change half of Stacks 0CW6, with its hypotheses in quantified form**: given
`AlgebraicGeometry.Space.UnitKernelQuasicoherentInput`,
`AlgebraicGeometry.Space.WeaklyAssociatedVanishingInput` and
`AlgebraicGeometry.Space.WeaklyAssociatedSubsetRelativeInput`, if `Ass_{X/Y}(ℱ)` is contained in
the image of `|X'|`, then `p_Z^*ℱ ⟶ g_{Z*}g_Z^*p_Z^*ℱ` is a monomorphism. The first of the three
hypotheses is false, so this statement is vacuous. -/
theorem mono_unit_baseChange_of_relativeWeaklyAssociatedPoints_subset_range'
    (h03M1 : UnitKernelQuasicoherentInput B S hS)
    (h0CU0 : WeaklyAssociatedVanishingInput B S hS)
    (h0CVL : WeaklyAssociatedSubsetRelativeInput B S hS)
    {X' X Y Z XZ X'Z : AlgebraicSpaces B S hS} {f : X ⟶ Y} {g : X' ⟶ X} {h : Z ⟶ Y}
    {pZ : XZ ⟶ X} {qZ : XZ ⟶ Z} {gZ : X'Z ⟶ XZ} {rZ : X'Z ⟶ X'}
    (sq : IsPullback pZ qZ f h) (sq' : IsPullback gZ rZ pZ g)
    (hf : IsLocallyOfFiniteType B S hS f.hom) (hg : IsFlat B S hS g.hom)
    (F : Modules.{u, u} B S hS X.1 X.2) [F.IsQuasicoherentOnSite] [F.IsFiniteType]
    (hF : IsFlatOver B S hS X.2 f.hom F)
    (hass : relativeWeaklyAssociatedPoints B S hS f F ⊆
      Set.range (pointsMap B S hS X'.1 g.hom)) :
    Mono ((modulePullbackAdjunction B S hS gZ).unit.app ((modulePullback B S hS pZ).obj F)) := by
  obtain ⟨KZ, ιZ, hιZ, hqcK, ⟨hKZ⟩⟩ := h03M1 X'Z XZ gZ
    ((isFlat_isStableUnderBaseChange B S hS).of_isPullback sq'.flip hg)
    ((modulePullback B S hS pZ).obj F)
    (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS pZ F inferInstance)
  exact mono_unit_baseChange_of_relativeWeaklyAssociatedPoints_subset_range_of_kernel B S hS sq
    sq' hf hg F hF ιZ hιZ hKZ (h0CU0 XZ KZ hqcK)
    (weaklyAssociatedSubsetRelative_modulePullback B S hS h0CVL pZ qZ F) hass

/-- **The base-change half of Stacks 0CW6 for a quasi-compact and quasi-separated `g`**, given
`AlgebraicGeometry.Space.WeaklyAssociatedSubsetRelativeInput`: if `Ass_{X/Y}(ℱ)` is contained in
the image of `|X'|`, then `p_Z^*ℱ ⟶ g_{Z*}g_Z^*p_Z^*ℱ` is a monomorphism. -/
theorem mono_unit_baseChange_of_relativeWeaklyAssociatedPoints_subset_range_of_qcqs
    (h0CVL : WeaklyAssociatedSubsetRelativeInput B S hS)
    {X' X Y Z XZ X'Z : AlgebraicSpaces B S hS} {f : X ⟶ Y} {g : X' ⟶ X} {h : Z ⟶ Y}
    {pZ : XZ ⟶ X} {qZ : XZ ⟶ Z} {gZ : X'Z ⟶ XZ} {rZ : X'Z ⟶ X'}
    (sq : IsPullback pZ qZ f h) (sq' : IsPullback gZ rZ pZ g)
    (hf : IsLocallyOfFiniteType B S hS f.hom) (hg : IsFlat B S hS g.hom)
    (hgqc : IsQuasiCompact B S hS g.hom) (hgqs : IsQuasiSeparated B S hS g.hom)
    (F : Modules.{u, u} B S hS X.1 X.2) [F.IsQuasicoherentOnSite] [F.IsFiniteType]
    (hF : IsFlatOver B S hS X.2 f.hom F)
    (hass : relativeWeaklyAssociatedPoints B S hS f F ⊆
      Set.range (pointsMap B S hS X'.1 g.hom)) :
    Mono ((modulePullbackAdjunction B S hS gZ).unit.app ((modulePullback B S hS pZ).obj F)) := by
  obtain ⟨KZ, ιZ, hιZ, hqcK, ⟨hKZ⟩⟩ := unitKernelQuasicoherentQcqsInput B S hS X'Z XZ gZ
    ((isFlat_isStableUnderBaseChange B S hS).of_isPullback sq'.flip hg)
    ((isQuasiCompact_isStableUnderBaseChange B S hS).of_isPullback sq'.flip hgqc)
    ((isQuasiSeparated_isStableUnderBaseChange B S hS).of_isPullback sq'.flip hgqs)
    ((modulePullback B S hS pZ).obj F)
    (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS pZ F inferInstance)
  exact mono_unit_baseChange_of_relativeWeaklyAssociatedPoints_subset_range_of_kernel B S hS sq
    sq' hf hg F hF ιZ hιZ hKZ (weaklyAssociatedVanishingInput B S hS XZ KZ hqcK)
    (weaklyAssociatedSubsetRelative_modulePullback B S hS h0CVL pZ qZ F) hass

end AlgebraicGeometry.Space

end
