module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.Topology.KrullDimension
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.Coherent
public import StacksFrontier.AlgebraicGeometry.AffineBaseChange.Basic
public import StacksFrontier.AlgebraicGeometry.CoherentPullback.Basic
public import StacksFrontier.AlgebraicGeometry.DerivedAffineMorphism.SupportedPushforwardReflect
public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.FourierMukai.Basic
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.Support
public import StacksFrontier.AlgebraicGeometry.Morphisms.JacobsonPoints.Tfae
public import StacksFrontier.AlgebraicGeometry.Morphisms.Support.TestModuleStalk
public import StacksFrontier.AlgebraicGeometry.Perfect.DerivedStalk.StalkSpellingBridge
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.StalkAdicHomologyBridge
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.ProjectionFormulaStrictlyPerfect
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.TriangulatedSubcategory
public import StacksFrontier.AlgebraicGeometry.Modules.StalkSupport
public import StacksFrontier.AlgebraicGeometry.Morphisms.Support.Defs
public import StacksFrontier.AlgebraicGeometry.Morphisms.Support.ZeroDimensionalTestModules
public import StacksFrontier.AlgebraicGeometry.OneDimensionalLocal.Basic
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.TorAmplitudeStalkwise
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Dimension.Trdeg
public import StacksFrontier.Topology.Dimension.DimensionLEOne
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.BasicProperties

/-!
# Fibrewise cohomological bands for a system of perfect kernels

Let `S` be a scheme, let `X` and `Y` be schemes over `S` and let `K₀ ⟶ K₁ ⟶ K₂ ⟶ ⋯` be a
system of perfect objects of `D(𝒪_{X ×_S Y})` whose cohomology vanishes above a degree `m ≥ 0`.
Each `Kₙ` is the kernel of a Fourier-Mukai functor

`Φ_{Kₙ} : D(𝒪_X) ⟶ D(𝒪_Y)`,  `M ⟼ R pr_{2,*}(L pr_1^* M ⊗^𝐋_{𝒪_{X ×_S Y}} Kₙ)`,

and the hypothesis of [Stacks, Tag 0FZ9] is a pair of conditions on the values of `Φ_{Kₙ}` on
the coherent `𝒪_X`-modules with zero-dimensional support: the cohomology of `Φ_{Kₙ}(𝓕)` is
concentrated in the union of the two bands `[-m, m]` and `[-m-n, m-n]`, and once `n > 2m` the
transition maps are isomorphisms on cohomology throughout `[-m, m]`. The assertion of the tag is
that the same two statements then hold for the kernels `Kₙ` themselves.

The tag's hypotheses are bundled here as `AlgebraicGeometry.BoundedFibreTransforms`, and the
file carries the globalisation step that its three assertions share: a cohomology sheaf of `Kₙ`
vanishes as soon as its stalks at the closed points of `X ×_S Y` vanish, because `X ×_S Y` is a
Jacobson space when `X` and `Y` are of finite type over a field.

## Main definitions

* `AlgebraicGeometry.InBands`: membership of a degree in the union of the band `[-m, m]` and the
  band `[-m-n, m-n]` receding with `n`.
* `AlgebraicGeometry.fourierMukaiKernelMap`: the natural transformation
  `Φ_K ⟶ Φ_{K'}` induced by a morphism `K ⟶ K'` of kernels, so that a system of kernels gives a
  system of Fourier-Mukai functors.
* `AlgebraicGeometry.BoundedFibreTransforms`: the hypotheses of [Stacks, Tag 0FZ9] on a system
  of perfect kernels — perfectness, the bound above on the cohomology of the kernels, and the
  two conditions on the integral transforms of the coherent modules with zero-dimensional
  support.

## Main results

* `AlgebraicGeometry.finite_and_subset_closedPoints_of_topologicalKrullDim_le_zero`: in a
  Noetherian sober `T0` space, a closed subset of Krull dimension at most zero is a finite set of
  closed points.
* `AlgebraicGeometry.topologicalKrullDim_singleton`: a one-point subspace has Krull dimension
  zero.
* `AlgebraicGeometry.isZero_of_forall_isZero_stalk_closedPoints`: on a Jacobson scheme a module
  of finite type whose stalks at the closed points vanish is zero.
* `AlgebraicGeometry.jacobsonSpace_pullback`: the fibre product of two schemes locally of finite
  type over a Jacobson base is a Jacobson space.

## Implementation notes

*The model of the derived categories.* Everything is read at
`CategoryTheory.HasDerivedCategory.standard`, the model at which
`AlgebraicGeometry.fourierMukai` is defined; the local instance selects it over the locally small
model arriving with the imports.

*The shape of the two fibre conditions.* The source applies `Φ_{Kₙ}` to a coherent module `𝓕`,
i.e. to the object `𝓕[0]` of `D(𝒪_X)`, so the conditions are stated at
`(DerivedCategory.singleFunctor X.Modules 0).obj 𝓕`. The condition `dim(Supp 𝓕) = 0` is read as
the vanishing of the topological Krull dimension of the support of `𝓕` as a subspace of `X`;
`finite_and_subset_closedPoints_of_topologicalKrullDim_le_zero` identifies such a support, on a
Noetherian scheme, with a finite set of closed points, which is the form in which the source
uses it.

*Why the transition maps are packaged through `fourierMukaiKernelMap`.* The transformation
`Φ_K ⟶ Φ_{K'}` attached to `K ⟶ K'` is the derived tensor product of [Stacks, Tag 06YU] in its
second variable, whiskered by the derived pullback along `pr₁` and the derived direct image along
`pr₂`; naming it keeps the stability condition of the bundle a statement about a single morphism
of `D(𝒪_Y)` rather than about a composite of three functors.

## References

* [Stacks Project, Tag 0FZ9](https://stacks.math.columbia.edu/tag/0FZ9)
* [Stacks Project, Tag 0FYQ](https://stacks.math.columbia.edu/tag/0FYQ)
* [Stacks Project, Tag 08CM](https://stacks.math.columbia.edu/tag/08CM)
* [Stacks Project, Tag 02J6](https://stacks.math.columbia.edu/tag/02J6)
* [Stacks Project, Tag 056J](https://stacks.math.columbia.edu/tag/056J)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Stacks Set TopologicalSpace

namespace AlgebraicGeometry

universe u

attribute [local instance 10000] HasDerivedCategory.standard

/-! ### Zero-dimensional closed subsets -/

/-- **A closed subset of Krull dimension at most zero is a finite set of closed points**, in a
Noetherian sober `T0` space. The subspace is again Noetherian, sober and `T0`, so it is finite
and all of its points are closed in it; being closed, its points are then closed in the ambient
space. -/
theorem finite_and_subset_closedPoints_of_topologicalKrullDim_le_zero
    {X : Type u} [TopologicalSpace X] [T0Space X] [NoetherianSpace X] [QuasiSober X]
    {Z : Set X} (hZ : IsClosed Z) (hdim : topologicalKrullDim Z ≤ 0) :
    Z.Finite ∧ Z ⊆ closedPoints X := by
  have hemb := hZ.isClosedEmbedding_subtypeVal
  have : QuasiSober Z := hemb.quasiSober
  refine ⟨Set.finite_coe_iff.1 (Set.finite_univ_iff.1
    (Stacks.Topology.Dimension.finite_of_topologicalKrullDim_le_zero hdim)), fun z hz => ?_⟩
  have h1 : IsClosed ({(⟨z, hz⟩ : Z)} : Set Z) :=
    Stacks.Topology.Dimension.isClosed_singleton_of_topologicalKrullDim_le_zero hdim _
  simpa using hemb.isClosedMap _ h1

/-- **A one-point subspace has Krull dimension zero**, so a module whose support is a single
point satisfies the zero-dimensionality condition of [Stacks, Tag 0FZ9]. -/
theorem topologicalKrullDim_singleton {X : Type u} [TopologicalSpace X] (x : X) :
    topologicalKrullDim ({x} : Set X) = 0 :=
  have : Nonempty ({x} : Set X) := ⟨⟨x, rfl⟩⟩
  have : Subsingleton ({x} : Set X) := (Set.subsingleton_coe _).mpr Set.subsingleton_singleton
  topologicalKrullDim_eq_zero_of_subsingleton

/-! ### Vanishing detected at the closed points -/

/-- **A module of finite type on a Jacobson scheme whose stalks at the closed points vanish is
zero.** The support of a module of finite type is closed ([Stacks, Tag 056J]), a nonempty closed
subset of a Jacobson space meets the closed points, and a point lies outside the support exactly
when the stalk there is zero. -/
theorem isZero_of_forall_isZero_stalk_closedPoints {X : Scheme.{u}} [JacobsonSpace X]
    (F : X.Modules) [F.IsFiniteType]
    (h : ∀ x ∈ closedPoints X, IsZero ((Scheme.Modules.stalkFunctor X x).obj F)) :
    IsZero F := by
  have hempty : SheafOfModules.supp F = ∅ := by
    rw [← Set.not_nonempty_iff_eq_empty]
    intro hne
    obtain ⟨z, hz, hzc⟩ :=
      nonempty_inter_closedPoints hne (SheafOfModules.isClosed_supp F).isLocallyClosed
    exact ((Scheme.Modules.notMem_supp_iff_isZero_stalk F z).2 (h z hzc)) hz
  refine isZero_of_forall_isZero_stalk F fun x => ?_
  have hx : ∀ a : F.presheaf.stalk x, a = 0 := by
    intro a
    by_contra ha
    exact absurd ((SheafOfModules.mem_supp_iff_nontrivial_stalk F x).2 ⟨⟨a, 0, ha⟩⟩)
      (by rw [hempty]; exact Set.notMem_empty x)
  have : Subsingleton (F.presheaf.stalk x) := ⟨fun a b => by rw [hx a, hx b]⟩
  exact AddCommGrpCat.isZero_of_subsingleton _

/-- **The fibre product of two schemes locally of finite type over a Jacobson base is a Jacobson
space** ([Stacks, Tag 02J6]): the second projection is locally of finite type by base change, and
so is its composite with the structure morphism of `Y`. -/
theorem jacobsonSpace_pullback {S X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    [LocallyOfFiniteType f] [LocallyOfFiniteType g] [JacobsonSpace S] :
    JacobsonSpace ↥(Limits.pullback f g : Scheme.{u}) :=
  have : LocallyOfFiniteType (Limits.pullback.snd f g) := inferInstance
  LocallyOfFiniteType.jacobsonSpace (Limits.pullback.snd f g ≫ g)

/-! ### The hypotheses of the bounded-fibres lemma -/

variable {S X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)

/-- **The Fourier-Mukai functor is functorial in its kernel.** A morphism `K ⟶ K'` of objects of
`D(𝒪_{X ×_S Y})` induces `Φ_K ⟶ Φ_{K'}`, namely the derived tensor product in its second
variable whiskered by the derived pullback along `pr₁` and the derived direct image along
`pr₂`. -/
abbrev fourierMukaiKernelMap {E E' : DerivedCategory (Limits.pullback f g).Modules} (a : E ⟶ E') :
    fourierMukai f g E ⟶ fourierMukai f g E' :=
  Functor.whiskerLeft (fourierMukaiPullback f g)
    (Functor.whiskerRight
      ((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor
        (Limits.pullback f g).toRingedSpace.sheaf).flip.map a)
      (fourierMukaiPushforward f g))

/-- The degrees in the union of the band `[-m, m]` and the band `[-m-n, m-n]` receding with
`n`. -/
public abbrev InBands (m n : ℕ) (i : ℤ) : Prop :=
  (-(m : ℤ) ≤ i ∧ i ≤ (m : ℤ)) ∨
    (-(m : ℤ) - (n : ℤ) ≤ i ∧ i ≤ (m : ℤ) - (n : ℤ))

/-- **The hypotheses of [Stacks, Tag 0FZ9]** on a system `K₀ ⟶ K₁ ⟶ ⋯` of objects of
`D(𝒪_{X ×_S Y})` and an integer `m ≥ 0`: the `Kₙ` are perfect with cohomology vanishing above
`m`, and for every coherent `𝒪_X`-module with zero-dimensional support the cohomology of its
integral transform by `Kₙ` is concentrated in `[-m, m] ∪ [-m-n, m-n]` and, for `n > 2m`, is
carried isomorphically by the transition maps throughout `[-m, m]`. -/
structure BoundedFibreTransforms
    (K : ℕ → DerivedCategory (Limits.pullback f g).Modules)
    (τ : ∀ n, K n ⟶ K (n + 1)) (m : ℕ) : Prop where
  /-- Every member of the system is a perfect object, [Stacks, Tag 08CM]. -/
  perfect : ∀ n, RingedSpace.IsPerfect (X := (Limits.pullback f g).toRingedSpace) (K n)
  /-- The cohomology of every member of the system vanishes in the degrees above `m`. -/
  upper : ∀ (n : ℕ) (i : ℤ), (m : ℤ) < i →
    IsZero ((DerivedCategory.homologyFunctor (Limits.pullback f g).Modules i).obj (K n))
  /-- For a coherent module with zero-dimensional support, the cohomology of the integral
  transform by `Kₙ` is concentrated in `[-m, m] ∪ [-m-n, m-n]`. -/
  fibreBand : ∀ (F : X.Modules) [F.IsCoherent],
      topologicalKrullDim (SheafOfModules.supp F) = 0 →
      ∀ (n : ℕ) (i : ℤ), ¬ InBands m n i →
      IsZero ((DerivedCategory.homologyFunctor Y.Modules i).obj
        ((fourierMukai f g (K n)).obj ((DerivedCategory.singleFunctor X.Modules 0).obj F)))
  /-- For a coherent module with zero-dimensional support and `n > 2m`, the transition map `τ n`
  is an isomorphism on the cohomology of the integral transforms throughout `[-m, m]`. -/
  fibreStable : ∀ (F : X.Modules) [F.IsCoherent],
      topologicalKrullDim (SheafOfModules.supp F) = 0 →
      ∀ (n : ℕ) (i : ℤ), 2 * m < n → -(m : ℤ) ≤ i → i ≤ (m : ℤ) →
      IsIso ((DerivedCategory.homologyFunctor Y.Modules i).map
        ((fourierMukaiKernelMap f g (τ n)).app
          ((DerivedCategory.singleFunctor X.Modules 0).obj F)))

/-! ### Vanishing of the cohomology of a perfect complex at the closed points -/

/-- **A cohomology sheaf of a perfect complex on a locally Noetherian Jacobson scheme vanishes in
a degree as soon as its stalks at the closed points do.** The cohomology sheaf of a perfect
complex is of finite type in every degree, which is the hypothesis that
`AlgebraicGeometry.isZero_of_forall_isZero_stalk_closedPoints` needs. -/
theorem isZero_homology_of_forall_isZero_stalk_closedPoints {X : Scheme.{u}}
    [IsLocallyNoetherian X] [JacobsonSpace X] (E : DerivedCategory X.Modules)
    (hE : RingedSpace.IsPerfect (X := X.toRingedSpace) E) (i : ℤ)
    (h : ∀ x ∈ closedPoints X, IsZero ((Scheme.Modules.stalkFunctor X x).obj
      ((DerivedCategory.homologyFunctor X.Modules i).obj E))) :
    IsZero ((DerivedCategory.homologyFunctor X.Modules i).obj E) :=
  have := isFiniteType_homology_of_isPerfect X E hE i
  isZero_of_forall_isZero_stalk_closedPoints _ h

/-! ### The integral transforms of the test modules -/

section Reflect

open RingedSpaceModuleAdjunction Stacks.Cohomology.PushforwardRestriction
open Stacks.AlgebraicGeometry.SupportedPushforwardReflect
  (isZero_homology_of_isZero_homology_derivedPushforward_pullback_snd)

/-- **A locally finite type morphism into a Jacobson scheme carries closed points to closed
points** ([Stacks, Tag 01TB]). -/
@[ega "IV 10.9.2" "more general"]
public theorem isClosed_singleton_base_of_isClosed_singleton {X' Y' : Scheme.{u}} (h : X' ⟶ Y')
    [LocallyOfFiniteType h] [JacobsonSpace ↥Y'] {x : X'}
    (hx : IsClosed ({x} : Set X')) : IsClosed ({h.base x} : Set Y') := by
  have hJ : JacobsonSpace ↥Y' := inferInstance
  have hY : ∀ (T : Scheme.{u}) (p : T ⟶ Y') [LocallyOfFiniteType p] (t : T),
      IsClosed ({t} : Set T) → IsClosed ({p t} : Set Y') :=
    ((jacobsonSpace_finiteTypePoints_tfae Y').out 1 3).mp hJ
  exact hY X' h x hx

/-- The two spellings of the stalk of a sheaf of modules on a scheme have the same carrier, so a
module whose stalk over the local ring vanishes has vanishing stalk over the `RingCat`-valued
stalk of the structure sheaf. -/
public theorem isZero_stalkFunctor_of_isZero_modulesStalk {W : Scheme.{u}} (w : W)
    {M : W.Modules} (h : IsZero ((Stacks.ModuleSkyscraper.modulesStalkFunctor W w).obj M)) :
    IsZero ((Scheme.Modules.stalkFunctor W w).obj M) := by
  have h2 := h.of_iso ((restrictScalarsStalkFunctorIso w).app M)
  rw [ModuleCat.isZero_iff_subsingleton] at h2 ⊢
  exact h2

/-- The derived tensor product of [Stacks, Tag 06YU] on `D(𝒪_{X ×_S Y})`, with its two variables
exchanged so that the kernel is the first one: `(K, M) ⟼ M ⊗^𝐋 K`. -/
public abbrev fourierMukaiTensorFlip :
    DerivedCategory (Limits.pullback f g).Modules ⥤
      DerivedCategory (Limits.pullback f g).Modules ⥤
        DerivedCategory (Limits.pullback f g).Modules :=
  (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor
    (Limits.pullback f g).toRingedSpace.sheaf).flip

/-- `R pr_{2,*}(pr_1^*𝓕 ⊗^𝐋_{𝒪_{X ×_S Y}} K)`: the integral transform by the kernel `K` of an
`𝒪_X`-module `𝓕`, pulled back along `pr₁` and placed in degree `0`. This is the object the two
conditions of [Stacks, Tag 0FZ9] constrain. -/
public abbrev fibreTransform (K : DerivedCategory (Limits.pullback f g).Modules)
    (F : X.Modules) : DerivedCategory Y.Modules :=
  (fourierMukaiPushforward f g).obj ((fourierMukaiTensor f g K).obj
    ((DerivedCategory.singleFunctor (Limits.pullback f g).Modules 0).obj
      ((Scheme.Modules.pullback (Limits.pullback.fst f g)).obj F)))

/-- **The three general comparisons for the derived tensor product on `D(𝒪_{X ×_S Y})`** that the
reflection step of [Stacks, Tag 0FZ9] consumes: the derived form of [Stacks, Tag 01CB] at each
point, the stability of quasi-coherent cohomology under tensoring with a quasi-coherent module,
and the fact that tensoring with the pullback of a module supported in `Z` has its cohomology
supported over `Z`. Each is quantified over all of its own data. -/
public structure FibreTensorComparisons where
  /-- A derived tensor product on `D(𝒪_{X ×_S Y, z})` at every point `z`. -/
  ringTensor : ∀ z : ↥(Limits.pullback f g),
    CochainComplex.DerivedTensor.DerivedTensorProduct ((Limits.pullback f g).presheaf.stalk z)
  /-- **[Stacks, Tag 01CB] in derived form**: the stalk of a derived tensor product of sheaves is
  the derived tensor product of the stalks. -/
  stalk : ∀ (z : ↥(Limits.pullback f g))
    (E F : DerivedCategory (Limits.pullback f g).Modules),
    (derivedStalkFunctor z).obj ((fourierMukaiTensor f g E).obj F) ≅
      ((ringTensor z).tensor.obj ((derivedStalkFunctor z).obj E)).obj
        ((derivedStalkFunctor z).obj F)
  /-- The derived tensor product of an object with quasi-coherent cohomology and a quasi-coherent
  module has quasi-coherent cohomology. -/
  quasicoherent : ∀ (E : DerivedCategory (Limits.pullback f g).Modules)
    (M : (Limits.pullback f g).Modules), M.IsQuasicoherent →
    (∀ j : ℤ, ((DerivedCategory.homologyFunctor (Limits.pullback f g).Modules j).obj
      E).IsQuasicoherent) →
    ∀ j : ℤ, ((DerivedCategory.homologyFunctor (Limits.pullback f g).Modules j).obj
      ((fourierMukaiTensor f g E).obj
        ((DerivedCategory.singleFunctor (Limits.pullback f g).Modules 0).obj
          M))).IsQuasicoherent
  /-- Tensoring with the pullback along `pr₁` of a module supported in `Z` gives an object whose
  cohomology is supported over `Z`. -/
  supported : ∀ (E : DerivedCategory (Limits.pullback f g).Modules) (F : X.Modules)
    (Z : Set ↥X), SheafOfModules.supp F ⊆ Z →
    CohomologySupportedOn (structureSheafRing (Limits.pullback f g).toRingedSpace)
      ((Limits.pullback.fst f g).base ⁻¹' Z)
      ((fourierMukaiTensor f g E).obj
        ((DerivedCategory.singleFunctor (Limits.pullback f g).Modules 0).obj
          ((Scheme.Modules.pullback (Limits.pullback.fst f g)).obj F)))

/-- **The degreewise reflection step of [Stacks, Tag 0FZ9].** Let `S` be affine and Jacobson, let
`X` and `Y` be locally of finite type over `S` with `X` and `X ×_S Y` locally Noetherian, and let
`K` be a perfect object of `D(𝒪_{X ×_S Y})` whose cohomology vanishes above some degree. If the
`i`-th cohomology sheaf of the integral transform `R pr_{2,*}(pr_1^*𝓕 ⊗^𝐋 K)` vanishes for every
coherent `𝒪_X`-module `𝓕` with zero-dimensional support, then the `i`-th cohomology sheaf of `K`
vanishes.

The transforms of the infinitesimal neighbourhoods `𝒪_X/𝔪_x^t` of a closed point `x` are enough:
the second projection detects vanishing of cohomology supported over `x`, the adic criterion
[Stacks, Tag 0EGV] then kills the cohomology of the stalk of `K` at every point over `x`, and a
cohomology sheaf of a perfect complex vanishing at all closed points vanishes. -/
public theorem isZero_homology_of_isZero_homology_fibreTransform [IsAffine S] [JacobsonSpace ↥S]
    [LocallyOfFiniteType f] [LocallyOfFiniteType g] [IsLocallyNoetherian X]
    [IsLocallyNoetherian (Limits.pullback f g)] (cmp : FibreTensorComparisons f g)
    (K : DerivedCategory (Limits.pullback f g).Modules)
    (hK : RingedSpace.IsPerfect (X := (Limits.pullback f g).toRingedSpace) K)
    (b : ℤ) (hb : ∀ j : ℤ, b < j →
      IsZero ((DerivedCategory.homologyFunctor (Limits.pullback f g).Modules j).obj K))
    (i : ℤ)
    (hvan : ∀ F : X.Modules, F.IsCoherent →
      topologicalKrullDim (SheafOfModules.supp F) = 0 →
      IsZero ((DerivedCategory.homologyFunctor Y.Modules i).obj (fibreTransform f g K F))) :
    IsZero ((DerivedCategory.homologyFunctor (Limits.pullback f g).Modules i).obj K) := by
  have hJX : JacobsonSpace ↥X := LocallyOfFiniteType.jacobsonSpace f
  have hJP : JacobsonSpace ↥(Limits.pullback f g) := jacobsonSpace_pullback f g
  have hKqc : ∀ j : ℤ,
      ((DerivedCategory.homologyFunctor (Limits.pullback f g).Modules j).obj K).IsQuasicoherent :=
    isQuasicoherentDerived_of_isPseudoCoherent _ K hK.isPseudoCoherent
  refine isZero_homology_of_forall_isZero_stalk_closedPoints K hK i fun w hw => ?_
  have hx : IsClosed ({(Limits.pullback.fst f g).base w} : Set X) :=
    isClosed_singleton_base_of_isClosed_singleton (Limits.pullback.fst f g) hw
  obtain ⟨-, ⟨U, hU, rfl⟩, hxU, -⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ ((Limits.pullback.fst f g).base w)) isOpen_univ
  refine isZero_stalkFunctor_of_isZero_modulesStalk w ?_
  have hten : ∀ t : ℕ, IsZero ((DerivedCategory.homologyFunctor
      (Limits.pullback f g).Modules i).obj ((fourierMukaiTensor f g K).obj
        (pullbackPointTestModuleSystem (Limits.pullback.fst f g) w t))) := by
    intro t
    change IsZero ((DerivedCategory.homologyFunctor (Limits.pullback f g).Modules i).obj
      ((fourierMukaiTensor f g K).obj
        ((DerivedCategory.singleFunctor (Limits.pullback f g).Modules 0).obj
          ((Scheme.Modules.pullback (Limits.pullback.fst f g)).obj
            (pointTestModule ((Limits.pullback.fst f g).base w) (t + 1))))))
    have hcoh : (pointTestModule ((Limits.pullback.fst f g).base w) (t + 1)).IsCoherent :=
      isCoherent_pointTestModule _ _
    have hqc : (pointTestModule ((Limits.pullback.fst f g).base w) (t + 1)).IsQuasicoherent :=
      isQuasicoherent_of_isCoherent _
    have hsupp := supp_pointTestModule ((Limits.pullback.fst f g).base w) hx
      (Nat.succ_ne_zero t)
    refine isZero_homology_of_isZero_homology_derivedPushforward_pullback_snd f g hU hx
      (Set.singleton_subset_iff.2 hxU) _
      (cmp.quasicoherent K _
        (Stacks.AlgebraicGeometry.AffineBaseChange.isQuasicoherent_pullback _ _) hKqc)
      (cmp.supported K _ _ hsupp.subset)
      (hvan _ hcoh (topologicalKrullDim_supp_pointTestModule _ hx (Nat.succ_ne_zero t)))
  refine (isZero_homology_derivedStalk_of_isZero_homology_pullbackPointTestModule
    (Limits.pullback.fst f g) w hx (fourierMukaiTensorFlip f g) (cmp.ringTensor w)
    (cmp.stalk w) K ?_ i hten).of_iso
      (((Stacks.ModuleSkyscraper.modulesStalkFunctor _ w).mapDerivedCategoryHomologyIso
        i).app K).symm
  exact isPseudoCoherent_derivedStalk_of_finite_stalk_homology w K ⟨b, hb⟩
    fun j => finite_modulesStalk_homology_of_isPerfect _ K hK w j

end Reflect

/-! ### Two readings of the homology sequence of a distinguished triangle -/

section Triangles

open CategoryTheory.Pretriangulated

variable {A : Type*} [Category A] [Abelian A] [HasDerivedCategory A]
  (T : Triangle (DerivedCategory A)) (hT : T ∈ distTriang (DerivedCategory A)) (n₀ n₁ : ℤ)
  (h : n₀ + 1 = n₁)

include hT h

/-- **The third vertex of a distinguished triangle has vanishing cohomology in a degree where
the first two do.** -/
public theorem isZero_homology_obj₃_of_isZero
    (h₂ : IsZero ((DerivedCategory.homologyFunctor A n₀).obj T.obj₂))
    (h₁ : IsZero ((DerivedCategory.homologyFunctor A n₁).obj T.obj₁)) :
    IsZero ((DerivedCategory.homologyFunctor A n₀).obj T.obj₃) :=
  (DerivedCategory.HomologySequence.exact₃ T hT n₀ n₁ h).isZero_of_both_isZero h₂ h₁


/-- **The first morphism of a distinguished triangle is invertible on `H^{n₁}`** as soon as the
third vertex has vanishing cohomology in the degrees `n₀` and `n₁`. -/
public theorem isIso_homologyMap_mor₁_of_isZero
    (h₀ : IsZero ((DerivedCategory.homologyFunctor A n₀).obj T.obj₃))
    (h₁ : IsZero ((DerivedCategory.homologyFunctor A n₁).obj T.obj₃)) :
    IsIso ((DerivedCategory.homologyFunctor A n₁).map T.mor₁) :=
  have : Epi ((DerivedCategory.homologyFunctor A n₁).map T.mor₁) :=
    (DerivedCategory.HomologySequence.epi_homologyMap_mor₁_iff T hT n₁).2
      (h₁.eq_of_tgt _ _)
  have : Mono ((DerivedCategory.homologyFunctor A n₁).map T.mor₁) :=
    (DerivedCategory.HomologySequence.mono_homologyMap_mor₁_iff T hT n₀ n₁ h).2
      (h₀.eq_of_src _ _)
  isIso_of_mono_of_epi _

end Triangles

/-! ### The two assertions of the tag -/

section Bands

open CategoryTheory.Pretriangulated RingedSpaceModuleAdjunction
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPushforward derivedPushforwardUnit)
open Stacks.DerivedTensor.RingedSite (canonicalDerivedTensorProduct derivedTensorProductFunctor)

/-- `R pr_{2,*}(pr_1^*𝓕 ⊗^𝐋 -)`, the integral transform of a fixed `𝒪_X`-module `𝓕` read as a
functor of the kernel. -/
public abbrev fibreTransformFunctor (F : X.Modules) :
    DerivedCategory (Limits.pullback f g).Modules ⥤ DerivedCategory Y.Modules :=
  (derivedTensorProductFunctor (Limits.pullback f g).toRingedSpace.sheaf).obj
      ((DerivedCategory.singleFunctor (Limits.pullback f g).Modules 0).obj
        ((Scheme.Modules.pullback (Limits.pullback.fst f g)).obj F)) ⋙
    fourierMukaiPushforward f g

/-- `R pr_{2,*}` commutes with the shift, being the right adjoint in the derived adjunction of
[Stacks, Tag 079W] whose left adjoint does. -/
local instance commShift_pushforward : (fourierMukaiPushforward f g).CommShift ℤ :=
  Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforwardCommShift
    (Limits.pullback.snd f g).toLRSHom.toShHom

/-- `R pr_{2,*}` is exact, being the right adjoint of the exact derived pullback. -/
local instance isTriangulated_pushforward : (fourierMukaiPushforward f g).IsTriangulated :=
  Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforward_isTriangulated
    (Limits.pullback.snd f g).toLRSHom.toShHom

/-- `pr_1^*𝓕 ⊗^𝐋 -` commutes with the shift, by [Stacks, Tag 06YU]. -/
local instance commShift_tensorFibre (F : X.Modules) :
    ((derivedTensorProductFunctor (Limits.pullback f g).toRingedSpace.sheaf).obj
      ((DerivedCategory.singleFunctor (Limits.pullback f g).Modules 0).obj
        ((Scheme.Modules.pullback (Limits.pullback.fst f g)).obj F))).CommShift ℤ :=
  (canonicalDerivedTensorProduct (Limits.pullback f g).toRingedSpace.sheaf).commShift_right _

/-- `pr_1^*𝓕 ⊗^𝐋 -` is exact, by [Stacks, Tag 06YU]. -/
local instance isTriangulated_tensorFibre (F : X.Modules) :
    ((derivedTensorProductFunctor (Limits.pullback f g).toRingedSpace.sheaf).obj
      ((DerivedCategory.singleFunctor (Limits.pullback f g).Modules 0).obj
        ((Scheme.Modules.pullback (Limits.pullback.fst f g)).obj F))).IsTriangulated :=
  (canonicalDerivedTensorProduct (Limits.pullback f g).toRingedSpace.sheaf).exact_right _
variable [IsAffine S] [JacobsonSpace ↥S] [LocallyOfFiniteType f] [LocallyOfFiniteType g]
  [IsLocallyNoetherian X] [IsLocallyNoetherian (Limits.pullback f g)]

/-- **Stacks Project, Tag 0FZ9, part (1).** Let `S` be affine and Jacobson, let `X` and `Y` be
locally of finite type over `S` with `X` and `X ×_S Y` locally Noetherian, and let `K` be a
perfect object of `D(𝒪_{X ×_S Y})` whose cohomology vanishes above `m`. If for every coherent
`𝒪_X`-module `𝓕` with zero-dimensional support the cohomology of the integral transform
`R pr_{2,*}(pr_1^*𝓕 ⊗^𝐋 K)` is concentrated in `[-m, m] ∪ [-m-n, m-n]`, then so is the
cohomology of `K` itself. -/
@[stacks 0FZ9 "part (1), the two bands for the kernels, with the general derived-tensor \
comparisons carried as FibreTensorComparisons"]
public theorem isZero_homology_of_notInBands (cmp : FibreTensorComparisons f g)
    (K : DerivedCategory (Limits.pullback f g).Modules)
    (hK : RingedSpace.IsPerfect (X := (Limits.pullback f g).toRingedSpace) K) (m n : ℕ)
    (hupper : ∀ j : ℤ, (m : ℤ) < j →
      IsZero ((DerivedCategory.homologyFunctor (Limits.pullback f g).Modules j).obj K))
    (hband : ∀ F : X.Modules, F.IsCoherent →
      topologicalKrullDim (SheafOfModules.supp F) = 0 → ∀ j : ℤ, ¬ InBands m n j →
      IsZero ((DerivedCategory.homologyFunctor Y.Modules j).obj (fibreTransform f g K F)))
    (i : ℤ) (hi : ¬ InBands m n i) :
    IsZero ((DerivedCategory.homologyFunctor (Limits.pullback f g).Modules i).obj K) :=
  isZero_homology_of_isZero_homology_fibreTransform f g cmp K hK (m : ℤ) hupper i
    fun F hF hdim => hband F hF hdim i hi

end Bands

end AlgebraicGeometry

end
