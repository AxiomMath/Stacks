module

public import StacksFrontier.AlgebraicGeometry.Blowup.AwayBaseChange
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjGradedBaseChange
public import StacksFrontier.AlgebraicGeometry.TwistChartLocality.ChartGamma

/-!
# The comparison maps on the twists of a base change are isomorphisms

Let `A` be a graded `R`-algebra with grading `𝒜 : ℕ → Submodule R A`, let `S` be an `R`-algebra,
and let `ψ : 𝒜 → S ⊗[R] 𝒜` be the base-change homomorphism `a ↦ 1 ⊗ a`. Tag 01MY attaches to
`ψ` a morphism `r_ψ : Y = Proj (S ⊗[R] A) ⟶ X = Proj A` together with comparison maps

`θ n : r_ψ^* 𝒪_X(n) ⟶ 𝒪_Y(n)`

on all the twisting sheaves. This file proves that every `θ n` is an **isomorphism**, which is
clause (3) of Tag 01N2, for an arbitrary graded algebra, an arbitrary base change and every
`n : ℤ`.

## Main results

* `Stacks.ProjBaseChange.isIso_twistMap_includeRight`: **clause (3) of Tag 01N2.**
* `Stacks.AlgebraicGeometry.TwistChartLocality.isIso_of_isIso_pullback_awayι_of_mapDomain_eq_top`
  and `isIso_projTwistComparison_of_forall_pullback_awayι_of_mapDomain_eq_top`: the reduction of
  invertibility to the chart spectra of **all** homogeneous elements of positive degree, for a
  graded ring homomorphism whose domain of definition is everything.
* `TwistChartLocality.isIso_pullback_awayι_map_twistMap_of_isIso_extension` and
  `isIso_transpose_chartAdjointTwistMap_of_isIso_extension`: the chart criterion of
  `StacksFrontier/AlgebraicGeometry/TwistChartLocality/ChartGamma.lean` with the degree-one hypothesis
  traded for invertibility of the coefficient extension of the algebraic chart comparison.
* `Stacks.ProjBaseChange.isPushout_chart`: the chart `(S ⊗ 𝒜)₍1 ⊗ a₎` of the base change is the
  base change `S ⊗_R 𝒜₍a₎` of the chart, as an `Algebra.IsPushout`.
* `Stacks.ProjBaseChange.chartTwistBaseChange_one_tmul`: the canonical base-change isomorphism of
  the degree-`n` twist on a chart **is** Tag 01MY's chart comparison.
* `Stacks.ProjBaseChange.isIso_twistDegreeZeroExtension`: the coefficient extension of that chart
  comparison is invertible, at a homogeneous element of **any** positive degree.

## The route, and why the degree-one restriction disappears

Invertibility of `θ n` is local on `Y`, and `Y` is covered by the charts `D₊(ψ f)` with `f`
homogeneous of positive degree precisely because the domain of definition of `ψ` is everything,
which is clause (1) of the tag
(`Stacks.AlgebraicGeometry.ProjShared.mapDomain_baseChange`). The chain of
`StacksFrontier/AlgebraicGeometry/TwistChartLocality/ChartGamma.lean` identifies the inverse image
of `θ n` along such a chart with an inverse adjoint transpose whose global sections are the
algebraic comparison `𝒜(n)₍f₎ → ℬ(n)₍ψ f₎`, and reduces invertibility to invertibility of the
coefficient extension

`ℬ₍ψ f₎ ⊗_{𝒜₍f₎} 𝒜(n)₍f₎ ⟶ ℬ(n)₍ψ f₎`.

For a general graded ring homomorphism that extension is handled by rank-one freeness of the two
chart modules, which forces `deg f = 1` and genuinely fails above it — see
`StacksFrontier/AlgebraicGeometry/TwistChartLocality/DegreeOneFree.lean`. For a **base change** no
freeness is needed, and this is the mathematical point of the file: the chart of the base change
is the base change of the chart, `ℬ₍1 ⊗ a₎ = S ⊗_R 𝒜₍a₎`, and the chart sections of the twist
base-change along it, `ℬ(n)₍1 ⊗ a₎ = S ⊗_R 𝒜(n)₍a₎`. So the coefficient extension is

`(S ⊗_R 𝒜₍a₎) ⊗_{𝒜₍a₎} 𝒜(n)₍a₎ = S ⊗_R 𝒜(n)₍a₎ = ℬ(n)₍1 ⊗ a₎`,

a cancellation of base changes followed by an identification, both canonical. The cancellation is
Mathlib's `Algebra.IsPushout.cancelBaseChange`, applied to
`Stacks.ProjBaseChange.isPushout_chart`; the identification is
`Stacks.ProjStandardOpenBaseChange.standardOpenBaseChange`; and the statement that the composite
is the chart comparison is `Stacks.ProjBaseChange.chartTwistBaseChange_one_tmul`.

## Implementation notes

The two models of the chart sections of a twist — a submodule of the localized module and a
submodule of the localized ring — are bridged by
`Stacks.AlgebraicGeometry.TwistAwayBridge.twistAwayEquiv`. The base-change isomorphism lives in
the second, Tag 01MY's comparison in the first, so every statement below passes through that
bridge.

The element `1 ⊗ a` of the base change has three definitionally equal spellings in the library —
the pure tensor, the image under `Stacks.ProjBaseChange.includeRight` and the image under
`Stacks.ProjStandardOpenBaseChange.gradedBaseChangeMap` — and `rw` does not see through the
difference, since it sits in the index of a dependent type. The pure tensor is taken as canonical
and `Stacks.ProjBaseChange.chartTwistBaseChange` and `Stacks.ProjBaseChange.chartTwistMap` are
named wrappers carrying the types in that spelling; the steps that cross from one spelling to
another are taken by `Eq.trans` and `congrArg`, which check at default transparency.

`Stacks.ProjBaseChange.isScalarTower_chart_base` and `isScalarTower_chart_away` pin their scalar
actions to the ones the algebra structures supply, by `@IsScalarTower … Algebra.toSMul …`. A
homogeneous localization carries Mathlib's own `SMul` for the base ring beside the one coming
from its algebra structure, and the two are not the same instance term; `Algebra.IsPushout` asks
for the second, so stating these towers with the instance that search finds makes them
unusable there.

## What is not proved

Compatibility of `θ` with the multiplication maps `𝒪(n) ⊗ 𝒪(m) → 𝒪(n + m)` and with the unit is
not proved here, and no clause about that is claimed. Clauses (1) and (2) of Tag 01N2 are
`Stacks.AlgebraicGeometry.ProjShared.mapDomain_baseChange` and
`Stacks.ProjBaseChange.isPullback_map_of_baseChange`.

The comparison map inverted here is `Stacks.ProjTwistComparison.twistMap`, the one indexed by
`AlgebraicGeometry.Proj.map ψ`, which is the shape Tag 01N2 states — the morphism is defined on
all of `Y`. The sibling `Stacks.AlgebraicGeometry.ProjTwistCompare.twistMap`, indexed by the open
domain of definition `U(ψ)`, is **not** inverted here: nothing in the library identifies the two
comparison maps, and the identification is not a formal consequence of
`Stacks.AlgebraicGeometry.RelativeProj.mapHomOfTop_eq_map`.

## References

* [Stacks Project, Tag 01N2](https://stacks.math.columbia.edu/tag/01N2)
* [Stacks Project, Tag 01MY](https://stacks.math.columbia.edu/tag/01MY)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct HomogeneousIdeal HomogeneousLocalization
open AlgebraicGeometry.ProjectiveSpectrum.Proj
open AlgebraicGeometry.Scheme.Modules
open Stacks.AlgebraicGeometry.ProjShared
open scoped ChangeOfRings

universe u

namespace Stacks.AlgebraicGeometry.TwistChartLocality

attribute [local implicit_reducible] TopCat.Sheaf sheafCompose AlgebraicGeometry.Proj
attribute [local instance] ProjectiveSpectrum.isPrime
attribute [local instance_reducible] ProjectiveSpectrum.top

/-! ### The positive-degree chart cover -/

section Cover

variable {A B : Type u} {σ τ : Type u}
  [CommRing A] [CommRing B] [SetLike σ A] [AddSubgroupClass σ A]
  [SetLike τ B] [AddSubgroupClass τ B]
  (𝒜 : ℕ → σ) (ℬ : ℕ → τ) [GradedRing 𝒜] [GradedRing ℬ]

omit [AddSubgroupClass σ A] [GradedRing 𝒜] in
/-- **Invertibility of a homomorphism of modules on `Proj ℬ` is detected by the inverse images
along the chart spectra of the images of the homogeneous elements of positive degree**, whenever
the domain of definition of `ψ` is all of `Proj ℬ`.

This is the positive-degree analogue of
`Stacks.AlgebraicGeometry.TwistChartLocality.isIso_of_isIso_pullback_awayι`, whose cover is
indexed by the degree-one elements alone and therefore needs the images of `𝒜 1` to generate the
irrelevant ideal of `ℬ`. Here the cover is the defining one of
`Stacks.AlgebraicGeometry.ProjShared.mapDomain`, so the hypothesis is exactly that the domain of
definition is everything. -/
public theorem isIso_of_isIso_pullback_awayι_of_mapDomain_eq_top (ψ : 𝒜 →+*ᵍ ℬ)
    (hdom : mapDomain 𝒜 ℬ ψ = ⊤)
    {M N : (AlgebraicGeometry.Proj ℬ).Modules} (φ : M ⟶ N)
    (h : ∀ (d : ℕ) (hd : 0 < d) (f : A) (hf : f ∈ 𝒜 d),
      IsIso ((Scheme.Modules.pullback (AlgebraicGeometry.Proj.awayι ℬ (ψ f)
        (ψ.map_mem hf) hd)).map φ)) :
    IsIso φ := by
  refine Scheme.Modules.isIso_of_isIso_pullback_ι
    (fun i : Σ d : {d : ℕ // 0 < d}, {f : A // f ∈ 𝒜 d.1} =>
      (AlgebraicGeometry.Proj.awayι ℬ (ψ i.2.1) (ψ.map_mem i.2.2) i.1.2).opensRange) ?_ φ ?_
  · refine eq_top_iff.mpr fun y _ => ?_
    have hy : y ∈ mapDomain 𝒜 ℬ ψ := hdom ▸ trivial
    obtain ⟨d, f, hd, hf, hfy⟩ := (mem_mapDomain_iff 𝒜 ℬ ψ y).mp hy
    refine TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨⟨d, hd⟩, ⟨f, hf⟩⟩, ?_⟩
    rw [AlgebraicGeometry.Proj.opensRange_awayι]
    exact (AlgebraicGeometry.Proj.mem_basicOpen ℬ _ _).mpr hfy
  · intro i
    have h1 := h i.1.1 i.1.2 i.2.1 i.2.2
    rw [← Scheme.Hom.isoOpensRange_hom_ι (AlgebraicGeometry.Proj.awayι ℬ (ψ i.2.1)
      (ψ.map_mem i.2.2) i.1.2)] at h1
    exact (Scheme.Modules.isIso_pullback_map_iff_of_isIso _ _).mp
      ((Scheme.Modules.isIso_pullback_comp_map_iff _ _ _).mp h1)

/-- **The reduction of Tag 01MY's comparison map to the inverse images along the chart spectra of
the images of all homogeneous elements of positive degree.** -/
public theorem isIso_projTwistComparison_of_forall_pullback_awayι_of_mapDomain_eq_top
    (ψ : 𝒜 →+*ᵍ ℬ) (hψ : ℬ₊ ≤ 𝒜₊.map ψ) (hdom : mapDomain 𝒜 ℬ ψ = ⊤) (n : ℤ)
    (h : ∀ (d : ℕ) (hd : 0 < d) (f : A) (hf : f ∈ 𝒜 d),
      IsIso ((Scheme.Modules.pullback (AlgebraicGeometry.Proj.awayι ℬ (ψ f)
          (ψ.map_mem hf) hd)).map
        (Stacks.ProjTwistComparison.twistMap ψ hψ n))) :
    IsIso (Stacks.ProjTwistComparison.twistMap ψ hψ n) :=
  isIso_of_isIso_pullback_awayι_of_mapDomain_eq_top 𝒜 ℬ ψ hdom _ h

end Cover

/-! ### The chart transpose in an arbitrary positive degree -/

section AnyDegree

universe v v'

variable {A B : Type u} {R : Type v} {R' : Type v'}
  [CommRing A] [CommRing B] [CommRing R] [CommRing R'] [Algebra R A] [Algebra R' B]
  (𝒜 : ℕ → Submodule R A) (ℬ : ℕ → Submodule R' B) [GradedAlgebra 𝒜] [GradedAlgebra ℬ]
  (ψ : 𝒜 →+*ᵍ ℬ) (hψ : ℬ₊ ≤ 𝒜₊.map ψ) {d : ℕ} (hd : 0 < d) {f : A} (hf : f ∈ 𝒜 d) (n : ℤ)

/-- **The chart transpose of Tag 01MY's comparison map is invertible as soon as the coefficient
extension of the algebraic chart comparison is**, at a homogeneous element of any positive degree.

This is `Stacks.AlgebraicGeometry.TwistChartLocality.isIso_transpose_chartAdjointTwistMap` with
the degree-one hypothesis traded for the invertibility of
`Stacks.AlgebraicGeometry.TwistChartLocality.twistDegreeZeroExtension`, which in degree one is
supplied by rank-one freeness of the two chart modules and in general is not. Everything else in
the chain is already stated at an arbitrary positive degree: the quasi-coherence of the two
chart inverse images, the chart identification
`Stacks.AlgebraicGeometry.TwistChartLocality.chartΓIso` and the Γ bridge
`Stacks.AlgebraicGeometry.TwistChartLocality.chartΓIso_moduleSpecΓ_chartAdjointTwistMap`. -/
public theorem isIso_transpose_chartAdjointTwistMap_of_isIso_extension
    (hext : IsIso (twistDegreeZeroExtension 𝒜 ℬ ψ (f := f) n)) :
    IsIso (transpose (CommRingCat.ofHom (Away.map ψ f))
      ((pullback (AlgebraicGeometry.Proj.awayι 𝒜 f hf hd)).obj (twistingSheaf 𝒜 n))
      ((pullback (AlgebraicGeometry.Proj.awayι ℬ (ψ f) (ψ.map_mem hf) hd)).obj
        (twistingSheaf ℬ n))
      (chartAdjointTwistMap 𝒜 ℬ ψ hψ hd hf n)) := by
  have := isQuasicoherent_pullback_awayι_twistingSheaf 𝒜 hd hf n
  have := isQuasicoherent_pullback_awayι_twistingSheaf ℬ hd (ψ.map_mem hf) n
  have := hext
  refine isIso_transpose_of_isIso_extension _ _ _ _
    ((ModuleCat.extendScalars (Away.map ψ f)).map
        (chartΓIso 𝒜 (twistGrading (S := A) 𝒜 n) hf hd).hom ≫
      twistDegreeZeroExtension 𝒜 ℬ ψ n ≫
      (chartΓIso ℬ (twistGrading (S := B) ℬ n) (ψ.map_mem hf) hd).inv) ?_
  intro m
  refine Eq.trans (ConcreteCategory.comp_apply _ _ _) ?_
  refine Eq.trans (ConcreteCategory.comp_apply _ _ _) ?_
  refine Eq.trans (congrArg (ConcreteCategory.hom
      (chartΓIso ℬ (twistGrading (S := B) ℬ n) (ψ.map_mem hf) hd).inv)
    (twistDegreeZeroExtension_tmul 𝒜 ℬ ψ n _)) ?_
  refine Eq.trans (congrArg (ConcreteCategory.hom
      (chartΓIso ℬ (twistGrading (S := B) ℬ n) (ψ.map_mem hf) hd).inv)
    (chartΓIso_moduleSpecΓ_chartAdjointTwistMap 𝒜 ℬ ψ hψ hd hf n m).symm) ?_
  exact (chartΓIso ℬ (twistGrading (S := B) ℬ n) (ψ.map_mem hf) hd).hom_inv_id_apply _

/-- **The chart inverse image of Tag 01MY's comparison map is invertible as soon as the
coefficient extension of the algebraic chart comparison is**, at a homogeneous element of any
positive degree. -/
public theorem isIso_pullback_awayι_map_twistMap_of_isIso_extension
    (hext : IsIso (twistDegreeZeroExtension 𝒜 ℬ ψ (f := f) n)) :
    IsIso ((pullback (AlgebraicGeometry.Proj.awayι ℬ (ψ f) (ψ.map_mem hf) hd)).map
      (Stacks.ProjTwistComparison.twistMap ψ hψ n)) :=
  (isIso_pullback_awayι_map_twistMap_iff 𝒜 ℬ ψ hψ hd hf n).mpr
    (isIso_transpose_chartAdjointTwistMap_of_isIso_extension 𝒜 ℬ ψ hψ hd hf n hext)

end AnyDegree

end Stacks.AlgebraicGeometry.TwistChartLocality

/-! ### The chart algebra of a graded base change -/

namespace Stacks.ProjBaseChange

open Stacks.AlgebraicGeometry.TwistAwayBridge Stacks.AlgebraicGeometry.TwistChartLocality
open Stacks.ProjStandardOpenBaseChange

section ChartAlgebra

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
  (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜] (S : Type u) [CommRing S] [Algebra R S]
  {d : ℕ} {a : A}

attribute [local instance] chartAlgebraBase

/-- The chart-level base-change homomorphism read as an algebra structure, so that the chart of
the base change is an algebra over the chart of `𝒜`. This is the structure the extension of
scalars of `Stacks.AlgebraicGeometry.TwistChartLocality.twistDegreeZeroExtension` is formed
with. -/
@[instance_reducible]
def chartMapAlgebra : Algebra (Away 𝒜 a) (Away (grading 𝒜 S) ((1 : S) ⊗ₜ[R] a)) :=
  (Away.map (includeRight 𝒜 S) a).toAlgebra

attribute [local instance] chartMapAlgebra

/-- The base-changed chart is an `S`-algebra over `R` through `R → S`, by the very definition of
`Stacks.ProjBaseChange.chartAlgebraBase`. The scalar actions are pinned to the ones the algebra
structures supply, which is the spelling `Algebra.IsPushout` asks for. -/
theorem isScalarTower_chart_base :
    @IsScalarTower R S (Away (grading 𝒜 S) ((1 : S) ⊗ₜ[R] a))
      Algebra.toSMul Algebra.toSMul Algebra.toSMul :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

/-- The base-changed chart is an algebra over the chart of `𝒜` compatibly with `R`: this is the
compatibility recorded by `Stacks.ProjBaseChange.awayMapₐ`. The scalar actions are pinned as in
`Stacks.ProjBaseChange.isScalarTower_chart_base`. -/
theorem isScalarTower_chart_away :
    @IsScalarTower R (Away 𝒜 a) (Away (grading 𝒜 S) ((1 : S) ⊗ₜ[R] a))
      Algebra.toSMul Algebra.toSMul Algebra.toSMul :=
  IsScalarTower.of_algebraMap_eq fun r => ((awayMapₐ 𝒜 S (a := a)).commutes r).symm

attribute [local instance] isScalarTower_chart_base isScalarTower_chart_away

/-- The chart-level base-change homomorphism on the structure map of `S`. -/
theorem awayBaseChange_algebraMap (s : S) :
    awayBaseChange 𝒜 S (a := a) (algebraMap S (S ⊗[R] Away 𝒜 a) s) =
      algebraMap S (Away (grading 𝒜 S) ((1 : S) ⊗ₜ[R] a)) s := by
  rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self_apply,
    awayBaseChange_tmul, map_one, mul_one]
  exact (algebraMap_eq_fromZeroRingHom_tmulOne 𝒜 S s).symm

/-- The chart-level base-change isomorphism of
`Stacks.ProjBaseChange.awayBaseChangeEquiv`, as an isomorphism of `S`-algebras. -/
def awayBaseChangeAlgEquivBase (ha : a ∈ 𝒜 d) :
    S ⊗[R] Away 𝒜 a ≃ₐ[S] Away (grading 𝒜 S) ((1 : S) ⊗ₜ[R] a) :=
  AlgEquiv.ofRingEquiv (f := awayBaseChangeEquiv 𝒜 S ha) (awayBaseChange_algebraMap 𝒜 S)

/-- The chart-level base-change homomorphism on a pure tensor with trivial scalar. -/
theorem awayBaseChange_one_tmul (z : Away 𝒜 a) :
    awayBaseChange 𝒜 S ((1 : S) ⊗ₜ[R] z) = Away.map (includeRight 𝒜 S) a z := by
  rw [awayBaseChange_tmul, tmulOne_one, map_one, one_mul]
  rfl

/-- **The chart of a graded base change is the base change of the chart**, in the form the
cancellation `Algebra.IsPushout.cancelBaseChange` consumes. -/
theorem isPushout_chart (ha : a ∈ 𝒜 d) :
    Algebra.IsPushout R S (Away 𝒜 a) (Away (grading 𝒜 S) ((1 : S) ⊗ₜ[R] a)) := by
  refine ⟨IsBaseChange.of_equiv (awayBaseChangeAlgEquivBase 𝒜 S ha).toLinearEquiv fun z => ?_⟩
  show awayBaseChange 𝒜 S ((1 : S) ⊗ₜ[R] z) = _
  rw [awayBaseChange_one_tmul]
  rfl

/-- The `R`-module structure on the chart sections of a twist, restricted along `R → 𝒜₍a₎`. -/
@[instance_reducible]
def twistChartModuleBase (n : ℤ) :
    Module R (GradedModuleDegreeZeroLocalization 𝒜
      (AlgebraicGeometry.ProjectiveSpectrum.Proj.twistGrading (S := A) 𝒜 n) a) :=
  Module.compHom _ (algebraMap R (Away 𝒜 a))

attribute [local instance] twistChartModuleBase

/-- The chart sections of a twist are an `𝒜₍a₎`-module compatibly with `R`. -/
theorem isScalarTower_twistChart (n : ℤ) :
    @IsScalarTower R (Away 𝒜 a) (GradedModuleDegreeZeroLocalization 𝒜
      (AlgebraicGeometry.ProjectiveSpectrum.Proj.twistGrading (S := A) 𝒜 n) a)
      Algebra.toSMul _ _ :=
  IsScalarTower.of_algebraMap_smul fun _ _ => rfl

/-- The fraction model of the chart sections of a twist is an `𝒜₍a₎`-module compatibly with the
base ring. -/
theorem isScalarTower_twistAway (n : ℤ) :
    @IsScalarTower R (Away 𝒜 a) (twistAway 𝒜 a d n) Algebra.toSMul _ _ :=
  IsScalarTower.of_algebraMap_smul fun _ _ => rfl

/-- The fraction model of the base-changed chart sections is a module over the base-changed chart
compatibly with `S`. -/
theorem isScalarTower_twistAway_chart (n : ℤ) :
    @IsScalarTower S (Away (grading 𝒜 S) ((1 : S) ⊗ₜ[R] a))
      (twistAway (grading 𝒜 S) ((1 : S) ⊗ₜ[R] a) d n) Algebra.toSMul _ _ :=
  IsScalarTower.of_algebraMap_smul fun _ _ => rfl

attribute [local instance] isScalarTower_twistChart isScalarTower_twistAway
  isScalarTower_twistAway_chart

/-- Both `R`-module structures — on the chart sections of a twist and on their fraction model —
are restricted along `R → 𝒜₍a₎`, so an `𝒜₍a₎`-linear map between them is automatically
`R`-linear. -/
theorem compatibleSMul_twistChart (n : ℤ) :
    LinearMap.CompatibleSMul
      (GradedModuleDegreeZeroLocalization 𝒜
        (AlgebraicGeometry.ProjectiveSpectrum.Proj.twistGrading (S := A) 𝒜 n) a)
      (twistAway 𝒜 a d n) R (Away 𝒜 a) :=
  ⟨fun f c x => f.map_smul (algebraMap R (Away 𝒜 a) c) x⟩

attribute [local instance] compatibleSMul_twistChart

/-- The base-change isomorphism of the chart ring, on a pure tensor with trivial scalar: it is
the chart-level base-change homomorphism. -/
theorem ringEquiv_one_tmul (ha : a ∈ 𝒜 d) (hd : 0 < d) (p : Away 𝒜 a) :
    (standardOpenBaseChange (R' := S) 𝒜 a d ha hd).ringEquiv ((1 : S) ⊗ₜ[R] p) =
      Away.map (gradedBaseChangeMap (R' := S) 𝒜) a p := by
  rw [(standardOpenBaseChange (R' := S) 𝒜 a d ha hd).ringEquiv_tmul 1 p, map_one, one_mul]

/-- The base-change isomorphism of the degree-`n` twist on the chart of `a`, with the chart
element written as the pure tensor `1 ⊗ a` rather than as the image of `a`. All spellings of that
element are definitionally equal; this is the one the chart algebra below is phrased in. -/
def chartTwistBaseChange (ha : a ∈ 𝒜 d) (hd : 0 < d) (n : ℤ) :
    S ⊗[R] twistAway 𝒜 a d n ≃ₗ[S] twistAway (grading 𝒜 S) ((1 : S) ⊗ₜ[R] a) d n :=
  (standardOpenBaseChange (R' := S) 𝒜 a d ha hd).twistEquiv n

/-- **Tag 01MY's chart comparison on the degree-`n` twist for a graded base change**, with the
chart element written as the pure tensor `1 ⊗ a`. -/
def chartTwistMap (n : ℤ) :
    GradedModuleDegreeZeroLocalization 𝒜 (twistGrading (S := A) 𝒜 n) a →+
      GradedModuleDegreeZeroLocalization (grading 𝒜 S)
        (twistGrading (S := S ⊗[R] A) (grading 𝒜 S) n) ((1 : S) ⊗ₜ[R] a) :=
  twistDegreeZeroMap 𝒜 (grading 𝒜 S) (includeRight 𝒜 S) a n

/-- The chart comparison is semilinear over the chart-level base-change homomorphism. -/
theorem chartTwistMap_smul (n : ℤ) (p : Away 𝒜 a)
    (z : GradedModuleDegreeZeroLocalization 𝒜 (twistGrading (S := A) 𝒜 n) a) :
    chartTwistMap 𝒜 S n (p • z) = awayMap 𝒜 S a p • chartTwistMap 𝒜 S n z :=
  twistDegreeZeroMap_smul 𝒜 (grading 𝒜 S) (includeRight 𝒜 S) a n p z

/-- The base change of the twist is semilinear over the chart-level base-change homomorphism. -/
theorem chartTwistBaseChange_one_tmul_smul (ha : a ∈ 𝒜 d) (hd : 0 < d) (n : ℤ)
    (p : Away 𝒜 a) (y : twistAway 𝒜 a d n) :
    chartTwistBaseChange 𝒜 S ha hd n ((1 : S) ⊗ₜ[R] (p • y)) =
      awayMap 𝒜 S a p • chartTwistBaseChange 𝒜 S ha hd n ((1 : S) ⊗ₜ[R] y) :=
  Eq.trans ((standardOpenBaseChange (R' := S) 𝒜 a d ha hd).twistEquiv_smul n 1 p y)
    (congrArg (fun q : Away (grading 𝒜 S) ((1 : S) ⊗ₜ[R] a) =>
        q • chartTwistBaseChange 𝒜 S ha hd n ((1 : S) ⊗ₜ[R] y))
      (ringEquiv_one_tmul 𝒜 S ha hd p))

/-- The chart comparison of Tag 01MY on a homogeneous fraction, read in the fraction model of the
chart sections: it applies `a ↦ 1 ⊗ a` to the numerator and to the denominator. -/
private theorem chartTwistMap_val_mk (ha : a ∈ 𝒜 d) (n : ℤ) (k : ℕ) (x : A)
    (hxt : x ∈ twistGrading (S := A) 𝒜 n (k • (d : ℤ))) :
    ((twistAwayEquiv (grading 𝒜 S) (tmul_one_mem 𝒜 S ha) n
          (chartTwistMap 𝒜 S n (degreeZeroFraction 𝒜 (twistGrading (S := A) 𝒜 n) ha k x hxt)) :
        twistAway (grading 𝒜 S) ((1 : S) ⊗ₜ[R] a) d n) :
        Localization (Submonoid.powers ((1 : S) ⊗ₜ[R] a))) =
      algebraMap S (Localization (Submonoid.powers ((1 : S) ⊗ₜ[R] a))) 1 *
        Localization.mk ((1 : S) ⊗ₜ[R] x)
          ⟨((1 : S) ⊗ₜ[R] a) ^ k, Submonoid.pow_mem _ (Submonoid.mem_powers _) k⟩ := by
  rw [map_one, one_mul]
  refine Eq.trans (twistAwayEquiv_apply_val (grading 𝒜 S) (tmul_one_mem 𝒜 S ha) n _) ?_
  refine Eq.trans (congrArg (localizedAwayEquiv ((1 : S) ⊗ₜ[R] a))
    (awayModuleMap_mk 𝒜 (grading 𝒜 S) (includeRight 𝒜 S) a x
      ⟨a ^ k, Submonoid.pow_mem _ (Submonoid.mem_powers a) k⟩
      (by rw [map_pow]; exact Submonoid.pow_mem _ (Submonoid.mem_powers _) k))) ?_
  refine Eq.trans (localizedAwayEquiv_mk _ _ _) ?_
  exact congrArg (Localization.mk ((1 : S) ⊗ₜ[R] x))
    (Subtype.ext (map_pow (includeRight 𝒜 S) a k))

/-- The base change of the degree-`n` twist agrees with the chart comparison of Tag 01MY on a
homogeneous fraction. -/
private theorem chartTwistBaseChange_one_tmul_gen (ha : a ∈ 𝒜 d) (hd : 0 < d) (n : ℤ)
    (k e : ℕ) (x : A) (he : (e : ℤ) = ((k * d : ℕ) : ℤ) + n) (hx : x ∈ 𝒜 e) :
    chartTwistBaseChange 𝒜 S ha hd n ((1 : S) ⊗ₜ[R]
        (⟨Localization.mk x ⟨a ^ k, Submonoid.pow_mem _ (Submonoid.mem_powers a) k⟩,
          Submodule.subset_span ⟨k, e, x, he, hx, rfl⟩⟩ : twistAway 𝒜 a d n)) =
      twistAwayEquiv (grading 𝒜 S) (tmul_one_mem 𝒜 S ha) n
        (chartTwistMap 𝒜 S n ((twistAwayEquiv 𝒜 ha n).symm
          ⟨Localization.mk x ⟨a ^ k, Submonoid.pow_mem _ (Submonoid.mem_powers a) k⟩,
            Submodule.subset_span ⟨k, e, x, he, hx, rfl⟩⟩)) := by
  have hxt : x ∈ twistGrading (S := A) 𝒜 n (k • (d : ℤ)) := by
    have hdeg : k • (d : ℤ) + n = (e : ℤ) := by
      rw [he, nsmul_eq_mul]
      push_cast
      ring
    rwa [twistGrading_apply, hdeg, integerGrading_natCast, mem_homogeneousSubmodule]
  have hbeta : twistAwayEquiv 𝒜 ha n
        (degreeZeroFraction 𝒜 (twistGrading (S := A) 𝒜 n) ha k x hxt) =
      (⟨Localization.mk x ⟨a ^ k, Submonoid.pow_mem _ (Submonoid.mem_powers a) k⟩,
        Submodule.subset_span ⟨k, e, x, he, hx, rfl⟩⟩ : twistAway 𝒜 a d n) :=
    Subtype.ext ((twistAwayEquiv_apply_val 𝒜 ha n _).trans
      (localizedAwayEquiv_mk a x ⟨a ^ k, Submonoid.pow_mem _ (Submonoid.mem_powers a) k⟩))
  have hsym := (twistAwayEquiv 𝒜 ha n).symm_apply_eq.mpr hbeta.symm
  refine Subtype.ext ?_
  refine Eq.trans ((standardOpenBaseChange (R' := S) 𝒜 a d ha hd).twistEquiv_tmul_val
    n 1 k e x he hx) ?_
  refine Eq.trans (chartTwistMap_val_mk 𝒜 S ha n k x hxt).symm ?_
  exact congrArg (fun w => ((twistAwayEquiv (grading 𝒜 S) (tmul_one_mem 𝒜 S ha) n
      (chartTwistMap 𝒜 S n w) : twistAway (grading 𝒜 S) ((1 : S) ⊗ₜ[R] a) d n) :
        Localization (Submonoid.powers ((1 : S) ⊗ₜ[R] a)))) hsym.symm

/-- **The base change of the degree-`n` twist on a chart is Tag 01MY's chart comparison.** The
canonical base-change isomorphism of
`Stacks.ProjStandardOpenBaseChange.standardOpenBaseChange` sends `1 ⊗ y` to the image of `y`
under `Stacks.ProjBaseChange.chartTwistMap`, for every element `y` of the chart sections of the
twist and not merely for a homogeneous fraction.

This is the one non-formal step of the chart algebra: it says that the chart comparison *is* a
base change, which is why no freeness of the chart sections is needed. -/
theorem chartTwistBaseChange_one_tmul (ha : a ∈ 𝒜 d) (hd : 0 < d) (n : ℤ)
    (y : twistAway 𝒜 a d n) :
    chartTwistBaseChange 𝒜 S ha hd n ((1 : S) ⊗ₜ[R] y) =
      twistAwayEquiv (grading 𝒜 S) (tmul_one_mem 𝒜 S ha) n
        (chartTwistMap 𝒜 S n ((twistAwayEquiv 𝒜 ha n).symm y)) := by
  obtain ⟨y, hy⟩ := y
  induction hy using Submodule.span_induction with
  | mem w hw =>
      obtain ⟨k, e, x, he, hx, rfl⟩ := hw
      exact chartTwistBaseChange_one_tmul_gen 𝒜 S ha hd n k e x he hx
  | zero => simp only [← ZeroMemClass.zero_def, TensorProduct.tmul_zero, map_zero]
  | add u v hu hv ihu ihv =>
      rw [show (⟨u + v, _⟩ : twistAway 𝒜 a d n) = ⟨u, hu⟩ + ⟨v, hv⟩ from rfl]
      simp only [TensorProduct.tmul_add, map_add, ihu, ihv]
  | smul p u hu ihu =>
      rw [show (⟨p • u, _⟩ : twistAway 𝒜 a d n) = p • ⟨u, hu⟩ from rfl]
      simp only [chartTwistBaseChange_one_tmul_smul, _root_.map_smul,
        chartTwistMap_smul, ihu]

/-! ### The chart comparison of a base change -/

/-- **The chart comparison of the degree-`n` twist for a graded base change, as a bijection.**

Writing `P = 𝒜₍a₎`, `Q = (S ⊗ 𝒜)₍1 ⊗ a₎` and `M = 𝒜(n)₍a₎`, the source is the coefficient
extension `Q ⊗_P M` and the target is the fraction model of `(S ⊗ 𝒜)(n)₍1 ⊗ a₎`. The composite is
the cancellation `Q ⊗_P M = (S ⊗_R P) ⊗_P M = S ⊗_R M` along
`Stacks.ProjBaseChange.isPushout_chart`, followed by the base-change isomorphism of the twist
supplied by `Stacks.ProjStandardOpenBaseChange.standardOpenBaseChange`. No freeness of `M` is
used: that is what makes the base-change case work in every degree. -/
def chartTwistCompareEquiv (ha : a ∈ 𝒜 d) (hd : 0 < d) (n : ℤ) :
    TensorProduct (Away 𝒜 a) (Away (grading 𝒜 S) ((1 : S) ⊗ₜ[R] a))
        (GradedModuleDegreeZeroLocalization 𝒜 (twistGrading (S := A) 𝒜 n) a) ≃ₗ[S]
      twistAway (grading 𝒜 S) ((1 : S) ⊗ₜ[R] a) d n :=
  letI := isPushout_chart 𝒜 S ha
  Algebra.IsPushout.cancelBaseChange R S (Away 𝒜 a)
      (Away (grading 𝒜 S) ((1 : S) ⊗ₜ[R] a))
      (GradedModuleDegreeZeroLocalization 𝒜 (twistGrading (S := A) 𝒜 n) a) ≪≫ₗ
    TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl S S)
      ((twistAwayEquiv 𝒜 ha n).restrictScalars R) ≪≫ₗ
    chartTwistBaseChange 𝒜 S ha hd n

/-- The chart comparison of a base change on a pure tensor with trivial scalar: it is Tag 01MY's
chart comparison, read in the fraction model. -/
theorem chartTwistCompareEquiv_one_tmul (ha : a ∈ 𝒜 d) (hd : 0 < d) (n : ℤ)
    (t : GradedModuleDegreeZeroLocalization 𝒜 (twistGrading (S := A) 𝒜 n) a) :
    chartTwistCompareEquiv 𝒜 S ha hd n
        ((1 : Away (grading 𝒜 S) ((1 : S) ⊗ₜ[R] a)) ⊗ₜ t) =
      twistAwayEquiv (grading 𝒜 S) (tmul_one_mem 𝒜 S ha) n (chartTwistMap 𝒜 S n t) := by
  let := isPushout_chart 𝒜 S ha
  have h := Algebra.IsPushout.cancelBaseChange_tmul R S (Away 𝒜 a)
    (Away (grading 𝒜 S) ((1 : S) ⊗ₜ[R] a))
    (GradedModuleDegreeZeroLocalization 𝒜 (twistGrading (S := A) 𝒜 n) a) t
  have h2 : chartTwistCompareEquiv 𝒜 S ha hd n
      ((1 : Away (grading 𝒜 S) ((1 : S) ⊗ₜ[R] a)) ⊗ₜ t) =
      chartTwistBaseChange 𝒜 S ha hd n
        ((1 : S) ⊗ₜ[R] twistAwayEquiv 𝒜 ha n t) := by
    show chartTwistBaseChange 𝒜 S ha hd n
        (TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl S S)
          ((twistAwayEquiv 𝒜 ha n).restrictScalars R)
          (Algebra.IsPushout.cancelBaseChange R S (Away 𝒜 a)
            (Away (grading 𝒜 S) ((1 : S) ⊗ₜ[R] a))
            (GradedModuleDegreeZeroLocalization 𝒜 (twistGrading (S := A) 𝒜 n) a)
            ((1 : Away (grading 𝒜 S) ((1 : S) ⊗ₜ[R] a)) ⊗ₜ t))) = _
    rw [h]
    rfl
  rw [h2, chartTwistBaseChange_one_tmul, LinearEquiv.symm_apply_apply]

/-- The chart comparison of a base change is semilinear over the base-changed chart ring on pure
tensors. The induction is over the presentation of that ring as `S ⊗_R 𝒜₍a₎`, which is
`Stacks.ProjBaseChange.isPushout_chart`. -/
theorem chartTwistCompareEquiv_tmul (ha : a ∈ 𝒜 d) (hd : 0 < d) (n : ℤ)
    (q : Away (grading 𝒜 S) ((1 : S) ⊗ₜ[R] a))
    (t : GradedModuleDegreeZeroLocalization 𝒜 (twistGrading (S := A) 𝒜 n) a) :
    chartTwistCompareEquiv 𝒜 S ha hd n (q ⊗ₜ t) =
      q • chartTwistCompareEquiv 𝒜 S ha hd n
        ((1 : Away (grading 𝒜 S) ((1 : S) ⊗ₜ[R] a)) ⊗ₜ t) := by
  let := isPushout_chart 𝒜 S ha
  induction q using (isPushout_chart 𝒜 S ha).out.inductionOn with
  | tmul p =>
      have h1 : algebraMap (Away 𝒜 a) (Away (grading 𝒜 S) ((1 : S) ⊗ₜ[R] a)) p ⊗ₜ[Away 𝒜 a] t =
          (1 : Away (grading 𝒜 S) ((1 : S) ⊗ₜ[R] a)) ⊗ₜ (p • t) := by
        rw [Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
      rw [show (IsScalarTower.toAlgHom R (Away 𝒜 a)
            (Away (grading 𝒜 S) ((1 : S) ⊗ₜ[R] a))).toLinearMap p =
          algebraMap (Away 𝒜 a) (Away (grading 𝒜 S) ((1 : S) ⊗ₜ[R] a)) p from rfl, h1,
        chartTwistCompareEquiv_one_tmul, chartTwistCompareEquiv_one_tmul,
        chartTwistMap_smul, _root_.map_smul]
      rfl
  | smul s q₀ ih => rw [← TensorProduct.smul_tmul', _root_.map_smul, ih, smul_assoc]
  | add q₁ q₂ ih₁ ih₂ => rw [TensorProduct.add_tmul, map_add, ih₁, ih₂, add_smul]

/-- **The coefficient extension of Tag 01MY's chart comparison is the chart comparison of the
base change.** -/
theorem twistAwayEquiv_twistDegreeZeroExtension (ha : a ∈ 𝒜 d) (hd : 0 < d) (n : ℤ)
    (x : TensorProduct (Away 𝒜 a) (Away (grading 𝒜 S) ((1 : S) ⊗ₜ[R] a))
      (GradedModuleDegreeZeroLocalization 𝒜 (twistGrading (S := A) 𝒜 n) a)) :
    twistAwayEquiv (grading 𝒜 S) (tmul_one_mem 𝒜 S ha) n
        (twistDegreeZeroExtension 𝒜 (grading 𝒜 S) (includeRight 𝒜 S) (f := a) n x) =
      chartTwistCompareEquiv 𝒜 S ha hd n x := by
  induction x using TensorProduct.induction_on with
  | zero =>
      refine Eq.trans (congrArg (twistAwayEquiv (grading 𝒜 S) (tmul_one_mem 𝒜 S ha) n)
        (map_zero (ModuleCat.Hom.hom (twistDegreeZeroExtension 𝒜 (grading 𝒜 S)
          (includeRight 𝒜 S) (f := a) n)))) ?_
      exact Eq.trans (map_zero _) (map_zero (chartTwistCompareEquiv 𝒜 S ha hd n)).symm
  | tmul q t =>
      have hq : q • ((1 : Away (grading 𝒜 S) ((1 : S) ⊗ₜ[R] a)) ⊗ₜ[Away 𝒜 a] t) =
          q ⊗ₜ[Away 𝒜 a] t := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      refine Eq.trans (congrArg (fun w => twistAwayEquiv (grading 𝒜 S) (tmul_one_mem 𝒜 S ha) n
        (twistDegreeZeroExtension 𝒜 (grading 𝒜 S) (includeRight 𝒜 S) (f := a) n w)) hq.symm) ?_
      refine Eq.trans (congrArg (twistAwayEquiv (grading 𝒜 S) (tmul_one_mem 𝒜 S ha) n)
        ((ModuleCat.Hom.hom (twistDegreeZeroExtension 𝒜 (grading 𝒜 S)
          (includeRight 𝒜 S) (f := a) n)).map_smul q _)) ?_
      refine Eq.trans (_root_.map_smul
        (twistAwayEquiv (grading 𝒜 S) (tmul_one_mem 𝒜 S ha) n) q _) ?_
      refine Eq.trans (congrArg (fun z => q • z)
        (congrArg (twistAwayEquiv (grading 𝒜 S) (tmul_one_mem 𝒜 S ha) n)
          (twistDegreeZeroExtension_tmul 𝒜 (grading 𝒜 S) (includeRight 𝒜 S) n t))) ?_
      refine Eq.trans (congrArg (fun z => q • z)
        (chartTwistCompareEquiv_one_tmul 𝒜 S ha hd n t).symm) ?_
      exact (chartTwistCompareEquiv_tmul 𝒜 S ha hd n q t).symm
  | add x y hx hy =>
      refine Eq.trans (congrArg (twistAwayEquiv (grading 𝒜 S) (tmul_one_mem 𝒜 S ha) n)
        (map_add (ModuleCat.Hom.hom (twistDegreeZeroExtension 𝒜 (grading 𝒜 S)
          (includeRight 𝒜 S) (f := a) n)) x y)) ?_
      refine Eq.trans (map_add _ _ _) ?_
      refine Eq.trans (congrArg₂ (· + ·) hx hy) ?_
      exact (map_add (chartTwistCompareEquiv 𝒜 S ha hd n) x y).symm

/-- **The coefficient extension of Tag 01MY's chart comparison is invertible for a graded base
change, at a homogeneous element of any positive degree.**

This is the step that fails for a general graded ring homomorphism above degree one, where
`Stacks.AlgebraicGeometry.TwistChartDegreeOne.isIso_of_tmul_eq_twistDegreeZeroMap` needs the
chart sections of the twist to be free of rank one. For a base change no freeness is needed: the
chart of the base change *is* the base change of the chart
(`Stacks.ProjBaseChange.isPushout_chart`) and the chart sections of the twist base-change along
it (`Stacks.ProjStandardOpenBaseChange.standardOpenBaseChange`), so the coefficient extension is
a base change of an identity. -/
theorem isIso_twistDegreeZeroExtension (ha : a ∈ 𝒜 d) (hd : 0 < d) (n : ℤ) :
    IsIso (twistDegreeZeroExtension 𝒜 (grading 𝒜 S) (includeRight 𝒜 S) (f := a) n) := by
  refine (ConcreteCategory.isIso_iff_bijective _).mpr ⟨fun x y hxy => ?_, fun z =>
    ⟨(chartTwistCompareEquiv 𝒜 S ha hd n).symm
      (twistAwayEquiv (grading 𝒜 S) (tmul_one_mem 𝒜 S ha) n z), ?_⟩⟩
  · refine (chartTwistCompareEquiv 𝒜 S ha hd n).injective ?_
    rw [← twistAwayEquiv_twistDegreeZeroExtension 𝒜 S ha hd n x,
      ← twistAwayEquiv_twistDegreeZeroExtension 𝒜 S ha hd n y, hxy]
  · refine (twistAwayEquiv (grading 𝒜 S) (tmul_one_mem 𝒜 S ha) n).injective ?_
    rw [twistAwayEquiv_twistDegreeZeroExtension 𝒜 S ha hd n, LinearEquiv.apply_symm_apply]

end ChartAlgebra

/-! ### Clause (3) of Tag 01N2 -/

section Global

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
  (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜] (S : Type u) [CommRing S] [Algebra R S]

/-- **Stacks Project, Tag 01N2, clause (3).** For a graded `R`-algebra `A` with grading `𝒜` and
an `R`-algebra `S`, the canonical comparison map `θ : r_ψ^* 𝒪_X(n) ⟶ 𝒪_Y(n)` of Tag 01MY for the
base-change homomorphism `ψ : 𝒜 → S ⊗[R] 𝒜` is an isomorphism, for every `n : ℤ`.

Here `X = Proj 𝒜`, `Y = Proj (S ⊗[R] 𝒜)` and `r_ψ = AlgebraicGeometry.Proj.map ψ`, which is
defined on all of `Y` by clause (1) of the tag,
`Stacks.AlgebraicGeometry.ProjShared.mapDomain_baseChange`.

Invertibility is local on `Y`, and the standard charts `D₊(ψ f)` with `f` homogeneous of positive
degree cover `Y` precisely because of clause (1); on such a chart the comparison is the
coefficient extension of the algebraic chart comparison
`Stacks.AlgebraicGeometry.TwistChartLocality.twistDegreeZeroMap`, and that is invertible by
`Stacks.ProjBaseChange.isIso_twistDegreeZeroExtension`. The degree-one hypothesis of
`Stacks.AlgebraicGeometry.TwistChartLocality.isIso_projTwistComparison` is therefore not needed
here. -/
theorem isIso_twistMap_includeRight (n : ℤ) :
    IsIso (Stacks.ProjTwistComparison.twistMap (includeRight 𝒜 S)
      (irrelevant_le_map 𝒜 S) n) :=
  isIso_projTwistComparison_of_forall_pullback_awayι_of_mapDomain_eq_top
    𝒜 (grading 𝒜 S) (includeRight 𝒜 S) (irrelevant_le_map 𝒜 S)
    (mapDomain_baseChange 𝒜 (includeRight 𝒜 S) fun _ => rfl) n fun _ hi _ hf =>
      isIso_pullback_awayι_map_twistMap_of_isIso_extension 𝒜 (grading 𝒜 S)
        (includeRight 𝒜 S) (irrelevant_le_map 𝒜 S) hi hf n
        (isIso_twistDegreeZeroExtension 𝒜 S hf hi n)

end Global

end Stacks.ProjBaseChange

end
