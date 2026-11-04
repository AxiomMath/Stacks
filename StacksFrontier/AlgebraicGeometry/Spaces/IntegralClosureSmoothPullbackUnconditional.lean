module

public import StacksFrontier.AlgebraicGeometry.Spaces.AlgebraPullbackChartSectionModule
public import StacksFrontier.AlgebraicGeometry.Spaces.AlgebraPullbackChartSections
public import StacksFrontier.AlgebraicGeometry.Spaces.AlgebraPullbackQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.IntegralClosureSmoothPullback
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The integral closure commutes with smooth pullback, with no further hypothesis

Let `f : Y ⟶ X` be a smooth morphism of algebraic spaces over `S` and let `A` be a quasi-coherent
sheaf of commutative `𝒪_X`-algebras, with integral closure `A' ⊆ A` of `𝒪_X`. Then the integral
closure of `𝒪_Y` in `f^*A` is `f^*A'` (Stacks 082E). The argument of
`StacksFrontier.AlgebraicGeometry.Spaces.IntegralClosureSmoothPullback` needs two instances of
Stacks 03GA for algebra sheaves: the affine-chart tensor presentation
`AlgebraicGeometry.Space.HasAffineTensorPresentation`, and quasi-coherence of `f^*A`. This file
proves the tensor presentation at the quasi-coherent algebra sheaves, which is where Descent,
Proposition 03DX(2) puts the hypothesis, and with it and the quasi-coherence of `f^*A` proves
Stacks 082E under its own hypotheses, as
`AlgebraicGeometry.Space.exists_iso_algebraPullback_integralClosureSheaf_unconditional`.

## Main definitions

* `AlgebraicGeometry.Space.HasAffineTensorPresentationOfQuasicoherent`: over every diagram of
  affine étale charts over `f` the sections of the pullback of a quasi-coherent algebra sheaf
  are the base change of its sections, naturally in a morphism of quasi-coherent algebra
  sheaves.
* `AlgebraicGeometry.Space.HasBijectiveAffineChartComparison`: the canonical comparison
  `AlgebraicGeometry.Space.algebraPullbackChartComparison` is bijective over every diagram of
  affine étale charts, at every quasi-coherent algebra sheaf.

## Main results

* `hasAffineTensorPresentationOfQuasicoherent_of_hasAffineTensorPresentation`: the presentation at
  every algebra sheaf restricts to the quasi-coherent ones.
* `hasAffineTensorPresentationOfQuasicoherent_of_hasBijectiveAffineChartComparison`: the tensor
  presentation at quasi-coherent algebra sheaves follows from bijectivity of the canonical
  comparison, its compatibility clause being the naturality of the comparison in the algebra sheaf.
* `AlgebraicGeometry.Space.hasBijectiveAffineChartComparison` and
  `AlgebraicGeometry.Space.hasAffineTensorPresentationOfQuasicoherent`: both hold for an arbitrary
  morphism of algebraic spaces.
* `AlgebraicGeometry.Space.algebraPullback_integralClosure_affine_range_unconditional`: over a
  diagram of affine étale charts over a smooth `f`, the sections of `f^*A'` are the integral
  closure of the chart ring of `Y` in the sections of `f^*A`.
* `AlgebraicGeometry.Space.exists_iso_algebraPullback_integralClosureSheaf_unconditional`:
  **Stacks 082E.** The integral closure of `𝒪_Y` in `f^*A` is `f^*A'`, for `f` smooth and `A`
  quasi-coherent.

## Implementation notes

`AlgebraicGeometry.Space.HasAffineTensorPresentation` quantifies over every algebra sheaf, which is
more than Stacks 03DX gives: the sections of a pullback are a base change because a quasi-coherent
module has a presentation over an affine chart. Here the presentation is asked for at
quasi-coherent algebra sheaves only. It applies to the inclusion `A' ⟶ A` because `A'` is
quasi-coherent by Stacks 0820,
`AlgebraicGeometry.Space.AlgebraSheaf.isQuasicoherent_integralClosureSheaf`.

Quasi-coherence of `f^*A` is `AlgebraicGeometry.Space.algebraPullback_isQuasicoherent`: Stacks 03GA
for modules,
`AlgebraicGeometry.Space.isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite`, read
through the isomorphism `AlgebraicGeometry.Space.underlyingModuleAlgebraPullbackModulePullbackIso`
of the `𝒪_Y`-module underlying `f^*A` with the module pullback of the module underlying `A`.

The tensor presentation reduces to bijectivity of one canonical `𝒪_Y(d.U)`-algebra homomorphism
`AlgebraicGeometry.Space.algebraPullbackChartComparison`
`𝒪_Y(d.U) ⊗_{𝒪_X(d.V)} A(d.V) ⟶ (f^*A)(d.U)`, the lift of the structure map `pushout.inr` and the
chart section `AlgebraicGeometry.Space.algebraPullbackChartSection`. Its naturality in `A`,
`AlgebraicGeometry.Space.algebraPullbackChartComparison_naturality`, is the compatibility clause of
the presentation, which no non-canonical family of equivalences need satisfy.
`HasAffineTensorPresentationOfQuasicoherent` is not defined as this bijectivity, which is strictly
stronger than the existence of compatible equivalences; the reduction is the implication
`hasAffineTensorPresentationOfQuasicoherent_of_hasBijectiveAffineChartComparison`.

Bijectivity is `AlgebraicGeometry.Space.bijective_algebraPullbackChartComparison_affine`. It
transports the bijectivity of the module comparison
`AlgebraicGeometry.Space.modulePullbackChartBaseChange` at a quasi-coherent module,
`AlgebraicGeometry.Space.bijective_modulePullbackChartBaseChange_of_isQuasicoherentOnSite`
(Stacks 083K), along the isomorphism `AlgebraicGeometry.Space.algebraPullbackModuleIso` of the
module underlying `f^*A` with the module pullback. That isomorphism is the adjunct across Stacks
03D7 of the unit of Stacks 03D3 composed with `pushout.inl`, and it carries
`AlgebraicGeometry.Space.modulePullbackChartSection` to
`AlgebraicGeometry.Space.algebraPullbackChartSection`.

## References

* [Stacks Project, Tag 082E](https://stacks.math.columbia.edu/tag/082E)
* [Stacks Project, Tag 0820](https://stacks.math.columbia.edu/tag/0820)
* [Stacks Project, Tag 03GA](https://stacks.math.columbia.edu/tag/03GA)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 083K](https://stacks.math.columbia.edu/tag/083K)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TensorProduct

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : AlgebraicSpaces B S hS}

/-! ### The affine-chart tensor presentation at quasi-coherent algebra sheaves -/

/-- **The affine-chart tensor presentation of the algebra pullback along `f`, at quasi-coherent
algebra sheaves.**  Over every diagram of affine étale charts over `f`, the sections of `f^*A`
over the chart of `Y` are the base change `𝒪_Y(U) ⊗_{𝒪_X(V)} A(V)` of the sections of `A` over
the chart of `X`, compatibly with a morphism `A ⟶ C` of quasi-coherent algebra sheaves on `X`.

This is `AlgebraicGeometry.Space.HasAffineTensorPresentation` with both algebra sheaves required
to be quasi-coherent. -/
def HasAffineTensorPresentationOfQuasicoherent (f : Y ⟶ X) : Prop :=
  ∀ {A C : AlgebraSheaf.{u, u} B S hS X.1 X.2} (φ : A ⟶ C),
    A.IsQuasicoherent → C.IsQuasicoherent →
    ∀ d : ChartDiagram B S hS Y.1 X.1 f.hom,
    IsAffine ((SmallEtale.toOver B S hS Y.1 ⋙ BigFppfOver.toScheme B S hS).obj d.U) →
    IsAffine ((SmallEtale.toOver B S hS X.1 ⋙ BigFppfOver.toScheme B S hS).obj d.V) →
      let _ := chartDiagramAlgebra B S hS f d
      let _ := chartSectionsAlgebra A d.V
      let _ := chartSectionsAlgebra C d.V
      let _ := chartSectionsAlgebra ((algebraPullback B S hS f).obj A) d.U
      let _ := chartSectionsAlgebra ((algebraPullback B S hS f).obj C) d.U
      ∃ (eA : TensorProduct (chartRing B S hS X.1 X.2 d.V) (chartRing B S hS Y.1 Y.2 d.U)
                (A.right.obj.obj (op d.V)) ≃ₐ[chartRing B S hS Y.1 Y.2 d.U]
              ((algebraPullback B S hS f).obj A).right.obj.obj (op d.U))
        (eC : TensorProduct (chartRing B S hS X.1 X.2 d.V) (chartRing B S hS Y.1 Y.2 d.U)
                (C.right.obj.obj (op d.V)) ≃ₐ[chartRing B S hS Y.1 Y.2 d.U]
              ((algebraPullback B S hS f).obj C).right.obj.obj (op d.U)),
        ∀ a, (((algebraPullback B S hS f).map φ).right.hom.app (op d.U)).hom (eA (1 ⊗ₜ a)) =
          eC (1 ⊗ₜ ((φ.right.hom.app (op d.V)).hom a))

/-- The tensor presentation at every algebra sheaf restricts to the one at quasi-coherent
algebra sheaves. -/
theorem hasAffineTensorPresentationOfQuasicoherent_of_hasAffineTensorPresentation {f : Y ⟶ X}
    (h : HasAffineTensorPresentation B S hS f) :
    HasAffineTensorPresentationOfQuasicoherent B S hS f :=
  fun φ _ _ d hU hV ↦ h φ d hU hV

/-- **Bijectivity of the canonical comparison on the sections over a diagram of affine étale
charts.**  Over every such diagram the canonical `𝒪_Y(d.U)`-algebra homomorphism
`AlgebraicGeometry.Space.algebraPullbackChartComparison`
`𝒪_Y(d.U) ⊗_{𝒪_X(d.V)} A(d.V) ⟶ (f^*A)(d.U)` is bijective, for every quasi-coherent algebra
sheaf `A`. -/
def HasBijectiveAffineChartComparison (f : Y ⟶ X) : Prop :=
  ∀ (A : AlgebraSheaf.{u, u} B S hS X.1 X.2), A.IsQuasicoherent →
    ∀ d : ChartDiagram B S hS Y.1 X.1 f.hom,
    IsAffine ((SmallEtale.toOver B S hS Y.1 ⋙ BigFppfOver.toScheme B S hS).obj d.U) →
    IsAffine ((SmallEtale.toOver B S hS X.1 ⋙ BigFppfOver.toScheme B S hS).obj d.V) →
      let _ := chartDiagramAlgebra B S hS f d
      let _ := chartSectionsAlgebra A d.V
      let _ := chartSectionsAlgebra ((algebraPullback B S hS f).obj A) d.U
      Function.Bijective (algebraPullbackChartComparison B S hS f A d)

/-- **The tensor presentation of a quasi-coherent algebra pullback reduces to the bijectivity of
one canonical map.**  Given that `AlgebraicGeometry.Space.algebraPullbackChartComparison` is
bijective over every diagram of affine étale charts, the whole of
`AlgebraicGeometry.Space.HasAffineTensorPresentationOfQuasicoherent` follows: the two algebra
equivalences are that one map, and the compatibility clause is its naturality in the algebra
sheaf, `AlgebraicGeometry.Space.algebraPullbackChartComparison_naturality`. -/
theorem hasAffineTensorPresentationOfQuasicoherent_of_hasBijectiveAffineChartComparison
    (f : Y ⟶ X) (h : HasBijectiveAffineChartComparison B S hS f) :
    HasAffineTensorPresentationOfQuasicoherent B S hS f := by
  intro A C φ hA hC d hU hV
  let _ := chartDiagramAlgebra B S hS f d
  let _ := chartSectionsAlgebra A d.V
  let _ := chartSectionsAlgebra C d.V
  let _ := chartSectionsAlgebra ((algebraPullback B S hS f).obj A) d.U
  let _ := chartSectionsAlgebra ((algebraPullback B S hS f).obj C) d.U
  exact ⟨AlgEquiv.ofBijective (algebraPullbackChartComparison B S hS f A d) (h A hA d hU hV),
    AlgEquiv.ofBijective (algebraPullbackChartComparison B S hS f C d) (h C hC d hU hV),
    fun a => algebraPullbackChartComparison_naturality B S hS f φ d a⟩

/-- **Bijectivity of the canonical comparison over every diagram of affine étale charts holds**,
for an arbitrary morphism of algebraic spaces and every quasi-coherent algebra sheaf. -/
theorem hasBijectiveAffineChartComparison (f : Y ⟶ X) :
    HasBijectiveAffineChartComparison B S hS f :=
  fun A hA d hU hV ↦ bijective_algebraPullbackChartComparison_affine B S hS f A hA d hU hV

/-- **The affine-chart tensor presentation of a quasi-coherent algebra pullback holds**, for an
arbitrary morphism of algebraic spaces: Stacks 03GA for algebra sheaves, on the sections over a
diagram of affine étale charts, compatibility clause and all. -/
theorem hasAffineTensorPresentationOfQuasicoherent (f : Y ⟶ X) :
    HasAffineTensorPresentationOfQuasicoherent B S hS f :=
  hasAffineTensorPresentationOfQuasicoherent_of_hasBijectiveAffineChartComparison B S hS f
    (hasBijectiveAffineChartComparison B S hS f)

/-! ### Stacks 082E with no further hypothesis -/

/-- **Over a diagram of affine étale charts over a smooth morphism, the pullback of the
integral-closure inclusion is injective with image the integral closure**, for a quasi-coherent
algebra sheaf `A`. -/
theorem algebraPullback_integralClosure_affine_range_unconditional (f : Y ⟶ X)
    (hf : IsSmooth B S hS f.hom)
    (A : AlgebraSheaf.{u, u} B S hS X.1 X.2) (hA : A.IsQuasicoherent)
    (d : ChartDiagram B S hS Y.1 X.1 f.hom)
    (hU : IsAffine ((SmallEtale.toOver B S hS Y.1 ⋙ BigFppfOver.toScheme B S hS).obj d.U))
    (hV : IsAffine ((SmallEtale.toOver B S hS X.1 ⋙ BigFppfOver.toScheme B S hS).obj d.V)) :
    letI := chartSectionsAlgebra ((algebraPullback B S hS f).obj A) d.U
    Function.Injective ((((algebraPullback B S hS f).map
          (AlgebraSheaf.integralClosureInclusion A)).right.hom.app (op d.U)).hom) ∧
      Set.range ((((algebraPullback B S hS f).map
          (AlgebraSheaf.integralClosureInclusion A)).right.hom.app (op d.U)).hom) =
        (integralClosure (chartRing B S hS Y.1 Y.2 d.U)
          (((algebraPullback B S hS f).obj A).right.obj.obj (op d.U)) : Set _) := by
  let _ := chartDiagramAlgebra B S hS f d
  let _ := chartSectionsAlgebra A d.V
  let _ := chartSectionsAlgebra (AlgebraSheaf.integralClosureSheaf A) d.V
  let _ := chartSectionsAlgebra ((algebraPullback B S hS f).obj A) d.U
  let _ := chartSectionsAlgebra
    ((algebraPullback B S hS f).obj (AlgebraSheaf.integralClosureSheaf A)) d.U
  have _ := smooth_chartDiagramAlgebra B S hS f hf d hU hV
  obtain ⟨eD, eA, he⟩ := hasAffineTensorPresentationOfQuasicoherent B S hS f
    (AlgebraSheaf.integralClosureInclusion A)
    (AlgebraSheaf.isQuasicoherent_integralClosureSheaf A hA) hA d hU hV
  have _ := AlgebraSheaf.mono_integralClosureInclusion_right A
  let iR : (AlgebraSheaf.integralClosureSheaf A).right.obj.obj (op d.V)
      →ₐ[chartRing B S hS X.1 X.2 d.V] A.right.obj.obj (op d.V) :=
    { __ := (((AlgebraSheaf.integralClosureInclusion A).right.hom.app (op d.V)).hom)
      commutes' := (AlgebraSheaf.integralClosureInclusion A).comm (op d.V) }
  let jT : ((algebraPullback B S hS f).obj
        (AlgebraSheaf.integralClosureSheaf A)).right.obj.obj (op d.U)
      →ₐ[chartRing B S hS Y.1 Y.2 d.U]
        ((algebraPullback B S hS f).obj A).right.obj.obj (op d.U) :=
    { __ := ((((algebraPullback B S hS f).map
                (AlgebraSheaf.integralClosureInclusion A)).right.hom.app (op d.U)).hom)
      commutes' := ((algebraPullback B S hS f).map
        (AlgebraSheaf.integralClosureInclusion A)).comm (op d.U) }
  have hr : Set.range iR =
      (integralClosure (chartRing B S hS X.1 X.2 d.V) (A.right.obj.obj (op d.V)) : Set _) :=
    AlgebraSheaf.range_integralClosureInclusion_app_eq_integralClosure' A hA d.V hV
  exact Stacks.injective_and_range_eq_integralClosure_of_tensor iR
    (Stacks.Sites.injective_app_of_mono _ (AlgebraSheaf.integralClosureInclusion A).right _)
    hr eD eA jT he

/-- **Stacks 082E.** Let `f : Y ⟶ X` be a smooth morphism of algebraic spaces over `S` and let
`A` be a quasi-coherent sheaf of commutative `𝒪_X`-algebras. The integral closure of `𝒪_Y` in
`f^*A` is `f^*A'`, where `A' ⊆ A` is the integral closure of `𝒪_X` in `A`: there is an
isomorphism `f^*A' ≅ (f^*A)'` of algebra sheaves on `Y` whose composite with the inclusion of
`(f^*A)'` into `f^*A` is the pullback of the inclusion of `A'` into `A`. -/
@[stacks 082E, sga "3 X 8.9" "partial"]
theorem exists_iso_algebraPullback_integralClosureSheaf_unconditional (f : Y ⟶ X)
    (hf : IsSmooth B S hS f.hom)
    (A : AlgebraSheaf.{u, u} B S hS X.1 X.2) (hA : A.IsQuasicoherent) :
    ∃ e : (algebraPullback B S hS f).obj (AlgebraSheaf.integralClosureSheaf A) ≅
        AlgebraSheaf.integralClosureSheaf ((algebraPullback B S hS f).obj A),
      e.hom ≫ AlgebraSheaf.integralClosureInclusion ((algebraPullback B S hS f).obj A) =
        (algebraPullback B S hS f).map (AlgebraSheaf.integralClosureInclusion A) := by
  have hfA : ((algebraPullback B S hS f).obj A).IsQuasicoherent :=
    algebraPullback_isQuasicoherent B S hS f A hA
  set j := (algebraPullback B S hS f).map (AlgebraSheaf.integralClosureInclusion A)
  set k := AlgebraSheaf.integralClosureInclusion ((algebraPullback B S hS f).obj A)
  have hlocal : ∀ U : SmallEtale B S hS Y.1, ∃ R : Presieve U,
      Sieve.generate R ∈ SmallEtale.topology B S hS Y.1 U ∧
        ∀ (V : SmallEtale B S hS Y.1) (g : V ⟶ U), R g →
          Function.Injective ((j.right.hom.app (op V)).hom) ∧
            Set.range ((j.right.hom.app (op V)).hom) =
              Set.range ((k.right.hom.app (op V)).hom) := by
    intro U
    refine ⟨fun W _ => HasAffineChartDiagram B S hS f W, ?_, ?_⟩
    · exact mem_topology_of_hasAffineChartDiagram B S hS f U _ fun {W} a hW =>
        ⟨W, 𝟙 W, a, hW, Category.id_comp a⟩
    · rintro V g ⟨hVaff, V', q, hcomm, hV'aff⟩
      let d : ChartDiagram B S hS Y.1 X.1 f.hom := ⟨V, V', q, hcomm.symm⟩
      have hdU : IsAffine
          ((SmallEtale.toOver B S hS Y.1 ⋙ BigFppfOver.toScheme B S hS).obj d.U) := hVaff
      have hdV : IsAffine
          ((SmallEtale.toOver B S hS X.1 ⋙ BigFppfOver.toScheme B S hS).obj d.V) := hV'aff
      obtain ⟨hinj, hrange⟩ :=
        algebraPullback_integralClosure_affine_range_unconditional B S hS f hf A hA d hdU hdV
      exact ⟨hinj, hrange.trans (AlgebraSheaf.range_integralClosureInclusion_app_eq_integralClosure'
        ((algebraPullback B S hS f).obj A) hfA d.U hdU).symm⟩
  have hjmono : Mono j.right :=
    Stacks.Sites.mono_of_locallyInjective_app _ j.right fun U => by
      obtain ⟨R, hR, h⟩ := hlocal U
      exact ⟨R, hR, fun V g hg => (h V g hg).1⟩
  have hkmono : Mono k.right :=
    AlgebraSheaf.mono_integralClosureInclusion_right ((algebraPullback B S hS f).obj A)
  exact AlgebraSheaf.exists_iso_of_locally_range_eq j k fun U => by
    obtain ⟨R, hR, h⟩ := hlocal U
    exact ⟨R, hR, fun V g hg => (h V g hg).2⟩

end AlgebraicGeometry.Space
