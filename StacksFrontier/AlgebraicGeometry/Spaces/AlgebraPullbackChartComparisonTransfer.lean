module

public import StacksFrontier.AlgebraicGeometry.Spaces.AlgebraPullbackChartSections
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartDiagramBaseChangeComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleSourceModuleFMapCompDischarge

/-!
# The algebra comparison over a chart diagram is the module comparison

Let `f : Y ⟶ X` be a morphism of algebraic spaces over a scheme `S` contained in a big fppf
site `B`, let `A` be a sheaf of commutative `𝒪_X`-algebras on the small étale site of `X` and
let `d` be a diagram of étale scheme charts over `f`.  Two canonical comparisons over `d` have
the same source `𝒪_Y(d.U) ⊗_{𝒪_X(d.V)} A(d.V)`:

* `AlgebraicGeometry.Space.algebraPullbackChartComparison`, the `𝒪_Y(d.U)`-algebra homomorphism
  into `(f^*A)(d.U)`, and
* `AlgebraicGeometry.Space.modulePullbackChartBaseChange` at the `𝒪_X`-module underlying `A`,
  the `𝒪_Y(d.U)`-linear map into `(f^*M)(d.U)`.

This file records that an isomorphism of the two targets carrying the module chart section to
the algebra chart section carries the second comparison to the first, and that the bijectivity
of `AlgebraicGeometry.Space.algebraPullbackChartComparison` therefore follows from
`AlgebraicGeometry.Space.bijective_modulePullbackChartBaseChange_of_isQuasicoherentOnSite`,
which assumes nothing beyond quasi-coherence of the module and affineness of the two charts.

So the sections half of Stacks 03GA for *algebra* sheaves is reduced to a single
identification: that some isomorphism of the `𝒪_Y`-module underlying `f^*A` with the module
pullback of the module underlying `A` carries
`AlgebraicGeometry.Space.modulePullbackChartSection` to
`AlgebraicGeometry.Space.algebraPullbackChartSection`.

## Main results

* `AlgebraicGeometry.Space.algebraPullbackChartComparison_eq_val_app_comp`: **the algebra
  comparison is the module comparison followed by the isomorphism.**  Both sides are additive
  and agree on `c ⊗ₜ a`, where each is `c` times a chart section.
* `AlgebraicGeometry.Space.bijective_algebraPullbackChartComparison_of_iso`: **granted such an
  isomorphism, the algebra comparison over a diagram of affine étale charts is bijective.**

## Implementation notes

Nothing here compares the two *targets* by hand: the identification is taken as data, and the
only thing asked of it is its value on a chart section.  That is deliberate — the construction
of such an isomorphism is a different matter, carried out in
`StacksFrontier/AlgebraicGeometry/Spaces/AlgebraPullbackChartSectionModule.lean`, and the
reduction below is independent of how it is built.

The two sources are the same type, not merely isomorphic ones: the tensor product is formed
over the same pair of chart rings, the sections of `A` over `d.V` and the sections of the module
underlying `A` over `d.V` are the same term, and the two `𝒪_X(d.V)`-module structures on them —
`AlgebraicGeometry.Space.chartSectionsAlgebra` and the one
`AlgebraicGeometry.Space.AlgebraSheaf.underlyingModule` carries — are the same structure.  The
same holds of the two `𝒪_Y(d.U)`-module structures on the sections of `f^*A`.  This is the
coincidence `AlgebraicGeometry.Space.chartSectionsBaseChangeAlgHom_apply` of
`StacksFrontier/AlgebraicGeometry/Spaces/IntegralClosureQuasicoherent.lean` already relies on, for
a morphism of charts of one space rather than for a chart diagram over `f`.

Nothing here raises a compiler limit or disables a linter.

## References

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

/-- Applying a morphism of modules to a section is applying its linear map of sections.  Both
spellings occur in this development and the bridge between them is taken once, here. -/
theorem val_app_eq_hom {Z : AlgebraicSpaces B S hS}
    {M N : Modules.{u, u} B S hS Z.1 Z.2} (ψ : M ⟶ N)
    (W : (SmallEtale B S hS Z.1)ᵒᵖ) (x : M.val.obj W) :
    ψ.val.app W x = (ψ.val.app W).hom x :=
  rfl

/-- **The canonical algebra comparison over a chart diagram is the canonical module comparison
of the underlying module, read through an isomorphism of the two targets which carries the
module chart section to the algebra chart section.**

Both sides are additive, so it is enough to check them on `c ⊗ₜ a`:  there the algebra
comparison is `c` times the algebra chart section of `a`, by
`CategoryTheory.Limits`-free evaluation of `Algebra.TensorProduct.lift`, and the module
comparison is `c` times the module chart section of `a` by
`AlgebraicGeometry.Space.modulePullbackChartBaseChange_tmul`; the isomorphism is
`𝒪_Y(d.U)`-linear, so it carries one to the other. -/
theorem algebraPullbackChartComparison_eq_val_app_comp (f : Y ⟶ X)
    (A : AlgebraSheaf.{u, u} B S hS X.1 X.2) (d : ChartDiagram B S hS Y.1 X.1 f.hom)
    (Ψ : (modulePullback B S hS f).obj (AlgebraSheaf.underlyingModule A) ⟶
      AlgebraSheaf.underlyingModule ((algebraPullback B S hS f).obj A))
    (hΨ : ∀ a : A.right.obj.obj (op d.V),
      Ψ.val.app (op d.U)
          (modulePullbackChartSection B S hS f (AlgebraSheaf.underlyingModule A) d a) =
        algebraPullbackChartSection B S hS f A d a) :
    letI := chartDiagramAlgebra B S hS f d
    letI := chartSectionsAlgebra A d.V
    letI := chartSectionsAlgebra ((algebraPullback B S hS f).obj A) d.U
    ∀ z : TensorProduct (chartRing B S hS X.1 X.2 d.V) (chartRing B S hS Y.1 Y.2 d.U)
        (A.right.obj.obj (op d.V)),
      algebraPullbackChartComparison B S hS f A d z =
        Ψ.val.app (op d.U)
          (modulePullbackChartBaseChange B S hS f (AlgebraSheaf.underlyingModule A) d z) := by
  let _ := chartDiagramAlgebra B S hS f d
  let _ := chartSectionsAlgebra A d.V
  let _ := chartSectionsAlgebra ((algebraPullback B S hS f).obj A) d.U
  intro z
  induction z using TensorProduct.induction_on with
  | zero =>
      exact (map_zero _).trans ((map_zero (Ψ.val.app (op d.U)).hom).symm.trans
        (congrArg _ (map_zero (modulePullbackChartBaseChange B S hS f
          (AlgebraSheaf.underlyingModule A) d)).symm))
  | tmul c a =>
      refine (Eq.trans (congrArg (fun y ↦ c • y) (hΨ a).symm) ?_ :)
      exact ((Ψ.val.app (op d.U)).hom.map_smul c _).symm.trans
        (congrArg _ (modulePullbackChartBaseChange_tmul B S hS f
          (AlgebraSheaf.underlyingModule A) d c a).symm)
  | add z w hz hw =>
      exact (map_add _ z w).trans ((congrArg₂ (· + ·) hz hw).trans
        (((Ψ.val.app (op d.U)).hom.map_add _ _).symm.trans
          (congrArg _ (map_add (modulePullbackChartBaseChange B S hS f
            (AlgebraSheaf.underlyingModule A) d) z w).symm)))

/-- **Granted an isomorphism of the `𝒪_Y`-module underlying `f^*A` with the module pullback of
the module underlying `A` which carries the module chart section to the algebra chart section,
the canonical algebra comparison over a diagram of affine étale charts is bijective.**

The algebra comparison is the module comparison followed by that isomorphism on sections, by
`AlgebraicGeometry.Space.algebraPullbackChartComparison_eq_val_app_comp`; the module comparison
is bijective by
`AlgebraicGeometry.Space.bijective_modulePullbackChartBaseChange_of_isQuasicoherentOnSite`, which
needs only quasi-coherence of the module — and quasi-coherence of an algebra sheaf *is*
quasi-coherence of its underlying module — and affineness of the two charts; and a component of
an isomorphism of modules is bijective on sections. -/
theorem bijective_algebraPullbackChartComparison_of_iso (f : Y ⟶ X)
    (A : AlgebraSheaf.{u, u} B S hS X.1 X.2) (hA : A.IsQuasicoherent)
    (d : ChartDiagram B S hS Y.1 X.1 f.hom)
    (hU : IsAffine ((SmallEtale.toOver B S hS Y.1 ⋙ BigFppfOver.toScheme B S hS).obj d.U))
    (hV : IsAffine ((SmallEtale.toOver B S hS X.1 ⋙ BigFppfOver.toScheme B S hS).obj d.V))
    (Ψ : (modulePullback B S hS f).obj (AlgebraSheaf.underlyingModule A) ≅
      AlgebraSheaf.underlyingModule ((algebraPullback B S hS f).obj A))
    (hΨ : ∀ a : A.right.obj.obj (op d.V),
      Ψ.hom.val.app (op d.U)
          (modulePullbackChartSection B S hS f (AlgebraSheaf.underlyingModule A) d a) =
        algebraPullbackChartSection B S hS f A d a) :
    letI := chartDiagramAlgebra B S hS f d
    letI := chartSectionsAlgebra A d.V
    letI := chartSectionsAlgebra ((algebraPullback B S hS f).obj A) d.U
    Function.Bijective (algebraPullbackChartComparison B S hS f A d) := by
  let _ := chartDiagramAlgebra B S hS f d
  let _ := chartSectionsAlgebra A d.V
  let _ := chartSectionsAlgebra ((algebraPullback B S hS f).obj A) d.U
  have hcomp : ⇑(algebraPullbackChartComparison B S hS f A d) =
      fun z ↦ Ψ.hom.val.app (op d.U)
        (modulePullbackChartBaseChange B S hS f (AlgebraSheaf.underlyingModule A) d z) :=
    funext (algebraPullbackChartComparison_eq_val_app_comp B S hS f A d Ψ.hom hΨ)
  rw [hcomp]
  exact (SheafOfModules.bijective_iso_hom_val_app Ψ (op d.U)).comp
    (bijective_modulePullbackChartBaseChange_of_isQuasicoherentOnSite B S hS f
      (AlgebraSheaf.underlyingModule A) hA d hU hV)

end AlgebraicGeometry.Space

end
