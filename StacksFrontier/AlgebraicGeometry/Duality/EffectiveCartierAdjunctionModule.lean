module

public import StacksFrontier.Algebra.Homology.DerivedCategory.SingleDegree
public import StacksFrontier.AlgebraicGeometry.Duality.EffectiveCartierDerivedSheafHomTensor
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.DegreeZeroTensorProduct
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.ClosedEmbeddingProjectionFormulaStalks

/-!
# The adjunction formula of an effective Cartier divisor, at the level of modules

Let `X` be a scheme, `D ⊆ X` an effective Cartier divisor with closed immersion `i : D ⟶ X`,
and `𝒩 = i^* 𝒪_X(D)` its normal sheaf. For an *arbitrary* `𝒪_X`-module `M`, write `a(-)` for
the right adjoint of derived pushforward of
[Stacks, Tag 0A76](https://stacks.math.columbia.edu/tag/0A76) — derived sheaf Hom with exact
support, `R ℰom(𝒪_D, -)`. This file proves

`H¹(a(M[0])) ≅ 𝒩 ⊗_{𝒪_D} i^* M` in `Mod(𝒪_D)`,

with **no hypothesis on `M`**: no torsion-freeness, no coherence, no invertibility. It is the
module-level content of [Stacks, Tag 0AA4] — the adjunction formula — read in the single degree
where the source's `Li^*M ⊗^L 𝒩[-1]` is concentrated when `M` is a module.

## Main results

* `Stacks.Divisors.nonempty_homologyOne_pushforward_iso`:
  `H¹(Ri_* a(M[0])) ≅ M ⊗_{𝒪_X} i_* 𝒩`.
* `Stacks.Divisors.nonempty_tensor_pushforward_iso`:
  `M ⊗_{𝒪_X} i_* 𝒩 ≅ i_*(𝒩 ⊗_{𝒪_D} i^* M)`, the projection formula.
* `Stacks.Divisors.nonempty_homologyOne_derivedSheafHomExactSupport_iso`:
  `H¹(a(M[0])) ≅ 𝒩 ⊗_{𝒪_D} i^* M`.

## The proof

`Stacks.Divisors.pushforwardDerivedSheafHomExactSupportTensorIso` is the computation
`Ri_* a(K) ≅ K ⊗^L_{𝒪_X} (i_* 𝒩)[-1]` of [Stacks, Tag 0AA4] for every `K`, proved with no
hypothesis. At `K = M[0]` the right-hand side has `H¹` the ordinary tensor product
`M ⊗_{𝒪_X} i_* 𝒩`, by
`Stacks.SheafOfModules.DerivedTensorProduct.nonempty_homologyOneTensorSingleOneIso`: the
derived tensor product of two modules has its ordinary tensor product in the top degree, which
is right exactness of the tensor product and needs no flatness. The ordinary projection formula
for a closed embedding,
`Stacks.ClosedEmbeddingProjectionFormula.projectionFormulaIso` ([Stacks, Tag 0B55] step 1,
again with no hypothesis), rewrites that as `i_*(𝒩 ⊗_{𝒪_D} i^* M)`.

The descent from `X` to `D` is then available because both sides are *modules*: `i_*` is exact,
so it commutes with the cohomology of the derived category
(`CategoryTheory.Functor.mapDerivedCategoryHomologyFunctorIso`), turning the left-hand side
into `i_*(H¹(a(M[0])))`; and `i_*` is fully faithful on modules ([Stacks, Tag 08KS]), so
`CategoryTheory.Functor.preimageIso` descends the isomorphism. This is the step that is
unavailable for a general `K`, where neither side is concentrated in a single degree — see the
module documentation of
`StacksFrontier.AlgebraicGeometry.Duality.EffectiveCartierDerivedSheafHomTensor`.

At `M = 𝒪_X` the conclusion is [Stacks, Tag 0B4B] in degree one,
`Stacks.Divisors.derivedSheafHomExactSupportIsoNormalShift`, which is proved separately and
not used here.

## References

* [Stacks Project, Tag 0AA4](https://stacks.math.columbia.edu/tag/0AA4)
* [Stacks Project, Tag 0A76](https://stacks.math.columbia.edu/tag/0A76)
* [Stacks Project, Tag 0B4B](https://stacks.math.columbia.edu/tag/0B4B)
* [Stacks Project, Tag 0B55](https://stacks.math.columbia.edu/tag/0B55)
* [Stacks Project, Tag 08KS](https://stacks.math.columbia.edu/tag/08KS)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory RingedSpaceModuleAdjunction
open Stacks.ProjectionFormula

attribute [local instance 10000] HasDerivedCategory.standard

universe u

namespace Stacks.Divisors

variable {X : Scheme.{u}} (D : X.IdealSheafData) [IsEffectiveCartierDivisor D]

/-- **`H¹(Ri_* a(M[0])) ≅ M ⊗_{𝒪_X} i_* 𝒩`.** The computation
`Stacks.Divisors.pushforwardDerivedSheafHomExactSupportTensorIso` of [Stacks, Tag 0AA4] at
`K = M[0]`, followed by the identification of the top cohomology of a derived tensor product of
two modules with their ordinary tensor product. -/
theorem nonempty_homologyOne_pushforward_iso (M : X.Modules) :
    Nonempty ((DerivedCategory.homologyFunctor X.Modules 1).obj
        ((modulePushforward (closedQuotient D).i).mapDerivedCategory.obj
          ((closedQuotient D).derivedSheafHomExactSupport.obj
            ((DerivedCategory.singleFunctor X.Modules 0).obj M))) ≅
      ((Stacks.SheafOfModules.Tensor.sheafTensor
          (Stacks.SheafOfModules.ringedSite X.sheaf).O).obj M).obj
        (normalShortComplex D).X₃) := by
  obtain ⟨e⟩ := Stacks.SheafOfModules.DerivedTensorProduct.nonempty_homologyOneTensorSingleOneIso
    (Stacks.SheafOfModules.canonicalDerivedTensorProduct
      (Stacks.SheafOfModules.ringedSite X.sheaf)) M (normalShortComplex D).X₃
  exact ⟨(DerivedCategory.homologyFunctor X.Modules 1).mapIso
    (pushforwardDerivedSheafHomExactSupportTensorIso D
      ((DerivedCategory.singleFunctor X.Modules 0).obj M)) ≪≫ e⟩

/-- **`M ⊗_{𝒪_X} i_* 𝒩 ≅ i_*(𝒩 ⊗_{𝒪_D} i^* M)`.** The symmetry of the tensor product followed
by the ordinary projection formula for the closed embedding `i`, which is step 1 of
[Stacks, Tag 0B55] and carries no hypothesis beyond closedness. -/
theorem nonempty_tensor_pushforward_iso (M : X.Modules) :
    Nonempty (((Stacks.SheafOfModules.Tensor.sheafTensor
          (Stacks.SheafOfModules.ringedSite X.sheaf).O).obj M).obj
        (normalShortComplex D).X₃ ≅
      (modulePushforward (closedQuotient D).i).obj
        (((Stacks.SheafOfModules.Tensor.sheafTensor
            (Stacks.SheafOfModules.ringedSite D.subscheme.sheaf).O).obj
          ((Scheme.Modules.pullback D.subschemeι).obj (divisorSheaf D))).obj
          ((Scheme.Modules.pullback D.subschemeι).obj M))) := by
  refine ⟨((Stacks.SheafOfModules.Tensor.sheafTensorBraiding
      (Stacks.SheafOfModules.ringedSite X.sheaf).O).app M).app
        (normalShortComplex D).X₃ ≪≫ ?_⟩
  exact Stacks.ClosedEmbeddingProjectionFormula.projectionFormulaIso
    D.subschemeι.toLRSHom.toShHom
    ((Scheme.Modules.pullback D.subschemeι).obj (divisorSheaf D)) M
    D.subschemeι.isClosedEmbedding

/-- **The adjunction formula of an effective Cartier divisor at the level of modules.** For
every `𝒪_X`-module `M`,

`H¹(R ℰom(𝒪_D, M[0])) ≅ 𝒩 ⊗_{𝒪_D} i^* M`,

where `R ℰom(𝒪_D, -)` is the right adjoint of derived pushforward of [Stacks, Tag 0A76] and
`𝒩 = i^* 𝒪_X(D)` is the normal sheaf of `D`. There is no hypothesis on `M`. See the module
documentation for the proof. -/
theorem nonempty_homologyOne_derivedSheafHomExactSupport_iso (M : X.Modules) :
    Nonempty ((DerivedCategory.homologyFunctor D.subscheme.Modules 1).obj
        ((closedQuotient D).derivedSheafHomExactSupport.obj
          ((DerivedCategory.singleFunctor X.Modules 0).obj M)) ≅
      ((Stacks.SheafOfModules.Tensor.sheafTensor
            (Stacks.SheafOfModules.ringedSite D.subscheme.sheaf).O).obj
          ((Scheme.Modules.pullback D.subschemeι).obj (divisorSheaf D))).obj
        ((Scheme.Modules.pullback D.subschemeι).obj M)) := by
  obtain ⟨e₁⟩ := nonempty_homologyOne_pushforward_iso D M
  obtain ⟨e₂⟩ := nonempty_tensor_pushforward_iso D M
  exact ⟨(modulePushforward (closedQuotient D).i).preimageIso
    ((((modulePushforward (closedQuotient D).i).mapDerivedCategoryHomologyFunctorIso
      1).app _).symm ≪≫ e₁ ≪≫ e₂)⟩

end Stacks.Divisors

end
