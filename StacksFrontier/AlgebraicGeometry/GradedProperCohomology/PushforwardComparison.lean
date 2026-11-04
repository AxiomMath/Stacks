module

public import StacksFrontier.AlgebraicGeometry.AffineCohomologyComparison.Basic
public import StacksFrontier.AlgebraicGeometry.GradedProperCohomology.CohomologyDirectSum

/-!
# `H^p(X, ℱ) = H^p(X', ℱ')`: the comparison step of [Stacks, Tag 0897]'s proof

The proof of [Stacks, Tag 0897] passes from the graded module `ℱ` on `X` to a single
`𝒪_{X'}`-module `ℱ'` on `X' = Spec(B) ×_{Spec(A)} X` with `π_* ℱ' = ℱ`, and then asserts

`H^p(X, ℱ) = H^p(X', ℱ')`,

*"since the morphism `π : X' ⟶ X` is affine"*, citing [Stacks, Tag 089W]. The left-hand side is
the graded module `⨁ₙ H^p(X, ℱₙ)` and the right-hand side is the cohomology of a single sheaf, so
the assertion is really two steps: [Stacks, Tag 089W] along `π`, and the identification of
`H^p(X, ⨁ₙ ℱₙ)` with `⨁ₙ H^p(X, ℱₙ)`. This file composes them.

What it needs is exactly the source's own `π_* ℱ' = ℱ` and nothing else: no comparison of the
cohomologies is assumed. Compare `Stacks.AlgebraicGeometry.GradedProperCohomology`
`.moduleFinite_gradedCohomologySum`, whose hypothesis `cmp` is this comparison, taken as given.

## Main results

* `Stacks.AlgebraicGeometry.GradedProperCohomology.gradedCohomologyIsoPushforward`: for an affine
  `π : X' ⟶ X` onto a quasi-compact quasi-separated scheme and a quasi-coherent `𝒪_{X'}`-module
  `ℱ'` whose direct image is the total module `⨁ₙ ℱₙ` of a graded module `ℱ`, the cohomology
  `H^p(X', ℱ')` is `Γ(X, ⊤)`-linearly isomorphic to the graded cohomology `⨁ₙ H^p(X, ℱₙ)`.
* `gradedCohomologyIsoPushforwardOfIsProper`: the same with the two topological hypotheses
  discharged from properness of `f : X ⟶ Spec A`, which is how [Stacks, Tag 0897] has them.

## Implementation notes

The isomorphism is over `Γ(X, ⊤)`, the ring of global functions downstairs: cohomology upstairs
is a `Γ(X', ⊤)`-module and is read as a `Γ(X, ⊤)`-module by restriction of scalars along `π^♯`,
which is the shape [Stacks, Tag 089W] is stated in.

**The `B`-linearity of the comparison is not supplied**, and that is what still stands between
this and an unconditional [Stacks, Tag 0897] part (1). The `B`-module structure on
`⨁ₙ H^p(X, ℱₙ)` of the tag's conclusion comes from the action of `ℬ = f^* B̃` on `ℱ` through
functoriality of cohomology; the `B`-module structure on `H^p(X', ℱ')` comes from
`f' : X' ⟶ Spec B`; and the identification of the two needs the identification of `X'` with the
relative spectrum of `ℬ`. None of that is built here. What is built is the underlying
`Γ(X, ⊤)`-linear isomorphism, which is the half of the source's `H^p(X, ℱ) = H^p(X', ℱ')` that
does not mention `B`.

## References

* [Stacks Project, Tag 0897](https://stacks.math.columbia.edu/tag/0897)
* [Stacks Project, Tag 089W](https://stacks.math.columbia.edu/tag/089W)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

universe u

namespace Stacks.AlgebraicGeometry.GradedProperCohomology

attribute [local instance] HasDerivedCategory.standard

variable {X : Scheme.{u}}
  {𝓑 : _root_.SheafOfModules.GradedAlgebra.{u, u} X.ringCatSheaf}

/-- **The comparison `H^p(X, ℱ) = H^p(X', ℱ')` of [Stacks, Tag 0897]'s proof.** Let `X` be a
quasi-compact quasi-separated scheme, `π : X' ⟶ X` an affine morphism, `ℱ` a graded
`𝓑`-module and `ℱ'` a quasi-coherent `𝒪_{X'}`-module whose direct image along `π` is the total
module `⨁ₙ ℱₙ`. Then the cohomology `H^p(X', ℱ')`, read as a `Γ(X, ⊤)`-module, is the graded
cohomology `⨁ₙ H^p(X, ℱₙ)`.

Two steps: [Stacks, Tag 089W] identifies `H^p(X', ℱ')` with `H^p(X, π_* ℱ')` because `π` is
affine, and `gradedCohomologySumEquiv` identifies `H^p(X, ⨁ₙ ℱₙ)` with `⨁ₙ H^p(X, ℱₙ)` because
cohomology on a quasi-compact quasi-separated scheme commutes with direct sums. Only the
source's own `π_* ℱ' = ℱ` is assumed. -/
def gradedCohomologyIsoPushforward
    [CompactSpace (X : Type u)] [QuasiSeparatedSpace (X : Type u)]
    {X' : Scheme.{u}} (π : X' ⟶ X) [_root_.AlgebraicGeometry.IsAffineHom π]
    (F' : X'.Modules) [F'.IsQuasicoherent]
    (F : _root_.SheafOfModules.GradedModule 𝓑) (p : ℕ)
    (hπ : (AlgebraicGeometry.Scheme.Modules.pushforward π).obj F' ≅ totalModule F) :
    ↥((ModuleCat.restrictScalars π.appTop.hom).obj (cohomologyOf X' p F')) ≃ₗ[Γ(X, ⊤)]
      gradedCohomologySum F p :=
  (Stacks.Cohomology.AffineComparison.cohomologyIsoPushforward π F' p ≪≫
      ((Stacks.Cohomology.AffineBase.moduleGlobalSections X).rightDerived p).mapIso
        hπ).toLinearEquiv.trans
    (gradedCohomologySumEquiv F p)

/-- **The comparison `H^p(X, ℱ) = H^p(X', ℱ')` of [Stacks, Tag 0897]'s proof**, with the two
topological hypotheses discharged from the tag's own hypothesis that `f : X ⟶ Spec A` is proper:
a scheme proper over an affine scheme is quasi-compact and quasi-separated. -/
def gradedCohomologyIsoPushforwardOfIsProper {A : Type u} [CommRing A]
    (f : X ⟶ Spec (.of A)) [IsProper f]
    {X' : Scheme.{u}} (π : X' ⟶ X) [_root_.AlgebraicGeometry.IsAffineHom π]
    (F' : X'.Modules) [F'.IsQuasicoherent]
    (F : _root_.SheafOfModules.GradedModule 𝓑) (p : ℕ)
    (hπ : (AlgebraicGeometry.Scheme.Modules.pushforward π).obj F' ≅ totalModule F) :
    ↥((ModuleCat.restrictScalars π.appTop.hom).obj (cohomologyOf X' p F')) ≃ₗ[Γ(X, ⊤)]
      gradedCohomologySum F p :=
  have := compactSpace_of_isProper_over_affine f
  have := quasiSeparatedSpace_of_isProper_over_affine f
  gradedCohomologyIsoPushforward π F' F p hπ

end Stacks.AlgebraicGeometry.GradedProperCohomology

end
