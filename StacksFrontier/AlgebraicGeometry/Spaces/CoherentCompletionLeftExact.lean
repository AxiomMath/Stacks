module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentAdicAbelian
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentCompletionExact
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentCartesianOnAffineCharts

/-!
# Left exactness of the completion functor on a Noetherian algebraic space

Let `F` be a Noetherian algebraic space over a scheme `S` and let `𝓘 ⊆ 𝒪_F` be a quasi-coherent
sheaf of ideals on its small étale site.  Stacks 08B5 asserts that the completion functor
`Coh(𝒪_F) ⥤ Coh(F, 𝓘)` of Stacks 08B4 is exact.

`StacksFrontier.AlgebraicGeometry.Spaces.CoherentCompletionExact` proves this under the source's own
hypotheses, `F` Noetherian and `𝓘` quasi-coherent, as
`AlgebraicGeometry.Space.preservesFiniteLimits_completionFunctor` and
`AlgebraicGeometry.Space.exactFunctor_completionFunctor`.  This file restates those two results
under the names below and derives the uniqueness half of Stacks 08BB from them.

## Main results

* `AlgebraicGeometry.Space.isNormalMonoCategory_coherentAdicSystems_of_isQuasicoherentOnSite` —
  every monomorphism of `Coh(F, 𝓘)` is a kernel, for a quasi-coherent `𝓘` on a Noetherian
  algebraic space.
* `AlgebraicGeometry.Space.preservesFiniteLimits_completionFunctor_of_isNoetherian` — **Stacks
  08B5, left exactness**: the completion functor preserves finite limits.
* `AlgebraicGeometry.Space.exactFunctor_completionFunctor_of_isNoetherian` — **Stacks 08B5**: the
  completion functor is exact.
* `AlgebraicGeometry.Space.existsUnique_iso_of_algebraization_of_isNoetherian` — **Stacks 08BB,
  uniqueness** of the algebraization, with left exactness of completion supplied rather than
  taken as an instance argument.

## Implementation notes

The source states Stacks 08B5 for a Noetherian algebraic space, and that is the hypothesis here:
`AlgebraicGeometry.Space.IsNoetherian` together with the ambient
`hZ : B.Contains (⊤_ Scheme.{u})` that makes the notion expressible.  The `Fact` instance on the
étale charts appears here only because the completion functor of Stacks 08B4 is itself stated
with it: it is that functor's own instance argument, reproduced unchanged so the functor
elaborates, and it is implied by the Noetherian hypothesis.  It stands in for no result.

Right exactness, `AlgebraicGeometry.Space.preservesFiniteColimits_completionFunctor`, needs
neither hypothesis and is not restated.

The last result re-derives the uniqueness half of Stacks 08BB from
`AlgebraicGeometry.Space.existsUnique_iso_of_algebraization`, whose statement takes left
exactness of the completion functor as an instance argument, by supplying that argument.  The
existence half of Stacks 08BB is not reached from here: the source obtains it by étale descent
from the case of a Noetherian scheme, and the restriction of coherent adic systems to an étale
chart is not available in this tree.

## References

* [Stacks Project, Tag 08B5](https://stacks.math.columbia.edu/tag/08B5)
* [Stacks Project, Tag 08B4](https://stacks.math.columbia.edu/tag/08B4)
* [Stacks Project, Tag 08BB](https://stacks.math.columbia.edu/tag/08BB)
* [Stacks Project, Tag 089P](https://stacks.math.columbia.edu/tag/089P)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)
    (𝓘 : (SheafOfModules.unit
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O))).Submodule)

/-! ### Monomorphisms of `Coh(F, 𝓘)` are kernels -/

/-- **Every monomorphism of `Coh(F, 𝓘)` is a kernel**, for a quasi-coherent sheaf of ideals `𝓘`
on a Noetherian algebraic space.

This is `AlgebraicGeometry.Space.isNormalMonoCategory_coherentAdicSystems`, a consequence of part
(1) of Stacks 089P, whose hypothesis that `𝓘` be cartesian on the affine charts is Descent
Proposition 03DX (2) and follows from quasi-coherence by
`AlgebraicGeometry.Space.isCartesianOnAffineCharts_of_isQuasicoherentOnSite`. -/
theorem isNormalMonoCategory_coherentAdicSystems_of_isQuasicoherentOnSite
    (hZ : B.Contains (⊤_ Scheme.{u})) (hN : IsNoetherian B S hS hZ F)
    (hI : 𝓘.toSheafOfModules.IsQuasicoherentOnSite) :
    IsNormalMonoCategory (CoherentAdicSystems B S hS F hF 𝓘) :=
  isNormalMonoCategory_coherentAdicSystems B S hS F hF 𝓘 hZ hN
    (isCartesianOnAffineCharts_of_isQuasicoherentOnSite B S hS F hF 𝓘.toSheafOfModules hI)

/-! ### Stacks 08B5 -/

variable [Fact (HasEtaleLocalProperty B S hS F (fun V : Scheme.{u} => IsLocallyNoetherian V))]
    (hI : 𝓘.toSheafOfModules.IsQuasicoherentOnSite)

/-- **Stacks 08B5, left exactness.**  On a Noetherian algebraic space the completion functor
`Coh(𝒪_F) ⥤ Coh(F, 𝓘)` of Stacks 08B4 preserves finite limits.

This is `AlgebraicGeometry.Space.preservesFiniteLimits_completionFunctor`. -/
@[stacks 08B5 "left exactness: the completion functor preserves finite limits, over the \
source's own hypotheses that the algebraic space is Noetherian and the sheaf of ideals \
quasi-coherent"]
alias preservesFiniteLimits_completionFunctor_of_isNoetherian :=
  AlgebraicGeometry.Space.preservesFiniteLimits_completionFunctor

/-- **Stacks 08B5.**  On a Noetherian algebraic space the completion functor
`Coh(𝒪_F) ⥤ Coh(F, 𝓘)` of Stacks 08B4 is exact.

This is `AlgebraicGeometry.Space.exactFunctor_completionFunctor`. -/
@[stacks 08B5 "exactness of the completion functor over the source's own hypotheses that the \
algebraic space is Noetherian and the sheaf of ideals quasi-coherent"]
alias exactFunctor_completionFunctor_of_isNoetherian :=
  AlgebraicGeometry.Space.exactFunctor_completionFunctor

/-! ### Stacks 08BB, uniqueness -/

/-- **Stacks 08BB, uniqueness of the algebraization**, over the source's own hypotheses.

Let `𝓘 ⊆ 𝒪_F` be a quasi-coherent sheaf of ideals on a Noetherian algebraic space `F`, let `G`
be a coherent `𝒪_F`-module and let `E` be a coherent `𝓘`-adic system with a map
`α : E ⟶ G^∧`.  Two algebraizations of `α` — coherent modules `M`, `N` with maps `a : M ⟶ G`,
`a' : N ⟶ G` whose kernels and cokernels are annihilated by a power of `𝓘`, and isomorphisms
`β : E ≅ M^∧`, `β' : E ≅ N^∧` factoring `α` — differ by a unique isomorphism `M ≅ N` compatible
with the maps to `G` and with the comparison isomorphisms.

`AlgebraicGeometry.Space.existsUnique_iso_of_algebraization` states this with left exactness of
the completion functor as an instance argument, because Stacks 08B5 was not available where it
was proved; here that argument is supplied by
`AlgebraicGeometry.Space.preservesFiniteLimits_completionFunctor_of_isNoetherian`, so the only
hypotheses left are the source's. -/
@[stacks 08BB "uniqueness of the algebraization over the source's own hypotheses, with left \
exactness of completion (Stacks 08B5) supplied"]
theorem existsUnique_iso_of_algebraization_of_isNoetherian
    (hZ : B.Contains (⊤_ Scheme.{u})) (hN : IsNoetherian B S hS hZ F)
    {G M N : CoherentModules.{u, u} B S hS F hF} {E : CoherentAdicSystems B S hS F hF 𝓘}
    (α : E ⟶ (completionFunctor B S hS F hF 𝓘 hI).obj G) (a : M ⟶ G) (a' : N ⟶ G)
    (β : E ≅ (completionFunctor B S hS F hF 𝓘 hI).obj M)
    (β' : E ≅ (completionFunctor B S hS F hF 𝓘 hI).obj N)
    (ha : IsMapKernelCokernelAnnihilatedByPower B S hS F hF 𝓘 a)
    (ha' : IsMapKernelCokernelAnnihilatedByPower B S hS F hF 𝓘 a')
    (hα : α = β.hom ≫ (completionFunctor B S hS F hF 𝓘 hI).map a)
    (hα' : α = β'.hom ≫ (completionFunctor B S hS F hF 𝓘 hI).map a') :
    ∃! e : M ≅ N, e.hom ≫ a' = a ∧
      β.hom ≫ (completionFunctor B S hS F hF 𝓘 hI).map e.hom = β'.hom :=
  have := preservesFiniteLimits_completionFunctor_of_isNoetherian B S hS F hF 𝓘 hI hZ hN
  existsUnique_iso_of_algebraization B S hS F hF 𝓘 hI α a a' β β' ha ha' hα hα'

end AlgebraicGeometry.Space

end
