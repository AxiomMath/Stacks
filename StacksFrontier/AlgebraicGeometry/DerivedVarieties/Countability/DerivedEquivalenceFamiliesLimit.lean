module

public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.Countability.DerivedEquivalenceFamilies
public import
  StacksFrontier.AlgebraicGeometry.DerivedVarieties.FourierMukai.RelativeEquivalenceLimitDescent

/-!
# The countable family of relative equivalences, with the limit inputs proved

The assembly `AlgebraicGeometry.exists_countable_relativeEquivalenceKernels_of_hasRelativeKernel`
of [Stacks, Tag 0G0Y] and the Noetherian form
`AlgebraicGeometry.exists_isRelativeEquivalenceKernel_of_descentSituation_of_isNoetherian` of
[Stacks, Tag 0G0L] take the two halves of [Stacks, Tag 09RF] along the tower of fibre products as
hypotheses `h09RFobj` and `h09RFiso`. Both are proved, for an index set in the universe of the
schemes, as `AlgebraicGeometry.perfectDescendsAlongBaseChangedTower` and
`AlgebraicGeometry.perfectIsoDescendsAlongBaseChangedTower`, in
`StacksFrontier/AlgebraicGeometry/DerivedVarieties/FourierMukai/RelativeEquivalenceLimitDescent.lean`,
from [Stacks, Tag 09RF] applied to the tower of fibre products. This file states the two results
with those hypotheses discharged.

## Main results

* `exists_isRelativeEquivalenceKernel_of_descentSituation_of_isNoetherian_stages`:
  [Stacks, Tag 0G0L] over Noetherian stages, with no hypothesis beyond the source's.
* `exists_countable_relativeEquivalenceKernels_of_derivedEquivalenceHasRelativeKernel`:
  the assembly of [Stacks, Tag 0G0Y], whose one remaining input is
  `AlgebraicGeometry.DerivedEquivalenceHasRelativeKernel`.

## Implementation notes

Neither theorem is registered. [Stacks, Tag 0G0L] is stated by the source for an arbitrary
Situation 09RD, not only for Noetherian stages, and the assembly of [Stacks, Tag 0G0Y] still takes
`DerivedEquivalenceHasRelativeKernel` (the Orlov chain) as a hypothesis.

## References

* [Stacks Project, Tag 09RF](https://stacks.math.columbia.edu/tag/09RF)
* [Stacks Project, Tag 0G0L](https://stacks.math.columbia.edu/tag/0G0L)
* [Stacks Project, Tag 0G0Y](https://stacks.math.columbia.edu/tag/0G0Y)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPullback)

namespace AlgebraicGeometry

attribute [local instance 100000] HasDerivedCategory.standard

universe u

/-- **[Stacks, Tag 0G0L] over Noetherian stages.** In the situation of [Stacks, Tag 09RD] with
every stage Noetherian and the index set in the universe of the schemes, for `X₀ ⟶ S₀` and
`Y₀ ⟶ S₀` smooth and proper, a Fourier-Mukai kernel of a relative equivalence from
`X₀ ×_{S₀} S` to `Y₀ ×_{S₀} S` over `S` comes from a Fourier-Mukai kernel of a relative equivalence
from `X₀ ×_{S₀} S_i` to `Y₀ ×_{S₀} S_i` over `S_i` for some `i ≥ 0`. -/
theorem exists_isRelativeEquivalenceKernel_of_descentSituation_of_isNoetherian_stages
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] (D : DescentSituation.{u, u} I)
    (hN : ∀ i : I, IsNoetherian (D.stage i))
    {X₀ Y₀ : Scheme.{u}} (x : X₀ ⟶ D.stage D.base) (y : Y₀ ⟶ D.stage D.base)
    [Smooth x] [IsProper x] [Smooth y] [IsProper y]
    {K : DerivedCategory (pullback (pullback.snd x (D.projection D.base))
      (pullback.snd y (D.projection D.base))).Modules}
    (hK : IsRelativeEquivalenceKernel (pullback.snd x (D.projection D.base))
      (pullback.snd y (D.projection D.base)) K) :
    ∃ (i : I) (hi : D.base ≤ i) (Ki : DerivedCategory (pullback
      (pullback.snd x (D.transition hi)) (pullback.snd y (D.transition hi))).Modules),
      IsRelativeEquivalenceKernel (pullback.snd x (D.transition hi))
        (pullback.snd y (D.transition hi)) Ki :=
  exists_isRelativeEquivalenceKernel_of_descentSituation_of_isNoetherian D
    perfectDescendsAlongBaseChangedTower perfectIsoDescendsAlongBaseChangedTower hN
    diagonalKernelAndConvolutionPerfectOfNoetherian x y hK

/-- **The assembly of [Stacks, Tag 0G0Y], with the inputs from [Stacks, Tag 09RF] proved.** Let
`K` be a field, and suppose every `K`-linear exact equivalence `D_perf(𝒪_A) ≌ D_perf(𝒪_B)` between
smooth proper `K`-schemes has a Fourier-Mukai kernel of a relative equivalence
(`AlgebraicGeometry.DerivedEquivalenceHasRelativeKernel`). There are a countable type `I` and,
for `i : I`, a scheme `S i` of finite type over `K`, smooth proper `X i ⟶ S i` and `Y i ⟶ S i`,
and a Fourier-Mukai kernel `M i` of a relative equivalence from `X i` to `Y i` over `S i`, such
that for all smooth proper `A`, `B` over `K` with a `K`-linear exact equivalence
`D_perf(𝒪_A) ≌ D_perf(𝒪_B)` there are `i` and a `K`-point `s` of `S i` with `A ≅ (X i)_s` and
`B ≅ (Y i)_s`. -/
theorem exists_countable_relativeEquivalenceKernels_of_derivedEquivalenceHasRelativeKernel
    (K : Type u) [Field K] (hkernel : DerivedEquivalenceHasRelativeKernel K) :
    ∃ (I : Type (u + 1)) (_ : Countable I)
      (S : I → Over (Spec (.of K)))
      (X Y : (i : I) → Over (S i).left)
      (M : (i : I) → DerivedCategory (pullback (X i).hom (Y i).hom).Modules)
      (_ : ∀ i, LocallyOfFiniteType (S i).hom ∧ QuasiCompact (S i).hom)
      (_ : ∀ i, Smooth (X i).hom ∧ IsProper (X i).hom)
      (_ : ∀ i, Smooth (Y i).hom ∧ IsProper (Y i).hom)
      (_ : ∀ i, IsRelativeEquivalenceKernel (X i).hom (Y i).hom (M i)),
      ∀ (A B : Over (Spec (.of K))),
        Smooth A.hom → IsProper A.hom → Smooth B.hom → IsProper B.hom →
          (letI : Linear K A.left.Modules := modulesLinear K A
           letI : Linear K B.left.Modules := modulesLinear K B
           ∃ e : Stacks.Perfect.BoundedLocallyFreeComplexes.PerfectDerivedCategory A.left ≌
               Stacks.Perfect.BoundedLocallyFreeComplexes.PerfectDerivedCategory B.left,
             e.functor.Linear K ∧
               ∃ h : e.functor.CommShift ℤ,
                 letI := h
                 e.functor.IsTriangulated) →
            ∃ (i : I) (s : Over.mk (𝟙 (Spec (.of K))) ⟶ S i),
              Nonempty (A ≅ (Over.pullback s.left).obj (X i)) ∧
                Nonempty (B ≅ (Over.pullback s.left).obj (Y i)) :=
  exists_countable_relativeEquivalenceKernels_of_hasRelativeKernel
    perfectDescendsAlongBaseChangedTower perfectIsoDescendsAlongBaseChangedTower K hkernel

end AlgebraicGeometry

end
