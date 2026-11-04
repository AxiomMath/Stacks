module

public import StacksFrontier.AlgebraicGeometry.Duality.NormalizedDualizingCocycle
public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImageFTS.Formalism

/-!
# The cocycle condition for the upper shriek functors of compactifications

[Stacks, Tag 0AU6], `Stacks.Duality.UpperShriek.overlapCompareRestrict_cocycle`, read for the
upper shriek formalism `Stacks.Duality.UpperShriek.ofCompactifications` built from a
compactification of every shriekable morphism: the functors `f^! = j^* ∘ ā` of
[Stacks, Tag 0A9Y] on `D⁺_QCoh`, with the comparisons of [Stacks, Tag 0ATX] and their coherence
[Stacks, Tag 0ATY].

## Main results

* `Stacks.Duality.UpperShriek.overlapCompareRestrict_cocycle_ofCompactifications` — the cocycle
  condition on a triple overlap.

## References

* [Stacks Project, Tag 0AU6](https://stacks.math.columbia.edu/tag/0AU6)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u v v' w

namespace Stacks.Duality

namespace UpperShriek

/-- **[Stacks, Tag 0AU6] for the upper shriek functors of compactifications.** For a
compactification `c f` of every separated finite-type `f` with Noetherian target, read with the
functors `f^! = j^* ∘ ā` of [Stacks, Tag 0A9Y] on `D⁺_QCoh`, the comparisons of
[Stacks, Tag 0ATX] and their coherence [Stacks, Tag 0ATY]
(`Stacks.Duality.UpperShriek.ofCompactifications`): for a finite covering `𝒰` of `X` by opens
separated over `S`, the canonical comparisons of the local models `p_i^!ω_S^•` satisfy
`φ_{ik}|_{U_i ∩ U_j ∩ U_k} = φ_{jk}|_{U_i ∩ U_j ∩ U_k} ∘ φ_{ij}|_{U_i ∩ U_j ∩ U_k}`. -/
theorem overlapCompareRestrict_cocycle_ofCompactifications
    (c : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y), IsShriekable f → CompactificationOf (Over.mk f))
    {X S : Scheme.{u}} {p : X ⟶ S} (hp : IsFiniteTypeOverNoetherian p)
    (ωS : quasiCoherentDerivedCategoryPlusOfModel S) {ι : Type w} (𝒰 : SeparatedCovering p ι)
    (i j k : ι) :
    (ofCompactifications c).overlapCompareRestrict hp ωS 𝒰 i k (𝒰.U i ⊓ 𝒰.U j ⊓ 𝒰.U k)
        (le_inf (inf_le_left.trans inf_le_left) inf_le_right) =
      (ofCompactifications c).overlapCompareRestrict hp ωS 𝒰 i j (𝒰.U i ⊓ 𝒰.U j ⊓ 𝒰.U k)
          inf_le_left ≪≫
        (ofCompactifications c).overlapCompareRestrict hp ωS 𝒰 j k (𝒰.U i ⊓ 𝒰.U j ⊓ 𝒰.U k)
          (le_inf (inf_le_left.trans inf_le_right) inf_le_right) :=
  (ofCompactifications c).overlapCompareRestrict_cocycle hp ωS 𝒰 i j k

end UpperShriek

end Stacks.Duality

end
