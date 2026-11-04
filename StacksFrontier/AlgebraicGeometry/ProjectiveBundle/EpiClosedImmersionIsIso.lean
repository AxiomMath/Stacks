module

public import StacksFrontier.AlgebraicGeometry.ProjectiveBundle.EpiClosedImmersionFactorization

/-!
# The closed immersion of projective bundles of an isomorphism is an isomorphism

Let `X` be a scheme and `u : F ⟶ G` an epimorphism of quasi-coherent modules with `u ≫ v = 𝟙 F`
for some `v` (so `u` is an isomorphism). The closed immersion
`i = Stacks.RelativeProj.projectiveBundleMapOfEpi u : 𝐏(G) ⟶ 𝐏(F)` is an isomorphism: by the
factorization criterion (`Stacks.RelativeProj.exists_comp_projectiveBundleMapOfEpi_of_eq_zero`,
for the split exact sequence `0 ⟶ 0 ⟶ F ⟶ G ⟶ 0`) the identity of `𝐏(F)` factors through `i`,
so `i` is a split epimorphism, and a closed immersion is a monomorphism.

## Main results

* `Stacks.RelativeProj.isIso_projectiveBundleMapOfEpi_of_comp_eq_id`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.RelativeProj

variable {X : Scheme.{u}} {F G : X.Modules} [F.IsQuasicoherent] [G.IsQuasicoherent]

/-- **The closed immersion of projective bundles of an isomorphism is an isomorphism**: for
`u : F ⟶ G` with `u ≫ v = 𝟙 F`, the identity of `𝐏(F)` factors through
`projectiveBundleMapOfEpi u`, which is a monomorphism. -/
theorem isIso_projectiveBundleMapOfEpi_of_comp_eq_id (u : F ⟶ G) [Epi u] (v : G ⟶ F)
    (huv : u ≫ v = 𝟙 F) : IsIso (projectiveBundleMapOfEpi u) := by
  obtain ⟨h, hh⟩ := exists_comp_projectiveBundleMapOfEpi_of_eq_zero u (0 : F ⟶ F) 0 v
    (by rw [zero_comp, zero_add, huv]) (𝟙 (projectiveBundle X F))
    (by rw [Functor.map_zero, zero_comp, Functor.map_zero])
  have : IsSplitEpi (projectiveBundleMapOfEpi u) := ⟨⟨h, hh⟩⟩
  exact isIso_of_mono_of_isSplitEpi _

end Stacks.RelativeProj

end
