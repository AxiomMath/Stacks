module

public import StacksFrontier.AlgebraicGeometry.LocalCohomology.ImprovingCoherentModules.DepthTwoExtensionConstruction
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.ImprovingCoherentModules.DepthTwoExtensionPullback
public import StacksFrontier.AlgebraicGeometry.Morphisms.CohenMacaulay.FibreStalk
public import StacksCore.Tactic.StacksAttribute

/-!
# The depth-two extension: existence, uniqueness and Cohen–Macaulay pullback

Let `X` be a Noetherian scheme which locally has a dualizing complex, let `T ⊆ X` be stable under
specialization and let `F` be a coherent module with `depth(F_x) ≥ 1` at every immediate
specialization `x ⤳ x'` with `x' ∈ T` and `x ∉ T`.  This module assembles [Stacks, Tag 0EI3]:
`F` has a depth-two extension along `T`, it is unique up to a unique isomorphism under `F`, and
its pullback along a Cohen–Macaulay morphism from a Noetherian scheme is again one, along the
preimage of `T`.

## Main results

* `AlgebraicGeometry.existsUnique_isDepthTwoExtension_and_pullback`: [Stacks, Tag 0EI3].

## References

* [Stacks Project, Tag 0EI3](https://stacks.math.columbia.edu/tag/0EI3)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- **Stacks Project, Tag 0EI3.**  Let `X` be a Noetherian scheme which locally has a dualizing
complex, let `T ⊆ X` be stable under specialization and let `F` be a coherent `𝒪_X`-module with
`depth(F_x) ≥ 1` at every immediate specialization `x ⤳ x'` with `x' ∈ T` and `x ∉ T`.  Then there
is a map `φ : F ⟶ F''` to a coherent module which is an isomorphism on the stalks off `T` and
whose stalks on `T` have depth at least two; it is unique, in that any other such map is carried
to it by a unique isomorphism under `F`; and for every Cohen–Macaulay morphism `f : Y ⟶ X` with
`Y` Noetherian, `f^*φ` has the same properties along `f⁻¹(T)` (and so is the unique such map). -/
@[stacks 0EI3 "existence, uniqueness and the Cohen-Macaulay pullback clause, at the source's \
hypotheses"]
public theorem existsUnique_isDepthTwoExtension_and_pullback
    (X : Scheme.{u}) [IsNoetherian X] (hdual : HasDualizingComplexOnAffineCover X)
    (T : Set X) (hT : StableUnderSpecialization T) (F : X.Modules) [F.IsCoherent]
    (himm : ∀ x x' : X, IsImmediateSpecialization x x' → x' ∈ T → x ∉ T →
      (1 : ℕ∞) ≤ Module.depth (X.presheaf.stalk x)
        (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) (F.presheaf.stalk x)) :
    ∃ (G : X.Modules) (φ : F ⟶ G), IsDepthTwoExtension T φ ∧
      (∀ (H : X.Modules) (ψ : F ⟶ H), IsDepthTwoExtension T ψ →
        ∃! e : G ≅ H, φ ≫ e.hom = ψ) ∧
      ∀ (Y : Scheme.{u}) [IsNoetherian Y] (f : Y ⟶ X),
        f.IsCohenMacaulay (fun x ↦ isLocallyNoetherian_fiber f x) →
        IsDepthTwoExtension (f ⁻¹' T) ((Scheme.Modules.pullback f).map φ) ∧
          ∀ (H : Y.Modules) (ψ : (Scheme.Modules.pullback f).obj F ⟶ H),
            IsDepthTwoExtension (f ⁻¹' T) ψ →
              ∃! e : (Scheme.Modules.pullback f).obj G ≅ H,
                (Scheme.Modules.pullback f).map φ ≫ e.hom = ψ := by
  obtain ⟨G, φ, hφ, huniq⟩ :=
    existsUnique_isDepthTwoExtension_of_hasDualizingComplex X hdual T hT F himm
  refine ⟨G, φ, hφ, huniq, fun Y _ f hcm ↦ ?_⟩
  have hpb := depthTwoExtension_pullback T F G φ hφ f (fun x ↦ isLocallyNoetherian_fiber f x) hcm
  exact ⟨hpb, fun H ψ hψ ↦ depthTwoExtension_unique Y (f ⁻¹' T) _ _ H _ ψ hpb hψ⟩

end AlgebraicGeometry

end
