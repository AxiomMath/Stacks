module

public import StacksFrontier.AlgebraicGeometry.Spaces.ProperFlatStein.FibreBettiNumbers
public import StacksFrontier.Homology.Perfect.BettiConstructible
import StacksCore.Tactic.StacksAttribute

/-!
# The level sets of the Betti numbers of the fibres of a proper family are locally constructible

Let `Y` be a scheme, `f : X ⟶ Y` a proper morphism of finite presentation from an algebraic space,
and `𝓕` an `𝒪_X`-module of finite presentation, flat over `Y`. The level sets of the Betti-number
function `β_i(y) = dim_{κ(y)} H^i(X_y, 𝓕_y)` are locally constructible in `Y`: locally on `Y`,
`β_i` is the derived-fibre Betti function of a pseudo-coherent complex on an affine open
(`exists_isOpenEmbedding_fibreBetti_comp_eq`), whose level sets are constructible (the affine case,
`StacksDraft.Perfect.isConstructible_fibreBetti_preimage`).

## Main results

* `AlgebraicGeometry.Space.ProperFlatStein.isLocallyConstructible_fibreBetti_preimage`:
  Stacks 0E0R (3). Parts (1) and (2) are in
  `StacksFrontier.AlgebraicGeometry.Spaces.ProperFlatStein.FibreBettiNumbers`.

## References

* [Stacks Project, Tag 0E0R](https://stacks.math.columbia.edu/tag/0E0R)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped Set.Notation

universe u

namespace AlgebraicGeometry.Space.ProperFlatStein

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {U : BigFppfOver B S hS} {X : AlgebraicSpaces B S hS}
  (f : X ⟶ ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩)

/-- **Stacks 0E0R, part (3): the level sets of the Betti numbers of the fibres are locally
constructible.** For `f : X ⟶ Y` proper and of finite presentation and `𝓕` of finite
presentation and flat over `Y`, each set `{y | dim_{κ(y)} Hⁱ(X_y, 𝓕_y) = n}` is locally
constructible in `Y`. -/
@[stacks 0E0R "(3)"]
theorem isLocallyConstructible_fibreBetti_preimage (hf : IsProper B S hS f.hom)
    (hfp : IsFinitePresentation B S hS f.hom) (F : Modules.{u, u} B S hS X.1 X.2)
    (hFfp : F.IsFinitePresentation) (hF : IsFlatOver B S hS X.2 f.hom F) (i : ℤ) (n : ℕ) :
    Topology.IsLocallyConstructible (fibreBettiFunction f F i ⁻¹' {n}) := by
  intro x
  obtain ⟨R, M, φ, hφ, hx, hM, heq⟩ :=
    exists_isOpenEmbedding_fibreBetti_comp_eq f hf hfp F hFfp hF i x
  refine ⟨Set.range φ, hφ.isOpen_range.mem_nhds hx, hφ.isOpen_range, ?_⟩
  let e := hφ.isEmbedding.toHomeomorph
  have hset : Set.range φ ↓∩ (fibreBettiFunction f F i ⁻¹' {n}) =
      e.symm ⁻¹' (StacksDraft.Perfect.fibreBetti.{u, u} M i ⁻¹' {n}) := by
    ext u
    rw [← heq]
    simp only [Set.mem_preimage, Function.comp_apply]
    rw [show φ (e.symm u) = (u : (BigFppfOver.toScheme B S hS).obj U) from
      congrArg Subtype.val (e.apply_symm_apply u)]
  rw [hset]
  exact (StacksDraft.Perfect.isConstructible_fibreBetti_preimage M hM i n
    ).preimage_of_isOpenEmbedding e.symm.isOpenEmbedding

end AlgebraicGeometry.Space.ProperFlatStein
