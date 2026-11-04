module

public import StacksFrontier.AlgebraicGeometry.Spaces.RelocalizeModules
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentModules
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocalTypesUnderSpecialCocontinuous
public import StacksFrontier.AlgebraicGeometry.Topologies.CoherentKernelOnSite

/-!
# Coherence across the relocalization of an algebraic space

Let `g : T ⟶ S` be a morphism of a big fppf site and `X` an algebraic space over `T`, with
lower-shriek extension `Λ X` over `S`. The equivalence
`AlgebraicGeometry.Space.relocalizeModulesEquivalence : Mod(𝒪_X) ≌ Mod(𝒪_{Λ X})` is the reindexing
along the equivalence of small étale sites `AlgebraicGeometry.Space.SmallEtale.relocalize`. Its
inverse, the restriction of modules along the special cocontinuous functor underlying that
equivalence, preserves and reflects coherence on the site (Stacks 03DM) and coherence
(Stacks 07UA).

## Main results

* `AlgebraicGeometry.Space.isCoherentOnSite_relocalizeModulesEquivalence_inverse_iff`: a module on
  `Λ X` is coherent on the site if and only if its image on `X` is.
* `AlgebraicGeometry.Space.isCoherent_relocalizeModulesEquivalence_inverse_iff`: a module on `Λ X`
  is coherent if and only if its image on `X` is.

## References

* [Stacks Project, Tag 03DM](https://stacks.math.columbia.edu/tag/03DM)
* [Stacks Project, Tag 07UA](https://stacks.math.columbia.edu/tag/07UA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) {T S : Scheme.{u}} (hT : B.Contains T) (hS : B.Contains S)
  (g : B.obj hT ⟶ B.obj hS) (X : (BigFppfOver B T hT)ᵒᵖ ⥤ Type u) (hX : IsAlgebraicSpace B T hT X)

/-- A module `M` on `Λ X` is coherent on the site if and only if its image
`(relocalizeModulesEquivalence B hT hS g X hX).inverse.obj M` on `X` is coherent on the site. -/
theorem isCoherentOnSite_relocalizeModulesEquivalence_inverse_iff
    (M : Modules.{u, u} B S hS ((OverShriek.relocalizePresheafFunctor g).obj X)
      (isAlgebraicSpace_relocalize' B hT hS g X hX)) :
    ((relocalizeModulesEquivalence B hT hS g X hX).inverse.obj M).IsCoherentOnSite ↔
      M.IsCoherentOnSite :=
  (Stacks.Sheaves.SpecialCocontinuous.isCoherentOnSite_iff (SmallEtale.topology B T hT X)
    (SmallEtale.topology B S hS _) (SmallEtale.relocalize B hT hS g X hX).functor
    (relocalizeRingSheaf B hT hS g X hX) M).symm

/-- A module `M` on `Λ X` is coherent if and only if its image
`(relocalizeModulesEquivalence B hT hS g X hX).inverse.obj M` on `X` is coherent. -/
theorem isCoherent_relocalizeModulesEquivalence_inverse_iff
    (M : Modules.{u, u} B S hS ((OverShriek.relocalizePresheafFunctor g).obj X)
      (isAlgebraicSpace_relocalize' B hT hS g X hX)) :
    IsCoherent B T hT X hX ((relocalizeModulesEquivalence B hT hS g X hX).inverse.obj M) ↔
      IsCoherent B S hS _ (isAlgebraicSpace_relocalize' B hT hS g X hX) M := by
  have h₁ := isQuasicoherentOnSite_relocalizeModulesEquivalence_iff B hT hS g X hX M
  have h₂ := isCoherentOnSite_relocalizeModulesEquivalence_inverse_iff B hT hS g X hX M
  exact ⟨fun hM => { toIsQuasicoherentOnSite := h₁.1 hM.toIsQuasicoherentOnSite
                     toIsCoherentOnSite := h₂.1 hM.toIsCoherentOnSite },
    fun hM => { toIsQuasicoherentOnSite := h₁.2 hM.toIsQuasicoherentOnSite
                toIsCoherentOnSite := h₂.2 hM.toIsCoherentOnSite }⟩

end AlgebraicGeometry.Space

end
