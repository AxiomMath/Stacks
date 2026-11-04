module

public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionStructureMap
public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalModuleFirstOrderIdeal

/-!
# The kernel of the structure map of the inclusion of a closed subspace

The defining ideal `AlgebraicGeometry.Space.definingIdealAt` of a closed subspace `Z ⊆ X` is the
kernel of the structure map `𝒪_X ⟶ i_*𝒪_Z` of the inclusion, read in sheaves of rings.  This
file records the same statement for the structure map of the morphism of small étale *ringed
topoi* of Stacks 03G8, a map of sheaves of commutative rings.

## Main results

* `AlgebraicGeometry.Space.fSharp_app_eq_zero_iff`: a section is killed by the structure map of
  the morphism of small étale ringed topoi of the inclusion of `Z` exactly when it lies in the
  defining ideal of `Z`.
-/

@[expose] public section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {Y : AlgebraicSpaces B S hS}

/-- Vanishing of a section under a map of sheaves of commutative rings is vanishing under the
map of sheaves of rings underlying it. -/
theorem app_eq_zero_iff_of_map_eq {O O' : Sheaf (SmallEtale.topology B S hS Y.1) CommRingCat.{u}}
    (f : O ⟶ O')
    {g : (sheafCompose (SmallEtale.topology B S hS Y.1) (forget₂ CommRingCat.{u} RingCat.{u})).obj
        O ⟶
      (sheafCompose (SmallEtale.topology B S hS Y.1) (forget₂ CommRingCat.{u} RingCat.{u})).obj O'}
    (h : (sheafCompose (SmallEtale.topology B S hS Y.1)
      (forget₂ CommRingCat.{u} RingCat.{u})).map f = g) (U : (SmallEtale B S hS Y.1)ᵒᵖ)
    (a : O.obj.obj U) :
    f.hom.app U a = 0 ↔ g.hom.app U a = 0 := by
  subst h
  rfl

variable (B S hS) {X : AlgebraicSpaces B S hS} (Z : ClosedSubspaces B S hS X.1)

/-- A section of `𝒪_X` is killed by the structure map of the inclusion of a closed subspace
exactly when it lies in the defining ideal. -/
theorem fSharp_app_eq_zero_iff (U : (SmallEtale B S hS X.1)ᵒᵖ)
    (a : (smallEtaleRingedTopos B S hS X).O.obj.obj U) :
    (smallEtaleRingedToposHom B S hS (subspaceInclusion B S hS X Z)).fSharp.hom.app U a = 0 ↔
      a ∈ definingIdealAt B S hS X Z U :=
  (app_eq_zero_iff_of_map_eq _
    (forgetCommRingSheaf_map_fSharp B S hS (subspaceInclusion B S hS X Z)) U a).trans
    (RingHom.mem_ker).symm

end AlgebraicGeometry.Space

end
