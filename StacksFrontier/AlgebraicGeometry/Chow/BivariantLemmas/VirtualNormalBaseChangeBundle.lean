module

public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.VirtualNormalBaseChangeExcess

/-!
# The pulled-back virtual normal sheaf along the chosen base change

Let `i : Z ⟶ X` be a closed immersion with a virtual normal sheaf `𝒩` (Stacks 0FBJ), let
`f : X' ⟶ X` be a morphism, and let `g : Z ×_X X' ⟶ Z` be the projection of the chosen fibre
product. The pullback `g^*𝒩` is a virtual normal sheaf for the closed immersion
`Z ×_X X' ⟶ X'`, and it has the constant rank of `𝒩`.

## Main definitions

* `Stacks.Chow.baseChangeVirtualNormalBundle` — the virtual normal sheaf `g^*𝒩` of
  `Z ×_X X' ⟶ X'`.

## References

* [Stacks Project, Tag 0FBJ](https://stacks.math.columbia.edu/tag/0FBJ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

/-- The virtual normal sheaf `g^*𝒩` of the closed immersion `Z ×_X X' ⟶ X'`, the pullback of a
virtual normal sheaf `𝒩` of `i : Z ⟶ X` along the projection `g : Z ×_X X' ⟶ Z` of the chosen
fibre product. -/
abbrev baseChangeVirtualNormalBundle {Z X X' : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (f : X' ⟶ X) (N : VirtualNormalBundle i) : VirtualNormalBundle (pullback.snd i f) :=
  VirtualNormalBundle.baseChange i (pullback.snd i f) (pullback.fst i f) f
    (isPullback_pullbackSnd i f) N

/-- If `𝒩` is finite locally free of constant rank `m`, then so is `g^*𝒩`. -/
instance isFiniteLocallyFreeOfRank_baseChangeVirtualNormalBundle {Z X X' : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i] (f : X' ⟶ X) (N : VirtualNormalBundle i) (m : ℕ)
    [hrank : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} N.bundle m] :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (baseChangeVirtualNormalBundle i f N).bundle m :=
  isFiniteLocallyFreeOfRank_modulePullback (pullback.fst i f) N.bundle m hrank

end Stacks.Chow

end
