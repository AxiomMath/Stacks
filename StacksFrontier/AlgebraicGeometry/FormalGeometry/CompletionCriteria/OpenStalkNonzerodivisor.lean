module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.AlgebraizationCoherentFormal.RegularSequence
public import Mathlib.Algebra.Ring.NonZeroDivisors

/-!
# Nonzerodivisors of the base ring stay nonzerodivisors in the local rings of the complement

Fix an algebraization situation: a Noetherian ring `A` with ideals `I ⊆ 𝔞`, the affine scheme
`X = Spec(A)` and the open complement `U = X ∖ V(𝔞)`. An element `a` of `A` determines a global
function on `U`, and hence a germ in each local ring `𝒪_{U,y}`.

The local ring `𝒪_{U,y}` is the localization `A_𝔮` of `A` at the prime `𝔮` under `y`, because the
stalk of an open subscheme is the stalk of the ambient scheme and on `Spec(A)` the stalk at a
prime is the localization there. Localization maps carry nonzerodivisors to nonzerodivisors, so a
nonzerodivisor of `A` has a nonzerodivisor germ at every point of `U`. This is the hypothesis on
the germs that the principal short exact sequences of `𝒪_U` require.

## Main results

* `Stacks.Algebraization.germOfBase_eq_baseToPointStalk` — the germ at `y ∈ U` of the function
  determined by `a ∈ A` is the image of `a` under the ring map `A → 𝒪_{U,y}` that goes through
  the stalk of `X` at the image of `y`.
* `Stacks.Algebraization.germOfBase_mem_nonZeroDivisors` — a nonzerodivisor of `A` has a
  nonzerodivisor germ in `𝒪_{U,y}` for every `y ∈ U`.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Algebraization

/-- The two descriptions of the image of `a ∈ A` in the local ring `𝒪_{U,y}` agree: taking the
germ on `U` of the global function determined by `a` is the same as taking the germ on
`X = Spec(A)` at the image of `y` and then mapping along the stalk map of the open immersion.
This is naturality of germs for `U ⟶ X`. -/
theorem germOfBase_eq_baseToPointStalk (S : AlgebraizationSituation.{u}) (y : S.U.toScheme)
    (a : S.A) :
    germOfBase S y a = baseToPointStalk S y a := by
  have hgerm : (S.U.ι.stalkMap y).hom.comp
      (S.X.presheaf.germ ⊤ (S.U.ι.base y) (Set.mem_univ _)).hom =
      (S.U.toScheme.presheaf.germ ⊤ y trivial).hom.comp (S.U.ι.appTop).hom := by
    rw [← CommRingCat.hom_comp, ← CommRingCat.hom_comp]
    exact congrArg CommRingCat.Hom.hom (Scheme.Hom.germ_stalkMap S.U.ι ⊤ y trivial)
  exact (DFunLike.congr_fun hgerm ((Scheme.ΓSpecIso (.of S.A)).inv.hom a)).symm

/-- A nonzerodivisor of the base ring `A` has a nonzerodivisor germ in the local ring of the open
complement at every one of its points: that local ring is a localization of `A`, and a
localization map carries nonzerodivisors to nonzerodivisors. -/
theorem germOfBase_mem_nonZeroDivisors (S : AlgebraizationSituation.{u}) {f : S.A}
    (hf : f ∈ nonZeroDivisors S.A) (y : S.U.toScheme) :
    germOfBase S y f ∈ nonZeroDivisors (S.U.toScheme.presheaf.stalk y) := by
  have hloc : algebraMap S.A (Localization.AtPrime (underlyingPrime S y).asIdeal) f ∈
      nonZeroDivisors (Localization.AtPrime (underlyingPrime S y).asIdeal) :=
    Submonoid.mem_comap.mp
      (IsLocalization.nonZeroDivisors_le_comap (underlyingPrime S y).asIdeal.primeCompl
        (Localization.AtPrime (underlyingPrime S y).asIdeal) hf)
  have hcomp : pointStalkRingEquiv S y (baseToPointStalk S y f) =
      algebraMap S.A (Localization.AtPrime (underlyingPrime S y).asIdeal) f :=
    pointStalkRingEquiv_baseToPointStalk_apply S y f
  rw [germOfBase_eq_baseToPointStalk]
  exact mem_nonZeroDivisors_of_injective (pointStalkRingEquiv S y).injective (hcomp ▸ hloc)

end Stacks.Algebraization

end
