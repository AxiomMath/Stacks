module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineHigherPushforwardUnconditional
public import StacksFrontier.AlgebraicGeometry.Spaces.CohomologyOverBaseUniverseLift
public import StacksFrontier.AlgebraicGeometry.Spaces.TwistedCohomologyPushforward
public import StacksFrontier.AlgebraicGeometry.Spaces.TwistedEulerDevissage

/-!
# Twisted Euler characteristics along a closed immersion

Let `k` be a field, `X` a proper algebraic space over `k`, `i : Z ⟶ X` a closed immersion, `𝒢` a
coherent `𝒪_Z`-module and `L₁, …, L_r` invertible `𝒪_X`-modules.  Then

`χ(X, i_*𝒢 ⊗ L₁^{⊗ n₁} ⊗ ⋯ ⊗ L_r^{⊗ n_r}) = χ(Z, 𝒢 ⊗ (i^*L₁)^{⊗ n₁} ⊗ ⋯ ⊗ (i^*L_r)^{⊗ n_r})`

for every integral tuple `n`.  The twist moves through `i_*` by the projection formula, the
higher direct images along a closed immersion vanish (it is affine, Stacks 073H), so the
cohomology of the direct image is the cohomology on `Z` (Stacks 0733), and the Euler
characteristic of `AlgebraicGeometry.Space.eulerCharacteristic` is read at the universe of the
structure sheaf through `AlgebraicGeometry.Space.finrank_cohomologyOverBase_uliftForPresentation`.

## Main results

* `eulerCharacteristic_twistedModuleUlift_modulePushforward_of_isClosedImmersion`:
  the equality above.

## References

* [Stacks Project, Tag 0D2U](https://stacks.math.columbia.edu/tag/0D2U)
* [Stacks Project, Tag 073H](https://stacks.math.columbia.edu/tag/073H)
* [Stacks Project, Tag 01E8](https://stacks.math.columbia.edu/tag/01E8)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

attribute [local instance 5000] SheafOfModules.instAbelian

universe u w

namespace AlgebraicGeometry.Space

variable (k : Type u) [Field k] (B : BigFppfSite.{u}) (hk : B.Contains (Spec (.of k)))

/-- **The twisted Euler characteristics of the direct image along a closed immersion are those of
the module on the closed subspace, twisted by the inverse images.** -/
theorem eulerCharacteristic_twistedModuleUlift_modulePushforward_of_isClosedImmersion
    {X Z : AlgebraicSpaces B (Spec (.of k)) hk} {r : ℕ}
    (f : X.1 ⟶ yoneda.obj (baseObject k B hk)) (hf : IsProper B (Spec (.of k)) hk f)
    (i : Z ⟶ X) (hi : IsClosedImmersion B (Spec (.of k)) hk i.hom)
    (G : Modules.{u, u} B (Spec (.of k)) hk Z.1 Z.2) (hG : IsCoherent B (Spec (.of k)) hk Z.1 Z.2 G)
    (L : Fin r → Modules.{u, u} B (Spec (.of k)) hk X.1 X.2)
    [∀ j, Stacks.SheafOfModules.IsInvertible (structurePresheaf B (Spec (.of k)) hk X.1)
      ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B (Spec (.of k)) hk X.1 X.2).O)).property (L j)]
    (n : Fin r → ℤ) :
    have hfZ : IsProper B (Spec (.of k)) hk (i.hom ≫ f) :=
      isProper_comp B (Spec (.of k)) hk Z.2 X.2
        (isAlgebraicSpace_yoneda B (Spec (.of k)) hk (baseObject k B hk)) i.hom f
        (isProper_of_isClosedImmersion B (Spec (.of k)) hk Z.2 X.2 i.hom hi) hf
    haveI := fun j => stacksIsInvertible_modulePullback_obj B (Spec (.of k)) hk i (L j)
    @eulerCharacteristic.{u, w} k _ B hk X.1 X.2 f hf
        (twistedModuleUlift.{u, w} B (Spec (.of k)) hk X.1 X.2
          ((modulePushforward B (Spec (.of k)) hk i).obj G) L n)
        (isCoherent_twistedModuleUlift_of_isProper.{u, w} k B hk X f hf L _
          (isCoherent_modulePushforward_of_isClosedImmersion B (Spec (.of k)) hk
            (hasEtaleLocalProperty_isLocallyNoetherian_of_isProper k B hk X.1 X.2 f hf) i hi G hG)
          n) =
      @eulerCharacteristic.{u, w} k _ B hk Z.1 Z.2 (i.hom ≫ f) hfZ
        (twistedModuleUlift.{u, w} B (Spec (.of k)) hk Z.1 Z.2 G
          (fun j => (modulePullback B (Spec (.of k)) hk i).obj (L j)) n)
        (isCoherent_twistedModuleUlift_of_isProper.{u, w} k B hk Z (i.hom ≫ f) hfZ _ G hG n) := by
  intro hfZ
  rw [eulerCharacteristic_eq_finsum, eulerCharacteristic_eq_finsum]
  refine finsum_congr fun q => ?_
  congr 2
  let fX : X ⟶ (⟨yoneda.obj (baseObject k B hk),
      isAlgebraicSpace_yoneda B (Spec (.of k)) hk (baseObject k B hk)⟩ :
        AlgebraicSpaces B (Spec (.of k)) hk) := ObjectProperty.homMk f
  have e := twistedCohomologyRestrictScalarsIsoOfAcyclic (baseObject k B hk) fX i L G
    (fun p hp => isZero_rightDerived_modulePushforward_of_isQuasicoherentOnSite B (Spec (.of k)) hk
      i (isAffineHom_of_isClosedImmersion B (Spec (.of k)) hk _ hi) G hG.toIsQuasicoherentOnSite
      p hp) n q
  exact ((finrank_cohomologyOverBase_uliftForPresentation.{u, w} B k hk X.1 X.2 _ q).trans
    e.toLinearEquiv.finrank_eq).trans
      (finrank_cohomologyOverBase_uliftForPresentation.{u, w} B k hk Z.1 Z.2 _ q).symm

end AlgebraicGeometry.Space

end
