module

public import StacksFrontier.AlgebraicGeometry.BaseAdicFiltration.AdicStageSpecialFibre
public import StacksFrontier.AlgebraicGeometry.BaseAdicFiltration.AdicStageSquareZero
public import StacksFrontier.AlgebraicGeometry.BaseAdicFiltration.SpecialFibreTransport
public import StacksFrontier.AlgebraicGeometry.ClosedPushforward.Basic

/-!
# The kernel of one adic step, named on the stage as a sum of copies of the special fibre

Let `A` be an Artinian local ring with maximal ideal `𝔪` and residue field `κ`, let
`p : U ⟶ Spec A` be flat, and let `i_X : X ⟶ U` be the closed immersion of the special fibre. The
step `Uₙ ⊆ Uₙ₊₁` of the `𝔪`-adic tower is a square-zero extension `E` of `𝒪_{Uₙ}` over `Spec A`
whose kernel is, on the stage `Uₙ` itself,

```
E.I  ≅  ⨁_{i < k} (i_{X,n})_* 𝒪_X,        k = dim_κ 𝔪ⁿ⁺¹/𝔪ⁿ⁺²,
```

where `i_{X,n} : X ⟶ Uₙ` is the inclusion of the special fibre into the stage.

## Main definitions

* `Stacks.BaseAdicFiltration.pushforwardAdicStageLiftIso`: the direct image to `U` of a module on
  the special fibre, computed through the stage `n`.

## Main results

* `Stacks.BaseAdicFiltration.exists_isoDirectSum_squareZeroExtension_adicStage_unit`: one step
  of the adic tower as a square-zero extension whose kernel is, on the stage itself, a finite
  direct sum of copies of the direct image of `𝒪_X`.
* `Stacks.BaseAdicFiltration.exists_isoDirectSum_squareZeroExtension_adicStage_unit_of_eq`: the
  same, for a structure morphism of the stage equal to
  `Stacks.BaseAdicFiltration.adicStageToBase`.

## References

* [Stacks Project, Tag 0E3X](https://stacks.math.columbia.edu/tag/0E3X)
* [Stacks Project, Tag 05YV](https://stacks.math.columbia.edu/tag/05YV)
* [Stacks Project, Tag 08KS](https://stacks.math.columbia.edu/tag/08KS)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.BaseAdicFiltration

/-- Sheaves of modules on a scheme have finite biproducts. -/
local instance hasFiniteBiproducts_adicStageKernel (W : Scheme.{u}) :
    HasFiniteBiproducts W.Modules :=
  HasFiniteBiproducts.of_hasFiniteProducts

variable {A : Type u} [CommRing A] {U X : Scheme.{u}} (p : U ⟶ Spec (CommRingCat.of A))
  (I : Ideal A) (iX : X ⟶ U) [IsClosedImmersion iX] (hk : iX.ker = baseIdeal p I)

/-- The direct image to `U` of a module on the special fibre, computed through the stage `n`:
pushing forward along the inclusion of the special fibre into the stage and then along the
immersion of the stage is pushing forward along the given closed immersion `i_X`. -/
def pushforwardAdicStageLiftIso (n : ℕ) (M : X.Modules) :
    (Scheme.Modules.pushforward (adicStageι p I n)).obj
        ((Scheme.Modules.pushforward (adicStageLift p I iX hk n)).obj M) ≅
      (Scheme.Modules.pushforward iX).obj M :=
  (Scheme.Modules.pushforwardComp (adicStageLift p I iX hk n) (adicStageι p I n)).app M ≪≫
    eqToIso (congrArg (fun φ : X ⟶ U => (Scheme.Modules.pushforward φ).obj M)
      (adicStageLift_comp_adicStageι p I iX hk n))

/-- **One step of the adic tower as a square-zero extension whose kernel is named on the stage.**
For a family `p : U ⟶ Spec A` flat over an Artinian local base and a closed immersion
`i_X : X ⟶ U` cutting out the special fibre, the stage `n` of the `𝔪`-adic tower carries a
square-zero extension of its structure sheaf over `Spec A`, realized by the stage `n + 1`, whose
kernel is a finite direct sum of `k = dim_κ 𝔪ⁿ⁺¹/𝔪ⁿ⁺²` copies of the direct image of `𝒪_X` along
the inclusion of the special fibre into the stage. -/
theorem exists_isoDirectSum_squareZeroExtension_adicStage_unit [IsArtinianRing A] [IsLocalRing A]
    [AlgebraicGeometry.Flat p] (hkm : iX.ker = baseIdeal p (IsLocalRing.maximalIdeal A)) (n : ℕ) :
    ∃ (E : Stacks.Thickenings.SquareZeroExtension
        (adicStageToBase p (IsLocalRing.maximalIdeal A) n)) (k : ℕ),
      Nonempty (E.I ≅ ⨁ fun _ : Fin k =>
          (Scheme.Modules.pushforward
            (adicStageLift p (IsLocalRing.maximalIdeal A) iX hkm n)).obj
              (SheafOfModules.unit X.ringCatSheaf)) ∧
        ∃ r : Stacks.Thickenings.Realization E,
          r.ambient = adicStage p (IsLocalRing.maximalIdeal A) (n + 1) ∧
            HEq r.immersion (adicStageSucc p (IsLocalRing.maximalIdeal A) n) ∧
              HEq r.toBase (adicStageToBase p (IsLocalRing.maximalIdeal A) (n + 1)) := by
  obtain ⟨E, ⟨e⟩, r, hamb, him, htb⟩ :=
    exists_squareZeroExtension_adicStage_gradedPiece p (IsLocalRing.maximalIdeal A) n
  obtain ⟨k, ⟨d⟩⟩ := exists_isoDirectSum_gradedPiece_unit p (n + 1)
  refine ⟨E, k, ⟨?_⟩, r, hamb, him, htb⟩
  refine (Stacks.ClosedImmersion.fullyFaithfulPushforward
    (adicStageι p (IsLocalRing.maximalIdeal A) n)).preimageIso ?_
  refine e ≪≫ d.symm ≪≫ ?_
  refine biproduct.mapIso (fun _ : Fin k =>
    specialFibreIsoPushforwardUnit p (IsLocalRing.maximalIdeal A) iX hkm ≪≫
      (pushforwardAdicStageLiftIso p (IsLocalRing.maximalIdeal A) iX hkm n
        (SheafOfModules.unit X.ringCatSheaf)).symm) ≪≫ ?_
  exact ((Scheme.Modules.pushforward
    (adicStageι p (IsLocalRing.maximalIdeal A) n)).mapBiproduct
      (fun _ : Fin k => (Scheme.Modules.pushforward
        (adicStageLift p (IsLocalRing.maximalIdeal A) iX hkm n)).obj
          (SheafOfModules.unit X.ringCatSheaf))).symm

/-- **One step of the adic tower as a square-zero extension whose kernel is named on the stage,
for a structure morphism `kk` of the stage equal to `Stacks.BaseAdicFiltration.adicStageToBase`.**
The stage `n` carries a square-zero extension over `kk`, realized by the stage `n + 1`, whose
kernel is a finite direct sum of copies of the direct image of `𝒪_X` along the inclusion of the
special fibre into the stage. -/
theorem exists_isoDirectSum_squareZeroExtension_adicStage_unit_of_eq [IsArtinianRing A]
    [IsLocalRing A] [AlgebraicGeometry.Flat p]
    (hkm : iX.ker = baseIdeal p (IsLocalRing.maximalIdeal A)) (n : ℕ)
    {kk : adicStage p (IsLocalRing.maximalIdeal A) n ⟶ Spec (CommRingCat.of A)}
    (hkk : kk = adicStageToBase p (IsLocalRing.maximalIdeal A) n) :
    ∃ (E : Stacks.Thickenings.SquareZeroExtension kk) (k : ℕ),
      Nonempty (E.I ≅ ⨁ fun _ : Fin k =>
          (Scheme.Modules.pushforward
            (adicStageLift p (IsLocalRing.maximalIdeal A) iX hkm n)).obj
              (SheafOfModules.unit X.ringCatSheaf)) ∧
        ∃ r : Stacks.Thickenings.Realization E,
          r.ambient = adicStage p (IsLocalRing.maximalIdeal A) (n + 1) ∧
            HEq r.immersion (adicStageSucc p (IsLocalRing.maximalIdeal A) n) ∧
              HEq r.toBase (adicStageToBase p (IsLocalRing.maximalIdeal A) (n + 1)) := by
  subst hkk
  exact exists_isoDirectSum_squareZeroExtension_adicStage_unit p iX hkm n

end Stacks.BaseAdicFiltration

end
