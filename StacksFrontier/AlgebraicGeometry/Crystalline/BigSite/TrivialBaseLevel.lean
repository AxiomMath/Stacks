module

public import StacksFrontier.AlgebraicGeometry.Crystalline.BigLevelBase
public import StacksFrontier.AlgebraicGeometry.Crystalline.BigSite.TrivialBaseSituation

/-!
# The closed fibre `S₀` over the finite levels `S_e`

For a global crystalline situation `(p, (S, I, γ), X)` with affine base and a finite divided power
level `e` (`(p^e) ⊆ I` preserved by `γ`), the divided power morphism `(S₀, 0, 0) ⟶ (S, I, γ)` of
`Crystalline.GlobalCrystallineSituation.closedFiberToBaseHom` factors through the level
`S_e = Spec(A/p^eA)`, because `p^e ∈ I` vanishes on `S₀`.  The factorization is a morphism
`S₀ ⟶ S_e` of divided power schemes over `S`, and the closed-fibre square of the pair
`(S₀ ⟶ S_e, 𝟙_X)` commutes, which is the hypothesis change of divided power base from `X/S₀` to
`X/S_e` takes.

## Main definitions

* `Crystalline.GlobalCrystallineSituation.trivialBaseToLevel` — the divided power morphism
  `S₀ ⟶ S_e`.

## Main results

* `Crystalline.GlobalCrystallineSituation.trivialBaseToLevel_comp_levelProj` — it lies over `S`.
* `Crystalline.GlobalCrystallineSituation.trivialBaseToLevel_condition` — the closed-fibre square
  of `(S₀ ⟶ S_e, 𝟙_X)`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped AlgebraicGeometry

universe u

namespace Crystalline.GlobalCrystallineSituation

variable (S : GlobalCrystallineSituation.{u}) [IsAffine S.S.scheme]

omit [IsAffine S.S.scheme] in
/-- **`p^e` vanishes on the closed fibre `S₀`** at a finite divided power level `e`, since
`p^e ∈ I`. -/
theorem natCast_pow_eq_zero_closedFiber {e : ℕ} (he : S.IsLevel e) :
    ((S.p : ℕ) : Γ((trivialDividedPowerScheme (DividedPowerScheme.closedFiber S.S)).scheme, ⊤)) ^
      e = 0 := by
  have hmem : ((S.p : ℕ) : Γ(S.S.scheme, ⊤)) ^ e ∈ S.baseIdeal := by
    refine he.1 ?_
    rw [DividedPowers.pAdicIdeal, Ideal.span_singleton_pow]
    exact Ideal.mem_span_singleton_self _
  have h := (DividedPowerScheme.closedFiberPresentation S.S).app_eq_zero_of_mem ⊤ _ hmem
  rw [map_pow, map_natCast] at h
  exact h

variable {S} in
/-- **The divided power morphism `S₀ ⟶ S_e`**: the factorization of `S₀ ⟶ S` through the level
`S_e`, `p^e` vanishing on `S₀`. -/
def trivialBaseToLevel {e : ℕ} (he : S.IsLevel e) :
    (trivialBaseSituation S).S ⟶ (S.levelSituation he).S :=
  S.levelLift he (closedFiberToBaseHom S) (S.natCast_pow_eq_zero_closedFiber he)

/-- **`S₀ ⟶ S_e ⟶ S` is `S₀ ⟶ S`.** -/
@[reassoc (attr := simp)]
theorem trivialBaseToLevel_comp_levelProj {e : ℕ} (he : S.IsLevel e) :
    trivialBaseToLevel he ≫ S.levelProj he = closedFiberToBaseHom S :=
  S.levelLift_comp_levelProj he _ _

/-- The map on closed fibres of `S_e ⟶ S` is a monomorphism, `S_e ⟶ S` being a closed
immersion. -/
instance mono_closedFiberMap_levelProj {e : ℕ} (he : S.IsLevel e) :
    Mono (DividedPowerScheme.closedFiberMap (S.levelProj he)) := by
  have : IsIso S.baseSpecIso.hom.hom :=
    ⟨⟨S.baseSpecIso.inv.hom, by
        rw [← DividedPowerScheme.Hom.comp_hom, Iso.hom_inv_id, DividedPowerScheme.Hom.id_hom],
      by rw [← DividedPowerScheme.Hom.comp_hom, Iso.inv_hom_id, DividedPowerScheme.Hom.id_hom]⟩⟩
  have : Mono (S.levelProj he).hom := by
    change Mono ((pAdicLevelSchemeProj S.baseIdeal S.baseDividedPowers S.p he).hom ≫
      S.baseSpecIso.hom.hom)
    infer_instance
  have : Mono (DividedPowerScheme.closedFiberι (S.levelSituation he).S) :=
    inferInstanceAs (Mono (DividedPowerScheme.closedFiberPresentation _).ι)
  have : Mono (DividedPowerScheme.closedFiberMap (S.levelProj he) ≫
      DividedPowerScheme.closedFiberι S.S) := by
    rw [DividedPowerScheme.closedFiberMap_comp_closedFiberι]
    infer_instance
  exact mono_of_mono _ (DividedPowerScheme.closedFiberι S.S)

/-- **The closed-fibre square of `(S₀ ⟶ S_e, 𝟙_X)` commutes**: the hypothesis taken by change of
divided power base from `X/S₀` to `X/S_e` along `S₀ ⟶ S_e` and the identity of `X`. -/
theorem trivialBaseToLevel_condition {e : ℕ} (he : S.IsLevel e) :
    (trivialBaseSituation S).toClosedFiber ≫
        DividedPowerScheme.closedFiberMap (trivialBaseToLevel he) =
      (𝟙 S.X : (trivialBaseSituation S).X ⟶ (S.levelSituation he).X) ≫
        (S.levelSituation he).toClosedFiber := by
  refine (cancel_mono (DividedPowerScheme.closedFiberMap (S.levelProj he))).1 ?_
  rw [Category.assoc, ← DividedPowerScheme.closedFiberMap_comp,
    trivialBaseToLevel_comp_levelProj, trivialBaseSituation_comm, Category.assoc,
    S.levelProj_condition he]
  simp only [Category.id_comp]

/-- **Change of divided power base from `X/S₀` to `X/S_e`** along `S₀ ⟶ S_e` and the identity of
`X`, [Stacks, Tag 07IC]. -/
abbrev trivialBaseLevelChangeBase {e : ℕ} (he : S.IsLevel e) :
    Thickening (trivialBaseSituation S) ⥤ Thickening (S.levelSituation he) :=
  changeBase (trivialBaseSituation S) (S.levelSituation he) (trivialBaseToLevel he) (𝟙 S.X)
    (S.trivialBaseToLevel_condition he)

end Crystalline.GlobalCrystallineSituation
