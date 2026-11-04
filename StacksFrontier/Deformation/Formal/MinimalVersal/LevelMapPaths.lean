module

public import StacksFrontier.Deformation.Formal.MinimalVersal.LevelMaps

/-!
# Compatibility of the level arrows with composite transitions

The arrows from the filtered levels into the levels of the original formal object are compatible
with the composite transition morphisms on both sides, and lie over the projections of the
filtration quotients onto the adic truncations. This yields, for every `n`, an arrow from the
filtered level at the chosen index into the `n`-th level of the original object.

## Main definitions

* `Deformation.stageFilteredLevelToOriginal`: the arrow from the filtered level at index
  `toAdicIndex I n` into the `n`-th level of the formal object.

## Main results

* `Deformation.formalObjectPath_succ`: `formalObjectPath` from a successor is the transition
  morphism followed by the shorter path.
* `Deformation.formalObjectPath_comp`: the composite transition morphisms of a formal object
  compose.
* `Deformation.stageFilteredLevelMapAtStage_path_naturality`: the arrows
  `stageFilteredLevelMapAtStage` commute with the composite transition morphisms on both sides.
* `Deformation.stageFilteredLevelMapAtStage_path_lift`: `stageFilteredLevelMapAtStage` followed
  by a composite transition morphism lies over the projection of the quotient onto the adic
  truncation.
* `Deformation.stageFilteredLevelToOriginal_naturality`: the arrows `stageFilteredLevelToOriginal`
  commute with the transition morphisms on both sides.

## References

* [Stacks Project, Tag 06T2](https://stacks.math.columbia.edu/tag/06T2)
-/

@[expose] public section

open CategoryTheory IsLocalRing

universe u v w uF vF

namespace Deformation

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
variable {F : Type uF} [Category.{vF} F]
variable {p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k}


/-- The composite transition morphism from a level to itself is the identity. -/
private theorem formalObjectPath_self (ξ : FormalObject p) (a : ℕ) :
    formalObjectPath ξ a a le_rfl = 𝟙 (ξ.level a) := by
  simp [formalObjectPath, Nat.leRecOn_self]

section
variable [IsNoetherianRing Λ] [Module.Finite Λ k]
omit [IsNoetherianRing Λ] [Module.Finite Λ k] in
/-- `formalObjectPath` from a successor is the transition morphism followed by the shorter path. -/
theorem formalObjectPath_succ
    (ξ : FormalObject p) (a b : ℕ) (hab : a ≤ b) :
    formalObjectPath ξ a (b + 1) (hab.trans (Nat.le_succ b)) =
      ξ.transition b ≫ formalObjectPath ξ a b hab := by
  unfold formalObjectPath
  exact Nat.leRecOn_succ hab _

omit [IsNoetherianRing Λ] [Module.Finite Λ k] in
/-- The composite transition morphisms of a formal object compose. -/
theorem formalObjectPath_comp
    (ξ : FormalObject p) {a b c : ℕ} (hab : a ≤ b) (hbc : b ≤ c) :
    formalObjectPath ξ b c hbc ≫ formalObjectPath ξ a b hab =
      formalObjectPath ξ a c (hab.trans hbc) := by
  induction c, hbc using Nat.le_induction with
  | base => simp [formalObjectPath_self]
  | succ c hbc ih =>
      rw [formalObjectPath_succ ξ b c hbc, formalObjectPath_succ ξ a c (hab.trans hbc),
        Category.assoc, ih]

/-- The arrows `stageFilteredLevelMapAtStage` commute with the composite transition morphisms on
both sides. -/
theorem stageFilteredLevelMapAtStage_path_naturality
    (hp : IsCofiberedInGroupoids p)
    (hS1 : SchlessingerConditionS1 p)
    (ξ : FormalObject p)
    (hbound : ∃ d : ℕ, ∀ n,
      Module.finrank (ResidueField (stageBaseTower hp hS1 ξ n))
        (CotangentSpace (stageBaseTower hp hS1 ξ n)) ≤ d)
    {a b : ℕ} (hab : a ≤ b) :
    let X := minimalStagesFilteredFormalObject hp hS1 ξ hbound
    filteredObjectPath (stageBaseTowerIdealFiltration hp hS1 ξ hbound) X hab ≫
        stageFilteredLevelMapAtStage hp hS1 ξ hbound a =
      stageFilteredLevelMapAtStage hp hS1 ξ hbound b ≫
        formalObjectPath ξ a b hab := by
  classical
  dsimp only
  induction b, hab using Nat.le_induction with
  | base =>
      simp [filteredObjectPath, formalObjectPath, Nat.leRecOn_self]
  | succ b hab ih =>
      rw [filteredObjectPath_succ _ _ a b hab, formalObjectPath_succ ξ a b hab, Category.assoc,
        ih, ← Category.assoc, stageFilteredLevelMapAtStage_naturality hp hS1 ξ hbound b,
        Category.assoc]

/-- `stageFilteredLevelMapAtStage` followed by a composite transition morphism lies over the
projection of the quotient onto the adic truncation. -/
theorem stageFilteredLevelMapAtStage_path_lift
    (hp : IsCofiberedInGroupoids p)
    (hS1 : SchlessingerConditionS1 p)
    (ξ : FormalObject p)
    (hbound : ∃ d : ℕ, ∀ n,
      Module.finrank (ResidueField (stageBaseTower hp hS1 ξ n))
        (CotangentSpace (stageBaseTower hp hS1 ξ n)) ≤ d)
    (n : ℕ) :
    let I := stageBaseTowerIdealFiltration hp hS1 ξ hbound
    let X := minimalStagesFilteredFormalObject hp hS1 ξ hbound
    let b := toAdicIndex I n
    p.map (stageFilteredLevelMapAtStage hp hS1 ξ hbound b ≫
      formalObjectPath ξ n b (toAdicIndex_ge I n)) ≫
        eqToHom (ξ.level_eq n) =
      eqToHom (X.level_eq b) ≫
        stageFormalQuotientToAdic hp hS1 ξ hbound n ≫
        (AdicTruncation.functor n).map
          (stageBaseTowerBaseHom hp hS1 ξ hbound) := by
  classical
  dsimp only
  let I := stageBaseTowerIdealFiltration hp hS1 ξ hbound
  let X := minimalStagesFilteredFormalObject hp hS1 ξ hbound
  let M := minimalStages hp hS1 ξ (toAdicIndex I n)
  let b := toAdicIndex I n
  have hM : p.obj M.obj.left = stageBaseTower hp hS1 ξ b := rfl
  let hnb : n ≤ b := toAdicIndex_ge I n
  let e := stageBaseTowerQuotientIso hp hS1 ξ hbound b
  let q := stageFormalQuotientToAdic hp hS1 ξ hbound n
  let α := stageFilteredLevelMapAtStage hp hS1 ξ hbound b
  let v := formalObjectPath ξ n b hnb
  let π := inverseLimitProj (stageBaseTower hp hS1 ξ)
    (stageBaseTowerTransition hp hS1 ξ)
  have hmid : e.hom ≫ stageTowerPath hp hS1 ξ n b hnb ≫
        stageBaseTowerInclusion hp hS1 ξ n ≫ eqToHom (ξ.level_eq n) =
      q ≫ (AdicTruncation.functor n).map
        (stageBaseTowerBaseHom hp hS1 ξ hbound) := by
    apply ArtinianLocalAlgCat.hom_ext
    apply AlgHom.ext
    intro z
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective z
    let zInv : inverseLimit (stageBaseTower hp hS1 ξ)
        (stageBaseTowerTransition hp hS1 ξ) := r
    have he := stageBaseTowerQuotientIso_mk hp hS1 ξ hbound b r
    have hbaseq := congrArg (fun f : inverseLimit (stageBaseTower hp hS1 ξ)
        (stageBaseTowerTransition hp hS1 ξ) →ₐ[Λ]
          AdicTruncation.obj ξ.base n => f r)
      (stageBaseTowerBaseHom_quotient hp hS1 ξ hbound n)
    change (Ideal.Quotient.mk (AdicTruncation.ideal ξ.base n)
          ((stageBaseTowerBaseHom hp hS1 ξ hbound).hom r)) =
        (formalInverseLimitCoordinate ξ n)
          (stageBaseInverseLimitMap hp hS1 ξ r) at hbaseq
    change (eqToHom (ξ.level_eq n)).hom
        ((stageBaseTowerInclusion hp hS1 ξ n).hom
          ((stageTowerPath hp hS1 ξ n b hnb).hom
            (e.hom.hom (Ideal.Quotient.mk (I.ideal b) r)))) =
      ((AdicTruncation.functor n).map (stageBaseTowerBaseHom hp hS1 ξ hbound)).hom
        (q.hom (Ideal.Quotient.mk (I.ideal b) r))
    have hcoord := stageTowerPath_coordinate hp hS1 ξ zInv n b hnb
    rw [he]
    have hπ : π b r = zInv.1 b := rfl
    rw [hπ, hcoord]
    simp only [stageBaseTowerInclusion]
    rw [stageFormalQuotientToAdic_mk]
    have hbaseq' := hbaseq.symm
    change (eqToHom (ξ.level_eq n)).hom
        ((stageBaseTowerInclusion hp hS1 ξ n).hom (π n r)) =
      Ideal.Quotient.mk (AdicTruncation.ideal ξ.base n)
        ((stageBaseTowerBaseHom hp hS1 ξ hbound).hom r) at hbaseq'
    exact hbaseq'
  calc
    p.map (α ≫ v) ≫ eqToHom (ξ.level_eq n) =
        (p.map α ≫ p.map v) ≫ eqToHom (ξ.level_eq n) := by
          rw [Functor.map_comp]
    _ = (stageFilteredLevelMapBaseAtStage hp hS1 ξ hbound b ≫
          p.map v) ≫ eqToHom (ξ.level_eq n) := by
          rw [stageFilteredLevelMapAtStage_map]
    _ = (eqToHom (X.level_eq b) ≫ e.hom ≫
          stageBaseTowerInclusion hp hS1 ξ b ≫ p.map v) ≫
          eqToHom (ξ.level_eq n) := by
          rw [stageFilteredLevelMapBaseAtStage_fac]
          cat_disch
    _ = _ := by
          simp only [v]
          calc
            _ = eqToHom (X.level_eq b) ≫
                (e.hom ≫ (stageBaseTowerInclusion hp hS1 ξ b ≫
                    p.map (formalObjectPath ξ n b hnb)) ≫
                  eqToHom (ξ.level_eq n)) := by cat_disch
            _ = eqToHom (X.level_eq b) ≫
                (e.hom ≫ (stageTowerPath hp hS1 ξ n b hnb ≫
                    stageBaseTowerInclusion hp hS1 ξ n) ≫
                  eqToHom (ξ.level_eq n)) := by
                    rw [← stageBaseTowerInclusion_path hp hS1 ξ n b hnb]
            _ = eqToHom (X.level_eq b) ≫
                (q ≫ (AdicTruncation.functor n).map
                  (stageBaseTowerBaseHom hp hS1 ξ hbound)) := by
                    simpa only [Category.assoc] using
                      congrArg (fun f => eqToHom (X.level_eq b) ≫ f) hmid
            _ = _ := by cat_disch

/-- The arrow from the filtered level at index `toAdicIndex I n` into the `n`-th level of the
formal object. -/
noncomputable def stageFilteredLevelToOriginal
    (hp : IsCofiberedInGroupoids p)
    (hS1 : SchlessingerConditionS1 p)
    (ξ : FormalObject p)
    (hbound : ∃ d : ℕ, ∀ n,
      Module.finrank (ResidueField (stageBaseTower hp hS1 ξ n))
        (CotangentSpace (stageBaseTower hp hS1 ξ n)) ≤ d)
    (n : ℕ) :
    (minimalStagesFilteredFormalObject hp hS1 ξ hbound).level
        (toAdicIndex (stageBaseTowerIdealFiltration hp hS1 ξ hbound) n) ⟶
      ξ.level n := by
  classical
  let I := stageBaseTowerIdealFiltration hp hS1 ξ hbound
  let b := toAdicIndex (stageBaseTowerIdealFiltration hp hS1 ξ hbound) n
  exact stageFilteredLevelMapAtStage hp hS1 ξ hbound b ≫
    formalObjectPath ξ n b (toAdicIndex_ge
      (stageBaseTowerIdealFiltration hp hS1 ξ hbound) n)

/-- The arrows `stageFilteredLevelToOriginal` commute with the transition morphisms on both sides.
The arrows `stageFilteredLevelToOriginal` commute with the transition morphisms on both sides. -/
theorem stageFilteredLevelToOriginal_naturality
    (hp : IsCofiberedInGroupoids p)
    (hS1 : SchlessingerConditionS1 p)
    (ξ : FormalObject p)
    (hbound : ∃ d : ℕ, ∀ n,
      Module.finrank (ResidueField (stageBaseTower hp hS1 ξ n))
        (CotangentSpace (stageBaseTower hp hS1 ξ n)) ≤ d)
    (n : ℕ) :
    filteredObjectPath (stageBaseTowerIdealFiltration hp hS1 ξ hbound)
        (minimalStagesFilteredFormalObject hp hS1 ξ hbound)
        (toAdicIndex_mono
          (stageBaseTowerIdealFiltration hp hS1 ξ hbound) (Nat.le_succ n)) ≫
        stageFilteredLevelToOriginal hp hS1 ξ hbound n =
      stageFilteredLevelToOriginal hp hS1 ξ hbound (n + 1) ≫ ξ.transition n := by
  let I := stageBaseTowerIdealFiltration hp hS1 ξ hbound
  let X := minimalStagesFilteredFormalObject hp hS1 ξ hbound
  let a := toAdicIndex (stageBaseTowerIdealFiltration hp hS1 ξ hbound) n
  let b := toAdicIndex (stageBaseTowerIdealFiltration hp hS1 ξ hbound) (n + 1)
  have hab : a ≤ b := toAdicIndex_mono I (Nat.le_succ n)
  have hna : n ≤ a := toAdicIndex_ge I n
  have hsb : n + 1 ≤ b := toAdicIndex_ge I (n + 1)
  have hnat := stageFilteredLevelMapAtStage_path_naturality hp hS1 ξ hbound hab
  change filteredObjectPath I X hab ≫
      (stageFilteredLevelMapAtStage hp hS1 ξ hbound a ≫
        formalObjectPath ξ n a hna) =
    (stageFilteredLevelMapAtStage hp hS1 ξ hbound b ≫
      formalObjectPath ξ (n + 1) b hsb) ≫ ξ.transition n
  have hstep : formalObjectPath ξ n (n + 1) (Nat.le_succ n) = ξ.transition n := by
    rw [formalObjectPath_succ ξ n n le_rfl, formalObjectPath_self, Category.comp_id]
  rw [← Category.assoc, hnat, Category.assoc, formalObjectPath_comp, Category.assoc,
    ← formalObjectPath_comp ξ (Nat.le_succ n) hsb, hstep]

end

end Deformation

end
