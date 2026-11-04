module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.MultiplicativeTorsorPointExistence
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackInvertible
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackRestriction

/-!
# Base change of the multiplicative torsor of an invertible sheaf

In Situation 0EDT let `X/B` be good, let `ℒ` be an invertible `𝒪_X`-module and let
`q : T ⟶ X` be its multiplicative torsor with `α : q^*ℒ ≅ 𝒪_T`.  For a morphism `g : Y ⟶ X` of
good algebraic spaces, `g^*ℒ` is invertible and has its own multiplicative torsor
`q_Y : T_Y ⟶ Y` with `α_Y : q_Y^*(g^*ℒ) ≅ 𝒪_{T_Y}`.  This file proves that the pair `(q, α)`
commutes with base change: there is a morphism `g' : T_Y ⟶ T` making the square
`g' ≫ q = q_Y ≫ g` cartesian, along which `α` pulls back to `α_Y`.

## Main results

* `AlgebraicGeometry.Space.torsorOfInvertible_baseChange`: **Stacks 0EQG, clause (3).**

## References

* [Stacks Project, Tag 0EQG](https://stacks.math.columbia.edu/tag/0EQG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

/-! ### A coherence for the comparison of pullbacks -/

section Coherence

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- `AlgebraicGeometry.Space.modulePullbackTriangle_comp_app`, applied to a trivialization along
`q_Y` followed by a morphism. -/
theorem modulePullbackTriangle_comp_app_map {Z TY Y X₀ : AlgebraicSpaces B S hS} (c : Z ⟶ TY)
    (qY : TY ⟶ Y) (gX : Y ⟶ X₀) (M : Modules.{u, u} B S hS X₀.1 X₀.2) {y : Z ⟶ Y}
    (hc : c ≫ qY = y) (h₁ : c ≫ (qY ≫ gX) = y ≫ gX) {N : Modules.{u, u} B S hS TY.1 TY.2}
    {W : Modules.{u, u} B S hS Z.1 Z.2}
    (αY : (modulePullback B S hS qY).obj ((modulePullback B S hS gX).obj M) ⟶ N)
    (U : (modulePullback B S hS c).obj N ⟶ W) :
    (modulePullbackTriangle B S hS h₁).hom.app M ≫
        ((modulePullback B S hS c).map
          ((modulePullbackTriangle B S hS (rfl : qY ≫ gX = qY ≫ gX)).hom.app M ≫ αY) ≫ U) =
      (modulePullbackTriangle B S hS (rfl : y ≫ gX = y ≫ gX)).hom.app M ≫
        ((modulePullbackTriangle B S hS hc).hom.app ((modulePullback B S hS gX).obj M) ≫
          ((modulePullback B S hS c).map αY ≫ U)) := by
  rw [Functor.map_comp, Category.assoc, ← Category.assoc,
    ← modulePullbackTriangle_comp_app (p := gX) hc rfl h₁ rfl M, Category.assoc]

end Coherence

/-- The trivialization of `x^*ℒ` induced by a point `t` of a multiplicative torsor over `x`,
written out; it refers to the names `D p hp L hL` given as arguments. -/
local macro "𝔱[" p:term ", " hp:term ", " L:term ", " hL:term ", " t:term ", " h:term "]" :
    term => do
  let D := Lean.mkIdent `D
  `((modulePullbackTriangle ($D).site ($D).base ($D).base_mem $h).hom.app $L ≫
    (((modulePullback ($D).site ($D).base ($D).base_mem $t).map
        (torsorOfInvertibleTrivialization $D $p $hp $L $hL).hom) ≫
      (modulePullbackUnitIso ($D).site ($D).base ($D).base_mem $t).hom))

variable (D : BaseSpaceDimensionSituation.{u})
    {X : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (p : X ⟶ D.space) (hp : D.IsGood p)
    (L : Modules.{u, u} D.site D.base D.base_mem X hp.1)
    (hL : IsInvertibleSheaf D p hp L)
    {Y : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u} (pY : Y ⟶ D.space) (hpY : D.IsGood pY)
    (g : (⟨Y, hpY.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) ⟶ ⟨X, hp.1⟩)

/-! ### The base change of the torsor -/

section BaseChange

/-- **The trivialization induced by a point of `T_Y`, read on `T`.**  If `g' : T_Y ⟶ T` lies
over `g` and pulls `α` back to `α_Y`, then for a point `c` of `T_Y` over `y` the point
`c ≫ g'` of `T` induces the trivialization of `(y ≫ g)^*ℒ = y^*(g^*ℒ)` induced by `c`. -/
theorem torsorTrivialization_comp_baseChange
    (g' : torsorOfInvertibleSpace D pY hpY ((modulePullback D.site D.base D.base_mem g).obj L)
        (isInvertible_modulePullback_obj D.site D.base D.base_mem g L hL) ⟶
      torsorOfInvertibleSpace D p hp L hL)
    (w : g' ≫ torsorOfInvertibleProjection D p hp L hL =
      torsorOfInvertibleProjection D pY hpY ((modulePullback D.site D.base D.base_mem g).obj L)
        (isInvertible_modulePullback_obj D.site D.base D.base_mem g L hL) ≫ g)
    (hg' : 𝔱[p, hp, L, hL, g', w] =
      (modulePullbackTriangle D.site D.base D.base_mem
        (rfl : torsorOfInvertibleProjection D pY hpY
          ((modulePullback D.site D.base D.base_mem g).obj L)
          (isInvertible_modulePullback_obj D.site D.base D.base_mem g L hL) ≫ g =
          torsorOfInvertibleProjection D pY hpY ((modulePullback D.site D.base D.base_mem g).obj L)
          (isInvertible_modulePullback_obj D.site D.base D.base_mem g L hL) ≫ g)).hom.app L ≫
        (torsorOfInvertibleTrivialization D pY hpY
          ((modulePullback D.site D.base D.base_mem g).obj L)
          (isInvertible_modulePullback_obj D.site D.base D.base_mem g L hL)).hom)
    {Z : AlgebraicSpaces D.site D.base D.base_mem}
    (c : Z ⟶ torsorOfInvertibleSpace D pY hpY ((modulePullback D.site D.base D.base_mem g).obj L)
      (isInvertible_modulePullback_obj D.site D.base D.base_mem g L hL))
    {y : Z ⟶ (⟨Y, hpY.1⟩ : AlgebraicSpaces D.site D.base D.base_mem)}
    (hc : c ≫ torsorOfInvertibleProjection D pY hpY
      ((modulePullback D.site D.base D.base_mem g).obj L)
      (isInvertible_modulePullback_obj D.site D.base D.base_mem g L hL) = y)
    (h : (c ≫ g') ≫ torsorOfInvertibleProjection D p hp L hL = y ≫ g) :
    𝔱[p, hp, L, hL, c ≫ g', h] =
      (modulePullbackTriangle D.site D.base D.base_mem (rfl : y ≫ g = y ≫ g)).hom.app L ≫
        𝔱[pY, hpY, (modulePullback D.site D.base D.base_mem g).obj L,
          isInvertible_modulePullback_obj D.site D.base D.base_mem g L hL, c, hc] := by
  have h' : c ≫ (torsorOfInvertibleProjection D pY hpY
      ((modulePullback D.site D.base D.base_mem g).obj L)
      (isInvertible_modulePullback_obj D.site D.base D.base_mem g L hL) ≫ g) = y ≫ g := by
    rw [← Category.assoc, hc]
  obtain ⟨hh, e⟩ := torsorLift_comp D p hp L hL _ w hg' c h'
  exact (triv_congr D p hp L hL rfl h hh).trans
    (e.trans (modulePullbackTriangle_comp_app_map D.site D.base D.base_mem c _ g L hc h' _ _))

/-- **The comparison morphism `T_Y ⟶ T` is compatible with cones**: a point of `T_Y` realizing
the transported trivialization of a cone maps to the first leg of the cone. -/
theorem baseChange_comp_eq
    (g' : torsorOfInvertibleSpace D pY hpY ((modulePullback D.site D.base D.base_mem g).obj L)
        (isInvertible_modulePullback_obj D.site D.base D.base_mem g L hL) ⟶
      torsorOfInvertibleSpace D p hp L hL)
    (w : g' ≫ torsorOfInvertibleProjection D p hp L hL =
      torsorOfInvertibleProjection D pY hpY ((modulePullback D.site D.base D.base_mem g).obj L)
        (isInvertible_modulePullback_obj D.site D.base D.base_mem g L hL) ≫ g)
    (hg' : 𝔱[p, hp, L, hL, g', w] =
      (modulePullbackTriangle D.site D.base D.base_mem
        (rfl : torsorOfInvertibleProjection D pY hpY
          ((modulePullback D.site D.base D.base_mem g).obj L)
        (isInvertible_modulePullback_obj D.site D.base D.base_mem g L hL) ≫ g =
          torsorOfInvertibleProjection D pY hpY ((modulePullback D.site D.base D.base_mem g).obj L)
        (isInvertible_modulePullback_obj D.site D.base D.base_mem g L hL) ≫ g)).hom.app L ≫
        (torsorOfInvertibleTrivialization D pY hpY
          ((modulePullback D.site D.base D.base_mem g).obj L)
        (isInvertible_modulePullback_obj D.site D.base D.base_mem g L hL)).hom)
    {Z : AlgebraicSpaces D.site D.base D.base_mem} (fst : Z ⟶ torsorOfInvertibleSpace D p hp L hL)
    (snd : Z ⟶ (⟨Y, hpY.1⟩ : AlgebraicSpaces D.site D.base D.base_mem))
    (cond : fst ≫ torsorOfInvertibleProjection D p hp L hL = snd ≫ g)
    (c : Z ⟶ torsorOfInvertibleSpace D pY hpY ((modulePullback D.site D.base D.base_mem g).obj L)
        (isInvertible_modulePullback_obj D.site D.base D.base_mem g L hL))
    (hc : c ≫ torsorOfInvertibleProjection D pY hpY
      ((modulePullback D.site D.base D.base_mem g).obj L)
        (isInvertible_modulePullback_obj D.site D.base D.base_mem g L hL) = snd)
    (hcβ : 𝔱[pY, hpY, (modulePullback D.site D.base D.base_mem g).obj L,
          isInvertible_modulePullback_obj D.site D.base D.base_mem g L hL, c, hc] =
      (modulePullbackTriangle D.site D.base D.base_mem (rfl : snd ≫ g = snd ≫ g)).inv.app L ≫
        𝔱[p, hp, L, hL, fst, cond]) :
    c ≫ g' = fst := by
  have h : (c ≫ g') ≫ torsorOfInvertibleProjection D p hp L hL = snd ≫ g := by
    rw [Category.assoc, w, ← Category.assoc, hc]
  refine torsorHom_eq_of_trivialization_eq D p hp L hL (c ≫ g') fst h cond ?_
  rw [torsorTrivialization_comp_baseChange D p hp L hL pY hpY g g' w hg' c hc h, hcβ,
    Iso.hom_inv_id_app_assoc]

/-- **Uniqueness of the lift into `T_Y`.** -/
theorem baseChange_hom_eq
    (g' : torsorOfInvertibleSpace D pY hpY ((modulePullback D.site D.base D.base_mem g).obj L)
        (isInvertible_modulePullback_obj D.site D.base D.base_mem g L hL) ⟶
      torsorOfInvertibleSpace D p hp L hL)
    (w : g' ≫ torsorOfInvertibleProjection D p hp L hL =
      torsorOfInvertibleProjection D pY hpY ((modulePullback D.site D.base D.base_mem g).obj L)
        (isInvertible_modulePullback_obj D.site D.base D.base_mem g L hL) ≫ g)
    (hg' : 𝔱[p, hp, L, hL, g', w] =
      (modulePullbackTriangle D.site D.base D.base_mem
        (rfl : torsorOfInvertibleProjection D pY hpY
          ((modulePullback D.site D.base D.base_mem g).obj L)
        (isInvertible_modulePullback_obj D.site D.base D.base_mem g L hL) ≫ g =
          torsorOfInvertibleProjection D pY hpY ((modulePullback D.site D.base D.base_mem g).obj L)
        (isInvertible_modulePullback_obj D.site D.base D.base_mem g L hL) ≫ g)).hom.app L ≫
        (torsorOfInvertibleTrivialization D pY hpY
          ((modulePullback D.site D.base D.base_mem g).obj L)
        (isInvertible_modulePullback_obj D.site D.base D.base_mem g L hL)).hom)
    {Z : AlgebraicSpaces D.site D.base D.base_mem} (fst : Z ⟶ torsorOfInvertibleSpace D p hp L hL)
    (snd : Z ⟶ (⟨Y, hpY.1⟩ : AlgebraicSpaces D.site D.base D.base_mem))
    (cond : fst ≫ torsorOfInvertibleProjection D p hp L hL = snd ≫ g)
    (m c : Z ⟶ torsorOfInvertibleSpace D pY hpY ((modulePullback D.site D.base D.base_mem g).obj L)
        (isInvertible_modulePullback_obj D.site D.base D.base_mem g L hL))
    (hm₁ : m ≫ g' = fst) (hm₂ : m ≫ torsorOfInvertibleProjection D pY hpY
      ((modulePullback D.site D.base D.base_mem g).obj L)
        (isInvertible_modulePullback_obj D.site D.base D.base_mem g L hL) = snd)
    (hc : c ≫ torsorOfInvertibleProjection D pY hpY
      ((modulePullback D.site D.base D.base_mem g).obj L)
        (isInvertible_modulePullback_obj D.site D.base D.base_mem g L hL) = snd)
    (hcβ : 𝔱[pY, hpY, (modulePullback D.site D.base D.base_mem g).obj L,
          isInvertible_modulePullback_obj D.site D.base D.base_mem g L hL, c, hc] =
      (modulePullbackTriangle D.site D.base D.base_mem (rfl : snd ≫ g = snd ≫ g)).inv.app L ≫
        𝔱[p, hp, L, hL, fst, cond]) :
    m = c := by
  have h : (m ≫ g') ≫ torsorOfInvertibleProjection D p hp L hL = snd ≫ g := by
    rw [hm₁, cond]
  have e := (triv_congr D p hp L hL hm₁ h cond).symm.trans
    (torsorTrivialization_comp_baseChange D p hp L hL pY hpY g g' w hg' m hm₂ h)
  refine torsorHom_eq_of_trivialization_eq D pY hpY _ _ m c hm₂ hc ?_
  rw [hcβ, e, Iso.inv_hom_id_app_assoc]

/-- **Stacks 0EQG, clause (3): formation of `(q : T ⟶ X, α)` commutes with base change.**  For a
morphism `g : Y ⟶ X` of good algebraic spaces, let `q_Y : T_Y ⟶ Y` and
`α_Y : q_Y^*(g^*ℒ) ≅ 𝒪_{T_Y}` be the multiplicative torsor of the invertible `𝒪_Y`-module
`g^*ℒ`.  There is a morphism `g' : T_Y ⟶ T` with `g' ≫ q = q_Y ≫ g` such that the square is
cartesian and `α` pulls back along `g'` to `α_Y`: the trivialization `g'^*α` of
`(g' ≫ q)^*ℒ = (q_Y ≫ g)^*ℒ` is `α_Y` composed with the canonical identification
`(q_Y ≫ g)^*ℒ ≅ q_Y^*(g^*ℒ)` of Stacks 03LU. -/
@[stacks 0EQG "clause (3): in Situation 0EDT with X/B good and L an invertible O_X-module, for
every morphism g : Y ⟶ X of good algebraic spaces the multiplicative torsor (q_Y : T_Y ⟶ Y,
alpha_Y) of g^*L, with T_Y = Spec_Y(⨁_n (g^*L)^{⊗n}), is the base change of (q : T ⟶ X, alpha):
there is g' : T_Y ⟶ T over g making the square cartesian and pulling alpha back to alpha_Y"]
theorem torsorOfInvertible_baseChange :
    ∃ (g' : torsorOfInvertibleSpace D pY hpY ((modulePullback D.site D.base D.base_mem g).obj L)
        (isInvertible_modulePullback_obj D.site D.base D.base_mem g L hL) ⟶
        torsorOfInvertibleSpace D p hp L hL)
      (w : g' ≫ torsorOfInvertibleProjection D p hp L hL =
        torsorOfInvertibleProjection D pY hpY ((modulePullback D.site D.base D.base_mem g).obj L)
        (isInvertible_modulePullback_obj D.site D.base D.base_mem g L hL) ≫ g),
      IsPullback g' (torsorOfInvertibleProjection D pY hpY
        ((modulePullback D.site D.base D.base_mem g).obj L)
        (isInvertible_modulePullback_obj D.site D.base D.base_mem g L hL))
          (torsorOfInvertibleProjection D p hp L hL) g ∧
        𝔱[p, hp, L, hL, g', w] =
          (modulePullbackTriangle D.site D.base D.base_mem
            (rfl : torsorOfInvertibleProjection D pY hpY
              ((modulePullback D.site D.base D.base_mem g).obj L)
        (isInvertible_modulePullback_obj D.site D.base D.base_mem g L hL) ≫ g =
              torsorOfInvertibleProjection D pY hpY
                ((modulePullback D.site D.base D.base_mem g).obj L)
        (isInvertible_modulePullback_obj D.site D.base D.base_mem g L hL) ≫ g)).hom.app L ≫
            (torsorOfInvertibleTrivialization D pY hpY
              ((modulePullback D.site D.base D.base_mem g).obj L)
        (isInvertible_modulePullback_obj D.site D.base D.base_mem g L hL)).hom := by
  obtain ⟨g', w, hg'⟩ := exists_torsorLift D p hp L hL (torsorOfInvertibleProjection D pY hpY
    ((modulePullback D.site D.base D.base_mem g).obj L)
        (isInvertible_modulePullback_obj D.site D.base D.base_mem g L hL) ≫ g)
    ((modulePullbackTriangle D.site D.base D.base_mem
      (rfl : torsorOfInvertibleProjection D pY hpY
        ((modulePullback D.site D.base D.base_mem g).obj L)
        (isInvertible_modulePullback_obj D.site D.base D.base_mem g L hL) ≫ g =
        torsorOfInvertibleProjection D pY hpY ((modulePullback D.site D.base D.base_mem g).obj L)
        (isInvertible_modulePullback_obj D.site D.base D.base_mem g L hL) ≫ g)).app L ≪≫
      torsorOfInvertibleTrivialization D pY hpY ((modulePullback D.site D.base D.base_mem g).obj L)
        (isInvertible_modulePullback_obj D.site D.base D.base_mem g L hL))
  rw [Iso.trans_hom, Iso.app_hom] at hg'
  have hlift : ∀ s : PullbackCone (torsorOfInvertibleProjection D p hp L hL) g,
      ∃ (c : s.pt ⟶ torsorOfInvertibleSpace D pY hpY
        ((modulePullback D.site D.base D.base_mem g).obj L)
        (isInvertible_modulePullback_obj D.site D.base D.base_mem g L hL))
        (hc : c ≫ torsorOfInvertibleProjection D pY hpY
          ((modulePullback D.site D.base D.base_mem g).obj L)
        (isInvertible_modulePullback_obj D.site D.base D.base_mem g L hL) = s.snd),
        𝔱[pY, hpY, (modulePullback D.site D.base D.base_mem g).obj L,
          isInvertible_modulePullback_obj D.site D.base D.base_mem g L hL, c, hc] =
          (modulePullbackTriangle D.site D.base D.base_mem
            (rfl : s.snd ≫ g = s.snd ≫ g)).inv.app L ≫
            𝔱[p, hp, L, hL, s.fst, s.condition] := by
    intro s
    obtain ⟨c, hc, e⟩ := exists_torsorLift D pY hpY _
      (isInvertible_modulePullback_obj D.site D.base D.base_mem g L hL) s.snd
      (((modulePullbackTriangle D.site D.base D.base_mem
        (rfl : s.snd ≫ g = s.snd ≫ g)).app L).symm ≪≫
        ((modulePullbackTriangle D.site D.base D.base_mem s.condition).app L ≪≫
          (modulePullback D.site D.base D.base_mem s.fst).mapIso
            (torsorOfInvertibleTrivialization D p hp L hL) ≪≫
          modulePullbackUnitIso D.site D.base D.base_mem s.fst))
    refine ⟨c, hc, e.trans ?_⟩
    rw [Iso.trans_hom, Iso.trans_hom, Iso.trans_hom, Iso.symm_hom, Iso.app_inv, Iso.app_hom,
      Functor.mapIso_hom]
  obtain ⟨lift, hl⟩ := Classical.skolem.mp hlift
  refine ⟨g', w, IsPullback.of_isLimit (PullbackCone.IsLimit.mk w lift (fun s => ?_)
    (fun s => (hl s).1) (fun s m hm₁ hm₂ => ?_)), ?_⟩
  · obtain ⟨hc, e⟩ := hl s
    exact baseChange_comp_eq D p hp L hL pY hpY g g' w hg' s.fst s.snd s.condition (lift s) hc e
  · obtain ⟨hc, e⟩ := hl s
    exact baseChange_hom_eq D p hp L hL pY hpY g g' w hg' s.fst s.snd s.condition m (lift s) hm₁
      hm₂ hc e
  · exact hg'

end BaseChange

end AlgebraicGeometry.Space

end
