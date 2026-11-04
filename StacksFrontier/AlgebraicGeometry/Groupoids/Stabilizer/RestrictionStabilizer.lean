module

public import StacksFrontier.AlgebraicGeometry.Groupoids.Stabilizer.Basic
public import StacksFrontier.AlgebraicGeometry.Groupoids.Stabilizer.OverPullbackLeft
public import StacksFrontier.AlgebraicGeometry.Groupoids.Stabilizer.RestrictionGroupoid
public import StacksCore.Tactic.StacksAttribute

/-!
# Stabilizers of restricted groupoid schemes

The stabilizer of the restriction of a groupoid scheme along a morphism to its object scheme is
the base change of the original stabilizer along that morphism.

## Main definitions

* `AlgebraicGeometry.restrictStabilizerIso` is the canonical identification of the restricted
  stabilizer with the base-changed stabilizer.

## Main results

The isomorphism `AlgebraicGeometry.restrictStabilizerIso` identifies the two stabilizers as
schemes over the new object scheme.

## Implementation notes

The source writes the canonical identification as an equality.  We express it as an isomorphism
in the over category of the new object scheme.  The left-hand object is transported along the
specified identification between the objects of the restriction and the domain of the
restricting morphism; the right-hand object is the chosen pullback.

## References

* [Stacks Project, Tag 04ML](https://stacks.math.columbia.edu/tag/04ML)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.Groupoids

universe u

namespace AlgebraicGeometry

/-- The stabilizer of a restriction, as a fibre product in `Over S`, is the base change of the
stabilizer of the original groupoid along the restricting map. -/
noncomputable def restrictedStabilizerOverIso {S : Scheme.{u}}
    (G : GroupoidScheme S) {U' : Over S} (g : U' ⟶ G.objects) :
    pullback (CartesianMonoidalCategory.lift (restrictionTarget G g) (restrictionSource G g))
        (CartesianMonoidalCategory.lift (𝟙 U') (𝟙 U')) ≅
      pullback g (pullback.snd (sourceTarget G) (diagonal G)) := by
  let ep := CartesianMonoidalCategory.lift (restrictionTarget G g) (restrictionSource G g)
  let d := CartesianMonoidalCategory.lift (𝟙 U') (𝟙 U')
  let P := pullback ep d
  let Q := pullback g (pullback.snd (sourceTarget G) (diagonal G))
  let pA := pullback.fst ep d
  let pU := pullback.snd ep d
  let pR := pA ≫ restrictionArrowsToArrows G g
  have hT : pA ≫ restrictionTarget G g = pU := by
    have h := congrArg (fun k => k ≫ CartesianMonoidalCategory.fst U' U')
      (pullback.condition (f := ep) (g := d))
    simpa [pA, pU, ep, d, restrictionTarget] using h
  have hS : pA ≫ restrictionSource G g = pU := by
    have h := congrArg (fun k => k ≫ CartesianMonoidalCategory.snd U' U')
      (pullback.condition (f := ep) (g := d))
    simpa [pA, pU, ep, d, restrictionSource] using h
  have hp : pR ≫ sourceTarget G = (pU ≫ g) ≫ diagonal G := by
    change pR ≫ CartesianMonoidalCategory.lift G.target G.source =
      (pU ≫ g) ≫ CartesianMonoidalCategory.lift (𝟙 G.objects) (𝟙 G.objects)
    apply CartesianMonoidalCategory.hom_ext
    · simp only [Category.assoc, CartesianMonoidalCategory.lift_fst, Category.comp_id]
      exact calc
        pA ≫ restrictionArrowsToArrows G g ≫ G.target
            = pA ≫ (restrictionTarget G g ≫ g) := by rw [GroupoidScheme.restriction_condition']
        _ = pU ≫ g := by rw [← Category.assoc, hT]
    · simp only [Category.assoc, CartesianMonoidalCategory.lift_snd, Category.comp_id]
      exact calc
        pA ≫ restrictionArrowsToArrows G g ≫ G.source
            = pA ≫ (restrictionSource G g ≫ g) := by rw [← GroupoidScheme.restriction_condition]
        _ = pU ≫ g := by rw [← Category.assoc, hS]
  let pSt : P ⟶ pullback (sourceTarget G) (diagonal G) :=
    pullback.lift (f := sourceTarget G) (g := diagonal G) pR (pU ≫ g) hp
  have hpStR : pSt ≫ pullback.fst (sourceTarget G) (diagonal G) = pR :=
    pullback.lift_fst pR (pU ≫ g) hp
  have hpStU : pSt ≫ pullback.snd (sourceTarget G) (diagonal G) = pU ≫ g :=
    pullback.lift_snd pR (pU ≫ g) hp
  let forward : P ⟶ Q := pullback.lift pU pSt hpStU.symm
  let qU := pullback.fst g (pullback.snd (sourceTarget G) (diagonal G))
  let qSt := pullback.snd g (pullback.snd (sourceTarget G) (diagonal G))
  let qR := qSt ≫ pullback.fst (sourceTarget G) (diagonal G)
  let qb := qSt ≫ pullback.snd (sourceTarget G) (diagonal G)
  have hqb : qU ≫ g = qb :=
    pullback.condition (f := g) (g := pullback.snd (sourceTarget G) (diagonal G))
  have hdiag : qR ≫ sourceTarget G = qb ≫ diagonal G := by
    change qSt ≫ (pullback.fst (sourceTarget G) (diagonal G) ≫ sourceTarget G) =
      qSt ≫ (pullback.snd (sourceTarget G) (diagonal G) ≫ diagonal G)
    exact congrArg (fun k => qSt ≫ k) (pullback.condition
      (f := sourceTarget G) (g := diagonal G))
  have hqt : qR ≫ G.target = qU ≫ g := by
    have h := congrArg (fun k => k ≫ CartesianMonoidalCategory.fst G.objects G.objects) hdiag
    simpa [sourceTarget, diagonal, hqb] using h
  have hqs : qR ≫ G.source = qU ≫ g := by
    have h := congrArg (fun k => k ≫ CartesianMonoidalCategory.snd G.objects G.objects) hdiag
    simpa [sourceTarget, diagonal, hqb] using h
  let a1 := pullback.lift (f := g) (g := G.target) qU qR hqt.symm
  let a2 := pullback.lift (f := G.source) (g := g) qR qU hqs
  have ha1U : a1 ≫ pullback.fst g G.target = qU := pullback.lift_fst qU qR hqt.symm
  have ha1R : a1 ≫ pullback.snd g G.target = qR := pullback.lift_snd qU qR hqt.symm
  have ha2R : a2 ≫ pullback.fst G.source g = qR := pullback.lift_fst qR qU hqs
  have ha2U : a2 ≫ pullback.snd G.source g = qU := pullback.lift_snd qR qU hqs
  have ha12 : a1 ≫ pullback.snd g G.target = a2 ≫ pullback.fst G.source g :=
    ha1R.trans ha2R.symm
  let a := pullback.lift (f := pullback.snd g G.target)
    (g := pullback.fst G.source g) a1 a2 ha12
  have haA1 : a ≫ pullback.fst (pullback.snd g G.target) (pullback.fst G.source g) = a1 :=
    pullback.lift_fst a1 a2 ha12
  have haA2 : a ≫ pullback.snd (pullback.snd g G.target) (pullback.fst G.source g) = a2 :=
    pullback.lift_snd a1 a2 ha12
  have haT : a ≫ restrictionTarget G g = qU := by
    change a ≫ pullback.fst (pullback.snd g G.target) (pullback.fst G.source g) ≫
      pullback.fst g G.target = qU
    rw [← Category.assoc, haA1, ha1U]
  have haS : a ≫ restrictionSource G g = qU := by
    change a ≫ pullback.snd (pullback.snd g G.target) (pullback.fst G.source g) ≫
      pullback.snd G.source g = qU
    rw [← Category.assoc, haA2, ha2U]
  have ha : a ≫ ep = qU ≫ d := by
    have hepF : ep ≫ CartesianMonoidalCategory.fst U' U' = restrictionTarget G g := by
      change CartesianMonoidalCategory.lift (restrictionTarget G g)
        (restrictionSource G g) ≫ CartesianMonoidalCategory.fst U' U' = _
      exact CartesianMonoidalCategory.lift_fst _ _
    have hepS : ep ≫ CartesianMonoidalCategory.snd U' U' = restrictionSource G g := by
      change CartesianMonoidalCategory.lift (restrictionTarget G g)
        (restrictionSource G g) ≫ CartesianMonoidalCategory.snd U' U' = _
      exact CartesianMonoidalCategory.lift_snd _ _
    have hdF : d ≫ CartesianMonoidalCategory.fst U' U' = 𝟙 U' := by
      change CartesianMonoidalCategory.lift (𝟙 U') (𝟙 U') ≫
        CartesianMonoidalCategory.fst U' U' = _
      exact CartesianMonoidalCategory.lift_fst _ _
    have hdS : d ≫ CartesianMonoidalCategory.snd U' U' = 𝟙 U' := by
      change CartesianMonoidalCategory.lift (𝟙 U') (𝟙 U') ≫
        CartesianMonoidalCategory.snd U' U' = _
      exact CartesianMonoidalCategory.lift_snd _ _
    apply CartesianMonoidalCategory.hom_ext
    · calc
        (a ≫ ep) ≫ CartesianMonoidalCategory.fst U' U' =
            a ≫ (ep ≫ CartesianMonoidalCategory.fst U' U') := Category.assoc _ _ _
        _ = a ≫ restrictionTarget G g := congrArg (fun k => a ≫ k) hepF
        _ = qU := haT
        _ = (qU ≫ d) ≫ CartesianMonoidalCategory.fst U' U' := by
          rw [Category.assoc, hdF, Category.comp_id]
    · calc
        (a ≫ ep) ≫ CartesianMonoidalCategory.snd U' U' =
            a ≫ (ep ≫ CartesianMonoidalCategory.snd U' U') := Category.assoc _ _ _
        _ = a ≫ restrictionSource G g := congrArg (fun k => a ≫ k) hepS
        _ = qU := haS
        _ = (qU ≫ d) ≫ CartesianMonoidalCategory.snd U' U' := by
          rw [Category.assoc, hdS, Category.comp_id]
  let backward : Q ⟶ P := pullback.lift a qU ha
  have hfwU : forward ≫ pullback.fst g (pullback.snd (sourceTarget G) (diagonal G)) = pU :=
    pullback.lift_fst pU pSt hpStU.symm
  have hfwSt : forward ≫ pullback.snd g (pullback.snd (sourceTarget G) (diagonal G)) = pSt :=
    pullback.lift_snd pU pSt hpStU.symm
  have hbackA : backward ≫ pullback.fst ep d = a := pullback.lift_fst a qU ha
  have hbackU : backward ≫ pullback.snd ep d = qU := pullback.lift_snd a qU ha
  have hfwR : forward ≫ qR = pR := by
    change forward ≫ qSt ≫ pullback.fst (sourceTarget G) (diagonal G) = pR
    rw [← Category.assoc, hfwSt, hpStR]
  have hforward_a1 : forward ≫ a1 =
      pA ≫ pullback.fst (pullback.snd g G.target) (pullback.fst G.source g) := by
    apply pullback.hom_ext
    · calc
        forward ≫ a1 ≫ pullback.fst g G.target = pU := by rw [ha1U, hfwU]
        _ = pA ≫ pullback.fst (pullback.snd g G.target) (pullback.fst G.source g) ≫
              pullback.fst g G.target := by
          simpa [restrictionTarget] using hT.symm
    · rw [Category.assoc, ha1R]
      exact hfwR
  have hforward_a2 : forward ≫ a2 =
      pA ≫ pullback.snd (pullback.snd g G.target) (pullback.fst G.source g) := by
    apply pullback.hom_ext
    · rw [Category.assoc, ha2R, hfwR]
      exact congrArg (pA ≫ ·) (pullback.condition (f := pullback.snd g G.target)
        (g := pullback.fst G.source g))
    · calc
        forward ≫ a2 ≫ pullback.snd G.source g = pU := by rw [ha2U, hfwU]
        _ = pA ≫ pullback.snd (pullback.snd g G.target) (pullback.fst G.source g) ≫
              pullback.snd G.source g := by
          simpa [restrictionSource] using hS.symm
  have hforward_a : forward ≫ a = pA := by
    apply pullback.hom_ext
    · rw [Category.assoc, haA1]
      exact hforward_a1
    · rw [Category.assoc, haA2]
      exact hforward_a2
  have hback_pR : backward ≫ pR = qR := by
    change backward ≫ (pA ≫ restrictionArrowsToArrows G g) = qR
    rw [← Category.assoc, hbackA]
    change a ≫ pullback.fst (pullback.snd g G.target) (pullback.fst G.source g) ≫
      pullback.snd g G.target = qR
    rw [← Category.assoc, haA1, ha1R]
  have hback_pSt : backward ≫ pSt = qSt := by
    apply pullback.hom_ext
    · rw [Category.assoc, hpStR]
      exact hback_pR
    · rw [Category.assoc, hpStU, ← Category.assoc, hbackU]
      exact hqb
  refine ⟨forward, backward, ?_, ?_⟩
  · apply pullback.hom_ext
    · change forward ≫ (backward ≫ pullback.fst ep d) = pullback.fst ep d
      rw [hbackA]
      simpa [pA, restrictionArrows] using hforward_a
    · change forward ≫ (backward ≫ pullback.snd ep d) = pullback.snd ep d
      rw [hbackU]
      simpa [pU] using hfwU
  · apply pullback.hom_ext
    · calc
        (backward ≫ forward) ≫ qU = backward ≫ pU := by rw [Category.assoc, hfwU]
        _ = qU := by simpa [pU] using hbackU
    · calc
        (backward ≫ forward) ≫ qSt = backward ≫ pSt := by rw [Category.assoc, hfwSt]
        _ = qSt := hback_pSt

/-- The comparison isomorphism is compatible with the projection to the new object scheme. -/
theorem restrictedStabilizerOverIso_hom_fst {S : Scheme.{u}} (G : GroupoidScheme S)
    {U' : Over S} (g : U' ⟶ G.objects) :
    (restrictedStabilizerOverIso G g).hom ≫
      pullback.fst g (pullback.snd (sourceTarget G) (diagonal G)) =
    pullback.snd
      (CartesianMonoidalCategory.lift (restrictionTarget G g) (restrictionSource G g))
      (CartesianMonoidalCategory.lift (𝟙 U') (𝟙 U')) := by
  unfold restrictedStabilizerOverIso
  simp only [pullback.lift_fst]

/-- **Stacks Project, Tag 04ML.** The stabilizer of a restricted groupoid scheme is canonically
the base change of the original stabilizer. -/
@[stacks 04ML]
noncomputable def restrictStabilizerIso {S : Scheme.{u}} (G : GroupoidScheme S)
    {U' : Scheme.{u}} (g : U' ⟶ G.objects.left) :
    let U'_S : Over S := Over.mk (g ≫ G.objects.hom)
    let g' : U'_S ⟶ G.objects := Over.homMk g
    Over.mk ((stabilizer (GroupoidScheme.restrict G g').groupoid).hom ≫
      eqToHom (congrArg Over.left (GroupoidScheme.restrict G g').objects_eq)) ≅
      Over.mk (pullback.fst g (stabilizer G).hom) := by
  classical
  dsimp
  let U'_S : Over S := Over.mk (g ≫ G.objects.hom)
  let g' : U'_S ⟶ G.objects := Over.homMk g
  let ep := CartesianMonoidalCategory.lift (restrictionTarget G g') (restrictionSource G g')
  let d := CartesianMonoidalCategory.lift (𝟙 U'_S) (𝟙 U'_S)
  let R := GroupoidScheme.restrict G g'
  change Over.mk ((stabilizer R.groupoid).hom ≫ eqToHom (congrArg Over.left R.objects_eq)) ≅ _
  cases R with
  | mk H oe ae se te hom moe mae ev =>
    cases H with
    | mk objects arrows source target comp identity inverse source_identity target_identity
        source_inverse target_inverse left_identity right_identity left_inverse
        right_inverse assoc =>
      have hObj : objects = U'_S := oe
      cases hObj
      have hArr : arrows = restrictionArrows G g' := ae
      cases hArr
      have hSrc : source = restrictionSource G g' := by
        simpa using se
      cases hSrc
      have hTgt : target = restrictionTarget G g' := by
        simpa using te
      cases hTgt
      let e₀ := (Over.forget S).mapIso (restrictedStabilizerOverIso G g')
      let e₁ := overPullbackLeftIso g' (pullback.snd (sourceTarget G) (diagonal G))
      let e := e₀.trans e₁
      refine Over.isoMk e ?_
      change (Over.Hom.left (restrictedStabilizerOverIso G g').hom ≫ e₁.hom) ≫
          pullback.fst g (Over.Hom.left (pullback.snd (sourceTarget G) (diagonal G))) =
        (pullback.snd ep d).left
      calc
        (Over.Hom.left (restrictedStabilizerOverIso G g').hom ≫ e₁.hom) ≫
            pullback.fst g (Over.Hom.left (pullback.snd (sourceTarget G) (diagonal G))) =
            Over.Hom.left (restrictedStabilizerOverIso G g').hom ≫
              (e₁.hom ≫ pullback.fst g
                (Over.Hom.left (pullback.snd (sourceTarget G) (diagonal G)))) :=
          Category.assoc _ _ _
        _ = Over.Hom.left (restrictedStabilizerOverIso G g').hom ≫
              (pullback.fst g' (pullback.snd (sourceTarget G) (diagonal G))).left := by
          have hh : e₁.hom ≫
              pullback.fst g (Over.Hom.left (pullback.snd (sourceTarget G) (diagonal G))) =
              (pullback.fst g' (pullback.snd (sourceTarget G) (diagonal G))).left := by
            change (overPullbackLeftIso g' (pullback.snd (sourceTarget G) (diagonal G))).hom ≫
                pullback.fst (Over.Hom.left g')
                  (Over.Hom.left (pullback.snd (sourceTarget G) (diagonal G))) = _
            exact overPullbackLeftIso_hom_fst g' (pullback.snd (sourceTarget G) (diagonal G))
          rw [hh]
        _ = (pullback.snd ep d).left := by
          simpa only [Over.comp_left] using
            congrArg Over.Hom.left (restrictedStabilizerOverIso_hom_fst G g')

end AlgebraicGeometry

end
