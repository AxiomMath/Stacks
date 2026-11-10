module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.LimitBaseChangeColimit
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.LimitBaseChangeDerived
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.LimitHigherDirectImageDerivedColimit

/-!
# Base change for bounded below complexes passes to the limit

Let `I` be a directed set and let `(X_i ← Y_i, S_i ← T_i)` be an inverse system of cartesian
squares as in [Stacks, Tag 0EZT], with limit square `(X, Y, S, T, f, h, e, g)`. Let `0 ∈ I`,
`K_0 ∈ D^+(T_{0, étale})`, `K_i` its pullback to `T_i` for `i ≥ 0` and `K` its pullback to `T`.
If `f_i^{-1}Rg_{i, *}K_i = Rh_{i, *}e_i^{-1}K_i` for all `i ≥ 0`, then
`f^{-1}Rg_*K = Rh_*e^{-1}K` ([Stacks, Tag 0GJL]).

## Main definitions

* `complexPullbackCompApp`: the comparison `f^{-1}g^{-1}𝒢^• ≅ (f ≫ g)^{-1}𝒢^•` of inverse
  images of complexes along a named composite.
* `derivedLevelComparison`: the derived base change map of the `i`-th square at the pullbacks of
  a complex, on cohomology sheaves and pulled back to the limit.

## Main results

* `derivedBaseChangeHomologyMap_paste_eq`: two decompositions of a commutative square into two
  squares give the same pasted base change map, when the pasted comparisons agree.
* `map_complexLeg_comp_derivedBaseChangeHomologyMap`,
  `map_pullbackDiagramMap_comp_derivedLevelComparison`: the level comparisons are compatible with
  the base change map of the limit square and with the transition maps of the two systems of
  [Stacks, Tag 0GIV].
* `isIso_smallEtaleDerivedBaseChangeAb_limit_of_cocone`: base change passes to the limit for the
  pullbacks of a bounded below object along a compatible family `T_i ⟶ T₀`.
* `isIso_smallEtaleDerivedBaseChangeAb_limit_of_isLimit`: [Stacks, Tag 0GJL].

## Implementation notes

The proof is the source's: by `isIso_of_forall_isIso_derivedLimitComparison` it suffices to show
that `f^{-1}R^pg_*K ⟶ R^ph_*e^{-1}K` is an isomorphism for every `p`. Representing `K_0` by a
complex `𝒢^•` vanishing in degrees `< a`, the colimit assertion of [Stacks, Tag 0GIU] is used in
the form of its proof, [Stacks, Tag 0GIV] for the systems of pullbacks of `𝒢^•` to the `T_i`
and to the `Y_i`: both sides are colimits of the systems `f^{-1}s_i^{-1}R^pg_{i, *}K_i` and
`r_i^{-1}R^ph_{i, *}e_i^{-1}K_i`, the base change maps of the levels form a map of systems
compatible with the base change map of the limit square, by the pasting of derived base change
maps ([Stacks, Tag 0E47]), and a map of colimits which is invertible on every level is
invertible. As in the source, the index set is `{i ∈ I | i ≥ 0}`; the systems are restricted to it
along `Stacks.EtaleCohomology.LimitHigherDirectImage.aboveInclusion`, which does not change their
limits.

The general statement `isIso_smallEtaleDerivedBaseChangeAb_limit_of_cocone` takes the maps
`Y_i ⟶ T₀` as a separate family `ιY` together with the equations `ιY_i = e_i ≫ ι_i`, and the
comparisons of inverse images of complexes along composites are the definition
`complexPullbackCompApp` rather than components of a natural isomorphism; the coherence of these
comparisons is then a matter of instantiating `complexPullbackCompApp_assoc`.

## References

* [Stacks Project, Tag 0GJL](https://stacks.math.columbia.edu/tag/0GJL)
* [Stacks Project, Tag 0GIU](https://stacks.math.columbia.edu/tag/0GIU)
* [Stacks Project, Tag 0GIV](https://stacks.math.columbia.edu/tag/0GIV)
* [Stacks Project, Tag 0EZT](https://stacks.math.columbia.edu/tag/0EZT)
* [Stacks Project, Tag 0E47](https://stacks.math.columbia.edu/tag/0E47)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
open CochainComplex (plusDerivedObj)

universe u

namespace Stacks.EtaleCohomology.LimitBaseChangeDerived

attribute [local instance] HasDerivedCategory.standard

open LimitHigherDirectImage

/-! ### Comparisons of inverse images of complexes along composites -/

/-- **The comparison `f^{-1}g^{-1}𝒢^• ≅ (f ≫ g)^{-1}𝒢^•`** of inverse images of complexes along a
named composite, with the iterated inverse image as source. -/
def complexPullbackCompApp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (fg : X ⟶ Z)
    (hfg : fg = f ≫ g) (G : CochainComplex (Sheaf (smallEtaleTopology Z) Ab.{u + 1}) ℤ) :
    ((smallEtalePullbackAb f).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (((smallEtalePullbackAb g).mapHomologicalComplex (ComplexShape.up ℤ)).obj G) ≅
      ((smallEtalePullbackAb fg).mapHomologicalComplex (ComplexShape.up ℤ)).obj G :=
  (NatIso.mapHomologicalComplex (smallEtalePullbackAbComp' f g fg hfg) (ComplexShape.up ℤ)).app G

/-- The forward map of `complexPullbackCompApp` is the component at `𝒢^•` of the comparison
`f^{-1}g^{-1} ⟶ (f ≫ g)^{-1}` applied degreewise. -/
theorem complexPullbackCompApp_hom {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (fg : X ⟶ Z)
    (hfg : fg = f ≫ g) (G : CochainComplex (Sheaf (smallEtaleTopology Z) Ab.{u + 1}) ℤ) :
    (complexPullbackCompApp f g fg hfg G).hom =
      (NatIso.mapHomologicalComplex (smallEtalePullbackAbComp' f g fg hfg)
        (ComplexShape.up ℤ)).hom.app G :=
  rfl

/-- The inverse map of `complexPullbackCompApp` is the component at `𝒢^•` of the comparison
`(f ≫ g)^{-1} ⟶ f^{-1}g^{-1}` applied degreewise. -/
theorem complexPullbackCompApp_inv {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (fg : X ⟶ Z)
    (hfg : fg = f ≫ g) (G : CochainComplex (Sheaf (smallEtaleTopology Z) Ab.{u + 1}) ℤ) :
    (complexPullbackCompApp f g fg hfg G).inv =
      (NatIso.mapHomologicalComplex (smallEtalePullbackAbComp' f g fg hfg)
        (ComplexShape.up ℤ)).inv.app G :=
  rfl

/-! ### Pasting both ways -/

section Paste

/-- **Two decompositions of a square give the same pasted derived base change map** on
cohomology sheaves, as soon as the pasted comparisons of derived inverse images agree. -/
theorem derivedBaseChangeHomologyMap_paste_eq {X₀ X₁ X₁' X₂ S₀ S₁ S₁' S₂ : Scheme.{u}}
    (g₀ : X₀ ⟶ S₀) (g₁ : X₁ ⟶ S₁) (g₁' : X₁' ⟶ S₁') (g₂ : X₂ ⟶ S₂)
    (u₁ : S₁ ⟶ S₀) (u₂ : S₂ ⟶ S₁) (u₁' : S₁' ⟶ S₀) (u₂' : S₂ ⟶ S₁')
    (v₁ : X₁ ⟶ X₀) (v₂ : X₂ ⟶ X₁) (v₁' : X₁' ⟶ X₀) (v₂' : X₂ ⟶ X₁')
    (w₁ : g₁ ≫ u₁ = v₁ ≫ g₀) (w₂ : g₂ ≫ u₂ = v₂ ≫ g₁) (w₁' : g₁' ≫ u₁' = v₁' ≫ g₀)
    (w₂' : g₂ ≫ u₂' = v₂' ≫ g₁') (u : S₂ ⟶ S₀) (hu : u = u₂ ≫ u₁) (hu' : u = u₂' ≫ u₁')
    (v : X₂ ⟶ X₀) (hv : v = v₂ ≫ v₁) (hv' : v = v₂' ≫ v₁') (w : g₂ ≫ u = v ≫ g₀) (p : ℤ)
    (L₀ : PlusAb X₀) (L₁ : PlusAb X₁) (L₁' : PlusAb X₁') (L₂ : PlusAb X₂)
    (κ₁ : (derivedPullbackAb v₁).obj L₀ ⟶ L₁) (κ₂ : (derivedPullbackAb v₂).obj L₁ ⟶ L₂)
    (κ₁' : (derivedPullbackAb v₁').obj L₀ ⟶ L₁') (κ₂' : (derivedPullbackAb v₂').obj L₁' ⟶ L₂)
    (hκ : (smallEtaleDerivedPullbackAbPlusComp' v₁ v₂ v hv).inv.app L₀ ≫
        (derivedPullbackAb v₂).map κ₁ ≫ κ₂ =
      (smallEtaleDerivedPullbackAbPlusComp' v₁' v₂' v hv').inv.app L₀ ≫
        (derivedPullbackAb v₂').map κ₁' ≫ κ₂') :
    (smallEtalePullbackAbComp' u₂ u₁ u hu).inv.app _ ≫
        (smallEtalePullbackAb u₂).map (derivedBaseChangeHomologyMap u₁ g₀ g₁ v₁ w₁ p L₀ L₁ κ₁) ≫
          derivedBaseChangeHomologyMap u₂ g₁ g₂ v₂ w₂ p L₁ L₂ κ₂ =
      (smallEtalePullbackAbComp' u₂' u₁' u hu').inv.app _ ≫
        (smallEtalePullbackAb u₂').map
          (derivedBaseChangeHomologyMap u₁' g₀ g₁' v₁' w₁' p L₀ L₁' κ₁') ≫
          derivedBaseChangeHomologyMap u₂' g₁' g₂ v₂' w₂' p L₁' L₂ κ₂' := by
  rw [← derivedBaseChangeHomologyMap_paste g₀ g₁ g₂ u₁ u₂ v₁ v₂ w₁ w₂ p L₀ L₁ L₂ κ₁ κ₂ u hu v hv w,
    ← derivedBaseChangeHomologyMap_paste g₀ g₁' g₂ u₁' u₂' v₁' v₂' w₁' w₂' p L₀ L₁' L₂ κ₁' κ₂' u
      hu' v hv' w, hκ]

/-- **Two decompositions of the comparison of derived inverse images of complexes** agree as soon
as the underlying maps of complexes do. -/
theorem smallEtaleComplexPullbackComparison_paste_eq (a : ℤ) {X₀ X₁ X₁' X₂ : Scheme.{u}}
    (f₁ : X₁ ⟶ X₀) (f₂ : X₂ ⟶ X₁) (f₁' : X₁' ⟶ X₀) (f₂' : X₂ ⟶ X₁') (f : X₂ ⟶ X₀)
    (hf : f = f₂ ≫ f₁) (hf' : f = f₂' ≫ f₁')
    (F₀ : CochainComplex (Sheaf (smallEtaleTopology X₀) Ab.{u + 1}) ℤ) [F₀.IsStrictlyGE a]
    (F₁ : CochainComplex (Sheaf (smallEtaleTopology X₁) Ab.{u + 1}) ℤ) [F₁.IsStrictlyGE a]
    (F₁' : CochainComplex (Sheaf (smallEtaleTopology X₁') Ab.{u + 1}) ℤ) [F₁'.IsStrictlyGE a]
    (F₂ : CochainComplex (Sheaf (smallEtaleTopology X₂) Ab.{u + 1}) ℤ) [F₂.IsStrictlyGE a]
    (ι₁ : ((smallEtalePullbackAb f₁).mapHomologicalComplex (ComplexShape.up ℤ)).obj F₀ ⟶ F₁)
    (ι₂ : ((smallEtalePullbackAb f₂).mapHomologicalComplex (ComplexShape.up ℤ)).obj F₁ ⟶ F₂)
    (ι₁' : ((smallEtalePullbackAb f₁').mapHomologicalComplex (ComplexShape.up ℤ)).obj F₀ ⟶ F₁')
    (ι₂' : ((smallEtalePullbackAb f₂').mapHomologicalComplex (ComplexShape.up ℤ)).obj F₁' ⟶ F₂)
    (h : (complexPullbackCompApp f₂ f₁ f hf F₀).inv ≫
          ((smallEtalePullbackAb f₂).mapHomologicalComplex (ComplexShape.up ℤ)).map ι₁ ≫ ι₂ =
      (complexPullbackCompApp f₂' f₁' f hf' F₀).inv ≫
          ((smallEtalePullbackAb f₂').mapHomologicalComplex (ComplexShape.up ℤ)).map ι₁' ≫ ι₂') :
    (smallEtaleDerivedPullbackAbPlusComp' f₁ f₂ f hf).inv.app (plusDerivedObj a F₀) ≫
        (derivedPullbackAb f₂).map (smallEtaleComplexPullbackComparison a f₁ F₀ F₁ ι₁) ≫
          smallEtaleComplexPullbackComparison a f₂ F₁ F₂ ι₂ =
      (smallEtaleDerivedPullbackAbPlusComp' f₁' f₂' f hf').inv.app (plusDerivedObj a F₀) ≫
        (derivedPullbackAb f₂').map (smallEtaleComplexPullbackComparison a f₁' F₀ F₁' ι₁') ≫
          smallEtaleComplexPullbackComparison a f₂' F₁' F₂ ι₂' :=
  (smallEtaleComplexPullbackComparison_paste a f₁ f₂ f hf F₀ F₁ F₂ ι₁ ι₂ _ rfl).symm.trans
    ((congrArg (smallEtaleComplexPullbackComparison a f F₀ F₂) h).trans
      (smallEtaleComplexPullbackComparison_paste a f₁' f₂' f hf' F₀ F₁' F₂ ι₁' ι₂' _ rfl))

end Paste


/-! ### The two compatibilities for arbitrary morphisms -/

local notation "App" => smallEtalePullbackAbCompApp

section Legs

variable {X S T Y X₀ S₀ T₀ Y₀ : Scheme.{u}} (fL : X ⟶ S) (gL : T ⟶ S) (hL : Y ⟶ X) (eL : Y ⟶ T)
  (r : X ⟶ X₀) (s : S ⟶ S₀) (t' : T ⟶ T₀) (y : Y ⟶ Y₀)
  (f₀ : X₀ ⟶ S₀) (g₀ : T₀ ⟶ S₀) (h₀ : Y₀ ⟶ X₀) (e₀ : Y₀ ⟶ T₀)
  (u : X ⟶ S₀) (v : Y ⟶ T₀) (hu₁ : u = fL ≫ s) (hu₂ : u = r ≫ f₀) (hv₁ : v = eL ≫ t')
  (hv₂ : v = y ≫ e₀) (hgL : gL ≫ s = t' ≫ g₀) (hhL : hL ≫ r = y ≫ h₀)
  (w₀ : h₀ ≫ f₀ = e₀ ≫ g₀) (wL : hL ≫ fL = eL ≫ gL) (p : ℤ)
  (L₀ : PlusAb T₀) (L₀' : PlusAb Y₀) (M : PlusAb T) (M' : PlusAb Y)
  (κt : (derivedPullbackAb t').obj L₀ ⟶ M) (κst : (derivedPullbackAb e₀).obj L₀ ⟶ L₀')
  (κy : (derivedPullbackAb y).obj L₀' ⟶ M') (κL : (derivedPullbackAb eL).obj M ⟶ M')

include hu₂ hv₂ hhL w₀ in
/-- Pasting the commutative squares `hL ≫ r = y ≫ h₀` and `h₀ ≫ f₀ = e₀ ≫ g₀` gives the
commutative rectangle `hL ≫ u = v ≫ g₀` for `u = r ≫ f₀` and `v = y ≫ e₀`. -/
theorem rectangle_comm : hL ≫ u = v ≫ g₀ := by
  rw [hu₂, hv₂, ← Category.assoc, hhL, Category.assoc, w₀, Category.assoc]

/-- **The compatibility of the derived base change maps of a level square and of the limit square
with the legs**, for arbitrary morphisms subject to the equations of the projection squares: both
composites are decompositions of the derived base change map of the rectangle with sides
`u = r ≫ f₀ = f ≫ s` and `v = y ≫ e₀ = e ≫ t'`. -/
theorem derivedBaseChangeHomologyMap_legs
    (hκ : (smallEtaleDerivedPullbackAbPlusComp' t' eL v hv₁).inv.app L₀ ≫
        (derivedPullbackAb eL).map κt ≫ κL =
      (smallEtaleDerivedPullbackAbPlusComp' e₀ y v hv₂).inv.app L₀ ≫
        (derivedPullbackAb y).map κst ≫ κy) :
    (smallEtalePullbackAb fL).map (derivedBaseChangeHomologyMap s g₀ gL t' hgL p L₀ M κt) ≫
        derivedBaseChangeHomologyMap fL gL hL eL wL p M M' κL =
      ((App fL s u hu₁ _).hom ≫ (App r f₀ u hu₂ _).inv ≫
        (smallEtalePullbackAb r).map (derivedBaseChangeHomologyMap f₀ g₀ h₀ e₀ w₀ p L₀ L₀' κst)) ≫
        derivedBaseChangeHomologyMap r h₀ hL y hhL p L₀' M' κy := by
  have key := derivedBaseChangeHomologyMap_paste_eq g₀ gL h₀ hL s fL f₀ r t' eL e₀ y hgL wL w₀
    hhL u hu₁ hu₂ v hv₁ hv₂ (rectangle_comm hL r y f₀ g₀ h₀ e₀ u v hu₂ hv₂ hhL w₀) p L₀ M L₀' M'
    κt κL κst κy hκ
  rw [← cancel_epi (App fL s u hu₁ _).inv]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  exact key

end Legs

section Diagram

variable {X S Xi Xj Si Sj Ti Tj Yi Yj : Scheme.{u}} (fL : X ⟶ S)
  (ri : X ⟶ Xi) (rj : X ⟶ Xj) (si : S ⟶ Si) (sj : S ⟶ Sj)
  (fi : Xi ⟶ Si) (fj : Xj ⟶ Sj) (gi : Ti ⟶ Si) (gj : Tj ⟶ Sj) (hi : Yi ⟶ Xi) (hj : Yj ⟶ Xj)
  (ei : Yi ⟶ Ti) (ej : Yj ⟶ Tj)
  (xa : Xi ⟶ Xj) (sa : Si ⟶ Sj) (ta : Ti ⟶ Tj) (ya : Yi ⟶ Yj)
  (hrj : rj = ri ≫ xa) (hsj : sj = si ≫ sa)
  (hgt : gi ≫ sa = ta ≫ gj) (hht : hi ≫ xa = ya ≫ hj)
  (wi : hi ≫ fi = ei ≫ gi) (wj : hj ≫ fj = ej ≫ gj)
  (ui : X ⟶ Si) (uj : X ⟶ Sj) (hui₁ : ui = fL ≫ si) (hui₂ : ui = ri ≫ fi)
  (huj₁ : uj = fL ≫ sj) (huj₂ : uj = rj ≫ fj)
  (U : Xi ⟶ Sj) (hU₁ : U = xa ≫ fj) (hU₂ : U = fi ≫ sa)
  (V : Yi ⟶ Tj) (hV₁ : V = ya ≫ ej) (hV₂ : V = ei ≫ ta) (p : ℤ)
  (Lj : PlusAb Tj) (Li : PlusAb Ti) (Lj' : PlusAb Yj) (Li' : PlusAb Yi)
  (κT : (derivedPullbackAb ta).obj Lj ⟶ Li) (κY : (derivedPullbackAb ya).obj Lj' ⟶ Li')
  (κi : (derivedPullbackAb ei).obj Li ⟶ Li') (κj : (derivedPullbackAb ej).obj Lj ⟶ Lj')

include U hU₁ hU₂ in
/-- **The naturality of the level comparisons**, for arbitrary morphisms subject to the equations
of the projection and transition squares: both composites are decompositions of the derived base
change map of the rectangle with sides `U = f_i ≫ s_{ji} = f_{ji} ≫ f_j` and
`V = e_i ≫ t_{ji} = y_{ji} ≫ e_j`, followed by the comparisons of inverse images along the two
factorisations of `X ⟶ S_j`. -/
theorem derivedBaseChangeHomologyMap_diagram
    (hκ : (smallEtaleDerivedPullbackAbPlusComp' ta ei V hV₂).inv.app Lj ≫
        (derivedPullbackAb ei).map κT ≫ κi =
      (smallEtaleDerivedPullbackAbPlusComp' ej ya V hV₁).inv.app Lj ≫
        (derivedPullbackAb ya).map κj ≫ κY) :
    (smallEtalePullbackAb fL).map ((App si sa sj hsj _).inv ≫
        (smallEtalePullbackAb si).map (derivedBaseChangeHomologyMap sa gj gi ta hgt p Lj Li κT)) ≫
      ((App fL si ui hui₁ _).hom ≫ (App ri fi ui hui₂ _).inv ≫
        (smallEtalePullbackAb ri).map (derivedBaseChangeHomologyMap fi gi hi ei wi p Li Li' κi)) =
    ((App fL sj uj huj₁ _).hom ≫ (App rj fj uj huj₂ _).inv ≫
        (smallEtalePullbackAb rj).map (derivedBaseChangeHomologyMap fj gj hj ej wj p Lj Lj' κj)) ≫
      (App ri xa rj hrj _).inv ≫
        (smallEtalePullbackAb ri).map
          (derivedBaseChangeHomologyMap xa hj hi ya hht p Lj' Li' κY) := by
  have wU := LimitBaseChange.diagram_rectangle_comm fj gj hi hj ej xa ya hht wj U hU₁ V hV₁
  have key := derivedBaseChangeHomologyMap_paste_eq gj gi hj hi sa fi fj xa ta ei ej ya hgt wi wj
    hht U hU₂ hU₁ V hV₂ hV₁ wU p Lj Li Lj' Li' κT κi κj κY hκ
  have k2 : (smallEtalePullbackAb fi).map
        (derivedBaseChangeHomologyMap sa gj gi ta hgt p Lj Li κT) ≫
        derivedBaseChangeHomologyMap fi gi hi ei wi p Li Li' κi =
      (App fi sa U hU₂ _).hom ≫ (App xa fj U hU₁ _).inv ≫
        (smallEtalePullbackAb xa).map (derivedBaseChangeHomologyMap fj gj hj ej wj p Lj Lj' κj) ≫
          derivedBaseChangeHomologyMap xa hj hi ya hht p Lj' Li' κY := by
    rw [smallEtalePullbackAbCompApp, smallEtalePullbackAbCompApp, Iso.app_hom, Iso.app_inv,
      ← cancel_epi ((smallEtalePullbackAbComp' fi sa U hU₂).inv.app _),
      Iso.inv_hom_id_app_assoc]
    exact key
  have k3 : (smallEtalePullbackAb ri).map ((smallEtalePullbackAb fi).map
        (derivedBaseChangeHomologyMap sa gj gi ta hgt p Lj Li κT)) ≫
        (smallEtalePullbackAb ri).map (derivedBaseChangeHomologyMap fi gi hi ei wi p Li Li' κi) =
      (smallEtalePullbackAb ri).map (App fi sa U hU₂ _).hom ≫
        (smallEtalePullbackAb ri).map (App xa fj U hU₁ _).inv ≫
        (smallEtalePullbackAb ri).map ((smallEtalePullbackAb xa).map
          (derivedBaseChangeHomologyMap fj gj hj ej wj p Lj Lj' κj)) ≫
          (smallEtalePullbackAb ri).map
            (derivedBaseChangeHomologyMap xa hj hi ya hht p Lj' Li' κY) := by
    rw [← Functor.map_comp, k2]
    simp only [Functor.map_comp]
  have hc := LimitBaseChange.pullbackComparison_coherence fL ri rj si sj fi fj xa sa hrj hsj ui uj
    hui₁ hui₂ huj₁ huj₂ U hU₁ hU₂ ((homologyAb Sj p).obj ((derivedPushforwardAb gj).obj Lj))
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% (smallEtalePullbackAbCompApp_hom_naturality fL si ui hui₁
      (derivedBaseChangeHomologyMap sa gj gi ta hgt p Lj Li κT)),
    reassoc_of% (smallEtalePullbackAbCompApp_inv_naturality ri fi ui hui₂
      (derivedBaseChangeHomologyMap sa gj gi ta hgt p Lj Li κT)),
    reassoc_of% (smallEtalePullbackAbCompApp_inv_naturality ri xa rj hrj
      (derivedBaseChangeHomologyMap fj gj hj ej wj p Lj Lj' κj)), k3,
    reassoc_of% hc, Iso.hom_inv_id_map_assoc]

end Diagram


/-! ### Coherence of the comparisons of inverse images of complexes -/

/-- **The comparisons of inverse images of complexes along composites are coherent**: for
`fgk = f ≫ gk = fg ≫ k`, the comparison along `f ≫ gk` after the one along `g ≫ k` is the one
along `fg ≫ k` after the one along `f ≫ g`. -/
theorem complexPullbackCompApp_assoc {T X Y Z : Scheme.{u}} (f : T ⟶ X) (g : X ⟶ Y)
    (k : Y ⟶ Z) (fg : T ⟶ Y) (hfg : fg = f ≫ g) (gk : X ⟶ Z) (hgk : gk = g ≫ k)
    (fgk : T ⟶ Z) (h₁ : fgk = fg ≫ k) (h₂ : fgk = f ≫ gk)
    (G : CochainComplex (Sheaf (smallEtaleTopology Z) Ab.{u + 1}) ℤ) :
    (complexPullbackCompApp f g fg hfg
        (((smallEtalePullbackAb k).mapHomologicalComplex (ComplexShape.up ℤ)).obj G)).inv ≫
      ((smallEtalePullbackAb f).mapHomologicalComplex (ComplexShape.up ℤ)).map
        (complexPullbackCompApp g k gk hgk G).hom ≫ (complexPullbackCompApp f gk fgk h₂ G).hom =
    (complexPullbackCompApp fg k fgk h₁ G).hom := by
  ext n : 1
  have h := smallEtalePullbackAbComp'_assoc_app f g k fg hfg gk hgk fgk h₁ h₂ (G.X n)
  simp only [complexPullbackCompApp, Iso.app_inv, HomologicalComplex.comp_f,
    NatIso.mapHomologicalComplex_inv_app_f, Iso.app_hom,
    NatIso.mapHomologicalComplex_hom_app_f, Functor.mapHomologicalComplex_map_f]
  rw [← h]
  exact Iso.inv_hom_id_app_assoc _ _ _

/-! ### Isomorphisms -/

/-- A map of complexes which is an isomorphism gives an isomorphism of derived inverse images. -/
theorem isIso_smallEtaleComplexPullbackComparison (a : ℤ) {X Y : Scheme.{u}} (f : X ⟶ Y)
    (F : CochainComplex (Sheaf (smallEtaleTopology Y) Ab.{u + 1}) ℤ) [F.IsStrictlyGE a]
    (G : CochainComplex (Sheaf (smallEtaleTopology X) Ab.{u + 1}) ℤ) [G.IsStrictlyGE a]
    (φ : ((smallEtalePullbackAb f).mapHomologicalComplex (ComplexShape.up ℤ)).obj F ⟶ G)
    [IsIso φ] : IsIso (smallEtaleComplexPullbackComparison a f F G φ) := by
  let : IsIso (smallEtalePullbackAb f).rightDerivedFunctorPlusUnith :=
    (smallEtalePullbackAb f).isIso_rightDerivedFunctorPlusUnit_of_preservesHomology
  have h1 : IsIso ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map φ) :=
    Functor.map_isIso _ _
  have : IsIso (ObjectProperty.homMk ((HomotopyCategory.quotient _ _).map φ) :
        (smallEtalePullbackAb f).mapHomotopyCategoryPlus.obj (CochainComplex.plusHomotopyObj a F) ⟶
          CochainComplex.plusHomotopyObj a G) := by
    have : IsIso ((HomotopyCategory.Plus.ι _).map (ObjectProperty.homMk
        ((HomotopyCategory.quotient _ _).map φ) :
          (smallEtalePullbackAb f).mapHomotopyCategoryPlus.obj
            (CochainComplex.plusHomotopyObj a F) ⟶
            CochainComplex.plusHomotopyObj a G)) := h1
    exact isIso_of_reflects_iso _ (HomotopyCategory.Plus.ι _)
  rw [smallEtaleComplexPullbackComparison_eq]
  infer_instance

/-- A functor applied to the derived base change map is invertible at an object as soon as it is
invertible at an isomorphic one. -/
theorem isIso_map_smallEtaleDerivedBaseChangeAb_app_of_iso {X' Y' S' T' : Scheme.{u}}
    (f' : X' ⟶ S') (g' : T' ⟶ S') (h' : Y' ⟶ X') (e' : Y' ⟶ T') (w' : h' ≫ f' = e' ≫ g')
    {𝒞 : Type*} [Category* 𝒞] (Φ : PlusAb X' ⥤ 𝒞) {L L' : PlusAb T'} (α : L ≅ L')
    (hL : IsIso (Φ.map ((smallEtaleDerivedBaseChangeAb f' g' h' e' w').app L))) :
    IsIso (Φ.map ((smallEtaleDerivedBaseChangeAb f' g' h' e' w').app L')) := by
  have e : Φ.map ((smallEtaleDerivedBaseChangeAb f' g' h' e' w').app L') ≫
      Φ.map ((derivedPushforwardAb h').map ((derivedPullbackAb e').map α.inv)) =
      Φ.map ((derivedPullbackAb f').map ((derivedPushforwardAb g').map α.inv)) ≫
        Φ.map ((smallEtaleDerivedBaseChangeAb f' g' h' e' w').app L) := by
    rw [← Φ.map_comp, ← Φ.map_comp]
    exact congrArg Φ.map ((smallEtaleDerivedBaseChangeAb f' g' h' e' w').naturality α.inv).symm
  have : IsIso (Φ.map ((smallEtaleDerivedBaseChangeAb f' g' h' e' w').app L') ≫
      Φ.map ((derivedPushforwardAb h').map ((derivedPullbackAb e').map α.inv))) := by
    rw [e]
    infer_instance
  exact IsIso.of_isIso_comp_right _
    (Φ.map ((derivedPushforwardAb h').map ((derivedPullbackAb e').map α.inv)))

/-- The derived base change map on cohomology sheaves attached to an isomorphism `κ` is
invertible as soon as the derived base change map is invertible on cohomology sheaves. -/
theorem isIso_derivedBaseChangeHomologyMap {X' Y S T : Scheme.{u}} (f' : X' ⟶ S) (g : T ⟶ S)
    (h : Y ⟶ X') (e : Y ⟶ T) (w : h ≫ f' = e ≫ g) (p : ℤ) (L : PlusAb T) (M : PlusAb Y)
    (κ : (derivedPullbackAb e).obj L ⟶ M) [IsIso κ]
    (hL : IsIso ((homologyAb X' p).map ((smallEtaleDerivedBaseChangeAb f' g h e w).app L))) :
    IsIso (derivedBaseChangeHomologyMap f' g h e w p L M κ) := by
  unfold derivedBaseChangeHomologyMap
  have := hL
  infer_instance

/-- Conversely, if the derived base change map on cohomology sheaves attached to an isomorphism
`κ` is invertible, so is the derived base change map on cohomology sheaves. -/
theorem isIso_homologyMap_of_isIso_derivedBaseChangeHomologyMap {X' Y S T : Scheme.{u}}
    (f' : X' ⟶ S) (g : T ⟶ S) (h : Y ⟶ X') (e : Y ⟶ T) (w : h ≫ f' = e ≫ g) (p : ℤ)
    (L : PlusAb T) (M : PlusAb Y) (κ : (derivedPullbackAb e).obj L ⟶ M) [IsIso κ]
    (hβ : IsIso (derivedBaseChangeHomologyMap f' g h e w p L M κ)) :
    IsIso ((homologyAb X' p).map ((smallEtaleDerivedBaseChangeAb f' g h e w).app L)) := by
  unfold derivedBaseChangeHomologyMap at hβ
  have h₁ := IsIso.of_isIso_comp_left
    ((Stacks.DerivedFunctor.exactRightDerivedPlusHomologyIso (smallEtalePullbackAb f') p).inv.app
      ((derivedPushforwardAb g).obj L))
    ((homologyAb X' p).map ((smallEtaleDerivedBaseChangeAb f' g h e w).app L) ≫
      (homologyAb X' p).map ((derivedPushforwardAb h).map κ))
  exact IsIso.of_isIso_comp_right _
    ((homologyAb X' p).map ((derivedPushforwardAb h).map κ))

/-- The base change map of the limit square on cohomology sheaves is invertible as soon as the
derived base change map is invertible on cohomology sheaves. -/
theorem isIso_derivedLimitComparison_of_isIso {I : Type*} [Preorder I]
    {DX DS DT DY : Iᵒᵖ ⥤ Scheme.{u}} (cX : Cone DX) (cS : Cone DS) (cT : Cone DT) (cY : Cone DY)
    (fL : cX.pt ⟶ cS.pt) (gL : cT.pt ⟶ cS.pt) (hL : cY.pt ⟶ cX.pt) (eL : cY.pt ⟶ cT.pt)
    (wL : hL ≫ fL = eL ≫ gL) (p : ℤ) (M : PlusAb cT.pt)
    (hM : IsIso ((homologyAb cX.pt p).map ((smallEtaleDerivedBaseChangeAb fL gL hL eL wL).app M))) :
    IsIso (derivedLimitComparison cX cS cT cY fL gL hL eL wL p M) := by
  unfold derivedLimitComparison
  infer_instance

/-- The pullbacks of a complex vanishing in degrees `< a` vanish in degrees `< a`. -/
instance isStrictlyGE_ofCocone_obj {K : Type u} [Preorder K] {D : Kᵒᵖ ⥤ Scheme.{u}}
    {T₀ : Scheme.{u}} (ι : ∀ j, D.obj j ⟶ T₀) (hι : ∀ {i j : Kᵒᵖ} (a : i ⟶ j), D.map a ≫ ι j = ι i)
    (G : CochainComplex (Sheaf (smallEtaleTopology T₀) Ab.{u + 1}) ℤ) (a : ℤ) [G.IsStrictlyGE a]
    (j : Kᵒᵖ) : ((EtaleComplexSystem.ofCocone ι hι G).obj j).IsStrictlyGE a :=
  isStrictlyGE_mapHomologicalComplex_smallEtalePullbackAb a (ι j) G

/-! ### Coherence for systems of inverse images of one complex -/

section OfCocone

variable {K : Type u} [Preorder K] {D : Kᵒᵖ ⥤ Scheme.{u}} {T₀ : Scheme.{u}}
  (ι : ∀ j, D.obj j ⟶ T₀) (hι : ∀ {i j : Kᵒᵖ} (a : i ⟶ j), D.map a ≫ ι j = ι i)
  (G : CochainComplex (Sheaf (smallEtaleTopology T₀) Ab.{u + 1}) ℤ)

/-- The cone maps `c_j^{-1}ι_j^{-1}𝒢^• ⟶ g^{-1}𝒢^•` of the system of inverse images of `𝒢^•`
are coherent with the comparisons of inverse images along composites. -/
theorem ofCoconeLeg_assoc (c : Cone D) (gc : c.pt ⟶ T₀) (hgc : ∀ j, c.π.app j ≫ ι j = gc)
    (j : Kᵒᵖ) {Y : Scheme.{u}} (f : Y ⟶ c.pt) (v : Y ⟶ D.obj j) (hv : v = f ≫ c.π.app j)
    (w : Y ⟶ T₀) (hw₁ : w = v ≫ ι j) (hw₂ : w = f ≫ gc) :
    (complexPullbackCompApp f (c.π.app j) v hv ((EtaleComplexSystem.ofCocone ι hι G).obj j)).inv ≫
      ((smallEtalePullbackAb f).mapHomologicalComplex (ComplexShape.up ℤ)).map
        (EtaleComplexSystem.ofCoconeLeg ι hι G c gc hgc j) ≫
      (complexPullbackCompApp f gc w hw₂ G).hom =
    (complexPullbackCompApp v (ι j) w hw₁ G).hom :=
  complexPullbackCompApp_assoc f (c.π.app j) (ι j) v hv gc (hgc j).symm w hw₁ hw₂ G

/-- The transition maps of the system of inverse images of `𝒢^•` are the comparisons of inverse
images along composites. -/
theorem ofCocone_map_eq {i j : Kᵒᵖ} (a : i ⟶ j) :
    (EtaleComplexSystem.ofCocone ι hι G).map a =
      (complexPullbackCompApp (D.map a) (ι j) (ι i) (hι a).symm G).hom :=
  rfl

/-- The transition maps of the system of inverse images of `𝒢^•` are coherent with the
comparisons of inverse images along composites. -/
theorem ofCocone_map_assoc {i j : Kᵒᵖ} (a : i ⟶ j) {Y : Scheme.{u}} (f : Y ⟶ D.obj i)
    (v : Y ⟶ D.obj j) (hv : v = f ≫ D.map a) (w : Y ⟶ T₀) (hw₁ : w = v ≫ ι j)
    (hw₂ : w = f ≫ ι i) :
    (complexPullbackCompApp f (D.map a) v hv ((EtaleComplexSystem.ofCocone ι hι G).obj j)).inv ≫
      ((smallEtalePullbackAb f).mapHomologicalComplex (ComplexShape.up ℤ)).map
        ((EtaleComplexSystem.ofCocone ι hι G).map a) ≫
      (complexPullbackCompApp f (ι i) w hw₂ G).hom =
    (complexPullbackCompApp v (ι j) w hw₁ G).hom :=
  complexPullbackCompApp_assoc f (D.map a) (ι j) v hv (ι i) (hι a).symm w hw₁ hw₂ G


/-- The transition maps of the system of inverse images of `𝒢^•` along `ι'_i`, where `ι'_j`
factors as `g' ≫ k`, are coherent with the comparisons of inverse images along composites. -/
theorem map_ofCocone_map_assoc {D' : Kᵒᵖ ⥤ Scheme.{u}} (ι' : ∀ j, D'.obj j ⟶ T₀)
    (hι' : ∀ {i j : Kᵒᵖ} (a : i ⟶ j), D'.map a ≫ ι' j = ι' i) {i j : Kᵒᵖ} (a : i ⟶ j)
    {Z : Scheme.{u}} (g' : D'.obj j ⟶ Z) (k : Z ⟶ T₀) (hk : ι' j = g' ≫ k)
    (V : D'.obj i ⟶ Z) (hV : V = D'.map a ≫ g') (hw : ι' i = V ≫ k) :
    (complexPullbackCompApp (D'.map a) g' V hV
        (((smallEtalePullbackAb k).mapHomologicalComplex (ComplexShape.up ℤ)).obj G)).inv ≫
      ((smallEtalePullbackAb (D'.map a)).mapHomologicalComplex (ComplexShape.up ℤ)).map
        (complexPullbackCompApp g' k (ι' j) hk G).hom ≫
      (EtaleComplexSystem.ofCocone ι' hι' G).map a =
    (complexPullbackCompApp V k (ι' i) hw G).hom := by
  rw [ofCocone_map_eq ι' hι' G a]
  exact complexPullbackCompApp_assoc (D'.map a) g' k V hV (ι' j) hk (ι' i) hw (hι' a).symm G

end OfCocone

/-! ### The general statement -/

section General

variable {J : Type u} [Preorder J] {DX DS DT DY : Jᵒᵖ ⥤ Scheme.{u}}
  (f : DX ⟶ DS) (g : DT ⟶ DS) (h : DY ⟶ DX) (e : DY ⟶ DT)
  {cX : Cone DX} {cS : Cone DS} {cT : Cone DT} {cY : Cone DY}
  (hcX : IsLimit cX) (hcS : IsLimit cS)
  (fL : cX.pt ⟶ cS.pt) (eL : cY.pt ⟶ cT.pt)
  (hfL : ∀ i : Jᵒᵖ, fL ≫ cS.π.app i = cX.π.app i ≫ f.app i)
  (heL : ∀ i : Jᵒᵖ, eL ≫ cT.π.app i = cY.π.app i ≫ e.app i)
  (w : ∀ i : Jᵒᵖ, h.app i ≫ f.app i = e.app i ≫ g.app i)
  {T₀ : Scheme.{u}} (ι : ∀ j, DT.obj j ⟶ T₀) (hι : ∀ {i j : Jᵒᵖ} (a : i ⟶ j), DT.map a ≫ ι j = ι i)
  (gT : cT.pt ⟶ T₀) (hgT : ∀ j, cT.π.app j ≫ ι j = gT)
  (ιY : ∀ j, DY.obj j ⟶ T₀) (hιY : ∀ {i j : Jᵒᵖ} (a : i ⟶ j), DY.map a ≫ ιY j = ιY i)
  (hιYe : ∀ j, ιY j = e.app j ≫ ι j)

variable (G : CochainComplex (Sheaf (smallEtaleTopology T₀) Ab.{u + 1}) ℤ)

/-- The identification `e_i^{-1}ι_i^{-1}𝒢^• ≅ ιY_i^{-1}𝒢^•` along `ιY_i = e_i ≫ ι_i`. -/
abbrev levelPullbackComparison (j : Jᵒᵖ) :
    ((smallEtalePullbackAb (e.app j)).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        ((EtaleComplexSystem.ofCocone ι hι G).obj j) ⟶
      ((smallEtalePullbackAb (ιY j)).mapHomologicalComplex (ComplexShape.up ℤ)).obj G :=
  (complexPullbackCompApp (e.app j) (ι j) (ιY j) (hιYe j) G).hom

/-- The cone maps of the system of pullbacks of `𝒢^•` to the `Y_i` are coherent with the
comparisons of inverse images along composites. -/
theorem levelPullbackComparison_leg_assoc (c : Cone DY) (gc : c.pt ⟶ T₀)
    (hgc : ∀ j, c.π.app j ≫ ιY j = gc) (j : Jᵒᵖ) (v : c.pt ⟶ DT.obj j)
    (hv : v = c.π.app j ≫ e.app j) (hw : gc = v ≫ ι j) :
    (complexPullbackCompApp (c.π.app j) (e.app j) v hv
        ((EtaleComplexSystem.ofCocone ι hι G).obj j)).inv ≫
      ((smallEtalePullbackAb (c.π.app j)).mapHomologicalComplex (ComplexShape.up ℤ)).map
        (levelPullbackComparison e ι hι ιY hιYe G j) ≫
      EtaleComplexSystem.ofCoconeLeg ιY hιY G c gc hgc j =
    (complexPullbackCompApp v (ι j) gc hw G).hom :=
  complexPullbackCompApp_assoc (c.π.app j) (e.app j) (ι j) v hv (ιY j) (hιYe j) gc hw
    (hgc j).symm G

/-- The transition maps of the system of pullbacks of `𝒢^•` to the `Y_i` are coherent with the
comparisons of inverse images along composites. -/
theorem levelPullbackComparison_map_assoc {i j : Jᵒᵖ} (a : i ⟶ j) (V : DY.obj i ⟶ DT.obj j)
    (hV : V = DY.map a ≫ e.app j) (hw : ιY i = V ≫ ι j) :
    (complexPullbackCompApp (DY.map a) (e.app j) V hV
        ((EtaleComplexSystem.ofCocone ι hι G).obj j)).inv ≫
      ((smallEtalePullbackAb (DY.map a)).mapHomologicalComplex (ComplexShape.up ℤ)).map
        (levelPullbackComparison e ι hι ιY hιYe G j) ≫
        (EtaleComplexSystem.ofCocone ιY hιY G).map a =
    (complexPullbackCompApp V (ι j) (ιY i) hw G).hom :=
  map_ofCocone_map_assoc G ιY hιY a (e.app j) (ι j) (hιYe j) V hV hw

/-- **The level comparison**: the derived base change map of the `i`-th square at the pullbacks
of `𝒢^•`, on degree-`p` cohomology sheaves, pulled back to `X` along `r_i` and read on the source
through the comparison `f^{-1}s_i^{-1} ≅ r_i^{-1}f_i^{-1}`. -/
abbrev derivedLevelComparison (a p : ℤ) [G.IsStrictlyGE a] (j : Jᵒᵖ) :=
  (App fL (cS.π.app j) (cX.π.app j ≫ f.app j) (hfL j).symm _).hom ≫
    (@smallEtalePullbackAbCompApp cX.pt (DX.obj j) (DS.obj j) (cX.π.app j) (f.app j)
      (cX.π.app j ≫ f.app j) rfl _).inv ≫
      (smallEtalePullbackAb (X := cX.pt) (cX.π.app j)).map (derivedBaseChangeHomologyMap (f.app j)
        (g.app j) (h.app j) (e.app j) (w j) p
        (plusDerivedObj a ((EtaleComplexSystem.ofCocone ι hι G).obj j))
        (plusDerivedObj a ((EtaleComplexSystem.ofCocone ιY hιY G).obj j))
        (smallEtaleComplexPullbackComparison a (e.app j) _ _
          (levelPullbackComparison e ι hι ιY hιYe G j)))

/-- The legs of the system for `g`, with the vertices of the cones as the sources of the
projections. -/
theorem complexLeg_g_eq (a p : ℤ) [G.IsStrictlyGE a] (j : Jᵒᵖ) :
    complexLeg g p a (EtaleComplexSystem.ofCocone ι hι G) cT cS hcS _
        (EtaleComplexSystem.ofCoconeLeg ι hι G cT gT hgT) j =
      derivedBaseChangeHomologyMap (X' := cS.pt) (Y := cT.pt) (cS.π.app j) (g.app j)
        (limitMorphism g cT cS hcS) (cT.π.app j) (limitMorphism_comp_π g cT cS hcS j) p
        (plusDerivedObj a ((EtaleComplexSystem.ofCocone ι hι G).obj j))
        (plusDerivedObj a (((smallEtalePullbackAb gT).mapHomologicalComplex _).obj G))
        (smallEtaleComplexPullbackComparison a (X := cT.pt) (cT.π.app j) _ _
          (EtaleComplexSystem.ofCoconeLeg ι hι G cT gT hgT j)) :=
  rfl

/-- The legs of the system for `h`, with the vertices of the cones as the sources of the
projections. -/
theorem complexLeg_h_eq (a p : ℤ) [G.IsStrictlyGE a] (gY : cY.pt ⟶ T₀)
    (hgY : ∀ j, cY.π.app j ≫ ιY j = gY) (j : Jᵒᵖ) :
    complexLeg h p a (EtaleComplexSystem.ofCocone ιY hιY G) cY cX hcX _
        (EtaleComplexSystem.ofCoconeLeg ιY hιY G cY gY hgY) j =
      derivedBaseChangeHomologyMap (X' := cX.pt) (Y := cY.pt) (cX.π.app j) (h.app j)
        (limitMorphism h cY cX hcX) (cY.π.app j) (limitMorphism_comp_π h cY cX hcX j) p
        (plusDerivedObj a ((EtaleComplexSystem.ofCocone ιY hιY G).obj j))
        (plusDerivedObj a (((smallEtalePullbackAb gY).mapHomologicalComplex _).obj G))
        (smallEtaleComplexPullbackComparison a (X := cY.pt) (cY.π.app j) _ _
          (EtaleComplexSystem.ofCoconeLeg ιY hιY G cY gY hgY j)) :=
  rfl

/-- The maps of the pulled back diagram for `g`, with the vertex of the cone as source. -/
theorem pullbackDiagramMap_g_eq (a p : ℤ) [G.IsStrictlyGE a] {i j : Jᵒᵖ} (c : i ⟶ j) :
    (complexHigherDirectImageSystem g p a
        (EtaleComplexSystem.ofCocone ι hι G)).pullbackDiagramMap cS (i := i) (j := j) c =
      (@smallEtalePullbackAbCompApp cS.pt (DS.obj i) (DS.obj j) (cS.π.app i) (DS.map c)
          (cS.π.app j) (cS.w c).symm _).inv ≫
        (smallEtalePullbackAb (X := cS.pt) (cS.π.app i)).map
          (derivedBaseChangeHomologyMap (DS.map c) (g.app j) (g.app i) (DT.map c)
            (transition_comm g c) p
            (plusDerivedObj a ((EtaleComplexSystem.ofCocone ι hι G).obj j))
            (plusDerivedObj a ((EtaleComplexSystem.ofCocone ι hι G).obj i))
            (complexTransitionComparison a (EtaleComplexSystem.ofCocone ι hι G) c)) := by
  rw [EtaleSheafSystem.pullbackDiagramMap, conePullbackComp_inv_app_eq]
  rfl

/-- The maps of the pulled back diagram for `h`, with the vertex of the cone as source. -/
theorem pullbackDiagramMap_h_eq (a p : ℤ) [G.IsStrictlyGE a] {i j : Jᵒᵖ} (c : i ⟶ j) :
    (complexHigherDirectImageSystem h p a
        (EtaleComplexSystem.ofCocone ιY hιY G)).pullbackDiagramMap cX (i := i) (j := j) c =
      (@smallEtalePullbackAbCompApp cX.pt (DX.obj i) (DX.obj j) (cX.π.app i) (DX.map c)
          (cX.π.app j) (cX.w c).symm _).inv ≫
        (smallEtalePullbackAb (X := cX.pt) (cX.π.app i)).map
          (derivedBaseChangeHomologyMap (DX.map c) (h.app j) (h.app i) (DY.map c)
            (transition_comm h c) p
            (plusDerivedObj a ((EtaleComplexSystem.ofCocone ιY hιY G).obj j))
            (plusDerivedObj a ((EtaleComplexSystem.ofCocone ιY hιY G).obj i))
            (complexTransitionComparison a (EtaleComplexSystem.ofCocone ιY hιY G) c)) :=
  pullbackDiagramMap_g_eq h ιY hιY G a p c

include heL in
/-- The two pasted comparisons of the derived inverse images of the pullbacks of `𝒢^•` in the
leg compatibility agree. -/
theorem legs_coherence (a : ℤ) [G.IsStrictlyGE a]
    (hgY : ∀ j, cY.π.app j ≫ ιY j = eL ≫ gT) (j : Jᵒᵖ) :
    (smallEtaleDerivedPullbackAbPlusComp' (cT.π.app j) eL (cY.π.app j ≫ e.app j)
        (heL j).symm).inv.app (plusDerivedObj a ((EtaleComplexSystem.ofCocone ι hι G).obj j)) ≫
      (derivedPullbackAb eL).map (smallEtaleComplexPullbackComparison a (cT.π.app j) _
        (((smallEtalePullbackAb gT).mapHomologicalComplex _).obj G)
        (EtaleComplexSystem.ofCoconeLeg ι hι G cT gT hgT j)) ≫
      smallEtaleComplexPullbackComparison a eL _
        (((smallEtalePullbackAb (eL ≫ gT)).mapHomologicalComplex _).obj G)
        (complexPullbackCompApp eL gT (eL ≫ gT) rfl G).hom =
    (smallEtaleDerivedPullbackAbPlusComp' (e.app j) (cY.π.app j) (cY.π.app j ≫ e.app j)
        rfl).inv.app (plusDerivedObj a ((EtaleComplexSystem.ofCocone ι hι G).obj j)) ≫
      (derivedPullbackAb (cY.π.app j)).map (smallEtaleComplexPullbackComparison a (e.app j) _
        ((EtaleComplexSystem.ofCocone ιY hιY G).obj j)
        (levelPullbackComparison e ι hι ιY hιYe G j)) ≫
      smallEtaleComplexPullbackComparison a (cY.π.app j) _
        (((smallEtalePullbackAb (eL ≫ gT)).mapHomologicalComplex _).obj G)
        (EtaleComplexSystem.ofCoconeLeg ιY hιY G cY (eL ≫ gT) hgY j) := by
  have h₁ : eL ≫ gT = (cY.π.app j ≫ e.app j) ≫ ι j := by
    rw [Category.assoc, ← hιYe, hgY j]
  exact smallEtaleComplexPullbackComparison_paste_eq a (cT.π.app j) eL (e.app j) (cY.π.app j)
    (cY.π.app j ≫ e.app j) (heL j).symm rfl _ _ _ _ _ _ _ _
    ((ofCoconeLeg_assoc ι hι G cT gT hgT j eL (cY.π.app j ≫ e.app j) (heL j).symm (eL ≫ gT) h₁
      rfl).trans
      (levelPullbackComparison_leg_assoc e ι hι ιY hιY hιYe G cY (eL ≫ gT) hgY j
        (cY.π.app j ≫ e.app j) rfl h₁).symm)

/-- The two pasted comparisons of the derived inverse images of the pullbacks of `𝒢^•` in the
transition compatibility agree. -/
theorem diagram_coherence (a : ℤ) [G.IsStrictlyGE a] {i j : Jᵒᵖ} (c : i ⟶ j) :
    (smallEtaleDerivedPullbackAbPlusComp' (DT.map c) (e.app i) (DY.map c ≫ e.app j)
        (e.naturality c)).inv.app
          (plusDerivedObj a ((EtaleComplexSystem.ofCocone ι hι G).obj j)) ≫
      (derivedPullbackAb (e.app i)).map
        (complexTransitionComparison a (EtaleComplexSystem.ofCocone ι hι G) c) ≫
      smallEtaleComplexPullbackComparison a (e.app i) _ _
        (levelPullbackComparison e ι hι ιY hιYe G i) =
    (smallEtaleDerivedPullbackAbPlusComp' (e.app j) (DY.map c) (DY.map c ≫ e.app j) rfl).inv.app
        (plusDerivedObj a ((EtaleComplexSystem.ofCocone ι hι G).obj j)) ≫
      (derivedPullbackAb (DY.map c)).map
        (smallEtaleComplexPullbackComparison a (e.app j) _ _
          (levelPullbackComparison e ι hι ιY hιYe G j)) ≫
      complexTransitionComparison a (EtaleComplexSystem.ofCocone ιY hιY G) c := by
  have h₁ : ιY i = (DY.map c ≫ e.app j) ≫ ι j := by
    rw [Category.assoc, ← hιYe, hιY c]
  exact smallEtaleComplexPullbackComparison_paste_eq a (DT.map c) (e.app i) (e.app j) (DY.map c)
    (DY.map c ≫ e.app j) (e.naturality c) rfl _ _ _ _ _ _ _ _
    ((ofCocone_map_assoc ι hι G c (e.app i) (DY.map c ≫ e.app j) (e.naturality c)
      (ιY i) h₁ (hιYe i)).trans
      (levelPullbackComparison_map_assoc e ι hι ιY hιY hιYe G c (DY.map c ≫ e.app j) rfl h₁).symm)

include heL in
/-- **The level comparisons are compatible with the base change map of the limit square.** -/
theorem map_complexLeg_comp_derivedBaseChangeHomologyMap (a p : ℤ) [G.IsStrictlyGE a]
    (wL : limitMorphism h cY cX hcX ≫ fL = eL ≫ limitMorphism g cT cS hcS)
    (hgY : ∀ j, cY.π.app j ≫ ιY j = eL ≫ gT) (j : Jᵒᵖ) :
    (smallEtalePullbackAb fL).map (complexLeg g p a (EtaleComplexSystem.ofCocone ι hι G) cT cS
        hcS _ (EtaleComplexSystem.ofCoconeLeg ι hι G cT gT hgT) j) ≫
      derivedBaseChangeHomologyMap fL (limitMorphism g cT cS hcS) (limitMorphism h cY cX hcX) eL wL
        p (plusDerivedObj a (((smallEtalePullbackAb gT).mapHomologicalComplex _).obj G))
        (plusDerivedObj a (((smallEtalePullbackAb (eL ≫ gT)).mapHomologicalComplex _).obj G))
        (smallEtaleComplexPullbackComparison a eL _ _
          (complexPullbackCompApp eL gT (eL ≫ gT) rfl G).hom) =
    derivedLevelComparison f g h e fL hfL w ι hι ιY hιY hιYe G a p j ≫
      complexLeg h p a (EtaleComplexSystem.ofCocone ιY hιY G) cY cX hcX _
        (EtaleComplexSystem.ofCoconeLeg ιY hιY G cY (eL ≫ gT) hgY) j := by
  rw [complexLeg_g_eq g hcS ι hι gT hgT G a p j,
    complexLeg_h_eq h hcX ιY hιY G a p (eL ≫ gT) hgY j]
  exact derivedBaseChangeHomologyMap_legs (X := cX.pt) (S := cS.pt) (T := cT.pt) (Y := cY.pt)
    (X₀ := DX.obj j) (S₀ := DS.obj j) (T₀ := DT.obj j) (Y₀ := DY.obj j) fL
    (limitMorphism g cT cS hcS) (limitMorphism h cY cX hcX) eL (cX.π.app j) (cS.π.app j)
    (cT.π.app j) (cY.π.app j) (f.app j) (g.app j) (h.app j) (e.app j) (cX.π.app j ≫ f.app j)
    (cY.π.app j ≫ e.app j) (hfL j).symm rfl (heL j).symm rfl (limitMorphism_comp_π g cT cS hcS j)
    (limitMorphism_comp_π h cY cX hcX j) (w j) wL p _ _ _ _ _ _ _ _
    (legs_coherence e eL heL ι hι gT hgT ιY hιY hιYe G a hgY j)

/-- **The level comparisons commute with the transition maps** of the two systems. -/
theorem map_pullbackDiagramMap_comp_derivedLevelComparison (a p : ℤ) [G.IsStrictlyGE a]
    {i j : Jᵒᵖ} (c : i ⟶ j) :
    (smallEtalePullbackAb fL).map ((complexHigherDirectImageSystem g p a
        (EtaleComplexSystem.ofCocone ι hι G)).pullbackDiagramMap cS (i := i) (j := j) c) ≫
      derivedLevelComparison f g h e fL hfL w ι hι ιY hιY hιYe G a p i =
    derivedLevelComparison f g h e fL hfL w ι hι ιY hιY hιYe G a p j ≫
      (complexHigherDirectImageSystem h p a
        (EtaleComplexSystem.ofCocone ιY hιY G)).pullbackDiagramMap cX (i := i) (j := j) c := by
  rw [pullbackDiagramMap_g_eq g ι hι G a p c, pullbackDiagramMap_h_eq h ιY hιY G a p c]
  exact derivedBaseChangeHomologyMap_diagram (X := cX.pt) (S := cS.pt) (Xi := DX.obj i)
    (Xj := DX.obj j) (Si := DS.obj i) (Sj := DS.obj j) (Ti := DT.obj i) (Tj := DT.obj j)
    (Yi := DY.obj i) (Yj := DY.obj j) fL (cX.π.app i) (cX.π.app j) (cS.π.app i)
    (cS.π.app j) (f.app i) (f.app j) (g.app i) (g.app j) (h.app i) (h.app j) (e.app i) (e.app j)
    (DX.map c) (DS.map c) (DT.map c) (DY.map c) (cX.w c).symm (cS.w c).symm (transition_comm g c)
    (transition_comm h c) (w i) (w j) (cX.π.app i ≫ f.app i) (cX.π.app j ≫ f.app j) (hfL i).symm
    rfl (hfL j).symm rfl (DX.map c ≫ f.app j) rfl (f.naturality c) (DY.map c ≫ e.app j) rfl
    (e.naturality c) p _ _ _ _ _ _ _ _ (diagram_coherence e ι hι ιY hιY hιYe G a c)

/-- The level comparison is invertible as soon as the derived base change map of the level
square is invertible at the pullback of `K₀`. -/
theorem isIso_derivedLevelComparison (a p : ℤ) [G.IsStrictlyGE a] {K₀ : PlusAb T₀}
    (eG : K₀ ≅ plusDerivedObj a G) (j : Jᵒᵖ)
    (hj : IsIso ((smallEtaleDerivedBaseChangeAb (f.app j) (g.app j) (h.app j) (e.app j)
      (w j)).app ((derivedPullbackAb (ι j)).obj K₀))) :
    IsIso (derivedLevelComparison f g h e fL hfL w ι hι ιY hιY hιYe G a p j) := by
  have h₁ : IsIso ((homologyAb (DX.obj j) p).map
      ((smallEtaleDerivedBaseChangeAb (f.app j) (g.app j) (h.app j) (e.app j) (w j)).app
        (plusDerivedObj a ((EtaleComplexSystem.ofCocone ι hι G).obj j)))) :=
    isIso_map_smallEtaleDerivedBaseChangeAb_app_of_iso _ _ _ _ _ (homologyAb (DX.obj j) p)
      ((complexPullbackIso a (ι j) G eG).symm :
        (derivedPullbackAb (ι j)).obj K₀ ≅
          plusDerivedObj a ((EtaleComplexSystem.ofCocone ι hι G).obj j))
      (Functor.map_isIso _ _)
  have hl : IsIso (levelPullbackComparison e ι hι ιY hιYe G j) :=
    inferInstanceAs (IsIso (complexPullbackCompApp (e.app j) (ι j) (ιY j) (hιYe j) G).hom)
  have := @isIso_smallEtaleComplexPullbackComparison a _ _ (e.app j) _ _
    ((EtaleComplexSystem.ofCocone ιY hιY G).obj j) _ (levelPullbackComparison e ι hι ιY hιYe G j)
    hl
  have := isIso_derivedBaseChangeHomologyMap (f.app j) (g.app j) (h.app j) (e.app j) (w j) p
    (plusDerivedObj a ((EtaleComplexSystem.ofCocone ι hι G).obj j))
    (plusDerivedObj a ((EtaleComplexSystem.ofCocone ιY hιY G).obj j))
    (smallEtaleComplexPullbackComparison a (e.app j) _ _
      (levelPullbackComparison e ι hι ιY hιYe G j)) h₁
  infer_instance

include hcX hcS hfL heL hι hgT in
/-- **Base change passes to the limit for pullbacks of a bounded below object**, for a system of
morphisms `ι_i : T_i ⟶ T₀` compatible with the transition maps and `g_T : T ⟶ T₀` with
`p_i ≫ ι_i = g_T`: if the derived base change map of every level is an isomorphism at
`R ι_i^{-1}K₀`, the derived base change map of the limit square is an isomorphism at
`R g_T^{-1}K₀`. -/
theorem isIso_smallEtaleDerivedBaseChangeAb_limit_of_cocone [IsDirected J (· ≤ ·)] [Nonempty J]
    [∀ {i j : Jᵒᵖ} (a : i ⟶ j), IsAffineHom (DX.map a)]
    [∀ {i j : Jᵒᵖ} (a : i ⟶ j), IsAffineHom (DS.map a)]
    [∀ {i j : Jᵒᵖ} (a : i ⟶ j), IsAffineHom (DT.map a)]
    [∀ {i j : Jᵒᵖ} (a : i ⟶ j), IsAffineHom (DY.map a)]
    [∀ i, QuasiCompact (g.app i)] [∀ i, QuasiSeparated (g.app i)]
    [∀ i, QuasiCompact (h.app i)] [∀ i, QuasiSeparated (h.app i)]
    (hcT : IsLimit cT) (hcY : IsLimit cY) (gL : cT.pt ⟶ cS.pt) (hL : cY.pt ⟶ cX.pt)
    (hgL : ∀ i, gL ≫ cS.π.app i = cT.π.app i ≫ g.app i)
    (hhL : ∀ i, hL ≫ cX.π.app i = cY.π.app i ≫ h.app i) (wL : hL ≫ fL = eL ≫ gL)
    (K₀ : PlusAb T₀)
    (hstage : ∀ j, IsIso ((smallEtaleDerivedBaseChangeAb (f.app j) (g.app j) (h.app j) (e.app j)
      (w j)).app ((derivedPullbackAb (ι j)).obj K₀))) :
    IsIso ((smallEtaleDerivedBaseChangeAb fL gL hL eL wL).app ((derivedPullbackAb gT).obj K₀)) := by
  obtain rfl : gL = limitMorphism g cT cS hcS :=
    hcS.hom_ext fun i => by rw [hgL, limitMorphism_comp_π]
  obtain rfl : hL = limitMorphism h cY cX hcX :=
    hcX.hom_ext fun i => by rw [hhL, limitMorphism_comp_π]
  obtain ⟨a, G, _, ⟨eG⟩⟩ := exists_iso_plusDerivedObj K₀
  obtain ⟨ιY, hιYe⟩ : ∃ ιY : ∀ j, DY.obj j ⟶ T₀, ∀ j, ιY j = e.app j ≫ ι j :=
    ⟨fun j => e.app j ≫ ι j, fun _ => rfl⟩
  have hιY : ∀ {i j : Jᵒᵖ} (c : i ⟶ j), DY.map c ≫ ιY j = ιY i := fun c => by
    rw [hιYe, hιYe, ← Category.assoc, e.naturality, Category.assoc, hι c]
  have hgY : ∀ j, cY.π.app j ≫ ιY j = eL ≫ gT := fun j => by
    rw [hιYe, ← Category.assoc, ← heL j, Category.assoc, hgT j]
  refine isIso_of_forall_isIso_derivedLimitComparison cX cS cT cY fL _ _ eL wL _ fun p => ?_
  have hβ : IsIso (derivedBaseChangeHomologyMap fL (limitMorphism g cT cS hcS)
      (limitMorphism h cY cX hcX) eL wL p
      (plusDerivedObj a (((smallEtalePullbackAb gT).mapHomologicalComplex _).obj G))
      (plusDerivedObj a (((smallEtalePullbackAb (eL ≫ gT)).mapHomologicalComplex _).obj G))
      (smallEtaleComplexPullbackComparison a eL _ _
        (complexPullbackCompApp eL gT (eL ≫ gT) rfl G).hom)) := by
    obtain ⟨hcocT, hcolT⟩ := complexHigherDirectImageColimit g hcT hcS
      (EtaleComplexSystem.ofCocone ι hι G) a _ (EtaleComplexSystem.ofCoconeLeg ι hι G cT gT hgT)
      (EtaleComplexSystem.isPullbackCocone_ofCocone ι hι G cT gT hgT)
      (EtaleComplexSystem.isPullbackColimitPresentation_ofCocone ι hι G cT gT hgT) p
    obtain ⟨hcocY, hcolY⟩ := complexHigherDirectImageColimit h hcY hcX
      (EtaleComplexSystem.ofCocone ιY hιY G) a _
      (EtaleComplexSystem.ofCoconeLeg ιY hιY G cY (eL ≫ gT) hgY)
      (EtaleComplexSystem.isPullbackCocone_ofCocone ιY hιY G cY (eL ≫ gT) hgY)
      (EtaleComplexSystem.isPullbackColimitPresentation_ofCocone ιY hιY G cY (eL ≫ gT) hgY) p
    have hθ : ∀ j, IsIso (derivedLevelComparison f g h e fL hfL w ι hι ιY hιY hιYe G a p j) :=
      fun j => isIso_derivedLevelComparison f g h e fL hfL w ι hι ιY hιY hιYe G a p eG j
        (hstage j)
    exact @IsSystemColimit.isIso_of_isIso_app _ _ _ _ _ _ _ _
      (hcolT.map_of_isLeftAdjoint (smallEtaleAdjunctionAb fL))
      (fun c => by rw [← Functor.map_comp, hcocT c]) _ _ _ _ hcolY hcocY
      (derivedLevelComparison f g h e fL hfL w ι hι ιY hιY hιYe G a p) hθ
      (fun c => map_pullbackDiagramMap_comp_derivedLevelComparison f g h e fL hfL w ι hι ιY hιY
        hιYe G a p c) _
      (fun j => map_complexLeg_comp_derivedBaseChangeHomologyMap f g h e hcX hcS fL eL hfL heL w
        ι hι gT hgT ιY hιY hιYe G a p wL hgY j)
  have := isIso_smallEtaleComplexPullbackComparison a eL
    (((smallEtalePullbackAb gT).mapHomologicalComplex _).obj G)
    (((smallEtalePullbackAb (eL ≫ gT)).mapHomologicalComplex _).obj G)
    (complexPullbackCompApp eL gT (eL ≫ gT) rfl G).hom
  have h₁ := isIso_homologyMap_of_isIso_derivedBaseChangeHomologyMap fL _ _ eL wL p _ _ _ hβ
  have h₂ := isIso_map_smallEtaleDerivedBaseChangeAb_app_of_iso fL _ _ eL wL (homologyAb cX.pt p)
    (complexPullbackIso a gT G eG) h₁
  exact isIso_derivedLimitComparison_of_isIso cX cS cT cY fL _ _ eL wL p _ h₂

end General

/-! ### Stacks 0GJL -/

section Tag

attribute [local instance] isDirected_Ici

/-- Invertibility of the derived base change map at an object is insensitive to how the data are
written. -/
theorem isIso_smallEtaleDerivedBaseChangeAb_app_congr {X' Y S T : Scheme.{u}}
    {f₁ f₂ : X' ⟶ S} {g₁ g₂ : T ⟶ S} {h₁ h₂ : Y ⟶ X'} {e₁ e₂ : Y ⟶ T} (hf : f₁ = f₂)
    (hg : g₁ = g₂) (hh : h₁ = h₂) (he : e₁ = e₂) (w₁ : h₁ ≫ f₁ = e₁ ≫ g₁)
    (w₂ : h₂ ≫ f₂ = e₂ ≫ g₂) {L₁ L₂ : PlusAb T} (hL : L₁ = L₂)
    (H : IsIso ((smallEtaleDerivedBaseChangeAb f₁ g₁ h₁ e₁ w₁).app L₁)) :
    IsIso ((smallEtaleDerivedBaseChangeAb f₂ g₂ h₂ e₂ w₂).app L₂) := by
  subst hf hg hh he hL
  exact H

variable {I : Type u} [Preorder I] {DX DS DT DY : Iᵒᵖ ⥤ Scheme.{u}}
  (f : DX ⟶ DS) (g : DT ⟶ DS) (h : DY ⟶ DX) (e : DY ⟶ DT)
  {cX : Cone DX} {cS : Cone DS} {cT : Cone DT} {cY : Cone DY}

/-- Let `I` be a directed set and let `(X_i, Y_i, S_i, T_i, f_i, h_i, e_i, g_i)` be an inverse
system of cartesian squares of schemes with affine transition morphisms and with `g_i`
quasi-compact and quasi-separated, with limit square `(X, Y, S, T, f, h, e, g)`. Let `0 = i₀ ∈ I`,
let `K_0 ∈ D^+(T_{0, étale})`, let `K_i` be the pullback of `K_0` to `T_i` for `i ≥ 0` and `K` the
pullback of `K_0` to `T`. If the derived base change map
`f_i^{-1}Rg_{i, *}K_i ⟶ Rh_{i, *}e_i^{-1}K_i` is an isomorphism for all `i ≥ 0`, then so is
`f^{-1}Rg_*K ⟶ Rh_*e^{-1}K`.

The limit morphisms are any morphisms `f`, `g`, `h`, `e` satisfying the equations of the
projection squares. -/
@[stacks 0GJL]
theorem isIso_smallEtaleDerivedBaseChangeAb_limit_of_isLimit [IsDirected I (· ≤ ·)] [Nonempty I]
    [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (DX.map a)]
    [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (DS.map a)]
    [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (DT.map a)]
    [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (DY.map a)]
    [∀ i, QuasiCompact (g.app i)] [∀ i, QuasiSeparated (g.app i)]
    (hsq : ∀ i : Iᵒᵖ, IsPullback (h.app i) (e.app i) (f.app i) (g.app i))
    (hcX : IsLimit cX) (hcS : IsLimit cS) (hcT : IsLimit cT) (hcY : IsLimit cY)
    (fL : cX.pt ⟶ cS.pt) (gL : cT.pt ⟶ cS.pt) (hL : cY.pt ⟶ cX.pt) (eL : cY.pt ⟶ cT.pt)
    (hfL : ∀ i : Iᵒᵖ, fL ≫ cS.π.app i = cX.π.app i ≫ f.app i)
    (hgL : ∀ i : Iᵒᵖ, gL ≫ cS.π.app i = cT.π.app i ≫ g.app i)
    (hhL : ∀ i : Iᵒᵖ, hL ≫ cX.π.app i = cY.π.app i ≫ h.app i)
    (heL : ∀ i : Iᵒᵖ, eL ≫ cT.π.app i = cY.π.app i ≫ e.app i)
    (i₀ : I) (K₀ : PlusAb (DT.obj (op i₀)))
    (hstage : ∀ (i : Iᵒᵖ) (a : i ⟶ op i₀),
      IsIso ((smallEtaleDerivedBaseChangeAb (f.app i) (g.app i) (h.app i) (e.app i)
        (hsq i).w).app (stageObj K₀ a))) :
    IsIso ((smallEtaleDerivedBaseChangeAb fL gL hL eL
      (LimitBaseChange.limitSquare_comm f g h e cX cS cT cY fL gL hL eL hcS hfL hgL hhL heL
        fun i => (hsq i).w)).app (limitObj cT K₀)) := by
  have : ∀ i, QuasiCompact (h.app i) := fun i =>
    MorphismProperty.of_isPullback (P := @QuasiCompact) (hsq i).flip inferInstance
  have : ∀ i, QuasiSeparated (h.app i) := fun i =>
    MorphismProperty.of_isPullback (P := @QuasiSeparated) (hsq i).flip inferInstance
  have : Nonempty (Set.Ici i₀) := ⟨⟨i₀, le_rfl⟩⟩
  have : ∀ j, QuasiCompact ((Functor.whiskerLeft (aboveInclusion i₀) g).app j) := fun j =>
    inferInstanceAs (QuasiCompact (g.app ((aboveInclusion i₀).obj j)))
  have : ∀ j, QuasiSeparated ((Functor.whiskerLeft (aboveInclusion i₀) g).app j) := fun j =>
    inferInstanceAs (QuasiSeparated (g.app ((aboveInclusion i₀).obj j)))
  have : ∀ j, QuasiCompact ((Functor.whiskerLeft (aboveInclusion i₀) h).app j) := fun j =>
    inferInstanceAs (QuasiCompact (h.app ((aboveInclusion i₀).obj j)))
  have : ∀ j, QuasiSeparated ((Functor.whiskerLeft (aboveInclusion i₀) h).app j) := fun j =>
    inferInstanceAs (QuasiSeparated (h.app ((aboveInclusion i₀).obj j)))
  have hcX' := (Functor.Initial.isLimitWhiskerEquiv (aboveInclusion i₀) cX).symm hcX
  have hcS' := (Functor.Initial.isLimitWhiskerEquiv (aboveInclusion i₀) cS).symm hcS
  have hcT' := (Functor.Initial.isLimitWhiskerEquiv (aboveInclusion i₀) cT).symm hcT
  have hcY' := (Functor.Initial.isLimitWhiskerEquiv (aboveInclusion i₀) cY).symm hcY
  have hst : ∀ j : (Set.Ici i₀)ᵒᵖ, IsIso ((smallEtaleDerivedBaseChangeAb
      ((Functor.whiskerLeft (aboveInclusion i₀) f).app j)
      ((Functor.whiskerLeft (aboveInclusion i₀) g).app j)
      ((Functor.whiskerLeft (aboveInclusion i₀) h).app j)
      ((Functor.whiskerLeft (aboveInclusion i₀) e).app j) (hsq _).w).app
        ((derivedPullbackAb (DT.map (aboveTransition i₀ j))).obj K₀)) := fun j =>
    isIso_smallEtaleDerivedBaseChangeAb_app_congr rfl rfl rfl rfl _ _ rfl
      (hstage _ (aboveTransition i₀ j))
  have key := isIso_smallEtaleDerivedBaseChangeAb_limit_of_cocone
    (Functor.whiskerLeft (aboveInclusion i₀) f) (Functor.whiskerLeft (aboveInclusion i₀) g)
    (Functor.whiskerLeft (aboveInclusion i₀) h) (Functor.whiskerLeft (aboveInclusion i₀) e)
    hcX' hcS' fL eL (fun j => hfL _) (fun j => heL _) (fun j => (hsq _).w)
    (fun j : (Set.Ici i₀)ᵒᵖ => DT.map (aboveTransition i₀ j))
    (fun {_ _} c => (map_aboveTransition (DX := DT) i₀ c).symm)
    (cT.π.app (op i₀)) (fun j => cT.w (aboveTransition i₀ j)) hcT' hcY' gL hL
    (fun j => hgL _) (fun j => hhL _)
    (LimitBaseChange.limitSquare_comm f g h e cX cS cT cY fL gL hL eL hcS hfL hgL hhL heL
      fun i => (hsq i).w) K₀ hst
  exact key

end Tag

end Stacks.EtaleCohomology.LimitBaseChangeDerived

end
