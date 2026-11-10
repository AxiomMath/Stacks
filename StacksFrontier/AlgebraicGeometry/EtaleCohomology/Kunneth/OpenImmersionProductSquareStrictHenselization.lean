module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Kunneth.OpenImmersionProductSquareRestriction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmoothBaseChange.SmoothLimitBaseChangeHolds
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmoothBaseChange.FieldExtensionBaseChange
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.HenselianRings.StrictHenselizationDirectedSystem

/-!
# The base change map of the product square of an open, pulled back to a strict henselization

Let `K` be a field, `j : U ⟶ X` a quasi-compact quasi-separated morphism of schemes over `K`, `Y`
a scheme over `K` and `𝓕` an abelian sheaf on `U_étale` annihilated by an integer invertible in
`K`. The proof of [Stacks, Tag 0F1H] studies the stalk of the base change map
`q⁻¹ R^i j_* 𝓕 ⟶ R^i h_* p⁻¹ 𝓕` of the square
```
Y ×_K X  ←-h-  Y ×_K U
   |q              |p
   X     ←-j-      U
```
at a geometric point `z̄` of `Y ×_K X` lying over `x ∈ X`, by pulling the square back to
`X' = Spec(𝒪^{sh}_{X,x̄})`: *"Observe that `X' ⟶ X` is a filtered colimit of étale morphisms. By
smooth base change in the form of Lemma 0F09 the pullback of `q⁻¹Rj_*𝓕 ⟶ Rh_*p⁻¹𝓕` to
`Y ×_K X'` is the map `(q')⁻¹Rj'_*𝓕' ⟶ Rh'_*(p')⁻¹𝓕'` [...] So it suffices to show that
`(q')⁻¹Rj'_*𝓕' ⟶ Rh'_*(p')⁻¹𝓕'` is an isomorphism in order to prove that our original map is an
isomorphism on stalks at `z̄`."* The point `z ↦ y ∈ Y` is treated in the same way with
`Y' = Spec(𝒪^{sh}_{Y,ȳ})`. This file proves both steps.

## Main results

* `OpenImmersionProductSquare.isIso_map_higherBaseChangeMapAb_iff_of_isIso_restriction_right` and
  `...left` — the restriction of the base change map along any `a : X' ⟶ X` (resp. `b : Y' ⟶ Y`)
  whose two auxiliary base change maps are invertible, after any functor.
* `Stacks.EtaleCohomology.isIso_higherBaseChangeMapAb_of_isPullback_strictHenselizationToBase` —
  [Stacks, Tag 0F09] for a base change of the strict henselization `X' ⟶ X`, which is a directed
  limit of affine étale neighbourhoods.
* `OpenImmersionProductSquare.isIso_stalk_higherBaseChangeMapAb_of_strictHenselization_right` —
  the stalk at `z̄` is invertible once the base change map of the square over `X'` is.
* `OpenImmersionProductSquare.isIso_stalk_higherBaseChangeMapAb_of_strictHenselization_left` —
  the stalk at `z̄` is invertible once the base change map of the square of `Y'` is.

## References

* [Stacks Project, Tag 0F1H](https://stacks.math.columbia.edu/tag/0F1H)
* [Stacks Project, Tag 0F09](https://stacks.math.columbia.edu/tag/0F09)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology

/-! ### Smooth base change along a base change of a strict henselization -/

/-- An abelian sheaf annihilated by an integer `n` invertible in a field `K` has torsion of orders
invertible on any scheme `S` over `K`. -/
theorem hasTorsionOrdersInvertibleOn_of_zsmul_eq_zero {K : Type u} [Field K] {S T : Scheme.{u}}
    (sS : S ⟶ Spec (.of K)) {n : ℤ} (hn : IsUnit (n : K))
    (F : Sheaf (smallEtaleTopology T) Ab.{u + 1})
    (hF : ∀ (V : T.Etale) (x : F.obj.obj (op V)), n • x = 0) :
    HasTorsionOrdersInvertibleOn S F :=
  FieldExtensionBaseChange.hasTorsionOrdersInvertibleOn_of_isPrimeToCharacteristicTorsion sS
    (BaseChangeOverField.isPrimeToCharacteristicTorsion_of_zsmul_eq_zero K hn F hF)

/-- **[Stacks, Tag 0F09] along a base change of a strict henselization.** Let `X` be a scheme in
a big étale site `B`, `s` a geometric point of `X`, `x' : X' ⟶ X` the strict henselization at
`s`, and `g : S' ⟶ S` the base change of `x'` along a morphism `t : S ⟶ X`. For every
quasi-compact quasi-separated `f : T ⟶ S`, every cartesian square `f' : T' ⟶ S'`, `g' : T' ⟶ T`
over `g` and `f`, and every abelian sheaf `G` on `T` with torsion of orders invertible on `S`,
the base change map `g⁻¹ R^q f_* G ⟶ R^q f'_* (g')⁻¹ G` is invertible.

`X'` is the directed limit of the affine étale neighbourhoods `V_i ⟶ X` of `s`
(`AlgebraicGeometry.nbhdConeIsLimit`), so `S'` is the directed limit of the étale `S`-schemes
`V_i ×_X S` (`Stacks.EtaleCohomology.isLimit_of_isPullback_stages`); this is
`Stacks.EtaleCohomology.isIso_higherBaseChangeMapAb_of_smoothLimit` for that system, with smooth
base change [Stacks, Tag 0EYU]. -/
theorem isIso_higherBaseChangeMapAb_of_isPullback_strictHenselizationToBase
    (B : BigEtaleSite.{u}) {X : Scheme.{u}} (hS : B.Contains X) (s : GeometricPoint X)
    {S S' : Scheme.{u}} (t : S ⟶ X) (gX : S' ⟶ strictHenselization B X hS s) (g : S' ⟶ S)
    (sq₀ : IsPullback gX g (strictHenselizationToBase B X hS s) t)
    {T T' : Scheme.{u}} (f : T ⟶ S) [QuasiCompact f] [QuasiSeparated f] (f' : T' ⟶ S')
    (g' : T' ⟶ T) (sq : IsPullback f' g' g f) (q : ℕ) (G : Sheaf (smallEtaleTopology T) Ab.{u + 1})
    (hG : HasTorsionOrdersInvertibleOn S G) :
    IsIso ((higherBaseChangeMapAb g f f' g' sq.w q).app G) := by
  obtain ⟨α, _, _, ⟨a₀⟩, Gα, _⟩ := exists_directed_nbhd B X hS s
  let N := nbhdSystem B X hS s Gα a₀
  let E : (nbhdIndex a₀)ᵒᵖ ⥤ Scheme.{u} := N ⋙ Scheme.Etale.forget X ⋙ Over.forget X
  let c := nbhdCone B X hS s Gα a₀
  have : IsConnected (nbhdIndex a₀)ᵒᵖ := IsCofiltered.isConnected _
  let pE : E ⟶ (Functor.const (nbhdIndex a₀)ᵒᵖ).obj X :=
    { app := fun i => (N.obj i).hom
      naturality := fun i i' a => by
        change (N.map a).left ≫ (N.obj i').hom = (N.obj i).hom ≫ 𝟙 X
        simp }
  have : ∀ i, Etale (pE.app i) := fun i => (N.obj i).prop
  have hcE : ∀ i, c.π.app i ≫ pE.app i = strictHenselizationToBase B X hS s :=
    nbhdCone_π_comp_hom B X hS s Gα a₀
  -- the base changed system `V_i ×_X S` over `S`, with limit `S'`
  let D := baseChangeDiagram E pE t
  have hw : ∀ i, (gX ≫ c.π.app i) ≫ pE.app i = g ≫ t := fun i => by
    rw [Category.assoc, hcE i, sq₀.w]
  have hcD : IsLimit (Cone.mk S' (baseChangeProjection E pE t c.π gX g hw)) :=
    isLimit_of_isPullback_stages (isPullback_baseChangeStage E pE t) sq₀ hcE
      (baseChangeProjection_comp_structureMap E pE t c.π gX g hw)
      (baseChangeProjection_comp_horizontal E pE t c.π gX g hw) (nbhdConeIsLimit B X hS s Gα a₀)
  have hsm : ∀ i, Smooth ((baseChangeStructureMap E pE t).app i) := fun i =>
    inferInstanceAs (Smooth (pullback.snd (pE.app i) t))
  have haff : ∀ ⦃i i' : (nbhdIndex a₀)ᵒᵖ⦄ (a : i ⟶ i'), IsAffineHom (D.map a) := fun _ _ a =>
    have : IsAffineHom (E.map a) := inferInstanceAs (IsAffineHom (N.map a).left)
    isAffineHom_baseChangeDiagram_map E pE t a
  exact isIso_higherBaseChangeMapAb_of_smoothLimit
    (fun _ _ _ _ f₀ g₀ h₀ e₀ sq₁ hf₀ hg₀ hg₀' q₀ ℱ hℱ => by
      have := hf₀
      have := hg₀
      have := hg₀'
      exact SmoothBaseChange.isIso_higherBaseChangeMapAb_app_of_smooth f₀ h₀ e₀ g₀ sq₁ ℱ
        (fun t₀ a => hℱ.exists_nsmul_eq_zero_smallEtaleStalkAb t₀ a) q₀)
    D (baseChangeStructureMap E pE t) hsm haff _ hcD g
    (baseChangeProjection_comp_structureMap E pE t c.π gX g hw) f f' g' sq q G hG

namespace OpenImmersionProductSquare

variable {K : Type u} [Field K] {X U Y : Scheme.{u}}
  (sX : X ⟶ Spec (.of K)) (sU : U ⟶ Spec (.of K)) (sY : Y ⟶ Spec (.of K))
  (j : U ⟶ X) (hj : j ≫ sX = sU)

/-- The projection `h : Y ×_K U ⟶ Y ×_K X` of a quasi-compact quasi-separated `j` is again
quasi-compact and quasi-separated. -/
private theorem quasiCompact_quasiSeparated_h [QuasiCompact j] [QuasiSeparated j] :
    QuasiCompact (h sX sU sY j hj) ∧ QuasiSeparated (h sX sU sY j hj) :=
  ⟨MorphismProperty.of_isPullback (isPullback sX sU sY j hj).flip ‹_›,
    MorphismProperty.of_isPullback (isPullback sX sU sY j hj).flip ‹_›⟩

/-- A sheaf map is invertible on the stalk at `z` if its inverse image along `f` is invertible on
the stalk at a lift `z'` of `z`. -/
private theorem isIso_stalkAb_map_of_isIso_stalkAb_map_pullbackAb {S T : Scheme.{u}} (f : T ⟶ S)
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (z' : Spec (.of Ω) ⟶ T) (z : Spec (.of Ω) ⟶ S)
    (hz : z' ≫ f = z) {A B : Sheaf (smallEtaleTopology S) Ab.{u + 1}} (φ : A ⟶ B)
    (H : IsIso ((smallEtaleStalkAb z').map ((smallEtalePullbackAb f).map φ))) :
    IsIso ((smallEtaleStalkAb z).map φ) := by
  subst hz
  exact (NatIso.isIso_map_iff (smallEtalePullbackStalkAbIso f z') φ).1 H

/-! ### Restriction along a morphism to `X` with invertible auxiliary base change maps -/

section Right

variable {X' U' : Scheme.{u}} (a : X' ⟶ X) (j' : U' ⟶ X') (c : U' ⟶ U)
  (hU : IsPullback j' c a j)

/-- **Restriction along a morphism `a : X' ⟶ X`.** Let `U' = X' ×_X U`, with projections
`j' : U' ⟶ X'` and `c : U' ⟶ U`. If the base change map of the square of `a` and `j` is
invertible at `𝓕`, and that of the square of `id_Y × a` and `h` is invertible at `p⁻¹ 𝓕`, then,
after any functor `Φ`, the inverse image along `id_Y × a : Y ×_K X' ⟶ Y ×_K X` of the base change
map `q⁻¹ R^i j_* 𝓕 ⟶ R^i h_* p⁻¹ 𝓕` is invertible exactly when the base change map of the square
of `j'` and `Y` is invertible at `c⁻¹ 𝓕`. This is the pasting law on the rectangle
`Y ×_K U' ⟶ U'` over `X`, pasted in two ways. -/
theorem isIso_map_higherBaseChangeMapAb_iff_of_isIso_restriction_right (i : ℕ)
    (𝓕 : Sheaf (smallEtaleTopology U) Ab.{u + 1})
    (hlow : IsIso ((higherBaseChangeMapAb a j j' c hU.w i).app 𝓕))
    (hup : IsIso ((higherBaseChangeMapAb (rightMap sY sX a) (h sX sU sY j hj)
      (h (a ≫ sX) (c ≫ sU) sY j' (comp_comp_eq sX sU j hj a j' c hU)) (rightMap sY sU c)
      (isPullback_h_rightMap sX sU sY j hj a j' c hU).w i).app
        ((smallEtalePullbackAb (p sU sY)).obj 𝓕)))
    {C : Type*} [Category* C]
    (Φ : Sheaf (smallEtaleTopology (pullback sY (a ≫ sX))) Ab.{u + 1} ⥤ C) :
    IsIso (Φ.map ((smallEtalePullbackAb (rightMap sY sX a)).map
        ((higherBaseChangeMapAb (q sX sY) j (h sX sU sY j hj) (p sU sY)
          (h_comp_q sX sU sY j hj) i).app 𝓕))) ↔
      IsIso (Φ.map ((higherBaseChangeMapAb (q (a ≫ sX) sY) j'
        (h (a ≫ sX) (c ≫ sU) sY j' (comp_comp_eq sX sU j hj a j' c hU))
        (p (c ≫ sU) sY) (h_comp_q (a ≫ sX) (c ≫ sU) sY j'
          (comp_comp_eq sX sU j hj a j' c hU)) i).app ((smallEtalePullbackAb c).obj 𝓕))) := by
  have hj' := comp_comp_eq sX sU j hj a j' c hU
  have hsq := isPullback_h_rightMap sX sU sY j hj a j' c hU
  rw [← isIso_map_higherBaseChangeMapAb_paste_iff_of_isIso_second j (h sX sU sY j hj)
    (h (a ≫ sX) (c ≫ sU) sY j' hj') (q sX sY) (rightMap sY sX a) (p sU sY) (rightMap sY sU c)
    (h_comp_q sX sU sY j hj) hsq.w i 𝓕 Φ hup,
    ← isIso_map_higherBaseChangeMapAb_paste_iff_of_isIso_first j j'
    (h (a ≫ sX) (c ≫ sU) sY j' hj') a (q (a ≫ sX) sY) c (p (c ≫ sU) sY) hU.w
    (h_comp_q (a ≫ sX) (c ≫ sU) sY j' hj') i 𝓕 Φ inferInstance]
  exact isIso_map_higherBaseChangeMapAb_app_congr j _ (by simp) (by simp) _ _ i 𝓕 Φ

end Right

/-! ### Restriction along a morphism to `Y` with an invertible auxiliary base change map -/

section Left

variable {Y' : Scheme.{u}} (b : Y' ⟶ Y)

/-- **Restriction along a morphism `b : Y' ⟶ Y`.** If the base change map of the square of
`b × id_X` and `h` is invertible at `p⁻¹ 𝓕`, then, after any functor `Φ`, the inverse image along
`b × id_X : Y' ×_K X ⟶ Y ×_K X` of the base change map `q⁻¹ R^i j_* 𝓕 ⟶ R^i h_* p⁻¹ 𝓕` is
invertible exactly when the base change map of the square of `j` and `Y'` is. -/
theorem isIso_map_higherBaseChangeMapAb_iff_of_isIso_restriction_left (i : ℕ)
    (𝓕 : Sheaf (smallEtaleTopology U) Ab.{u + 1})
    (hup : IsIso ((higherBaseChangeMapAb (leftMap sY b X sX) (h sX sU sY j hj)
      (h sX sU (b ≫ sY) j hj) (leftMap sY b U sU) (isPullback_h_leftMap sX sU sY j hj b).w i).app
        ((smallEtalePullbackAb (p sU sY)).obj 𝓕)))
    {C : Type*} [Category* C]
    (Φ : Sheaf (smallEtaleTopology (pullback (b ≫ sY) sX)) Ab.{u + 1} ⥤ C) :
    IsIso (Φ.map ((smallEtalePullbackAb (leftMap sY b X sX)).map
        ((higherBaseChangeMapAb (q sX sY) j (h sX sU sY j hj) (p sU sY)
          (h_comp_q sX sU sY j hj) i).app 𝓕))) ↔
      IsIso (Φ.map ((higherBaseChangeMapAb (q sX (b ≫ sY)) j (h sX sU (b ≫ sY) j hj)
        (p sU (b ≫ sY)) (h_comp_q sX sU (b ≫ sY) j hj) i).app 𝓕)) := by
  rw [← isIso_map_higherBaseChangeMapAb_paste_iff_of_isIso_second j (h sX sU sY j hj)
    (h sX sU (b ≫ sY) j hj) (q sX sY) (leftMap sY b X sX) (p sU sY) (leftMap sY b U sU)
    (h_comp_q sX sU sY j hj) (isPullback_h_leftMap sX sU sY j hj b).w i 𝓕 Φ hup]
  exact isIso_map_higherBaseChangeMapAb_app_congr j _ (by simp) (by simp) _ _ i 𝓕 Φ

end Left

/-! ### The stalks at a geometric point -/

/-- **The stalk at `z̄` from the square over the strict henselization of `X`** ([Stacks,
Tag 0F1H], the case `z ↦ x`). Let `j` be quasi-compact and quasi-separated, `𝓕` annihilated by an
integer `n` invertible in `K`, `z̄` a geometric point of `Y ×_K X`, `x' : X' ⟶ X` the strict
henselization of `X` at the image `s̄` of `z̄`, and `U' = X' ×_X U` (any cartesian square `j'`,
`c`). If the base change map of the square of `j' : U' ⟶ X'` and `Y` is invertible at `c⁻¹ 𝓕`,
then the stalk at `z̄` of `q⁻¹ R^i j_* 𝓕 ⟶ R^i h_* p⁻¹ 𝓕` is invertible.

The point `z̄` lifts to `Y ×_K X'` through the canonical lift of `s̄` to `X'`. The base change
maps of the squares of `x'` and `j`, and of `id_Y × x'` and `h`, are invertible by
[Stacks, Tag 0F09] (`isIso_higherBaseChangeMapAb_of_isPullback_strictHenselizationToBase`), so
the stalk at the lift of the inverse image of the base change map is that of the base change map
of the square over `X'`. -/
theorem isIso_stalk_higherBaseChangeMapAb_of_strictHenselization_right [QuasiCompact j]
    [QuasiSeparated j] (B : BigEtaleSite.{u}) (hS : B.Contains X) (i : ℕ) {n : ℤ}
    (hn : IsUnit (n : K)) (𝓕 : Sheaf (smallEtaleTopology U) Ab.{u + 1})
    (h𝓕 : ∀ (V : U.Etale) (x : 𝓕.obj.obj (op V)), n • x = 0)
    (z : GeometricPoint (pullback sY sX)) {U' : Scheme.{u}}
    (j' : U' ⟶ strictHenselization B X hS (z.map (q sX sY))) (c : U' ⟶ U)
    (hU : IsPullback j' c (strictHenselizationToBase B X hS (z.map (q sX sY))) j)
    (H : IsIso ((higherBaseChangeMapAb
        (q (strictHenselizationToBase B X hS (z.map (q sX sY)) ≫ sX) sY) j'
        (h (strictHenselizationToBase B X hS (z.map (q sX sY)) ≫ sX) (c ≫ sU) sY j'
          (comp_comp_eq sX sU j hj _ j' c hU))
        (p (c ≫ sU) sY) (h_comp_q (strictHenselizationToBase B X hS (z.map (q sX sY)) ≫ sX)
          (c ≫ sU) sY j' (comp_comp_eq sX sU j hj _ j' c hU)) i).app
        ((smallEtalePullbackAb c).obj 𝓕))) :
    IsIso ((smallEtaleStalkAb z.hom).map ((higherBaseChangeMapAb (q sX sY) j
      (h sX sU sY j hj) (p sU sY) (h_comp_q sX sU sY j hj) i).app 𝓕)) := by
  set x' := strictHenselizationToBase B X hS (z.map (q sX sY))
  obtain ⟨_, _⟩ := quasiCompact_quasiSeparated_h sX sU sY j hj
  -- the two auxiliary base change maps, by [Stacks, Tag 0F09]
  have hlow : IsIso ((higherBaseChangeMapAb x' j j' c hU.w i).app 𝓕) :=
    isIso_higherBaseChangeMapAb_of_isPullback_strictHenselizationToBase B hS (z.map (q sX sY))
      (𝟙 X) (𝟙 _) x' (IsPullback.id_horiz x') j j' c hU i 𝓕
      (hasTorsionOrdersInvertibleOn_of_zsmul_eq_zero sX hn 𝓕 h𝓕)
  have hup := isIso_higherBaseChangeMapAb_of_isPullback_strictHenselizationToBase B hS
    (z.map (q sX sY)) (q sX sY) (pullback.snd sY (x' ≫ sX)) (rightMap sY sX x')
    (isPullback_rightMap sY sX x')
    (h sX sU sY j hj) (h (x' ≫ sX) (c ≫ sU) sY j' (comp_comp_eq sX sU j hj x' j' c hU))
    (rightMap sY sU c) (isPullback_h_rightMap sX sU sY j hj x' j' c hU) i
    ((smallEtalePullbackAb (p sU sY)).obj 𝓕)
    (hasTorsionOrdersInvertibleOn_of_zsmul_eq_zero (q sX sY ≫ sX) hn _
      (SmoothBaseChange.zsmul_pullbackAb_eq_zero (p sU sY) 𝓕 n h𝓕))
  -- the lift of `z̄` to `Y ×_K X'`
  let z' : Spec (.of z.residueField) ⟶ pullback sY (x' ≫ sX) :=
    pullback.lift (z.hom ≫ pullback.fst sY sX)
      (geometricPointToStrictHenselization B X hS (z.map (q sX sY))) (by
        calc (z.hom ≫ pullback.fst sY sX) ≫ sY = (z.map (q sX sY)).hom ≫ sX := by
              rw [GeometricPoint.map_hom, Category.assoc, Category.assoc, pullback.condition]
          _ = _ := by
              rw [← geometricPointToStrictHenselization_comp B X hS (z.map (q sX sY)),
                Category.assoc])
  have hz : z' ≫ rightMap sY sX x' = z.hom := by
    refine pullback.hom_ext ?_ ?_
    · simp only [Category.assoc, rightMap, pullback.map, pullback.lift_fst, Category.comp_id, z']
    · simp only [Category.assoc, rightMap, pullback.map, pullback.lift_snd, z',
        pullback.lift_snd_assoc]
      exact geometricPointToStrictHenselization_comp B X hS (z.map (q sX sY))
  exact isIso_stalkAb_map_of_isIso_stalkAb_map_pullbackAb (rightMap sY sX x') z' z.hom hz
    ((higherBaseChangeMapAb (q sX sY) j (h sX sU sY j hj) (p sU sY)
      (h_comp_q sX sU sY j hj) i).app 𝓕)
    ((isIso_map_higherBaseChangeMapAb_iff_of_isIso_restriction_right sX sU sY j hj x'
      j' c hU i 𝓕 hlow hup (smallEtaleStalkAb z')).2 (Functor.map_isIso _ _))

/-- **The stalk at `z̄` from the square of the strict henselization of `Y`** ([Stacks,
Tag 0F1H], the case `z ↦ y`). Let `j` be quasi-compact and quasi-separated, `𝓕` annihilated by an
integer `n` invertible in `K`, `z̄` a geometric point of `Y ×_K X` and `b : Y' ⟶ Y` the strict
henselization of `Y` at the image `ȳ` of `z̄`. If the base change map of the square of `j` and
`Y'` is invertible at `𝓕`, then the stalk at `z̄` of `q⁻¹ R^i j_* 𝓕 ⟶ R^i h_* p⁻¹ 𝓕` is
invertible: `z̄` lifts to `Y' ×_K X`, and the base change map of the square of `b × id_X` and `h`
is invertible by [Stacks, Tag 0F09]. -/
theorem isIso_stalk_higherBaseChangeMapAb_of_strictHenselization_left [QuasiCompact j]
    [QuasiSeparated j] (B : BigEtaleSite.{u}) (hS : B.Contains Y) (i : ℕ) {n : ℤ}
    (hn : IsUnit (n : K)) (𝓕 : Sheaf (smallEtaleTopology U) Ab.{u + 1})
    (h𝓕 : ∀ (V : U.Etale) (x : 𝓕.obj.obj (op V)), n • x = 0)
    (z : GeometricPoint (pullback sY sX))
    (H : IsIso ((higherBaseChangeMapAb
        (q sX (strictHenselizationToBase B Y hS (z.map (pullback.fst sY sX)) ≫ sY)) j
        (h sX sU (strictHenselizationToBase B Y hS (z.map (pullback.fst sY sX)) ≫ sY) j hj)
        (p sU (strictHenselizationToBase B Y hS (z.map (pullback.fst sY sX)) ≫ sY))
        (h_comp_q sX sU (strictHenselizationToBase B Y hS (z.map (pullback.fst sY sX)) ≫ sY)
          j hj) i).app 𝓕)) :
    IsIso ((smallEtaleStalkAb z.hom).map ((higherBaseChangeMapAb (q sX sY) j
      (h sX sU sY j hj) (p sU sY) (h_comp_q sX sU sY j hj) i).app 𝓕)) := by
  set b := strictHenselizationToBase B Y hS (z.map (pullback.fst sY sX))
  obtain ⟨_, _⟩ := quasiCompact_quasiSeparated_h sX sU sY j hj
  have hup := isIso_higherBaseChangeMapAb_of_isPullback_strictHenselizationToBase B hS
    (z.map (pullback.fst sY sX)) (pullback.fst sY sX) (pullback.fst (b ≫ sY) sX) (leftMap sY b X sX)
    (isPullback_leftMap sY b X sX) (h sX sU sY j hj) (h sX sU (b ≫ sY) j hj)
    (leftMap sY b U sU) (isPullback_h_leftMap sX sU sY j hj b) i
    ((smallEtalePullbackAb (p sU sY)).obj 𝓕)
    (hasTorsionOrdersInvertibleOn_of_zsmul_eq_zero (pullback.fst sY sX ≫ sY) hn _
      (SmoothBaseChange.zsmul_pullbackAb_eq_zero (p sU sY) 𝓕 n h𝓕))
  -- the lift of `z̄` to `Y' ×_K X`
  let z' : Spec (.of z.residueField) ⟶ pullback (b ≫ sY) sX :=
    pullback.lift (geometricPointToStrictHenselization B Y hS (z.map (pullback.fst sY sX)))
      (z.hom ≫ pullback.snd sY sX) (by
        calc _ = (z.map (pullback.fst sY sX)).hom ≫ sY := by
              rw [← geometricPointToStrictHenselization_comp B Y hS (z.map (pullback.fst sY sX)),
                Category.assoc]
          _ = (z.hom ≫ pullback.snd sY sX) ≫ sX := by
              rw [GeometricPoint.map_hom, Category.assoc, Category.assoc, pullback.condition])
  have hz : z' ≫ leftMap sY b X sX = z.hom := by
    refine pullback.hom_ext ?_ ?_
    · simp only [Category.assoc, leftMap, pullback.map, pullback.lift_fst, z',
        pullback.lift_fst_assoc]
      exact geometricPointToStrictHenselization_comp B Y hS (z.map (pullback.fst sY sX))
    · simp only [Category.assoc, leftMap, pullback.map, pullback.lift_snd, Category.comp_id, z']
  exact isIso_stalkAb_map_of_isIso_stalkAb_map_pullbackAb (leftMap sY b X sX) z' z.hom hz
    ((higherBaseChangeMapAb (q sX sY) j (h sX sU sY j hj) (p sU sY)
      (h_comp_q sX sU sY j hj) i).app 𝓕)
    ((isIso_map_higherBaseChangeMapAb_iff_of_isIso_restriction_left sX sU sY j hj b
      i 𝓕 hup (smallEtaleStalkAb z')).2 (Functor.map_isIso _ _))

end OpenImmersionProductSquare

end Stacks.EtaleCohomology

end
