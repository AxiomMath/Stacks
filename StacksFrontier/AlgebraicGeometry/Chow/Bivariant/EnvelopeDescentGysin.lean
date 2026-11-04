module

public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.EnvelopeDescentLift
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.GysinCommuting
public import StacksFrontier.AlgebraicGeometry.Chow.Gysin42.ProperPushforwardGysinSystem

/-!
# The Gysin condition of the descended cap operation

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project, let `f : X ⟶ Y` be a
morphism of schemes locally of finite type over `S`, let `g : Y' ⟶ Y` be an envelope and let
`c' ∈ A^p(X' ⟶ Y')` be a bivariant class whose two restrictions to
`A^p(X' ×_X X' ⟶ Y' ×_Y Y')` agree. This file proves condition (3) of Stacks 0B76 for the
descended cap operation `Stacks.Chow.envelopeDescentCap`: it commutes with the Gysin map of the
zero scheme `D` of a section `s` of an invertible module on a test scheme `T`.

## Main results

* `Stacks.Chow.envelopeDescentCap_gysin_naturality` — the Gysin condition, for a Gysin system
  natural under proper pushforward (Stacks 02TA) and under the comparison of iterated pullbacks.

## Implementation notes

Lift `β` to `β'` on `T' = Y' ×_Y T`. By Stacks 02TA for the envelope `T' ⟶ T`, the Gysin map of
`β` is the pushforward of the Gysin map of `β'` along the proper morphism `Z(s|_{T'}) ⟶ D` of
Remark 0B6Y, so it is lifted by that class, and the descended cap of it is read off with
`Stacks.Chow.envelopeDescentCap_envelopeLiftPush`. On the other side, Stacks 02TA for
`h : X' ×_{Y'} T' ⟶ X ×_Y T` moves the Gysin map past `h_*`, and the Gysin condition of `c'`
at `T' ⟶ Y'` finishes the computation; the zero schemes met on the way are identified by
Stacks 0B6Y (`Stacks.Chow.bivariantDivisorBaseChangeIso`,
`Stacks.Divisors.zeroScheme_pullback_comp_eq`) and the identity of morphisms they have to satisfy
is checked after composing with the closed immersion of the zero scheme.

## References

* [Stacks Project, Tag 0GUC](https://stacks.math.columbia.edu/tag/0GUC)
* [Stacks Project, Tag 0B76](https://stacks.math.columbia.edu/tag/0B76)
* [Stacks Project, Tag 02TA](https://stacks.math.columbia.edu/tag/02TA)
* [Stacks Project, Tag 0B6Y](https://stacks.math.columbia.edu/tag/0B6Y)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

/-- The formal core of the Gysin axiom of a descended class: a chain of pushforwards along a
proper morphism and two isomorphisms, compared with a proper pushforward `jE` through a commuting
identity of morphisms. -/
theorem chowPush_assemble (C : ChowSituation.{u}) {P₀ PB PQ PA PE : Scheme.{u}}
    {s₀ : P₀ ⟶ C.S} [LocallyOfFiniteType s₀] {sB : PB ⟶ C.S} [LocallyOfFiniteType sB]
    {sQ : PQ ⟶ C.S} [LocallyOfFiniteType sQ] {sA : PA ⟶ C.S} [LocallyOfFiniteType sA]
    {sE : PE ⟶ C.S} [LocallyOfFiniteType sE]
    (e₁ : P₀ ⟶ PB) [IsProper e₁] (φB : PB ⟶ PQ) [IsIso φB] (φA' : PA ⟶ PQ) [IsIso φA']
    (φA : PQ ⟶ PA) [IsIso φA] (jE : PA ⟶ PE) [IsProper jE] (w : P₀ ⟶ PE) [IsProper w]
    (he₁ : e₁ ≫ sB = s₀) (hφB : φB ≫ sQ = sB) (hφA' : φA' ≫ sQ = sA) (hφA : φA ≫ sA = sQ)
    (hjE : jE ≫ sE = sA) (hw : w ≫ sE = s₀) (hwe : w = e₁ ≫ φB ≫ φA ≫ jE) {m : ℤ}
    (z : chowGroup C s₀ m) (gB : chowGroup C sB m) (gQ : chowGroup C sQ m)
    (gA : chowGroup C sA m)
    (hc : chowPushforwardOfIso C sQ sA φA hφA m (chowPushforwardOfIso C sA sQ φA' hφA' m gA) =
      gA)
    (hA : chowPushforwardOfIso C sA sQ φA' hφA' m gA = gQ)
    (hB : chowPushforwardOfIso C sB sQ φB hφB m gB = gQ)
    (hG : chowPush C s₀ sB e₁ he₁ m z = gB) :
    chowPush C s₀ sE w hw m z = chowPush C sA sE jE hjE m gA := by
  have hgA : gA = chowPush C s₀ sA (e₁ ≫ φB ≫ φA) (by simp [hφA, hφB, he₁]) m z := by
    rw [← hc, hA, ← hB, ← hG]
    exact chowPushforwardOfIso_chowPushforwardOfIso_chowPush C _ _ _ _ e₁ φB φA he₁ hφB hφA _
      m z
  rw [hgA, chowPush_comp C _ _ _ (e₁ ≫ φB ≫ φA) jE w (by rw [hwe]; simp)]

section Gysin

variable (C : ChowSituation.{u}) (G : GysinSystem C) {X Y Y' : Scheme.{u}}
  (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (sY : Y ⟶ C.S) [LocallyOfFiniteType sY]
  (f : X ⟶ Y) [LocallyOfFiniteType f] (hf : f ≫ sY = sX) (g : Y' ⟶ Y) [IsProper g] (p : ℤ)
  (c' : BivariantClass C G (pullback.fst f g ≫ sX) (g ≫ sY) (pullback.snd f g)
    (pullbackSnd_comp_structureMorphism_eq C sX sY f hf g) p)
  (hgys : G.IsNaturalUnderBaseChangeIso)
  (hres : envelopeDescentRes₁ C G sX sY f hf g p hgys c' =
    envelopeDescentRes₂ C G sX sY f hf g p hgys c')
  (hgE : IsEnvelope g)

/-- **Stacks 0B76 (3) for the descended cap operation**, for a Gysin system natural under proper
pushforward (Stacks 02TA) and under the comparison of iterated pullbacks. -/
theorem envelopeDescentCap_gysin_naturality (hprop : G.IsNaturalUnderProperPushforward)
    (hcomp : G.IsNaturalUnderPullbackCompPushforward) {T : Scheme.{u}} (t : T ⟶ Y)
    [LocallyOfFiniteType t] (L : T.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible T.sheaf.obj T.ringCatSheaf.property L]
    [AlgebraicGeometry.SheafOfModules.IsInvertible (pullback f t).sheaf.obj
      (pullback f t).ringCatSheaf.property
      ((Scheme.Modules.pullback (pullback.snd f t)).obj L)]
    (s : Γ(L, ⊤)) (k : ℤ) :
    let D := Stacks.Divisors.zeroScheme T L s
    let L' := (Scheme.Modules.pullback (pullback.snd f t)).obj L
    let s' := AlgebraicGeometry.pullbackGlobalSections (pullback.snd f t) L s
    let E := Stacks.Divisors.zeroScheme (pullback f t) L' s'
    ∀ (e : pullback f (D.subschemeι ≫ t) ≅ E.subscheme)
      (_he : e.hom ≫ E.subschemeι = bivariantBaseChangeMap f t D.subschemeι)
      (hbase : e.hom ≫ (E.subschemeι ≫ pullback.fst f t ≫ sX) =
        pullback.fst f (D.subschemeι ≫ t) ≫ sX)
      (hfac : ProperPushforwardFactorsThroughRationalEquivalence C
        (pullback.fst f (D.subschemeι ≫ t) ≫ sX) (E.subschemeι ≫ pullback.fst f t ≫ sX)
        e.hom hbase (k - p))
      (α : chowGroup C (t ≫ sY) (k + 1)),
      properChowPushforward C (pullback.fst f (D.subschemeι ≫ t) ≫ sX)
          (E.subschemeι ≫ pullback.fst f t ≫ sX) e.hom hbase (k - p) hfac
          (envelopeDescentCap C G sX sY f hf g p c' hgys hres hgE (D.subschemeι ≫ t) k
            (G.onChow (t ≫ sY) L s k α)) =
        G.onChow (pullback.fst f t ≫ sX) L' s' (k - p)
          (Eq.mp (congrArg (chowGroup C (pullback.fst f t ≫ sX))
            (by omega : (k + 1) - p = (k - p) + 1))
            (envelopeDescentCap C G sX sY f hf g p c' hgys hres hgE t (k + 1) α)) := by
  intro D L' s' E e he hbase hfac α
  obtain ⟨β', rfl⟩ := exists_envelopeLiftPush_eq C sY g hgE t (k + 1) α
  set g₁ := pullback.snd g t with hg₁
  set t₁ := pullback.fst g t with ht₁
  set L₁ := (Scheme.Modules.pullback g₁).obj L with hL₁
  set s₁ := AlgebraicGeometry.pullbackGlobalSections g₁ L s with hs₁
  set D₁ := Stacks.Divisors.zeroScheme (pullback g t) L₁ s₁ with hD₁
  set j₂ := zeroSchemePullbackHom g₁ L s with hj₂def
  have hj₂ : j₂ ≫ D.subschemeι = D₁.subschemeι ≫ g₁ := zeroSchemePullbackHom_subschemeι g₁ L s
  have hm₀ : (D₁.subschemeι ≫ t₁) ≫ g = j₂ ≫ (D.subschemeι ≫ t) := by
    rw [Category.assoc, pullback.condition, ← Category.assoc, ← hj₂, Category.assoc]
  set H := envelopeDescentMap f g t g₁ t₁ pullback.condition with hH
  set H₂ := envelopeDescentMap f g (D.subschemeι ≫ t) j₂ (D₁.subschemeι ≫ t₁) hm₀ with hH₂
  set snd' := pullback.snd (pullback.snd f g) t₁ with hsnd'
  have hq : H ≫ pullback.snd f t = snd' ≫ g₁ := envelopeDescentMap_snd f g t g₁ t₁ _
  set ZA := pullbackZeroScheme H L' s' with hZAdef
  set ZB := Stacks.Divisors.zeroScheme (pullback (pullback.snd f g) t₁)
    ((Scheme.Modules.pullback snd').obj L₁)
    (AlgebraicGeometry.pullbackGlobalSections snd' L₁ s₁) with hZBdef
  set ZQ := Stacks.Divisors.zeroScheme (pullback (pullback.snd f g) t₁)
    ((Scheme.Modules.pullback (snd' ≫ g₁)).obj L)
    (AlgebraicGeometry.pullbackGlobalSections (snd' ≫ g₁) L s) with hZQdef
  have hZA : ZA = ZQ := Stacks.Divisors.zeroScheme_pullback_comp_eq H (pullback.snd f t)
    (snd' ≫ g₁) hq L s
  have hZB : ZB = ZQ := Stacks.Divisors.zeroScheme_pullback_comp_eq snd' g₁ (snd' ≫ g₁) rfl L s
  set jE := zeroSchemePullbackHom H L' s' with hjE
  set e' := bivariantDivisorBaseChangeIso (pullback.snd f g) t₁ L₁ s₁ with he'def
  have he' : e'.hom ≫ ZB.subschemeι =
      bivariantBaseChangeMap (pullback.snd f g) t₁ D₁.subschemeι :=
    bivariantDivisorBaseChangeIso_hom_subschemeι (pullback.snd f g) t₁ L₁ s₁
  have hι : eqToHom (congrArg Scheme.IdealSheafData.subscheme hZB) ≫
      eqToHom (congrArg Scheme.IdealSheafData.subscheme hZA.symm) ≫ ZA.subschemeι =
        ZB.subschemeι := by
    rw [subschemeι_eqToHom hZA.symm, subschemeι_eqToHom hZB]
  -- the identity of morphisms behind the computation
  have hME : H₂ ≫ e.hom = e'.hom ≫ eqToHom (congrArg Scheme.IdealSheafData.subscheme hZB) ≫
      eqToHom (congrArg Scheme.IdealSheafData.subscheme hZA.symm) ≫ jE := by
    rw [← cancel_mono E.subschemeι]
    simp only [Category.assoc]
    rw [he, zeroSchemePullbackHom_subschemeι, reassoc_of% hι, reassoc_of% he']
    refine pullback.hom_ext ?_ ?_
    · simp [hH₂, hH, bivariantBaseChangeMap]
    · simp only [hH₂, hH, bivariantBaseChangeMap, Category.assoc, envelopeDescentMap_snd,
        pullback.lift_snd]
      rw [envelopeDescentMap_snd_assoc, hj₂, pullbackMap_snd_assoc]
  set sPA := pullback.fst (pullback.snd f g) t₁ ≫ (pullback.fst f g ≫ sX) with hsPA
  have hHs : H ≫ (pullback.fst f t ≫ sX) = sPA :=
    envelopeDescentMap_comp_structureMorphism C sX f g t _ _ _
  have hjE' : jE ≫ E.subschemeι = ZA.subschemeι ≫ H := zeroSchemePullbackHom_subschemeι H L' s'
  -- Stacks 02TA downstairs, for the envelope `Y' ×_Y T ⟶ T`
  have hL1 : G.onChow (t ≫ sY) L s k
      (envelopeLiftPush C sY g t g₁ t₁ pullback.condition (k + 1) β') =
      envelopeLiftPush C sY g (D.subschemeι ≫ t) j₂ (D₁.subschemeι ≫ t₁) hm₀ k
        (G.onChow (t₁ ≫ (g ≫ sY)) L₁ s₁ k β') :=
    hprop (t₁ ≫ (g ≫ sY)) (t ≫ sY) g₁
      (envelopeDescent_comp_structureMorphism C sY g t _ _ pullback.condition) L s k j₂ hj₂
      (properPushforwardFactorsThroughRationalEquivalence C _ _ _ _ _)
      (properPushforwardFactorsThroughRationalEquivalence C _ _ _ _ _) β'
  set z := c'.cap (D₁.subschemeι ≫ t₁) k (G.onChow (t₁ ≫ (g ≫ sY)) L₁ s₁ k β') with hz
  have hH₂s : H₂ ≫ (pullback.fst f (D.subschemeι ≫ t) ≫ sX) =
      pullback.fst (pullback.snd f g) (D₁.subschemeι ≫ t₁) ≫ (pullback.fst f g ≫ sX) :=
    envelopeDescentMap_comp_structureMorphism C sX f g _ _ _ _
  have hLHS : properChowPushforward C (pullback.fst f (D.subschemeι ≫ t) ≫ sX)
      (E.subschemeι ≫ pullback.fst f t ≫ sX) e.hom hbase (k - p) hfac
      (envelopeDescentCap C G sX sY f hf g p c' hgys hres hgE (D.subschemeι ≫ t) k
        (G.onChow (t ≫ sY) L s k
          (envelopeLiftPush C sY g t g₁ t₁ pullback.condition (k + 1) β'))) =
      chowPush C _ (E.subschemeι ≫ pullback.fst f t ≫ sX) (H₂ ≫ e.hom)
        (by rw [Category.assoc, hbase, hH₂s]) (k - p) z := by
    rw [hL1]
    refine (congrArg _ (envelopeDescentCap_envelopeLiftPush C G sX sY f hf g p c' hgys hres hgE
      _ j₂ _ hm₀ k _)).trans ?_
    exact chowPush_comp C _ _ _ H₂ e.hom (H₂ ≫ e.hom) rfl _ _ _ (k - p) z
  rw [hLHS, envelopeDescentCap_envelopeLiftPush, envelopeDescentPush_apply]
  rw [properChowPushforward_cast C _ _ H hHs (by omega : (k + 1) - p = (k - p) + 1) _
    (properPushforwardFactorsThroughRationalEquivalence C _ _ H hHs _)]
  set y := Eq.mp (congrArg (chowGroup C sPA) (by omega : (k + 1) - p = (k - p) + 1))
    (c'.cap t₁ (k + 1) β') with hy
  rw [hprop sPA (pullback.fst f t ≫ sX) H hHs L' s' (k - p) jE hjE'
    (properPushforwardFactorsThroughRationalEquivalence C _ _ H hHs _)
    (properPushforwardFactorsThroughRationalEquivalence C _ _ _ _ _) y]
  -- the Gysin axiom of `c'` at `Y' ×_Y T ⟶ Y'`
  have hbase' : e'.hom ≫ (ZB.subschemeι ≫ sPA) =
      pullback.fst (pullback.snd f g) (D₁.subschemeι ≫ t₁) ≫ (pullback.fst f g ≫ sX) := by
    rw [← Category.assoc, he']
    simp [hsPA, bivariantBaseChangeMap]
  have hG' := c'.gysin_naturality t₁ L₁ s₁ k e' he' hbase'
    (properPushforwardFactorsThroughRationalEquivalence C _ _ _ _ _) β'
  have hA := GysinSystem.onChow_pullbackComp hcomp H (pullback.snd f t) (snd' ≫ g₁) hq sPA L s
    (k - p) y
  have hB := GysinSystem.onChow_pullbackComp hcomp snd' g₁ (snd' ≫ g₁) rfl sPA L s (k - p) y
  have hc := chowPushforwardOfIso_eqToHom_cancel C hZA sPA (k - p)
    (by rw [← Category.assoc, subschemeι_eqToHom hZA])
    (by rw [← Category.assoc, subschemeι_eqToHom hZA.symm])
    (G.onChow sPA ((Scheme.Modules.pullback H).obj L')
      (AlgebraicGeometry.pullbackGlobalSections H L' s') (k - p) y)
  exact chowPush_assemble C e'.hom _ _ _ jE (H₂ ≫ e.hom) hbase' _ _ _ _ _ hME z _ _ _ hc hA hB hG'

end Gysin

end Stacks.Chow

end
