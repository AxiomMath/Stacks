module

public import StacksFrontier.AlgebraicGeometry.Morphisms.EtaleNeighbourhood.BaseChangeFullApproximation
public import StacksFrontier.AlgebraicGeometry.Morphisms.EtaleNeighbourhood.RelativeMapApproximation
public import StacksCore.Tactic.StacksAttribute
import all StacksFrontier.AlgebraicGeometry.Morphisms.EtaleNeighbourhood.RelativeMapApproximation

/-!
# Approximating a map into the completed local ring of a base change

Let `S` be a locally Noetherian scheme with `𝒪_{S, s}` a G-ring, let `X → S`, `Y → T` and
`T → S` be locally of finite type, let `σ : 𝒪_{T, t} → 𝒪^∧_{S, s}` be a local
`𝒪_{S, s}`-algebra map and let `φ : 𝒪_{X, x} → 𝒪^∧_{Y_σ, y_σ}` be a local `𝒪_{S, s}`-algebra
map into the completed local ring of `Y_σ = Y ×_{T, σ} Spec 𝒪^∧_{S, s}`. For every `N ≥ 1`,
`σ` and `φ` are approximated modulo `𝔪 ^ N` by an elementary étale neighbourhood `(V, v)` of
`(S, s)` with `τ : V → T` and an elementary étale neighbourhood `(W, w)` of
`(Y ×_{T, τ} V, (y, v))` with `f : W → X ×_S V` (Stacks Tag 0CAW).

## Main results

* `StacksDraft.ArtinApproximation.exists_relativeMapApproximation`: Stacks Tag 0CAW.

## Implementation notes

The proof is the source's: Tag 0CAU over `Spec 𝒪^∧_{S, s}`, the descent of the resulting pointed
span to a smooth stage of Popescu's presentation of `𝒪^∧_{S, s}`, and Tag 0CAU over `Spec 𝒪_{S, s}`
once more. The identification `𝒪_{Y_σ, y_σ}/𝔪^N ≅ 𝒪_{Y ×_{T, τ} V, (y, v)}/𝔪^N` of clause (5)
is the order-`N` comparison of the two base changes of the stage object. The construction over
the stage lives in `RelativeMapApproximation.lean`, whose private lemmas are imported with
`import all`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry IsLocalRing
open scoped TensorProduct

universe u

namespace StacksDraft.ArtinApproximation

/-- **The approximating diagram of Tag 0CAW from a pointed span over `Spec 𝒪^∧_{S, s}`, with
clause (5)'s identification.** The conclusion of
`StacksDraft.ArtinApproximation.exists_approximationDiagram_over_base_of_span` together with the
ring isomorphism
`θ : 𝒪_{Y_σ, y_σ}/𝔪^N ≅ 𝒪_{Y ×_{T, τ} V, y_τ}/𝔪^N` matching the two maps from `𝒪_{Y, y}` and
the two maps from `𝒪_{S, s}`, through which the congruence on `Usch` becomes the square of
clause (5) in `𝒪_{W, w}/𝔪_w ^ N`. -/
private theorem exists_approximationDiagram_over_base_of_span_truncationEquiv
    {X S Y T B : Scheme.{u}} [IsLocallyNoetherian S] (p : X ⟶ S) (q : Y ⟶ T)
    [LocallyOfFiniteType p] [LocallyOfFiniteType q] [IsLocallyNoetherian T]
    (bS : S ⟶ B) (hTB : T ⟶ B) [LocallyOfFinitePresentation hTB]
    {x : X} {s : S} {y : Y} {t : T} (hx : p x = s)
    (hG : IsGRing (S.presheaf.stalk s)) (N : ℕ) (hN : 1 ≤ N)
    (σ : T.presheaf.stalk t →+*
      AdicCompletion (maximalIdeal (S.presheaf.stalk s)) (S.presheaf.stalk s))
    (hσ : IsLocalHom σ)
    (hβB : relativeBaseChangeMorphism s σ ≫ hTB = specCompletedStalkTo S s ≫ bS)
    (xσ : (pullback p (specCompletedStalkTo S s) : Scheme.{u}))
    (hxσX : pullback.fst p (specCompletedStalkTo S s) xσ = x)
    (hxσZ : pullback.snd p (specCompletedStalkTo S s) xσ = specCompletedStalkPoint S s)
    (yσ : (pullback q (relativeBaseChangeMorphism s σ) : Scheme.{u}))
    (hyσY : pullback.fst q (relativeBaseChangeMorphism s σ) yσ = y)
    (hyσZ : pullback.snd q (relativeBaseChangeMorphism s σ) yσ =
      specCompletedStalkPoint S s)
    (Usch : Scheme.{u}) (u : Usch)
    (fU : Usch ⟶ (pullback p (specCompletedStalkTo S s) : Scheme.{u})) (hfU : fU u = xσ)
    (gU : Usch ⟶ (pullback q (relativeBaseChangeMorphism s σ) : Scheme.{u}))
    (hgUEt : Etale gU) (hgU : gU u = yσ) (hgUres : IsIso (gU.residueFieldMap u))
    (hUBase : gU ≫ pullback.snd q (relativeBaseChangeMorphism s σ) =
      fU ≫ pullback.snd p (specCompletedStalkTo S s))
    (P : X.presheaf.stalk x → Y.presheaf.stalk y → Prop)
    (hUX : (fU ≫ pullback.fst p (specCompletedStalkTo S s)) u = x)
    (hUY : (gU ≫ pullback.fst q (relativeBaseChangeMorphism s σ)) u = y)
    (hUcong : ∀ (α : X.presheaf.stalk x) (b : Y.presheaf.stalk y), P α b →
      (fU ≫ pullback.fst p (specCompletedStalkTo S s)).stalkHomAt hUX α -
          (gU ≫ pullback.fst q (relativeBaseChangeMorphism s σ)).stalkHomAt hUY b ∈
        maximalIdeal (Usch.presheaf.stalk u) ^ N) :
    ∃ (V : EtaleNeighborhood S s) (τV : V.scheme ⟶ T) (hτV : τV V.point = t)
      (yτ : (pullback q τV : Scheme.{u}))
      (hyτY : pullback.fst q τV yτ = y) (hyτV : pullback.snd q τV yτ = V.point)
      (Wsch : Scheme.{u}) (w : Wsch) (pW : Wsch ⟶ X) (hpW : pW w = x)
      (g : Wsch ⟶ pullback q τV)
      (hgPoint : g w = yτ) (_ : Etale g),
      V.IsElementary ∧ τV ≫ hTB = V.toBase ≫ bS ∧
        IsIso (((pullback q τV).residueFieldCongr hgPoint).inv ≫
          g.residueFieldMap w) ∧
        g ≫ pullback.snd q τV ≫ V.toBase = pW ≫ p ∧
        (Etale fU →
          IsIso ((fU ≫ pullback.fst p (specCompletedStalkTo S s)).residueFieldMap u) →
          Etale pW ∧ IsIso (pW.residueFieldMap w)) ∧
        (∀ b : T.presheaf.stalk t,
          V.completionMap (σ b) -
              algebraMap (V.scheme.presheaf.stalk V.point)
                (AdicCompletion (maximalIdeal (V.scheme.presheaf.stalk V.point))
                  (V.scheme.presheaf.stalk V.point)) (τV.stalkHomAt hτV b) ∈
            Ideal.map
              (algebraMap (V.scheme.presheaf.stalk V.point)
                (AdicCompletion (maximalIdeal (V.scheme.presheaf.stalk V.point))
                  (V.scheme.presheaf.stalk V.point)))
              (maximalIdeal (V.scheme.presheaf.stalk V.point) ^ N)) ∧
        (∀ (α : X.presheaf.stalk x) (b : Y.presheaf.stalk y), P α b →
          Ideal.Quotient.mk (maximalIdeal (Wsch.presheaf.stalk w) ^ N)
              (pW.stalkHomAt hpW α) =
            Ideal.Quotient.mk (maximalIdeal (Wsch.presheaf.stalk w) ^ N)
              (g.stalkHomAt hgPoint ((pullback.fst q τV).stalkHomAt hyτY b))) ∧
        (∃ θ : ((pullback q (relativeBaseChangeMorphism s σ)).presheaf.stalk yσ ⧸
              maximalIdeal
                ((pullback q (relativeBaseChangeMorphism s σ)).presheaf.stalk yσ) ^ N) ≃+*
            ((pullback q τV).presheaf.stalk yτ ⧸
              maximalIdeal ((pullback q τV).presheaf.stalk yτ) ^ N),
          (∀ b : Y.presheaf.stalk y,
            θ (Ideal.Quotient.mk (maximalIdeal
                ((pullback q (relativeBaseChangeMorphism s σ)).presheaf.stalk yσ) ^ N)
                ((pullback.fst q (relativeBaseChangeMorphism s σ)).stalkHomAt hyσY b)) =
              Ideal.Quotient.mk (maximalIdeal ((pullback q τV).presheaf.stalk yτ) ^ N)
                ((pullback.fst q τV).stalkHomAt hyτY b)) ∧
          (∀ c : S.presheaf.stalk s,
            θ (Ideal.Quotient.mk (maximalIdeal
                ((pullback q (relativeBaseChangeMorphism s σ)).presheaf.stalk yσ) ^ N)
                ((pullback.snd q (relativeBaseChangeMorphism s σ)).stalkHomAt hyσZ
                  ((specCompletedStalkTo S s).stalkHomAt
                    (specCompletedStalkTo_specCompletedStalkPoint S s) c))) =
              Ideal.Quotient.mk (maximalIdeal ((pullback q τV).presheaf.stalk yτ) ^ N)
                ((pullback.snd q τV).stalkHomAt hyτV (V.stalkHom c))) ∧
          ∀ (α : X.presheaf.stalk x)
              (ξ : (pullback q (relativeBaseChangeMorphism s σ)).presheaf.stalk yσ)
              (z : (pullback q τV).presheaf.stalk yτ),
            (fU ≫ pullback.fst p (specCompletedStalkTo S s)).stalkHomAt hUX α -
                gU.stalkHomAt hgU ξ ∈ maximalIdeal (Usch.presheaf.stalk u) ^ N →
            θ (Ideal.Quotient.mk (maximalIdeal
                ((pullback q (relativeBaseChangeMorphism s σ)).presheaf.stalk yσ) ^ N) ξ) =
              Ideal.Quotient.mk (maximalIdeal ((pullback q τV).presheaf.stalk yτ) ^ N) z →
            Ideal.Quotient.mk (maximalIdeal (Wsch.presheaf.stalk w) ^ N)
                (g.stalkHomAt hgPoint z) =
              Ideal.Quotient.mk (maximalIdeal (Wsch.presheaf.stalk w) ^ N)
                (pW.stalkHomAt hpW α)) ∧
        ∃ (eBase : (specCompletedStalk S s).residueField (specCompletedStalkPoint S s) ≅
            V.scheme.residueField V.point)
          (eFiber : (pullback.snd q (relativeBaseChangeMorphism s σ)).fiber
              (specCompletedStalkPoint S s) ≅
            (pullback.snd q τV).fiber V.point),
          (Spec.map eBase.inv ≫ V.scheme.fromSpecResidueField V.point ≫ V.toBase =
            (specCompletedStalk S s).fromSpecResidueField (specCompletedStalkPoint S s) ≫
              specCompletedStalkTo S s) ∧
          (Spec.map eBase.inv ≫ V.scheme.fromSpecResidueField V.point ≫ τV =
            (specCompletedStalk S s).fromSpecResidueField (specCompletedStalkPoint S s) ≫
              relativeBaseChangeMorphism s σ) ∧
          (eFiber.hom ≫ (pullback.snd q τV).fiberι V.point ≫ pullback.fst q τV =
            (pullback.snd q (relativeBaseChangeMorphism s σ)).fiberι
                (specCompletedStalkPoint S s) ≫
              pullback.fst q (relativeBaseChangeMorphism s σ)) ∧
          (eFiber.hom ≫ (pullback.snd q τV).fiberToSpecResidueField V.point =
            (pullback.snd q (relativeBaseChangeMorphism s σ)).fiberToSpecResidueField
                (specCompletedStalkPoint S s) ≫ Spec.map eBase.inv) ∧
          (eFiber.hom (((pullback.snd q (relativeBaseChangeMorphism s σ)).fiberHomeo
              (specCompletedStalkPoint S s)).symm ⟨yσ, hyσZ⟩) =
            ((pullback.snd q τV).fiberHomeo V.point).symm ⟨yτ, hyτV⟩) := by
  classical
  have := hσ
  have : IsLocalHom (CommRingCat.ofHom σ).hom := inferInstanceAs (IsLocalHom σ)
  have : IsNoetherianRing (S.presheaf.stalk s) := inferInstance
  have hGhat := completion_isGRing (S.presheaf.stalk s) hG
  have : IsNoetherianRing (AdicCompletion (maximalIdeal (S.presheaf.stalk s))
    (S.presheaf.stalk s)) := hGhat.1
  have : IsLocallyNoetherian (specCompletedStalk S s) := inferInstance
  -- descend the pair to a smooth stage of the presentation of `Spec 𝒪^∧_{S, s}`
  obtain ⟨Dst, ρ, hρSm, τ, m, hmρ, hmτ, A, fD, gD, hfD₀, hgD, a, hτρ, hAa, hfa, hfres₀, hgres,
    hga, aσ, haσA, haσZ, Uaff, jUaff, hjUaff, eAff, heAffIso, a₀, hja₀, heAffa₀,
    hAffX, hAffY, hAffZ⟩ :=
    exists_stage_etale_pair_of_pointed_span p q bS hTB hx hG
      (relativeBaseChangeMorphism s σ) hβB xσ hxσX hxσZ yσ hyσZ Usch u fU
      hfU gU hgUEt hgU hgUres hUBase
  have := hρSm
  have : LocallyOfFiniteType ρ := inferInstance
  have hτm : τ (m (specCompletedStalkPoint S s)) = t := by
    show (m ≫ τ) (specCompletedStalkPoint S s) = t
    rw [hmτ]
    exact relativeBaseChangeMorphism_specCompletedStalkPoint s σ
  have hσstage : (Scheme.stalkClosedPointTo m).hom.comp (τ.stalkHomAt hτm) = σ :=
    stalkClosedPointTo_comp_stalkHomAt m τ (CommRingCat.ofHom σ) hmτ hτm
  -- the two routes out of `𝒪_{A, a}`, and the point of the base change of `A` along `m`
  have hgYa : (gD.left ≫ pullback.fst q τ) a = y := by
    show pullback.fst q τ (gD.left a) = y
    rw [hga]
    show (baseChangeCompare q τ m (relativeBaseChangeMorphism s σ) hmτ ≫
      pullback.fst q τ) yσ = y
    rw [baseChangeCompare_fst]
    exact hyσY
  have hAσX : (pullback.fst A.hom m ≫ fD.left ≫ pullback.fst p ρ) aσ = x := by
    show (fD.left ≫ pullback.fst p ρ) (pullback.fst A.hom m aσ) = x
    rw [haσA]
    exact hfa
  have hAσY : (pullback.fst A.hom m ≫ gD.left ≫ pullback.fst q τ) aσ = y := by
    show (gD.left ≫ pullback.fst q τ) (pullback.fst A.hom m aσ) = y
    rw [haσA]
    exact hgYa
  -- the Noetherian local rings in play
  have : IsLocallyNoetherian (pullback q (relativeBaseChangeMorphism s σ)) :=
    LocallyOfFiniteType.isLocallyNoetherian
      (pullback.snd q (relativeBaseChangeMorphism s σ))
  have : IsLocallyNoetherian (pullback p (specCompletedStalkTo S s)) :=
    LocallyOfFiniteType.isLocallyNoetherian (pullback.snd p (specCompletedStalkTo S s))
  have := hgUEt
  have : IsLocallyNoetherian Usch := LocallyOfFiniteType.isLocallyNoetherian gU
  have : IsNoetherianRing
    ((pullback q (relativeBaseChangeMorphism s σ)).presheaf.stalk yσ) := inferInstance
  have : IsNoetherianRing
    ((pullback p (specCompletedStalkTo S s)).presheaf.stalk xσ) := inferInstance
  have : IsNoetherianRing (Usch.presheaf.stalk u) := inferInstance
  -- **Clause (5).** The congruence in `𝒪_{Usch, u}` is a congruence in
  -- `𝒪_{A ×_D Spec 𝒪^∧_{S, s}, aσ}`, `Usch` being that base change near its point.
  have := hjUaff
  have := heAffIso
  have : IsOpenImmersion eAff := inferInstance
  have : IsIso (eAff.stalkMap a₀) := inferInstance
  have : IsIso (((pullback A.hom m).presheaf.stalkCongr
    (.of_eq heAffa₀.symm)).hom) := inferInstance
  have hfbij : Function.Bijective (eAff.stalkHomAt heAffa₀) :=
    ConcreteCategory.bijective_of_isIso
      (((pullback A.hom m).presheaf.stalkCongr (.of_eq heAffa₀.symm)).hom ≫
        eAff.stalkMap a₀)
  -- the stalk maps of `Usch` and of the base change of `A` along `m` agree through `eAff`
  have htrans : ∀ {Z : Scheme.{u}} {z : Z} (f₁ : Usch ⟶ Z) (f₂ : pullback A.hom m ⟶ Z)
      (h₁ : f₁ u = z) (h₂ : f₂ aσ = z), jUaff ≫ f₁ = eAff ≫ f₂ →
      (jUaff.stalkHomAt hja₀).comp (f₁.stalkHomAt h₁) =
        (eAff.stalkHomAt heAffa₀).comp (f₂.stalkHomAt h₂) := by
    intro Z z f₁ f₂ h₁ h₂ hf
    rw [← Scheme.Hom.stalkHomAt_comp jUaff f₁ hja₀ h₁,
      ← Scheme.Hom.stalkHomAt_comp eAff f₂ heAffa₀ h₂]
    exact stalkHomAt_congr hf _ _
  have hXtrans := htrans _ _ hUX hAσX hAffX
  have hYtrans := htrans _ _ hUY hAσY hAffY
  have hle : (maximalIdeal (Usch.presheaf.stalk u) ^ N).map (jUaff.stalkHomAt hja₀) ≤
      maximalIdeal (Uaff.presheaf.stalk a₀) ^ N := by
    rw [Ideal.map_pow]
    exact Ideal.pow_right_mono (IsLocalRing.map_maximalIdeal_le _) N
  -- a congruence mod `𝔪 ^ N` in `Usch` transfers to the base change of `A`
  have hcong : ∀ (c₁ c₂ : Usch.presheaf.stalk u) (d₁ d₂ : (pullback A.hom m).presheaf.stalk aσ),
      jUaff.stalkHomAt hja₀ c₁ = eAff.stalkHomAt heAffa₀ d₁ →
      jUaff.stalkHomAt hja₀ c₂ = eAff.stalkHomAt heAffa₀ d₂ →
      c₁ - c₂ ∈ maximalIdeal (Usch.presheaf.stalk u) ^ N →
      d₁ - d₂ ∈ maximalIdeal ((pullback A.hom m).presheaf.stalk aσ) ^ N := by
    intro c₁ c₂ d₁ d₂ h₁ h₂ hc
    have hfdiff : eAff.stalkHomAt heAffa₀ (d₁ - d₂) ∈
        maximalIdeal (Uaff.presheaf.stalk a₀) ^ N := by
      rw [map_sub, ← h₁, ← h₂, ← map_sub]
      exact hle (Ideal.mem_map_of_mem _ hc)
    rw [← IsLocalRing.map_maximalIdeal_of_surjective (eAff.stalkHomAt heAffa₀)
      hfbij.surjective, ← Ideal.map_pow] at hfdiff
    obtain ⟨η, hη, hfη⟩ := (Ideal.mem_map_iff_of_surjective _ hfbij.surjective).mp hfdiff
    exact hfbij.injective hfη ▸ hη
  have hAcong : ∀ (α : X.presheaf.stalk x) (b : Y.presheaf.stalk y), P α b →
      (pullback.fst A.hom m ≫ fD.left ≫ pullback.fst p ρ).stalkHomAt hAσX α -
          (pullback.fst A.hom m ≫ gD.left ≫ pullback.fst q τ).stalkHomAt hAσY b ∈
        maximalIdeal ((pullback A.hom m).presheaf.stalk aσ) ^ N :=
    fun α b hP => hcong _ _ _ _ (RingHom.congr_fun hXtrans α) (RingHom.congr_fun hYtrans b)
      (hUcong α b hP)
  obtain ⟨V, τV, hτV, yτ, hyτY, hyτV, Wsch, w, pW, hpW, g, hgPoint, hgEt, hVel, hτVB, hresg,
    hover, hXcond, hc3, hc5, hgZθ, hfib⟩ :=
    exists_approximationDiagram_of_stage p q hx hG N hN σ ρ τ bS hTB hτρ m
      hmρ (relativeBaseChangeMorphism s σ) hmτ hτm hσstage A fD gD hgD a hAa hfa
      hgres hgYa yσ hyσY hyσZ hga aσ haσA haσZ hAσX hAσY P hAcong
  obtain ⟨gZ, hgZ, hgZfst, hgZsnd, θ, hθY, hθS, hθsq⟩ := hgZθ
  -- `Usch` and the base change of `A` along `m` have the same leg to `Y_σ`
  have hjgZ : jUaff ≫ gU = eAff ≫ gZ := by
    refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, Category.assoc, hgZfst]
      exact hAffY
    · rw [Category.assoc, Category.assoc, hgZsnd, hUBase]
      exact hAffZ
  have hGZtrans := htrans gU gZ hgU hgZ hjgZ
  refine ⟨V, τV, hτV, yτ, hyτY, hyτV, Wsch, w, pW, hpW, g, hgPoint, hgEt, hVel, hτVB, hresg,
    hover, fun hfe hfr => hXcond (hfD₀ hfe) (hfres₀ hfr), hc3, hc5,
    ⟨θ, hθY, hθS, fun α ξ z hcongU hz =>
      hθsq α ξ z (hcong _ _ _ _ (RingHom.congr_fun hXtrans α) (RingHom.congr_fun hGZtrans ξ)
        hcongU) hz⟩, hfib⟩

/-- **Stacks Project, Tag 0CAW (More on Morphisms, Lemma 37.39.6).** Let `S` be a locally
Noetherian scheme, let `p : X ⟶ S`, `q : Y ⟶ T` and `h : T ⟶ S` be locally of finite type, let
`x ∈ X` lie over `s ∈ S` and `y ∈ Y` over `t ∈ T` with `h t = s`, and assume `𝒪_{S, s}` is a
G-ring. Let `σ : 𝒪_{T, t} → 𝒪^∧_{S, s}` be a local `𝒪_{S, s}`-algebra map, write
`Y_σ = Y ×_{T, σ} Spec 𝒪^∧_{S, s}`, let `y_σ` be a point of `Y_σ` over `y` — the only one, since
such a point lies over the closed point by
`StacksDraft.ArtinApproximation.snd_eq_closedPoint_of_fst_eq` — and let
`φ : 𝒪_{X, x} → 𝒪^∧_{Y_σ, y_σ}` be a local `𝒪_{S, s}`-algebra map.

Then for every `N ≥ 1` there is a commutative diagram
```
X ← X ×_S V ←—f— W —→ Y ×_{T, τ} V → Y
↓               ↓                     ↓
S ←——————————— V ———τ——————————————→ T
```
of schemes over `S` with points `w ∈ W` and `v ∈ V` such that
1. `v ↦ s`, `τ v = t`, `f w = (x, v)` and `w ↦ (y, v)`;
2. `(V, v) → (S, s)` is an elementary étale neighbourhood;
3. the square relating `σ` to `τ^♯_v` commutes modulo `𝔪_v ^ N`;
4. `(W, w) → (Y ×_{T, τ} V, (y, v))` is an elementary étale neighbourhood;
5. the square
```
𝒪_{X, x} —φ→ 𝒪^∧_{Y_σ, y_σ} → 𝒪_{Y_σ, y_σ}/𝔪^N —θ→ 𝒪_{Y ×_{T, τ} V, (y, v)}/𝔪^N
   ‖                                                           ↓
𝒪_{X, x} → 𝒪_{X ×_S V, (x, v)} —f^♯_w→ 𝒪_{W, w} ———————→ 𝒪_{W, w}/𝔪^N
```
commutes, where `θ` is the canonical isomorphism of `Y_σ` with `Y ×_{T, τ} V` over
`𝒪_{V, v}/𝔪_v ^ N = 𝒪_{S, s}/𝔪_s ^ N` that clauses (2) and (3) provide.

The isomorphism `θ` is exhibited, together with the compatibilities which characterise it: it
matches the two maps from `𝒪_{Y, y}` and the two maps from `𝒪_{S, s}`. Only the `𝔪 ^ N`
truncations are identified; the completions `𝒪^∧_{Y_σ, y_σ}` and `𝒪^∧_{Y ×_{T, τ} V, (y, v)}`
need not be isomorphic, as the cusp-versus-node example in the module docstring of
`StacksFrontier/AlgebraicGeometry/Morphisms/EtaleNeighbourhood/FiniteTypeBaseApproximation.lean`
shows. The correspondence of `(y, v)` with `y_σ` on the closed fibres is recorded in addition, as
in Tag 0GDX. -/
@[stacks 0CAW "the source's own hypotheses, with nothing beyond them: `h : T ⟶ S` locally of \
finite type, a G-ring `𝒪_{S, s}`, a local `𝒪_{S, s}`-algebra map `σ : 𝒪_{T, t} → 𝒪^∧_{S, s}`, \
the base change `Y_σ = Y ×_{T, σ} Spec 𝒪^∧_{S, s}`, a point `y_σ` of `Y_σ` over `y` (the \
source's `the` point: lying over `y` forces it over the closed point, by \
`StacksDraft.ArtinApproximation.snd_eq_closedPoint_of_fst_eq`, so no second hypothesis places \
it there) and a local `𝒪_{S, s}`-algebra map `φ : 𝒪_{X, x} → 𝒪^∧_{Y_σ, y_σ}`. Theorem 07QZ is \
discharged, not an input: the `LocalApproximationProperty` hypothesis of Tag 0CAU \
behind both stages is supplied by \
`StacksDraft.ArtinApproximation.localApproximationProperty`, which rests on the \
unconditional Tag 07QZ `Stacks.Smoothing.exists_localEtaleSolution_of_isGRing` and hence on the \
unconditional Popescu Theorem 07GC \
`Stacks.Smoothing.indSmooth_of_isRegularRingMap`. The conclusion is the source's whole diagram: \
clause (1) — `v ↦ s`, `τ(v) = t`, `f(w) = (x, v)` as the two projection identities of `f` with \
`F w = x`, and `w ↦ (y, v)` as `W.map_point` with the point of `Y ×_{T, τ} V` lying over `y` \
and `v`; clause (2); clause (3); clause (4); and clause (5), the commuting square, whose `=` \
between `𝒪_{Y_σ, y_σ}/𝔪^N` and `𝒪_{Y ×_{T, τ} V, (y, v)}/𝔪^N` is exhibited as the ring \
isomorphism `θ` together with the two compatibilities that characterise it as the source's \
canonical identification over `𝒪_{V, v}/𝔪_v ^ N = 𝒪_{S, s}/𝔪_s ^ N`: it matches the two maps \
from `𝒪_{Y, y}` and the two maps from `𝒪_{S, s}`. Only the truncations are identified; the \
completions need not be isomorphic, as the cusp-versus-node example in the module docstring of \
`StacksFrontier/AlgebraicGeometry/Morphisms/EtaleNeighbourhood/FiniteTypeBaseApproximation.lean` \
shows. The route is the source's own: Tag 0CAU over `Spec 𝒪^∧_{S, s}` replaces `φ` by a \
morphism to `X` out of an elementary étale neighbourhood of `(Y_σ, y_σ)`, that pointed span \
descends to a smooth stage of Popescu's presentation of `𝒪^∧_{S, s}`, and Tag 0CAU applied one \
more time to `Spec 𝒪_{T, t}` and `Spec 𝒪_{S, s}` over `Spec 𝒪_{S, s}` replaces the stage by \
`(V, v)`; `θ` is the order-`N` comparison of the two base changes of the stage object, along \
`Spec 𝒪^∧_{S, s} ⟶ D` and along `V ⟶ D`, read through the two étale legs. The identification \
of the closed fibres `(Y_σ)_s ≅ (Y ×_T V)_v` of Tag 0GDX is recorded as well"]
theorem exists_relativeMapApproximation
    {X S Y T : Scheme.{u}} [IsLocallyNoetherian S] (p : X ⟶ S) (q : Y ⟶ T) (h : T ⟶ S)
    [LocallyOfFiniteType p] [LocallyOfFiniteType q] [LocallyOfFiniteType h]
    {x : X} {s : S} {y : Y} {t : T} (hx : p x = s) (hy : q y = t) (hts : h t = s)
    (hG : IsGRing (S.presheaf.stalk s)) (N : ℕ) (hN : 1 ≤ N)
    (σ : T.presheaf.stalk t →+*
      AdicCompletion (maximalIdeal (S.presheaf.stalk s)) (S.presheaf.stalk s))
    (hσ : IsLocalHom σ)
    (hσbase : σ.comp (h.stalkHomAt hts) =
      algebraMap (S.presheaf.stalk s)
        (AdicCompletion (maximalIdeal (S.presheaf.stalk s)) (S.presheaf.stalk s)))
    (yσ : (pullback q (relativeBaseChangeMorphism s σ) : Scheme.{u}))
    (hyσY : pullback.fst q (relativeBaseChangeMorphism s σ) yσ = y)
    (φ : X.presheaf.stalk x →+*
      AdicCompletion
        (maximalIdeal
          ((pullback q (relativeBaseChangeMorphism s σ)).presheaf.stalk yσ))
        ((pullback q (relativeBaseChangeMorphism s σ)).presheaf.stalk yσ))
    (hφ : IsLocalHom φ)
    (hφbase : φ.comp (p.stalkHomAt hx) =
      (algebraMap ((pullback q (relativeBaseChangeMorphism s σ)).presheaf.stalk yσ)
          (AdicCompletion
            (maximalIdeal
              ((pullback q (relativeBaseChangeMorphism s σ)).presheaf.stalk yσ))
            ((pullback q (relativeBaseChangeMorphism s σ)).presheaf.stalk yσ))).comp
        (((pullback.snd q (relativeBaseChangeMorphism s σ)).stalkHomAt
            (snd_eq_closedPoint_of_fst_eq h q hy hts σ hσbase
              (relativeBaseChangeMorphism s σ) rfl yσ hyσY)).comp
          ((specCompletedStalkTo S s).stalkHomAt
            (specCompletedStalkTo_specCompletedStalkPoint S s)))) :
    ∃ (V : EtaleNeighborhood S s) (τ : V.scheme ⟶ T) (hτ : τ V.point = t)
      (yτ : (pullback q τ : Scheme.{u}))
      (hyτY : pullback.fst q τ yτ = y) (hyτV : pullback.snd q τ yτ = V.point)
      (W : EtaleNeighborhood (pullback q τ) yτ) (F : W.scheme ⟶ X) (hF : F W.point = x)
      (f : W.scheme ⟶ pullback p V.toBase),
      V.IsElementary ∧ W.IsElementary ∧ τ ≫ h = V.toBase ∧
        f ≫ pullback.fst p V.toBase = F ∧
        f ≫ pullback.snd p V.toBase = W.toBase ≫ pullback.snd q τ ∧
        F ≫ p = W.toBase ≫ pullback.snd q τ ≫ V.toBase ∧
        (∀ b : T.presheaf.stalk t,
          V.completionMap (σ b) -
              algebraMap (V.scheme.presheaf.stalk V.point)
                (AdicCompletion (maximalIdeal (V.scheme.presheaf.stalk V.point))
                  (V.scheme.presheaf.stalk V.point)) (τ.stalkHomAt hτ b) ∈
            Ideal.map
              (algebraMap (V.scheme.presheaf.stalk V.point)
                (AdicCompletion (maximalIdeal (V.scheme.presheaf.stalk V.point))
                  (V.scheme.presheaf.stalk V.point)))
              (maximalIdeal (V.scheme.presheaf.stalk V.point) ^ N)) ∧
        (∃ θ : ((pullback q (relativeBaseChangeMorphism s σ)).presheaf.stalk yσ ⧸
              maximalIdeal
                ((pullback q (relativeBaseChangeMorphism s σ)).presheaf.stalk yσ) ^ N) ≃+*
            ((pullback q τ).presheaf.stalk yτ ⧸
              maximalIdeal ((pullback q τ).presheaf.stalk yτ) ^ N),
          (∀ b : Y.presheaf.stalk y,
            θ (Ideal.Quotient.mk (maximalIdeal
                ((pullback q (relativeBaseChangeMorphism s σ)).presheaf.stalk yσ) ^ N)
                ((pullback.fst q (relativeBaseChangeMorphism s σ)).stalkHomAt hyσY b)) =
              Ideal.Quotient.mk (maximalIdeal ((pullback q τ).presheaf.stalk yτ) ^ N)
                ((pullback.fst q τ).stalkHomAt hyτY b)) ∧
          (∀ c : S.presheaf.stalk s,
            θ (Ideal.Quotient.mk (maximalIdeal
                ((pullback q (relativeBaseChangeMorphism s σ)).presheaf.stalk yσ) ^ N)
                ((pullback.snd q (relativeBaseChangeMorphism s σ)).stalkHomAt
                  (snd_eq_closedPoint_of_fst_eq h q hy hts σ hσbase
                    (relativeBaseChangeMorphism s σ) rfl yσ hyσY)
                  ((specCompletedStalkTo S s).stalkHomAt
                    (specCompletedStalkTo_specCompletedStalkPoint S s) c))) =
              Ideal.Quotient.mk (maximalIdeal ((pullback q τ).presheaf.stalk yτ) ^ N)
                ((pullback.snd q τ).stalkHomAt hyτV (V.stalkHom c))) ∧
          ∀ (α : X.presheaf.stalk x) (z : (pullback q τ).presheaf.stalk yτ),
            θ (AdicCompletion.evalₐ (maximalIdeal
                ((pullback q (relativeBaseChangeMorphism s σ)).presheaf.stalk yσ)) N
                (φ α)) =
              Ideal.Quotient.mk (maximalIdeal ((pullback q τ).presheaf.stalk yτ) ^ N) z →
            Ideal.Quotient.mk (maximalIdeal (W.scheme.presheaf.stalk W.point) ^ N)
                (W.stalkHom z) =
              Ideal.Quotient.mk (maximalIdeal (W.scheme.presheaf.stalk W.point) ^ N)
                (F.stalkHomAt hF α)) ∧
        ∃ (eBase : (specCompletedStalk S s).residueField (specCompletedStalkPoint S s) ≅
            V.scheme.residueField V.point)
          (eFiber : (pullback.snd q (relativeBaseChangeMorphism s σ)).fiber
              (specCompletedStalkPoint S s) ≅
            (pullback.snd q τ).fiber V.point),
          (Spec.map eBase.inv ≫ V.scheme.fromSpecResidueField V.point ≫ V.toBase =
            (specCompletedStalk S s).fromSpecResidueField (specCompletedStalkPoint S s) ≫
              specCompletedStalkTo S s) ∧
          (Spec.map eBase.inv ≫ V.scheme.fromSpecResidueField V.point ≫ τ =
            (specCompletedStalk S s).fromSpecResidueField (specCompletedStalkPoint S s) ≫
              relativeBaseChangeMorphism s σ) ∧
          (eFiber.hom ≫ (pullback.snd q τ).fiberι V.point ≫ pullback.fst q τ =
            (pullback.snd q (relativeBaseChangeMorphism s σ)).fiberι
                (specCompletedStalkPoint S s) ≫
              pullback.fst q (relativeBaseChangeMorphism s σ)) ∧
          (eFiber.hom ≫ (pullback.snd q τ).fiberToSpecResidueField V.point =
            (pullback.snd q (relativeBaseChangeMorphism s σ)).fiberToSpecResidueField
                (specCompletedStalkPoint S s) ≫ Spec.map eBase.inv) ∧
          (eFiber.hom (((pullback.snd q (relativeBaseChangeMorphism s σ)).fiberHomeo
              (specCompletedStalkPoint S s)).symm
              ⟨yσ, snd_eq_closedPoint_of_fst_eq h q hy hts σ hσbase
                (relativeBaseChangeMorphism s σ) rfl yσ hyσY⟩) =
            ((pullback.snd q τ).fiberHomeo V.point).symm ⟨yτ, hyτV⟩) := by
  have := hσ
  have := hφ
  have : IsLocallyNoetherian T := LocallyOfFiniteType.isLocallyNoetherian h
  have : LocallyOfFinitePresentation h := inferInstance
  have : IsNoetherianRing (S.presheaf.stalk s) := inferInstance
  have hGhat := completion_isGRing (S.presheaf.stalk s) hG
  have : IsNoetherianRing (AdicCompletion (maximalIdeal (S.presheaf.stalk s))
    (S.presheaf.stalk s)) := hGhat.1
  have : IsLocallyNoetherian (specCompletedStalk S s) := inferInstance
  have hyσZ : pullback.snd q (relativeBaseChangeMorphism s σ) yσ =
      specCompletedStalkPoint S s :=
    snd_eq_closedPoint_of_fst_eq h q hy hts σ hσbase (relativeBaseChangeMorphism s σ) rfl
      yσ hyσY
  have hGz : IsGRing ((specCompletedStalk S s).presheaf.stalk
      (specCompletedStalkPoint S s)) :=
    isGRing_of_ringEquiv (stalkClosedPointIso (CommRingCat.of
      (AdicCompletion (maximalIdeal (S.presheaf.stalk s))
        (S.presheaf.stalk s)))).symm.commRingCatIsoToRingEquiv hGhat
  have : IsLocallyNoetherian (pullback q (relativeBaseChangeMorphism s σ)) :=
    LocallyOfFiniteType.isLocallyNoetherian
      (pullback.snd q (relativeBaseChangeMorphism s σ))
  have : IsNoetherianRing
    ((pullback q (relativeBaseChangeMorphism s σ)).presheaf.stalk yσ) := inferInstance
  -- **Tag 0CAU over `Spec 𝒪^∧_{S, s}`.** It replaces `φ` by a morphism to `X` out of an
  -- elementary étale neighbourhood of `(Y_σ, y_σ)`, agreeing with `φ` modulo `𝔪 ^ N`.
  obtain ⟨U, hUel, F, hF, hFover, hUcong0⟩ :=
    exists_elementaryEtaleNeighborhood_approximation_over_base p (specCompletedStalkTo S s)
      (pullback.snd q (relativeBaseChangeMorphism s σ)) x s (specCompletedStalkPoint S s) yσ
      hx hyσZ (specCompletedStalkTo_specCompletedStalkPoint S s) hGz N hN φ hφ hφbase
  have : IsLocallyNoetherian U.scheme := LocallyOfFiniteType.isLocallyNoetherian U.toBase
  have : IsNoetherianRing (U.scheme.presheaf.stalk U.point) := inferInstance
  have hUres : IsIso (U.toBase.residueFieldMap U.point) :=
    (EtaleNeighborhood.isElementary_iff U).mp hUel
  -- the pointed span over `Spec 𝒪^∧_{S, s}`: the `X`-leg is the morphism `F`, which Tag 0CAU
  -- does not make étale
  have hFcond : F ≫ p = (U.toBase ≫ pullback.snd q (relativeBaseChangeMorphism s σ)) ≫
      specCompletedStalkTo S s := by
    rwa [Category.assoc]
  let fU : U.scheme ⟶ (pullback p (specCompletedStalkTo S s) : Scheme.{u}) :=
    pullback.lift F (U.toBase ≫ pullback.snd q (relativeBaseChangeMorphism s σ)) hFcond
  have hfUfst : fU ≫ pullback.fst p (specCompletedStalkTo S s) = F :=
    pullback.lift_fst _ _ _
  have hfUsnd : fU ≫ pullback.snd p (specCompletedStalkTo S s) =
      U.toBase ≫ pullback.snd q (relativeBaseChangeMorphism s σ) := pullback.lift_snd _ _ _
  have hxσX : pullback.fst p (specCompletedStalkTo S s) (fU U.point) = x := by
    show (fU ≫ pullback.fst p (specCompletedStalkTo S s)) U.point = x
    rwa [hfUfst]
  have hxσZ : pullback.snd p (specCompletedStalkTo S s) (fU U.point) =
      specCompletedStalkPoint S s := by
    show (fU ≫ pullback.snd p (specCompletedStalkTo S s)) U.point = _
    rw [hfUsnd]
    show pullback.snd q (relativeBaseChangeMorphism s σ) (U.toBase U.point) = _
    rwa [U.map_point]
  have hUX : (fU ≫ pullback.fst p (specCompletedStalkTo S s)) U.point = x := by
    rwa [hfUfst]
  have hUY : (U.toBase ≫ pullback.fst q (relativeBaseChangeMorphism s σ)) U.point = y := by
    show pullback.fst q (relativeBaseChangeMorphism s σ) (U.toBase U.point) = y
    rwa [U.map_point]
  -- the congruence of Tag 0CAU, read as a congruence between `F^♯` and any lift of `φ`
  have hUsq : ∀ (α : X.presheaf.stalk x)
      (ξ : (pullback q (relativeBaseChangeMorphism s σ)).presheaf.stalk yσ),
      Ideal.Quotient.mk (maximalIdeal
          ((pullback q (relativeBaseChangeMorphism s σ)).presheaf.stalk yσ) ^ N) ξ =
        AdicCompletion.evalₐ (maximalIdeal
          ((pullback q (relativeBaseChangeMorphism s σ)).presheaf.stalk yσ)) N (φ α) →
      (fU ≫ pullback.fst p (specCompletedStalkTo S s)).stalkHomAt hUX α -
          U.toBase.stalkHomAt U.map_point ξ ∈
        maximalIdeal (U.scheme.presheaf.stalk U.point) ^ N := by
    intro α ξ hξ
    have h0 : AdicCompletion.evalₐ (maximalIdeal (U.scheme.presheaf.stalk U.point)) N
        (U.completionMap (φ α) -
          algebraMap (U.scheme.presheaf.stalk U.point)
            (AdicCompletion (maximalIdeal (U.scheme.presheaf.stalk U.point))
              (U.scheme.presheaf.stalk U.point)) (F.stalkHomAt hF α)) = 0 :=
      (evalₐ_eq_zero_iff_mem_map_pow
        (maximalIdeal (U.scheme.presheaf.stalk U.point)).fg_of_isNoetherianRing N _).mpr
        (hUcong0 α)
    rw [map_sub, sub_eq_zero, evalₐ_algebraMap] at h0
    have h1 : AdicCompletion.evalₐ (maximalIdeal (U.scheme.presheaf.stalk U.point)) N
          (U.completionMap (φ α)) =
        quotientPowMap (U.toBase.stalkHomAt U.map_point) N
          (AdicCompletion.evalₐ (maximalIdeal
            ((pullback q (relativeBaseChangeMorphism s σ)).presheaf.stalk yσ)) N (φ α)) :=
      evalₐ_completionMapAt U.toBase U.map_point N (φ α)
    have h2 : Ideal.Quotient.mk (maximalIdeal (U.scheme.presheaf.stalk U.point) ^ N)
          (F.stalkHomAt hF α) =
        Ideal.Quotient.mk (maximalIdeal (U.scheme.presheaf.stalk U.point) ^ N)
          (U.toBase.stalkHomAt U.map_point ξ) :=
      (h0.symm.trans h1).trans
        ((congrArg (quotientPowMap (U.toBase.stalkHomAt U.map_point) N) hξ).symm.trans
          (quotientPowMap_mk (U.toBase.stalkHomAt U.map_point) N ξ))
    have h3 : (fU ≫ pullback.fst p (specCompletedStalkTo S s)).stalkHomAt hUX α =
        F.stalkHomAt hF α :=
      RingHom.congr_fun (stalkHomAt_congr hfUfst hUX hF) α
    rw [h3]
    exact (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mp h2
  -- the diagram, from the pointed span, with `B = S`
  obtain ⟨V, τV, hτV, yτ, hyτY, hyτV, Wsch, w, pW, hpW, g, hgPoint, hgEt, hVel, hτVB, hresg,
    hover, -, hc3, -, hgZθ, hfib⟩ :=
    exists_approximationDiagram_over_base_of_span_truncationEquiv p q (𝟙 S) h hx hG N hN σ hσ
      (by rw [Category.comp_id]; exact relativeBaseChangeMorphism_comp h hts σ hσbase)
      (fU U.point) hxσX hxσZ yσ hyσY hyσZ U.scheme U.point fU rfl U.toBase inferInstance
      U.map_point hUres hfUsnd.symm
      (fun α b => Ideal.Quotient.mk (maximalIdeal
          ((pullback q (relativeBaseChangeMorphism s σ)).presheaf.stalk yσ) ^ N)
          ((pullback.fst q (relativeBaseChangeMorphism s σ)).stalkHomAt hyσY b) =
        AdicCompletion.evalₐ (maximalIdeal
          ((pullback q (relativeBaseChangeMorphism s σ)).presheaf.stalk yσ)) N (φ α))
      hUX hUY (fun α b hP => by
        have hc : (U.toBase ≫
              pullback.fst q (relativeBaseChangeMorphism s σ)).stalkHomAt hUY b =
            U.toBase.stalkHomAt U.map_point
              ((pullback.fst q (relativeBaseChangeMorphism s σ)).stalkHomAt hyσY b) :=
          RingHom.congr_fun (Scheme.Hom.stalkHomAt_comp U.toBase
            (pullback.fst q (relativeBaseChangeMorphism s σ)) U.map_point hyσY) b
        rw [hc]
        exact hUsq α _ hP)
  obtain ⟨θ, hθY, hθS, hθsq⟩ := hgZθ
  have := hgEt
  have : IsIso (g.residueFieldMap w) :=
    IsIso.of_isIso_comp_left ((pullback q τV).residueFieldCongr hgPoint).inv _
  have hcomm : pW ≫ p = (g ≫ pullback.snd q τV) ≫ V.toBase := by
    rw [Category.assoc]
    exact hover.symm
  refine ⟨V, τV, hτV, yτ, hyτY, hyτV,
    { scheme := Wsch, point := w, toBase := g, map_point := hgPoint }, pW, hpW,
    pullback.lift pW (g ≫ pullback.snd q τV) hcomm, hVel, ?_,
    hτVB.trans (Category.comp_id _), pullback.lift_fst _ _ hcomm,
    pullback.lift_snd _ _ hcomm, hover.symm, hc3, ⟨θ, hθY, hθS, ?_⟩, hfib⟩
  · rw [EtaleNeighborhood.isElementary_iff]
    exact inferInstance
  · intro α z hz
    obtain ⟨ξ, hξ⟩ := Ideal.Quotient.mk_surjective
      (AdicCompletion.evalₐ (maximalIdeal
        ((pullback q (relativeBaseChangeMorphism s σ)).presheaf.stalk yσ)) N (φ α))
    exact hθsq α ξ z (hUsq α ξ hξ) (hξ ▸ hz)

end StacksDraft.ArtinApproximation

end
