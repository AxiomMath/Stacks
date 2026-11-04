module

public import StacksFrontier.AlgebraicGeometry.ChartModuleSystem.Pullback
public import StacksFrontier.AlgebraicGeometry.NaiveCotangentDeterminant.BaseChange
public import StacksFrontier.AlgebraicGeometry.NaiveCotangentDeterminant.GoodChart

/-!
# The identification `b^*det(NL_{Y/X}) ≅ det(NL_{Y'/X'})`

Consider a commutative square of schemes

```
Y' --b--> Y
|f'       |f
X' --a--> X
```

with `f` and `f'` syntomic, which induces an isomorphism of `Y'` with an open subscheme of
`X' ×_X Y`. Then the canonical map `Lb^*NL_{Y/X} → NL_{Y'/X'}` is a quasi-isomorphism and gives
a canonical isomorphism `b^*det(NL_{Y/X}) ≅ det(NL_{Y'/X'})` (Discriminants, Section 0FKB).
On charts `(U, V)` of `f` and `(U', V')` of `f'` lying over them it is the base change map
`det(NL_{Γ(V)/Γ(U)}) → det(NL_{Γ(V')/Γ(U')})` of the square of rings of the charts, which is
good for the naive cotangent complex; such charts cover `b⁻¹V` arbitrarily finely because `Y'`
is open in the fibre product (`AlgebraicGeometry.Scheme.Hom.exists_isGoodChartSquare`).

## Main definitions

* `AlgebraicGeometry.Scheme.Hom.detNLChartMapData`: the charts of `f'` lying over the charts
  of `f`.
* `AlgebraicGeometry.Scheme.Hom.detNLMapData`: the base change maps of determinants along them.
* `AlgebraicGeometry.Scheme.Hom.detNLPullbackIso`: the isomorphism
  `b^*det(NL_{Y/X}) ≅ det(NL_{Y'/X'})`.

## Main results

* `AlgebraicGeometry.Scheme.Hom.detNLSectionsEquiv_homEquiv_detNLPullbackIso_hom`: on charts
  lying over charts, `detNLPullbackIso` is the base change map of determinants.
* `AlgebraicGeometry.Scheme.Hom.homEquiv_detNLPullbackIso_hom_deltaNL`: it carries
  `δ(NL_{Y/X})` to `δ(NL_{Y'/X'})`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.ChartModuleSystem.MapData

open AlgebraicGeometry.Scheme

variable {Y' Y : Scheme.{u}} {b : Y' ⟶ Y} {I' : Y'.AffineChartIndex} {I : Y.AffineChartIndex}
  {D : I'.MapData b I} {S : ChartModuleSystem I} {S' : ChartModuleSystem I'}

/-- **Global sections under `pushforwardMap`**: a global section of `S.sheaf` whose values on the
charts are carried by `τ` to the values of a global section of `S'.sheaf` on the charts over them
is carried by `pushforwardMap` to that section. -/
theorem pushforwardMap_app_top_eq (T : MapData D S S') (s : Γ(S.sheaf, ⊤)) (s' : Γ(S'.sheaf, ⊤))
    (h : ∀ {c' : I'.ι} {c : I.ι} (h : D.Over c' c),
      T.τ h (S.sectionsEquiv c (S.sheaf.presheaf.map (homOfLE le_top).op s)) =
        S'.sectionsEquiv c' (S'.sheaf.presheaf.map (homOfLE le_top).op s')) :
    T.pushforwardMap.app ⊤ s = S'.sheaf.presheaf.map (homOfLE le_top).op s' := by
  refine S'.section_ext fun e he => ?_
  let J := {p : I'.ι × I.ι // D.Over p.1 p.2 ∧ I'.Refines p.1 e}
  refine S'.eq_of_ρ_eq (d := e) (fun j : J => j.1.1) (fun j => j.2.2) (fun y hy => ?_)
    fun j => ?_
  · obtain ⟨c, hc⟩ := I.exists_mem (b y)
    obtain ⟨e', he', hee', hye'⟩ := D.exists_over_refines (show y ∈ b ⁻¹ᵁ (I.V c).1 from hc) hy
    exact ⟨⟨(e', c), he', hee'⟩, hye'⟩
  · obtain ⟨⟨e', c⟩, he', hee'⟩ := j
    rw [← sectionsEquiv_restrict, ← sectionsEquiv_restrict]
    have key := T.sectionsEquiv_pushforwardMap_app he'
      (S.sheaf.presheaf.map (homOfLE le_top).op s)
    rw [T.pushforwardMap.app_presheaf_map (homOfLE (le_top : (I.V c).1 ≤ ⊤)) s] at key
    refine Eq.trans ?_ (key.trans ((h he').trans ?_))
    · rfl
    · rfl

end AlgebraicGeometry.ChartModuleSystem.MapData

namespace AlgebraicGeometry.Scheme.Hom

variable {X Y X' Y' : Scheme.{u}} {f : Y ⟶ X} {f' : Y' ⟶ X'} {a : X' ⟶ X} {b : Y' ⟶ Y}
  (w : b ≫ f = f' ≫ a) [IsOpenImmersion (pullback.lift b f' w)] (hf : Syntomic f)
  (hf' : Syntomic f')

/-- The charts of `f'` lying over the charts of `f` along a square which induces an open
immersion of `Y'` into `X' ×_X Y`. -/
def detNLChartMapData : f'.chartIndex.MapData b f.chartIndex where
  Over c' c := ChartOver w c' c
  le_preimage h := h.snd.fst
  over_of_refines h h' := h.of_refines w hf hf' h'
  exists_over {c y'} hy {W} hyW := by
    obtain ⟨U', V', e', hU, hV, hsq, hyV', hV'W⟩ :=
      exists_isGoodChartSquare w hf c.1.1 c.1.2 c.2 hy hyW
    exact ⟨⟨(U', V'), e'⟩, ⟨hU, hV, hsq⟩, hyV', hV'W⟩

/-- The base change maps of determinants along the charts of `f'` lying over the charts of `f`,
a morphism of chart module systems along `b`. -/
def detNLMapData :
    ChartModuleSystem.MapData (detNLChartMapData w hf hf') (f.detNLSystem hf) (f'.detNLSystem hf')
    where
  τ h := ChartOver.map w hf hf' h
  τ_ρ h h₁ hc hc' x := ChartOver.map_detNLChartRestrict w hf hf' h h₁ hc hc' x

/-- **The identification `b^*det(NL_{Y/X}) ≅ det(NL_{Y'/X'})`** of Discriminants, Section 0FKB,
for a commutative square `b ≫ f = f' ≫ a` of syntomic morphisms inducing an isomorphism of `Y'`
with an open subscheme of `X' ×_X Y`: on charts of `f'` lying over charts of `f` it is the base
change map of determinants of naive cotangent complexes. -/
def detNLPullbackIso : (Scheme.Modules.pullback b).obj (f.detNL hf) ≅ f'.detNL hf' :=
  (detNLMapData w hf hf').pullbackIso fun _ _ h =>
    isBaseChangeAlong_detNLSquareMap w hf hf' _ _ h.fst h.snd.fst h.snd.snd


/-- The adjoint transpose `det(NL_{Y/X}) ⟶ b_*det(NL_{Y'/X'})` of `detNLPullbackIso` is the
morphism of glued sheaves induced by the base change maps. -/
theorem homEquiv_detNLPullbackIso_hom :
    (Scheme.Modules.pullbackPushforwardAdjunction b).homEquiv _ _ (detNLPullbackIso w hf hf').hom =
      (detNLMapData w hf hf').pushforwardMap :=
  Equiv.apply_symm_apply _ _

/-- **`detNLPullbackIso` on sections**: for a chart `c'` of `f'` lying over a chart `c` of `f`, a
section of `det(NL_{Y/X})` over `V` is carried, through the adjoint transpose of
`detNLPullbackIso` and restriction to `V'`, to its image under the base change map
`det(NL_{Γ(V)/Γ(U)}) → det(NL_{Γ(V')/Γ(U')})`. -/
theorem detNLSectionsEquiv_homEquiv_detNLPullbackIso_hom {c' : f'.chartIndex.ι}
    {c : f.chartIndex.ι} (h : ChartOver w c' c) (s : Γ(f.detNL hf, c.1.2.1)) :
    f'.detNLSectionsEquiv hf' c' ((f'.detNL hf').presheaf.map (homOfLE h.snd.fst).op
      (((Scheme.Modules.pullbackPushforwardAdjunction b).homEquiv _ _
        (detNLPullbackIso w hf hf').hom).app c.1.2.1 s)) =
      h.map w hf hf' (f.detNLSectionsEquiv hf c s) := by
  rw [homEquiv_detNLPullbackIso_hom]
  exact (detNLMapData w hf hf').sectionsEquiv_pushforwardMap_app (D := detNLChartMapData w hf hf')
    (c' := c') (c := c) h s


/-- **`detNLPullbackIso` carries `δ(NL_{Y/X})` to `δ(NL_{Y'/X'})`** (Discriminants,
Section 0FKB): through the adjoint transpose `det(NL_{Y/X}) ⟶ b_*det(NL_{Y'/X'})` of
`detNLPullbackIso`, the global section `δ(NL_{Y/X})` goes to `δ(NL_{Y'/X'})`, for `f` and `f'`
locally quasi-finite and syntomic. -/
theorem homEquiv_detNLPullbackIso_hom_deltaNL [LocallyQuasiFinite f] [LocallyQuasiFinite f'] :
    ((Scheme.Modules.pullbackPushforwardAdjunction b).homEquiv _ _
      (detNLPullbackIso w hf hf').hom).app ⊤ (f.deltaNL hf) =
      (f'.detNL hf').presheaf.map (homOfLE le_top).op (f'.deltaNL hf') := by
  rw [homEquiv_detNLPullbackIso_hom]
  refine (detNLMapData w hf hf').pushforwardMap_app_top_eq _ _ fun {c' c} h => ?_
  exact (congrArg (h.map w hf hf') (f.detNLSectionsEquiv_deltaNL hf c)).trans
    ((detNLSquareMap_deltaNLChart w hf hf' c c' h.fst h.snd.fst h.snd.snd).trans
      (f'.detNLSectionsEquiv_deltaNL hf' c').symm)

end AlgebraicGeometry.Scheme.Hom

end
