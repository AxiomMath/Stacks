module

public import Mathlib.Algebra.Category.Ring.Constructions
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import Mathlib.AlgebraicGeometry.Pullbacks
public import StacksCore.Tactic.StacksAttribute

/-!
# Cartesian affine-open charts for a base-change square of schemes

Let

```
X' --g'--> X
|          |
f'         f
v          v
S' --g---> S
```

be a cartesian diagram of schemes. Conditions (2) and (3) of Stacks 0DJ8 quantify over the
data of affine opens `U ⊆ X` and `V' ⊆ S'` both mapping into an affine open `V ⊆ S`, together
with `U' = V' ×_V U`. This module packages that data as a structure and proves the two facts
about it that the source proof uses without comment: that `U'` really is an open of `X'`, and
that every point of `X'` lies in such a `U'`.

Nothing here mentions a derived category, so none of it depends on a choice of model for the
derived category of sheaves of modules.

## Main definitions

* `AlgebraicGeometry.BaseChangeChart`: a Cartesian affine-open chart — the quadruple
  `U, V, V', U'` of Stacks 0DJ8 (2), presented by its four coordinate rings, the three open
  immersions from their spectra, the four induced ring maps and the pushout square
  `𝒪_{X'}(U') = 𝒪_X(U) ⊗_{𝒪_S(V)} 𝒪_{S'}(V')` that expresses `U' = V' ×_V U`.
* `AlgebraicGeometry.BaseChangeChart.ofAffineOpens`: the chart built from affine opens
  `U ⊆ X`, `V ⊆ S`, `V' ⊆ S'` with `f(U) ⊆ V` and `g(V') ⊆ V`.

## Main results

* `AlgebraicGeometry.BaseChangeChart.isOpenImmersion_incU'`: `U'` is an open of `X'`. The
  structure imposes no open-immersion hypothesis on `Spec 𝒪_{X'}(U') ⟶ X'`; once the outer
  square is cartesian this is automatic, `U'` being the base change of `U ⊆ X` and `V' ⊆ S'`
  over `V ⊆ S`.
* `AlgebraicGeometry.exists_baseChangeChart_covering`: every point of `X'` lies in the `U'` of
  some chart. This is the covering input to the step (2) ⟹ (3) of Stacks 0DJ8, the only
  content of that step beyond choosing the family of all charts.

## Implementation notes

A chart records `U ⊆ X`, `V ⊆ S`, `V' ⊆ S'` as open immersions from affine schemes rather than
as affine opens, because the ring maps and the pushout square are what the cohomological
statements of Stacks 0DJ8 consume. `BaseChangeChart.ofAffineOpens` is the translation from the
affine-open presentation, and `exists_baseChangeChart_covering` goes through it.

The pushout square `IsPushout a b c d` is `𝒪_{X'}(U') = 𝒪_X(U) ⊗_{𝒪_S(V)} 𝒪_{S'}(V')`, which
is the ring-level form of `U' = V' ×_V U`; `isPullback_SpecMap_of_isPushout` converts it back to
a pullback of affine schemes, and that is how `isOpenImmersion_incU'` is proved.

## References

* [Stacks Project, Tag 0DJ8](https://stacks.math.columbia.edu/tag/0DJ8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

universe u

namespace AlgebraicGeometry

/-- **A Cartesian affine-open chart for a base-change square of schemes.** This is the
quadruple `U, V, V', U'` of Stacks 0DJ8 (2): affine opens `U ⊆ X` and `V' ⊆ S'` both mapping
into an affine open `V ⊆ S`, together with `U' = V' ×_V U`, the last expressed by the pushout
square of coordinate rings. -/
@[stacks 0DJ8 "the Cartesian affine-open chart quantified over in (2) and (3)"]
public structure BaseChangeChart {X X' S S' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S)
    (f' : X' ⟶ S') (g' : X' ⟶ X) where
  /-- The coordinate ring `𝒪_S(V)` of the affine open `V ⊆ S`. -/
  R : CommRingCat.{u}
  /-- The coordinate ring `𝒪_X(U)` of the affine open `U ⊆ X`. -/
  A : CommRingCat.{u}
  /-- The coordinate ring `𝒪_{S'}(V')` of the affine open `V' ⊆ S'`. -/
  R' : CommRingCat.{u}
  /-- The coordinate ring `𝒪_{X'}(U')` of `U' = V' ×_V U`. -/
  A' : CommRingCat.{u}
  /-- The affine open `V ⊆ S`. -/
  incV : Spec R ⟶ S
  /-- The affine open `U ⊆ X`. -/
  incU : Spec A ⟶ X
  /-- The affine open `V' ⊆ S'`. -/
  incV' : Spec R' ⟶ S'
  /-- The open `U' = V' ×_V U` of `X'`. -/
  incU' : Spec A' ⟶ X'
  /-- `V` is an open of `S`. -/
  isOpenImmersion_incV : IsOpenImmersion incV
  /-- `U` is an open of `X`. -/
  isOpenImmersion_incU : IsOpenImmersion incU
  /-- `V'` is an open of `S'`. -/
  isOpenImmersion_incV' : IsOpenImmersion incV'
  /-- The map `𝒪_S(V) → 𝒪_X(U)` induced by `f(U) ⊆ V`. -/
  a : R ⟶ A
  /-- The map `𝒪_S(V) → 𝒪_{S'}(V')` induced by `g(V') ⊆ V`. -/
  b : R ⟶ R'
  /-- The map `𝒪_X(U) → 𝒪_{X'}(U')`. -/
  c : A ⟶ A'
  /-- The map `𝒪_{S'}(V') → 𝒪_{X'}(U')`. -/
  d : R' ⟶ A'
  /-- `U` maps into `V`. -/
  wU : incU ≫ f = Spec.map a ≫ incV
  /-- `V'` maps into `V`. -/
  wV' : incV' ≫ g = Spec.map b ≫ incV
  /-- `U'` maps into `U`. -/
  wU'U : incU' ≫ g' = Spec.map c ≫ incU
  /-- `U'` maps into `V'`. -/
  wU'V' : incU' ≫ f' = Spec.map d ≫ incV'
  /-- `U' = V' ×_V U`, i.e. `𝒪_{X'}(U') = 𝒪_X(U) ⊗_{𝒪_S(V)} 𝒪_{S'}(V')`. -/
  isPushout : IsPushout a b c d

namespace BaseChangeChart

variable {X X' S S' : Scheme.{u}} {f : X ⟶ S} {g : S' ⟶ S} {f' : X' ⟶ S'}
  {g' : X' ⟶ X}

/-- Restricting from `X` to `U'` through `U` agrees with restricting through `X'`, at the level
of morphisms of ringed spaces. This is `wU'U` in the form the derived pullback consumes. -/
public theorem wU'U_toShHom (ch : BaseChangeChart f g f' g') :
    (Spec.map ch.c).toLRSHom.toShHom ≫ ch.incU.toLRSHom.toShHom =
      ch.incU'.toLRSHom.toShHom ≫ g'.toLRSHom.toShHom := by
  simpa only [Scheme.Hom.comp_toLRSHom, LocallyRingedSpace.comp_toShHom] using
    congrArg (fun k : Spec ch.A' ⟶ X => k.toLRSHom.toShHom) ch.wU'U.symm

/-- The ring square of a chart, as a square of ring homomorphisms. -/
public theorem isPushout_hom (ch : BaseChangeChart f g f' g') :
    ch.c.hom.comp ch.a.hom = ch.d.hom.comp ch.b.hom := by
  rw [← CommRingCat.hom_comp, ← CommRingCat.hom_comp, ch.isPushout.w]

/-- **`U'` is an open of `X'`.** The structure imposes no open-immersion hypothesis on
`Spec 𝒪_{X'}(U') ⟶ X'`: once the outer square is cartesian the chart data determine that
morphism uniquely, and it is then automatically an open immersion, being the base change of
`U ⊆ X` and `V' ⊆ S'` over `V ⊆ S`. -/
@[stacks 0DJ8 "the U' of a chart is an open of X'"]
public theorem isOpenImmersion_incU' (sq : IsPullback g' f' f g)
    (ch : BaseChangeChart f g f' g') : IsOpenImmersion ch.incU' := by
  let inner := isPullback_SpecMap_of_isPushout ch.a ch.b ch.c ch.d ch.isPushout
  let q := pullback.map (Spec.map ch.a) (Spec.map ch.b) f g
    ch.incU ch.incV' ch.incV ch.wU.symm ch.wV'.symm
  have : IsOpenImmersion ch.incU := ch.isOpenImmersion_incU
  have : IsOpenImmersion ch.incV := ch.isOpenImmersion_incV
  have : IsOpenImmersion ch.incV' := ch.isOpenImmersion_incV'
  have he : ch.incU' = inner.isoPullback.hom ≫ q ≫ sq.isoPullback.inv := by
    apply sq.hom_ext
    · simp only [Category.assoc, sq.isoPullback_inv_fst]
      change ch.incU' ≫ g' = inner.isoPullback.hom ≫
        (pullback.map _ _ _ _ _ _ _ _ _ ≫ pullback.fst f g)
      dsimp only [pullback.map]
      rw [pullback.lift_fst, ← Category.assoc, inner.isoPullback_hom_fst]
      exact ch.wU'U
    · simp only [Category.assoc, sq.isoPullback_inv_snd]
      change ch.incU' ≫ f' = inner.isoPullback.hom ≫
        (pullback.map _ _ _ _ _ _ _ _ _ ≫ pullback.snd f g)
      dsimp only [pullback.map]
      rw [pullback.lift_snd, ← Category.assoc, inner.isoPullback_hom_snd]
      exact ch.wU'V'
  rw [he]
  dsimp only [q]
  infer_instance

/-- **The chart on given affine opens.** For affine opens `U ⊆ X`, `V ⊆ S`, `V' ⊆ S'` with
`f(U) ⊆ V` and `g(V') ⊆ V`, the coordinate rings and the tensor product
`𝒪_X(U) ⊗_{𝒪_S(V)} 𝒪_{S'}(V')` form a chart, its `U'` being the canonical open
`V' ×_V U` of `X'`. -/
@[stacks 0DJ8 "the chart on a triple of affine opens"]
public def ofAffineOpens (sq : IsPullback g' f' f g)
    (U : X.Opens) (V : S.Opens) (V' : S'.Opens)
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) (hV' : IsAffineOpen V')
    (hUV : U ≤ f ⁻¹ᵁ V) (hV'V : V' ≤ g ⁻¹ᵁ V) : BaseChangeChart f g f' g' := by
  let R : CommRingCat := CommRingCat.of Γ(S, V)
  let A : CommRingCat := CommRingCat.of Γ(X, U)
  let R' : CommRingCat := CommRingCat.of Γ(S', V')
  let a : R ⟶ A := f.appLE V U hUV
  let b : R ⟶ R' := g.appLE V V' hV'V
  letI : Algebra Γ(S, V) Γ(X, U) := a.hom.toAlgebra
  letI : Algebra Γ(S, V) Γ(S', V') := b.hom.toAlgebra
  let A' : CommRingCat := CommRingCat.of (Γ(X, U) ⊗[Γ(S, V)] Γ(S', V'))
  let c : A ⟶ A' := CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom
  let d : R' ⟶ A' := CommRingCat.ofHom Algebra.TensorProduct.includeRight.toRingHom
  let incU : Spec A ⟶ X := hU.fromSpec
  let incV : Spec R ⟶ S := hV.fromSpec
  let incV' : Spec R' ⟶ S' := hV'.fromSpec
  let α := Spec.map (CommRingCat.ofHom (algebraMap Γ(S, V) Γ(X, U)))
  let β := Spec.map (CommRingCat.ofHom (algebraMap Γ(S, V) Γ(S', V')))
  let e := pullbackSpecIso Γ(S, V) Γ(X, U) Γ(S', V')
  have hefst : e.inv ≫ pullback.fst α β = Spec.map c :=
    pullbackSpecIso_inv_fst Γ(S, V) Γ(X, U) Γ(S', V')
  have hesnd : e.inv ≫ pullback.snd α β = Spec.map d :=
    pullbackSpecIso_inv_snd Γ(S, V) Γ(X, U) Γ(S', V')
  have hwU : α ≫ incV = incU ≫ f := IsAffineOpen.SpecMap_appLE_fromSpec f hV hU hUV
  have hwV' : β ≫ incV = incV' ≫ g := IsAffineOpen.SpecMap_appLE_fromSpec g hV hV' hV'V
  let q : pullback α β ⟶ pullback f g := pullback.map α β f g incU incV' incV hwU hwV'
  have hqf : q ≫ pullback.fst f g = pullback.fst α β ≫ incU := by
    dsimp only [q, pullback.map]
    rw [pullback.lift_fst]
  have hqg : q ≫ pullback.snd f g = pullback.snd α β ≫ incV' := by
    dsimp only [q, pullback.map]
    rw [pullback.lift_snd]
  let incU' : Spec A' ⟶ X' := e.inv ≫ q ≫ sq.isoPullback.inv
  refine ⟨R, A, R', A', incV, incU, incV', incU', hV.isOpenImmersion_fromSpec,
    hU.isOpenImmersion_fromSpec, hV'.isOpenImmersion_fromSpec, a, b, c, d,
    ?_, ?_, ?_, ?_, ?_⟩
  · exact (IsAffineOpen.SpecMap_appLE_fromSpec f hV hU hUV).symm
  · exact (IsAffineOpen.SpecMap_appLE_fromSpec g hV hV' hV'V).symm
  · dsimp only [incU']
    calc
      e.inv ≫ q ≫ sq.isoPullback.inv ≫ g' = e.inv ≫ q ≫ pullback.fst f g := by
        simp [sq.isoPullback_inv_fst]
      _ = e.inv ≫ pullback.fst α β ≫ incU := by rw [hqf]
      _ = Spec.map c ≫ incU := by rw [← Category.assoc, hefst]
  · dsimp only [incU']
    calc
      e.inv ≫ q ≫ sq.isoPullback.inv ≫ f' = e.inv ≫ q ≫ pullback.snd f g := by
        simp [sq.isoPullback_inv_snd]
      _ = e.inv ≫ pullback.snd α β ≫ incV' := by rw [hqg]
      _ = Spec.map d ≫ incV' := by rw [← Category.assoc, hesnd]
  · exact CommRingCat.isPushout_tensorProduct Γ(S, V) Γ(X, U) Γ(S', V')

end BaseChangeChart

/-- **Every point of `X'` lies in the `U'` of a chart.** Choose an affine open `V ⊆ S` around
`f(g' x')`, then an affine open `U ⊆ X` around `g' x'` inside `f⁻¹V`, then an affine open
`V' ⊆ S'` around `f' x'` inside `g⁻¹V`; the resulting chart's `U' = V' ×_V U` contains `x'`,
because `x'` corresponds to a point of `U ×_V V'` under the cartesian square.

This is the covering input to the step (2) ⟹ (3) of Stacks 0DJ8. -/
@[stacks 0DJ8 "every point of X' lies in the U' of a chart, the covering input to (2) ⟹ (3)"]
public theorem exists_baseChangeChart_covering {X X' S S' : Scheme.{u}} {f : X ⟶ S}
    {g : S' ⟶ S} {f' : X' ⟶ S'} {g' : X' ⟶ X} (sq : IsPullback g' f' f g) (x' : X') :
    ∃ ch : BaseChangeChart f g f' g', ∃ y : Spec ch.A', ch.incU' y = x' := by
  obtain ⟨V, hV, hsV, -⟩ := exists_isAffineOpen_mem_and_subset
    (X := S) (x := f (g' x')) (U := ⊤) (by simp)
  obtain ⟨U, hU, hxU, hUV⟩ := exists_isAffineOpen_mem_and_subset
    (X := X) (x := g' x') (U := f ⁻¹ᵁ V) (by simpa using hsV)
  have hsq : f (g' x') = g (f' x') := by
    simpa only [Scheme.Hom.comp_apply] using congrArg (fun k : X' ⟶ S => k x') sq.w
  have hs'V : f' x' ∈ g ⁻¹ᵁ V := by
    change g (f' x') ∈ V
    rw [← hsq]
    exact hsV
  obtain ⟨V', hV', hs'V', hV'V⟩ := exists_isAffineOpen_mem_and_subset
    (X := S') (x := f' x') (U := g ⁻¹ᵁ V) hs'V
  let _ : Algebra Γ(S, V) Γ(X, U) := (f.appLE V U hUV).hom.toAlgebra
  let _ : Algebra Γ(S, V) Γ(S', V') := (g.appLE V V' hV'V).hom.toAlgebra
  let incU : Spec (CommRingCat.of Γ(X, U)) ⟶ X := hU.fromSpec
  let incV : Spec (CommRingCat.of Γ(S, V)) ⟶ S := hV.fromSpec
  let incV' : Spec (CommRingCat.of Γ(S', V')) ⟶ S' := hV'.fromSpec
  have hα : Spec.map (CommRingCat.ofHom (algebraMap Γ(S, V) Γ(X, U))) =
      Spec.map (f.appLE V U hUV) := by
    apply congrArg Spec.map
    exact CommRingCat.hom_ext rfl
  have hβ : Spec.map (CommRingCat.ofHom (algebraMap Γ(S, V) Γ(S', V'))) =
      Spec.map (g.appLE V V' hV'V) := by
    apply congrArg Spec.map
    exact CommRingCat.hom_ext rfl
  let e := AlgebraicGeometry.pullbackSpecIso (Γ(S, V) : Type u)
    (Γ(X, U) : Type u) (Γ(S', V') : Type u)
  have hwU : Spec.map (CommRingCat.ofHom (algebraMap Γ(S, V) Γ(X, U))) ≫ incV =
      incU ≫ f := by
    rw [hα]
    exact IsAffineOpen.SpecMap_appLE_fromSpec f hV hU hUV
  have hwV' : Spec.map (CommRingCat.ofHom (algebraMap Γ(S, V) Γ(S', V'))) ≫ incV =
      incV' ≫ g := by
    rw [hβ]
    exact IsAffineOpen.SpecMap_appLE_fromSpec g hV hV' hV'V
  let q := pullback.map
    (Spec.map (CommRingCat.ofHom (algebraMap Γ(S, V) Γ(X, U))))
    (Spec.map (CommRingCat.ofHom (algebraMap Γ(S, V) Γ(S', V')))) f g
    incU incV' incV hwU hwV'
  let ch := BaseChangeChart.ofAffineOpens sq U V V' hU hV hV' hUV hV'V
  have : IsOpenImmersion ch.incU := ch.isOpenImmersion_incU
  have : IsOpenImmersion ch.incV := ch.isOpenImmersion_incV
  have : IsOpenImmersion ch.incV' := ch.isOpenImmersion_incV'
  let z := sq.isoPullback.hom x'
  have hz1 : pullback.fst f g z ∈ Set.range ch.incU := by
    change pullback.fst f g (sq.isoPullback.hom x') ∈ Set.range ch.incU
    rw [← Scheme.Hom.comp_apply, sq.isoPullback_hom_fst]
    rw [← Scheme.Hom.coe_opensRange]
    change g' x' ∈ ↑(hU.fromSpec.opensRange)
    rw [hU.opensRange_fromSpec]
    exact hxU
  have hz2 : pullback.snd f g z ∈ Set.range ch.incV' := by
    change pullback.snd f g (sq.isoPullback.hom x') ∈ Set.range ch.incV'
    rw [← Scheme.Hom.comp_apply, sq.isoPullback_hom_snd]
    rw [← Scheme.Hom.coe_opensRange]
    change f' x' ∈ ↑(hV'.fromSpec.opensRange)
    rw [hV'.opensRange_fromSpec]
    exact hs'V'
  have hz : z ∈ Set.range q := by
    rw [Scheme.Pullback.range_map
      (f := Spec.map (CommRingCat.ofHom (algebraMap Γ(S, V) Γ(X, U))))
      (g := Spec.map (CommRingCat.ofHom (algebraMap Γ(S, V) Γ(S', V'))))
      f g incU incV' incV hwU hwV']
    exact ⟨hz1, hz2⟩
  obtain ⟨w, hw⟩ := hz
  refine ⟨ch, e.hom w, ?_⟩
  change sq.isoPullback.inv (q (e.inv (e.hom w))) = x'
  have he : e.inv (e.hom w) = w := by
    have h := congrArg (fun k => k w) e.hom_inv_id
    rw [Scheme.Hom.comp_apply] at h
    exact h.trans (by rfl)
  have hs : sq.isoPullback.inv (sq.isoPullback.hom x') = x' := by
    have h := congrArg (fun k => k x') sq.isoPullback.hom_inv_id
    rw [Scheme.Hom.comp_apply] at h
    exact h.trans (by rfl)
  rw [he, hw]
  exact hs

/-- **The step (2) ⟹ (3) of Stacks 0DJ8.** If a property of charts holds for every chart then
there is a family of charts on which it holds whose opens `U'` cover `X'`: take the family of
all charts and apply `exists_baseChangeChart_covering`.

The property is left abstract because this step uses nothing about it. Reading `P ch` as
"the comparison map of `ch` is an isomorphism" turns this into the implication (2) ⟹ (3) of
the source, which is the only use intended. -/
@[stacks 0DJ8 "(2) ⟹ (3), for an arbitrary property of charts"]
public theorem exists_coveringFamily_of_forall_baseChangeChart {X X' S S' : Scheme.{u}}
    {f : X ⟶ S} {g : S' ⟶ S} {f' : X' ⟶ S'} {g' : X' ⟶ X} (sq : IsPullback g' f' f g)
    (P : BaseChangeChart f g f' g' → Prop) (h : ∀ ch : BaseChangeChart f g f' g', P ch) :
    ∃ 𝒞 : Set (BaseChangeChart f g f' g'), (∀ ch ∈ 𝒞, P ch) ∧
      ∀ x' : X', ∃ ch ∈ 𝒞, ∃ y : Spec ch.A', ch.incU' y = x' := by
  refine ⟨Set.univ, fun ch _ => h ch, fun x' => ?_⟩
  obtain ⟨ch, y, hy⟩ := exists_baseChangeChart_covering sq x'
  exact ⟨ch, Set.mem_univ _, y, hy⟩

end AlgebraicGeometry

end
