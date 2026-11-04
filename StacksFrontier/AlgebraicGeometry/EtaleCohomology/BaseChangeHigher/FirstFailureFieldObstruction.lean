module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.BaseChangeTransitivity
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.EtaleBaseChange
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.FieldPointDirected
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.FirstFailureField
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.IntegralSurjectiveCover
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.ObstructionLimit
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.ObstructionRestriction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.SmallEtaleDerivedIdentity
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.StalkwiseCriterion
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.TorsionSheafEmbedding
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.SystemPullbackComparison
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TopologicalInvarianceThickening

/-!
# A failure of étale base change is already visible over a field: the obstruction class

Let `f : X ⟶ S` be a morphism of schemes and `n` an integer, as in the condition `BC(f, n, q₀)`
of [Stacks, Tag 0F02]. If `BC(f, n, q)` holds while `BC(f, n, q + 1)` fails, then the failure can
be realized over the spectrum of a field: there are a commutative diagram

```
X  ←--  X'  ←-h-  Y
|f      |f'       |e
S  ←--  S'  ←-g-  Spec K
```

with both squares cartesian and `K` a field, and an abelian sheaf `F` on the small étale site of
`Spec K` annihilated by `n`, for which `(f')⁻¹ R^{q+1} g_* F ⟶ R^{q+1} h_* e⁻¹ F` is not an
isomorphism. This is [Stacks, Tag 0F07].

The route is the source's. A counterexample over a general base exists because `BC(f, n, q + 1)`
fails, and sits in degree exactly `q + 1` because `BC(f, n, q)` holds. Its base is shrunk to an
affine open of `S'`, which makes the base `T₀` of the sheaf quasi-compact and quasi-separated. By
part (1) of [Stacks, Tag 0F03] the base change map is injective, so some stalk at a geometric
point `x` of `X'` misses a class `ξ`. The dévissage
`AlgebraicGeometry.exists_field_point_of_isDirected` of [Stacks, Tag 0F06] is then applied to the
source's property `P(T')`: the image of `ξ` under the pullback map to `T'` still misses the
image of the base change map over `T'`. That property holds at `T₀` itself, and at a
field-valued point it forces the base change map to fail.

## Main results

* `Stacks.EtaleCohomology.obstructionSurvives_iff_of_isThickening` — `P` is invariant under
  thickenings, hypothesis (1) of the dévissage.
* `Stacks.EtaleCohomology.exists_affine_field_not_isIso_higherBaseChangeMapAb` —
  [Stacks, Tag 0F07], with the base `S'` of the diagram moreover affine.

The obstruction class and the property `P` (`Stacks.EtaleCohomology.obstructionStalk`,
`Stacks.EtaleCohomology.ObstructionSurvives`) are in `ObstructionClass.lean`; the opening of the
source's proof, `Stacks.EtaleCohomology.exists_not_isIso_higherBaseChangeMapAb_succ`, is in
`FirstFailureField.lean`.

## Implementation notes

The index convention is the one the rest of this development uses: the source's `q ≥ 1` with
`BC(f, n, q - 1)` true and `BC(f, n, q)` false is read as degree `q + 1` with `BC(f, n, q)` true
and `BC(f, n, q + 1)` false, so that no subtraction on `ℤ` has to be moved across the
`Stacks.EtaleCohomology.BaseChangeHolds` argument.

The property `P` records a *fixed* class `ξ`, as the source does, and not merely the failure of
the base change map over `T'`. Only the fixed class makes the limit hypothesis of the dévissage
true: a cokernel can be nonzero at every stage of an inverse system and vanish at its limit,
whereas a class that survives at every stage survives in the colimit computing the stalk at the
limit.

The cartesian square over `T'` is part of the data asserted to exist rather than a chosen fibre
product, and the pullback map of the source is the base change map of the square
`h' ≫ 𝟙 = y ≫ h₀`, which is defined for an arbitrary commutative square.

The step *"we may and do replace `S'` by an affine open of `S'`"* is
`Stacks.EtaleCohomology.isIso_higherBaseChangeMapAb_app_of_forall_isAffine`. The three
hypotheses of the dévissage for `P` are:

* (1) invariance under thickenings, from the topological invariance of the étale site
  ([Stacks, Tag 03SI]): `Stacks.EtaleCohomology.obstructionSurvives_iff_of_isThickening`;
* (2) passage to directed limits with affine transition morphisms, from [Stacks, Tag 09Z1]:
  `Stacks.EtaleCohomology.obstructionSurvives_of_isLimit`;
* (3) the open-or-closed alternative, from parts (2) and (3) of [Stacks, Tag 0F03]:
  `Stacks.EtaleCohomology.obstructionSurvives_open_or_closed`.

## References

* [Stacks Project, Tag 0F07](https://stacks.math.columbia.edu/tag/0F07)
* [Stacks Project, Tag 0F06](https://stacks.math.columbia.edu/tag/0F06)
* [Stacks Project, Tag 0F02](https://stacks.math.columbia.edu/tag/0F02)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
open Stacks.Thickenings

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard

/-- The comparison of two squares underlying the invariance of `ObstructionSurvives` under
thickenings: a square over `W₁` with a universal homeomorphism `yφ` to a square over `W₂`, lying
over a universal homeomorphism `φ : W₁ ⟶ W₂`, has the obstruction condition exactly when the
square over `W₂` has it. -/
private theorem obstructionCondition_iff {V X_V T₀ Y₀ : Scheme.{u}} {fV : X_V ⟶ V}
    {g₀ : T₀ ⟶ V} {h₀ : Y₀ ⟶ X_V} {e₀ : Y₀ ⟶ T₀} (sq₀ : IsPullback h₀ e₀ fV g₀)
    {F₀ : Sheaf (smallEtaleTopology T₀) Ab.{u + 1}} {r : ℕ} (x : GeometricPoint X_V)
    (ξ : obstructionStalk h₀ e₀ F₀ r x) {W₁ W₂ Y₁ Y₂ : Scheme.{u}} (φ : W₁ ⟶ W₂)
    [UniversalHomeomorphism φ] (π : W₂ ⟶ T₀) (h₁ : Y₁ ⟶ X_V) (e₁ : Y₁ ⟶ W₁)
    (sq₁ : IsPullback h₁ e₁ fV ((φ ≫ π) ≫ g₀)) (y₁ : Y₁ ⟶ Y₀) (hy₁ : y₁ ≫ e₀ = e₁ ≫ φ ≫ π)
    (hyh₁ : h₁ ≫ 𝟙 X_V = y₁ ≫ h₀) (h₂ : Y₂ ⟶ X_V) (e₂ : Y₂ ⟶ W₂)
    (sq₂ : IsPullback h₂ e₂ fV (π ≫ g₀)) (y₂ : Y₂ ⟶ Y₀) (hy₂ : y₂ ≫ e₀ = e₂ ≫ π)
    (hyh₂ : h₂ ≫ 𝟙 X_V = y₂ ≫ h₀) (yφ : Y₁ ⟶ Y₂) (hφh : h₁ ≫ 𝟙 X_V = yφ ≫ h₂)
    (hφe : yφ ≫ e₂ = e₁ ≫ φ) (hpb : IsPullback yφ e₁ e₂ φ) :
    (∀ η, (smallEtaleStalkAb x.hom).map
        ((higherBaseChangeMapAb fV ((φ ≫ π) ≫ g₀) h₁ e₁ sq₁.w r).app
          ((smallEtalePullbackAb (φ ≫ π)).obj F₀)) η ≠
      (smallEtaleStalkAb x.hom).map
        ((higherBaseChangeMapAb (𝟙 X_V) h₀ h₁ y₁ hyh₁ r).app ((smallEtalePullbackAb e₀).obj F₀) ≫
          ((smallEtalePushforwardAb h₁).rightDerived r).map
            ((smallEtalePullbackAbComp' y₁ e₀ (y₁ ≫ e₀) rfl).hom.app F₀ ≫
              (smallEtalePullbackAbComp' e₁ (φ ≫ π) (y₁ ≫ e₀) hy₁).inv.app F₀)) ξ) ↔
    (∀ η, (smallEtaleStalkAb x.hom).map
        ((higherBaseChangeMapAb fV (π ≫ g₀) h₂ e₂ sq₂.w r).app
          ((smallEtalePullbackAb π).obj F₀)) η ≠
      (smallEtaleStalkAb x.hom).map
        ((higherBaseChangeMapAb (𝟙 X_V) h₀ h₂ y₂ hyh₂ r).app ((smallEtalePullbackAb e₀).obj F₀) ≫
          ((smallEtalePushforwardAb h₂).rightDerived r).map
            ((smallEtalePullbackAbComp' y₂ e₀ (y₂ ≫ e₀) rfl).hom.app F₀ ≫
              (smallEtalePullbackAbComp' e₂ π (y₂ ≫ e₀) hy₂).inv.app F₀)) ξ) := by
  have := Stacks.Etale.universalHomeomorphism_of_isPullback hpb
  have hy : y₁ = yφ ≫ y₂ := sq₀.hom_ext
    (by
      simp only [Category.comp_id] at hyh₁ hyh₂ hφh
      rw [← hyh₁, Category.assoc, ← hyh₂, hφh])
    (by rw [hy₁, Category.assoc, hy₂, reassoc_of% hφe])
  exact forall_stalk_ne_iff_of_universalHomeomorphism h₁ e₁ (φ ≫ π) ((φ ≫ π) ≫ g₀) h₂ e₂ π
    (π ≫ g₀) φ rfl yφ hφh hφe y₁ y₂ hy₁ hy₂ hyh₁ hyh₂ hy sq₁.w sq₂.w
    (by rw [Category.comp_id, Category.assoc]) x ξ

/-- **The property `P` is invariant under thickenings**: hypothesis (1) of the dévissage
`AlgebraicGeometry.exists_field_point_of_isDirected` of [Stacks, Tag 0F06] for
`Stacks.EtaleCohomology.ObstructionSurvives`. For a thickening `i : Z ⟶ Z'` and `π : Z' ⟶ T₀`,
`P` holds for `i ≫ π` exactly when it holds for `π`.

A thickening is a universal homeomorphism, so is its base change `X_V ×_V Z ⟶ X_V ×_V Z'`, and
the obstruction condition is invariant under such a pair
(`Stacks.EtaleCohomology.forall_stalk_ne_iff_of_universalHomeomorphism`); this is where the
topological invariance of the étale site ([Stacks, Tag 03SI]) enters. A square over `Z` is
compared with the chosen fibre product over `Z'`, and a square over `Z'` with its base change
to `Z`. -/
public theorem obstructionSurvives_iff_of_isThickening {V X_V T₀ Y₀ : Scheme.{u}}
    {fV : X_V ⟶ V} {g₀ : T₀ ⟶ V} {h₀ : Y₀ ⟶ X_V} {e₀ : Y₀ ⟶ T₀}
    (sq₀ : IsPullback h₀ e₀ fV g₀) (F₀ : Sheaf (smallEtaleTopology T₀) Ab.{u + 1}) (r : ℕ)
    (x : GeometricPoint X_V) (ξ : obstructionStalk h₀ e₀ F₀ r x) {Z Z' : Scheme.{u}}
    (i : Z ⟶ Z') (π : Z' ⟶ T₀) (hi : IsThickening i) :
    ObstructionSurvives fV g₀ h₀ e₀ F₀ r x ξ Z (i ≫ π) ↔
      ObstructionSurvives fV g₀ h₀ e₀ F₀ r x ξ Z' π := by
  have := hi.1
  have : UniversalHomeomorphism i :=
    Stacks.Etale.universalHomeomorphism_of_isClosedImmersion_of_surjective i hi.2
  constructor
  · rintro ⟨Y₁, h₁, e₁, g₁, rfl, sq₁, y₁, hy₁, hyh₁, hne⟩
    have sq₂ := IsPullback.of_hasPullback fV (π ≫ g₀)
    have hw₂ : pullback.fst fV (π ≫ g₀) ≫ fV = (pullback.snd fV (π ≫ g₀) ≫ π) ≫ g₀ := by
      rw [sq₂.w, Category.assoc]
    have hy₂ := sq₀.lift_snd _ _ hw₂
    have hyh₂ : pullback.fst fV (π ≫ g₀) ≫ 𝟙 X_V = sq₀.lift _ _ hw₂ ≫ h₀ := by
      rw [Category.comp_id, sq₀.lift_fst]
    have hw₁ : h₁ ≫ fV = (e₁ ≫ i) ≫ π ≫ g₀ := by
      rw [sq₁.w]
      simp only [Category.assoc]
    have hφh : h₁ ≫ 𝟙 X_V = sq₂.lift h₁ (e₁ ≫ i) hw₁ ≫ pullback.fst fV (π ≫ g₀) := by
      rw [Category.comp_id, sq₂.lift_fst]
    have hφe := sq₂.lift_snd h₁ (e₁ ≫ i) hw₁
    have hpb : IsPullback (sq₂.lift h₁ (e₁ ≫ i) hw₁) e₁ (pullback.snd fV (π ≫ g₀)) i :=
      IsPullback.of_right (by rwa [sq₂.lift_fst, ← Category.assoc]) hφe sq₂
    exact ⟨_, _, _, π ≫ g₀, rfl, sq₂, _, hy₂, hyh₂, (obstructionCondition_iff sq₀ x ξ i π h₁ e₁
      sq₁ y₁ hy₁ hyh₁ _ _ sq₂ _ hy₂ hyh₂ _ hφh hφe hpb).1 hne⟩
  · rintro ⟨Y₂, h₂, e₂, g₂, rfl, sq₂, y₂, hy₂, hyh₂, hne⟩
    have hpb := IsPullback.of_hasPullback e₂ i
    have sq₁ : IsPullback (pullback.fst e₂ i ≫ h₂) (pullback.snd e₂ i) fV ((i ≫ π) ≫ g₀) := by
      rw [Category.assoc]
      exact hpb.paste_horiz sq₂
    have hy₁ : (pullback.fst e₂ i ≫ y₂) ≫ e₀ = pullback.snd e₂ i ≫ i ≫ π := by
      rw [Category.assoc, hy₂, ← Category.assoc, pullback.condition, Category.assoc]
    have hyh₁ : (pullback.fst e₂ i ≫ h₂) ≫ 𝟙 X_V = (pullback.fst e₂ i ≫ y₂) ≫ h₀ := by
      rw [Category.assoc, hyh₂, Category.assoc]
    exact ⟨_, _, _, (i ≫ π) ≫ g₀, rfl, sq₁, _, hy₁, hyh₁, (obstructionCondition_iff sq₀ x ξ i π
      _ _ sq₁ _ hy₁ hyh₁ h₂ e₂ sq₂ y₂ hy₂ hyh₂ (pullback.fst e₂ i) (by rw [Category.comp_id])
      pullback.condition hpb).2 hne⟩

/-- A base change map that is not invertible already fails to be invertible after shrinking the
base to some affine `V` over which the base of the sheaf is nonempty. -/
private theorem exists_affine_not_isIso_higherBaseChangeMapAb_app {X' Y S T : Scheme.{u}}
    {f' : X' ⟶ S} {g : T ⟶ S} {h : Y ⟶ X'} {e : Y ⟶ T} (sq : IsPullback h e f' g)
    (F : Sheaf (smallEtaleTopology T) Ab.{u + 1}) (r : ℕ)
    (hni : ¬ IsIso ((higherBaseChangeMapAb f' g h e sq.w r).app F)) :
    ∃ (V X_V T₀ Y₀ : Scheme.{u}) (v : V ⟶ S) (_hV : IsAffine V) (pv : X_V ⟶ X')
      (fV : X_V ⟶ V) (_hpv : IsPullback pv fV f' v) (t₀ : T₀ ⟶ T) (g₀ : T₀ ⟶ V)
      (_hsq : IsPullback t₀ g₀ g v) (h₀ : Y₀ ⟶ X_V) (e₀ : Y₀ ⟶ T₀)
      (sq₀ : IsPullback h₀ e₀ fV g₀) (_hne : Nonempty T₀),
      ¬ IsIso ((higherBaseChangeMapAb fV g₀ h₀ e₀ sq₀.w r).app
        ((smallEtalePullbackAb t₀).obj F)) := by
  by_contra hcon
  refine hni (isIso_higherBaseChangeMapAb_app_of_forall_isAffine f' g h e sq F r ?_)
  intro V X_V T₀ Y₀ v _ hV pv fV hpv t₀ g₀ hsq h₀ e₀ sq₀ hne
  by_contra hiso
  exact hcon ⟨V, X_V, T₀, Y₀, v, hV, pv, fV, hpv, t₀, g₀, hsq, h₀, e₀, sq₀, hne, hiso⟩

/-- **Stacks Project, Tag 0F07.** With `f : X ⟶ S` and `n` as in [Stacks, Tag 0F02], assume
`BC(f, n, q)` holds and `BC(f, n, q + 1)` does not. Then there are a commutative diagram

```
X  ←--  X'  ←-h-  Y
|f      |f'       |e
S  ←--  S'  ←-g-  Spec K
```

with `X' = X ×_S S'`, `Y = X' ×_{S'} Spec K`, `S'` affine and `K` a field, and an abelian sheaf
`F` on the small étale site of `Spec K` annihilated by `n`, such that
`(f')⁻¹ R^{q+1} g_* F ⟶ R^{q+1} h_* e⁻¹ F` is not an isomorphism.

The source's *"we may and do replace `S'` by an affine open of `S'`"* is
`Stacks.EtaleCohomology.isIso_higherBaseChangeMapAb_app_of_forall_isAffine`. The dévissage
`AlgebraicGeometry.exists_field_point_of_isDirected` of [Stacks, Tag 0F06] is applied to the
source's property `P`, which is `Stacks.EtaleCohomology.ObstructionSurvives`; its three
hypotheses are `Stacks.EtaleCohomology.obstructionSurvives_iff_of_isThickening`,
`Stacks.EtaleCohomology.obstructionSurvives_of_isLimit` and
`Stacks.EtaleCohomology.obstructionSurvives_open_or_closed`.

Proved here: that the failure of `BC(f, n, q + 1)` under `BC(f, n, q)` is a failure in degree
exactly `q + 1`, that the shrunk base is quasi-compact and quasi-separated, the choice of the
obstruction class and that `P` holds at the base, that `P` at a field-valued point is a failure
of base change, and that the sheaf the dévissage returns is annihilated by `n`. -/
@[stacks 0F07]
public theorem exists_affine_field_not_isIso_higherBaseChangeMapAb {X S : Scheme.{u}} (f : X ⟶ S)
    (n : ℤ) (q : ℕ) (hprev : BaseChangeHolds f n (q : ℤ))
    (hfail : ¬ BaseChangeHolds f n ((q : ℤ) + 1)) :
    ∃ (S' X' Y : Scheme.{u}) (_ : IsAffine S') (s : S' ⟶ S) (p : X' ⟶ X) (f' : X' ⟶ S')
      (_hp : IsPullback p f' f s) (K : Type u) (_ : Field K) (g : Spec (.of K) ⟶ S')
      (h : Y ⟶ X') (e : Y ⟶ Spec (.of K)) (sq : IsPullback h e f' g)
      (F : Sheaf (smallEtaleTopology (Spec (.of K))) Ab.{u + 1}),
      (∀ (U : (Spec (.of K)).Etale) (x : F.obj.obj (op U)), n • x = 0) ∧
        ¬ IsIso ((higherBaseChangeMapAb f' g h e sq.w (q + 1)).app F) := by
  classical
  obtain ⟨S', X', T, Y, s, p, f', hp, g, h, e, sq, hqc, hqs, F, hF, hni⟩ :=
    exists_not_isIso_higherBaseChangeMapAb_succ f n q hprev hfail
  obtain ⟨V, X_V, T₀, Y₀, v, hV, pv, fV, hpv, t₀, g₀, hsq, h₀, e₀, sq₀, hne, hfail₀⟩ :=
    exists_affine_not_isIso_higherBaseChangeMapAb_app sq F (q + 1) hni
  have hqc₀ : QuasiCompact g₀ :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @QuasiCompact) hsq hqc
  have hqs₀ : QuasiSeparated g₀ :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @QuasiSeparated) hsq hqs
  have : CompactSpace T₀ := QuasiCompact.compactSpace_of_compactSpace g₀
  have : QuasiSeparatedSpace T₀ := quasiSeparatedSpace_of_quasiSeparated g₀
  -- `X_V = X ×_S V`, by pasting the two cartesian squares over `S'`.
  have hpaste : IsPullback (pv ≫ p) fV f (v ≫ s) := hpv.paste_horiz hp
  -- Pullback preserves being annihilated by `n`.
  have hann : ∀ {T T' : Scheme.{u}} (t : T ⟶ T') (G : Sheaf (smallEtaleTopology T') Ab.{u + 1}),
      (∀ (U : T'.Etale) (x : G.obj.obj (op U)), n • x = 0) →
        ∀ (U : T.Etale) (x : ((smallEtalePullbackAb t).obj G).obj.obj (op U)), n • x = 0 :=
    fun t G hG U ↦ zsmul_eq_zero_of_additive (smallEtalePullbackAb t) G n
      (fun W ↦ hG W.unop) (op U)
  -- The sheaf `F₀ = t₀⁻¹F` on the shrunk base, annihilated by `n`.
  set F₀ := (smallEtalePullbackAb t₀).obj F
  have hF₀ := hann t₀ F hF
  -- The obstruction class: a class in a stalk of the target missing the image of the base change
  -- map, which is injective by part (1) of [Stacks, Tag 0F03].
  obtain ⟨x, ξ, hP₀⟩ := exists_obstructionSurvives_self fV g₀ h₀ e₀ sq₀ F₀ (q + 1)
    (mono_higherBaseChangeMapAb_app_of_annihilated f n q (v ≫ s) (pv ≫ p) fV g₀ h₀ e₀ hprev
      hpaste sq₀ (hann _ _ hF₀)) hfail₀
  -- The dévissage of 0F06, applied to the property `ObstructionSurvives`.
  obtain ⟨K, hK, gK, hPK⟩ := exists_field_point_of_isDirected
    (ObstructionSurvives fV g₀ h₀ e₀ F₀ (q + 1) x ξ)
    (fun i f hi ↦ obstructionSurvives_iff_of_isThickening sq₀ F₀ (q + 1) x ξ i f hi)
    (by
      intro I _ _ _ D _ _ _ c hc _ _ π πi hπi hπ hP
      exact obstructionSurvives_of_isLimit sq₀ F₀ (q + 1) x ξ D c hc π πi hπi hπ hP)
    (fun π J _ _ O hO _ _ hP ↦ obstructionSurvives_open_or_closed hprev hpaste hF₀ π J O hO hP)
    hP₀
  obtain ⟨Y', h', e', g', _hg', sq', hni'⟩ := not_isIso_of_obstructionSurvives hPK
  exact ⟨V, X_V, Y', hV, v ≫ s, pv ≫ p, fV, hpaste, K, hK, g', h', e', sq',
    (smallEtalePullbackAb gK).obj F₀, hann gK F₀ hF₀, hni'⟩

end Stacks.EtaleCohomology

end
