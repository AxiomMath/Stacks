module

public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizingComplexBaseChange
public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizingComplexAffineChart
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.PseudoCoherentThree.TorIndependenceAtPoints
public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.ClosedImmersionBaseChangeTorIndependent
public import StacksFrontier.AlgebraicGeometry.Perfect.DerivedStalk.ClosedImmersionPushforward
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.UnitComparison
public import StacksFrontier.AlgebraicGeometry.Intersection.ProductTorIndependence

/-!
# The diagonal square of a base change

Consider a cartesian square of schemes `X' = X ×_S S'` with `g' : X' ⟶ X`, `f' : X' ⟶ S'`, and
`f : X ⟶ S` flat. Let `W ⊆ X ×_S X` and `W' ⊆ X' ×_{S'} X'` be opens through which the relative
diagonals factor as closed immersions `Δ`, `Δ'`, and let `w : W' ⟶ W` be the restriction of
`g' × g'`. Then the square

```
X' --Δ'--> W'
|          |
g'         w
v          v
X  --Δ---> W
```

is cartesian, and `X`, `W'` are Tor independent over `W` (Stacks 0CTA, at the diagonal). Hence
Tor-independent base change along the closed immersion `Δ` (Stacks 0E23) identifies
`Lw^*(Δ_*𝒪_X)` with `Δ'_*𝒪_{X'}`. This is the identification of the proof of Stacks 0E2Y.

## Main definitions

* `AlgebraicGeometry.Scheme.Hom.pullbackMapOfIsPullback`: `g' × g' : X' ×_{S'} X' ⟶ X ×_S X`.
* `AlgebraicGeometry.Scheme.Hom.DiagonalOpen.baseChangeDiagonalIso`: `Lw^*(Δ_*𝒪_X) ≅ Δ'_*𝒪_{X'}`.

## Main results

* `AlgebraicGeometry.Scheme.Hom.DiagonalOpen.isPullback_diag_baseChange`: the square above is
  cartesian.
* `AlgebraicGeometry.Scheme.Hom.DiagonalOpen.torIndependent_diag_baseChange`: `Δ` and `w` are Tor
  independent.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPullback derivedPushforward)

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {X S S' X' : Scheme.{u}} {f : X ⟶ S} {g : S' ⟶ S} {g' : X' ⟶ X} {f' : X' ⟶ S'}

/-- `g' × g' : X' ×_{S'} X' ⟶ X ×_S X` for a commutative square `g' ≫ f = f' ≫ g`. -/
abbrev pullbackMapOfIsPullback (hpb : IsPullback g' f' f g) : pullback f' f' ⟶ pullback f f :=
  pullback.map f' f' f f g' g' g hpb.w.symm hpb.w.symm

/-- `g' × g'` followed by the first projection of `X ×_S X` is the first projection of
`X' ×_{S'} X'` followed by `g'`. -/
@[reassoc (attr := simp)]
theorem pullbackMapOfIsPullback_fst (hpb : IsPullback g' f' f g) :
    pullbackMapOfIsPullback hpb ≫ pullback.fst f f = pullback.fst f' f' ≫ g' :=
  pullback.lift_fst _ _ _

/-- `g' × g'` followed by the second projection of `X ×_S X` is the second projection of
`X' ×_{S'} X'` followed by `g'`. -/
@[reassoc (attr := simp)]
theorem pullbackMapOfIsPullback_snd (hpb : IsPullback g' f' f g) :
    pullbackMapOfIsPullback hpb ≫ pullback.snd f f = pullback.snd f' f' ≫ g' :=
  pullback.lift_snd _ _ _

/-- The relative diagonal of `f'` followed by `g' × g'` is `g'` followed by the relative diagonal
of `f`. -/
theorem diagonal_comp_pullbackMapOfIsPullback (hpb : IsPullback g' f' f g) :
    pullback.diagonal f' ≫ pullbackMapOfIsPullback hpb = g' ≫ pullback.diagonal f := by
  apply pullback.hom_ext <;> simp

/-- The identification `X' ×_{S'} X' ≅ (X ×_S S') ×_{S'} (X ×_S S')` carried by the cartesian
square. -/
def pullbackIsoOfIsPullback (hpb : IsPullback g' f' f g) :
    pullback f' f' ≅ pullback (pullback.snd f g) (pullback.snd f g) :=
  haveI : IsIso (pullback.map f' f' (pullback.snd f g) (pullback.snd f g) hpb.isoPullback.hom
      hpb.isoPullback.hom (𝟙 S') (by simp) (by simp)) := inferInstance
  asIso (pullback.map f' f' (pullback.snd f g) (pullback.snd f g) hpb.isoPullback.hom
    hpb.isoPullback.hom (𝟙 S') (by simp) (by simp))

/-- Under the identification `pullbackIsoOfIsPullback`, the map `diagonalBaseChangeMap f g` is
`g' × g'`. -/
theorem pullbackIsoOfIsPullback_hom_comp (hpb : IsPullback g' f' f g) :
    (pullbackIsoOfIsPullback hpb).hom ≫ diagonalBaseChangeMap f g =
      pullbackMapOfIsPullback hpb := by
  apply pullback.hom_ext
  · simp only [pullbackIsoOfIsPullback, asIso_hom, Category.assoc, pullbackMapOfIsPullback_fst]
    rw [diagonalBaseChangeMap, pullback.lift_fst, ← Category.assoc, pullback.lift_fst,
      Category.assoc, IsPullback.isoPullback_hom_fst]
  · simp only [pullbackIsoOfIsPullback, asIso_hom, Category.assoc, pullbackMapOfIsPullback_snd]
    rw [diagonalBaseChangeMap, pullback.lift_snd, ← Category.assoc, pullback.lift_snd,
      Category.assoc, IsPullback.isoPullback_hom_fst]

/-- **Stacks 0CTA at the diagonal square of a cartesian square.** For `f` flat, `g' × g'` and the
relative diagonal of `f` are Tor independent over `X ×_S X`. -/
theorem torIndependent_pullbackMapOfIsPullback [Flat f] (hpb : IsPullback g' f' f g) :
    TorIndependent (pullbackMapOfIsPullback hpb) (pullback.diagonal f) := by
  rw [← pullbackIsoOfIsPullback_hom_comp hpb]
  exact TorIndependent.iso_left (pullbackIsoOfIsPullback hpb)
    (torIndependent_diagonalBaseChangeMap f g)

namespace DiagonalOpen

variable (hpb : IsPullback g' f' f g) (D : DiagonalOpen f) (D' : DiagonalOpen f')
  (w : D'.W ⟶ D.W) (hw : w ≫ D.ι = D'.ι ≫ pullbackMapOfIsPullback hpb)

attribute [local instance] DiagonalOpen.isOpenImmersion DiagonalOpen.isClosedImmersion

/-- The diagonal `Y ⟶ W` followed by the first projection `W ⟶ Y` is the identity. -/
@[reassoc (attr := simp)]
theorem diag_ι_fst {Y T : Scheme.{u}} {h : Y ⟶ T} (E : DiagonalOpen h) :
    E.diag ≫ E.ι ≫ pullback.fst h h = 𝟙 Y := by
  rw [← Category.assoc, E.fac, pullback.diagonal_fst]

/-- The diagonal `Y ⟶ W` followed by the second projection `W ⟶ Y` is the identity. -/
@[reassoc (attr := simp)]
theorem diag_ι_snd {Y T : Scheme.{u}} {h : Y ⟶ T} (E : DiagonalOpen h) :
    E.diag ≫ E.ι ≫ pullback.snd h h = 𝟙 Y := by
  rw [← Category.assoc, E.fac, pullback.diagonal_snd]

include hw in
/-- `Δ' ≫ w = g' ≫ Δ`. -/
theorem diag_comp_baseChange : D'.diag ≫ w = g' ≫ D.diag := by
  rw [← cancel_mono D.ι, Category.assoc, hw, ← Category.assoc, D'.fac, Category.assoc, D.fac,
    diagonal_comp_pullbackMapOfIsPullback]

include hw in
/-- `w` is compatible with the first projections: `w ≫ pr₁|_W = pr₁|_{W'} ≫ g'`. -/
theorem proj_baseChange : w ≫ D.proj = D'.proj ≫ g' := by
  simp only [proj, ← Category.assoc, hw]
  simp

include hw in
/-- **The diagonal square of a base change is cartesian.** -/
theorem isPullback_diag_baseChange : IsPullback D'.diag g' w D.diag := by
  have h₁ : ∀ s : PullbackCone w D.diag, s.fst ≫ D'.ι ≫ pullback.fst f' f' ≫ g' = s.snd := by
    intro s
    have := congrArg (· ≫ D.ι ≫ pullback.fst f f) s.condition
    simp only [Category.assoc, reassoc_of% hw] at this
    simpa using this
  refine ⟨⟨diag_comp_baseChange hpb D D' w hw⟩, ⟨PullbackCone.IsLimit.mk _ (fun s => ?_)
    (fun s => ?_) (fun s => ?_) (fun s m hm _ => ?_)⟩⟩
  · exact s.fst ≫ D'.ι ≫ pullback.fst f' f'
  · -- `s.fst ≫ D'.ι` is the diagonal of its first component
    have h₂ : s.fst ≫ D'.ι ≫ pullback.snd f' f' ≫ g' = s.snd := by
      have := congrArg (· ≫ D.ι ≫ pullback.snd f f) s.condition
      simp only [Category.assoc, reassoc_of% hw] at this
      simpa using this
    have heq : s.fst ≫ D'.ι ≫ pullback.fst f' f' = s.fst ≫ D'.ι ≫ pullback.snd f' f' := by
      apply hpb.hom_ext
      · rw [Category.assoc, Category.assoc, h₁ s, Category.assoc, Category.assoc, h₂]
      · simp only [Category.assoc]
        rw [pullback.condition]
    rw [← cancel_mono D'.ι, Category.assoc, D'.fac]
    apply pullback.hom_ext
    · simp
    · simp [heq]
  · exact h₁ s
  · have := congrArg (· ≫ D'.ι ≫ pullback.fst f' f') hm
    simp only [Category.assoc] at this
    simpa using this

include hw in
/-- **`X` and `W'` are Tor independent over `W`** (Stacks 0CTA at the diagonal). -/
theorem torIndependent_diag_baseChange [Flat f] : TorIndependent D.diag w := by
  have H := (torIndependent_pullbackMapOfIsPullback hpb).symm
  rw [torIndependent_iff_forall_torIndependentAt] at H ⊢
  intro x y h
  have ha : 𝟙 X ≫ pullback.diagonal f = D.diag ≫ D.ι := by rw [Category.id_comp, D.fac]
  have hb : D'.ι ≫ pullbackMapOfIsPullback hpb = w ≫ D.ι := hw.symm
  have h₁ : (pullback.diagonal f).base ((𝟙 X : X ⟶ X).base x) =
      (pullbackMapOfIsPullback hpb).base (D'.ι.base y) := by
    have e₁ := congrArg (fun k : X ⟶ pullback f f => k.base x) ha
    have e₂ := congrArg (fun k : D'.W ⟶ pullback f f => k.base y) hb
    simp only [Scheme.Hom.comp_base, TopCat.comp_app] at e₁ e₂
    rw [e₁, e₂, h]
  exact (torIndependentAt_iff_of_isIso_stalkMap (𝟙 X) D'.ι D.ι ha hb h h₁).1 (H _ _ h₁)

section Derived

attribute [local instance 10000] HasDerivedCategory.standard

/-- `Δ_*𝒪_X` is the derived direct image of `𝒪_X[0]` along the closed immersion `Δ`. -/
def diagonalObjectIsoDerivedPushforward {Y T : Scheme.{u}} {h : Y ⟶ T} (E : DiagonalOpen h) :
    E.diagonalObject ≅ (derivedPushforward E.diag.toLRSHom.toShHom).obj (structureSingle Y) :=
  E.diagonalObjectIso ≪≫
    ((Stacks.ClosedImmersion.derivedPushforwardIsoMapDerivedCategoryOfSchemes E.diag).app _).symm

/-- **The derived base change of the diagonal object** (proof of Stacks 0E2Y):
`Lw^*(Δ_*𝒪_X) ≅ Δ'_*𝒪_{X'}`, by Tor-independent base change along the closed immersion `Δ`
(Stacks 0E23) at the cartesian square `isPullback_diag_baseChange`, whose Tor independence is
Stacks 0CTA, followed by `L(g')^*𝒪_X ≅ 𝒪_{X'}`. -/
def baseChangeDiagonalIso [Flat f] :
    (derivedPullback w.toLRSHom.toShHom).obj D.diagonalObject ≅ D'.diagonalObject :=
  (derivedPullback w.toLRSHom.toShHom).mapIso D.diagonalObjectIsoDerivedPushforward ≪≫
    (Stacks.Cohomology.ClosedImmersionBaseChange.derivedBaseChangeSquareIso
      (isPullback_diag_baseChange hpb D D' w hw)
      (torIndependent_diag_baseChange hpb D D' w hw)).app (structureSingle X) ≪≫
    (derivedPushforward D'.diag.toLRSHom.toShHom).mapIso
      (Stacks.Cohomology.DerivedPullbackUnit.derivedPullbackUnitIso g'.toLRSHom.toShHom) ≪≫
    D'.diagonalObjectIsoDerivedPushforward.symm

end Derived

end DiagonalOpen

end AlgebraicGeometry.Scheme.Hom

end
