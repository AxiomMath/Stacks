module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.IntegralSquareLimitSetup
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.LimitBaseChangeHigherDirectImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.PullbackSystemCohomologyColimit
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmoothBaseChange.SmoothLimitBaseChangeReduction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.SmallEtaleDerivedIdentity
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedGeometricStalkSections

/-!
# Base change for the product square of an open, passed to a limit of the base

Let `X' = lim_i X_i` be a directed inverse limit of schemes with affine transition morphisms,
the `X_i` mapping compatibly to a scheme `X` by `π_i`, so that `x' : X' ⟶ X` is the common
composite. Let `ιU : U ⟶ X` be a morphism (in the application an open immersion), `k : X ⟶ B₀`
and `y : Y ⟶ B₀` two morphisms (in the application `B₀ = Spec K`, and `Y` and `X` are schemes
over the field `K`). Put

* `U_i = X_i ×_X U`, with projection `j_i : U_i ⟶ X_i`;
* `X_i ×_{B₀} Y` with projection `q_i` to `X_i`, and `U_i ×_{B₀} Y` with projection `p_i` to
  `U_i` and the map `h_i : U_i ×_{B₀} Y ⟶ X_i ×_{B₀} Y` induced by `j_i`.

These form an inverse system of cartesian squares
```
X_i ×_{B₀} Y  <--h_i--  U_i ×_{B₀} Y
     |q_i                   |p_i
     X_i      <--j_i--      U_i
```
whose limit is the corresponding square for `X'` and `U' = X' ×_X U`. This is the setup of the
step of the proof of [Stacks, Tag 0F1H] which writes `X' = Spec(𝒪^{sh}_{X,x})` as a limit of
schemes `X_i` of smaller dimension, chooses opens `U_i ⊆ X_i` with limit `U'`, applies the
induction hypothesis to the squares of the `X_i` and concludes by [Stacks, Tag 0EZT]. Here the
`U_i` are the inverse images of `U` along the maps `X_i ⟶ X`, so they restrict to `U'` at every
level and not only for `i` large.

This file proves the last step: if the base change maps `q_i^{-1}R^n j_{i,*}𝓕_i ⟶
R^n h_{i,*}p_i^{-1}𝓕_i` of the levels are isomorphisms for the inverse images `𝓕_i` of an abelian
sheaf `𝓕` on `U`, so is the base change map of the limit square at the inverse image of `𝓕` to
`U'`. It is [Stacks, Tag 0EZT] (2), `isIso_higherBaseChangeMapAb_of_isLimit`, for these systems.

## Main definitions

* `Stacks.EtaleCohomology.OpenProductLimit.openLevels` — the system `U_i = X_i ×_X U`.
* `Stacks.EtaleCohomology.OpenProductLimit.productLevels` — the system `X_i ×_{B₀} Y`.
* `Stacks.EtaleCohomology.OpenProductLimit.openProductLevels` — the system `U_i ×_{B₀} Y`.
* `Stacks.EtaleCohomology.OpenProductLimit.openProductLevelsInclusion` — the maps `h_i`.

## Main results

* `Stacks.EtaleCohomology.OpenProductLimit.isPullback_level` — the squares of the levels are
  cartesian.
* `Stacks.EtaleCohomology.OpenProductLimit.isIso_higherBaseChangeMapAb_limit_of_levels` — the
  passage to the limit described above.
* `Stacks.EtaleCohomology.OpenProductLimit.isIso_higherBaseChangeMapAb_of_isLimit_of_fixedBase` —
  [Stacks, Tag 0EZT] (2) for an inverse system of squares over a fixed bottom row and one sheaf.
* `Stacks.EtaleCohomology.OpenProductLimit.isIso_higherBaseChangeMapAb_limit_of_factorLevels` —
  the same passage to the limit in the other factor: `Y' = lim Y_i` over `B₀`, and the squares
  `Y_i ×_{B₀} X ⟵ Y_i ×_{B₀} U` over the fixed `X ⟵ U`. This is the step of the proof of
  [Stacks, Tag 0F1H] for a point `z ↦ y ∈ Y` with `trdeg_K κ(y) > 0`.

## Implementation notes

The morphism `ιU : U ⟶ X` is arbitrary (quasi-compact and quasi-separated where the limit is
taken), so that the results apply to any open immersion and not only to the inclusion of an open
subscheme. The square on the limit is given by arbitrary cartesian squares (`IsPullback`), not by
chosen fibre products, so that it can be matched with any presentation of `U'`, `X' ×_{B₀} Y` and
`U' ×_{B₀} Y`. The levels are the chosen fibre products of
`Stacks.EtaleCohomology.baseChangeDiagram`.

Over a fixed bottom row the direct-image leg of the `i`-th square is written
`((Functor.const Iᵒᵖ).map j).app i`, which is `j` by definition, exactly as
`isIso_higherBaseChangeMapAb_of_isLimit` sees it. Restating the hypothesis with `j` itself would
force the elaborator and the kernel to identify the two spellings inside
`higherBaseChangeMapAb`, which they do not manage within the heartbeat budget. A caller
instantiates a statement quantified over squares at these legs, as
`Stacks.EtaleCohomology.isIso_higherBaseChangeMapAb_of_smoothLimit` does.

## References

* [Stacks Project, Tag 0F1H](https://stacks.math.columbia.edu/tag/0F1H)
* [Stacks Project, Tag 0EZT](https://stacks.math.columbia.edu/tag/0EZT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology.OpenProductLimit

variable {I : Type u} [Preorder I] {X B₀ Y : Scheme.{u}} (D : Iᵒᵖ ⥤ Scheme.{u})
  (π : D ⟶ (Functor.const Iᵒᵖ).obj X) {U : Scheme.{u}} (ιU : U ⟶ X) (k : X ⟶ B₀) (y : Y ⟶ B₀)

/-- The system `U_i = X_i ×_X U` of the levels. -/
abbrev openLevels : Iᵒᵖ ⥤ Scheme.{u} := baseChangeDiagram D π ιU

/-- The projections `j_i : U_i ⟶ X_i`, open immersions when `ιU` is one. -/
abbrev openLevelsInclusion : openLevels D π ιU ⟶ D := baseChangeHorizontal D π ιU

/-- The maps `U_i ⟶ U`. -/
abbrev openLevelsToOpen : openLevels D π ιU ⟶ (Functor.const Iᵒᵖ).obj U :=
  baseChangeStructureMap D π ιU

/-- The system of products `X_i ×_{B₀} Y`. -/
abbrev productLevels : Iᵒᵖ ⥤ Scheme.{u} :=
  baseChangeDiagram D (π ≫ (Functor.const Iᵒᵖ).map k) y

/-- The projections `q_i : X_i ×_{B₀} Y ⟶ X_i`. -/
abbrev productLevelsProjection : productLevels D π k y ⟶ D :=
  baseChangeHorizontal D (π ≫ (Functor.const Iᵒᵖ).map k) y

/-- The system of products `U_i ×_{B₀} Y`. -/
abbrev openProductLevels : Iᵒᵖ ⥤ Scheme.{u} :=
  baseChangeDiagram (openLevels D π ιU)
    (openLevelsInclusion D π ιU ≫ π ≫ (Functor.const Iᵒᵖ).map k) y

/-- The projections `p_i : U_i ×_{B₀} Y ⟶ U_i`. -/
abbrev openProductLevelsProjection : openProductLevels D π ιU k y ⟶ openLevels D π ιU :=
  baseChangeHorizontal (openLevels D π ιU)
    (openLevelsInclusion D π ιU ≫ π ≫ (Functor.const Iᵒᵖ).map k) y

/-- The maps `h_i : U_i ×_{B₀} Y ⟶ X_i ×_{B₀} Y` induced by the inclusions `j_i`. -/
def openProductLevelsInclusion : openProductLevels D π ιU k y ⟶ productLevels D π k y where
  app i := pullback.lift (pullback.fst _ _ ≫ (openLevelsInclusion D π ιU).app i)
    (pullback.snd _ _) ((Category.assoc _ _ _).trans pullback.condition)
  naturality i j a := by
    refine pullback.hom_ext ?_ ?_
    · simp only [Category.assoc, pullback.lift_fst,
        pullback.lift_fst_assoc]
      congr 1
      exact (openLevelsInclusion D π ιU).naturality a
    · simp only [Category.assoc, pullback.lift_snd]

/-- `h_i` followed by `q_i : X_i ×_{B₀} Y ⟶ X_i` equals `p_i` followed by `j_i : U_i ⟶ X_i`. -/
@[reassoc (attr := simp)]
theorem openProductLevelsInclusion_app_fst (i : Iᵒᵖ) :
    (openProductLevelsInclusion D π ιU k y).app i ≫ (productLevelsProjection D π k y).app i =
      (openProductLevelsProjection D π ιU k y).app i ≫ (openLevelsInclusion D π ιU).app i :=
  pullback.lift_fst _ _ _

/-- `h_i` commutes with the projections of `U_i ×_{B₀} Y` and `X_i ×_{B₀} Y` to `Y`. -/
@[reassoc (attr := simp)]
theorem openProductLevelsInclusion_app_snd (i : Iᵒᵖ) :
    (openProductLevelsInclusion D π ιU k y).app i ≫
        (baseChangeStructureMap D (π ≫ (Functor.const Iᵒᵖ).map k) y).app i =
      (baseChangeStructureMap (openLevels D π ιU)
        (openLevelsInclusion D π ιU ≫ π ≫ (Functor.const Iᵒᵖ).map k) y).app i :=
  pullback.lift_snd _ _ _

/-- **The squares of the levels are cartesian.** `U_i ×_{B₀} Y` is the fibre product of
`X_i ×_{B₀} Y` and `U_i` over `X_i`: this is the left half of the pasting of the two product
squares over `B₀`. -/
theorem isPullback_level (i : Iᵒᵖ) :
    IsPullback ((openProductLevelsInclusion D π ιU k y).app i)
      ((openProductLevelsProjection D π ιU k y).app i) ((productLevelsProjection D π k y).app i)
      ((openLevelsInclusion D π ιU).app i) := by
  refine IsPullback.of_right (h₁₂ := pullback.snd _ y) (h₂₂ := π.app i ≫ k) (v₁₃ := y) ?_
    (openProductLevelsInclusion_app_fst D π ιU k y i) (IsPullback.of_hasPullback _ y).flip
  rw [show (openProductLevelsInclusion D π ιU k y).app i ≫ pullback.snd _ y =
      pullback.snd _ y from pullback.lift_snd _ _ _]
  exact (IsPullback.of_hasPullback _ y).flip

/-- The projections `j_i : U_i ⟶ X_i` are open immersions when `ιU` is one. -/
instance isOpenImmersion_openLevelsInclusion_app [IsOpenImmersion ιU] (i : Iᵒᵖ) :
    IsOpenImmersion ((openLevelsInclusion D π ιU).app i) :=
  inferInstanceAs (IsOpenImmersion (pullback.fst (π.app i) ιU))

/-- The projections `j_i : U_i ⟶ X_i` are quasi-compact when `ιU` is. -/
instance quasiCompact_openLevelsInclusion_app [QuasiCompact ιU] (i : Iᵒᵖ) :
    QuasiCompact ((openLevelsInclusion D π ιU).app i) :=
  inferInstanceAs (QuasiCompact (pullback.fst (π.app i) ιU))

/-- The projections `j_i : U_i ⟶ X_i` are quasi-separated when `ιU` is. -/
instance quasiSeparated_openLevelsInclusion_app [QuasiSeparated ιU] (i : Iᵒᵖ) :
    QuasiSeparated ((openLevelsInclusion D π ιU).app i) :=
  inferInstanceAs (QuasiSeparated (pullback.fst (π.app i) ιU))

/-- The cone from a cartesian square over the limit cone `p` to the base change of the system
`E` along `g` is a limit cone. -/
private def isLimitBaseChangeProjection {J : Type u} [Category J] [IsConnected J]
    {S T W W' : Scheme.{u}} (E : J ⥤ Scheme.{u}) (st : E ⟶ (Functor.const J).obj S) (g : T ⟶ S)
    {p : (Functor.const J).obj W ⟶ E} (g' : W' ⟶ W) (f' : W' ⟶ T) {f : W ⟶ S}
    (hsq : IsPullback g' f' f g) (hp : ∀ i, p.app i ≫ st.app i = f) (hW : IsLimit (Cone.mk W p)) :
    IsLimit (Cone.mk W' (baseChangeProjection E st g p g' f'
      (fun i => by rw [Category.assoc, hp i, hsq.w]))) :=
  isLimit_of_isPullback_stages (isPullback_baseChangeStage E st g) hsq hp
    (baseChangeProjection_comp_structureMap E st g p g' f' _)
    (baseChangeProjection_comp_horizontal E st g p g' f' _) hW

section Limit

variable [IsDirected I (· ≤ ·)] [Nonempty I]
  [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (D.map a)]

open LimitBaseChange LimitHigherDirectImage SmallEtaleLimitCohomology in
/-- **Base change for the product square of an open passes to the limit of the base.** Let
`X' = lim X_i` (the cone `p`, a limit), with affine transitions, the levels mapping to `X` by
`π_i` with common composite `x'`, and let `ιU : U ⟶ X` be quasi-compact and quasi-separated. Let
`U' = X' ×_X U` (any cartesian square `jU, u'`), `X' ×_{B₀} Y` (any cartesian square `f', r`
over `x' ≫ k` and `y`) and `U' ×_{B₀} Y` (any cartesian square `e', r'` over `jU ≫ x' ≫ k` and
`y`), with `h' : U' ×_{B₀} Y ⟶ X' ×_{B₀} Y` over `jU` and `Y`. Let `𝓕` be an abelian sheaf on
`U`. If for every `i` the base change map of the square of the `i`-th level
`q_i^{-1}R^n j_{i,*}(𝓕|U_i) ⟶ R^n h_{i,*}p_i^{-1}(𝓕|U_i)` is an isomorphism, then so is the base
change map `f'^{-1}R^n jU_*(𝓕|U') ⟶ R^n h'_*e'^{-1}(𝓕|U')` of the limit square.

This is [Stacks, Tag 0EZT] (2) (`isIso_higherBaseChangeMapAb_of_isLimit`) for the systems of
`Stacks.EtaleCohomology.OpenProductLimit`; the limits of the three systems other than `X_i` are
the base changes of `X' = lim X_i` (`Stacks.EtaleCohomology.isLimit_of_isPullback_stages`), and
the system of sheaves is the system of inverse images of `𝓕`, presented on `U'` by the inverse
image of `𝓕` (`isColimitPresentation_pullbackSystem`). -/
theorem isIso_higherBaseChangeMapAb_limit_of_levels [QuasiCompact ιU] [QuasiSeparated ιU]
    {X' : Scheme.{u}} (p : (Functor.const Iᵒᵖ).obj X' ⟶ D) (hp : IsLimit (Cone.mk X' p))
    (x' : X' ⟶ X) (hx' : ∀ i, p.app i ≫ π.app i = x')
    {U' : Scheme.{u}} (jU : U' ⟶ X') (u' : U' ⟶ U) (hU : IsPullback jU u' x' ιU)
    {P' : Scheme.{u}} (f' : P' ⟶ X') (r : P' ⟶ Y) (hP : IsPullback f' r (x' ≫ k) y)
    {Q' : Scheme.{u}} (e' : Q' ⟶ U') (r' : Q' ⟶ Y) (hQ : IsPullback e' r' (jU ≫ x' ≫ k) y)
    (h' : Q' ⟶ P') (hh' : h' ≫ f' = e' ≫ jU) (hh'r : h' ≫ r = r') (n : ℕ)
    (𝓕 : Sheaf (smallEtaleTopology U) Ab.{u + 1})
    (hlevel : ∀ i : Iᵒᵖ, IsIso ((higherBaseChangeMapAb ((productLevelsProjection D π k y).app i)
      ((openLevelsInclusion D π ιU).app i) ((openProductLevelsInclusion D π ιU k y).app i)
      ((openProductLevelsProjection D π ιU k y).app i) (isPullback_level D π ιU k y i).w n).app
        ((etaleAbelianInverseImage.{u, u + 1} ((openLevelsToOpen D π ιU).app i)).obj 𝓕))) :
    IsIso ((higherBaseChangeMapAb f' jU h' e' hh' n).app
      ((etaleAbelianInverseImage.{u, u + 1} u').obj 𝓕)) := by
  have : IsConnected Iᵒᵖ := IsCofiltered.isConnected _
  have : ∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom ((openLevels D π ιU).map a) :=
    fun a => isAffineHom_baseChangeDiagram_map D π ιU a
  have : ∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom ((productLevels D π k y).map a) :=
    fun a => isAffineHom_baseChangeDiagram_map D _ y a
  have : ∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom ((openProductLevels D π ιU k y).map a) :=
    fun a => isAffineHom_baseChangeDiagram_map (openLevels D π ιU) _ y a
  have hwT : ∀ i, (jU ≫ p.app i) ≫ π.app i = u' ≫ ιU := fun i => by
    rw [Category.assoc, hx' i, hU.w]
  let pT := baseChangeProjection D π ιU p jU u' hwT
  have hT : IsLimit (Cone.mk U' pT) := isLimitBaseChangeProjection D π ιU jU u' hU hx' hp
  have hwX : ∀ i, (f' ≫ p.app i) ≫ (π.app i ≫ k) = r ≫ y := fun i => by
    rw [Category.assoc, ← Category.assoc (p.app i), hx' i, hP.w]
  let pX := baseChangeProjection D (π ≫ (Functor.const Iᵒᵖ).map k) y p f' r hwX
  have hX : IsLimit (Cone.mk P' pX) :=
    isLimitBaseChangeProjection D _ y f' r hP
      (fun i => by
        change p.app i ≫ π.app i ≫ k = x' ≫ k
        rw [← Category.assoc, hx' i]) hp
  have hpT : ∀ i, pT.app i ≫ (openLevelsInclusion D π ιU).app i ≫ π.app i ≫ k = jU ≫ x' ≫ k :=
    fun i => by
      rw [← Category.assoc, baseChangeProjection_comp_horizontal, Category.assoc,
        ← Category.assoc (p.app i), hx' i]
  have hwY : ∀ i, (e' ≫ pT.app i) ≫ ((openLevelsInclusion D π ιU).app i ≫ π.app i ≫ k) =
      r' ≫ y := fun i => by
    rw [Category.assoc, hpT i, hQ.w]
  let pY := baseChangeProjection (openLevels D π ιU)
    (openLevelsInclusion D π ιU ≫ π ≫ (Functor.const Iᵒᵖ).map k) y pT e' r' hwY
  have hY : IsLimit (Cone.mk Q' pY) :=
    isLimitBaseChangeProjection (openLevels D π ιU) _ y e' r' hQ hpT hT
  have hs : ∀ {i j : Iᵒᵖ} (a : i ⟶ j), (openLevelsToOpen D π ιU).app i =
      (openLevels D π ιU).map a ≫ (openLevelsToOpen D π ιU).app j :=
    fun a => (baseChangeDiagram_map_snd D π ιU a).symm
  have hsc : ∀ i : Iᵒᵖ, u' = conePi (Cone.mk U' pT) i ≫ (openLevelsToOpen D π ιU).app i :=
    fun i => (baseChangeProjection_comp_structureMap D π ιU p jU u' hwT i).symm
  obtain ⟨hcompat, hpres⟩ := (isColimitPresentation_iff _ _ _).mp
    (isColimitPresentation_pullbackSystem (c := Cone.mk U' pT) 𝓕
      (fun i => (openLevelsToOpen D π ιU).app i) hs u' hsc)
  have hfL : ∀ i : Iᵒᵖ, f' ≫ p.app i = pX.app i ≫ (productLevelsProjection D π k y).app i :=
    fun i => (baseChangeProjection_comp_horizontal D _ y p f' r hwX i).symm
  have hgL : ∀ i : Iᵒᵖ, jU ≫ p.app i = pT.app i ≫ (openLevelsInclusion D π ιU).app i :=
    fun i => (baseChangeProjection_comp_horizontal D π ιU p jU u' hwT i).symm
  have heL : ∀ i : Iᵒᵖ, e' ≫ pT.app i = pY.app i ≫ (openProductLevelsProjection D π ιU k y).app i :=
    fun i => (baseChangeProjection_comp_horizontal (openLevels D π ιU) _ y pT e' r' hwY i).symm
  have hhL : ∀ i : Iᵒᵖ, h' ≫ pX.app i = pY.app i ≫ (openProductLevelsInclusion D π ιU k y).app i :=
    fun i => by
      refine pullback.hom_ext ?_ ?_
      · change (h' ≫ pX.app i) ≫ (productLevelsProjection D π k y).app i =
          (pY.app i ≫ (openProductLevelsInclusion D π ιU k y).app i) ≫
            (productLevelsProjection D π k y).app i
        simp only [Category.assoc]
        rw [← hfL i, openProductLevelsInclusion_app_fst, reassoc_of% hh', hgL i,
          reassoc_of% (heL i)]
      · change (h' ≫ pX.app i) ≫ (baseChangeStructureMap D _ y).app i =
          (pY.app i ≫ (openProductLevelsInclusion D π ιU k y).app i) ≫
            (baseChangeStructureMap D _ y).app i
        have hXs : pX.app i ≫ (baseChangeStructureMap D _ y).app i = r :=
          baseChangeProjection_comp_structureMap D _ y p f' r hwX i
        have hYs : pY.app i ≫ (baseChangeStructureMap (openLevels D π ιU)
            (openLevelsInclusion D π ιU ≫ π ≫ (Functor.const Iᵒᵖ).map k) y).app i = r' :=
          baseChangeProjection_comp_structureMap (openLevels D π ιU)
            (openLevelsInclusion D π ιU ≫ π ≫ (Functor.const Iᵒᵖ).map k) y pT e' r' hwY i
        simp only [Category.assoc]
        rw [hXs, hh'r, openProductLevelsInclusion_app_snd, hYs]
  have key := isIso_higherBaseChangeMapAb_of_isLimit (productLevelsProjection D π k y)
    (openLevelsInclusion D π ιU) (openProductLevelsInclusion D π ιU k y)
    (openProductLevelsProjection D π ιU k y) f' jU h' e' (isPullback_level D π ιU k y) hX hp hT hY
    hfL hgL hhL heL n (hpres := hpres)
    (hι := fun a => (isCompatibleFamily_iff _ _ _).mp hcompat a) (hstage := hlevel)
  exact key

end Limit

/-! ### Passing to the limit over a fixed bottom row -/

section FixedBase

variable {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I] {S T : Scheme.{u}}
  (j : T ⟶ S) [QuasiCompact j] [QuasiSeparated j] {DX DY : Iᵒᵖ ⥤ Scheme.{u}}
  [∀ {i i' : Iᵒᵖ} (a : i ⟶ i'), IsAffineHom (DX.map a)]
  [∀ {i i' : Iᵒᵖ} (a : i ⟶ i'), IsAffineHom (DY.map a)]
  (f : DX ⟶ (Functor.const Iᵒᵖ).obj S) (h : DY ⟶ DX) (e : DY ⟶ (Functor.const Iᵒᵖ).obj T)

open LimitBaseChange LimitHigherDirectImage SmallEtaleLimitCohomology in
/-- **[Stacks, Tag 0EZT] (2) over a fixed bottom row, for one sheaf.** Let
`(X_i ← Y_i, S ← T)` be an inverse system of cartesian squares `h_i ≫ f_i = e_i ≫ j` over a
directed set, with affine transition morphisms and fixed bottom row `j : T ⟶ S` quasi-compact
and quasi-separated, and let `X = lim X_i`, `Y = lim Y_i` with the induced square
`hL ≫ fL = eL ≫ j`. If for an abelian sheaf `𝓕` on `T` every base change map
`f_i^{-1}R^n j_*𝓕 ⟶ R^n h_{i,*}e_i^{-1}𝓕` is an isomorphism, so is
`fL^{-1}R^n j_*𝓕 ⟶ R^n hL_*eL^{-1}𝓕`.

This is `isIso_higherBaseChangeMapAb_of_isLimit` for the constant systems `S` and `T` and the
constant system of sheaves `𝓕`. -/
theorem isIso_higherBaseChangeMapAb_of_isLimit_of_fixedBase
    (hsq : ∀ i : Iᵒᵖ,
      IsPullback (h.app i) (e.app i) (f.app i) (((Functor.const Iᵒᵖ).map j).app i))
    {cX cY : Scheme.{u}} {pX : (Functor.const Iᵒᵖ).obj cX ⟶ DX}
    {pY : (Functor.const Iᵒᵖ).obj cY ⟶ DY} (hcX : IsLimit (Cone.mk cX pX))
    (hcY : IsLimit (Cone.mk cY pY)) (fL : cX ⟶ S) (hL : cY ⟶ cX) (eL : cY ⟶ T)
    (hfL : ∀ i, pX.app i ≫ f.app i = fL) (hhL : ∀ i, hL ≫ pX.app i = pY.app i ≫ h.app i)
    (heL : ∀ i, pY.app i ≫ e.app i = eL) (w : hL ≫ fL = eL ≫ j) (n : ℕ)
    (𝓕 : Sheaf (smallEtaleTopology T) Ab.{u + 1})
    (hlevel : ∀ i : Iᵒᵖ,
      IsIso ((higherBaseChangeMapAb (f.app i) (((Functor.const Iᵒᵖ).map j).app i) (h.app i)
        (e.app i) (hsq i).w n).app 𝓕)) :
    IsIso ((higherBaseChangeMapAb fL j hL eL w n).app 𝓕) := by
  have : IsConnected Iᵒᵖ := IsCofiltered.isConnected _
  have : ∀ {i i' : Iᵒᵖ} (a : i ⟶ i'), IsAffineHom (((Functor.const Iᵒᵖ).obj S).map a) :=
    fun _ => inferInstanceAs (IsAffineHom (𝟙 S))
  have : ∀ {i i' : Iᵒᵖ} (a : i ⟶ i'), IsAffineHom (((Functor.const Iᵒᵖ).obj T).map a) :=
    fun _ => inferInstanceAs (IsAffineHom (𝟙 T))
  have : ∀ i : Iᵒᵖ, QuasiCompact (((Functor.const Iᵒᵖ).map j).app i) :=
    fun _ => inferInstanceAs (QuasiCompact j)
  have : ∀ i : Iᵒᵖ, QuasiSeparated (((Functor.const Iᵒᵖ).map j).app i) :=
    fun _ => inferInstanceAs (QuasiSeparated j)
  have hs : ∀ {i i' : Iᵒᵖ} (a : i ⟶ i'),
      (fun _ => 𝟙 T : ∀ i : Iᵒᵖ, ((Functor.const Iᵒᵖ).obj T).obj i ⟶ T) i =
        ((Functor.const Iᵒᵖ).obj T).map a ≫
          (fun _ => 𝟙 T : ∀ i : Iᵒᵖ, ((Functor.const Iᵒᵖ).obj T).obj i ⟶ T) i' :=
    fun _ => (Category.id_comp _).symm
  have hsc : ∀ i : Iᵒᵖ, 𝟙 T = conePi (constCone Iᵒᵖ T) i ≫ 𝟙 T := fun _ =>
    (Category.id_comp _).symm
  obtain ⟨hcompat, hpres⟩ := (isColimitPresentation_iff _ _ _).mp
    (isColimitPresentation_pullbackSystem (c := constCone Iᵒᵖ T) 𝓕 (fun _ => 𝟙 T) hs (𝟙 T) hsc)
  let ε : (etaleAbelianInverseImage.{u, u + 1} (𝟙 T)).obj 𝓕 ≅ 𝓕 :=
    (smallEtalePullbackAbIsoEtaleAbelianInverseImage (𝟙 T)).symm.app 𝓕 ≪≫
      (smallEtalePullbackAbIdOf (𝟙 T) rfl).app 𝓕
  have key := isIso_higherBaseChangeMapAb_of_isLimit f ((Functor.const Iᵒᵖ).map j) h e fL j hL
    eL hsq hcX (isLimitConstCone Iᵒᵖ S) (isLimitConstCone Iᵒᵖ T) hcY
    (fun i => (Category.comp_id _).trans (hfL i).symm)
    (fun i => (Category.comp_id _).trans (Category.id_comp _).symm) hhL
    (fun i => (Category.comp_id _).trans (heL i).symm) n _
    (pullbackSystem 𝓕 (fun _ => 𝟙 T) hs) _ (fun a => (isCompatibleFamily_iff _ _ _).mp hcompat a)
    hpres (fun i => (NatTrans.isIso_app_iff_of_iso _ ε).mpr (hlevel i))
  exact (NatTrans.isIso_app_iff_of_iso (higherBaseChangeMapAb fL j hL eL w n) ε).mp key

end FixedBase

/-! ### The limit in the second factor -/

section ConstBase

variable {I : Type u} [Preorder I] {X B₀ : Scheme.{u}} (D : Iᵒᵖ ⥤ Scheme.{u})
  (π : D ⟶ (Functor.const Iᵒᵖ).obj B₀) {U : Scheme.{u}} (ιU : U ⟶ X) (k : X ⟶ B₀)

/-- The system of products `Y_i ×_{B₀} X`, with the structure maps `π_i : Y_i ⟶ B₀`. -/
abbrev factorProductLevels : Iᵒᵖ ⥤ Scheme.{u} := baseChangeDiagram D π k

/-- The projections `Y_i ×_{B₀} X ⟶ X`. -/
abbrev factorProductLevelsProjection :
    factorProductLevels D π k ⟶ (Functor.const Iᵒᵖ).obj X :=
  baseChangeStructureMap D π k

/-- The system of products `Y_i ×_{B₀} U`. -/
abbrev factorOpenProductLevels : Iᵒᵖ ⥤ Scheme.{u} := baseChangeDiagram D π (ιU ≫ k)

/-- The projections `Y_i ×_{B₀} U ⟶ U`. -/
abbrev factorOpenProductLevelsProjection :
    factorOpenProductLevels D π ιU k ⟶ (Functor.const Iᵒᵖ).obj U :=
  baseChangeStructureMap D π (ιU ≫ k)

/-- The maps `Y_i ×_{B₀} U ⟶ Y_i ×_{B₀} X` induced by `ιU`. -/
def factorOpenProductLevelsInclusion :
    factorOpenProductLevels D π ιU k ⟶ factorProductLevels D π k where
  app i := pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ ιU)
    (pullback.condition.trans (Category.assoc _ _ _).symm)
  naturality i j a := by
    refine pullback.hom_ext ?_ ?_
    · simp only [Category.assoc, pullback.lift_fst,
        pullback.lift_fst_assoc]
    · simp only [Category.assoc, pullback.lift_snd,
        pullback.lift_snd_assoc]

/-- The map `Y_i ×_{B₀} U ⟶ Y_i ×_{B₀} X` commutes with the projections to `Y_i`. -/
@[reassoc (attr := simp)]
theorem factorOpenProductLevelsInclusion_app_fst (i : Iᵒᵖ) :
    (factorOpenProductLevelsInclusion D π ιU k).app i ≫ (baseChangeHorizontal D π k).app i =
      (baseChangeHorizontal D π (ιU ≫ k)).app i :=
  pullback.lift_fst _ _ _

/-- The map `Y_i ×_{B₀} U ⟶ Y_i ×_{B₀} X` followed by the projection to `X` equals the
projection to `U` followed by `ιU`. -/
@[reassoc (attr := simp)]
theorem factorOpenProductLevelsInclusion_app_snd (i : Iᵒᵖ) :
    (factorOpenProductLevelsInclusion D π ιU k).app i ≫
        (factorProductLevelsProjection D π k).app i =
      (factorOpenProductLevelsProjection D π ιU k).app i ≫ ιU :=
  pullback.lift_snd _ _ _

/-- **The squares of the levels are cartesian**: `Y_i ×_{B₀} U` is the fibre product of
`Y_i ×_{B₀} X` and `U` over `X`, the upper half of the pasting of the two product squares over
`B₀`. -/
theorem isPullback_factorLevel (i : Iᵒᵖ) :
    IsPullback ((factorOpenProductLevelsInclusion D π ιU k).app i)
      ((factorOpenProductLevelsProjection D π ιU k).app i)
      ((factorProductLevelsProjection D π k).app i) ιU := by
  refine (IsPullback.of_bot (v₂₁ := pullback.fst (π.app i) k) (v₂₂ := k) (h₃₁ := π.app i) ?_
    (factorOpenProductLevelsInclusion_app_snd D π ιU k i).symm
    (IsPullback.of_hasPullback (π.app i) k).flip).flip
  rw [show (factorOpenProductLevelsInclusion D π ιU k).app i ≫ pullback.fst (π.app i) k =
      pullback.fst (π.app i) (ιU ≫ k) from pullback.lift_fst _ _ _]
  exact (IsPullback.of_hasPullback (π.app i) (ιU ≫ k)).flip

variable [IsDirected I (· ≤ ·)] [Nonempty I]
  [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (D.map a)]

open LimitBaseChange LimitHigherDirectImage SmallEtaleLimitCohomology in
/-- **Base change for the product square of an open passes to a limit in the other factor.** Let
`Y' = lim Y_i` (the cone `p`, a limit) be a directed inverse limit of schemes over `B₀` with
affine transitions, `y' : Y' ⟶ B₀` the common structure morphism, `k : X ⟶ B₀` and `ιU : U ⟶ X`
quasi-compact and quasi-separated. Let `Y' ×_{B₀} X` (any cartesian square `fP, rP`) and
`Y' ×_{B₀} U` (any cartesian square `eQ, rQ`), with `hL : Y' ×_{B₀} U ⟶ Y' ×_{B₀} X` over `Y'`
and `ιU`. Let `𝓕` be an abelian sheaf on `U`. If for every `i` the base change map of the
square `Y_i ×_{B₀} X ⟵ Y_i ×_{B₀} U` over `X ⟵ U` is an isomorphism at `𝓕` in degree `n`, then
so is the base change map of the square `Y' ×_{B₀} X ⟵ Y' ×_{B₀} U` over `X ⟵ U`.

This is the second use of [Stacks, Tag 0EZT] in the proof of [Stacks, Tag 0F1H], where
`Y' = Spec(𝒪^{sh}_{Y,y})` is the limit of schemes `Y_i` of smaller dimension. It is
`isIso_higherBaseChangeMapAb_of_isLimit` for the systems above over the constant systems `X`
and `U`, with the constant system of sheaves `𝓕`. -/
theorem isIso_higherBaseChangeMapAb_limit_of_factorLevels [QuasiCompact ιU]
    [QuasiSeparated ιU]
    {Y' : Scheme.{u}} (p : (Functor.const Iᵒᵖ).obj Y' ⟶ D) (hp : IsLimit (Cone.mk Y' p))
    (y' : Y' ⟶ B₀) (hy' : ∀ i, p.app i ≫ π.app i = y')
    {P' : Scheme.{u}} (fP : P' ⟶ Y') (rP : P' ⟶ X) (hP : IsPullback fP rP y' k)
    {Q' : Scheme.{u}} (eQ : Q' ⟶ Y') (rQ : Q' ⟶ U) (hQ : IsPullback eQ rQ y' (ιU ≫ k))
    (hL : Q' ⟶ P') (hhL : hL ≫ fP = eQ) (hhLr : hL ≫ rP = rQ ≫ ιU) (n : ℕ)
    (𝓕 : Sheaf (smallEtaleTopology U) Ab.{u + 1})
    (hlevel : ∀ i : Iᵒᵖ, IsIso ((higherBaseChangeMapAb
      ((factorProductLevelsProjection D π k).app i) (((Functor.const Iᵒᵖ).map ιU).app i)
      ((factorOpenProductLevelsInclusion D π ιU k).app i)
      ((factorOpenProductLevelsProjection D π ιU k).app i) (isPullback_factorLevel D π ιU k i).w
        n).app 𝓕)) :
    IsIso ((higherBaseChangeMapAb rP ιU hL rQ hhLr n).app 𝓕) := by
  have : IsConnected Iᵒᵖ := IsCofiltered.isConnected _
  have : ∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom ((factorProductLevels D π k).map a) :=
    fun a => isAffineHom_baseChangeDiagram_map D π k a
  have : ∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom ((factorOpenProductLevels D π ιU k).map a) :=
    fun a => isAffineHom_baseChangeDiagram_map D π (ιU ≫ k) a
  have hwX : ∀ i, (fP ≫ p.app i) ≫ π.app i = rP ≫ k := fun i => by
    rw [Category.assoc, hy' i, hP.w]
  let pX := baseChangeProjection D π k p fP rP hwX
  have hX : IsLimit (Cone.mk P' pX) := isLimitBaseChangeProjection D π k fP rP hP hy' hp
  have hwY : ∀ i, (eQ ≫ p.app i) ≫ π.app i = rQ ≫ ιU ≫ k := fun i => by
    rw [Category.assoc, hy' i, hQ.w]
  let pY := baseChangeProjection D π (ιU ≫ k) p eQ rQ hwY
  have hY : IsLimit (Cone.mk Q' pY) := isLimitBaseChangeProjection D π (ιU ≫ k) eQ rQ hQ hy' hp
  have hhL' : ∀ i : Iᵒᵖ,
      hL ≫ pX.app i = pY.app i ≫ (factorOpenProductLevelsInclusion D π ιU k).app i :=
    fun i => by
      refine pullback.hom_ext ?_ ?_
      · change (hL ≫ pX.app i) ≫ (baseChangeHorizontal D π k).app i =
          (pY.app i ≫ (factorOpenProductLevelsInclusion D π ιU k).app i) ≫
            (baseChangeHorizontal D π k).app i
        have hXh : pX.app i ≫ (baseChangeHorizontal D π k).app i = fP ≫ p.app i :=
          baseChangeProjection_comp_horizontal D π k p fP rP hwX i
        have hYh : pY.app i ≫ (baseChangeHorizontal D π (ιU ≫ k)).app i = eQ ≫ p.app i :=
          baseChangeProjection_comp_horizontal D π (ιU ≫ k) p eQ rQ hwY i
        simp only [Category.assoc]
        rw [hXh, factorOpenProductLevelsInclusion_app_fst, hYh, reassoc_of% hhL]
      · change (hL ≫ pX.app i) ≫ (factorProductLevelsProjection D π k).app i =
          (pY.app i ≫ (factorOpenProductLevelsInclusion D π ιU k).app i) ≫
            (factorProductLevelsProjection D π k).app i
        have hXs : pX.app i ≫ (factorProductLevelsProjection D π k).app i = rP :=
          baseChangeProjection_comp_structureMap D π k p fP rP hwX i
        have hYs : pY.app i ≫ (factorOpenProductLevelsProjection D π ιU k).app i = rQ :=
          baseChangeProjection_comp_structureMap D π (ιU ≫ k) p eQ rQ hwY i
        simp only [Category.assoc]
        rw [hXs, hhLr, factorOpenProductLevelsInclusion_app_snd, reassoc_of% hYs]
  exact isIso_higherBaseChangeMapAb_of_isLimit_of_fixedBase ιU
    (factorProductLevelsProjection D π k) (factorOpenProductLevelsInclusion D π ιU k)
    (factorOpenProductLevelsProjection D π ιU k) (isPullback_factorLevel D π ιU k) hX hY rP hL rQ
    (baseChangeProjection_comp_structureMap D π k p fP rP hwX) hhL'
    (baseChangeProjection_comp_structureMap D π (ιU ≫ k) p eQ rQ hwY) hhLr n 𝓕 hlevel

end ConstBase

end Stacks.EtaleCohomology.OpenProductLimit

end
