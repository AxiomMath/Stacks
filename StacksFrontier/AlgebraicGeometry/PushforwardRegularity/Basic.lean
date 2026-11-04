module

public import Mathlib.Algebra.Category.ModuleCat.Stalk
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.RingTheory.Flat.Localization
public import Mathlib.RingTheory.Regular.RegularSequence
public import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Modules.Stalk
public import StacksFrontier.AlgebraicGeometry.RingedSpace.Flat
public import StacksFrontier.AlgebraicGeometry.PushforwardRegularity.FlatRelations

/-!
# Regular sequences on the stalk of a flat pushforward

Let `f : X ⟶ S` be a quasi-compact and quasi-separated morphism of schemes and let `F` be an
`𝒪_X`-module which is flat over `S`. Let `s : S`. This file proves [Stacks, Tag 0EY0] parts (4)
and (5): a nonzerodivisor on `𝒪_{S,s}` remains a nonzerodivisor on `(f_* F)_s`, and a weakly
regular pair on `𝒪_{S,s}` remains weakly regular on `(f_* F)_s`.

The source deduces both from flat base change, replacing `S` by `Spec 𝒪_{S,s}`. Here the
argument is carried out directly on germs, which needs no base change machinery.

Fix an affine open `V ∋ s` and a point `y ∈ f⁻¹V`. The stalk `F_y` is flat over `𝒪_{S, f y}`,
which is a localization of `Γ(S, V)`, so `F_y` is a flat `Γ(S, V)`-module. The equational
criterion for flatness, [Stacks, Tag 00HK], therefore turns any relation
`t • germ ξ = r • germ η` in `F_y`, for `r t : Γ(S, V)`, into a finite expression
`germ ξ = ∑ c j • m j` whose coefficients satisfy `t * c j ∈ (r)` in `Γ(S, V)`; this is
`exists_stalk_smul_repr`.

* For part (4) one takes `r = 0`. Each coefficient is then annihilated by `t`, so -- `germ t`
  being a nonzerodivisor at `s` -- has vanishing germ at `s`, hence vanishes on a neighbourhood
  of `s`. Lifting the expression to a neighbourhood `U` of `y` shows that `ξ` has vanishing
  germs on `U` over that neighbourhood of `s`. Quasi-compactness of `f⁻¹V` assembles these into
  a single neighbourhood `V'` of `s` with `ξ|_{f⁻¹V'} = 0`, which says that the germ of `ξ` in
  `(f_* F)_s` is zero.
* For part (5) one divides each coefficient by `r` near `s`, using that `germ t` is a
  nonzerodivisor on `𝒪_{S,s} ⧸ (germ r)`, and obtains local solutions of `ξ = r • ζ`. Their
  pairwise differences are annihilated by `r`, so part (4)'s assembly step kills them after a
  further shrinking of the neighbourhood of `s`; the pairwise intersections involved are
  quasi-compact precisely because `f⁻¹V` is a quasi-separated space. The local solutions then
  glue.

## Main definitions

* `pushforwardGerm`: the germ at `s` of a section of `F` over `f⁻¹V`, viewed in the stalk of the
  pushforward.
* `stalkPullback`: the image in `𝒪_{X,y}` of a section of `𝒪_S` over an open containing `f y`.
* `resF`, `abSheaf`: restriction of sections of `F`, and the underlying sheaf of abelian groups.

## Main results

* `isSMulRegular_stalk_pushforward`: [Stacks, Tag 0EY0] part (4).
* `exists_resF_div`: the division step on sections, the geometric heart of part (5).
* `isWeaklyRegular_stalk_pushforward`: [Stacks, Tag 0EY0] part (5).

## Implementation notes

Flatness over the base is `AlgebraicGeometry.IsFlatOver`, the ringed-space notion, applied to the
underlying morphism of sheafed spaces. The module structure on the stalk of a sheaf of modules on
a scheme is Mathlib's, re-exposed as `AlgebraicGeometry.Scheme.Modules.moduleStalk` because the
shape of the structure sheaf of a scheme hides it from instance search.

The two statements drop the source's hypothesis that the elements lie in the maximal ideal of
`𝒪_{S,s}`, which the source uses only for the depth statements of parts (3) and (6), and part
(5) concludes weak regularity because the pushforward stalk may be zero. Quasi-coherence of `F`
is not used; `isWeaklyRegular_stalk_pushforward'` is the statement without it.

## References

* [Stacks Project, Tag 0EY0](https://stacks.math.columbia.edu/tag/0EY0)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace Pointwise

universe u

namespace Stacks.AlgebraicGeometry.PushforwardRegularity

variable {X S : Scheme.{u}} (f : X ⟶ S) (F : X.Modules)

/-- The sheaf of abelian groups underlying an `𝒪_X`-module. -/
public noncomputable def abSheaf : TopCat.Sheaf Ab.{u} X :=
  ⟨F.val.presheaf, Scheme.Modules.isSheaf F⟩

/-- The image in the stalk `𝒪_{X,y}` of a section of `𝒪_S` over an open `V` containing `f y`. -/
public noncomputable abbrev stalkPullback (V : S.Opens) (y : X) (hy : f.base y ∈ V)
    (r : Γ(S, V)) : X.presheaf.stalk y :=
  X.presheaf.germ (f ⁻¹ᵁ V) y hy (f.app V r)

/-- The germ at `s` of a section of `F` over `f⁻¹V`, as an element of the stalk at `s` of the
pushforward of `F`. -/
public noncomputable def pushforwardGerm (s : S) (V : S.Opens) (hs : s ∈ V)
    (ξ : Γ(F, f ⁻¹ᵁ V)) :
    TopCat.Presheaf.stalk (C := Ab.{u}) ((Scheme.Modules.pushforward f).obj F).val.presheaf s :=
  TopCat.Presheaf.germ ((Scheme.Modules.pushforward f).obj F).val.presheaf V s hs ξ

/-- Germs of the pushforward are compatible with the action of sections of `𝒪_S`. -/
public lemma pushforwardGerm_smul (s : S) (V : S.Opens) (hs : s ∈ V) (r : Γ(S, V))
    (ξ : Γ(F, f ⁻¹ᵁ V)) :
    pushforwardGerm f F s V hs ((f.app V r) • ξ) =
      (S.presheaf.germ V s hs r) • pushforwardGerm f F s V hs ξ :=
  PresheafOfModules.germ_smul ((Scheme.Modules.pushforward f).obj F).val s V hs r ξ

/-- Germs of the pushforward are compatible with restriction. -/
public lemma pushforwardGerm_res (s : S) {V V' : S.Opens} (hVV' : V' ≤ V) (hs : s ∈ V')
    (hpre : f ⁻¹ᵁ V' ≤ f ⁻¹ᵁ V) (ξ : Γ(F, f ⁻¹ᵁ V)) :
    pushforwardGerm f F s V' hs (F.val.map (homOfLE hpre).op ξ) =
      pushforwardGerm f F s V (hVV' hs) ξ :=
  TopCat.Presheaf.germ_res_apply
    ((Scheme.Modules.pushforward f).obj F).val.presheaf (homOfLE hVV') s hs ξ

/-- The germ of the zero section of the pushforward is zero. -/
public lemma pushforwardGerm_zero (s : S) (V : S.Opens) (hs : s ∈ V) :
    pushforwardGerm f F s V hs 0 = 0 :=
  map_zero (TopCat.Presheaf.germ
    ((Scheme.Modules.pushforward f).obj F).val.presheaf V s hs).hom

/-- Every element of the stalk of the pushforward at `s` is the germ of a section over the
preimage of an affine open neighbourhood of `s`. -/
public lemma exists_pushforwardGerm_eq (s : S)
    (x : TopCat.Presheaf.stalk (C := Ab.{u})
      ((Scheme.Modules.pushforward f).obj F).val.presheaf s) :
    ∃ (V : S.Opens) (_ : IsAffineOpen V) (hs : s ∈ V) (ξ : Γ(F, f ⁻¹ᵁ V)),
      pushforwardGerm f F s V hs ξ = x := by
  obtain ⟨V, hs, hV, ξ, hξ⟩ := TopCat.Presheaf.exists_mem_germ_eq_of_isBasis
    S.isBasis_affineOpens ((Scheme.Modules.pushforward f).obj F).val.presheaf s x
  exact ⟨V, hV, hs, ξ, hξ⟩

/-- Restriction of a section of `F` to a smaller open. -/
public noncomputable abbrev resF {U U' : X.Opens} (h : U' ≤ U) (ξ : Γ(F, U)) : Γ(F, U') :=
  F.val.map (homOfLE h).op ξ

/-- Restriction of sections of `F` is transitive. -/
public lemma resF_resF {U U' U'' : X.Opens} (h : U' ≤ U) (h' : U'' ≤ U') (ξ : Γ(F, U)) :
    resF F h' (resF F h ξ) = resF F (h'.trans h) ξ :=
  (PresheafOfModules.map_comp_apply F.val (homOfLE h).op (homOfLE h').op ξ).symm

/-- Germs are unchanged by restriction. -/
public lemma germ_resF {U U' : X.Opens} (h : U' ≤ U) (ξ : Γ(F, U)) (y : X) (hy : y ∈ U') :
    TopCat.Presheaf.germ F.val.presheaf U' y hy (resF F h ξ) =
      TopCat.Presheaf.germ F.val.presheaf U y (h hy) ξ :=
  TopCat.Presheaf.germ_res_apply F.val.presheaf (homOfLE h) y hy ξ

/-- Germs are additive. -/
public lemma germF_sub {U : X.Opens} (y : X) (hy : y ∈ U) (a b : Γ(F, U)) :
    TopCat.Presheaf.germ F.val.presheaf U y hy (a - b) =
      TopCat.Presheaf.germ F.val.presheaf U y hy a -
        TopCat.Presheaf.germ F.val.presheaf U y hy b :=
  map_sub (TopCat.Presheaf.germ F.val.presheaf U y hy).hom a b

/-- Germs commute with finite sums. -/
public lemma germF_sum {U : X.Opens} (y : X) (hy : y ∈ U) {k : ℕ} (a : Fin k → Γ(F, U)) :
    TopCat.Presheaf.germ F.val.presheaf U y hy (∑ j, a j) =
      ∑ j, TopCat.Presheaf.germ F.val.presheaf U y hy (a j) :=
  map_sum (TopCat.Presheaf.germ F.val.presheaf U y hy).hom a Finset.univ

/-- Restriction of sections of `F` is additive. -/
public lemma resF_sub {U U' : X.Opens} (h : U' ≤ U) (a b : Γ(F, U)) :
    resF F h (a - b) = resF F h a - resF F h b :=
  map_sub (F.val.map (homOfLE h).op).hom a b

/-- Restriction of sections of `F` commutes with finite sums. -/
public lemma resF_sum {U U' : X.Opens} (h : U' ≤ U) {k : ℕ} (a : Fin k → Γ(F, U)) :
    resF F h (∑ j, a j) = ∑ j, resF F h (a j) :=
  map_sum (F.val.map (homOfLE h).op).hom a Finset.univ

/-- Restriction of the zero section is zero. -/
public lemma resF_zero {U U' : X.Opens} (h : U' ≤ U) : resF F h (0 : Γ(F, U)) = 0 :=
  map_zero (F.val.map (homOfLE h).op).hom

/-- The germ of the zero section is zero. -/
public lemma germF_zero {U : X.Opens} (y : X) (hy : y ∈ U) :
    TopCat.Presheaf.germ F.val.presheaf U y hy (0 : Γ(F, U)) = 0 :=
  map_zero (TopCat.Presheaf.germ F.val.presheaf U y hy).hom

/-- Two sections of `F` with the same germs everywhere are equal. -/
public lemma section_ext_F {U : X.Opens} (ξ₁ ξ₂ : Γ(F, U))
    (h : ∀ (y : X) (hy : y ∈ U),
      TopCat.Presheaf.germ F.val.presheaf U y hy ξ₁ =
        TopCat.Presheaf.germ F.val.presheaf U y hy ξ₂) : ξ₁ = ξ₂ :=
  TopCat.Presheaf.section_ext (abSheaf F) U ξ₁ ξ₂ h

/-- Gluing of sections of `F` along an open cover. -/
public lemma exists_glue {ι : Type*} (W : X.Opens) (U : ι → X.Opens)
    (hcover : W ≤ ⨆ i, U i) (hUW : ∀ i, U i ≤ W) (sf : ∀ i, Γ(F, U i))
    (h : ∀ i j, resF F (inf_le_left : U i ⊓ U j ≤ U i) (sf i) =
      resF F (inf_le_right : U i ⊓ U j ≤ U j) (sf j)) :
    ∃ ζ : Γ(F, W), ∀ i, resF F (hUW i) ζ = sf i := by
  obtain ⟨ζ, hζ, -⟩ := (abSheaf F).existsUnique_gluing' U W (fun i => homOfLE (hUW i)) hcover sf
    (fun i j => h i j)
  exact ⟨ζ, hζ⟩

/-- The germ at `y` of a section of `𝒪_S` pulled back to `W ≤ f⁻¹V`. -/
public lemma germ_appLE {V : S.Opens} {W : X.Opens} (hW : W ≤ f ⁻¹ᵁ V) (r : Γ(S, V)) (y : X)
    (hy : y ∈ W) :
    X.presheaf.germ W y hy (f.appLE V W hW r) = stalkPullback f V y (hW hy) r := by
  rw [Scheme.Hom.appLE, CommRingCat.comp_apply, ← CommRingCat.comp_apply,
    X.presheaf.germ_res (homOfLE hW) y hy]

/-- Germs of `F` are compatible with the action of sections of `𝒪_S` pulled back along `f`. -/
public lemma germ_smul_appLE {V : S.Opens} {W : X.Opens} (hW : W ≤ f ⁻¹ᵁ V) (r : Γ(S, V))
    (ξ : Γ(F, W)) (y : X) (hy : y ∈ W) :
    TopCat.Presheaf.germ F.val.presheaf W y hy ((f.appLE V W hW r) • ξ) =
      stalkPullback f V y (hW hy) r • TopCat.Presheaf.germ F.val.presheaf W y hy ξ := by
  refine Eq.trans (PresheafOfModules.germ_smul F.val y W hy (f.appLE V W hW r) ξ) ?_
  congr 1
  exact germ_appLE f hW r y hy

/-- Restriction of a section of `F` is compatible with the action of sections of `𝒪_S`. -/
public lemma resF_smul_appLE {V : S.Opens} {W W' : X.Opens} (hW : W ≤ f ⁻¹ᵁ V) (hW' : W' ≤ W)
    (r : Γ(S, V)) (ξ : Γ(F, W)) :
    resF F hW' ((f.appLE V W hW r) • ξ) =
      (f.appLE V W' (hW'.trans hW) r) • resF F hW' ξ := by
  refine Eq.trans (PresheafOfModules.map_smul F.val (homOfLE hW').op (f.appLE V W hW r) ξ) ?_
  congr 1
  have h := ConcreteCategory.congr_hom (f.appLE_map hW (homOfLE hW').op) r
  rwa [CommRingCat.comp_apply] at h

/-- Restriction of a section of `F` commutes with finite combinations of pulled back sections. -/
private theorem resF_sum_smul_appLE {V : S.Opens} {W W' : X.Opens} (hW : W ≤ f ⁻¹ᵁ V)
    (hW' : W' ≤ W) {k : ℕ} (c : Fin k → Γ(S, V)) (m : Fin k → Γ(F, W)) :
    resF F hW' (∑ j, (f.appLE V W hW (c j)) • m j) =
      ∑ j, (f.appLE V W' (hW'.trans hW) (c j)) • resF F hW' (m j) :=
  (resF_sum F hW' _).trans
    (Finset.sum_congr rfl fun j _ => resF_smul_appLE f F hW hW' (c j) (m j))

/-- Pulling back a restricted section of `𝒪_S` agrees with pulling back the original section. -/
private theorem appLE_map_res {V V' : S.Opens} (hV : V' ≤ V) {W : X.Opens} (hW : W ≤ f ⁻¹ᵁ V')
    (hW' : W ≤ f ⁻¹ᵁ V) (c : Γ(S, V)) :
    f.appLE V' W hW (S.presheaf.map (homOfLE hV).op c) = f.appLE V W hW' c := by
  have h := ConcreteCategory.congr_hom (f.map_appLE hW (homOfLE hV).op) c
  rwa [CommRingCat.comp_apply] at h

/-- `appLE_map_res` for `W` the full preimage of `V'`, phrased with `f.app`. -/
private theorem app_res_eq_appLE {V V' : S.Opens} (hV : V' ≤ V) (hpre : f ⁻¹ᵁ V' ≤ f ⁻¹ᵁ V)
    (c : Γ(S, V)) :
    f.app V' (S.presheaf.map (homOfLE hV).op c) = f.appLE V (f ⁻¹ᵁ V') hpre c := by
  rw [← f.appLE_eq_app (U := V')]
  exact appLE_map_res f hV le_rfl hpre c

/-- A point lying in each of finitely many opens lies in their infimum. -/
private theorem mem_iInf_opens {α : Type*} [TopologicalSpace α] {ι : Type*} [Finite ι] {x : α}
    {U : ι → Opens α} (h : ∀ i, x ∈ U i) : x ∈ ⨅ i, U i := by
  rw [← SetLike.mem_coe, Opens.coe_iInf, Set.mem_iInter]
  exact h

/-- A section of `𝒪_S` that vanishes on `V'` pulls back to zero in the stalk at a point of `X`
lying over `V'`. -/
public lemma stalkPullback_eq_zero {V V' : S.Opens} (hV' : V' ≤ V) (c : Γ(S, V))
    (hc : S.presheaf.map (homOfLE hV').op c = 0) (y : X) (hy : f.base y ∈ V') :
    stalkPullback f V y (hV' hy) c = 0 := by
  rw [show stalkPullback f V y (hV' hy) c = f.stalkMap y (S.presheaf.germ V (f.base y) (hV' hy) c)
      from (Scheme.Hom.germ_stalkMap_apply f V y (hV' hy) c).symm,
    ← S.presheaf.germ_res_apply (homOfLE hV') (f.base y) hy c, hc, map_zero, map_zero]

/-- A germ of `F` which is a finite combination of pullbacks of sections of `𝒪_S` is, on a
small enough neighbourhood, the same combination of actual sections. -/
public lemma exists_resF_eq_sum {V : S.Opens} {W : X.Opens} (hW : W ≤ f ⁻¹ᵁ V) (ξ : Γ(F, W))
    (y : X) (hy : y ∈ W) {k : ℕ} (c : Fin k → Γ(S, V))
    (m : Fin k → TopCat.Presheaf.stalk (C := Ab.{u}) F.val.presheaf y)
    (h : TopCat.Presheaf.germ F.val.presheaf W y hy ξ =
      ∑ j, stalkPullback f V y (hW hy) (c j) • m j) :
    ∃ (U : X.Opens) (_ : y ∈ U) (hUW : U ≤ W) (m' : Fin k → Γ(F, U)),
      resF F hUW ξ = ∑ j, (f.appLE V U (hUW.trans hW) (c j)) • m' j := by
  -- Choose sections representing the germs `m j`, all defined on `W`.
  choose U hUW hyU m' hm' using fun j =>
    TopCat.Presheaf.exists_le_germ_eq F.val.presheaf (m j) hy
  -- Restrict them to the common open `U₀`.
  set U₀ : X.Opens := W ⊓ ⨅ j, U j with hU₀
  have hyU₀ : y ∈ U₀ := ⟨hy, mem_iInf_opens hyU⟩
  have hU₀W : U₀ ≤ W := inf_le_left
  have hU₀U : ∀ j, U₀ ≤ U j := fun j => inf_le_right.trans (iInf_le _ j)
  set η : Fin k → Γ(F, U₀) := fun j => resF F (hU₀U j) (m' j) with hη
  have hgerm_η : ∀ j, TopCat.Presheaf.germ F.val.presheaf U₀ y hyU₀ (η j) = m j := fun j => by
    rw [hη, germ_resF F (hU₀U j) (m' j) y hyU₀, hm' j]
  -- The difference of the two sides has vanishing germ at `y`.
  set β : Γ(F, U₀) := ∑ j, (f.appLE V U₀ (hU₀W.trans hW) (c j)) • η j with hβ
  have hβgerm : TopCat.Presheaf.germ F.val.presheaf U₀ y hyU₀ β =
      TopCat.Presheaf.germ F.val.presheaf U₀ y hyU₀ (resF F hU₀W ξ) := by
    refine Eq.trans (germF_sum F y hyU₀ fun j => (f.appLE V U₀ (hU₀W.trans hW) (c j)) • η j) ?_
    refine Eq.trans (Finset.sum_congr rfl fun j _ =>
      (germ_smul_appLE f F (hU₀W.trans hW) (c j) (η j) y hyU₀).trans
        (congrArg (fun z => stalkPullback f V y (hW hy) (c j) • z) (hgerm_η j))) ?_
    exact h.symm.trans (germ_resF F hU₀W ξ y hyU₀).symm
  -- Hence the two sections agree on a neighbourhood of `y`.
  obtain ⟨U₁, hyU₁, i₁, i₂, hres⟩ :=
    TopCat.Presheaf.germ_eq F.val.presheaf y hyU₀ hyU₀ (resF F hU₀W ξ) β hβgerm.symm
  have hU₁ : U₁ ≤ U₀ := i₁.le
  have h0 : resF F hU₁ (resF F hU₀W ξ) = resF F hU₁ β := hres
  refine ⟨U₁, hyU₁, hU₁.trans hU₀W, fun j => resF F hU₁ (η j), ?_⟩
  exact (resF_resF F hU₀W hU₁ ξ).symm.trans
    (h0.trans (resF_sum_smul_appLE f F (hU₀W.trans hW) hU₁ c η))

/-- Restriction of sections of `𝒪_S` is transitive. -/
public lemma resS_resS {V V' V'' : S.Opens} (h : V' ≤ V) (h' : V'' ≤ V') (c : Γ(S, V)) :
    S.presheaf.map (homOfLE h').op (S.presheaf.map (homOfLE h).op c) =
      S.presheaf.map (homOfLE (h'.trans h)).op c := by
  rw [← CommRingCat.comp_apply, ← S.presheaf.map_comp]
  rfl

/-- **Flatness at a stalk, in coefficient form.** If `F` is flat over `S` and `V` is an affine
open of `S`, then the stalk of `F` at a point `y` over `V` is a flat `Γ(S, V)`-module, because
`𝒪_{S, f y}` is a localization of `Γ(S, V)`. Consequently every relation `t • x = r • z` in that
stalk, for `r t : Γ(S, V)`, is witnessed by coefficients in the colon ideal `(r : t)` of
`Γ(S, V)`. -/
public lemma exists_stalk_smul_repr (hflat : IsFlatOver f.toLRSHom.toShHom F)
    {V : S.Opens} (hV : IsAffineOpen V) (y : X) (hy : f.base y ∈ V) (r t : Γ(S, V))
    (x z : TopCat.Presheaf.stalk (C := Ab.{u}) F.val.presheaf y)
    (h : stalkPullback f V y hy t • x = stalkPullback f V y hy r • z) :
    ∃ (k : ℕ) (c : Fin k → Γ(S, V)) (v : Fin k → Γ(S, V))
      (m : Fin k → TopCat.Presheaf.stalk (C := Ab.{u}) F.val.presheaf y),
      (∀ j, t * c j = r * v j) ∧ x = ∑ j, stalkPullback f V y hy (c j) • m j := by
  let N := TopCat.Presheaf.stalk (C := Ab.{u}) F.val.presheaf y
  let R := S.presheaf.stalk (f.base y)
  let : Module R N := Module.compHom _ (f.stalkMap y).hom
  have : Module.Flat R N := hflat y
  let : Algebra Γ(S, V) R := S.presheaf.algebra_section_stalk ⟨f.base y, hy⟩
  have : IsLocalization.AtPrime R (hV.primeIdealOf ⟨f.base y, hy⟩).asIdeal :=
    hV.isLocalization_stalk ⟨f.base y, hy⟩
  have : Module.Flat Γ(S, V) R :=
    IsLocalization.flat R (hV.primeIdealOf ⟨f.base y, hy⟩).asIdeal.primeCompl
  let : Module Γ(S, V) N :=
    Module.compHom _ ((X.presheaf.germ (f ⁻¹ᵁ V) y hy).hom.comp (f.app V).hom)
  have hsmul : ∀ (c : Γ(S, V)) (n : N), c • n = stalkPullback f V y hy c • n := fun _ _ => rfl
  have : IsScalarTower Γ(S, V) R N := by
    refine ⟨fun c b n => ?_⟩
    rw [hsmul]
    show (f.stalkMap y).hom (_ * b) • n = _
    rw [map_mul]
    show _ = stalkPullback f V y hy c • ((f.stalkMap y) b • n)
    rw [← mul_smul]
    congr 2
    simp [← Scheme.Hom.germ_stalkMap_apply, stalkPullback]
  obtain ⟨k, c, v, m, hc, hx⟩ :=
    Stacks.RingTheory.Flat.exists_smul_repr_of_smul_eq_smul_of_tower R r t x z
      (by rwa [hsmul, hsmul])
  exact ⟨k, c, v, m, hc, hx.trans (Finset.sum_congr rfl fun j _ => hsmul _ _)⟩

/-- The `r = 0` case of `exists_stalk_smul_repr`: an element of the stalk annihilated by the
pullback of `r : Γ(S, V)` is a combination of elements with coefficients annihilated by `r`. -/
public lemma exists_stalk_smul_repr_of_smul_eq_zero (hflat : IsFlatOver f.toLRSHom.toShHom F)
    {V : S.Opens} (hV : IsAffineOpen V) (y : X) (hy : f.base y ∈ V) (r : Γ(S, V))
    (x : TopCat.Presheaf.stalk (C := Ab.{u}) F.val.presheaf y)
    (h : stalkPullback f V y hy r • x = 0) :
    ∃ (k : ℕ) (c : Fin k → Γ(S, V))
      (m : Fin k → TopCat.Presheaf.stalk (C := Ab.{u}) F.val.presheaf y),
      (∀ j, r * c j = 0) ∧ x = ∑ j, stalkPullback f V y hy (c j) • m j := by
  obtain ⟨k, c, v, m, hc, hx⟩ := exists_stalk_smul_repr f F hflat hV y hy 0 r x 0
    (by simp [h])
  exact ⟨k, c, m, fun j => by simpa using hc j, hx⟩

/-- **Local form of the annihilator step.** If `r : Γ(S, V)` has germ a nonzerodivisor at `s` and
annihilates `ξ : Γ(F, W)`, then around every point `y` of `W` there is an open `U` and a
neighbourhood `V'` of `s` on which `ξ` has vanishing germs over `V'`. -/
public lemma exists_nbhd_germ_eq_zero_aux (hflat : IsFlatOver f.toLRSHom.toShHom F) {s : S}
    {V : S.Opens} (hV : IsAffineOpen V) (hs : s ∈ V) (r : Γ(S, V))
    (hr : IsSMulRegular (S.presheaf.stalk s) (S.presheaf.germ V s hs r))
    {W : X.Opens} (hW : W ≤ f ⁻¹ᵁ V) (ξ : Γ(F, W))
    (hξ : (f.appLE V W hW r) • ξ = 0) {y : X} (hy : y ∈ W) :
    ∃ (U : X.Opens) (_ : y ∈ U) (hUW : U ≤ W) (V' : S.Opens) (_ : s ∈ V') (_ : V' ≤ V),
      ∀ (y' : X) (hy' : y' ∈ U), f.base y' ∈ V' →
        TopCat.Presheaf.germ F.val.presheaf W y' (hUW hy') ξ = 0 := by
  have h1 : stalkPullback f V y (hW hy) r • TopCat.Presheaf.germ F.val.presheaf W y hy ξ = 0 := by
    rw [← germ_smul_appLE f F hW r ξ y hy, hξ, germF_zero]
  obtain ⟨k, c, m, hc, hsum⟩ :=
    exists_stalk_smul_repr_of_smul_eq_zero f F hflat hV y (hW hy) r _ h1
  -- Each coefficient has vanishing germ at `s`, hence vanishes near `s`.
  have hc0 : ∀ j, ∃ (V' : S.Opens) (_ : s ∈ V') (hle : V' ≤ V),
      S.presheaf.map (homOfLE hle).op (c j) = 0 := by
    intro j
    have hmul : S.presheaf.germ V s hs r * S.presheaf.germ V s hs (c j) = 0 := by
      rw [← map_mul (S.presheaf.germ V s hs).hom r (c j), hc j,
        map_zero (S.presheaf.germ V s hs).hom]
    have hzero : S.presheaf.germ V s hs (c j) = 0 := by
      apply hr
      show S.presheaf.germ V s hs r • S.presheaf.germ V s hs (c j) =
        S.presheaf.germ V s hs r • (0 : S.presheaf.stalk s)
      rw [smul_eq_mul, smul_eq_mul, mul_zero, hmul]
    obtain ⟨V', hsV', i₁, i₂, he⟩ := TopCat.Presheaf.germ_eq S.presheaf s hs hs (c j) 0
      (hzero.trans (map_zero (S.presheaf.germ V s hs).hom).symm)
    exact ⟨V', hsV', i₁.le, he.trans (map_zero (S.presheaf.map i₂.op).hom)⟩
  choose V' hsV' hV'le hV'0 using hc0
  obtain ⟨U, hyU, hUW, m', hm'⟩ := exists_resF_eq_sum f F hW ξ y hy c m hsum
  refine ⟨U, hyU, hUW, V ⊓ ⨅ j, V' j, ⟨hs, mem_iInf_opens hsV'⟩, inf_le_left, ?_⟩
  · intro y' hy'U hy'V
    rw [← germ_resF F hUW ξ y' hy'U, hm']
    refine Eq.trans (germF_sum F y' hy'U fun j =>
      (f.appLE V U (hUW.trans hW) (c j)) • m' j) ?_
    refine Finset.sum_eq_zero fun j _ => ?_
    have h2 : (V ⊓ ⨅ j, V' j) ≤ V' j := inf_le_right.trans (iInf_le _ j)
    have h3 : S.presheaf.map (homOfLE (inf_le_left : V ⊓ ⨅ j, V' j ≤ V)).op (c j) = 0 :=
      (resS_resS (hV'le j) h2 (c j)).symm.trans
        (by rw [hV'0 j, map_zero (S.presheaf.map (homOfLE h2).op).hom])
    rw [germ_smul_appLE f F (hUW.trans hW) (c j) (m' j) y' hy'U,
      stalkPullback_eq_zero f (inf_le_left : V ⊓ ⨅ j, V' j ≤ V) (c j) h3 y' hy'V,
      zero_smul]

/-- **The annihilator step of [Stacks, Tag 0EY0] part (4).** If `r : Γ(S, V)` has germ a
nonzerodivisor at `s` and annihilates `ξ : Γ(F, W)` on a quasi-compact `W ≤ f⁻¹V`, then the germs
of `ξ` vanish at every point of `W` lying over a suitable neighbourhood of `s`. -/
public lemma exists_nbhd_germ_eq_zero (hflat : IsFlatOver f.toLRSHom.toShHom F) {s : S}
    {V : S.Opens} (hV : IsAffineOpen V) (hs : s ∈ V) (r : Γ(S, V))
    (hr : IsSMulRegular (S.presheaf.stalk s) (S.presheaf.germ V s hs r))
    {W : X.Opens} (hW : W ≤ f ⁻¹ᵁ V) (hWc : IsCompact (W : Set X)) (ξ : Γ(F, W))
    (hξ : (f.appLE V W hW r) • ξ = 0) :
    ∃ (V' : S.Opens) (_ : s ∈ V') (_ : V' ≤ V), ∀ (y : X) (hy : y ∈ W), f.base y ∈ V' →
        TopCat.Presheaf.germ F.val.presheaf W y hy ξ = 0 := by
  choose U hyU hUW V' hsV' hV'le hgerm using fun (y : W) =>
    exists_nbhd_germ_eq_zero_aux f F hflat hV hs r hr hW ξ hξ y.2
  obtain ⟨T, hT⟩ := hWc.elim_finite_subcover (fun y : W => (U y : Set X))
    (fun y => (U y).isOpen) fun z hz => Set.mem_iUnion.mpr ⟨⟨z, hz⟩, hyU ⟨z, hz⟩⟩
  refine ⟨V ⊓ ⨅ i : {x : W // x ∈ T}, V' i.1, ⟨hs, mem_iInf_opens fun i => hsV' i.1⟩,
    inf_le_left, ?_⟩
  · intro y hy hyV
    obtain ⟨i, hi, hyi⟩ := Set.mem_iUnion₂.mp (hT hy)
    have hle : (V ⊓ ⨅ i : {x : W // x ∈ T}, V' i.1) ≤ V' i :=
      le_trans inf_le_right (iInf_le (fun i : {x : W // x ∈ T} => V' i.1) ⟨i, hi⟩)
    exact hgerm i y hyi (hle hyV)

/-- The affine version of `exists_resF_eq_sum`: the neighbourhood can be taken affine, hence
quasi-compact. -/
public lemma exists_affine_resF_eq_sum {V : S.Opens} {W : X.Opens} (hW : W ≤ f ⁻¹ᵁ V)
    (ξ : Γ(F, W)) (y : X) (hy : y ∈ W) {k : ℕ} (c : Fin k → Γ(S, V))
    (m : Fin k → TopCat.Presheaf.stalk (C := Ab.{u}) F.val.presheaf y)
    (h : TopCat.Presheaf.germ F.val.presheaf W y hy ξ =
      ∑ j, stalkPullback f V y (hW hy) (c j) • m j) :
    ∃ (U : X.Opens) (_ : IsAffineOpen U) (_ : y ∈ U) (hUW : U ≤ W) (m' : Fin k → Γ(F, U)),
      resF F hUW ξ = ∑ j, (f.appLE V U (hUW.trans hW) (c j)) • m' j := by
  obtain ⟨U₀, hyU₀, hU₀W, m₀, hm₀⟩ := exists_resF_eq_sum f F hW ξ y hy c m h
  obtain ⟨_, ⟨U, hU, rfl⟩, hyU, hUU₀⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hyU₀ U₀.isOpen
  have hUU₀' : U ≤ U₀ := hUU₀
  refine ⟨U, hU, hyU, hUU₀'.trans hU₀W, fun j => resF F hUU₀' (m₀ j), ?_⟩
  rw [← resF_resF F hU₀W hUU₀' ξ, hm₀]
  exact resF_sum_smul_appLE f F (hU₀W.trans hW) hUU₀' c m₀

/-- **Local form of the division step.** If `germ t` is a nonzerodivisor on `𝒪_{S,s} ⧸ (germ r)`
and `t • ξ = r • η` on `W`, then near every point of `W`, and over a neighbourhood of `s`, the
section `ξ` is `r` times a section. -/
public lemma exists_nbhd_div_aux (hflat : IsFlatOver f.toLRSHom.toShHom F) {s : S}
    {V : S.Opens} (hV : IsAffineOpen V) (hs : s ∈ V) (r t : Γ(S, V))
    (hb : IsSMulRegular (QuotSMulTop (S.presheaf.germ V s hs r) (S.presheaf.stalk s))
      (S.presheaf.germ V s hs t))
    {W : X.Opens} (hW : W ≤ f ⁻¹ᵁ V) (ξ η : Γ(F, W))
    (hξ : (f.appLE V W hW t) • ξ = (f.appLE V W hW r) • η) {y : X} (hy : y ∈ W) :
    ∃ (U : X.Opens) (_ : IsAffineOpen U) (_ : y ∈ U) (_ : U ≤ W)
      (V' : S.Opens) (_ : s ∈ V') (_ : V' ≤ V)
      (hA : U ⊓ f ⁻¹ᵁ V' ≤ W) (ζ : Γ(F, U ⊓ f ⁻¹ᵁ V')),
      resF F hA ξ = (f.appLE V (U ⊓ f ⁻¹ᵁ V') (hA.trans hW) r) • ζ := by
  have h1 : stalkPullback f V y (hW hy) t • TopCat.Presheaf.germ F.val.presheaf W y hy ξ =
      stalkPullback f V y (hW hy) r • TopCat.Presheaf.germ F.val.presheaf W y hy η := by
    rw [← germ_smul_appLE f F hW t ξ y hy, ← germ_smul_appLE f F hW r η y hy, hξ]
  obtain ⟨k, u, v, m, huv, hsum⟩ :=
    exists_stalk_smul_repr f F hflat hV y (hW hy) r t _ _ h1
  -- Divide each coefficient by `r` on a neighbourhood of `s`.
  have hdiv : ∀ j, ∃ (V' : S.Opens) (_ : s ∈ V') (hle : V' ≤ V) (w : Γ(S, V')),
      S.presheaf.map (homOfLE hle).op (u j) =
        S.presheaf.map (homOfLE hle).op r * w := by
    intro j
    have hmul : S.presheaf.germ V s hs t * S.presheaf.germ V s hs (u j) =
        S.presheaf.germ V s hs r * S.presheaf.germ V s hs (v j) := by
      rw [← map_mul (S.presheaf.germ V s hs).hom, ← map_mul (S.presheaf.germ V s hs).hom, huv j]
    obtain ⟨ω, hω⟩ :=
      Stacks.RingTheory.exists_mul_eq_of_isSMulRegular_quotSMulTop _ _ hb _ _ hmul
    obtain ⟨V₁, hsV₁, -, w₁, hw₁⟩ := TopCat.Presheaf.exists_mem_germ_eq_of_isBasis
      S.isBasis_affineOpens S.presheaf s ω
    set V₂ : S.Opens := V ⊓ V₁ with hV₂
    have hsV₂ : s ∈ V₂ := ⟨hs, hsV₁⟩
    set θ : Γ(S, V₂) := S.presheaf.map (homOfLE (inf_le_left : V₂ ≤ V)).op r *
      S.presheaf.map (homOfLE (inf_le_right : V₂ ≤ V₁)).op w₁ with hθ
    have hθgerm : S.presheaf.germ V₂ s hsV₂ θ = S.presheaf.germ V s hs (u j) := by
      rw [hθ, map_mul (S.presheaf.germ V₂ s hsV₂).hom,
        S.presheaf.germ_res_apply (homOfLE (inf_le_left : V₂ ≤ V)) s hsV₂ r,
        S.presheaf.germ_res_apply (homOfLE (inf_le_right : V₂ ≤ V₁)) s hsV₂ w₁, hw₁, ← hω]
    obtain ⟨V', hsV', -, hV'V, hV'V₂, he⟩ := TopCat.Presheaf.germ_eq_of_isBasis
      S.isBasis_affineOpens S.presheaf s hs hsV₂ hθgerm.symm
    refine ⟨V', hsV', hV'V, S.presheaf.map (homOfLE (hV'V₂.trans inf_le_right)).op w₁, ?_⟩
    rw [he, hθ, map_mul (S.presheaf.map (homOfLE hV'V₂).op).hom,
      resS_resS (inf_le_left : V₂ ≤ V) hV'V₂ r, resS_resS (inf_le_right : V₂ ≤ V₁) hV'V₂ w₁]
  choose V' hsV' hV'le w hw using hdiv
  obtain ⟨U, hU, hyU, hUW, m', hm'⟩ := exists_affine_resF_eq_sum f F hW ξ y hy u m hsum
  set V₀ : S.Opens := V ⊓ ⨅ j, V' j with hV₀
  have hsV₀ : s ∈ V₀ := ⟨hs, mem_iInf_opens hsV'⟩
  have hV₀V : V₀ ≤ V := inf_le_left
  have hV₀V' : ∀ j, V₀ ≤ V' j := fun j => inf_le_right.trans (iInf_le _ j)
  set A : X.Opens := U ⊓ f ⁻¹ᵁ V₀ with hA'
  have hAU : A ≤ U := inf_le_left
  have hAW : A ≤ W := hAU.trans hUW
  have hApre : A ≤ f ⁻¹ᵁ V₀ := inf_le_right
  -- The restricted coefficients are divisible by `r` on `V₀`.
  set w₀ : Fin k → Γ(S, V₀) := fun j => S.presheaf.map (homOfLE (hV₀V' j)).op (w j) with hw₀
  have hu₀ : ∀ j, S.presheaf.map (homOfLE hV₀V).op (u j) =
      S.presheaf.map (homOfLE hV₀V).op r * w₀ j := by
    intro j
    have := congrArg (fun z => S.presheaf.map (homOfLE (hV₀V' j)).op z) (hw j)
    simp only at this
    rw [map_mul (S.presheaf.map (homOfLE (hV₀V' j)).op).hom] at this
    rw [← resS_resS (hV'le j) (hV₀V' j) (u j), this, resS_resS (hV'le j) (hV₀V' j) r, hw₀]
  refine ⟨U, hU, hyU, hUW, V₀, hsV₀, hV₀V, hAW, ∑ j, (f.appLE V₀ A hApre (w₀ j)) •
    resF F hAU (m' j), ?_⟩
  rw [← resF_resF F hUW hAU ξ, hm', resF_sum_smul_appLE f F (hUW.trans hW) hAU u m',
    Finset.smul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← mul_smul]
  congr 1
  -- `appLE r * appLE (w₀ j) = appLE (u j)`
  rw [← appLE_map_res f hV₀V hApre (hAW.trans hW) (u j),
    ← appLE_map_res f hV₀V hApre (hAW.trans hW) r, hu₀ j, map_mul (f.appLE V₀ A hApre).hom]

/-- **The division step of [Stacks, Tag 0EY0] part (5).** Let `f` be quasi-compact and
quasi-separated, let `F` be flat over `S`, and let `r t : Γ(S, V)` on an affine open `V ∋ s` be
such that `germ r` is a nonzerodivisor on `𝒪_{S,s}` and `germ t` is a nonzerodivisor on
`𝒪_{S,s} ⧸ (germ r)`. If `t • ξ = r • η` over `f⁻¹V`, then over the preimage of a smaller
neighbourhood of `s` the section `ξ` is `r` times a section.

Locally on `f⁻¹V` this is `exists_nbhd_div_aux`; the local solutions are glued after shrinking
the neighbourhood of `s` so that their pairwise differences, which are annihilated by `r`, are
killed by `exists_nbhd_germ_eq_zero` on the pairwise intersections. Those intersections are
quasi-compact because `f⁻¹V` is a quasi-separated space. -/
public lemma exists_resF_div [QuasiCompact f] [QuasiSeparated f]
    (hflat : IsFlatOver f.toLRSHom.toShHom F) {s : S}
    {V : S.Opens} (hV : IsAffineOpen V) (hs : s ∈ V) (r t : Γ(S, V))
    (ha : IsSMulRegular (S.presheaf.stalk s) (S.presheaf.germ V s hs r))
    (hb : IsSMulRegular (QuotSMulTop (S.presheaf.germ V s hs r) (S.presheaf.stalk s))
      (S.presheaf.germ V s hs t))
    (ξ η : Γ(F, f ⁻¹ᵁ V)) (hξ : (f.app V t) • ξ = (f.app V r) • η) :
    ∃ (V₃ : S.Opens) (_ : s ∈ V₃) (_ : V₃ ≤ V) (hpre : f ⁻¹ᵁ V₃ ≤ f ⁻¹ᵁ V)
      (ζ : Γ(F, f ⁻¹ᵁ V₃)),
      resF F hpre ξ = (f.appLE V (f ⁻¹ᵁ V₃) hpre r) • ζ := by
  have hqs : IsQuasiSeparated ((f ⁻¹ᵁ V : X.Opens) : Set X) :=
    f.isQuasiSeparated_preimage hV.isQuasiSeparated
  have hVc : IsCompact ((f ⁻¹ᵁ V : X.Opens) : Set X) := f.isCompact_preimage hV.isCompact
  have hξ' : (f.appLE V (f ⁻¹ᵁ V) (le_refl _) t) • ξ =
      (f.appLE V (f ⁻¹ᵁ V) (le_refl _) r) • η := by rwa [f.appLE_eq_app]
  -- Step 1: local division at every point.
  choose U hUaff hyU hUW V' hsV' hV'le hAW ζ hζ using fun (y : (f ⁻¹ᵁ V : X.Opens)) =>
    exists_nbhd_div_aux f F hflat hV hs r t hb (le_refl (f ⁻¹ᵁ V)) ξ η hξ' y.2
  -- Step 2: a finite subcover.
  obtain ⟨T, hT⟩ := hVc.elim_finite_subcover (fun y : (f ⁻¹ᵁ V : X.Opens) => (U y : Set X))
    (fun y => (U y).isOpen) fun z hz => Set.mem_iUnion.mpr ⟨⟨z, hz⟩, hyU ⟨z, hz⟩⟩
  -- Step 3: an affine neighbourhood `V₂` of `s` inside all of the `V' i`.
  have hsV₁ : s ∈ V ⊓ ⨅ i : {x : (f ⁻¹ᵁ V : X.Opens) // x ∈ T}, V' i.1 :=
    ⟨hs, mem_iInf_opens fun i => hsV' i.1⟩
  obtain ⟨_, ⟨V₂, hV₂aff, rfl⟩, hsV₂, hV₂sub⟩ :=
    S.isBasis_affineOpens.exists_subset_of_mem_open hsV₁ (_ : S.Opens).isOpen
  have hV₂V₁ : V₂ ≤ V ⊓ ⨅ i : {x : (f ⁻¹ᵁ V : X.Opens) // x ∈ T}, V' i.1 := hV₂sub
  have hV₂V : V₂ ≤ V := hV₂V₁.trans inf_le_left
  have hV₂V' : ∀ i : {x : (f ⁻¹ᵁ V : X.Opens) // x ∈ T}, V₂ ≤ V' i.1 := fun i =>
    hV₂V₁.trans (inf_le_right.trans (iInf_le _ i))
  have hV₂c : IsCompact ((f ⁻¹ᵁ V₂ : X.Opens) : Set X) := f.isCompact_preimage hV₂aff.isCompact
  have hpre₂ : (f ⁻¹ᵁ V₂ : X.Opens) ≤ f ⁻¹ᵁ V := fun _ hz => hV₂V hz
  -- Step 4: the local solutions on the pieces `B i`.
  set B : {x : (f ⁻¹ᵁ V : X.Opens) // x ∈ T} → X.Opens := fun i => U i.1 ⊓ f ⁻¹ᵁ V₂ with hB
  have hBle : ∀ i, B i ≤ U i.1 ⊓ f ⁻¹ᵁ V' i.1 := fun i =>
    inf_le_inf_left _ fun _ hz => hV₂V' i hz
  have hBpre : ∀ i, B i ≤ f ⁻¹ᵁ V := fun i => inf_le_left.trans (hUW i.1)
  have hBc : ∀ i, IsCompact ((B i : X.Opens) : Set X) := fun i => by
    rw [hB, Opens.coe_inf]
    exact hqs _ _ (hUW i.1) (U i.1).isOpen (hUaff i.1).isCompact hpre₂
      (f ⁻¹ᵁ V₂).isOpen hV₂c
  set σ : (i : {x : (f ⁻¹ᵁ V : X.Opens) // x ∈ T}) → Γ(F, B i) :=
    fun i => resF F (hBle i) (ζ i) with hσ
  have hσeq : ∀ i, resF F (hBpre i) ξ = (f.appLE V (B i) (hBpre i) r) • σ i := by
    intro i
    rw [← resF_resF F (hAW i.1) (hBle i) ξ, hζ i.1]
    exact resF_smul_appLE f F ((hAW i.1).trans (le_refl _)) (hBle i) r (ζ i.1)
  -- Step 5: kill the pairwise discrepancies by shrinking the neighbourhood of `s`.
  have hpair : ∀ i j : {x : (f ⁻¹ᵁ V : X.Opens) // x ∈ T},
      ∃ (V'' : S.Opens) (_ : s ∈ V'') (_ : V'' ≤ V), ∀ (y : X) (hy : y ∈ B i ⊓ B j),
        f.base y ∈ V'' → TopCat.Presheaf.germ F.val.presheaf (B i ⊓ B j) y hy
          (resF F (inf_le_left : B i ⊓ B j ≤ B i) (σ i) -
            resF F (inf_le_right : B i ⊓ B j ≤ B j) (σ j)) = 0 := by
    intro i j
    have hWij : (B i ⊓ B j : X.Opens) ≤ f ⁻¹ᵁ V := inf_le_left.trans (hBpre i)
    have hWijc : IsCompact ((B i ⊓ B j : X.Opens) : Set X) := by
      rw [Opens.coe_inf]
      exact hqs _ _ (hBpre i) (B i).isOpen (hBc i) (hBpre j) (B j).isOpen (hBc j)
    refine exists_nbhd_germ_eq_zero f F hflat hV hs r ha hWij hWijc _ ?_
    have ei := congrArg (resF F (inf_le_left : B i ⊓ B j ≤ B i)) (hσeq i)
    have ej := congrArg (resF F (inf_le_right : B i ⊓ B j ≤ B j)) (hσeq j)
    rw [resF_resF F (hBpre i) inf_le_left ξ,
      resF_smul_appLE f F (hBpre i) (inf_le_left : B i ⊓ B j ≤ B i) r (σ i)] at ei
    rw [resF_resF F (hBpre j) inf_le_right ξ,
      resF_smul_appLE f F (hBpre j) (inf_le_right : B i ⊓ B j ≤ B j) r (σ j)] at ej
    rw [smul_sub, ← ei, ← ej, sub_self]
  choose V'' hsV'' hV''le hV''germ using hpair
  -- Step 6: the compatible family on the pieces `C i`.
  set V₃ : S.Opens := V₂ ⊓ ⨅ i : {x : (f ⁻¹ᵁ V : X.Opens) // x ∈ T},
    ⨅ j : {x : (f ⁻¹ᵁ V : X.Opens) // x ∈ T}, V'' i j with hV₃
  have hsV₃ : s ∈ V₃ := ⟨hsV₂, mem_iInf_opens fun i => mem_iInf_opens (hsV'' i)⟩
  have hV₃V₂ : V₃ ≤ V₂ := inf_le_left
  have hV₃V : V₃ ≤ V := hV₃V₂.trans hV₂V
  have hV₃V'' : ∀ i j, V₃ ≤ V'' i j := fun i j =>
    inf_le_right.trans ((iInf_le _ i).trans (iInf_le _ j))
  have hpre₃ : (f ⁻¹ᵁ V₃ : X.Opens) ≤ f ⁻¹ᵁ V := fun _ hz => hV₃V hz
  set C : {x : (f ⁻¹ᵁ V : X.Opens) // x ∈ T} → X.Opens := fun i => U i.1 ⊓ f ⁻¹ᵁ V₃ with hC
  have hCB : ∀ i, C i ≤ B i := fun i => inf_le_inf_left _ fun _ hz => hV₃V₂ hz
  have hCpre : ∀ i, C i ≤ f ⁻¹ᵁ V₃ := fun i => inf_le_right
  have hcompat : ∀ i j, resF F (inf_le_left.trans (hCB i) : C i ⊓ C j ≤ B i) (σ i) =
      resF F (inf_le_right.trans (hCB j) : C i ⊓ C j ≤ B j) (σ j) := by
    intro i j
    refine section_ext_F F _ _ fun y hy => ?_
    have hyij : y ∈ B i ⊓ B j := ⟨hCB i hy.1, hCB j hy.2⟩
    have h0 := hV''germ i j y hyij (hV₃V'' i j hy.1.2)
    rw [germF_sub F y hyij, germ_resF F (inf_le_left : B i ⊓ B j ≤ B i) (σ i) y hyij,
      germ_resF F (inf_le_right : B i ⊓ B j ≤ B j) (σ j) y hyij, sub_eq_zero] at h0
    rwa [germ_resF F (inf_le_left.trans (hCB i) : C i ⊓ C j ≤ B i) (σ i) y hy,
      germ_resF F (inf_le_right.trans (hCB j) : C i ⊓ C j ≤ B j) (σ j) y hy]
  -- Step 7: glue.
  obtain ⟨ζ₀, hζ₀⟩ := exists_glue F (f ⁻¹ᵁ V₃) C
    (fun z hz => by
      obtain ⟨i, hi, hzi⟩ := Set.mem_iUnion₂.mp (hT (hV₃V hz))
      exact Opens.mem_iSup.mpr ⟨⟨i, hi⟩, hzi, hz⟩)
    hCpre (fun i => resF F (hCB i) (σ i)) fun i j =>
      (resF_resF F (hCB i) (inf_le_left : C i ⊓ C j ≤ C i) (σ i)).trans ((hcompat i j).trans
        (resF_resF F (hCB j) (inf_le_right : C i ⊓ C j ≤ C j) (σ j)).symm)
  refine ⟨V₃, hsV₃, hV₃V, hpre₃, ζ₀, ?_⟩
  -- Step 8: the glued section divides `ξ`.
  refine section_ext_F F _ _ fun y hy => ?_
  obtain ⟨i, hi, hyi⟩ := Set.mem_iUnion₂.mp (hT (hV₃V hy))
  set I : {x : (f ⁻¹ᵁ V : X.Opens) // x ∈ T} := ⟨i, hi⟩ with hI
  have hyC : y ∈ C I := ⟨hyi, hy⟩
  have e2 : resF F (hCB I) (resF F (hBpre I) ξ) =
      (f.appLE V (C I) ((hCB I).trans (hBpre I)) r) • resF F (hCB I) (σ I) := by
    rw [hσeq I]
    exact resF_smul_appLE f F (hBpre I) (hCB I) r (σ I)
  have e3 : resF F (hCpre I) ((f.appLE V (f ⁻¹ᵁ V₃) hpre₃ r) • ζ₀) =
      (f.appLE V (C I) ((hCB I).trans (hBpre I)) r) • resF F (hCB I) (σ I) := by
    rw [resF_smul_appLE f F hpre₃ (hCpre I) r ζ₀, hζ₀ I]
  rw [← germ_resF F (hCpre I) (resF F hpre₃ ξ) y hyC,
    ← germ_resF F (hCpre I) ((f.appLE V (f ⁻¹ᵁ V₃) hpre₃ r) • ζ₀) y hyC,
    e3, resF_resF F hpre₃ (hCpre I) ξ, ← e2, resF_resF F (hBpre I) (hCB I) ξ]

/-- If `r : Γ(S, V)` has germ a nonzerodivisor at `s` and annihilates a section of `F` over
`f⁻¹V`, then that section has zero germ in the stalk of the pushforward at `s`. -/
public lemma pushforwardGerm_eq_zero_of_smul_eq_zero [QuasiCompact f]
    (hflat : IsFlatOver f.toLRSHom.toShHom F) {s : S}
    {V : S.Opens} (hV : IsAffineOpen V) (hs : s ∈ V) (r : Γ(S, V))
    (hr : IsSMulRegular (S.presheaf.stalk s) (S.presheaf.germ V s hs r))
    (ξ : Γ(F, f ⁻¹ᵁ V)) (hξ : (f.app V r) • ξ = 0) :
    pushforwardGerm f F s V hs ξ = 0 := by
  obtain ⟨V', hsV', hV'V, hgerm⟩ := exists_nbhd_germ_eq_zero f F hflat hV hs r hr
    (le_refl (f ⁻¹ᵁ V)) (f.isCompact_preimage hV.isCompact) ξ
    (by rwa [f.appLE_eq_app])
  have hpre : f ⁻¹ᵁ V' ≤ f ⁻¹ᵁ V := fun _ h => hV'V h
  have hres : F.val.map (homOfLE hpre).op ξ = 0 := by
    refine TopCat.Presheaf.section_ext (abSheaf F) (f ⁻¹ᵁ V') _ _ fun y hy => ?_
    refine Eq.trans (germ_resF F hpre ξ y hy) ?_
    exact (hgerm y (hpre hy) hy).trans (germF_zero F y hy).symm
  rw [← pushforwardGerm_res f F s hV'V hsV' hpre ξ, hres]
  exact pushforwardGerm_zero f F s V' hsV'

/-- **[Stacks, Tag 0EY0] part (4).** Let `f : X ⟶ S` be a quasi-compact morphism of schemes and
let `F` be an `𝒪_X`-module flat over `S`. A nonzerodivisor on `𝒪_{S,s}` is a nonzerodivisor on
`(f_* F)_s`.

The source states this for an element of the maximal ideal of `𝒪_{S,s}`; that hypothesis is used
there only for the depth consequences, so it is omitted here. -/
@[sga "3 VIB 12.8" "more general"]
public theorem isSMulRegular_stalk_pushforward [QuasiCompact f]
    (hflat : IsFlatOver f.toLRSHom.toShHom F) (s : S) (a : S.presheaf.stalk s)
    (ha : IsSMulRegular (S.presheaf.stalk s) a) :
    IsSMulRegular (TopCat.Presheaf.stalk (C := Ab.{u})
      ((Scheme.Modules.pushforward f).obj F).val.presheaf s) a := by
  -- It suffices to show that `a` annihilates only `0`.
  have key : ∀ x : TopCat.Presheaf.stalk (C := Ab.{u})
      ((Scheme.Modules.pushforward f).obj F).val.presheaf s, a • x = 0 → x = 0 := by
    intro x hx
    -- Represent `a` and `x` on a common affine open neighbourhood of `s`.
    obtain ⟨Va, hsVa, hVa, ra, hra⟩ :=
      TopCat.Presheaf.exists_mem_germ_eq_of_isBasis S.isBasis_affineOpens S.presheaf s a
    obtain ⟨Vx, hVx, hsVx, ξ, hξ⟩ := exists_pushforwardGerm_eq f F s x
    obtain ⟨_, ⟨V, -, rfl⟩, hsV, hVsub⟩ := S.isBasis_affineOpens.exists_subset_of_mem_open
      (show s ∈ (Va ⊓ Vx : S.Opens) from ⟨hsVa, hsVx⟩) (Va ⊓ Vx).isOpen
    have hVle : V ≤ Va ⊓ Vx := hVsub
    have hVa' : V ≤ Va := hVle.trans inf_le_left
    have hVx' : V ≤ Vx := hVle.trans inf_le_right
    set r : Γ(S, V) := S.presheaf.map (homOfLE hVa').op ra with hr
    have hpreVx : f ⁻¹ᵁ V ≤ f ⁻¹ᵁ Vx := fun _ h => hVx' h
    set η : Γ(F, f ⁻¹ᵁ V) := resF F hpreVx ξ with hη
    have hgerm_r : S.presheaf.germ V s hsV r = a := by
      rw [hr, S.presheaf.germ_res_apply (homOfLE hVa') s hsV ra, hra]
    have hgerm_η : pushforwardGerm f F s V hsV η = x := by
      rw [hη, pushforwardGerm_res f F s hVx' hsV hpreVx ξ, hξ]
    -- The annihilation statement becomes a statement about sections.
    have hsmul : pushforwardGerm f F s V hsV ((f.app V r) • η) = 0 := by
      rw [pushforwardGerm_smul f F s V hsV r η, hgerm_r, hgerm_η, hx]
    obtain ⟨V₁, hsV₁, hV₁, hV₁V, hV₁V', he⟩ := TopCat.Presheaf.germ_eq_of_isBasis
      S.isBasis_affineOpens ((Scheme.Modules.pushforward f).obj F).val.presheaf s hsV hsV
      (hsmul.trans (pushforwardGerm_zero f F s V hsV).symm)
    -- On the affine open `V₁` the pulled back section is annihilated outright.
    have hpre : f ⁻¹ᵁ V₁ ≤ f ⁻¹ᵁ V := fun _ h => hV₁V h
    set r₁ : Γ(S, V₁) := S.presheaf.map (homOfLE hV₁V).op r with hr₁
    have hξ₁ : (f.app V₁ r₁) • (resF F hpre η) = 0 := by
      rw [hr₁, app_res_eq_appLE f hV₁V hpre,
        ← resF_smul_appLE f F (le_refl (f ⁻¹ᵁ V)) hpre r η, f.appLE_eq_app]
      exact he.trans (resF_zero F fun _ h => hV₁V' h)
    have hgerm_r₁ : S.presheaf.germ V₁ s hsV₁ r₁ = a := by
      rw [hr₁, S.presheaf.germ_res_apply (homOfLE hV₁V) s hsV₁ r, hgerm_r]
    rw [← hgerm_η, ← pushforwardGerm_res f F s hV₁V hsV₁ hpre η]
    refine pushforwardGerm_eq_zero_of_smul_eq_zero f F hflat hV₁ hsV₁ r₁ ?_ _ hξ₁
    rwa [hgerm_r₁]
  intro x₁ x₂ hx
  have hx' : a • x₁ = a • x₂ := hx
  have h0 : a • (x₁ - x₂) = 0 := by rw [smul_sub, hx', sub_self]
  exact sub_eq_zero.mp (key _ h0)

/-- **[Stacks, Tag 0EY0] part (5), stalk-level division.** For `f` quasi-compact and
quasi-separated and `F` flat over `S`, if `a, b` is a weakly regular sequence on `𝒪_{S,s}` and
`b • x` is divisible by `a` in `(f_* F)_s`, then so is `x`. -/
public theorem exists_smul_eq_of_smul_eq_smul [QuasiCompact f] [QuasiSeparated f]
    (hflat : IsFlatOver f.toLRSHom.toShHom F) (s : S) (a b : S.presheaf.stalk s)
    (ha : IsSMulRegular (S.presheaf.stalk s) a)
    (hb : IsSMulRegular (QuotSMulTop a (S.presheaf.stalk s)) b)
    (x y : TopCat.Presheaf.stalk (C := Ab.{u})
      ((Scheme.Modules.pushforward f).obj F).val.presheaf s)
    (h : b • x = a • y) :
    ∃ z, x = a • z := by
  -- Represent everything on a common affine open neighbourhood of `s`.
  obtain ⟨Va, hsVa, -, ra, hra⟩ :=
    TopCat.Presheaf.exists_mem_germ_eq_of_isBasis S.isBasis_affineOpens S.presheaf s a
  obtain ⟨Vb, hsVb, -, rb, hrb⟩ :=
    TopCat.Presheaf.exists_mem_germ_eq_of_isBasis S.isBasis_affineOpens S.presheaf s b
  obtain ⟨Vx, -, hsVx, ξ₀, hξ₀⟩ := exists_pushforwardGerm_eq f F s x
  obtain ⟨Vy, -, hsVy, η₀, hη₀⟩ := exists_pushforwardGerm_eq f F s y
  obtain ⟨_, ⟨V, -, rfl⟩, hsV, hVsub⟩ := S.isBasis_affineOpens.exists_subset_of_mem_open
    (show s ∈ ((Va ⊓ Vb) ⊓ (Vx ⊓ Vy) : S.Opens) from ⟨⟨hsVa, hsVb⟩, ⟨hsVx, hsVy⟩⟩)
    ((Va ⊓ Vb) ⊓ (Vx ⊓ Vy)).isOpen
  have hVle : V ≤ (Va ⊓ Vb) ⊓ (Vx ⊓ Vy) := hVsub
  have hVa : V ≤ Va := hVle.trans (inf_le_left.trans inf_le_left)
  have hVb : V ≤ Vb := hVle.trans (inf_le_left.trans inf_le_right)
  have hVx : V ≤ Vx := hVle.trans (inf_le_right.trans inf_le_left)
  have hVy : V ≤ Vy := hVle.trans (inf_le_right.trans inf_le_right)
  set r : Γ(S, V) := S.presheaf.map (homOfLE hVa).op ra with hr
  set t : Γ(S, V) := S.presheaf.map (homOfLE hVb).op rb with ht
  set ξ : Γ(F, f ⁻¹ᵁ V) := resF F (show f ⁻¹ᵁ V ≤ f ⁻¹ᵁ Vx from fun _ hz => hVx hz) ξ₀ with hξ
  set η : Γ(F, f ⁻¹ᵁ V) := resF F (show f ⁻¹ᵁ V ≤ f ⁻¹ᵁ Vy from fun _ hz => hVy hz) η₀ with hη
  have hgr : S.presheaf.germ V s hsV r = a := by
    rw [hr, S.presheaf.germ_res_apply (homOfLE hVa) s hsV ra, hra]
  have hgt : S.presheaf.germ V s hsV t = b := by
    rw [ht, S.presheaf.germ_res_apply (homOfLE hVb) s hsV rb, hrb]
  have hgξ : pushforwardGerm f F s V hsV ξ = x := by
    rw [hξ, pushforwardGerm_res f F s hVx hsV _ ξ₀, hξ₀]
  have hgη : pushforwardGerm f F s V hsV η = y := by
    rw [hη, pushforwardGerm_res f F s hVy hsV _ η₀, hη₀]
  -- The divisibility relation becomes an equation of sections after shrinking.
  have heq : pushforwardGerm f F s V hsV ((f.app V t) • ξ) =
      pushforwardGerm f F s V hsV ((f.app V r) • η) := by
    rw [pushforwardGerm_smul f F s V hsV t ξ, pushforwardGerm_smul f F s V hsV r η,
      hgr, hgt, hgξ, hgη, h]
  obtain ⟨V₁, hsV₁, hV₁aff, hV₁V, hV₁V', hsec⟩ := TopCat.Presheaf.germ_eq_of_isBasis
    S.isBasis_affineOpens ((Scheme.Modules.pushforward f).obj F).val.presheaf s hsV hsV heq
  have hpre₁ : (f ⁻¹ᵁ V₁ : X.Opens) ≤ f ⁻¹ᵁ V := fun _ hz => hV₁V hz
  set r₁ : Γ(S, V₁) := S.presheaf.map (homOfLE hV₁V).op r with hr₁
  set t₁ : Γ(S, V₁) := S.presheaf.map (homOfLE hV₁V).op t with ht₁
  set ξ₁ : Γ(F, f ⁻¹ᵁ V₁) := resF F hpre₁ ξ with hξ₁
  set η₁ : Γ(F, f ⁻¹ᵁ V₁) := resF F hpre₁ η with hη₁
  have happ := app_res_eq_appLE f hV₁V hpre₁
  have hsec' : (f.app V₁ t₁) • ξ₁ = (f.app V₁ r₁) • η₁ := by
    rw [ht₁, happ t, hξ₁, ← resF_smul_appLE f F (le_refl (f ⁻¹ᵁ V)) hpre₁ t ξ,
      hr₁, happ r, hη₁, ← resF_smul_appLE f F (le_refl (f ⁻¹ᵁ V)) hpre₁ r η]
    rwa [f.appLE_eq_app]
  have hgr₁ : S.presheaf.germ V₁ s hsV₁ r₁ = a := by
    rw [hr₁, S.presheaf.germ_res_apply (homOfLE hV₁V) s hsV₁ r, hgr]
  have hgt₁ : S.presheaf.germ V₁ s hsV₁ t₁ = b := by
    rw [ht₁, S.presheaf.germ_res_apply (homOfLE hV₁V) s hsV₁ t, hgt]
  -- Divide.
  obtain ⟨V₃, hsV₃, hV₃V₁, hpre₃, ζ, hζ⟩ := exists_resF_div f F hflat hV₁aff hsV₁ r₁ t₁
    (by rwa [hgr₁]) (by rwa [hgr₁, hgt₁]) ξ₁ η₁ hsec'
  refine ⟨pushforwardGerm f F s V₃ hsV₃ ζ, ?_⟩
  have c1 : pushforwardGerm f F s V₁ hsV₁ ξ₁ = x := by
    rw [hξ₁, pushforwardGerm_res f F s hV₁V hsV₁ hpre₁ ξ, hgξ]
  have c2 : pushforwardGerm f F s V₃ hsV₃ (resF F hpre₃ ξ₁) = x := by
    rw [pushforwardGerm_res f F s hV₃V₁ hsV₃ hpre₃ ξ₁, c1]
  rw [← c2, hζ, ← app_res_eq_appLE f hV₃V₁ hpre₃ r₁, pushforwardGerm_smul f F s V₃ hsV₃ _ ζ,
    S.presheaf.germ_res_apply (homOfLE hV₃V₁) s hsV₃ r₁, hgr₁]

/-- **[Stacks, Tag 0EY0] part (5).** Let `f : X ⟶ S` be a quasi-compact and quasi-separated
morphism of schemes and let `F` be an `𝒪_X`-module flat over `S`. A weakly regular sequence of
length two on `𝒪_{S,s}` acts weakly regularly on the stalk of `f_* F` at `s`.

The source assumes that `a` and `b` lie in the maximal ideal of `𝒪_{S,s}`; that hypothesis is
used there only for the depth consequences, so it is omitted here. The conclusion is weak
regularity rather than regularity because the pushforward stalk may be zero. -/
public theorem isWeaklyRegular_stalk_pushforward' [QuasiCompact f] [QuasiSeparated f]
    (hflat : IsFlatOver f.toLRSHom.toShHom F) (s : S) (a b : S.presheaf.stalk s)
    (hab : RingTheory.Sequence.IsWeaklyRegular (S.presheaf.stalk s) [a, b]) :
    RingTheory.Sequence.IsWeaklyRegular (TopCat.Presheaf.stalk (C := Ab.{u})
      ((Scheme.Modules.pushforward f).obj F).val.presheaf s) [a, b] := by
  rw [RingTheory.Sequence.isWeaklyRegular_cons_iff,
    RingTheory.Sequence.isWeaklyRegular_singleton_iff] at hab ⊢
  obtain ⟨ha, hb⟩ := hab
  refine ⟨isSMulRegular_stalk_pushforward f F hflat s a ha, ?_⟩
  intro X₁ X₂ hX
  obtain ⟨x₁, rfl⟩ := Submodule.Quotient.mk_surjective _ X₁
  obtain ⟨x₂, rfl⟩ := Submodule.Quotient.mk_surjective _ X₂
  have hX' : (Submodule.Quotient.mk (b • x₁) : QuotSMulTop a _) =
      Submodule.Quotient.mk (b • x₂) := by
    rwa [Submodule.Quotient.mk_smul, Submodule.Quotient.mk_smul]
  have hmem : b • (x₁ - x₂) ∈ a • (⊤ : Submodule (S.presheaf.stalk s) _) := by
    rw [smul_sub]
    exact (Submodule.Quotient.eq _).mp hX'
  obtain ⟨w, -, hw⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp hmem
  obtain ⟨z, hz⟩ := exists_smul_eq_of_smul_eq_smul f F hflat s a b ha hb (x₁ - x₂) w hw.symm
  refine (Submodule.Quotient.eq _).mpr ?_
  rw [hz]
  exact (Submodule.mem_smul_pointwise_iff_exists _ _ _).mpr ⟨z, Submodule.mem_top, rfl⟩

/-- **[Stacks, Tag 0EY0] part (5).** Let `f : X ⟶ S` be a quasi-compact and quasi-separated
morphism of schemes and let `F` be a quasi-coherent `𝒪_X`-module flat over `S`. If `a, b` is a
weakly regular sequence on `𝒪_{S,s}`, then it is weakly regular on the stalk of `f_* F` at `s`:
`a` is a nonzerodivisor on `(f_* F)_s` and `b` is a nonzerodivisor on
`(f_* F)_s / a (f_* F)_s`.

The source assumes in addition that `a` and `b` lie in the maximal ideal of `𝒪_{S,s}`; that
hypothesis is used there only to pass to the depth statements, so it is omitted. The conclusion
is weak regularity rather than regularity because the pushforward stalk may be zero.
Quasi-coherence of `F` is recorded because the source assumes it, but the proof does not use it:
see `isWeaklyRegular_stalk_pushforward'`. -/
@[stacks 0EY0 "pushforward_two_step"]
public theorem isWeaklyRegular_stalk_pushforward [QuasiCompact f] [QuasiSeparated f]
    [F.IsQuasicoherent] (s : S) (hflat : IsFlatOver f.toLRSHom.toShHom F)
    (a b : S.presheaf.stalk s)
    (hab : RingTheory.Sequence.IsWeaklyRegular (S.presheaf.stalk s) [a, b]) :
    RingTheory.Sequence.IsWeaklyRegular (TopCat.Presheaf.stalk (C := Ab.{u})
      ((Scheme.Modules.pushforward f).obj F).val.presheaf s) [a, b] :=
  isWeaklyRegular_stalk_pushforward' f F hflat s a b hab

end Stacks.AlgebraicGeometry.PushforwardRegularity
