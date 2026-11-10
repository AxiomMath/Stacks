module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Kunneth.OpenImmersionProductSquareStrictHenselization
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Kunneth.OpenProductLimitBaseChange
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Kunneth.StrictHenselizationLowerDimensionLimit
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Kunneth.OpenImmersionProductSquareFieldExtension
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Kunneth.OpenImmersionProductSquareClosedPoints
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.HigherBaseChangeUpperCornerIso
public import StacksFrontier.AlgebraicGeometry.Curves.GenusCurve.BaseChange
public import StacksFrontier.AlgebraicGeometry.TwistedSheaf.Dimension
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Dimension.ClosedPointChain
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The induction step of [Stacks, Tag 0F1H] at the points with a non-closed image

Let `K` be a field, `j : U ⟶ X` an open immersion of schemes of finite type over `K`, `Y` a scheme
of finite type over `K`, and `𝓕` an abelian sheaf on `U_étale` annihilated by an integer `n`
invertible in `K`. The proof of [Stacks, Tag 0F1H] is an induction on `dim(X) + dim(Y)`. Its
second and third paragraphs show, from the induction hypothesis, that the stalk of the base change
map `q⁻¹ R^i j_* 𝓕 ⟶ R^i h_* p⁻¹ 𝓕` of
```
Y ×_K X  ←-h-  Y ×_K U
   |q              |p
   X     ←-j-      U
```
is invertible at every geometric point `z̄` lying over a non-closed point of `Y ×_K X`:

* if `z ↦ x ∈ X` with `trdeg_K κ(x) > 0`, the square is pulled back to `X' = Spec(𝒪^{sh}_{X,x̄})`
  ([Stacks, Tag 0F09]); `X'` is the limit of affine schemes `X_i` of finite type over a separably
  closed field `L ⊇ K` with `dim(X_i) < dim(X)` ([Stacks, Tag 0F0U]); the square of `Y ×_K X_i`,
  which is the square of `Y_L ×_L X_i` over `L`, is covered by the induction hypothesis, and
  [Stacks, Tag 0EZT] passes to the limit;
* if `z ↦ y ∈ Y` with `trdeg_K κ(y) > 0`, the square is pulled back to `Y' = Spec(𝒪^{sh}_{Y,ȳ})
  = lim Y_i`, rewritten as the square of `Y' ×_L X_L` over `X_L ⟵ U_L` pasted with the square of
  the base change to `L` ([Stacks, Tag 0F1C]), and the same argument applies over `L`.

Since a point of `Y ×_K X` is closed exactly when both of its images are, this covers every
non-closed point.

## Main definitions

* `OpenImmersionProductSquare.BaseChangeBelowDimension d` — the statement of [Stacks, Tag 0F1H]
  for sheaves annihilated by one integer invertible in the field, in every degree, for all data
  with `dim(X) + dim(Y) < d`: the induction hypothesis.

## Main results

* `OpenImmersionProductSquare.isIso_stalk_higherBaseChangeMapAb_of_not_isClosed_snd_of_lt` — the
  case `z ↦ x`.
* `OpenImmersionProductSquare.isIso_stalk_higherBaseChangeMapAb_of_not_isClosed_fst_of_lt` — the
  case `z ↦ y`.
* `OpenImmersionProductSquare.isIso_stalk_higherBaseChangeMapAb_of_not_isClosed_of_lt` — every
  geometric point over a non-closed point of `Y ×_K X`, when `dim(X) + dim(Y) ≤ d`.

## References

* [Stacks Project, Tag 0F1H](https://stacks.math.columbia.edu/tag/0F1H)
* [Stacks Project, Tag 0F0U](https://stacks.math.columbia.edu/tag/0F0U)
* [Stacks Project, Tag 0EZT](https://stacks.math.columbia.edu/tag/0EZT)
* [Stacks Project, Tag 0F1C](https://stacks.math.columbia.edu/tag/0F1C)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology.OpenImmersionProductSquare

-- `Stacks.EtaleCohomology.smallEtaleDerivedBaseChangeAb`, at
-- `StacksFrontier/AlgebraicGeometry/EtaleCohomology/BaseChangeHigher/BaseChangeCondition.lean:220`,
-- is formed for the standard model of the derived categories; the base change to `L` of
-- [Stacks, Tag 0F1C] is read off it. The statements involve no derived category.
attribute [local instance] HasDerivedCategory.standard

/-! ### Auxiliary facts -/

/-- In `WithBot ℕ∞`, adding an element which is neither `⊥` nor `⊤` preserves strict
inequalities. -/
theorem withBotENat_add_lt_add_right {a b c : WithBot ℕ∞} (h : a < b) (hc : c ≠ ⊥)
    (hc' : c ≠ ⊤) : a + c < b + c := by
  obtain ⟨c, rfl⟩ := WithBot.ne_bot_iff_exists.1 hc
  have hc'' : c ≠ ⊤ := fun e => hc' (by rw [e]; rfl)
  obtain ⟨b, rfl⟩ := WithBot.ne_bot_iff_exists.1 (ne_bot_of_gt h)
  induction a using WithBot.recBotCoe with
  | bot => rw [WithBot.bot_add, ← WithBot.coe_add]; exact WithBot.bot_lt_coe _
  | coe a =>
    rw [← WithBot.coe_add, ← WithBot.coe_add, WithBot.coe_lt_coe] at *
    exact (ENat.add_lt_add_iff_right hc'').2 h

/-- A nonempty scheme of finite type over a field has dimension neither `⊥` nor `⊤`. -/
theorem topologicalKrullDim_ne_bot_and_ne_top {K : Type u} [Field K] {Y : Scheme.{u}}
    (sY : Y ⟶ Spec (.of K)) [LocallyOfFiniteType sY] [QuasiCompact sY] (y : Y) :
    topologicalKrullDim Y ≠ ⊥ ∧ topologicalKrullDim Y ≠ ⊤ := by
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace sY
  refine ⟨fun h => ?_, topologicalKrullDim_ne_top_of_locallyOfFiniteType K sY⟩
  exact ((topologicalKrullDim_eq_bot_iff_isEmpty _).1 h).false y

/-- An open immersion `U ⟶ X` of schemes of finite type over a field is quasi-compact: `X` is
noetherian, hence quasi-separated over the field. -/
@[ega "IV 1.7.7" "special case"]
theorem quasiCompact_of_finiteType {K : Type u} [Field K] {X U : Scheme.{u}}
    (sX : X ⟶ Spec (.of K)) (sU : U ⟶ Spec (.of K)) (j : U ⟶ X) (hj : j ≫ sX = sU)
    [LocallyOfFiniteType sX] [QuasiCompact sX] [QuasiCompact sU] : QuasiCompact j := by
  have := LocallyOfFiniteType.isLocallyNoetherian sX
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
  have : IsNoetherian X := ⟨⟩
  have : QuasiCompact (j ≫ sX) := hj ▸ inferInstance
  exact QuasiCompact.of_comp j sX

/-- An open immersion is quasi-separated, being a monomorphism. (Stated as a term: in the contexts
of this file the instance search for it does not terminate within the heartbeat budget.) -/
@[ega "IV 1.2.2" "open immersions"]
theorem quasiSeparated_of_isOpenImmersion {X U : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    QuasiSeparated j :=
  @IsSeparated.instQuasiSeparated _ _ j
    (@IsSeparated.isSeparated_of_mono _ _ j (IsOpenImmersion.mono j))

/-- A point of a scheme locally of finite type over a field which is not closed has a residue
field of positive transcendence degree. -/
theorem trdeg_residueField_pos_of_not_isClosed (k : Type u) [Field k] (X : Scheme.{u})
    (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f] (x : X) (hx : ¬ IsClosed ({x} : Set X)) :
    letI : Algebra k (X.residueField x) :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫ X.Γevaluation x).hom.toAlgebra
    0 < Algebra.trdeg k (X.residueField x) := by
  let : Algebra k (X.residueField x) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫ X.Γevaluation x).hom.toAlgebra
  refine pos_iff_ne_zero.2 fun h0 =>
    hx (isClosed_singleton_of_natTrdegResidueField_eq_zero k X f x ?_)
  change Cardinal.toNat (Algebra.trdeg k (X.residueField x)) = 0
  rw [h0]
  simp

/-- Inverse image of abelian sheaves preserves annihilation by `n`, for the inverse image
`etaleAbelianInverseImage` of the limit arguments. -/
theorem zsmul_etaleAbelianInverseImage_eq_zero {T T' : Scheme.{u}} (e : T' ⟶ T)
    (F : Sheaf (smallEtaleTopology T) Ab.{u + 1}) (n : ℤ)
    (hF : ∀ (V : T.Etale) (x : F.obj.obj (op V)), n • x = 0) (V : T'.Etale)
    (x : ((etaleAbelianInverseImage.{u, u + 1} e).obj F).obj.obj (op V)) : n • x = 0 := by
  let ι := (smallEtalePullbackAbIsoEtaleAbelianInverseImage e).app F
  have h1 : n • 𝟙 ((smallEtalePullbackAb e).obj F) = 0 :=
    (Stacks.Cohomology.ZModSheaf.zsmul_id_eq_zero_iff _ n).2 fun V x =>
      SmoothBaseChange.zsmul_pullbackAb_eq_zero e F n hF V.unop x
  have h2 : n • 𝟙 ((etaleAbelianInverseImage.{u, u + 1} e).obj F) = 0 := by
    calc n • 𝟙 ((etaleAbelianInverseImage.{u, u + 1} e).obj F)
        = ι.inv ≫ (n • 𝟙 ((smallEtalePullbackAb e).obj F)) ≫ ι.hom := by
          simp
      _ = 0 := by rw [h1]; simp
  exact (Stacks.Cohomology.ZModSheaf.zsmul_id_eq_zero_iff _ n).1 h2 (op V) x

/-- **A square isomorphic to a product square of an open immersion.** Let `j₁ : U₁ ⟶ X₁` be a
morphism of schemes over a field `L` and `Y₁` a scheme over `L`. For any cartesian squares
`P = X₁ ×_L Y₁` and `Q = U₁ ×_L Y₁` (with projections `fP, rP` and `eQ, rQ`) and the induced
`Q ⟶ P`, the base change map of the square `P ⟵ Q` over `X₁ ⟵ U₁` is invertible as soon as that
of the product square `Y₁ ×_L X₁ ⟵ Y₁ ×_L U₁` is: the upper corners are isomorphic.

The square is arbitrary, so that the statement is instantiated at the levels of an inverse
system exactly as these are spelled there. -/
theorem isIso_higherBaseChangeMapAb_of_isPullback_of_productSquare {L : Type u} [Field L]
    {X₁ U₁ Y₁ P Q : Scheme.{u}} (sX₁ : X₁ ⟶ Spec (.of L)) (sU₁ : U₁ ⟶ Spec (.of L))
    (sY₁ : Y₁ ⟶ Spec (.of L)) (j₁ : U₁ ⟶ X₁) (hj₁ : j₁ ≫ sX₁ = sU₁)
    (fP : P ⟶ X₁) (rP : P ⟶ Y₁) (hP : IsPullback fP rP sX₁ sY₁)
    (eQ : Q ⟶ U₁) (rQ : Q ⟶ Y₁) (hQ : IsPullback eQ rQ sU₁ sY₁)
    (hQP : Q ⟶ P) (w : hQP ≫ fP = eQ ≫ j₁) (hr : hQP ≫ rP = rQ) (i : ℕ)
    (G : Sheaf (smallEtaleTopology U₁) Ab.{u + 1})
    (H : IsIso ((higherBaseChangeMapAb (q sX₁ sY₁) j₁ (h sX₁ sU₁ sY₁ j₁ hj₁) (p sU₁ sY₁)
      (h_comp_q sX₁ sU₁ sY₁ j₁ hj₁) i).app G)) :
    IsIso ((higherBaseChangeMapAb fP j₁ hQP eQ w i).app G) := by
  let φ : P ≅ pullback sY₁ sX₁ := hP.flip.isoPullback
  let ψ : Q ≅ pullback sY₁ sU₁ := hQ.flip.isoPullback
  have hφψ : hQP ≫ φ.hom = ψ.hom ≫ h sX₁ sU₁ sY₁ j₁ hj₁ := by
    refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, IsPullback.isoPullback_hom_fst, hr, Category.assoc, h_comp_fst,
        IsPullback.isoPullback_hom_fst]
    · rw [Category.assoc, IsPullback.isoPullback_hom_snd, w, Category.assoc]
      change _ = ψ.hom ≫ (h sX₁ sU₁ sY₁ j₁ hj₁ ≫ q sX₁ sY₁)
      rw [h_comp_q, ← Category.assoc, IsPullback.isoPullback_hom_snd]
  exact (isIso_higherBaseChangeMapAb_app_iff_of_iso (q sX₁ sY₁) j₁ (h sX₁ sU₁ sY₁ j₁ hj₁)
    (p sU₁ sY₁) (h_comp_q sX₁ sU₁ sY₁ j₁ hj₁) φ ψ hQP hφψ fP
    (IsPullback.isoPullback_hom_snd _).symm eQ (IsPullback.isoPullback_hom_snd _).symm w i G).2 H

/-- If the image of a geometric point `z̄` in `S` is not closed, neither is the image of the
closed point of the residue field of `z̄ ⟶ W ⟶ S`. -/
private theorem not_isClosed_closedPoint_map_of_not_isClosed {W S : Scheme.{u}} (g : W ⟶ S)
    (z : GeometricPoint W) (hz : ¬ IsClosed ({g (z.hom default)} : Set S)) :
    ¬ IsClosed ({(z.map g).hom (IsLocalRing.closedPoint (z.map g).residueField)} : Set S) := by
  have e : (z.map g).hom (IsLocalRing.closedPoint (z.map g).residueField) =
      g (z.hom default) :=
    (Scheme.Hom.comp_apply z.hom g _).trans (congrArg _ (congrArg _ (Subsingleton.elim _ _)))
  exact fun hc => hz (e ▸ hc)

/-! ### The induction hypothesis -/

/-- **[Stacks, Tag 0F1H] below dimension `d`**, for sheaves annihilated by one integer: for every
field `K`, every open immersion `j : U ⟶ X` of schemes of finite type over `K` and every scheme
`Y` of finite type over `K` with `dim(X) + dim(Y) < d`, every integer `n` invertible in `K` and
every abelian sheaf `𝓕` on `U_étale` annihilated by `n`, the base change map
`q⁻¹ R^i j_* 𝓕 ⟶ R^i h_* p⁻¹ 𝓕` is invertible in every degree `i`. -/
def BaseChangeBelowDimension (d : WithBot ℕ∞) : Prop :=
  ∀ (K : Type u) [Field K] (X U Y : Scheme.{u}) (sX : X ⟶ Spec (.of K))
    (sU : U ⟶ Spec (.of K)) (sY : Y ⟶ Spec (.of K)) (j : U ⟶ X) [IsOpenImmersion j]
    (hj : j ≫ sX = sU) [LocallyOfFiniteType sX] [QuasiCompact sX] [LocallyOfFiniteType sU]
    [QuasiCompact sU] [LocallyOfFiniteType sY] [QuasiCompact sY],
    topologicalKrullDim X + topologicalKrullDim Y < d →
    ∀ (n : ℤ), IsUnit (n : K) → ∀ (𝓕 : Sheaf (smallEtaleTopology U) Ab.{u + 1}),
      (∀ (V : U.Etale) (x : 𝓕.obj.obj (op V)), n • x = 0) →
      ∀ i : ℕ, IsIso ((higherBaseChangeMapAb (q sX sY) j (h sX sU sY j hj) (p sU sY)
        (h_comp_q sX sU sY j hj) i).app 𝓕)

variable {d : WithBot ℕ∞} {K : Type u} [Field K] {X U Y : Scheme.{u}}
  (sX : X ⟶ Spec (.of K)) (sU : U ⟶ Spec (.of K)) (sY : Y ⟶ Spec (.of K))
  (j : U ⟶ X) [IsOpenImmersion j] (hj : j ≫ sX = sU) [LocallyOfFiniteType sX] [QuasiCompact sX]
  [LocallyOfFiniteType sU] [QuasiCompact sU] [LocallyOfFiniteType sY] [QuasiCompact sY]

omit [LocallyOfFiniteType sU] in
open OpenProductLimit in
/-- **The case `z ↦ x` with `x` not closed** ([Stacks, Tag 0F1H], second paragraph). Assume
[Stacks, Tag 0F1H] below dimension `d` and `dim(X) + dim(Y) ≤ d`. For `𝓕` annihilated by an
integer `n` invertible in `K` and a geometric point `z̄` of `Y ×_K X` whose image in `X` is not
closed, the stalk at `z̄` of `q⁻¹ R^i j_* 𝓕 ⟶ R^i h_* p⁻¹ 𝓕` is invertible.

With `x' : X' = Spec(𝒪^{sh}_{X,x̄}) ⟶ X`, it suffices that the base change map of the square
over `X'` is invertible
(`isIso_stalk_higherBaseChangeMapAb_of_strictHenselization_right`). `X'` is the limit of affine
schemes `X_i` of finite type over a separably closed `L ⊇ K` with `dim(X_i) < dim(X)`
(`AlgebraicGeometry.exists_isLimit_strictHenselization_of_topologicalKrullDim_lt`); the square of
`Y ×_K X_i` is that of `Y_L ×_L X_i` over `L`, with `dim(Y_L) = dim(Y)`, so the induction
hypothesis applies to it, and [Stacks, Tag 0EZT] passes to the limit
(`OpenProductLimit.isIso_higherBaseChangeMapAb_limit_of_levels`). -/
theorem isIso_stalk_higherBaseChangeMapAb_of_not_isClosed_snd_of_lt
    (IH : BaseChangeBelowDimension.{u} d)
    (hd : topologicalKrullDim X + topologicalKrullDim Y ≤ d) {n : ℤ} (hn : IsUnit (n : K))
    (𝓕 : Sheaf (smallEtaleTopology U) Ab.{u + 1})
    (h𝓕 : ∀ (V : U.Etale) (x : 𝓕.obj.obj (op V)), n • x = 0) (i : ℕ)
    (z : GeometricPoint (pullback sY sX))
    (hz : ¬ IsClosed ({pullback.snd sY sX (z.hom default)} : Set X)) :
    IsIso ((smallEtaleStalkAb z.hom).map ((higherBaseChangeMapAb (q sX sY) j
      (h sX sU sY j hj) (p sU sY) (h_comp_q sX sU sY j hj) i).app 𝓕)) := by
  have : QuasiCompact j := quasiCompact_of_finiteType sX sU j hj
  have : QuasiSeparated j := quasiSeparated_of_isOpenImmersion j
  obtain ⟨B, hS⟩ := BigEtaleSite.exists_contains X
  have hz' := not_isClosed_closedPoint_map_of_not_isClosed _ z hz
  obtain ⟨L, _, _, _, I, _, _, _, D, π, gL, pc, ⟨hlim⟩, hπ, haffD, haffmap, hft, hcompat, hdim⟩ :=
    exists_isLimit_strictHenselization_of_topologicalKrullDim_lt B hS sX (z.map (q sX sY))
      (trdeg_residueField_pos_of_not_isClosed K X sX _ hz')
  have : ∀ {i i' : Iᵒᵖ} (a : i ⟶ i'), IsAffineHom (D.map a) := fun a => haffmap a
  set x' := strictHenselizationToBase B X hS (z.map (q sX sY)) with hx'
  have hYd := topologicalKrullDim_ne_bot_and_ne_top sY (pullback.fst sY sX (z.hom default))
  have hYL : topologicalKrullDim (pullback (extensionMap K L) sY : Scheme.{u}) =
      topologicalKrullDim Y :=
    topologicalKrullDim_baseChange K L (pullback.snd (extensionMap K L) sY)
      (pullback.fst (extensionMap K L) sY) sY (IsPullback.of_hasPullback _ sY).flip
  have hnL : IsUnit (n : L) := by simpa using hn.map (algebraMap K L)
  refine isIso_stalk_higherBaseChangeMapAb_of_strictHenselization_right sX sU sY j hj B hS i hn
    𝓕 h𝓕 z (pullback.fst x' j) (pullback.snd x' j) (IsPullback.of_hasPullback x' j) ?_
  refine (NatTrans.isIso_app_iff_of_iso _
    ((smallEtalePullbackAbIsoEtaleAbelianInverseImage (pullback.snd x' j)).app 𝓕)).2 ?_
  have hQ : IsPullback (pullback.snd sY (pullback.snd x' j ≫ sU))
      (pullback.fst sY (pullback.snd x' j ≫ sU)) (pullback.fst x' j ≫ x' ≫ sX) sY := by
    rw [← Category.assoc, pullback.condition, Category.assoc, hj]
    exact (IsPullback.of_hasPullback _ _).flip
  refine isIso_higherBaseChangeMapAb_limit_of_levels D π j sX sY pc hlim x' hπ (pullback.fst x' j)
    (pullback.snd x' j) (IsPullback.of_hasPullback x' j) (pullback.snd sY (x' ≫ sX))
    (pullback.fst sY (x' ≫ sX)) (IsPullback.of_hasPullback sY (x' ≫ sX)).flip
    (pullback.snd sY (pullback.snd x' j ≫ sU)) (pullback.fst sY (pullback.snd x' j ≫ sU)) hQ
    (h (x' ≫ sX) (pullback.snd x' j ≫ sU) sY (pullback.fst x' j)
      (comp_comp_eq sX sU j hj x' _ _ (IsPullback.of_hasPullback x' j)))
    (h_comp_q _ _ _ _ _) (h_comp_fst _ _ _ _ _) i 𝓕 fun i' => ?_
  -- the level `i'`: the square of `Y ×_K X_{i'}`, which is the square of `Y_L ×_L X_{i'}`
  have := hft i'
  have : IsAffine (D.obj i') := haffD i'
  have : QuasiCompact (gL.app i') :=
    inferInstanceAs (QuasiCompact (show D.obj i' ⟶ Spec (.of L) from gL.app i'))
  let j₁ := (openLevelsInclusion D π j).app i'
  have hc₁ : ((productLevelsProjection D π sX sY).app i' ≫ gL.app i') ≫ extensionMap K L =
      pullback.snd ((π ≫ (Functor.const Iᵒᵖ).map sX).app i') sY ≫ sY := by
    rw [Category.assoc, hcompat i']
    exact pullback.condition
  have hc₂ : ((openProductLevelsProjection D π j sX sY).app i' ≫ j₁ ≫ gL.app i') ≫
      extensionMap K L =
      pullback.snd ((openLevelsInclusion D π j ≫ π ≫ (Functor.const Iᵒᵖ).map sX).app i') sY ≫
        sY := by
    rw [Category.assoc, Category.assoc, hcompat i']
    exact pullback.condition
  let rP : (productLevels D π sX sY).obj i' ⟶ pullback (extensionMap K L) sY :=
    pullback.lift _ _ hc₁
  let rQ : (openProductLevels D π j sX sY).obj i' ⟶ pullback (extensionMap K L) sY :=
    pullback.lift _ _ hc₂
  have sP : IsPullback (rP ≫ pullback.snd (extensionMap K L) sY)
      ((productLevelsProjection D π sX sY).app i') sY (gL.app i' ≫ extensionMap K L) := by
    have e₁ : rP ≫ pullback.snd (extensionMap K L) sY =
        pullback.snd ((π ≫ (Functor.const Iᵒᵖ).map sX).app i') sY := pullback.lift_snd _ _ _
    rw [e₁, hcompat i']
    exact (IsPullback.of_hasPullback _ _).flip
  have sQ : IsPullback (rQ ≫ pullback.snd (extensionMap K L) sY)
      ((openProductLevelsProjection D π j sX sY).app i') sY
      ((j₁ ≫ gL.app i') ≫ extensionMap K L) := by
    have e₁ : rQ ≫ pullback.snd (extensionMap K L) sY = pullback.snd
        ((openLevelsInclusion D π j ≫ π ≫ (Functor.const Iᵒᵖ).map sX).app i') sY :=
      pullback.lift_snd _ _ _
    rw [e₁, Category.assoc, hcompat i']
    exact (IsPullback.of_hasPullback _ _).flip
  have hP : IsPullback ((productLevelsProjection D π sX sY).app i') rP (gL.app i')
      (pullback.fst (extensionMap K L) sY) :=
    (IsPullback.of_right sP (pullback.lift_fst _ _ _)
      (IsPullback.of_hasPullback (extensionMap K L) sY).flip).flip
  have hQ' : IsPullback ((openProductLevelsProjection D π j sX sY).app i') rQ (j₁ ≫ gL.app i')
      (pullback.fst (extensionMap K L) sY) :=
    (IsPullback.of_right sQ (pullback.lift_fst _ _ _)
      (IsPullback.of_hasPullback (extensionMap K L) sY).flip).flip
  have hr : (openProductLevelsInclusion D π j sX sY).app i' ≫ rP = rQ := by
    refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst]
      exact openProductLevelsInclusion_app_fst_assoc D π j sX sY i' (gL.app i')
    · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd]
      exact openProductLevelsInclusion_app_snd D π j sX sY i'
  refine isIso_higherBaseChangeMapAb_of_isPullback_of_productSquare (gL.app i')
    (j₁ ≫ gL.app i') (pullback.fst (extensionMap K L) sY) j₁ rfl _ rP hP _ rQ hQ' _
    (isPullback_level D π j sX sY i').w hr i _ ?_
  refine IH L (D.obj i') _ (pullback (extensionMap K L) sY) (gL.app i') (j₁ ≫ gL.app i')
    (pullback.fst (extensionMap K L) sY) j₁ rfl ?_ n hnL _
    (zsmul_etaleAbelianInverseImage_eq_zero _ 𝓕 n h𝓕) i
  rw [hYL]
  exact (withBotENat_add_lt_add_right (hdim i') hYd.1 hYd.2).trans_le hd

omit [QuasiCompact sY] in
open OpenProductLimit in
/-- **The case `z ↦ y` with `y` not closed** ([Stacks, Tag 0F1H], third paragraph). Assume
[Stacks, Tag 0F1H] below dimension `d` and `dim(X) + dim(Y) ≤ d`. For `𝓕` annihilated by an
integer `n` invertible in `K` and a geometric point `z̄` of `Y ×_K X` whose image in `Y` is not
closed, the stalk at `z̄` of `q⁻¹ R^i j_* 𝓕 ⟶ R^i h_* p⁻¹ 𝓕` is invertible.

With `b : Y' = Spec(𝒪^{sh}_{Y,ȳ}) ⟶ Y`, it suffices that the base change map of the square of
`j` and `Y'` is invertible (`isIso_stalk_higherBaseChangeMapAb_of_strictHenselization_left`).
`Y'` is the limit of affine schemes `Y_i` of finite type over a separably closed `L ⊇ K` with
`dim(Y_i) < dim(Y)`, and `Y' ×_K X = Y' ×_L X_L`. The squares of `Y_i ×_L X_L` over
`X_L ⟵ U_L` are covered by the induction hypothesis (`dim(X_L) = dim(X)`), [Stacks, Tag 0EZT]
passes to the limit (`OpenProductLimit.isIso_higherBaseChangeMapAb_limit_of_factorLevels`), and
the square of `Y' ×_L X_L` pasted with the square of `X_L ⟵ U_L` over `X ⟵ U`, whose base change
map is invertible by [Stacks, Tag 0F1C], is the square of `Y'` ([Stacks, Tag 0E46]). -/
theorem isIso_stalk_higherBaseChangeMapAb_of_not_isClosed_fst_of_lt
    (IH : BaseChangeBelowDimension.{u} d)
    (hd : topologicalKrullDim X + topologicalKrullDim Y ≤ d) {n : ℤ} (hn : IsUnit (n : K))
    (𝓕 : Sheaf (smallEtaleTopology U) Ab.{u + 1})
    (h𝓕 : ∀ (V : U.Etale) (x : 𝓕.obj.obj (op V)), n • x = 0) (i : ℕ)
    (z : GeometricPoint (pullback sY sX))
    (hz : ¬ IsClosed ({pullback.fst sY sX (z.hom default)} : Set Y)) :
    IsIso ((smallEtaleStalkAb z.hom).map ((higherBaseChangeMapAb (q sX sY) j
      (h sX sU sY j hj) (p sU sY) (h_comp_q sX sU sY j hj) i).app 𝓕)) := by
  have : QuasiCompact j := quasiCompact_of_finiteType sX sU j hj
  have : QuasiSeparated j := quasiSeparated_of_isOpenImmersion j
  obtain ⟨B, hS⟩ := BigEtaleSite.exists_contains Y
  have hz' := not_isClosed_closedPoint_map_of_not_isClosed _ z hz
  obtain ⟨L, _, _, _, I, _, _, _, D, π, gL, pc, ⟨hlim⟩, hπ, haffD, haffmap, hft, hcompat, hdim⟩ :=
    exists_isLimit_strictHenselization_of_topologicalKrullDim_lt B hS sY
      (z.map (pullback.fst sY sX)) (trdeg_residueField_pos_of_not_isClosed K Y sY _ hz')
  have : ∀ {i i' : Iᵒᵖ} (a : i ⟶ i'), IsAffineHom (D.map a) := fun a => haffmap a
  set b := strictHenselizationToBase B Y hS (z.map (pullback.fst sY sX)) with hb
  have hXd := topologicalKrullDim_ne_bot_and_ne_top sX (pullback.snd sY sX (z.hom default))
  have hXL : topologicalKrullDim (pullback (extensionMap K L) sX : Scheme.{u}) =
      topologicalKrullDim X :=
    topologicalKrullDim_baseChange K L (pullback.snd (extensionMap K L) sX)
      (pullback.fst (extensionMap K L) sX) sX (IsPullback.of_hasPullback _ sX).flip
  have hnL : IsUnit (n : L) := by simpa using hn.map (algebraMap K L)
  refine isIso_stalk_higherBaseChangeMapAb_of_strictHenselization_left sX sU sY j hj B hS i hn
    𝓕 h𝓕 z ?_
  -- the base change `j_L : U_L ⟶ X_L` of `j`
  have : IsOpenImmersion (extensionOpen K L sX sU j hj) :=
    MorphismProperty.of_isPullback (P := @IsOpenImmersion)
      (FieldExtensionBaseChange.isPullback_baseChangeMap _ sX sU j hj).flip inferInstance
  have : QuasiCompact (extensionOpen K L sX sU j hj) :=
    MorphismProperty.of_isPullback (P := @QuasiCompact)
      (FieldExtensionBaseChange.isPullback_baseChangeMap _ sX sU j hj).flip inferInstance
  have : QuasiSeparated (extensionOpen K L sX sU j hj) :=
    quasiSeparated_of_isOpenImmersion _
  -- the structure morphism `Y' ⟶ Spec L`
  let i₀ : Iᵒᵖ := op (Classical.arbitrary I)
  let gY : strictHenselization B Y hS (z.map (pullback.fst sY sX)) ⟶ Spec (.of L) :=
    pc.app i₀ ≫ gL.app i₀
  have hkey : ∀ {k i' : Iᵒᵖ} (f : k ⟶ i'), pc.app i' ≫ gL.app i' = pc.app k ≫ gL.app k :=
    fun {k i'} f => by
      have h₁ : pc.app i' = pc.app k ≫ D.map f := (Category.id_comp _).symm.trans (pc.naturality f)
      have h₂ : D.map f ≫ gL.app i' = gL.app k := (gL.naturality f).trans (Category.comp_id _)
      rw [h₁, Category.assoc, h₂]
  have hy : ∀ i', pc.app i' ≫ gL.app i' = gY := fun i' =>
    (hkey (IsCofiltered.minToLeft i' i₀)).trans (hkey (IsCofiltered.minToRight i' i₀)).symm
  have hgY : gY ≫ extensionMap K L = b ≫ sY := by
    change (pc.app i₀ ≫ gL.app i₀) ≫ extensionMap K L = b ≫ sY
    rw [Category.assoc, hcompat i₀, ← Category.assoc, hπ i₀]
  -- the square of `Y' ×_L X_L` over `X_L ⟵ U_L`, as a limit
  have hQ : IsPullback (pullback.fst gY (pullback.fst (extensionMap K L) sU))
      (pullback.snd gY (pullback.fst (extensionMap K L) sU)) gY
      (extensionOpen K L sX sU j hj ≫ pullback.fst (extensionMap K L) sX) := by
    rw [extensionOpen_fst]
    exact IsPullback.of_hasPullback _ _
  let hL : pullback gY (pullback.fst (extensionMap K L) sU) ⟶
      pullback gY (pullback.fst (extensionMap K L) sX) :=
    pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ extensionOpen K L sX sU j hj) (by
      rw [Category.assoc, extensionOpen_fst]
      exact pullback.condition)
  have hhLr : hL ≫ pullback.snd gY (pullback.fst (extensionMap K L) sX) =
      pullback.snd gY (pullback.fst (extensionMap K L) sU) ≫ extensionOpen K L sX sU j hj :=
    pullback.lift_snd _ _ _
  have hupper := isIso_higherBaseChangeMapAb_limit_of_factorLevels D gL
    (extensionOpen K L sX sU j hj) (pullback.fst (extensionMap K L) sX) pc hlim gY hy
    (pullback.fst gY _) (pullback.snd gY _) (IsPullback.of_hasPullback _ _)
    (pullback.fst gY _) (pullback.snd gY _) hQ hL (pullback.lift_fst _ _ _) hhLr i
    ((smallEtalePullbackAb (pullback.snd (extensionMap K L) sU)).obj 𝓕) fun i' => by
      -- every object and morphism of the level is spelled as the level spells it
      let XL₁ := ((Functor.const Iᵒᵖ).obj (pullback (extensionMap K L) sX)).obj i'
      let UL₁ := ((Functor.const Iᵒᵖ).obj (pullback (extensionMap K L) sU)).obj i'
      let sXL₁ : XL₁ ⟶ Spec (.of L) := pullback.fst (extensionMap K L) sX
      let sUL₁ : UL₁ ⟶ Spec (.of L) := pullback.fst (extensionMap K L) sU
      let jL₁ := ((Functor.const Iᵒᵖ).map (extensionOpen K L sX sU j hj)).app i'
      have := hft i'
      have : IsAffine (D.obj i') := haffD i'
      have : QuasiCompact (gL.app i') :=
        inferInstanceAs (QuasiCompact (show D.obj i' ⟶ Spec (.of L) from gL.app i'))
      have : IsOpenImmersion jL₁ := inferInstanceAs (IsOpenImmersion (extensionOpen K L sX sU j hj))
      have : LocallyOfFiniteType sXL₁ :=
        inferInstanceAs (LocallyOfFiniteType (pullback.fst (extensionMap K L) sX))
      have : QuasiCompact sXL₁ :=
        inferInstanceAs (QuasiCompact (pullback.fst (extensionMap K L) sX))
      have : LocallyOfFiniteType sUL₁ :=
        inferInstanceAs (LocallyOfFiniteType (pullback.fst (extensionMap K L) sU))
      have : QuasiCompact sUL₁ :=
        inferInstanceAs (QuasiCompact (pullback.fst (extensionMap K L) sU))
      have hj₁ : jL₁ ≫ sXL₁ = sUL₁ := extensionOpen_fst K L sX sU j hj
      have hP₁ : IsPullback ((factorProductLevelsProjection D gL
          (pullback.fst (extensionMap K L) sX)).app i')
          ((baseChangeHorizontal D gL (pullback.fst (extensionMap K L) sX)).app i') sXL₁
          (gL.app i') :=
        (isPullback_baseChangeStage D gL (pullback.fst (extensionMap K L) sX) i').flip
      have hQ₁ : IsPullback ((factorOpenProductLevelsProjection D gL
          (extensionOpen K L sX sU j hj) (pullback.fst (extensionMap K L) sX)).app i')
          ((baseChangeHorizontal D gL (extensionOpen K L sX sU j hj ≫
            pullback.fst (extensionMap K L) sX)).app i') sUL₁ (gL.app i') := by
        change IsPullback _ _ (pullback.fst (extensionMap K L) sU) _
        rw [← extensionOpen_fst K L sX sU j hj]
        exact (isPullback_baseChangeStage D gL _ i').flip
      refine isIso_higherBaseChangeMapAb_of_isPullback_of_productSquare (X₁ := XL₁) (U₁ := UL₁)
        sXL₁ sUL₁ (gL.app i') jL₁ hj₁ _ _ hP₁ _ _ hQ₁ _
        (isPullback_factorLevel D gL (extensionOpen K L sX sU j hj)
          (pullback.fst (extensionMap K L) sX) i').w
        (factorOpenProductLevelsInclusion_app_fst D gL (extensionOpen K L sX sU j hj)
          (pullback.fst (extensionMap K L) sX) i') i _ ?_
      refine IH L XL₁ UL₁ (D.obj i') sXL₁ sUL₁ (gL.app i') jL₁ hj₁ ?_ n hnL _
        (SmoothBaseChange.zsmul_pullbackAb_eq_zero _ 𝓕 n h𝓕) i
      change topologicalKrullDim (pullback (extensionMap K L) sX : Scheme.{u}) +
        topologicalKrullDim (D.obj i') < d
      rw [hXL, add_comm]
      exact (withBotENat_add_lt_add_right (hdim i') hXd.1 hXd.2).trans_le
        ((add_comm _ _).le.trans hd)
  -- the square of `X_L ⟵ U_L` over `X ⟵ U`, by [Stacks, Tag 0F1C]
  let M := (DerivedCategory.Plus.singleFunctor (Sheaf (smallEtaleTopology U) Ab.{u + 1}) 0).obj 𝓕
  have hM : ∀ r : ℤ, Stacks.Torsion.IsPrimeToCharacteristicTorsion _ (ringExpChar K)
      ((DerivedCategory.Plus.homologyFunctor _ r).obj M) :=
    BaseChangeOverField.isPrimeToCharacteristicTorsion_homology_single 𝓕
      (BaseChangeOverField.isPrimeToCharacteristicTorsion_of_zsmul_eq_zero K hn 𝓕 h𝓕)
  have hlow : IsIso ((higherBaseChangeMapAb (pullback.snd (extensionMap K L) sX) j
      (extensionOpen K L sX sU j hj) (pullback.snd (extensionMap K L) sU)
      (FieldExtensionBaseChange.baseChangeMap_snd _ sX sU j hj) i).app 𝓕) :=
    isIso_higherBaseChangeMapAb_app_of_isIso_derived _ _ _ _ _ 𝓕
      (FieldExtensionBaseChange.isIso_smallEtaleDerivedBaseChangeAb_baseChange K L sX sU j hj
        smoothLimitBaseChange_holds M hM) i
  have h₁ : IsIso ((smallEtalePullbackAb (pullback.snd gY (pullback.fst (extensionMap K L) sX))).map
      ((higherBaseChangeMapAb (pullback.snd (extensionMap K L) sX) j
        (extensionOpen K L sX sU j hj) (pullback.snd (extensionMap K L) sU)
        (FieldExtensionBaseChange.baseChangeMap_snd _ sX sU j hj) i).app 𝓕)) := inferInstance
  have hrect := (isIso_map_higherBaseChangeMapAb_paste_iff_of_isIso_first j
    (extensionOpen K L sX sU j hj) hL (pullback.snd (extensionMap K L) sX)
    (pullback.snd gY _) (pullback.snd (extensionMap K L) sU) (pullback.snd gY _)
    (FieldExtensionBaseChange.baseChangeMap_snd _ sX sU j hj) hhLr i 𝓕 (𝟭 _) h₁).2 hupper
  -- `Y' ×_L X_L = Y' ×_K X` and `Y' ×_L U_L = Y' ×_K U`
  have tX := (IsPullback.of_hasPullback gY (pullback.fst (extensionMap K L) sX)).flip.paste_horiz
    (IsPullback.of_hasPullback (extensionMap K L) sX).flip
  have tU := (IsPullback.of_hasPullback gY (pullback.fst (extensionMap K L) sU)).flip.paste_horiz
    (IsPullback.of_hasPullback (extensionMap K L) sU).flip
  rw [hgY] at tX tU
  let φ := tX.flip.isoPullback
  let ψ := tU.flip.isoPullback
  have hφψ : hL ≫ φ.hom = ψ.hom ≫ h sX sU (b ≫ sY) j hj := by
    refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, IsPullback.isoPullback_hom_fst, pullback.lift_fst, Category.assoc,
        h_comp_fst, IsPullback.isoPullback_hom_fst]
    · rw [Category.assoc, IsPullback.isoPullback_hom_snd, ← Category.assoc, pullback.lift_snd,
        Category.assoc, Category.assoc, FieldExtensionBaseChange.baseChangeMap_snd]
      change _ = ψ.hom ≫ (h sX sU (b ≫ sY) j hj ≫ q sX (b ≫ sY))
      rw [h_comp_q, ← Category.assoc ψ.hom, IsPullback.isoPullback_hom_snd, Category.assoc]
  exact (isIso_higherBaseChangeMapAb_app_iff_of_iso (q sX (b ≫ sY)) j (h sX sU (b ≫ sY) j hj)
    (p sU (b ≫ sY)) (h_comp_q sX sU (b ≫ sY) j hj) φ ψ hL hφψ _
    (IsPullback.isoPullback_hom_snd _).symm _ (IsPullback.isoPullback_hom_snd _).symm _ i 𝓕).1
    hrect

/-- **The stalks at the points over non-closed points** ([Stacks, Tag 0F1H]). Assume
[Stacks, Tag 0F1H] below dimension `d` and `dim(X) + dim(Y) ≤ d`. For `𝓕` annihilated by an
integer `n` invertible in `K`, the stalk of `q⁻¹ R^i j_* 𝓕 ⟶ R^i h_* p⁻¹ 𝓕` is invertible at
every geometric point of `Y ×_K X` lying over a non-closed point: one of its images in `X` and
`Y` is not closed. -/
theorem isIso_stalk_higherBaseChangeMapAb_of_not_isClosed_of_lt
    (IH : BaseChangeBelowDimension.{u} d)
    (hd : topologicalKrullDim X + topologicalKrullDim Y ≤ d) {n : ℤ} (hn : IsUnit (n : K))
    (𝓕 : Sheaf (smallEtaleTopology U) Ab.{u + 1})
    (h𝓕 : ∀ (V : U.Etale) (x : 𝓕.obj.obj (op V)), n • x = 0) (i : ℕ)
    (z : GeometricPoint (pullback sY sX)) (hz : ¬ IsClosed ({z.hom default} : Set _)) :
    IsIso ((smallEtaleStalkAb z.hom).map ((higherBaseChangeMapAb (q sX sY) j
      (h sX sU sY j hj) (p sU sY) (h_comp_q sX sU sY j hj) i).app 𝓕)) :=
  isIso_stalk_higherBaseChangeMapAb_of_not_isClosed sX sU sY j hj i 𝓕
    (fun z hz => isIso_stalk_higherBaseChangeMapAb_of_not_isClosed_snd_of_lt sX sU sY j hj IH hd
      hn 𝓕 h𝓕 i z hz)
    (fun z hz => isIso_stalk_higherBaseChangeMapAb_of_not_isClosed_fst_of_lt sX sU sY j hj IH hd
      hn 𝓕 h𝓕 i z hz) z hz

end Stacks.EtaleCohomology.OpenImmersionProductSquare

end
