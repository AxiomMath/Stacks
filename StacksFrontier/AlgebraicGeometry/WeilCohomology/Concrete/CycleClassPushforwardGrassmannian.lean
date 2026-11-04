module

public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.GrassmannianTowerEmbedding
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.GrassmannianClosedEmbedding
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.ExtendableConormalReduction
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.ClosedImmersionGysinPushforward
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.CycleClassWeilThree
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.WeilChernPerfectPairing
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.ClopenDecompositionChow

/-!
# `γ` commutes with pushforward, granted the closed immersions and the Grassmannians

Let (D0), (D1), (D2') satisfy (A1)–(A7) (`Stacks.WeilCohomology.WeilChernData`). This file proves
that `γ` commutes with pushforward along every morphism `f : X ⟶ Y` of nonempty equidimensional
smooth projective schemes over `k` provided

* `i_*1 = γ([Z])` for every closed immersion `i : Z ⟶ X` of nonempty equidimensional smooth
  projective schemes (the hypothesis of [Stacks, Tag 0FIP]), and
* `γ` commutes with pushforward along every projection `V × G(l, n) ⟶ V`, `0 < l < n` (the
  conclusion of [Stacks, Tag 0FIQ]).

For `X` connected the proof is the following, which replaces the splitting principle and
Bertini's theorem of the source by Grassmannians. Embed `X` into a Grassmannian and replace `f`
by the closed immersion `(f, ψ) : X ⟶ Y × G(l, n)` followed by the projection. For a closed
immersion `f` and `α ∈ CH^p(X)`, write `α = ch(x) ∩ [X]` in `CH^*(X) ⊗ 𝐐` (Stacks 0FEY),
`c x = 1 ⊗ x₀` with `x₀ ∈ K₀(Vect(X))`, and embed `X` into a tower of Grassmannian bundles
`π : W ⟶ Y` by `j` with `x₀ = j^*y₀`
(`Stacks.WeilCohomology.SmoothProjectiveScheme.exists_grassmannianTowerEmbedding`). Then
`cα` is rationally `j^!(ch(y₀) ∩ [W])` (Stacks 0FF8), so `γ(j_*α) = j_*γ(α)`
(`Stacks.WeilCohomology.WeilData.cycleClass_pushforward_of_closedImmersion_of_lciGysinRational`),
and `π` is a composite of projections from Grassmannian bundles.

## Main definitions

* `Stacks.WeilCohomology.WeilData.PushforwardCompatible`: `γ` commutes with `f_*`.

## Main results

* `Stacks.WeilCohomology.WeilChernData.pushforwardCompatible_of_connectedSpace`: the case of a
  connected source.
* `Stacks.WeilCohomology.WeilChernData.cycleClassPushforward_of_grassmannian`: `γ` commutes with
  pushforward, by induction on the number of connected components of the source.
-/

@[expose] public noncomputable section

open CategoryTheory hiding ConnectedComponents
open CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.VectorBundleKZero Stacks.Chow
open scoped TensorProduct

universe u w

namespace Stacks.WeilCohomology

variable {k : Type u} [Field k]

namespace WeilData

variable {F : Type w} [Field F] (W : WeilData k F) (hA : W.PerfectPairing)

/-- **`γ` commutes with pushforward along `f`**: `γ(f_*α) = f_*γ(α)` for `α ∈ CH^p(X)`, whenever
`X` and `Y` are nonempty and equidimensional (axiom (C)(b) for the single morphism `f`). -/
def PushforwardCompatible {X Y : (SmoothProjectiveScheme k).FullSubcategory} (f : X ⟶ Y) : Prop :=
  ∀ (d e : ℕ) (hX : IsNonemptyEquidimensional X d) (hY : IsNonemptyEquidimensional Y e)
    (p q : ℤ) (h : q = p + e - d) (α : codimensionChowGroup k X.obj.hom p),
    W.cycleClass Y q (equidimensionalPushforward f d e p q h α) =
      W.pushforward hA f hX hY (2 * p) p (2 * q) q (by omega) (by omega) (W.cycleClass X p α)

/-- Axiom (C)(b) is compatibility along every morphism. -/
theorem cycleClassPushforward_iff :
    W.CycleClassPushforward hA ↔
      ∀ {X Y : (SmoothProjectiveScheme k).FullSubcategory} (f : X ⟶ Y),
        W.PushforwardCompatible hA f :=
  ⟨fun h _ _ f d e hX hY p q hq α => h f d e hX hY p q hq α,
    fun h _ _ f d e hX hY p q hq α => h f d e hX hY p q hq α⟩

variable {W hA}

/-- Compatibility is stable under composition through a nonempty equidimensional middle. -/
theorem PushforwardCompatible.comp {X Y Z : (SmoothProjectiveScheme k).FullSubcategory} {f : X ⟶ Y}
    {g : Y ⟶ Z} {e : ℕ} (hY : IsNonemptyEquidimensional Y e)
    (hrat : ∀ (n : ℤ) (a a' : codimensionChowGroup k Z.obj.hom n),
      codimensionToRationalChow k Z.obj.hom n a = codimensionToRationalChow k Z.obj.hom n a' →
        W.cycleClass Z n a = W.cycleClass Z n a')
    (hf : W.PushforwardCompatible hA f) (hg : W.PushforwardCompatible hA g) :
    W.PushforwardCompatible hA (f ≫ g) := by
  intro d c hX hZ p r hr α
  exact W.cycleClass_pushforward_comp hA f g hX hY hZ hrat p (p + e - d) r rfl (by omega) α
    (hf d e hX hY p _ rfl α) (hg e c hY hZ _ r (by omega) _)

end WeilData

namespace WeilChernData

open SmoothProjectiveScheme

variable {F : Type w} [Field F] [CharZero F] (𝔚 : WeilChernData k F)

/-- The cycle class map of `𝔚` depends only on rational classes. -/
theorem cycleClass_congr (X : (SmoothProjectiveScheme k).FullSubcategory) (n : ℤ)
    (a a' : codimensionChowGroup k X.obj.hom n)
    (haa' : codimensionToRationalChow k X.obj.hom n a =
      codimensionToRationalChow k X.obj.hom n a') :
    𝔚.toWeilData.cycleClass X n a = 𝔚.toWeilData.cycleClass X n a' :=
  𝔚.isCohomologicalChernCharacter.toWeilData_cycleClass_congr 𝔚.coproduct 𝔚.projectiveBundle
    𝔚.kunneth 𝔚.trace X n a a' haa'

/-- Axiom (C)(a) for the data of `𝔚`. -/
theorem cycleClassPullback : 𝔚.toWeilData.CycleClassPullback :=
  𝔚.isCohomologicalChernCharacter.cycleClassPullback_toWeilData 𝔚.coproduct 𝔚.projectiveBundle
    𝔚.kunneth 𝔚.trace

/-- Axiom (C)(c) for the data of `𝔚`. -/
theorem cycleClassMul : 𝔚.toWeilData.CycleClassMul :=
  𝔚.isCohomologicalChernCharacter.cycleClassMul_toWeilData 𝔚.coproduct 𝔚.projectiveBundle
    𝔚.kunneth 𝔚.trace

variable {𝔚}
variable (hG : ∀ (X : (SmoothProjectiveScheme k).FullSubcategory) (l n : ℕ), 0 < l → l < n →
      ∀ (d d' : ℕ)
      (hX : IsNonemptyEquidimensional X d)
      (hP : IsNonemptyEquidimensional (prod X (SmoothProjectiveScheme.grassmannian k l n)) d')
      (p q : ℤ) (hq : q = p + d - d')
      (α : codimensionChowGroup k (prod X (SmoothProjectiveScheme.grassmannian k l n)).obj.hom p),
      𝔚.toWeilData.cycleClass X q (equidimensionalPushforward (fst X _) d' d p q hq α) =
        𝔚.toWeilData.pushforward 𝔚.perfectPairing (fst X _) hP hX (2 * p) p (2 * q) q (by omega)
          (by omega) (𝔚.toWeilData.cycleClass _ p α))
  (hi : ∀ {Z X : (SmoothProjectiveScheme k).FullSubcategory} (i : Z ⟶ X)
      [IsClosedImmersion i.hom.left]
      {e d : ℕ} (hZ : IsNonemptyEquidimensional Z e) (hX : IsNonemptyEquidimensional X d)
      (c : ℤ) (hc : c = d - e),
      𝔚.toWeilData.pushforward 𝔚.perfectPairing i hZ hX 0 0 (2 * c) c (by omega) (by omega)
          (𝔚.toWeilData.unitTw Z 0 0 rfl) =
        𝔚.toWeilData.cycleClass X c (closedSubschemeClass X.obj.hom i.hom.left c))

include hi in
/-- `γ` commutes with pushforward along the identity. -/
theorem pushforwardCompatible_id (X : (SmoothProjectiveScheme k).FullSubcategory) :
    𝔚.toWeilData.PushforwardCompatible 𝔚.perfectPairing (𝟙 X) := by
  intro d e hX hY p q hq α
  obtain rfl : d = e :=
    relativeDimension_unique hX.nonempty.some hX.relativeDimension hY.relativeDimension
  obtain rfl : q = p + ((d : ℤ) - d) := by omega
  have : IsClosedImmersion (𝟙 X : X ⟶ X).hom.left := by
    show IsClosedImmersion (𝟙 _)
    infer_instance
  exact 𝔚.toWeilData.cycleClass_pushforward_of_closedImmersion_of_retraction 𝔚.perfectPairing
    𝔚.cycleClassPullback 𝔚.cycleClassMul (𝔚.cycleClass_congr X) (𝟙 X) (𝟙 X)
    (Category.id_comp _) hX hY _ rfl (hi (𝟙 X) hX hY _ rfl) p α

include hG hi in
/-- **`γ` commutes with pushforward along a tower of Grassmannian bundles** with nonempty
source, which is then nonempty and equidimensional. -/
theorem pushforwardCompatible_of_isGrassmannianTower
    {V Y : (SmoothProjectiveScheme k).FullSubcategory}
    {π : V ⟶ Y} (hπ : IsGrassmannianTower π) {e : ℕ} (hY : IsNonemptyEquidimensional Y e)
    (hV : Nonempty V.obj.left) :
    ∃ dV, IsNonemptyEquidimensional V dV ∧
      𝔚.toWeilData.PushforwardCompatible 𝔚.perfectPairing π := by
  induction hπ with
  | id Y => exact ⟨e, hY, pushforwardCompatible_id hi Y⟩
  | comp π l n hl hln hπ ih =>
    rename_i V' Y'
    have hV' : Nonempty V'.obj.left :=
      ⟨(fst V' (SmoothProjectiveScheme.grassmannian k l n)).hom.left.base hV.some⟩
    have hGne : Nonempty (SmoothProjectiveScheme.grassmannian k l n).obj.left :=
      ⟨(snd V' (SmoothProjectiveScheme.grassmannian k l n)).hom.left.base hV.some⟩
    obtain ⟨dV, hdV, hc⟩ := ih hY hV'
    refine ⟨_, isNonemptyEquidimensional_prod hdV
      (isNonemptyEquidimensional_grassmannian l n hGne), ?_⟩
    exact WeilData.PushforwardCompatible.comp hdV (𝔚.cycleClass_congr Y')
      (fun d d' hX hP p q hq α => hG V' l n hl hln d' d hP hX p q hq α) hc

include hG hi in
/-- **`γ` commutes with pushforward along a closed immersion with connected source.** -/
theorem pushforwardCompatible_of_isClosedImmersion
    {X Y : (SmoothProjectiveScheme k).FullSubcategory}
    (f : X ⟶ Y) [IsClosedImmersion f.hom.left] [ConnectedSpace X.obj.left] :
    𝔚.toWeilData.PushforwardCompatible 𝔚.perfectPairing f := by
  intro d e hX hY p q hq α
  have := isNoetherian_of_compactSpace (C := fieldChowSituation k) X.obj.hom
  set chX := rationalChernCharacterAlgEquiv (isRegular_of_smooth_over_field X.obj.hom)
    (exists_bounds_relativeDimension_fieldChowSituation k X.obj.hom)
  obtain ⟨⟨x₀, c⟩, hc⟩ := IsLocalizedModule.surj (nonZeroDivisors ℤ)
    (TensorProduct.mk ℤ ℚ (VectorBundleKZero X.obj.left) 1)
    (chX.symm (smoothChowEquiv X.obj.hom (codimensionToRationalChow k X.obj.hom p α)))
  have hc' : (c : ℤ) • chX.symm (smoothChowEquiv X.obj.hom
      (codimensionToRationalChow k X.obj.hom p α)) = (1 : ℚ) ⊗ₜ[ℤ] x₀ := hc
  obtain ⟨T, y₀, hy₀⟩ := exists_grassmannianTowerEmbedding f x₀
  have := T.isClosedImmersion
  have := isNoetherian_of_compactSpace (C := fieldChowSituation k) T.W.obj.hom
  obtain ⟨dW, hW, hπ⟩ := pushforwardCompatible_of_isGrassmannianTower hG hi T.isTower hY
    ⟨T.j.hom.left.base hX.nonempty.some⟩
  set chW := rationalChernCharacterAlgEquiv (isRegular_of_smooth_over_field T.W.obj.hom)
    (exists_bounds_relativeDimension_fieldChowSituation k T.W.obj.hom)
  have hw : codimensionToRationalChow k X.obj.hom p ((c : ℤ) • α) =
      lciGysinRational (fieldChowSituation k) X.obj.hom T.W.obj.hom (Over.w T.j.hom)
        (isLocalCompleteIntersectionMorphism_of_smooth_of_smooth T.j.hom.left T.W.obj.hom
          X.obj.hom (Over.w T.j.hom))
        (GysinMapExists.of_smooth_source T.j.hom.left T.W.obj.hom X.obj.hom (Over.w T.j.hom))
        ((smoothChowEquiv T.W.obj.hom).symm (chW ((1 : ℚ) ⊗ₜ[ℤ] y₀))) := by
    apply (smoothChowEquiv X.obj.hom).injective
    have h1 := smoothGysinRingHom_equiv X.obj.hom T.W.obj.hom (Over.w T.j.hom)
      ((smoothChowEquiv T.W.obj.hom).symm (chW ((1 : ℚ) ⊗ₜ[ℤ] y₀)))
    rw [LinearEquiv.apply_symm_apply] at h1
    show _ = smoothChowEquiv X.obj.hom (smoothGysinRational X.obj.hom T.W.obj.hom
      (Over.w T.j.hom) _)
    rw [← h1, smoothGysinRingHom_rationalChernCharacterAlgEquiv, LinearMap.baseChange_tmul,
      AddMonoidHom.coe_toIntLinearMap, pullback_eq_pullbackRingHom, hy₀, ← hc', map_zsmul,
      map_zsmul, map_zsmul, AlgEquiv.apply_symm_apply]
  have hj := 𝔚.toWeilData.cycleClass_pushforward_of_closedImmersion_of_lciGysinRational
    𝔚.perfectPairing 𝔚.cycleClassPullback 𝔚.cycleClassMul (𝔚.cycleClass_congr T.W) T.j hX hW
    ((dW : ℤ) - d) rfl (hi T.j hX hW _ rfl) p ((c : ℤ) • α) _ hw
  rw [map_zsmul, map_zsmul, map_zsmul, map_zsmul, ← Int.cast_smul_eq_zsmul F,
    ← Int.cast_smul_eq_zsmul F] at hj
  have hj' := smul_right_injective _ (Int.cast_ne_zero.2 (nonZeroDivisors.coe_ne_zero c)) hj
  have hcomp := 𝔚.toWeilData.cycleClass_pushforward_comp 𝔚.perfectPairing T.j T.π hX hW hY
    (𝔚.cycleClass_congr Y) p (p + ((dW : ℤ) - d)) q (by omega) (by omega) α hj'
    (hπ dW e hW hY _ q (by omega) _)
  rwa [T.fac] at hcomp

include hG hi in
/-- **`γ` commutes with pushforward along every morphism with connected source.** Embed `X` into
a Grassmannian `G` by `ψ` (`exists_closedImmersion_grassmannian`); then `f` is the closed
immersion `(f, ψ) : X ⟶ Y × G` followed by the projection. -/
theorem pushforwardCompatible_of_connectedSpace
    {X Y : (SmoothProjectiveScheme k).FullSubcategory} (f : X ⟶ Y)
    [ConnectedSpace X.obj.left] :
    𝔚.toWeilData.PushforwardCompatible 𝔚.perfectPairing f := by
  obtain ⟨l, n, hl, hln, ψ, hψ⟩ := exists_closedImmersion_grassmannian X
  have := hψ
  let hlft : X.obj.left ⟶
      Limits.pullback Y.obj.hom (SmoothProjectiveScheme.grassmannian k l n).obj.hom :=
    pullback.lift (f := Y.obj.hom) (g := (SmoothProjectiveScheme.grassmannian k l n).obj.hom)
      f.hom.left ψ.hom.left (by rw [Over.w f.hom]; exact (Over.w ψ.hom).symm)
  have hlfst : hlft ≫ pullback.fst Y.obj.hom (SmoothProjectiveScheme.grassmannian k l n).obj.hom =
      f.hom.left := pullback.lift_fst _ _ _
  have hlsnd : hlft ≫ pullback.snd Y.obj.hom (SmoothProjectiveScheme.grassmannian k l n).obj.hom =
      ψ.hom.left := pullback.lift_snd _ _ _
  let j : X ⟶ prod Y (SmoothProjectiveScheme.grassmannian k l n) :=
    ObjectProperty.homMk (Over.homMk hlft (by
      show hlft ≫ pullback.fst Y.obj.hom (SmoothProjectiveScheme.grassmannian k l n).obj.hom ≫
        Y.obj.hom = X.obj.hom
      rw [← Category.assoc, hlfst, Over.w f.hom]))
  have : IsClosedImmersion j.hom.left := by
    show IsClosedImmersion hlft
    have : IsClosedImmersion
        (hlft ≫ pullback.snd Y.obj.hom (SmoothProjectiveScheme.grassmannian k l n).obj.hom) := by
      rw [hlsnd]
      infer_instance
    exact .of_comp hlft (pullback.snd Y.obj.hom (SmoothProjectiveScheme.grassmannian k l n).obj.hom)
  have hjf : j ≫ fst Y (SmoothProjectiveScheme.grassmannian k l n) = f :=
    ObjectProperty.hom_ext _ (Over.OverMorphism.ext hlfst)
  intro d e hX hY p q hq α
  have hGne : Nonempty (SmoothProjectiveScheme.grassmannian k l n).obj.left :=
    ⟨ψ.hom.left.base hX.nonempty.some⟩
  have hP := isNonemptyEquidimensional_prod hY (isNonemptyEquidimensional_grassmannian l n hGne)
  have hc := WeilData.PushforwardCompatible.comp hP (𝔚.cycleClass_congr Y)
    (pushforwardCompatible_of_isClosedImmersion hG hi j)
    (fun d d' hX hP p q hq α => hG Y l n hl hln d' d hP hX p q hq α)
  rw [hjf] at hc
  exact hc d e hX hY p q hq α

include hi in
/-- `γ(j_*(j^!b)) = j_*γ(j^!b)` for a closed immersion `j`, at any spelling of the target
codimension. -/
theorem cycleClass_pushforward_codimensionGysin
    {Z X : (SmoothProjectiveScheme k).FullSubcategory} (j : Z ⟶ X)
    [IsClosedImmersion j.hom.left] {e d : ℕ} (hZ : IsNonemptyEquidimensional Z e)
    (hX : IsNonemptyEquidimensional X d) (p q : ℤ) (hq : q = p + d - e)
    (b : codimensionChowGroup k X.obj.hom p) :
    𝔚.toWeilData.cycleClass X q (equidimensionalPushforward j e d p q hq
        (codimensionGysin Z.obj.hom X.obj.hom (Over.w j.hom) p b)) =
      𝔚.toWeilData.pushforward 𝔚.perfectPairing j hZ hX (2 * p) p (2 * q) q (by omega) (by omega)
        (𝔚.toWeilData.cycleClass Z p
          (codimensionGysin Z.obj.hom X.obj.hom (Over.w j.hom) p b)) := by
  obtain rfl : q = p + ((d : ℤ) - e) := by omega
  exact 𝔚.toWeilData.cycleClass_pushforward_codimensionGysin_of_closedImmersion 𝔚.perfectPairing
    𝔚.cycleClassPullback 𝔚.cycleClassMul (𝔚.cycleClass_congr X) j hZ hX _ rfl
    (hi j hZ hX _ rfl) p b

include hG hi in
/-- **`γ` commutes with pushforward along every morphism**: by induction on the number of
connected components of the source, splitting off a clopen piece
(`exists_clopen_split`): both sides are additive in the decomposition
`α = ι₁_*(ι₁^!α) + ι₂_*(ι₂^!α)`, and `γ` commutes with `ι_{i,*}` on `ι_i^!`-classes. -/
theorem pushforwardCompatible {X Y : (SmoothProjectiveScheme k).FullSubcategory} (f : X ⟶ Y) :
    𝔚.toWeilData.PushforwardCompatible 𝔚.perfectPairing f := by
  suffices H : ∀ N : ℕ, ∀ X : (SmoothProjectiveScheme k).FullSubcategory,
      Nat.card (ConnectedComponents X.obj.left) = N →
        ∀ {Y : (SmoothProjectiveScheme k).FullSubcategory} (f : X ⟶ Y),
          𝔚.toWeilData.PushforwardCompatible 𝔚.perfectPairing f from
    H _ X rfl f
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  intro X hN Y f d e hX hY p q hq α
  have : Nonempty X.obj.left := hX.nonempty
  by_cases hconn : ConnectedSpace X.obj.left
  · exact pushforwardCompatible_of_connectedSpace hG hi f d e hX hY p q hq α
  obtain ⟨X₁, X₂, ι₁, ι₂, hc₁, hc₂, -, -, hn₁, hn₂, hlt₁, hlt₂, hdec⟩ := exists_clopen_split hconn
  obtain ⟨hd₁, hd₂, hsum⟩ := hdec d hX.relativeDimension
  have := hc₁
  have := hc₂
  have hX₁ : IsNonemptyEquidimensional X₁ d := ⟨hn₁, hd₁⟩
  have hX₂ : IsNonemptyEquidimensional X₂ d := ⟨hn₂, hd₂⟩
  set a₁ := codimensionGysin X₁.obj.hom X.obj.hom (Over.w ι₁.hom) p α
  set a₂ := codimensionGysin X₂.obj.hom X.obj.hom (Over.w ι₂.hom) p α
  have IH₁ := ih _ (hN ▸ hlt₁) X₁ rfl (ι₁ ≫ f) d e hX₁ hY p q hq a₁
  have IH₂ := ih _ (hN ▸ hlt₂) X₂ rfl (ι₂ ≫ f) d e hX₂ hY p q hq a₂
  have hY' : 𝔚.toWeilData.cycleClass Y q (equidimensionalPushforward f d e p q hq α) =
      𝔚.toWeilData.cycleClass Y q (equidimensionalPushforward (ι₁ ≫ f) d e p q hq a₁) +
        𝔚.toWeilData.cycleClass Y q (equidimensionalPushforward (ι₂ ≫ f) d e p q hq a₂) := by
    rw [← map_add]
    refine 𝔚.cycleClass_congr Y q _ _ ?_
    rw [map_add, ← codimensionToRationalChow_equidimensionalPushforward_comp ι₁ f hd₁
        hX.relativeDimension hY.relativeDimension p p q (by omega) hq,
      ← codimensionToRationalChow_equidimensionalPushforward_comp ι₂ f hd₂
        hX.relativeDimension hY.relativeDimension p p q (by omega) hq,
      ← map_add, ← map_add,
      codimensionToRationalChow_equidimensionalPushforward f hX.relativeDimension
        hY.relativeDimension, codimensionToRationalChow_equidimensionalPushforward f
        hX.relativeDimension hY.relativeDimension, map_add, ← hsum p α]
  have hX' : 𝔚.toWeilData.cycleClass X p α =
      𝔚.toWeilData.cycleClass X p (equidimensionalPushforward ι₁ d d p p (by omega) a₁) +
        𝔚.toWeilData.cycleClass X p (equidimensionalPushforward ι₂ d d p p (by omega) a₂) := by
    rw [← map_add]
    refine 𝔚.cycleClass_congr X p _ _ ?_
    rw [map_add, ← hsum p α]
  rw [hY', IH₁, IH₂, hX', map_add,
    cycleClass_pushforward_codimensionGysin hi ι₁ hX₁ hX p p (by omega) α,
    cycleClass_pushforward_codimensionGysin hi ι₂ hX₂ hX p p (by omega) α,
    𝔚.toWeilData.pushforward_comp 𝔚.perfectPairing ι₁ f hX₁ hX hY,
    𝔚.toWeilData.pushforward_comp 𝔚.perfectPairing ι₂ f hX₂ hX hY]

include hG hi in
/-- **`γ` commutes with pushforward**, granted `i_*1 = γ([Z])` for every closed immersion and the
compatibility along the projections `V × G(l, n) ⟶ V` of Stacks 0FIQ. -/
theorem cycleClassPushforward_of_grassmannian :
    𝔚.toWeilData.CycleClassPushforward 𝔚.perfectPairing :=
  (WeilData.cycleClassPushforward_iff _ _).2 fun f => pushforwardCompatible hG hi f

end WeilChernData

end Stacks.WeilCohomology

end
