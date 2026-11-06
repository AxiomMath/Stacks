module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.ComplexHigherDirectImageColimit

/-!
# Higher direct images of a colimit of bounded below complexes along a limit of morphisms

Let `I` be a directed set, let `g_i : X_i ⟶ S_i` be an inverse system of quasi-compact and
quasi-separated morphisms of schemes over `I` with affine transition morphisms `f_{i'i}`,
`h_{i'i}`, and let `g : X ⟶ S` be its limit, with projections `f_i : X ⟶ X_i`, `h_i : S ⟶ S_i`.
Let `(ℱ_i^•, φ_{i'i})` be a system of complexes of abelian sheaves on the `X_{i, étale}` with
`ℱ_i^n = 0` for `n < a`, `a` independent of `i`, and `ℱ^• = colim f_i^{-1}ℱ_i^•`. Then

`R^pg_*(ℱ^•) = colim_i h_i^{-1}R^pg_{i, *}ℱ_i^•` for all `p ∈ ℤ` ([Stacks, Tag 0GIV]).

## Main results

* `Stacks.EtaleCohomology.LimitHigherDirectImage.isComplexHigherDirectImageColimit_single`: the
  colimit assertion for a system of sheaves placed in any degree.
* `Stacks.EtaleCohomology.LimitHigherDirectImage.complexHigherDirectImageColimit`:
  [Stacks, Tag 0GIV].

## Implementation notes

The proof is the alternative argument by stupid truncations that the source mentions; see
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.ComplexHigherDirectImageColimit` for the
five lemma it rests on. The colimit `ℱ^• = colim f_i^{-1}ℱ_i^•` is given, as in Stacks 0EZM, by a
complex `ℱ^•` on `X` with maps of complexes `ι_i : f_i^{-1}ℱ_i^• ⟶ ℱ^•` compatible with the
transition maps which present every term `ℱ^n` as the colimit `colim f_i^{-1}ℱ_i^n`; colimits of
complexes are computed termwise, and `ℱ^•` then vanishes in degrees `< a` as well.

## References

* [Stacks Project, Tag 0GIV](https://stacks.math.columbia.edu/tag/0GIV)
* [Stacks Project, Tag 0EYM](https://stacks.math.columbia.edu/tag/0EYM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology.LimitHigherDirectImage

attribute [local instance] HasDerivedCategory.standard

open EtaleComplexSystem

attribute [local instance] hasColimitsOfShape_systemLift_sheaf

/-- The comparison map of a system of complexes is an isomorphism exactly when the colimit
assertion holds. -/
theorem isIso_complexColimitDesc_iff {I : Type u} [Preorder I] {DX DS : Iᵒᵖ ⥤ Scheme.{u}}
    (γ : DX ⟶ DS) (q b : ℤ) {cX : Cone DX} (cS : Cone DS) (hcS : IsLimit cS)
    (F : EtaleComplexSystem DX) [∀ i, (F.obj i).IsStrictlyGE b]
    (𝓕 : CochainComplex (Sheaf (smallEtaleTopology cX.pt) Ab.{u + 1}) ℤ) [𝓕.IsStrictlyGE b]
    (ι : ∀ i : Iᵒᵖ, ((smallEtalePullbackAb (cX.π.app i)).mapHomologicalComplex _).obj (F.obj i) ⟶ 𝓕)
    (hι : F.IsPullbackCocone cX ι) :
    IsIso (complexColimitDesc γ q b cS hcS F 𝓕 ι hι) ↔
      IsComplexHigherDirectImageColimit γ q b F cX cS hcS 𝓕 ι :=
  (SystemLift.isSystemColimit_iff_isIso_colimitDesc _ _
    (fun x => complexLeg_cocone γ q b F cX cS hcS 𝓕 ι hι x)).symm

/-- A sheaf placed in degree `n` is strictly `≥ B` as soon as `B ≤ n`. -/
private theorem isStrictlyGE_single_obj {X : Scheme.{u}}
    (A : Sheaf (smallEtaleTopology X) Ab.{u + 1}) (B n : ℤ) (h : B ≤ n) :
    CochainComplex.IsStrictlyGE ((HomologicalComplex.single _ (ComplexShape.up ℤ) n).obj A) B :=
  CochainComplex.isStrictlyGE_of_ge _ B n h

section Single

variable {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I] {DX DS : Iᵒᵖ ⥤ Scheme.{u}}
  (γ : DX ⟶ DS) [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (DX.map a)]
  [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (DS.map a)] [∀ i, QuasiCompact (γ.app i)]
  [∀ i, QuasiSeparated (γ.app i)] {cX : Cone DX} {cS : Cone DS} (hcX : IsLimit cX)
  (hcS : IsLimit cS) (G : EtaleSheafSystem DX Ab.{u + 1})
  {𝓖 : Sheaf (smallEtaleTopology cX.pt) Ab.{u + 1}}
  {ιG : ∀ i : Iᵒᵖ, (smallEtalePullbackAb (cX.π.app i)).obj (G.obj i) ⟶ 𝓖}
  (hιG : IsPullbackCocone cX G ιG) (hpres : IsPullbackColimitPresentation cX 𝓖 G ιG)

omit [IsDirected I (· ≤ ·)] [Nonempty I] [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (DX.map a)]
  [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (DS.map a)] [∀ i, QuasiCompact (γ.app i)]
  [∀ i, QuasiSeparated (γ.app i)] in
/-- The colimit assertion for a system of sheaves placed in one degree does not depend on the
lower bound through which its complexes are placed in `D^+`. -/
theorem isComplexHigherDirectImageColimit_single_bound_iff (n q b b' : ℤ)
    [∀ i, ((single DX G n).obj i).IsStrictlyGE b] [∀ i, ((single DX G n).obj i).IsStrictlyGE b']
    [CochainComplex.IsStrictlyGE ((HomologicalComplex.single _ (ComplexShape.up ℤ) n).obj 𝓖) b]
    [CochainComplex.IsStrictlyGE ((HomologicalComplex.single _ (ComplexShape.up ℤ) n).obj 𝓖) b'] :
    IsComplexHigherDirectImageColimit γ q b (single DX G n) cX cS hcS
        ((HomologicalComplex.single _ (ComplexShape.up ℤ) n).obj 𝓖) (singleι G ιG n) ↔
      IsComplexHigherDirectImageColimit γ q b' (single DX G n) cX cS hcS
        ((HomologicalComplex.single _ (ComplexShape.up ℤ) n).obj 𝓖) (singleι G ιG n) :=
  Iff.rfl


include hcX hιG hpres in
/-- The colimit assertion for a system of sheaves placed in degree `k ≥ 0`, with a lower bound
`B ≤ 0`, by moving the sheaves up from degree zero. -/
theorem isComplexHigherDirectImageColimit_single_nonneg (B : ℤ) (hB : B ≤ 0) (k : ℕ) (q : ℤ) :
    haveI := fun i => CochainComplex.isStrictlyGE_of_ge
        ((HomologicalComplex.single _ (ComplexShape.up ℤ) k).obj (G.obj i)) B k (by omega)
    haveI := CochainComplex.isStrictlyGE_of_ge
        ((HomologicalComplex.single _ (ComplexShape.up ℤ) k).obj 𝓖) B k (by omega)
    IsComplexHigherDirectImageColimit γ q B (single DX G k) cX cS hcS
      ((HomologicalComplex.single _ (ComplexShape.up ℤ) k).obj 𝓖) (singleι G ιG k) := by
  induction k generalizing q with
  | zero =>
    have := fun i => isStrictlyGE_single_obj (G.obj i) B 0 hB
    have := isStrictlyGE_single_obj 𝓖 B 0 hB
    have := fun i => isStrictlyGE_single_obj (G.obj i) 0 0 le_rfl
    have := isStrictlyGE_single_obj 𝓖 0 0 le_rfl
    rcases lt_or_ge q 0 with hq | hq
    · exact IsSystemColimit.of_isZero
        (fun i => Functor.map_isZero _ (isZero_homologyAb_derivedPushforwardAb (γ.app i) B 0 q
          ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj (G.obj i)) hq))
        (isZero_homologyAb_derivedPushforwardAb (limitMorphism γ cX cS hcS) B 0 q
          ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj 𝓖) hq)
    · obtain ⟨q, rfl⟩ := Int.eq_ofNat_of_zero_le hq
      exact isComplexHigherDirectImageColimit_single_zero γ hcX hcS G hιG hpres B q
  | succ k ih =>
    have := fun i => isStrictlyGE_single_obj (G.obj i) B k (by omega)
    have := isStrictlyGE_single_obj 𝓖 B k (by omega)
    have := fun i => isStrictlyGE_single_obj (G.obj i) B (k + 1 : ℕ) (by omega)
    have := isStrictlyGE_single_obj 𝓖 B (k + 1 : ℕ) (by omega)
    exact (isComplexHigherDirectImageColimit_single_iff γ cX cS hcS B G ιG
      (i₀ := (k : ℤ)) (i₁ := ((k + 1 : ℕ) : ℤ))
      (by change (k : ℤ) + 1 = ((k + 1 : ℕ) : ℤ); push_cast; rfl)
      (by omega) (q - 1) q (by omega)).1 (ih (q - 1))

include hcX hιG hpres in
/-- The colimit assertion for a system of sheaves placed in degree `-k ≥ B`, by moving the
sheaves down from degree zero. -/
theorem isComplexHigherDirectImageColimit_single_nonpos (B : ℤ) (hB : B ≤ 0) (k : ℕ)
    (hk : B ≤ -(k : ℤ)) (q : ℤ) :
    haveI := fun i => CochainComplex.isStrictlyGE_of_ge
        ((HomologicalComplex.single _ (ComplexShape.up ℤ) (-(k : ℤ))).obj (G.obj i)) B (-(k : ℤ)) hk
    haveI := CochainComplex.isStrictlyGE_of_ge
        ((HomologicalComplex.single _ (ComplexShape.up ℤ) (-(k : ℤ))).obj 𝓖) B (-(k : ℤ)) hk
    IsComplexHigherDirectImageColimit γ q B (single DX G (-(k : ℤ))) cX cS hcS
      ((HomologicalComplex.single _ (ComplexShape.up ℤ) (-(k : ℤ))).obj 𝓖)
      (singleι G ιG (-(k : ℤ))) := by
  induction k generalizing q with
  | zero => exact isComplexHigherDirectImageColimit_single_nonneg γ hcX hcS G hιG hpres B hB 0 q
  | succ k ih =>
    have := fun i => isStrictlyGE_single_obj (G.obj i) B (-(k : ℤ)) (by omega)
    have := isStrictlyGE_single_obj 𝓖 B (-(k : ℤ)) (by omega)
    have := fun i => isStrictlyGE_single_obj (G.obj i) B (-((k + 1 : ℕ) : ℤ)) hk
    have := isStrictlyGE_single_obj 𝓖 B (-((k + 1 : ℕ) : ℤ)) hk
    exact (isComplexHigherDirectImageColimit_single_iff γ cX cS hcS B G ιG
      (i₀ := -((k + 1 : ℕ) : ℤ)) (i₁ := -(k : ℤ))
      (by change -((k + 1 : ℕ) : ℤ) + 1 = -(k : ℤ); push_cast; ring) hk q (q + 1) rfl).2
      (ih (by omega) (q + 1))

include hcX hιG hpres in
/-- **The colimit assertion for a system of sheaves placed in degree `n`**, in every degree `q`:
`R^qg_*(𝒢[-n]) = colim_i h_i^{-1}R^qg_{i, *}(𝒢_i[-n])`, which is [Stacks, Tag 0EYM] in degree
`q - n`. -/
theorem isComplexHigherDirectImageColimit_single (n q b : ℤ)
    [∀ i, ((single DX G n).obj i).IsStrictlyGE b]
    [CochainComplex.IsStrictlyGE ((HomologicalComplex.single _ (ComplexShape.up ℤ) n).obj 𝓖) b]
    (hb : b ≤ n) :
    IsComplexHigherDirectImageColimit γ q b (single DX G n) cX cS hcS
      ((HomologicalComplex.single _ (ComplexShape.up ℤ) n).obj 𝓖) (singleι G ιG n) := by
  have hB : min b 0 ≤ 0 := min_le_right _ _
  have := fun i => isStrictlyGE_single_obj (G.obj i) (min b 0) n (by omega)
  have := isStrictlyGE_single_obj 𝓖 (min b 0) n (by omega)
  refine (isComplexHigherDirectImageColimit_single_bound_iff γ hcS G n q (min b 0) b).1 ?_
  rcases le_or_gt 0 n with hn | hn
  · obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le hn
    exact isComplexHigherDirectImageColimit_single_nonneg γ hcX hcS G hιG hpres _ hB k q
  · obtain ⟨k, hk⟩ := Int.exists_eq_neg_ofNat (le_of_lt hn)
    subst hk
    exact isComplexHigherDirectImageColimit_single_nonpos γ hcX hcS G hιG hpres _ hB k
      (by omega) q

end Single


/-! ### The stupid truncations -/

section Main

open StacksDraft.StupidTruncation

attribute [local instance] StacksDraft.StupidTruncation.isStrictlyGE_stupidTruncGE
  hasColimitsOfShape_systemLift_sheaf

variable {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I] {DX DS : Iᵒᵖ ⥤ Scheme.{u}}
  (γ : DX ⟶ DS) [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (DX.map a)]
  [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (DS.map a)] [∀ i, QuasiCompact (γ.app i)]
  [∀ i, QuasiSeparated (γ.app i)] {cX : Cone DX} {cS : Cone DS} (hcX : IsLimit cX)
  (hcS : IsLimit cS) (F : EtaleComplexSystem DX) (a : ℤ) [∀ i, (F.obj i).IsStrictlyGE a]
  {𝓕 : CochainComplex (Sheaf (smallEtaleTopology cX.pt) Ab.{u + 1}) ℤ} [𝓕.IsStrictlyGE a]
  {ι : ∀ i : Iᵒᵖ, ((smallEtalePullbackAb (cX.π.app i)).mapHomologicalComplex _).obj (F.obj i) ⟶ 𝓕}
  (hι : F.IsPullbackCocone cX ι)

omit [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (DX.map a)]
  [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (DS.map a)] [∀ i, QuasiCompact (γ.app i)]
  [∀ i, QuasiSeparated (γ.app i)] [IsDirected I (· ≤ ·)] [Nonempty I] in
/-- In every degree, the bottom term of a stupid truncation of the system or the next truncation
vanishes. -/
theorem isZero_single_or_truncGE (n m : ℤ) :
    (∀ i, IsZero (((single DX (F.term n) n).obj i).X m)) ∨
      (∀ i, IsZero (((F.truncGE (n + 1)).obj i).X m)) := by
  by_cases hm : m ≤ n
  · exact Or.inr fun i => CochainComplex.isZero_of_isStrictlyGE _ (n + 1) m (by omega)
  · exact Or.inl fun i => HomologicalComplex.isZero_single_obj_X _ _ _ _ (by omega)

omit [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (DX.map a)]
  [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (DS.map a)] [∀ i, QuasiCompact (γ.app i)]
  [∀ i, QuasiSeparated (γ.app i)] in
/-- **The induction step for the stupid truncations, epimorphism half.** -/
theorem epi_complexColimitDesc_truncGE (n q : ℤ)
    [∀ i, ((single DX (F.term n) n).obj i).IsStrictlyGE a]
    [CochainComplex.IsStrictlyGE ((HomologicalComplex.single _ (ComplexShape.up ℤ) n).obj
      (𝓕.X n)) a]
    (h₁ : Epi (complexColimitDesc γ q a cS hcS (F.truncGE (n + 1)) _ (F.truncGEι ι (n + 1))
      (hι.truncGE (n + 1))))
    (h₃ : Epi (complexColimitDesc γ q a cS hcS (single DX (F.term n) n) _
      (singleι (F.term n) (fun i => (ι i).f n) n)
      (isPullbackCocone_single (F.term n) (hι.term n) n)))
    (h₄ : Mono (complexColimitDesc γ (q + 1) a cS hcS (F.truncGE (n + 1)) _
      (F.truncGEι ι (n + 1)) (hι.truncGE (n + 1)))) :
    Epi (complexColimitDesc γ q a cS hcS (F.truncGE n) _ (F.truncGEι ι n) (hι.truncGE n)) :=
  epi_complexColimitDesc_of_shortExact (F₁ := F.truncGE (n + 1)) (F₂ := F.truncGE n)
    (F₃ := single DX (F.term n) n)
    (φ₁₂ := fun i => (stupidTruncGEShortComplex (F.obj i) n).f)
    (φ₂₃ := fun i => (stupidTruncGEShortComplex (F.obj i) n).g)
    (𝓕₁ := 𝓕.stupidTrunc (ComplexShape.embeddingUpIntGE (n + 1)))
    (𝓕₂ := 𝓕.stupidTrunc (ComplexShape.embeddingUpIntGE n))
    (𝓕₃ := (HomologicalComplex.single _ (ComplexShape.up ℤ) n).obj (𝓕.X n))
    (φ'₁₂ := (stupidTruncGEShortComplex 𝓕 n).f) (φ'₂₃ := (stupidTruncGEShortComplex 𝓕 n).g)
    γ a (fun c => (stupidTruncGEShortComplexMapOfHom (systemPullback DX Ab.{u + 1} c) (F.map c)
      n).comm₁₂.symm)
    (fun c => (stupidTruncGEShortComplexMapOfHom (systemPullback DX Ab.{u + 1} c) (F.map c)
      n).comm₂₃.symm)
    (fun i => (stupidTruncGEShortComplex (F.obj i) n).zero)
    (fun i m => stupidTruncGEShortComplexSplitting (F.obj i) n m)
    (isZero_single_or_truncGE F n) cS hcS
    (fun i => (stupidTruncGEShortComplexMapOfHom (smallEtalePullbackAb (cX.π.app i)) (ι i)
      n).comm₁₂.symm)
    (fun i => (stupidTruncGEShortComplexMapOfHom (smallEtalePullbackAb (cX.π.app i)) (ι i)
      n).comm₂₃.symm)
    (stupidTruncGEShortComplex 𝓕 n).zero (fun m => stupidTruncGEShortComplexSplitting 𝓕 n m)
    (fun i m => isZero_stupidTruncGEShortComplex_X₃_or_X₁ (K := F.obj i) 𝓕 n m)
    (hι.truncGE (n + 1)) (hι.truncGE n) (isPullbackCocone_single (F.term n) (hι.term n) n)
    q (q + 1) rfl h₁ h₃ h₄

omit [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (DX.map a)]
  [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (DS.map a)] [∀ i, QuasiCompact (γ.app i)]
  [∀ i, QuasiSeparated (γ.app i)] in
/-- **The induction step for the stupid truncations, monomorphism half.** -/
theorem mono_complexColimitDesc_truncGE (n q : ℤ)
    [∀ i, ((single DX (F.term n) n).obj i).IsStrictlyGE a]
    [CochainComplex.IsStrictlyGE ((HomologicalComplex.single _ (ComplexShape.up ℤ) n).obj
      (𝓕.X n)) a]
    (h₁ : Epi (complexColimitDesc γ (q - 1) a cS hcS (single DX (F.term n) n) _
      (singleι (F.term n) (fun i => (ι i).f n) n)
      (isPullbackCocone_single (F.term n) (hι.term n) n)))
    (h₂ : Mono (complexColimitDesc γ q a cS hcS (F.truncGE (n + 1)) _ (F.truncGEι ι (n + 1))
      (hι.truncGE (n + 1))))
    (h₄ : Mono (complexColimitDesc γ q a cS hcS (single DX (F.term n) n) _
      (singleι (F.term n) (fun i => (ι i).f n) n)
      (isPullbackCocone_single (F.term n) (hι.term n) n))) :
    Mono (complexColimitDesc γ q a cS hcS (F.truncGE n) _ (F.truncGEι ι n) (hι.truncGE n)) :=
  mono_complexColimitDesc_of_shortExact (F₁ := F.truncGE (n + 1)) (F₂ := F.truncGE n)
    (F₃ := single DX (F.term n) n)
    (φ₁₂ := fun i => (stupidTruncGEShortComplex (F.obj i) n).f)
    (φ₂₃ := fun i => (stupidTruncGEShortComplex (F.obj i) n).g)
    (𝓕₁ := 𝓕.stupidTrunc (ComplexShape.embeddingUpIntGE (n + 1)))
    (𝓕₂ := 𝓕.stupidTrunc (ComplexShape.embeddingUpIntGE n))
    (𝓕₃ := (HomologicalComplex.single _ (ComplexShape.up ℤ) n).obj (𝓕.X n))
    (φ'₁₂ := (stupidTruncGEShortComplex 𝓕 n).f) (φ'₂₃ := (stupidTruncGEShortComplex 𝓕 n).g)
    γ a (fun c => (stupidTruncGEShortComplexMapOfHom (systemPullback DX Ab.{u + 1} c) (F.map c)
      n).comm₁₂.symm)
    (fun c => (stupidTruncGEShortComplexMapOfHom (systemPullback DX Ab.{u + 1} c) (F.map c)
      n).comm₂₃.symm)
    (fun i => (stupidTruncGEShortComplex (F.obj i) n).zero)
    (fun i m => stupidTruncGEShortComplexSplitting (F.obj i) n m)
    (isZero_single_or_truncGE F n) cS hcS
    (fun i => (stupidTruncGEShortComplexMapOfHom (smallEtalePullbackAb (cX.π.app i)) (ι i)
      n).comm₁₂.symm)
    (fun i => (stupidTruncGEShortComplexMapOfHom (smallEtalePullbackAb (cX.π.app i)) (ι i)
      n).comm₂₃.symm)
    (stupidTruncGEShortComplex 𝓕 n).zero (fun m => stupidTruncGEShortComplexSplitting 𝓕 n m)
    (fun i m => isZero_stupidTruncGEShortComplex_X₃_or_X₁ (K := F.obj i) 𝓕 n m)
    (hι.truncGE (n + 1)) (hι.truncGE n) (isPullbackCocone_single (F.term n) (hι.term n) n)
    (q - 1) q (by omega) h₁ h₂ h₄

variable (hpres : ∀ n, IsPullbackColimitPresentation cX (𝓕.X n) (F.term n) (fun i => (ι i).f n))

omit [∀ i, (F.obj i).IsStrictlyGE a] [𝓕.IsStrictlyGE a] in
include hcX hpres in
/-- The comparison map of the system of the bottom terms placed in degree `n` is an
isomorphism. -/
theorem isIso_complexColimitDesc_single (n q : ℤ) (hn : a ≤ n)
    [∀ i, ((single DX (F.term n) n).obj i).IsStrictlyGE a]
    [CochainComplex.IsStrictlyGE ((HomologicalComplex.single _ (ComplexShape.up ℤ) n).obj
      (𝓕.X n)) a] :
    IsIso (complexColimitDesc γ q a cS hcS (single DX (F.term n) n) _
      (singleι (F.term n) (fun i => (ι i).f n) n)
      (isPullbackCocone_single (F.term n) (hι.term n) n)) :=
  (isIso_complexColimitDesc_iff γ q a cS hcS _ _ _ _).2
    (isComplexHigherDirectImageColimit_single γ hcX hcS (F.term n) (hι.term n) (hpres n) n q a hn)

include hcX hpres in
/-- **The two halves of the colimit assertion for the stupid truncations**, by descending
induction on the truncation degree: for `n ≥ a` the comparison map in degree `q` of
`σ^{≥n}ℱ^•` is an epimorphism for `q ≤ p` and a monomorphism for `q ≤ p + 1`. -/
theorem epi_mono_complexColimitDesc_truncGE (p : ℤ) :
    (∀ q ≤ p, Epi (complexColimitDesc γ q a cS hcS (F.truncGE a) _ (F.truncGEι ι a)
      (hι.truncGE a))) ∧
      ∀ q ≤ p + 1, Mono (complexColimitDesc γ q a cS hcS (F.truncGE a) _ (F.truncGEι ι a)
        (hι.truncGE a)) := by
  refine Int.leInductionDown (m := max (p + 2) a)
    (motive := fun n _ => a ≤ n →
      (∀ q ≤ p, Epi (complexColimitDesc γ q a cS hcS (F.truncGE n) _ (F.truncGEι ι n)
        (hι.truncGE n))) ∧
      ∀ q ≤ p + 1, Mono (complexColimitDesc γ q a cS hcS (F.truncGE n) _ (F.truncGEι ι n)
        (hι.truncGE n))) ?_ ?_ a (le_max_right _ _) le_rfl
  · intro _
    have hz : ∀ q, q ≤ p + 1 → IsIso (complexColimitDesc γ q a cS hcS
        (F.truncGE (max (p + 2) a)) _ (F.truncGEι ι (max (p + 2) a))
        (hι.truncGE (max (p + 2) a))) := fun q hq =>
      (isIso_complexColimitDesc_iff γ q a cS hcS _ _ _ _).2
        (IsSystemColimit.of_isZero
          (fun i => Functor.map_isZero _ (isZero_homologyAb_derivedPushforwardAb (γ.app i) a
            (max (p + 2) a) q _ (by omega)))
          (isZero_homologyAb_derivedPushforwardAb _ a (max (p + 2) a) q _ (by omega)))
    exact ⟨fun q hq => by have := hz q (by omega); infer_instance,
      fun q hq => by have := hz q hq; infer_instance⟩
  · intro n _ ih hn
    have e : n - 1 + 1 = n := by omega
    rw [← e] at ih
    obtain ⟨ih₁, ih₂⟩ := ih (by omega)
    have : ∀ i, ((single DX (F.term (n - 1)) (n - 1)).obj i).IsStrictlyGE a := fun i =>
      isStrictlyGE_single_obj ((F.term (n - 1)).obj i) a (n - 1) hn
    have := isStrictlyGE_single_obj (𝓕.X (n - 1)) a (n - 1) hn
    have hs := fun q => isIso_complexColimitDesc_single γ hcX hcS F a hι hpres (n - 1) q hn
    exact ⟨fun q hq => epi_complexColimitDesc_truncGE γ hcS F a hι (n - 1) q (ih₁ q hq)
        (by have := hs q; infer_instance) (ih₂ (q + 1) (by omega)),
      fun q hq => mono_complexColimitDesc_truncGE γ hcS F a hι (n - 1) q
        (by have := hs (q - 1); infer_instance) (ih₂ q hq) (by have := hs q; infer_instance)⟩

include hcX hι hpres in
/-- **The colimit assertion for a uniformly bounded below system of complexes**, in every
degree: the stupid truncation `σ^{≥a}` of the system is the system itself. -/
theorem isComplexHigherDirectImageColimit (p : ℤ) :
    IsComplexHigherDirectImageColimit γ p a F cX cS hcS 𝓕 ι := by
  obtain ⟨h₁, h₂⟩ := epi_mono_complexColimitDesc_truncGE γ hcX hcS F a hι hpres p
  have := h₁ p le_rfl
  have := h₂ p (by omega)
  have : IsIso (complexColimitDesc γ p a cS hcS (F.truncGE a) _ (F.truncGEι ι a)
      (hι.truncGE a)) := isIso_of_mono_of_epi _
  have hσ := (isIso_complexColimitDesc_iff γ p a cS hcS _ _ _ (hι.truncGE a)).1 this
  have hφ : ∀ {i j : Iᵒᵖ} (c : i ⟶ j),
      ((systemPullback DX Ab.{u + 1} c).mapHomologicalComplex _).map
          (HomologicalComplex.ιStupidTrunc (F.obj j) (ComplexShape.embeddingUpIntGE a)) ≫
        F.map c =
      (F.truncGE a).map c ≫
        HomologicalComplex.ιStupidTrunc (F.obj i) (ComplexShape.embeddingUpIntGE a) :=
    fun c => (stupidTruncGEMapOfHom_ι (systemPullback DX Ab.{u + 1} c) (F.map c) a).symm
  have hβ : ∀ i, ((smallEtalePullbackAb (cX.π.app i)).mapHomologicalComplex _).map
        (HomologicalComplex.ιStupidTrunc (F.obj i) (ComplexShape.embeddingUpIntGE a)) ≫ ι i =
      F.truncGEι ι a i ≫ HomologicalComplex.ιStupidTrunc 𝓕 (ComplexShape.embeddingUpIntGE a) :=
    fun i => (stupidTruncGEMapOfHom_ι (smallEtalePullbackAb (cX.π.app i)) (ι i) a).symm
  have hiso : ∀ {X : Scheme.{u}} (K : CochainComplex (Sheaf (smallEtaleTopology X) Ab.{u + 1}) ℤ)
      [K.IsStrictlyGE a],
      IsIso (plusComplexMap a
        (HomologicalComplex.ιStupidTrunc K (ComplexShape.embeddingUpIntGE a))) :=
    fun K _ => by
      have : IsIso (ObjectProperty.homMk ((HomotopyCategory.quotient _ _).map
          (HomologicalComplex.ιStupidTrunc K (ComplexShape.embeddingUpIntGE a))) :
            CochainComplex.plusHomotopyObj a _ ⟶ CochainComplex.plusHomotopyObj a K) :=
        (ObjectProperty.isoMk _ ((HomotopyCategory.quotient _ _).mapIso
          (asIso (HomologicalComplex.ιStupidTrunc K (ComplexShape.embeddingUpIntGE a)))) :
            CochainComplex.plusHomotopyObj a _ ≅ CochainComplex.plusHomotopyObj a K).isIso_hom
      infer_instance
  have hI : ∀ i, IsIso ((smallEtalePullbackAb (cS.π.app i)).map
      (complexHigherDirectImageMap (F := F.truncGE a) (F' := F) γ p a
        (fun i => HomologicalComplex.ιStupidTrunc (F.obj i) (ComplexShape.embeddingUpIntGE a))
        i)) :=
    fun i => by
      have := hiso (F.obj i)
      have : IsIso ((derivedPushforwardAb (γ.app i)).map (plusComplexMap a
          (HomologicalComplex.ιStupidTrunc (F.obj i) (ComplexShape.embeddingUpIntGE a)))) :=
        Functor.map_isIso _ _
      have : IsIso (complexHigherDirectImageMap (F := F.truncGE a) (F' := F) γ p a
          (fun i => HomologicalComplex.ιStupidTrunc (F.obj i) (ComplexShape.embeddingUpIntGE a))
          i) :=
        Functor.map_isIso (homologyAb (DS.obj i) p) _
      exact Functor.map_isIso _ _
  have hI' : IsIso ((homologyAb cS.pt p).map ((derivedPushforwardAb (limitMorphism γ cX cS hcS)).map
      (plusComplexMap a
        (HomologicalComplex.ιStupidTrunc 𝓕 (ComplexShape.embeddingUpIntGE a))))) := by
    have := hiso 𝓕
    exact Functor.map_isIso _ _
  exact (IsSystemColimit.iff_of_isoSystem
    (fun i => asIso ((smallEtalePullbackAb (cS.π.app i)).map
      (complexHigherDirectImageMap (F := F.truncGE a) (F' := F) γ p a
        (fun i => HomologicalComplex.ιStupidTrunc (F.obj i) (ComplexShape.embeddingUpIntGE a)) i)))
    (asIso ((homologyAb cS.pt p).map ((derivedPushforwardAb (limitMorphism γ cX cS hcS)).map
      (plusComplexMap a (HomologicalComplex.ιStupidTrunc 𝓕 (ComplexShape.embeddingUpIntGE a))))))
    (fun c => pullbackDiagramMap_comp_complexHigherDirectImageMap (F := F.truncGE a) (F' := F)
      γ p a hφ cS c)
    (fun i => complexLeg_comp_map (F := F.truncGE a) (F' := F) γ p a cX cS hcS (F.truncGEι ι a) ι
      hβ i)).1 hσ

end Main

/-! ### Stacks 0GIV -/

section Tag

variable {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I] {DX DS : Iᵒᵖ ⥤ Scheme.{u}}
  (γ : DX ⟶ DS) [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (DX.map a)]
  [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (DS.map a)] [∀ i, QuasiCompact (γ.app i)]
  [∀ i, QuasiSeparated (γ.app i)] {cX : Cone DX} {cS : Cone DS} (hcX : IsLimit cX)
  (hcS : IsLimit cS)

include hcX in
/-- **[Stacks, Tag 0GIV].** Let `I` be a directed set, `g_i : X_i ⟶ S_i` an inverse system of
quasi-compact and quasi-separated morphisms of schemes with affine transition morphisms
`f_{i'i}`, `h_{i'i}`, and `g : X ⟶ S` its limit with projections `f_i`, `h_i`. Let
`(ℱ_i^•, φ_{i'i})` be a system of complexes of abelian sheaves on the `X_{i, étale}`, with
`ℱ_i^n = 0` for `n < a` and all `i`, and `ℱ^• = colim f_i^{-1}ℱ_i^•`, presented by maps of
complexes `ι_i : f_i^{-1}ℱ_i^• ⟶ ℱ^•` compatible with the transition maps and presenting every
term `ℱ^n` as `colim f_i^{-1}ℱ_i^n`. Then for every `p ∈ ℤ` the maps
`h_i^{-1}R^pg_{i, *}ℱ_i^• ⟶ R^pg_*ℱ^•` (the derived base change maps of the projection squares
followed by `R^pg_*ι_i`) are compatible with the maps
`h_{i'i}^{-1}R^pg_{i, *}ℱ_i^• ⟶ R^pg_{i', *}ℱ_{i'}^•` of the system of the
`R^pg_{i, *}ℱ_i^•` and present `R^pg_*ℱ^• = colim_i h_i^{-1}R^pg_{i, *}ℱ_i^•`. -/
@[stacks 0GIV, sga "4 VII 5.11" "more general"]
theorem complexHigherDirectImageColimit (F : EtaleComplexSystem DX) (a : ℤ)
    [∀ i, (F.obj i).IsStrictlyGE a]
    (𝓕 : CochainComplex (Sheaf (smallEtaleTopology cX.pt) Ab.{u + 1}) ℤ)
    (ι : ∀ i : Iᵒᵖ, ((smallEtalePullbackAb (cX.π.app i)).mapHomologicalComplex _).obj (F.obj i) ⟶ 𝓕)
    (hι : F.IsPullbackCocone cX ι)
    (hpres : ∀ n, IsPullbackColimitPresentation cX (𝓕.X n) (F.term n) (fun i => (ι i).f n))
    (p : ℤ) :
    haveI := F.isStrictlyGE_of_isPullbackColimitPresentation a hpres
    (∀ {i j : Iᵒᵖ} (c : i ⟶ j),
        (complexHigherDirectImageSystem γ p a F).pullbackDiagramMap cS (i := i) (j := j) c ≫
          complexLeg γ p a F cX cS hcS 𝓕 ι i = complexLeg γ p a F cX cS hcS 𝓕 ι j) ∧
      IsComplexHigherDirectImageColimit γ p a F cX cS hcS 𝓕 ι := by
  have := F.isStrictlyGE_of_isPullbackColimitPresentation a hpres
  exact ⟨fun c => complexLeg_cocone γ p a F cX cS hcS 𝓕 ι hι c,
    isComplexHigherDirectImageColimit γ hcX hcS F a hι hpres p⟩

end Tag

end Stacks.EtaleCohomology.LimitHigherDirectImage

end
