module

public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.DisjointUnionIdempotent
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.DimensionInduction
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.ProjectiveLine
public import StacksFrontier.AlgebraicGeometry.Chow.FamilyFibreDivisors.PointSectionCartier

/-!
# Stacks 0FHJ: the cohomology of a disjoint union

Let `W` be data (D0)–(D3) of Section 45.9 (Tag 0FHA) over the actual category of smooth projective
schemes over `k`, satisfying (A), (B) and (C), with coefficient field `F` of characteristic zero.
For smooth projective `X` and `Y` over `k` with disjoint union `Z = X ⨿ Y` and coprojections `i`,
`j`, the map `H^*(Z) → H^*(X) × H^*(Y)`, `a ↦ (i^*a, j^*a)` is an isomorphism (Stacks 0FHJ).

## Surjectivity of `i^*`

The source base changes to `Spec k'` for a finite separable `k'/k` with `X(k') ≠ ∅`, so that there
is a morphism `Y × Spec k' ⟶ X × Spec k'`. Any nonempty smooth projective `T` with a morphism
`T ⟶ X` serves, and `T = X` does: the morphism `Y × X ⟶ X × X`, `(y, x) ↦ (x, x)`, together with
the identity of `X × X`, glues to a retraction `g : Z × X ⟶ X × X` of `i × id`, because
`Z × X = (X × X) ⨿ (Y × X)` (coproducts of schemes are stable under base change). So
`(i × id)^*` is surjective, which by (B)(a) is `i^* ⊗ id : H^*(Z) ⊗ H^*(X) → H^*(X) ⊗ H^*(X)`;
as `H^*(X) ≠ 0` by Stacks 0FHF, `i^*` is surjective.

## References

* [Stacks Project, Tag 0FHJ](https://stacks.math.columbia.edu/tag/0FHJ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct

universe u w

namespace Stacks.WeilCohomology

variable {k : Type u} [Field k]

open SmoothProjectiveScheme

/-- A linear map `f` is surjective as soon as `f ⊗ id_V` is, for a nonzero vector space `V`. -/
theorem surjective_of_surjective_rTensor {F : Type w} [Field F] {M N V : Type w}
    [AddCommGroup M] [Module F M] [AddCommGroup N] [Module F N] [AddCommGroup V] [Module F V]
    [Nontrivial V] (f : M →ₗ[F] N) (hf : Function.Surjective (LinearMap.rTensor V f)) :
    Function.Surjective f := by
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  obtain ⟨φ, hφ⟩ : ∃ φ : Module.Dual F V, φ v = 1 := by
    obtain ⟨φ, hφ⟩ : ∃ φ : Module.Dual F V, φ v ≠ 0 := by
      by_contra! h
      exact hv ((Module.forall_dual_apply_eq_zero_iff F v).mp h)
    exact ⟨(φ v)⁻¹ • φ, by simp [hφ]⟩
  let ρ : ∀ (P : Type w) [AddCommGroup P] [Module F P], P ⊗[F] V →ₗ[F] P := fun P _ _ ↦
    (TensorProduct.rid F P).toLinearMap ∘ₗ LinearMap.lTensor P φ
  have hnat : ∀ t : M ⊗[F] V, ρ N (LinearMap.rTensor V f t) = f (ρ M t) := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul m x => simp [ρ]
    | add s t hs ht => rw [map_add, map_add, hs, ht, map_add, map_add]
  intro n
  obtain ⟨t, ht⟩ := hf (n ⊗ₜ[F] v)
  refine ⟨ρ M t, ?_⟩
  rw [← hnat, ht]
  simp [ρ, hφ]

namespace SmoothProjectiveScheme

/-- The product `f × id_W : X × W ⟶ Z × W` of a morphism with the identity of `W`. -/
def prodMapLeft {X Z : (SmoothProjectiveScheme k).FullSubcategory} (f : X ⟶ Z)
    (W : (SmoothProjectiveScheme k).FullSubcategory) :
    prod X W ⟶ prod Z W :=
  prodLift (fst X W ≫ f) (snd X W)

/-- The first projection of `f × id_W` is `f` composed with the first projection of `X × W`. -/
@[reassoc (attr := simp)]
theorem prodMapLeft_fst {X Z : (SmoothProjectiveScheme k).FullSubcategory} (f : X ⟶ Z)
    (W : (SmoothProjectiveScheme k).FullSubcategory) : prodMapLeft f W ≫ fst Z W = fst X W ≫ f :=
  prodLift_fst _ _

/-- The second projection of `f × id_W` is the second projection of `X × W`. -/
@[reassoc (attr := simp)]
theorem prodMapLeft_snd {X Z : (SmoothProjectiveScheme k).FullSubcategory} (f : X ⟶ Z)
    (W : (SmoothProjectiveScheme k).FullSubcategory) : prodMapLeft f W ≫ snd Z W = snd X W :=
  prodLift_snd _ _

/-- The square `X × W ⟶ Z × W` over `X ⟶ Z` is cartesian on underlying schemes. -/
theorem isPullback_prodMapLeft {X Z : (SmoothProjectiveScheme k).FullSubcategory} (f : X ⟶ Z)
    (W : (SmoothProjectiveScheme k).FullSubcategory) :
    IsPullback (prodMapLeft f W).hom.left (fst X W).hom.left (fst Z W).hom.left f.hom.left := by
  have hout : IsPullback ((prodMapLeft f W).hom.left ≫ (snd Z W).hom.left) (fst X W).hom.left
      W.obj.hom (f.hom.left ≫ Z.obj.hom) := by
    have h1 : (prodMapLeft f W).hom.left ≫ (snd Z W).hom.left = (snd X W).hom.left :=
      congrArg (fun φ ↦ φ.hom.left) (prodMapLeft_snd f W)
    rw [h1, Over.w f.hom]
    exact (IsPullback.of_hasPullback X.obj.hom W.obj.hom).flip
  exact IsPullback.of_right hout (congrArg (fun φ ↦ φ.hom.left) (prodMapLeft_fst f W))
    (IsPullback.of_hasPullback Z.obj.hom W.obj.hom).flip

/-- **Products with `W` preserve disjoint unions**: if `Z` is the coproduct of `X` and `Y`, then
`Z × W` is the coproduct of `X × W` and `Y × W`. Coproducts of schemes are universal
(`AlgebraicGeometry.Scheme` is finitary extensive). -/
def isColimitProdMapLeft {X Y Z : (SmoothProjectiveScheme k).FullSubcategory} {i : X ⟶ Z}
    {j : Y ⟶ Z}
    (hc : IsColimit (BinaryCofan.mk i j)) (W : (SmoothProjectiveScheme k).FullSubcategory) :
    IsColimit (BinaryCofan.mk (prodMapLeft i W) (prodMapLeft j W)) := by
  refine isColimitOfIsColimitMapCofan (Classical.choice ?_)
  have hvk := FinitaryExtensive.vanKampen _ (isColimitMapCofan hc)
  rw [BinaryCofan.isVanKampen_iff] at hvk
  exact (hvk (BinaryCofan.mk (prodMapLeft i W).hom.left (prodMapLeft j W).hom.left)
    (fst X W).hom.left (fst Y W).hom.left (fst Z W).hom.left
    (congrArg (fun φ ↦ φ.hom.left) (prodMapLeft_fst i W)).symm
    (congrArg (fun φ ↦ φ.hom.left) (prodMapLeft_fst j W)).symm).mpr
    ⟨isPullback_prodMapLeft i W, isPullback_prodMapLeft j W⟩

/-! ### Equalizing dimensions -/

/-- The `k`-point `0` of `𝐏¹_k`. -/
def projectiveLinePoint : point k ⟶ projectiveLineObj k :=
  ObjectProperty.homMk (Over.homMk (U := (point k).obj) (V := (projectiveLineObj k).obj)
    (Stacks.Chow.lineSection (Spec (.of k)) 0) (Stacks.Chow.lineSection_comp _ _))

/-- `(𝐏¹_k)^m`, a smooth projective scheme over `k` of dimension `m` with a `k`-point. -/
def projectiveLinePow : ℕ → (SmoothProjectiveScheme k).FullSubcategory
  | 0 => point k
  | m + 1 => prod (projectiveLinePow m) (projectiveLineObj k)

/-- The `k`-point `(0, …, 0)` of `(𝐏¹_k)^m`. -/
def projectiveLinePowPoint : (m : ℕ) → (point k ⟶ projectiveLinePow (k := k) m)
  | 0 => 𝟙 _
  | m + 1 => prodLift (projectiveLinePowPoint m) projectiveLinePoint

/-- `(𝐏¹_k)^m` has relative dimension `m` over `k`. -/
theorem relativeDimension_projectiveLinePow :
    ∀ m : ℕ, RelativeDimension (projectiveLinePow (k := k) m).obj.hom m
  | 0 => isNonemptyEquidimensional_point.relativeDimension
  | m + 1 => by
    have h := relativeDimension_prodBase k (projectiveLinePow (k := k) m).obj.hom
      (projectiveLineObj k).obj.hom (relativeDimension_projectiveLinePow m)
      (isNonemptyEquidimensional_projectiveLineObj k).relativeDimension
    rw [Nat.add_comm] at h
    exact h

/-- **Raising the dimension**: for `X` equidimensional of dimension `d`, the scheme
`X × (𝐏¹_k)^m` is equidimensional of dimension `m + d`, and its projection to `X` has the section
`x ↦ (x, 0)`. This is the scheme `X_d × 𝐏^{n-d}` of the source, with a power of `𝐏¹` in place of
a projective space. -/
theorem exists_retraction_relativeDimension_add {X : (SmoothProjectiveScheme k).FullSubcategory}
    {d : ℕ}
    (hX : RelativeDimension X.obj.hom d) (m : ℕ) :
    ∃ (X' : (SmoothProjectiveScheme k).FullSubcategory) (g : X' ⟶ X) (s : X ⟶ X'), s ≫ g = 𝟙 X ∧
      RelativeDimension X'.obj.hom (m + d) :=
  ⟨prod X (projectiveLinePow m), fst _ _, prodLift (𝟙 X) (toPoint X ≫ projectiveLinePowPoint m),
    prodLift_fst _ _, relativeDimension_prodBase k X.obj.hom _ hX
      (relativeDimension_projectiveLinePow m)⟩

/-- **A coproduct of retracts is a retract**: if `X` and `Y` are retracts of `X'` and `Y'`, then
`X ⨿ Y` is a retract of `X' ⨿ Y'`, compatibly with the coprojections. -/
theorem exists_retraction_coprodObj {X Y Z X' Y' : (SmoothProjectiveScheme k).FullSubcategory}
    {i : X ⟶ Z} {j : Y ⟶ Z} (hc : IsColimit (BinaryCofan.mk i j))
    {gX : X' ⟶ X} {sX : X ⟶ X'} (hX : sX ≫ gX = 𝟙 X)
    {gY : Y' ⟶ Y} {sY : Y ⟶ Y'} (hY : sY ≫ gY = 𝟙 Y) :
    ∃ (σ : Z ⟶ coprodObj X' Y') (γ : coprodObj X' Y' ⟶ Z), σ ≫ γ = 𝟙 Z ∧
      coprodInl X' Y' ≫ γ = gX ≫ i ∧ coprodInr X' Y' ≫ γ = gY ≫ j := by
  let σ : Z ⟶ coprodObj X' Y' := hc.desc (BinaryCofan.mk (P := coprodObj X' Y')
    (sX ≫ coprodInl X' Y') (sY ≫ coprodInr X' Y'))
  let γ : coprodObj X' Y' ⟶ Z := (isColimitCoprodCofan X' Y').desc
    (BinaryCofan.mk (P := Z) (gX ≫ i) (gY ≫ j))
  have hSl : i ≫ σ = sX ≫ coprodInl X' Y' := hc.fac _ ⟨WalkingPair.left⟩
  have hSr : j ≫ σ = sY ≫ coprodInr X' Y' := hc.fac _ ⟨WalkingPair.right⟩
  have hDl : coprodInl X' Y' ≫ γ = gX ≫ i := (isColimitCoprodCofan X' Y').fac _ ⟨WalkingPair.left⟩
  have hDr : coprodInr X' Y' ≫ γ = gY ≫ j :=
    (isColimitCoprodCofan X' Y').fac _ ⟨WalkingPair.right⟩
  refine ⟨σ, γ, BinaryCofan.IsColimit.hom_ext hc ?_ ?_, hDl, hDr⟩
  · show i ≫ σ ≫ γ = i ≫ 𝟙 Z
    rw [reassoc_of% hSl, hDl, reassoc_of% hX]
    exact (Category.comp_id _).symm
  · show j ≫ σ ≫ γ = j ≫ 𝟙 Z
    rw [reassoc_of% hSr, hDr, reassoc_of% hY]
    exact (Category.comp_id _).symm

/-- Retracts `X' ⟶ X`, `Y' ⟶ Y` of equidimensional schemes can be chosen of a common dimension
`N`, so that `X ⨿ Y` is a retract of `X'' ⨿ Y''`, compatibly with the coprojections. -/
private theorem exists_retraction_coprodObj_relativeDimension
    {X Y Z : (SmoothProjectiveScheme k).FullSubcategory} {i : X ⟶ Z} {j : Y ⟶ Z}
    (hc : IsColimit (BinaryCofan.mk i j))
    (hX : ∃ (M : ℕ) (X' : (SmoothProjectiveScheme k).FullSubcategory) (g : X' ⟶ X) (s : X ⟶ X'),
      s ≫ g = 𝟙 X ∧ RelativeDimension X'.obj.hom M)
    (hY : ∃ (M : ℕ) (Y' : (SmoothProjectiveScheme k).FullSubcategory) (g : Y' ⟶ Y) (s : Y ⟶ Y'),
      s ≫ g = 𝟙 Y ∧ RelativeDimension Y'.obj.hom M) :
    ∃ (N : ℕ) (X'' Y'' : (SmoothProjectiveScheme k).FullSubcategory) (gX : X'' ⟶ X) (gY : Y'' ⟶ Y)
      (σ : Z ⟶ coprodObj X'' Y'') (γ : coprodObj X'' Y'' ⟶ Z), σ ≫ γ = 𝟙 Z ∧
      coprodInl X'' Y'' ≫ γ = gX ≫ i ∧ coprodInr X'' Y'' ≫ γ = gY ≫ j ∧
      RelativeDimension X''.obj.hom N ∧ RelativeDimension Y''.obj.hom N := by
  obtain ⟨M₁, X', gX, sX, hX, hM₁⟩ := hX
  obtain ⟨M₂, Y', gY, sY, hY, hM₂⟩ := hY
  obtain ⟨X'', gX', sX', hX', hX''⟩ := exists_retraction_relativeDimension_add hM₁ (max M₁ M₂ - M₁)
  obtain ⟨Y'', gY', sY', hY', hY''⟩ := exists_retraction_relativeDimension_add hM₂ (max M₁ M₂ - M₂)
  rw [Nat.sub_add_cancel (le_max_left _ _)] at hX''
  rw [Nat.sub_add_cancel (le_max_right _ _)] at hY''
  obtain ⟨σ, γ, hσγ, hDl, hDr⟩ := exists_retraction_coprodObj hc
    (gX := gX' ≫ gX) (sX := sX ≫ sX') (by simp [reassoc_of% hX', hX])
    (gY := gY' ≫ gY) (sY := sY ≫ sY') (by simp [reassoc_of% hY', hY])
  exact ⟨_, X'', Y'', gX' ≫ gX, gY' ≫ gY, σ, γ, hσγ, hDl, hDr, hX'', hY''⟩

/-- **Every smooth projective scheme is a retract of an equidimensional one**: there are an
equidimensional smooth projective `X'` and morphisms `g : X' ⟶ X`, `s : X ⟶ X'` with
`s ≫ g = 𝟙`. This is the source's `X' = ∐ X_d × 𝐏^{n-d}`; it is obtained by induction on the
parts of `X` of constant dimension. -/
theorem exists_retraction_relativeDimension (X : (SmoothProjectiveScheme k).FullSubcategory) :
    ∃ (M : ℕ) (X' : (SmoothProjectiveScheme k).FullSubcategory) (g : X' ⟶ X) (s : X ⟶ X'), s ≫ g
        = 𝟙 X ∧
      RelativeDimension X'.obj.hom M := by
  refine induction_relativeDimension
      (fun X ↦ ∃ (M : ℕ) (X' : (SmoothProjectiveScheme k).FullSubcategory)
    (g : X' ⟶ X) (s : X ⟶ X'), s ≫ g = 𝟙 X ∧ RelativeDimension X'.obj.hom M) ?_ ?_ ?_ X
  · rintro X Y e ⟨M, X', g, s, hsg, hM⟩
    exact ⟨M, X', g ≫ e.hom, e.inv ≫ s, by simp [reassoc_of% hsg], hM⟩
  · rintro U V c hc hU hV
    obtain ⟨N, U'', V'', -, -, σ, γ, hσγ, -, -, hU'', hV''⟩ :=
      exists_retraction_coprodObj_relativeDimension (WeilData.isColimitMkOfIsColimit hc) hU hV
    exact ⟨N, coprodObj U'' V'', γ, σ, hσγ,
      relativeDimension_pt (isColimitCoprodCofan U'' V'') hU'' hV''⟩
  · exact fun X d hd ↦ ⟨d, X, 𝟙 X, 𝟙 X, Category.id_comp _, hd⟩

end SmoothProjectiveScheme

namespace WeilData

variable {F : Type w} [Field F] {W : WeilData k F}

/-- **Naturality of the Künneth map** in the first factor: `(f × id)^*(pr₁^*a ∪ pr₂^*b) =
pr₁^*(f^*a) ∪ pr₂^*b`. -/
theorem pull_prodMapLeft_comp_kunnethMap {X Z : (SmoothProjectiveScheme k).FullSubcategory}
    (f : X ⟶ Z)
    (T : (SmoothProjectiveScheme k).FullSubcategory) :
    (W.pull (prodMapLeft f T)).toLinearMap ∘ₗ W.kunnethMap Z T =
      W.kunnethMap X T ∘ₗ LinearMap.rTensor (W.H T) (W.pull f).toLinearMap := by
  refine TensorProduct.ext' fun a b ↦ ?_
  simp only [LinearMap.coe_comp, Function.comp_apply, kunnethMap_tmul, AlgHom.toLinearMap_apply,
    map_mul, LinearMap.rTensor_tmul]
  rw [← AlgHom.comp_apply, ← AlgHom.comp_apply, ← W.pull_comp, ← W.pull_comp, ← AlgHom.comp_apply,
    ← W.pull_comp, prodMapLeft_fst, prodMapLeft_snd]

/-- If `s ≫ g = 𝟙`, then `g^*` is a right inverse of `s^*`. -/
theorem pull_leftInverse_of_comp_eq_id {A B : (SmoothProjectiveScheme k).FullSubcategory}
    {s : A ⟶ B} {g : B ⟶ A} (h : s ≫ g = 𝟙 A) :
    Function.LeftInverse (W.pull s) (W.pull g) := fun y ↦ by
  rw [← AlgHom.comp_apply, ← W.pull_comp, h, W.pull_id, AlgHom.id_apply]

variable {X Y Z : (SmoothProjectiveScheme k).FullSubcategory} {i : X ⟶ Z} {j : Y ⟶ Z}

/-- **`i^*` is surjective** for the coprojection `i : X ⟶ X ⨿ Y` with `X` nonempty, under (A), (B)
and (C) and `F` of characteristic zero. -/
theorem pull_surjective_of_isColimit [CharZero F] (hA : W.PoincareDuality) (hB : W.Kunneth)
    (hC : W.CycleClassAxiom hA.perfectPairing) (hc : IsColimit (BinaryCofan.mk i j))
    [Nonempty X.obj.left] : Function.Surjective (W.pull i) := by
  have hcX := isColimitProdMapLeft hc X
  -- the retraction `Z × X ⟶ X × X` of `i × id`
  let g : prod Z X ⟶ prod X X :=
    hcX.desc (BinaryCofan.mk (𝟙 (prod X X)) (prodLift (snd Y X) (snd Y X)))
  have hg : prodMapLeft i X ≫ g = 𝟙 _ :=
    hcX.fac (BinaryCofan.mk (𝟙 (prod X X)) (prodLift (snd Y X) (snd Y X))) ⟨WalkingPair.left⟩
  have := nontrivial_of_nonempty hA hB hC X
  refine surjective_of_surjective_rTensor (V := W.H X) (W.pull i).toLinearMap fun t ↦ ?_
  obtain ⟨y, hy⟩ := (pull_leftInverse_of_comp_eq_id (W := W) hg).surjective (W.kunnethMap X X t)
  obtain ⟨s, rfl⟩ := (hB.kunnethIsomorphism Z X).2 y
  refine ⟨s, (hB.kunnethIsomorphism X X).1 ?_⟩
  rw [← hy]
  exact (LinearMap.congr_fun (pull_prodMapLeft_comp_kunnethMap (W := W) i X) s).symm

/-- A morphism of graded algebras commutes with taking homogeneous components. -/
theorem pull_decompose {X Y : (SmoothProjectiveScheme k).FullSubcategory} (f : X ⟶ Y) (a : W.H Y)
    (n : ℤ) :
    (DirectSum.decompose (W.grade X) (W.pull f a) n : W.H X) =
      W.pull f (DirectSum.decompose (W.grade Y) a n) := by
  classical
  induction a using DirectSum.Decomposition.inductionOn (W.grade Y) with
  | zero => simp
  | @homogeneous m x =>
    obtain ⟨x, hx⟩ := x
    by_cases hmn : m = n
    · subst hmn
      rw [DirectSum.decompose_of_mem_same _ hx,
        DirectSum.decompose_of_mem_same _ (W.pull_grade f m x hx)]
    · rw [DirectSum.decompose_of_mem_ne _ hx hmn,
        DirectSum.decompose_of_mem_ne _ (W.pull_grade f m x hx) hmn, map_zero]
  | add x y hx hy => rw [map_add, DirectSum.decompose_add, DirectSum.decompose_add,
      DFinsupp.add_apply, DFinsupp.add_apply, Submodule.coe_add, Submodule.coe_add, hx, hy,
      map_add]

/-- **Injectivity for equidimensional summands of the same dimension**: if `X` and `Y` are
nonempty and equidimensional of dimension `d`, a class on `X ⨿ Y` restricting to zero on `X` and
on `Y` vanishes. Each homogeneous component `a` satisfies `a = i_*(i^*a) + j_*(j^*a)`
(`Stacks.WeilCohomology.WeilData.eq_pushforward_pullTw_add_of_isColimit`). -/
theorem eq_zero_of_pull_eq_zero_of_isNonemptyEquidimensional (hA : W.PoincareDuality)
    (hB : W.Kunneth) (hC : W.CycleClassAxiom hA.perfectPairing)
    (hc : IsColimit (BinaryCofan.mk i j)) {d : ℕ} (hX : IsNonemptyEquidimensional X d)
    (hY : IsNonemptyEquidimensional Y d) (hZ : IsNonemptyEquidimensional Z d) (a : W.H Z)
    (hi : W.pull i a = 0) (hj : W.pull j a = 0) : a = 0 := by
  classical
  have hcomp : ∀ n : ℤ, (DirectSum.decompose (W.grade Z) a n : W.H Z) = 0 := by
    intro n
    set x : W.grade Z n := DirectSum.decompose (W.grade Z) a n
    let y : W.Tw Z n 0 := (W.twCoord Z n 0).symm x
    have hp : ∀ {T : (SmoothProjectiveScheme k).FullSubcategory} (f : T ⟶ Z),
        W.pull f a = 0 → W.pullTw f n 0 y = 0 := fun {T} f hf ↦ by
      apply (W.twCoord T n 0).injective
      apply Subtype.ext
      rw [twCoord_pullTw, coe_pullDeg, LinearEquiv.apply_symm_apply, map_zero,
        ZeroMemClass.coe_zero, ← pull_decompose, hf, DirectSum.decompose_zero]
      rfl
    have hy := eq_pushforward_pullTw_add_of_isColimit hA hB hC hc hX hY hZ n 0 y
    rw [hp i hi, hp j hj, map_zero, map_zero, add_zero] at hy
    have hx : x = 0 := by
      have := congrArg (W.twCoord Z n 0) hy
      rwa [LinearEquiv.apply_symm_apply, map_zero] at this
    rw [hx, ZeroMemClass.coe_zero]
  rw [← DirectSum.sum_support_decompose (W.grade Z) a]
  exact Finset.sum_eq_zero fun n _ ↦ hcomp n

/-- An empty smooth projective scheme is an initial object. -/
def isInitialOfIsEmpty' (T : (SmoothProjectiveScheme k).FullSubcategory)
    [IsEmpty T.obj.left] : IsInitial T :=
  IsInitial.ofUniqueHom (fun T' ↦ homOfIsEmpty T T') (fun _ _ ↦ hom_ext_of_isEmpty _ _)

/-- **Injectivity for summands of the same dimension**, allowing empty summands: if `X` and `Y`
have relative dimension `d` over `k`, then `(i^*, j^*)` is injective on `H^*(X ⨿ Y)`. If `X` is
empty, `j` is an isomorphism. -/
theorem pull_prod_injective_of_relativeDimension (hA : W.PoincareDuality) (hB : W.Kunneth)
    (hC : W.CycleClassAxiom hA.perfectPairing) (hc : IsColimit (BinaryCofan.mk i j)) {d : ℕ}
    (hX : RelativeDimension X.obj.hom d) (hY : RelativeDimension Y.obj.hom d) :
    Function.Injective ((W.pull i).prod (W.pull j)) := by
  rcases isEmpty_or_nonempty X.obj.left with hXe | hXne
  · have := hXe
    have hiso : IsIso j := (BinaryCofan.isColimit_iff_isIso_inr (isInitialOfIsEmpty' X) _).mp ⟨hc⟩
    intro a b hab
    have h := congrArg Prod.snd hab
    simp only [AlgHom.prod_apply] at h
    exact (pull_leftInverse_of_comp_eq_id (W := W) (IsIso.inv_hom_id j)).injective h
  rcases isEmpty_or_nonempty Y.obj.left with hYe | hYne
  · have := hYe
    have hiso : IsIso i := (BinaryCofan.isColimit_iff_isIso_inl (isInitialOfIsEmpty' Y) _).mp ⟨hc⟩
    intro a b hab
    have h := congrArg Prod.fst hab
    simp only [AlgHom.prod_apply] at h
    exact (pull_leftInverse_of_comp_eq_id (W := W) (IsIso.inv_hom_id i)).injective h
  have hX' : IsNonemptyEquidimensional X d := ⟨hXne, hX⟩
  have hY' : IsNonemptyEquidimensional Y d := ⟨hYne, hY⟩
  have hZ : IsNonemptyEquidimensional Z d :=
    ⟨nonempty_pt_of_left (c := BinaryCofan.mk i j), relativeDimension_pt hc hX hY⟩
  intro a b hab
  have hi := congrArg Prod.fst hab
  have hj := congrArg Prod.snd hab
  simp only [AlgHom.prod_apply] at hi hj
  rw [← sub_eq_zero]
  exact eq_zero_of_pull_eq_zero_of_isNonemptyEquidimensional hA hB hC hc hX' hY' hZ _
    (by rw [map_sub, hi, sub_self]) (by rw [map_sub, hj, sub_self])

/-- **Injectivity of `(i^*, j^*)`**, for arbitrary smooth projective `X` and `Y`. The source
replaces `X` and `Y` by equidimensional schemes `X'`, `Y'` of a common dimension of which they
are retracts
(`Stacks.WeilCohomology.SmoothProjectiveScheme.exists_retraction_relativeDimension`),
so that `X ⨿ Y` is a retract of `X' ⨿ Y'`, compatibly with the coprojections. -/
theorem pull_prod_injective (hA : W.PoincareDuality) (hB : W.Kunneth)
    (hC : W.CycleClassAxiom hA.perfectPairing) (hc : IsColimit (BinaryCofan.mk i j)) :
    Function.Injective ((W.pull i).prod (W.pull j)) := by
  obtain ⟨N, X'', Y'', gX, gY, σ, γ, hσγ, hDl, hDr, hX'', hY''⟩ :=
    exists_retraction_coprodObj_relativeDimension hc (exists_retraction_relativeDimension X)
      (exists_retraction_relativeDimension Y)
  have hinj := pull_prod_injective_of_relativeDimension hA hB hC (isColimitCoprodCofan X'' Y'')
    hX'' hY''
  intro a b hab
  have hi := congrArg Prod.fst hab
  have hj := congrArg Prod.snd hab
  simp only [AlgHom.prod_apply] at hi hj
  have key : ∀ {T S : (SmoothProjectiveScheme k).FullSubcategory} (m : T ⟶ coprodObj X'' Y'')
      (g : T ⟶ S) (f : S ⟶ Z), m ≫ γ = g ≫ f → ∀ x, W.pull m (W.pull γ x) = W.pull g (W.pull f x) :=
    fun m g f h x ↦ by rw [← AlgHom.comp_apply, ← W.pull_comp, h, W.pull_comp, AlgHom.comp_apply]
  have hγ : W.pull γ a = W.pull γ b := by
    refine hinj ?_
    simp only [AlgHom.prod_apply, Prod.mk.injEq]
    exact ⟨by rw [key _ _ _ hDl, key _ _ _ hDl, hi], by rw [key _ _ _ hDr, key _ _ _ hDr, hj]⟩
  exact (pull_leftInverse_of_comp_eq_id (W := W) hσγ).injective hγ

/-- **`(i^*, j^*)` is bijective** for a coproduct cofan `BinaryCofan.mk i j`. -/
theorem pull_prod_bijective [CharZero F] (hA : W.PoincareDuality) (hB : W.Kunneth)
    (hC : W.CycleClassAxiom hA.perfectPairing) (hc : IsColimit (BinaryCofan.mk i j)) :
    Function.Bijective ((W.pull i).prod (W.pull j)) := by
  refine ⟨pull_prod_injective hA hB hC hc, ?_⟩
  have hsurj : ∀ {X Y : (SmoothProjectiveScheme k).FullSubcategory} {i : X ⟶ Z} {j : Y ⟶ Z},
      IsColimit (BinaryCofan.mk i j) → Function.Surjective (W.pull i) := by
    intro X Y i j hc
    rcases isEmpty_or_nonempty X.obj.left with hXe | hXne
    · have := hXe
      have := subsingleton_of_isEmpty hB.kunnethIsomorphism hC.pullback hC.mul hC.point X
      exact fun b ↦ ⟨0, Subsingleton.elim _ _⟩
    · exact pull_surjective_of_isColimit hA hB hC hc
  exact pull_prod_surjective_of_surjective hB.kunnethIsomorphism hC.pullback hC.mul hC.point hc
    (hsurj hc) (hsurj (isColimitSwap hc))

/-- Assume given (D0)–(D3) satisfying (A), (B) and (C), with coefficient field `F` of
characteristic zero. If `X` and `Y` are smooth projective schemes over `k`, then
`H^*(X ⨿ Y) → H^*(X) × H^*(Y)`, `a ↦ (i^*a, j^*a)` is an isomorphism, where `i`, `j` are the
coprojections. Here `X ⨿ Y` is any coproduct of `X` and `Y` in the category of smooth projective
schemes over `k`, given by a colimit cofan `c`. -/
@[stacks 0FHJ "H^*(X ⨿ Y) → H^*(X) × H^*(Y), a ↦ (i^*a, j^*a), is bijective, for any coproduct \
cofan of X and Y in the actual category of smooth projective schemes over k"]
theorem pullbackPair_bijective_of_isColimit [CharZero F] (hA : W.PoincareDuality)
    (hB : W.Kunneth) (hC : W.CycleClassAxiom hA.perfectPairing)
        {X Y : (SmoothProjectiveScheme k).FullSubcategory}
    {c : BinaryCofan X Y} (hc : IsColimit c) :
    Function.Bijective fun a : W.H c.pt ↦ (W.pull c.inl a, W.pull c.inr a) :=
  pull_prod_bijective (Z := c.pt) hA hB hC (isColimitMkOfIsColimit hc)

/-- For smooth projective `X` and `Y` over `k`, restriction to the two coprojections is an
isomorphism of `F`-algebras `H^*(X ⨿ Y) ≃ H^*(X) × H^*(Y)`, where `X ⨿ Y` is the coproduct in the
category of smooth projective schemes over `k`. -/
@[stacks 0FHJ "the F-algebra isomorphism H^*(X ⨿ Y) ≃ H^*(X) × H^*(Y), a ↦ (i^*a, j^*a), for \
the coproduct X ⨿ Y in the actual category of smooth projective schemes over k"]
def coprodAlgEquiv [CharZero F] (hA : W.PoincareDuality) (hB : W.Kunneth)
    (hC : W.CycleClassAxiom hA.perfectPairing) (X Y : (SmoothProjectiveScheme k).FullSubcategory) :
    W.H (X ⨿ Y) ≃ₐ[F] W.H X × W.H Y :=
  AlgEquiv.ofBijective ((W.pull (coprod.inl : X ⟶ X ⨿ Y)).prod (W.pull coprod.inr))
    (pull_prod_bijective hA hB hC (coprodIsCoprod X Y))

/-- `coprodAlgEquiv` sends `a` to its pair of pullbacks `(i^*a, j^*a)` along the coprojections. -/
@[simp]
theorem coprodAlgEquiv_apply [CharZero F] (hA : W.PoincareDuality) (hB : W.Kunneth)
    (hC : W.CycleClassAxiom hA.perfectPairing) (X Y : (SmoothProjectiveScheme k).FullSubcategory)
    (a : W.H (X ⨿ Y)) :
    coprodAlgEquiv hA hB hC X Y a = (W.pull coprod.inl a, W.pull coprod.inr a) :=
  rfl

end WeilData

end Stacks.WeilCohomology

end
