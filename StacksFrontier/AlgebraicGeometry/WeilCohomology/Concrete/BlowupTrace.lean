module

public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.TraceDiagonal
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.DisjointUnionIdempotent
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.BlowupPushforward

/-!
# Comparing two diagonal classes after restriction to points

This file carries out the cohomological part of the proof of Stacks 0FIS, for data (D0), (D1),
(D2') satisfying (A5) (`Stacks.WeilCohomology.FirstChernClassData.KunnethAxiom`).

Let `b : X' ⟶ X` be a morphism of smooth projective schemes over `k`, `g ∈ H^{2d}(X × X)(d)` and
`g' ∈ H^{2d}(X' × X')(d)` two classes (they will be the classes of the diagonals), and
`iⱼ : Pⱼ ⟶ X'` finitely many morphisms (they will be closed points of `X'`) such that `g` and `g'`
have the same pullback to every `Pⱼ × X'`, through `(b ∘ iⱼ) × b` and `iⱼ × 1`. If restriction to
the `Pⱼ` is injective on `H^0(X')`, then the contractions `(1 ⊗ λ')((b × b)^* g)` and
`(1 ⊗ λ') g'` agree for every `λ' : H^{2d}(X')(d) ⟶ F`. As `(1 ⊗ λ')((b × b)^* g)` is
`b^*((1 ⊗ λ' b^*) g)`, a trace `λ'` normalized for `g'` (axiom (A6) for `X'`) makes `λ' ∘ b^*`
normalized for `g`, when `b^*` is injective.

## Main results

* `Stacks.WeilCohomology.FirstChernClassData.symm_pull_prodMap`: naturality of the Künneth
  isomorphism of (A5).
* `Stacks.WeilCohomology.FirstChernClassData.traceContract_pullTw_prodMap`:
  `(1 ⊗ λ')((b × b)^* g) = b^*((1 ⊗ λ' b^*) g)`.
* `Stacks.WeilCohomology.FirstChernClassData.traceContract_eq_of_pullTw_points`: the comparison
  through the points.
* `Stacks.WeilCohomology.FirstChernClassData.traceContract_comp_pullTw_eq_one`: the conclusion
  `(1 ⊗ λ' b^*) g = 1`.

## References

* [Stacks Project, Tag 0FIS](https://stacks.math.columbia.edu/tag/0FIS)
-/

@[expose] public noncomputable section

open CategoryTheory TensorProduct

universe u w

namespace Stacks.WeilCohomology

namespace SmoothProjectiveScheme

variable {k : Type u} [Field k]

/-- The product `f × g : X' × Y' ⟶ X × Y` of two morphisms. -/
def prodMap {X' X Y' Y : (SmoothProjectiveScheme k).FullSubcategory} (f : X' ⟶ X) (g : Y' ⟶ Y) :
    prod X' Y' ⟶ prod X Y :=
  prodLift (fst X' Y' ≫ f) (snd X' Y' ≫ g)

/-- Composing `f × g` with the first projection gives the first projection followed by `f`. -/
@[reassoc (attr := simp)]
theorem prodMap_fst {X' X Y' Y : (SmoothProjectiveScheme k).FullSubcategory} (f : X' ⟶ X)
    (g : Y' ⟶ Y) :
    prodMap f g ≫ fst X Y = fst X' Y' ≫ f :=
  prodLift_fst _ _

/-- Composing `f × g` with the second projection gives the second projection followed by `g`. -/
@[reassoc (attr := simp)]
theorem prodMap_snd {X' X Y' Y : (SmoothProjectiveScheme k).FullSubcategory} (f : X' ⟶ X)
    (g : Y' ⟶ Y) :
    prodMap f g ≫ snd X Y = snd X' Y' ≫ g :=
  prodLift_snd _ _

/-- `(f' × g') ≫ (f × g) = (f' ≫ f) × (g' ≫ g)`. -/
theorem prodMap_comp {X'' X' X Y'' Y' Y : (SmoothProjectiveScheme k).FullSubcategory}
    (f' : X'' ⟶ X')
    (f : X' ⟶ X) (g' : Y'' ⟶ Y') (g : Y' ⟶ Y) :
    prodMap f' g' ≫ prodMap f g = prodMap (f' ≫ f) (g' ≫ g) :=
  prod_hom_ext (by simp) (by simp)

end SmoothProjectiveScheme

namespace FirstChernClassData

open SmoothProjectiveScheme

variable {k : Type u} [Field k] {F : Type w} [Field F] (𝔇 : FirstChernClassData k F)

/-! ### Naturality of the Künneth isomorphism -/

/-- `(f × g)^*(p^*a ∪ q^*b) = p^*(f^*a) ∪ q^*(g^*b)`. -/
theorem pull_prodMap_kunnethMap {X' X Y' Y : (SmoothProjectiveScheme k).FullSubcategory}
    (f : X' ⟶ X)
    (g : Y' ⟶ Y) (z : 𝔇.H X ⊗[F] 𝔇.H Y) :
    𝔇.pull (prodMap f g) (𝔇.kunnethMap X Y z) =
      𝔇.kunnethMap X' Y' (TensorProduct.map (𝔇.pull f).toLinearMap (𝔇.pull g).toLinearMap z) := by
  induction z using TensorProduct.inductionOn with
  | tmul a b =>
    rw [kunnethMap_tmul, map_mul, TensorProduct.map_tmul, kunnethMap_tmul,
      AlgHom.toLinearMap_apply, AlgHom.toLinearMap_apply]
    simp only [← AlgHom.comp_apply, ← 𝔇.pull_comp, prodMap_fst, prodMap_snd]
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]

/-- **Naturality of the Künneth isomorphism of (A5)** along a product of morphisms. -/
theorem symm_pull_prodMap (hA5 : 𝔇.KunnethAxiom)
    {X' X Y' Y : (SmoothProjectiveScheme k).FullSubcategory}
    (f : X' ⟶ X) (g : Y' ⟶ Y) (z : 𝔇.H (prod X Y)) :
    (𝔇.kunnethEquiv hA5 X' Y').symm (𝔇.pull (prodMap f g) z) =
      TensorProduct.map (𝔇.pull f).toLinearMap (𝔇.pull g).toLinearMap
        ((𝔇.kunnethEquiv hA5 X Y).symm z) := by
  rw [LinearEquiv.symm_apply_eq]
  conv_lhs => rw [← (𝔇.kunnethEquiv hA5 X Y).apply_symm_apply z]
  exact 𝔇.pull_prodMap_kunnethMap f g _

/-! ### Naturality of the contraction -/

/-- Pullback on twists is functorial. -/
theorem pullTw_pullTw {X Y Z : (SmoothProjectiveScheme k).FullSubcategory} (f : X ⟶ Y) (g : Y ⟶ Z)
    (n : ℤ)
    (x : tateTwist F 𝔇.tate (𝔇.H Z) n) :
    𝔇.pullTw f n (𝔇.pullTw g n x) = 𝔇.pullTw (f ≫ g) n x := by
  simp only [pullTw, tateTwistMap]
  rw [← LinearMap.comp_apply, ← TensorProduct.map_comp, LinearMap.id_comp, 𝔇.pull_comp]
  rfl

/-- `f^*` on `H^n(Y)(m) ⟶ H^n(X)(m)`, on the twisted graded pieces. -/
def pullGradeTw {X Y : (SmoothProjectiveScheme k).FullSubcategory} (f : X ⟶ Y) (n m : ℤ) :
    tateTwist F 𝔇.tate (𝔇.grade Y n) m →ₗ[F] tateTwist F 𝔇.tate (𝔇.grade X n) m :=
  tateTwistMap ((𝔇.pull f).toLinearMap.restrict (𝔇.pull_grade f n)) m

/-- Pullback commutes with the projection to a graded piece. -/
theorem projGrade_pull {X Y : (SmoothProjectiveScheme k).FullSubcategory} (f : X ⟶ Y) (n : ℤ)
    (a : 𝔇.H Y) :
    (𝔇.projGrade X n (𝔇.pull f a) : 𝔇.H X) = 𝔇.pull f (𝔇.projGrade Y n a) := by
  rw [coe_projGrade, coe_projGrade]
  exact decompose_map (𝔇.grade Y) (𝔇.grade X) (𝔇.pull f) (𝔇.pull_grade f) a n

/-- `λ ∘ f^*`, untwisted, is the untwisting of `λ` composed with `f^*`. -/
theorem untwistTrace_pull {X Y : (SmoothProjectiveScheme k).FullSubcategory} (f : X ⟶ Y) (d : ℕ)
    (lam : tateTwist F 𝔇.tate (𝔇.grade X (2 * (d : ℤ))) d →ₗ[F] F) (a : 𝔇.H Y) :
    𝔇.untwistTrace X d lam (𝔇.pull f a) =
      𝔇.untwistTrace Y d (lam ∘ₗ 𝔇.pullGradeTw f (2 * (d : ℤ)) d) a := by
  simp only [untwistTrace, LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe]
  congr 1
  apply (tateTwistCoordinates 𝔇.coord (d : ℤ)).injective
  rw [LinearEquiv.apply_symm_apply, pullGradeTw, tateTwistCoordinates_map,
    LinearEquiv.apply_symm_apply]
  exact Subtype.ext (𝔇.projGrade_pull f _ a)

/-- **`(1 ⊗ λ)((f × g)^* z) = f^*((1 ⊗ λ g^*) z)`**, in untwisted form. -/
theorem tensorContractRight_symm_pull_prodMap (hA5 : 𝔇.KunnethAxiom)
    {X' X Y' Y : (SmoothProjectiveScheme k).FullSubcategory} (f : X' ⟶ X) (g : Y' ⟶ Y)
    (μ : 𝔇.H Y' →ₗ[F] F) (z : 𝔇.H (prod X Y)) :
    tensorContractRight μ ((𝔇.kunnethEquiv hA5 X' Y').symm (𝔇.pull (prodMap f g) z)) =
      𝔇.pull f (tensorContractRight (μ ∘ₗ (𝔇.pull g).toLinearMap)
        ((𝔇.kunnethEquiv hA5 X Y).symm z)) := by
  rw [𝔇.symm_pull_prodMap hA5, tensorContractRight_map]
  rfl

/-- The contraction of (A6) is the untwisted contraction of the Künneth preimage. -/
theorem traceContract_eq (hA5 : 𝔇.KunnethAxiom) (X : (SmoothProjectiveScheme k).FullSubcategory)
    (d : ℕ)
    (lam : tateTwist F 𝔇.tate (𝔇.grade X (2 * (d : ℤ))) d →ₗ[F] F)
    (g : tateTwist F 𝔇.tate (𝔇.H (prod X X)) d) :
    𝔇.traceContract hA5 X d lam g =
      tensorContractRight (𝔇.untwistTrace X d lam)
        ((𝔇.kunnethEquiv hA5 X X).symm (𝔇.κ (prod X X) d g)) :=
  rfl

/-- **`(1 ⊗ λ')((b × b)^* g) = b^*((1 ⊗ λ' b^*) g)`.** -/
theorem traceContract_pullTw_prodMap (hA5 : 𝔇.KunnethAxiom)
    {X' X : (SmoothProjectiveScheme k).FullSubcategory}
    (b : X' ⟶ X) (d : ℕ) (lam : tateTwist F 𝔇.tate (𝔇.grade X' (2 * (d : ℤ))) d →ₗ[F] F)
    (g : tateTwist F 𝔇.tate (𝔇.H (prod X X)) d) :
    𝔇.traceContract hA5 X' d lam (𝔇.pullTw (prodMap b b) d g) =
      𝔇.pull b (𝔇.traceContract hA5 X d (lam ∘ₗ 𝔇.pullGradeTw b (2 * (d : ℤ)) d) g) := by
  rw [traceContract_eq, traceContract_eq, κ_pullTw, tensorContractRight_symm_pull_prodMap]
  congr 2
  exact congrArg tensorContractRight (LinearMap.ext (𝔇.untwistTrace_pull b d lam))

/-! ### Detecting the contraction on points -/

/-- The contraction of a class of `H^{2d}(X × X)(d)` lies in `H^0(X)`. -/
theorem traceContract_mem_grade_zero (hA5 : 𝔇.KunnethAxiom)
    (X : (SmoothProjectiveScheme k).FullSubcategory)
    (d : ℕ) (lam : tateTwist F 𝔇.tate (𝔇.grade X (2 * (d : ℤ))) d →ₗ[F] F)
    (g : tateTwist F 𝔇.tate (𝔇.H (prod X X)) d)
    (hg : 𝔇.κ (prod X X) d g ∈ 𝔇.grade (prod X X) (2 * (d : ℤ))) :
    𝔇.traceContract hA5 X d lam g ∈ 𝔇.grade X 0 := by
  obtain ⟨l, hl, hle⟩ := DiagonalExpansion.exists_expansion
    (fun m a ha => 𝔇.pull_grade _ m a ha) (fun m a ha => 𝔇.pull_grade _ m a ha) (hA5.2 X X).2 hg
  have h : (𝔇.kunnethEquiv hA5 X X).symm (𝔇.κ (prod X X) d g) = DiagonalExpansion.tensorSum l :=
    (LinearEquiv.symm_apply_eq _).2 hle.symm
  rw [traceContract_eq, h, DiagonalExpansion.map_tensorSum]
  refine list_sum_mem fun x hx => ?_
  obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hx
  obtain ⟨h1, h2⟩ := hl t ht
  rw [tensorContractRight_tmul]
  by_cases h0 : t.1 = 0
  · exact Submodule.smul_mem _ _ (h0 ▸ h1)
  · rw [𝔇.untwistTrace_eq_zero X d lam _ (by omega) _ h2, zero_smul]
    exact zero_mem _

/-- **The contraction is detected on points.** Let `iⱼ : Pⱼ ⟶ X` be finitely many morphisms such
that restriction to the `Pⱼ` is injective on `H^0(X)`, and let `δ ∈ H^{2d}(X × X)(d)` pull back
to zero on every `Pⱼ × X` along `iⱼ × 1`. Then `(1 ⊗ λ) δ = 0`. -/
theorem traceContract_eq_zero_of_pullTw_points (hA5 : 𝔇.KunnethAxiom)
    (X : (SmoothProjectiveScheme k).FullSubcategory) (d : ℕ)
    (lam : tateTwist F 𝔇.tate (𝔇.grade X (2 * (d : ℤ))) d →ₗ[F] F) {ι : Type*}
    {P : ι → (SmoothProjectiveScheme k).FullSubcategory} (i : ∀ j, P j ⟶ X)
    (hinj : ∀ a ∈ 𝔇.grade X 0, (∀ j, 𝔇.pull (i j) a = 0) → a = 0)
    (δ : tateTwist F 𝔇.tate (𝔇.H (prod X X)) d)
    (hδ : 𝔇.κ (prod X X) d δ ∈ 𝔇.grade (prod X X) (2 * (d : ℤ)))
    (h0 : ∀ j, 𝔇.pullTw (prodMap (i j) (𝟙 X)) d δ = 0) :
    𝔇.traceContract hA5 X d lam δ = 0 := by
  refine hinj _ (𝔇.traceContract_mem_grade_zero hA5 X d lam δ hδ) fun j => ?_
  have h := 𝔇.tensorContractRight_symm_pull_prodMap hA5 (i j) (𝟙 X) (𝔇.untwistTrace X d lam)
    (𝔇.κ (prod X X) d δ)
  rw [← κ_pullTw, h0 j, 𝔇.pull_id, AlgHom.toLinearMap_id, LinearMap.comp_id] at h
  simp only [map_zero] at h
  rw [traceContract_eq, ← h]

/-- **The normalization transported along `b`.** Let `b : X' ⟶ X`, let `g ∈ H^{2d}(X × X)(d)` and
`g' ∈ H^{2d}(X' × X')(d)`, and let `iⱼ : Pⱼ ⟶ X'` be finitely many morphisms detecting `H^0(X')`
such that `((b iⱼ) × b)^* g = (iⱼ × 1)^* g'` for every `j`. If `λ'` satisfies `(1 ⊗ λ') g' = 1` and
`b^*` is injective, then `(1 ⊗ λ' b^*) g = 1`. -/
theorem traceContract_comp_pullTw_eq_one (hA5 : 𝔇.KunnethAxiom)
    {X' X : (SmoothProjectiveScheme k).FullSubcategory} (b : X' ⟶ X)
    (hb : Function.Injective (𝔇.pull b))
    (d : ℕ) (g : tateTwist F 𝔇.tate (𝔇.H (prod X X)) d)
    (g' : tateTwist F 𝔇.tate (𝔇.H (prod X' X')) d)
    (hg : 𝔇.κ (prod X X) d g ∈ 𝔇.grade (prod X X) (2 * (d : ℤ)))
    (hg' : 𝔇.κ (prod X' X') d g' ∈ 𝔇.grade (prod X' X') (2 * (d : ℤ)))
    (lam' : tateTwist F 𝔇.tate (𝔇.grade X' (2 * (d : ℤ))) d →ₗ[F] F)
    (hlam' : 𝔇.traceContract hA5 X' d lam' g' = 1) {ι : Type*}
    {P : ι → (SmoothProjectiveScheme k).FullSubcategory} (i : ∀ j, P j ⟶ X')
    (hinj : ∀ a ∈ 𝔇.grade X' 0, (∀ j, 𝔇.pull (i j) a = 0) → a = 0)
    (hpts : ∀ j, 𝔇.pullTw (prodMap (i j ≫ b) b) d g = 𝔇.pullTw (prodMap (i j) (𝟙 X')) d g') :
    𝔇.traceContract hA5 X d (lam' ∘ₗ 𝔇.pullGradeTw b (2 * (d : ℤ)) d) g = 1 := by
  set δ := 𝔇.pullTw (prodMap b b) d g - g'
  have hδ : 𝔇.κ (prod X' X') d δ ∈ 𝔇.grade (prod X' X') (2 * (d : ℤ)) := by
    rw [map_sub, κ_pullTw]
    exact Submodule.sub_mem _ (𝔇.pull_grade _ _ _ hg) hg'
  have h0 : ∀ j, 𝔇.pullTw (prodMap (i j) (𝟙 X')) d δ = 0 := fun j => by
    rw [map_sub, sub_eq_zero, ← hpts j, 𝔇.pullTw_pullTw, prodMap_comp, Category.id_comp]
  have hc := 𝔇.traceContract_eq_zero_of_pullTw_points hA5 X' d lam' i hinj δ hδ h0
  rw [map_sub, sub_eq_zero, traceContract_pullTw_prodMap, hlam', ← map_one (𝔇.pull b)] at hc
  exact hb hc

end FirstChernClassData

end Stacks.WeilCohomology

end
