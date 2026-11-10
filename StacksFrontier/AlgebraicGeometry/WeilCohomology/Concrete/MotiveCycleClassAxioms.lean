module

public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.DualityUnitName
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.FundamentalClassMotive
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.MotiveCycleClass
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.RationalPointSummands
public import StacksFrontier.CategoryTheory.Graded.TwistedKaroubiTateTensorHom
public import StacksFrontier.CategoryTheory.GradedObject.MonoidalFunctorKunneth
public import StacksFrontier.AlgebraicGeometry.Morphisms.Projective.AffineBase
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Correspondences.SmoothProjectiveComposition

/-!
# Axioms (C)(b) and (C)(d) for the cycle class map of a realization

Let `G : M_k ⥤ graded F-vector spaces` be a monoidal functor, additive, with compatible
generators `eₙ ∈ G(𝟏(n))^{-2n}` (Stacks 0FH1, second paragraph of the proof). The cycle class of
`α ∈ CH^i(X)` is `γ(α) = G(a_α)(e_{-i})`, with `a_α : 𝟏(-i) ⟶ h(X)` the correspondence of `α`
(`Stacks.WeilCohomology.ChowMotiveCat.cycleClassMotive`), the cup product of `H^*(X) = G(h(X))`
is `G` of the multiplication `[Γ_Δ]` of `h(X)`, and the trace of `X` equidimensional of dimension
`d` is `∫_X x = G([X])(x ⊗ e_d)`. This file proves two parts of axiom (C) in the proof of
Stacks 0FH1 for these data.

* (C)(d): `∫_{Spec k} γ([Spec k]) = 1`, because the cycle `[Spec k]` is the identity
  correspondence of `Spec k`: `[Spec k] ∘ a_{[Spec k]} = 1` in the category of correspondences.
* (C)(b): `∫_X f^*b ∪ γ(α) = ∫_Y b ∪ γ(f_*α)`. Both sides are `G` of a morphism
  `h(Y) ⊗ 𝟏(n) ⟶ 𝟏` applied to `b ⊗ e_n`, the morphisms being
  `(([Γ_f] ⊗ a_α) ≫ [Γ_Δ]) ≫ [X]` and `((1 ⊗ a_{f_*α}) ≫ [Γ_Δ]) ≫ [Y]` up to the products of
  Tate twists; these agree by Stacks 0FG8
  (`Stacks.WeilCohomology.tensorHom_graphHom_pointCorrHom_comp_fundamentalClassHom`).

The comparisons are proved for an arbitrary graded monoidal category `C` in namespace
`CategoryTheory.GradedCategory.TwistedKaroubi` and specialised: comparing morphisms of motives
built over different spellings of the same objects (`𝟏(n)` and `T(n)`, `h(X) ⊗ 𝟏(n)` and
`X × Spec k`) makes `isDefEq` unfold correspondences down to cycles.

## Main results

* `Stacks.WeilCohomology.pointCorrHom_tensorUnit_comp_fundamentalClassHom`:
  `[Spec k] ∘ a_{[Spec k]} = 1`.
* `Stacks.WeilCohomology.graphHom_tensorHom_pointCorrHom_mul_comp_fundamentalClassHom`:
  `(([Γ_f] ⊗ a_α) ≫ μ_X) ≫ [X] = ((1 ⊗ a_{f_*α}) ≫ μ_Y) ≫ [Y]`.
* `Stacks.WeilCohomology.ChowMotiveCat.gradedTrace_cycleClassMotive_point`: axiom (C)(d).
* `Stacks.WeilCohomology.ChowMotiveCat.gradedTrace_gradedMonMul_cycleClassMotive_pushforward`:
  the axiom (C)(b).

## References

* [Stacks Project, Tag 0FH1](https://stacks.math.columbia.edu/tag/0FH1)
* [Stacks Project, Tag 0FG8](https://stacks.math.columbia.edu/tag/0FG8)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory MonoidalCategory Stacks.Chow

universe u w

namespace CategoryTheory.GradedCategory.TwistedKaroubi

/- As in `StacksFrontier.CategoryTheory.Graded.TwistedKaroubiUnitTwistTrace`, the tensor product of
triples is taken through `TwistedKaroubi.monoidalCategory`. -/
attribute [-instance] TwistedKaroubi.monoidalCategoryStruct

/-- `G.map` of a composite acts on elements as the composite of the actions. -/
private theorem map_comp_apply_hom {D : Type*} [Category D] {F : Type*} [Field F]
    (G : D ⥤ GradedObject ℤ (ModuleCat F)) {A B E : D} (f : A ⟶ B) (g : B ⟶ E) (n : ℤ)
    (w : G.obj A n) : (G.map (f ≫ g) n).hom w = (G.map g n).hom ((G.map f n).hom w) := by
  rw [G.map_comp]
  rfl

variable {R : Type*} [Ring R] {C : Type*} [Category C] [Preadditive C] [GradedCategory R C]
  [MonoidalCategory C] [IsGradedMonoidal R C]

/-- If `f : T(n) ⟶ (A, 1, 0)` and `a : A ⟶ 𝟙` compose to the identity of `𝟙`, then
`(f ⊗ T(d)) ≫ a` is the product of twisted units `T(n) ⊗ T(d) ≅ T(0)`, `n + d = 0`. -/
theorem whiskerRight_comp_unitTwistTrace {A : C} {n d : ℤ} (f : tateTriple R C n ⟶ ofObj (R := R) A)
    (a : A ⟶ 𝟙_ C) (ha : a ∈ grade (R := R) A (𝟙_ C) (-d)) (h : f.val ≫ a = 𝟙 (𝟙_ C))
    (hnd : n + d = 0) :
    (f ▷ tateTriple R C d) ≫ unitTwistTrace d a ha = (unitTwistTensorIsoOfEq n d 0 hnd).hom := by
  apply hom_ext
  have key : ∀ g : 𝟙_ C ⟶ A, g ≫ a = 𝟙 (𝟙_ C) →
      (g ⊗ₘ 𝟙 (𝟙_ C)) ≫ (ρ_ A).hom ≫ a = (ρ_ (𝟙_ C)).hom := fun g hg ↦ by
    rw [MonoidalCategory.tensorHom_id, MonoidalCategory.rightUnitor_naturality_assoc, hg,
      Category.comp_id]
  rw [comp_val, whiskerRight_val, unitTwistTrace_val, unitTwistTensorIsoOfEq_hom_val]
  exact key f.val h

variable {F : Type*} [Field F] (G : TwistedKaroubi R C ⥤ GradedObject ℤ (ModuleCat F))
  [G.Monoidal]

/-- The trace attached to `a : A ⟶ 𝟙` of the image of `x` under `f : T(n) ⟶ (A, 1, 0)` is the
counit of the product of `x` and `e` in `G(T(0))`, when `f` followed by `a` is the identity. -/
theorem gradedTrace_unitTwistTrace_map {A : C} {n d : ℤ} (hnd : n + d = 0)
    (f : tateTriple R C n ⟶ ofObj (R := R) A) (a : A ⟶ 𝟙_ C)
    (ha : a ∈ grade (R := R) A (𝟙_ C) (-d)) (h : f.val ≫ a = 𝟙 (𝟙_ C)) {m s : ℤ}
    (hms : m + s = 0) (x : G.obj (tateTriple R C n) m) (y : G.obj (tateTriple R C d) s) :
    G.gradedTrace (unitTwistTrace d a ha) y m hms ((G.map f m).hom x) =
      G.gradedCounit (tateMul G n d 0 hnd m s 0 hms x y) := by
  have hc : ∀ w, (G.map (unitTwistTrace d a ha) 0).hom ((G.map (f ▷ tateTriple R C d) 0).hom w) =
      (G.map (unitTwistTensorIsoOfEq n d 0 hnd).hom 0).hom w := fun w ↦ by
    rw [← map_comp_apply_hom G, whiskerRight_comp_unitTwistTrace f a ha h hnd]
    rfl
  rw [Functor.gradedTrace_apply, ← Functor.map_whiskerRight_gradedMul, tateMul_apply, hc]

/-- The counit of a product `e_n e_d` of compatible generators, `n + d = 0`, is `1`. -/
theorem gradedCounit_tateMul_eq_one (e : ∀ n : ℤ, G.obj (tateTriple R C n) (-2 * n))
    (he0 : e 0 ≍ tateOne G)
    (hemul : ∀ n m : ℤ, tateMul G n m (n + m) rfl (-2 * n) (-2 * m) (-2 * (n + m)) (by ring)
      (e n) (e m) = e (n + m))
    {n d m s : ℤ} (hnd : n + d = 0) (hms : m + s = 0) (hm : m = -2 * n) (hs : s = -2 * d)
    (x : G.obj (tateTriple R C n) m) (hx : x ≍ e n) (y : G.obj (tateTriple R C d) s)
    (hy : y ≍ e d) :
    G.gradedCounit (tateMul G n d 0 hnd m s 0 hms x y) = 1 := by
  have h₁ : tateMul G n d 0 hnd m s 0 hms x y ≍ tateOne G := by
    refine (tateMul_heq G hnd rfl hms (show -2 * n + -2 * d = -2 * (n + d) by ring) hnd.symm hm hs
      hx hy).trans ?_
    rw [hemul]
    exact (congr_arg_heq e hnd).trans he0
  rw [eq_of_heq h₁]
  exact G.gradedCounit_gradedOne

/-- **The trace of the image of a generator is `1`**: if `f : M ⟶ (A, 1, 0)` with `M = T(n)`
followed by `a : A ⟶ 𝟙` is the identity, then `G(a)(G(f)(eₙ) ⊗ e_d) = 1` for compatible
generators `eₙ` and `n + d = 0`. -/
theorem gradedTrace_unitTwistTrace_map_eq_one (e : ∀ n : ℤ, G.obj (tateTriple R C n) (-2 * n))
    (he0 : e 0 ≍ tateOne G)
    (hemul : ∀ n m : ℤ, tateMul G n m (n + m) rfl (-2 * n) (-2 * m) (-2 * (n + m)) (by ring)
      (e n) (e m) = e (n + m))
    {A : C} {M : TwistedKaroubi R C} {n d : ℤ} (hM : M = tateTriple R C n) (hnd : n + d = 0)
    (f : M ⟶ ofObj (R := R) A) (a : A ⟶ 𝟙_ C) (ha : a ∈ grade (R := R) A (𝟙_ C) (-d))
    (h : ∀ g : 𝟙_ C ⟶ A, g ≍ f.val → g ≫ a = 𝟙 (𝟙_ C)) {m s : ℤ} (hms : m + s = 0)
    (hm : m = -2 * n) (hs : s = -2 * d) (x : G.obj M m) (hx : x ≍ e n)
    (y : G.obj (tateTriple R C d) s) (hy : y ≍ e d) :
    G.gradedTrace (unitTwistTrace d a ha) y m hms ((G.map f m).hom x) = 1 := by
  subst hM
  rw [gradedTrace_unitTwistTrace_map G hnd f a ha (h f.val HEq.rfl) hms x y]
  exact gradedCounit_tateMul_eq_one G e he0 hemul hnd hms hm hs x hx y hy

/-- The inverse of the product of twisted units is the inverse right unitor of `𝟙`. -/
theorem unitTwistTensorIsoOfEq_inv_val (n m p : ℤ) (h : n + m = p) :
    (unitTwistTensorIsoOfEq (R := R) (C := C) n m p h).inv.val = (ρ_ (𝟙_ C)).inv := by
  have h₁ := congrArg Subtype.val (unitTwistTensorIsoOfEq (R := R) (C := C) n m p h).hom_inv_id
  rw [comp_val, unitTwistTensorIsoOfEq_hom_val] at h₁
  have key : ∀ g : 𝟙_ C ⟶ 𝟙_ C ⊗ 𝟙_ C, (ρ_ (𝟙_ C)).hom ≫ g = 𝟙 (𝟙_ C) ⊗ₘ 𝟙 (𝟙_ C) →
      g = (ρ_ (𝟙_ C)).inv := fun g hg ↦ by
    rw [MonoidalCategory.id_tensorHom_id, ← Iso.eq_inv_comp, Category.comp_id] at hg
    exact hg
  exact key _ h₁

/-- `G(Φ)(b ⊗ z)` depends on `Φ : (A, 1, 0) ⊗ T(N) ⟶ 𝟙` only through the underlying morphism,
and on `z` only up to heterogeneous equality. -/
theorem gradedCounit_map_gradedMul_congr {A : C} {N N' : ℤ} (hN : N = N')
    (Φ : ofObj (R := R) A ⊗ tateTriple R C N ⟶ 𝟙_ (TwistedKaroubi R C))
    (Φ' : ofObj (R := R) A ⊗ tateTriple R C N' ⟶ 𝟙_ (TwistedKaroubi R C))
    (u : A ⊗ 𝟙_ C ⟶ 𝟙_ C) (hΦ : Φ.val = u) (hΦ' : Φ'.val = u) {i k k' : ℤ} (hk : k = k')
    (hik : i + k = 0) (hik' : i + k' = 0) (b : G.obj (ofObj (R := R) A) i)
    (z : G.obj (tateTriple R C N) k) (z' : G.obj (tateTriple R C N') k') (hz : z ≍ z') :
    G.gradedCounit ((G.map Φ 0).hom (G.gradedMul _ _ i k 0 hik b z)) =
      G.gradedCounit ((G.map Φ' 0).hom (G.gradedMul _ _ i k' 0 hik' b z')) := by
  subst hN hk
  obtain rfl := eq_of_heq hz
  obtain rfl : Φ = Φ' := hom_ext (hΦ.trans hΦ'.symm)
  rfl

/-- **The trace of a product with a generator, through the product of twisted units.** For
`φ : (A, 1, 0) ⊗ M ⟶ (B, 1, 0)` with `M = T(n)`, `t : B ⟶ 𝟙` of degree `-d`, `b ∈ G(A)ⁱ`,
`x ∈ G(M)^m` and `y ∈ G(T(d))^s`, the trace `G(t)(G(φ)(b ⊗ x) ⊗ y)` is `G(Φ)(b ⊗ xy)` for the
product `xy ∈ G(T(n + d))` and some `Φ` whose underlying morphism is `φ ≫ t`. -/
theorem exists_gradedCounit_map_whiskerRight_comp_unitTwistTrace {A B : C} {M : TwistedKaroubi R C}
    {n d : ℤ} (hM : M = tateTriple R C n) (φ : ofObj (R := R) A ⊗ M ⟶ ofObj (R := R) B)
    (t : B ⟶ 𝟙_ C) (ht : t ∈ grade (R := R) B (𝟙_ C) (-d)) {i m s j : ℤ} (hij : i + m = j)
    (hj : j + s = 0) (b : G.obj (ofObj (R := R) A) i) (x : G.obj M m)
    (y : G.obj (tateTriple R C d) s) :
    ∃ (Φ : ofObj (R := R) A ⊗ tateTriple R C (n + d) ⟶ 𝟙_ (TwistedKaroubi R C))
      (u : A ⊗ 𝟙_ C ⟶ B) (_ : u ≍ φ.val) (_ : Φ.val = u ≫ t)
      (z : G.obj (tateTriple R C (n + d)) (m + s))
      (_ : z ≍ tateMul G n d (n + d) rfl m s (m + s) rfl (hM ▸ x) y),
      G.gradedCounit ((G.map ((φ ▷ tateTriple R C d) ≫ unitTwistTrace d t ht) 0).hom
          (G.gradedMul _ _ j s 0 hj (G.gradedMul _ _ i m j hij b x) y)) =
        G.gradedCounit ((G.map Φ 0).hom (G.gradedMul _ _ i (m + s) 0 (by omega) b z)) := by
  subst hM hij
  let ψ := unitTwistTensorIsoOfEq (R := R) (C := C) n d (n + d) rfl
  refine ⟨(ofObj (R := R) A ◁ ψ.inv) ≫ (α_ _ _ _).inv ≫ (φ ▷ tateTriple R C d) ≫
    unitTwistTrace d t ht, φ.val, HEq.rfl, ?_, _, HEq.rfl, ?_⟩
  · have key : ∀ g : A ⊗ 𝟙_ C ⟶ B,
        (𝟙 A ⊗ₘ (ρ_ (𝟙_ C)).inv) ≫ ((𝟙 A ⊗ₘ (𝟙 (𝟙_ C) ⊗ₘ 𝟙 (𝟙_ C))) ≫ (α_ A (𝟙_ C) (𝟙_ C)).inv) ≫
          (g ⊗ₘ 𝟙 (𝟙_ C)) ≫ (ρ_ B).hom ≫ t = g ≫ t := fun g ↦ by
      rw [MonoidalCategory.id_tensorHom_id, MonoidalCategory.id_tensorHom_id, Category.id_comp,
        MonoidalCategory.id_tensorHom, ← MonoidalCategory.rightUnitor_tensor_inv_assoc,
        MonoidalCategory.tensorHom_id, MonoidalCategory.rightUnitor_naturality_assoc,
        Iso.inv_hom_id_assoc]
    rw [comp_val, comp_val, comp_val, whiskerLeft_val, associator_inv_val, whiskerRight_val,
      unitTwistTrace_val, unitTwistTensorIsoOfEq_inv_val]
    exact key φ.val
  · have e₁ : ∀ w : G.obj (tateTriple R C n ⊗ tateTriple R C d) (m + s),
        (G.map (ofObj (R := R) A ◁ ψ.inv) 0).hom
          (G.gradedMul _ _ i (m + s) 0 (by omega) b ((G.map ψ.hom (m + s)).hom w)) =
        G.gradedMul _ _ i (m + s) 0 (by omega) b w := fun w ↦ by
      rw [Functor.map_whiskerLeft_gradedMul, ← map_comp_apply_hom G, Iso.hom_inv_id, G.map_id]
      rfl
    have e₂ : (G.map (α_ (ofObj (R := R) A) (tateTriple R C n) (tateTriple R C d)).inv 0).hom
        (G.gradedMul _ _ i (m + s) 0 (by omega) b (G.gradedMul _ _ m s (m + s) rfl x y)) =
        G.gradedMul _ _ (i + m) s 0 hj (G.gradedMul _ _ i m (i + m) rfl b x) y := by
      rw [← Functor.map_associator_gradedMul' (G := G) _ _ _ i m s (i + m) (m + s) 0 rfl rfl hj
        (by omega), ← map_comp_apply_hom G, Iso.hom_inv_id, G.map_id]
      rfl
    dsimp only
    rw [tateMul_apply, map_comp_apply_hom G, map_comp_apply_hom G, map_comp_apply_hom G, e₁, e₂,
      G.map_comp]
    rfl

/-- Transport of an identity `(g ≫ m) ≫ t₀ = (g' ≫ m') ≫ t₀'` between morphisms of `C` (with
`U ≅ 𝟙` and `U' = 𝟙` spelled as other objects) to the underlying morphisms of morphisms of triples
`ψ`, `μ` (resp. `ψ'`, `μ'`) with `ψ` defined on `(A, 1, 0) ⊗ T(n)`. -/
theorem comp_comp_val_heq {A B B' U U' : C} {M M' : TwistedKaroubi R C} {n n' : ℤ}
    (hM : M = tateTriple R C n) (hM' : M' = tateTriple R C n') (hU : U = 𝟙_ C) (hU' : U' = 𝟙_ C)
    (ψ : ofObj (R := R) A ⊗ M ⟶ ofObj (R := R) B ⊗ ofObj (R := R) B)
    (μ : ofObj (R := R) B ⊗ ofObj (R := R) B ⟶ ofObj (R := R) B) (t : B ⟶ 𝟙_ C)
    (ψ' : ofObj (R := R) A ⊗ M' ⟶ ofObj (R := R) B' ⊗ ofObj (R := R) B')
    (μ' : ofObj (R := R) B' ⊗ ofObj (R := R) B' ⟶ ofObj (R := R) B') (t' : B' ⟶ 𝟙_ C)
    (g : A ⊗ U ⟶ B ⊗ B) (m : B ⊗ B ⟶ B) (t₀ : B ⟶ U') (g' : A ⊗ U ⟶ B' ⊗ B')
    (m' : B' ⊗ B' ⟶ B') (t₀' : B' ⟶ U') (hψ : ψ.val ≍ g) (hμ : μ.val ≍ m) (ht : t ≍ t₀)
    (hψ' : ψ'.val ≍ g') (hμ' : μ'.val ≍ m') (ht' : t' ≍ t₀')
    (h : (g ≫ m) ≫ t₀ = (g' ≫ m') ≫ t₀') :
    (ψ.val ≫ μ.val) ≫ t ≍ (ψ'.val ≫ μ'.val) ≫ t' := by
  subst hM hM' hU hU'
  rw [eq_of_heq hψ, eq_of_heq hμ, eq_of_heq hψ', eq_of_heq hμ', eq_of_heq ht, eq_of_heq ht']
  exact heq_of_eq h

/-- **A product of morphisms out of twisted units through a multiplication**: for
`f : M ⟶ (A, 1, 0)`, `g : N ⟶ (A, 1, 0)`, `w : P ⟶ (A, 1, 0)` with `M = T(n)`, `N = T(m)`,
`P = T(p)`, `n + m = p`, and `μ : (A, 1, 0) ⊗ (A, 1, 0) ⟶ (A, 1, 0)`, if
`(f ⊗ g) ≫ μ = ρ ≫ w` holds for the underlying morphisms of `C` (read through other spellings
`f₀, g₀, μ₀, ρ₀, w₀` of them), then `(f ⊗ g) ≫ μ = (T(n) ⊗ T(m) ⟶ T(p)) ≫ w`. -/
theorem tensorHom_comp_eq_tateTensorHomOfEq_comp {A U : C} {M N P : TwistedKaroubi R C}
    {n m p : ℤ} (hnmp : n + m = p) (hM : M = tateTriple R C n) (hN : N = tateTriple R C m)
    (hP : P = tateTriple R C p) (hU : U = 𝟙_ C) (f : M ⟶ ofObj (R := R) A)
    (g : N ⟶ ofObj (R := R) A) (μ : ofObj (R := R) A ⊗ ofObj (R := R) A ⟶ ofObj (R := R) A)
    (w : P ⟶ ofObj (R := R) A) (f₀ g₀ w₀ : U ⟶ A) (μ₀ : A ⊗ A ⟶ A) (ρ₀ : U ⊗ U ⟶ U)
    (hf : f.val ≍ f₀) (hg : g.val ≍ g₀) (hμ : μ.val ≍ μ₀) (hw : w.val ≍ w₀)
    (hρ : (ρ_ (𝟙_ C)).hom ≍ ρ₀) (H : (f₀ ⊗ₘ g₀) ≫ μ₀ = ρ₀ ≫ w₀) :
    (f ⊗ₘ g) ≫ μ = tateTensorHomOfEq n m p hnmp hM hN hP ≫ w := by
  subst hM hN hP hU
  rw [tateTensorHomOfEq_rfl]
  apply hom_ext
  rw [comp_val, comp_val, tensorHom_val, tateTensorHom_val, eq_of_heq hf, eq_of_heq hg,
    eq_of_heq hμ, eq_of_heq hw, eq_of_heq hρ]
  exact H

/-- A product of generators, in any spelling of the degrees, is the generator of the sum. -/
theorem tateMul_heq_of_heq (e : ∀ n : ℤ, G.obj (tateTriple R C n) (-2 * n))
    (hemul : ∀ n m : ℤ, tateMul G n m (n + m) rfl (-2 * n) (-2 * m) (-2 * (n + m)) (by ring)
      (e n) (e m) = e (n + m))
    {n d m s : ℤ} (hm : m = -2 * n) (hs : s = -2 * d) (x : G.obj (tateTriple R C n) m)
    (hx : x ≍ e n) (y : G.obj (tateTriple R C d) s) (hy : y ≍ e d) :
    tateMul G n d (n + d) rfl m s (m + s) rfl x y ≍ e (n + d) := by
  refine (tateMul_heq G rfl rfl rfl (show -2 * n + -2 * d = -2 * (n + d) by ring) rfl hm hs
      hx hy).trans ?_
  rw [hemul]

/-- **Comparison of traces of products with generators** (the linear algebra of axiom (C)(b) in
the proof of Stacks 0FH1). Let `φ : (A, 1, 0) ⊗ T(n) ⟶ (B, 1, 0)` and
`φ' : (A, 1, 0) ⊗ T(n') ⟶ (B', 1, 0)`, and let `t : B ⟶ 𝟙`, `t' : B' ⟶ 𝟙` have degrees `-d`,
`-d'` with `n + d = n' + d'`. If `φ ≫ t = φ' ≫ t'` as morphisms of `C`, then for every `b`
the traces `G(t)(G(φ)(b ⊗ eₙ) ⊗ e_d)` and `G(t')(G(φ')(b ⊗ e_{n'}) ⊗ e_{d'})` agree. -/
theorem gradedCounit_map_comp_unitTwistTrace_eq (e : ∀ n : ℤ, G.obj (tateTriple R C n) (-2 * n))
    (hemul : ∀ n m : ℤ, tateMul G n m (n + m) rfl (-2 * n) (-2 * m) (-2 * (n + m)) (by ring)
      (e n) (e m) = e (n + m))
    {A B B' : C} {M M' : TwistedKaroubi R C} {n n' d d' : ℤ} (hM : M = tateTriple R C n)
    (hM' : M' = tateTriple R C n') (hnd : n + d = n' + d')
    (φ : ofObj (R := R) A ⊗ M ⟶ ofObj (R := R) B) (φ' : ofObj (R := R) A ⊗ M' ⟶ ofObj (R := R) B')
    (t : B ⟶ 𝟙_ C) (ht : t ∈ grade (R := R) B (𝟙_ C) (-d)) (t' : B' ⟶ 𝟙_ C)
    (ht' : t' ∈ grade (R := R) B' (𝟙_ C) (-d'))
    (H : φ.val ≫ t ≍ φ'.val ≫ t')
    {i m s j m' s' j' : ℤ} (hij : i + m = j) (hj : j + s = 0) (hij' : i + m' = j')
    (hj' : j' + s' = 0) (hm : m = -2 * n) (hs : s = -2 * d) (hm' : m' = -2 * n')
    (hs' : s' = -2 * d') (b : G.obj (ofObj (R := R) A) i) (x : G.obj M m) (hx : x ≍ e n)
    (y : G.obj (tateTriple R C d) s) (hy : y ≍ e d) (x' : G.obj M' m') (hx' : x' ≍ e n')
    (y' : G.obj (tateTriple R C d') s') (hy' : y' ≍ e d') :
    G.gradedCounit ((G.map ((φ ▷ tateTriple R C d) ≫ unitTwistTrace d t ht) 0).hom
        (G.gradedMul _ _ j s 0 hj (G.gradedMul _ _ i m j hij b x) y)) =
      G.gradedCounit ((G.map ((φ' ▷ tateTriple R C d') ≫ unitTwistTrace d' t' ht') 0).hom
        (G.gradedMul _ _ j' s' 0 hj' (G.gradedMul _ _ i m' j' hij' b x') y')) := by
  obtain ⟨Φ, u, hu, hΦ, z, hz, h₁⟩ :=
    exists_gradedCounit_map_whiskerRight_comp_unitTwistTrace G hM φ t ht hij hj b x y
  obtain ⟨Φ', u', hu', hΦ', z', hz', h₂⟩ :=
    exists_gradedCounit_map_whiskerRight_comp_unitTwistTrace G hM' φ' t' ht' hij' hj' b x' y'
  rw [h₁, h₂]
  have H' : u ≫ t = u' ≫ t' := by
    subst hM hM'
    rw [eq_of_heq hu, eq_of_heq hu']
    exact eq_of_heq H
  refine gradedCounit_map_gradedMul_congr G hnd Φ Φ' (u ≫ t) hΦ (hΦ'.trans H'.symm)
    (by omega) _ _ b z z' ?_
  subst hM hM'
  exact (hz.trans (tateMul_heq_of_heq G e hemul hm hs _ hx y hy)).trans
    ((congr_arg_heq e hnd).trans
      (hz'.trans (tateMul_heq_of_heq G e hemul hm' hs' _ hx' y' hy')).symm)

end CategoryTheory.GradedCategory.TwistedKaroubi

namespace CategoryTheory.Functor

open MonoidalCategory

variable {D : Type*} [Category D] [MonoidalCategory D] {F : Type*} [Field F]
  (G : D ⥤ GradedObject ℤ (ModuleCat F)) [G.Monoidal]

/-- **The trace of a product of images**: `∫ G(u)(b) · G(v)(x) = G(t)(G((u ⊗ v) ≫ μ)(b ⊗ x) ⊗ y)`,
as a single morphism applied to `(b ⊗ x) ⊗ y`. -/
theorem gradedTrace_gradedMonMul_map_map_eq_gradedCounit (M : D) [MonObj M] {N P T : D}
    (t : M ⊗ T ⟶ 𝟙_ D)
    (u : N ⟶ M) (v : P ⟶ M) {i j m s : ℤ} (hij : i + j = m) (hm : m + s = 0)
    (y : G.obj T s) (b : G.obj N i) (x : G.obj P j) :
    G.gradedTrace t y m hm (G.gradedMonMul M i j m hij ((G.map u i).hom b) ((G.map v j).hom x)) =
      G.gradedCounit ((G.map ((((u ⊗ₘ v) ≫ MonObj.mul) ▷ T) ≫ t) 0).hom
        (G.gradedMul _ _ m s 0 hm (G.gradedMul _ _ i j m hij b x) y)) := by
  rw [gradedTrace_apply, gradedMonMul_apply, G.map_comp, GradedObject.categoryOfGradedObjects_comp,
    ModuleCat.comp_apply, map_whiskerRight_gradedMul, G.map_comp,
    GradedObject.categoryOfGradedObjects_comp, ModuleCat.comp_apply, map_tensorHom_gradedMul]

/-- `gradedTrace_gradedMonMul_map_map_eq_gradedCounit` with the first factor not mapped. -/
theorem gradedTrace_gradedMonMul_map_eq_gradedCounit (M : D) [MonObj M] {P T : D} (t : M ⊗ T ⟶ 𝟙_ D)
    (v : P ⟶ M) {i j m s : ℤ} (hij : i + j = m) (hm : m + s = 0)
    (y : G.obj T s) (b : G.obj M i) (x : G.obj P j) :
    G.gradedTrace t y m hm (G.gradedMonMul M i j m hij b ((G.map v j).hom x)) =
      G.gradedCounit ((G.map ((((𝟙 M ⊗ₘ v) ≫ MonObj.mul) ▷ T) ≫ t) 0).hom
        (G.gradedMul _ _ m s 0 hm (G.gradedMul _ _ i j m hij b x) y)) := by
  rw [← gradedTrace_gradedMonMul_map_map_eq_gradedCounit, G.map_id]
  rfl

end CategoryTheory.Functor

namespace Stacks.WeilCohomology

open CorrespondenceCategory ChowMotiveCat SmoothProjectiveScheme

variable {k : Type u} [Field k]

local notation "𝐎" => (GradedCompositionData.Obj.mk :
  CategoryTheory.ObjectProperty.FullSubcategory (SmoothProjectiveScheme _) →
    CorrespondenceCategory _)

/-! ### The cycle of the point -/

local notation "𝟙ₛ" => 𝟙_ (CategoryTheory.ObjectProperty.FullSubcategory (SmoothProjectiveScheme k))

/-- The fundamental class of `Spec k` in `CH^0(Spec k)` is its fundamental class in dimension `0`,
read in codimension `0`. -/
theorem fundamentalClass_tensorUnit_eq_chowGroupToCodimension :
    fundamentalClass 𝟙ₛ =
      chowGroupToCodimension (𝟙ₛ).obj.hom (((0 : ℕ) : ℤ) - 0) 0
        (fundamentalChowClass (fieldChowSituation k) (𝟙ₛ).obj.hom (((0 : ℕ) : ℤ) - 0)) := by
  have hpt := relativeDimension_tensorUnit_hom (k := k)
  funext d
  by_cases hd : d = 0
  · subst hd
    rw [chowGroupToCodimension_apply_of_eq _ _ _ _ _ rfl,
      chowGroupRestrict_fundamentalChowClass _ _ _ _ _ _
        (by simpa using schemeDeltaDimension_le_of_relativeDimension (k := k) _ hpt)]
    exact eq_of_heq ((chowGroupDegreeEquiv_heq _ _ _ _).trans
      ((chowGroupDegreeEquiv_heq _ _ _ _).symm))
  · have := isEmpty_dimPart_of_ne _ hpt hd
    exact (subsingleton_chowGroup_of_isEmpty _ _ _).elim _ _

/-- The correspondence of the cycle `[Spec k]` is the class of the point of `Spec k`. -/
theorem pointCorrHom_tensorUnit_fundamentalClass :
    pointCorrHom 𝟙ₛ 0 (fundamentalClass 𝟙ₛ) =
      homOf ((0 : ℕ) : ℤ) (pointClassCorr (relativeDimension_tensorUnit_hom (k := k)) (𝟙 _)) := by
  have hpt := relativeDimension_tensorUnit_hom (k := k)
  rw [pointCorrHom_apply]
  refine homOf_eq_homOf hpt hpt rfl _ _ ?_
  rw [correspondenceCongr_self]
  simp only [pointCorrEquiv, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]
  unfold pointClassCorr
  have key : ∀ w, corrEquivCorrespondence k (𝟙ₛ).obj.hom (𝟙ₛ).obj.hom hpt hpt 0
      (SmoothProjectiveCorr.toCorr 𝟙ₛ 𝟙ₛ 0 ((SmoothProjectiveCorr.toCorr 𝟙ₛ 𝟙ₛ 0).symm
        ((corrEquivCorrespondence k (𝟙ₛ).obj.hom (𝟙ₛ).obj.hom hpt hpt 0).symm w))) = w :=
    fun w ↦ by simp only [LinearEquiv.apply_symm_apply]
  refine Eq.trans ?_ (key _).symm
  have : CompactSpace (𝟙ₛ).obj.left := QuasiCompact.compactSpace_of_compactSpace (𝟙ₛ).obj.hom
  rw [fundamentalClass_tensorUnit_eq_chowGroupToCodimension,
    show ∀ x, codimensionToCodimChow k (𝟙ₛ).obj.hom 0 x =
      rationalCodimensionToCodimChow k (𝟙ₛ).obj.hom 0 ((1 : ℚ) ⊗ₜ[ℤ] x) from fun x ↦ by
        rw [rationalCodimensionToCodimChow_tmul, one_smul]]
  refine (corrEquivCorrespondence_corrFromPointEquiv_chowGroupToCodimension k _ hpt 0 _
    rfl 1 _).trans (congrArg (fun x ↦ (1 : ℚ) ⊗ₜ[ℤ] x) ?_)
  rw [chowGroupDegreeEquiv_self, ← AddEquiv.eq_symm_apply,
    chowGroupEquivPullbackUnitLeft_symm_apply, chowPushforwardOfIso_mk_coe]
  have := isClosedImmersion_pointSectionEmbedding k (𝟙ₛ).obj.hom (𝟙ₛ).obj.hom
    (InducedCategory.Hom.hom (𝟙 𝟙ₛ)).left (Over.w (InducedCategory.Hom.hom (𝟙 𝟙ₛ)))
  have hc : pointSectionEmbedding k (𝟙ₛ).obj.hom (𝟙ₛ).obj.hom (InducedCategory.Hom.hom (𝟙 𝟙ₛ)).left
      (Over.w (InducedCategory.Hom.hom (𝟙 𝟙ₛ))) ≫
        Limits.pullback.snd (𝟙 (fieldChowSituation k).S) (𝟙ₛ).obj.hom =
        𝟙 _ := Limits.pullback.lift_snd _ _ _
  refine Eq.trans ?_ (congrArg QuotientAddGroup.mk
    (properPushforward_cycleAssociatedToClosedSubscheme_of_isClosedImmersion_comp
      (fieldChowSituation k) _ _ _ _ _ _).symm)
  rw [cycleAssociatedToClosedSubscheme_congr _ _ _ _ hc]
  rfl

/-- **`[Spec k] ∘ a_{[Spec k]} = 1`** in the category of correspondences: the cycle `[Spec k]`
read as a correspondence from `Spec k` to `Spec k`, followed by the fundamental class of
`Spec k`, is the identity. -/
theorem pointCorrHom_tensorUnit_comp_fundamentalClassHom :
    pointCorrHom 𝟙ₛ 0 (fundamentalClass 𝟙ₛ) ≫
        fundamentalClassHom (relativeDimension_tensorUnit_hom (k := k)) = 𝟙 _ := by
  rw [pointCorrHom_tensorUnit_fundamentalClass, fundamentalClassHom, ← DirectSum.lof_eq_of ℚ]
  exact pointClass_comp_fundamentalClass _ _

/-- `[Spec k] ∘ a_{[Spec k]} = 1`, with `Spec k` written `SmoothProjectiveScheme.point k`. -/
theorem pointCorrHom_point_comp_fundamentalClassHom :
    pointCorrHom (point k) 0 (fundamentalClass (point k)) ≫
        fundamentalClassHom (isNonemptyEquidimensional_point (k := k)).relativeDimension = 𝟙 _ :=
  pointCorrHom_tensorUnit_comp_fundamentalClassHom

section Monoidal

attribute [-instance] CorrespondenceCategory.monoidalCategoryStruct

/-- **Stacks 0FH1, proof of (C)(b)**, with the monoidal structure of the category of
correspondences: `(([Γ_f] ⊗ a_α) ≫ μ_X) ≫ [X] = ((1 ⊗ a_{f_*α}) ≫ μ_Y) ≫ [Y]`. -/
theorem graphHom_tensorHom_pointCorrHom_mul_comp_fundamentalClassHom
    {X Y : (SmoothProjectiveScheme k).FullSubcategory} (f : X ⟶ Y) {d e : ℕ}
    (hX : RelativeDimension X.obj.hom d)
    (hY : RelativeDimension Y.obj.hom e) (p : ℤ) (α : codimensionChowGroup k X.obj.hom p) :
    (((graphHom f : 𝐎 Y ⟶ 𝐎 X) ⊗ₘ pointCorrHom X p α) ≫ MonObj.mul (X := 𝐎 X)) ≫
        fundamentalClassHom hX =
      ((𝟙 (𝐎 Y) ⊗ₘ pointCorrHom Y (p + ((e : ℤ) - d))
          (equidimensionalPushforward f d e p (p + ((e : ℤ) - d)) (by ring) α)) ≫
          MonObj.mul (X := 𝐎 Y)) ≫
        fundamentalClassHom hY := by
  have h := tensorHom_graphHom_pointCorrHom_comp_fundamentalClassHom f hX hY p α
  rw [Category.assoc, Category.assoc, mul_eq_diagonalGraphHom,
    mul_eq_diagonalGraphHom]
  generalize (graphHom f : 𝐎 Y ⟶ 𝐎 X) = Γ at h ⊢
  generalize pointCorrHom X p α = a at h ⊢
  generalize pointCorrHom Y (p + ((e : ℤ) - d))
    (equidimensionalPushforward f d e p (p + ((e : ℤ) - d)) (by ring) α) = a' at h ⊢
  generalize diagonalGraphHom X = ηX at h ⊢
  generalize diagonalGraphHom Y = ηY at h ⊢
  generalize fundamentalClassHom hX = tX at h ⊢
  generalize fundamentalClassHom hY = tY at h ⊢
  exact h

end Monoidal

namespace ChowMotiveCat

open CategoryTheory.GradedCategory

attribute [-instance] ChowMotiveCat.monoidalCategory ChowMotiveCat.braidedCategory
  ChowMotiveCat.symmetricCategory TwistedKaroubi.monoidalCategoryStruct
  CorrespondenceCategory.monoidalCategoryStruct TwistedKaroubi.symmetricCategory

section Realization

/-- Transport of an element along an equality of degrees is heterogeneously the identity. -/
theorem eqToHom_apply_heq {F : Type w} [Field F] (V : ℤ → ModuleCat.{w} F) {i j : ℤ} (h : i = j)
    (x : V i) : (eqToHom (congrArg V h)).hom x ≍ x := by
  subst h
  rfl

variable {F : Type w} [Field F]
  (G : TwistedKaroubi ℚ (canonicalCorrespondenceCompositionData k).Obj ⥤
    GradedObject ℤ (ModuleCat.{w} F)) [G.Monoidal] [G.Additive]
  (e : ∀ n : ℤ, (G.obj (tate k n)) (-2 * n))

/-- **Axiom (C)(d)** (Stacks 0FH1): `∫_{Spec k} γ([Spec k]) = 1`. -/
theorem gradedTrace_cycleClassMotive_point (he0 : e 0 ≍ TwistedKaroubi.tateOne G)
    (hemul : ∀ n m : ℤ, TwistedKaroubi.tateMul G n m (n + m) rfl (-2 * n) (-2 * m) (-2 * (n + m))
      (by ring) (e n) (e m) = e (n + m)) :
    G.gradedTrace (fundamentalClassMot (isNonemptyEquidimensional_point (k := k)).relativeDimension)
        (e ((0 : ℕ) : ℤ)) (2 * ((0 : ℕ) : ℤ)) (by ring)
        (cycleClassMotive G e (point k) 0 (fundamentalClass (point k))) = 1 := by
  rw [cycleClassMotive_apply]
  refine TwistedKaroubi.gradedTrace_unitTwistTrace_map_eq_one G e he0 hemul (A := 𝐎 (point k))
    (M := tate k (-0)) (n := -0) (d := ((0 : ℕ) : ℤ)) rfl
    (show -0 + ((0 : ℕ) : ℤ) = 0 by simp) (pointMotiveHom (point k) 0 (fundamentalClass (point k)))
    (fundamentalClassHom (isNonemptyEquidimensional_point (k := k)).relativeDimension)
    (fundamentalClassHom_mem_grade _) ?_ (m := 2 * 0) (s := -2 * ((0 : ℕ) : ℤ))
    (by simp) (by simp) rfl (tateGenNeg G e 0) (eqToHom_apply_heq _ (by ring) _) _ HEq.rfl
  intro g hg
  exact comp_eq_of_heq pointCorrHom_point_comp_fundamentalClassHom
    (A := 𝟙_ (canonicalCorrespondenceCompositionData k).Obj) (B := 𝐎 (point k))
    (C := 𝟙_ (canonicalCorrespondenceCompositionData k).Obj) rfl rfl rfl
    (x := g) (y := fundamentalClassHom (isNonemptyEquidimensional_point (k := k)).relativeDimension)
    (z := 𝟙 (𝟙_ (canonicalCorrespondenceCompositionData k).Obj)) (hg.trans HEq.rfl) HEq.rfl HEq.rfl

/-- **Axiom (C)(b)** (Stacks 0FH1): for `f : X ⟶ Y` of nonempty equidimensional smooth
projective schemes of dimensions `d` and `e'`, `α ∈ CH^p(X)` and `b ∈ H^i(Y)` of complementary
degree, `∫_X f^*b ∪ γ(α) = ∫_Y b ∪ γ(f_*α)`. -/
theorem gradedTrace_gradedMonMul_cycleClassMotive_pushforward
    (hemul : ∀ n m : ℤ, TwistedKaroubi.tateMul G n m (n + m) rfl (-2 * n) (-2 * m) (-2 * (n + m))
      (by ring) (e n) (e m) = e (n + m))
    {X Y : (SmoothProjectiveScheme k).FullSubcategory} (f : X ⟶ Y) (d e' : ℕ)
    (hX : IsNonemptyEquidimensional X d) (hY : IsNonemptyEquidimensional Y e') (p q : ℤ)
    (hpq : q = p + e' - d) (α : codimensionChowGroup k X.obj.hom p) (i : ℤ)
    (hi : i + 2 * p = 2 * d) (hi' : i + 2 * q = 2 * e')
    (b : G.obj (TwistedKaroubi.ofObj (R := ℚ) (𝐎 Y)) i) :
    G.gradedTrace (fundamentalClassMot hX.relativeDimension) (e d) (2 * d) (by ring)
        (Functor.gradedMonMul G (TwistedKaroubi.ofObj (R := ℚ) (𝐎 X)) i (2 * p) (2 * d) hi
          ((G.map (motMap f) i).hom b) (cycleClassMotive G e X p α)) =
      G.gradedTrace (fundamentalClassMot hY.relativeDimension) (e e') (2 * e') (by ring)
        (Functor.gradedMonMul G (TwistedKaroubi.ofObj (R := ℚ) (𝐎 Y)) i (2 * q) (2 * e') hi' b
          (cycleClassMotive G e Y q (equidimensionalPushforward f d e' p q hpq α))) := by
  obtain rfl : q = p + ((e' : ℤ) - d) := by omega
  rw [cycleClassMotive_apply, cycleClassMotive_apply]
  refine (Functor.gradedTrace_gradedMonMul_map_map_eq_gradedCounit G _ _ _ _ _ _ _ _ _).trans
    (Eq.trans ?_ (Functor.gradedTrace_gradedMonMul_map_eq_gradedCounit G _ _ _ _ _ _ _ _).symm)
  refine TwistedKaroubi.gradedCounit_map_comp_unitTwistTrace_eq G e hemul (A := 𝐎 Y) (B := 𝐎 X)
    (B' := 𝐎 Y) (M := tate k (-p)) (M' := tate k (-(p + ((e' : ℤ) - d)))) (n := -p)
    (n' := -(p + ((e' : ℤ) - d))) (d := d) (d' := e') rfl rfl (by ring) _ _
    (fundamentalClassHom hX.relativeDimension) (fundamentalClassHom_mem_grade _)
    (fundamentalClassHom hY.relativeDimension) (fundamentalClassHom_mem_grade _) ?_ _ _ _ _
    (by ring) rfl (by ring) rfl b _ (eqToHom_apply_heq _ (by ring) _) _ HEq.rfl _
    (eqToHom_apply_heq _ (by ring) _) _ HEq.rfl
  have h := graphHom_tensorHom_pointCorrHom_mul_comp_fundamentalClassHom f hX.relativeDimension
    hY.relativeDimension p α
  rw [TwistedKaroubi.comp_val, TwistedKaroubi.comp_val]
  refine TwistedKaroubi.comp_comp_val_heq (A := 𝐎 Y) (B := 𝐎 X) (B' := 𝐎 Y)
    (U := 𝐎 (𝟙_ ((SmoothProjectiveScheme k).FullSubcategory)))
    (U' := CorrespondenceCategory.tensorUnit)
    (M := tate k (-p)) (M' := tate k (-(p + ((e' : ℤ) - d)))) (n := -p)
    (n' := -(p + ((e' : ℤ) - d))) rfl rfl rfl rfl
    (motMap f ⊗ₘ pointMotiveHom X p α) MonObj.mul (fundamentalClassHom hX.relativeDimension)
    (𝟙 _ ⊗ₘ pointMotiveHom Y (p + ((e' : ℤ) - d))
      (equidimensionalPushforward f d e' p (p + ((e' : ℤ) - d)) hpq α)) MonObj.mul
    (fundamentalClassHom hY.relativeDimension)
    ((graphHom f : 𝐎 Y ⟶ 𝐎 X) ⊗ₘ pointCorrHom X p α) (MonObj.mul (X := 𝐎 X))
    (fundamentalClassHom hX.relativeDimension)
    (𝟙 (𝐎 Y) ⊗ₘ pointCorrHom Y (p + ((e' : ℤ) - d))
      (equidimensionalPushforward f d e' p (p + ((e' : ℤ) - d)) hpq α)) (MonObj.mul (X := 𝐎 Y))
    (fundamentalClassHom hY.relativeDimension)
    HEq.rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl ?_
  generalize (graphHom f : 𝐎 Y ⟶ 𝐎 X) = Γ at h ⊢
  generalize pointCorrHom X p α = a at h ⊢
  generalize pointCorrHom Y (p + ((e' : ℤ) - d))
    (equidimensionalPushforward f d e' p (p + ((e' : ℤ) - d)) hpq α) = a' at h ⊢
  generalize MonObj.mul (X := 𝐎 X) = μX at h ⊢
  generalize MonObj.mul (X := 𝐎 Y) = μY at h ⊢
  generalize fundamentalClassHom hX.relativeDimension = tX at h ⊢
  generalize fundamentalClassHom hY.relativeDimension = tY at h ⊢
  exact h

end Realization

end ChowMotiveCat

end Stacks.WeilCohomology

end
