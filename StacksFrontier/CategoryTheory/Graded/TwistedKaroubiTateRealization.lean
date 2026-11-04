module

public import Mathlib.Algebra.GradedMonoid
public import StacksFrontier.CategoryTheory.Graded.TwistedKaroubiTateCoherence
public import StacksFrontier.CategoryTheory.GradedObject.InvertibleGradedVectorSpace
public import StacksFrontier.CategoryTheory.GradedObject.MonoidalFunctorElements
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Monoidal functors from twisted Karoubi envelopes to graded vector spaces on twisted units

Let `C` be a category graded over a ring `R` with a graded monoidal structure, and let
`G : TwistedKaroubi R C ⥤ GradedObject ℤ (ModuleCat F)` be a monoidal functor to `ℤ`-graded
vector spaces over a field `F`. Suppose that `G(T(1))` is concentrated in a single degree `d`,
where `T(n) = (𝟙_ C, 𝟙, n)` are the twisted units. Then (Stacks 0FH1, second paragraph of the
proof, where `d = -2` and `T(n)` is the Tate motive `𝟏(n)`):

* each `G(T(n))` is one dimensional and concentrated in degree `d n`;
* a nonzero `e₁ ∈ G(T(1))ᵈ` extends to nonzero `eₙ ∈ G(T(n))^{dn}` for all `n : ℤ`, with `e₀`
  the unit of `G` and `eₙ eₘ = e_{n+m}` for the product given by the tensorator of `G` and
  `T(n) ⊗ T(m) ≅ T(n + m)`. Equivalently, the `eₙ` are isomorphisms `F[-dn] → G(T(n))`
  compatible with tensor products.

## Main definitions

* `CategoryTheory.GradedCategory.TwistedKaroubi.tateMul`: the product
  `G(T(n))ⁱ × G(T(m))ʲ → G(T(p))ᵏ` for `n + m = p`, `i + j = k`.
* `CategoryTheory.GradedCategory.TwistedKaroubi.tateLine`: the line `G(T(n))^{dn}`, a graded
  monoid under `tateMul`.
* `CategoryTheory.GradedCategory.TwistedKaroubi.tateGen`: the generators `eₙ`.

## Main results

* `CategoryTheory.GradedCategory.TwistedKaroubi.finrank_tateTriple_apply` and
  `CategoryTheory.GradedCategory.TwistedKaroubi.isZero_tateTriple_apply`: `G(T(n))` is one
  dimensional, concentrated in degree `d n`.
* `CategoryTheory.GradedCategory.TwistedKaroubi.tateGen_ne_zero`, `tateGen_one`, `tateGen_zero`,
  `tateMul_tateGen`: the properties of the generators.

## Implementation notes

The lines `G(T(n))^{dn}` form a `GradedMonoid.GMonoid` over `ℤ`; its associativity and unit laws
come from the coherence of `T(n) ⊗ T(m) ≅ T(n + m)`
(`CategoryTheory.GradedCategory.TwistedKaroubi.unitTwistTensorIsoOfEq_assoc`) and of `G`. In the
resulting monoid `⟨1, e₁⟩` is a unit, because multiplication by a nonzero element is a bijection
between lines, and `eₙ` is the component of its `n`-th power. All products are first stated
into a flexible target twist and degree (`tateMul`), so that every law is an equation in one
type; heterogeneous equalities only appear when comparing such targets (`tateMul_heq`).

## References

* [Stacks Project, Tag 0FH1](https://stacks.math.columbia.edu/tag/0FH1)
-/

@[expose] public section

open CategoryTheory MonoidalCategory Category Limits GradedObject GradedObject.Monoidal
open scoped TensorProduct

namespace CategoryTheory.GradedCategory.TwistedKaroubi

universe w v u uF

variable {R : Type w} [Ring R] {C : Type u} [Category.{v} C] [Preadditive C] [GradedCategory R C]
  [MonoidalCategory C] [IsGradedMonoidal R C] {F : Type uF} [Field F]
  (G : TwistedKaroubi R C ⥤ GradedObject ℤ (ModuleCat.{uF} F))

/-! ### The product on the images of the twisted units -/

section Mul

variable [G.LaxMonoidal]

/-- The product `G(T(n))ⁱ × G(T(m))ʲ → G(T(p))ᵏ`, for `n + m = p` and `i + j = k`: the
tensorator of `G` followed by `G` of `T(n) ⊗ T(m) ≅ T(p)`. -/
noncomputable def tateMul (n m p : ℤ) (hp : n + m = p) (i j k : ℤ) (hk : i + j = k) :
    G.obj (tateTriple R C n) i →ₗ[F] G.obj (tateTriple R C m) j →ₗ[F]
      G.obj (tateTriple R C p) k :=
  (G.gradedMul (tateTriple R C n) (tateTriple R C m) i j k hk).compr₂
    (G.map (unitTwistTensorIsoOfEq n m p hp).hom k).hom

/-- `tateMul` sends `x ⊗ y` through the tensorator of `G` and then through `G` of
`T(n) ⊗ T(m) ≅ T(p)`. -/
lemma tateMul_apply (n m p : ℤ) (hp : n + m = p) (i j k : ℤ) (hk : i + j = k)
    (x : G.obj (tateTriple R C n) i) (y : G.obj (tateTriple R C m) j) :
    tateMul G n m p hp i j k hk x y =
      G.map (unitTwistTensorIsoOfEq n m p hp).hom k
        (G.gradedMul (tateTriple R C n) (tateTriple R C m) i j k hk x y) :=
  rfl

/-- The product does not depend on how the twists and degrees are written. -/
lemma tateMul_heq {n m p p' i i' j j' k k' : ℤ} (hp : n + m = p) (hp' : n + m = p')
    (hk : i + j = k) (hk' : i' + j' = k') (hpp : p = p') (hii : i = i') (hjj : j = j')
    {x : G.obj (tateTriple R C n) i} {x' : G.obj (tateTriple R C n) i'} (hx : x ≍ x')
    {y : G.obj (tateTriple R C m) j} {y' : G.obj (tateTriple R C m) j'} (hy : y ≍ y') :
    tateMul G n m p hp i j k hk x y ≍ tateMul G n m p' hp' i' j' k' hk' x' y' := by
  subst hpp hii hjj hk hk'
  obtain rfl := eq_of_heq hx
  obtain rfl := eq_of_heq hy
  rfl

omit [MonoidalCategory C] [IsGradedMonoidal R C] [G.LaxMonoidal] in
private lemma map_comp_apply {X Y Z : TwistedKaroubi R C} (f : X ⟶ Y) (g : Y ⟶ Z) (k : ℤ)
    (x : G.obj X k) : G.map (f ≫ g) k x = G.map g k (G.map f k x) := by
  rw [G.map_comp]
  rfl

/-- **Associativity of the product.** -/
lemma tateMul_assoc (n m l p : ℤ) (hp : n + m + l = p) (i j l' k : ℤ) (hk : i + j + l' = k)
    (x : G.obj (tateTriple R C n) i) (y : G.obj (tateTriple R C m) j)
    (z : G.obj (tateTriple R C l) l') :
    tateMul G (n + m) l p hp (i + j) l' k hk (tateMul G n m (n + m) rfl i j (i + j) rfl x y) z =
      tateMul G n (m + l) p (by rw [← hp, add_assoc]) i (j + l') k (by rw [← hk, add_assoc]) x
        (tateMul G m l (m + l) rfl j l' (j + l') rfl y z) := by
  simp only [tateMul_apply]
  rw [← Functor.map_whiskerRight_gradedMul, ← map_comp_apply, unitTwistTensorIsoOfEq_assoc,
    map_comp_apply, map_comp_apply, Functor.map_associator_gradedMul,
    Functor.map_whiskerLeft_gradedMul]

/-- The unit `1 ∈ G(T(0))⁰` of `G`, through `T(0) = 𝟙`. -/
noncomputable def tateOne : G.obj (tateTriple R C 0) 0 :=
  G.gradedOne

/-- **Left unitality of the product.** -/
lemma tateMul_one_left (n i : ℤ) (x : G.obj (tateTriple R C n) i) :
    tateMul G 0 n n (zero_add n) 0 i i (zero_add i) (tateOne G) x = x := by
  rw [tateMul_apply, unitTwistTensorIsoOfEq_leftUnitor]
  exact Functor.map_leftUnitor_gradedMul _ _ x

/-- **Right unitality of the product.** -/
lemma tateMul_one_right (n i : ℤ) (x : G.obj (tateTriple R C n) i) :
    tateMul G n 0 n (add_zero n) i 0 i (add_zero i) x (tateOne G) = x := by
  rw [tateMul_apply, unitTwistTensorIsoOfEq_rightUnitor]
  exact Functor.map_rightUnitor_gradedMul _ _ x

end Mul

/-! ### The images of the twisted units are lines -/

section Degree

variable [G.Monoidal]

/-- `G(T(n))` is one dimensional and concentrated in a single degree, because `T(n)` is
invertible. -/
lemma exists_finrank_tateTriple_eq_one (n : ℤ) :
    ∃ a : ℤ, Module.finrank F (G.obj (tateTriple R C n) a) = 1 ∧
      ∀ i, i ≠ a → IsZero (G.obj (tateTriple R C n) i) :=
  exists_finrank_eq_one_of_tensorObj_iso_tensorUnit _ (G.obj (tateTriple R C (-n)))
    (Functor.Monoidal.μIso G _ _ ≪≫
      G.mapIso (unitTwistHasInverse n (-n) (add_neg_cancel n)).isoLeft ≪≫
        (Functor.Monoidal.εIso G).symm)

omit [IsGradedMonoidal R C] in
private lemma not_isZero_of_finrank_eq_one {V : GradedObject ℤ (ModuleCat.{uF} F)} {a : ℤ}
    (h : Module.finrank F (V a) = 1) : ¬ IsZero (V a) := by
  rw [ModuleCat.isZero_iff_subsingleton]
  intro hs
  rw [Module.finrank_zero_of_subsingleton] at h
  exact zero_ne_one h

omit [IsGradedMonoidal R C] in
private lemma eq_of_finrank_eq_one {V : GradedObject ℤ (ModuleCat.{uF} F)} {a b : ℤ}
    (ha : Module.finrank F (V a) = 1) (hb : ∀ i, i ≠ b → IsZero (V i)) : a = b := by
  by_contra h
  exact not_isZero_of_finrank_eq_one ha (hb a h)

omit [IsGradedMonoidal R C] in
private lemma not_isZero_tensorObj (V W : GradedObject ℤ (ModuleCat.{uF} F)) {a b : ℤ}
    (ha : Module.finrank F (V a) = 1) (hb : Module.finrank F (W b) = 1) :
    ¬ IsZero ((V ⊗ W) (a + b)) := by
  have := Module.finite_of_finrank_eq_succ ha
  have := Module.finite_of_finrank_eq_succ hb
  have h₁ : Module.finrank F (V a ⊗[F] W b) = 1 := by
    rw [Module.finrank_tensorProduct, ha, hb]
  have : Nontrivial (V a ⊗[F] W b) := Module.nontrivial_of_finrank_eq_succ h₁
  have := (ιTensorObj_injective V W a b (a + b) rfl).nontrivial
  rw [ModuleCat.isZero_iff_subsingleton, ← not_nontrivial_iff_subsingleton, not_not]
  assumption

/-- Degrees add: if `G(T(n))` lives in degree `a` and `G(T(m))` in degree `b`, then `G(T(n + m))`
lives in degree `a + b`. -/
private lemma finrank_tateTriple_add {n m a b : ℤ}
    (ha : Module.finrank F (G.obj (tateTriple R C n) a) = 1)
    (hb : Module.finrank F (G.obj (tateTriple R C m) b) = 1) :
    Module.finrank F (G.obj (tateTriple R C (n + m)) (a + b)) = 1 ∧
      ∀ i, i ≠ a + b → IsZero (G.obj (tateTriple R C (n + m)) i) := by
  obtain ⟨c, hc₁, hc₂⟩ := exists_finrank_tateTriple_eq_one G (n + m)
  have e : G.obj (tateTriple R C n) ⊗ G.obj (tateTriple R C m) ≅ G.obj (tateTriple R C (n + m)) :=
    Functor.Monoidal.μIso G _ _ ≪≫ G.mapIso (unitTwistTensorIso n m)
  have hne : ¬ IsZero (G.obj (tateTriple R C (n + m)) (a + b)) := fun h =>
    not_isZero_tensorObj _ _ ha hb (h.of_iso ((GradedObject.eval (a + b)).mapIso e))
  obtain rfl : a + b = c := by
    by_contra h
    exact hne (hc₂ _ h)
  exact ⟨hc₁, hc₂⟩

variable {G} {d : ℤ} (hG : ∀ i, i ≠ d → IsZero ((G.obj (tateTriple R C 1)) i))
include hG

/-- **Stacks 0FH1, the degrees of the Tate twists.** If `G(T(1))` is concentrated in degree `d`,
then `G(T(n))` is one dimensional in degree `d n` and zero in the other degrees. -/
theorem finrank_tateTriple_apply_and_isZero (n : ℤ) :
    Module.finrank F (G.obj (tateTriple R C n) (d * n)) = 1 ∧
      ∀ i, i ≠ d * n → IsZero (G.obj (tateTriple R C n) i) := by
  have h₁ : Module.finrank F (G.obj (tateTriple R C 1) (d * 1)) = 1 := by
    obtain ⟨a, ha₁, -⟩ := exists_finrank_tateTriple_eq_one G 1
    obtain rfl := eq_of_finrank_eq_one ha₁ hG
    rwa [mul_one]
  refine Int.induction_on n ?_ (fun n ih => ?_) (fun n ih => ?_)
  · obtain ⟨a, ha₁, ha₂⟩ := exists_finrank_tateTriple_eq_one G 0
    have h := (finrank_tateTriple_add G ha₁ ha₁).1
    rw [add_zero] at h
    obtain rfl : a = 0 := by linarith [eq_of_finrank_eq_one h ha₂]
    rw [mul_zero]
    exact ⟨ha₁, ha₂⟩
  · have h := finrank_tateTriple_add G ih.1 h₁
    rwa [show d * n + d * 1 = d * (n + 1) by ring] at h
  · obtain ⟨a, ha₁, ha₂⟩ := exists_finrank_tateTriple_eq_one G (-n - 1)
    have h := (finrank_tateTriple_add G ha₁ h₁).1
    rw [show -(n : ℤ) - 1 + 1 = -n by ring] at h
    obtain rfl : a = d * (-n - 1) := by linarith [eq_of_finrank_eq_one h ih.2]
    exact ⟨ha₁, ha₂⟩

/-- If `G(T(1))` is concentrated in degree `d`, then `G(T(n))` is one-dimensional in degree
`d n`. -/
theorem finrank_tateTriple_apply (n : ℤ) :
    Module.finrank F (G.obj (tateTriple R C n) (d * n)) = 1 :=
  (finrank_tateTriple_apply_and_isZero hG n).1

/-- If `G(T(1))` is concentrated in degree `d`, then `G(T(n))` vanishes in every degree other
than `d n`. -/
theorem isZero_tateTriple_apply (n i : ℤ) (hi : i ≠ d * n) :
    IsZero (G.obj (tateTriple R C n) i) :=
  (finrank_tateTriple_apply_and_isZero hG n).2 i hi

end Degree

/-! ### The lines `G(T(n))^{dn}` form a graded monoid -/

section Line

variable [G.LaxMonoidal] (d : ℤ)

/-- The line `G(T(n))^{dn}`. -/
abbrev tateLine (n : ℤ) : Type uF :=
  G.obj (tateTriple R C n) (d * n)

/-- The unit of `G` as an element of the line `G(T(0))^{d·0}`. -/
noncomputable def tateLineOne : tateLine G d 0 :=
  cast (congrArg (fun j : ℤ => (G.obj (tateTriple R C 0) j : Type uF)) (mul_zero d).symm)
    (tateOne G)

/-- `tateLineOne` is the unit `tateOne` of `G`, up to the identification `d * 0 = 0`. -/
lemma tateLineOne_heq : tateLineOne G d ≍ tateOne G :=
  cast_heq _ _

/-- Associativity of the product of lines. -/
lemma tateMul_assoc_heq (n m l : ℤ) (x : tateLine G d n) (y : tateLine G d m)
    (z : tateLine G d l) :
    tateMul G (n + m) l (n + m + l) rfl (d * (n + m)) (d * l) (d * (n + m + l)) (by ring)
        (tateMul G n m (n + m) rfl (d * n) (d * m) (d * (n + m)) (by ring) x y) z ≍
      tateMul G n (m + l) (n + (m + l)) rfl (d * n) (d * (m + l)) (d * (n + (m + l))) (by ring) x
        (tateMul G m l (m + l) rfl (d * m) (d * l) (d * (m + l)) (by ring) y z) := by
  refine (tateMul_heq G rfl rfl (by ring) (show d * n + d * m + d * l = d * (n + m + l) by ring)
    rfl (mul_add d n m) rfl (tateMul_heq G rfl rfl (by ring) rfl rfl rfl rfl HEq.rfl HEq.rfl)
    HEq.rfl).trans ?_
  rw [tateMul_assoc]
  exact tateMul_heq G _ rfl _ (by ring) (add_assoc n m l) rfl (mul_add d m l).symm HEq.rfl
    (tateMul_heq G rfl rfl rfl (by ring) rfl rfl rfl HEq.rfl HEq.rfl)

/-- The product of lines. -/
noncomputable instance : GradedMonoid.GMul (tateLine G d) where
  mul {n m} x y := tateMul G n m (n + m) rfl (d * n) (d * m) (d * (n + m)) (by ring) x y

/-- The unit of the lines. -/
noncomputable instance : GradedMonoid.GOne (tateLine G d) where
  one := tateLineOne G d

/-- The lines `G(T(n))^{dn}` form a graded monoid under the product of `G`. -/
noncomputable instance : GradedMonoid.GMonoid (tateLine G d) :=
  { (inferInstance : GradedMonoid.GMul (tateLine G d)),
    (inferInstance : GradedMonoid.GOne (tateLine G d)) with
    one_mul := by
      rintro ⟨n, x⟩
      refine Sigma.ext (zero_add n) ?_
      exact (tateMul_heq G _ (zero_add n) _ (zero_add (d * n)) (zero_add n) (mul_zero d) rfl
        (tateLineOne_heq G d) HEq.rfl).trans (heq_of_eq (tateMul_one_left G n (d * n) x))
    mul_one := by
      rintro ⟨n, x⟩
      refine Sigma.ext (add_zero n) ?_
      exact (tateMul_heq G _ (add_zero n) _ (add_zero (d * n)) (add_zero n) rfl (mul_zero d)
        HEq.rfl (tateLineOne_heq G d)).trans (heq_of_eq (tateMul_one_right G n (d * n) x))
    mul_assoc := by
      rintro ⟨n, x⟩ ⟨m, y⟩ ⟨l, z⟩
      exact Sigma.ext (add_assoc n m l) (tateMul_assoc_heq G d n m l x y z) }

/-- The product of `⟨n, x⟩` and `⟨m, y⟩` in the graded monoid of lines is
`⟨n + m, tateMul x y⟩`. -/
lemma tateLine_mk_mul_mk {n m : ℤ} (x : tateLine G d n) (y : tateLine G d m) :
    GradedMonoid.mk n x * GradedMonoid.mk m y = GradedMonoid.mk (n + m)
      (tateMul G n m (n + m) rfl (d * n) (d * m) (d * (n + m)) (by ring) x y) :=
  rfl

/-- The unit of the graded monoid of lines is `⟨0, tateLineOne⟩`. -/
lemma tateLine_one : (1 : GradedMonoid (tateLine G d)) = GradedMonoid.mk 0 (tateLineOne G d) :=
  rfl

end Line

/-! ### The generators -/

section Generators

omit [IsGradedMonoidal R C] in
private lemma eq_zero_of_tmul_eq_zero_left {V W : Type*} [AddCommGroup V] [Module F V]
    [AddCommGroup W] [Module F W] {x : V} (hx : x ≠ 0) {y : W} (h : x ⊗ₜ[F] y = 0) : y = 0 := by
  obtain ⟨φ, hφ⟩ := Module.Projective.exists_dual_eq_one F hx
  simpa [hφ] using congrArg ((TensorProduct.lid F W).toLinearMap ∘ₗ φ.rTensor W) h

omit [IsGradedMonoidal R C] in
private lemma eq_zero_of_tmul_eq_zero_right {V W : Type*} [AddCommGroup V] [Module F V]
    [AddCommGroup W] [Module F W] {x : V} {y : W} (hy : y ≠ 0) (h : x ⊗ₜ[F] y = 0) : x = 0 :=
  eq_zero_of_tmul_eq_zero_left hy (by simpa using congrArg (TensorProduct.comm F V W) h)

omit [IsGradedMonoidal R C] in
private lemma iso_apply_injective {X Y : GradedObject ℤ (ModuleCat.{uF} F)} (e : X ≅ Y) (k : ℤ) :
    Function.Injective (e.hom k) := fun a b h => by
  have ha := ConcreteCategory.congr_hom (CategoryTheory.Iso.hom_inv_id_eval e k) a
  have hb := ConcreteCategory.congr_hom (CategoryTheory.Iso.hom_inv_id_eval e k) b
  simp only [ConcreteCategory.comp_apply, ModuleCat.id_apply] at ha hb
  rw [← ha, ← hb, h]

variable [G.Monoidal]

private lemma tmul_eq_zero_of_tateMul_eq_zero {n m p : ℤ} (hp : n + m = p) {i j k : ℤ}
    (hk : i + j = k) {x : G.obj (tateTriple R C n) i} {y : G.obj (tateTriple R C m) j}
    (h : tateMul G n m p hp i j k hk x y = 0) : x ⊗ₜ[F] y = 0 := by
  rw [tateMul_apply, Functor.gradedMul_apply] at h
  have h₁ := iso_apply_injective (G.mapIso (unitTwistTensorIsoOfEq n m p hp)) k
    (h.trans (map_zero _).symm)
  rw [ConcreteCategory.comp_apply] at h₁
  have h₂ := iso_apply_injective (Functor.Monoidal.μIso G _ _) k (h₁.trans (map_zero _).symm)
  exact ιTensorObj_injective _ _ i j k hk (h₂.trans (map_zero _).symm)

/-- Multiplication by a nonzero element is injective. -/
lemma tateMul_injective {n m p : ℤ} (hp : n + m = p) {i j k : ℤ} (hk : i + j = k)
    {x : G.obj (tateTriple R C n) i} (hx : x ≠ 0) :
    Function.Injective (tateMul G n m p hp i j k hk x) :=
  (injective_iff_map_eq_zero _).2 fun _ hy =>
    eq_zero_of_tmul_eq_zero_left hx (tmul_eq_zero_of_tateMul_eq_zero G hp hk hy)

/-- Multiplication by a nonzero element on the right is injective. -/
lemma tateMul_flip_injective {n m p : ℤ} (hp : n + m = p) {i j k : ℤ} (hk : i + j = k)
    {y : G.obj (tateTriple R C m) j} (hy : y ≠ 0) :
    Function.Injective ((tateMul G n m p hp i j k hk).flip y) :=
  (injective_iff_map_eq_zero _).2 fun _ hx =>
    eq_zero_of_tmul_eq_zero_right hy (tmul_eq_zero_of_tateMul_eq_zero G hp hk hx)

variable {G} {d : ℤ} (hG : ∀ i, i ≠ d → IsZero ((G.obj (tateTriple R C 1)) i))
  {e₁ : tateLine G d 1} (he₁ : e₁ ≠ 0)

include hG in
/-- If `G(T(1))` is concentrated in degree `d`, each line `G(T(n))^{dn}` is finite dimensional. -/
lemma finiteDimensional_tateLine (n : ℤ) : FiniteDimensional F (tateLine G d n) :=
  Module.finite_of_finrank_eq_succ (finrank_tateTriple_apply hG n)

/-- An injective linear map between one-dimensional lines hits the unit of the lines in degree
`0`. -/
private lemma exists_apply_eq_tateLineOne {a b : ℤ} (hb : 0 = b)
    (φ : tateLine G d a →ₗ[F] tateLine G d b) (hφ : Function.Injective φ)
    (ha : Module.finrank F (tateLine G d a) = 1) (hb₁ : Module.finrank F (tateLine G d b) = 1) :
    ∃ z, φ z = cast (congrArg (tateLine G d) hb) (tateLineOne G d) := by
  have := Module.finite_of_finrank_eq_succ ha
  have := Module.finite_of_finrank_eq_succ hb₁
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (ha.trans hb₁.symm)).1 hφ _

/-- An element of a line in degree `0` equal to the unit of the lines represents `1`. -/
private lemma mk_eq_one_of_eq_cast {a : ℤ} (ha : 0 = a) {z : tateLine G d a}
    (h : z = cast (congrArg (tateLine G d) ha) (tateLineOne G d)) :
    GradedMonoid.mk a z = 1 :=
  Sigma.ext ha.symm ((heq_of_eq h).trans (cast_heq _ _))

include hG he₁ in
/-- A nonzero `e₁ ∈ G(T(1))ᵈ` has a right inverse `f ∈ G(T(-1))^{-d}` in the graded monoid of
lines. -/
lemma exists_tateLine_mul_eq_one :
    ∃ f : tateLine G d (-1), GradedMonoid.mk 1 e₁ * GradedMonoid.mk (-1) f = 1 := by
  obtain ⟨f, hf⟩ := exists_apply_eq_tateLineOne (by norm_num : (0 : ℤ) = 1 + -1)
    (tateMul G 1 (-1) (1 + -1) rfl (d * 1) (d * (-1)) (d * (1 + -1)) (by ring) e₁)
    (tateMul_injective G _ _ he₁)
    (finrank_tateTriple_apply hG (-1)) (finrank_tateTriple_apply hG (1 + -1))
  exact ⟨f, (tateLine_mk_mul_mk G d _ _).trans (mk_eq_one_of_eq_cast (by norm_num) hf)⟩

include hG he₁ in
/-- A nonzero `e₁ ∈ G(T(1))ᵈ` has a left inverse `g ∈ G(T(-1))^{-d}` in the graded monoid of
lines. -/
lemma exists_mul_tateLine_eq_one :
    ∃ g : tateLine G d (-1), GradedMonoid.mk (-1) g * GradedMonoid.mk 1 e₁ = 1 := by
  obtain ⟨g, hg⟩ := exists_apply_eq_tateLineOne (by norm_num : (0 : ℤ) = -1 + 1)
    ((tateMul G (-1) 1 (-1 + 1) rfl (d * (-1)) (d * 1) (d * (-1 + 1)) (by ring)).flip e₁)
    (tateMul_flip_injective G _ _ he₁)
    (finrank_tateTriple_apply hG (-1)) (finrank_tateTriple_apply hG (-1 + 1))
  exact ⟨g, (tateLine_mk_mul_mk G d _ _).trans (mk_eq_one_of_eq_cast (by norm_num) hg)⟩

/-- `⟨1, e₁⟩` is a unit of the graded monoid of lines. -/
noncomputable def tateUnit : (GradedMonoid (tateLine G d))ˣ where
  val := GradedMonoid.mk 1 e₁
  inv := GradedMonoid.mk (-1) (exists_tateLine_mul_eq_one hG he₁).choose
  val_inv := (exists_tateLine_mul_eq_one hG he₁).choose_spec
  inv_val := by
    obtain ⟨g, hg⟩ := exists_mul_tateLine_eq_one hG he₁
    rwa [← left_inv_eq_right_inv hg (exists_tateLine_mul_eq_one hG he₁).choose_spec]

/-- The underlying element of `tateUnit` is `⟨1, e₁⟩`. -/
lemma tateUnit_val : (tateUnit hG he₁).val =
    GradedMonoid.mk 1 e₁ :=
  rfl

/-- The degree of `⟨1, e₁⟩ⁿ` is `n`. -/
lemma fst_tateUnit_zpow (n : ℤ) :
    (tateUnit hG he₁ ^ n).val.fst = n := by
  let φ : GradedMonoid (tateLine G d) →* Multiplicative ℤ :=
    { toFun := fun a => Multiplicative.ofAdd a.fst
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have h := congrArg Multiplicative.toAdd (map_zpow (φ.comp (Units.coeHom _)) (tateUnit hG he₁) n)
  simp only [φ, MonoidHom.coe_comp, MonoidHom.coe_mk, OneHom.coe_mk, Function.comp_apply,
    Units.coeHom_apply, toAdd_ofAdd, toAdd_zpow, tateUnit_val, smul_eq_mul] at h
  rw [h]
  exact mul_one n

/-- **The generator `eₙ ∈ G(T(n))^{dn}`**: the component of `⟨1, e₁⟩ⁿ`. -/
noncomputable def tateGen (n : ℤ) : tateLine G d n :=
  cast (congrArg (tateLine G d) (fst_tateUnit_zpow hG he₁ n))
    (tateUnit hG he₁ ^ n).val.snd

/-- `⟨n, eₙ⟩` is the `n`-th power of the unit `⟨1, e₁⟩`. -/
lemma mk_tateGen (n : ℤ) : GradedMonoid.mk n (tateGen hG he₁ n) =
    (tateUnit hG he₁ ^ n).val :=
  Sigma.ext (fst_tateUnit_zpow hG he₁ n).symm (cast_heq _ _)

omit [IsGradedMonoidal R C] [G.Monoidal] in
private lemma mk_eq_mk_iff {a b : ℤ} {x : tateLine G d a} {y : tateLine G d b} :
    GradedMonoid.mk a x = GradedMonoid.mk b y ↔ a = b ∧ x ≍ y :=
  Sigma.mk.inj_iff

omit [IsGradedMonoidal R C] [G.Monoidal] in
private lemma eq_zero_of_heq {a b : ℤ} (hab : a = b) {x : tateLine G d a} {y : tateLine G d b}
    (h : x ≍ y) (hx : x = 0) : y = 0 := by
  subst hab
  rw [← eq_of_heq h, hx]

/-- **Multiplicativity of the generators**: `eₙ eₘ = e_{n+m}`. -/
theorem tateMul_tateGen (n m : ℤ) :
    tateMul G n m (n + m) rfl (d * n) (d * m) (d * (n + m)) (by ring) (tateGen hG he₁ n)
      (tateGen hG he₁ m) = tateGen hG he₁ (n + m) := by
  have h := congrArg Units.val (zpow_add (tateUnit hG he₁) n m)
  rw [Units.val_mul, ← mk_tateGen, ← mk_tateGen, ← mk_tateGen, tateLine_mk_mul_mk] at h
  exact (eq_of_heq (mk_eq_mk_iff.1 h).2).symm

/-- The generator `tateGen 1` is the given nonzero `e₁ ∈ G(T(1))ᵈ`. -/
theorem tateGen_one : tateGen hG he₁ 1 = e₁ := by
  have h := mk_tateGen hG he₁ 1
  rw [zpow_one, tateUnit_val] at h
  exact eq_of_heq (mk_eq_mk_iff.1 h).2

/-- The generator `tateGen 0` is the unit `tateLineOne` of the lines. -/
theorem tateGen_zero : tateGen hG he₁ 0 = tateLineOne G d := by
  have h := mk_tateGen hG he₁ 0
  rw [zpow_zero, Units.val_one, tateLine_one] at h
  exact eq_of_heq (mk_eq_mk_iff.1 h).2

/-- The generator `tateGen 0` is the unit `tateOne` of `G`, up to the identification `d * 0 = 0`. -/
theorem tateGen_zero_heq : tateGen hG he₁ 0 ≍ tateOne G :=
  (heq_of_eq (tateGen_zero hG he₁)).trans (tateLineOne_heq G d)

include he₁ in
private lemma tateLineOne_ne_zero : tateLineOne G d ≠ 0 := by
  intro h
  have h' := one_mul (GradedMonoid.mk 1 e₁)
  rw [tateLine_one, tateLine_mk_mul_mk, mk_eq_mk_iff] at h'
  refine he₁ (eq_zero_of_heq (zero_add 1) h'.2 ?_)
  rw [h, LinearMap.map_zero₂]

/-- **The generators are nonzero.** -/
theorem tateGen_ne_zero (n : ℤ) : tateGen hG he₁ n ≠ 0 := by
  intro h
  have h₁ : (tateUnit hG he₁ ^ n).val * (tateUnit hG he₁ ^ (-n)).val = 1 := by
    rw [← Units.val_mul, ← zpow_add, add_neg_cancel, zpow_zero, Units.val_one]
  rw [← mk_tateGen, ← mk_tateGen, tateLine_mk_mul_mk, tateLine_one, mk_eq_mk_iff, h,
    LinearMap.map_zero₂] at h₁
  exact tateLineOne_ne_zero he₁ (eq_zero_of_heq (add_neg_cancel n) h₁.2 rfl)

end Generators

end CategoryTheory.GradedCategory.TwistedKaroubi
