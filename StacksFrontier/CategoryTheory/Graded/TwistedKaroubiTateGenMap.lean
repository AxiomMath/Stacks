module

public import StacksFrontier.CategoryTheory.Graded.TwistedKaroubiTateRealization
public import StacksFrontier.CategoryTheory.GradedObject.MonoidalNatTransElements

/-!
# The generators of the twisted units under maps of lines

Let `G : TwistedKaroubi R C ⥤ GradedObject ℤ (ModuleCat F)` be monoidal with `G(T(1))`
concentrated in degree `d`, and let `eₙ ∈ G(T(n))^{dn}` be the generators determined by a nonzero
`e₁` (`CategoryTheory.GradedCategory.TwistedKaroubi.tateGen`). The generators are the components of
the powers of the unit `⟨1, e₁⟩` of the graded monoid of lines, so any family of maps of lines
compatible with the products and the units carries the generators of `e₁` to the generators of
the image of `e₁`. Two instances:

* a monoidal natural transformation `θ : G ⟶ G'` sends the generators of `e₁` to the generators
  of `θ(e₁)` (`CategoryTheory.GradedCategory.TwistedKaroubi.app_tateGen`);
* the generators of `c e₁`, for `c ∈ Fˣ`, are `cⁿ eₙ`
  (`CategoryTheory.GradedCategory.TwistedKaroubi.tateGen_smul`).

## Main results

* `CategoryTheory.GradedCategory.TwistedKaroubi.tateGen_map`: the general statement.
* `CategoryTheory.GradedCategory.TwistedKaroubi.app_tateGen`,
  `CategoryTheory.GradedCategory.TwistedKaroubi.tateGen_smul`.
-/

@[expose] public section

open CategoryTheory MonoidalCategory CategoryTheory.Limits

namespace CategoryTheory.GradedCategory.TwistedKaroubi

universe w v u uF

variable {R : Type w} [Ring R] {C : Type u} [Category.{v} C] [Preadditive C] [GradedCategory R C]
  [MonoidalCategory C] [IsGradedMonoidal R C] {F : Type uF} [Field F]
  {G G' : TwistedKaroubi R C ⥤ GradedObject ℤ (ModuleCat.{uF} F)}

section Map

variable [G.Monoidal] [G'.Monoidal] {d : ℤ}

/-- The map of graded monoids of lines induced by maps of lines compatible with the products and
the units. -/
noncomputable def lineHom (φ : ∀ n, tateLine G d n → tateLine G' d n)
    (hmul : ∀ (n m : ℤ) (x : tateLine G d n) (y : tateLine G d m),
      φ (n + m) (tateMul G n m (n + m) rfl (d * n) (d * m) (d * (n + m)) (by ring) x y) =
        tateMul G' n m (n + m) rfl (d * n) (d * m) (d * (n + m)) (by ring) (φ n x) (φ m y))
    (hone : φ 0 (tateLineOne G d) = tateLineOne G' d) :
    GradedMonoid (tateLine G d) →* GradedMonoid (tateLine G' d) where
  toFun a := ⟨a.1, φ a.1 a.2⟩
  map_one' := Sigma.ext rfl (heq_of_eq hone)
  map_mul' a b := by
    obtain ⟨n, x⟩ := a
    obtain ⟨m, y⟩ := b
    exact Sigma.ext rfl (heq_of_eq (hmul n m x y))


/-- **Maps of lines carry generators to generators.** A family of maps of lines compatible with
the products and the units, sending `e₁` to `e₁'`, sends `eₙ` to `eₙ'` for every `n`. -/
theorem tateGen_map (φ : ∀ n, tateLine G d n → tateLine G' d n)
    (hmul : ∀ (n m : ℤ) (x : tateLine G d n) (y : tateLine G d m),
      φ (n + m) (tateMul G n m (n + m) rfl (d * n) (d * m) (d * (n + m)) (by ring) x y) =
        tateMul G' n m (n + m) rfl (d * n) (d * m) (d * (n + m)) (by ring) (φ n x) (φ m y))
    (hone : φ 0 (tateLineOne G d) = tateLineOne G' d)
    (hG : ∀ i, i ≠ d → IsZero ((G.obj (tateTriple R C 1)) i))
    (hG' : ∀ i, i ≠ d → IsZero ((G'.obj (tateTriple R C 1)) i))
    {e₁ : tateLine G d 1} (he₁ : e₁ ≠ 0) {e₁' : tateLine G' d 1} (he₁' : e₁' ≠ 0)
    (h₁ : φ 1 e₁ = e₁') (n : ℤ) :
    φ n (tateGen hG he₁ n) = tateGen hG' he₁' n := by
  let f : GradedMonoid (tateLine G d) →* GradedMonoid (tateLine G' d) := lineHom φ hmul hone
  let u : (GradedMonoid (tateLine G d))ˣ := tateUnit hG he₁
  have hu : Units.map f u = tateUnit hG' he₁' := by
    refine Units.ext ?_
    rw [Units.coe_map, tateUnit_val, tateUnit_val]
    exact Sigma.ext rfl (heq_of_eq h₁)
  have h := congrArg (fun u ↦ (u ^ n).val) hu
  simp only [← map_zpow, Units.coe_map] at h
  rw [← mk_tateGen, ← mk_tateGen] at h
  exact eq_of_heq (Sigma.mk.inj_iff.1 h).2

end Map

section NatTrans

variable [G.Monoidal] [G'.Monoidal] (θ : G ⟶ G') [θ.IsMonoidal]

/-- A monoidal natural transformation commutes with the products of the twisted units. -/
theorem app_tateMul (n m p : ℤ) (hp : n + m = p) (i j k : ℤ) (hk : i + j = k)
    (x : G.obj (tateTriple R C n) i) (y : G.obj (tateTriple R C m) j) :
    θ.app (tateTriple R C p) k (tateMul G n m p hp i j k hk x y) =
      tateMul G' n m p hp i j k hk (θ.app _ i x) (θ.app _ j y) := by
  rw [tateMul_apply, tateMul_apply, NatTrans.app_map_apply, NatTrans.app_gradedMul]

/-- A monoidal natural transformation sends the unit of the lines to the unit of the lines. -/
theorem app_tateLineOne (d : ℤ) :
    θ.app (tateTriple R C 0) (d * 0) (tateLineOne G d) = tateLineOne G' d := by
  have h : ∀ (j : ℤ) (hj : 0 = j), θ.app (tateTriple R C 0) j
      (cast (congrArg (fun j : ℤ => (G.obj (tateTriple R C 0) j : Type uF)) hj) (tateOne G)) =
      cast (congrArg (fun j : ℤ => (G'.obj (tateTriple R C 0) j : Type uF)) hj) (tateOne G') := by
    rintro j rfl
    exact NatTrans.app_gradedOne θ
  exact h _ (mul_zero d).symm

/-- **A monoidal natural transformation carries the generators of `e₁` to the generators of
`θ(e₁)`.** -/
theorem app_tateGen {d : ℤ} (hG : ∀ i, i ≠ d → IsZero ((G.obj (tateTriple R C 1)) i))
    (hG' : ∀ i, i ≠ d → IsZero ((G'.obj (tateTriple R C 1)) i))
    {e₁ : tateLine G d 1} (he₁ : e₁ ≠ 0) (he₁' : θ.app (tateTriple R C 1) (d * 1) e₁ ≠ 0)
    (n : ℤ) :
    θ.app (tateTriple R C n) (d * n) (tateGen hG he₁ n) = tateGen hG' he₁' n :=
  tateGen_map (fun n x ↦ θ.app (tateTriple R C n) (d * n) x)
    (fun _ _ x y ↦ app_tateMul θ _ _ _ _ _ _ _ _ x y) (app_tateLineOne θ d) hG hG' he₁ he₁'
    rfl n

end NatTrans

section Smul

variable [G.Monoidal] {d : ℤ} (hG : ∀ i, i ≠ d → IsZero ((G.obj (tateTriple R C 1)) i))

/-- **The generators of `c e₁` are `cⁿ eₙ`.** -/
theorem tateGen_smul {e₁ : tateLine G d 1} (he₁ : e₁ ≠ 0) (c : Fˣ)
    (hce₁ : ((c : F) • e₁) ≠ 0) (n : ℤ) :
    tateGen hG hce₁ n = ((c ^ n : Fˣ) : F) • tateGen hG he₁ n := by
  refine (tateGen_map (G := G) (G' := G) (fun n x ↦ ((c ^ n : Fˣ) : F) • x) (fun n m x y ↦ ?_)
    ?_ hG hG he₁ hce₁ (by simp) n).symm
  · rw [map_smul, map_smul, LinearMap.smul_apply, smul_smul, ← Units.val_mul, ← zpow_add,
      add_comm m n]
  · simp

end Smul

end CategoryTheory.GradedCategory.TwistedKaroubi
