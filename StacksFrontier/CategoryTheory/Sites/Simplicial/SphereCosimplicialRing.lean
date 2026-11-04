module

public import Mathlib.AlgebraicTopology.SimplexCategory.Basic
public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.Data.ZMod.Basic
public import Mathlib.RingTheory.RingHom.Flat

/-!
# A cosimplicial ring which is `ℤ` in degrees at most two and has `2`-torsion in degree three

Let `Q` be the pointed simplicial set `Δ[3] / ∂Δ[3]`: its `n`-simplices are the base point and the
surjections `[n] ↠ [3]`, and a simplex map `θ : [m] ⟶ [n]` sends a surjection `σ` to `θ ≫ σ` when
this is still surjective, and to the base point otherwise. The cosimplicial ring of this file is
the ring of functions on the simplicial scheme `Xₙ = Spec ℤ ⊔ (Qₙ ∖ {*})`, the points of
`Qₙ ∖ {*}` being `𝔽₂`-points glued to `Spec ℤ` at the base point: in degree `n` it is

  `Bₙ = {(a, F) ∈ ℤ × (Qₙ → 𝔽₂) | F(*) = a mod 2}`,

with the maps `(a, F) ↦ (a, F ∘ θ^*)`. There are no surjections `[n] ↠ [3]` for `n ≤ 2`, so
`Bₙ = ℤ` and all ring maps between these degrees are bijective; in degree three the element
`(0, δ_{id})` is nonzero and killed by `2`. The kernels `Iₙ` of the projections `Bₙ ⟶ ℤ` form a
cosimplicial ideal of `2`-torsion elements.

## Main definitions

* `CategoryTheory.SphereCosimplicialRing.sphereRing`: the cosimplicial ring.
* `CategoryTheory.SphereCosimplicialRing.augIdeal`: the ideals `Iₙ`.

## Main results

* `CategoryTheory.SphereCosimplicialRing.flat_map`: the ring maps between degrees at most two
  are flat.
* `CategoryTheory.SphereCosimplicialRing.eq_zero_of_add_self_eq_zero`: `B₀` has no `2`-torsion.
* `CategoryTheory.SphereCosimplicialRing.add_self_eq_zero_of_mem`: `Iₙ` is killed by `2`.
* `CategoryTheory.SphereCosimplicialRing.top_ne_zero`: the top element of `I₃` is nonzero.
-/

@[expose] public section

open CategoryTheory
open scoped Simplicial

universe u

namespace CategoryTheory.SphereCosimplicialRing

/-- The non-base-point `n`-simplices of `Δ[3] / ∂Δ[3]`: the surjections `[n] ↠ [3]`. -/
abbrev Surj (n : SimplexCategory) : Type := {σ : n ⟶ ⦋3⦌ // Epi σ}

/-- There are no surjections `[n] ↠ [3]` for `n ≤ 2`. -/
theorem isEmpty_surj {n : SimplexCategory} (hn : n.len ≤ 2) : IsEmpty (Surj n) :=
  ⟨fun σ => by
    have := σ.2
    have := SimplexCategory.len_le_of_epi σ.1
    change 3 ≤ n.len at this
    omega⟩

open Classical in
/-- The simplicial structure map of `Δ[3] / ∂Δ[3]` along a simplex map `θ : [m] ⟶ [n]`, on
`Option (Surj n)` with `none` the base point. -/
noncomputable def pull {m n : SimplexCategory} (θ : m ⟶ n) :
    Option (Surj n) → Option (Surj m)
  | none => none
  | some σ => if h : Epi (θ ≫ σ.1) then some ⟨θ ≫ σ.1, h⟩ else none

/-- The structure map fixes the base point. -/
theorem pull_none {m n : SimplexCategory} (θ : m ⟶ n) : pull θ none = none := rfl

/-- The structure map along an identity is the identity. -/
theorem pull_id (n : SimplexCategory) : pull (𝟙 n) = id := by
  funext q
  rcases q with _ | σ
  · rfl
  · have h : Epi (𝟙 n ≫ σ.1) := by rw [Category.id_comp]; exact σ.2
    simp only [pull, dif_pos h, id]
    exact congrArg some (Subtype.ext (Category.id_comp σ.1))

/-- The structure maps are contravariantly functorial: `pull (θ ≫ θ') = pull θ ∘ pull θ'`. -/
theorem pull_comp {l m n : SimplexCategory} (θ : l ⟶ m) (θ' : m ⟶ n) :
    pull (θ ≫ θ') = pull θ ∘ pull θ' := by
  funext q
  rcases q with _ | σ
  · rfl
  · simp only [Function.comp, pull]
    by_cases h : Epi ((θ ≫ θ') ≫ σ.1)
    · have h' : Epi (θ' ≫ σ.1) := by
        rw [Category.assoc] at h
        exact epi_of_epi θ _
      have h'' : Epi (θ ≫ θ' ≫ σ.1) := by rw [← Category.assoc]; exact h
      rw [dif_pos h, dif_pos h']
      simp only [dif_pos h'']
      exact congrArg some (Subtype.ext (Category.assoc θ θ' σ.1))
    · rw [dif_neg h]
      split_ifs with h'
      · have h'' : ¬ Epi (θ ≫ θ' ≫ σ.1) := by rw [← Category.assoc]; exact h
        simp only [dif_neg h'']
      · rfl

/-- The ring of degree `n`: pairs `(a, F)` of an integer and a function `Qₙ → 𝔽₂` whose value at
the base point is the reduction of `a`. -/
def ringSub (n : SimplexCategory) : Subring (ℤ × (Option (Surj n) → ZMod 2)) where
  carrier := {x | x.2 none = (x.1 : ZMod 2)}
  mul_mem' {a b} ha hb := by
    simp only [Set.mem_setOf_eq, Prod.fst_mul, Prod.snd_mul, Pi.mul_apply, Int.cast_mul] at *
    rw [ha, hb]
  one_mem' := by simp
  add_mem' {a b} ha hb := by
    simp only [Set.mem_setOf_eq, Prod.fst_add, Prod.snd_add, Pi.add_apply, Int.cast_add] at *
    rw [ha, hb]
  zero_mem' := by simp
  neg_mem' {a} ha := by
    simp only [Set.mem_setOf_eq, Prod.fst_neg, Prod.snd_neg, Pi.neg_apply, Int.cast_neg] at *
    rw [ha]

/-- The ring of degree `n`. -/
abbrev Ring (n : SimplexCategory) : Type := ringSub n

/-- The ring map along a simplex map: precomposition with the structure map of `Δ[3] / ∂Δ[3]`. -/
noncomputable def ringMap {m n : SimplexCategory} (θ : m ⟶ n) : Ring m →+* Ring n where
  toFun x := ⟨(x.1.1, x.1.2 ∘ pull θ), x.2⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

/-- The ring map along an identity is the identity. -/
theorem ringMap_id (n : SimplexCategory) (x : Ring n) : ringMap (𝟙 n) x = x :=
  Subtype.ext (Prod.ext rfl (by change x.1.2 ∘ pull (𝟙 n) = x.1.2; rw [pull_id]; rfl))

/-- The ring maps are functorial: `ringMap (θ ≫ θ') = ringMap θ' ∘ ringMap θ`. -/
theorem ringMap_comp {l m n : SimplexCategory} (θ : l ⟶ m) (θ' : m ⟶ n) (x : Ring l) :
    ringMap (θ ≫ θ') x = ringMap θ' (ringMap θ x) :=
  Subtype.ext (Prod.ext rfl (by
    show x.1.2 ∘ pull (θ ≫ θ') = (x.1.2 ∘ pull θ) ∘ pull θ'
    rw [pull_comp]; rfl))

/-- **The cosimplicial ring of `Δ[3] / ∂Δ[3]`.** -/
noncomputable def sphereRing : SimplexCategory ⥤ CommRingCat.{u} where
  obj n := CommRingCat.of (ULift.{u} (Ring n))
  map θ := CommRingCat.ofHom (ULift.ringEquiv.symm.toRingHom.comp
    ((ringMap θ).comp ULift.ringEquiv.toRingHom))
  map_id n := CommRingCat.hom_ext (RingHom.ext fun x => congrArg ULift.up (ringMap_id n x.down))
  map_comp θ θ' := CommRingCat.hom_ext (RingHom.ext fun x =>
    congrArg ULift.up (ringMap_comp θ θ' x.down))

/-- The map of `sphereRing` along `θ` is `ringMap θ` on the underlying rings. -/
theorem sphereRing_map_apply {m n : SimplexCategory} (θ : m ⟶ n) (x : Ring m) :
    (sphereRing.{u}.map θ).hom (ULift.up x) = ULift.up (ringMap θ x) := rfl

/-- If there are no surjections `[n] ↠ [3]`, an element of the ring of degree `n` is determined by
its integer coordinate. -/
private theorem ring_ext_of_isEmpty {n : SimplexCategory} [IsEmpty (Surj n)] {x y : Ring n}
    (h : x.1.1 = y.1.1) : x = y := by
  refine Subtype.ext (Prod.ext h (funext fun q => ?_))
  rcases q with _ | σ
  · rw [x.2, y.2, h]
  · exact isEmptyElim σ

/-- **The rings of degree at most two are `ℤ`**: every ring map between them is bijective. -/
theorem bijective_ringMap {m n : SimplexCategory} (θ : m ⟶ n) (hm : m.len ≤ 2)
    (hn : n.len ≤ 2) : Function.Bijective (ringMap θ) := by
  have := isEmpty_surj hm
  have := isEmpty_surj hn
  exact ⟨fun x y hxy => ring_ext_of_isEmpty (congrArg (fun z : Ring n => z.1.1) hxy),
    fun y => ⟨⟨(y.1.1, fun _ => (y.1.1 : ZMod 2)), rfl⟩, ring_ext_of_isEmpty rfl⟩⟩

/-- The ring maps between degrees at most two are flat. -/
theorem flat_map {m n : SimplexCategory} (θ : m ⟶ n) (hm : m.len ≤ 2) (hn : n.len ≤ 2) :
    (sphereRing.{u}.map θ).hom.Flat := by
  refine RingHom.Flat.of_bijective ?_
  show Function.Bijective (ULift.ringEquiv.symm ∘ ringMap θ ∘ ULift.ringEquiv)
  exact ULift.ringEquiv.symm.bijective.comp
    ((bijective_ringMap θ hm hn).comp ULift.ringEquiv.bijective)

/-- **The ring of degree zero has no `2`-torsion.** -/
theorem eq_zero_of_add_self_eq_zero {x : sphereRing.{u}.obj ⦋0⦌} (h : x + x = 0) : x = 0 := by
  have := isEmpty_surj (n := ⦋0⦌) (by decide)
  have ha := congrArg (fun z : sphereRing.{u}.obj ⦋0⦌ => z.down.1.1) h
  refine congrArg ULift.up (ring_ext_of_isEmpty ?_)
  change _ + _ = 0 at ha
  change _ = (0 : ℤ)
  omega

/-- The projection `Bₙ ⟶ ℤ` to the integer coordinate. -/
noncomputable def proj (n : SimplexCategory) : sphereRing.{u}.obj n →+* ℤ :=
  (RingHom.fst ℤ _).comp ((ringSub n).subtype.comp ULift.ringEquiv.toRingHom)

/-- The ideals `Iₙ = ker (Bₙ ⟶ ℤ)`. -/
noncomputable def augIdeal (n : SimplexCategory) : Ideal (sphereRing.{u}.obj n) :=
  RingHom.ker (proj n)

/-- The ring maps of `sphereRing` carry `Iₘ` into `Iₙ`. -/
theorem augIdeal_comap {m n : SimplexCategory} (θ : m ⟶ n) :
    augIdeal.{u} m ≤ (augIdeal n).comap (sphereRing.map θ).hom :=
  fun _ hx => hx

/-- **The ideals `Iₙ` are killed by `2`.** -/
theorem add_self_eq_zero_of_mem {n : SimplexCategory} {x : sphereRing.{u}.obj n}
    (hx : x ∈ augIdeal n) : x + x = 0 := by
  obtain ⟨⟨⟨a, F⟩, hF⟩⟩ := x
  have ha : a = 0 := hx
  refine congrArg ULift.up (Subtype.ext (Prod.ext ?_ (funext fun q => ?_)))
  · show a + a = 0
    rw [ha, add_zero]
  · show F q + F q = 0
    generalize F q = c
    fin_cases c <;> rfl

/-- The identity of `[3]`, as a surjection. -/
abbrev surjId : Surj ⦋3⦌ := ⟨𝟙 _, inferInstance⟩

open Classical in
/-- The element `(0, δ_{id})` of degree three. -/
noncomputable def top : sphereRing.{u}.obj ⦋3⦌ :=
  ULift.up ⟨(0, fun q => if q = some surjId then 1 else 0), by
    change (if (none : Option (Surj ⦋3⦌)) = some surjId then (1 : ZMod 2) else 0) =
      ((0 : ℤ) : ZMod 2)
    simp⟩

/-- The element `top` lies in `I₃`. -/
theorem top_mem : top.{u} ∈ augIdeal ⦋3⦌ := rfl

/-- **The element `top` is nonzero.** -/
theorem top_ne_zero : top.{u} ≠ 0 := by
  intro h
  have := congrArg (fun z : sphereRing.{u}.obj ⦋3⦌ => z.down.1.2 (some surjId)) h
  change (if (some surjId : Option (Surj ⦋3⦌)) = some surjId then (1 : ZMod 2) else 0) = 0 at this
  simp at this

end CategoryTheory.SphereCosimplicialRing

end
