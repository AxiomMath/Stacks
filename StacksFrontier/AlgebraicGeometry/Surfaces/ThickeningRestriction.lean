module

public import StacksFrontier.AlgebraicGeometry.Cohomology.SectionsSurjective
public import StacksFrontier.AlgebraicGeometry.Divisors.DivisorPicardClass
public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartier.SumSequence
public import StacksFrontier.AlgebraicGeometry.Scheme.QuasiCoherent.ClosedUnionExactSequence
public import StacksFrontier.AlgebraicGeometry.Surfaces.FormalNeighborhoodRing

/-!
# Functions extend from one infinitesimal thickening to the next

Let `D` be an effective Cartier divisor on a scheme `X` and let `Eₙ₊₁ = (D ^ (n + 1)).subscheme`
be its infinitesimal thickenings. Restriction of global functions
`Γ(Eₙ₊₂, 𝒪) ⟶ Γ(Eₙ₊₁, 𝒪)` is **surjective** as soon as `H¹(X, 𝒪_X(-D ^ (n + 1))|_D)` vanishes:
the short exact sequence of [Stacks, Tag 0C4T]

`0 ⟶ 𝒪_X(-D ^ (n + 1))|_D ⟶ 𝒪_{Eₙ₊₂} ⟶ 𝒪_{Eₙ₊₁} ⟶ 0`

has that module as its kernel, and the long exact sequence of sheaf cohomology turns the
vanishing of its `H¹` into surjectivity on global sections
(`Stacks.Cohomology.surjective_sections_of_isZero_firstCohomology`).

This surjectivity is the geometric input to [Stacks, Tag 0C2K]: for `D` an exceptional curve of
the first kind the kernel pulls back to `𝒪(n + 1)` on `𝐏¹_k`, whose first cohomology vanishes,
so the inverse system defining
`AlgebraicGeometry.Scheme.IdealSheafData.formalNeighborhoodRing` has surjective transition maps.
Once they are surjective the projections out of the inverse limit are surjective too: a function
on one thickening is lifted step by step to a compatible sequence on all of them.

## Main definitions

* `AlgebraicGeometry.Scheme.IdealSheafData.thickeningRestrictionLE` — restriction of global
  functions from the `(j + 1)`-st thickening to the `(i + 1)`-st, for `i ≤ j`.

## Main results

* `AlgebraicGeometry.Scheme.IdealSheafData.closedSubschemeRestriction_appTop` — on global
  functions, the restriction between nested closed subschemes is the structure-sheaf map of the
  inclusion of subschemes.
* `AlgebraicGeometry.Scheme.IdealSheafData.surjective_inclusion_appTop` — global functions
  extend along the inclusion of a closed subscheme into the sum with an effective Cartier
  divisor, given the vanishing of the first cohomology of the twisted ideal sheaf.
* `AlgebraicGeometry.Scheme.IdealSheafData.surjective_thickeningRestriction` — the transition
  maps of the inverse system of the infinitesimal thickenings of an effective Cartier divisor
  are surjective, given the same vanishing.
* `AlgebraicGeometry.Scheme.IdealSheafData.surjective_formalNeighborhoodProjection` — if every
  transition map is surjective then so is every projection out of the ring of compatible
  functions.

## References

* [Stacks Project, Tag 0C2K](https://stacks.math.columbia.edu/tag/0C2K)
* [Stacks Project, Tag 0C4T](https://stacks.math.columbia.edu/tag/0C4T)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {X : Scheme.{u}}

/-! ### Restriction on global functions -/

/-- The powers of an ideal sheaf decrease: `D ^ (j + 1) ≤ D ^ (i + 1)` for `i ≤ j`. -/
theorem pow_succ_le_pow_succ (D : X.IdealSheafData) {i j : ℕ} (h : i ≤ j) :
    D ^ (j + 1) ≤ D ^ (i + 1) :=
  le_def.mpr fun U ↦ by
    simp only [ideal_pow]
    exact Ideal.pow_le_pow_right (by omega)

/-- A positive power of an ideal sheaf is contained in it: the `(n + 1)`-st thickening of `D`
contains `V(D)`, so a function on it restricts to `V(D)`. -/
theorem pow_succ_le_self (D : X.IdealSheafData) (n : ℕ) : D ^ (n + 1) ≤ D :=
  le_def.mpr fun _ ↦ Ideal.pow_le_self (by simp)

/-- **Restricting a global function to a closed subscheme and then to a smaller one restricts it
to the smaller one.** The transitivity of
`AlgebraicGeometry.Scheme.IdealSheafData.inclusion_comp`, read on global functions. -/
theorem inclusion_appTop_inclusion_appTop {I J K : X.IdealSheafData} (h₁ : I ≤ J) (h₂ : J ≤ K)
    (w : Γ(I.subscheme, (⊤ : I.subscheme.Opens))) :
    (inclusion h₂).appTop.hom ((inclusion h₁).appTop.hom w) =
      (inclusion (h₁.trans h₂)).appTop.hom w := by
  rw [← inclusion_comp h₁ h₂, Scheme.Hom.comp_appTop]
  rfl

/-- **Restricting a global function along the identity inclusion does nothing.** -/
theorem inclusion_appTop_rfl {I : X.IdealSheafData} (h : I ≤ I)
    (w : Γ(I.subscheme, (⊤ : I.subscheme.Opens))) : (inclusion h).appTop.hom w = w := by
  rw [inclusion_id]
  rfl

/-- **Restriction along an equality of ideal sheaves is bijective**, the inverse being
restriction along the equality the other way round. -/
theorem inclusion_appTop_inclusion_appTop_of_eq {I J : X.IdealSheafData} (h : I = J)
    (w : Γ(I.subscheme, (⊤ : I.subscheme.Opens))) :
    (inclusion h.ge).appTop.hom ((inclusion h.le).appTop.hom w) = w :=
  (inclusion_appTop_inclusion_appTop h.le h.ge w).trans (inclusion_appTop_rfl _ w)

/-- `AlgebraicGeometry.Scheme.IdealSheafData.inclusion_appTop_inclusion_appTop_of_eq` the other
way round. -/
theorem inclusion_appTop_inclusion_appTop_of_eq_symm {I J : X.IdealSheafData} (h : I = J)
    (w : Γ(J.subscheme, (⊤ : J.subscheme.Opens))) :
    (inclusion h.le).appTop.hom ((inclusion h.ge).appTop.hom w) = w :=
  inclusion_appTop_inclusion_appTop_of_eq h.symm w

/-- Restriction between successive thickenings is restriction along `D ^ (n + 2) ≤ D ^ (n + 1)`,
at whichever proof of that inequality is at hand. -/
theorem thickeningRestriction_eq_inclusion_appTop (D : X.IdealSheafData) (n : ℕ)
    (h : D ^ (n + 2) ≤ D ^ (n + 1)) (v : Γ(thickening D (n + 1), ⊤)) :
    thickeningRestriction D n v = (inclusion h).appTop.hom v := rfl

private lemma comp_app_apply_aux {M N K : X.Modules} (f : M ⟶ N) (g : N ⟶ K) (U : X.Opens)
    (m : Γ(M, U)) : (f ≫ g).app U m = g.app U (f.app U m) := rfl

private lemma eqToHom_app_heq_aux {N K : X.Modules} (e : N = K) (U : X.Opens) (n : Γ(N, U))
    (k : Γ(K, U)) (hk : HEq n k) : (eqToHom e).app U n = k := by
  subst e
  exact eq_of_heq hk

private lemma pushforwardComp_app_apply_aux {Y Z : Scheme.{u}} (p : X ⟶ Y) (q : Y ⟶ Z)
    (M : X.Modules) (U : Z.Opens)
    (m : Γ((Scheme.Modules.pushforward q).obj ((Scheme.Modules.pushforward p).obj M), U)) :
    ((Scheme.Modules.pushforwardComp p q).hom.app M).app U m = m := rfl

private lemma pushforward_map_app_apply_aux {Z : Scheme.{u}} (q : X ⟶ Z) {M N : X.Modules}
    (φ : M ⟶ N) (U : Z.Opens) (m : Γ((Scheme.Modules.pushforward q).obj M, U)) :
    ((Scheme.Modules.pushforward q).map φ).app U m = φ.app (q ⁻¹ᵁ U) m := rfl

private lemma unitToPushforward_app_apply_aux {Z : Scheme.{u}} (r : X ⟶ Z) (U : Z.Opens)
    (a : Γ(Z, U)) :
    Scheme.Modules.Hom.app (M := SheafOfModules.unit Z.ringCatSheaf)
      (N := (Scheme.Modules.pushforward r).obj (SheafOfModules.unit X.ringCatSheaf))
      (SheafOfModules.unitToPushforwardObjUnit r.toRingCatSheafHom) U a = r.app U a := rfl

/-- **On global functions, restriction between nested closed subschemes is the structure-sheaf
map of the inclusion.** For `I ≤ J` the map `𝒪_{V(I)} ⟶ 𝒪_{V(J)}` of `𝒪_X`-modules evaluated at
the total open is the ring map induced by `V(J) ⟶ V(I)`. -/
theorem closedSubschemeRestriction_appTop {I J : X.IdealSheafData} (h : I ≤ J)
    (x : Γ(closedSubschemeStructureSheaf I, (⊤ : X.Opens))) :
    (closedSubschemeRestriction h).app ⊤ x = (inclusion h).appTop x := by
  rw [closedSubschemeRestriction]
  refine Eq.trans (comp_app_apply_aux _ _ ⊤ x) ?_
  refine Eq.trans (comp_app_apply_aux _ _ ⊤ _) ?_
  refine eqToHom_app_heq_aux _ ⊤ _ _ ?_
  refine heq_of_eq ?_
  refine Eq.trans (pushforwardComp_app_apply_aux _ _ _ ⊤ _) ?_
  refine Eq.trans (pushforward_map_app_apply_aux _ _ ⊤ _) ?_
  exact unitToPushforward_app_apply_aux (inclusion h) (I.subschemeι ⁻¹ᵁ ⊤) x

/-! ### Extending functions across an effective Cartier divisor -/

open Stacks.Divisors in
/-- **Global functions extend from a closed subscheme to its sum with an effective Cartier
divisor.** Let `D ⊆ D'` be effective Cartier divisors with `D' = D + C`. If the first cohomology
of `𝒪_X(-D)|_C` vanishes, then every global function on `V(D)` is the restriction of a global
function on `V(D')`.

The short exact sequence `0 ⟶ 𝒪_X(-D)|_C ⟶ 𝒪_{D'} ⟶ 𝒪_D ⟶ 0` is [Stacks, Tag 0C4T]. -/
theorem surjective_inclusion_appTop (D D' C : X.IdealSheafData)
    (hD : IsEffectiveCartierDivisor D) (hD' : IsEffectiveCartierDivisor D')
    (hC : IsEffectiveCartierDivisor C) (hsub : D' ≤ D) (hsum : D' = D * C)
    (h : IsZero (((Stacks.Cohomology.sectionsFunctor X ⊤).rightDerived 1).obj
      ((Scheme.Modules.pushforward C.subschemeι).obj
        ((Scheme.Modules.pullback C.subschemeι).obj (negativeTwist D))))) :
    Function.Surjective (inclusion hsub).appTop.hom := by
  obtain ⟨_, _, hse⟩ := addEffectiveCartierDivisor_shortExact D D' C hD hD' hC hsub hsum
  intro b
  obtain ⟨a, ha⟩ :=
    Stacks.Cohomology.surjective_sections_of_isZero_firstCohomology X ⊤ hse h b
  exact ⟨a, (closedSubschemeRestriction_appTop hsub a).symm.trans ha⟩

open Stacks.Divisors in
/-- **The transition maps of the inverse system of infinitesimal thickenings are surjective.**
For `D` an effective Cartier divisor, a global function on the `(n + 1)`-st thickening extends
to the `(n + 2)`-nd as soon as `H¹(X, 𝒪_X(-D ^ (n + 1))|_D)` vanishes.

This is [Stacks, Tag 0C4T] for `D ^ (n + 2) = D ^ (n + 1) + D` together with the long exact
sequence of sheaf cohomology. -/
theorem surjective_thickeningRestriction (D : X.IdealSheafData) [IsEffectiveCartierDivisor D]
    (n : ℕ)
    (h : IsZero (((Stacks.Cohomology.sectionsFunctor X ⊤).rightDerived 1).obj
      ((Scheme.Modules.pushforward D.subschemeι).obj
        ((Scheme.Modules.pullback D.subschemeι).obj (negativeTwist (D ^ (n + 1))))))) :
    Function.Surjective (thickeningRestriction D n) :=
  surjective_inclusion_appTop (D ^ (n + 1)) (D ^ (n + 2)) D inferInstance inferInstance
    inferInstance (pow_succ_le_pow_succ D (Nat.le_succ n)) (pow_succ D (n + 1)) h

/-! ### Lifting a function through the whole tower of thickenings -/

/-- Restriction of global functions from the `(j + 1)`-st infinitesimal thickening to the
`(i + 1)`-st, for `i ≤ j`. -/
def thickeningRestrictionLE (D : X.IdealSheafData) {i j : ℕ} (h : i ≤ j) :
    Γ(thickening D j, ⊤) →+* Γ(thickening D i, ⊤) :=
  (inclusion (pow_succ_le_pow_succ D h)).appTop.hom

/-- Restriction from an infinitesimal thickening to itself is the identity. -/
@[simp]
theorem thickeningRestrictionLE_self (D : X.IdealSheafData) (i : ℕ)
    (x : Γ(thickening D i, ⊤)) : thickeningRestrictionLE D (le_refl i) x = x :=
  inclusion_appTop_rfl _ x

/-- Restricting global functions from `thickening D k` to `thickening D j` and then to
`thickening D i` is the restriction from `thickening D k` to `thickening D i`. -/
theorem thickeningRestrictionLE_comp (D : X.IdealSheafData) {i j k : ℕ} (hij : i ≤ j)
    (hjk : j ≤ k) (x : Γ(thickening D k, ⊤)) :
    thickeningRestrictionLE D hij (thickeningRestrictionLE D hjk x) =
      thickeningRestrictionLE D (hij.trans hjk) x :=
  inclusion_appTop_inclusion_appTop (pow_succ_le_pow_succ D hjk) (pow_succ_le_pow_succ D hij) x

/-- Restriction from the `(n + 2)`-nd infinitesimal thickening to the `(n + 1)`-st is the
transition map `thickeningRestriction D n`. -/
@[simp]
theorem thickeningRestrictionLE_succ (D : X.IdealSheafData) (n : ℕ)
    (x : Γ(thickening D (n + 1), ⊤)) :
    thickeningRestrictionLE D (Nat.le_succ n) x = thickeningRestriction D n x := rfl

/-- The tower of successive lifts of a global function on one infinitesimal thickening, chosen
using surjectivity of the transition maps. -/
private noncomputable def thickeningLiftTower (D : X.IdealSheafData)
    (hsurj : ∀ m, Function.Surjective (thickeningRestriction D m)) {n : ℕ}
    (a : Γ(thickening D n, ⊤)) : ∀ k, Γ(thickening D (n + k), ⊤)
  | 0 => a
  | k + 1 => Classical.choose (hsurj (n + k) (thickeningLiftTower D hsurj a k))

private lemma thickeningLiftTower_spec (D : X.IdealSheafData)
    (hsurj : ∀ m, Function.Surjective (thickeningRestriction D m)) {n : ℕ}
    (a : Γ(thickening D n, ⊤)) (k : ℕ) :
    thickeningRestriction D (n + k) (thickeningLiftTower D hsurj a (k + 1)) =
      thickeningLiftTower D hsurj a k :=
  Classical.choose_spec (hsurj (n + k) (thickeningLiftTower D hsurj a k))

private lemma thickeningLiftTower_restrict (D : X.IdealSheafData)
    (hsurj : ∀ m, Function.Surjective (thickeningRestriction D m)) {n : ℕ}
    (a : Γ(thickening D n, ⊤)) (k : ℕ) :
    thickeningRestrictionLE D (Nat.le_add_right n k) (thickeningLiftTower D hsurj a k) = a := by
  induction k with
  | zero => exact thickeningRestrictionLE_self D n a
  | succ k ih =>
    rw [← thickeningRestrictionLE_comp D (Nat.le_add_right n k) (Nat.le_succ (n + k)),
      thickeningRestrictionLE_succ, thickeningLiftTower_spec, ih]

/-- **The projections out of the ring of compatible functions are surjective when the transition
maps are.** A global function on one infinitesimal thickening then lifts to a compatible family
of global functions on all of them. -/
theorem surjective_formalNeighborhoodProjection (D : X.IdealSheafData)
    (hsurj : ∀ m, Function.Surjective (thickeningRestriction D m)) (n : ℕ) :
    Function.Surjective (formalNeighborhoodProjection D n) := by
  intro a
  refine ⟨⟨fun m => thickeningRestrictionLE D (Nat.le_add_left m n)
    (thickeningLiftTower D hsurj a m), fun m => ?_⟩, ?_⟩
  · show thickeningRestriction D m (thickeningRestrictionLE D (Nat.le_add_left (m + 1) n)
          (thickeningLiftTower D hsurj a (m + 1))) =
        thickeningRestrictionLE D (Nat.le_add_left m n) (thickeningLiftTower D hsurj a m)
    rw [← thickeningRestrictionLE_succ,
      thickeningRestrictionLE_comp D (Nat.le_succ m) (Nat.le_add_left (m + 1) n),
      ← thickeningLiftTower_spec D hsurj a m, ← thickeningRestrictionLE_succ,
      thickeningRestrictionLE_comp D (Nat.le_add_left m n) (Nat.le_succ (n + m))]
  · exact thickeningLiftTower_restrict D hsurj a n

end AlgebraicGeometry.Scheme.IdealSheafData

end
