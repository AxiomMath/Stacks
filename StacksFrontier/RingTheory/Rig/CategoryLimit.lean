module

public import Mathlib.CategoryTheory.Equivalence
public import StacksFrontier.RingTheory.AdicCompletion.InverseLimit
public import StacksFrontier.RingTheory.AdicCompletion.SmulTopPow
public import StacksFrontier.RingTheory.Rig.Category

/-!
# The limit of an adic system of algebras

Fix a commutative ring `A` and a finitely generated ideal `I ⊆ A`. Stacks chapter 88 attaches
to this datum two categories: `Rig.AdicAlgebraSystem A I`, whose objects are the inverse systems
`… → B₃ → B₂ → B₁` of finite type `A ⧸ Iⁿ`-algebras in which each transition exhibits its target
as the reduction of its source, and `Rig.AdicFiniteTypeAlgebra A I`, whose objects are the
`I`-adically complete `A`-algebras `B` whose reduction `B ⧸ IB` is of finite type over `A ⧸ I`.
The functor `B ↦ (B ⧸ Iⁿ⁺¹B)` between them is `Rig.adicQuotientFunctor`.

This file constructs the functor in the other direction, `(Bₙ) ↦ lim Bₙ`, and proves that the
two are quasi-inverse, so that the two categories are equivalent.

## Main definitions

* `Rig.AdicAlgebraSystem.limitCarrier` — the limit `lim Bₙ` of a system, as a ring: the
  compatible families in the product of its terms.
* `Rig.AdicAlgebraSystem.limitProj` — the projection `lim Bₙ → Bₙ`.
* `Rig.adicLimitFunctor` — the functor `(Bₙ) ↦ lim Bₙ` from systems to complete algebras.
* `Rig.adicQuotientEquivalence` — the equivalence of the two categories whose functor is
  `Rig.adicQuotientFunctor` and whose inverse is `Rig.adicLimitFunctor`.

## Main results

* `Rig.AdicAlgebraSystem.ker_limitProj` — the kernel of `lim Bₙ → Bₙ` is `Iⁿ⁺¹ lim Bₙ`, so
  that the system is recovered from its limit.
* `Rig.AdicAlgebraSystem.limit_isAdicComplete` — the limit is `I`-adically complete.

## Implementation notes

The terms of a system are indexed from zero, `X.B n` standing for the source's `B_{n+1}`, while
the inverse systems of [StacksProject 09B8] carry the relation `Mₙ = M_{n+1} ⧸ Iⁿ M_{n+1}`, which
forces the zero module at level `0`. The comparison is `AdicAlgebraSystem.shiftType`, the system
extended by the zero module, together with the linear equivalence `shiftEquiv` of its limit with
the limit of the original system; the kernel computation and the adic completeness of the limit
are read off from [StacksProject 09B8] through it.

## References

* [StacksProject 09B8](https://stacks.math.columbia.edu/tag/09B8)
* [StacksProject 0AJN](https://stacks.math.columbia.edu/tag/0AJN)
* [StacksProject 0AJP](https://stacks.math.columbia.edu/tag/0AJP)
* [StacksProject 0AL3](https://stacks.math.columbia.edu/tag/0AL3)
* [StacksProject 0AL4](https://stacks.math.columbia.edu/tag/0AL4)
-/

@[expose] public section

open CategoryTheory

universe u v

namespace Rig

namespace AdicAlgebraSystem

variable {A : Type u} [CommRing A] {I : Ideal A} (X : AdicAlgebraSystem.{u, v} A I)

/-- The structure map `A → Bₙ` of a system, through the quotient `A ⧸ I ^ (n + 1)`. -/
public def baseMap (n : ℕ) : A →+* X.B n :=
  (X.algebraMap n).comp (Ideal.Quotient.mk (I ^ (n + 1)))

/-- Each term of a system is an `A`-algebra through `A → A ⧸ I ^ (n + 1) → Bₙ`. -/
local instance algebraB (n : ℕ) : Algebra A (X.B n) := (X.baseMap n).toAlgebra

/-- The algebra structure of a term of the system is the one given by `baseMap`. -/
public theorem algebraMap_B (n : ℕ) : Algebra.algebraMap A (X.B n) = X.baseMap n := rfl

/-- The transition maps of a system commute with its structure maps from `A`. -/
public theorem transition_baseMap (n : ℕ) (a : A) :
    X.transition n (X.baseMap (n + 1) a) = X.baseMap n a :=
  DFunLike.congr_fun (X.transition_comp_algebraMap n) a

/-- A transition map of a system, as an `A`-linear map. -/
private def transitionLinear (n : ℕ) : X.B (n + 1) →ₗ[A] X.B n where
  toFun := X.transition n
  map_add' := map_add _
  map_smul' a x := by
    change X.transition n (a • x) = a • X.transition n x
    rw [Algebra.smul_def, Algebra.smul_def, algebraMap_B, algebraMap_B, map_mul,
      X.transition_baseMap]

/-! ### The limit of a system -/

/-- The limit `lim Bₙ` of a system, as a subring of the product of its terms. -/
public def limitSubring : Subring (∀ n, X.B n) where
  carrier := {f | ∀ n, X.transition n (f (n + 1)) = f n}
  mul_mem' hf hg n := by simp [hf n, hg n]
  one_mem' n := by simp
  add_mem' hf hg n := by simp [hf n, hg n]
  zero_mem' n := by simp
  neg_mem' hf n := by simp [hf n]

/-- The limit `B = lim Bₙ` of a system. -/
public def limitCarrier : Type v := X.limitSubring

/-- The limit is a commutative ring, as a subring of the product `∏ₙ Bₙ`. -/
public instance : CommRing X.limitCarrier := inferInstanceAs (CommRing X.limitSubring)

/-- The compatible family underlying an element of the limit. -/
public def limitVal (f : X.limitCarrier) (n : ℕ) : X.B n := (f : X.limitSubring).1 n

/-- The components of an element of the limit are a compatible family. -/
public theorem transition_limitVal (f : X.limitCarrier) (n : ℕ) :
    X.transition n (X.limitVal f (n + 1)) = X.limitVal f n :=
  (f : X.limitSubring).2 n

/-- An element of the limit is determined by its components. -/
@[ext] public theorem limit_ext {f g : X.limitCarrier}
    (h : ∀ n, X.limitVal f n = X.limitVal g n) : f = g :=
  Subtype.ext (funext h)

/-- The structure map `A → lim Bₙ` of the limit. -/
public def limitBaseMap : A →+* X.limitCarrier :=
  (RingHom.pi fun n => X.baseMap n).codRestrict X.limitSubring
    fun a n => X.transition_baseMap n a

/-- The limit is an `A`-algebra through the structure map `A → lim Bₙ`. -/
public instance : Algebra A X.limitCarrier := X.limitBaseMap.toAlgebra

/-- The projection `lim Bₙ → Bₙ` of the limit onto its `n`-th term. -/
public def limitProj (n : ℕ) : X.limitCarrier →+* X.B n where
  toFun f := X.limitVal f n
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

/-- The projection of the limit onto its `n`-th term is the `n`-th component. -/
@[simp] public theorem limitProj_apply (n : ℕ) (f : X.limitCarrier) :
    X.limitProj n f = X.limitVal f n := rfl

/-- The components of the image of an element of `A` in the limit. -/
@[simp] public theorem limitVal_algebraMap (a : A) (n : ℕ) :
    X.limitVal (Algebra.algebraMap A X.limitCarrier a) n = X.baseMap n a := rfl

/-! ### The shifted system of modules -/

/-- The terms of a system, shifted up by one and extended by the zero module, so that the
relation `Mₙ = M_{n+1} ⧸ Iⁿ M_{n+1}` of [StacksProject 09B8] holds at every level. -/
private def shiftType : ℕ → Type v
  | 0 => PUnit.{v + 1}
  | n + 1 => X.B n

private instance shiftTypeAddCommGroup : ∀ n, AddCommGroup (X.shiftType n)
  | 0 => inferInstanceAs (AddCommGroup PUnit)
  | n + 1 => inferInstanceAs (AddCommGroup (X.B n))

private instance shiftTypeModule : ∀ n, Module A (X.shiftType n)
  | 0 => inferInstanceAs (Module A PUnit)
  | n + 1 => inferInstanceAs (Module A (X.B n))

private instance shiftTypeSubsingleton : Subsingleton (X.shiftType 0) :=
  inferInstanceAs (Subsingleton PUnit)

/-- The zeroth term of the shifted system is the zero module. -/
private theorem shiftType_zero_eq (x y : X.shiftType 0) : x = y := Subsingleton.elim x y

/-- The transition maps of the shifted system: a transition map of the original system above
level `0`, and the zero map onto the zero module at level `0`. -/
private def shiftπ : ∀ n, X.shiftType (n + 1) →ₗ[A] X.shiftType n
  | 0 => 0
  | n + 1 => X.transitionLinear n

/-- Membership in `Iᵏ • ⊤` for an `A`-algebra is membership in the `k`-th power of the ideal
generated by `I`. -/
private theorem mem_smul_top_pow_iff {B : Type*} [CommRing B] [Algebra A B] (k : ℕ) (x : B) :
    x ∈ I ^ k • (⊤ : Submodule A B) ↔ x ∈ I.map (Algebra.algebraMap A B) ^ k := by
  rw [smul_top_pow_eq_restrictScalars I B k, Submodule.restrictScalars_mem, Ideal.smul_eq_mul,
    Ideal.mul_top]

/-- The kernel of a transition map of a system is `I ^ (n + 1)` times its source. -/
private theorem ker_transitionLinear (n : ℕ) :
    LinearMap.ker (X.transitionLinear n) = I ^ (n + 1) • (⊤ : Submodule A (X.B (n + 1))) := by
  ext x
  rw [LinearMap.mem_ker, mem_smul_top_pow_iff, algebraMap_B, ← Ideal.map_pow]
  change X.transition n x = 0 ↔ _
  rw [← RingHom.mem_ker, X.transition_ker n]
  exact Iff.rfl

/-- The shifted system, as an inverse system in the sense of [StacksProject 09B8]. -/
private def shiftSystem : Stacks.AdicCompletion.InverseLimit.InverseSystem I where
  M := X.shiftType
  π := X.shiftπ
  surjective n := by
    cases n with
    | zero => exact fun y => ⟨0, X.shiftType_zero_eq _ _⟩
    | succ n => exact X.transition_surjective n
  ker_π n := by
    cases n with
    | zero =>
      rw [pow_zero, one_smul]
      exact Submodule.eq_top_iff'.2 fun x => X.shiftType_zero_eq _ _
    | succ n => exact X.ker_transitionLinear n

/-! ### The comparison of the two limits -/

/-- The compatible family of the shifted system attached to an element of the limit. -/
private def shiftUp (f : X.limitCarrier) : ∀ n, X.shiftType n
  | 0 => 0
  | n + 1 => X.limitVal f n

/-- The limit of a system is linearly equivalent to the limit of its shift: a compatible family
for the shifted system is one for the original, extended by zero at level `0`. -/
private def shiftEquiv : X.limitCarrier ≃ₗ[A] X.shiftSystem.limit where
  toFun f := ⟨X.shiftUp f, by
    intro n
    cases n with
    | zero => exact X.shiftType_zero_eq _ _
    | succ n => exact X.transition_limitVal f n⟩
  map_add' f g := by
    refine Subtype.ext (funext fun n => ?_)
    cases n with
    | zero => exact X.shiftType_zero_eq _ _
    | succ n => rfl
  map_smul' a f := by
    refine Subtype.ext (funext fun n => ?_)
    cases n with
    | zero => exact X.shiftType_zero_eq _ _
    | succ n => rfl
  invFun g := ⟨fun n => g.1 (n + 1), fun n => g.2 (n + 1)⟩
  left_inv f := by ext n; rfl
  right_inv g := by
    refine Subtype.ext (funext fun n => ?_)
    cases n with
    | zero => exact X.shiftType_zero_eq _ _
    | succ n => rfl

/-- Membership in `Iᵏ • ⊤` is invariant under a linear equivalence. -/
private theorem mem_smul_top_iff_of_linearEquiv {M N : Type*} [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module A N] (e : M ≃ₗ[A] N) (k : ℕ) (x : M) :
    e x ∈ I ^ k • (⊤ : Submodule A N) ↔ x ∈ I ^ k • (⊤ : Submodule A M) := by
  have hmap : (I ^ k • (⊤ : Submodule A M)).map (e : M →ₗ[A] N) =
      I ^ k • (⊤ : Submodule A N) := by
    rw [Submodule.map_smul'', Submodule.map_top, LinearEquiv.range]
  rw [← hmap, Submodule.mem_map_equiv, LinearEquiv.symm_apply_apply]

/-- The projection of the shifted limit at level `n + 1` is the `n`-th component. -/
private theorem proj_shiftEquiv (f : X.limitCarrier) (n : ℕ) :
    X.shiftSystem.proj (n + 1) (X.shiftEquiv f) = X.limitVal f n := rfl

/-! ### The limit is an object of the category of complete algebras -/

/-- The projections from the limit of a system are surjective; this is Mittag-Leffler. -/
public theorem limitProj_surjective (n : ℕ) : Function.Surjective (X.limitProj n) := by
  intro y
  obtain ⟨g, hg⟩ := X.shiftSystem.proj_surjective (n + 1) (show X.shiftType (n + 1) from y)
  refine ⟨X.shiftEquiv.symm g, ?_⟩
  rw [limitProj_apply, ← X.proj_shiftEquiv, LinearEquiv.apply_symm_apply]
  exact hg

/-- **Stacks 09B8** for a system of algebras: the kernel of the projection `lim Bₙ → Bₙ` is
`Iⁿ⁺¹ lim Bₙ`, so that the system is recovered from its limit. -/
public theorem ker_limitProj (hI : I.FG) (n : ℕ) :
    RingHom.ker (X.limitProj n) = (I.map (Algebra.algebraMap A X.limitCarrier)) ^ (n + 1) := by
  ext x
  rw [RingHom.mem_ker, limitProj_apply, ← mem_smul_top_pow_iff (A := A),
    ← mem_smul_top_iff_of_linearEquiv X.shiftEquiv, ← X.shiftSystem.ker_proj hI (n + 1),
    LinearMap.mem_ker]
  exact Iff.rfl

/-- Adic completeness transfers along a linear equivalence. -/
private theorem isAdicComplete_of_linearEquiv {M N : Type v} [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module A N] (e : M ≃ₗ[A] N) (h : IsAdicComplete I N) :
    IsAdicComplete I M := by
  have hmem := mem_smul_top_iff_of_linearEquiv (I := I) e
  have hh : IsHausdorff I M := ⟨fun x hx => by
    refine e.injective ?_
    rw [map_zero]
    refine h.toIsHausdorff.haus (e x) fun k => ?_
    rw [SModEq.zero]
    exact (hmem k x).2 (SModEq.zero.1 (hx k))⟩
  have hp : IsPrecomplete I M := ⟨fun f hf => by
    obtain ⟨L, hL⟩ := h.toIsPrecomplete.prec (f := fun n => e (f n)) fun {m n} hmn => by
      rw [SModEq.sub_mem, ← map_sub]
      exact (hmem m _).2 (SModEq.sub_mem.1 (hf hmn))
    refine ⟨e.symm L, fun n => ?_⟩
    rw [SModEq.sub_mem]
    refine (hmem n _).1 ?_
    rw [map_sub, LinearEquiv.apply_symm_apply, ← SModEq.sub_mem]
    exact hL n⟩
  exact { toIsHausdorff := hh, toIsPrecomplete := hp }

/-- **Stacks 09B8** for a system of algebras: the limit of a system is `I`-adically complete. -/
public theorem limit_isAdicComplete (hI : I.FG) :
    IsAdicComplete (I.map (Algebra.algebraMap A X.limitCarrier)) X.limitCarrier :=
  (IsAdicComplete.map_algebraMap_iff (S := X.limitCarrier) I X.limitCarrier).mpr
    (isAdicComplete_of_linearEquiv X.shiftEquiv (X.shiftSystem.isAdicComplete hI))

/-- The reduction of the limit of a system modulo `I` is its first term. -/
public noncomputable def limitReductionEquiv (hI : I.FG) :
    X.limitCarrier ⧸ I.map (Algebra.algebraMap A X.limitCarrier) ≃+* X.B 0 :=
  (Ideal.quotEquivOfEq (by rw [X.ker_limitProj hI 0, pow_one])).trans
    (RingHom.quotientKerEquivOfSurjective (X.limitProj_surjective 0))

/-- The reduction isomorphism of the limit sends a residue class to a zeroth component. -/
public theorem limitReductionEquiv_mk (hI : I.FG) (x : X.limitCarrier) :
    X.limitReductionEquiv hI (Ideal.Quotient.mk _ x) = X.limitVal x 0 := rfl

/-- The reduction of the limit of a system is of finite type over `A ⧸ I`, being its first
term. -/
public theorem limit_finiteType (hI : I.FG) :
    Algebra.FiniteType (A ⧸ I)
      (X.limitCarrier ⧸ I.map (Algebra.algebraMap A X.limitCarrier)) := by
  set e := X.limitReductionEquiv hI
  set q := Ideal.quotEquivOfEq (pow_one I)
  have hcomp : (e.symm.toRingHom.comp ((X.algebraMap 0).comp q.symm.toRingHom)).FiniteType :=
    (RingHom.FiniteType.of_surjective _ e.symm.surjective).comp
      ((X.finiteType 0).comp (RingHom.FiniteType.of_surjective _ q.symm.surjective))
  have heq : Algebra.algebraMap (A ⧸ I)
      (X.limitCarrier ⧸ I.map (Algebra.algebraMap A X.limitCarrier)) =
      e.symm.toRingHom.comp ((X.algebraMap 0).comp q.symm.toRingHom) := by
    refine Ideal.Quotient.ringHom_ext (RingHom.ext fun a => e.injective ?_)
    rw [RingHom.comp_apply, RingHom.comp_apply, RingHom.comp_apply, RingHom.comp_apply,
      RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, RingEquiv.apply_symm_apply]
    exact X.limitReductionEquiv_mk hI _
  exact RingHom.finiteType_algebraMap.mp (heq ▸ hcomp)

/-- The limit of a system, as an object of the category of `I`-adically complete `A`-algebras
of finite type modulo `I`. -/
public noncomputable def limitObj (hI : I.FG) : AdicFiniteTypeAlgebra.{u, v} A I :=
  ⟨CommAlgCat.of A X.limitCarrier, X.limit_isAdicComplete hI, X.limit_finiteType hI⟩

/-- The carrier of the limit object is the limit. -/
@[simp] public theorem limitObj_carrier (hI : I.FG) :
    (X.limitObj hI).carrier = X.limitCarrier := rfl

/-! ### Functoriality of the limit -/

section Map

variable {X Y : AdicAlgebraSystem.{u, v} A I}

/-- Two morphisms of systems with the same components are equal. -/
public theorem hom_ext {f g : AdicAlgebraSystem.Hom X Y} (h : ∀ n, f.app n = g.app n) : f = g := by
  cases f
  cases g
  simp only [Hom.mk.injEq]
  exact funext h

/-- A morphism of systems commutes with the structure maps from `A`. -/
public theorem Hom.app_baseMap (f : AdicAlgebraSystem.Hom X Y) (n : ℕ) (a : A) :
    f.app n (X.baseMap n a) = Y.baseMap n a :=
  DFunLike.congr_fun (f.commutes_algebraMap n) (Ideal.Quotient.mk (I ^ (n + 1)) a)

/-- The map of limits induced by a morphism of systems. -/
public def limitMap (f : AdicAlgebraSystem.Hom X Y) : X.limitCarrier →+* Y.limitCarrier where
  toFun g := ⟨fun n => f.app n (X.limitVal g n), fun n => by
    have h := DFunLike.congr_fun (f.naturality n) (X.limitVal g (n + 1))
    simp only [RingHom.comp_apply] at h
    rw [h, X.transition_limitVal]⟩
  map_one' := Subtype.ext (funext fun n => map_one (f.app n))
  map_mul' _ _ := Subtype.ext (funext fun n => map_mul (f.app n) _ _)
  map_zero' := Subtype.ext (funext fun n => map_zero (f.app n))
  map_add' _ _ := Subtype.ext (funext fun n => map_add (f.app n) _ _)

/-- The components of the image of an element of the limit under an induced map. -/
@[simp] public theorem limitVal_limitMap (f : AdicAlgebraSystem.Hom X Y) (g : X.limitCarrier)
    (n : ℕ) : Y.limitVal (limitMap f g) n = f.app n (X.limitVal g n) := rfl

/-- The map of limits induced by a morphism of systems, as a map of `A`-algebras. -/
public def limitAlgHom (f : AdicAlgebraSystem.Hom X Y) : X.limitCarrier →ₐ[A] Y.limitCarrier :=
  { limitMap f with
    commutes' := fun a => Y.limit_ext fun n => by
      change Y.limitVal (limitMap f (Algebra.algebraMap A X.limitCarrier a)) n =
        Y.limitVal (Algebra.algebraMap A Y.limitCarrier a) n
      rw [limitVal_limitMap, limitVal_algebraMap, limitVal_algebraMap, f.app_baseMap] }

end Map

/-! ### Isomorphisms of systems -/

/-- An isomorphism of systems built from a compatible family of isomorphisms of their terms. -/
public def isoOfRingEquiv {X Y : AdicAlgebraSystem.{u, v} A I} (e : ∀ n, X.B n ≃+* Y.B n)
    (he : ∀ n, (e n).toRingHom.comp (X.algebraMap n) = Y.algebraMap n)
    (hn : ∀ n, (Y.transition n).comp (e (n + 1)).toRingHom =
      (e n).toRingHom.comp (X.transition n)) : X ≅ Y where
  hom := { app := fun n => (e n).toRingHom, commutes_algebraMap := he, naturality := hn }
  inv :=
    { app := fun n => (e n).symm.toRingHom
      commutes_algebraMap := fun n => RingHom.ext fun y => (e n).injective (by
        rw [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
          RingEquiv.apply_symm_apply]
        exact (DFunLike.congr_fun (he n) y).symm)
      naturality := fun n => RingHom.ext fun y => (e n).injective (by
        have h := DFunLike.congr_fun (hn n) ((e (n + 1)).symm y)
        simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
          RingEquiv.apply_symm_apply] at h ⊢
        rw [h]) }
  hom_inv_id := hom_ext fun n => RingHom.ext fun y => by
    change (e n).symm ((e n) y) = y
    exact (e n).symm_apply_apply y
  inv_hom_id := hom_ext fun n => RingHom.ext fun y => by
    change (e n) ((e n).symm y) = y
    exact (e n).apply_symm_apply y

/-- The comparison between the quotients of the limit of a system and the terms of the
system. -/
public noncomputable def limitQuotientEquiv (hI : I.FG) (n : ℕ) :
    X.limitCarrier ⧸ (I.map (Algebra.algebraMap A X.limitCarrier)) ^ (n + 1) ≃+* X.B n :=
  (Ideal.quotEquivOfEq (X.ker_limitProj hI n).symm).trans
    (RingHom.quotientKerEquivOfSurjective (X.limitProj_surjective n))

/-- The comparison isomorphism sends a residue class to the corresponding component. -/
@[simp] public theorem limitQuotientEquiv_mk (hI : I.FG) (n : ℕ) (x : X.limitCarrier) :
    X.limitQuotientEquiv hI n (Ideal.Quotient.mk _ x) = X.limitVal x n := rfl

end AdicAlgebraSystem

/-! ### The limit functor -/

section Functor

variable (A : Type u) [CommRing A] (I : Ideal A)

/-- **Stacks 0AJP**, the functor `(Bₙ) ↦ lim Bₙ`: a system of finite type algebras over the
quotients `A ⧸ Iⁿ` goes to the limit of its terms, an adically complete algebra of finite type
modulo `I`. -/
public noncomputable def adicLimitFunctor (hI : I.FG) :
    AdicAlgebraSystem.{u, v} A I ⥤ AdicFiniteTypeAlgebra.{u, v} A I where
  obj X := X.limitObj hI
  map f := AdicFiniteTypeAlgebra.homMk (AdicAlgebraSystem.limitAlgHom f)
  map_id X := by
    apply ObjectProperty.hom_ext
    apply CommAlgCat.hom_ext
    exact AlgHom.ext fun g => X.limit_ext fun n => rfl
  map_comp f g := by
    apply ObjectProperty.hom_ext
    apply CommAlgCat.hom_ext
    exact AlgHom.ext fun x => AdicAlgebraSystem.limit_ext _ fun n => rfl

end Functor

/-! ### The quotients of a complete algebra recover it -/

namespace AdicFiniteTypeAlgebra

section Unit

variable {A : Type u} [CommRing A] {I : Ideal A} (B : AdicFiniteTypeAlgebra.{u, v} A I)

/-- The canonical map from an adically complete algebra to the limit of its adic quotients. -/
public noncomputable def toLimitQuotients :
    B.carrier →ₐ[A] ((adicQuotientFunctor A I).obj B).limitCarrier where
  toFun b := ⟨fun _ => Ideal.Quotient.mk _ b, fun _ => rfl⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

/-- The components of the canonical map to the limit of the adic quotients. -/
@[simp] public theorem limitVal_toLimitQuotients (b : B.carrier) (n : ℕ) :
    ((adicQuotientFunctor A I).obj B).limitVal (B.toLimitQuotients b) n =
      Ideal.Quotient.mk (B.adicIdeal ^ (n + 1)) b := rfl

/-- The canonical map to the limit of the adic quotients is injective, since an element lying
in every power of `IB` vanishes. -/
public theorem toLimitQuotients_injective : Function.Injective B.toLimitQuotients := by
  intro b c hbc
  have hb : ∀ n, Ideal.Quotient.mk (B.adicIdeal ^ (n + 1)) b
      = Ideal.Quotient.mk (B.adicIdeal ^ (n + 1)) c := fun n =>
    congrArg (fun z => ((adicQuotientFunctor A I).obj B).limitVal z n) hbc
  have hsub : ∀ n, b - c ∈ B.adicIdeal ^ (n + 1) := fun n => by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, hb n, sub_self]
  refine sub_eq_zero.mp (B.isAdicallyComplete.toIsHausdorff.haus (b - c) fun k => ?_)
  rw [SModEq.zero, Ideal.smul_eq_mul, Ideal.mul_top]
  cases k with
  | zero => simp
  | succ m => exact hsub m

/-- The canonical map to the limit of the adic quotients is surjective: a compatible family of
residue classes is a Cauchy sequence, and the algebra is precomplete. -/
public theorem toLimitQuotients_surjective : Function.Surjective B.toLimitQuotients := by
  intro g
  have hex : ∀ n, ∃ x : B.carrier, Ideal.Quotient.mk (B.adicIdeal ^ (n + 1)) x =
      ((adicQuotientFunctor A I).obj B).limitVal g n := fun n => Ideal.Quotient.mk_surjective _
  choose b hb using hex
  have hadj : ∀ n, b (n + 1) - b n ∈ B.adicIdeal ^ (n + 1) := by
    intro n
    have h := ((adicQuotientFunctor A I).obj B).transition_limitVal g n
    rw [← hb (n + 1), ← hb n] at h
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, sub_eq_zero]
    exact h
  have hstep : ∀ i j, i ≤ j → b j - b i ∈ B.adicIdeal ^ (i + 1) := by
    intro i j hij
    induction j, hij using Nat.le_induction with
    | base => simp
    | succ j hij ih =>
      have h1 : b (j + 1) - b j ∈ B.adicIdeal ^ (i + 1) :=
        Ideal.pow_le_pow_right (by omega) (hadj j)
      have h2 : b (j + 1) - b i = (b (j + 1) - b j) + (b j - b i) := by ring
      rw [h2]
      exact Submodule.add_mem _ h1 ih
  have hcauchy : ∀ {m n : ℕ}, m ≤ n → (fun k => Nat.casesOn k 0 b) m ≡
      (fun k => Nat.casesOn k 0 b) n
        [SMOD (B.adicIdeal ^ m • (⊤ : Submodule B.carrier B.carrier))] := by
    intro m n hmn
    rw [SModEq.sub_mem, Ideal.smul_eq_mul, Ideal.mul_top]
    match m, n, hmn with
    | 0, _, _ => simp
    | i + 1, j + 1, hmn =>
      have h : b i - b j = -(b j - b i) := by ring
      change b i - b j ∈ B.adicIdeal ^ (i + 1)
      rw [h]
      exact neg_mem (hstep i j (by omega))
  obtain ⟨L, hL⟩ := B.isAdicallyComplete.toIsPrecomplete.prec hcauchy
  refine ⟨L, ((adicQuotientFunctor A I).obj B).limit_ext fun n => ?_⟩
  have hLn := hL (n + 1)
  rw [SModEq.sub_mem, Ideal.smul_eq_mul, Ideal.mul_top] at hLn
  change Ideal.Quotient.mk (B.adicIdeal ^ (n + 1)) L =
    ((adicQuotientFunctor A I).obj B).limitVal g n
  rw [← hb n, eq_comm, ← sub_eq_zero, ← map_sub, Ideal.Quotient.eq_zero_iff_mem]
  exact hLn

/-- **Stacks 0AJP**: an adically complete algebra is the limit of its system of adic
quotients. -/
public noncomputable def toLimitQuotientsEquiv :
    B.carrier ≃ₐ[A] ((adicQuotientFunctor A I).obj B).limitCarrier :=
  AlgEquiv.ofBijective B.toLimitQuotients
    ⟨toLimitQuotients_injective B, toLimitQuotients_surjective B⟩

end Unit

end AdicFiniteTypeAlgebra

/-! ### The equivalence of the two categories -/

section Equivalence

variable (A : Type u) [CommRing A] (I : Ideal A)

/-- The unit of the equivalence: an adically complete algebra is the limit of its adic
quotients. -/
public noncomputable def adicQuotientLimitUnitIso (hI : I.FG) :
    𝟭 (AdicFiniteTypeAlgebra.{u, v} A I) ≅
      adicQuotientFunctor A I ⋙ adicLimitFunctor A I hI :=
  NatIso.ofComponents
    (fun B => ObjectProperty.isoMk _ (CommAlgCat.isoMk B.toLimitQuotientsEquiv))
    fun f => by
      apply ObjectProperty.hom_ext
      apply CommAlgCat.hom_ext
      exact AlgHom.ext fun x => AdicAlgebraSystem.limit_ext _ fun n => rfl

/-- The counit of the equivalence: the adic quotients of the limit of a system are the terms of
the system. -/
public noncomputable def adicQuotientLimitCounitIso (hI : I.FG) :
    adicLimitFunctor A I hI ⋙ adicQuotientFunctor A I ≅
      𝟭 (AdicAlgebraSystem.{u, v} A I) :=
  NatIso.ofComponents
    (fun X => AdicAlgebraSystem.isoOfRingEquiv (fun n => X.limitQuotientEquiv hI n)
      (fun _ => Ideal.Quotient.ringHom_ext (RingHom.ext fun _ => rfl))
      fun n => Ideal.Quotient.ringHom_ext (RingHom.ext fun x => X.transition_limitVal x n))
    fun _ => AdicAlgebraSystem.hom_ext fun _ =>
      Ideal.Quotient.ringHom_ext (RingHom.ext fun _ => rfl)

/-- **Stacks Project, Tag 0AJP.** The functor `(Bₙ) ↦ lim Bₙ` from systems of finite type
algebras over the quotients `A ⧸ Iⁿ` to adically complete algebras of finite type modulo `I` is
quasi-inverse to the functor `B ↦ (B ⧸ Iⁿ⁺¹B)` of [StacksProject 0AJN]: the two categories are
equivalent. -/
@[stacks 0AJP "the functor (Bₙ) ↦ lim Bₙ is a quasi-inverse of the functor of 0AJN, so the \
two categories are equivalent"]
public noncomputable def adicQuotientEquivalence (hI : I.FG) :
    AdicFiniteTypeAlgebra.{u, v} A I ≌ AdicAlgebraSystem.{u, v} A I :=
  CategoryTheory.Equivalence.mk (adicQuotientFunctor A I) (adicLimitFunctor A I hI)
    (adicQuotientLimitUnitIso A I hI) (adicQuotientLimitCounitIso A I hI)

/-- The equivalence of [StacksProject 0AJP] is given by the functor of [StacksProject 0AJN]. -/
@[simp] public theorem adicQuotientEquivalence_functor (hI : I.FG) :
    (adicQuotientEquivalence A I hI).functor = adicQuotientFunctor A I := rfl

/-- The quasi-inverse in the equivalence of [StacksProject 0AJP] is the limit functor. -/
@[simp] public theorem adicQuotientEquivalence_inverse (hI : I.FG) :
    (adicQuotientEquivalence A I hI).inverse = adicLimitFunctor A I hI := rfl

end Equivalence

end Rig
