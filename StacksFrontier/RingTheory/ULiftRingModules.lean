module

public import Mathlib.LinearAlgebra.TensorProduct.Quotient
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.RingTheory.Finiteness.Basic
public import Mathlib.RingTheory.Flat.Stability
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.Noetherian.Basic

/-!
# Carrying a ring and its modules up a universe

A statement quantified over rings in `Type u` is instantiated at a ring of `Type 0` by replacing
the ring with its `ULift`. Mathlib supplies the algebraic structure of `ULift R` and the module
structures `Module (ULift R) M` and `Module R (ULift M)`, but not the ring-theoretic predicates
and not the comparison of a base change over `ULift R` with the one over `R`. This file supplies
them, in the generality the instantiation needs: Noetherianness, finiteness, flatness in both
directions, surjectivity and kernels of structure maps, the ideal dictionary, the bijectivity of
`R/I → S/IS`, localizations, and the base-change comparison.

## Main results

* `Stacks.ULiftTransport.tensorBaseCongr`: **the base of a base change may be replaced by an
  isomorphic ring.** For a ring isomorphism `γ : T ≃+* T'`, a `T'`-algebra `C` and a module `X`
  carrying compatible `T`- and `T'`-actions, `C ⊗[T'] X ≃ₗ[C] C ⊗[T] X`. Taking `γ` to be
  `R ≃+* ULift R` this moves a base change from `ULift R` to `R`, where the `Type 0` facts live.
* `Stacks.ULiftTransport.tensorUliftCongr` and
  `Stacks.ULiftTransport.tensorUliftCongrOfRingEquiv`: an identification of two base changes
  carried up a universe, the second with the upper base rings replaced by isomorphic ones.
* `Stacks.ULiftTransport.flat_ulift`, `Stacks.ULiftTransport.flat_of_ulift_left`: flatness goes up
  along `ULift` on both arguments, and comes back down on the base.
* `Stacks.ULiftTransport.isScalarTower_ulift`: a tower of rings stays a tower.
* `Stacks.ULiftTransport.bijective_quotientMap_ulift`: `R/I = S/IS` is inherited by the `ULift`s.
* `Stacks.ULiftTransport.isLocalization_away_ulift`: `ULift (R_g)` is the localization of
  `ULift R` away from `ULift.up g`.
* `Stacks.ULiftTransport.eq_smul_of_tmul_eq_zero`: `1 ⊗ y = 0` in `P ⊗[P'] N` forces `y` into
  the kernel of `P' → P` times `N`, for any surjection `P' → P` with principal kernel.

## Implementation notes

`ULift.algebra' : Algebra (ULift R) A` is not a global instance in Mathlib, because for
`A = ULift R` it creates a non-reducible diamond. Making it one locally is also wrong here, for a
reason worth recording: it applies to `Algebra (ULift R) X` for *every* `R`-algebra `X`, so it
takes over the structure map of `Localization.Away g` for `g : ULift R` — and then
`IsLocalization.Away g (Localization.Away g)` is no longer an instance, because the localization's
own structure map is the one that statement is about. What is declared instead is
`Stacks.ULiftTransport.uliftAlgebra`, whose conclusion `Algebra (ULift R) (ULift S)` matches only
a pair of `ULift`s. Naming it also pins the term down, which matters: a goal mentioning
`Ideal.map (algebraMap (ULift R) (ULift S))` is only rewritable by a lemma that mentions the same
instance, and two files searching for it independently need not compose `ULift.algebra'` with
`ULift.algebra` the same way round. Its `Algebra.toModule` is *syntactically* the
`Module (ULift R) (ULift S)` that instance search finds on its own, so no diamond arises there.

`tensorBaseCongr` takes both module structures on `X` and both algebra structures on `C` as
hypotheses, together with the equations relating them, rather than building one of them from the
other with a `letI` inside its statement. That is deliberate: at a use site the two structures are
already fixed — one by the statement being instantiated, the other by `ULift`'s own instances —
and a `letI` in the statement would force the caller to produce that exact term.
-/

@[expose] public noncomputable section

open scoped TensorProduct

universe u v w

namespace Stacks.ULiftTransport

/-- **`ULift S` as a `ULift R`-algebra**, through `ULift.ringEquiv` on both sides. -/
instance uliftAlgebra {R S : Type} [CommRing R] [CommRing S] [Algebra R S] :
    Algebra (ULift.{u} R) (ULift.{u} S) :=
  ULift.algebra' (R := R) (ULift.{u} S)

section Basic

variable (R S : Type) [CommRing R] [CommRing S] [Algebra R S]

/-- The structure map of `ULift S` over `ULift R` is the structure map of `S` over `R`, up and
down again. -/
theorem algebraMap_ulift_apply (x : ULift.{u} R) :
    algebraMap (ULift.{u} R) (ULift.{u} S) x = ULift.up (algebraMap R S x.down) := rfl

/-- The structure map of `ULift R` over `R` is `ULift.up`. -/
theorem algebraMap_self_ulift (x : R) : algebraMap R (ULift.{u} R) x = ULift.up x := rfl

/-- A scalar tower of rings stays a scalar tower after `ULift`. -/
theorem isScalarTower_ulift (T : Type) [CommRing T] [Algebra R T] [Algebra S T]
    [IsScalarTower R S T] :
    IsScalarTower (ULift.{u} R) (ULift.{u} S) (ULift.{u} T) :=
  IsScalarTower.of_algebraMap_eq fun x => by
    rw [algebraMap_ulift_apply, algebraMap_ulift_apply, algebraMap_ulift_apply,
      IsScalarTower.algebraMap_apply R S T]

/-- `ULift` of a Noetherian ring is Noetherian. -/
theorem isNoetherianRing_ulift [IsNoetherianRing R] : IsNoetherianRing (ULift.{u} R) :=
  isNoetherianRing_of_ringEquiv R ULift.ringEquiv.symm

end Basic

section Modules

variable {R M : Type} [CommRing R] [AddCommGroup M] [Module R M]

/-- `ULift` of a finite module is finite over `ULift` of the base. The finiteness is an explicit
argument, not an instance: on the concrete rings of a counterexample the search for `Module R M`
is expensive, and passing the fact fixes the instance by unification instead. -/
theorem finite_ulift (h : Module.Finite R M) : Module.Finite (ULift.{u} R) (ULift.{u} M) :=
  have := h
  have := Module.Finite.ulift (R := R) (M := M)
  Module.Finite.of_restrictScalars_finite R (ULift.{u} R) (ULift.{u} M)

/-- `ULift` of a flat module is flat over `ULift` of the base. The flatness is an explicit
argument for the reason `Stacks.ULiftTransport.finite_ulift` records. -/
theorem flat_ulift (h : Module.Flat R M) : Module.Flat (ULift.{u} R) (ULift.{u} M) :=
  Module.Flat.ulift_left_iff.2 (Module.Flat.ulift_right_iff.2 h)

end Modules

section Surj

variable (R S : Type) [CommRing R] [CommRing S] [Algebra R S]

/-- A surjective structure map stays surjective after `ULift`. -/
theorem surjective_algebraMap_ulift (h : Function.Surjective (algebraMap R S)) :
    Function.Surjective (algebraMap (ULift.{u} R) (ULift.{u} S)) := by
  intro y
  obtain ⟨x, hx⟩ := h y.down
  exact ⟨ULift.up x, by rw [algebraMap_ulift_apply]; exact ULift.ext hx⟩

end Surj

section Ideals

variable (R S : Type) [CommRing R] [CommRing S] [Algebra R S]

/-- The ideal dictionary: an element of `ULift R` lies in the ideal generated by `I` exactly when
it comes from `I`. -/
theorem mem_map_self_ulift (I : Ideal R) (x : ULift.{u} R) :
    x ∈ I.map (algebraMap R (ULift.{u} R)) ↔ x.down ∈ I := by
  constructor
  · intro hx
    have hle : I.map (algebraMap R (ULift.{u} R)) ≤
        I.comap (ULift.ringEquiv.toRingHom : ULift.{u} R →+* R) := by
      rw [Ideal.map_le_iff_le_comap]
      exact fun y hy => hy
    exact hle hx
  · exact fun hx => Ideal.mem_map_of_mem _ hx

/-- The kernel of a structure map is the ideal generated by the kernel downstairs. -/
theorem ker_algebraMap_ulift :
    RingHom.ker (algebraMap (ULift.{u} R) (ULift.{u} S)) =
      (RingHom.ker (algebraMap R S)).map (algebraMap R (ULift.{u} R)) := by
  ext x
  rw [RingHom.mem_ker, mem_map_self_ulift R, RingHom.mem_ker, algebraMap_ulift_apply]
  exact ⟨fun h => congrArg ULift.down h, fun h => ULift.ext h⟩

/-- Extending an ideal to `ULift R` and then pushing it to `ULift S` is pushing it to `S` and then
extending. -/
theorem map_map_self_ulift (I : Ideal R) :
    (I.map (algebraMap R (ULift.{u} R))).map (algebraMap (ULift.{u} R) (ULift.{u} S))
      = (I.map (algebraMap R S)).map (algebraMap S (ULift.{u} S)) := by
  rw [Ideal.map_map, Ideal.map_map]
  exact congrArg (fun f => Ideal.map f I) (RingHom.ext fun x => rfl)

/-- A nilpotent ideal stays nilpotent in `ULift R`. -/
theorem isNilpotent_map_self_ulift {I : Ideal R} (h : IsNilpotent I) :
    IsNilpotent (I.map (algebraMap R (ULift.{u} R))) := by
  obtain ⟨n, hn⟩ := h
  refine ⟨n, ?_⟩
  rw [← Ideal.map_pow, hn]
  simp

/-- **`R/I = S/IS` is inherited by the `ULift`s.** -/
theorem bijective_quotientMap_ulift (I : Ideal R)
    (h : Function.Bijective (Ideal.quotientMap (I.map (algebraMap R S)) (algebraMap R S)
      Ideal.le_comap_map)) :
    Function.Bijective (Ideal.quotientMap
      ((I.map (algebraMap R (ULift.{u} R))).map (algebraMap (ULift.{u} R) (ULift.{u} S)))
      (algebraMap (ULift.{u} R) (ULift.{u} S)) Ideal.le_comap_map) := by
  have hmem : ∀ y : ULift.{u} S,
      y ∈ (I.map (algebraMap R (ULift.{u} R))).map (algebraMap (ULift.{u} R) (ULift.{u} S)) ↔
        y.down ∈ I.map (algebraMap R S) := by
    intro y
    rw [map_map_self_ulift R S I]
    exact mem_map_self_ulift S _ y
  constructor
  · refine Ideal.quotientMap_injective' ?_
    intro x hx
    rw [Ideal.mem_comap, hmem, algebraMap_ulift_apply] at hx
    rw [mem_map_self_ulift R]
    have hz : Ideal.Quotient.mk (I.map (algebraMap R S)) (algebraMap R S x.down) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.2 hx
    have h0 := h.1 (a₁ := Ideal.Quotient.mk I x.down) (a₂ := 0) (by
      rw [Ideal.quotientMap_mk, map_zero, hz])
    exact Ideal.Quotient.eq_zero_iff_mem.1 h0
  · intro y
    obtain ⟨q, rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨pb, hpb⟩ := h.2 (Ideal.Quotient.mk (I.map (algebraMap R S)) q.down)
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective pb
    refine ⟨Ideal.Quotient.mk _ (ULift.up.{u} p), ?_⟩
    rw [Ideal.quotientMap_mk, Ideal.Quotient.eq, hmem]
    rw [Ideal.quotientMap_mk, Ideal.Quotient.eq] at hpb
    simpa [algebraMap_ulift_apply] using hpb

end Ideals

section TensorBase

variable {T T' : Type*} [CommRing T] [CommRing T'] {C : Type*} [CommRing C]
  [Algebra T C] [Algebra T' C] {X : Type*} [AddCommGroup X] [Module T X] [Module T' X]
  (γ : T ≃+* T') (hC : ∀ t : T, algebraMap T C t = algebraMap T' C (γ t))
  (hX : ∀ (t : T) (x : X), t • x = (γ t) • x)

include hC in
/-- The two actions of the isomorphic base rings on `C` agree. -/
theorem smul_eq_ringEquiv (t : T) (c : C) : t • c = (γ t) • c := by
  rw [Algebra.smul_def, Algebra.smul_def, hC]

include hC in
/-- Scalars from the two isomorphic base rings commute on `C`. -/
theorem smulCommClass_ringEquiv : SMulCommClass T T' C :=
  ⟨fun t t' c => by
    rw [smul_eq_ringEquiv γ hC t (t' • c), smul_eq_ringEquiv γ hC t c, smul_comm (γ t) t' c]⟩

include hC hX in
/-- A `T'`-scalar may be moved across `⊗[T]`. -/
theorem compatibleSMul_ringEquiv : TensorProduct.CompatibleSMul T T' C X :=
  ⟨fun a m n => by
    obtain ⟨t, rfl⟩ : ∃ t, γ t = a := ⟨γ.symm a, γ.apply_symm_apply a⟩
    rw [← smul_eq_ringEquiv γ hC t m, ← hX t n]
    exact TensorProduct.smul_tmul t m n⟩

include hC hX in
/-- A `T`-scalar may be moved across `⊗[T']`. -/
theorem compatibleSMul_ringEquiv' : TensorProduct.CompatibleSMul T' T C X :=
  ⟨fun t m n => by
    rw [smul_eq_ringEquiv γ hC t m, hX t n]
    exact TensorProduct.smul_tmul (γ t) m n⟩

/-- **The base of a base change may be replaced by an isomorphic ring.** -/
def tensorBaseCongr : (C ⊗[T'] X) ≃ₗ[C] (C ⊗[T] X) :=
  letI := smulCommClass_ringEquiv γ hC (C := C)
  letI := compatibleSMul_ringEquiv γ hC hX
  letI := compatibleSMul_ringEquiv' γ hC hX
  TensorProduct.equivOfCompatibleSMul T T' C C X

/-- `tensorBaseCongr` sends `c ⊗ₜ[T'] x` to `c ⊗ₜ[T] x`. -/
@[simp]
theorem tensorBaseCongr_tmul (c : C) (x : X) :
    tensorBaseCongr γ hC hX (c ⊗ₜ[T'] x) = c ⊗ₜ[T] x := rfl

/-- The inverse of `tensorBaseCongr` sends `c ⊗ₜ[T] x` to `c ⊗ₜ[T'] x`. -/
@[simp]
theorem tensorBaseCongr_symm_tmul (c : C) (x : X) :
    (tensorBaseCongr γ hC hX).symm (c ⊗ₜ[T] x) = c ⊗ₜ[T'] x := rfl

end TensorBase

section Chain

open TensorProduct.AlgebraTensorModule

variable {R₀ T₁ T₂ : Type} [CommRing R₀] [CommRing T₁] [CommRing T₂] [Algebra T₁ T₂]
  [Algebra R₀ T₂] {X : Type} [AddCommGroup X] [Module T₁ X]
  {Y : Type} [AddCommGroup Y] [Module R₀ Y]

/-- **An identification of two base changes, carried up a universe.** The route is through
`T₂ → ULift T₂`: `AlgebraTensorModule.cancelBaseChange` turns a base change over `ULift T₂` into
one over `T₂`, where the given equivalence lives, and `tensorBaseCongr` moves the base from
`ULift T₁` to `T₁` and back from `R₀` to `ULift R₀`. -/
def tensorUliftCongr (E : (T₂ ⊗[T₁] X) ≃ₗ[T₂] (T₂ ⊗[R₀] Y)) :
    (ULift.{u} T₂ ⊗[ULift.{u} T₁] ULift.{u} X) ≃ₗ[ULift.{u} T₂]
      (ULift.{u} T₂ ⊗[ULift.{u} R₀] ULift.{u} Y) :=
  (tensorBaseCongr (ULift.ringEquiv.symm : T₁ ≃+* ULift.{u} T₁)
      (fun _ => rfl) (fun _ _ => rfl)).trans
    ((congr (LinearEquiv.refl (ULift.{u} T₂) (ULift.{u} T₂))
        (ULift.moduleEquiv : ULift.{u} X ≃ₗ[T₁] X)).trans
      ((cancelBaseChange T₁ T₂ (ULift.{u} T₂) (ULift.{u} T₂) X).symm.trans
        ((congr (LinearEquiv.refl (ULift.{u} T₂) (ULift.{u} T₂)) E).trans
          ((cancelBaseChange R₀ T₂ (ULift.{u} T₂) (ULift.{u} T₂) Y).trans
            ((congr (LinearEquiv.refl (ULift.{u} T₂) (ULift.{u} T₂))
                (ULift.moduleEquiv : ULift.{u} Y ≃ₗ[R₀] Y).symm).trans
              (tensorBaseCongr (ULift.ringEquiv.symm : R₀ ≃+* ULift.{u} R₀)
                (fun _ => rfl) (fun _ _ => rfl)).symm)))))

variable {R₁ R₂ : Type u} [CommRing R₁] [CommRing R₂] [Algebra R₁ R₂]
  [Algebra (ULift.{u} T₂) R₂] [Algebra (ULift.{u} T₁) R₂] [Algebra (ULift.{u} R₀) R₂]
  [IsScalarTower (ULift.{u} T₁) (ULift.{u} T₂) R₂]
  [IsScalarTower (ULift.{u} R₀) (ULift.{u} T₂) R₂] [Module R₁ (ULift.{u} X)]

/-- **The same identification over a ring isomorphic to `ULift T₁`.** `R₁` is a ring with an
isomorphism `γ` from `ULift T₁`, acting on `ULift X` through `γ`; `R₂` is an algebra over `R₁`,
over `ULift T₂` and over `ULift R₀`, compatibly. -/
def tensorUliftCongrOfRingEquiv (γ : ULift.{u} T₁ ≃+* R₁)
    (hC : ∀ t, algebraMap (ULift.{u} T₁) R₂ t = algebraMap R₁ R₂ (γ t))
    (hX : ∀ (t : ULift.{u} T₁) (x : ULift.{u} X), t • x = (γ t) • x)
    (E : (T₂ ⊗[T₁] X) ≃ₗ[T₂] (T₂ ⊗[R₀] Y)) :
    (R₂ ⊗[R₁] ULift.{u} X) ≃ₗ[R₂] (R₂ ⊗[ULift.{u} R₀] ULift.{u} Y) :=
  (tensorBaseCongr γ hC hX).trans
    ((cancelBaseChange (ULift.{u} T₁) (ULift.{u} T₂) R₂ R₂ (ULift.{u} X)).symm.trans
      ((congr (LinearEquiv.refl R₂ R₂) (tensorUliftCongr E)).trans
        (cancelBaseChange (ULift.{u} R₀) (ULift.{u} T₂) R₂ R₂ (ULift.{u} Y))))

end Chain

section TmulKernel

/-- **A tensor `1 ⊗ y` vanishing forces `y` into the kernel ideal.** For a surjection
`P' → P` whose kernel is generated by `t`, if `1 ⊗ y = 0` in `P ⊗[P'] N` then `y = t · w` for
some `w`. -/
theorem eq_smul_of_tmul_eq_zero {P' : Type w} {P : Type v} {N : Type u}
    [CommRing P'] [CommRing P] [Algebra P' P] [AddCommGroup N] [Module P' N]
    (hsurj : Function.Surjective (algebraMap P' P)) {t : P'}
    (hker : RingHom.ker (algebraMap P' P) = Ideal.span {t})
    {y : N} (h : (1 : P) ⊗ₜ[P'] y = 0) : ∃ w : N, y = t • w := by
  set J := RingHom.ker (algebraMap P' P) with hJ
  let ι : P ≃ₐ[P'] (P' ⧸ J) :=
    (Ideal.quotientKerAlgEquivOfSurjective (f := Algebra.ofId P' P) hsurj).symm
  let e1 : (P ⊗[P'] N) ≃ₗ[P'] ((P' ⧸ J) ⊗[P'] N) :=
    TensorProduct.congr ι.toLinearEquiv (LinearEquiv.refl P' N)
  let e2 := TensorProduct.quotTensorEquivQuotSMul N J
  have h1 : e1 ((1 : P) ⊗ₜ[P'] y) = (Ideal.Quotient.mk J 1) ⊗ₜ[P'] y := by
    show ι (1 : P) ⊗ₜ[P'] y = _
    rw [map_one]
    rfl
  have h2 : e2 (e1 ((1 : P) ⊗ₜ[P'] y)) = Submodule.Quotient.mk y := by
    rw [h1, TensorProduct.quotTensorEquivQuotSMul_mk_tmul, one_smul]
  have h3 : Submodule.Quotient.mk (p := J • (⊤ : Submodule P' N)) y = 0 := by
    rw [← h2, h, map_zero, map_zero]
  rw [Submodule.Quotient.mk_eq_zero] at h3
  refine Submodule.smul_induction_on h3 ?_ ?_
  · intro r hr n _
    rw [hker, Ideal.mem_span_singleton] at hr
    obtain ⟨c, rfl⟩ := hr
    exact ⟨c • n, by rw [mul_smul]⟩
  · rintro a b ⟨wa, rfl⟩ ⟨wb, rfl⟩
    exact ⟨wa + wb, (smul_add _ _ _).symm⟩

end TmulKernel

section Localization

/-- `ULift` of a localization away from `g` is the localization of `ULift R` away from
`ULift.up g`. -/
theorem isLocalization_away_ulift {R : Type} [CommRing R] (g : R) (S : Type) [CommRing S]
    [Algebra R S] [IsLocalization.Away g S] :
    IsLocalization.Away (ULift.up.{u} g : ULift.{u} R) (ULift.{u} S) := by
  have h1 : IsLocalization (Submonoid.powers g) (ULift.{u} S) :=
    IsLocalization.isLocalization_of_algEquiv (Submonoid.powers g)
      (ULift.algEquiv (R := R) (A := S)).symm
  refine IsLocalization.of_ringEquiv_left (ULift.ringEquiv : ULift.{u} R ≃+* R)
    (M₁ := Submonoid.powers g) ?_ fun x => rfl
  ext x
  simp only [Submonoid.mem_map, Submonoid.mem_powers_iff]
  constructor
  · rintro ⟨y, ⟨n, hn⟩, rfl⟩
    exact ⟨n, by rw [← hn]; rfl⟩
  · rintro ⟨n, hn⟩
    exact ⟨ULift.up.{u} g ^ n, ⟨n, rfl⟩, by rw [← hn]; rfl⟩

end Localization

section FlatDescent

variable (R : Type) [CommRing R] (M : Type v) [AddCommGroup M] [Module (ULift.{u} R) M]

/-- A flat `ULift R`-module is flat over `R`. -/
theorem flat_of_ulift_left (h : Module.Flat (ULift.{u} R) M) :
    letI : Module R M := Module.compHom M (algebraMap R (ULift.{u} R))
    Module.Flat R M := by
  let : Module R M := Module.compHom M (algebraMap R (ULift.{u} R))
  have : IsScalarTower R (ULift.{u} R) M := ⟨fun r a x => mul_smul (ULift.up.{u} r) a x⟩
  have : Module.Flat R (ULift.{u} R) := Module.Flat.ulift_right_iff.2 Module.Flat.self
  have := h
  exact Module.Flat.trans R (ULift.{u} R) M

end FlatDescent

end Stacks.ULiftTransport

end
