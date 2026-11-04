module

public import Mathlib.CategoryTheory.Functor.OfSequence
public import StacksFrontier.RingTheory.AdicCompletion.NoetherianRing
public import StacksFrontier.RingTheory.Module.AdicSystem.Hom

@[expose] public section

/-!
# The isomorphism system of the adic reductions of a module finite over the completed base

Let `Λ` be a Noetherian ring, `I ⊆ Λ` an ideal and `M` a `Λ`-module whose completion is finite
over the completion `Λ^∧` — but which need not be finite over `Λ` itself.  Writing
`Mₙ = M ⧸ Iⁿ M`, this file shows that the inverse system

`n ↦ Isom_Λ(Mₙ, Mₙ)`

of self-isomorphisms of the adic reductions of `M`, with the transition maps induced by
`Mₙ₊₁ → Mₙ`, satisfies the Mittag-Leffler condition.

The point is that the Mittag-Leffler statement for a module finite over the *base* is Stacks 09BB,
available as
`Stacks.AdicSystem.HomComparison.hom_isom_quotient_systems_mittagLeffler_and_completion`, so it
suffices to run it over `Λ^∧` for the module `M^∧` and to carry the result back. Two
identifications do that. First, `Iⁿ` and `(I Λ^∧)ⁿ` cut out the same subgroup of `M^∧`, so
`M^∧ ⧸ (I Λ^∧)ⁿ M^∧` is `M^∧ ⧸ Iⁿ M^∧`, which is `Mₙ` by Stacks 05GG
(`AdicCompletion.quotPowSMulTopEquiv`). Second, on a module killed by `(I Λ^∧)ⁿ` every scalar of
`Λ^∧` acts through a scalar of `Λ`, because `Λ → Λ^∧ ⧸ (I Λ^∧)ⁿ` is surjective; so `Λ`-linearity
and `Λ^∧`-linearity are the same condition there, and the two sets of self-isomorphisms are in
bijection. The bijections commute with the transition maps, and the Mittag-Leffler condition passes
along a pointwise surjective morphism of systems.

## Main results

* `Stacks.AdicSystem.CompleteBase.isom_quotient_system_isMittagLeffler_of_finite_adicCompletion`:
  for an `I`-adically complete module `M` over a Noetherian ring `Λ` whose completion is a finite
  `Λ^∧`-module, the system `n ↦ Isom_Λ(Mₙ, Mₙ)` with the induced transition maps is
  Mittag-Leffler.
* `Stacks.AdicSystem.CompleteBase.isMittagLeffler_of_equiv`: the Mittag-Leffler condition
  transfers along a family of bijections commuting with the transition maps.  This is independent
  of adic completions.
* `Stacks.AdicSystem.CompleteBase.restrictScalars_map_smul_top`: for an `R`-algebra `S`, an ideal
  `K ⊆ R` and an `S`-module `N`, the submodules `(K S) N` and `K N` of `N` agree.
* `Stacks.AdicSystem.CompleteBase.linearEquivRestrictScalarsEquiv`: on a module where every
  scalar of `S` acts as a scalar of `R`, the `S`-linear and the `R`-linear self-equivalences are
  the same.

## Implementation notes

Inverse systems of sets are functors on `ℕᵒᵖ` built with `CategoryTheory.Functor.ofOpSequence`,
matching the shape in which Stacks 09BB states its conclusion.  The transfer of the Mittag-Leffler
condition is phrased for an arbitrary pair of sequences of types, so that the adic input enters
only through the family of bijections and the square they make with the transition maps; this
keeps the elaboration of the final assembly small.

The completed base enters as `AdicCompletion I Λ` with the ideal
`I.map (algebraMap Λ (AdicCompletion I Λ))`, written out rather than abbreviated so that the
submodules appearing here are syntactically those produced by Stacks 09BB.

## References

* [Stacks Project, Tag 09BB](https://stacks.math.columbia.edu/tag/09BB)
* [Stacks Project, Tag 09BV](https://stacks.math.columbia.edu/tag/09BV)
* [Stacks Project, Tag 05GG](https://stacks.math.columbia.edu/tag/05GG)
-/

section

open CategoryTheory Opposite

namespace Stacks.AdicSystem.CompleteBase

universe u v w

/-! ### Transfer of the Mittag-Leffler condition along per-level bijections -/

/-- **The Mittag-Leffler condition transfers along per-level bijections.** If `ε n : X n ≃ Y n`
turns the transition maps `f` of one tower of sets into the transition maps `g` of another, then
the second tower is Mittag-Leffler as soon as the first one is.

The bijections assemble into a morphism of systems by
`CategoryTheory.NatTrans.ofOpSequence`, whose naturality has to be checked only at the successor
steps, and the condition passes along a pointwise surjective morphism. -/
theorem isMittagLeffler_of_equiv {X Y : ℕ → Type w}
    (f : ∀ n : ℕ, X (n + 1) → X n) (g : ∀ n : ℕ, Y (n + 1) → Y n) (ε : ∀ n : ℕ, X n ≃ Y n)
    (hcomm : ∀ (n : ℕ) (x : X (n + 1)), ε n (f n x) = g n (ε (n + 1) x))
    (hML : (Functor.ofOpSequence (X := X) (fun n => TypeCat.ofHom (f n))).IsMittagLeffler) :
    (Functor.ofOpSequence (X := Y) (fun n => TypeCat.ofHom (g n))).IsMittagLeffler := by
  have hnat : ∀ n : ℕ,
      (Functor.ofOpSequence (X := X) (fun n => TypeCat.ofHom (f n))).map
            (homOfLE (n.le_add_right 1)).op ≫ TypeCat.ofHom (fun x => ε n x)
          = TypeCat.ofHom (fun x => ε (n + 1) x) ≫
            (Functor.ofOpSequence (X := Y) (fun n => TypeCat.ofHom (g n))).map
              (homOfLE (n.le_add_right 1)).op := by
    intro n
    rw [Functor.ofOpSequence_map_homOfLE_succ, Functor.ofOpSequence_map_homOfLE_succ]
    exact ConcreteCategory.hom_ext _ _ fun x => hcomm n x
  exact Functor.isMittagLeffler_of_surjective_natTrans
    (NatTrans.ofOpSequence (fun n => TypeCat.ofHom (fun x => ε n x)) hnat)
    (fun i => (ε i.unop).surjective) hML

/-! ### Scalars of an algebra acting through the base -/

section Scalars

variable {R : Type u} [CommRing R] {S : Type v} [CommRing S] [Algebra R S]
  {N : Type w} [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R S N]

/-- The scalars of `S` carrying every element of `N` into the submodule `K N`, for `K` an ideal
of the base `R`.  It is an ideal of `S` because `K N` is stable under the `S`-action read through
the tower, which is where the commutativity of `S` is used. -/
def smulMemIdeal (K : Ideal R) : Ideal S where
  carrier := {s : S | ∀ y : N, s • y ∈ K • (⊤ : Submodule R N)}
  add_mem' {s t} hs ht y := by rw [add_smul]; exact Submodule.add_mem _ (hs y) (ht y)
  zero_mem' y := by rw [zero_smul]; exact Submodule.zero_mem _
  smul_mem' c {s} hs y := by rw [smul_eq_mul, mul_comm, mul_smul]; exact hs (c • y)

/-- Every scalar of the ideal `K S ⊆ S` generated by an ideal `K` of the base carries `N` into
`K N`. -/
theorem map_le_smulMemIdeal (K : Ideal R) :
    K.map (algebraMap R S) ≤ smulMemIdeal (N := N) K :=
  Ideal.map_le_iff_le_comap.mpr fun a ha y => by
    rw [IsScalarTower.algebraMap_smul]
    exact Submodule.smul_mem_smul ha Submodule.mem_top

/-- A scalar `a ∈ K` of the base carries `N` into the `S`-submodule `(K S) N`. -/
private theorem smul_mem_map_smul_top {K : Ideal R} {a : R} (ha : a ∈ K) (y : N) :
    a • y ∈ (K.map (algebraMap R S)) • (⊤ : Submodule S N) := by
  rw [← IsScalarTower.algebraMap_smul S a y]
  exact Submodule.smul_mem_smul (Ideal.mem_map_of_mem _ ha) Submodule.mem_top

/-- **`(K S) N = K N`.** For an `R`-algebra `S`, an ideal `K` of `R` and an `S`-module `N`, the
`S`-submodule of `N` generated by `K` and the `R`-submodule of `N` generated by `K` have the same
elements.  One inclusion is the tower identity `(algebraMap a) • y = a • y`; the other holds
because `K N` is already stable under the `S`-action. -/
theorem restrictScalars_map_smul_top (K : Ideal R) :
    ((K.map (algebraMap R S)) • (⊤ : Submodule S N)).restrictScalars R
      = K • (⊤ : Submodule R N) := by
  refine le_antisymm (fun x hx => ?_) (Submodule.smul_le.2 fun a ha y _ => ?_)
  · exact Submodule.smul_induction_on ((Submodule.restrictScalars_mem R _ x).mp hx)
      (fun s hs y _ => map_le_smulMemIdeal K hs y) fun u v hu hv => Submodule.add_mem _ hu hv
  · exact smul_mem_map_smul_top ha y

variable {Q : Type w} [AddCommGroup Q] [Module R Q] [Module S Q] [IsScalarTower R S Q]

/-- **On a module killed by an ideal of the base, the scalars of an algebra act through the
base.** If `K Q = 0` and `R → S ⧸ K S` is surjective — the latter in the explicit form that every
`s : S` differs from the image of some `a : R` by an element of `K S` — then every scalar of `S`
acts on `Q` as a scalar of `R`. -/
theorem exists_forall_smul_eq (K : Ideal R) (hann : ∀ c ∈ K, ∀ x : Q, c • x = 0)
    (hsurj : ∀ s : S, ∃ a : R, s - algebraMap R S a ∈ (K • ⊤ : Submodule R S)) (s : S) :
    ∃ a : R, ∀ x : Q, s • x = a • x := by
  obtain ⟨a, ha⟩ := hsurj s
  refine ⟨a, fun x => ?_⟩
  have h0 : (s - algebraMap R S a) • x = 0 :=
    Submodule.smul_induction_on ha
      (fun c hc t _ => by rw [smul_assoc]; exact hann c hc _)
      fun u v hu hv => by rw [add_smul, hu, hv, add_zero]
  rwa [sub_smul, IsScalarTower.algebraMap_smul, sub_eq_zero] at h0

/-- **`S`-linear and `R`-linear self-equivalences agree where `S` acts through `R`.** If every
scalar of `S` acts on `Q` as some scalar of `R`, then restriction of scalars is a bijection from
the `S`-linear self-equivalences of `Q` onto the `R`-linear ones: an `R`-linear map is
automatically `S`-linear. -/
def linearEquivRestrictScalarsEquiv (h : ∀ s : S, ∃ a : R, ∀ x : Q, s • x = a • x) :
    (Q ≃ₗ[S] Q) ≃ (Q ≃ₗ[R] Q) where
  toFun e := e.restrictScalars R
  invFun e :=
    { toFun := e
      map_add' := e.map_add
      map_smul' s x := by
        obtain ⟨a, ha⟩ := h s
        rw [RingHom.id_apply, ha x, ha (e x)]
        exact map_smul e a x
      invFun := e.symm
      left_inv := e.left_inv
      right_inv := e.right_inv }
  left_inv _ := rfl
  right_inv _ := rfl

/-- `linearEquivRestrictScalarsEquiv h e` acts on `Q` as `e`. -/
@[simp]
theorem linearEquivRestrictScalarsEquiv_apply (h : ∀ s : S, ∃ a : R, ∀ x : Q, s • x = a • x)
    (e : Q ≃ₗ[S] Q) (x : Q) : linearEquivRestrictScalarsEquiv h e x = e x := rfl

/-- The `S`-linear self-equivalence corresponding to an `R`-linear one `e` acts on `Q` as `e`. -/
@[simp]
theorem linearEquivRestrictScalarsEquiv_symm_apply
    (h : ∀ s : S, ∃ a : R, ∀ x : Q, s • x = a • x) (e : Q ≃ₗ[R] Q) (x : Q) :
    (linearEquivRestrictScalarsEquiv h).symm e x = e x := rfl

end Scalars

/-! ### Conjugation of self-equivalences -/

section Conj

variable {R : Type u} [CommRing R] {Q : Type v} [AddCommGroup Q] [Module R Q]
  {P : Type w} [AddCommGroup P] [Module R P]

/-- Conjugation by a linear equivalence `ψ : Q ≃ₗ[R] P`, as a bijection between the self-
equivalences of `Q` and those of `P`. -/
def conjEquiv (ψ : Q ≃ₗ[R] P) : (Q ≃ₗ[R] Q) ≃ (P ≃ₗ[R] P) where
  toFun f := (ψ.symm.trans f).trans ψ
  invFun g := (ψ.trans g).trans ψ.symm
  left_inv f := by ext x; simp
  right_inv g := by ext x; simp

/-- The conjugate of `f` by `ψ` sends `x` to `ψ (f (ψ.symm x))`. -/
@[simp]
theorem conjEquiv_apply (ψ : Q ≃ₗ[R] P) (f : Q ≃ₗ[R] Q) (x : P) :
    conjEquiv ψ f x = ψ (f (ψ.symm x)) := rfl

/-- The inverse conjugation by `ψ` sends `g` to the map `x ↦ ψ.symm (g (ψ x))`. -/
@[simp]
theorem conjEquiv_symm_apply (ψ : Q ≃ₗ[R] P) (g : P ≃ₗ[R] P) (x : Q) :
    (conjEquiv ψ).symm g x = ψ.symm (g (ψ x)) := rfl

end Conj

/-! ### The adic reductions of a module and of its completion -/

section Adic

variable {Λ : Type u} [CommRing Λ] [IsNoetherianRing Λ] (I : Ideal Λ)
  {M : Type v} [AddCommGroup M] [Module Λ M]

omit [IsNoetherianRing Λ] in
/-- A scalar in `Iⁿ` carries `M^∧` into `(I Λ^∧)ⁿ M^∧`: it is the image of a scalar of `Λ^∧`
lying in `(I Λ^∧)ⁿ`. -/
theorem smul_mem_map_pow_smul_top {n : ℕ} {c : Λ} (hc : c ∈ I ^ n) (y : AdicCompletion I M) :
    c • y ∈ (I.map (algebraMap Λ (AdicCompletion I Λ))) ^ n •
      (⊤ : Submodule (AdicCompletion I Λ) (AdicCompletion I M)) := by
  rw [← Ideal.map_pow]
  exact smul_mem_map_smul_top hc y

omit [IsNoetherianRing Λ] in
/-- `Iⁿ` kills `M^∧ ⧸ (I Λ^∧)ⁿ M^∧`. -/
theorem pow_smul_quot_eq_zero {n : ℕ} (c : Λ) (hc : c ∈ I ^ n)
    (x : AdicCompletion I M ⧸ ((I.map (algebraMap Λ (AdicCompletion I Λ))) ^ n •
      (⊤ : Submodule (AdicCompletion I Λ) (AdicCompletion I M)))) : c • x = 0 := by
  induction x using Submodule.Quotient.induction_on with
  | _ y => exact (Submodule.Quotient.mk_eq_zero _).mpr (smul_mem_map_pow_smul_top I hc y)

/-- **`Λ → Λ^∧ ⧸ Iⁿ Λ^∧` is surjective.** Every element of the completion of a Noetherian ring
differs from the image of a scalar of the base by an element of `Iⁿ Λ^∧`.  Indeed the `n`-th
component of `s : Λ^∧` lies in `Λ ⧸ Iⁿ`, so it is the class of some `a : Λ`, and `Iⁿ Λ^∧` is
exactly the kernel of the `n`-th projection (Stacks 05GG). -/
theorem exists_sub_algebraMap_mem (n : ℕ) (s : AdicCompletion I Λ) :
    ∃ a : Λ, s - algebraMap Λ (AdicCompletion I Λ) a ∈
      (I ^ n • ⊤ : Submodule Λ (AdicCompletion I Λ)) := by
  obtain ⟨a, ha⟩ := Submodule.Quotient.mk_surjective _ (s.val n)
  refine ⟨a, ?_⟩
  rw [AdicCompletion.pow_smul_top_eq_ker_eval (Ideal.fg_of_isNoetherianRing I),
    LinearMap.mem_ker, map_sub, sub_eq_zero]
  change s.val n = (AdicCompletion.of I Λ a).val n
  rw [AdicCompletion.of_apply, Submodule.mkQ_apply, ← ha]

/-- Every scalar of `Λ^∧` acts on `M^∧ ⧸ (I Λ^∧)ⁿ M^∧` as a scalar of `Λ`. -/
theorem exists_forall_smul_eq_quot (n : ℕ) (s : AdicCompletion I Λ) :
    ∃ a : Λ, ∀ x : AdicCompletion I M ⧸ ((I.map (algebraMap Λ (AdicCompletion I Λ))) ^ n •
      (⊤ : Submodule (AdicCompletion I Λ) (AdicCompletion I M))), s • x = a • x :=
  exists_forall_smul_eq (I ^ n) (fun c hc => pow_smul_quot_eq_zero I c hc)
    (exists_sub_algebraMap_mem I n) s

/-- **The adic reductions of `M` and of `M^∧` agree.** For `I` an ideal of a Noetherian ring `Λ`
and `M` a `Λ`-module, `M^∧ ⧸ (I Λ^∧)ⁿ M^∧` is `M ⧸ Iⁿ M` as a `Λ`-module.

The submodules `(I Λ^∧)ⁿ M^∧` and `Iⁿ M^∧` of `M^∧` coincide
(`restrictScalars_map_smul_top`), and `M^∧ ⧸ Iⁿ M^∧ = M ⧸ Iⁿ M` is Stacks 05GG
(`AdicCompletion.quotPowSMulTopEquiv`). -/
noncomputable def quotEquiv (n : ℕ) :
    (AdicCompletion I M ⧸ ((I.map (algebraMap Λ (AdicCompletion I Λ))) ^ n •
        (⊤ : Submodule (AdicCompletion I Λ) (AdicCompletion I M)))) ≃ₗ[Λ]
      (M ⧸ (I ^ n • ⊤ : Submodule Λ M)) :=
  (Submodule.Quotient.restrictScalarsEquiv Λ _).symm.trans
    ((Submodule.quotEquivOfEq _ _ (by
        rw [← Ideal.map_pow]; exact restrictScalars_map_smul_top (I ^ n))).trans
      (AdicCompletion.quotPowSMulTopEquiv (Ideal.fg_of_isNoetherianRing I) M n))

/-- `quotEquiv` sends the class of `x : M^∧` to the `n`-th component of `x` in `M ⧸ Iⁿ M`. -/
@[simp]
theorem quotEquiv_mk (n : ℕ) (x : AdicCompletion I M) :
    quotEquiv I n (Submodule.Quotient.mk x) = x.val n := by
  simp [quotEquiv]

/-- `quotEquiv` sends the class of the image of `m : M` in `M^∧` to the class of `m`. -/
@[simp]
theorem quotEquiv_mk_of (n : ℕ) (m : M) :
    quotEquiv I n (Submodule.Quotient.mk (AdicCompletion.of I M m)) =
      Submodule.Quotient.mk m := by
  rw [quotEquiv_mk, AdicCompletion.of_apply, Submodule.mkQ_apply]

/-- The inverse of `quotEquiv` sends the class of `m : M` to the class of its image in `M^∧`. -/
@[simp]
theorem quotEquiv_symm_mk (n : ℕ) (m : M) :
    (quotEquiv I n).symm (Submodule.Quotient.mk m) =
      Submodule.Quotient.mk (AdicCompletion.of I M m) := by
  rw [LinearEquiv.symm_apply_eq, quotEquiv_mk_of]

/-- The identification of the adic reductions of `M` and of `M^∧` commutes with the transition
maps of the two systems. -/
theorem quotEquiv_transitionMap (n : ℕ)
    (z : AdicCompletion I M ⧸ ((I.map (algebraMap Λ (AdicCompletion I Λ))) ^ (n + 1) •
      (⊤ : Submodule (AdicCompletion I Λ) (AdicCompletion I M)))) :
    quotEquiv I n (AdicCompletion.transitionMap
        (I.map (algebraMap Λ (AdicCompletion I Λ))) (AdicCompletion I M) (Nat.le_succ n) z)
      = AdicCompletion.transitionMap I M (Nat.le_succ n) (quotEquiv I (n + 1) z) := by
  induction z using Submodule.Quotient.induction_on with
  | _ y =>
    rw [quotEquiv_mk]
    change quotEquiv I n (Submodule.Quotient.mk y) = _
    rw [quotEquiv_mk, AdicCompletion.transitionMap_comp_eval_apply]

/-- **The self-isomorphisms of the adic reductions of `M` and of `M^∧` are in bijection.** Over
`Λ` the two reductions agree (`quotEquiv`), and on `M^∧ ⧸ (I Λ^∧)ⁿ M^∧` a `Λ`-linear
self-equivalence is the same thing as a `Λ^∧`-linear one, because `Λ^∧` acts there through `Λ`. -/
noncomputable def isoEquiv (n : ℕ) :
    ((AdicCompletion I M ⧸ ((I.map (algebraMap Λ (AdicCompletion I Λ))) ^ n •
          (⊤ : Submodule (AdicCompletion I Λ) (AdicCompletion I M)))) ≃ₗ[AdicCompletion I Λ]
        (AdicCompletion I M ⧸ ((I.map (algebraMap Λ (AdicCompletion I Λ))) ^ n •
          (⊤ : Submodule (AdicCompletion I Λ) (AdicCompletion I M))))) ≃
      ((M ⧸ (I ^ n • ⊤ : Submodule Λ M)) ≃ₗ[Λ] (M ⧸ (I ^ n • ⊤ : Submodule Λ M))) :=
  (linearEquivRestrictScalarsEquiv (exists_forall_smul_eq_quot I n)).trans
    (conjEquiv (quotEquiv I n))

/-- `isoEquiv` sends a self-equivalence `g` of `M^∧ ⧸ (I Λ^∧)ⁿ M^∧` to its conjugate by
`quotEquiv`. -/
theorem isoEquiv_apply (n : ℕ) (g : _) (x : M ⧸ (I ^ n • ⊤ : Submodule Λ M)) :
    isoEquiv I n g x = quotEquiv I n (g ((quotEquiv I n).symm x)) := rfl

/-- The inverse of `isoEquiv` sends a self-equivalence `e` of `M ⧸ Iⁿ M` to its conjugate by the
inverse of `quotEquiv`. -/
theorem isoEquiv_symm_apply (n : ℕ) (e : (M ⧸ (I ^ n • ⊤ : Submodule Λ M)) ≃ₗ[Λ]
      (M ⧸ (I ^ n • ⊤ : Submodule Λ M)))
    (x : AdicCompletion I M ⧸ ((I.map (algebraMap Λ (AdicCompletion I Λ))) ^ n •
      (⊤ : Submodule (AdicCompletion I Λ) (AdicCompletion I M)))) :
    (isoEquiv I n).symm e x = (quotEquiv I n).symm (e (quotEquiv I n x)) := rfl

/-- The transition map of the system of self-isomorphisms of the reductions of `M`, obtained by
transporting the transition map of the system for `M^∧` along `isoEquiv`, is computed by the
quotient projection `Mₙ₊₁ → Mₙ`.

This is the characterisation used to recognise the transported system as the one induced by
`AdicCompletion.transitionMap`. -/
theorem isoEquiv_transition_apply_mk
    (isoTransition : ∀ n : ℕ,
      ((AdicCompletion I M ⧸ ((I.map (algebraMap Λ (AdicCompletion I Λ))) ^ (n + 1) •
          (⊤ : Submodule (AdicCompletion I Λ) (AdicCompletion I M)))) ≃ₗ[AdicCompletion I Λ]
        (AdicCompletion I M ⧸ ((I.map (algebraMap Λ (AdicCompletion I Λ))) ^ (n + 1) •
          (⊤ : Submodule (AdicCompletion I Λ) (AdicCompletion I M))))) →
      ((AdicCompletion I M ⧸ ((I.map (algebraMap Λ (AdicCompletion I Λ))) ^ n •
          (⊤ : Submodule (AdicCompletion I Λ) (AdicCompletion I M)))) ≃ₗ[AdicCompletion I Λ]
        (AdicCompletion I M ⧸ ((I.map (algebraMap Λ (AdicCompletion I Λ))) ^ n •
          (⊤ : Submodule (AdicCompletion I Λ) (AdicCompletion I M))))))
    (hiso : ∀ (n : ℕ) (g : _) (y : AdicCompletion I M),
      isoTransition n g (Submodule.Quotient.mk y) = AdicCompletion.transitionMap
        (I.map (algebraMap Λ (AdicCompletion I Λ))) (AdicCompletion I M) (Nat.le_succ n)
        (g (Submodule.Quotient.mk y)))
    (n : ℕ) (e : (M ⧸ (I ^ (n + 1) • ⊤ : Submodule Λ M)) ≃ₗ[Λ]
      (M ⧸ (I ^ (n + 1) • ⊤ : Submodule Λ M))) (x : M) :
    isoEquiv I n (isoTransition n ((isoEquiv I (n + 1)).symm e)) (Submodule.Quotient.mk x)
      = AdicCompletion.transitionMap I M (Nat.le_succ n) (e (Submodule.Quotient.mk x)) := by
  rw [isoEquiv_apply, quotEquiv_symm_mk, hiso n _ (AdicCompletion.of I M x),
    quotEquiv_transitionMap, isoEquiv_symm_apply, quotEquiv_mk_of,
    LinearEquiv.apply_symm_apply]

/-- **Stacks 09BB for a module finite over the completed base.** Let `Λ` be a Noetherian ring,
`I ⊆ Λ` an ideal and `M` a `Λ`-module whose completion is a finite module over the completion
`Λ^∧` of `Λ` — the case of interest being an `I`-adically complete `M`, which is then itself
finite over `Λ^∧`.  Then the inverse system of self-isomorphisms of the adic
reductions `Mₙ = M ⧸ Iⁿ M` of `M`, with the transition maps induced by the projections
`Mₙ₊₁ → Mₙ`, satisfies the Mittag-Leffler condition.

Stacks 09BB over the Noetherian ring `Λ^∧` gives the statement for the system of
`Λ^∧`-linear self-isomorphisms of the reductions of `M^∧` along `I Λ^∧`; those reductions are the
`Mₙ` and `Λ`-linearity is `Λ^∧`-linearity on them, so the two systems are related by a
level-wise bijection and the condition transfers. -/
public theorem isom_quotient_system_isMittagLeffler_of_finite_adicCompletion
    {Λ : Type u} [CommRing Λ] [IsNoetherianRing Λ] (I : Ideal Λ)
    {M : Type v} [AddCommGroup M] [Module Λ M]
    [Module.Finite (AdicCompletion I Λ) (AdicCompletion I M)] :
    ∃ tr : ∀ n : ℕ,
        ((M ⧸ (I ^ (n + 1) • ⊤ : Submodule Λ M)) ≃ₗ[Λ]
          (M ⧸ (I ^ (n + 1) • ⊤ : Submodule Λ M))) →
        ((M ⧸ (I ^ n • ⊤ : Submodule Λ M)) ≃ₗ[Λ] (M ⧸ (I ^ n • ⊤ : Submodule Λ M))),
      (∀ (n : ℕ) (e : _) (x : M), tr n e (Submodule.Quotient.mk x) =
          AdicCompletion.transitionMap I M (Nat.le_succ n) (e (Submodule.Quotient.mk x))) ∧
      (CategoryTheory.Functor.ofOpSequence
          (X := fun n : ℕ => ((M ⧸ (I ^ n • ⊤ : Submodule Λ M)) ≃ₗ[Λ]
            (M ⧸ (I ^ n • ⊤ : Submodule Λ M))))
          (fun n => TypeCat.ofHom (tr n))).IsMittagLeffler := by
  have : IsNoetherianRing (AdicCompletion I Λ) :=
    Stacks.AdicCompletion.NoetherianRing.solution I
  obtain ⟨-, isoTransition, -, -, hiso, -, -, hML, -⟩ :=
    Stacks.AdicSystem.HomComparison.hom_isom_quotient_systems_mittagLeffler_and_completion
      (A := AdicCompletion I Λ) (M := AdicCompletion I M) (N := AdicCompletion I M)
      (I.map (algebraMap Λ (AdicCompletion I Λ)))
  refine ⟨fun n e => isoEquiv I n (isoTransition n ((isoEquiv I (n + 1)).symm e)),
    isoEquiv_transition_apply_mk I isoTransition hiso, ?_⟩
  refine isMittagLeffler_of_equiv _ _ (fun n => isoEquiv I n) (fun n x => ?_) hML
  rw [Equiv.symm_apply_apply]

end Adic

end Stacks.AdicSystem.CompleteBase

end

end
