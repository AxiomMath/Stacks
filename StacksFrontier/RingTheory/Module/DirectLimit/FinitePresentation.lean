module

public import StacksFrontier.RingTheory.FinitePresentation.ModuleDescent
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Finitely presented modules over a directed colimit of rings

Let `A` be a ring and let `R = colim_j S j` be a directed colimit of `A`-algebras. The category
of finitely presented `R`-modules is the colimit of the categories of finitely presented
`S j`-modules:

1. every finitely presented `R`-module is isomorphic to the base change `R ⊗[S j] M_j` of a
   finitely presented `S j`-module `M_j`, for some stage `j`;
2. every `R`-linear map `R ⊗[A] M → R ⊗[A] N` between base changes of `A`-modules, with `M`
   finitely presented, is the base change of an `S j`-linear map `S j ⊗[A] M → S j ⊗[A] N`
   for some `j`;
3. two `A`-linear maps `u, u' : M → N` with `M` finite whose base changes to `R` agree already
   have equal base changes to `S j` for some `j`.

For (1), a presentation `R^m → R^n → M → 0` is an `m × n` matrix over `R`; its finitely many
entries come from one stage `S j`, and base change takes the module presented over `S j` by the
lifted matrix to `M`, since
`R ⊗[S] ((ι → S) ⧸ ⟪range g⟫) ≃ (ι → R) ⧸ ⟪range (algebraMap S R ∘ g)⟫`. Items (2) and (3) follow
from `Stacks.FinitePresentation.ColimitDescent.statement_three` and
`Stacks.FinitePresentation.ColimitDescent.statement_one`, once `R ⊗[A] P` is shown to be the
colimit of the `S j ⊗[A] P` (`Stacks.ColimitPresentation.FPModules.isModuleColimit`), which holds
because tensoring commutes with directed colimits (`TensorProduct.directLimitLeft`).

## Main results

* `Module.exists_finitePresentation_and_baseChange_eq_of_lift_bijective`: the three items above,
  for a directed system `S` of `A`-algebras whose colimit is `R`.
* `Stacks.ColimitPresentation.FPModules.isModuleColimit`: `R ⊗[A] P` is the colimit of the
  `S j ⊗[A] P`.

## Implementation notes

The directed colimit is a `DirectedSystem` of `A`-algebras `S : J → Type*` over a nonempty
directed preorder `J`, together with an `A`-algebra `R` receiving the maps `algebraMap (S j) R`,
compatibly with the transition maps (`hf`), such that the induced map `colim_j S j → R` is
bijective (`hR`). The case `R = DirectLimit S f` is an instance.

Items (2) and (3) are stated over an arbitrary base ring `A` of which the whole system consists
of algebras. In (2) only the source module is finitely presented, and in (3) the source is merely
finite. The conclusion of (2), that `φ` is the base change of `φ_j`, is the commuting square
`φ ∘ (ι_j ⊗ 1_M) = (ι_j ⊗ 1_N) ∘ φ_j` with `ι_j ⊗ 1_M = LinearMap.rTensor M ι_j`; since the image
of `LinearMap.rTensor M ι_j` generates `R ⊗[A] M` as an `R`-module, this determines `φ`.

Tensor products carry the new scalars on the left, as in `LinearMap.baseChange`.

## References

* [StacksProject 05N7](https://stacks.math.columbia.edu/tag/05N7);
  [StacksProject 05LI](https://stacks.math.columbia.edu/tag/05LI)
-/

@[expose] public section

universe u v w t t'


namespace Stacks.ColimitPresentation.FPModules

open scoped _root_.TensorProduct

section BaseChange

variable (S : Type*) [CommRing S] (R : Type*) [CommRing R] [Algebra S R]

/-- Base change commutes with quotients: `R ⊗[S] (N ⧸ p) = (R ⊗[S] N) ⧸ p.baseChange R`. -/
private noncomputable def baseChangeQuotEquiv {N : Type*} [AddCommGroup N] [Module S N]
    (p : Submodule S N) : R ⊗[S] (N ⧸ p) ≃ₗ[R] (R ⊗[S] N) ⧸ p.baseChange R :=
  (TensorProduct.AlgebraTensorModule.tensorQuotientEquiv (R := S) (A := R) (B := S)
      (M := R) (N := N) p).trans (Submodule.quotEquivOfEq _ _ (by
    refine le_antisymm (LinearMap.range_le_iff_comap.2 (eq_top_iff.2 fun x _ ↦ ?_)) ?_
    · induction x with
      | tmul r y => exact Submodule.tmul_mem_baseChange_of_mem r y.2
      | add x y hx hy => exact Submodule.add_mem _ (hx trivial) (hy trivial)
    · rw [Submodule.baseChange_eq_span, Submodule.span_le]
      rintro _ ⟨y, hy, rfl⟩
      exact ⟨(1 : R) ⊗ₜ[S] (⟨y, hy⟩ : p), rfl⟩))

/-- Base change takes the module presented by a matrix over `S` to the module presented by the
same matrix read over `R`: if the rows `t : κ → ι → R` are the images of the rows
`g : κ → ι → S`, then `R ⊗[S] ((ι → S) ⧸ ⟪range g⟫) = (ι → R) ⧸ ⟪range t⟫`. -/
private noncomputable def baseChangeQuotSpanEquiv {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    (g : κ → ι → S) (t : κ → ι → R) (ht : ∀ k l, algebraMap S R (g k l) = t k l) :
    R ⊗[S] ((ι → S) ⧸ Submodule.span S (Set.range g)) ≃ₗ[R]
      (ι → R) ⧸ Submodule.span R (Set.range t) :=
  (baseChangeQuotEquiv S R _).trans
    (Submodule.Quotient.equiv _ _ (TensorProduct.piScalarRight S R R ι) (by
      rw [Submodule.baseChange_span, Submodule.map_span, ← Set.image_comp, ← Set.range_comp]
      refine congrArg _ (congrArg _ (funext fun k ↦ funext fun l ↦ ?_))
      simp [TensorProduct.piScalarRight_apply, TensorProduct.piScalarRightHom_tmul,
        Algebra.smul_def, ht k l]))

end BaseChange

section Colimit

variable {J : Type w} [Preorder J] [Nonempty J] [IsDirectedOrder J] {A : Type u} [CommRing A]
  {S : J → Type v} [∀ j, CommRing (S j)] [∀ j, Algebra A (S j)]
  (f : ∀ i j, i ≤ j → S i →ₐ[A] S j) [DirectedSystem S fun i j h ↦ ⇑(f i j h)]
  {R : Type*} [CommRing R] [Algebra A R] [∀ j, Algebra (S j) R]
  [∀ j, IsScalarTower A (S j) R]
  (hf : ∀ i j (h : i ≤ j) (x : S i), algebraMap (S j) R (f i j h x) = algebraMap (S i) R x)
  (hsurj : ∀ r : R, ∃ (j : J) (s : S j), algebraMap (S j) R s = r)
  (hinj : ∀ (j : J) (s : S j), algebraMap (S j) R s = 0 →
    ∃ (k : J) (hjk : j ≤ k), f j k hjk s = 0)

/-- The transition maps of the system, as `A`-linear maps. -/
private abbrev transLin (i j : J) (h : i ≤ j) : S i →ₗ[A] S j := (f i j h).toLinearMap

omit [Nonempty J] [IsDirectedOrder J] in
/-- The transition maps of the system form a directed system of `A`-linear maps. -/
private theorem directedSystem_transLin :
    DirectedSystem S fun i j (h : i ≤ j) ↦ ⇑(transLin f i j h) :=
  ⟨fun _ x ↦ DirectedSystem.map_self' f x,
    fun _ _ _ hij hjk x ↦ DirectedSystem.map_map' f hij hjk x⟩

omit [Nonempty J] [IsDirectedOrder J] [DirectedSystem S fun i j h ↦ ⇑(f i j h)] in
include hf in
/-- The comparison map `colim_j S j → R` induced by the maps `algebraMap (S j) R`. -/
private noncomputable def limLift [DecidableEq J] : Module.DirectLimit S (transLin f) →ₗ[A] R :=
  Module.DirectLimit.lift A J S (transLin f)
    (fun j ↦ (IsScalarTower.toAlgHom A (S j) R).toLinearMap) fun i j hij x ↦ hf i j hij x

omit [Nonempty J] [IsDirectedOrder J] [DirectedSystem S fun i j h ↦ ⇑(f i j h)] in
include hf in
/-- The comparison map sends the image of `s : S i` to `algebraMap (S i) R s`. -/
private theorem limLift_of [DecidableEq J] (i : J) (s : S i) :
    limLift f hf (Module.DirectLimit.of A J S (transLin f) i s) = algebraMap (S i) R s :=
  Module.DirectLimit.lift_of _ _ s

include hf hsurj hinj in
/-- The comparison map `colim_j S j → R`, as an `A`-linear equivalence. -/
private noncomputable def limEquiv [DecidableEq J] :
    Module.DirectLimit S (transLin f) ≃ₗ[A] R :=
  LinearEquiv.ofBijective (limLift f hf)
    ⟨by
      rw [injective_iff_map_eq_zero]
      intro z hz
      obtain ⟨i, s, rfl⟩ := Module.DirectLimit.exists_of z
      rw [limLift_of] at hz
      obtain ⟨k, hik, hk⟩ := hinj i s hz
      have hk' : transLin f i k hik s = 0 := hk
      rw [show Module.DirectLimit.of A J S (transLin f) i s
            = Module.DirectLimit.of A J S (transLin f) k (transLin f i k hik s) from
          Module.DirectLimit.of_f.symm, hk', map_zero], by
      intro r
      obtain ⟨i, s, hs⟩ := hsurj r
      exact ⟨Module.DirectLimit.of A J S (transLin f) i s, (limLift_of f hf i s).trans hs⟩⟩

omit [DirectedSystem S fun i j h ↦ ⇑(f i j h)] in
include hf hsurj hinj in
/-- The inverse of the comparison equivalence sends `algebraMap (S i) R s` to the image of `s`. -/
private theorem limEquiv_symm_algebraMap [DecidableEq J] (i : J) (s : S i) :
    (limEquiv f hf hsurj hinj).symm (algebraMap (S i) R s) =
      Module.DirectLimit.of A J S (transLin f) i s :=
  (limEquiv f hf hsurj hinj).symm_apply_eq.mpr (limLift_of f hf i s).symm

variable (P : Type t') [AddCommGroup P] [Module A P]

include hf hsurj hinj in
/-- The comparison isomorphism `R ⊗[A] P ≃ colim_j (S j ⊗[A] P)`. -/
private noncomputable def tensorLimEquiv [DecidableEq J] :
    R ⊗[A] P ≃ₗ[A] Module.DirectLimit (fun i ↦ S i ⊗[A] P)
      (fun i j h ↦ LinearMap.rTensor P (transLin f i j h)) :=
  (TensorProduct.congr (limEquiv f hf hsurj hinj).symm (LinearEquiv.refl A P)).trans
    (TensorProduct.directLimitLeft (transLin f) P)

omit [DirectedSystem S fun i j h ↦ ⇑(f i j h)] in
include hf hsurj hinj in
/-- The comparison isomorphism identifies the canonical map `S i ⊗[A] P → R ⊗[A] P` with the
structure map of the colimit. -/
private theorem tensorLimEquiv_canonMod [DecidableEq J] (i : J) (y : S i ⊗[A] P) :
    tensorLimEquiv f hf hsurj hinj P
        (Stacks.FinitePresentation.ColimitDescent.canonMod
          (fun j ↦ IsScalarTower.toAlgHom A (S j) R) P i y) =
      Module.DirectLimit.of A J (fun i ↦ S i ⊗[A] P)
        (fun i j h ↦ LinearMap.rTensor P (transLin f i j h)) i y := by
  induction y using TensorProduct.inductionOn with
  | tmul s p =>
      change tensorLimEquiv f hf hsurj hinj P (algebraMap (S i) R s ⊗ₜ[A] p) = _
      rw [tensorLimEquiv]
      simp only [LinearEquiv.trans_apply, TensorProduct.congr_tmul, LinearEquiv.refl_apply,
        limEquiv_symm_algebraMap, TensorProduct.directLimitLeft_tmul_of]
  | add x y hx hy => simp only [map_add, hx, hy]

include hf hsurj hinj in
/-- `R ⊗[A] P` is the colimit of the `S j ⊗[A] P`. -/
theorem isModuleColimit :
    Stacks.FinitePresentation.ColimitDescent.IsModuleColimit (fun i j (h : i ≤ j) ↦ f i j h)
      (fun j ↦ IsScalarTower.toAlgHom A (S j) R) P := by
  classical
  have := directedSystem_transLin f
  refine ⟨fun x ↦ ?_, fun i y z hyz ↦ ?_⟩
  · obtain ⟨i, y, hy⟩ := Module.DirectLimit.exists_of (tensorLimEquiv f hf hsurj hinj P x)
    exact ⟨i, y, (tensorLimEquiv f hf hsurj hinj P).injective
      (by rw [tensorLimEquiv_canonMod, hy])⟩
  · have h : Module.DirectLimit.of A J (fun i ↦ S i ⊗[A] P)
        (fun i j h ↦ LinearMap.rTensor P (transLin f i j h)) i y =
        Module.DirectLimit.of A J (fun i ↦ S i ⊗[A] P)
        (fun i j h ↦ LinearMap.rTensor P (transLin f i j h)) i z := by
      have h' := congrArg (tensorLimEquiv f hf hsurj hinj P) hyz
      rwa [tensorLimEquiv_canonMod, tensorLimEquiv_canonMod] at h'
    obtain ⟨k, hik, hk⟩ := Module.DirectLimit.exists_eq_of_of_eq h
    exact ⟨k, hik, hk⟩

omit [DirectedSystem S fun i j h ↦ ⇑(f i j h)] [∀ j, IsScalarTower A (S j) R] [Algebra A R] in
include f hf hsurj in
/-- Finitely many elements of `R` are all images of elements of a single stage. -/
private theorem exists_forall_algebraMap_eq {α : Type*} [Finite α] (x : α → R) :
    ∃ (j : J) (y : α → S j), ∀ a, algebraMap (S j) R (y a) = x a := by
  choose i s hs using fun a ↦ hsurj (x a)
  obtain ⟨j, hj⟩ := Finite.exists_le i
  exact ⟨j, fun a ↦ f (i a) j (hj a) (s a), fun a ↦ (hf _ _ (hj a) (s a)).trans (hs a)⟩

omit [DirectedSystem S fun i j h ↦ ⇑(f i j h)] [∀ j, IsScalarTower A (S j) R] [Algebra A R] in
include f hf hsurj in
/-- Every finitely presented `R`-module is the base change of a finitely presented module over one
of the stages. -/
private theorem exists_finitePresentation (M : Type t) [AddCommGroup M] [Module R M]
    [Module.FinitePresentation R M] :
    ∃ (j : J) (Mj : Type v) (_ : AddCommGroup Mj) (_ : Module (S j) Mj),
      Module.FinitePresentation (S j) Mj ∧ Nonempty (R ⊗[S j] Mj ≃ₗ[R] M) := by
  classical
  obtain ⟨n, K, eM, hK⟩ := Module.FinitePresentation.exists_fin R M
  obtain ⟨m, t, ht⟩ := Submodule.fg_iff_exists_fin_generating_family.mp hK
  obtain ⟨j, t', ht'⟩ := exists_forall_algebraMap_eq f hf hsurj fun p : Fin m × Fin n ↦ t p.1 p.2
  refine ⟨j, (Fin n → S j) ⧸ Submodule.span (S j) (Set.range fun k l ↦ t' (k, l)),
    inferInstance, inferInstance,
    Module.finitePresentation_of_free_of_surjective _ (Submodule.mkQ_surjective _)
      (by rw [Submodule.ker_mkQ]; exact Submodule.fg_span (Set.finite_range _)),
    ⟨(baseChangeQuotSpanEquiv (S j) R _ t fun k l ↦ ht' (k, l)).trans
      ((Submodule.quotEquivOfEq _ K ht).trans eM.symm)⟩⟩

variable (hR : Function.Bijective (DirectLimit.Algebra.lift S f R
  (fun j ↦ IsScalarTower.toAlgHom A (S j) R) hf))

include hf in
/-- The comparison algebra map `colim_j S j → R` sends the image of `s : S i` to
`algebraMap (S i) R s`. -/
private theorem algebraLift_of (i : J) (x : S i) :
    DirectLimit.Algebra.lift S f R (fun j ↦ IsScalarTower.toAlgHom A (S j) R) hf
      (DirectLimit.Algebra.of S f i x) = algebraMap (S i) R x :=
  DirectLimit.Algebra.lift_of R (fun j ↦ IsScalarTower.toAlgHom A (S j) R) hf i x

include hR in
/-- Every element of `R` is the image of an element of some stage. -/
private theorem exists_algebraMap_eq (r : R) : ∃ (j : J) (s : S j), algebraMap (S j) R s = r := by
  obtain ⟨z, hz⟩ := hR.2 r
  obtain ⟨j, s, rfl⟩ := DirectLimit.exists_eq_mk f z
  exact ⟨j, s, hz⟩

include hR in
/-- An element of a stage which vanishes in `R` already vanishes at a later stage. -/
private theorem exists_map_eq_zero (j : J) (s : S j) (h : algebraMap (S j) R s = 0) :
    ∃ (k : J) (hjk : j ≤ k), f j k hjk s = 0 := by
  obtain ⟨k, hjk, _, heq⟩ := Quotient.exact (hR.1 ((algebraLift_of f hf j s).trans
    (h.trans ((map_zero (algebraMap (S j) R)).symm.trans (algebraLift_of f hf j 0).symm))))
  exact ⟨k, hjk, by simpa using heq⟩

end Colimit

end Stacks.ColimitPresentation.FPModules

open scoped TensorProduct

@[expose] public section

namespace Module

/-- Let `A` be a ring, let `S` be a directed system of `A`-algebras over a nonempty directed
preorder `J` with transition maps `f i j : S i →ₐ[A] S j`, and let `R` be an `A`-algebra
receiving compatible maps `algebraMap (S j) R` which exhibit it as the colimit `colim_j S j`.
Then the category of finitely presented `R`-modules is the colimit of the categories of finitely
presented `S j`-modules:

1. every finitely presented `R`-module `M` is isomorphic to the base change `R ⊗[S j] M_j` of a
   finitely presented `S j`-module, for some `j`;
2. for `A`-modules `M`, `N` with `M` finitely presented, every `R`-linear map
   `R ⊗[A] M → R ⊗[A] N` is the base change of an `S j`-linear map `S j ⊗[A] M → S j ⊗[A] N`
   for some `j`, in the sense that the square with the canonical maps
   `S j ⊗[A] M → R ⊗[A] M` commutes;
3. for `A`-modules `M`, `N` with `M` finite, two `A`-linear maps `u, u' : M → N` with
   `u ⊗ 1_R = u' ⊗ 1_R` satisfy `u ⊗ 1_{S j} = u' ⊗ 1_{S j}` for some `j`. -/
@[stacks 05N7 "The colimit is a `DirectedSystem` of `A`-algebras whose comparison map
`colim_j S j → R` is bijective, as in 00QN; items (2) and (3) are stated over an arbitrary base
ring `A` and with the finiteness hypotheses of 05LI (3) and (1), of which they are instances, the
source's form being `A = R_λ` and the system restricted to `μ ≥ λ`; `φ = φ_μ ⊗ 1_R` is the
commuting square with the canonical maps `LinearMap.rTensor M (algebraMap (S j) R)`. See the
module docstring.", ega "IV 8.5.3" "affine case"]
public theorem exists_finitePresentation_and_baseChange_eq_of_lift_bijective
    {J : Type w} [Preorder J] [Nonempty J] [IsDirectedOrder J] {A : Type u} [CommRing A]
    {S : J → Type v} [∀ j, CommRing (S j)] [∀ j, Algebra A (S j)]
    (f : ∀ i j, i ≤ j → S i →ₐ[A] S j) [DirectedSystem S fun i j h ↦ ⇑(f i j h)]
    {R : Type v} [CommRing R] [Algebra A R] [∀ j, Algebra (S j) R]
    [∀ j, IsScalarTower A (S j) R]
    (hf : ∀ i j (h : i ≤ j) (x : S i), algebraMap (S j) R (f i j h x) = algebraMap (S i) R x)
    (hR : Function.Bijective (DirectLimit.Algebra.lift S f R
      (fun j ↦ IsScalarTower.toAlgHom A (S j) R) hf)) :
    (∀ (M : Type t) [AddCommGroup M] [Module R M] [Module.FinitePresentation R M],
        ∃ (j : J) (Mj : Type v) (_ : AddCommGroup Mj) (_ : Module (S j) Mj),
          Module.FinitePresentation (S j) Mj ∧ Nonempty (R ⊗[S j] Mj ≃ₗ[R] M)) ∧
    (∀ (M : Type t) [AddCommGroup M] [Module A M] [Module.FinitePresentation A M]
        (N : Type t') [AddCommGroup N] [Module A N] (φ : R ⊗[A] M →ₗ[R] R ⊗[A] N),
        ∃ (j : J) (φj : S j ⊗[A] M →ₗ[S j] S j ⊗[A] N), ∀ x : S j ⊗[A] M,
          φ (LinearMap.rTensor M (IsScalarTower.toAlgHom A (S j) R).toLinearMap x) =
            LinearMap.rTensor N (IsScalarTower.toAlgHom A (S j) R).toLinearMap (φj x)) ∧
    (∀ (M : Type t) [AddCommGroup M] [Module A M] [Module.Finite A M]
        (N : Type t') [AddCommGroup N] [Module A N] (u u' : M →ₗ[A] N),
        u.baseChange R = u'.baseChange R →
          ∃ j : J, u.baseChange (S j) = u'.baseChange (S j)) := by
  have hsurj := Stacks.ColimitPresentation.FPModules.exists_algebraMap_eq f hf hR
  have hinj := Stacks.ColimitPresentation.FPModules.exists_map_eq_zero f hf hR
  have hc := Stacks.ColimitPresentation.FPModules.isModuleColimit f hf hsurj hinj
  refine ⟨fun M _ _ _ ↦
    Stacks.ColimitPresentation.FPModules.exists_finitePresentation f hf hsurj M, ?_, ?_⟩
  · intro M _ _ _ N _ _ φ
    obtain ⟨i, φi, hφi⟩ := Stacks.FinitePresentation.ColimitDescent.statement_three
      (fun i j (h : i ≤ j) ↦ f i j h)
      (fun j ↦ IsScalarTower.toAlgHom A (S j) R)
      ⟨fun i x ↦ DirectedSystem.map_self' f x,
        fun _ _ _ hij hjk x ↦ DirectedSystem.map_map' f hij hjk x⟩
      (fun _ _ hij x ↦ hf _ _ hij x) (hc N) inferInstance φ
    exact ⟨i, φi, fun x ↦ LinearMap.congr_fun hφi x⟩
  · intro M _ _ _ N _ _ u u' h
    exact Stacks.FinitePresentation.ColimitDescent.statement_one (fun i j (h : i ≤ j) ↦ f i j h)
      (fun j ↦ IsScalarTower.toAlgHom A (S j) R) (hc N) inferInstance u u' h

end Module

namespace Stacks.ColimitPresentation.FPModules

/-- For a directed system `S` of `A`-algebras whose colimit is `R`: every finitely presented
`R`-module is the base change of a finitely presented `S j`-module; every `R`-linear map
`R ⊗[A] M → R ⊗[A] N` with `M` finitely presented descends to an `S j`-linear map
`S j ⊗[A] M → S j ⊗[A] N`; and two `A`-linear maps `M → N` with `M` finite whose base changes to
`R` agree have equal base changes to some `S j`. -/
public alias solution := Module.exists_finitePresentation_and_baseChange_eq_of_lift_bijective

end Stacks.ColimitPresentation.FPModules

end
