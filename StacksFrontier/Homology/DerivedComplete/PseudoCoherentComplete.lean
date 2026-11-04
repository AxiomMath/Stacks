module

public import Mathlib
public import StacksFrontier.Algebra.Homology.PseudoCoherent
public import StacksFrontier.Homology.DerivedComplete.NakayamaModule

/-!
# Derived completeness of pseudo-coherent objects

Let `A` be a commutative ring and `I ⊆ A` an ideal. If `A`, regarded as a module over itself, is
derived complete with respect to `I`, then every pseudo-coherent object of `D(A)` is derived
complete with respect to `I`.

## Main definitions

There are no new definitions.

## Main results

* `isDerivedComplete_iff_forall_isDerivedCompleteModule_homology`: derived completeness of an
  object of `D(A)` is detected on its cohomology modules.
* `IsDerivedCompleteModule.of_iso`, `IsDerivedCompleteModule.kernel`,
  `IsDerivedCompleteModule.cokernel`, `IsDerivedCompleteModule.of_finite_free`: the closure
  properties of derived complete modules used below.
* `isDerivedComplete_of_isPseudoCoherent`: pseudo-coherent objects over a derived complete ring
  are derived complete (Stacks 0A05).

## Implementation notes

Pseudo-coherence of `K` is spelled out as in Stacks 064Q (2): `K` is isomorphic in `D(A)` to the
image of a bounded-above cochain complex whose terms are finite free `A`-modules. The ring is
regarded as an object of its own module category, and countable products in `D(A)` are assumed
through `HasProductsOfShape ℕ`.

The proof tests derived completeness on cohomology and then only needs that the finite free
modules are derived complete and that derived complete modules are closed under kernels and
cokernels. Both closure properties are obtained from the description of derived completeness as
solvability of the recurrence `aₙ - f aₙ₊₁ = bₙ` in
`StacksFrontier.Homology.DerivedComplete.NakayamaModule`.

## References

* [The Stacks Project, Tag 0A05](https://stacks.math.columbia.edu/tag/0A05)
* [The Stacks Project, Tag 064Q](https://stacks.math.columbia.edu/tag/064Q)
* [Bhatt--Scholze, *Projectivity of the Witt vector affine Grassmannian*][BS]
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

attribute [local instance] HasDerivedCategory.standard

noncomputable section

universe u

/-! ### Detecting derived completeness on cohomology -/

section Homology

variable {A : Type u} [CommRing A]
  [HasProductsOfShape ℕ (DerivedCategory (ModuleCat.{u} A))]

/-- Derived completeness of a module at `f` is invertibility of `oneSubSmulShift` on the module
itself. -/
theorem isDerivedCompleteAt_single_iff_isIso_oneSubSmulShift (M : ModuleCat.{u} A) (f : A) :
    IsDerivedCompleteAt ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M) f ↔
      IsIso (oneSubSmulShift M f) :=
  (bijective_recurrence_iff_isDerivedCompleteAt_single M f).trans
    (isIso_oneSubSmulShift_moduleCat_iff M f).symm

/-- An object of `D(A)` is derived complete with respect to `I` exactly when all of its
cohomology modules are derived complete with respect to `I`. -/
theorem isDerivedComplete_iff_forall_isDerivedCompleteModule_homology (I : Ideal A)
    (K : DerivedCategory (ModuleCat.{u} A)) :
    IsDerivedComplete I K ↔
      ∀ n : ℤ,
        IsDerivedCompleteModule I
          ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) n).obj K) := by
  have key : ∀ f : A, IsDerivedCompleteAt K f ↔
      ∀ n : ℤ,
        IsDerivedCompleteAt
          ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj
            ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) n).obj K)) f := by
    intro f
    rw [isDerivedCompleteAt_iff_isIso, DerivedCategory.isIso_iff]
    refine forall_congr' fun n ↦ ?_
    rw [isIso_homology_map_oneSubSmulShift_iff,
      isDerivedCompleteAt_single_iff_isIso_oneSubSmulShift]
  constructor
  · intro h n f hf
    exact (key f).mp (h f hf) n
  · intro h f hf
    exact (key f).mpr fun n => h n f hf

end Homology

/-! ### Closure properties of derived complete modules -/

section Closure

variable {A : Type u} [CommRing A]
  [HasProductsOfShape ℕ (DerivedCategory (ModuleCat.{u} A))] {I : Ideal A}

/-- Derived completeness of a module only depends on its isomorphism class. -/
theorem IsDerivedCompleteModule.of_iso {M N : ModuleCat.{u} A}
    (hM : IsDerivedCompleteModule I M) (e : M ≅ N) : IsDerivedCompleteModule I N := by
  intro f hf
  rw [isDerivedCompleteAt_iff_isIso]
  exact (isIso_oneSubSmulShift_congr
    ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).mapIso e) f).mp (hM f hf)

/-- Derived completeness of a module transports along an `A`-linear equivalence. -/
theorem IsDerivedCompleteModule.of_linearEquiv {M N : ModuleCat.{u} A}
    (hM : IsDerivedCompleteModule I M) (e : M ≃ₗ[A] N) : IsDerivedCompleteModule I N :=
  hM.of_iso (linearEquivIsoModuleIso.hom e)

/-- A module with at most one element is derived complete. -/
theorem IsDerivedCompleteModule.of_subsingleton (M : ModuleCat.{u} A) [Subsingleton M] :
    IsDerivedCompleteModule I M := by
  rw [bijective_recurrence_iff_isDerivedCompleteModule]
  exact fun f _ =>
    ⟨fun _ _ _ => Subsingleton.elim _ _, fun a => ⟨a, Subsingleton.elim _ _⟩⟩

/-- An arbitrary product of derived complete modules is derived complete. -/
theorem IsDerivedCompleteModule.pi {ι : Type u} (P : ι → Type u)
    [∀ i, AddCommGroup (P i)] [∀ i, Module A (P i)]
    (hP : ∀ i, IsDerivedCompleteModule I (ModuleCat.of A (P i))) :
    IsDerivedCompleteModule I (ModuleCat.of A (∀ i, P i)) := by
  rw [bijective_recurrence_iff_isDerivedCompleteModule]
  intro f hf
  have hcomp : ∀ i,
      Function.Bijective (fun a : ℕ → P i => fun n => a n - f • a (n + 1)) := fun i =>
    (bijective_recurrence_iff_isDerivedCompleteModule I (ModuleCat.of A (P i))).mp (hP i) f hf
  constructor
  · intro a b hab
    funext n i
    have hi : (fun m => a m i) = fun m => b m i := by
      apply (hcomp i).1
      funext m
      simpa using congrFun (congrFun hab m) i
    exact congrFun hi n
  · intro b
    choose a ha using fun i => (hcomp i).2 (fun n => b n i)
    refine ⟨fun n i => a i n, ?_⟩
    funext n i
    exact congrFun (ha i) n

/-- A finite free module over a derived complete ring is derived complete. -/
theorem IsDerivedCompleteModule.of_finite_free
    (hA : IsDerivedCompleteModule I (ModuleCat.of A A)) (M : ModuleCat.{u} A)
    [Module.Finite A M] [Module.Free A M] : IsDerivedCompleteModule I M := by
  rcases subsingleton_or_nontrivial A with _ | _
  · have : Subsingleton M := Module.subsingleton A M
    exact IsDerivedCompleteModule.of_subsingleton M
  · let ι := Module.Free.ChooseBasisIndex A M
    have : Finite ι := Module.Finite.finite_basis (Module.Free.chooseBasis A M)
    have hpi : IsDerivedCompleteModule I (ModuleCat.of A (ι → A)) :=
      IsDerivedCompleteModule.pi (fun _ : ι => A) fun _ => hA
    exact hpi.of_linearEquiv
      ((Finsupp.linearEquivFunOnFinite A A ι).symm.trans
        (Module.Free.chooseBasis A M).repr.symm)

/-- The kernel of a morphism of derived complete modules is derived complete. -/
theorem IsDerivedCompleteModule.kernel {M N : ModuleCat.{u} A} (φ : M ⟶ N)
    (hM : IsDerivedCompleteModule I M) (hN : IsDerivedCompleteModule I N) :
    IsDerivedCompleteModule I (Limits.kernel φ) := by
  have hsub : IsDerivedCompleteModule I
      (ModuleCat.of A (LinearMap.ker φ.hom)) := by
    rw [bijective_recurrence_iff_isDerivedCompleteModule] at hM hN ⊢
    intro f hf
    have hMf := hM f hf
    have hNf := hN f hf
    constructor
    · intro a b hab
      have hval : (fun n => (a n : M)) = fun n => (b n : M) := by
        apply hMf.1
        funext n
        simpa using congrArg (fun y : LinearMap.ker φ.hom => (y : M)) (congrFun hab n)
      funext n
      exact Subtype.ext (congrFun hval n)
    · intro b
      obtain ⟨x, hx⟩ := hMf.2 fun n => (b n : M)
      have hx' : ∀ n, x n - f • x (n + 1) = (b n : M) := fun n => congrFun hx n
      have hker : ∀ n, x n ∈ LinearMap.ker φ.hom := by
        have hzero : (fun n => φ.hom (x n)) = fun _ : ℕ => (0 : N) := by
          apply hNf.1
          funext n
          have : φ.hom (x n) - f • φ.hom (x (n + 1)) = 0 := by
            rw [← map_smul, ← map_sub, hx' n]
            exact LinearMap.mem_ker.mp (b n).2
          simpa using this
        intro n
        exact LinearMap.mem_ker.mpr (congrFun hzero n)
      refine ⟨fun n => ⟨x n, hker n⟩, ?_⟩
      funext n
      exact Subtype.ext (hx' n)
  exact hsub.of_iso (ModuleCat.kernelIsoKer φ).symm

/-- The cokernel of a morphism of derived complete modules is derived complete. -/
theorem IsDerivedCompleteModule.cokernel {M N : ModuleCat.{u} A} (φ : M ⟶ N)
    (hM : IsDerivedCompleteModule I M) (hN : IsDerivedCompleteModule I N) :
    IsDerivedCompleteModule I (Limits.cokernel φ) := by
  have hquot : IsDerivedCompleteModule I
      (ModuleCat.of A (N ⧸ LinearMap.range φ.hom)) := by
    rw [bijective_recurrence_iff_isDerivedCompleteModule] at hM hN ⊢
    intro f hf
    have hMf := hM f hf
    have hNf := hN f hf
    exact bijective_recurrence_quotient_range f φ.hom hMf.2 hNf
  exact hquot.of_iso (ModuleCat.cokernelIsoRangeQuotient φ).symm

/-- The cohomology of a cochain complex of derived complete modules is derived complete. -/
theorem IsDerivedCompleteModule.homology (E : CochainComplex (ModuleCat.{u} A) ℤ)
    (hE : ∀ i : ℤ, IsDerivedCompleteModule I (E.X i)) (i : ℤ) :
    IsDerivedCompleteModule I (E.homology i) := by
  have hker : IsDerivedCompleteModule I (Limits.kernel (E.sc i).g) :=
    IsDerivedCompleteModule.kernel _ (hE _) (hE _)
  exact (IsDerivedCompleteModule.cokernel
    (Limits.kernel.lift (E.sc i).g (E.sc i).f (E.sc i).zero) (hE _) hker).of_iso
      (E.sc i).homologyIsoCokernelLift.symm

end Closure

/-! ### Pseudo-coherent objects -/

/-- **Stacks 0A05.** A pseudo-coherent object over a ring that is derived complete with respect
to `I` is itself derived complete with respect to `I`. Pseudo-coherence is spelled out as in
Stacks 064Q (2): `K` is represented by a bounded-above complex of finite free modules. -/
@[stacks 0A05]
theorem isDerivedComplete_of_isPseudoCoherent
    (A : Type u) [CommRing A] (I : Ideal A)
    [HasProductsOfShape ℕ (DerivedCategory (ModuleCat.{u} A))] :
    IsDerivedCompleteModule I (ModuleCat.of A A) →
      ∀ K : DerivedCategory (ModuleCat.{u} A),
        (∃ E : CochainComplex (ModuleCat.{u} A) ℤ,
            ((∃ b : ℤ, E.IsStrictlyLE b) ∧
              ∀ i : ℤ, Module.Finite A (E.X i) ∧ Module.Free A (E.X i)) ∧
            Nonempty (DerivedCategory.Q.obj E ≅ K)) →
          IsDerivedComplete I K := by
  intro hA K hK
  obtain ⟨E, ⟨-, hfree⟩, ⟨e⟩⟩ := hK
  rw [isDerivedComplete_iff_forall_isDerivedCompleteModule_homology]
  intro i
  have hterm : ∀ j : ℤ, IsDerivedCompleteModule I (E.X j) := by
    intro j
    have : Module.Finite A (E.X j) := (hfree j).1
    have : Module.Free A (E.X j) := (hfree j).2
    exact IsDerivedCompleteModule.of_finite_free hA (E.X j)
  exact (IsDerivedCompleteModule.homology E hterm i).of_iso
    ((DerivedCategory.homologyFunctorFactors (ModuleCat.{u} A) i).symm.app E ≪≫
      (DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).mapIso e)

end

end
