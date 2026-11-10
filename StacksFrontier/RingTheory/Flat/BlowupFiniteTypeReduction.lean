module

public import Mathlib.Algebra.Exact.Basic
public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.LinearAlgebra.TensorProduct.Prod
public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.TensorProduct.Basic
public import StacksFrontier.RingTheory.Blowup.StrictTransform
public import StacksFrontier.RingTheory.Flat.Prod

/-!
# The finite-type reduction for flattening by blowing up

This file collects the ring-theoretic ingredients of the first step in the proof of
[Stacks, Tag 053I]: the reduction of the general case, where `S` is a finite type algebra over
the local domain `R`, to the case where `S` is a polynomial algebra. There one writes
`S = R[x₁, …, xₙ]/J` and works with the module `N = S ⊕ M` over `P = R[x₁, …, xₙ]`, reading off
the two summands of `N` after passing to the strict transform.

Nothing here involves the blowup algebra except the last section, and none of it needs the
flatness results about blowups; the statements are elementary facts about finite presentation,
flatness, base change and strict transforms.

## Main results

* `Algebra.FinitePresentation.of_surjective_of_module_finitePresentation`: if `T` is a finitely
  presented `C`-algebra, `T → E` is surjective and `E` is finitely presented as a `T`-module, then
  `E` is a finitely presented `C`-algebra. This is the source's step "hence `S_{I,a}` is finitely
  presented as an `R[I/a]`-algebra".
* `Module.FinitePresentation.prod_iff`: a product of two modules is finitely presented if and only
  if both factors are.
* `strictTransform.prodEquiv`: the strict transform of a product is the product of the strict
  transforms, which is what lets one read off `S_{I,a}` and `M_{I,a}` from `N_{I,a}`.
* `Module.FinitePresentation.of_restrictScalars_of_finiteType`: **Stacks 0561** in the direction
  the source uses, namely from finite presentation over the base to finite presentation over a
  finite type algebra.

That base change commutes with products, `C ⊗[R] (X × Y) ≃ₗ[C] (C ⊗[R] X) × (C ⊗[R] Y)`, is
Mathlib's `TensorProduct.prodRight`; it is the input to `strictTransform.prodEquiv`.

## References

* [Stacks Project, Tag 053I](https://stacks.math.columbia.edu/tag/053I)
* [Stacks Project, Tag 0561](https://stacks.math.columbia.edu/tag/0561)
-/

@[expose] public section

universe u v w

open scoped TensorProduct

/-! ### Finite presentation as a module upgrades to finite presentation as an algebra -/

section AlgebraFinitePresentation

variable {C : Type u} [CommRing C] {T : Type v} [CommRing T] [Algebra C T] {E : Type w}
  [CommRing E] [Algebra C E] [Algebra T E] [IsScalarTower C T E]

/-- If `T` is a finitely presented `C`-algebra, `E` is a `T`-algebra whose structure map is
surjective, and `E` is finitely presented as a `T`-module, then `E` is a finitely presented
`C`-algebra.

The point is that finite presentation of the cyclic `T`-module `E` says exactly that the kernel of
`T → E` is a finitely generated ideal, which is what finite presentation as an algebra asks for. -/
theorem Algebra.FinitePresentation.of_surjective_of_module_finitePresentation
    [Algebra.FinitePresentation C T] [Module.FinitePresentation T E]
    (h : Function.Surjective (algebraMap T E)) : Algebra.FinitePresentation C E := by
  refine Algebra.FinitePresentation.of_surjective (f := IsScalarTower.toAlgHom C T E) h ?_
  exact Module.FinitePresentation.fg_ker (Algebra.linearMap T E) h

/-- A quotient of a finitely presented `C`-algebra `T` which is finitely presented as a
`T`-module is a finitely presented `C`-algebra. -/
theorem Algebra.FinitePresentation.quotient_of_module_finitePresentation
    [Algebra.FinitePresentation C T] (J : Ideal T)
    [Module.FinitePresentation T (T ⧸ J)] : Algebra.FinitePresentation C (T ⧸ J) :=
  Algebra.FinitePresentation.of_surjective_of_module_finitePresentation
    Ideal.Quotient.mk_surjective

end AlgebraFinitePresentation

/-- The special case of `Algebra.FinitePresentation.of_surjective_of_module_finitePresentation`
used in [Stacks, Tag 053I]: a quotient `E` of a polynomial algebra `T = C[x₁, …, xₙ]` which is
finitely presented as a `T`-module is a finitely presented `C`-algebra. -/
theorem Algebra.FinitePresentation.of_mvPolynomial_module_finitePresentation
    {C : Type u} [CommRing C] {n : ℕ} {E : Type w} [CommRing E] [Algebra C E]
    [Algebra (MvPolynomial (Fin n) C) E] [IsScalarTower C (MvPolynomial (Fin n) C) E]
    [Module.FinitePresentation (MvPolynomial (Fin n) C) E]
    (h : Function.Surjective (algebraMap (MvPolynomial (Fin n) C) E)) :
    Algebra.FinitePresentation C E :=
  Algebra.FinitePresentation.of_surjective_of_module_finitePresentation h

/-! ### Finite presentation for products -/

section Prod

variable {T : Type u} [CommRing T] {X : Type v} [AddCommGroup X] [Module T X] {Y : Type w}
  [AddCommGroup Y] [Module T Y]

/-- A direct summand of a finitely presented module whose complement is finitely presented is
finitely presented: the first factor of a finitely presented product. -/
theorem Module.FinitePresentation.of_prod_left [Module.FinitePresentation T (X × Y)] :
    Module.FinitePresentation T X :=
  Module.finitePresentation_of_split_exact (LinearMap.inl T X Y) (LinearMap.snd T X Y)
    (LinearMap.inr T X Y) (LinearMap.snd_comp_inr T X Y) LinearMap.inl_injective
    Function.Exact.inl_snd

/-- A direct summand of a finitely presented module whose complement is finitely presented is
finitely presented: the second factor of a finitely presented product. -/
theorem Module.FinitePresentation.of_prod_right [Module.FinitePresentation T (X × Y)] :
    Module.FinitePresentation T Y :=
  Module.finitePresentation_of_split_exact (LinearMap.inr T X Y) (LinearMap.fst T X Y)
    (LinearMap.inl T X Y) (LinearMap.fst_comp_inl T X Y) LinearMap.inr_injective
    Function.Exact.inr_fst

/-- A product of two modules is finitely presented if and only if both factors are finitely
presented. -/
theorem Module.FinitePresentation.prod_iff :
    Module.FinitePresentation T (X × Y) ↔
      Module.FinitePresentation T X ∧ Module.FinitePresentation T Y := by
  refine ⟨fun _ => ⟨Module.FinitePresentation.of_prod_left (Y := Y),
    Module.FinitePresentation.of_prod_right (X := X)⟩, fun h => ?_⟩
  obtain ⟨_, _⟩ := h
  exact Module.FinitePresentation.prod X Y

end Prod

/-! ### The strict transform of a product -/

section StrictTransform

variable {R : Type u} [CommRing R] (I : Ideal R) (a : R) [Fact (a ∈ I)] (X : Type v)
  [AddCommGroup X] [Module R X] (Y : Type w) [AddCommGroup Y] [Module R Y]

/-- Being `a`-power torsion is witnessed by all large enough powers of `a`. -/
theorem strictTransform.smul_pow_eq_zero_of_le {M : Type*} [AddCommGroup M] [Module R M]
    {x : TensorProduct R (Blowup I a) M} {n m : ℕ} (hnm : n ≤ m)
    (hx : algebraMap R (Blowup I a) a ^ n • x = 0) :
    algebraMap R (Blowup I a) a ^ m • x = 0 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hnm
  rw [pow_add, mul_comm, mul_smul, hx, smul_zero]

/-- The `a`-power torsion of a base change of a product is the product of the `a`-power torsions,
read through `TensorProduct.prodRight`. -/
theorem strictTransform.mem_torsionSubmodule_prod_iff
    {z : TensorProduct R (Blowup I a) (X × Y)} :
    z ∈ strictTransform.torsionSubmodule I a (X × Y) ↔
      (TensorProduct.prodRight R (Blowup I a) (Blowup I a) X Y z).1 ∈
          strictTransform.torsionSubmodule I a X ∧
        (TensorProduct.prodRight R (Blowup I a) (Blowup I a) X Y z).2 ∈
          strictTransform.torsionSubmodule I a Y := by
  simp only [strictTransform.mem_torsionSubmodule_iff]
  constructor
  · rintro ⟨n, hn⟩
    have h := congrArg (TensorProduct.prodRight R (Blowup I a) (Blowup I a) X Y) hn
    simp only [map_smul, map_zero, Prod.ext_iff, Prod.smul_fst, Prod.smul_snd, Prod.fst_zero,
      Prod.snd_zero] at h
    exact ⟨⟨n, h.1⟩, ⟨n, h.2⟩⟩
  · rintro ⟨⟨n, hn⟩, m, hm⟩
    refine ⟨max n m, (map_eq_zero_iff _
      (TensorProduct.prodRight R (Blowup I a) (Blowup I a) X Y).injective).mp ?_⟩
    rw [map_smul]
    exact Prod.ext (strictTransform.smul_pow_eq_zero_of_le I a (le_max_left n m) hn)
      (strictTransform.smul_pow_eq_zero_of_le I a (le_max_right n m) hm)

/-- The comparison map from the strict transform of a product to the product of the strict
transforms, induced by `TensorProduct.prodRight`. -/
noncomputable def strictTransform.toProd :
    strictTransform I a (X × Y) →ₗ[Blowup I a]
      strictTransform I a X × strictTransform I a Y :=
  Submodule.liftQ (strictTransform.torsionSubmodule I a (X × Y))
    (LinearMap.prodMap (strictTransform.mkQ I a X) (strictTransform.mkQ I a Y) ∘ₗ
      (TensorProduct.prodRight R (Blowup I a) (Blowup I a) X Y).toLinearMap)
    fun z hz => by
      obtain ⟨h1, h2⟩ := (strictTransform.mem_torsionSubmodule_prod_iff I a X Y).mp hz
      exact Prod.ext ((Submodule.Quotient.mk_eq_zero _).mpr h1)
        ((Submodule.Quotient.mk_eq_zero _).mpr h2)

/-- The comparison map splits the class of `z` into the classes of the two components of `z`. -/
@[simp]
theorem strictTransform.toProd_mkQ (z : TensorProduct R (Blowup I a) (X × Y)) :
    strictTransform.toProd I a X Y (strictTransform.mkQ I a (X × Y) z) =
      (strictTransform.mkQ I a X
          ((TensorProduct.prodRight R (Blowup I a) (Blowup I a) X Y) z).1,
        strictTransform.mkQ I a Y
          ((TensorProduct.prodRight R (Blowup I a) (Blowup I a) X Y) z).2) :=
  rfl

/-- The strict transform of a product of `R`-modules is the product of their strict transforms.

This is what lets one read off the strict transforms of the two summands of `N = S ⊕ M` in the
proof of [Stacks, Tag 053I]. -/
noncomputable def strictTransform.prodEquiv :
    strictTransform I a (X × Y) ≃ₗ[Blowup I a]
      strictTransform I a X × strictTransform I a Y := by
  refine LinearEquiv.ofBijective (strictTransform.toProd I a X Y)
    ⟨fun u v huv => ?_, fun w => ?_⟩
  · obtain ⟨z, rfl⟩ := strictTransform.mkQ_surjective I a (X × Y) u
    obtain ⟨z', rfl⟩ := strictTransform.mkQ_surjective I a (X × Y) v
    rw [strictTransform.toProd_mkQ, strictTransform.toProd_mkQ, Prod.ext_iff] at huv
    refine (Submodule.Quotient.eq _).mpr
      ((strictTransform.mem_torsionSubmodule_prod_iff I a X Y).mpr ?_)
    rw [map_sub]
    exact ⟨(Submodule.Quotient.eq _).mp huv.1, (Submodule.Quotient.eq _).mp huv.2⟩
  · obtain ⟨u, hu⟩ := strictTransform.mkQ_surjective I a X w.1
    obtain ⟨v, hv⟩ := strictTransform.mkQ_surjective I a Y w.2
    refine ⟨strictTransform.mkQ I a (X × Y)
      ((TensorProduct.prodRight R (Blowup I a) (Blowup I a) X Y).symm (u, v)), ?_⟩
    rw [strictTransform.toProd_mkQ]
    simp only [LinearEquiv.apply_symm_apply]
    exact Prod.ext hu hv

/-- The identification of the strict transform of a product with the product of the strict
transforms sends the class of `z` to the classes of the two components of `z`. -/
@[simp]
theorem strictTransform.prodEquiv_mkQ (z : TensorProduct R (Blowup I a) (X × Y)) :
    strictTransform.prodEquiv I a X Y (strictTransform.mkQ I a (X × Y) z) =
      (strictTransform.mkQ I a X
          ((TensorProduct.prodRight R (Blowup I a) (Blowup I a) X Y) z).1,
        strictTransform.mkQ I a Y
          ((TensorProduct.prodRight R (Blowup I a) (Blowup I a) X Y) z).2) :=
  rfl

end StrictTransform

/-! ### Stacks 0561 in the direction the reduction needs -/

/-- **Stacks 0561.** Let `R → S` be a ring map of finite type and let `M` be an `S`-module which
is finitely presented as an `R`-module. Then `M` is finitely presented as an `S`-module.

Mathlib's `Module.FinitePresentation.trans` is the converse implication: it deduces finite
presentation over `R` from finite presentation over `S` together with finite presentation of `S`
over `R`. Mathlib's own declaration carrying the tag `0561`,
`Algebra.FinitePresentation.of_restrict_scalars_finitePresentation`, is not this lemma but the
analogue for algebras in place of modules. -/
@[stacks 0561 "the module statement, not the analogue for algebras"]
theorem Module.FinitePresentation.of_restrictScalars_of_finiteType (R S M : Type*) [CommRing R]
    [CommRing S] [Algebra R S] [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]
    [Algebra.FiniteType R S] [Module.FinitePresentation R M] : Module.FinitePresentation S M := by
  classical
  obtain ⟨σ, hσ⟩ := (Algebra.FiniteType.out : (⊤ : Subalgebra R S).FG)
  obtain ⟨τ, hτ⟩ : (⊤ : Submodule R M).FG := Module.Finite.fg_top
  -- The multiplication map `S ⊗[R] M → M`.
  set f : S ⊗[R] M →ₗ[S] M := LinearMap.liftBaseChange S LinearMap.id with hf_def
  have hf : Function.Surjective f := fun x => ⟨1 ⊗ₜ x, by simp [hf_def]⟩
  -- The candidate finite generating set of the kernel.
  set G : Set (S ⊗[R] M) :=
    (fun p : S × M => p.1 ⊗ₜ p.2 - 1 ⊗ₜ (p.1 • p.2)) '' (σ ×ˢ τ : Finset (S × M))
  set K : Submodule S (S ⊗[R] M) := Submodule.span S G with hK_def
  have hKle : K ≤ LinearMap.ker f := by
    rw [hK_def, Submodule.span_le]
    rintro _ ⟨⟨s, x⟩, -, rfl⟩
    simp [hf_def]
  -- Work in the quotient by `K`.
  set q : S ⊗[R] M →ₗ[S] (S ⊗[R] M) ⧸ K := K.mkQ with hq_def
  -- Step 1: modulo `K` one may move any scalar from an algebra generator across the tensor sign.
  have step1 : ∀ s ∈ σ, ∀ x : M, q (s ⊗ₜ x) = q (1 ⊗ₜ (s • x)) := by
    intro s hs x
    have hx : x ∈ Submodule.span R (τ : Set M) := hτ ▸ Submodule.mem_top
    induction hx using Submodule.span_induction with
    | mem y hy =>
      refine sub_eq_zero.mp ?_
      rw [← map_sub]
      exact (Submodule.Quotient.mk_eq_zero _).mpr
        (Submodule.subset_span ⟨(s, y), by simpa using ⟨hs, hy⟩, rfl⟩)
    | zero => simp
    | add y z _ _ hy hz =>
      rw [TensorProduct.tmul_add, smul_add, TensorProduct.tmul_add, map_add, map_add, hy, hz]
    | smul r y _ hy =>
      rw [TensorProduct.tmul_smul, smul_comm, TensorProduct.tmul_smul,
        LinearMap.map_smul_of_tower, LinearMap.map_smul_of_tower, hy]
  -- Step 2: the image of `M` in the quotient is an `R`-submodule stable under all of `S`.
  set V : Submodule R ((S ⊗[R] M) ⧸ K) :=
    LinearMap.range ((q.restrictScalars R) ∘ₗ TensorProduct.mk R S M 1)
  have hmemV : ∀ x : M, q (1 ⊗ₜ x) ∈ V := fun x => ⟨x, rfl⟩
  have hsmul : ∀ (s : S) (x : M), s • q (1 ⊗ₜ x) = q (s ⊗ₜ x) := fun s x => by
    rw [← map_smul, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  have hstable : ∀ s : S, ∀ u ∈ V, s • u ∈ V := by
    have hW : (σ : Set S) ⊆ {s : S | ∀ u ∈ V, s • u ∈ V} := by
      rintro s hs u ⟨x, rfl⟩
      have : s • q (1 ⊗ₜ x) = q (1 ⊗ₜ (s • x)) := (hsmul s x).trans (step1 s hs x)
      rw [show ((q.restrictScalars R) ∘ₗ TensorProduct.mk R S M 1) x = q (1 ⊗ₜ x) from rfl, this]
      exact hmemV _
    intro s
    have : s ∈ Algebra.adjoin R (σ : Set S) := hσ ▸ Algebra.mem_top
    induction this using Algebra.adjoin_induction with
    | mem s hs => exact hW hs
    | algebraMap r => intro u hu; rw [algebraMap_smul]; exact V.smul_mem r hu
    | add s t _ _ hs ht => intro u hu; rw [add_smul]; exact V.add_mem (hs u hu) (ht u hu)
    | mul s t _ _ hs ht => intro u hu; rw [mul_smul]; exact hs _ (ht u hu)
  have hall : ∀ z : S ⊗[R] M, q z ∈ V := by
    intro z
    induction z using TensorProduct.inductionOn with
    | tmul s x =>
      rw [← hsmul]
      exact hstable s _ (hmemV x)
    | add z z' hz hz' =>
      rw [map_add]
      exact V.add_mem hz hz'
  have hVtop : V = ⊤ := eq_top_iff.mpr fun u _ => by
    obtain ⟨z, rfl⟩ := Submodule.mkQ_surjective K u
    exact hall z
  -- Step 3: the induced map to `M` is injective, so the kernel of `f` is exactly `K`.
  have hker : LinearMap.ker f = K := by
    refine le_antisymm (fun z hz => ?_) hKle
    have hinj : Function.Injective (K.liftQ f hKle) := by
      intro u u' huu'
      obtain ⟨x, rfl⟩ : u ∈ V := hVtop ▸ Submodule.mem_top
      obtain ⟨x', rfl⟩ : u' ∈ V := hVtop ▸ Submodule.mem_top
      have : x = x' := by simpa [hq_def, hf_def] using huu'
      rw [this]
    have : K.liftQ f hKle (q z) = K.liftQ f hKle 0 := by
      simpa [hq_def, hf_def] using hz
    simpa [hq_def] using (Submodule.Quotient.mk_eq_zero K).mp (hinj this)
  refine Module.finitePresentation_of_surjective f hf ?_
  rw [hker, hK_def]
  exact Submodule.fg_span ((σ ×ˢ τ : Finset (S × M)).finite_toSet.image _)
