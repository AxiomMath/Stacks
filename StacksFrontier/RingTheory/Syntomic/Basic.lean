module

public import StacksFrontier.RingTheory.RingHom.FinitePresentation
public import StacksFrontier.RingTheory.Syntomic.Defs

@[expose] public section

/-!
# Syntomic ring maps and relative global complete intersections

Let `R → S` be a ring map. It is *syntomic* (`IsSyntomic`) if it is flat, of finite
presentation, and all of its fibre rings `S ⊗_R κ(p)` are local complete intersections over
`κ(p)`. It is a *relative global complete intersection* if it admits a presentation
`S = R[x_1, …, x_n]/(f_1, …, f_c)` all of whose nonempty fibres have dimension `n - c`.

Throughout, `κ(p)` denotes the residue field of `R` at the prime `p`, realized as
`IsLocalRing.ResidueField (Localization.AtPrime p)`, and the fibre ring at `p` is the base
change `TensorProduct R S κ(p)` with the `κ(p)`-algebra structure coming from the right
tensor factor (`Algebra.TensorProduct.rightAlgebra`), exactly as in `IsSyntomic`.

## Main definitions

* `IsRelativeGlobalCompleteIntersection`: relative global complete intersections.

## Main results

* `IsRelativeGlobalCompleteIntersection.finitePresentation`: a relative global complete
  intersection is of finite presentation.
* `IsRelativeGlobalCompleteIntersection.isGlobalCompleteIntersectionOver_fibre`: every fibre
  of a relative global complete intersection is a *global* complete intersection over the
  residue field, with the same numbers `n` and `c`.
* `IsRelativeGlobalCompleteIntersection.isLocalCompleteIntersectionOver_fibre`: hence a local
  complete intersection over the residue field.
* `IsRelativeGlobalCompleteIntersection.isSyntomic_of_flat`: a *flat* relative global complete
  intersection is syntomic.

## References

* [StacksProject 00SL](https://stacks.math.columbia.edu/tag/00SL)
* [StacksProject 00SP](https://stacks.math.columbia.edu/tag/00SP)
-/

@[expose] public section

open TensorProduct

/-- Composing an algebra map with an isomorphism does not change its kernel. -/
private theorem ker_algEquiv_comp {k : Type*} [CommSemiring k] {A B C : Type*} [Semiring A]
    [Semiring B] [Semiring C] [Algebra k A] [Algebra k B] [Algebra k C]
    (e : B ≃ₐ[k] C) (φ : A →ₐ[k] B) :
    RingHom.ker ((e.toAlgHom.comp φ).toRingHom) = RingHom.ker φ.toRingHom := by
  ext x
  simp only [RingHom.mem_ker, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgHom.coe_comp,
    Function.comp_apply]
  exact ⟨fun hx ↦ e.injective (by simpa using hx), fun hx ↦ by simp [hx]⟩

/-- Let `R → S` be a ring map. It is a *relative global complete intersection* if there are
`n c : ℕ`, a surjective `R`-algebra homomorphism `π : R[x_1, …, x_n] ↠ S` and elements
`f_1, …, f_c ∈ R[x_1, …, x_n]` with `ker π = (f_1, …, f_c)`, such that every *nonempty* fibre
of `Spec S → Spec R` has dimension `n - c`.

A fibre of `Spec S → Spec R` at a prime `p` of `R` is `Spec (S ⊗_R κ(p))`, and it is nonempty
exactly when the fibre ring `S ⊗_R κ(p)` is nonzero; this is the `Nontrivial` hypothesis. The
Krull dimension lives in `WithBot ℕ∞`, where truncated subtraction is ill-behaved, so the
condition `dim (S ⊗_R κ(p)) = n − c` is written in the equivalent additive form
`ringKrullDim (S ⊗_R κ(p)) + c = n` (which, in this finite case, also encodes `c ≤ n`). -/
noncomputable def IsRelativeGlobalCompleteIntersection
    (R : Type*) [CommRing R] (S : Type*) [CommRing S] [Algebra R S] : Prop :=
  ∃ (n c : ℕ) (π : MvPolynomial (Fin n) R →ₐ[R] S) (f : Fin c → MvPolynomial (Fin n) R),
    Function.Surjective π ∧
      RingHom.ker π.toRingHom = Ideal.span (Set.range f) ∧
      ∀ (p : Ideal R), [p.IsPrime] →
        Nontrivial (TensorProduct R S (IsLocalRing.ResidueField (Localization.AtPrime p))) →
          ringKrullDim (TensorProduct R S (IsLocalRing.ResidueField (Localization.AtPrime p)))
            + (c : WithBot ℕ∞) = (n : WithBot ℕ∞)

/-- A presentation `S = R[x_1, …, x_n]/(f_1, …, f_c)` with finitely many relations exhibits `S`
as a finitely presented `R`-algebra. -/
theorem IsRelativeGlobalCompleteIntersection.finitePresentation
    {R : Type*} [CommRing R] {S : Type*} [CommRing S] [Algebra R S]
    (h : IsRelativeGlobalCompleteIntersection R S) : Algebra.FinitePresentation R S := by
  obtain ⟨n, c, π, f, hsurj, hker, -⟩ := h
  have hFG : (RingHom.ker π.toRingHom).FG := by
    rw [hker]
    exact Submodule.fg_span (Set.finite_range f)
  exact Algebra.FinitePresentation.of_surjective hsurj hFG

/-- Being a global complete intersection over `k` is invariant under `k`-algebra isomorphism. -/
private theorem gciOver_transport {k : Type*} [Field k] {A B : Type*} [CommRing A] [CommRing B]
    [Algebra k A] [Algebra k B] (e : A ≃ₐ[k] B)
    (h : IsGlobalCompleteIntersectionOver k A) : IsGlobalCompleteIntersectionOver k B := by
  rcases h with hsub | ⟨n, c, π, f, hsurj, hker, hdim⟩
  · exact Or.inl e.toEquiv.symm.subsingleton
  · refine Or.inr ⟨n, c, e.toAlgHom.comp π, f, e.surjective.comp hsurj, ?_, ?_⟩
    · rwa [ker_algEquiv_comp e π]
    · rwa [← ringKrullDim_eq_of_ringEquiv e.toRingEquiv]

/-- A global complete intersection over `k` is a local complete intersection over `k`. -/
private theorem lciOver_of_gciOver {k : Type*} [Field k] {A : Type*} [CommRing A] [Algebra k A]
    (h : IsGlobalCompleteIntersectionOver k A) : IsLocalCompleteIntersectionOver k A := by
  refine ⟨1, fun _ ↦ 1, ?_, fun _ ↦ ?_⟩
  · simp
  · change IsGlobalCompleteIntersectionOver k (Localization.Away (1 : A))
    have e : A ≃ₐ[A] Localization.Away (1 : A) :=
      IsLocalization.atUnits A (Submonoid.powers (1 : A)) fun x hx ↦ by
        obtain ⟨m, rfl⟩ := (Submonoid.mem_powers_iff x 1).mp hx
        simp
    exact gciOver_transport (e.restrictScalars k) h

/-- Every fibre of a relative global complete intersection is a global complete intersection
over the residue field, presented by the same numbers `n` and `c`. -/
theorem IsRelativeGlobalCompleteIntersection.isGlobalCompleteIntersectionOver_fibre
    {R : Type*} [CommRing R] {S : Type*} [CommRing S] [Algebra R S]
    (h : IsRelativeGlobalCompleteIntersection R S) (p : Ideal R) [p.IsPrime] :
    letI κ := IsLocalRing.ResidueField (Localization.AtPrime p)
    letI := Algebra.TensorProduct.rightAlgebra (R := R) (A := S) (B := κ)
    IsGlobalCompleteIntersectionOver κ (TensorProduct R S κ) := by
  let κ := IsLocalRing.ResidueField (Localization.AtPrime p)
  let := Algebra.TensorProduct.rightAlgebra (R := R) (A := S) (B := κ)
  obtain ⟨n, c, π, f, hsurj, hker, hdim⟩ := h
  by_cases hsub : Subsingleton (TensorProduct R S κ)
  · exact Or.inl hsub
  · have hnt : Nontrivial (TensorProduct R S κ) := not_subsingleton_iff_nontrivial.mp hsub
    let f' : Fin c → MvPolynomial (Fin n) κ := fun i ↦ MvPolynomial.map (algebraMap R κ) (f i)
    let eA : (MvPolynomial (Fin n) R ⧸ Ideal.span (Set.range f)) ≃ₐ[R] S :=
      (Ideal.quotientEquivAlgOfEq R hker.symm).trans
        (Ideal.quotientKerAlgEquivOfSurjective hsurj)
    have heq : ∀ x : MvPolynomial (Fin n) R,
        MvPolynomial.algebraTensorAlgEquiv R κ
            (Algebra.TensorProduct.includeRight (R := R) (A := κ) x) =
          MvPolynomial.map (algebraMap R κ) x := by
      intro x
      rw [Algebra.TensorProduct.includeRight_apply,
        ← MvPolynomial.algebraTensorAlgEquiv_symm_map (σ := Fin n) R κ x,
        AlgEquiv.apply_symm_apply]
    have hJ : Ideal.span (Set.range f') =
        Ideal.map
          (MvPolynomial.algebraTensorAlgEquiv (σ := Fin n) R κ :
            TensorProduct R κ (MvPolynomial (Fin n) R) →+* MvPolynomial (Fin n) κ)
          (Ideal.map
            (Algebra.TensorProduct.includeRight (R := R) (A := κ)
              (B := MvPolynomial (Fin n) R)) (Ideal.span (Set.range f))) := by
      rw [Ideal.map_span, Ideal.map_span, ← Set.image_comp, ← Set.range_comp]
      exact congrArg Ideal.span (congrArg Set.range (funext fun i ↦ (heq (f i)).symm))
    let e1 : TensorProduct R κ (MvPolynomial (Fin n) R ⧸ Ideal.span (Set.range f)) ≃ₐ[κ]
        (TensorProduct R κ (MvPolynomial (Fin n) R)) ⧸
          Ideal.map (Algebra.TensorProduct.includeRight (R := R) (A := κ)
            (B := MvPolynomial (Fin n) R)) (Ideal.span (Set.range f)) :=
      Algebra.TensorProduct.tensorQuotientEquiv κ (MvPolynomial (Fin n) R) κ
        (Ideal.span (Set.range f))
    let e2 : (MvPolynomial (Fin n) κ ⧸ Ideal.span (Set.range f')) ≃ₐ[κ]
        (TensorProduct R κ (MvPolynomial (Fin n) R)) ⧸
          Ideal.map (Algebra.TensorProduct.includeRight (R := R) (A := κ)
            (B := MvPolynomial (Fin n) R)) (Ideal.span (Set.range f)) :=
      (Ideal.quotientEquivAlg _ (Ideal.span (Set.range f'))
        (MvPolynomial.algebraTensorAlgEquiv R κ) hJ).symm
    let Φ : (MvPolynomial (Fin n) κ ⧸ Ideal.span (Set.range f')) ≃ₐ[κ] TensorProduct R S κ :=
      e2.trans (e1.symm.trans
        ((Algebra.TensorProduct.congr (AlgEquiv.refl (R := κ) (A₁ := κ)) eA).trans
          (aux_kcomm R S κ).symm))
    refine Or.inr ⟨n, c, Φ.toAlgHom.comp (Ideal.Quotient.mkₐ κ (Ideal.span (Set.range f'))), f',
      Φ.surjective.comp Ideal.Quotient.mk_surjective, ?_, hdim p hnt⟩
    rw [ker_algEquiv_comp Φ (Ideal.Quotient.mkₐ κ (Ideal.span (Set.range f'))),
      Ideal.Quotient.mkₐ_toRingHom, Ideal.mk_ker]

/-- Every fibre of a relative global complete intersection is a local complete intersection over
the residue field, since it is even a global one. -/
theorem IsRelativeGlobalCompleteIntersection.isLocalCompleteIntersectionOver_fibre
    {R : Type*} [CommRing R] {S : Type*} [CommRing S] [Algebra R S]
    (h : IsRelativeGlobalCompleteIntersection R S) (p : Ideal R) [p.IsPrime] :
    letI κ := IsLocalRing.ResidueField (Localization.AtPrime p)
    letI := Algebra.TensorProduct.rightAlgebra (R := R) (A := S) (B := κ)
    IsLocalCompleteIntersectionOver κ (TensorProduct R S κ) := by
  let κ := IsLocalRing.ResidueField (Localization.AtPrime p)
  let := Algebra.TensorProduct.rightAlgebra (R := R) (A := S) (B := κ)
  exact lciOver_of_gciOver (h.isGlobalCompleteIntersectionOver_fibre p)

/-- A flat relative global complete intersection is syntomic. -/
theorem IsRelativeGlobalCompleteIntersection.isSyntomic_of_flat
    {R : Type*} [CommRing R] {S : Type*} [CommRing S] [Algebra R S]
    (h : IsRelativeGlobalCompleteIntersection R S) (hflat : Module.Flat R S) :
    IsSyntomic R S :=
  ⟨hflat, h.finitePresentation, fun p _ ↦ h.isLocalCompleteIntersectionOver_fibre p⟩
