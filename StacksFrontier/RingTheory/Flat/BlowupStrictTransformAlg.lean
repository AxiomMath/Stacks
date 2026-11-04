module

public import StacksFrontier.RingTheory.Flat.Blowup
public import StacksFrontier.RingTheory.Flat.BlowupFiniteTypeReduction
public import StacksFrontier.RingTheory.Flat.BlowupFlatten

/-!
# The strict transform of a polynomial algebra, and clause (4) of Stacks Tag 053I

Let `R` be a commutative ring, `I ⊆ R` an ideal, `a ∈ I`, write `C = R[I/a] = Blowup I a` for the
affine blowup chart and `Cx = C[x_1, …, x_n]`.  This file identifies the strict transform
(Stacks Tag 053H) of the polynomial algebra `S = R[x_1, …, x_n]` on the chart with `Cx`, and uses
that identification to supply clause (4) of Stacks Tag 053I for a polynomial algebra, given the
relation submodule `L` of `Stacks.Flatness.BlowupFlattening.flat_strictTransform_of_flat_quotient`.
  It also carries the
descended flat model of `Stacks.Flatness.BlowupFlattening.exists_chart_flat_model` across the
  identification of the
chart ring `Stacks.AffineBlowup.chartRing c` with the quotient model `Blowup c.I c.a`.

## Main results

* `Module.FinitePresentation.of_ringEquiv`, `Module.Flat.of_ringEquiv`: finite presentation and
  flatness of a module transported along a ring isomorphism of the base together with a compatible
  additive isomorphism.
* `Stacks.Flatness.BlowupFlattening.strictTransformAlgMvPolynomialEquiv`: **the strict transform of
  `R[x_1, …, x_n]` is
  `C[x_1, …, x_n]`**, as `C`-algebras.  Consequently
  `Stacks.Flatness.BlowupFlattening.flat_strictTransformAlg_mvPolynomial` and
  `Stacks.Flatness.BlowupFlattening.finitePresentation_strictTransformAlg_mvPolynomial` give the
    first two conjuncts of
  clause (4) of Stacks Tag 053I for `S = R[x_1, …, x_n]`.
* `Stacks.Flatness.BlowupFlattening.mvPolynomialBaseChangeEquiv_symm_smul`: the comparison
  `C ⊗_R M ≃ₗ[C] Cx ⊗_{R[x]} M` of `Stacks.Flatness.BlowupFlattening.mvPolynomialBaseChangeEquiv`
    is not merely
  `C`-linear but compatible with the action of `C ⊗_R R[x]` on the left and of `Cx` on the right.
* `Stacks.Flatness.BlowupFlattening.strictTransformQuotEquiv`: the equivalence of
  `Stacks.Flatness.BlowupFlattening.nonempty_strictTransform_equiv`, produced as a term rather than
    as a `Nonempty`, so
  that its interaction with the polynomial scalars can be recorded
  (`Stacks.Flatness.BlowupFlattening.strictTransformQuotEquiv_smul`).
* `Stacks.Flatness.BlowupFlattening.finitePresentation_strictTransform_of_fg`: **the last conjunct
  of clause (4) of
  Stacks Tag 053I for a polynomial algebra**: the strict transform of `M` is finitely presented
  over the strict transform of `R[x_1, …, x_n]`.  All four conjuncts together are
  `Stacks.Flatness.BlowupFlattening.strictTransformFlatFinitePresentation_mvPolynomial`.
* `Stacks.Flatness.BlowupFlattening.flat_quotient_of_ringEquiv` and
  `Stacks.Flatness.BlowupFlattening.exists_blowupChart_flat_model`: **the
  descended flat model on the quotient model of the chart.**  The conclusion of
  `Stacks.Flatness.BlowupFlattening.exists_chart_flat_model` is stated over the subring
    `Stacks.AffineBlowup.chartRing c` of `K`;
  this carries it over `Stacks.AffineBlowup.AdmissibleChart.blowupRingEquiv` to `Blowup c.I c.a`,
    the model
  on which the strict transform is built.

## Implementation notes

Nothing here carries the `053I` tag: what is still missing at this point is the *comparison* of
the relation vectors produced by `Stacks.Flatness.BlowupFlattening.exists_blowupChart_flat_model`
  with a presentation of
`M` — the hypotheses `hZL` and `hLsat` of
`Stacks.Flatness.BlowupFlattening.finitePresentation_strictTransform_of_fg` — and the reduction
  from a general finite
type algebra to a polynomial one.  Both are supplied in
`StacksFrontier.RingTheory.Flat.BlowupFlattenAssembly`, which carries the tag on
`Stacks.Flatness.BlowupFlattening.stacks053I`; see also the implementation notes of
`StacksFrontier.RingTheory.Flat.BlowupFlatten`.

## References

* [Stacks Project, Tag 053H](https://stacks.math.columbia.edu/tag/053H)
* [Stacks Project, Tag 053I](https://stacks.math.columbia.edu/tag/053I)
* [Stacks Project, Tag 0561](https://stacks.math.columbia.edu/tag/0561)
-/

@[expose] public section

open scoped TensorProduct

universe u v w

/-! ### Finite presentation transported along a ring isomorphism -/

/-- **Finite presentation transported along a ring isomorphism.** Let `e : T ≃+* T'` be a ring
isomorphism, `N` a `T`-module, `N'` a finitely presented `T'`-module, and `f : N ≃+ N'` an
additive isomorphism with `f (t • x) = e t • f x`.  Then `N` is a finitely presented `T`-module.

Restricting scalars along `e` makes `N'` a `T`-module which is finitely presented over `T`,
because `T'` is finitely presented over `T` (it is free of rank one, via `e`) and
`Module.FinitePresentation.trans` composes; `f` is then a `T`-linear isomorphism. -/
theorem Module.FinitePresentation.of_ringEquiv {T : Type u} [CommRing T] {T' : Type v}
    [CommRing T'] (e : T ≃+* T') {N : Type w} [AddCommGroup N] [Module T N] {N' : Type*}
    [AddCommGroup N'] [Module T' N'] [Module.FinitePresentation T' N'] (f : N ≃+ N')
    (hf : ∀ (t : T) (x : N), f (t • x) = e t • f x) : Module.FinitePresentation T N := by
  let _ : Algebra T T' := e.toRingHom.toAlgebra
  let _ : Module T N' := Module.compHom N' (e.toRingHom : T →+* T')
  have _ : IsScalarTower T T' N' := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have _ : Module.FinitePresentation T T' :=
    Module.FinitePresentation.of_equiv
      (AddEquiv.toLinearEquiv (R := T) e.symm.toAddEquiv fun c x => by
        show e.symm (e c * x) = c * e.symm x
        rw [map_mul, RingEquiv.symm_apply_apply]).symm
  have _ : Module.FinitePresentation T N' := Module.FinitePresentation.trans T N' T'
  exact Module.FinitePresentation.of_equiv (AddEquiv.toLinearEquiv f hf).symm

/-- **Flatness transported along a ring isomorphism.** Let `e : T ≃+* T'` be a ring isomorphism,
`N` a `T`-module, `N'` a flat `T'`-module, and `f : N ≃+ N'` an additive isomorphism with
`f (t • x) = e t • f x`.  Then `N` is a flat `T`-module.

The proof is the same as for `Module.FinitePresentation.of_ringEquiv`: restricting scalars along
`e` makes `N'` a flat `T`-module because `T'` is flat over `T`, and `f` is then a `T`-linear
isomorphism. -/
theorem Module.Flat.of_ringEquiv {T : Type u} [CommRing T] {T' : Type v} [CommRing T']
    (e : T ≃+* T') {N : Type w} [AddCommGroup N] [Module T N] {N' : Type*} [AddCommGroup N']
    [Module T' N'] [Module.Flat T' N'] (f : N ≃+ N')
    (hf : ∀ (t : T) (x : N), f (t • x) = e t • f x) : Module.Flat T N := by
  let _ : Algebra T T' := e.toRingHom.toAlgebra
  let _ : Module T N' := Module.compHom N' (e.toRingHom : T →+* T')
  have _ : IsScalarTower T T' N' := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have _ : Module.Flat T T' :=
    Module.Flat.of_linearEquiv
      (AddEquiv.toLinearEquiv (R := T) e.symm.toAddEquiv fun c x => by
        show e.symm (e c * x) = c * e.symm x
        rw [map_mul, RingEquiv.symm_apply_apply])
  have _ : Module.Flat T N' := Module.Flat.trans T T' N'
  exact Module.Flat.of_linearEquiv (AddEquiv.toLinearEquiv f hf)

namespace Stacks.Flatness.BlowupFlattening

attribute [local instance] MvPolynomial.algebraMvPolynomial

/-! ### The strict transform of a polynomial algebra -/

section PolyStrictTransform

variable {R : Type u} [CommRing R] (I : Ideal R) (a : R) [Fact (a ∈ I)] (n : ℕ)

/-- **The base change of a polynomial algebra to the chart is a polynomial algebra.** The
`C`-algebra `C ⊗_R R[x_1, …, x_n]` is `C[x_1, …, x_n]`; this is
`MvPolynomial.algebraTensorAlgEquiv`. -/
noncomputable def polyBaseChangeAlgEquiv :
    TensorProduct R (Blowup I a) (MvPolynomial (Fin n) R) ≃ₐ[Blowup I a]
      MvPolynomial (Fin n) (Blowup I a) :=
  MvPolynomial.algebraTensorAlgEquiv R (Blowup I a)

/-- `polyBaseChangeAlgEquiv` sends `b ⊗ p` to `b • p`, where `p` is mapped to `C[x_1, …, x_n]`
by the coefficientwise `algebraMap R C`. -/
@[simp]
theorem polyBaseChangeAlgEquiv_tmul (b : Blowup I a) (p : MvPolynomial (Fin n) R) :
    polyBaseChangeAlgEquiv I a n (b ⊗ₜ[R] p) =
      b • MvPolynomial.map (algebraMap R (Blowup I a)) p :=
  MvPolynomial.algebraTensorAlgEquiv_tmul R (Blowup I a) b p

/-- The base change of a polynomial algebra to the chart is flat over the chart, being a
polynomial algebra over it. -/
theorem flat_polyBaseChange :
    Module.Flat (Blowup I a) (TensorProduct R (Blowup I a) (MvPolynomial (Fin n) R)) :=
  Module.Flat.of_linearEquiv (polyBaseChangeAlgEquiv I a n).toLinearEquiv

/-- **The base change of a polynomial algebra to a chart which is a domain has no `a`-power
torsion.** The base change is the polynomial algebra over the chart, hence free, hence flat, so
`strictTransform.torsionSubmodule_eq_bot` applies. -/
theorem strictTransformIdeal_mvPolynomial_eq_bot [IsDomain (Blowup I a)] :
    strictTransformIdeal I a (MvPolynomial (Fin n) R) = ⊥ := by
  have _ := flat_polyBaseChange I a n
  have h := strictTransform.torsionSubmodule_eq_bot I a (MvPolynomial (Fin n) R)
  refine (Submodule.eq_bot_iff _).mpr fun x hx => ?_
  have hx' := (mem_strictTransformIdeal_iff_mem_torsionSubmodule I a
    (MvPolynomial (Fin n) R)).mp hx
  simpa [h] using hx'

/-- **The strict transform of a polynomial algebra is the polynomial algebra over the chart.**
For `R` a ring whose chart `C = R[I/a]` is a domain, the strict transform (Stacks Tag 053H) of
`S = R[x_1, …, x_n]` on the chart is `C[x_1, …, x_n]` as a `C`-algebra: the `a`-power torsion
ideal of `C ⊗_R S` is zero by
  `Stacks.Flatness.BlowupFlattening.strictTransformIdeal_mvPolynomial_eq_bot`, so the strict
transform is the base change itself, which is `C[x_1, …, x_n]`.

This is what makes clause (4) of Stacks Tag 053I accessible for a polynomial algebra: the
first two conjuncts follow at once, and the module structure on the strict transform of an
`S`-module can be read through the polynomial ring. -/
noncomputable def strictTransformAlgMvPolynomialEquiv [IsDomain (Blowup I a)] :
    strictTransformAlg I a (MvPolynomial (Fin n) R) ≃ₐ[Blowup I a]
      MvPolynomial (Fin n) (Blowup I a) :=
  (Ideal.quotientEquivAlgOfEq (Blowup I a)
      (strictTransformIdeal_mvPolynomial_eq_bot I a n)).trans
    ((AlgEquiv.quotientBot (Blowup I a) _).trans (polyBaseChangeAlgEquiv I a n))

/-- On the class of `u ∈ C ⊗_R R[x_1, …, x_n]`, `strictTransformAlgMvPolynomialEquiv` agrees
with `polyBaseChangeAlgEquiv` applied to `u`. -/
@[simp]
theorem strictTransformAlgMvPolynomialEquiv_mk [IsDomain (Blowup I a)]
    (u : TensorProduct R (Blowup I a) (MvPolynomial (Fin n) R)) :
    strictTransformAlgMvPolynomialEquiv I a n
        (strictTransformAlg.mk I a (MvPolynomial (Fin n) R) u) =
      polyBaseChangeAlgEquiv I a n u :=
  rfl

/-- **Clause (4) of Stacks Tag 053I, flatness of the strict transform of a polynomial algebra.**
-/
theorem flat_strictTransformAlg_mvPolynomial [IsDomain (Blowup I a)] :
    Module.Flat (Blowup I a) (strictTransformAlg I a (MvPolynomial (Fin n) R)) :=
  Module.Flat.of_linearEquiv (strictTransformAlgMvPolynomialEquiv I a n).toLinearEquiv

/-- **Clause (4) of Stacks Tag 053I, finite presentation of the strict transform of a polynomial
algebra**: it is a polynomial algebra over the chart, and a polynomial algebra in finitely many
variables is of finite presentation. -/
theorem finitePresentation_strictTransformAlg_mvPolynomial [IsDomain (Blowup I a)] :
    Algebra.FinitePresentation (Blowup I a) (strictTransformAlg I a (MvPolynomial (Fin n) R)) :=
  Algebra.FinitePresentation.equiv (strictTransformAlgMvPolynomialEquiv I a n).symm

end PolyStrictTransform

/-! ### The polynomial scalars on the strict transform of a module -/

section Semilinear

variable {R : Type u} [CommRing R] (I : Ideal R) (a : R) [Fact (a ∈ I)] (n : ℕ) (M : Type w)
  [AddCommGroup M] [Module (MvPolynomial (Fin n) R) M] [Module R M]
  [IsScalarTower R (MvPolynomial (Fin n) R) M]

attribute [local instance] strictTransform.baseChangeModule

/-- The inverse of `mvPolynomialBaseChangeEquiv` sends `c ⊗ m ∈ C ⊗_R M` to
`c ⊗ m ∈ C[x_1, …, x_n] ⊗_{R[x_1, …, x_n]} M`, with `c` viewed as a constant polynomial. -/
@[simp]
theorem mvPolynomialBaseChangeEquiv_symm_tmul (c : Blowup I a) (m : M) :
    (mvPolynomialBaseChangeEquiv R (Blowup I a) n M).symm (c ⊗ₜ[R] m) =
      algebraMap (Blowup I a) (MvPolynomial (Fin n) (Blowup I a)) c
        ⊗ₜ[MvPolynomial (Fin n) R] m :=
  Algebra.IsPushout.cancelBaseChange_symm_tmul R (Blowup I a) (MvPolynomial (Fin n) R)
    (MvPolynomial (Fin n) (Blowup I a)) M c m

/-- **The comparison of the two spellings of the base change is compatible with the polynomial
scalars.** The `C`-linear equivalence
`Stacks.Flatness.BlowupFlattening.mvPolynomialBaseChangeEquiv`
`C[x_1, …, x_n] ⊗_{R[x]} M ≃ₗ[C] C ⊗_R M` also matches the action of `C ⊗_R R[x]` on the target
(`strictTransform.baseChangeModule`) with the action of `C[x_1, …, x_n]` on the source, the two
rings being identified by `Stacks.Flatness.BlowupFlattening.polyBaseChangeAlgEquiv`.

This is what upgrades the identification of the strict transform with a quotient of a finite free
module from a `C`-linear to a `C[x_1, …, x_n]`-linear statement, which clause (4) of
Stacks Tag 053I needs. -/
theorem mvPolynomialBaseChangeEquiv_symm_smul
    (u : TensorProduct R (Blowup I a) (MvPolynomial (Fin n) R))
    (z : TensorProduct R (Blowup I a) M) :
    (mvPolynomialBaseChangeEquiv R (Blowup I a) n M).symm (u • z) =
      polyBaseChangeAlgEquiv I a n u •
        (mvPolynomialBaseChangeEquiv R (Blowup I a) n M).symm z := by
  induction u using TensorProduct.induction_on with
  | zero => simp
  | add u u' hu hu' => rw [add_smul, map_add, hu, hu', map_add, add_smul]
  | tmul b p =>
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add z z' hz hz' => rw [smul_add, map_add, hz, hz', map_add, smul_add]
    | tmul c m =>
      have hq : ∀ q x : MvPolynomial (Fin n) (Blowup I a), ∀ y : M,
          q • (x ⊗ₜ[MvPolynomial (Fin n) R] y) = (q * x) ⊗ₜ[MvPolynomial (Fin n) R] y :=
        fun _ _ _ => rfl
      have hscal : p • algebraMap (Blowup I a) (MvPolynomial (Fin n) (Blowup I a)) (b * c) =
          (b • MvPolynomial.map (algebraMap R (Blowup I a)) p) *
            algebraMap (Blowup I a) (MvPolynomial (Fin n) (Blowup I a)) c := by
        rw [map_mul, Algebra.smul_def, Algebra.smul_def, MvPolynomial.algebraMap_def]
        ring
      rw [strictTransform.baseChange_smul_tmul, mvPolynomialBaseChangeEquiv_symm_tmul,
        mvPolynomialBaseChangeEquiv_symm_tmul, polyBaseChangeAlgEquiv_tmul, hq,
        ← TensorProduct.smul_tmul, hscal]

variable {r : ℕ} {π : (Fin r → MvPolynomial (Fin n) R) →ₗ[MvPolynomial (Fin n) R] M}

/-- **The scalar extension of `M` as a quotient of a finite free module over the polynomial ring
on the chart.** For a surjection `π : R[x]ʳ → M` this is the `C`-linear identification of
`C ⊗_R M` with `C[x]ʳ` modulo the base change of `ker π`, the composite of
`Stacks.Flatness.BlowupFlattening.mvPolynomialBaseChangeEquiv` with
  `Stacks.Flatness.BlowupFlattening.tensorQuotEquivOf`.

It is the equivalence out of which
  `Stacks.Flatness.BlowupFlattening.nonempty_strictTransform_equiv` is built; it is
named here because `Stacks.Flatness.BlowupFlattening.baseChangeQuotEquivOf_smul` records how it
  interacts with the
polynomial scalars. -/
noncomputable def baseChangeQuotEquivOf (hπ : Function.Surjective π) :
    TensorProduct R (Blowup I a) M ≃ₗ[Blowup I a]
      ((Fin r → MvPolynomial (Fin n) (Blowup I a)) ⧸
        relSpanOf (MvPolynomial (Fin n) R) (MvPolynomial (Fin n) (Blowup I a)) r
          (LinearMap.ker π)) :=
  (mvPolynomialBaseChangeEquiv R (Blowup I a) n M).symm ≪≫ₗ
    (tensorQuotEquivOf (T := MvPolynomial (Fin n) (Blowup I a)) π hπ).restrictScalars
      (Blowup I a)

/-- The identification `Stacks.Flatness.BlowupFlattening.baseChangeQuotEquivOf` carries the action
  of `C ⊗_R R[x]` to
the action of `C[x_1, …, x_n]`. -/
theorem baseChangeQuotEquivOf_smul (hπ : Function.Surjective π)
    (u : TensorProduct R (Blowup I a) (MvPolynomial (Fin n) R))
    (z : TensorProduct R (Blowup I a) M) :
    baseChangeQuotEquivOf I a n M hπ (u • z) =
      polyBaseChangeAlgEquiv I a n u • baseChangeQuotEquivOf I a n M hπ z := by
  rw [baseChangeQuotEquivOf, LinearEquiv.trans_apply, LinearEquiv.trans_apply,
    LinearEquiv.restrictScalars_apply, LinearEquiv.restrictScalars_apply,
    mvPolynomialBaseChangeEquiv_symm_smul, map_smul]

variable (hπ : Function.Surjective π)
  (L : Submodule (MvPolynomial (Fin n) (Blowup I a))
    (Fin r → MvPolynomial (Fin n) (Blowup I a)))
  (hZL : relSpanOf (MvPolynomial (Fin n) R) (MvPolynomial (Fin n) (Blowup I a)) r
    (LinearMap.ker π) ≤ L)
  (hLsat : ∀ v ∈ L, ∃ N : ℕ, algebraMap R (Blowup I a) a ^ N • v ∈
    relSpanOf (MvPolynomial (Fin n) R) (MvPolynomial (Fin n) (Blowup I a)) r (LinearMap.ker π))
  (hsat : ∀ (N : ℕ) (v : Fin r → MvPolynomial (Fin n) (Blowup I a)),
    algebraMap R (Blowup I a) a ^ N • v ∈ L → v ∈ L)

/-- **The strict transform is the descended quotient**, as a term rather than as a `Nonempty`.
This is the equivalence whose existence is
  `Stacks.Flatness.BlowupFlattening.nonempty_strictTransform_equiv`, built by
the same composite; naming it makes
  `Stacks.Flatness.BlowupFlattening.strictTransformQuotEquiv_smul` available. -/
noncomputable def strictTransformQuotEquiv :
    strictTransform I a M ≃ₗ[Blowup I a]
      ((Fin r → MvPolynomial (Fin n) (Blowup I a)) ⧸ L) :=
  Submodule.Quotient.equiv _ _ (baseChangeQuotEquivOf I a n M hπ)
      (map_torsion' (baseChangeQuotEquivOf I a n M hπ) _) ≪≫ₗ
    quotTorsionEquiv
      ((relSpanOf (MvPolynomial (Fin n) R) (MvPolynomial (Fin n) (Blowup I a)) r
        (LinearMap.ker π)).restrictScalars (Blowup I a))
      (L.restrictScalars (Blowup I a)) (fun _ hv => hZL hv) (fun v hv => hLsat v hv)
      fun N v h => hsat N v h

/-- The identification `Stacks.Flatness.BlowupFlattening.strictTransformQuotEquiv` sends the class
  of `z` to the class
of `Stacks.Flatness.BlowupFlattening.baseChangeQuotEquivOf z`. -/
theorem strictTransformQuotEquiv_mkQ (z : TensorProduct R (Blowup I a) M) :
    strictTransformQuotEquiv I a n M hπ L hZL hLsat hsat (strictTransform.mkQ I a M z) =
      Submodule.factor hZL (baseChangeQuotEquivOf I a n M hπ z) := by
  obtain ⟨v, hv⟩ := Submodule.Quotient.mk_surjective _ (baseChangeQuotEquivOf I a n M hπ z)
  have key : strictTransformQuotEquiv I a n M hπ L hZL hLsat hsat
      (strictTransform.mkQ I a M z) =
      quotTorsionEquiv
        ((relSpanOf (MvPolynomial (Fin n) R) (MvPolynomial (Fin n) (Blowup I a)) r
          (LinearMap.ker π)).restrictScalars (Blowup I a))
        (L.restrictScalars (Blowup I a)) (fun _ hv' => hZL hv') (fun w hw => hLsat w hw)
        (fun N w h => hsat N w h)
        (Submodule.Quotient.mk (baseChangeQuotEquivOf I a n M hπ z)) := rfl
  rw [key, ← hv]
  exact (Submodule.factor_mk hZL v).symm

/-- **The identification of the strict transform with the descended quotient is linear over the
polynomial ring on the chart.** The polynomial ring acts on the strict transform of `M` through
the strict transform of `R[x_1, …, x_n]`, which
`Stacks.Flatness.BlowupFlattening.strictTransformAlgMvPolynomialEquiv` identifies with it. -/
theorem strictTransformQuotEquiv_smul [IsDomain (Blowup I a)]
    (t : strictTransformAlg I a (MvPolynomial (Fin n) R)) (x : strictTransform I a M) :
    strictTransformQuotEquiv I a n M hπ L hZL hLsat hsat (t • x) =
      strictTransformAlgMvPolynomialEquiv I a n t •
        strictTransformQuotEquiv I a n M hπ L hZL hLsat hsat x := by
  obtain ⟨u, rfl⟩ := strictTransformAlg.mk_surjective I a (MvPolynomial (Fin n) R) t
  obtain ⟨z, rfl⟩ := strictTransform.mkQ_surjective I a M x
  rw [strictTransformAlg.mk_smul, strictTransform.smul_mkQ,
    strictTransformQuotEquiv_mkQ, strictTransformQuotEquiv_mkQ,
    strictTransformAlgMvPolynomialEquiv_mk, baseChangeQuotEquivOf_smul, map_smul]

include hπ hZL hLsat in
/-- **Clause (4) of Stacks Tag 053I for a polynomial algebra, the finite presentation of the
strict transform of the module.** In the situation of
`Stacks.Flatness.BlowupFlattening.flat_strictTransform_of_flat_quotient`, with the relation
  submodule `L` moreover
finitely generated, the strict transform of `M` is finitely presented over the strict transform of
`R[x_1, …, x_n]`.

The quotient `C[x]ʳ / L` is finitely presented over `C[x_1, …, x_n]`, being a finite free module
modulo a finitely generated submodule;
  `Stacks.Flatness.BlowupFlattening.strictTransformAlgMvPolynomialEquiv`
identifies `C[x_1, …, x_n]` with the strict transform of `R[x_1, …, x_n]`, and
`Stacks.Flatness.BlowupFlattening.strictTransformQuotEquiv_smul` says that this identification
  carries the module
structure over. -/
theorem finitePresentation_strictTransform_of_fg [IsDomain (Blowup I a)] (hL : L.FG)
    (hflat : Module.Flat (Blowup I a)
      ((Fin r → MvPolynomial (Fin n) (Blowup I a)) ⧸ L)) :
    Module.FinitePresentation (strictTransformAlg I a (MvPolynomial (Fin n) R))
      (strictTransform I a M) := by
  have hα : algebraMap R (Blowup I a) a ≠ 0 := strictTransform.algebraMap_a_ne_zero I a
  have htf : Module.IsTorsionFree (Blowup I a)
      ((Fin r → MvPolynomial (Fin n) (Blowup I a)) ⧸ L) := Module.Flat.isTorsionFree
  have hsat' : ∀ (N : ℕ) (v : Fin r → MvPolynomial (Fin n) (Blowup I a)),
      algebraMap R (Blowup I a) a ^ N • v ∈ L → v ∈ L :=
    fun N v h => mem_of_smul_pow_mem (L.restrictScalars (Blowup I a)) hα htf (N := N) h
  have : Module.FinitePresentation (MvPolynomial (Fin n) (Blowup I a))
      ((Fin r → MvPolynomial (Fin n) (Blowup I a)) ⧸ L) :=
    Module.finitePresentation_of_surjective L.mkQ (Submodule.mkQ_surjective _)
      (by rwa [Submodule.ker_mkQ])
  exact Module.FinitePresentation.of_ringEquiv
    (strictTransformAlgMvPolynomialEquiv I a n).toRingEquiv
    (strictTransformQuotEquiv I a n M hπ L hZL hLsat hsat').toAddEquiv
    (strictTransformQuotEquiv_smul I a n M hπ L hZL hLsat hsat')

include hπ hZL hLsat in
/-- **Clause (4) of Stacks Tag 053I for a polynomial algebra.** Let `C = R[I/a]` be a chart which
is a domain, let `M` be a module over `S = R[x_1, …, x_n]` presented by a surjection
`π : Sʳ → M`, and let `L` be a finitely generated `C[x]`-submodule of `C[x]ʳ` containing the
base-changed relations, all of whose elements are `a`-power torsion modulo them, such that
`C[x]ʳ / L` is flat over `C`.  Then the strict transforms of `S` and of `M` on the chart satisfy
clause (4) of Stacks Tag 053I.

The two conjuncts about `S` are
  `Stacks.Flatness.BlowupFlattening.flat_strictTransformAlg_mvPolynomial` and
`Stacks.Flatness.BlowupFlattening.finitePresentation_strictTransformAlg_mvPolynomial`; the flatness
  of the strict
transform of `M` is `Stacks.Flatness.BlowupFlattening.flat_strictTransform_of_flat_quotient`; its
  finite presentation is
`Stacks.Flatness.BlowupFlattening.finitePresentation_strictTransform_of_fg`. -/
theorem strictTransformFlatFinitePresentation_mvPolynomial [IsDomain (Blowup I a)] (hL : L.FG)
    (hflat : Module.Flat (Blowup I a)
      ((Fin r → MvPolynomial (Fin n) (Blowup I a)) ⧸ L)) :
    StrictTransformFlatFinitePresentation I a (MvPolynomial (Fin n) R) M :=
  ⟨flat_strictTransformAlg_mvPolynomial I a n,
    finitePresentation_strictTransformAlg_mvPolynomial I a n,
    flat_strictTransform_of_flat_quotient I a n M hπ L hZL hLsat hflat,
    finitePresentation_strictTransform_of_fg I a n M hπ L hZL hLsat hL hflat⟩

end Semilinear

/-! ### Transporting the descended flat model to the quotient model of the chart -/

section Transport

/-- **The descended flat quotient transported along a ring isomorphism of the coefficients.**
Let `φ : B ≃+* D` be a ring isomorphism, let `k₁, …, k_m` be vectors in `D[x_1, …, x_n]ʳ` and
suppose the quotient of `D[x_1, …, x_n]ʳ` by their span is flat over `D`.  Then the quotient of
`B[x_1, …, x_n]ʳ` by the span of the vectors obtained by applying `φ⁻¹` coefficientwise is flat
over `B`.

This is deliberately stated for abstract coefficient rings: the instance needed for
Stacks Tag 053I has `D = Stacks.AffineBlowup.chartRing c`, a subring of the fraction field, and
  unification
against the flatness machinery spends an unbounded amount of time unfolding it — the same
phenomenon recorded in the implementation notes of
`StacksFrontier.RingTheory.Flat.BlowupDescent`. -/
theorem flat_quotient_of_ringEquiv {B : Type u} [CommRing B] {D : Type v} [CommRing D]
    (φ : B ≃+* D) {n r m : ℕ} (k : Fin m → (Fin r → MvPolynomial (Fin n) D))
    (hflat : Module.Flat D ((Fin r → MvPolynomial (Fin n) D) ⧸
      Submodule.span (MvPolynomial (Fin n) D) (Set.range k))) :
    Module.Flat B ((Fin r → MvPolynomial (Fin n) B) ⧸
      Submodule.span (MvPolynomial (Fin n) B)
        (Set.range fun j => vecMap n r φ.symm.toRingHom (k j))) := by
  set k' : Fin m → (Fin r → MvPolynomial (Fin n) B) :=
    fun j => vecMap n r φ.symm.toRingHom (k j) with hk'
  set L := Submodule.span (MvPolynomial (Fin n) B) (Set.range k')
  set Q := Submodule.span (MvPolynomial (Fin n) D) (Set.range k)
  have hkk : ∀ j, vecMap n r φ.toRingHom (k' j) = k j := fun j => by
    rw [hk', vecMap_vecMap, φ.toRingHom_comp_symm_toRingHom, vecMap_id]
  have hspanQ : Submodule.span (MvPolynomial (Fin n) D)
      (vecMap n r φ.toRingHom '' (L : Set (Fin r → MvPolynomial (Fin n) B))) = Q :=
    span_image_span_range (vecMap n r φ.toRingHom) k' k hkk
  have hspanL : Submodule.span (MvPolynomial (Fin n) B)
      (vecMap n r φ.symm.toRingHom '' (Q : Set (Fin r → MvPolynomial (Fin n) D))) = L :=
    span_image_span_range (vecMap n r φ.symm.toRingHom) k k' fun _ => rfl
  have hLQ : L ≤ Submodule.comap (vecMap n r φ.toRingHom) Q := fun v hv => by
    rw [Submodule.mem_comap, ← hspanQ]
    exact Submodule.subset_span ⟨v, hv, rfl⟩
  have hQL : Q ≤ Submodule.comap (vecMap n r φ.symm.toRingHom) L := fun w hw => by
    rw [Submodule.mem_comap, ← hspanL]
    exact Submodule.subset_span ⟨w, hw, rfl⟩
  set g := Submodule.mapQ L Q (vecMap n r φ.toRingHom) hLQ
  set g' := Submodule.mapQ Q L (vecMap n r φ.symm.toRingHom) hQL
  have hgg' : ∀ x, g' (g x) = x := by
    intro x
    obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective L x
    show Submodule.Quotient.mk
      (vecMap n r φ.symm.toRingHom (vecMap n r φ.toRingHom v)) = _
    rw [vecMap_vecMap, φ.symm_toRingHom_comp_toRingHom, vecMap_id]
  have hg'g : ∀ y, g (g' y) = y := by
    intro y
    obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective Q y
    show Submodule.Quotient.mk
      (vecMap n r φ.toRingHom (vecMap n r φ.symm.toRingHom w)) = _
    rw [vecMap_vecMap, φ.toRingHom_comp_symm_toRingHom, vecMap_id]
  have hsmul : ∀ (b : B) (p : MvPolynomial (Fin n) B),
      MvPolynomial.map φ.toRingHom (b • p) = φ b • MvPolynomial.map φ.toRingHom p := by
    intro b p
    rw [Algebra.smul_def, Algebra.smul_def, map_mul, MvPolynomial.algebraMap_eq,
      MvPolynomial.algebraMap_eq, MvPolynomial.map_C]
    rfl
  have _ : Module.Flat D ((Fin r → MvPolynomial (Fin n) D) ⧸ Q) := hflat
  refine Module.Flat.of_ringEquiv φ
    { toFun := g, invFun := g', left_inv := hgg', right_inv := hg'g, map_add' := map_add g }
    fun b x => ?_
  obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective L x
  show Submodule.Quotient.mk (vecMap n r φ.toRingHom (b • v)) =
    φ b • Submodule.Quotient.mk (p := Q) (vecMap n r φ.toRingHom v)
  rw [← Submodule.Quotient.mk_smul]
  exact congrArg _ (funext fun i => hsmul b (v i))

variable {R : Type u} [CommRing R] [IsDomain R] [IsLocalRing R] {K : Type v} [Field K]
  [Algebra R K] [IsFractionRing R K] {A : ValuationSubring K}

open Stacks.AffineBlowup

/-- **The descended flat model of Stacks Tag 053I on the quotient model of the chart.** This is
`Stacks.Flatness.BlowupFlattening.exists_chart_flat_model` with its conclusion carried across the
  identification
`Stacks.AffineBlowup.AdmissibleChart.blowupRingEquiv` of the chart ring `chartRing c`, a subring of
  `K`,
with the quotient model `Blowup c.I c.a` on which the strict transform of Stacks Tag 053H is
built.

So: for `(R, 𝔪)` a local domain with fraction field `K` and `𝔪 ≠ 0`, `A ⊆ K` a valuation ring
dominating `R` and `M` a finite module over `R[x_1, …, x_n]`, there are a rank `r`, finitely many
relation vectors over the quotient model of an admissible chart, and the corresponding quotient
of the finite free module is flat over that quotient model.

What is *not* asserted is any relation between these vectors and a presentation of `M`; supplying
that is gaps 2 and 3 of the implementation notes of
`StacksFrontier.RingTheory.Flat.BlowupFlatten`. -/
theorem exists_blowupChart_flat_model (hdom : Dominates R A)
    (hm : IsLocalRing.maximalIdeal R ≠ ⊥) (n : ℕ) (M : Type w) [AddCommGroup M]
    [Module (MvPolynomial (Fin n) R) M] [Module.Finite (MvPolynomial (Fin n) R) M] :
    ∃ (r m : ℕ) (c : AdmissibleChart R A)
      (k : Fin m → (Fin r → MvPolynomial (Fin n) (Blowup c.I c.a))),
      Module.Flat (Blowup c.I c.a)
        ((Fin r → MvPolynomial (Fin n) (Blowup c.I c.a)) ⧸
          Submodule.span (MvPolynomial (Fin n) (Blowup c.I c.a)) (Set.range k)) := by
  obtain ⟨r, m, c₀, c, hc, k, -, hflat⟩ := exists_chart_flat_model hdom hm n M
  exact ⟨r, m, c, fun j =>
    vecMap n r (AdmissibleChart.blowupRingEquiv c).symm.toRingHom
      (relGen hc k j),
    flat_quotient_of_ringEquiv (AdmissibleChart.blowupRingEquiv c) (relGen hc k) hflat⟩

end Transport

end Stacks.Flatness.BlowupFlattening
