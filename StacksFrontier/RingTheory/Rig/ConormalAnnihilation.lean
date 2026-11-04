module

public import StacksFrontier.RingTheory.Rig.JacobianAlgebraization
public import StacksFrontier.RingTheory.Rig.NaiveCotangent.CombinedPresentation
public import StacksFrontier.RingTheory.Rig.RigEtaleSurjection
public import StacksFrontier.RingTheory.Restricted.RigSmoothCriteria

/-!
# Conormal annihilation for a surjection of adic objects

Let `A` be a Noetherian ring, `I ⊆ A` an ideal, and let `T → B` be a **surjection** of objects
of the category of Stacks 0AL4 over `(A, I)`.  Stacks 0ALR
(`exists_finiteType_algEquiv_adicCompletion_of_cotangent_annihilated`) algebraizes `B` from
such a surjection as soon as a power of `I` annihilates the conormal module
`Ker(T → B)/Ker(T → B)²`, and that annihilation is a step of the proof of Stacks 0GAW.  This
file proves it from the two inputs the source uses, with one of them — the comparison of the two
degree-zero cohomologies — taken as a hypothesis.

## The route

Apply the six-term exact sequence of Stacks 0ALM
(`Rig.CompletedPolynomialPresentation.exists_sixTerm_exact_combined`) to the presentation of
`B` over `T` by **zero** outer variables.  The presenting ring is then the completed polynomial
algebra over `T` in no variables, which is `T` itself because `T` is `I`-adically complete
(`Rig.zeroVarRingEquiv`, which is `Rig.zeroVariableEquiv` at the adic ideal of `T`), so

* the degree-`1` term of `NL^∧_{B/T}` is `Ker(T → B)/Ker(T → B)²`
  (`Rig.ker_zeroVarExtension`), and its degree-`0` term vanishes, so
  `H⁻¹(NL^∧_{B/T})` is the whole conormal module;
* `H⁻¹(NL^∧_{B/A})` is annihilated by a power of `I` because `B` is rig-smooth — this is
  condition (3) of Stacks 0GAJ, `Rig.isRigSmooth_iff_cotangentFactorization`;
* what is left injects into the kernel of `H⁰(NL^∧_{T/A} ⊗_T B) → H⁰(NL^∧_{B/A})`.

The last kernel is what the source annihilates by inverting the element `b` of the Jacobian
chart, both localized `H⁰`'s being free of rank `r - m`; that comparison is **not** proved
here, it is the hypothesis `hcomparison` of the main theorem.  Note that the surjectivity of
the comparison is free: `H⁰(NL^∧_{B/T}) = 0` with no outer variables, so the fourth exactness
clause of `exists_sixTerm_exact_combined` gives it.  What the hypothesis carries is the
injectivity, after inverting `b`.

## Main results

* `Rig.smul_smul_eq_zero_of_exact_connecting` — the two-term-complex book-keeping: in a six-term
  exact sequence, a scalar annihilating `H⁻¹(Y)` times one annihilating `Ker(H⁰(X) → H⁰(Y))`
  annihilates `H⁻¹(Z)`.
* `Rig.zeroVarHom`, `Rig.zeroCombinedPresentation`, `Rig.ker_zeroVarExtension` — the
  zero-variable presentation of `B` over `T` and its kernel.
* `Rig.exists_pow_smul_conormal_eq_bot_of_hzeroComparison` — the conormal annihilation, given
  the comparison.

## What is **not** proved here, and why no hypothesis is a stand-in for the conclusion

The hypothesis `hcomparison` is not a weaker form of the conclusion: without a comparison of
the two degree-zero cohomologies the statement is **false**.  Take `A` Noetherian and
`I`-adically complete with `I` not nilpotent (say `A = ℤ_p`, `I = (p)`), `B = A`, and
`T = A⟨y⟩` the `I`-adic completion of `A[y]`, with `T → B` the evaluation `y ↦ 0`.  Both `B`
and `T` are rig-smooth over `(A, I)` — `B` because `A → A` is an isomorphism, `T` because
`A[y]` is smooth, `Rig.isRigSmooth_adicCompletionObj_of_smoothAwayFrom` — the map is
surjective, and `Ker(T → B) = (y)` is principal with `Ker/Ker² ≅ A` free of rank one, which
`I^c` does not annihilate for any `c`.  So no amount of rig-smoothness of the two ends implies
the conormal annihilation; the comparison of the `H⁰`'s is doing real work.

## References

* [Stacks Project, Tag 0ALM](https://stacks.math.columbia.edu/tag/0ALM)
* [Stacks Project, Tag 0ALR](https://stacks.math.columbia.edu/tag/0ALR)
* [Stacks Project, Tag 0GAJ](https://stacks.math.columbia.edu/tag/0GAJ)
* [Stacks Project, Tag 0GAW](https://stacks.math.columbia.edu/tag/0GAW)
-/

@[expose] public noncomputable section

open CategoryTheory

namespace Rig

universe u

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] AdicFiniteTypeAlgebra.isAdicallyComplete

/-! ## A two-term-complex lemma -/

section Abstract

open NaiveCotangent

variable {S : Type*} [CommRing S] {X Y Z : TwoTerm S}

/-- **Two scalars annihilating two neighbouring terms annihilate the third.**  In the six-term
exact sequence attached to a short exact sequence of two-term complexes, if `a` annihilates
`H⁻¹(Y)` and `b` annihilates the kernel of `H⁰(X) → H⁰(Y)`, then `ab` annihilates `H⁻¹(Z)`:
the connecting map sends `b · z` into that kernel, hence to zero, so `b · z` comes from
`H⁻¹(Y)`, where `a` kills it. -/
public theorem smul_smul_eq_zero_of_exact_connecting (α : ChainMap X Y) (β : ChainMap Y Z)
    (δ : H₁ Z →ₗ[S] H₀ X) (hβδ : Function.Exact β.onH₁ δ) (hδα : Function.Exact δ α.onH₀)
    (a b : S) (hY : ∀ y : H₁ Y, a • y = 0)
    (hker : ∀ y : H₀ X, α.onH₀ y = 0 → b • y = 0) (z : H₁ Z) :
    (a * b) • z = 0 := by
  have hδz : α.onH₀ (δ z) = 0 := hδα.apply_apply_eq_zero z
  have hbz : δ (b • z) = 0 := by rw [map_smul, hker _ hδz]
  obtain ⟨y, hy⟩ := (hβδ (b • z)).mp hbz
  rw [mul_smul, ← hy, ← map_smul, hY y, map_zero]

end Abstract

section ScalarAction

/-- **Annihilation of the conormal module of an extension, read at the level of ideals.**
Let `E` be an extension of `S` whose presenting ring is identified by a ring isomorphism `e`
with a ring `R'` in which the kernel of `E` is the ideal `J`.  If a scalar `s` of `S`
annihilates `E.Cotangent` and is the image of `e t`, then `t · J ⊆ J²`. -/
private theorem mul_mem_sq_of_smul_cotangent_eq_zero_aux
    {R S R' : Type*} [CommRing R] [CommRing S] [Algebra R S] [CommRing R']
    (E : Algebra.Extension R S) (e : R' ≃+* E.Ring) (J : Ideal R')
    (hJ : E.ker = J.map e) (t : R') (s : S)
    (hs : algebraMap E.Ring S (e t) = s)
    (h : ∀ x : E.Cotangent, s • x = 0) (y : R') (hy : y ∈ J) :
    t * y ∈ J ^ 2 := by
  have hyE : (e y) ∈ E.ker := by
    rw [hJ]; exact Ideal.mem_map_of_mem _ hy
  have hsmul : ∀ x : E.Cotangent, s • x = (e t) • x := fun x ↦ by
    rw [cotangent_ring_smul E (e t) x, hs]
  have hzero : Algebra.Extension.Cotangent.mk (P := E) ((e t) • (⟨e y, hyE⟩ : E.ker)) = 0 := by
    rw [map_smul, ← hsmul]
    exact h _
  have hval : (((e t) • (⟨e y, hyE⟩ : E.ker) : E.ker) : E.Ring) = e (t * y) := by
    simp [map_mul]
  have hmem : e (t * y) ∈ E.ker ^ 2 := by
    rw [← hval]
    exact (Algebra.Extension.Cotangent.mk_eq_zero_iff (P := E) _).mp hzero
  have hmem2 : e (t * y) ∈ (J ^ 2).map e := by
    rw [Ideal.map_pow, ← hJ]
    exact hmem
  exact Ideal.apply_mem_of_equiv_iff.mp hmem2

end ScalarAction

/-! ## The zero-variable presentation of a quotient -/

variable {A : Type u} [CommRing A] [IsNoetherianRing A] {I : Ideal A}

section Setup

variable (T B : AdicFiniteTypeAlgebra.{u, u} A I) [Algebra T.carrier B.carrier]
  [IsScalarTower A T.carrier B.carrier]

/-- The identification of the `I`-adically complete ring `T` with the completed polynomial
algebra over `T` in zero variables: `Rig.zeroVariableEquiv` at the adic ideal of `T`. -/
public def zeroVarRingEquiv :
    T.carrier ≃+* AdicCompletion.completedMvPolynomial T.adicIdeal (Fin 0) :=
  zeroVariableEquiv T.adicIdeal

/-- The presentation of a quotient `B` of `T` by **zero** outer variables: the structure map
`T → B` read through `Rig.zeroVarRingEquiv`. -/
public def zeroVarHom :
    AdicCompletion.completedMvPolynomial T.adicIdeal (Fin 0) →ₐ[T.carrier] B.carrier where
  toRingHom := (algebraMap T.carrier B.carrier).comp (zeroVarRingEquiv T).symm.toRingHom
  commutes' t := by
    change algebraMap T.carrier B.carrier ((zeroVarRingEquiv T).symm
      (algebraMap T.carrier _ t)) = _
    rw [show algebraMap T.carrier
        (AdicCompletion.completedMvPolynomial T.adicIdeal (Fin 0)) t =
        zeroVarRingEquiv T t from (zeroVariableEquiv_apply T.adicIdeal t).symm,
      RingEquiv.symm_apply_apply]

omit [IsNoetherianRing A] [IsScalarTower A T.carrier B.carrier] in
/-- `Rig.zeroVarHom` is the structure map `T → B` composed with an isomorphism. -/
public theorem zeroVarHom_apply (x : AdicCompletion.completedMvPolynomial T.adicIdeal (Fin 0)) :
    zeroVarHom T B x = algebraMap T.carrier B.carrier ((zeroVarRingEquiv T).symm x) := rfl

omit [IsNoetherianRing A] in
/-- `Rig.zeroVarHom` is surjective as soon as `T → B` is. -/
public theorem surjective_zeroVarHom
    (hsurj : Function.Surjective (algebraMap T.carrier B.carrier)) :
    Function.Surjective ((zeroVarHom T B).restrictScalars A) :=
  hsurj.comp (zeroVarRingEquiv T).symm.surjective

variable (hsurj : Function.Surjective (algebraMap T.carrier B.carrier))

/-- The presentation `B = A⟨x₁, …, x_r⟩ / K` of Stacks 0ALM obtained from a presentation
`T = A⟨x₁, …, x_r⟩ / J` of `T` and a surjection `T → B`, with no new variables. -/
public def zeroCombinedPresentation (P : CompletedPolynomialPresentation I T) :
    CompletedPolynomialPresentation I B :=
  P.combinedPresentation 0 ((zeroVarHom T B).restrictScalars A)
    (surjective_zeroVarHom T B hsurj)

/-- The extension of `T`-algebras presenting `B` by zero variables. -/
public abbrev zeroVarExtension : Algebra.Extension T.carrier B.carrier :=
  Algebra.Extension.ofSurjective (zeroVarHom T B) (surjective_zeroVarHom T B hsurj)

omit [IsNoetherianRing A] in
/-- The kernel of the zero-variable presentation of `B` over `T` is the kernel of `T → B`,
transported along `Rig.zeroVarRingEquiv`. -/
public theorem ker_zeroVarExtension :
    (zeroVarExtension T B hsurj).ker =
      (RingHom.ker (algebraMap T.carrier B.carrier)).map (zeroVarRingEquiv T) := by
  rw [← Ideal.comap_symm]
  exact Ideal.ext fun x ↦ Iff.rfl

omit [IsNoetherianRing A] in
/-- **Annihilation of the conormal module, read at the level of ideals.**  If a scalar of `T`
annihilates the conormal module of the zero-variable presentation of `B` over `T`, then it
carries the kernel of `T → B` into its square. -/
public theorem mul_mem_sq_of_smul_cotangent_eq_zero (t : T.carrier)
    (h : ∀ x : (zeroVarExtension T B hsurj).Cotangent,
      (algebraMap T.carrier B.carrier t) • x = 0) (y : T.carrier)
    (hy : y ∈ RingHom.ker (algebraMap T.carrier B.carrier)) :
    t * y ∈ RingHom.ker (algebraMap T.carrier B.carrier) ^ 2 :=
  mul_mem_sq_of_smul_cotangent_eq_zero_aux (zeroVarExtension T B hsurj) (zeroVarRingEquiv T)
    (RingHom.ker (algebraMap T.carrier B.carrier)) (ker_zeroVarExtension T B hsurj) t
    (algebraMap T.carrier B.carrier t)
    (by
      change zeroVarHom T B (zeroVarRingEquiv T t) = algebraMap T.carrier B.carrier t
      rw [zeroVarHom_apply, RingEquiv.symm_apply_apply])
    h y hy

end Setup

/-! ## The conormal annihilation -/

section Main

variable (T B : AdicFiniteTypeAlgebra.{u, u} A I) [Algebra T.carrier B.carrier]
  [IsScalarTower A T.carrier B.carrier]
  (hsurj : Function.Surjective (algebraMap T.carrier B.carrier))
  (P : CompletedPolynomialPresentation I T)

/-- **The conormal annihilation step in the proof of Stacks 0GAW.**

Let `A` be a Noetherian ring, `I ⊆ A` an ideal, and let `T → B` be a surjection of objects of
the category of Stacks 0AL4 over `(A, I)`, with `T` presented as `T = A⟨x₁, …, x_r⟩/J`.  Assume

* `B` is rig-smooth over `(A, I)`;
* a power of `I` annihilates the kernel of the comparison map
  `H⁰(NL^∧_{T/A} ⊗_T B) → H⁰(NL^∧_{B/A})` of Stacks 0ALM, written out here as: a power of `I`
  carries every `r`-tuple over `B` whose extension by zero is a relation of the combined
  presentation of `B` into the relations coming from `T`.

Then a power of `I` annihilates `Ker(T → B)/Ker(T → B)²`, which is the hypothesis of
Stacks 0ALR (`exists_finiteType_algEquiv_adicCompletion_of_cotangent_annihilated`).

This is the last paragraph of the proof of Stacks 0GAW, minus the comparison.  The six-term
exact sequence of Stacks 0ALM
(`Rig.CompletedPolynomialPresentation.exists_sixTerm_exact_combined`) at `s = 0`

```
H⁻¹(NL^∧_{T/A} ⊗_T B) → H⁻¹(NL^∧_{B/A}) → H⁻¹(NL^∧_{B/T}) →
  H⁰(NL^∧_{T/A} ⊗_T B) → H⁰(NL^∧_{B/A}) → 0
```

has `H⁻¹(NL^∧_{B/T}) = Ker(T → B)/Ker(T → B)²`, because with no outer variables the presenting
ring of `B` over `T` is `T` itself (`Rig.zeroVarRingEquiv`, `Rig.ker_zeroVarExtension`) and the
degree-`0` term of `NL^∧_{B/T}` vanishes.  A power of `I` annihilates `H⁻¹(NL^∧_{B/A})` because
`B` is rig-smooth — condition (3) of Stacks 0GAJ,
`Rig.isRigSmooth_iff_cotangentFactorization` — and what is left injects into the kernel of the
`H⁰` comparison, which the second hypothesis annihilates.

**The second hypothesis is not a repackaging of the conclusion.**  The source proves it by
inverting the element `b` of the Jacobian chart: both localized `H⁰`'s are free
`B[1/b]`-modules of rank `r - m` on the classes of `dx_{m+1}, …, dx_r`, so the comparison is an
isomorphism after inverting `b`, and `V(b) ⊆ V(IB)` turns `b`-power torsion into `I`-power
torsion.  That argument is not part of this theorem: it is the hypothesis `hcomparison`.

The hypothesis also cannot be dropped in favour of rig-smoothness of `T`: for `A = B` and
`T = A⟨y⟩` with `T → B` the evaluation `y ↦ 0`, both ends are rig-smooth over `(A, I)` and the
map is surjective, while `Ker(T → B)/Ker(T → B)² ≅ A` is free of rank one, which no power of a
non-nilpotent `I` annihilates.  A comparison of the two `H⁰`'s is therefore genuinely needed;
see the module docstring. -/
public theorem exists_pow_smul_conormal_eq_bot_of_hzeroComparison
    (hB : IsRigSmooth B)
    (hcomparison : ∃ c : ℕ, ∀ a ∈ I ^ c, ∀ v : Fin P.variableCount → B.carrier,
      NaiveCotangent.finInl B.carrier P.variableCount 0 v ∈
          LinearMap.range (completedNaiveCotangentComplex B
            (zeroCombinedPresentation T B hsurj P)).differential →
        algebraMap A B.carrier a • v ∈ LinearMap.range
          (P.innerBaseChangeDifferential (C := B) (completedNaiveCotangentComplex T P))) :
    ∃ c : ℕ, I ^ c •
      (⊤ : Submodule A (RingHom.ker (algebraMap T.carrier B.carrier)).Cotangent) = ⊥ := by
  classical
  obtain ⟨cH, hcH⟩ := hcomparison
  obtain ⟨cB, hcB⟩ :=
    (isRigSmooth_iff_cotangentFactorization B (zeroCombinedPresentation T B hsurj P)).mp hB
  obtain ⟨δ, h1, h2, h3, h4, h5⟩ :=
    P.exists_sixTerm_exact_combined 0 (zeroVarHom T B) (surjective_zeroVarHom T B hsurj)
      (completedNaiveCotangentComplex T P)
      (completedNaiveCotangentComplex B (zeroCombinedPresentation T B hsurj P))
      (fun j ↦ j.elim0) (fun j ↦ j.elim0) (fun j ↦ j.elim0)
  -- `H⁻¹(NL^∧_{B/A})` is annihilated by `I^{cB}`: `B` is rig-smooth
  have hY : ∀ a ∈ I ^ cB, ∀ y : NaiveCotangent.H₁ (NaiveCotangent.TwoTerm.ofFree
      (P.combinedDifferential 0 (zeroVarHom T B) (surjective_zeroVarHom T B hsurj)
        (completedNaiveCotangentComplex B (zeroCombinedPresentation T B hsurj P)))),
      (algebraMap A B.carrier a) • y = 0 := by
    intro a ha y
    obtain ⟨h, hh⟩ := hcB a ha
    have hd : (completedNaiveCotangentComplex B
        (zeroCombinedPresentation T B hsurj P)).differential y.1 = 0 :=
      LinearMap.mem_ker.mp y.2
    have hval : (algebraMap A B.carrier a) • y.1 = 0 := by
      have hy : h ((completedNaiveCotangentComplex B
            (zeroCombinedPresentation T B hsurj P)).differential y.1) =
          (algebraMap A B.carrier a) • y.1 := LinearMap.congr_fun hh y.1
      rw [hd, map_zero] at hy
      exact hy.symm
    exact Subtype.ext hval
  -- the kernel of the `H⁰` comparison is annihilated by `I^{cH}`: the hypothesis
  have hker : ∀ a ∈ I ^ cH, ∀ y : NaiveCotangent.H₀ (NaiveCotangent.TwoTerm.ofFree
      (P.innerBaseChangeDifferential (C := B) (completedNaiveCotangentComplex T P))),
      (NaiveCotangent.chainMapInl _
        (P.combinedDifferential_comp_innerCotangentMap 0 (zeroVarHom T B)
          (surjective_zeroVarHom T B hsurj) (completedNaiveCotangentComplex T P)
          (completedNaiveCotangentComplex B (zeroCombinedPresentation T B hsurj P)))).onH₀ y
        = 0 → (algebraMap A B.carrier a) • y = 0 := by
    intro a ha y hy
    obtain ⟨v, rfl⟩ := Submodule.mkQ_surjective _ y
    rw [NaiveCotangent.ChainMap.onH₀_mkQ, NaiveCotangent.chainMapInl_f₀,
      Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hy
    rw [← map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact hcH a ha v hy
  -- with no outer variables every class lies in `H⁻¹(NL^∧_{B/T})`
  have hH₁Z : ∀ x : (zeroVarExtension T B hsurj).Cotangent,
      x ∈ NaiveCotangent.H₁ (NaiveCotangent.TwoTerm.ofFree
        (CompletedPolynomialPresentation.outerDifferential 0 (zeroVarHom T B)
          (surjective_zeroVarHom T B hsurj) (fun j ↦ j.elim0))) := by
    intro x
    have hz : CompletedPolynomialPresentation.outerDifferential 0 (zeroVarHom T B)
        (surjective_zeroVarHom T B hsurj) (fun j ↦ j.elim0) x = 0 := funext fun j ↦ j.elim0
    exact hz
  -- hence `I^{cB + cH}` annihilates the conormal module of the zero-variable presentation
  have hkey : ∀ a ∈ I ^ (cB + cH), ∀ x : (zeroVarExtension T B hsurj).Cotangent,
      (algebraMap A B.carrier a) • x = 0 := by
    intro a ha
    rw [pow_add] at ha
    refine Submodule.mul_induction_on ha
      (C := fun r ↦ ∀ x : (zeroVarExtension T B hsurj).Cotangent,
        (algebraMap A B.carrier r) • x = 0) ?_ ?_
    · intro r hr s hs x
      have hzero := smul_smul_eq_zero_of_exact_connecting _ _ δ h2 h3
        (algebraMap A B.carrier r) (algebraMap A B.carrier s) (hY r hr) (hker s hs)
        ⟨x, hH₁Z x⟩
      have h0 : (algebraMap A B.carrier r * algebraMap A B.carrier s) • x = 0 :=
        congrArg Subtype.val hzero
      rw [map_mul]
      exact h0
    · intro x y hx hy z
      rw [map_add, add_smul, hx z, hy z, add_zero]
  -- transport to the conormal module of `T → B` itself
  refine ⟨cB + cH, le_antisymm (Submodule.smul_le.mpr ?_) bot_le⟩
  intro a ha z _
  obtain ⟨⟨y, hy⟩, rfl⟩ := Ideal.toCotangent_surjective _ z
  rw [Submodule.mem_bot, ← algebraMap_smul T.carrier, ← map_smul]
  refine (Ideal.toCotangent_eq_zero _ _).mpr ?_
  rw [Submodule.coe_smul, smul_eq_mul]
  refine mul_mem_sq_of_smul_cotangent_eq_zero T B hsurj (algebraMap A T.carrier a) ?_ y hy
  intro x
  rw [← IsScalarTower.algebraMap_apply A T.carrier B.carrier]
  exact hkey a ha x

/-- **The `H⁰` comparison of Stacks 0ALM is surjective at `s = 0`.**  With no outer variables
the degree-`0` term of `NL^∧_{B/T}` vanishes, so `H⁰(NL^∧_{B/T}) = 0` and the fourth exactness
clause of the six-term sequence makes `H⁰(NL^∧_{T/A} ⊗_T B) → H⁰(NL^∧_{B/A})` surjective.
What the hypothesis `hcomparison` of
`Rig.exists_pow_smul_conormal_eq_bot_of_hzeroComparison` adds is therefore exactly injectivity
up to `I`-power torsion. -/
public theorem surjective_hzeroComparison :
    Function.Surjective (NaiveCotangent.chainMapInl _
      (P.combinedDifferential_comp_innerCotangentMap 0 (zeroVarHom T B)
        (surjective_zeroVarHom T B hsurj) (completedNaiveCotangentComplex T P)
        (completedNaiveCotangentComplex B (zeroCombinedPresentation T B hsurj P)))).onH₀ := by
  obtain ⟨δ, h1, h2, h3, h4, h5⟩ :=
    P.exists_sixTerm_exact_combined 0 (zeroVarHom T B) (surjective_zeroVarHom T B hsurj)
      (completedNaiveCotangentComplex T P)
      (completedNaiveCotangentComplex B (zeroCombinedPresentation T B hsurj P))
      (fun j ↦ j.elim0) (fun j ↦ j.elim0) (fun j ↦ j.elim0)
  intro y
  refine (h4 y).mp ?_
  obtain ⟨v, rfl⟩ := Submodule.mkQ_surjective _ y
  rw [NaiveCotangent.ChainMap.onH₀_mkQ, NaiveCotangent.chainMapProj_f₀,
    Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  exact ⟨0, by
    rw [map_zero]
    exact (funext fun j ↦ j.elim0 : NaiveCotangent.finProj B.carrier P.variableCount 0 v = 0).symm⟩

/-- **`b`-power torsion suffices for the comparison hypothesis.**  If an element `b` of `B`
cuts out a closed subset inside `V(IB)` and `b^k` already carries the relations of the combined
presentation into the relations coming from `T`, then a power of `I` does, which is the
hypothesis `hcomparison` of `Rig.exists_pow_smul_conormal_eq_bot_of_hzeroComparison`.

This is the reduction the source makes before localizing: "it suffices to show that it is
annihilated by a power of `b`". -/
public theorem hzeroComparison_of_pow_smul (b : B.carrier) (k : ℕ)
    (hvanish : B.adicIdeal ≤ (Ideal.span {b}).radical)
    (htorsion : ∀ v : Fin P.variableCount → B.carrier,
      NaiveCotangent.finInl B.carrier P.variableCount 0 v ∈
          LinearMap.range (completedNaiveCotangentComplex B
            (zeroCombinedPresentation T B hsurj P)).differential →
        b ^ k • v ∈ LinearMap.range
          (P.innerBaseChangeDifferential (C := B) (completedNaiveCotangentComplex T P))) :
    ∃ c : ℕ, ∀ a ∈ I ^ c, ∀ v : Fin P.variableCount → B.carrier,
      NaiveCotangent.finInl B.carrier P.variableCount 0 v ∈
          LinearMap.range (completedNaiveCotangentComplex B
            (zeroCombinedPresentation T B hsurj P)).differential →
        algebraMap A B.carrier a • v ∈ LinearMap.range
          (P.innerBaseChangeDifferential (C := B) (completedNaiveCotangentComplex T P)) := by
  obtain ⟨c, hc⟩ := exists_pow_adicIdeal_le_span_of_le_radical B b hvanish
  refine ⟨c * k, fun a ha v hv ↦ ?_⟩
  have hmem : algebraMap A B.carrier a ∈ Ideal.span {b ^ k} := by
    have h1 : algebraMap A B.carrier a ∈ (B.adicIdeal ^ c) ^ k := by
      rw [← pow_mul, show B.adicIdeal ^ (c * k) = (I ^ (c * k)).map (algebraMap A B.carrier) from
        by rw [show B.adicIdeal = I.map (algebraMap A B.carrier) from rfl, Ideal.map_pow]]
      exact Ideal.mem_map_of_mem _ ha
    have h2 : (B.adicIdeal ^ c) ^ k ≤ Ideal.span {b ^ k} := by
      rw [← Ideal.span_singleton_pow]
      exact Ideal.pow_right_mono hc k
    exact h2 h1
  obtain ⟨w, hw⟩ := Ideal.mem_span_singleton'.mp hmem
  rw [← hw, mul_smul]
  exact Submodule.smul_mem _ w (htorsion v hv)

end Main

end Rig

end
