module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.Rig.Algebraization.MultiJacobianCotangentCokernel
public import StacksFrontier.RingTheory.Rig.Algebraization.PrincipalSurjection
public import StacksFrontier.RingTheory.Rig.ConormalAnnihilation
public import StacksFrontier.RingTheory.Rig.RigEtaleLocus
public import StacksFrontier.RingTheory.RigSmooth.ComparisonAlgHom

/-!
# Stacks 0ALS: the rig-étale case of Elkik's theorem over a principal ideal

Let `A` be a Noetherian ring and `I = (a)` a principal ideal.  Let `B` be an object of the
category of Stacks 0AL4 over `(A, I)` which is rig-étale over `(A, I)`.  Then `B` is the
`I`-adic completion of a finite type `A`-algebra.  This file proves that, with no carried
hypothesis.

## The route

The three inputs are already in the library; what this file does is close the one gap between
them and compose them.

1. `Rig.exists_jacobianCriterion_of_isRigEtale_principal` (Stacks 0AJU part (6)) gives a
   **square** Jacobian chart for a presentation `B = A⟨x₁, …, x_r⟩/J`: an element `b = a^c`
   with `V(b) ⊆ V(IB)`, elements `f₁, …, f_r ∈ J` — as many as there are variables — whose
   Jacobian determinant divides the image of `b`, and `bJ ⊆ (f₁, …, f_r) + J²`.
2. `Rig.exists_multiJacobian_surjection_of_jacobianChart_principal` (Stacks 0GAW up to its
   last step) builds from that chart the finite type `A`-algebra
   `C = A[z, x₁, …, x_r]/(zΔ' - a^{c₁}, f'₁, …, f'_r)` of Stacks 0GAV and a **surjection**
   `φ : C^∧ ↠ B`.
3. `Rig.exists_pow_smul_conormal_eq_bot_of_hzeroComparison` turns the comparison of the two
   degree-`0` cohomologies of Stacks 0ALM into the annihilation of `Ker(φ)/Ker(φ)²` by a power
   of `I`, and `exists_finiteType_algEquiv_adicCompletion_of_cotangent_annihilated`
   (Stacks 0ALR) turns *that* into an isomorphism `B ≅ D^∧` for a finite type `A`-algebra `D`.

The gap was the comparison in (3).  The source of Stacks 0GAW proves it by inverting `b` and
observing that both localized `H⁰`'s are free `B[1/b]`-modules of rank `r - m`.  Here the
chart is square, `m = r`, so that rank is `0`: *both* localized modules vanish, and the
vanishing of the first one alone already annihilates the kernel.  Better still, for the
algebra `C` that step (2) builds the vanishing holds with an exponent produced over `A`
directly, with no localization at all — the presentation of `C` has `1 + r` variables and
`1 + r` relations, its Jacobian determinant is `(Δ')²`, and `a^{c₁} = zΔ'` in `C`.  That is
`Rig.pow_smul_mem_range_innerBaseChangeDifferential_multiJacobian`, which supplies the
hypothesis `hcomparison` in the strong form that ignores the relation it is applied to.

## Main results

* `Rig.exists_finiteType_algEquiv_of_multiJacobian_surjection` — the conormal annihilation and
  Stacks 0ALR for a surjection out of the completion of a *square* multi-Jacobian algebra.
* `Rig.exists_finiteType_algEquiv_of_jacobianChart_principal_square` — the same from a square
  Jacobian chart on `B`: this is Stacks 0GAW in the square case over a principal ideal.
* `Rig.exists_finiteType_algEquiv_of_isRigEtale_principal_sameUniverse` — **Stacks 0ALS** for a
  `B` whose carrier lies in the universe of `A`, which is what the six-term exact sequence of
  Stacks 0ALM needs: it requires the source and the target of the surjection in one universe,
  and the source is the completion of a finite type `A`-algebra.
* `Rig.exists_finiteType_algEquiv_of_isRigEtale_principal` — **Stacks 0ALS** with no universe
  restriction, by replacing `B` with the quotient `A⟨x₁, …, x_r⟩/J` of one of its
  presentations (`Rig.quotientObj`, `Rig.isRigEtale_of_algEquiv`).

## Relation to `Rig.exists_finiteType_algEquiv_adicCompletion_of_isRigEtale_principal`

`StacksFrontier.RingTheory.Rig.RigEtaleLifting` states Stacks 0ALS with the whole of Stacks 0GAW
carried as a hypothesis `jacobianAlgebraization`, and deliberately places no tag.  That
declaration is left untouched; the theorem here is the unconditional one and carries the tag.
The two are distinct constants with distinct names.

## References

* [Stacks Project, Tag 0ALS](https://stacks.math.columbia.edu/tag/0ALS)
* [Stacks Project, Tag 0GAW](https://stacks.math.columbia.edu/tag/0GAW)
* [Stacks Project, Tag 0ALR](https://stacks.math.columbia.edu/tag/0ALR)
* [Stacks Project, Tag 0ALM](https://stacks.math.columbia.edu/tag/0ALM)
* [Stacks Project, Tag 0AJU](https://stacks.math.columbia.edu/tag/0AJU)
-/

@[expose] public noncomputable section

open CategoryTheory MvPolynomial

namespace Rig

universe u v

attribute [local instance] HasDerivedCategory.standard

section Main

variable {A : Type u} [CommRing A] [IsNoetherianRing A] {I : Ideal A}

/-- **A surjection onto `B` from the completion of a square multi-Jacobian algebra
algebraizes `B`.**

Let `A` be a Noetherian ring, `I = (a)` a principal ideal, and
`C = A[z, x₁, …, x_r]/(zΔ - a^{c₁}, f'₁, …, f'_r)` the multi-generator Jacobian algebra of
Stacks 0GAV for the one-element family `{a}` and a **square** system `f'₁, …, f'_r` of
polynomials in `r` variables.  Let `B` be a rig-smooth object of the category of Stacks 0AL4
over `(A, I)` and `φ : C^∧ → B` a surjection of `A`-algebras.  Then `B` is the `I`-adic
completion of a finite type `A`-algebra.

The conormal module `Ker(φ)/Ker(φ)²` is annihilated by a power of `I`: the degree-`0`
cohomology `H⁰(NL^∧_{C^∧/A} ⊗_{C^∧} B)` is annihilated by a power of `I` outright
(`Rig.pow_smul_mem_range_innerBaseChangeDifferential_multiJacobian`, which is Cramer's rule on
the square presentation of `C`), so a fortiori the kernel of its comparison to
`H⁰(NL^∧_{B/A})` is, and the six-term exact sequence of Stacks 0ALM then gives the
annihilation (`Rig.exists_pow_smul_conormal_eq_bot_of_hzeroComparison`).  Stacks 0ALR
concludes. -/
public theorem exists_finiteType_algEquiv_of_multiJacobian_surjection {r : ℕ}
    (a : A) (hI : I = Ideal.span {a}) (hm : r ≤ r)
    (f' : Fin r → MvPolynomial (Fin r) A) (c₁ : ℕ)
    (B : AdicFiniteTypeAlgebra.{u, u} A I) (hB : IsRigSmooth B)
    (φ : AdicCompletion (I.map (algebraMap A (MultiJacobianAlgebra hm f' (fun _ : Fin 1 ↦ a) c₁)))
        (MultiJacobianAlgebra hm f' (fun _ : Fin 1 ↦ a) c₁) →ₐ[A] B.carrier)
    (hφ : Function.Surjective φ) :
    ∃ (C : Type u) (_ : CommRing C) (_ : Algebra A C),
      Algebra.FiniteType A C ∧
        Nonempty (B.carrier ≃ₐ[A] AdicCompletion (I.map (algebraMap A C)) C) := by
  classical
  have hagen : I = Ideal.span (Set.range (fun _ : Fin 1 ↦ a)) := by
    rw [hI, Set.range_const]
  let : Algebra (adicCompletionObj I
      (B := MultiJacobianAlgebra hm f' (fun _ : Fin 1 ↦ a) c₁)).carrier B.carrier :=
    φ.toRingHom.toAlgebra
  have : IsScalarTower A (adicCompletionObj I
      (B := MultiJacobianAlgebra hm f' (fun _ : Fin 1 ↦ a) c₁)).carrier B.carrier :=
    IsScalarTower.of_algebraMap_eq fun x ↦ (φ.commutes x).symm
  have hsurj : Function.Surjective (algebraMap (adicCompletionObj I
      (B := MultiJacobianAlgebra hm f' (fun _ : Fin 1 ↦ a) c₁)).carrier B.carrier) := hφ
  obtain ⟨c, hc⟩ := exists_pow_smul_conormal_eq_bot_of_hzeroComparison
    (adicCompletionObj I (B := MultiJacobianAlgebra hm f' (fun _ : Fin 1 ↦ a) c₁)) B hsurj
    (multiJacobianCompletedPresentation I hm f' (fun _ : Fin 1 ↦ a) c₁) hB
    ⟨1 + 1 * ((1 + 1) * c₁ - 1), fun y hy v _ ↦
      pow_smul_mem_range_innerBaseChangeDifferential_multiJacobian hm f' (fun _ : Fin 1 ↦ a) c₁
        hagen B y hy v⟩
  exact exists_finiteType_algEquiv_adicCompletion_of_cotangent_annihilated A
    (MultiJacobianAlgebra hm f' (fun _ : Fin 1 ↦ a) c₁) B.carrier I φ hφ c hc

/-- **Stacks 0GAW over a principal ideal, in the square case.**  Let `A` be a Noetherian ring,
`I = (a)` principal, and let `B` be an object of the category of Stacks 0AL4 carrying a
**square** Jacobian chart on a presentation `B = A⟨x₁, …, x_r⟩/J`: an element `b` with
`V(b) ⊆ V(IB)`, elements `f₁, …, f_r ∈ J`, one for each variable, whose Jacobian determinant
divides the image of `b`, and `bJ ⊆ (f₁, …, f_r) + J²`.  Then `B` is the `I`-adic completion of
a finite type `A`-algebra.

No `stacks` attribute for 0GAW is placed: 0GAW asserts this for a chart of any size `m ≤ r`,
and it is the square case `m = r` that is proved here — which is the case Stacks 0ALS needs,
and the only case in which the comparison of the two degree-`0` cohomologies is the vanishing
statement proved in
`Rig.pow_smul_mem_range_innerBaseChangeDifferential_multiJacobian`. -/
public theorem exists_finiteType_algEquiv_of_jacobianChart_principal_square
    (a : A) (hI : I = Ideal.span {a})
    (B : AdicFiniteTypeAlgebra.{u, u} A I) (P : CompletedPolynomialPresentation I B)
    (b : P.completedPolynomialRing) (f : Fin P.variableCount → P.ker)
    (hvanish : B.adicIdeal ≤ (Ideal.span {P.toAlgHom b}).radical)
    (hjacobian :
      P.toAlgHom (Matrix.det fun i j : Fin P.variableCount ↦
        (completedNaiveCotangentComplex B P).partialDeriv (Fin.castLE le_rfl i)
          (f j : P.completedPolynomialRing)) ∣ P.toAlgHom b)
    (hrelations : ∀ x : P.completedPolynomialRing, x ∈ P.ker →
      b * x ∈ Ideal.span (Set.range fun j : Fin P.variableCount ↦
        (f j : P.completedPolynomialRing)) + P.ker ^ 2) :
    ∃ (C : Type u) (_ : CommRing C) (_ : Algebra A C),
      Algebra.FiniteType A C ∧
        Nonempty (B.carrier ≃ₐ[A] AdicCompletion (I.map (algebraMap A C)) C) := by
  obtain ⟨f', c₁, φ, hφsurj, -, hBsmooth, -⟩ :=
    exists_multiJacobian_surjection_of_jacobianChart_principal a hI B P P.variableCount le_rfl b
      f hvanish hjacobian hrelations
  exact exists_finiteType_algEquiv_of_multiJacobian_surjection a hI le_rfl f' c₁ B hBsmooth φ
    hφsurj

/-- **Stacks 0ALS**, the rig-étale case of [Elkik, III Theorem 7].  Let `A` be a Noetherian
ring and `I = (a)` a principal ideal.  Let `B` be an object of the category of `I`-adically
complete `A`-algebras of finite type modulo `I` (Stacks 0AL4) which is rig-étale over `(A, I)`.
Then there is a finite type `A`-algebra `C` and an isomorphism `B ≅ C^∧`.

Rig-étaleness supplies a square Jacobian chart on any presentation of `B`
(`Rig.exists_jacobianCriterion_of_isRigEtale_principal`, Stacks 0AJU part (6)), and
`Rig.exists_finiteType_algEquiv_of_jacobianChart_principal_square` algebraizes it.

This is the case in which the carrier of `B` lies in the universe of `A`.  The general case
is `Rig.exists_finiteType_algEquiv_of_isRigEtale_principal`, obtained from this one by
replacing `B` with the quotient `A⟨x₁, …, x_r⟩/J` of one of its presentations; the universe
restriction here is inherited from `Rig.exists_pow_smul_conormal_eq_bot_of_hzeroComparison`,
whose six-term exact sequence needs the surjection's source and target in a common
universe. -/
public theorem exists_finiteType_algEquiv_of_isRigEtale_principal_sameUniverse
    (hI : I.IsPrincipal) (B : AdicFiniteTypeAlgebra.{u, u} A I) (hB : IsRigEtale B) :
    ∃ (C : Type u) (_ : CommRing C) (_ : Algebra A C),
      Algebra.FiniteType A C ∧
        Nonempty (B.carrier ≃ₐ[A] AdicCompletion (I.map (algebraMap A C)) C) := by
  obtain ⟨a, ha⟩ := hI.principal
  obtain ⟨P⟩ := nonempty_completedPolynomialPresentation hI.fg B
  obtain ⟨b, f, hvanish, hjacobian, hrelations⟩ :=
    exists_jacobianCriterion_of_isRigEtale_principal hI B P hB
  refine exists_finiteType_algEquiv_of_jacobianChart_principal_square a ha B P b f hvanish ?_
    (fun x hx ↦ hrelations ⟨x, hx⟩)
  -- the chart of `exists_jacobianCriterion_of_isRigEtale_principal` takes the determinant of
  -- the images; the chart of Stacks 0GAW takes the image of the determinant
  have hbridge : P.toAlgHom (Matrix.det fun i j : Fin P.variableCount ↦
        (completedNaiveCotangentComplex B P).partialDeriv (Fin.castLE le_rfl i)
          (f j : P.completedPolynomialRing)) =
      Matrix.det fun i j : Fin P.variableCount ↦ P.toAlgHom
        ((completedNaiveCotangentComplex B P).partialDeriv i
          (f j : P.completedPolynomialRing)) := by
    simp only [Fin.castLE_rfl, id_eq]
    exact RingHom.map_det (P.toAlgHom : P.completedPolynomialRing →+* B.carrier) _
  rw [hbridge]
  exact hjacobian

/-- **Stacks 0ALS**, the rig-étale case of [Elkik, III Theorem 7], with no restriction on the
universe of `B`.  Let `A` be a Noetherian ring and `I = (a)` a principal ideal.  Let `B` be an
object of the category of `I`-adically complete `A`-algebras of finite type modulo `I`
(Stacks 0AL4) which is rig-étale over `(A, I)`.  Then there is a finite type `A`-algebra `C`
and an isomorphism `B ≅ C^∧`.

The carrier of `B` is replaced by the quotient `A⟨x₁, …, x_r⟩/J` of a presentation of `B`
(`Rig.quotientObj`), which lives in the universe of `A` and is `A`-algebra isomorphic to
`B.carrier` by `Rig.CompletedPolynomialPresentation.quotientEquiv`; rig-étaleness transports
across that isomorphism by `Rig.isRigEtale_of_algEquiv` (Stacks 0GB2), and
`Rig.exists_finiteType_algEquiv_of_isRigEtale_principal_sameUniverse` applies to it. -/
@[stacks 0ALS "the rig-étale case of Elkik III Theorem 7, over a principal ideal"]
public theorem exists_finiteType_algEquiv_of_isRigEtale_principal
    (hI : I.IsPrincipal) (B : AdicFiniteTypeAlgebra.{u, v} A I) (hB : IsRigEtale B) :
    ∃ (C : Type u) (_ : CommRing C) (_ : Algebra A C),
      Algebra.FiniteType A C ∧
        Nonempty (B.carrier ≃ₐ[A] AdicCompletion (I.map (algebraMap A C)) C) := by
  obtain ⟨P⟩ := nonempty_completedPolynomialPresentation hI.fg B
  have he : (PerturbedPresentation.quotientObj A I P.variableCount P.ideal).carrier ≃ₐ[A]
      B.carrier := P.quotientEquiv
  obtain ⟨C, _, _, hCft, ⟨E⟩⟩ :=
    exists_finiteType_algEquiv_of_isRigEtale_principal_sameUniverse hI
      (PerturbedPresentation.quotientObj A I P.variableCount P.ideal)
      (isRigEtale_of_algEquiv he hB)
  exact ⟨C, inferInstance, inferInstance, hCft, ⟨he.symm.trans E⟩⟩

end Main

end Rig

end
