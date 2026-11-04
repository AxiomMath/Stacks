module

public import StacksFrontier.Homology.TwoTermComplex.Ext
public import StacksFrontier.RingTheory.Rig.Lifting
public import StacksFrontier.RingTheory.Rig.RigSmooth
public import StacksFrontier.RingTheory.Restricted.RigEtale

/-!
# From rig-étaleness to the obstruction calculus

Let `A` be a Noetherian ring, `I` an ideal of `A`, and `B` an `I`-adically complete `A`-algebra
of finite type modulo `I`.  Rig-étaleness of `B` over `(A, I)` (Stacks 0GAY) says that some
power of `I` annihilates the *identity* of the completed naive cotangent complex
`NL^∧_{B/A}` in `D(B)`; rig-smoothness (Stacks 0GAI) says that some power of `I` annihilates
the first `Ext` groups out of it.  The lifting calculus of Stacks 0GAP and 0AK6 is phrased in
the second, weaker form, while the structure theory of Chapter 88 — Stacks 0ALS, 0AKA, 0GB2 —
carries the first.  This file supplies the step between the two.

The step itself is formal: a scalar annihilating `𝟙 K` annihilates every morphism out of `K`,
because any such morphism factors through `𝟙 K`.  Specialised to
`ξ : Ext¹(NL^∧_{B/A}, N) = (NL^∧_{B/A} ⟶ N[0]⟦1⟧)` it turns the hypothesis of Stacks 0GAY into
the hypothesis of Stacks 0GAP, hence into the conormal Cramer relation

`β · g - ∑ i, (∂g/∂xᵢ) · γᵢ ∈ J²`  for every `g ∈ J`,

which is condition (7)(b) of Stacks 0AJU, and into the lifting statement of Stacks 0AK6.

## Main results

* `Rig.smul_eq_zero_of_smul_id_eq_zero`: a scalar annihilating the identity of an object of an
  `R`-linear category annihilates every morphism out of it, and
  `Rig.ext_eq_zero_of_smul_id_eq_zero` its specialisation to the first `Ext` groups of the
  completed naive cotangent complex.
* `Rig.exists_conormal_cramer_relation_of_smul_id_eq_zero`: the conormal Cramer relation of
  **Stacks 0GAP** from annihilation of the identity of the complex, which is the form Stacks
  0GAY and 0AJU(2) provide.  `Rig.conormal_cramer_relation_of_representatives` is the same
  relation for a prescribed family of representatives.
* `Rig.exists_linearMap_twoSided_of_smul_id_eq_zero`: the *two-sided* retraction of the
  differential supplied by **Stacks 0ALN(1)**, the stronger conclusion that annihilation of the
  identity gives over mere `Ext` annihilation.
* `Rig.isArtinJacobian_of_isRigEtale`: **Stacks 0AJU, (1) implies (6)** — the elementwise
  Jacobian criterion, which is the form the structure theory of Stacks 0ALS consumes.
* `Rig.exists_algHom_lift_of_isRigEtale`: **Stacks 0AK6** for a rig-étale algebra over a
  principal ideal, with the exponent produced from rig-étaleness rather than assumed.
* `Rig.exists_jacobianCriterion_of_isRigEtale_principal`: over a principal ideal `I = (a)` the
  Jacobian data of a rig-étale algebra, in the three-condition form `V(b) ⊆ V(IB)`,
  `Δ ∣ b`, `bJ ⊆ (f₁, …, f_r) + J²` with `b = a ^ c`.
* `Rig.exists_finiteType_algEquiv_adicCompletion_of_isRigEtale_principal`: **Stacks 0ALS**, the
  rig-étale case of Elkik's theorem, from that data together with the Jacobian criterion for
  algebraization.

## Implementation notes

The implication `Rig.IsRigEtale → Rig.IsRigSmooth` itself (**Stacks 0GB1**) is
`Rig.isRigSmooth_of_isRigEtale` in `StacksFrontier.RingTheory.Restricted.RigEtale`, and is not
restated here: this file supplies that step only in the pointwise form
`Rig.ext_eq_zero_of_smul_id_eq_zero`, for a single scalar and a single presentation, which is
the form the obstruction calculus below actually consumes. The two spellings of the implication
are interderivable by a bare application in either direction, so nothing is lost by stating it
once; what differs is only the order in which the Noetherian hypothesis and the ideal are bound,
and that is enough for the two to be distinct constants under the same name.

`Rig.nonempty_completedPolynomialPresentation` bundles the existential of Stacks 0AJP into a
`Nonempty (CompletedPolynomialPresentation I B)`, which is what `Rig.IsRigSmooth` needs: that
predicate asserts the existence of a presentation together with an exponent, whereas
`Rig.IsRigEtale` quantifies over all presentations and so carries no presentation of its own.
Over a Noetherian base the finite generation hypothesis of Stacks 0AJP is automatic.

In `Rig.exists_algHom_lift_of_isRigEtale` the exponent `c` is existentially quantified ahead of
the precision `n`, exactly as in the source: rig-étaleness fixes `c` once, and the lifting
statement is then available for every `n > 2c`.  Note that `a ^ c ∈ I ^ c` for `I = (a)`, so the
power of the single element `a` suffices and no further choice of generator is needed.

The Jacobian criterion for algebraization (**Stacks 0GAW**: a completed polynomial presentation
carrying an element `b` with `V(b) ⊆ V(IB)`, a Jacobian determinant dividing `b` and
`bJ ⊆ (f₁, …, f_m) + J²` comes from a finite type algebra) is not available here, so
`Rig.exists_finiteType_algEquiv_adicCompletion_of_isRigEtale_principal` carries it as the
hypothesis `jacobianAlgebraization`, in the square case `m = r` produced by rig-étaleness and
quantified over all objects of the category.

## References

* [Stacks Project, Tag 0GAY](https://stacks.math.columbia.edu/tag/0GAY)
* [Stacks Project, Tag 0GAI](https://stacks.math.columbia.edu/tag/0GAI)
* [Stacks Project, Tag 0GAP](https://stacks.math.columbia.edu/tag/0GAP)
* [Stacks Project, Tag 0AK6](https://stacks.math.columbia.edu/tag/0AK6)
* [Stacks Project, Tag 0AJU](https://stacks.math.columbia.edu/tag/0AJU)
* [Stacks Project, Tag 0ALN](https://stacks.math.columbia.edu/tag/0ALN)
* [Stacks Project, Tag 0GAW](https://stacks.math.columbia.edu/tag/0GAW)
* [Stacks Project, Tag 0ALS](https://stacks.math.columbia.edu/tag/0ALS)
* [Elkik, III Theorem 7]
-/

@[expose] public noncomputable section

open CategoryTheory

namespace Rig

universe u v w

attribute [local instance] HasDerivedCategory.standard

section Transfer

variable {C : Type*} [Category* C] [Preadditive C] {R : Type*} [Semiring R] [Linear R C]

/-- A scalar which annihilates the identity of an object annihilates every morphism out of that
object, since every such morphism factors through the identity. -/
public theorem smul_eq_zero_of_smul_id_eq_zero {X Y : C} (r : R) (h : r • 𝟙 X = 0)
    (f : X ⟶ Y) : r • f = 0 := by
  rw [← Category.id_comp f, ← Linear.smul_comp, h, Limits.zero_comp]

end Transfer

section Presentation

variable {A : Type u} [CommRing A] {I : Ideal A}

/-- **Stacks 0AJP**, as a `Nonempty` instead of an existential: an adically complete algebra of
finite type modulo a finitely generated ideal admits a completed polynomial presentation. -/
public theorem nonempty_completedPolynomialPresentation (hI : I.FG)
    (B : AdicFiniteTypeAlgebra.{u, v} A I) :
    Nonempty (CompletedPolynomialPresentation I B) := by
  obtain ⟨r, J, ⟨e⟩⟩ := exists_adicCompletion_mvPolynomial_quotient_equiv I hI B
  exact ⟨⟨r, J, e⟩⟩

end Presentation

section Bridge

variable {A : Type u} [CommRing A] {I : Ideal A}
  {B : AdicFiniteTypeAlgebra.{u, v} A I} {P : CompletedPolynomialPresentation I B}

/-- A scalar annihilating the identity of the completed naive cotangent complex in `D(B)`
annihilates every first `Ext` group out of it.  This is the implication
`Rig.IsRigEtale → Rig.IsRigSmooth` at the level of a single scalar and a single presentation. -/
public theorem ext_eq_zero_of_smul_id_eq_zero (K : CompletedNaiveCotangentComplex P)
    (b : B.carrier)
    (hb : b • 𝟙 ((DerivedCategory.Q (C := ModuleCat.{max u v} B.carrier)).obj
      K.cochainComplex) = 0)
    (N : ModuleCat.{max u v} B.carrier)
    (ξ : DerivedCategory.Ext (DerivedCategory.Q.obj K.cochainComplex)
      ((DerivedCategory.singleFunctor (ModuleCat.{max u v} B.carrier) 0).obj N) 1) :
    b • ξ = 0 :=
  smul_eq_zero_of_smul_id_eq_zero b hb ξ

/-- The conormal Cramer relation of **Stacks 0GAP**, from the hypothesis in the form
**Stacks 0GAY** and condition (2) of **Stacks 0AJU** supply it: if `b` annihilates the identity
of the completed naive cotangent complex in `D(B)` and `β` lifts `b` to `A⟨x₁, …, x_r⟩`, then
there are `γ₁, …, γ_r ∈ J` with

`β · g - ∑ i, (∂g/∂xᵢ) · γᵢ ∈ J²`  for every `g ∈ J`.

This is condition (7)(b) of Stacks 0AJU for the element `b`. -/
public theorem exists_conormal_cramer_relation_of_smul_id_eq_zero
    (K : CompletedNaiveCotangentComplex P) (b : B.carrier)
    (β : P.completedPolynomialRing) (hβ : P.toAlgHom β = b)
    (hb : b • 𝟙 ((DerivedCategory.Q (C := ModuleCat.{max u v} B.carrier)).obj
      K.cochainComplex) = 0) :
    ∃ γ : Fin P.variableCount → P.completedPolynomialRing,
      (∀ i, γ i ∈ P.ker) ∧
      ∀ g ∈ P.ker, β * g - ∑ i, K.partialDeriv i g * γ i ∈ P.ker ^ 2 :=
  exists_conormal_cramer_relation_of_ext_annihilated K b β hβ
    (ext_eq_zero_of_smul_id_eq_zero K b hb)

/-- The two-sided retraction of **Stacks 0ALN(1)** for the completed naive cotangent complex:
if `b` annihilates the identity of `NL^∧_{B/A}` in `D(B)`, then there is a `B`-linear
`H : ⨁ i, B dxᵢ → J / J²` with *both* composites `H ∘ d` and `d ∘ H` equal to multiplication
by `b`.

This is the sentence "by More on Algebra, Lemma 0ALN part (1) there exists a map
`α : ⨁ B dxᵢ → J/J²` such that `d ∘ α` and `α ∘ d` are both multiplication by `a^c`" in the
proof of Stacks 0AJU.  Only the first composite is available from annihilation of `Ext¹`
(`Rig.exists_linearMap_comp_differential_eq_smul`); the second needs the stronger hypothesis
used here, and is what makes condition (6)(a) of Stacks 0AJU — divisibility of the Jacobian
determinant — and the base-change argument of Stacks 0AK2 go through. -/
public theorem exists_linearMap_twoSided_of_smul_id_eq_zero
    (K : CompletedNaiveCotangentComplex P) (b : B.carrier)
    (hb : b • 𝟙 ((DerivedCategory.Q (C := ModuleCat.{max u v} B.carrier)).obj
      K.cochainComplex) = 0) :
    ∃ H : (Fin P.variableCount → B.carrier) →ₗ[B.carrier] P.extension.Cotangent,
      (∀ x, H (K.differential x) = b • x) ∧ (∀ y, K.differential (H y) = b • y) := by
  have hGE := K.isStrictlyGE
  have hLE := K.isStrictlyLE
  have hfree := K.free_X_zero
  have hposL : ∀ i : ℤ, 0 < i → Limits.IsZero (K.cochainComplex.X i) := fun i hi =>
    CochainComplex.isZero_of_isStrictlyLE K.cochainComplex 0 i hi
  have hlowL : ∀ i : ℤ, i ≤ -2 → Limits.IsZero (K.cochainComplex.X i) := fun i hi =>
    CochainComplex.isZero_of_isStrictlyGE K.cochainComplex (-1) i (by omega)
  have hprojmod : Module.Projective B.carrier (K.cochainComplex.X 0) := by
    have := hfree; infer_instance
  have hproj : Projective (K.cochainComplex.X 0) :=
    (IsProjective.iff_projective (R := B.carrier) (K.cochainComplex.X 0)).mp hprojmod
  -- `b • 𝟙` is null-homotopic, because it is zero in `D(B)` and `Hom_{K(B)} → Hom_{D(B)}` is
  -- injective out of a complex in degrees `≤ 0` with projective degree-zero term.
  have hQ : DerivedCategory.Q.map (b • 𝟙 K.cochainComplex) = 0 := by
    rw [Functor.Linear.map_smul, CategoryTheory.Functor.map_id]
    exact hb
  have hclass : (HomotopyCategory.quotient (ModuleCat.{max u v} B.carrier)
        (ComplexShape.up ℤ)).map (b • 𝟙 K.cochainComplex) =
      (HomotopyCategory.quotient (ModuleCat.{max u v} B.carrier) (ComplexShape.up ℤ)).map
        (0 : K.cochainComplex ⟶ K.cochainComplex) := by
    refine (TwoTermComplexExt.toHomD_bijective K.cochainComplex K.cochainComplex
      hposL hproj hlowL).injective ?_
    rw [TwoTermComplexExt.toHomD_quotient_map, TwoTermComplexExt.toHomD_quotient_map, hQ,
      CategoryTheory.Functor.map_zero]
  obtain htp := HomotopyCategory.homotopyOfEq _ _ hclass
  set h := htp.hom 0 (-1) with hhdef
  have hd2 : K.cochainComplex.d (-2) (-1) = 0 :=
    (hlowL (-2) (by norm_num)).eq_zero_of_src _
  have hd1 : K.cochainComplex.d 0 1 = 0 := (hposL 1 (by norm_num)).eq_zero_of_tgt _
  have c1 := htp.comm (-1)
  have c0 := htp.comm 0
  rw [dNext_eq htp.hom (show (ComplexShape.up ℤ).Rel (-1) 0 by simp),
    prevD_eq htp.hom (show (ComplexShape.up ℤ).Rel (-2) (-1) by simp), hd2] at c1
  rw [dNext_eq htp.hom (show (ComplexShape.up ℤ).Rel 0 1 by simp),
    prevD_eq htp.hom (show (ComplexShape.up ℤ).Rel (-1) 0 by simp), hd1] at c0
  have hh1 : K.cochainComplex.d (-1) 0 ≫ h = b • 𝟙 (K.cochainComplex.X (-1)) := by
    simpa [hhdef] using c1.symm
  have hh0 : h ≫ K.cochainComplex.d (-1) 0 = b • 𝟙 (K.cochainComplex.X 0) := by
    simpa [hhdef] using c0.symm
  -- Transport the two identities through the identifications of the two terms.
  set isoZero := K.degreeZeroIso with hisoZero
  set isoNegOne := K.degreeNegOneIso with hisoNegOne
  set D := ModuleCat.ofHom K.liftedDifferential with hD
  have hD' : D = isoNegOne.inv ≫ K.cochainComplex.d (-1) 0 ≫ isoZero.hom := by
    rw [K.cochainComplex_d]; simp [hD]
  set ht : ModuleCat.of B.carrier
        (CompletedNaiveCotangentComplex.LiftedDifferentials (P := P)) ⟶
      ModuleCat.of B.carrier (CompletedNaiveCotangentComplex.LiftedCotangent (P := P)) :=
    isoZero.inv ≫ h ≫ isoNegOne.hom with hht
  have key1 : D ≫ ht = b • 𝟙 _ := by
    simpa [hD', hht] using congrArg (fun f => isoNegOne.inv ≫ f ≫ isoNegOne.hom) hh1
  have key0 : ht ≫ D = b • 𝟙 _ := by
    simpa [hD', hht] using congrArg (fun f => isoZero.inv ≫ f ≫ isoZero.hom) hh0
  refine ⟨ULift.moduleEquiv.toLinearMap.comp
    ((ModuleCat.Hom.hom ht).comp ULift.moduleEquiv.symm.toLinearMap), ?_, ?_⟩
  · intro x
    have hx := congrArg (fun (f : _ ⟶ _) => (ModuleCat.Hom.hom f) (ULift.up x)) key1
    rw [hD] at hx
    simp only [ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply,
      ModuleCat.hom_ofHom, CompletedNaiveCotangentComplex.liftedDifferential_up,
      ModuleCat.hom_smul, ModuleCat.hom_id, LinearMap.smul_apply, LinearMap.id_apply] at hx
    simpa using congrArg ULift.down hx
  · intro y
    have hy := congrArg (fun (f : _ ⟶ _) => (ModuleCat.Hom.hom f) (ULift.up y)) key0
    rw [hD] at hy
    simp only [ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply,
      ModuleCat.hom_ofHom, ModuleCat.hom_smul, ModuleCat.hom_id, LinearMap.smul_apply,
      LinearMap.id_apply] at hy
    have hld : ∀ z : CompletedNaiveCotangentComplex.LiftedCotangent (P := P),
        (K.liftedDifferential z).down = K.differential z.down := fun _ => rfl
    simpa [hld] using congrArg ULift.down hy

/-- The conormal Cramer relation for a *prescribed* family of representatives.  If `H` retracts
the differential up to the scalar `b`, and `γᵢ ∈ J` represents `H(dxᵢ)`, then for every `g ∈ J`

`β · g - ∑ i, (∂g/∂xᵢ) · γᵢ ∈ J²`

where `β` lifts `b`.  Unlike `Rig.exists_conormal_cramer_relation` this does not choose the
representatives itself, so the same `γ` can also be used as the family of elements of `J`
appearing in the Jacobian criterion. -/
public theorem conormal_cramer_relation_of_representatives
    (K : CompletedNaiveCotangentComplex P) (b : B.carrier)
    (β : P.completedPolynomialRing) (hβ : P.toAlgHom β = b)
    (H : (Fin P.variableCount → B.carrier) →ₗ[B.carrier] P.extension.Cotangent)
    (hH : ∀ x, H (K.differential x) = b • x)
    (γ : Fin P.variableCount → P.completedPolynomialRing) (hγmem : ∀ i, γ i ∈ P.ker)
    (hγ : ∀ i, Algebra.Extension.Cotangent.mk (P := P.extension) ⟨γ i, hγmem i⟩ =
      H (Pi.single i 1))
    (g : P.completedPolynomialRing) (hg : g ∈ P.ker) :
    β * g - ∑ i, K.partialDeriv i g * γ i ∈ P.ker ^ 2 := by
  refine Algebra.Extension.sub_sum_mul_mem_ker_sq P.extension β
    (fun i => K.partialDeriv i g) (fun i => ⟨γ i, hγmem i⟩) ⟨g, hg⟩ ?_
  have h1 : b • Algebra.Extension.Cotangent.mk (P := P.extension) ⟨g, hg⟩
      = H (K.differential (Algebra.Extension.Cotangent.mk ⟨g, hg⟩)) := (hH _).symm
  rw [K.differential_mk ⟨g, hg⟩] at h1
  have h2 : (fun i => P.toAlgHom (K.partialDeriv i g))
      = ∑ i, P.toAlgHom (K.partialDeriv i g) •
        (Pi.single i 1 : Fin P.variableCount → B.carrier) := by
    funext j
    simp [Finset.sum_apply, Pi.single_apply]
  rw [h2, map_sum] at h1
  simp only [map_smul, ← hγ] at h1
  rw [← hβ] at h1
  exact h1

end Bridge

section Artin

variable {A : Type u} [CommRing A] [IsNoetherianRing A] {I : Ideal A}

/-- **Stacks 0AJU, (1) implies (6).**  A rig-étale adic algebra satisfies the elementwise
Jacobian criterion: for every `a ∈ I` there are an exponent `c` and elements
`f₁, …, f_r` of the kernel `J` of a completed polynomial presentation such that the Jacobian
determinant `det(∂fⱼ/∂xᵢ)` divides `a ^ c` in `B` and `a ^ c · J ⊆ (f₁, …, f_r) + J²`.

The proof is the one in the source.  Rig-étaleness gives an exponent `c₀` with
`a ^ c₀ · 𝟙 NL^∧_{B/A} = 0` in `D(B)`, hence by Stacks 0ALN(1) a two-sided retraction
`H : ⨁ i, B dxᵢ → J / J²` of the differential up to `a ^ c₀`
(`Rig.exists_linearMap_twoSided_of_smul_id_eq_zero`).  Taking `fᵢ ∈ J` representing `H(dxᵢ)`,
the identity `d ∘ H = a ^ c₀` says that the Jacobian matrix `(∂fⱼ/∂xᵢ)` is exactly
`a ^ c₀` times the identity, so its determinant is `a ^ (c₀ r)`; and `H ∘ d = a ^ c₀` is the
conormal Cramer relation.  The exponent is taken to be `c₀ (r + 1)`, which dominates both
`c₀ r` and `c₀`, the latter being needed when `r = 0`. -/
@[stacks 0AJU "(1) implies (6)"]
public theorem isArtinJacobian_of_isRigEtale (B : AdicFiniteTypeAlgebra.{u, v} A I)
    (P : CompletedPolynomialPresentation I B) (hB : IsRigEtale B) :
    ∀ a : A, a ∈ I →
      ∃ (c : ℕ) (f : Fin P.variableCount → P.ker),
        Matrix.det (fun i j : Fin P.variableCount =>
          P.toAlgHom ((completedNaiveCotangentComplex B P).partialDeriv i
            (f j : P.completedPolynomialRing))) ∣ (algebraMap A B.carrier a) ^ c ∧
        ∀ g : P.ker,
          algebraMap A P.completedPolynomialRing (a ^ c) * (g : P.completedPolynomialRing) ∈
            Ideal.span (Set.range fun i => (f i : P.completedPolynomialRing)) + P.ker ^ 2 := by
  classical
  obtain ⟨c₀, hc₀⟩ := hB P
  intro a ha
  set K := completedNaiveCotangentComplex B P with hKdef
  set b : B.carrier := (algebraMap A B.carrier a) ^ c₀ with hbdef
  have hbzero : b • 𝟙 ((DerivedCategory.Q (C := ModuleCat.{max u v} B.carrier)).obj
      K.cochainComplex) = 0 := by
    rw [hbdef, ← map_pow]
    exact hc₀ (a ^ c₀) (Ideal.pow_mem_pow ha c₀)
  obtain ⟨H, hHd, hdH⟩ := exists_linearMap_twoSided_of_smul_id_eq_zero K b hbzero
  obtain ⟨γ, hγmem, hγ⟩ : ∃ (γ : Fin P.variableCount → P.completedPolynomialRing)
      (hm : ∀ i, γ i ∈ P.ker),
      ∀ i, Algebra.Extension.Cotangent.mk (P := P.extension) ⟨γ i, hm i⟩ =
        H (Pi.single i 1) := by
    choose g hg using fun i : Fin P.variableCount =>
      Algebra.Extension.Cotangent.mk_surjective (P := P.extension) (H (Pi.single i 1))
    exact ⟨fun i => (g i).val, fun i => (g i).2, fun i => hg i⟩
  -- `d ∘ H = b` says the Jacobian matrix of the `γᵢ` is `b` times the identity matrix.
  have hmatrix : (fun i j : Fin P.variableCount =>
      P.toAlgHom (K.partialDeriv i (γ j))) =
      b • (1 : Matrix (Fin P.variableCount) (Fin P.variableCount) B.carrier) := by
    ext i j
    have h1 : K.differential (Algebra.Extension.Cotangent.mk
        (P := P.extension) ⟨γ j, hγmem j⟩) = b • Pi.single j 1 := by
      rw [hγ j]; exact hdH _
    rw [K.differential_mk ⟨γ j, hγmem j⟩] at h1
    simpa [Matrix.one_apply, Pi.single_apply, eq_comm] using congrFun h1 i
  refine ⟨c₀ * (P.variableCount + 1), fun i => ⟨γ i, hγmem i⟩, ?_, ?_⟩
  · rw [show (fun i j : Fin P.variableCount =>
      P.toAlgHom (K.partialDeriv i (γ j))) =
      b • (1 : Matrix (Fin P.variableCount) (Fin P.variableCount) B.carrier) from hmatrix,
      Matrix.det_smul, Matrix.det_one, mul_one, hbdef, ← pow_mul]
    simpa using pow_dvd_pow (algebraMap A B.carrier a)
      (Nat.mul_le_mul_left c₀ (Nat.le_succ P.variableCount))
  · intro g
    have hrel := conormal_cramer_relation_of_representatives K b
      (algebraMap A P.completedPolynomialRing (a ^ c₀)) (by rw [AlgHom.commutes, map_pow])
      H hHd γ hγmem hγ (g : P.completedPolynomialRing) g.2
    have hsum : ∑ i, K.partialDeriv i (g : P.completedPolynomialRing) * γ i ∈
        Ideal.span (Set.range γ) :=
      Ideal.sum_mem _ fun i _ =>
        Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i, rfl⟩)
    have hβg : algebraMap A P.completedPolynomialRing (a ^ c₀) *
        (g : P.completedPolynomialRing) ∈ Ideal.span (Set.range γ) + P.ker ^ 2 := by
      have hsplit : algebraMap A P.completedPolynomialRing (a ^ c₀) *
          (g : P.completedPolynomialRing) =
          (∑ i, K.partialDeriv i (g : P.completedPolynomialRing) * γ i) +
          (algebraMap A P.completedPolynomialRing (a ^ c₀) * (g : P.completedPolynomialRing) -
            ∑ i, K.partialDeriv i (g : P.completedPolynomialRing) * γ i) := by
        ring
      rw [hsplit, Submodule.add_eq_sup]
      exact Submodule.add_mem_sup hsum hrel
    have hpow : algebraMap A P.completedPolynomialRing (a ^ (c₀ * (P.variableCount + 1))) =
        algebraMap A P.completedPolynomialRing (a ^ (c₀ * P.variableCount)) *
          algebraMap A P.completedPolynomialRing (a ^ c₀) := by
      rw [← map_mul, ← pow_add, Nat.mul_succ]
    rw [hpow, mul_assoc]
    exact Ideal.mul_mem_left _ _ hβg

end Artin

section Lifting

variable {A : Type u} [CommRing A] [IsNoetherianRing A]

/-- **Stacks 0AK6** for a rig-étale algebra.  Let `I = (a)` be a principal ideal of a Noetherian
ring `A` and let `B` be rig-étale over `(A, I)`.  Then there is an exponent `c` such that for
every `I`-adically complete `A`-algebra `C` on which `a` is a nonzerodivisor and every `n > 2c`,
each `A`-algebra map `B → C / aⁿC` agrees modulo `a ^ (n - c)` with the reduction of an
`A`-algebra map `B → C`.

Compared with `Rig.exists_algHom_lift_of_isRegular` the annihilation hypothesis is replaced by
rig-étaleness, which is the form in which Stacks 0ALS and 0AKA have it. -/
public theorem exists_algHom_lift_of_isRigEtale
    (a : A) (I : Ideal A) (hI : I = Ideal.span {a})
    (B : AdicFiniteTypeAlgebra.{u, v} A I)
    (P : CompletedPolynomialPresentation I B)
    (hB : IsRigEtale B) :
    ∃ c : ℕ, ∀ {C : Type w} [CommRing C] [Algebra A C]
      [IsAdicComplete (I.map (algebraMap A C)) C],
      IsRegular (algebraMap A C a) →
      ∀ (n : ℕ), 2 * c < n →
      ∀ ψn : B.carrier →ₐ[A] C ⧸ (I.map (algebraMap A C)) ^ n,
        ∃ φ : B.carrier →ₐ[A] C,
          (Ideal.Quotient.factorₐ A
            (Ideal.pow_le_pow_right (Nat.sub_le n c))).comp ψn =
          (Ideal.Quotient.mkₐ A ((I.map (algebraMap A C)) ^ (n - c))).comp φ := by
  obtain ⟨c, hc⟩ := hB P
  have hmem : a ^ c ∈ I ^ c :=
    Ideal.pow_mem_pow (hI ▸ Ideal.mem_span_singleton_self a) c
  have hExt : ∀ (N : ModuleCat.{max u v} B.carrier)
      (ξ : DerivedCategory.Ext
        (DerivedCategory.Q.obj (completedNaiveCotangentComplex B P).cochainComplex)
        ((DerivedCategory.singleFunctor (ModuleCat.{max u v} B.carrier) 0).obj N) 1),
      (algebraMap A B.carrier a) ^ c • ξ = 0 := by
    intro N ξ
    rw [← map_pow]
    exact ext_eq_zero_of_smul_id_eq_zero (completedNaiveCotangentComplex B P) _
      (hc (a ^ c) hmem) N ξ
  exact ⟨c, fun {_C} _ _ _ ha n hn ψn ↦
    exists_algHom_lift_of_isRegular a I hI B P c hExt ha n hn ψn⟩

end Lifting

section Algebraization

variable {A : Type u} [CommRing A] [IsNoetherianRing A] {I : Ideal A}

/-- Over a principal ideal `I = (a)` the elementwise Jacobian criterion of a rig-étale algebra
takes the three-condition form of the Jacobian criterion for algebraization: for `b = a ^ c`
with `c` large the vanishing locus of `b` lies in `V(IB)`, the Jacobian determinant of
`f₁, …, f_r ∈ J` divides the image of `b`, and `bJ ⊆ (f₁, …, f_r) + J²`. -/
public theorem exists_jacobianCriterion_of_isRigEtale_principal (hI : I.IsPrincipal)
    (B : AdicFiniteTypeAlgebra.{u, v} A I) (P : CompletedPolynomialPresentation I B)
    (hB : IsRigEtale B) :
    ∃ (b : P.completedPolynomialRing) (f : Fin P.variableCount → P.ker),
      B.adicIdeal ≤ (Ideal.span {P.toAlgHom b}).radical ∧
      (Matrix.det fun i j : Fin P.variableCount =>
        P.toAlgHom ((completedNaiveCotangentComplex B P).partialDeriv i
          (f j : P.completedPolynomialRing))) ∣ P.toAlgHom b ∧
      ∀ g : P.ker,
        b * (g : P.completedPolynomialRing) ∈
          Ideal.span (Set.range fun i => (f i : P.completedPolynomialRing)) + P.ker ^ 2 := by
  obtain ⟨a, ha⟩ := hI.principal
  have haI : a ∈ I := by
    rw [show I = Ideal.span {a} from ha]
    exact Ideal.mem_span_singleton_self a
  obtain ⟨c, f, hdet, hrelations⟩ := isArtinJacobian_of_isRigEtale B P hB a haI
  have hb : P.toAlgHom (algebraMap A P.completedPolynomialRing (a ^ c)) =
      algebraMap A B.carrier a ^ c := by
    rw [AlgHom.commutes, map_pow]
  refine ⟨algebraMap A P.completedPolynomialRing (a ^ c), f, ?_, ?_, hrelations⟩
  · have hmap : B.adicIdeal = Ideal.span {algebraMap A B.carrier a} := by
      rw [show B.adicIdeal = (Ideal.span {a}).map (algebraMap A B.carrier) from
        congrArg (fun J : Ideal A => J.map (algebraMap A B.carrier)) ha, Ideal.map_span,
        Set.image_singleton]
    rw [hmap, hb]
    refine Ideal.span_le.mpr (Set.singleton_subset_iff.mpr ?_)
    exact Ideal.mem_radical_iff.mpr ⟨c, Ideal.mem_span_singleton_self _⟩
  · rw [hb]
    exact hdet

/-- **Stacks 0ALS**, the rig-étale case of [Elkik, III Theorem 7].  Let `A` be a Noetherian ring
and `I = (a)` a principal ideal.  A rig-étale object `B` of the category of `I`-adically
complete `A`-algebras of finite type modulo `I` is the `I`-adic completion of a finite type
`A`-algebra.

The hypothesis `jacobianAlgebraization` is **Stacks 0GAW** in the square case, quantified over
all objects of the category: a presentation carrying an element `b` whose vanishing locus lies
in `V(IB)`, whose Jacobian determinant divides it and with `bJ ⊆ (f₁, …, f_r) + J²`, comes from
a finite type algebra.

No `stacks` attribute is placed here. Instantiating `jacobianAlgebraization` at `B` itself
yields this statement directly, so the hypothesis is not an auxiliary input but the substance of
the result; the tag is earned only once Stacks 0GAW is proved. The unconditional content is
`exists_jacobianCriterion_of_isRigEtale_principal` above, which verifies 0GAW's hypotheses. -/
public theorem exists_finiteType_algEquiv_adicCompletion_of_isRigEtale_principal
    (hI : I.IsPrincipal) (B : AdicFiniteTypeAlgebra.{u, v} A I) (hB : IsRigEtale B)
    (jacobianAlgebraization : ∀ (B' : AdicFiniteTypeAlgebra.{u, v} A I)
      (P : CompletedPolynomialPresentation I B') (b : P.completedPolynomialRing)
      (f : Fin P.variableCount → P.ker),
      B'.adicIdeal ≤ (Ideal.span {P.toAlgHom b}).radical →
      (Matrix.det fun i j : Fin P.variableCount =>
        P.toAlgHom ((completedNaiveCotangentComplex B' P).partialDeriv i
          (f j : P.completedPolynomialRing))) ∣ P.toAlgHom b →
      (∀ g : P.ker,
        b * (g : P.completedPolynomialRing) ∈
          Ideal.span (Set.range fun i => (f i : P.completedPolynomialRing)) + P.ker ^ 2) →
      ∃ (C : Type u) (_ : CommRing C) (_ : Algebra A C),
        Algebra.FiniteType A C ∧
          Nonempty (B'.carrier ≃ₐ[A] AdicCompletion (I.map (algebraMap A C)) C)) :
    ∃ (C : Type u) (_ : CommRing C) (_ : Algebra A C),
      Algebra.FiniteType A C ∧
        Nonempty (B.carrier ≃ₐ[A] AdicCompletion (I.map (algebraMap A C)) C) := by
  obtain ⟨P⟩ := nonempty_completedPolynomialPresentation hI.fg B
  obtain ⟨b, f, hvanish, hjacobian, hrelations⟩ :=
    exists_jacobianCriterion_of_isRigEtale_principal hI B P hB
  exact jacobianAlgebraization B P b f hvanish hjacobian hrelations

end Algebraization

end Rig

end
