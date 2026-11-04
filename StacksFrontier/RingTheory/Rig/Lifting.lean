module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.Rig.Deformation
public import StacksFrontier.RingTheory.Rig.Obstruction

/-!
# Lifting a map into a quotient of a complete algebra (Stacks 0GAP, 0AK6)

Let `A` be a Noetherian ring, `I = (a)` a principal ideal of `A`, `B` an object of the category
of `I`-adically complete `A`-algebras of finite type modulo `I`, and `C` an `I`-adically complete
`A`-algebra on which `a` is a nonzerodivisor. Assume `a ^ c` annihilates
`Ext¹_B(NL^∧_{B/A}, N)` for every `B`-module `N`. Stacks 0AK6 says that for `n > 2c` every
`A`-algebra map `ψₙ : B → C / aⁿC` is, modulo `a ^ (n - c)`, the reduction of an `A`-algebra map
`B → C`.

The proof is the one in the source. Write `B = A⟨x₁, …, x_r⟩ / J` for a completed polynomial
presentation and lift `ψₙ` to a continuous `A`-algebra map `ψ : A⟨x₁, …, x_r⟩ → C`; then
`ψ(J) ⊆ aⁿC`. The obstruction class of `ψ` is killed by `a ^ c`, which by Stacks 0GAP means
(see `Rig.exists_conormal_cramer_relation_of_ext_annihilated`) that there are `γ₁, …, γ_r ∈ J`
with `a ^ c · g ≡ ∑ i (∂g/∂xᵢ) γᵢ` modulo `J²` for every `g ∈ J`. Applying `ψ` and dividing by
the nonzerodivisor `a ^ c` — this is where the regularity of `a` on `C` enters, and it is what
replaces the source's isomorphism `aⁿC/a²ⁿC ≅ a^{n-c}C/a^{2n-c}C` — gives

`ψ(g) - ∑ i ψ(∂g/∂xᵢ) δᵢ ∈ a^{2n-c} C`,  `δᵢ ∈ a^{n-c}C`,  `a ^ c δᵢ = ψ(γᵢ)`.

The perturbation `ψ' : xᵢ ↦ ψ(xᵢ) - δᵢ` therefore has `ψ'(J) ⊆ a^{2(n-c)}C` by the first-order
expansion of Stacks 0AK3, while `ψ' - ψ` takes values in `a^{n-c}C`. Iterating and passing to
the limit in the complete ring `C` produces `φ : A⟨x₁, …, x_r⟩ → C` with `φ(J) = 0`, i.e. a map
`B → C`, agreeing with `ψ` modulo `a^{n-c}`.

## Main results

* `Rig.exists_perturbed_continuousAlgHom`: **Stacks 0GAP**, the lifting claim — one step of the
  iteration, raising the precision from `n` to `2(n - c)`.
* `Rig.exists_limit_algHom`: the iteration and the passage to the limit, as a statement about an
  abstract precision-raising step.
* `Rig.exists_algHom_lift_of_isRegular`: **Stacks 0AK6**.

Auxiliary, and reusable:

* `Rig.existsUnique_continuousAlgHom_eval`: Stacks 0AJM in evaluation form — a polynomial
  algebra map into a complete linearly topologised algebra extends uniquely and continuously to
  restricted power series.
* `Rig.exists_continuousAlgHom_lift_quotient`: lifting an `A`-algebra map `B → C / IⁿC` to a
  continuous `A`-algebra map `A⟨x₁, …, x_r⟩ → C`.
* `Rig.CompletedPolynomialPresentation.restrictedToAlgHom` and `.restrictedKer`: the presenting
  surjection and its kernel, read on restricted power series rather than on the adic completion
  of the polynomial ring.
* `Rig.exists_restricted_cramer_relation`: the obstruction relation of Stacks 0GAP transported
  to restricted power series, where Stacks 0AK3 lives.

## Implementation notes

Two inverse-limit descriptions of `A⟨x₁, …, x_r⟩` are in play: the adic completion of the
polynomial ring, which carries the completed naive cotangent complex, and the ring of restricted
power series, which carries the first-order expansion of Stacks 0AK3. They are identified by
`RestrictedPowerSeries.adicCompletionAlgEquiv`, and everything in this file is stated on the
restricted-power-series side, the obstruction relation being transported across that
identification once and for all in `Rig.exists_restricted_cramer_relation`.

The topologies are given explicitly rather than as instances, as in
`StacksFrontier/RingTheory/Rig/Deformation.lean`: the source carries
`RestrictedPowerSeries.limitTopology` and the target the `I C`-adic topology. Continuity into a
discrete target is obtained from local constancy, which is all that is ever needed here; the two
criteria `Rig.continuous_of_adicTopology_locallyConstant` and
`Rig.continuous_of_coefficientProjection_locallyConstant` record this for the two sources.

That `ψₙ` kills a neighbourhood of zero is the one place where the completed polynomial algebra
is used as an adic completion: a restricted power series all of whose coefficients lie in `Iⁿ`
lies in `Kⁿ · A⟨x⟩` by `AdicCompletion.pow_smul_top_eq_ker_eval`, hence maps into
`(I B)ⁿ`, which `ψₙ` annihilates.

The passage to the limit is isolated as `Rig.exists_limit_algHom`, which quantifies over an
abstract precision-raising step and a predicate `Good` standing for continuity. Only the limit
map's algebra-homomorphism property and its vanishing on the kernel are produced; the limit is
not claimed continuous, as nothing downstream needs that.

## References

* [Stacks Project, Tag 0AK6](https://stacks.math.columbia.edu/tag/0AK6)
* [Stacks Project, Tag 0GAP](https://stacks.math.columbia.edu/tag/0GAP)
* [Stacks Project, Tag 0AK3](https://stacks.math.columbia.edu/tag/0AK3)
-/

@[expose] public noncomputable section

open CategoryTheory RestrictedPowerSeries

namespace Rig

universe u v w

section Continuity

variable {A : Type u} [CommRing A]

/-- A locally constant function on a ring with its adic topology is continuous: here local
constancy is witnessed by invariance under translation by a fixed power of the ideal. -/
public theorem continuous_of_adicTopology_locallyConstant {C : Type w} [CommRing C]
    (J : Ideal C) (n : ℕ) {Y : Type*} [TopologicalSpace Y] (f : C → Y)
    (hf : ∀ x z : C, z ∈ J ^ n → f (x + z) = f x) :
    @Continuous C Y J.adicTopology _ f := by
  let _ : TopologicalSpace C := J.adicTopology
  rw [continuous_def]
  intro s _
  rw [isOpen_iff_mem_nhds]
  intro x hx
  rw [(J.hasBasis_nhds_adic x).mem_iff]
  refine ⟨n, trivial, ?_⟩
  rintro y ⟨z, hz, rfl⟩
  simp only [Set.mem_preimage] at hx ⊢
  rwa [hf x z hz]

/-- A function on restricted power series which only depends on the coefficients modulo `Iⁿ` is
continuous for the inverse-limit topology. -/
public theorem continuous_of_coefficientProjection_locallyConstant
    (I : Ideal A) (σ : Type v) (n : ℕ) {Y : Type*} [TopologicalSpace Y]
    (F : RestrictedPowerSeries I σ → Y)
    (hF : ∀ g h, coefficientProjection I σ n h = 0 → F (g + h) = F g) :
    Continuous F := by
  let _ : TopologicalSpace (MvPolynomial σ (A ⧸ I ^ n)) := ⊥
  let _ : DiscreteTopology (MvPolynomial σ (A ⧸ I ^ n)) := ⟨rfl⟩
  let U : Set (RestrictedPowerSeries I σ) := (coefficientProjection I σ n) ⁻¹' {0}
  have hUopen : IsOpen U :=
    (continuous_coefficientProjection I σ n).isOpen_preimage _ (isOpen_discrete _)
  have hU0 : (0 : RestrictedPowerSeries I σ) ∈ U := by
    simp only [U, Set.mem_preimage, Set.mem_singleton_iff]
    exact map_zero _
  rw [continuous_def]
  intro s _
  rw [isOpen_iff_mem_nhds]
  intro x hx
  have hsub : (fun y => x + y) '' U ⊆ F ⁻¹' s := by
    rintro y ⟨z, hz, rfl⟩
    simp only [Set.mem_preimage] at hx ⊢
    rwa [hF x z hz]
  exact Filter.mem_of_superset
    (IsOpen.mem_nhds ((Homeomorph.addLeft x).isOpen_image.mpr hUopen) ⟨0, hU0, by simp⟩) hsub

/-- A power of an ideal is closed for the adic topology, being an open additive subgroup. -/
public theorem isClosed_pow_adicTopology {C : Type w} [CommRing C] (J : Ideal C) (n : ℕ) :
    @IsClosed C J.adicTopology ((J ^ n : Ideal C) : Set C) := by
  let _ : TopologicalSpace C := J.adicTopology
  rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
  intro x hx
  rw [(J.hasBasis_nhds_adic x).mem_iff]
  refine ⟨n, trivial, ?_⟩
  rintro y ⟨z, hz, rfl⟩
  intro hmem
  exact hx (by simpa using (J ^ n).sub_mem hmem hz)

end Continuity

section UniversalProperty

variable {A : Type u} [CommRing A]

/-- **Stacks 0AJM**, in evaluation form. An `A`-algebra map out of a polynomial algebra into an
`I`-adically complete `A`-algebra extends uniquely to a continuous `A`-algebra map out of the
restricted power series. This is
`RestrictedPowerSeries.existsUnique_continuousAlgHom_extends` (Stacks 0AJM) specialised to the
`I`-adic filtration, with the completeness and linear-topology side conditions discharged. -/
@[ega "0 7.5.3" "special case"]
public theorem existsUnique_continuousAlgHom_eval (I : Ideal A)
    {C : Type w} [CommRing C] [Algebra A C] [IsAdicComplete (I.map (algebraMap A C)) C]
    {σ : Type v} (f : MvPolynomial σ A →ₐ[A] C) :
    ∃! ψ : RestrictedPowerSeries I σ →ₐ[A] C,
      @Continuous _ _ (limitTopology I σ) ((I.map (algebraMap A C)).adicTopology) ψ ∧
      ψ.comp (polynomialAlgHom I σ) = f := by
  classical
  let _ : TopologicalSpace A := I.adicTopology
  let _ : IsTopologicalRing A := inferInstance
  let J : Ideal C := I.map (algebraMap A C)
  let _ : TopologicalSpace C := J.adicTopology
  let _ : IsTopologicalRing C := inferInstance
  let _ : IsLinearTopology C C := J.isLinearTopology
  have hopen : ∀ n : ℕ, IsOpen ((I ^ n : Ideal A) : Set A) := by
    intro n
    rw [isOpen_iff_mem_nhds]
    intro b hb
    rw [(I.hasBasis_nhds_adic b).mem_iff]
    exact ⟨n, trivial, by
      rintro x ⟨y, hy, rfl⟩
      exact (I ^ n).add_mem hb hy⟩
  have hfund : ∀ U ∈ nhds (0 : A), ∃ n : ℕ, ((I ^ n : Ideal A) : Set A) ⊆ U :=
    fun _ hU => (I.hasBasis_nhds_zero_adic.mem_iff.mp hU).imp fun _ => And.right
  let _ : WithIdeal A := ⟨I⟩
  let _ : WithIdeal C := ⟨J⟩
  have hAC : Continuous (algebraMap A C) :=
    (WithIdeal.uniformContinuous_of_map_le (f := algebraMap A C) (le_of_eq rfl)).continuous
  have hC : TopologicalRing.IsComplete C := by
    rcases (IsAdic.isAdicComplete_iff (I := J) rfl).mp ‹IsAdicComplete J C› with
      ⟨hcomplete, hhausdorff⟩
    exact ⟨hhausdorff, hcomplete⟩
  exact RestrictedPowerSeries.existsUnique_continuousAlgHom_extends
    (J := fun n : ℕ ↦ I ^ n) (hJ := fun _ _ h ↦ Ideal.pow_le_pow_right h)
    hopen hfund hAC hC f

/-- A restricted power series all of whose coefficients lie in `Iⁿ` is carried into `Iⁿ` times
the target by any `A`-algebra map out of the completed polynomial algebra. This is the statement
that `Kⁿ A⟨x⟩` is the kernel of reduction to `A/Iⁿ[x]`, for `K` the coefficient ideal. -/
public theorem mem_map_pow_of_coefficientProjection_eq_zero
    (I : Ideal A) (hI : I.FG) {σ : Type v} {Bc : Type w} [CommRing Bc] [Algebra A Bc]
    (f : AdicCompletion (I.map (MvPolynomial.C : A →+* MvPolynomial σ A))
      (MvPolynomial σ A) →ₐ[A] Bc)
    (n : ℕ) (g : RestrictedPowerSeries I σ)
    (hg : coefficientProjection I σ n g = 0) :
    f (adicCompletionAlgEquiv I σ g) ∈ (I ^ n).map (algebraMap A Bc) := by
  classical
  have hev : AdicCompletion.evalₐ (I.map (MvPolynomial.C : A →+* MvPolynomial σ A)) n
      (adicCompletionAlgEquiv I σ g) = 0 := by
    rw [show (adicCompletionAlgEquiv I σ) g = (adicCompletionEquiv I σ) g from rfl,
      eval_adicCompletionEquiv I σ n g]
    exact show (polynomialQuotientEquiv I σ n).toRingHom (coefficientProjection I σ n g) = 0 by
      rw [hg, map_zero]
  have hmem : (adicCompletionAlgEquiv I σ g) ∈
      ((I.map (MvPolynomial.C : A →+* MvPolynomial σ A)) ^ n •
        (⊤ : Submodule (MvPolynomial σ A)
          (AdicCompletion (I.map (MvPolynomial.C : A →+* MvPolynomial σ A))
            (MvPolynomial σ A)))) := by
    rw [AdicCompletion.pow_smul_top_eq_ker_eval (M := MvPolynomial σ A) (n := n) (hI.map _)]
    have h2 := AdicCompletion.factor_evalₐ_eq_eval
      (I.map (MvPolynomial.C : A →+* MvPolynomial σ A)) (adicCompletionAlgEquiv I σ g)
      (show (I.map (MvPolynomial.C : A →+* MvPolynomial σ A)) ^ n ≤
        (I.map (MvPolynomial.C : A →+* MvPolynomial σ A)) ^ n • ⊤ by simp)
    rw [hev, map_zero] at h2
    simpa [LinearMap.mem_ker] using h2.symm
  refine Submodule.smul_induction_on hmem ?_ ?_
  · intro k hk y _
    have hcomp : (f.toRingHom.comp (algebraMap (MvPolynomial σ A) _)).comp
        (MvPolynomial.C : A →+* MvPolynomial σ A) = algebraMap A Bc := by
      ext b
      exact show f (algebraMap (MvPolynomial σ A) _ (MvPolynomial.C b)) = algebraMap A Bc b by
        rw [show (MvPolynomial.C b : MvPolynomial σ A)
            = algebraMap A (MvPolynomial σ A) b from rfl,
          ← IsScalarTower.algebraMap_apply A (MvPolynomial σ A) _, f.commutes]
    have hk' : k ∈ (I ^ n).map (MvPolynomial.C : A →+* MvPolynomial σ A) := by
      rwa [Ideal.map_pow]
    have hmap := Ideal.mem_map_of_mem
      (f.toRingHom.comp (algebraMap (MvPolynomial σ A) _)) hk'
    rw [Ideal.map_map, hcomp] at hmap
    rw [Algebra.smul_def, map_mul]
    exact Ideal.mul_mem_right _ _ hmap
  · intro y z hy hz
    rw [map_add]
    exact Ideal.add_mem _ hy hz

/-- An `A`-algebra map into `C / IⁿC` annihilates `Iⁿ` times its source. -/
public theorem eq_zero_of_mem_map_pow {Bc : Type v} [CommRing Bc] [Algebra A Bc]
    {I : Ideal A} {C : Type w} [CommRing C] [Algebra A C] (n : ℕ)
    (ψn : Bc →ₐ[A] C ⧸ (I.map (algebraMap A C)) ^ n)
    (x : Bc) (hx : x ∈ (I ^ n).map (algebraMap A Bc)) : ψn x = 0 := by
  have h1 := Ideal.mem_map_of_mem ψn.toRingHom hx
  rw [Ideal.map_map] at h1
  have h2 : ψn.toRingHom.comp (algebraMap A Bc)
      = algebraMap A (C ⧸ (I.map (algebraMap A C)) ^ n) := by
    ext b
    exact ψn.commutes b
  rw [h2] at h1
  have h3 : (I ^ n).map (algebraMap A (C ⧸ (I.map (algebraMap A C)) ^ n)) = ⊥ := by
    have h4 : (algebraMap A (C ⧸ (I.map (algebraMap A C)) ^ n))
        = (Ideal.Quotient.mk ((I.map (algebraMap A C)) ^ n)).comp (algebraMap A C) := rfl
    rw [h4, ← Ideal.map_map, Ideal.map_pow, Ideal.map_quotient_self]
  rw [h3] at h1
  simpa using h1

end UniversalProperty

section Presentation

variable {A : Type u} [CommRing A] {I : Ideal A} {B : AdicFiniteTypeAlgebra.{u, v} A I}

/-- The presenting surjection of a completed polynomial presentation, read on restricted power
series rather than on the adic completion of the polynomial ring. -/
public def CompletedPolynomialPresentation.restrictedToAlgHom
    (P : CompletedPolynomialPresentation I B) :
    RestrictedPowerSeries I (Fin P.variableCount) →ₐ[A] B.carrier :=
  P.toAlgHom.comp
    (RestrictedPowerSeries.adicCompletionAlgEquiv I (Fin P.variableCount)).toAlgHom

/-- The kernel `J` of a completed polynomial presentation, read on restricted power series. -/
public abbrev CompletedPolynomialPresentation.restrictedKer
    (P : CompletedPolynomialPresentation I B) :
    Ideal (RestrictedPowerSeries I (Fin P.variableCount)) :=
  RingHom.ker P.restrictedToAlgHom.toRingHom

/-- The presenting surjection on restricted power series is surjective. -/
public theorem CompletedPolynomialPresentation.restrictedToAlgHom_surjective
    (P : CompletedPolynomialPresentation I B) :
    Function.Surjective P.restrictedToAlgHom :=
  P.toAlgHom_surjective.comp
    (RestrictedPowerSeries.adicCompletionAlgEquiv I (Fin P.variableCount)).surjective

/-- A restricted power series lies in the kernel of the presentation exactly when its image in
the adic completion of the polynomial ring does. -/
public theorem CompletedPolynomialPresentation.mem_restrictedKer_iff
    (P : CompletedPolynomialPresentation I B)
    (g : RestrictedPowerSeries I (Fin P.variableCount)) :
    g ∈ P.restrictedKer ↔
      RestrictedPowerSeries.adicCompletionAlgEquiv I (Fin P.variableCount) g ∈ P.ker :=
  Iff.rfl

/-- The kernel of a completed polynomial presentation is the ideal it is presented by. -/
public theorem CompletedPolynomialPresentation.ker_eq_ideal
    (P : CompletedPolynomialPresentation I B) : P.ker = P.ideal := by
  ext x
  refine ⟨fun hx => ?_, fun hx => ?_⟩
  · have h : P.quotientEquiv (Ideal.Quotient.mk P.ideal x) = 0 := hx
    exact Ideal.Quotient.eq_zero_iff_mem.mp (P.quotientEquiv.injective (by simpa using h))
  · exact show P.quotientEquiv (Ideal.Quotient.mk P.ideal x) = 0 by
      rw [(Ideal.Quotient.eq_zero_iff_mem).mpr hx, map_zero]

/-- The formal partial derivatives of any completed naive cotangent complex of a presentation are
the canonical ones, by the uniqueness of continuous derivations extending `∂/∂xᵢ`. -/
public theorem CompletedNaiveCotangentComplex.partialDeriv_eq [IsNoetherianRing A]
    {P : CompletedPolynomialPresentation I B} (K : CompletedNaiveCotangentComplex P)
    (i : Fin P.variableCount) : K.partialDeriv i = completedPartialDeriv P i :=
  (K.partialDeriv_unique i _ (continuous_completedPartialDeriv P i)
    (completedPartialDeriv_polynomial P i)).symm

end Presentation

section QuotientLift

variable {A : Type u} [CommRing A] {I : Ideal A} {B : AdicFiniteTypeAlgebra.{u, v} A I}

/-- An `A`-algebra map `B → C / IⁿC` lifts to a continuous `A`-algebra map
`A⟨x₁, …, x_r⟩ → C`, for any completed polynomial presentation of `B`.

The lift is built by choosing lifts in `C` of the images of the variables and extending by the
universal property of restricted power series; it reduces to the given map because both
reductions are continuous and agree on the dense subalgebra of polynomials. -/
public theorem exists_continuousAlgHom_lift_quotient (hI : I.FG)
    (P : CompletedPolynomialPresentation I B)
    {C : Type w} [CommRing C] [Algebra A C]
    [IsAdicComplete (I.map (algebraMap A C)) C] (n : ℕ)
    (ψn : B.carrier →ₐ[A] C ⧸ (I.map (algebraMap A C)) ^ n) :
    ∃ ψ : RestrictedPowerSeries I (Fin P.variableCount) →ₐ[A] C,
      @Continuous _ _ (limitTopology I (Fin P.variableCount))
        ((I.map (algebraMap A C)).adicTopology) ψ ∧
      ∀ g, Ideal.Quotient.mk ((I.map (algebraMap A C)) ^ n) (ψ g)
        = ψn (P.restrictedToAlgHom g) := by
  classical
  have hlift : ∀ i : Fin P.variableCount, ∃ u : C,
      Ideal.Quotient.mk ((I.map (algebraMap A C)) ^ n) u
        = ψn (P.restrictedToAlgHom
            (polynomialAlgHom I (Fin P.variableCount) (MvPolynomial.X i))) :=
    fun i => Ideal.Quotient.mk_surjective _
  choose u hu using hlift
  obtain ⟨ψ, ⟨hψcont, hψpoly⟩, -⟩ := existsUnique_continuousAlgHom_eval I
    (MvPolynomial.aeval u : MvPolynomial (Fin P.variableCount) A →ₐ[A] C)
  refine ⟨ψ, hψcont, ?_⟩
  let _ : TopologicalSpace C := (I.map (algebraMap A C)).adicTopology
  let _ : TopologicalSpace (C ⧸ (I.map (algebraMap A C)) ^ n) := ⊥
  let _ : DiscreteTopology (C ⧸ (I.map (algebraMap A C)) ^ n) := ⟨rfl⟩
  have hc1 : @Continuous _ _ (limitTopology I (Fin P.variableCount)) _
      (fun g => Ideal.Quotient.mk ((I.map (algebraMap A C)) ^ n) (ψ g)) :=
    (continuous_of_adicTopology_locallyConstant (I.map (algebraMap A C)) n
      (Ideal.Quotient.mk ((I.map (algebraMap A C)) ^ n)) (by
        intro x z hz
        rw [map_add, (Ideal.Quotient.eq_zero_iff_mem).mpr hz, add_zero])).comp hψcont
  have hc2 : @Continuous _ _ (limitTopology I (Fin P.variableCount)) _
      (fun g => ψn (P.restrictedToAlgHom g)) := by
    refine continuous_of_coefficientProjection_locallyConstant I (Fin P.variableCount) n _ ?_
    intro g h hh
    rw [map_add, map_add,
      show ψn (P.restrictedToAlgHom h) = 0 from
        eq_zero_of_mem_map_pow n ψn _
          (mem_map_pow_of_coefficientProjection_eq_zero I hI P.toAlgHom n h hh), add_zero]
  refine fun g => congrFun
    ((denseRange_restrictedPolynomials (I := I) (Fin P.variableCount)).equalizer hc1 hc2 ?_) g
  funext p
  have hvar := MvPolynomial.algHom_ext
    (f := ((Ideal.Quotient.mkₐ A ((I.map (algebraMap A C)) ^ n)).comp ψ).comp
      (polynomialAlgHom I (Fin P.variableCount)))
    (g := (ψn.comp P.restrictedToAlgHom).comp (polynomialAlgHom I (Fin P.variableCount)))
    (fun i => show Ideal.Quotient.mk _
          (ψ (polynomialAlgHom I (Fin P.variableCount) (MvPolynomial.X i)))
        = ψn (P.restrictedToAlgHom
            (polynomialAlgHom I (Fin P.variableCount) (MvPolynomial.X i))) by
      rw [← hu i]
      congr 1
      simpa using AlgHom.congr_fun hψpoly (MvPolynomial.X i))
  exact AlgHom.congr_fun hvar p

end QuotientLift

section Perturbation

variable {A : Type u} [CommRing A]

/-- A ring hom sending an ideal `J` into `K` sends `Jⁿ` into `Kⁿ`. -/
private theorem apply_mem_pow_of_forall_mem {R S F : Type*} [CommRing R] [CommRing S]
    [FunLike F R S] [RingHomClass F R S] (f : F) (J : Ideal R) (K : Ideal S)
    (h : ∀ x ∈ J, f x ∈ K) (n : ℕ) {x : R} (hx : x ∈ J ^ n) : f x ∈ K ^ n := by
  have h1 := Ideal.mem_map_of_mem (f : R →+* S) hx
  rw [Ideal.map_pow] at h1
  exact pow_le_pow_left' (Ideal.map_le_iff_le_comap.mpr h) n h1

/-- **Stacks 0GAP**, the lifting claim, in the principal case.

Let `I = (a)`, let `C` be an `I`-adically complete `A`-algebra on which `a` is a nonzerodivisor,
and let `J` be an ideal of `A⟨x₁, …, x_r⟩` satisfying the obstruction relation
`a ^ c · g ≡ ∑ i (∂g/∂xᵢ) γᵢ` modulo `J²` for a fixed family `γ₁, …, γ_r ∈ J`. Then a continuous
`A`-algebra map `ψ : A⟨x₁, …, x_r⟩ → C` with `ψ(J) ⊆ aⁿC` can be perturbed to a continuous
`ψ'` with `ψ'(J) ⊆ a^{2(n-c)}C`, the perturbation taking values in `a^{n-c}C`.

The perturbation is `xᵢ ↦ ψ(xᵢ) - δᵢ` where `a ^ c δᵢ = ψ(γᵢ)`; the two conclusions are the
first-order expansion of Stacks 0AK3 applied to it. -/
@[stacks 0GAP "the lifting claim"]
public theorem exists_perturbed_continuousAlgHom (a : A) (I : Ideal A) (hI : I = Ideal.span {a})
    {C : Type w} [CommRing C] [Algebra A C] [IsAdicComplete (I.map (algebraMap A C)) C]
    (ha : IsRegular (algebraMap A C a))
    {r : ℕ} (Jid : Ideal (RestrictedPowerSeries I (Fin r))) (c n : ℕ) (hc : c ≤ n)
    (γ : Fin r → RestrictedPowerSeries I (Fin r)) (hγ : ∀ i, γ i ∈ Jid)
    (hcramer : ∀ g ∈ Jid, algebraMap A (RestrictedPowerSeries I (Fin r)) (a ^ c) * g
        - ∑ i, partialDerivative I i g * γ i ∈ Jid ^ 2)
    (ψ : RestrictedPowerSeries I (Fin r) →ₐ[A] C)
    (hψc : @Continuous _ _ (limitTopology I (Fin r))
      ((I.map (algebraMap A C)).adicTopology) ψ)
    (hψJ : ∀ g ∈ Jid, ψ g ∈ (I.map (algebraMap A C)) ^ n) :
    ∃ ψ' : RestrictedPowerSeries I (Fin r) →ₐ[A] C,
      (@Continuous _ _ (limitTopology I (Fin r))
        ((I.map (algebraMap A C)).adicTopology) ψ') ∧
      (∀ g ∈ Jid, ψ' g ∈ (I.map (algebraMap A C)) ^ (2 * (n - c))) ∧
      (∀ g, ψ' g - ψ g ∈ (I.map (algebraMap A C)) ^ (n - c)) := by
  classical
  have hIfg : I.FG := hI ▸ (Submodule.fg_span_singleton a)
  set α := algebraMap A C a with hα
  set JC : Ideal C := I.map (algebraMap A C) with hJC
  have hαpow : ∀ m : ℕ, algebraMap A C (a ^ m) = α ^ m := fun m => by rw [hα, map_pow]
  have hspan : JC = Ideal.span {α} := by rw [hJC, hI, Ideal.map_span]; simp [hα]
  have hpow : ∀ m : ℕ, JC ^ m = Ideal.span {α ^ m} := by
    intro m; rw [hspan, Ideal.span_singleton_pow]
  have hdiv : ∀ i, ∃ d : C, d ∈ JC ^ (n - c) ∧ α ^ c * d = ψ (γ i) := by
    intro i
    have h := hψJ (γ i) (hγ i)
    rw [hpow n, Ideal.mem_span_singleton'] at h
    obtain ⟨y, hy⟩ := h
    refine ⟨α ^ (n - c) * y, ?_, ?_⟩
    · rw [hpow (n - c), Ideal.mem_span_singleton']
      exact ⟨y, by ring⟩
    · rw [← hy, ← mul_assoc, ← pow_add, Nat.add_sub_cancel' hc]; ring
  choose δ hδmem hδ using hdiv
  obtain ⟨ψ', ⟨hψ'c, hψ'var⟩, -⟩ :=
    exists_continuousAlgHom_add_variables I hIfg ψ hψc (fun i => -δ i)
  have hexp : ∀ g : RestrictedPowerSeries I (Fin r),
      ψ' g - (ψ g - ∑ i, ψ (partialDerivative I i g) * δ i) ∈ JC ^ (2 * (n - c)) := by
    intro g
    obtain ⟨ξ, hξmem, hξ⟩ := eval_add_variables_eq_linear_add_error I hIfg ψ ψ' hψc hψ'c
      (fun i => -δ i) hψ'var g
    have hξJ : ξ ∈ JC ^ (2 * (n - c)) := by
      refine (Ideal.span_le.mpr ?_) hξmem
      rintro x ⟨ij, rfl⟩
      simp only [SetLike.mem_coe, neg_mul_neg]
      rw [two_mul, pow_add]
      exact Ideal.mul_mem_mul (hδmem ij.1) (hδmem ij.2)
    rw [show ψ' g - (ψ g - ∑ i, ψ (partialDerivative I i g) * δ i) = ξ by
      rw [hξ]
      simp only [mul_neg, Finset.sum_neg_distrib]
      ring]
    exact hξJ
  refine ⟨ψ', hψ'c, ?_, ?_⟩
  · intro g hg
    have hrel := apply_mem_pow_of_forall_mem ψ Jid (JC ^ n) hψJ 2 (hcramer g hg)
    rw [← pow_mul, mul_comm n 2] at hrel
    rw [map_sub, map_mul, map_sum] at hrel
    simp only [map_mul] at hrel
    simp only [← hδ] at hrel
    rw [show ψ (algebraMap A (RestrictedPowerSeries I (Fin r)) (a ^ c)) = α ^ c by
      rw [ψ.commutes, hαpow]] at hrel
    have heq : α ^ c * (ψ g - ∑ i, ψ (partialDerivative I i g) * δ i)
        = α ^ c * ψ g - ∑ i, ψ (partialDerivative I i g) * (α ^ c * δ i) := by
      rw [mul_sub, Finset.mul_sum]
      congr 1
      exact Finset.sum_congr rfl fun i _ => by ring
    have hrel2 : α ^ c * (ψ g - ∑ i, ψ (partialDerivative I i g) * δ i)
        ∈ JC ^ (2 * n) := by rw [heq]; exact hrel
    have hmain : ψ g - ∑ i, ψ (partialDerivative I i g) * δ i ∈ JC ^ (2 * n - c) := by
      rw [hpow (2 * n), Ideal.mem_span_singleton'] at hrel2
      obtain ⟨y, hy⟩ := hrel2
      rw [hpow (2 * n - c), Ideal.mem_span_singleton']
      refine ⟨y, (ha.pow c).left ?_⟩
      exact show α ^ c * (y * α ^ (2 * n - c)) = α ^ c * _ by
        rw [← hy, show α ^ c * (y * α ^ (2 * n - c)) = y * α ^ (c + (2 * n - c)) by ring,
          Nat.add_sub_cancel' (by omega : c ≤ 2 * n)]
    have hsum := Ideal.add_mem (JC ^ (2 * (n - c)))
      (Ideal.pow_le_pow_right (by omega : 2 * (n - c) ≤ 2 * n - c) hmain) (hexp g)
    simpa using hsum
  · intro g
    have h1 : (∑ i, ψ (partialDerivative I i g) * δ i) ∈ JC ^ (n - c) :=
      Ideal.sum_mem _ fun i _ => Ideal.mul_mem_left _ _ (hδmem i)
    have h2 := Ideal.sub_mem (JC ^ (n - c))
      (Ideal.pow_le_pow_right (by omega : n - c ≤ 2 * (n - c)) (hexp g)) h1
    rw [show ψ' g - ψ g
        = (ψ' g - (ψ g - ∑ i, ψ (partialDerivative I i g) * δ i))
          - (∑ i, ψ (partialDerivative I i g) * δ i) by ring]
    exact h2

end Perturbation

section Limit

/-- Iterating a precision-raising step and passing to the limit.

`Good` stands for whatever property the step preserves — continuity, in the application. The
step raises the precision from `m` to `2 (m - c)`, which is a strict increase as soon as
`2c < m`, and leaves the map unchanged modulo `I^{m-c}`. Since `C` is `I`-adically complete the
iterates converge pointwise, and the limit is an `A`-algebra map vanishing on `J` and agreeing
with the initial map modulo `I^{n-c}`. -/
public theorem exists_limit_algHom
    {A : Type u} [CommRing A] {Rs : Type v} [CommRing Rs] [Algebra A Rs]
    {C : Type w} [CommRing C] [Algebra A C] (JC : Ideal C) [IsAdicComplete JC C]
    (Jid : Ideal Rs) (Good : (Rs →ₐ[A] C) → Prop)
    (c n : ℕ) (hn : 2 * c < n)
    (step : ∀ (m : ℕ) (ψ : Rs →ₐ[A] C), 2 * c < m → Good ψ → (∀ g ∈ Jid, ψ g ∈ JC ^ m) →
      ∃ ψ' : Rs →ₐ[A] C, Good ψ' ∧ (∀ g ∈ Jid, ψ' g ∈ JC ^ (2 * (m - c))) ∧
        ∀ g, ψ' g - ψ g ∈ JC ^ (m - c))
    (ψ₀ : Rs →ₐ[A] C) (h0 : Good ψ₀) (h0J : ∀ g ∈ Jid, ψ₀ g ∈ JC ^ n) :
    ∃ φ : Rs →ₐ[A] C, (∀ g ∈ Jid, φ g = 0) ∧ ∀ g, φ g - ψ₀ g ∈ JC ^ (n - c) := by
  classical
  let _ : TopologicalSpace C := JC.adicTopology
  let _ : IsTopologicalRing C := inferInstance
  let _ : IsLinearTopology C C := JC.isLinearTopology
  let _ : WithIdeal C := ⟨JC⟩
  have hC : TopologicalRing.IsComplete C := by
    rcases (IsAdic.isAdicComplete_iff (I := JC) rfl).mp ‹IsAdicComplete JC C› with
      ⟨hcomplete, hhausdorff⟩
    exact ⟨hhausdorff, hcomplete⟩
  let _ : T2Space C := hC.1
  let _ : CompleteSpace C := hC.2
  let State := {p : ℕ × (Rs →ₐ[A] C) //
    2 * c < p.1 ∧ Good p.2 ∧ ∀ g ∈ Jid, p.2 g ∈ JC ^ p.1}
  have hstep : ∀ s : State, ∃ t : State,
      t.1.1 = 2 * (s.1.1 - c) ∧ ∀ g, t.1.2 g - s.1.2 g ∈ JC ^ (s.1.1 - c) := by
    intro s
    obtain ⟨ψ', hgood, hJ, hdiff⟩ := step s.1.1 s.1.2 s.2.1 s.2.2.1 s.2.2.2
    exact ⟨⟨(2 * (s.1.1 - c), ψ'), by have := s.2.1; omega, hgood, hJ⟩, rfl, hdiff⟩
  choose nextS hnextlev hnextdiff using hstep
  let s₀ : State := ⟨(n, ψ₀), hn, h0, h0J⟩
  let S : ℕ → State := fun k => Nat.rec s₀ (fun _ s => nextS s) k
  have hS0 : S 0 = s₀ := rfl
  have hSsucc : ∀ k, S (k + 1) = nextS (S k) := fun _ => rfl
  have hlev : ∀ k, 2 * c + k + 1 ≤ (S k).1.1 := by
    intro k
    induction k with
    | zero => simpa [hS0, s₀] using hn
    | succ k ih =>
      rw [hSsucc k, hnextlev (S k)]
      omega
  have hmonoLev' : Monotone (fun k => (S k).1.1) := by
    refine monotone_nat_of_le_succ fun k => ?_
    exact show (S k).1.1 ≤ (S (k + 1)).1.1 by
      rw [hSsucc k, hnextlev (S k)]
      have := hlev k
      omega
  have hmonoLev : ∀ k l : ℕ, k ≤ l → (S k).1.1 ≤ (S l).1.1 := fun k l h => hmonoLev' h
  have htel : ∀ k l, k ≤ l → ∀ g, (S l).1.2 g - (S k).1.2 g ∈ JC ^ ((S k).1.1 - c) := by
    intro k l hkl
    induction l with
    | zero =>
      intro g
      obtain rfl : k = 0 := Nat.eq_zero_of_le_zero hkl
      simp
    | succ l ih =>
      intro g
      rcases Nat.lt_or_ge k (l + 1) with h | h
      · have hkl' : k ≤ l := by omega
        have h1 := ih hkl' g
        have h2 : (S (l + 1)).1.2 g - (S l).1.2 g ∈ JC ^ ((S k).1.1 - c) := by
          refine Ideal.pow_le_pow_right ?_ (by rw [hSsucc l]; exact hnextdiff (S l) g)
          have := hmonoLev k l hkl'
          omega
        have h3 := Ideal.add_mem (JC ^ ((S k).1.1 - c)) h2 h1
        simpa using h3
      · obtain rfl : k = l + 1 := by omega
        simp
  have hNle : ∀ k, k ≤ (S k).1.1 - c := by
    intro k
    have := hlev k
    omega
  have hcauchy : ∀ g, CauchySeq (fun k => (S k).1.2 g) := by
    intro g
    rw [cauchySeq_iff, uniformity_eq_comap_nhds_zero]
    intro V hV
    obtain ⟨U, hU, hUV⟩ := Filter.mem_comap.mp hV
    obtain ⟨N, -, hNU⟩ := (JC.hasBasis_nhds_zero_adic).mem_iff.mp hU
    refine ⟨N, fun k hk l hl => hUV ?_⟩
    rcases le_total k l with hkl | hlk
    · exact hNU (Ideal.pow_le_pow_right (by have := hNle k; omega) (htel k l hkl g))
    · have h := Ideal.pow_le_pow_right (m := N) (by have := hNle l; omega) (htel l k hlk g)
      simpa using hNU ((JC ^ N).neg_mem h)
  choose F hF using fun g => cauchySeq_tendsto_of_complete (hcauchy g)
  have hFconst : ∀ x : C, Filter.Tendsto (fun _ : ℕ => x) Filter.atTop (nhds x) :=
    fun x => tendsto_const_nhds
  have hdiff : ∀ k g, F g - (S k).1.2 g ∈ JC ^ ((S k).1.1 - c) := fun k g => by
    refine (isClosed_pow_adicTopology JC ((S k).1.1 - c)).mem_of_tendsto
      ((hF g).sub (hFconst ((S k).1.2 g))) ?_
    filter_upwards [Filter.eventually_ge_atTop k] with l hl
    exact htel k l hl g
  refine ⟨{ toFun := F
            map_one' := tendsto_nhds_unique (hF 1)
              ((hFconst (1 : C)).congr fun k => (map_one ((S k).1.2)).symm)
            map_mul' := fun x y => tendsto_nhds_unique (hF (x * y))
              (((hF x).mul (hF y)).congr fun k => (map_mul ((S k).1.2) x y).symm)
            map_zero' := tendsto_nhds_unique (hF 0)
              ((hFconst (0 : C)).congr fun k => (map_zero ((S k).1.2)).symm)
            map_add' := fun x y => tendsto_nhds_unique (hF (x + y))
              (((hF x).add (hF y)).congr fun k => (map_add ((S k).1.2) x y).symm)
            commutes' := fun b => tendsto_nhds_unique (hF (algebraMap A Rs b))
              ((hFconst (algebraMap A C b)).congr
                fun k => (((S k).1.2).commutes b).symm) }, ?_, ?_⟩
  · intro g hg
    have hmem : ∀ k, F g ∈ JC ^ ((S k).1.1 - c) := by
      intro k
      have hval : (S k).1.2 g ∈ JC ^ ((S k).1.1 - c) :=
        Ideal.pow_le_pow_right (by omega) ((S k).2.2.2 g hg)
      simpa using Ideal.add_mem (JC ^ ((S k).1.1 - c)) (hdiff k g) hval
    refine IsHausdorff.haus' (I := JC) (F g) fun m => ?_
    rw [SModEq.sub_mem]
    simpa using Ideal.pow_le_pow_right (hNle m) (hmem m)
  · intro g
    simpa [hS0, s₀] using hdiff 0 g

end Limit

section Main

variable {A : Type u} [CommRing A] [IsNoetherianRing A]

attribute [local instance] HasDerivedCategory.standard

/-- The obstruction relation of Stacks 0GAP, transported from the adic completion of the
polynomial ring to the ring of restricted power series.

If `(algebraMap A B a) ^ c` annihilates every first Ext group of the completed naive cotangent
complex, then there are `γ₁, …, γ_r` in the kernel `J` of the presentation with
`a ^ c · g ≡ ∑ i (∂g/∂xᵢ) γᵢ` modulo `J²` for every `g ∈ J`. -/
public theorem exists_restricted_cramer_relation {I : Ideal A} (a : A)
    (B : AdicFiniteTypeAlgebra.{u, v} A I) (P : CompletedPolynomialPresentation I B) (c : ℕ)
    (hExt : ∀ (N : ModuleCat.{max u v} B.carrier)
      (ξ : DerivedCategory.Ext
        (DerivedCategory.Q.obj (completedNaiveCotangentComplex B P).cochainComplex)
        ((DerivedCategory.singleFunctor (ModuleCat.{max u v} B.carrier) 0).obj N) 1),
      (algebraMap A B.carrier a) ^ c • ξ = 0) :
    ∃ γ : Fin P.variableCount → RestrictedPowerSeries I (Fin P.variableCount),
      (∀ i, γ i ∈ P.restrictedKer) ∧
      ∀ g ∈ P.restrictedKer,
        algebraMap A (RestrictedPowerSeries I (Fin P.variableCount)) (a ^ c) * g
          - ∑ i, partialDerivative I i g * γ i ∈ P.restrictedKer ^ 2 := by
  classical
  set e := RestrictedPowerSeries.adicCompletionAlgEquiv I (Fin P.variableCount) with he
  obtain ⟨γ, hγmem, hγrel⟩ := exists_conormal_cramer_relation_of_ext_annihilated
    (completedNaiveCotangentComplex B P) ((algebraMap A B.carrier a) ^ c)
    (algebraMap A P.completedPolynomialRing (a ^ c))
    (by rw [AlgHom.commutes, map_pow]) hExt
  have hmem : ∀ x ∈ P.ker, e.symm x ∈ P.restrictedKer := by
    intro x hx
    rw [RingHom.mem_ker]
    exact show P.toAlgHom (e (e.symm x)) = 0 by rw [e.apply_symm_apply]; exact hx
  have hderiv : ∀ (i : Fin P.variableCount) (g : RestrictedPowerSeries I (Fin P.variableCount)),
      e.symm ((completedNaiveCotangentComplex B P).partialDeriv i (e g))
        = partialDerivative I i g := by
    intro i g
    rw [CompletedNaiveCotangentComplex.partialDeriv_eq]
    exact show e.symm (e (partialDerivative I i (e.symm (e g)))) = partialDerivative I i g by
      rw [e.symm_apply_apply, e.symm_apply_apply]
  refine ⟨fun i => e.symm (γ i), fun i => hmem _ (hγmem i), ?_⟩
  intro g hg
  have hgk : e g ∈ P.ker := hg
  have h := apply_mem_pow_of_forall_mem e.symm P.ker _ hmem 2 (hγrel (e g) hgk)
  rw [map_sub, map_mul, map_sum] at h
  simp only [map_mul, AlgEquiv.commutes, e.symm_apply_apply, hderiv] at h
  exact h

/-- **Stacks 0AK6.** Let `I = (a)` be a principal ideal of a Noetherian ring `A`, let `B` be an
`I`-adically complete `A`-algebra of finite type modulo `I`, and suppose `a ^ c` annihilates
`Ext¹_B(NL^∧_{B/A}, N)` for every `B`-module `N`. Let `C` be an `I`-adically complete
`A`-algebra on which `a` is a nonzerodivisor and let `n > 2c`. Then every `A`-algebra map
`B → C / aⁿC` agrees modulo `a ^ (n - c)` with the reduction of an `A`-algebra map `B → C`. -/
@[stacks 0AK6]
public theorem exists_algHom_lift_of_isRegular
    (a : A) (I : Ideal A) (hI : I = Ideal.span {a})
    (B : AdicFiniteTypeAlgebra.{u, v} A I)
    (P : CompletedPolynomialPresentation I B)
    (c : ℕ)
    (hExt : ∀ (N : ModuleCat.{max u v} B.carrier)
      (ξ : DerivedCategory.Ext
        (DerivedCategory.Q.obj (completedNaiveCotangentComplex B P).cochainComplex)
        ((DerivedCategory.singleFunctor (ModuleCat.{max u v} B.carrier) 0).obj N) 1),
      (algebraMap A B.carrier a) ^ c • ξ = 0)
    {C : Type w} [CommRing C] [Algebra A C]
    [IsAdicComplete (I.map (algebraMap A C)) C]
    (ha : IsRegular (algebraMap A C a))
    (n : ℕ) (hn : 2 * c < n)
    (ψn : B.carrier →ₐ[A] C ⧸ (I.map (algebraMap A C)) ^ n) :
    ∃ φ : B.carrier →ₐ[A] C,
      (Ideal.Quotient.factorₐ A
        (Ideal.pow_le_pow_right (Nat.sub_le n c))).comp ψn =
      (Ideal.Quotient.mkₐ A ((I.map (algebraMap A C)) ^ (n - c))).comp φ := by
  classical
  have hIfg : I.FG := hI ▸ (Submodule.fg_span_singleton a)
  set e := RestrictedPowerSeries.adicCompletionAlgEquiv I (Fin P.variableCount) with he
  obtain ⟨γ, hγmem, hγrel⟩ := exists_restricted_cramer_relation a B P c hExt
  obtain ⟨ψ, hψc, hψred⟩ := exists_continuousAlgHom_lift_quotient hIfg P n ψn
  have hψJ : ∀ g ∈ P.restrictedKer, ψ g ∈ (I.map (algebraMap A C)) ^ n := by
    intro g hg
    rw [← Ideal.Quotient.eq_zero_iff_mem, hψred g,
      show P.restrictedToAlgHom g = 0 from hg, map_zero]
  obtain ⟨φ, hφker, hφdiff⟩ := exists_limit_algHom (I.map (algebraMap A C)) P.restrictedKer
    (fun f => @Continuous _ _ (limitTopology I (Fin P.variableCount))
      ((I.map (algebraMap A C)).adicTopology) f) c n hn
    (fun m f hm hcont hJ => exists_perturbed_continuousAlgHom a I hI ha P.restrictedKer c m
      (by omega) γ hγmem hγrel f hcont hJ)
    ψ hψc hψJ
  have hvanish : ∀ x ∈ P.ideal, (φ.comp e.symm.toAlgHom) x = 0 := by
    intro x hx
    rw [← P.ker_eq_ideal] at hx
    refine hφker _ ?_
    rw [RingHom.mem_ker]
    exact show P.toAlgHom (e (e.symm x)) = 0 by rw [e.apply_symm_apply]; exact hx
  refine ⟨(Ideal.Quotient.liftₐ P.ideal (φ.comp e.symm.toAlgHom) hvanish).comp
    P.quotientEquiv.symm.toAlgHom, ?_⟩
  have hfac : ∀ y : RestrictedPowerSeries I (Fin P.variableCount),
      ((Ideal.Quotient.liftₐ P.ideal (φ.comp e.symm.toAlgHom) hvanish).comp
        P.quotientEquiv.symm.toAlgHom) (P.restrictedToAlgHom y) = φ y := by
    intro y
    have hq : P.quotientEquiv.symm (P.restrictedToAlgHom y)
        = Ideal.Quotient.mk P.ideal (e y) :=
      P.quotientEquiv.symm_apply_apply _
    exact show (Ideal.Quotient.liftₐ P.ideal (φ.comp e.symm.toAlgHom) hvanish)
        (P.quotientEquiv.symm (P.restrictedToAlgHom y)) = φ y by
      rw [hq]
      exact show φ (e.symm (e y)) = φ y by rw [e.symm_apply_apply]
  refine AlgHom.ext fun b => ?_
  obtain ⟨y, rfl⟩ := P.restrictedToAlgHom_surjective b
  rw [AlgHom.comp_apply, AlgHom.comp_apply, hfac y, ← hψred y]
  exact show Ideal.Quotient.mk ((I.map (algebraMap A C)) ^ (n - c)) (ψ y)
      = Ideal.Quotient.mk ((I.map (algebraMap A C)) ^ (n - c)) (φ y) by
    rw [Ideal.Quotient.eq]
    simpa using (I.map (algebraMap A C) ^ (n - c)).neg_mem (hφdiff y)

end Main

end Rig

end
