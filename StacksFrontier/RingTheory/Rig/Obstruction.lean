module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Homology.TwoTermComplex.Representative
public import StacksFrontier.RingTheory.Rig.NaiveCotangent

/-!
# The obstruction class of a completed presentation (Stacks 0GAP)

Let `A` be a Noetherian ring, `I` an ideal of `A`, `B` an `I`-adically complete `A`-algebra of
finite type modulo `I`, and `B = A⟨x₁, …, x_r⟩ / J` a completed polynomial presentation. The
completed naive cotangent complex of the presentation is the two-term complex
`J / J² → ⨁ i, B dxᵢ`, and Stacks 0GAP identifies

`Ext¹_B(NL^∧_{B/A}, N) = Coker (Hom_B(⨁ i, B dxᵢ, N) → Hom_B(J / J², N))`

so that the obstruction to lifting an `A`-algebra map `B → C / IⁿC` is a class in
`Ext¹_B(NL^∧_{B/A}, IⁿC / I²ⁿC)`.

This file extracts from that identification the form in which the obstruction class is
*used*: that `b` annihilates every first Ext group out of the complex says exactly that
multiplication by `b` on the conormal module `J / J²` factors through the differential, and
hence — reading the factorisation back on representatives in `A⟨x₁, …, x_r⟩` — that for every
`g ∈ J` one has

`β · g - ∑ i, (∂g/∂xᵢ) · γᵢ ∈ J²`

for a fixed family `γ₁, …, γ_r ∈ J`, where `β` is any lift of `b`. Applying an `A`-algebra map
`ψ : A⟨x₁, …, x_r⟩ → C` with `ψ(J) ⊆ IⁿC` to this relation is precisely the statement that the
obstruction class of `ψ` becomes `b`-divisible by `(h ∘ d)`, with no quotient module needing to
be built; this is what `Rig.exists_algHom_lift_of_isRegular` consumes.

## Main results

* `Rig.exists_linearMap_comp_differential_eq_smul`: ideal annihilation of the first Ext groups
  of the completed naive cotangent complex gives a `B`-linear retraction of its differential up
  to the annihilating scalar. **Stacks 0GAP**, the `Ext¹`-as-cokernel half.
* `Rig.exists_conormal_cramer_relation`: the resulting relation in `A⟨x₁, …, x_r⟩` modulo `J²`.
* `Rig.exists_conormal_cramer_relation_of_ext_annihilated`: the two combined, in the form the
  lifting arguments of Stacks 0AK6, 0AK7 and 0GAQ use.

## Implementation notes

The `Ext¹`-as-cokernel identification is not rebuilt here: it is
`TwoTermComplex.ext_one_annihilated_iff_twoTerm_factorization` (Stacks 0G9F), which rests on
`TwoTermComplexExt.toHomD_bijective` (Stacks 0ALN part (1)). That theorem is stated for an
arbitrary two-term representative with projective degree-zero term, and the completed naive
cotangent complex is such a representative of itself: it is `HomologicalComplex.double`, so it
is strictly supported in degrees `-1` and `0`, and its degree-zero term is the universe lift of
the free module `⨁ i, B dxᵢ`.

Passing from the categorical factorisation to the relation modulo `J²` uses no quotient module.
The point is that a `B`-linear map out of `J / J²` evaluated on the class of `g ∈ J` is computed
by any representative, so the identity `b • [g] = ∑ i (∂g/∂xᵢ) • [γᵢ]` in `J / J²` already says
that the difference of representatives lies in `J²`.

## References

* [Stacks Project, Tag 0GAP](https://stacks.math.columbia.edu/tag/0GAP)
* [Stacks Project, Tag 0G9F](https://stacks.math.columbia.edu/tag/0G9F)
* [Stacks Project, Tag 0ALN](https://stacks.math.columbia.edu/tag/0ALN)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Algebra.Extension

namespace Algebra.Extension

/-- The class of `r • x` in the conormal module of an extension is the image of the class of
`x` under the scalar `r` viewed in the quotient algebra. -/
public theorem Cotangent.mk_smul_algebraMap {R S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] (P : Algebra.Extension R S) (r : P.Ring) (x : P.ker) :
    Cotangent.mk (r • x) = (algebraMap P.Ring S r) • Cotangent.mk x := by
  rw [map_smul]; rfl

/-- A relation between classes in the conormal module `ker / ker²` of an extension is a relation
between representatives modulo `ker²`. -/
public theorem sub_sum_mul_mem_ker_sq {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (P : Algebra.Extension R S) {ι : Type*} [Fintype ι] (β : P.Ring) (d : ι → P.Ring)
    (γ : ι → P.ker) (g : P.ker)
    (h : (algebraMap P.Ring S β) • Cotangent.mk g
        = ∑ i, (algebraMap P.Ring S (d i)) • Cotangent.mk (γ i)) :
    β * (g : P.Ring) - ∑ i, d i * (γ i : P.Ring) ∈ P.ker ^ 2 := by
  rw [← Cotangent.mk_smul_algebraMap] at h
  rw [show (∑ i, (algebraMap P.Ring S (d i)) • Cotangent.mk (γ i))
      = Cotangent.mk (∑ i, d i • γ i) by
    rw [map_sum]
    exact (Finset.sum_congr rfl fun i _ => Cotangent.mk_smul_algebraMap P _ _).symm] at h
  simpa [Submodule.coe_smul, smul_eq_mul] using
    (Cotangent.mk_eq_mk_iff_sub_mem (P := P) _ _).mp h

end Algebra.Extension

namespace Rig

universe u v

variable {A : Type u} [CommRing A] {I : Ideal A}

attribute [local instance] HasDerivedCategory.standard

section Strictness

variable {B : AdicFiniteTypeAlgebra.{u, v} A I} {P : CompletedPolynomialPresentation I B}

/-- The completed naive cotangent complex vanishes in degrees below `-1`. -/
public theorem CompletedNaiveCotangentComplex.isStrictlyGE
    (K : CompletedNaiveCotangentComplex P) : K.cochainComplex.IsStrictlyGE (-1) := by
  rw [CochainComplex.isStrictlyGE_iff]
  intro i hi
  exact HomologicalComplex.isZero_double_X _ _ i (by omega) (by omega)

/-- The completed naive cotangent complex vanishes in positive degrees. -/
public theorem CompletedNaiveCotangentComplex.isStrictlyLE
    (K : CompletedNaiveCotangentComplex P) : K.cochainComplex.IsStrictlyLE 0 := by
  rw [CochainComplex.isStrictlyLE_iff]
  intro i hi
  exact HomologicalComplex.isZero_double_X _ _ i (by omega) (by omega)

/-- The degree-zero term of the completed naive cotangent complex is free, being the universe
lift of `⨁ i, B dxᵢ`. -/
public theorem CompletedNaiveCotangentComplex.free_X_zero
    (K : CompletedNaiveCotangentComplex P) :
    Module.Free B.carrier (K.cochainComplex.X 0) :=
  Module.Free.of_equiv (K.degreeZeroIso.toLinearEquiv (R := B.carrier)).symm

/-- The cohomology of the completed naive cotangent complex is concentrated in degrees `-1`
and `0`. -/
public theorem CompletedNaiveCotangentComplex.isZero_homologyFunctor
    (K : CompletedNaiveCotangentComplex P) (i : ℤ) (hi₁ : i ≠ -1) (hi₀ : i ≠ 0) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} B.carrier) i).obj
      (DerivedCategory.Q.obj K.cochainComplex)) := by
  have := K.isStrictlyGE
  have := K.isStrictlyLE
  apply IsZero.of_iso _ ((DerivedCategory.homologyFunctorFactors _ i).app K.cochainComplex)
  rcases lt_or_gt_of_ne hi₀ with hi | hi
  · exact (CochainComplex.exactAt_of_isGE K.cochainComplex (-1) i (by omega)).isZero_homology
  · exact (CochainComplex.exactAt_of_isLE K.cochainComplex 0 i hi).isZero_homology

end Strictness

section Retraction

variable {B : AdicFiniteTypeAlgebra.{u, v} A I} {P : CompletedPolynomialPresentation I B}

/-- **Stacks 0GAP**, the identification of `Ext¹_B(NL^∧_{B/A}, -)` with the cokernel of
`Hom_B(⨁ i, B dxᵢ, -) → Hom_B(J / J², -)`, in the form it is used.

If multiplication by `b` kills `Ext¹_B(NL^∧_{B/A}, N)` for every `B`-module `N`, then
multiplication by `b` on the conormal module `J / J²` factors through the differential of the
completed naive cotangent complex: there is a `B`-linear `H : ⨁ i, B dxᵢ → J / J²` with
`H ∘ d = b`. Taking `N = J / J²` and the class of the identity, this is exactly the vanishing
hypothesis read through the cokernel description. -/
public theorem exists_linearMap_comp_differential_eq_smul
    (K : CompletedNaiveCotangentComplex P) (b : B.carrier)
    (hExt : ∀ (N : ModuleCat.{max u v} B.carrier)
      (ξ : DerivedCategory.Ext (DerivedCategory.Q.obj K.cochainComplex)
        ((DerivedCategory.singleFunctor (ModuleCat.{max u v} B.carrier) 0).obj N) 1),
      b • ξ = 0) :
    ∃ H : (Fin P.variableCount → B.carrier) →ₗ[B.carrier] P.extension.Cotangent,
      ∀ x, H (K.differential x) = b • x := by
  have h1 := K.isStrictlyGE
  have h2 := K.isStrictlyLE
  have h3 := K.free_X_zero
  have hproj : Module.Projective B.carrier (K.cochainComplex.X 0) := by
    have := h3; infer_instance
  have hAnn : ∀ (N : ModuleCat.{max u v} B.carrier) (x : B.carrier), x ∈ Ideal.span {b} →
      ∀ ξ : DerivedCategory.Ext (DerivedCategory.Q.obj K.cochainComplex)
        ((DerivedCategory.singleFunctor (ModuleCat.{max u v} B.carrier) 0).obj N) 1,
        x • ξ = 0 := by
    intro N x hx ξ
    obtain ⟨y, rfl⟩ := Ideal.mem_span_singleton'.mp hx
    rw [mul_smul, hExt N ξ, smul_zero]
  have criterion := TwoTermComplex.ext_one_annihilated_iff_twoTerm_factorization
    (Ideal.span {b}) (DerivedCategory.Q.obj K.cochainComplex) K.isZero_homologyFunctor
  obtain ⟨h, hh⟩ := criterion.2.1.mp (criterion.1.mp hAnn) K.cochainComplex h1 h2 hproj
    ⟨Iso.refl _⟩ b (Ideal.mem_span_singleton_self b)
  set isoZero := K.degreeZeroIso
  set isoNegOne := K.degreeNegOneIso
  set ht : ModuleCat.of B.carrier
        (CompletedNaiveCotangentComplex.LiftedDifferentials (P := P)) ⟶
      ModuleCat.of B.carrier (CompletedNaiveCotangentComplex.LiftedCotangent (P := P)) :=
    isoZero.inv ≫ h ≫ isoNegOne.hom with hht
  have key : ModuleCat.ofHom K.liftedDifferential ≫ ht = b • 𝟙 _ := by
    rw [K.cochainComplex_d] at hh
    rw [hht]
    set D := ModuleCat.ofHom K.liftedDifferential with hD
    calc D ≫ (isoZero.inv ≫ h ≫ isoNegOne.hom)
        = isoNegOne.inv ≫ (isoNegOne.hom ≫ D ≫ isoZero.inv ≫ h) ≫ isoNegOne.hom := by
          simp
      _ = isoNegOne.inv ≫ (b • 𝟙 (K.cochainComplex.X (-1))) ≫ isoNegOne.hom := by
          rw [show isoNegOne.hom ≫ D ≫ isoZero.inv ≫ h
              = (isoNegOne.hom ≫ D ≫ isoZero.inv) ≫ h by simp, ← hh]
      _ = b • 𝟙 _ := by simp
  refine ⟨ULift.moduleEquiv.toLinearMap.comp
    ((ModuleCat.Hom.hom ht).comp ULift.moduleEquiv.symm.toLinearMap), ?_⟩
  intro x
  have hx := congrArg (fun (f : _ ⟶ _) => (ModuleCat.Hom.hom f) (ULift.up x)) key
  simp only [ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply,
    ModuleCat.hom_ofHom, CompletedNaiveCotangentComplex.liftedDifferential_up,
    ModuleCat.hom_smul, ModuleCat.hom_id, LinearMap.smul_apply, LinearMap.id_apply] at hx
  simpa using congrArg ULift.down hx

/-- A `B`-linear retraction of the differential up to the scalar `b`, read on representatives:
for every `g ∈ J` the element `β · g` agrees with `∑ i, (∂g/∂xᵢ) · γᵢ` modulo `J²`, where `β`
lifts `b` and the `γᵢ ∈ J` represent the images of the basis of `⨁ i, B dxᵢ`. -/
public theorem exists_conormal_cramer_relation
    (K : CompletedNaiveCotangentComplex P) (b : B.carrier)
    (β : P.completedPolynomialRing) (hβ : P.toAlgHom β = b)
    (H : (Fin P.variableCount → B.carrier) →ₗ[B.carrier] P.extension.Cotangent)
    (hH : ∀ x, H (K.differential x) = b • x) :
    ∃ γ : Fin P.variableCount → P.completedPolynomialRing,
      (∀ i, γ i ∈ P.ker) ∧
      ∀ g ∈ P.ker, β * g - ∑ i, K.partialDeriv i g * γ i ∈ P.ker ^ 2 := by
  classical
  choose γ hγ using fun i => Cotangent.mk_surjective (P := P.extension) (H (Pi.single i 1))
  refine ⟨fun i => (γ i).val, fun i => (γ i).2, ?_⟩
  intro g hg
  refine Algebra.Extension.sub_sum_mul_mem_ker_sq P.extension β
    (fun i => K.partialDeriv i g) γ ⟨g, hg⟩ ?_
  have h1 : b • Cotangent.mk (P := P.extension) ⟨g, hg⟩
      = H (K.differential (Cotangent.mk ⟨g, hg⟩)) := (hH _).symm
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

/-- **Stacks 0GAP.** The obstruction relation in the form the lifting arguments use: if `b`
annihilates every first Ext group of the completed naive cotangent complex, and `β` lifts `b` to
`A⟨x₁, …, x_r⟩`, then there are `γ₁, …, γ_r ∈ J` with

`β · g - ∑ i, (∂g/∂xᵢ) · γᵢ ∈ J²`  for every `g ∈ J`.

Applying an `A`-algebra map `ψ : A⟨x₁, …, x_r⟩ → C` with `ψ(J) ⊆ IⁿC` turns this into the
statement that `b · o(ψ)` is the composite of the differential with the map
`dxᵢ ↦ ψ(γᵢ) mod I²ⁿC`, i.e. that the obstruction class is killed by `b`. -/
@[stacks 0GAP "the obstruction class"]
public theorem exists_conormal_cramer_relation_of_ext_annihilated
    (K : CompletedNaiveCotangentComplex P) (b : B.carrier)
    (β : P.completedPolynomialRing) (hβ : P.toAlgHom β = b)
    (hExt : ∀ (N : ModuleCat.{max u v} B.carrier)
      (ξ : DerivedCategory.Ext (DerivedCategory.Q.obj K.cochainComplex)
        ((DerivedCategory.singleFunctor (ModuleCat.{max u v} B.carrier) 0).obj N) 1),
      b • ξ = 0) :
    ∃ γ : Fin P.variableCount → P.completedPolynomialRing,
      (∀ i, γ i ∈ P.ker) ∧
      ∀ g ∈ P.ker, β * g - ∑ i, K.partialDeriv i g * γ i ∈ P.ker ^ 2 := by
  obtain ⟨H, hH⟩ := exists_linearMap_comp_differential_eq_smul K b hExt
  exact exists_conormal_cramer_relation K b β hβ H hH

end Retraction

end Rig

end
