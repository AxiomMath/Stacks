module

public import StacksFrontier.AlgebraicGeometry.Blowup.ProjBaseChangeGlobal
public import StacksFrontier.AlgebraicGeometry.ProjModelStructureMap.BaseChange

/-!
# `Proj R[T₀, …, Tₙ]` is cartesian in the coefficient ring, unconditionally

`StacksFrontier/AlgebraicGeometry/ProjModelStructureMap/BaseChange.lean` builds, for a ring
homomorphism `f : R →+* S`, the morphism `Proj S[T₀, …, Tₙ] ⟶ Proj R[T₀, …, Tₙ]` over
`Spec S ⟶ Spec R`, and reduces cartesianness of that square to the single hypothesis
`Stacks.Proj.IsBaseChangeOnCharts (polyGradedMap (Fin (n + 1)) f)`. This file discharges the
cartesianness — **with no hypothesis at all** — and reads off the comparison of the two models of
projective `n`-space over an arbitrary coefficient ring.

## What this closes, and by which route

The `## What is not proved` note of
`StacksFrontier/AlgebraicGeometry/ProjectiveCohomology/ModelComparison.lean` lists three missing
inputs for the general-coefficient-ring comparison. The first and third — the graded ring
homomorphism with its containment of irrelevant ideals, and the degree-zero identification
carrying `AlgebraicGeometry.Proj.toSpecZero` to the structure morphism — are
`Stacks.ProjectiveCohomology.polyGradedMap`,
`Stacks.ProjectiveCohomology.irrelevant_le_map_polyGradedMap` and
`Stacks.ProjectiveCohomology.projModelMap_comp_projModelToSpec`, all already proved.

The second — the chart hypothesis — is **not** proved here, and does not have to be. The note
proposes reaching the global square through `AlgebraicGeometry.Proj.isPullback_toSpecZero_map`,
whose input is the chart hypothesis. But the development already carries the global square for a
*literal* tensor product of graded algebras, `Stacks.ProjBaseChange.isPullback_map_Spec`,
together with its transport along a graded isomorphism onto that tensor product,
`Stacks.ProjBaseChange.isPullback_map_of_baseChange`. That transport asks for exactly a graded
isomorphism `S ⊗[R] 𝒜 ≅ ℬ` compatible with the given graded homomorphism, and for nothing about
charts or localizations. So the whole remaining content is that one graded isomorphism for
polynomial rings,

`S ⊗[R] R[T₀, …, Tₙ] ≅ S[T₀, …, Tₙ]`,

which is `MvPolynomial.algebraTensorAlgEquiv` promoted to a homomorphism of graded rings:
`Stacks.ProjectiveCohomology.polyBaseChangeGradedHom` below. The one degreewise fact it needs is
that `MvPolynomial.algebraTensorAlgEquiv` carries the scalar extension of the degree-`i`
homogeneous piece onto the degree-`i` homogeneous piece. One inclusion is
`MvPolynomial.IsHomogeneous.map` applied to the spanning tensors `1 ⊗ₜ p`; the other is that a
homogeneous polynomial over `S` is an `S`-combination of monomials, each of which is the image of
the same monomial over `R`.

## Main definitions

* `Stacks.ProjectiveCohomology.polyBaseChangeGradedHom` and
  `Stacks.ProjectiveCohomology.polyBaseChangeGradedInv`: the graded ring isomorphism
  `S ⊗[R] R[T₀, …, Tₙ] ≅ S[T₀, …, Tₙ]` and its inverse, both carried by
  `MvPolynomial.algebraTensorAlgEquiv`.
* `Stacks.ProjectiveCohomology.fromULiftInt`: the ring homomorphism `ULift ℤ → S`.
* `Stacks.ProjectiveCohomology.projModelIso`: **the comparison of the two models of projective
  `n`-space over an arbitrary coefficient ring.**

## Main results

* `Stacks.ProjectiveCohomology.map_baseChange_homogeneousSubmodule`: the degreewise transport.
* `Stacks.ProjectiveCohomology.irrelevant_le_map_of_gradedRightInverse`: a graded ring
  homomorphism with a graded right inverse satisfies the containment of irrelevant ideals that
  `AlgebraicGeometry.Proj.map` requires.
* `Stacks.ProjectiveCohomology.isPullback_projModelToSpec`: **`Proj S[T₀, …, Tₙ]` is the base
  change of `Proj R[T₀, …, Tₙ]` along `Spec S ⟶ Spec R`**, for every ring homomorphism
  `f : R →+* S` and with no further hypothesis. This is the conclusion of
  `Stacks.ProjectiveCohomology.isPullback_projModelToSpec_of_isBaseChangeOnCharts` with its
  hypothesis discharged.
* `Stacks.ProjectiveCohomology.isPullback_terminal_from_projModel`: the same square over the
  terminal scheme, the base being `Spec (ULift ℤ)`.
* `Stacks.ProjectiveCohomology.projModelIso_hom_structureMorphism` and
  `Stacks.ProjectiveCohomology.projModelIso_hom_toIntegralAtUniverse`: **the comparison is a
  morphism over `Spec S`**, and it carries `Stacks.ProjectiveCohomology.projModelMap` to the
  projection to the integral model.

## Implementation notes

**The coefficient rings live in one universe.** `Stacks.ProjBaseChange.grading` quantifies the
graded algebra, its base ring and the extension ring at a single universe, so `R` and `S` are both
`Type u` here, and the polynomial ring in `Fin (n + 1)` variables over either of them is again in
`Type u`. For the intended application — comparing `ULift ℤ` with a coefficient ring in the
universe of the base scheme — that is the right shape, and it is why the integral model is
`ULift ℤ` rather than `ℤ`.

**No `Algebra R S` instance appears in the cartesian square or anything after it.** Those results
are stated for a bare `RingHom`, and the `R`-algebra structure that
`Stacks.ProjBaseChange.isPullback_map_of_baseChange` needs is introduced inside the proof as
`RingHom.toAlgebra`, for which `algebraMap R S` is the given homomorphism by definition.

**The graded homomorphisms and their lemmas take their rings explicitly.** A statement that
mentions a section variable only inside a named argument does not cause that variable to be
included, so the implicit-variable spelling of these lemmas elaborates with the coefficient rings
as metavariables. Making the three type arguments explicit is what keeps the statements about the
intended rings.

**The index type of the graded homomorphisms is in `Type 0`, and that too is forced by the single
universe.** `Stacks.ProjBaseChange.includeRight` asks for its graded algebra in `Type u`, so
`MvPolynomial σ R` must be in `Type u`, so `σ` cannot be an arbitrary `Type w` — stated that way,
`Stacks.ProjectiveCohomology.polyGradedMap_eq_comp_includeRight` is a deterministic `whnf` timeout
on the universe constraint `max u w =?= u` rather than an error. The only index type any consumer
needs is `Fin (n + 1)`, which is in `Type 0`. The degreewise transport
`Stacks.ProjectiveCohomology.map_baseChange_homogeneousSubmodule` mentions no scheme and is kept
at an arbitrary index type.

**No tag attribute is attached.** The base-change clause of the projective-space tag is about the
library's model, whose square over the integral model holds by construction; what is proved here
is that the other model has the same square, which is a comparison of two constants rather than a
clause of that tag. The tag whose content the underlying square is carries its attribute where it
is proved, on `Stacks.ProjBaseChange.isPullback_map_Spec`. The attribute tokens are deliberately
not spelled out, because a comment-blind attribute grep reads a spelled token as coverage.

## References

* [Stacks Project, Tag 01N2](https://stacks.math.columbia.edu/tag/01N2)
* [Stacks Project, Tag 01NF](https://stacks.math.columbia.edu/tag/01NF)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TensorProduct
open HomogeneousIdeal HomogeneousLocalization Graded

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

namespace Stacks.ProjectiveCohomology

/-! ### Irrelevant ideals under a graded homomorphism with a graded right inverse -/

section Irrelevant

variable {A B σ τ : Type*} [CommRing A] [CommRing B]
  [SetLike σ A] [AddSubgroupClass σ A] [SetLike τ B] [AddSubgroupClass τ B]
  {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ]

/-- **A graded ring homomorphism with a graded right inverse satisfies the containment of
irrelevant ideals that `AlgebraicGeometry.Proj.map` requires.** Every homogeneous element of
positive degree in the target is the image of its own preimage under the right inverse, which is
homogeneous of the same degree and therefore irrelevant. -/
theorem irrelevant_le_map_of_gradedRightInverse (e : 𝒜 →+*ᵍ ℬ) (e' : ℬ →+*ᵍ 𝒜)
    (h : e.comp e' = GradedRingHom.id ℬ) : ℬ₊ ≤ 𝒜₊.map e := by
  refine (HomogeneousIdeal.irrelevant_le _).2 fun i hi x hx => ?_
  have hex : e (e' x) = x := congrFun (congrArg DFunLike.coe h) x
  exact hex ▸ Ideal.mem_map_of_mem e (HomogeneousIdeal.mem_irrelevant_of_mem 𝒜 hi (map_mem e' hx))

end Irrelevant

/-! ### The graded isomorphism `S ⊗[R] R[T₀, …, Tₙ] ≅ S[T₀, …, Tₙ]` -/

section Degreewise

variable {σ : Type*} {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

/-- `MvPolynomial.algebraTensorAlgEquiv` sends `1 ⊗ₜ p` to the coefficientwise image of `p`. -/
private theorem algebraTensorAlgEquiv_one_tmul (p : MvPolynomial σ R) :
    MvPolynomial.algebraTensorAlgEquiv R S ((1 : S) ⊗ₜ[R] p) =
      MvPolynomial.map (algebraMap R S) p := by
  rw [MvPolynomial.algebraTensorAlgEquiv_tmul, one_smul]

/-- **Scalar extension of a polynomial algebra carries each homogeneous piece onto the piece of
the same degree.** The scalar extension of the degree-`i` piece is spanned by the tensors
`1 ⊗ₜ p` with `p` homogeneous of degree `i`, whose images are the `MvPolynomial.map`s of those
`p` and so homogeneous of degree `i`; conversely the degree-`i` piece over `S` is spanned by the
monomials of degree `i`, each of which is the image of the same monomial over `R`. -/
theorem map_baseChange_homogeneousSubmodule (i : ℕ) :
    Submodule.map (MvPolynomial.algebraTensorAlgEquiv R S).toLinearMap
        ((MvPolynomial.homogeneousSubmodule σ R i).baseChange S) =
      MvPolynomial.homogeneousSubmodule σ S i := by
  rw [Submodule.baseChange_eq_span, Submodule.map_span]
  refine le_antisymm ?_ ?_
  · rw [Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨p, hp, rfl⟩ := Submodule.mem_map.mp hx
    exact (algebraTensorAlgEquiv_one_tmul (S := S) p).symm ▸ hp.map (algebraMap R S)
  · rw [MvPolynomial.homogeneousSubmodule_eq_finsupp_supported,
      AddMonoidAlgebra.supported_eq_span_single, Submodule.span_le]
    rintro _ ⟨d, hd, rfl⟩
    refine Submodule.subset_span ⟨TensorProduct.tmul R 1 (MvPolynomial.monomial d (1 : R)), ?_, ?_⟩
    · exact Submodule.mem_map.mpr
        ⟨MvPolynomial.monomial d 1, MvPolynomial.isHomogeneous_monomial 1 hd, rfl⟩
    · refine (algebraTensorAlgEquiv_one_tmul (S := S) _).trans ?_
      rw [MvPolynomial.map_monomial, map_one]
      rfl

end Degreewise

section GradedTransport

variable (σ : Type) (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]

/-- **Scalar extension of a polynomial algebra is a polynomial algebra, as graded rings.**
`MvPolynomial.algebraTensorAlgEquiv` carries the base-changed grading of `S ⊗[R] R[T₀, …, Tₙ]` to
the total-degree grading of `S[T₀, …, Tₙ]`. -/
def polyBaseChangeGradedHom :
    (fun i => (MvPolynomial.homogeneousSubmodule σ R i).baseChange S) →+*ᵍ
      MvPolynomial.homogeneousSubmodule σ S where
  __ := (MvPolynomial.algebraTensorAlgEquiv R S).toRingHom
  map_mem {i x} hx := by
    have h : (MvPolynomial.algebraTensorAlgEquiv R S).toLinearMap x ∈
        Submodule.map (MvPolynomial.algebraTensorAlgEquiv R S).toLinearMap
          ((MvPolynomial.homogeneousSubmodule σ R i).baseChange S) :=
      Submodule.mem_map_of_mem hx
    rwa [map_baseChange_homogeneousSubmodule] at h

/-- The inverse of `Stacks.ProjectiveCohomology.polyBaseChangeGradedHom`, carried by the inverse
of `MvPolynomial.algebraTensorAlgEquiv`. -/
def polyBaseChangeGradedInv :
    MvPolynomial.homogeneousSubmodule σ S →+*ᵍ
      fun i => (MvPolynomial.homogeneousSubmodule σ R i).baseChange S where
  __ := (MvPolynomial.algebraTensorAlgEquiv R S).symm.toRingHom
  map_mem {i x} hx := by
    rw [← map_baseChange_homogeneousSubmodule (σ := σ) (R := R) (S := S) i] at hx
    obtain ⟨y, hy, hxy⟩ := Submodule.mem_map.mp hx
    have hsymm : (MvPolynomial.algebraTensorAlgEquiv R S).symm x = y :=
      hxy ▸ (MvPolynomial.algebraTensorAlgEquiv R S).symm_apply_apply y
    exact hsymm ▸ hy

/-- `Stacks.ProjectiveCohomology.polyBaseChangeGradedHom` agrees with
`MvPolynomial.algebraTensorAlgEquiv` on every element. -/
@[simp]
theorem polyBaseChangeGradedHom_apply (x : S ⊗[R] MvPolynomial σ R) :
    polyBaseChangeGradedHom σ R S x = MvPolynomial.algebraTensorAlgEquiv R S x := rfl

/-- `Stacks.ProjectiveCohomology.polyBaseChangeGradedInv` agrees with the inverse of
`MvPolynomial.algebraTensorAlgEquiv` on every element. -/
@[simp]
theorem polyBaseChangeGradedInv_apply (x : MvPolynomial σ S) :
    polyBaseChangeGradedInv σ R S x = (MvPolynomial.algebraTensorAlgEquiv R S).symm x := rfl

/-- `polyBaseChangeGradedInv` is a left inverse of `polyBaseChangeGradedHom` as graded ring
homomorphisms. -/
theorem polyBaseChangeGradedInv_comp_hom :
    (polyBaseChangeGradedInv σ R S).comp (polyBaseChangeGradedHom σ R S) =
      GradedRingHom.id (fun i => (MvPolynomial.homogeneousSubmodule σ R i).baseChange S) :=
  GradedRingHom.ext fun x => (MvPolynomial.algebraTensorAlgEquiv R S).symm_apply_apply x

/-- `polyBaseChangeGradedInv` is a right inverse of `polyBaseChangeGradedHom` as graded ring
homomorphisms. -/
theorem polyBaseChangeGradedHom_comp_inv :
    (polyBaseChangeGradedHom σ R S).comp (polyBaseChangeGradedInv σ R S) =
      GradedRingHom.id (MvPolynomial.homogeneousSubmodule σ S) :=
  GradedRingHom.ext fun x => (MvPolynomial.algebraTensorAlgEquiv R S).apply_symm_apply x

/-- The containment of irrelevant ideals for
`Stacks.ProjectiveCohomology.polyBaseChangeGradedHom`. -/
theorem irrelevant_le_map_polyBaseChangeGradedHom :
    (MvPolynomial.homogeneousSubmodule σ S)₊ ≤
      (fun i => (MvPolynomial.homogeneousSubmodule σ R i).baseChange S)₊.map
        (polyBaseChangeGradedHom σ R S) :=
  irrelevant_le_map_of_gradedRightInverse _ _ (polyBaseChangeGradedHom_comp_inv σ R S)

/-- The containment of irrelevant ideals for
`Stacks.ProjectiveCohomology.polyBaseChangeGradedInv`. -/
theorem irrelevant_le_map_polyBaseChangeGradedInv :
    (fun i => (MvPolynomial.homogeneousSubmodule σ R i).baseChange S)₊ ≤
      (MvPolynomial.homogeneousSubmodule σ S)₊.map (polyBaseChangeGradedInv σ R S) :=
  irrelevant_le_map_of_gradedRightInverse _ _ (polyBaseChangeGradedInv_comp_hom σ R S)

/-- **`Stacks.ProjectiveCohomology.polyGradedMap` factors through the base change.** The graded
homomorphism induced by the structure map of `S` is the inclusion `p ↦ 1 ⊗ₜ p` into the scalar
extension followed by the graded isomorphism onto `S[T₀, …, Tₙ]`. -/
theorem polyGradedMap_eq_comp_includeRight :
    polyGradedMap σ (algebraMap R S) =
      (polyBaseChangeGradedHom σ R S).comp
        (Stacks.ProjBaseChange.includeRight (MvPolynomial.homogeneousSubmodule σ R) S) :=
  GradedRingHom.ext fun p => by
    exact (algebraTensorAlgEquiv_one_tmul (S := S) p).symm

end GradedTransport

/-! ### The degree-zero identifications -/

section DegreeZero

variable (R S : Type u) [CommRing R] [CommRing S]

/-- The degree-zero identification of
`StacksFrontier/AlgebraicGeometry/ProjModelStructureMap/Basic.lean` is the structure map of the
degree-zero part: both send a scalar to the corresponding constant polynomial. -/
theorem polyDegreeZeroHom_eq_ofHom_algebraMap (n : ℕ) :
    polyDegreeZeroHom R n = CommRingCat.ofHom (algebraMap R ↥(polyGrading R n 0)) :=
  CommRingCat.hom_ext (RingHom.ext fun _ => Subtype.ext rfl)

/-- **The degree-zero part of the graded isomorphism is the degree-zero identification.** Under
`Stacks.ProjectiveCohomology.polyBaseChangeGradedHom` the degree-zero scalar `s ⊗ₜ 1` of the
base-changed grading goes to the constant polynomial `C s`. -/
theorem ofHom_gradedZeroRingHom_polyBaseChangeGradedHom_comp [Algebra R S] (n : ℕ) :
    CommRingCat.ofHom
        ((polyBaseChangeGradedHom (Fin (n + 1)) R S).gradedZeroRingHom.comp
          (algebraMap S ↥(Stacks.ProjBaseChange.grading
            (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) S 0))) =
      polyDegreeZeroHom S n := by
  refine CommRingCat.hom_ext (RingHom.ext fun s => Subtype.ext ?_)
  show MvPolynomial.algebraTensorAlgEquiv R S
      (TensorProduct.tmul R s (1 : MvPolynomial (Fin (n + 1)) R)) =
    MvPolynomial.C s
  rw [MvPolynomial.algebraTensorAlgEquiv_tmul, map_one, MvPolynomial.smul_eq_C_mul, mul_one]

end DegreeZero

/-! ### The cartesian square, with no hypothesis -/

section Cartesian

variable (R S : Type u) [CommRing R] [CommRing S]

/-- The structure morphism of `Proj R[T₀, …, Tₙ]` factored through the degree-zero part, in the
spelling `Stacks.ProjBaseChange.isPullback_map_of_baseChange` produces. -/
theorem toSpecZero_comp_Spec_map_ofHom_algebraMap (n : ℕ) :
    AlgebraicGeometry.Proj.toSpecZero (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) ≫
        Spec.map (CommRingCat.ofHom
          (algebraMap R ↥(MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R 0))) =
      projModelToSpec R n := by
  rw [projModelToSpec_eq, polyDegreeZeroHom_eq_ofHom_algebraMap]

/-- The structure morphism of `Proj S[T₀, …, Tₙ]` read through the graded isomorphism onto the
scalar extension, in the spelling `Stacks.ProjBaseChange.isPullback_map_of_baseChange`
produces. -/
theorem map_polyBaseChangeGradedHom_comp_toSpecZero [Algebra R S] (n : ℕ) :
    AlgebraicGeometry.Proj.map (polyBaseChangeGradedHom (Fin (n + 1)) R S)
          (irrelevant_le_map_polyBaseChangeGradedHom (Fin (n + 1)) R S) ≫
        AlgebraicGeometry.Proj.toSpecZero (Stacks.ProjBaseChange.grading
            (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) S) ≫
          Spec.map (CommRingCat.ofHom (algebraMap S ↥(Stacks.ProjBaseChange.grading
            (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) S 0))) =
      projModelToSpec S n := by
  rw [AlgebraicGeometry.Proj.map_toSpecZero_assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
    ofHom_gradedZeroRingHom_polyBaseChangeGradedHom_comp, projModelToSpec_eq]

/-- **`Proj S[T₀, …, Tₙ]` is the base change of `Proj R[T₀, …, Tₙ]` along `Spec S ⟶ Spec R`**, for
every ring homomorphism `f : R →+* S` and with no further hypothesis.

This is the conclusion of
`Stacks.ProjectiveCohomology.isPullback_projModelToSpec_of_isBaseChangeOnCharts` with its chart
hypothesis discharged. The route is not through the chart hypothesis: the square for a *literal*
tensor product is `Stacks.ProjBaseChange.isPullback_map_Spec`, its transport along a graded
isomorphism onto the tensor product is
`Stacks.ProjBaseChange.isPullback_map_of_baseChange`, and the graded isomorphism is
`Stacks.ProjectiveCohomology.polyBaseChangeGradedHom`. -/
theorem isPullback_projModelToSpec (n : ℕ) (f : R →+* S) :
    IsPullback (projModelToSpec S n) (projModelMap n f)
      (Spec.map (CommRingCat.ofHom f)) (projModelToSpec R n) := by
  let _ : Algebra R S := f.toAlgebra
  have H := Stacks.ProjBaseChange.isPullback_map_of_baseChange
    (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) S
    (f := polyGradedMap (Fin (n + 1)) (algebraMap R S))
    (irrelevant_le_map_polyGradedMap (Fin (n + 1)) (algebraMap R S))
    (e := polyBaseChangeGradedHom (Fin (n + 1)) R S)
    (irrelevant_le_map_polyBaseChangeGradedHom (Fin (n + 1)) R S)
    (e' := polyBaseChangeGradedInv (Fin (n + 1)) R S)
    (irrelevant_le_map_polyBaseChangeGradedInv (Fin (n + 1)) R S)
    (polyBaseChangeGradedInv_comp_hom (Fin (n + 1)) R S)
    (polyBaseChangeGradedHom_comp_inv (Fin (n + 1)) R S)
    (polyGradedMap_eq_comp_includeRight (Fin (n + 1)) R S)
  rw [map_polyBaseChangeGradedHom_comp_toSpecZero R S n,
    toSpecZero_comp_Spec_map_ofHom_algebraMap R n] at H
  exact H.flip

end Cartesian

/-! ### The comparison of the two models over an arbitrary coefficient ring -/

section ModelComparison

variable (S : Type u) [CommRing S]

/-- The ring homomorphism out of the integral model's coefficient ring. -/
def fromULiftInt : ULift.{u} ℤ →+* S :=
  (Int.castRingHom S).comp (ULift.ringEquiv : ULift.{u} ℤ ≃+* ℤ).toRingHom

/-- **The square of `Stacks.ProjectiveCohomology.isPullback_projModelToSpec` over the terminal
scheme.** `Spec (ULift ℤ)` is terminal, so the base change of the integral `Proj` model along
`Spec S` may be read over the terminal scheme, which is the shape in which the library's model of
projective space is defined. -/
theorem isPullback_terminal_from_projModel (n : ℕ) :
    IsPullback (projModelToSpec S n) (projModelMap n (fromULiftInt S))
      (terminal.from (Spec (CommRingCat.of S)))
      (terminal.from (AlgebraicGeometry.projectiveSpaceAtUniverse.{u} n)) :=
  (isPullback_projModelToSpec (ULift.{u} ℤ) S n (fromULiftInt S)).of_iso
    (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (AlgebraicGeometry.specULiftZIsTerminal.uniqueUpToIso terminalIsTerminal)
    (by simp) (by simp) (terminal.hom_ext _ _) (terminal.hom_ext _ _)

/-- **The two models of projective `n`-space agree over an arbitrary coefficient ring.** The
source's `Proj S[T₀, …, Tₙ]` and the library's `AlgebraicGeometry.projectiveSpaceOverRing`, which
is defined as the base change of the integral model along `Spec S ⟶ Spec ℤ`, are isomorphic. Over
a terminal base this specialises to `Stacks.ProjectiveCohomology.integralModelIso`, which was
previously the only case available. -/
def projModelIso (n : ℕ) :
    AlgebraicGeometry.Proj (polyGrading S n) ≅
      AlgebraicGeometry.projectiveSpaceOverRing n (CommRingCat.of S) :=
  (isPullback_terminal_from_projModel S n).isoPullback

/-- **The comparison is a morphism over `Spec S`**: it carries the structure morphism of the
library's model to `Stacks.ProjectiveCohomology.projModelToSpec`. -/
@[reassoc]
theorem projModelIso_hom_structureMorphism (n : ℕ) :
    (projModelIso S n).hom ≫
        pullback.fst (terminal.from (Spec (CommRingCat.of S)))
          (terminal.from (AlgebraicGeometry.projectiveSpaceAtUniverse.{u} n)) =
      projModelToSpec S n :=
  (isPullback_terminal_from_projModel S n).isoPullback_hom_fst

/-- **The comparison carries `Stacks.ProjectiveCohomology.projModelMap` to the projection to the
integral model.** -/
@[reassoc]
theorem projModelIso_hom_toIntegralAtUniverse (n : ℕ) :
    (projModelIso S n).hom ≫
        AlgebraicGeometry.projectiveSpaceOver.toIntegralAtUniverse n (Spec (CommRingCat.of S)) =
      projModelMap n (fromULiftInt S) :=
  (isPullback_terminal_from_projModel S n).isoPullback_hom_snd

end ModelComparison

end Stacks.ProjectiveCohomology

end
