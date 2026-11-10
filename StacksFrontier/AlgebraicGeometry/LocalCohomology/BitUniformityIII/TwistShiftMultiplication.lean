module

public import StacksFrontier.AlgebraicGeometry.Constructions.ProjTwistSectionModuleGraded
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.BitUniformityIII.TwistShiftIdeal
public import StacksFrontier.AlgebraicGeometry.ProjRepresentsF1.TwistPowers
public import StacksCore.Tactic.StacksAttribute

/-!
# `𝒪_X(t+1) ⟶ 𝒪_X(t)` on the blowup against the multiplication of twists

Let `A` be a commutative ring, `I ⊆ A` an ideal, `S = ⨁_{n ≥ 0} Iⁿ` the Rees algebra and
`X = Proj(S)` the blowup of `Spec(A)` in `I`. The map `𝒪_X(t+1) ⟶ 𝒪_X(t)` of
`StacksFrontier/AlgebraicGeometry/LocalCohomology/BitUniformityIII/AmbientTwistMap.lean` is
`Stacks.Blowup.twistShiftMap`, division by `X` in the Rees model. This file records how it meets
*multiplication* on the twists, in the two forms the library has them:

* the multiplication of two twists,
  `Stacks.AlgebraicGeometry.ProjInvertibleLocus.twistMultiplicationMap 𝒮 a b : 𝒪(a) ⊗ 𝒪(b) ⟶
  𝒪(a+b)`, which on the blowup is an **isomorphism** in all integer degrees, because the Rees
  algebra is generated in degree one;
* multiplication by a single homogeneous scalar,
  `Stacks.AlgebraicGeometry.ProjTwistedSections.twistScalarSheafMap 𝒮 i n k h a : 𝒪(n) ⟶ 𝒪(k)`
  for `a` homogeneous of degree `i` and `i + n = k`, with which `twistShiftMap` **commutes on
  both sides**: composed either way with multiplication by the degree-one element
  `b⁽¹⁾ = bX` attached to `b ∈ I` it is multiplication by `b`.

The second statement is [Stacks, Tag 02OS] part (3) at the level of morphisms of sheaves. Its
algebraic form, `Stacks.Blowup.reesDegOne_mul_reesShift`, was already available on the module
`S₊`; what is added here is that it holds between the *morphisms of twisting sheaves* the
sequences of [Stacks, Tag 0GA7] are written in, which needs the factorisation of multiplication
by `b⁽¹⁾` through the truncation `S₊` on which `divX` is linear.

## Main definitions

* `Stacks.Blowup.reesDegOneTrunc`: multiplication by `b⁽¹⁾`, read as a linear map
  `S →ₗ[S] S₊` into the truncation of `S(t+1)` above degree `-t`. Every product with `b⁽¹⁾` has
  vanishing constant term, which is exactly membership in that truncation.

## Main results

* `Stacks.Blowup.isIso_twistMultiplicationMap_reesGrading`: **the multiplication
  `𝒪_X(a) ⊗ 𝒪_X(b) ⟶ 𝒪_X(a+b)` of twists on the blowup is an isomorphism**, for all `a b : ℤ`.
* `Stacks.Blowup.twistScalarSheafMap_reesDegOne_eq`: multiplication by `b⁽¹⁾` as a morphism
  `𝒪_X(t) ⟶ 𝒪_X(t+1)` factors through the truncation, as the map `reesDegOneTrunc` induces
  followed by the comparison `(S₊(t+1))~ ≅ 𝒪_X(t+1)`.
* `Stacks.Blowup.twistScalarSheafMap_reesDegOne_comp_twistShiftMap` and
  `Stacks.Blowup.twistShiftMap_comp_twistScalarSheafMap_reesDegOne`: **multiplication by `b⁽¹⁾`
  and `twistShiftMap` compose, in either order, to multiplication by `b`.**
* `Stacks.Blowup.mul_mem_twistGrading_add`: multiplying by a homogeneous element of degree `d`
  carries the degree-`i` piece of `S(t)` into the degree-`i` piece of `S(t+d)`, at the spelling
  of the grading the Rees files use.

## Implementation notes

**The multiplication of twists was never instantiated at the Rees grading.**
`Stacks.AlgebraicGeometry.ProjRepresentsF1.isIso_twistMultiplicationMap_of_adjoin` holds for any
graded ring generated in degree one over its degree-zero part, and
`Stacks.Blowup.adjoin_reesGradingZero_reesGrading_one_eq_top` says the Rees algebra is one; the
two had not been composed. The docstring of
`StacksFrontier/AlgebraicGeometry/Blowup/TwistDegreeOne.lean` recording the degree-`n`
multiplication comparison as the "one gap left open" is stale.

**Multiplication by `b⁽¹⁾` is not stated by hand.** It is
`Stacks.AlgebraicGeometry.ProjTwistedSections.twistScalarSheafMap` at `i = 1`, whose unit,
composition and biadditivity laws are already proved there, and whose target degree is a
parameter with an equation — which is what lets `1 + t` be read as `t + 1` without an
`eqToHom`. The degrees here are therefore supplied as `reesTwistedDegree_one` and
`Stacks.AlgebraicGeometry.ProjTwistedSections.twistedDegree_zero` rather than closed by `rfl`:
neither `((1 : ℕ) : ℤ) + t = t + 1` nor `((0 : ℕ) : ℤ) + t = t` holds by reflexivity.

**The truncation receives all of `S` once it receives `b⁽¹⁾`.** `reesDegOneTrunc` is not built by
checking the defining condition of `Stacks.GradedModule.truncationAbove` for a general product:
`b⁽¹⁾` itself is homogeneous of degree `-t` in `S(t+1)`, hence lies in the truncation above
`-t`, and the truncation is an `S`-submodule, so `x * b⁽¹⁾ = x • b⁽¹⁾` lies in it for every `x`.

**No `rw` is applied to an equation between morphisms.** Both composition statements are proved
by chains of `congrArg` whose functions carry the type of the morphism, as everything else about
`Stacks.Blowup.twistShiftMap` is: the map is `irreducible` and a `rw` under a `.val.app` or
inside a `≫` is where the heartbeat budget of this subtree goes. The inverse of
`Stacks.Blowup.reesTruncationComparison` is never computed — the first statement cancels it
against `Stacks.Blowup.comparison_hom_comp_twistShiftMap`, and the second cancels the comparison
on the left by `CategoryTheory.Iso.cancel_iso_hom_left`.

**No attribute for [Stacks, Tag 02OS] is attached.** That tag is deliberately unregistered in
this repository, and what is proved here is its part (3) only in the algebraic form above: that
`twistShiftMap` and multiplication by `b⁽¹⁾` are inverse up to `b`. The identification of
`𝒪_X(1)` with the ideal sheaf `𝒪_X(-Y)` of the exceptional divisor — the statement the
exactness field `amb_shortExact` of
`Stacks.LocalCohomology.UniformityIII.GeometricInput` needs — is not proved here; see the
obstruction register of
`StacksFrontier/AlgebraicGeometry/LocalCohomology/BitUniformityIII/BlowupTwists.lean` for what it
still takes.

## References

* [Stacks Project, Tag 01MO](https://stacks.math.columbia.edu/tag/01MO)
* [Stacks Project, Tag 01MU](https://stacks.math.columbia.edu/tag/01MU)
* [Stacks Project, Tag 02OS](https://stacks.math.columbia.edu/tag/02OS)
* [Stacks Project, Tag 0GA7](https://stacks.math.columbia.edu/tag/0GA7)
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory Opposite TopologicalSpace Polynomial
open AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpectrum.Proj (twistingSheaf associatedModuleSheaf
  integerGrading_neg twistGrading_apply)
open Stacks.GradedModule
open Stacks.AlgebraicGeometry.ProjSheafFunctoriality (associatedModuleSheafMap
  associatedModuleSheafMap_comp)
open Stacks.AlgebraicGeometry.ProjInvertibleLocus (twistMultiplicationMap)
open Stacks.AlgebraicGeometry.ProjTwistedSections (twistScalarSheafMap twistedDegree_zero)

universe u

namespace Stacks.Blowup

variable {A : Type u} [CommRing A] (I : Ideal A)

/-! ### The multiplication of twists on the blowup -/

/-- **The multiplication `𝒪_X(a) ⊗ 𝒪_X(b) ⟶ 𝒪_X(a+b)` of twists on the blowup is an
isomorphism**, in all integer degrees. The Rees algebra is generated in degree one over its
degree-zero part, which is what
`Stacks.AlgebraicGeometry.ProjRepresentsF1.isIso_twistMultiplicationMap_of_adjoin` asks for; no
file had instantiated that at `Stacks.Blowup.reesGrading`. -/
theorem isIso_twistMultiplicationMap_reesGrading (a b : ℤ) :
    IsIso (twistMultiplicationMap (reesGrading I) a b) :=
  Stacks.AlgebraicGeometry.ProjRepresentsF1.isIso_twistMultiplicationMap_of_adjoin
    (reesGrading I) (adjoin_reesGradingZero_reesGrading_one_eq_top I) a b

/-! ### Multiplication by a homogeneous element, on the twists of the Rees algebra -/

/-- **Multiplying by a homogeneous element of degree `d` shifts the twist index by `d`**: it
carries the degree-`i` piece of `S(t)` into the degree-`i` piece of `S(t+d)`, both being
degree-`i+t+d` pieces of `S`. Below the cut the source piece is zero, so no hypothesis on `i`
is needed. The target index is a parameter with an equation, so that `t + 1` can be asked for
where `t + ((1 : ℕ) : ℤ)` is produced. -/
theorem mul_mem_twistGrading_add (t : ℤ) {d : ℕ} {t' : ℤ} (hd : t + (d : ℤ) = t')
    {c : reesAlgebra I} (hc : c ∈ reesGrading I d) (i : ℤ) {x : reesAlgebra I}
    (hx : x ∈ ProjectiveSpectrum.Proj.twistGrading (S := reesAlgebra I) (reesGrading I) t i) :
    x * c ∈ ProjectiveSpectrum.Proj.twistGrading (S := reesAlgebra I) (reesGrading I) t' i := by
  subst hd
  rcases lt_or_ge (i + t) 0 with hi | hi
  · have hbot : ProjectiveSpectrum.Proj.twistGrading (S := reesAlgebra I)
        (reesGrading I) t i = ⊥ := by
      simp only [twistGrading_apply]
      exact integerGrading_neg (reesGrading I) (i + t) hi
    rw [hbot, Submodule.mem_bot] at hx
    rw [hx, zero_mul]
    exact zero_mem _
  · have hx' := (mem_twistGrading_iff I hi x).mp hx
    refine (mem_twistGrading_iff I (t := t + (d : ℤ)) (i := i) (by omega) _).mpr ?_
    rw [show (i + (t + (d : ℤ))).toNat = (i + t).toNat + d from by omega]
    exact SetLike.mul_mem_graded hx' hc

/-- **The degree-one element `b⁽¹⁾` lies in the truncation of `S(t+1)` above `-t`**: it is
homogeneous of degree `-t` there, since `-t + (t+1) = 1`, and `-t` is not below the cut. -/
theorem reesDegOne_mem_reesTruncation (t : ℤ) {b : A} (hb : b ∈ I) :
    (reesDegOne I hb : reesAlgebra I) ∈ reesTruncation I t := by
  refine mem_truncationAbove_of_mem (reesGrading I)
    (ProjectiveSpectrum.Proj.twistGrading (S := reesAlgebra I) (reesGrading I) (t + 1)) (-t)
    (le_refl (-t)) ?_
  refine (mem_twistGrading_iff I (t := t + 1) (i := -t) (by omega) _).mpr ?_
  rw [show (-t + (t + 1)).toNat = 1 from by omega]
  exact reesDegOne_mem_reesGrading I hb

/-- **Every multiple of `b⁽¹⁾` lies in the truncation.** The truncation is an `S`-submodule
containing `b⁽¹⁾`, and `b⁽¹⁾ * x` is `x • b⁽¹⁾`; no component of a general product has to be
computed. -/
theorem reesDegOne_mul_mem_reesTruncation (t : ℤ) {b : A} (hb : b ∈ I) (x : reesAlgebra I) :
    LinearMap.mul (reesAlgebra I) (reesAlgebra I) (reesDegOne I hb) x ∈ reesTruncation I t := by
  change (reesDegOne I hb : reesAlgebra I) * x ∈ reesTruncation I t
  rw [mul_comm]
  exact (reesTruncation I t).smul_mem x (reesDegOne_mem_reesTruncation I t hb)

/-- **Multiplication by `b⁽¹⁾`, read into the truncation of `S(t+1)` above `-t`.** Every
product with `b⁽¹⁾` has vanishing constant term, which is what membership in that truncation
amounts to; this is the factorisation that makes multiplication by `b⁽¹⁾` composable with
`Stacks.Blowup.reesShift`, which is defined on the truncation only. -/
def reesDegOneTrunc (t : ℤ) {b : A} (hb : b ∈ I) :
    reesAlgebra I →ₗ[reesAlgebra I] reesTruncation I t :=
  LinearMap.codRestrict (reesTruncation I t)
    (LinearMap.mul (reesAlgebra I) (reesAlgebra I) (reesDegOne I hb))
    (reesDegOne_mul_mem_reesTruncation I t hb)

/-- `reesDegOneTrunc` followed by the inclusion of the truncation is multiplication by `b⁽¹⁾`
on `S`; this is the only thing the restriction of the codomain changes. -/
theorem subtype_comp_reesDegOneTrunc (t : ℤ) {b : A} (hb : b ∈ I) :
    (reesTruncation I t).subtype ∘ₗ reesDegOneTrunc I t hb =
      LinearMap.mul (reesAlgebra I) (reesAlgebra I) (reesDegOne I hb) :=
  LinearMap.ext fun _ => rfl

/-- **`divX` undoes multiplication by `b⁽¹⁾` up to `b`**: `divX (b⁽¹⁾ · x) = b · x`, since
`b⁽¹⁾ = bX` and `divX` is linear on the truncation. This is the algebraic content of [Stacks,
Tag 02OS] part (3), on the whole of `S` rather than on a homogeneous piece. -/
theorem reesShift_comp_reesDegOneTrunc (t : ℤ) {b : A} (hb : b ∈ I) :
    (reesShift I t) ∘ₗ reesDegOneTrunc I t hb =
      LinearMap.mul (reesAlgebra I) (reesAlgebra I) (reesConst I b) := by
  refine LinearMap.ext fun x => Subtype.ext ?_
  change divX ((monomial 1 b : A[X]) * (x : A[X])) = (C b : A[X]) * (x : A[X])
  rw [mul_comm (monomial 1 b : A[X]), divX_mul_of_coeff_zero _ (by simp),
    divX_monomial_succ 0 b, monomial_zero_left, mul_comm]

/-- `reesDegOneTrunc` is degree-preserving, from the grading of `S(t)` to that of the
truncation of `S(t+1)`: membership in the latter is membership in the grading of `S(t+1)`, and
multiplying by a degree-one element raises the twist index by one. -/
theorem reesDegOneTrunc_mem_reesTruncationGrading (t : ℤ) {b : A} (hb : b ∈ I) (i : ℤ)
    (x : reesAlgebra I)
    (hx : x ∈ ProjectiveSpectrum.Proj.twistGrading (S := reesAlgebra I) (reesGrading I) t i) :
    reesDegOneTrunc I t hb x ∈ reesTruncationGrading I t i := by
  change (reesDegOne I hb : reesAlgebra I) * x ∈
      ProjectiveSpectrum.Proj.twistGrading (S := reesAlgebra I) (reesGrading I) (t + 1) i
  rw [mul_comm]
  exact mul_mem_twistGrading_add I t (d := 1) (by push_cast; ring)
    (reesDegOne_mem_reesGrading I hb) i hx

/-- The associated-sheaf morphism between twists depends on the linear map only, not on the
proof that it preserves degrees. -/
theorem associatedModuleSheafMap_rees_congr (n k : ℤ)
    (φ ψ : reesAlgebra I →ₗ[reesAlgebra I] reesAlgebra I)
    (hφ : ∀ (j : ℤ) (m : reesAlgebra I),
      m ∈ ProjectiveSpectrum.Proj.twistGrading (S := reesAlgebra I) (reesGrading I) n j →
        φ m ∈ ProjectiveSpectrum.Proj.twistGrading (S := reesAlgebra I) (reesGrading I) k j)
    (hψ : ∀ (j : ℤ) (m : reesAlgebra I),
      m ∈ ProjectiveSpectrum.Proj.twistGrading (S := reesAlgebra I) (reesGrading I) n j →
        ψ m ∈ ProjectiveSpectrum.Proj.twistGrading (S := reesAlgebra I) (reesGrading I) k j)
    (h : φ = ψ) :
    associatedModuleSheafMap (reesGrading I)
        (ProjectiveSpectrum.Proj.twistGrading (S := reesAlgebra I) (reesGrading I) n)
        (ProjectiveSpectrum.Proj.twistGrading (S := reesAlgebra I) (reesGrading I) k) φ hφ =
      associatedModuleSheafMap (reesGrading I)
        (ProjectiveSpectrum.Proj.twistGrading (S := reesAlgebra I) (reesGrading I) n)
        (ProjectiveSpectrum.Proj.twistGrading (S := reesAlgebra I) (reesGrading I) k) ψ hψ := by
  subst h
  rfl

/-- The degree bookkeeping of multiplication by a degree-one element: `1 + t = t + 1`. It is
not `rfl` for the integers, which is why
`Stacks.AlgebraicGeometry.ProjTwistedSections.twistScalarSheafMap` takes its target degree as a
parameter. -/
theorem reesTwistedDegree_one (t : ℤ) : ((1 : ℕ) : ℤ) + t = t + 1 := by push_cast; ring

/-! ### `twistShiftMap` against multiplication by a degree-one generator -/

/-- **Multiplication by `b⁽¹⁾` as a morphism `𝒪_X(t) ⟶ 𝒪_X(t+1)` factors through the
truncation**: it is the morphism `reesDegOneTrunc` induces, followed by the comparison
`(S₊(t+1))~ ≅ 𝒪_X(t+1)`. This is what lets it be composed with `Stacks.Blowup.twistShiftMap`
without inverting that comparison. -/
theorem twistScalarSheafMap_reesDegOne_eq (t : ℤ) {b : A} (hb : b ∈ I) :
    twistScalarSheafMap (reesGrading I) 1 t (t + 1) (reesTwistedDegree_one t)
        ⟨(reesDegOne I hb : reesAlgebra I), reesDegOne_mem_reesGrading I hb⟩ =
      associatedModuleSheafMap (reesGrading I)
          (ProjectiveSpectrum.Proj.twistGrading (S := reesAlgebra I) (reesGrading I) t)
          (reesTruncationGrading I t) (reesDegOneTrunc I t hb)
          (reesDegOneTrunc_mem_reesTruncationGrading I t hb) ≫
        (reesTruncationComparison I t).hom := by
  refine Eq.trans (associatedModuleSheafMap_rees_congr I t (t + 1) _
    ((reesTruncation I t).subtype ∘ₗ reesDegOneTrunc I t hb) _
    (fun j m hm => truncationAbove_subtype_mem (reesGrading I)
      (ProjectiveSpectrum.Proj.twistGrading (S := reesAlgebra I) (reesGrading I) (t + 1)) (-t) j
      _ (reesDegOneTrunc_mem_reesTruncationGrading I t hb j m hm))
    (subtype_comp_reesDegOneTrunc I t hb).symm) ?_
  exact associatedModuleSheafMap_comp (reesGrading I)
    (ProjectiveSpectrum.Proj.twistGrading (S := reesAlgebra I) (reesGrading I) t)
    (reesTruncationGrading I t)
    (ProjectiveSpectrum.Proj.twistGrading (S := reesAlgebra I) (reesGrading I) (t + 1))
    (reesDegOneTrunc I t hb) (reesDegOneTrunc_mem_reesTruncationGrading I t hb)
    (reesTruncation I t).subtype
    (truncationAbove_subtype_mem (reesGrading I)
      (ProjectiveSpectrum.Proj.twistGrading (S := reesAlgebra I) (reesGrading I) (t + 1)) (-t))

/-- **Multiplication by `b⁽¹⁾` followed by `twistShiftMap` is multiplication by `b`**, as
morphisms `𝒪_X(t) ⟶ 𝒪_X(t)`, for every `b ∈ I` and every `t : ℤ`.

This is [Stacks, Tag 02OS] part (3) at the level of morphisms of twisting sheaves: on the
standard open `D₊(b⁽¹⁾)`, where multiplication by `b⁽¹⁾` is invertible, it exhibits
`twistShiftMap` as that inverse followed by multiplication by `b`. -/
theorem twistScalarSheafMap_reesDegOne_comp_twistShiftMap (t : ℤ) {b : A} (hb : b ∈ I) :
    twistScalarSheafMap (reesGrading I) 1 t (t + 1) (reesTwistedDegree_one t)
          ⟨(reesDegOne I hb : reesAlgebra I), reesDegOne_mem_reesGrading I hb⟩ ≫
        twistShiftMap I t =
      twistScalarSheafMap (reesGrading I) 0 t t (twistedDegree_zero t)
        ⟨(reesConst I b : reesAlgebra I),
          SetLike.algebraMap_mem_graded (reesGrading I) b⟩ := by
  refine Eq.trans (congrArg
    (fun φ : twistingSheaf (reesGrading I) t ⟶ twistingSheaf (reesGrading I) (t + 1) =>
      φ ≫ twistShiftMap I t) (twistScalarSheafMap_reesDegOne_eq I t hb)) ?_
  refine Eq.trans (Category.assoc _ _ _) ?_
  refine Eq.trans (congrArg
    (fun φ : associatedModuleSheaf (reesGrading I) (reesTruncationGrading I t) ⟶
        twistingSheaf (reesGrading I) t =>
      associatedModuleSheafMap (reesGrading I)
          (ProjectiveSpectrum.Proj.twistGrading (S := reesAlgebra I) (reesGrading I) t)
          (reesTruncationGrading I t) (reesDegOneTrunc I t hb)
          (reesDegOneTrunc_mem_reesTruncationGrading I t hb) ≫ φ)
    (comparison_hom_comp_twistShiftMap I t)) ?_
  refine Eq.trans (associatedModuleSheafMap_comp (reesGrading I)
    (ProjectiveSpectrum.Proj.twistGrading (S := reesAlgebra I) (reesGrading I) t)
    (reesTruncationGrading I t)
    (ProjectiveSpectrum.Proj.twistGrading (S := reesAlgebra I) (reesGrading I) t)
    (reesDegOneTrunc I t hb) (reesDegOneTrunc_mem_reesTruncationGrading I t hb)
    (reesShift I t) (reesShift_mem_twistGrading I t)).symm ?_
  exact associatedModuleSheafMap_rees_congr I t t _ _ _ _ (reesShift_comp_reesDegOneTrunc I t hb)

/-- `associatedModuleSheafMap_rees_congr` with the truncation of `S(t+1)` as source: again the
morphism depends on the linear map only. -/
theorem associatedModuleSheafMap_trunc_congr (t : ℤ)
    (φ ψ : reesTruncation I t →ₗ[reesAlgebra I] reesAlgebra I)
    (hφ : ∀ (j : ℤ) (m : reesTruncation I t), m ∈ reesTruncationGrading I t j →
      φ m ∈ ProjectiveSpectrum.Proj.twistGrading (S := reesAlgebra I) (reesGrading I) (t + 1) j)
    (hψ : ∀ (j : ℤ) (m : reesTruncation I t), m ∈ reesTruncationGrading I t j →
      ψ m ∈ ProjectiveSpectrum.Proj.twistGrading (S := reesAlgebra I) (reesGrading I) (t + 1) j)
    (h : φ = ψ) :
    associatedModuleSheafMap (reesGrading I) (reesTruncationGrading I t)
        (ProjectiveSpectrum.Proj.twistGrading (S := reesAlgebra I) (reesGrading I) (t + 1))
        φ hφ =
      associatedModuleSheafMap (reesGrading I) (reesTruncationGrading I t)
        (ProjectiveSpectrum.Proj.twistGrading (S := reesAlgebra I) (reesGrading I) (t + 1))
        ψ hψ := by
  subst h
  rfl

/-- **Multiplication by `b⁽¹⁾` undoes `divX` up to `b`**, read on the truncation: for `m ∈ S₊`,
`b⁽¹⁾ · divX m = b · m`. This is `Stacks.Blowup.reesDegOne_mul_reesShift` as an equation of
linear maps. -/
theorem subtype_comp_reesDegOneTrunc_comp_reesShift (t : ℤ) {b : A} (hb : b ∈ I) :
    (reesTruncation I t).subtype ∘ₗ (reesDegOneTrunc I t hb ∘ₗ reesShift I t) =
      LinearMap.mul (reesAlgebra I) (reesAlgebra I) (reesConst I b) ∘ₗ
        (reesTruncation I t).subtype :=
  LinearMap.ext fun m => reesDegOne_mul_reesShift I t hb m

/-- **`twistShiftMap` followed by multiplication by `b⁽¹⁾` is multiplication by `b`**, as
morphisms `𝒪_X(t+1) ⟶ 𝒪_X(t+1)`, for every `b ∈ I` and every `t : ℤ`.

Together with `twistScalarSheafMap_reesDegOne_comp_twistShiftMap` this says the two morphisms
are inverse to one another up to multiplication by `b`, which is the content of [Stacks,
Tag 02OS] part (3) that a local argument consumes: wherever `b` is a nonzerodivisor on the
twists, `twistShiftMap` is a monomorphism. -/
theorem twistShiftMap_comp_twistScalarSheafMap_reesDegOne (t : ℤ) {b : A} (hb : b ∈ I) :
    twistShiftMap I t ≫ twistScalarSheafMap (reesGrading I) 1 t (t + 1)
          (reesTwistedDegree_one t)
          ⟨(reesDegOne I hb : reesAlgebra I), reesDegOne_mem_reesGrading I hb⟩ =
      twistScalarSheafMap (reesGrading I) 0 (t + 1) (t + 1) (twistedDegree_zero (t + 1))
        ⟨(reesConst I b : reesAlgebra I),
          SetLike.algebraMap_mem_graded (reesGrading I) b⟩ := by
  refine (Iso.cancel_iso_hom_left (reesTruncationComparison I t) _ _).mp ?_
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine Eq.trans (congrArg
    (fun φ : associatedModuleSheaf (reesGrading I) (reesTruncationGrading I t) ⟶
        twistingSheaf (reesGrading I) t =>
      φ ≫ twistScalarSheafMap (reesGrading I) 1 t (t + 1) (reesTwistedDegree_one t)
        ⟨(reesDegOne I hb : reesAlgebra I), reesDegOne_mem_reesGrading I hb⟩)
    (comparison_hom_comp_twistShiftMap I t)) ?_
  refine Eq.trans (congrArg
    (fun φ : twistingSheaf (reesGrading I) t ⟶ twistingSheaf (reesGrading I) (t + 1) =>
      associatedModuleSheafMap (reesGrading I) (reesTruncationGrading I t)
        (ProjectiveSpectrum.Proj.twistGrading (S := reesAlgebra I) (reesGrading I) t)
        (reesShift I t) (reesShift_mem_twistGrading I t) ≫ φ)
    (twistScalarSheafMap_reesDegOne_eq I t hb)) ?_
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine Eq.trans (congrArg
    (fun φ : associatedModuleSheaf (reesGrading I) (reesTruncationGrading I t) ⟶
        associatedModuleSheaf (reesGrading I) (reesTruncationGrading I t) =>
      φ ≫ (reesTruncationComparison I t).hom)
    (associatedModuleSheafMap_comp (reesGrading I) (reesTruncationGrading I t)
      (ProjectiveSpectrum.Proj.twistGrading (S := reesAlgebra I) (reesGrading I) t)
      (reesTruncationGrading I t) (reesShift I t) (reesShift_mem_twistGrading I t)
      (reesDegOneTrunc I t hb) (reesDegOneTrunc_mem_reesTruncationGrading I t hb)).symm) ?_
  refine Eq.trans (congrArg
    (fun φ : associatedModuleSheaf (reesGrading I) (reesTruncationGrading I t) ⟶
        twistingSheaf (reesGrading I) (t + 1) =>
      associatedModuleSheafMap (reesGrading I) (reesTruncationGrading I t)
        (reesTruncationGrading I t) (reesDegOneTrunc I t hb ∘ₗ reesShift I t)
        (fun j m hm => reesDegOneTrunc_mem_reesTruncationGrading I t hb j (reesShift I t m)
          (reesShift_mem_twistGrading I t j m hm)) ≫ φ)
    (reesTruncationComparison_hom I t)) ?_
  refine Eq.trans (associatedModuleSheafMap_comp (reesGrading I) (reesTruncationGrading I t)
    (reesTruncationGrading I t)
    (ProjectiveSpectrum.Proj.twistGrading (S := reesAlgebra I) (reesGrading I) (t + 1))
    (reesDegOneTrunc I t hb ∘ₗ reesShift I t)
    (fun j m hm => reesDegOneTrunc_mem_reesTruncationGrading I t hb j (reesShift I t m)
      (reesShift_mem_twistGrading I t j m hm))
    (reesTruncation I t).subtype
    (truncationAbove_subtype_mem (reesGrading I)
      (ProjectiveSpectrum.Proj.twistGrading (S := reesAlgebra I) (reesGrading I) (t + 1))
      (-t))).symm ?_
  refine Eq.trans (associatedModuleSheafMap_trunc_congr I t _
    (LinearMap.mul (reesAlgebra I) (reesAlgebra I) (reesConst I b) ∘ₗ
      (reesTruncation I t).subtype) _
    (fun j m hm => Stacks.AlgebraicGeometry.ProjTwistedSections.homogeneousMul_mem_twistGrading
      (reesGrading I) 0 (t + 1) (t + 1) (twistedDegree_zero (t + 1))
      ⟨(reesConst I b : reesAlgebra I), SetLike.algebraMap_mem_graded (reesGrading I) b⟩ j
      ((reesTruncation I t).subtype m)
      (truncationAbove_subtype_mem (reesGrading I)
        (ProjectiveSpectrum.Proj.twistGrading (S := reesAlgebra I) (reesGrading I) (t + 1))
        (-t) j m hm))
    (subtype_comp_reesDegOneTrunc_comp_reesShift I t hb)) ?_
  refine Eq.trans (associatedModuleSheafMap_comp (reesGrading I) (reesTruncationGrading I t)
    (ProjectiveSpectrum.Proj.twistGrading (S := reesAlgebra I) (reesGrading I) (t + 1))
    (ProjectiveSpectrum.Proj.twistGrading (S := reesAlgebra I) (reesGrading I) (t + 1))
    (reesTruncation I t).subtype
    (truncationAbove_subtype_mem (reesGrading I)
      (ProjectiveSpectrum.Proj.twistGrading (S := reesAlgebra I) (reesGrading I) (t + 1))
      (-t))
    (LinearMap.mul (reesAlgebra I) (reesAlgebra I) (reesConst I b))
    (Stacks.AlgebraicGeometry.ProjTwistedSections.homogeneousMul_mem_twistGrading
      (reesGrading I) 0 (t + 1) (t + 1) (twistedDegree_zero (t + 1))
      ⟨(reesConst I b : reesAlgebra I), SetLike.algebraMap_mem_graded (reesGrading I) b⟩)) ?_
  exact congrArg
    (fun φ : associatedModuleSheaf (reesGrading I) (reesTruncationGrading I t) ⟶
        twistingSheaf (reesGrading I) (t + 1) =>
      φ ≫ twistScalarSheafMap (reesGrading I) 0 (t + 1) (t + 1) (twistedDegree_zero (t + 1))
        ⟨(reesConst I b : reesAlgebra I), SetLike.algebraMap_mem_graded (reesGrading I) b⟩)
    (reesTruncationComparison_hom I t).symm

end Stacks.Blowup

end
