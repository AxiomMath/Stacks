module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Surfaces.ExceptionalCurveDegreeOneGeneration
public import StacksFrontier.AlgebraicGeometry.Surfaces.ExceptionalCurveTwistMultiplicative
public import StacksFrontier.AlgebraicGeometry.Surfaces.GradedSectionsLocal

/-!
# Stacks 0C2K, unconditionally

Let `X` be a Noetherian scheme and let `E ⊆ X` be an exceptional curve of the first kind, cut out
by an ideal sheaf `D` and presented as the projective line by an isomorphism `e : 𝐏¹_k ≅ E`. Write
`A = lim H⁰(Eₙ, 𝒪ₙ)` for the ring of compatible global functions on the infinitesimal thickenings
of `E`. **Stacks 0C2K** asserts that `A` is a complete Noetherian regular local ring of dimension
`2` and that the kernel of `A ⟶ H⁰(Eₙ, 𝒪ₙ)` is the `n`-th power of its maximal ideal.

This file discharges the last input those four conclusions were waiting on, and so states them
with no hypothesis beyond the exceptional curve itself.

## The last input

`AlgebraicGeometry.Scheme.IdealSheafData.ExceptionalMonomialData`
`.ofGradedSectionsDegreeOneGeneration`
reduces the five geometric inputs of
`AlgebraicGeometry.Scheme.IdealSheafData.ExceptionalMonomialData` to degree-one generation of the
symbols: every global section of `𝒪_X(-D ^ (p + 2))|_E` is a finite sum of members of
`AlgebraicGeometry.Scheme.IdealSheafData.gradedSectionsDegreeOneProducts`. That is now proved,
in two steps.

* On the sections of the twists themselves, degree-one generation is
  `AlgebraicGeometry.Scheme.IdealSheafData.IsExceptionalCurveOfFirstKind`
  `.mem_closure_restrictedIdealMulSections`: every global section of `𝒪_X(-(D · D ^ n))|_E` is a
  finite sum of restricted products `Stacks.Divisors.restrictedIdealMulSections a b`.
* The restricted products are symbols of degree-one products, by
  `AlgebraicGeometry.Scheme.IdealSheafData`
  `.mem_gradedSectionsDegreeOneProducts_of_gradedSectionsHom_eq`.

The two speak of the same ideal sheaf under two names — `D · D ^ (p + 1)` and `D ^ (p + 2)` — so
one transport along an equality of ideal sheaves appears, `castSections`, confined to this file
and to the proof of `mem_closure_gradedSectionsDegreeOneProducts`; the symbol it has to commute
with is `AlgebraicGeometry.Scheme.IdealSheafData.gradedSectionsHomOfEq`, whose divisor is a free
variable for exactly this reason.

## What the four conclusions now need

The exceptional-curve hypothesis, and nothing else. It is used: the bundle
`ExceptionalMonomialData D` is built from it. The Noetherian hypothesis on `X` is the one
[Stacks, Tag 0C2K] states and is kept, although the reduction in
`StacksFrontier/AlgebraicGeometry/Surfaces/FormalNeighborhoodReduction.lean` does not use it — the
Noetherianity of `A` comes from the monomial filtration, not from `X`.

## Main definitions

* `AlgebraicGeometry.Scheme.IdealSheafData.ExceptionalMonomialData`
  `.ofIsExceptionalCurveOfFirstKind` — **the five geometric inputs of [Stacks, Tag 0C2K] from the
  exceptional curve alone.** In particular `ExceptionalMonomialData D` is inhabited whenever `D`
  is an exceptional curve of the first kind.

## Main results

* `AlgebraicGeometry.Scheme.IdealSheafData.IsExceptionalCurveOfFirstKind`
  `.mem_closure_gradedSectionsDegreeOneProducts` — degree-one generation of the symbols.
* `AlgebraicGeometry.Scheme.IdealSheafData`
  `.isNoetherianCompleteLocalRing_formalNeighborhoodRing_of_monomialData`,
  `isRegularLocalRing_formalNeighborhoodRing_of_monomialData`,
  `ringKrullDim_formalNeighborhoodRing_eq_two_of_monomialData` and
  `ker_formalNeighborhoodProjection_eq_maximalIdeal_pow_of_monomialData` — **the four conclusions
  of [Stacks, Tag 0C2K].**

## References

* [Stacks Project, Tag 0C2K](https://stacks.math.columbia.edu/tag/0C2K)
-/

@[expose] public noncomputable section

open CategoryTheory
open Stacks.Divisors

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {X : Scheme.{u}} (D : X.IdealSheafData)

/-! ### Transport along an equality of ideal sheaves -/

/-- Global sections of the restricted negative twist, transported along an equality of ideal
sheaves. Two equal ideal sheaves that are not the same term cut out different terms, so their
restricted twists are different terms with the same sections. -/
def castSections {I J : X.IdealSheafData} (h : I = J) :
    Γ((Scheme.Modules.pullback D.subschemeι).obj (negativeTwist I),
        (⊤ : D.subscheme.Opens)) ≃+
      Γ((Scheme.Modules.pullback D.subschemeι).obj (negativeTwist J),
        (⊤ : D.subscheme.Opens)) := by
  subst h; exact AddEquiv.refl _

/-- The transport along an equality of an ideal sheaf with itself is the identity: proofs are
irrelevant, so such an equality is `rfl` and the transport is `AddEquiv.refl`. -/
theorem castSections_rfl {I : X.IdealSheafData} (h : I = I)
    (y : Γ((Scheme.Modules.pullback D.subschemeι).obj (negativeTwist I),
      (⊤ : D.subscheme.Opens))) :
    castSections D h y = y := rfl

/-- **The transport commutes with the 0C4T symbol.** The symbol in the free-variable shape
`AlgebraicGeometry.Scheme.IdealSheafData.gradedSectionsHomOfEq` at a divisor `J` equal to
`D ^ (N + 1)` agrees with `AlgebraicGeometry.Scheme.IdealSheafData.gradedSectionsHom` at `N`,
read through the transport. -/
theorem gradedSectionsHom_castSections [IsEffectiveCartierDivisor D] {J : X.IdealSheafData}
    [IsEffectiveCartierDivisor J] {N : ℕ} (hJ : J = D ^ (N + 1))
    (h : D * J = D ^ (N + 1 + 1))
    (y : Γ((Scheme.Modules.pullback D.subschemeι).obj (negativeTwist J),
      (⊤ : D.subscheme.Opens))) :
    gradedSectionsHom D N (castSections D hJ y) = gradedSectionsHomOfEq D J h y := by
  subst hJ
  rw [castSections_rfl]
  exact (gradedSectionsHomOfEq_pow D N y).symm

/-- **A transported restricted product is a symbol of a degree-one product.** The product
`Stacks.Divisors.restrictedIdealMulSections a b` lives at the divisor `D · D ^ (p + 1)`, read
along `h` at `D ^ (p + 2)`; its symbol is the symbol of the restricted product by
`AlgebraicGeometry.Scheme.IdealSheafData.gradedSectionsHom_castSections`, which is what
membership in
`AlgebraicGeometry.Scheme.IdealSheafData.gradedSectionsDegreeOneProducts` asks for. -/
theorem castSections_restrictedIdealMulSections_mem [IsEffectiveCartierDivisor D] {p : ℕ}
    (h : D ^ 1 * D ^ (p + 1) = D ^ (p + 1 + 1))
    (a : Γ((Scheme.Modules.pullback D.subschemeι).obj (negativeTwist (D ^ 1)),
      (⊤ : D.subscheme.Opens)))
    (b : Γ((Scheme.Modules.pullback D.subschemeι).obj (negativeTwist (D ^ (p + 1))),
      (⊤ : D.subscheme.Opens))) :
    castSections D h
        (restrictedIdealMulSections D (D ^ 1) (D ^ (p + 1)) inferInstance a b) ∈
      gradedSectionsDegreeOneProducts D p :=
  mem_gradedSectionsDegreeOneProducts_of_gradedSectionsHom_eq D a b _
    (gradedSectionsHom_castSections D h (self_mul_pow_one_mul_pow_succ D p) _)

namespace IsExceptionalCurveOfFirstKind

variable {k : Type u} [Field k] {e : projectiveLineProj k ≅ D.subscheme}

/-! ### Degree-one generation of the symbols -/

/-- **Degree-one generation of the twisted sections, read at a divisor named by an equation and
against an arbitrary set of generators.**

`AlgebraicGeometry.Scheme.IdealSheafData.IsExceptionalCurveOfFirstKind`
`.mem_closure_restrictedIdealMulSections` with the divisor `D · D ^ n` replaced by a free
variable `J` and an equation, and the generating set replaced by any set whose generated subgroup
contains the transported restricted products. Taking the set as an argument is what keeps the
two sections types — the one at `D · D ^ n` and the one at `J` — out of the same statement:
inside the proof the equation is substituted away first, and the set is opaque. -/
theorem mem_closure_of_castSections_restrictedIdealMulSections_mem
    [IsEffectiveCartierDivisor D] (hE : IsExceptionalCurveOfFirstKind D k e) (n : ℕ)
    {J : X.IdealSheafData} (hJ : D ^ 1 * D ^ n = J)
    (T : Set Γ((Scheme.Modules.pullback D.subschemeι).obj (negativeTwist J),
      (⊤ : D.subscheme.Opens)))
    (hT : ∀ a b, castSections D hJ
      (restrictedIdealMulSections D (D ^ 1) (D ^ n) inferInstance a b) ∈
        AddSubgroup.closure T)
    (x : Γ((Scheme.Modules.pullback D.subschemeι).obj (negativeTwist J),
      (⊤ : D.subscheme.Opens))) :
    x ∈ AddSubgroup.closure T := by
  subst hJ
  refine (AddSubgroup.closure_le _).2 ?_ (hE.mem_closure_restrictedIdealMulSections n x)
  rintro z ⟨a, b, rfl⟩
  exact hT a b

/-- **Degree-one generation of the symbols on an exceptional curve of the first kind.** Every
global section of `𝒪_X(-D ^ (p + 2))|_E` is a finite sum of symbols of degree-one products.

This is the input `AlgebraicGeometry.Scheme.IdealSheafData.ExceptionalMonomialData`
`.ofGradedSectionsDegreeOneGeneration` asks for, and the last one [Stacks, Tag 0C2K] was waiting
on. Degree-one generation of the sections of the twists is
`AlgebraicGeometry.Scheme.IdealSheafData.IsExceptionalCurveOfFirstKind`
`.mem_closure_restrictedIdealMulSections`; that each transported restricted product is a symbol
of a degree-one product is
`AlgebraicGeometry.Scheme.IdealSheafData.castSections_restrictedIdealMulSections_mem`. -/
theorem mem_closure_gradedSectionsDegreeOneProducts [IsEffectiveCartierDivisor D]
    (hE : IsExceptionalCurveOfFirstKind D k e) (p : ℕ)
    (x : Γ((Scheme.Modules.pullback D.subschemeι).obj (negativeTwist (D ^ (p + 1 + 1))),
      (⊤ : D.subscheme.Opens))) :
    x ∈ AddSubgroup.closure (gradedSectionsDegreeOneProducts D p) := by
  have h : D ^ 1 * D ^ (p + 1) = D ^ (p + 1 + 1) :=
    Eq.trans (pow_add D 1 (p + 1)).symm
      (congrArg (fun i => D ^ i) (show 1 + (p + 1) = p + 1 + 1 by omega))
  refine mem_closure_of_castSections_restrictedIdealMulSections_mem D hE (p + 1)
    (J := D ^ (p + 1 + 1)) h (gradedSectionsDegreeOneProducts D p) ?_ x
  intro a b
  exact AddSubgroup.subset_closure (castSections_restrictedIdealMulSections_mem D h a b)

end IsExceptionalCurveOfFirstKind

namespace ExceptionalMonomialData

/-- **The five geometric inputs of [Stacks, Tag 0C2K] from the exceptional curve alone.**

Degree-one generation of the symbols is
`AlgebraicGeometry.Scheme.IdealSheafData.IsExceptionalCurveOfFirstKind`
`.mem_closure_gradedSectionsDegreeOneProducts`, and it was the last input
`AlgebraicGeometry.Scheme.IdealSheafData.ExceptionalMonomialData`
`.ofGradedSectionsDegreeOneGeneration` was carrying.

In particular `ExceptionalMonomialData D` is inhabited for every exceptional curve of the first
kind, so the conclusions read off it are not vacuous. -/
def ofIsExceptionalCurveOfFirstKind {D : X.IdealSheafData} (k : Type u) [Field k]
    {e : projectiveLineProj k ≅ D.subscheme} (hE : IsExceptionalCurveOfFirstKind D k e) :
    ExceptionalMonomialData D :=
  haveI : IsEffectiveCartierDivisor D := hE.isEffectiveCartierDivisor
  ofGradedSectionsDegreeOneGeneration hE hE.mem_closure_gradedSectionsDegreeOneProducts

end ExceptionalMonomialData

variable (k : Type u) [Field k] {e : projectiveLineProj k ≅ D.subscheme}

/-- **Stacks 0C2K, the complete Noetherian local clause.** For an exceptional curve of the first
kind on a Noetherian scheme, the ring of compatible global functions on the infinitesimal
thickenings is a Noetherian complete local ring. -/
@[stacks 0C2K "the complete Noetherian local clause, unconditionally"]
public theorem isNoetherianCompleteLocalRing_formalNeighborhoodRing_of_monomialData [IsNoetherian X]
    (hE : IsExceptionalCurveOfFirstKind D k e) :
    IsNoetherianCompleteLocalRing (formalNeighborhoodRing D) :=
  formalNeighborhoodRing_isNoetherianCompleteLocalRing D
    (ExceptionalMonomialData.ofIsExceptionalCurveOfFirstKind k hE).monomialFiltration

/-- **Stacks 0C2K, the regularity clause.** -/
@[stacks 0C2K "the regularity clause, unconditionally"]
public theorem isRegularLocalRing_formalNeighborhoodRing_of_monomialData [IsNoetherian X]
    (hE : IsExceptionalCurveOfFirstKind D k e) :
    IsRegularLocalRing (formalNeighborhoodRing D) :=
  formalNeighborhoodRing_isRegularLocalRing D
    (ExceptionalMonomialData.ofIsExceptionalCurveOfFirstKind k hE).monomialFiltration

/-- **Stacks 0C2K, the dimension clause.** -/
@[stacks 0C2K "the dimension clause, unconditionally"]
public theorem ringKrullDim_formalNeighborhoodRing_eq_two_of_monomialData [IsNoetherian X]
    (hE : IsExceptionalCurveOfFirstKind D k e) :
    ringKrullDim (formalNeighborhoodRing D) = 2 :=
  formalNeighborhoodRing_ringKrullDim D
    (ExceptionalMonomialData.ofIsExceptionalCurveOfFirstKind k hE).monomialFiltration

/-- **Stacks 0C2K, the projection-kernel clause.** The kernel of the projection to the
`(n + 1)`-st thickening is the `(n + 1)`-st power of the maximal ideal. -/
@[stacks 0C2K "the projection-kernel clause, unconditionally"]
public theorem ker_formalNeighborhoodProjection_eq_maximalIdeal_pow_of_monomialData
    [IsNoetherian X] (hE : IsExceptionalCurveOfFirstKind D k e) (n : ℕ) :
    letI : IsLocalRing (formalNeighborhoodRing D) :=
      (ExceptionalMonomialData.ofIsExceptionalCurveOfFirstKind k hE).monomialFiltration.isLocalRing
    RingHom.ker (formalNeighborhoodProjection D n) =
      IsLocalRing.maximalIdeal (formalNeighborhoodRing D) ^ (n + 1) :=
  ker_formalNeighborhoodProjection_eq_maximalIdeal_pow D
    (ExceptionalMonomialData.ofIsExceptionalCurveOfFirstKind k hE).monomialFiltration
    (ExceptionalMonomialData.ofIsExceptionalCurveOfFirstKind k hE).monomialFiltration_ideal n

end AlgebraicGeometry.Scheme.IdealSheafData

end
