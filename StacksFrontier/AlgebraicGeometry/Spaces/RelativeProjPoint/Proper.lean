module

public import Mathlib.Tactic.TFAE
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.Finiteness
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjPoint.EtaleLocalConditions
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjPoint.FiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjPoint.Separated
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjPoint.UniversallyClosed

/-!
# The relative Proj of an algebraic space is proper under the finite type conditions

In Situation 0849 let `S` be a scheme, `X` an algebraic space over `S` and `𝒜` a quasi-coherent
graded `𝒪_X`-algebra, and let `π : Proj_X(𝒜) ⟶ X` be the relative homogeneous spectrum of
Stacks 084C, `AlgebraicGeometry.Space.RelativeProjSituation.π`. Stacks 084I says that the
conditions

1. `𝒜₀` is a finite type `𝒪_X`-module and `𝒜` is of finite type as an `𝒜₀`-algebra,
2. `𝒜₀` is a finite type `𝒪_X`-module and `𝒜` is of finite type as an `𝒪_X`-algebra

are equivalent, and that under them `π` is proper. This file proves both assertions for the
relative Proj itself.

## Main results

* `AlgebraicGeometry.Space.RelativeProjSituation.tfae_finiteType_and_isProper_π`:
  **Stacks 084I.**

## Implementation notes

**The conditions** are conditions on a quasi-coherent sheaf on an algebraic space, so they are
read étale locally: on the restriction `g^*𝒜` of Stacks 084B to every étale scheme point
`g : U ⟶ X` (`AlgebraicGeometry.Space.RelativeProjSituation.HoldsAtEtalePoints`), the reading
Stacks 084E, 084F, 084G and 084H use for theirs. On `g^*𝒜`:

* "`𝒜₀` is a finite type `𝒪_X`-module" is `SheafOfModules.IsFiniteType` of the degree-zero piece
  of `g^*𝒜`, which is `g^*𝒜₀`;
* "`𝒜` is of finite type as an `𝒜₀`-algebra" is
  `Stacks.AlgebraicGeometry.RelativeProjBridge.SheafGradedAlgebra.IsFiniteTypeOverDegreeZero`, the
  hypothesis of Stacks 084H;
* "`𝒜` is of finite type as an `𝒪_X`-algebra" is
  `Stacks.AlgebraicGeometry.RelativeProjFiniteType.IsFiniteType`, the hypothesis of Stacks 084G.

**The equivalence** is, at each étale point and over each affine open `U` of it, the
transitivity of finite type algebras along the tower `Γ(U, 𝒪) ⟶ Γ(U, 𝒜₀) ⟶ Γ(U, 𝒜)`: the first
step is finite because `𝒜₀` is a quasi-coherent module of finite type, so the composite is of
finite type when the second step is, and conversely a finite type composite makes the second step
of finite type.

**Properness** is separatedness, finite type and universal closedness together (Stacks 03ZM), and
the proof is the source's: each of the three reduces along a surjective étale chart to the case of
schemes. Separatedness is Stacks 084E, with no hypothesis on `𝒜`; finite type is Stacks 084G, fed
condition (2), which the equivalence supplies; universal closedness is Stacks 084H, fed the
integrality of `𝒪_X ⟶ 𝒜₀`, which follows from its finiteness (Stacks 00GK), and condition (1).

## References

* [Stacks Project, Tag 0849](https://stacks.math.columbia.edu/tag/0849)
* [Stacks Project, Tag 084B](https://stacks.math.columbia.edu/tag/084B)
* [Stacks Project, Tag 084C](https://stacks.math.columbia.edu/tag/084C)
* [Stacks Project, Tag 084E](https://stacks.math.columbia.edu/tag/084E)
* [Stacks Project, Tag 084G](https://stacks.math.columbia.edu/tag/084G)
* [Stacks Project, Tag 084H](https://stacks.math.columbia.edu/tag/084H)
* [Stacks Project, Tag 084I](https://stacks.math.columbia.edu/tag/084I)
* [Stacks Project, Tag 03ZM](https://stacks.math.columbia.edu/tag/03ZM)
* [Stacks Project, Tag 00GK](https://stacks.math.columbia.edu/tag/00GK)
-/

@[expose] public section

universe u m

open CategoryTheory AlgebraicGeometry
open Stacks.AlgebraicGeometry.RelativeProjBridge

namespace AlgebraicGeometry.Space.RelativeProjSituation

/-! ### The case of schemes, over an affine open -/

section SchemeCase

variable {T : Scheme.{u}} (A : SheafGradedAlgebra T)

/-- **The structure map lands in degree zero.** The map from the functions on an open to the
graded ring of sections factors through the degree-zero part, which makes
`Γ(U, 𝒪) ⟶ Γ(U, 𝒜)₀ ⟶ Γ(U, 𝒜)` a tower. -/
private theorem algebraMap_comp_degreeZero (U : T.Opens) :
    (algebraMap (A.grading U 0) (A.sectionRing U)).comp
        ((GradedRing.projZeroRingHom' (A.grading U)).comp (A.strHom U)) = A.strHom U := by
  refine RingHom.ext fun r => ?_
  show ((GradedRing.projZeroRingHom' (A.grading U) (A.strHom U r) : A.grading U 0) :
    A.sectionRing U) = A.strHom U r
  exact congrArg Subtype.val
    (GradedRing.projZeroRingHom'_apply_coe (A.grading U) ⟨_, A.strHom_mem U r⟩)

/-- **A finite type degree-zero piece is finite over the functions on every affine open.** The
sections of the quasi-coherent finite type module `𝒜₀` over an affine open `U` are a finite
`Γ(U, 𝒪)`-module, and they map onto the degree-zero part of the graded ring of sections,
`Γ(U, 𝒪)`-linearly. -/
private theorem finite_degreeZero (h : SheafOfModules.IsFiniteType (A.piece 0)) (U : T.Opens)
    (hU : IsAffineOpen U) :
    ((GradedRing.projZeroRingHom' (A.grading U)).comp (A.strHom U)).Finite := by
  let _ : (A.piece 0).IsFiniteType := h
  have hF : Module.Finite Γ(T, U) Γ(A.piece 0, U) := moduleFinite_sections_on_affine _ U hU
  let φ : Γ(T, U) →+* A.grading U 0 :=
    (GradedRing.projZeroRingHom' (A.grading U)).comp (A.strHom U)
  let _ : Algebra Γ(T, U) (A.grading U 0) := φ.toAlgebra
  have hcoe (r : Γ(T, U)) : ((φ r : A.grading U 0) : A.sectionRing U) = A.strHom U r :=
    congrArg Subtype.val
      (GradedRing.projZeroRingHom'_apply_coe (A.grading U) ⟨_, A.strHom_mem U r⟩)
  let z : Γ(A.piece 0, U) →ₗ[Γ(T, U)] A.grading U 0 :=
    { toFun := fun x => ⟨DirectSum.of (A.sectionPieces U) 0 x, A.of_mem_grading U x⟩
      map_add' := fun x y => Subtype.ext ((DirectSum.of (A.sectionPieces U) 0).map_add x y)
      map_smul' := fun r x => by
        refine Subtype.ext ?_
        rw [Algebra.smul_def]
        show DirectSum.of (A.sectionPieces U) 0 (r • x) =
          ((φ r : A.grading U 0) : A.sectionRing U) * DirectSum.of (A.sectionPieces U) 0 x
        rw [hcoe r]
        exact (A.strHom_mul_of U r x).symm }
  have hz : Function.Surjective z := by
    rintro ⟨y, x, rfl⟩
    exact ⟨x, rfl⟩
  exact Module.Finite.of_surjective z hz

/-- **Condition (1) gives condition (2) on a scheme.** If `𝒜₀` is of finite type and `𝒜` is of
finite type over `𝒜₀`, then `𝒜` is of finite type over `𝒪`: over every affine open this is
`RingHom.FiniteType.comp` along the tower. -/
private theorem isFiniteType_of_finiteTypeOverDegreeZero
    (h : SheafOfModules.IsFiniteType (A.piece 0)) (hdeg : A.IsFiniteTypeOverDegreeZero) :
    Stacks.AlgebraicGeometry.RelativeProjFiniteType.IsFiniteType A := by
  refine (SheafGradedAlgebra.isFiniteType_iff_onAffines A).2 fun U hU => ?_
  have hcomp := RingHom.FiniteType.comp (RingHom.finiteType_algebraMap.mpr (hdeg U hU))
    (finite_degreeZero A h U hU).finiteType
  rwa [algebraMap_comp_degreeZero] at hcomp

/-- **Condition (2) gives condition (1) on a scheme.** If `𝒜` is of finite type over `𝒪`, it is
of finite type over `𝒜₀`: over every affine open this is `RingHom.FiniteType.of_comp_finiteType`
along the tower. -/
private theorem finiteTypeOverDegreeZero_of_isFiniteType
    (h : Stacks.AlgebraicGeometry.RelativeProjFiniteType.IsFiniteType A) :
    A.IsFiniteTypeOverDegreeZero := by
  intro U hU
  have hft : (A.strHom U).FiniteType := (SheafGradedAlgebra.isFiniteType_iff_onAffines A).1 h U hU
  rw [← algebraMap_comp_degreeZero A U] at hft
  exact RingHom.finiteType_algebraMap.mp (RingHom.FiniteType.of_comp_finiteType hft)

end SchemeCase

/-! ### Stacks 084I -/

variable (s : RelativeProjSituation.{u, m})

/-- **Stacks 084I.** In Situation 0849 — `X` an algebraic space over a scheme `S` and `𝒜` a
quasi-coherent graded `𝒪_X`-algebra — the following conditions are equivalent:

1. `𝒜₀` is a finite type `𝒪_X`-module and `𝒜` is of finite type as an `𝒜₀`-algebra,
2. `𝒜₀` is a finite type `𝒪_X`-module and `𝒜` is of finite type as an `𝒪_X`-algebra;

and if they hold, the structure morphism `π : Proj_X(𝒜) ⟶ X` of the relative homogeneous
spectrum of Stacks 084C is proper.

The conditions are read étale locally, on the restriction `g^*𝒜` of Stacks 084B to every étale
scheme point `g` of `X`, as for Stacks 084G and 084H: `𝒜₀` of finite type is
`SheafOfModules.IsFiniteType` of the degree-zero piece of `g^*𝒜`, and the two algebra conditions
are the hypotheses of Stacks 084H and 084G. -/
@[stacks 084I]
theorem tfae_finiteType_and_isProper_π :
    List.TFAE
        [s.HoldsAtEtalePoints (fun A => SheafOfModules.IsFiniteType (A.piece 0)) ∧
            s.HoldsAtEtalePoints SheafGradedAlgebra.IsFiniteTypeOverDegreeZero,
          s.HoldsAtEtalePoints (fun A => SheafOfModules.IsFiniteType (A.piece 0)) ∧
            s.HoldsAtEtalePoints Stacks.AlgebraicGeometry.RelativeProjFiniteType.IsFiniteType] ∧
      (s.HoldsAtEtalePoints (fun A => SheafOfModules.IsFiniteType (A.piece 0)) ∧
          s.HoldsAtEtalePoints SheafGradedAlgebra.IsFiniteTypeOverDegreeZero →
        IsProper s.site s.base s.containsBase s.π.hom) := by
  refine ⟨?_, fun ⟨hzero, hdeg⟩ => ?_⟩
  · tfae_have 1 → 2 := fun ⟨hzero, hdeg⟩ =>
      ⟨hzero, fun V g hg => isFiniteType_of_finiteTypeOverDegreeZero _ (hzero V g hg)
        (hdeg V g hg)⟩
    tfae_have 2 → 1 := fun ⟨hzero, hft⟩ =>
      ⟨hzero, fun V g hg => finiteTypeOverDegreeZero_of_isFiniteType _ (hft V g hg)⟩
    tfae_finish
  · have hft : s.HoldsAtEtalePoints Stacks.AlgebraicGeometry.RelativeProjFiniteType.IsFiniteType :=
      fun V g hg => isFiniteType_of_finiteTypeOverDegreeZero _ (hzero V g hg) (hdeg V g hg)
    have hint : s.HoldsAtEtalePoints SheafGradedAlgebra.IsIntegralInDegreeZero :=
      fun V g hg U hU => (finite_degreeZero _ (hzero V g hg) U hU).to_isIntegral
    refine ⟨?_, s.isFiniteType_π hft, s.universallyClosed_π hint hdeg⟩
    rw [s.π_hom]
    exact s.isSeparated_relativeProjπ

end AlgebraicGeometry.Space.RelativeProjSituation

end
