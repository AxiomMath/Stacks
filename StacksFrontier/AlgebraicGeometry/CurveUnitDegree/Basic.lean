module

public import StacksFrontier.AlgebraicGeometry.AmpleCurve.Basic
public import StacksFrontier.AlgebraicGeometry.ClosedCoverGlue.Sections
public import StacksFrontier.AlgebraicGeometry.NormAmple.Nonvanishing
public import StacksFrontier.AlgebraicGeometry.NormInvertible.TensorPowerGenerator
public import StacksFrontier.AlgebraicGeometry.ProjectiveCurve.Basic
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.Degree

/-!
# The structure sheaf is never ample on a proper curve, and Tag 0B5X at the projective line

[Stacks, Tag 0B5X] says that an invertible module on a proper curve over a field is ample exactly
when its degree is positive. The assembly of both directions is
`AlgebraicGeometry.isAmple_iff_degree_pos`, and it carries five hypotheses the library does not
have. This file proves the biconditional **unconditionally** at one object and one invertible
module — the projective line over a field and its structure sheaf — by establishing each side
separately and finding both false.

The negative side is the content. On a proper curve the ring of global functions is a field
(`AlgebraicGeometry.isField_of_universallyClosed`, which needs only integrality and universal
closedness), so a global function is zero or a unit, and the tensor powers of the structure sheaf
carry a *global* frame built from the unit section
(`Stacks.SheafOfModules.tensorPowerGenerator`). Reading a global section of such a power off that
frame (`Stacks.SheafOfModules.mem_nonvanishingLocus_iff_isUnit_ringGerm`) shows its nonvanishing
locus is empty or everything. Ampleness asks for a nonvanishing locus that is nonempty and
affine, and on a proper curve an affine open is a proper subset
(`AlgebraicGeometry.IsAffineOpen.ne_top_of_isCurve`, since a proper curve is not affine) — so no
section of any power can serve, and the structure sheaf is not ample.

The positive side is `AlgebraicGeometry.invertibleCurveDegree_unit_eq_zero`: the degree of the
structure sheaf is zero, hence not positive. Zero is also the only value of
`AlgebraicGeometry.invertibleCurveDegree` previously computed anywhere in this development, and
the only previous computation
(`AlgebraicGeometry.invertibleCurveDegree_eq_zero_of_discreteTopology`) is on a scheme with the
discrete topology, where no curve hypothesis holds; the statements below are the first instances
of the degree at an object that *is* a proper curve.

## Main results

The elided prefix throughout is `AlgebraicGeometry`.

* `nonvanishingLocus_tensorPower_unit_eq_empty_or_univ`: on an integral scheme universally closed
  over a field, every global section of every tensor power of the structure sheaf has
  nonvanishing locus `∅` or `Set.univ`.
* `not_isAmple_unit_of_isCurve`: **the structure sheaf of a proper curve over a field is not
  ample.**
* `topologicalKrullDim_le_one_projectiveSpaceOver_one` and
  `invertibleCurveDegree_unit_projectiveSpaceOver_one_eq_zero`: the dimension bound that
  `invertibleCurveDegree` takes as an argument, and the degree of the structure sheaf, at
  `ℙ¹_k`.
* `not_isAmple_unit_projectiveSpaceOver_one`: the structure sheaf of `ℙ¹_k` is not ample.
* `isAmple_unit_iff_invertibleCurveDegree_pos_projectiveSpaceOver_one`: **the biconditional of
  [Stacks, Tag 0B5X], with no hypotheses, at `ℙ¹_k` and its structure sheaf.**

## Implementation notes

**No `@[stacks]` attribute is attached to anything here.** Tag 0B5X is the biconditional for an
arbitrary invertible module on an arbitrary proper curve; the last result below is that statement
at one object and one module, which is an instance of the tag and not the tag. Tag 01PS is the
definition of ampleness and is carried by `AlgebraicGeometry.Scheme.Modules.IsAmple`; Tag 0AYR is
the definition of the degree and is carried by `AlgebraicGeometry.invertibleCurveDegree`. By the
covering-set rule none of these belongs on a specialization.

**The hypothesis of the first result is weaker than a curve.** It asks for `IsIntegral X` and
`UniversallyClosed f` only, which is what `AlgebraicGeometry.isField_of_universallyClosed` needs;
neither finite type nor separatedness nor the dimension enters. The dimension is used only by
`not_isAmple_unit_of_isCurve`, and only through non-affineness of a proper curve.

**Two spellings of the structure sheaf as a module occur and both are needed.**
`AlgebraicGeometry.Scheme.Modules.IsAmple` and the nonvanishing locus are stated at
`SheafOfModules.unit (structureSheafRing
  X.toRingedSpace)`, while
`AlgebraicGeometry.invertibleCurveDegree` is stated at `SheafOfModules.unit X.ringCatSheaf`. The
two are equal by `rfl` but are different inputs to instance search, so the ampleness statements
below use the first and the degree statements the second, and the biconditional — which needs one
module in both slots — is written at the second with the invertibility witness supplied
explicitly.

**The nonvanishing locus is computed from a frame, not from an isomorphism
`𝒪_X^{⊗ n} ≅ 𝒪_X`.** No such isomorphism exists in either tree for general `n`
(`Stacks.SheafOfModules.tensorPowerOneIso` covers `n = 1` and
`Stacks.SheafOfModules.tensorPowerZeroIso` covers `n = 0`), and none is needed:
`Stacks.SheafOfModules.tensorPowerGenerator` propagates the unit section up the tower of powers
as a generator over `⊤`, which is all the frame calculus asks for.

## References

* [Stacks Project, Tag 0B5X](https://stacks.math.columbia.edu/tag/0B5X)
* [Stacks Project, Tag 01PS](https://stacks.math.columbia.edu/tag/01PS)
* [Stacks Project, Tag 01CY](https://stacks.math.columbia.edu/tag/01CY)
* [Stacks Project, Tag 0AYR](https://stacks.math.columbia.edu/tag/0AYR)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TopologicalSpace
open Stacks.SheafOfModules.TensorStalkRingedSpace (ringGerm)
open Stacks.SheafOfModules (nonvanishingLocus GeneratorSections
  generatorSectionsOfNonvanishing unitSections nonvanishingLocus_unitSections
  tensorPowerGenerator mem_nonvanishingLocus_iff_isUnit_ringGerm generator_restrict_self)
open Stacks.SheafOfModules.Invertible (tensorPower)

universe u

namespace AlgebraicGeometry

variable (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

/-- The structure sheaf of a scheme as a module over itself, at the spelling that
`AlgebraicGeometry.Scheme.Modules.IsAmple` and the nonvanishing locus use. -/
public abbrev unitModules (X : Scheme.{u}) : X.Modules :=
  SheafOfModules.unit (structureSheafRing X.toRingedSpace)

/-- The unit section, as a generator of the structure sheaf over the whole space. It vanishes
nowhere (`Stacks.SheafOfModules.nonvanishingLocus_unitSections`), and a global section vanishing
nowhere generates over every open. -/
public def unitGeneratorTop (X : Scheme.{u}) :
    GeneratorSections X.toRingedSpace (unitModules X) ⊤ :=
  generatorSectionsOfNonvanishing (unitModules X) (unitSections X.toRingedSpace)
    (fun x => (nonvanishingLocus_unitSections X.toRingedSpace).ge (Set.mem_univ x)) ⊤

/-- The frame of the `n`-th tensor power of the structure sheaf over the whole space, obtained
from `AlgebraicGeometry.unitGeneratorTop` by `Stacks.SheafOfModules.tensorPowerGenerator`. -/
public def unitTensorPowerGeneratorTop (X : Scheme.{u}) (n : ℕ) :
    GeneratorSections X.toRingedSpace
      (tensorPower X.toRingedSpace.presheaf
        (structureSheafRing X.toRingedSpace).property (unitModules X) (n : ℤ)) ⊤ :=
  tensorPowerGenerator (unitModules X) (unitGeneratorTop X) n

/-- **On a scheme integral and universally closed over a field, a global section of a tensor
power of the structure sheaf vanishes nowhere or everywhere.** The ring of global functions is a
field, so the coefficient of the section against the global frame
`AlgebraicGeometry.unitTensorPowerGeneratorTop` is zero or a unit; in the first case its germ is
zero at every point and in the second a unit at every point. -/
public theorem nonvanishingLocus_tensorPower_unit_eq_empty_or_univ
    [IsIntegral X] [UniversallyClosed f] (n : ℕ)
    (s : (tensorPower X.toRingedSpace.presheaf
      (structureSheafRing X.toRingedSpace).property (unitModules X) (n : ℤ)).sections) :
    nonvanishingLocus (X := X.toRingedSpace) _ s = ∅ ∨
      nonvanishingLocus (X := X.toRingedSpace) _ s = Set.univ := by
  classical
  have hF : IsField (Γ(X, ⊤)) := isField_of_universallyClosed k f
  obtain ⟨a, ha⟩ := ((unitTensorPowerGeneratorTop X n).property ⊤ le_rfl).2 (s.eval (op ⊤))
  rw [generator_restrict_self _ _ (unitTensorPowerGeneratorTop X n)] at ha
  have hiff := fun (x : X) => mem_nonvanishingLocus_iff_isUnit_ringGerm
    (X := X.toRingedSpace) _ s (unitTensorPowerGeneratorTop X n) a ha.symm x (Opens.mem_top x)
  by_cases hA : a = 0
  · left
    refine Set.eq_empty_iff_forall_notMem.2 fun x hx => ?_
    have hu := (hiff x).1 hx
    subst hA
    have hz : (ringGerm X.toRingedSpace x ⊤ (Opens.mem_top x))
        (0 : (structureSheafRing X.toRingedSpace).obj.obj (op (⊤ : X.Opens))) = 0 := map_zero _
    exact zero_ne_one (isUnit_zero_iff.1 (cast (congrArg IsUnit hz) hu))
  · right
    refine Set.eq_univ_of_forall fun x => (hiff x).2 ?_
    obtain ⟨b, hb⟩ := hF.mul_inv_cancel (a := (show Γ(X, ⊤) from a)) (by exact hA)
    have hua : IsUnit a := IsUnit.of_mul_eq_one (M := Γ(X, ⊤)) b hb
    exact IsUnit.map (ringGerm X.toRingedSpace x ⊤ (Opens.mem_top x)) hua

/-- **The structure sheaf of a proper curve over a field is not ample.** Ampleness produces a
global section of some positive tensor power whose nonvanishing locus is nonempty and affine. By
`AlgebraicGeometry.nonvanishingLocus_tensorPower_unit_eq_empty_or_univ` that locus is the whole
space, and an affine open of a proper curve is a proper subset
(`AlgebraicGeometry.IsAffineOpen.ne_top_of_isCurve`). -/
public theorem not_isAmple_unit_of_isCurve [IsProper f] [IsCurve k f] :
    ¬ Scheme.Modules.IsAmple X (unitModules X) := by
  rintro ⟨-, hpt⟩
  obtain ⟨x⟩ : Nonempty X := inferInstance
  obtain ⟨n, -, s, hxs, haff⟩ := hpt x
  rcases nonvanishingLocus_tensorPower_unit_eq_empty_or_univ k f n s with h | h
  · exact (Set.eq_empty_iff_forall_notMem.1 h x) hxs
  · exact haff.ne_top_of_isCurve k f (Opens.ext (h.trans Opens.coe_top.symm))

/-! ### At the projective line over a field -/

/-- `ℙ¹_k` is a proper curve over `k`, made an instance for the declarations below. -/
private instance : IsCurve k (projectiveSpaceOver 1 (Spec (.of k)) ↘ Spec (.of k)) :=
  isCurve_projectiveSpaceOver_one k

/-- The dimension bound that `AlgebraicGeometry.invertibleCurveDegree` takes as an argument, at
the projective line over a field. It is `AlgebraicGeometry.isCurve_projectiveSpaceOver_one`
read through `AlgebraicGeometry.IsCurve.topologicalKrullDim_eq_one`. -/
public theorem topologicalKrullDim_le_one_projectiveSpaceOver_one :
    topologicalKrullDim (projectiveSpaceOver 1 (Spec (.of k))) ≤ 1 :=
  le_of_eq (IsCurve.topologicalKrullDim_eq_one
    (f := projectiveSpaceOver 1 (Spec (.of k)) ↘ Spec (.of k)))

/-- **The degree of the structure sheaf of the projective line over a field is zero.** This is
`AlgebraicGeometry.invertibleCurveDegree_unit_eq_zero` at
`AlgebraicGeometry.isCurve_projectiveSpaceOver_one`, and it is the first value of
`AlgebraicGeometry.invertibleCurveDegree` in this development at an object that is a proper
curve. -/
public theorem invertibleCurveDegree_unit_projectiveSpaceOver_one_eq_zero :
    @invertibleCurveDegree k _ (projectiveSpaceOver 1 (Spec (.of k)))
        (projectiveSpaceOver 1 (Spec (.of k)) ↘ Spec (.of k)) inferInstance
        (topologicalKrullDim_le_one_projectiveSpaceOver_one k)
        (SheafOfModules.unit (projectiveSpaceOver 1 (Spec (.of k))).ringCatSheaf)
        (Scheme.Modules.isInvertible_unit (projectiveSpaceOver 1 (Spec (.of k)))) = 0 :=
  invertibleCurveDegree_unit_eq_zero k (projectiveSpaceOver 1 (Spec (.of k)) ↘ Spec (.of k))
    (topologicalKrullDim_le_one_projectiveSpaceOver_one k)

/-- **The structure sheaf of the projective line over a field is not ample.**
`AlgebraicGeometry.not_isAmple_unit_of_isCurve` fired at
`AlgebraicGeometry.isCurve_projectiveSpaceOver_one`, whose properness is the registered instance
`AlgebraicGeometry.projectiveSpaceOver_isProper`. -/
public theorem not_isAmple_unit_projectiveSpaceOver_one :
    ¬ Scheme.Modules.IsAmple (projectiveSpaceOver 1 (Spec (.of k)))
      (unitModules (projectiveSpaceOver 1 (Spec (.of k)))) :=
  not_isAmple_unit_of_isCurve k (projectiveSpaceOver 1 (Spec (.of k)) ↘ Spec (.of k))

/-- **The biconditional of [Stacks, Tag 0B5X] at the projective line over a field and its
structure sheaf, with no hypotheses.** Both sides are false and each is established on its own:
the left by `AlgebraicGeometry.not_isAmple_unit_projectiveSpaceOver_one` and the right by
`AlgebraicGeometry.invertibleCurveDegree_unit_projectiveSpaceOver_one_eq_zero`.

The attribute for Tag 0B5X is withheld: this is the tag at one object and one invertible module,
not the tag. What it supplies is the data the assembly
`AlgebraicGeometry.isAmple_iff_degree_pos` has never had — an object satisfying both its
typeclass hypotheses, an invertible module on it, and a computed degree — on the side where the
degree is not positive. It supplies nothing on the side where it is: no invertible module of
nonzero degree is exhibited anywhere in this development. -/
public theorem isAmple_unit_iff_invertibleCurveDegree_pos_projectiveSpaceOver_one :
    @Scheme.Modules.IsAmple (projectiveSpaceOver 1 (Spec (.of k)))
        (SheafOfModules.unit (projectiveSpaceOver 1 (Spec (.of k))).ringCatSheaf)
        (Scheme.Modules.isInvertible_unit (projectiveSpaceOver 1 (Spec (.of k)))) ↔
      0 < @invertibleCurveDegree k _ (projectiveSpaceOver 1 (Spec (.of k)))
        (projectiveSpaceOver 1 (Spec (.of k)) ↘ Spec (.of k)) inferInstance
        (topologicalKrullDim_le_one_projectiveSpaceOver_one k)
        (SheafOfModules.unit (projectiveSpaceOver 1 (Spec (.of k))).ringCatSheaf)
        (Scheme.Modules.isInvertible_unit (projectiveSpaceOver 1 (Spec (.of k)))) := by
  rw [invertibleCurveDegree_unit_projectiveSpaceOver_one_eq_zero k]
  exact ⟨fun h => absurd h (not_isAmple_unit_projectiveSpaceOver_one k),
    fun h => absurd h (lt_irrefl 0)⟩

end AlgebraicGeometry

end
