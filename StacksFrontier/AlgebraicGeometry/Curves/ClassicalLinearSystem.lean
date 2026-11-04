module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Curves.LinearSeries
public import StacksFrontier.AlgebraicGeometry.Divisors.DivisorPicardClass
public import StacksFrontier.AlgebraicGeometry.PicardGroup.Scheme
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.DivisorDegreeTwist

/-!
# Linear equivalence of divisors and the complete linear system

Two effective Cartier divisors `D, D' ⊆ X` are *linearly equivalent* when the invertible
modules they define are isomorphic, `𝒪_X(D) ≅ 𝒪_X(D')`, and the *complete linear system* — or
*complete linear series* — `|D|` of an effective Cartier divisor `D` is the set of effective
Cartier divisors linearly equivalent to `D`.

## Main definitions

* `Stacks.Divisors.LinearlyEquivalent`: linear equivalence of divisors.
* `Stacks.Divisors.completeLinearSystem`: the complete linear system `|D|`.
* `Stacks.Divisors.linearSeriesOfDivisor`: the linear series `(𝒪_X(D), V)` attached to an
  effective Cartier divisor `D` on a proper curve and a space `V` of global sections of
  `𝒪_X(D)`.

## Main results

* `Stacks.Divisors.linearlyEquivalent_equivalence`: linear equivalence is an equivalence
  relation.
* `Stacks.Divisors.linearlyEquivalent_iff_picardClass_eq`: two effective Cartier divisors are
  linearly equivalent exactly when their invertible modules have the same class in `Pic(X)`.
* `Stacks.Divisors.completeLinearSystem_eq_iff_linearlyEquivalent`: `|D| = |D'|` exactly when
  `D` and `D'` are linearly equivalent.
* `Stacks.Divisors.mem_completeLinearSystem_iff_picardClass_eq`: `|D|` is the fibre over the
  class of `𝒪_X(D)` of the map sending an effective Cartier divisor to its class in `Pic(X)`.

## Implementation notes

The invertible module of a divisor is `Stacks.Divisors.modulesInvertibleSheaf`, which is
`Stacks.Divisors.invertibleSheaf` with its type ascribed as
`AlgebraicGeometry.Scheme.Modules`; that is the spelling both the Picard group
`AlgebraicGeometry.Scheme.picardGroup` and `AlgebraicGeometry.LinearSeries` are written over, so
no bridge between the two is needed in any statement below.

Invertibility of `𝒪_X(D)` is available from `Stacks.Divisors.IsEffectiveCartierDivisor D` in
two formalisations and at several spellings of the structure sheaf of rings; instance search is
syntactic, so `Stacks.Divisors.stacksIsInvertible_modulesInvertibleSheaf` crosses to the one
spelling that `AlgebraicGeometry.Scheme.picardClass` is stated at, following the "rebind with a
declared type" idiom of `StacksFrontier/AlgebraicGeometry/PicardGroup/Scheme.lean`.

Neither definition needs the hypotheses of the remark it formalizes — a smooth projective curve
over an algebraically closed field — and neither is stated with them: `𝒪_X(D)` and its
isomorphism class make sense on an arbitrary scheme. The degree `d` of the remark enters only
through the morphism `γ_d` to the Picard functor, which is not what `|D|` is defined to be.

## References

* [Stacks Project, Tag 0CCT](https://stacks.math.columbia.edu/tag/0CCT)
* [Stacks Project, Tag 01WX](https://stacks.math.columbia.edu/tag/01WX)
* [Stacks Project, Tag 01CX](https://stacks.math.columbia.edu/tag/01CX)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Divisors

variable {X : Scheme.{u}}

/-! ### Linear equivalence -/

/-- **Stacks Project, Tag 0CCT.** Two effective Cartier divisors `D, D' ⊆ X` are *linearly
equivalent* when `𝒪_X(D) ≅ 𝒪_X(D')` as `𝒪_X`-modules. -/
@[stacks 0CCT "the classical definition of linear equivalence: 𝒪_X(D) ≅ 𝒪_X(D')"]
def LinearlyEquivalent (D D' : X.IdealSheafData) : Prop :=
  Nonempty (modulesInvertibleSheaf D ≅ modulesInvertibleSheaf D')

/-- A divisor is linearly equivalent to itself. -/
theorem LinearlyEquivalent.refl (D : X.IdealSheafData) : LinearlyEquivalent D D :=
  ⟨Iso.refl _⟩

/-- Linear equivalence is symmetric. -/
theorem LinearlyEquivalent.symm {D D' : X.IdealSheafData} (h : LinearlyEquivalent D D') :
    LinearlyEquivalent D' D :=
  ⟨h.some.symm⟩

/-- Linear equivalence is transitive. -/
theorem LinearlyEquivalent.trans {D D' D'' : X.IdealSheafData} (h : LinearlyEquivalent D D')
    (h' : LinearlyEquivalent D' D'') : LinearlyEquivalent D D'' :=
  ⟨h.some ≪≫ h'.some⟩

/-- **Linear equivalence is an equivalence relation** on the closed subschemes of `X`. -/
theorem linearlyEquivalent_equivalence :
    Equivalence (LinearlyEquivalent (X := X)) :=
  ⟨LinearlyEquivalent.refl, LinearlyEquivalent.symm, LinearlyEquivalent.trans⟩

/-! ### Linear equivalence through the Picard group -/

/-- The invertible module `𝒪_X(D)` of an effective Cartier divisor is invertible at the index
`AlgebraicGeometry.Scheme.picardClass` is written over. -/
theorem stacksIsInvertible_modulesInvertibleSheaf (D : X.IdealSheafData)
    [IsEffectiveCartierDivisor D] :
    Stacks.SheafOfModules.IsInvertible X.presheaf X.ringCatIsSheaf (modulesInvertibleSheaf D) :=
  isTensorInvertible_invertibleSheaf D

/-- **Linear equivalence is equality of classes in `Pic(X)`.** Two effective Cartier divisors are
linearly equivalent exactly when `𝒪_X(D)` and `𝒪_X(D')` define the same element of the Picard
group, isomorphism of invertible modules being equality of Picard classes. -/
theorem linearlyEquivalent_iff_picardClass_eq (D D' : X.IdealSheafData)
    [IsEffectiveCartierDivisor D] [IsEffectiveCartierDivisor D'] :
    LinearlyEquivalent D D' ↔
      X.picardClass (modulesInvertibleSheaf D) (stacksIsInvertible_modulesInvertibleSheaf D) =
        X.picardClass (modulesInvertibleSheaf D')
          (stacksIsInvertible_modulesInvertibleSheaf D') :=
  (X.picardClass_eq_iff _ _ _ _).symm

/-! ### The complete linear system -/

/-- **Stacks Project, Tag 0CCT.** The *complete linear system*, or *complete linear series*,
`|D|` of an effective Cartier divisor `D ⊆ X`: the set of effective Cartier divisors `E ⊆ X`
which are linearly equivalent to `D`. -/
@[stacks 0CCT "the complete linear system |D|: the effective Cartier divisors linearly \
equivalent to D"]
def completeLinearSystem (D : X.IdealSheafData) : Set X.IdealSheafData :=
  {E | IsEffectiveCartierDivisor E ∧ LinearlyEquivalent E D}

/-- Membership in `|D|` is being an effective Cartier divisor linearly equivalent to `D`. -/
theorem mem_completeLinearSystem_iff {D E : X.IdealSheafData} :
    E ∈ completeLinearSystem D ↔ IsEffectiveCartierDivisor E ∧ LinearlyEquivalent E D :=
  Iff.rfl

/-- An effective Cartier divisor lies in its own complete linear system. -/
theorem self_mem_completeLinearSystem (D : X.IdealSheafData) [h : IsEffectiveCartierDivisor D] :
    D ∈ completeLinearSystem D :=
  ⟨h, .refl D⟩

/-- **`|D| = |D'|` exactly when `D` and `D'` are linearly equivalent**, for effective Cartier
divisors `D` and `D'`. -/
theorem completeLinearSystem_eq_iff_linearlyEquivalent {D D' : X.IdealSheafData}
    [IsEffectiveCartierDivisor D] :
    completeLinearSystem D = completeLinearSystem D' ↔ LinearlyEquivalent D D' := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · exact ((h ▸ self_mem_completeLinearSystem D : D ∈ completeLinearSystem D').2)
  · ext E
    exact and_congr_right fun _ =>
      ⟨fun hE => hE.trans h, fun hE => hE.trans h.symm⟩

/-- **`|D|` is a fibre of the Picard class map.** An effective Cartier divisor `E` lies in `|D|`
exactly when `𝒪_X(E)` and `𝒪_X(D)` have the same class in `Pic(X)`. -/
theorem mem_completeLinearSystem_iff_picardClass_eq {D E : X.IdealSheafData}
    [IsEffectiveCartierDivisor D] [hE : IsEffectiveCartierDivisor E] :
    E ∈ completeLinearSystem D ↔
      X.picardClass (modulesInvertibleSheaf E) (stacksIsInvertible_modulesInvertibleSheaf E) =
        X.picardClass (modulesInvertibleSheaf D)
          (stacksIsInvertible_modulesInvertibleSheaf D) := by
  rw [mem_completeLinearSystem_iff, linearlyEquivalent_iff_picardClass_eq]
  exact and_iff_right hE

/-! ### The linear series of a divisor and a space of sections -/

/-- **The linear series `(𝒪_X(D), V)` of an effective Cartier divisor `D` of degree `d` on a
proper scheme of dimension at most one over a field, together with an `(r + 1)`-dimensional
space `V` of global sections of `𝒪_X(D)`.** This is the linear series, in the sense of
[Stacks, Tag 0CCN], that the classical linear series cut out by `V` inside `|D|` corresponds
to. -/
def linearSeriesOfDivisor (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    [IsProper f] (hdim : topologicalKrullDim X ≤ 1) (D : X.IdealSheafData)
    [IsEffectiveCartierDivisor D] {d r : ℕ}
    (hd : invertibleCurveDegree k f hdim (modulesInvertibleSheaf D) = (d : ℤ))
    (V : Submodule k (cohomologyOverField k f (modulesInvertibleSheaf D) 0))
    (hV : Module.finrank k V = r + 1) :
    LinearSeries k f hdim d r where
  L := modulesInvertibleSheaf D
  isInvertible := inferInstance
  degree_eq := hd
  V := V
  finrank_eq := hV

end Stacks.Divisors

end
