module

public import StacksFrontier.AlgebraicGeometry.Spaces.NagataCompactification.NoetherianCase
public import StacksFrontier.AlgebraicGeometry.Spaces.NagataCompactification.NoetherianReduction
public import StacksFrontier.AlgebraicGeometry.Spaces.NagataCompactification.EtaleSquareCompactification
public import StacksFrontier.AlgebraicGeometry.Spaces.NagataCompactification.Relocalize

/-!
# Nagata's compactification theorem for algebraic spaces

Let `Y` be a quasi-compact and quasi-separated algebraic space over a scheme `S` and let
`f : X ⟶ Y` be a separated morphism of finite type. Then `X` has a compactification over `Y`: a
quasi-compact open immersion into an algebraic space proper over `Y`.

As in the source, the base scheme is first replaced by `Spec ℤ`: viewing `X` and `Y` over the
terminal scheme along Stacks 03I5 changes neither the hypotheses (quasi-separatedness of `Y` is
the absolute notion of Stacks 03BS) nor the conclusion
(`AlgebraicGeometry.Space.hasCompactification_relocalize_iff`). Over `Spec ℤ` the proof reduces
to the case of a base of finite type over `Spec ℤ`
(`AlgebraicGeometry.Space.hasCompactification_of_forall_isFiniteType_viewOverIntegers`), where it
is a Noetherian induction
(`AlgebraicGeometry.Space.hasCompactification_of_isFiniteType_viewOverIntegers`).

## Main results

* `AlgebraicGeometry.Space.hasCompactification_of_isSeparated_of_isFiniteType`: the theorem.

## Implementation notes

Stacks 0F4B is
`AlgebraicGeometry.Space.hasCompactification_of_isElementaryDistinguishedSquare`, applied after
the passage to `Spec ℤ`; Stacks 07VR enters it through flattening by blowing up (Stacks 087E),
and Stacks 0873 enters it there and in the reduction to a base of finite type. Stacks 09YA
enters through Zariski's main theorem (Stacks 082K,
`AlgebraicGeometry.Space.exists_isOpenImmersion_isFinite_comp_eq_of_isQuasiFinite`), and
Stacks 07SU through the reduction to a base of finite type over `Spec ℤ`, in the form of the
proof of `AlgebraicGeometry.Space.hasNoetherianApproximation_of_isQuasiCompactSpace`, whose
inverse system satisfies the chapter's convention of Section 70.2 (see the implementation notes
of `StacksFrontier.AlgebraicGeometry.Spaces.NagataCompactification.NoetherianReduction`).

## References

* [Stacks Project, Tag 0F4D](https://stacks.math.columbia.edu/tag/0F4D)
* [Stacks Project, Section 03I3](https://stacks.math.columbia.edu/tag/03I3)
* [Stacks Project, Tag 03BS](https://stacks.math.columbia.edu/tag/03BS)
* [B. Conrad, M. Lieblich, M. Olsson, *Nagata compactification for algebraic spaces*][CLO]
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Cardinal Opposite

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **Nagata's compactification theorem for algebraic spaces.** Let `Y` be a quasi-compact and
quasi-separated algebraic space over `S`, and let `f : X ⟶ Y` be a separated morphism of finite
type. Then `X` has a compactification over `Y`. -/
@[stacks 0F4D]
theorem hasCompactification_of_isSeparated_of_isFiniteType (hZ : B.Contains (⊤_ Scheme.{u}))
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (hYqc : IsQuasiCompactSpace B S hS Y)
    (hYqs : IsAbsolutelyQuasiSeparated B S hS hZ Y) (f : X ⟶ Y) (hsep : IsSeparated B S hS f)
    (hft : IsFiniteType B S hS f) : HasCompactification B S hS f := by
  -- Replace `S` by `Spec ℤ`.
  let g : B.obj hS ⟶ B.obj hZ := ⟨terminal.from S⟩
  refine (hasCompactification_relocalize_iff g hY f).1 ?_
  exact hasCompactification_of_forall_isFiniteType_viewOverIntegers hZ
    (fun g hX' hY' hY'qc hY'qs hY'ft hgsep hgft =>
      hasCompactification_of_isFiniteType_viewOverIntegers hZ
        (hasCompactification_of_isElementaryDistinguishedSquare hZ) hX' hY'
        hY'qc hY'qs hY'ft g hgsep hgft)
    _ (isAlgebraicSpace_viewOver B S (⊤_ Scheme.{u}) hS hZ g X hX)
    (isAlgebraicSpace_viewOver B S (⊤_ Scheme.{u}) hS hZ g Y hY)
    ((isQuasiCompactSpace_relocalize_iff B S hS (⊤_ Scheme.{u}) hZ g Y).2 hYqc)
    (isAbsolutelyQuasiSeparated_viewOverIntegers B S hS hZ Y hYqs)
    (isSeparated_relocalize B S hS hZ g hsep)
    ((isFiniteType_relocalize_iff B S hS (⊤_ Scheme.{u}) hZ g f).2 hft)

end AlgebraicGeometry.Space

end
