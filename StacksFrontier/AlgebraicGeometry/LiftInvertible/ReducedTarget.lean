module

public import StacksFrontier.AlgebraicGeometry.ClosedCoverGlue.Basic
public import StacksFrontier.AlgebraicGeometry.LiftInvertible.ClosedUnion
public import StacksFrontier.AlgebraicGeometry.ClosedLift.Basic

/-!
# Tag 09NY for a reduced ambient scheme

[Stacks, Tag 09NY](https://stacks.math.columbia.edu/tag/09NY) is proved here under the single
extra hypothesis that `X` is **reduced**, with no condition whatever on the closed subscheme
`Z`; in particular `Z` may contain some irreducible components of `X` and not others.

## The proof is a two-member closed cover

`Stacks.LiftInvertible.complementaryComponents` gives the union `Y` of the irreducible
components of `X` not contained in the image of `Z`, and
`Stacks.LiftInvertible.union_complementaryComponents` says `Z` and `Y` cover `X`
set-theoretically. So `X` is covered by **two** closed subschemes — `Z`, and the reduced
induced subscheme on `Y`, namely the subscheme of
`AlgebraicGeometry.Scheme.IdealSheafData.vanishingIdeal Y` — whose intersection is
`Stacks.LiftInvertible.discreteTopology_range_inter_complementaryClosed`, a finite discrete set
of closed points.

That is exactly the hypothesis of [Stacks, Tag 09NE], stated as
`StacksTag09NE.exists_invertible_of_closed_cover_discrete_intersections`: invertible modules on
the members of a finite closed cover of a **reduced** scheme, meeting pairwise in discrete
spaces, glue to an invertible module restricting to each. Feed it `L` on `Z` and the structure
sheaf on the reduced complement — the latter is invertible — and the member at `Z` of the
conclusion is Tag 09NY's conclusion, already in Tag 09NY's own
`RingedSpaceModuleAdjunction.modulePullback` spelling.

Reducedness of `X` is used by Tag 09NE and nowhere here. It is what makes the two-member cover
a cover *scheme*-theoretically and not merely set-theoretically; for a general `X` the
corresponding statement is about the scheme-theoretic union
`Stacks.LiftInvertible.closedUnionIdeal`, and
`Stacks.LiftInvertible.picPullbackSurjective_of_closedUnionLift` reduces Tag 09NY to it.

## Main results

* `Stacks.LiftInvertible.picPullbackSurjective_of_isReduced`: **Tag 09NY for reduced `X`**, in
  predicate form.
* `Stacks.LiftInvertible.exists_modulePullback_iso_of_isReduced`: the same in Tag 09NY's own
  `∃`-form, with Tag 09NY's own hypotheses plus `[IsReduced X]`.

## References

* [Stacks Project, Tag 09NY](https://stacks.math.columbia.edu/tag/09NY)
* [Stacks Project, Tag 09NE](https://stacks.math.columbia.edu/tag/09NE)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Set TopologicalSpace Topology
open CategoryTheory.Limits
open RingedSpaceModuleAdjunction
open AlgebraicGeometry.Scheme.IdealSheafData

universe u

open Stacks.AlgebraicGeometry.Tag09NY (LiftsInvertibleModules)

namespace Stacks.LiftInvertible

variable {X Z : Scheme.{u}}

/-- **The two-member closed cover of `X` attached to a closed subscheme `Z`**: `Z` itself at
`true`, and the reduced induced subscheme on the irreducible components `Z` misses at `false`. -/
noncomputable def coverScheme (i : Z ⟶ X) [NoetherianSpace X] : Bool → Scheme.{u}
  | true => Z
  | false => (vanishingIdeal (complementaryClosed i)).subscheme

/-- The two closed immersions of `Stacks.LiftInvertible.coverScheme` into `X`. -/
noncomputable def coverMap (i : Z ⟶ X) [NoetherianSpace X] : ∀ b, coverScheme i b ⟶ X
  | true => i
  | false => (vanishingIdeal (complementaryClosed i)).subschemeι

/-- Each member `Stacks.LiftInvertible.coverMap i b` of the cover is a closed immersion. -/
instance isClosedImmersion_coverMap (i : Z ⟶ X) [IsClosedImmersion i] [NoetherianSpace X]
    (b : Bool) : IsClosedImmersion (coverMap i b) := by
  cases b with
  | true => exact ‹IsClosedImmersion i›
  | false => exact inferInstanceAs (IsClosedImmersion (vanishingIdeal _).subschemeι)

/-- The `true` member of the cover has the image of `Z` as its image. -/
@[simp]
theorem range_coverMap_true (i : Z ⟶ X) [NoetherianSpace X] :
    Set.range (coverMap i true).base = Set.range i.base := rfl

/-- The `false` member of the cover has the complementary components as its image: it is the
reduced induced subscheme on them, and `AlgebraicGeometry.Scheme.IdealSheafData.vanishingIdeal`
of a closed set has that set as its support. -/
@[simp]
theorem range_coverMap_false (i : Z ⟶ X) [NoetherianSpace X] :
    Set.range (coverMap i false).base = (complementaryClosed i : Set (X : Type u)) := by
  show Set.range (vanishingIdeal (complementaryClosed i)).subschemeι = _
  rw [Scheme.IdealSheafData.range_subschemeι]
  exact coe_support_vanishingIdeal _

/-- **The two members cover `X`**, with no hypothesis beyond `i` being a closed immersion: a
point lies in some irreducible component of `X`, and that component is either inside the image
of `Z` or is one of the components making up the complement. -/
theorem exists_coverMap_eq (i : Z ⟶ X) [IsClosedImmersion i] [NoetherianSpace X] (x : X) :
    ∃ (b : Bool) (z : coverScheme i b), (coverMap i b) z = x := by
  have hx : x ∈ Set.range i.base ∪ complementaryComponents (X : Type u) (Set.range i.base) := by
    rw [union_complementaryComponents]; exact mem_univ x
  rcases hx with hx | hx
  · obtain ⟨z, hz⟩ := hx
    exact ⟨true, z, hz⟩
  · obtain ⟨z, hz⟩ : x ∈ Set.range (coverMap i false).base := by
      rw [range_coverMap_false]; exact hx
    exact ⟨false, z, hz⟩

/-- The two members of the cover meet in a discrete space: their intersection is the overlap of
the image of `Z` with the components it misses, which is
`Stacks.LiftInvertible.discreteTopology_range_inter_complementaryClosed`. -/
theorem discreteTopology_range_coverMap_inter (i : Z ⟶ X) [IsClosedImmersion i]
    [NoetherianSpace X] (hdim : topologicalKrullDim X ≤ 1) (b b' : Bool) (hbb' : b ≠ b') :
    DiscreteTopology
      ((Set.range (coverMap i b).base ∩ Set.range (coverMap i b').base : Set (X : Type u))) := by
  have hdisc := discreteTopology_range_inter_complementaryClosed i hdim
  cases b <;> cases b' <;> first | exact absurd rfl hbb' | skip
  · rw [range_coverMap_true, range_coverMap_false, Set.inter_comm]; exact hdisc
  · rw [range_coverMap_true, range_coverMap_false]; exact hdisc

/-- The family of modules on the members of `Stacks.LiftInvertible.coverScheme`: the given `L`
on `Z`, and the structure sheaf on the reduced complement. -/
noncomputable def coverModule (i : Z ⟶ X) [NoetherianSpace X]
    (L : SheafOfModules.{u} (structureSheafRing Z.toRingedSpace)) : ∀ b, (coverScheme i b).Modules
  | true => L
  | false => SheafOfModules.unit (structureSheafRing (coverScheme i false).toRingedSpace)

/-- **Tag 09NY for a reduced ambient scheme.** If `X` is reduced with Noetherian underlying
space of dimension at most one, then every invertible module on **every** closed subscheme of
`X` is the pullback of an invertible module on `X`, with no hypothesis on how `Z` meets the
irreducible components of `X`. -/
theorem picPullbackSurjective_of_isReduced (i : Z ⟶ X) [IsClosedImmersion i] [IsReduced X]
    [NoetherianSpace X] (hdim : topologicalKrullDim X ≤ 1) : LiftsInvertibleModules i := by
  intro L hL
  have hinv : ∀ b, AlgebraicGeometry.SheafOfModules.IsInvertible (coverScheme i b).presheaf
      (coverScheme i b).ringCatSheaf.2 (coverModule i L b) := by
    intro b
    cases b with
    | true => exact hL
    | false =>
      exact (Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry _ _ _).mp
        (Stacks.SheafOfModules.isInvertible_unit _ _)
  obtain ⟨M, hM, hMpull⟩ :=
    StacksTag09NE.exists_invertible_of_closed_cover_discrete_intersections X (coverScheme i)
      (coverMap i) (exists_coverMap_eq i)
      (discreteTopology_range_coverMap_inter i hdim) (coverModule i L)
  exact ⟨M, hM, hMpull true⟩

/-- **Tag 09NY for a reduced ambient scheme**, in Tag 09NY's own `∃`-form: Tag 09NY's own
hypotheses, plus `[IsReduced X]`, and Tag 09NY's own conclusion. -/
theorem exists_modulePullback_iso_of_isReduced (X Z : Scheme.{u}) (i : Z ⟶ X)
    [IsClosedImmersion i] [IsReduced X] [NoetherianSpace X]
    (hdim : topologicalKrullDim X ≤ 1)
    (L : SheafOfModules.{u} (structureSheafRing Z.toRingedSpace))
    (hL : AlgebraicGeometry.SheafOfModules.IsInvertible Z.presheaf
      (Presheaf.isSheaf_comp_of_isSheaf _ _ (forget₂ CommRingCat RingCat) Z.IsSheaf) L) :
    ∃ (M : SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
      (_ : AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf
        (Presheaf.isSheaf_comp_of_isSheaf _ _ (forget₂ CommRingCat RingCat) X.IsSheaf) M),
      Nonempty ((modulePullback i.toLRSHom.toShHom).obj M ≅ L) :=
  let ⟨M, hM, hiso⟩ := picPullbackSurjective_of_isReduced i hdim L hL
  ⟨M, hM, hiso⟩

end Stacks.LiftInvertible

end
