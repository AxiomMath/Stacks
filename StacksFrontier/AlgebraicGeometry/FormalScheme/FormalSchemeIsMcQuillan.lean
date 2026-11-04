module

public import Mathlib.CategoryTheory.Filtered.Final
public import StacksFrontier.AlgebraicGeometry.FormalScheme.IdealOfDefinition
public import StacksFrontier.AlgebraicGeometry.FormalScheme.WeakAffineFormalOpen

/-!
# Formal schemes à la EGA are formal schemes in the sense of McQuillan

The formal spectrum `Spf A` of an admissible topological ring is the limit of the
pseudo-discretised structure sheaves of the `Spec (A/I)` over the ideals of definition `I`, and
McQuillan's `Spfw A` is the same limit over the weak ideals of definition. Over a pre-admissible
ring the ideals of definition are initial among the weak ones — a weak ideal of definition
contains its intersection with an ideal of definition, which is again one — so the two limits
agree. Hence every affine formal open subscheme is a weak affine formal open subscheme, and every
formal scheme à la EGA is a formal scheme in the sense of McQuillan, the inclusion of Stacks 0AI3
that Stacks 0AIW uses to read Remark 0AIV for formal schemes à la EGA.

## Main results

* `AlgebraicGeometry.spfIsoSpfw`: `Spf A ≅ Spfw A` for a pre-admissible `A`.
* `AlgebraicGeometry.IsAffineFormalOpen.isWeakAffineFormalOpen`: an affine formal open subscheme
  is a weak affine formal open subscheme.
* `AlgebraicGeometry.IsFormalScheme.isMcQuillanFormalScheme`: a formal scheme à la EGA is a formal
  scheme in the sense of McQuillan.

## References

* [Stacks Project, Tag 0AI3](https://stacks.math.columbia.edu/tag/0AI3)
* [Stacks Project, Tag 0AIW](https://stacks.math.columbia.edu/tag/0AIW)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace TopologicalRing

namespace AlgebraicGeometry

universe u

variable (A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]

/-- The inclusion of the ideals of definition among the weak ideals of definition. -/
abbrev idealsOfDefinitionToWeak : IdealsOfDefinition A ⥤ WeakIdealsOfDefinition A :=
  (show Monotone (fun I : IdealsOfDefinition A =>
      (⟨I.1, isWeakIdealOfDefinition_of_isIdealOfDefinition I.2⟩ : WeakIdealsOfDefinition A))
    from fun _ _ h => h).functor

/-- Over a pre-admissible ring the ideals of definition are initial among the weak ideals of
definition: a weak ideal of definition contains its intersection with an ideal of definition,
which is again an ideal of definition. -/
instance initial_idealsOfDefinitionToWeak [Fact (IsPreAdmissible A)] :
    (idealsOfDefinitionToWeak A).Initial := by
  obtain ⟨I, hI⟩ := (Fact.out : IsPreAdmissible A)
  have : IsCodirectedOrder (IdealsOfDefinition A) :=
    ⟨fun J K => ⟨spfIndexMeet A J K, (show J.1 ⊓ K.1 ≤ J.1 from inf_le_left),
      (show J.1 ⊓ K.1 ≤ K.1 from inf_le_right)⟩⟩
  have : Nonempty (IdealsOfDefinition A) := ⟨⟨I, hI⟩⟩
  refine (Monotone.initial_functor_iff _).mpr fun J => ?_
  exact ⟨⟨I ⊓ J.1, isIdealOfDefinition_of_le_of_isOpen hI (hI.1.inter J.2.1) inf_le_left⟩,
    (show I ⊓ J.1 ≤ J.1 from inf_le_right)⟩

/-- **The formal spectrum of an admissible ring is its McQuillan formal spectrum.** Over a
pre-admissible ring, the limit of the pseudo-discretised structure sheaves of the `Spec (A/I)`
over the ideals of definition `I` is the limit over the weak ideals of definition, since the
former are initial among the latter. -/
noncomputable def spfIsoSpfw (hA : IsPreAdmissible A) : Spf A ≅ Spfw A := by
  haveI : Fact (IsPreAdmissible A) := ⟨hA⟩
  let diagramIso : spfDiagramOn A IsIdealOfDefinition ⋙ pseudoDiscreteFunctor ≅
      idealsOfDefinitionToWeak A ⋙ (spfDiagramOn A IsWeakIdealOfDefinition ⋙
        pseudoDiscreteFunctor) :=
    NatIso.ofComponents (fun I => Iso.refl _) (by intros; rfl)
  let presheafIso : spfPresheafOn A IsIdealOfDefinition ≅ spfPresheafOn A IsWeakIdealOfDefinition :=
    HasLimit.isoOfNatIso diagramIso ≪≫ Functor.Initial.limitIso (idealsOfDefinitionToWeak A) _
  exact PresheafedSpace.isoOfComponents (Iso.refl _) presheafIso

/-- An affine formal open subscheme is a weak affine formal open subscheme: an admissible ring is
weakly admissible, and its formal spectrum is its McQuillan formal spectrum. -/
theorem IsAffineFormalOpen.isWeakAffineFormalOpen {X : LTRS.{u}} {U : Opens X}
    (hU : IsAffineFormalOpen X U) : IsWeakAffineFormalOpen X U := by
  obtain ⟨A, hlinear, hA, ⟨e⟩⟩ := hU
  let _ := hlinear
  exact ⟨A, hlinear, ⟨isWeaklyPreAdmissible_of_isPreAdmissible hA.1, hA.2.2, hA.2.1⟩,
    ⟨e ≪≫ spfIsoSpfw A.α hA.1⟩⟩

/-- **A formal scheme à la EGA is a formal scheme in the sense of McQuillan** (Stacks 0AI3): every
point has an affine formal open neighbourhood, which is a weak affine formal open. -/
theorem IsFormalScheme.isMcQuillanFormalScheme {X : LTRS.{u}} (hX : IsFormalScheme X) :
    IsMcQuillanFormalScheme X := by
  refine (isMcQuillanFormalScheme_iff_forall_isWeakAffineFormalOpen X).mpr fun x => ?_
  obtain ⟨U, hxU, hU⟩ := (isFormalScheme_iff_forall_isAffineFormalOpen X).mp hX x
  exact ⟨U, hxU, hU.isWeakAffineFormalOpen⟩

end AlgebraicGeometry

end
