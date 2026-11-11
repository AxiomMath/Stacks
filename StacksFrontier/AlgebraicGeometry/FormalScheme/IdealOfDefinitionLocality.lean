module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalScheme.AffineFormalOpenBasis
public import StacksFrontier.AlgebraicGeometry.FormalScheme.IdealOfDefinition
public import StacksFrontier.AlgebraicGeometry.FormalScheme.WeakIdealOfDefinitionLocality

/-!
# Locality of a fundamental system of ideals of definition

A family `𝒮` of ideal sheaves on a locally topologically ringed space is a fundamental system of
ideals of definition over a class `𝒜` of opens — the affine formal open subschemes — when every
member is an ideal of definition over `𝒜` and, over every open of `𝒜`, the ideals of sections of
the members form a neighbourhood basis of zero (Stacks 0AIW). This file proves that both halves of
that condition may be checked on the opens of `𝒜` refining the members of a covering, for a
nonempty family directed by inclusion: the neighbourhood-basis half is transported along the
covering, not assumed.

## Main results

* `AlgebraicGeometry.LocallyTopologicallyRingedSpace`
  `.isFundamentalSystemOfIdealsOfDefinitionOn_of_cover_of_directed`: **Stacks 0AIW**, the
  fundamental-system condition may be checked on the opens of the class contained in the members
  of a covering.
* `AlgebraicGeometry.LocallyTopologicallyRingedSpace.IdealSheaf`
  `.isIdealOfDefinitionOn_of_cover_of_isFormalScheme` and
  `AlgebraicGeometry.LocallyTopologicallyRingedSpace`
  `.isFundamentalSystemOfIdealsOfDefinitionOn_of_cover_of_isFormalScheme`: the same on a formal
  scheme à la EGA, with no hypothesis on the class of opens: the affine formal open subschemes are
  quasi-compact and form a basis (`IsFormalScheme.exists_isAffineFormalOpen_mem_le`).

## Implementation notes

The source says that the condition may be checked on the members of an affine open covering. That
is false for ideal sheaves in the generality in which the source states it, even for a single
ideal of definition and the covering of an affine formal scheme by itself:
`not_forall_isFundamentalSystemOfIdealsOfDefinitionOn_of_hasBasis_cover` in
`StacksFrontier.AlgebraicGeometry.FormalScheme.IdealOfDefinitionCounterexample`. The conditions are
therefore checked on the opens of `𝒜` *contained in* a member of the covering, exactly as in the
single-ideal statement `IdealSheaf.isIdealOfDefinitionOn_of_cover`.

The family is nonempty and downward directed by inclusion, which is how the source's indexing set
`Λ` enters Section 87.13. Without directedness the neighbourhood-basis half does not pass to a
union, as for weak ideals of definition (see
`isFundamentalSystemOfWeakIdealsOfDefinitionOn_of_cover_of_directed`): on a disjoint union of two
affine schemes `Spec A` with a non-zero square-zero ideal `N ⊆ A`, the two ideals of definition
`0 ⊔ N` and `N ⊔ 0` form a fundamental system over every affine open of either piece, but neither
has zero sections over the affine union, on which `{0}` is open.

The neighbourhood-basis half is transported by `IdealSheaf.hasBasis_ideal_of_isCompact`, which
needs only that the ideals of sections are open over the quasi-compact opens of the class; for
ideals of definition this is part of the first half.

## References

* [Stacks Project, Tag 0AIW](https://stacks.math.columbia.edu/tag/0AIW)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace AlgebraicGeometry.LocallyTopologicallyRingedSpace

universe u

/-- **Stacks 0AIW**, the locality of the fundamental-system condition. Let `𝒰` be a covering of
`X` and let `𝒜` be a class of quasi-compact opens — the affine formal open subschemes — whose
members contained in an open cover that open. Let `𝒮` be a nonempty family of ideal sheaves,
downward directed by inclusion, such that over every open of `𝒜` contained in a member of `𝒰`
each member of `𝒮` has an ideal of definition for its ideal of sections and these ideals of
sections form a neighbourhood basis of zero. Then `𝒮` is a fundamental system of ideals of
definition over `𝒜`.

Both halves of the condition are transported along the covering: the ideal-of-definition half by
`IdealSheaf.isIdealOfDefinitionOn_of_cover`, the neighbourhood-basis half by
`IdealSheaf.hasBasis_ideal_of_isCompact`. On a formal scheme à la EGA the hypotheses `hcompact`
and `hrefine` hold, and the tagged form is
`isFundamentalSystemOfIdealsOfDefinitionOn_of_cover_of_isFormalScheme`. -/
theorem isFundamentalSystemOfIdealsOfDefinitionOn_of_cover_of_directed {X : LTRS.{u}}
    (𝒮 : Set (IdealSheaf X)) (𝒜 : Opens X → Prop) (hne : 𝒮.Nonempty)
    (hdir : ∀ I ∈ 𝒮, ∀ J ∈ 𝒮, ∃ K ∈ 𝒮, ∀ W : Opens X,
      K.ideal W ≤ I.ideal W ∧ K.ideal W ≤ J.ideal W)
    (𝒰 : Set (Opens X)) (hcover : sSup 𝒰 = ⊤)
    (hcompact : ∀ U : Opens X, 𝒜 U → IsCompact (U : Set X))
    (hrefine : ∀ V ∈ 𝒰, ∀ W : Opens X, W ≤ V → ∀ x ∈ W,
      ∃ U : Opens X, U ≤ W ∧ x ∈ U ∧ 𝒜 U)
    (h𝒮 : ∀ I ∈ 𝒮, ∀ V ∈ 𝒰, ∀ U : Opens X, U ≤ V → 𝒜 U →
      TopologicalRing.IsIdealOfDefinition (I.ideal U))
    (hbasis : ∀ V ∈ 𝒰, ∀ U : Opens X, U ≤ V → 𝒜 U →
      (nhds (0 : (X.presheaf.obj (op U)).α)).HasBasis (· ∈ 𝒮)
        fun I : IdealSheaf X => (I.ideal U : Set (X.presheaf.obj (op U)).α)) :
    IsFundamentalSystemOfIdealsOfDefinitionOn 𝒮 𝒜 := by
  have hdef : ∀ I ∈ 𝒮, I.IsIdealOfDefinitionOn 𝒜 := fun I hI =>
    I.isIdealOfDefinitionOn_of_cover 𝒜 𝒰 hcover hcompact hrefine (h𝒮 I hI)
  refine ⟨hdef, fun T hT => ?_⟩
  refine IdealSheaf.hasBasis_ideal_of_isCompact hne hdir T (hcompact T hT)
    (fun I hI => (hdef I hI T hT).1) fun x hx => ?_
  obtain ⟨V, hV, hxV⟩ := Opens.mem_sSup.mp (show x ∈ sSup 𝒰 by rw [hcover]; trivial)
  obtain ⟨U, hUW, hxU, hU⟩ := hrefine V hV (V ⊓ T) inf_le_left x ⟨hxV, hx⟩
  exact ⟨U, hUW.trans inf_le_right, hxU, hbasis V hV U (hUW.trans inf_le_left) hU⟩

/-- **Stacks 0AIW**, the locality of the ideal-of-definition condition on a formal scheme à la EGA.
An ideal sheaf is an ideal of definition as soon as its ideals of sections over the affine formal
open subschemes contained in the members of some covering are ideals of definition. The
affine formal open subschemes are quasi-compact and form a basis, which are the two hypotheses
`IdealSheaf.isIdealOfDefinitionOn_of_cover` asks of the class of opens. -/
@[stacks 0AIW "it suffices to check the ideal-of-definition condition on an affine open covering, \
CORRECTED, on a formal scheme à la EGA with no further hypothesis: the condition is checked on the \
affine formal opens contained in a covering member, not on the covering members themselves, which \
is false as the source states it (`not_forall_isIdealOfDefinitionOn_of_cover`)"]
theorem IdealSheaf.isIdealOfDefinitionOn_of_cover_of_isFormalScheme {X : LTRS.{u}}
    (hX : IsFormalScheme X) (I : IdealSheaf X) (𝒰 : Set (Opens X)) (hcover : sSup 𝒰 = ⊤)
    (hI : ∀ V ∈ 𝒰, ∀ U : Opens X, U ≤ V → IsAffineFormalOpen X U →
      TopologicalRing.IsIdealOfDefinition (I.ideal U)) :
    I.IsIdealOfDefinitionOn (IsAffineFormalOpen X) :=
  I.isIdealOfDefinitionOn_of_cover _ 𝒰 hcover
    (fun _ hU => hU.isWeakAffineFormalOpen.isCompact)
    (fun _ _ _ _ _ hx => hX.exists_isAffineFormalOpen_mem_le hx) hI

/-- **Stacks 0AIW**, the locality of the fundamental-system condition on a formal scheme à la EGA,
with no hypothesis on the class of opens: for a nonempty family directed by inclusion, both halves
of the condition may be checked on the affine formal open subschemes contained in the members of a
covering. -/
@[stacks 0AIW "it suffices to check the fundamental-system condition on an affine open covering, \
CORRECTED, on a formal scheme à la EGA with no further hypothesis: both halves are checked on the \
affine formal opens contained in a covering member, not on the covering members themselves, which \
is false as the source states it \
(`not_forall_isFundamentalSystemOfIdealsOfDefinitionOn_of_hasBasis_cover`), for a nonempty system \
directed by inclusion (`hne`, `hdir`), the source's directed index set `Λ`"]
theorem isFundamentalSystemOfIdealsOfDefinitionOn_of_cover_of_isFormalScheme {X : LTRS.{u}}
    (hX : IsFormalScheme X) (𝒮 : Set (IdealSheaf X)) (hne : 𝒮.Nonempty)
    (hdir : ∀ I ∈ 𝒮, ∀ J ∈ 𝒮, ∃ K ∈ 𝒮, ∀ W : Opens X,
      K.ideal W ≤ I.ideal W ∧ K.ideal W ≤ J.ideal W)
    (𝒰 : Set (Opens X)) (hcover : sSup 𝒰 = ⊤)
    (h𝒮 : ∀ I ∈ 𝒮, ∀ V ∈ 𝒰, ∀ U : Opens X, U ≤ V → IsAffineFormalOpen X U →
      TopologicalRing.IsIdealOfDefinition (I.ideal U))
    (hbasis : ∀ V ∈ 𝒰, ∀ U : Opens X, U ≤ V → IsAffineFormalOpen X U →
      (nhds (0 : (X.presheaf.obj (op U)).α)).HasBasis (· ∈ 𝒮)
        fun I : IdealSheaf X => (I.ideal U : Set (X.presheaf.obj (op U)).α)) :
    IsFundamentalSystemOfIdealsOfDefinitionOn 𝒮 (IsAffineFormalOpen X) :=
  isFundamentalSystemOfIdealsOfDefinitionOn_of_cover_of_directed 𝒮 _ hne hdir 𝒰 hcover
    (fun _ hU => hU.isWeakAffineFormalOpen.isCompact)
    (fun _ _ _ _ _ hx => hX.exists_isAffineFormalOpen_mem_le hx) h𝒮 hbasis

end AlgebraicGeometry.LocallyTopologicallyRingedSpace

end
