module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalScheme.WeakFormalSpectrumBasicOpen
public import StacksFrontier.AlgebraicGeometry.FormalScheme.WeakIdealOfDefinitionCoverCounterexample
public import StacksFrontier.AlgebraicGeometry.FormalScheme.WeakIdealOfDefinitionLocality

/-!
# Locality of weak ideals of definition on a McQuillan formal scheme

Let `𝔛` be a formal scheme in the sense of McQuillan. Being a weak ideal of definition, and being a
fundamental system of weak ideals of definition, may be checked on the affine formal opens of `𝔛`
(`AlgebraicGeometry.IsWeakAffineFormalOpen`) contained in the members of any open covering. For the
fundamental-system condition the family is moreover nonempty and directed by inclusion.

Checking on the covering members alone is not enough:
`exists_not_isWeakIdealOfDefinitionOn_of_cover` exhibits an ideal sheaf on an affine scheme which
is a weak ideal of definition over an affine formal open covering the whole space, but not over a
smaller affine open.

## Main results

* `IdealSheaf.isWeakIdealOfDefinitionOn_of_cover_of_isMcQuillanFormalScheme`: an ideal sheaf is a
  weak ideal of definition if it is one over the affine formal opens contained in the members of an
  open covering.
* `isFundamentalSystemOfWeakIdealsOfDefinitionOn_of_cover_of_isMcQuillanFormalScheme`: a nonempty
  directed family of ideal sheaves is a fundamental system of weak ideals of definition if it is
  one over the affine formal opens contained in the members of an open covering.

## Implementation notes

The two geometric inputs are that affine formal opens are quasi-compact
(`IsWeakAffineFormalOpen.isCompact`) and that they form a basis of the topology
(`isBasis_isWeakAffineFormalOpen`, from `D(f) ∩ Spfw A ≅ Spfw A_{\{f\}}`).

## References

* [Stacks Project, Tag 0AIV](https://stacks.math.columbia.edu/tag/0AIV)
-/

@[expose] public section

open CategoryTheory TopologicalSpace Opposite

universe u

namespace AlgebraicGeometry.LocallyTopologicallyRingedSpace

variable {X : LTRS.{u}}

/-- The affine formal opens of a McQuillan formal scheme contained in a member of a covering cover
every open inside that member. -/
theorem refine_isWeakAffineFormalOpen (hX : IsMcQuillanFormalScheme X) (𝒰 : Set (Opens X)) :
    ∀ V ∈ 𝒰, ∀ W : Opens X, W ≤ V → ∀ x ∈ W,
      ∃ U : Opens X, U ≤ W ∧ x ∈ U ∧ IsWeakAffineFormalOpen X U := fun _ _ W _ x hx => by
  obtain ⟨U, hU, hxU, hUW⟩ := exists_isWeakAffineFormalOpen_le hX hx
  exact ⟨U, hUW, hxU, hU⟩

/-- An ideal sheaf on a formal scheme `𝔛` in the sense of McQuillan is a weak ideal of definition
as soon as its ideals of sections over the affine formal opens contained in the members of an open
covering are weak ideals of definition. -/
@[stacks 0AIV "it suffices to check the weak ideal-of-definition condition on an affine open \
covering, CORRECTED: on the affine formal opens contained in a covering member, checking the \
covering members alone being insufficient (`exists_not_isWeakIdealOfDefinitionOn_of_cover`)"]
theorem IdealSheaf.isWeakIdealOfDefinitionOn_of_cover_of_isMcQuillanFormalScheme
    (hX : IsMcQuillanFormalScheme X) (I : IdealSheaf X) (𝒰 : Set (Opens X)) (hcover : sSup 𝒰 = ⊤)
    (hI : ∀ V ∈ 𝒰, ∀ U : Opens X, U ≤ V → IsWeakAffineFormalOpen X U →
      TopologicalRing.IsWeakIdealOfDefinition (I.ideal U)) :
    I.IsWeakIdealOfDefinitionOn (IsWeakAffineFormalOpen X) :=
  I.isWeakIdealOfDefinitionOn_of_cover _ 𝒰 hcover (fun _ hU => hU.isCompact)
    (refine_isWeakAffineFormalOpen hX 𝒰) hI

/-- A nonempty family of ideal sheaves on a formal scheme `𝔛` in the sense of McQuillan, directed
by inclusion, is a fundamental system of weak ideals of definition as soon as, over every affine
formal open contained in a member of an open covering, its members are weak ideals of definition
whose ideals of sections form a neighbourhood basis of zero. -/
@[stacks 0AIV "it suffices to check the fundamental-system condition on an affine open covering, \
CORRECTED: on the affine formal opens contained in a covering member, checking the covering \
members alone being insufficient (`exists_not_isWeakIdealOfDefinitionOn_of_cover`), for a \
nonempty system directed by inclusion"]
theorem isFundamentalSystemOfWeakIdealsOfDefinitionOn_of_cover_of_isMcQuillanFormalScheme
    (hX : IsMcQuillanFormalScheme X) (𝒮 : Set (IdealSheaf X)) (hne : 𝒮.Nonempty)
    (hdir : ∀ I ∈ 𝒮, ∀ J ∈ 𝒮, ∃ K ∈ 𝒮, ∀ W : Opens X,
      K.ideal W ≤ I.ideal W ∧ K.ideal W ≤ J.ideal W)
    (𝒰 : Set (Opens X)) (hcover : sSup 𝒰 = ⊤)
    (h𝒮 : ∀ I ∈ 𝒮, ∀ V ∈ 𝒰, ∀ U : Opens X, U ≤ V → IsWeakAffineFormalOpen X U →
      TopologicalRing.IsWeakIdealOfDefinition (I.ideal U))
    (hbasis : ∀ V ∈ 𝒰, ∀ U : Opens X, U ≤ V → IsWeakAffineFormalOpen X U →
      (nhds (0 : (X.presheaf.obj (op U)).α)).HasBasis (· ∈ 𝒮)
        fun I : IdealSheaf X => (I.ideal U : Set (X.presheaf.obj (op U)).α)) :
    IsFundamentalSystemOfWeakIdealsOfDefinitionOn 𝒮 (IsWeakAffineFormalOpen X) :=
  isFundamentalSystemOfWeakIdealsOfDefinitionOn_of_cover_of_directed 𝒮 _ hne hdir 𝒰 hcover
    (fun _ hU => hU.isCompact) (refine_isWeakAffineFormalOpen hX 𝒰) h𝒮 hbasis

end AlgebraicGeometry.LocallyTopologicallyRingedSpace

end
