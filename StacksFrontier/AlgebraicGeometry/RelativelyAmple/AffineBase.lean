module

public import StacksFrontier.AlgebraicGeometry.AmpleTransport.Basic
public import StacksFrontier.AlgebraicGeometry.RelativeAmple.Basic
public import StacksFrontier.AlgebraicGeometry.AmpleBridge.Basic

/-!
# Relative ampleness over an affine base

[Stacks, Tag 01VT] lists six conditions on an invertible sheaf `L` on a scheme `X` of finite type
over an **affine** base `S` that are all equivalent, the first two of which are that `L` is ample
on `X` and that `L` is ample relative to `X ⟶ S`. This file proves that those two agree, as far
as the library can currently reach: relative ampleness always implies ampleness, and ampleness
implies relative ampleness when the base has a single point — in particular over the spectrum of
a field, which is the case [Stacks, Tag 0BDE] needs.

## Main results

* `AlgebraicGeometry.Scheme.Modules.isAmple_of_isRelativelyAmple`: over an affine base a
  relatively ample invertible sheaf is ample. This is the implication (2) ⇒ (1) of
  [Stacks, Tag 01VT].
* `AlgebraicGeometry.Scheme.Modules.isRelativelyAmple_of_isAmple`: over an affine base whose
  underlying space is a single point, an ample invertible sheaf is relatively ample. This is the
  implication (1) ⇒ (2) of [Stacks, Tag 01VT] in that case.
* `AlgebraicGeometry.Scheme.Modules.isRelativelyAmple_iff_isAmple`: the two together.

Everything in this file is stated over `AlgebraicGeometry.Scheme.Modules.IsAmple`, the spelling of
Stacks Tag 01PS that carries the tag. It is **not** the predicate
`Stacks.RelativeAmpleAffineBase.isRelativelyAmple_iff_isAmple` is stated over, which is
`Stacks.Ample.IsAmple`; the two are separate definitions, compared by
`Stacks.AmpleBridge.isAmple_iff_isAmple`, and that is why the two theorems share a short name
without stating the same thing.

## Implementation notes

Relative ampleness quantifies over the affine opens `V` of the base and asserts ampleness of the
restriction of `L` to `f⁻¹ V`. Taking `V = ⊤`, which is affine exactly because the base is, gives
`f⁻¹ V = ⊤` by definition, and the inclusion of `⊤` is an isomorphism
(`AlgebraicGeometry.Scheme.topIso`), so both implications are transports of ampleness along an
isomorphism of schemes: `AlgebraicGeometry.Scheme.Modules.isAmple_pullback_of_isIso` in one
direction, and in the other the same statement for the inverse isomorphism followed by
`AlgebraicGeometry.Scheme.Modules.isAmple_of_iso` across the unit of
`AlgebraicGeometry.Scheme.Modules.pullbackEquivOfIso`, which identifies the two successive
pullbacks with the identity.

**Why the second implication is only proved over a one-point base.** For a general affine base
the quantifier runs over affine opens `V` other than `⊤`, and `f⁻¹ V ⟶ X` is then an open
immersion and not an isomorphism; ampleness of the restriction of `L` to it is the content of
[Stacks, Tag 0B3E] for a quasi-compact immersion, which needs the nonvanishing locus of a
restricted section to be affine and is not in the library. When the base has a single point its
only opens are `⊥` and `⊤`, both affine, and the case of `⊥` is vacuous because `f⁻¹ ⊥` has no
points.

**The attribute for Tag 01VT is withheld.** The tag asserts a six-term `List.TFAE`; what is here
is one of the fifteen equivalences, and one half of that one is conditional on the base being a
single point. The remaining four conditions — eventual relative very ampleness, and the
immersions into relative projective space — are not formulated in the library at all.

## References

* [Stacks Project, Tag 01VT](https://stacks.math.columbia.edu/tag/01VT)
* [Stacks Project, Tag 01VH](https://stacks.math.columbia.edu/tag/01VH)
* [Stacks Project, Tag 01PS](https://stacks.math.columbia.edu/tag/01PS)
* [Stacks Project, Tag 0B3E](https://stacks.math.columbia.edu/tag/0B3E)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X S : Scheme.{u}} (f : X ⟶ S) (L : X.Modules)
  [AlgebraicGeometry.SheafOfModules.IsInvertible X.toRingedSpace.presheaf
    (structureSheafRing X.toRingedSpace).property L]

/-- The pullback of an invertible sheaf along a morphism of schemes is invertible. -/
private theorem isInvertible_pullback {Y : Scheme.{u}} (g : Y ⟶ X) (L : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.toRingedSpace.presheaf
      (structureSheafRing X.toRingedSpace).property L] :
    AlgebraicGeometry.SheafOfModules.IsInvertible Y.toRingedSpace.presheaf
      (structureSheafRing Y.toRingedSpace).property ((Scheme.Modules.pullback g).obj L) :=
  Stacks.RingedSpace.algebraicGeometryIsInvertible_modulePullback g.toLRSHom.toShHom L

/-- **The implication (2) ⇒ (1) of [Stacks, Tag 01VT].** Over an affine base, an invertible sheaf
that is ample relative to the structure morphism is ample. -/
public theorem isAmple_of_isRelativelyAmple [IsAffine S]
    (h : Stacks.RelativeAmple.IsRelativelyAmple f L) :
    IsAmple X L := by
  have : IsIso (f ⁻¹ᵁ (⊤ : S.Opens)).ι := inferInstanceAs (IsIso X.topIso.hom)
  have h1 := h.isAmple_preimage _ _ ⊤ (isAffineOpen_top S)
  have := isInvertible_pullback (f ⁻¹ᵁ (⊤ : S.Opens)).ι L
  have := isInvertible_pullback (asIso (f ⁻¹ᵁ (⊤ : S.Opens)).ι).inv
    ((Scheme.Modules.pullback (f ⁻¹ᵁ (⊤ : S.Opens)).ι).obj L)
  have e0 : (Scheme.Modules.pullback (asIso (f ⁻¹ᵁ (⊤ : S.Opens)).ι).inv).obj
      ((Scheme.Modules.pullback (f ⁻¹ᵁ (⊤ : S.Opens)).ι).obj L) ≅ L :=
    ((pullbackEquivOfIso (asIso (f ⁻¹ᵁ (⊤ : S.Opens)).ι)).unitIso.app L).symm
  exact isAmple_of_iso e0
    (isAmple_pullback_of_isIso (asIso (f ⁻¹ᵁ (⊤ : S.Opens)).ι).inv _
      ((Stacks.AmpleBridge.isAmple_iff_isAmple _ _).mp h1))

/-- **The implication (1) ⇒ (2) of [Stacks, Tag 01VT] over a one-point base.** If the base is
affine with a single point — the spectrum of a field, for instance — then an ample invertible
sheaf is ample relative to the structure morphism. -/
public theorem isRelativelyAmple_of_isAmple [IsAffine S] [Subsingleton ↥S] (h : IsAmple X L) :
    Stacks.RelativeAmple.IsRelativelyAmple f L := by
  refine ⟨(quasiCompact_iff_compactSpace f).mpr h.compactSpace, fun V hV => ?_⟩
  rcases Set.eq_empty_or_nonempty (V : Set ↥S) with hb | ⟨y, hy⟩
  · have hV0 : V = ⊥ := TopologicalSpace.Opens.ext hb
    subst hV0
    have : IsEmpty ↥(f ⁻¹ᵁ (⊥ : S.Opens)).toScheme := ⟨fun x => x.2⟩
    exact ⟨⟨by rw [Set.univ_eq_empty_iff.2 ‹IsEmpty _›]; exact isCompact_empty⟩,
      fun x => isEmptyElim x⟩
  · have hVt : V = ⊤ := TopologicalSpace.Opens.ext (Set.eq_univ_of_forall fun z => by
      rw [Subsingleton.elim z y]; exact hy)
    subst hVt
    have : IsIso (f ⁻¹ᵁ (⊤ : S.Opens)).ι := inferInstanceAs (IsIso X.topIso.hom)
    have := isInvertible_pullback (f ⁻¹ᵁ (⊤ : S.Opens)).ι L
    exact (Stacks.AmpleBridge.isAmple_iff_isAmple _ _).mpr
      (isAmple_pullback_of_isIso (f ⁻¹ᵁ (⊤ : S.Opens)).ι L h)

/-- Over an affine base with a single point, an invertible sheaf is ample precisely when it is
ample relative to the structure morphism. This is the equivalence of conditions (1) and (2) of
[Stacks, Tag 01VT] in that case. -/
public theorem isRelativelyAmple_iff_isAmple [IsAffine S] [Subsingleton ↥S] :
    Stacks.RelativeAmple.IsRelativelyAmple f L ↔ IsAmple X L :=
  ⟨isAmple_of_isRelativelyAmple f L, isRelativelyAmple_of_isAmple f L⟩

end AlgebraicGeometry.Scheme.Modules

end
