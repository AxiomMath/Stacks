module

public import StacksFrontier.AlgebraicGeometry.ModuleLimits.CanonicalFullyFaithful
public import StacksFrontier.AlgebraicGeometry.ModuleLimits.DescendResidue
public import StacksFrontier.AlgebraicGeometry.PullbackInvertible.Basic

/-!
# Descent of finitely presented and of invertible modules, from Tag 01ZR (2)

Let `c` be a limit cone on a cofiltered diagram `D` of quasi-compact quasi-separated schemes
with affine transition morphisms.  This file records what follows for such a system from
[Stacks Project, Tag 01ZR] (2) in the canonically pinned form
`Stacks.AlgebraicGeometry.ModuleLimits.HasCanonicalDescent` and nothing else:

* part (1) of the same tag — every finitely presented module on the limit is the pullback of a
  finitely presented module at a stage;
* clause (2) of [Stacks Project, Tag 0B8W] — every invertible module on the limit is the
  pullback of an invertible module at a stage.

Both are obtained by supplying the hypotheses of statements already in the library with the
reductions of `...ModuleLimits.CanonicalFullyFaithful`, so the content here is the bookkeeping
that identifies Tag 01ZR (2) as the *single* remaining input for either.  Neither statement
carries a tag attribute: the tags assert their parts unconditionally.

## Main results

* `...ModuleLimits.exists_isFinitePresentation_pullback_iso_of_hasCanonicalDescent`:
  [Stacks Project, Tag 01ZR] (1) in the general quasi-compact quasi-separated case, from
  Tag 01ZR (2) alone.  This is
  `exists_isFinitePresentation_pullback_iso_of_upToIso_map` with its `hmap` hypothesis supplied
  by `hasCanonicalDescent_upToIso`.
* `...ModuleLimits.exists_isInvertible_pullback_iso_of_hasCanonicalDescent`:
  [Stacks Project, Tag 0B8W] (2) from Tag 01ZR (2) alone.  This is
  `exists_isInvertible_pullback_iso_of_isLimit_of_descent` with *both* of its hypotheses
  supplied — `hDescend` by the previous statement and `hFullyFaithful` by
  `exists_pullback_iso_of_hasCanonicalDescent`.

## Implementation notes

The index object universe is the universe of the schemes, because
`...ModuleLimits.EventualMapEq.exists_pullback_map_eq_of_isLimit'` — Tag 01ZR (3) in the general
case, used for the faithfulness half — is proved at that shape; the index *morphism* universe is
free.  Tag 0B8W (2) itself is universe polymorphic in the index objects
(`exists_isInvertible_pullback_iso_of_isLimit_of_descent` is stated that way), so the
restriction here comes from Tag 01ZR, not from Tag 0B8W.

Which `IsInvertible`: `AlgebraicGeometry.SheafOfModules.IsInvertible`, the class
`exists_isInvertible_pullback_iso_of_isLimit_of_descent` is stated for.

## References

* [Stacks Project, Tag 01ZR](https://stacks.math.columbia.edu/tag/01ZR)
* [Stacks Project, Tag 0B8W](https://stacks.math.columbia.edu/tag/0B8W)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry.SheafOfModules (IsInvertible)

universe v u

namespace Stacks.AlgebraicGeometry.ModuleLimits

variable {I : Type u} [Category.{v} I] [IsCofiltered I] (D : I ⥤ Scheme.{u}) (c : Cone D)
  [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)]
  [∀ i : I, CompactSpace (D.obj i)] [∀ i : I, QuasiSeparatedSpace (D.obj i)]

/-- **[Stacks Project, Tag 01ZR] (1)** in the general quasi-compact quasi-separated case, from
part (2) of the same tag in the canonically pinned form and nothing else: every finitely
presented module on the limit of a cofiltered system of quasi-compact quasi-separated schemes
with affine transition morphisms is the pullback of a finitely presented module at some stage. -/
theorem exists_isFinitePresentation_pullback_iso_of_hasCanonicalDescent (hc : IsLimit c)
    (hmap : HasCanonicalDescent D c) (F : c.pt.Modules) [F.IsFinitePresentation] :
    ∃ (i : I) (Fᵢ : (D.obj i).Modules), Fᵢ.IsFinitePresentation ∧
      Nonempty (F ≅ (Scheme.Modules.pullback (c.π.app i)).obj Fᵢ) :=
  exists_isFinitePresentation_pullback_iso_of_upToIso_map D c hc
    (fun i F G hF hG φ => hasCanonicalDescent_upToIso D c hmap i F G hF hG φ) F

/-- **[Stacks Project, Tag 0B8W] (2)** from [Stacks Project, Tag 01ZR] (2) in the canonically
pinned form and nothing else: every invertible module on the limit of a cofiltered system of
quasi-compact quasi-separated schemes with affine transition morphisms is the pullback of an
invertible module at some stage. -/
theorem exists_isInvertible_pullback_iso_of_hasCanonicalDescent (hc : IsLimit c)
    (hmap : HasCanonicalDescent D c) (L : c.pt.Modules)
    (hL : IsInvertible c.pt.sheaf.obj c.pt.ringCatSheaf.property L) :
    ∃ (i : I) (Lᵢ : (D.obj i).Modules),
      IsInvertible (D.obj i).sheaf.obj (D.obj i).ringCatSheaf.property Lᵢ ∧
        Nonempty (L ≅ (Scheme.Modules.pullback (c.π.app i)).obj Lᵢ) :=
  exists_isInvertible_pullback_iso_of_isLimit_of_descent D c
    (fun F hF => @exists_isFinitePresentation_pullback_iso_of_hasCanonicalDescent
      _ _ _ D c _ _ _ hc hmap F hF)
    (fun i A B hA hB h => exists_pullback_iso_of_hasCanonicalDescent D c hc hmap i A B hA hB h)
    L hL

end Stacks.AlgebraicGeometry.ModuleLimits

end
