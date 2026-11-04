module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import StacksFrontier.AlgebraicGeometry.LimitIndexReduction.Basic
public import StacksFrontier.AlgebraicGeometry.ModuleDescent.InvertibleInput

/-!
# Descent of an invertible module through a limit of schemes, reduced to one input

Stacks Tag 0B8W asserts that an invertible module on the cofiltered limit of a system of
quasi-compact and quasi-separated schemes with affine transition morphisms is pulled back from an
invertible module at some stage of the system. The statement leaves both index universes free of
the universe of the schemes.

This file reduces that assertion to a **single** statement, at the **smallest** index shape: the
same descent for *finite locally free modules of rank one*, over an index category whose objects
and morphisms both live in the universe of the schemes.

## Route

The index category may be replaced by the cofiltered category `CategoryTheory.Quotient D.homRel`
and, when the index objects are `u`-small, then by its `CategoryTheory.SmallModel`, whose objects
and morphisms lie in `Type u`, without changing the limit or the hypotheses on the system. On a
scheme, a module is invertible if and only if it is finite locally free of rank one (Tag 0B8M).

## Main definitions

* `Stacks.InvertibleLimitDescentReduction.RankOneLimitDescent`: descent of a rank-one finite
  locally free module through a cofiltered limit, index objects and morphisms in the universe of
  the schemes.
* `Stacks.InvertibleLimitDescentReduction.InvertibleLimitDescent`: descent of an invertible module
  through a cofiltered limit, at the same index shape.

## Main results

* `Stacks.InvertibleLimitDescentReduction.invertibleLimitDescent_iff_rankOneLimitDescent`: the
  invertible and the rank-one descent statements are equivalent.
* `Stacks.InvertibleLimitDescentReduction.exists_isInvertible_pullback_iso_of_isLimit`: the
  reduction, with the index objects in an arbitrary universe and the index morphisms in another,
  under `Small.{u} I`.
* `Stacks.InvertibleLimitDescentReduction.exists_isInvertible_pullback_iso_of_isLimit_max`: the
  same with the schemes in `max u w` and the index objects in `Type w`, so that `Small` is
  discharged by instance search and **no** hypothesis on the index survives.

## Implementation notes

Both results take `Stacks.InvertibleLimitDescentReduction.RankOneLimitDescent` as a hypothesis, so
neither carries a Tag 0B8W attribute.

`Stacks.InvertibleLimitDescentReduction.RankOneLimitDescent` is stated with the limit cone and its
limit property as explicit arguments and the three geometric conditions as instance arguments,
matching the shape in which `Stacks.LimitIndexReduction.essentiallySmall_reduction` delivers them.

Transport of the conclusion back to a stage of the original system is by definitional unfolding
rather than by rewriting: an object of `CategoryTheory.Quotient D.homRel` is a one-field structure
on the objects of `I`, so, in namespace `Stacks.LimitIndexReduction`, `(diagram D).obj a` is
`D.obj a.as` and `(diagramCone D c).π.app a` is `c.π.app a.as`, both by `rfl`.

## References

* [Stacks Project, Tag 0B8W](https://stacks.math.columbia.edu/tag/0B8W)
* [Stacks Project, Tag 0B8M](https://stacks.math.columbia.edu/tag/0B8M)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

universe v w u

namespace Stacks.InvertibleLimitDescentReduction

/-- **Descent of rank-one finite locally free modules through a limit.** A finite locally free
module of rank one on the limit of a cofiltered system of quasi-compact and quasi-separated schemes
with affine transition morphisms is pulled back, up to isomorphism, from a finite locally free
module of rank one at some stage. The index objects and the index morphisms both live in the
universe of the schemes. -/
def RankOneLimitDescent : Prop :=
  ∀ {J : Type u} [Category.{u} J] [IsCofiltered J] (E : J ⥤ Scheme.{u})
    [∀ {a b : J} (g : a ⟶ b), IsAffineHom (E.map g)]
    [∀ a : J, CompactSpace (E.obj a)] [∀ a : J, QuasiSeparatedSpace (E.obj a)]
    (t : Cone E), IsLimit t → ∀ (F : t.pt.Modules),
      SheafOfModules.IsFiniteLocallyFreeOfRank (R := t.pt.ringCatSheaf) F 1 →
        ∃ (a : J) (Fa : (E.obj a).Modules),
          SheafOfModules.IsFiniteLocallyFreeOfRank (R := (E.obj a).ringCatSheaf) Fa 1 ∧
            Nonempty (F ≅ (Scheme.Modules.pullback (t.π.app a)).obj Fa)

/-- **Descent of invertible modules through a limit.** An invertible module on the limit of a
cofiltered system of quasi-compact and quasi-separated schemes with affine transition morphisms is
pulled back, up to isomorphism, from an invertible module at some stage. The index objects and the
index morphisms both live in the universe of the schemes, as in
`Stacks.InvertibleLimitDescentReduction.RankOneLimitDescent`. -/
def InvertibleLimitDescent : Prop :=
  ∀ {J : Type u} [Category.{u} J] [IsCofiltered J] (E : J ⥤ Scheme.{u})
    [∀ {a b : J} (g : a ⟶ b), IsAffineHom (E.map g)]
    [∀ a : J, CompactSpace (E.obj a)] [∀ a : J, QuasiSeparatedSpace (E.obj a)]
    (t : Cone E), IsLimit t → ∀ (F : t.pt.Modules),
      SheafOfModules.IsInvertible t.pt.sheaf.obj t.pt.ringCatSheaf.property F →
        ∃ (a : J) (Fa : (E.obj a).Modules),
          SheafOfModules.IsInvertible (E.obj a).sheaf.obj (E.obj a).ringCatSheaf.property Fa ∧
            Nonempty (F ≅ (Scheme.Modules.pullback (t.π.app a)).obj Fa)

/-- **The invertible and the rank-one descent statements are equivalent.**
`Stacks.InvertibleLimitDescentReduction.InvertibleLimitDescent` holds if and only if
`Stacks.InvertibleLimitDescentReduction.RankOneLimitDescent` holds, at the same universe. -/
theorem invertibleLimitDescent_iff_rankOneLimitDescent :
    InvertibleLimitDescent.{u} ↔ RankOneLimitDescent.{u} := by
  constructor
  · intro h J _ _ E _ _ _ t ht F hF
    obtain ⟨a, Fa, hFa, e⟩ := h E t ht F
      (Stacks.ModuleDescent.isInvertible_of_isFiniteLocallyFreeOfRank_one t.pt F hF)
    exact ⟨a, Fa, Stacks.ModuleDescent.isFiniteLocallyFreeOfRank_one_of_isInvertible _ Fa hFa, e⟩
  · intro h J _ _ E _ _ _ t ht F hF
    obtain ⟨a, Fa, hFa, e⟩ := h E t ht F
      (Stacks.ModuleDescent.isFiniteLocallyFreeOfRank_one_of_isInvertible t.pt F hF)
    exact ⟨a, Fa, Stacks.ModuleDescent.isInvertible_of_isFiniteLocallyFreeOfRank_one _ Fa hFa, e⟩

/-- **Descent of invertible modules through a limit, given
`Stacks.InvertibleLimitDescentReduction.RankOneLimitDescent`.** An invertible module on the limit
of a cofiltered system of quasi-compact and quasi-separated schemes with affine transition
morphisms is pulled back from an invertible module at some stage, granted the rank-one case at a
`u`-small index category.

The index morphisms live in an arbitrary universe `v`, and the index objects in an arbitrary
universe `w` subject only to `Small.{u} I`. -/
theorem exists_isInvertible_pullback_iso_of_isLimit
    (hDescent : RankOneLimitDescent.{u})
    {I : Type w} [Category.{v} I] [IsCofiltered I] [Small.{u} I]
    (D : I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)]
    [∀ i : I, CompactSpace (D.obj i)]
    [∀ i : I, QuasiSeparatedSpace (D.obj i)]
    (L : c.pt.Modules)
    (hL : SheafOfModules.IsInvertible c.pt.sheaf.obj c.pt.ringCatSheaf.property L) :
    ∃ (i : I) (Lᵢ : (D.obj i).Modules),
      SheafOfModules.IsInvertible (D.obj i).sheaf.obj (D.obj i).ringCatSheaf.property Lᵢ ∧
        Nonempty (L ≅ (Scheme.Modules.pullback (c.π.app i)).obj Lᵢ) := by
  let E₀ := LimitIndexReduction.diagram D
  let t₀ := LimitIndexReduction.diagramCone D c
  let e := equivSmallModel.{u} (LimitIndexReduction.Index D)
  let : IsCofiltered (SmallModel.{u} (LimitIndexReduction.Index D)) :=
    IsCofiltered.of_equivalence e
  let E := e.inverse ⋙ E₀
  have ht : IsLimit (t₀.whisker e.inverse) :=
    (LimitIndexReduction.isLimitDiagramCone D hc).whiskerEquivalence e.symm
  let : ∀ {a b} (g : a ⟶ b), IsAffineHom (E.map g) :=
    fun g => inferInstanceAs (IsAffineHom (E₀.map (e.inverse.map g)))
  let : ∀ a, CompactSpace (E.obj a) :=
    fun a => inferInstanceAs (CompactSpace (E₀.obj (e.inverse.obj a)))
  let : ∀ a, QuasiSeparatedSpace (E.obj a) :=
    fun a => inferInstanceAs (QuasiSeparatedSpace (E₀.obj (e.inverse.obj a)))
  obtain ⟨a, Fa, hFa, eFa⟩ := hDescent E (t₀.whisker e.inverse) ht L
    (Stacks.ModuleDescent.isFiniteLocallyFreeOfRank_one_of_isInvertible c.pt L hL)
  exact ⟨(e.inverse.obj a).as, Fa,
    Stacks.ModuleDescent.isInvertible_of_isFiniteLocallyFreeOfRank_one _ Fa hFa, eFa⟩

/-- **Descent of invertible modules through a limit indexed by `Type w`, given
`Stacks.InvertibleLimitDescentReduction.RankOneLimitDescent`.** With the schemes in
`Scheme.{max u w}` and the index objects in `Type w`, an invertible module on the limit of a
cofiltered system of quasi-compact and quasi-separated schemes with affine transition morphisms is
pulled back from an invertible module at some stage, with no smallness hypothesis on the index
category. -/
theorem exists_isInvertible_pullback_iso_of_isLimit_max
    (hDescent : RankOneLimitDescent.{max u w})
    {I : Type w} [Category.{v} I] [IsCofiltered I]
    (D : I ⥤ Scheme.{max u w}) (c : Cone D) (hc : IsLimit c)
    [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)]
    [∀ i : I, CompactSpace (D.obj i)]
    [∀ i : I, QuasiSeparatedSpace (D.obj i)]
    (L : c.pt.Modules)
    (hL : SheafOfModules.IsInvertible c.pt.sheaf.obj c.pt.ringCatSheaf.property L) :
    ∃ (i : I) (Lᵢ : (D.obj i).Modules),
      SheafOfModules.IsInvertible (D.obj i).sheaf.obj (D.obj i).ringCatSheaf.property Lᵢ ∧
        Nonempty (L ≅ (Scheme.Modules.pullback (c.π.app i)).obj Lᵢ) :=
  exists_isInvertible_pullback_iso_of_isLimit hDescent D c hc L hL

end Stacks.InvertibleLimitDescentReduction

end
