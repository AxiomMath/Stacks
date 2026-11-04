module

public import StacksFrontier.AlgebraicGeometry.Stacks.ClosedSubsetSeparationAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.EtaleChartDiagramTest
public import StacksFrontier.AlgebraicGeometry.Stacks.FinitePresentationDescentComposition
public import StacksFrontier.AlgebraicGeometry.Stacks.FlatDescentAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.GerbeFlatFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiCompactFiniteCoverDescent
public import StacksFrontier.AlgebraicGeometry.Stacks.ReducedUniquePointStack
public import StacksFrontier.AlgebraicGeometry.Stacks.ReducedUniquePointStackFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Stacks.SelfIntersectionChartTwoIso

/-!
# Descending flatness and local finite presentation from a slice of a charted self-intersection

Let `p : U ⟶ 𝒴` be a smooth 1-morphism from the algebraic stack represented by a scheme `U` of
the site, let `P` be a 2-commutative square over the cospan `(p, p)` — for instance a 2-fibre
product `U ×_𝒴 U` — charted by a morphism `c : h_R ⟶ F` out of a scheme `R` of the site, and
write `a = chartLeg … P.fst` and `b = chartLeg … P.snd` for the two induced morphisms of schemes
`R ⟶ U`.

Suppose a closed-or-open piece `ι : Z ⟶ U` of the chart is covered, through `a`, by a piece
`j : T ⟶ R` of the relation: that is, there is `k : T ⟶ Z` with `k ≫ ι = j ≫ a`, with `k` flat,
locally of finite presentation and surjective. Then `Z ⟶ U ⟶ 𝒴` is flat and locally of finite
presentation as soon as `T ⟶ R ⟶ U` taken along the *other* leg `b` is flat and locally of
finite presentation as a morphism of schemes.

This is the descent step of the chart construction of Stacks 06MF: the slice `T` of the relation
is flat and locally finitely presented over `U` via `b`, hence over `𝒴` via `b ≫ p`, hence over
`𝒴` via `a ≫ p` because the two agree up to the square's filler; and that composite factors
through `Z`, along a cover, so **Stacks 06Q0** and **Stacks 06Q9** push the two properties down
to `Z ⟶ 𝒴`.

## Main results

* `AlgebraicGeometry.Stack.isFlat_schemeStackMap`,
  `AlgebraicGeometry.Stack.isLocallyOfFinitePresentation_schemeStackMap`: two scheme-level
  properties, read on the 1-morphism of represented algebraic stacks; the third, surjectivity, is
  the base's `AlgebraicGeometry.Stack.isSurjective_schemeStackMap`
  (`StacksFrontier.AlgebraicGeometry.Stacks.EtaleChartDiagramTest`).
* `AlgebraicGeometry.Stack.isFlat_and_isLocallyOfFinitePresentation_chartedSlice`: the descent
  described above.

## Implementation notes

The 2-isomorphism that the argument turns on is
`AlgebraicGeometry.Stack.nonempty_twoIso_chartLeg_comp`; everything else here is bookkeeping,
namely the associators of the bicategory of algebraic stacks and the functoriality
`AlgebraicGeometry.Stack.schemeStackMap_comp` of the 2-Yoneda construction, which turn the four
composites into one another.

The hypothesis on `k` is stated as flatness, local finite presentation and surjectivity on
points of the morphism of schemes rather than as smoothness, since that is what the two descent
lemmas consume; a smooth surjective `k`, which is what the construction produces, has all
three.

No `@[stacks]` attribute is claimed: this is a step of Stacks 06MF, not the whole tag, and the
two descent inputs carry their own attributes (**Stacks 06Q0** on
`AlgebraicGeometry.Stack.AlgebraicStacks.isFlat_of_isSurjective_of_isFlat_comp` and
**Stacks 06Q9** on
`AlgebraicGeometry.Stack.AlgebraicStacks.isLocallyOfFinitePresentation_of_comp_of_fppf`).

## References

* [Stacks Project, Tag 06MF](https://stacks.math.columbia.edu/tag/06MF)
* [Stacks Project, Tag 06Q0](https://stacks.math.columbia.edu/tag/06Q0)
* [Stacks Project, Tag 06Q9](https://stacks.math.columbia.edu/tag/06Q9)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **A flat morphism of schemes of the site induces a flat 1-morphism of represented algebraic
stacks**, by `AlgebraicGeometry.Stack.isFlat_schemeFibredCategoryMap`. -/
theorem isFlat_schemeStackMap {V U : BigFppfOver B S hS} (k : V ⟶ U)
    (hk : Flat ((BigFppfOver.toScheme B S hS).map k)) :
    AlgebraicStacks.IsFlat B S hS (schemeStackMap.{u, w} B S hS k) :=
  isFlat_schemeFibredCategoryMap.{u, w} B S hS k hk

/-- **A morphism of schemes of the site locally of finite presentation induces a 1-morphism of
represented algebraic stacks locally of finite presentation**, by
`AlgebraicGeometry.Stack.isLocallyOfFinitePresentation_schemeFibredCategoryMap`. -/
theorem isLocallyOfFinitePresentation_schemeStackMap {V U : BigFppfOver B S hS} (k : V ⟶ U)
    (hk : LocallyOfFinitePresentation ((BigFppfOver.toScheme B S hS).map k)) :
    AlgebraicStacks.IsLocallyOfFinitePresentation B S hS (schemeStackMap.{u, w} B S hS k) :=
  isLocallyOfFinitePresentation_schemeFibredCategoryMap.{u, w} B S hS k hk

variable {𝒴 : AlgebraicStacks.{u, w} B S hS} (U : BigFppfOver B S hS)
  (p : schemeStack.{u, w} B S hS U ⟶ 𝒴) (P : Bicategory.TwoCommSq p p)
  (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
  (eF : StacksRepresentableCFG.EquivalenceOver P.pt.val.val.p
    (presheafOfCategories (F ⋙ typeToCat)).p)
  (R : BigFppfOver B S hS) (c : yoneda.obj R ⟶ F)

/-- Functoriality of the 2-Yoneda construction, with the associator of the bicategory of algebraic
stacks, as an isomorphism of composites with `p`. -/
private def schemeStackMap_comp_comp_iso {V W : BigFppfOver B S hS} (f : V ⟶ W) (g : W ⟶ U) :
    schemeStackMap.{u, w} B S hS (f ≫ g) ≫ p ≅
      schemeStackMap.{u, w} B S hS f ≫ (schemeStackMap.{u, w} B S hS g ≫ p) :=
  eqToIso (congrArg (fun q => q ≫ p) (schemeStackMap_comp.{u, w} B S hS f g).symm) ≪≫
    Bicategory.associator _ _ p

/-- **The two composites `T ⟶ U ⟶ 𝒴` through the two legs of a charted square are
2-isomorphic.** This is `AlgebraicGeometry.Stack.nonempty_twoIso_chartLeg_comp` whiskered by
`j : T ⟶ R` and rewritten by functoriality of the 2-Yoneda construction, with the two
associators of the bicategory of algebraic stacks inserted. -/
theorem nonempty_twoIso_comp_chartLeg_restrict (T : BigFppfOver B S hS) (j : T ⟶ R) :
    Nonempty (schemeStackMap.{u, w} B S hS
        (j ≫ chartLeg B S hS U p P F eF R c P.fst) ≫ p ≅
      schemeStackMap.{u, w} B S hS (j ≫ chartLeg B S hS U p P F eF R c P.snd) ≫ p) := by
  obtain ⟨e⟩ := nonempty_twoIso_chartLeg_comp B S hS U p P F eF R c
  exact ⟨schemeStackMap_comp_comp_iso B S hS U p j _ ≪≫
    Bicategory.whiskerLeftIso (schemeStackMap.{u, w} B S hS j) e ≪≫
    (schemeStackMap_comp_comp_iso B S hS U p j _).symm⟩

/-- **The descent step of the chart construction.** Let `p : U ⟶ 𝒴` be smooth, let `P` be a
2-commutative square over `(p, p)` charted by `c : h_R ⟶ F`, with legs `a` and `b` read as
morphisms of schemes `R ⟶ U`, and let `ι : Z ⟶ U`, `j : T ⟶ R` and `k : T ⟶ Z` satisfy
`k ≫ ι = j ≫ a` with `k` flat, locally of finite presentation and surjective. If `j ≫ b` is flat
and locally of finite presentation as a morphism of schemes, then `Z ⟶ U ⟶ 𝒴` is flat and
locally of finite presentation.

The composite `T ⟶ Z ⟶ U ⟶ 𝒴` equals `T ⟶ R ⟶ U ⟶ 𝒴` through `a`, which is 2-isomorphic to the
same through `b` by `AlgebraicGeometry.Stack.nonempty_twoIso_comp_chartLeg_restrict`; the latter
is flat and locally of finite presentation, `p` being smooth, and the two properties then descend
along the surjective flat locally finitely presented `T ⟶ Z` by **Stacks 06Q0** and
**Stacks 06Q9**. -/
theorem isFlat_and_isLocallyOfFinitePresentation_chartedSlice
    (hp : AlgebraicStacks.IsSmooth B S hS p)
    (Z T : BigFppfOver B S hS) (ι : Z ⟶ U) (j : T ⟶ R) (k : T ⟶ Z)
    (hcomm : k ≫ ι = j ≫ chartLeg B S hS U p P F eF R c P.fst)
    (hkflat : Flat ((BigFppfOver.toScheme B S hS).map k))
    (hklfp : LocallyOfFinitePresentation ((BigFppfOver.toScheme B S hS).map k))
    (hksurj : ∀ x : (BigFppfOver.toScheme B S hS).obj Z,
      x ∈ Set.range ((BigFppfOver.toScheme B S hS).map k).base)
    (hbflat : Flat ((BigFppfOver.toScheme B S hS).map
      (j ≫ chartLeg B S hS U p P F eF R c P.snd)))
    (hblfp : LocallyOfFinitePresentation ((BigFppfOver.toScheme B S hS).map
      (j ≫ chartLeg B S hS U p P F eF R c P.snd))) :
    AlgebraicStacks.IsFlat B S hS (schemeStackMap.{u, w} B S hS ι ≫ p) ∧
      AlgebraicStacks.IsLocallyOfFinitePresentation B S hS
        (schemeStackMap.{u, w} B S hS ι ≫ p) := by
  obtain ⟨e⟩ := nonempty_twoIso_comp_chartLeg_restrict B S hS U p P F eF R c T j
  -- the composite `T ⟶ Z ⟶ 𝒴` is the composite `T ⟶ R ⟶ 𝒴` through the first leg
  have hfac : schemeStackMap.{u, w} B S hS k ≫ (schemeStackMap.{u, w} B S hS ι ≫ p) ≅
      schemeStackMap.{u, w} B S hS (j ≫ chartLeg B S hS U p P F eF R c P.fst) ≫ p :=
    (schemeStackMap_comp_comp_iso B S hS U p k ι).symm ≪≫
      eqToIso (congrArg (fun q => schemeStackMap.{u, w} B S hS q ≫ p) hcomm)
  -- the composite through the second leg is flat and locally of finite presentation
  have hbtotalflat : AlgebraicStacks.IsFlat B S hS
      (schemeStackMap.{u, w} B S hS (j ≫ chartLeg B S hS U p P F eF R c P.snd) ≫ p) :=
    AlgebraicStacks.isFlat_comp B S hS _ _
      (isFlat_schemeStackMap.{u, w} B S hS _ hbflat)
      (AlgebraicStacks.isFlat_of_isSmooth B S hS p hp)
  have hbtotallfp : AlgebraicStacks.IsLocallyOfFinitePresentation B S hS
      (schemeStackMap.{u, w} B S hS (j ≫ chartLeg B S hS U p P F eF R c P.snd) ≫ p) :=
    AlgebraicStacks.isLocallyOfFinitePresentation_comp B S hS _ _
      (isLocallyOfFinitePresentation_schemeStackMap.{u, w} B S hS _ hblfp)
      (AlgebraicStacks.isLocallyOfFinitePresentation_of_isSmooth B S hS p hp)
  have hktotal : schemeStackMap.{u, w} B S hS k ≫ (schemeStackMap.{u, w} B S hS ι ≫ p) ≅
      schemeStackMap.{u, w} B S hS (j ≫ chartLeg B S hS U p P F eF R c P.snd) ≫ p :=
    hfac ≪≫ e
  refine ⟨AlgebraicStacks.isFlat_of_isSurjective_of_isFlat_comp B S hS
      (schemeStackMap.{u, w} B S hS k) (schemeStackMap.{u, w} B S hS ι ≫ p)
      ((AlgebraicStacks.isFlat_iff_of_twoIso B S hS _ _
        (Bicategory.InducedBicategory.isoHom hktotal.symm)).1 hbtotalflat)
      (isSurjective_schemeStackMap.{u, w} B S hS k hksurj)
      (isFlat_schemeStackMap.{u, w} B S hS k hkflat),
    AlgebraicStacks.isLocallyOfFinitePresentation_of_comp_of_fppf B S hS
      (schemeStackMap.{u, w} B S hS k) (schemeStackMap.{u, w} B S hS ι ≫ p)
      ((AlgebraicStacks.isLocallyOfFinitePresentation_iff_of_twoIso B S hS _ _
        (Bicategory.InducedBicategory.isoHom hktotal.symm)).1 hbtotallfp)
      (isSurjective_schemeStackMap.{u, w} B S hS k hksurj)
      (isFlat_schemeStackMap.{u, w} B S hS k hkflat)
      (isLocallyOfFinitePresentation_schemeStackMap.{u, w} B S hS k hklfp)⟩

end AlgebraicGeometry.Stack

end
