module

public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.ConormalChartAssociatedModule

/-!
# A presented étale chart of a closed subspace, restricted to a smaller ambient chart

`StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.ConormalChartAssociatedModule` identifies the
inverse image of the conormal module `𝒞_{Z/X'}` to the small étale site of a chart of `Z` cut out
by a cartesian square

```
T --incl--> U'
|           |
c           |
v           v
Z --------> X'
```

with the associated module of the Zariski conormal sheaf of `incl`,
`AlgebraicGeometry.Space.conormalModulePresentedChartAssociatedIso`.  This file supplies the data
that a *second* such presentation over a smaller ambient chart `m : V' ⟶ U'` produces, which is
what a naturality square for that identification is stated against.

The point of the file is the **cartesian square of the two base-changed subspaces**: the range of
`incl₂` inside the chart space of `V'` is the base change of the range of `incl` inside the chart
space of `U'` along `AlgebraicGeometry.Space.chartMap`.  Granted that, the two étale charts of
`X'` compose — `AlgebraicGeometry.Space.chartMap_comp_chartToSpace` — and so the functoriality of
[Stacks Project, Tag 04CO] in the étale source,
`AlgebraicGeometry.Space.conormalModuleEtaleRestrictionCanonicalIso_comp`, applies to the two
presentations at once.  That is the [Stacks Project, Tag 04CO] factor of the identification above.

## Main definitions

* `AlgebraicGeometry.Space.presentedRangeMap`: **the morphism of the two base-changed subspaces of
  the two chart spaces**, induced by a morphism `σ : T₂ ⟶ T` of the two presenting objects.

## Main results

* `AlgebraicGeometry.Space.isPullback_presentedChartMap`: the square of the two presenting closed
  immersions over `m` is cartesian.  It is the presenting square of the smaller chart with the
  presenting square of the bigger one cancelled off underneath, by
  `CategoryTheory.IsPullback.of_bot`.
* `AlgebraicGeometry.Space.presentedRangeMap_square` and
  `AlgebraicGeometry.Space.isPullback_presentedRangeMap`: **the square of the two base-changed
  subspaces commutes and is cartesian** — the two hypotheses that
  `AlgebraicGeometry.Space.conormalModuleEtaleRestrictionCanonicalIso` asks of the lower stage.
  They are the square above read through the comparison
  `AlgebraicGeometry.Space.rangeIsoPresheaf` of each presenting object with the range of its
  closed immersion.
* `AlgebraicGeometry.Space.presentedSubspaceRangeMap_comp`: the projection to `Z` of the smaller
  base-changed subspace factors through the bigger one, which is what makes the two stages of the
  composition law meet.
* `AlgebraicGeometry.Space.conormalModuleEtaleRestrictionCanonicalIso_congr` and
  `AlgebraicGeometry.Space.conormalModuleEtaleRestrictionCanonicalIso_hom_eq_of_eq`: the two
  congruences in the arguments of the identification of [Stacks Project, Tag 04CO] which the
  composition law has to be read across.

## Why the two congruences are needed, and why they are two

The composition law states the identification at the *composites* `g ≫ g'` and `f ≫ f'`, while
`AlgebraicGeometry.Space.conormalModulePresentedChartAssociatedIso` at the smaller presentation
reads it at `AlgebraicGeometry.Space.chartToSpace` of `V'` and at
`AlgebraicGeometry.Space.presentedSubspaceRangeMap` of the smaller presentation.  Those agree with
the composites, by `AlgebraicGeometry.Space.chartMap_comp_chartToSpace` and by
`AlgebraicGeometry.Space.presentedSubspaceRangeMap_comp`, but the two agreements have to be used
differently:

* the étale morphism `g` occurs in the identification's type **only inside propositions**, so a
  change of `g` is a plain equation of isomorphisms and `subst` plus proof irrelevance proves it —
  that is `.._congr`;
* the morphism `f` of subspaces occurs in the type, under
  `AlgebraicGeometry.Space.modulePullback`, so a change of `f` can only be an equation of
  `CategoryTheory.eqToHom`-transported morphisms — that is `.._hom_eq_of_eq`, whose object
  equality is taken as a hypothesis rather than as a `congrArg` so that proof irrelevance frees
  the consumer from matching the proof term.

No `@[stacks]` attribute is claimed: Tags 03FU, 03LU, 04CO and 04G2 (1) are registered where the
constructions they name are built, and what is proved here is the restriction data those
constructions are read at, which is an interior step of [Stacks Project, Tag 04AM].

## References

* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 04AM](https://stacks.math.columbia.edu/tag/04AM)
* [Stacks Project, Tag 04CO](https://stacks.math.columbia.edu/tag/04CO)
* [Stacks Project, Tag 04G2](https://stacks.math.columbia.edu/tag/04G2)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The two congruences in the identification of Stacks 04CO -/

section Congr

variable {X X₂ : AlgebraicSpaces B S hS}

/-- **The identification of [Stacks Project, Tag 04CO] depends on the étale morphism only through
the propositions naming it.**  The morphism `g` does not occur in the identification's type, so
two spellings of it give isomorphisms of one type, and substituting one for the other leaves only
propositions to match. -/
theorem conormalModuleEtaleRestrictionCanonicalIso_congr
    (Zc : ClosedSubspaces B S hS X.1) (Z' : ClosedSubspaces B S hS X₂.1) {g g₂ : X ⟶ X₂}
    (f : (⟨Zc.1.toFunctor, Zc.2.1⟩ : AlgebraicSpaces B S hS) ⟶
      (⟨Z'.1.toFunctor, Z'.2.1⟩ : AlgebraicSpaces B S hS))
    (hgg : g = g₂)
    (hsq : subspaceInclusion B S hS X Zc ≫ g = f ≫ subspaceInclusion B S hS X₂ Z')
    (hcart : IsPullback Zc.1.ι f.hom g.hom Z'.1.ι) (hg : IsEtale B S hS g.hom)
    (hsq₂ : subspaceInclusion B S hS X Zc ≫ g₂ = f ≫ subspaceInclusion B S hS X₂ Z')
    (hcart₂ : IsPullback Zc.1.ι f.hom g₂.hom Z'.1.ι) (hg₂ : IsEtale B S hS g₂.hom) :
    conormalModuleEtaleRestrictionCanonicalIso B S hS Zc Z' g f hsq hcart hg =
      conormalModuleEtaleRestrictionCanonicalIso B S hS Zc Z' g₂ f hsq₂ hcart₂ hg₂ := by
  subst hgg
  rfl

/-- **The identification of [Stacks Project, Tag 04CO] at two spellings of the morphism of
subspaces.**  That morphism occurs in the identification's type, under
`AlgebraicGeometry.Space.modulePullback`, so the two readings differ by a transport; the object
equality is a hypothesis, so that proof irrelevance frees the consumer from producing it as a
particular `congrArg`. -/
theorem conormalModuleEtaleRestrictionCanonicalIso_hom_eq_of_eq
    (Zc : ClosedSubspaces B S hS X.1) (Z' : ClosedSubspaces B S hS X₂.1) (g : X ⟶ X₂)
    {f f₂ : (⟨Zc.1.toFunctor, Zc.2.1⟩ : AlgebraicSpaces B S hS) ⟶
      (⟨Z'.1.toFunctor, Z'.2.1⟩ : AlgebraicSpaces B S hS)}
    (hff : f = f₂)
    (hsq : subspaceInclusion B S hS X Zc ≫ g = f ≫ subspaceInclusion B S hS X₂ Z')
    (hcart : IsPullback Zc.1.ι f.hom g.hom Z'.1.ι) (hg : IsEtale B S hS g.hom)
    (hsq₂ : subspaceInclusion B S hS X Zc ≫ g = f₂ ≫ subspaceInclusion B S hS X₂ Z')
    (hcart₂ : IsPullback Zc.1.ι f₂.hom g.hom Z'.1.ι)
    (e : (modulePullback B S hS f).obj (conormalModule B S hS X₂ Z') =
      (modulePullback B S hS f₂).obj (conormalModule B S hS X₂ Z')) :
    (conormalModuleEtaleRestrictionCanonicalIso B S hS Zc Z' g f hsq hcart hg).hom =
      eqToHom e ≫
        (conormalModuleEtaleRestrictionCanonicalIso B S hS Zc Z' g f₂ hsq₂ hcart₂ hg).hom := by
  subst hff
  rw [eqToHom_refl, Category.id_comp]

end Congr

/-! ### The restriction data of a presented chart -/

section Restriction

variable {X' : AlgebraicSpaces B S hS}
variable (Z : ClosedSubspaces B S hS X'.1) (U' V' : SmallEtale B S hS X'.1) (m : V' ⟶ U')
    {T T₂ : BigFppfOver B S hS}
    (incl : T ⟶ (SmallEtale.toOver B S hS X'.1).obj U')
    (hincl : AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map incl))
    (c : yoneda.obj T ⟶ Z.1.toFunctor)
    (hpb : IsPullback (yoneda.map incl) c U'.1.hom Z.1.ι)
    (incl₂ : T₂ ⟶ (SmallEtale.toOver B S hS X'.1).obj V')
    (hincl₂ : AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map incl₂))
    (c₂ : yoneda.obj T₂ ⟶ Z.1.toFunctor)
    (hpb₂ : IsPullback (yoneda.map incl₂) c₂ V'.1.hom Z.1.ι)
    (σ : T₂ ⟶ T)
    (hσ : σ ≫ incl = incl₂ ≫ (SmallEtale.toOver B S hS X'.1).map m)
    (hσc : yoneda.map σ ≫ c = c₂)

include hpb hpb₂ hσ hσc in
/-- **The square of the two presenting closed immersions over the morphism of ambient charts is
cartesian.**  The presenting square of the smaller chart is the presenting square of the bigger
one with this square stacked on top, so cancelling the bigger one off underneath leaves this one
cartesian: that is `CategoryTheory.IsPullback.of_bot`, with the bottom square `hpb` and the outer
rectangle `hpb₂` read through the two factorizations `hσc` and the triangle of `m` over `X'`. -/
theorem isPullback_presentedChartMap :
    IsPullback (yoneda.map incl₂) (yoneda.map σ)
      (yoneda.map ((SmallEtale.toOver B S hS X'.1).map m)) (yoneda.map incl) := by
  refine IsPullback.of_bot (h₂₁ := yoneda.map incl) ?_ ?_ hpb
  · have hV : yoneda.map ((SmallEtale.toOver B S hS X'.1).map m) ≫ U'.1.hom = V'.1.hom :=
      CostructuredArrow.w _
    rw [hσc, hV]
    exact hpb₂
  · rw [← Functor.map_comp, ← Functor.map_comp, hσ]

/-- **The morphism of the two base-changed subspaces of the two chart spaces.**  The range of
`incl₂` is a closed subspace of the chart space of `V'` and the range of `incl` one of the chart
space of `U'`; the morphism between them is `σ` read through the comparison
`AlgebraicGeometry.Space.rangeIsoPresheaf` of each presenting object with its range. -/
noncomputable def presentedRangeMap :
    closedSubspaceRangeSpace B S hS incl₂ hincl₂ ⟶ closedSubspaceRangeSpace B S hS incl hincl :=
  ObjectProperty.homMk ((rangeIsoPresheaf B S hS incl₂ hincl₂).inv ≫
    yoneda.map σ ≫ (rangeIsoPresheaf B S hS incl hincl).hom)

include hσ in
/-- The square of the two base-changed subspaces commutes: the inclusion of the smaller one
followed by the morphism of chart spaces is the morphism of base-changed subspaces followed by the
inclusion of the bigger one. -/
theorem presentedRangeMap_square :
    subspaceInclusion B S hS (chartSpace B S hS X' V')
          (closedSubspaceRange B S hS incl₂ hincl₂) ≫ chartMap B S hS X' m =
      presentedRangeMap B S hS U' V' incl hincl incl₂ hincl₂ σ ≫
        subspaceInclusion B S hS (chartSpace B S hS X' U')
          (closedSubspaceRange B S hS incl hincl) := by
  apply ObjectProperty.hom_ext
  change (Subfunctor.range (yoneda.map incl₂)).ι ≫
      yoneda.map ((SmallEtale.toOver B S hS X'.1).map m) =
    ((rangeIsoPresheaf B S hS incl₂ hincl₂).inv ≫
      yoneda.map σ ≫ (rangeIsoPresheaf B S hS incl hincl).hom) ≫
      (Subfunctor.range (yoneda.map incl)).ι
  have h1 : (rangeIsoPresheaf B S hS incl hincl).hom ≫
      (Subfunctor.range (yoneda.map incl)).ι = yoneda.map incl :=
    Subfunctor.toRange_ι (yoneda.map incl)
  have h2 : (rangeIsoPresheaf B S hS incl₂ hincl₂).inv ≫ yoneda.map incl₂ =
      (Subfunctor.range (yoneda.map incl₂)).ι :=
    (Iso.inv_comp_eq _).2 (Subfunctor.toRange_ι (yoneda.map incl₂)).symm
  rw [Category.assoc, Category.assoc, h1, ← h2, Category.assoc,
    ← Functor.map_comp, ← Functor.map_comp, hσ]

/-- `σ` followed by the comparison with the range of `incl` is the comparison with the range of
`incl₂` followed by `presentedRangeMap`, at the level of presheaf morphisms. -/
private theorem yoneda_map_comp_rangeIsoPresheaf_hom_eq :
    yoneda.map σ ≫ (rangeIsoPresheaf B S hS incl hincl).hom =
      (rangeIsoPresheaf B S hS incl₂ hincl₂).hom ≫
        (presentedRangeMap B S hS U' V' incl hincl incl₂ hincl₂ σ).hom := by
  change _ = _ ≫ ((rangeIsoPresheaf B S hS incl₂ hincl₂).inv ≫
    yoneda.map σ ≫ (rangeIsoPresheaf B S hS incl hincl).hom)
  rw [← Category.assoc, Iso.hom_inv_id, Category.id_comp]

/-- **The identification of each presenting object with the range of its closed immersion is
natural in the presenting object.**  The morphism of algebraic spaces represented by `σ`, followed
by the identification `AlgebraicGeometry.Space.rangeSpaceIso` of `T` with the range of `incl`, is
the identification of `T₂` with the range of `incl₂` followed by the morphism
`AlgebraicGeometry.Space.presentedRangeMap` of the two ranges.

No commutation hypothesis is needed: `AlgebraicGeometry.Space.presentedRangeMap` is `σ` conjugated
by the two identifications, so this is the cancellation of one of them.  It is the junction at
which a naturality square for
`AlgebraicGeometry.Space.conormalModulePresentedChartAssociatedIso` crosses from the two
base-changed subspaces of the chart spaces to the two presenting objects of the site, which is the
reading the comparison of [Stacks Project, Tag 04G2] (1) is stated at. -/
theorem representedSpaceMap_comp_rangeSpaceIso_hom :
    representedSpaceMap B S hS σ ≫ (rangeSpaceIso B S hS incl hincl).hom =
      (rangeSpaceIso B S hS incl₂ hincl₂).hom ≫
        presentedRangeMap B S hS U' V' incl hincl incl₂ hincl₂ σ := by
  apply ObjectProperty.hom_ext
  exact yoneda_map_comp_rangeIsoPresheaf_hom_eq B S hS U' V' incl hincl incl₂ hincl₂ σ

include hpb hpb₂ hσ hσc in
/-- **The square of the two base-changed subspaces is cartesian.**  It is
`AlgebraicGeometry.Space.isPullback_presentedChartMap` with the two presenting objects replaced by
the ranges of their closed immersions, along `AlgebraicGeometry.Space.rangeIsoPresheaf`, by
`CategoryTheory.IsPullback.of_iso`. -/
theorem isPullback_presentedRangeMap :
    IsPullback (closedSubspaceRange B S hS incl₂ hincl₂).1.ι
      (presentedRangeMap B S hS U' V' incl hincl incl₂ hincl₂ σ).hom
      (chartMap B S hS X' m).hom (closedSubspaceRange B S hS incl hincl).1.ι :=
  (isPullback_presentedChartMap B S hS Z U' V' m incl c hpb incl₂ c₂ hpb₂ σ hσ hσc).of_iso
    (rangeIsoPresheaf B S hS incl₂ hincl₂) (Iso.refl _)
    (rangeIsoPresheaf B S hS incl hincl) (Iso.refl _)
    (by
      change yoneda.map incl₂ ≫ 𝟙 _ =
        Subfunctor.toRange (yoneda.map incl₂) ≫ (Subfunctor.range (yoneda.map incl₂)).ι
      rw [Category.comp_id, Subfunctor.toRange_ι])
    (yoneda_map_comp_rangeIsoPresheaf_hom_eq B S hS U' V' incl hincl incl₂ hincl₂ σ)
    (by
      change yoneda.map ((SmallEtale.toOver B S hS X'.1).map m) ≫ 𝟙 _ =
        𝟙 _ ≫ yoneda.map ((SmallEtale.toOver B S hS X'.1).map m)
      rw [Category.comp_id, Category.id_comp])
    (by
      change yoneda.map incl ≫ 𝟙 _ =
        Subfunctor.toRange (yoneda.map incl) ≫ (Subfunctor.range (yoneda.map incl)).ι
      rw [Category.comp_id, Subfunctor.toRange_ι])

include hσc in
/-- **The projection to `Z` of the smaller base-changed subspace factors through the bigger
one.**  This is what makes the two stages of the composition law of [Stacks Project, Tag 04CO]
meet: the lower stage's morphism of subspaces is
`AlgebraicGeometry.Space.presentedRangeMap` and the upper stage's is the projection of the bigger
presentation. -/
theorem presentedSubspaceRangeMap_comp :
    presentedSubspaceRangeMap B S hS Z V' incl₂ hincl₂ c₂ =
      presentedRangeMap B S hS U' V' incl hincl incl₂ hincl₂ σ ≫
        presentedSubspaceRangeMap B S hS Z U' incl hincl c := by
  apply ObjectProperty.hom_ext
  change (rangeIsoPresheaf B S hS incl₂ hincl₂).inv ≫ c₂ =
    ((rangeIsoPresheaf B S hS incl₂ hincl₂).inv ≫
      yoneda.map σ ≫ (rangeIsoPresheaf B S hS incl hincl).hom) ≫
      ((rangeIsoPresheaf B S hS incl hincl).inv ≫ c)
  rw [Category.assoc, Category.assoc, ← Category.assoc
    (rangeIsoPresheaf B S hS incl hincl).hom, Iso.hom_inv_id, Category.id_comp, hσc]

end Restriction

end AlgebraicGeometry.Space

end
