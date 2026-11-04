module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.StrictHenselizationBaseChangeLimit

/-!
# The étale neighbourhood base change system of a morphism of schemes

Let `B` be a big étale site containing a scheme `S`, let `s` be a geometric point of `S` and let
`f : X ⟶ S` be a morphism of schemes. The base changes `X ×_S V` of `f` to the étale
neighbourhoods `(V, v)` of `s` form a diagram
`AlgebraicGeometry.etaleNeighborhoodBaseChangeDiagram` whose limit is
`X ×_S Spec(𝒪^{sh}_{S,s})`, by
`AlgebraicGeometry.isLimitStrictHenselizationBaseChangeCone`. This file records the structure
that diagram carries beyond being a diagram of schemes:

* every `X ×_S V` sits over `X`, compatibly with the transition morphisms — that is, the
  projections `X ×_S V ⟶ X` are the legs of a cocone with vertex `X`, and the legs of the limit
  cone followed by them are the projection `p : X ×_S Spec(𝒪^{sh}_{S,s}) ⟶ X`;
* over the small cofinal family of *affine* étale neighbourhoods the transition morphisms are
  affine;
* the structure morphisms `X ×_S V ⟶ V`, and the structure morphism
  `X ×_S Spec(𝒪^{sh}_{S,s}) ⟶ Spec(𝒪^{sh}_{S,s})` of the limit, are quasi-compact and
  quasi-separated as soon as `f` is.

## Main definitions

* `AlgebraicGeometry.etaleNeighborhoodBaseChangeCocone` — the projections `X ×_S V ⟶ X`, as a
  cocone with vertex `X`.
* `AlgebraicGeometry.etaleNeighborhoodBaseChangeAffineDiagram` — the diagram of base changes
  restricted to the small cofinal family of affine étale neighbourhoods.

## Main results

* `AlgebraicGeometry.strictHenselizationBaseChangeCone_π_comp_ι` — a leg of the limit cone
  followed by the projection to `X` is the projection
  `p : X ×_S Spec(𝒪^{sh}_{S,s}) ⟶ X`.
* `AlgebraicGeometry.isAffineHom_etaleNeighborhoodBaseChangeAffineDiagram_map` — **the transition
  morphisms of the affine subsystem are affine.**
* `AlgebraicGeometry.quasiCompact_etaleNeighborhoodBaseChange_fst`,
  `AlgebraicGeometry.quasiSeparated_etaleNeighborhoodBaseChange_fst`,
  `AlgebraicGeometry.quasiCompact_strictHenselizationBaseChange_fst`,
  `AlgebraicGeometry.quasiSeparated_strictHenselizationBaseChange_fst` — the structure morphisms
  of the levels and of the limit are quasi-compact and quasi-separated when `f` is.

## Implementation notes

The cocone with vertex `X` is `CategoryTheory.Over.forgetCocone` whiskered along the diagram of
base changes taken in the category of schemes over `X`; its naturality is therefore the
naturality of the forgetful cocone and needs no computation. Affineness of a transition morphism
is `CategoryTheory.MorphismProperty.overPullbackMap` — base change of an affine morphism is
affine — applied to the transition morphism of the neighbourhoods themselves, which is a
morphism between affine schemes and hence affine. Quasi-compactness and quasi-separatedness of
the structure morphisms are
`CategoryTheory.MorphismProperty.IsStableUnderBaseChange.of_isPullback` for the two properties,
both of which are stable under base change in Mathlib.

### What this file is for, and what it does not contain

[Stacks, Tag 03Q9] identifies the stalk `(R^n f_* ℱ)_s` of a higher direct image at a geometric
point with the étale cohomology group `H^n_ét(X ×_S Spec(𝒪^{sh}_{S,s}), p^{-1}ℱ)`, for `f`
quasi-compact and quasi-separated, an arbitrary base `S` and an arbitrary geometric point `s`.
In the library's vocabulary that conclusion reads

```
etaleStalk B S hS s (((Stacks.HigherDirectImage.pushforward B f).rightDerived n).obj ℱ).obj ≅
  ((smallEtaleGlobalSections B W).rightDerived n).obj
    ((smallEtaleBaseChange B p).sheafPullback AddCommGrpCat.{u + 1}
      (SmallEtale.topology B X.obj X.property)
      (SmallEtale.topology B W.obj W.property) |>.obj ℱ)
```

for `W` the scheme `X ×_S Spec(𝒪^{sh}_{S,s})` of the big étale site and `p : W ⟶ X` the
projection, and the `D^+(X_ét)` variant is the same with the right derived functors replaced by
the cohomology functors of the bounded below derived category.

Two of the three steps of the source's proof are in the library. The stalk is the colimit of the
cohomology presheaf over the neighbourhoods,
`Stacks.HigherDirectImage.higherDirectImageEtaleStalkIsoCohomologyStalk`, which is Tag 03Q8 and
invariance of a stalk under sheafification; and `X ×_S Spec(𝒪^{sh}_{S,s})` is the limit of the
`X ×_S V`, which is `AlgebraicGeometry.isLimitStrictHenselizationBaseChangeCone`. The third step
is Tag 03Q6 — that étale cohomology turns that limit of schemes into the colimit of the
cohomology groups of the levels. The assembled statement is
`AlgebraicGeometry.stalkHigherDirectImageIso`, with its complex and derived-category forms, in
`StacksFrontier/AlgebraicGeometry/EtaleCohomology/StalkHigherDirectImageStrictHenselization.lean`;
nothing in this file assumes it.

## References

* [Stacks Project, Tag 03Q9](https://stacks.math.columbia.edu/tag/03Q9)
* [Stacks Project, Tag 03Q6](https://stacks.math.columbia.edu/tag/03Q6)
* [Stacks Project, Tag 01YX](https://stacks.math.columbia.edu/tag/01YX)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

universe u

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (s : GeometricPoint S)
  {X : Scheme.{u}} (f : X ⟶ S)

/-! ### The projections to the source -/

/-- The projections `X ×_S V ⟶ X` of the base changes of `f` to the étale neighbourhoods of `s`,
as a cocone with vertex `X`: the forgetful cocone of the category of schemes over `X`, whiskered
along the diagram of base changes taken over `X`. -/
abbrev etaleNeighborhoodBaseChangeCocone :
    Cocone (etaleNeighborhoodBaseChangeDiagram B S hS s f) :=
  Cocone.whisker (etaleNeighborhoodOverDiagram B S hS s ⋙ Over.pullback f)
    (Over.forgetCocone X)

/-- The vertex of `etaleNeighborhoodBaseChangeCocone` is `X`. -/
@[simp]
theorem etaleNeighborhoodBaseChangeCocone_pt :
    (etaleNeighborhoodBaseChangeCocone B S hS s f).pt = X :=
  rfl

/-- The leg of `etaleNeighborhoodBaseChangeCocone` at an étale neighbourhood `V` of `s` is the
second projection `V ×_S X ⟶ X`. -/
@[simp]
theorem etaleNeighborhoodBaseChangeCocone_ι_app
    (V : (geometricPointFiber B S hS s).Elements) :
    (etaleNeighborhoodBaseChangeCocone B S hS s f).ι.app V =
      pullback.snd (B.inclusion.map V.1.obj.hom) f :=
  rfl

/-- **A leg of the limit cone, followed by the projection to `X`, is the projection
`p : X ×_S Spec(𝒪^{sh}_{S,s}) ⟶ X`.** This is the compatibility that makes the inverse image
`p^{-1}ℱ` of an abelian sheaf on `X` the limit term of the system of inverse images of `ℱ` along
the projections `X ×_S V ⟶ X`. -/
theorem strictHenselizationBaseChangeCone_π_comp_ι
    (V : (geometricPointFiber B S hS s).Elements) :
    (strictHenselizationBaseChangeCone B S hS s f).π.app V ≫
        (etaleNeighborhoodBaseChangeCocone B S hS s f).ι.app V =
      pullback.snd (strictHenselizationToBase B S hS s) f :=
  strictHenselizationBaseChangeCone_π_app_comp_snd B S hS s f V

/-! ### The affine subsystem and its affine transition morphisms -/

/-- The diagram `(V, v) ↦ X ×_S V` restricted to the small cofinal family of affine étale
neighbourhoods of `s`. -/
abbrev etaleNeighborhoodBaseChangeAffineDiagram :
    etaleNeighborhoodAffineIndex B S hS s ⥤ Scheme.{u} :=
  etaleNeighborhoodAffineInclusion B S hS s ⋙ etaleNeighborhoodBaseChangeDiagram B S hS s f

/-- **The transition morphisms of the affine subsystem are affine.** The transition morphism
`X ×_S V ⟶ X ×_S V'` is the base change along `X ×_S V' ⟶ V'` of the transition morphism
`V ⟶ V'` of the neighbourhoods, and the latter is a morphism of affine schemes, hence affine. -/
instance isAffineHom_etaleNeighborhoodBaseChangeAffineDiagram_map
    {a b : etaleNeighborhoodAffineIndex B S hS s} (g : a ⟶ b) :
    IsAffineHom ((etaleNeighborhoodBaseChangeAffineDiagram B S hS s f).map g) :=
  MorphismProperty.overPullbackMap f
    ((etaleNeighborhoodOverDiagram B S hS s).map
      ((etaleNeighborhoodAffineInclusion B S hS s).map g))
    (inferInstanceAs
      (IsAffineHom ((etaleNeighborhoodAffineDiagram B S hS s).map g)))

/-! ### Quasi-compactness and quasi-separatedness of the structure morphisms -/

section Qcqs

variable [QuasiCompact f] [QuasiSeparated f]

omit [QuasiSeparated f] in
/-- The structure morphism `X ×_S V ⟶ V` of a level is quasi-compact, being a base change of
`f`. -/
theorem quasiCompact_etaleNeighborhoodBaseChange_fst
    (V : (geometricPointFiber B S hS s).Elements) :
    QuasiCompact (pullback.fst (B.inclusion.map V.1.obj.hom) f) :=
  inferInstance

omit [QuasiCompact f] in
/-- The structure morphism `X ×_S V ⟶ V` of a level is quasi-separated, being a base change of
`f`. -/
theorem quasiSeparated_etaleNeighborhoodBaseChange_fst
    (V : (geometricPointFiber B S hS s).Elements) :
    QuasiSeparated (pullback.fst (B.inclusion.map V.1.obj.hom) f) :=
  inferInstance

omit [QuasiSeparated f] in
/-- The structure morphism `X ×_S Spec(𝒪^{sh}_{S,s}) ⟶ Spec(𝒪^{sh}_{S,s})` of the limit is
quasi-compact, being a base change of `f`. -/
theorem quasiCompact_strictHenselizationBaseChange_fst :
    QuasiCompact (pullback.fst (strictHenselizationToBase B S hS s) f) :=
  inferInstance

omit [QuasiCompact f] in
/-- The structure morphism `X ×_S Spec(𝒪^{sh}_{S,s}) ⟶ Spec(𝒪^{sh}_{S,s})` of the limit is
quasi-separated, being a base change of `f`. -/
theorem quasiSeparated_strictHenselizationBaseChange_fst :
    QuasiSeparated (pullback.fst (strictHenselizationToBase B S hS s) f) :=
  inferInstance

end Qcqs

end AlgebraicGeometry

end
