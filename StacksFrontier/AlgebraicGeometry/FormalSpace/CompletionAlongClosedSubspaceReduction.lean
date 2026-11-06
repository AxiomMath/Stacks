module

public import StacksFrontier.CategoryTheory.PullbackCancelMono
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionSubspaceBaseChange
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Reduction
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Representable
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.InvariantSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsOfPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsRepresentable
public import StacksFrontier.AlgebraicGeometry.Spaces.ReducedFactorThroughClosedSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.UniversalFirstOrderThickening
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Affine.ThickeningStage
public import StacksFrontier.CategoryTheory.SubfunctorFactor

/-!
# The reduction of the completion of an algebraic space along a closed subspace

Let `S` be a scheme contained in a big fppf site `B`, let `X` be an algebraic space over `S`
and let `Z ⊆ X` be a closed subspace. **Stacks 0GXW** says that the reduction of the
completion `X^∧_Z` of `X` along `Z` is `Z_red`, the reduced closed subspace of `X` supported
on the point set of `Z`.

The completion `X^∧_Z` is `AlgebraicGeometry.Space.completionSubspace`, the colimit
`colim Z_n` of the infinitesimal neighbourhoods of `Z` in `X` of Stacks 0GXU. Each `Z_n` has
the same point set as `Z` and `Z = Z_0 ⟶ Z_n` is a thickening, so the canonical morphism
`Z ⟶ X^∧_Z` is a stage of a colimit presentation with thickening transition morphisms and is
therefore representable and a thickening. That single property of the completion is all the
source's assertion rests on.

The reduction is then `Z_red ⟶ Z ⟶ X^∧_Z`: the second morphism is a representable thickening,
and the first one is a representable thickening because `Z_red` is a closed subspace of `X`
contained in `Z` with the same point set as `Z`, which is proved here.

This file proves the statement for *any* fppf sheaf receiving a representable thickening from
`Z` (`AlgebraicGeometry.FormalSpace.isReduction_of_isRepresentableThickening_closedSubspace`)
and constructs the morphism `Z ⟶ X^∧_Z`; that this morphism is a representable thickening, and
with it Stacks 0GXW itself, is
`StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionSubspaceThickening`, which needs the
comparison with the completion along the point set of `Z`.

## Main definitions

* `AlgebraicGeometry.FormalSpace.sheafOfAlgebraicSpace` is an algebraic space over `S` viewed
  as an fppf sheaf of `Type (u + 1)`, the value universe of the formal algebraic spaces.
* `AlgebraicGeometry.FormalSpace.closedSubspaceSheaf` is a closed subspace of `X` viewed that
  way, and `AlgebraicGeometry.FormalSpace.reductionOfClosedSubspace` is its reduction `Z_red`,
  the reduced closed subspace of `X` on the point set of `Z`, with
  `AlgebraicGeometry.FormalSpace.reductionOfClosedSubspaceSheaf` and
  `AlgebraicGeometry.FormalSpace.reductionInclusion` the corresponding sheaf and the inclusion
  `Z_red ⟶ Z`.
* `AlgebraicGeometry.FormalSpace.closedSubspaceToCompletionSubspace` is the canonical
  morphism `Z ⟶ X^∧_Z`, the stage `Z = Z_0` of the colimit presentation of Stacks 0GXU.

## Main results

* `AlgebraicGeometry.Space.reducedClosedSubspace_le_of_isClosedSubspace`: the reduced closed
  subspace of `X` on the point set of a closed subspace `Z` is contained in `Z`.
* `AlgebraicGeometry.Space.isThickening_homOfLe_of_range_subset`: a closed subspace contained
  in another one which has no more points includes into it by a representable thickening.
* `AlgebraicGeometry.Space.isThickening_of_isPullback_of_range_subset_of_isClosedSubspace`: the
  inverse image of a closed subspace along a scheme-valued point of the ambient space whose point
  set lands in the point set of the subspace is a thickening of its base.
* `AlgebraicGeometry.Space.isNthOrderThickening_top`: the whole of an algebraic space is an
  `n`th-order thickening of itself, for every `n`.
* `AlgebraicGeometry.FormalSpace.mono_of_isRepresentableThickeningULift`: a representable
  thickening of presheaves is a monomorphism.
* `AlgebraicGeometry.FormalSpace.isReduction_of_isRepresentableThickening`: a representable
  thickening of an fppf sheaf by a reduced algebraic space exhibits its source as the
  reduction of its target.
* `AlgebraicGeometry.FormalSpace.isReduction_of_isRepresentableThickening_closedSubspace`: the
  form of **Stacks 0GXW** proved here, at any fppf sheaf receiving a representable thickening
  from `Z`.
* `AlgebraicGeometry.FormalSpace.closedSubspaceToCompletionSubfunctor_comp_ι`: the canonical
  morphism `Z ⟶ X^∧_Z` is a morphism over `X`, before sheafifying.

`AlgebraicGeometry.Space.isNthOrderThickening_top` is what makes
`AlgebraicGeometry.FormalSpace.mem_completionSubspaceSubfunctor_of_mem` — every section of `Z`
is a section of the completion subfunctor, at order zero — and hence the morphism
`AlgebraicGeometry.FormalSpace.closedSubspaceToCompletionSubspace` exist at all.

`AlgebraicGeometry.Space.completionSheaf` is **not** the object of this statement. That is the
completion `X_{/T}` of `X` along the closed *subset* `T = |Z|` of Stacks 0AIX, and Stacks 0H8N
says the canonical morphism `X^∧_Z ⟶ X_{/T}` is an isomorphism when `Z ⟶ X` is of finite
presentation but not in general; the counterexample given there is
`A = ℤ[x₁, x₂, …]` with `I = (x₁, x₂, …)`. Formalizing 0GXW at `X_{/T}` would therefore be a
statement about a different formal algebraic space.

## Implementation notes

The reduction is expressed through `AlgebraicGeometry.FormalSpace.IsReduction`, the predicate
naming the defining properties of the reduction of a formal algebraic space, as in
`AlgebraicGeometry.FormalSpace.isReduction_formalSpectrum`: the conclusion is that a
canonically constructed morphism has those properties, so Stacks 0AIN — the existence of a
reduction — is not needed and no choice is involved.

`Z_red` is the datum `AlgebraicGeometry.Space.reducedClosedSubspace` at the point set
of `Z`, which is closed by Stacks 04CD. Its inclusion into `Z` is
`CategoryTheory.Subfunctor.homOfLe` at the containment `Z_red ≤ Z`, and that containment is
Stacks 03JJ applied to `Z_red`, which is reduced and has the same points as `Z`: the
factorization 03JJ produces is turned into a containment of subfunctors rather than kept as
data, so the inclusion is a construction and not a choice of a witness.

That the inclusion `Z_red ⟶ Z` is a thickening after every representable base change is where
the point sets are compared: the base change is a closed immersion because `Z_red` is a closed
subspace of `X`, and it is surjective because its point set is the preimage of the point set
of `Z_red`, which is all of the point set of `Z`. Stacks 03H4 produces the point of the base
change and Stacks 03H5 turns surjectivity on points into surjectivity.

The private helpers of this file duplicate, at file scope, the block of helpers that
`StacksFrontier.AlgebraicGeometry.FormalSpace.FormalSpectrumReduction` declares privately
(`exists_app_eq_of_isReduced`, `injective_app_of_isRepresentableThickening`,
`exists_app_eq_of_singleton_cover` and `existsUnique_comp_eq_of_hasEtaleLocalProperty`); they
are private there, hence not importable, and promoting them is a refactor of that file rather
than part of this result.

## References

* [Stacks Project, Tag 03H4](https://stacks.math.columbia.edu/tag/03H4)
* [Stacks Project, Tag 03JJ](https://stacks.math.columbia.edu/tag/03JJ)
* [Stacks Project, Tag 04CD](https://stacks.math.columbia.edu/tag/04CD)
* [Stacks Project, Tag 0GXU](https://stacks.math.columbia.edu/tag/0GXU)
* [Stacks Project, Tag 0GXW](https://stacks.math.columbia.edu/tag/0GXW)
* [Stacks Project, Tag 0H8N](https://stacks.math.columbia.edu/tag/0H8N)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Thickenings

universe u

namespace AlgebraicGeometry

attribute [local instance] Space.pointTopology

/-! ### Thickenings of schemes as a morphism property -/

/-- Thickenings of schemes are stable under composition: a composition of closed immersions is
a closed immersion, and a composition of surjections is a surjection. -/
private instance isThickening_isStableUnderComposition :
    MorphismProperty.IsStableUnderComposition
      (@Stacks.Thickenings.IsThickening : MorphismProperty Scheme.{u}) where
  comp_mem f g hf hg := by
    refine ⟨?_, ?_⟩
    · have _ := hf.1
      have _ := hg.1
      infer_instance
    · intro z
      obtain ⟨y, hy⟩ := hg.2 z
      obtain ⟨x, hx⟩ := hf.2 y
      exact ⟨x, by rw [Scheme.Hom.comp_apply, hx, hy]⟩

/-! ### Subfunctors -/

namespace Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Comparing two closed subspaces with the same points -/

/-- **The reduced closed subspace of `X` on the point set of a closed subspace `Z` of `X` is
contained in `Z`.** This is Stacks 03JJ applied to `Z_red`, which is reduced and whose point
set is the point set of `Z`: the factorization through `Z` that 03JJ produces exhibits every
section of `Z_red` as a section of `Z`. -/
theorem reducedClosedSubspace_le_of_isClosedSubspace
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (Z : Subfunctor X) (hZ : IsClosedSubspace B S hS Z) :
    reducedClosedSubspace B S hS X hX (Set.range (pointsMap B S hS Z.toFunctor Z.ι))
        (isClosed_range_pointsMap_of_isClosedImmersion B S hS hX Z.ι hZ.2) ≤ Z := by
  set T := Set.range (pointsMap B S hS Z.toFunctor Z.ι) with hTdef
  set hT := isClosed_range_pointsMap_of_isClosedImmersion B S hS hX Z.ι hZ.2 with hTeq
  set W := reducedClosedSubspace B S hS X hX T hT with hWdef
  have hWclosed : IsClosedSubspace B S hS W :=
    isClosedSubspace_reducedClosedSubspace B S hS X hX T hT
  obtain ⟨g, hg⟩ := (exists_lift_closedSubspace_iff_pointsMap_range_subset B S hS hX
      hWclosed.1 Z hZ
      (hasEtaleLocalProperty_isReduced_reducedClosedSubspace B S hS X hX T hT) W.ι).mpr
    (le_of_eq (range_pointsMap_ι_reducedClosedSubspace B S hS X hX T hT))
  exact Subfunctor.le_of_comp_eq_ι g hg

/-- The base change of a scheme-valued point `gs` of `X` along a subfunctor `Z` is surjective
if the point set of the base lands in the point set of `Z`. -/
private theorem surjective_map_of_isPullback_of_range_subset
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {Z : Subfunctor X}
    {a : BigFppfOver B S hS} {gs : yoneda.obj a ⟶ X}
    (hgs : Set.range (pointsMap B S hS (yoneda.obj a) gs) ⊆
      Set.range (pointsMap B S hS Z.toFunctor Z.ι))
    {b : BigFppfOver B S hS} {fst : yoneda.obj b ⟶ Z.toFunctor} {snd : b ⟶ a}
    (sq : IsPullback fst (yoneda.map snd) Z.ι gs) :
    Function.Surjective ((BigFppfOver.toScheme B S hS).map snd) := by
  rw [← surjective_pointsMap_yoneda_iff B S hS snd]
  intro pa
  obtain ⟨pz, hpz⟩ := hgs ⟨pa, rfl⟩
  obtain ⟨v, -, hv⟩ := exists_point_of_isPullback_presheaf B S hS sq pz pa hpz
  exact ⟨v, hv⟩

/-- **A closed subspace of `X` contained in a second closed subspace with no more points
includes into the second one by a representable thickening**: every representable base change
of the inclusion is a closed immersion, because the smaller subspace is a closed subspace of
`X`, and is surjective because the point set of the base change is the preimage of the point
set of the smaller subspace, which contains that of the larger one. -/
theorem isThickening_homOfLe_of_range_subset
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {W Z : Subfunctor X}
    (hW : IsClosedSubspace B S hS W)
    (hWZ : Set.range (pointsMap B S hS Z.toFunctor Z.ι) ⊆
      Set.range (pointsMap B S hS W.toFunctor W.ι))
    (hle : W ≤ Z) :
    (MorphismProperty.inverseImage (@Stacks.Thickenings.IsThickening.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (Subfunctor.homOfLe hle) := by
  have _ : (MorphismProperty.inverseImage (@Stacks.Thickenings.IsThickening.{u})
      (BigFppfOver.toScheme B S hS)).RespectsIso :=
    MorphismProperty.RespectsIso.inverseImage _ _
  apply MorphismProperty.relative.of_exists
  intro a ξ
  obtain ⟨P, j, i, hij⟩ := hW.2.1 (ξ ≫ Z.ι)
  refine ⟨P, i, j, isPullback_of_comp_mono Z.ι ?_, hW.2.2 (ξ ≫ Z.ι) i j hij,
    surjective_map_of_isPullback_of_range_subset B S hS ?_ hij⟩
  · rw [Subfunctor.homOfLe_ι]
    exact hij
  · rintro _ ⟨pa, rfl⟩
    refine hWZ ⟨pointsMap B S hS (yoneda.obj a) ξ pa, ?_⟩
    rw [pointsMap_comp]
    rfl

/-- **The inverse image of a closed subspace `Z` of `X` along a scheme-valued point of `X`
whose point set lands in `|Z|` is a thickening of that scheme.** It is a closed immersion
because `Z` is a closed subspace, and it is surjective because every point of the base is
carried into the point set of `Z`; Stacks 03H4 produces the point of the inverse image and
Stacks 03H5 turns surjectivity on points into surjectivity. -/
theorem isThickening_of_isPullback_of_range_subset_of_isClosedSubspace
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {Z : Subfunctor X} (hZ : IsClosedSubspace B S hS Z)
    {a : BigFppfOver B S hS} {gs : yoneda.obj a ⟶ X}
    (hgs : Set.range (pointsMap B S hS (yoneda.obj a) gs) ⊆
      Set.range (pointsMap B S hS Z.toFunctor Z.ι))
    {b : BigFppfOver B S hS} {fst : yoneda.obj b ⟶ Z.toFunctor} {snd : b ⟶ a}
    (sq : IsPullback fst (yoneda.map snd) Z.ι gs) :
    Stacks.Thickenings.IsThickening ((BigFppfOver.toScheme B S hS).map snd) :=
  ⟨hZ.2.property gs fst snd sq, surjective_map_of_isPullback_of_range_subset B S hS hgs sq⟩

/-! ### The whole of an algebraic space as a thickening of itself -/

/-- **An algebraic space is a thickening of itself of every order.** This is
`AlgebraicGeometry.Space.isNthOrderThickening'_top` with the topological clause of Stacks 05ZK
part (1) added: the inclusion of `⊤` is an isomorphism, hence surjective on points. -/
theorem isNthOrderThickening_top (n : ℕ) (X : AlgebraicSpaces B S hS) :
    IsNthOrderThickening B S hS n X ⊤ := by
  refine ⟨⟨isClosedSubspace_top B S hS X, fun y => ?_⟩,
    fun U => (isNthOrderThickening'_top B S hS n X).2 (op U)⟩
  refine ⟨pointsMap B S hS X.1 (inv (⊤ : Subfunctor X.1).ι) y, ?_⟩
  have h := congrFun (pointsMap_comp B S hS X.1 (inv (⊤ : Subfunctor X.1).ι)
    (⊤ : Subfunctor X.1).ι) y
  rw [IsIso.inv_hom_id, pointsMap_id] at h
  exact h.symm

end Space

namespace FormalSpace

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Transfers to the value universe of the formal algebraic spaces -/

/-- A relative morphism property of a morphism of presheaves of `Type u` relative to the
Yoneda embedding holds of its universe lift relative to the universe-lifted Yoneda embedding:
the universe lift of presheaves is fully faithful, so a represented base change computed
before lifting is a represented base change after lifting, and conversely. -/
theorem relative_uliftFunctor_of_presheaf
    {C : Type (u + 1)} [Category.{u} C] (P : MorphismProperty C)
    {X Y : Cᵒᵖ ⥤ Type u} (f : X ⟶ Y) (hf : P.presheaf f) :
    P.relative uliftYoneda.{u + 1} (Functor.whiskerRight f uliftFunctor.{u + 1}) := by
  let H : (Cᵒᵖ ⥤ Type u) ⥤ (Cᵒᵖ ⥤ Type (u + 1)) :=
    (Functor.whiskeringRight Cᵒᵖ (Type u) (Type (u + 1))).obj uliftFunctor.{u + 1}
  show P.relative (yoneda ⋙ H) (H.map f)
  refine ⟨?_, ?_⟩
  · intro a g
    obtain ⟨g₀, rfl⟩ := H.map_surjective g
    obtain ⟨b, snd, fst, hpb⟩ := hf.1 g₀
    exact ⟨b, snd, H.map fst, by simpa using hpb.map H⟩
  · intro a b g fst snd hpb
    obtain ⟨g₀, hg₀⟩ := H.map_surjective g
    obtain ⟨fst₀, hfst₀⟩ := H.map_surjective fst
    have hpbMap : IsPullback (H.map fst₀) (H.map (yoneda.map snd)) (H.map f) (H.map g₀) := by
      convert hpb using 1 <;> simp
    exact hf.2 g₀ fst₀ snd (hpbMap.of_map H
      (H.map_injective (by simpa only [Functor.map_comp] using hpbMap.w)))

/-- An algebraic space over `S` which has an étale-local property of schemes has it in the
value universe of the formal algebraic spaces: the atlas is the universe lift of an atlas
before lifting. -/
theorem hasEtaleLocalPropertyULift_comp_uliftFunctor
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (P : ObjectProperty Scheme.{u})
    [P.IsLocal Scheme.etalePrecoverage] (hF : Space.HasEtaleLocalProperty B S hS F P) :
    Space.HasEtaleLocalPropertyULift.{u + 1} B S hS (F ⋙ uliftFunctor.{u + 1}) P := by
  obtain ⟨U, f, hs, he, hU⟩ := hF
  exact ⟨U, Functor.whiskerRight f uliftFunctor.{u + 1},
    relative_uliftFunctor_of_presheaf _ f hs, relative_uliftFunctor_of_presheaf _ f he, hU⟩

/-- A composition of representable thickenings of presheaves in the value universe of the
formal algebraic spaces is a representable thickening. -/
theorem isRepresentableThickeningULift_comp
    {F G H : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (u + 1)} {a : F ⟶ G} {b : G ⟶ H}
    (ha : Space.IsRepresentableThickeningULift.{u + 1} B S hS a)
    (hb : Space.IsRepresentableThickeningULift.{u + 1} B S hS b) :
    Space.IsRepresentableThickeningULift.{u + 1} B S hS (a ≫ b) := by
  have _ : (MorphismProperty.inverseImage
      (@Stacks.Thickenings.IsThickening.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).IsStableUnderComposition :=
    MorphismProperty.IsStableUnderComposition.inverseImage
      (BigFppfOver.toScheme B S hS)
  exact MorphismProperty.comp_mem _ a b ha hb

/-! ### Factorization through a representable thickening -/

/-- A section of the target of a representable thickening over an object of the site with
reduced underlying scheme is the image of a section of the source: the base change of the
thickening to that object is a surjective closed immersion into a reduced scheme, hence an
isomorphism. -/
private theorem exists_app_eq_of_isReduced
    {Xr Xt : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (u + 1)} {m : Xr ⟶ Xt}
    (hm : Space.IsRepresentableThickeningULift.{u + 1} B S hS m)
    {T : BigFppfOver B S hS} (hT : IsReduced ((BigFppfOver.toScheme B S hS).obj T))
    (v : Xt.obj (op T)) : ∃ a : Xr.obj (op T), m.app (op T) a = v := by
  obtain ⟨b, snd, fst, sq⟩ := hm.rep (uliftYonedaEquiv.{u + 1}.symm v)
  obtain ⟨hclosed, hsurj⟩ := hm.property _ fst snd sq
  have _ : IsReduced ((BigFppfOver.toScheme B S hS).obj T) := hT
  have _ : IsClosedImmersion ((BigFppfOver.toScheme B S hS).map snd) := hclosed
  have _ : Surjective ((BigFppfOver.toScheme B S hS).map snd) := ⟨hsurj⟩
  have _ : IsIso ((BigFppfOver.toScheme B S hS).map snd) :=
    isIso_of_isClosedImmersion_of_surjective _
  have _ : IsIso snd := isIso_of_reflects_iso snd (BigFppfOver.toScheme B S hS)
  have _ : IsIso ((uliftYoneda.{u + 1}).map snd) := inferInstance
  refine ⟨uliftYonedaEquiv.{u + 1} (inv ((uliftYoneda.{u + 1}).map snd) ≫ fst), ?_⟩
  apply (uliftYonedaEquiv.{u + 1} (X := T) (F := Xt)).symm.injective
  rw [← uliftYonedaEquiv_comp, Equiv.symm_apply_apply, Category.assoc, sq.w,
    ← Category.assoc, IsIso.inv_hom_id, Category.id_comp]

/-- A representable thickening of presheaves is injective on sections: a lift of a section of
the target splits the base change of the thickening to the object carrying it, and a split
closed immersion is an isomorphism, so the lift is the unique one. -/
private theorem injective_app_of_isRepresentableThickening
    {Xr Xt : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (u + 1)} {m : Xr ⟶ Xt}
    (hm : Space.IsRepresentableThickeningULift.{u + 1} B S hS m)
    (T : BigFppfOver B S hS) : Function.Injective (m.app (op T)) := by
  intro a₁ a₂ he
  apply (uliftYonedaEquiv.{u + 1} (X := T) (F := Xr)).symm.injective
  obtain ⟨b, snd, fst, sq⟩ := hm.rep (uliftYonedaEquiv.{u + 1}.symm (m.app (op T) a₁))
  obtain ⟨hclosed, -⟩ := hm.property _ fst snd sq
  have hw₁ : uliftYonedaEquiv.{u + 1}.symm a₁ ≫ m
      = 𝟙 _ ≫ uliftYonedaEquiv.{u + 1}.symm (m.app (op T) a₁) := by
    rw [Category.id_comp]
    exact uliftYonedaEquiv_symm_comp a₁ m
  have hw₂ : uliftYonedaEquiv.{u + 1}.symm a₂ ≫ m
      = 𝟙 _ ≫ uliftYonedaEquiv.{u + 1}.symm (m.app (op T) a₁) := by
    rw [Category.id_comp, uliftYonedaEquiv_symm_comp, he]
  have _ : IsClosedImmersion ((BigFppfOver.toScheme B S hS).map snd) := hclosed
  have _ : Mono snd := (BigFppfOver.toScheme B S hS).mono_of_mono_map inferInstance
  have _ : IsSplitEpi snd := by
    refine IsSplitEpi.mk' ⟨(ULiftYoneda.fullyFaithful _).preimage (sq.lift _ (𝟙 _) hw₁), ?_⟩
    apply (ULiftYoneda.fullyFaithful (BigFppfOver B S hS)).map_injective
    rw [Functor.map_comp, Functor.FullyFaithful.map_preimage, sq.lift_snd]
    simp
  have _ : IsIso snd := isIso_of_mono_of_isSplitEpi snd
  have hl : sq.lift _ (𝟙 _) hw₁ = sq.lift _ (𝟙 _) hw₂ :=
    (cancel_mono ((uliftYoneda.{u + 1}).map snd)).mp (by rw [sq.lift_snd, sq.lift_snd])
  rw [← sq.lift_fst _ _ hw₁, ← sq.lift_fst _ _ hw₂, hl]

/-- **A representable thickening of presheaves is a monomorphism.** A morphism of presheaves
of types is a monomorphism as soon as it is injective on sections over every object, and a
representable thickening is. -/
theorem mono_of_isRepresentableThickeningULift
    {Xr Xt : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (u + 1)} {m : Xr ⟶ Xt}
    (hm : Space.IsRepresentableThickeningULift.{u + 1} B S hS m) : Mono m := by
  have happ : ∀ T : (BigFppfOver B S hS)ᵒᵖ, Mono (m.app T) := fun T ↦
    (mono_iff_injective (m.app T)).2
      (injective_app_of_isRepresentableThickening B S hS hm T.unop)
  exact NatTrans.mono_of_mono_app m

/-- A section of the target of a morphism of sheaves which is injective on sections and whose
restriction along one surjective étale morphism lifts is itself the image of a section: the
lifts over the arrows of the covering sieve generated by that morphism are compatible because
of injectivity, and their amalgamation is the required section. -/
private theorem exists_app_eq_of_singleton_cover
    {Xr Xt : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (u + 1)} {m : Xr ⟶ Xt}
    (hinj : ∀ T : BigFppfOver B S hS, Function.Injective (m.app (op T)))
    (hXr : Presheaf.IsSheaf (BigFppfOver.topology B S hS) Xr)
    (hXt : Presheaf.IsSheaf (BigFppfOver.topology B S hS) Xt)
    {T c : BigFppfOver B S hS} {π : c ⟶ T}
    (hcov : Sieve.generate (Presieve.singleton π) ∈ BigFppfOver.topology B S hS T)
    (v : Xt.obj (op T)) (a : Xr.obj (op c)) (ha : m.app (op c) a = Xt.map π.op v) :
    ∃ w : Xr.obj (op T), m.app (op T) w = v := by
  classical
  have key : ∀ ⦃Y : BigFppfOver B S hS⦄ (g : Y ⟶ T),
      (Sieve.generate (Presieve.singleton π)).arrows g →
      ∃ z : Xr.obj (op Y), m.app (op Y) z = Xt.map g.op v := by
    intro Y g hg
    obtain ⟨Z, e, g', hg', hfac⟩ := hg
    cases hg'
    refine ⟨Xr.map e.op a, ?_⟩
    rw [NatTrans.naturality_apply m e.op a, ha, ← Functor.map_comp_apply, ← op_comp, hfac]
  let x : Presieve.FamilyOfElements Xr (Sieve.generate (Presieve.singleton π)).arrows :=
    fun _ g hg => (key g hg).choose
  have hx : ∀ ⦃Y : BigFppfOver B S hS⦄ (g : Y ⟶ T)
      (hg : (Sieve.generate (Presieve.singleton π)).arrows g),
      m.app (op Y) (x g hg) = Xt.map g.op v := fun _ g hg => (key g hg).choose_spec
  have hxc : x.Compatible := by
    intro Y₁ Y₂ Z g₁ g₂ f₁ f₂ h₁ h₂ hcomm
    apply hinj Z
    rw [NatTrans.naturality_apply m g₁.op, NatTrans.naturality_apply m g₂.op, hx f₁ h₁,
      hx f₂ h₂, ← Functor.map_comp_apply, ← Functor.map_comp_apply, ← op_comp, ← op_comp,
      hcomm]
  obtain ⟨w, hw, -⟩ := ((isSheaf_iff_isSheaf_of_type _ _).mp hXr) _ hcov x hxc
  refine ⟨w, ?_⟩
  refine (((isSheaf_iff_isSheaf_of_type _ _).mp hXt) _ hcov).isSeparatedFor.ext
    fun Y g hg => ?_
  rw [← NatTrans.naturality_apply m g.op w, hw g hg, hx g hg]

/-- A morphism to the target of a representable thickening from a sheaf admitting a surjective
étale atlas by a reduced object of the site factors uniquely through the thickening: the
factorization exists over the atlas because the base change of a thickening to a reduced
object is an isomorphism, and it descends and is unique because a representable thickening is
injective on sections. -/
private theorem existsUnique_comp_eq_of_hasEtaleLocalProperty
    {X Xred : FppfSheaf B S hS} {i : Xred ⟶ X}
    (hm : Space.IsRepresentableThickeningULift.{u + 1} B S hS i.hom)
    (U : FppfSheaf B S hS)
    (hUred : Space.HasEtaleLocalPropertyULift.{u + 1} B S hS U.obj
      (fun T : Scheme.{u} ↦ IsReduced T))
    (f : U ⟶ X) : ∃! g : U ⟶ Xred, g ≫ i = f := by
  classical
  obtain ⟨W, p, hpsurj, hpetale, hWred⟩ := hUred
  obtain ⟨l, hl⟩ : ∃ l : (uliftYoneda.{u + 1}).obj W ⟶ Xred.obj, l ≫ i.hom = p ≫ f.hom := by
    obtain ⟨l₀, hl₀⟩ := exists_app_eq_of_isReduced B S hS hm hWred
      (uliftYonedaEquiv.{u + 1} (p ≫ f.hom))
    exact ⟨uliftYonedaEquiv.{u + 1}.symm l₀, by
      rw [uliftYonedaEquiv_symm_comp, hl₀, Equiv.symm_apply_apply]⟩
  have hinj₀ := injective_app_of_isRepresentableThickening B S hS hm
  have hex : ∀ (T : (BigFppfOver B S hS)ᵒᵖ) (s : U.obj.obj T),
      ∃ a : Xred.obj.obj T, i.hom.app T a = f.hom.app T s := by
    rintro ⟨T⟩ s
    obtain ⟨c, π, fstp, sqp⟩ := hpsurj.rep (uliftYonedaEquiv.{u + 1}.symm s)
    refine exists_app_eq_of_singleton_cover B S hS hinj₀ Xred.property X.property
      (Space.sieve_generate_singleton_mem_topology_over B S hS π
        (hpsurj.property _ fstp π sqp) (hpetale.property _ fstp π sqp))
      (f.hom.app (op T) s) (uliftYonedaEquiv.{u + 1} (fstp ≫ l)) ?_
    calc i.hom.app (op c) (uliftYonedaEquiv.{u + 1} (fstp ≫ l))
        = uliftYonedaEquiv.{u + 1} ((fstp ≫ l) ≫ i.hom) := (uliftYonedaEquiv_comp _ _).symm
      _ = uliftYonedaEquiv.{u + 1}
            ((uliftYoneda.{u + 1}).map π ≫ (uliftYonedaEquiv.{u + 1}.symm s ≫ f.hom)) := by
          rw [Category.assoc, hl, ← Category.assoc, sqp.w, Category.assoc]
      _ = X.obj.map π.op
            (uliftYonedaEquiv.{u + 1} (uliftYonedaEquiv.{u + 1}.symm s ≫ f.hom)) :=
          (uliftYonedaEquiv_naturality _ π.op).symm
      _ = X.obj.map π.op (f.hom.app (op T) s) := by
          rw [uliftYonedaEquiv_comp, Equiv.apply_symm_apply]
  choose a ha using hex
  refine ⟨⟨{ app := fun T => TypeCat.ofHom (a T), naturality := ?_ }⟩, ?_, ?_⟩
  · intro T T' k
    have hnat : ∀ s : U.obj.obj T, a T' (U.obj.map k s) = Xred.obj.map k (a T s) := by
      intro s
      apply hinj₀ T'.unop
      rw [ha, NatTrans.naturality_apply i.hom k, ha, NatTrans.naturality_apply f.hom k]
    exact TypeCat.homEquiv.injective (funext hnat)
  · refine Sheaf.hom_ext (NatTrans.ext (funext fun T => ?_))
    exact TypeCat.homEquiv.injective (funext (ha T))
  · intro φ hφ
    have huniq : ∀ (T : (BigFppfOver B S hS)ᵒᵖ) (s : U.obj.obj T),
        TypeCat.homEquiv (φ.hom.app T) s = a T s := by
      intro T s
      apply hinj₀ T.unop
      rw [ha]
      exact congrArg (fun ψ : U ⟶ X => TypeCat.homEquiv (ψ.hom.app T) s) hφ
    refine Sheaf.hom_ext (NatTrans.ext (funext fun T => ?_))
    exact TypeCat.homEquiv.injective (funext (huniq T))

/-! ### The reduction of a formal thickening -/

/-- **A representable thickening of an fppf sheaf by a reduced algebraic space exhibits its
source as the reduction of its target.** The two representability clauses are the hypothesis,
and the unique factorization of a morphism from a reduced algebraic space follows from it. -/
theorem isReduction_of_isRepresentableThickening {C R : FppfSheaf B S hS} (r : R ⟶ C)
    (hRalg : Space.IsAlgebraicSpaceULift.{u + 1} B S hS R.obj)
    (hRred : Space.HasEtaleLocalPropertyULift.{u + 1} B S hS R.obj
      (fun T : Scheme.{u} ↦ IsReduced T))
    (hr : Space.IsRepresentableThickeningULift.{u + 1} B S hS r.hom) :
    IsReduction B S hS C R r where
  algebraic := hRalg
  reduced := hRred
  representable := hr.rep
  thickening := hr.property
  universal := fun U _ hUred f ↦
    existsUnique_comp_eq_of_hasEtaleLocalProperty B S hS hr U hUred f

/-! ### The completion along a closed subspace and its reduction -/

/-- An algebraic space over `S` viewed as an fppf sheaf of `Type (u + 1)`, the value universe
of the formal algebraic spaces. -/
noncomputable def sheafOfAlgebraicSpace (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hF : IsAlgebraicSpace B S hS F) : FppfSheaf B S hS :=
  ⟨F ⋙ uliftFunctor.{u + 1},
    ((Space.isAlgebraicSpaceULift_comp_uliftFunctor_iff B S hS F).mpr hF).isSheaf⟩

variable {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
variable (Z : Subfunctor X) (hZ : Space.IsClosedSubspace B S hS Z)

/-- A closed subspace of an algebraic space over `S`, viewed as an fppf sheaf of
`Type (u + 1)`. -/
noncomputable def closedSubspaceSheaf : FppfSheaf B S hS :=
  sheafOfAlgebraicSpace B S hS Z.toFunctor hZ.1

/-- **The reduction `Z_red` of a closed subspace `Z` of an algebraic space `X` over `S`**: the
reduced closed subspace of `X` supported on the point set of `Z`, which is closed by Stacks
04CD. -/
noncomputable def reductionOfClosedSubspace : Subfunctor X :=
  Space.reducedClosedSubspace B S hS X hX (Set.range (Space.pointsMap B S hS Z.toFunctor Z.ι))
    (Space.isClosed_range_pointsMap_of_isClosedImmersion B S hS hX Z.ι hZ.2)

/-- `Z_red` is a closed subspace of `X`. -/
theorem isClosedSubspace_reductionOfClosedSubspace :
    Space.IsClosedSubspace B S hS (reductionOfClosedSubspace B S hS hX Z hZ) :=
  Space.isClosedSubspace_reducedClosedSubspace B S hS X hX _ _

/-- `Z_red` is contained in `Z`, by Stacks 03JJ. -/
theorem reductionOfClosedSubspace_le : reductionOfClosedSubspace B S hS hX Z hZ ≤ Z :=
  Space.reducedClosedSubspace_le_of_isClosedSubspace B S hS hX Z hZ

/-- `Z_red`, viewed as an fppf sheaf of `Type (u + 1)`. -/
noncomputable def reductionOfClosedSubspaceSheaf : FppfSheaf B S hS :=
  sheafOfAlgebraicSpace B S hS (reductionOfClosedSubspace B S hS hX Z hZ).toFunctor
    (isClosedSubspace_reductionOfClosedSubspace B S hS hX Z hZ).1

/-- The inclusion `Z_red ⟶ Z` of fppf sheaves. -/
noncomputable def reductionInclusion :
    reductionOfClosedSubspaceSheaf B S hS hX Z hZ ⟶ closedSubspaceSheaf B S hS Z hZ :=
  ObjectProperty.homMk (Functor.whiskerRight
    (Subfunctor.homOfLe (reductionOfClosedSubspace_le B S hS hX Z hZ)) uliftFunctor.{u + 1})

/-- **The inclusion `Z_red ⟶ Z` is a representable thickening.** -/
theorem isRepresentableThickeningULift_reductionInclusion :
    Space.IsRepresentableThickeningULift.{u + 1} B S hS
      (reductionInclusion B S hS hX Z hZ).hom :=
  relative_uliftFunctor_of_presheaf _ _
    (Space.isThickening_homOfLe_of_range_subset B S hS
      (isClosedSubspace_reductionOfClosedSubspace B S hS hX Z hZ)
      (le_of_eq (Space.range_pointsMap_ι_reducedClosedSubspace B S hS X hX _ _).symm)
      (reductionOfClosedSubspace_le B S hS hX Z hZ))

/-- **The reduction of a formal thickening of a closed subspace `Z` of `X` is `Z_red`.** If an
fppf sheaf `C` receives a representable thickening `c` from `Z`, then the composite
`Z_red ⟶ Z ⟶ C` exhibits `Z_red` as the reduction of `C`.

This is the form in which Stacks 0GXW is proved: see
`AlgebraicGeometry.FormalSpace.isReduction_completionSubspace'`, which is the statement at the
completion `X^∧_Z`. -/
theorem isReduction_of_isRepresentableThickening_closedSubspace {C : FppfSheaf B S hS}
    (c : closedSubspaceSheaf B S hS Z hZ ⟶ C)
    (hc : Space.IsRepresentableThickeningULift.{u + 1} B S hS c.hom) :
    IsReduction B S hS C (reductionOfClosedSubspaceSheaf B S hS hX Z hZ)
      (reductionInclusion B S hS hX Z hZ ≫ c) := by
  refine isReduction_of_isRepresentableThickening B S hS _
    ((Space.isAlgebraicSpaceULift_comp_uliftFunctor_iff B S hS _).mpr
      (isClosedSubspace_reductionOfClosedSubspace B S hS hX Z hZ).1)
    (hasEtaleLocalPropertyULift_comp_uliftFunctor B S hS _
      (Space.hasEtaleLocalProperty_isReduced_reducedClosedSubspace B S hS X hX _ _)) ?_
  exact isRepresentableThickeningULift_comp B S hS
    (isRepresentableThickeningULift_reductionInclusion B S hS hX Z hZ) hc

/-! ### The canonical morphism from a closed subspace into the completion -/

/-- A section of a subfunctor `Z` of `X` has inverse image of `Z` equal to the whole of the
presheaf represented by the object carrying it: the restrictions of a section of `Z` are
sections of `Z`. -/
theorem preimage_yonedaEquiv_symm_eq_top (W : Subfunctor X) {U : BigFppfOver B S hS}
    (g : X.obj (op U)) (hg : g ∈ W.obj (op U)) :
    (W.preimage (yonedaEquiv.symm g : yoneda.obj U ⟶ X)) = ⊤ := by
  rw [Subfunctor.preimage_eq_top_iff]
  intro V y hy
  obtain ⟨k, rfl⟩ := hy
  exact W.map k.op hg

/-- A section of a subfunctor `Z` of `X` is a section of the union of the infinitesimal
neighbourhoods of `Z`, at order zero: its inverse image of `Z` is everything, and the whole of
an algebraic space is a zeroth-order thickening of itself. -/
theorem mem_completionSubspaceSubfunctor_of_mem
    (W : Subfunctor X) (U : (BigFppfOver B S hS)ᵒᵖ)
    (g : (X ⋙ uliftFunctor.{u + 1}).obj U) (hg : g.down ∈ W.obj U) :
    g ∈ (Space.completionSubspaceSubfunctor B S hS ⟨X, hX⟩ W).obj U := by
  refine ⟨0, fun V k => ?_⟩
  rw [preimage_yonedaEquiv_symm_eq_top B S hS W g.down hg]
  rw [show ((⊤ : Subfunctor (yoneda.obj U.unop)).preimage k : Subfunctor (yoneda.obj V)) = ⊤ from
    (Subfunctor.preimage_eq_top_iff _ k).mpr le_top]
  exact Space.isNthOrderThickening_top B S hS 0 _

/-- The canonical morphism from a closed subspace `Z` of `X` into the union of the
infinitesimal neighbourhoods of `Z`, before sheafifying. -/
noncomputable def closedSubspaceToCompletionSubfunctor :
    Z.toFunctor ⋙ uliftFunctor.{u + 1} ⟶
      (Space.completionSubspaceSubfunctor B S hS ⟨X, hX⟩ Z).toFunctor where
  app U := ↾fun x => ⟨ULift.up x.down.1,
    mem_completionSubspaceSubfunctor_of_mem B S hS hX Z U (ULift.up x.down.1) x.down.2⟩
  naturality := by
    intro U V i
    ext x
    exact Subtype.ext (ULift.ext rfl)

/-- **The canonical morphism `Z ⟶ X^∧_Z` from a closed subspace into the completion of `X`
along it**, the stage `Z = Z_0` of the colimit presentation of Stacks 0GXU. -/
noncomputable def closedSubspaceToCompletionSubspace :
    closedSubspaceSheaf B S hS Z hZ ⟶ Space.completionSubspace B S hS ⟨X, hX⟩ Z :=
  ObjectProperty.homMk (closedSubspaceToCompletionSubfunctor B S hS hX Z ≫
    (BigFppfOver.topology B S hS).toSheafify
      (Space.completionSubspaceSubfunctor B S hS ⟨X, hX⟩ Z).toFunctor)

/-- The canonical morphism from `Z` into the union of the infinitesimal neighbourhoods of `Z`
is the inclusion of `Z` into `X`, read in the value universe of the formal algebraic
spaces. -/
theorem closedSubspaceToCompletionSubfunctor_comp_ι :
    closedSubspaceToCompletionSubfunctor B S hS hX Z ≫
        (Space.completionSubspaceSubfunctor B S hS ⟨X, hX⟩ Z).ι =
      Functor.whiskerRight Z.ι uliftFunctor.{u + 1} := rfl

/-- **Stacks 0GXW.** Let `X` be an algebraic space over `S` and let `Z ⊆ X` be a closed
subspace. The reduction of the completion `X^∧_Z` of `X` along `Z` is `Z_red`: the composite
`Z_red ⟶ Z ⟶ X^∧_Z` exhibits `Z_red` as the reduction of the completion.

The hypothesis is that the canonical morphism `Z ⟶ X^∧_Z` is a representable thickening. That
is exactly what it is: `Z = Z_0` is a stage of the colimit presentation of `X^∧_Z` by the
infinitesimal neighbourhoods of `Z`, whose transition morphisms are thickenings, so Stacks
0AI9 applies. The library has Stacks 0AI9 only for a colimit of *affine* objects of the site,
`AlgebraicGeometry.FormalSpace.isThickening_colimitι`, which is why the property is carried
here as a hypothesis; see the module docstring. -/
@[stacks 0GXW "the whole statement, under the additional hypothesis that the canonical \
morphism `Z ⟶ X^∧_Z` is a representable thickening; that is Tag 0AI9 for a colimit of \
algebraic spaces, which is available here only for a colimit of affine objects of the site"]
theorem isReduction_completionSubspace
    (hc : Space.IsRepresentableThickeningULift.{u + 1} B S hS
      (closedSubspaceToCompletionSubspace B S hS hX Z hZ).hom) :
    IsReduction B S hS (Space.completionSubspace B S hS ⟨X, hX⟩ Z)
      (reductionOfClosedSubspaceSheaf B S hS hX Z hZ)
      (reductionInclusion B S hS hX Z hZ ≫
        closedSubspaceToCompletionSubspace B S hS hX Z hZ) :=
  isReduction_of_isRepresentableThickening_closedSubspace B S hS hX Z hZ _ hc

end FormalSpace

end AlgebraicGeometry

end
