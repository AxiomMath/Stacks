module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.Immersions
public import StacksFrontier.AlgebraicGeometry.Spaces.Points
public import StacksFrontier.AlgebraicGeometry.Spaces.Presentation

/-!
# Finite type and quasi-finiteness at a point of an algebraic space

A property of scheme morphisms holds *near a point* `x` of the source of a morphism
`f : X ⟶ Y` of algebraic spaces over `S` when some open subspace of `X` whose points
include `x` restricts `f` to a morphism satisfying the every-étale-chart condition for
that property. Finite type at a point and quasi-finiteness at a point are the two
instances of this pattern used by the Stacks project.

## Main definitions

* `AlgebraicGeometry.Space.HoldsOnEveryEtaleChartNear` is the every-étale-chart condition
  localized at a point of the source.

## Main results

* `AlgebraicGeometry.Space.pointsMap_top_surjective`: the inclusion of the top subfunctor of an
  algebraic space is surjective on points. That the top subfunctor is an open subspace is
  `AlgebraicGeometry.Space.isOpenSubspace_top`, in
  `StacksFrontier/AlgebraicGeometry/Spaces/Immersions.lean`.
* `AlgebraicGeometry.Space.holdsOnEveryEtaleChartNear_of_holdsOnEveryEtaleChart`: a
  morphism satisfying the every-étale-chart condition satisfies it near every point. Its
  instance here is
  `AlgebraicGeometry.Space.isFiniteTypeAt_of_isLocallyOfFiniteType'`.
* `AlgebraicGeometry.Space.holdsOnEveryEtaleChartNear_mono`: the localized condition is
  monotone in the tested property of scheme morphisms, whence
  `AlgebraicGeometry.Space.isFiniteTypeAt_of_isQuasiFiniteAt`.

## Implementation notes

The localized condition is stated for an arbitrary `P : MorphismProperty Scheme` rather
than separately for each of the two properties the Stacks project localizes, so the
witness-producing lemma is proved once. `AlgebraicGeometry.Space.IsFiniteTypeAt` and
`AlgebraicGeometry.Space.IsQuasiFiniteAt` of
`StacksFrontier.AlgebraicGeometry.Spaces.FiniteType` are the two instances of it, up to
unfolding the abbreviations on both sides, so the lemmas below are stated directly about
them.

The witness for a globally valid property is the top subfunctor, whose inclusion is an
isomorphism. The two facts that makes it available —
`AlgebraicGeometry.Space.isOpenSubspace_top` and
`AlgebraicGeometry.Space.pointsMap_top_surjective` — are stated separately because they
are about the top subfunctor alone and are independent of any morphism out of it.

`AlgebraicGeometry.Space.IsQuasiFiniteAt` is part (2) of Stacks 03XJ and
`AlgebraicGeometry.Space.IsFiniteTypeAt` is part (2) of Stacks 03XF; both carry their part
keys where they are defined, in `StacksFrontier.AlgebraicGeometry.Spaces.FiniteType`
alongside parts (1) and (3), so nothing here claims a part key of 03XF or 03XJ. Finite type
at every point is condition (2) of Stacks 040Y, and
`AlgebraicGeometry.Space.isFiniteTypeAt_of_isLocallyOfFiniteType'` is the implication from
condition (1) to it; the tag itself is carried by the complete nine-way equivalence
`AlgebraicGeometry.Space.isLocallyOfFiniteType_tfae` of
`StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.FiniteType`.

## References

* [Stacks Project, Tag 03XF](https://stacks.math.columbia.edu/tag/03XF)
* [Stacks Project, Tag 03XJ](https://stacks.math.columbia.edu/tag/03XJ)
* [Stacks Project, Tag 040Y](https://stacks.math.columbia.edu/tag/040Y)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The top subfunctor as an open subspace -/

section Top

variable {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- The top subfunctor of `X` is isomorphic to `X`, via its inclusion. -/
def topSubfunctorIso : (⊤ : Subfunctor X).toFunctor ≅ X where
  hom := (⊤ : Subfunctor X).ι
  inv := Subfunctor.lift (𝟙 X) le_top
  hom_inv_id := by ext T x; rfl
  inv_hom_id := by ext T x; rfl

/-- The forward map of `topSubfunctorIso` is the inclusion of the top subfunctor. -/
@[simp]
theorem topSubfunctorIso_hom :
    (topSubfunctorIso B S hS (X := X)).hom = (⊤ : Subfunctor X).ι := rfl

/-- The inclusion of the top subfunctor is surjective on points. -/
theorem pointsMap_top_surjective :
    Function.Surjective
      (pointsMap B S hS (⊤ : Subfunctor X).toFunctor (⊤ : Subfunctor X).ι) := by
  intro x
  refine ⟨pointsMap B S hS X (topSubfunctorIso B S hS (X := X)).inv x, ?_⟩
  calc
    pointsMap B S hS (⊤ : Subfunctor X).toFunctor (⊤ : Subfunctor X).ι
        (pointsMap B S hS X (topSubfunctorIso B S hS (X := X)).inv x) =
      pointsMap B S hS X
        ((topSubfunctorIso B S hS (X := X)).inv ≫ (⊤ : Subfunctor X).ι) x :=
      (congrFun (pointsMap_comp B S hS X
        (topSubfunctorIso B S hS (X := X)).inv (⊤ : Subfunctor X).ι) x).symm
    _ = pointsMap B S hS X (𝟙 X) x := by
      rw [show (topSubfunctorIso B S hS (X := X)).inv ≫ (⊤ : Subfunctor X).ι = 𝟙 X from
        (topSubfunctorIso B S hS (X := X)).inv_hom_id]
    _ = x := congrFun (pointsMap_id B S hS X) x

end Top

/-! ### The every-étale-chart condition near a point -/

section Near

variable (P : MorphismProperty Scheme.{u})
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- A property `P` of scheme morphisms *holds on every étale chart near* a point `x` of
the source of `f : X ⟶ Y` when some open subspace of `X` whose points include `x`
restricts `f` to a morphism on whose every étale chart `P` holds.

This is the schema of which `AlgebraicGeometry.Space.IsFinitePresentationAt`,
`AlgebraicGeometry.Space.IsFiniteTypeAt`, `AlgebraicGeometry.Space.IsSmoothAt` and their
siblings are the instances at a fixed `P`; each of those writes the condition out longhand
rather than through this abbreviation, and each is a different part of a different tag of
the source. The quantifier over `P` here is what distinguishes this declaration from all of
them. -/
abbrev HoldsOnEveryEtaleChartNear (f : X ⟶ Y) (x : points B S hS X) : Prop :=
  ∃ U : Subfunctor X, IsOpenSubspace B S hS U ∧
    ∃ x' : points B S hS U.toFunctor,
      pointsMap B S hS U.toFunctor U.ι x' = x ∧
        HoldsOnEveryEtaleChart B S hS P (U.ι ≫ f)

/-- A property holding on every étale chart of `f` holds on every étale chart near every
point of the source: the top subfunctor is the witness. -/
theorem holdsOnEveryEtaleChartNear_of_holdsOnEveryEtaleChart
    (hX : IsAlgebraicSpace B S hS X) {f : X ⟶ Y}
    (hf : HoldsOnEveryEtaleChart B S hS P f) (x : points B S hS X) :
    HoldsOnEveryEtaleChartNear B S hS P f x := by
  obtain ⟨x', hx'⟩ := pointsMap_top_surjective B S hS (X := X) x
  refine ⟨⊤, isOpenSubspace_top hX, x', hx', ?_⟩
  intro U V a b h ha hb hab
  refine hf U V (a ≫ (⊤ : Subfunctor X).ι) b h ?_ hb ?_
  · exact MorphismProperty.RespectsIso.postcomp _ (⊤ : Subfunctor X).ι a ha
  · simpa only [Category.assoc] using hab

/-- The every-étale-chart condition near a point is monotone in the tested property of
scheme morphisms. -/
theorem holdsOnEveryEtaleChartNear_mono {P P' : MorphismProperty Scheme.{u}}
    (hPP' : ∀ {Z W : Scheme.{u}} (g : Z ⟶ W), P g → P' g)
    {f : X ⟶ Y} {x : points B S hS X}
    (hf : HoldsOnEveryEtaleChartNear B S hS P f x) :
    HoldsOnEveryEtaleChartNear B S hS P' f x := by
  obtain ⟨U, hU, x', hx', hchart⟩ := hf
  exact ⟨U, hU, x', hx', holdsOnEveryEtaleChart_mono B S hS hPP' hchart⟩

end Near

/-! ### Finite type and quasi-finiteness at a point -/

section AtPoint

variable {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- **Stacks 040Y, condition (1) implies condition (2).** A morphism locally of finite type
is of finite type at every point of its source.

Only the source has to be an algebraic space, which is what distinguishes this from
`AlgebraicGeometry.Space.isFiniteTypeAt_of_isLocallyOfFiniteType`: that form goes through the
permanence of local finite type under composition and so carries an algebraicity hypothesis on
the target as well. -/
theorem isFiniteTypeAt_of_isLocallyOfFiniteType' (hX : IsAlgebraicSpace B S hS X)
    {f : X ⟶ Y} (hf : IsLocallyOfFiniteType B S hS f) (x : points B S hS X) :
    IsFiniteTypeAt B S hS f x :=
  holdsOnEveryEtaleChartNear_of_holdsOnEveryEtaleChart B S hS _ hX hf x


/-- A morphism quasi-finite at a point is of finite type at that point. -/
theorem isFiniteTypeAt_of_isQuasiFiniteAt {f : X ⟶ Y} {x : points B S hS X}
    (hf : IsQuasiFiniteAt B S hS f x) : IsFiniteTypeAt B S hS f x :=
  holdsOnEveryEtaleChartNear_mono B S hS (fun _ hg => hg.1) hf

end AtPoint

end AlgebraicGeometry.Space

end
