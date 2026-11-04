module

public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.QuasiFinite
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.OpenImmersion

/-!
# Base change of a morphism to an open piece of its source and target

Let `f : X ⟶ Y` be a morphism of schemes, let `U ⊆ X` and `V ⊆ Y` be open subschemes and let
`fU : U ⟶ V` be a morphism with `fU ≫ V.ι = U.ι ≫ f`, so that `fU` is the restriction of `f`.
For a test morphism `g : T ⟶ V` there is then a canonical comparison

  `U ×_V T ⟶ X ×_Y T`,

where the second pullback is taken along `g ≫ V.ι`. It is `Stacks.Chow.opensPullbackComparison`,
and it exhibits `U ×_V T` as the base change of `U ⊆ X` along the projection `X ×_Y T ⟶ X`.
The only thing that makes this work is that `V.ι` is a monomorphism: the square is cartesian
because a morphism into `Y` that factors through `V` factors through it uniquely. In particular
the comparison is an open immersion, hence flat, locally of finite type and of relative
dimension zero.

This is the morphism that compares the cap operation of a bivariant class for `f` with the cap
operation of its restriction to a piece of a disjoint union decomposition of `X` and `Y`, as in
Stacks 0FDZ; the restriction is obtained by flat pullback along it. Nothing here needs the
pieces to be closed, disjoint, or to cover.

## Main definitions

* `Stacks.Chow.opensPullbackComparison` — the comparison `U ×_V T ⟶ X ×_Y T`.

## Main results

* `Stacks.Chow.eq_opensPullbackComparison` — it is the unique morphism with the two projection
  identities that the componentwise cap formula of Stacks 0FDZ quantifies over.
* `Stacks.Chow.isPullback_opensPullbackComparison` — the comparison square is cartesian, so the
  comparison is a base change of the open immersion `U.ι`.
* `Stacks.Chow.relativeDimension_opensPullbackComparison` — the comparison has relative
  dimension zero, so flat pullback along it is defined in degree `k ↦ k`.

## References

* [Stacks Project, Tag 0FDZ](https://stacks.math.columbia.edu/tag/0FDZ)
* [Stacks Project, Tag 02NJ](https://stacks.math.columbia.edu/tag/02NJ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.Chow

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (U : X.Opens) (V : Y.Opens)
  (fU : (U : Scheme.{u}) ⟶ (V : Scheme.{u})) (hfU : fU ≫ V.ι = U.ι ≫ f)
  {T : Scheme.{u}} (g : T ⟶ (V : Scheme.{u}))

/-- The canonical comparison `U ×_V T ⟶ X ×_Y T` attached to a restriction `fU : U ⟶ V` of
`f : X ⟶ Y` to open subschemes and a test morphism `g : T ⟶ V`. -/
def opensPullbackComparison : pullback fU g ⟶ pullback f (g ≫ V.ι) :=
  pullback.lift (pullback.fst fU g ≫ U.ι) (pullback.snd fU g) (by
    rw [Category.assoc, ← hfU, ← Category.assoc, pullback.condition, Category.assoc])

/-- The composite of `opensPullbackComparison` with the first projection `X ×_Y T ⟶ X` is
`U ×_V T ⟶ U ⟶ X`. -/
@[simp, reassoc]
theorem opensPullbackComparison_fst :
    opensPullbackComparison f U V fU hfU g ≫ pullback.fst f (g ≫ V.ι) =
      pullback.fst fU g ≫ U.ι :=
  pullback.lift_fst _ _ _

/-- The composite of `opensPullbackComparison` with the second projection `X ×_Y T ⟶ T` is the
second projection `U ×_V T ⟶ T`. -/
@[simp, reassoc]
theorem opensPullbackComparison_snd :
    opensPullbackComparison f U V fU hfU g ≫ pullback.snd f (g ≫ V.ι) = pullback.snd fU g :=
  pullback.lift_snd _ _ _

/-- The comparison is the **only** morphism `U ×_V T ⟶ X ×_Y T` whose composites with the two
projections are the expected ones, because `X ×_Y T` is a pullback. So a statement that quantifies
over a morphism with those two properties — as the componentwise cap formula of Stacks 0FDZ does —
is a statement about the comparison. -/
theorem eq_opensPullbackComparison (h : pullback fU g ⟶ pullback f (g ≫ V.ι))
    (hfst : h ≫ pullback.fst f (g ≫ V.ι) = pullback.fst fU g ≫ U.ι)
    (hsnd : h ≫ pullback.snd f (g ≫ V.ι) = pullback.snd fU g) :
    h = opensPullbackComparison f U V fU hfU g :=
  pullback.hom_ext (by rw [hfst, opensPullbackComparison_fst])
    (by rw [hsnd, opensPullbackComparison_snd])

/-- The comparison exhibits `U ×_V T` as the base change of the open subscheme `U ⊆ X` along the
projection `X ×_Y T ⟶ X`. -/
theorem isPullback_opensPullbackComparison :
    IsPullback (pullback.fst fU g) (opensPullbackComparison f U V fU hfU g) U.ι
      (pullback.fst f (g ≫ V.ι)) := by
  refine IsPullback.of_isLimit (PullbackCone.IsLimit.mk
    (opensPullbackComparison_fst f U V fU hfU g).symm
    (fun s => pullback.lift s.fst (s.snd ≫ pullback.snd f (g ≫ V.ι)) ?_) ?_ ?_ ?_)
  · rw [← cancel_mono V.ι]
    simp only [Category.assoc]
    rw [hfU, ← Category.assoc, s.condition, Category.assoc, pullback.condition]
  · intro s
    exact pullback.lift_fst _ _ _
  · intro s
    refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, opensPullbackComparison_fst, ← Category.assoc, pullback.lift_fst,
        s.condition]
    · rw [Category.assoc, opensPullbackComparison_snd, pullback.lift_snd]
  · intro s m h₁ h₂
    refine pullback.hom_ext ?_ ?_
    · rw [pullback.lift_fst, h₁]
    · rw [pullback.lift_snd, ← opensPullbackComparison_snd f U V fU hfU g, ← Category.assoc, h₂]

/-- The comparison is an open immersion, being a base change of the open immersion `U.ι`. -/
instance isOpenImmersion_opensPullbackComparison :
    IsOpenImmersion (opensPullbackComparison f U V fU hfU g) :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (isPullback_opensPullbackComparison f U V fU hfU g) inferInstance

/-- **Stacks 02NJ.** The comparison has relative dimension zero: it is an open immersion, hence
locally quasi-finite. -/
theorem relativeDimension_opensPullbackComparison :
    AlgebraicGeometry.RelativeDimension (opensPullbackComparison f U V fU hfU g) 0 :=
  (locallyQuasiFinite_iff_relativeDimension_zero _).mp inferInstance

end Stacks.Chow

end
