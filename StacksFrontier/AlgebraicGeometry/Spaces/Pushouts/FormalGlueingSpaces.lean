module

public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import Mathlib.CategoryTheory.Functor.ReflectsIso.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Category
public import StacksFrontier.AlgebraicGeometry.Spaces.FpqcCoveringBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.IsomorphismFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits
public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.FormalGlueingCovering
public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.FormalGlueingModules

/-!
# Formal glueing data for algebraic spaces

In a formal glueing situation `(f : Y ⟶ X, Z, U = X \ Z, V = Y \ f⁻¹(Z))`, an algebraic space
over `X` restricts to an algebraic space over `U` and one over `Y`, together with the canonical
identification of their further restrictions to `V`. This module builds the category of such
cartesian triples and the restriction functor into it, and shows that the functor reflects
isomorphisms.

## Main definitions

* `AlgebraicGeometry.Space.FormalGlueingSituation.spacesOverX`: the category of algebraic
  spaces over the ambient space `X`.
* `AlgebraicGeometry.Space.FormalGlueingSituation.glueingData`: the category of cartesian
  formal-glueing triples.
* `AlgebraicGeometry.Space.FormalGlueingSituation.restrictionComparison`: the canonical
  identification of the two ways of restricting from `X` to `V`.
* `AlgebraicGeometry.Space.FormalGlueingSituation.restrictionDiagram`: the presheaf-level
  restriction functor.

## Main results

* `AlgebraicGeometry.Space.FormalGlueingSituation.formalGlueingFunctor`: **Stacks 0AF3**, the
  restriction functor from algebraic spaces over `X` to cartesian glueing triples, together
  with the natural isomorphism identifying it with the presheaf-level restriction diagram.
* `AlgebraicGeometry.Space.FormalGlueingSituation.reflectsIsomorphisms_formalGlueingFunctor`:
  **Stacks 0AF5**, that functor reflects isomorphisms.

## Implementation notes

A cartesian triple is an object of the comma category of the two pullback functors
`Over V ⟵ Over U` and `Over V ⟵ Over Y`, cut down by invertibility of its structure arrow and
by algebraicity of its two outer components; the third component is then the common restriction
to `V`, so recording one arrow is the same as recording both cartesian squares.

The functor is returned together with its specification: the bare functor would not pin down
which restrictions it computes, so the result is a dependent pair whose second component is a
natural isomorphism with `restrictionDiagram`. Both legs of
`restrictionComparison` are composites of `CategoryTheory.Over.pullback`, identified by
`CategoryTheory.Over.pullbackComp` and by `CategoryTheory.Subfunctor.fromPreimage_ι`, which
says that the inclusion of `V` composed with `f` is the inclusion of `U` composed with the
projection `V ⟶ U`.

Reflection of isomorphisms is proved first for the presheaf-level restriction diagram, where
being an isomorphism of the two restrictions is just invertibility of the two components of the
comma morphism, and is then transported to `formalGlueingFunctor` along the natural isomorphism
that the dependent pair carries, by
`CategoryTheory.reflectsIsomorphisms_of_iso` and `CategoryTheory.reflectsIsomorphisms_of_comp`.
At the presheaf level the argument is the one of the source: the fpqc covering of `X` refining
`U ⟶ X` and `Y ⟶ X` of Stacks 0AF1 pulls back to an fpqc covering of the target by Stacks 03MR,
each member of the pullback covering restricts the morphism to one of the two given
restrictions, and Stacks 041Y assembles invertibility over the covering into invertibility over
`X`. Invertibility is then reflected back along the forgetful functor of `Over X` and the
inclusion of the full subcategory of algebraic spaces.

## References

* [Stacks Project, Tag 03MR](https://stacks.math.columbia.edu/tag/03MR)
* [Stacks Project, Tag 041Y](https://stacks.math.columbia.edu/tag/041Y)
* [Stacks Project, Tag 0AF1](https://stacks.math.columbia.edu/tag/0AF1)
* [Stacks Project, Tag 0AF3](https://stacks.math.columbia.edu/tag/0AF3)
* [Stacks Project, Tag 0AF5](https://stacks.math.columbia.edu/tag/0AF5)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space.FormalGlueingSituation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- Algebraic spaces over the ambient space `X`. -/
abbrev spacesOverX (D : FormalGlueingSituation B S hS) :=
  (show ObjectProperty (Over D.X) from
    fun T ↦ IsAlgebraicSpace B S hS T.left).FullSubcategory

/-- The category of cartesian formal-glueing diagrams of algebraic spaces. -/
abbrev glueingData (D : FormalGlueingSituation B S hS) :=
  (show ObjectProperty (Comma (Over.pullback (D.U.fromPreimage D.f)) (Over.pullback D.V.ι)) from
    fun T ↦ IsIso T.hom ∧ IsAlgebraicSpace B S hS T.left.left ∧
      IsAlgebraicSpace B S hS T.right.left).FullSubcategory

/-- The canonical identification of the two ways of restricting a space
over `X` to `V`. -/
noncomputable def restrictionComparison (D : FormalGlueingSituation B S hS) :
    Over.pullback D.U.ι ⋙ Over.pullback (D.U.fromPreimage D.f) ≅
      Over.pullback D.f ⋙ Over.pullback D.V.ι :=
  (Over.pullbackComp (D.U.fromPreimage D.f) D.U.ι).symm ≪≫
    eqToIso (congrArg (fun g : D.V.toFunctor ⟶ D.X ↦ Over.pullback g)
      (Subfunctor.fromPreimage_ι D.U D.f)) ≪≫ Over.pullbackComp D.V.ι D.f

/-- The presheaf-level diagram obtained by restricting a space over `X`
to `U` and `Y`. -/
noncomputable def restrictionDiagram (D : FormalGlueingSituation B S hS) :
    Over D.X ⥤ Comma (Over.pullback (D.U.fromPreimage D.f))
        (Over.pullback D.V.ι) :=
  { obj := fun T ↦ ⟨(Over.pullback D.U.ι).obj T,
        (Over.pullback D.f).obj T, (restrictionComparison D).hom.app T⟩
    map := fun g ↦ ⟨(Over.pullback D.U.ι).map g,
        (Over.pullback D.f).map g, (restrictionComparison D).hom.naturality g⟩
    map_id T := by ext <;> simp
    map_comp g h := by ext <;> simp }

/-- Restriction from algebraic spaces over `X` to their cartesian
formal-glueing diagrams. The comparison identifies it naturally with
pullback on each component and the canonical associativity identification
on the overlap. -/
@[stacks 0AF3]
noncomputable def formalGlueingFunctor (D : FormalGlueingSituation B S hS) :
    Σ F : spacesOverX D ⥤ glueingData D,
      F ⋙ (show ObjectProperty
          (Comma (Over.pullback (D.U.fromPreimage D.f))
            (Over.pullback D.V.ι)) from
          fun T ↦ IsIso T.hom ∧
            IsAlgebraicSpace B S hS T.left.left ∧
            IsAlgebraicSpace B S hS T.right.left).ι ≅
        (show ObjectProperty (Over D.X) from
          fun T ↦ IsAlgebraicSpace B S hS T.left).ι ⋙
          restrictionDiagram D :=
  ⟨{
    obj T := ⟨(restrictionDiagram D).obj T.1,
      ⟨(show IsIso ((restrictionComparison D).hom.app T.1) from inferInstance),
        isAlgebraicSpace_pullback B S hS T.1.hom D.U.ι
          T.property (isOpenSubspace_U D).1
          D.algebraicSpace_X,
        isAlgebraicSpace_pullback B S hS T.1.hom D.f
          T.property D.algebraicSpace_Y D.algebraicSpace_X⟩⟩
    map f := ⟨(restrictionDiagram D).map f.hom⟩
    map_id T := by ext <;> simp
    map_comp f g := by ext <;> simp },
    NatIso.ofComponents (fun _ ↦ Iso.refl _) (by intros; simp)⟩

/-! ### Reflection of isomorphisms -/

/-- Base change along a composite is the composite of the base changes, so invertibility of the
restriction along the second factor forces invertibility of the restriction along the
composite. -/
private theorem isIso_pullback_map_of_comp
    {C : Type*} [Category C] [HasPullbacks C]
    {X U V : C} (a : V ⟶ U) (b : U ⟶ X)
    {P Q : Over X} (f : P ⟶ Q)
    (hf : IsIso ((Over.pullback b).map f)) :
    IsIso ((Over.pullback (a ≫ b)).map f) :=
  (NatIso.isIso_map_iff (Over.pullbackComp a b) f).2
    (Functor.map_isIso (Over.pullback a) ((Over.pullback b).map f))

/-- If the second leg of a pullback square is invertible, so is the second projection of the
chosen pullback. -/
private theorem isIso_pullback_snd_of_isPullback
    {C : Type*} [Category C] {P X Y Z : C} {p₁ : P ⟶ X} {p₂ : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}
    [HasPullback f g] (h : IsPullback p₁ p₂ f g) [IsIso p₂] : IsIso (pullback.snd f g) := by
  have _ : IsIso (h.isoPullback.hom ≫ pullback.snd f g) := by
    rw [h.isoPullback_hom_snd]
    infer_instance
  exact IsIso.of_isIso_comp_left h.isoPullback.hom _

/-- The restriction of `f : P ⟶ Q` over `X` along `g : U ⟶ X`, read as a morphism of `Over U`,
is the base change of `f.left` along the projection `U ×_X Q ⟶ P`; so if the restriction is
invertible then so is that base change. -/
private theorem isIso_pullback_snd_of_over_pullback
    {C : Type*} [Category C] [HasPullbacks C]
    {X U : C} (g : U ⟶ X) {A B : Over X} (f : A ⟶ B)
    (hf : IsIso ((Over.pullback g).map f)) :
    IsIso (pullback.snd f.left (pullback.snd g B.hom)) := by
  have _ : IsIso ((Over.pullback g).map f).left :=
    Functor.map_isIso (Over.forget U) ((Over.pullback g).map f)
  have hm₁ : ((Over.pullback g).map f).left ≫ pullback.fst B.hom g =
      pullback.fst A.hom g ≫ f.left := by
    dsimp [Over.pullback]
    exact pullback.lift_fst _ _ _
  have hm₂ : ((Over.pullback g).map f).left ≫ pullback.snd B.hom g =
      pullback.snd A.hom g := by
    dsimp [Over.pullback]
    exact pullback.lift_snd _ _ _
  have hpb : IsPullback ((Over.pullback g).map f).left (pullback.fst A.hom g)
      (pullback.fst B.hom g) f.left :=
    IsPullback.of_right
      (by
        rw [hm₂, Over.w f]
        exact (IsPullback.of_hasPullback A.hom g).flip)
      hm₁ (IsPullback.of_hasPullback B.hom g).flip
  have hpb' : IsPullback (((Over.pullback g).map f).left ≫ (pullbackSymmetry B.hom g).hom)
      (pullback.fst A.hom g) (pullback.snd g B.hom) f.left :=
    hpb.of_iso (Iso.refl _) (pullbackSymmetry B.hom g) (Iso.refl _) (Iso.refl _)
      (by simp) (by simp) (by simp) (by simp)
  exact isIso_pullback_snd_of_isPullback hpb'.flip

/-- **Stacks 0AF5** for the presheaf-level restriction diagram: a morphism of algebraic spaces
over `X` whose restrictions to `U` and to `Y` are both invertible is itself invertible.

The fpqc covering of `X` refining `U ⟶ X` and `Y ⟶ X` of Stacks 0AF1 pulls back to an fpqc
covering of the target, and over each member the morphism is one of the two restrictions, hence
invertible; Stacks 041Y then makes the morphism of algebraic spaces invertible, and that is
reflected along the forgetful functor of `Over X`. -/
private theorem restrictionDiagram_reflectsIsomorphisms
    (D : FormalGlueingSituation B S hS) :
    (((show ObjectProperty (Over D.X) from
        fun T ↦ IsAlgebraicSpace B S hS T.left).ι) ⋙
      restrictionDiagram D).ReflectsIsomorphisms := by
  let sourceIncl := (show ObjectProperty (Over D.X) from
    fun T ↦ IsAlgebraicSpace B S hS T.left).ι
  refine ⟨fun {T₁ T₂} (f : T₁ ⟶ T₂) [hf :
      IsIso ((sourceIncl ⋙ restrictionDiagram D).map f)] ↦ ?_⟩
  let f₀ := sourceIncl.map f
  have _ : IsIso ((restrictionDiagram D).map f₀) := hf
  have hU : IsIso ((Over.pullback D.U.ι).map f₀) :=
    Functor.map_isIso
      (Comma.fst (Over.pullback (D.U.fromPreimage D.f)) (Over.pullback D.V.ι))
      ((restrictionDiagram D).map f₀)
  have hY : IsIso ((Over.pullback D.f).map f₀) :=
    Functor.map_isIso
      (Comma.snd (Over.pullback (D.U.fromPreimage D.f)) (Over.pullback D.V.ι))
      ((restrictionDiagram D).map f₀)
  obtain ⟨I, Xi, g, hXi, hcover, hfactor⟩ :=
    exists_fpqcCovering_refining_openComplement_and_source B S hS D
  let T₁' : AlgebraicSpaces B S hS := ⟨T₁.1.left, T₁.property⟩
  let T₂' : AlgebraicSpaces B S hS := ⟨T₂.1.left, T₂.property⟩
  let a : T₁' ⟶ T₂' := ⟨f₀.left⟩
  let X' : AlgebraicSpaces B S hS := ⟨D.X, D.algebraicSpace_X⟩
  let Xi' (i : I) : AlgebraicSpaces B S hS := ⟨Xi i, hXi i⟩
  let gi (i : I) : Xi' i ⟶ X' := ⟨g i⟩
  have hgi : ∀ i, IsIso ((Over.pullback (g i)).map f₀) := by
    intro i
    rcases hfactor i with ⟨b, hb⟩ | ⟨c, hc⟩
    · rw [← hb]
      exact isIso_pullback_map_of_comp b D.U.ι f₀ hU
    · rw [← hc]
      exact isIso_pullback_map_of_comp c D.f f₀ hY
  let t₂ : T₂' ⟶ X' := ⟨T₂.1.hom⟩
  let P (i : I) : AlgebraicSpaces B S hS := AlgebraicSpaces.fiberProduct B S hS (gi i) t₂
  let q (i : I) : P i ⟶ T₂' := ⟨pullback.snd (gi i).hom t₂.hom⟩
  let K := Topology.precoverage.{u, u} .fpqc B S hS
  let 𝒰 : K.ZeroHypercover T₂' :=
    { I₀ := I
      X := P
      f := q
      mem₀ := ⟨I, P, q, rfl, T₂'.property, fun i ↦ (P i).property,
        isFpqcCovering_pullback B S hS gi t₂ hcover⟩ }
  have ha : IsIso a := by
    have _ : (MorphismProperty.isomorphisms (AlgebraicSpaces B S hS)).IsLocalAtTarget K :=
      isomorphisms_isLocalAtTarget_fpqc B S hS
    apply MorphismProperty.IsLocalAtTarget.of_zeroHypercover
      (P := MorphismProperty.isomorphisms (AlgebraicSpaces B S hS)) 𝒰
    intro i
    have hp := AlgebraicSpaces.isPullback_fiberProduct B S hS a (q i)
    let hpSnd : AlgebraicSpaces.fiberProduct B S hS a (q i) ⟶ P i :=
      ObjectProperty.homMk (pullback.snd a.hom (q i).hom)
    have hfp : IsIso hpSnd := by
      have : IsIso ((ObjectProperty.ι _).map hpSnd) :=
        isIso_pullback_snd_of_over_pullback (g i) f₀ (hgi i)
      exact isIso_of_reflects_iso hpSnd (ObjectProperty.ι _)
    exact isIso_pullback_snd_of_isPullback hp
  have _ : IsIso ((Over.forget D.X).map f₀) := Functor.map_isIso (ObjectProperty.ι _) a
  have _ : IsIso f₀ := isIso_of_reflects_iso f₀ (Over.forget D.X)
  exact isIso_of_reflects_iso f (ObjectProperty.ι _)

/-- **Stacks 0AF5.** The restriction functor from algebraic spaces over `X` to cartesian
formal-glueing triples reflects isomorphisms: a morphism over `X` whose restrictions to `U` and
to `Y` are invertible is itself invertible. -/
@[stacks 0AF5]
instance reflectsIsomorphisms_formalGlueingFunctor
    (D : FormalGlueingSituation B S hS) :
    (formalGlueingFunctor D).1.ReflectsIsomorphisms := by
  let inclusion := (show ObjectProperty
      (Comma (Over.pullback (D.U.fromPreimage D.f)) (Over.pullback D.V.ι)) from
      fun T ↦ IsIso T.hom ∧ IsAlgebraicSpace B S hS T.left.left ∧
        IsAlgebraicSpace B S hS T.right.left).ι
  have := restrictionDiagram_reflectsIsomorphisms D
  have _ : ((formalGlueingFunctor D).1 ⋙ inclusion).ReflectsIsomorphisms :=
    reflectsIsomorphisms_of_iso (formalGlueingFunctor D).2.symm
  exact reflectsIsomorphisms_of_comp (formalGlueingFunctor D).1 inclusion

end AlgebraicGeometry.Space.FormalGlueingSituation

end
