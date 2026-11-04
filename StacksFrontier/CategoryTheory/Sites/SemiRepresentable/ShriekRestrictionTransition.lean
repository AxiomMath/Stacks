module

public import StacksFrontier.CategoryTheory.Sites.SemiRepresentable.PushPullRestrictionTransition

/-!
# Restricting lower shriek further along a morphism of semi-representable objects

Let `(C, J)` be a small site and `f : M ⟶ N` a morphism of semi-representable objects of `C`.
The componentwise localization functor of `M` is the relocalization functor `r_f : C/M ⥤ C/N`
followed by the componentwise localization functor of `N`, so the triangle of restriction
functors carries a transition on each of its two adjoint sides. The right-adjoint side is
`CategoryTheory.SemiRepresentable.pushPullRestrictionTransition`, the canonical
`j_{N,*}j_N^{-1} ⟶ j_{M,*}j_M^{-1}`. This module supplies the left-adjoint side, the canonical

`j_{M!}j_M^{-1} ⟶ j_{N!}j_N^{-1}`,

and identifies the two as conjugates of one another.

The direction is worth stating: the transition runs *from* `M` *to* `N` on the shriek side and
*from* `N` *to* `M` on the push-pull side. That is the direction in which the shriek transition
can match `F(f)^♯`, and hence the direction in which it can be compared with Stacks 0D87,
part (2), whose right-hand side `F(-)^♯ × -` is covariant in the semi-representable object.

## Main definitions

* `CategoryTheory.SemiRepresentable.shriekRestrictionTransition`: the transition
  `j_{M!}j_M^{-1} ⟶ j_{N!}j_N^{-1}`, for sheaves valued in any category in which the three
  restrictions have left adjoints.

## Main results

* `CategoryTheory.SemiRepresentable.shriekRestrictionTransition_comp_counit`: the transition is a
  map over the identity — following it by the counit of `j_{N!} ⊣ j_N^{-1}` gives the counit of
  `j_{M!} ⊣ j_M^{-1}`.
* `CategoryTheory.SemiRepresentable.shriekRestrictionTransition_app`: its component, with the
  three whiskerings of `Stacks.CategoryTheory.shriekTransition` evaluated.
* `CategoryTheory.SemiRepresentable.conjugateEquiv_shriekRestrictionTransition`: on sheaves of
  sets it is the conjugate of `pushPullRestrictionTransition` under the two push-pull
  adjunctions. This is what lets the naturality of Stacks 0D86 in the semi-representable object
  (`CategoryTheory.SemiRepresentable.pushPullSheafHomIso_naturality`) be transported to the
  shriek side.

## Implementation notes

Everything is an instantiation of the abstract triangle machinery of
`StacksFrontier/CategoryTheory/Sites/SemiRepresentable/PushPullRestrictionTransition.lean`:
`Stacks.CategoryTheory.shriekTransition` at the comparison of the restrictions along the two
legs of the triangle.

That comparison is taken to be `CategoryTheory.Functor.sheafPushforwardContinuousComp'` of
`componentOverMap_comp_componentOverForget` directly, rather than
`CategoryTheory.SemiRepresentable.relocalizationForgetPushforwardIso`, for two reasons: it exists
for sheaves valued in any category, which is what the abelian consumers need, and it needs no
hypothesis identifying the two topologies on the component sites with the componentwise localized
ones — only the continuity of the three functors. The two agree on sheaves of sets, by
`relocalizationForgetPushforwardIso_eq`, which is what the conjugacy statement rewrites with;
there the hypotheses reappear, because `pushPullRestrictionTransition` carries them.

## References

* [Stacks Project, Tag 0D85](https://stacks.math.columbia.edu/tag/0D85)
* [Stacks Project, Tag 0D86](https://stacks.math.columbia.edu/tag/0D86)
* [Stacks Project, Tag 0D87](https://stacks.math.columbia.edu/tag/0D87)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe t u

namespace CategoryTheory.SemiRepresentable

open Stacks.CategoryTheory

variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
  {M N : FormalCoproduct.{u} C} (f : M ⟶ N)
  (Jm : GrothendieckTopology (ComponentOver M)) (Jn : GrothendieckTopology (ComponentOver N))

section

variable (A : Type t) [Category.{u} A]
  [(componentOverForget M).IsContinuous Jm J] [(componentOverForget N).IsContinuous Jn J]
  [(componentOverMap f).IsContinuous Jm Jn]
  [HasWeakSheafify Jm A] [HasWeakSheafify Jn A] [HasWeakSheafify J A]
  [∀ F : (ComponentOver M)ᵒᵖ ⥤ A, (componentOverForget M).op.HasLeftKanExtension F]
  [∀ F : (ComponentOver N)ᵒᵖ ⥤ A, (componentOverForget N).op.HasLeftKanExtension F]
  [∀ F : (ComponentOver M)ᵒᵖ ⥤ A, (componentOverMap f).op.HasLeftKanExtension F]

/-- **Restriction along `j_N` then along `r_f` is restriction along `j_M`**, for sheaves valued
in any category. This is
`CategoryTheory.SemiRepresentable.relocalizationForgetPushforwardIso` with the two topologies
free and the value category a parameter: the content is only the equality of site functors
`componentOverMap_comp_componentOverForget`, which the continuity instances already use. -/
def relocalizationForgetPushforwardIso' :
    (componentOverForget N).sheafPushforwardContinuous A Jn J ⋙
        (componentOverMap f).sheafPushforwardContinuous A Jm Jn ≅
      (componentOverForget M).sheafPushforwardContinuous A Jm J :=
  Functor.sheafPushforwardContinuousComp'
    (F := componentOverMap f) (G := componentOverForget N) (FG := componentOverForget M)
    (eqToIso (componentOverMap_comp_componentOverForget f)) A Jm Jn J

omit [HasWeakSheafify Jm A] [HasWeakSheafify Jn A] [HasWeakSheafify J A]
  [∀ F : (ComponentOver M)ᵒᵖ ⥤ A, (componentOverForget M).op.HasLeftKanExtension F]
  [∀ F : (ComponentOver N)ᵒᵖ ⥤ A, (componentOverForget N).op.HasLeftKanExtension F]
  [∀ F : (ComponentOver M)ᵒᵖ ⥤ A, (componentOverMap f).op.HasLeftKanExtension F] in
/-- `relocalizationForgetPushforwardIso'` is the comparison of
`CategoryTheory.Functor.sheafPushforwardContinuousComp'` it is defined to be. Stated so that the
bridge to `relocalizationForgetPushforwardIso` on sheaves of sets is a composite of two named
equations rather than a delta-reduction of the definition, which the elaborator does not finish
in its heartbeat budget. -/
theorem relocalizationForgetPushforwardIso'_eq :
    relocalizationForgetPushforwardIso' J f Jm Jn A =
      Functor.sheafPushforwardContinuousComp'
        (F := componentOverMap f) (G := componentOverForget N) (FG := componentOverForget M)
        (eqToIso (componentOverMap_comp_componentOverForget f)) A Jm Jn J :=
  rfl

/-- **Restricting lower shriek further along `f : M ⟶ N`.** The canonical transformation
`j_{M!} j_M^{-1} ⟶ j_{N!} j_N^{-1}` attached to a morphism of semi-representable objects: the
comparison of the left adjoints of the triangle of restrictions, followed by the counit of the
relocalization adjunction of `r_f`.

This is the left-adjoint counterpart of
`CategoryTheory.SemiRepresentable.pushPullRestrictionTransition`, and it runs in the opposite
direction. -/
def shriekRestrictionTransition :
    (componentOverForget M).sheafPushforwardContinuous A Jm J ⋙
        Functor.sheafPullbackConstruction.sheafPullback (componentOverForget M) A Jm J ⟶
      (componentOverForget N).sheafPushforwardContinuous A Jn J ⋙
        Functor.sheafPullbackConstruction.sheafPullback (componentOverForget N) A Jn J :=
  shriekTransition (relocalizationForgetPushforwardIso' J f Jm Jn A)
    (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous (componentOverForget N) A Jn J)
    (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous (componentOverForget M) A Jm J)
    (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous (componentOverMap f) A Jm Jn)

omit [HasWeakSheafify Jm A] in
/-- The component of `shriekRestrictionTransition` at a sheaf, with the three whiskerings of
`Stacks.CategoryTheory.shriekTransition` evaluated. -/
theorem shriekRestrictionTransition_app (X : Sheaf J A) :
    (shriekRestrictionTransition J f Jm Jn A).app X =
      (Functor.sheafPullbackConstruction.sheafPullback (componentOverForget M) A Jm J).map
          ((relocalizationForgetPushforwardIso' J f Jm Jn A).inv.app X) ≫
        (restrictionLeftAdjointIso (relocalizationForgetPushforwardIso' J f Jm Jn A)
              (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
                (componentOverForget N) A Jn J)
              (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
                (componentOverForget M) A Jm J)
              (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
                (componentOverMap f) A Jm Jn)).hom.app
            (((componentOverForget N).sheafPushforwardContinuous A Jn J ⋙
              (componentOverMap f).sheafPushforwardContinuous A Jm Jn).obj X) ≫
          (Functor.sheafPullbackConstruction.sheafPullback (componentOverForget N) A Jn J).map
            ((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous (componentOverMap f)
              A Jm Jn).counit.app
              (((componentOverForget N).sheafPushforwardContinuous A Jn J).obj X)) :=
  shriekTransition_app _ _ _ _ X

omit [HasWeakSheafify Jm A] in
/-- **The shriek restriction transition is a map over the identity.** Following it by the counit
of `j_{N!} ⊣ j_N^{-1}` gives the counit of `j_{M!} ⊣ j_M^{-1}`.

Under Stacks 0D87, part (2), which identifies `j_{M!}j_M^{-1}` with `F(M)^♯ × -` and carries the
counit to the projection onto the second factor, this is the statement that the transition is the
identity on that factor: one of the two halves of its comparison with `F(f)^♯`. -/
theorem shriekRestrictionTransition_comp_counit (X : Sheaf J A) :
    (shriekRestrictionTransition J f Jm Jn A).app X ≫
        (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous (componentOverForget N)
          A Jn J).counit.app X =
      (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous (componentOverForget M)
        A Jm J).counit.app X :=
  Stacks.CategoryTheory.shriekTransition_comp_counit _ _ _ _ X

end

section Sets

variable (hJm : Jm = componentwiseTopology J M) (hJn : Jn = componentwiseTopology J N)
  [(componentOverForget M).IsContinuous Jm J] [(componentOverForget M).IsCocontinuous Jm J]
  [(componentOverForget N).IsContinuous Jn J] [(componentOverForget N).IsCocontinuous Jn J]
  [(componentOverMap f).IsContinuous Jm Jn] [(componentOverMap f).IsCocontinuous Jm Jn]
  [HasWeakSheafify Jm (Type u)] [HasWeakSheafify Jn (Type u)] [HasWeakSheafify J (Type u)]
  [∀ F : (ComponentOver M)ᵒᵖ ⥤ Type u, (componentOverForget M).op.HasLeftKanExtension F]
  [∀ F : (ComponentOver N)ᵒᵖ ⥤ Type u, (componentOverForget N).op.HasLeftKanExtension F]
  [∀ F : (ComponentOver M)ᵒᵖ ⥤ Type u, (componentOverMap f).op.HasLeftKanExtension F]

omit [(componentOverForget M).IsCocontinuous Jm J] [(componentOverForget N).IsCocontinuous Jn J]
  [(componentOverMap f).IsCocontinuous Jm Jn]
  [HasWeakSheafify Jm (Type u)] [HasWeakSheafify Jn (Type u)] [HasWeakSheafify J (Type u)]
  [∀ F : (ComponentOver M)ᵒᵖ ⥤ Type u, (componentOverForget M).op.HasLeftKanExtension F]
  [∀ F : (ComponentOver N)ᵒᵖ ⥤ Type u, (componentOverForget N).op.HasLeftKanExtension F]
  [∀ F : (ComponentOver M)ᵒᵖ ⥤ Type u, (componentOverMap f).op.HasLeftKanExtension F] in
/-- On sheaves of sets the comparison used by `shriekRestrictionTransition` is the one
`pushPullRestrictionTransition` uses. -/
theorem relocalizationForgetPushforwardIso'_eq_relocalizationForgetPushforwardIso :
    relocalizationForgetPushforwardIso' J f Jm Jn (Type u) =
      relocalizationForgetPushforwardIso J f Jm hJm Jn hJn :=
  (relocalizationForgetPushforwardIso'_eq J f Jm Jn (Type u)).trans
    (relocalizationForgetPushforwardIso_eq J f Jm hJm Jn hJn).symm

omit [HasWeakSheafify Jm (Type u)] in
/-- **The push-pull restriction transition is the conjugate of the shriek restriction
transition.** Both `j_{M!}j_M^{-1} ⊣ j_{M,*}j_M^{-1}` and `j_{N!}j_N^{-1} ⊣ j_{N,*}j_N^{-1}`
hold, and under that adjointness the two transitions of the relocalization triangle correspond.

This is what moves the naturality of Stacks 0D86 in the semi-representable object onto the
shriek side, where Stacks 0D87, part (2) lives. -/
theorem conjugateEquiv_shriekRestrictionTransition :
    conjugateEquiv
        (((componentOverForget N).sheafAdjunctionCocontinuous (Type u) Jn J).comp
          (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous (componentOverForget N)
            (Type u) Jn J))
        (((componentOverForget M).sheafAdjunctionCocontinuous (Type u) Jm J).comp
          (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous (componentOverForget M)
            (Type u) Jm J))
        (shriekRestrictionTransition J f Jm Jn (Type u)) =
      pushPullRestrictionTransition J f Jm hJm Jn hJn :=
  (congrArg
        (conjugateEquiv
          (((componentOverForget N).sheafAdjunctionCocontinuous (Type u) Jn J).comp
            (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
              (componentOverForget N) (Type u) Jn J))
          (((componentOverForget M).sheafAdjunctionCocontinuous (Type u) Jm J).comp
            (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
              (componentOverForget M) (Type u) Jm J)))
        (congrArg
          (fun e =>
            shriekTransition e
              (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
                (componentOverForget N) (Type u) Jn J)
              (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
                (componentOverForget M) (Type u) Jm J)
              (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
                (componentOverMap f) (Type u) Jm Jn))
          (relocalizationForgetPushforwardIso'_eq_relocalizationForgetPushforwardIso
            J f Jm Jn hJm hJn))).trans
    (Stacks.CategoryTheory.conjugateEquiv_shriekTransition _ _ _ _ _ _ _)

end Sets

end CategoryTheory.SemiRepresentable

end
