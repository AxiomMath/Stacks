module

public import StacksFrontier.CategoryTheory.Sites.Continuous.FreeAbelianLowerShriekCounit

/-!
# Stacks 0D87 part (2) on free abelian sheaves is natural in the semi-representable object

Let `(C, J)` be a small site and `f : M ⟶ N` a morphism of semi-representable objects of `C`.
`CategoryTheory.SemiRepresentable.shriekRestrictionTransition` is the canonical transformation
`j_{M!}j_M^{-1} ⟶ j_{N!}j_N^{-1}`, and it exists for sheaves valued in any category in which the
three restrictions of the relocalization triangle have left adjoints -- in particular on sheaves
of sets and on abelian sheaves. The free abelian sheaf functor `ℤ_{(-)}^♯` commutes with each of
the two legs `j^{-1}` and `j_!` separately
(`CategoryTheory.SemiRepresentable.freeSheafPushforwardIso` and `.freeSheafPullbackIso`). This
module proves that the two commutations **carry the abelian transition to the set-level one**.

## Main results

* `CategoryTheory.SemiRepresentable.shriekRestrictionTransition_app_lowerShriekComp`: the
  transition with its comparison of left adjoints read as
  `CategoryTheory.Functor.lowerShriekComp` and pulled past the leading restriction, so that the
  whole transition is one comparison followed by one `j_{N!}`-image.
* `CategoryTheory.SemiRepresentable.freeSheafPushforwardIso_naturality_inv`: the restriction
  square, solved for the reindexing of the free abelian sheaf.
* `CategoryTheory.SemiRepresentable.freeAbelianShriekTransitionLeg`: the `r_f`-leg of the
  transition carried across the free abelian sheaf functor.
* `CategoryTheory.SemiRepresentable.freeAbelianShriekRestrictionTransition`: the naturality on
  the restriction-and-extension factor.
* `CategoryTheory.SemiRepresentable.freeSheafPushforwardCompSheafPullbackIso_hom_app` and
  `.freeYonedaSheafPushforwardPullbackIso_hom`: the components of the two forms of Stacks 0D87
  part (2) on free abelian sheaves, with the associators of their definitions discharged.
* `CategoryTheory.SemiRepresentable`
  `.shriekRestrictionTransition_comp_freeSheafPushforwardCompSheafPullbackIso`:
  **Stacks 0D87 part (2) on free abelian sheaves is natural in the semi-representable object.**
* `CategoryTheory.SemiRepresentable`
  `.shriekRestrictionTransition_comp_freeYonedaSheafPushforwardPullbackIso`:
  **the same at the coefficient sheaf `ℤ_V^♯`** -- the form the cohomological descent of a
  hypercovering consumes, where the right-hand side is the free abelian sheaf of
  `h_V × F(f)`.

## Implementation notes

The three squares the assembly consumes are
`CategoryTheory.SemiRepresentable.freeSheafPushforwardIso_naturality'` (restriction),
`CategoryTheory.Functor.freeLowerShriekIso_comp` (extension by zero against composition) and
`CategoryTheory.Functor.freeLowerShriekIso_hom_app_comp_map_counit` (the counit). What glues them
is the naturality of `CategoryTheory.Functor.lowerShriekComp` on abelian sheaves and on sheaves
of sets, the naturality of `freeSheafPullbackIso` of degree `N`, and the naturality of the
extension-by-zero commutation for `r_f`. The set-level square
`CategoryTheory.SemiRepresentable`
`.shriekRestrictionTransition_comp_sheafPushforwardCompSheafPullbackIso`
and `.freeAbelianSheafTensorIso_naturality` are what carry that to the two forms of the tag.

Every object occurring in the assembly is a `.app` of a *named* functor: the commutation of the
free abelian sheaf functor with restriction along `r_f` is
`CategoryTheory.Functor.freePushforwardIso` rather than the Mathlib comparison it is built from,
whose components are indexed by presheaves and expose `r_f^{op} ⋙ (j_N^{op} ⋙ X ⋙ ℤ)` where the
surrounding composites produce `(j_N^{op} ⋙ X) ⋙ ℤ`. With the two spellings in one goal the
`isDefEq` checks of the assembly do not finish inside a declaration's heartbeat budget.

Associativity is never rearranged by `CategoryTheory.Category.assoc` under `rw`, which does not
fire in these sheaf categories -- outer and inner `≫` carry different spellings of the category
instance -- but by `simp only [Category.assoc]`, by `CategoryTheory.whisker_eq` and
`CategoryTheory.eq_whisker`, and by `← CategoryTheory.Functor.map_comp_assoc`. `reassoc_of%` is
not used: it unfolds `CategoryTheory.Sheaf.composeAndSheafify` in the pattern it builds, and the
goal keeps it folded.

## References

* [Stacks Project, Tag 0D87](https://stacks.math.columbia.edu/tag/0D87)
* [Stacks Project, Tag 0D85](https://stacks.math.columbia.edu/tag/0D85)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CartesianMonoidalCategory MonoidalCategory
  Opposite

universe t u

namespace CategoryTheory.SemiRepresentable

variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
  {M N : FormalCoproduct.{u} C} (f : M ⟶ N)
  (Jm : GrothendieckTopology (ComponentOver M)) (Jn : GrothendieckTopology (ComponentOver N))
  (A : Type t) [Category.{u} A]
  [(componentOverForget M).IsContinuous Jm J] [(componentOverForget N).IsContinuous Jn J]
  [(componentOverMap f).IsContinuous Jm Jn]
  [HasWeakSheafify Jm A] [HasWeakSheafify Jn A] [HasWeakSheafify J A]
  [∀ F : (ComponentOver M)ᵒᵖ ⥤ A, (componentOverForget M).op.HasLeftKanExtension F]
  [∀ F : (ComponentOver N)ᵒᵖ ⥤ A, (componentOverForget N).op.HasLeftKanExtension F]
  [∀ F : (ComponentOver M)ᵒᵖ ⥤ A, (componentOverMap f).op.HasLeftKanExtension F]

omit [HasWeakSheafify Jm A] in
/-- **The shriek restriction transition, with its comparison of left adjoints read as
`CategoryTheory.Functor.lowerShriekComp` and pulled past the leading restriction.** The
transition `j_{M!}j_M^{-1} ⟶ j_{N!}j_N^{-1}` at a sheaf `Y` is the composition comparison
`j_{M!} ≅ r_{f!} j_{N!}` at `j_M^{-1}Y`, followed by the extension by zero along `j_N` of the
`r_f`-part: the reindexing of `j_M^{-1}Y` into `r_f^{-1} j_N^{-1}Y`, then the counit of
`r_{f!} ⊣ r_f^{-1}`.

This is `CategoryTheory.SemiRepresentable.shriekRestrictionTransition_app` with
`CategoryTheory.SemiRepresentable.restrictionLeftAdjointIso_eq_lowerShriekComp` substituted and
the naturality of `lowerShriekComp` used to move the restriction transport from the left of the
comparison to the right of it, where the counit already is. In that shape the whole transition
is a comparison at one object followed by a single `j_{N!}`-image, which is what matching it
against the free abelian sheaf comparisons needs. -/
theorem shriekRestrictionTransition_app_lowerShriekComp (Y : Sheaf J A) :
    (shriekRestrictionTransition J f Jm Jn A).app Y =
      (Functor.lowerShriekComp Jm Jn J (componentOverMap f) (componentOverForget N)
            (componentOverForget M) A
            (eqToIso (componentOverMap_comp_componentOverForget f))).hom.app
          (((componentOverForget M).sheafPushforwardContinuous A Jm J).obj Y) ≫
        (Functor.sheafPullbackConstruction.sheafPullback (componentOverForget N) A Jn J).map
          ((Functor.sheafPullbackConstruction.sheafPullback (componentOverMap f) A Jm Jn).map
              ((relocalizationForgetPushforwardIso' J f Jm Jn A).inv.app Y) ≫
            (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous (componentOverMap f)
              A Jm Jn).counit.app
              (((componentOverForget N).sheafPushforwardContinuous A Jn J).obj Y)) := by
  rw [shriekRestrictionTransition_app, restrictionLeftAdjointIso_eq_lowerShriekComp,
    Functor.map_comp, ← Category.assoc,
    (Functor.lowerShriekComp Jm Jn J (componentOverMap f) (componentOverForget N)
      (componentOverForget M) A
      (eqToIso (componentOverMap_comp_componentOverForget f))).hom.naturality
      ((relocalizationForgetPushforwardIso' J f Jm Jn A).inv.app Y)]
  simp only [Category.assoc, Functor.comp_map]

end CategoryTheory.SemiRepresentable

namespace CategoryTheory.SemiRepresentable

attribute [local instance] GrothendieckTopology.hasSheafify_addCommGrpCat
-- Mathlib's instance that a left adjoint preserves sheafification, tried first: at its default
-- priority the search for `J.PreservesSheafification AddCommGrpCat.free` runs out of budget.
attribute [local instance high] Sheaf.instPreservesSheafificationOfIsLeftAdjoint

variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
  [J.WEqualsLocallyBijective (Type u)] {M N : FormalCoproduct.{u} C} (f : M ⟶ N)

/-- **`freeSheafPushforwardIso` is natural in the semi-representable object, solved for the
reindexing of the free abelian sheaf.** This is
`CategoryTheory.SemiRepresentable.freeSheafPushforwardIso_naturality'` with the commutation
`CategoryTheory.Functor.freePushforwardIso` for `r_f` moved to the other side of the square,
where the counit square of `r_{f!} ⊣ r_f^{-1}` consumes it. -/
theorem freeSheafPushforwardIso_naturality_inv (X : Sheaf J (Type u)) :
    (relocalizationForgetPushforwardIso' J f (componentwiseTopology J M)
            (componentwiseTopology J N) AddCommGrpCat.{u}).inv.app
          ((Sheaf.composeAndSheafify J AddCommGrpCat.free).obj X) ≫
        ((componentOverMap f).sheafPushforwardContinuous AddCommGrpCat.{u}
            (componentwiseTopology J M) (componentwiseTopology J N)).map
          ((freeSheafPushforwardIso J N).hom.app X) =
      (freeSheafPushforwardIso J M).hom.app X ≫
        (Sheaf.composeAndSheafify (componentwiseTopology J M) AddCommGrpCat.free).map
            ((relocalizationForgetPushforwardIso' J f (componentwiseTopology J M)
              (componentwiseTopology J N) (Type u)).inv.app X) ≫
          (Functor.freePushforwardIso (componentwiseTopology J M) (componentwiseTopology J N)
              (componentOverMap f)).inv.app
            (((componentOverForget N).sheafPushforwardContinuous (Type u)
              (componentwiseTopology J N) J).obj X) := by
  rw [← Category.assoc, freeSheafPushforwardIso_naturality' J f X, Category.assoc,
    Iso.hom_inv_id_app]
  exact (Category.comp_id _).symm

/-- **The `r_f`-part of the shriek restriction transition, carried across the free abelian sheaf
functor.** The reindexing of `j_M^{-1}ℤ_X^♯` into `r_f^{-1} j_N^{-1}ℤ_X^♯` followed by the counit
of `r_{f!} ⊣ r_f^{-1}`, then the commutation of the free abelian sheaf functor with `j_N^{-1}`,
is the commutation with `j_M^{-1}`, then the commutation with `r_{f!}`, then the free abelian
sheaf of the same `r_f`-part on sheaves of sets.

This is the whole content of the naturality of Stacks 0D87 part (2) on free abelian sheaves
that lies inside the `r_f`-leg of the relocalization triangle: the counit square
`CategoryTheory.Functor.freeLowerShriekIso_hom_app_comp_map_counit` for `r_f`, the restriction
square `freeSheafPushforwardIso_naturality_inv`, and the naturality of the extension-by-zero
commutation for `r_f`. -/
theorem freeAbelianShriekTransitionLeg (X : Sheaf J (Type u)) :
    ((Functor.sheafPullbackConstruction.sheafPullback (componentOverMap f) AddCommGrpCat.{u}
        (componentwiseTopology J M) (componentwiseTopology J N)).map
            ((relocalizationForgetPushforwardIso' J f (componentwiseTopology J M)
                (componentwiseTopology J N) AddCommGrpCat.{u}).inv.app ((Sheaf.composeAndSheafify J
                AddCommGrpCat.free).obj X)) ≫
          (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous (componentOverMap f)
              AddCommGrpCat.{u} (componentwiseTopology J M) (componentwiseTopology J N)).counit.app
            (((componentOverForget N).sheafPushforwardContinuous AddCommGrpCat.{u}
                (componentwiseTopology J N) J).obj ((Sheaf.composeAndSheafify J
                AddCommGrpCat.free).obj X))) ≫
        (freeSheafPushforwardIso J N).hom.app X =
      (Functor.sheafPullbackConstruction.sheafPullback (componentOverMap f) AddCommGrpCat.{u}
          (componentwiseTopology J M) (componentwiseTopology J N)).map ((freeSheafPushforwardIso J
          M).hom.app X) ≫
        (Functor.freeLowerShriekIso (componentwiseTopology J M) (componentwiseTopology J N)
            (componentOverMap f)).hom.app (((componentOverForget M).sheafPushforwardContinuous (Type
            u) (componentwiseTopology J M) J).obj X) ≫
          (Sheaf.composeAndSheafify (componentwiseTopology J N) AddCommGrpCat.free).map
            ((Functor.sheafPullbackConstruction.sheafPullback (componentOverMap f) (Type u)
                (componentwiseTopology J M) (componentwiseTopology J N)).map
                ((relocalizationForgetPushforwardIso' J f (componentwiseTopology J M)
                (componentwiseTopology J N) (Type u)).inv.app X) ≫
              (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous (componentOverMap f)
                  (Type u) (componentwiseTopology J M) (componentwiseTopology J N)).counit.app
                  (((componentOverForget N).sheafPushforwardContinuous (Type u)
                  (componentwiseTopology J N) J).obj X)) := by
  have hcounit :
      (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous (componentOverMap f)
          AddCommGrpCat.{u} (componentwiseTopology J M) (componentwiseTopology J N)).counit.app
          (((componentOverForget N).sheafPushforwardContinuous AddCommGrpCat.{u}
          (componentwiseTopology J N) J).obj ((Sheaf.composeAndSheafify J AddCommGrpCat.free).obj
          X)) ≫ (freeSheafPushforwardIso J N).hom.app X =
        (Functor.sheafPullbackConstruction.sheafPullback (componentOverMap f) AddCommGrpCat.{u}
            (componentwiseTopology J M) (componentwiseTopology J N)).map (((componentOverMap
            f).sheafPushforwardContinuous AddCommGrpCat.{u} (componentwiseTopology J M)
            (componentwiseTopology J N)).map ((freeSheafPushforwardIso J N).hom.app X)) ≫
          (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous (componentOverMap f)
              AddCommGrpCat.{u} (componentwiseTopology J M) (componentwiseTopology J N)).counit.app
              ((Sheaf.composeAndSheafify (componentwiseTopology J N) AddCommGrpCat.free).obj
              (((componentOverForget N).sheafPushforwardContinuous (Type u) (componentwiseTopology J
              N) J).obj X)) :=
    ((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous (componentOverMap f)
        AddCommGrpCat.{u} (componentwiseTopology J M) (componentwiseTopology J N)).counit_naturality
        ((freeSheafPushforwardIso J N).hom.app X)).symm
  have hS3 :
      (Functor.sheafPullbackConstruction.sheafPullback (componentOverMap f) AddCommGrpCat.{u}
          (componentwiseTopology J M) (componentwiseTopology J N)).map ((Functor.freePushforwardIso
          (componentwiseTopology J M) (componentwiseTopology J N) (componentOverMap f)).inv.app
          (((componentOverForget N).sheafPushforwardContinuous (Type u) (componentwiseTopology J N)
          J).obj X)) ≫
          (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous (componentOverMap f)
              AddCommGrpCat.{u} (componentwiseTopology J M) (componentwiseTopology J N)).counit.app
              ((Sheaf.composeAndSheafify (componentwiseTopology J N) AddCommGrpCat.free).obj
              (((componentOverForget N).sheafPushforwardContinuous (Type u) (componentwiseTopology J
              N) J).obj X)) =
        (Functor.freeLowerShriekIso (componentwiseTopology J M) (componentwiseTopology J N)
            (componentOverMap f)).hom.app (((componentOverMap f).sheafPushforwardContinuous (Type u)
            (componentwiseTopology J M) (componentwiseTopology J N)).obj (((componentOverForget
            N).sheafPushforwardContinuous (Type u) (componentwiseTopology J N) J).obj X)) ≫
          (Sheaf.composeAndSheafify (componentwiseTopology J N) AddCommGrpCat.free).map
              ((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous (componentOverMap f)
              (Type u) (componentwiseTopology J M) (componentwiseTopology J N)).counit.app
              (((componentOverForget N).sheafPushforwardContinuous (Type u) (componentwiseTopology J
              N) J).obj X)) :=
    (Functor.freeLowerShriekIso_hom_app_comp_map_counit (componentwiseTopology J M)
      (componentwiseTopology J N) (componentOverMap f) (((componentOverForget
          N).sheafPushforwardContinuous (Type u) (componentwiseTopology J N) J).obj X)).symm
  have hQr :
      (Functor.sheafPullbackConstruction.sheafPullback (componentOverMap f) AddCommGrpCat.{u}
          (componentwiseTopology J M) (componentwiseTopology J N)).map ((Sheaf.composeAndSheafify
          (componentwiseTopology J M) AddCommGrpCat.free).map ((relocalizationForgetPushforwardIso'
          J f (componentwiseTopology J M) (componentwiseTopology J N) (Type u)).inv.app X)) ≫
          (Functor.freeLowerShriekIso (componentwiseTopology J M) (componentwiseTopology J N)
              (componentOverMap f)).hom.app (((componentOverMap f).sheafPushforwardContinuous (Type
              u) (componentwiseTopology J M) (componentwiseTopology J N)).obj (((componentOverForget
              N).sheafPushforwardContinuous (Type u) (componentwiseTopology J N) J).obj X)) =
        (Functor.freeLowerShriekIso (componentwiseTopology J M) (componentwiseTopology J N)
            (componentOverMap f)).hom.app (((componentOverForget M).sheafPushforwardContinuous (Type
            u) (componentwiseTopology J M) J).obj X) ≫
          (Sheaf.composeAndSheafify (componentwiseTopology J N) AddCommGrpCat.free).map
              ((Functor.sheafPullbackConstruction.sheafPullback (componentOverMap f) (Type u)
              (componentwiseTopology J M) (componentwiseTopology J N)).map
              ((relocalizationForgetPushforwardIso' J f (componentwiseTopology J M)
              (componentwiseTopology J N) (Type u)).inv.app X)) :=
    (Functor.freeLowerShriekIso (componentwiseTopology J M) (componentwiseTopology J N)
        (componentOverMap f)).hom.naturality ((relocalizationForgetPushforwardIso' J f
        (componentwiseTopology J M) (componentwiseTopology J N) (Type u)).inv.app X)
  refine Eq.trans (Category.assoc _ _ _) ?_
  refine Eq.trans (whisker_eq _ hcounit) ?_
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine Eq.trans (eq_whisker (Functor.map_comp _ _ _).symm _) ?_
  refine Eq.trans (eq_whisker (congrArg (fun m => (Functor.sheafPullbackConstruction.sheafPullback
      (componentOverMap f) AddCommGrpCat.{u} (componentwiseTopology J M) (componentwiseTopology J
      N)).map m)
    (freeSheafPushforwardIso_naturality_inv J f X)) _) ?_
  refine Eq.trans (eq_whisker (Functor.map_comp _ _ _) _) ?_
  refine Eq.trans (eq_whisker (whisker_eq _ (Functor.map_comp _ _ _)) _) ?_
  refine Eq.trans (Category.assoc _ _ _) ?_
  refine Eq.trans (whisker_eq _ (Category.assoc _ _ _)) ?_
  refine Eq.trans (whisker_eq _ (whisker_eq _ hS3)) ?_
  refine Eq.trans (whisker_eq _ (Category.assoc _ _ _).symm) ?_
  refine Eq.trans (whisker_eq _ (eq_whisker hQr _)) ?_
  refine Eq.trans (whisker_eq _ (Category.assoc _ _ _)) ?_
  exact whisker_eq _ (whisker_eq _ (Functor.map_comp _ _ _).symm)

/-- **Stacks 0D87 part (2) on free abelian sheaves is natural in the semi-representable
object, on the restriction-and-extension factor.** For `f : M ⟶ N` the shriek restriction
transition `j_{M!}j_M^{-1} ⟶ j_{N!}j_N^{-1}` on abelian sheaves, read at a free abelian sheaf
ℤ_X^♯, is carried by the two commutations of the free abelian sheaf functor -- with restriction
along `j` and with extension by zero along `j` -- to the shriek restriction transition on sheaves
of sets.

The derivation is the counit square for `r_f` and the restriction square, packaged as
`freeAbelianShriekTransitionLeg`, the naturality of
`CategoryTheory.Functor.lowerShriekComp` on abelian sheaves and on sheaves of sets, the
naturality of `CategoryTheory.SemiRepresentable.freeSheafPullbackIso` of degree `N`, and the
composition compatibility `CategoryTheory.Functor.freeLowerShriekIso_comp`. The two instances of
`shriekRestrictionTransition_app_lowerShriekComp` are what put the transition in the shape those
squares fit together in. -/
theorem freeAbelianShriekRestrictionTransition (X : Sheaf J (Type u)) :
    (shriekRestrictionTransition J f (componentwiseTopology J M) (componentwiseTopology J N)
          AddCommGrpCat.{u}).app ((Sheaf.composeAndSheafify J AddCommGrpCat.free).obj X) ≫
        (Functor.sheafPullbackConstruction.sheafPullback (componentOverForget N) AddCommGrpCat.{u}
            (componentwiseTopology J N) J).map ((freeSheafPushforwardIso J N).hom.app X) ≫
            (freeSheafPullbackIso J N).hom.app (((componentOverForget N).sheafPushforwardContinuous
            (Type u) (componentwiseTopology J N) J).obj X) =
      (Functor.sheafPullbackConstruction.sheafPullback (componentOverForget M) AddCommGrpCat.{u}
          (componentwiseTopology J M) J).map ((freeSheafPushforwardIso J M).hom.app X) ≫
          (freeSheafPullbackIso J M).hom.app (((componentOverForget M).sheafPushforwardContinuous
          (Type u) (componentwiseTopology J M) J).obj X) ≫
        (Sheaf.composeAndSheafify J AddCommGrpCat.free).map
          ((shriekRestrictionTransition J f (componentwiseTopology J M)
            (componentwiseTopology J N) (Type u)).app X) := by
  have hLA :
      (Functor.lowerShriekComp (componentwiseTopology J M) (componentwiseTopology J N) J
          (componentOverMap f) (componentOverForget N) (componentOverForget M) AddCommGrpCat.{u}
          (eqToIso (componentOverMap_comp_componentOverForget f))).hom.app (((componentOverForget
          M).sheafPushforwardContinuous AddCommGrpCat.{u} (componentwiseTopology J M) J).obj
          ((Sheaf.composeAndSheafify J AddCommGrpCat.free).obj X)) ≫
          (Functor.sheafPullbackConstruction.sheafPullback (componentOverForget N) AddCommGrpCat.{u}
              (componentwiseTopology J N) J).map ((Functor.sheafPullbackConstruction.sheafPullback
              (componentOverMap f) AddCommGrpCat.{u} (componentwiseTopology J M)
              (componentwiseTopology J N)).map ((freeSheafPushforwardIso J M).hom.app X)) =
        (Functor.sheafPullbackConstruction.sheafPullback (componentOverForget M) AddCommGrpCat.{u}
            (componentwiseTopology J M) J).map ((freeSheafPushforwardIso J M).hom.app X) ≫
            (Functor.lowerShriekComp (componentwiseTopology J M) (componentwiseTopology J N) J
            (componentOverMap f) (componentOverForget N) (componentOverForget M) AddCommGrpCat.{u}
            (eqToIso (componentOverMap_comp_componentOverForget f))).hom.app
            ((Sheaf.composeAndSheafify (componentwiseTopology J M) AddCommGrpCat.free).obj
            (((componentOverForget M).sheafPushforwardContinuous (Type u) (componentwiseTopology J
            M) J).obj X)) :=
    ((Functor.lowerShriekComp (componentwiseTopology J M) (componentwiseTopology J N) J
        (componentOverMap f) (componentOverForget N) (componentOverForget M) AddCommGrpCat.{u}
        (eqToIso (componentOverMap_comp_componentOverForget f))).hom.naturality
        ((freeSheafPushforwardIso J M).hom.app X)).symm
  have hQN :
      (Functor.sheafPullbackConstruction.sheafPullback (componentOverForget N) AddCommGrpCat.{u}
          (componentwiseTopology J N) J).map ((Sheaf.composeAndSheafify (componentwiseTopology J N)
          AddCommGrpCat.free).map ((Functor.sheafPullbackConstruction.sheafPullback
          (componentOverMap f) (Type u) (componentwiseTopology J M) (componentwiseTopology J N)).map
          ((relocalizationForgetPushforwardIso' J f (componentwiseTopology J M)
          (componentwiseTopology J N) (Type u)).inv.app X) ≫
          (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous (componentOverMap f) (Type u)
          (componentwiseTopology J M) (componentwiseTopology J N)).counit.app (((componentOverForget
          N).sheafPushforwardContinuous (Type u) (componentwiseTopology J N) J).obj X))) ≫
          (freeSheafPullbackIso J N).hom.app (((componentOverForget N).sheafPushforwardContinuous
          (Type u) (componentwiseTopology J N) J).obj X) =
        (freeSheafPullbackIso J N).hom.app ((Functor.sheafPullbackConstruction.sheafPullback
            (componentOverMap f) (Type u) (componentwiseTopology J M) (componentwiseTopology J
            N)).obj (((componentOverForget M).sheafPushforwardContinuous (Type u)
            (componentwiseTopology J M) J).obj X)) ≫ (Sheaf.composeAndSheafify J
            AddCommGrpCat.free).map ((Functor.sheafPullbackConstruction.sheafPullback
            (componentOverForget N) (Type u) (componentwiseTopology J N) J).map
            ((Functor.sheafPullbackConstruction.sheafPullback (componentOverMap f) (Type u)
            (componentwiseTopology J M) (componentwiseTopology J N)).map
            ((relocalizationForgetPushforwardIso' J f (componentwiseTopology J M)
            (componentwiseTopology J N) (Type u)).inv.app X) ≫
            (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous (componentOverMap f) (Type
            u) (componentwiseTopology J M) (componentwiseTopology J N)).counit.app
            (((componentOverForget N).sheafPushforwardContinuous (Type u) (componentwiseTopology J
            N) J).obj X))) :=
    (freeSheafPullbackIso J N).hom.naturality ((Functor.sheafPullbackConstruction.sheafPullback
        (componentOverMap f) (Type u) (componentwiseTopology J M) (componentwiseTopology J N)).map
        ((relocalizationForgetPushforwardIso' J f (componentwiseTopology J M) (componentwiseTopology
        J N) (Type u)).inv.app X) ≫ (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
        (componentOverMap f) (Type u) (componentwiseTopology J M) (componentwiseTopology J
        N)).counit.app (((componentOverForget N).sheafPushforwardContinuous (Type u)
        (componentwiseTopology J N) J).obj X))
  have hS2 :
      (Functor.lowerShriekComp (componentwiseTopology J M) (componentwiseTopology J N) J
          (componentOverMap f) (componentOverForget N) (componentOverForget M) AddCommGrpCat.{u}
          (eqToIso (componentOverMap_comp_componentOverForget f))).hom.app
          ((Sheaf.composeAndSheafify (componentwiseTopology J M) AddCommGrpCat.free).obj
          (((componentOverForget M).sheafPushforwardContinuous (Type u) (componentwiseTopology J M)
          J).obj X)) ≫
          (Functor.sheafPullbackConstruction.sheafPullback (componentOverForget N) AddCommGrpCat.{u}
              (componentwiseTopology J N) J).map ((Functor.freeLowerShriekIso (componentwiseTopology
              J M) (componentwiseTopology J N) (componentOverMap f)).hom.app (((componentOverForget
              M).sheafPushforwardContinuous (Type u) (componentwiseTopology J M) J).obj X)) ≫
            (freeSheafPullbackIso J N).hom.app ((Functor.sheafPullbackConstruction.sheafPullback
                (componentOverMap f) (Type u) (componentwiseTopology J M) (componentwiseTopology J
                N)).obj (((componentOverForget M).sheafPushforwardContinuous (Type u)
                (componentwiseTopology J M) J).obj X)) =
        (freeSheafPullbackIso J M).hom.app (((componentOverForget M).sheafPushforwardContinuous
            (Type u) (componentwiseTopology J M) J).obj X) ≫ (Sheaf.composeAndSheafify J
            AddCommGrpCat.free).map ((Functor.lowerShriekComp (componentwiseTopology J M)
            (componentwiseTopology J N) J (componentOverMap f) (componentOverForget N)
            (componentOverForget M) (Type u) (eqToIso (componentOverMap_comp_componentOverForget
            f))).hom.app (((componentOverForget M).sheafPushforwardContinuous (Type u)
            (componentwiseTopology J M) J).obj X)) :=
    NatTrans.congr_app (Functor.freeLowerShriekIso_comp (componentwiseTopology J M)
      (componentwiseTopology J N) J (componentOverMap f) (componentOverForget N)
      (componentOverForget M) (eqToIso (componentOverMap_comp_componentOverForget f)))
      (((componentOverForget M).sheafPushforwardContinuous (Type u) (componentwiseTopology J M)
          J).obj X)
  have hS2' :
      (Functor.lowerShriekComp (componentwiseTopology J M) (componentwiseTopology J N) J
          (componentOverMap f) (componentOverForget N) (componentOverForget M) AddCommGrpCat.{u}
          (eqToIso (componentOverMap_comp_componentOverForget f))).hom.app
          ((Sheaf.composeAndSheafify (componentwiseTopology J M) AddCommGrpCat.free).obj
          (((componentOverForget M).sheafPushforwardContinuous (Type u) (componentwiseTopology J M)
          J).obj X)) ≫
            (Functor.sheafPullbackConstruction.sheafPullback (componentOverForget N)
                AddCommGrpCat.{u} (componentwiseTopology J N) J).map ((Functor.freeLowerShriekIso
                (componentwiseTopology J M) (componentwiseTopology J N) (componentOverMap
                f)).hom.app (((componentOverForget M).sheafPushforwardContinuous (Type u)
                (componentwiseTopology J M) J).obj X)) ≫
              (freeSheafPullbackIso J N).hom.app ((Functor.sheafPullbackConstruction.sheafPullback
                  (componentOverMap f) (Type u) (componentwiseTopology J M) (componentwiseTopology J
                  N)).obj (((componentOverForget M).sheafPushforwardContinuous (Type u)
                  (componentwiseTopology J M) J).obj X)) ≫
                (Sheaf.composeAndSheafify J AddCommGrpCat.free).map
                    ((Functor.sheafPullbackConstruction.sheafPullback (componentOverForget N) (Type
                    u) (componentwiseTopology J N) J).map
                    ((Functor.sheafPullbackConstruction.sheafPullback (componentOverMap f) (Type u)
                    (componentwiseTopology J M) (componentwiseTopology J N)).map
                    ((relocalizationForgetPushforwardIso' J f (componentwiseTopology J M)
                    (componentwiseTopology J N) (Type u)).inv.app X) ≫
                    (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous (componentOverMap
                    f) (Type u) (componentwiseTopology J M) (componentwiseTopology J N)).counit.app
                    (((componentOverForget N).sheafPushforwardContinuous (Type u)
                    (componentwiseTopology J N) J).obj X))) =
          (freeSheafPullbackIso J M).hom.app (((componentOverForget M).sheafPushforwardContinuous
              (Type u) (componentwiseTopology J M) J).obj X) ≫
            (Sheaf.composeAndSheafify J AddCommGrpCat.free).map ((Functor.lowerShriekComp
                (componentwiseTopology J M) (componentwiseTopology J N) J (componentOverMap f)
                (componentOverForget N) (componentOverForget M) (Type u) (eqToIso
                (componentOverMap_comp_componentOverForget f))).hom.app (((componentOverForget
                M).sheafPushforwardContinuous (Type u) (componentwiseTopology J M) J).obj X)) ≫
              (Sheaf.composeAndSheafify J AddCommGrpCat.free).map
                  ((Functor.sheafPullbackConstruction.sheafPullback (componentOverForget N) (Type u)
                  (componentwiseTopology J N) J).map
                  ((Functor.sheafPullbackConstruction.sheafPullback (componentOverMap f) (Type u)
                  (componentwiseTopology J M) (componentwiseTopology J N)).map
                  ((relocalizationForgetPushforwardIso' J f (componentwiseTopology J M)
                  (componentwiseTopology J N) (Type u)).inv.app X) ≫
                  (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous (componentOverMap f)
                  (Type u) (componentwiseTopology J M) (componentwiseTopology J N)).counit.app
                  (((componentOverForget N).sheafPushforwardContinuous (Type u)
                  (componentwiseTopology J N) J).obj X))) :=
    (whisker_eq _ (Category.assoc _ _ _).symm).trans
      ((Category.assoc _ _ _).symm.trans
        ((eq_whisker hS2 _).trans (Category.assoc _ _ _)))
  rw [shriekRestrictionTransition_app_lowerShriekComp J f (componentwiseTopology J M)
      (componentwiseTopology J N) AddCommGrpCat.{u} ((Sheaf.composeAndSheafify J
          AddCommGrpCat.free).obj X),
    shriekRestrictionTransition_app_lowerShriekComp J f (componentwiseTopology J M)
      (componentwiseTopology J N) (Type u) X]
  simp only [Category.assoc]
  rw [← Functor.map_comp_assoc, freeAbelianShriekTransitionLeg J f X,
    (Functor.sheafPullbackConstruction.sheafPullback (componentOverForget N) AddCommGrpCat.{u}
        (componentwiseTopology J N) J).map_comp, (Functor.sheafPullbackConstruction.sheafPullback
        (componentOverForget N) AddCommGrpCat.{u} (componentwiseTopology J N) J).map_comp]
  simp only [Category.assoc]
  rw [← Category.assoc, hLA, Category.assoc, hQN, hS2', (Sheaf.composeAndSheafify J
      AddCommGrpCat.free).map_comp]

section Component

variable (K : FormalCoproduct.{u} C)

/-- **The component of Stacks 0D87 part (2) on free abelian sheaves**, with the three associators
of its definition discharged: the commutation of the free abelian sheaf functor with restriction
along `j_K`, extended by zero; then the commutation with the extension by zero; then the free
abelian sheaf of Stacks 0D87 part (2) on sheaves of sets. -/
theorem freeSheafPushforwardCompSheafPullbackIso_hom_app (X : Sheaf J (Type u)) :
    (freeSheafPushforwardCompSheafPullbackIso J K).hom.app X =
      (Functor.sheafPullbackConstruction.sheafPullback (componentOverForget K) AddCommGrpCat.{u}
          (componentwiseTopology J K) J).map ((freeSheafPushforwardIso J K).hom.app X) ≫
        (freeSheafPullbackIso J K).hom.app (((componentOverForget K).sheafPushforwardContinuous
            (Type u) (componentwiseTopology J K) J).obj X) ≫
          (Sheaf.composeAndSheafify J AddCommGrpCat.free).map ((sheafPushforwardCompSheafPullbackIso
              J K).hom.app X) := by
  dsimp only [freeSheafPushforwardCompSheafPullbackIso, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, Functor.associator_hom_app, Functor.associator_inv_app,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app,
    Functor.whiskerLeft_app]
  simp only [Category.id_comp, Category.comp_id]

end Component

/-- **Stacks 0D87 part (2) on free abelian sheaves is natural in the semi-representable
object.** For `f : M ⟶ N` the shriek restriction transition `j_{M!}j_M^{-1} ⟶ j_{N!}j_N^{-1}` on
abelian sheaves, read at a free abelian sheaf `ℤ_X^♯`, is carried by the two instances of
Stacks 0D87 part (2) on free abelian sheaves to the free abelian sheaf of `X ⊗ F(f)^♯`.

This is `freeAbelianShriekRestrictionTransition` followed by the free abelian sheaf of the
set-level square `CategoryTheory.SemiRepresentable`
`.shriekRestrictionTransition_comp_sheafPushforwardCompSheafPullbackIso`. -/
theorem shriekRestrictionTransition_comp_freeSheafPushforwardCompSheafPullbackIso
    (X : Sheaf J (Type u)) :
    (shriekRestrictionTransition J f (componentwiseTopology J M) (componentwiseTopology J N)
          AddCommGrpCat.{u}).app ((Sheaf.composeAndSheafify J AddCommGrpCat.free).obj X) ≫
        (freeSheafPushforwardCompSheafPullbackIso J N).hom.app X =
      (freeSheafPushforwardCompSheafPullbackIso J M).hom.app X ≫
        (Sheaf.composeAndSheafify J AddCommGrpCat.free).map
          (X ◁ formalCoproductSheafificationMap J f) := by
  have hset :
      (Sheaf.composeAndSheafify J AddCommGrpCat.free).map
            ((shriekRestrictionTransition J f (componentwiseTopology J M)
              (componentwiseTopology J N) (Type u)).app X) ≫
          (Sheaf.composeAndSheafify J AddCommGrpCat.free).map ((sheafPushforwardCompSheafPullbackIso
              J N).hom.app X) =
        (Sheaf.composeAndSheafify J AddCommGrpCat.free).map ((sheafPushforwardCompSheafPullbackIso J
            M).hom.app X) ≫
          (Sheaf.composeAndSheafify J AddCommGrpCat.free).map (X ◁ formalCoproductSheafificationMap
              J f) :=
    (((Sheaf.composeAndSheafify J AddCommGrpCat.free)).map_comp _ _).symm.trans
      ((congrArg ((Sheaf.composeAndSheafify J AddCommGrpCat.free)).map
          (shriekRestrictionTransition_comp_sheafPushforwardCompSheafPullbackIso J f X)).trans
        (((Sheaf.composeAndSheafify J AddCommGrpCat.free)).map_comp _ _))
  rw [freeSheafPushforwardCompSheafPullbackIso_hom_app,
    freeSheafPushforwardCompSheafPullbackIso_hom_app]
  simp only [Category.assoc]
  refine Eq.trans (whisker_eq _ (Category.assoc _ _ _).symm) ?_
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  rw [freeAbelianShriekRestrictionTransition J f X]
  simp only [Category.assoc]
  rw [hset]
  rfl

section ComponentYoneda

variable (K : FormalCoproduct.{u} C)

/-- **The component of `j_! j^{-1} ℤ_V^♯ ≅ ℤ_{h_V × F(K)}^♯`**, with the three factors of its
definition exposed: the identification of `ℤ_V^♯` with the free abelian sheaf of the sheafified
`h_V`, restricted and extended by zero; then Stacks 0D87 part (2) on free abelian sheaves at that
sheafification; then the free abelian sheaf of the product. -/
theorem freeYonedaSheafPushforwardPullbackIso_hom (V : C) :
    (freeYonedaSheafPushforwardPullbackIso J K V).hom =
      (((componentOverForget K).sheafPushforwardContinuous AddCommGrpCat.{u} (componentwiseTopology
          J K) J) ⋙ (Functor.sheafPullbackConstruction.sheafPullback (componentOverForget K)
          AddCommGrpCat.{u} (componentwiseTopology J K) J)).map
          (((presheafToSheafCompComposeAndSheafifyIso J AddCommGrpCat.free).app (yoneda.obj V)).inv)
          ≫
        (freeSheafPushforwardCompSheafPullbackIso J K).hom.app (((presheafToSheaf J (Type u)).obj
            (yoneda.obj V))) ≫
          (freeAbelianSheafTensorIso J (yoneda.obj V)
            ((FormalCoproduct.yoneda (C := C)).obj K)).hom :=
  rfl

end ComponentYoneda

/-- **`j_! j^{-1} ℤ_V^♯ ≅ ℤ_{h_V × F(K)}^♯` is natural in the semi-representable object.** For
`f : M ⟶ N` the shriek restriction transition `j_{M!}j_M^{-1} ⟶ j_{N!}j_N^{-1}` read at `ℤ_V^♯`
is carried by the two instances of Stacks 0D87 part (2) on free abelian sheaves to the free
abelian sheaf of `h_V × F(f)`.

This is the naturality of the shriek restriction transition itself at the identification of
`ℤ_V^♯` with the free abelian sheaf of the sheafified `h_V`, then
`shriekRestrictionTransition_comp_freeSheafPushforwardCompSheafPullbackIso`, then
`CategoryTheory.SemiRepresentable.freeAbelianSheafTensorIso_naturality` at `F(f)`. -/
theorem shriekRestrictionTransition_comp_freeYonedaSheafPushforwardPullbackIso (V : C) :
    (shriekRestrictionTransition J f (componentwiseTopology J M) (componentwiseTopology J N)
          AddCommGrpCat.{u}).app
          (Stacks.Cohomology.CohomologyPresheaf.freeYonedaSheaf J V) ≫
        (freeYonedaSheafPushforwardPullbackIso J N V).hom =
      (freeYonedaSheafPushforwardPullbackIso J M V).hom ≫
        (presheafToSheaf J AddCommGrpCat.{u}).map
          (Functor.whiskerRight (Limits.prod.map (𝟙 (yoneda.obj V)) (((FormalCoproduct.yoneda (C :=
              C)).map f)))
            AddCommGrpCat.free) := by
  have hnat :
      (shriekRestrictionTransition J f (componentwiseTopology J M) (componentwiseTopology J N)
              AddCommGrpCat.{u}).app
            (Stacks.Cohomology.CohomologyPresheaf.freeYonedaSheaf J V) ≫
          (((componentOverForget N).sheafPushforwardContinuous AddCommGrpCat.{u}
              (componentwiseTopology J N) J) ⋙ (Functor.sheafPullbackConstruction.sheafPullback
              (componentOverForget N) AddCommGrpCat.{u} (componentwiseTopology J N) J)).map
              (((presheafToSheafCompComposeAndSheafifyIso J AddCommGrpCat.free).app (yoneda.obj
              V)).inv) =
        (((componentOverForget M).sheafPushforwardContinuous AddCommGrpCat.{u}
            (componentwiseTopology J M) J) ⋙ (Functor.sheafPullbackConstruction.sheafPullback
            (componentOverForget M) AddCommGrpCat.{u} (componentwiseTopology J M) J)).map
            (((presheafToSheafCompComposeAndSheafifyIso J AddCommGrpCat.free).app (yoneda.obj
            V)).inv) ≫
          (shriekRestrictionTransition J f (componentwiseTopology J M)
            (componentwiseTopology J N) AddCommGrpCat.{u}).app
            ((Sheaf.composeAndSheafify J AddCommGrpCat.free).obj (((presheafToSheaf J (Type u)).obj
                (yoneda.obj V)))) :=
    ((shriekRestrictionTransition J f (componentwiseTopology J M) (componentwiseTopology J N)
      AddCommGrpCat.{u}).naturality (((presheafToSheafCompComposeAndSheafifyIso J
          AddCommGrpCat.free).app (yoneda.obj V)).inv)).symm
  have htensor :
      (Sheaf.composeAndSheafify J AddCommGrpCat.free).map
            (((presheafToSheaf J (Type u)).obj (yoneda.obj V)) ◁ formalCoproductSheafificationMap J
                f) ≫
          (freeAbelianSheafTensorIso J (yoneda.obj V)
            ((FormalCoproduct.yoneda (C := C)).obj N)).hom =
        (freeAbelianSheafTensorIso J (yoneda.obj V)
              ((FormalCoproduct.yoneda (C := C)).obj M)).hom ≫
          (presheafToSheaf J AddCommGrpCat.{u}).map
            (Functor.whiskerRight (Limits.prod.map (𝟙 (yoneda.obj V)) (((FormalCoproduct.yoneda (C
                := C)).map f)))
              AddCommGrpCat.free) :=
    freeAbelianSheafTensorIso_naturality J (yoneda.obj V)
      ((FormalCoproduct.yoneda (C := C)).obj M) ((FormalCoproduct.yoneda (C := C)).obj N)
          (((FormalCoproduct.yoneda (C := C)).map f))
  rw [freeYonedaSheafPushforwardPullbackIso_hom, freeYonedaSheafPushforwardPullbackIso_hom]
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine Eq.trans (eq_whisker hnat _) ?_
  refine Eq.trans (Category.assoc _ _ _) ?_
  refine Eq.trans (whisker_eq _ (Category.assoc _ _ _).symm) ?_
  refine Eq.trans (whisker_eq _ (eq_whisker
    (shriekRestrictionTransition_comp_freeSheafPushforwardCompSheafPullbackIso J f
      ((presheafToSheaf J (Type u)).obj (yoneda.obj V))) _)) ?_
  refine Eq.trans (whisker_eq _ (Category.assoc _ _ _)) ?_
  refine Eq.trans (whisker_eq _ (whisker_eq _ htensor)) ?_
  refine Eq.trans (whisker_eq _ (Category.assoc _ _ _).symm) ?_
  exact (Category.assoc _ _ _).symm

end CategoryTheory.SemiRepresentable

end
