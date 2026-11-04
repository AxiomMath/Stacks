module

public import StacksFrontier.CategoryTheory.Abelian.Projective.SplitResolutionSes

/-! # Comparing `Lₙ G ∘ W` with `Lₙ (W ⋙ G)` for an exact `W`

Let `W : C ⥤ D` be an exact additive functor between abelian categories with enough projectives
and let `G : D ⥤ T` be additive. There are two ways to derive in the `C`-direction: derive `G` on
`D` and evaluate at `W X`, or derive the composite `W ⋙ G` on `C` and evaluate at `X`. This file
constructs the comparison

`Lₙ G (W X) ⟶ Lₙ (W ⋙ G) (X)`

and proves the three statements that make it usable: it does not depend on the resolutions chosen
to compute it, it is natural in `X`, and it commutes with the connecting morphisms of the two
long exact sequences. In other words it is a morphism of homological δ-functors; that is what the
universality of a δ-functor is applied to.

The construction is `CategoryTheory.ProjectiveResolution.lift'`: the `W`-image of a projective
resolution of `X` is a resolution of `W X`, not a projective one, so a projective resolution of
`W X` lifts into it, uniquely up to homotopy; applying `G` and taking homology gives the
comparison. As with `CategoryTheory.ProjectiveResolution.transferHomology`, the point of the
construction is `leftDerivedCompAppOf_eq`: *any* augmentation-compatible chain map computes it,
which is what makes all three statements provable, since each exhibits a different convenient
lift.

For the connecting morphisms the convenient lift is the one produced by
`CategoryTheory.ShortComplex.SplitResolutionSes.mapSesHom`: a horseshoe for `S.map W` lifts into
the `W`-image of a horseshoe for `S`, which is a degreewise split short exact sequence of
resolutions and never one of projective resolutions — which is exactly why that generalization of
the horseshoe morphism is needed here.

## Main definitions

* `CategoryTheory.Functor.leftDerivedCompAppOf`: the comparison computed from a given pair of
  projective resolutions.
* `CategoryTheory.Functor.leftDerivedCompApp`: the comparison `Lₙ G (W X) ⟶ Lₙ (W ⋙ G) (X)`,
  computed from the chosen projective resolutions.
* `CategoryTheory.Functor.leftDerivedComp`: the same, as a natural transformation
  `W ⋙ Lₙ G ⟶ Lₙ (W ⋙ G)`.

## Main results

* `CategoryTheory.Functor.leftDerivedCompAppOf_eq`: any augmentation-compatible chain map from
  the projective resolution of `W X` into the `W`-image of the projective resolution of `X`
  computes the comparison.
* `CategoryTheory.Functor.leftDerivedCompAppOf_fst`, `leftDerivedCompAppOf_snd` and
  `leftDerivedCompAppOf_eq_app`: the comparison does not depend on either resolution.
* `CategoryTheory.Functor.leftDerivedCompApp_naturality`: it is natural in `X`.
* `CategoryTheory.Functor.leftDerivedCompApp_δ`: it commutes with the connecting morphisms.

## Implementation notes

**Why the comparison is parametrized by the resolutions rather than fixed to the chosen ones.**
`CategoryTheory.ShortComplex.horseshoe` is `@[no_expose]`, so outside its own module the fact
that its outer resolutions *are* the chosen projective resolutions is not available even as a
definitional equality — a `rfl` proof of `(horseshoe hS).PA = ProjectiveResolution.of S.X₁` is
rejected for an exported theorem, and the chain map `mapτ₁` out of `(horseshoe hS).PA.complex`
does not even typecheck as a chain map out of `(ProjectiveResolution.of S.X₁).complex`. The
comparison is therefore defined for an arbitrary pair of resolutions and proved independent of
the choice, which is the better statement anyway, and the connecting-morphism compatibility is
proved at the horseshoe's own resolutions and transported.

**`(W ⋙ G).mapHomologicalComplex` against `G.mapHomologicalComplex ∘ W.mapHomologicalComplex`.**
They are equal by `rfl` but not syntactically, and the object between the comparison's homology
factor and the inverse comparison isomorphism is spelled one way by the first and the other way
by the second. So `rw [Category.assoc]` and `rw [Iso.inv_hom_id_assoc]` report no occurrence of
patterns that print exactly; the reassociation is done inside
`CategoryTheory.ShortComplex.SplitResolutionSes.δ_comp_transfer`, where one spelling is used
throughout and the trailing morphism is a parameter, and the use site closes by `exact`, which
checks the definitional equality at default transparency.

**`Functor.comp_map` in the `simp` sets.** A statement written `(F ⋙ G).map x` is stored folded
in some declarations below and unfolded in others, depending on how it was elaborated. Adding
`CategoryTheory.Functor.comp_map` to the `simp only` sets puts every occurrence in the unfolded
form, so that the rewrites match.

## References

* [Stacks Project, Tag 08PG](https://stacks.math.columbia.edu/tag/08PG)
* [Stacks Project, Tag 08PH](https://stacks.math.columbia.edu/tag/08PH)
-/

@[expose] public noncomputable section

open CategoryTheory Category Limits

universe v u v₂ u₂ vT uT

namespace CategoryTheory.Functor

section Bridge

variable {C : Type u} [Category.{v} C] [Abelian C] [EnoughProjectives C]
  {T : Type uT} [Category.{vT} T] [Abelian T]

/-- Two projective resolutions of the same object give the same left derived functor: the lift of
the identity intertwines the two comparison isomorphisms. This is
`CategoryTheory.Functor.leftDerived_map_eq` at the identity. -/
lemma isoLeftDerivedObj_hom_comp_lift (F : C ⥤ T) [F.Additive] {X : C}
    (P P' : ProjectiveResolution X) (n : ℕ) :
    (P.isoLeftDerivedObj F n).hom ≫
        (F.mapHomologicalComplex (ComplexShape.down ℕ) ⋙
          HomologicalComplex.homologyFunctor T (ComplexShape.down ℕ) n).map
            (ProjectiveResolution.lift (𝟙 X) P P') =
      (P'.isoLeftDerivedObj F n).hom := by
  rw [← cancel_mono (P'.isoLeftDerivedObj F n).inv, Category.assoc,
    ← Functor.leftDerived_map_eq F n (𝟙 X) (P := P) (Q := P')
      (ProjectiveResolution.lift (𝟙 X) P P') (ProjectiveResolution.lift_commutes _ _ _)]
  simp

/-- The inverse form of `CategoryTheory.Functor.isoLeftDerivedObj_hom_comp_lift`. -/
lemma isoLeftDerivedObj_inv_eq_lift (F : C ⥤ T) [F.Additive] {X : C}
    (P P' : ProjectiveResolution X) (n : ℕ) :
    (P.isoLeftDerivedObj F n).inv =
      (F.mapHomologicalComplex (ComplexShape.down ℕ) ⋙
        HomologicalComplex.homologyFunctor T (ComplexShape.down ℕ) n).map
          (ProjectiveResolution.lift (𝟙 X) P P') ≫ (P'.isoLeftDerivedObj F n).inv := by
  rw [Iso.eq_comp_inv, ← isoLeftDerivedObj_hom_comp_lift F P P' n, Iso.inv_hom_id_assoc]

end Bridge

section Comparison

variable {C : Type u} [Category.{v} C] [Abelian C] [EnoughProjectives C]
  {D : Type u₂} [Category.{v₂} D] [Abelian D] [EnoughProjectives D]
  {T : Type uT} [Category.{vT} T] [Abelian T]
  (W : C ⥤ D) [W.Additive] [PreservesFiniteLimits W] [PreservesFiniteColimits W]
  (G : D ⥤ T) [G.Additive]

/-- The `W`-image of a projective resolution of `X`, as a resolution of `W X`. It is a
resolution, not a projective one: `W` is exact, so it preserves homology and the augmentation
stays a quasi-isomorphism, but it has no reason to preserve projectivity. -/
abbrev mapAugOf {X : C} (P : ProjectiveResolution X) :
    (W.mapHomologicalComplex (ComplexShape.down ℕ)).obj P.complex ⟶
      (ChainComplex.single₀ D).obj (W.obj X) :=
  W.mapAugmentation P.π

/-- The lift of the identity of `W X` from a projective resolution of `W X` into the `W`-image of
a projective resolution of `X`. -/
abbrev leftDerivedCompLift {X : C} (P : ProjectiveResolution X)
    (Q : ProjectiveResolution (W.obj X)) :
    Q.complex ⟶ (W.mapHomologicalComplex (ComplexShape.down ℕ)).obj P.complex :=
  ProjectiveResolution.lift' (𝟙 (W.obj X)) Q (mapAugOf W P)

/-- **The comparison `Lₙ G (W X) ⟶ Lₙ (W ⋙ G) (X)`** for an exact additive `W`, computed from a
projective resolution `P` of `X` and a projective resolution `Q` of `W X`: lift the identity of
`W X` from `Q` into the `W`-image of `P`, apply `G`, and take homology. By
`leftDerivedCompAppOf_fst` and `leftDerivedCompAppOf_snd` it does not depend on `P` or `Q`. -/
def leftDerivedCompAppOf (n : ℕ) {X : C} (P : ProjectiveResolution X)
    (Q : ProjectiveResolution (W.obj X)) :
    (G.leftDerived n).obj (W.obj X) ⟶ ((W ⋙ G).leftDerived n).obj X :=
  (Q.isoLeftDerivedObj G n).hom ≫
    (G.mapHomologicalComplex (ComplexShape.down ℕ) ⋙
      HomologicalComplex.homologyFunctor T (ComplexShape.down ℕ) n).map
        (leftDerivedCompLift W P Q) ≫
    (P.isoLeftDerivedObj (W ⋙ G) n).inv

/-- **Any augmentation-compatible chain map computes the comparison**, not only the chosen lift:
two such are homotopic by `CategoryTheory.ProjectiveResolution.liftHomotopy'`, hence induce the
same map on the homology of their images under `G`. This is the only property of the construction
that the statements below use. -/
lemma leftDerivedCompAppOf_eq (n : ℕ) {X : C} (P : ProjectiveResolution X)
    (Q : ProjectiveResolution (W.obj X))
    (ψ : Q.complex ⟶ (W.mapHomologicalComplex (ComplexShape.down ℕ)).obj P.complex)
    (hψ : ψ ≫ mapAugOf W P = Q.π ≫ (ChainComplex.single₀ D).map (𝟙 (W.obj X))) :
    leftDerivedCompAppOf W G n P Q =
      (Q.isoLeftDerivedObj G n).hom ≫
        (G.mapHomologicalComplex (ComplexShape.down ℕ) ⋙
          HomologicalComplex.homologyFunctor T (ComplexShape.down ℕ) n).map ψ ≫
        (P.isoLeftDerivedObj (W ⋙ G) n).inv := by
  dsimp only [leftDerivedCompAppOf]
  congr 2
  exact ProjectiveResolution.homologyMap_map_eq_of_comp_eq (mapAugOf W P) G _ ψ
    (by rw [ProjectiveResolution.lift'_commutes, hψ]) n

/-- The comparison does not depend on the projective resolution of `W X`. -/
lemma leftDerivedCompAppOf_snd (n : ℕ) {X : C} (P : ProjectiveResolution X)
    (Q Q' : ProjectiveResolution (W.obj X)) :
    leftDerivedCompAppOf W G n P Q = leftDerivedCompAppOf W G n P Q' := by
  have hw : (ProjectiveResolution.lift (𝟙 (W.obj X)) Q Q' ≫ leftDerivedCompLift W P Q') ≫
      mapAugOf W P = Q.π ≫ (ChainComplex.single₀ D).map (𝟙 (W.obj X)) := by
    rw [Category.assoc, ProjectiveResolution.lift'_commutes]
    simp [ProjectiveResolution.lift_commutes]
  rw [leftDerivedCompAppOf_eq W G n P Q _ hw]
  dsimp only [leftDerivedCompAppOf]
  simp only [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.comp_map, Category.assoc]
  rw [reassoc_of% isoLeftDerivedObj_hom_comp_lift G Q Q' n]

/-- The comparison does not depend on the projective resolution of `X`. -/
lemma leftDerivedCompAppOf_fst (n : ℕ) {X : C} (P P' : ProjectiveResolution X)
    (Q : ProjectiveResolution (W.obj X)) :
    leftDerivedCompAppOf W G n P Q = leftDerivedCompAppOf W G n P' Q := by
  have hw : (leftDerivedCompLift W P Q ≫ (W.mapHomologicalComplex (ComplexShape.down ℕ)).map
        (ProjectiveResolution.lift (𝟙 X) P P')) ≫ mapAugOf W P' =
      Q.π ≫ (ChainComplex.single₀ D).map (𝟙 (W.obj X)) := by
    rw [Category.assoc, Functor.map_comp_mapAugmentation,
      ProjectiveResolution.lift_commutes (𝟙 X), Functor.mapAugmentation_comp_single₀_map]
    simp [ProjectiveResolution.lift'_commutes]
  rw [leftDerivedCompAppOf_eq W G n P' Q _ hw]
  dsimp only [leftDerivedCompAppOf]
  simp only [CategoryTheory.Functor.comp_map]
  rw [show (G.mapHomologicalComplex (ComplexShape.down ℕ)).map
        (leftDerivedCompLift W P Q ≫ (W.mapHomologicalComplex (ComplexShape.down ℕ)).map
          (ProjectiveResolution.lift (𝟙 X) P P')) =
      (G.mapHomologicalComplex (ComplexShape.down ℕ)).map (leftDerivedCompLift W P Q) ≫
        ((W ⋙ G).mapHomologicalComplex (ComplexShape.down ℕ)).map
          (ProjectiveResolution.lift (𝟙 X) P P') from
    CategoryTheory.Functor.map_comp _ _ _]
  rw [CategoryTheory.Functor.map_comp, isoLeftDerivedObj_inv_eq_lift (W ⋙ G) P P' n]
  simp only [CategoryTheory.Functor.comp_map, Category.assoc]

/-- **The comparison `Lₙ G (W X) ⟶ Lₙ (W ⋙ G) (X)`**, computed from the chosen projective
resolutions. -/
def leftDerivedCompApp (n : ℕ) (X : C) :
    (G.leftDerived n).obj (W.obj X) ⟶ ((W ⋙ G).leftDerived n).obj X :=
  leftDerivedCompAppOf W G n (ProjectiveResolution.of X) (ProjectiveResolution.of (W.obj X))

/-- The comparison is computed by *any* pair of projective resolutions. -/
lemma leftDerivedCompAppOf_eq_app (n : ℕ) {X : C} (P : ProjectiveResolution X)
    (Q : ProjectiveResolution (W.obj X)) :
    leftDerivedCompAppOf W G n P Q = leftDerivedCompApp W G n X :=
  (leftDerivedCompAppOf_fst W G n P (ProjectiveResolution.of X) Q).trans
    (leftDerivedCompAppOf_snd W G n (ProjectiveResolution.of X) Q
      (ProjectiveResolution.of (W.obj X)))

/-- **The comparison is natural in `X`.** Both composites in the square are computed by a chain
map from the chosen projective resolution of `W X` into the `W`-image of the chosen projective
resolution of `Y` covering `W h`, and any two such agree after `G` and homology. -/
lemma leftDerivedCompApp_naturality (n : ℕ) {X Y : C} (h : X ⟶ Y) :
    (G.leftDerived n).map (W.map h) ≫ leftDerivedCompApp W G n Y =
      leftDerivedCompApp W G n X ≫ ((W ⋙ G).leftDerived n).map h := by
  have hw : (ProjectiveResolution.lift (W.map h) (ProjectiveResolution.of (W.obj X))
          (ProjectiveResolution.of (W.obj Y)) ≫
        leftDerivedCompLift W (ProjectiveResolution.of Y)
          (ProjectiveResolution.of (W.obj Y))) ≫
      mapAugOf W (ProjectiveResolution.of Y) =
      (leftDerivedCompLift W (ProjectiveResolution.of X) (ProjectiveResolution.of (W.obj X)) ≫
        (W.mapHomologicalComplex (ComplexShape.down ℕ)).map
          (ProjectiveResolution.lift h (ProjectiveResolution.of X)
            (ProjectiveResolution.of Y))) ≫ mapAugOf W (ProjectiveResolution.of Y) := by
    simp only [Category.assoc]
    rw [ProjectiveResolution.lift'_commutes, Functor.map_comp_mapAugmentation,
      ProjectiveResolution.lift_commutes h, Functor.mapAugmentation_comp_single₀_map]
    simp [ProjectiveResolution.lift_commutes]
  rw [Functor.leftDerived_map_eq G n (W.map h)
      (P := ProjectiveResolution.of (W.obj X)) (Q := ProjectiveResolution.of (W.obj Y))
      (ProjectiveResolution.lift (W.map h) _ _) (ProjectiveResolution.lift_commutes _ _ _),
    Functor.leftDerived_map_eq (W ⋙ G) n h
      (P := ProjectiveResolution.of X) (Q := ProjectiveResolution.of Y)
      (ProjectiveResolution.lift h _ _) (ProjectiveResolution.lift_commutes _ _ _)]
  dsimp only [leftDerivedCompApp, leftDerivedCompAppOf]
  simp only [Category.assoc, Iso.inv_hom_id_assoc, CategoryTheory.Functor.comp_map]
  rw [show ((W ⋙ G).mapHomologicalComplex (ComplexShape.down ℕ)).map
        (ProjectiveResolution.lift h (ProjectiveResolution.of X) (ProjectiveResolution.of Y)) =
      (G.mapHomologicalComplex (ComplexShape.down ℕ)).map
        ((W.mapHomologicalComplex (ComplexShape.down ℕ)).map
          (ProjectiveResolution.lift h (ProjectiveResolution.of X)
            (ProjectiveResolution.of Y))) from rfl]
  rw [← Functor.map_comp_assoc, ← Functor.map_comp_assoc, ← Functor.map_comp, ← Functor.map_comp]
  congr 2
  exact ProjectiveResolution.homologyMap_map_eq_of_comp_eq
    (mapAugOf W (ProjectiveResolution.of Y)) G _ _ hw n

/-- **The comparison, as a natural transformation `W ⋙ Lₙ G ⟶ Lₙ (W ⋙ G)`.** -/
def leftDerivedComp (n : ℕ) : W ⋙ G.leftDerived n ⟶ (W ⋙ G).leftDerived n where
  app X := leftDerivedCompApp W G n X
  naturality _ _ h := leftDerivedCompApp_naturality W G n h

/-- The components of `CategoryTheory.Functor.leftDerivedComp`. -/
@[simp]
lemma leftDerivedComp_app (n : ℕ) (X : C) :
    (leftDerivedComp W G n).app X = leftDerivedCompApp W G n X :=
  rfl

open ShortComplex in
/-- **The comparison commutes with the connecting morphisms.** The lift used to compute it is the
one produced by `CategoryTheory.ShortComplex.SplitResolutionSes.mapSesHom` from the chosen
horseshoe of `S.map W` into the `W`-image of the chosen horseshoe of `S`, and the statement is
then the naturality of the connecting morphism of the long exact homology sequence for that
morphism of short exact sequences of complexes. -/
theorem leftDerivedCompApp_δ {S : ShortComplex C} (hS : S.ShortExact) (n : ℕ) :
    G.leftDerivedδ (hS.map_of_exact W) n ≫ leftDerivedCompApp W G n S.X₁ =
      leftDerivedCompApp W G (n + 1) S.X₃ ≫ (W ⋙ G).leftDerivedδ hS n := by
  have hδ : (W ⋙ G).leftDerivedδ hS n =
      ((horseshoe hS).PC.isoLeftDerivedObj (W ⋙ G) (n + 1)).hom ≫
        ((horseshoe hS).mapSes_shortExact (W ⋙ G)).δ (n + 1) n (down_rel_succ n) ≫
          ((horseshoe hS).PA.isoLeftDerivedObj (W ⋙ G) n).inv :=
    Horseshoe.δ_eq (horseshoe hS) (W ⋙ G) n
  rw [← leftDerivedCompAppOf_eq_app W G n (horseshoe hS).PA
      (horseshoe (hS.map_of_exact W)).PA,
    ← leftDerivedCompAppOf_eq_app W G (n + 1) (horseshoe hS).PC
      (horseshoe (hS.map_of_exact W)).PC,
    leftDerivedCompAppOf_eq W G n (horseshoe hS).PA (horseshoe (hS.map_of_exact W)).PA
      (SplitResolutionSes.mapτ₁ (horseshoe (hS.map_of_exact W))
        ((horseshoe hS).toSplitResolutionSes.mapExact W) (𝟙 (S.map W)))
      (SplitResolutionSes.mapτ₁_comm _ _ _),
    leftDerivedCompAppOf_eq W G (n + 1) (horseshoe hS).PC (horseshoe (hS.map_of_exact W)).PC
      (SplitResolutionSes.mapτ₃ (horseshoe (hS.map_of_exact W))
        ((horseshoe hS).toSplitResolutionSes.mapExact W) (𝟙 (S.map W)))
      (SplitResolutionSes.mapτ₃_comm _ _ _), hδ]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  exact SplitResolutionSes.δ_comp_transfer (horseshoe (hS.map_of_exact W))
    ((horseshoe hS).toSplitResolutionSes.mapExact W) G n _

end Comparison

end CategoryTheory.Functor

end
