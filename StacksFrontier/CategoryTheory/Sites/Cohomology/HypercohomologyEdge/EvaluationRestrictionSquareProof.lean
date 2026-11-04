module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.HypercohomologyEdge.EvaluationRestrictionHomotopySquare
public import StacksFrontier.Algebra.Homology.DerivedCategory.ExactDerivedHomologyComposition

/-!
# The evaluation restriction square, discharged

The naturality in the object of the site of
`Stacks.Cohomology.HypercohomologyEdge.sectionsEvaluationIso` reduces to a square on the homotopy
category in which no right derived functor and no unit occurs — the hypothesis `hsq` of
`Stacks.Cohomology.HypercohomologyEdge.sectionsEvaluationIso_restrict_of_homotopySquare`.  This
file proves that square and so makes both consequences unconditional.

Two observations do it.

* The underived comparison is the general one.
  `Stacks.Cohomology.HypercohomologyEdge.homotopySectionsEvaluationIso` *is*
  `Stacks.Homology.derivedSourceIso` of the forgetful functor against evaluation at the object —
  the two are the same morphism, the chains they are assembled from differing only by
  associators — so the square in the object of the site is an instance of
  `Stacks.Homology.derivedSourceIso_hom_naturality`, naturality of that comparison in the exact
  functor it is taken against.  The exact functor here is
  `CategoryTheory.PresheafOfModules.restriction`, a transformation from evaluation at `U` to
  evaluation at `U'` read through restriction of scalars; the transformation it induces on
  complexes of sections is exactly
  `Stacks.Cohomology.HypercohomologyEdge.sectionsRestrict`.

* What remains is the composition law for that comparison against the restriction of scalars,
  `derivedSourceIso_comp`: the comparison for `E ⋙ Res` is the comparison for `E` read through
  `Res`, once the degreewise action of `Res` has been identified with its action on the derived
  category and homology has been commuted past it.  That is where the two factors of
  `Stacks.Cohomology.HypercohomologyEdge.homotopySectionsRestrict` beyond the termwise
  restriction, and `Stacks.Homology.derivedHomologyIso`, are consumed.  It rests on the
  composition law of `Stacks.Homology.exactHomologyIso` and on the agreement of the homotopy-
  and derived-category homology comparisons of one exact functor,
  `derivedHomologyIso_homotopyHomologyIso`.

Nothing here is a clause of a tag's statement: every declaration is a step in the proof of a
hypothesis the previous file left open, so no `@[stacks ...]` attribute appears.

## Main results

* `Stacks.Cohomology.HypercohomologyEdge.sectionsEvaluationIso_restrict_homotopySquare`: the
  unit-free square on the homotopy category, which is what was left open.
* `Stacks.Cohomology.HypercohomologyEdge.sectionsEvaluationIso_restrict_natTrans` and
  `Stacks.Cohomology.HypercohomologyEdge.sectionsEvaluationIso_restrict`: the transformation form
  and the object-wise form of the evaluation restriction square, unconditionally.

## Implementation notes

*Every step is its own lemma with the categories, functors, objects and morphisms variables, and
is applied by `exact`*, as in the file this one extends.  Here that is forced rather than
preferred: the two paths of each square are written at two spellings of one functor — the
degreewise action of a composite against the composite of the degreewise actions, the degreewise
action against the action on the derived category, `(F ⋙ G).obj X` against `G.obj (F.obj X)` —
so the composites are type-correct only at `default` transparency, and on such a goal no rewrite
runs at all: `rw` re-checks at `implicit` transparency and reports *no occurrence* of a pattern
the goal visibly contains, and `dsimp only` with the definitional lemmas does not help, since
normalizing the ambient types only moves the mismatch to the terms' own.  So the chases
`derived_vs_homotopy_chase` and `source_chase` carry every object and morphism as a variable and
take the pieces as hypotheses, each crossing being one `isDefEq` at the `exact` that applies
them.

## References

* [Stacks Project, Tag 0A94](https://stacks.math.columbia.edu/tag/0A94)
* [Stacks Project, Tag 0D68](https://stacks.math.columbia.edu/tag/0D68)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [local instance] CategoryTheory.Limits.comp_preservesFiniteLimits
  CategoryTheory.Limits.comp_preservesFiniteColimits

namespace Stacks.Cohomology.HypercohomologyEdge

/-! ### Two diagram lemmas, stated with every object and morphism a variable -/

/-- The component of the inverse of a natural isomorphism is pinned by one equation.  Stated
with the categories, functors and object variables so that it is applied by `exact`. -/
theorem natIso_inv_app_eq {X Y : Type*} [Category* X] [Category* Y] {F G : X ⥤ Y}
    (e : F ≅ G) (a : X) (u : G.obj a ⟶ F.obj a)
    (h : e.hom.app a ≫ u = 𝟙 (F.obj a)) : e.inv.app a = u := by
  calc e.inv.app a = e.inv.app a ≫ e.hom.app a ≫ u := by rw [h, Category.comp_id]
    _ = u := by rw [← Category.assoc, Iso.inv_hom_id_app, Category.id_comp]

/-- **A square from a naturality square and a factorization.**  The left-hand path `σ` splits as
`s₁ ≫ s₂ ≫ s₃`; the first leg fits into a naturality square with `β`, and `β` followed by the
remaining legs and `w` is the right-hand path. -/
theorem square_from_two {X : Type*} [Category* X] {x₁ x₂ x₃ x₄ x₅ x₆ y : X}
    {α : x₁ ⟶ x₂} {s₁ : x₂ ⟶ x₃} {s₂ : x₃ ⟶ x₄} {s₃ : x₄ ⟶ x₅} {w : x₅ ⟶ x₆}
    {δ : x₁ ⟶ y} {β : y ⟶ x₃} {γ : y ⟶ x₆} {σ : x₂ ⟶ x₅}
    (hσ : σ = s₁ ≫ s₂ ≫ s₃) (h₁ : δ ≫ β = α ≫ s₁)
    (h₂ : β ≫ s₂ ≫ s₃ ≫ w = γ) : α ≫ σ ≫ w = δ ≫ γ := by
  subst hσ h₂
  simp [reassoc_of% h₁]

/-- Three composable transformations whisker one at a time. -/
theorem whiskerRight_comp3 {X Y Z : Type*} [Category* X] [Category* Y] [Category* Z]
    {F₁ F₂ F₃ F₄ : X ⥤ Y} (a : F₁ ⟶ F₂) (b : F₂ ⟶ F₃) (c : F₃ ⟶ F₄) (H : Y ⥤ Z) :
    Functor.whiskerRight (a ≫ b ≫ c) H =
      Functor.whiskerRight a H ≫ Functor.whiskerRight b H ≫ Functor.whiskerRight c H := by
  simp

/-- Two nested cancellations.  Stated with variables because the two sides are written at two
spellings of one object. -/
theorem comp_comp_inv_id {X : Type*} [Category* X] {x₁ x₂ x₃ : X}
    (u : x₁ ⟶ x₂) (u' : x₂ ⟶ x₁) (v : x₂ ⟶ x₃) (v' : x₃ ⟶ x₂)
    (hv : v ≫ v' = 𝟙 x₂) (hu : u ≫ u' = 𝟙 x₁) :
    (u ≫ v) ≫ v' ≫ u' = 𝟙 x₁ := by
  rw [Category.assoc, ← Category.assoc v v' u', hv, Category.id_comp, hu]

/-- A cancelling pair inside the image of a functor changes nothing.  Stated with the two
categories, the functor and every object and morphism variable. -/
theorem comp_cancel_functor {X Y : Type*} [Category* X] [Category* Y] (R : X ⥤ Y)
    {a₁ a₂ a₃ a₄ : X} {b₁ b₂ : Y}
    (m : a₁ ⟶ a₂) (p : a₂ ⟶ a₃) (z : a₃ ⟶ a₄) (w : a₄ ⟶ a₃)
    (r : R.obj a₃ ⟶ b₁) (s : b₁ ⟶ b₂) (h : z ≫ w = 𝟙 a₃) :
    R.map m ≫ (R.map p ≫ r) ≫ s = R.map (m ≫ p ≫ z) ≫ R.map w ≫ r ≫ s := by
  rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp]
  simp only [Category.assoc]
  rw [← Category.assoc (R.map z) (R.map w), ← CategoryTheory.Functor.map_comp, h,
    CategoryTheory.Functor.map_id, Category.id_comp]

/-- **The chase behind the composition law for the comparison of the sources.**  Two paths of
four legs each, three of whose legs are identities and the rest of which are related by `hν`
(the composition law one level down) and `hρ` (the agreement of the two homology comparisons).
Stated with every category, functor, object and morphism a variable. -/
theorem source_chase {X Y : Type*} [Category* X] [Category* Y] (R : X ⥤ Y)
    {a₁ a₂ a₃ a₄ : X} {c₁ c₂ c₃ : Y}
    {μ' : a₁ ⟶ a₂} {ν' : a₂ ⟶ a₃} {ι₂ : a₃ ⟶ a₃} {κ' : a₃ ⟶ a₄}
    {μ : R.obj a₁ ⟶ R.obj a₂} {ν : R.obj a₂ ⟶ c₁} {ι₁ : c₁ ⟶ c₁} {κ : c₁ ⟶ c₂}
    {lam₁ : c₂ ⟶ c₂} {lam₂ : c₂ ⟶ c₃} {lam₃ : c₃ ⟶ R.obj a₄} {ρ : R.obj a₃ ⟶ c₁}
    (hμ : μ = R.map μ') (hι₁ : ι₁ = 𝟙 c₁) (hι₂ : ι₂ = 𝟙 a₃) (hlam₁ : lam₁ = 𝟙 c₂)
    (hν : ν = R.map ν' ≫ ρ) (hρ : ρ ≫ κ ≫ lam₂ ≫ lam₃ = R.map κ') :
    (μ ≫ ν ≫ ι₁ ≫ κ) ≫ lam₁ ≫ lam₂ ≫ lam₃ = R.map (μ' ≫ ν' ≫ ι₂ ≫ κ') := by
  subst hμ hι₁ hι₂ hlam₁ hν
  simp only [Category.id_comp, Category.assoc, CategoryTheory.Functor.map_comp]
  rw [hρ]

/-- A functor on a three-fold composite. -/
theorem map_comp3 {X Y : Type*} [Category* X] [Category* Y] (T : X ⥤ Y) {a b c d : X}
    (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) :
    T.map (f ≫ g ≫ h) = T.map f ≫ T.map g ≫ T.map h := by simp

/-- A functor on a four-fold composite. -/
theorem map_comp4 {X Y : Type*} [Category* X] [Category* Y] (T : X ⥤ Y) {a b c d e : X}
    (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) (k : d ⟶ e) :
    T.map (f ≫ g ≫ h ≫ k) = T.map f ≫ T.map g ≫ T.map h ≫ T.map k := by simp

/-- A functor carries a morphism that is an identity to an identity. -/
theorem map_eq_id {X Y : Type*} [Category* X] [Category* Y] (T : X ⥤ Y) {a : X} (u : a ⟶ a)
    (h : u = 𝟙 a) : T.map u = 𝟙 (T.obj a) := by
  simp [h]

/-- Two functors carry a morphism that is an identity to an identity. -/
theorem map_map_eq_id {X Y Z : Type*} [Category* X] [Category* Y] [Category* Z]
    (S : X ⥤ Y) (T : Y ⥤ Z) {a : X} (u : a ⟶ a) (h : u = 𝟙 a) :
    T.map (S.map u) = 𝟙 (T.obj (S.obj a)) :=
  map_eq_id T _ (map_eq_id S u h)

/-- A functor carries a cancelling pair to a cancelling pair. -/
theorem map_comp_eq_id {X Y : Type*} [Category* X] [Category* Y] (T : X ⥤ Y) {a b : X}
    (u : a ⟶ b) (v : b ⟶ a) (h : u ≫ v = 𝟙 a) : T.map u ≫ T.map v = 𝟙 (T.obj a) := by
  rw [← CategoryTheory.Functor.map_comp, h, CategoryTheory.Functor.map_id]

/-- Two functors carry a cancelling pair to a cancelling pair. -/
theorem map_map_comp_eq_id {X Y Z : Type*} [Category* X] [Category* Y] [Category* Z]
    (S : X ⥤ Y) (T : Y ⥤ Z) {a b : X} (u : a ⟶ b) (v : b ⟶ a) (h : u ≫ v = 𝟙 a) :
    T.map (S.map u) ≫ T.map (S.map v) = 𝟙 (T.obj (S.obj a)) :=
  map_comp_eq_id T _ _ (map_comp_eq_id S u v h)

/-- **The chase behind the agreement of the two homology comparisons of an exact functor.**  The
four legs `A`, `B`, `C`, `D` each split through the category of complexes, `Ev` splits the same
way, and the pieces cancel in pairs; `f` is the comparison of the two images of the complex in
the derived category, invertible with inverse `f'`.

Stated with every object and morphism a variable: the two paths are written at two spellings of
one functor — the degreewise action of the functor against its action on the derived category —
so the composites are type-correct only at `default` transparency, and no rewrite can be run on
them. -/
theorem derived_vs_homotopy_chase {X : Type*} [Category* X]
    {x₀ x₁ x₂ x₃ x₄ x₅ u₁ u₂ u₃ u₄ : X}
    {A : x₀ ⟶ x₁} {B : x₁ ⟶ x₂} {C : x₂ ⟶ x₃} {D : x₃ ⟶ x₄} {Ev : x₀ ⟶ x₄}
    {f : x₄ ⟶ x₅} {f' : x₅ ⟶ x₄}
    {a₁ : x₀ ⟶ u₁} {a₂ : u₁ ⟶ u₂} {a₃ : u₂ ⟶ x₁}
    {b₁ : x₁ ⟶ u₂} {b₂ : u₂ ⟶ u₃} {b₃ : u₃ ⟶ x₂}
    {c₁ : x₂ ⟶ x₂} {c₂ : x₂ ⟶ u₃} {c₃ : u₃ ⟶ u₄} {c₄ : u₄ ⟶ x₃}
    {Θ : x₃ ⟶ u₄} {d₁ : u₄ ⟶ u₃} {d₂ : u₃ ⟶ u₂} {d₃ : u₂ ⟶ u₁} {d₄ : u₁ ⟶ x₅}
    (hA : A = a₁ ≫ a₂ ≫ a₃) (hB : B = b₁ ≫ b₂ ≫ b₃)
    (hC : C = c₁ ≫ c₂ ≫ c₃ ≫ c₄) (hDf : D ≫ f = Θ ≫ d₁ ≫ d₂ ≫ d₃ ≫ d₄)
    (hEv : Ev = a₁ ≫ d₄ ≫ f') (hc₁ : c₁ = 𝟙 x₂)
    (h₁ : a₃ ≫ b₁ = 𝟙 u₂) (h₂ : b₃ ≫ c₂ = 𝟙 u₃) (h₃ : c₄ ≫ Θ = 𝟙 u₄)
    (h₄ : c₃ ≫ d₁ = 𝟙 u₃) (h₅ : b₂ ≫ d₂ = 𝟙 u₂) (h₆ : a₂ ≫ d₃ = 𝟙 u₁)
    (h₇ : f ≫ f' = 𝟙 x₄) (h₈ : f' ≫ f = 𝟙 x₅) :
    A ≫ B ≫ C ≫ D = Ev := by
  have key : (A ≫ B ≫ C ≫ D) ≫ f = a₁ ≫ d₄ := by
    rw [hA, hB, hC]
    simp only [Category.assoc, hc₁, Category.id_comp]
    rw [hDf, ← Category.assoc a₃ b₁, h₁, Category.id_comp,
      ← Category.assoc b₃ c₂, h₂, Category.id_comp,
      ← Category.assoc c₄ Θ, h₃, Category.id_comp,
      ← Category.assoc c₃ d₁, h₄, Category.id_comp,
      ← Category.assoc b₂ d₂, h₅, Category.id_comp,
      ← Category.assoc a₂ d₃, h₆, Category.id_comp]
  have key2 : Ev ≫ f = a₁ ≫ d₄ := by
    rw [hEv]
    simp only [Category.assoc]
    rw [h₈, Category.comp_id]
  calc A ≫ B ≫ C ≫ D = ((A ≫ B ≫ C ≫ D) ≫ f) ≫ f' := by
        rw [Category.assoc, h₇, Category.comp_id]
    _ = (Ev ≫ f) ≫ f' := by rw [key, key2]
    _ = Ev := by rw [Category.assoc, h₇, Category.comp_id]

/-! ### The homology comparisons of an exact functor, on a complex -/

section Abstract

variable {A P G M : Type*} [Category* A] [Category* P] [Category* G] [Category* M]
  [Abelian A] [Abelian P] [Abelian G] [Abelian M]

/-- The comparison between the degreewise action on complexes and the degreewise action on the
homotopy category is the identity on a complex. -/
theorem mapHomotopyCategoryFactors_hom_app (R : G ⥤ M) [R.Additive] (L : CochainComplex G ℤ) :
    (R.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).hom.app L = 𝟙 _ := rfl

/-- The comparison of the degreewise action of a composite with the composite of the degreewise
actions is the identity on a complex, in the inverse direction too. -/
theorem compIso_refl_inv_app_quotient (F : A ⥤ P) [F.Additive] (T : P ⥤ G) [T.Additive]
    (K : CochainComplex A ℤ) :
    (Functor.mapHomotopyCategoryCompIso (Iso.refl (F ⋙ T)) (ComplexShape.up ℤ)).inv.app
        ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K) = 𝟙 _ := by
  refine natIso_inv_app_eq _ _ _ ?_
  rw [Stacks.Homology.mapHomotopyCategoryCompIso_refl_app_quotient]
  exact Category.comp_id _

variable (R : G ⥤ M) [R.Additive] [PreservesFiniteLimits R] [PreservesFiniteColimits R]

/-- **The component of `Stacks.Homology.derivedHomologyIso` on the image of the localization.**
It is the comparison on complexes, conjugated by the factorizations of the degreewise action of
the functor and of the homology functors through the category of complexes. -/
theorem derivedHomologyIso_hom_app_Q [HasDerivedCategory G] [HasDerivedCategory M] (q : ℤ)
    (L : CochainComplex G ℤ) :
    (Stacks.Homology.derivedHomologyIso R q).hom.app (DerivedCategory.Q.obj L) =
      (DerivedCategory.homologyFunctor M q).map (R.mapDerivedCategoryFactors.hom.app L) ≫
        (DerivedCategory.homologyFunctorFactors M q).hom.app
          ((R.mapHomologicalComplex (ComplexShape.up ℤ)).obj L) ≫
        (Stacks.Homology.exactHomologyIso R q).hom.app L ≫
        R.map ((DerivedCategory.homologyFunctorFactors G q).inv.app L) := by
  simp [Stacks.Homology.derivedHomologyIso, Localization.liftNatTrans_app]

/-- The inverse of the comparison between the two factorizations of the degreewise action of an
exact functor, on the image of the quotient. -/
theorem mapDerivedCategoryFactorsh_inv_app_quotient [HasDerivedCategory G]
    [HasDerivedCategory M] (L : CochainComplex G ℤ) :
    R.mapDerivedCategoryFactorsh.inv.app
        ((HomotopyCategory.quotient G (ComplexShape.up ℤ)).obj L) =
      DerivedCategory.Qh.map
          ((R.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).hom.app L) ≫
        (DerivedCategory.quotientCompQhIso M).hom.app
          ((R.mapHomologicalComplex (ComplexShape.up ℤ)).obj L) ≫
        R.mapDerivedCategoryFactors.inv.app L ≫
        R.mapDerivedCategory.map ((DerivedCategory.quotientCompQhIso G).inv.app L) := by
  refine natIso_inv_app_eq _ _ _ ?_
  rw [Functor.mapDerivedCategoryFactorsh_hom_app]
  simp [← Functor.map_comp]

variable (E : P ⥤ G) [E.Additive] [PreservesFiniteLimits E] [PreservesFiniteColimits E]

/-- **The homology comparison on complexes is compatible with composition**, in the inverse
direction. -/
theorem exactHomologyIso_comp_inv_app (q : ℤ) (L : CochainComplex P ℤ) :
    (Stacks.Homology.exactHomologyIso (E ⋙ R) q).inv.app L =
      R.map ((Stacks.Homology.exactHomologyIso E q).inv.app L) ≫
        (Stacks.Homology.exactHomologyIso R q).inv.app
          ((E.mapHomologicalComplex (ComplexShape.up ℤ)).obj L) := by
  refine natIso_inv_app_eq _ _ _ ?_
  rw [← Stacks.Homology.exactHomologyIso_comp_hom_app E R q L]
  exact comp_comp_inv_id _ _ _ _
    (by rw [← Functor.map_comp, Iso.hom_inv_id_app]; exact CategoryTheory.Functor.map_id R _)
    (Iso.hom_inv_id_app _ _)

/-- **The homology comparison on the homotopy category is compatible with composition**, on the
image of the quotient. -/
theorem homotopyHomologyIso_comp_hom_app_quotient (q : ℤ) (L : CochainComplex P ℤ) :
    (Stacks.Homology.homotopyHomologyIso (E ⋙ R) q).hom.app
        ((HomotopyCategory.quotient P (ComplexShape.up ℤ)).obj L) =
      R.map ((Stacks.Homology.homotopyHomologyIso E q).hom.app
          ((HomotopyCategory.quotient P (ComplexShape.up ℤ)).obj L)) ≫
        (Stacks.Homology.homotopyHomologyIso R q).hom.app
          ((HomotopyCategory.quotient G (ComplexShape.up ℤ)).obj
            ((E.mapHomologicalComplex (ComplexShape.up ℤ)).obj L)) := by
  rw [Stacks.Homology.homotopyHomologyIso_hom_app_quotient,
    Stacks.Homology.homotopyHomologyIso_hom_app_quotient,
    Stacks.Homology.homotopyHomologyIso_hom_app_quotient,
    Stacks.Homology.quotHomologyIso_hom_app, Stacks.Homology.quotHomologyIso_hom_app,
    Stacks.Homology.quotHomologyIso_hom_app, exactHomologyIso_comp_inv_app]
  exact comp_cancel_functor R _ _ _ _ _ _ (Iso.inv_hom_id_app _ _)

/-- **The homotopy-category and derived-category homology comparisons of an exact functor
agree.**  Read through the factorizations of homology and of the degreewise action through the
homotopy category, `Stacks.Homology.derivedHomologyIso` is
`Stacks.Homology.homotopyHomologyIso`.  This is the step at which the derived category leaves
the square. -/
theorem derivedHomologyIso_homotopyHomologyIso [HasDerivedCategory G] [HasDerivedCategory M]
    (q : ℤ) (L : CochainComplex G ℤ) :
    (Stacks.Homology.homotopyHomologyIso R q).hom.app
          ((HomotopyCategory.quotient G (ComplexShape.up ℤ)).obj L) ≫
        (DerivedCategory.homologyFunctorFactorsh M q).inv.app
          ((HomotopyCategory.quotient M (ComplexShape.up ℤ)).obj
            ((R.mapHomologicalComplex (ComplexShape.up ℤ)).obj L)) ≫
        (DerivedCategory.homologyFunctor M q).map
          (R.mapDerivedCategoryFactorsh.inv.app
            ((HomotopyCategory.quotient G (ComplexShape.up ℤ)).obj L)) ≫
        (Stacks.Homology.derivedHomologyIso R q).hom.app
          (DerivedCategory.Qh.obj
            ((HomotopyCategory.quotient G (ComplexShape.up ℤ)).obj L)) =
      R.map ((DerivedCategory.homologyFunctorFactorsh G q).inv.app
        ((HomotopyCategory.quotient G (ComplexShape.up ℤ)).obj L)) := by
  exact derived_vs_homotopy_chase
    ((Stacks.Homology.homotopyHomologyIso_hom_app_quotient R q L).trans
      (Stacks.Homology.quotHomologyIso_hom_app R q L))
    (DerivedCategory.homologyFunctorFactorsh_inv_app_quotient_obj M
      ((R.mapHomologicalComplex (ComplexShape.up ℤ)).obj L) q)
    ((congrArg (DerivedCategory.homologyFunctor M q).map
        (mapDerivedCategoryFactorsh_inv_app_quotient R L)).trans
      (map_comp4 (DerivedCategory.homologyFunctor M q) _ _ _ _))
    ((((Stacks.Homology.derivedHomologyIso R q).hom.naturality
          ((DerivedCategory.quotientCompQhIso G).hom.app L)).symm).trans
      (congrArg (fun t => (R.mapDerivedCategory ⋙
            DerivedCategory.homologyFunctor M q).map
          ((DerivedCategory.quotientCompQhIso G).hom.app L) ≫ t)
        (derivedHomologyIso_hom_app_Q R q L)))
    ((congrArg R.map
        (DerivedCategory.homologyFunctorFactorsh_inv_app_quotient_obj G L q)).trans
      (map_comp3 R _ _ _))
    (map_map_eq_id DerivedCategory.Qh (DerivedCategory.homologyFunctor M q) _
      (mapHomotopyCategoryFactors_hom_app R L))
    (Iso.inv_hom_id_app _ _)
    (map_comp_eq_id (DerivedCategory.homologyFunctor M q) _ _ (Iso.inv_hom_id_app _ _))
    (map_map_comp_eq_id R.mapDerivedCategory (DerivedCategory.homologyFunctor M q) _ _
      (Iso.inv_hom_id_app _ _))
    (map_comp_eq_id (DerivedCategory.homologyFunctor M q) _ _ (Iso.inv_hom_id_app _ _))
    (Iso.inv_hom_id_app _ _) (Iso.inv_hom_id_app _ _)
    (map_map_comp_eq_id (DerivedCategory.homologyFunctor G q) R _ _ (Iso.hom_inv_id_app _ _))
    (map_map_comp_eq_id (DerivedCategory.homologyFunctor G q) R _ _ (Iso.inv_hom_id_app _ _))

end Abstract

/-! ### The composition law for the comparison of the sources -/

section Source

variable {A P G M : Type*} [Category* A] [Category* P] [Category* G] [Category* M]
  [Abelian A] [Abelian P] [Abelian G] [Abelian M]
  [HasDerivedCategory P] [HasDerivedCategory G] [HasDerivedCategory M]
  (F : A ⥤ P) [F.Additive] (E : P ⥤ G) [E.Additive]
  [PreservesFiniteLimits E] [PreservesFiniteColimits E]
  (R : G ⥤ M) [R.Additive] [PreservesFiniteLimits R] [PreservesFiniteColimits R]

/-- **The composition law for `Stacks.Homology.derivedSourceIso`, on a complex.** -/
theorem derivedSourceIso_comp_app (q : ℤ) (K : CochainComplex A ℤ) :
    (Stacks.Homology.derivedSourceIso F (E ⋙ R) q).hom.app
          ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K) ≫
        (DerivedCategory.homologyFunctor M q).map (DerivedCategory.Qh.map
          ((Functor.mapHomotopyCategoryCompIso (Iso.refl ((F ⋙ E) ⋙ R))
            (ComplexShape.up ℤ)).inv.app
              ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K))) ≫
        (DerivedCategory.homologyFunctor M q).map
          (R.mapDerivedCategoryFactorsh.inv.app
            (((F ⋙ E).mapHomotopyCategory (ComplexShape.up ℤ)).obj
              ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K))) ≫
        (Stacks.Homology.derivedHomologyIso R q).hom.app
          (DerivedCategory.Qh.obj
            (((F ⋙ E).mapHomotopyCategory (ComplexShape.up ℤ)).obj
              ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K))) =
      R.map ((Stacks.Homology.derivedSourceIso F E q).hom.app
        ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K)) := by
  rw [Stacks.Homology.derivedSourceIso_hom_app, Stacks.Homology.derivedSourceIso_hom_app]
  exact source_chase R rfl
    (map_eq_id (HomotopyCategory.homologyFunctor M (ComplexShape.up ℤ) q) _
      (Stacks.Homology.mapHomotopyCategoryCompIso_refl_app_quotient F (E ⋙ R) K))
    (map_eq_id (HomotopyCategory.homologyFunctor G (ComplexShape.up ℤ) q) _
      (Stacks.Homology.mapHomotopyCategoryCompIso_refl_app_quotient F E K))
    (map_map_eq_id DerivedCategory.Qh (DerivedCategory.homologyFunctor M q) _
      (compIso_refl_inv_app_quotient (F ⋙ E) R K))
    (homotopyHomologyIso_comp_hom_app_quotient R E q
      ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K))
    (derivedHomologyIso_homotopyHomologyIso R q
      ((E.mapHomologicalComplex (ComplexShape.up ℤ)).obj
        ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K)))

/-- **The composition law for `Stacks.Homology.derivedSourceIso`.**  The comparison of the
sources for `E ⋙ R` is the comparison for `E` read through `R`, once the degreewise action of
`R` has been identified with its action on the derived category and homology commuted past
it. -/
theorem derivedSourceIso_comp (q : ℤ) :
    (Stacks.Homology.derivedSourceIso F (E ⋙ R) q).hom ≫
        Functor.whiskerRight (Functor.whiskerRight
            (Functor.mapHomotopyCategoryCompIso (Iso.refl ((F ⋙ E) ⋙ R))
              (ComplexShape.up ℤ)).inv DerivedCategory.Qh)
          (DerivedCategory.homologyFunctor M q) ≫
        Functor.whiskerRight (Functor.whiskerLeft
            ((F ⋙ E).mapHomotopyCategory (ComplexShape.up ℤ))
            R.mapDerivedCategoryFactorsh.inv) (DerivedCategory.homologyFunctor M q) ≫
        Functor.whiskerLeft
          ((F ⋙ E).mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)
          (Stacks.Homology.derivedHomologyIso R q).hom =
      Functor.whiskerRight (Stacks.Homology.derivedSourceIso F E q).hom R := by
  refine NatTrans.ext (funext fun I => ?_)
  obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective I
  exact derivedSourceIso_comp_app F E R q K

end Source

/-! ### The square -/

universe u v wRing wModule g

attribute [local instance] HasDerivedCategory.standard

open Stacks.Cohomology.SiteCohomologyPresheaf

attribute [local instance] restrictScalars_preservesFiniteLimits
  restrictScalars_preservesFiniteColimits evaluation_additive

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (O : Sheaf J RingCat.{wRing}) [HasSheafify J AddCommGrpCat.{wModule}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{wModule}]
  [IsGrothendieckAbelian.{g} (SheafOfModules.{wModule} O)]

omit [IsGrothendieckAbelian.{g} (SheafOfModules.{wModule} O)] in
/-- **The underived evaluation comparison is the general comparison of sources.**
`Stacks.Cohomology.HypercohomologyEdge.homotopySectionsEvaluationIso` and
`Stacks.Homology.derivedSourceIso` of the forgetful functor against evaluation at the object are
the same morphism: the chains they are assembled from differ only by associators, whose
components are identities. -/
theorem homotopySectionsEvaluationIso_hom_eq (U : C) (q : ℤ) :
    (homotopySectionsEvaluationIso O U q).hom =
      (Stacks.Homology.derivedSourceIso (SheafOfModules.forget O)
        (PresheafOfModules.evaluation O.obj (.op U)) q).hom := rfl

omit [IsGrothendieckAbelian.{g} (SheafOfModules.{wModule} O)] in
/-- **The evaluation restriction square on the homotopy category.**  This is the hypothesis left
open by
`Stacks.Cohomology.HypercohomologyEdge.sectionsEvaluationIso_restrict_natTrans_of_homotopySquare`.

It is naturality of the comparison of sources in the exact functor it is taken against —
`CategoryTheory.PresheafOfModules.restriction`, from evaluation at `U` to evaluation at `U'`
read through restriction of scalars — followed by the composition law for that comparison. -/
theorem sectionsEvaluationIso_restrict_homotopySquare {U U' : C} (g : U' ⟶ U) (q : ℤ) :
    (homotopySectionsEvaluationIso O U q).hom ≫
        Functor.whiskerRight (homotopySectionsRestrict O g)
            (DerivedCategory.homologyFunctor (ModuleCat.{wModule} (O.obj.obj (.op U))) q) ≫
          Functor.whiskerLeft (homotopySections O U')
            (Stacks.Homology.derivedHomologyIso
              (ModuleCat.restrictScalars (O.obj.map g.op).hom) q).hom =
      Functor.whiskerLeft (homotopySectionsPresheaf O ⋙
            DerivedCategory.homologyFunctor (PresheafOfModules.{wModule} O.obj) q)
          (PresheafOfModules.restriction O.obj g.op) ≫
        Functor.whiskerRight (homotopySectionsEvaluationIso O U' q).hom
          (ModuleCat.restrictScalars (O.obj.map g.op).hom) := by
  have hσ : Functor.whiskerRight (homotopySectionsRestrict O g)
        (DerivedCategory.homologyFunctor (ModuleCat.{wModule} (O.obj.obj (.op U))) q) =
      Functor.whiskerRight (Functor.whiskerRight (NatTrans.mapHomotopyCategory
            (sectionsRestrict O g) (ComplexShape.up ℤ)) DerivedCategory.Qh)
          (DerivedCategory.homologyFunctor (ModuleCat.{wModule} (O.obj.obj (.op U))) q) ≫
        Functor.whiskerRight (Functor.whiskerRight (Functor.mapHomotopyCategoryCompIso
              (Iso.refl (SheafOfModules.evaluation O (.op U') ⋙
                ModuleCat.restrictScalars (O.obj.map g.op).hom))
              (ComplexShape.up ℤ)).inv DerivedCategory.Qh)
            (DerivedCategory.homologyFunctor (ModuleCat.{wModule} (O.obj.obj (.op U))) q) ≫
          Functor.whiskerRight (Functor.whiskerLeft
              ((SheafOfModules.evaluation O (.op U')).mapHomotopyCategory (ComplexShape.up ℤ))
              (ModuleCat.restrictScalars (O.obj.map g.op).hom).mapDerivedCategoryFactorsh.inv)
            (DerivedCategory.homologyFunctor (ModuleCat.{wModule} (O.obj.obj (.op U))) q) :=
    whiskerRight_comp3 _ _ _ _
  exact square_from_two hσ
    (Stacks.Homology.derivedSourceIso_hom_naturality (SheafOfModules.forget O) q
      (PresheafOfModules.restriction O.obj g.op))
    (derivedSourceIso_comp (SheafOfModules.forget O)
      (PresheafOfModules.evaluation O.obj (.op U'))
      (ModuleCat.restrictScalars (O.obj.map g.op).hom) q)

/-- **The transformation form of the evaluation restriction square**, unconditionally. -/
theorem sectionsEvaluationIso_restrict_natTrans {U U' : C} (g : U' ⟶ U) (q : ℤ) :
    (sectionsEvaluationIso O U q).hom ≫ derivedSectionsRestrictHomology O g q =
      Functor.whiskerLeft (derivedSectionsPresheaf O ⋙
          DerivedCategory.homologyFunctor (PresheafOfModules.{wModule} O.obj) q)
        (PresheafOfModules.restriction O.obj g.op) ≫
        Functor.whiskerRight (sectionsEvaluationIso O U' q).hom
          (ModuleCat.restrictScalars (O.obj.map g.op).hom) :=
  sectionsEvaluationIso_restrict_natTrans_of_homotopySquare O g q
    (sectionsEvaluationIso_restrict_homotopySquare O g q)

/-- **The object-wise evaluation restriction square**, unconditionally.  This is the shape in
which the restriction compatibility of
`Stacks.Cohomology.UnboundedHigherDirectImage.preimageCohomologyEvaluationIso` consumes this
half of the square. -/
theorem sectionsEvaluationIso_restrict {U U' : C} (g : U' ⟶ U) (q : ℤ)
    (K : DerivedCategory (SheafOfModules.{wModule} O)) :
    (sectionsEvaluationIso O U q).hom.app K ≫ (derivedSectionsRestrictHomology O g q).app K =
      (PresheafOfModules.restriction O.obj g.op).app
          ((DerivedCategory.homologyFunctor (PresheafOfModules.{wModule} O.obj) q).obj
            ((derivedSectionsPresheaf O).obj K)) ≫
        (ModuleCat.restrictScalars (O.obj.map g.op).hom).map
          ((sectionsEvaluationIso O U' q).hom.app K) :=
  sectionsEvaluationIso_restrict_of_homotopySquare O g q
    (sectionsEvaluationIso_restrict_homotopySquare O g q) K

/-- **The edge morphism commutes with restriction.** For `g : U' ⟶ U`, the degree-`q` derived
restriction `H^q(U, K) ⟶ H^q(U', K)` followed by the edge morphism over `U'` is the edge
morphism over `U` followed by the restriction `Γ(U, H^q K) ⟶ Γ(U', H^q K)` of the cohomology
sheaf. -/
theorem derivedSectionsRestrictHomology_app_comp_hypercohomologyEdge {U U' : C} (g : U' ⟶ U)
    (q : ℤ) (K : DerivedCategory (SheafOfModules.{wModule} O)) :
    (derivedSectionsRestrictHomology O g q).app K ≫
        (ModuleCat.restrictScalars (O.obj.map g.op).hom).map ((hypercohomologyEdge O U' q).app K) =
      (hypercohomologyEdge O U q).app K ≫
        (sectionsRestrict O g).app
          ((DerivedCategory.homologyFunctor (SheafOfModules.{wModule} O) q).obj K) := by
  rw [hypercohomologyEdge_app, hypercohomologyEdge_app, cohomologyPresheafUnit_app,
    cohomologyPresheafUnit_app]
  have h1' : (derivedSectionsRestrictHomology O g q).app K ≫
      (ModuleCat.restrictScalars (O.obj.map g.op).hom).map
        ((sectionsEvaluationIso O U' q).inv.app K) =
      (sectionsEvaluationIso O U q).inv.app K ≫
        (PresheafOfModules.restriction O.obj g.op).app
          ((DerivedCategory.homologyFunctor (PresheafOfModules.{wModule} O.obj) q).obj
            ((derivedSectionsPresheaf O).obj K)) := by
    rw [← cancel_epi ((sectionsEvaluationIso O U q).hom.app K),
      reassoc_of% (sectionsEvaluationIso_restrict O g q K), Iso.hom_inv_id_app_assoc,
      ← Functor.map_comp, Iso.hom_inv_id_app]
    exact Category.comp_id _
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% h1']
  congr 1
  exact ((PresheafOfModules.restriction O.obj g.op).naturality
    ((PresheafOfModules.sheafificationAdjunction (𝟙 O.obj)).unit.app
      ((DerivedCategory.homologyFunctor (PresheafOfModules.{wModule} O.obj) q).obj
        ((derivedSectionsPresheaf O).obj K)) ≫
      (SheafOfModules.forget O).map ((sheafificationCohomologyPresheafIso O q).hom.app K))).symm

end Stacks.Cohomology.HypercohomologyEdge

end
