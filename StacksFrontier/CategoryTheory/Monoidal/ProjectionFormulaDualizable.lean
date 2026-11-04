module

public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
public import StacksFrontier.CategoryTheory.Adjunction.ProjectionFormulaMap
public import StacksFrontier.CategoryTheory.Monoidal.Rigid

/-!
# The projection formula and the comparison with pullback at a dualizable object

Let `F : C ⥤ D` be a strong monoidal functor between monoidal categories, with a right adjoint
`G`. The *projection-formula map* is the adjoint transpose

  `π : K ⊗ G E ⟶ G (F K ⊗ E)`

of `δ_{K, G E} : F (K ⊗ G E) ⟶ F K ⊗ F G E` followed by `F K` tensored with the counit at `E`.
It is `CategoryTheory.adjunctionTensorMap` at the tensor products with their arguments
interchanged, which is the shape every projection formula of the library is written in.

If `G` has a further right adjoint `a`, and `π` is invertible, the *comparison map*

  `c : F K ⊗ a L ⟶ a (K ⊗ L)`

is the transpose of `π⁻¹` followed by `K` tensored with the counit of `G ⊣ a`. This is the
two-variable form of Equation 48.8.0.1 of [Stacks, Tag 0A9S], with `F = Lf^*`, `G = Rf_*`.

This file proves, in this abstract setting, the two facts about a *dualizable* `K` that the source
proves by Yoneda arguments:

* `isIso_projectionFormulaMap_of_exactPairing`: if `K` has a right dual then `π` is invertible
  at `K` and every `E`. This is the dualizable case of [Stacks, Tag 08EU] and [Stacks, Tag 0B54].
* `isIso_comparison_of_exactPairing`: if `K` has a right dual which itself has a right dual, then
  `c` is invertible at `K` and every `L`. This is [Stacks, Tag 0A9T].

## The method

Both are conjugations of isomorphisms between left adjoints
(`CategoryTheory.conjugateEquiv_iso`).

* `K ⊗ G(-)` is right adjoint to `F (K' ⊗ -)`, and `G (F K ⊗ -)` is right adjoint to
  `F K' ⊗ F(-)`, where `K'` is the dual of `K`. The tensorator `μ : F K' ⊗ F(-) ⟶ F (K' ⊗ -)`
  is an isomorphism, and its conjugate is `π` (`conjugateEquiv_mu_app`).
* `F K ⊗ a(-)` is right adjoint to `G (F K' ⊗ -)`, and `a (K ⊗ -)` is right adjoint to
  `K' ⊗ G(-)`. The projection-formula map at `K'` is an isomorphism between them by the first
  item, and its conjugate is `c` (`conjugateEquiv_projectionFormulaNatTrans_app`).

The identification of the conjugates is where the work is: for the first it is a computation with
the coherence of `F` and the zigzag identity (`coevaluation_tensorator`); for the second it is
that the map conjugation produces is a left inverse of `π` at `K`
(`projectionFormulaMap_comp_inverse`), which rests on the compatibility of `π` with the
associativity and unit of the tensor product (`whiskerLeft_projectionFormulaMap_comp`,
`projectionFormulaMap_unit`).

## Main definitions

All in the namespace `CategoryTheory.MonoidalProjectionFormula`.

* `tensorSwap` — the tensor product as a functor on pairs, with its arguments interchanged.
* `oplaxSwap` — the cotensorator of `F` read on `tensorSwap`.
* `projectionFormulaMap` — the map `π`.
* `comparison` — the map `c`.

## References

* [Stacks Project, Tag 0A9S](https://stacks.math.columbia.edu/tag/0A9S)
* [Stacks Project, Tag 0A9T](https://stacks.math.columbia.edu/tag/0A9T)
* [Stacks Project, Tag 08EU](https://stacks.math.columbia.edu/tag/08EU)
* [Stacks Project, Tag 0B54](https://stacks.math.columbia.edu/tag/0B54)
-/

@[expose] public noncomputable section

namespace CategoryTheory.MonoidalProjectionFormula

open MonoidalCategory Functor.LaxMonoidal Functor.OplaxMonoidal
open scoped CategoryTheory.Prod

universe v₁ v₂ u₁ u₂

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
  [MonoidalCategory C] [MonoidalCategory D]

/-! ### The interchanged tensor product and the cotensorator -/

variable (C) in
/-- The tensor product of `C` as a functor on `C × C`, with its arguments interchanged:
`(X, Y) ↦ Y ⊗ X`. -/
abbrev tensorSwap : C × C ⥤ C :=
  Prod.swap C C ⋙ Functor.uncurry.obj (curriedTensor C)

variable (F : C ⥤ D) [F.Monoidal]

/-- The cotensorator `δ : F (Y ⊗ X) ⟶ F Y ⊗ F X` of `F`, read as a morphism of functors on
`C × C` between the interchanged tensor products. -/
def oplaxSwap : tensorSwap C ⋙ F ⟶ F.prod F ⋙ tensorSwap D where
  app X := δ F X.2 X.1
  naturality X Y f := by
    obtain ⟨f₁, f₂⟩ := f
    dsimp
    rw [Functor.map_comp, Category.assoc, ← δ_natural_right, ← δ_natural_left_assoc,
      ← whisker_exchange]

/-- The component of `oplaxSwap F` at `(X₁, X₂)` is the cotensorator `δ F X₂ X₁`. -/
@[simp]
lemma oplaxSwap_app (X : C × C) : (oplaxSwap F).app X = δ F X.2 X.1 := rfl

/-! ### The projection-formula map -/

variable {F} {G : D ⥤ C} (adj : F ⊣ G)

/-- **The projection-formula map** `K ⊗ G E ⟶ G (F K ⊗ E)`: the adjoint transpose of the
cotensorator followed by `F K` tensored with the counit. It is
`CategoryTheory.adjunctionTensorMap` at the interchanged tensor products. -/
def projectionFormulaMap (E : D) (K : C) : K ⊗ G.obj E ⟶ G.obj (F.obj K ⊗ E) :=
  adjunctionTensorMap adj (tensorSwap C) (tensorSwap D) (oplaxSwap F) E K

omit [MonoidalCategory C] [MonoidalCategory D] [F.Monoidal] in
/-- Naturality of the counit, in the form used for rewriting. (Mathlib's
`CategoryTheory.Adjunction.counit_naturality` is stated with its implicit arguments in an order
that `rw` does not instantiate here.) -/
@[reassoc]
lemma counit_naturality' {X Y : D} (f : X ⟶ Y) :
    F.map (G.map f) ≫ adj.counit.app Y = adj.counit.app X ≫ f :=
  adj.counit.naturality f

omit [MonoidalCategory C] [MonoidalCategory D] [F.Monoidal] in
/-- Two morphisms into `G Y` agree as soon as their adjoint transposes do. -/
lemma ext_of_counit {X : C} {Y : D} {f g : X ⟶ G.obj Y}
    (h : F.map f ≫ adj.counit.app Y = F.map g ≫ adj.counit.app Y) : f = g := by
  apply (adj.homEquiv X Y).symm.injective
  simpa [Adjunction.homEquiv_counit] using h

/-- **The defining property of the projection-formula map**: its adjoint transpose is the
cotensorator followed by `F K` tensored with the counit. -/
@[reassoc]
lemma map_projectionFormulaMap_comp_counit (E : D) (K : C) :
    F.map (projectionFormulaMap adj E K) ≫ adj.counit.app (F.obj K ⊗ E) =
      δ F K (G.obj E) ≫ F.obj K ◁ adj.counit.app E := by
  have h := map_adjunctionTensorMap_comp_counit adj (tensorSwap C) (tensorSwap D)
    (oplaxSwap F) E K
  rw [projectionFormulaMap]
  simpa using h

/-- The projection-formula map is natural in the dualized variable. -/
@[reassoc]
lemma projectionFormulaMap_naturality_left (E : D) {K K' : C} (f : K ⟶ K') :
    f ▷ G.obj E ≫ projectionFormulaMap adj E K' =
      projectionFormulaMap adj E K ≫ G.map (F.map f ▷ E) := by
  apply ext_of_counit adj
  rw [Functor.map_comp, Functor.map_comp, Category.assoc, Category.assoc,
    map_projectionFormulaMap_comp_counit, counit_naturality' adj,
    map_projectionFormulaMap_comp_counit_assoc, ← δ_natural_left_assoc, whisker_exchange]

/-- The projection-formula map is natural in the pushed-forward variable. -/
@[reassoc]
lemma projectionFormulaMap_naturality_right {E E' : D} (g : E ⟶ E') (K : C) :
    K ◁ G.map g ≫ projectionFormulaMap adj E' K =
      projectionFormulaMap adj E K ≫ G.map (F.obj K ◁ g) := by
  apply ext_of_counit adj
  rw [Functor.map_comp, Functor.map_comp, Category.assoc, Category.assoc,
    map_projectionFormulaMap_comp_counit, counit_naturality' adj,
    map_projectionFormulaMap_comp_counit_assoc, ← δ_natural_right_assoc,
    ← MonoidalCategory.whiskerLeft_comp, ← MonoidalCategory.whiskerLeft_comp,
    counit_naturality' adj]

/-- **The projection-formula map is compatible with the associativity of the tensor product.**
Applying it at `K` and then at `K'` is applying it at `K' ⊗ K`, up to the associators and the
cotensorator of `F`. -/
lemma whiskerLeft_projectionFormulaMap_comp (E : D) (K K' : C) :
    K' ◁ projectionFormulaMap adj E K ≫ projectionFormulaMap adj (F.obj K ⊗ E) K' =
      (α_ K' K (G.obj E)).inv ≫ projectionFormulaMap adj E (K' ⊗ K) ≫
        G.map (δ F K' K ▷ E ≫ (α_ _ _ _).hom) := by
  apply ext_of_counit adj
  rw [Functor.map_comp, Category.assoc, map_projectionFormulaMap_comp_counit,
    ← δ_natural_right_assoc, ← MonoidalCategory.whiskerLeft_comp,
    map_projectionFormulaMap_comp_counit, Functor.map_comp, Functor.map_comp, Category.assoc,
    Category.assoc, counit_naturality' adj, map_projectionFormulaMap_comp_counit_assoc,
    MonoidalCategory.whiskerLeft_comp, δ_comp_whiskerLeft_δ_assoc, whisker_exchange_assoc,
    associator_naturality_right]

/-- **The projection-formula map at the unit object is the left unitor**, up to the counit `η` of
`F`. -/
lemma projectionFormulaMap_unit (E : D) :
    projectionFormulaMap adj E (𝟙_ C) ≫ G.map (η F ▷ E ≫ (λ_ E).hom) = (λ_ (G.obj E)).hom := by
  apply ext_of_counit adj
  rw [Functor.map_comp, Category.assoc, counit_naturality' adj,
    map_projectionFormulaMap_comp_counit_assoc, whisker_exchange_assoc]
  simp only [id_whiskerLeft, Category.assoc, left_unitality_hom_assoc,
    Iso.inv_hom_id, Category.comp_id]

/-! ### The dualizable case of the projection formula -/

/-- The zigzag identity of an exact pairing `K, K'`, tensored on the right with `M`. -/
lemma leftUnitor_inv_coevaluation_evaluation (K K' M : C) [ExactPairing K K'] :
    (λ_ (K ⊗ M)).inv ≫ η_ K K' ▷ (K ⊗ M) ≫ (α_ K K' (K ⊗ M)).hom ≫
      K ◁ ((α_ K' K M).inv ≫ ε_ K K' ▷ M ≫ (λ_ M).hom) = 𝟙 _ := by
  calc _ = 𝟙 _ ⊗≫ (η_ K K' ▷ K ⊗≫ K ◁ ε_ K K') ▷ M ⊗≫ 𝟙 _ := by monoidal
    _ = _ := by
      rw [ExactPairing.evaluation_coevaluation'']
      monoidal

variable (F) in
/-- **The coherence behind the dualizable projection formula.** For `K` with right dual `K'`
and any `M`, transporting the coevaluation of `K` along `F` and evaluating it back on
`K ⊗ M` recovers the cotensorator `δ_{K, M}`. This is the zigzag identity of the pairing, read
through the coherence of `F`. -/
@[reassoc]
lemma coevaluation_tensorator (K K' M : C) [ExactPairing K K'] :
    (λ_ (F.obj (K ⊗ M))).inv ≫ (ε F ≫ F.map (η_ K K') ≫ δ F K K') ▷ F.obj (K ⊗ M) ≫
      (α_ _ _ _).hom ≫ F.obj K ◁ (μ F K' (K ⊗ M) ≫
        F.map ((α_ K' K M).inv ≫ ε_ K K' ▷ M ≫ (λ_ M).hom)) = δ F K M := by
  have h₁ : (λ_ (F.obj (K ⊗ M))).inv ≫ ε F ▷ F.obj (K ⊗ M) =
      F.map (λ_ (K ⊗ M)).inv ≫ δ F (𝟙_ C) (K ⊗ M) := by
    rw [← left_unitality_inv F (K ⊗ M)]
    simp
  rw [comp_whiskerRight, comp_whiskerRight, MonoidalCategory.whiskerLeft_comp]
  simp only [Category.assoc]
  rw [reassoc_of% h₁, δ_natural_left_assoc, Functor.OplaxMonoidal.associativity_assoc,
    Functor.Monoidal.whiskerLeft_δ_μ_assoc, δ_natural_right]
  simp only [← Functor.map_comp_assoc]
  rw [leftUnitor_inv_coevaluation_evaluation K K' M, Functor.map_id, Category.id_comp]

variable (F) in
/-- The tensorator `μ : F K' ⊗ F(-) ⟶ F (K' ⊗ -)`, as a morphism of functors. -/
@[simps]
def muNatTrans (K' : C) : F ⋙ tensorLeft (F.obj K') ⟶ tensorLeft K' ⋙ F where
  app T := μ F K' T
  naturality _ _ f := μ_natural_right F K' f

/-- The transpose of the conjugate of `θ` for the adjunctions `(P ⊣ P') ∘ A` and `A ∘ (Q ⊣ Q')`
is the `tensorLeftHomEquiv`-transpose of `θ` at `P ⊗ R E`, evaluated and followed by the counit. -/
private lemma map_conjugateEquiv_comp_counit {X Y : Type*} [Category X] [Category Y]
    [MonoidalCategory X] [MonoidalCategory Y] {L : X ⥤ Y} {R : Y ⥤ X} (A : L ⊣ R)
    (P P' : X) (Q Q' : Y) [ExactPairing P P'] [ExactPairing Q Q']
    (θ : L ⋙ tensorLeft Q' ⟶ tensorLeft P' ⋙ L) (E : Y) :
    L.map ((conjugateEquiv ((tensorLeftAdjunction P P').comp A)
      (A.comp (tensorLeftAdjunction Q Q')) θ).app E) ≫ A.counit.app (Q ⊗ E) =
      tensorLeftHomEquiv _ Q Q' E (θ.app (P ⊗ R.obj E) ≫
        L.map ((α_ P' P (R.obj E)).inv ≫ ε_ P P' ▷ R.obj E ≫ (λ_ (R.obj E)).hom) ≫
          A.counit.app E) := by
  have h := conjugateEquiv_counit ((tensorLeftAdjunction P P').comp A)
    (A.comp (tensorLeftAdjunction Q Q')) θ E
  simp only [Functor.comp_map, Adjunction.comp_counit_app, tensorLeftAdjunction,
    Adjunction.mkOfHomEquiv_counit_app, tensorLeftHomEquiv, Equiv.coe_fn_symm_mk,
    MonoidalCategory.whiskerLeft_id, Category.id_comp, Functor.comp_obj] at h
  apply (tensorLeftHomEquiv _ Q Q' E).symm.injective
  simp only [Functor.comp_obj, curriedTensor_obj_obj, Equiv.symm_apply_apply]
  refine Eq.trans ?_ h
  simp only [tensorLeftHomEquiv, Equiv.coe_fn_symm_mk, MonoidalCategory.whiskerLeft_comp,
    Category.assoc]
  rfl

section Dualizable

variable (K K' : C) [ExactPairing K K']

/-- `K ⊗ G(-)` is right adjoint to `F (K' ⊗ -)`. -/
abbrev tensorPushAdjunction : tensorLeft K' ⋙ F ⊣ G ⋙ tensorLeft K :=
  (tensorLeftAdjunction K K').comp adj

/-- `G (F K ⊗ -)` is right adjoint to `F K' ⊗ F(-)`, for the image pairing of `F`. -/
abbrev pushTensorAdjunction :
    letI := ExactPairing.map F K K'
    F ⋙ tensorLeft (F.obj K') ⊣ tensorLeft (F.obj K) ⋙ G :=
  letI := ExactPairing.map F K K'
  adj.comp (tensorLeftAdjunction (F.obj K) (F.obj K'))

/-- **The projection-formula map at a dualizable object is the conjugate of the tensorator.** -/
lemma conjugateEquiv_muNatTrans_app (E : D) :
    (conjugateEquiv (tensorPushAdjunction adj K K') (pushTensorAdjunction adj K K')
      (muNatTrans F K')).app E = projectionFormulaMap adj E K := by
  let := ExactPairing.map F K K'
  apply ext_of_counit adj
  have hX := map_conjugateEquiv_comp_counit adj K K' (F.obj K) (F.obj K') (muNatTrans F K') E
  simp only [muNatTrans_app] at hX
  refine (hX.trans ?_).trans (map_projectionFormulaMap_comp_counit adj E K).symm
  simp only [tensorLeftHomEquiv, Equiv.coe_fn_mk, ExactPairing.map_coevaluation,
    MonoidalCategory.whiskerLeft_comp]
  rw [← coevaluation_tensorator_assoc F K K' (G.obj E)]
  simp only [MonoidalCategory.whiskerLeft_comp, Category.assoc]

end Dualizable

/-- The natural transformation `muNatTrans F K'`, whose components are the tensorators of `F`, is
an isomorphism. -/
instance (K' : C) : IsIso (muNatTrans F K') :=
  @NatIso.isIso_of_isIso_app _ _ _ _ _ _ (muNatTrans F K') fun X => by
    rw [muNatTrans_app]
    infer_instance

/-- **The projection formula at a dualizable object** ([Stacks, Tag 0B54] in this abstract form):
if `K` has a right dual, the projection-formula map `K ⊗ G E ⟶ G (F K ⊗ E)` is an isomorphism
for every `E`. -/
theorem isIso_projectionFormulaMap_of_exactPairing (K K' : C) [ExactPairing K K'] (E : D) :
    IsIso (projectionFormulaMap adj E K) := by
  rw [← conjugateEquiv_muNatTrans_app adj K K' E]
  infer_instance

/-! ### The comparison with pullback -/

/-- Applying the projection-formula map at `K` and then at its dual `K'`, and evaluating the image
pairing, is evaluating the pairing of `K, K'`. -/
lemma whiskerLeft_projectionFormulaMap_comp_evaluation (K K' : C) [ExactPairing K K'] (N : D) :
    letI := ExactPairing.map F K K'
    K' ◁ projectionFormulaMap adj N K ≫ projectionFormulaMap adj (F.obj K ⊗ N) K' ≫
      G.map ((α_ _ _ _).inv ≫ ε_ (F.obj K) (F.obj K') ▷ N ≫ (λ_ N).hom) =
        (α_ _ _ _).inv ≫ ε_ K K' ▷ G.obj N ≫ (λ_ (G.obj N)).hom := by
  let := ExactPairing.map F K K'
  rw [← Category.assoc, whiskerLeft_projectionFormulaMap_comp, Category.assoc, Category.assoc,
    ← G.map_comp, ExactPairing.map_evaluation]
  have h : (δ F K' K ▷ N ≫ (α_ (F.obj K') (F.obj K) N).hom) ≫ (α_ _ _ _).inv ≫
      (μ F K' K ≫ F.map (ε_ K K') ≫ η F) ▷ N ≫ (λ_ N).hom =
      F.map (ε_ K K') ▷ N ≫ η F ▷ N ≫ (λ_ N).hom := by
    simp only [Category.assoc, Iso.hom_inv_id_assoc, comp_whiskerRight,
      Functor.Monoidal.whiskerRight_δ_μ_assoc]
  rw [h, G.map_comp, ← Category.assoc (projectionFormulaMap adj N (K' ⊗ K)),
    ← projectionFormulaMap_naturality_left, Category.assoc, projectionFormulaMap_unit]

/-- **A left inverse of the projection-formula map at a dualizable object.** If `K` has right dual
`K'`, the map `G (F K ⊗ N) ⟶ K ⊗ G N` obtained from the projection-formula map at `K'` and the
evaluation of the image pairing is a left inverse of the projection-formula map at `K`. -/
lemma projectionFormulaMap_comp_inverse (K K' : C) [ExactPairing K K'] (N : D) :
    letI := ExactPairing.map F K K'
    projectionFormulaMap adj N K ≫ (λ_ _).inv ≫ η_ K K' ▷ _ ≫ (α_ _ _ _).hom ≫
      K ◁ (projectionFormulaMap adj (F.obj K ⊗ N) K' ≫
        G.map ((α_ _ _ _).inv ≫ ε_ (F.obj K) (F.obj K') ▷ N ≫ (λ_ N).hom)) = 𝟙 _ := by
  let := ExactPairing.map F K K'
  calc _ = (λ_ _).inv ≫ η_ K K' ▷ _ ≫ (α_ _ _ _).hom ≫ K ◁ (K' ◁ projectionFormulaMap adj N K ≫
        projectionFormulaMap adj (F.obj K ⊗ N) K' ≫
          G.map ((α_ _ _ _).inv ≫ ε_ (F.obj K) (F.obj K') ▷ N ≫ (λ_ N).hom)) := by
        rw [leftUnitor_inv_naturality_assoc, whisker_exchange_assoc,
          associator_naturality_right_assoc, ← MonoidalCategory.whiskerLeft_comp]
    _ = 𝟙 _ := by
        rw [whiskerLeft_projectionFormulaMap_comp_evaluation adj K K' N]
        exact leftUnitor_inv_coevaluation_evaluation K K' (G.obj N)

/-- The projection-formula map at `K`, as a morphism of functors of the pushed-forward
variable. -/
@[simps]
def projectionFormulaNatTrans (K : C) : G ⋙ tensorLeft K ⟶ tensorLeft (F.obj K) ⋙ G where
  app E := projectionFormulaMap adj E K
  naturality _ _ g := projectionFormulaMap_naturality_right adj g K

section Comparison

variable {a : C ⥤ D} (adj' : G ⊣ a) [∀ (E : D) (K : C), IsIso (projectionFormulaMap adj E K)]

/-- **The comparison map** `F K ⊗ a L ⟶ a (K ⊗ L)`: the transpose, for `G ⊣ a`, of the inverse
projection-formula map followed by `K` tensored with the counit of `G ⊣ a`. This is the
two-variable form of Equation 48.8.0.1 of [Stacks, Tag 0A9S]. -/
def comparison (K L : C) : F.obj K ⊗ a.obj L ⟶ a.obj (K ⊗ L) :=
  adj'.homEquiv _ _ (inv (projectionFormulaMap adj (a.obj L) K) ≫ K ◁ adj'.counit.app L)

/-- The defining property of the comparison map, transposed. -/
lemma map_comparison_comp_counit (K L : C) :
    G.map (comparison adj adj' K L) ≫ adj'.counit.app (K ⊗ L) =
      inv (projectionFormulaMap adj (a.obj L) K) ≫ K ◁ adj'.counit.app L := by
  have h := (adj'.homEquiv (F.obj K ⊗ a.obj L) (K ⊗ L)).symm_apply_apply
    (inv (projectionFormulaMap adj (a.obj L) K) ≫ K ◁ adj'.counit.app L)
  rw [Adjunction.homEquiv_counit] at h
  exact h

/-- The comparison map is natural in the pulled-back variable. -/
@[reassoc]
lemma comparison_naturality_left {K K' : C} (f : K ⟶ K') (L : C) :
    F.map f ▷ a.obj L ≫ comparison adj adj' K' L = comparison adj adj' K L ≫ a.map (f ▷ L) := by
  apply (adj'.homEquiv _ _).symm.injective
  rw [Adjunction.homEquiv_naturality_left_symm, Adjunction.homEquiv_naturality_right_symm,
    Adjunction.homEquiv_counit, Adjunction.homEquiv_counit, map_comparison_comp_counit,
    map_comparison_comp_counit]
  have h' : G.map (F.map f ▷ a.obj L) ≫ inv (projectionFormulaMap adj (a.obj L) K') =
      inv (projectionFormulaMap adj (a.obj L) K) ≫ f ▷ G.obj (a.obj L) := by
    rw [IsIso.comp_inv_eq, Category.assoc, projectionFormulaMap_naturality_left,
      IsIso.inv_hom_id_assoc]
  rw [reassoc_of% h', Category.assoc, ← whisker_exchange]
  rfl

/-- `F K ⊗ a(-)` is right adjoint to `G (F K' ⊗ -)`, for the image pairing of `F`. -/
abbrev tensorRightAdjointAdjunction (K K' : C) [ExactPairing K K'] :
    letI := ExactPairing.map F K K'
    tensorLeft (F.obj K') ⋙ G ⊣ a ⋙ tensorLeft (F.obj K) :=
  letI := ExactPairing.map F K K'
  (tensorLeftAdjunction (F.obj K) (F.obj K')).comp adj'

/-- `a (K ⊗ -)` is right adjoint to `K' ⊗ G(-)`. -/
abbrev rightAdjointTensorAdjunction (K K' : C) [ExactPairing K K'] :
    G ⋙ tensorLeft K' ⊣ tensorLeft K ⋙ a :=
  adj'.comp (tensorLeftAdjunction K K')

/-- **The comparison map at a dualizable object is the conjugate of the projection-formula map
at its dual.** -/
lemma conjugateEquiv_projectionFormulaNatTrans_app (K K' : C) [ExactPairing K K'] (L : C) :
    (conjugateEquiv (tensorRightAdjointAdjunction adj' K K')
      (rightAdjointTensorAdjunction adj' K K') (projectionFormulaNatTrans adj K')).app L =
        comparison adj adj' K L := by
  let := ExactPairing.map F K K'
  apply (adj'.homEquiv _ _).symm.injective
  rw [Adjunction.homEquiv_counit, Adjunction.homEquiv_counit]
  refine Eq.trans ?_ (map_comparison_comp_counit adj adj' K L).symm
  have hX := map_conjugateEquiv_comp_counit adj' (F.obj K) (F.obj K') K K'
    (projectionFormulaNatTrans adj K') L
  simp only [projectionFormulaNatTrans_app] at hX
  refine hX.trans ?_
  rw [IsIso.eq_inv_comp]
  simp only [tensorLeftHomEquiv, Equiv.coe_fn_mk, MonoidalCategory.whiskerLeft_comp]
  have h' := projectionFormulaMap_comp_inverse adj K K' (a.obj L)
  simp only [MonoidalCategory.whiskerLeft_comp] at h' ⊢
  rw [reassoc_of% h']

/-- **[Stacks, Tag 0A9T], abstractly.** If the projection-formula map is invertible everywhere and
`K` has a right dual, the comparison map `F K ⊗ a L ⟶ a (K ⊗ L)` is an isomorphism for every `L`:
it is the conjugate of the projection-formula map at the dual of `K`, an isomorphism between left
adjoints. -/
theorem isIso_comparison_of_exactPairing (K K' : C) [ExactPairing K K'] (L : C) :
    IsIso (comparison adj adj' K L) := by
  rw [← conjugateEquiv_projectionFormulaNatTrans_app adj adj' K K' L]
  have : IsIso (projectionFormulaNatTrans adj K') :=
    @NatIso.isIso_of_isIso_app _ _ _ _ _ _ (projectionFormulaNatTrans adj K') fun X => by
      rw [projectionFormulaNatTrans_app]
      infer_instance
  infer_instance

end Comparison

end CategoryTheory.MonoidalProjectionFormula
