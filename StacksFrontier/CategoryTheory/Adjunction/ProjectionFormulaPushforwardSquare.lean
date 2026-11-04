module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.ProjectionFormula
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PushforwardTensorMap

/-!
# The two projection formulas around a square of adjunctions, pushed forward

Consider a square of categories in which all four functors have right adjoints

```
        Lj
   CX -----→ CU
 Li |         | Li'
    v         v
   CN -----→ CM
        Ljn
```

with `Lj ⊣ Rj`, `Li ⊣ Ri`, `Ljn ⊣ Rjn`, `Li' ⊣ Ri'`, the two composites around the square
identified with one functor `Lc` by `e₁ : Li ⋙ Ljn ≅ Lc` and `e₂ : Lj ⋙ Li' ≅ Lc`, and bifunctors
`TX`, `TU`, `TN`, `TM` on the four corners with a comparison along each of the four left adjoints.
For `E` in `CU` and `G` in `CN` there are two maps

`TX(Rj E, Ri G) ⟶ Ri (Rjn (TM (Li' E, Ljn G)))`

built from projection-formula maps and base change maps:

* the projection formula of `Lj ⊣ Rj` at `(E, Ri G)`, then `Rj` of the base change map
  `Lj Ri G ⟶ Ri' Ljn G` of the transposed square, then `Rj` of the projection formula of
  `Li' ⊣ Ri'` with the counit in the second factor at `(E, Ljn G)`, then the conjugate
  identification `Rj Ri' ≅ Ri Rjn`;
* the projection formula of `Li ⊣ Ri` with the counit in the second factor at `(Rj E, G)`, then
  `Ri` of the base change map `Li Rj E ⟶ Rjn Li' E`, then `Ri` of the projection formula of
  `Ljn ⊣ Rjn` at `(Li' E, G)`.

They agree as soon as the four comparisons are compatible around the square
(`Stacks.AffineProjectionFormula.TensorComparisonCompatible`). In the geometric situation of an
étale `j : U ⟶ X`, a closed immersion `i : Xₙ ⟶ X` and their base changes, this is the
compatibility of the projection formula along `j` with the one along `jₙ : Uₙ ⟶ Xₙ`, through the
projection formula along `i`.

## Main results

* `Stacks.AffineProjectionFormula.adjunctionTensorMap_pushforward_square`: the two maps agree.
-/

@[expose] public section

open CategoryTheory
open scoped CategoryTheory.Prod

namespace Stacks.AffineProjectionFormula

variable {CX CU CN CM : Type*} [Category CX] [Category CU] [Category CN] [Category CM]
  {Lj : CX ⥤ CU} {Rj : CU ⥤ CX} (aj : Lj ⊣ Rj)
  {Li : CX ⥤ CN} {Ri : CN ⥤ CX} (ai : Li ⊣ Ri)
  {Ljn : CN ⥤ CM} {Rjn : CM ⥤ CN} (ajn : Ljn ⊣ Rjn)
  {Li' : CU ⥤ CM} {Ri' : CM ⥤ CU} (ai' : Li' ⊣ Ri')
  {Lc : CX ⥤ CM} (e₁ : Li ⋙ Ljn ≅ Lc) (e₂ : Lj ⋙ Li' ≅ Lc)
  (TX : CX × CX ⥤ CX) (TU : CU × CU ⥤ CU) (TN : CN × CN ⥤ CN) (TM : CM × CM ⥤ CM)
  (μj : TX ⋙ Lj ⟶ Lj.prod Lj ⋙ TU) (μi : TX ⋙ Li ⟶ Li.prod Li ⋙ TN)
  (μjn : TN ⋙ Ljn ⟶ Ljn.prod Ljn ⋙ TM) (μi' : TU ⋙ Li' ⟶ Li'.prod Li' ⋙ TM)

/-- The identification `Ri' ⋙ Rj ≅ Rjn ⋙ Ri` of the two composites of right adjoints around the
square: the conjugate of `e₁ ≪≫ e₂.symm : Li ⋙ Ljn ≅ Lj ⋙ Li'`. -/
def pushforwardSquareIso : Ri' ⋙ Rj ≅ Rjn ⋙ Ri :=
  conjugateIsoEquiv (aj.comp ai') (ai.comp ajn) (e₁ ≪≫ e₂.symm)

/-- The adjunct of the projection formula with the counit in the second factor: applying the left
adjoint and the counit gives the comparison followed by the counit in the second factor. -/
private theorem map_adjunctionTensorMapSnd_comp_counit' {C D : Type*} [Category C] [Category D]
    {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R) (A : C × C ⥤ C) (B : D × D ⥤ D)
    (α : A ⋙ L ⟶ L.prod L ⋙ B) (H : C) (G' : D) :
    L.map (Stacks.ProjectionFormula.adjunctionTensorMapSnd adj A B α H G') ≫
        adj.counit.app (B.obj (L.obj H, G')) =
      α.app (H, R.obj G') ≫ B.map (𝟙 (L.obj H) ×ₘ adj.counit.app G') := by
  have h := (adj.homEquiv _ _).symm_apply_apply
    (α.app (H, R.obj G') ≫ B.map (𝟙 (L.obj H) ×ₘ adj.counit.app G'))
  rwa [Adjunction.homEquiv_counit] at h

/-- Maps of a bifunctor out of a product compose componentwise. -/
private theorem map_prod_comp_map_prod {C D : Type*} [Category C] [Category D] (T : C × C ⥤ D)
    {a a' a'' b b' b'' : C} (f : a ⟶ a') (f' : a' ⟶ a'') (g : b ⟶ b') (g' : b' ⟶ b'') :
    T.map (f ×ₘ g) ≫ T.map (f' ×ₘ g') = T.map ((f ≫ f') ×ₘ (g ≫ g')) := by
  rw [← Functor.map_comp]; rfl

/-- A map of both variables followed by a map in the second. -/
private theorem map_prod_comp_map_id_prod {C D : Type*} [Category C] [Category D]
    (T : C × C ⥤ D) {a a' b b' b'' : C} (f : a ⟶ a') (g : b ⟶ b') (g' : b' ⟶ b'') :
    T.map (f ×ₘ g) ≫ T.map (𝟙 a' ×ₘ g') = T.map (f ×ₘ (g ≫ g')) := by
  rw [map_prod_comp_map_prod, Category.comp_id]

/-- A map of both variables followed by a map in the first. -/
private theorem map_prod_comp_map_prod_id {C D : Type*} [Category C] [Category D]
    (T : C × C ⥤ D) {a a' a'' b b' : C} (f : a ⟶ a') (f' : a' ⟶ a'') (g : b ⟶ b') :
    T.map (f ×ₘ g) ≫ T.map (f' ×ₘ 𝟙 b') = T.map ((f ≫ f') ×ₘ g) := by
  rw [map_prod_comp_map_prod, Category.comp_id]

/-- Transposing a composite with a conjugate: for `α : L₂ ⟶ L₁` with conjugate
`β : R₁ ⟶ R₂`, the adjunct under `L₂ ⊣ R₂` of `f ≫ β` is `α` followed by the adjunct of `f` under
`L₁ ⊣ R₁`. -/
private theorem homEquiv_symm_comp_conjugateEquiv {C D : Type*} [Category C] [Category D]
    {L₁ L₂ : C ⥤ D} {R₁ R₂ : D ⥤ C} (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (α : L₂ ⟶ L₁) (X : C)
    (Y : D) (f : X ⟶ R₁.obj Y) :
    (adj₂.homEquiv X Y).symm (f ≫ (conjugateEquiv adj₁ adj₂ α).app Y) =
      α.app X ≫ (adj₁.homEquiv X Y).symm f := by
  simp only [Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc,
    conjugateEquiv_counit]
  rw [← α.naturality_assoc]

/-- A chain of two pushed-forward maps and the counit, after applying the left adjoint, is the
counit at the source followed by the two maps. -/
private theorem map_comp_map_map_counit {C D : Type*} [Category C] [Category D] {L : C ⥤ D}
    {R : D ⥤ C} (adj : L ⊣ R) {X : C} {Y Y' Y'' : D} (f : X ⟶ R.obj Y) (g : Y ⟶ Y')
    (h : Y' ⟶ Y'') :
    L.map f ≫ L.map (R.map g) ≫ L.map (R.map h) ≫ adj.counit.app Y'' =
      L.map f ≫ adj.counit.app Y ≫ g ≫ h := by
  simp

/-- **The two projection formulas around a square agree after pushing forward.** For `E` in `CU`
and `G` in `CN`, the projection formula of `Lj ⊣ Rj` at `(E, Ri G)` followed by the base change
map of the transposed square, the projection formula of `Li' ⊣ Ri'` and the identification
`Rj Ri' ≅ Ri Rjn`, equals the projection formula of `Li ⊣ Ri` at `(Rj E, G)` followed by the base
change map `Li Rj E ⟶ Rjn Li' E` and the projection formula of `Ljn ⊣ Rjn`. -/
theorem adjunctionTensorMap_pushforward_square (E : CU) (G : CN)
    (hsq : TensorComparisonCompatible e₁ e₂ TX TN TU TM μj μjn μi μi' (Rj.obj E) (Ri.obj G)) :
    adjunctionTensorMap aj TX TU μj E (Ri.obj G) ≫
        Rj.map (TU.map (𝟙 E ×ₘ Stacks.CategoryTheory.BaseChange.map ai ai' e₂ e₁ G) ≫
          Stacks.ProjectionFormula.adjunctionTensorMapSnd ai' TU TM μi' E (Ljn.obj G)) ≫
        (pushforwardSquareIso aj ai ajn ai' e₁ e₂).hom.app (TM.obj (Li'.obj E, Ljn.obj G)) =
      Stacks.ProjectionFormula.adjunctionTensorMapSnd ai TX TN μi (Rj.obj E) G ≫
        Ri.map (TN.map (Stacks.CategoryTheory.BaseChange.map aj ajn e₁ e₂ E ×ₘ 𝟙 G) ≫
          adjunctionTensorMap ajn TN TM μjn (Li'.obj E) G) := by
  rw [TensorComparisonCompatible] at hsq
  have hconj : ∀ {X : CX} {Y : CM} (f : X ⟶ Rj.obj (Ri'.obj Y)),
      ((ai.comp ajn).homEquiv X Y).symm
          (f ≫ (pushforwardSquareIso aj ai ajn ai' e₁ e₂).hom.app Y) =
        (e₁.hom.app X ≫ e₂.inv.app X) ≫ ((aj.comp ai').homEquiv X Y).symm f :=
    homEquiv_symm_comp_conjugateEquiv (aj.comp ai') (ai.comp ajn) (e₁ ≪≫ e₂.symm).hom _ _
  refine ((ai.comp ajn).homEquiv _ _).symm.injective ?_
  rw [← Category.assoc, hconj]
  simp only [Adjunction.homEquiv_counit, Functor.comp_map, Functor.map_comp, Category.assoc,
    Adjunction.comp_counit_app, Functor.comp_obj]
  have k1 : Lj.map (adjunctionTensorMap aj TX TU μj E (Ri.obj G)) ≫
      Lj.map (Rj.map (TU.map (𝟙 E ×ₘ Stacks.CategoryTheory.BaseChange.map ai ai' e₂ e₁ G))) ≫
      Lj.map (Rj.map (Stacks.ProjectionFormula.adjunctionTensorMapSnd ai' TU TM μi' E
        (Ljn.obj G))) ≫
      aj.counit.app (Ri'.obj (TM.obj (Li'.obj E, Ljn.obj G))) =
      μj.app (Rj.obj E, Ri.obj G) ≫ TU.map (aj.counit.app E ×ₘ 𝟙 (Lj.obj (Ri.obj G))) ≫
        TU.map (𝟙 E ×ₘ Stacks.CategoryTheory.BaseChange.map ai ai' e₂ e₁ G) ≫
        Stacks.ProjectionFormula.adjunctionTensorMapSnd ai' TU TM μi' E (Ljn.obj G) := by
    rw [map_comp_map_map_counit, map_adjunctionTensorMap_comp_counit_assoc]
  have m1 : TU.map (aj.counit.app E ×ₘ 𝟙 (Lj.obj (Ri.obj G))) ≫
      TU.map (𝟙 E ×ₘ Stacks.CategoryTheory.BaseChange.map ai ai' e₂ e₁ G) =
      TU.map (aj.counit.app E ×ₘ Stacks.CategoryTheory.BaseChange.map ai ai' e₂ e₁ G) := by
    rw [← Functor.map_comp]; simp
  have h2 := μi'.naturality
    (X := ((Lj.obj (Rj.obj E), Lj.obj (Ri.obj G)) : CU × CU))
    (Y := ((E, Ri'.obj (Ljn.obj G)) : CU × CU))
    (aj.counit.app E ×ₘ Stacks.CategoryTheory.BaseChange.map ai ai' e₂ e₁ G)
  simp only [Functor.comp_map, Functor.prod_map] at h2
  have hL : Li'.map (Lj.map (adjunctionTensorMap aj TX TU μj E (Ri.obj G))) ≫
      Li'.map (Lj.map (Rj.map (TU.map (𝟙 E ×ₘ
        Stacks.CategoryTheory.BaseChange.map ai ai' e₂ e₁ G)))) ≫
      Li'.map (Lj.map (Rj.map (Stacks.ProjectionFormula.adjunctionTensorMapSnd ai' TU TM μi' E
        (Ljn.obj G)))) ≫
      Li'.map (aj.counit.app (Ri'.obj (TM.obj (Li'.obj E, Ljn.obj G)))) ≫
      ai'.counit.app (TM.obj (Li'.obj E, Ljn.obj G)) =
      Li'.map (μj.app (Rj.obj E, Ri.obj G)) ≫ μi'.app (Lj.obj (Rj.obj E), Lj.obj (Ri.obj G)) ≫
        TM.map (Li'.map (aj.counit.app E) ×ₘ
          ((squareCompositeIso e₂ e₁).hom.app (Ri.obj G) ≫ Ljn.map (ai.counit.app G))) := by
    simp only [← Li'.map_comp_assoc]
    rw [k1, reassoc_of% m1,
      Li'.map_comp, Li'.map_comp, Category.assoc, Category.assoc,
      map_adjunctionTensorMapSnd_comp_counit' ai' TU TM μi' E (Ljn.obj G), reassoc_of% h2,
      map_prod_comp_map_id_prod, map_baseChangeMap_comp_counit]
  have k2 : Li.map (Stacks.ProjectionFormula.adjunctionTensorMapSnd ai TX TN μi (Rj.obj E) G) ≫
      Li.map (Ri.map (TN.map (Stacks.CategoryTheory.BaseChange.map aj ajn e₁ e₂ E ×ₘ 𝟙 G))) ≫
      Li.map (Ri.map (adjunctionTensorMap ajn TN TM μjn (Li'.obj E) G)) ≫
      ai.counit.app (Rjn.obj (TM.obj (Li'.obj E, Ljn.obj G))) =
      μi.app (Rj.obj E, Ri.obj G) ≫ TN.map (𝟙 (Li.obj (Rj.obj E)) ×ₘ ai.counit.app G) ≫
        TN.map (Stacks.CategoryTheory.BaseChange.map aj ajn e₁ e₂ E ×ₘ 𝟙 G) ≫
        adjunctionTensorMap ajn TN TM μjn (Li'.obj E) G := by
    rw [map_comp_map_map_counit,
      reassoc_of% (map_adjunctionTensorMapSnd_comp_counit' ai TX TN μi (Rj.obj E) G)]
  have m2 : TN.map (𝟙 (Li.obj (Rj.obj E)) ×ₘ ai.counit.app G) ≫
      TN.map (Stacks.CategoryTheory.BaseChange.map aj ajn e₁ e₂ E ×ₘ 𝟙 G) =
      TN.map (Stacks.CategoryTheory.BaseChange.map aj ajn e₁ e₂ E ×ₘ ai.counit.app G) := by
    rw [← Functor.map_comp]; simp
  have h2' := μjn.naturality
    (X := ((Li.obj (Rj.obj E), Li.obj (Ri.obj G)) : CN × CN))
    (Y := ((Rjn.obj (Li'.obj E), G) : CN × CN))
    (Stacks.CategoryTheory.BaseChange.map aj ajn e₁ e₂ E ×ₘ ai.counit.app G)
  simp only [Functor.comp_map, Functor.prod_map] at h2'
  have hR : Ljn.map (Li.map (Stacks.ProjectionFormula.adjunctionTensorMapSnd ai TX TN μi (Rj.obj E)
        G)) ≫
      Ljn.map (Li.map (Ri.map (TN.map (Stacks.CategoryTheory.BaseChange.map aj ajn e₁ e₂ E ×ₘ
        𝟙 G)))) ≫
      Ljn.map (Li.map (Ri.map (adjunctionTensorMap ajn TN TM μjn (Li'.obj E) G))) ≫
      Ljn.map (ai.counit.app (Rjn.obj (TM.obj (Li'.obj E, Ljn.obj G)))) ≫
      ajn.counit.app (TM.obj (Li'.obj E, Ljn.obj G)) =
      Ljn.map (μi.app (Rj.obj E, Ri.obj G)) ≫ μjn.app (Li.obj (Rj.obj E), Li.obj (Ri.obj G)) ≫
        TM.map (((squareCompositeIso e₁ e₂).hom.app (Rj.obj E) ≫ Li'.map (aj.counit.app E)) ×ₘ
          Ljn.map (ai.counit.app G)) := by
    simp only [← Ljn.map_comp_assoc]
    rw [k2, reassoc_of% m2,
      Ljn.map_comp, Ljn.map_comp, Category.assoc, Category.assoc,
      map_adjunctionTensorMap_comp_counit, reassoc_of% h2',
      map_prod_comp_map_prod_id, map_baseChangeMap_comp_counit]
  rw [hL, hR]
  have hsplit : TM.map (((squareCompositeIso e₁ e₂).hom.app (Rj.obj E) ≫
        Li'.map (aj.counit.app E)) ×ₘ Ljn.map (ai.counit.app G)) =
      TM.map ((squareCompositeIso e₁ e₂).hom.app (Rj.obj E) ×ₘ
          (squareCompositeIso e₁ e₂).hom.app (Ri.obj G)) ≫
        TM.map (Li'.map (aj.counit.app E) ×ₘ
          ((squareCompositeIso e₂ e₁).hom.app (Ri.obj G) ≫ Ljn.map (ai.counit.app G))) := by
    rw [map_prod_comp_map_prod]
    congr 2
    simp [squareCompositeIso_hom_app]
  rw [hsplit, reassoc_of% hsq]
  simp only [squareCompositeIso_hom_app, Category.assoc]

end Stacks.AffineProjectionFormula

end
