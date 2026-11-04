module

public import StacksFrontier.CategoryTheory.Sites.Simplicial.CartesianDerivedRealization
public import StacksFrontier.CategoryTheory.Triangulated.SequentialPostnikovSystems

/-!
# The Postnikov system of the realization of a cartesian simplicial system

Let `S` be a simplicial-site situation and `T` a cartesian simplicial system of the derived
categories of its components, in the sense of Stacks 0D9G, whose objects have no positively
shifted self-maps.  The object of the derived category of the total site that induces `T` is the
totalization of the complex `CategoryTheory.SimplicialSiteSituation.realizationComplex`, whose
term in degree `n` is the extension by lower shriek of the object of the system in degree `n`.
Building that totalization means building a Postnikov system for the complex, and this file
produces one.

The two inputs the construction of Stacks 0D83 asks for are supplied here.  That the differentials
of the complex compose to zero is automatic, the complex being the alternating face map complex of
a simplicial object.  That every positively shifted morphism between its terms vanishes is the
content of the sum formula: restricting a term of the complex to one simplicial degree gives, by
Stacks 09WG, a direct sum of inverse images along the transitions, and cartesianness identifies
each summand with one object of the system, so the vanishing descends from the hypothesis on the
system.

## Main results

* `CategoryTheory.SimplicialSiteSituation.derived_component_summand`: the summand inclusions of
  the direct-sum formula of Stacks 09WG, read on derived categories, are the unit of
  `g_{n!} ⊣ g_n^{-1}` followed by the derived transition of Stacks 07TF.
* `CategoryTheory.SimplicialSiteSituation.realizationTermComponentIso`: the restriction of a term
  of the realization to one simplicial degree is a direct sum of inverse images of the objects of
  the system.
* `CategoryTheory.SimplicialSiteSituation.realizationTerm_hom_zero_of_biproduct`: consequently the
  positively shifted morphisms between the terms of the realization vanish.
* `CategoryTheory.SimplicialSiteSituation.nonempty_sequentialPostnikovSystem_realizationComplex`:
  the realization complex carries a sequential Postnikov system.

## References

* [Stacks Project, Tag 07TF](https://stacks.math.columbia.edu/tag/07TF)
* [Stacks Project, Tag 09WG](https://stacks.math.columbia.edu/tag/09WG)
* [Stacks Project, Tag 0D83](https://stacks.math.columbia.edu/tag/0D83)
* [Stacks Project, Tag 0D9G](https://stacks.math.columbia.edu/tag/0D9G)
* [Stacks Project, Tag 0D9I](https://stacks.math.columbia.edu/tag/0D9I)
* [Stacks Project, Tag 0D9L](https://stacks.math.columbia.edu/tag/0D9L)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
open CategoryTheory.SimplicialSiteSituation
open scoped Simplicial

universe v u


namespace CategoryTheory.SimplicialSiteSituation

attribute [local implicit_reducible] CategoryTheory.derivedInverseImage
  CategoryTheory.SimplicialSiteSituation.componentLowerShriekDerived

attribute [local instance]
  CategoryTheory.SimplicialSiteSituation.componentFunctorHasCoproductsOfShape
  CategoryTheory.SimplicialSiteSituation.abelianTransitionHasBiproduct

variable (S : SimplicialSiteSituation.{u})
  [HasDerivedCategory.{v} (Sheaf S.totalTopology Ab.{u})]
  [∀ n, HasDerivedCategory.{v} (Sheaf (S.componentTopology n) Ab.{u})]

/-- Mapping the identity transformation to complexes gives the identity. -/
theorem natIso_mapHomologicalComplex_refl_hom_app {A' B' : Type*} [Category A']
    [Category B'] [Preadditive A'] [Preadditive B'] (F : A' ⥤ B') [F.Additive]
    (X : CochainComplex A' ℤ) :
    (NatIso.mapHomologicalComplex (Iso.refl F) (ComplexShape.up ℤ)).hom.app X = 𝟙 _ :=
  HomologicalComplex.hom_ext _ _ fun _ => rfl

/-- Naturality of the canonical derived transition, with the derived restriction spelled as the
derived functor of `S.abelianComponent`. -/
theorem derivedTransition_naturality' {n m : SimplexCategory} (φ : n ⟶ m)
    {K K' : DerivedCategory (Sheaf S.totalTopology Ab.{u})} (g : K ⟶ K') :
    (derivedInverseImage S φ).map ((S.abelianComponent n).mapDerivedCategory.map g) ≫
        (derivedTransition S φ).app K' =
      (derivedTransition S φ).app K ≫ (S.abelianComponent m).mapDerivedCategory.map g :=
  (derivedTransition S φ).naturality g

/-- Naturality of the canonical derived transition, with the derived restriction spelled as the
derived functor of `S.restrictAb`. -/
theorem derivedTransition_naturality'' {n m : SimplexCategory} (φ : n ⟶ m)
    {K K' : DerivedCategory (Sheaf S.totalTopology Ab.{u})} (g : K ⟶ K') :
    (derivedInverseImage S φ).map ((S.restrictAb n).mapDerivedCategory.map g) ≫
        (derivedTransition S φ).app K' =
      (derivedTransition S φ).app K ≫ (S.restrictAb m).mapDerivedCategory.map g :=
  (derivedTransition S φ).naturality g

/-- The canonical derived transition on the image of a complex. -/
theorem derivedTransition_app_Q' {n m : SimplexCategory} (φ : n ⟶ m)
    (Y : CochainComplex (Sheaf S.totalTopology Ab.{u}) ℤ) :
    (derivedTransition S φ).app (DerivedCategory.Q.obj Y) =
      (derivedInverseImage S φ).map
          ((S.abelianComponent n).mapDerivedCategoryFactors.hom.app Y) ≫
        (abelianTransition S φ).mapDerivedCategoryFactors.hom.app
          (((S.abelianComponent n).mapHomologicalComplex (ComplexShape.up ℤ)).obj Y) ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex
          (S.abelianTransitionOfFiber φ) (ComplexShape.up ℤ)).app Y) ≫
        (S.abelianComponent m).mapDerivedCategoryFactors.inv.app Y := by
  refine (cancel_mono ((S.abelianComponent m).mapDerivedCategoryFactors.hom.app Y)).1 ?_
  refine Eq.trans (derivedTransition_app_Q_comp S φ Y) ?_
  simp

/-- The canonical derived transition on the image of a complex, with the restrictions spelled as
`S.restrictAb`. -/
theorem derivedTransition_app_Q'' {n m : SimplexCategory} (φ : n ⟶ m)
    (Y : CochainComplex (Sheaf S.totalTopology Ab.{u}) ℤ) :
    (derivedTransition S φ).app (DerivedCategory.Q.obj Y) =
      (derivedInverseImage S φ).map
          ((S.restrictAb n).mapDerivedCategoryFactors.hom.app Y) ≫
        (abelianTransition S φ).mapDerivedCategoryFactors.hom.app
          (((S.restrictAb n).mapHomologicalComplex (ComplexShape.up ℤ)).obj Y) ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex
          (S.abelianTransitionOfFiber' φ) (ComplexShape.up ℤ)).app Y) ≫
        (S.restrictAb m).mapDerivedCategoryFactors.inv.app Y :=
  derivedTransition_app_Q' S φ Y

omit [HasDerivedCategory.{v} (Sheaf S.totalTopology Ab.{u})] in
/-- Naturality of the identification of the derived functor of the transition with the
localization of the transition applied to complexes. -/
theorem abelianTransition_mapDerivedCategoryFactors_hom_naturality
    {n m : SimplexCategory} (φ : n ⟶ m)
    {X Y : CochainComplex (Sheaf (S.componentTopology n) Ab.{u}) ℤ} (u : X ⟶ Y) :
    (derivedInverseImage S φ).map (DerivedCategory.Q.map u) ≫
        (abelianTransition S φ).mapDerivedCategoryFactors.hom.app Y =
      (abelianTransition S φ).mapDerivedCategoryFactors.hom.app X ≫
        DerivedCategory.Q.map
          (((abelianTransition S φ).mapHomologicalComplex (ComplexShape.up ℤ)).map u) :=
  (abelianTransition S φ).mapDerivedCategoryFactors.hom.naturality u

/-- **The summands of the direct-sum formula, on derived categories.** The derived functor of the
`φ`th summand inclusion of the direct-sum formula of Stacks 09WG, composed with the comparison of
derived functors of a composite, is the unit of `g_{n!} ⊣ g_n^{-1}` followed by the derived
transition of Stacks 07TF. -/
theorem derived_component_summand {n m : SimplexCategory} (φ : n ⟶ m) :
    derivedNatTrans (abelianTransition S φ)
        (Functor.sheafPullbackConstruction.sheafPullback (S.componentFunctor n) Ab.{u}
          (S.componentTopology n) S.totalTopology ⋙ S.abelianComponent m)
        (Limits.biproduct.ι (fun ψ : n ⟶ m => abelianTransition S ψ) φ ≫
          (S.componentLowerShriekBiproductIso m n).inv) ≫
      (derivedCompIso
        (Functor.sheafPullbackConstruction.sheafPullback (S.componentFunctor n) Ab.{u}
          (S.componentTopology n) S.totalTopology) (S.abelianComponent m) _ (Iso.refl _)).hom =
    Functor.whiskerRight (S.componentLowerShriekDerivedAdjunction n).unit
        (derivedInverseImage S φ) ≫
      Functor.whiskerLeft (S.componentLowerShriekDerived n) (derivedTransition S φ) := by
  rw [componentLowerShriekBiproductIso_ι]
  refine Localization.natTrans_ext DerivedCategory.Q
    (HomologicalComplex.quasiIso (Sheaf (S.componentTopology n) Ab.{u}) (ComplexShape.up ℤ))
    fun X => ?_
  simp only [NatTrans.comp_app, derivedNatTrans_app_Q', derivedCompIso_hom_app_Q,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, Category.assoc,
    Iso.inv_hom_id_app_assoc]
  have hunit : (S.componentLowerShriekDerivedAdjunction n).unit.app
        (DerivedCategory.Q.obj X) =
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex
          (S.componentLowerShriekAbAdjunction n).unit (ComplexShape.up ℤ)).app X) ≫
        (S.abelianComponent n).mapDerivedCategoryFactors.inv.app
          (((Functor.sheafPullbackConstruction.sheafPullback (S.componentFunctor n) Ab.{u}
            (S.componentTopology n) S.totalTopology).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj X) ≫
        (S.abelianComponent n).mapDerivedCategory.map
          ((Functor.sheafPullbackConstruction.sheafPullback (S.componentFunctor n) Ab.{u}
            (S.componentTopology n) S.totalTopology).mapDerivedCategoryFactors.inv.app X) :=
    mapDerivedCategoryAdjunction_unit_app_Q (S.componentLowerShriekAbAdjunction n) X
  dsimp only [Functor.comp_obj]
  rw [natIso_mapHomologicalComplex_refl_hom_app, Functor.map_id]
  simp only [Category.id_comp]
  rw [hunit]
  simp only [Functor.map_comp, Category.assoc]
  refine Eq.trans ?_ (congrArg (fun k =>
    (derivedInverseImage S φ).map (DerivedCategory.Q.map
      ((NatTrans.mapHomologicalComplex (S.componentLowerShriekAbAdjunction n).unit
        (ComplexShape.up ℤ)).app X)) ≫
    (derivedInverseImage S φ).map
      ((S.abelianComponent n).mapDerivedCategoryFactors.inv.app
        (((Functor.sheafPullbackConstruction.sheafPullback (S.componentFunctor n) Ab.{u}
          (S.componentTopology n) S.totalTopology).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj X)) ≫ k)
    (derivedTransition_naturality' S φ
      ((Functor.sheafPullbackConstruction.sheafPullback (S.componentFunctor n) Ab.{u}
        (S.componentTopology n) S.totalTopology).mapDerivedCategoryFactors.inv.app X))).symm
  dsimp only [Functor.comp_obj]
  rw [derivedTransition_app_Q']
  have hc : (derivedInverseImage S φ).map
        ((S.abelianComponent n).mapDerivedCategoryFactors.inv.app
          (((Functor.sheafPullbackConstruction.sheafPullback (S.componentFunctor n) Ab.{u}
            (S.componentTopology n) S.totalTopology).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj X)) ≫
      (derivedInverseImage S φ).map
        ((S.abelianComponent n).mapDerivedCategoryFactors.hom.app
          (((Functor.sheafPullbackConstruction.sheafPullback (S.componentFunctor n) Ab.{u}
            (S.componentTopology n) S.totalTopology).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj X)) = 𝟙 _ := by
    rw [← Functor.map_comp, Iso.inv_hom_id_app, Functor.map_id]
  simp only [Category.assoc]
  rw [reassoc_of% hc]
  rw [reassoc_of% (abelianTransition_mapDerivedCategoryFactors_hom_naturality S φ
    (show X ⟶ ((S.abelianComponent n).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (((Functor.sheafPullbackConstruction.sheafPullback (S.componentFunctor n) Ab.{u}
          (S.componentTopology n) S.totalTopology).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj X) from
      (NatTrans.mapHomologicalComplex (S.componentLowerShriekAbAdjunction n).unit
        (ComplexShape.up ℤ)).app X))]
  simp only [← DerivedCategory.Q.map_comp_assoc]
  congr 1

/-- `derived_component_summand`, with the restriction to degree `m` spelled as `S.restrictAb m`. -/
theorem derived_component_summand' {n m : SimplexCategory} (φ : n ⟶ m) :
    derivedNatTrans (abelianTransition S φ)
        (Functor.sheafPullbackConstruction.sheafPullback (S.componentFunctor n) Ab.{u}
          (S.componentTopology n) S.totalTopology ⋙ S.restrictAb m)
        (Limits.biproduct.ι (fun ψ : n ⟶ m => abelianTransition S ψ) φ ≫
          (S.componentLowerShriekBiproductIso' m n).inv) ≫
      (derivedCompIso
        (Functor.sheafPullbackConstruction.sheafPullback (S.componentFunctor n) Ab.{u}
          (S.componentTopology n) S.totalTopology) (S.restrictAb m) _ (Iso.refl _)).hom =
    Functor.whiskerRight (S.componentLowerShriekDerivedAdjunction n).unit
        (derivedInverseImage S φ) ≫
      Functor.whiskerLeft (S.componentLowerShriekDerived n) (derivedTransition S φ) :=
  derived_component_summand S φ

/-- The restriction to degree `i` of the realization in degree `j` is the direct sum over the
simplex maps `[j] ⟶ [i]` of the inverse images of the object of the system. -/
noncomputable def realizationTermComponentIso (T : SimplicialDerivedSystem S)
    (i j : SimplexCategory) :
    (derivedComponent S i).obj (realizationTerm S T j) ≅
      ⨁ fun φ : j ⟶ i => (derivedInverseImage S φ).obj (T.obj j) := by
  letI : Fintype (j ⟶ i) := Fintype.ofFinite (j ⟶ i)
  exact ((derivedCompIso
      (Functor.sheafPullbackConstruction.sheafPullback (S.componentFunctor j) Ab.{u}
        (S.componentTopology j) S.totalTopology) (S.abelianComponent i) _
      (Iso.refl _)).app (T.obj j)).symm ≪≫
    derivedBiproductIso
      (Functor.sheafPullbackConstruction.sheafPullback (S.componentFunctor j) Ab.{u}
        (S.componentTopology j) S.totalTopology ⋙ S.abelianComponent i)
      (fun φ : j ⟶ i => abelianTransition S φ) (S.componentLowerShriekBiproductIso i j)
      (T.obj j)

/-- The `φ`th summand inclusion into the direct-sum formula for the restriction of the
realization is the unit followed by the derived transition. -/
theorem realizationTermComponentIso_ι (T : SimplicialDerivedSystem S)
    {n m : SimplexCategory} (φ : n ⟶ m) :
    letI : Fintype (n ⟶ m) := Fintype.ofFinite (n ⟶ m)
    Limits.biproduct.ι (fun ψ : n ⟶ m => (derivedInverseImage S ψ).obj (T.obj n)) φ ≫
        (realizationTermComponentIso S T m n).inv =
      (derivedInverseImage S φ).map
          ((S.componentLowerShriekDerivedAdjunction n).unit.app (T.obj n)) ≫
        (derivedTransition S φ).app (realizationTerm S T n) := by
  let _ : Fintype (n ⟶ m) := Fintype.ofFinite (n ⟶ m)
  simpa only [realizationTermComponentIso, derivedBiproductIso, Iso.trans_inv, Iso.symm_inv,
    Iso.app_hom, realizationTerm, Category.assoc, Limits.biproduct.ι_desc_assoc,
    NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app] using
    congr_app (derived_component_summand S φ) (T.obj n)

/-- The realization in degree `n`, shifted, is the extension by lower shriek of the shift. -/
noncomputable def realizationTermShiftIso (T : SimplicialDerivedSystem S) (n : SimplexCategory)
    (t : ℤ) :
    (shiftFunctor (DerivedCategory (Sheaf S.totalTopology Ab.{u})) t).obj
        (realizationTerm S T n) ≅
      (S.componentLowerShriekDerived n).obj
        ((shiftFunctor (DerivedCategory (Sheaf (S.componentTopology n) Ab.{u})) t).obj
          (T.obj n)) :=
  letI : (S.componentLowerShriekDerived n).CommShift ℤ := by
    dsimp only [componentLowerShriekDerived]
    infer_instance
  ((S.componentLowerShriekDerived n).commShiftIso t).symm.app (T.obj n)

/-- The derived extension by lower shriek from simplicial degree `n` is additive. -/
local instance componentLowerShriekDerived_additive (n : SimplexCategory) :
    (S.componentLowerShriekDerived n).Additive := by
  dsimp only [componentLowerShriekDerived]
  infer_instance

/-- The derived restriction to simplicial degree `n` is additive. -/
local instance derivedComponent_additive (n : SimplexCategory) :
    (S.derivedComponent n).Additive := by
  dsimp only [derivedComponent]
  infer_instance

/-- **The positively shifted morphisms between the terms of the realization vanish.** For a
cartesian system whose objects have no positively shifted self-maps, every morphism from a
positive shift of the realization in degree `i` to the realization in degree `j` is zero. -/
theorem realizationTerm_hom_zero_of_biproduct (T : SimplicialDerivedSystem S)
    (hT : SimplicialDerivedSystem.Cartesian T)
    (hHom : ∀ (k : SimplexCategory) (t : ℕ), 0 < t →
      ∀ f : (shiftFunctor (DerivedCategory (Sheaf (S.componentTopology k) Ab.{u}))
        (t : ℤ)).obj (T.obj k) ⟶ T.obj k, f = 0)
    (i j : SimplexCategory) (t : ℕ) (ht : 0 < t)
    (f : (shiftFunctor (DerivedCategory (Sheaf S.totalTopology Ab.{u})) (t : ℤ)).obj
        (realizationTerm S T i) ⟶ realizationTerm S T j) : f = 0 := by
  let _ : Fintype (j ⟶ i) := Fintype.ofFinite (j ⟶ i)
  exact hom_eq_zero_of_shifted_leftAdjoint_biproduct
    (S.componentLowerShriekDerivedAdjunction i)
    (fun φ : j ⟶ i => (derivedInverseImage S φ).obj (T.obj j))
    (T.obj i) (t : ℤ) (realizationTermComponentIso S T i j)
    (fun φ => by
      let := hT φ
      exact asIso (T.map φ))
    (hHom i t ht) (realizationTermShiftIso S T i (t : ℤ)) f

/-- The comparison of the copower of the object of the system in degree `m` with the restriction
to degree `m` of the realization: on the simplex indexed by `φ` it is the transpose of the
transition of the realization along `φ`. -/
noncomputable def realizationComponentComparison (T : SimplicialDerivedSystem S)
    (hT : SimplicialDerivedSystem.Cartesian T) (m : SimplexCategory) :
    simplexCopower (T.obj m) m ⟶ realizationSimplicial T hT ⋙ derivedComponent S m where
  app n := Limits.Sigma.desc fun φ => realizationComponentInclusion T hT φ
  naturality _ _ ψ := by
    refine Limits.Sigma.hom_ext _ _ fun φ => ?_
    simp only [simplexCopower, Limits.Sigma.ι_desc_assoc, Limits.Sigma.ι_desc, Functor.comp_map,
      realizationSimplicial]
    exact (realizationComponentInclusion_comp T hT ψ.unop φ).symm

/-- The `φ`th summand of the comparison is the transpose of the transition along `φ`. -/
theorem realizationComponentComparison_ι (T : SimplicialDerivedSystem S)
    (hT : SimplicialDerivedSystem.Cartesian T) {m : SimplexCategory} {n : SimplexCategoryᵒᵖ}
    (φ : n.unop ⟶ m) :
    Limits.Sigma.ι (fun _ : n.unop ⟶ m => T.obj m) φ ≫
        (realizationComponentComparison S T hT m).app n =
      realizationComponentInclusion T hT φ :=
  Limits.Sigma.ι_desc _ _

/-- **Stacks 0D9L, the Postnikov system of the realization.**  The complex whose term in degree
`n` is the extension by lower shriek of the object of the system in degree `n`, and whose
differential is the alternating sum of the transitions along the face maps, carries a sequential
Postnikov system: its differentials compose to zero, and all positively shifted morphisms between
its terms vanish.

This is the construction step of Stacks 0D9L.  The totalization of this Postnikov system, the
identification of its restriction to each simplicial degree with the object of the system in that
degree, and the cartesianness of the result are in
`StacksFrontier.CategoryTheory.Sites.Simplicial.CartesianDerivedOfSystem`. -/
@[stacks 0D9L "the Postnikov system of the realization complex"]
theorem nonempty_sequentialPostnikovSystem_realizationComplex (T : SimplicialDerivedSystem S)
    (hT : SimplicialDerivedSystem.Cartesian T)
    (hHom : ∀ (k : SimplexCategory) (t : ℕ), 0 < t →
      ∀ f : (shiftFunctor (DerivedCategory (Sheaf (S.componentTopology k) Ab.{u}))
        (t : ℤ)).obj (T.obj k) ⟶ T.obj k, f = 0) :
    Nonempty (Triangulated.SequentialPostnikovSystem
      (fun n : ℕ => realizationTerm S T ⦋n⦌)
      (fun n : ℕ => (realizationComplex T hT).d (n + 1) n)) :=
  Triangulated.nonempty_sequentialPostnikovSystem _ _
    (fun n => (realizationComplex T hT).d_comp_d (n + 2) (n + 1) n)
    (fun i j t ht f => realizationTerm_hom_zero_of_biproduct S T hT hHom ⦋i⦌ ⦋j⦌ t ht f)

end CategoryTheory.SimplicialSiteSituation

end
