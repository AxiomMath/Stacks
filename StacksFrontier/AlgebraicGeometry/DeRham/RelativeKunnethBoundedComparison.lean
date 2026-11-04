module

public import StacksFrontier.AlgebraicGeometry.DeRham.RelativeKunnethUnbounded
import StacksCore.Tactic.StacksAttribute

/-!
# The two relative Künneth maps of the box product agree on bounded-below complexes

Let `𝓕^•` on `X/S` and `𝓖^•` on `Y/S` be strictly bounded-below complexes whose differentials are
differential operators of finite order. Then `Tot(𝓕^• ⊠ 𝓖^•)` can be formed in two places:

* in the category of finite-order differential operators on `X ×_S Y / S`, where only finite
  coproducts exist; this is the target of `relativeBoxKunnethMap` of [Stacks, Tag 0G4B];
* over `f^{-1}𝒪_S`, where all coproducts exist; this is the target of
  `relativeBoxKunnethMapUnbounded`.

In each degree both are coproducts of the same finitely many nonzero summands `𝓕^i ⊠ 𝓖^j`. This
file identifies them and shows that the two Künneth maps differ by that identification.

## Main definitions

* `HomologicalComplex.mapBifunctorCompIso`: for an additive `G` and bounded-below `K`, `L`,
  `Tot(G ∘ F(K, L)) ≅ G(Tot(F(K, L)))`.
* `Stacks.Cohomology.BoxKunneth.boxTotalModulesIso`: the identification of the two total
  complexes of the box product.

## Main results

* `CategoryTheory.Limits.isColimitCofanMkMapOfFinite`: an additive functor preserves a
  coproduct of a family with finitely many nonzero members.
* `Stacks.Cohomology.BoxKunneth.relativeBoxKunnethMap_eq_unbounded`: **the map of
  [Stacks, Tag 0G4B] is the unbounded map followed by `Rf_*` of `boxTotalModulesIso`.**
* `Stacks.Cohomology.BoxKunneth.isIso_relativeBoxKunnethMap_iff`: so one is invertible exactly
  when the other is.

## References

* [Stacks Project, Tag 0G4B](https://stacks.math.columbia.edu/tag/0G4B)
* [Stacks Project, Tag 012Z](https://stacks.math.columbia.edu/tag/012Z)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open Stacks.DeRhamDirectImage
open Stacks.DerivedTensor.RingedSite
open AlgebraicGeometry.FiniteOrderDifferentialOperatorCategory
open Stacks.Cohomology.GlobalKunneth

universe u

namespace CategoryTheory.Limits

/-- **An additive functor carries a coproduct of a family with finitely many nonzero members to
a coproduct.** In a preadditive category such a coproduct is a finite biproduct: the identity of
its point is the finite sum of the composites of the projections with the inclusions, and an
additive functor preserves that decomposition. -/
noncomputable def isColimitCofanMkMapOfFinite {C D : Type*} [Category* C] [Category* D]
    [Preadditive C] [Preadditive D] (G : C ⥤ D) [G.Additive] {J : Type*} {f : J → C}
    (hf : {j | ¬ IsZero (f j)}.Finite) {c : Cofan f} (hc : IsColimit c) :
    IsColimit (Cofan.mk (G.obj c.pt) fun j => G.map (c.inj j)) := by
  classical
  let π : ∀ s, c.pt ⟶ f s := fun s =>
    Cofan.IsColimit.desc hc (fun t => if h : t = s then eqToHom (congrArg f h) else 0)
  have hιπ : ∀ t s, c.inj t ≫ π s = if h : t = s then eqToHom (congrArg f h) else 0 :=
    fun t s => Cofan.IsColimit.fac hc _ t
  have hsum : ∑ s ∈ hf.toFinset, π s ≫ c.inj s = 𝟙 c.pt := by
    refine Cofan.IsColimit.hom_ext hc _ _ (fun t => ?_)
    rw [Preadditive.comp_sum, Category.comp_id]
    by_cases ht : IsZero (f t)
    · exact ht.eq_of_src _ _
    · rw [Finset.sum_eq_single t]
      · rw [← Category.assoc, hιπ, dite_eq_left rfl, eqToHom_refl, Category.id_comp]
      · intro s _ hst
        rw [← Category.assoc, hιπ, dite_eq_right (fun h => hst h.symm), zero_comp]
      · exact fun h => absurd (hf.mem_toFinset.2 ht) h
  refine Cofan.IsColimit.mk _ (fun t => ∑ s ∈ hf.toFinset, G.map (π s) ≫ t.inj s) ?_ ?_
  · intro t j
    change G.map (c.inj j) ≫ _ = _
    rw [Preadditive.comp_sum]
    by_cases hj : IsZero (f j)
    · exact (G.map_isZero hj).eq_of_src _ _
    · rw [Finset.sum_eq_single j]
      · rw [← Category.assoc, ← G.map_comp, hιπ, dite_eq_left rfl, eqToHom_refl, G.map_id,
          Category.id_comp]
      · intro s _ hs
        rw [← Category.assoc, ← G.map_comp, hιπ, dite_eq_right (fun h => hs h.symm), G.map_zero,
          zero_comp]
      · exact fun h => absurd (hf.mem_toFinset.2 hj) h
  · intro t m hm
    have hm' : ∀ s, G.map (c.inj s) ≫ m = t.inj s := hm
    calc m = G.map (𝟙 c.pt) ≫ m := by rw [G.map_id, Category.id_comp]
      _ = _ := by
        rw [← hsum, G.map_sum, Preadditive.sum_comp]
        refine Finset.sum_congr rfl (fun s _ => ?_)
        rw [G.map_comp, Category.assoc, hm']

end CategoryTheory.Limits

namespace HomologicalComplex

/-- The index map `(p, q) ↦ p + q` of the total complex of a bicomplex of `ℤ`-indexed cochain
complexes. -/
abbrev totalIndex : ℤ × ℤ → ℤ :=
  ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)

/-- The bigraded object `(p, q) ↦ F(Kᵖ, L^q)` whose coproducts along `totalIndex` are the terms of
`Tot(F(K, L))`. -/
abbrev mapBifunctorGraded {C₁ C₂ D : Type*} [Category* C₁] [Category* C₂] [Category* D]
    [HasZeroMorphisms C₁] [HasZeroMorphisms C₂] [HasZeroMorphisms D]
    (K : CochainComplex C₁ ℤ) (L : CochainComplex C₂ ℤ) (F : C₁ ⥤ C₂ ⥤ D)
    [F.PreservesZeroMorphisms] [∀ X, (F.obj X).PreservesZeroMorphisms] :
    GradedObject (ℤ × ℤ) D :=
  (((F.mapBifunctorHomologicalComplex (ComplexShape.up ℤ) (ComplexShape.up ℤ)).obj K).obj
    L).toGradedObject

section

variable {C₁ C₂ C D : Type*} [Category* C₁] [Category* C₂] [Category* C] [Category* D]
  [HasZeroMorphisms C₁] [HasZeroMorphisms C₂] [Preadditive C] [Preadditive D]
  (F : C₁ ⥤ C₂ ⥤ C) [F.PreservesZeroMorphisms] [∀ X, (F.obj X).PreservesZeroMorphisms]
  (G : C ⥤ D) [G.Additive]
  [(F ⋙ (Functor.whiskeringRight C₂ C D).obj G).PreservesZeroMorphisms]
  [∀ X, ((F ⋙ (Functor.whiskeringRight C₂ C D).obj G).obj X).PreservesZeroMorphisms]
  (K : CochainComplex C₁ ℤ) (L : CochainComplex C₂ ℤ)

section

variable [HasMapBifunctor K L F (ComplexShape.up ℤ)]
  [HasMapBifunctor K L (F ⋙ (Functor.whiskeringRight C₂ C D).obj G) (ComplexShape.up ℤ)]

omit [HasMapBifunctor K L F (ComplexShape.up ℤ)]
  [HasMapBifunctor K L (F ⋙ (Functor.whiskeringRight C₂ C D).obj G) (ComplexShape.up ℤ)] in
/-- In each total degree, only finitely many summands of `Tot(F(K, L))` are nonzero when `K` and
`L` are strictly bounded below. -/
theorem finite_not_isZero_mapObjFun (n₁ n₂ : ℤ) [K.IsStrictlyGE n₁] [L.IsStrictlyGE n₂] (n : ℤ) :
    {x : ↑(totalIndex ⁻¹' {n}) |
      ¬ IsZero ((mapBifunctorGraded K L F).mapObjFun totalIndex n x)}.Finite := by
  have key : ∀ p q : ℤ, IsZero (K.X p) → IsZero ((F.obj (K.X p)).obj (L.X q)) := by
    intro p q h
    rw [IsZero.iff_id_eq_zero, ← NatTrans.id_app, ← F.map_id,
      (IsZero.iff_id_eq_zero (K.X p)).1 h, F.map_zero]
    rfl
  have hS : ((fun p : ℤ => (p, n - p)) '' Set.Icc n₁ (n - n₂)).Finite :=
    (Set.finite_Icc n₁ (n - n₂)).image _
  refine (hS.preimage Subtype.val_injective.injOn).subset ?_
  rintro ⟨⟨p, q⟩, hpq⟩ hz
  have hpq' : p + q = n := hpq
  have hp : n₁ ≤ p := by
    by_contra hp
    exact hz (key p q (K.isZero_of_isStrictlyGE n₁ p (by lia)))
  have hq : n₂ ≤ q := by
    by_contra hq
    exact hz (Functor.map_isZero (F.obj (K.X p)) (L.isZero_of_isStrictlyGE n₂ q (by lia)))
  exact ⟨p, ⟨hp, by lia⟩, by simp [show n - p = q by lia]⟩

/-- **An additive functor commutes with a bounded-below total complex, in each degree**:
`Tot(G ∘ F(K, L))ⁿ ≅ G(Tot(F(K, L))ⁿ)`, both being coproducts of the same finitely many nonzero
summands. -/
noncomputable def mapBifunctorCompXIso (n₁ n₂ : ℤ) [K.IsStrictlyGE n₁] [L.IsStrictlyGE n₂] (n : ℤ) :
    (mapBifunctor K L (F ⋙ (Functor.whiskeringRight C₂ C D).obj G) (ComplexShape.up ℤ)).X n ≅
      G.obj ((mapBifunctor K L F (ComplexShape.up ℤ)).X n) :=
  IsColimit.coconePointUniqueUpToIso
    (coproductIsCoproduct ((mapBifunctorGraded K L
      (F ⋙ (Functor.whiskeringRight C₂ C D).obj G)).mapObjFun totalIndex n))
    (isColimitCofanMkMapOfFinite G (finite_not_isZero_mapObjFun F K L n₁ n₂ n)
      (coproductIsCoproduct ((mapBifunctorGraded K L F).mapObjFun totalIndex n)))

/-- The isomorphism `mapBifunctorCompXIso` carries the inclusion of the summand of index `(i, j)`
of `Tot(G ∘ F(K, L))ⁿ` to the image under `G` of the inclusion of the same summand of
`Tot(F(K, L))ⁿ`. -/
@[reassoc]
theorem ι_mapBifunctorCompXIso_hom (n₁ n₂ : ℤ) [K.IsStrictlyGE n₁] [L.IsStrictlyGE n₂] (i j n : ℤ)
    (h : i + j = n) :
    ιMapBifunctor K L (F ⋙ (Functor.whiskeringRight C₂ C D).obj G) (ComplexShape.up ℤ) i j n h ≫
        (mapBifunctorCompXIso F G K L n₁ n₂ n).hom =
      G.map (ιMapBifunctor K L F (ComplexShape.up ℤ) i j n h) :=
  IsColimit.comp_coconePointUniqueUpToIso_hom
    (coproductIsCoproduct ((mapBifunctorGraded K L
      (F ⋙ (Functor.whiskeringRight C₂ C D).obj G)).mapObjFun totalIndex n))
    (isColimitCofanMkMapOfFinite G (finite_not_isZero_mapObjFun F K L n₁ n₂ n)
      (coproductIsCoproduct ((mapBifunctorGraded K L F).mapObjFun totalIndex n)))
    ⟨⟨(i, j), h⟩⟩

/-- **An additive functor commutes with a bounded-below total complex**:
`Tot(G ∘ F(K, L)) ≅ G(Tot(F(K, L)))` as complexes. -/
noncomputable def mapBifunctorCompIso (n₁ n₂ : ℤ) [K.IsStrictlyGE n₁] [L.IsStrictlyGE n₂] :
    mapBifunctor K L (F ⋙ (Functor.whiskeringRight C₂ C D).obj G) (ComplexShape.up ℤ) ≅
      (G.mapHomologicalComplex (ComplexShape.up ℤ)).obj (mapBifunctor K L F (ComplexShape.up ℤ)) :=
  Hom.isoOfComponents (fun n => mapBifunctorCompXIso F G K L n₁ n₂ n) (by
    rintro n _ rfl
    refine mapBifunctor.hom_ext (fun i j h => ?_)
    have h' : i + j = n := h
    change _ ≫ _ ≫ G.map _ = _
    rw [ι_mapBifunctorCompXIso_hom_assoc,
      Functor.map_comp_eq_add_units_smul G _ _ _ _ _ _ _ (ιMapBifunctor_d_up_ℤ K L F i j n h'),
      ← Category.assoc, ιMapBifunctor_d_up_ℤ K L _ i j n h', Preadditive.add_comp,
      Category.assoc, ι_mapBifunctorCompXIso_hom, Linear.units_smul_comp, Category.assoc,
      ι_mapBifunctorCompXIso_hom]
    rfl)

/-- In degree `n`, the isomorphism `mapBifunctorCompIso` carries the inclusion of the summand of
index `(i, j)` of `Tot(G ∘ F(K, L))` to the image under `G` of the inclusion of the same summand
of `Tot(F(K, L))`. -/
@[reassoc]
theorem ι_mapBifunctorCompIso_hom_f (n₁ n₂ : ℤ) [K.IsStrictlyGE n₁] [L.IsStrictlyGE n₂] (i j n : ℤ)
    (h : i + j = n) :
    ιMapBifunctor K L (F ⋙ (Functor.whiskeringRight C₂ C D).obj G) (ComplexShape.up ℤ) i j n h ≫
        (mapBifunctorCompIso F G K L n₁ n₂).hom.f n =
      G.map (ιMapBifunctor K L F (ComplexShape.up ℤ) i j n h) :=
  ι_mapBifunctorCompXIso_hom F G K L n₁ n₂ i j n h

end

end

end HomologicalComplex

namespace CategoryTheory

/-- Over variables: `ι ≫ x = r ≫ ι'` and `ι' ≫ y = t` give `ι ≫ x ≫ y = r ≫ t`. -/
theorem comp_comp_eq_of_comp_eq_comp {C : Type*} [Category* C] {P Q R T E : C} (ι : P ⟶ Q)
    (x : Q ⟶ R) (y : R ⟶ T) (r : P ⟶ E) (ι' : E ⟶ R) (t : E ⟶ T) (h₁ : ι ≫ x = r ≫ ι')
    (h₂ : ι' ≫ y = t) : ι ≫ x ≫ y = r ≫ t := by
  rw [reassoc_of% h₁, h₂]

/-- Over variables: the image under `R` of a four-step composite ending in `Q.map (x ≫ y)` is the
image of the composite ending in `Q.map x`, followed by `R.map (Q.map y)`. -/
theorem Functor.map_comp_four_map_comp {C D E : Type*} [Category* C] [Category* D] [Category* E]
    (R : D ⥤ E) (Q : C ⥤ D) {Z : E} {B₀ B₁ B₂ : D} {X₀ X₁ X₂ : C}
    (k : Z ⟶ R.obj B₀) (f₁ : B₀ ⟶ B₁) (f₂ : B₁ ⟶ B₂) (f₃ : B₂ ⟶ Q.obj X₀) (x : X₀ ⟶ X₁)
    (y : X₁ ⟶ X₂) :
    k ≫ R.map (f₁ ≫ f₂ ≫ f₃ ≫ Q.map (x ≫ y)) =
      (k ≫ R.map (f₁ ≫ f₂ ≫ f₃ ≫ Q.map x)) ≫ R.map (Q.map y) := by
  simp only [Functor.map_comp, Category.assoc]

end CategoryTheory

namespace Stacks.Cohomology.BoxKunneth

attribute [local instance 2000] HasDerivedCategory.standard

variable {X Y S : Scheme.{u}} (a : X ⟶ S) (b : Y ⟶ S)
  (K : CochainComplex (FiniteOrderDifferentialOperatorCategory a) ℤ)
  (L : CochainComplex (FiniteOrderDifferentialOperatorCategory b) ℤ)
  (n₁ n₂ : ℤ) [K.IsStrictlyGE n₁] [L.IsStrictlyGE n₂]

/-- **The two total complexes of the box product agree on bounded-below complexes**: the total
complex formed over `f^{-1}𝒪_S` is the one formed in the category of finite-order differential
operators, read over `f^{-1}𝒪_S`. In each degree both are coproducts of the same finitely many
nonzero summands `𝓕^i ⊠ 𝓖^j`. -/
noncomputable def boxTotalModulesIso :
    HomologicalComplex.mapBifunctor K L (boxProductRelativeCurried a b) (ComplexShape.up ℤ) ≅
      boxTotalModules a b K L n₁ n₂ :=
  haveI := hasMapBifunctor_up_ℤ K L n₁ n₂
  haveI : (boxProductCurried a b ⋙ (Functor.whiskeringRight _ _ _).obj
      (toInverseImageModules (pullback.fst a b ≫ a))).PreservesZeroMorphisms :=
    boxProductRelativeCurried_preservesZeroMorphisms a b
  haveI : ∀ F, ((boxProductCurried a b ⋙ (Functor.whiskeringRight _ _ _).obj
      (toInverseImageModules (pullback.fst a b ≫ a))).obj F).PreservesZeroMorphisms :=
    boxProductRelativeCurried_obj_preservesZeroMorphisms a b
  haveI : HomologicalComplex.HasMapBifunctor K L (boxProductCurried a b ⋙
      (Functor.whiskeringRight _ _ _).obj (toInverseImageModules (pullback.fst a b ≫ a)))
      (ComplexShape.up ℤ) :=
    (inferInstance : HomologicalComplex.HasMapBifunctor K L (boxProductRelativeCurried a b)
      (ComplexShape.up ℤ))
  HomologicalComplex.mapBifunctorCompIso (boxProductCurried a b)
    (toInverseImageModules (pullback.fst a b ≫ a)) K L n₁ n₂

/-- On the summand of degree `(i, j)` the comparison of the two total complexes is the inclusion
of the summand of the total complex of differential operators, read over `f^{-1}𝒪_S`. -/
theorem ι_boxTotalModulesIso_hom_f (i j n : ℤ) (h : i + j = n) :
    HomologicalComplex.ιMapBifunctor K L (boxProductRelativeCurried a b) (ComplexShape.up ℤ)
        i j n h ≫ (boxTotalModulesIso a b K L n₁ n₂).hom.f n =
      boxTotalι a b K L n₁ n₂ i j n h :=
  have := hasMapBifunctor_up_ℤ K L n₁ n₂
  have : (boxProductCurried a b ⋙ (Functor.whiskeringRight _ _ _).obj
      (toInverseImageModules (pullback.fst a b ≫ a))).PreservesZeroMorphisms :=
    boxProductRelativeCurried_preservesZeroMorphisms a b
  have : ∀ F, ((boxProductCurried a b ⋙ (Functor.whiskeringRight _ _ _).obj
      (toInverseImageModules (pullback.fst a b ≫ a))).obj F).PreservesZeroMorphisms :=
    boxProductRelativeCurried_obj_preservesZeroMorphisms a b
  have : HomologicalComplex.HasMapBifunctor K L (boxProductCurried a b ⋙
      (Functor.whiskeringRight _ _ _).obj (toInverseImageModules (pullback.fst a b ≫ a)))
      (ComplexShape.up ℤ) :=
    (inferInstance : HomologicalComplex.HasMapBifunctor K L (boxProductRelativeCurried a b)
      (ComplexShape.up ℤ))
  HomologicalComplex.ι_mapBifunctorCompIso_hom_f (boxProductCurried a b)
    (toInverseImageModules (pullback.fst a b ≫ a)) K L n₁ n₂ i j n h


/-- **The step-(5) comparison is step (5) for unbounded complexes followed by the comparison of the
two total complexes**: a datum of `Stacks.Cohomology.BoxKunneth.BoxTotalComparison` built from
`boxTotalComplexComparison` and `boxTotalModulesIso`. -/
noncomputable def boxTotalComparisonOfUnbounded : BoxTotalComparison a b K L n₁ n₂ where
  hom := boxTotalComplexComparison a b K L ≫ (boxTotalModulesIso a b K L n₁ n₂).hom
  ι_hom i j n h := comp_comp_eq_of_comp_eq_comp _ _ _ _ _ _
    (ι_boxTotalComplexComparison a b K L i j n h) (ι_boxTotalModulesIso_hom_f a b K L n₁ n₂ i j n h)

/-- **The relative Künneth map of [Stacks, Tag 0G4B] is the unbounded one followed by the
comparison of the two total complexes.** For strictly bounded-below `𝓕^•` and `𝓖^•`, the map
`relativeBoxKunnethMap`, whose target total complex is formed in the category of finite-order
differential operators, is `relativeBoxKunnethMapUnbounded`, whose target total complex is formed
over `f^{-1}𝒪_S`, followed by `Rf_*` of the isomorphism `boxTotalModulesIso` between the two. -/
theorem relativeBoxKunnethMap_eq_unbounded :
    relativeBoxKunnethMap a b K L n₁ n₂ =
      relativeBoxKunnethMapUnbounded a b K L ≫
        (derivedPushforward.{u, u + 1, u + 1}
            (inverseImageBaseProjection (pullback.fst a b ≫ a))).map
          (DerivedCategory.Q.map (boxTotalModulesIso a b K L n₁ n₂).hom) := by
  rw [relativeBoxKunnethMap_unique a b K L n₁ n₂ (boxTotalComparisonOfUnbounded a b K L n₁ n₂)]
  exact Functor.map_comp_four_map_comp _ DerivedCategory.Q _ _ _ _ _ _

/-- **The relative Künneth map of [Stacks, Tag 0G4B] is invertible exactly when the unbounded one
is**, the two differing by an isomorphism. -/
theorem isIso_relativeBoxKunnethMap_iff :
    IsIso (relativeBoxKunnethMap a b K L n₁ n₂) ↔
      IsIso (relativeBoxKunnethMapUnbounded a b K L) := by
  rw [relativeBoxKunnethMap_eq_unbounded]
  have : IsIso ((derivedPushforward.{u, u + 1, u + 1}
      (inverseImageBaseProjection (pullback.fst a b ≫ a))).map
        (DerivedCategory.Q.map (boxTotalModulesIso a b K L n₁ n₂).hom)) :=
    ((derivedPushforward.{u, u + 1, u + 1}
      (inverseImageBaseProjection (pullback.fst a b ≫ a))).mapIso
        (DerivedCategory.Q.mapIso (boxTotalModulesIso a b K L n₁ n₂))).isIso_hom
  constructor
  · intro h
    exact @IsIso.of_isIso_comp_right _ _ _ _ _ _ _ this h
  · intro h
    exact @IsIso.comp_isIso _ _ _ _ _ _ _ h this

end Stacks.Cohomology.BoxKunneth
