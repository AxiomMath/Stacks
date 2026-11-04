module

public import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
public import Mathlib.AlgebraicTopology.ExtraDegeneracy
public import StacksFrontier.Algebra.Homology.DerivedCategory.Coproducts
public import StacksFrontier.AlgebraicGeometry.Simplicial.DerivedCocycleSystem
public import StacksFrontier.CategoryTheory.Sites.Simplicial.AbelianTransitionBridgeCocontinuous
public import StacksFrontier.CategoryTheory.Sites.Simplicial.AssociatedDerivedSystem
public import StacksFrontier.CategoryTheory.Sites.Simplicial.ComponentDerivedAdjunction
public import StacksFrontier.CategoryTheory.Sites.Simplicial.IntegerResolution

/-!
# Realizing a cartesian simplicial system of the derived category

Let `S` be a simplicial-site situation and `T` a cartesian simplicial system of the derived
categories of its components, in the sense of Stacks 0D9G: objects `T n` of
`D(Sh(C_n, Ab))` together with isomorphisms `g_φ^{-1} (T m) ≅ T n` satisfying the cocycle
condition.  The object of the derived category of the total site that induces `T` is the
totalization of the complex whose term in degree `n` is `g_{n!} (T n)`, the extension by lower
shriek of the object in degree `n`.  This file builds that complex and the comparisons that
identify its terms.

The transition of the complex along a simplex map `φ : [m] ⟶ [n]` is the transpose, under
`g_{n!} ⊣ g_n^{-1}`, of the inverse of the transition of `T` followed by the unit and the
transition of Stacks 07TF; the resulting simplicial object of the derived category has the
alternating face map complex of Stacks 09WI as its associated complex, so that the vanishing of
the composition of two differentials is automatic.

The restriction of a term of the complex to one simplicial degree is computed by the sum formula
of Stacks 09WG: `g_i^{-1} g_{j!}` is the direct sum over the simplex maps `[j] ⟶ [i]` of the
inverse images along the transitions.  That formula is stated here as a direct sum of the inverse
images of Stacks 04JC, which is the form in which the derived category sees it, and its summand
inclusions are identified with the canonical maps.

All names below are in the namespace `CategoryTheory.SimplicialSiteSituation` unless written
with the prefix `CategoryTheory`.

## Main definitions

* `CategoryTheory.derivedBiproductIso`: the derived functor of a finite direct sum of exact
  functors is the direct sum of their derived functors.
* `realizationTerm` and `realizationTermMap`: the terms and the transitions of the realization.
* `realizationSimplicial` and `realizationComplex`: the realization as a simplicial object of the
  derived category, and its alternating face map complex.
* `componentLowerShriekBiproductIso`: the sum formula of Stacks 09WG as a direct sum of the
  inverse images of Stacks 04JC.
* `CategoryTheory.simplexCopowerExtraDegeneracy`: the copower of an object by the simplices of a
  standard simplex is an augmented simplicial object with an extra degeneracy.

## Main results

* `sigma_ι_comp_componentLowerShriekRestrictionIsoCoproduct_inv_eq_leg`: the summand inclusions
  of the sum formula of Stacks 09WG are the canonical maps, in both cases of Stacks 09WE.
* `componentLowerShriekBiproductIso_ι`: the same statement for the direct-sum form, with the
  summands read as the inverse images of Stacks 04JC.
* `CategoryTheory.hom_eq_zero_of_shifted_leftAdjoint_biproduct`: the vanishing of the positively
  shifted self-maps of the objects of the system propagates to the terms of the realization.

## References

* [Stacks Project, Tag 04JC](https://stacks.math.columbia.edu/tag/04JC)
* [Stacks Project, Tag 07TF](https://stacks.math.columbia.edu/tag/07TF)
* [Stacks Project, Tag 09WE](https://stacks.math.columbia.edu/tag/09WE)
* [Stacks Project, Tag 09WG](https://stacks.math.columbia.edu/tag/09WG)
* [Stacks Project, Tag 09WI](https://stacks.math.columbia.edu/tag/09WI)
* [Stacks Project, Tag 0D9G](https://stacks.math.columbia.edu/tag/0D9G)
* [Stacks Project, Tag 0D9L](https://stacks.math.columbia.edu/tag/0D9L)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
open CategoryTheory.SimplicialSiteSituation
open scoped Simplicial

universe v u v₁ v₂ u₁ u₂ w₁ w₂

namespace CategoryTheory


section Vanishing

/-- If every morphism `A' ⟶ B'` vanishes, so does every morphism `A ⟶ B`, for `A ≅ A'` and
`B ≅ B'`. -/
theorem hom_eq_zero_of_iso {C : Type*} [Category C] [Preadditive C] {A A' B B' : C}
    (eA : A ≅ A') (eB : B ≅ B') (h : ∀ f : A' ⟶ B', f = 0) (f : A ⟶ B) : f = 0 := by
  calc
    f = eA.hom ≫ (eA.inv ≫ f ≫ eB.hom) ≫ eB.inv := by simp
    _ = 0 := by rw [h (eA.inv ≫ f ≫ eB.hom)]; simp

/-- A morphism out of a coproduct vanishes if every morphism out of every summand does. -/
theorem hom_eq_zero_of_coproduct {C : Type*} [Category C] [Preadditive C]
    {ι : Type*} (F : ι → C) [HasCoproduct F] {Y : C}
    (h : ∀ i, ∀ f : F i ⟶ Y, f = 0) (f : ∐ F ⟶ Y) : f = 0 := by
  refine Sigma.hom_ext f 0 fun i => ?_
  rw [h i (Sigma.ι F i ≫ f)]
  simp

/-- A morphism into a biproduct vanishes if every morphism into every summand does. -/
theorem hom_eq_zero_into_biproduct {C : Type*} [Category C] [HasZeroMorphisms C]
    {ι : Type*} (F : ι → C) [HasBiproduct F] {X : C}
    (h : ∀ i, ∀ f : X ⟶ F i, f = 0) (f : X ⟶ ⨁ F) : f = 0 := by
  refine biproduct.hom_ext _ _ fun i => ?_
  rw [h i (f ≫ biproduct.π F i)]
  simp

/-- If every morphism `A[t] ⟶ A` vanishes, so does every morphism `A[t] ⟶ ⨁ F` into a biproduct
of copies of `A`. -/
theorem hom_eq_zero_of_shifted_biproduct {C : Type*} [Category C] [Preadditive C] [HasShift C ℤ]
    {ι : Type*} (F : ι → C) [HasBiproduct F] (A : C) (t : ℤ) (e : ∀ i, F i ≅ A)
    (h : ∀ f : (shiftFunctor C t).obj A ⟶ A, f = 0)
    (f : (shiftFunctor C t).obj A ⟶ ⨁ F) : f = 0 :=
  hom_eq_zero_into_biproduct F
    (fun i g => hom_eq_zero_of_iso (Iso.refl _) (e i) h g) f

/-- For an adjunction `L ⊣ R` with `R(B) ≅ ⨁ F` a biproduct of copies of `A`, if every morphism
`A[t] ⟶ A` vanishes, so does every morphism `L(A[t]) ⟶ B`. -/
theorem hom_eq_zero_of_leftAdjoint_biproduct {C : Type u₁} {D : Type u₂}
    [Category.{v₁} C] [Category.{v₂} D] [Preadditive C] [Preadditive D] [HasShift C ℤ]
    {L : C ⥤ D} {R : D ⥤ C} [L.Additive] [R.Additive] (adj : L ⊣ R)
    {ι : Type*} (F : ι → C) [HasBiproduct F] (A : C) (t : ℤ)
    {B : D} (e : R.obj B ≅ ⨁ F) (eF : ∀ i, F i ≅ A)
    (h : ∀ f : (shiftFunctor C t).obj A ⟶ A, f = 0)
    (f : L.obj ((shiftFunctor C t).obj A) ⟶ B) : f = 0 := by
  refine (adj.homEquiv ((shiftFunctor C t).obj A) B).injective ?_
  have hz := hom_eq_zero_of_shifted_biproduct F A t eF h
    (adj.homEquiv ((shiftFunctor C t).obj A) B f ≫ e.hom)
  have hzero : adj.homEquiv _ _ f = 0 := by
    refine (cancel_mono e.hom).1 ?_
    simpa using hz
  refine hzero.trans ?_
  simp [Adjunction.homEquiv_unit]

/-- For an adjunction `L ⊣ R` with `R(B) ≅ ⨁ F` a biproduct of copies of `A`, and an
isomorphism `(L A)[t] ≅ L(A[t])`, if every morphism `A[t] ⟶ A` vanishes, so does every morphism
`(L A)[t] ⟶ B`. -/
theorem hom_eq_zero_of_shifted_leftAdjoint_biproduct {C : Type u₁} {D : Type u₂}
    [Category.{v₁} C] [Category.{v₂} D] [Preadditive C] [Preadditive D]
    [HasShift C ℤ] [HasShift D ℤ]
    {L : C ⥤ D} {R : D ⥤ C} [L.Additive] [R.Additive] (adj : L ⊣ R)
    {ι : Type*} (F : ι → C) [HasBiproduct F] (A : C) (t : ℤ)
    {B : D} (e : R.obj B ≅ ⨁ F) (eF : ∀ i, F i ≅ A)
    (h : ∀ g : (shiftFunctor C t).obj A ⟶ A, g = 0)
    (shiftIso : (shiftFunctor D t).obj (L.obj A) ≅ L.obj ((shiftFunctor C t).obj A))
    (f : (shiftFunctor D t).obj (L.obj A) ⟶ B) : f = 0 := by
  have hz := hom_eq_zero_of_leftAdjoint_biproduct adj F A t e eF h (shiftIso.inv ≫ f)
  exact (cancel_epi shiftIso.inv).1 (by simpa using hz)

/-- **A shifted morphism out of the image of a left adjoint vanishes as soon as the corresponding
`Hom`-group across the adjunction does.** Transposing along `L ⊣ R` identifies the maps
`L(A[t]) ⟶ B` with the maps `A[t] ⟶ R(B)`, and the given isomorphism moves the shift inside `L`;
so the vanishing of the second group forces the vanishing of a map `(L A)[t] ⟶ B`. -/
theorem hom_eq_zero_of_shifted_leftAdjoint {C : Type u₁} {D : Type u₂}
    [Category.{v₁} C] [Category.{v₂} D] [Preadditive C] [Preadditive D]
    [HasShift C ℤ] [HasShift D ℤ] {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)
    (A : C) (t : ℤ) {B : D}
    (shiftIso : (shiftFunctor D t).obj (L.obj A) ≅ L.obj ((shiftFunctor C t).obj A))
    (h : ∀ v : (shiftFunctor C t).obj A ⟶ R.obj B, v = 0)
    (u : (shiftFunctor D t).obj (L.obj A) ⟶ B) : u = 0 :=
  (cancel_epi shiftIso.inv).1
    (((adj.homEquiv _ _).injective ((h _).trans (h _).symm)).trans comp_zero.symm)

/-- **A morphism out of the image of a left adjoint is annihilated by any morphism whose image
under the right adjoint vanishes.** The transpose of `a ≫ b` along `L ⊣ R` is the transpose of
`a` followed by `R(b)`, so it is zero as soon as `R(b)` is; and the transposition is injective. -/
theorem comp_eq_zero_of_leftAdjoint {C : Type u₁} {D : Type u₂}
    [Category.{v₁} C] [Category.{v₂} D] [Preadditive C] [Preadditive D]
    {L : C ⥤ D} {R : D ⥤ C} [R.PreservesZeroMorphisms] (adj : L ⊣ R) {A : C} {B B' : D}
    (a : L.obj A ⟶ B) {b : B ⟶ B'} (hb : R.map b = 0) : a ≫ b = 0 := by
  refine (adj.homEquiv A B').injective ?_
  simp [Adjunction.homEquiv_unit, Functor.map_comp, hb]

end Vanishing

section Biproducts

/-- The sum of the composites `π i ≫ ι i` over the summands of a finite biproduct is the
identity. -/
theorem biproduct_total {C : Type*} [Category C] [Preadditive C]
    {ι : Type*} [Fintype ι] (L : ι → C) [HasBiproduct L] :
    ∑ i, biproduct.π L i ≫ biproduct.ι L i = 𝟙 (⨁ L) := by
  classical
  refine biproduct.hom_ext' _ _ fun i => ?_
  simp [Preadditive.comp_sum, biproduct.ι_π_assoc, dite_comp]

/-- `biproduct.lift f ≫ biproduct.desc g` is the sum of the composites `f i ≫ g i`. -/
theorem biproduct_lift_desc {C : Type*} [Category C] [Preadditive C]
    {ι : Type*} [Fintype ι] {L : ι → C} [HasBiproduct L] {X Y : C}
    (f : ∀ i, X ⟶ L i) (g : ∀ i, L i ⟶ Y) :
    biproduct.lift f ≫ biproduct.desc g = ∑ i, f i ≫ g i := by
  calc
    _ = biproduct.lift f ≫ (∑ i, biproduct.π L i ≫ biproduct.ι L i) ≫
        biproduct.desc g := by rw [biproduct_total]; simp
    _ = _ := by simp [Preadditive.comp_sum, Preadditive.sum_comp]

end Biproducts

section DerivedNatTrans

variable {A : Type u₁} [Category.{v₁} A] [Abelian A] [HasDerivedCategory.{w₁} A]
  {B : Type u₂} [Category.{v₂} B] [Abelian B] [HasDerivedCategory.{w₂} B]
  (F G H : A ⥤ B) [F.Additive] [G.Additive] [H.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  [PreservesFiniteLimits H] [PreservesFiniteColimits H]

/-- The derived transformation at `Q X` is the image under `Q` of the transformation of complexes
induced by `α`, conjugated by the factorization isomorphisms of the derived functors. -/
theorem derivedNatTrans_app_Q' (α : F ⟶ G) (X : CochainComplex A ℤ) :
    (derivedNatTrans F G α).app (DerivedCategory.Q.obj X) =
      F.mapDerivedCategoryFactors.hom.app X ≫
        DerivedCategory.Q.map
          ((NatTrans.mapHomologicalComplex α (ComplexShape.up ℤ)).app X) ≫
        G.mapDerivedCategoryFactors.inv.app X := by
  refine (cancel_mono (G.mapDerivedCategoryFactors.hom.app X)).1 ?_
  refine Eq.trans (derivedNatTrans_app_Q F G α X) ?_
  simp

/-- The derived transformation of the identity is the identity. -/
theorem derivedNatTrans_id : derivedNatTrans F F (𝟙 F) = 𝟙 F.mapDerivedCategory := by
  refine Localization.natTrans_ext DerivedCategory.Q
    (HomologicalComplex.quasiIso A (ComplexShape.up ℤ)) fun X => ?_
  simp [derivedNatTrans_app_Q', NatTrans.mapHomologicalComplex_id]

/-- The derived transformation of a composite is the composite of the derived transformations. -/
theorem derivedNatTrans_comp (α : F ⟶ G) (β : G ⟶ H) :
    derivedNatTrans F H (α ≫ β) = derivedNatTrans F G α ≫ derivedNatTrans G H β := by
  refine Localization.natTrans_ext DerivedCategory.Q
    (HomologicalComplex.quasiIso A (ComplexShape.up ℤ)) fun X => ?_
  simp [derivedNatTrans_app_Q', NatTrans.mapHomologicalComplex_comp, Category.assoc]

/-- The derived transformation of a sum is the sum of the derived transformations. -/
theorem derivedNatTrans_add (α β : F ⟶ G) :
    derivedNatTrans F G (α + β) = derivedNatTrans F G α + derivedNatTrans F G β := by
  refine Localization.natTrans_ext DerivedCategory.Q
    (HomologicalComplex.quasiIso A (ComplexShape.up ℤ)) fun X => ?_
  have h : (NatTrans.mapHomologicalComplex (α + β) (ComplexShape.up ℤ)).app X =
      (NatTrans.mapHomologicalComplex α (ComplexShape.up ℤ)).app X +
        (NatTrans.mapHomologicalComplex β (ComplexShape.up ℤ)).app X :=
    HomologicalComplex.hom_ext _ _ fun _ => rfl
  simp only [derivedNatTrans_app_Q', h, Functor.map_add,
    Preadditive.add_comp, Preadditive.comp_add, NatTrans.app_add]

/-- The derived transformation of zero is zero. -/
theorem derivedNatTrans_zero : derivedNatTrans F G (0 : F ⟶ G) = 0 := by
  simpa only [add_zero, left_eq_add] using derivedNatTrans_add F G (0 : F ⟶ G) 0

/-- The additive map induced on derived functors by a transformation of exact functors. -/
noncomputable def derivedNatTransAddHom :
    (F ⟶ G) →+ (F.mapDerivedCategory ⟶ G.mapDerivedCategory) where
  toFun := derivedNatTrans F G
  map_zero' := derivedNatTrans_zero F G
  map_add' := derivedNatTrans_add F G

/-- **The derived functor of a finite direct sum of exact functors is the direct sum of their
derived functors.** The comparison is given by the derived transformations of the projections
and of the inclusions. -/
noncomputable def derivedBiproductIso {ι : Type*} [Fintype ι]
    (L : ι → A ⥤ B) [HasBiproduct L] [∀ i, (L i).Additive]
    [∀ i, PreservesFiniteLimits (L i)] [∀ i, PreservesFiniteColimits (L i)]
    (e : F ≅ ⨁ L) (K : DerivedCategory A) :
    F.mapDerivedCategory.obj K ≅ ⨁ fun i => (L i).mapDerivedCategory.obj K where
  hom := biproduct.lift fun i => (derivedNatTrans F (L i) (e.hom ≫ biproduct.π L i)).app K
  inv := biproduct.desc fun i => (derivedNatTrans (L i) F (biproduct.ι L i ≫ e.inv)).app K
  hom_inv_id := by
    rw [biproduct_lift_desc]
    simp only [← NatTrans.comp_app, ← derivedNatTrans_comp, Category.assoc]
    change (∑ i, (derivedNatTransAddHom F F
      (e.hom ≫ biproduct.π L i ≫ biproduct.ι L i ≫ e.inv)).app K) = _
    rw [← NatTrans.app_sum, ← _root_.map_sum]
    have hsum : ∑ i, e.hom ≫ biproduct.π L i ≫ biproduct.ι L i ≫ e.inv = 𝟙 F := by
      rw [← Preadditive.comp_sum]
      simp only [← Category.assoc]
      rw [← Preadditive.sum_comp, biproduct_total]
      simp
    rw [hsum]
    exact congr_app (derivedNatTrans_id F) K
  inv_hom_id := by
    refine biproduct.hom_ext' _ _ fun i => biproduct.hom_ext _ _ fun j => ?_
    simp only [Category.assoc, biproduct.ι_desc_assoc, biproduct.lift_π, Category.id_comp]
    rw [← NatTrans.comp_app, ← derivedNatTrans_comp]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    by_cases h : i = j
    · subst j
      simp only [biproduct.ι_π_self, derivedNatTrans_id, NatTrans.id_app]
    · simp only [biproduct.ι_π_ne _ h, derivedNatTrans_zero, NatTrans.app_zero]

end DerivedNatTrans

section Coproducts

/-- A functor preserving the coproducts of the image of an essentially surjective functor
preserves coproducts. -/
theorem preservesCoproducts_of_comp {C D E : Type*} [Category C] [Category D] [Category E]
    {I : Type*} [HasColimitsOfShape (Discrete I) C]
    (Q : C ⥤ D) [Q.EssSurj] (F : D ⥤ E)
    [PreservesColimitsOfShape (Discrete I) Q]
    [PreservesColimitsOfShape (Discrete I) (Q ⋙ F)] :
    PreservesColimitsOfShape (Discrete I) F := by
  constructor
  intro X
  let Y := Discrete.functor fun i : I => Q.objPreimage (X.obj ⟨i⟩)
  let e : Y ⋙ Q ≅ X := Discrete.natIso fun i => Q.objObjPreimageIso (X.obj i)
  have : PreservesColimit (Y ⋙ Q) F :=
    preservesColimit_of_preserves_colimit_cocone
      (isColimitOfPreserves Q (colimit.isColimit Y))
      (isColimitOfPreserves (Q ⋙ F) (colimit.isColimit Y))
  exact preservesColimit_of_iso_diagram F e

/-- An exact functor preserving countable direct sums induces a functor on derived categories
preserving countable direct sums. -/
theorem mapDerivedCategory_preservesCountableCoproducts
    {A : Type*} {B : Type*} [Category A] [Category B] [Abelian A] [Abelian B]
    [HasDerivedCategory A] [HasDerivedCategory B]
    (hA : HasExactCountableDirectSums A) (hB : HasExactCountableDirectSums B)
    (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesColimitsOfShape (Discrete ℕ) F] :
    PreservesColimitsOfShape (Discrete ℕ) F.mapDerivedCategory := by
  let _ : HasCoproductsOfShape ℕ A := hA.hasCoproducts.1 ℕ
  let _ : HasCoproductsOfShape ℕ B := hB.hasCoproducts.1 ℕ
  let _ := derivedCategory_Q_preservesCoproductsOfShape A hA ℕ
  let _ := derivedCategory_Q_preservesCoproductsOfShape B hB ℕ
  let _ : PreservesColimitsOfShape (Discrete ℕ)
      (DerivedCategory.Q ⋙ F.mapDerivedCategory) :=
    preservesColimitsOfShape_of_natIso F.mapDerivedCategoryFactors.symm
  exact preservesCoproducts_of_comp DerivedCategory.Q F.mapDerivedCategory

end Coproducts

end CategoryTheory



namespace CategoryTheory


variable {D : Type u₁} [Category.{v₁} D] [HasFiniteCoproducts D]

/-- The simplicial object whose `n`-simplices are the copower of a fixed object by the simplices
of the standard simplex on `m`. -/
noncomputable def simplexCopower (A : D) (m : SimplexCategory) : SimplicialObject D where
  obj n := ∐ fun _ : n.unop ⟶ m => A
  map ψ := Limits.Sigma.desc fun φ => Limits.Sigma.ι (fun _ : _ ⟶ m => A) (ψ.unop ≫ φ)
  map_id n := by
    refine Limits.Sigma.hom_ext _ _ fun φ => ?_
    simp
  map_comp ψ χ := by
    refine Limits.Sigma.hom_ext _ _ fun φ => ?_
    simp [Category.assoc]

/-- The copower simplicial object, augmented by the fixed object. -/
noncomputable def simplexCopowerAugmented (A : D) (m : SimplexCategory) :
    SimplicialObject.Augmented D where
  left := simplexCopower A m
  right := A
  hom :=
    { app := fun _ => Limits.Sigma.desc fun _ => 𝟙 A
      naturality := by
        intro n k f
        refine Limits.Sigma.hom_ext _ _ fun φ => ?_
        simp [simplexCopower] }

/-- The copower simplicial object carries an extra degeneracy: on the simplex indexed by `φ` it
is the shift of `φ`. -/
noncomputable def simplexCopowerExtraDegeneracy (A : D) (m : SimplexCategory) :
    (simplexCopowerAugmented A m).ExtraDegeneracy where
  s' := Limits.Sigma.ι (fun _ : ⦋0⦌ ⟶ m => A) (SimplexCategory.const _ _ 0)
  s n := Limits.Sigma.desc fun φ => Limits.Sigma.ι (fun _ : ⦋n + 1⦌ ⟶ m => A)
    (SSet.Augmented.StandardSimplex.shift φ)
  s'_comp_ε := by
    simp only [simplexCopowerAugmented]
    exact Limits.Sigma.ι_desc _ _
  s₀_comp_δ₁ := by
    refine Limits.Sigma.hom_ext _ _ fun φ => ?_
    simp only [simplexCopowerAugmented, SimplicialObject.δ, simplexCopower,
      Limits.Sigma.ι_desc_assoc, Limits.Sigma.ι_desc, Category.id_comp]
    congr 1
    apply SimplexCategory.Hom.ext
    ext j : 2
    fin_cases j
    rfl
  s_comp_δ₀ n := by
    refine Limits.Sigma.hom_ext _ _ fun φ => ?_
    simp only [simplexCopowerAugmented, SimplicialObject.δ, simplexCopower,
      Limits.Sigma.ι_desc_assoc, Limits.Sigma.ι_desc, Category.comp_id]
    congr 1
    apply SimplexCategory.Hom.ext
    ext j : 2
    rfl
  s_comp_δ n i := by
    refine Limits.Sigma.hom_ext _ _ fun φ => ?_
    simp only [simplexCopowerAugmented, SimplicialObject.δ, simplexCopower,
      Limits.Sigma.ι_desc_assoc, Limits.Sigma.ι_desc]
    congr 1
    apply SimplexCategory.Hom.ext
    ext j : 2
    cases j using Fin.cases <;>
      simp [SSet.Augmented.StandardSimplex.shift, OrderHom.coe_mk,
        SSet.Augmented.StandardSimplex.shiftFun, SimplexCategory.δ]
    all_goals rfl
  s_comp_σ n i := by
    refine Limits.Sigma.hom_ext _ _ fun φ => ?_
    simp only [simplexCopowerAugmented, SimplicialObject.σ, simplexCopower,
      Limits.Sigma.ι_desc_assoc, Limits.Sigma.ι_desc]
    congr 1
    apply SimplexCategory.Hom.ext
    ext j : 2
    cases j using Fin.cases <;>
      simp [SSet.Augmented.StandardSimplex.shift, OrderHom.coe_mk,
        SSet.Augmented.StandardSimplex.shiftFun, SimplexCategory.σ]
    all_goals rfl

end CategoryTheory




namespace CategoryTheory.SimplicialSiteSituation

attribute [local implicit_reducible] CategoryTheory.derivedInverseImage

variable (S : SimplicialSiteSituation.{u})
  [HasDerivedCategory.{v} (Sheaf S.totalTopology Ab.{u})]
  [∀ n, HasDerivedCategory.{v} (Sheaf (S.componentTopology n) Ab.{u})]

/-- The term of the realization complex in one simplicial degree: the extension by lower shriek
of the object of the system in that degree. -/
noncomputable def realizationTerm (T : SimplicialDerivedSystem S) (n : SimplexCategory) :
    DerivedCategory (Sheaf S.totalTopology Ab.{u}) :=
  (S.componentLowerShriekDerived n).obj (T.obj n)

variable {S}

omit [HasDerivedCategory.{v} (Sheaf S.totalTopology Ab.{u})] in
/-- Naturality of the unit comparison `derivedInverseImageIdIso` of derived inverse images. -/
theorem derivedInverseImageIdIso_hom_naturality (n : SimplexCategory)
    {K K' : DerivedCategory (Sheaf (S.componentTopology n) Ab.{u})} (g : K ⟶ K') :
    (derivedInverseImage S (𝟙 n)).map g ≫ (derivedInverseImageIdIso S n).hom.app K' =
      (derivedInverseImageIdIso S n).hom.app K ≫ g :=
  (derivedInverseImageIdIso S n).hom.naturality g

/-- The transition of the realization complex along a simplex map: the transpose of the inverse
of the transition of the system, followed by the unit and the derived transition. -/
noncomputable def realizationTermMap (T : SimplicialDerivedSystem S)
    (hT : SimplicialDerivedSystem.Cartesian T) {m n : SimplexCategory} (φ : m ⟶ n) :
    realizationTerm S T n ⟶ realizationTerm S T m := by
  have := hT φ
  exact ((S.componentLowerShriekDerivedAdjunction n).homEquiv _ _).symm
    (inv (T.map φ) ≫ (derivedInverseImage S φ).map
      ((S.componentLowerShriekDerivedAdjunction m).unit.app (T.obj m)) ≫
      (derivedTransition S φ).app (realizationTerm S T m))

/-- The transpose of the transition of the realization complex. -/
theorem realizationTermMap_homEquiv (T : SimplicialDerivedSystem S)
    (hT : SimplicialDerivedSystem.Cartesian T) {m n : SimplexCategory} (φ : m ⟶ n) :
    (S.componentLowerShriekDerivedAdjunction n).homEquiv _ _ (realizationTermMap T hT φ) =
      @inv _ _ _ _ (T.map φ) (hT φ) ≫
        (derivedInverseImage S φ).map
          ((S.componentLowerShriekDerivedAdjunction m).unit.app (T.obj m)) ≫
        (derivedTransition S φ).app (realizationTerm S T m) := by
  simp only [realizationTermMap, Equiv.apply_symm_apply]

/-- The transition of the realization complex along an identity is the identity. -/
theorem realizationTermMap_id (T : SimplicialDerivedSystem S)
    (hT : SimplicialDerivedSystem.Cartesian T) (n : SimplexCategory) :
    realizationTermMap T hT (𝟙 n) = 𝟙 _ := by
  refine ((S.componentLowerShriekDerivedAdjunction n).homEquiv _ _).injective ?_
  refine Eq.trans (realizationTermMap_homEquiv T hT (𝟙 n)) ?_
  refine Eq.trans ?_ ((S.componentLowerShriekDerivedAdjunction n).homEquiv_id (T.obj n)).symm
  refine Eq.trans (congrArg (fun k => @inv _ _ _ _ (T.map (𝟙 n)) (hT (𝟙 n)) ≫
      (derivedInverseImage S (𝟙 n)).map
        ((S.componentLowerShriekDerivedAdjunction n).unit.app (T.obj n)) ≫ k)
    (derivedTransition_id_app S n (realizationTerm S T n))) ?_
  refine Eq.trans (congrArg (fun k => @inv _ _ _ _ (T.map (𝟙 n)) (hT (𝟙 n)) ≫ k)
    (derivedInverseImageIdIso_hom_naturality n
      ((S.componentLowerShriekDerivedAdjunction n).unit.app (T.obj n)))) ?_
  refine Eq.trans (congrArg (fun k => @inv _ _ _ _ (T.map (𝟙 n)) (hT (𝟙 n)) ≫ k ≫
      (S.componentLowerShriekDerivedAdjunction n).unit.app (T.obj n)) (hT.map_id n).symm) ?_
  exact IsIso.inv_hom_id_assoc _ _

/-- Naturality of the canonical derived transition `derivedTransition`. -/
theorem derivedTransition_naturality {m n : SimplexCategory} (φ : m ⟶ n)
    {K K' : DerivedCategory (Sheaf S.totalTopology Ab.{u})} (g : K ⟶ K') :
    (derivedInverseImage S φ).map ((derivedComponent S m).map g) ≫
        (derivedTransition S φ).app K' =
      (derivedTransition S φ).app K ≫ (derivedComponent S n).map g :=
  (derivedTransition S φ).naturality g

/-- The transition of the realization complex is contravariantly functorial. -/
theorem realizationTermMap_comp (T : SimplicialDerivedSystem S)
    (hT : SimplicialDerivedSystem.Cartesian T) {l m n : SimplexCategory} (ψ : l ⟶ m)
    (φ : m ⟶ n) :
    realizationTermMap T hT (ψ ≫ φ) =
      realizationTermMap T hT φ ≫ realizationTermMap T hT ψ := by
  have hψ := hT ψ
  have hφ := hT φ
  have hψφ := hT (ψ ≫ φ)
  have hmid : (derivedInverseImage S ψ).map
        ((S.componentLowerShriekDerivedAdjunction l).unit.app (T.obj l)) ≫
        (derivedTransition S ψ).app (realizationTerm S T l) =
      T.map ψ ≫ (S.componentLowerShriekDerivedAdjunction m).homEquiv _ _
        (realizationTermMap T hT ψ) := by
    refine Eq.trans ?_ (congrArg (fun k => T.map ψ ≫ k)
      (realizationTermMap_homEquiv T hT ψ)).symm
    exact (IsIso.hom_inv_id_assoc (T.map ψ) _).symm
  have hinv : @inv _ _ _ _ (T.map (ψ ≫ φ)) hψφ ≫
        (derivedInverseImageCompIso S ψ φ).hom.app (T.obj l) ≫
        (derivedInverseImage S φ).map (T.map ψ) = @inv _ _ _ _ (T.map φ) hφ := by
    refine (cancel_mono (T.map φ)).1 ?_
    refine Eq.trans ?_ (IsIso.inv_hom_id (T.map φ)).symm
    refine Eq.trans (Category.assoc _ _ _) ?_
    refine Eq.trans (congrArg (fun k => @inv _ _ _ _ (T.map (ψ ≫ φ)) hψφ ≫ k)
      (Category.assoc _ _ _)) ?_
    refine Eq.trans (congrArg (fun k => @inv _ _ _ _ (T.map (ψ ≫ φ)) hψφ ≫ k)
      (T.map_comp ψ φ).symm) ?_
    exact IsIso.inv_hom_id _
  have hinner : (derivedInverseImage S φ).map
        ((derivedInverseImage S ψ).map
          ((S.componentLowerShriekDerivedAdjunction l).unit.app (T.obj l))) ≫
        ((derivedInverseImage S φ).map ((derivedTransition S ψ).app (realizationTerm S T l)) ≫
          (derivedTransition S φ).app (realizationTerm S T l)) =
      (derivedInverseImage S φ).map (T.map ψ) ≫
        (derivedInverseImage S φ).map
          ((S.componentLowerShriekDerivedAdjunction m).homEquiv _ _
            (realizationTermMap T hT ψ)) ≫
        (derivedTransition S φ).app (realizationTerm S T l) := by
    refine Eq.trans (Category.assoc _ _ _).symm ?_
    refine Eq.trans (congrArg (fun k => k ≫ (derivedTransition S φ).app (realizationTerm S T l))
      ((derivedInverseImage S φ).map_comp _ _).symm) ?_
    refine Eq.trans (congrArg (fun k => (derivedInverseImage S φ).map k ≫
      (derivedTransition S φ).app (realizationTerm S T l)) hmid) ?_
    refine Eq.trans (congrArg (fun k => k ≫
      (derivedTransition S φ).app (realizationTerm S T l))
      ((derivedInverseImage S φ).map_comp _ _)) ?_
    exact Category.assoc _ _ _
  refine ((S.componentLowerShriekDerivedAdjunction n).homEquiv _ _).injective ?_
  have hL : (S.componentLowerShriekDerivedAdjunction n).homEquiv _ _
        (realizationTermMap T hT (ψ ≫ φ)) =
      @inv _ _ _ _ (T.map φ) hφ ≫
        (derivedInverseImage S φ).map
          ((S.componentLowerShriekDerivedAdjunction m).homEquiv _ _
            (realizationTermMap T hT ψ)) ≫
        (derivedTransition S φ).app (realizationTerm S T l) := by
    refine Eq.trans (realizationTermMap_homEquiv T hT (ψ ≫ φ)) ?_
    refine Eq.trans (congrArg (fun k => @inv _ _ _ _ (T.map (ψ ≫ φ)) hψφ ≫
      (derivedInverseImage S (ψ ≫ φ)).map
        ((S.componentLowerShriekDerivedAdjunction l).unit.app (T.obj l)) ≫ k)
      (derivedTransition_comp_app S ψ φ (realizationTerm S T l))) ?_
    refine Eq.trans (congrArg (fun k => @inv _ _ _ _ (T.map (ψ ≫ φ)) hψφ ≫ k)
      (derivedInverseImageCompIso_hom_naturality_assoc S ψ φ
        ((S.componentLowerShriekDerivedAdjunction l).unit.app (T.obj l))
        ((derivedInverseImage S φ).map ((derivedTransition S ψ).app (realizationTerm S T l)) ≫
          (derivedTransition S φ).app (realizationTerm S T l))).symm) ?_
    refine Eq.trans (congrArg (fun k => @inv _ _ _ _ (T.map (ψ ≫ φ)) hψφ ≫
      (derivedInverseImageCompIso S ψ φ).hom.app (T.obj l) ≫ k) hinner) ?_
    refine Eq.trans (congrArg (fun k => @inv _ _ _ _ (T.map (ψ ≫ φ)) hψφ ≫ k)
      (Category.assoc _ _ _).symm) ?_
    refine Eq.trans (Category.assoc _ _ _).symm ?_
    exact congrArg (fun k => k ≫ ((derivedInverseImage S φ).map
      ((S.componentLowerShriekDerivedAdjunction m).homEquiv _ _ (realizationTermMap T hT ψ)) ≫
      (derivedTransition S φ).app (realizationTerm S T l))) hinv
  have hR : (S.componentLowerShriekDerivedAdjunction n).homEquiv _ _
        (realizationTermMap T hT φ ≫ realizationTermMap T hT ψ) =
      @inv _ _ _ _ (T.map φ) hφ ≫
        (derivedInverseImage S φ).map
          ((S.componentLowerShriekDerivedAdjunction m).homEquiv _ _
            (realizationTermMap T hT ψ)) ≫
        (derivedTransition S φ).app (realizationTerm S T l) := by
    refine Eq.trans ((S.componentLowerShriekDerivedAdjunction n).homEquiv_naturality_right
      (realizationTermMap T hT φ) (realizationTermMap T hT ψ)) ?_
    refine Eq.trans (congrArg (fun k => k ≫
      (derivedComponent S n).map (realizationTermMap T hT ψ))
      (realizationTermMap_homEquiv T hT φ)) ?_
    refine Eq.trans (Category.assoc _ _ _) ?_
    refine congrArg (fun k => @inv _ _ _ _ (T.map φ) hφ ≫ k) ?_
    refine Eq.trans (Category.assoc _ _ _) ?_
    refine Eq.trans (congrArg (fun k => (derivedInverseImage S φ).map
      ((S.componentLowerShriekDerivedAdjunction m).unit.app (T.obj m)) ≫ k)
      (derivedTransition_naturality φ (realizationTermMap T hT ψ)).symm) ?_
    refine Eq.trans (Category.assoc _ _ _).symm ?_
    refine Eq.trans (congrArg (fun k => k ≫ (derivedTransition S φ).app (realizationTerm S T l))
      ((derivedInverseImage S φ).map_comp _ _).symm) ?_
    exact congrArg (fun k => (derivedInverseImage S φ).map k ≫
      (derivedTransition S φ).app (realizationTerm S T l))
      ((S.componentLowerShriekDerivedAdjunction m).homEquiv_unit _ _
        (realizationTermMap T hT ψ)).symm
  exact hL.trans hR.symm

/-- The realization of a cartesian system as a simplicial object of the derived category of the
total site: in degree `n` the extension by lower shriek of the object of the system, and along a
simplex map the transpose of the inverse of the transition of the system. -/
noncomputable def realizationSimplicial (T : SimplicialDerivedSystem S)
    (hT : SimplicialDerivedSystem.Cartesian T) :
    SimplicialObject (DerivedCategory (Sheaf S.totalTopology Ab.{u})) where
  obj n := realizationTerm S T n.unop
  map φ := realizationTermMap T hT φ.unop
  map_id n := realizationTermMap_id T hT n.unop
  map_comp φ ψ := realizationTermMap_comp T hT ψ.unop φ.unop

/-- The complex whose totalization realizes the system: the alternating face map complex of the
realization. -/
noncomputable def realizationComplex (T : SimplicialDerivedSystem S)
    (hT : SimplicialDerivedSystem.Cartesian T) :
    ChainComplex (DerivedCategory (Sheaf S.totalTopology Ab.{u})) ℕ :=
  (AlgebraicTopology.alternatingFaceMapComplex _).obj (realizationSimplicial T hT)

/-- The transpose of the transition of the realization: a morphism from the object of the system
in degree `m` to the restriction in degree `m` of the realization in degree `n`. -/
noncomputable def realizationComponentInclusion (T : SimplicialDerivedSystem S)
    (hT : SimplicialDerivedSystem.Cartesian T) {m n : SimplexCategory} (φ : n ⟶ m) :
    T.obj m ⟶ (derivedComponent S m).obj (realizationTerm S T n) :=
  (S.componentLowerShriekDerivedAdjunction m).homEquiv _ _ (realizationTermMap T hT φ)

/-- The transposes of the transitions of the realization compose. -/
theorem realizationComponentInclusion_comp (T : SimplicialDerivedSystem S)
    (hT : SimplicialDerivedSystem.Cartesian T) {l n m : SimplexCategory} (ψ : l ⟶ n)
    (φ : n ⟶ m) :
    realizationComponentInclusion T hT φ ≫
        (derivedComponent S m).map (realizationTermMap T hT ψ) =
      realizationComponentInclusion T hT (ψ ≫ φ) := by
  refine Eq.trans ((S.componentLowerShriekDerivedAdjunction m).homEquiv_naturality_right
    (realizationTermMap T hT φ) (realizationTermMap T hT ψ)).symm ?_
  exact congrArg ((S.componentLowerShriekDerivedAdjunction m).homEquiv _ _)
    (realizationTermMap_comp T hT ψ φ).symm

end CategoryTheory.SimplicialSiteSituation

namespace CategoryTheory.SimplicialSiteSituation

/-- The coproduct of the inverse images along the transitions at the simplex maps `n ⟶ m`
exists. -/
local instance componentFunctorHasCoproductsOfShape (S : SimplicialSiteSituation.{u})
    (n m : SimplexCategory) :
    Limits.HasCoproductsOfShape (n ⟶ m)
      (Sheaf (S.componentTopology n) Ab.{u} ⥤ Sheaf (S.componentTopology m) Ab.{u}) :=
  Limits.HasColimitsOfSize.has_colimits_of_shape _

/-- The direct sum of the inverse images along the transitions at the simplex maps `j ⟶ i`
exists, the set of simplex maps being finite. -/
local instance abelianTransitionHasBiproduct (S : SimplicialSiteSituation.{u})
    (i j : SimplexCategory) :
    Limits.HasBiproduct (fun φ : j ⟶ i => abelianTransition S φ) := by
  let _ : Fintype (j ⟶ i) := Fintype.ofFinite (j ⟶ i)
  let _ : Limits.HasFiniteBiproducts (Sheaf (S.componentTopology i) Ab.{u}) :=
    Abelian.hasFiniteBiproducts
  let _ : Limits.HasFiniteBiproducts
      (Sheaf (S.componentTopology j) Ab.{u} ⥤ Sheaf (S.componentTopology i) Ab.{u}) :=
    Abelian.hasFiniteBiproducts
  infer_instance

/-- **Stacks 09WG.** The `φ`th summand inclusion into the abelian sum formula, followed by the
inverse of that formula, is the canonical map attached to `φ`. -/
theorem sigma_ι_comp_componentLowerShriekRestrictionIsoCoproduct_inv_eq_leg
    (S : SimplicialSiteSituation.{u}) (n m : SimplexCategory) (φ : n ⟶ m) :
    Limits.Sigma.ι (fun ψ : n ⟶ m => S.transitionInverseImageAb ψ) φ ≫
        (S.componentLowerShriekRestrictionIsoCoproduct n m).inv =
      S.componentSumFormulaLeg φ := by
  obtain ⟨c⟩ := S
  cases c with
  | inl C => exact C.sigma_ι_comp_componentLowerShriekRestrictionIsoCoproduct_inv_eq_leg n m φ
  | inr C => exact C.sigma_ι_comp_componentLowerShriekRestrictionIsoCoproduct_inv_eq_leg n m φ

/-- **Stacks 09WG.** The `φ`th summand inclusion into the abelian sum formula, followed by the
inverse of that formula, is the canonical map attached to `φ`, for the summand transformation
`componentSumFormulaLeg'` read through `restrictAb`. -/
theorem sigma_ι_comp_componentLowerShriekRestrictionIsoCoproduct_inv_eq_leg'
    (S : SimplicialSiteSituation.{u}) (n m : SimplexCategory) (φ : n ⟶ m) :
    Limits.Sigma.ι (fun ψ : n ⟶ m => S.transitionInverseImageAb ψ) φ ≫
        (S.componentLowerShriekRestrictionIsoCoproduct n m).inv =
      S.componentSumFormulaLeg' φ := by
  obtain ⟨c⟩ := S
  cases c with
  | inl C => exact C.sigma_ι_comp_componentLowerShriekRestrictionIsoCoproduct_inv_eq_leg' n m φ
  | inr C => exact C.sigma_ι_comp_componentLowerShriekRestrictionIsoCoproduct_inv_eq_leg' n m φ

/-- **Stacks 09WG as a direct sum.** Lower shriek from simplicial degree `j`, restricted to
degree `i`, is the direct sum over the simplex maps `φ : [j] ⟶ [i]` of the inverse images of
Stacks 04JC along the transitions. -/
noncomputable def componentLowerShriekBiproductIso (S : SimplicialSiteSituation.{u})
    (i j : SimplexCategory) :
    Functor.sheafPullbackConstruction.sheafPullback (S.componentFunctor j) Ab.{u}
        (S.componentTopology j) S.totalTopology ⋙ S.abelianComponent i ≅
      ⨁ fun φ : j ⟶ i => abelianTransition S φ :=
  S.componentLowerShriekRestrictionIsoCoproduct j i ≪≫
    (Limits.Sigma.mapIso fun φ : j ⟶ i => S.transitionInverseImageAbIso φ) ≪≫
    (Limits.biproduct.isoCoproduct _).symm

/-- **Stacks 09WG as a direct sum.** Lower shriek from simplicial degree `j`, restricted to
degree `i`, is the direct sum over the simplex maps `φ : [j] ⟶ [i]` of the inverse images of
Stacks 04JC along the transitions. -/
noncomputable def componentLowerShriekBiproductIso' (S : SimplicialSiteSituation.{u})
    (i j : SimplexCategory) :
    Functor.sheafPullbackConstruction.sheafPullback (S.componentFunctor j) Ab.{u}
        (S.componentTopology j) S.totalTopology ⋙ S.restrictAb i ≅
      ⨁ fun φ : j ⟶ i => abelianTransition S φ :=
  S.componentLowerShriekRestrictionIsoCoproduct j i ≪≫
    (Limits.Sigma.mapIso fun φ : j ⟶ i => S.transitionInverseImageAbIso φ) ≪≫
    (Limits.biproduct.isoCoproduct _).symm

/-- The `φ`th summand inclusion of a biproduct, followed by the inverse of the isomorphism
`e ≪≫ Sigma.mapIso α ≪≫ biproduct.isoCoproduct.symm`, is `(α φ).inv` followed by the `φ`th
coproduct inclusion and `e.inv`. -/
private theorem biproduct_ι_comp_inv_mapIso {C : Type*} [Category C] [Preadditive C]
    {ι : Type*} {F G : ι → C} [HasBiproduct F] [HasCoproductsOfShape ι C] {Z : C}
    (e : Z ≅ ∐ G) (α : ∀ i, G i ≅ F i) (i : ι) :
    biproduct.ι F i ≫ (e ≪≫ Sigma.mapIso α ≪≫ (biproduct.isoCoproduct F).symm).inv =
      (α i).inv ≫ Sigma.ι G i ≫ e.inv := by
  simp

/-- Transporting a component of the inverse of `α : b ≅ a` along `b.map u` and a map `F` that
factors through `α.hom` gives `a.map u` followed by the remaining factor. -/
private theorem inv_app_comp_map_comp_eq {C D : Type*} [Category C] [Category D] {b a : C ⥤ D}
    (α : b ≅ a) {X Y : C} (u : X ⟶ Y) {Z : D} {F : b.obj Y ⟶ Z} {O : a.obj Y ⟶ Z}
    (hF : F = α.hom.app Y ≫ O) : α.inv.app X ≫ b.map u ≫ F = a.map u ≫ O := by
  rw [hF]
  exact NatIso.naturality_1_assoc α u O

/-- **The summands of the direct-sum formula are the canonical maps.** The `φ`th summand
inclusion into the direct sum, followed by the inverse of the formula, is the unit of
`g_{n!} ⊣ g_n^{-1}` transported along the transition, followed by the transition of Stacks
07TF. -/
theorem componentLowerShriekBiproductIso_ι (S : SimplicialSiteSituation.{u})
    {n m : SimplexCategory} (φ : n ⟶ m) :
    Limits.biproduct.ι (fun ψ : n ⟶ m => abelianTransition S ψ) φ ≫
        (S.componentLowerShriekBiproductIso m n).inv =
      Functor.whiskerRight (S.componentLowerShriekAbAdjunction n).unit (abelianTransition S φ) ≫
        Functor.whiskerLeft
          (Functor.sheafPullbackConstruction.sheafPullback (S.componentFunctor n) Ab.{u}
            (S.componentTopology n) S.totalTopology)
          (abelianTransitionOfFiber S φ) := by
  refine (biproduct_ι_comp_inv_mapIso (S.componentLowerShriekRestrictionIsoCoproduct n m)
    (fun ψ => S.transitionInverseImageAbIso ψ) φ).trans ?_
  rw [S.sigma_ι_comp_componentLowerShriekRestrictionIsoCoproduct_inv_eq_leg n m φ]
  refine NatTrans.ext (funext fun X => ?_)
  exact (congrArg ((S.transitionInverseImageAbIso φ).inv.app X ≫ ·)
    (S.componentSumFormulaLeg_app φ X)).trans
    (inv_app_comp_map_comp_eq (S.transitionInverseImageAbIso φ) _
      (congr_app (S.fiberTransitionAb_eq φ) _))

/-- **The summands of the direct-sum formula are the canonical maps.** The `φ`th summand
inclusion into the direct sum, followed by the inverse of the formula, is the unit of
`g_{n!} ⊣ g_n^{-1}` transported along the transition, followed by the transition of Stacks
07TF. -/
theorem componentLowerShriekBiproductIso_ι' (S : SimplicialSiteSituation.{u})
    {n m : SimplexCategory} (φ : n ⟶ m) :
    Limits.biproduct.ι (fun ψ : n ⟶ m => abelianTransition S ψ) φ ≫
        (S.componentLowerShriekBiproductIso' m n).inv =
      Functor.whiskerRight (S.componentLowerShriekAbAdjunction' n).unit (abelianTransition S φ) ≫
        Functor.whiskerLeft
          (Functor.sheafPullbackConstruction.sheafPullback (S.componentFunctor n) Ab.{u}
            (S.componentTopology n) S.totalTopology)
          (abelianTransitionOfFiber' S φ) := by
  refine (biproduct_ι_comp_inv_mapIso (S.componentLowerShriekRestrictionIsoCoproduct n m)
    (fun ψ => S.transitionInverseImageAbIso ψ) φ).trans ?_
  rw [S.sigma_ι_comp_componentLowerShriekRestrictionIsoCoproduct_inv_eq_leg' n m φ]
  refine NatTrans.ext (funext fun X => ?_)
  exact (congrArg ((S.transitionInverseImageAbIso φ).inv.app X ≫ ·)
    (S.componentSumFormulaLeg_app' φ X)).trans
    (inv_app_comp_map_comp_eq (S.transitionInverseImageAbIso φ) _
      (congr_app (S.fiberTransitionAb_eq' φ) _))

end CategoryTheory.SimplicialSiteSituation

end
