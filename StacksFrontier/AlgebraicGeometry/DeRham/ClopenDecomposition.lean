module

public import StacksFrontier.Topology.Sheaves.ClopenDecompositionSections
public import StacksFrontier.AlgebraicGeometry.DeRham.ClosedImmersionPullback
public import StacksFrontier.AlgebraicGeometry.DeRham.FormsDirectImageComparisonSections
public import StacksFrontier.AlgebraicGeometry.DeRham.PullbackComplexDegreewise
public import StacksFrontier.Algebra.Homology.Embedding.ExtendMap
public import StacksFrontier.Algebra.Homology.DerivedCategory.StandardModelScoped
public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedFunctorInjective
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.CategoryTheory.Abelian.Basic

/-!
# De Rham cohomology along a decomposition into open and closed pieces

Let `p : X ⟶ B` be a morphism of schemes and let `X` be the disjoint union of finitely many open
and closed subschemes `U i`. Then the pullbacks along the inclusions `U i ⟶ X` identify

`H^m_{dR}(X/B) = ∏ᵢ H^m_{dR}(U i/B)`.

This is condition (2) of Weil Cohomology Theories, Section 45.12 for de Rham cohomology, which the
source verifies in the proof of Lemma 0FW9 by observing that de Rham cohomology is the cohomology
of a sheaf: the de Rham complex of `X` is the biproduct of the direct images of the de Rham
complexes of the pieces, forms on an open subscheme being forms on `X` over that open; and along
the inclusion of an open and closed subscheme, a closed immersion, the direct image is exact, so
that the cohomology of the direct image is the cohomology of the piece.

## Main results

* `Stacks.DeRhamClopen.bijective_deRhamCohomologyPullback`: the bijection, in the abelian-sheaf
  realization of Section 0FL6.

## References

* [Stacks Project, Tag 0FW9](https://stacks.math.columbia.edu/tag/0FW9)
* [Stacks Project, Tag 0FI4](https://stacks.math.columbia.edu/tag/0FI4)
* [Stacks Project, Section 0FL6](https://stacks.math.columbia.edu/tag/0FL6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry
open scoped Stacks.StandardDerivedModel

universe u

namespace CategoryTheory.Limits

/-- An additive functor carries a morphism into a finite biproduct to the morphism into the
biproduct of the images, through the comparison of the two biproducts. -/
theorem map_biproduct_lift_comp_mapBiproduct_hom {C D : Type*} [Category* C] [Category* D]
    [Preadditive C] [Preadditive D] [HasFiniteBiproducts C] [HasFiniteBiproducts D]
    (F : C ⥤ D) [F.Additive] {J : Type} [Finite J] {A : C} (B : J → C) (g : ∀ j, A ⟶ B j) :
    F.map (biproduct.lift g) ≫ (F.mapBiproduct B).hom = biproduct.lift fun j => F.map (g j) := by
  ext j
  exact (Category.assoc _ _ _).trans ((congrArg (F.map _ ≫ ·) (biproduct.lift_π _ j)).trans
    ((F.map_comp _ _).symm.trans ((congrArg F.map (biproduct.lift_π g j)).trans
      (biproduct.lift_π (f := fun j => F.obj (B j)) (fun j => F.map (g j)) j).symm)))

/-- An additive functor carries a morphism into a finite biproduct to an isomorphism once the
morphism into the biproduct of the images is one. -/
theorem isIso_map_biproduct_lift {C D : Type*} [Category* C] [Category* D]
    [Preadditive C] [Preadditive D] [HasFiniteBiproducts C] [HasFiniteBiproducts D]
    (F : C ⥤ D) [F.Additive] {J : Type} [Finite J] {A : C}
    (B : J → C) (g : ∀ j, A ⟶ B j) (h : IsIso (biproduct.lift fun j => F.map (g j))) :
    IsIso (F.map (biproduct.lift g)) := by
  have h' : F.map (biproduct.lift g) =
      (biproduct.lift fun j => F.map (g j)) ≫ (F.mapBiproduct B).inv := by
    rw [← map_biproduct_lift_comp_mapBiproduct_hom F B g, Category.assoc, Iso.hom_inv_id,
      Category.comp_id]
  rw [h']
  infer_instance

/-- An additive functor which reflects isomorphisms detects that a morphism into a finite
biproduct is an isomorphism. -/
theorem isIso_biproduct_lift_of_isIso_map {C D : Type*} [Category* C] [Category* D]
    [Preadditive C] [Preadditive D] [HasFiniteBiproducts C] [HasFiniteBiproducts D]
    (F : C ⥤ D) [F.Additive] [F.ReflectsIsomorphisms] {J : Type} [Finite J] {A : C}
    (B : J → C) (g : ∀ j, A ⟶ B j) (h : IsIso (biproduct.lift fun j => F.map (g j))) :
    IsIso (biproduct.lift g) :=
  have := isIso_map_biproduct_lift F B g h
  isIso_of_reflects_iso _ F

end CategoryTheory.Limits

namespace Stacks.DeRhamClopen

/-- A morphism into a finite biproduct of bounded below complexes is an isomorphism once it is
one in every degree. -/
theorem isIso_biproduct_lift_plus {C : Type*} [Category* C] [Abelian C] [HasFiniteBiproducts C]
    [HasFiniteBiproducts (CochainComplex.Plus C)] {J : Type} [Finite J]
    {A : CochainComplex.Plus C} (B : J → CochainComplex.Plus C) (g : ∀ j, A ⟶ B j)
    (h : ∀ n : ℤ, IsIso (biproduct.lift fun j => (g j).hom.f n)) :
    IsIso (biproduct.lift g) := by
  have : HasFiniteBiproducts (CochainComplex C ℤ) := HasFiniteBiproducts.of_hasFiniteProducts
  refine CategoryTheory.Limits.isIso_biproduct_lift_of_isIso_map (CochainComplex.Plus.ι C) B g ?_
  have : ∀ n, IsIso ((biproduct.lift fun j => (CochainComplex.Plus.ι C).map (g j)).f n) :=
    fun n => CategoryTheory.Limits.isIso_map_biproduct_lift
      (HomologicalComplex.eval C (ComplexShape.up ℤ) n) _ _ (h n)
  exact HomologicalComplex.Hom.isIso_of_components _

/-- **A direct image along a map into an open `U` only sees `U`**: restriction of its sections
from `W` to `W ∩ U` is bijective, both opens having the same preimage. -/
theorem bijective_pushforward_map_inf {Y Z : TopCat.{u}} (f : Y ⟶ Z) (U : Opens Z)
    (hU : (Opens.map f).obj U = ⊤)
    (M : Sheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u}) (W : Opens Z) :
    Function.Bijective
      (((Stacks.Cohomology.LerayLowDegree.abelianPushforward.{u, u} f).obj M).obj.map
        (homOfLE (inf_le_left : W ⊓ U ≤ W)).op) := by
  have he : (Opens.map f).obj (W ⊓ U) = (Opens.map f).obj W := by
    show (Opens.map f).obj W ⊓ (Opens.map f).obj U = _
    rw [hU, inf_top_eq]
  have hiso : IsIso ((Opens.map f).map (homOfLE (inf_le_left : W ⊓ U ≤ W))) :=
    ⟨⟨homOfLE he.symm.le, Subsingleton.elim _ _, Subsingleton.elim _ _⟩⟩
  have : IsIso (M.obj.map ((Opens.map f).map (homOfLE (inf_le_left : W ⊓ U ≤ W))).op) :=
    inferInstance
  exact ConcreteCategory.bijective_of_isIso
    (M.obj.map ((Opens.map f).map (homOfLE (inf_le_left : W ⊓ U ≤ W))).op)

/-- Every section over `W` of a zero abelian sheaf vanishes. -/
private theorem eq_zero_of_isZero_obj {Y : TopCat.{u}}
    {F : Sheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u}} (h : IsZero F) (W : Opens Y)
    (x : ToType (F.obj.obj (op W))) : x = 0 := by
  simpa using ConcreteCategory.congr_hom
    (congrArg (fun φ => φ.hom.app (op W)) (h.eq_of_src (𝟙 _) 0)) x

section DeRham

variable {X B : Scheme.{u}} (p : X ⟶ B)

/-- The canonical map of de Rham complexes along the inclusion of an open subscheme is, on
sections over an open inside it, the pullback of forms, which is bijective. -/
theorem bijective_deRhamFormsPushforwardHom_app {U : X.Opens} (n : ℕ) (W : X.Opens) (hW : W ≤ U) :
    Function.Bijective
      (((Scheme.Hom.deRhamFormsPushforwardHom U.ι p (U.ι ≫ p) (𝟙 B) (Category.comp_id _).symm).app
        (n : ℤ)).val.app (op W)) := by
  have h := Scheme.Hom.bijective_relativeDifferentialFormsPullback_of_isOpenImmersion' U.ι p
    (U.ι ≫ p) (Category.comp_id _).symm (n : ℤ) W (by rwa [Scheme.Opens.opensRange_ι])
  rw [← Scheme.Hom.homEquiv_relativeDifferentialFormsMap]
  exact h

/-- The canonical map of de Rham complexes along the inclusion of an open subscheme, in one
degree, is bijective on sections over the opens inside it. -/
theorem bijective_deRhamAbelianPushforwardMapPlus_f_app {U : X.Opens} (n : ℤ) (W : X.Opens)
    (hW : W ≤ U) :
    Function.Bijective
      (((Scheme.Hom.deRhamAbelianPushforwardMapPlus U.ι p (U.ι ≫ p) (𝟙 B)
        (Category.comp_id _).symm).hom.f n).hom.app (op W)) := by
  by_cases hn : 0 ≤ n
  · obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le hn
    have hf := HomologicalComplex.extendMap_mapHomologicalComplexExtendIso_f
      (F := Stacks.Cohomology.LerayLowDegree.abelianPushforward.{u, u} U.ι.base)
      (SheafOfModules.deRhamAbelianComplex (Scheme.Hom.deRhamAlgebras (U.ι ≫ p))
        (SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras (U.ι ≫ p))))
      (Scheme.Hom.deRhamAbelianPushforwardMap U.ι p (U.ι ≫ p) (𝟙 B) (Category.comp_id _).symm)
      ComplexShape.embeddingUpNat (i := k) (i' := (k : ℤ)) rfl
    have hψ : (Scheme.Hom.deRhamAbelianPushforwardMapPlus U.ι p (U.ι ≫ p) (𝟙 B)
        (Category.comp_id _).symm).hom.f (k : ℤ) = _ := hf
    rw [hψ]
    have h1 : Function.Bijective ((HomologicalComplex.extendXIso
        (SheafOfModules.deRhamAbelianComplex (Scheme.Hom.deRhamAlgebras p)
          (SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras p)))
        ComplexShape.embeddingUpNat (i := k) (i' := (k : ℤ)) rfl).hom.hom.app (op W)) :=
      ConcreteCategory.bijective_of_isIso _
    have h3 : Function.Bijective (((Stacks.Cohomology.LerayLowDegree.abelianPushforward.{u, u}
        U.ι.base).map (HomologicalComplex.extendXIso
        (SheafOfModules.deRhamAbelianComplex (Scheme.Hom.deRhamAlgebras (U.ι ≫ p))
          (SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras (U.ι ≫ p))))
        ComplexShape.embeddingUpNat (i := k) (i' := (k : ℤ)) rfl).inv).hom.app (op W)) :=
      ConcreteCategory.bijective_of_isIso _
    have h2 := bijective_deRhamFormsPushforwardHom_app p k W hW
    exact h3.comp (h2.comp h1)
  · have h0 : IsZero ((SheafOfModules.deRhamAbelianComplexInt (Scheme.Hom.deRhamAlgebras p)
        (SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras p))).X n) :=
      HomologicalComplex.isZero_extend_X (SheafOfModules.deRhamAbelianComplex
        (Scheme.Hom.deRhamAlgebras p) (SheafOfModules.deRhamDifferential
          (Scheme.Hom.deRhamAlgebras p))) ComplexShape.embeddingUpNat n fun k hk => hn (by
        rw [← hk]
        exact Int.natCast_nonneg k)
    have h0' : IsZero ((Scheme.Hom.deRhamPushforwardPlus U.ι (U.ι ≫ p)).obj.X n) :=
      Functor.map_isZero (Stacks.Cohomology.LerayLowDegree.abelianPushforward.{u, u} U.ι.base)
        (HomologicalComplex.isZero_extend_X (SheafOfModules.deRhamAbelianComplex
        (Scheme.Hom.deRhamAlgebras (U.ι ≫ p)) (SheafOfModules.deRhamDifferential
          (Scheme.Hom.deRhamAlgebras (U.ι ≫ p)))) ComplexShape.embeddingUpNat n fun k hk => hn (by
        rw [← hk]
        exact Int.natCast_nonneg k))
    exact ⟨fun a b _ => (eq_zero_of_isZero_obj h0 W a).trans (eq_zero_of_isZero_obj h0 W b).symm,
      fun y => ⟨0, (eq_zero_of_isZero_obj h0' W _).trans (eq_zero_of_isZero_obj h0' W y).symm⟩⟩

variable {ι : Type} [Finite ι] (U : ι → X.Opens) (hU : ∀ i, IsClopen (U i : Set X))
  (hdisj : ∀ i j, i ≠ j → Disjoint (U i) (U j)) (hcov : (⨆ i, U i) = ⊤)

omit [Finite ι] in
/-- Bounded below complexes in an abelian category have finite products, being closed under the
finite limits of all complexes. -/
theorem hasFiniteProducts_plus (C : Type*) [Category* C] [Abelian C] :
    HasFiniteProducts (CochainComplex.Plus C) :=
  ⟨fun n => by
    have : (CochainComplex.plus C).IsClosedUnderLimitsOfShape (Discrete (Fin n)) :=
      inferInstance
    infer_instance⟩

/-- Bounded below complexes of abelian sheaves on a topological space have finite biproducts. -/
instance hasFiniteBiproducts_plus_abelianSheaf (Y : TopCat.{u}) :
    HasFiniteBiproducts
      (CochainComplex.Plus (Sheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u})) :=
  haveI := hasFiniteProducts_plus (Sheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u})
  HasFiniteBiproducts.of_hasFiniteProducts

include hdisj hcov in
/-- **The de Rham complex of `X` is the biproduct of the direct images of the de Rham complexes of
the pieces**, through the canonical maps of Section 07HX along the inclusions. -/
theorem isIso_biproduct_lift_deRhamAbelianPushforwardMapPlus :
    IsIso (biproduct.lift fun i => Scheme.Hom.deRhamAbelianPushforwardMapPlus (U i).ι p
      ((U i).ι ≫ p) (𝟙 B) (Category.comp_id _).symm) := by
  refine isIso_biproduct_lift_plus _ _ fun n => ?_
  exact Stacks.ClopenDecomposition.isIso_biproduct_lift (X := X.carrier)
    (fun i => (U i : Opens X.carrier)) hdisj hcov _ _ _
    (fun i W => bijective_pushforward_map_inf (U i).ι.base (U i) (U i).ι_preimage_self _ W)
    (fun i W hW => bijective_deRhamAbelianPushforwardMapPlus_f_app p n W hW)

/-- The localization functor of bounded below complexes is additive. -/
instance plusQ_additive (C : Type*) [Category* C] [Abelian C] :
    (DerivedCategory.Plus.Q (C := C)).Additive where
  map_add {_ _ f g} :=
    ObjectProperty.hom_ext _ ((DerivedCategory.Q (C := C)).map_add (f := f.hom) (g := g.hom))

/-- Hypercohomology `H^m(X, -)` of bounded below complexes of abelian sheaves, as a functor. -/
abbrev hypercohomologyFunctor (Y : TopCat.{u}) (m : ℤ) :
    CochainComplex.Plus (Sheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u}) ⥤
      AddCommGrpCat.{u} :=
  DerivedCategory.Plus.Q ⋙
    (Stacks.Cohomology.Leray.sectionsFunctor Y ⊤).rightDerivedFunctorPlus ⋙
    DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u} m

include hdisj hcov in
/-- **Hypercohomology of the de Rham complex along a decomposition into open and closed pieces**:
the canonical maps to the direct images of the de Rham complexes of the pieces induce a bijection
`H^m(X, Ω^•_{X/B}) ⟶ ∏ᵢ H^m(X, (U i)_*Ω^•_{U i/B})`. -/
theorem bijective_hypercohomology_deRhamAbelianPushforwardMapPlus (m : ℤ) :
    Function.Bijective (fun z : ToType ((hypercohomologyFunctor X.carrier m).obj
        (SheafOfModules.deRhamAbelianComplexPlus (Scheme.Hom.deRhamAlgebras p)
          (SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras p)))) => fun i =>
      (hypercohomologyFunctor X.carrier m).map (Scheme.Hom.deRhamAbelianPushforwardMapPlus (U i).ι p
        ((U i).ι ≫ p) (𝟙 B) (Category.comp_id _).symm) z) := by
  have := isIso_biproduct_lift_deRhamAbelianPushforwardMapPlus p U hdisj hcov
  let : (Stacks.Cohomology.Leray.sectionsFunctor X.carrier ⊤).rightDerivedFunctorPlus.CommShift ℤ :=
    CategoryTheory.Functor.commShiftRightDerivedFunctorPlus _
  have :
    (Stacks.Cohomology.Leray.sectionsFunctor X.carrier ⊤).rightDerivedFunctorPlus.IsTriangulated :=
    CategoryTheory.Functor.isTriangulated_rightDerivedFunctorPlus _
  have : (Stacks.Cohomology.Leray.sectionsFunctor X.carrier ⊤).rightDerivedFunctorPlus.Additive :=
    inferInstance
  have : (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u} m).Additive := inferInstance
  have : (hypercohomologyFunctor X.carrier m).Additive :=
    inferInstanceAs (DerivedCategory.Plus.Q ⋙ _ ⋙ _).Additive
  exact (CategoryTheory.Limits.bijective_map_biproduct_lift_iff
    (hypercohomologyFunctor X.carrier m) _ _).1 (ConcreteCategory.bijective_of_isIso _)

include hU hdisj hcov in
/-- **De Rham cohomology along a decomposition into open and closed pieces** (condition (2) of
Weil Cohomology Theories, Section 45.12, as verified in the proof of Stacks, Lemma 0FW9): if `X`
is the disjoint union of finitely many open and closed subschemes `U i`, the pullbacks along the
inclusions identify `H^m_{dR}(X/B)` with `∏ᵢ H^m_{dR}(U i/B)`. -/
theorem bijective_deRhamCohomologyPullback (m : ℤ) :
    Function.Bijective (fun z : ToType (Scheme.Hom.deRhamCohomology p m) => fun i =>
      (Scheme.Hom.deRhamCohomologyPullback (U i).ι p ((U i).ι ≫ p) (𝟙 B)
        (Category.comp_id _).symm m).hom z) := by
  let φ := fun i => (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u} m).map
      ((Stacks.Cohomology.Leray.sectionsFunctor X.carrier ⊤).rightDerivedFunctorPlus.map
        (Scheme.Hom.deRhamPushforwardToDerived (U i).ι ((U i).ι ≫ p)) ≫
      (Scheme.Hom.derivedSectionsPushforwardIso (U i).ι).inv.app
        (DerivedCategory.Plus.Q.obj (SheafOfModules.deRhamAbelianComplexPlus
          (Scheme.Hom.deRhamAlgebras ((U i).ι ≫ p))
          (SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras ((U i).ι ≫ p))))))
  have hR : ∀ i, Function.Bijective (φ i) := by
    intro i
    have : IsClosedImmersion (U i).ι := IsClosedImmersion.of_isPreimmersion (U i).ι
      (by rw [Scheme.Opens.range_ι]; exact (hU i).isClosed)
    exact ConcreteCategory.bijective_of_isIso _
  have hsplit : ∀ i (z : ToType (Scheme.Hom.deRhamCohomology p m)),
      (Scheme.Hom.deRhamCohomologyPullback (U i).ι p ((U i).ι ≫ p) (𝟙 B)
        (Category.comp_id _).symm m).hom z =
      (φ i).hom ((hypercohomologyFunctor X.carrier m).map
        (Scheme.Hom.deRhamAbelianPushforwardMapPlus
          (U i).ι p ((U i).ι ≫ p) (𝟙 B) (Category.comp_id _).symm) z) := by
    intro i z
    show ((DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u} m).map (_ ≫ _)).hom z = _
    rw [Functor.map_comp]
    rfl
  have hc := (Function.Bijective.piMap hR).comp
    (bijective_hypercohomology_deRhamAbelianPushforwardMapPlus p U hdisj hcov m)
  refine (congrArg Function.Bijective (funext fun z => funext fun i => ?_)).mp hc
  exact (hsplit i z).symm

end DeRham

end Stacks.DeRhamClopen

end
