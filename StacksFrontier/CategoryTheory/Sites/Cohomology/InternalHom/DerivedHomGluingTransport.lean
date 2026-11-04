module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedHomGluingTransition

/-!
# Gluing morphisms of a derived category read through the slices of a ringed site

Let `(C, 𝒪)` be a ringed site and `E : 𝒜' ⥤ Mod(𝒪)` an exact functor, fully faithful on derived
categories, from an abelian category (for instance the modules on a site equivalent to `C`). Let
`e : 𝒜 ≌ C` be an equivalence of categories, and for each `A : 𝒜` let restriction to `A` be the
restriction to the slice at `e A` read in an abelian category `D_A` along an exact functor which
is fully faithful on derived categories. If for every morphism `c : C' ⟶ A` the restrictions
along `c` in the `D_A` are compatible with restriction along `e c` in the slices, then morphisms
`P ⟶ I` of the derived category with `R𝓗om(E P, E I)` in `D^{≥ 0}` glue uniquely from compatible
families given on a family covering the site. This is the shape of the gluing principle along
étale charts of an algebraic space, read through the equi-universe model of its small étale site.

## Main results

* `AlgebraicGeometry.RingedSite.existsUnique_restrictQMap_eq_of_transport`: the gluing principle.

## References

* [Stacks Project, Tag 0D66](https://stacks.math.columbia.edu/tag/0D66)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Stacks.DerivedCategoryComparisons
open Stacks.SheafOfModules.Tensor

universe w₁ w₂ v₁ v₂ u₁ u₂ u

namespace AlgebraicGeometry.RingedSite

attribute [local instance] HasDerivedCategory.standard

attribute [local instance] CategoryTheory.Limits.comp_preservesFiniteLimits
  CategoryTheory.Limits.comp_preservesFiniteColimits

variable (X : RingedSite.{u, u, u})
  [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ U : X.C, HasSheafify (X.J.over U) AddCommGrpCat.{u}]
  [∀ U : X.C, (X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ U : X.C, PreservesFiniteLimits
    (SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U)]
  [∀ U : X.C, PreservesFiniteColimits
    (SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U)]
  {C₁ : Type u₁} [Category.{v₁} C₁] [Abelian C₁] [HasDerivedCategory.{w₁} C₁]
  (E : C₁ ⥤ SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) [hEadd : E.Additive]
  {𝒜 : Type u₂} [Category.{v₂} 𝒜] (e : 𝒜 ≌ X.C)
  {D : 𝒜 → Type u₁} [∀ A, Category.{v₁} (D A)] [∀ A, Abelian (D A)]
  [∀ A, HasDerivedCategory.{w₂} (D A)]
  (T : ∀ A, SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over
    (e.functor.obj A)) ⥤ D A)
  [hTadd : ∀ A, (T A).Additive] [hTpfl : ∀ A, PreservesFiniteLimits (T A)]
  [hTpfc : ∀ A, PreservesFiniteColimits (T A)]
  (R : ∀ A, C₁ ⥤ D A) [hRadd : ∀ A, (R A).Additive]
  (ν : ∀ A, (E ⋙ SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
    (e.functor.obj A)) ⋙ T A ≅ R A)

/-- Restriction to the slice at `e A`, read in `D_A` through `ν A`. -/
abbrev sliceTransportQMap (A : 𝒜) {P I : CochainComplex C₁ ℤ}
    (β : DerivedCategory.Q.obj (((E ⋙ SheafOfModules.overFunctor.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O) (e.functor.obj A)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj P) ⟶
      DerivedCategory.Q.obj (((E ⋙ SheafOfModules.overFunctor.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O) (e.functor.obj A)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj I)) :
    DerivedCategory.Q.obj (((R A).mapHomologicalComplex (ComplexShape.up ℤ)).obj P) ⟶
      DerivedCategory.Q.obj (((R A).mapHomologicalComplex (ComplexShape.up ℤ)).obj I) :=
  transportQMap (ν A) β

variable (ρ : ∀ {C A : 𝒜} (_ : C ⟶ A), D A ⥤ D C)
  [hρadd : ∀ {C A : 𝒜} (c : C ⟶ A), (ρ c).Additive]
  [hρpfl : ∀ {C A : 𝒜} (c : C ⟶ A), PreservesFiniteLimits (ρ c)]
  [hρpfc : ∀ {C A : 𝒜} (c : C ⟶ A), PreservesFiniteColimits (ρ c)]
  (γ : ∀ {C A : 𝒜} (c : C ⟶ A), R A ⋙ ρ c ≅ R C)
  (θ : ∀ {C A : 𝒜} (c : C ⟶ A),
    T A ⋙ ρ c ≅ SheafOfModules.overMap.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
      (e.functor.map c) ⋙ T C)
  (hθ : ∀ {C A : 𝒜} (c : C ⟶ A),
    Functor.isoWhiskerLeft
        (E ⋙ SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
          (e.functor.obj A))
        (θ c) ≪≫
      ((Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight
          (Functor.isoWhiskerLeft E
            (SheafOfModules.overFunctorMap (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
              (e.functor.map c))) (T C) ≪≫ ν C) =
    (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight (ν A) (ρ c) ≪≫ γ c)

omit [∀ U : X.C, PreservesFiniteLimits
    (SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U)]
  [∀ U : X.C, PreservesFiniteColimits
    (SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U)] in
include hθ in
/-- **The compatibility of the slice readings with restriction along a morphism.** -/
theorem sliceTransportQMap_restrictComplexDerivedMapAlong {C A : 𝒜} (c : C ⟶ A)
    {P I : CochainComplex C₁ ℤ}
    (β : DerivedCategory.Q.obj (((E ⋙ SheafOfModules.overFunctor.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O) (e.functor.obj A)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj P) ⟶
      DerivedCategory.Q.obj (((E ⋙ SheafOfModules.overFunctor.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O) (e.functor.obj A)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj I)) :
    sliceTransportQMap X E e T R ν C
        (restrictComplexDerivedMapAlong X ((E.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)
          ((E.mapHomologicalComplex (ComplexShape.up ℤ)).obj I) (e.functor.map c) β) =
      transportQMap (γ c) (sliceTransportQMap X E e T R ν A β) := by
  let := Stacks.SheafOfModules.LocalCokernel.overMap_preservesFiniteLimits
    (R := (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (e.functor.map c)
  let := Stacks.SheafOfModules.LocalCokernel.overMap_preservesFiniteColimits
    (R := (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (e.functor.map c)
  rw [restrictComplexDerivedMapAlong_eq_transportQMap,
    ← transportQMap_isoWhiskerLeft_obj E
      (SheafOfModules.overFunctorMap (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
        (e.functor.map c)) β]
  dsimp only [sliceTransportQMap]
  rw [transportQMap_transportQMap, transportQMap_transportQMap, ← hθ c,
    transportQMap_isoWhiskerLeft]

omit [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ U : X.C, HasSheafify (X.J.over U) AddCommGrpCat.{u}]
  [∀ U : X.C, (X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ U : X.C, PreservesFiniteLimits
    (SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U)]
  [∀ U : X.C, PreservesFiniteColimits
    (SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U)] in
/-- A morphism `Z ⟶ e A` of the site is the inverse of the counit at `Z` followed by the image
of the corresponding morphism `e⁻¹ Z ⟶ A`. -/
theorem counitIso_inv_app_comp_functor_map {Z : X.C} {A : 𝒜} (a : Z ⟶ e.functor.obj A) :
    e.counitIso.inv.app Z ≫ e.functor.map (e.inverse.map a ≫ e.unitIso.inv.app A) = a := by
  rw [Functor.map_comp, ← Category.assoc]
  have h1 : e.counitIso.inv.app Z ≫ e.functor.map (e.inverse.map a) =
      a ≫ e.counitIso.inv.app (e.functor.obj A) := (e.counitIso.inv.naturality a).symm
  rw [h1, Category.assoc, Equivalence.counitInv_app_functor, ← Functor.map_comp,
    Iso.hom_inv_id_app]
  exact (congrArg (a ≫ ·) (e.functor.map_id _)).trans (Category.comp_id a)

variable [EnoughInjectives (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))]
  [(sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ A, ((sheafTensor.{u, u, u, u, u} X.O).obj A).Additive]
  [∀ (K₁ K₂ : HomologicalComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u,
    u} X.O)) (ComplexShape.up ℤ)),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (sheafTensor X.O) (ComplexShape.up ℤ)]

/-- `R𝓗om(E P, E I)` lies in `D^{≥ 0}`. -/
def IsGEDerivedSheafHomMap (P I : CochainComplex C₁ ℤ) : Prop :=
  (((derivedSheafHomBifunctor X).obj (op (DerivedCategory.Q.obj
      ((E.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)))).obj
        (DerivedCategory.Q.obj ((E.mapHomologicalComplex (ComplexShape.up ℤ)).obj I))).IsGE 0

variable [hEpfl : PreservesFiniteLimits E] [hEpfc : PreservesFiniteColimits E]
  [hRpfl : ∀ A, PreservesFiniteLimits (R A)] [hRpfc : ∀ A, PreservesFiniteColimits (R A)]
  [hEfull : E.mapDerivedCategory.Full] [hEfaith : E.mapDerivedCategory.Faithful]
  [hTfull : ∀ A, (T A).mapDerivedCategory.Full] [hTfaith : ∀ A, (T A).mapDerivedCategory.Faithful]

include hθ in
/-- **Gluing morphisms of a derived category through the slices of a ringed site.** For
complexes `P`, `I` with `R𝓗om(E P, E I)` in `D^{≥ 0}` and a family `A i` whose images cover the
site, a family of morphisms `R_{A i}(P) ⟶ R_{A i}(I)` of the `D(D_{A i})` whose restrictions
along any two morphisms `c : C ⟶ A i`, `c' : C ⟶ A j` agree is the family of restrictions of a
unique morphism `P ⟶ I` (compare Stacks 0D66 for ringed spaces). -/
theorem existsUnique_restrictQMap_eq_of_transport {P I : CochainComplex C₁ ℤ}
    (hPI : IsGEDerivedSheafHomMap X E P I) {ι : Type*} {A : ι → 𝒜}
    (hA : X.J.CoversTop fun i => e.functor.obj (A i))
    (α : ∀ i, DerivedCategory.Q.obj (((R (A i)).mapHomologicalComplex (ComplexShape.up ℤ)).obj P) ⟶
      DerivedCategory.Q.obj (((R (A i)).mapHomologicalComplex (ComplexShape.up ℤ)).obj I))
    (hα : ∀ (C : 𝒜) (i j : ι) (c : C ⟶ A i) (c' : C ⟶ A j),
      transportQMap (γ c) (α i) = transportQMap (γ c') (α j)) :
    ∃! d : DerivedCategory.Q.obj P ⟶ DerivedCategory.Q.obj I,
      ∀ i, restrictQMap (R (A i)) d = α i := by
  choose β hβ using fun i => transportQMap_surjective (ν (A i)) (α i)
  have hβ' : ∀ (Z : X.C) (i j : ι) (a : Z ⟶ e.functor.obj (A i)) (b : Z ⟶ e.functor.obj (A j)),
      restrictComplexDerivedMapAlong X ((E.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)
          ((E.mapHomologicalComplex (ComplexShape.up ℤ)).obj I) a (β i) =
        restrictComplexDerivedMapAlong X ((E.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)
          ((E.mapHomologicalComplex (ComplexShape.up ℤ)).obj I) b (β j) := by
    intro Z i j a b
    rw [← counitIso_inv_app_comp_functor_map X e a, ← counitIso_inv_app_comp_functor_map X e b,
      restrictComplexDerivedMapAlong_comp_hom, restrictComplexDerivedMapAlong_comp_hom]
    congr 1
    apply transportQMap_injective (ν (e.inverse.obj Z))
    refine (sliceTransportQMap_restrictComplexDerivedMapAlong X E e T R ν ρ γ θ hθ
      (e.inverse.map a ≫ e.unitIso.inv.app (A i)) (β i)).trans (Eq.trans ?_
        (sliceTransportQMap_restrictComplexDerivedMapAlong X E e T R ν ρ γ θ hθ
          (e.inverse.map b ≫ e.unitIso.inv.app (A j)) (β j)).symm)
    exact (congrArg (transportQMap (γ (e.inverse.map a ≫ e.unitIso.inv.app (A i)))) (hβ i)).trans
      ((hα _ i j _ _).trans
        (congrArg (transportQMap (γ (e.inverse.map b ≫ e.unitIso.inv.app (A j)))) (hβ j)).symm)
  obtain ⟨d', hd', huniq⟩ := existsUnique_restrictComplexDerivedMap_eq_of_isGE X _ _ hPI hA β hβ'
  obtain ⟨d, rfl⟩ := restrictQMap_surjective E d'
  have key : ∀ (d₂ : DerivedCategory.Q.obj P ⟶ DerivedCategory.Q.obj I) (i : ι),
      restrictQMap (R (A i)) d₂ = sliceTransportQMap X E e T R ν (A i)
        (restrictComplexDerivedMap X (e.functor.obj (A i)) (restrictQMap E d₂)) := by
    intro d₂ i
    rw [restrictComplexDerivedMap_eq_restrictQMap, restrictQMap_comp_functor]
    exact (transportQMap_restrictQMap (ν (A i)) d₂).symm
  refine ⟨d, fun i => (key d i).trans ((congrArg _ (hd' i)).trans (hβ i)), fun d₂ hd₂ => ?_⟩
  apply restrictQMap_injective E
  refine huniq _ fun i => transportQMap_injective (ν (A i)) ?_
  exact ((key d₂ i).symm.trans (hd₂ i)).trans (hβ i).symm

end AlgebraicGeometry.RingedSite
