module

public import StacksFrontier.Algebra.Homology.DerivedCategory.CompositionOfRightDerivedFunctors
public import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedSquareTransComposition
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The derived comparison of a square, computed on acyclic resolutions

Let `Γ₀ : 𝒞₀ ⥤ ℳ₀` and `Γ : 𝒞 ⥤ ℳ` be additive, `P : 𝒞₀ ⥤ 𝒞` and `r : ℳ ⥤ ℳ₀` exact, and
`α : Γ₀ ⟶ P ⋙ Γ ⋙ r`.  The derived comparison `derivedSquareMap α X : RΓ₀(X[0]) ⟶ r(RΓ(P X[0]))`
is computed by acyclic resolutions: given a resolution `ι : X[0] ⟶ J` of `X` by `Γ₀`-acyclic
objects, a resolution `ι' : (P X)[0] ⟶ J'` of `P X` by `Γ`-acyclic objects and a map of complexes
`τ : P(J) ⟶ J'` compatible with the resolutions, `RΓ₀(X[0]) ≅ Γ₀(J)` and `RΓ((P X)[0]) ≅ Γ(J')`
(Leray's acyclicity lemma, [Stacks, Tag 015E]), and under these identifications
`derivedSquareMap α X` is the class of the map of complexes

`Γ₀(J) ⟶ r(Γ(P J)) ⟶ r(Γ(J'))`,

`α` applied degreewise followed by `r(Γ(τ))`.  In particular `derivedSquareMap α X` is an
isomorphism as soon as that map of complexes is a quasi-isomorphism.

## Main definitions

* `CategoryTheory.Functor.rightDerivedFunctorPlusObjSingleIsoOfResolution` — `RΓ(X[0]) ≅ Γ(J)`
  for a resolution `X[0] ⟶ J` by `Γ`-acyclic objects.
* `CategoryTheory.Functor.plusOfIsStrictlyGE`, `CategoryTheory.Functor.singleHomPlusOfIsStrictlyGE`
  — a bounded below cochain complex and a map `X[0] ⟶ J` of cochain complexes, read in the
  bounded below homotopy category (a quasi-isomorphism stays one,
  `CategoryTheory.Functor.quasiIso_singleHomPlusOfIsStrictlyGE`).

## Main results

* `CategoryTheory.Functor.derivedSquareMap_eq_of_resolutions` — `derivedSquareMap α X` on two
  compatible acyclic resolutions.
* `CategoryTheory.Functor.isIso_derivedSquareMap_of_resolutions` — it is an isomorphism when the
  underived map of complexes is a quasi-isomorphism.
* `CategoryTheory.Functor.derivedSquareMap_eq_of_resolution`,
  `CategoryTheory.Functor.isIso_derivedSquareMap_of_resolution` — the same for a single resolution
  `J` of `X` whose image `P(J)` is a resolution of `P X` by `Γ`-acyclic objects.

## References

* [Stacks, Tag 015E](https://stacks.math.columbia.edu/tag/015E)
* [Stacks, Tag 05T2](https://stacks.math.columbia.edu/tag/05T2)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

namespace CategoryTheory.Functor

section Resolution

variable {C : Type*} [Category* C] [Abelian C] [HasDerivedCategory C]

/-- A quasi-isomorphism of bounded below complexes becomes an isomorphism in the bounded below
derived category. -/
theorem isIso_Qh_map_of_mem_quasiIso {K L : HomotopyCategory.Plus C} (f : K ⟶ L)
    (hf : HomotopyCategory.Plus.quasiIso C f) : IsIso (DerivedCategory.Plus.Qh.map f) :=
  Localization.inverts DerivedCategory.Plus.Qh (HomotopyCategory.Plus.quasiIso C) f hf

/-- **`X[0] ≅ J` in `D⁺`** for a quasi-isomorphism `ι : X[0] ⟶ J` of bounded below complexes. -/
def singleFunctorPlusObjIsoQhOfIsIso {X : C} {J : HomotopyCategory.Plus C}
    (ι : (HomotopyCategory.Plus.singleFunctor C 0).obj X ⟶ J)
    (hι : IsIso (DerivedCategory.Plus.Qh.map ι)) :
    (DerivedCategory.Plus.singleFunctor C 0).obj X ≅ DerivedCategory.Plus.Qh.obj J :=
  (singleFunctorPlusIsoCompQh (A := C) 0).app X ≪≫ asIso (DerivedCategory.Plus.Qh.map ι)

/-- A cochain complex concentrated in degrees `≥ n`, as an object of the bounded below homotopy
category. -/
def plusOfIsStrictlyGE (J : CochainComplex C ℤ) (n : ℤ) [J.IsStrictlyGE n] :
    HomotopyCategory.Plus C :=
  ⟨(HomotopyCategory.quotient C (.up ℤ)).obj J,
    (HomotopyCategory.plus_quotient_obj_iff J).2 ⟨n, inferInstance⟩⟩

/-- A map of cochain complexes `X[0] ⟶ J`, as a morphism of the bounded below homotopy
category. -/
def singleHomPlusOfIsStrictlyGE {X : C} {J : CochainComplex C ℤ} (n : ℤ) [J.IsStrictlyGE n]
    (ι : (HomologicalComplex.single C (.up ℤ) 0).obj X ⟶ J) :
    (HomotopyCategory.Plus.singleFunctor C 0).obj X ⟶ plusOfIsStrictlyGE J n :=
  ObjectProperty.homMk ((HomotopyCategory.quotient C (.up ℤ)).map ι)

omit [HasDerivedCategory C] in
/-- A quasi-isomorphism of cochain complexes `X[0] ⟶ J` is a quasi-isomorphism of the bounded
below homotopy category. -/
theorem quasiIso_singleHomPlusOfIsStrictlyGE {X : C} {J : CochainComplex C ℤ} (n : ℤ)
    [J.IsStrictlyGE n] (ι : (HomologicalComplex.single C (.up ℤ) 0).obj X ⟶ J) [QuasiIso ι] :
    HomotopyCategory.Plus.quasiIso C (singleHomPlusOfIsStrictlyGE n ι) := by
  rw [HomotopyCategory.Plus.quasiIso_iff]
  exact (HomotopyCategory.quotient_map_mem_quasiIso_iff ι).2
    ((HomologicalComplex.mem_quasiIso_iff ι).2 inferInstance)

variable {M : Type*} [Category* M] [Abelian M] [HasDerivedCategory M] [EnoughInjectives C]

variable (Γ : C ⥤ M) [Γ.Additive]

/-- **`RΓ(X[0]) ≅ Γ(J)`** for a resolution `ι : X[0] ⟶ J` of `X` by a bounded below complex of
`Γ`-acyclic objects: `RΓ` applied to `X[0] ≅ J`, followed by the inverse of the canonical map
`Γ(J) ⟶ RΓ(J)`, which is invertible by Leray's acyclicity lemma ([Stacks, Tag 015E],
`CategoryTheory.Functor.isIso_rightDerivedFunctorPlusUnit_app_of_rightAcyclic`). -/
@[ega "0 11.5.4" "special case", sga "4½ Rapport 4.12" "special case"]
def rightDerivedFunctorPlusObjSingleIsoOfResolution {X : C} {J : HomotopyCategory.Plus C}
    (ι : (HomotopyCategory.Plus.singleFunctor C 0).obj X ⟶ J)
    (hι : IsIso (DerivedCategory.Plus.Qh.map ι)) (hJ : ∀ n : ℤ, Γ.rightAcyclic (J.obj.as.X n)) :
    Γ.rightDerivedFunctorPlus.obj ((DerivedCategory.Plus.singleFunctor C 0).obj X) ≅
      DerivedCategory.Plus.Qh.obj (Γ.mapHomotopyCategoryPlus.obj J) :=
  haveI := isIso_rightDerivedFunctorPlusUnit_app_of_rightAcyclic Γ J hJ
  Γ.rightDerivedFunctorPlus.mapIso (singleFunctorPlusObjIsoQhOfIsIso ι hι) ≪≫
    (asIso (Γ.rightDerivedFunctorPlusUnith.app J)).symm

end Resolution

section Square

variable {C₀ : Type*} [Category* C₀] [Abelian C₀] [HasDerivedCategory C₀] [EnoughInjectives C₀]
  {C : Type*} [Category* C] [Abelian C] [HasDerivedCategory C] [EnoughInjectives C]
  {M₀ : Type*} [Category* M₀] [Abelian M₀] [HasDerivedCategory M₀]
  {M : Type*} [Category* M] [Abelian M] [HasDerivedCategory M] [EnoughInjectives M]
  {Γ₀ : C₀ ⥤ M₀} {Γ : C ⥤ M} {P : C₀ ⥤ C} {r : M ⥤ M₀}
  [Γ₀.Additive] [Γ.Additive] [P.Additive] [r.Additive]
  [PreservesFiniteLimits P] [PreservesFiniteColimits P]
  [PreservesFiniteLimits r] [PreservesFiniteColimits r]

/-- The bookkeeping of `derivedSquareMap_eq_of_resolutions`, in an arbitrary category. -/
private lemma bookkeeping {𝒦 : Type*} [Category* 𝒦] {A B C D E F G H B' D' : 𝒦}
    (a : A ⟶ B) (n₁ : B ⟶ C) (n₂ : C ⟶ D) (f₁ : D ⟶ E) (f₂ : E ⟶ F) (f₃ : F ⟶ G) (f₄ : G ⟶ H)
    (b : B ⟶ B') (g₁ : B' ⟶ D') (g₂ : D' ⟶ H) (t : D ⟶ H) (m : C ⟶ D') (c : A ⟶ B')
    (hc : c = a ≫ b) (hk : f₁ ≫ f₂ ≫ f₃ ≫ f₄ = t) (hu : n₂ ≫ t = m ≫ g₂)
    (hr : b ≫ g₁ = n₁ ≫ m) :
    a ≫ ((n₁ ≫ n₂) ≫ f₁) ≫ f₂ ≫ f₃ ≫ f₄ = c ≫ g₁ ≫ g₂ := by
  subst hc
  simp only [Category.assoc, hk, hu, reassoc_of% hr]

/-- Naturality of `mapDerivedCategoryPlusFactorsh` with respect to `Qh`, for a map `f` of the
bounded below homotopy category. -/
private theorem mapDerivedCategoryPlus_map_Qh_map_comp_factorsh {D₀ D : Type*} [Category* D₀]
    [Abelian D₀] [HasDerivedCategory D₀] [Category* D] [Abelian D] [HasDerivedCategory D]
    (Q : D₀ ⥤ D) [Q.Additive] [PreservesFiniteLimits Q] [PreservesFiniteColimits Q]
    {J₁ J₂ : HomotopyCategory.Plus D₀} (f : J₁ ⟶ J₂) :
    Q.mapDerivedCategoryPlus.map (DerivedCategory.Plus.Qh.map f) ≫
        Q.mapDerivedCategoryPlusFactorsh.hom.app J₂ =
      Q.mapDerivedCategoryPlusFactorsh.hom.app J₁ ≫
        DerivedCategory.Plus.Qh.map (Q.mapHomotopyCategoryPlus.map f) := by
  simpa using Q.mapDerivedCategoryPlusFactorsh.hom.naturality f

omit [EnoughInjectives C] in
/-- The comparison of the two resolutions inside `D⁺(𝒞)`: the map `P(J) ⟶ J'` is, after
localization, `P(J) ≅ P(X[0]) ≅ (P X)[0] ≅ J'`. -/
private theorem resolution_key {X : C₀} {J : HomotopyCategory.Plus C₀}
    (ι : (HomotopyCategory.Plus.singleFunctor C₀ 0).obj X ⟶ J)
    (hι : IsIso (DerivedCategory.Plus.Qh.map ι)) {J' : HomotopyCategory.Plus C}
    (ι' : (HomotopyCategory.Plus.singleFunctor C 0).obj (P.obj X) ⟶ J')
    (hι' : IsIso (DerivedCategory.Plus.Qh.map ι'))
    (τ : P.mapHomotopyCategoryPlus.obj J ⟶ J')
    (hτ : P.mapHomotopyCategoryPlus.map ι ≫ τ =
      (P.mapHomotopyCategoryPlusObjSingleIso 0 X).hom ≫ ι') :
    P.mapDerivedCategoryPlusFactorsh.inv.app J ≫
        P.mapDerivedCategoryPlus.map (singleFunctorPlusObjIsoQhOfIsIso ι hι).inv ≫
        (P.mapDerivedCategoryPlusObjSingleIso X).hom ≫
        (singleFunctorPlusObjIsoQhOfIsIso ι' hι').hom =
      DerivedCategory.Plus.Qh.map τ := by
  suffices h : (P.mapDerivedCategoryPlusObjSingleIso X).hom ≫
      (singleFunctorPlusObjIsoQhOfIsIso ι' hι').hom =
        P.mapDerivedCategoryPlus.map (singleFunctorPlusObjIsoQhOfIsIso ι hι).hom ≫
          P.mapDerivedCategoryPlusFactorsh.hom.app J ≫ DerivedCategory.Plus.Qh.map τ by
    rw [h, ← Functor.map_comp_assoc, Iso.inv_hom_id, Functor.map_id, Category.id_comp,
      Iso.inv_hom_id_app_assoc]
  simp only [singleFunctorPlusObjIsoQhOfIsIso, Iso.trans_hom, Iso.app_hom, asIso_hom,
    Functor.map_comp, Category.assoc, mapDerivedCategoryPlusObjSingleIso_hom]
  rw [reassoc_of% mapDerivedCategoryPlus_map_Qh_map_comp_factorsh P, ← Functor.map_comp, hτ,
    Functor.map_comp, Iso.inv_hom_id_app_assoc]

/-- **The derived comparison of a square on two compatible acyclic resolutions.**  Let
`ι : X[0] ⟶ J` be a quasi-isomorphism onto a bounded below complex of `Γ₀`-acyclic objects,
`ι' : (P X)[0] ⟶ J'` one onto a bounded below complex of `Γ`-acyclic objects, and
`τ : P(J) ⟶ J'` a map of complexes with `P(ι) ≫ τ = ι'` (through `P(X[0]) ≅ (P X)[0]`).  Then,
under `RΓ₀(X[0]) ≅ Γ₀(J)` and `RΓ((P X)[0]) ≅ Γ(J')`, `derivedSquareMap α X` is the class of the
map of complexes `Γ₀(J) ⟶ r(Γ(J'))` given by `α` applied degreewise followed by `r(Γ(τ))`. -/
theorem derivedSquareMap_eq_of_resolutions (α : Γ₀ ⟶ P ⋙ Γ ⋙ r) {X : C₀}
    {J : HomotopyCategory.Plus C₀} (ι : (HomotopyCategory.Plus.singleFunctor C₀ 0).obj X ⟶ J)
    (hι : IsIso (DerivedCategory.Plus.Qh.map ι)) (hJ : ∀ n : ℤ, Γ₀.rightAcyclic (J.obj.as.X n))
    {J' : HomotopyCategory.Plus C}
    (ι' : (HomotopyCategory.Plus.singleFunctor C 0).obj (P.obj X) ⟶ J')
    (hι' : IsIso (DerivedCategory.Plus.Qh.map ι')) (hJ' : ∀ n : ℤ, Γ.rightAcyclic (J'.obj.as.X n))
    (τ : P.mapHomotopyCategoryPlus.obj J ⟶ J')
    (hτ : P.mapHomotopyCategoryPlus.map ι ≫ τ =
      (P.mapHomotopyCategoryPlusObjSingleIso 0 X).hom ≫ ι') :
    derivedSquareMap α X =
      (rightDerivedFunctorPlusObjSingleIsoOfResolution Γ₀ ι hι hJ).hom ≫
        DerivedCategory.Plus.Qh.map ((mapHomotopyCategoryPlusNatTrans α).app J ≫
          r.mapHomotopyCategoryPlus.map (Γ.mapHomotopyCategoryPlus.map τ)) ≫
        r.mapDerivedCategoryPlusFactorsh.inv.app (Γ.mapHomotopyCategoryPlus.obj J') ≫
        r.mapDerivedCategoryPlus.map
          (rightDerivedFunctorPlusObjSingleIsoOfResolution Γ ι' hι' hJ').inv := by
  have := isIso_rightDerivedFunctorPlusUnit_app_of_rightAcyclic Γ₀ J hJ
  have := isIso_rightDerivedFunctorPlusUnit_app_of_rightAcyclic Γ J' hJ'
  let e := singleFunctorPlusObjIsoQhOfIsIso ι hι
  let e' := singleFunctorPlusObjIsoQhOfIsIso ι' hι'
  -- the derived comparison, read after the unit of `RΓ₀` at `J`
  have core : Γ₀.rightDerivedFunctorPlusUnith.app J ≫ Γ₀.rightDerivedFunctorPlus.map e.inv ≫
      derivedSquareMap α X ≫ r.mapDerivedCategoryPlus.map (Γ.rightDerivedFunctorPlus.map e'.hom) =
        DerivedCategory.Plus.Qh.map ((mapHomotopyCategoryPlusNatTrans α).app J ≫
          r.mapHomotopyCategoryPlus.map (Γ.mapHomotopyCategoryPlus.map τ)) ≫
        r.mapDerivedCategoryPlusFactorsh.inv.app (Γ.mapHomotopyCategoryPlus.obj J') ≫
        r.mapDerivedCategoryPlus.map (Γ.rightDerivedFunctorPlusUnith.app J') := by
    have hnat := (derivedSquareTrans' α).naturality e.inv
    simp only [Functor.comp_map] at hnat
    rw [derivedSquareMap]
    simp only [Category.assoc]
    rw [reassoc_of% hnat, reassoc_of% (unit_comp_derivedSquareTrans'_app α J)]
    have hk : P.mapDerivedCategoryPlusFactorsh.inv.app J ≫ P.mapDerivedCategoryPlus.map e.inv ≫
        (P.mapDerivedCategoryPlusObjSingleIso X).hom ≫ e'.hom = DerivedCategory.Plus.Qh.map τ :=
      resolution_key ι hι ι' hι' τ hτ
    have hk2 : r.mapDerivedCategoryPlus.map
          (Γ.rightDerivedFunctorPlus.map (P.mapDerivedCategoryPlusFactorsh.inv.app J)) ≫
        r.mapDerivedCategoryPlus.map
          (Γ.rightDerivedFunctorPlus.map (P.mapDerivedCategoryPlus.map e.inv)) ≫
        r.mapDerivedCategoryPlus.map
          (Γ.rightDerivedFunctorPlus.map (P.mapDerivedCategoryPlusObjSingleIso X).hom) ≫
        r.mapDerivedCategoryPlus.map (Γ.rightDerivedFunctorPlus.map e'.hom) =
          r.mapDerivedCategoryPlus.map
            (Γ.rightDerivedFunctorPlus.map (DerivedCategory.Plus.Qh.map τ)) := by
      simp only [← Functor.map_comp, hk]
    have hu := Γ.rightDerivedFunctorPlusUnith.naturality τ
    simp only [Functor.comp_map] at hu
    have hu2 : r.mapDerivedCategoryPlus.map
          (Γ.rightDerivedFunctorPlusUnith.app (P.mapHomotopyCategoryPlus.obj J)) ≫
        r.mapDerivedCategoryPlus.map
          (Γ.rightDerivedFunctorPlus.map (DerivedCategory.Plus.Qh.map τ)) =
        r.mapDerivedCategoryPlus.map
          (DerivedCategory.Plus.Qh.map (Γ.mapHomotopyCategoryPlus.map τ)) ≫
        r.mapDerivedCategoryPlus.map (Γ.rightDerivedFunctorPlusUnith.app J') := by
      simp only [← Functor.map_comp, hu]
    have hr := r.mapDerivedCategoryPlusFactorsh.inv.naturality (Γ.mapHomotopyCategoryPlus.map τ)
    simp only [Functor.comp_map] at hr
    simpa only [derivedSquareNu, Functor.comp_map, Category.assoc] using
      bookkeeping (DerivedCategory.Plus.Qh.map ((mapHomotopyCategoryPlusNatTrans α).app J))
        _ _ _ _ _ _ _ _ _ _ _ _ (Functor.map_comp _ _ _) hk2 hu2 hr
  have hΦ₀ : (rightDerivedFunctorPlusObjSingleIsoOfResolution Γ₀ ι hι hJ).hom =
      Γ₀.rightDerivedFunctorPlus.map e.hom ≫
        CategoryTheory.inv (Γ₀.rightDerivedFunctorPlusUnith.app J) := rfl
  have hΦ' : (rightDerivedFunctorPlusObjSingleIsoOfResolution Γ ι' hι' hJ').inv =
      Γ.rightDerivedFunctorPlusUnith.app J' ≫ Γ.rightDerivedFunctorPlus.map e'.inv := rfl
  rw [hΦ₀, hΦ', Functor.map_comp r.mapDerivedCategoryPlus, ← reassoc_of% core]
  simp only [Category.assoc, IsIso.inv_hom_id_assoc, ← Functor.map_comp_assoc, Iso.hom_inv_id,
    Functor.map_id, Category.id_comp]
  rw [← Functor.map_comp, ← Functor.map_comp, Iso.hom_inv_id, Functor.map_id, Functor.map_id,
    Category.comp_id]

/-- **The derived comparison of a square is an isomorphism when it is one on resolutions**: in the
situation of `derivedSquareMap_eq_of_resolutions`, with `ι` and `ι'` quasi-isomorphisms, if the
map of complexes `Γ₀(J) ⟶ r(Γ(J'))` (`α` applied degreewise followed by `r(Γ(τ))`) is a
quasi-isomorphism, then `derivedSquareMap α X` is an isomorphism. -/
theorem isIso_derivedSquareMap_of_resolutions (α : Γ₀ ⟶ P ⋙ Γ ⋙ r) {X : C₀}
    {J : HomotopyCategory.Plus C₀} (ι : (HomotopyCategory.Plus.singleFunctor C₀ 0).obj X ⟶ J)
    (hι : HomotopyCategory.Plus.quasiIso C₀ ι) (hJ : ∀ n : ℤ, Γ₀.rightAcyclic (J.obj.as.X n))
    {J' : HomotopyCategory.Plus C}
    (ι' : (HomotopyCategory.Plus.singleFunctor C 0).obj (P.obj X) ⟶ J')
    (hι' : HomotopyCategory.Plus.quasiIso C ι') (hJ' : ∀ n : ℤ, Γ.rightAcyclic (J'.obj.as.X n))
    (τ : P.mapHomotopyCategoryPlus.obj J ⟶ J')
    (hτ : P.mapHomotopyCategoryPlus.map ι ≫ τ =
      (P.mapHomotopyCategoryPlusObjSingleIso 0 X).hom ≫ ι')
    (hα : HomotopyCategory.Plus.quasiIso M₀ ((mapHomotopyCategoryPlusNatTrans α).app J ≫
      r.mapHomotopyCategoryPlus.map (Γ.mapHomotopyCategoryPlus.map τ))) :
    IsIso (derivedSquareMap α X) := by
  rw [derivedSquareMap_eq_of_resolutions α ι (isIso_Qh_map_of_mem_quasiIso ι hι) hJ ι'
    (isIso_Qh_map_of_mem_quasiIso ι' hι') hJ' τ hτ]
  have := isIso_Qh_map_of_mem_quasiIso _ hα
  infer_instance

omit [EnoughInjectives C₀] [EnoughInjectives C] in
/-- The image under an exact functor `P` of a resolution `ι : X[0] ⟶ J` is a resolution
`(P X)[0] ≅ P(X[0]) ⟶ P(J)`: it is still inverted by the localization. -/
theorem isIso_Qh_map_mapHomotopyCategoryPlusResolution {X : C₀} {J : HomotopyCategory.Plus C₀}
    (ι : (HomotopyCategory.Plus.singleFunctor C₀ 0).obj X ⟶ J)
    (hι : IsIso (DerivedCategory.Plus.Qh.map ι)) :
    IsIso (DerivedCategory.Plus.Qh.map ((P.mapHomotopyCategoryPlusObjSingleIso 0 X).inv ≫
      P.mapHomotopyCategoryPlus.map ι)) := by
  rw [Functor.map_comp]
  have : IsIso (P.mapDerivedCategoryPlusFactorsh.hom.app _ ≫
      DerivedCategory.Plus.Qh.map (P.mapHomotopyCategoryPlus.map ι)) := by
    rw [← mapDerivedCategoryPlus_map_Qh_map_comp_factorsh P]
    infer_instance
  have := IsIso.of_isIso_comp_left (P.mapDerivedCategoryPlusFactorsh.hom.app _)
    (DerivedCategory.Plus.Qh.map (P.mapHomotopyCategoryPlus.map ι))
  infer_instance

/-- **The derived comparison of a square on one acyclic resolution.**  Let `ι : X[0] ⟶ J` be a
quasi-isomorphism onto a bounded below complex of `Γ₀`-acyclic objects whose image `P(J)` is a
complex of `Γ`-acyclic objects.  Then, under `RΓ₀(X[0]) ≅ Γ₀(J)` and `RΓ((P X)[0]) ≅ Γ(P(J))`
(the latter through the resolution `P(ι)` of `P X`), `derivedSquareMap α X` is the class of the
map of complexes `Γ₀(J) ⟶ r(Γ(P(J)))` given by `α` applied degreewise. -/
theorem derivedSquareMap_eq_of_resolution (α : Γ₀ ⟶ P ⋙ Γ ⋙ r) {X : C₀}
    {J : HomotopyCategory.Plus C₀} (ι : (HomotopyCategory.Plus.singleFunctor C₀ 0).obj X ⟶ J)
    (hι : IsIso (DerivedCategory.Plus.Qh.map ι)) (hJ : ∀ n : ℤ, Γ₀.rightAcyclic (J.obj.as.X n))
    (hPJ : ∀ n : ℤ, Γ.rightAcyclic (P.obj (J.obj.as.X n))) :
    derivedSquareMap α X =
      (rightDerivedFunctorPlusObjSingleIsoOfResolution Γ₀ ι hι hJ).hom ≫
        DerivedCategory.Plus.Qh.map ((mapHomotopyCategoryPlusNatTrans α).app J) ≫
        r.mapDerivedCategoryPlusFactorsh.inv.app
          (Γ.mapHomotopyCategoryPlus.obj (P.mapHomotopyCategoryPlus.obj J)) ≫
        r.mapDerivedCategoryPlus.map (rightDerivedFunctorPlusObjSingleIsoOfResolution Γ
          ((P.mapHomotopyCategoryPlusObjSingleIso 0 X).inv ≫ P.mapHomotopyCategoryPlus.map ι)
          (isIso_Qh_map_mapHomotopyCategoryPlusResolution ι hι) hPJ).inv := by
  refine (derivedSquareMap_eq_of_resolutions α ι hι hJ _
    (isIso_Qh_map_mapHomotopyCategoryPlusResolution ι hι) hPJ (𝟙 _)
    (by rw [Category.comp_id, Iso.hom_inv_id_assoc])).trans ?_
  rw [Functor.map_id, Functor.map_id]
  exact congrArg (fun f => _ ≫ DerivedCategory.Plus.Qh.map f ≫ _)
    (Category.comp_id ((mapHomotopyCategoryPlusNatTrans α).app J))

/-- **The derived comparison of a square is an isomorphism when it is one on a resolution**: in
the situation of `derivedSquareMap_eq_of_resolution`, with `ι` a quasi-isomorphism, if `α`
applied degreewise, `Γ₀(J) ⟶ r(Γ(P(J)))`, is a quasi-isomorphism, then `derivedSquareMap α X` is
an isomorphism. -/
theorem isIso_derivedSquareMap_of_resolution (α : Γ₀ ⟶ P ⋙ Γ ⋙ r) {X : C₀}
    {J : HomotopyCategory.Plus C₀} (ι : (HomotopyCategory.Plus.singleFunctor C₀ 0).obj X ⟶ J)
    (hι : HomotopyCategory.Plus.quasiIso C₀ ι) (hJ : ∀ n : ℤ, Γ₀.rightAcyclic (J.obj.as.X n))
    (hPJ : ∀ n : ℤ, Γ.rightAcyclic (P.obj (J.obj.as.X n)))
    (hα : HomotopyCategory.Plus.quasiIso M₀ ((mapHomotopyCategoryPlusNatTrans α).app J)) :
    IsIso (derivedSquareMap α X) := by
  rw [derivedSquareMap_eq_of_resolution α ι (isIso_Qh_map_of_mem_quasiIso ι hι) hJ hPJ]
  exact IsIso.comp_isIso' inferInstance
    (IsIso.comp_isIso' (isIso_Qh_map_of_mem_quasiIso _ hα)
      (IsIso.comp_isIso' (Iso.isIso_hom ((r.mapDerivedCategoryPlusFactorsh.app _).symm))
        inferInstance))

end Square

end CategoryTheory.Functor
