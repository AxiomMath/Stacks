module

public import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedSquareTransComposition
public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlusResolution

/-!
# Derived comparison maps of squares, computed on a resolution

For additive functors `Γ₀ : C₀ ⥤ M₀`, `P : C₀ ⥤ C`, `Γ : C ⥤ M`, `r : M ⥤ M₀` and a
transformation `α : Γ₀ ⟶ P ⋙ Γ ⋙ r`, the derived comparison `derivedSquareMap α X` is computed on
a resolution `X[0] ⟶ K` of `X` whose terms are acyclic for `Γ₀` and are sent by `P` to
`Γ`-acyclic objects: under the identifications `RΓ₀(X) ≅ Γ₀(K)` and `RΓ(P X) ≅ Γ(P K)` it is the
class of the degreewise map `α_K`.  The same holds for a pasting of two such squares with a
composition of the restriction functors.

## Main results

* `Functor.rightDerivedFunctorPlusResolutionIso` — `RΓ(X[0]) ≅ Qh(Γ(K))` for a resolution `K`
  on which the unit of `RΓ` is invertible.
* `Functor.pushResolution` — the image `P(X)[0] ⟶ P(K)` of a resolution.
* `Functor.derivedSquareMap_comp_resolutionIso` — `derivedSquareMap α X` on a resolution.
* `Functor.derivedSquareMap_transition_resolutionIso` — the same for a pasted square.
* `Functor.mapDerivedCategoryPlusCompTransOfComp` — the derived transformation
  `r₂⁺ ⋙ r₁⁺ ⟶ r⁺` induced by `r₂ ⋙ r₁ ⟶ r` on bounded below derived categories.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

namespace CategoryTheory.Functor

section Resolution

variable {C : Type*} [Category* C] [Abelian C] [HasDerivedCategory C] [EnoughInjectives C]
  {M : Type*} [Category* M] [Abelian M] [HasDerivedCategory M] (Γ : C ⥤ M) [Γ.Additive]

/-- A morphism `X[0] ⟶ K` of the bounded below homotopy category inverted by the localization,
read as an isomorphism `X[0] ≅ Qh(K)` of the bounded below derived category. -/
def resolutionQhIso {X : C} {K : HomotopyCategory.Plus C}
    (r : (HomotopyCategory.Plus.singleFunctor C 0).obj X ⟶ K)
    [IsIso (DerivedCategory.Plus.Qh.map r)] :
    (DerivedCategory.Plus.singleFunctor C 0).obj X ≅ DerivedCategory.Plus.Qh.obj K :=
  (singleFunctorPlusIsoCompQh (A := C) 0).app X ≪≫
    asIso (DerivedCategory.Plus.Qh.map r)

/-- **The right derived functor computed on a resolution**: for `r : X[0] ⟶ K` inverted by the
localization and `K` a complex on which the unit of `RΓ` is invertible (e.g. a bounded below
complex of `Γ`-acyclic objects), `RΓ(X[0]) ≅ Qh(Γ(K))`. -/
def rightDerivedFunctorPlusResolutionIso {X : C} {K : HomotopyCategory.Plus C}
    (r : (HomotopyCategory.Plus.singleFunctor C 0).obj X ⟶ K)
    [IsIso (DerivedCategory.Plus.Qh.map r)] [IsIso (Γ.rightDerivedFunctorPlusUnith.app K)] :
    Γ.rightDerivedFunctorPlus.obj ((DerivedCategory.Plus.singleFunctor C 0).obj X) ≅
      DerivedCategory.Plus.Qh.obj (Γ.mapHomotopyCategoryPlus.obj K) :=
  Γ.rightDerivedFunctorPlus.mapIso (resolutionQhIso r) ≪≫
    (asIso (Γ.rightDerivedFunctorPlusUnith.app K)).symm

/-- **The identification on a resolution is natural**: a morphism `f : X ⟶ X'` covered by a
morphism `g : K ⟶ K'` of resolutions is computed by `Γ(g)`. -/
theorem rightDerivedFunctorPlusResolutionIso_naturality {X X' : C} {K K' : HomotopyCategory.Plus C}
    (r : (HomotopyCategory.Plus.singleFunctor C 0).obj X ⟶ K)
    (r' : (HomotopyCategory.Plus.singleFunctor C 0).obj X' ⟶ K')
    [IsIso (DerivedCategory.Plus.Qh.map r)] [IsIso (Γ.rightDerivedFunctorPlusUnith.app K)]
    [IsIso (DerivedCategory.Plus.Qh.map r')] [IsIso (Γ.rightDerivedFunctorPlusUnith.app K')]
    (f : X ⟶ X') (g : K ⟶ K')
    (h : (HomotopyCategory.Plus.singleFunctor C 0).map f ≫ r' = r ≫ g) :
    Γ.rightDerivedFunctorPlus.map ((DerivedCategory.Plus.singleFunctor C 0).map f) ≫
        (rightDerivedFunctorPlusResolutionIso Γ r').hom =
      (rightDerivedFunctorPlusResolutionIso Γ r).hom ≫
        DerivedCategory.Plus.Qh.map (Γ.mapHomotopyCategoryPlus.map g) := by
  have e₁ : (DerivedCategory.Plus.singleFunctor C 0).map f ≫ (resolutionQhIso r').hom =
      (resolutionQhIso r).hom ≫ DerivedCategory.Plus.Qh.map g := by
    simp only [resolutionQhIso, Iso.trans_hom, Iso.app_hom, asIso_hom, ← Category.assoc,
      (singleFunctorPlusIsoCompQh (A := C) 0).hom.naturality f]
    simp only [Functor.comp_map, Category.assoc, ← Functor.map_comp, h]
  have e₂ := Γ.rightDerivedFunctorPlusUnith.naturality g
  simp only [rightDerivedFunctorPlusResolutionIso, Iso.trans_hom, Functor.mapIso_hom,
    Iso.symm_hom, asIso_inv, Category.assoc, ← Functor.map_comp_assoc, e₁]
  simp only [Functor.map_comp, Category.assoc]
  congr 1
  rw [IsIso.eq_inv_comp, ← Category.assoc, IsIso.comp_inv_eq]
  exact e₂.symm

end Resolution

section Push

variable {C₀ : Type*} [Category* C₀] [Abelian C₀] [HasDerivedCategory C₀] [EnoughInjectives C₀]
  {C : Type*} [Category* C] [Abelian C] [HasDerivedCategory C]
  (P : C₀ ⥤ C) [P.Additive] [PreservesFiniteLimits P] [PreservesFiniteColimits P]

/-- **A resolution pushed along an exact functor**: `P(X)[0] ≅ P(X[0]) ⟶ P(K)`. -/
def pushResolution {X : C₀} {K : HomotopyCategory.Plus C₀}
    (r : (HomotopyCategory.Plus.singleFunctor C₀ 0).obj X ⟶ K) :
    (HomotopyCategory.Plus.singleFunctor C 0).obj (P.obj X) ⟶ P.mapHomotopyCategoryPlus.obj K :=
  (P.mapHomotopyCategoryPlusObjSingleIso 0 X).inv ≫ P.mapHomotopyCategoryPlus.map r

omit [EnoughInjectives C₀] in
/-- An exact functor carries a morphism inverted by the localization to one. -/
theorem isIso_Qh_map_mapHomotopyCategoryPlus_map {K L : HomotopyCategory.Plus C₀} (f : K ⟶ L)
    [IsIso (DerivedCategory.Plus.Qh.map f)] :
    IsIso (DerivedCategory.Plus.Qh.map (P.mapHomotopyCategoryPlus.map f)) := by
  have h := P.mapDerivedCategoryPlusFactorsh.hom.naturality f
  have : DerivedCategory.Plus.Qh.map (P.mapHomotopyCategoryPlus.map f) =
      P.mapDerivedCategoryPlusFactorsh.inv.app K ≫
        P.mapDerivedCategoryPlus.map (DerivedCategory.Plus.Qh.map f) ≫
          P.mapDerivedCategoryPlusFactorsh.hom.app L := by
    simp only [Functor.comp_map] at h
    rw [h, Iso.inv_hom_id_app_assoc]
  rw [this]
  infer_instance

/-- A pushed resolution is again inverted by the localization. -/
instance isIso_Qh_map_pushResolution {X : C₀} {K : HomotopyCategory.Plus C₀}
    (r : (HomotopyCategory.Plus.singleFunctor C₀ 0).obj X ⟶ K)
    [IsIso (DerivedCategory.Plus.Qh.map r)] :
    IsIso (DerivedCategory.Plus.Qh.map (pushResolution P r)) := by
  have := isIso_Qh_map_mapHomotopyCategoryPlus_map P r
  rw [pushResolution, Functor.map_comp]
  infer_instance

/-- **The pushed resolution, read in the derived category**, is the image of the resolution under
the induced functor of `P`. -/
theorem resolutionQhIso_pushResolution_hom {X : C₀} {K : HomotopyCategory.Plus C₀}
    (r : (HomotopyCategory.Plus.singleFunctor C₀ 0).obj X ⟶ K)
    [IsIso (DerivedCategory.Plus.Qh.map r)] :
    (resolutionQhIso (pushResolution P r)).hom =
      (P.mapDerivedCategoryPlusObjSingleIso X).inv ≫
        P.mapDerivedCategoryPlus.map (resolutionQhIso r).hom ≫
          P.mapDerivedCategoryPlusFactorsh.hom.app K := by
  refine (Iso.eq_inv_comp (P.mapDerivedCategoryPlusObjSingleIso X)).2 ?_
  rw [mapDerivedCategoryPlusObjSingleIso_hom P X]
  have h := P.mapDerivedCategoryPlusFactorsh.hom.naturality r
  simp only [Functor.comp_map] at h
  let d := singleFunctorPlusIsoCompQh (A := C) 0
  let c := P.mapHomotopyCategoryPlusObjSingleIso 0 X
  rw [Category.assoc, Category.assoc, Category.assoc]
  change _ ≫ _ ≫ DerivedCategory.Plus.Qh.map c.hom ≫ d.inv.app (P.obj X) ≫ d.hom.app (P.obj X) ≫
      DerivedCategory.Plus.Qh.map (c.inv ≫ P.mapHomotopyCategoryPlus.map r) =
    P.mapDerivedCategoryPlus.map ((singleFunctorPlusIsoCompQh (A := C₀) 0).hom.app X ≫
      DerivedCategory.Plus.Qh.map r) ≫ P.mapDerivedCategoryPlusFactorsh.hom.app K
  rw [Iso.inv_hom_id_app_assoc d (P.obj X), DerivedCategory.Plus.Qh.map_comp,
    ← DerivedCategory.Plus.Qh.map_comp_assoc, c.hom_inv_id, DerivedCategory.Plus.Qh.map_id,
    Category.id_comp, P.mapDerivedCategoryPlus.map_comp, Category.assoc, h]

end Push

section One

variable {C₀ : Type*} [Category* C₀] [Abelian C₀] [HasDerivedCategory C₀] [EnoughInjectives C₀]
  {C : Type*} [Category* C] [Abelian C] [HasDerivedCategory C] [EnoughInjectives C]
  {M₀ : Type*} [Category* M₀] [Abelian M₀] [HasDerivedCategory M₀]
  {M : Type*} [Category* M] [Abelian M] [HasDerivedCategory M] [EnoughInjectives M]
  {Γ₀ : C₀ ⥤ M₀} {Γ : C ⥤ M} {P : C₀ ⥤ C} {r : M ⥤ M₀}
  [Γ₀.Additive] [Γ.Additive] [P.Additive] [r.Additive]
  [PreservesFiniteLimits P] [PreservesFiniteColimits P]
  [PreservesFiniteLimits r] [PreservesFiniteColimits r]

/-- **The derived comparison of a square, computed on a resolution.**  For a resolution
`X[0] ⟶ K` on which the unit of `RΓ₀` is invertible, and on whose image `P(K)` the unit of `RΓ`
is invertible, the derived comparison `RΓ₀(X[0]) ⟶ r̄(RΓ(P(X)[0]))` is, through the two
identifications `RΓ₀(X[0]) ≅ Qh(Γ₀(K))` and `r̄(RΓ(P(X)[0])) ≅ Qh(r(Γ(P(K))))`, the underived `α`
applied degreewise to `K`. -/
theorem derivedSquareMap_comp_resolutionIso (α : Γ₀ ⟶ P ⋙ Γ ⋙ r) (X : C₀)
    {K : HomotopyCategory.Plus C₀} (res : (HomotopyCategory.Plus.singleFunctor C₀ 0).obj X ⟶ K)
    [IsIso (DerivedCategory.Plus.Qh.map res)] [IsIso (Γ₀.rightDerivedFunctorPlusUnith.app K)]
    [IsIso (Γ.rightDerivedFunctorPlusUnith.app (P.mapHomotopyCategoryPlus.obj K))] :
    derivedSquareMap α X ≫
        r.mapDerivedCategoryPlus.map
          (Γ.rightDerivedFunctorPlusResolutionIso (pushResolution P res)).hom ≫
        r.mapDerivedCategoryPlusFactorsh.hom.app
          (Γ.mapHomotopyCategoryPlus.obj (P.mapHomotopyCategoryPlus.obj K)) =
      (Γ₀.rightDerivedFunctorPlusResolutionIso res).hom ≫
        DerivedCategory.Plus.Qh.map ((Functor.mapHomotopyCategoryPlusNatTrans α).app K) := by
  let ρ := resolutionQhIso res
  have e1 : (derivedSquareTrans' α).app ((DerivedCategory.Plus.singleFunctor C₀ 0).obj X) =
      Γ₀.rightDerivedFunctorPlus.map ρ.hom ≫
        (derivedSquareTrans' α).app (DerivedCategory.Plus.Qh.obj K) ≫
          (P.mapDerivedCategoryPlus ⋙ Γ.rightDerivedFunctorPlus ⋙ r.mapDerivedCategoryPlus).map
            ρ.inv := by
    rw [← Category.assoc, (derivedSquareTrans' α).naturality, Category.assoc,
      ← Functor.map_comp, ρ.hom_inv_id, Functor.map_id, Category.comp_id]
  have e2 : (derivedSquareTrans' α).app (DerivedCategory.Plus.Qh.obj K) =
      CategoryTheory.inv (Γ₀.rightDerivedFunctorPlusUnith.app K) ≫
        (DerivedCategory.Plus.Qh.map ((Functor.mapHomotopyCategoryPlusNatTrans α).app K) :
          DerivedCategory.Plus.Qh.obj (Γ₀.mapHomotopyCategoryPlus.obj K) ⟶
            DerivedCategory.Plus.Qh.obj (r.mapHomotopyCategoryPlus.obj
              (Γ.mapHomotopyCategoryPlus.obj (P.mapHomotopyCategoryPlus.obj K)))) ≫
          derivedSquareNu Γ r (P.mapHomotopyCategoryPlus.obj K) ≫
            r.mapDerivedCategoryPlus.map (Γ.rightDerivedFunctorPlus.map
              (P.mapDerivedCategoryPlusFactorsh.inv.app K)) := by
    rw [IsIso.eq_inv_comp]
    exact unit_comp_derivedSquareTrans'_app α K
  have e3 := resolutionQhIso_pushResolution_hom P res
  have hmid : P.mapDerivedCategoryPlusFactorsh.inv.app K ≫ P.mapDerivedCategoryPlus.map ρ.inv ≫
      (P.mapDerivedCategoryPlusObjSingleIso X).hom ≫ (resolutionQhIso (pushResolution P res)).hom =
        𝟙 _ := by
    rw [e3, Iso.hom_inv_id_assoc, ← Functor.map_comp_assoc, ρ.inv_hom_id, Functor.map_id,
      Category.id_comp, Iso.inv_hom_id_app]
  have htail : derivedSquareNu Γ r (P.mapHomotopyCategoryPlus.obj K) ≫
      r.mapDerivedCategoryPlus.map
        (Γ.rightDerivedFunctorPlus.map (P.mapDerivedCategoryPlusFactorsh.inv.app K)) ≫
      r.mapDerivedCategoryPlus.map (Γ.rightDerivedFunctorPlus.map
        (P.mapDerivedCategoryPlus.map ρ.inv)) ≫
      r.mapDerivedCategoryPlus.map (Γ.rightDerivedFunctorPlus.map
        (P.mapDerivedCategoryPlusObjSingleIso X).hom) ≫
      r.mapDerivedCategoryPlus.map
        (Γ.rightDerivedFunctorPlusResolutionIso (pushResolution P res)).hom ≫
      r.mapDerivedCategoryPlusFactorsh.hom.app
        (Γ.mapHomotopyCategoryPlus.obj (P.mapHomotopyCategoryPlus.obj K)) = 𝟙 _ := by
    have hmid' : Γ.rightDerivedFunctorPlus.map (P.mapDerivedCategoryPlusFactorsh.inv.app K) ≫
        Γ.rightDerivedFunctorPlus.map (P.mapDerivedCategoryPlus.map ρ.inv) ≫
        Γ.rightDerivedFunctorPlus.map (P.mapDerivedCategoryPlusObjSingleIso X).hom ≫
        Γ.rightDerivedFunctorPlus.map (resolutionQhIso (pushResolution P res)).hom = 𝟙 _ := by
      rw [← Γ.rightDerivedFunctorPlus.map_comp, ← Γ.rightDerivedFunctorPlus.map_comp,
        ← Γ.rightDerivedFunctorPlus.map_comp, hmid, Γ.rightDerivedFunctorPlus.map_id]
    have h2 : r.mapDerivedCategoryPlus.map
          (Γ.rightDerivedFunctorPlusUnith.app (P.mapHomotopyCategoryPlus.obj K)) ≫
        r.mapDerivedCategoryPlus.map
          (Γ.rightDerivedFunctorPlus.map (P.mapDerivedCategoryPlusFactorsh.inv.app K)) ≫
        r.mapDerivedCategoryPlus.map (Γ.rightDerivedFunctorPlus.map
          (P.mapDerivedCategoryPlus.map ρ.inv)) ≫
        r.mapDerivedCategoryPlus.map (Γ.rightDerivedFunctorPlus.map
          (P.mapDerivedCategoryPlusObjSingleIso X).hom) ≫
        r.mapDerivedCategoryPlus.map
          (Γ.rightDerivedFunctorPlus.map (resolutionQhIso (pushResolution P res)).hom ≫
            CategoryTheory.inv (Γ.rightDerivedFunctorPlusUnith.app
              (P.mapHomotopyCategoryPlus.obj K))) = 𝟙 _ := by
      rw [← r.mapDerivedCategoryPlus.map_comp, ← r.mapDerivedCategoryPlus.map_comp,
        ← r.mapDerivedCategoryPlus.map_comp, ← r.mapDerivedCategoryPlus.map_comp,
        reassoc_of% hmid', IsIso.hom_inv_id, r.mapDerivedCategoryPlus.map_id]
    simp only [derivedSquareNu, rightDerivedFunctorPlusResolutionIso, Iso.trans_hom,
      Functor.mapIso_hom, Iso.symm_hom, asIso_inv]
    simp only [Category.assoc]
    rw [reassoc_of% h2, Iso.inv_hom_id_app]
    rfl
  rw [derivedSquareMap, e1, e2]
  simp only [Functor.comp_map, Category.assoc]
  rw [htail, Category.comp_id]
  simp only [rightDerivedFunctorPlusResolutionIso, Iso.trans_hom, Functor.mapIso_hom,
    Iso.symm_hom, asIso_inv, Category.assoc]
  rfl

end One

section Composition

/-- Conjugating a commutative square by two isomorphisms. -/
private lemma comp_hom_eq_of_inv_comp_eq {𝒦 : Type*} [Category* 𝒦] {A B C D : 𝒦} (e₁ : B ≅ A)
    (e₂ : D ≅ C) (b : B ⟶ D) (c : A ⟶ C) (h : e₁.inv ≫ b = c ≫ e₂.inv) :
    b ≫ e₂.hom = e₁.hom ≫ c := by
  rw [← cancel_epi e₁.inv, ← Category.assoc, h, Category.assoc, Iso.inv_hom_id,
    Category.comp_id, Iso.inv_hom_id_assoc]

variable {C₀ : Type*} [Category* C₀] [Abelian C₀] [HasDerivedCategory C₀] [EnoughInjectives C₀]
  {C₁ : Type*} [Category* C₁] [Abelian C₁] [HasDerivedCategory C₁] [EnoughInjectives C₁]
  {C₂ : Type*} [Category* C₂] [Abelian C₂] [HasDerivedCategory C₂] [EnoughInjectives C₂]
  {M₀ : Type*} [Category* M₀] [Abelian M₀] [HasDerivedCategory M₀]
  {M₁ : Type*} [Category* M₁] [Abelian M₁] [HasDerivedCategory M₁] [EnoughInjectives M₁]
  {M₂ : Type*} [Category* M₂] [Abelian M₂] [HasDerivedCategory M₂] [EnoughInjectives M₂]
  {Γ₁ : C₁ ⥤ M₁} {Γ₂ : C₂ ⥤ M₂} [Γ₁.Additive] [Γ₂.Additive]
  {P₁ : C₀ ⥤ C₁} {P₂ : C₁ ⥤ C₂} {P : C₀ ⥤ C₂} [P₁.Additive] [P₂.Additive] [P.Additive]
  [PreservesFiniteLimits P₁] [PreservesFiniteColimits P₁]
  [PreservesFiniteLimits P₂] [PreservesFiniteColimits P₂]
  [PreservesFiniteLimits P] [PreservesFiniteColimits P]
  {r₁ : M₁ ⥤ M₀} {r₂ : M₂ ⥤ M₁} {r : M₂ ⥤ M₀} [r₁.Additive] [r₂.Additive] [r.Additive]
  [PreservesFiniteLimits r₁] [PreservesFiniteColimits r₁]
  [PreservesFiniteLimits r₂] [PreservesFiniteColimits r₂]
  [PreservesFiniteLimits r] [PreservesFiniteColimits r]

omit [EnoughInjectives C₀] [EnoughInjectives M₁] in
/-- **The derived comparison of a second square, computed on a resolution pushed along the first
pullback.**  For a square `α₂ : Γ₁ ⟶ P₂ ⋙ Γ₂ ⋙ r₂` following a pullback `P₁`, an isomorphism
`c : P₁ ⋙ P₂ ≅ P`, and comparisons `ρ₀`, `ρ` of the restrictions with the compatibility `hρ`, the
"transition" `r̄₁(RΓ₁(P₁X[0])) ⟶ r̄(RΓ₂(P X[0]))` built from the derived comparison of `α₂` is,
through the identifications on the pushed resolutions, the degreewise underived transition
`r₁(α₂) ≫ ρ₀ ≫ r(Γ₂(g))`, for any `g : P₂(P₁(K)) ⟶ P(K)` covering `c` on the resolutions. -/
theorem derivedSquareMap_transition_resolutionIso (α₂ : Γ₁ ⟶ P₂ ⋙ Γ₂ ⋙ r₂) (c : P₁ ⋙ P₂ ≅ P)
    (ρ₀ : r₂ ⋙ r₁ ⟶ r)
    (ρ : r₂.mapDerivedCategoryPlus ⋙ r₁.mapDerivedCategoryPlus ⟶ r.mapDerivedCategoryPlus)
    (hρ : ∀ L : HomotopyCategory.Plus M₂,
      r₁.mapDerivedCategoryPlusFactorsh.inv.app (r₂.mapHomotopyCategoryPlus.obj L) ≫
          r₁.mapDerivedCategoryPlus.map (r₂.mapDerivedCategoryPlusFactorsh.inv.app L) ≫
            ρ.app (DerivedCategory.Plus.Qh.obj L) =
        DerivedCategory.Plus.Qh.map ((Functor.mapHomotopyCategoryPlusNatTrans ρ₀).app L) ≫
          r.mapDerivedCategoryPlusFactorsh.inv.app L)
    (X : C₀) {K : HomotopyCategory.Plus C₀}
    (res : (HomotopyCategory.Plus.singleFunctor C₀ 0).obj X ⟶ K)
    [IsIso (DerivedCategory.Plus.Qh.map res)]
    [IsIso (Γ₁.rightDerivedFunctorPlusUnith.app (P₁.mapHomotopyCategoryPlus.obj K))]
    [IsIso (Γ₂.rightDerivedFunctorPlusUnith.app
      (P₂.mapHomotopyCategoryPlus.obj (P₁.mapHomotopyCategoryPlus.obj K)))]
    [IsIso (Γ₂.rightDerivedFunctorPlusUnith.app (P.mapHomotopyCategoryPlus.obj K))]
    (g : P₂.mapHomotopyCategoryPlus.obj (P₁.mapHomotopyCategoryPlus.obj K) ⟶
      P.mapHomotopyCategoryPlus.obj K)
    (hg : (HomotopyCategory.Plus.singleFunctor C₂ 0).map (c.hom.app X) ≫ pushResolution P res =
      pushResolution P₂ (pushResolution P₁ res) ≫ g) :
    r₁.mapDerivedCategoryPlus.map (derivedSquareMap α₂ (P₁.obj X)) ≫
        ρ.app _ ≫
          r.mapDerivedCategoryPlus.map (Γ₂.rightDerivedFunctorPlus.map
            ((DerivedCategory.Plus.singleFunctor C₂ 0).map (c.hom.app X))) ≫
            r.mapDerivedCategoryPlus.map
              (Γ₂.rightDerivedFunctorPlusResolutionIso (pushResolution P res)).hom ≫
              r.mapDerivedCategoryPlusFactorsh.hom.app
                (Γ₂.mapHomotopyCategoryPlus.obj (P.mapHomotopyCategoryPlus.obj K)) =
      r₁.mapDerivedCategoryPlus.map
          (Γ₁.rightDerivedFunctorPlusResolutionIso (pushResolution P₁ res)).hom ≫
        r₁.mapDerivedCategoryPlusFactorsh.hom.app
          (Γ₁.mapHomotopyCategoryPlus.obj (P₁.mapHomotopyCategoryPlus.obj K)) ≫
          DerivedCategory.Plus.Qh.map
            (r₁.mapHomotopyCategoryPlus.map ((Functor.mapHomotopyCategoryPlusNatTrans α₂).app
                (P₁.mapHomotopyCategoryPlus.obj K)) ≫
              (Functor.mapHomotopyCategoryPlusNatTrans ρ₀).app (Γ₂.mapHomotopyCategoryPlus.obj
                (P₂.mapHomotopyCategoryPlus.obj (P₁.mapHomotopyCategoryPlus.obj K))) ≫
              r.mapHomotopyCategoryPlus.map (Γ₂.mapHomotopyCategoryPlus.map g)) := by
  let res₁ := pushResolution P₁ res
  let res₂ := pushResolution P₂ res₁
  let A₁ := Γ₁.rightDerivedFunctorPlusResolutionIso res₁
  let A₂ := Γ₂.rightDerivedFunctorPlusResolutionIso res₂
  let A := Γ₂.rightDerivedFunctorPlusResolutionIso (pushResolution P res)
  let L := Γ₂.mapHomotopyCategoryPlus.obj
    (P₂.mapHomotopyCategoryPlus.obj (P₁.mapHomotopyCategoryPlus.obj K))
  let α' : Γ₁.mapHomotopyCategoryPlus.obj (P₁.mapHomotopyCategoryPlus.obj K) ⟶
      r₂.mapHomotopyCategoryPlus.obj L :=
    (Functor.mapHomotopyCategoryPlusNatTrans α₂).app (P₁.mapHomotopyCategoryPlus.obj K)
  let E := r₂.mapDerivedCategoryPlus.mapIso A₂ ≪≫ r₂.mapDerivedCategoryPlusFactorsh.app L
  have h3 : derivedSquareMap α₂ (P₁.obj X) ≫ E.hom = A₁.hom ≫ DerivedCategory.Plus.Qh.map α' :=
    derivedSquareMap_comp_resolutionIso α₂ (P₁.obj X) res₁
  have hdSM : derivedSquareMap α₂ (P₁.obj X) = (A₁.hom ≫ DerivedCategory.Plus.Qh.map α') ≫ E.inv :=
    (Iso.eq_comp_inv E).2 h3
  have hR : Γ₂.rightDerivedFunctorPlus.map
        ((DerivedCategory.Plus.singleFunctor C₂ 0).map (c.hom.app X)) ≫ A.hom =
      A₂.hom ≫ DerivedCategory.Plus.Qh.map (Γ₂.mapHomotopyCategoryPlus.map g) :=
    rightDerivedFunctorPlusResolutionIso_naturality Γ₂ res₂ (pushResolution P res) _ g hg
  have hR' : A₂.inv ≫ Γ₂.rightDerivedFunctorPlus.map
        ((DerivedCategory.Plus.singleFunctor C₂ 0).map (c.hom.app X)) ≫ A.hom =
      DerivedCategory.Plus.Qh.map (Γ₂.mapHomotopyCategoryPlus.map g) := by
    rw [hR, Iso.inv_hom_id_assoc]
  have hRρ : (r₂.mapDerivedCategoryPlus ⋙ r₁.mapDerivedCategoryPlus).map A₂.inv ≫ ρ.app _ =
      ρ.app _ ≫ r.mapDerivedCategoryPlus.map A₂.inv := ρ.naturality A₂.inv
  have hfac₁ : r₁.mapDerivedCategoryPlus.map (DerivedCategory.Plus.Qh.map α') ≫
        r₁.mapDerivedCategoryPlusFactorsh.hom.app (r₂.mapHomotopyCategoryPlus.obj L) =
      r₁.mapDerivedCategoryPlusFactorsh.hom.app _ ≫
        DerivedCategory.Plus.Qh.map (r₁.mapHomotopyCategoryPlus.map α') :=
    r₁.mapDerivedCategoryPlusFactorsh.hom.naturality α'
  have hfac : r.mapDerivedCategoryPlus.map
        (DerivedCategory.Plus.Qh.map (Γ₂.mapHomotopyCategoryPlus.map g)) ≫
        r.mapDerivedCategoryPlusFactorsh.hom.app
          (Γ₂.mapHomotopyCategoryPlus.obj (P.mapHomotopyCategoryPlus.obj K)) =
      r.mapDerivedCategoryPlusFactorsh.hom.app L ≫
        DerivedCategory.Plus.Qh.map (r.mapHomotopyCategoryPlus.map
          (Γ₂.mapHomotopyCategoryPlus.map g)) :=
    r.mapDerivedCategoryPlusFactorsh.hom.naturality (Γ₂.mapHomotopyCategoryPlus.map g)
  let ρ₀' : r₁.mapHomotopyCategoryPlus.obj (r₂.mapHomotopyCategoryPlus.obj L) ⟶
      r.mapHomotopyCategoryPlus.obj L := (Functor.mapHomotopyCategoryPlusNatTrans ρ₀).app L
  have h : r₁.mapDerivedCategoryPlusFactorsh.inv.app (r₂.mapHomotopyCategoryPlus.obj L) ≫
      r₁.mapDerivedCategoryPlus.map (r₂.mapDerivedCategoryPlusFactorsh.inv.app L) ≫
        ρ.app (DerivedCategory.Plus.Qh.obj L) =
      DerivedCategory.Plus.Qh.map ρ₀' ≫ r.mapDerivedCategoryPlusFactorsh.inv.app L := hρ L
  have hρL : r₁.mapDerivedCategoryPlus.map (r₂.mapDerivedCategoryPlusFactorsh.inv.app L) ≫
        ρ.app (DerivedCategory.Plus.Qh.obj L) ≫ r.mapDerivedCategoryPlusFactorsh.hom.app L =
      r₁.mapDerivedCategoryPlusFactorsh.hom.app (r₂.mapHomotopyCategoryPlus.obj L) ≫
        DerivedCategory.Plus.Qh.map ρ₀' := by
    rw [← cancel_epi (r₁.mapDerivedCategoryPlusFactorsh.inv.app (r₂.mapHomotopyCategoryPlus.obj L)),
      reassoc_of% h, Iso.inv_hom_id_app, Iso.inv_hom_id_app_assoc]
    exact Category.comp_id _
  have hR'' : (A₂.inv ≫ Γ₂.rightDerivedFunctorPlus.map
        ((DerivedCategory.Plus.singleFunctor C₂ 0).map (c.hom.app X))) ≫ A.hom =
      DerivedCategory.Plus.Qh.map (Γ₂.mapHomotopyCategoryPlus.map g) := by
    rw [Category.assoc]
    exact hR'
  simp only [Functor.comp_map] at hRρ
  have hEinv : E.inv = r₂.mapDerivedCategoryPlusFactorsh.inv.app L ≫
      r₂.mapDerivedCategoryPlus.map A₂.inv := rfl
  rw [hdSM, hEinv]
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% hRρ, ← Functor.map_comp_assoc r.mapDerivedCategoryPlus,
    ← Functor.map_comp_assoc r.mapDerivedCategoryPlus, hR'', hfac,
    reassoc_of% hρL, reassoc_of% hfac₁, ← DerivedCategory.Plus.Qh.map_comp,
    ← DerivedCategory.Plus.Qh.map_comp]

end Composition

section Concrete

variable {C₀ : Type*} [Category* C₀] [Abelian C₀] [HasDerivedCategory C₀] [EnoughInjectives C₀]
  {C₁ : Type*} [Category* C₁] [Abelian C₁] [HasDerivedCategory C₁] [EnoughInjectives C₁]
  {C₂ : Type*} [Category* C₂] [Abelian C₂] [HasDerivedCategory C₂]
  {P₁ : C₀ ⥤ C₁} {P₂ : C₁ ⥤ C₂} {P : C₀ ⥤ C₂} [P₁.Additive] [P₂.Additive] [P.Additive]
  [PreservesFiniteLimits P₁] [PreservesFiniteColimits P₁]
  [PreservesFiniteLimits P₂] [PreservesFiniteColimits P₂]
  [PreservesFiniteLimits P] [PreservesFiniteColimits P]

omit [HasDerivedCategory C₀] [EnoughInjectives C₀] [HasDerivedCategory C₁] [EnoughInjectives C₁]
  [HasDerivedCategory C₂] [PreservesFiniteLimits P₁] [PreservesFiniteColimits P₁]
  [PreservesFiniteLimits P₂] [PreservesFiniteColimits P₂] [PreservesFiniteLimits P]
  [PreservesFiniteColimits P] in
/-- **Pushed resolutions coming from a resolution by a complex are compatible with an isomorphism
`P₁ ⋙ P₂ ≅ P`**: the pushed resolution along `P` is the one pushed along `P₁` and then `P₂`,
followed by the degreewise isomorphism. -/
theorem pushResolution_quotientHomMk_comp (c : P₁ ⋙ P₂ ≅ P) {X : C₀} {L : CochainComplex C₀ ℤ}
    (hL : CochainComplex.plus C₀ L) (ι : (CochainComplex.singleFunctor C₀ 0).obj X ⟶ L)
    (g : P₂.mapHomotopyCategoryPlus.obj (P₁.mapHomotopyCategoryPlus.obj
      ((HomotopyCategory.Plus.quotient C₀).obj ⟨L, hL⟩)) ⟶
        P.mapHomotopyCategoryPlus.obj ((HomotopyCategory.Plus.quotient C₀).obj ⟨L, hL⟩))
    (hg : g.hom = (HomotopyCategory.quotient C₂ _).map
      ((NatTrans.mapHomologicalComplex c.hom (ComplexShape.up ℤ)).app L)) :
    (HomotopyCategory.Plus.singleFunctor C₂ 0).map (c.hom.app X) ≫
        pushResolution P (HomotopyCategory.Plus.quotientHomMk
          (CochainComplex.plus_singleFunctor_obj X) hL ι) =
      pushResolution P₂ (pushResolution P₁ (HomotopyCategory.Plus.quotientHomMk
          (CochainComplex.plus_singleFunctor_obj X) hL ι)) ≫ g := by
  have t3 : (P.mapHomotopyCategoryPlusObjSingleIso 0 X).inv.hom =
      (HomotopyCategory.quotient C₂ _).map
        ((HomologicalComplex.singleMapHomologicalComplex P (ComplexShape.up ℤ) 0).inv.app X) :=
    (HomotopyCategory.Plus.ι C₂).map_preimage _
  have t5 : (P₂.mapHomotopyCategoryPlusObjSingleIso 0 (P₁.obj X)).inv.hom =
      (HomotopyCategory.quotient C₂ _).map
        ((HomologicalComplex.singleMapHomologicalComplex P₂ (ComplexShape.up ℤ) 0).inv.app
          (P₁.obj X)) :=
    (HomotopyCategory.Plus.ι C₂).map_preimage _
  have t6 : (P₁.mapHomotopyCategoryPlusObjSingleIso 0 X).inv.hom =
      (HomotopyCategory.quotient C₁ _).map
        ((HomologicalComplex.singleMapHomologicalComplex P₁ (ComplexShape.up ℤ) 0).inv.app X) :=
    (HomotopyCategory.Plus.ι C₁).map_preimage _
  have t4 : (P₂.mapHomotopyCategoryPlus.map
      (P₁.mapHomotopyCategoryPlusObjSingleIso 0 X).inv).hom =
      (HomotopyCategory.quotient C₂ _).map ((P₂.mapHomologicalComplex (ComplexShape.up ℤ)).map
          ((HomologicalComplex.singleMapHomologicalComplex P₁ (ComplexShape.up ℤ) 0).inv.app
            X)) :=
    (congrArg (P₂.mapHomotopyCategory _).map t6).trans rfl
  simp only [pushResolution, Functor.map_comp, Category.assoc]
  ext
  change (HomotopyCategory.quotient C₂ _).map
        ((HomologicalComplex.single C₂ (ComplexShape.up ℤ) 0).map (c.hom.app X)) ≫
      (P.mapHomotopyCategoryPlusObjSingleIso 0 X).inv.hom ≫
        (HomotopyCategory.quotient C₂ _).map ((P.mapHomologicalComplex _).map ι) =
    (P₂.mapHomotopyCategoryPlusObjSingleIso 0 (P₁.obj X)).inv.hom ≫
      (P₂.mapHomotopyCategoryPlus.map (P₁.mapHomotopyCategoryPlusObjSingleIso 0 X).inv).hom ≫
        (HomotopyCategory.quotient C₂ _).map
          ((P₂.mapHomologicalComplex _).map ((P₁.mapHomologicalComplex _).map ι)) ≫ g.hom
  rw [t3, t4, t5, hg]
  refine (((congrArg (fun t => _ ≫ t) ((HomotopyCategory.quotient C₂ _).map_comp _ _).symm).trans
    ((HomotopyCategory.quotient C₂ _).map_comp _ _).symm).trans ?_).trans
    (((congrArg (fun t => _ ≫ t) ((congrArg (fun t => _ ≫ t)
      ((HomotopyCategory.quotient C₂ _).map_comp _ _).symm).trans
        ((HomotopyCategory.quotient C₂ _).map_comp _ _).symm)).trans
          ((HomotopyCategory.quotient C₂ _).map_comp _ _).symm).symm)
  refine congrArg (HomotopyCategory.quotient C₂ _).map ?_
  refine HomologicalComplex.from_single_hom_ext (V := C₂) (c := ComplexShape.up ℤ) (j := 0)
    (A := P₂.obj (P₁.obj X)) ?_
  change ((HomologicalComplex.single C₂ (ComplexShape.up ℤ) 0).map (c.hom.app X)).f 0 ≫
      ((HomologicalComplex.singleMapHomologicalComplex P (ComplexShape.up ℤ) 0).inv.app X).f 0 ≫
        P.map (ι.f 0) =
    ((HomologicalComplex.singleMapHomologicalComplex P₂ (ComplexShape.up ℤ) 0).inv.app
        (P₁.obj X)).f 0 ≫
      P₂.map (((HomologicalComplex.singleMapHomologicalComplex P₁ (ComplexShape.up ℤ) 0).inv.app
        X).f 0) ≫ P₂.map (P₁.map (ι.f 0)) ≫ c.hom.app (L.X 0)
  rw [HomologicalComplex.singleMapHomologicalComplex_inv_app_self,
    HomologicalComplex.singleMapHomologicalComplex_inv_app_self,
    HomologicalComplex.singleMapHomologicalComplex_inv_app_self,
    HomologicalComplex.single_map_f_self]
  have := c.hom.naturality ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 X).inv ≫
    ι.f 0)
  simp only [Functor.comp_map, Functor.map_comp, Category.assoc] at this
  simp only [Functor.map_comp, Category.assoc, Iso.inv_hom_id_assoc, this]
  rw [← P₂.map_comp_assoc, Iso.inv_hom_id, P₂.map_id, Category.id_comp]
  rfl

end Concrete

section RestrictComposition

variable {M₀ : Type*} [Category* M₀] [Abelian M₀] [HasDerivedCategory M₀]
  {M₁ : Type*} [Category* M₁] [Abelian M₁] [HasDerivedCategory M₁]
  {M₂ : Type*} [Category* M₂] [Abelian M₂] [HasDerivedCategory M₂]
  {r₁ : M₁ ⥤ M₀} {r₂ : M₂ ⥤ M₁} {r : M₂ ⥤ M₀} [r₁.Additive] [r₂.Additive] [r.Additive]
  [PreservesFiniteLimits r₁] [PreservesFiniteColimits r₁]
  [PreservesFiniteLimits r₂] [PreservesFiniteColimits r₂]
  [PreservesFiniteLimits r] [PreservesFiniteColimits r]

/-- The composite of the induced functors of two exact functors lifts the composite of the
induced functors on bounded below homotopy categories. -/
instance mapDerivedCategoryPlusCompLifting' :
    Localization.Lifting DerivedCategory.Plus.Qh (HomotopyCategory.Plus.quasiIso M₂)
      ((r₂.mapHomotopyCategoryPlus ⋙ r₁.mapHomotopyCategoryPlus) ⋙ DerivedCategory.Plus.Qh)
      (r₂.mapDerivedCategoryPlus ⋙ r₁.mapDerivedCategoryPlus) :=
  ⟨isoWhiskerRight r₂.mapDerivedCategoryPlusFactorsh r₁.mapDerivedCategoryPlus ≪≫
    isoWhiskerLeft r₂.mapHomotopyCategoryPlus r₁.mapDerivedCategoryPlusFactorsh⟩

/-- **The transformation `r̄₂ ⋙ r̄₁ ⟶ r̄` of induced functors** induced by a transformation
`ρ₀ : r₂ ⋙ r₁ ⟶ r` of exact functors. -/
def mapDerivedCategoryPlusCompTransOfComp (ρ₀ : r₂ ⋙ r₁ ⟶ r) :
    r₂.mapDerivedCategoryPlus ⋙ r₁.mapDerivedCategoryPlus ⟶ r.mapDerivedCategoryPlus :=
  Localization.liftNatTrans DerivedCategory.Plus.Qh (HomotopyCategory.Plus.quasiIso M₂)
    ((r₂.mapHomotopyCategoryPlus ⋙ r₁.mapHomotopyCategoryPlus) ⋙ DerivedCategory.Plus.Qh)
    (r.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh)
    (r₂.mapDerivedCategoryPlus ⋙ r₁.mapDerivedCategoryPlus) r.mapDerivedCategoryPlus
    (Functor.whiskerRight ((mapHomotopyCategoryPlusCompIso (Iso.refl (r₂ ⋙ r₁))).hom ≫
      Functor.mapHomotopyCategoryPlusNatTrans ρ₀) DerivedCategory.Plus.Qh)

/-- **`mapDerivedCategoryPlusCompTransOfComp` satisfies the compatibility with `ρ₀` that the
pasting of derived squares asks for.** -/
theorem mapDerivedCategoryPlusCompTransOfComp_compat (ρ₀ : r₂ ⋙ r₁ ⟶ r)
    (L : HomotopyCategory.Plus M₂) :
    r₁.mapDerivedCategoryPlusFactorsh.inv.app (r₂.mapHomotopyCategoryPlus.obj L) ≫
        r₁.mapDerivedCategoryPlus.map (r₂.mapDerivedCategoryPlusFactorsh.inv.app L) ≫
          (mapDerivedCategoryPlusCompTransOfComp ρ₀).app (DerivedCategory.Plus.Qh.obj L) =
      DerivedCategory.Plus.Qh.map ((Functor.mapHomotopyCategoryPlusNatTrans ρ₀).app L :
        r₁.mapHomotopyCategoryPlus.obj (r₂.mapHomotopyCategoryPlus.obj L) ⟶
          r.mapHomotopyCategoryPlus.obj L) ≫
        r.mapDerivedCategoryPlusFactorsh.inv.app L := by
  have h := mapHomotopyCategoryPlusCompIso_refl_inv_app r₂ r₁ L
  have h' : (mapHomotopyCategoryPlusCompIso (Iso.refl (r₂ ⋙ r₁))).hom.app L = 𝟙 _ :=
    (Category.comp_id _).symm.trans ((congrArg (fun t => _ ≫ t) h).symm.trans
      (Iso.hom_inv_id_app _ L))
  let ρ₀' : r₁.mapHomotopyCategoryPlus.obj (r₂.mapHomotopyCategoryPlus.obj L) ⟶
      r.mapHomotopyCategoryPlus.obj L := (Functor.mapHomotopyCategoryPlusNatTrans ρ₀).app L
  have hc : DerivedCategory.Plus.Qh.map
      ((mapHomotopyCategoryPlusCompIso (Iso.refl (r₂ ⋙ r₁))).hom.app L ≫
        (Functor.mapHomotopyCategoryPlusNatTrans ρ₀).app L) = DerivedCategory.Plus.Qh.map ρ₀' :=
    congrArg DerivedCategory.Plus.Qh.map
      ((congrArg (fun t => t ≫ (Functor.mapHomotopyCategoryPlusNatTrans ρ₀).app L) h').trans
        (Category.id_comp _))
  have hA : r₁.mapDerivedCategoryPlusFactorsh.inv.app (r₂.mapHomotopyCategoryPlus.obj L) ≫
      r₁.mapDerivedCategoryPlus.map (r₂.mapDerivedCategoryPlusFactorsh.inv.app L) ≫
        r₁.mapDerivedCategoryPlus.map (r₂.mapDerivedCategoryPlusFactorsh.hom.app L) ≫
          r₁.mapDerivedCategoryPlusFactorsh.hom.app (r₂.mapHomotopyCategoryPlus.obj L) = 𝟙 _ := by
    have e : r₁.mapDerivedCategoryPlus.map (r₂.mapDerivedCategoryPlusFactorsh.inv.app L) ≫
        r₁.mapDerivedCategoryPlus.map (r₂.mapDerivedCategoryPlusFactorsh.hom.app L) = 𝟙 _ :=
      (r₁.mapDerivedCategoryPlus.map_comp _ _).symm.trans
        ((congrArg r₁.mapDerivedCategoryPlus.map (Iso.inv_hom_id_app _ L)).trans
          (r₁.mapDerivedCategoryPlus.map_id _))
    rw [reassoc_of% e, Iso.inv_hom_id_app]
  change _ = DerivedCategory.Plus.Qh.map ρ₀' ≫ r.mapDerivedCategoryPlusFactorsh.inv.app L
  rw [mapDerivedCategoryPlusCompTransOfComp, Localization.liftNatTrans_app]
  change _ ≫ _ ≫ (r₁.mapDerivedCategoryPlus.map (r₂.mapDerivedCategoryPlusFactorsh.hom.app L) ≫
      r₁.mapDerivedCategoryPlusFactorsh.hom.app (r₂.mapHomotopyCategoryPlus.obj L)) ≫
    DerivedCategory.Plus.Qh.map ((mapHomotopyCategoryPlusCompIso (Iso.refl (r₂ ⋙ r₁))).hom.app L ≫
      (Functor.mapHomotopyCategoryPlusNatTrans ρ₀).app L) ≫
    r.mapDerivedCategoryPlusFactorsh.inv.app L = _
  rw [hc]
  simp only [Category.assoc]
  rw [reassoc_of% hA]

end RestrictComposition

end CategoryTheory.Functor
