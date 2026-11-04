module
public import StacksFrontier.Homology.KFlat.Bifunctor
public import StacksFrontier.Homology.KFlat.BifunctorLocalization

public import StacksFrontier.Homology.KFlat.BifunctorTransport
public import StacksFrontier.Homology.KFlat.BifunctorOneSided
public import StacksFrontier.Homology.KFlat.BifunctorOneSidedComparison
public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryComparisons

/-!
# The transported derived bifunctor on representatives

`CochainComplex.KFlatBifunctor.derivedTransportIso` is the isomorphism
`G₃(F^𝐋(K, L)) ≅ F'^𝐋(G₁ K, G₂ L)` of bifunctors on the derived categories obtained by descending
the complex-level transport `transportComplexIso` along the K-flat localizations. This file
computes it on representatives: at `(Qh K, Qh L)` for an **arbitrary** object `K` of the homotopy
category and a K-flat `L` it is the explicit composite `homotopyTransportAtIso` of the one-sided
comparisons of `F` and `F'`, the comparisons of the exact functors with the localizations, and the
homotopy-level transport, which at classes of complexes is the class of `transportComplexIso`.

## Main definitions

* `CochainComplex.KFlatBifunctor.homotopyComparisonRightIso`: the one-sided comparison
  `F^𝐋(Qh K, Qh L) ≅ Qh(F^h(K, L))` for `K` arbitrary and `L` K-flat, as an isomorphism of
  functors on the homotopy category.
* `CochainComplex.KFlatBifunctor.homotopyTransportAtIso`: the transport at a K-flat second
  argument, assembled on the homotopy category.

* `CochainComplex.KFlatBifunctor.derivedTransportProdIso`: `derivedTransportIso` along a single
  exact functor, uncurried to an isomorphism of functors on `D(A) × D(A)`, the shape in which a
  comparison of bifunctors enters `CategoryTheory.adjunctionTensorMap`.

## Main results

* `CochainComplex.KFlatBifunctor.derivedTransportIso_hom_app_app_Qh`: **the transport on
  representatives**, with `homotopyTransportAtIso_hom_app` its six factors.
* `CochainComplex.KFlatBifunctor.homotopyTransportIso_hom_app_app_quotient'`: the homotopy-level
  transport at classes of complexes is the class of `transportComplexIso`.
* `CochainComplex.KFlatBifunctor.comparisonRight_hom_Qh` relates `comparisonRight` to
  `homotopyComparisonRightIso`; that on a left K-flat first factor the one-sided comparison is
  the two-sided one is `CochainComplex.KFlatBifunctor.comparisonRight_eq_comparison`, imported.
* `CochainComplex.KFlatBifunctor.natTrans_ext_of_kFlatLeft`,
  `natTrans_app_Qh_eq_of_kFlatLeft`: natural transformations out of `D(A)` are determined by their
  values at left K-flat objects.

## Implementation notes

Several statements below are proved by applying an arrow-algebra lemma stated in a bare category
(`comp_id_chain`, `uncurry_obj_map_prod`). The objects of the homotopy and derived categories
involved have several definitionally equal spellings (`(G ⋙ H).obj` against `H.obj (G.obj _)`,
`Qh.obj (quotient.obj K)` against the objects of the K-flat subcategories), and a rewrite cannot
cross between them; the bare lemmas are applied by `exact`, whose unification runs at default
transparency.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Prod

namespace CochainComplex.KFlatBifunctor

section Uncurry

variable {C₁ C₂ C₃ : Type*} [Category C₁] [Category C₂] [Category C₃]

/-- The uncurried map of a bifunctor, with the two factors in the other order. -/
theorem uncurry_obj_map_prod (P : C₁ ⥤ C₂ ⥤ C₃) {a a' : C₁} {b b' : C₂} (f : a ⟶ a')
    (g : b ⟶ b') :
    (Functor.uncurry.obj P).map (f ×ₘ g) = (P.obj a).map g ≫ (P.map f).app b' := by
  simp only [Functor.uncurry_obj_map]
  exact ((P.map f).naturality g).symm

/-- Identities in a composite can be dropped, in a bare category. -/
theorem comp_id_chain {C : Type*} [Category C] {X₀ X₁ X₂ X₃ : C} (a : X₀ ⟶ X₁)
    (i₁ : X₁ ⟶ X₁) (b : X₁ ⟶ X₂) (c : X₂ ⟶ X₃) (i₂ : X₃ ⟶ X₃) (i₃ : X₃ ⟶ X₃)
    (h₁ : i₁ = 𝟙 _) (h₂ : i₂ = 𝟙 _) (h₃ : i₃ = 𝟙 _) :
    a ≫ i₁ ≫ b ≫ c ≫ i₂ ≫ i₃ = a ≫ b ≫ c := by
  subst h₁ h₂ h₃
  simp

/-- Naturality of a natural transformation of bifunctors in both variables at once. -/
theorem bifunctor_natTrans_naturality₂ {C₁ C₂ C₃ : Type*} [Category C₁] [Category C₂]
    [Category C₃] {P P' : C₁ ⥤ C₂ ⥤ C₃} (τ : P ⟶ P') {x x' : C₁} {y y' : C₂} (f : x ⟶ x')
    (g : y ⟶ y') :
    (P.map f).app y ≫ (P.obj x').map g ≫ (τ.app x').app y' =
      (τ.app x).app y ≫ (P'.map f).app y ≫ (P'.obj x').map g := by
  rw [(τ.app x').naturality g, ← Category.assoc, ← NatTrans.comp_app, τ.naturality,
    NatTrans.comp_app, Category.assoc]

end Uncurry

section Ext

variable {A B D : Type*} [Category A] [Category B] [Category D]
  [Abelian A] [Abelian B] [Abelian D]
  (F : A ⥤ B ⥤ D) [F.Additive] [∀ X, (F.obj X).Additive]
  [∀ (K₁ : CochainComplex A ℤ) (K₂ : CochainComplex B ℤ),
    HomologicalComplex.HasMapBifunctor K₁ K₂ F (ComplexShape.up ℤ)]
  [HasDerivedCategory A] [(kFlatQLeft F).IsLocalization (kFlatQuasiIsoLeft F)]

/-- **A natural transformation out of `D(A)` is determined by its values at the left K-flat
complexes.** -/
theorem natTrans_ext_of_kFlatLeft {E : Type*} [Category E] {P P' : DerivedCategory A ⥤ E}
    {τ τ' : P ⟶ P'}
    (h : ∀ K : CochainComplex A ℤ, KFlatLeft F K →
      τ.app (DerivedCategory.Q.obj K) = τ'.app (DerivedCategory.Q.obj K)) : τ = τ' := by
  refine Localization.natTrans_ext (kFlatQLeft F) (kFlatQuasiIsoLeft F) (fun X => ?_)
  let e := (DerivedCategory.quotientCompQhIso A).app X.obj.as
  exact (cancel_mono (P'.mapIso e).hom).1 ((τ.naturality e.hom).symm.trans
    ((congrArg (fun t => P.map e.hom ≫ t) (h _ X.property)).trans (τ'.naturality e.hom)))

/-- **A natural transformation out of `D(A)` is determined on `K(A)` by its values at the left
K-flat objects.** If its whiskering along `Qh` agrees with a given natural transformation `Θ`
of functors on `K(A)` at every left K-flat object, then it agrees with `Θ` everywhere. -/
theorem natTrans_app_Qh_eq_of_kFlatLeft {E : Type*} [Category E]
    {P P' : DerivedCategory A ⥤ E} (τ : P ⟶ P')
    (Θ : DerivedCategory.Qh ⋙ P ⟶ DerivedCategory.Qh ⋙ P')
    (h : ∀ X : (kFlatObjectsLeft F).FullSubcategory,
      τ.app (DerivedCategory.Qh.obj X.obj) = Θ.app X.obj)
    (K : HomotopyCategory A (ComplexShape.up ℤ)) :
    τ.app (DerivedCategory.Qh.obj K) = Θ.app K := by
  have hθ := (Localization.fullyFaithfulWhiskeringLeft DerivedCategory.Qh
    (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) E).map_preimage Θ
  have hτ : τ = (Localization.fullyFaithfulWhiskeringLeft DerivedCategory.Qh
      (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) E).preimage Θ :=
    Localization.natTrans_ext (kFlatQLeft F) (kFlatQuasiIsoLeft F)
      (fun X => (h X).trans (NatTrans.congr_app hθ X.obj).symm)
  rw [hτ]
  exact NatTrans.congr_app hθ K

end Ext

section OneSided

variable {A B D : Type*} [Category A] [Category B] [Category D]
  [Abelian A] [Abelian B] [Abelian D]
  (F : A ⥤ B ⥤ D) [F.Additive] [∀ X, (F.obj X).Additive]
  [∀ (K₁ : CochainComplex A ℤ) (K₂ : CochainComplex B ℤ),
    HomologicalComplex.HasMapBifunctor K₁ K₂ F (ComplexShape.up ℤ)]
  [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory D]
  [(kFlatQLeft F).IsLocalization (kFlatQuasiIsoLeft F)]
  [(kFlatQ F).IsLocalization (kFlatQuasiIso F)]

/-- **The one-sided comparison on the homotopy category**: for an arbitrary object `K` of
`K(A)` and a K-flat object `L` of `K(B)`, the derived bifunctor at `(Qh K, Qh L)` is `Qh` of
the homotopy-level bifunctor at `(K, L)`, naturally in `K` and `L`. -/
def homotopyComparisonRightIso :
    DerivedCategory.Qh ⋙ derivedBifunctorRight F ≅ homotopyToDerivedRight F :=
  Functor.isoWhiskerLeft DerivedCategory.Qh (derivedBifunctorRightIso F) ≪≫
    homotopyToDerivedRightIso F

/-- On a left K-flat first factor, the homotopy-level one-sided comparison is the two-sided
comparison `derivedBifunctorComparisonIso`. -/
theorem homotopyComparisonRightIso_hom_app_kFlat (X : (kFlatObjectsLeft F).FullSubcategory) :
    (homotopyComparisonRightIso F).hom.app X.obj = (derivedBifunctorComparisonIso F).hom.app X :=
  derivedBifunctorRightIso_hom_app_comp F X.obj X.property

/-- The inverse form of `homotopyComparisonRightIso_hom_app_kFlat`. -/
theorem homotopyComparisonRightIso_inv_app_kFlat (X : (kFlatObjectsLeft F).FullSubcategory) :
    (homotopyComparisonRightIso F).inv.app X.obj = (derivedBifunctorComparisonIso F).inv.app X := by
  rw [← cancel_mono ((homotopyComparisonRightIso F).hom.app X.obj), Iso.inv_hom_id_app,
    homotopyComparisonRightIso_hom_app_kFlat]
  exact ((derivedBifunctorComparisonIso F).inv_hom_id_app X).symm

/-- **The one-sided comparison read on the homotopy category.** At the classes of a complex `K`
and of a K-flat complex `L`, `comparisonRight` precomposed with the two bridges
`Qh ∘ quotient ≅ Q` is `homotopyComparisonRightIso` followed by the total-complex bridge. -/
theorem comparisonRight_hom_Qh (K : CochainComplex A ℤ) (L : CochainComplex B ℤ)
    (hL : KFlat F L) :
    ((derivedBifunctor F).map ((DerivedCategory.quotientCompQhIso A).hom.app K)).app
        (DerivedCategory.Qh.obj ((HomotopyCategory.quotient B (ComplexShape.up ℤ)).obj L)) ≫
      ((derivedBifunctor F).obj (DerivedCategory.Q.obj K)).map
        ((DerivedCategory.quotientCompQhIso B).hom.app L) ≫
      (comparisonRight F K L hL).hom =
    ((homotopyComparisonRightIso F).hom.app
        ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K)).app
        ⟨(HomotopyCategory.quotient B (ComplexShape.up ℤ)).obj L, hL⟩ ≫
      (totalComplexQhIso F K L).hom := by
  have h1 := NatTrans.congr_app
    ((derivedBifunctorRightIso F).hom.naturality
      ((DerivedCategory.quotientCompQhIso A).hom.app K))
    (⟨(HomotopyCategory.quotient B (ComplexShape.up ℤ)).obj L, hL⟩ :
      (kFlatObjects F).FullSubcategory)
  have h3 := NatTrans.congr_app (homotopyToDerivedRightIso_hom_app_quotient F K)
    (⟨(HomotopyCategory.quotient B (ComplexShape.up ℤ)).obj L, hL⟩ :
      (kFlatObjects F).FullSubcategory)
  simp only [NatTrans.comp_app] at h1 h3
  have hc : ((derivedBifunctor F).obj (DerivedCategory.Q.obj K)).map
        ((DerivedCategory.quotientCompQhIso B).hom.app L) ≫
      ((derivedBifunctor F).obj (DerivedCategory.Q.obj K)).map
        ((DerivedCategory.quotientCompQhIso B).inv.app L) = 𝟙 _ := by
    rw [← CategoryTheory.Functor.map_comp, Iso.hom_inv_id_app, CategoryTheory.Functor.map_id]
  rw [comparisonRight]
  simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom, Iso.symm_hom, Iso.app_inv,
    homotopyComparisonRightIso, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.whiskerLeft_app]
  rw [reassoc_of% hc]
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (fun t => t ≫ ((derivedToDerivedRightFac F).hom.app K).app
    ⟨(HomotopyCategory.quotient B (ComplexShape.up ℤ)).obj L, hL⟩ ≫
      (totalComplexQhIso F K L).hom) h1).trans ?_
  simp only [Category.assoc]
  rw [← reassoc_of% h3]
  rfl

/-- **The one-sided comparison at the classes of two complexes**: for a complex `K` and a K-flat
complex `L`, `F^𝐋(Qh K, Qh L) ≅ Qh(Tot(F(K, L)))`, all on the homotopy category. -/
def comparisonRightQhIso (K : CochainComplex A ℤ) (L : CochainComplex B ℤ) (hL : KFlat F L) :
    ((derivedBifunctor F).obj
        (DerivedCategory.Qh.obj ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K))).obj
        (DerivedCategory.Qh.obj ((HomotopyCategory.quotient B (ComplexShape.up ℤ)).obj L)) ≅
      DerivedCategory.Qh.obj ((HomotopyCategory.quotient D (ComplexShape.up ℤ)).obj
        (totalComplex F K L)) :=
  ((homotopyComparisonRightIso F).app
      ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K)).app
      ⟨(HomotopyCategory.quotient B (ComplexShape.up ℤ)).obj L, hL⟩ ≪≫
    DerivedCategory.Qh.mapIso (((homotopyBifunctorIso F).app K).app L)

end OneSided

section Transport

variable {A B D A' B' D' : Type*}
  [Category A] [Category B] [Category D] [Category A'] [Category B'] [Category D']
  [Abelian A] [Abelian B] [Abelian D] [Abelian A'] [Abelian B'] [Abelian D']
  (F : A ⥤ B ⥤ D) [F.Additive] [∀ X, (F.obj X).Additive]
  [∀ (K₁ : CochainComplex A ℤ) (K₂ : CochainComplex B ℤ),
    HomologicalComplex.HasMapBifunctor K₁ K₂ F (ComplexShape.up ℤ)]
  (F' : A' ⥤ B' ⥤ D') [F'.Additive] [∀ X, (F'.obj X).Additive]
  [∀ (K₁ : CochainComplex A' ℤ) (K₂ : CochainComplex B' ℤ),
    HomologicalComplex.HasMapBifunctor K₁ K₂ F' (ComplexShape.up ℤ)]
  (G₁ : A ⥤ A') (G₂ : B ⥤ B') (G₃ : D ⥤ D')
  [G₁.Additive] [G₂.Additive] [G₃.Additive]
  (ε : ∀ (a : A) (b : B), G₃.obj ((F.obj a).obj b) ≅ (F'.obj (G₁.obj a)).obj (G₂.obj b))
  (hε₁ : ∀ {a a' : A} (f : a ⟶ a') (b : B),
    G₃.map ((F.map f).app b) ≫ (ε a' b).hom =
      (ε a b).hom ≫ (F'.map (G₁.map f)).app (G₂.obj b))
  (hε₂ : ∀ (a : A) {b b' : B} (g : b ⟶ b'),
    G₃.map ((F.obj a).map g) ≫ (ε a b').hom =
      (ε a b).hom ≫ (F'.obj (G₁.obj a)).map (G₂.map g))
  [∀ n : ℤ, PreservesColimitsOfShape
    (Discrete ↥(ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ)
      (ComplexShape.up ℤ) ⁻¹' {n})) G₃]
  [∀ (K : CochainComplex A ℤ) (L : CochainComplex B ℤ),
    HomologicalComplex₂.HasTotal (HomologicalComplex₂.mapBicomplex G₃
      (((F.mapBifunctorHomologicalComplex (ComplexShape.up ℤ) (ComplexShape.up ℤ)).obj K).obj L))
      (ComplexShape.up ℤ)]

/-- At classes of complexes, the homotopy-level transport is its restriction to complexes. -/
theorem homotopyTransportIso_hom_app_app_quotient (K : CochainComplex A ℤ)
    (L : CochainComplex B ℤ) :
    ((homotopyTransportIso F F' G₁ G₂ G₃ ε hε₁ hε₂).hom.app
        ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K)).app
        ((HomotopyCategory.quotient B (ComplexShape.up ℤ)).obj L) =
      ((homotopyTransportRestrIso F F' G₁ G₂ G₃ ε hε₁ hε₂).hom.app K).app L := by
  simp only [homotopyTransportIso, Localization.lift₂NatIso_hom,
    Localization.lift₂NatTrans_app_app]
  exact (Category.id_comp _).trans (Category.comp_id _)

/-- The six factors of the restriction of the homotopy-level transport to complexes. -/
theorem homotopyTransportRestrIso_hom_app_app (K : CochainComplex A ℤ)
    (L : CochainComplex B ℤ) :
    ((homotopyTransportRestrIso F F' G₁ G₂ G₃ ε hε₁ hε₂).hom.app K).app L =
      (G₃.mapHomotopyCategory (ComplexShape.up ℤ)).map
          (((homotopyBifunctorLiftingIso F).hom.app K).app L) ≫
        (G₃.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).hom.app (totalComplex F K L) ≫
        (HomotopyCategory.quotient D' (ComplexShape.up ℤ)).map
          (transportComplexIso F F' G₁ G₂ G₃ ε hε₁ hε₂ K L).hom ≫
        ((homotopyBifunctorLiftingIso F').inv.app
            ((G₁.mapHomologicalComplex (ComplexShape.up ℤ)).obj K)).app
          ((G₂.mapHomologicalComplex (ComplexShape.up ℤ)).obj L) ≫
        ((homotopyBifunctor F').obj ((HomotopyCategory.quotient A' (ComplexShape.up ℤ)).obj
            ((G₁.mapHomologicalComplex (ComplexShape.up ℤ)).obj K))).map
          ((G₂.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).inv.app L) ≫
        ((homotopyBifunctor F').map
            ((G₁.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).inv.app K)).app
          ((G₂.mapHomotopyCategory (ComplexShape.up ℤ)).obj
            ((HomotopyCategory.quotient B (ComplexShape.up ℤ)).obj L)) :=
  rfl

/-- **The homotopy-level transport at the classes of two complexes** is the class of the
complex-level transport, between the two homotopy-level descents of the total complexes. -/
theorem homotopyTransportIso_hom_app_app_quotient' (K : CochainComplex A ℤ)
    (L : CochainComplex B ℤ) :
    ((homotopyTransportIso F F' G₁ G₂ G₃ ε hε₁ hε₂).hom.app
        ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K)).app
        ((HomotopyCategory.quotient B (ComplexShape.up ℤ)).obj L) =
      (G₃.mapHomotopyCategory (ComplexShape.up ℤ)).map
          (((homotopyBifunctorLiftingIso F).hom.app K).app L) ≫
        (HomotopyCategory.quotient D' (ComplexShape.up ℤ)).map
          (transportComplexIso F F' G₁ G₂ G₃ ε hε₁ hε₂ K L).hom ≫
        ((homotopyBifunctorLiftingIso F').inv.app
            ((G₁.mapHomologicalComplex (ComplexShape.up ℤ)).obj K)).app
          ((G₂.mapHomologicalComplex (ComplexShape.up ℤ)).obj L) := by
  rw [homotopyTransportIso_hom_app_app_quotient, homotopyTransportRestrIso_hom_app_app]
  exact comp_id_chain _ _ _ _ _ _ rfl (CategoryTheory.Functor.map_id _ _)
    ((congrArg (fun f => NatTrans.app f _) (CategoryTheory.Functor.map_id _ _)).trans
      (NatTrans.id_app _ _))

section Derived

variable [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory D]
  [HasDerivedCategory A'] [HasDerivedCategory B'] [HasDerivedCategory D']
  [PreservesFiniteLimits G₁] [PreservesFiniteColimits G₁]
  [PreservesFiniteLimits G₂] [PreservesFiniteColimits G₂]
  [PreservesFiniteLimits G₃] [PreservesFiniteColimits G₃]
  [(kFlatQLeft F).IsLocalization (kFlatQuasiIsoLeft F)]
  [(kFlatQ F).IsLocalization (kFlatQuasiIso F)]
  [(kFlatQLeft F').IsLocalization (kFlatQuasiIsoLeft F')]
  [(kFlatQ F').IsLocalization (kFlatQuasiIso F')]
  (hKFlatLeft : ∀ K : CochainComplex A ℤ, KFlatLeft F K →
    KFlatLeft F' ((G₁.mapHomologicalComplex (ComplexShape.up ℤ)).obj K))
  (hKFlat : ∀ L : CochainComplex B ℤ, KFlat F L →
    KFlat F' ((G₂.mapHomologicalComplex (ComplexShape.up ℤ)).obj L))

/-- At (left) K-flat objects, the derived transport is its restriction to them. -/
theorem derivedTransportIso_hom_app_app_kFlatQ (X₁ : (kFlatObjectsLeft F).FullSubcategory)
    (X₂ : (kFlatObjects F).FullSubcategory) :
    ((derivedTransportIso F F' G₁ G₂ G₃ ε hε₁ hε₂ hKFlatLeft hKFlat).hom.app
        ((kFlatQLeft F).obj X₁)).app ((kFlatQ F).obj X₂) =
      ((derivedTransportRestrIso F F' G₁ G₂ G₃ ε hε₁ hε₂ hKFlatLeft hKFlat).hom.app X₁).app
        X₂ := by
  simp only [derivedTransportIso, Localization.lift₂NatIso_hom,
    Localization.lift₂NatTrans_app_app]
  exact (Category.id_comp _).trans (Category.comp_id _)

/-- The six factors of the restriction of the derived transport to (left) K-flat objects. -/
theorem derivedTransportRestrIso_hom_app_app (X₁ : (kFlatObjectsLeft F).FullSubcategory)
    (X₂ : (kFlatObjects F).FullSubcategory) :
    ((derivedTransportRestrIso F F' G₁ G₂ G₃ ε hε₁ hε₂ hKFlatLeft hKFlat).hom.app X₁).app X₂ =
      G₃.mapDerivedCategory.map (((derivedBifunctorComparisonIso F).hom.app X₁).app X₂) ≫
        G₃.mapDerivedCategoryFactorsh.hom.app (((homotopyBifunctor F).obj X₁.obj).obj X₂.obj) ≫
        DerivedCategory.Qh.map
          (((homotopyTransportIso F F' G₁ G₂ G₃ ε hε₁ hε₂).hom.app X₁.obj).app X₂.obj) ≫
        ((derivedBifunctorComparisonIso F').inv.app
            ((kFlatMapLeft F F' G₁ hKFlatLeft).obj X₁)).app
          ((kFlatMapRight F F' G₂ hKFlat).obj X₂) ≫
        ((derivedBifunctor F').obj
            (DerivedCategory.Qh.obj ((G₁.mapHomotopyCategory (ComplexShape.up ℤ)).obj X₁.obj))).map
          (G₂.mapDerivedCategoryFactorsh.inv.app X₂.obj) ≫
        ((derivedBifunctor F').map (G₁.mapDerivedCategoryFactorsh.inv.app X₁.obj)).app
          (G₂.mapDerivedCategory.obj (DerivedCategory.Qh.obj X₂.obj)) :=
  rfl

/-- The source of the transport at a fixed K-flat second argument `L`, as a functor of the
first argument: `M ↦ G₃(F^𝐋(M, L))`. -/
abbrev derivedTransportSourceAt (X₂ : (kFlatObjects F).FullSubcategory) :
    DerivedCategory A ⥤ DerivedCategory D' :=
  derivedTransportSource F G₃ ⋙ (evaluation _ _).obj (DerivedCategory.Qh.obj X₂.obj)

/-- The target of the transport at a fixed K-flat second argument `L`:
`M ↦ F'^𝐋(G₁ M, G₂ L)`. -/
abbrev derivedTransportTargetAt (X₂ : (kFlatObjects F).FullSubcategory) :
    DerivedCategory A ⥤ DerivedCategory D' :=
  derivedTransportTarget F' G₁ G₂ ⋙ (evaluation _ _).obj (DerivedCategory.Qh.obj X₂.obj)

/-- **The transport on the homotopy category, at a K-flat second argument**, assembled from
the one-sided comparisons of `F` and `F'`, the comparisons of the three exact functors with the
localizations, and the homotopy-level transport. -/
def homotopyTransportAtIso (X₂ : (kFlatObjects F).FullSubcategory) :
    DerivedCategory.Qh ⋙ derivedTransportSourceAt F G₃ X₂ ≅
      DerivedCategory.Qh ⋙ derivedTransportTargetAt F F' G₁ G₂ X₂ :=
  Functor.isoWhiskerRight (homotopyComparisonRightIso F)
      ((evaluation _ _).obj X₂ ⋙ G₃.mapDerivedCategory) ≪≫
    Functor.isoWhiskerLeft (homotopyBifunctor F ⋙ (evaluation _ _).obj X₂.obj)
      G₃.mapDerivedCategoryFactorsh ≪≫
    Functor.isoWhiskerRight
      (Functor.isoWhiskerRight (homotopyTransportIso F F' G₁ G₂ G₃ ε hε₁ hε₂)
        ((evaluation _ _).obj X₂.obj)) DerivedCategory.Qh ≪≫
    Functor.isoWhiskerLeft (G₁.mapHomotopyCategory (ComplexShape.up ℤ))
      (Functor.isoWhiskerRight (homotopyComparisonRightIso F').symm
        ((evaluation _ _).obj ((kFlatMapRight F F' G₂ hKFlat).obj X₂))) ≪≫
    Functor.isoWhiskerRight G₁.mapDerivedCategoryFactorsh.symm
      (derivedBifunctor F' ⋙ (evaluation _ _).obj
        (DerivedCategory.Qh.obj ((G₂.mapHomotopyCategory (ComplexShape.up ℤ)).obj X₂.obj))) ≪≫
    Functor.isoWhiskerLeft (DerivedCategory.Qh ⋙ G₁.mapDerivedCategory ⋙ derivedBifunctor F')
      ((evaluation _ _).mapIso (G₂.mapDerivedCategoryFactorsh.app X₂.obj).symm)

/-- The six factors of `homotopyTransportAtIso`. -/
theorem homotopyTransportAtIso_hom_app (X₂ : (kFlatObjects F).FullSubcategory)
    (K : HomotopyCategory A (ComplexShape.up ℤ)) :
    (homotopyTransportAtIso F F' G₁ G₂ G₃ ε hε₁ hε₂ hKFlat X₂).hom.app K =
      G₃.mapDerivedCategory.map (((homotopyComparisonRightIso F).hom.app K).app X₂) ≫
        G₃.mapDerivedCategoryFactorsh.hom.app (((homotopyBifunctor F).obj K).obj X₂.obj) ≫
        DerivedCategory.Qh.map
          (((homotopyTransportIso F F' G₁ G₂ G₃ ε hε₁ hε₂).hom.app K).app X₂.obj) ≫
        ((homotopyComparisonRightIso F').inv.app
            ((G₁.mapHomotopyCategory (ComplexShape.up ℤ)).obj K)).app
          ((kFlatMapRight F F' G₂ hKFlat).obj X₂) ≫
        ((derivedBifunctor F').map (G₁.mapDerivedCategoryFactorsh.inv.app K)).app
          (DerivedCategory.Qh.obj ((G₂.mapHomotopyCategory (ComplexShape.up ℤ)).obj X₂.obj)) ≫
        ((derivedBifunctor F').obj (G₁.mapDerivedCategory.obj (DerivedCategory.Qh.obj K))).map
          (G₂.mapDerivedCategoryFactorsh.inv.app X₂.obj) := by
  simp only [homotopyTransportAtIso, Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, Iso.symm_hom, Functor.mapIso_hom, Iso.app_inv, Functor.comp_map,
    evaluation_obj_map, evaluation_map_app, Functor.comp_obj, evaluation_obj_obj]

/-- **The transported derived bifunctor at `(Qh K, Qh L)` for an arbitrary `K` and a K-flat
`L`** is `homotopyTransportAtIso`. -/
theorem derivedTransportIso_hom_app_app_Qh (K : HomotopyCategory A (ComplexShape.up ℤ))
    (X₂ : (kFlatObjects F).FullSubcategory) :
    ((derivedTransportIso F F' G₁ G₂ G₃ ε hε₁ hε₂ hKFlatLeft hKFlat).hom.app
        (DerivedCategory.Qh.obj K)).app (DerivedCategory.Qh.obj X₂.obj) =
      (homotopyTransportAtIso F F' G₁ G₂ G₃ ε hε₁ hε₂ hKFlat X₂).hom.app K := by
  refine natTrans_app_Qh_eq_of_kFlatLeft F
    (Functor.whiskerRight (derivedTransportIso F F' G₁ G₂ G₃ ε hε₁ hε₂ hKFlatLeft hKFlat).hom
      ((evaluation _ _).obj (DerivedCategory.Qh.obj X₂.obj)))
    (homotopyTransportAtIso F F' G₁ G₂ G₃ ε hε₁ hε₂ hKFlat X₂).hom (fun X₁ => ?_) K
  have h := derivedTransportIso_hom_app_app_kFlatQ F F' G₁ G₂ G₃ ε hε₁ hε₂ hKFlatLeft hKFlat
    X₁ X₂
  rw [derivedTransportRestrIso_hom_app_app] at h
  refine h.trans ?_
  rw [homotopyTransportAtIso_hom_app]
  rw [homotopyComparisonRightIso_hom_app_kFlat F X₁, show (homotopyComparisonRightIso F').inv.app
      ((G₁.mapHomotopyCategory (ComplexShape.up ℤ)).obj X₁.obj) =
      (derivedBifunctorComparisonIso F').inv.app ((kFlatMapLeft F F' G₁ hKFlatLeft).obj X₁)
      from homotopyComparisonRightIso_inv_app_kFlat F' ((kFlatMapLeft F F' G₁ hKFlatLeft).obj X₁)]
  congr 4
  exact ((derivedBifunctor F').map (G₁.mapDerivedCategoryFactorsh.inv.app X₁.obj)).naturality
    (G₂.mapDerivedCategoryFactorsh.inv.app X₂.obj)

end Derived

end Transport

section Prod

variable {A A' : Type*} [Category A] [Category A'] [Abelian A] [Abelian A']
  (F : A ⥤ A ⥤ A) [F.Additive] [∀ X, (F.obj X).Additive]
  [∀ (K₁ K₂ : CochainComplex A ℤ),
    HomologicalComplex.HasMapBifunctor K₁ K₂ F (ComplexShape.up ℤ)]
  (F' : A' ⥤ A' ⥤ A') [F'.Additive] [∀ X, (F'.obj X).Additive]
  [∀ (K₁ K₂ : CochainComplex A' ℤ),
    HomologicalComplex.HasMapBifunctor K₁ K₂ F' (ComplexShape.up ℤ)]
  (G : A ⥤ A') [G.Additive]
  (ε : ∀ (a b : A), G.obj ((F.obj a).obj b) ≅ (F'.obj (G.obj a)).obj (G.obj b))
  (hε₁ : ∀ {a a' : A} (f : a ⟶ a') (b : A),
    G.map ((F.map f).app b) ≫ (ε a' b).hom = (ε a b).hom ≫ (F'.map (G.map f)).app (G.obj b))
  (hε₂ : ∀ (a : A) {b b' : A} (g : b ⟶ b'),
    G.map ((F.obj a).map g) ≫ (ε a b').hom = (ε a b).hom ≫ (F'.obj (G.obj a)).map (G.map g))
  [∀ n : ℤ, PreservesColimitsOfShape
    (Discrete ↥(ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ)
      (ComplexShape.up ℤ) ⁻¹' {n})) G]
  [∀ (K L : CochainComplex A ℤ),
    HomologicalComplex₂.HasTotal (HomologicalComplex₂.mapBicomplex G
      (((F.mapBifunctorHomologicalComplex (ComplexShape.up ℤ) (ComplexShape.up ℤ)).obj K).obj L))
      (ComplexShape.up ℤ)]
  [HasDerivedCategory A] [HasDerivedCategory A']
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  [(kFlatQLeft F).IsLocalization (kFlatQuasiIsoLeft F)]
  [(kFlatQ F).IsLocalization (kFlatQuasiIso F)]
  [(kFlatQLeft F').IsLocalization (kFlatQuasiIsoLeft F')]
  [(kFlatQ F').IsLocalization (kFlatQuasiIso F')]
  (hKFlatLeft : ∀ K : CochainComplex A ℤ, KFlatLeft F K →
    KFlatLeft F' ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj K))
  (hKFlat : ∀ L : CochainComplex A ℤ, KFlat F L →
    KFlat F' ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj L))

/-- **The transported derived bifunctor, uncurried**: `derivedTransportIso` along a single exact
functor `G`, as an isomorphism `G(F^𝐋(-, -)) ≅ F'^𝐋(G -, G -)` of functors on `D(A) × D(A)`. -/
def derivedTransportProdIso :
    Functor.uncurry.obj (derivedBifunctor F) ⋙ G.mapDerivedCategory ≅
      G.mapDerivedCategory.prod G.mapDerivedCategory ⋙
        Functor.uncurry.obj (derivedBifunctor F') :=
  NatIso.ofComponents
    (fun X => ((derivedTransportIso F F' G G G ε hε₁ hε₂ hKFlatLeft hKFlat).app X.1).app X.2)
    (fun {X Y} f => by
      obtain ⟨f₁, f₂⟩ := f
      have h := bifunctor_natTrans_naturality₂
        (derivedTransportIso F F' G G G ε hε₁ hε₂ hKFlatLeft hKFlat).hom f₁ f₂
      simp only [Functor.comp_obj, Functor.uncurry_obj_obj, Functor.comp_map,
        Functor.uncurry_obj_map, Functor.map_comp, Category.assoc, Iso.app_hom,
        Functor.prod_obj, Functor.prod_map]
      exact h)

/-- The component of `derivedTransportProdIso` at a pair `X = (X₁, X₂)` is the component of
`derivedTransportIso` at `X₁` and `X₂`. -/
@[simp]
theorem derivedTransportProdIso_hom_app (X : DerivedCategory A × DerivedCategory A) :
    (derivedTransportProdIso F F' G ε hε₁ hε₂ hKFlatLeft hKFlat).hom.app X =
      ((derivedTransportIso F F' G G G ε hε₁ hε₂ hKFlatLeft hKFlat).hom.app X.1).app X.2 :=
  rfl

end Prod

end CochainComplex.KFlatBifunctor

end
