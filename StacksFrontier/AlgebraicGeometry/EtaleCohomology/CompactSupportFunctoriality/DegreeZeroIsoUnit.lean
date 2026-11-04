module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.CompositionIsoUnbounded
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.BaseChangeCube
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CompactSupportFunctoriality.BoundedBelowToDirectImage
public import StacksFrontier.Homology.DerivedIndexing.StandardComparisonUnit
public import StacksFrontier.Homology.DerivedIndexing.StandardComparison
public import StacksFrontier.Homology.DerivedIndexing.SingleDegreeUnit
public import StacksFrontier.Homology.DerivedIndexing.UnitSingleFunctoriality
public import StacksFrontier.Algebra.Homology.DerivedCategory.ExactUnitSingle
public import StacksFrontier.Algebra.Homology.DerivedCategory.ExactRightDerivedPlusSingleHomology
public import StacksFrontier.Algebra.Homology.DerivedCategory.ExactMapDerivedPlusIsoApp
public import StacksFrontier.Algebra.Homology.DerivedCategory.ExactDerivedHomologyComposition

/-!
# The degree-zero identifications of the open immersion case of [Stacks, Tag 0F7B]

The isomorphism `i_! ∘ f'_* ≅ f̄_* ∘ b_!` of sheaves of the unbounded composition of derived
lower shrieks, `Stacks.EtaleCohomology.etaleModuleDirectImageExtensionByZeroIso`, is the
cohomology in degree zero of a derived isomorphism on objects placed in degree zero. It is
assembled from three identifications of a functor with the degree-zero cohomology of its right
derived functor on objects placed in degree zero:

* `Stacks.EtaleCohomology.rightDerivedFunctorPlusZeroIso`: `F ≅ H⁰ ∘ RF ∘ (-)[0]` for a left exact
  functor `F`;
* `Stacks.EtaleCohomology.rightDerivedFunctorPlusHomologyIso`: `H⁰ ∘ RE ≅ E ∘ H⁰` for an exact
  functor `E`;
* `Stacks.EtaleCohomology.singleFunctorCompRightDerivedFunctorPlusIso`: `RE ∘ (-)[0] ≅ (-)[0] ∘ E`
  for an exact functor `E`.

This file expresses each of them through the canonical map `(F X)[0] ⟶ RF(X[0])`
(`Stacks.DerivedIndexing.rightDerivedPlusUnitSingle`), which is natural in the functor and
compatible with composition, and deduces that a compatibility of derived functors on objects
placed in degree zero gives the corresponding compatibility of the functors themselves.

## Main results

* `Stacks.EtaleCohomology.rightDerivedFunctorPlusZeroIso_hom_app_eq`: `F X ≅ H⁰(RF(X[0]))` is
  `H⁰` of the canonical map.
* `Stacks.EtaleCohomology.singleFunctorCompRightDerivedFunctorPlusIso_inv_app_eq`: for an exact
  functor, `E(X)[0] ≅ RE(X[0])` is the canonical map.
* `Stacks.EtaleCohomology.rightDerivedFunctorPlusZeroIso_hom_app_comp_homologyIso`: for an exact
  functor, `E X ≅ H⁰(RE(X[0])) ≅ E(H⁰(X[0]))` is `E` of `X ≅ H⁰(X[0])`.
* `Stacks.EtaleCohomology.rightDerivedPlusUnitSingle_comp_compIsoOfIso_hom_app`: the canonical
  map of a composite, followed by the composition isomorphism of right derived functors.
* `Stacks.EtaleCohomology.degreeZero_comp_natTrans_of_derived`: a compatibility of derived
  functors on objects placed in degree zero, read on objects.

## References

* [Stacks Project, Tag 0F7B](https://stacks.math.columbia.edu/tag/0F7B)
* [Stacks Project, Tag 05TD](https://stacks.math.columbia.edu/tag/05TD)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Stacks.EtaleCohomology

section Abstract

attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

variable {A B : Type*} [Category* A] [Category* B] [Abelian A] [Abelian B]
  [HasDerivedCategory A] [HasDerivedCategory B] [EnoughInjectives A]

/-- If `cyc = s ≫ cm`, `cm ≫ π₂ = π₁ ≫ hm`, `s ≫ π₁ = sh` and `hm ≫ f₂ = f₁ ≫ qφ`, then
`cyc ≫ π₂ ≫ f₂ = (sh ≫ f₁) ≫ qφ`. -/
private theorem single_chain {X : Type*} [Category* X] {P Z₁ Z₂ H₁ H₂ D D' : X} (cyc : P ⟶ Z₂)
    (s : P ⟶ Z₁) (cm : Z₁ ⟶ Z₂) (π₂ : Z₂ ⟶ H₂) (π₁ : Z₁ ⟶ H₁) (hm : H₁ ⟶ H₂) (f₂ : H₂ ⟶ D)
    (sh : P ⟶ H₁) (f₁ : H₁ ⟶ D') (qφ : D' ⟶ D) (hc : cyc = s ≫ cm) (hπ : cm ≫ π₂ = π₁ ≫ hm)
    (hs : s ≫ π₁ = sh) (hn : hm ≫ f₂ = f₁ ≫ qφ) :
    cyc ≫ π₂ ≫ f₂ = (sh ≫ f₁) ≫ qφ := by
  subst hc hs
  simp only [Category.assoc]
  rw [reassoc_of% hπ, hn]

/-- If `cyc ≫ i₂ = x ≫ φ`, `cm ≫ i₂ = i₁ ≫ φ` and `s ≫ i₁ = x`, then
`cyc ≫ i₂ = (s ≫ cm) ≫ i₂`. -/
private theorem single_cycles_chain {X : Type*} [Category* X] {P Q Z₁ Z₂ K : X} (cyc : P ⟶ Z₂)
    (s : P ⟶ Z₁) (cm : Z₁ ⟶ Z₂) (i₂ : Z₂ ⟶ K) (i₁ : Z₁ ⟶ Q) (φ : Q ⟶ K) (x : P ⟶ Q)
    (hcyc : cyc ≫ i₂ = x ≫ φ) (hm : cm ≫ i₂ = i₁ ≫ φ) (hs : s ≫ i₁ = x) :
    cyc ≫ i₂ = (s ≫ cm) ≫ i₂ := by
  rw [hcyc, Category.assoc, hm, reassoc_of% hs]

/-- `F X` as the degree-zero cycles of `F(X[0])`, followed by the class map, is the
identification of `F X` with the cohomology of `(F X)[0]` followed by the comparison of `(F X)[0]`
with `F(X[0])`. -/
theorem singleCyclesHom_comp_homologyπ_eq (F : A ⥤ B) [F.Additive] (M : A) :
    Stacks.DerivedIndexing.singleCyclesHom F M ≫ HomologicalComplex.homologyπ _ 0 ≫
        (DerivedCategory.homologyFunctorFactors B 0).inv.app _ =
      (DerivedCategory.Plus.singleFunctorCompHomologyFunctorIso (C := B) 0).inv.app (F.obj M) ≫
        (DerivedCategory.Plus.homologyFunctor B 0).map
          (DerivedCategory.Plus.Q.map ((Stacks.DerivedIndexing.mapSinglePlus F 0).app M)) := by
  let φ := (HomologicalComplex.singleMapHomologicalComplex F (ComplexShape.up ℤ) 0).inv.app M
  have hθ := Stacks.DerivedFunctor.singleFunctorCompHomologyFunctorIso_inv_app B (F.obj M)
  have hn := (DerivedCategory.homologyFunctorFactors B 0).inv.naturality φ
  have hx : (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (F.obj M)).inv ≫ φ.f 0 =
      F.map (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 M).inv := by
    simp [φ, HomologicalComplex.singleMapHomologicalComplex_inv_app_self]
  have hc : Stacks.DerivedIndexing.singleCyclesHom F M =
      (HomologicalComplex.singleObjCyclesSelfIso (ComplexShape.up ℤ) 0 (F.obj M)).inv ≫
        HomologicalComplex.cyclesMap φ 0 :=
    (cancel_mono (HomologicalComplex.iCycles _ 0)).1
      (single_cycles_chain _ _ _ _ _ _ _
        ((Stacks.DerivedIndexing.singleCyclesHom_iCycles F M).trans hx.symm)
        (HomologicalComplex.cyclesMap_i φ 0)
        (HomologicalComplex.singleObjCyclesSelfIso_inv_iCycles _ _ _))
  show _ = (DerivedCategory.singleFunctorCompHomologyFunctorIso B 0).inv.app (F.obj M) ≫
    (DerivedCategory.homologyFunctor B 0).map (DerivedCategory.Q.map φ)
  rw [hθ]
  exact single_chain _ _ _ _ _ _ _ _ _ _ hc
    (HomologicalComplex.homologyπ_naturality φ 0).symm
    (HomologicalComplex.singleObjCyclesSelfIso_inv_homologyπ _ _ _) hn

/-- If `x ≫ y ≫ z = t ≫ H.map q`, then `x ≫ y ≫ z ≫ H.map u = t ≫ H.map (q ≫ u)`. -/
private theorem map_tail {X Y : Type*} [Category* X] [Category* Y] (H : X ⥤ Y) {P a b : Y}
    {c d e : X} (x : P ⟶ a) (y : a ⟶ b) (z : b ⟶ H.obj c) (t : P ⟶ H.obj d) (q : d ⟶ c)
    (u : c ⟶ e) (h : x ≫ y ≫ z = t ≫ H.map q) :
    x ≫ y ≫ z ≫ H.map u = t ≫ H.map (q ≫ u) := by
  rw [H.map_comp, ← Category.assoc t, ← h]
  simp only [Category.assoc]

/-- **`F X ≅ H⁰(RF(X[0]))` is the degree-zero cohomology of the canonical map**
`(F X)[0] ⟶ RF(X[0])`, after the identification of the cohomology of `(F X)[0]` with `F X`, for a
left exact functor `F`. -/
theorem rightDerivedFunctorPlusZeroIso_hom_app_eq (F : A ⥤ B) [F.Additive]
    [PreservesFiniteLimits F] (M : A) :
    (rightDerivedFunctorPlusZeroIso F).hom.app M =
      (DerivedCategory.Plus.singleFunctorCompHomologyFunctorIso (C := B) 0).inv.app (F.obj M) ≫
        (DerivedCategory.Plus.homologyFunctor B 0).map
          ((Stacks.DerivedIndexing.rightDerivedPlusUnitSingle F).app M) := by
  have hI : (Stacks.DerivedIndexing.rightDerivedIso F 0).hom.app M =
      (Stacks.Cohomology.HigherDirectImagePresheaf.derivedPlusToStandard F 0).inv.app M := by
    rw [← cancel_mono ((Stacks.DerivedIndexing.rightDerivedIso F 0).inv.app M), Iso.hom_inv_id_app,
      Stacks.DerivedIndexing.rightDerivedIso_inv_eq, Iso.inv_hom_id_app]
  have h₁ : (rightDerivedFunctorPlusZeroIso F).hom.app M =
      F.toRightDerivedZero.app M ≫ (Stacks.DerivedIndexing.rightDerivedIso F 0).hom.app M :=
    rfl
  rw [h₁, hI, Stacks.DerivedIndexing.toRightDerivedZero_comp_derivedPlusToStandard_inv,
    ← Stacks.DerivedIndexing.singleDerivedUnit_zero, Stacks.DerivedIndexing.singleDerivedUnit]
  exact map_tail (DerivedCategory.Plus.homologyFunctor B 0)
    (c := DerivedCategory.Plus.Q.obj
      (F.mapCochainComplexPlus.obj ((Stacks.DerivedIndexing.singlePlusFunctor A 0).obj M)))
    _ _ _ _ _ _ (singleCyclesHom_comp_homologyπ_eq F M)

variable (E : A ⥤ B) [E.Additive] [PreservesFiniteLimits E] [PreservesFiniteColimits E]

/-- The identification of the right derived functor of an exact functor with its degreewise
action is the inverse of `Stacks.DerivedFunctor.exactMapDerivedCategoryPlusIso`: both lift
`E.mapDerivedCategoryPlusFactorsh ≪≫ asIso E.rightDerivedFunctorPlusUnit` along the
localization. -/
theorem rightDerivedFunctorPlusIsoMapDerivedCategoryPlus_eq_exact :
    E.rightDerivedFunctorPlusIsoMapDerivedCategoryPlus =
      (Stacks.DerivedFunctor.exactMapDerivedCategoryPlusIso E).symm := by
  have : IsIso E.rightDerivedFunctorPlusUnit :=
    E.isIso_rightDerivedFunctorPlusUnit_of_preservesHomology
  refine Iso.ext (Localization.natTrans_ext DerivedCategory.Plus.Qh
    (HomotopyCategory.Plus.quasiIso A) (fun N => ?_))
  rw [Iso.symm_hom, Stacks.DerivedFunctor.exactMapDerivedCategoryPlusIso_inv_app_Qh]
  simp [Functor.rightDerivedFunctorPlusIsoMapDerivedCategoryPlus]
  rfl

omit [EnoughInjectives A] in
/-- The two comparisons of the cohomology of the degreewise action of an exact functor on the
unbounded derived category with the functor agree: both descend the comparison
`H^n(E(K)) ≅ E(H^n(K))` of complexes. -/
theorem homologyDerivedHomologyIso_eq (n : ℤ) :
    Stacks.Homology.derivedHomologyIso E n = Stacks.DerivedFunctor.derivedHomologyIso E n := by
  refine Iso.ext (Localization.natTrans_ext DerivedCategory.Q
    (HomologicalComplex.quasiIso A (ComplexShape.up ℤ)) (fun K => ?_))
  rw [Stacks.DerivedFunctor.derivedHomologyIso_hom_app_Q]
  simp [Stacks.Homology.derivedHomologyIso, Stacks.Homology.exactHomologyIso_hom_app,
    Stacks.DerivedFunctor.complexHomologyIso_hom_app]

/-- The comparison `H^n ∘ RE ≅ E ∘ H^n` for an exact functor is
`Stacks.DerivedFunctor.exactRightDerivedPlusHomologyIso`. -/
theorem rightDerivedFunctorPlusHomologyIso_eq_exact (n : ℤ) :
    rightDerivedFunctorPlusHomologyIso E n =
      Stacks.DerivedFunctor.exactRightDerivedPlusHomologyIso E n := by
  rw [rightDerivedFunctorPlusHomologyIso, rightDerivedFunctorPlusIsoMapDerivedCategoryPlus_eq_exact,
    homologyDerivedHomologyIso_eq]
  rfl

end Abstract

section AbstractUniverse

attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

universe w

variable {A B : Type*} [Category* A] [Category* B] [Abelian A] [Abelian B]
  [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} B] [EnoughInjectives A]
  (E : A ⥤ B) [E.Additive] [PreservesFiniteLimits E] [PreservesFiniteColimits E]

/-- **For an exact functor, `RE(X[0]) ≅ E(X)[0]` is the inverse of the canonical map**
`E(X)[0] ⟶ RE(X[0])`. -/
theorem singleFunctorCompRightDerivedFunctorPlusIso_inv_app_eq (M : A) :
    (singleFunctorCompRightDerivedFunctorPlusIso E).inv.app M =
      (Stacks.DerivedIndexing.rightDerivedPlusUnitSingle E).app M := by
  refine Eq.trans ?_ (congrArg (fun t => t.app M)
    (Stacks.DerivedFunctor.exactSingleFunctorRightDerivedPlusIso_hom E))
  simp only [singleFunctorCompRightDerivedFunctorPlusIso, Iso.trans_inv, NatTrans.comp_app,
    Functor.isoWhiskerLeft_inv, Functor.whiskerLeft_app,
    Stacks.DerivedFunctor.exactSingleFunctorRightDerivedPlusIso, Iso.trans_hom, Iso.symm_hom,
    Functor.isoWhiskerLeft_hom, rightDerivedFunctorPlusIsoMapDerivedCategoryPlus_eq_exact,
    Iso.symm_inv]
  congr 1
  apply DerivedCategory.Plus.ι.map_injective
  rw [Stacks.DerivedFunctor.ι_map_exactMapDerivedCategoryPlusSingle_inv_app]
  exact (Functor.FullyFaithful.ofFullyFaithful DerivedCategory.Plus.ι).map_preimage
    (X := (DerivedCategory.Plus.singleFunctor B 0).obj (E.obj M))
    (Y := E.mapDerivedCategoryPlus.obj ((DerivedCategory.Plus.singleFunctor A 0).obj M))
    ((E.mapDerivedCategorySingleFunctor 0).inv.app M)

/-- **For an exact functor, `E X ≅ H⁰(RE(X[0])) ≅ E(H⁰(X[0]))` is `E` of `X ≅ H⁰(X[0])`.** -/
theorem rightDerivedFunctorPlusZeroIso_hom_app_comp_homologyIso (M : A) :
    (rightDerivedFunctorPlusZeroIso E).hom.app M ≫
        (rightDerivedFunctorPlusHomologyIso E 0).hom.app
          ((DerivedCategory.Plus.singleFunctor A 0).obj M) =
      E.map ((DerivedCategory.Plus.singleFunctorCompHomologyFunctorIso (C := A) 0).inv.app M) := by
  rw [rightDerivedFunctorPlusZeroIso_hom_app_eq, rightDerivedFunctorPlusHomologyIso_eq_exact,
    ← Stacks.DerivedFunctor.isoRightDerivedPlusSingle_hom_app_comp_exactRightDerivedPlusHomologyIso,
    Stacks.DerivedFunctor.isoRightDerivedPlusSingle_zero_hom_app]

end AbstractUniverse

section Composite

attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

variable {A B C : Type*} [Category* A] [Category* B] [Category* C] [Abelian A] [Abelian B]
  [Abelian C] [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory C]
  [EnoughInjectives A] [EnoughInjectives B]

/-- **The canonical map `(H X)[0] ⟶ RH(X[0])` against the composition isomorphism**
`RH ≅ RF ∘ RG` attached to `F ⋙ G ≅ H`: it is `(F ⋙ G ≅ H)` in degree zero followed by the
canonical map of `G` at `F X` and `RG` of the canonical map of `F` at `X`. -/
theorem rightDerivedPlusUnitSingle_comp_compIsoOfIso_hom_app (F : A ⥤ B) (G : B ⥤ C)
    (H : A ⥤ C) [F.Additive] [G.Additive] [H.Additive] [F.PreservesInjectiveObjects]
    (e : F ⋙ G ≅ H) (M : A) :
    (Stacks.DerivedIndexing.rightDerivedPlusUnitSingle H).app M ≫
        (rightDerivedFunctorPlusCompIsoOfIso F G H e).hom.app
          ((DerivedCategory.Plus.singleFunctor A 0).obj M) =
      (DerivedCategory.Plus.singleFunctor C 0).map (e.inv.app M) ≫
        (Stacks.DerivedIndexing.rightDerivedPlusUnitSingle G).app (F.obj M) ≫
          G.rightDerivedFunctorPlus.map
            ((Stacks.DerivedIndexing.rightDerivedPlusUnitSingle F).app M) := by
  have h₁ : (rightDerivedFunctorPlusCompIsoOfIso F G H e).hom =
      Stacks.DerivedIndexing.rightDerivedFunctorPlusNatTrans e.inv ≫
        Stacks.DerivedIndexing.rightDerivedPlusCompTrans F G := by
    rw [rightDerivedFunctorPlusCompIsoOfIso, Iso.trans_hom, Iso.symm_hom,
      rightDerivedFunctorPlusIsoOfCompIso_eq,
      Stacks.DerivedIndexing.rightDerivedFunctorPlusNatIso_inv_eq,
      Functor.rightDerivedFunctorPlusCompIso_hom]
    rfl
  rw [h₁, NatTrans.comp_app,
    ← reassoc_of% (Stacks.DerivedIndexing.rightDerivedPlusUnitSingle_natTrans_app e.inv M),
    Stacks.DerivedIndexing.rightDerivedPlusUnitSingle_comp_app]

end Composite

section DegreeZero

attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

universe w

/-- If `x ≫ lh = sinv ≫ y₁ ≫ y₂`, `s ≫ sinv = 𝟙 a` and `lh ≫ linv = 𝟙 c`, then
`s ≫ x = y₁ ≫ y₂ ≫ linv`. -/
theorem conj_inv_chain {C : Type*} [Category* C] {a b c d e : C} (s : a ⟶ b) (sinv : b ⟶ a)
    (x : b ⟶ c) (lh : c ⟶ d) (linv : d ⟶ c) (y₁ : a ⟶ e) (y₂ : e ⟶ d)
    (h : x ≫ lh = sinv ≫ y₁ ≫ y₂) (hs : s ≫ sinv = 𝟙 a) (hl : lh ≫ linv = 𝟙 c) :
    s ≫ x = y₁ ≫ y₂ ≫ linv := by
  calc s ≫ x = s ≫ x ≫ lh ≫ linv := by rw [hl, Category.comp_id]
    _ = y₁ ≫ y₂ ≫ linv := by rw [reassoc_of% h, reassoc_of% hs]

/-- The canonical map of `H`, after `e` in degree zero, is the canonical map of `G` at `F X`
followed by `RG` of the canonical map of `F` and the inverse composition isomorphism. -/
private theorem single_map_comp_rightDerivedPlusUnitSingle_eq {A B C : Type*} [Category* A]
    [Category* B] [Category* C] [Abelian A] [Abelian B] [Abelian C] [HasDerivedCategory.{w} A]
    [HasDerivedCategory.{w} B] [HasDerivedCategory.{w} C] [EnoughInjectives A]
    [EnoughInjectives B] (F : A ⥤ B) (G : B ⥤ C) (H : A ⥤ C) [F.Additive] [G.Additive]
    [H.Additive] [F.PreservesInjectiveObjects] (e : F ⋙ G ≅ H) (M : A) :
    (DerivedCategory.Plus.singleFunctor C 0).map (e.hom.app M) ≫
        (Stacks.DerivedIndexing.rightDerivedPlusUnitSingle H).app M =
      (Stacks.DerivedIndexing.rightDerivedPlusUnitSingle G).app (F.obj M) ≫
        G.rightDerivedFunctorPlus.map
          ((Stacks.DerivedIndexing.rightDerivedPlusUnitSingle F).app M) ≫
        (rightDerivedFunctorPlusCompIsoOfIso F G H e).inv.app
          ((DerivedCategory.Plus.singleFunctor A 0).obj M) :=
  conj_inv_chain _ _ _ _ _ _ _
    (rightDerivedPlusUnitSingle_comp_compIsoOfIso_hom_app F G H e M)
    ((Functor.map_comp _ _ _).symm.trans ((congrArg _ (e.hom_inv_id_app M)).trans
      (CategoryTheory.Functor.map_id _ _))) (Iso.hom_inv_id_app _ _)

/-- If `r ≫ σN = σS ≫ m`, `(t ≫ n) ≫ σS = p`, `x = p ≫ m` and `σN ≫ σNinv = 𝟙 d`, then
`x ≫ σNinv = t ≫ n ≫ r`. -/
theorem degreeZero_inv_chain {C : Type*} [Category* C] {a b c d e f : C} (t : a ⟶ b)
    (n : b ⟶ c) (r : c ⟶ d) (σN : d ⟶ f) (σNinv : f ⟶ d) (σS : c ⟶ e) (m : e ⟶ f)
    (p : a ⟶ e) (x : a ⟶ f) (hn : r ≫ σN = σS ≫ m) (hz : (t ≫ n) ≫ σS = p) (hx : x = p ≫ m)
    (hσ : σN ≫ σNinv = 𝟙 d) : x ≫ σNinv = t ≫ n ≫ r := by
  rw [hx, ← hz]
  simp only [Category.assoc]
  rw [← reassoc_of% hn, hσ, Category.comp_id]

/-- An identity `A₁ ≫ A₂ ≫ H₀.map Ψi ≫ H₀.map A₄ ≫ A₅ ≫ A₆ ≫ A₇ = E₁ ≫ E₂` of composites in `C`,
deduced from the given commutative squares and identities after composing with the monomorphism
`ρH`. -/
theorem degreeZero_chain {C D : Type*} [Category* C] [Category* D] (H₀ : D ⥤ C)
    {c₀ c₁ c₅ c₆ c₇ c₈ : C} {d₁ d₂ d₃ d₄ d₅ d₇ e₁ s₀ s₅ s₆ s₇ s₈ : D}
    (A₁ : c₀ ⟶ c₁) (A₂ : c₁ ⟶ H₀.obj d₁) (Ψi : d₁ ⟶ d₂) (A₄ : d₂ ⟶ d₃) (A₅ : H₀.obj d₃ ⟶ c₅)
    (A₆ : c₅ ⟶ c₆) (A₇ : c₆ ⟶ c₇) (E₁ : c₀ ⟶ c₈) (E₂ : c₈ ⟶ c₇) (ρH : c₇ ⟶ H₀.obj d₇)
    [Mono ρH] (θ₀ : c₀ ⟶ H₀.obj s₀) (θ₅ : c₅ ⟶ H₀.obj s₅) (θ₆ : c₆ ⟶ H₀.obj s₆)
    (θ₇ : c₇ ⟶ H₀.obj s₇) (θ₈ : c₈ ⟶ H₀.obj s₈) (S₆ : s₅ ⟶ s₆) (S₇ : s₆ ⟶ s₇)
    (SE₁ : s₀ ⟶ s₈) (SE₂ : s₈ ⟶ s₇) (νH : s₇ ⟶ d₇) (νg : s₅ ⟶ d₃) (X₁ : d₃ ⟶ d₂)
    (Y₁ : d₂ ⟶ d₄) (Lb : d₄ ⟶ d₇) (νi : s₀ ⟶ e₁) (Rνf : e₁ ⟶ d₁) (Rε : d₁ ⟶ d₅)
    (Lf : d₅ ⟶ d₇)
    (hρH : ρH = θ₇ ≫ H₀.map νH) (h₆ : A₆ ≫ θ₆ = θ₅ ≫ H₀.map S₆)
    (h₇ : A₇ ≫ θ₇ = θ₆ ≫ H₀.map S₇) (hB : S₆ ≫ S₇ ≫ νH = νg ≫ X₁ ≫ Y₁ ≫ Lb)
    (hρg : A₅ ≫ θ₅ ≫ H₀.map νg = 𝟙 _) (hσ : A₄ ≫ X₁ = 𝟙 _)
    (hC : Ψi ≫ Y₁ ≫ Lb = Rε ≫ Lf) (hK : A₁ ≫ A₂ = θ₀ ≫ H₀.map νi ≫ H₀.map Rνf)
    (hE₁ : E₁ ≫ θ₈ = θ₀ ≫ H₀.map SE₁) (hE₂ : E₂ ≫ θ₇ = θ₈ ≫ H₀.map SE₂)
    (hR : SE₁ ≫ SE₂ ≫ νH = νi ≫ Rνf ≫ Rε ≫ Lf) :
    A₁ ≫ A₂ ≫ H₀.map Ψi ≫ H₀.map A₄ ≫ A₅ ≫ A₆ ≫ A₇ = E₁ ≫ E₂ := by
  rw [← cancel_mono ρH]
  simp only [Category.assoc]
  have l₁ : A₆ ≫ A₇ ≫ ρH = θ₅ ≫ H₀.map νg ≫ H₀.map (X₁ ≫ Y₁ ≫ Lb) := by
    rw [hρH, reassoc_of% h₇, reassoc_of% h₆, ← H₀.map_comp, ← H₀.map_comp, hB, H₀.map_comp]
  have l₂ : H₀.map Ψi ≫ H₀.map A₄ ≫ H₀.map (X₁ ≫ Y₁ ≫ Lb) = H₀.map (Rε ≫ Lf) := by
    rw [← H₀.map_comp, ← H₀.map_comp, reassoc_of% hσ, hC]
  have r₁ : E₁ ≫ E₂ ≫ ρH = θ₀ ≫ H₀.map (νi ≫ Rνf ≫ Rε ≫ Lf) := by
    rw [hρH, reassoc_of% hE₂, reassoc_of% hE₁, ← H₀.map_comp, ← H₀.map_comp, hR]
  rw [l₁, reassoc_of% hρg, l₂, reassoc_of% hK, r₁]
  simp only [Functor.map_comp]

open Stacks.DerivedIndexing in
/-- **A compatibility on `D⁺` evaluated on objects placed in degree zero, read on objects.**
Let `ψ : f₁ ⋙ i₁ ≅ b₁ ⋙ g` be obtained from an isomorphism `Ψ : Rb₁ ⋙ Rg ≅ Rf₁ ⋙ Ri₁` of
derived functors through the identifications of a functor with the degree-zero cohomology of its
right derived functor on objects placed in degree zero, `i₁` and `b₁` being exact. If `Ψ⁻¹`
carries `Rεi : Ri₁ ⟶ Ri₂` to `Rεb : Rb₁ ⟶ Rb₂` on objects placed in degree zero, through the
composition isomorphisms `RH ≅ Rf₁ ⋙ Ri₂` and `RH ≅ Rb₂ ⋙ Rg`, then `ψ` carries `εi` to `εb`
through `f₁ ⋙ i₂ ≅ H` and `b₂ ⋙ g ≅ H`. -/
theorem degreeZero_comp_natTrans_of_derived {AP AY AT AU : Type*} [Category* AP] [Category* AY]
    [Category* AT] [Category* AU] [Abelian AP] [Abelian AY] [Abelian AT] [Abelian AU]
    [HasDerivedCategory.{w} AP] [HasDerivedCategory.{w} AY] [HasDerivedCategory.{w} AT]
    [HasDerivedCategory.{w} AU] [EnoughInjectives AP] [EnoughInjectives AY] [EnoughInjectives AT]
    (f₁ : AP ⥤ AY) (i₁ i₂ : AY ⥤ AU) (b₁ b₂ : AP ⥤ AT) (g : AT ⥤ AU) (H : AP ⥤ AU)
    [f₁.Additive] [i₁.Additive] [i₂.Additive] [b₁.Additive] [b₂.Additive] [g.Additive] [H.Additive]
    [PreservesFiniteLimits f₁] [PreservesFiniteLimits i₁] [PreservesFiniteLimits i₂]
    [PreservesFiniteLimits b₁] [PreservesFiniteLimits b₂] [PreservesFiniteLimits g]
    [PreservesFiniteLimits H] [PreservesFiniteColimits i₁] [PreservesFiniteColimits b₁]
    [f₁.PreservesInjectiveObjects] [b₂.PreservesInjectiveObjects]
    (εi : i₁ ⟶ i₂) (εb : b₁ ⟶ b₂) (cb : b₂ ⋙ g ≅ H) (cf : f₁ ⋙ i₂ ≅ H)
    (Ψ : b₁.rightDerivedFunctorPlus ⋙ g.rightDerivedFunctorPlus ≅
      f₁.rightDerivedFunctorPlus ⋙ i₁.rightDerivedFunctorPlus) (F : AP)
    (hC : Ψ.inv.app ((DerivedCategory.Plus.singleFunctor AP 0).obj F) ≫
        g.rightDerivedFunctorPlus.map ((rightDerivedFunctorPlusNatTrans εb).app
          ((DerivedCategory.Plus.singleFunctor AP 0).obj F)) ≫
        (rightDerivedFunctorPlusCompIsoOfIso b₂ g H cb).inv.app
          ((DerivedCategory.Plus.singleFunctor AP 0).obj F) =
      (rightDerivedFunctorPlusNatTrans εi).app
          (f₁.rightDerivedFunctorPlus.obj ((DerivedCategory.Plus.singleFunctor AP 0).obj F)) ≫
        (rightDerivedFunctorPlusCompIsoOfIso f₁ i₂ H cf).inv.app
          ((DerivedCategory.Plus.singleFunctor AP 0).obj F)) :
    i₁.map ((rightDerivedFunctorPlusZeroIso f₁).hom.app F) ≫
        (rightDerivedFunctorPlusHomologyIso i₁ 0).inv.app
          (f₁.rightDerivedFunctorPlus.obj ((DerivedCategory.Plus.singleFunctor AP 0).obj F)) ≫
        (DerivedCategory.Plus.homologyFunctor AU 0).map
          (Ψ.inv.app ((DerivedCategory.Plus.singleFunctor AP 0).obj F)) ≫
        (DerivedCategory.Plus.homologyFunctor AU 0).map (g.rightDerivedFunctorPlus.map
          ((singleFunctorCompRightDerivedFunctorPlusIso b₁).hom.app F)) ≫
        (rightDerivedFunctorPlusZeroIso g).inv.app (b₁.obj F) ≫ g.map (εb.app F) ≫
        cb.hom.app F =
      εi.app (f₁.obj F) ≫ cf.hom.app F := by
  let S := DerivedCategory.Plus.singleFunctor AP 0
  let H₀ := DerivedCategory.Plus.homologyFunctor AU 0
  let θ := DerivedCategory.Plus.singleFunctorCompHomologyFunctorIso (C := AU) 0
  let N := f₁.rightDerivedFunctorPlus.obj (S.obj F)
  let G := f₁.obj F
  let νf := (rightDerivedPlusUnitSingle f₁).app F
  let Lf := rightDerivedFunctorPlusCompIsoOfIso f₁ i₂ H cf
  let Lb := rightDerivedFunctorPlusCompIsoOfIso b₂ g H cb
  have hLf : (DerivedCategory.Plus.singleFunctor AU 0).map (cf.hom.app F) ≫
      (rightDerivedPlusUnitSingle H).app F =
      (rightDerivedPlusUnitSingle i₂).app G ≫ i₂.rightDerivedFunctorPlus.map νf ≫
        Lf.inv.app (S.obj F) :=
    single_map_comp_rightDerivedPlusUnitSingle_eq f₁ i₂ H cf F
  have hLb : (DerivedCategory.Plus.singleFunctor AU 0).map (cb.hom.app F) ≫
      (rightDerivedPlusUnitSingle H).app F =
      (rightDerivedPlusUnitSingle g).app (b₂.obj F) ≫
        g.rightDerivedFunctorPlus.map ((rightDerivedPlusUnitSingle b₂).app F) ≫
        Lb.inv.app (S.obj F) :=
    single_map_comp_rightDerivedPlusUnitSingle_eq b₂ g H cb F
  have hB : (DerivedCategory.Plus.singleFunctor AU 0).map (g.map (εb.app F)) ≫
      (DerivedCategory.Plus.singleFunctor AU 0).map (cb.hom.app F) ≫
      (rightDerivedPlusUnitSingle H).app F =
      (rightDerivedPlusUnitSingle g).app (b₁.obj F) ≫
        g.rightDerivedFunctorPlus.map ((rightDerivedPlusUnitSingle b₁).app F) ≫
        g.rightDerivedFunctorPlus.map ((rightDerivedFunctorPlusNatTrans εb).app (S.obj F)) ≫
        Lb.inv.app (S.obj F) := by
    have hng : (DerivedCategory.Plus.singleFunctor AU 0).map (g.map (εb.app F)) ≫
        (rightDerivedPlusUnitSingle g).app (b₂.obj F) =
        (rightDerivedPlusUnitSingle g).app (b₁.obj F) ≫
          g.rightDerivedFunctorPlus.map
            ((DerivedCategory.Plus.singleFunctor AT 0).map (εb.app F)) :=
      (rightDerivedPlusUnitSingle g).naturality (εb.app F)
    have hnb : (DerivedCategory.Plus.singleFunctor AT 0).map (εb.app F) ≫
        (rightDerivedPlusUnitSingle b₂).app F =
        (rightDerivedPlusUnitSingle b₁).app F ≫
          (rightDerivedFunctorPlusNatTrans εb).app (S.obj F) :=
      rightDerivedPlusUnitSingle_natTrans_app εb F
    rw [hLb, reassoc_of% hng, ← Functor.map_comp_assoc, hnb, Functor.map_comp_assoc]
  have hR : (DerivedCategory.Plus.singleFunctor AU 0).map (εi.app G) ≫
      (DerivedCategory.Plus.singleFunctor AU 0).map (cf.hom.app F) ≫
      (rightDerivedPlusUnitSingle H).app F =
      (rightDerivedPlusUnitSingle i₁).app G ≫ i₁.rightDerivedFunctorPlus.map νf ≫
        (rightDerivedFunctorPlusNatTrans εi).app N ≫ Lf.inv.app (S.obj F) := by
    have hni : (DerivedCategory.Plus.singleFunctor AU 0).map (εi.app G) ≫
        (rightDerivedPlusUnitSingle i₂).app G =
        (rightDerivedPlusUnitSingle i₁).app G ≫
          (rightDerivedFunctorPlusNatTrans εi).app
            ((DerivedCategory.Plus.singleFunctor AY 0).obj G) :=
      rightDerivedPlusUnitSingle_natTrans_app εi G
    have hnR : i₁.rightDerivedFunctorPlus.map νf ≫ (rightDerivedFunctorPlusNatTrans εi).app N =
        (rightDerivedFunctorPlusNatTrans εi).app ((DerivedCategory.Plus.singleFunctor AY 0).obj G) ≫
          i₂.rightDerivedFunctorPlus.map νf :=
      (rightDerivedFunctorPlusNatTrans εi).naturality νf
    rw [hLf, reassoc_of% hni, reassoc_of% hnR]
  have hK : i₁.map ((rightDerivedFunctorPlusZeroIso f₁).hom.app F) ≫
      (rightDerivedFunctorPlusHomologyIso i₁ 0).inv.app N =
      (DerivedCategory.Plus.singleFunctorCompHomologyFunctorIso (C := AU) 0).inv.app (i₁.obj G) ≫
        H₀.map ((rightDerivedPlusUnitSingle i₁).app G) ≫
        H₀.map (i₁.rightDerivedFunctorPlus.map νf) := by
    have hn : H₀.map (i₁.rightDerivedFunctorPlus.map νf) ≫
        (rightDerivedFunctorPlusHomologyIso i₁ 0).hom.app N =
        (rightDerivedFunctorPlusHomologyIso i₁ 0).hom.app
          ((DerivedCategory.Plus.singleFunctor AY 0).obj G) ≫
          i₁.map ((DerivedCategory.Plus.homologyFunctor AY 0).map νf) :=
      (rightDerivedFunctorPlusHomologyIso i₁ 0).hom.naturality νf
    exact degreeZero_inv_chain _ _ _ _ _ _ _ _ _ hn
      ((eq_whisker (rightDerivedFunctorPlusZeroIso_hom_app_eq i₁ G).symm _).trans
        (rightDerivedFunctorPlusZeroIso_hom_app_comp_homologyIso i₁ G))
      ((congrArg i₁.map (rightDerivedFunctorPlusZeroIso_hom_app_eq f₁ F)).trans (i₁.map_comp _ _))
      (Iso.hom_inv_id_app _ _)
  have hσ : g.rightDerivedFunctorPlus.map
        ((singleFunctorCompRightDerivedFunctorPlusIso b₁).hom.app F) ≫
      g.rightDerivedFunctorPlus.map ((rightDerivedPlusUnitSingle b₁).app F) = 𝟙 _ := by
    rw [← Functor.map_comp, ← singleFunctorCompRightDerivedFunctorPlusIso_inv_app_eq,
      Iso.hom_inv_id_app, CategoryTheory.Functor.map_id]
  have hρg : (rightDerivedFunctorPlusZeroIso g).inv.app (b₁.obj F) ≫
      (DerivedCategory.Plus.singleFunctorCompHomologyFunctorIso (C := AU) 0).inv.app
        (g.obj (b₁.obj F)) ≫ H₀.map ((rightDerivedPlusUnitSingle g).app (b₁.obj F)) = 𝟙 _ := by
    rw [← rightDerivedFunctorPlusZeroIso_hom_app_eq, Iso.inv_hom_id_app]
  exact degreeZero_chain H₀ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (rightDerivedFunctorPlusZeroIso_hom_app_eq H F)
    ((DerivedCategory.Plus.singleFunctorCompHomologyFunctorIso (C := AU) 0).inv.naturality _)
    ((DerivedCategory.Plus.singleFunctorCompHomologyFunctorIso (C := AU) 0).inv.naturality _)
    hB hρg hσ hC hK
    ((DerivedCategory.Plus.singleFunctorCompHomologyFunctorIso (C := AU) 0).inv.naturality _)
    ((DerivedCategory.Plus.singleFunctorCompHomologyFunctorIso (C := AU) 0).inv.naturality _) hR

end DegreeZero

end Stacks.EtaleCohomology

end
