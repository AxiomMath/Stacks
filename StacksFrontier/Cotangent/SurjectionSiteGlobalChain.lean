module

public import StacksFrontier.Algebra.Homology.DerivedCategory.CanonicalDeltaFunctor
public import StacksFrontier.Algebra.Homology.DerivedCategory.LeftDerivedRightTExact
public import StacksFrontier.Cotangent.SurjectionSiteGlobalObjectwise

/-!
# Pro-nilpotence of a filtration of presheaves of modules on a chaotic site

Let `C` be a small category with the chaotic topology, let `a : 𝒪 ⟶ 𝒪'` be a morphism of
presheaves of rings on `C` and let `𝒦 : ℕ → PresheafOfModules 𝒪` be a filtration — a family with
transition maps `𝒦ᵐ ⟶ 𝒦ⁿ` for `n ≤ m` which compose and are the identity in the trivial case.
Given the objectwise vanishing of the derived change of coefficients on the transition maps, the
inclusion `𝒦^{M} ⊆ 𝒦^{N}` induces the zero map on

`H^{-i}(Lπ_!(𝒦^{•} ⊗^L_𝒪 𝒪'))`

for `i < k`, as soon as the chain from `M` down to `N` can be cut into `k` steps whose `j`-th has
size more than `j`.

## Main results

* `Stacks.ChaoticSite.tensorPresheafIso` and its naturality: `(-) ⊗^L_𝒪 𝒪'` at a K-projective
  complex, read on abelian presheaves.
* `Stacks.ChaoticSite.homology_derivedColimit_tensor_map_eq_zero_of_objectwise`: the transition map
  `𝒦^{M} ⟶ 𝒦^{N}` induces zero on `H^{-i}(Lπ_!(- ⊗^L_𝒪 𝒪'))` for `i < k`.

## References

* [Stacks Project, Tag 08RF](https://stacks.math.columbia.edu/tag/08RF)
* [Stacks Project, Tag 08Q2](https://stacks.math.columbia.edu/tag/08Q2)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory.ProjectiveResolution

/-- **The cochain complex of a projective resolution is K-projective**: it is a bounded above
complex of projective objects. -/
instance isKProjective_cochainComplex {C : Type*} [Category* C] [Abelian C] {X : C}
    (R : ProjectiveResolution X) : R.cochainComplex.IsKProjective :=
  CochainComplex.isKProjective_of_projective _ 0

end CategoryTheory.ProjectiveResolution

namespace Stacks.ChaoticSite

variable {C : Type u} [SmallCategory C] {O O' : Cᵒᵖ ⥤ RingCat.{u}} (a : O ⟶ O')

/-- `(-) ⊗^L_𝒪 𝒪'`, read on the underlying abelian presheaves. -/
abbrev derivedTensorPresheaf : DerivedCategory (PresheafOfModules.{u} O) ⥤
    DerivedCategory (Cᵒᵖ ⥤ AddCommGrpCat.{u}) :=
  derivedExtendScalars a ⋙ (PresheafOfModules.toPresheaf.{u} O').mapDerivedCategory

/-- **`(-) ⊗^L_𝒪 𝒪'` at a K-projective complex is `(-) ⊗_𝒪 𝒪'` applied degreewise**, read on
abelian presheaves. -/
def tensorPresheafIso (P : CochainComplex (PresheafOfModules.{u} O) ℤ) [P.IsKProjective] :
    (derivedTensorPresheaf a).obj (DerivedCategory.Q.obj P) ≅
      DerivedCategory.Q.obj
        (((extendScalars a ⋙ PresheafOfModules.toPresheaf.{u} O').mapHomologicalComplex
          (ComplexShape.up ℤ)).obj P) :=
  have := Stacks.CategoryHomology.hasPointwiseLeftDerivedFunctor_of_enoughProjectives
    (extendScalars a)
  have := derivedExtendScalars_isLeftDerivedFunctor a
  (PresheafOfModules.toPresheaf.{u} O').mapDerivedCategory.mapIso
      (Stacks.CategoryHomology.leftDerivedObjIsoOfIsKProjective (extendScalars a)
        (derivedExtendScalars a) (derivedExtendScalarsCounit a) P) ≪≫
    (PresheafOfModules.toPresheaf.{u} O').mapDerivedCategoryFactors.app _

/-- **The computation of `(-) ⊗^L_𝒪 𝒪'` on a K-projective complex is natural in the complex.** -/
lemma tensorPresheafIso_naturality {P P' : CochainComplex (PresheafOfModules.{u} O) ℤ}
    [P.IsKProjective] [P'.IsKProjective] (φ : P ⟶ P') :
    (derivedTensorPresheaf a).map (DerivedCategory.Q.map φ) ≫ (tensorPresheafIso a P').hom =
      (tensorPresheafIso a P).hom ≫ DerivedCategory.Q.map
        (((extendScalars a ⋙ PresheafOfModules.toPresheaf.{u} O').mapHomologicalComplex
          (ComplexShape.up ℤ)).map φ) := by
  have := Stacks.CategoryHomology.hasPointwiseLeftDerivedFunctor_of_enoughProjectives
    (extendScalars a)
  have := derivedExtendScalars_isLeftDerivedFunctor a
  dsimp only [tensorPresheafIso, Iso.trans_hom, Functor.mapIso_hom, derivedTensorPresheaf,
    Functor.comp_map, Iso.app_hom]
  rw [← Category.assoc, ← Functor.map_comp,
    Stacks.CategoryHomology.leftDerivedObjIsoOfIsKProjective_naturality (extendScalars a)
      (derivedExtendScalars a) (derivedExtendScalarsCounit a) φ,
    Functor.map_comp]
  simp only [Category.assoc]
  exact congrArg (fun g => (PresheafOfModules.toPresheaf.{u} O').mapDerivedCategory.map
      (Stacks.CategoryHomology.leftDerivedObjIsoOfIsKProjective (extendScalars a)
        (derivedExtendScalars a) (derivedExtendScalarsCounit a) P).hom ≫ g)
    ((PresheafOfModules.toPresheaf.{u} O').mapDerivedCategoryFactors_hom_naturality
      (((extendScalars a).mapHomologicalComplex (ComplexShape.up ℤ)).map φ))

/-- `Stacks.ChaoticSite.tensorPresheafIso_naturality`, solved for the value of
`(-) ⊗^L_𝒪 𝒪'` on the morphism. -/
lemma tensorPresheafIso_naturality' {P P' : CochainComplex (PresheafOfModules.{u} O) ℤ}
    [P.IsKProjective] [P'.IsKProjective] (φ : P ⟶ P') :
    (derivedTensorPresheaf a).map (DerivedCategory.Q.map φ) =
      (tensorPresheafIso a P).hom ≫ DerivedCategory.Q.map
          (((extendScalars a ⋙ PresheafOfModules.toPresheaf.{u} O').mapHomologicalComplex
            (ComplexShape.up ℤ)).map φ) ≫ (tensorPresheafIso a P').inv := by
  rw [← Category.assoc, ← tensorPresheafIso_naturality a φ, Category.assoc, Iso.hom_inv_id,
    Category.comp_id]

section Chain

variable {M N : PresheafOfModules.{u} O}

/-- The lift of `f` to projective resolutions commutes with the augmentations `π'`. -/
private lemma hom'_comp_π'_single (f : M ⟶ N) :
    (homOfLift f).hom' ≫ (ProjectiveResolution.of N).π' =
      (ProjectiveResolution.of M).π' ≫
        (HomologicalComplex.single (PresheafOfModules.{u} O) (ComplexShape.up ℤ) 0).map f :=
  ProjectiveResolution.Hom.hom'_comp_π' (homOfLift f)

end Chain

/-- Let `𝒦 : ℕ → Mod(𝒪)` be a filtration with transition maps `incl`, let `idx` be a decreasing
sequence of indices whose `j`-th step has size more than `j` for `j < k`, and suppose the derived
change of coefficients kills every transition map, over enough objects of the site, in the degrees
its step size allows. Then for `i < k` the transition map `𝒦^{idx 0} ⟶ 𝒦^{idx k}` induces the zero
map on `H^{-i}(Lπ_!(- ⊗^L_𝒪 𝒪'))`. -/
theorem homology_derivedColimit_tensor_map_eq_zero_of_objectwise
    (K : ℕ → PresheafOfModules.{u} O)
    (incl : ∀ {m n : ℕ}, n ≤ m → (K m ⟶ K n))
    (incl_self : ∀ (n : ℕ) (h : n ≤ n), incl h = 𝟙 (K n))
    (incl_comp : ∀ {n m p : ℕ} (h : n ≤ m) (h' : m ≤ p), incl h' ≫ incl h = incl (h.trans h'))
    (P : Cᵒᵖ → Prop)
    (hdet : ∀ {F₁ F₂ : Cᵒᵖ ⥤ AddCommGrpCat.{u}} (α : F₁ ⟶ F₂),
      (∀ U, P U → α.app U = 0) → ∀ U, α.app U = 0)
    (hobj : ∀ (U : Cᵒᵖ), P U → ∀ (m n : ℕ) (h : n ≤ m) (j : ℕ), j < m - n →
      ((Stacks.NoncommChangeOfRings.extendScalars.{u} (a.app U).hom).leftDerived j).map
        ((PresheafOfModules.evaluation.{u} O U).map (incl h)) = 0)
    (k : ℕ) (idx : ℕ → ℕ) (hmono : ∀ j, idx (j + 1) ≤ idx j)
    (hstep : ∀ j, j < k → j < idx j - idx (j + 1))
    {Nn Mm : ℕ} (hNM : Nn ≤ Mm) (hM : idx 0 = Mm) (hN : idx k = Nn)
    (i : ℕ) (hi : i < k) :
    (DerivedCategory.homologyFunctor AddCommGrpCat.{u} (-(i : ℤ))).map
      ((derivedExtendScalars a ⋙ abelianDerivedColimitOfModules O').map
        (DerivedCategory.Q.map ((HomologicalComplex.single (PresheafOfModules.{u} O)
          (ComplexShape.up ℤ) 0).map (incl hNM)))) = 0 := by
  subst hM
  subst hN
  let Kc : ℕ → CochainComplex (Cᵒᵖ ⥤ AddCommGrpCat.{u}) ℤ := fun j =>
    ((extendScalars a ⋙ PresheafOfModules.toPresheaf.{u} O').mapHomologicalComplex
      (ComplexShape.up ℤ)).obj (ProjectiveResolution.of (K (idx j))).cochainComplex
  let fc : ∀ j, Kc j ⟶ Kc (j + 1) := fun j =>
    ((extendScalars a ⋙ PresheafOfModules.toPresheaf.{u} O').mapHomologicalComplex
      (ComplexShape.up ℤ)).map (homOfLift (incl (hmono j))).hom'
  have h1 : ∀ p : ℤ, 0 < p → IsZero ((Kc 0).homology p) := fun p hp =>
    ShortComplex.isZero_homology_of_isZero_X₂ _
      (Functor.map_isZero (extendScalars a ⋙ PresheafOfModules.toPresheaf.{u} O')
        (CochainComplex.isZero_of_isStrictlyLE
          (ProjectiveResolution.of (K (idx 0))).cochainComplex 0 p hp))
  have h2 : ∀ j : ℕ, j < k → HomologicalComplex.homologyMap (fc j) (-(j : ℤ)) = 0 := fun j hj =>
    homologyMap_map_hom'_eq_zero_of_objectwise a (incl (hmono j)) j P hdet
      fun U hU => hobj U hU (idx j) (idx (j + 1)) (hmono j) j (hstep j hj)
  obtain ⟨hfac, hfaceq⟩ := main_covariant k Kc fc h1 h2
  have hmid : IsZero ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} (-(i : ℤ))).obj
      ((Stacks.CategoryHomology.totalDerivedColimit C AddCommGrpCat.{u}).obj
        (DerivedCategory.Q.obj ((Kc k).truncLE (-(k : ℤ)))))) :=
    Stacks.CategoryHomology.isZero_homology_totalDerivedColimit_obj C AddCommGrpCat.{u} _
      (-(k : ℤ)) (-(i : ℤ)) (by omega)
  have hzero : ((Stacks.CategoryHomology.totalDerivedColimit C AddCommGrpCat.{u} ⋙
      DerivedCategory.homologyFunctor AddCommGrpCat.{u} (-(i : ℤ))).map
        (DerivedCategory.Q.map (chainComp Kc fc k))) = 0 := by
    have hz := hmid.eq_of_tgt
      ((Stacks.CategoryHomology.totalDerivedColimit C AddCommGrpCat.{u} ⋙
        DerivedCategory.homologyFunctor AddCommGrpCat.{u} (-(i : ℤ))).map hfac) 0
    rw [hfaceq, Functor.map_comp, hz, zero_comp]
  have hstep1 : ∀ (m n : ℕ) (h : n ≤ m),
      (derivedTensorPresheaf a).map
            (DerivedCategory.Q.map (ProjectiveResolution.of (K m)).π') ≫
          (derivedTensorPresheaf a).map (DerivedCategory.Q.map
            ((HomologicalComplex.single (PresheafOfModules.{u} O) (ComplexShape.up ℤ) 0).map
              (incl h))) =
        (tensorPresheafIso a (ProjectiveResolution.of (K m)).cochainComplex).hom ≫
          DerivedCategory.Q.map
              (((extendScalars a ⋙ PresheafOfModules.toPresheaf.{u} O').mapHomologicalComplex
                (ComplexShape.up ℤ)).map (homOfLift (incl h)).hom') ≫
            (tensorPresheafIso a (ProjectiveResolution.of (K n)).cochainComplex).inv ≫
              (derivedTensorPresheaf a).map
                (DerivedCategory.Q.map (ProjectiveResolution.of (K n)).π') := by
    intro m n h
    rw [← Functor.map_comp, ← DerivedCategory.Q.map_comp, ← hom'_comp_π'_single (incl h),
      DerivedCategory.Q.map_comp, Functor.map_comp, tensorPresheafIso_naturality' a,
      Category.assoc, Category.assoc]
  have hchain : ∀ t, idx t ≤ idx 0 := fun t => antitone_nat_of_succ_le hmono t.zero_le
  have htel : ∀ t : ℕ,
      (derivedTensorPresheaf a).map
            (DerivedCategory.Q.map (ProjectiveResolution.of (K (idx 0))).π') ≫
          (derivedTensorPresheaf a).map (DerivedCategory.Q.map
            ((HomologicalComplex.single (PresheafOfModules.{u} O) (ComplexShape.up ℤ) 0).map
              (incl (hchain t)))) =
        (tensorPresheafIso a (ProjectiveResolution.of (K (idx 0))).cochainComplex).hom ≫
          DerivedCategory.Q.map (chainComp Kc fc t) ≫
            (tensorPresheafIso a (ProjectiveResolution.of (K (idx t))).cochainComplex).inv ≫
              (derivedTensorPresheaf a).map
                (DerivedCategory.Q.map (ProjectiveResolution.of (K (idx t))).π') := by
    intro t
    induction t with
    | zero =>
        have e0 : incl (hchain 0) = 𝟙 (K (idx 0)) := incl_self _ _
        have eL : (HomologicalComplex.single (PresheafOfModules.{u} O) (ComplexShape.up ℤ) 0).map
            (incl (hchain 0)) = 𝟙 _ := by
          rw [e0]; exact CategoryTheory.Functor.map_id _ _
        have eL2 : DerivedCategory.Q.map
            ((HomologicalComplex.single (PresheafOfModules.{u} O) (ComplexShape.up ℤ) 0).map
              (incl (hchain 0))) = 𝟙 _ := by
          rw [eL]; exact CategoryTheory.Functor.map_id _ _
        have eL3 : (derivedTensorPresheaf a).map (DerivedCategory.Q.map
            ((HomologicalComplex.single (PresheafOfModules.{u} O) (ComplexShape.up ℤ) 0).map
              (incl (hchain 0)))) = 𝟙 _ := by
          rw [eL2]; exact CategoryTheory.Functor.map_id _ _
        have eR : DerivedCategory.Q.map (chainComp Kc fc 0) =
            𝟙 (DerivedCategory.Q.obj (Kc 0)) := CategoryTheory.Functor.map_id _ _
        rw [eL3, eR]
        refine (Category.comp_id _).trans ((Iso.hom_inv_id_assoc
          (tensorPresheafIso a (ProjectiveResolution.of (K (idx 0))).cochainComplex)
          ((derivedTensorPresheaf a).map
            (DerivedCategory.Q.map (ProjectiveResolution.of (K (idx 0))).π'))).symm.trans ?_)
        exact congrArg
          ((tensorPresheafIso a (ProjectiveResolution.of (K (idx 0))).cochainComplex).hom ≫ ·)
          (Category.id_comp _).symm
    | succ t ih =>
        have hcomp : incl (hchain (t + 1)) = incl (hchain t) ≫ incl (hmono t) :=
          (incl_comp (hmono t) (hchain t)).symm
        rw [hcomp, Functor.map_comp, Functor.map_comp, Functor.map_comp, ← Category.assoc, ih,
          Category.assoc, Category.assoc, Category.assoc,
          hstep1 (idx t) (idx (t + 1)) (hmono t), Iso.inv_hom_id_assoc,
          show chainComp Kc fc (t + 1) = chainComp Kc fc t ≫ fc t from rfl,
          DerivedCategory.Q.map_comp, Category.assoc]
  have hQiso : IsIso (DerivedCategory.Q.map (ProjectiveResolution.of (K (idx 0))).π') :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2 inferInstance
  have happ := congrArg
    (Stacks.CategoryHomology.totalDerivedColimit C AddCommGrpCat.{u} ⋙
      DerivedCategory.homologyFunctor AddCommGrpCat.{u} (-(i : ℤ))).map (htel k)
  simp only [Functor.map_comp, hzero, zero_comp, comp_zero] at happ
  exact zero_of_epi_comp _ happ

end Stacks.ChaoticSite

end
