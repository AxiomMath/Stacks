module

public import StacksFrontier.Homology.CompositeCollapse
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Comparison.DerivedFunctor
public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryNatTrans

/-!
# Naturality of the collapse and evaluation isomorphisms of right derived functors

For an additive left exact `G : C ⥤ D` carrying injectives to `T`-acyclic objects and an object
`A` with `Rⁿ G (A) = 0` for `n > 0`, `Stacks.RightDerivedComp.objIsoOfAcyclicImage` identifies
`Rⁿ (G ⋙ T) (A)` with `Rⁿ T (G A)`; and for an exact `T`,
`Stacks.DerivedFunctor.rightDerivedEvaluationIso` identifies `T (Rⁿ P (F))` with `Rⁿ (P ⋙ T) (F)`.
This file proves that both identifications are natural in the functors involved and that the
first is transitive in `G`.

All the statements come down to one computation
(`Stacks.RightDerivedComp.isoRightDerivedObjOfAcyclic_inv_eq`): the identification of `Rⁿ T (X)`
with the cohomology of `T` applied to a `T`-acyclic resolution of `X` is, for *every* injective
resolution `J` of `X` and every comparison of the resolution with `J`, the map on cohomology
induced by the comparison followed by the computation of `Rⁿ T (X)` on `J`. The comparison is
unique up to homotopy, and the computations on two injective resolutions differ by the map they
induce.

## Main results

* `Stacks.RightDerivedComp.isoRightDerivedObjOfAcyclic_inv_eq` — the identification on an
  acyclic resolution, along an arbitrary injective resolution and comparison.
* `Stacks.RightDerivedComp.objIsoOfAcyclicImage_hom_eq` — the collapse isomorphism, along an
  arbitrary injective resolution of `G A` and comparison.
* `Stacks.RightDerivedComp.rightDerived_whiskerLeft_comp_objIsoOfAcyclicImage` — naturality of
  the collapse in `T`.
* `Stacks.RightDerivedComp.rightDerived_whiskerRight_comp_objIsoOfAcyclicImage` — naturality of
  the collapse in `G`.
* `Stacks.RightDerivedComp.objIsoOfAcyclicImage_trans` — transitivity of the collapse in `G`.
* `Stacks.DerivedFunctor.app_comp_rightDerivedEvaluationIso` — naturality of the evaluation
  isomorphism in the exact functor `T`, from the naturality
  `Stacks.DerivedFunctor.complexHomologyIso_naturality` of the comparison on complexes.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Stacks.RightDerivedComp

section Rearrangement

variable {C : Type*} [Category C]

/-- Replacing a middle composite by an equal one, at an abstract category. -/
theorem comp_mid_comp_eq {X₀ X₁ X₂ X₃ Y Z : C} (i : X₀ ⟶ X₁) (a : X₁ ⟶ X₂) (b : X₂ ⟶ X₃)
    (a' : X₁ ⟶ Y) (b' : Y ⟶ X₃) (j : X₃ ⟶ Z) (h : a ≫ b = a' ≫ b') :
    i ≫ a ≫ b ≫ j = i ≫ a' ≫ b' ≫ j := by
  rw [← Category.assoc a b j, h, Category.assoc]

/-- Cancelling `e₁.inv ≫ e₁.hom` and `e₂.inv ≫ e₂.hom` on the two sides of an equation whose
middles agree, at an abstract category. -/
theorem comp_inv_hom_comp_eq {P Q N M R Z N' M' : C} (i : P ⟶ Q) (a : Q ⟶ N) (e₁ : M ≅ N)
    (b : N ⟶ R) (f : R ⟶ Z) (b' : Q ⟶ N') (e₂ : M' ≅ N') (a' : N' ⟶ R) (h : a ≫ b = b' ≫ a') :
    (i ≫ a ≫ e₁.inv) ≫ (e₁.hom ≫ b ≫ f) = (i ≫ b' ≫ e₂.inv) ≫ (e₂.hom ≫ a' ≫ f) := by
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [← Category.assoc a b f, h, Category.assoc]

/-- Cancelling `e₁.inv ≫ e₁.hom` on the left and replacing a square on the right, at an abstract
category. -/
theorem comp_inv_hom_comp_eq_comp {P Q N M R Z N' W : C} (i : P ⟶ Q) (a : Q ⟶ N) (e₁ : M ≅ N)
    (b : N ⟶ R) (f : R ⟶ Z) (b' : Q ⟶ N') (g : N' ⟶ W) (m : W ⟶ Z) (a' : N' ⟶ R)
    (h : a ≫ b = b' ≫ a') (hm : g ≫ m = a' ≫ f) :
    (i ≫ a ≫ e₁.inv) ≫ (e₁.hom ≫ b ≫ f) = (i ≫ b' ≫ g) ≫ m := by
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [hm, ← Category.assoc a b f, h, Category.assoc]

/-- Cancelling `e.inv ≫ e.hom` and composing the two middle factors, at an abstract category. -/
theorem comp_inv_hom_comp_eq_comp_single {P Q N M R Z : C} (i : P ⟶ Q) (a : Q ⟶ N) (e : M ≅ N)
    (b : N ⟶ R) (f : R ⟶ Z) (c : Q ⟶ R) (h : a ≫ b = c) :
    (i ≫ a ≫ e.inv) ≫ (e.hom ≫ b ≫ f) = i ≫ c ≫ f := by
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [← Category.assoc a b f, h]

/-- The cohomology map of a functor applied to a composite of complex maps is the composite of the
cohomology maps. -/
private theorem homologyMap_map_comp {D E : Type*} [Category* D] [Category* E] [Abelian D]
    [Abelian E] (F : D ⥤ E) [F.Additive] {K₁ K₂ K₃ : CochainComplex D ℕ}
    (f : K₁ ⟶ K₂) (g : K₂ ⟶ K₃) (n : ℕ) :
    HomologicalComplex.homologyMap ((F.mapHomologicalComplex _).map (f ≫ g)) n =
      HomologicalComplex.homologyMap ((F.mapHomologicalComplex _).map f) n ≫
        HomologicalComplex.homologyMap ((F.mapHomologicalComplex _).map g) n := by
  rw [Functor.map_comp, HomologicalComplex.homologyMap_comp]

/-- Two comparisons out of a quasi-isomorphism into a K-injective complex that agree after
precomposition induce the same map on cohomology after applying a functor. -/
private theorem homologyMap_map_eq_of_precomp_eq {D E : Type*} [Category* D] [Category* E]
    [Abelian D] [Abelian E] (F : D ⥤ E) [F.Additive] {Z : D}
    {K₂ K₃ : CochainComplex D ℕ} [∀ n, Injective (K₃.X n)]
    (ε : (CochainComplex.single₀ D).obj Z ⟶ K₂) [QuasiIso ε] {β₁ β₂ : K₂ ⟶ K₃}
    (h : ε ≫ β₁ = ε ≫ β₂) (n : ℕ) :
    HomologicalComplex.homologyMap ((F.mapHomologicalComplex _).map β₁) n =
      HomologicalComplex.homologyMap ((F.mapHomologicalComplex _).map β₂) n := by
  obtain ⟨h⟩ := CochainComplex.nonempty_homotopy_of_precomp_quasiIso ε (Homotopy.ofEq h)
  exact (F.mapHomotopy h).homologyMap_eq n

end Rearrangement

section AcyclicResolution

variable {D E : Type*} [Category* D] [Category* E] [Abelian D] [Abelian E] [EnoughInjectives D]
  (T : D ⥤ E) [T.Additive] [PreservesFiniteLimits T] {X : D} {K : CochainComplex D ℕ}

/-- **The computation of `Rⁿ T` on an acyclic resolution does not depend on the injective
resolution it is compared with.** For every injective resolution `J` of `X` and every comparison
`β` of the acyclic resolution `ε : X[0] ⟶ K` with `J`, the inverse of the identification of
`Rⁿ T (X)` with `Hⁿ (T K)` is the map on cohomology induced by `β`, followed by the computation
of `Rⁿ T (X)` on `J`. -/
theorem isoRightDerivedObjOfAcyclic_inv_eq (ε : (CochainComplex.single₀ D).obj X ⟶ K)
    [QuasiIso ε] (hK : ∀ q, acyclic T (K.X q)) (n : ℕ) (J : InjectiveResolution X)
    (β : K ⟶ J.cocomplex) (hβ : ε ≫ β = J.ι) :
    (isoRightDerivedObjOfAcyclic T ε hK n).inv =
      HomologicalComplex.homologyMap ((T.mapHomologicalComplex _).map β) n ≫
        (J.isoRightDerivedObj T n).inv := by
  let J₀ := injectiveResolution X
  let φ : J₀.cocomplex ⟶ J.cocomplex := InjectiveResolution.desc (𝟙 X) J J₀
  have hφ : J₀.ι ≫ φ = J.ι := by
    rw [InjectiveResolution.desc_commutes, CategoryTheory.Functor.map_id, Category.id_comp]
  have hJ : (J₀.isoRightDerivedObj T n).inv =
      HomologicalComplex.homologyMap ((T.mapHomologicalComplex _).map φ) n ≫
        (J.isoRightDerivedObj T n).inv := by
    have h := InjectiveResolution.isoRightDerivedObj_inv_naturality (𝟙 X) J₀ J φ
      (InjectiveResolution.desc_commutes_zero (𝟙 X) J J₀) T n
    rw [CategoryTheory.Functor.map_id, Category.comp_id] at h
    exact h
  have hhom := homologyMap_map_eq_of_precomp_eq T ε
    (β₁ := descOfResolution ε J₀ ≫ φ) (β₂ := β)
    (by rw [← Category.assoc, comp_descOfResolution, hφ, hβ]) n
  have hcomp := homologyMap_map_comp T (descOfResolution ε J₀) φ n
  have hdef : (isoRightDerivedObjOfAcyclic T ε hK n).inv =
      HomologicalComplex.homologyMap
          ((T.mapHomologicalComplex _).map (descOfResolution ε J₀)) n ≫
        (J₀.isoRightDerivedObj T n).inv := rfl
  exact hdef.trans ((congrArg (_ ≫ ·) hJ).trans ((Category.assoc _ _ _).symm.trans
    (congrArg (· ≫ (J.isoRightDerivedObj T n).inv) (hcomp.symm.trans hhom))))

end AcyclicResolution

section Collapse

variable {C D E : Type*} [Category* C] [Category* D] [Category* E] [Abelian C] [Abelian D]
  [Abelian E] [HasInjectiveResolutions C] [EnoughInjectives D]

/-- The augmentation of `G` applied to an injective resolution is natural in `G`. -/
theorem mapι_comp_mapHomologicalComplex_app {G G' : C ⥤ D} [G.Additive] [G'.Additive]
    (μ : G ⟶ G') {A : C} (I : InjectiveResolution A) :
    mapι G I ≫ (NatTrans.mapHomologicalComplex μ (ComplexShape.up ℕ)).app I.cocomplex =
      (CochainComplex.single₀ D).map (μ.app A) ≫ mapι G' I := by
  refine HomologicalComplex.from_single_hom_ext ?_
  simp only [HomologicalComplex.comp_f, mapι_f_zero, NatTrans.mapHomologicalComplex_app_f,
    CochainComplex.single₀_map_f_zero]
  exact μ.naturality (I.ι.f 0)

variable (G : C ⥤ D) [G.Additive] [PreservesFiniteLimits G] (T : D ⥤ E) [T.Additive]
  [PreservesFiniteLimits T] {A : C}

/-- **The collapse isomorphism, along an arbitrary injective resolution of `G A`.** On the chosen
injective resolution `I` of `A`, the collapse `Rⁿ (G ⋙ T) (A) ≅ Rⁿ T (G A)` is the computation of
`Rⁿ (G ⋙ T)` on `I`, the map on cohomology induced by any comparison `β` of `G I` with an
injective resolution `J` of `G A`, and the inverse of the computation of `Rⁿ T` on `J`. -/
theorem objIsoOfAcyclicImage_hom_eq (hA : ∀ n, 0 < n → IsZero ((G.rightDerived n).obj A))
    (hGT : ∀ Z : C, Injective Z → acyclic T (G.obj Z)) (n : ℕ) (J : InjectiveResolution (G.obj A))
    (β : mapCocomplex G (injectiveResolution A) ⟶ J.cocomplex)
    (hβ : mapι G (injectiveResolution A) ≫ β = J.ι) :
    (objIsoOfAcyclicImage G T hA hGT n).hom =
      ((injectiveResolution A).isoRightDerivedObj (G ⋙ T) n).hom ≫
        HomologicalComplex.homologyMap ((T.mapHomologicalComplex _).map β) n ≫
          (J.isoRightDerivedObj T n).inv := by
  have : QuasiIso (mapι G (injectiveResolution A)) :=
    quasiIso_mapι G (injectiveResolution A) hA
  exact congrArg (((injectiveResolution A).isoRightDerivedObj (G ⋙ T) n).hom ≫ ·)
    (isoRightDerivedObjOfAcyclic_inv_eq T (mapι G (injectiveResolution A))
      (fun q => hGT _ ((injectiveResolution A).injective q)) n J β hβ)


/-- **The collapse is natural in `T`.** For `ν : T ⟶ T'`, the right derived functor of `G ⋙ ν`
followed by the collapse for `T'` is the collapse for `T` followed by `Rⁿ ν` at `G A`. -/
theorem rightDerived_whiskerLeft_comp_objIsoOfAcyclicImage {T' : D ⥤ E} [T'.Additive]
    [PreservesFiniteLimits T'] (ν : T ⟶ T')
    (hA : ∀ n, 0 < n → IsZero ((G.rightDerived n).obj A))
    (hGT : ∀ Z : C, Injective Z → acyclic T (G.obj Z))
    (hGT' : ∀ Z : C, Injective Z → acyclic T' (G.obj Z)) (n : ℕ) :
    (NatTrans.rightDerived (Functor.whiskerLeft G ν) n).app A ≫
        (objIsoOfAcyclicImage G T' hA hGT' n).hom =
      (objIsoOfAcyclicImage G T hA hGT n).hom ≫ (NatTrans.rightDerived ν n).app (G.obj A) := by
  have : QuasiIso (mapι G (injectiveResolution A)) := quasiIso_mapι G _ hA
  let β := descOfResolution (mapι G (injectiveResolution A)) (injectiveResolution (G.obj A))
  have hβ : mapι G (injectiveResolution A) ≫ β = (injectiveResolution (G.obj A)).ι :=
    comp_descOfResolution _ _
  have hmid : (HomologicalComplex.homologyFunctor E (ComplexShape.up ℕ) n).map
        ((NatTrans.mapHomologicalComplex (Functor.whiskerLeft G ν) (ComplexShape.up ℕ)).app
          (injectiveResolution A).cocomplex) ≫
      HomologicalComplex.homologyMap ((T'.mapHomologicalComplex _).map β) n =
      HomologicalComplex.homologyMap ((T.mapHomologicalComplex _).map β) n ≫
        (HomologicalComplex.homologyFunctor E (ComplexShape.up ℕ) n).map
          ((NatTrans.mapHomologicalComplex ν (ComplexShape.up ℕ)).app
            (injectiveResolution (G.obj A)).cocomplex) :=
    (HomologicalComplex.homologyMap_comp _ _ n).symm.trans
      ((congrArg (fun t => HomologicalComplex.homologyMap t n)
        ((NatTrans.mapHomologicalComplex ν (ComplexShape.up ℕ)).naturality β).symm).trans
        (HomologicalComplex.homologyMap_comp _ _ n))
  rw [objIsoOfAcyclicImage_hom_eq G T' hA hGT' n _ β hβ,
    objIsoOfAcyclicImage_hom_eq G T hA hGT n _ β hβ,
    InjectiveResolution.rightDerived_app_eq _ (injectiveResolution A),
    InjectiveResolution.rightDerived_app_eq _ (injectiveResolution (G.obj A))]
  exact comp_inv_hom_comp_eq _ _ _ _ _ _ _ _ hmid

/-- **The collapse is natural in `G`.** For `μ : G ⟶ G'`, the right derived functor of `μ ⋙ T`
followed by the collapse for `G'` is the collapse for `G` followed by `Rⁿ T` of `μ` at `A`. -/
theorem rightDerived_whiskerRight_comp_objIsoOfAcyclicImage {G' : C ⥤ D} [G'.Additive]
    [PreservesFiniteLimits G'] (μ : G ⟶ G')
    (hA : ∀ n, 0 < n → IsZero ((G.rightDerived n).obj A))
    (hA' : ∀ n, 0 < n → IsZero ((G'.rightDerived n).obj A))
    (hGT : ∀ Z : C, Injective Z → acyclic T (G.obj Z))
    (hGT' : ∀ Z : C, Injective Z → acyclic T (G'.obj Z)) (n : ℕ) :
    (NatTrans.rightDerived (Functor.whiskerRight μ T) n).app A ≫
        (objIsoOfAcyclicImage G' T hA' hGT' n).hom =
      (objIsoOfAcyclicImage G T hA hGT n).hom ≫ (T.rightDerived n).map (μ.app A) := by
  have : QuasiIso (mapι G (injectiveResolution A)) := quasiIso_mapι G _ hA
  have : QuasiIso (mapι G' (injectiveResolution A)) := quasiIso_mapι G' _ hA'
  let J := injectiveResolution (G.obj A)
  let J' := injectiveResolution (G'.obj A)
  let β := descOfResolution (mapι G (injectiveResolution A)) J
  let β' := descOfResolution (mapι G' (injectiveResolution A)) J'
  have hβ : mapι G (injectiveResolution A) ≫ β = J.ι := comp_descOfResolution _ _
  have hβ' : mapι G' (injectiveResolution A) ≫ β' = J'.ι := comp_descOfResolution _ _
  let φ : J.cocomplex ⟶ J'.cocomplex := InjectiveResolution.desc (μ.app A) J' J
  have hφ : J.ι ≫ φ = (CochainComplex.single₀ D).map (μ.app A) ≫ J'.ι :=
    InjectiveResolution.desc_commutes _ _ _
  have hmap := InjectiveResolution.isoRightDerivedObj_inv_naturality (μ.app A) J J' φ
    (InjectiveResolution.desc_commutes_zero _ _ _) T n
  have hhom : HomologicalComplex.homologyMap ((T.mapHomologicalComplex _).map
        ((NatTrans.mapHomologicalComplex μ (ComplexShape.up ℕ)).app
          (injectiveResolution A).cocomplex ≫ β')) n =
      HomologicalComplex.homologyMap ((T.mapHomologicalComplex _).map (β ≫ φ)) n := by
    refine homologyMap_map_eq_of_precomp_eq T (mapι G (injectiveResolution A)) ?_ n
    rw [← Category.assoc, mapι_comp_mapHomologicalComplex_app, Category.assoc, hβ',
      ← Category.assoc, hβ, hφ]
  have hmid : (HomologicalComplex.homologyFunctor E (ComplexShape.up ℕ) n).map
        ((NatTrans.mapHomologicalComplex (Functor.whiskerRight μ T) (ComplexShape.up ℕ)).app
          (injectiveResolution A).cocomplex) ≫
      HomologicalComplex.homologyMap ((T.mapHomologicalComplex _).map β') n =
      HomologicalComplex.homologyMap ((T.mapHomologicalComplex _).map β) n ≫
        (T.mapHomologicalComplex _ ⋙ HomologicalComplex.homologyFunctor _ _ n).map φ :=
    (homologyMap_map_comp T _ _ n).symm.trans (hhom.trans (homologyMap_map_comp T _ _ n))
  rw [objIsoOfAcyclicImage_hom_eq G' T hA' hGT' n J' β' hβ',
    objIsoOfAcyclicImage_hom_eq G T hA hGT n J β hβ,
    InjectiveResolution.rightDerived_app_eq _ (injectiveResolution A)]
  exact comp_inv_hom_comp_eq_comp _ _ _ _ _ _ _ _ _ hmid hmap

/-- **The collapse is transitive.** For `G₂ : D ⥤ D'`, the collapse along `G` for `G₂ ⋙ T₂`,
followed by the collapse along `G₂` at `G A`, is the collapse along `G ⋙ G₂`. -/
theorem objIsoOfAcyclicImage_trans {D' : Type*} [Category* D'] [Abelian D'] [EnoughInjectives D']
    (G₂ : D ⥤ D') [G₂.Additive] [PreservesFiniteLimits G₂] (T₂ : D' ⥤ E) [T₂.Additive]
    [PreservesFiniteLimits T₂] [PreservesFiniteLimits (G₂ ⋙ T₂)]
    [PreservesFiniteLimits (G ⋙ G₂)]
    (hA : ∀ n, 0 < n → IsZero ((G.rightDerived n).obj A))
    (hA₂ : ∀ n, 0 < n → IsZero ((G₂.rightDerived n).obj (G.obj A)))
    (hA₁₂ : ∀ n, 0 < n → IsZero (((G ⋙ G₂).rightDerived n).obj A))
    (hGT : ∀ Z : C, Injective Z → acyclic (G₂ ⋙ T₂) (G.obj Z))
    (hG₂T : ∀ Z : D, Injective Z → acyclic T₂ (G₂.obj Z))
    (hG₁₂T : ∀ Z : C, Injective Z → acyclic T₂ ((G ⋙ G₂).obj Z)) (n : ℕ) :
    (objIsoOfAcyclicImage G (G₂ ⋙ T₂) hA hGT n).hom ≫
        (objIsoOfAcyclicImage G₂ T₂ hA₂ hG₂T n).hom =
      (objIsoOfAcyclicImage (G ⋙ G₂) T₂ hA₁₂ hG₁₂T n).hom := by
  have : QuasiIso (mapι G (injectiveResolution A)) := quasiIso_mapι G _ hA
  have : QuasiIso (mapι G₂ (injectiveResolution (G.obj A))) := quasiIso_mapι G₂ _ hA₂
  let J₁ := injectiveResolution (G.obj A)
  let J₂ := injectiveResolution (G₂.obj (G.obj A))
  let β₁ := descOfResolution (mapι G (injectiveResolution A)) J₁
  let β₂ := descOfResolution (mapι G₂ J₁) J₂
  have hβ₁ : mapι G (injectiveResolution A) ≫ β₁ = J₁.ι := comp_descOfResolution _ _
  have hβ₂ : mapι G₂ J₁ ≫ β₂ = J₂.ι := comp_descOfResolution _ _
  have hβ : mapι (G ⋙ G₂) (injectiveResolution A) ≫
      (G₂.mapHomologicalComplex _).map β₁ ≫ β₂ = J₂.ι := by
    refine HomologicalComplex.from_single_hom_ext ?_
    have h₁ := HomologicalComplex.congr_hom hβ₁ 0
    have h₂ := HomologicalComplex.congr_hom hβ₂ 0
    simp only [HomologicalComplex.comp_f, mapι_f_zero] at h₁ h₂ ⊢
    rw [← h₂, ← h₁, Functor.mapHomologicalComplex_map_f]
    exact (Category.assoc _ _ _).symm.trans (congrArg (· ≫ β₂.f 0) (G₂.map_comp _ _).symm)
  rw [objIsoOfAcyclicImage_hom_eq G (G₂ ⋙ T₂) hA hGT n J₁ β₁ hβ₁,
    objIsoOfAcyclicImage_hom_eq G₂ T₂ hA₂ hG₂T n J₂ β₂ hβ₂,
    objIsoOfAcyclicImage_hom_eq (G ⋙ G₂) T₂ hA₁₂ hG₁₂T n J₂ _ hβ]
  exact comp_inv_hom_comp_eq_comp_single _ _ _ _ _ _
    (homologyMap_map_comp T₂ ((G₂.mapHomologicalComplex _).map β₁) β₂ n).symm

end Collapse


section Exact

variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
  [HasInjectiveResolutions C]

/-- **The higher right derived functors of an exact functor vanish.** -/
theorem isZero_rightDerived_obj_of_exact (G : C ⥤ D) [G.Additive] [PreservesFiniteLimits G]
    [PreservesFiniteColimits G] (A : C) (n : ℕ) (hn : 0 < n) :
    IsZero ((G.rightDerived n).obj A) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hex : ((G.mapHomologicalComplex (ComplexShape.up ℕ)).obj
      (injectiveResolution A).cocomplex).ExactAt (m + 1) :=
    ((injectiveResolution A).cocomplex_exactAt_succ m).map G
  exact ((HomologicalComplex.exactAt_iff_isZero_homology _ _).1 hex).of_iso
    ((injectiveResolution A).isoRightDerivedObj G (m + 1))

/-- Acyclicity is invariant under isomorphism. -/
theorem acyclic_of_iso (T : C ⥤ D) [T.Additive] {Z Z' : C} (e : Z ≅ Z') (h : acyclic T Z) :
    acyclic T Z' :=
  fun n hn => (h n hn).of_iso ((T.rightDerived n).mapIso e).symm

end Exact

end Stacks.RightDerivedComp

namespace Stacks.DerivedFunctor

variable {A D E : Type*} [Category A] [Category D] [Category E] [Abelian A] [Abelian D]
  [Abelian E]

/-- A commuting square with isomorphic sides commutes with the inverses, at an abstract
category. -/
theorem comp_inv_eq_inv_comp_of_square {C : Type*} [Category C] {X Y X' Y' : C} (e : X ≅ Y)
    (e' : X' ≅ Y') (x : Y ⟶ Y') (y : X ⟶ X') (h : e.hom ≫ x = y ≫ e'.hom) :
    x ≫ e'.inv = e.inv ≫ y := by
  rw [Iso.comp_inv_eq, Category.assoc, ← h, Iso.inv_hom_id_assoc]

/-- The inverse comparison, natural in the functor. -/
theorem app_comp_complexHomologyIso_inv_app {T T' : D ⥤ E} [T.Additive] [T.PreservesHomology]
    [T'.Additive] [T'.PreservesHomology] (ν : T ⟶ T') {ι : Type*} (c : ComplexShape ι) (i : ι)
    (K : HomologicalComplex D c) :
    ν.app (K.homology i) ≫ (complexHomologyIso T' c i).inv.app K =
      (complexHomologyIso T c i).inv.app K ≫
        HomologicalComplex.homologyMap ((NatTrans.mapHomologicalComplex ν c).app K) i := by
  exact comp_inv_eq_inv_comp_of_square ((complexHomologyIso T c i).app K)
    ((complexHomologyIso T' c i).app K) _ _ (complexHomologyIso_naturality ν c i K).symm

/-- The rearrangement behind `app_comp_rightDerivedEvaluationIso`, at an abstract category. -/
theorem evaluation_rearrange {C : Type*} [Category C] {A₀ A₁ B₀ B₁ C₀ C₁ R Z : C}
    (ν₀ : A₀ ⟶ A₁) (t : A₀ ⟶ B₀) (t' : A₁ ⟶ B₁) (ν₁ : B₀ ⟶ B₁) (c : B₀ ⟶ C₀) (c' : B₁ ⟶ C₁)
    (νc : C₀ ⟶ C₁) (e : R ≅ C₀) (f : C₁ ⟶ Z) (h₁ : ν₀ ≫ t' = t ≫ ν₁)
    (h₂ : ν₁ ≫ c' = c ≫ νc) :
    ν₀ ≫ t' ≫ c' ≫ f = (t ≫ c ≫ e.inv) ≫ (e.hom ≫ νc ≫ f) := by
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [← Category.assoc ν₀ t', h₁, Category.assoc, ← Category.assoc ν₁ c', h₂, Category.assoc]

variable [HasInjectiveResolutions A]

/-- **The evaluation isomorphism is natural in the exact functor.** For `ν : T ⟶ T'` between exact
functors, `ν` at `Rᵖ P (F)` followed by the evaluation isomorphism for `T'` is the evaluation
isomorphism for `T` followed by the right derived functor of `P ⋙ ν`. -/
theorem app_comp_rightDerivedEvaluationIso (P : A ⥤ D) [P.Additive] {T T' : D ⥤ E}
    [T.Additive] [T.PreservesHomology] [T'.Additive] [T'.PreservesHomology] (ν : T ⟶ T')
    (F : A) (p : ℕ) :
    ν.app ((P.rightDerived p).obj F) ≫ (rightDerivedEvaluationIso P T' F p).hom =
      (rightDerivedEvaluationIso P T F p).hom ≫
        (NatTrans.rightDerived (Functor.whiskerLeft P ν) p).app F := by
  rw [InjectiveResolution.rightDerived_app_eq _ (injectiveResolution F)]
  exact evaluation_rearrange _ _ _ _ _ _ _ _ _
    (ν.naturality ((injectiveResolution F).isoRightDerivedObj P p).hom).symm
    (app_comp_complexHomologyIso_inv_app ν (.up ℕ) p
      ((P.mapHomologicalComplex (.up ℕ)).obj (injectiveResolution F).cocomplex))

end Stacks.DerivedFunctor

end
