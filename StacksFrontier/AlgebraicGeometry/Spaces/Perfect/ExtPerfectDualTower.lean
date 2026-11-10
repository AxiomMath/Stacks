module

public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.ExtPerfectDirectImage
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.SmallEtaleDualExtAddEquiv
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.ExtRepresentingTowerStageMaps
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.TensorPullbackComplexSingle

/-!
# `Ext` out of the dual of `Rf_* RSheafHom(E, 𝒢^•)` and its transition maps

Let `f : X ⟶ Y` be as in Stacks 08JN (`Y` Noetherian, `f` locally of finite type and
quasi-separated), `E` a perfect object of `D(𝒪_X)`, `𝒢^•` a bounded complex of coherent
`𝒪_X`-modules flat over `Y` with support proper over `Y`, and `K = Rf_* RSheafHom(E, 𝒢^•)`,
a perfect object of `D(𝒪_Y)` (Stacks 0DKK).  For `L = K^∨` the dual perfect object
(Stacks 08JJ) this file constructs the map

`Hom(L, M) ⟶ Hom(E, 𝒢^• ⊗^L Lf^*M)`,

natural in `M ∈ D(𝒪_Y)` and bijective for `M ∈ D_QCoh(𝒪_Y)`, and its shifted form.  These are
the identifications `Ext^i(Lₙ, ℱ) = H^i(Y, Kₙ ⊗^L ℱ) = Ext^i(Eₙ, 𝒢^• ⊗ f^*ℱ)` of the proof of
Stacks 08JR, part (B).  A map `E ⟶ E'` of perfect objects induces a map `L ⟶ L'` compatible
with these identifications: since `L'` lies in `D_QCoh(𝒪_Y)`, the Yoneda argument
`AlgebraicGeometry.Space.exists_comp_eq_comp_of_surjective` produces it.

## Main definitions

* `AlgebraicGeometry.Space.smallEtaleDualHomAddEquiv`: `Hom(K^∨, M) ≃+ Hom(𝒪_Y, K ⊗^L M)`.
* `AlgebraicGeometry.Space.extPerfectDualHom`: `Hom(K^∨, M) →+ Hom(E, 𝒢^• ⊗^L Lf^*M)`.

## References

* [Stacks Project, Tag 08JR](https://stacks.math.columbia.edu/tag/08JR)
* [Stacks Project, Tag 08JN](https://stacks.math.columbia.edu/tag/08JN)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

/-- **A Yoneda argument for natural maps out of `Hom`.**  Let `θ : Hom(L, -) ⟶ Hom(P, Φ -)` and
`θ' : Hom(L', -) ⟶ Hom(P', Φ -)` be natural, and `p : P ⟶ P'`.  If `θ` is surjective at `L'`,
there is `λ : L ⟶ L'` with `θ(λ ≫ e) = p ≫ θ'(e)` for every `e : L' ⟶ M`. -/
theorem CategoryTheory.exists_comp_eq_comp_of_surjective {C D : Type*} [Category C] [Category D]
    (Φ : C ⥤ D) {L L' : C} {P P' : D} (p : P ⟶ P')
    (θ : ∀ M : C, (L ⟶ M) → (P ⟶ Φ.obj M))
    (hθ : ∀ {M M' : C} (q : M ⟶ M') (e : L ⟶ M), θ M' (e ≫ q) = θ M e ≫ Φ.map q)
    (θ' : ∀ M : C, (L' ⟶ M) → (P' ⟶ Φ.obj M))
    (hθ' : ∀ {M M' : C} (q : M ⟶ M') (e : L' ⟶ M), θ' M' (e ≫ q) = θ' M e ≫ Φ.map q)
    (hs : Function.Surjective (θ L')) :
    ∃ l : L ⟶ L', ∀ (M : C) (e : L' ⟶ M), θ M (l ≫ e) = p ≫ θ' M e := by
  obtain ⟨l, hl⟩ := hs (p ≫ θ' L' (𝟙 L'))
  refine ⟨l, fun M e => ?_⟩
  rw [hθ, hl, Category.assoc, ← hθ', Category.id_comp]

/-- **A natural map out of `Hom` and the boundary maps.**  For `θ : Hom(L, -) ⟶ Hom(P, Φ -)`
natural, with `Φ` commuting with the shifts, and `a : M₃ ⟶ M₁[1]`, the value of `θ` on
`e ≫ a[i] ≫ (M₁[1][i] ≅ M₁[j])`, followed by `Φ(M₁[j]) ≅ (Φ M₁)[j]`, is the value on `e`
followed by `Φ(M₃[i]) ≅ (Φ M₃)[i]`, `(Φ a ≫ (Φ(M₁[1]) ≅ (Φ M₁)[1]))[i]` and
`(Φ M₁)[1][i] ≅ (Φ M₁)[j]`. -/
theorem CategoryTheory.natural_comp_shiftFunctorAdd'_inv_commShiftIso {C D : Type*} [Category C]
    [Category D] [HasShift C ℤ] [HasShift D ℤ] (Φ : C ⥤ D) [Φ.CommShift ℤ] {L : C} {P : D}
    (θ : ∀ M : C, (L ⟶ M) → (P ⟶ Φ.obj M))
    (hθ : ∀ {M M' : C} (q : M ⟶ M') (e : L ⟶ M), θ M' (e ≫ q) = θ M e ≫ Φ.map q)
    {M₁ M₃ : C} (a : M₃ ⟶ M₁⟦(1 : ℤ)⟧) (i j : ℤ) (h : 1 + i = j) (e : L ⟶ M₃⟦i⟧) :
    θ _ (e ≫ a⟦i⟧' ≫ (shiftFunctorAdd' C 1 i j h).inv.app M₁) ≫ (Φ.commShiftIso j).hom.app M₁ =
      θ _ e ≫ (Φ.commShiftIso i).hom.app M₃ ≫
        (Φ.map a ≫ (Φ.commShiftIso (1 : ℤ)).hom.app M₁)⟦i⟧' ≫
          (shiftFunctorAdd' D 1 i j h).inv.app (Φ.obj M₁) := by
  rw [hθ, Category.assoc, Functor.map_comp_shiftFunctorAdd'_inv_commShiftIso]

/-- **A natural map out of `Hom` followed by a comparison, and the boundary maps.**  The
abstract form of the compatibility of `AlgebraicGeometry.Space.extPerfectDualExtEquiv` with
boundary maps: for `θ : Hom(L, -) ⟶ Hom(P, Φ -)` natural, comparisons `τₖ : Φ Mₖ ⟶ Nₖ` and
`a : M₃ ⟶ M₁[1]`, `δ : N₃ ⟶ N₁[1]` with `Φ a` corresponding to `δ`, the shifted maps
`e ↦ θ(e) ≫ (Φ(-[i]) ≅ (Φ -)[i]) ≫ τ[i]` carry composition with `a` to composition with `δ`. -/
theorem CategoryTheory.natural_comp_commShiftIso_comp_shift_delta {C D : Type*} [Category C]
    [Category D] [HasShift C ℤ] [HasShift D ℤ] (Φ : C ⥤ D) [Φ.CommShift ℤ] {L : C} {P : D}
    (θ : ∀ M : C, (L ⟶ M) → (P ⟶ Φ.obj M))
    (hθ : ∀ {M M' : C} (q : M ⟶ M') (e : L ⟶ M), θ M' (e ≫ q) = θ M e ≫ Φ.map q)
    {M₁ M₃ : C} {N₁ N₃ : D} (a : M₃ ⟶ M₁⟦(1 : ℤ)⟧) (τ₁ : Φ.obj M₁ ⟶ N₁) (τ₃ : Φ.obj M₃ ⟶ N₃)
    (δ : N₃ ⟶ N₁⟦(1 : ℤ)⟧)
    (hδ : Φ.map a ≫ (Φ.commShiftIso (1 : ℤ)).hom.app M₁ ≫ τ₁⟦(1 : ℤ)⟧' = τ₃ ≫ δ)
    (i : ℤ) (e : L ⟶ M₃⟦i⟧) :
    θ _ (e ≫ a⟦i⟧' ≫ (shiftFunctorAdd' C 1 i (i + 1) (add_comm 1 i)).inv.app M₁) ≫
        (Φ.commShiftIso (i + 1)).hom.app M₁ ≫ τ₁⟦i + 1⟧' =
      (θ _ e ≫ (Φ.commShiftIso i).hom.app M₃ ≫ τ₃⟦i⟧') ≫ δ⟦i⟧' ≫
        (shiftFunctorAdd' D 1 i (i + 1) (add_comm 1 i)).inv.app N₁ := by
  have hk := CategoryTheory.natural_comp_shiftFunctorAdd'_inv_commShiftIso Φ θ hθ a i (i + 1)
    (add_comm 1 i) e
  have hn := ((shiftFunctorAdd' D 1 i (i + 1) (add_comm 1 i)).inv.naturality τ₁).symm
  have key : (Φ.map a ≫ (Φ.commShiftIso (1 : ℤ)).hom.app M₁)⟦i⟧' ≫ (τ₁⟦(1 : ℤ)⟧')⟦i⟧' =
      τ₃⟦i⟧' ≫ δ⟦i⟧' := by
    rw [← Functor.map_comp, ← Functor.map_comp, Category.assoc, hδ]
  simp only [Functor.comp_map] at hn
  rw [← Category.assoc, hk]
  simp only [Category.assoc]
  rw [hn, ← Category.assoc ((Φ.map a ≫ _)⟦i⟧'), key, Category.assoc]

namespace AlgebraicGeometry.Space

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) {X Y : AlgebraicSpaces B S hS}

section AbelianPriority

attribute [local instance 5000] SheafOfModules.instAbelian

/-- The derived category `D(𝒪_Z)` of modules on the small étale site of `Z`, in the model
`HasDerivedCategory.standard`; an abbreviation, which keeps the elaboration of statements with
many objects of `D(𝒪_Z)` cheap. -/
abbrev smallEtaleModulesDerived (Z : AlgebraicSpaces B S hS) : Type (u + 1) :=
  DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Z))

/-- A module `ℱ` on `Z` placed in degree `0`, as an object of `D(𝒪_Z)`. -/
abbrev smallEtaleModulesSingle {Z : AlgebraicSpaces B S hS}
    (F : SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Z)) :
    smallEtaleModulesDerived B S hS Z :=
  (DerivedCategory.singleFunctor
    (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Z)) 0).obj F

/-- A morphism of modules on `Z` placed in degree `0`, as a morphism of `D(𝒪_Z)`. -/
abbrev smallEtaleModulesSingleMap {Z : AlgebraicSpaces B S hS}
    {F F' : SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Z)} (q : F ⟶ F') :
    smallEtaleModulesSingle B S hS F ⟶ smallEtaleModulesSingle B S hS F' :=
  (DerivedCategory.singleFunctor
    (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Z)) 0).map q

/-- The cohomology sheaf functor `H^j : D(𝒪_Z) ⥤ Mod(𝒪_Z)`. -/
abbrev smallEtaleModulesHomology (Z : AlgebraicSpaces B S hS) (j : ℤ) :
    smallEtaleModulesDerived B S hS Z ⥤
      SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Z) :=
  DerivedCategory.homologyFunctor (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Z)) j

/-- Perfectness of an object of `D(𝒪_Z)` (an abbreviation fixing the spelling of the model). -/
abbrev SmallEtaleIsPerfect {Z : AlgebraicSpaces B S hS}
    (E : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Z))) : Prop :=
  (smallEtaleRingedSite B S hS Z.1 Z.2).IsPerfect E

/-- Pseudo-coherence of an object of `D(𝒪_Z)` (an abbreviation fixing the spelling of the
model). -/
abbrev SmallEtaleIsPseudoCoherent {Z : AlgebraicSpaces B S hS}
    (E : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Z))) : Prop :=
  (smallEtaleRingedSite B S hS Z.1 Z.2).IsPseudoCoherent E

/-- The hypotheses of Stacks 0DKJ on a complex `𝒢^•` (an abbreviation fixing the spelling). -/
abbrev SmallEtaleFlatProperSupport (f : X ⟶ Y) (hf : IsLocallyOfFiniteType B S hS f.hom)
    (G : CochainComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) ℤ) : Prop :=
  FlatProperSupportComplex B S hS f hf G

/-- **`Hom(K^∨, M) ≃+ Hom(𝒪_Y, K ⊗^L M)` for a perfect `K`**: the identification
`AlgebraicGeometry.Space.smallEtaleHomAddEquivUnitTensorDual` for `K^∨`, read through the double
dual isomorphism `K^∨∨ ≅ K`. -/
def smallEtaleDualHomAddEquiv
    (K : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)))
    (hK : SmallEtaleIsPerfect B S hS K)
    (M : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y))) :
    (smallEtaleDerivedDual B S hS Y K ⟶ M) ≃+
      (structureDerived Y ⟶ ((smallEtaleDerivedTensor B S hS Y).obj K).obj M) :=
  (smallEtaleHomAddEquivUnitTensorDual B S hS Y (smallEtaleDerivedDual B S hS Y K)
      (isPerfect_smallEtaleDerivedDual B S hS Y K hK) M).trans
    { toFun := fun h => h ≫ (smallEtaleDerivedTensorBidualIso B S hS Y K hK).hom.app M
      invFun := fun h => h ≫ (smallEtaleDerivedTensorBidualIso B S hS Y K hK).inv.app M
      left_inv := fun h => by simp
      right_inv := fun h => by simp
      map_add' := fun h h' => Preadditive.add_comp _ _ _ _ _ _ }

/-- `AlgebraicGeometry.Space.smallEtaleDualHomAddEquiv` is natural in `M`. -/
theorem smallEtaleDualHomAddEquiv_naturality
    (K : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)))
    (hK : SmallEtaleIsPerfect B S hS K)
    {M M' : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y))}
    (q : M ⟶ M') (g : smallEtaleDerivedDual B S hS Y K ⟶ M) :
    smallEtaleDualHomAddEquiv B S hS K hK M' (g ≫ q) =
      smallEtaleDualHomAddEquiv B S hS K hK M g ≫
        ((smallEtaleDerivedTensor B S hS Y).obj K).map q := by
  change smallEtaleHomAddEquivUnitTensorDual B S hS Y _ _ M' (g ≫ q) ≫ _ =
    (smallEtaleHomAddEquivUnitTensorDual B S hS Y _ _ M g ≫ _) ≫ _
  rw [smallEtaleHomAddEquivUnitTensorDual_naturality, Category.assoc, Category.assoc,
    NatTrans.naturality]

section Comparison

variable (hTop : B.Contains (⊤_ Scheme.{u})) (f : X ⟶ Y) (hf : IsLocallyOfFiniteType B S hS f.hom)
  (hfqs : IsQuasiSeparated B S hS f.hom) (hY : IsNoetherian B S hS hTop Y.1)
  (E : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)))
  (hE : SmallEtaleIsPerfect B S hS E)
  (G : CochainComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) ℤ)
  (hG : SmallEtaleFlatProperSupport B S hS f hf G)

include hTop hfqs hY hE hG in
/-- `K = Rf_* RSheafHom(E, 𝒢^•)` is perfect (Stacks 0DKK). -/
theorem isPerfect_extPerfectDirectImageObj :
    SmallEtaleIsPerfect B S hS (extPerfectDirectImageObj B S hS f E G) :=
  isPerfect_derivedModulePushforward_smallEtaleDerivedSheafHom B S hS hTop f hf hfqs hY E hE G hG

/-- The dual `L = K^∨` of `K = Rf_* RSheafHom(E, 𝒢^•)`. -/
abbrev extPerfectDualObj :
    DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)) :=
  smallEtaleDerivedDual B S hS Y (extPerfectDirectImageObj B S hS f E G)

/-- **`Hom(K^∨, M) ⟶ Hom(E, 𝒢^• ⊗^L Lf^*M)`**: `Hom(K^∨, M) = Hom(𝒪_Y, K ⊗^L M)` followed by
`AlgebraicGeometry.Space.extPerfectUnitHomNatTrans`. -/
def extPerfectDualHom
    (M : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y))) :
    (extPerfectDualObj B S hS f E G ⟶ M) →+
      (E ⟶ (extPerfectCoefficientFunctor B S hS f G).obj M) :=
  ((extPerfectUnitHomNatTrans B S hS hTop f hf hfqs hY E hE G hG).app M).hom.comp
    (smallEtaleDualHomAddEquiv B S hS (extPerfectDirectImageObj B S hS f E G)
      (isPerfect_extPerfectDirectImageObj B S hS hTop f hf hfqs hY E hE G hG) M).toAddMonoidHom

/-- `AlgebraicGeometry.Space.extPerfectDualHom` is natural in `M`. -/
theorem extPerfectDualHom_naturality
    {M M' : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y))}
    (q : M ⟶ M') (e : extPerfectDualObj B S hS f E G ⟶ M) :
    extPerfectDualHom B S hS hTop f hf hfqs hY E hE G hG M' (e ≫ q) =
      extPerfectDualHom B S hS hTop f hf hfqs hY E hE G hG M e ≫
        (extPerfectCoefficientFunctor B S hS f G).map q := by
  have h := ConcreteCategory.congr_hom
    ((extPerfectUnitHomNatTrans B S hS hTop f hf hfqs hY E hE G hG).naturality q)
    (smallEtaleDualHomAddEquiv B S hS (extPerfectDirectImageObj B S hS f E G)
      (isPerfect_extPerfectDirectImageObj B S hS hTop f hf hfqs hY E hE G hG) M e)
  exact (congrArg ((extPerfectUnitHomNatTrans B S hS hTop f hf hfqs hY E hE G hG).app M').hom
    (smallEtaleDualHomAddEquiv_naturality B S hS _
      (isPerfect_extPerfectDirectImageObj B S hS hTop f hf hfqs hY E hE G hG) q e)).trans h

/-- `AlgebraicGeometry.Space.extPerfectDualHom` is bijective for `M ∈ D_QCoh(𝒪_Y)`. -/
theorem bijective_extPerfectDualHom
    (M : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)))
    (hM : QcohDerived B S hS Y M) :
    Function.Bijective (extPerfectDualHom B S hS hTop f hf hfqs hY E hE G hG M) := by
  have := isIso_extPerfectUnitHomNatTrans_app B S hS hTop f hf hfqs hY E hE G hG M hM
  exact ((ConcreteCategory.bijective_of_isIso
    ((extPerfectUnitHomNatTrans B S hS hTop f hf hfqs hY E hE G hG).app M))).comp
      (AddEquiv.bijective _)

/- The map is used through `extPerfectDualHom_naturality` and `bijective_extPerfectDualHom` only;
keeping it irreducible stops unification from unfolding it. -/
attribute [irreducible] extPerfectDualHom

/-- The functor `ℱ ↦ 𝒢^• ⊗ f^*ℱ` from `𝒪_Y`-modules to `D(𝒪_X)`. -/
abbrev extPerfectCoefficientSingleFunctor :
    SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y) ⥤
      smallEtaleModulesDerived B S hS X :=
  HomologicalComplex.single _ (ComplexShape.up ℤ) 0 ⋙ tensorPullbackComplex f G ⋙
    DerivedCategory.Q

/-- The type of comparisons `τ : 𝒢^• ⊗^L Lf^*Q(-) ⟶ Q(𝒢^• ⊗ f^*(-))` of coefficients. -/
abbrev ExtPerfectCoefficientComparison : Type (u + 1) :=
  DerivedCategory.Q ⋙ extPerfectCoefficientFunctor B S hS f G ⟶
    tensorPullbackComplex f G ⋙ DerivedCategory.Q

/-- **The boundary map `𝒢^• ⊗ f^*ℱ₃ ⟶ (𝒢^• ⊗ f^*ℱ₁)[1]`** of the distinguished triangle in
`D(𝒪_X)` of a short exact sequence `0 ⟶ 𝒢^• ⊗ f^*ℱ₁ ⟶ 𝒢^• ⊗ f^*ℱ₂ ⟶ 𝒢^• ⊗ f^*ℱ₃ ⟶ 0` of
complexes (`DerivedCategory.triangleOfSESδ`), with source and target in the spelling
`AlgebraicGeometry.Space.extPerfectCoefficientObj`. -/
def extPerfectCoefficientDelta
    (T : ShortComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)))
    (hexT : ((T.map (HomologicalComplex.single
        (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)) (ComplexShape.up ℤ) 0)).map
          (tensorPullbackComplex f G)).ShortExact) :
    extPerfectCoefficientObj B S hS f G T.X₃ ⟶
      (extPerfectCoefficientObj B S hS f G T.X₁)⟦(1 : ℤ)⟧ :=
  DerivedCategory.triangleOfSESδ hexT

/-- `𝒢^• ⊗^L Lf^*(ℱ[0][i]) ≅ (𝒢^• ⊗ f^*ℱ)[i]` from an invertible comparison of coefficients. -/
def extPerfectCoefficientShiftIso (τ : ExtPerfectCoefficientComparison B S hS f G)
    (F : SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y))
    (hτF : IsIso (extPerfectCoefficientComparison B S hS f G τ F)) (i : ℤ) :
    (extPerfectCoefficientFunctor B S hS f G).obj ((smallEtaleModulesSingle B S hS F)⟦i⟧) ≅
      ((extPerfectCoefficientSingleFunctor B S hS f G).obj F)⟦i⟧ :=
  ((extPerfectCoefficientFunctor B S hS f G).commShiftIso i).app _ ≪≫ (shiftFunctor _ i).mapIso
    (@asIso _ _ _ _ (extPerfectCoefficientComparison B S hS f G τ F) hτF)

/-- **`Ext^i(K^∨, ℱ) ≃+ Ext^i(E, 𝒢^• ⊗ f^*ℱ)` for quasi-coherent `ℱ`**:
`AlgebraicGeometry.Space.extPerfectDualHom` at `ℱ[0][i]`, followed by the commutation of
`𝒢^• ⊗^L Lf^*-` with the shift and the comparison of coefficients. -/
def extPerfectDualExtEquiv (τ : ExtPerfectCoefficientComparison B S hS f G)
    (F : SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y))
    (hF : F.IsQuasicoherentOnSite) (hτF : IsIso (extPerfectCoefficientComparison B S hS f G τ F))
    (i : ℤ) :
    (extPerfectDualObj B S hS f E G ⟶ (smallEtaleModulesSingle B S hS F)⟦i⟧) ≃+
      (E ⟶ ((extPerfectCoefficientSingleFunctor B S hS f G).obj F)⟦i⟧) :=
  AddEquiv.ofBijective ((Preadditive.rightComp _
      (extPerfectCoefficientShiftIso B S hS f G τ F hτF i).hom).comp
    (extPerfectDualHom B S hS hTop f hf hfqs hY E hE G hG ((smallEtaleModulesSingle B S hS F)⟦i⟧)))
    ((Iso.homToEquiv (extPerfectCoefficientShiftIso B S hS f G τ F hτF i)).bijective.comp
      (bijective_extPerfectDualHom B S hS hTop f hf hfqs hY E hE G hG _
        (qcohDerived_shift _ i (qcohDerived_Q_singleFunctor_obj B S hS F hF))))

/-- `AlgebraicGeometry.Space.extPerfectDualExtEquiv` sends `e` to
`AlgebraicGeometry.Space.extPerfectDualHom` of `e`, followed by the commutation of
`𝒢^• ⊗^L Lf^*-` with the shift `[i]` and the shifted comparison of coefficients. -/
theorem extPerfectDualExtEquiv_apply (τ : ExtPerfectCoefficientComparison B S hS f G)
    (F : SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y))
    (hF : F.IsQuasicoherentOnSite) (hτF : IsIso (extPerfectCoefficientComparison B S hS f G τ F))
    (i : ℤ) (e : extPerfectDualObj B S hS f E G ⟶ (smallEtaleModulesSingle B S hS F)⟦i⟧) :
    extPerfectDualExtEquiv B S hS hTop f hf hfqs hY E hE G hG τ F hF hτF i e =
      extPerfectDualHom B S hS hTop f hf hfqs hY E hE G hG _ e ≫
        ((extPerfectCoefficientFunctor B S hS f G).commShiftIso i).hom.app _ ≫
          (extPerfectCoefficientComparison B S hS f G τ F)⟦i⟧' :=
  rfl

/-- **`AlgebraicGeometry.Space.extPerfectDualExtEquiv` is natural in `ℱ`.** -/
theorem extPerfectDualExtEquiv_naturality (τ : ExtPerfectCoefficientComparison B S hS f G)
    {F F' : SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)}
    (hF : F.IsQuasicoherentOnSite) (hF' : F'.IsQuasicoherentOnSite)
    (hτF : IsIso (extPerfectCoefficientComparison B S hS f G τ F))
    (hτF' : IsIso (extPerfectCoefficientComparison B S hS f G τ F')) (q : F ⟶ F') (i : ℤ)
    (e : extPerfectDualObj B S hS f E G ⟶ (smallEtaleModulesSingle B S hS F)⟦i⟧) :
    extPerfectDualExtEquiv B S hS hTop f hf hfqs hY E hE G hG τ F' hF' hτF' i
        (e ≫ (smallEtaleModulesSingleMap B S hS q)⟦i⟧') =
      extPerfectDualExtEquiv B S hS hTop f hf hfqs hY E hE G hG τ F hF hτF i e ≫
        ((extPerfectCoefficientSingleFunctor B S hS f G).map q)⟦i⟧' := by
  have hτq : (extPerfectCoefficientFunctor B S hS f G).map (extPerfectSingleMap B S hS q) ≫
      extPerfectCoefficientComparison B S hS f G τ F' =
      extPerfectCoefficientComparison B S hS f G τ F ≫ extPerfectCoefficientMap B S hS f G q :=
    τ.naturality _
  rw [extPerfectDualExtEquiv_apply, extPerfectDualExtEquiv_apply, extPerfectDualHom_naturality,
    Category.assoc, Category.assoc, Category.assoc, Functor.commShiftIso_hom_naturality_assoc]
  refine congrArg (fun t => extPerfectDualHom B S hS hTop f hf hfqs hY E hE G hG _ e ≫
    ((extPerfectCoefficientFunctor B S hS f G).commShiftIso i).hom.app _ ≫ t) ?_
  rw [← Functor.map_comp, ← Functor.map_comp]
  exact congrArg (fun t => t⟦i⟧') hτq

/-- **`AlgebraicGeometry.Space.extPerfectDualExtEquiv` is compatible with the boundary maps.** -/
theorem extPerfectDualExtEquiv_delta (τ : ExtPerfectCoefficientComparison B S hS f G)
    (T : ShortComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)))
    (hT : T.ShortExact)
    (hexT : ((T.map (HomologicalComplex.single
        (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)) (ComplexShape.up ℤ) 0)).map
          (tensorPullbackComplex f G)).ShortExact)
    (hδT : (extPerfectCoefficientFunctor B S hS f G).map hT.singleδ ≫
        ((extPerfectCoefficientFunctor B S hS f G).commShiftIso (1 : ℤ)).hom.app
          (smallEtaleModulesSingle B S hS T.X₁) ≫
        (extPerfectCoefficientComparison B S hS f G τ T.X₁)⟦(1 : ℤ)⟧' =
      extPerfectCoefficientComparison B S hS f G τ T.X₃ ≫
        extPerfectCoefficientDelta B S hS f G T hexT)
    (h₁ : T.X₁.IsQuasicoherentOnSite) (h₃ : T.X₃.IsQuasicoherentOnSite)
    (hτ₁ : IsIso (extPerfectCoefficientComparison B S hS f G τ T.X₁))
    (hτ₃ : IsIso (extPerfectCoefficientComparison B S hS f G τ T.X₃)) (i : ℤ)
    (e : extPerfectDualObj B S hS f E G ⟶ (smallEtaleModulesSingle B S hS T.X₃)⟦i⟧) :
    extPerfectDualExtEquiv B S hS hTop f hf hfqs hY E hE G hG τ T.X₁ h₁ hτ₁ (i + 1)
        (e ≫ hT.singleδ⟦i⟧' ≫ (shiftFunctorAdd' (smallEtaleModulesDerived B S hS Y) 1 i (i + 1)
          (add_comm 1 i)).inv.app (smallEtaleModulesSingle B S hS T.X₁)) =
      extPerfectDualExtEquiv B S hS hTop f hf hfqs hY E hE G hG τ T.X₃ h₃ hτ₃ i e ≫
        (extPerfectCoefficientDelta B S hS f G T hexT)⟦i⟧' ≫
          (shiftFunctorAdd' (smallEtaleModulesDerived B S hS X) 1 i (i + 1)
            (add_comm 1 i)).inv.app (extPerfectCoefficientObj B S hS f G T.X₁) := by
  rw [extPerfectDualExtEquiv_apply, extPerfectDualExtEquiv_apply]
  exact CategoryTheory.natural_comp_commShiftIso_comp_shift_delta
    (extPerfectCoefficientFunctor B S hS f G)
    (fun M => extPerfectDualHom B S hS hTop f hf hfqs hY E hE G hG M)
    (fun q e => extPerfectDualHom_naturality B S hS hTop f hf hfqs hY E hE G hG q e)
    hT.singleδ (extPerfectCoefficientComparison B S hS f G τ T.X₁)
    (extPerfectCoefficientComparison B S hS f G τ T.X₃)
    (extPerfectCoefficientDelta B S hS f G T hexT)
    hδT i e

/-- **Transitions.**  If `l : K^∨ ⟶ K'^∨` and `p : E ⟶ E'` satisfy
`Θ(l ≫ e) = p ≫ Θ'(e)`, then `AlgebraicGeometry.Space.extPerfectDualExtEquiv` is compatible
with them. -/
theorem extPerfectDualExtEquiv_comp (τ : ExtPerfectCoefficientComparison B S hS f G)
    {E' : smallEtaleModulesDerived B S hS X}
    (hE' : SmallEtaleIsPerfect B S hS E') (p : E ⟶ E')
    (l : extPerfectDualObj B S hS f E G ⟶ extPerfectDualObj B S hS f E' G)
    (hl : ∀ (M : smallEtaleModulesDerived B S hS Y) (e : extPerfectDualObj B S hS f E' G ⟶ M),
      extPerfectDualHom B S hS hTop f hf hfqs hY E hE G hG M (l ≫ e) =
        p ≫ extPerfectDualHom B S hS hTop f hf hfqs hY E' hE' G hG M e)
    (F : SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y))
    (hF : F.IsQuasicoherentOnSite) (hτF : IsIso (extPerfectCoefficientComparison B S hS f G τ F))
    (i : ℤ) (e : extPerfectDualObj B S hS f E' G ⟶ (smallEtaleModulesSingle B S hS F)⟦i⟧) :
    extPerfectDualExtEquiv B S hS hTop f hf hfqs hY E hE G hG τ F hF hτF i (l ≫ e) =
      p ≫ extPerfectDualExtEquiv B S hS hTop f hf hfqs hY E' hE' G hG τ F hF hτF i e := by
  rw [extPerfectDualExtEquiv_apply, extPerfectDualExtEquiv_apply, hl, Category.assoc]

/-- The dual `L = K^∨` of `K = Rf_* RSheafHom(E, 𝒢^•)` is perfect. -/
private theorem isPerfect_extPerfectDualObj
    (hTop : B.Contains (⊤_ Scheme.{u})) (hfqs : IsQuasiSeparated B S hS f.hom)
    (hY : IsNoetherian B S hS hTop Y.1) (hE : SmallEtaleIsPerfect B S hS E)
    (hG : SmallEtaleFlatProperSupport B S hS f hf G) :
    SmallEtaleIsPerfect B S hS (extPerfectDualObj B S hS f E G) :=
  isPerfect_smallEtaleDerivedDual B S hS Y _
    (isPerfect_extPerfectDirectImageObj B S hS hTop f hf hfqs hY E hE G hG)

end Comparison

end AbelianPriority

section Tower

variable (hTop : B.Contains (⊤_ Scheme.{u})) (f : X ⟶ Y) (hf : IsLocallyOfFiniteType B S hS f.hom)
  (hfqs : IsQuasiSeparated B S hS f.hom) (hY : IsNoetherian B S hS hTop Y.1)
  (E : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)))
  (hE : SmallEtaleIsPerfect B S hS E)
  (G : CochainComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) ℤ)
  (hG : SmallEtaleFlatProperSupport B S hS f hf G)

/-! ### The tower, read in the spelling `Modules` of `𝒪_Y`-modules

`AlgebraicGeometry.Space.exists_isPseudoCoherent_extAddEquiv_stageMaps_of_tower` is stated for
`D(𝒪_Y)` in the spelling `AlgebraicGeometry.Space.Modules`; the objects above are in the spelling
`ringedToposStructureRingSheaf`.  The two are definitionally equal, but the comparison is costly,
so each declaration below crosses once. -/

variable (tE : ℕ ⥤ smallEtaleModulesDerived B S hS X)
  (htE : ∀ n, SmallEtaleIsPerfect B S hS (tE.obj n))

include hTop hf hfqs hY hG htE in
/-- There is a map `l : Lₙ ⟶ Lₙ₊₁` of the duals `Lₙ = (Rf_* RSheafHom(tEₙ, 𝒢^•))^∨` with
`Θₙ(l ≫ e) = t ≫ Θₙ₊₁(e)` for every `e : Lₙ₊₁ ⟶ M`, where `t : tEₙ ⟶ tEₙ₊₁` is the
transition map and `Θₙ` is `AlgebraicGeometry.Space.extPerfectDualHom` for `tEₙ`. -/
theorem exists_extPerfectDualTowerMap (n : ℕ) :
    ∃ l : extPerfectDualObj B S hS f (tE.obj n) G ⟶ extPerfectDualObj B S hS f (tE.obj (n + 1)) G,
      ∀ (M : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)))
        (e : extPerfectDualObj B S hS f (tE.obj (n + 1)) G ⟶ M),
        extPerfectDualHom B S hS hTop f hf hfqs hY (tE.obj n) (htE n) G hG M (l ≫ e) =
          tE.map (homOfLE (Nat.le_succ n)) ≫
            extPerfectDualHom B S hS hTop f hf hfqs hY (tE.obj (n + 1)) (htE (n + 1)) G hG M e :=
  CategoryTheory.exists_comp_eq_comp_of_surjective (extPerfectCoefficientFunctor B S hS f G)
    (tE.map (homOfLE (Nat.le_succ n)))
    (fun M => extPerfectDualHom B S hS hTop f hf hfqs hY (tE.obj n) (htE n) G hG M)
    (extPerfectDualHom_naturality B S hS hTop f hf hfqs hY _ (htE n) G hG)
    (fun M => extPerfectDualHom B S hS hTop f hf hfqs hY (tE.obj (n + 1)) (htE (n + 1)) G hG M)
    (extPerfectDualHom_naturality B S hS hTop f hf hfqs hY _ (htE (n + 1)) G hG)
    (bijective_extPerfectDualHom B S hS hTop f hf hfqs hY (tE.obj n) (htE n) G hG _
      (qcohDerived_of_isPerfect B S hS Y _
        (isPerfect_extPerfectDualObj B S hS f hf _ G hTop hfqs hY (htE (n + 1)) hG))).2

/-- **The tower `L₀ ⟶ L₁ ⟶ ⋯` of the proof of Stacks 08JR (B)**: `Lₙ` is the dual of
`Rf_* RSheafHom(tEₙ, 𝒢^•)` (`AlgebraicGeometry.Space.extPerfectDualObj`), and `Lₙ ⟶ Lₙ₊₁` is
the map of `AlgebraicGeometry.Space.exists_extPerfectDualTowerMap`. -/
def extPerfectDualTower : ℕ ⥤ DerivedCategory (Modules.{u, u} B S hS Y.1 Y.2) :=
  Functor.ofSequence (C := DerivedCategory (Modules.{u, u} B S hS Y.1 Y.2))
    (X := fun n => extPerfectDualObj B S hS f (tE.obj n) G)
    (fun n => (exists_extPerfectDualTowerMap B S hS hTop f hf hfqs hY G hG tE htE n).choose)

/-- The `n`-th object of `AlgebraicGeometry.Space.extPerfectDualTower` is the dual of
`Rf_* RSheafHom(tEₙ, 𝒢^•)`. -/
theorem extPerfectDualTower_obj (n : ℕ) :
    (extPerfectDualTower B S hS hTop f hf hfqs hY G hG tE htE).obj n =
      extPerfectDualObj B S hS f (tE.obj n) G :=
  rfl

/-- Every object of `AlgebraicGeometry.Space.extPerfectDualTower` is perfect. -/
theorem isPerfect_extPerfectDualTower_obj (n : ℕ) :
    (smallEtaleRingedSite B S hS Y.1 Y.2).IsPerfect
      ((extPerfectDualTower B S hS hTop f hf hfqs hY G hG tE htE).obj n) :=
  isPerfect_extPerfectDualObj B S hS f hf _ G hTop hfqs hY (htE n) hG

/-- The functor `ℱ ↦ 𝒢^• ⊗ f^*ℱ`, from `𝒪_Y`-modules in the spelling `Modules`. -/
abbrev extPerfectCoefficientModulesFunctor :
    Modules.{u, u} B S hS Y.1 Y.2 ⥤ smallEtaleModulesDerived B S hS X :=
  extPerfectCoefficientSingleFunctor B S hS f G

/-- `AlgebraicGeometry.Space.extPerfectDualExtEquiv` at the `n`-th stage of the tower. -/
def extPerfectDualTowerExt
    (τ : ExtPerfectCoefficientComparison B S hS f G)
    (hτ : ∀ F : SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y),
      IsIso (extPerfectCoefficientComparison B S hS f G τ F))
    (n : ℕ) (F : Modules.{u, u} B S hS Y.1 Y.2) (hF : F.IsQuasicoherentOnSite) (i : ℤ) :
    ((extPerfectDualTower B S hS hTop f hf hfqs hY G hG tE htE).obj n ⟶
        ((DerivedCategory.singleFunctor (Modules.{u, u} B S hS Y.1 Y.2) 0).obj F)⟦i⟧) ≃+
      (tE.obj n ⟶ ((extPerfectCoefficientModulesFunctor B S hS f G).obj F)⟦i⟧) :=
  extPerfectDualExtEquiv B S hS hTop f hf hfqs hY (tE.obj n) (htE n) G hG τ F hF (hτ F) i

/-- `AlgebraicGeometry.Space.extPerfectDualTowerExt` is natural in the quasi-coherent `ℱ`. -/
theorem extPerfectDualTowerExt_naturality
    (τ : ExtPerfectCoefficientComparison B S hS f G)
    (hτ : ∀ F : SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y),
      IsIso (extPerfectCoefficientComparison B S hS f G τ F))
    (n : ℕ) {F F' : Modules.{u, u} B S hS Y.1 Y.2} (hF : F.IsQuasicoherentOnSite)
    (hF' : F'.IsQuasicoherentOnSite)
    (q : F ⟶ F') (i : ℤ)
    (e : (extPerfectDualTower B S hS hTop f hf hfqs hY G hG tE htE).obj n ⟶
      ((DerivedCategory.singleFunctor (Modules.{u, u} B S hS Y.1 Y.2) 0).obj F)⟦i⟧) :
    extPerfectDualTowerExt B S hS hTop f hf hfqs hY G hG tE htE τ hτ n F' hF' i
        (e ≫ ((DerivedCategory.singleFunctor (Modules.{u, u} B S hS Y.1 Y.2) 0).map q)⟦i⟧') =
      extPerfectDualTowerExt B S hS hTop f hf hfqs hY G hG tE htE τ hτ n F hF i e ≫
        ((extPerfectCoefficientModulesFunctor B S hS f G).map q)⟦i⟧' :=
  extPerfectDualExtEquiv_naturality B S hS hTop f hf hfqs hY (tE.obj n) (htE n) G hG τ hF hF'
    (hτ F) (hτ F') q i e

/-- `AlgebraicGeometry.Space.extPerfectDualTowerExt` is compatible with the transition maps
`Lₙ ⟶ Lₙ₊₁` and `tEₙ ⟶ tEₙ₊₁`. -/
theorem extPerfectDualTowerExt_trans
    (τ : ExtPerfectCoefficientComparison B S hS f G)
    (hτ : ∀ F : SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y),
      IsIso (extPerfectCoefficientComparison B S hS f G τ F))
    (n : ℕ) (F : Modules.{u, u} B S hS Y.1 Y.2) (hF : F.IsQuasicoherentOnSite) (i : ℤ)
    (e : (extPerfectDualTower B S hS hTop f hf hfqs hY G hG tE htE).obj (n + 1) ⟶
      ((DerivedCategory.singleFunctor (Modules.{u, u} B S hS Y.1 Y.2) 0).obj F)⟦i⟧) :
    extPerfectDualTowerExt B S hS hTop f hf hfqs hY G hG tE htE τ hτ n F hF i
        ((extPerfectDualTower B S hS hTop f hf hfqs hY G hG tE htE).map
          (homOfLE (Nat.le_succ n)) ≫ e) =
      tE.map (homOfLE (Nat.le_succ n)) ≫
        extPerfectDualTowerExt B S hS hTop f hf hfqs hY G hG tE htE τ hτ (n + 1) F hF i e := by
  have hm := Functor.ofSequence_map_homOfLE_succ
    (C := DerivedCategory (Modules.{u, u} B S hS Y.1 Y.2))
    (X := fun n => extPerfectDualObj B S hS f (tE.obj n) G)
    (fun n => (exists_extPerfectDualTowerMap B S hS hTop f hf hfqs hY G hG tE htE n).choose) n
  refine (congrArg (extPerfectDualTowerExt B S hS hTop f hf hfqs hY G hG tE htE τ hτ n F hF i)
    (congrArg (· ≫ e) hm)).trans ?_
  exact extPerfectDualExtEquiv_comp B S hS hTop f hf hfqs hY (tE.obj n) (htE n) G hG τ
    (htE (n + 1)) _ _
    (exists_extPerfectDualTowerMap B S hS hTop f hf hfqs hY G hG tE htE n).choose_spec
    F hF (hτ F) i e

/-- `AlgebraicGeometry.Space.extPerfectCoefficientDelta` for a short exact sequence of modules
in the spelling `Modules`. -/
def extPerfectCoefficientModulesDelta
    (hex : ∀ T : ShortComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)),
      T.ShortExact → ((T.map (HomologicalComplex.single
        (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)) (ComplexShape.up ℤ) 0)).map
          (tensorPullbackComplex f G)).ShortExact)
    (T : ShortComplex (Modules.{u, u} B S hS Y.1 Y.2)) (hT : T.ShortExact) :
    (extPerfectCoefficientModulesFunctor B S hS f G).obj T.X₃ ⟶
      ((extPerfectCoefficientModulesFunctor B S hS f G).obj T.X₁)⟦(1 : ℤ)⟧ :=
  extPerfectCoefficientDelta B S hS f G T (hex T hT)

/-- `AlgebraicGeometry.Space.extPerfectDualTowerExt` is compatible with the boundary maps of a
short exact sequence of quasi-coherent modules. -/
theorem extPerfectDualTowerExt_delta
    (τ : ExtPerfectCoefficientComparison B S hS f G)
    (hτ : ∀ F : SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y),
      IsIso (extPerfectCoefficientComparison B S hS f G τ F))
    (hex : ∀ T : ShortComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)),
      T.ShortExact → ((T.map (HomologicalComplex.single
        (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)) (ComplexShape.up ℤ) 0)).map
          (tensorPullbackComplex f G)).ShortExact)
    (hδ : ∀ (T : ShortComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)))
      (hT : T.ShortExact),
      (extPerfectCoefficientFunctor B S hS f G).map hT.singleδ ≫
        ((extPerfectCoefficientFunctor B S hS f G).commShiftIso (1 : ℤ)).hom.app
          (smallEtaleModulesSingle B S hS T.X₁) ≫
        (extPerfectCoefficientComparison B S hS f G τ T.X₁)⟦(1 : ℤ)⟧' =
      extPerfectCoefficientComparison B S hS f G τ T.X₃ ≫
        extPerfectCoefficientDelta B S hS f G T (hex T hT))
    (n : ℕ) (T : ShortComplex (Modules.{u, u} B S hS Y.1 Y.2)) (hT : T.ShortExact)
    (h₁ : T.X₁.IsQuasicoherentOnSite) (h₃ : T.X₃.IsQuasicoherentOnSite) (i : ℤ)
    (e : ShiftedHom ((extPerfectDualTower B S hS hTop f hf hfqs hY G hG tE htE).obj n)
      ((DerivedCategory.singleFunctor (Modules.{u, u} B S hS Y.1 Y.2) 0).obj T.X₃) i) :
    extPerfectDualTowerExt B S hS hTop f hf hfqs hY G hG tE htE τ hτ n T.X₁ h₁ (i + 1)
        (e.comp hT.singleδ (add_comm 1 i)) =
      (show ShiftedHom (tE.obj n) ((extPerfectCoefficientModulesFunctor B S hS f G).obj T.X₃) i
        from extPerfectDualTowerExt B S hS hTop f hf hfqs hY G hG tE htE τ hτ n T.X₃ h₃ i e).comp
          (extPerfectCoefficientModulesDelta B S hS f G hex T hT) (add_comm 1 i) :=
  extPerfectDualExtEquiv_delta B S hS hTop f hf hfqs hY (tE.obj n) (htE n) G hG τ T hT (hex T hT)
    (hδ T hT) h₁ h₃ (hτ _) (hτ _) i e

include hTop hf hfqs hY hG in
/-- **Stacks 08JR (B) from a comparison of coefficients, for a tower of perfect approximations.**
Let `E₀ ∈ D(𝒪_X)` with a tower `tE₀ ⟶ tE₁ ⟶ ⋯ ⟶ E₀` of perfect objects whose `n`-th map is an
isomorphism on cohomology in degrees `> -(n + 2)`, and suppose `𝒢ⁿ = 0` for `n < a`.  Given a
comparison `τ` of coefficients as in
`AlgebraicGeometry.Space.extPerfectCohomologyIsoOfCoefficient`, the tower
`Lₙ = (Rf_* RSheafHom(tEₙ, 𝒢^•))^∨` (`AlgebraicGeometry.Space.extPerfectDualTower`) has a
pseudo-coherent homotopy colimit `L` with `Ext^i(L, ℱ) ≅ Ext^i(E₀, 𝒢^• ⊗ f^*ℱ)`, natural in the
quasi-coherent `ℱ` and compatible with the boundary maps; at every stage, `Ext^i(L, ℱ)` is
`Ext^i(Lₙ, ℱ) = Ext^i(tEₙ, 𝒢^• ⊗ f^*ℱ)` (`AlgebraicGeometry.Space.extPerfectDualTowerExt`). -/
theorem exists_isPseudoCoherent_extPerfectDual_of_coefficient
    (τ : ExtPerfectCoefficientComparison B S hS f G)
    (hτ : ∀ F : SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y),
      IsIso (extPerfectCoefficientComparison B S hS f G τ F))
    (hex : ∀ T : ShortComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)),
      T.ShortExact → ((T.map (HomologicalComplex.single
        (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)) (ComplexShape.up ℤ) 0)).map
          (tensorPullbackComplex f G)).ShortExact)
    (hδ : ∀ (T : ShortComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)))
      (hT : T.ShortExact),
      (extPerfectCoefficientFunctor B S hS f G).map hT.singleδ ≫
        ((extPerfectCoefficientFunctor B S hS f G).commShiftIso (1 : ℤ)).hom.app
          (smallEtaleModulesSingle B S hS T.X₁) ≫
        (extPerfectCoefficientComparison B S hS f G τ T.X₁)⟦(1 : ℤ)⟧' =
      extPerfectCoefficientComparison B S hS f G τ T.X₃ ≫
        extPerfectCoefficientDelta B S hS f G T (hex T hT))
    (a : ℤ) (hGa : ∀ n : ℤ, n < a → IsZero (G.X n))
    (E₀ : smallEtaleModulesDerived B S hS X)
    (cE : ∀ n, tE.obj n ⟶ E₀)
    (hcEcomp : ∀ n, tE.map (homOfLE (Nat.le_succ n)) ≫ cE (n + 1) = cE n)
    (hcE : ∀ (n : ℕ) (j : ℤ), -((n : ℤ) + 2) < j →
      IsIso ((smallEtaleModulesHomology B S hS X j).map (cE n))) :
    ∃ (Linf : DerivedCategory (Modules.{u, u} B S hS Y.1 Y.2))
      (ι : ∀ n, (extPerfectDualTower B S hS hTop f hf hfqs hY G hG tE htE).obj n ⟶ Linf)
      (_ : ∀ n, (extPerfectDualTower B S hS hTop f hf hfqs hY G hG tE htE).map
        (homOfLE (Nat.le_succ n)) ≫ ι (n + 1) = ι n)
      (_ : ∀ (n : ℕ) (j : ℤ), -((n : ℤ) + a) < j →
        IsIso ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS Y.1 Y.2) j).map (ι n)))
      (_ : (smallEtaleRingedSite B S hS Y.1 Y.2).IsPseudoCoherent Linf)
      (Φ : ∀ (F : Modules.{u, u} B S hS Y.1 Y.2) (_ : F.IsQuasicoherentOnSite) (i : ℤ),
        (Linf ⟶ ((DerivedCategory.singleFunctor (Modules.{u, u} B S hS Y.1 Y.2) 0).obj F)⟦i⟧) ≃+
          (E₀ ⟶ ((extPerfectCoefficientModulesFunctor B S hS f G).obj F)⟦i⟧)),
      (∀ (F : Modules.{u, u} B S hS Y.1 Y.2) (hF : F.IsQuasicoherentOnSite) (i : ℤ)
        (e : Linf ⟶ ((DerivedCategory.singleFunctor (Modules.{u, u} B S hS Y.1 Y.2) 0).obj F)⟦i⟧)
        (n : ℕ),
        cE n ≫ Φ F hF i e =
          extPerfectDualTowerExt B S hS hTop f hf hfqs hY G hG tE htE τ hτ n F hF i (ι n ≫ e)) ∧
      (∀ {F F' : Modules.{u, u} B S hS Y.1 Y.2} (hF : F.IsQuasicoherentOnSite)
        (hF' : F'.IsQuasicoherentOnSite) (q : F ⟶ F') (i : ℤ)
        (e : Linf ⟶ ((DerivedCategory.singleFunctor (Modules.{u, u} B S hS Y.1 Y.2) 0).obj F)⟦i⟧),
        Φ F' hF' i
            (e ≫ ((DerivedCategory.singleFunctor (Modules.{u, u} B S hS Y.1 Y.2) 0).map q)⟦i⟧') =
          Φ F hF i e ≫ ((extPerfectCoefficientModulesFunctor B S hS f G).map q)⟦i⟧') ∧
      (∀ (T : ShortComplex (Modules.{u, u} B S hS Y.1 Y.2)) (hT : T.ShortExact)
        (h₁ : T.X₁.IsQuasicoherentOnSite), T.X₂.IsQuasicoherentOnSite →
        ∀ (h₃ : T.X₃.IsQuasicoherentOnSite) (i : ℤ)
        (e : ShiftedHom Linf
          ((DerivedCategory.singleFunctor (Modules.{u, u} B S hS Y.1 Y.2) 0).obj T.X₃) i),
        Φ T.X₁ h₁ (i + 1) (e.comp hT.singleδ (add_comm 1 i)) =
          (show ShiftedHom E₀ ((extPerfectCoefficientModulesFunctor B S hS f G).obj T.X₃) i from
            Φ T.X₃ h₃ i e).comp (extPerfectCoefficientModulesDelta B S hS f G hex T hT)
              (add_comm 1 i)) :=
  exists_isPseudoCoherent_extAddEquiv_stageMaps_of_tower Y hY.1 E₀ tE cE hcEcomp hcE
    (extPerfectCoefficientModulesFunctor B S hS f G) a
    (fun F _ => isGE_Q_obj_tensorPullbackComplex_single f G a hGa F)
    (extPerfectDualTower B S hS hTop f hf hfqs hY G hG tE htE)
    (isPerfect_extPerfectDualTower_obj B S hS hTop f hf hfqs hY G hG tE htE)
    (extPerfectDualTowerExt B S hS hTop f hf hfqs hY G hG tE htE τ hτ)
    (extPerfectDualTowerExt_naturality B S hS hTop f hf hfqs hY G hG tE htE τ hτ)
    (extPerfectDualTowerExt_trans B S hS hTop f hf hfqs hY G hG tE htE τ hτ)
    (fun T hT _ _ _ => extPerfectCoefficientModulesDelta B S hS f G hex T hT)
    (fun n T hT h₁ _ h₃ i e => extPerfectDualTowerExt_delta B S hS hTop f hf hfqs hY G hG tE htE τ
      hτ hex hδ n T hT h₁ h₃ i e)

end Tower

end AlgebraicGeometry.Space

end
