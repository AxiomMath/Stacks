module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleComplexes.CanonicalDerivedTensorGeneral.DerivedTensorBifunctor

/-!
# The canonical map to the total tensor product, and exactness at three universes

The canonical natural map `Stacks.SheafOfModules.toTensorGeneral` from the derived tensor
bifunctor to the ordinary total tensor product, the derived tensor product
`Stacks.SheafOfModules.derivedTensorProductOfExactGeneral` built from exactness in each variable,
and the reduction of that exactness to K-flat objects.
-/

/-! ### The canonical map to the ordinary total tensor product -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe c v w d

namespace Stacks.SheafOfModules

variable (X : AlgebraicGeometry.RingedSite.{c, v, w})
  [HasSheafify X.J AddCommGrpCat.{w}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{c, v, w, w, w} X.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{c, v, w, w, w} X.O).obj M).Additive]
  [∀ (K₁ K₂ : CochainComplex
      (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf.{c, v, w} X.O)) ℤ),
    HomologicalComplex.HasMapBifunctorReg K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)]

/-- A chosen K-flat resolution of a complex of sheaves of modules. -/
def kFlatResGeneral
    (K : CochainComplex (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) :
    CochainComplex (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ :=
  (exists_kFlat_quasiIso_general X K).choose

/-- The augmentation of the chosen K-flat resolution. -/
def kFlatResMapGeneral
    (K : CochainComplex (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) :
    kFlatResGeneral X K ⟶ K :=
  (exists_kFlat_quasiIso_general X K).choose_spec.choose

/-- The chosen K-flat resolution is K-flat. -/
theorem isKFlat_kFlatRes_general
    (K : CochainComplex (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) :
    IsKFlat X.O (kFlatResGeneral X K) :=
  (exists_kFlat_quasiIso_general X K).choose_spec.choose_spec.1

/-- The augmentation of the chosen K-flat resolution is a quasi-isomorphism. -/
instance quasiIso_kFlatResMap_general
    (K : CochainComplex (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) :
    QuasiIso (kFlatResMapGeneral X K) :=
  (exists_kFlat_quasiIso_general X K).choose_spec.choose_spec.2

variable [HasDerivedCategory.{d}
  (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf.{c, v, w} X.O))]

attribute [local instance] kFlatQ_isLocalization_general derivedTensorBifunctorLiftingGeneral

section Comparison

/-- The comparison isomorphism is natural in the K-flat variable alone. -/
theorem kFlatComparison_naturality_left_general
    {A B L : CochainComplex (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (hA : IsKFlat X.O A) (hB : IsKFlat X.O B) (c : A ⟶ B) :
    ((derivedTensorBifunctorGeneral X).map (DerivedCategory.Q.map c)).app
          (DerivedCategory.Q.obj L) ≫ (kFlatComparisonGeneral X B hB L).hom =
      (kFlatComparisonGeneral X A hA L).hom ≫
        DerivedCategory.Q.map (((Stacks.SheafOfModules.Tensor.tensorComplex X.O).map c).app L) := by
  simpa using kFlatComparison_naturality_general X hA hB c (𝟙 L)

end Comparison

/-- The isomorphism of derived tensor products induced by the chosen K-flat resolution of the
first factor. -/
instance isIso_derivedTensor_map_kFlatResMap_general
    (K L : CochainComplex (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) :
    IsIso (((derivedTensorBifunctorGeneral X).map
      (DerivedCategory.Q.map (kFlatResMapGeneral X K))).app (DerivedCategory.Q.obj L)) := by
  have : IsIso (DerivedCategory.Q.map (kFlatResMapGeneral X K)) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2 inferInstance
  infer_instance

/-- The canonical map from the derived tensor product to the ordinary total tensor product.
It is defined through the chosen K-flat resolution of the first factor;
`toTensor_comp_of_kFlat_general` shows that any map out of a K-flat complex computes it. -/
def toTensorGeneral
    (K L : CochainComplex (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) :
    ((derivedTensorBifunctorGeneral X).obj (DerivedCategory.Q.obj K)).obj
        (DerivedCategory.Q.obj L) ⟶
      DerivedCategory.Q.obj (((Stacks.SheafOfModules.Tensor.tensorComplex X.O).obj K).obj L) :=
  inv (((derivedTensorBifunctorGeneral X).map
      (DerivedCategory.Q.map (kFlatResMapGeneral X K))).app (DerivedCategory.Q.obj L)) ≫
    (kFlatComparisonGeneral X (kFlatResGeneral X K) (isKFlat_kFlatRes_general X K) L).hom ≫
    DerivedCategory.Q.map
      (((Stacks.SheafOfModules.Tensor.tensorComplex X.O).map (kFlatResMapGeneral X K)).app L)

/-- The defining property of `toTensorGeneral`, for the chosen resolution. -/
theorem toTensor_comp_kFlatResMap_general
    (K L : CochainComplex (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) :
    ((derivedTensorBifunctorGeneral X).map
          (DerivedCategory.Q.map (kFlatResMapGeneral X K))).app (DerivedCategory.Q.obj L) ≫
        toTensorGeneral X K L =
      (kFlatComparisonGeneral X (kFlatResGeneral X K) (isKFlat_kFlatRes_general X K) L).hom ≫
        DerivedCategory.Q.map
          (((Stacks.SheafOfModules.Tensor.tensorComplex X.O).map
            (kFlatResMapGeneral X K)).app L) := by
  rw [toTensorGeneral, IsIso.hom_inv_id_assoc]

/-- **The defining property of `toTensorGeneral`.** For *any* map `a : A ⟶ K` out of a K-flat
complex `A`, precomposing `toTensorGeneral` with the induced map of derived tensor products gives
the comparison at `A` followed by the ordinary total tensor of `a`. In particular the value of
`toTensorGeneral` does not depend on the chosen resolution. -/
theorem toTensor_comp_of_kFlat_general
    {A K : CochainComplex (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (hA : IsKFlat X.O A) (a : A ⟶ K)
    (L : CochainComplex (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) :
    ((derivedTensorBifunctorGeneral X).map (DerivedCategory.Q.map a)).app
          (DerivedCategory.Q.obj L) ≫ toTensorGeneral X K L =
      (kFlatComparisonGeneral X A hA L).hom ≫
        DerivedCategory.Q.map (((Stacks.SheafOfModules.Tensor.tensorComplex X.O).map a).app L) := by
  obtain ⟨hsat, _⟩ := quasiIso_isSaturated_and_isCompatibleWithTriangulation.{c, v, w} X.O
  have := hsat.hasRightCalculusOfFractions
  obtain ⟨ψ, hψ⟩ := MorphismProperty.HasRightCalculusOfFractions.exists_rightFraction
    (W := HomotopyCategory.quasiIso
      (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (ComplexShape.up ℤ))
    (MorphismProperty.LeftFraction.mk
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map a)
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map (kFlatResMapGeneral X K))
      ((HomotopyCategory.quotient_map_mem_quasiIso_iff _).2 (quasiIso_kFlatResMap_general X K)))
  have hψ' : ψ.s ≫ (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map a =
      ψ.f ≫ (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map (kFlatResMapGeneral X K) := hψ
  obtain ⟨W', ρ, hW', hρ⟩ := exists_kFlat_quasiIso_general X ψ.X'.as
  obtain ⟨s₀, hs₀⟩ := (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map_surjective ψ.s
  obtain ⟨f₀, hf₀⟩ := (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map_surjective ψ.f
  have hs₀Q : QuasiIso s₀ := by
    refine (HomotopyCategory.quotient_map_mem_quasiIso_iff s₀).1 ?_
    rw [hs₀]
    exact ψ.hs
  obtain ⟨w, v, hwQ, hsq⟩ : ∃ (w : W' ⟶ A) (v : W' ⟶ kFlatResGeneral X K), QuasiIso w ∧
      (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map (w ≫ a) =
        (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map (v ≫ kFlatResMapGeneral X K) := by
    have hρQ : QuasiIso ρ := hρ
    refine ⟨ρ ≫ s₀, ρ ≫ f₀, inferInstance, ?_⟩
    have h1 : (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map (s₀ ≫ a) =
        (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map (f₀ ≫ kFlatResMapGeneral X K) := by
      rw [Functor.map_comp, Functor.map_comp, hs₀, hf₀]
      exact hψ'
    rw [Category.assoc, Category.assoc, Functor.map_comp _ ρ (s₀ ≫ a),
      Functor.map_comp _ ρ (f₀ ≫ kFlatResMapGeneral X K), h1]
  have htot : DerivedCategory.Q.map
        (((Stacks.SheafOfModules.Tensor.tensorComplex X.O).map (w ≫ a)).app L) =
      DerivedCategory.Q.map
        (((Stacks.SheafOfModules.Tensor.tensorComplex X.O).map
          (v ≫ kFlatResMapGeneral X K)).app L) := by
    refine DerivedCategory.Q_map_eq_of_homotopy _ (HomotopyCategory.homotopyOfEq _ _ ?_)
    have e : ∀ f : W' ⟶ K,
        (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map
            (((Stacks.SheafOfModules.Tensor.tensorComplex X.O).map f).app L) =
          (Stacks.SheafOfModules.Tensor.Reduction.bifunctorPhiR
              (Stacks.SheafOfModules.Tensor.sheafTensor X.O) L).map
            ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map f) := fun _ ↦ rfl
    rw [e, e, hsq]
  have hQ : DerivedCategory.Q.map (w ≫ a) =
      DerivedCategory.Q.map (v ≫ kFlatResMapGeneral X K) :=
    DerivedCategory.Q_map_eq_of_homotopy _ (HomotopyCategory.homotopyOfEq _ _ hsq)
  have hwIso : IsIso (DerivedCategory.Q.map w) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2 hwQ
  have key₂ : ((derivedTensorBifunctorGeneral X).map
        (DerivedCategory.Q.map w)).app (DerivedCategory.Q.obj L) ≫
      (kFlatComparisonGeneral X A hA L).hom ≫
        DerivedCategory.Q.map (((Stacks.SheafOfModules.Tensor.tensorComplex X.O).map a).app L) =
      (kFlatComparisonGeneral X W' hW' L).hom ≫
        DerivedCategory.Q.map
          (((Stacks.SheafOfModules.Tensor.tensorComplex X.O).map (w ≫ a)).app L) := by
    rw [← Category.assoc, kFlatComparison_naturality_left_general X hW' hA w, Category.assoc,
      ← Functor.map_comp, ← NatTrans.comp_app, ← Functor.map_comp]
  have key₁ : ((derivedTensorBifunctorGeneral X).map
        (DerivedCategory.Q.map w)).app (DerivedCategory.Q.obj L) ≫
      ((derivedTensorBifunctorGeneral X).map (DerivedCategory.Q.map a)).app
          (DerivedCategory.Q.obj L) ≫ toTensorGeneral X K L =
      (kFlatComparisonGeneral X W' hW' L).hom ≫
        DerivedCategory.Q.map
          (((Stacks.SheafOfModules.Tensor.tensorComplex X.O).map
            (v ≫ kFlatResMapGeneral X K)).app L) := by
    rw [← Category.assoc, ← NatTrans.comp_app, ← Functor.map_comp, ← Functor.map_comp, hQ,
      Functor.map_comp, Functor.map_comp, NatTrans.comp_app, Category.assoc,
      toTensor_comp_kFlatResMap_general X K L, ← Category.assoc,
      kFlatComparison_naturality_left_general X hW' (isKFlat_kFlatRes_general X K) v,
      Category.assoc, ← Functor.map_comp, ← NatTrans.comp_app, ← Functor.map_comp]
  rw [← cancel_epi (((derivedTensorBifunctorGeneral X).map
    (DerivedCategory.Q.map w)).app (DerivedCategory.Q.obj L)), key₁, key₂, htot]

/-- The comparison isomorphism is natural in the arbitrary variable alone. -/
theorem kFlatComparison_naturality_right_general
    {A L L' : CochainComplex (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (hA : IsKFlat X.O A) (g : L ⟶ L') :
    ((derivedTensorBifunctorGeneral X).obj (DerivedCategory.Q.obj A)).map
          (DerivedCategory.Q.map g) ≫ (kFlatComparisonGeneral X A hA L').hom =
      (kFlatComparisonGeneral X A hA L).hom ≫
        DerivedCategory.Q.map (((Stacks.SheafOfModules.Tensor.tensorComplex X.O).obj A).map g) := by
  simpa using kFlatComparison_naturality_general X hA hA (𝟙 A) g

/-- `toTensorGeneral` is invertible once the total tensor of the resolution augmentation is a
quasi-isomorphism. -/
private theorem isIso_toTensor_of_quasiIso_general
    (K L : CochainComplex (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (h : QuasiIso
      (((Stacks.SheafOfModules.Tensor.tensorComplex X.O).map (kFlatResMapGeneral X K)).app L)) :
    IsIso (toTensorGeneral X K L) := by
  have := (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2 h
  rw [toTensorGeneral]
  infer_instance

/-- The canonical map is an isomorphism when the right factor is K-flat: the only
non-invertible ingredient of its definition is the total tensor of the resolution
augmentation, and Stacks 06YP makes that a quasi-isomorphism. -/
theorem isIso_toTensor_of_kFlat_right_general
    (K L : CochainComplex (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (hL : IsKFlat X.O L) : IsIso (toTensorGeneral X K L) :=
  isIso_toTensor_of_quasiIso_general X K L
    (IsKFlat.quasiIso_tensorComplex_map_app X.O L hL (kFlatResMapGeneral X K)
      (quasiIso_kFlatResMap_general X K))

/-- The canonical map is an isomorphism when the left factor is K-flat: the resolution
augmentation is then a quasi-isomorphism of K-flat complexes, and Stacks 06YT makes its total
tensor with an arbitrary complex a quasi-isomorphism. -/
theorem isIso_toTensor_of_kFlat_left_general
    (K L : CochainComplex (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (hK : IsKFlat X.O K) : IsIso (toTensorGeneral X K L) :=
  isIso_toTensor_of_quasiIso_general X K L
    (quasiIso_tensorComplex_map_app_of_kFlat_general X (kFlatResMapGeneral X K)
      (quasiIso_kFlatResMap_general X K) (isKFlat_kFlatRes_general X K) hK L)

/-- **Naturality of the canonical map** in both complexes, with no K-flatness hypothesis. -/
theorem toTensor_naturality_general
    {K K' L L' : CochainComplex (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (f : K ⟶ K') (g : L ⟶ L') :
    ((derivedTensorBifunctorGeneral X).map (DerivedCategory.Q.map f)).app
          (DerivedCategory.Q.obj L) ≫
        ((derivedTensorBifunctorGeneral X).obj (DerivedCategory.Q.obj K')).map
          (DerivedCategory.Q.map g) ≫
        toTensorGeneral X K' L' =
      toTensorGeneral X K L ≫
        DerivedCategory.Q.map (((Stacks.SheafOfModules.Tensor.tensorComplex X.O).map f).app L ≫
          ((Stacks.SheafOfModules.Tensor.tensorComplex X.O).obj K').map g) := by
  have hP := isKFlat_kFlatRes_general X K
  have hcomplex :
      ((Stacks.SheafOfModules.Tensor.tensorComplex X.O).obj (kFlatResGeneral X K)).map g ≫
        ((Stacks.SheafOfModules.Tensor.tensorComplex X.O).map (kFlatResMapGeneral X K ≫ f)).app L' =
      ((Stacks.SheafOfModules.Tensor.tensorComplex X.O).map (kFlatResMapGeneral X K)).app L ≫
        ((Stacks.SheafOfModules.Tensor.tensorComplex X.O).map f).app L ≫
        ((Stacks.SheafOfModules.Tensor.tensorComplex X.O).obj K').map g := by
    rw [Functor.map_comp, NatTrans.comp_app,
      ← Category.assoc, ((Stacks.SheafOfModules.Tensor.tensorComplex X.O).map (kFlatResMapGeneral X
        K)).naturality g,
      Category.assoc, ((Stacks.SheafOfModules.Tensor.tensorComplex X.O).map f).naturality g]
  rw [← cancel_epi (((derivedTensorBifunctorGeneral X).map
    (DerivedCategory.Q.map (kFlatResMapGeneral X K))).app (DerivedCategory.Q.obj L))]
  rw [← Category.assoc, ← NatTrans.comp_app, ← Functor.map_comp, ← Functor.map_comp,
    ← Category.assoc,
    ← ((derivedTensorBifunctorGeneral X).map
      (DerivedCategory.Q.map (kFlatResMapGeneral X K ≫ f))).naturality (DerivedCategory.Q.map g),
    Category.assoc,
    toTensor_comp_of_kFlat_general X hP (kFlatResMapGeneral X K ≫ f) L',
    ← Category.assoc, kFlatComparison_naturality_right_general X hP g, Category.assoc,
    ← Functor.map_comp, ← Category.assoc,
    toTensor_comp_of_kFlat_general X hP (kFlatResMapGeneral X K) L,
    Category.assoc, ← Functor.map_comp, hcomplex]

end Stacks.SheafOfModules

end

/-! ### The derived tensor product from its exactness -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe c v w d

namespace Stacks.SheafOfModules

variable (X : AlgebraicGeometry.RingedSite.{c, v, w})
  [HasSheafify X.J AddCommGrpCat.{w}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{c, v, w, w, w} X.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{c, v, w, w, w} X.O).obj M).Additive]
  [∀ (K₁ K₂ : CochainComplex
      (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf.{c, v, w} X.O)) ℤ),
    HomologicalComplex.HasMapBifunctorReg K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)]
  [HasDerivedCategory.{d}
    (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf.{c, v, w} X.O))]

attribute [local instance] kFlatQ_isLocalization_general derivedTensorBifunctorLiftingGeneral

/-- The derived tensor product assembled from the given shift coherence and exactness,
with its canonical natural map to the total tensor product and one-sided K-flat comparisons. -/
def derivedTensorProductOfExactGeneral
    (hcs : (derivedTensorBifunctorGeneral X).CommShift₂Int)
    (hel : ∀ M, letI := hcs.commShiftFlipObj M;
      ((derivedTensorBifunctorGeneral X).flip.obj M).IsTriangulated)
    (her : ∀ N, letI := hcs.commShiftObj N;
      ((derivedTensorBifunctorGeneral X).obj N).IsTriangulated) :
    DerivedTensorProduct.{c, v, w, d} X :=
  { tensor := derivedTensorBifunctorGeneral X
    comparison := fun K L _ hL ↦
      @asIso _ _ _ _ _ (isIso_toTensor_of_kFlat_right_general X K L hL)
    comparison_naturality := fun f g _ _ _ _ ↦ by
      refine (toTensor_naturality_general X f g).trans ?_
      congr 2
      exact HomologicalComplex.mapBifunctorMap_eq_map₂_comp
        (Stacks.SheafOfModules.Tensor.sheafTensor X.O) (ComplexShape.up ℤ) f g
    comparisonRight := fun K L hL ↦
      @asIso _ _ _ _ _ (isIso_toTensor_of_kFlat_right_general X K L hL)
    comparisonRight_naturality := fun f g _ _ ↦ by
      refine (toTensor_naturality_general X f g).trans ?_
      congr 2
      exact HomologicalComplex.mapBifunctorMap_eq_map₂_comp
        (Stacks.SheafOfModules.Tensor.sheafTensor X.O) (ComplexShape.up ℤ) f g
    comparisonRight_eq_comparison := fun _ _ _ _ ↦ rfl
    comparisonLeft := fun K L hK ↦
      @asIso _ _ _ _ _ (isIso_toTensor_of_kFlat_left_general X K L hK)
    comparisonLeft_naturality := fun f g _ _ ↦ by
      refine (toTensor_naturality_general X f g).trans ?_
      congr 2
      exact HomologicalComplex.mapBifunctorMap_eq_map₂_comp
        (Stacks.SheafOfModules.Tensor.sheafTensor X.O) (ComplexShape.up ℤ) f g
    comparisonLeft_eq_comparison := fun _ _ _ _ ↦ rfl
    toTensor := toTensorGeneral X
    toTensor_naturality := fun f g ↦ by
      refine (toTensor_naturality_general X f g).trans ?_
      congr 2
      exact HomologicalComplex.mapBifunctorMap_eq_map₂_comp
        (Stacks.SheafOfModules.Tensor.sheafTensor X.O) (ComplexShape.up ℤ) f g
    toTensor_eq_comparisonRight := fun _ _ _ ↦ rfl
    toTensor_eq_comparisonLeft := fun _ _ _ ↦ rfl
    commShift₂ := hcs
    exact_left := hel
    exact_right := her }

/-- **Stacks 06YU, granted exactness.** The derived tensor product of sheaves of modules on a
ringed site exists, with its canonical natural map to the ordinary total tensor product and
its one-sided K-flat comparisons, as soon as the bifunctor is exact in each variable. -/
theorem nonempty_derivedTensorProduct_of_exact_general
    (hcs : (derivedTensorBifunctorGeneral X).CommShift₂Int)
    (hel : ∀ rightModule, letI := hcs.commShiftFlipObj rightModule;
      ((derivedTensorBifunctorGeneral X).flip.obj rightModule).IsTriangulated)
    (her : ∀ leftModule, letI := hcs.commShiftObj leftModule;
      ((derivedTensorBifunctorGeneral X).obj leftModule).IsTriangulated) :
    Nonempty (DerivedTensorProduct.{c, v, w, d} X) :=
  ⟨derivedTensorProductOfExactGeneral X hcs hel her⟩

end Stacks.SheafOfModules

end

/-! ### Exactness in each variable -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe c v w d

namespace Stacks.SheafOfModules

variable (X : AlgebraicGeometry.RingedSite.{c, v, w})
  [HasSheafify X.J AddCommGrpCat.{w}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{c, v, w, w, w} X.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{c, v, w, w, w} X.O).obj M).Additive]
  [∀ (K₁ K₂ : CochainComplex
      (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf.{c, v, w} X.O)) ℤ),
    HomologicalComplex.HasMapBifunctorReg K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)]
  [HasDerivedCategory.{d}
    (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf.{c, v, w} X.O))]

attribute [local instance] kFlatQ_isLocalization_general derivedTensorBifunctorLiftingGeneral

/-- Every object of the derived category is isomorphic to the class of a K-flat complex. -/
theorem exists_kFlat_iso_general
    (N : DerivedCategory (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    ∃ (A : CochainComplex (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
      (_ : IsKFlat X.O A), Nonempty (DerivedCategory.Q.obj A ≅ N) := by
  refine ⟨kFlatResGeneral X (DerivedCategory.Q.objPreimage N), isKFlat_kFlatRes_general X _, ⟨?_⟩⟩
  have : IsIso (DerivedCategory.Q.map (kFlatResMapGeneral X (DerivedCategory.Q.objPreimage N))) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2 inferInstance
  exact asIso (DerivedCategory.Q.map (kFlatResMapGeneral X (DerivedCategory.Q.objPreimage N))) ≪≫
    DerivedCategory.Q.objObjPreimageIso N

/-- For a K-flat complex `A`, the functor `A ⊗^L_O -` on the derived category descends
`Tot(A ⊗_O -)` on the homotopy category along `DerivedCategory.Qh`. -/
@[instance_reducible]
def derivedTensorObjLiftingGeneral
    (A : CochainComplex (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (hA : IsKFlat X.O A) :
    Localization.Lifting DerivedCategory.Qh
      (HomotopyCategory.quasiIso
        (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (ComplexShape.up ℤ))
      (Stacks.SheafOfModules.Tensor.Reduction.bifunctorPhi (Stacks.SheafOfModules.Tensor.sheafTensor
        X.O) A ⋙
        DerivedCategory.Qh)
      ((derivedTensorBifunctorGeneral X).obj (DerivedCategory.Q.obj A)) := by
  letI := Localization.Lifting₂.fst (kFlatComplexQGeneral X) DerivedCategory.Q
    (kFlatComplexQuasiIsoGeneral X)
    (HomologicalComplex.quasiIso
      (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (ComplexShape.up ℤ))
    (kFlatTensorToDerivedGeneral X) (derivedTensorBifunctorGeneral X) (kFlatObjGeneral X A hA)
  letI : Localization.Lifting (HomotopyCategory.quotient _ (ComplexShape.up ℤ))
      (HomologicalComplex.homotopyEquivalences _ (ComplexShape.up ℤ))
      ((Stacks.SheafOfModules.Tensor.tensorComplex X.O).obj A ⋙ DerivedCategory.Q)
      (DerivedCategory.Qh ⋙ (derivedTensorBifunctorGeneral X).obj (DerivedCategory.Q.obj A)) :=
    ⟨(Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (DerivedCategory.quotientCompQhIso _)
        ((derivedTensorBifunctorGeneral X).obj (DerivedCategory.Q.obj A)) ≪≫
      Localization.Lifting.iso DerivedCategory.Q
        (HomologicalComplex.quasiIso _ (ComplexShape.up ℤ))
        ((kFlatTensorToDerivedGeneral X).obj (kFlatObjGeneral X A hA))
        ((derivedTensorBifunctorGeneral X).obj
          ((kFlatComplexQGeneral X).obj (kFlatObjGeneral X A hA)))⟩
  letI : Localization.Lifting (HomotopyCategory.quotient _ (ComplexShape.up ℤ))
      (HomologicalComplex.homotopyEquivalences _ (ComplexShape.up ℤ))
      ((Stacks.SheafOfModules.Tensor.tensorComplex X.O).obj A ⋙ DerivedCategory.Q)
      (Stacks.SheafOfModules.Tensor.Reduction.bifunctorPhi (Stacks.SheafOfModules.Tensor.sheafTensor
        X.O) A ⋙
        DerivedCategory.Qh) :=
    ⟨(Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight
        (Stacks.SheafOfModules.Tensor.Reduction.bifunctorPhiFactors
          (Stacks.SheafOfModules.Tensor.sheafTensor X.O) A)
        DerivedCategory.Qh ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft ((Stacks.SheafOfModules.Tensor.tensorComplex X.O).obj A)
        (DerivedCategory.quotientCompQhIso _)⟩
  exact ⟨Localization.liftNatIso (HomotopyCategory.quotient _ (ComplexShape.up ℤ))
    (HomologicalComplex.homotopyEquivalences _ (ComplexShape.up ℤ))
    ((Stacks.SheafOfModules.Tensor.tensorComplex X.O).obj A ⋙ DerivedCategory.Q)
    ((Stacks.SheafOfModules.Tensor.tensorComplex X.O).obj A ⋙ DerivedCategory.Q) _ _ (Iso.refl _)
      |>.symm⟩

/-- **Exactness in the second variable, for a K-flat first factor.** The functor is the
descent of the exact functor `Tot(A ⊗_O -)` of Stacks 06YM, so Stacks 05R7 applies. -/
theorem exists_commShift_isTriangulated_obj_kFlat_general
    (A : CochainComplex (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (hA : IsKFlat X.O A) :
    ∃ s : ((derivedTensorBifunctorGeneral X).obj (DerivedCategory.Q.obj A)).CommShift ℤ,
      letI := s
      ((derivedTensorBifunctorGeneral X).obj (DerivedCategory.Q.obj A)).IsTriangulated := by
  let _ := Stacks.SheafOfModules.Tensor.Reduction.bifunctorXi
    (Stacks.SheafOfModules.Tensor.sheafTensor X.O) A
  have _ := Stacks.SheafOfModules.Tensor.Reduction.bifunctorPhi_isTriangulated
    (Stacks.SheafOfModules.Tensor.sheafTensor X.O) A
  let _ := derivedTensorObjLiftingGeneral X A hA
  let _ := Functor.commShiftOfLocalization DerivedCategory.Qh
    (HomotopyCategory.quasiIso
      (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (ComplexShape.up ℤ)) ℤ
    (Stacks.SheafOfModules.Tensor.Reduction.bifunctorPhi (Stacks.SheafOfModules.Tensor.sheafTensor
      X.O) A ⋙
      DerivedCategory.Qh)
    ((derivedTensorBifunctorGeneral X).obj (DerivedCategory.Q.obj A))
  exact ⟨inferInstance, Functor.isTriangulated_of_localization DerivedCategory.Qh
    (HomotopyCategory.quasiIso
      (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (ComplexShape.up ℤ)) _ _⟩

/-- Transfer exactness along an isomorphism `A ≅ N` in the first slot of a bifunctor. -/
private theorem exists_commShift_isTriangulated_of_iso_general
    {D : Type*} [Category D] [Preadditive D] [HasZeroObject D] [HasShift D ℤ]
    [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D] (F : D ⥤ D ⥤ D) {A N : D}
    (e : A ≅ N) (h : ∃ s : (F.obj A).CommShift ℤ, letI := s; (F.obj A).IsTriangulated) :
    ∃ s : (F.obj N).CommShift ℤ, letI := s; (F.obj N).IsTriangulated := by
  obtain ⟨s, hs⟩ := h
  let _ := s
  have _ := hs
  let e' := F.mapIso e
  let _ := Functor.CommShift.ofIso e' ℤ
  have _ := Functor.CommShift.ofIso_compatibility e' ℤ
  exact ⟨inferInstance, Functor.isTriangulated_of_iso e'⟩

/-- **Exactness of the derived tensor product in its second variable**: fixing the first
argument gives an exact functor of triangulated categories. -/
theorem exists_commShift_isTriangulated_obj_general
    (N : DerivedCategory (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    ∃ s : ((derivedTensorBifunctorGeneral X).obj N).CommShift ℤ,
      letI := s; ((derivedTensorBifunctorGeneral X).obj N).IsTriangulated := by
  obtain ⟨A, hA, ⟨e⟩⟩ := exists_kFlat_iso_general X N
  exact exists_commShift_isTriangulated_of_iso_general _ e
    (exists_commShift_isTriangulated_obj_kFlat_general X A hA)

omit [HasDerivedCategory.{d}
  (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf.{c, v, w} X.O))] in
/-- The quasi-isomorphisms between K-flat objects of the homotopy category admit a left
calculus of fractions, being the class generated by the acyclic K-flat objects. -/
theorem kFlatQuasiIso_hasLeftCalculusOfFractions_general :
    (kFlatQuasiIso.{c, v, w} X.O).HasLeftCalculusOfFractions := by
  have h : kFlatQuasiIso.{c, v, w} X.O =
      ((HomotopyCategory.subcategoryAcyclic
        (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))).inverseImage
          (kFlatObjects.{c, v, w} X.O).ι).trW := by
    ext Y Z f
    change HomotopyCategory.quasiIso _ (ComplexShape.up ℤ)
      ((kFlatObjects X.O).ι.map f) ↔ _
    rw [HomotopyCategory.quasiIso_eq_trW_subcategoryAcyclic]
    exact ((HomotopyCategory.subcategoryAcyclic
      (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))).inverseImage_trW_iff
        (kFlatObjects X.O).ι f).symm
  rw [h]
  infer_instance

attribute [local instance] kFlatQuasiIso_hasLeftCalculusOfFractions_general

/-- The localization of the K-flat objects onto the derived category is essentially surjective
on arrows. -/
theorem kFlatQ_mapArrow_essSurj_general : (kFlatQGeneral.{c, v, w, d} X).mapArrow.EssSurj :=
  Localization.essSurj_mapArrow (kFlatQGeneral X) (kFlatQuasiIso X.O)

attribute [local instance] kFlatQ_mapArrow_essSurj_general

/-- For any complex `B`, the functor `- ⊗^L_O B` on the derived category descends
`Tot(- ⊗_O B)` on the K-flat objects of the homotopy category along
`Stacks.SheafOfModules.kFlatQGeneral`. -/
@[instance_reducible]
def derivedTensorFlipObjLiftingGeneral
    (B : CochainComplex (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) :
    Localization.Lifting (kFlatQGeneral.{c, v, w, d} X) (kFlatQuasiIso.{c, v, w} X.O)
      ((kFlatObjects.{c, v, w} X.O).ι ⋙
        Stacks.SheafOfModules.Tensor.Reduction.bifunctorPhiR
          (Stacks.SheafOfModules.Tensor.sheafTensor X.O) B ⋙
          DerivedCategory.Qh)
      ((derivedTensorBifunctorGeneral X).flip.obj (DerivedCategory.Q.obj B)) := by
  letI := Localization.Lifting₂.snd (kFlatComplexQGeneral X) DerivedCategory.Q
    (kFlatComplexQuasiIsoGeneral X)
    (HomologicalComplex.quasiIso
      (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (ComplexShape.up ℤ))
    (kFlatTensorToDerivedGeneral X) (derivedTensorBifunctorGeneral X) B
  letI : Localization.Lifting
      (ObjectProperty.complexSubcategoryQuotient (kFlatObjects.{c, v, w} X.O))
      ((HomologicalComplex.homotopyEquivalences
        (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (ComplexShape.up
          ℤ)).inverseImage
          (kFlatComplexesGeneral X).ι)
      ((kFlatTensorToDerivedGeneral X).flip.obj B)
      (kFlatQGeneral.{c, v, w, d} X ⋙
        (derivedTensorBifunctorGeneral X).flip.obj (DerivedCategory.Q.obj B)) :=
    ⟨(Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight
        (ObjectProperty.complexSubcategoryQuotientCompIso (kFlatObjects.{c, v, w} X.O))
        ((derivedTensorBifunctorGeneral X).flip.obj (DerivedCategory.Q.obj B)) ≪≫
      Localization.Lifting.iso (kFlatComplexQGeneral X) (kFlatComplexQuasiIsoGeneral X)
        ((kFlatTensorToDerivedGeneral X).flip.obj B)
        ((derivedTensorBifunctorGeneral X).flip.obj (DerivedCategory.Q.obj B))⟩
  letI : Localization.Lifting
      (ObjectProperty.complexSubcategoryQuotient (kFlatObjects.{c, v, w} X.O))
      ((HomologicalComplex.homotopyEquivalences
        (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (ComplexShape.up
          ℤ)).inverseImage
          (kFlatComplexesGeneral X).ι)
      ((kFlatTensorToDerivedGeneral X).flip.obj B)
      ((kFlatObjects.{c, v, w} X.O).ι ⋙
        Stacks.SheafOfModules.Tensor.Reduction.bifunctorPhiR
          (Stacks.SheafOfModules.Tensor.sheafTensor X.O) B ⋙
          DerivedCategory.Qh) :=
    ⟨(Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight
        (ObjectProperty.liftCompιIso (kFlatObjects.{c, v, w} X.O) _ _)
        (Stacks.SheafOfModules.Tensor.Reduction.bifunctorPhiR
          (Stacks.SheafOfModules.Tensor.sheafTensor X.O) B ⋙
          DerivedCategory.Qh) ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft (kFlatComplexesGeneral X).ι
        ((Functor.associator _ _ _).symm ≪≫
          Functor.isoWhiskerRight
            (Stacks.SheafOfModules.Tensor.Reduction.bifunctorPhiRFactors
              (Stacks.SheafOfModules.Tensor.sheafTensor X.O) B) DerivedCategory.Qh ≪≫
          Functor.associator _ _ _ ≪≫
          Functor.isoWhiskerLeft ((Stacks.SheafOfModules.Tensor.tensorComplex X.O).flip.obj B)
            (DerivedCategory.quotientCompQhIso _))⟩
  exact ⟨Localization.liftNatIso
    (ObjectProperty.complexSubcategoryQuotient (kFlatObjects.{c, v, w} X.O))
    ((HomologicalComplex.homotopyEquivalences
      (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (ComplexShape.up
        ℤ)).inverseImage
        (kFlatComplexesGeneral X).ι)
    ((kFlatTensorToDerivedGeneral X).flip.obj B) ((kFlatTensorToDerivedGeneral X).flip.obj B)
    _ _ (Iso.refl _) |>.symm⟩

/-- **Exactness in the first variable, for any second factor.** -/
theorem exists_commShift_isTriangulated_flip_obj_complex_general
    (B : CochainComplex (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) :
    ∃ s : ((derivedTensorBifunctorGeneral X).flip.obj (DerivedCategory.Q.obj B)).CommShift ℤ,
      letI := s
      ((derivedTensorBifunctorGeneral X).flip.obj (DerivedCategory.Q.obj B)).IsTriangulated := by
  let _ := Stacks.SheafOfModules.Tensor.Reduction.bifunctorXiR
    (Stacks.SheafOfModules.Tensor.sheafTensor X.O) B
  have _ := Stacks.SheafOfModules.Tensor.Reduction.bifunctorPhiR_isTriangulated
    (Stacks.SheafOfModules.Tensor.sheafTensor X.O) B
  let _ := derivedTensorFlipObjLiftingGeneral X B
  let _ := Functor.commShiftOfLocalization (kFlatQGeneral.{c, v, w, d} X) (kFlatQuasiIso X.O) ℤ
    ((kFlatObjects.{c, v, w} X.O).ι ⋙
      Stacks.SheafOfModules.Tensor.Reduction.bifunctorPhiR (Stacks.SheafOfModules.Tensor.sheafTensor
        X.O) B ⋙
        DerivedCategory.Qh)
    ((derivedTensorBifunctorGeneral X).flip.obj (DerivedCategory.Q.obj B))
  exact ⟨inferInstance, Functor.isTriangulated_of_localization (kFlatQGeneral.{c, v, w, d} X)
    (kFlatQuasiIso X.O) _ _⟩

/-- **Exactness of the derived tensor product in its first variable**: fixing the second
argument gives an exact functor of triangulated categories. -/
theorem exists_commShift_isTriangulated_flip_obj_general
    (M : DerivedCategory (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    ∃ s : ((derivedTensorBifunctorGeneral X).flip.obj M).CommShift ℤ,
      letI := s; ((derivedTensorBifunctorGeneral X).flip.obj M).IsTriangulated := by
  obtain ⟨B, _, ⟨e⟩⟩ := exists_kFlat_iso_general X M
  exact exists_commShift_isTriangulated_of_iso_general _ e
    (exists_commShift_isTriangulated_flip_obj_complex_general X B)

end Stacks.SheafOfModules

end
