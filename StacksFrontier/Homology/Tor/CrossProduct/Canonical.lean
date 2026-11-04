module

public import StacksFrontier.Homology.Tor.CrossProduct.ChainComparison
public import StacksFrontier.Homology.Tor.CrossProduct.DerivedProductAgreement

/-!
# Tor cross products: the canonical system

The base change of total tensor complexes, the assembly of the cross product from projective
resolutions, its degree-zero normalization and uniqueness, the canonical system
`TorCrossProduct.canonical`, and the Tor product `RingTheory.TorProducts.torProduct` for an
`R`-algebra `A`.
-/

open CategoryTheory CategoryTheory.Limits MonoidalCategory CochainComplex.DerivedTensor
open scoped TensorProduct

universe uR uA v w x

noncomputable section

open HomologicalComplex

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace TorCrossProduct

/-- Maps out of a tensor product of scalar extensions agree if they agree on pure tensors. -/
private lemma hom_ext_extensionScalars_tensor
    {R : Type uR} {A : Type uA} [CommRing R] [CommRing A] (f : R →+* A)
    {M N : ModuleCat.{max uR uA v} R} {X : ModuleCat.{max uR uA v} A}
    (g h : ((ModuleCat.moduleTensorLarge.{uA, max uR v} A).obj
      ((extensionScalars f).obj M)).obj ((extensionScalars f).obj N) ⟶ X)
    (H : letI := f.toAlgebra
      ∀ (a b : A) (x : M) (y : N),
        g.hom ((a ⊗ₜ[R] x) ⊗ₜ[A] (b ⊗ₜ[R] y)) = h.hom ((a ⊗ₜ[R] x) ⊗ₜ[A] (b ⊗ₜ[R] y))) :
    g = h := by
  let := f.toAlgebra
  apply ModuleCat.hom_ext
  apply TensorProduct.AlgebraTensorModule.ext
  intro x y
  induction x using TensorProduct.induction_on with
  | zero => simp only [TensorProduct.zero_tmul, map_zero]
  | add x x' hx hx' => simp only [TensorProduct.add_tmul, map_add, hx, hx']
  | tmul a x =>
    induction y using TensorProduct.induction_on with
    | zero => simp only [TensorProduct.tmul_zero, map_zero]
    | add y y' hy hy' => simp only [TensorProduct.tmul_add, map_add, hy, hy']
    | tmul b y => exact H a b x y

private lemma zeroBaseChange_naturality
    {R : Type uR} {A : Type uA} [CommRing R] [CommRing A]
    (f : R →+* A) {M M' N N' : ModuleCat.{max uR uA v} R}
    (g : M ⟶ M') (h : N ⟶ N') :
    moduleTensorMap.{uR, uA, v} ((extensionScalars f).map g)
        ((extensionScalars f).map h) ≫ zeroBaseChange R A f M' N' =
      zeroBaseChange R A f M N ≫
        (extensionScalars f).map (moduleTensorMap.{uA, uR, v} g h) := by
  let := f.toAlgebra
  apply hom_ext_extensionScalars_tensor
  intro a b x y
  dsimp only [extensionScalars, ModuleCat.extendScalars, ModuleCat.ExtendScalars.obj',
    ModuleCat.ExtendScalars.map', zeroBaseChange, moduleTensorMap,
    ModuleCat.moduleTensorLarge]
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_ofHom]
  show (TensorProduct.AlgebraTensorModule.distribBaseChange R A M' N').symm
      ((a ⊗ₜ[R] g x) ⊗ₜ[A] (b ⊗ₜ[R] h y)) =
    (LinearMap.baseChange A ((h.hom.lTensor M').comp (g.hom.rTensor N)))
      ((TensorProduct.AlgebraTensorModule.distribBaseChange R A M N).symm
        ((a ⊗ₜ[R] x) ⊗ₜ[A] (b ⊗ₜ[R] y)))
  simp only [TensorProduct.AlgebraTensorModule.distribBaseChange_symm_tmul,
    LinearMap.baseChange_tmul, LinearMap.comp_apply,
    LinearMap.lTensor_tmul, LinearMap.rTensor_tmul]

private lemma moduleTensorMap_hom
    {S : Type uA} [CommRing S]
    {M M' N N' : ModuleCat.{max uR uA v} S} (f : M ⟶ M') (g : N ⟶ N') :
    (moduleTensorMap.{uR, uA, v} f g).hom = TensorProduct.map f.hom g.hom := by
  apply TensorProduct.ext
  ext x y
  rfl

private lemma epi_moduleTensorMap
    {S : Type uA} [CommRing S]
    {M M' N N' : ModuleCat.{max uR uA v} S}
    (f : M ⟶ M') (g : N ⟶ N') [Epi f] [Epi g] :
    Epi (moduleTensorMap.{uR, uA, v} f g) := by
  apply (ModuleCat.epi_iff_surjective _).2
  show Function.Surjective (moduleTensorMap.{uR, uA, v} f g).hom
  rw [moduleTensorMap_hom.{uR, uA, v}]
  exact TensorProduct.map_surjective ((ModuleCat.epi_iff_surjective f).1 inferInstance)
    ((ModuleCat.epi_iff_surjective g).1 inferInstance)

private lemma chainHomologyProduct_map_eq
    {A : Type uA} [CommRing A]
    {K L : ChainComplex (ModuleCat.{max uR uA v} A) ℕ} {n m : ℕ}
    (c d : ChainHomologyProduct.{uR, uA, v} A K L n m) : c.map = d.map := by
  obtain ⟨z, hz, hc⟩ := c.maps_cycles
  obtain ⟨w, hw, hd⟩ := d.maps_cycles
  have hzw : z = w := (cancel_mono _).1 (hz.trans hw.symm)
  have := epi_moduleTensorMap.{uR, uA, v} (K.homologyπ n) (L.homologyπ m)
  rw [← cancel_epi (moduleTensorMap.{uR, uA, v} (K.homologyπ n) (L.homologyπ m)),
    hc, hd, hzw]

section Uniqueness

variable {R : Type uR} {A : Type uA} [CommRing R] [CommRing A]
  {f : R →+* A} {n m : ℕ}
  {p q :
    (torBaseChange.{uR, uA, v} R A f n).prod (torBaseChange.{uR, uA, v} R A f m) ⋙
      Functor.uncurry.obj (ModuleCat.moduleTensorLarge.{uA, max uR v} A) ⟶
      Functor.uncurry.obj (ModuleCat.moduleTensorLarge.{uR, max uA v} R) ⋙
        torBaseChange.{uR, uA, v} R A f (n + m)}

private lemma resolutionModel_app_eq
    {M N : ModuleCat.{max uR uA v} R}
    {P : ProjectiveResolution M} {Q : ProjectiveResolution N}
    {T : ProjectiveResolution (((ModuleCat.moduleTensorLarge.{uR, max uA v} R).obj M).obj N)}
    (x : ResolutionModel R A f n m p M N P Q T)
    (y : ResolutionModel R A f n m q M N P Q T) : p.app (M, N) = q.app (M, N) := by
  have hbc : x.baseChange = y.baseChange := by
    ext k : 1
    apply mapBifunctor.hom_ext
    intro i j h
    rw [x.baseChange_ι, y.baseChange_ι]
  have hc : x.cohomologyProduct.map = y.cohomologyProduct.map :=
    chainHomologyProduct_map_eq.{uR, uA, v} _ _
  obtain ⟨hμ⟩ := x.μ_unique y.μ y.μ_zero
  have hH := (((extensionScalars f).mapHomotopy hμ).compLeft
    x.baseChange).homologyMap_eq (n + m)
  rw [← CategoryTheory.cancel_mono (C := ModuleCat.{max uR uA v} A)
      (T.isoLeftDerivedObj (extensionScalars.{uR, uA, v} f) (n + m)).hom,
    x.product_eq, y.product_eq, hc, hH, hbc]

private lemma product_eq_of_resolution
    (hp : ∀ (M N : ModuleCat.{max uR uA v} R)
      (P : ProjectiveResolution M) (Q : ProjectiveResolution N)
      (T : ProjectiveResolution (((ModuleCat.moduleTensorLarge.{uR, max uA v} R).obj M).obj N)),
      Nonempty (ResolutionModel R A f n m p M N P Q T))
    (hq : ∀ (M N : ModuleCat.{max uR uA v} R)
      (P : ProjectiveResolution M) (Q : ProjectiveResolution N)
      (T : ProjectiveResolution (((ModuleCat.moduleTensorLarge.{uR, max uA v} R).obj M).obj N)),
      Nonempty (ResolutionModel R A f n m q M N P Q T)) : p = q := by
  apply NatTrans.ext
  funext ⟨M, N⟩
  obtain ⟨x⟩ := hp M N (projectiveResolution M) (projectiveResolution N) (projectiveResolution _)
  obtain ⟨y⟩ := hq M N (projectiveResolution M) (projectiveResolution N) (projectiveResolution _)
  exact resolutionModel_app_eq x y

end Uniqueness

section BaseChange

variable {R : Type uR} {A : Type uA} [CommRing R] [CommRing A] (f : R →+* A)

/-- The termwise extension of scalars along `f` of a chain complex of `R`-modules. -/
public abbrev extC (K : ChainComplex (ModuleCat.{max uR uA v} R) ℕ) :=
  ((extensionScalars.{uR, uA, v} f).mapHomologicalComplex (ComplexShape.down ℕ)).obj K

private abbrev extC_map {K L : ChainComplex (ModuleCat.{max uR uA v} R) ℕ} (φ : K ⟶ L) :
    extC.{uR, uA, v} f K ⟶ extC.{uR, uA, v} f L :=
  ((extensionScalars.{uR, uA, v} f).mapHomologicalComplex (ComplexShape.down ℕ)).map φ

@[reassoc]
private lemma zeroBaseChange_naturality_left {M M' : ModuleCat.{max uR uA v} R}
    (g : M ⟶ M') (N : ModuleCat.{max uR uA v} R) :
    ((ModuleCat.moduleTensorLarge.{uA, max uR v} A).map ((extensionScalars f).map g)).app
        ((extensionScalars f).obj N) ≫ zeroBaseChange R A f M' N =
      zeroBaseChange R A f M N ≫
        (extensionScalars f).map
          (((ModuleCat.moduleTensorLarge.{uR, max uA v} R).map g).app N) := by
  let := f.toAlgebra
  apply hom_ext_extensionScalars_tensor
  intros
  rfl

@[reassoc]
private lemma zeroBaseChange_naturality_right (M : ModuleCat.{max uR uA v} R)
    {N N' : ModuleCat.{max uR uA v} R} (g : N ⟶ N') :
    ((ModuleCat.moduleTensorLarge.{uA, max uR v} A).obj ((extensionScalars f).obj M)).map
        ((extensionScalars f).map g) ≫ zeroBaseChange R A f M N' =
      zeroBaseChange R A f M N ≫
        (extensionScalars f).map
          (((ModuleCat.moduleTensorLarge.{uR, max uA v} R).obj M).map g) := by
  let := f.toAlgebra
  apply hom_ext_extensionScalars_tensor
  intros
  rfl

private def chainBaseChange (K L : ChainComplex (ModuleCat.{max uR uA v} R) ℕ) :
    chainTensor.{uR, uA, v} (extC.{uR, uA, v} f K) (extC.{uR, uA, v} f L) ⟶
      extC.{uR, uA, v} f (chainTensor.{uA, uR, v} K L) where
  f k := mapBifunctorDesc fun p q h ↦ zeroBaseChange R A f (K.X p) (L.X q) ≫
    (extensionScalars f).map (ιMapBifunctor K L
      (ModuleCat.moduleTensorLarge.{uR, max uA v} R) (ComplexShape.down ℕ) p q k h)
  comm' k k' hk := by
    apply mapBifunctor.hom_ext
    intro p q h
    simp only [ι_mapBifunctorDesc_assoc, Category.assoc, Functor.mapHomologicalComplex_obj_d,
      ← Functor.map_comp]
    rw [mapBifunctor.d_eq, mapBifunctor.d_eq, Preadditive.comp_add, Preadditive.add_comp,
      Preadditive.comp_add, mapBifunctor.ι_D₁, mapBifunctor.ι_D₂, mapBifunctor.ι_D₁_assoc,
      mapBifunctor.ι_D₂_assoc, Functor.map_add, Preadditive.comp_add]
    congr 1
    · by_cases hp : (ComplexShape.down ℕ).Rel p ((ComplexShape.down ℕ).next p)
      · rw [mapBifunctor.d₁_eq' _ _ _ _ hp, mapBifunctor.d₁_eq' _ _ _ _ hp]
        by_cases hk' : ComplexShape.π (ComplexShape.down ℕ) (ComplexShape.down ℕ)
            (ComplexShape.down ℕ) ⟨(ComplexShape.down ℕ).next p, q⟩ = k'
        · simp only [ιMapBifunctorOrZero_eq _ _ _ _ _ _ _ hk', Linear.units_smul_comp,
            Functor.map_units_smul, Linear.comp_units_smul, Category.assoc,
            ι_mapBifunctorDesc, Functor.mapHomologicalComplex_obj_d, Functor.map_comp]
          rw [← zeroBaseChange_naturality_left_assoc]
          rfl
        · simp [ιMapBifunctorOrZero_eq_zero _ _ _ _ _ _ _ hk']
      · simp [mapBifunctor.d₁_eq_zero _ _ _ _ _ _ _ hp]
    · by_cases hq : (ComplexShape.down ℕ).Rel q ((ComplexShape.down ℕ).next q)
      · rw [mapBifunctor.d₂_eq' _ _ _ _ _ hq, mapBifunctor.d₂_eq' _ _ _ _ _ hq]
        by_cases hk' : ComplexShape.π (ComplexShape.down ℕ) (ComplexShape.down ℕ)
            (ComplexShape.down ℕ) ⟨p, (ComplexShape.down ℕ).next q⟩ = k'
        · simp only [ιMapBifunctorOrZero_eq _ _ _ _ _ _ _ hk', Linear.units_smul_comp,
            Functor.map_units_smul, Linear.comp_units_smul, Category.assoc,
            ι_mapBifunctorDesc, Functor.mapHomologicalComplex_obj_d, Functor.map_comp]
          rw [← zeroBaseChange_naturality_right_assoc]
          rfl
        · simp [ιMapBifunctorOrZero_eq_zero _ _ _ _ _ _ _ hk']
      · simp [mapBifunctor.d₂_eq_zero _ _ _ _ _ _ _ hq]

private lemma chainBaseChange_ι (K L : ChainComplex (ModuleCat.{max uR uA v} R) ℕ)
    (p q k : ℕ) (h : p + q = k) :
    letI := f.toAlgebra
    HomologicalComplex.ιMapBifunctor _ _ (ModuleCat.moduleTensorLarge.{uA, max uR v} A)
        (ComplexShape.down ℕ) p q k h ≫ (chainBaseChange.{uR, uA, v} f K L).f k =
      (TensorProduct.AlgebraTensorModule.distribBaseChange
        R A (K.X p) (L.X q)).symm.toModuleIso.hom ≫
        (extensionScalars f).map
          (HomologicalComplex.ιMapBifunctor K L (ModuleCat.moduleTensorLarge.{uR, max uA v} R)
            (ComplexShape.down ℕ) p q k h) := by
  dsimp only [chainBaseChange]
  rw [ι_mapBifunctorDesc]
  rfl

@[reassoc]
private lemma chainBaseChange_naturality
    {K K' L L' : ChainComplex (ModuleCat.{max uR uA v} R) ℕ} (φ : K ⟶ K') (ψ : L ⟶ L') :
    mapBifunctorMap
        (((extensionScalars.{uR, uA, v} f).mapHomologicalComplex _).map φ)
        (((extensionScalars.{uR, uA, v} f).mapHomologicalComplex _).map ψ)
        (ModuleCat.moduleTensorLarge.{uA, max uR v} A) (ComplexShape.down ℕ) ≫
        chainBaseChange.{uR, uA, v} f K' L' =
      chainBaseChange.{uR, uA, v} f K L ≫
        ((extensionScalars.{uR, uA, v} f).mapHomologicalComplex _).map
          (mapBifunctorMap φ ψ (ModuleCat.moduleTensorLarge.{uR, max uA v} R)
            (ComplexShape.down ℕ)) := by
  ext k : 1
  apply mapBifunctor.hom_ext
  intro p q h
  simp only [HomologicalComplex.comp_f, ι_mapBifunctorMap_assoc, chainBaseChange,
    ι_mapBifunctorDesc, ι_mapBifunctorDesc_assoc, Category.assoc,
    Functor.mapHomologicalComplex_map_f, ← Functor.map_comp, ι_mapBifunctorMap]
  erw [zeroBaseChange_naturality_right_assoc.{uR, uA, v} f (K'.X p) (ψ.f q),
    reassoc_of% (zeroBaseChange_naturality_left.{uR, uA, v} f (φ.f p) (L.X q))]
  simp only [← Functor.map_comp]

end BaseChange

section Assembly

variable {R : Type uR} {A : Type uA} [CommRing R] [CommRing A] (f : R →+* A)

/-- The map on homology induced by a comparison `μ : Tot(P ⊗ Q) ⟶ T`, after extension of
scalars, preceded by the cycle product. -/
private noncomputable def resolutionProduct (n m : ℕ)
    {K L T : ChainComplex (ModuleCat.{max uR uA v} R) ℕ}
    (μ : chainTensor.{uA, uR, v} K L ⟶ T) :
    ((ModuleCat.moduleTensorLarge.{uA, max uR v} A).obj ((extC.{uR, uA, v} f K).homology n)).obj
        ((extC.{uR, uA, v} f L).homology m) ⟶ (extC.{uR, uA, v} f T).homology (n + m) :=
  (chainHomologyProductOfCycles.{uR, uA, v} (extC.{uR, uA, v} f K)
    (extC.{uR, uA, v} f L) n m).map ≫
    homologyMap (chainBaseChange.{uR, uA, v} f K L ≫
      ((extensionScalars.{uR, uA, v} f).mapHomologicalComplex _).map μ) (n + m)

private lemma resolutionProduct_naturality (n m : ℕ)
    {K K' L L' T T' : ChainComplex (ModuleCat.{max uR uA v} R) ℕ}
    (φ : K ⟶ K') (ψ : L ⟶ L') (χ : T ⟶ T')
    (μ : chainTensor.{uA, uR, v} K L ⟶ T) (μ' : chainTensor.{uA, uR, v} K' L' ⟶ T')
    (hχ : Homotopy (μ ≫ χ)
      (mapBifunctorMap φ ψ (ModuleCat.moduleTensorLarge.{uR, max uA v} R)
        (ComplexShape.down ℕ) ≫ μ')) :
    moduleTensorMap.{uR, uA, v} (homologyMap (extC_map f φ) n)
        (homologyMap (extC_map f ψ) m) ≫ resolutionProduct.{uR, uA, v} f n m μ' =
      resolutionProduct.{uR, uA, v} f n m μ ≫ homologyMap (extC_map f χ) (n + m) := by
  have hH := (((extensionScalars.{uR, uA, v} f).mapHomotopy hχ).compLeft
    (chainBaseChange.{uR, uA, v} f K L)).homologyMap_eq (n + m)
  have h1 := chainHomologyProductOfCycles_naturality.{uR, uA, v}
    (extC_map f φ) (extC_map f ψ) n m
  have h2 := chainBaseChange_naturality.{uR, uA, v} f φ ψ
  dsimp only [resolutionProduct]
  rw [reassoc_of% h1, ← homologyMap_comp, Category.assoc, ← homologyMap_comp,
    ← Category.assoc, h2, Category.assoc, ← Functor.map_comp, Category.assoc,
    ← Functor.map_comp, ← hH]

/-- A component of the cross product computed from arbitrary projective resolutions and a
comparison of total complexes. -/
private noncomputable def resolutionComponent (n m : ℕ)
    {M N : ModuleCat.{max uR uA v} R}
    (P : ProjectiveResolution M) (Q : ProjectiveResolution N)
    (T : ProjectiveResolution (((ModuleCat.moduleTensorLarge.{uR, max uA v} R).obj M).obj N))
    (μ : chainTensor.{uA, uR, v} P.complex Q.complex ⟶ T.complex) :
    ((ModuleCat.moduleTensorLarge.{uA, max uR v} A).obj
        ((torBaseChange.{uR, uA, v} R A f n).obj M)).obj
        ((torBaseChange.{uR, uA, v} R A f m).obj N) ⟶
      (torBaseChange.{uR, uA, v} R A f (n + m)).obj
        (((ModuleCat.moduleTensorLarge.{uR, max uA v} R).obj M).obj N) :=
  moduleTensorMap.{uR, uA, v} (P.isoLeftDerivedObj (extensionScalars f) n).hom
      (Q.isoLeftDerivedObj (extensionScalars f) m).hom ≫
    resolutionProduct.{uR, uA, v} f n m μ ≫
      (T.isoLeftDerivedObj (extensionScalars f) (n + m)).inv

private lemma resolutionComponent_naturality (n m : ℕ)
    {M M' N N' : ModuleCat.{max uR uA v} R} (g : M ⟶ M') (h : N ⟶ N')
    {P : ProjectiveResolution M} {P' : ProjectiveResolution M'}
    {Q : ProjectiveResolution N} {Q' : ProjectiveResolution N'}
    {T : ProjectiveResolution (((ModuleCat.moduleTensorLarge.{uR, max uA v} R).obj M).obj N)}
    {T' : ProjectiveResolution (((ModuleCat.moduleTensorLarge.{uR, max uA v} R).obj M').obj N')}
    (μ : chainTensor.{uA, uR, v} P.complex Q.complex ⟶ T.complex)
    (hμ : ιMapBifunctor P.complex Q.complex (ModuleCat.moduleTensorLarge.{uR, max uA v} R)
        (ComplexShape.down ℕ) 0 0 0 rfl ≫ μ.f 0 ≫ T.π.f 0 =
      moduleTensorMap.{uA, uR, v} (P.π.f 0) (Q.π.f 0))
    (μ' : chainTensor.{uA, uR, v} P'.complex Q'.complex ⟶ T'.complex)
    (hμ' : ιMapBifunctor P'.complex Q'.complex (ModuleCat.moduleTensorLarge.{uR, max uA v} R)
        (ComplexShape.down ℕ) 0 0 0 rfl ≫ μ'.f 0 ≫ T'.π.f 0 =
      moduleTensorMap.{uA, uR, v} (P'.π.f 0) (Q'.π.f 0)) :
    moduleTensorMap.{uR, uA, v} ((torBaseChange.{uR, uA, v} R A f n).map g)
        ((torBaseChange.{uR, uA, v} R A f m).map h) ≫
        resolutionComponent.{uR, uA, v} f n m P' Q' T' μ' =
      resolutionComponent.{uR, uA, v} f n m P Q T μ ≫
        (torBaseChange.{uR, uA, v} R A f (n + m)).map (moduleTensorMap.{uA, uR, v} g h) := by
  let φ := ProjectiveResolution.lift g P P'
  let ψ := ProjectiveResolution.lift h Q Q'
  let χ := ProjectiveResolution.lift (moduleTensorMap.{uA, uR, v} g h) T T'
  obtain ⟨H⟩ := comparison_homotopy.{uR, uA, v} g h φ
    (ProjectiveResolution.lift_commutes_zero _ _ _) ψ
    (ProjectiveResolution.lift_commutes_zero _ _ _) χ
    (ProjectiveResolution.lift_commutes_zero _ _ _) μ hμ μ' hμ'
  have hP := ProjectiveResolution.isoLeftDerivedObj_hom_naturality g P P' φ
    (ProjectiveResolution.lift_commutes_zero _ _ _) (extensionScalars.{uR, uA, v} f) n
  have hQ := ProjectiveResolution.isoLeftDerivedObj_hom_naturality h Q Q' ψ
    (ProjectiveResolution.lift_commutes_zero _ _ _) (extensionScalars.{uR, uA, v} f) m
  have hT := ProjectiveResolution.isoLeftDerivedObj_hom_naturality _ T T' χ
    (ProjectiveResolution.lift_commutes_zero _ _ _) (extensionScalars.{uR, uA, v} f) (n + m)
  have hR := resolutionProduct_naturality.{uR, uA, v} f n m φ ψ χ μ μ' H
  dsimp only [resolutionComponent]
  rw [← CategoryTheory.cancel_mono (C := ModuleCat.{max uR uA v} A)
    (T'.isoLeftDerivedObj (extensionScalars.{uR, uA, v} f) (n + m)).hom]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [hT, Iso.inv_hom_id_assoc, reassoc_of% (moduleTensorMap_comp.{uR, uA, v}), hP, hQ,
    ← moduleTensorMap_comp.{uR, uA, v}, Category.assoc]
  exact congrArg _ hR

private lemma moduleTensorMap_id {S : Type uA} [CommRing S] (M N : ModuleCat.{max uR uA v} S) :
    moduleTensorMap.{uR, uA, v} (𝟙 M) (𝟙 N) = 𝟙 _ := by
  apply ModuleCat.hom_ext
  apply TensorProduct.ext
  ext x y
  rfl

private lemma resolutionComponent_eq (n m : ℕ)
    {M N : ModuleCat.{max uR uA v} R}
    {P P' : ProjectiveResolution M} {Q Q' : ProjectiveResolution N}
    {T T' : ProjectiveResolution (((ModuleCat.moduleTensorLarge.{uR, max uA v} R).obj M).obj N)}
    (μ : chainTensor.{uA, uR, v} P.complex Q.complex ⟶ T.complex)
    (hμ : ιMapBifunctor P.complex Q.complex (ModuleCat.moduleTensorLarge.{uR, max uA v} R)
        (ComplexShape.down ℕ) 0 0 0 rfl ≫ μ.f 0 ≫ T.π.f 0 =
      moduleTensorMap.{uA, uR, v} (P.π.f 0) (Q.π.f 0))
    (μ' : chainTensor.{uA, uR, v} P'.complex Q'.complex ⟶ T'.complex)
    (hμ' : ιMapBifunctor P'.complex Q'.complex (ModuleCat.moduleTensorLarge.{uR, max uA v} R)
        (ComplexShape.down ℕ) 0 0 0 rfl ≫ μ'.f 0 ≫ T'.π.f 0 =
      moduleTensorMap.{uA, uR, v} (P'.π.f 0) (Q'.π.f 0)) :
    resolutionComponent.{uR, uA, v} f n m P Q T μ =
      resolutionComponent.{uR, uA, v} f n m P' Q' T' μ' := by
  have := resolutionComponent_naturality.{uR, uA, v} f n m (𝟙 M) (𝟙 N) μ hμ μ' hμ'
  simpa only [CategoryTheory.Functor.map_id, moduleTensorMap_id.{uR, uA, v},
    moduleTensorMap_id.{uA, uR, v}, Category.id_comp, Category.comp_id] using this.symm

private noncomputable def chosenComparison (M N : ModuleCat.{max uR uA v} R) :
    chainTensor.{uA, uR, v} (projectiveResolution M).complex (projectiveResolution N).complex ⟶
      (projectiveResolution
        (((ModuleCat.moduleTensorLarge.{uR, max uA v} R).obj M).obj N)).complex :=
  (exists_normalized_comparison.{uR, uA, v} (projectiveResolution M) (projectiveResolution N)
    (projectiveResolution _)).choose

private lemma chosenComparison_zero (M N : ModuleCat.{max uR uA v} R) :
    ιMapBifunctor (projectiveResolution M).complex (projectiveResolution N).complex
        (ModuleCat.moduleTensorLarge.{uR, max uA v} R) (ComplexShape.down ℕ) 0 0 0 rfl ≫
        (chosenComparison.{uR, uA, v} M N).f 0 ≫ (projectiveResolution _).π.f 0 =
      moduleTensorMap.{uA, uR, v} ((projectiveResolution M).π.f 0)
        ((projectiveResolution N).π.f 0) :=
  (exists_normalized_comparison.{uR, uA, v} (projectiveResolution M) (projectiveResolution N)
    (projectiveResolution _)).choose_spec.1

/-- The cross product in bidegree `(n, m)`, computed from the chosen projective
resolutions. -/
private noncomputable def crossProduct (n m : ℕ) :
    (torBaseChange.{uR, uA, v} R A f n).prod (torBaseChange.{uR, uA, v} R A f m) ⋙
        Functor.uncurry.obj (ModuleCat.moduleTensorLarge.{uA, max uR v} A) ⟶
      Functor.uncurry.obj (ModuleCat.moduleTensorLarge.{uR, max uA v} R) ⋙
        torBaseChange.{uR, uA, v} R A f (n + m) where
  app X := resolutionComponent.{uR, uA, v} f n m (projectiveResolution X.1)
    (projectiveResolution X.2) (projectiveResolution _) (chosenComparison.{uR, uA, v} X.1 X.2)
  naturality X Y g :=
    resolutionComponent_naturality.{uR, uA, v} f n m g.1 g.2 _
      (chosenComparison_zero.{uR, uA, v} X.1 X.2) _ (chosenComparison_zero.{uR, uA, v} Y.1 Y.2)

end Assembly

section DegreeZero
variable {R : Type uR} {A : Type uA} [CommRing R] [CommRing A] (f : R →+* A)

private lemma homologyπ_fromLeftDerivedZero
    {M : ModuleCat.{max uR uA v} R} (P : ProjectiveResolution M) :
    (extC.{uR, uA, v} f P.complex).homologyπ 0 ≫
        (ChainComplex.isoHomologyι₀ (extC.{uR, uA, v} f P.complex)).hom ≫
        P.fromLeftDerivedZero' (extensionScalars f) =
      (extC.{uR, uA, v} f P.complex).iCycles 0 ≫
        (extensionScalars f).map (P.π.f 0) := by
  show _ ≫ (extC.{uR, uA, v} f P.complex).homologyι 0 ≫ _ = _
  rw [homology_π_ι_assoc, ProjectiveResolution.pOpcycles_comp_fromLeftDerivedZero']

private lemma resolutionProduct_degree_zero
    {M N : ModuleCat.{max uR uA v} R}
    (P : ProjectiveResolution M) (Q : ProjectiveResolution N)
    (T : ProjectiveResolution (((ModuleCat.moduleTensorLarge.{uR, max uA v} R).obj M).obj N))
    (μ : chainTensor.{uA, uR, v} P.complex Q.complex ⟶ T.complex)
    (hμ : ιMapBifunctor P.complex Q.complex (ModuleCat.moduleTensorLarge.{uR, max uA v} R)
      (ComplexShape.down ℕ) 0 0 0 rfl ≫ μ.f 0 ≫ T.π.f 0 =
      moduleTensorMap.{uA, uR, v} (P.π.f 0) (Q.π.f 0)) :
    resolutionProduct.{uR, uA, v} f 0 0 μ ≫
        (ChainComplex.isoHomologyι₀ (extC.{uR, uA, v} f T.complex)).hom ≫
        T.fromLeftDerivedZero' (extensionScalars f) =
      moduleTensorMap.{uR, uA, v}
        ((ChainComplex.isoHomologyι₀ (extC.{uR, uA, v} f P.complex)).hom ≫
          P.fromLeftDerivedZero' (extensionScalars f))
        ((ChainComplex.isoHomologyι₀ (extC.{uR, uA, v} f Q.complex)).hom ≫
          Q.fromLeftDerivedZero' (extensionScalars f)) ≫ zeroBaseChange R A f M N := by
  let C := chainHomologyProductOfCycles.{uR, uA, v}
    (extC.{uR, uA, v} f P.complex) (extC.{uR, uA, v} f Q.complex) 0 0
  obtain ⟨z, hz, hπ⟩ := C.maps_cycles
  let χ := chainBaseChange.{uR, uA, v} f P.complex Q.complex ≫ extC_map f μ
  have hprod : resolutionProduct.{uR, uA, v} f 0 0 μ = C.map ≫ homologyMap χ 0 := rfl
  have : Epi (moduleTensorMap.{uR, uA, v}
      ((extC.{uR, uA, v} f P.complex).homologyπ 0)
      ((extC.{uR, uA, v} f Q.complex).homologyπ 0)) := epi_moduleTensorMap _ _
  rw [← cancel_epi (moduleTensorMap.{uR, uA, v}
    ((extC.{uR, uA, v} f P.complex).homologyπ 0)
    ((extC.{uR, uA, v} f Q.complex).homologyπ 0))]
  rw [hprod]
  simp only [Category.assoc]
  rw [reassoc_of% hπ, homologyπ_naturality_assoc,
    homologyπ_fromLeftDerivedZero.{uR, uA, v} f T,
    reassoc_of% (moduleTensorMap_comp.{uR, uA, v}),
    homologyπ_fromLeftDerivedZero.{uR, uA, v} f P,
    homologyπ_fromLeftDerivedZero.{uR, uA, v} f Q]
  rw [cyclesMap_i_assoc, reassoc_of% hz]
  dsimp only [χ, HomologicalComplex.comp_f, extC_map, Functor.mapHomologicalComplex_map_f]
  simp only [Category.assoc]
  rw [reassoc_of% (chainBaseChange_ι.{uR, uA, v} f P.complex Q.complex 0 0 0 rfl),
    ← Functor.map_comp_assoc, ← Functor.map_comp]
  rw [Category.assoc, hμ]
  erw [← zeroBaseChange_naturality.{uR, uA, v} f (P.π.f 0) (Q.π.f 0)]
  rw [reassoc_of% (moduleTensorMap_comp.{uR, uA, v})]
  rfl

private lemma crossProduct_degree_zero (M N : ModuleCat.{max uR uA v} R) :
    (crossProduct.{uR, uA, v} f 0 0).app (M, N) ≫
        (extensionScalars.{uR, uA, v} f).fromLeftDerivedZero.app
          (((ModuleCat.moduleTensorLarge.{uR, max uA v} R).obj M).obj N) =
      moduleTensorMap.{uR, uA, v}
          ((extensionScalars.{uR, uA, v} f).fromLeftDerivedZero.app M)
          ((extensionScalars.{uR, uA, v} f).fromLeftDerivedZero.app N) ≫
        zeroBaseChange.{uR, uA, v} R A f M N := by
  dsimp only [crossProduct, resolutionComponent]
  rw [(projectiveResolution M).fromLeftDerivedZero_eq (extensionScalars f),
    (projectiveResolution N).fromLeftDerivedZero_eq (extensionScalars f),
    (projectiveResolution _).fromLeftDerivedZero_eq (extensionScalars f)]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [resolutionProduct_degree_zero.{uR, uA, v} f _ _ _ _ (chosenComparison_zero.{uR, uA, v} M N)]
  rw [reassoc_of% (moduleTensorMap_comp.{uR, uA, v})]

end DegreeZero

section FinalAssembly
variable {R : Type uR} {A : Type uA} [CommRing R] [CommRing A] (f : R →+* A)

private lemma projective_extensionScalars
    (M : ModuleCat.{max uR uA v} R) [Projective M] :
    Projective ((extensionScalars.{uR, uA, v} f).obj M) := by
  let := f.toAlgebra
  show Projective (ModuleCat.of A (A ⊗[R] M))
  infer_instance

private noncomputable def resolutionModel (n m : ℕ)
    (M N : ModuleCat.{max uR uA v} R)
    (P : ProjectiveResolution M) (Q : ProjectiveResolution N)
    (T : ProjectiveResolution
      (((ModuleCat.moduleTensorLarge.{uR, max uA v} R).obj M).obj N)) :
    ResolutionModel R A f n m (crossProduct.{uR, uA, v} f n m) M N P Q T := by
  haveI (k : ℕ) : Projective ((extC.{uR, uA, v} f P.complex).X k) :=
    projective_extensionScalars.{uR, uA, v} f (P.complex.X k)
  haveI (k : ℕ) : Projective ((extC.{uR, uA, v} f Q.complex).X k) :=
    projective_extensionScalars.{uR, uA, v} f (Q.complex.X k)
  let H := exists_normalized_comparison.{uR, uA, v} P Q T
  let μ := H.choose
  have hμ := H.choose_spec.1
  have huniq := H.choose_spec.2
  refine
    { μ := μ
      μ_zero := hμ
      μ_unique := huniq
      baseChange := chainBaseChange.{uR, uA, v} f P.complex Q.complex
      baseChange_ι := chainBaseChange_ι.{uR, uA, v} f P.complex Q.complex
      cohomologyProduct := chainHomologyProductOfCycles.{uR, uA, v}
        (extC.{uR, uA, v} f P.complex) (extC.{uR, uA, v} f Q.complex) n m
      cohomologyProduct_agreesWith068H := chainHomologyProduct_agreesWith068H.{uR, uA, v} _
      product_eq := ?_ }
  have he := resolutionComponent_eq.{uR, uA, v} f n m
    (chosenComparison.{uR, uA, v} M N) (chosenComparison_zero.{uR, uA, v} M N) μ hμ
  dsimp only [crossProduct]
  rw [he]
  dsimp only [resolutionComponent, resolutionProduct]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

private noncomputable def normalizedSystem : System.{uR, uA, v} R A f where
  product := crossProduct.{uR, uA, v} f
  resolution n m M N P Q T := ⟨resolutionModel.{uR, uA, v} f n m M N P Q T⟩
  degree_zero := crossProduct_degree_zero.{uR, uA, v} f
  product_unique n m _q hq := product_eq_of_resolution.{uR, uA, v} hq
    (fun M N P Q T ↦ ⟨resolutionModel.{uR, uA, v} f n m M N P Q T⟩)

end FinalAssembly

end TorCrossProduct

/-- A natural, normalized Tor cross-product system exists for every ring map. -/
public theorem TorCrossProduct.canonical_nonempty (R : Type uR) (A : Type uA)
    [CommRing R] [CommRing A] (f : R →+* A) :
    Nonempty (TorCrossProduct.System.{uR, uA, v} R A f) :=
  ⟨TorCrossProduct.normalizedSystem.{uR, uA, v} f⟩

end

@[expose] public noncomputable section

namespace TorCrossProduct

attribute [local instance] HasDerivedCategory.standard

variable (R : Type uR) (A : Type uA) [CommRing R] [CommRing A]

/-- The canonical Tor cross-product system, selected from its resolution construction. -/
public noncomputable def canonical (f : R →+* A) : System.{uR, uA, v} R A f :=
  Classical.choice (canonical_nonempty.{uR, uA, v} R A f)

/-- The canonical natural Tor cross product in bidegree `(n, m)`. -/
public noncomputable abbrev product (f : R →+* A) (n m : ℕ) :=
  (canonical.{uR, uA, v} R A f).product n m

/-- Transport the first of two independently universed module carriers to their common
universe. -/
public abbrev liftLeft (M : ModuleCat.{w} R) :
    ModuleCat.{max uR uA w x} R :=
  (ModuleCat.uliftFunctor.{max uR uA x, w} R).obj M

/-- Transport the second of two independently universed module carriers to their common
universe. -/
public abbrev liftRight (N : ModuleCat.{x} R) :
    ModuleCat.{max uR uA w x} R :=
  (ModuleCat.uliftFunctor.{max uR uA w, x} R).obj N

/-- The canonical Tor cross product evaluated on modules with independently universed
carriers.  Both modules are explicitly transported to the common universe
`max uR uA w x`. -/
public noncomputable def map (f : R →+* A) (n m : ℕ)
    (M : ModuleCat.{w} R) (N : ModuleCat.{x} R) :
    ((ModuleCat.moduleTensorLarge.{uA, max uR w x} A).obj
      ((torBaseChange.{uR, uA, max w x} R A f n).obj
        (liftLeft.{uR, uA, w, x} R M))).obj
        ((torBaseChange.{uR, uA, max w x} R A f m).obj
          (liftRight.{uR, uA, w, x} R N)) ⟶
      (torBaseChange.{uR, uA, max w x} R A f (n + m)).obj
        (((ModuleCat.moduleTensorLarge.{uR, max uA w x} R).obj
          (liftLeft.{uR, uA, w, x} R M)).obj
          (liftRight.{uR, uA, w, x} R N)) :=
  (product.{uR, uA, max w x} R A f n m).app
    (liftLeft.{uR, uA, w, x} R M, liftRight.{uR, uA, w, x} R N)

end TorCrossProduct

namespace RingTheory.TorProducts

variable (R : Type uR) (A : Type uA) [CommRing R] [CommRing A] [Algebra R A]

/-- The tensor product of modules as a bifunctor of a pair, in a carrier universe independent
of the ring universe. This is the uncurried form of `ModuleCat.moduleTensorLarge`, so that a
product of Tor functors can be composed with it. -/
abbrev tensorBifunctor.{s, t} (S : Type s) [CommRing S] :
    (ModuleCat.{max s t} S × ModuleCat.{max s t} S) ⥤ ModuleCat.{max s t} S :=
  Functor.uncurry.obj (ModuleCat.moduleTensorLarge.{s, t} S)

/-- `Torⁿᴿ(-, A)` as an `A`-module-valued functor, for an `R`-algebra `A`. This is the `n`-th
left-derived functor of extension of scalars along the structure map `R → A`. -/
abbrev torBaseChange (n : ℕ) : ModuleCat.{max uR uA v} R ⥤ ModuleCat.{max uR uA v} A :=
  TorCrossProduct.torBaseChange.{uR, uA, v} R A (algebraMap R A) n

/-- **Stacks 068J.** The canonical Tor product
`Torⁿᴿ(M, A) ⊗[A] Torᵐᴿ(N, A) → Torⁿ⁺ᵐᴿ(M ⊗[R] N, A)`, simultaneously for all `R`-modules
`M` and `N`. Packaging it as a natural transformation records its naturality in both
variables. -/
@[stacks 068J]
public noncomputable def torProduct (n m : ℕ) :
    (torBaseChange.{uR, uA, v} R A n).prod (torBaseChange.{uR, uA, v} R A m) ⋙
        tensorBifunctor.{uA, max uR v} A ⟶
      tensorBifunctor.{uR, max uA v} R ⋙ torBaseChange.{uR, uA, v} R A (n + m) :=
  TorCrossProduct.product.{uR, uA, v} R A (algebraMap R A) n m

/-- The Tor product is induced by the normalized chain comparison and the cocycle product on
the homology of the scalar-extended resolutions, for every choice of projective
resolutions. -/
public theorem torProduct_resolution (n m : ℕ) (M N : ModuleCat.{max uR uA v} R)
    (P : ProjectiveResolution M) (Q : ProjectiveResolution N)
    (T : ProjectiveResolution ((tensorBifunctor.{uR, max uA v} R).obj (M, N))) :
    Nonempty (TorCrossProduct.ResolutionModel.{uR, uA, v} R A (algebraMap R A) n m
      (torProduct.{uR, uA, v} R A n m) M N P Q T) :=
  (TorCrossProduct.canonical.{uR, uA, v} R A (algebraMap R A)).resolution n m M N P Q T

/-- In bidegree `(0,0)`, the product is ordinary tensor base change under the canonical
maps from zeroth left-derived functors. In particular, it sends unit classes to unit
classes. -/
public theorem torProduct_degree_zero (M N : ModuleCat.{max uR uA v} R) :
    (torProduct.{uR, uA, v} R A 0 0).app (M, N) ≫
        (CochainComplex.DerivedTensor.extensionScalars.{uR, uA, v}
          (algebraMap R A)).fromLeftDerivedZero.app
          ((tensorBifunctor.{uR, max uA v} R).obj (M, N)) =
      TorCrossProduct.moduleTensorMap.{uR, uA, v}
          ((CochainComplex.DerivedTensor.extensionScalars.{uR, uA, v}
            (algebraMap R A)).fromLeftDerivedZero.app M)
          ((CochainComplex.DerivedTensor.extensionScalars.{uR, uA, v}
            (algebraMap R A)).fromLeftDerivedZero.app N) ≫
        TorCrossProduct.zeroBaseChange.{uR, uA, v} R A (algebraMap R A) M N :=
  (TorCrossProduct.canonical.{uR, uA, v} R A (algebraMap R A)).degree_zero M N

/-- The normalized resolution construction uniquely determines the Tor product. -/
public theorem torProduct_unique (n m : ℕ)
    (q : (torBaseChange.{uR, uA, v} R A n).prod (torBaseChange.{uR, uA, v} R A m) ⋙
        tensorBifunctor.{uA, max uR v} A ⟶
      tensorBifunctor.{uR, max uA v} R ⋙ torBaseChange.{uR, uA, v} R A (n + m))
    (hq : ∀ (M N : ModuleCat.{max uR uA v} R)
      (P : ProjectiveResolution M) (Q : ProjectiveResolution N)
      (T : ProjectiveResolution ((tensorBifunctor.{uR, max uA v} R).obj (M, N))),
      Nonempty (TorCrossProduct.ResolutionModel.{uR, uA, v} R A (algebraMap R A) n m
        q M N P Q T)) :
    q = torProduct.{uR, uA, v} R A n m :=
  (TorCrossProduct.canonical.{uR, uA, v} R A (algebraMap R A)).product_unique n m q hq

end RingTheory.TorProducts

end
