module

public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.RingCohomologyMapTensor
public import StacksFrontier.Homology.Tor.DerivedTensorKFlatLeft
public import StacksFrontier.Homology.Tor.BaseChangeTensorMonoidalIso

/-!
# The comparison of Stacks 065Z on a derived tensor product

Let `R → A`, `R → R'`, `A → A'`, `R' → A'` be a commutative square of commutative rings. If the
comparison of Stacks 065Z followed by `φ : M ⊗ᴸ_A A' ⟶ N` is invertible, then so is the
comparison at `E ⊗ᴸ_A M` followed by `(E ⊗ᴸ_A M) ⊗ᴸ_A A' ≅ (E ⊗ᴸ_A A') ⊗ᴸ_{A'} (M ⊗ᴸ_A A')` and
`(E ⊗ᴸ_A A') ⊗ᴸ_{A'} φ`, for every `E` in `D(A)`. This is the ring-level content of
Stacks 0DKI (1).

## Main definitions

* `RingTheory.TorIndependence.derivedProjectionIso`: the projection formula
  `E ⊗ᴸ_A N|_A ≅ ((E ⊗ᴸ_A A') ⊗ᴸ_{A'} N)|_A`, natural in `N`, for `E` K-flat.

## References

* [Stacks Project, Tag 065Z](https://stacks.math.columbia.edu/tag/065Z)
* [Stacks Project, Tag 0DKI](https://stacks.math.columbia.edu/tag/0DKI)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CochainComplex.ExtendScalars CochainComplex.DerivedTensor

universe u

namespace RingTheory.TorIndependence

attribute [local instance] HasDerivedCategory.standard

section Projection

variable {A A' : Type u} [CommRing A] [CommRing A'] (h : A →+* A')

/-- Extension of scalars of a K-flat complex is K-flat. -/
theorem kFlat_mapCochainComplex (E : CochainComplex (ModuleCat.{u} A) ℤ) (hE : E.KFlat) :
    ((mapCochainComplex h).obj E).KFlat :=
  CochainComplex.KFlat.ScalarBaseChange.kFlat_extendScalars.{u, u, u} h E hE

/-- The chain-level projection formula as a natural isomorphism in the complex of
`A'`-modules. -/
def leftProjectionNatIso (E : CochainComplex (ModuleCat.{u} A) ℤ) :
    CochainComplex.restrictScalarsLarge.{u, u, u} h ⋙ tensorLeft E ≅
      tensorLeft ((mapCochainComplex h).obj E) ⋙ CochainComplex.restrictScalarsLarge.{u, u, u} h :=
  NatIso.ofComponents (fun L => asIso (leftProjectionMap h E L))
    (fun v => by
      simp only [Functor.comp_map, asIso_hom]
      exact leftProjectionMap_naturality_right h E v)

/-- Pasting six commutative squares. -/
theorem comp_six_squares {C : Type*} [Category C] {x₀ x₁ x₂ x₃ x₄ x₅ x₆ y₀ y₁ y₂ y₃ y₄ y₅ y₆ : C}
    (a₀ : x₀ ⟶ y₀) (a₁ : x₁ ⟶ y₁) (a₂ : x₂ ⟶ y₂) (a₃ : x₃ ⟶ y₃) (a₄ : x₄ ⟶ y₄) (a₅ : x₅ ⟶ y₅)
    (a₆ : x₆ ⟶ y₆) (p₁ : x₀ ⟶ x₁) (p₂ : x₁ ⟶ x₂) (p₃ : x₂ ⟶ x₃) (p₄ : x₃ ⟶ x₄) (p₅ : x₄ ⟶ x₅)
    (p₆ : x₅ ⟶ x₆) (q₁ : y₀ ⟶ y₁) (q₂ : y₁ ⟶ y₂) (q₃ : y₂ ⟶ y₃) (q₄ : y₃ ⟶ y₄) (q₅ : y₄ ⟶ y₅)
    (q₆ : y₅ ⟶ y₆) (s₁ : a₀ ≫ q₁ = p₁ ≫ a₁) (s₂ : a₁ ≫ q₂ = p₂ ≫ a₂) (s₃ : a₂ ≫ q₃ = p₃ ≫ a₃)
    (s₄ : a₃ ≫ q₄ = p₄ ≫ a₄) (s₅ : a₄ ≫ q₅ = p₅ ≫ a₅) (s₆ : a₅ ≫ q₆ = p₆ ≫ a₆) :
    a₀ ≫ q₁ ≫ q₂ ≫ q₃ ≫ q₄ ≫ q₅ ≫ q₆ = (p₁ ≫ p₂ ≫ p₃ ≫ p₄ ≫ p₅ ≫ p₆) ≫ a₆ := by
  rw [reassoc_of% s₁, reassoc_of% s₂, reassoc_of% s₃, reassoc_of% s₄, reassoc_of% s₅, s₆]
  simp only [Category.assoc]

/-- A functor carries a commutative square to a commutative square. -/
theorem map_square {C D : Type*} [Category C] [Category D] (G : C ⥤ D) {w x y z : C}
    {a : w ⟶ x} {b : x ⟶ z} {c : w ⟶ y} {d : y ⟶ z} (e : a ≫ b = c ≫ d) :
    G.map a ≫ G.map b = G.map c ≫ G.map d := by
  rw [← G.map_comp, e, G.map_comp]

/-- The projection formula on complexes, read in the derived category. -/
def derivedProjectionIsoQ (E : CochainComplex (ModuleCat.{u} A) ℤ) (hE : E.KFlat) :
    DerivedCategory.Q ⋙ ((ModuleCat.restrictScalars.{u} h).mapDerivedCategory ⋙
        (canonicalDerivedTensorProduct A).tensor.obj (DerivedCategory.Q.obj E)) ≅
      DerivedCategory.Q ⋙ ((canonicalDerivedTensorProduct A').tensor.obj
          ((CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
            h).functor.obj (DerivedCategory.Q.obj E)) ⋙
        (ModuleCat.restrictScalars.{u} h).mapDerivedCategory) :=
  NatIso.ofComponents (fun L =>
    ((canonicalDerivedTensorProduct A).tensor.obj (DerivedCategory.Q.obj E)).mapIso
        ((ModuleCat.restrictScalars.{u} h).mapDerivedCategoryFactors.app L) ≪≫
      ((canonicalDerivedTensorProduct A).kFlatLeftComparison E hE).app
        ((CochainComplex.restrictScalarsLarge.{u, u, u} h).obj L) ≪≫
      DerivedCategory.Q.mapIso (asIso (leftProjectionMap h E L)) ≪≫
      ((ModuleCat.restrictScalars.{u} h).mapDerivedCategoryFactors.app
        ((mapCochainComplex h).obj E ⊗ L)).symm ≪≫
      (ModuleCat.restrictScalars.{u} h).mapDerivedCategory.mapIso
        (((canonicalDerivedTensorProduct A').kFlatLeftComparison ((mapCochainComplex h).obj E)
          (kFlat_mapCochainComplex h E hE)).app L).symm ≪≫
      (ModuleCat.restrictScalars.{u} h).mapDerivedCategory.mapIso
        (((canonicalDerivedTensorProduct A').tensor.mapIso
          (@asIso _ _ _ _ ((extensionComparison h).app E)
            (isIso_extensionComparison_app h E hE))).symm.app (DerivedCategory.Q.obj L)))
    (fun {L L'} v => by
      have := isIso_extensionComparison_app h E hE
      have s₆ := map_square (ModuleCat.restrictScalars.{u} h).mapDerivedCategory
        (((canonicalDerivedTensorProduct A').tensor.map
          (inv ((extensionComparison h).app E))).naturality (DerivedCategory.Q.map v))
      have := comp_six_squares _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
        (map_square ((canonicalDerivedTensorProduct A).tensor.obj (DerivedCategory.Q.obj E))
          ((ModuleCat.restrictScalars.{u} h).mapDerivedCategoryFactors.hom.naturality v))
        (((canonicalDerivedTensorProduct A).kFlatLeftComparison E hE).hom.naturality
          ((CochainComplex.restrictScalarsLarge.{u, u, u} h).map v))
        (map_square DerivedCategory.Q (leftProjectionMap_naturality_right h E v))
        ((ModuleCat.restrictScalars.{u} h).mapDerivedCategoryFactors.inv.naturality
          ((mapCochainComplex h).obj E ◁ v))
        (map_square (ModuleCat.restrictScalars.{u} h).mapDerivedCategory
          (((canonicalDerivedTensorProduct A').kFlatLeftComparison ((mapCochainComplex h).obj E)
            (kFlat_mapCochainComplex h E hE)).inv.naturality v))
        s₆
      simp only [Functor.comp_map] at this
      exact this)

/-- **The derived projection formula** `E ⊗ᴸ_A N|_A ≅ ((E ⊗ᴸ_A A') ⊗ᴸ_{A'} N)|_A`, natural in
`N`, for a K-flat complex `E` of `A`-modules. -/
def derivedProjectionIso (E : CochainComplex (ModuleCat.{u} A) ℤ) (hE : E.KFlat) :
    (ModuleCat.restrictScalars.{u} h).mapDerivedCategory ⋙
        (canonicalDerivedTensorProduct A).tensor.obj (DerivedCategory.Q.obj E) ≅
      (canonicalDerivedTensorProduct A').tensor.obj
          ((CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
            h).functor.obj (DerivedCategory.Q.obj E)) ⋙
        (ModuleCat.restrictScalars.{u} h).mapDerivedCategory :=
  Localization.liftNatIso DerivedCategory.Q
    (HomologicalComplex.quasiIso (ModuleCat.{u} A') (ComplexShape.up ℤ)) _ _ _ _
    (derivedProjectionIsoQ h E hE)

/-- The component of `derivedProjectionIso` at the image of a complex `L` under
`DerivedCategory.Q` is the component of `derivedProjectionIsoQ` at `L`. -/
theorem derivedProjectionIso_hom_app_Q (E : CochainComplex (ModuleCat.{u} A) ℤ) (hE : E.KFlat)
    (L : CochainComplex (ModuleCat.{u} A') ℤ) :
    (derivedProjectionIso h E hE).hom.app (DerivedCategory.Q.obj L) =
      (derivedProjectionIsoQ h E hE).hom.app L := by
  simp [derivedProjectionIso]

end Projection

section Abstract

/-- Inverting an equation between triple composites of isomorphisms. -/
theorem inv_eq_of_triple {C : Type*} [Category C] {a b c d e f : C} (X : a ≅ b) (Y : b ≅ c)
    (Z : c ≅ d) (U : a ≅ e) (V : e ≅ f) (W : f ≅ d)
    (h : X.hom ≫ Y.hom ≫ Z.hom = U.hom ≫ V.hom ≫ W.hom) :
    Z.inv ≫ Y.inv ≫ X.inv = W.inv ≫ V.inv ≫ U.inv := by
  calc Z.inv ≫ Y.inv ≫ X.inv
      = (W.inv ≫ V.inv ≫ U.inv) ≫ (X.hom ≫ Y.hom ≫ Z.hom) ≫ Z.inv ≫ Y.inv ≫ X.inv := by
        rw [h]
        simp
    _ = W.inv ≫ V.inv ≫ U.inv := by simp

/-- The bookkeeping of the tensor step of Stacks 0DKI (1), for arbitrary functors: if a
composite through `ρ_h` is invertible, so is its image under `T_E` read through the projection
formula `λ`. -/
theorem isIso_of_projection_chain {DA DA' : Type*} [Category DA] [Category DA']
    (ρh : DA' ⥤ DA) (TE : DA ⥤ DA) (TE' : DA' ⥤ DA') (lam : ρh ⋙ TE ≅ TE' ⋙ ρh)
    {a r₁ a₂ r₂ r₃ r₄ b : DA} {d d₂ d₃ d₄ d₅ d₆ n e₁ : DA'}
    (Qκ : a ⟶ r₁) (φh₁ : ρh.obj d ≅ r₁) (c1d : TE.obj r₁ ⟶ r₂) (c1a : TE.obj a ⟶ a₂)
    (QEk : a₂ ⟶ r₂) (hc1 : TE.map Qκ ≫ c1d = c1a ≫ QEk)
    (c' : TE.obj a ≅ b) (Qα : b ⟶ a₂) (hc' : c'.inv ≫ c1a = Qα)
    (Qm : r₂ ⟶ r₃) (φh₂ : r₃ ⟶ ρh.obj d₂) (c1d' : d₂ ⟶ e₁) (τE : e₁ ⟶ TE'.obj d)
    (hlam : lam.hom.app d = TE.map φh₁.hom ≫ c1d ≫ Qm ≫ φh₂ ≫ ρh.map (c1d' ≫ τE))
    (Qκ' : b ⟶ r₄) (Qrμ : r₄ ⟶ r₃) (hY : Qα ≫ QEk ≫ Qm = Qκ' ≫ Qrμ)
    (φh₃ : r₄ ⟶ ρh.obj d₃) (Qμ : d₃ ⟶ d₂) (hfh : Qrμ ≫ φh₂ = φh₃ ≫ ρh.map Qμ)
    (yi : d ⟶ d₄) (φ : d₄ ⟶ n) (w : d₃ ⟶ d₅) (z₁ : d₅ ⟶ d₆) (z₂ : d₆ ⟶ TE'.obj d₄)
    (hkey : Qμ ≫ c1d' ≫ τE ≫ TE'.map yi = w ≫ z₁ ≫ z₂)
    (hP : IsIso (Qκ ≫ φh₁.inv ≫ ρh.map (yi ≫ φ))) :
    IsIso (Qκ' ≫ φh₃ ≫ ρh.map (w ≫ z₁ ≫ z₂ ≫ TE'.map φ)) := by
  have key : Qκ' ≫ φh₃ ≫ ρh.map (w ≫ z₁ ≫ z₂ ≫ TE'.map φ) =
      c'.inv ≫ TE.map (Qκ ≫ φh₁.inv ≫ ρh.map (yi ≫ φ)) ≫ lam.hom.app n := by
    have hn : TE.map (ρh.map (yi ≫ φ)) ≫ lam.hom.app n =
        lam.hom.app d ≫ ρh.map (TE'.map (yi ≫ φ)) := lam.hom.naturality (yi ≫ φ)
    rw [TE.map_comp Qκ, TE.map_comp φh₁.inv, Category.assoc, Category.assoc, hn, hlam]
    simp only [Functor.map_comp, Category.assoc]
    rw [← TE.map_comp_assoc φh₁.inv, Iso.inv_hom_id, CategoryTheory.Functor.map_id,
      Category.id_comp, reassoc_of% hc1, reassoc_of% hc', reassoc_of% hY, reassoc_of% hfh]
    have hk := congrArg ρh.map hkey
    simp only [Functor.map_comp] at hk
    rw [reassoc_of% hk]
  rw [key]
  infer_instance

end Abstract

section KFlat

variable {R A R' A' : Type u} [CommRing R] [CommRing A] [CommRing R'] [CommRing A']
  (f : R →+* A) (g : R →+* R') (h : A →+* A') (i : R' →+* A') (sq : h.comp f = i.comp g)

/-- The standard tensor base-change isomorphism of Stacks 068I for derived extension of scalars
along `h`, for the canonical derived tensor products. -/
abbrev extensionTensorIso :=
  derivedExtensionScalarsTensorIso.{u, u, u} h (canonicalDerivedTensorProduct A).toGeneral
    (canonicalDerivedTensorProduct A').toGeneral
    (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u} h)

/-- **The tensor step of Stacks 0DKI (1) on K-flat models.** -/
theorem isIso_model_tensor (F : CochainComplex (ModuleCat.{u} R) ℤ)
    (q : F ⟶ (CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj
      ((ModuleCat.restrictScalars.{u} g).obj (ModuleCat.of R' R')))
    (E P : CochainComplex (ModuleCat.{u} A) ℤ) (hE : E.KFlat) (hP : P.KFlat)
    {N : DerivedCategory (ModuleCat.{u} A')}
    (φ : (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
      h).functor.obj (DerivedCategory.Q.obj P) ⟶ N)
    (hφ : haveI := isIso_extensionComparison_app h P hP
      IsIso (DerivedCategory.Q.map (resolutionModelMap f g h i sq F q P) ≫
        (ModuleCat.restrictScalars.{u} h).mapDerivedCategoryFactors.inv.app
          ((mapCochainComplex h).obj P) ≫
        (ModuleCat.restrictScalars.{u} h).mapDerivedCategory.map
          (inv ((extensionComparison h).app P) ≫ φ))) :
    haveI := isIso_extensionComparison_app h (E ⊗ P)
      (CochainComplex.KFlat.tensor A E P hE hP)
    IsIso (DerivedCategory.Q.map (resolutionModelMap f g h i sq F q (E ⊗ P)) ≫
        (ModuleCat.restrictScalars.{u} h).mapDerivedCategoryFactors.inv.app
          ((mapCochainComplex h).obj (E ⊗ P)) ≫
        (ModuleCat.restrictScalars.{u} h).mapDerivedCategory.map
          (inv ((extensionComparison h).app (E ⊗ P)) ≫
            (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
              h).functor.map ((canonicalDerivedTensorProduct A).comparison E P hE hP).inv ≫
            (extensionTensorIso h).iso.inv.app (DerivedCategory.Q.obj E, DerivedCategory.Q.obj P) ≫
            ((canonicalDerivedTensorProduct A').tensor.obj
              ((CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
                h).functor.obj (DerivedCategory.Q.obj E))).map φ)) := by
  have hcP := isIso_extensionComparison_app h P hP
  have hcE := isIso_extensionComparison_app h E hE
  have hcEP := isIso_extensionComparison_app h (E ⊗ P) (CochainComplex.KFlat.tensor A E P hE hP)
  let V := (mapCochainComplex f).obj F
  let κ := resolutionModelMap f g h i sq F q P
  let c1 := (canonicalDerivedTensorProduct A).kFlatLeftComparison E hE
  let c1' := (canonicalDerivedTensorProduct A').kFlatLeftComparison ((mapCochainComplex h).obj E)
    (kFlat_mapCochainComplex h E hE)
  let fh := (ModuleCat.restrictScalars.{u} h).mapDerivedCategoryFactors
  let μ := extendScalarsMonoidalIso h E P
  refine isIso_of_projection_chain (ModuleCat.restrictScalars.{u} h).mapDerivedCategory
    ((canonicalDerivedTensorProduct A).tensor.obj (DerivedCategory.Q.obj E))
    ((canonicalDerivedTensorProduct A').tensor.obj
      ((CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
        h).functor.obj (DerivedCategory.Q.obj E)))
    (derivedProjectionIso h E hE)
    (DerivedCategory.Q.map κ) (fh.app ((mapCochainComplex h).obj P))
    (c1.hom.app _) (c1.hom.app (P ⊗ V)) (DerivedCategory.Q.map (E ◁ κ)) (c1.hom.naturality κ)
    (c1.app (P ⊗ V) ≪≫ DerivedCategory.Q.mapIso (α_ E P V).symm)
    (DerivedCategory.Q.map (α_ E P V).hom) (by simp)
    (DerivedCategory.Q.map (leftProjectionMap h E ((mapCochainComplex h).obj P)))
    (fh.inv.app ((mapCochainComplex h).obj E ⊗ (mapCochainComplex h).obj P))
    (c1'.inv.app ((mapCochainComplex h).obj P))
    (((canonicalDerivedTensorProduct A').tensor.map (inv ((extensionComparison h).app E))).app
      (DerivedCategory.Q.obj ((mapCochainComplex h).obj P)))
    ?hlam
    (DerivedCategory.Q.map (resolutionModelMap f g h i sq F q (E ⊗ P)))
    (DerivedCategory.Q.map ((CochainComplex.restrictScalarsLarge.{u, u, u} h).map μ.inv)) ?hY
    (fh.inv.app ((mapCochainComplex h).obj (E ⊗ P))) (DerivedCategory.Q.map μ.inv)
    (fh.inv.naturality μ.inv)
    (inv ((extensionComparison h).app P)) φ
    (inv ((extensionComparison h).app (E ⊗ P)))
    ((CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
      h).functor.map ((canonicalDerivedTensorProduct A).comparison E P hE hP).inv)
    ((extensionTensorIso h).iso.inv.app (DerivedCategory.Q.obj E, DerivedCategory.Q.obj P))
    ?hkey hφ
  case hlam =>
    rw [derivedProjectionIso_hom_app_Q, Functor.map_comp]
    rfl
  case hY =>
    have e' : (α_ E P V).hom ≫ (E ◁ κ) ≫ leftProjectionMap h E ((mapCochainComplex h).obj P) =
        resolutionModelMap f g h i sq F q (E ⊗ P) ≫
          (CochainComplex.restrictScalarsLarge.{u, u, u} h).map μ.inv := by
      rw [← cancel_epi (α_ E P V).inv, Iso.inv_hom_id_assoc,
        reassoc_of% (resolutionModelMap_tensor f g h i sq F q E P), ← Functor.map_comp,
        Iso.hom_inv_id, CategoryTheory.Functor.map_id, Category.comp_id]
    simp only [← Functor.map_comp]
    exact congrArg DerivedCategory.Q.map e'
  case hkey =>
    obtain ⟨hFK, hFL, e, he, heq⟩ := (extensionTensorIso h).comparison E P hE hP
    have heμ := IsTensorBaseChangeIso.hom_eq_extendScalarsMonoidalIso_hom h E P he
    have hc1' := (canonicalDerivedTensorProduct A').kFlatLeftComparison_app_of_kFlat
      ((mapCochainComplex h).obj E) (kFlat_mapCochainComplex h E hE)
      ((mapCochainComplex h).obj P) (kFlat_mapCochainComplex h P hP)
    have key := inv_eq_of_triple
      (((canonicalDerivedTensorProduct A').tensor.obj
          ((CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
            h).functor.obj (DerivedCategory.Q.obj E))).mapIso
          (@asIso _ _ _ _ ((extensionComparison h).app P) hcP) ≪≫
        (((canonicalDerivedTensorProduct A').tensor.mapIso
          (@asIso _ _ _ _ ((extensionComparison h).app E) hcE)).app
            (DerivedCategory.Q.obj ((mapCochainComplex h).obj P))))
      ((canonicalDerivedTensorProduct A').comparison _ _ (kFlat_mapCochainComplex h E hE)
        (kFlat_mapCochainComplex h P hP))
      (DerivedCategory.Q.mapIso μ)
      ((extensionTensorIso h).iso.app (DerivedCategory.Q.obj E, DerivedCategory.Q.obj P))
      ((CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
        h).functor.mapIso ((canonicalDerivedTensorProduct A).comparison E P hE hP))
      (@asIso _ _ _ _ ((extensionComparison h).app (E ⊗ P)) hcEP)
      (by
        have t1 : ((canonicalDerivedTensorProduct A').toGeneral.comparison _ _ hFK hFL).hom =
            ((canonicalDerivedTensorProduct A').comparison _ _ (kFlat_mapCochainComplex h E hE)
              (kFlat_mapCochainComplex h P hP)).hom := rfl
        have t3 : DerivedCategory.Q.map e.hom = (DerivedCategory.Q.mapIso μ).hom := by
          rw [heμ]
          rfl
        rw [t1, t3] at heq
        have nat := ((canonicalDerivedTensorProduct A').tensor.map
          ((extensionComparison h).app E)).naturality ((extensionComparison h).app P)
        simp only [Iso.trans_hom, Category.assoc, Functor.mapIso_hom, asIso_hom, Iso.app_hom]
        rw [reassoc_of% nat]
        exact heq)
    simp only [Iso.trans_inv, Functor.mapIso_inv, asIso_inv, Iso.app_inv] at key
    have hc1i : c1'.inv.app ((mapCochainComplex h).obj P) =
        ((canonicalDerivedTensorProduct A').comparison _ _ (kFlat_mapCochainComplex h E hE)
          (kFlat_mapCochainComplex h P hP)).inv := by
      rw [← hc1']
      rfl
    rw [hc1i]
    refine Eq.trans ?_ key
    simp only [Functor.map_inv]

end KFlat

section Final

/-- If `a ≫ b = c ≫ d ≫ e`, `m ≫ n = d ≫ ℓ` and `ℓ = e ≫ k`, then
`a ≫ b ≫ k = (c ≫ m) ≫ n`. -/
theorem comp_chain_aux₁ {C : Type*} [Category C] {x₀ x₁ x₂ x₃ x₄ x₅ : C} (a : x₀ ⟶ x₁)
    (b : x₁ ⟶ x₂) (c : x₀ ⟶ x₃) (d : x₃ ⟶ x₄) (e : x₄ ⟶ x₂) (k : x₂ ⟶ x₅) {y : C}
    (m : x₃ ⟶ y) (n : y ⟶ x₅) (ℓ : x₄ ⟶ x₅) (hε : a ≫ b = c ≫ d ≫ e) (hT : m ≫ n = d ≫ ℓ)
    (hℓ : ℓ = e ≫ k) : a ≫ b ≫ k = (c ≫ m) ≫ n := by
  rw [Category.assoc c m n, hT, hℓ, ← Category.assoc, hε]
  simp only [Category.assoc]

/-- If `p ≫ σ₁ = σ₀ ≫ G.map a` and `a ≫ b = r ≫ n`, then
`p ≫ σ₁ ≫ G.map b = (σ₀ ≫ G.map r) ≫ G.map n`. -/
theorem comp_chain_aux₂ {C D : Type*} [Category C] [Category D] (G : C ⥤ D) {x₀ x₂ x₃ : C}
    {y₀ y₁ : D} (σ₀ : y₀ ⟶ G.obj x₀) (σ₁ : y₁ ⟶ G.obj x₂) (p : y₀ ⟶ y₁) (a : x₀ ⟶ x₂)
    (b : x₂ ⟶ x₃) {x₄ : C} (r : x₀ ⟶ x₄) (n : x₄ ⟶ x₃) (hn : p ≫ σ₁ = σ₀ ≫ G.map a)
    (hin : a ≫ b = r ≫ n) : p ≫ σ₁ ≫ G.map b = (σ₀ ≫ G.map r) ≫ G.map n := by
  rw [← Category.assoc, hn, Category.assoc, ← G.map_comp, hin, G.map_comp, Category.assoc]

variable {R A R' A' : Type u} [CommRing R] [CommRing A] [CommRing R'] [CommRing A']
  (f : R →+* A) (g : R →+* R') (h : A →+* A') (i : R' →+* A') (sq : h.comp f = i.comp g)

/-- **Stacks 0DKI (1), ring level, on K-flat models.** -/
theorem isIso_ringHomSquareComparison_derivedTensor_kFlat
    (E P : CochainComplex (ModuleCat.{u} A) ℤ) (hE : E.KFlat) (hP : P.KFlat)
    {N : DerivedCategory (ModuleCat.{u} A')}
    (φ : (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
      h).functor.obj (DerivedCategory.Q.obj P) ⟶ N)
    (hφ : IsIso ((ringHomSquareComparison f g h i sq).app (DerivedCategory.Q.obj P) ≫
        (ModuleCat.restrictScalars.{u} i).mapDerivedCategory.map φ)) :
    IsIso ((ringHomSquareComparison f g h i sq).app
        (((canonicalDerivedTensorProduct A).tensor.obj (DerivedCategory.Q.obj E)).obj
          (DerivedCategory.Q.obj P)) ≫
      (ModuleCat.restrictScalars.{u} i).mapDerivedCategory.map
        ((extensionTensorIso h).iso.inv.app (DerivedCategory.Q.obj E, DerivedCategory.Q.obj P) ≫
          ((canonicalDerivedTensorProduct A').tensor.obj
            ((CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
              h).functor.obj (DerivedCategory.Q.obj E))).map φ)) := by
  obtain ⟨F, q, hF, -, hq, -⟩ := CochainComplex.KFlat.exists_kFlat_resolution.{u, u}
    ((CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj
      ((ModuleCat.restrictScalars.{u} g).obj (ModuleCat.of R' R')))
  have h3 := (isIso_ringHomSquareComparison_comp_iff_model f g h i sq F hF q (E ⊗ P)
    (CochainComplex.KFlat.tensor A E P hE hP) _).mpr
    (isIso_model_tensor f g h i sq F q E P hE hP φ
      ((isIso_ringHomSquareComparison_comp_iff_model f g h i sq F hF q P hP φ).mp hφ))
  let c := (canonicalDerivedTensorProduct A).comparison E P hE hP
  let D := CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u} h
  have hn := (ringHomSquareComparison f g h i sq).naturality c.hom
  simp only [Functor.comp_map] at hn
  have key : (ringHomSquareComparison f g h i sq).app
        (((canonicalDerivedTensorProduct A).tensor.obj (DerivedCategory.Q.obj E)).obj
          (DerivedCategory.Q.obj P)) ≫
      (ModuleCat.restrictScalars.{u} i).mapDerivedCategory.map
        ((extensionTensorIso h).iso.inv.app (DerivedCategory.Q.obj E, DerivedCategory.Q.obj P) ≫
          ((canonicalDerivedTensorProduct A').tensor.obj (D.functor.obj
            (DerivedCategory.Q.obj E))).map φ) =
      (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u} g).functor.map
          ((ModuleCat.restrictScalars.{u} f).mapDerivedCategory.map c.hom) ≫
        ((ringHomSquareComparison f g h i sq).app (DerivedCategory.Q.obj (E ⊗ P)) ≫
          (ModuleCat.restrictScalars.{u} i).mapDerivedCategory.map
            (D.functor.map c.inv ≫ (extensionTensorIso h).iso.inv.app
              (DerivedCategory.Q.obj E, DerivedCategory.Q.obj P) ≫
              ((canonicalDerivedTensorProduct A').tensor.obj (D.functor.obj
                (DerivedCategory.Q.obj E))).map φ)) := by
    rw [reassoc_of% hn, Functor.map_comp, ← Category.assoc
      ((ModuleCat.restrictScalars.{u} i).mapDerivedCategory.map (D.functor.map c.hom)),
      ← Functor.map_comp, ← Category.assoc, ← Functor.map_comp, Iso.hom_inv_id,
      CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id, Category.comp_id]
  rw [key]
  infer_instance

/-- **Stacks 0DKI (1), ring level.** For a commutative square of commutative rings
`R → A`, `R → R'`, `A → A'`, `R' → A'`, objects `E`, `M` of `D(A)` and `φ : M ⊗ᴸ_A A' ⟶ N`
in `D(A')`: if the comparison of Stacks 065Z at `M` followed by `φ` is invertible, so is the
comparison at `E ⊗ᴸ_A M` followed by the base-change isomorphism of Stacks 068I
`(E ⊗ᴸ_A M) ⊗ᴸ_A A' ≅ (E ⊗ᴸ_A A') ⊗ᴸ_{A'} (M ⊗ᴸ_A A')` and `(E ⊗ᴸ_A A') ⊗ᴸ_{A'} φ`. -/
theorem isIso_ringHomSquareComparison_derivedTensor (E M : DerivedCategory (ModuleCat.{u} A))
    {N : DerivedCategory (ModuleCat.{u} A')}
    (φ : (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
      h).functor.obj M ⟶ N)
    (hφ : IsIso ((ringHomSquareComparison f g h i sq).app M ≫
        (ModuleCat.restrictScalars.{u} i).mapDerivedCategory.map φ)) :
    IsIso ((ringHomSquareComparison f g h i sq).app
        (((canonicalDerivedTensorProduct A).tensor.obj E).obj M) ≫
      (ModuleCat.restrictScalars.{u} i).mapDerivedCategory.map
        ((extensionTensorIso h).iso.inv.app (E, M) ≫
          ((canonicalDerivedTensorProduct A').tensor.obj
            ((CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
              h).functor.obj E)).map φ)) := by
  obtain ⟨E₀, hE₀, ⟨eE⟩⟩ := CochainComplex.DerivedExtensionScalars.exists_kFlat_model.{u, u, u} E
  obtain ⟨P, hP, ⟨eM⟩⟩ := CochainComplex.DerivedExtensionScalars.exists_kFlat_model.{u, u, u} M
  let D := CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u} h
  let T := (canonicalDerivedTensorProduct A).tensor
  let T' := (canonicalDerivedTensorProduct A').tensor
  let ρi := (ModuleCat.restrictScalars.{u} i).mapDerivedCategory
  let σ := ringHomSquareComparison f g h i sq
  let φ₀ := D.functor.map eM.inv ≫ φ
  have h₀ : IsIso (σ.app (DerivedCategory.Q.obj P) ≫ ρi.map φ₀) := by
    have hn := σ.naturality eM.inv
    simp only [Functor.comp_map] at hn
    dsimp only [φ₀]
    rw [Functor.map_comp, ← Category.assoc, ← hn, Category.assoc]
    infer_instance
  have hK := isIso_ringHomSquareComparison_derivedTensor_kFlat f g h i sq E₀ P hE₀ hP φ₀ h₀
  let s : (T.obj (DerivedCategory.Q.obj E₀)).obj (DerivedCategory.Q.obj P) ⟶ (T.obj E).obj M :=
    (Functor.uncurry.obj T).map (X := (DerivedCategory.Q.obj E₀, DerivedCategory.Q.obj P))
      (Y := (E, M)) (eE.inv, eM.inv)
  have hs : IsIso s := by
    change IsIso ((T.map eE.inv).app _ ≫ (T.obj E).map eM.inv)
    infer_instance
  have hε := (extensionTensorIso h).iso.inv.naturality
    (X := (DerivedCategory.Q.obj E₀, DerivedCategory.Q.obj P)) (Y := (E, M)) (eE.inv, eM.inv)
  have key : ((ModuleCat.restrictScalars.{u} f).mapDerivedCategory ⋙
        (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
          g).functor).map s ≫
      (σ.app ((T.obj E).obj M) ≫
        ρi.map ((extensionTensorIso h).iso.inv.app (E, M) ≫ (T'.obj (D.functor.obj E)).map φ)) =
      (σ.app ((T.obj (DerivedCategory.Q.obj E₀)).obj (DerivedCategory.Q.obj P)) ≫
        ρi.map ((extensionTensorIso h).iso.inv.app
            (DerivedCategory.Q.obj E₀, DerivedCategory.Q.obj P) ≫
          (T'.obj (D.functor.obj (DerivedCategory.Q.obj E₀))).map φ₀)) ≫
        ρi.map ((T'.map (D.functor.map eE.inv)).app N) := by
    have hε' : D.functor.map s ≫ (extensionTensorIso h).iso.inv.app (E, M) =
        (extensionTensorIso h).iso.inv.app (DerivedCategory.Q.obj E₀, DerivedCategory.Q.obj P) ≫
          (T'.map (D.functor.map eE.inv)).app _ ≫ (T'.obj (D.functor.obj E)).map
            (D.functor.map eM.inv) := hε
    exact comp_chain_aux₂ ρi _ _ _ _ _ _ _ (σ.naturality s) <|
      comp_chain_aux₁ (D.functor.map s) ((extensionTensorIso h).iso.inv.app (E, M))
        ((extensionTensorIso h).iso.inv.app (DerivedCategory.Q.obj E₀, DerivedCategory.Q.obj P))
        ((T'.map (D.functor.map eE.inv)).app _) ((T'.obj (D.functor.obj E)).map
          (D.functor.map eM.inv)) ((T'.obj (D.functor.obj E)).map φ)
        ((T'.obj (D.functor.obj (DerivedCategory.Q.obj E₀))).map φ₀)
        ((T'.map (D.functor.map eE.inv)).app N) ((T'.obj (D.functor.obj E)).map φ₀)
        hε' ((T'.map (D.functor.map eE.inv)).naturality φ₀)
        ((T'.obj (D.functor.obj E)).map_comp _ _)
  have hfin : IsIso (((ModuleCat.restrictScalars.{u} f).mapDerivedCategory ⋙
        (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
          g).functor).map s ≫
      (σ.app ((T.obj E).obj M) ≫
        ρi.map ((extensionTensorIso h).iso.inv.app (E, M) ≫
          (T'.obj (D.functor.obj E)).map φ))) := by
    rw [key]
    exact @IsIso.comp_isIso _ _ _ _ _ _ _ hK inferInstance
  exact @IsIso.of_isIso_comp_left _ _ _ _ _ _ _ inferInstance hfin

end Final

end RingTheory.TorIndependence

end
