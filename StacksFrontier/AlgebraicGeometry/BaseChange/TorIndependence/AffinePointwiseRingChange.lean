module

public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.AffinePointwiseRing
public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.TensorBaseChange.SchemeToRing
public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.DerivedStalkCompositionTails
public import StacksFrontier.Homology.Tor.DerivedExtensionScalarsSelfIso

/-!
# The map of Stacks 0DJ7 under a change of the rings of the square

Let `R → A`, `R → R'`, `A → B`, `R' → B` be a square of rings with `B` a localization of
`A ⊗_R R'`, and let `R₁`, `A₁`, `R'₁` be localizations of `R`, `A`, `R'` forming a second square
with the same `B`.  For `K ∈ D(A)`, `E ∈ D(B)` and `ψ : K ⊗ᴸ_A B ⟶ E`, the map of Stacks 0DJ7 of
the first square at `ψ` is invertible in a degree exactly when that of the second square at the
induced map `(K ⊗ᴸ_A A₁) ⊗ᴸ_{A₁} B ⟶ E` is.  Likewise, replacing the corner `A'` of a square by
an isomorphic ring `A'₂` and `K'` by `K' ⊗ᴸ_{A'} A'₂` does not change the invertibility of the
map of Stacks 0DJ7.

## Main results

* `RingTheory.TorIndependence.isIso_ringBaseChangeCohomologyMap_iff_of_iso`
* `RingTheory.TorIndependence.isIso_ringBaseChangeCohomologyMap_iff_localization`
* `RingTheory.TorIndependence.isIso_ringBaseChangeCohomologyMap_target`
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped TensorProduct ChangeOfRings
open CochainComplex.DerivedExtensionScalars StacksDraft.DerivedExtensionScalarsComp

universe u

namespace RingTheory.TorIndependence

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance] Algebra.TensorProduct.rightAlgebra

section Transport

variable {R A R' A' : Type u} [CommRing R] [CommRing A] [CommRing R'] [CommRing A']
  [Algebra R A] [Algebra R R'] [Algebra R A'] [Algebra A A'] [Algebra R' A']
  [IsScalarTower R A A'] [IsScalarTower R R' A']

/-- **The map of Stacks 0DJ7 transports along isomorphisms of the source and of the target.** -/
theorem isIso_ringBaseChangeCohomologyMap_iff_of_iso {K₁ K₂ : DerivedCategory (ModuleCat.{u} A)}
    {K₁' K₂' : DerivedCategory (ModuleCat.{u} A')} (θ : K₁ ≅ K₂) (ψ : K₁' ≅ K₂')
    (φ₁ : (totalDerivedExtensionScalars.{u, u, u} (algebraMap A A')).functor.obj K₁ ⟶ K₁')
    (φ₂ : (totalDerivedExtensionScalars.{u, u, u} (algebraMap A A')).functor.obj K₂ ⟶ K₂')
    (h : (totalDerivedExtensionScalars.{u, u, u} (algebraMap A A')).functor.map θ.hom ≫ φ₂ =
      φ₁ ≫ ψ.hom) (n : ℤ) :
    IsIso (ringBaseChangeCohomologyMap (R := R) (R' := R') K₁ K₁' φ₁ n) ↔
      IsIso (ringBaseChangeCohomologyMap (R := R) (R' := R') K₂ K₂' φ₂ n) :=
  (isIso_choose_ringBaseChangeCohomologyMap_iff K₁ K₁' φ₁ n).symm.trans
    ((isIso_chosenBaseChangeMap_iff_of_iso θ ψ φ₁ φ₂ h n).trans
      (isIso_choose_ringBaseChangeCohomologyMap_iff K₂ K₂' φ₂ n))

omit [Algebra R A'] [IsScalarTower R A A'] [IsScalarTower R R' A'] in
/-- **A morphism out of a derived base change, on complexes.**  Every `φ : K ⊗ᴸ_A A' ⟶ K'` is,
up to isomorphisms `Q N ≅ K` with `N` K-flat and `K' ≅ Q Z`, the class of a map of complexes
`A' ⊗_A N ⟶ Z`. -/
theorem exists_complexDatum (K : DerivedCategory (ModuleCat.{u} A))
    (K' : DerivedCategory (ModuleCat.{u} A'))
    (φ : (totalDerivedExtensionScalars.{u, u, u} (algebraMap A A')).functor.obj K ⟶ K') :
    ∃ (N : CochainComplex (ModuleCat.{u} A) ℤ) (_ : N.KFlat) (e : DerivedCategory.Q.obj N ≅ K)
      (Z : CochainComplex (ModuleCat.{u} A') ℤ) (v : K' ≅ DerivedCategory.Q.obj Z)
      (α : ((ModuleCat.extendScalars (algebraMap A A')).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj N ⟶ Z),
      (totalDerivedExtensionScalars.{u, u, u} (algebraMap A A')).functor.map e.hom ≫ φ ≫ v.hom =
        alphaH A A' N ≫ DerivedCategory.Q.map α := by
  obtain ⟨N, p, hN, -, hp, -⟩ := CochainComplex.KFlat.exists_kFlat_resolution.{u, u}
    (DerivedCategory.Q.objPreimage K)
  have := hp
  let e : DerivedCategory.Q.obj N ≅ K :=
    asIso (DerivedCategory.Q.map p) ≪≫ DerivedCategory.Q.objObjPreimageIso K
  let T := totalDerivedExtensionScalars.{u, u, u} (algebraMap A A')
  have : IsIso (alphaH A A' N) := T.comparison_isIso_of_kFlat N hN
  obtain ⟨Z, α, s, hs, hf⟩ := DerivedCategory.left_fac (inv (alphaH A A' N) ≫ T.functor.map e.hom ≫
    φ ≫ (DerivedCategory.Q.objObjPreimageIso K').inv)
  refine ⟨N, hN, e, Z, (DerivedCategory.Q.objObjPreimageIso K').symm ≪≫
    asIso (DerivedCategory.Q.map s), α, ?_⟩
  have h2 : alphaH A A' N ≫ DerivedCategory.Q.map α = alphaH A A' N ≫
      (inv (alphaH A A' N) ≫ T.functor.map e.hom ≫ φ ≫
        (DerivedCategory.Q.objObjPreimageIso K').inv) ≫ DerivedCategory.Q.map s := by
    rw [hf, Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  rw [h2]
  simp only [Iso.trans_hom, Iso.symm_hom, asIso_hom, Category.assoc, IsIso.hom_inv_id_assoc]
  rfl

end Transport

/-- The comparison `alphaH` and the complex datum `(N, e, Z, v, α)` of `φ` give
`T e⁻¹ ≫ (alphaH ≫ Q α) = φ ≫ v`. -/
private theorem map_inv_comp_alphaH_comp_eq {A A' : Type u} [CommRing A] [CommRing A']
    [Algebra A A'] {K : DerivedCategory (ModuleCat.{u} A)}
    {K' : DerivedCategory (ModuleCat.{u} A')}
    (φ : (totalDerivedExtensionScalars.{u, u, u} (algebraMap A A')).functor.obj K ⟶ K')
    {N : CochainComplex (ModuleCat.{u} A) ℤ} (e : DerivedCategory.Q.obj N ≅ K)
    {Z : CochainComplex (ModuleCat.{u} A') ℤ} (v : K' ≅ DerivedCategory.Q.obj Z)
    {α : ((ModuleCat.extendScalars (algebraMap A A')).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj N ⟶ Z}
    (hα : (totalDerivedExtensionScalars.{u, u, u} (algebraMap A A')).functor.map e.hom ≫ φ ≫
      v.hom = alphaH A A' N ≫ DerivedCategory.Q.map α) :
    (totalDerivedExtensionScalars.{u, u, u} (algebraMap A A')).functor.map e.inv ≫
      alphaH A A' N ≫ DerivedCategory.Q.map α = φ ≫ v.hom := by
  rw [← hα, ← Category.assoc, ← CategoryTheory.Functor.map_comp, Iso.inv_hom_id,
    CategoryTheory.Functor.map_id, Category.id_comp]

section Tower

variable (C D E : Type u) [CommRing C] [CommRing D] [CommRing E] [Algebra C D] [Algebra D E]
  [Algebra C E] [IsScalarTower C D E]

/-- Derived extension of scalars along `C → D` and then along `D → E` is derived extension of
scalars along `C → E`. -/
def derivedTowerIso :
    (totalDerivedExtensionScalars.{u, u, u} (algebraMap C D)).functor ⋙
        (totalDerivedExtensionScalars.{u, u, u} (algebraMap D E)).functor ≅
      (totalDerivedExtensionScalars.{u, u, u} (algebraMap C E)).functor :=
  derivedExtensionScalarsCompIso (algebraMap C D) (algebraMap D E) ≪≫
    eqToIso (congrArg (fun ψ => (totalDerivedExtensionScalars.{u, u, u} ψ).functor)
      (IsScalarTower.algebraMap_eq C D E).symm)

/-- Degreewise extension of scalars along `C → D` and then along `D → E` is degreewise extension
of scalars along `C → E`, `e ⊗ (d ⊗ m) ↦ e d ⊗ m`. -/
def towerComplexMap (N : CochainComplex (ModuleCat.{u} C) ℤ) :
    ((ModuleCat.extendScalars (algebraMap D E)).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (((ModuleCat.extendScalars (algebraMap C D)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj N) ⟶
      ((ModuleCat.extendScalars (algebraMap C E)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj N :=
  (Functor.mapHomologicalComplexCompIso
      (ModuleCat.extendScalarsComp (algebraMap C D) (algebraMap D E)).symm
      (ComplexShape.up ℤ)).hom.app N ≫
    eqToHom (congrArg (fun ψ => ((ModuleCat.extendScalars ψ).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj N) (IsScalarTower.algebraMap_eq C D E).symm)

omit [Algebra C D] [Algebra D E] [Algebra C E] [IsScalarTower C D E] in
/-- For `φ = b.comp a`, the image in the derived category of the degreewise composition
isomorphism of extension of scalars along `a` and `b`, transported to `φ`, is the composition
isomorphism `extensionScalarsComplexCompIso a b` transported to `φ`. -/
theorem extendScalarsComp_tower_eq {a : C →+* D} {b : D →+* E} {φ : C →+* E} (h : φ = b.comp a)
    (N : CochainComplex (ModuleCat.{u} C) ℤ) :
    DerivedCategory.Q.map ((Functor.mapHomologicalComplexCompIso
      (ModuleCat.extendScalarsComp a b).symm (ComplexShape.up ℤ)).hom.app N ≫
        eqToHom (congrArg (fun ψ => ((ModuleCat.extendScalars ψ).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj N) h.symm)) =
      (extensionScalarsComplexCompIso a b).hom.app N ≫
        eqToHom (congrArg (fun ψ => (extensionOfScalarsComplex.{u, u, u} ψ).obj N) h.symm) := by
  subst h
  simp only [eqToHom_refl, Category.comp_id]
  rfl

omit [Algebra C D] [Algebra D E] [Algebra C E] [IsScalarTower C D E] in
/-- For `φ = b.comp a`, the degreewise composition map of extension of scalars along `a` and `b`,
transported to `φ`, sends `1 ⊗ (1 ⊗ m)` to `1 ⊗ m`. -/
theorem extendScalarsComp_tower_apply {a : C →+* D} {b : D →+* E} {φ : C →+* E}
    (h : φ = b.comp a) (N : CochainComplex (ModuleCat.{u} C) ℤ) (i : ℤ) (m : N.X i) :
    (((Functor.mapHomologicalComplexCompIso
      (ModuleCat.extendScalarsComp a b).symm (ComplexShape.up ℤ)).hom.app N ≫
        eqToHom (congrArg (fun ψ => ((ModuleCat.extendScalars ψ).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj N) h.symm)).f i).hom
        ((1 : E) ⊗ₜ[D, b] ((1 : D) ⊗ₜ[C, a] m)) = (1 : E) ⊗ₜ[C, φ] m := by
  subst h
  simp only [eqToHom_refl, Category.comp_id]
  change ((ModuleCat.extendScalarsComp a b).inv.app (N.X i)).hom _ = _
  exact (congrArg (fun x => ((ModuleCat.extendScalarsComp a b).inv.app (N.X i)).hom x)
    (ModuleCat.extendScalarsComp_hom_app_one_tmul a b (N.X i) m).symm).trans
    (congrArg (fun f => f.hom ((1 : E) ⊗ₜ[C, b.comp a] m))
      ((ModuleCat.extendScalarsComp a b).hom_inv_id_app (N.X i)))

/-- `towerComplexMap` sends `1 ⊗ (1 ⊗ m)` to `1 ⊗ m`. -/
theorem towerComplexMap_apply (N : CochainComplex (ModuleCat.{u} C) ℤ) (i : ℤ) (m : N.X i) :
    ((towerComplexMap C D E N).f i).hom
        ((1 : E) ⊗ₜ[D, algebraMap D E] ((1 : D) ⊗ₜ[C, algebraMap C D] m)) =
      (1 : E) ⊗ₜ[C, algebraMap C E] m :=
  extendScalarsComp_tower_apply C D E (IsScalarTower.algebraMap_eq C D E) N i m

/-- Under the comparison maps `alphaH`, the isomorphism `derivedTowerIso` corresponds to
`towerComplexMap`. -/
theorem derivedTowerIso_hom_app_alphaH (N : CochainComplex (ModuleCat.{u} C) ℤ) :
    (derivedTowerIso C D E).hom.app (DerivedCategory.Q.obj N) ≫ alphaH C E N =
      (totalDerivedExtensionScalars.{u, u, u} (algebraMap D E)).functor.map (alphaH C D N) ≫
        alphaH D E _ ≫ DerivedCategory.Q.map (towerComplexMap C D E N) := by
  rw [towerComplexMap, extendScalarsComp_tower_eq C D E (IsScalarTower.algebraMap_eq C D E) N]
  exact derivedExtensionScalarsCompIso_eqToIso_comp_comparison (algebraMap C D) (algebraMap D E)
    (algebraMap C E) (IsScalarTower.algebraMap_eq C D E) N

end Tower

section Localization

variable {R A R' B R₁ A₁ R'₁ : Type u} [CommRing R] [CommRing A] [CommRing R'] [CommRing B]
  [CommRing R₁] [CommRing A₁] [CommRing R'₁]
  [Algebra R A] [Algebra R R'] [Algebra R B] [Algebra A B] [Algebra R' B]
  [IsScalarTower R A B] [IsScalarTower R R' B]
  [Algebra R₁ A₁] [Algebra R₁ R'₁] [Algebra R₁ B] [Algebra A₁ B] [Algebra R'₁ B]
  [IsScalarTower R₁ A₁ B] [IsScalarTower R₁ R'₁ B]
  [Algebra R R₁] [Algebra A A₁] [Algebra R' R'₁] [Algebra R A₁] [Algebra R R'₁]
  [IsScalarTower R A A₁] [IsScalarTower R R₁ A₁] [IsScalarTower A A₁ B] [IsScalarTower R' R'₁ B]
  [IsScalarTower R R₁ R'₁] [IsScalarTower R R' R'₁]

/-- **The map of Stacks 0DJ7 is invariant under localizing the square.**  Let `R₁`, `A₁`, `R'₁`
be localizations of `R`, `A`, `R'` forming with `B` a second square, and let `B` be a
localization both of `A ⊗_R R'` and of `A₁ ⊗_{R₁} R'₁`.  For `ψ : K ⊗ᴸ_A B ⟶ E` the map of Stacks
0DJ7 of the first square at `ψ` is invertible in degree `n` exactly when that of the second
square at `(K ⊗ᴸ_A A₁) ⊗ᴸ_{A₁} B ≅ K ⊗ᴸ_A B ⟶ E` is. -/
theorem isIso_ringBaseChangeCohomologyMap_iff_localization
    (U : Submonoid R) [IsLocalization U R₁] (W : Submonoid A) [IsLocalization W A₁]
    (V : Submonoid R') [IsLocalization V R'₁]
    (hloc : letI := (baseChangeTensorRingMap (R := R) (A := A) (R' := R') (A' := B)).toAlgebra
      ∃ S : Submonoid (A ⊗[R] R'), IsLocalization S B)
    (hloc₁ : letI := (baseChangeTensorRingMap (R := R₁) (A := A₁) (R' := R'₁) (A' := B)).toAlgebra
      ∃ S : Submonoid (A₁ ⊗[R₁] R'₁), IsLocalization S B)
    (K : DerivedCategory (ModuleCat.{u} A)) (E : DerivedCategory (ModuleCat.{u} B))
    (ψ : (totalDerivedExtensionScalars.{u, u, u} (algebraMap A B)).functor.obj K ⟶ E) (n : ℤ) :
    IsIso (ringBaseChangeCohomologyMap (R := R) (R' := R') K E ψ n) ↔
      IsIso (ringBaseChangeCohomologyMap (R := R₁) (R' := R'₁)
        ((totalDerivedExtensionScalars.{u, u, u} (algebraMap A A₁)).functor.obj K) E
        ((derivedTowerIso A A₁ B).hom.app K ≫ ψ) n) := by
  obtain ⟨N, hN, e, Z, v, α, hα⟩ := exists_complexDatum K E ψ
  let T := totalDerivedExtensionScalars.{u, u, u} (algebraMap A A₁)
  let T₁ := totalDerivedExtensionScalars.{u, u, u} (algebraMap A₁ B)
  let T₂ := totalDerivedExtensionScalars.{u, u, u} (algebraMap A B)
  have : IsIso (alphaH A A₁ N) := T.comparison_isIso_of_kFlat N hN
  let N₁ := ((ModuleCat.extendScalars (algebraMap A A₁)).mapHomologicalComplex
    (ComplexShape.up ℤ)).obj N
  let α₁ := towerComplexMap A A₁ B N ≫ α
  have h1 : IsIso (ringBaseChangeCohomologyMap (R := R) (R' := R') K E ψ n) ↔
      IsIso (ringBaseChangeCohomologyMap (R := R) (R' := R') (DerivedCategory.Q.obj N)
        (DerivedCategory.Q.obj Z) (alphaH A B N ≫ DerivedCategory.Q.map α) n) := by
    exact isIso_ringBaseChangeCohomologyMap_iff_of_iso e.symm v ψ _
      (map_inv_comp_alphaH_comp_eq ψ e v hα) n
  have h2 : IsIso (ringBaseChangeCohomologyMap (R := R₁) (R' := R'₁) (T.functor.obj K) E
        ((derivedTowerIso A A₁ B).hom.app K ≫ ψ) n) ↔
      IsIso (ringBaseChangeCohomologyMap (R := R₁) (R' := R'₁) (DerivedCategory.Q.obj N₁)
        (DerivedCategory.Q.obj Z) (alphaH A₁ B N₁ ≫ DerivedCategory.Q.map α₁) n) := by
    refine isIso_ringBaseChangeCohomologyMap_iff_of_iso (R := R₁) (R' := R'₁) (A := A₁) (A' := B)
      (T.functor.mapIso e.symm ≪≫ asIso (alphaH A A₁ N)) v
      ((derivedTowerIso A A₁ B).hom.app K ≫ ψ) (alphaH A₁ B N₁ ≫ DerivedCategory.Q.map α₁) ?_ n
    have hn := (derivedTowerIso A A₁ B).hom.naturality e.hom
    have ht := derivedTowerIso_hom_app_alphaH A A₁ B N
    have hQ : DerivedCategory.Q.map α₁ =
        DerivedCategory.Q.map (towerComplexMap A A₁ B N) ≫ DerivedCategory.Q.map α :=
      DerivedCategory.Q.map_comp _ _
    have hm : T₁.functor.map ((T.functor.mapIso e.symm ≪≫ asIso (alphaH A A₁ N)).hom) =
        T₁.functor.map (T.functor.map e.inv) ≫ T₁.functor.map (alphaH A A₁ N) :=
      T₁.functor.map_comp _ _
    have hinv : T₁.functor.map (T.functor.map e.inv) ≫ T₁.functor.map (T.functor.map e.hom) =
        𝟙 _ := by
      rw [← T₁.functor.map_comp, ← T.functor.map_comp, Iso.inv_hom_id,
        CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]
    calc T₁.functor.map ((T.functor.mapIso e.symm ≪≫ asIso (alphaH A A₁ N)).hom) ≫
          alphaH A₁ B N₁ ≫ DerivedCategory.Q.map α₁
        = T₁.functor.map (T.functor.map e.inv) ≫ ((T₁.functor.map (alphaH A A₁ N) ≫
            alphaH A₁ B N₁ ≫ DerivedCategory.Q.map (towerComplexMap A A₁ B N)) ≫
            DerivedCategory.Q.map α) := by
          rw [hm, hQ]; simp only [Category.assoc]
      _ = T₁.functor.map (T.functor.map e.inv) ≫ (derivedTowerIso A A₁ B).hom.app
            (DerivedCategory.Q.obj N) ≫ alphaH A B N ≫ DerivedCategory.Q.map α := by
          rw [← ht, Category.assoc]
      _ = T₁.functor.map (T.functor.map e.inv) ≫ (derivedTowerIso A A₁ B).hom.app
            (DerivedCategory.Q.obj N) ≫ T₂.functor.map e.hom ≫ ψ ≫ v.hom := by
          rw [← hα]
      _ = T₁.functor.map (T.functor.map e.inv) ≫ (T₁.functor.map (T.functor.map e.hom) ≫
            (derivedTowerIso A A₁ B).hom.app K) ≫ ψ ≫ v.hom := by
          rw [← reassoc_of% hn]; simp only [Category.assoc]; rfl
      _ = ((derivedTowerIso A A₁ B).hom.app K ≫ ψ) ≫ v.hom := by
          simp only [Category.assoc]; rw [reassoc_of% hinv]
  let : Algebra (MvPolynomial R' R) R' :=
    (MvPolynomial.aeval (R := R) (fun x : R' => x)).toRingHom.toAlgebra
  have : IsScalarTower R (MvPolynomial R' R) R' :=
    IsScalarTower.of_algebraMap_eq fun r =>
      ((MvPolynomial.aeval (R := R) (fun x : R' => x)).commutes r).symm
  have hsurj : Function.Surjective (algebraMap (MvPolynomial R' R) R') := fun x =>
    ⟨MvPolynomial.X x, MvPolynomial.aeval_X _ x⟩
  obtain ⟨F, ε, hF, -, hε, -⟩ := CochainComplex.KFlat.exists_kFlat_resolution.{u, u}
    ((CochainComplex.singleFunctor (ModuleCat.{u} (MvPolynomial R' R)) 0).obj
      (ModuleCat.of (MvPolynomial R' R) R'))
  have := hε
  let eN : ((baseChangeFunctor A A₁).mapHomologicalComplex (ComplexShape.up ℤ)).obj N ≅ N₁ :=
    (NatIso.mapHomologicalComplex (baseChangeIsoExtendScalars A A₁) (ComplexShape.up ℤ)).app N
  have hα₁ : ∀ i (m : N.X i), (α₁.f i).hom ((1 : B) ⊗ₜ[A₁, algebraMap A₁ B]
      (eN.hom.f i).hom ((1 : A₁) ⊗ₜ[A] m)) = (α.f i).hom ((1 : B) ⊗ₜ[A, algebraMap A B] m) :=
    fun i m => congrArg (α.f i).hom (towerComplexMap_apply A A₁ B N i m)
  exact h1.trans ((isIso_ringBaseChangeCohomologyMap_iff_isLocalizedModule_units ε hF n hloc hsurj
    N Z α).trans ((isIso_local_iff_isLocalizedModule_modelKappa U W V hsurj ε hF hloc₁ eN α α₁ hα₁
      n).symm.trans h2.symm))

end Localization

section Target

variable {R A R' A' A'₂ : Type u} [CommRing R] [CommRing A] [CommRing R'] [CommRing A']
  [CommRing A'₂]
  [Algebra R A] [Algebra R R'] [Algebra R A'] [Algebra A A'] [Algebra R' A']
  [IsScalarTower R A A'] [IsScalarTower R R' A']
  [Algebra A' A'₂] [Algebra A A'₂] [Algebra R' A'₂] [Algebra R A'₂]
  [IsScalarTower A A' A'₂] [IsScalarTower R' A' A'₂] [IsScalarTower R A A'₂]
  [IsScalarTower R R' A'₂]

omit [Algebra R A'] [IsScalarTower R A A'] [IsScalarTower R R' A'] [Algebra R A'₂]
  [IsScalarTower R A A'₂] [IsScalarTower R R' A'₂] in
/-- Extension of scalars along an isomorphism of rings: the unit `Z ⟶ A'₂ ⊗_{A'} Z` is an
isomorphism. -/
theorem isIso_extendScalars_unit (hτ : Function.Bijective (algebraMap A' A'₂))
    (Z : CochainComplex (ModuleCat.{u} A') ℤ) :
    IsIso ((Adjunction.mapHomologicalComplexAdjunction
      (ModuleCat.extendRestrictScalarsAdj (algebraMap A' A'₂))
        (ComplexShape.up ℤ)).unit.app Z) := by
  let e := RingEquiv.ofBijective (algebraMap A' A'₂) hτ
  have : (ModuleCat.restrictScalars (algebraMap A' A'₂)).IsEquivalence :=
    (ModuleCat.restrictScalarsEquivalenceOfRingEquiv e).isEquivalence_functor
  have : ∀ i, IsIso (((Adjunction.mapHomologicalComplexAdjunction
      (ModuleCat.extendRestrictScalarsAdj (algebraMap A' A'₂)) (ComplexShape.up ℤ)).unit.app Z).f
        i) := fun i =>
    (ModuleCat.extendRestrictScalarsAdj (algebraMap A' A'₂)).isIso_unit_app_of_iso
      ((ModuleCat.restrictScalars (algebraMap A' A'₂)).objObjPreimageIso (Z.X i)).symm
  exact HomologicalComplex.Hom.isIso_of_components _

/-- A ring isomorphic over `A ⊗_R R'` to a localization of `A ⊗_R R'` is one. -/
theorem exists_isLocalization_of_bijective (hτ : Function.Bijective (algebraMap A' A'₂))
    (hloc : letI := (baseChangeTensorRingMap (R := R) (A := A) (R' := R') (A' := A')).toAlgebra
      ∃ S : Submonoid (A ⊗[R] R'), IsLocalization S A') :
    letI := (baseChangeTensorRingMap (R := R) (A := A) (R' := R') (A' := A'₂)).toAlgebra
    ∃ S : Submonoid (A ⊗[R] R'), IsLocalization S A'₂ := by
  let := (baseChangeTensorRingMap (R := R) (A := A) (R' := R') (A' := A')).toAlgebra
  obtain ⟨S, hS⟩ := hloc
  let := (baseChangeTensorRingMap (R := R) (A := A) (R' := R') (A' := A'₂)).toAlgebra
  refine ⟨S, ?_⟩
  let eτ := RingEquiv.ofBijective (algebraMap A' A'₂) hτ
  have hk : ∀ x, eτ (algebraMap (A ⊗[R] R') A' x) = algebraMap (A ⊗[R] R') A'₂ x := fun x =>
    (RingHom.congr_fun (baseChangeTensorRingMap_comp_algebraMap (R := R) (A := A) (R' := R')
      (A' := A') A'₂) x).symm
  exact IsLocalization.isLocalization_of_algEquiv S (AlgEquiv.ofRingEquiv (f := eτ) hk)

/-- **The map of Stacks 0DJ7 under an isomorphism of the corner `A'`.**  For `A' → A'₂` bijective
and `A'` a localization of `A ⊗_R R'`, if the map of Stacks 0DJ7 at `φ : K ⊗ᴸ_A A' ⟶ K'` is
invertible in degree `n`, so is the map of the square `R → A → A'₂ ← R'` at
`K ⊗ᴸ_A A'₂ ≅ (K ⊗ᴸ_A A') ⊗ᴸ_{A'} A'₂ ⟶ K' ⊗ᴸ_{A'} A'₂`. -/
theorem isIso_ringBaseChangeCohomologyMap_target (hτ : Function.Bijective (algebraMap A' A'₂))
    (hloc : letI := (baseChangeTensorRingMap (R := R) (A := A) (R' := R') (A' := A')).toAlgebra
      ∃ S : Submonoid (A ⊗[R] R'), IsLocalization S A')
    (K : DerivedCategory (ModuleCat.{u} A)) (K' : DerivedCategory (ModuleCat.{u} A'))
    (φ : (totalDerivedExtensionScalars.{u, u, u} (algebraMap A A')).functor.obj K ⟶ K') (n : ℤ)
    (hφ : IsIso (ringBaseChangeCohomologyMap (R := R) (R' := R') K K' φ n)) :
    IsIso (ringBaseChangeCohomologyMap (R := R) (R' := R') (A' := A'₂) K
      ((totalDerivedExtensionScalars.{u, u, u} (algebraMap A' A'₂)).functor.obj K')
      ((derivedTowerIso A A' A'₂).inv.app K ≫
        (totalDerivedExtensionScalars.{u, u, u} (algebraMap A' A'₂)).functor.map φ) n) := by
  obtain ⟨N, hN, e, Z, v, α, hα⟩ := exists_complexDatum K K' φ
  let T := totalDerivedExtensionScalars.{u, u, u} (algebraMap A A')
  let Tτ := totalDerivedExtensionScalars.{u, u, u} (algebraMap A' A'₂)
  let T₂ := totalDerivedExtensionScalars.{u, u, u} (algebraMap A A'₂)
  let eτ := RingEquiv.ofBijective (algebraMap A' A'₂) hτ
  have : IsIso Tτ.comparison := isIso_comparison_of_ringEquiv eτ
  have : IsIso (alphaH A' A'₂ Z) := inferInstanceAs (IsIso (Tτ.comparison.app Z))
  let Z₂ := ((ModuleCat.extendScalars (algebraMap A' A'₂)).mapHomologicalComplex
    (ComplexShape.up ℤ)).obj Z
  let τN := towerComplexMap A A' A'₂ N
  have : IsIso τN := by
    dsimp only [τN, towerComplexMap]
    infer_instance
  let α₂ := inv τN ≫ ((ModuleCat.extendScalars (algebraMap A' A'₂)).mapHomologicalComplex
    (ComplexShape.up ℤ)).map α
  have h1 : IsIso (ringBaseChangeCohomologyMap (R := R) (R' := R') K K' φ n) ↔
      IsIso (ringBaseChangeCohomologyMap (R := R) (R' := R') (DerivedCategory.Q.obj N)
        (DerivedCategory.Q.obj Z) (alphaH A A' N ≫ DerivedCategory.Q.map α) n) := by
    exact isIso_ringBaseChangeCohomologyMap_iff_of_iso e.symm v φ _
      (map_inv_comp_alphaH_comp_eq φ e v hα) n
  have h2 : IsIso (ringBaseChangeCohomologyMap (R := R) (R' := R') (A' := A'₂) K
        (Tτ.functor.obj K') ((derivedTowerIso A A' A'₂).inv.app K ≫ Tτ.functor.map φ) n) ↔
      IsIso (ringBaseChangeCohomologyMap (R := R) (R' := R') (A' := A'₂) (DerivedCategory.Q.obj N)
        (DerivedCategory.Q.obj Z₂) (alphaH A A'₂ N ≫ DerivedCategory.Q.map α₂) n) := by
    refine isIso_ringBaseChangeCohomologyMap_iff_of_iso (R := R) (R' := R') (A := A) (A' := A'₂)
      e.symm (Tτ.functor.mapIso v ≪≫ asIso (alphaH A' A'₂ Z))
      ((derivedTowerIso A A' A'₂).inv.app K ≫ Tτ.functor.map φ)
      (alphaH A A'₂ N ≫ DerivedCategory.Q.map α₂) ?_ n
    have hn := (derivedTowerIso A A' A'₂).inv.naturality e.inv
    have ht := derivedTowerIso_hom_app_alphaH A A' A'₂ N
    have hc : Tτ.functor.map (DerivedCategory.Q.map α) ≫ alphaH A' A'₂ Z =
        alphaH A' A'₂ _ ≫ DerivedCategory.Q.map
          (((ModuleCat.extendScalars (algebraMap A' A'₂)).mapHomologicalComplex
            (ComplexShape.up ℤ)).map α) := Tτ.comparison.naturality α
    have hφ' := (map_inv_comp_alphaH_comp_eq φ e v hα).symm
    have hQ : DerivedCategory.Q.map α₂ = inv (DerivedCategory.Q.map τN) ≫
        DerivedCategory.Q.map (((ModuleCat.extendScalars (algebraMap A' A'₂)).mapHomologicalComplex
          (ComplexShape.up ℤ)).map α) := by
      rw [DerivedCategory.Q.map_comp, CategoryTheory.Functor.map_inv]
    have ht' : (derivedTowerIso A A' A'₂).inv.app (DerivedCategory.Q.obj N) ≫
        Tτ.functor.map (alphaH A A' N) ≫ alphaH A' A'₂ _ =
        alphaH A A'₂ N ≫ inv (DerivedCategory.Q.map τN) := by
      rw [← cancel_mono (DerivedCategory.Q.map τN)]
      simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
      rw [← ht, Iso.inv_hom_id_app_assoc]
    have hm : Tτ.functor.map (φ ≫ v.hom) = Tτ.functor.map (T.functor.map e.inv) ≫
        Tτ.functor.map (alphaH A A' N) ≫ Tτ.functor.map (DerivedCategory.Q.map α) := by
      rw [hφ', Tτ.functor.map_comp, Tτ.functor.map_comp]
    have hn' : T₂.functor.map e.inv ≫ (derivedTowerIso A A' A'₂).inv.app (DerivedCategory.Q.obj N) =
        (derivedTowerIso A A' A'₂).inv.app K ≫ Tτ.functor.map (T.functor.map e.inv) := hn
    calc T₂.functor.map e.symm.hom ≫ alphaH A A'₂ N ≫ DerivedCategory.Q.map α₂
        = T₂.functor.map e.inv ≫ (alphaH A A'₂ N ≫ inv (DerivedCategory.Q.map τN)) ≫
            DerivedCategory.Q.map
              (((ModuleCat.extendScalars (algebraMap A' A'₂)).mapHomologicalComplex
                (ComplexShape.up ℤ)).map α) := by
          rw [hQ]; simp only [Iso.symm_hom, Category.assoc]
      _ = (T₂.functor.map e.inv ≫ (derivedTowerIso A A' A'₂).inv.app (DerivedCategory.Q.obj N)) ≫
            Tτ.functor.map (alphaH A A' N) ≫ alphaH A' A'₂ _ ≫
            DerivedCategory.Q.map
              (((ModuleCat.extendScalars (algebraMap A' A'₂)).mapHomologicalComplex
                (ComplexShape.up ℤ)).map α) := by
          rw [← ht']; simp only [Category.assoc]
      _ = ((derivedTowerIso A A' A'₂).inv.app K ≫ Tτ.functor.map (T.functor.map e.inv)) ≫
            Tτ.functor.map (alphaH A A' N) ≫ Tτ.functor.map (DerivedCategory.Q.map α) ≫
            alphaH A' A'₂ Z := by
          rw [hn', hc]
      _ = ((derivedTowerIso A A' A'₂).inv.app K ≫ Tτ.functor.map φ) ≫
            (Tτ.functor.mapIso v ≪≫ asIso (alphaH A' A'₂ Z)).hom := by
          have h3 := congrArg (fun t => (derivedTowerIso A A' A'₂).inv.app K ≫ t ≫
            alphaH A' A'₂ Z) hm
          simp only [CategoryTheory.Functor.map_comp, Category.assoc] at h3
          simp only [Iso.trans_hom, Functor.mapIso_hom, asIso_hom, Category.assoc]
          exact h3.symm
  have hloc₂ := exists_isLocalization_of_bijective (R := R) (A := A) (R' := R') (A' := A') hτ hloc
  let : Algebra (MvPolynomial R' R) R' :=
    (MvPolynomial.aeval (R := R) (fun x : R' => x)).toRingHom.toAlgebra
  have : IsScalarTower R (MvPolynomial R' R) R' :=
    IsScalarTower.of_algebraMap_eq fun r =>
      ((MvPolynomial.aeval (R := R) (fun x : R' => x)).commutes r).symm
  have hsurj : Function.Surjective (algebraMap (MvPolynomial R' R) R') := fun x =>
    ⟨MvPolynomial.X x, MvPolynomial.aeval_X _ x⟩
  obtain ⟨F, ε, hF, -, hε, -⟩ := CochainComplex.KFlat.exists_kFlat_resolution.{u, u}
    ((CochainComplex.singleFunctor (ModuleCat.{u} (MvPolynomial R' R)) 0).obj
      (ModuleCat.of (MvPolynomial R' R) R'))
  have := hε
  let ζ : Z ⟶ ((ModuleCat.restrictScalars (algebraMap A' A'₂)).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj Z₂ :=
    (Adjunction.mapHomologicalComplexAdjunction
      (ModuleCat.extendRestrictScalarsAdj (algebraMap A' A'₂)) (ComplexShape.up ℤ)).unit.app Z
  have : IsIso ζ := isIso_extendScalars_unit hτ Z
  have hinv : ∀ i (m : N.X i), ((inv τN).f i).hom ((1 : A'₂) ⊗ₜ[A, algebraMap A A'₂] m) =
      (1 : A'₂) ⊗ₜ[A', algebraMap A' A'₂] (show (ModuleCat.extendScalars (algebraMap A A')).obj
        (N.X i) from (1 : A') ⊗ₜ[A, algebraMap A A'] m) := fun i m =>
    (congrArg (fun x => ((inv τN).f i).hom x) (towerComplexMap_apply A A' A'₂ N i m).symm).trans
      (congrArg (fun g => (g.f i).hom ((1 : A'₂) ⊗ₜ[A', algebraMap A' A'₂]
        (show (ModuleCat.extendScalars (algebraMap A A')).obj (N.X i) from
          (1 : A') ⊗ₜ[A, algebraMap A A'] m))) (IsIso.hom_inv_id τN))
  have hαζ : ∀ i (m : N.X i), (α₂.f i).hom ((1 : A'₂) ⊗ₜ[A, algebraMap A A'₂] m) =
      (ζ.f i).hom ((α.f i).hom ((1 : A') ⊗ₜ[A, algebraMap A A'] m)) := fun i m =>
    (congrArg (fun x => ((((ModuleCat.extendScalars (algebraMap A' A'₂)).mapHomologicalComplex
      (ComplexShape.up ℤ)).map α).f i).hom x) (hinv i m)).trans
      (ModuleCat.ExtendScalars.map_tmul _ (α.f i) 1 _)
  have hκ := modelKappa_algebra_eq (R := R) (A := A) (R' := R') (A' := A')
    (R₀ := MvPolynomial R' R) ε A'₂ N Z α Z₂ ζ α₂ hαζ
  have hL := (isIso_ringBaseChangeCohomologyMap_iff_isLocalizedModule_units ε hF n hloc hsurj
    N Z α).1 (h1.1 hφ)
  refine h2.2 ((isIso_ringBaseChangeCohomologyMap_iff_isLocalizedModule_units ε hF n hloc₂ hsurj
    N Z₂ α₂).2 ?_)
  have hU : IsLocalizedModule.unitsComap (modelRingMap R A R' A'₂ (MvPolynomial R' R)) =
      IsLocalizedModule.unitsComap (modelRingMap R A R' A' (MvPolynomial R' R)) := by
    ext b
    change IsUnit (modelRingMap R A R' A'₂ (MvPolynomial R' R) b) ↔
      IsUnit (modelRingMap R A R' A' (MvPolynomial R' R) b)
    rw [modelRingMap_apply_of_algebra (R := R) (A := A) (R' := R') (A' := A')
      (R₀ := MvPolynomial R' R) A'₂ b]
    exact MulEquiv.isUnit_map eτ.toMulEquiv
  let μ := modelTargetMap (R := R) (A := A) (R' := R') (A' := A') (R₀ := MvPolynomial R' R) A'₂
    Z Z₂ ζ
  have : IsIso μ := by
    have : ∀ i, IsIso (μ.f i) := fun i => by
      have : IsIso (ζ.f i) := inferInstanceAs (IsIso ((HomologicalComplex.eval _ _ i).map ζ))
      exact (ConcreteCategory.isIso_iff_bijective _).2
        (ConcreteCategory.bijective_of_isIso (ζ.f i))
    exact HomologicalComplex.Hom.isIso_of_components μ
  have hcomp : ((DerivedCategory.homologyFunctor (ModuleCat.{u} (A ⊗[R] MvPolynomial R' R)) n).map
      (DerivedCategory.Q.map (modelKappa (R := R) (A := A) (R' := R') (A' := A'₂)
        (R₀ := MvPolynomial R' R) ε N Z₂ α₂))).hom =
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} (A ⊗[R] MvPolynomial R' R)) n).map
        (DerivedCategory.Q.map μ)).hom ∘ₗ
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} (A ⊗[R] MvPolynomial R' R)) n).map
        (DerivedCategory.Q.map (modelKappa (R := R) (A := A) (R' := R') (A' := A')
          (R₀ := MvPolynomial R' R) ε N Z α))).hom := by
    rw [hκ, DerivedCategory.Q.map_comp, CategoryTheory.Functor.map_comp, ModuleCat.hom_comp]
  rw [hU, hcomp]
  exact (IsLocalizedModule.comp_iff_of_bijective_left _ _
    (ConcreteCategory.bijective_of_isIso _)).2 hL

end Target

/-- A bijective ring map is the localization at the trivial submonoid. -/
theorem isLocalization_bot_of_bijective {C D : Type u} [CommRing C] [CommRing D] [Algebra C D]
    (h : Function.Bijective (algebraMap C D)) : IsLocalization (⊥ : Submonoid C) D :=
  IsLocalization.of_le_isUnit_of_bijective (fun _ ⟨y, hy, hxy⟩ => by
    rw [← hxy, Submonoid.mem_bot.1 hy, map_one]
    exact isUnit_one) h

end RingTheory.TorIndependence
