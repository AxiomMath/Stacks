module

public import StacksFrontier.Homology.KFlat.Resolution
public import StacksFrontier.Homology.Tor.DerivedChangeOfRings
public import StacksFrontier.Homology.TorAmplitude.CanonicalCertificate
public import StacksFrontier.Homology.TorAmplitude.Comparison
public import StacksFrontier.RingTheory.Module.AdicSystem.IdealPowerTensor
public import StacksFrontier.Homology.PseudoCoherent.Relative.PolynomialRetract
public import StacksFrontier.Homology.TwoTermComplex.BaseChange

@[expose] public noncomputable section

/-!
# Scalar compatibility of a certified derived tensor product

Tensoring the termwise multiplication map `K ⊗ J ⟶ K` induced by `j : J ⟶ R` with a module `N`
annihilated by the image of `j` gives the zero morphism of `D(R)`.

This holds for every derived tensor product certified in the sense of
`DerivedTensorData.DerivedTensorProduct` — in particular for the canonical derived tensor
product of Stacks 0BYI with the canonical comparison of
`StacksDraft.TorAmplitude.canonicalTensorComparison`. It is the annihilation consequence of
associativity used in the ideal-power argument of tag 0FXN, and it needs only the comparison
maps and their universal property, not the shift or triangulated structures.
-/

open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Functor

namespace StacksDraft.ScalarCompat

universe u

attribute [local instance] HasDerivedCategory.standard

variable {R : Type u} [CommRing R]

/-! ### The comparison map is invertible on K-flat complexes

This is the generic statement behind `StacksDraft.TorAmplitude`'s private
`tensorModuleComparison_isIso`: it needs only the universal property, not the particular
construction of the comparison. -/

/-- The counit of a total left derived functor of termwise tensoring by a module is invertible
on K-flat complexes. -/
theorem isIso_comparison_app_of_kFlat (N : ModuleCat.{u} R)
    (L : DerivedCategory (ModuleCat.{u} R) ⥤ DerivedCategory (ModuleCat.{u} R))
    (α : DerivedCategory.Q ⋙ L ⟶ PseudoCoherence.tensorRightComplexToDerived N)
    (hα : L.IsLeftDerivedFunctor α
      (HomologicalComplex.quasiIso (ModuleCat.{u} R) (ComplexShape.up ℤ)))
    (P : CochainComplex (ModuleCat.{u} R) ℤ) (hP : P.KFlat) :
    IsIso (α.app P) := by
  have := hα
  let T := TorAmplitude.tensorModuleRight N
  let Uh := T.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh
  let e : HomotopyCategory.quotient (ModuleCat.{u} R) (ComplexShape.up ℤ) ⋙ Uh ≅
      T.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q :=
    (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (T.mapHomotopyCategoryFactors (ComplexShape.up ℤ))
        DerivedCategory.Qh ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft (T.mapHomologicalComplex (ComplexShape.up ℤ))
        (DerivedCategory.quotientCompQhIso _)
  refine CochainComplex.DerivedTensor.KFlatDerived.isIso_app_of_kFlat.{u, u} _ Uh e ?_ _ α P hP
  intro X Y s hs hX hY
  have : QuasiIso s.out := (HomotopyCategory.quotient_map_mem_quasiIso_iff s.out).1 (by
    rw [HomotopyCategory.quotient_map_out s]
    exact hs)
  have : QuasiIso ((T.mapHomologicalComplex (ComplexShape.up ℤ)).map s.out) :=
    StacksDraft.TorAmplitude.quasiIso_tensorModuleRight_map N s.out hX hY
  have : IsIso ((T.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q).map s.out) := by
    dsimp
    infer_instance
  have hi : IsIso ((HomotopyCategory.quotient (ModuleCat.{u} R) (ComplexShape.up ℤ) ⋙ Uh).map
      s.out) := by
    rw [← NatIso.naturality_2 e s.out]
    dsimp
    infer_instance
  rw [← HomotopyCategory.quotient_map_out s]
  exact hi

/-! ### The termwise multiplication map -/

variable (J : ModuleCat.{u} R) (j : J ⟶ 𝟙_ (ModuleCat.{u} R))

/-- `DerivedTensorData.tensorRightUnitMapComplex`, with its source named as the value of
`TorAmplitude.tensorModuleRight`, so that tactics see the same spelling the comparison maps of
`DerivedTensorData.DerivedTensorProduct` take their values in. -/
def unitMapComplex (K : CochainComplex (ModuleCat.{u} R) ℤ) :
    ((TorAmplitude.tensorModuleRight J).mapHomologicalComplex (ComplexShape.up ℤ)).obj K ⟶
      K :=
  DerivedTensorData.tensorRightUnitMapComplex K J j

/-- The components of `unitMapComplex` are the multiplication `x ⊗ y ↦ j y • x`. -/
lemma unitMapComplex_f_apply (K : CochainComplex (ModuleCat.{u} R) ℤ) (i : ℤ)
    (x : K.X i) (y : J) :
    ModuleCat.Hom.hom ((unitMapComplex J j K).f i) (x ⊗ₜ[R] y) = (j.hom y : R) • x :=
  rfl

/-- The hypothesis of `tensor_unitMap_zero` says exactly that the scalars in the image of `j`
annihilate `N`. -/
lemma smul_eq_zero_of_unitMap (N : ModuleCat.{u} R)
    (h : ((tensoringRight (ModuleCat.{u} R)).obj N).map j ≫
      (MonoidalCategory.leftUnitor N).hom = 0) (y : J) (n : N) :
    (j.hom y : R) • n = 0 := by
  have key : ModuleCat.Hom.hom (((tensoringRight (ModuleCat.{u} R)).obj N).map j ≫
      (MonoidalCategory.leftUnitor N).hom) (y ⊗ₜ[R] n) = 0 := by
    rw [h]
    rfl
  exact key

/-- The module-level computation behind the vanishing: a multiplication map by scalars
annihilating `N`, tensored with `N`, is zero. -/
lemma tensorModuleRight_map_eq_zero (N : ModuleCat.{u} R)
    (hz : ∀ (y : J) (n : N), (j.hom y : R) • n = 0) (X : ModuleCat.{u} R)
    (f : ModuleCat.of R (TensorProduct R X J) ⟶ X)
    (hf : ∀ (x : X) (y : J), f.hom (x ⊗ₜ[R] y) = (j.hom y : R) • x) :
    ModuleCat.ofHom (f.hom.rTensor N) = 0 := by
  apply ModuleCat.hom_ext
  apply TensorProduct.ext_threefold
  intro x y n
  change f.hom.rTensor N ((x ⊗ₜ[R] y) ⊗ₜ[R] n) = (0 : _ →ₗ[R] _) ((x ⊗ₜ[R] y) ⊗ₜ[R] n)
  rw [LinearMap.rTensor_tmul, hf x y, TensorProduct.smul_tmul, hz y n, TensorProduct.tmul_zero,
    LinearMap.zero_apply]

/-- The module-level computation behind the naturality of the multiplication map. -/
lemma mul_naturality_aux {X Y : ModuleCat.{u} R} (g : X ⟶ Y)
    (fX : ModuleCat.of R (TensorProduct R X J) ⟶ X)
    (fY : ModuleCat.of R (TensorProduct R Y J) ⟶ Y)
    (hX : ∀ (x : X) (y : J), fX.hom (x ⊗ₜ[R] y) = (j.hom y : R) • x)
    (hY : ∀ (x : Y) (y : J), fY.hom (x ⊗ₜ[R] y) = (j.hom y : R) • x) :
    ModuleCat.ofHom (g.hom.rTensor J) ≫ fY = fX ≫ g := by
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro x y
  change fY.hom (g.hom.rTensor J (x ⊗ₜ[R] y)) = g.hom (fX.hom (x ⊗ₜ[R] y))
  rw [LinearMap.rTensor_tmul, hY (g.hom x) y, hX x y, _root_.map_smul]

/-- Tensoring the termwise multiplication map with a module annihilated by the image of `j`
gives the zero map of complexes. -/
lemma mapHomologicalComplex_unitMapComplex_eq_zero
    (K : CochainComplex (ModuleCat.{u} R) ℤ) (N : ModuleCat.{u} R)
    (h : ((tensoringRight (ModuleCat.{u} R)).obj N).map j ≫
      (MonoidalCategory.leftUnitor N).hom = 0) :
    ((TorAmplitude.tensorModuleRight N).mapHomologicalComplex
        (ComplexShape.up ℤ)).map (unitMapComplex J j K) = 0 := by
  apply HomologicalComplex.hom_ext
  intro i
  rw [HomologicalComplex.zero_f]
  exact tensorModuleRight_map_eq_zero J j N (smul_eq_zero_of_unitMap J j N h) (K.X i)
    ((unitMapComplex J j K).f i) (unitMapComplex_f_apply J j K i)

/-- The termwise multiplication map is natural in the complex. -/
lemma unitMapComplex_naturality {P K : CochainComplex (ModuleCat.{u} R) ℤ} (π : P ⟶ K) :
    ((TorAmplitude.tensorModuleRight J).mapHomologicalComplex (ComplexShape.up ℤ)).map π ≫
        unitMapComplex J j K =
      unitMapComplex J j P ≫ π := by
  apply HomologicalComplex.hom_ext
  intro i
  exact mul_naturality_aux J j (π.f i) ((unitMapComplex J j P).f i)
    ((unitMapComplex J j K).f i) (unitMapComplex_f_apply J j P i) (unitMapComplex_f_apply J j K i)

/-- The localization of the termwise multiplication map, with its source named as the value of
`tensorRightComplexToDerived` so that composites with a comparison map are syntactically
well typed. -/
def unitMapDerived (K : CochainComplex (ModuleCat.{u} R) ℤ) :
    (PseudoCoherence.tensorRightComplexToDerived J).obj K ⟶ DerivedCategory.Q.obj K :=
  DerivedCategory.Q.map (unitMapComplex J j K)

/-! ### The vanishing, for an arbitrary certified derived tensor product -/

variable (D : DerivedCategory (ModuleCat.{u} R) ⥤ DerivedCategory (ModuleCat.{u} R) ⥤
  DerivedCategory (ModuleCat.{u} R))

/-- Before the comparison for `N` is inverted, tensoring with a module `N` annihilated by the
image of `j` kills the "multiply by `j`" map. -/
lemma map_comparison_comp_unitMapDerived_comp_eq_zero (N : ModuleCat.{u} R)
    (cmpJ : DerivedCategory.Q ⋙
        D.flip.obj ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj J) ⟶
      PseudoCoherence.tensorRightComplexToDerived J)
    (cmpN : DerivedCategory.Q ⋙
        D.flip.obj ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj N) ⟶
      PseudoCoherence.tensorRightComplexToDerived N)
    (h : ((tensoringRight (ModuleCat.{u} R)).obj N).map j ≫
      (MonoidalCategory.leftUnitor N).hom = 0) (X : CochainComplex (ModuleCat.{u} R) ℤ) :
    (D.flip.obj ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj N)).map
        (cmpJ.app X ≫ unitMapDerived J j X) ≫ cmpN.app X = 0 := by
  have hzero : (PseudoCoherence.tensorRightComplexToDerived N).map
      (unitMapComplex J j X) = 0 := by
    simp only [Functor.comp_map, mapHomologicalComplex_unitMapComplex_eq_zero J j X N h,
      Functor.map_zero]
  have hstep : (D.flip.obj ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj N)).map
      (unitMapDerived J j X) ≫ cmpN.app X = 0 := by
    have hnat := cmpN.naturality (unitMapComplex J j X)
    rwa [hzero, Limits.comp_zero] at hnat
  rw [Functor.map_comp, Category.assoc, hstep, Limits.comp_zero]

/-- The comparison followed by the "multiply by `j`" map is natural in the complex. -/
lemma comparison_comp_unitMapDerived_naturality
    (cmpJ : DerivedCategory.Q ⋙
        D.flip.obj ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj J) ⟶
      PseudoCoherence.tensorRightComplexToDerived J)
    {P K : CochainComplex (ModuleCat.{u} R) ℤ} (π : P ⟶ K) :
    (D.flip.obj ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj J)).map
        (DerivedCategory.Q.map π) ≫ (cmpJ.app K ≫ unitMapDerived J j K) =
      (cmpJ.app P ≫ unitMapDerived J j P) ≫ DerivedCategory.Q.map π := by
  have hnatJ : (D.flip.obj ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj J)).map
        (DerivedCategory.Q.map π) ≫ cmpJ.app K =
      cmpJ.app P ≫ (PseudoCoherence.tensorRightComplexToDerived J).map π :=
    cmpJ.naturality π
  have hunit : (PseudoCoherence.tensorRightComplexToDerived J).map π ≫
      unitMapDerived J j K = unitMapDerived J j P ≫ DerivedCategory.Q.map π := by
    simp only [unitMapDerived, Functor.comp_map, ← Functor.map_comp, unitMapComplex_naturality]
  rw [← Category.assoc, hnatJ, Category.assoc, hunit, Category.assoc]

/-- **(★)** For any derived tensor bifunctor certified by a comparison with termwise tensoring
together with the total-left-derived universal property, tensoring on the right with a module
`N` annihilated by the image of `j : J ⟶ R` kills the "multiply by `j`" map
`K ⊗ᴸ J ⟶ Q (K ⊗ J) ⟶ Q K`. -/
theorem map_comparison_comp_unitMap_eq_zero
    (cmp : ∀ M : ModuleCat.{u} R,
      DerivedCategory.Q ⋙
          D.flip.obj ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj M) ⟶
        PseudoCoherence.tensorRightComplexToDerived M)
    (hcmp : ∀ M : ModuleCat.{u} R,
      (D.flip.obj
        ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj M)).IsLeftDerivedFunctor
          (cmp M) (HomologicalComplex.quasiIso (ModuleCat.{u} R) (ComplexShape.up ℤ)))
    (K : CochainComplex (ModuleCat.{u} R) ℤ) (N : ModuleCat.{u} R)
    (h : ((tensoringRight (ModuleCat.{u} R)).obj N).map j ≫
      (MonoidalCategory.leftUnitor N).hom = 0) :
    (D.flip.obj ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj N)).map
        ((cmp J).app K ≫ unitMapDerived J j K) = 0 := by
  obtain ⟨P, π, hP, -, hπ, -⟩ := CochainComplex.KFlat.exists_kFlat_resolution.{u, u} K
  have hisoN : IsIso ((cmp N).app P) :=
    isIso_comparison_app_of_kFlat N _ (cmp N) (hcmp N) P hP
  have hzP : (D.flip.obj ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj N)).map
      ((cmp J).app P ≫ unitMapDerived J j P) = 0 := by
    rw [← cancel_mono ((cmp N).app P), Limits.zero_comp]
    exact map_comparison_comp_unitMapDerived_comp_eq_zero J j D N (cmp J) (cmp N) h P
  have : IsIso (DerivedCategory.Q.map π) := by
    have := hπ
    infer_instance
  rw [← cancel_epi ((D.flip.obj
      ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj N)).map
    ((D.flip.obj ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj J)).map
      (DerivedCategory.Q.map π))), Limits.comp_zero, ← Functor.map_comp,
    comparison_comp_unitMapDerived_naturality J j D (cmp J) π, Functor.map_comp, hzP,
    Limits.zero_comp]

/-! ### The field `tensor_unitMap_zero` -/

/-- **Scalar annihilation, for a bifunctor with an arbitrary certifying comparison.** The
quantified symmetry isomorphism plays no role: the morphism it contributes is precomposed, and a
functor sends a composite ending in a zero morphism to zero. -/
theorem tensor_unitMap_zero_of_certified
    (cmp : ∀ M : ModuleCat.{u} R,
      DerivedCategory.Q ⋙
          D.flip.obj ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj M) ⟶
        PseudoCoherence.tensorRightComplexToDerived M)
    (hcmp : ∀ M : ModuleCat.{u} R,
      (D.flip.obj
        ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj M)).IsLeftDerivedFunctor
          (cmp M) (HomologicalComplex.quasiIso (ModuleCat.{u} R) (ComplexShape.up ℤ)))
    (symmetry : D ≅ D.flip)
    (K : CochainComplex (ModuleCat.{u} R) ℤ) (N : ModuleCat.{u} R)
    (h : ((tensoringRight (ModuleCat.{u} R)).obj N).map j ≫
      (MonoidalCategory.leftUnitor N).hom = 0) :
    (D.flip.obj ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj N)).map
        ((symmetry.hom.app
            ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj J)).app
              (DerivedCategory.Q.obj K) ≫
          (cmp J).app K ≫
          DerivedCategory.Q.map (DerivedTensorData.tensorRightUnitMapComplex K J j)) = 0 :=
  (Functor.map_comp _ _ _).trans
    ((congrArg _ (map_comparison_comp_unitMap_eq_zero J j D cmp hcmp K N h)).trans
      Limits.comp_zero)

/-- Scalar annihilation for every derived tensor product certified in the sense of
`DerivedTensorData.DerivedTensorProduct`: tensoring the multiplication by `j` with a module
annihilated by the image of `j` gives the zero morphism. -/
theorem tensor_unitMap_zero (T : DerivedTensorData.DerivedTensorProduct.{u, u} R)
    (symmetry : T.tensor ≅ T.tensor.flip)
    (K : CochainComplex (ModuleCat.{u} R) ℤ) (N : ModuleCat.{u} R)
    (h : ((tensoringRight (ModuleCat.{u} R)).obj N).map j ≫
      (MonoidalCategory.leftUnitor N).hom = 0) :
    (T.tensor.flip.obj ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj N)).map
        ((symmetry.hom.app
            ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj J)).app
              (DerivedCategory.Q.obj K) ≫
          (T.comparison J).app K ≫
          DerivedCategory.Q.map (DerivedTensorData.tensorRightUnitMapComplex K J j)) = 0 :=
  tensor_unitMap_zero_of_certified J j T.tensor T.comparison T.isLeftDerived symmetry K N h

/-- **The field `tensor_unitMap_zero` for the canonical derived tensor product of Stacks 0BYI,
with the canonical comparison `StacksDraft.TorAmplitude.canonicalTensorComparison`.** -/
theorem canonical_tensor_unitMap_zero (A : Type u) [CommRing A]
    (symmetry : (CochainComplex.DerivedTensor.canonicalDerivedTensorProduct A).tensor ≅
      (CochainComplex.DerivedTensor.canonicalDerivedTensorProduct A).tensor.flip)
    (K : CochainComplex (ModuleCat.{u} A) ℤ) (J N : ModuleCat.{u} A)
    (j : J ⟶ 𝟙_ (ModuleCat.{u} A))
    (h : ((tensoringRight (ModuleCat.{u} A)).obj N).map j ≫
      (MonoidalCategory.leftUnitor N).hom = 0) :
    ((CochainComplex.DerivedTensor.canonicalDerivedTensorProduct A).tensor.flip.obj
        ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj N)).map
        ((symmetry.hom.app
            ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj J)).app
              (DerivedCategory.Q.obj K) ≫
          (StacksDraft.TorAmplitude.canonicalTensorComparison A J).app K ≫
          DerivedCategory.Q.map (DerivedTensorData.tensorRightUnitMapComplex K J j)) = 0 :=
  tensor_unitMap_zero_of_certified J j
    (CochainComplex.DerivedTensor.canonicalDerivedTensorProduct A).tensor
    (StacksDraft.TorAmplitude.canonicalTensorComparison A)
    (StacksDraft.TorAmplitude.canonicalTensorIsLeftDerived A) symmetry K N h

end StacksDraft.ScalarCompat

end
