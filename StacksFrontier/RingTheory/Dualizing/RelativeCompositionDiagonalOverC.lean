module

public import StacksFrontier.Homology.HomComplex.Evaluation.TensorHomRestrictKFlat
public import StacksFrontier.Homology.ExtendScalars.AlongARingIsomorphism
public import StacksFrontier.RingTheory.Dualizing.RelativeCompositionDiagonalSection

/-!
# The tensor--Hom diagonal of `B ⊗[R] B` at the twisting factor of [stacks 0E2H]

Write `C = B ⊗[R] B`, `C' = B ⊗[A] B` and `D = A ⊗[R] A`.  This file proves that the single-ring
tensor--Hom diagonal of `C`

`W ⊗ᴸ_C RHom_C(C', X) ⟶ RHom_C(C', W ⊗ᴸ_C X)`,
`W = K_{B/A} ⊗ᴸ_B C`, `X = (K_{A/R} ⊗ᴸ_A B) ⊗ᴸ_B C`,

is an isomorphism.  None of the criteria of [stacks 0ATK] applies to it over `C`, but `X` and `C'`
are base changes along the flat map `D → C` of a bounded complex and of a bounded above complex of
finite free modules, and `W` is represented by a bounded complex whose restriction to `D` is
K-flat; that is the situation of
`Stacks.DerivedTensorHomDiagonal.isIso_derivedTensorHomDiagonal_of_restrictKFlat`.

## Main results

* `Dualizing.isIso_derivedTensorHomDiagonalOverRing_of_restrictKFlat` -- the criterion, for the
  diagonal `Dualizing.derivedTensorHomDiagonalOverRing`.
-/

@[expose] public section

open CategoryTheory
open CochainComplex.DerivedExtensionScalars
open StacksDraft.DerivedHom
open scoped TensorProduct

universe u

namespace Dualizing

noncomputable section

attribute [local instance] HasDerivedCategory.standard

section Criterion

variable {S C : Type u} [CommRing S] [CommRing C]

/-- **The criterion for `Dualizing.derivedTensorHomDiagonalOverRing`.**  Let `δ : S →+* C` be
flat.  If `K` is represented by a bounded below complex whose restriction to `S` is K-flat, `L` by
the base change of a bounded complex of `S`-modules and `M` by the base change of a bounded above
complex of finite free `S`-modules, then the tensor--Hom diagonal of `D(C)` at `(K, L, M)` is an
isomorphism. -/
theorem isIso_derivedTensorHomDiagonalOverRing_of_restrictKFlat (δ : S →+* C) (hδ : δ.Flat)
    (K L M : DerivedCategory (ModuleCat.{u} C))
    (W : CochainComplex (ModuleCat.{u} C) ℤ) (a : ℤ) [W.IsStrictlyGE a]
    (hW : CochainComplex.KFlat.{u, u} ((CochainComplex.restrictScalarsLarge.{u, u, u} δ).obj W))
    (eK : K ≅ DerivedCategory.Q.obj W)
    (X : CochainComplex (ModuleCat.{u} S) ℤ) (b c : ℤ) [X.IsStrictlyGE b] [X.IsStrictlyLE c]
    (eL : L ≅ DerivedCategory.Q.obj ((CochainComplex.extendScalarsLarge.{u, u, u} δ).obj X))
    (F : CochainComplex (ModuleCat.{u} S) ℤ) (d : ℤ) [F.IsStrictlyLE d]
    [∀ i, Module.Finite S (F.X i)] [∀ i, Module.Free S (F.X i)]
    (eM : M ≅ DerivedCategory.Q.obj ((CochainComplex.extendScalarsLarge.{u, u, u} δ).obj F)) :
    IsIso (derivedTensorHomDiagonalOverRing.{u, u} K L M) := by
  rw [← derivedTensorHomDiagonalModel_eq_overRing.{u, u},
    isIso_derivedTensorHomDiagonalModel_iff.{u, u}]
  let e : ULift.{u} C ≃+* C := ULift.ringEquiv
  let ψ : S →+* ULift.{u} C := e.symm.toRingHom.comp δ
  have hψ : ψ.Flat := RingHom.Flat.comp hδ (RingHom.Flat.of_bijective e.symm.bijective)
  let U := ModuleCat.restrictScalars.{u} e.toRingHom
  let Φ : ModuleCat.extendScalars.{u, u, u} ψ ≅ ModuleCat.extendScalars.{u, u, u} δ ⋙ U :=
    ModuleCat.extendScalarsComp δ e.symm.toRingHom ≪≫
      Functor.isoWhiskerLeft _ (ModuleCat.extendScalarsIsoRestrictScalarsSymm e.symm)
  let tr : ∀ V : CochainComplex (ModuleCat.{u} S) ℤ,
      U.mapDerivedCategory.obj
          (DerivedCategory.Q.obj ((CochainComplex.extendScalarsLarge.{u, u, u} δ).obj V)) ≅
        DerivedCategory.Q.obj ((CochainComplex.extendScalarsLarge.{u, u, u} ψ).obj V) :=
    fun V => U.mapDerivedCategoryFactors.app _ ≪≫
      DerivedCategory.Q.mapIso ((NatIso.mapHomologicalComplex Φ (ComplexShape.up ℤ)).symm.app V)
  let W' := (CochainComplex.restrictScalarsLarge.{u, u, u} e.toRingHom).obj W
  have : W'.IsStrictlyGE a := (CochainComplex.isStrictlyGE_iff _ a).mpr fun i hi =>
    U.map_isZero (W.isZero_of_isStrictlyGE a i hi)
  have hW' : CochainComplex.KFlat.{u, u}
      ((CochainComplex.restrictScalarsLarge.{u, u, u} ψ).obj W') := hW
  have : IsIso (DerivedInternalHom.Model.diagonal (DerivedCategory.Q.obj W')
      (DerivedCategory.Q.obj ((CochainComplex.extendScalarsLarge.{u, u, u} ψ).obj X))
      (DerivedCategory.Q.obj ((CochainComplex.extendScalarsLarge.{u, u, u} ψ).obj F))) :=
    Stacks.DerivedTensorHomDiagonal.isIso_derivedTensorHomDiagonal_of_restrictKFlat ψ hψ
      W' a hW' X b c F d
  let eK' : U.mapDerivedCategory.obj K ≅ DerivedCategory.Q.obj W' :=
    U.mapDerivedCategory.mapIso eK ≪≫ U.mapDerivedCategoryFactors.app W
  exact Stacks.DerivedTensorHomDiagonal.isIso_diagonal_of_iso eK'
    (U.mapDerivedCategory.mapIso eL ≪≫ tr X) (U.mapDerivedCategory.mapIso eM ≪≫ tr F)

end Criterion

section Composite

variable (R A B : Type u) [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra A B] [Algebra R B] [IsScalarTower R A B]
  [Module.Flat R A] [Algebra.FinitePresentation R A]
  [Module.Flat A B] [Algebra.FinitePresentation A B]

/-- **The tensor--Hom diagonal of `C = B ⊗[R] B` at `(K_{B/A} ⊗ᴸ_B C, (K_{A/R} ⊗ᴸ_A B) ⊗ᴸ_B C, C')`
is an isomorphism.**  Here `K_{A/R}` is perfect relative to `R` and `K_{B/A}` perfect relative to
`A`; the internal-Hom source is `C' = B ⊗[A] B`, as the restricted algebra of
`Dualizing.diagonalQuotient`. -/
theorem isIso_derivedTensorHomDiagonalOverRing_diagonalQuotient_composite
    (KA : DerivedCategory (ModuleCat.{u} A)) (KB : DerivedCategory (ModuleCat.{u} B))
    (hKA : PseudoCoherence.IsRelativelyPerfect.{u, u, u}
      (CochainComplex.DerivedTensor.canonicalDerivedTensorProduct R).tensor
      (StacksDraft.TorAmplitude.canonicalTensorComparison R)
      (StacksDraft.TorAmplitude.canonicalTensorIsLeftDerived R) KA)
    (hKB : PseudoCoherence.IsRelativelyPerfect.{u, u, u}
      (CochainComplex.DerivedTensor.canonicalDerivedTensorProduct A).tensor
      (StacksDraft.TorAmplitude.canonicalTensorComparison A)
      (StacksDraft.TorAmplitude.canonicalTensorIsLeftDerived A) KB) :
    letI : Module.Flat R B := Module.Flat.trans R A B
    IsIso (derivedTensorHomDiagonalOverRing.{u, u}
        ((diagonalDerivedExtension R B).obj KB)
        ((diagonalDerivedExtension R B).obj
          ((totalDerivedExtensionScalars.{u, u, u} (algebraMap A B)).functor.obj KA))
        (ProjectionFormula.restrictedAlgebra.{u, u}
          (ModuleCat.restrictScalars.{u}
            (diagonalQuotient R A B).toRingHom).mapDerivedCategory)) := by
  let : Module.Flat R B := Module.Flat.trans R A B
  set δ : (A ⊗[R] A) →+* B ⊗[R] B := (diagonalBaseMap R A B).toRingHom
  have hδ : δ.Flat := flat_diagonalBaseMap R A B
  set p : B →+* B ⊗[R] B := Algebra.TensorProduct.includeLeftRingHom
  set pA : A →+* A ⊗[R] A := Algebra.TensorProduct.includeLeftRingHom
  obtain ⟨Q, a, b, hQGE, hQLE, hQflat, -, ⟨eQ⟩⟩ :=
    (PseudoCoherence.isRelativelyPerfect_iff_exists_bounded_flat_finitePresentation.{u, u, u}
      _ _ _ KB).1 hKB
  have := hQGE
  have := hQLE
  let Wc := (CochainComplex.extendScalars p).obj Q
  have : Wc.IsStrictlyGE a := Stacks.DerivedTensorHomDiagonal.isStrictlyGE_extendScalars p Q a
  let E := (CochainComplex.restrictScalarsLarge.{u, u, u} δ).obj Wc
  have : ∀ n : ℤ, Module.Flat (A ⊗[R] A) (E.X n) := fun n =>
    flat_restrictScalars_diagonalExtendScalars R A B (Q.X n) (hQflat n)
  have : E.IsStrictlyLE b := (CochainComplex.isStrictlyLE_iff E b).mpr fun i hi =>
    (ModuleCat.restrictScalars δ).map_isZero
      ((ModuleCat.extendScalars p).map_isZero (Q.isZero_of_isStrictlyLE b i hi))
  obtain ⟨Pa, c₀, c₁, hPGE, hPLE, -, -, ⟨eP⟩⟩ :=
    (PseudoCoherence.isRelativelyPerfect_iff_exists_bounded_flat_finitePresentation.{u, u, u}
      _ _ _ KA).1 hKA
  have := hPGE
  have := hPLE
  let XD := (CochainComplex.extendScalars pA).obj Pa
  have : XD.IsStrictlyGE c₀ := Stacks.DerivedTensorHomDiagonal.isStrictlyGE_extendScalars pA Pa c₀
  have : XD.IsStrictlyLE c₁ :=
    Stacks.DerivedTensorHomDiagonal.isStrictlyLE_extendScalarsLarge pA Pa c₁
  let := (preservesFiniteLimits_extendScalars_of_flat δ hδ).1
  let := (preservesFiniteLimits_extendScalars_of_flat δ hδ).2
  let flatQ : ∀ V : CochainComplex (ModuleCat.{u} (A ⊗[R] A)) ℤ,
      (totalDerivedExtensionScalars.{u, u, u} δ).functor.obj (DerivedCategory.Q.obj V) ≅
        DerivedCategory.Q.obj ((CochainComplex.extendScalarsLarge.{u, u, u} δ).obj V) :=
    fun V => (totalDerivedExtensionScalarsIsoOfFlat δ hδ).app _ ≪≫
      (ModuleCat.extendScalars.{u, u, u} δ).mapDerivedCategoryFactors.app V
  obtain ⟨eX⟩ := diagonalDerivedExtensionBaseChangeIso R A B KA
  let eL := eX.symm ≪≫ (totalDerivedExtensionScalars.{u, u, u} δ).functor.mapIso
      (diagonalDerivedExtensionIso R A KA Pa eP.symm) ≪≫ flatQ XD
  obtain ⟨F, hF, ⟨eF⟩⟩ := isPseudoCoherent_diagonal R A
  obtain ⟨d, hd⟩ := hF.upperBound
  have := hd
  have : ∀ i, Module.Finite (A ⊗[R] A) (F.X i) := fun i => (hF.finiteFree i).1
  have : ∀ i, Module.Free (A ⊗[R] A) (F.X i) := fun i => (hF.finiteFree i).2
  let := diagonalAlgebra R A B
  let := diagonalAlgebraSelf R A
  let := diagonalQuotientAlgebra R A B
  let := diagonalAlgebraQuot R A B
  let := diagonalIsScalarTowerSelf R A B
  obtain ⟨eS⟩ := diagonalDerivedExtensionSingleIso R A B
  let i := (diagonalQuotient R A B).toRingHom
  let ra : ProjectionFormula.restrictedAlgebra.{u, u}
        (ModuleCat.restrictScalars.{u} i).mapDerivedCategory ≅
      (DerivedCategory.singleFunctor (ModuleCat.{u} (B ⊗[R] B)) 0).obj
        (ModuleCat.of (B ⊗[R] B) (B ⊗[A] B)) :=
    (ModuleCat.restrictScalars.{u} i).mapDerivedCategory.mapIso
        (derivedTensorUnitIsoSingleSelf (B ⊗[A] B)) ≪≫
      ((ModuleCat.restrictScalars.{u} i).mapDerivedCategorySingleFunctor 0).app _
  let eA : DerivedCategory.Q.obj F ≅
      (DerivedCategory.singleFunctor (ModuleCat.{u} (A ⊗[R] A)) 0).obj
        (ModuleCat.of (A ⊗[R] A) A) :=
    eF ≪≫ ((ModuleCat.restrictScalars.{u}
      (Algebra.TensorProduct.lmul' R : A ⊗[R] A →ₐ[R] A).toRingHom).mapDerivedCategorySingleFunctor
        0).app _
  let eM := ra ≪≫ eS.symm ≪≫ (totalDerivedExtensionScalars.{u, u, u} δ).functor.mapIso eA.symm ≪≫
    flatQ F
  exact isIso_derivedTensorHomDiagonalOverRing_of_restrictKFlat δ hδ _ _ _ Wc a
    (CochainComplex.KFlat.kFlat_of_flat.{u, u} E b) (diagonalDerivedExtensionIso R B KB Q eQ.symm)
    XD c₀ c₁ eL F d eM

end Composite

end

end Dualizing

end
