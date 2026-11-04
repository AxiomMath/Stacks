module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.CategoryTheory.Presentable.Directed
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Meromorphic.NoEmbeddedPoints
public import StacksFrontier.AlgebraicGeometry.Morphisms.Normalization.LocalPresentation
public import StacksFrontier.RingTheory.Henselian.HenselizationMinimalPrimes
public import StacksFrontier.RingTheory.Henselian.StrictHenselization.BaseChange
public import StacksFrontier.RingTheory.IntegralClosure.BaseChange

/-!
# Normalization after henselization

Let `X` be a locally Noetherian scheme and `x` a point of `X`. The base change of the
normalization morphism of `X` along the spectrum of a henselization, or of a strict
henselization, of the local ring `𝒪_{X, x}` is the normalization morphism of that spectrum.

## Main results

* `AlgebraicGeometry.normalization_baseChange_isHenselization`: the statement for an arbitrary
  henselization in the sense of `IsLocalRing.IsHenselization`.
* `AlgebraicGeometry.normalization_baseChange_henselization`: the case of the henselization.
* `AlgebraicGeometry.normalization_baseChange_strictHenselization`: the case of a strict
  henselization.
* `AlgebraicGeometry.toIntegralClosure_bijective_of_isHenselization`: base change to a
  henselization commutes with integral closure.
* `AlgebraicGeometry.pullback_baseChange_spec`: an identification of the base change of a
  morphism to `Spec A` with `Spec N` gives, for any `A`-algebra `B`, an identification of the base
  change to `Spec B` with `Spec (B ⊗[A] N)`.

## References

* [Stacks Project, Tag 0CBM](https://stacks.math.columbia.edu/tag/0CBM)
* [Stacks Project, Tag 0CBF](https://stacks.math.columbia.edu/tag/0CBF)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open IsLocalRing
open scoped TensorProduct

universe u v

namespace AlgebraicGeometry

/-- A henselization transported along an isomorphism of algebras is again a henselization. -/
private theorem isHenselization_of_algEquiv {A B C : Type u} [CommRing A] [IsLocalRing A]
    [CommRing B] [IsLocalRing B] [Algebra A B] [CommRing C] [IsLocalRing C] [Algebra A C]
    (L : Type v) [Field L] [Algebra (ResidueField A) L] [IsHenselization A L B] (e : B ≃ₐ[A] C) :
    IsHenselization A L C := by
  let : HenselianLocalRing B := IsHenselization.henselian (R := A) (L := L) (Rh := B)
  obtain ⟨a, ha⟩ := IsHenselization.exists_residueFieldEquiv (R := A) (L := L) (Rh := B)
  apply IsHenselization.of_ind_etale.{u, v} (HenselianLocalRing.of_ringEquiv e.toRingEquiv)
    ((CommAlgCat.etale A).ind.prop_of_iso (CommAlgCat.isoMk e)
      (IsHenselization.ind_etale_of_universe_le.{u, v} L))
  refine ⟨a.trans (ResidueField.mapEquiv e.toRingEquiv), fun r => ?_⟩
  show ResidueField.map (e : B →+* C) (a _) = _
  rw [ha, ResidueField.map_residue]
  exact congrArg (residue C) (e.commutes r)

/-- Pulling back a morphism `ν` along `Spec B → Spec A → X`, where the base change of `ν` to
`Spec A` is `Spec N` over `Spec A`, gives `Spec (B ⊗[A] N)` over `Spec B`. -/
public theorem pullback_baseChange_spec {A B N : Type u} [CommRing A] [CommRing B] [CommRing N]
    [Algebra A B] [Algebra A N] {X Y : Scheme.{u}} (ν : Y ⟶ X) (f : Spec (.of A) ⟶ X)
    (e : pullback ν f ≅ Spec (.of N))
    (he : e.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap A N)) = pullback.snd ν f) :
    Nonempty (Over.mk (pullback.snd ν (Spec.map (CommRingCat.ofHom (algebraMap A B)) ≫ f)) ≅
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap B (B ⊗[A] N))))) := by
  let g : Spec (.of B) ⟶ Spec (.of A) := Spec.map (CommRingCat.ofHom (algebraMap A B))
  let e' : pullback f ν ≅ Spec (.of N) := (pullbackSymmetry f ν).trans e
  have he' : e'.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap A N)) = pullback.fst f ν := by
    dsimp [e']
    rw [Category.assoc, he, pullbackSymmetry_hom_comp_snd]
  let m : pullback g (pullback.fst f ν) ⟶
      pullback g (Spec.map (CommRingCat.ofHom (algebraMap A N))) :=
    pullback.map g (pullback.fst f ν) g (Spec.map (CommRingCat.ofHom (algebraMap A N)))
      (𝟙 _) e'.hom (𝟙 _) (by simp) he'.symm
  have hm : IsIso m := by
    dsimp only [m]
    exact pullback.map_isIso ..
  let toTarget := pullbackRightPullbackFstIso f ν g ≪≫ pullbackSymmetry (g ≫ f) ν
  let toTensor := asIso m ≪≫ pullbackSpecIso A B N
  let totalIso := toTarget.symm ≪≫ toTensor
  have hm_fst : m ≫ pullback.fst g (Spec.map (CommRingCat.ofHom (algebraMap A N))) =
      pullback.fst g (pullback.fst f ν) := by
    dsimp [m, pullback.map]
    rw [pullback.lift_fst]
    simp
  have hright : toTarget.hom ≫ pullback.snd ν (g ≫ f) =
      pullback.fst g (pullback.fst f ν) := by
    dsimp [toTarget]
    simp [pullbackRightPullbackFstIso_hom_fst, pullbackSymmetry_hom_comp_snd]
  have htensor : toTensor.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap B (B ⊗[A] N))) =
      toTarget.hom ≫ pullback.snd ν (g ≫ f) := by
    show m ≫ (pullbackSpecIso A B N).hom ≫
      Spec.map (CommRingCat.ofHom (algebraMap B (B ⊗[A] N))) = _
    calc
      _ = m ≫ pullback.fst g (Spec.map (CommRingCat.ofHom (algebraMap A N))) := by
            rw [pullbackSpecIso_hom_fst]
      _ = pullback.fst g (pullback.fst f ν) := hm_fst
      _ = toTarget.hom ≫ pullback.snd ν (g ≫ f) := hright.symm
  refine ⟨Over.isoMk totalIso ?_⟩
  calc
    totalIso.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap B (B ⊗[A] N))) =
        toTarget.inv ≫ (toTensor.hom ≫
          Spec.map (CommRingCat.ofHom (algebraMap B (B ⊗[A] N)))) := by
      simp [totalIso, Category.assoc]
    _ = toTarget.inv ≫ (toTarget.hom ≫ pullback.snd ν (g ≫ f)) := by rw [htensor]
    _ = pullback.snd ν (g ≫ f) := by simp

/-- Base change to a henselization commutes with integral closure. -/
public theorem toIntegralClosure_bijective_of_isHenselization {A B D : Type u} [CommRing A]
    [IsLocalRing A] [CommRing B] [IsLocalRing B] [Algebra A B] {L : Type v} [Field L]
    [Algebra (ResidueField A) L] [IsHenselization A L B] [CommRing D] [Algebra A D] :
    Function.Bijective (TensorProduct.toIntegralClosure A B D) := by
  classical
  obtain ⟨J, hsmall, hfiltered, pres, hetale⟩ := IsHenselization.ind_etale (R := A) (L := L)
    (Rh := B)
  let : SmallCategory J := hsmall
  let : IsFiltered J := hfiltered
  obtain ⟨ι, hpo, hdirected, hnonempty, FJ, hfinal⟩ := IsFiltered.exists_directed J
  let : PartialOrder ι := hpo
  let : IsDirected ι (· ≤ ·) := hdirected
  let : Nonempty ι := hnonempty
  let : IsDirectedOrder ι := IsFiltered.isDirectedOrder ι
  let p := pres.reindex FJ
  let G : ι → Type u := fun i => (p.diag.obj i : CommAlgCat A)
  let (i : ι) : CommRing (G i) := inferInstance
  let (i : ι) : Algebra A (G i) := inferInstance
  let f : ∀ i j, i ≤ j → (G i →ₐ[A] G j) := fun i j hij => (p.diag.map (homOfLE hij)).hom
  have hf : DirectedSystem G fun i j hij => f i j hij := by
    refine ⟨?_, ?_⟩
    · intro i y
      show (p.diag.map (𝟙 i)).hom y = y
      simp
    · intro k j i hij hjk y
      have hcomp : homOfLE hij ≫ homOfLE hjk = homOfLE (hij.trans hjk) :=
        Subsingleton.elim _ _
      have hm := congrArg (fun g => (p.diag.map g).hom) hcomp
      rw [Functor.map_comp] at hm
      exact DFunLike.congr_fun hm y
  let : DirectedSystem G fun i j hij => f i j hij := hf
  let e0 : DirectLimit G f ≃ₐ[A] ULift.{u} B := by
    let stageToB : ∀ i, G i →ₐ[A] ULift.{u} B := fun i => (p.ι.app i).hom
    have stageCompat : ∀ i j hij y, stageToB j (f i j hij y) = stageToB i y := fun i j hij y =>
      ConcreteCategory.congr_hom (p.w (homOfLE hij)) y
    let toB : DirectLimit G f →ₐ[A] ULift.{u} B :=
      DirectLimit.Algebra.lift G f (ULift.{u} B) stageToB stageCompat
    let cocBack : Cocone p.diag :=
      { pt := CommAlgCat.of A (DirectLimit G f)
        ι :=
          { app := fun i => CommAlgCat.ofHom (DirectLimit.Algebra.of G f i)
            naturality := by
              intro i j g
              ext y
              exact DirectLimit.Algebra.of_f (G := G) (f := f) (hij := leOfHom g) y } }
    let fromB : ULift.{u} B →ₐ[A] DirectLimit G f := (p.isColimit.desc cocBack).hom
    have hfac (i : ι) (y : G i) : fromB (stageToB i y) = DirectLimit.Algebra.of G f i y :=
      (ConcreteCategory.congr_hom (p.isColimit.fac cocBack i) y).trans rfl
    have hleft : Function.LeftInverse fromB toB := by
      intro z
      obtain ⟨i, y, hz⟩ := DirectLimit.exists_eq_mk f z
      rw [hz]
      show fromB (toB (DirectLimit.Algebra.of G f i y)) = DirectLimit.Algebra.of G f i y
      rw [DirectLimit.Algebra.lift_of (ULift.{u} B) stageToB stageCompat i y]
      exact hfac i y
    have hright : Function.LeftInverse toB fromB := by
      intro z
      have hh : CommAlgCat.ofHom (toB.comp fromB) = 𝟙 (CommAlgCat.of A (ULift.{u} B)) := by
        apply p.isColimit.hom_ext
        intro i
        apply CommAlgCat.hom_ext
        ext y
        show (toB (fromB (stageToB i y))).down = (stageToB i y).down
        rw [hfac, DirectLimit.Algebra.lift_of (ULift.{u} B) stageToB stageCompat i y]
      exact DFunLike.congr_fun (congrArg CommAlgCat.Hom.hom hh) z
    exact AlgEquiv.ofBijective toB ⟨hleft.injective, hright.surjective⟩
  let e : DirectLimit G f ≃ₐ[A] B := e0.trans (ULift.algEquiv : ULift.{u} B ≃ₐ[A] B)
  let (i : ι) : Algebra.Smooth A (G i) :=
    (Algebra.Etale.iff_formallyUnramified_and_smooth.mp (hetale (FJ.obj i))).2
  exact TensorProduct.toIntegralClosure_bijective_of_directLimit_smooth f e

/-- For a locally Noetherian scheme `X` and a point `x`, the base change of the normalization
morphism of `X` to the spectrum of a henselization `Ah` of the local ring of `X` at `x` is the
normalization morphism of `Spec Ah`. -/
public theorem normalization_baseChange_isHenselization (X : Scheme.{u}) [IsLocallyNoetherian X]
    (x : X) (Ah : Type u) [CommRing Ah] [IsLocalRing Ah] [Algebra (X.presheaf.stalk x) Ah]
    (L : Type v) [Field L] [Algebra (ResidueField (X.presheaf.stalk x)) L]
    [IsHenselization (X.presheaf.stalk x) L Ah] :
    haveI : IsNoetherianRing Ah :=
      IsLocalRing.isNoetherianRing_of_isHenselization (A := X.presheaf.stalk x) (B := Ah) L
    Nonempty
      (Over.mk (pullback.snd
          (Scheme.normalization X (finite_irreducibleComponents_of_isCompact X))
          (Spec.map (CommRingCat.ofHom (algebraMap (X.presheaf.stalk x) Ah)) ≫
            X.fromSpecStalk x)) ≅
        Over.mk (Scheme.normalization (Spec (.of Ah))
          (finite_irreducibleComponents_of_isCompact (Spec (.of Ah))))) := by
  classical
  have : IsNoetherianRing Ah :=
    IsLocalRing.isNoetherianRing_of_isHenselization (A := X.presheaf.stalk x) (B := Ah) L
  let hX := finite_irreducibleComponents_of_isCompact X
  let hAh := finite_irreducibleComponents_of_isCompact (Spec (.of Ah))
  let A := X.presheaf.stalk x
  let D := minimalPrimes.residueFieldProduct A
  let N := integralClosure A D
  let νX := Scheme.normalization X hX
  obtain ⟨eX, heX⟩ := exists_iso_pullback_normalization_fromSpecStalk X hX x
  obtain ⟨eSource⟩ := @pullback_baseChange_spec A Ah N inferInstance inferInstance inferInstance
    inferInstance inferInstance X _ νX (X.fromSpecStalk x) eX heX
  let Y := Spec (.of Ah)
  let y : Y := closedPoint (↑(CommRingCat.of Ah))
  let νY := Scheme.normalization Y hAh
  obtain ⟨eY, heY⟩ := exists_iso_pullback_normalization_fromSpecStalk Y hAh y
  let A0 := Y.presheaf.stalk y
  let i := stalkClosedPointIso (.of Ah)
  let iRing : Ah ≃+* A0 := i.symm.commRingCatIsoToRingEquiv
  let : IsLocalRing A0 := iRing.isLocalRing
  let : Algebra A A0 := ((i.inv.hom).comp (algebraMap A Ah)).toAlgebra
  let eAh0 : Ah ≃ₐ[A] A0 := AlgEquiv.ofRingEquiv (f := iRing) (fun _ => rfl)
  let : IsHenselization A L A0 :=
    isHenselization_of_algEquiv (A := A) (B := Ah) (C := A0) L eAh0
  let D0 := minimalPrimes.residueFieldProduct A0
  let N0 := integralClosure A0 D0
  obtain ⟨eD⟩ :=
    IsLocalRing.nonempty_algEquiv_tensor_pi_residueField_minimalPrimes_of_isHenselization
      (A := A) (B := A0) L
  let : Algebra A N0 := ((algebraMap A0 N0).comp (algebraMap A A0)).toAlgebra
  let : IsScalarTower A A0 N0 := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let eBaseChange : (A0 ⊗[A] N) ≃ₐ[A0] integralClosure A0 (A0 ⊗[A] D) :=
    AlgEquiv.ofBijective (TensorProduct.toIntegralClosure A A0 D)
      (toIntegralClosure_bijective_of_isHenselization (L := L))
  let eN0 : (A0 ⊗[A] N) ≃ₐ[A0] N0 := eBaseChange.trans eD.mapIntegralClosure
  let eTensor : (Ah ⊗[A] N) ≃ₐ[A] (A0 ⊗[A] N) :=
    Algebra.TensorProduct.congr eAh0 AlgEquiv.refl
  let eA := eTensor.trans (eN0.restrictScalars A)
  let : Algebra Ah N0 := ((algebraMap A0 N0).comp eAh0.toRingHom).toAlgebra
  have hTensorLeft (b : Ah) :
      eTensor (Algebra.TensorProduct.includeLeft (R := A) (S := Ah) (A := Ah) (B := N) b) =
        algebraMap A0 (A0 ⊗[A] N) (eAh0 b) := by
    simp [eTensor, Algebra.TensorProduct.includeLeft]
  have hscalar (b : Ah) :
      eA (Algebra.TensorProduct.includeLeft (R := A) (S := Ah) (A := Ah) (B := N) b) =
        algebraMap A0 N0 (eAh0 b) := by
    show eN0 (eTensor (Algebra.TensorProduct.includeLeft (R := A) (S := Ah)
      (A := Ah) (B := N) b)) = _
    simpa only [hTensorLeft] using eN0.commutes (eAh0 b)
  let eN : (Ah ⊗[A] N) ≃ₐ[Ah] N0 := AlgEquiv.ofRingEquiv (f := eA.toRingEquiv) hscalar
  let eSpec := Scheme.Spec.mapIso eN.symm.toRingEquiv.toCommRingCatIso.op
  have heSpec : eSpec.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap Ah N0)) =
      Spec.map (CommRingCat.ofHom (algebraMap Ah (Ah ⊗[A] N))) := by
    dsimp [eSpec]
    rw [← Spec.map_comp, Spec.map_injective.eq_iff]
    apply CommRingCat.hom_ext
    ext b
    show eN.symm (algebraMap Ah N0 b) = algebraMap Ah (Ah ⊗[A] N) b
    rw [eN.symm.commutes]
  let j := Spec.map i.inv
  have hj : j = Y.fromSpecStalk y := Spec_stalkClosedPointIso (.of Ah)
  let eY' : pullback νY j ≅ Spec (.of N0) := (pullback.congrHom (rfl : νY = νY) hj).trans eY
  have heY' : eY'.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap A0 N0)) = pullback.snd νY j := by
    dsimp [eY']
    simp only [Category.assoc, heY]
    exact pullback.lift_snd _ _ _
  let : IsIso j := by
    dsimp [j]
    infer_instance
  let fstIso : pullback νY j ≅ Scheme.normalizationScheme Y hAh := asIso (pullback.fst νY j)
  let eTarget := fstIso.symm.trans eY'
  have heTarget : eTarget.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap A0 N0)) ≫ j = νY := by
    dsimp [eTarget]
    rw [Iso.trans_hom]
    calc
      fstIso.inv ≫ eY'.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap A0 N0)) ≫ j =
          fstIso.inv ≫ (eY'.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap A0 N0))) ≫ j := by
            simp [Category.assoc]
      _ = fstIso.inv ≫ pullback.snd νY j ≫ j := by rw [heY']
      _ = fstIso.inv ≫ pullback.fst νY j ≫ νY := by rw [← pullback.condition]
      _ = νY := by simp [fstIso]
  have htargetMap : Spec.map (CommRingCat.ofHom (algebraMap Ah N0)) =
      Spec.map (CommRingCat.ofHom (algebraMap A0 N0)) ≫ j := by rw [← Spec.map_comp]; rfl
  have heTarget' : eTarget.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap Ah N0)) = νY := by
    rwa [htargetMap]
  let eTargetOver : Over.mk νY ≅ Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Ah N0))) :=
    Over.isoMk eTarget heTarget'
  exact ⟨eSource.trans ((Over.isoMk eSpec heSpec).trans eTargetOver.symm)⟩

/-- The base change of the normalization morphism of a locally Noetherian scheme `X` to the
spectrum of the henselization of the local ring of `X` at a point is the normalization morphism
of that spectrum. -/
@[stacks 0CBM "henselization"]
public theorem normalization_baseChange_henselization (X : Scheme.{u}) [IsLocallyNoetherian X]
    (x : X) (Ah : Type u) [CommRing Ah] [IsLocalRing Ah] [Algebra (X.presheaf.stalk x) Ah]
    [IsHenselization (X.presheaf.stalk x) (ResidueField (X.presheaf.stalk x)) Ah] :
    haveI : IsNoetherianRing Ah :=
      IsLocalRing.isNoetherianRing_of_isHenselization (A := X.presheaf.stalk x) (B := Ah)
        (ResidueField (X.presheaf.stalk x))
    Nonempty
      (Over.mk (pullback.snd
          (Scheme.normalization X (finite_irreducibleComponents_of_isCompact X))
          (Spec.map (CommRingCat.ofHom (algebraMap (X.presheaf.stalk x) Ah)) ≫
            X.fromSpecStalk x)) ≅
        Over.mk (Scheme.normalization (Spec (.of Ah))
          (finite_irreducibleComponents_of_isCompact (Spec (.of Ah))))) :=
  normalization_baseChange_isHenselization X x Ah (ResidueField (X.presheaf.stalk x))

/-- The base change of the normalization morphism of a locally Noetherian scheme `X` to the
spectrum of a strict henselization of the local ring of `X` at a point is the normalization
morphism of that spectrum. -/
@[stacks 0CBM "strict_henselization"]
public theorem normalization_baseChange_strictHenselization (X : Scheme.{u})
    [IsLocallyNoetherian X] (x : X) (Ash : Type u) [CommRing Ash] [IsLocalRing Ash]
    [Algebra (X.presheaf.stalk x) Ash] (ksep : Type v) [Field ksep]
    [Algebra (ResidueField (X.presheaf.stalk x)) ksep]
    [IsSepClosure (ResidueField (X.presheaf.stalk x)) ksep]
    [IsHenselization (X.presheaf.stalk x) ksep Ash] :
    haveI : IsNoetherianRing Ash :=
      IsLocalRing.isNoetherianRing_of_isHenselization (A := X.presheaf.stalk x) (B := Ash) ksep
    Nonempty
      (Over.mk (pullback.snd
          (Scheme.normalization X (finite_irreducibleComponents_of_isCompact X))
          (Spec.map (CommRingCat.ofHom (algebraMap (X.presheaf.stalk x) Ash)) ≫
            X.fromSpecStalk x)) ≅
        Over.mk (Scheme.normalization (Spec (.of Ash))
          (finite_irreducibleComponents_of_isCompact (Spec (.of Ash))))) :=
  normalization_baseChange_isHenselization X x Ash ksep

end AlgebraicGeometry
