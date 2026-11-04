module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Morphisms.CohenMacaulay.FibreStalk
public import StacksFrontier.AlgebraicGeometry.Perfect.BaseChangeStalk
public import StacksFrontier.AlgebraicGeometry.Perfect.TorIndependence
public import StacksFrontier.Homology.Tor.Independence

/-!
# Flat base change of Tor-independent schemes

Tor independence of two schemes `X` and `Y` over a base `S` is preserved after changing the base
by a flat morphism `S' ⟶ S`.

At a pair of points of `X ×_S S'` and `Y ×_S S'` lying over the same point of `S'`, the local
ring of the fibre product is a localization of the tensor product of the local ring of `X`,
resp. `Y`, with the local ring of `S'` over the local ring of `S`. All three extensions
`𝒪_{S,s} → 𝒪_{S',s'}`, `𝒪_{X,x} → 𝒪_{X ×_S S', x'}` and `𝒪_{Y,y} → 𝒪_{Y ×_S S', y'}` are
therefore flat, so the base-change comparison map on Tor modules is an isomorphism, and the
source Tor modules vanish in positive degrees by hypothesis.

## Main results

* `AlgebraicGeometry.torIndependent_pullback_of_flat`: flat base change preserves Tor
  independence.

## Implementation notes

The two base-changed schemes are represented by categorical pullbacks, and their structure
morphisms to the new base are the second pullback projections. The identification of the local
ring of a fibre product as a localization of a tensor product of local rings is
`AlgebraicGeometry.BaseChangeStalk.pullback_stalk_isLocalization`.

Several `eqToHom`s appear because the local ring of `S` is indexed by a point that the two sides
of the square reach by different routes; `AlgebraicGeometry.stalkCongr_of_eq` turns the stalk
congruence of the general theory into such an `eqToHom`, after which the comparisons are
assembled by `eqToHom_trans`.

## References

* [Stacks Project, Tag 0FXW](https://stacks.math.columbia.edu/tag/0FXW)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- Tor independence of two schemes over a common base is preserved by a flat base change. -/
@[stacks 0FXW]
lemma torIndependent_pullback_of_flat
    {S X Y S' : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) (s : S' ⟶ S)
    [Flat s] (h : TorIndependent f g) :
    TorIndependent (pullback.snd f s) (pullback.snd g s) := by
  let pX := pullback.fst f s
  let pS := pullback.snd f s
  let qY := pullback.fst g s
  let qS := pullback.snd g s
  show ∀ (x' : (pullback f s).carrier) (y' : (pullback g s).carrier)
      (h' : pS.base x' = qS.base y'), _
  intro x' y' h'
  let x := pX.base x'
  let y := qY.base y'
  have hxbase : f.base x = s.base (pS.base x') :=
    congrArg (fun k : pullback f s ⟶ S => k.base x') pullback.condition
  have hybase : g.base y = s.base (qS.base y') :=
    congrArg (fun k : pullback g s ⟶ S => k.base y') pullback.condition
  have hbase : f.base x = g.base y := hxbase.trans ((congrArg s.base h').trans hybase.symm)
  have hsource := h x y hbase
  let R := S.presheaf.stalk (f.base (pX.base x'))
  let R' := S'.presheaf.stalk (pS.base x')
  let A := X.presheaf.stalk x
  let B := Y.presheaf.stalk y
  let A' := (pullback f s).presheaf.stalk x'
  let B' := (pullback g s).presheaf.stalk y'
  let : Algebra R A := (f.stalkMap x).hom.toAlgebra
  let : Algebra R B :=
    ((eqToHom (congrArg S.presheaf.stalk hbase) ≫ g.stalkMap y).hom).toAlgebra
  have hX : (pX ≫ f).base x' = (pS ≫ s).base x' :=
    congrArg (fun k : pullback f s ⟶ S => k.base x') pullback.condition
  let : Algebra R R' :=
    ((eqToHom (congrArg S.presheaf.stalk hxbase) ≫ s.stalkMap (pS.base x')).hom).toAlgebra
  let : Algebra R' A' := (pS.stalkMap x').hom.toAlgebra
  let : Algebra R' B' :=
    ((eqToHom (congrArg S'.presheaf.stalk h') ≫ qS.stalkMap y').hom).toAlgebra
  let : Algebra R A' :=
    ((eqToHom (congrArg S.presheaf.stalk hxbase) ≫ s.stalkMap (pS.base x') ≫
      pS.stalkMap x').hom).toAlgebra
  let : Algebra R B' :=
    ((eqToHom (congrArg S.presheaf.stalk hxbase) ≫ s.stalkMap (pS.base x') ≫
      eqToHom (congrArg S'.presheaf.stalk h') ≫ qS.stalkMap y').hom).toAlgebra
  have : IsScalarTower R R' A' := IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower R R' B' := IsScalarTower.of_algebraMap_eq' rfl
  obtain ⟨φA, hφAL, hφAR, M_A, hM_A⟩ := BaseChangeStalk.pullback_stalk_isLocalization f s x'
  obtain ⟨φB, hφBL, hφBR, M_B, hM_B⟩ := BaseChangeStalk.pullback_stalk_isLocalization g s y'
  change TensorProduct R A R' →+* A' at φA
  change φA.comp Algebra.TensorProduct.includeLeftRingHom =
    (pX.stalkMap x').hom at hφAL
  change φA.comp Algebra.TensorProduct.includeRight.toRingHom =
    (pS.stalkMap x').hom at hφAR
  -- The scheme pullback stalk comparisons identify both factor extensions with localizations.
  dsimp only [pX, pS, qY, qS, R, R', A, B, A', B'] at hφAL hφAR hM_A hφBL hφBR hM_B
  simp only [Scheme.Hom.comp_base] at hφAL hφAR hM_A hφBL hφBR hM_B
  have hcompA :
      f.stalkMap x ≫ pX.stalkMap x' =
        eqToHom (congrArg S.presheaf.stalk hxbase) ≫ s.stalkMap (pS.base x') ≫
          pS.stalkMap x' := by
    have e := (Scheme.Hom.stalkMap_congr_hom (pX ≫ f) (pS ≫ s)
      pullback.condition x').symm
    rw [stalkCongr_of_eq S.presheaf
      (congrArg (fun k : pullback f s ⟶ S => k.base x') pullback.condition),
      Scheme.Hom.stalkMap_comp] at e
    rw [← Scheme.Hom.stalkMap_comp]
    exact e.symm
  let fA : A →ₐ[R] A' := AlgHom.mk' (pX.stalkMap x').hom (by
    intro r z
    show (pX.stalkMap x').hom ((f.stalkMap x).hom r * z) =
      ((eqToHom (congrArg S.presheaf.stalk hxbase) ≫ s.stalkMap (pS.base x') ≫
        pS.stalkMap x').hom r) * (pX.stalkMap x').hom z
    rw [map_mul]
    congr 1
    exact DFunLike.congr_fun (CommRingCat.hom_ext_iff.mp hcompA) r)
  have hstalkSquare := Scheme.Hom.stalkMap_congr s s rfl (pS.base x') (qS.base y') h'
  rw [stalkCongr_of_eq S'.presheaf h',
    stalkCongr_of_eq S.presheaf (congrArg s.base h')] at hstalkSquare
  have hcompB :
      eqToHom (congrArg S.presheaf.stalk hbase) ≫ g.stalkMap y ≫ qY.stalkMap y' =
        eqToHom (congrArg S.presheaf.stalk hxbase) ≫ s.stalkMap (pS.base x') ≫
          eqToHom (congrArg S'.presheaf.stalk h') ≫ qS.stalkMap y' := by
    have eY := (Scheme.Hom.stalkMap_congr_hom (qY ≫ g) (qS ≫ s)
      pullback.condition y').symm
    dsimp [y] at eY
    rw [stalkCongr_of_eq S.presheaf hybase, Scheme.Hom.stalkMap_comp] at eY
    dsimp [y] at eY ⊢
    calc
      _ = eqToHom (congrArg S.presheaf.stalk hbase) ≫
          (qY ≫ g).stalkMap y' := by
        simp only [← Scheme.Hom.stalkMap_comp]
      _ = eqToHom (congrArg S.presheaf.stalk hbase) ≫
          eqToHom (congrArg S.presheaf.stalk hybase) ≫
            s.stalkMap (qS.base y') ≫ qS.stalkMap y' := by
        rw [← eY]
      _ = _ := by rw [reassoc_of% hstalkSquare, eqToHom_trans_assoc, eqToHom_trans_assoc]
  let fB : B →ₐ[R] B' := AlgHom.mk' (qY.stalkMap y').hom (by
    intro r z
    show (qY.stalkMap y').hom
        (((eqToHom (congrArg S.presheaf.stalk hbase) ≫ g.stalkMap y).hom r) * z) =
      ((eqToHom (congrArg S.presheaf.stalk hxbase) ≫ s.stalkMap (pS.base x') ≫
        eqToHom (congrArg S'.presheaf.stalk h') ≫ qS.stalkMap y').hom r) *
        (qY.stalkMap y').hom z
    rw [map_mul]
    congr 1
    exact DFunLike.congr_fun (CommRingCat.hom_ext_iff.mp hcompB) r)
  let ψA := Algebra.TensorProduct.lift fA (IsScalarTower.toAlgHom R R' A')
    (fun _ _ ↦ Commute.all _ _)
  let ψB := Algebra.TensorProduct.lift (IsScalarTower.toAlgHom R R' B') fB
    (fun _ _ ↦ Commute.all _ _)
  have hRflat : RingHom.Flat (algebraMap R R') := by
    show ((eqToHom (congrArg S.presheaf.stalk hxbase) ≫
      s.stalkMap (pS.base x')).hom).Flat
    exact RingHom.Flat.comp
      (.of_bijective (ConcreteCategory.bijective_of_isIso _))
      (Flat.stalkMap s (pS.base x'))
  let R₀ := S.presheaf.stalk ((pX ≫ f).base x')
  let : Algebra R₀ A := (f.stalkMap (pX.base x')).hom.toAlgebra
  let : Algebra R₀ R' :=
    ((eqToHom (congrArg S.presheaf.stalk hX) ≫
      s.stalkMap (pS.base x')).hom).toAlgebra
  let T₀ := TensorProduct R₀ A R'
  have hAflat : RingHom.Flat ψA.toRingHom := by
    have hψA : ψA.toRingHom = φA := by
      apply Algebra.TensorProduct.ringHom_ext
      · show (ψA.comp Algebra.TensorProduct.includeLeft).toRingHom = _
        rw [Algebra.TensorProduct.lift_comp_includeLeft, hφAL]
        rfl
      · show (ψA.comp Algebra.TensorProduct.includeRight).toRingHom = _
        rw [Algebra.TensorProduct.lift_comp_includeRight', hφAR]
        rfl
    rw [hψA]
    let : Algebra T₀ A' := φA.toAlgebra
    have : IsLocalization M_A A' := hM_A
    exact RingHom.flat_algebraMap_iff.mpr (IsLocalization.flat A' M_A)
  let R₁ := S.presheaf.stalk (g.base (qY.base y'))
  let R₁' := S'.presheaf.stalk (qS.base y')
  let eR₁ : R₁ ≃+* R := RingEquiv.ofBijective
    (eqToHom (congrArg S.presheaf.stalk hbase.symm)).hom
    (ConcreteCategory.bijective_of_isIso _)
  let : Algebra R₁ R := eR₁.toRingHom.toAlgebra
  let : Algebra R₁ B := (g.stalkMap (qY.base y')).hom.toAlgebra
  let : Algebra R₁ R₁' :=
    ((eqToHom (congrArg S.presheaf.stalk hybase) ≫
      s.stalkMap (qS.base y')).hom).toAlgebra
  change TensorProduct R₁ B R₁' →+* B' at φB
  change φB.comp Algebra.TensorProduct.includeLeftRingHom =
    (qY.stalkMap y').hom at hφBL
  change φB.comp Algebra.TensorProduct.includeRight.toRingHom =
    (qS.stalkMap y').hom at hφBR
  let : Algebra R R₁ := eR₁.symm.toRingHom.toAlgebra
  let : Algebra R R₁' :=
    ((eqToHom (congrArg S.presheaf.stalk hxbase) ≫ s.stalkMap (pS.base x') ≫
      eqToHom (congrArg S'.presheaf.stalk h')).hom).toAlgebra
  have hbaseTower :
      (algebraMap R B).comp (algebraMap R₁ R) = algebraMap R₁ B := by
    ext z
    show ((eqToHom (congrArg S.presheaf.stalk hbase.symm) ≫
      (eqToHom (congrArg S.presheaf.stalk hbase) ≫ g.stalkMap y)).hom) z =
      (g.stalkMap y).hom z
    rw [eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  have : IsScalarTower R₁ R B := IsScalarTower.of_algebraMap_eq' hbaseTower.symm
  have hmapToR₁' :
      eqToHom (congrArg S.presheaf.stalk hbase.symm) ≫
        (eqToHom (congrArg S.presheaf.stalk hxbase) ≫
          s.stalkMap (pS.base x') ≫ eqToHom (congrArg S'.presheaf.stalk h')) =
      eqToHom (congrArg S.presheaf.stalk hybase) ≫ s.stalkMap (qS.base y') := by
    rw [hstalkSquare, eqToHom_trans_assoc, eqToHom_trans_assoc]
  have htargetTower :
      (algebraMap R R₁').comp (algebraMap R₁ R) = algebraMap R₁ R₁' := by
    ext z
    exact DFunLike.congr_fun (CommRingCat.hom_ext_iff.mp hmapToR₁') z
  have : IsScalarTower R₁ R R₁' := IsScalarTower.of_algebraMap_eq' htargetTower.symm
  let : TensorProduct.CompatibleSMul R₁ R B R₁' :=
    TensorProduct.CompatibleSMul.of_algebraMap_surjective
      (R := R₁) (A := R) (M := B) (N := R₁') eR₁.surjective
  let eTB := Algebra.TensorProduct.equivOfCompatibleSMul R R₁ B B R₁'
  let eS : R₁' ≃ₐ[R] R' := AlgEquiv.ofRingEquiv
    (f := RingEquiv.ofBijective
      (eqToHom (congrArg S'.presheaf.stalk h'.symm)).hom
      (ConcreteCategory.bijective_of_isIso _)) (by
      intro r
      have hc :
          eqToHom (congrArg S.presheaf.stalk hxbase) ≫
            s.stalkMap (pS.base x') ≫
              eqToHom (congrArg S'.presheaf.stalk h') ≫
                eqToHom (congrArg S'.presheaf.stalk h'.symm) =
          eqToHom (congrArg S.presheaf.stalk hxbase) ≫
            s.stalkMap (pS.base x') := by
        rw [eqToHom_trans, eqToHom_refl, Category.comp_id]
      show ((eqToHom (congrArg S'.presheaf.stalk h'.symm)).hom
        (((eqToHom (congrArg S.presheaf.stalk hxbase) ≫
          s.stalkMap (pS.base x') ≫
          eqToHom (congrArg S'.presheaf.stalk h')).hom r))) =
        ((eqToHom (congrArg S.presheaf.stalk hxbase) ≫
          s.stalkMap (pS.base x')).hom r)
      exact DFunLike.congr_fun (CommRingCat.hom_ext_iff.mp hc) r)
  let eTB' : (TensorProduct R₁ B R₁') ≃+* (TensorProduct R R' B) :=
    eTB.toRingEquiv.trans
      (Algebra.TensorProduct.congr (AlgEquiv.refl : B ≃ₐ[R] B) eS).toRingEquiv |>.trans
        (Algebra.TensorProduct.comm R R' B).toRingEquiv.symm
  let hTB := eTB'.symm.toRingHom
  have hTBleft : hTB.comp Algebra.TensorProduct.includeLeftRingHom =
      Algebra.TensorProduct.includeRight.toRingHom.comp eS.symm.toRingHom := by
    ext z
    show eTB'.symm (z ⊗ₜ[R] (1 : B)) = (1 : B) ⊗ₜ[R₁] eS.symm z
    simp [eTB', eTB, Algebra.TensorProduct.equivOfCompatibleSMul,
      Algebra.TensorProduct.mapOfCompatibleSMul_tmul]
  have hTBright : hTB.comp Algebra.TensorProduct.includeRight.toRingHom =
      Algebra.TensorProduct.includeLeftRingHom := by
    ext z
    show eTB'.symm ((1 : R') ⊗ₜ[R] z) = z ⊗ₜ[R₁] (1 : R₁')
    simp [eTB', eTB, Algebra.TensorProduct.equivOfCompatibleSMul,
      Algebra.TensorProduct.mapOfCompatibleSMul_tmul]
  have hBflat : RingHom.Flat ψB.toRingHom := by
    have hψB : ψB.toRingHom = φB.comp hTB := by
      apply Algebra.TensorProduct.ringHom_ext
      · show (ψB.comp Algebra.TensorProduct.includeLeft).toRingHom = _
        rw [Algebra.TensorProduct.lift_comp_includeLeft]
        ext z
        show (algebraMap R' B') z =
          φB ((hTB.comp Algebra.TensorProduct.includeLeftRingHom) z)
        have hzTB := congrArg φB (DFunLike.congr_fun hTBleft z)
        change φB ((hTB.comp Algebra.TensorProduct.includeLeftRingHom) z) =
          φB (Algebra.TensorProduct.includeRight (eS.symm z)) at hzTB
        rw [hzTB]
        have hz := DFunLike.congr_fun hφBR (eS.symm z)
        change φB (Algebra.TensorProduct.includeRight (eS.symm z)) = _ at hz
        calc
          _ = (qS.stalkMap y').hom (eS.symm z) := by
            show ((eqToHom (congrArg S'.presheaf.stalk h') ≫
              qS.stalkMap y').hom) z = _
            apply congrArg (qS.stalkMap y').hom
            apply eS.injective
            have hp : eS ((eqToHom (congrArg S'.presheaf.stalk h')).hom' z) = z := by
              show ((eqToHom (congrArg S'.presheaf.stalk h'.symm)).hom'.comp
                (eqToHom (congrArg S'.presheaf.stalk h')).hom') z = z
              exact DFunLike.congr_fun (CommRingCat.hom_ext_iff.mp
                ((eqToIso (congrArg S'.presheaf.stalk h')).hom_inv_id)) z
            rw [hp, eS.apply_symm_apply]
          _ = _ := hz.symm
      · show (ψB.comp Algebra.TensorProduct.includeRight).toRingHom = _
        rw [Algebra.TensorProduct.lift_comp_includeRight']
        ext z
        show (fB.toRingHom) z =
          φB ((hTB.comp Algebra.TensorProduct.includeRight.toRingHom) z)
        have hzTB := congrArg φB (DFunLike.congr_fun hTBright z)
        rw [hzTB]
        have hz := DFunLike.congr_fun hφBL z
        change φB (Algebra.TensorProduct.includeLeftRingHom z) = _ at hz
        simpa [fB] using hz.symm
    have hφflat : RingHom.Flat φB := by
      let T₁ := TensorProduct R₁ B R₁'
      let : Algebra T₁ B' := φB.toAlgebra
      change Submonoid T₁ at M_B
      change IsLocalization M_B B' at hM_B
      have : IsLocalization M_B B' := hM_B
      exact RingHom.flat_algebraMap_iff.mpr (IsLocalization.flat B' M_B)
    rw [hψB]
    exact RingHom.Flat.comp (.of_bijective eTB'.symm.bijective) hφflat
  rw [_root_.Algebra.torIndependent_iff]
  intro i hi
  let e := TorChangeOfRings.extensionMap TorChangeOfRings.canonicalSystem_nonempty
    R R' A B A' B' i fA fB
  have he : IsIso e :=
    RingTheory.TorIndependence.isIso_torExtensionMap_of_flat_sameUniverse
      R R' A B A' B' fA fB hRflat hAflat hBflat i
  have : Subsingleton (TorChangeOfRings.torObj R i A B) :=
    ModuleCat.isZero_iff_subsingleton.mp (hsource.isZero i hi)
  have hbig := (asIso e).isZero_iff.mp ((ModuleCat.extendScalars _).map_isZero
    (ModuleCat.isZero_iff_subsingleton.mpr inferInstance))
  have hsub := ModuleCat.isZero_iff_subsingleton.mp hbig
  exact ModuleCat.isZero_iff_subsingleton.mpr hsub

end AlgebraicGeometry

end
