module

public import StacksFrontier.RingTheory.Dualizing.UpperShriek.FlatBaseChangeHomology
public import StacksFrontier.RingTheory.Dualizing.BaseChangeComparison.BridgeA.MateSquare
public import StacksFrontier.RingTheory.Dualizing.BaseChangeComparison.ComparisonMateDualizing

/-!
# The flat case of Stacks 0BZM, on cohomology

Let `R → A` and `R → R'` be homomorphisms of commutative rings with `R → R'` flat, and let
`A' = A ⊗_R R'`.  The base-change morphism of [Stacks, Tag 0E29],

`RHom_R(A, K) ⊗_A^L A' ⟶ RHom_{R'}(A', K ⊗_R^L R')`,

is invertible at every bounded-below `K` as soon as `A` is pseudo-coherent over `R`: this is the
flat case of [Stacks, Tag 0BZM].

## Main results

* `Dualizing.isIso_derivedHomBaseChange_app_of_flat_flatModelsLarge` — the flat case of
  [Stacks, Tag 0BZM], at the exact models of the two derived extensions of scalars and at every
  module universe.
* `Dualizing.isIso_derivedHomBaseChange_app_of_flat_flatModels` — the same at the module universe
  of the rings and the models `Dualizing.flatDerivedExtension`.

## References

* [Stacks Project, Tag 0BZM](https://stacks.math.columbia.edu/tag/0BZM)
* [Stacks Project, Tag 0E29](https://stacks.math.columbia.edu/tag/0E29)
* [Stacks Project, Tag 0E1X](https://stacks.math.columbia.edu/tag/0E1X)
* [Stacks Project, Tag 0A6A](https://stacks.math.columbia.edu/tag/0A6A)
* [Stacks Project, Tag 0661](https://stacks.math.columbia.edu/tag/0661)
-/

@[expose] public section

open CategoryTheory

attribute [local instance] HasDerivedCategory.standard

universe u v

namespace Dualizing

noncomputable section

attribute [local instance] Algebra.TensorProduct.rightAlgebra

variable {R A R' : Type u} [CommRing R] [CommRing A] [CommRing R'] [Algebra R A] [Algebra R R']
  (hTor : RingTheory.TorIndependence.TorIndependent R A R')
  (hT : (algebraMap R R').Flat) (hA : (algebraMap A (TensorProduct R A R')).Flat)

/-- **The flat case of [Stacks, Tag 0BZM].**  Let `R → R'` be flat, `A' = A ⊗_R R'` (flat over
`A`), and let `A` be pseudo-coherent as an `R`-module.  Then the base-change morphism of
[Stacks, Tag 0E29] at the exact models of derived extension of scalars along `R → R'` and
`A → A'` is invertible at every bounded-below object of `D(R)`. -/
theorem isIso_derivedHomBaseChange_app_of_flat_flatModelsLarge
    (hPC : StacksDraft.PseudoCoherence.IsPseudoCoherent
      ((DerivedCategory.singleFunctor (ModuleCat.{max v u} R) 0).obj
        ((ModuleCat.restrictScalars (algebraMap R A)).obj
          (ModuleCat.of A (ULift.{max v u} A)))))
    (K : DerivedCategory (ModuleCat.{max v u} R)) (b : ℤ) (hK : DerivedCategory.IsGE K b) :
    IsIso ((derivedHomBaseChange.{u, u, u, v} hTor
      (flatDerivedExtensionLarge.{u, v} (algebraMap R R') hT)
      (flatDerivedExtensionLargeFactors.{u, v} _ hT)
      (flatDerivedExtensionLarge_isLeftDerived.{u, v} _ hT)
      (flatDerivedExtensionLarge.{u, v} (algebraMap A (TensorProduct R A R')) hA)
      (flatDerivedExtensionLargeFactors.{u, v} _ hA)
      (flatDerivedExtensionLarge_isLeftDerived.{u, v} _ hA)).app K) := by
  let dR := flatDerivedExtensionLarge.{u, v} (algebraMap R R') hT
  let cR := flatDerivedExtensionLargeFactors.{u, v} (algebraMap R R') hT
  let lR := flatDerivedExtensionLarge_isLeftDerived.{u, v} (algebraMap R R') hT
  let dA := flatDerivedExtensionLarge.{u, v} (algebraMap A (TensorProduct R A R')) hA
  let cA := flatDerivedExtensionLargeFactors.{u, v} (algebraMap A (TensorProduct R A R')) hA
  let lA := flatDerivedExtensionLarge_isLeftDerived.{u, v} (algebraMap A (TensorProduct R A R')) hA
  let ri := (Algebra.TensorProduct.includeRight : R' →ₐ[R] TensorProduct R A R').toRingHom
  let δ := derivedHomBaseChange.{u, u, u, v} hTor dR cR lR dA cA lA
  let Hp := derivedHom.{u, v, u} (algebraMap R A)
  let I := derivedHom.{u, v, u} ri
  let resσ := (ModuleCat.restrictScalars.{max v u} (algebraMap R A)).mapDerivedCategory
  let resT := (ModuleCat.restrictScalars.{max v u} (algebraMap R R')).mapDerivedCategory
  let resri := (ModuleCat.restrictScalars.{max v u} ri).mapDerivedCategory
  let resA :=
    (ModuleCat.restrictScalars.{max v u} (algebraMap A (TensorProduct R A R'))).mapDerivedCategory
  refine isIso_derivedHomBaseChange_app_of_restrictScalars hTor dR cR lR dA cA lA K ?_
  let c := (restrictionBaseChangeIsoGeneral.{u, u, u, v} hTor dR cR lR dA cA lA).inv.app (Hp.obj K)
  suffices hc : IsIso (c ≫ resri.map (δ.app K)) from
    @IsIso.of_isIso_comp_left _ _ _ _ _ c _ _ hc
  let B' := (DerivedCategory.singleFunctor (ModuleCat.{max v u} R) 0).obj
        ((ModuleCat.restrictScalars (algebraMap R A)).obj (ModuleCat.of A (ULift.{max v u} A)))
  let ψ := derivedHomRestrictScalarsInternalHomIsoCanonical.{u, u, max v u} (algebraMap R A)
  let w := Stacks.DerivedHom.ExtensionOfScalars.derivedHomBaseChange.{u, u, max v u}
    (algebraMap R R') dR cR B' K
  let mT := mateTargetIso.{u, u, u, v} hTor dR cR lR dA cA lA K
  let hom := Stacks.DerivedHom.ScalarTransportedInternalHom.hom.{u, max v u} R
  let ψY : ∀ Y : DerivedCategory (ModuleCat.{max v u} R),
      resσ.obj (Hp.obj Y) ⟶ hom.obj (Opposite.op B', Y) := fun Y => ψ.hom.app Y
  let f₂ := dR.map (ψY K) ≫ w ≫ mT.inv
  let adjRA := derivedHomAdjunction.{u, u, max v u} (algebraMap R A)
  let adjRI := derivedHomAdjunction.{u, u, max v u} ri
  let adjT :=
    CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsAdjunction.{u, u, max v u}
      (algebraMap R R') dR cR
  let adjA :=
    CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsAdjunction.{u, u, max v u}
      (algebraMap A (TensorProduct R A R')) dA cA
  let G := restrictionBaseChangeIsoGeneral.{u, u, u, v} hTor dR cR lR dA cA lA
  let κ := conjugateEquiv (adjRA.comp adjT) (adjA.comp adjRI) G.hom
  let γ := RingTheory.TorIndependence.restrictSquareDerivedIso.{u, u, u, u, v} (algebraMap R A)
    (algebraMap R R') (algebraMap A (TensorProduct R A R')) (algebraMap R' (TensorProduct R A R'))
    ((IsScalarTower.algebraMap_eq R A (TensorProduct R A R')).symm.trans
      (IsScalarTower.algebraMap_eq R R' (TensorProduct R A R')))
  have hstar := unit_comp_restrictionBaseChangeIsoGeneral_inv.{u, u, u, v} hTor dR cR dA cA
    (Hp.obj K)
  let δ' : ∀ K' : DerivedCategory (ModuleCat.{max v u} R), dA.obj (Hp.obj K') ⟶ I.obj (dR.obj K') :=
    fun K' => adjRI.unit.app _ ≫ I.map (G.hom.app (Hp.obj K')) ≫
      I.map (dR.map (adjRA.counit.app K'))
  have hδ : ∀ K' : DerivedCategory (ModuleCat.{max v u} R), δ.app K' = δ' K' := by
    intro K'
    rw [show δ.app K' = _ from derivedHomBaseChange_eq hTor dR cR lR dA cA lA K',
      Adjunction.homEquiv_unit, restrictionBaseChangeIso_hom_app, Functor.map_comp]
    rfl
  let κY : ∀ Y : DerivedCategory (ModuleCat.{max v u} R'),
      Hp.obj (resT.obj Y) ⟶ resA.obj (I.obj Y) :=
    fun Y => κ.app Y
  have hκ : ∀ Y, κY Y = adjA.unit.app (Hp.obj (resT.obj Y)) ≫
      resA.map (adjRI.unit.app (dA.obj (Hp.obj (resT.obj Y)))) ≫
        resA.map (I.map (G.hom.app (Hp.obj (resT.obj Y)))) ≫
          resA.map (I.map (dR.map (adjRA.counit.app (resT.obj Y)))) ≫
            resA.map (I.map (adjT.counit.app Y)) := by
    intro Y
    simp only [κY, κ, conjugateEquiv_apply_app, Adjunction.comp_unit_app,
      Adjunction.comp_counit_app, Functor.comp_map, Functor.map_comp, Category.assoc]
    rfl
  have hκnat : ∀ {Y Y' : DerivedCategory (ModuleCat.{max v u} R')} (h : Y ⟶ Y'),
      Hp.map (resT.map h) ≫ κY Y' = κY Y ≫ resA.map (I.map h) := fun h => κ.naturality h
  have K1 : adjA.unit.app (Hp.obj K) ≫ resA.map (δ' K) =
      Hp.map (adjT.unit.app K) ≫ κY (dR.obj K) := by
    have e1 : Hp.map (adjT.unit.app K) ≫ adjA.unit.app (Hp.obj (resT.obj (dR.obj K))) =
        adjA.unit.app (Hp.obj K) ≫ resA.map (dA.map (Hp.map (adjT.unit.app K))) :=
      adjA.unit.naturality (Hp.map (adjT.unit.app K))
    have e2 : dA.map (Hp.map (adjT.unit.app K)) ≫ δ' (resT.obj (dR.obj K)) =
        δ' K ≫ I.map (dR.map (adjT.unit.app K)) :=
      (congrArg (fun t => dA.map (Hp.map (adjT.unit.app K)) ≫ t) (hδ _)).symm.trans
        ((δ.naturality (adjT.unit.app K)).trans
          (congrArg (fun t => t ≫ I.map (dR.map (adjT.unit.app K))) (hδ K)))
    have e3 : I.map (dR.map (adjT.unit.app K)) ≫ I.map (adjT.counit.app (dR.obj K)) = 𝟙 _ :=
      (I.map_comp _ _).symm.trans ((congrArg I.map (adjT.left_triangle_components K)).trans
        (I.map_id _))
    have e6 : dA.map (Hp.map (adjT.unit.app K)) ≫
        adjRI.unit.app (dA.obj (Hp.obj (resT.obj (dR.obj K)))) ≫
          I.map (G.hom.app (Hp.obj (resT.obj (dR.obj K)))) ≫
            I.map (dR.map (adjRA.counit.app (resT.obj (dR.obj K)))) ≫
              I.map (adjT.counit.app (dR.obj K)) = δ' K := by
      calc _ = (dA.map (Hp.map (adjT.unit.app K)) ≫ δ' (resT.obj (dR.obj K))) ≫
            I.map (adjT.counit.app (dR.obj K)) := by
              simp only [δ', Category.assoc]
              exact whisker_eq _ (whisker_eq _ (Category.assoc _ _ _).symm)
        _ = (δ' K ≫ I.map (dR.map (adjT.unit.app K))) ≫ I.map (adjT.counit.app (dR.obj K)) := by
            rw [e2]
        _ = δ' K := by rw [Category.assoc, e3]; exact Category.comp_id _
    rw [hκ, reassoc_of% e1]
    refine whisker_eq _ ?_
    rw [← e6]
    simp only [Functor.map_comp]
    exact whisker_eq _ (whisker_eq _ ((resA.map_comp _ _).trans
      (whisker_eq _ (resA.map_comp _ _))))
  let Φ : ∀ Y : DerivedCategory (ModuleCat.{max v u} R'),
      resσ.obj (Hp.obj (resT.obj Y)) ⟶ resT.obj (resri.obj (I.obj Y)) :=
    fun Y => resσ.map (κY Y) ≫ γ.hom.app (I.obj Y)
  have T1 : adjT.homEquiv _ _ (c ≫ resri.map (δ' K)) =
      resσ.map (Hp.map (adjT.unit.app K)) ≫ Φ (dR.obj K) := by
    have hγ : γ.hom.app (dA.obj (Hp.obj K)) ≫ resT.map (resri.map (δ' K)) =
        resσ.map (resA.map (δ' K)) ≫ γ.hom.app (I.obj (dR.obj K)) :=
      (γ.hom.naturality (δ' K)).symm
    rw [Adjunction.homEquiv_unit, Functor.map_comp, reassoc_of% hstar, hγ, ← resσ.map_comp_assoc,
      K1, resσ.map_comp, Category.assoc]
  let ψri := derivedHomRestrictScalarsInternalHomIsoCanonical.{u, u, max v u} ri
  let dBAI := derivedBaseChangeAlgebraIso.{u, u, u, v} hTor dR cR lR dA cA lA
  let hom' := Stacks.DerivedHom.ScalarTransportedInternalHom.hom.{u, max v u} R'
  let mT' : ∀ Y : DerivedCategory (ModuleCat.{max v u} R'),
      resri.obj (I.obj Y) ≅ hom'.obj (Opposite.op (dR.obj B'), Y) :=
    fun Y => ψri.app Y ≪≫ hom'.mapIso (Iso.prod (Iso.op dBAI) (Iso.refl Y))
  have hmT : mT' (dR.obj K) = mT := rfl
  let Ω := Stacks.DerivedHom.BaseChange.derivedHomRestrictScalarsNatIso.{u, u, max v u}
    (algebraMap R R') dR cR
  let Φ' : ∀ Y : DerivedCategory (ModuleCat.{max v u} R'),
      resσ.obj (Hp.obj (resT.obj Y)) ⟶ resT.obj (resri.obj (I.obj Y)) :=
    fun Y => ψY (resT.obj Y) ≫ (Ω.app (Opposite.op B', Y)).hom ≫ resT.map (mT' Y).inv
  have T2 : adjT.homEquiv _ _ f₂ = resσ.map (Hp.map (adjT.unit.app K)) ≫ Φ' (dR.obj K) := by
    have hw := Stacks.DerivedHom.ExtensionOfScalars.derivedHomBaseChange_homEquiv.{u, u, max v u}
      (algebraMap R R') dR cR B' K
    have hψ0 := ψ.hom.naturality (adjT.unit.app K)
    have e1 : adjT.homEquiv _ _ f₂ = ψY K ≫ adjT.homEquiv _ _ w ≫ resT.map mT.inv := by
      rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right]
    rw [e1, hw]
    refine (Category.assoc _ _ _).symm.trans ?_
    refine ((congrArg (fun t => t ≫ resT.map mT.inv) (Category.assoc _ _ _).symm)).trans ?_
    refine (congrArg (fun t => (t ≫ _) ≫ resT.map mT.inv) hψ0.symm).trans ?_
    exact (Category.assoc _ _ _).trans (Category.assoc _ _ _)
  have N1 : ∀ (s : R') (Y : DerivedCategory (ModuleCat.{max v u} R')),
      resri.map (I.map (s • 𝟙 Y)) = s • 𝟙 (resri.obj (I.obj Y)) := by
    intro s Y
    rw [FlatHomology.derivedHom_map_smul_id.{v, u, u} ri s Y]
    exact FlatHomology.restrictScalars_mapDerivedCategory_map_smul_id.{v, u, u} ri s (I.obj Y)
  have N2 : ∀ {Y : DerivedCategory (ModuleCat.{max v u} R')} (h : Y ⟶ Y),
      resσ.map (Hp.map (resT.map h)) ≫ Φ Y = Φ Y ≫ resT.map (resri.map (I.map h)) := by
    intro Y h
    have e := γ.hom.naturality (I.map h)
    dsimp only [Functor.comp_map] at e
    calc resσ.map (Hp.map (resT.map h)) ≫ Φ Y
        = resσ.map (Hp.map (resT.map h) ≫ κY Y) ≫ γ.hom.app (I.obj Y) := by
          simp only [Φ, resσ.map_comp, Category.assoc]
      _ = resσ.map (κY Y ≫ resA.map (I.map h)) ≫ γ.hom.app (I.obj Y) := by rw [hκnat]
      _ = resσ.map (κY Y) ≫ resσ.map (resA.map (I.map h)) ≫ γ.hom.app (I.obj Y) := by
          rw [resσ.map_comp, Category.assoc]
      _ = Φ Y ≫ resT.map (resri.map (I.map h)) := by
          rw [e]
          simp only [Φ, Category.assoc]
          rfl
  have N3 : ∀ {Y : DerivedCategory (ModuleCat.{max v u} R')} (h : Y ⟶ Y),
      resσ.map (Hp.map (resT.map h)) ≫ Φ' Y = Φ' Y ≫ resT.map (resri.map (I.map h)) := by
    intro Y h
    have n1 : resσ.map (Hp.map (resT.map h)) ≫ ψY (resT.obj Y) =
        ψY (resT.obj Y) ≫ hom.map ((𝟙 (Opposite.op B'), resT.map h) :
          (Opposite.op B', resT.obj Y) ⟶ (Opposite.op B', resT.obj Y)) :=
      ψ.hom.naturality (resT.map h)
    have n2 : hom.map ((𝟙 (Opposite.op B'), resT.map h) :
          (Opposite.op B', resT.obj Y) ⟶ (Opposite.op B', resT.obj Y)) ≫
        (Ω.app (Opposite.op B', Y)).hom = (Ω.app (Opposite.op B', Y)).hom ≫
          resT.map (hom'.map ((𝟙 (Opposite.op (dR.obj B')), h) :
            (Opposite.op (dR.obj B'), Y) ⟶ (Opposite.op (dR.obj B'), Y))) := by
      have := Ω.hom.naturality ((𝟙 (Opposite.op B'), h) :
        (Opposite.op B', Y) ⟶ (Opposite.op B', Y))
      dsimp only [Functor.comp_map, Functor.prod_map, Functor.id_map, Functor.op_map] at this
      simp only [unop_id, CategoryTheory.Functor.map_id, op_id] at this
      exact this
    have n3 : hom'.map ((𝟙 (Opposite.op (dR.obj B')), h) :
          (Opposite.op (dR.obj B'), Y) ⟶ (Opposite.op (dR.obj B'), Y)) ≫ (mT' Y).inv =
        (mT' Y).inv ≫ resri.map (I.map h) := by
      let B'ri := (DerivedCategory.singleFunctor (ModuleCat.{max v u} R') 0).obj
        ((ModuleCat.restrictScalars (algebraMap R' (TensorProduct R A R'))).obj
          (ModuleCat.of (TensorProduct R A R') (ULift.{max v u} (TensorProduct R A R'))))
      let ψriY : resri.obj (I.obj Y) ⟶ hom'.obj (Opposite.op B'ri, Y) := ψri.hom.app Y
      let eY : hom'.obj (Opposite.op B'ri, Y) ⟶ hom'.obj (Opposite.op (dR.obj B'), Y) :=
        hom'.map ((Iso.prod (Iso.op dBAI) (Iso.refl Y)).hom)
      have hmh : (mT' Y).hom = ψriY ≫ eY := rfl
      have m1 : resri.map (I.map h) ≫ ψriY = ψriY ≫
          hom'.map ((𝟙 (Opposite.op B'ri), h) :
            (Opposite.op B'ri, Y) ⟶ (Opposite.op B'ri, Y)) :=
        ψri.hom.naturality h
      have m2 : hom'.map ((𝟙 (Opposite.op B'ri), h) :
            (Opposite.op B'ri, Y) ⟶ (Opposite.op B'ri, Y)) ≫ eY = eY ≫
            hom'.map ((𝟙 (Opposite.op (dR.obj B')), h) :
              (Opposite.op (dR.obj B'), Y) ⟶ (Opposite.op (dR.obj B'), Y)) := by
        simp only [eY]
        rw [← hom'.map_comp, ← hom'.map_comp]
        congr 1
        exact Prod.ext ((Category.id_comp _).trans (Category.comp_id _).symm)
          ((Category.comp_id _).trans (Category.id_comp _).symm)
      have m3 : resri.map (I.map h) ≫ (mT' Y).hom = (mT' Y).hom ≫
          hom'.map ((𝟙 (Opposite.op (dR.obj B')), h) :
            (Opposite.op (dR.obj B'), Y) ⟶ (Opposite.op (dR.obj B'), Y)) := by
        rw [hmh, reassoc_of% m1, m2, Category.assoc]
      rw [Iso.comp_inv_eq, Category.assoc, Iso.eq_inv_comp, m3]
    simp only [Φ', Category.assoc]
    rw [reassoc_of% n1, reassoc_of% n2, ← resT.map_comp, n3, resT.map_comp]
  let : Limits.PreservesFiniteLimits (FlatHomology.E.{u, v} (algebraMap R R')) :=
    extendScalars_preservesFiniteLimits_of_flat'.{u, v} _ hT
  have hw : IsIso w :=
    isIso_derivedHomBaseChangeAtAlgebra_of_flat.{u, u, u, v} dR cR lR hT hPC K b hK
  have hψY : ∀ Y, IsIso (ψY Y) := fun Y => inferInstanceAs (IsIso (ψ.hom.app Y))
  have hf₂ : IsIso f₂ := by infer_instance
  have hΦ' : ∀ Y, IsIso (Φ' Y) := fun Y => by infer_instance
  have hκiso : IsIso κ := conjugateEquiv_iso _ _ G.hom
  have hΦ : ∀ Y, IsIso (Φ Y) := fun Y => by
    have : IsIso (κY Y) := inferInstanceAs (IsIso (κ.app Y))
    infer_instance
  let V := resri.obj (I.obj (dR.obj K))
  let θ : resT.obj V ⟶ resT.obj V := inv (Φ' (dR.obj K)) ≫ Φ (dR.obj K)
  have hθ : ∀ s : R', resT.map (s • 𝟙 V) ≫ θ = θ ≫ resT.map (s • 𝟙 V) := by
    intro s
    rw [← N1 s (dR.obj K)]
    have a := N2 (s • 𝟙 (dR.obj K))
    have b := N3 (s • 𝟙 (dR.obj K))
    have b' : resT.map (resri.map (I.map (s • 𝟙 (dR.obj K)))) ≫ inv (Φ' (dR.obj K)) =
        inv (Φ' (dR.obj K)) ≫ resσ.map (Hp.map (resT.map (s • 𝟙 (dR.obj K)))) := by
      rw [IsIso.comp_inv_eq, Category.assoc, b, IsIso.inv_hom_id_assoc]
    simp only [θ, Category.assoc]
    rw [← a, reassoc_of% b']
  have hθiso : IsIso θ := by simp only [θ]; infer_instance
  have h' : adjT.homEquiv _ _ (c ≫ resri.map (δ' K)) = adjT.homEquiv _ _ f₂ ≫ θ := by
    rw [T1, T2]
    simp only [θ]
    exact (whisker_eq _ (IsIso.hom_inv_id_assoc (Φ' (dR.obj K)) (Φ (dR.obj K))).symm).trans
      (Category.assoc _ _ _).symm
  rw [hδ K]
  exact @FlatHomology.isIso_of_homEquiv_eq_comp _ _ _ _ (algebraMap R R') _ _ _
    (c ≫ resri.map (δ' K)) f₂ θ hθ h' hf₂ hθiso

/-- **The flat case of [Stacks, Tag 0BZM]**, at the module universe of the rings and the models
`Dualizing.flatDerivedExtension`: the case `v = 0` of
`Dualizing.isIso_derivedHomBaseChange_app_of_flat_flatModelsLarge`. -/
theorem isIso_derivedHomBaseChange_app_of_flat_flatModels
    (hPC : StacksDraft.PseudoCoherence.IsPseudoCoherent
      ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj
        ((ModuleCat.restrictScalars (algebraMap R A)).obj
          (ModuleCat.of A (ULift.{u} A)))))
    (K : DerivedCategory (ModuleCat.{u} R)) (b : ℤ) (hK : DerivedCategory.IsGE K b) :
    IsIso ((derivedHomBaseChange.{u, u, u, 0} hTor
      (flatDerivedExtension (algebraMap R R') hT) (flatDerivedExtensionFactors _ hT)
      (flatDerivedExtension_isLeftDerived _ hT)
      (flatDerivedExtension (algebraMap A (TensorProduct R A R')) hA)
      (flatDerivedExtensionFactors _ hA) (flatDerivedExtension_isLeftDerived _ hA)).app K) :=
  isIso_derivedHomBaseChange_app_of_flat_flatModelsLarge.{u, 0} hTor hT hA hPC K b hK

end

end Dualizing
