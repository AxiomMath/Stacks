module

public import StacksFrontier.RingTheory.Dualizing.TorsionComplete.AdicQuotientComparison
public import StacksFrontier.RingTheory.Dualizing.TorsionComplete.CompletedLocalCohomologyLimit
import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ConstantRingDerivedEquivalence
import StacksFrontier.Homology.HomComplex.DerivedAdjunction

/-!
# Unit-normalized derived limits for functors given by a derived tensor product

Let `I` be an ideal of a Noetherian ring `A` and let `Φ : Mod(A) ⥤ D(A)` be a functor naturally
isomorphic to `M ↦ C ⊗ᴸ M[0]` for a fixed object `C` of `D(A)`. For a finite `A`-module `M`, the
derived `I`-adic completion of `Φ(M)` is a derived limit of the tower `n ↦ Φ(M/IⁿM)`, with
projections whose composites with the completion unit are the maps `Φ(M ↠ M/IⁿM)`.

This is the argument of the normalized form of Stacks 0EEW part (1)
(`Dualizing.exists_isDerivedLimitWithProjections_of_uliftAdicQuotientIso`, where `Φ` is local
cohomology and `C` the extended Čech complex), with the only input it uses about `Φ` — the tensor
model — made a hypothesis. It applies equally to the third term of the localization triangle, by
`Stacks.LocalCohomology.exists_complementIso_tensor`, which is how Stacks 0BLX enters the proof of
Stacks 0EIF.

## Main results

* `Dualizing.exists_isDerivedLimitWithProjections_of_tensorIso` — the reflection of Stacks 0922
  onto the derived `I`-complete objects, as an adjunction, together with a unit-normalized
  derived-limit cone on the tower `n ↦ Φ(M/IⁿM)`, granted the universe-lift comparison of the
  adic quotient towers.

## Implementation notes

As in the source of the argument, the comparison of towers is carried out over `ULift A`, where
the normalized form of Stacks 0922 is available, and the universe boundary is crossed only by
natural isomorphisms in the module variable, which respect the legs `Φ(M ↠ M/IⁿM)` by
naturality. The reflection is returned as an adjunction `L ⊣ ι` so that a consumer can compare
it with any other model of derived completion by `CategoryTheory.Adjunction.leftAdjointUniq`.

## References

* [Stacks Project, Tag 0EEW](https://stacks.math.columbia.edu/tag/0EEW)
* [Stacks Project, Tag 0922](https://stacks.math.columbia.edu/tag/0922)
* [Stacks Project, Tag 0BLX](https://stacks.math.columbia.edu/tag/0BLX)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Dualizing

attribute [local instance] Dualizing.AdicQuotientComparison.derivedCategoryHasProductsNat

/-- **Unit-normalized derived limits for a functor given by a derived tensor product.** Let
`Φ : Mod(A) ⥤ D(A)` be naturally isomorphic to `M ↦ C ⊗ᴸ M[0]`, let `M` be a finite module over
the Noetherian ring `A`, and grant the universe-lift comparison `lam` of the adic quotient towers
together with its compatibility `hlam` with the quotient maps. Then the reflection `L ⊣ ι` of
Stacks 0922 onto the derived `I`-complete objects carries a derived-limit cone on the tower
`n ↦ Φ(M/IⁿM)` whose composites with the unit are the maps `Φ(M ↠ M/IⁿM)`. -/
theorem exists_isDerivedLimitWithProjections_of_tensorIso
    (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    (Φ : ModuleCat.{u} A ⥤ DerivedCategory (ModuleCat.{u} A))
    (C : DerivedCategory (ModuleCat.{u} A))
    (ψ : Φ ≅ DerivedCategory.singleFunctor (ModuleCat.{u} A) 0 ⋙
      (CochainComplex.DerivedTensor.canonicalDerivedTensorProduct A).tensor.obj C)
    (M : ModuleCat.{u} A) [Module.Finite A M]
    [IsNoetherianRing (ULift.{u} A)]
    [Module.Finite (ULift.{u} A) ((AdicKoszul.moduleUniverseLift.{u, u} A).obj M)]
    (hJB : (I.comap (ULift.ringEquiv.{u, u} (R := A)).toRingHom).FG)
    (lam : AlgebraicGeometry.ProEtale.adicQuotientModuleSystem A I M ⋙
        AdicKoszul.moduleUniverseLift.{u, u} A ≅
      AlgebraicGeometry.ProEtale.adicQuotientModuleSystem (ULift.{u} A)
        (I.comap (ULift.ringEquiv.{u, u} (R := A)).toRingHom)
        ((AdicKoszul.moduleUniverseLift.{u, u} A).obj M))
    (hlam : ∀ n : ℕ, (AdicKoszul.moduleUniverseLift.{u, u} A).map
          (ModuleCat.ofHom (I ^ n • (⊤ : Submodule A (M : Type u))).mkQ) ≫ lam.hom.app ⟨n⟩ =
        ModuleCat.ofHom ((I.comap (ULift.ringEquiv.{u, u} (R := A)).toRingHom) ^ n •
          (⊤ : Submodule (ULift.{u} A)
            (((AdicKoszul.moduleUniverseLift.{u, u} A).obj M : Type u)))).mkQ) :
    ∃ (L : DerivedCategory (ModuleCat.{u} A) ⥤ (derivedCompleteProperty.{u, u} A I).FullSubcategory)
      (adj : L ⊣ (derivedCompleteProperty.{u, u} A I).ι),
      ∃ q : ∀ n : ℕ, (L ⋙ (derivedCompleteProperty.{u, u} A I).ι).obj (Φ.obj M) ⟶
          (AlgebraicGeometry.ProEtale.adicQuotientModuleSystem A I M ⋙ Φ).obj ⟨n⟩,
        NoetherianAdicCompletion.IsDerivedLimitWithProjections
          (AlgebraicGeometry.ProEtale.adicQuotientModuleSystem A I M ⋙ Φ)
          ((L ⋙ (derivedCompleteProperty.{u, u} A I).ι).obj (Φ.obj M)) q ∧
        ∀ n : ℕ, adj.unit.app (Φ.obj M) ≫ q n =
            Φ.map (ModuleCat.ofHom (I ^ n • (⊤ : Submodule A (M : Type u))).mkQ) := by
  classical
  set P : ObjectProperty (DerivedCategory (ModuleCat.{u} A)) :=
    fun K ↦ IsDerivedComplete I K with hP
  set U := AdicKoszul.derivedUniverseLift.{u, u} A with hU
  set TA := CochainComplex.DerivedTensor.canonicalDerivedTensorProduct A with hTA
  set TB := CochainComplex.DerivedTensor.canonicalDerivedTensorProduct (ULift.{u} A) with hTB
  set SA := DerivedCategory.singleFunctor (ModuleCat.{u} A) 0 with hSA
  set SB := DerivedCategory.singleFunctor (ModuleCat.{u} (ULift.{u} A)) 0 with hSB
  let : (ModuleCat.uliftFunctor.{u,u} A).IsEquivalence :=
    Functor.isEquivalence_of_iso (NatIso.ofComponents (fun M =>
      { hom := ModuleCat.ofHom (ULift.moduleEquiv (R := A) (M := M)).toLinearMap
        inv := ModuleCat.ofHom (ULift.moduleEquiv (R := A) (M := M)).symm.toLinearMap })
      (fun _ => rfl) : ModuleCat.uliftFunctor.{u,u} A ≅ 𝟭 (ModuleCat.{u} A)).symm
  let : (ModuleCat.restrictScalars
      (ULift.ringEquiv : ULift.{u} A ≃+* A).toRingHom).IsEquivalence := by
    show (StacksDraft.DerivedHom.uliftModuleEquivalence.{u,u,u} A).inverse.IsEquivalence
    infer_instance
  let : (AdicKoszul.moduleUniverseLift.{u,u} A).IsEquivalence := by
    show (ModuleCat.uliftFunctor.{u,u} A ⋙ ModuleCat.restrictScalars
      (ULift.ringEquiv : ULift.{u} A ≃+* A).toRingHom).IsEquivalence
    infer_instance
  let : U.IsEquivalence :=
    Stacks.Injectives.mapDerivedCategory_isEquivalence (AdicKoszul.moduleUniverseLift.{u,u} A)
  obtain ⟨tUFI⟩ := AdicCompletionTor.nonempty_tensorUliftFunctorIso A TA C
  set Xi : Φ ⋙ U ≅
      AdicKoszul.moduleUniverseLift.{u, u} A ⋙ SB ⋙ TB.tensor.obj (U.obj C) :=
    Functor.isoWhiskerRight ψ U ≪≫ Functor.isoWhiskerLeft SA tUFI ≪≫
      Functor.isoWhiskerRight
        ((AdicKoszul.moduleUniverseLift.{u, u} A).mapDerivedCategorySingleFunctor 0)
        (TB.tensor.obj (U.obj C)) with hXi
  obtain ⟨L, adj, π, hlim, hunit⟩ :=
    NoetherianAdicCompletion.idealPowerDerivedLimit_isLeftAdjoint.{u, u} A I TB
  set X := Φ.obj M with hX
  set θ := Xi.app M with hθ
  have hθhom : θ.hom = Xi.hom.app M := rfl
  set eT : NoetherianAdicCompletion.idealPowerQuotientSystem
        (I.comap (ULift.ringEquiv.{u, u} (R := A)).toRingHom) ⋙ TB.tensor.obj (U.obj X) ≅
      NoetherianAdicCompletion.idealPowerQuotientSystem
        (I.comap (ULift.ringEquiv.{u, u} (R := A)).toRingHom) ⋙
        TB.tensor.obj ((TB.tensor.obj (U.obj C)).obj
          (SB.obj ((AdicKoszul.moduleUniverseLift.{u, u} A).obj M))) :=
    Functor.isoWhiskerLeft _ (TB.tensor.mapIso θ) with heT
  have hlim₁ := (hlim X).ofNatIso eT
  set w := θ.inv ≫ U.map (adj.unit.app X) with hw
  have hunitw : U.map (adj.unit.app X) = θ.hom ≫ w := by
    rw [hw, ← Category.assoc, θ.hom_inv_id, Category.id_comp]
  have hw₁ : ∀ n : ℕ, w ≫ ((π n).app X ≫ eT.hom.app ⟨n⟩) =
      (NoetherianAdicCompletion.derivedReductionMap
          (I.comap (ULift.ringEquiv.{u, u} (R := A)).toRingHom) TB n).app
        ((TB.tensor.obj (U.obj C)).obj
          (SB.obj ((AdicKoszul.moduleUniverseLift.{u, u} A).obj M))) := by
    intro n
    have hnat2 : (NoetherianAdicCompletion.derivedReductionMap
          (I.comap (ULift.ringEquiv.{u, u} (R := A)).toRingHom) TB n).app (U.obj X) ≫
        (TB.tensor.map θ.hom).app
          ((NoetherianAdicCompletion.idealPowerQuotientSystem
            (I.comap (ULift.ringEquiv.{u, u} (R := A)).toRingHom)).obj ⟨n⟩) =
        θ.hom ≫ (NoetherianAdicCompletion.derivedReductionMap
          (I.comap (ULift.ringEquiv.{u, u} (R := A)).toRingHom) TB n).app
            ((TB.tensor.obj (U.obj C)).obj
              (SB.obj ((AdicKoszul.moduleUniverseLift.{u, u} A).obj M))) :=
      ((NoetherianAdicCompletion.derivedReductionMap
        (I.comap (ULift.ringEquiv.{u, u} (R := A)).toRingHom) TB n).naturality θ.hom).symm
    have heTapp : eT.hom.app ⟨n⟩ = (TB.tensor.map θ.hom).app
        ((NoetherianAdicCompletion.idealPowerQuotientSystem
          (I.comap (ULift.ringEquiv.{u, u} (R := A)).toRingHom)).obj ⟨n⟩) := rfl
    rw [hw, Category.assoc, ← Category.assoc (U.map (adj.unit.app X)), hunit X n, heTapp,
      hnat2, ← Category.assoc, θ.inv_hom_id, Category.id_comp]
  obtain ⟨qB, hqB, hqBnorm⟩ :=
    Dualizing.AdicQuotientComparison.isDerivedLimitWithProjections_tensor_adicQuotient
      (ULift.{u} A) (I.comap (ULift.ringEquiv.{u, u} (R := A)).toRingHom) hJB
      ((AdicKoszul.moduleUniverseLift.{u, u} A).obj M) (U.obj C)
      (U.obj ((L ⋙ P.ι).obj X)) _ w hlim₁ hw₁
  have hqBnorm' : ∀ n : ℕ, w ≫ qB n =
      (TB.tensor.obj (U.obj C)).map (SB.map (ModuleCat.ofHom
        ((I.comap (ULift.ringEquiv.{u, u} (R := A)).toRingHom) ^ n •
          (⊤ : Submodule (ULift.{u} A)
            (((AdicKoszul.moduleUniverseLift.{u, u} A).obj M : Type u)))).mkQ)) := hqBnorm
  set Phi : AlgebraicGeometry.ProEtale.adicQuotientModuleSystem (ULift.{u} A)
          (I.comap (ULift.ringEquiv.{u, u} (R := A)).toRingHom)
          ((AdicKoszul.moduleUniverseLift.{u, u} A).obj M) ⋙
        SB ⋙ TB.tensor.obj (U.obj C) ≅
        (AlgebraicGeometry.ProEtale.adicQuotientModuleSystem A I M ⋙ Φ) ⋙ U :=
    Functor.isoWhiskerRight lam.symm (SB ⋙ TB.tensor.obj (U.obj C)) ≪≫
      Functor.isoWhiskerLeft (AlgebraicGeometry.ProEtale.adicQuotientModuleSystem A I M) Xi.symm
    with hPhi
  have hlim₂ := hqB.ofNatIso Phi
  have hnorm : ∀ n : ℕ, U.map (adj.unit.app X) ≫ (qB n ≫ Phi.hom.app ⟨n⟩) =
      U.map (Φ.map
        (ModuleCat.ofHom (I ^ n • (⊤ : Submodule A (M : Type u))).mkQ)) := by
    intro n
    have hXinat : U.map (Φ.map
          (ModuleCat.ofHom (I ^ n • (⊤ : Submodule A (M : Type u))).mkQ)) ≫
        Xi.hom.app ((AlgebraicGeometry.ProEtale.adicQuotientModuleSystem A I M).obj ⟨n⟩) =
        Xi.hom.app M ≫ (TB.tensor.obj (U.obj C)).map (SB.map
          ((AdicKoszul.moduleUniverseLift.{u, u} A).map
            (ModuleCat.ofHom (I ^ n • (⊤ : Submodule A (M : Type u))).mkQ))) :=
      Xi.hom.naturality _
    have hPhiapp : Phi.hom.app ⟨n⟩ =
        (TB.tensor.obj (U.obj C)).map (SB.map (lam.inv.app ⟨n⟩)) ≫
          Xi.inv.app ((AlgebraicGeometry.ProEtale.adicQuotientModuleSystem A I M).obj ⟨n⟩) := rfl
    have hmap : (TB.tensor.obj (U.obj C)).map (SB.map
          ((AdicKoszul.moduleUniverseLift.{u, u} A).map
            (ModuleCat.ofHom (I ^ n • (⊤ : Submodule A (M : Type u))).mkQ) ≫
              lam.hom.app ⟨n⟩)) ≫
        (TB.tensor.obj (U.obj C)).map (SB.map (lam.inv.app ⟨n⟩)) ≫
          Xi.inv.app ((AlgebraicGeometry.ProEtale.adicQuotientModuleSystem A I M).obj ⟨n⟩) =
        (TB.tensor.obj (U.obj C)).map (SB.map
          ((AdicKoszul.moduleUniverseLift.{u, u} A).map
            (ModuleCat.ofHom (I ^ n • (⊤ : Submodule A (M : Type u))).mkQ))) ≫
          Xi.inv.app ((AlgebraicGeometry.ProEtale.adicQuotientModuleSystem A I M).obj ⟨n⟩) := by
      rw [← Category.assoc, ← Functor.map_comp, ← Functor.map_comp]
      refine congrArg (fun g ↦ (TB.tensor.obj (U.obj C)).map (SB.map g) ≫
        Xi.inv.app ((AlgebraicGeometry.ProEtale.adicQuotientModuleSystem A I M).obj ⟨n⟩)) ?_
      refine (Category.assoc _ _ _).trans ?_
      exact (congrArg (fun g ↦ (AdicKoszul.moduleUniverseLift.{u, u} A).map
        (ModuleCat.ofHom (I ^ n • (⊤ : Submodule A (M : Type u))).mkQ) ≫ g)
        (lam.hom_inv_id_app ⟨n⟩)).trans (Category.comp_id _)
    rw [hunitw, Category.assoc, ← Category.assoc w, hqBnorm' n, ← hlam n, hPhiapp]
    refine (congrArg (fun g ↦ θ.hom ≫ g) hmap).trans ?_
    rw [hθhom]
    refine (Category.assoc _ _ _).symm.trans ?_
    rw [← hXinat]
    refine (Category.assoc _ _ _).trans ?_
    exact (congrArg (fun g ↦ U.map (Φ.map
        (ModuleCat.ofHom (I ^ n • (⊤ : Submodule A (M : Type u))).mkQ)) ≫ g)
      (Xi.hom_inv_id_app _)).trans (Category.comp_id _)
  refine ⟨L, adj, fun n ↦ U.preimage (qB n ≫ Phi.hom.app ⟨n⟩), ?_, ?_⟩
  · have heq : (fun n : ℕ ↦ U.map (U.preimage (qB n ≫ Phi.hom.app ⟨n⟩))) =
        fun n : ℕ ↦ qB n ≫ Phi.hom.app ⟨n⟩ := by
      funext n
      exact U.map_preimage _
    refine NoetherianAdicCompletion.isDerivedLimitWithProjections_of_map_of_equivalence U
      (AlgebraicGeometry.ProEtale.adicQuotientModuleSystem A I M ⋙ Φ) _ _ ?_
    rw [heq]
    exact hlim₂
  · intro n
    refine U.map_injective ?_
    rw [U.map_comp, U.map_preimage]
    exact hnorm n

end Dualizing

end
