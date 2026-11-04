module

public import Mathlib.RingTheory.AdicCompletion.LocalRing
public import StacksFrontier.RingTheory.Dualizing.DerivedHomDuality.ExtComparison
public import StacksFrontier.RingTheory.Dualizing.UbiquityDualizingComplexes.AdicCompletion
public import StacksFrontier.RingTheory.LocalCohomology.LocalDualityTransfer.CompleteLocal
public import StacksFrontier.RingTheory.LocalCohomology.LocalDualityTransfer.ExtBaseChange
public import StacksFrontier.RingTheory.LocalCohomology.LocalDualityTransfer.Matlis
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.Triangles
public import StacksFrontier.RingTheory.Dualizing.DerivedLocalization
public import StacksFrontier.RingTheory.Dualizing.LocalizationCriterion
import all StacksFrontier.RingTheory.LocalCohomology.FaltingsAnnihilator

/-!
# Local duality at a prime, natural in the module

Let `A` be a Noetherian ring with a dualizing complex `ω`, let `q` be a prime, `B = A_q` and
`Ŝ` the completion of `B` at its maximal ideal. Base change of `ω` to `Ŝ` is a dualizing
complex over the complete local ring `Ŝ`, so over `Ŝ` local duality holds naturally in the source
(`Dualizing.bijective_homology_map_localCohomology_map`). Combined with flat base change of Ext
along `A → Ŝ` this identifies, naturally in a finite `A`-module `N`, the Matlis dual over `Ŝ`
of `H^e_{𝔪_Ŝ}(Ŝ ⊗_A N)` with `Ŝ ⊗_A Ext^j_A(N, ω)` for a suitable `j`.

This is the identification of [Stacks, Tag 0AAK] at a prime used in the proof of
[Stacks, Tag 0EFX], with the naturality in `N` that the proof needs.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits IsLocalRing Opposite
open scoped ChangeOfRings

attribute [local instance] HasDerivedCategory.standard
  Dualizing.hasProductsOfShape_nat_derivedCategory

universe u

namespace Stacks.LocalCohomology.LocalDualityTransfer

variable {A : Type u} [CommRing A] [IsNoetherianRing A] (q : PrimeSpectrum A)

/-- The localization `A_q`. -/
abbrev Bq := Localization.AtPrime q.asIdeal

/-- The completion of `A_q` at its maximal ideal. -/
abbrev Sq := AdicCompletion (maximalIdeal (Bq q)) (Bq q)

/-- The localization `A_q` of a Noetherian ring is Noetherian. -/
instance : IsNoetherianRing (Bq q) :=
  IsLocalization.isNoetherianRing q.asIdeal.primeCompl _ inferInstance

/-- The completion `Ŝ` of `A_q` is Noetherian. -/
instance : IsNoetherianRing (Sq q) := AdicCompletion.isNoetherianRing _

/-- The completion `Ŝ` of `A_q` is a local ring. -/
instance : IsLocalRing (Sq q) := AdicCompletion.isLocalRing_of_fg (IsNoetherian.noetherian _)

/-- The completion `Ŝ` is complete with respect to its maximal ideal. -/
instance : IsAdicComplete (maximalIdeal (Sq q)) (Sq q) :=
  AdicCompletion.isAdicComplete_of_fg (IsNoetherian.noetherian _)

/-- The completion `Ŝ` of `A_q` is flat over `A_q`. -/
instance : Module.Flat (Bq q) (Sq q) := AdicCompletion.flat_of_isNoetherian _

/-- The completion `Ŝ` of `A_q` is flat over `A`. -/
instance : Module.Flat A (Sq q) := Module.Flat.trans A (Bq q) (Sq q)

/-- The ring map `A → Ŝ` is flat. -/
theorem flat_algebraMap_Sq : (algebraMap A (Sq q)).Flat :=
  RingHom.flat_algebraMap_iff.mpr inferInstance

/-- The base change of `ω` to `Ŝ`. -/
abbrev omegaSq (ω : DerivedCategory (ModuleCat.{u} A)) : DerivedCategory (ModuleCat.{u} (Sq q)) :=
  (flatDerived (algebraMap A (Sq q)) (flat_algebraMap_Sq q)).obj ω

/-- The base change of a dualizing complex to the completion of a localization is dualizing. -/
theorem isDualizingComplex_omegaSq (ω : DerivedCategory (ModuleCat.{u} A))
    (hω : Dualizing.IsDualizingComplex ω) : Dualizing.IsDualizingComplex (omegaSq q ω) := by
  let f₁ := algebraMap A (Bq q)
  let f₂ := algebraMap (Bq q) (Sq q)
  have hf₁ : f₁.Flat := RingHom.flat_algebraMap_iff.mpr inferInstance
  have hf₂ : f₂.Flat := RingHom.flat_algebraMap_iff.mpr inferInstance
  have h₁ : Dualizing.IsDualizingComplex ((flatDerived f₁ hf₁).obj ω) :=
    Stacks.LocalCohomology.isDualizingComplex_localizedMap q ω hω
  have h₂ : Dualizing.IsDualizingComplex ((flatDerived f₂ hf₂).obj ((flatDerived f₁ hf₁).obj ω)) :=
    Dualizing.isDualizingComplex_adicCompletion _ _ h₁
  let : PreservesFiniteLimits (ModuleCat.extendScalars.{u, u, u} f₁) :=
    extendScalars_preservesFiniteLimits_of_flat' f₁ hf₁
  let : PreservesFiniteLimits (ModuleCat.extendScalars.{u, u, u} f₂) :=
    extendScalars_preservesFiniteLimits_of_flat' f₂ hf₂
  let : PreservesFiniteLimits (ModuleCat.extendScalars.{u, u, u} (f₂.comp f₁)) :=
    extendScalars_preservesFiniteLimits_of_flat' _ (hf₁.comp hf₂)
  let e₁ := Stacks.Cohomology.PerfectComplexTriangles.mapDerivedCategoryIsoOfNatIso
    (ModuleCat.extendScalars.{u, u, u} (f₂.comp f₁))
    (ModuleCat.extendScalars.{u, u, u} f₁ ⋙ ModuleCat.extendScalars.{u, u, u} f₂)
    (ModuleCat.extendScalarsComp f₁ f₂)
  let e₂ := Stacks.Cohomology.PerfectComplexTriangles.mapDerivedCategoryCompIso
    (ModuleCat.extendScalars.{u, u, u} f₁) (ModuleCat.extendScalars.{u, u, u} f₂)
  have key : Dualizing.IsDualizingComplex
      ((ModuleCat.extendScalars.{u, u, u} (f₂.comp f₁)).mapDerivedCategory.obj ω) :=
    Stacks.LocalCohomology.isDualizingComplex_of_iso ((e₁ ≪≫ e₂).app ω).symm h₂
  unfold omegaSq flatDerived
  simp only [IsScalarTower.algebraMap_eq A (Bq q) (Sq q)]
  exact key

section Duality

variable (ω : DerivedCategory (ModuleCat.{u} A)) (hω : Dualizing.IsDualizingComplex ω)

/-- The data realizing `RΓ_𝔪` of the shifts of `ω_Ŝ`: an injective module containing the residue
field of `Ŝ` and the degree in which it sits. -/
def hullData : Σ' (E : ModuleCat.{u} (Sq q)) (_ : Injective E)
    (ι : ResidueField (Sq q) →ₗ[Sq q] E) (_ : Function.Injective ι) (d : ℤ), ∀ j : ℤ,
      Nonempty ((Dualizing.derivedPowerTorsionProperty (Sq q) (maximalIdeal (Sq q))
          (IsNoetherian.noetherian _)).ι.obj
        ((Dualizing.localCohomologyFunctor (Sq q) (maximalIdeal (Sq q))
          (IsNoetherian.noetherian _)).obj ((omegaSq q ω)⟦j⟧)) ≅
          (DerivedCategory.singleFunctor (ModuleCat.{u} (Sq q)) (d - j)).obj E) := by
  have h := Dualizing.exists_localCohomology_iso_single_injectiveHull (omegaSq q ω)
    (isDualizingComplex_omegaSq q ω hω)
  exact ⟨h.choose, h.choose_spec.choose, h.choose_spec.choose_spec.choose,
    h.choose_spec.choose_spec.choose_spec.choose,
    h.choose_spec.choose_spec.choose_spec.choose_spec.choose,
    h.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec⟩

/-- The injective hull `E` of the residue field of `Ŝ`. -/
abbrev hullE : ModuleCat.{u} (Sq q) := (hullData q ω hω).1

/-- The module `hullE` is an injective object of `ModuleCat (Sq q)`. -/
instance : Injective (hullE q ω hω) := (hullData q ω hω).2.1

/-- The degree `d` with `RΓ_𝔪(ω_Ŝ⟦j⟧) ≅ E[-(d - j)]`. -/
abbrev hullDeg : ℤ := (hullData q ω hω).2.2.2.2.1

/-- The source complex `Ŝ ⊗_A N` placed in degree zero, as an object of `D(Ŝ)`. -/
abbrev srcSq (N : ModuleCat.{u} A) : DerivedCategory (ModuleCat.{u} (Sq q)) :=
  (flatDerived (algebraMap A (Sq q)) (flat_algebraMap_Sq q)).obj
    ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj N)

/-- The local cohomology module `H^e_𝔪(Ŝ ⊗ᴸ N)` over `Ŝ`, in the coreflection model. -/
abbrev locSq (e : ℤ) (N : ModuleCat.{u} A) : ModuleCat.{u} (Sq q) :=
  (DerivedCategory.homologyFunctor (ModuleCat.{u} (Sq q)) e).obj
    ((Dualizing.derivedPowerTorsionProperty (Sq q) (maximalIdeal (Sq q))
        (IsNoetherian.noetherian _)).ι.obj
      ((Dualizing.localCohomologyFunctor (Sq q) (maximalIdeal (Sq q))
        (IsNoetherian.noetherian _)).obj (srcSq q N)))

/-- The map induced on `H^e_𝔪(Ŝ ⊗ᴸ -)` by a map of `A`-modules. -/
abbrev locSqMap (e : ℤ) {N N' : ModuleCat.{u} A} (g : N ⟶ N') : locSq q e N ⟶ locSq q e N' :=
  (DerivedCategory.homologyFunctor (ModuleCat.{u} (Sq q)) e).map
    ((Dualizing.derivedPowerTorsionProperty (Sq q) (maximalIdeal (Sq q))
        (IsNoetherian.noetherian _)).ι.map
      ((Dualizing.localCohomologyFunctor (Sq q) (maximalIdeal (Sq q))
        (IsNoetherian.noetherian _)).map
        ((flatDerived (algebraMap A (Sq q)) (flat_algebraMap_Sq q)).map
          ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).map g))))

/-- **Local duality on `Ŝ`, natural in the source, as an additive equivalence.** Maps
`Ŝ ⊗ᴸ N ⟶ ω_Ŝ⟦n⟧` in `D(Ŝ)` correspond to `Ŝ`-linear maps `H^{d-n}_𝔪(Ŝ ⊗ᴸ N) → E`. -/
def dualityAddEquiv (n : ℤ) (N : ModuleCat.{u} A) :
    (srcSq q N ⟶ (omegaSq q ω)⟦n⟧) ≃+ (locSq q (hullDeg q ω hω - n) N →ₗ[Sq q] hullE q ω hω) :=
  let β := ((hullData q ω hω).2.2.2.2.2 n).some
  have hX : IsDerivedComplete (maximalIdeal (Sq q)) ((omegaSq q ω)⟦n⟧) :=
    Dualizing.isDerivedComplete_of_finite_homology _ _
      (Dualizing.isDualizingComplex_shift (omegaSq q ω) (isDualizingComplex_omegaSq q ω hω)
        n).finiteCohomology
  have b := Dualizing.bijective_homology_map_localCohomology_map (Sq q) (maximalIdeal (Sq q))
    (IsNoetherian.noetherian _) ((omegaSq q ω)⟦n⟧) hX (hullE q ω hω)
    (hullDeg q ω hω - n) β (srcSq q N)
  letI : (Dualizing.localCohomologyFunctor (Sq q) (maximalIdeal (Sq q))
      (IsNoetherian.noetherian _)).Additive :=
    (Dualizing.localCohomologyAdjunction (Sq q) (maximalIdeal (Sq q))
      (IsNoetherian.noetherian _)).right_adjoint_additive
  let H := DerivedCategory.homologyFunctor (ModuleCat.{u} (Sq q)) (hullDeg q ω hω - n)
  let ι := (Dualizing.derivedPowerTorsionProperty (Sq q) (maximalIdeal (Sq q))
    (IsNoetherian.noetherian _)).ι
  let G := Dualizing.localCohomologyFunctor (Sq q) (maximalIdeal (Sq q))
    (IsNoetherian.noetherian _)
  let φ : (srcSq q N ⟶ (omegaSq q ω)⟦n⟧) →+ (locSq q (hullDeg q ω hω - n) N ⟶ hullE q ω hω) :=
    (Preadditive.rightComp _ (H.map β.hom ≫
      (DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat.{u} (Sq q))
        (hullDeg q ω hω - n)).hom.app (hullE q ω hω))).comp
      (H.mapAddHom.comp (ι.mapAddHom.comp G.mapAddHom))
  (AddEquiv.ofBijective φ b).trans ModuleCat.homAddEquiv

/-- Naturality of `dualityAddEquiv` in the module. -/
theorem dualityAddEquiv_naturality (n : ℤ) {N N' : ModuleCat.{u} A} (g : N ⟶ N')
    (ψ : srcSq q N' ⟶ (omegaSq q ω)⟦n⟧) :
    dualityAddEquiv q ω hω n N
        ((flatDerived (algebraMap A (Sq q)) (flat_algebraMap_Sq q)).map
          ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).map g) ≫ ψ) =
      dualityAddEquiv q ω hω n N' ψ ∘ₗ (locSqMap q (hullDeg q ω hω - n) g).hom := by
  let H := DerivedCategory.homologyFunctor (ModuleCat.{u} (Sq q)) (hullDeg q ω hω - n)
  let ι := (Dualizing.derivedPowerTorsionProperty (Sq q) (maximalIdeal (Sq q))
    (IsNoetherian.noetherian _)).ι
  let G := Dualizing.localCohomologyFunctor (Sq q) (maximalIdeal (Sq q))
    (IsNoetherian.noetherian _)
  let a := (flatDerived (algebraMap A (Sq q)) (flat_algebraMap_Sq q)).map
    ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).map g)
  let c := H.map ((hullData q ω hω).2.2.2.2.2 n).some.hom ≫
    (DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat.{u} (Sq q))
      (hullDeg q ω hω - n)).hom.app (hullE q ω hω)
  show (H.map (ι.map (G.map (a ≫ ψ))) ≫ c).hom =
    (H.map (ι.map (G.map ψ)) ≫ c).hom ∘ₗ (H.map (ι.map (G.map a))).hom
  rw [G.map_comp, ι.map_comp, H.map_comp, Category.assoc]
  rfl

/-- `Ext^n` into `ω`, as a contravariant functor of the module. -/
abbrev extOmega (n : ℤ) : (ModuleCat.{u} A)ᵒᵖ ⥤ ModuleCat.{u} A :=
  (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).op ⋙
    Dualizing.dualizingDerivedHomFunctor.{u, u} A ω ⋙
      DerivedCategory.homologyFunctor (ModuleCat.{u} A) n

/-- **Maps into `ω_Ŝ⟦n⟧` are the base change of `Ext^n` into `ω`**, naturally in the finite
module: `Hom_{D(Ŝ)}(Ŝ ⊗ᴸ N, ω_Ŝ⟦n⟧) ≅ Ŝ ⊗_A Extⁿ_A(N, ω)`. -/
def extAddEquiv (hω' : ∃ b : ℤ, ω.IsGE b) (n : ℤ) (N : ModuleCat.{u} A) [Module.Finite A N] :
    (srcSq q N ⟶ (omegaSq q ω)⟦n⟧) ≃+
      (ModuleCat.extendScalars.{u, u, u} (algebraMap A (Sq q))).obj ((extOmega ω n).obj (op N)) :=
  ((((StacksDraft.DerivedHom.ExtComparison.extCohomologyComparisonIso.{u, u} (Sq q)
      (omegaSq q ω) n).app (op (srcSq q N))).toLinearEquiv.toAddEquiv.trans
    (ULift.moduleEquiv (R := Sq q)).toAddEquiv).trans
    (extFlatBaseChangeIso (algebraMap A (Sq q)) (flat_algebraMap_Sq q) ω
      ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj N)
      (Dualizing.isPseudoCoherent_singleFunctor_obj N) hω' n).symm.toLinearEquiv.toAddEquiv)

/-- Naturality of `extAddEquiv` in the module. -/
theorem extAddEquiv_naturality (hω' : ∃ b : ℤ, ω.IsGE b) (n : ℤ) {N N' : ModuleCat.{u} A}
    [Module.Finite A N] [Module.Finite A N'] (g : N ⟶ N')
    (ψ : srcSq q N' ⟶ (omegaSq q ω)⟦n⟧) :
    extAddEquiv q ω hω' n N
        ((flatDerived (algebraMap A (Sq q)) (flat_algebraMap_Sq q)).map
          ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).map g) ≫ ψ) =
      ((ModuleCat.extendScalars.{u, u, u} (algebraMap A (Sq q))).map
        ((extOmega ω n).map g.op)).hom (extAddEquiv q ω hω' n N' ψ) := by
  set F := flatDerived (algebraMap A (Sq q)) (flat_algebraMap_Sq q)
  set a := F.map ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).map g)
  have h1 := congrArg (fun f ↦ f.hom ψ)
    ((StacksDraft.DerivedHom.ExtComparison.extCohomologyComparisonIso.{u, u} (Sq q)
      (omegaSq q ω) n).hom.naturality a.op)
  let e : ∀ (M : ModuleCat.{u} A) [Module.Finite A M],
      (ModuleCat.extendScalars.{u, u, u} (algebraMap A (Sq q))).obj ((extOmega ω n).obj (op M)) ≅
        (DerivedCategory.homologyFunctor (ModuleCat.{u} (Sq q)) n).obj
          ((Dualizing.dualizingDerivedHomFunctor.{u, u} (Sq q) (omegaSq q ω)).obj
            (op (srcSq q M))) := fun M _ ↦
    extFlatBaseChangeIso (algebraMap A (Sq q)) (flat_algebraMap_Sq q) ω
      ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M)
      (Dualizing.isPseudoCoherent_singleFunctor_obj M) hω' n
  have h2' : (e N').inv ≫ (ModuleCat.extendScalars.{u, u, u} (algebraMap A (Sq q))).map
      ((extOmega ω n).map g.op) =
      (DerivedCategory.homologyFunctor (ModuleCat.{u} (Sq q)) n).map
        ((Dualizing.dualizingDerivedHomFunctor.{u, u} (Sq q) (omegaSq q ω)).map a.op) ≫
        (e N).inv := by
    rw [Iso.inv_comp_eq, ← Category.assoc, Iso.eq_comp_inv]
    exact extFlatBaseChangeIso_naturality (algebraMap A (Sq q)) (flat_algebraMap_Sq q) ω
      ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).map g)
      (Dualizing.isPseudoCoherent_singleFunctor_obj N')
      (Dualizing.isPseudoCoherent_singleFunctor_obj N) hω' n
  show (e N).inv (ULift.down
      (((StacksDraft.DerivedHom.ExtComparison.extCohomologyComparisonIso.{u, u} (Sq q)
        (omegaSq q ω) n).hom.app (op (srcSq q N))).hom (a ≫ ψ))) =
    ((ModuleCat.extendScalars.{u, u, u} (algebraMap A (Sq q))).map
      ((extOmega ω n).map g.op)).hom ((e N').inv (ULift.down
        (((StacksDraft.DerivedHom.ExtComparison.extCohomologyComparisonIso.{u, u} (Sq q)
          (omegaSq q ω) n).hom.app (op (srcSq q N'))).hom ψ)))
  have h1' : ((StacksDraft.DerivedHom.ExtComparison.extCohomologyComparisonIso.{u, u} (Sq q)
        (omegaSq q ω) n).hom.app (op (srcSq q N))).hom (a ≫ ψ) =
      ULift.up (((DerivedCategory.homologyFunctor (ModuleCat.{u} (Sq q)) n).map
        ((Dualizing.dualizingDerivedHomFunctor.{u, u} (Sq q) (omegaSq q ω)).map a.op)).hom
        (ULift.down (((StacksDraft.DerivedHom.ExtComparison.extCohomologyComparisonIso.{u, u}
          (Sq q) (omegaSq q ω) n).hom.app (op (srcSq q N'))).hom ψ))) := h1
  rw [h1']
  exact (congrArg (fun f ↦ f.hom (ULift.down
    (((StacksDraft.DerivedHom.ExtComparison.extCohomologyComparisonIso.{u, u} (Sq q)
      (omegaSq q ω) n).hom.app (op (srcSq q N'))).hom ψ))) h2').symm

/-- **The Matlis dual of `H^{d-n}_𝔪(Ŝ ⊗ N)` is `Ŝ ⊗_A Extⁿ_A(N, ω)`**, naturally in the finite
module `N`. -/
def matlisExtAddEquiv (hω' : ∃ b : ℤ, ω.IsGE b) (n : ℤ) (N : ModuleCat.{u} A)
    [Module.Finite A N] :
    (locSq q (hullDeg q ω hω - n) N →ₗ[Sq q] hullE q ω hω) ≃+
      (ModuleCat.extendScalars.{u, u, u} (algebraMap A (Sq q))).obj ((extOmega ω n).obj (op N)) :=
  (dualityAddEquiv q ω hω n N).symm.trans (extAddEquiv q ω hω' n N)

/-- Naturality of `matlisExtAddEquiv` in the module. -/
theorem matlisExtAddEquiv_naturality (hω' : ∃ b : ℤ, ω.IsGE b) (n : ℤ) {N N' : ModuleCat.{u} A}
    [Module.Finite A N] [Module.Finite A N'] (g : N ⟶ N')
    (φ : locSq q (hullDeg q ω hω - n) N' →ₗ[Sq q] hullE q ω hω) :
    matlisExtAddEquiv q ω hω hω' n N (φ ∘ₗ (locSqMap q (hullDeg q ω hω - n) g).hom) =
      ((ModuleCat.extendScalars.{u, u, u} (algebraMap A (Sq q))).map
        ((extOmega ω n).map g.op)).hom (matlisExtAddEquiv q ω hω hω' n N' φ) := by
  obtain ⟨ψ, rfl⟩ := (dualityAddEquiv q ω hω n N').surjective φ
  simp only [matlisExtAddEquiv, AddEquiv.trans_apply, AddEquiv.symm_apply_apply]
  rw [← dualityAddEquiv_naturality q ω hω n g ψ, AddEquiv.symm_apply_apply,
    extAddEquiv_naturality]

omit [IsNoetherianRing A] in
/-- Extension of scalars agrees with the tensor product for the algebra structure, naturally:
the two are intertwined by `Dualizing.extendScalarsTensorIso` and `LinearMap.baseChange`. -/
theorem extendScalarsTensorIso_naturality {P P' : ModuleCat.{u} A} (φ : P ⟶ P') :
    (ModuleCat.extendScalars.{u, u, u} (algebraMap A (Sq q))).map φ ≫
        (Dualizing.extendScalarsTensorIso.{u, u} (Sq q) P').hom =
      (Dualizing.extendScalarsTensorIso.{u, u} (Sq q) P).hom ≫
        ModuleCat.ofHom (φ.hom.baseChange (Sq q)) := by
  ext m
  show (Dualizing.extendScalarsTensorIso.{u, u} (Sq q) P').hom
      ((1 : Sq q) ⊗ₜ[A, algebraMap A (Sq q)] φ.hom m) =
    φ.hom.baseChange (Sq q) ((Dualizing.extendScalarsTensorIso.{u, u} (Sq q) P).hom
      ((1 : Sq q) ⊗ₜ[A, algebraMap A (Sq q)] m))
  rw [Dualizing.extendScalarsTensorIso_hom_tmul, Dualizing.extendScalarsTensorIso_hom_tmul,
    LinearMap.baseChange_tmul]

/-- The Matlis dual of `H^{d-n}_𝔪(Ŝ ⊗ N)` as the tensor product `Ŝ ⊗_A Extⁿ_A(N, ω)`. -/
def matlisTensorAddEquiv (hω' : ∃ b : ℤ, ω.IsGE b) (n : ℤ) (N : ModuleCat.{u} A)
    [Module.Finite A N] :
    (locSq q (hullDeg q ω hω - n) N →ₗ[Sq q] hullE q ω hω) ≃+
      TensorProduct A (Sq q) ((extOmega ω n).obj (op N)) :=
  (matlisExtAddEquiv q ω hω hω' n N).trans
    (Dualizing.extendScalarsTensorIso.{u, u} (Sq q) _).toLinearEquiv.toAddEquiv

/-- Naturality of `matlisTensorAddEquiv` in the module. -/
theorem matlisTensorAddEquiv_naturality (hω' : ∃ b : ℤ, ω.IsGE b) (n : ℤ)
    {N N' : ModuleCat.{u} A} [Module.Finite A N] [Module.Finite A N'] (g : N ⟶ N')
    (φ : locSq q (hullDeg q ω hω - n) N' →ₗ[Sq q] hullE q ω hω) :
    matlisTensorAddEquiv q ω hω hω' n N (φ ∘ₗ (locSqMap q (hullDeg q ω hω - n) g).hom) =
      ((extOmega ω n).map g.op).hom.lTensor (Sq q) (matlisTensorAddEquiv q ω hω hω' n N' φ) := by
  show (Dualizing.extendScalarsTensorIso.{u, u} (Sq q) _).hom.hom
      (matlisExtAddEquiv q ω hω hω' n N (φ ∘ₗ (locSqMap q (hullDeg q ω hω - n) g).hom)) =
    ((extOmega ω n).map g.op).hom.lTensor (Sq q)
      ((Dualizing.extendScalarsTensorIso.{u, u} (Sq q) _).hom.hom
        (matlisExtAddEquiv q ω hω hω' n N' φ))
  rw [matlisExtAddEquiv_naturality]
  exact congrArg (fun f ↦ f.hom (matlisExtAddEquiv q ω hω hω' n N' φ))
    (extendScalarsTensorIso_naturality q ((extOmega ω n).map g.op))

/-- The cogenerator property of the injective hull `E` over `Ŝ`. -/
theorem hullE_cogenerator {M : Type u} [AddCommGroup M] [Module (Sq q) M] {x : M} (hx : x ≠ 0) :
    ∃ f : M →ₗ[Sq q] hullE q ω hω, f x ≠ 0 :=
  have : Injective (ModuleCat.of (Sq q) (hullE q ω hω)) :=
    inferInstanceAs (Injective (hullE q ω hω))
  have : Module.Injective (Sq q) (hullE q ω hω) :=
    Module.injective_module_of_injective_object (Sq q) (hullE q ω hω)
  Module.exists_apply_ne_zero_of_injective_residueField (J := hullE q ω hω)
    (hullData q ω hω).2.2.1
    (hullData q ω hω).2.2.2.1 hx

/-- **The per-prime transfer over `Ŝ`.** For maps of finite `A`-modules, vanishing, equality of
images and injectivity on an image for `H^{d-n}_𝔪(Ŝ ⊗ -)` are the dual statements for
`Ŝ ⊗_A Extⁿ_A(-, ω)`. -/
theorem transfer_Sq (hω' : ∃ b : ℤ, ω.IsGE b) (n : ℤ) :
    (∀ (N₀ N₁ : ModuleCat.{u} A) [Module.Finite A N₀] [Module.Finite A N₁] (g : N₀ ⟶ N₁),
      locSqMap q (hullDeg q ω hω - n) g = 0 ↔
        ((extOmega ω n).map g.op).hom.lTensor (Sq q) = 0) ∧
    (∀ (N₀ N₁ N₂ : ModuleCat.{u} A) [Module.Finite A N₀] [Module.Finite A N₁]
      [Module.Finite A N₂] (a : N₀ ⟶ N₁) (b : N₁ ⟶ N₂),
      LinearMap.range (locSqMap q (hullDeg q ω hω - n) (a ≫ b)).hom =
          LinearMap.range (locSqMap q (hullDeg q ω hω - n) b).hom ↔
        LinearMap.ker (((extOmega ω n).map (a ≫ b).op).hom.lTensor (Sq q)) =
          LinearMap.ker (((extOmega ω n).map b.op).hom.lTensor (Sq q))) ∧
    (∀ (N₀ N₁ N₂ : ModuleCat.{u} A) [Module.Finite A N₀] [Module.Finite A N₁]
      [Module.Finite A N₂] (t : N₀ ⟶ N₁) (w : N₁ ⟶ N₂),
      (∀ x, (locSqMap q (hullDeg q ω hω - n) t).hom x ∈
          LinearMap.ker (locSqMap q (hullDeg q ω hω - n) w).hom →
        (locSqMap q (hullDeg q ω hω - n) t).hom x = 0) ↔
        LinearMap.range (((extOmega ω n).map (t ≫ w).op).hom.lTensor (Sq q)) =
          LinearMap.range (((extOmega ω n).map t.op).hom.lTensor (Sq q))) := by
  have : Injective (ModuleCat.of (Sq q) (hullE q ω hω)) :=
    inferInstanceAs (Injective (hullE q ω hω))
  have : Module.Injective (Sq q) (hullE q ω hω) :=
    Module.injective_module_of_injective_object (Sq q) (hullE q ω hω)
  have hJ := fun {M : Type u} [AddCommGroup M] [Module (Sq q) M] {x : M} (hx : x ≠ 0) ↦
    hullE_cogenerator q ω hω hx
  have hmap : ∀ {N₀ N₁ N₂ : ModuleCat.{u} A} (a : N₀ ⟶ N₁) (b : N₁ ⟶ N₂),
      (locSqMap q (hullDeg q ω hω - n) (a ≫ b)).hom =
        (locSqMap q (hullDeg q ω hω - n) b).hom ∘ₗ (locSqMap q (hullDeg q ω hω - n) a).hom := by
    intro N₀ N₁ N₂ a b
    simp only [locSqMap, Functor.map_comp, ModuleCat.hom_comp]
  have hext : ∀ {N₀ N₁ N₂ : ModuleCat.{u} A} (a : N₀ ⟶ N₁) (b : N₁ ⟶ N₂),
      ((extOmega ω n).map (a ≫ b).op).hom.lTensor (Sq q) =
        ((extOmega ω n).map a.op).hom.lTensor (Sq q) ∘ₗ
          ((extOmega ω n).map b.op).hom.lTensor (Sq q) := by
    intro N₀ N₁ N₂ a b
    rw [op_comp, Functor.map_comp, ModuleCat.hom_comp, LinearMap.lTensor_comp]
  refine ⟨fun N₀ N₁ _ _ g ↦ ?_, fun N₀ N₁ N₂ _ _ _ a b ↦ ?_, fun N₀ N₁ N₂ _ _ _ t w ↦ ?_⟩
  · have h := LinearMap.eq_zero_iff_of_dual_addEquiv hJ
      (matlisTensorAddEquiv q ω hω hω' n N₀) (matlisTensorAddEquiv q ω hω hω' n N₁)
      (locSqMap q (hullDeg q ω hω - n) g).hom
      (((extOmega ω n).map g.op).hom.lTensor (Sq q)).toAddMonoidHom
      (matlisTensorAddEquiv_naturality q ω hω hω' n g)
    refine ⟨fun hg ↦ ?_, fun hg ↦ ?_⟩
    · exact LinearMap.toAddMonoidHom_injective (h.mp (by rw [hg]; rfl))
    · exact ModuleCat.hom_ext (h.mpr (by rw [hg]; rfl))
  · have h := LinearMap.range_comp_eq_iff_of_dual_addEquiv hJ
      (matlisTensorAddEquiv q ω hω hω' n N₀) (matlisTensorAddEquiv q ω hω hω' n N₁)
      (matlisTensorAddEquiv q ω hω hω' n N₂)
      (locSqMap q (hullDeg q ω hω - n) a).hom (locSqMap q (hullDeg q ω hω - n) b).hom
      (((extOmega ω n).map a.op).hom.lTensor (Sq q)).toAddMonoidHom
      (((extOmega ω n).map b.op).hom.lTensor (Sq q)).toAddMonoidHom
      (matlisTensorAddEquiv_naturality q ω hω hω' n a)
      (matlisTensorAddEquiv_naturality q ω hω hω' n b)
    rw [hmap, hext, h]
    simp only [SetLike.ext_iff, AddMonoidHom.mem_ker, AddMonoidHom.comp_apply,
      LinearMap.toAddMonoidHom_coe, LinearMap.mem_ker, LinearMap.comp_apply]
  · have h := LinearMap.forall_ker_comp_iff_of_dual_addEquiv hJ
      (matlisTensorAddEquiv q ω hω hω' n N₀) (matlisTensorAddEquiv q ω hω hω' n N₁)
      (matlisTensorAddEquiv q ω hω hω' n N₂)
      (locSqMap q (hullDeg q ω hω - n) t).hom (locSqMap q (hullDeg q ω hω - n) w).hom
      (((extOmega ω n).map t.op).hom.lTensor (Sq q)).toAddMonoidHom
      (((extOmega ω n).map w.op).hom.lTensor (Sq q)).toAddMonoidHom
      (matlisTensorAddEquiv_naturality q ω hω hω' n t)
      (matlisTensorAddEquiv_naturality q ω hω hω' n w)
    rw [h, hext]
    simp only [SetLike.ext_iff, AddMonoidHom.mem_range, AddMonoidHom.comp_apply,
      LinearMap.toAddMonoidHom_coe, LinearMap.mem_range, LinearMap.comp_apply]

end Duality

end Stacks.LocalCohomology.LocalDualityTransfer
