module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.TorsionHomAcyclic
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GaloisTwistSheaf

/-!
# Acyclicity for the twist functor `Hom_{ℤ/ℓᴹ[G]}(E^∨, -)` on étale sheaves

Let `ℓ` be a prime, `k₀ = ℤ/ℓᴹ`, `G` a finite group, `Λ` a commutative `k₀`-algebra and `E` a
finite `Λ`-module with a `Λ`-linear action of `G`.  Write `Ψ = Hom_{k₀[G]}(E^∨, -)` for the twist
functor (`Stacks.EtaleCohomology.twistFunctor`) on sheaves of `k₀[G]`-modules.  This file proves
the acyclicity statements which make `Ψ` compute compactly supported cohomology in the proof of
[Tag 03UZ]:

* `Ψ` carries injective sheaves to sheaves acyclic for the sections over every étale object;
* the inverse image along any morphism and the extension by zero along any étale morphism carry
  `Ψ`-acyclic sheaves to `Ψ`-acyclic sheaves, and `Ψ`-acyclicity descends along a surjective
  étale morphism;
* a sheaf coinduced from a flat sheaf of `k₀`-modules is `Ψ`-acyclic.

The argument: on a coinduced sheaf `Hom_{k₀}(k₀[G], 𝒥)` the functor `Ψ` is `Hom_{k₀}(E^∨, 𝒥)`
(`Stacks.EtaleCohomology.sourceHomCoinductionIso`), which is exact on flat sheaves
(`Stacks.EtaleCohomology.isTorsionHomAdapted_zmodHomFunctor`), so flat sheaves are acyclic for it
(Tag 05T8); an injective sheaf of `k₀[G]`-modules is a retract of the coinduction of its
underlying injective, hence flat, sheaf of `k₀`-modules, and inverse image and extension by zero
commute with `Ψ` and with coinduction and preserve flatness (Tag 015M).

## Main results

* `Stacks.EtaleCohomology.isAcyclicEverywhere_twistFunctor_obj`
* `Stacks.EtaleCohomology.rightAcyclic_twistFunctor_coinduction`
* `Stacks.EtaleCohomology.rightAcyclic_twistFunctor_inverseImage`
* `Stacks.EtaleCohomology.rightAcyclic_twistFunctor_extensionByZero`
* `Stacks.EtaleCohomology.rightAcyclic_twistFunctor_of_inverseImage`

## References

* [Stacks Project, Tag 03UZ](https://stacks.math.columbia.edu/tag/03UZ)
* [Stacks Project, Tag 05T8](https://stacks.math.columbia.edu/tag/05T8)
* [Stacks Project, Tag 015M](https://stacks.math.columbia.edu/tag/015M)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

/-- **Acyclicity everywhere can be tested after restriction of scalars along any ring map**: the
cohomology of `B` over `U` is the cohomology of `res_ρ B`, because restriction of scalars carries
injectives to sheaves acyclic everywhere. -/
theorem IsAcyclicEverywhere.of_restrictScalars {Λ₀ Λ : Type} [Ring Λ₀] [Ring Λ] (ρ : Λ₀ →+* Λ)
    {X : Scheme.{u}} (B : EtaleModules.{u, 0} Λ X)
    (h : IsAcyclicEverywhere ((etaleModuleRestrictScalars ρ X).obj B)) :
    IsAcyclicEverywhere B := by
  intro U
  rw [Stacks.Cohomology.LerayDegreewise.rightAcyclic_iff_isZero_rightDerived]
  intro p hp
  have hU := h U
  rw [Stacks.Cohomology.LerayDegreewise.rightAcyclic_iff_isZero_rightDerived] at hU
  let G := (sheafSections X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj (Opposite.op U)
  let G₀ := (sheafSections X.smallEtaleTopology (ModuleCat.{u + 1} Λ₀)).obj (Opposite.op U)
  let F := etaleModuleRestrictScalars ρ X
  let r := ModuleCat.restrictScalars.{u + 1} ρ
  let e : G ⋙ r ≅ F ⋙ G₀ := NatIso.ofComponents (fun _ => Iso.refl _) (fun _ => rfl)
  have hz : IsZero (r.obj ((G.rightDerived p).obj B)) :=
    (hU p hp).of_iso
      ((Stacks.Cohomology.DerivedForget.rightDerivedCompIso G r p).app B ≪≫
        (ModuleSheafCohomology.rightDerivedIso e p).app B ≪≫
        (Stacks.Cohomology.AcyclicCollapse.rightDerivedCompIsoOfAcyclic F G₀
          (fun I _ => isAcyclicEverywhere_restrictScalars' ρ I U) p).app B)
  rw [IsZero.iff_id_eq_zero] at hz ⊢
  exact r.map_injective (by rwa [CategoryTheory.Functor.map_id, Functor.map_zero])

/-! ### `Hom_{k₀}(D, -)` with coefficients acting through `D` -/

section Coefficients

variable (ℓ M : ℕ) [Fact ℓ.Prime] (Λ : Type) [CommRing Λ] [Algebra (ZMod (ℓ ^ M)) Λ]
  (D : Type (u + 1)) [AddCommGroup D] [Module (ZMod (ℓ ^ M)) D] [Module Λ D]
  [SMulCommClass Λ (ZMod (ℓ ^ M)) D] [IsScalarTower (ZMod (ℓ ^ M)) Λ D]

/-- After restriction of scalars to `k₀ = ℤ/ℓᴹ`, `Hom_{k₀}(D, -)` with `Λ` acting through `D` is
`Hom_{k₀}(D, -)`. -/
def zmodHomFunctorRestrictScalarsIso :
    zmodHomFunctor.{u} ℓ M D ≅ sourceHomFunctor (ZMod (ℓ ^ M)) Λ D ⋙
      ModuleCat.restrictScalars.{u + 1} (algebraMap (ZMod (ℓ ^ M)) Λ) :=
  NatIso.ofComponents
    (fun N => LinearEquiv.toModuleIso
      ({ toFun := fun φ => (SourceHom.ofLinearMap φ.toLinearMap : SourceHom _ Λ _ N)
         invFun := fun φ => SourceHom.ofLinearMap (SourceHom.toLinearMap (Λ := Λ) φ)
         map_add' := fun _ _ => rfl
         map_smul' := fun c φ => SourceHom.ext fun d => by
          change φ.toLinearMap (c • d) = φ.toLinearMap (algebraMap (ZMod (ℓ ^ M)) Λ c • d)
          rw [algebraMap_smul]
         left_inv := fun _ => rfl
         right_inv := fun _ => rfl } :
        SourceHom (ZMod (ℓ ^ M)) (ZMod (ℓ ^ M)) D N ≃ₗ[ZMod (ℓ ^ M)]
          (ModuleCat.restrictScalars.{u + 1} (algebraMap (ZMod (ℓ ^ M)) Λ)).obj
            ((sourceHomFunctor (ZMod (ℓ ^ M)) Λ D).obj N)))
    (fun _ => rfl)

variable [Finite D]

/-- **`Hom_{k₀}(D, -)` is exact on a short exact sequence of sheaves with flat first term.** -/
theorem shortExact_map_sourceHomFunctor {X : Scheme.{u}}
    (S : ShortComplex (EtaleModules.{u, 0} (ZMod (ℓ ^ M)) X)) (hS : S.ShortExact)
    (h₁ : PowExact ℓ M S.X₁) :
    (S.map (sheafCompose X.smallEtaleTopology (sourceHomFunctor (ZMod (ℓ ^ M)) Λ D))).ShortExact :=
  ShortExact.reflects_shortExact_of_faithful
    (etaleModuleRestrictScalars (algebraMap (ZMod (ℓ ^ M)) Λ) X)
    (ShortComplex.shortExact_of_iso
      (S.mapNatIso (sheafComposeIsoOfIso (J := X.smallEtaleTopology)
        (zmodHomFunctorRestrictScalarsIso ℓ M Λ D)))
      ((isTorsionHomAdapted_zmodHomFunctor D X).1 S hS h₁))

/-- **`Hom_{k₀}(D, -)` carries injective sheaves to sheaves acyclic everywhere.** -/
theorem isAcyclicEverywhere_sourceHomFunctor_obj {X : Scheme.{u}}
    (I : EtaleModules.{u, 0} (ZMod (ℓ ^ M)) X) [Injective I] :
    IsAcyclicEverywhere
      ((sheafCompose X.smallEtaleTopology (sourceHomFunctor (ZMod (ℓ ^ M)) Λ D)).obj I) :=
  IsAcyclicEverywhere.of_restrictScalars (algebraMap (ZMod (ℓ ^ M)) Λ) _ fun U =>
    Stacks.RightAcyclicProduct.rightAcyclic_of_iso _
      ((sheafComposeIsoOfIso (J := X.smallEtaleTopology)
        (zmodHomFunctorRestrictScalarsIso ℓ M Λ D)).app I)
      ((isTorsionHomAdapted_zmodHomFunctor D X).2 I inferInstance U)

/-- **Flat sheaves of `k₀`-modules are acyclic for `Hom_{k₀}(D, -)`** (Tag 05T8). -/
theorem rightAcyclic_sourceHomFunctor_of_powExact {X : Scheme.{u}}
    (J : EtaleModules.{u, 0} (ZMod (ℓ ^ M)) X) (hJ : PowExact ℓ M J) :
    (sheafCompose X.smallEtaleTopology (sourceHomFunctor (ZMod (ℓ ^ M)) Λ D)).rightAcyclic J :=
  Functor.le_rightAcyclic _ (PowExact ℓ M)
    (fun A => ⟨Injective.under A, powExact_of_injective _, Injective.ι A, inferInstance⟩)
    (fun S hS h₁ h₂ => ⟨PowExact.of_shortExact hS h₁ h₂ (etaleModules_pow_nsmul_id _),
      shortExact_map_sourceHomFunctor ℓ M Λ D S hS h₁⟩) J hJ

end Coefficients

/-! ### The twist functor -/

section Twist

variable (ℓ M : ℕ) [Fact ℓ.Prime] (G : Type) [Group G] [Fintype G] (Λ : Type) [CommRing Λ]
  [Algebra (ZMod (ℓ ^ M)) Λ] (E : Type (u + 1)) [AddCommGroup E] [Module Λ E]
  [Module (ZMod (ℓ ^ M)) E] [IsScalarTower (ZMod (ℓ ^ M)) Λ E] (ρ : Representation Λ G E)
  [Finite E]

local notation "k₀" => ZMod (ℓ ^ M)
local notation "Ψ" X =>
  sheafCompose (Scheme.smallEtaleTopology X) (twistFunctor (ZMod (ℓ ^ M)) G Λ E ρ)

/-- For a prime `ℓ`, the power `ℓ ^ M` is nonzero. -/
instance : NeZero (ℓ ^ M) := ⟨pow_ne_zero _ (Fact.out : ℓ.Prime).ne_zero⟩

/-- `Ψ` of a coinduced sheaf is `Hom_{k₀}(E^∨, -)` of the sheaf it is coinduced from. -/
def twistFunctorCoinductionIso (X : Scheme.{u}) :
    etaleModuleCoinduction k₀ G X ⋙ (Ψ X) ≅
      sheafCompose X.smallEtaleTopology (sourceHomFunctor k₀ Λ (TwistDual k₀ G Λ E ρ)) :=
  (Iso.refl _ : etaleModuleCoinduction k₀ G X ⋙ (Ψ X) ≅ sheafCompose X.smallEtaleTopology
      (groupRingCoinduction.{u + 1} k₀ G ⋙ twistFunctor k₀ G Λ E ρ)) ≪≫
    sheafComposeIsoOfIso (sourceHomCoinductionIso k₀ G Λ (TwistDual k₀ G Λ E ρ))

omit [Fintype G] in
/-- **A sheaf coinduced from a flat sheaf of `k₀`-modules is acyclic for the twist functor.** -/
theorem rightAcyclic_twistFunctor_coinduction [Finite G] {X : Scheme.{u}}
    (J : EtaleModules.{u, 0} k₀ X) (hJ : PowExact ℓ M J) :
    (Ψ X).rightAcyclic ((etaleModuleCoinduction k₀ G X).obj J) := by
  have := Fintype.ofFinite G
  have hFG : ∀ I : EtaleModules.{u, 0} k₀ X, Injective I →
      (Ψ X).rightAcyclic ((etaleModuleCoinduction k₀ G X).obj I) := fun I hI =>
    have := (etaleModuleCoinduction k₀ G X).injective_obj_of_injective hI
    Functor.rightAcyclic_of_injective _ _
  have hS : (etaleModuleCoinduction k₀ G X).rightAcyclic J :=
    Stacks.Cohomology.ModuleComparison.rightAcyclic_of_exact _ J
  have hcomp : (etaleModuleCoinduction k₀ G X ⋙ (Ψ X)).rightAcyclic J :=
    Functor.rightAcyclic_of_iso (twistFunctorCoinductionIso ℓ M G Λ E ρ X).symm J
      (rightAcyclic_sourceHomFunctor_of_powExact ℓ M Λ (TwistDual k₀ G Λ E ρ) J hJ)
  rw [Stacks.DerivedIndexing.rightAcyclic_iff_forall_nat] at hcomp ⊢
  exact fun n hn => (hcomp n hn).of_iso
    (Stacks.Cohomology.AffineComparison.rightDerivedCollapseIso _ _ hFG J hS n).symm

omit [Fintype G] in
/-- Restriction of scalars along `k₀ → k₀[G]` preserves injective sheaves, being right adjoint to
the exact functor coinduction. -/
instance etaleModuleRestrictScalars_groupRingScalars_preservesInjectiveObjects [Finite G]
    (X : Scheme.{u}) :
    (etaleModuleRestrictScalars (groupRingScalars k₀ G) X).PreservesInjectiveObjects :=
  letI := Fintype.ofFinite G
  Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
    (etaleModuleCoinductionAdj k₀ G X)

/-- Right acyclicity of `P I` for an injective `I` follows from that of `P` of the coinduction of
its underlying sheaf of `R`-modules, `I` being a retract of it. -/
private theorem rightAcyclic_map_of_coextend_unit {R H : Type} [CommRing R] [Group H] {C D : Type*}
    [Category* C] [Category* D] [Abelian C] [Abelian D] [HasDerivedCategory C]
    [HasDerivedCategory D] [EnoughInjectives C]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] {X : Scheme.{u}}
    (P : EtaleModules.{u, 0} (MonoidAlgebra R H) X ⥤ C)
    (I : EtaleModules.{u, 0} (MonoidAlgebra R H) X) [Injective I]
    (h : F.rightAcyclic (P.obj
      ((etaleModuleCoextendScalars (groupRingScalars R H) X).obj
        ((etaleModuleRestrictScalars (groupRingScalars R H) X).obj I)))) :
    F.rightAcyclic (P.obj I) := by
  obtain ⟨r, hr⟩ := exists_retract_coinduction R H I
  exact Functor.rightAcyclic_of_retract _ (P.map
    ((etaleModuleCoextendScalarsAdj (groupRingScalars R H) X).unit.app I)) (P.map r)
    (by rw [← Functor.map_comp, hr, CategoryTheory.Functor.map_id]) h

omit [Fintype G] in
/-- **The twist functor carries injective sheaves to sheaves acyclic everywhere**: an injective
sheaf is a retract of the coinduction of its underlying injective sheaf of `k₀`-modules, on which
`Ψ` is `Hom_{k₀}(E^∨, -)`. -/
theorem isAcyclicEverywhere_twistFunctor_obj [Finite G] {X : Scheme.{u}}
    (I : EtaleModules.{u, 0} (MonoidAlgebra k₀ G) X) [Injective I] :
    IsAcyclicEverywhere ((Ψ X).obj I) := by
  have := Fintype.ofFinite G
  have : Injective ((etaleModuleRestrictScalars (groupRingScalars k₀ G) X).obj I) :=
    (etaleModuleRestrictScalars (groupRingScalars k₀ G) X).injective_obj_of_injective inferInstance
  have h := isAcyclicEverywhere_sourceHomFunctor_obj ℓ M Λ (TwistDual k₀ G Λ E ρ)
    ((etaleModuleRestrictScalars (groupRingScalars k₀ G) X).obj I)
  intro U
  exact rightAcyclic_map_of_coextend_unit _ (Ψ X) I
    (Stacks.RightAcyclicProduct.rightAcyclic_of_iso _
      ((twistFunctorCoinductionIso ℓ M G Λ E ρ X).app _).symm (h U))

omit [Fintype G] in
/-- An exact functor commuting with coinduction and preserving flatness carries injective sheaves
to sheaves acyclic for the twist functor. -/
theorem rightAcyclic_twistFunctor_map_injective [Finite G] {X Y : Scheme.{u}}
    (P : EtaleModules.{u, 0} (MonoidAlgebra k₀ G) Y ⥤ EtaleModules.{u, 0} (MonoidAlgebra k₀ G) X)
    (P₀ : EtaleModules.{u, 0} k₀ Y ⥤ EtaleModules.{u, 0} k₀ X) [P₀.Additive]
    [PreservesFiniteLimits P₀] [PreservesFiniteColimits P₀]
    (eCo : etaleModuleCoinduction k₀ G Y ⋙ P ≅ P₀ ⋙ etaleModuleCoinduction k₀ G X)
    (I : EtaleModules.{u, 0} (MonoidAlgebra k₀ G) Y) (hI : Injective I) :
    (Ψ X).rightAcyclic (P.obj I) := by
  have := Fintype.ofFinite G
  have : Injective ((etaleModuleRestrictScalars (groupRingScalars k₀ G) Y).obj I) :=
    (etaleModuleRestrictScalars (groupRingScalars k₀ G) Y).injective_obj_of_injective hI
  exact rightAcyclic_map_of_coextend_unit _ P I
    (Stacks.RightAcyclicProduct.rightAcyclic_of_iso _ (eCo.app _).symm
      (rightAcyclic_twistFunctor_coinduction ℓ M G Λ E ρ _
        (PowExact.map P₀ (etaleModules_pow_nsmul_id _) (powExact_of_injective _))))

/-- The comparison `g^{-1}(Ψ 𝒩) ≅ Ψ(g^{-1} 𝒩)`. -/
def twistFunctorInverseImageIso {X Y : Scheme.{u}} (g : X ⟶ Y) :
    (Ψ Y) ⋙ etaleModuleInverseImage.{u, 0} Λ g ≅
      etaleModuleInverseImage.{u, 0} (MonoidAlgebra k₀ G) g ⋙ (Ψ X) :=
  haveI := isIso_inverseImageMate_twistFunctor k₀ G Λ E ρ g
  asIso (sheafComposeCoefficientMate (smallEtaleBaseChange g) Y.smallEtaleTopology
    X.smallEtaleTopology
    (etaleModuleInverseImageAdj.{u, 0} (MonoidAlgebra k₀ G) g)
    (etaleModuleInverseImageAdj.{u, 0} Λ g) (twistFunctor k₀ G Λ E ρ))

/-- The comparison `j_!(Ψ 𝒩) ≅ Ψ(j_! 𝒩)`. -/
def twistFunctorExtensionByZeroIso {U X : Scheme.{u}} (j : U ⟶ X) [Etale j] :
    (Ψ U) ⋙ etaleModuleExtensionByZero.{u, 0} Λ j ≅
      etaleModuleExtensionByZero.{u, 0} (MonoidAlgebra k₀ G) j ⋙ (Ψ X) :=
  haveI := isIso_extensionByZeroMate_twistFunctor k₀ G Λ E ρ j
  asIso (sheafComposeCoefficientMate (Scheme.Etale.smallEtaleCompose j) U.smallEtaleTopology
    X.smallEtaleTopology (etaleModuleExtensionByZeroAdj.{u, 0} (MonoidAlgebra k₀ G) j)
    (etaleModuleExtensionByZeroAdj.{u, 0} Λ j) (twistFunctor k₀ G Λ E ρ))

omit [Fintype G] in
/-- **Inverse image preserves acyclicity for the twist functor** (Tag 015M). -/
theorem rightAcyclic_twistFunctor_inverseImage [Finite G] {X Y : Scheme.{u}} (g : X ⟶ Y)
    (N : EtaleModules.{u, 0} (MonoidAlgebra k₀ G) Y) (hN : (Ψ Y).rightAcyclic N) :
    (Ψ X).rightAcyclic ((etaleModuleInverseImage.{u, 0} (MonoidAlgebra k₀ G) g).obj N) :=
  have := Fintype.ofFinite G
  have := etaleModuleInverseImage_preservesFiniteLimits.{u, 0} k₀ g
  have := etaleModuleInverseImage_preservesFiniteColimits.{u, 0} k₀ g
  have := etaleModuleInverseImage_preservesFiniteLimits.{u, 0} Λ g
  have := etaleModuleInverseImage_preservesFiniteColimits.{u, 0} Λ g
  have := etaleModuleInverseImage_preservesFiniteLimits.{u, 0} (MonoidAlgebra k₀ G) g
  have := etaleModuleInverseImage_preservesFiniteColimits.{u, 0} (MonoidAlgebra k₀ G) g
  Functor.rightAcyclic_obj_of_rightAcyclic _ _ _ _ (twistFunctorInverseImageIso ℓ M G Λ E ρ g)
    (rightAcyclic_twistFunctor_map_injective ℓ M G Λ E ρ _ _
      (etaleModuleInverseImageCoinductionIso k₀ G g)) N hN

omit [Fintype G] in
/-- **Extension by zero preserves acyclicity for the twist functor** (Tag 015M). -/
theorem rightAcyclic_twistFunctor_extensionByZero [Finite G] {U X : Scheme.{u}} (j : U ⟶ X)
    [Etale j] (N : EtaleModules.{u, 0} (MonoidAlgebra k₀ G) U) (hN : (Ψ U).rightAcyclic N) :
    (Ψ X).rightAcyclic ((etaleModuleExtensionByZero.{u, 0} (MonoidAlgebra k₀ G) j).obj N) :=
  have := Fintype.ofFinite G
  Functor.rightAcyclic_obj_of_rightAcyclic _ _ _ _ (twistFunctorExtensionByZeroIso ℓ M G Λ E ρ j)
    (rightAcyclic_twistFunctor_map_injective ℓ M G Λ E ρ _ _
      (etaleModuleExtensionByZeroCoinductionIso k₀ G j)) N hN

omit [Fintype G] in
/-- **Acyclicity for the twist functor descends along a surjective étale morphism.** -/
theorem rightAcyclic_twistFunctor_of_inverseImage [Finite G] {V Y : Scheme.{u}} (π : Y ⟶ V)
    [Etale π] [Surjective π] (N : EtaleModules.{u, 0} (MonoidAlgebra k₀ G) V)
    (hN : (Ψ Y).rightAcyclic ((etaleModuleInverseImage.{u, 0} (MonoidAlgebra k₀ G) π).obj N)) :
    (Ψ V).rightAcyclic N :=
  have := Fintype.ofFinite G
  have := etaleModuleInverseImage_preservesFiniteLimits.{u, 0} k₀ π
  have := etaleModuleInverseImage_preservesFiniteColimits.{u, 0} k₀ π
  have := etaleModuleInverseImage_preservesFiniteLimits.{u, 0} Λ π
  have := etaleModuleInverseImage_preservesFiniteColimits.{u, 0} Λ π
  have := etaleModuleInverseImage_preservesFiniteLimits.{u, 0} (MonoidAlgebra k₀ G) π
  have := etaleModuleInverseImage_preservesFiniteColimits.{u, 0} (MonoidAlgebra k₀ G) π
  have := reflectsIsomorphisms_etaleModuleInverseImage Λ π
  Functor.rightAcyclic_of_rightAcyclic_obj _ _ _ _ (twistFunctorInverseImageIso ℓ M G Λ E ρ π)
    (rightAcyclic_twistFunctor_map_injective ℓ M G Λ E ρ _ _
      (etaleModuleInverseImageCoinductionIso k₀ G π)) N hN

end Twist

end Stacks.EtaleCohomology

end
