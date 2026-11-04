module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GroupRingCoinduction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CompactSupportGroupInvariants
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.RightAcyclicTransfer
public import StacksFrontier.AlgebraicGeometry.AffineCohomologyComparison.Basic
public import StacksFrontier.AlgebraicGeometry.RightAcyclicProduct.Basic
public import StacksFrontier.Algebra.Homology.DerivedCategory.RightAcyclicFiniteProduct
public import StacksFrontier.Topology.Sheaves.Cohomology.ModuleComparison.AcyclicityAndBoundedBelow
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.ModuleRestrictionInverseImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Descent.PropertyCPushforward
public import Mathlib.CategoryTheory.Sites.LocalProperties
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.EtaleLocality

/-!
# Coinduced sheaves are acyclic for invariants

Let `Λ` be a commutative ring and `G` a finite group. Coinduction `𝒮 ↦ Hom_Λ(Λ[G], 𝒮)` of
sheaves of `Λ`-modules on the small étale site is exact, both left and right adjoint to
restriction of scalars along `Λ → Λ[G]`, and its composite with the sheaf of invariants is the
identity; a coinduced sheaf is acyclic for invariants.

An injective sheaf of `Λ[G]`-modules is a direct summand of a coinduced one, and coinduction
commutes with inverse image and extension by zero. Inverse image and extension by zero preserve
acyclicity for invariants (Tag 015M), and acyclicity for invariants descends along a surjective
étale morphism. Consequently a sheaf which is coinduced étale locally is acyclic for invariants,
and so are its extension by zero and its inverse images.

## Main results

* `Stacks.EtaleCohomology.rightAcyclic_invariants_coinduction`: coinduced sheaves are acyclic
  for invariants.
* `Stacks.EtaleCohomology.rightAcyclic_invariants_inverseImage`,
  `Stacks.EtaleCohomology.rightAcyclic_invariants_extensionByZero`: inverse image and extension
  by zero preserve acyclicity for invariants.
* `Stacks.EtaleCohomology.rightAcyclic_invariants_of_inverseImage`: acyclicity descends along a
  surjective étale morphism.
* `Stacks.EtaleCohomology.rightAcyclic_compactSupportRestrictedComplex`: the terms of
  `(j_! 𝒩)|_{X̄_k̄}` are acyclic for invariants when those of `𝒩` are.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

namespace CategoryTheory.Functor

variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
  [HasDerivedCategory C] [HasDerivedCategory D] [EnoughInjectives C]

/-- **Right acyclicity passes to retracts**, for a left exact functor. -/
theorem rightAcyclic_of_retract (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] {X Y : C}
    (i : X ⟶ Y) (r : Y ⟶ X) (h : i ≫ r = 𝟙 X) (hY : F.rightAcyclic Y) : F.rightAcyclic X := by
  rw [Stacks.DerivedIndexing.rightAcyclic_iff_forall_nat] at hY ⊢
  intro n hn
  have : Mono ((F.rightDerived n).map i) :=
    ⟨fun a b hab => by
      simpa only [Category.assoc, ← Functor.map_comp, h, Functor.map_id, Category.comp_id]
        using congrArg (· ≫ (F.rightDerived n).map r) hab⟩
  exact (hY n hn).of_mono ((F.rightDerived n).map i)

end CategoryTheory.Functor

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard

variable (Λ : Type) [CommRing Λ] (G : Type) [Group G] [Fintype G]

/-! ### Coinduction of sheaves -/

/-- **Coinduction** of sheaves of modules on the small étale site:
`𝒮 ↦ Hom_Λ(Λ[G], 𝒮)` sectionwise. -/
abbrev etaleModuleCoinduction (X : Scheme.{u}) :
    EtaleModules.{u, 0} Λ X ⥤ EtaleModules.{u, 0} (MonoidAlgebra Λ G) X :=
  etaleModuleCoextendScalars (groupRingScalars Λ G) X

/-- **Frobenius reciprocity for sheaves**: coinduction is left adjoint to restriction of scalars
along `Λ → Λ[G]`, for finite `G`. -/
def etaleModuleCoinductionAdj (X : Scheme.{u}) :
    etaleModuleCoinduction Λ G X ⊣ etaleModuleRestrictScalars (groupRingScalars Λ G) X :=
  Adjunction.restrictFullyFaithful
    ((groupRingCoinductionAdj.{u + 1} Λ G).whiskerRight X.Etaleᵒᵖ)
    (fullyFaithfulSheafToPresheaf _ _) (fullyFaithfulSheafToPresheaf _ _)
    (Iso.refl _) (Iso.refl _)

/-- Coinduction is a left adjoint. -/
instance etaleModuleCoinduction_isLeftAdjoint (X : Scheme.{u}) :
    (etaleModuleCoinduction Λ G X).IsLeftAdjoint :=
  (etaleModuleCoinductionAdj Λ G X).isLeftAdjoint

/-- Coinduction is a right adjoint. -/
instance etaleModuleCoinduction_isRightAdjoint (X : Scheme.{u}) :
    (etaleModuleCoinduction Λ G X).IsRightAdjoint :=
  (etaleModuleCoextendScalarsAdj (groupRingScalars Λ G) X).isRightAdjoint

/-- Coinduction is additive. -/
instance etaleModuleCoinduction_additive (X : Scheme.{u}) :
    (etaleModuleCoinduction Λ G X).Additive :=
  (etaleModuleCoextendScalarsAdj (groupRingScalars Λ G) X).right_adjoint_additive

/-- Coinduction preserves finite colimits. -/
instance etaleModuleCoinduction_preservesFiniteColimits (X : Scheme.{u}) :
    PreservesFiniteColimits (etaleModuleCoinduction Λ G X) :=
  have : PreservesColimitsOfSize.{0, 0} (etaleModuleCoinduction Λ G X) :=
    (etaleModuleCoinductionAdj Λ G X).leftAdjoint_preservesColimits
  PreservesColimitsOfSize.preservesFiniteColimits _

/-- Coinduction preserves finite limits. -/
instance etaleModuleCoinduction_preservesFiniteLimits (X : Scheme.{u}) :
    PreservesFiniteLimits (etaleModuleCoinduction Λ G X) :=
  have : PreservesLimitsOfSize.{0, 0} (etaleModuleCoinduction Λ G X) :=
    (etaleModuleCoextendScalarsAdj (groupRingScalars Λ G) X).rightAdjoint_preservesLimits
  PreservesLimitsOfSize.preservesFiniteLimits _

/-- Coinduction preserves injective objects. -/
instance etaleModuleCoinduction_preservesInjectiveObjects (X : Scheme.{u}) :
    (etaleModuleCoinduction Λ G X).PreservesInjectiveObjects :=
  Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
    (etaleModuleCoextendScalarsAdj (groupRingScalars Λ G) X)

/-- `sheafCompose` carries an isomorphism of coefficient functors to an isomorphism. -/
def sheafComposeIsoOfIso {C : Type*} [Category* C] {J : GrothendieckTopology C}
    {A B : Type*} [Category* A] [Category* B] {F F' : A ⥤ B} [J.HasSheafCompose F]
    [J.HasSheafCompose F'] (e : F ≅ F') : sheafCompose J F ≅ sheafCompose J F' where
  hom := sheafCompose_map J e.hom
  inv := sheafCompose_map J e.inv
  hom_inv_id := by rw [← sheafCompose_comp, e.hom_inv_id, sheafCompose_id]
  inv_hom_id := by rw [← sheafCompose_comp, e.inv_hom_id, sheafCompose_id]

/-- **Invariants of a coinduced sheaf**: coinduction followed by invariants is the identity. -/
def etaleModuleCoinductionInvariantsIso (X : Scheme.{u}) :
    etaleModuleCoinduction Λ G X ⋙ etaleModuleInvariants Λ G X ≅ 𝟭 _ :=
  (Iso.refl _ : etaleModuleCoinduction Λ G X ⋙ etaleModuleInvariants Λ G X ≅
      sheafCompose X.smallEtaleTopology (groupRingCoinduction.{u + 1} Λ G ⋙
        ModuleCat.coextendScalars (groupRingAugmentation Λ G))) ≪≫
    sheafComposeIsoOfIso (groupRingCoinductionInvariantsIso.{u + 1} Λ G) ≪≫
    (Iso.refl _ : sheafCompose X.smallEtaleTopology (𝟭 (ModuleCat.{u + 1} Λ)) ≅ 𝟭 _)

omit [Fintype G] in
/-- **Coinduced sheaves are acyclic for invariants.** -/
theorem rightAcyclic_invariants_coinduction [Finite G] (X : Scheme.{u})
    (S : EtaleModules.{u, 0} Λ X) :
    (etaleModuleInvariants Λ G X).rightAcyclic ((etaleModuleCoinduction Λ G X).obj S) := by
  have := Fintype.ofFinite G
  have hFG : ∀ I : EtaleModules.{u, 0} Λ X, Injective I →
      (etaleModuleInvariants Λ G X).rightAcyclic ((etaleModuleCoinduction Λ G X).obj I) :=
    fun I hI =>
      have := (etaleModuleCoinduction Λ G X).injective_obj_of_injective hI
      Functor.rightAcyclic_of_injective _ _
  have hS : (etaleModuleCoinduction Λ G X).rightAcyclic S :=
    Stacks.Cohomology.ModuleComparison.rightAcyclic_of_exact _ S
  have hcomp : (etaleModuleCoinduction Λ G X ⋙ etaleModuleInvariants Λ G X).rightAcyclic S :=
    Functor.rightAcyclic_of_iso (etaleModuleCoinductionInvariantsIso Λ G X).symm S
      (Stacks.Cohomology.ModuleComparison.rightAcyclic_of_exact _ S)
  rw [Stacks.DerivedIndexing.rightAcyclic_iff_forall_nat] at hcomp ⊢
  intro n hn
  exact (hcomp n hn).of_iso
    (Stacks.Cohomology.AffineComparison.rightDerivedCollapseIso _ _ hFG S hS n).symm

omit [Fintype G] in
/-- **An injective sheaf of `Λ[G]`-modules is a retract of a coinduced sheaf**: the unit of
restriction of scalars along `Λ → Λ[G]` against coinduction has a left inverse. -/
theorem exists_retract_coinduction {X : Scheme.{u}}
    (I : EtaleModules.{u, 0} (MonoidAlgebra Λ G) X) [Injective I] :
    ∃ r, (etaleModuleCoextendScalarsAdj (groupRingScalars Λ G) X).unit.app I ≫ r = 𝟙 I :=
  ⟨Injective.factorThru (𝟙 I)
      ((etaleModuleCoextendScalarsAdj (groupRingScalars Λ G) X).unit.app I),
    Injective.comp_factorThru _ _⟩

/-! ### Transport and descent of acyclicity -/

section Transfer

variable {X Y : Scheme.{u}}
  (P' : EtaleModules.{u, 0} (MonoidAlgebra Λ G) Y ⥤ EtaleModules.{u, 0} (MonoidAlgebra Λ G) X)
  (P : EtaleModules.{u, 0} Λ Y ⥤ EtaleModules.{u, 0} Λ X)
  [P'.Additive] [P.Additive] [PreservesFiniteLimits P'] [PreservesFiniteColimits P']
  [PreservesFiniteLimits P] [PreservesFiniteColimits P]
  (eInv : etaleModuleInvariants Λ G Y ⋙ P ≅ P' ⋙ etaleModuleInvariants Λ G X)
  (eCo : etaleModuleCoinduction Λ G Y ⋙ P' ≅ P ⋙ etaleModuleCoinduction Λ G X)

omit [Fintype G] [P'.Additive] [P.Additive] [PreservesFiniteLimits P'] [PreservesFiniteColimits P']
  [PreservesFiniteLimits P] [PreservesFiniteColimits P] in
include eCo in
/-- An exact functor commuting with coinduction carries injectives to sheaves acyclic for
invariants. -/
theorem rightAcyclic_invariants_map_injective [Finite G]
    (I : EtaleModules.{u, 0} (MonoidAlgebra Λ G) Y) (hI : Injective I) :
    (etaleModuleInvariants Λ G X).rightAcyclic (P'.obj I) := by
  obtain ⟨r, hr⟩ := exists_retract_coinduction Λ G I
  let η := (etaleModuleCoextendScalarsAdj (groupRingScalars Λ G) Y).unit.app I
  refine Functor.rightAcyclic_of_retract _ (P'.map η) (P'.map r)
    (by rw [← Functor.map_comp, hr, CategoryTheory.Functor.map_id]) ?_
  exact ObjectProperty.prop_of_iso _ (eCo.app _).symm
    (rightAcyclic_invariants_coinduction Λ G X _)

omit [Fintype G] in
include eInv eCo in
/-- **An exact functor commuting with invariants and with coinduction preserves acyclicity for
invariants** (Tag 015M). -/
theorem rightAcyclic_invariants_map (N : EtaleModules.{u, 0} (MonoidAlgebra Λ G) Y) [Finite G]
    (hN : (etaleModuleInvariants Λ G Y).rightAcyclic N) :
    (etaleModuleInvariants Λ G X).rightAcyclic (P'.obj N) :=
  Functor.rightAcyclic_obj_of_rightAcyclic _ _ P' P eInv
    (rightAcyclic_invariants_map_injective Λ G P' P eCo) N hN

omit [Fintype G] in
include eInv eCo in
/-- **Acyclicity for invariants descends along an exact functor commuting with invariants and
coinduction whose `Λ`-module version reflects isomorphisms.** -/
theorem rightAcyclic_invariants_of_map [P.ReflectsIsomorphisms] [Finite G]
    (N : EtaleModules.{u, 0} (MonoidAlgebra Λ G) Y)
    (hN : (etaleModuleInvariants Λ G X).rightAcyclic (P'.obj N)) :
    (etaleModuleInvariants Λ G Y).rightAcyclic N :=
  Functor.rightAcyclic_of_rightAcyclic_obj _ _ P' P eInv
    (rightAcyclic_invariants_map_injective Λ G P' P eCo) N hN

end Transfer

/-! ### Inverse image and extension by zero -/

/-- **Inverse image commutes with coinduction.** -/
def etaleModuleInverseImageCoinductionIso {X Y : Scheme.{u}} (f : X ⟶ Y) :
    etaleModuleCoinduction Λ G Y ⋙ etaleModuleInverseImage.{u, 0} (MonoidAlgebra Λ G) f ≅
      etaleModuleInverseImage.{u, 0} Λ f ⋙ etaleModuleCoinduction Λ G X :=
  Adjunction.leftAdjointUniq
    ((etaleModuleCoinductionAdj Λ G Y).comp
      (etaleModuleInverseImageAdj.{u, 0} (MonoidAlgebra Λ G) f))
    (((etaleModuleInverseImageAdj.{u, 0} Λ f).comp (etaleModuleCoinductionAdj Λ G X)).ofNatIsoRight
      (Iso.refl _))

/-- **Extension by zero commutes with coinduction.** -/
def etaleModuleExtensionByZeroCoinductionIso {U X : Scheme.{u}} (j : U ⟶ X) [Etale j] :
    etaleModuleCoinduction Λ G U ⋙ etaleModuleExtensionByZero.{u, 0} (MonoidAlgebra Λ G) j ≅
      etaleModuleExtensionByZero.{u, 0} Λ j ⋙ etaleModuleCoinduction Λ G X :=
  Adjunction.leftAdjointUniq
    ((etaleModuleCoinductionAdj Λ G U).comp
      (etaleModuleExtensionByZeroAdj.{u, 0} (MonoidAlgebra Λ G) j))
    (((etaleModuleExtensionByZeroAdj.{u, 0} Λ j).comp
      (etaleModuleCoinductionAdj Λ G X)).ofNatIsoRight (Iso.refl _))

/-- Inverse image of `Λ`-modules and of `Λ[G]`-modules is exact; this is the exactness input of
`rightAcyclic_invariants_map`. -/
private theorem inverseImage_exact (Λ : Type) [CommRing Λ] (G : Type) [Group G] [Finite G]
    {X Y : Scheme.{u}} (f : X ⟶ Y) {Q : Prop}
    (h : ∀ [Fintype G] [PreservesFiniteLimits (etaleModuleInverseImage.{u, 0} Λ f)]
      [PreservesFiniteColimits (etaleModuleInverseImage.{u, 0} Λ f)]
      [PreservesFiniteLimits (etaleModuleInverseImage.{u, 0} (MonoidAlgebra Λ G) f)]
      [PreservesFiniteColimits (etaleModuleInverseImage.{u, 0} (MonoidAlgebra Λ G) f)], Q) :
    Q :=
  @h (Fintype.ofFinite G) (etaleModuleInverseImage_preservesFiniteLimits Λ f)
    (etaleModuleInverseImage_preservesFiniteColimits Λ f)
    (etaleModuleInverseImage_preservesFiniteLimits (MonoidAlgebra Λ G) f)
    (etaleModuleInverseImage_preservesFiniteColimits (MonoidAlgebra Λ G) f)

omit [Fintype G] in
/-- **Inverse image preserves acyclicity for invariants.** -/
theorem rightAcyclic_invariants_inverseImage {X Y : Scheme.{u}} (f : X ⟶ Y) [Finite G]
    (N : EtaleModules.{u, 0} (MonoidAlgebra Λ G) Y)
    (hN : (etaleModuleInvariants Λ G Y).rightAcyclic N) :
    (etaleModuleInvariants Λ G X).rightAcyclic
      ((etaleModuleInverseImage.{u, 0} (MonoidAlgebra Λ G) f).obj N) :=
  inverseImage_exact Λ G f <|
  rightAcyclic_invariants_map Λ G _ _ (etaleModuleInverseImageInvariants Λ G f)
    (etaleModuleInverseImageCoinductionIso Λ G f) N hN

omit [Fintype G] in
/-- **Extension by zero preserves acyclicity for invariants.** -/
theorem rightAcyclic_invariants_extensionByZero {U X : Scheme.{u}} (j : U ⟶ X) [Etale j] [Finite G]
    (N : EtaleModules.{u, 0} (MonoidAlgebra Λ G) U)
    (hN : (etaleModuleInvariants Λ G U).rightAcyclic N) :
    (etaleModuleInvariants Λ G X).rightAcyclic
      ((etaleModuleExtensionByZero.{u, 0} (MonoidAlgebra Λ G) j).obj N) :=
  have := Fintype.ofFinite G
  rightAcyclic_invariants_map Λ G _ _ (etaleModuleExtensionByZeroInvariants Λ G j)
    (etaleModuleExtensionByZeroCoinductionIso Λ G j) N hN

/-! ### Descent along a surjective étale morphism -/

section Descent

/-- For a surjective étale `π : Y ⟶ V`, the object `Y` of the small étale site of `V` covers
it. -/
theorem coversTop_smallEtale_of_surjective {V Y : Scheme.{u}} (π : Y ⟶ V) [Etale π]
    [Surjective π] :
    V.smallEtaleTopology.CoversTop (fun _ : PUnit.{1} => smallEtaleObj π) := by
  intro U
  have hU : Etale U.hom := U.prop
  let P : V.Etale := MorphismProperty.Over.mk ⊤ (pullback.fst U.hom π ≫ U.hom) inferInstance
  let e : P ⟶ U := MorphismProperty.Over.homMk (pullback.fst U.hom π) rfl trivial
  refine V.smallEtaleTopology.superset_covering ?_
    (mem_smallEtaleTopology_of_surjective e (inferInstanceAs (Surjective (pullback.fst U.hom π))))
  rintro W f ⟨W', h, g, hg, rfl⟩
  cases hg
  exact ⟨PUnit.unit, ⟨h ≫ MorphismProperty.Over.homMk (pullback.snd U.hom π)
    pullback.condition.symm trivial⟩⟩

/-- **Restriction along a surjective étale morphism reflects isomorphisms** of sheaves of
modules. -/
theorem isIso_of_isIso_etaleModuleRestriction (R : Type) [Ring R] {V Y : Scheme.{u}}
    (π : Y ⟶ V) [Etale π] [Surjective π] {A B : EtaleModules.{u, 0} R V} (φ : A ⟶ B)
    (h : IsIso ((etaleModuleRestriction.{u, 0} R π).map φ)) : IsIso φ := by
  refine Sheaf.isIso_of_coversTop (coversTop_smallEtale_of_surjective π) fun _ => ?_
  rw [← ObjectProperty.isIso_hom_iff, NatTrans.isIso_iff_isIso_app]
  rintro ⟨Z⟩
  have hw : Z.hom.left ≫ π = Z.left.hom := MorphismProperty.Over.w Z.hom
  have hZπ : Etale (Z.hom.left ≫ π) := hw ▸ (Z.left.prop : Etale Z.left.hom)
  have : Etale Z.hom.left :=
    MorphismProperty.of_postcomp (W' := @Etale) @Etale Z.hom.left π ‹Etale π› hZπ
  let Z' : Y.Etale := MorphismProperty.Over.mk ⊤ Z.hom.left this
  let iso : (Scheme.Etale.smallEtaleCompose π).obj Z' ≅ Z.left :=
    MorphismProperty.Over.isoMk (Iso.refl _) ((Category.id_comp Z.left.hom).trans hw.symm)
  have h' : IsIso (φ.hom.app (op ((Scheme.Etale.smallEtaleCompose π).obj Z'))) :=
    (NatTrans.isIso_iff_isIso_app _).1 ((ObjectProperty.isIso_hom_iff _).2 h) (op Z')
  exact (NatTrans.isIso_app_iff_of_iso φ.hom iso.op).2 h'

/-- **Inverse image along a surjective étale morphism reflects isomorphisms** of sheaves of
modules. -/
theorem reflectsIsomorphisms_etaleModuleInverseImage (R : Type) [Ring R] {V Y : Scheme.{u}}
    (π : Y ⟶ V) [Etale π] [Surjective π] :
    (etaleModuleInverseImage.{u, 0} R π).ReflectsIsomorphisms where
  reflects φ hφ := isIso_of_isIso_etaleModuleRestriction R π φ
    ((NatIso.isIso_map_iff (etaleModuleInverseImageRestrictionIso.{u, 0} R π) φ).1 hφ)

omit [Fintype G] in
/-- **Acyclicity for invariants descends along a surjective étale morphism.** -/
theorem rightAcyclic_invariants_of_inverseImage {V Y : Scheme.{u}} (π : Y ⟶ V) [Etale π] [Finite G]
    [Surjective π] (N : EtaleModules.{u, 0} (MonoidAlgebra Λ G) V)
    (hN : (etaleModuleInvariants Λ G Y).rightAcyclic
      ((etaleModuleInverseImage.{u, 0} (MonoidAlgebra Λ G) π).obj N)) :
    (etaleModuleInvariants Λ G V).rightAcyclic N :=
  inverseImage_exact Λ G π <|
  have := reflectsIsomorphisms_etaleModuleInverseImage Λ π
  rightAcyclic_invariants_of_map Λ G _ _ (etaleModuleInverseImageInvariants Λ G π)
    (etaleModuleInverseImageCoinductionIso Λ G π) N hN

omit [Fintype G] in
/-- **A sheaf of `Λ[G]`-modules which is coinduced étale locally is acyclic for invariants.** -/
theorem rightAcyclic_invariants_of_inverseImage_iso_coinduction {V Y : Scheme.{u}} [Finite G]
    (π : Y ⟶ V) [Etale π] [Surjective π] (N : EtaleModules.{u, 0} (MonoidAlgebra Λ G) V)
    (S : EtaleModules.{u, 0} Λ Y)
    (e : (etaleModuleInverseImage.{u, 0} (MonoidAlgebra Λ G) π).obj N ≅
      (etaleModuleCoinduction Λ G Y).obj S) :
    (etaleModuleInvariants Λ G V).rightAcyclic N :=
  rightAcyclic_invariants_of_inverseImage Λ G π N
    (ObjectProperty.prop_of_iso _ e.symm (rightAcyclic_invariants_coinduction Λ G Y S))

end Descent

/-! ### The acyclicity hypothesis of the Hochschild–Serre comparison -/

section CompactSupport

open Stacks.Frobenius

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
  (j : CompactificationOf (Over.mk f)) (kbar : Type u) [Field kbar] [Algebra k kbar]

omit [Fintype G] in
/-- **The terms of `(j_! 𝒩)|_{X̄_k̄}` are acyclic for invariants** as soon as the terms of `𝒩`
are. -/
theorem rightAcyclic_compactSupportRestrictedComplex [Finite G]
    (K : CochainComplex.Plus (EtaleModules.{u, 0} (MonoidAlgebra Λ G) X))
    (hK : ∀ n, (etaleModuleInvariants Λ G X).rightAcyclic (K.obj.X n)) (n : ℤ) :
    (etaleModuleInvariants Λ G _).rightAcyclic
      ((compactSupportRestrictedComplex f j kbar (MonoidAlgebra Λ G) K).obj.X n) :=
  rightAcyclic_invariants_inverseImage Λ G _ _
    (rightAcyclic_invariants_extensionByZero Λ G j.immersion _ (hK n))

end CompactSupport

end Stacks.EtaleCohomology

end
