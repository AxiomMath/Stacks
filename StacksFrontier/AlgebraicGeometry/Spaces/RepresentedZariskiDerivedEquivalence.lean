module

public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedZariskiModuleAdjunction
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentDerivedCategory
public import StacksFrontier.AlgebraicGeometry.Duality.QuasiCoherentPushforwardAdjoint
public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryHomology
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedModuleAdjunction
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPushforward.DerivedAdjunctionOfToposHom
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPushforward.PullbackInvertsQuasiIsoOfToposHom

/-!
# `ε^* : D_QCoh(𝒪_{X_0}) ⥤ D_QCoh(𝒪_X)` is an equivalence for a representable algebraic space

Let `X = yoneda.obj U` be the algebraic space represented by an object `U` of the big fppf site
over `S`, with underlying scheme `X_0`, and let `ε : (X_étale, 𝒪_X) ⟶ (X_{0,Zar}, 𝒪_{X_0})` be
`representedZariskiRingedToposHomRepresentedZariskiRingedToposHom`. This file proves the statement
of Stacks 071Q for `X`: the derived pullback `Lε^*`, which is computed degreewise because `ε^*` is
exact, restricts to an equivalence `D_QCoh(𝒪_{X_0}) ≌ D_QCoh(𝒪_X)` with quasi-inverse `Rε_*`.

For `E` in `D_QCoh(𝒪_X)`, represented by a K-injective complex `I`, the cohomology sheaves of
`Rε_* E = ε_* I` are `ε_* H^q(I)`
(`isIso_homologyComparison_representedZariskiModulePushforward_representedZariskiDirectImage`), so
`Rε_* E` has quasi-coherent cohomology, and the counit `ε^* Rε_* E ⟶ E` is the degreewise counit,
which is a quasi-isomorphism because the counit of `ε^* ⊣ ε_*` is invertible on quasi-coherent
modules. The unit is then invertible on `D_QCoh(𝒪_{X_0})` because `ε^*` is conservative there.

## Main results

* `AlgebraicGeometry.Space.isIso_representedZariskiDerivedPullbackComparison`: `Lε^*` is computed
  by degreewise pullback.
* `AlgebraicGeometry.Space.isIso_representedZariskiDerivedAdjunction_counit_app` and
  `AlgebraicGeometry.Space.isIso_representedZariskiDerivedAdjunction_unit_app`: the counit of
  `Lε^* ⊣ Rε_*` is invertible on `D_QCoh(𝒪_X)`, the unit on `D_QCoh(𝒪_{X_0})`.
* `AlgebraicGeometry.Space.representedZariskiQuasicoherentDerivedEquivalence`: the equivalence
  `D_QCoh(𝒪_{X_0}) ≌ D_QCoh(𝒪_X)`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.Cohomology.DerivedPullbackOfToposHom
open Stacks.Cohomology.DerivedPushforward (pullbackAdjPushforwardMapHomotopy pushforwardMapHomotopy)
open Stacks.Cohomology.DerivedPushforward (derivedPushforward pushforwardOnHomotopy sourceQuasiIso)

universe u

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

open AlgebraicGeometry AlgebraicGeometry.RingedToposHom Stacks.Cohomology.HypercohomologyEdge

namespace Stacks.Cohomology.DerivedPullbackOfToposHom

attribute [local instance 10000] HasDerivedCategory.standard

universe v₁ u₁ w₁ v₂ u₂ w₂

variable {X : RingedTopos.{v₁, u₁, w₁}} {Y : RingedTopos.{v₂, u₂, w₂}}
  [X.J.HasSheafCompose (forget RingCat.{w₁})] [Y.J.HasSheafCompose (forget RingCat.{w₂})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w₁} RingCat.{w₁})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w₂} RingCat.{w₂})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w₁})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w₂})]
  [HasSheafify X.J AddCommGrpCat.{w₁}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w₁}]
  [HasSheafify Y.J AddCommGrpCat.{w₂}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w₂}]
  [HasSheafify X.J (Type w₁)] [HasSheafify Y.J (Type w₂)]

attribute [local instance] pushforwardModules_preservesFiniteLimits
  pullbackModules_preservesFiniteColimits

omit [HasSheafify X.J (Type w₁)] [HasSheafify Y.J (Type w₂)] in
/-- The degreewise counit `f^* f_* I ⟶ I` of a morphism of ringed topoi becomes invertible in the
derived category when `f^*` is exact and, in every degree, the comparison
`H^n(f_* I) ⟶ f_* H^n(I)` and the counit at `H^n(I)` are isomorphisms. -/
theorem isIso_Qh_map_pullbackAdjPushforwardMapHomotopy_counit_app (f : RingedToposHom X Y)
    (hf : PreservesFiniteLimits f.toModulesHom.pullbackModules)
    (I : CochainComplex
      (SheafOfModules.{w₁} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J) X.O))) ℤ)
    (h₁ : ∀ n, IsIso (HomologyComparison.homologyComparison (pushforwardModules f) I n))
    (h₂ : ∀ n, IsIso ((pullbackAdjPushforwardModules f).counit.app (I.homology n))) :
    IsIso (DerivedCategory.Qh.map ((pullbackAdjPushforwardMapHomotopy f).counit.app
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I))) :=
  have := hf
  Adjunction.isIso_Qh_map_mapHomotopyCategory_counit_app_adjunctionCounitHomology
    (pullbackAdjPushforwardModules f) I
    (Adjunction.quasiIso_mapHomologicalComplex_counit_app_adjunctionCounitHomology
      (pullbackAdjPushforwardModules f) I h₁ h₂)

end Stacks.Cohomology.DerivedPullbackOfToposHom

namespace AlgebraicGeometry.Space

attribute [local instance 10000] HasDerivedCategory.standard

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (U : BigFppfOver B S hS)

/-- The pullback `ε^*` of modules preserves finite limits. -/
instance preservesFiniteLimits_representedZariskiModulePullback :
    PreservesFiniteLimits
      (representedZariskiModulePullbackRepresentedZariskiPullbackExact B S hS U) :=
  ((exactFunctor_iff _).1
    (representedZariskiModulePullback_exact_representedZariskiPullbackExact B S hS U)).1

/-- The pullback `ε^*` of modules preserves finite colimits. -/
instance preservesFiniteColimits_representedZariskiModulePullback :
    PreservesFiniteColimits
      (representedZariskiModulePullbackRepresentedZariskiPullbackExact B S hS U) :=
  ((exactFunctor_iff _).1
    (representedZariskiModulePullback_exact_representedZariskiPullbackExact B S hS U)).2

/-- The pullback `ε^*` of modules is additive. -/
instance additive_representedZariskiModulePullback :
    (representedZariskiModulePullbackRepresentedZariskiPullbackExact B S hS U).Additive :=
  RingedToposHom.pullbackModules_additive
    (representedZariskiRingedToposHomRepresentedZariskiRingedToposHom B S hS U)

section

attribute [local instance 5000] SheafOfModules.instAbelian

/-- Degreewise `ε^*` inverts quasi-isomorphisms, `ε^*` being exact. -/
theorem quasiIso_isInvertedBy_representedZariskiPullbackOnHomotopy :
    MorphismProperty.IsInvertedBy
      (quasiIsoTarget
        (Y := (representedSchemeRepresentedZariskiRingedToposHom B S hS U).zariskiRingedTopos))
      (pullbackOnHomotopy (X := smallEtaleRingedTopos B S hS (representedSpace U))
        (Y := (representedSchemeRepresentedZariskiRingedToposHom B S hS U).zariskiRingedTopos)
        (representedZariskiRingedToposHomRepresentedZariskiRingedToposHom B S hS U)) := by
  intro K L f hf
  obtain ⟨K₀, rfl⟩ := HomotopyCategory.quotient_obj_surjective K
  obtain ⟨L₀, rfl⟩ := HomotopyCategory.quotient_obj_surjective L
  obtain ⟨f₀, rfl⟩ := (HomotopyCategory.quotient _ _).map_surjective f
  have hf' : QuasiIso f₀ := (HomotopyCategory.quotient_map_mem_quasiIso_iff f₀).1 hf
  have : QuasiIso ((Functor.mapHomologicalComplex
      (representedZariskiModulePullbackRepresentedZariskiPullbackExact B S hS U)
      (ComplexShape.up ℤ)).map f₀) := inferInstance
  have h₁ := (Functor.mapHomotopyCategoryFactors
    (representedZariskiModulePullbackRepresentedZariskiPullbackExact B S hS U)
    (ComplexShape.up ℤ)).hom.naturality f₀
  dsimp only [Functor.comp_map] at h₁
  show IsIso (DerivedCategory.Qh.map
    (((representedZariskiModulePullbackRepresentedZariskiPullbackExact B S hS U).mapHomotopyCategory
      (ComplexShape.up ℤ)).map ((HomotopyCategory.quotient _ _).map f₀)))
  have h₂ : IsIso (DerivedCategory.Qh.map ((HomotopyCategory.quotient _ _).map
      ((Functor.mapHomologicalComplex
        (representedZariskiModulePullbackRepresentedZariskiPullbackExact B S hS U)
        (ComplexShape.up ℤ)).map f₀))) :=
    Localization.inverts DerivedCategory.Qh (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ)) _
      ((HomotopyCategory.quotient_map_mem_quasiIso_iff _).2 this)
  rw [← IsIso.eq_comp_inv] at h₁
  rw [h₁, Functor.map_comp, Functor.map_comp]
  infer_instance

/-- The derived pullback along `ε` exists. -/
instance hasLeftDerivedFunctor_representedZariskiPullbackOnHomotopy :
    Functor.HasLeftDerivedFunctor
      (pullbackOnHomotopy (X := smallEtaleRingedTopos B S hS (representedSpace U))
        (Y := (representedSchemeRepresentedZariskiRingedToposHom B S hS U).zariskiRingedTopos)
        (representedZariskiRingedToposHomRepresentedZariskiRingedToposHom B S hS U))
      (quasiIsoTarget
        (Y := (representedSchemeRepresentedZariskiRingedToposHom B S hS U).zariskiRingedTopos)) :=
  hasLeftDerivedFunctor_pullbackOnHomotopy (X := smallEtaleRingedTopos B S hS (representedSpace U))
    (Y := (representedSchemeRepresentedZariskiRingedToposHom B S hS U).zariskiRingedTopos)
    (representedZariskiRingedToposHomRepresentedZariskiRingedToposHom B S hS U)

/-- **`Lε^*` is computed by degreewise pullback**: the comparison of the derived pullback with
degreewise `ε^*` is an isomorphism, `ε^*` being exact. -/
instance isIso_representedZariskiDerivedPullbackComparison :
    IsIso (derivedPullbackComparison (X := smallEtaleRingedTopos B S hS (representedSpace U))
      (Y := (representedSchemeRepresentedZariskiRingedToposHom B S hS U).zariskiRingedTopos)
      (representedZariskiRingedToposHomRepresentedZariskiRingedToposHom B S hS U)) :=
  Functor.isIso_of_isLeftDerivedFunctor_of_inverts _ _
    (quasiIso_isInvertedBy_representedZariskiPullbackOnHomotopy B S hS U)

/-- The derived pullback `Lε^*`. -/
abbrev representedZariskiDerivedPullback :=
  derivedPullback (X := smallEtaleRingedTopos B S hS (representedSpace U))
    (Y := (representedSchemeRepresentedZariskiRingedToposHom B S hS U).zariskiRingedTopos)
    (representedZariskiRingedToposHomRepresentedZariskiRingedToposHom B S hS U)

/-- **`Lε^*` is the functor `D(ε^*)` induced on derived categories by the exact functor `ε^*`.** -/
def representedZariskiDerivedPullbackIso :
    representedZariskiDerivedPullback B S hS U ≅
      Functor.mapDerivedCategory
        (representedZariskiModulePullbackRepresentedZariskiPullbackExact B S hS U) :=
  (Localization.whiskeringLeftFunctor' DerivedCategory.Qh
      (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ)) _).preimageIso
    (@asIso _ _ _ _ (derivedPullbackComparison
      (X := smallEtaleRingedTopos B S hS (representedSpace U))
      (Y := (representedSchemeRepresentedZariskiRingedToposHom B S hS U).zariskiRingedTopos)
      (representedZariskiRingedToposHomRepresentedZariskiRingedToposHom B S hS U))
      (isIso_representedZariskiDerivedPullbackComparison B S hS U) ≪≫
      ((representedZariskiModulePullbackRepresentedZariskiPullbackExact B S hS U)
        |>.mapDerivedCategoryFactorsh).symm)

/-- **The cohomology sheaves of `Lε^* K` are `ε^*` of those of `K`**, naturally in `K`. -/
def representedZariskiDerivedPullbackHomologyIso (q : ℤ) :
    representedZariskiDerivedPullback B S hS U ⋙ DerivedCategory.homologyFunctor _ q ≅
      DerivedCategory.homologyFunctor _ q ⋙
        representedZariskiModulePullbackRepresentedZariskiPullbackExact B S hS U :=
  Functor.isoWhiskerRight (representedZariskiDerivedPullbackIso B S hS U) _ ≪≫
    (representedZariskiModulePullbackRepresentedZariskiPullbackExact B S hS U
      |>.mapDerivedCategoryHomologyIso q)

end

/-- The modules on the small étale ringed topos of a representable algebraic space are
Grothendieck abelian, at the spelling the derived direct image is formed over. -/
instance isGrothendieckAbelian_representedSpaceModules :
    IsGrothendieckAbelian.{u} (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u + 1, u, u}
        (smallEtaleRingedTopos B S hS (representedSpace U)).O)) :=
  isGrothendieckAbelian_ringedToposStructureRingSheaf B S hS (representedSpace U)

/-- The derived direct image `Rε_*`. -/
abbrev representedZariskiDerivedPushforward :=
  derivedPushforward.{u, u, u, u + 1, u, u}
    (X := smallEtaleRingedTopos B S hS (representedSpace U))
    (Y := (representedSchemeRepresentedZariskiRingedToposHom B S hS U).zariskiRingedTopos)
    (representedZariskiRingedToposHomRepresentedZariskiRingedToposHom B S hS U)

/-- **`Lε^* ⊣ Rε_*`**, Stacks 07A6 for `ε`. -/
abbrev representedZariskiDerivedAdjunction :
    representedZariskiDerivedPullback B S hS U ⊣ representedZariskiDerivedPushforward B S hS U :=
  derivedAdjunction.{u, u + 1, u, u, u, u}
    (X := smallEtaleRingedTopos B S hS (representedSpace U))
    (Y := (representedSchemeRepresentedZariskiRingedToposHom B S hS U).zariskiRingedTopos)
    (representedZariskiRingedToposHomRepresentedZariskiRingedToposHom B S hS U)

section

attribute [local instance 5000] SheafOfModules.instAbelian

/-- The degreewise counit `ε^* ε_* I ⟶ I` becomes invertible in the derived category at a
K-injective complex with quasi-coherent cohomology. -/
theorem isIso_Qh_map_representedZariskiMapHomotopyCounit_app
    (I : CochainComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS
      (representedSpace U))) ℤ)
    (hI : I.IsKInjective) (hqc : ∀ q : ℤ, (I.homology q).IsQuasicoherentOnSite) :
    IsIso (DerivedCategory.Qh.map ((pullbackAdjPushforwardMapHomotopy
      (representedZariskiRingedToposHomRepresentedZariskiRingedToposHom B S hS U)).counit.app
        ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I))) := by
  refine isIso_Qh_map_pullbackAdjPushforwardMapHomotopy_counit_app
    (representedZariskiRingedToposHomRepresentedZariskiRingedToposHom B S hS U)
    (preservesFiniteLimits_representedZariskiModulePullback B S hS U) I ?_ ?_
  · intro q
    exact isIso_homologyComparison_representedZariskiModulePushforward_representedZariskiDirectImage
      B S hS U I hI hqc q
  · intro q
    exact isIso_representedZariskiModuleAdjunction_counit_app_representedZariskiModuleAdjunction
      B S hS U (I.homology q) (hqc q)

/-- The unit `ε_* I ⟶ Rε_* I` of the derived direct image is invertible at a K-injective
complex. -/
theorem isIso_representedZariskiDerivedPushforwardUnit_app_of_isKInjective
    (I : CochainComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS
      (representedSpace U))) ℤ)
    (hI : I.IsKInjective) :
    IsIso ((Functor.totalRightDerivedUnit
      (pushforwardOnHomotopy (X := smallEtaleRingedTopos B S hS (representedSpace U))
        (Y := (representedSchemeRepresentedZariskiRingedToposHom B S hS U).zariskiRingedTopos)
        (representedZariskiRingedToposHomRepresentedZariskiRingedToposHom B S hS U))
      DerivedCategory.Qh (sourceQuasiIso (smallEtaleRingedTopos B S hS (representedSpace U)))).app
        ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I)) :=
  Stacks.Cohomology.UnboundedComplexes.isIso_app_of_isKInjective
    (pushforwardOnHomotopy (X := smallEtaleRingedTopos B S hS (representedSpace U))
      (Y := (representedSchemeRepresentedZariskiRingedToposHom B S hS U).zariskiRingedTopos)
      (representedZariskiRingedToposHomRepresentedZariskiRingedToposHom B S hS U))
    DerivedCategory.Qh (representedZariskiDerivedPushforward B S hS U)
    (Functor.totalRightDerivedUnit _ _ _) I hI

/-- **The counit `Lε^* Rε_* E ⟶ E` is invertible at a K-injective complex with quasi-coherent
cohomology.**  By Stacks 0FPI it is the degreewise counit `ε^* ε_* I ⟶ I`, whose effect on
`H^q` is the counit of `ε^* ⊣ ε_*` at `H^q(I)` after the identification
`H^q(ε_* I) = ε_* H^q(I)`. -/
theorem isIso_representedZariskiDerivedAdjunction_counit_app_of_isKInjective
    (I : CochainComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS
      (representedSpace U))) ℤ)
    (hI : I.IsKInjective) (hqc : ∀ q : ℤ, (I.homology q).IsQuasicoherentOnSite) :
    IsIso ((representedZariskiDerivedAdjunction B S hS U).counit.app
      (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I))) := by
  have hfac := derivedAdjunction_counit_fac
    (X := smallEtaleRingedTopos B S hS (representedSpace U))
    (Y := (representedSchemeRepresentedZariskiRingedToposHom B S hS U).zariskiRingedTopos)
    (representedZariskiRingedToposHomRepresentedZariskiRingedToposHom B S hS U)
    ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I)
  refine @IsIso.of_isIso_fac_left _ _ _ _ _ _ _ _ ?_ ?_ hfac
  · exact @Functor.map_isIso _ _ _ _ _ _ _ _
      (isIso_representedZariskiDerivedPushforwardUnit_app_of_isKInjective B S hS U I hI)
  · refine IsIso.comp_isIso' ?_ ?_
    · exact NatIso.isIso_app_of_isIso _ _
    · exact isIso_Qh_map_representedZariskiMapHomotopyCounit_app B S hS U I hI hqc

/-- A K-injective complex representing an object with quasi-coherent cohomology sheaves has
quasi-coherent cohomology sheaves. -/
theorem isQuasicoherentOnSite_homology_of_iso
    (I : CochainComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS
      (representedSpace U))) ℤ)
    (E : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS
      (representedSpace U))))
    (e : DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I) ≅ E)
    (hE : ∀ q : ℤ, ((DerivedCategory.homologyFunctor _ q).obj E).IsQuasicoherentOnSite) (q : ℤ) :
    (I.homology q).IsQuasicoherentOnSite :=
  SheafOfModules.IsQuasicoherentOnSite.of_iso
    (((HomotopyCategory.homologyFunctorFactors _ (ComplexShape.up ℤ) q).app I).symm ≪≫
      ((DerivedCategory.homologyFunctorFactorsh _ q).app _).symm ≪≫
      (DerivedCategory.homologyFunctor _ q).mapIso e).symm (hE q)

/-- **The counit `Lε^* Rε_* E ⟶ E` is invertible for every `E` with quasi-coherent cohomology
sheaves**: represent `E` by a K-injective complex. -/
theorem isIso_representedZariskiDerivedAdjunction_counit_app
    (E : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS
      (representedSpace U))))
    (hE : ∀ q : ℤ, ((DerivedCategory.homologyFunctor _ q).obj E).IsQuasicoherentOnSite) :
    IsIso ((representedZariskiDerivedAdjunction B S hS U).counit.app E) := by
  obtain ⟨I, hI, ⟨e⟩⟩ := Stacks.Cohomology.UnboundedComplexes.exists_isKInjective_iso
    DerivedCategory.Qh E
  exact (NatTrans.isIso_app_iff_of_iso _ e).1
    (isIso_representedZariskiDerivedAdjunction_counit_app_of_isKInjective B S hS U I hI
      (isQuasicoherentOnSite_homology_of_iso B S hS U I E e hE))

/-- `ε^*` reflects isomorphisms between quasi-coherent `𝒪_{X_0}`-modules. -/
theorem isIso_of_isIso_representedZariskiModulePullback_map
    {F F' : (representedSchemeRepresentedZariskiRingedToposHom B S hS U).Modules}
    (hF : F.IsQuasicoherent) (hF' : F'.IsQuasicoherent) (g : F ⟶ F')
    (hg : IsIso
      ((representedZariskiModulePullbackRepresentedZariskiPullbackExact B S hS U).map g)) :
    IsIso g := by
  obtain ⟨g', hg'⟩ :=
    (bijective_representedZariskiModulePullback_map_representedZariskiModuleAdjunction
      B S hS U hF' hF).2
      (inv ((representedZariskiModulePullbackRepresentedZariskiPullbackExact B S hS U).map g))
  have hg'' : (representedZariskiModulePullbackRepresentedZariskiPullbackExact B S hS U).map g' =
      inv ((representedZariskiModulePullbackRepresentedZariskiPullbackExact B S hS U).map g) := hg'
  refine ⟨g',
    (bijective_representedZariskiModulePullback_map_representedZariskiModuleAdjunction
      B S hS U hF hF).1 ?_,
    (bijective_representedZariskiModulePullback_map_representedZariskiModuleAdjunction
      B S hS U hF' hF').1 ?_⟩
  · have h₁ :=
      (representedZariskiModulePullbackRepresentedZariskiPullbackExact B S hS U).map_comp g g'
    rw [hg'', IsIso.hom_inv_id] at h₁
    exact h₁.trans
      ((representedZariskiModulePullbackRepresentedZariskiPullbackExact B S hS U).map_id F).symm
  · have h₁ :=
      (representedZariskiModulePullbackRepresentedZariskiPullbackExact B S hS U).map_comp g' g
    rw [hg'', IsIso.inv_hom_id] at h₁
    exact h₁.trans
      ((representedZariskiModulePullbackRepresentedZariskiPullbackExact B S hS U).map_id F').symm

/-- **`Rε_*` carries `D_QCoh(𝒪_X)` into `D_QCoh(𝒪_{X_0})`**: at a K-injective complex `I` the
cohomology sheaves of `Rε_* I = ε_* I` are `ε_* H^q(I)`. -/
theorem isQuasicoherent_homology_representedZariskiDerivedPushforward_obj_of_isKInjective
    (I : CochainComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS
      (representedSpace U))) ℤ)
    (hI : I.IsKInjective) (hqc : ∀ q : ℤ, (I.homology q).IsQuasicoherentOnSite) (q : ℤ) :
    ((DerivedCategory.homologyFunctor _ q).obj ((representedZariskiDerivedPushforward B S hS U).obj
      (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
        I)))).IsQuasicoherent := by
  have hu := isIso_representedZariskiDerivedPushforwardUnit_app_of_isKInjective B S hS U I hI
  have hθ :=
    isIso_homologyComparison_representedZariskiModulePushforward_representedZariskiDirectImage
      B S hS U I hI hqc q
  exact ObjectProperty.prop_of_iso (SheafOfModules.isQuasicoherent _)
    ((asIso (HomologyComparison.homologyComparison
        (representedZariskiModulePushforwardRepresentedZariskiPullbackExact B S hS U) I q)).symm ≪≫
      ((HomotopyCategory.homologyFunctorFactors _ (ComplexShape.up ℤ) q).app _).symm ≪≫
      ((DerivedCategory.homologyFunctorFactorsh _ q).app _).symm ≪≫
      (DerivedCategory.homologyFunctor _ q).mapIso (@asIso _ _ _ _ _ hu))
    (isQuasicoherent_representedZariskiModulePushforward_obj_representedZariskiModuleAdjunction
      B S hS U _ (hqc q))

/-- **`Rε_*` carries `D_QCoh(𝒪_X)` into `D_QCoh(𝒪_{X_0})`.** -/
theorem isQuasicoherent_homology_representedZariskiDerivedPushforward_obj
    (E : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS
      (representedSpace U))))
    (hE : ∀ q : ℤ, ((DerivedCategory.homologyFunctor _ q).obj E).IsQuasicoherentOnSite) (q : ℤ) :
    ((DerivedCategory.homologyFunctor _ q).obj
      ((representedZariskiDerivedPushforward B S hS U).obj E)).IsQuasicoherent := by
  obtain ⟨I, hI, ⟨e⟩⟩ := Stacks.Cohomology.UnboundedComplexes.exists_isKInjective_iso
    DerivedCategory.Qh E
  exact ObjectProperty.prop_of_iso (SheafOfModules.isQuasicoherent _)
    ((DerivedCategory.homologyFunctor _ q).mapIso
      ((representedZariskiDerivedPushforward B S hS U).mapIso e))
    (isQuasicoherent_homology_representedZariskiDerivedPushforward_obj_of_isKInjective B S hS U I hI
      (isQuasicoherentOnSite_homology_of_iso B S hS U I E e hE) q)

/-- **`Lε^*` carries `D_QCoh(𝒪_{X_0})` into `D_QCoh(𝒪_X)`**: its cohomology sheaves are
`ε^* H^q`. -/
theorem isQuasicoherentOnSite_homology_representedZariskiDerivedPullback_obj
    (F : DerivedCategory (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf
      (J := (representedSchemeRepresentedZariskiRingedToposHom B S hS U).zariskiRingedTopos.J)
      (representedSchemeRepresentedZariskiRingedToposHom B S hS U).zariskiRingedTopos.O))))
    (hF : ∀ q : ℤ, ((DerivedCategory.homologyFunctor _ q).obj F).IsQuasicoherent) (q : ℤ) :
    ((DerivedCategory.homologyFunctor _ q).obj
      ((representedZariskiDerivedPullback B S hS U).obj F)).IsQuasicoherentOnSite :=
  SheafOfModules.IsQuasicoherentOnSite.of_iso
    ((representedZariskiDerivedPullbackHomologyIso B S hS U q).app F).symm
    (isQuasicoherentOnSite_representedZariskiModulePullback_obj_representedZariskiModuleAdjunction
      B S hS U _ (hF q))

/-- **The unit `F ⟶ Rε_* Lε^* F` is invertible for every `F` with quasi-coherent cohomology
sheaves**: by the triangle identity `Lε^*` of it is invertible, and `Lε^*` reflects
isomorphisms between objects of `D_QCoh`, `ε^*` being exact and fully faithful on
quasi-coherent modules. -/
theorem isIso_representedZariskiDerivedAdjunction_unit_app
    (F : DerivedCategory (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf
      (J := (representedSchemeRepresentedZariskiRingedToposHom B S hS U).zariskiRingedTopos.J)
      (representedSchemeRepresentedZariskiRingedToposHom B S hS U).zariskiRingedTopos.O))))
    (hF : ∀ q : ℤ, ((DerivedCategory.homologyFunctor _ q).obj F).IsQuasicoherent) :
    IsIso ((representedZariskiDerivedAdjunction B S hS U).unit.app F) := by
  have hLF := isQuasicoherentOnSite_homology_representedZariskiDerivedPullback_obj B S hS U F hF
  have hc := isIso_representedZariskiDerivedAdjunction_counit_app B S hS U _ hLF
  have ht := (representedZariskiDerivedAdjunction B S hS U).left_triangle_components F
  have hm : IsIso ((representedZariskiDerivedPullback B S hS U).map
      ((representedZariskiDerivedAdjunction B S hS U).unit.app F)) := by
    have : IsIso ((representedZariskiDerivedPullback B S hS U).map
        ((representedZariskiDerivedAdjunction B S hS U).unit.app F) ≫
        (representedZariskiDerivedAdjunction B S hS U).counit.app
          ((representedZariskiDerivedPullback B S hS U).obj F)) := by
      rw [ht]; exact IsIso.id _
    exact IsIso.of_isIso_comp_right _
      ((representedZariskiDerivedAdjunction B S hS U).counit.app
        ((representedZariskiDerivedPullback B S hS U).obj F))
  refine (DerivedCategory.isIso_iff _ _).2 fun q => ?_
  have hq : IsIso ((representedZariskiModulePullbackRepresentedZariskiPullbackExact B S hS U).map
      ((DerivedCategory.homologyFunctor _ q).map
        ((representedZariskiDerivedAdjunction B S hS U).unit.app F))) :=
    (NatIso.isIso_map_iff (representedZariskiDerivedPullbackHomologyIso B S hS U q) _).1
      (Functor.map_isIso (DerivedCategory.homologyFunctor _ q) _)
  exact isIso_of_isIso_representedZariskiModulePullback_map B S hS U (hF q)
    (isQuasicoherent_homology_representedZariskiDerivedPushforward_obj B S hS U _ hLF q) _ hq

/-- `Lε^* : D_QCoh(𝒪_{X_0}) ⥤ D_QCoh(𝒪_X)`. -/
def representedZariskiQuasicoherentDerivedPullback :
    Stacks.Duality.quasiCoherentDerivedCategory
        (representedSchemeRepresentedZariskiRingedToposHom B S hS U) ⥤
      QuasicoherentDerivedCategory.{u, u} B S hS (representedSpace U).1
        (representedSpace U).2 :=
  ObjectProperty.lift _ (ObjectProperty.ι _ ⋙ representedZariskiDerivedPullback B S hS U)
    (fun F => isQuasicoherentOnSite_homology_representedZariskiDerivedPullback_obj B S hS U F.obj
      F.property)

/-- `Rε_* : D_QCoh(𝒪_X) ⥤ D_QCoh(𝒪_{X_0})`. -/
def representedZariskiQuasicoherentDerivedPushforward :
    QuasicoherentDerivedCategory.{u, u} B S hS (representedSpace U).1
        (representedSpace U).2 ⥤
      Stacks.Duality.quasiCoherentDerivedCategory
        (representedSchemeRepresentedZariskiRingedToposHom B S hS U) :=
  ObjectProperty.lift _ (ObjectProperty.ι _ ⋙ representedZariskiDerivedPushforward B S hS U)
    (fun E => isQuasicoherent_homology_representedZariskiDerivedPushforward_obj B S hS U E.obj
      E.property)

/-- **Stacks 071Q for a representable algebraic space**: `Lε^*` is an equivalence
`D_QCoh(𝒪_{X_0}) ≌ D_QCoh(𝒪_X)` with quasi-inverse `Rε_*`. -/
def representedZariskiQuasicoherentDerivedEquivalence :
    Stacks.Duality.quasiCoherentDerivedCategory
        (representedSchemeRepresentedZariskiRingedToposHom B S hS U) ≌
      QuasicoherentDerivedCategory.{u, u} B S hS (representedSpace U).1
        (representedSpace U).2 :=
  CategoryTheory.Equivalence.mk (representedZariskiQuasicoherentDerivedPullback B S hS U)
    (representedZariskiQuasicoherentDerivedPushforward B S hS U)
    (NatIso.ofComponents
      (fun F => ObjectProperty.isoMk _ (@asIso _ _ _ _
        ((representedZariskiDerivedAdjunction B S hS U).unit.app F.obj)
        (isIso_representedZariskiDerivedAdjunction_unit_app B S hS U F.obj F.property)))
      (fun φ => ObjectProperty.hom_ext _
        ((representedZariskiDerivedAdjunction B S hS U).unit.naturality φ.hom)))
    (NatIso.ofComponents
      (fun E => ObjectProperty.isoMk _ (@asIso _ _ _ _
        ((representedZariskiDerivedAdjunction B S hS U).counit.app E.obj)
        (isIso_representedZariskiDerivedAdjunction_counit_app B S hS U E.obj E.property)))
      (fun φ => ObjectProperty.hom_ext _
        ((representedZariskiDerivedAdjunction B S hS U).counit.naturality φ.hom)))

end

end AlgebraicGeometry.Space
