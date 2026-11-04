module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CanonicalCompactSupportFrobenius
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.EtaleModuleGroupInvariants
public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlusComparisons
public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlusResolution
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DirectImageSectionsRestrictScalarsUnit

/-!
# Compactly supported cohomology of a sheaf of invariants

Let `Λ` be a commutative ring, `G` a finite group, `k` a field with a compactification
`j : X ⟶ X̄` of a `k`-scheme `X`, and `k̄` an extension field of `k`.  For a bounded below
complex `𝒩` of sheaves of `Λ[G]`-modules on `X_étale`, write `𝒩^G` for its sheaf of invariants
and `RΓ_c(X_k̄, -) = RΓ(X̄_k̄, (j_! -)|_{X̄_k̄})` as in
`Stacks.EtaleCohomology.compactSupportFrobeniusCohomology`.  This file proves the
Hochschild–Serre comparison

`RΓ_c(X_k̄, 𝒩^G) ≅ R(-)^G (RΓ_c(X_k̄, 𝒩))`

in `D⁺(Λ)`, where `R(-)^G : D⁺(Λ[G]) ⥤ D⁺(Λ)` is the derived functor of invariants, provided the
terms of `(j_! 𝒩)|_{X̄_k̄}` are acyclic for the sheaf of invariants.

The proof uses only right derived functors.  The sheaf of invariants commutes with extension by
zero and with inverse image (`Stacks.EtaleCohomology.etaleModuleExtensionByZeroInvariants`,
`Stacks.EtaleCohomology.etaleModuleInverseImageInvariants`); under the acyclicity hypothesis it
computes its own derived functor on `(j_! 𝒩)|_{X̄_k̄}` (Leray's acyclicity lemma, Tag 015E); it
commutes on the nose with direct image and with global sections; and it preserves injectives,
being right adjoint to the exact functor "trivial action", as do direct image and global
sections.  So both composites `R(f_*) ∘ R(-)^G` and `R(-)^G ∘ R(f_*)` are the derived functor of
the same composite (Tag 015M), and likewise for global sections.

## Implementation notes

The derived category is the model `HasDerivedCategory.standard`, made a local instance (with no
priority) only so that the statement matches the frozen
`Stacks.EtaleCohomology.compactSupportFrobeniusCohomology`, which is built in that model.  The
general square lemma `CategoryTheory.Functor.rightDerivedFunctorPlusSquareIso` is stated over an
arbitrary `[HasDerivedCategory]`.

## Main definitions

* `Stacks.EtaleCohomology.etaleModuleDerivedInvariants`: `R(-)^G` on sheaves.
* `Stacks.EtaleCohomology.compactSupportInvariantsIso`: the comparison above.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

namespace CategoryTheory.Functor

variable {A' A M' M : Type*} [Category* A'] [Category* A] [Category* M'] [Category* M]
  [Abelian A'] [Abelian A] [Abelian M'] [Abelian M]
  [HasDerivedCategory A'] [HasDerivedCategory A] [HasDerivedCategory M'] [HasDerivedCategory M]
  [EnoughInjectives A'] [EnoughInjectives A] [EnoughInjectives M']
  (G' : A' ⥤ M') (G : A ⥤ M) (rA : A' ⥤ A) (rM : M' ⥤ M)
  [G'.Additive] [G.Additive] [rA.Additive] [rM.Additive]

/-- **Right derived functors of a commutative square of left exact functors.**  For
`G' ⋙ r_M ≅ r_A ⋙ G`, if `G'` carries injectives to `r_M`-acyclic objects and `r_A` carries
injectives to `G`-acyclic objects, then `RG' ⋙ Rr_M ≅ Rr_A ⋙ RG`: both are the right derived
functor of the composite (Tag 015M). -/
def rightDerivedFunctorPlusSquareIso (e : G' ⋙ rM ≅ rA ⋙ G)
    (h₁ : ∀ I : A', Injective I → rM.rightAcyclic (G'.obj I))
    (h₂ : ∀ I : A', Injective I → G.rightAcyclic (rA.obj I)) :
    G'.rightDerivedFunctorPlus ⋙ rM.rightDerivedFunctorPlus ≅
      rA.rightDerivedFunctorPlus ⋙ G.rightDerivedFunctorPlus :=
  (rightDerivedFunctorPlusCompIsoOfRightAcyclic G' rM h₁).symm ≪≫
    rightDerivedFunctorPlusNatIso e ≪≫ rightDerivedFunctorPlusCompIsoOfRightAcyclic rA G h₂

end CategoryTheory.Functor

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard

variable (Λ : Type) [CommRing Λ] (G : Type) [Group G] [Fintype G]

/-- Coextension of scalars is additive, being a right adjoint. -/
instance moduleCat_coextendScalars_additive {R S : Type} [Ring R] [Ring S] (f : R →+* S) :
    (ModuleCat.coextendScalars f : ModuleCat.{u + 1} R ⥤ ModuleCat.{u + 1} S).Additive :=
  (ModuleCat.restrictCoextendScalarsAdj.{u + 1} f).right_adjoint_additive

/-- The sheaf of invariants is additive, being a right adjoint. -/
instance etaleModuleInvariants_additive (X : Scheme.{u}) :
    (etaleModuleInvariants Λ G X).Additive :=
  (etaleModuleCoextendScalarsAdj (groupRingAugmentation Λ G) X).right_adjoint_additive

omit [Fintype G] in
/-- The sheaf of invariants preserves injectives: it is right adjoint to restriction of scalars
along the augmentation, which is exact. -/
theorem injective_etaleModuleInvariants_obj {X : Scheme.{u}}
    (I : EtaleModules.{u, 0} (MonoidAlgebra Λ G) X) [Injective I] :
    Injective ((etaleModuleInvariants Λ G X).obj I) :=
  (etaleModuleCoextendScalarsAdj (groupRingAugmentation Λ G) X).map_injective I inferInstance

/-- **`R(-)^G` on sheaves**: the bounded below right derived functor of the sheaf of
invariants. -/
abbrev etaleModuleDerivedInvariants (X : Scheme.{u}) :
    DerivedCategory.Plus (EtaleModules.{u, 0} (MonoidAlgebra Λ G) X) ⥤
      DerivedCategory.Plus (EtaleModules.{u, 0} Λ X) :=
  (etaleModuleInvariants Λ G X).rightDerivedFunctorPlus

/-- **`R(-)^G` on modules**: the bounded below right derived functor of invariants. -/
abbrev derivedInvariants :
    DerivedCategory.Plus (ModuleCat.{u + 1} (MonoidAlgebra Λ G)) ⥤
      DerivedCategory.Plus (ModuleCat.{u + 1} Λ) :=
  (ModuleCat.coextendScalars (groupRingAugmentation Λ G) :
    ModuleCat.{u + 1} (MonoidAlgebra Λ G) ⥤ ModuleCat.{u + 1} Λ).rightDerivedFunctorPlus

/-- **`Rf_* ∘ R(-)^G ≅ R(-)^G ∘ Rf_*`.** -/
def etaleModuleDerivedDirectImageInvariants {X Y : Scheme.{u}} (f : X ⟶ Y) :
    etaleModuleDerivedInvariants Λ G X ⋙ etaleModuleDerivedDirectImage.{u, 0} Λ f ≅
      etaleModuleDerivedDirectImage.{u, 0} (MonoidAlgebra Λ G) f ⋙
        etaleModuleDerivedInvariants Λ G Y :=
  Functor.rightDerivedFunctorPlusSquareIso _ _ _ _ (Iso.refl _)
    (fun I _ => have := injective_etaleModuleInvariants_obj Λ G I
      Functor.rightAcyclic_of_injective _ _)
    (fun I _ =>
      have := etaleModuleInverseImage_preservesFiniteLimits.{u, 0} (MonoidAlgebra Λ G) f
      have : Injective ((etaleModuleDirectImage.{u, 0} (MonoidAlgebra Λ G) f).obj I) :=
        (etaleModuleInverseImageAdj.{u, 0} (MonoidAlgebra Λ G) f).map_injective I inferInstance
      Functor.rightAcyclic_of_injective _ _)

/-- Global sections of sheaves of modules on the small étale site preserve injectives: they are
right adjoint to the constant sheaf functor, which is exact. -/
theorem injective_etaleModuleGlobalSections_obj (R : Type) [Ring R] {X : Scheme.{u}}
    (I : EtaleModules.{u, 0} R X) [Injective I] :
    Injective ((etaleModuleGlobalSections.{u, 0} R X).obj I) := by
  have : (constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} R)).PreservesMonomorphisms := by
    unfold constantSheaf
    infer_instance
  exact (constantSheafΓAdj X.smallEtaleTopology (ModuleCat.{u + 1} R)).map_injective I
    inferInstance

/-- **Global sections commute with invariants**, on the nose: both send a sheaf of
`Λ[G]`-modules to the invariants of its sections over `X`. -/
def etaleModuleGlobalSectionsInvariants (X : Scheme.{u}) :
    etaleModuleGlobalSections.{u, 0} (MonoidAlgebra Λ G) X ⋙
        (ModuleCat.coextendScalars (groupRingAugmentation Λ G) :
          ModuleCat.{u + 1} (MonoidAlgebra Λ G) ⥤ ModuleCat.{u + 1} Λ) ≅
      etaleModuleInvariants Λ G X ⋙ etaleModuleGlobalSections.{u, 0} Λ X :=
  Functor.isoWhiskerRight (Sheaf.ΓNatIsoSheafSections X.smallEtaleTopology
      (ModuleCat.{u + 1} (MonoidAlgebra Λ G)) terminalIsTerminal) _ ≪≫
    (NatIso.ofComponents (fun _ => Iso.refl _) (fun _ => rfl) :
      (sheafSections X.smallEtaleTopology (ModuleCat.{u + 1} (MonoidAlgebra Λ G))).obj
            (Opposite.op (⊤_ X.Etale)) ⋙
          (ModuleCat.coextendScalars (groupRingAugmentation Λ G) :
            ModuleCat.{u + 1} (MonoidAlgebra Λ G) ⥤ ModuleCat.{u + 1} Λ) ≅
        etaleModuleInvariants Λ G X ⋙
          (sheafSections X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
            (Opposite.op (⊤_ X.Etale))) ≪≫
    Functor.isoWhiskerLeft (etaleModuleInvariants Λ G X)
      (Sheaf.ΓNatIsoSheafSections X.smallEtaleTopology (ModuleCat.{u + 1} Λ)
        terminalIsTerminal).symm

/-- **`RΓ(X, -) ∘ R(-)^G ≅ R(-)^G ∘ RΓ(X, -)`.** -/
def etaleModuleDerivedGlobalSectionsInvariants (X : Scheme.{u}) :
    etaleModuleDerivedGlobalSections.{u, 0} (MonoidAlgebra Λ G) X ⋙ derivedInvariants Λ G ≅
      etaleModuleDerivedInvariants Λ G X ⋙ etaleModuleDerivedGlobalSections.{u, 0} Λ X :=
  Functor.rightDerivedFunctorPlusSquareIso _ _ _ _ (etaleModuleGlobalSectionsInvariants Λ G X)
    (fun I _ => have := injective_etaleModuleGlobalSections_obj (MonoidAlgebra Λ G) I
      Functor.rightAcyclic_of_injective _ _)
    (fun I _ => have := injective_etaleModuleInvariants_obj Λ G I
      Functor.rightAcyclic_of_injective _ _)

section CompactSupport

open Stacks.Frobenius

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
  (j : CompactificationOf (Over.mk f)) (kbar : Type u) [Field kbar] [Algebra k kbar]

/-- The complex `(j_! 𝒩)|_{X̄_k̄}` whose terms the comparison asks to be acyclic for invariants. -/
abbrev compactSupportRestrictedComplex (R : Type) [Ring R]
    (K : CochainComplex.Plus (EtaleModules.{u, 0} R X)) :
    CochainComplex.Plus (EtaleModules.{u, 0} R (fieldBaseChange (Over.mk j.toBase) kbar)) :=
  (etaleModuleInverseImage.{u, 0} R
      (fieldBaseChangeProj (Over.mk j.toBase) kbar)).mapCochainComplexPlus.obj
    ((etaleModuleExtensionByZero.{u, 0} R j.immersion).mapCochainComplexPlus.obj K)

/-- `j_!(𝒩^G) ≅ (j_! 𝒩)^G`, termwise on a bounded below complex. -/
def extensionByZeroInvariantsComplexIso {U Y : Scheme.{u}} (i : U ⟶ Y) [Etale i]
    (K : CochainComplex.Plus (EtaleModules.{u, 0} (MonoidAlgebra Λ G) U)) :
    (etaleModuleExtensionByZero.{u, 0} Λ i).mapCochainComplexPlus.obj
        ((etaleModuleInvariants Λ G U).mapCochainComplexPlus.obj K) ≅
      (etaleModuleInvariants Λ G Y).mapCochainComplexPlus.obj
        ((etaleModuleExtensionByZero.{u, 0} (MonoidAlgebra Λ G) i).mapCochainComplexPlus.obj K) :=
  ObjectProperty.isoMk _ (by
    exact (NatIso.mapHomologicalComplex (etaleModuleExtensionByZeroInvariants Λ G i)
      (ComplexShape.up ℤ)).app K.obj)

/-- `g^{-1}(𝒩^G) ≅ (g^{-1} 𝒩)^G`, termwise on a bounded below complex. -/
def inverseImageInvariantsComplexIso {Y Z : Scheme.{u}} (g : Y ⟶ Z)
    (K : CochainComplex.Plus (EtaleModules.{u, 0} (MonoidAlgebra Λ G) Z)) :
    (etaleModuleInverseImage.{u, 0} Λ g).mapCochainComplexPlus.obj
        ((etaleModuleInvariants Λ G Z).mapCochainComplexPlus.obj K) ≅
      (etaleModuleInvariants Λ G Y).mapCochainComplexPlus.obj
        ((etaleModuleInverseImage.{u, 0} (MonoidAlgebra Λ G) g).mapCochainComplexPlus.obj K) :=
  ObjectProperty.isoMk _ (by
    exact (NatIso.mapHomologicalComplex (etaleModuleInverseImageInvariants Λ G g)
      (ComplexShape.up ℤ)).app K.obj)

/-- `((j_! 𝒩)|_{X̄_k̄})^G ≅ (j_! (𝒩^G))|_{X̄_k̄}`, termwise. -/
def compactSupportRestrictedComplexInvariantsIso
    (K : CochainComplex.Plus (EtaleModules.{u, 0} (MonoidAlgebra Λ G) X)) :
    compactSupportRestrictedComplex f j kbar Λ
        ((etaleModuleInvariants Λ G X).mapCochainComplexPlus.obj K) ≅
      (etaleModuleInvariants Λ G _).mapCochainComplexPlus.obj
        (compactSupportRestrictedComplex f j kbar (MonoidAlgebra Λ G) K) :=
  (etaleModuleInverseImage.{u, 0} Λ
      (fieldBaseChangeProj (Over.mk j.toBase) kbar)).mapCochainComplexPlus.mapIso
      (extensionByZeroInvariantsComplexIso Λ G j.immersion K) ≪≫
    inverseImageInvariantsComplexIso Λ G (fieldBaseChangeProj (Over.mk j.toBase) kbar) _

/-- **Hochschild–Serre for compactly supported cohomology.**  For a bounded below complex `𝒩` of
sheaves of `Λ[G]`-modules on `X_étale` whose restricted extension by zero `(j_! 𝒩)|_{X̄_k̄}` has
terms acyclic for the sheaf of invariants,

`RΓ_c(X_k̄, 𝒩^G) ≅ R(-)^G (RΓ_c(X_k̄, 𝒩))`. -/
def compactSupportInvariantsIso
    (K : CochainComplex.Plus (EtaleModules.{u, 0} (MonoidAlgebra Λ G) X))
    (hK : ∀ n, (etaleModuleInvariants Λ G _).rightAcyclic
      ((compactSupportRestrictedComplex f j kbar (MonoidAlgebra Λ G) K).obj.X n)) :
    compactSupportFrobeniusCohomology.{u, 0} Λ f j kbar
        ((etaleModuleInvariants Λ G X).mapCochainComplexPlus.obj K) ≅
      (derivedInvariants Λ G).obj
        (compactSupportFrobeniusCohomology.{u, 0} (MonoidAlgebra Λ G) f j kbar K) :=
  have := isIso_mapCochainComplexPlusDerivedUnit_app_of_rightAcyclic
    (etaleModuleInvariants Λ G _) _ hK
  (etaleModuleDerivedGlobalSections.{u, 0} Λ (Spec (.of kbar))).mapIso
      ((etaleModuleDerivedDirectImage.{u, 0} Λ
          (pullback.snd (Over.mk j.toBase).hom (specAlgebraMap k kbar))).mapIso
        (DerivedCategory.Plus.Q.mapIso
            (compactSupportRestrictedComplexInvariantsIso Λ G f j kbar K) ≪≫
          asIso ((etaleModuleInvariants Λ G _).mapCochainComplexPlusDerivedUnit.app
            (compactSupportRestrictedComplex f j kbar (MonoidAlgebra Λ G) K)))) ≪≫
    (etaleModuleDerivedGlobalSections.{u, 0} Λ (Spec (.of kbar))).mapIso
      ((etaleModuleDerivedDirectImageInvariants Λ G
        (pullback.snd (Over.mk j.toBase).hom (specAlgebraMap k kbar))).app _) ≪≫
    ((etaleModuleDerivedGlobalSectionsInvariants Λ G (Spec (.of kbar))).app _).symm

end CompactSupport

end Stacks.EtaleCohomology

end
