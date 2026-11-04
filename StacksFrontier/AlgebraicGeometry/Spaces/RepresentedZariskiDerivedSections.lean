module

public import StacksFrontier.AlgebraicGeometry.Cohomology.DerivedSections
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.DerivedSectionsUnbounded
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineQuasicoherentDerivedEquivalence
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedZariskiDerivedEquivalence
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedZariskiModuleAdjunction
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedZariskiPullbackSquare
public import StacksFrontier.Algebra.Homology.DerivedCategory.KInjective

/-!
# Derived sections across `ε` on an affine representable algebraic space

Let `T` be an object of the big fppf site over `S` whose underlying scheme `X_0` is affine, and
let `ε : (X_étale, 𝒪_X) ⟶ (X_{0,Zar}, 𝒪_{X_0})` be the comparison morphism for the algebraic
space `X = yoneda.obj T`. For `F ∈ D_QCoh(𝒪_{X_0})` the derived sections of `Lε^* F` over `X`
are the derived sections of `F` over `X_0`:

`RΓ(X, Lε^* F) ≅ RΓ(X_0, F)`.

The sections over `X` are the sections over `X_0` of `ε_*`, and `ε_*` carries K-injective
complexes to K-injective complexes, being right adjoint to the exact functor `ε^*`; so both
sides are computed on a K-injective complex `I` representing `Lε^* F` by `Γ(X_0, ε_* I)`, and
`ε_* I` represents `Rε_* Lε^* F = F` (Stacks 071Q).

## Main results

* `Scheme.specSectionsIso`: sections through `X_0 ≅ Spec Γ(X_0, 𝒪)` are the sections over
  `X_0`.
* `Space.nonempty_representedAffineDerivedSections_representedZariskiDerivedPullback_iso`:
  **`RΓ(X, Lε^* F) ≅ RΓ(X_0, F)`** for `F ∈ D_QCoh(𝒪_{X_0})`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Scheme

variable (X : Scheme.{u}) [IsAffine X]

/-- **Global sections read through `X ≅ Spec Γ(X, 𝒪_X)`.** Pushing an `𝒪_X`-module forward to
`Spec Γ(X, 𝒪_X)` and taking global sections there is taking global sections over `X`. -/
theorem isoSpec_hom_appTop_ΓSpecIso_inv_smul (M : X.Modules) (r : Γ(X, ⊤))
    (x : Γ(M, ⊤)) : (X.isoSpec.hom.appTop ((Scheme.ΓSpecIso Γ(X, ⊤)).inv r)) • x = r • x := by
  have h : X.isoSpec.hom.appTop ((Scheme.ΓSpecIso Γ(X, ⊤)).inv r) = r := by
    change X.toSpecΓ.appTop ((Scheme.ΓSpecIso Γ(X, ⊤)).inv r) = r
    rw [Scheme.toSpecΓ_appTop, ← CommRingCat.comp_apply, Iso.inv_hom_id, CommRingCat.id_apply]
  rw [h]

/-- The global sections of `M` read through `X ≅ Spec Γ(X, 𝒪_X)`, as a `Γ(X, 𝒪_X)`-module, are
the global sections of `M`: the underlying map is the identity. -/
def specSectionsIsoApp (M : X.Modules) :
    (Scheme.Modules.pushforward X.isoSpec.hom ⋙ moduleSpecΓFunctor (R := Γ(X, ⊤))).obj M ≅
      (Stacks.Cohomology.sectionsFunctor X ⊤).obj M :=
  (AddEquiv.toLinearEquiv
    (M := ↑((Scheme.Modules.pushforward X.isoSpec.hom ⋙ moduleSpecΓFunctor (R := Γ(X, ⊤))).obj M))
    (M₂ := ↑((Stacks.Cohomology.sectionsFunctor X ⊤).obj M))
    (by rfl) (fun r x ↦ isoSpec_hom_appTop_ΓSpecIso_inv_smul X M r x)).toModuleIso

/-- **Global sections read through `X ≅ Spec Γ(X, 𝒪_X)`.** Pushing an `𝒪_X`-module forward to
`Spec Γ(X, 𝒪_X)` and taking global sections there is taking global sections over `X`. -/
def specSectionsIso :
    Scheme.Modules.pushforward X.isoSpec.hom ⋙ moduleSpecΓFunctor (R := Γ(X, ⊤)) ≅
      Stacks.Cohomology.sectionsFunctor X ⊤ :=
  NatIso.ofComponents (specSectionsIsoApp X) fun _ ↦ rfl

end AlgebraicGeometry.Scheme

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

namespace AlgebraicGeometry.Space

attribute [local instance 10000] HasDerivedCategory.standard

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} (T : BigFppfOver B S hS)

/-- The inverse of the equivalence of module categories of Stacks 04M0 in its reindexing form is
the transport `AlgebraicGeometry.Space.representedModuleRestriction`: both are right adjoint to
the same transport of modules. -/
def representedSmallEtaleModuleEquivalenceInverseAdjointIso :
    (representedSmallEtaleModuleEquivalence B S hS T).inverse ≅
      representedModuleRestriction B S hS T :=
  Adjunction.rightAdjointUniq (representedSmallEtaleModuleEquivalence B S hS T).toAdjunction
    ((representedModuleEquivalence.{u, u} B S hS T).toAdjunction.ofNatIsoLeft
      (representedModulePushforwardIsoSmallEtaleModuleEquivalenceFunctor B S hS T))

variable [IsAffine ((BigFppfOver.toScheme B S hS).obj T)]

/-- The sections over an affine represented algebraic space are the sections over its scheme of
`ε_*`. -/
def representedAffineSectionsIso :
    representedAffineSections B S hS T ≅
      representedZariskiModulePushforwardRepresentedZariskiPullbackExact B S hS T ⋙
        (Scheme.Modules.pushforward ((BigFppfOver.toScheme B S hS).obj T).isoSpec.hom ⋙
          moduleSpecΓFunctor (R := Γ((BigFppfOver.toScheme B S hS).obj T, ⊤))) :=
  Functor.isoWhiskerRight (representedSmallEtaleModuleEquivalenceInverseAdjointIso T) _ ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (representedZariskiModulePushforwardIsoRepresentedZariskiModuleAdjunction B S hS T).symm _

/-- The sections over an affine represented algebraic space are the sections over its scheme of
`ε_*`, with the sections over the scheme spelled as `Stacks.Cohomology.sectionsFunctor`. -/
def representedAffineSectionsZariskiIso :
    representedAffineSections B S hS T ≅
      representedZariskiModulePushforwardRepresentedZariskiPullbackExact B S hS T ⋙
        Stacks.Cohomology.sectionsFunctor
          (representedSchemeRepresentedZariskiRingedToposHom B S hS T) ⊤ :=
  representedAffineSectionsIso T ≪≫
    Functor.isoWhiskerLeft _
      (Scheme.specSectionsIso (representedSchemeRepresentedZariskiRingedToposHom B S hS T))

/-- **`RΓ(X, Lε^* F) ≅ RΓ(X_0, F)`** for `F ∈ D_QCoh(𝒪_{X_0})` on an affine represented
algebraic space: both are computed by `Γ(X_0, ε_* I)` for a K-injective complex `I` representing
`Lε^* F`, and `ε_* I` represents `Rε_* Lε^* F = F`. -/
theorem nonempty_representedAffineDerivedSections_representedZariskiDerivedPullback_iso
    (F : DerivedCategory (representedSchemeRepresentedZariskiRingedToposHom B S hS T).Modules)
    (hF : ∀ q : ℤ, ((DerivedCategory.homologyFunctor _ q).obj F).IsQuasicoherent) :
    Nonempty ((representedAffineDerivedSections B S hS T).obj
        ((representedZariskiDerivedPullback B S hS T).obj F) ≅
      (derivedSectionsUnbounded
        (representedSchemeRepresentedZariskiRingedToposHom B S hS T) ⊤).obj F) := by
  obtain ⟨I, hI, ⟨eI⟩⟩ := Stacks.Cohomology.UnboundedComplexes.exists_isKInjective_iso
    (A := SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS (representedSpace T)))
    DerivedCategory.Qh ((representedZariskiDerivedPullback B S hS T).obj F)
  have : I.IsKInjective := hI
  have hJ : CochainComplex.IsKInjective
      ((Functor.mapHomologicalComplex
        (representedZariskiModulePushforwardRepresentedZariskiPullbackExact B S hS T)
          (ComplexShape.up ℤ)).obj I) :=
    CochainComplex.isKInjective_mapHomologicalComplex_of_exact _ _
      (representedZariskiModuleAdjunctionRepresentedZariskiModuleAdjunction B S hS T) I
  have := isGrothendieckAbelian_modules B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T)
  have h₁ := Stacks.Cohomology.UnboundedComplexes.isIso_app_of_isKInjective
    ((representedAffineSections B S hS T).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh) DerivedCategory.Qh (representedAffineDerivedSections B S hS T)
    (Functor.totalRightDerivedUnit _ _ _) I hI
  have h₂ := Stacks.Cohomology.UnboundedComplexes.isIso_app_of_isKInjective
    ((Stacks.Cohomology.sectionsFunctor
        (representedSchemeRepresentedZariskiRingedToposHom B S hS T) ⊤).mapHomotopyCategory
      (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh) DerivedCategory.Qh
    (derivedSectionsUnbounded (representedSchemeRepresentedZariskiRingedToposHom B S hS T) ⊤)
    (derivedSectionsUnboundedUnit (representedSchemeRepresentedZariskiRingedToposHom B S hS T) ⊤)
      _ hJ
  have h₃ := isIso_representedZariskiDerivedPushforwardUnit_app_of_isKInjective B S hS T I hI
  have h₄ := isIso_representedZariskiDerivedAdjunction_unit_app B S hS T F hF
  have := Functor.preservesZeroMorphisms_of_iso (representedAffineSectionsZariskiIso T)
  exact ⟨(representedAffineDerivedSections B S hS T).mapIso eI.symm ≪≫
    (@asIso _ _ _ _ _ h₁).symm ≪≫
    DerivedCategory.Qh.mapIso ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).mapIso
      ((NatIso.mapHomologicalComplex (representedAffineSectionsZariskiIso T)
        (ComplexShape.up ℤ)).app I ≪≫ Iso.refl _)) ≪≫
    @asIso _ _ _ _ _ h₂ ≪≫
    (derivedSectionsUnbounded (representedSchemeRepresentedZariskiRingedToposHom B S hS T) ⊤).mapIso
      (@asIso _ _ _ _ _ h₃ ≪≫ (representedZariskiDerivedPushforward B S hS T).mapIso eI ≪≫
        (@asIso _ _ _ _ _ h₄).symm)⟩

end AlgebraicGeometry.Space

end
