module

public import StacksFrontier.AlgebraicGeometry.DerivedGlobalSectionsRestrictIso
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.RelativeFinitePushforward
public import StacksFrontier.AlgebraicGeometry.Spaces.ProjectiveTwistHigherDirectImageVanishing
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedQuasicoherentDerivedSquare
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedZariskiDerivedSections

/-!
# Derived sections of a direct image across `ε`, over an affine base

Let `g : T' ⟶ T` be a morphism of the big fppf site over `S` with `T` affine, whose represented
morphism of algebraic spaces `h_g` is quasi-compact and quasi-separated, and let
`Z ∈ D_QCoh(𝒪_{T'})` on the Zariski site of the scheme `T'`. Then the derived sections over
the algebraic space `h_T` of `R(h_g)_* Lε^* Z` are the derived sections of `Z` over `T'`, read
as `Γ(T, 𝒪)`-modules:

`RΓ(h_T, R(h_g)_* Lε^* Z) ≅ RΓ(T', Z)`.

Over the base `Spec A` this identifies the étale `RΓ` with the `A`-linear Zariski `RΓ`, so the
two are pseudo-coherent together.

## Main results

* `AlgebraicGeometry.Space.nonempty_representedAffineDerivedSections_pushforward_iso`
* `AlgebraicGeometry.nonempty_derivedGlobalSectionsOver_iso_restrictScalars`: `A`-linear derived
  global sections are derived sections over `⊤` with scalars restricted.
* `AlgebraicGeometry.Space.isPseudoCoherent_representedAffineDerivedSections_pushforward_iff`
* `AlgebraicGeometry.Space.nonempty_representedAffineDerivedSections_representedSpaceMap_iso`:
  `RΓ(h_T, R(h_g)_* N) ≅ RΓ(h_{T'}, N)` over `Γ(T)` for `T`, `T'` affine.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

attribute [local instance 10000] HasDerivedCategory.standard

namespace AlgebraicGeometry

variable {A : Type u} [CommRing A] {Y : Scheme.{u}} (f : Y ⟶ Spec (CommRingCat.of A))

/-- **`A`-linear derived global sections are derived sections over `⊤`, with scalars restricted
along `A ≅ Γ(Spec A, 𝒪) ⟶ Γ(Y, 𝒪_Y)`.** Both are computed on a K-injective representative by
the same functor. -/
theorem nonempty_derivedGlobalSectionsOver_iso_restrictScalars (E : DerivedCategory Y.Modules) :
    Nonempty ((derivedGlobalSectionsOver f).obj E ≅
      (ModuleCat.restrictScalars.{u}
        (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom).mapDerivedCategory.obj
        ((ModuleCat.restrictScalars.{u} (f.app ⊤).hom).mapDerivedCategory.obj
          ((derivedSectionsUnbounded Y (f ⁻¹ᵁ ⊤)).obj E))) := by
  have hres := Stacks.Cohomology.Localization.enoughKInjectives (C := Y.Modules)
  obtain ⟨I, hI, ⟨e⟩⟩ := exists_isKInjective_representative hres E
  let F := Stacks.Cohomology.sectionsFunctor Y (f ⁻¹ᵁ ⊤)
  let R₁ := ModuleCat.restrictScalars.{u} (f.app ⊤).hom
  let R₂ := ModuleCat.restrictScalars.{u} (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom
  let D := derivedSectionsUnbounded Y (f ⁻¹ᵁ ⊤)
  let eD := rightDerivedObjIso hres F inferInstance D
    (derivedSectionsUnboundedUnit Y (f ⁻¹ᵁ ⊤)) inferInstance I hI
  let eG := rightDerivedObjIso hres (globalSectionsOver f) inferInstance
    (derivedGlobalSectionsOver f) (derivedGlobalSectionsOverUnit f) inferInstance I hI
  exact ⟨(derivedGlobalSectionsOver f).mapIso e.symm ≪≫ eG.symm ≪≫
    DerivedCategory.Q.mapIso (Iso.refl _ : _ ≅ (R₂.mapHomologicalComplex (.up ℤ)).obj
      ((R₁.mapHomologicalComplex (.up ℤ)).obj ((F.mapHomologicalComplex (.up ℤ)).obj I))) ≪≫
    (R₂.mapDerivedCategoryFactors.app
      ((R₁.mapHomologicalComplex (.up ℤ)).obj ((F.mapHomologicalComplex (.up ℤ)).obj I))).symm ≪≫
    R₂.mapDerivedCategory.mapIso ((R₁.mapDerivedCategoryFactors.app
        ((F.mapHomologicalComplex (.up ℤ)).obj I)).symm ≪≫
      R₁.mapDerivedCategory.mapIso (eD ≪≫ D.mapIso e))⟩

end AlgebraicGeometry

namespace AlgebraicGeometry.Space

section General

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {T' T : BigFppfOver B S hS}
  (g : T' ⟶ T)

/-- **`RΓ(h_T, R(h_g)_* Lε^* Z) ≅ RΓ(T', Z)` over an affine `T`.** The direct image square of
Stacks 08GH and the unit of Stacks 071Q identify `Rε_*` of the left side with `Rg_{0,*} Z`; the
affine comparison of derived sections across `ε` and Stacks 0D5W on the scheme side finish. -/
theorem nonempty_representedAffineDerivedSections_pushforward_iso
    [IsAffine ((BigFppfOver.toScheme B S hS).obj T)]
    (hfqc : IsQuasiCompact B S hS (schemeSpaceMap g).hom)
    (hfqs : IsQuasiSeparated B S hS (schemeSpaceMap g).hom)
    (Z : DerivedCategory (representedSchemeRepresentedZariskiRingedToposHom B S hS T').Modules)
    (hZ : ∀ q : ℤ, ((DerivedCategory.homologyFunctor _ q).obj Z).IsQuasicoherent) :
    Nonempty ((representedAffineDerivedSections B S hS T).obj
        ((derivedModulePushforward B S hS (schemeSpaceMap g)).obj
          ((representedZariskiDerivedPullback B S hS T').obj Z)) ≅
      (ModuleCat.restrictScalars.{u} ((B.inclusion.map g.left).app ⊤).hom).mapDerivedCategory.obj
        ((derivedSectionsUnbounded (representedSchemeRepresentedZariskiRingedToposHom B S hS T')
          ((B.inclusion.map g.left) ⁻¹ᵁ ⊤)).obj Z)) := by
  let W := (derivedModulePushforward B S hS (schemeSpaceMap g)).obj
    ((representedZariskiDerivedPullback B S hS T').obj Z)
  have hLZ : QcohDerived B S hS (schemeSpace T')
      ((representedZariskiDerivedPullback B S hS T').obj Z) := fun q =>
    isQuasicoherentOnSite_homology_representedZariskiDerivedPullback_obj B S hS T' Z hZ q
  have hW : QcohDerived B S hS (schemeSpace T) W :=
    qcohDerived_derivedModulePushforward_obj B S hS _ hfqc hfqs _ hLZ
  have hεW := isQuasicoherent_homology_representedZariskiDerivedPushforward_obj B S hS T W hW
  have := isIso_representedZariskiDerivedAdjunction_counit_app B S hS T W hW
  have := isIso_representedZariskiDerivedAdjunction_unit_app B S hS T' Z hZ
  obtain ⟨e₂⟩ := nonempty_representedAffineDerivedSections_representedZariskiDerivedPullback_iso
    T ((representedZariskiDerivedPushforward B S hS T).obj W) hεW
  obtain ⟨e₅⟩ := nonempty_derivedSectionsPushforwardIso (B.inclusion.map g.left) ⊤ Z
  let e₁ : (representedZariskiDerivedPushforward B S hS T).obj W ≅
      (RingedSpace.derivedPushforward (B.inclusion.map g.left).toLRSHom.toShHom).obj Z :=
    (representedDerivedPushforwardSquareIso g).app Z ≪≫
      (Stacks.Cohomology.DerivedPushforward.derivedPushforward
          (X := (representedSchemeRepresentedZariskiRingedToposHom B S hS T').zariskiRingedTopos)
          (Y := (representedSchemeRepresentedZariskiRingedToposHom B S hS T).zariskiRingedTopos)
          (B.inclusion.map g.left).zariskiRingedToposHom).mapIso
        (asIso ((representedZariskiDerivedAdjunction B S hS T').unit.app Z)).symm ≪≫
      (Scheme.Hom.zariskiDerivedPushforwardIso (B.inclusion.map g.left)).app Z
  exact ⟨(representedAffineDerivedSections B S hS T).mapIso
      (asIso ((representedZariskiDerivedAdjunction B S hS T).counit.app W)).symm ≪≫ e₂ ≪≫
    (derivedSectionsUnbounded _ ⊤).mapIso e₁ ≪≫ e₅.symm⟩

attribute [local instance 5000] SmallEtale.instHasSheafify SmallEtale.instWEqualsLocallyBijective
  SmallEtale.instHasSheafifyOver SmallEtale.instWEqualsLocallyBijectiveOver

/-- **`RΓ(h_T, R(h_g)_* N) ≅ RΓ(h_{T'}, N)` with scalars restricted along `Γ(T) ⟶ Γ(T')`**, for
`g : T' ⟶ T` with `T` and `T'` affine and `N ∈ D_QCoh(𝒪_{h_{T'}})`: write `N = Lε^*Rε_*N`
(Stacks 071Q) and compare both sides with the Zariski `RΓ(T', Rε_*N)`. -/
theorem nonempty_representedAffineDerivedSections_representedSpaceMap_iso
    [IsAffine ((BigFppfOver.toScheme B S hS).obj T)]
    [IsAffine ((BigFppfOver.toScheme B S hS).obj T')]
    (hfqc : IsQuasiCompact B S hS (schemeSpaceMap g).hom)
    (hfqs : IsQuasiSeparated B S hS (schemeSpaceMap g).hom)
    (N : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS
      (schemeSpace T'))))
    (hN : QcohDerived B S hS (schemeSpace T') N) :
    Nonempty ((representedAffineDerivedSections B S hS T).obj
        ((derivedModulePushforward B S hS (schemeSpaceMap g)).obj N) ≅
      (ModuleCat.restrictScalars.{u} ((B.inclusion.map g.left).app ⊤).hom).mapDerivedCategory.obj
        ((representedAffineDerivedSections B S hS T').obj N)) := by
  have := isIso_representedZariskiDerivedAdjunction_counit_app B S hS T' N hN
  have hZ := isQuasicoherent_homology_representedZariskiDerivedPushforward_obj B S hS T' N hN
  obtain ⟨e₁⟩ := nonempty_representedAffineDerivedSections_pushforward_iso g hfqc hfqs
    ((representedZariskiDerivedPushforward B S hS T').obj N) hZ
  obtain ⟨e₂⟩ := nonempty_representedAffineDerivedSections_representedZariskiDerivedPullback_iso
    T' ((representedZariskiDerivedPushforward B S hS T').obj N) hZ
  let c := asIso ((representedZariskiDerivedAdjunction B S hS T').counit.app N)
  exact ⟨(representedAffineDerivedSections B S hS T).mapIso
      ((derivedModulePushforward B S hS (schemeSpaceMap g)).mapIso c.symm) ≪≫ e₁ ≪≫
    (ModuleCat.restrictScalars.{u} ((B.inclusion.map g.left).app ⊤).hom).mapDerivedCategory.mapIso
      (e₂.symm ≪≫ (representedAffineDerivedSections B S hS T').mapIso c)⟩

end General

section SpecBase

variable {B : BigFppfSite.{u}} {A : Type u} [CommRing A] {hA : B.Contains (Spec (CommRingCat.of A))}
  {T' : BigFppfOver B (Spec (CommRingCat.of A)) hA}

/-- The base `Spec A`, as an object of its own big fppf site, is affine. -/
instance isAffine_toScheme_baseSiteObj_spec :
    IsAffine ((BigFppfOver.toScheme B (Spec (CommRingCat.of A)) hA).obj
      (baseSiteObj B (Spec (CommRingCat.of A)) hA)) :=
  inferInstanceAs (IsAffine (Spec (CommRingCat.of A)))

/-- Pseudo-coherence is invariant under isomorphism in the derived category. -/
private theorem isPseudoCoherent_iff_of_iso {R : Type*} [Ring R]
    [HasDerivedCategory (ModuleCat.{u} R)] {K L : DerivedCategory (ModuleCat.{u} R)} (e : K ≅ L) :
    StacksDraft.PseudoCoherence.IsPseudoCoherent K ↔
      StacksDraft.PseudoCoherence.IsPseudoCoherent L :=
  ⟨fun h => h.ofIso e, fun h => h.ofIso e.symm⟩

/-- **The étale and the Zariski `RΓ` over `Spec A` are pseudo-coherent together.** For
`g : T' ⟶ Spec A` in the site with `h_g` quasi-compact and quasi-separated, and
`Z ∈ D_QCoh(𝒪_{T'})`, the complex `RΓ(Spec A, R(h_g)_* Lε^* Z)` of the algebraic spaces is
pseudo-coherent exactly when the `A`-linear `RΓ(T', Z)` is. -/
theorem isPseudoCoherent_representedAffineDerivedSections_pushforward_iff
    (g : T' ⟶ baseSiteObj B (Spec (CommRingCat.of A)) hA)
    (hfqc : IsQuasiCompact B _ hA (schemeSpaceMap g).hom)
    (hfqs : IsQuasiSeparated B _ hA (schemeSpaceMap g).hom)
    (Z : DerivedCategory (representedSchemeRepresentedZariskiRingedToposHom B _ hA T').Modules)
    (hZ : ∀ q : ℤ, ((DerivedCategory.homologyFunctor _ q).obj Z).IsQuasicoherent) :
    StacksDraft.PseudoCoherence.IsPseudoCoherent
        ((representedAffineDerivedSections B _ hA (baseSiteObj B _ hA)).obj
          ((derivedModulePushforward B _ hA (schemeSpaceMap g)).obj
            ((representedZariskiDerivedPullback B _ hA T').obj Z))) ↔
      StacksDraft.PseudoCoherence.IsPseudoCoherent
        ((derivedGlobalSectionsOver (B.inclusion.map g.left)).obj Z) := by
  obtain ⟨e₁⟩ := nonempty_representedAffineDerivedSections_pushforward_iso g hfqc hfqs Z hZ
  obtain ⟨e₂⟩ := nonempty_derivedGlobalSectionsOver_iso_restrictScalars
    (B.inclusion.map g.left) Z
  let e : A ≃+* Γ(Spec (CommRingCat.of A), ⊤) :=
    (Scheme.ΓSpecIso (CommRingCat.of A)).symm.commRingCatIsoToRingEquiv
  exact (isPseudoCoherent_iff_of_iso e₁).trans
    ((StacksDraft.PseudoCoherence.pseudoCoherent_iff_of_ringEquiv e _).2.trans
      (isPseudoCoherent_iff_of_iso e₂.symm))

/-- `AlgebraicGeometry.Space.isPseudoCoherent_representedAffineDerivedSections_pushforward_iff`
with the morphism of schemes of `g` named, so that it can be instantiated where that morphism
has another spelling. -/
theorem isPseudoCoherent_representedAffineDerivedSections_pushforward_iff_of_eq
    (g : T' ⟶ baseSiteObj B (Spec (CommRingCat.of A)) hA)
    (f : representedSchemeRepresentedZariskiRingedToposHom B _ hA T' ⟶ Spec (CommRingCat.of A))
        (hf : B.inclusion.map g.left = f)
    (hfqc : IsQuasiCompact B _ hA (schemeSpaceMap g).hom)
    (hfqs : IsQuasiSeparated B _ hA (schemeSpaceMap g).hom)
    (Z : DerivedCategory (representedSchemeRepresentedZariskiRingedToposHom B _ hA T').Modules)
    (hZ : ∀ q : ℤ, ((DerivedCategory.homologyFunctor _ q).obj Z).IsQuasicoherent) :
    StacksDraft.PseudoCoherence.IsPseudoCoherent
        ((representedAffineDerivedSections B _ hA (baseSiteObj B _ hA)).obj
          ((derivedModulePushforward B _ hA (schemeSpaceMap g)).obj
            ((representedZariskiDerivedPullback B _ hA T').obj Z))) ↔
      StacksDraft.PseudoCoherence.IsPseudoCoherent ((derivedGlobalSectionsOver f).obj Z) := by
  subst hf
  exact isPseudoCoherent_representedAffineDerivedSections_pushforward_iff g hfqc hfqs Z hZ

end SpecBase

end AlgebraicGeometry.Space

end
