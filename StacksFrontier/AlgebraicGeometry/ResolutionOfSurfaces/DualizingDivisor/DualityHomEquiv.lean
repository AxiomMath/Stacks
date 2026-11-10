module

public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizingModule
public import StacksFrontier.AlgebraicGeometry.Duality.CompactGeneration.QcqsCompactGeneration
public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.AffineDerivedEquivalence
public import StacksFrontier.AlgebraicGeometry.ProperSupportCoherent.LerayLocallySmall
public import StacksFrontier.AlgebraicGeometry.QuasiCoherent.Coherator.QcqsPushforwardAnyModel

/-!
# Duality over an affine base, read in `D(A)`

Let `f : X ⟶ Spec(A)` be a quasi-compact quasi-separated morphism with `X` quasi-compact and
quasi-separated, and let `N` be an object of `D(A)`. Write `f^×` for the right adjoint of
`Rf_* : D_QCoh(𝒪_X) ⥤ D_QCoh(𝒪_{Spec A})` ([Stacks, Tag 0A9E]) and `Ñ` for the derived
sheafification of `N`. For every `F` in `D_QCoh(𝒪_X)` there is a bijection
`Hom_X(F, f^× Ñ) ≃ Hom_{D(A)}(RΓ(X, F), N)`, natural in `F`. It is the composite of the adjunction
`Rf_* ⊣ f^×`, the equivalence `D(A) ≃ D_QCoh(𝒪_{Spec A})` of [Stacks, Tag 06Z0], under which
`RΓ(Spec A, -)` is inverse to derived sheafification, and Leray `RΓ(X, -) = RΓ(Spec A, Rf_* -)`
([Stacks, Tag 0D5W]). This is the form of duality used in the proof of [Stacks, Tag 0EA2].

## Main definitions

* `AlgebraicGeometry.DualizingDivisor.dualityHomEquiv`: the bijection
  `Hom_X(F, f^× Ñ) ≃ Hom_{D(A)}(RΓ(X, F), N)`.

## Main results

* `AlgebraicGeometry.DualizingDivisor.dualityHomEquiv_comp`: its naturality in `F`.

## References

* [Stacks Project, Tag 0A9E](https://stacks.math.columbia.edu/tag/0A9E)
* [Stacks Project, Tag 06Z0](https://stacks.math.columbia.edu/tag/06Z0)
* [Stacks Project, Tag 0D5W](https://stacks.math.columbia.edu/tag/0D5W)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for `R`-modules.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] ModuleCat.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Stacks.Duality

universe u

namespace AlgebraicGeometry.DualizingDivisor

variable {A : Type u} [CommRing A] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A))
  [QuasiCompact f] [QuasiSeparated f] [CompactSpace X] [QuasiSeparatedSpace X]

/-- Derived sheafification `D(A) ≌ D_QCoh(𝒪_{Spec A})`, as an equivalence
([Stacks, Tag 06Z0]). -/
def tildeEquivalence :
    DerivedCategory (ModuleCat.{u} A) ≌ quasiCoherentDerivedCategory (Spec (CommRingCat.of A)) :=
  @Functor.asEquivalence _ _ _ _ (derivedTilde (CommRingCat.of A))
    (derivedTilde_isEquivalence (CommRingCat.of A))

/-- The inverse of derived sheafification is `RΓ(Spec A, -)` on `D_QCoh(𝒪_{Spec A})`: both are
right adjoint to derived sheafification. -/
def tildeEquivalenceInverseIso :
    (tildeEquivalence (A := A)).inverse ≅
      derivedGlobalSectionsQuasicoherent (CommRingCat.of A) :=
  (tildeEquivalence (A := A)).toAdjunction.rightAdjointUniq
    (derivedTildeQuasicoherentAdjunction (CommRingCat.of A))

/-- Morphisms into a derived sheafification `Ñ` are morphisms of `RΓ(Spec A, -)` into `N`:
`RΓ(Spec A, -)` on `D_QCoh(𝒪_{Spec A})` is inverse to derived sheafification
([Stacks, Tag 06Z0]). -/
def globalSectionsTildeHomEquiv (M : quasiCoherentDerivedCategory (Spec (CommRingCat.of A)))
    (N : DerivedCategory (ModuleCat.{u} A)) :
    (M ⟶ (derivedTilde (CommRingCat.of A)).obj N) ≃
      ((derivedGlobalSectionsQuasicoherent (CommRingCat.of A)).obj M ⟶ N) where
  toFun g := tildeEquivalenceInverseIso.inv.app M ≫
    ((tildeEquivalence (A := A)).symm.toAdjunction.homEquiv M N).symm g
  invFun h := (tildeEquivalence (A := A)).symm.toAdjunction.homEquiv M N
    (tildeEquivalenceInverseIso.hom.app M ≫ h)
  left_inv g := by
    simp only [Iso.hom_inv_id_app_assoc]
    exact Equiv.apply_symm_apply _ g
  right_inv h := by
    simp only [Equiv.symm_apply_apply, Iso.inv_hom_id_app_assoc]

/-- Naturality of `globalSectionsTildeHomEquiv` in `M`: precomposing with `β : M' ⟶ M`
corresponds to precomposing with `RΓ(Spec A, β)`. -/
theorem globalSectionsTildeHomEquiv_comp
    {M M' : quasiCoherentDerivedCategory (Spec (CommRingCat.of A))}
    (N : DerivedCategory (ModuleCat.{u} A)) (β : M' ⟶ M)
    (g : M ⟶ (derivedTilde (CommRingCat.of A)).obj N) :
    globalSectionsTildeHomEquiv M' N (β ≫ g) =
      (derivedGlobalSectionsQuasicoherent (CommRingCat.of A)).map β ≫
        globalSectionsTildeHomEquiv M N g := by
  change tildeEquivalenceInverseIso.inv.app M' ≫
      ((tildeEquivalence (A := A)).symm.toAdjunction.homEquiv M' N).symm (β ≫ g) =
    _ ≫ tildeEquivalenceInverseIso.inv.app M ≫
      ((tildeEquivalence (A := A)).symm.toAdjunction.homEquiv M N).symm g
  have h : ((tildeEquivalence (A := A)).symm.toAdjunction.homEquiv M' N).symm (β ≫ g) =
      (tildeEquivalence (A := A)).inverse.map β ≫
        ((tildeEquivalence (A := A)).symm.toAdjunction.homEquiv M N).symm g :=
    Adjunction.homEquiv_naturality_left_symm _ _ _
  rw [h, ← Category.assoc, ← Category.assoc]
  congr 1
  exact (tildeEquivalenceInverseIso.inv.naturality β).symm

/-- Leray over the base ring ([Stacks, Tag 0D5W]) at an object of `D_QCoh(𝒪_X)`, with the target
written as `RΓ(Spec A, -)` of the restricted derived direct image. -/
def lerayIso (F : quasiCoherentDerivedCategory X) :
    (derivedGlobalSectionsOver f).obj F.obj ≅
      (derivedGlobalSectionsQuasicoherent (CommRingCat.of A)).obj
        ((quasiCoherentDerivedPushforward f
          (isQuasicoherent_homology_derivedPushforward_of_qcqs f)).obj F) :=
  (derivedGlobalSectionsOverPushforwardIsoLocallySmall f).app F.obj

omit [CompactSpace X] [QuasiSeparatedSpace X] in
/-- The isomorphisms `lerayIso f F` are natural in `F`. -/
theorem lerayIso_hom_naturality {F F' : quasiCoherentDerivedCategory X} (β : F' ⟶ F) :
    (lerayIso f F').hom ≫ (derivedGlobalSectionsQuasicoherent (CommRingCat.of A)).map
        ((quasiCoherentDerivedPushforward f
          (isQuasicoherent_homology_derivedPushforward_of_qcqs f)).map β) =
      (derivedGlobalSectionsOver f).map β.hom ≫ (lerayIso f F).hom :=
  ((derivedGlobalSectionsOverPushforwardIsoLocallySmall f).hom.naturality β.hom).symm

/-- **Duality over an affine base, read in `D(A)`.** For `F` in `D_QCoh(𝒪_X)` and `N` in `D(A)`,
morphisms `F ⟶ f^× Ñ` correspond to morphisms `RΓ(X, F) ⟶ N` of `D(A)`: adjunction
`Rf_* ⊣ f^×` ([Stacks, Tag 0A9E]), then `D_QCoh(𝒪_{Spec A}) ≃ D(A)` ([Stacks, Tag 06Z0]), then
Leray `RΓ(X, F) ≅ RΓ(Spec A, Rf_* F)` ([Stacks, Tag 0D5W]). -/
def dualityHomEquiv (F : quasiCoherentDerivedCategory X) (N : DerivedCategory (ModuleCat.{u} A)) :
    (F ⟶ (twistedInverseImage f (isQuasicoherent_homology_derivedPushforward_of_qcqs f)).obj
        ((derivedTilde (CommRingCat.of A)).obj N)) ≃
      ((derivedGlobalSectionsOver f).obj F.obj ⟶ N) where
  toFun g := (lerayIso f F).hom ≫ globalSectionsTildeHomEquiv _ N
    (((twistedInverseImageAdjunction f
      (isQuasicoherent_homology_derivedPushforward_of_qcqs f)).homEquiv F _).symm g)
  invFun h := (twistedInverseImageAdjunction f
      (isQuasicoherent_homology_derivedPushforward_of_qcqs f)).homEquiv F _
    ((globalSectionsTildeHomEquiv _ N).symm ((lerayIso f F).inv ≫ h))
  left_inv g := by
    dsimp only
    rw [Iso.inv_hom_id_assoc, Equiv.symm_apply_apply, Equiv.apply_symm_apply]
  right_inv h := by
    dsimp only
    rw [Equiv.symm_apply_apply, Equiv.apply_symm_apply, Iso.hom_inv_id_assoc]

/-- `dualityHomEquiv f F N g` is the Leray isomorphism followed by the image under
`globalSectionsTildeHomEquiv` of the adjoint of `g` along `Rf_* ⊣ f^×`. -/
theorem dualityHomEquiv_apply (F : quasiCoherentDerivedCategory X)
    (N : DerivedCategory (ModuleCat.{u} A))
    (g : F ⟶ (twistedInverseImage f (isQuasicoherent_homology_derivedPushforward_of_qcqs f)).obj
        ((derivedTilde (CommRingCat.of A)).obj N)) :
    dualityHomEquiv f F N g = (lerayIso f F).hom ≫ globalSectionsTildeHomEquiv _ N
      (((twistedInverseImageAdjunction f
        (isQuasicoherent_homology_derivedPushforward_of_qcqs f)).homEquiv F _).symm g) := by
  rfl

/-- **Naturality of `dualityHomEquiv` in `F`.** -/
theorem dualityHomEquiv_comp {F F' : quasiCoherentDerivedCategory X}
    (N : DerivedCategory (ModuleCat.{u} A)) (β : F' ⟶ F)
    (g : F ⟶ (twistedInverseImage f (isQuasicoherent_homology_derivedPushforward_of_qcqs f)).obj
        ((derivedTilde (CommRingCat.of A)).obj N)) :
    dualityHomEquiv f F' N (β ≫ g) =
      (derivedGlobalSectionsOver f).map β.hom ≫ dualityHomEquiv f F N g := by
  rw [dualityHomEquiv_apply, dualityHomEquiv_apply, Adjunction.homEquiv_naturality_left_symm,
    globalSectionsTildeHomEquiv_comp, ← Category.assoc, lerayIso_hom_naturality]
  exact Category.assoc _ _ _

end AlgebraicGeometry.DualizingDivisor

end
