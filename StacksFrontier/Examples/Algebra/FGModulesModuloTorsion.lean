module

public import Mathlib.Algebra.Category.FGModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Localization
public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.CategoryTheory.Abelian.SerreClass.Localization
public import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects
public import Mathlib.CategoryTheory.Localization.LocalizerMorphism
public import Mathlib.RingTheory.Localization.Finiteness
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Localization.Module
public import StacksCore.CategoryTheory.Abelian.SerreClass.Localization
public import StacksCore.CategoryTheory.Abelian.SerreClass.Weak
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Examples.Algebra.ModulesModuloTorsion

/-!
# Finitely generated modules modulo torsion

For a Noetherian domain `A`, the Serre quotient of finitely generated `A`-modules by the finitely
generated torsion modules is canonically equivalent to the category of finite-dimensional vector
spaces over the fraction field of `A`.

The functor realizing the equivalence is extension of scalars to the fraction field, which on
finitely generated modules is the restriction of module localization at the nonzerodivisors. It is
essentially surjective because a finite-dimensional vector space is the localization of a free
module of the same rank, and it is fully faithful after inverting the torsion morphisms: a linear
map between localizations lifts, after multiplying by a nonzerodivisor, to a map of the original
finitely generated (hence finitely presented) modules, and multiplication by a nonzerodivisor has
torsion kernel and cokernel.

## Main definitions

* `Stacks.Examples.fgTorsionModuleProperty`: the property of being a finitely generated torsion
  module.
* `Stacks.Examples.fgFractionModuleFunctor`: extension of scalars to the fraction field on
  finitely generated modules.

## Main results

* `Stacks.Examples.fgTorsionModuleProperty_isSerreClass`: the finitely generated torsion modules
  form a Serre subcategory.
* `Stacks.Examples.fgFractionModuleFunctor_isLocalization`: the canonical functor presents the
  Serre quotient as the category of finite-dimensional fraction-field vector spaces.

## Implementation notes

`FGModuleCat (FractionRing A)` is the category of finite-dimensional vector spaces over the
fraction field. The `IsLocalization` structure specifies the canonical equivalence: its source is
the quotient at the morphisms with torsion kernel and cokernel, and its target is this category of
vector spaces. The first tagged instance covers the Serre subcategory; the second covers the
equivalence and its compatibility with scalar extension.

## References

* [Stacks Project, Tag 0B0L](https://stacks.math.columbia.edu/tag/0B0L)
-/

@[expose] public noncomputable section

universe u v

namespace Stacks.Examples

open CategoryTheory Module
open CategoryTheory.Limits

/-- Finitely generated modules annihilated elementwise by nonzerodivisors of `A`. -/
public def fgTorsionModuleProperty (A : Type u) [CommRing A] :
    ObjectProperty (FGModuleCat.{v} A) :=
  fun M ↦ ∀ x : M, ∃ s : nonZeroDivisors A, (s : A) • x = 0

/-- Extension of scalars from a finitely generated module to the fraction field. -/
public def fgFractionModuleFunctor (A : Type u) [CommRing A] [Small.{v, u} A] :
    FGModuleCat.{v} A ⥤ FGModuleCat.{v} (FractionRing A) :=
  (ModuleCat.isFG (FractionRing A)).lift
    ((forget₂ (FGModuleCat.{v} A) (ModuleCat.{v} A)) ⋙
      ModuleCat.localizedModuleFunctor (nonZeroDivisors A))
    (by
      intro M
      change Module.Finite (FractionRing A)
        (M.obj.localizedModule (nonZeroDivisors A))
      have : Module.Finite A M.obj := M.property
      exact Module.Finite.of_isLocalizedModule (nonZeroDivisors A)
        (M.obj.localizedModuleMkLinearMap (nonZeroDivisors A)))

/-- Finitely generated torsion modules form a Serre subcategory. -/
@[stacks 0B0L "the Serre subcategory"]
public instance fgTorsionModuleProperty_isSerreClass (A : Type u) [CommRing A]
    [IsNoetherianRing A] :
    (fgTorsionModuleProperty A : ObjectProperty (FGModuleCat.{v} A)).IsSerreClass :=
  let F := forget₂ (FGModuleCat.{v} A) (ModuleCat.{v} A)
  letI : F.Additive := ⟨by intros; rfl⟩
  have hmap : ∀ (S : ShortComplex (FGModuleCat.{v} A)), S.Exact → (S.map F).Exact :=
    ((Functor.exact_tfae F).out 4 2).mp (by constructor <;> infer_instance)
  { exists_zero := by
      let Z : FGModuleCat.{v} A := FGModuleCat.of A PUnit
      refine ⟨Z, CategoryTheory.Limits.IsZero.of_full_of_faithful_of_isZero F Z ?_, ?_⟩
      · exact ModuleCat.isZero_of_subsingleton (ModuleCat.of A PUnit)
      · intro x
        exact ⟨1, by subsingleton⟩
    prop_of_mono := by
      intro X Y f hf hY x
      obtain ⟨s, hs⟩ := hY (f.hom.hom x)
      refine ⟨s, (ModuleCat.mono_iff_injective f.hom).mp (Functor.map_mono F f) ?_⟩
      simpa only [map_smul, map_zero] using hs
    prop_of_epi := by
      intro X Y f hf hX y
      obtain ⟨x, hx⟩ := (ModuleCat.epi_iff_surjective (F.map f)).mp
        (Functor.map_epi F f) y
      obtain ⟨s, hs⟩ := hX x
      refine ⟨s, ?_⟩
      rw [← hx]
      calc
        (s : A) • (F.map f).hom x = (F.map f).hom ((s : A) • x) := by rw [map_smul]
        _ = 0 := by simpa only [map_zero] using congrArg (F.map f).hom hs
    prop_X₂_of_shortExact := by
      intro S hS h₁ h₃ x
      let T := S.map F
      have hT : T.Exact := hmap S hS.exact
      have hTfun : Function.Exact T.f.hom T.g.hom :=
        (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact T).mp hT
      obtain ⟨t, ht⟩ := h₃ (S.g.hom.hom x)
      have hzero : T.g.hom ((t : A) • x) = 0 := by
        rw [map_smul]
        change (t : A) • S.g.hom.hom x = 0
        exact ht
      obtain ⟨y, hy⟩ := (hTfun ((t : A) • x)).mp hzero
      obtain ⟨s, hs⟩ := h₁ y
      refine ⟨s * t, ?_⟩
      calc
        (s * t : A) • x = (s : A) • ((t : A) • x) := by rw [mul_smul]
        _ = (s : A) • T.f.hom y := by rw [← hy]
        _ = T.f.hom ((s : A) • y) := by rw [map_smul]
        _ = 0 := by rw [hs, map_zero] }

private lemma fgFractionModuleFunctor_essSurj (A : Type u) [CommRing A]
    [IsDomain A] [Small.{v, u} A] :
    (fgFractionModuleFunctor A).EssSurj := by
  refine ⟨fun X => ?_⟩
  let K := FractionRing A
  let n := Module.finrank K X
  let V := Shrink.{v} (Fin n →₀ A)
  let M : FGModuleCat.{v} A := FGModuleCat.of A V
  let bA : Basis (Fin n) A V :=
    (Finsupp.basisSingleOne : Basis (Fin n) A (Fin n →₀ A)).map
      (Shrink.linearEquiv A (Fin n →₀ A)).symm
  let bK : Basis (Fin n) K X := Module.finBasis K X
  let bLoc : Basis (Fin n) K ((fgFractionModuleFunctor A).obj M) := by
    change Basis (Fin n) K (M.obj.localizedModule (nonZeroDivisors A))
    let : IsLocalizedModule (nonZeroDivisors A)
        (M.obj.localizedModuleMkLinearMap (nonZeroDivisors A)) :=
      M.obj.localizedModule_isLocalizedModule (nonZeroDivisors A)
    exact bA.ofIsLocalizedModule K (nonZeroDivisors A)
      (M.obj.localizedModuleMkLinearMap (nonZeroDivisors A))
  exact ⟨M, ⟨(bLoc.equiv bK (Equiv.refl _)).toFGModuleCatIso⟩⟩

private lemma fgFractionModuleFunctor_hom_lift (A : Type u) [CommRing A]
    [IsDomain A] [IsNoetherianRing A] [Small.{v, u} A]
    (M N : FGModuleCat.{v} A)
    (f : M.obj.localizedModule (nonZeroDivisors A) →ₗ[Localization (nonZeroDivisors A)]
      N.obj.localizedModule (nonZeroDivisors A)) :
    ∃ (g : M.obj →ₗ[A] N.obj) (s : nonZeroDivisors A),
      IsLocalizedModule.mapExtendScalars (nonZeroDivisors A)
        (M.obj.localizedModuleMkLinearMap (nonZeroDivisors A))
        (N.obj.localizedModuleMkLinearMap (nonZeroDivisors A))
        (Localization (nonZeroDivisors A)) g =
          algebraMap A (Localization (nonZeroDivisors A)) (s : A) • f := by
  let S := nonZeroDivisors A
  let : Module.FinitePresentation A M.obj := Module.finitePresentation_of_finite A M.obj
  let g₀ : M.obj →ₗ[A] N.obj.localizedModule S :=
    f.restrictScalars A ∘ₗ M.obj.localizedModuleMkLinearMap S
  obtain ⟨g, s, hg⟩ := Module.FinitePresentation.exists_lift_of_isLocalizedModule S
    (N.obj.localizedModuleMkLinearMap S) g₀
  refine ⟨g, s, ?_⟩
  apply LinearMap.restrictScalars_injective A
  apply IsLocalizedModule.linearMap_ext S (M.obj.localizedModuleMkLinearMap S)
    (N.obj.localizedModuleMkLinearMap S)
  ext x
  calc
    (IsLocalizedModule.map S (M.obj.localizedModuleMkLinearMap S)
      (N.obj.localizedModuleMkLinearMap S)) g (M.obj.localizedModuleMkLinearMap S x) =
        N.obj.localizedModuleMkLinearMap S (g x) :=
      IsLocalizedModule.map_apply S _ _ g x
    _ = algebraMap A (Localization S) (s : A) •
      f (M.obj.localizedModuleMkLinearMap S x) := by
      simpa [g₀, LinearMap.comp_apply, LinearMap.smul_apply, Submonoid.smul_def,
        IsScalarTower.algebraMap_smul] using
        congrArg (fun q : M.obj →ₗ[A] N.obj.localizedModule S => q x) hg

/-- Localizing finitely generated modules at the nonzerodivisors presents the category of
finite-dimensional fraction-field vector spaces as their Serre quotient by the torsion
modules. -/
@[stacks 0B0L "the canonical equivalence"]
public instance fgFractionModuleFunctor_isLocalization (A : Type u) [CommRing A]
    [IsDomain A] [IsNoetherianRing A] [Small.{v, u} A] :
    (fgFractionModuleFunctor A : FGModuleCat.{v} A ⥤
      FGModuleCat.{v} (FractionRing A)).IsLocalization
      (fgTorsionModuleProperty A : ObjectProperty (FGModuleCat.{v} A)).isoModSerre := by
  let S := nonZeroDivisors A
  let P := fgTorsionModuleProperty A
  let Q := localizationTorsionModuleProperty (R := A) S
  let F := forget₂ (FGModuleCat.{v} A) (ModuleCat.{v} A)
  let G := forget₂ (FGModuleCat.{v} (FractionRing A))
    (ModuleCat.{v} (FractionRing A))
  let M := ModuleCat.localizedModuleFunctor.{v} S
  let L := fgFractionModuleFunctor A
  let : Q.IsSerreClass := localizationTorsionModuleProperty_isSerreClass S
  let : M.IsLocalization Q.isoModSerre := localizedModuleFunctor_isLocalization S
  let : F.Additive := ⟨by intros; rfl⟩
  have hF : Limits.PreservesFiniteLimits F ∧ Limits.PreservesFiniteColimits F := by
    constructor <;> infer_instance
  let : Limits.PreservesFiniteLimits F := hF.1
  let : Limits.PreservesFiniteColimits F := hF.2
  let : Limits.PreservesFiniteLimits (F ⋙ M) := Limits.comp_preservesFiniteLimits F M
  let : Limits.PreservesFiniteColimits (F ⋙ M) := Limits.comp_preservesFiniteColimits F M
  let Φ : LocalizerMorphism P.isoModSerre Q.isoModSerre := by
    refine ⟨F, ?_⟩
    intro X Y f hf
    change P (kernel f) ∧ P (cokernel f) at hf
    exact ⟨Q.prop_of_iso (PreservesKernel.iso F f) hf.1,
      Q.prop_of_iso (PreservesCokernel.iso F f) hf.2⟩
  let : CatCommSq Φ.functor L M G := ⟨((ModuleCat.isFG (FractionRing A)).liftCompιIso _ _).symm⟩
  have hInv : P.isoModSerre.IsInvertedBy (F ⋙ M) := by
    intro X Y f hf
    exact Localization.inverts M Q.isoModSerre (F.map f) (Φ.map f hf)
  let H : P.isoModSerre.Localization ⥤ ModuleCat.{v} (FractionRing A) :=
    Localization.lift (F ⋙ M) hInv P.isoModSerre.Q
  let fac := Localization.fac (F ⋙ M) hInv P.isoModSerre.Q
  have hkernel : P = (F ⋙ M).kernel := by
    ext X
    exact (congrFun (localizedModuleFunctor_kernel_eq (R := A) S) (F.obj X)).symm.to_iff
  have hFaith : H.Faithful :=
    (ObjectProperty.SerreClassLocalization.faithful_iff P.isoModSerre.Q P H fac).2 hkernel
  have hFull : H.Full := by
    refine ⟨?_⟩
    intro X Y f
    let : P.isoModSerre.Q.EssSurj :=
      Localization.essSurj P.isoModSerre.Q P.isoModSerre
    obtain ⟨M₀, ⟨iM⟩⟩ := Functor.EssSurj.mem_essImage P.isoModSerre.Q X
    obtain ⟨N₀, ⟨iN⟩⟩ := Functor.EssSurj.mem_essImage P.isoModSerre.Q Y
    let f₀ := H.map iM.hom ≫ f ≫ H.map iN.inv
    let f₁ := (fac.app M₀).inv ≫ f₀ ≫ (fac.app N₀).hom
    obtain ⟨g, s, hg⟩ := fgFractionModuleFunctor_hom_lift A M₀ N₀ f₁.hom
    let g₀ : M₀ ⟶ N₀ := FGModuleCat.ofHom g
    let μ : N₀ ⟶ N₀ := FGModuleCat.ofHom ((s : A) • LinearMap.id)
    have hkerRange : Q (ModuleCat.of A (F.map μ).hom.ker) := by
      intro x
      rcases x with ⟨x, hx⟩
      refine ⟨s, ?_⟩
      apply Subtype.ext
      have hμx : (F.map μ).hom x = (s : A) • x := by
        change ((s : A) • LinearMap.id) x = (s : A) • x
        simp
      change (s : A) • x = 0
      rw [← hμx]
      exact hx
    have hker : Q (kernel (F.map μ)) :=
      Q.prop_of_iso (ModuleCat.kernelIsoKer (F.map μ)).symm hkerRange
    have hcoker : Q (cokernel (F.map μ)) := by
      intro y
      obtain ⟨x, rfl⟩ := (ModuleCat.epi_iff_surjective
        (cokernel.π (F.map μ))).mp (by infer_instance) y
      refine ⟨s, ?_⟩
      rw [← map_smul]
      have hμx : (F.map μ).hom x = (s : A) • x := by
        change ((s : A) • LinearMap.id) x = (s : A) • x
        simp
      rw [← hμx]
      exact cokernel.condition_apply (F.map μ) x
    have hμ : P.isoModSerre μ := by
      rw [ObjectProperty.isoModSerre_iff P]
      constructor
      · rw [ObjectProperty.monoModSerre_iff P]
        have hk : Q (F.obj (kernel μ)) :=
          Q.prop_of_iso (PreservesKernel.iso F μ).symm hker
        change P (kernel μ)
        exact hk
      · rw [ObjectProperty.epiModSerre_iff P]
        have hc : Q (F.obj (cokernel μ)) :=
          Q.prop_of_iso (PreservesCokernel.iso F μ).symm hcoker
        change P (cokernel μ)
        exact hc
    have hμiso : IsIso (P.isoModSerre.Q.map μ) :=
      Localization.inverts P.isoModSerre.Q P.isoModSerre μ hμ
    let : IsIso (P.isoModSerre.Q.map μ) := hμiso
    have hFMiso : IsIso ((F ⋙ M).map μ) := hInv μ hμ
    let : IsIso ((F ⋙ M).map μ) := hFMiso
    let q₀ : P.isoModSerre.Q.obj M₀ ⟶ P.isoModSerre.Q.obj N₀ :=
      P.isoModSerre.Q.map g₀ ≫ inv (P.isoModSerre.Q.map μ)
    let q := iM.inv ≫ q₀ ≫ iN.hom
    let : Module A (M₀.obj.localizedModule S) :=
      M₀.obj.instModuleCarrierLocalizationLocalizedModule S
    let : Module A (N₀.obj.localizedModule S) :=
      N₀.obj.instModuleCarrierLocalizationLocalizedModule S
    let : Module A ((F ⋙ M).obj M₀) :=
      M₀.obj.instModuleCarrierLocalizationLocalizedModule S
    let : Module A ((F ⋙ M).obj N₀) :=
      N₀.obj.instModuleCarrierLocalizationLocalizedModule S
    let : Module (Localization S) (M₀.obj.localizedModule S) := inferInstance
    let : Module (Localization S) (N₀.obj.localizedModule S) := inferInstance
    let : Module (Localization S) ((F ⋙ M).obj M₀) := inferInstance
    let : Module (Localization S) ((F ⋙ M).obj N₀) := inferInstance
    let : IsScalarTower A (Localization S) (M₀.obj.localizedModule S) := inferInstance
    let : IsScalarTower A (Localization S) (N₀.obj.localizedModule S) := inferInstance
    let : IsScalarTower A (Localization S) ((F ⋙ M).obj M₀) := by
      change IsScalarTower A (Localization S) (M₀.obj.localizedModule S)
      infer_instance
    let : IsScalarTower A (Localization S) ((F ⋙ M).obj N₀) := by
      change IsScalarTower A (Localization S) (N₀.obj.localizedModule S)
      infer_instance
    have hmapg : ((F ⋙ M).map g₀).hom =
        algebraMap A (Localization S) (s : A) • f₁.hom := by
      change IsLocalizedModule.mapExtendScalars S
        (M₀.obj.localizedModuleMkLinearMap S) (N₀.obj.localizedModuleMkLinearMap S)
        (Localization S) g = _
      exact hg
    have hmapμ : ((F ⋙ M).map μ).hom =
        algebraMap A (Localization S) (s : A) • LinearMap.id := by
      apply LinearMap.restrictScalars_injective A
      apply IsLocalizedModule.linearMap_ext S
        (N₀.obj.localizedModuleMkLinearMap S) (N₀.obj.localizedModuleMkLinearMap S)
      ext x
      calc
        (IsLocalizedModule.map S (N₀.obj.localizedModuleMkLinearMap S)
          (N₀.obj.localizedModuleMkLinearMap S)) ((s : A) • LinearMap.id)
            (N₀.obj.localizedModuleMkLinearMap S x) =
              N₀.obj.localizedModuleMkLinearMap S ((s : A) • x) :=
          IsLocalizedModule.map_apply S _ _ ((s : A) • LinearMap.id) x
        _ = (LinearMap.restrictScalars A
            ((algebraMap A (Localization S) (s : A)) •
              (LinearMap.id : N₀.obj.localizedModule S →ₗ[Localization S]
                N₀.obj.localizedModule S)) ∘ₗ
            N₀.obj.localizedModuleMkLinearMap S) x := by
          simp
    have hfactor : (F ⋙ M).map g₀ = f₁ ≫ (F ⋙ M).map μ := by
      apply ModuleCat.hom_ext
      change ((F ⋙ M).map g₀).hom = ((F ⋙ M).map μ).hom.comp f₁.hom
      rw [hmapg, hmapμ]
      ext x
      simp only [LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.id_apply]
    have hq0 : H.map q₀ = f₀ := by
      have htr : (fac.app M₀).inv ≫ H.map q₀ ≫ (fac.app N₀).hom = f₁ := by
        dsimp [q₀]
        rw [Functor.map_comp, Functor.map_inv]
        have hnatg : (fac.app M₀).inv ≫ H.map (P.isoModSerre.Q.map g₀) =
            (F ⋙ M).map g₀ ≫ (fac.app N₀).inv :=
          (fac.inv.naturality g₀).symm
        have hnatμ0 : (F ⋙ M).map μ ≫ (fac.app N₀).inv =
            (fac.app N₀).inv ≫ H.map (P.isoModSerre.Q.map μ) :=
          fac.inv.naturality μ
        have hnatμ : inv ((F ⋙ M).map μ) ≫ (fac.app N₀).inv =
            (fac.app N₀).inv ≫ inv (H.map (P.isoModSerre.Q.map μ)) := by
          apply (cancel_mono (H.map (P.isoModSerre.Q.map μ))).1
          rw [Category.assoc, ← hnatμ0]
          simp [Category.assoc]
        calc
          (((fac.app M₀).inv ≫ H.map (P.isoModSerre.Q.map g₀)) ≫
              inv (H.map (P.isoModSerre.Q.map μ))) ≫ (fac.app N₀).hom =
            (((F ⋙ M).map g₀ ≫ (fac.app N₀).inv) ≫
              inv (H.map (P.isoModSerre.Q.map μ))) ≫ (fac.app N₀).hom := by rw [hnatg]
          _ = (F ⋙ M).map g₀ ≫
              ((fac.app N₀).inv ≫ inv (H.map (P.isoModSerre.Q.map μ)) ≫
                (fac.app N₀).hom) := by simp [Category.assoc]
          _ = (F ⋙ M).map g₀ ≫ inv ((F ⋙ M).map μ) := by
            congr 1
            calc
              (fac.app N₀).inv ≫ inv (H.map (P.isoModSerre.Q.map μ)) ≫
                (fac.app N₀).hom =
                inv ((F ⋙ M).map μ) ≫ (fac.app N₀).inv ≫ (fac.app N₀).hom := by
                  rw [← Category.assoc, ← hnatμ]
                  simp [Category.assoc]
              _ = inv ((F ⋙ M).map μ) := by simp
          _ = f₁ := by
            rw [hfactor]
            simp [Category.assoc]
      apply (cancel_epi (fac.app M₀).inv).1
      apply (cancel_mono (fac.app N₀).hom).1
      simpa [f₁, Category.assoc] using htr
    have hq : H.map q = f := by
      dsimp [q]
      rw [Functor.map_comp, Functor.map_comp]
      simp [hq0, f₀, Category.assoc]
    exact ⟨q, hq⟩
  let : H.Full := hFull
  let : H.Faithful := hFaith
  let : CatCommSq Φ.functor P.isoModSerre.Q M H := ⟨fac.symm⟩
  let : Φ.IsLocalizedFullyFaithful :=
    LocalizerMorphism.IsLocalizedFullyFaithful.mk' Φ P.isoModSerre.Q M H
      (Functor.FullyFaithful.ofFullyFaithful H)
  let : G.Full := inferInstance
  let : G.Faithful := inferInstance
  let : L.EssSurj := fgFractionModuleFunctor_essSurj A
  exact LocalizerMorphism.isLocalization_of_isLocalizedFullyFaithful Φ
    (iso := CatCommSq.iso Φ.functor L M G)

end Stacks.Examples

end
