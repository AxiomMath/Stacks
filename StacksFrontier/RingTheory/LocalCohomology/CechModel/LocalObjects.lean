module

public import Mathlib.Algebra.Category.ModuleCat.Products
public import StacksFrontier.RingTheory.Dualizing.Ext
public import StacksFrontier.RingTheory.LocalCohomology.CechModel.BoundedTerms

/-!
# Modules on which an element acts invertibly are orthogonal to torsion objects

Let `A` be a commutative ring, `g ∈ A`, and let `N` be an `A`-module on which `g` acts
invertibly, so that the localization map `N ⟶ N[1/g]` is an isomorphism. If `W` is an object of
`D(A)` killed by the derived localization at `g` — for instance an object whose cohomology is
`I`-power torsion for an ideal `I` containing `g` — then there is no nonzero morphism from `W` to
`N` placed in any degree. This is the computation which makes the terms of the extended
alternating Čech complex in positive degrees invisible to torsion objects, and hence makes that
complex a coreflection.

A finite direct sum of such modules, with a possibly different element acting invertibly on each
summand, is again orthogonal to `W`: a finite direct sum of modules is a product, and morphisms
into a product are detected by their components.

## Main results

* `Stacks.LocalCohomology.isIso_derivedUnit_app_singleFunctor` — a transformation out of the
  identity which is invertible on `N` is invertible on `N` placed in degree `q`.
* `Stacks.LocalCohomology.subsingleton_hom_singleFunctor_of_isUnit_smul` — a module on which `g`
  acts invertibly, placed in any degree, receives no nonzero morphism from an object killed by
  the derived localization at `g`.
* `Stacks.LocalCohomology.subsingleton_hom_singleFunctor_directSum` — the same for a finite
  direct sum of such modules.

## References

* [Stacks Project, Tag 0A6R](https://stacks.math.columbia.edu/tag/0A6R)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [local instance] HasDerivedCategory.standard

universe v u

namespace Stacks.LocalCohomology

section General

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory C]
  (L : C ⥤ C) [L.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L] (τ : 𝟭 C ⟶ L)

/-- A natural transformation between functors whose values at an object are both zero is
invertible there. -/
theorem isIso_app_of_isZero {D₁ D₂ : Type*} [Category D₁] [Category D₂] {F G : D₁ ⥤ D₂}
    (σ : F ⟶ G) (X : D₁) (hF : IsZero (F.obj X)) (hG : IsZero (G.obj X)) :
    IsIso (σ.app X) :=
  ⟨⟨hG.to_ _, hF.eq_of_src _ _, hG.eq_of_tgt _ _⟩⟩

/-- A transformation out of the identity which is invertible on every term of a cochain complex
is invertible on the object of the derived category it defines. -/
theorem isIso_derivedUnit_app_Q_obj (K : CochainComplex C ℤ)
    (h : ∀ i, IsIso (τ.app (K.X i))) :
    IsIso ((Dualizing.PowerTorsionBaseChange.derivedUnit L τ).app
      (DerivedCategory.Q.obj K)) := by
  rw [Dualizing.PowerTorsionBaseChange.derivedUnit_app_Q]
  have h' : ∀ i, IsIso (((Dualizing.PowerTorsionBaseChange.complexUnit L τ).app K).f i) := h
  have : IsIso ((Dualizing.PowerTorsionBaseChange.complexUnit L τ).app K) :=
    HomologicalComplex.Hom.isIso_of_components _
  infer_instance

/-- A transformation out of the identity which is invertible on `N` is invertible on `N` placed
in degree `q`. -/
theorem isIso_derivedUnit_app_singleFunctor (N : C) (q : ℤ) (hN : IsIso (τ.app N)) :
    IsIso ((Dualizing.PowerTorsionBaseChange.derivedUnit L τ).app
      ((DerivedCategory.singleFunctor C q).obj N)) := by
  refine Dualizing.PowerTorsionBaseChange.isIso_app_of_iso _
    ((DerivedCategory.singleFunctorIsoCompQ C q).app N) ?_
  refine isIso_derivedUnit_app_Q_obj L τ _ (fun i => ?_)
  by_cases hi : i = q
  · subst hi
    exact Dualizing.PowerTorsionBaseChange.isIso_app_of_iso τ
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) i N) hN
  · have hz : IsZero (((CochainComplex.singleFunctor C q).obj N).X i) :=
      HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) q N i hi
    exact isIso_app_of_isZero τ _ hz (L.map_isZero hz)

end General

section Subsingleton

variable {D : Type u} [Category.{v} D]

/-- Morphisms into a product are detected componentwise, so there is no nonzero morphism into a
product of objects receiving no nonzero morphism. -/
theorem subsingleton_hom_pi (W : D) {ι : Type*} (Z : ι → D) [HasProduct Z]
    (h : ∀ j, Subsingleton (W ⟶ Z j)) : Subsingleton (W ⟶ ∏ᶜ Z) :=
  ⟨fun _f _g => limit.hom_ext fun j => (h j.as).elim _ _⟩

/-- Transport of the absence of nonzero morphisms along an isomorphism of targets. -/
theorem subsingleton_hom_of_iso {W X Y : D} (e : X ≅ Y) (h : Subsingleton (W ⟶ X)) :
    Subsingleton (W ⟶ Y) :=
  (Iso.homCongr (Iso.refl W) e.symm).injective.subsingleton

end Subsingleton

section Localization

open Dualizing.PowerTorsionBaseChange

variable {A : Type u} [CommRing A]

/-- If `g` acts invertibly on `N`, multiplication by `g` is an automorphism of `N`. -/
theorem isIso_smul_id_of_isUnit (g : A) (N : ModuleCat.{max v u} A)
    (h : IsUnit (algebraMap A (Module.End A N) g)) : IsIso (g • 𝟙 N) := by
  rw [ConcreteCategory.isIso_iff_bijective]
  have he : (g • 𝟙 N).hom = algebraMap A (Module.End A N) g :=
    LinearMap.ext fun x => by simp [Module.algebraMap_end_apply]
  change Function.Bijective (g • 𝟙 N).hom
  rw [he]
  exact (Module.End.isUnit_iff _).mp h

/-- **Orthogonality of a local module to a torsion object.** If `g` acts invertibly on the
`A`-module `N` and the derived localization of `W` at `g` vanishes, then every morphism from `W`
to `N` placed in degree `q` is zero. -/
theorem subsingleton_hom_singleFunctor_of_isUnit_smul (g : A)
    (W : DerivedCategory (ModuleCat.{max v u} A)) (hW : IsZero ((locDerived.{v} g).obj W))
    (N : ModuleCat.{max v u} A) (hN : IsUnit (algebraMap A (Module.End A N) g)) (q : ℤ) :
    Subsingleton (W ⟶ (DerivedCategory.singleFunctor (ModuleCat.{max v u} A) q).obj N) := by
  have hloc : IsIso ((locDerivedUnit.{v} g).app
      ((DerivedCategory.singleFunctor (ModuleCat.{max v u} A) q).obj N)) :=
    isIso_derivedUnit_app_singleFunctor (locFunctor.{v} g) (locUnit.{v} g) N q
      (isIso_locUnit_of_isIso_smul g N (isIso_smul_id_of_isUnit g N hN))
  exact subsingleton_of_forall_eq 0 fun u =>
    hom_eq_zero_of_isLocal (locDerived.{v} g) (locDerivedUnit.{v} g) hW hloc u

/-- The same conclusion for a finite direct sum of modules, each carrying its own element acting
invertibly on it. -/
theorem subsingleton_hom_singleFunctor_directSum {ι : Type} [Finite ι] (g : ι → A)
    (N : ι → ModuleCat.{max v u} A) (W : DerivedCategory (ModuleCat.{max v u} A))
    (hW : ∀ j, IsZero ((locDerived.{v} (g j)).obj W))
    (hN : ∀ j, IsUnit (algebraMap A (Module.End A (N j)) (g j))) (q : ℤ) :
    Subsingleton (W ⟶ (DerivedCategory.singleFunctor (ModuleCat.{max v u} A) q).obj
      (ModuleCat.of A (DirectSum ι (fun j => (N j : Type (max v u)))))) := by
  classical
  have : Fintype ι := Fintype.ofFinite ι
  have e₁ : ModuleCat.of A (DirectSum ι (fun j => (N j : Type (max v u)))) ≅ ∏ᶜ N :=
    (DirectSum.linearEquivFunOnFintype A ι (fun j => (N j : Type (max v u)))).toModuleIso ≪≫
      (ModuleCat.piIsoPi N).symm
  refine subsingleton_hom_of_iso
    ((DerivedCategory.singleFunctor (ModuleCat.{max v u} A) q).mapIso e₁).symm ?_
  refine subsingleton_hom_of_iso
    (PreservesProduct.iso (DerivedCategory.singleFunctor (ModuleCat.{max v u} A) q) N).symm ?_
  exact subsingleton_hom_pi W _ fun j =>
    subsingleton_hom_singleFunctor_of_isUnit_smul (g j) W (hW j) (N j) (hN j) q

end Localization

end Stacks.LocalCohomology

end
