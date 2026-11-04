module

public import StacksFrontier.AlgebraicGeometry.Duality.CompactGeneration.AffinePerfectGenerator
public import StacksFrontier.Homology.DerivedCategory.ModelComparisonGeneration

/-!
# The Koszul generator of `D_{QCoh,T}(𝒪_{Spec A})` at the standard model

`StacksFrontier/AlgebraicGeometry/Duality/CompactGeneration/AffinePerfectGenerator.lean` proves that
the sheafified Koszul complex on `f₁, …, f_r ∈ A` generates `D_{QCoh,T}(𝒪_{Spec A})`,
`T = V(f₁, …, f_r)`, at the locally small model of the derived category. This file transports
that statement to `HasDerivedCategory.standard`, which is the model at which the derived
categories of the algebraic spaces of this library live; and it records, at that model, that
an object restricting to zero on the complement of `T` has its cohomology supported on `T`.

## Main results

* `Stacks.Duality.Supported.derivedSupported_of_isZero_derivedRestrict_standard`: at the standard
  model, vanishing on an open containing the complement of `T` implies support in `T`.
* `Stacks.Duality.Supported.isZero_of_derivedSupported_of_forall_hom_koszulObject_eq_zero`: at
  the standard model, an object of `D_{QCoh,T}(𝒪_{Spec A})` receiving only zero maps from the
  shifts of the Koszul object is zero.
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for sheaves of modules on a small site.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] SheafOfModules.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.Duality.OpenImmersion Stacks.Koszul.Truncation StacksDraft.DerivedModel

universe u

namespace Stacks.Duality.Supported

attribute [local instance 10000] HasDerivedCategory.standard

/-- **Support from vanishing on an open, at the standard model of `D(𝒪_Z)`.** An object of
`D(𝒪_Z)` whose restriction to an open `U ⊇ Z \ T` vanishes has every cohomology sheaf with zero
stalks off `T`. This is `Stacks.Duality.Supported.derivedSupported_of_isZero_derivedRestrict` at
the standard model
`HasDerivedCategory.standard`. -/
theorem derivedSupported_of_isZero_derivedRestrict_standard {Z : Scheme.{u}} (U : Z.Opens)
    (T : Set Z)
    (hTU : Tᶜ ⊆ (U : Set Z)) (E : DerivedCategory Z.Modules)
    (h : IsZero ((derivedRestrict U.ι).obj E)) :
    derivedSupported Z.ringCatSheaf T E := fun n x hx =>
  have h₁ : IsZero ((Scheme.Modules.restrictFunctor U.ι).obj
      ((DerivedCategory.homologyFunctor Z.Modules n).obj E)) :=
    IsZero.of_iso ((DerivedCategory.isZero_iff_forall_isZero_homology _).1 h n)
      ((StacksDraft.DerivedCategoryHomology.mapDerivedCategoryHomologyIso
        (Scheme.Modules.restrictFunctor U.ι) n).app E).symm
  have _hpz := AlgebraicGeometry.SheafOfModules.stalkAddCommGroupFunctor_preservesZeroMorphisms
    U.toScheme.ringCatSheaf (⟨x, hTU hx⟩ : U.toScheme)
  IsZero.of_iso
    (Functor.map_isZero (SheafOfModules.stalkAddCommGroupFunctor U.toScheme.ringCatSheaf
      (⟨x, hTU hx⟩ : U.toScheme)) h₁)
    ((Scheme.Modules.restrictStalkNatIso U.ι (⟨x, hTU hx⟩ : U.toScheme)).app
      ((DerivedCategory.homologyFunctor Z.Modules n).obj E)).symm

variable {A : Type u} [CommRing A] {r : ℕ} (f : Fin r → A)

/-- **The sheafified Koszul object generates `D_{QCoh,T}(𝒪_{Spec A})` at the standard model.** For
`T = V(f₁, …, f_r)`, an object of `D(𝒪_{Spec A})` with quasi-coherent cohomology supported on `T`
which receives only zero maps from the integer shifts of the Koszul object is zero.

The statement at the locally small model is
`Stacks.Duality.Supported.isZero_of_quasiCoherentSupported_of_forall_hom_koszulObject_eq_zero`;
the comparison of the two models preserves the cohomology objects, carries the Koszul object to
the Koszul object compatibly with the shifts, and is an equivalence. -/
theorem isZero_of_derivedSupported_of_forall_hom_koszulObject_eq_zero
    (E : DerivedCategory (Spec (CommRingCat.of A)).Modules)
    (hqc : derivedQuasiCoherent (Spec (CommRingCat.of A)) E)
    (hsupp : derivedSupported (Spec (CommRingCat.of A)).ringCatSheaf
      (((openComplement f : (Spec (CommRingCat.of A)).Opens) :
        Set (Spec (CommRingCat.of A)))ᶜ) E)
    (h : ∀ (n : ℤ) (g : (koszulObject f)⟦n⟧ ⟶ E), g = 0) :
    IsZero E := by
  let hD := HasDerivedCategory.standard (Spec (CommRingCat.of A)).Modules
  let hls : HasDerivedCategory.{u} (Spec (CommRingCat.of A)).Modules :=
    AlgebraicGeometry.Scheme.Modules.hasDerivedCategory _
  refine isZero_of_isZero_modelEquiv_functor_obj hD hls E ?_
  have key : ∀ (P : ObjectProperty (Spec (CommRingCat.of A)).Modules)
      [P.IsClosedUnderIsomorphisms], @DerivedCategoryB.derivedCategoryB _ _ _ hD P E →
      @DerivedCategoryB.derivedCategoryB _ _ _ hls P ((modelEquiv hD hls).functor.obj E) :=
    fun P _ hP => (derivedCategoryB_modelEquiv_functor_obj_iff P hD hls E).2 hP
  refine isZero_of_quasiCoherentSupported_of_forall_hom_koszulObject_eq_zero f
    ((modelEquiv hD hls).functor.obj E) ⟨?_, ?_⟩ ?_
  · exact @key _ (inferInstanceAs (SheafOfModules.isQuasicoherent
      (Spec (CommRingCat.of A)).ringCatSheaf).IsClosedUnderIsomorphisms) hqc
  · exact @key _ (supportedModules_isClosedUnderIsomorphisms _ _) hsupp
  · exact forall_hom_shift_eq_zero_modelEquiv hD hls _ E h

end Stacks.Duality.Supported

end
