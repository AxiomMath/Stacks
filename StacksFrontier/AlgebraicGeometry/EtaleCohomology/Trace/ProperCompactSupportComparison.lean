module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.FrobeniusRestrictionIntegralDirectImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.LowerShriekCompactification
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.ProperCohomologyExtComparison
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleComplexes.EtaleModulesCtfPullback

/-!
# `RΓ_c` of a proper scheme through an arbitrary compactification

Let `X` be proper over a finite field `k` and let `j : X ⟶ X̄` be any compactification of `X`
over `k`.  Then `j` is an open immersion with closed image (the image of a proper scheme in a
separated one is closed), hence also a closed immersion, and extension by zero along it is its
direct image: `j_! ≅ j_*`.  The direct image along the integral morphism `j` does not change the
cohomology of the geometric fibre (`Stacks.EtaleCohomology.frobeniusRestrictionDirectImageIso`),
so

`RΓ_c(X_k̄, K) = RΓ(X̄_k̄, (j_! K)|_{X̄_k̄}) ≅ RΓ(X_k̄, K|_{X_k̄})`,

naturally in `K` and compatibly with the canonical geometric Frobenius endomorphisms.  In the
reduction of the weight bound of Weil II ([Tag 03VH](https://stacks.math.columbia.edu/tag/03VH))
to curves this computes the compactly supported cohomology of the zero-dimensional strata, which
are finite, hence proper, over `k`.

## Main definitions

* `Stacks.EtaleCohomology.etaleModuleExtensionByZeroIsoDirectImageOfIsProper`: `j_! ≅ j_*`.
* `Stacks.EtaleCohomology.compactSupportFrobeniusCohomologyIsoOfIsProper`:
  `RΓ_c(X_k̄, K) ≅ RΓ(X_k̄, K|_{X_k̄})`.

## Main results

* `Stacks.EtaleCohomology.compactSupportFrobeniusCohomologyIsoOfIsProper_hom_frobenius`.
* `Stacks.EtaleCohomology.compactSupportFrobeniusCohomologyIsoOfIsProper_hom_naturality`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open Stacks.Frobenius

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard

variable (Λ : Type) [CommRing Λ] {k : Type u} [Field k] {X : Scheme.{u}}
  (f : X ⟶ Spec (.of k)) [IsProper f] (j : CompactificationOf (Over.mk f))

/-- **A compactification of a proper scheme is a closed immersion**: its image is closed, the
open immersion being universally closed as the first factor of the proper `f = f̄ ∘ j` with `f̄`
separated. -/
public instance isClosedImmersion_immersion_of_isProper : IsClosedImmersion j.immersion := by
  have : UniversallyClosed (j.immersion ≫ j.toBase) := by
    rw [CompactificationOf.immersion_toBase]
    infer_instance
  have : UniversallyClosed j.immersion := UniversallyClosed.of_comp_of_isSeparated j.immersion
    j.toBase
  exact .of_isPreimmersion _ j.immersion.isClosedMap.isClosed_range

/-- **`j_! ≅ j_*` for a compactification of a proper scheme**: `j` is open and closed, and the
square of `𝟙 X`, `𝟙 X`, `j`, `j` is cartesian since `j` is a monomorphism. -/
public def etaleModuleExtensionByZeroIsoDirectImageOfIsProper :
    etaleModuleExtensionByZero.{u, 0} Λ j.immersion ≅
      etaleModuleDirectImage.{u, 0} Λ j.immersion :=
  (Functor.leftUnitor _).symm ≪≫
    Functor.isoWhiskerRight (etaleModuleDirectImageIdIso Λ X).symm _ ≪≫
    etaleModuleExtensionByZeroDirectImageIso.{u, 0} Λ (𝟙 X) (𝟙 X) j.immersion j.immersion
      (IsKernelPair.id_of_mono j.immersion) ≪≫
    Functor.isoWhiskerRight (etaleModuleExtensionByZeroIdIso Λ X) _ ≪≫ Functor.leftUnitor _

/-- `j` as a morphism over `k`, from `X` to the ambient proper scheme of the compactification. -/
public abbrev compactificationOverHom : Over.mk f ⟶ Over.mk j.toBase :=
  Over.homMk j.immersion (CompactificationOf.immersion_toBase j)

/-- The immersion of `j`, underlying `compactificationOverHom f j`, is integral. -/
public instance : IsIntegralHom (compactificationOverHom f j).left :=
  (inferInstance : IsIntegralHom j.immersion)

/-- `j_! K ≅ j_* K`, degreewise on a bounded below complex. -/
public def extensionByZeroIsoDirectImagePlusOfIsProper
    (K : CochainComplex.Plus (EtaleModules.{u, 0} Λ X)) :
    (etaleModuleExtensionByZero.{u, 0} Λ j.immersion).mapCochainComplexPlus.obj K ≅
      (etaleModuleDirectImage.{u, 0} Λ (compactificationOverHom f j).left).mapCochainComplexPlus.obj
        K :=
  ObjectProperty.isoMk _ ((NatIso.mapHomologicalComplex
    (etaleModuleExtensionByZeroIsoDirectImageOfIsProper Λ f j) _).app K.obj)

variable (kbar : Type u) [Field kbar] [Algebra k kbar] [Fintype k]

/-- **`RΓ_c(X_k̄, K) ≅ RΓ(X_k̄, K|_{X_k̄})` for `X` proper over `k`**, through any
compactification of `X`. -/
public def compactSupportFrobeniusCohomologyIsoOfIsProper
    (K : CochainComplex.Plus (EtaleModules.{u, 0} Λ X)) :
    compactSupportFrobeniusCohomology.{u, 0} Λ f j kbar K ≅
      (etaleModuleDerivedGlobalSections.{u, 0} Λ (Spec (.of kbar))).obj
        ((etaleModuleDerivedDirectImage.{u, 0} Λ
            (pullback.snd (Over.mk f).hom (specAlgebraMap k kbar))).obj
          (fieldBaseChangeRestriction.{u, 0} Λ (Over.mk f) kbar K)) :=
  (etaleModuleDerivedGlobalSections.{u, 0} Λ (Spec (.of kbar))).mapIso
      ((etaleModuleDerivedDirectImage.{u, 0} Λ
          (pullback.snd (Over.mk j.toBase).hom (specAlgebraMap k kbar))).mapIso
        ((fieldBaseChangeRestrictionFunctor.{u, 0} Λ (Over.mk j.toBase) kbar).mapIso
          (extensionByZeroIsoDirectImagePlusOfIsProper Λ f j K))) ≪≫
    (frobeniusRestrictionDirectImageIso Λ (compactificationOverHom f j) kbar K).symm

/-- **The identification is natural in the complex.** -/
public theorem compactSupportFrobeniusCohomologyIsoOfIsProper_hom_naturality
    {K K' : CochainComplex.Plus (EtaleModules.{u, 0} Λ X)} (φ : K ⟶ K') :
    (compactSupportFrobeniusFunctor.{u, 0} Λ f j kbar).map φ ≫
        (compactSupportFrobeniusCohomologyIsoOfIsProper Λ f j kbar K').hom =
      (compactSupportFrobeniusCohomologyIsoOfIsProper Λ f j kbar K).hom ≫
        (etaleModuleDerivedGlobalSections.{u, 0} Λ (Spec (.of kbar))).map
          ((etaleModuleDerivedDirectImage.{u, 0} Λ
              (pullback.snd (Over.mk f).hom (specAlgebraMap k kbar))).map
            ((fieldBaseChangeRestrictionFunctor.{u, 0} Λ (Over.mk f) kbar).map φ)) := by
  have h₁ : (etaleModuleExtensionByZero.{u, 0} Λ j.immersion).mapCochainComplexPlus.map φ ≫
        (extensionByZeroIsoDirectImagePlusOfIsProper Λ f j K').hom =
      (extensionByZeroIsoDirectImagePlusOfIsProper Λ f j K).hom ≫
        (etaleModuleDirectImage.{u, 0} Λ
          (compactificationOverHom f j).left).mapCochainComplexPlus.map φ := by
    ext n : 2
    exact (etaleModuleExtensionByZeroIsoDirectImageOfIsProper Λ f j).hom.naturality (φ.hom.f n)
  have h₁' := congrArg (fun t => (etaleModuleDerivedGlobalSections.{u, 0} Λ (Spec (.of kbar))).map
    ((etaleModuleDerivedDirectImage.{u, 0} Λ
      (pullback.snd (Over.mk j.toBase).hom (specAlgebraMap k kbar))).map
        ((fieldBaseChangeRestrictionFunctor.{u, 0} Λ (Over.mk j.toBase) kbar).map t))) h₁
  simp only [Functor.map_comp] at h₁'
  have h₂ := frobeniusRestrictionDirectImageIso_hom_naturality Λ (compactificationOverHom f j)
    kbar φ
  exact comp_comp_eq_comp_comp_of_squares _ _ _ _ _ _ _ h₁'
    (comp_inv_eq_inv_comp_of_hom_comm _ _ _ _ h₂)

variable (p q : ℕ) [Fact p.Prime] [CharP k p] (hcard : Fintype.card k = p ^ q)

/-- **The identification `RΓ_c(X_k̄, K) ≅ RΓ(X_k̄, K|_{X_k̄})` commutes with the canonical
geometric Frobenius.** -/
public theorem compactSupportFrobeniusCohomologyIsoOfIsProper_hom_frobenius
    (K : CochainComplex.Plus (EtaleModules.{u, 0} Λ X)) :
    canonicalCompactSupportFrobenius.{u, 0} Λ f j kbar p q hcard K ≫
        (compactSupportFrobeniusCohomologyIsoOfIsProper Λ f j kbar K).hom =
      (compactSupportFrobeniusCohomologyIsoOfIsProper Λ f j kbar K).hom ≫
        frobeniusRestrictionCohomologyEndo.{u, 0} Λ (Over.mk f) kbar p q hcard K := by
  have h₁ := frobeniusRestrictionCohomologyEndo_naturality (Λ := Λ) (Over.mk j.toBase) kbar p q
    hcard (extensionByZeroIsoDirectImagePlusOfIsProper Λ f j K).hom
  have h₂ := frobeniusRestrictionDirectImageIso_hom_frobenius Λ (compactificationOverHom f j) kbar
    p q hcard K
  exact comp_comp_eq_comp_comp_of_squares _ _ _ _ _ _ _ h₁.symm
    (comp_inv_eq_inv_comp_of_hom_comm _ _ _ _ h₂)

end Stacks.EtaleCohomology

end
