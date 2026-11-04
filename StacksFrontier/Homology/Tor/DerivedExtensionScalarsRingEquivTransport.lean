module

public import StacksFrontier.Homology.Tor.DerivedExtensionScalarsSelfIso
public import StacksFrontier.Homology.Tor.DerivedExtensionScalarsRingIso
public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryHomology

/-!
# Cohomology of a derived base change, transported along ring isomorphisms

Let `e : A ≃+* R` and `e₀ : A₀ ≃+* R₀` be isomorphisms of commutative rings and `π : A →+* A₀`,
`g : R →+* R₀` maps with `g ∘ e = e₀ ∘ π`. For `N ∈ D(R)` the derived base change
`(N|_A) ⊗^𝐋_A A₀` of the restriction of `N` along `e` is, up to restriction along `e₀`, the derived
base change `N ⊗^𝐋_R R₀`; in particular the two have the same vanishing cohomology.

## Main results

* `StacksDraft.isZero_homology_of_isZero_homology_restrictScalars`.
* `StacksDraft.isZero_homology_extendScalars_restrictScalars_ringEquiv`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [local instance] HasDerivedCategory.standard

universe u

namespace StacksDraft

/-- **Restriction of scalars reflects vanishing cohomology** in the derived category. -/
theorem isZero_homology_of_isZero_homology_restrictScalars {R S : Type u} [CommRing R]
    [CommRing S] (f : R →+* S) (N : DerivedCategory (ModuleCat.{u} S)) (i : ℤ)
    (h : IsZero ((DerivedCategory.homologyFunctor _ i).obj
      ((ModuleCat.restrictScalars f).mapDerivedCategory.obj N))) :
    IsZero ((DerivedCategory.homologyFunctor _ i).obj N) := by
  have h' := IsZero.of_iso h
    (((ModuleCat.restrictScalars f).mapDerivedCategoryHomologyIso i).app N).symm
  rw [IsZero.iff_id_eq_zero] at h' ⊢
  exact (ModuleCat.restrictScalars f).map_injective
    (((ModuleCat.restrictScalars f).map_id _).trans
      (h'.trans ((ModuleCat.restrictScalars f).map_zero _ _).symm))

/-- **Restriction of scalars preserves vanishing cohomology** in the derived category. -/
theorem isZero_homology_restrictScalars {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
    (N : DerivedCategory (ModuleCat.{u} S)) (i : ℤ)
    (h : IsZero ((DerivedCategory.homologyFunctor _ i).obj N)) :
    IsZero ((DerivedCategory.homologyFunctor _ i).obj
      ((ModuleCat.restrictScalars f).mapDerivedCategory.obj N)) :=
  IsZero.of_iso (Functor.map_isZero (ModuleCat.restrictScalars f) h)
    (((ModuleCat.restrictScalars f).mapDerivedCategoryHomologyIso i).app N)

/-- **Vanishing cohomology of a derived base change, along ring isomorphisms.** For
`g ∘ e = e₀ ∘ π` with `e`, `e₀` isomorphisms, if `Hⁱ(N ⊗^𝐋_R R₀) = 0` then
`Hⁱ((N|_A) ⊗^𝐋_A A₀) = 0`. -/
theorem isZero_homology_extendScalars_restrictScalars_ringEquiv {A A₀ R R₀ : Type u}
    [CommRing A] [CommRing A₀] [CommRing R] [CommRing R₀] (e : A ≃+* R) (e₀ : A₀ ≃+* R₀)
    (π : A →+* A₀) (g : R →+* R₀) (hg : g.comp e.toRingHom = e₀.toRingHom.comp π)
    (N : DerivedCategory (ModuleCat.{u} R)) (i : ℤ)
    (hN : IsZero ((DerivedCategory.homologyFunctor _ i).obj
      ((CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u} g).functor.obj
        N))) :
    IsZero ((DerivedCategory.homologyFunctor _ i).obj
      ((CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u} π).functor.obj
        ((ModuleCat.restrictScalars e.toRingHom).mapDerivedCategory.obj N))) := by
  have hring : π.comp e.symm.toRingHom = e₀.symm.toRingHom.comp g := by
    ext x
    have := congrArg (fun φ => e₀.symm (φ (e.symm x))) hg
    simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
      RingEquiv.apply_symm_apply, RingEquiv.symm_apply_apply] at this
    simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom]
    exact this.symm
  let P :=
    (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u} g).functor.obj N
  have hL : IsZero ((DerivedCategory.homologyFunctor _ i).obj
      ((CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
        e₀.symm.toRingHom).functor.obj P)) :=
    isZero_homology_of_isZero_homology_restrictScalars e₀.symm.toRingHom _ i
      (IsZero.of_iso hN ((DerivedCategory.homologyFunctor _ i).mapIso
        ((CochainComplex.DerivedExtensionScalars.totalDerivedExtendRestrictScalarsSelfIso.{u, u}
          e₀.symm).app P)))
  exact IsZero.of_iso hL ((DerivedCategory.homologyFunctor _ i).mapIso
    ((DerivedRingIso.derivedExtensionScalarsRestrictIso e.symm.toRingHom e.toRingHom
        (fun x => e.apply_symm_apply x) (fun y => e.symm_apply_apply y) π).app N ≪≫
      eqToIso (congrArg
        (fun φ => (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
          φ).functor.obj N) hring) ≪≫
      ((CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalarsComp g
        e₀.symm.toRingHom).app N).symm))

end StacksDraft

end
