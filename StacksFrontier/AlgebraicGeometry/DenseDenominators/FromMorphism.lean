module

public import StacksFrontier.AlgebraicGeometry.DenseDenominators.Sections
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.FiniteFlat
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.SpecTarget

/-!
# The algebra of sections of a finite locally free surjective morphism

Let `Ω` be an affine open subset of a scheme `Y` and let `π : Z ⟶ Ω` be a finite locally free
surjective morphism. Then the global sections of `Z`, as an algebra over the sections of `Y`
over `Ω`, are the algebraic input `Stacks.DenseDenominators.SectionsData` of the construction of
local sections over a dense affine open subset.

## Main results

* `Stacks.DenseDenominators.nonempty_sectionsData` produces the algebraic input from the
  morphism.

## Implementation notes

The algebra is the ring map `q.appLE Ω ⊤ _` of the composite `q : Z ⟶ Y` of `π` with the
inclusion of `Ω`, and the comparison morphism is the inverse of the canonical isomorphism of
`Z` with the spectrum of its global sections; `Z` is affine because `π` is an affine morphism
over an affine base. Its compatibility over the base is
`AlgebraicGeometry.IsAffineOpen.SpecMap_appLE_fromSpec`.

The three module hypotheses come from the module-theoretic description of finite local freeness
over an affine base, `Stacks.Morphisms.sheafOfModules_isFiniteLocallyFree_iff_module`, which is
stated for a target that is literally the spectrum of a ring; so it is applied to `π` composed
with `hΩ.isoSpec`. The algebra structure it produces is the one through
`AlgebraicGeometry.Scheme.ΓSpecIso`, and
`Stacks.DenseDenominators.ΓSpecIso_inv_comp_appTop_isoSpec_hom` identifies it with `q.appLE Ω ⊤ _`
on the nose, so nothing has to be transported along an isomorphism of the base ring.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.DenseDenominators

/-- The ring map of a morphism to an open subscheme, read on the sections over that open subset
of the ambient scheme, is the map on global sections precomposed with the comparison of the two
descriptions of those sections. -/
theorem appLE_eq_topIso_inv_appTop {Y : Scheme.{u}} {Ω : Y.Opens} {Z : Scheme.{u}}
    (π : Z ⟶ Ω.toScheme) (i : (⊤ : Z.Opens) ≤ (π ≫ Ω.ι) ⁻¹ᵁ Ω) :
    (π ≫ Ω.ι).appLE Ω ⊤ i = Ω.topIso.inv ≫ π.appTop := by
  have e₁ : (⊤ : Ω.toScheme.Opens) ≤ Ω.ι ⁻¹ᵁ Ω := by simp
  have e₂ : (⊤ : Z.Opens) ≤ π ⁻¹ᵁ (⊤ : Ω.toScheme.Opens) := by simp
  have h₁ : Ω.topIso.inv = Ω.ι.appLE Ω (⊤ : Ω.toScheme.Opens) e₁ := by
    rw [Scheme.Opens.topIso_inv, Scheme.Opens.ι_appLE]
    exact congrArg Y.presheaf.map (Quiver.Hom.unop_inj (Subsingleton.elim _ _))
  have h₂ : π.appTop = π.appLE (⊤ : Ω.toScheme.Opens) (⊤ : Z.Opens) e₂ :=
    Scheme.Hom.app_eq_appLE π
  rw [h₁, h₂, Scheme.Hom.appLE_comp_appLE]

/-- The algebra structure that the module-theoretic description of finite local freeness over
the spectrum of the sections on an affine open subset produces is the one given by the ring map
of the composite with the inclusion of that open subset. -/
theorem ΓSpecIso_inv_comp_appTop_isoSpec_hom {Y : Scheme.{u}} {Ω : Y.Opens}
    (hΩ : IsAffineOpen Ω) {Z : Scheme.{u}} (π : Z ⟶ Ω.toScheme)
    (i : (⊤ : Z.Opens) ≤ (π ≫ Ω.ι) ⁻¹ᵁ Ω) :
    (Scheme.ΓSpecIso Γ(Y, Ω)).inv ≫ (π ≫ hΩ.isoSpec.hom).appTop
      = (π ≫ Ω.ι).appLE Ω ⊤ i := by
  rw [Scheme.Hom.comp_appTop, IsAffineOpen.isoSpec_hom_appTop, Category.assoc,
    Iso.inv_hom_id_assoc, appLE_eq_topIso_inv_appTop]

/-- **A finite locally free surjective morphism over an affine open subset is an algebra of
sections.** The global sections of the source, as an algebra over the sections of the base over
the affine open subset, are module-finite, flat and of finite presentation with surjective
spectrum, and the source is the spectrum of that algebra over the base. -/
theorem nonempty_sectionsData {Y : Scheme.{u}} {Ω : Y.Opens} (hΩ : IsAffineOpen Ω)
    {Z : Scheme.{u}} (π : Z ⟶ Ω.toScheme)
    (hflf : Stacks.Morphisms.IsFiniteLocallyFree π) (hsurj : Surjective π) :
    Nonempty (SectionsData hΩ π) := by
  have i : (⊤ : Z.Opens) ≤ (π ≫ Ω.ι) ⁻¹ᵁ Ω := by simp
  have hΩaff : IsAffine Ω.toScheme := hΩ
  have hafh : IsAffineHom π := hflf.toIsAffineHom
  have hZ : IsAffine Z := isAffine_of_isAffineHom π
  have hg : Stacks.Morphisms.IsFiniteLocallyFree (π ≫ hΩ.isoSpec.hom) :=
    MorphismProperty.RespectsIso.postcomp _ hΩ.isoSpec.hom π hflf
  have hgafh : IsAffineHom (π ≫ hΩ.isoSpec.hom) := hg.toIsAffineHom
  let inst : Algebra ↑Γ(Y, Ω) ↑Γ(Z, ⊤) :=
    ((Scheme.ΓSpecIso Γ(Y, Ω)).inv ≫ (π ≫ hΩ.isoSpec.hom).appTop).hom.toAlgebra
  have hmod : Module.IsFiniteLocallyFree ↑Γ(Y, Ω) ↑Γ(Z, ⊤) :=
    (Stacks.Morphisms.sheafOfModules_isFiniteLocallyFree_iff_module
        (π ≫ hΩ.isoSpec.hom)).mp
      ((Stacks.Morphisms.isFiniteLocallyFree_iff (π ≫ hΩ.isoSpec.hom)).mp hg).2
  obtain ⟨hfp, hfl⟩ := (Module.isFiniteLocallyFree_iff _ _).mp hmod
  have := hfp
  have := hfl
  have hfin : Module.Finite ↑Γ(Y, Ω) ↑Γ(Z, ⊤) := inferInstance
  have halgc : CommRingCat.ofHom (algebraMap ↑Γ(Y, Ω) ↑Γ(Z, ⊤)) = (π ≫ Ω.ι).appLE Ω ⊤ i :=
    ΓSpecIso_inv_comp_appTop_isoSpec_hom hΩ π i
  have halg : algebraMap ↑Γ(Y, Ω) ↑Γ(Z, ⊤) = ((π ≫ Ω.ι).appLE Ω ⊤ i).hom :=
    congrArg CommRingCat.Hom.hom halgc
  have hs := IsAffineOpen.SpecMap_appLE_fromSpec (π ≫ Ω.ι) hΩ (isAffineOpen_top Z) i
  rw [IsAffineOpen.fromSpec_top] at hs
  have hcomp : Spec.map ((π ≫ Ω.ι).appLE Ω ⊤ i) ≫ hΩ.isoSpec.inv = Z.isoSpec.inv ≫ π := by
    rw [← cancel_mono Ω.ι]
    simpa only [Category.assoc, IsAffineOpen.isoSpec_inv_ι] using hs
  have hsp : Spec.map ((π ≫ Ω.ι).appLE Ω ⊤ i) = Z.isoSpec.inv ≫ π ≫ hΩ.isoSpec.hom := by
    rw [← Category.assoc, ← hcomp]
    simp
  have : Surjective (Spec.map ((π ≫ Ω.ι).appLE Ω ⊤ i)) := by
    rw [hsp]; infer_instance
  exact ⟨{ S := ↑Γ(Z, ⊤)
           algebra := inst
           specSurjective := by
             rw [halg]
             exact (Spec.map _).surjective
           σ := Z.isoSpec.inv
           σ_comp := by rw [halgc, hs] }⟩

end Stacks.DenseDenominators

end
