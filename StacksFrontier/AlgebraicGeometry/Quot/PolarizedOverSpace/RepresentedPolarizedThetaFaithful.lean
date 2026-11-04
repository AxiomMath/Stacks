module

public import StacksFrontier.AlgebraicGeometry.Quot.PolarizedOverSpace.RepresentedPolarizedTheta
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleCounit

/-!
# The comparison `Θ : RepresentedPolarized ⥤ Polarized` is faithful

A morphism of `AlgebraicGeometry.PolarizedOverSpace.RepresentedPolarized` is determined by its
image under `Θ = AlgebraicGeometry.PolarizedOverSpace.toPolarized`: its square of schemes is the
square of the image, and its comparison of modules is recovered from the comparison of
polarizations because restriction from the small étale site to the Zariski site is faithful on
quasi-coherent modules (its counit is an isomorphism there,
`AlgebraicGeometry.SmallEtale.isIso_counit`).

## Main results

* `CategoryTheory.Adjunction.map_injective_of_isIso_counit_app`: a right adjoint is injective on
  morphisms out of an object at which the counit is an isomorphism.
* `AlgebraicGeometry.PolarizedOverSpace.toPolarized_faithful`: `Θ` is faithful.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace CategoryTheory.Adjunction

/-- **A right adjoint is injective on morphisms out of an object at which the counit is an
isomorphism**: `χ = ε⁻¹ ≫ L(R χ) ≫ ε`. -/
theorem map_injective_of_isIso_counit_app {C D : Type*} [Category C] [Category D] {L : C ⥤ D}
    {R : D ⥤ C} (adj : L ⊣ R) {M N : D} (hM : IsIso (adj.counit.app M)) {φ ψ : M ⟶ N}
    (h : R.map φ = R.map ψ) : φ = ψ := by
  have key : ∀ χ : M ⟶ N, χ = inv (adj.counit.app M) ≫ L.map (R.map χ) ≫ adj.counit.app N :=
    fun χ => by simp
  rw [key φ, key ψ, h]

end CategoryTheory.Adjunction

namespace AlgebraicGeometry.PolarizedOverSpace

attribute [local irreducible] Space.modulePullback Space.modulePullbackCompIso
        Scheme.Modules.pullback
  Space.representedSmallEtaleModuleEquivalence SmallEtale.restrictModule

variable {B : BigFppfSite.{u}}

/-- **The polarization functor `R` of a quasi-coherent module is faithful**: two morphisms out of
a quasi-coherent module on the small étale site of `yoneda Z` with the same restriction to the
Zariski site of `Z` agree. -/
theorem zariskiRestriction_map_injective {A : Arrow (Site B)}
    {M N : SheafOfModules.{u} (Space.representedStructureRingSheaf B integerBase (hZ B) A.left)}
        (hM : SheafOfModules.IsQuasicoherentOnSite M)
    {a b : M ⟶ N}
    (h : (zariskiRestriction A).map ((etaleInverse A).map a) =
      (zariskiRestriction A).map ((etaleInverse A).map b)) : a = b :=
  have hQ := Space.isQuasicoherentOnSite_representedSmallEtaleInverse B integerBase (hZ B) A.left
    M hM
  (etaleInverse A).map_injective
    (Adjunction.map_injective_of_isIso_counit_app
      (_root_.AlgebraicGeometry.SmallEtale.associatedModuleAdjunction (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B integerBase (hZ B)).obj A.left) A.left.left.property)
      (_root_.AlgebraicGeometry.SmallEtale.isIso_counit _ _ _ _ hQ
        (_root_.AlgebraicGeometry.SmallEtale.isQuasicoherent_restrictModule _ _ _ _ hQ))
      h)

variable (B) in
/-- **`Θ` is faithful.** -/
instance toPolarized_faithful : (toPolarized B).Faithful where
  map_injective {X Y} {φ ψ} h := by
    obtain ⟨⟨⟨b₁, f₁⟩⟩, p₁⟩ := φ
    obtain ⟨⟨⟨b₂, f₂⟩⟩, p₂⟩ := ψ
    have h1 : sch B b₁.left = sch B b₂.left := congrArg PolarizedFamily.Hom.totalMap h
    have h2 : (BigFppfOver.forget B integerBase (hZ B)).map b₁.right =
        (BigFppfOver.forget B integerBase (hZ B)).map b₂.right :=
      congrArg PolarizedFamily.Hom.baseMap h
    have hb : b₁ = b₂ := Arrow.hom_ext _ _
      ((BigFppfOver.toScheme B integerBase (hZ B)).map_injective h1)
      ((BigFppfOver.forget B integerBase (hZ B)).map_injective h2)
    subst hb
    change PolarizedFamily.Hom.mk _ _ _ _ = PolarizedFamily.Hom.mk _ _ _ _ at h
    injection h with _ _ h3
    have h4 := congrArg Iso.hom h3
    rw [toPolarizedLineBundleIso_hom_eq, toPolarizedLineBundleIso_hom_eq, cancel_epi] at h4
    have h5 := zariskiRestriction_map_injective
      (Space.isQuasicoherentOnSite_modulePullback_representedSpaceMap B integerBase (hZ B) b₁.left
        (Space.relativelyRepresentable_yoneda_map B integerBase (hZ B) _) Y.obj.obj.fiber
        Y.obj.property.quasicoherent) h4
    have h6 : f₁ = f₂ := by
      have := p₁.2
      have := p₂.2
      exact (IsIso.inv_eq_inv).mp h5
    subst h6
    rfl

end AlgebraicGeometry.PolarizedOverSpace

end
