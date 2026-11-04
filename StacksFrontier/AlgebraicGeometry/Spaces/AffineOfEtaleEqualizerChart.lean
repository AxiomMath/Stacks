module

public import Mathlib.AlgebraicGeometry.EffectiveEpi
public import Mathlib.AlgebraicGeometry.Pullbacks
public import StacksFrontier.AlgebraicGeometry.Descent.QuasiAffineEtaleDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.Affine
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleFieldAtlas

/-!
# An algebraic space presented by an étale relation of affine schemes over its invariant ring

Let `F` be an algebraic space over a scheme `S`, let `f : U ⟶ F` be a surjective étale chart
with `U` affine, and let `t, s : R ⟶ U` be its kernel pair, with `R` affine.  Write
`A ⊆ Γ(U, 𝒪_U)` for the ring of functions on `U` equalized by `t` and `s`.  If `Spec Γ(U) → Spec A`
is étale and surjective and the square `Γ(R) ← Γ(U) ⇇ A` is a pushout of rings, then `F` is the
affine scheme `Spec A`.

The structure morphism `Spec A ⟶ S` is obtained by fpqc descent: `U ⟶ Spec A` is a flat
surjection of affine schemes, hence an effective epimorphism of schemes (Stacks 023Q), and the
structure morphism of `U` is equalized by its kernel pair, which is `R` because the square of
rings is a pushout.  The identification `F ≅ Spec A` is then the statement that two surjective
flat charts of finite presentation with the same kernel pair present the same sheaf,
`AlgebraicGeometry.Space.exists_iso_yoneda_of_isPullback`.

## Main results

* `AlgebraicGeometry.Space.isAffineSpace_of_isPushout_eqLocus`

## References

* [Stacks Project, Tag 023Q](https://stacks.math.columbia.edu/tag/023Q)
* [Stacks Project, Tag 0262](https://stacks.math.columbia.edu/tag/0262)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **An algebraic space presented by an étale relation of affine schemes over its invariant
ring is that affine scheme.**  Let `f : U ⟶ F` be a surjective étale chart of an algebraic space,
with kernel pair `t, s : R ⟶ U`, `U` and `R` affine, and let `A ⊆ Γ(U)` be the subring equalized
by `t` and `s`.  If `Spec Γ(U) → Spec A` is étale and surjective and `Γ(R)` is the pushout
`Γ(U) ⊗_A Γ(U)` along `t` and `s`, then `F` is affine. -/
theorem isAffineSpace_of_isPushout_eqLocus {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : IsAlgebraicSpace B S hS F) {U R : BigFppfOver B S hS}
    (hU : IsAffine ((BigFppfOver.toScheme B S hS).obj U))
    (hR : IsAffine ((BigFppfOver.toScheme B S hS).obj R))
    (f : yoneda.obj U ⟶ F) (t s : R ⟶ U)
    (hpb : IsPullback (yoneda.map t) (yoneda.map s) f f)
    (hsurj : (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf f)
    (hetale : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf f)
    (hEt : Etale (Spec.map (CommRingCat.ofHom
      ((((BigFppfOver.toScheme B S hS).map t).appTop.hom.eqLocus
        ((BigFppfOver.toScheme B S hS).map s).appTop.hom).subtype))))
    (hSurj : Surjective (Spec.map (CommRingCat.ofHom
      ((((BigFppfOver.toScheme B S hS).map t).appTop.hom.eqLocus
        ((BigFppfOver.toScheme B S hS).map s).appTop.hom).subtype))))
    (hpo : IsPushout
      (CommRingCat.ofHom ((((BigFppfOver.toScheme B S hS).map t).appTop.hom.eqLocus
        ((BigFppfOver.toScheme B S hS).map s).appTop.hom).subtype))
      (CommRingCat.ofHom ((((BigFppfOver.toScheme B S hS).map t).appTop.hom.eqLocus
        ((BigFppfOver.toScheme B S hS).map s).appTop.hom).subtype))
      ((BigFppfOver.toScheme B S hS).map t).appTop
      ((BigFppfOver.toScheme B S hS).map s).appTop) :
    IsAffineSpace B S hS F := by
  classical
  set 𝒰 := (BigFppfOver.toScheme B S hS).obj U
  set ℛ := (BigFppfOver.toScheme B S hS).obj R
  set τ := (BigFppfOver.toScheme B S hS).map t
  set σ := (BigFppfOver.toScheme B S hS).map s
  set A := τ.appTop.hom.eqLocus σ.appTop.hom
  set ι : CommRingCat.of A ⟶ Γ(𝒰, ⊤) := CommRingCat.ofHom A.subtype
  set π₀ : 𝒰 ⟶ Spec (CommRingCat.of A) := 𝒰.isoSpec.hom ≫ Spec.map ι
  have : IsAffine 𝒰 := hU
  have : IsAffine ℛ := hR
  have : Etale (Spec.map ι) := hEt
  have : Surjective (Spec.map ι) := hSurj
  have hpbS : IsPullback τ σ π₀ π₀ :=
    IsPullback.of_iso (isPullback_SpecMap_of_isPushout _ _ _ _ hpo) ℛ.isoSpec.symm
      𝒰.isoSpec.symm 𝒰.isoSpec.symm (Iso.refl _) (Scheme.isoSpec_inv_naturality τ)
      (Scheme.isoSpec_inv_naturality σ) (by simp [π₀]) (by simp [π₀])
  have : IsRegularEpi π₀ := isRegularEpi_of_flat_of_surjective_of_isAffine π₀
  let e : 𝒰 ⟶ S := B.inclusion.map U.hom
  have hw : ∀ r : R ⟶ U, (BigFppfOver.toScheme B S hS).map r ≫ e = B.inclusion.map R.hom := by
    intro r
    simp only [e, BigFppfOver.toScheme, Functor.comp_map, ← Functor.map_comp]
    exact congrArg B.inclusion.map (Over.w r)
  have he : ∀ {Z : Scheme.{u}} (g₁ g₂ : Z ⟶ 𝒰), g₁ ≫ π₀ = g₂ ≫ π₀ → g₁ ≫ e = g₂ ≫ e := by
    intro Z g₁ g₂ h
    calc g₁ ≫ e = hpbS.lift g₁ g₂ h ≫ τ ≫ e := by rw [← Category.assoc, hpbS.lift_fst]
      _ = hpbS.lift g₁ g₂ h ≫ σ ≫ e := congrArg _ ((hw t).trans (hw s).symm)
      _ = g₂ ≫ e := by rw [← Category.assoc, hpbS.lift_snd]
  let g : Spec (CommRingCat.of A) ⟶ S := EffectiveEpi.desc π₀ e he
  have hAmem : B.Contains (Spec (CommRingCat.of A)) :=
    Scheme.size_Spec_lt_of_injective_sections B.aleph0_lt_cutoff B.cutoff_isStrongPrelimit
      (p := ι) Subtype.val_injective U.left.property
  let U' : BigFppfOver B S hS := Over.mk (⟨g⟩ : B.obj hAmem ⟶ B.obj hS)
  let π : (Over.post B.inclusion).obj U ⟶ (Over.post B.inclusion).obj U' :=
    Over.homMk π₀ (EffectiveEpi.fac π₀ e he)
  have hπ : IsPullback ((Over.post B.inclusion).map t) ((Over.post B.inclusion).map s) π π :=
    IsPullback.of_map (Over.forget _) (by ext; exact hpbS.w) hpbS
  obtain ⟨-, eF, -, -⟩ := exists_iso_yoneda_of_isPullback B S hS hF f t s hpb hsurj hetale π
    (inferInstanceAs (Flat π₀)) (inferInstanceAs (LocallyOfFinitePresentation π₀))
    (inferInstanceAs (Surjective π₀)) hπ
  exact ⟨U', inferInstanceAs (IsAffine (Spec (CommRingCat.of A))), ⟨eF⟩⟩

end AlgebraicGeometry.Space

end
