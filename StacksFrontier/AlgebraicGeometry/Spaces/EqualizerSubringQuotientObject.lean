module

public import StacksFrontier.AlgebraicGeometry.Descent.Germs.MorphismDescent
public import StacksFrontier.AlgebraicGeometry.Descent.QuasiAffineEtaleDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.Representability

/-!
# The spectrum of an étale, faithfully flat subring as a quotient object of the site

Let `t, s : R ⟶ U` be morphisms of the big fppf site of `S` between affine objects, and let
`A ⊆ Γ(U, ⊤)` be a subring such that `A → Γ(U, ⊤)` is étale and faithfully flat and
`Γ(R, ⊤) = Γ(U, ⊤) ⊗_A Γ(U, ⊤)` via `t` and `s`. Then `Spec A` is an affine object `U'` of the
site, and the canonical morphism `U ⟶ Spec A` is flat, locally of finite presentation and
surjective. It lies over `S`, and `t, s` is its kernel pair.

## Main results

* `exists_quotientObject_of_isPushout_subring`: the statement above.

## References

* [Stacks Project, Tag 000R](https://stacks.math.columbia.edu/tag/000R)
* [Stacks Project, Tag 023Q](https://stacks.math.columbia.edu/tag/023Q)
* [Stacks Project, Tag 05ZR](https://stacks.math.columbia.edu/tag/05ZR)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The spectrum of an étale, faithfully flat subring of sections is a quotient object.** Let
`t, s : R ⟶ U` be morphisms of the big fppf site of `S` between affine objects. Let
`A ⊆ Γ(U, ⊤)` be a subring whose inclusion is étale and faithfully flat, and suppose `Γ(R, ⊤)` is
the pushout of the inclusion along itself, with structure maps the maps on global sections of
`t` and `s`. Then there is an affine object `U'` of the site (namely `Spec A`) and a morphism of
schemes `π : U ⟶ U'` over `S` which is flat, locally of finite presentation and surjective, and
whose kernel pair is `t, s`. -/
theorem exists_quotientObject_of_isPushout_subring {U R : BigFppfOver B S hS} (t s : R ⟶ U)
    [IsAffine ((BigFppfOver.toScheme B S hS).obj U)]
    [IsAffine ((BigFppfOver.toScheme B S hS).obj R)]
    (A : Subring Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)) (hAe : A.subtype.Etale)
    (hAff : A.subtype.FaithfullyFlat)
    (hpo : IsPushout (CommRingCat.ofHom A.subtype) (CommRingCat.ofHom A.subtype)
      ((BigFppfOver.toScheme B S hS).map t).appTop
      ((BigFppfOver.toScheme B S hS).map s).appTop) :
    ∃ (U' : BigFppfOver B S hS)
      (π : (Over.post B.inclusion).obj U ⟶ (Over.post B.inclusion).obj U'),
      IsAffine ((BigFppfOver.toScheme B S hS).obj U') ∧ Flat π.left ∧
        LocallyOfFinitePresentation π.left ∧ Surjective π.left ∧
        IsPullback ((Over.post B.inclusion).map t) ((Over.post B.inclusion).map s) π π := by
  obtain ⟨q₀, hq₀⟩ : ∃ q₀ : (BigFppfOver.toScheme B S hS).obj U ⟶ Spec (CommRingCat.of A),
      q₀ = ((BigFppfOver.toScheme B S hS).obj U).isoSpec.hom ≫
        Spec.map (CommRingCat.ofHom A.subtype) := ⟨_, rfl⟩
  have hSflat : Flat (Spec.map (CommRingCat.ofHom A.subtype)) := by
    exact (HasRingHomProperty.Spec_iff (P := @Flat)).mpr hAff.flat
  have hSlfp : LocallyOfFinitePresentation (Spec.map (CommRingCat.ofHom A.subtype)) := by
    exact (HasRingHomProperty.Spec_iff (P := @LocallyOfFinitePresentation)).mpr
      hAe.finitePresentation
  have hSsurj : Surjective (Spec.map (CommRingCat.ofHom A.subtype)) := by
    constructor
    let := (CommRingCat.ofHom A.subtype).hom.toAlgebra
    have : Module.FaithfullyFlat (CommRingCat.of A)
        Γ((BigFppfOver.toScheme B S hS).obj U, ⊤) := hAff
    exact PrimeSpectrum.comap_surjective_of_faithfullyFlat
  have hqflat : Flat q₀ := by subst hq₀; infer_instance
  have hqlfp : LocallyOfFinitePresentation q₀ := by subst hq₀; infer_instance
  have hqsurj : Surjective q₀ := by subst hq₀; infer_instance
  have hSpec : IsPullback (Spec.map ((BigFppfOver.toScheme B S hS).map t).appTop)
      (Spec.map ((BigFppfOver.toScheme B S hS).map s).appTop)
      (Spec.map (CommRingCat.ofHom A.subtype)) (Spec.map (CommRingCat.ofHom A.subtype)) :=
    (hpo.op.map Scheme.Spec).flip
  have hsch : IsPullback ((BigFppfOver.toScheme B S hS).map t)
      ((BigFppfOver.toScheme B S hS).map s) q₀ q₀ := by
    refine hSpec.of_iso ((BigFppfOver.toScheme B S hS).obj R).isoSpec.symm
      ((BigFppfOver.toScheme B S hS).obj U).isoSpec.symm
      ((BigFppfOver.toScheme B S hS).obj U).isoSpec.symm (Iso.refl _) ?_ ?_ ?_ ?_
    · exact Scheme.isoSpec_inv_naturality _
    · exact Scheme.isoSpec_inv_naturality _
    all_goals simp [hq₀]
  have hts : (BigFppfOver.toScheme B S hS).map t ≫ B.inclusion.map U.hom =
      (BigFppfOver.toScheme B S hS).map s ≫ B.inclusion.map U.hom := by
    have ht := congrArg B.inclusion.map (Over.w t)
    have hs := congrArg B.inclusion.map (Over.w s)
    rw [Functor.map_comp] at ht hs
    exact ht.trans hs.symm
  have : IsRegularEpi q₀ := (isRegularEpi_iff_effectiveEpi q₀).mpr inferInstance
  obtain ⟨ψ, hψ⟩ := IsRegularEpi.exists_of_isKernelPair q₀ hsch (B.inclusion.map U.hom) hts
  have hmem : B.Contains (Spec (CommRingCat.of A)) :=
    Scheme.size_Spec_lt_of_injective_sections B.aleph0_lt_cutoff B.cutoff_isStrongPrelimit
      (p := CommRingCat.ofHom A.subtype) Subtype.val_injective U.left.property
  exact ⟨BigFppfOver.mk B S hS hmem ψ, Over.homMk q₀ hψ,
    inferInstanceAs (IsAffine (Spec (CommRingCat.of A))), hqflat, hqlfp, hqsurj,
    IsPullback.of_map_of_faithful (Over.forget S) hsch⟩

end AlgebraicGeometry.Space

end
