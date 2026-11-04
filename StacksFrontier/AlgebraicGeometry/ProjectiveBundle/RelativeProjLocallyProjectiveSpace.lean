module

public import StacksFrontier.AlgebraicGeometry.Morphisms.Proper.Projective
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundle.LocallyFreeLocallyProjectiveSpace
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundle.TautologicalDatumExists

/-!
# The projective bundle of a module of rank `n + 1` over a local base is `ℙⁿ`

Let `F` be a module on a scheme `X`, finite locally free of constant rank `n + 1`, and
`π : 𝐏(F) ⟶ X` the projection of its projective bundle `Stacks.RelativeProj.projectiveBundle`.
Then `π` is Zariski-locally on `X` the projective space `ℙⁿ`: this is
`Stacks.ProjectiveBundle.isLocallyProjectiveSpace_toBase` for the `SheafGradedAlgebra`
presentation of the bundle, transported along the comparison
`Stacks.RelativeProj.bundlePresentationIso` of the two presentations over the base.

If moreover `X` has a point whose only open neighbourhood is `X` itself — for instance the
spectrum of a field, or of a local ring at its closed point — then a morphism which is
Zariski-locally `ℙⁿ` is globally `ℙⁿ_X` over `X`.  In particular the fibre of `π` over a point
`x` of `X`, the projective bundle of `F ⊗ κ(x)` over `Spec κ(x)`, is `ℙⁿ_{κ(x)}`.

## Main results

* `Stacks.ProjectiveBundle.IsLocallyProjectiveSpace.exists_iso_of_forall_eq_top`: over a base
  with a point whose only open neighbourhood is everything, Zariski-locally `ℙⁿ` is `ℙⁿ`.
* `Stacks.RelativeProj.isLocallyProjectiveSpace_projectiveBundleToBase`: the projection of the
  projective bundle of a module of rank `n + 1` is Zariski-locally `ℙⁿ`.
* `Stacks.RelativeProj.exists_iso_projectiveSpaceOver_of_forall_eq_top`: over such a local
  base, the projective bundle of a module of rank `n + 1` is `ℙⁿ`.

## References

* [Stacks Project, Tag 01OE](https://stacks.math.columbia.edu/tag/01OE)
* [Stacks Project, Tag 01OF](https://stacks.math.columbia.edu/tag/01OF)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.ProjectiveBundle

/-- **Over a base with a point whose only open neighbourhood is everything, a morphism which is
Zariski-locally `ℙⁿ` is `ℙⁿ`.**  The neighbourhood of that point over which the morphism is
`ℙⁿ` is the whole base; the inclusion of the whole base, and of its preimage, are isomorphisms,
and `ℙⁿ` over the whole base is the base change of `ℙⁿ_P` along that inclusion. -/
theorem IsLocallyProjectiveSpace.exists_iso_of_forall_eq_top {H P : Scheme.{u}} {f : H ⟶ P}
    {n : ℕ} (h : IsLocallyProjectiveSpace f n) (y : P) (hy : ∀ W : P.Opens, y ∈ W → W = ⊤) :
    ∃ e : H ≅ projectiveSpaceOver n P, e.hom ≫ (projectiveSpaceOver n P ↘ P) = f := by
  obtain ⟨W, hyW, e, he⟩ := h y
  obtain rfl := hy W hyW
  have : IsIso (⊤ : P.Opens).ι := inferInstanceAs (IsIso P.topIso.hom)
  have : IsIso (f ⁻¹ᵁ (⊤ : P.Opens)).ι :=
    (isPullback_morphismRestrict f (⊤ : P.Opens)).isIso_snd_of_isIso
  let ι₁ : (f ⁻¹ᵁ (⊤ : P.Opens)).toScheme ≅ H := asIso (f ⁻¹ᵁ (⊤ : P.Opens)).ι
  let bc := projectiveSpaceOverBaseChangeIso n (⊤ : P.Opens).ι
  refine ⟨ι₁.symm ≪≫ e ≪≫ bc.symm ≪≫
    asIso (pullback.fst (projectiveSpaceOver n P ↘ P) (⊤ : P.Opens).ι), ?_⟩
  have hbc : bc.inv ≫ pullback.snd (projectiveSpaceOver n P ↘ P) (⊤ : P.Opens).ι =
      (projectiveSpaceOver n (⊤ : P.Opens).toScheme ↘ (⊤ : P.Opens).toScheme) := by
    rw [Iso.inv_comp_eq]
    exact (projectiveSpaceOverBaseChangeIso_hom_over n (⊤ : P.Opens).ι).symm
  simp only [Iso.trans_hom, Iso.symm_hom, asIso_hom, Category.assoc, pullback.condition]
  rw [reassoc_of% hbc, reassoc_of% he, morphismRestrict_ι]
  simp [ι₁]

end Stacks.ProjectiveBundle

namespace Stacks.RelativeProj

variable {X : Scheme.{u}} (F : X.Modules) [F.IsQuasicoherent]

/-- **The projection of the projective bundle of a module of rank `n + 1` is Zariski-locally
`ℙⁿ`** (Stacks 01OE, 01OF): `Stacks.ProjectiveBundle.isLocallyProjectiveSpace_toBase` for the
`SheafGradedAlgebra` presentation, transported along
`Stacks.RelativeProj.bundlePresentationIso`. -/
theorem isLocallyProjectiveSpace_projectiveBundleToBase (n : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} F (n + 1)] :
    Stacks.ProjectiveBundle.IsLocallyProjectiveSpace (projectiveBundleToBase X F) n := by
  rw [← bundlePresentationIso_inv_comp_toBase F]
  exact (Stacks.ProjectiveBundle.isLocallyProjectiveSpace_toBase F
    (Stacks.SymGraded.isQuasicoherentPieces_of_isQuasicoherent F) n).of_iso
      (bundlePresentationIso F).symm

/-- **Over a base with a point whose only open neighbourhood is everything, the projective bundle
of a module of rank `n + 1` is `ℙⁿ`** over the base: for instance the fibre of a projective
bundle over the spectrum of the residue field at a point. -/
theorem exists_iso_projectiveSpaceOver_of_forall_eq_top (n : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} F (n + 1)]
    (y : X) (hy : ∀ W : X.Opens, y ∈ W → W = ⊤) :
    ∃ e : projectiveBundle X F ≅ projectiveSpaceOver n X,
      e.hom ≫ (projectiveSpaceOver n X ↘ X) = projectiveBundleToBase X F :=
  (isLocallyProjectiveSpace_projectiveBundleToBase F n).exists_iso_of_forall_eq_top y hy

end Stacks.RelativeProj

end
