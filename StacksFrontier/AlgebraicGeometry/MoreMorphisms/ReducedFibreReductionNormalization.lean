module

public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ReducedFibreReduction
public import StacksFrontier.AlgebraicGeometry.NormalizationBaseChange.UniversalProperty

/-!
# From an abstract presentation of the reduction to the normalization of the scheme itself

The reduction of a scheme `W` is `W.nilradical.subscheme`, and that construction does not
transport along an isomorphism of schemes without a dependent rewrite, so results producing a
reduction state it by its universal characterisation: a closed immersion `ρ` with kernel ideal
sheaf the nilradical.  That is how
`AlgebraicGeometry.exists_finite_extension_dense_open_smooth_reduction_genericFibre` delivers
the dense smooth open of the generic fibre, whereas
`AlgebraicGeometry.Scheme.exists_normalizationScheme_iso_reduction`, which compares the
normalization of `W` with the normalization of its reduction, is stated for
`W.nilradical.subscheme`.

This file closes the gap between the two.  A closed immersion whose kernel is the nilradical is
*the* reduction: the universal property of closed immersions produces a morphism to
`W.nilradical.subscheme` over `W`, and two closed immersions with the same kernel differ by an
isomorphism (`AlgebraicGeometry.IsClosedImmersion.isIso_lift`).  Transporting a dense open
smooth over the base along that isomorphism, applying
`AlgebraicGeometry.exists_dense_open_smooth_normalization` on the reduction and transporting
back along the comparison of normalizations then puts the dense smooth open on the
normalization of `W` itself.

## Main results

* `AlgebraicGeometry.exists_iso_nilradical_subscheme_of_ker_eq_nilradical`: a closed immersion
  whose kernel ideal sheaf is the nilradical is isomorphic, over the target, to the reduction.
* `AlgebraicGeometry.exists_dense_open_smooth_normalization_of_ker_eq_nilradical`: if some
  closed immersion presenting the reduction of `W` carries a dense open smooth over the base,
  then so does the normalization of `W`.

## References

* [Stacks Project, Tag 09IL](https://stacks.math.columbia.edu/tag/09IL)
* [Stacks Project, Tag 035Q](https://stacks.math.columbia.edu/tag/035Q)
-/

public noncomputable section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- **A closed immersion whose kernel ideal sheaf is the nilradical is the reduction.** The
universal property of closed immersions lifts it to the reduction, and that lift is an
isomorphism because the two closed immersions have the same kernel. No reducedness of the
source is assumed; it follows. -/
theorem exists_iso_nilradical_subscheme_of_ker_eq_nilradical {Z W : Scheme.{u}} (ρ : Z ⟶ W)
    [IsClosedImmersion ρ] (hρ : ρ.ker = W.nilradical) :
    ∃ e : Z ≅ W.nilradical.subscheme, e.hom ≫ W.nilradical.subschemeι = ρ := by
  have hker : W.nilradical.subschemeι.ker = ρ.ker := by
    rw [Scheme.IdealSheafData.ker_subschemeι, hρ]
  have _ := IsClosedImmersion.isIso_lift W.nilradical.subschemeι ρ hker
  exact ⟨asIso (IsClosedImmersion.lift W.nilradical.subschemeι ρ hker.le),
    IsClosedImmersion.lift_fac _ _ hker.le⟩

/-- A dense open smooth over the base transports along an isomorphism of the source. -/
private theorem exists_dense_open_smooth_of_iso {Z Z' T : Scheme.{u}} (e : Z ≅ Z') (r : Z' ⟶ T)
    {U : Z.Opens} (hU : Dense (U : Set Z)) (hsm : Smooth (U.ι ≫ e.hom ≫ r)) :
    ∃ V : Z'.Opens, Dense (V : Set Z') ∧ Smooth (V.ι ≫ r) := by
  refine ⟨e.inv ⁻¹ᵁ U, hU.preimage (Scheme.homeoOfIso e.symm).isOpenMap, ?_⟩
  have h : (e.inv ∣_ U) ≫ U.ι ≫ e.hom ≫ r = (e.inv ⁻¹ᵁ U).ι ≫ r := by
    rw [← Category.assoc, morphismRestrict_ι, Category.assoc, Iso.inv_hom_id_assoc]
  rw [← h]
  exact MorphismProperty.comp_mem _ _ _ inferInstance hsm

/-- **A dense smooth open on a presentation of the reduction gives one on the normalization.**
Let `q : W ⟶ Spec k` be locally of finite type over a field, with `W` normalizable, and let
`ρ : Z ⟶ W` be a closed immersion whose kernel ideal sheaf is the nilradical of `W`, that is, a
presentation of the reduction of `W`. If `Z` has a dense open subscheme smooth over `k`, then
the normalization of `W` has one too.

The reduction is identified with `W.nilradical.subscheme` by
`AlgebraicGeometry.exists_iso_nilradical_subscheme_of_ker_eq_nilradical`, which is the form in
which `AlgebraicGeometry.Scheme.exists_normalizationScheme_iso_reduction` compares the
normalization of `W` with the normalization of its reduction. -/
theorem exists_dense_open_smooth_normalization_of_ker_eq_nilradical {k : Type u} [Field k]
    {W : Scheme.{u}} (q : W ⟶ Spec (.of k)) [LocallyOfFiniteType q]
    (hW : ∀ U : W.Opens, IsCompact (U : Set W) → (irreducibleComponents U).Finite)
    {Z : Scheme.{u}} (ρ : Z ⟶ W) [IsClosedImmersion ρ] (hρ : ρ.ker = W.nilradical)
    (U : Z.Opens) (hU : Dense (U : Set Z)) (hsm : Smooth (U.ι ≫ ρ ≫ q)) :
    ∃ V : (W.normalizationScheme hW).Opens, Dense (V : Set (W.normalizationScheme hW)) ∧
      Smooth (V.ι ≫ W.normalization hW ≫ q) := by
  obtain ⟨e, he⟩ := exists_iso_nilradical_subscheme_of_ker_eq_nilradical ρ hρ
  have _ : IsReduced W.nilradical.subscheme := isReduced_nilradical_subscheme W
  have _ : LocallyOfFiniteType (W.nilradical.subschemeι ≫ q) := inferInstance
  obtain ⟨U₁, hU₁, hsm₁⟩ := exists_dense_open_smooth_of_iso e (W.nilradical.subschemeι ≫ q) hU
    (by rw [← Category.assoc e.hom, he]; exact hsm)
  obtain ⟨V₁, hV₁, hsmV₁⟩ := exists_dense_open_smooth_normalization
    (W.nilradical.subschemeι ≫ q) (W.finite_irreducibleComponents_reduction hW) U₁ hU₁ hsm₁
  obtain ⟨e', he'⟩ := W.exists_normalizationScheme_iso_reduction hW
  refine exists_dense_open_smooth_of_iso e'.symm (W.normalization hW ≫ q) hV₁ ?_
  rw [show (e'.symm.hom ≫ W.normalization hW ≫ q) =
      W.nilradical.subscheme.normalization (W.finite_irreducibleComponents_reduction hW) ≫
        W.nilradical.subschemeι ≫ q by
    rw [← he', Iso.symm_hom, Category.assoc, Iso.inv_hom_id_assoc, Category.assoc]]
  exact hsmV₁

end AlgebraicGeometry

end
