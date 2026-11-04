module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.Integral

/-!
# Coproducts of integral morphisms

A morphism of schemes is integral when the preimage of every affine open of the target is affine
and the induced map on sections is an integral ring map. This file shows that the morphism
`∐ Y ⟶ S` induced by a family `q i : Y i ⟶ S` of integral morphisms is again integral, as soon
as the family is *locally finite over `S`*: every affine open of `S` is met by the images of
only finitely many members.

Some such hypothesis is needed, because integrality is not a local property at the source: an
infinite coproduct of copies of `S ⟶ S` is never integral over `S`, since the preimage of a
nonempty affine open is an infinite disjoint union and hence not affine.

## Main results

* `AlgebraicGeometry.isIntegralHom_sigmaDesc`: a locally finite coproduct of integral morphisms
  with common target is integral.
* `AlgebraicGeometry.isIntegralHom_sigmaDesc_of_finite`: the special case of a finite family,
  where local finiteness is automatic.

## Implementation notes

Integrality is tested on affine opens `W` of `S` through
`AlgebraicGeometry.targetAffineLocally_affineAnd_iff`, which splits the two halves of the
definition. Over such a `W` the part of `∐ Y` lying over `W` is the disjoint union of the opens
`Oᵢ = ι i '' (q i ⁻¹ᵁ W)`, each affine and all but finitely many empty, so it is affine by
`AlgebraicGeometry.IsAffineOpen.biSup_of_disjoint`.

For the ring-theoretic half, a section `a` over that open is integral over `Γ(S, W)` because its
restriction to each `Oᵢ` is killed by a monic polynomial `pᵢ`, and the finite product of the
`pᵢ` belonging to the nonempty members then kills `a` on every `Oᵢ` at once — on the empty ones
because `Γ(∐ Y, ⊥)` is the zero ring. Separatedness of the structure sheaf upgrades this to
`a` being killed globally. This replaces the usual argument through the isomorphism
`Γ(∐ Y, V) ≅ ∏ i, Γ(Y i, ι i ⁻¹ᵁ V)`, which Mathlib only has for binary coproducts
(`AlgebraicGeometry.Scheme.coprodPresheafObjIso`).

The index type is required to live in the same universe as the schemes, because the sheaf
condition `TopCat.Presheaf.IsSheafUniqueGluing` quantifies over index types in the universe of
the underlying space.

## References

* [Stacks, Tag 01WM](https://stacks.math.columbia.edu/tag/01WM) for integral morphisms.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

variable {ι : Type u} [Small.{u} ι] {Y : ι → Scheme.{u}} {S : Scheme.{u}}
  (q : ∀ i, Y i ⟶ S) (W : S.Opens)

/-- The part of the summand `Y i` lying over `W` is the part of `Y i` lying over the preimage of
`W` in the coproduct. -/
private lemma preimage_sigmaι_preimage_sigmaDesc (i : ι) :
    Sigma.ι Y i ⁻¹ᵁ (Sigma.desc q ⁻¹ᵁ W) = q i ⁻¹ᵁ W := by
  rw [← Scheme.Hom.comp_preimage, Sigma.ι_desc]

/-- The image in `∐ Y` of the part of the summand `Y i` lying over `W` is contained in the part
of `∐ Y` lying over `W`. -/
private lemma sigmaι_image_preimage_le (i : ι) :
    Sigma.ι Y i ''ᵁ (q i ⁻¹ᵁ W) ≤ Sigma.desc q ⁻¹ᵁ W := by
  rw [← preimage_sigmaι_preimage_sigmaDesc q W i]
  exact (Scheme.Hom.image_preimage_eq_opensRange_inf _ _).trans_le inf_le_right

/-- The part of `∐ Y` lying over `W` is covered by the images of the parts of the summands lying
over `W`. -/
private lemma iSup_sigmaι_image_preimage :
    ⨆ i, Sigma.ι Y i ''ᵁ (q i ⁻¹ᵁ W) = Sigma.desc q ⁻¹ᵁ W := by
  have htop : ⨆ i, (Sigma.ι Y i).opensRange = (⊤ : (∐ Y).Opens) := by
    rw [← (sigmaOpenCover Y).iSup_opensRange]; rfl
  simp only [← preimage_sigmaι_preimage_sigmaDesc q W,
    Scheme.Hom.image_preimage_eq_opensRange_inf, ← iSup_inf_eq, htop, top_inf_eq]

/-- Over `W`, the map on sections induced by `Sigma.desc q` becomes, on the image of the summand
`Y i`, the map on sections induced by `q i`. -/
private lemma appLE_sigmaι_image_comp_appIso_hom (i : ι) :
    (Sigma.desc q).appLE W (Sigma.ι Y i ''ᵁ (q i ⁻¹ᵁ W)) (sigmaι_image_preimage_le q W i) ≫
        ((Sigma.ι Y i).appIso (q i ⁻¹ᵁ W)).hom = (q i).app W := by
  simp [Scheme.Hom.appIso_hom', Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_comp_appLE]

/-- A coproduct of integral morphisms to a common target is integral, provided the family is
locally finite over the target: every affine open of the target is met by the image of only
finitely many members.

See [Stacks, Tag 01WM](https://stacks.math.columbia.edu/tag/01WM) for integral morphisms. -/
theorem isIntegralHom_sigmaDesc [∀ i, IsIntegralHom (q i)]
    (hlf : ∀ U : S.Opens, IsAffineOpen U → {i : ι | (q i ⁻¹ᵁ U) ≠ ⊥}.Finite) :
    IsIntegralHom (Sigma.desc q) := by
  have hAP : HasAffineProperty @IsIntegralHom (affineAnd RingHom.IsIntegral) :=
    IsIntegralHom.hasAffineProperty
  rw [HasAffineProperty.eq_targetAffineLocally (P := @IsIntegralHom) (Q := affineAnd _),
    targetAffineLocally_affineAnd_iff RingHom.isIntegral_respectsIso]
  clear hAP
  intro W hW
  set O : ι → (∐ Y).Opens := fun i ↦ Sigma.ι Y i ''ᵁ (q i ⁻¹ᵁ W) with hOdef
  have hle : ∀ i, O i ≤ Sigma.desc q ⁻¹ᵁ W := sigmaι_image_preimage_le q W
  have hsup : ⨆ i, O i = Sigma.desc q ⁻¹ᵁ W := iSup_sigmaι_image_preimage q W
  have hfin := hlf W hW
  have haff : ∀ i, IsAffineOpen (O i) := fun i ↦
    (hW.preimage (q i)).image_of_isOpenImmersion _
  have hbot : ∀ i, q i ⁻¹ᵁ W = ⊥ → O i = ⊥ := by
    intro i hi
    simp only [hOdef, hi]
    ext x
    simp
  refine ⟨?_, ?_⟩
  · -- The part of `∐ Y` over `W` is a finite disjoint union of affine opens.
    have hrestrict : ⨆ i, O i = ⨆ i ∈ {i : ι | q i ⁻¹ᵁ W ≠ ⊥}, O i := by
      refine le_antisymm (iSup_le fun i ↦ ?_) (iSup₂_le fun i _ ↦ le_iSup _ i)
      by_cases hi : q i ⁻¹ᵁ W = ⊥
      · rw [hbot i hi]
        exact bot_le
      · exact le_iSup_of_le i (le_iSup_of_le hi le_rfl)
    rw [← hsup, hrestrict]
    exact IsAffineOpen.biSup_of_disjoint hfin (fun i _ ↦ haff i) fun i _ j _ hij ↦
      (disjoint_opensRange_sigmaι Y i j hij).mono
        (Scheme.Hom.image_le_opensRange _ _) (Scheme.Hom.image_le_opensRange _ _)
  · -- A section over that part is killed by a product of monic polynomials.
    intro a
    set r : ∀ i, Γ(∐ Y, Sigma.desc q ⁻¹ᵁ W) ⟶ Γ(∐ Y, O i) := fun i ↦
      (∐ Y).presheaf.map (homOfLE (hle i)).op with hrdef
    have hcomp : ∀ i, (Sigma.desc q).app W ≫ r i =
        (Sigma.desc q).appLE W (O i) (hle i) := by
      intro i
      rw [hrdef, Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_map]
    have hψ : ∀ i, RingHom.IsIntegral ((Sigma.desc q).appLE W (O i) (hle i)).hom := by
      intro i
      rw [← RingHom.isIntegral_respectsIso.cancel_right_isIso _
        ((Sigma.ι Y i).appIso (q i ⁻¹ᵁ W)).hom, ← CommRingCat.hom_comp,
        appLE_sigmaι_image_comp_appIso_hom q W i]
      exact (q i).isIntegral_app W hW
    choose p hpm hp0 using fun i ↦ hψ i ((r i).hom a)
    refine ⟨∏ i ∈ hfin.toFinset, p i,
      Polynomial.monic_prod_of_monic _ _ fun i _ ↦ hpm i, ?_⟩
    refine (∐ Y).sheaf.eq_of_locally_eq' O (Sigma.desc q ⁻¹ᵁ W) (fun i ↦ homOfLE (hle i))
      hsup.ge _ 0 fun i ↦ ?_
    classical
    show (r i).hom _ = (r i).hom 0
    rw [map_zero, Polynomial.hom_eval₂, ← CommRingCat.hom_comp, hcomp i]
    by_cases hi : i ∈ hfin.toFinset
    · rw [← Finset.mul_prod_erase _ _ hi, Polynomial.eval₂_mul, hp0 i, zero_mul]
    · have : Subsingleton Γ(∐ Y, O i) := by
        rw [hbot i (by simpa using hi)]
        infer_instance
      exact Subsingleton.elim _ _

/-- A finite coproduct of integral morphisms to a common target is integral.

See [Stacks, Tag 01WM](https://stacks.math.columbia.edu/tag/01WM) for integral morphisms. -/
theorem isIntegralHom_sigmaDesc_of_finite [Finite ι] [∀ i, IsIntegralHom (q i)] :
    IsIntegralHom (Sigma.desc q) :=
  isIntegralHom_sigmaDesc q fun _ _ ↦ Set.toFinite _

end AlgebraicGeometry

end
