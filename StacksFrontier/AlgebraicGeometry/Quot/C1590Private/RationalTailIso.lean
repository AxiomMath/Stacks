module

public import StacksFrontier.AlgebraicGeometry.Curves.ContractingRationalTails.RationalTail
public import StacksFrontier.AlgebraicGeometry.Curves.GenusCurve.GeometricGenusNormalizationBound

/-!
# Rational tails are invariant under isomorphism

Let `ψ : Y ⟶ X` be an isomorphism of schemes over a field `k`. Pulling back ideal sheaves along
`ψ` takes the rational tails of `X` ([Stacks, Tag 0E3H]) to the rational tails of `Y`. In
particular `X` has no rational tail exactly when `Y` has none.

Every ingredient of the rational-tail condition is transported by `ψ`: along an isomorphism the
pullback of an ideal sheaf is its pushforward along the inverse, so it commutes with suprema and
takes vanishing ideals of closed sets to vanishing ideals of their images; the closed subscheme
of the pullback is isomorphic to the closed subscheme of the ideal sheaf; the closure of the
complement of a closed subscheme is carried to the closure of the complement of its pullback;
and evaluation of global functions at a point and the genus are invariant under isomorphism.

## Main results

* `AlgebraicGeometry.C1590Private.comap_eq_map_inv`: along an isomorphism, pullback of ideal
  sheaves is pushforward along the inverse.
* `AlgebraicGeometry.C1590Private.comapSubschemeIso`: the closed subscheme of the pullback of an
  ideal sheaf along an isomorphism is isomorphic to the closed subscheme of the ideal sheaf.
* `AlgebraicGeometry.C1590Private.complementaryCurveIdeal_comap`: the closure of the complement
  commutes with pullback along an isomorphism.
* `AlgebraicGeometry.C1590Private.isRationalTail_comap`: pullback along an isomorphism over `k`
  takes rational tails to rational tails.
* `AlgebraicGeometry.C1590Private.forall_not_isRationalTail_iff_of_isIso`: two schemes isomorphic
  over `k` have rational tails simultaneously.

## References

* [Stacks Project, Tag 0E3H](https://stacks.math.columbia.edu/tag/0E3H)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.C1590Private

open Scheme.IdealSheafData

variable {X Y : Scheme.{u}}

/-- Along an isomorphism `ψ`, the pullback of an ideal sheaf is its pushforward along `ψ⁻¹`. -/
theorem comap_eq_map_inv (I : X.IdealSheafData) (ψ : Y ⟶ X) [IsIso ψ] :
    I.comap ψ = I.map (inv ψ) := by
  refine le_antisymm ?_ ?_
  · rw [le_map_iff_comap_le, ← comap_comp, IsIso.inv_hom_id, comap_id]
  · calc I.map (inv ψ) = (I.map (inv ψ)).comap (ψ ≫ inv ψ) := by
          rw [IsIso.hom_inv_id, comap_id]
      _ = ((I.map (inv ψ)).comap (inv ψ)).comap ψ := comap_comp _ _ _
      _ ≤ I.comap ψ := comap_mono ψ (comap_map_le I (inv ψ))

/-- The closed subscheme cut out by the pullback of an ideal sheaf along an isomorphism is
isomorphic to the closed subscheme cut out by the ideal sheaf. -/
def comapSubschemeIso (I : X.IdealSheafData) (ψ : Y ⟶ X) [IsIso ψ] :
    (I.comap ψ).subscheme ≅ I.subscheme :=
  I.comapIso ψ ≪≫ asIso (pullback.snd ψ I.subschemeι)

/-- The isomorphism `comapSubschemeIso I ψ`, followed by the closed immersion of `I.subscheme`, is
the closed immersion of the subscheme of the pullback followed by `ψ`. -/
@[reassoc (attr := simp)]
theorem comapSubschemeIso_hom_subschemeι (I : X.IdealSheafData) (ψ : Y ⟶ X) [IsIso ψ] :
    (comapSubschemeIso I ψ).hom ≫ I.subschemeι = (I.comap ψ).subschemeι ≫ ψ := by
  simp [comapSubschemeIso]

/-- The point of the subscheme of the pullback corresponding to a point of the subscheme lies over
the image of that point under `ψ⁻¹`. -/
theorem subschemeι_comapSubschemeIso_inv_apply (I : X.IdealSheafData) (ψ : Y ⟶ X) [IsIso ψ]
    (x : I.subscheme) :
    (I.comap ψ).subschemeι ((comapSubschemeIso I ψ).inv x) = inv ψ (I.subschemeι x) := by
  have h := congrArg (fun f => (f ≫ inv ψ) ((comapSubschemeIso I ψ).inv x))
    (comapSubschemeIso_hom_subschemeι I ψ)
  simp only [Category.assoc, IsIso.hom_inv_id, Category.comp_id, Scheme.Hom.comp_apply,
    Scheme.inv_hom_apply] at h
  exact h.symm

/-- The image of an open subset under `ψ⁻¹` is its preimage under `ψ`. -/
theorem inv_image_eq_preimage (ψ : Y ⟶ X) [IsIso ψ] (s : Set X) :
    (inv ψ : X ⟶ Y) '' s = ψ ⁻¹' s := by
  ext y
  refine ⟨?_, fun hy => ⟨ψ y, hy, ?_⟩⟩
  · rintro ⟨x, hx, rfl⟩
    have : ψ (inv ψ x) = x := Scheme.inv_hom_apply (asIso ψ) x
    simpa [Set.mem_preimage, this] using hx
  · exact Scheme.hom_inv_apply (asIso ψ) y

/-- **The closure of the complement commutes with pullback along an isomorphism.** -/
theorem complementaryCurveIdeal_comap (C : X.IdealSheafData) (ψ : Y ⟶ X) [IsIso ψ] :
    complementaryCurveIdeal (C.comap ψ) = (complementaryCurveIdeal C).comap ψ := by
  have hU : (C.comap ψ).support.compl = (inv ψ) ''ᵁ C.support.compl := by
    apply TopologicalSpace.Opens.ext
    rw [support_comap]
    show (ψ ⁻¹' (C.support : Set X))ᶜ = (inv ψ : X ⟶ Y) '' (C.support : Set X)ᶜ
    rw [inv_image_eq_preimage]
    rfl
  rw [complementaryCurveIdeal, complementaryCurveIdeal, hU, comap_eq_map_inv, map_ker,
    ← Scheme.Hom.isoImage_hom_ι, Scheme.Hom.ker_comp_of_isIso]

/-- **Rational tails are invariant under isomorphism.** For an isomorphism `ψ : Y ⟶ X` of schemes
over `k`, with `X` proper over `k`, the pullback along `ψ` of a rational tail of `X` is a rational
tail of `Y`. -/
theorem isRationalTail_comap {k : Type u} [Field k] [X.Over (Spec (.of k))]
    [Y.Over (Spec (.of k))] [IsProper (X ↘ Spec (.of k))] (ψ : Y ⟶ X) [IsIso ψ]
    (hψ : ψ ≫ X ↘ Spec (.of k) = Y ↘ Spec (.of k)) {C : X.IdealSheafData}
    (hC : IsRationalTail k X C) : IsRationalTail k Y (C.comap ψ) := by
  obtain ⟨hint, hirr, hne, x, hx, hinter, hΓ, hg⟩ := hC
  set θ := comapSubschemeIso C ψ
  have hx' : (C.comap ψ).subschemeι (θ.inv x) = inv ψ (C.subschemeι x) :=
    subschemeι_comapSubschemeIso_inv_apply C ψ x
  have hcl : IsClosed ({(C.comap ψ).subschemeι (θ.inv x)} : Set Y) := by
    rw [hx', ← Set.image_singleton]
    exact (Scheme.homeoOfIso (asIso (inv ψ))).isClosedMap _ hx
  refine ⟨IsIntegral.of_isIso θ.inv, ?_, ?_, θ.inv x, hcl, ?_, ?_, ?_⟩
  · rw [support_comap, TopologicalSpace.Closeds.coe_preimage]
    refine preimage_mem_irreducibleComponents hirr ψ.isOpenEmbedding ?_
    obtain ⟨z, hz⟩ := hirr.1.nonempty
    exact ⟨z, hz, inv ψ z, Scheme.inv_hom_apply (asIso ψ) z⟩
  · show Nonempty (complementaryCurveIdeal (C.comap ψ)).subscheme
    rw [complementaryCurveIdeal_comap]
    exact hne.map (comapSubschemeIso (complementaryCurveIdeal C) ψ).inv
  · rw [intersectionWithComplementaryCurveIdeal, complementaryCurveIdeal_comap, ← comap_sup]
    show (intersectionWithComplementaryCurveIdeal C).comap ψ = _
    rw [hinter, comap_eq_map_inv, map_vanishingIdeal]
    congr 1
    ext1
    rw [TopologicalSpace.Closeds.coe_closure]
    show closure ((inv ψ : X ⟶ Y) '' {C.subschemeι x}) =
      {(C.comap ψ).subschemeι (θ.inv x)}
    rw [Set.image_singleton, ← hx']
    exact hcl.closure_eq
  · have hnat := Scheme.Γevaluation_naturality θ.hom (θ.inv x)
    have hΓ' : IsIso (C.subscheme.Γevaluation (θ.hom (θ.inv x))) := by
      rwa [Scheme.inv_hom_apply]
    have : IsIso θ.hom.appTop := inferInstanceAs (IsIso (θ.hom.app ⊤))
    have : IsIso (θ.hom.appTop ≫ (C.comap ψ).subscheme.Γevaluation (θ.inv x)) := by
      rw [← hnat]
      infer_instance
    exact IsIso.of_isIso_comp_left θ.hom.appTop _
  · rw [← hψ, ← Category.assoc, ← comapSubschemeIso_hom_subschemeι, Category.assoc,
      genus_comp_iso_eq k (C.subschemeι ≫ X ↘ Spec (.of k)) θ]
    exact hg

/-- **Isomorphic schemes have rational tails simultaneously.** For an isomorphism `ψ : Y ⟶ X` of
proper schemes over `k`, `X` has no rational tail exactly when `Y` has none. -/
theorem forall_not_isRationalTail_iff_of_isIso {k : Type u} [Field k] [X.Over (Spec (.of k))]
    [Y.Over (Spec (.of k))] [IsProper (X ↘ Spec (.of k))] (ψ : Y ⟶ X) [IsIso ψ]
    (hψ : ψ ≫ X ↘ Spec (.of k) = Y ↘ Spec (.of k)) :
    (∀ C : X.IdealSheafData, ¬ IsRationalTail k X C) ↔
      ∀ D : Y.IdealSheafData, ¬ IsRationalTail k Y D := by
  have hψ' : inv ψ ≫ Y ↘ Spec (.of k) = X ↘ Spec (.of k) := by
    rw [← hψ, IsIso.inv_hom_id_assoc]
  have : IsProper (Y ↘ Spec (.of k)) := by
    rw [← hψ]
    infer_instance
  refine ⟨fun h D hD => ?_, fun h C hC => h _ (isRationalTail_comap ψ hψ hC)⟩
  exact h _ (isRationalTail_comap (inv ψ) hψ' hD)

end AlgebraicGeometry.C1590Private

end
