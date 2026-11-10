module

public import StacksFrontier.AlgebraicGeometry.Chow.AffineBundle.LocalModelBundleCharts
public import StacksFrontier.AlgebraicGeometry.Chow.RationalEquivalence.IntersectionInvertibleSheaf

/-!
# A zero scheme presented by local models is a local-model bundle

Let `q : T ⟶ Y` be a morphism of schemes, let `M` be an invertible `𝒪_T`-module and let `t` be a
global section of it. The zero scheme `Z(t) ⊆ T` carries the morphism `Z(t) ⟶ T ⟶ Y`, and this
file gives the criterion for that morphism to be a local-model bundle in the sense of
`Stacks.AffineBundle.IsLocalModelBundle`: on an affine open `V` of `Y` over which the inverse
image `q^{-1}V` is affine and `M` is trivialized, the part of `Z(t)` lying over `V` is the
spectrum of `Γ(T, q^{-1}V)` modulo the local equation of `t`, and it suffices to identify that
quotient with a local model `B[z₁, z₂]/(z₁z₂ - b)` over `B = Γ(Y, V)`.

This is the shape in which the structure morphism `p : L ⟶ Y` of [Stacks, Tag 0F97] is a
local-model bundle: `T` is the fibre product of the two line bundles, `t` is the equation
`z₁ ⊗ z₂ - q^*s`, and the identification of the quotient is the rescaling of the two coordinates
into the standard ones.

## Main results

* `Stacks.AffineBundle.isLocalModelBundle_zeroScheme_of_charts` — **a zero scheme whose local
  equation presents a local model over every affine open of a base is a local-model bundle over
  that base.**

## Implementation notes

The identification of the part of the zero scheme over an affine open with the spectrum of the
quotient is `Stacks.Divisors.zeroSchemeAffineOpenIso`, and its compatibility with the closed
immersion into the ambient scheme is `Stacks.Divisors.zeroSchemeAffineOpenIso_comp`; composing the
latter with `q` and using `AlgebraicGeometry.IsAffineOpen.SpecMap_appLE_fromSpec` to push `q` past
`fromSpec` turns the whole statement into one equation between morphisms of spectra, hence into
one equation between ring maps, which is the hypothesis `hψ`.

The ring isomorphism is taken in the direction *out of* the quotient, since that is the direction
in which the chart of `Stacks.AffineBundle.IsLocalModelBundle` runs; the isomorphism of schemes
built from it is written out rather than obtained from an opposite-category functor, so that
`AlgebraicGeometry.Spec.map_comp` applies to it directly.

## References

* [Stacks Project, Tag 0F97](https://stacks.math.columbia.edu/tag/0F97)
* [Stacks Project, Tag 02OQ](https://stacks.math.columbia.edu/tag/02OQ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite

universe u

namespace Stacks.AffineBundle

/-- `Spec` of a ring map and of a left inverse of it compose to the identity. -/
private theorem spec_map_ofHom_comp_eq_id {A C : Type u} [CommRing A] [CommRing C] (f : A →+* C)
    (g : C →+* A) (h : ∀ x, g (f x) = x) :
    Spec.map (CommRingCat.ofHom g) ≫ Spec.map (CommRingCat.ofHom f) =
      𝟙 (Spec (CommRingCat.of A)) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  convert Spec.map_id (CommRingCat.of A)
  exact CommRingCat.hom_ext (RingHom.ext h)

/-- The spectrum of a ring isomorphism, as an isomorphism of schemes. -/
private def specIsoOfRingEquiv {A C : Type u} [CommRing A] [CommRing C] (ψ : A ≃+* C) :
    Spec (CommRingCat.of A) ≅ Spec (CommRingCat.of C) where
  hom := Spec.map (CommRingCat.ofHom ψ.symm.toRingHom)
  inv := Spec.map (CommRingCat.ofHom ψ.toRingHom)
  hom_inv_id := spec_map_ofHom_comp_eq_id ψ.toRingHom ψ.symm.toRingHom ψ.symm_apply_apply
  inv_hom_id := spec_map_ofHom_comp_eq_id ψ.symm.toRingHom ψ.toRingHom ψ.apply_symm_apply

/-- **A zero scheme whose local equation presents a local model over every affine open of a base
is a local-model bundle over that base.** The data asked for at a point `y` of `Y` is an affine
open `V` containing it over which the inverse image `q^{-1}V` is affine, a trivialization `ε` of
the invertible module there with `a` the local equation of the section, an element `b` of
`Γ(Y, V)` and a ring isomorphism of `Γ(T, q^{-1}V)/(a)` with the local model of `b` that carries
the image of a function on `V` to the corresponding constant. -/
theorem isLocalModelBundle_zeroScheme_of_charts {Y T : Scheme.{u}} (q : T ⟶ Y) (M : T.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible T.sheaf.obj T.ringCatSheaf.property M]
    (t : Γ(M, ⊤))
    (h : ∀ y : Y, ∃ (V : Y.Opens) (_ : IsAffineOpen V) (_ : y ∈ V)
      (_ : IsAffineOpen (q ⁻¹ᵁ V))
      (ε : Γ(M, q ⁻¹ᵁ V) ≃ₗ[Γ(T, q ⁻¹ᵁ V)] Γ(T, q ⁻¹ᵁ V)) (a : Γ(T, q ⁻¹ᵁ V))
      (_ : ε (M.presheaf.map (homOfLE le_top).op t) = a) (b : Γ(Y, V))
      (ψ : (Γ(T, q ⁻¹ᵁ V) ⧸ Ideal.span ({a} : Set Γ(T, q ⁻¹ᵁ V))) ≃+*
        LocalModel Γ(Y, V) b),
      ∀ c : Γ(Y, V),
        ψ (Ideal.Quotient.mk (Ideal.span ({a} : Set Γ(T, q ⁻¹ᵁ V)))
            ((q.appLE V (q ⁻¹ᵁ V) le_rfl).hom c)) =
          algebraMap Γ(Y, V) (LocalModel Γ(Y, V) b) c) :
    IsLocalModelBundle ((Stacks.Divisors.zeroScheme T M t).subschemeι ≫ q) := by
  refine isLocalModelBundle_of_charts _ fun y ↦ ?_
  obtain ⟨V, hV, hyV, hW, ε, a, hεa, b, ψ, hψ⟩ := h y
  refine ⟨V, hV, hyV, b,
    Stacks.Divisors.zeroSchemeAffineOpenIso T M t ⟨q ⁻¹ᵁ V, hW⟩ ε a hεa ≪≫
      specIsoOfRingEquiv ψ, ?_⟩
  -- The ring-level identity behind the chart.
  have hring : CommRingCat.ofHom (algebraMap Γ(Y, V) (LocalModel Γ(Y, V) b)) ≫
      CommRingCat.ofHom ψ.symm.toRingHom =
      q.appLE V (q ⁻¹ᵁ V) le_rfl ≫
        CommRingCat.ofHom
          (Ideal.Quotient.mk (Ideal.span ({a} : Set Γ(T, q ⁻¹ᵁ V)))) :=
    CommRingCat.hom_ext (RingHom.ext fun c ↦ by
      simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.coe_comp,
        Function.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom]
      rw [← hψ c, ψ.symm_apply_apply])
  -- Push `q` past `fromSpec` on the affine open.
  have hpush : hW.fromSpec ≫ q = Spec.map (q.appLE V (q ⁻¹ᵁ V) le_rfl) ≫ hV.fromSpec :=
    (IsAffineOpen.SpecMap_appLE_fromSpec q hV hW le_rfl).symm
  have hzero : (Stacks.Divisors.zeroSchemeAffineOpenIso T M t ⟨q ⁻¹ᵁ V, hW⟩ ε a hεa).hom ≫
      Spec.map (CommRingCat.ofHom
          (Ideal.Quotient.mk (Ideal.span ({a} : Set Γ(T, q ⁻¹ᵁ V))))) ≫ hW.fromSpec =
      ((Stacks.Divisors.zeroScheme T M t).subschemeι ⁻¹ᵁ (q ⁻¹ᵁ V)).ι ≫
        (Stacks.Divisors.zeroScheme T M t).subschemeι :=
    Stacks.Divisors.zeroSchemeAffineOpenIso_comp T M t ⟨q ⁻¹ᵁ V, hW⟩ ε a hεa
  calc
    (Stacks.Divisors.zeroSchemeAffineOpenIso T M t ⟨q ⁻¹ᵁ V, hW⟩ ε a hεa ≪≫
            specIsoOfRingEquiv ψ).hom ≫
          localModelSpecMap Γ(Y, V) b ≫ hV.fromSpec
        = (Stacks.Divisors.zeroSchemeAffineOpenIso T M t ⟨q ⁻¹ᵁ V, hW⟩ ε a hεa).hom ≫
            Spec.map (CommRingCat.ofHom
              (Ideal.Quotient.mk (Ideal.span ({a} : Set Γ(T, q ⁻¹ᵁ V))))) ≫
              hW.fromSpec ≫ q := by
          rw [Iso.trans_hom, Category.assoc]
          refine congrArg _ ?_
          rw [hpush, localModelSpecMap, specIsoOfRingEquiv]
          change Spec.map (CommRingCat.ofHom ψ.symm.toRingHom) ≫
            Spec.map (CommRingCat.ofHom (algebraMap Γ(Y, V) (LocalModel Γ(Y, V) b))) ≫
              hV.fromSpec = _
          rw [← Category.assoc, ← Spec.map_comp, ← Category.assoc, ← Spec.map_comp, hring]
    _ = ((Stacks.Divisors.zeroScheme T M t).subschemeι ⁻¹ᵁ (q ⁻¹ᵁ V)).ι ≫
          (Stacks.Divisors.zeroScheme T M t).subschemeι ≫ q := by
          rw [← Category.assoc ((Stacks.Divisors.zeroScheme T M t).subschemeι ⁻¹ᵁ (q ⁻¹ᵁ V)).ι
            (Stacks.Divisors.zeroScheme T M t).subschemeι q, ← hzero]
          simp only [Category.assoc]

end Stacks.AffineBundle

end
