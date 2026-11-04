module

public import StacksFrontier.AlgebraicGeometry.Spaces.FormallySmooth.ChartLifts
public import StacksFrontier.AlgebraicGeometry.Spaces.FormallySmooth.Etale

/-!
# Étale charts have unique infinitesimal lifts

Let `p : X ⟶ h_{Spec A'}` be a presheaf over `Spec A'`, and let `c : h_{Spec C} ⟶ X` be a
formally étale transformation from the spectrum of an `A'`-algebra `C`, lying over `Spec A'`.
Then the tautological section of `X` over `Spec C` has unique infinitesimal lifts in the sense
of `AlgebraicGeometry.Space.ChartUniqueLifts`
(`AlgebraicGeometry.Space.chartUniqueLifts_of_formallyEtale`): the lifts of a section of `X`
along a square-zero thickening through the chart are the lifts of the ring map presenting it.

The comparison between morphisms of the site and maps of algebras is
`AlgebraicGeometry.Space.existsUnique_specOverHom`: a morphism `Spec E ⟶ Spec C` of the site
lying over `Spec A'` is `Spec` of exactly one map of `A'`-algebras `C → E`.

## Main results

* `AlgebraicGeometry.Space.existsUnique_specOverHom`: a morphism of spectra of `A'`-algebras
  lying over `Spec A'` is `Spec` of a unique map of `A'`-algebras.
* `AlgebraicGeometry.Space.chartUniqueLifts_of_formallyEtale`: the tautological section of a
  formally étale chart has unique infinitesimal lifts.

## References

* [Stacks Project, Tag 04AM](https://stacks.math.columbia.edu/tag/04AM)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite Stacks.SquareZeroLift

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {A' : Type u} [CommRing A'] {s₀ : Spec (.of A') ⟶ S} {hA' : B.Contains (Spec (.of A'))}

/-- The map `g ↦ specOverHom g` from maps of `A'`-algebras `R → R'` to morphisms of the site
`Spec R' ⟶ Spec R` is injective. -/
theorem specOverHom_injective {R R' : Type u} [CommRing R] [CommRing R'] [Algebra A' R]
    [Algebra A' R'] {hR : B.Contains (Spec (.of R))} {hR' : B.Contains (Spec (.of R'))}
    {g g' : R →ₐ[A'] R'}
    (h : specOverHom B S hS s₀ hR hR' g = specOverHom B S hS s₀ hR hR' g') : g = g' := by
  have h' := congrArg (BigFppfOver.toScheme B S hS).map h
  rw [toScheme_map_specOverHom, toScheme_map_specOverHom] at h'
  have h'' := Spec.map_injective h'
  exact AlgHom.coe_ringHom_injective (congrArg CommRingCat.Hom.hom h'')

/-- **A morphism of spectra of `A'`-algebras lying over `Spec A'` is `Spec` of a unique map of
algebras.** -/
theorem existsUnique_specOverHom {E C : Type u} [CommRing E] [CommRing C] [Algebra A' E]
    [Algebra A' C] [hE : InSite B E] [hC : InSite B C]
    (u : specOver B S hS s₀ E hE.out ⟶ specOver B S hS s₀ C hC.out)
    (hu : u ≫ specOverHom B S hS s₀ hA' hC.out (Algebra.ofId A' C) =
      specOverHom B S hS s₀ hA' hE.out (Algebra.ofId A' E)) :
    ∃! q : C →ₐ[A'] E, specOverHom B S hS s₀ hC.out hE.out q = u := by
  let φ : CommRingCat.of C ⟶ CommRingCat.of E := Spec.preimage ((BigFppfOver.toScheme B S hS).map u)
  have hφ : Spec.map φ = (BigFppfOver.toScheme B S hS).map u := Spec.map_preimage _
  have hcomm : φ.hom.comp (algebraMap A' C) = algebraMap A' E := by
    have h := congrArg (BigFppfOver.toScheme B S hS).map hu
    rw [Functor.map_comp, toScheme_map_specOverHom, toScheme_map_specOverHom, ← hφ,
      ← Spec.map_comp] at h
    have h' := Spec.map_injective h
    exact congrArg CommRingCat.Hom.hom h'
  let q : C →ₐ[A'] E := { φ.hom with commutes' := fun a => RingHom.congr_fun hcomm a }
  refine ⟨q, ?_, fun q' hq' => specOverHom_injective (hq'.trans ?_)⟩
  · apply (BigFppfOver.toScheme B S hS).map_injective
    rw [toScheme_map_specOverHom, ← hφ]
    rfl
  · apply (BigFppfOver.toScheme B S hS).map_injective
    rw [toScheme_map_specOverHom, ← hφ]
    rfl

variable {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {p : X ⟶ yoneda.obj (specOver B S hS s₀ A' hA')}

/-- The tautological section of `X` over the source of a chart lying over `Spec A'`. -/
def relChartSection {C : Type u} [CommRing C] [Algebra A' C] [hC : InSite B C]
    (c : yoneda.obj (specOver B S hS s₀ C hC.out) ⟶ X)
    (hcp : c ≫ p = yoneda.map (specOverHom B S hS s₀ hA' hC.out (Algebra.ofId A' C))) :
    RelSec p C :=
  ⟨c.app _ (𝟙 _), by
    have h := congrArg (fun g => g.app (op (specOver B S hS s₀ C hC.out)) (𝟙 _)) hcp
    simpa using h⟩

/-- Pulling back the tautological section of a chart `c` along a map of `A'`-algebras `q : C → E`
gives the value of `c` at the morphism `Spec E ⟶ Spec C` induced by `q`. -/
theorem chartSection_map {C E : Type u} [CommRing C] [CommRing E] [Algebra A' C] [Algebra A' E]
    [hC : InSite B C] [hE : InSite B E] (c : yoneda.obj (specOver B S hS s₀ C hC.out) ⟶ X)
    (hcp : c ≫ p = yoneda.map (specOverHom B S hS s₀ hA' hC.out (Algebra.ofId A' C)))
    (q : C →ₐ[A'] E) :
    (RelSec.map q (relChartSection c hcp)).1 = c.app _ (specOverHom B S hS s₀ hC.out hE.out q) := by
  rw [RelSec.map_val]
  show X.map _ (c.app _ (𝟙 _)) = _
  rw [← NatTrans.naturality_apply]
  show c.app _ (specOverHom B S hS s₀ hC.out hE.out q ≫ 𝟙 _) = _
  rw [Category.comp_id]

/-- For a surjective map of `A'`-algebras `π : E → F` with square-zero kernel, the induced
morphism `Spec F ⟶ Spec E` is a square-zero closed immersion. -/
theorem isSquareZeroClosedImmersion_specOverHom {E F : Type u} [CommRing E] [CommRing F]
    [Algebra A' E] [Algebra A' F] [hE : InSite B E] [hF : InSite B F] {π : E →ₐ[A'] F}
    (hπ : Function.Surjective π) (hsq : IsSqZero π) :
    IsSquareZeroClosedImmersion B S hS (specOverHom B S hS s₀ hE.out hF.out π) := by
  have hker : RingHom.ker (CommRingCat.ofHom π.toRingHom).hom ^ 2 = ⊥ := by
    rw [pow_two, eq_bot_iff, Ideal.mul_le]
    exact fun a ha b hb => (Ideal.mem_bot).2 (hsq a b ha hb)
  exact Stacks.Smooth.isFirstOrderThickening_specMap (CommRingCat.ofHom π.toRingHom) hπ hker

/-- **A formally étale chart has unique infinitesimal lifts.** -/
theorem chartUniqueLifts_of_formallyEtale {C : Type u} [CommRing C] [Algebra A' C]
    [hC : InSite B C] (c : yoneda.obj (specOver B S hS s₀ C hC.out) ⟶ X) (hc : FormallyEtale c)
    (hcp : c ≫ p = yoneda.map (specOverHom B S hS s₀ hA' hC.out (Algebra.ofId A' C))) :
    ChartUniqueLifts (relChartSection c hcp) := by
  intro E F _ _ _ _ hE hF π hπ hsq ζ z hz
  have hi := isSquareZeroClosedImmersion_specOverHom (B := B) (hS := hS) (s₀ := s₀) hπ hsq
  have hxy : c.app _ (specOverHom B S hS s₀ hC.out hF.out ζ) =
      X.map (specOverHom B S hS s₀ hE.out hF.out π).op z.1 := by
    rw [← chartSection_map c hcp ζ]
    exact (congrArg Subtype.val hz).symm
  obtain ⟨u, ⟨hu₁, hu₂⟩, huniq⟩ := hc (specOver B S hS s₀ F hF.out) (specOver B S hS s₀ E hE.out)
    (inferInstanceAs (IsAffine (Spec (.of F)))) (inferInstanceAs (IsAffine (Spec (.of E)))) _
    hi _ z.1 hxy
  have hover : u ≫ specOverHom B S hS s₀ hA' hC.out (Algebra.ofId A' C) =
      specOverHom B S hS s₀ hA' hE.out (Algebra.ofId A' E) := by
    have h := congrArg (fun g => g.app (op (specOver B S hS s₀ E hE.out)) u) hcp
    simp only [NatTrans.comp_app, types_comp_apply, hu₂, z.2] at h
    exact h.symm
  obtain ⟨q, hq, hquniq⟩ := existsUnique_specOverHom (hA' := hA') u hover
  refine ⟨q, ⟨?_, ?_⟩, fun q' ⟨hq'₁, hq'₂⟩ => ?_⟩
  · apply specOverHom_injective (hR := hC.out) (hR' := hF.out) (s₀ := s₀)
    rw [← specOverHom_comp, hq]
    exact hu₁
  · exact RelSec.ext ((chartSection_map c hcp q).trans (by rw [hq]; exact hu₂))
  · refine hquniq q' (huniq _ ⟨?_, ?_⟩)
    · show specOverHom B S hS s₀ hE.out hF.out π ≫ specOverHom B S hS s₀ hC.out hE.out q' = _
      rw [specOverHom_comp, hq'₁]
    · exact (chartSection_map c hcp q').symm.trans (congrArg Subtype.val hq'₂)

end AlgebraicGeometry.Space

end
