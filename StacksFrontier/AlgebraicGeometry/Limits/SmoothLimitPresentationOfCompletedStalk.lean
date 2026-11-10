module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Stalk
public import StacksFrontier.AlgebraicGeometry.Limits.SmoothLimitPresentation
public import StacksFrontier.RingTheory.FormalFibres.Localization
public import StacksFrontier.RingTheory.GRing.EssFiniteType
public import StacksFrontier.RingTheory.Smoothing.IndSmoothCompletedLocalization

/-!
# The completed local ring of an affine Noetherian scheme as a cofiltered limit of smooth schemes

Let `S` be an affine Noetherian scheme and `s` a point of `S` whose local ring `𝒪_{S, s}` is a
G-ring. Then the spectrum of the completion `𝒪^∧_{S, s}` is the limit of a cofiltered diagram of
affine schemes smooth over `S`, compatibly with the canonical morphism
`Spec 𝒪^∧_{S, s} ⟶ Spec 𝒪_{S, s} ⟶ S`.

## Main results

* `AlgebraicGeometry.exists_cofiltered_smooth_limit_presentation_specCompletedStalk`: the
  geometric form described above.

## Implementation notes

The two inputs are `Stacks.Smoothing.indSmooth_adicCompletion_atPrime` — for a Noetherian ring
`R` and a prime `p` with `R_p` a G-ring, the completion of `R_p` at its maximal ideal is
ind-smooth over `R` — and `AlgebraicGeometry.exists_cofiltered_smooth_limit_presentation`, which
turns an ind-smooth algebra into a cofiltered limit of affine schemes smooth over the base.

Gluing them is a matter of three identifications. With `R = Γ(S, ⊤)` and `p` the prime of `R`
corresponding to `s`, the stalk `𝒪_{S, s}` is a localization of `R` at `p`
(`AlgebraicGeometry.IsAffineOpen.isLocalization_stalk`), hence isomorphic to
`Localization.AtPrime p` by `IsLocalization.algEquiv`; the G-ring hypothesis transports across
that isomorphism by Tag 07PV (`isGRing_of_essFiniteType`, applied to the algebra structure the
isomorphism defines); and the completions of the two isomorphic local rings are isomorphic by
`Stacks.FormalFibres.completionRingEquiv`, compatibly with the maps from the uncompleted rings
by `Stacks.FormalFibres.completionRingEquiv_algebraMap`. That last compatibility is exactly the
hypothesis of `Stacks.Smoothing.indSmooth_of_ringEquiv`, so ind-smoothness is moved from the
completion of `Localization.AtPrime p` to the completion of the stalk itself.

The diagram produced by `AlgebraicGeometry.exists_cofiltered_smooth_limit_presentation` lies
over `Spec Γ(S, ⊤)` rather than over `S`. The isomorphism `S ≅ Spec Γ(S, ⊤)` is absorbed into
the structure morphisms by post-composing each of them with `AlgebraicGeometry.Scheme.isoSpec`'s
inverse; smoothness survives because an isomorphism is an open immersion, hence smooth, and
smooth morphisms compose. The cone compatibility then becomes the statement
`Spec.map (S.presheaf.germ ⊤ s trivial) ≫ S.isoSpec.inv = S.fromSpecStalk s`, which is Mathlib's
`AlgebraicGeometry.Scheme.fromSpecStalk_toSpecΓ` together with
`AlgebraicGeometry.Scheme.toSpecΓ_isoSpec_inv`.

## References

* [Stacks Project, Tag 07C3](https://stacks.math.columbia.edu/tag/07C3)
* [Stacks Project, Tag 07GC](https://stacks.math.columbia.edu/tag/07GC)
* [Stacks Project, Tag 07PV](https://stacks.math.columbia.edu/tag/07PV)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits IsLocalRing

universe u

namespace AlgebraicGeometry

/-- **The completed local ring of an affine Noetherian scheme is a cofiltered limit of smooth
affine schemes over the scheme.** Let `S` be an affine Noetherian scheme and `s` a point of `S`
whose local ring is a G-ring. Then `Spec 𝒪^∧_{S, s}` is the limit of a cofiltered diagram of
affine schemes, each smooth over `S`, and the limit projections composed with the smooth
structure morphisms all agree with the canonical morphism
`Spec 𝒪^∧_{S, s} ⟶ Spec 𝒪_{S, s} ⟶ S`. -/
public theorem exists_cofiltered_smooth_limit_presentation_specCompletedStalk
    {S : Scheme.{u}} [IsAffine S] [IsNoetherian S] (s : S)
    (hG : IsGRing (S.presheaf.stalk s)) :
    ∃ (I : Type u) (_ : SmallCategory I) (_ : IsCofiltered I)
      (D : I ⥤ Scheme.{u})
      (p : D ⟶ (Functor.const I).obj S)
      (c : Cone D) (_ : IsLimit c)
      (e : Spec (CommRingCat.of (AdicCompletion (maximalIdeal (S.presheaf.stalk s))
        (S.presheaf.stalk s))) ≅ c.pt),
      (∀ i, IsAffine (D.obj i)) ∧
      (∀ i, Smooth (p.app i)) ∧
      (∀ i, e.hom ≫ c.π.app i ≫ p.app i =
        Spec.map (CommRingCat.ofHom (algebraMap (S.presheaf.stalk s)
          (AdicCompletion (maximalIdeal (S.presheaf.stalk s)) (S.presheaf.stalk s)))) ≫
        S.fromSpecStalk s) := by
  have hTop : IsAffineOpen (⊤ : S.Opens) := isAffineOpen_top S
  have hNoeth : IsNoetherianRing Γ(S, ⊤) :=
    IsLocallyNoetherian.component_noetherian ⟨⊤, hTop⟩
  let pS : PrimeSpectrum Γ(S, ⊤) := hTop.primeIdealOf ⟨s, trivial⟩
  let _ : Algebra Γ(S, ⊤) (S.presheaf.stalk s) :=
    S.presheaf.algebra_section_stalk (U := ⊤) ⟨s, trivial⟩
  have : IsLocalization.AtPrime (S.presheaf.stalk s) pS.asIdeal :=
    hTop.isLocalization_stalk ⟨s, trivial⟩
  let eS : (S.presheaf.stalk s) ≃+* Localization.AtPrime pS.asIdeal :=
    (IsLocalization.algEquiv pS.asIdeal.primeCompl (S.presheaf.stalk s)
      (Localization.AtPrime pS.asIdeal)).toRingEquiv
  have hcomm : ∀ r : Γ(S, ⊤),
      eS (algebraMap Γ(S, ⊤) (S.presheaf.stalk s) r) =
        algebraMap Γ(S, ⊤) (Localization.AtPrime pS.asIdeal) r :=
    fun r => (IsLocalization.algEquiv pS.asIdeal.primeCompl (S.presheaf.stalk s)
      (Localization.AtPrime pS.asIdeal)).commutes r
  have hGp : IsGRing (Localization.AtPrime pS.asIdeal) := by
    let _ : Algebra (S.presheaf.stalk s) (Localization.AtPrime pS.asIdeal) :=
      eS.toRingHom.toAlgebra
    have : Algebra.FiniteType (S.presheaf.stalk s) (Localization.AtPrime pS.asIdeal) :=
      RingHom.finiteType_algebraMap.mp
        (RingHom.FiniteType.of_surjective eS.toRingHom eS.surjective)
    exact isGRing_of_essFiniteType hG
  have hind := Stacks.Smoothing.indSmooth_adicCompletion_atPrime Γ(S, ⊤) pS.asIdeal hGp
  have hind' : Stacks.Smoothing.IndSmooth Γ(S, ⊤)
      (AdicCompletion (maximalIdeal (S.presheaf.stalk s)) (S.presheaf.stalk s)) := by
    refine Stacks.Smoothing.indSmooth_of_ringEquiv _ _ _ _ (RingEquiv.refl Γ(S, ⊤))
      (Stacks.FormalFibres.completionRingEquiv eS.symm) (fun r => ?_) hind
    change Stacks.FormalFibres.completionRingEquiv eS.symm
        (algebraMap (Localization.AtPrime pS.asIdeal) _
          (algebraMap Γ(S, ⊤) (Localization.AtPrime pS.asIdeal) r)) = _
    rw [Stacks.FormalFibres.completionRingEquiv_algebraMap, ← hcomm r, eS.symm_apply_apply]
    rfl
  obtain ⟨I, hI, hcof, D, pp, c, hc, e, haff, hsm, hcompat⟩ :=
    exists_cofiltered_smooth_limit_presentation hind'
  refine ⟨I, hI, hcof, D, pp ≫ (Functor.const I).map S.isoSpec.inv, c, hc, e, haff,
    fun i => ?_, fun i => ?_⟩
  · have := hsm i
    change Smooth (pp.app i ≫ S.isoSpec.inv)
    infer_instance
  · have key : Spec.map (CommRingCat.ofHom (algebraMap Γ(S, ⊤)
        (AdicCompletion (maximalIdeal (S.presheaf.stalk s)) (S.presheaf.stalk s)))) ≫
        S.isoSpec.inv =
        Spec.map (CommRingCat.ofHom (algebraMap (S.presheaf.stalk s)
          (AdicCompletion (maximalIdeal (S.presheaf.stalk s)) (S.presheaf.stalk s)))) ≫
        S.fromSpecStalk s := by
      have hfss : Spec.map (S.presheaf.germ ⊤ s trivial) ≫ S.isoSpec.inv =
          S.fromSpecStalk s := by
        rw [← Scheme.fromSpecStalk_toSpecΓ S s, Category.assoc, Scheme.toSpecΓ_isoSpec_inv,
          Category.comp_id]
      rw [← hfss, ← Category.assoc, ← Spec.map_comp]
      rfl
    change e.hom ≫ c.π.app i ≫ pp.app i ≫ S.isoSpec.inv = _
    rw [← key, ← hcompat i]
    simp only [Category.assoc]

end AlgebraicGeometry

end
