module

public import StacksFrontier.Deformation.VersalRing.Uniqueness
public import StacksFrontier.RingTheory.MvPowerSeries.KrullDimension
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The ring of isomorphisms of a versal formal object

Let `ℱ` be a category cofibered in groupoids over `𝒞_Λ`, let `ξ` be a versal formal object of
`ℱ` lying over `A`, and let `B` be a Noetherian complete local `Λ`-algebra prorepresenting the
functor of isomorphisms `A|_{𝒞_Λ} ×_{ξ, ℱ, ξ} A|_{𝒞_Λ}` (the arrow functor of the groupoid in
functors of Stacks 06KY attached to `ξ`). This is the situation of Remark 0DR3. The source
projection of that groupoid is induced by a morphism `s : A ⟶ B`, and since `ξ` is versal, `s`
exhibits `B` as a power series ring over `A`. In particular `dim B = dim A + r` for the number
`r` of variables.

## Main results

* `Deformation.exists_source_isPowerSeriesOver`: the source projection of the arrow functor is
  `restrictedCoyonedaMap s` for a morphism `s : A ⟶ B` which exhibits `B` as a power series ring
  over `A`.
* `Deformation.exists_ringKrullDim_isomorphismRing_eq_add`: `dim B = dim A + r`, with `r` the
  number of power series variables of `s`.

## Implementation notes

The argument is the first half of the proof of Stacks 0DQD
(`Deformation.formallyHomotopic_of_isVersal`): versality of `ξ` makes the associated morphism
smooth, hence the groupoid of Stacks 06KY smooth (Stacks 06L1), so its source projection is
smooth; transported along the representing isomorphism it is `restrictedRepresentableMap s`,
and Stacks 06HL turns smoothness into a power series structure. The dimension is then
`MvPowerSeries.ringKrullDim_fin_eq_add`.

## References

* [Stacks Project, Tag 06HL](https://stacks.math.columbia.edu/tag/06HL)
* [Stacks Project, Tag 06KY](https://stacks.math.columbia.edu/tag/06KY)
* [Stacks Project, Tag 06L1](https://stacks.math.columbia.edu/tag/06L1)
* [Stacks Project, Tag 0DR3](https://stacks.math.columbia.edu/tag/0DR3)
-/

@[expose] public section

open CategoryTheory IsLocalRing Opposite

universe u v w u₃ v₃

namespace Deformation

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
variable {F : Type u₃} [Category.{v₃} F]

/-- **The source projection of the isomorphism functor is induced by a power series map.**
For a versal formal object `ξ` over `A` and a complete local algebra `B` prorepresenting the
arrow functor of the groupoid in functors of Stacks 06KY attached to `ξ`, the source projection
is precomposition with a morphism `s : A ⟶ B` exhibiting `B` as a power series ring over `A`. -/
@[sga "7 VI 2.11" "(ii) ⇒ (i), special case"]
theorem exists_source_isPowerSeriesOver
    (p : F ⥤ ArtinianLocalAlgCat.{u, max v v₃ w, w} Λ k)
    (hp : IsCofiberedInGroupoids p) (ξ : FormalObject p) (hξ : IsVersal hp ξ)
    (pushforwards : ChosenPushforwards p)
    (B : CompleteLocalAlgCat.{u, max v v₃ w, w} Λ k)
    (e : restrictedCoyoneda B ≅
      (presentationGroupoid p (restrictedCoyoneda ξ.base)
        (associatedMorphism hp ξ pushforwards).toBasedFunctor.toFunctor
        (associatedMorphism hp ξ pushforwards).toBasedFunctor.w hp).toGroupoidInFunctors.arrows) :
    ∃ s : ξ.base ⟶ B,
      restrictedCoyonedaMap s = natTransDown.{u, w, v₃, max v w} (e.hom ≫
        (presentationGroupoid p (restrictedCoyoneda ξ.base)
          (associatedMorphism hp ξ pushforwards).toBasedFunctor.toFunctor
          (associatedMorphism hp ξ pushforwards).toBasedFunctor.w hp).toGroupoidInFunctors.source) ∧
        IsPowerSeriesOver s := by
  let associated := associatedMorphism hp ξ pushforwards
  let U := restrictedCoyoneda ξ.base
  let G := (presentationGroupoid p U associated.toBasedFunctor.toFunctor
    associated.toBasedFunctor.w hp).toGroupoidInFunctors
  let αs := natTransDown.{u, w, v₃, max v w} (e.hom ≫ G.source)
  obtain ⟨s, hs⟩ := (restrictedCoyonedaMap_bijective ξ.base B).2 αs
  refine ⟨s, hs, (restrictedRepresentableMap_isSmooth_iff_isPowerSeriesOver s).mp ?_⟩
  have h := smooth_of_representing_iso.{u, w, v₃, max v w} e G.source
    (isSmooth_presentationGroupoid p U associated.toBasedFunctor hp (hξ pushforwards)).1
  change IsSmooth (elementsBasedFunctor αs) at h
  rwa [← hs] at h

/-- **The dimension of the ring of isomorphisms.** In the situation of
`Deformation.exists_source_isPowerSeriesOver`, `dim B = dim A + r`, where `r` is the number of
power series variables of the source map `s : A ⟶ B`. -/
theorem exists_ringKrullDim_isomorphismRing_eq_add
    (p : F ⥤ ArtinianLocalAlgCat.{u, max v v₃ w, w} Λ k)
    (hp : IsCofiberedInGroupoids p) (ξ : FormalObject p) (hξ : IsVersal hp ξ)
    (pushforwards : ChosenPushforwards p)
    (B : CompleteLocalAlgCat.{u, max v v₃ w, w} Λ k)
    (e : restrictedCoyoneda B ≅
      (presentationGroupoid p (restrictedCoyoneda ξ.base)
        (associatedMorphism hp ξ pushforwards).toBasedFunctor.toFunctor
        (associatedMorphism hp ξ pushforwards).toBasedFunctor.w hp).toGroupoidInFunctors.arrows) :
    ∃ (s : ξ.base ⟶ B) (r : ℕ),
      restrictedCoyonedaMap s = natTransDown.{u, w, v₃, max v w} (e.hom ≫
        (presentationGroupoid p (restrictedCoyoneda ξ.base)
          (associatedMorphism hp ξ pushforwards).toBasedFunctor.toFunctor
          (associatedMorphism hp ξ pushforwards).toBasedFunctor.w hp).toGroupoidInFunctors.source) ∧
        (letI : Algebra ξ.base B := s.hom.toRingHom.toAlgebra;
          Nonempty (B ≃ₐ[ξ.base] MvPowerSeries (Fin r) ξ.base)) ∧
        ringKrullDim B = ringKrullDim ξ.base + r := by
  obtain ⟨s, hs, r, ⟨eB⟩⟩ := exists_source_isPowerSeriesOver.{u, v, w, u₃, v₃} p hp ξ hξ
    pushforwards B e
  refine ⟨s, r, hs, ⟨eB⟩, ?_⟩
  let : Algebra ξ.base B := s.hom.toRingHom.toAlgebra
  rw [ringKrullDim_eq_of_ringEquiv eB.toRingEquiv]
  exact MvPowerSeries.ringKrullDim_fin_eq_add ξ.base r

end Deformation

end
