module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Topology.Algebra.AdicTopology.CompletedTensorProduct.Quotient

/-!
# Right exactness of the completed tensor product along an arbitrary surjection

`TopologicalRing.exists_completedTensorProductQuotientRingEquiv` identifies `B ⊗̂[A] C` with the
quotient of `B ⊗̂[A] R` by the closure of the extension of `ker (id ⊗ π)`, for a continuous open
surjection `π : R ↠ C`.  Two things stand between that and the form the third paragraph of
Tag 0GGR needs, and both are supplied here.

First, the ideal: `ker (id ⊗ π)` is the extension of `ker π` to `B ⊗[A] R`.  Tag 0AMZ's
`TopologicalRing.ker_tensorProduct_map_quotientMk` says this when `π` is a quotient map
`R → R ⧸ K`; an arbitrary surjection factors through its own quotient map by an isomorphism,
and tensoring with `B` keeps that isomorphism injective, so the kernel does not change.

Second, the closure: it may be dropped as soon as every ideal of `B ⊗̂[A] R` is closed, which
holds when that ring is Noetherian, adic, complete and separated
(`TopologicalRing.isClosed_ideal_of_isAdic_of_isNoetherianRing`).

## Main results

* `Ideal.closure_eq_of_isAdic_of_isNoetherianRing`: the closure of an ideal is itself in a
  Noetherian adic complete separated ring.
* `TopologicalRing.ker_tensorProduct_map_of_surjective`: `ker (id ⊗ π) = (ker π) · (B ⊗[A] R)`
  for any surjective `π`.

## References

* [Stacks Project, Tag 0GGR](https://stacks.math.columbia.edu/tag/0GGR)
* [Stacks Project, Tag 0AMZ](https://stacks.math.columbia.edu/tag/0AMZ)
-/

@[expose] public section

/-- **The closure of an ideal is itself in a Noetherian ring which is adic, complete and
separated.**  This is `TopologicalRing.isClosed_ideal_of_isAdic_of_isNoetherianRing` in the form
that removes the closure from the right-exactness statements for the completed tensor
product. -/
@[sga "3 VIIB 5.5.2" "partial"]
public theorem Ideal.closure_eq_of_isAdic_of_isNoetherianRing {S : Type*} [CommRing S]
    [UniformSpace S] [IsUniformAddGroup S] [IsTopologicalRing S] [IsLinearTopology S S]
    [IsNoetherianRing S] [CompleteSpace S] [T2Space S]
    {𝔦 : Ideal S} (h𝔦 : _root_.IsAdic 𝔦) (𝔞 : Ideal S) : Ideal.closure 𝔞 = 𝔞 :=
  SetLike.coe_injective
    (TopologicalRing.isClosed_ideal_of_isAdic_of_isNoetherianRing h𝔦 𝔞).closure_eq

namespace TopologicalRing

section

open scoped TensorProduct

variable {A B R C : Type*} [CommRing A] [CommRing B] [CommRing R] [CommRing C]
  [Algebra A B] [Algebra A R] [Algebra A C]

/-- The kernel of a composite whose outer factor is injective is the kernel of the inner
factor. -/
private theorem ker_comp_of_injective {X Y Z : Type*} [CommRing X] [CommRing Y] [CommRing Z]
    (f : X →+* Y) (g : Y →+* Z) (hg : Function.Injective g) :
    RingHom.ker (g.comp f) = RingHom.ker f := by
  ext x
  simp only [RingHom.mem_ker, RingHom.comp_apply]
  exact ⟨fun h => hg (by rw [h, map_zero]), fun h => by rw [h, map_zero]⟩

variable [TopologicalSpace B] [IsTopologicalRing B] [IsLinearTopology B B]
  [TopologicalSpace R] [IsTopologicalRing R] [IsLinearTopology R R]
  [TopologicalSpace C] [IsTopologicalRing C] [IsLinearTopology C C]

/-- **The kernel of `id ⊗ π` is the extension of `ker π`, for an arbitrary surjection.**
Tag 0AMZ's `TopologicalRing.ker_tensorProduct_map_quotientMk` is the case of a quotient map; a
general surjective `π : R ↠ C` is its own quotient map followed by an isomorphism, and
tensoring an isomorphism with `B` leaves an injection, so the kernel is unchanged. -/
public theorem ker_tensorProduct_map_of_surjective (π : R →ₐ[A] C)
    (hsurj : Function.Surjective π) :
    RingHom.ker (Algebra.TensorProduct.map (AlgHom.id A B) π).toRingHom =
      (RingHom.ker (π : R →+* C)).map
        (Algebra.TensorProduct.includeRight : R →ₐ[A] B ⊗[A] R).toRingHom := by
  set K : Ideal R := RingHom.ker (π : R →+* C)
  set ε : (R ⧸ K) ≃+* C := RingHom.quotientKerEquivOfSurjective hsurj
  have hεmk : ∀ r : R, ε (Ideal.Quotient.mk K r) = π r :=
    RingHom.quotientKerEquivOfSurjective_apply_mk hsurj
  let εA : (R ⧸ K) ≃ₐ[A] C :=
    AlgEquiv.ofRingEquiv (f := ε) fun a => (hεmk (algebraMap A R a)).trans (π.commutes a)
  have hinj : Function.Injective
      (Algebra.TensorProduct.map (AlgHom.id A B) (εA : (R ⧸ K) →ₐ[A] C)).toRingHom :=
    (Algebra.TensorProduct.congr AlgEquiv.refl εA).injective
  have hfac : (Algebra.TensorProduct.map (AlgHom.id A B) π).toRingHom =
      (Algebra.TensorProduct.map (AlgHom.id A B) (εA : (R ⧸ K) →ₐ[A] C)).toRingHom.comp
        (Algebra.TensorProduct.map (AlgHom.id A B) (Ideal.Quotient.mkₐ A K)).toRingHom := by
    refine RingHom.ext fun z => ?_
    induction z with
    | zero => rw [map_zero, RingHom.comp_apply, map_zero, map_zero]
    | tmul b r => exact congrArg (b ⊗ₜ[A] ·) (hεmk r).symm
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  rw [hfac, ker_comp_of_injective _ _ hinj, ker_tensorProduct_map_quotientMk K]

end

end TopologicalRing

end
