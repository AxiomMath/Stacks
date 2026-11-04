module

public import StacksFrontier.Deformation.Artin.Infinitesimal.Functoriality
public import StacksFrontier.Deformation.Artin.Obstruction.FieldBaseChangeNaturality
public import StacksFrontier.Deformation.Artin.Obstruction.FieldCohomology

/-!
# The Rim–Schlessinger comparison read on the tangent modules

Let `𝒳` be a category fibred in groupoids over the big fppf site of `S` satisfying (RS*), let
`x` be an object of `𝒳` over `Spec A`, let `A ⟶ A'` be a ring map and let `M ⟶ N` be an
`f`-semilinear bijection of coefficients. Condition (RS*) at the square
`A[M] = A ×_{A'} A'[N]` identifies the isomorphism classes of lifts of `x` over `Spec A[M]`
with those of `x|_{Spec A'}` over `Spec A'[N]`; that is
`Deformation.Artin.baseChangeLiftClassesEquiv`. This file reads that identification on the
tangent modules themselves rather than on lift classes, through the identifications
`T_x(M) = Lift(x, A[M])` carried by the tangent functor data of Stacks 07Y9, and proves it
natural in the coefficient pair.

## Main definitions

* `Deformation.Artin.tangentBaseChangeEquiv` — the comparison `T_x(M) = T_{x|_{Spec A'}}(N)`.

## Main results

* `Deformation.Artin.liftEquiv_tangentBaseChangeEquiv` — read on lift classes it is
  `Deformation.Artin.baseChangeLiftClassesEquiv`, which pins it down to the (RS*) comparison.
* `Deformation.Artin.tangentBaseChangeEquiv_map` — **naturality in the coefficient pair**: for
  module maps `φ : M ⟶ M'` over `A` and `φ' : N ⟶ N'` over `A'` compatible with the two
  semilinear comparisons, the comparison commutes with the maps the two tangent functors
  induce. Both routes around the square are, on lift classes, pullbacks of one class of lifts
  along one morphism of bases, so they agree by
  `Deformation.Artin.isPullbackOfSquareZeroLift_unique`.

## Implementation notes

The lift-class half of the naturality is
`Deformation.Artin.isPullbackOfSquareZeroLift_baseChangeLiftClassesEquiv`, stated beside
`Deformation.Artin.baseChangeLiftClassesEquiv` itself. It is separated from the tangent-module
half here only because the single-valuedness statement
`Deformation.Artin.isPullbackOfSquareZeroLift_unique` lives in
`StacksFrontier.Deformation.Artin.Infinitesimal.Functoriality`, whose import closure is several
times that of `StacksFrontier.Deformation.Artin.Obstruction.FieldCohomology`.

## References

* [Stacks Project, Tag 07YA](https://stacks.math.columbia.edu/tag/07YA)
* [Stacks Project, Tag 07Y9](https://stacks.math.columbia.edu/tag/07Y9)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u v w

namespace Deformation.Artin

section BaseChangeTangent

open CategoryTheory.Limits CategoryTheory.Functor

variable {A A' : Type u} [CommRing A] [CommRing A'] (f : A →+* A')
  (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (toS : Spec (.of A) ⟶ S) (toS' : Spec (.of A') ⟶ S)
  (hA : B.Contains (Spec (.of A))) (hA' : B.Contains (Spec (.of A')))
  (hf : Spec.map (CommRingCat.ofHom f) ≫ toS = toS')
  (M M' : SiteModule A B) (N N' : SiteModule A' B)
  (ψ : (M.obj : Type u) →+ (N.obj : Type u))
  (hψ : ∀ (a : A) (m : M.obj), ψ (a • m) = f a • ψ m)
  (ψ' : (M'.obj : Type u) →+ (N'.obj : Type u))
  (hψ' : ∀ (a : A) (m : M'.obj), ψ' (a • m) = f a • ψ' m)
  (φ : M ⟶ M') (φ' : N ⟶ N')
  (hcompat : ∀ m : (M.obj : Type u), ψ' (φ.hom.hom m) = φ'.hom.hom (ψ m))

variable {X : Type v} [Category.{w} X] (p : X ⥤ BigFppfOver B S hS)
  (hp : p.IsFiberedInGroupoids) (hRS : SatisfiesRSStar B S hS p hp)
  (hbij : Function.Bijective ψ) (hbij' : Function.Bijective ψ')
  (x : X) (hx : p.obj x = algebraOver A B S hS toS hA)

include hf in
/-- **The (RS\*) comparison, read on the tangent modules.** The Rim–Schlessinger identification
`Deformation.Artin.baseChangeLiftClassesEquiv` of lift classes, transported along the
identifications `T_x(M) = Lift(x, A[M])` of the tangent functor data of Stacks 07Y9 on both
sides: `T_x(M) = T_{x|_{Spec A'}}(N)`. -/
public def tangentBaseChangeEquiv :
    letI : p.IsFibered := hp.isFibered
    ((tangentFunctor A B S hS toS hA p x hx hp hRS).functor.obj M :
        Type max (u + 1) v w) ≃
      ((tangentFunctor A' B S hS toS' hA' p
          (((Functor.chosenPullbacks p).pullbackFunctor
            (algebraOverMapOfRingHom f B S hS toS toS' hA hA' hf)).obj ⟨x, hx⟩).1
          (((Functor.chosenPullbacks p).pullbackFunctor
            (algebraOverMapOfRingHom f B S hS toS toS' hA hA' hf)).obj ⟨x, hx⟩).2
          hp hRS).functor.obj N : Type max (u + 1) v w) :=
  let : p.IsFibered := hp.isFibered
  ((tangentFunctor A B S hS toS hA p x hx hp hRS).liftEquiv M).trans
    ((baseChangeLiftClassesEquiv f B S hS toS toS' hA hA' hf M N ψ hψ p hp hRS hbij x hx).trans
      ((tangentFunctor A' B S hS toS' hA' p _ _ hp hRS).liftEquiv N).symm)

include hf in
/-- `Deformation.Artin.tangentBaseChangeEquiv` read on lift classes is the Rim–Schlessinger
identification it was built from. This is what pins it down to the (RS\*) comparison rather
than leaving it some bijection. -/
public theorem liftEquiv_tangentBaseChangeEquiv
    (z : letI : p.IsFibered := hp.isFibered
      ((tangentFunctor A B S hS toS hA p x hx hp hRS).functor.obj M :
        Type max (u + 1) v w)) :
    letI : p.IsFibered := hp.isFibered
    (tangentFunctor A' B S hS toS' hA' p
          (((Functor.chosenPullbacks p).pullbackFunctor
            (algebraOverMapOfRingHom f B S hS toS toS' hA hA' hf)).obj ⟨x, hx⟩).1
          (((Functor.chosenPullbacks p).pullbackFunctor
            (algebraOverMapOfRingHom f B S hS toS toS' hA hA' hf)).obj ⟨x, hx⟩).2
          hp hRS).liftEquiv N
        (tangentBaseChangeEquiv f B S hS toS toS' hA hA' hf M N ψ hψ p hp hRS hbij x hx z) =
      baseChangeLiftClassesEquiv f B S hS toS toS' hA hA' hf M N ψ hψ p hp hRS hbij x hx
        ((tangentFunctor A B S hS toS hA p x hx hp hRS).liftEquiv M z) :=
  Equiv.apply_symm_apply _ _

include hf hcompat in
/-- **The (RS\*) comparison on tangent modules is natural in the coefficients.** For a pair of
module maps compatible with the two semilinear comparisons, the comparison commutes with the
maps the two tangent functors induce.

The two sides are, on lift classes, pullbacks of one class along the same morphism of bases, so
they agree by `Deformation.Artin.isPullbackOfSquareZeroLift_unique`: the relation is supplied on
one side by the tangent functor data's own `liftEquiv_natural` and on the other by
`Deformation.Artin.isPullbackOfSquareZeroLift_baseChangeLiftClassesEquiv`. -/
public theorem tangentBaseChangeEquiv_map
    (z : letI : p.IsFibered := hp.isFibered
      ((tangentFunctor A B S hS toS hA p x hx hp hRS).functor.obj M :
        Type max (u + 1) v w)) :
    letI : p.IsFibered := hp.isFibered
    tangentBaseChangeEquiv f B S hS toS toS' hA hA' hf M' N' ψ' hψ' p hp hRS hbij' x hx
        ((tangentFunctor A B S hS toS hA p x hx hp hRS).functor.map φ z) =
      (tangentFunctor A' B S hS toS' hA' p
          (((Functor.chosenPullbacks p).pullbackFunctor
            (algebraOverMapOfRingHom f B S hS toS toS' hA hA' hf)).obj ⟨x, hx⟩).1
          (((Functor.chosenPullbacks p).pullbackFunctor
            (algebraOverMapOfRingHom f B S hS toS toS' hA hA' hf)).obj ⟨x, hx⟩).2
          hp hRS).functor.map φ'
        (tangentBaseChangeEquiv f B S hS toS toS' hA hA' hf M N ψ hψ p hp hRS hbij x hx z) := by
  let : p.IsFibered := hp.isFibered
  set x₀ := ((Functor.chosenPullbacks p).pullbackFunctor
    (algebraOverMapOfRingHom f B S hS toS toS' hA hA' hf)).obj ⟨x, hx⟩ with hx₀def
  set T' := tangentFunctor A' B S hS toS' hA' p x₀.1 x₀.2 hp hRS with hT'def
  refine (T'.liftEquiv N').injective ?_
  rw [liftEquiv_tangentBaseChangeEquiv]
  refine isPullbackOfSquareZeroLift_unique A' B S hS toS' hA' p x₀.1 x₀.2 hp φ'
    (a := T'.liftEquiv N
      (tangentBaseChangeEquiv f B S hS toS toS' hA hA' hf M N ψ hψ p hp hRS hbij x hx z)) ?_ ?_
  · rw [liftEquiv_tangentBaseChangeEquiv]
    exact isPullbackOfSquareZeroLift_baseChangeLiftClassesEquiv f B S hS toS toS' hA hA' hf M M'
      N N' ψ hψ ψ' hψ' φ φ' hcompat p hp hRS hbij hbij' x hx
      ((tangentFunctor A B S hS toS hA p x hx hp hRS).liftEquiv_natural φ z)
  · exact T'.liftEquiv_natural φ' _

include hf in
/-- **The (RS\*) comparison on tangent modules is additive.** Suppose the coefficient module
`M` admits a split square in the site modules over `A` — a module `P` with two projections to
`M` and two sections, satisfying the biproduct relations — together with a semilinear
comparison `ω : P ⟶ Q` whose two projections on the `A'`-side match the two on the `A`-side
across `ψ`. Then the comparison `Deformation.Artin.tangentBaseChangeEquiv` at `(M, N, ψ)` is
additive.

This is the argument of Stacks 06I6 in the shape the two sides of the comparison force: the
source and target of the comparison are values of two *different* linear functors, on two
different categories of site modules and over two different rings, so
`Deformation.Artin.isLinearMap_of_natural_split` — which needs one category and one ring — does
not apply, and the split square is supplied here on both sides at once. The element of `T_x(P)`
with coordinates `z`, `z'` is produced from the two sections; the sum of the two projections
carries it to `z + z'`, and the three instances of
`Deformation.Artin.tangentBaseChangeEquiv_map` at the two projections and at their sum turn
that into the sum of the two comparisons. -/
public theorem tangentBaseChangeEquiv_add
    (P : SiteModule A B) (Q : SiteModule A' B)
    (ω : (P.obj : Type u) →+ (Q.obj : Type u))
    (hω : ∀ (a : A) (m : P.obj), ω (a • m) = f a • ω m)
    (hbijω : Function.Bijective ω)
    (fstP sndP : P ⟶ M) (inlP inrP : M ⟶ P) (fstQ sndQ : Q ⟶ N)
    (h₁₁ : inlP ≫ fstP = 𝟙 M) (h₂₂ : inrP ≫ sndP = 𝟙 M)
    (h₁₂ : inrP ≫ fstP = 0) (h₂₁ : inlP ≫ sndP = 0)
    (hcf : ∀ m : (P.obj : Type u), ψ (fstP.hom.hom m) = fstQ.hom.hom (ω m))
    (hcs : ∀ m : (P.obj : Type u), ψ (sndP.hom.hom m) = sndQ.hom.hom (ω m))
    (z z' : letI : p.IsFibered := hp.isFibered
      ((tangentFunctor A B S hS toS hA p x hx hp hRS).functor.obj M :
        Type max (u + 1) v w)) :
    letI : p.IsFibered := hp.isFibered
    tangentBaseChangeEquiv f B S hS toS toS' hA hA' hf M N ψ hψ p hp hRS hbij x hx (z + z') =
      tangentBaseChangeEquiv f B S hS toS toS' hA hA' hf M N ψ hψ p hp hRS hbij x hx z +
        tangentBaseChangeEquiv f B S hS toS toS' hA hA' hf M N ψ hψ p hp hRS hbij x hx z' := by
  let : p.IsFibered := hp.isFibered
  have haddP : ∀ {W : SiteModule A B} (g₁ g₂ : P ⟶ W) (m : (P.obj : Type u)),
      (g₁ + g₂).hom.hom m = g₁.hom.hom m + g₂.hom.hom m := fun _ _ _ => rfl
  have haddQ : ∀ {W : SiteModule A' B} (g₁ g₂ : Q ⟶ W) (m : (Q.obj : Type u)),
      (g₁ + g₂).hom.hom m = g₁.hom.hom m + g₂.hom.hom m := fun _ _ _ => rfl
  have hcsum : ∀ m : (P.obj : Type u),
      ψ ((fstP + sndP).hom.hom m) = (fstQ + sndQ).hom.hom (ω m) := by
    intro m
    rw [haddP, _root_.map_add, hcf, hcs, haddQ]
  have e : ∀ (a : M ⟶ P) (b : P ⟶ M) (g : M ⟶ M), a ≫ b = g → ∀ w,
      (tangentFunctor A B S hS toS hA p x hx hp hRS).functor.map b
        ((tangentFunctor A B S hS toS hA p x hx hp hRS).functor.map a w) =
        (tangentFunctor A B S hS toS hA p x hx hp hRS).functor.map g w := by
    rintro a b g rfl w
    simp
  have e₁₁ := by simpa using e inlP fstP _ h₁₁ z
  have e₁₂ := by simpa using e inrP fstP _ h₁₂ z'
  have e₂₁ := by simpa using e inlP sndP _ h₂₁ z
  have e₂₂ := by simpa using e inrP sndP _ h₂₂ z'
  obtain ⟨t, hfst, hsnd⟩ :
      ∃ t : ((tangentFunctor A B S hS toS hA p x hx hp hRS).functor.obj P :
          Type max (u + 1) v w),
        (tangentFunctor A B S hS toS hA p x hx hp hRS).functor.map fstP t = z ∧
          (tangentFunctor A B S hS toS hA p x hx hp hRS).functor.map sndP t = z' := by
    refine ⟨(tangentFunctor A B S hS toS hA p x hx hp hRS).functor.map inlP z +
      (tangentFunctor A B S hS toS hA p x hx hp hRS).functor.map inrP z', ?_, ?_⟩
    · rw [_root_.map_add, e₁₁, e₁₂, add_zero]
    · rw [_root_.map_add, e₂₁, e₂₂, zero_add]
  have hsum : (tangentFunctor A B S hS toS hA p x hx hp hRS).functor.map (fstP + sndP) t =
      z + z' := by
    rw [(tangentFunctor A B S hS toS hA p x hx hp hRS).functor.map_add]
    change (tangentFunctor A B S hS toS hA p x hx hp hRS).functor.map fstP t +
      (tangentFunctor A B S hS toS hA p x hx hp hRS).functor.map sndP t = z + z'
    rw [hfst, hsnd]
  have nfst := tangentBaseChangeEquiv_map f B S hS toS toS' hA hA' hf P M Q N ω hω ψ hψ
    fstP fstQ hcf p hp hRS hbijω hbij x hx t
  have nsnd := tangentBaseChangeEquiv_map f B S hS toS toS' hA hA' hf P M Q N ω hω ψ hψ
    sndP sndQ hcs p hp hRS hbijω hbij x hx t
  have nsum := tangentBaseChangeEquiv_map f B S hS toS toS' hA hA' hf P M Q N ω hω ψ hψ
    (fstP + sndP) (fstQ + sndQ) hcsum p hp hRS hbijω hbij x hx t
  have hga : ∀ b : ((tangentFunctor A' B S hS toS' hA' p
        (((Functor.chosenPullbacks p).pullbackFunctor
          (algebraOverMapOfRingHom f B S hS toS toS' hA hA' hf)).obj ⟨x, hx⟩).1
        (((Functor.chosenPullbacks p).pullbackFunctor
          (algebraOverMapOfRingHom f B S hS toS toS' hA hA' hf)).obj ⟨x, hx⟩).2
        hp hRS).functor.obj Q : Type max (u + 1) v w),
      (tangentFunctor A' B S hS toS' hA' p _ _ hp hRS).functor.map (fstQ + sndQ) b =
        (tangentFunctor A' B S hS toS' hA' p _ _ hp hRS).functor.map fstQ b +
          (tangentFunctor A' B S hS toS' hA' p _ _ hp hRS).functor.map sndQ b := by
    intro b
    rw [(tangentFunctor A' B S hS toS' hA' p _ _ hp hRS).functor.map_add]
    rfl
  rw [← hsum, nsum, hga, ← nfst, ← nsnd, hfst, hsnd]

end BaseChangeTangent

end Deformation.Artin

end
