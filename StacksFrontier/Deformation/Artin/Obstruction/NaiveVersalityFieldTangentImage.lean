module

public import StacksFrontier.Deformation.Artin.Obstruction.NaiveVersalityFieldArrowShape
public import StacksFrontier.Deformation.Artin.Obstruction.NaiveVersalityFieldClassEquationLift

/-!
# An extendable infinitesimal deformation is in the image of the tangent map

Let `x` be an object of a category fibred in groupoids over the big fppf site of `S` lying over
`Spec A`, let `k` be a residue field of `A`, and let `x₀` be the chosen pullback of `x` to
`Spec k`. An infinitesimal deformation of `x₀` over the dual numbers `k[k]` is a class in
`Deformation.Artin.squareZeroLiftClasses`, represented by an arrow `χ : x₀ ⟶ z` lying over the
square-zero immersion `Spec k ⟶ Spec k[k]`.

This file proves: if that representative *extends* to `x`, in the sense that there is an arrow
`b : z ⟶ x` with `χ ≫ b` the chosen restriction arrow `η : x₀ ⟶ x`, then its class is the image
of a tangent vector `θ : Ω[A⁄Λ] →ₗ[A] k` under the map on tangent spaces.

This is the whole content of the surjectivity of `Der_Λ(A, k) ⟶ T_x(k)` apart from versality
itself: versality at the point is exactly what produces the extension `b`, and no other
property of it is used.

## Main results

* `Deformation.Artin.exists_canonicalTangentMap_eq_of_extends` — an infinitesimal deformation
  of `x₀` over the dual numbers of `k` whose representative extends to `x` is the image of a
  tangent vector.

## Implementation notes

The two inputs are the classification of the dual-numbers arrows,
`Deformation.Artin.exists_unique_eq_canonicalDualNumbersArrow`, which produces the `θ` from the
arrow of the site that `b` lies over, and the class equation at an arbitrary connecting arrow,
`Deformation.Artin.canonicalFieldBaseChangeEquiv_canonicalTangentMap_of_fac`, which computes the
class once the `θ` is known. What the proof itself does is the translation between the two
descriptions of a lift: the fibre condition carried by an element of
`Deformation.Artin.squareZeroLiftClasses` is an equality of objects of a slice category, and the
class equation wants it as a pair of `CategoryTheory.Functor.IsHomLift` hypotheses, so the
equality is taken apart into its object and morphism components and reassembled through
`CategoryTheory.IsHomLift.of_fac'`.

The arrow of the site that `b` lies over is introduced together with the two properties of it
that are needed — that `b` lies over it, and that restricting it along the square-zero immersion
gives the point of `Spec A` determined by the `A`-algebra structure of `k` — rather than as a
`let`, so that neither property has to be stated about an unfolded composite of `eqToHom`s. Its
augmentation property is read off from `CategoryTheory.IsHomLift` rather than computed: the
composite of the representative with `b` is the chosen restriction arrow, which lies over both
the composite base arrow and over `Deformation.Artin.algebraOverMapOfRingHom`, and a morphism
determines the base arrow it lies over. Rewriting the composite directly is not available —
every `eqToHom` here carries the chosen pullback of `x` in its implicit arguments, and
`rewrite`'s motive for such a goal is not type-correct at `implicit` transparency.

As with the class equation, the hypotheses about the representative are stated inside the
conclusion, after the `letI` supplying `p.IsFibered`: the chosen pullback of `x` to `Spec k` is
only available once that instance is.

## References

* [Stacks Project, Tag 07YM](https://stacks.math.columbia.edu/tag/07YM)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

namespace Deformation.Artin

universe u v

/-- An equality of objects of a slice category identifies their structure morphisms, up to the
`eqToHom` of the induced equality of their codomains. -/
public theorem under_hom_comp_eqToHom {T : Type*} [Category T] {Z : T} {a b : Under Z}
    (h : a = b) : a.hom ≫ eqToHom (congrArg Comma.right h) = b.hom := by
  cases h
  simp

variable (Λ A k : Type u) [CommRing Λ] [CommRing A] [Field k] [Algebra Λ A] [Algebra A k]
  [Algebra Λ k] [IsScalarTower Λ A k]
variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (toS : Spec (.of A) ⟶ S) (hA : B.Contains (Spec (.of A))) (hAk : B.Contains (Spec (.of k)))
variable {X : Type v} [Category X] (p : X ⥤ BigFppfOver B S hS) (x : X)
  (hx : p.obj x = algebraOver A B S hS toS hA)
  (hp : p.IsFiberedInGroupoids) (hRS : SatisfiesRSStar B S hS p hp)
  (hΩ : B.Contains (Spec (squareZeroRing A (differentialsModule Λ A))))
  (hk : B.Contains (Spec (squareZeroRing A (ModuleCat.of A k))))
  (hkk : B.Contains (Spec (squareZeroRing k (ModuleCat.of k k))))
  (baseMap : Spec (.of Λ) ⟶ S)
  (baseFactorization : Spec.map (CommRingCat.ofHom (algebraMap Λ A)) ≫ baseMap = toS)

include B S hS toS hA hAk x hx hp hRS hΩ hk hkk baseMap baseFactorization in
/-- **Stacks 07YM.** Let `x₀` be the chosen pullback of `x` to `Spec k` and let `w` represent an
infinitesimal deformation of `x₀` over the dual numbers `k[k]`, that is a lift of `x₀` along the
square-zero immersion `Spec k ⟶ Spec k[k]`. If the representative extends to `x`, that is if
there is an arrow `b` from its target to `x` composing with it to the chosen restriction arrow
`η : x₀ ⟶ x`, then the class of `w` is the image of a tangent vector `θ : Ω[A⁄Λ] →ₗ[A] k` under
the map on tangent spaces, moved across the identification
`Deformation.Artin.canonicalFieldBaseChangeEquiv`.

Versality of `x` at the point is exactly what supplies the extension `b`; no other property of
it enters. The `θ` is the one attached to the arrow of the site that `b` lies over by
`Deformation.Artin.exists_unique_eq_canonicalDualNumbersArrow`, which applies because the
restriction of that arrow along the square-zero immersion is forced, by the factorization
through `η`, to be the point of `Spec A` determined by the `A`-algebra structure of `k`; the
class is then computed by
`Deformation.Artin.canonicalFieldBaseChangeEquiv_canonicalTangentMap_of_fac`. -/
@[stacks 07YM "an extendable infinitesimal deformation is in the image of the tangent map"]
public theorem exists_canonicalTangentMap_eq_of_extends [Mono baseMap] :
    letI : p.IsFibered := hp.isFibered
    ∀ (w : (Under.post p).Fiber (Under.mk (eqToHom
          (((Functor.chosenPullbacks p).pullbackFunctor
            (algebraOverMapOfRingHom (algebraMap A k) B S hS toS
              (Spec.map (CommRingCat.ofHom (algebraMap A k)) ≫ toS) hA hAk rfl)).obj ⟨x, hx⟩).2 ≫
        squareZeroArrow k B S hS (Spec.map (CommRingCat.ofHom (algebraMap A k)) ≫ toS) hAk
          (⟨ModuleCat.of k k, hkk⟩ : SiteModule k B))))
      (b : w.1.right ⟶ x),
      w.1.hom ≫ b = (Functor.chosenPullbacks p).map
          (algebraOverMapOfRingHom (algebraMap A k) B S hS toS
            (Spec.map (CommRingCat.ofHom (algebraMap A k)) ≫ toS) hA hAk rfl) ⟨x, hx⟩ →
        ∃ θ : Ω[A⁄Λ] →ₗ[A] k,
          canonicalFieldBaseChangeEquiv A k B S hS toS hA p x hx hp hRS hk hAk hkk
              ((tangentFunctor A B S hS toS hA p x hx hp hRS).liftEquiv
                (⟨ModuleCat.of A k, hk⟩ : SiteModule A B)
                (canonicalTangentMap Λ A k B S hS toS hA p x hx hp hRS hΩ hk baseMap
                  baseFactorization θ)) =
            Quotient.mk _ w := by
  let : p.IsFibered := hp.isFibered
  intro w b hfac
  have hx₀ := (((Functor.chosenPullbacks p).pullbackFunctor
    (algebraOverMapOfRingHom (algebraMap A k) B S hS toS
      (Spec.map (CommRingCat.ofHom (algebraMap A k)) ≫ toS) hA hAk rfl)).obj ⟨x, hx⟩).2
  have hright : p.obj w.1.right =
      squareZeroOver k B S hS (Spec.map (CommRingCat.ofHom (algebraMap A k)) ≫ toS)
        (⟨ModuleCat.of k k, hkk⟩ : SiteModule k B) :=
    congrArg Comma.right w.2
  have hhom : p.map w.1.hom ≫ eqToHom hright =
      eqToHom hx₀ ≫ squareZeroArrow k B S hS
        (Spec.map (CommRingCat.ofHom (algebraMap A k)) ≫ toS) hAk
        (⟨ModuleCat.of k k, hkk⟩ : SiteModule k B) :=
    under_hom_comp_eqToHom w.2
  -- The representative lies over the square-zero immersion.
  have hwlift : p.IsHomLift
      (squareZeroArrow k B S hS (Spec.map (CommRingCat.ofHom (algebraMap A k)) ≫ toS) hAk
        (⟨ModuleCat.of k k, hkk⟩ : SiteModule k B)) w.1.hom := by
    refine IsHomLift.of_fac' p _ w.1.hom hx₀ hright ?_
    calc p.map w.1.hom = (p.map w.1.hom ≫ eqToHom hright) ≫ eqToHom hright.symm := by simp
      _ = (eqToHom hx₀ ≫ squareZeroArrow k B S hS
            (Spec.map (CommRingCat.ofHom (algebraMap A k)) ≫ toS) hAk
            (⟨ModuleCat.of k k, hkk⟩ : SiteModule k B)) ≫ eqToHom hright.symm :=
          congrArg (fun t => t ≫ eqToHom hright.symm) hhom
      _ = eqToHom hx₀ ≫ squareZeroArrow k B S hS
            (Spec.map (CommRingCat.ofHom (algebraMap A k)) ≫ toS) hAk
            (⟨ModuleCat.of k k, hkk⟩ : SiteModule k B) ≫ eqToHom hright.symm :=
          Category.assoc _ _ _
  -- The chosen restriction arrow lies over `algebraOverMapOfRingHom`.
  have hηlift : p.IsHomLift
      (algebraOverMapOfRingHom (algebraMap A k) B S hS toS
        (Spec.map (CommRingCat.ofHom (algebraMap A k)) ≫ toS) hA hAk rfl)
      ((Functor.chosenPullbacks p).map
        (algebraOverMapOfRingHom (algebraMap A k) B S hS toS
          (Spec.map (CommRingCat.ofHom (algebraMap A k)) ≫ toS) hA hAk rfl) ⟨x, hx⟩) :=
    ((Functor.chosenPullbacks p).isStronglyCartesian
      (algebraOverMapOfRingHom (algebraMap A k) B S hS toS
        (Spec.map (CommRingCat.ofHom (algebraMap A k)) ≫ toS) hA hAk rfl)
      ⟨x, hx⟩).toIsHomLift
  -- The arrow of the site that `b` lies over, with its augmentation property.
  obtain ⟨ν, hνb, hν⟩ : ∃ ν : squareZeroOver k B S hS
      (Spec.map (CommRingCat.ofHom (algebraMap A k)) ≫ toS)
      (⟨ModuleCat.of k k, hkk⟩ : SiteModule k B) ⟶ algebraOver A B S hS toS hA,
      p.IsHomLift ν b ∧
        squareZeroArrow k B S hS (Spec.map (CommRingCat.ofHom (algebraMap A k)) ≫ toS) hAk
            (⟨ModuleCat.of k k, hkk⟩ : SiteModule k B) ≫ ν =
          algebraOverMapOfRingHom (algebraMap A k) B S hS toS
            (Spec.map (CommRingCat.ofHom (algebraMap A k)) ≫ toS) hA hAk rfl := by
    refine ⟨eqToHom hright.symm ≫ p.map b ≫ eqToHom hx, ?_, ?_⟩
    · exact IsHomLift.of_fac' p _ b hright hx (by simp)
    · have := hwlift
      have hνb : p.IsHomLift (eqToHom hright.symm ≫ p.map b ≫ eqToHom hx) b :=
        IsHomLift.of_fac' p _ b hright hx (by simp)
      have := hηlift
      have hcomp : p.IsHomLift
          (squareZeroArrow k B S hS (Spec.map (CommRingCat.ofHom (algebraMap A k)) ≫ toS) hAk
              (⟨ModuleCat.of k k, hkk⟩ : SiteModule k B) ≫
            (eqToHom hright.symm ≫ p.map b ≫ eqToHom hx))
          ((Functor.chosenPullbacks p).map
            (algebraOverMapOfRingHom (algebraMap A k) B S hS toS
              (Spec.map (CommRingCat.ofHom (algebraMap A k)) ≫ toS) hA hAk rfl) ⟨x, hx⟩) :=
        hfac ▸ (inferInstance : p.IsHomLift
          (squareZeroArrow k B S hS (Spec.map (CommRingCat.ofHom (algebraMap A k)) ≫ toS) hAk
              (⟨ModuleCat.of k k, hkk⟩ : SiteModule k B) ≫
            (eqToHom hright.symm ≫ p.map b ≫ eqToHom hx)) (w.1.hom ≫ b))
      exact (IsHomLift.fac p _ ((Functor.chosenPullbacks p).map
          (algebraOverMapOfRingHom (algebraMap A k) B S hS toS
            (Spec.map (CommRingCat.ofHom (algebraMap A k)) ≫ toS) hA hAk rfl) ⟨x, hx⟩)).trans
        (IsHomLift.fac p _ ((Functor.chosenPullbacks p).map
          (algebraOverMapOfRingHom (algebraMap A k) B S hS toS
            (Spec.map (CommRingCat.ofHom (algebraMap A k)) ≫ toS) hA hAk rfl) ⟨x, hx⟩)).symm
  -- The tangent vector attached to that arrow.
  obtain ⟨θ, hθ, -⟩ := exists_unique_eq_canonicalDualNumbersArrow Λ A k B S hS toS hA hAk p x hx
    hp hRS hΩ hkk baseMap baseFactorization ν hν
  refine ⟨θ, ?_⟩
  have hbθ : p.IsHomLift
      (canonicalDualNumbersArrow Λ A k B S hS toS hA p x hx hp hRS hΩ hkk baseMap
        baseFactorization θ) b := hθ ▸ hνb
  refine (canonicalFieldBaseChangeEquiv_canonicalTangentMap_of_fac Λ A k B S hS toS hA hAk p x hx
    hp hRS hΩ hk hkk baseMap baseFactorization θ w.1.right b hbθ w.1.hom hwlift hfac
    w.2).trans (congrArg (Quotient.mk _) ?_)
  exact Subtype.ext rfl

end Deformation.Artin
