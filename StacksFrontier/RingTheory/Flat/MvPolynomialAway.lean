module

public import Mathlib.RingTheory.MvPolynomial.Localization
public import Mathlib.RingTheory.RingHom.Flat
public import StacksCore.Tactic.StacksAttribute

/-!
# Flatness of a polynomial extension after inverting a constant

Let `φ : A →+* B` be a homomorphism of commutative rings and let `S` be a `B`-algebra which is
flat over `A`.  Then `B[σ]` is flat over `A[σ]` after base change to `S`, because
`S[σ] = S ⊗[A] A[σ]`; this is flat base change along `A → A[σ]`.  Taking `S` to be the
localization of `B` away from an element `g`, and using that `S[σ]` is the localization of
`B[σ]` away from the constant `g`, the conclusion reads: if `B[1/g]` is flat over `A`, then
`B[σ][1/g]` is flat over `A[σ]`.

This is the flatness statement behind the passage from a ring homomorphism to its polynomial
extension in the theory of rig-flatness, where flatness is only available after inverting a
topologically nilpotent element.

## Main results

* `MvPolynomial.flat_map_of_flat`: flatness of `A → S` gives flatness of `A[σ] → S[σ]`, in the
  form of the composite through `B[σ]`.
* `MvPolynomial.flat_away_C_of_flat_away`: flatness of `A → B[1/g]` gives flatness of
  `A[σ] → B[σ][1/C g]`.
* `MvPolynomial.flat_away_map_C_of_flat_away`: the same, with the localizing element written as
  the image of the constant `f` under the polynomial extension of `φ`.

## Implementation notes

All rings and the variable set lie in a single universe, as `RingHom.IsStableUnderBaseChange`
quantifies over four rings in one universe.  The algebra structure of `A` on `S` is the one
determined by the composite `A → B → S`, supplied by `algebraize` inside the proofs rather than
assumed, so that the statements may be instantiated at a concrete localization without the
scalar actions competing.  The `A[σ]`-algebra structure on `B[σ]` is
`MvPolynomial.algebraMvPolynomial`, which is not a global instance.

## References

* [Stacks Project, Tag 00HI](https://stacks.math.columbia.edu/tag/00HI)
* [Stacks Project, Tag 0GGM](https://stacks.math.columbia.edu/tag/0GGM)
-/

@[expose] public section

namespace MvPolynomial

section

universe u

variable {A B : Type u} [CommRing A] [CommRing B]

attribute [local instance] MvPolynomial.algebraMvPolynomial

/-- If a `B`-algebra `S` is flat over `A` along `φ`, then `S[σ]` is flat over `A[σ]`: the
polynomial algebra `S[σ]` is the base change of `S` along `A → A[σ]`. -/
public theorem flat_map_of_flat {S : Type u} [CommRing S] [Algebra B S] (φ : A →+* B)
    (σ : Type u) (h : _root_.RingHom.Flat ((algebraMap B S).comp φ)) :
    _root_.RingHom.Flat
      ((algebraMap (MvPolynomial σ B) (MvPolynomial σ S)).comp (MvPolynomial.map φ)) := by
  algebraize [(algebraMap B S).comp φ, φ]
  let _ : IsScalarTower A S (MvPolynomial σ S) := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let _ : IsScalarTower A (MvPolynomial σ A) (MvPolynomial σ S) :=
    IsScalarTower.of_algebraMap_eq fun a => (MvPolynomial.map_C (algebraMap A S) a).symm
  have heq : algebraMap (MvPolynomial σ A) (MvPolynomial σ S) =
      (algebraMap (MvPolynomial σ B) (MvPolynomial σ S)).comp (MvPolynomial.map φ) :=
    RingHom.ext fun p => (MvPolynomial.map_map φ (algebraMap B S) p).symm
  exact heq ▸ _root_.RingHom.Flat.isStableUnderBaseChange A S (MvPolynomial σ A)
    (MvPolynomial σ S) h

/-- **Flatness away from a constant passes to a polynomial extension.**  If the localization of
`B` away from `g` is flat over `A` along `φ`, then the localization of `B[σ]` away from the
constant `g` is flat over `A[σ]` along the polynomial extension of `φ`. -/
public theorem flat_away_C_of_flat_away (φ : A →+* B) (g : B) (σ : Type u)
    (h : _root_.RingHom.Flat ((algebraMap B (Localization.Away g)).comp φ)) :
    _root_.RingHom.Flat ((algebraMap (MvPolynomial σ B)
      (Localization.Away (MvPolynomial.C g : MvPolynomial σ B))).comp (MvPolynomial.map φ)) := by
  have hloc : IsLocalization (Submonoid.powers (MvPolynomial.C g : MvPolynomial σ B))
      (MvPolynomial σ (Localization.Away g)) := by
    have hm := MvPolynomial.isLocalization (σ := σ) (Submonoid.powers g) (Localization.Away g)
    rwa [Submonoid.map_powers] at hm
  let e := IsLocalization.algEquiv (Submonoid.powers (MvPolynomial.C g : MvPolynomial σ B))
    (MvPolynomial σ (Localization.Away g))
    (Localization.Away (MvPolynomial.C g : MvPolynomial σ B))
  have heq : e.toRingEquiv.toRingHom.comp
        ((algebraMap (MvPolynomial σ B) (MvPolynomial σ (Localization.Away g))).comp
          (MvPolynomial.map φ)) =
      (algebraMap (MvPolynomial σ B)
        (Localization.Away (MvPolynomial.C g : MvPolynomial σ B))).comp (MvPolynomial.map φ) :=
    RingHom.ext fun _ => e.commutes _
  exact heq ▸ (flat_map_of_flat (S := Localization.Away g) φ σ h).comp
    (_root_.RingHom.Flat.of_bijective e.bijective)

/-- The flatness clause of naive rig-flatness passes to a polynomial extension at every constant
polynomial: if `B[1/φ f]` is flat over `A`, then `B[σ]` localized away from the image of the
constant `f` is flat over `A[σ]`. -/
public theorem flat_away_map_C_of_flat_away (φ : A →+* B) (f : A) (σ : Type u)
    (h : _root_.RingHom.Flat ((algebraMap B (Localization.Away (φ f))).comp φ)) :
    _root_.RingHom.Flat ((algebraMap (MvPolynomial σ B)
        (Localization.Away (MvPolynomial.map φ (MvPolynomial.C f : MvPolynomial σ A)))).comp
      (MvPolynomial.map φ)) := by
  rw [MvPolynomial.map_C]
  exact flat_away_C_of_flat_away φ (φ f) σ h

end

end MvPolynomial

end
