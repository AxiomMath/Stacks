module

public import StacksFrontier.RingTheory.Localization.Glueing.RingHomGluing.Glue

/-!
# The comparison behind the glued ring

The module of compatible sections `Stacks.RingHomGluing.glueSections` is cut out of the product
of the glued target with the local pieces of the base ring by a condition comparing the image of
the generic component in the localization of the glued target with the image of the local
components under the comparison isomorphism of the transported datum.  Because the comparison
isomorphism of the transported datum is the inverse of a bijection composed with the canonical
comparison, that condition can be rewritten as an equation between the localization map of the
generic component and a single map out of a local piece.

This file constructs that map, `genericCompare`, and computes it: on the image of the base ring
it is the structure map of the glued target with denominator one, and it is semilinear for the
action of the base ring.  Those two facts determine it, because a power of `x j` carries any
element of the local piece into the image of the base ring and acts invertibly on the target.

## Main results

* `Stacks.RingHomGluing.injective_pow_smul_localizedModule` — a power of the image of `x j` acts
  injectively on the localization of the glued target.
* `Stacks.RingHomGluing.genericCompare` — the comparison of a local piece with the localized
  glued target.
* `Stacks.RingHomGluing.genericCompare_mk` — its value on the image of the base ring.
* `Stacks.RingHomGluing.genericCompare_smul` — its semilinearity over the base ring.

## Implementation notes

The universe of the glued target occurs in these statements only inside `Type max u v w`, so the
level `v` is not determined by a use site and the declarations must be applied with explicit
universes.

The local pieces of the canonical datum carry the action of the base ring restricted along
`A → A[1/x j]`, which is not the action that instance search finds on the underlying
`LocalizedModule`; statements here therefore use the `restrictFromAway` spelling throughout, and
the ring structure on that spelling is not found by instance search at all.

## References

* [Stacks Project, Tag 05ER](https://stacks.math.columbia.edu/tag/05ER)
* [Stacks Project, Tag 0EAE](https://stacks.math.columbia.edu/tag/0EAE)
-/

@[expose] public noncomputable section

universe u v w

namespace Stacks.RingHomGluing

open CategoryTheory Cech TensorProduct FormalGlueing

section Compare

variable {A : Type u} [CommRing A] {I : Type w} [Finite I] (m : I → Ideal A)
  [∀ i, (m i).IsMaximal]
  {T : Type max u v w} [CommRing T] [Algebra (∀ i, Localization.AtPrime (m i)) T]
  {r : ℕ} (x : Fin r → A)

omit [Finite I] in
/-- A power of the image of `x j` acts injectively on the localization of the glued target away
from that image. -/
theorem injective_pow_smul_localizedModule (j : Fin r) (k : ℕ) :
    Function.Injective fun z : LocalizedModule.Away
        (algebraMap A (∀ i, Localization.AtPrime (m i)) (x j)) T ↦
      algebraMap A (∀ i, Localization.AtPrime (m i)) (x j) ^ k • z := by
  have hunit := IsLocalizedModule.map_units
    (LocalizedModule.mkLinearMap
      (Submonoid.powers (algebraMap A (∀ i, Localization.AtPrime (m i)) (x j))) T)
    (⟨algebraMap A (∀ i, Localization.AtPrime (m i)) (x j) ^ k, k, rfl⟩ :
      Submonoid.powers (algebraMap A (∀ i, Localization.AtPrime (m i)) (x j)))
  have hfun : ⇑(algebraMap (∀ i, Localization.AtPrime (m i))
        (Module.End (∀ i, Localization.AtPrime (m i))
          (LocalizedModule.Away (algebraMap A (∀ i, Localization.AtPrime (m i)) (x j)) T))
        (algebraMap A (∀ i, Localization.AtPrime (m i)) (x j) ^ k)) =
      fun z ↦ algebraMap A (∀ i, Localization.AtPrime (m i)) (x j) ^ k • z := by
    ext z
    simp [Algebra.algebraMap_eq_smul_one]
  rw [Module.End.isUnit_iff, hfun] at hunit
  exact hunit.injective

/-- The comparison of the `j`-th local piece of the canonical datum of the base ring with the
localization of the glued target away from `x j`: the unit of the base change, the inverse of the
canonical comparison isomorphism, and the localization of the structure map. -/
def genericCompare (j : Fin r)
    (y : restrictFromAway (R := A) x j (canonicalLocalPiece x (liftedBase.{u, max v w} A) j)) :
    LocalizedModule.Away (algebraMap A (∀ i, Localization.AtPrime (m i)) (x j)) T :=
  transportMap (∀ i, Localization.AtPrime (m i)) x (baseDatum.{u, v, w} m x)
      (glueTarget.{u, v, w} m (T := T)) (gluePsi.{u, v, w} m x) j
    ((canonicalAlpha (∀ i, Localization.AtPrime (m i)) x (liftedBase.{u, max v w} A) j).symm
      ((1 : ∀ i, Localization.AtPrime (m i)) ⊗ₜ[A] y))

omit [Finite I] in
/-- The value of the comparison on the image of the base ring: the structure map of the glued
target, with denominator one. -/
theorem genericCompare_mk (j : Fin r) (a : ULift.{max v w} A) :
    genericCompare.{u, v, w} m x (T := T) j
        (canonicalLocalMk x (liftedBase.{u, max v w} A) j a) =
      LocalizedModule.mk (algebraMap (∀ i, Localization.AtPrime (m i)) T
        (algebraMap A (∀ i, Localization.AtPrime (m i)) a.down)) 1 := by
  have halpha : (canonicalAlpha (∀ i, Localization.AtPrime (m i)) x
        (liftedBase.{u, max v w} A) j).symm
        ((1 : ∀ i, Localization.AtPrime (m i)) ⊗ₜ[A]
          canonicalLocalMk x (liftedBase.{u, max v w} A) j a) =
      LocalizedModule.mk ((1 : ∀ i, Localization.AtPrime (m i)) ⊗ₜ[A] a) 1 := by
    rw [LinearEquiv.symm_apply_eq]
    exact (canonicalAlpha_mk (∀ i, Localization.AtPrime (m i)) x
      (liftedBase.{u, max v w} A) j 1 a).symm
  unfold genericCompare
  rw [halpha]
  refine (LocalizedModule.map_mk _ _ _ _).trans ?_
  congr 1
  rw [gluePsi_apply, glueRid_tmul]
  simp [Algebra.smul_def]

omit [Finite I] in
/-- The comparison is semilinear for the action of the base ring. -/
theorem genericCompare_smul (j : Fin r) (c : A)
    (y : restrictFromAway (R := A) x j (canonicalLocalPiece x (liftedBase.{u, max v w} A) j)) :
    genericCompare.{u, v, w} m x (T := T) j (c • y) =
      algebraMap A (∀ i, Localization.AtPrime (m i)) c •
        genericCompare.{u, v, w} m x (T := T) j y := by
  have h1 : (1 : ∀ i, Localization.AtPrime (m i)) ⊗ₜ[A] (c • y) =
      algebraMap A (∀ i, Localization.AtPrime (m i)) c •
        ((1 : ∀ i, Localization.AtPrime (m i)) ⊗ₜ[A] y) :=
    calc (1 : ∀ i, Localization.AtPrime (m i)) ⊗ₜ[A] (c • y)
        = (c • (1 : ∀ i, Localization.AtPrime (m i))) ⊗ₜ[A] y :=
          (TensorProduct.smul_tmul c (1 : ∀ i, Localization.AtPrime (m i)) y).symm
      _ = (algebraMap A (∀ i, Localization.AtPrime (m i)) c •
            (1 : ∀ i, Localization.AtPrime (m i))) ⊗ₜ[A] y := by
          rw [Algebra.smul_def, smul_eq_mul]
      _ = algebraMap A (∀ i, Localization.AtPrime (m i)) c •
            ((1 : ∀ i, Localization.AtPrime (m i)) ⊗ₜ[A] y) :=
          TensorProduct.smul_tmul' _ _ _
  unfold genericCompare
  rw [h1, map_smul]
  exact map_smul (transportMap (∀ i, Localization.AtPrime (m i)) x (baseDatum.{u, v, w} m x)
    (glueTarget.{u, v, w} m (T := T)) (gluePsi.{u, v, w} m x) j) _ _

end Compare

end Stacks.RingHomGluing

end
