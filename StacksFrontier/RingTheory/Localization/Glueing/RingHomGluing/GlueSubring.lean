module

public import StacksFrontier.RingTheory.Localization.Glueing.RingHomGluing.OverlapRing

/-!
# The glued ring

The module of compatible sections of the glueing datum of Stacks 0EAE is cut out of the product
of the glued target with the local pieces of the base ring by two conditions, one comparing the
generic component with each local component and one comparing two local components on an overlap.
Rewritten through the comparison maps of the two preceding files, both conditions become equations
between ring maps out of a local piece — so the module of compatible sections is a *subring* of
that product, and the base ring maps into it.

## Main definitions

* `Stacks.RingHomGluing.glueSubring` — the module of compatible sections, as a subring.
* `Stacks.RingHomGluing.glueRingHom` — the structure map of the base ring into it.

## Main results

* `Stacks.RingHomGluing.mem_glueSections_iff` — membership in the module of compatible sections,
  as two equations between ring maps.
* `Stacks.RingHomGluing.glueSubring_coe` — the underlying set of the subring is the module of
  compatible sections, so the two carry the same elements.
* `Stacks.RingHomGluing.glueRingHom_coe_fst` and `Stacks.RingHomGluing.glueRingHom_coe_snd` —
  the two components of the structure map.

## Implementation notes

The ring structure of a local piece is not found by instance search and is supplied by the local
instance `Stacks.RingHomGluing.localPieceRing`; the universe of the lift is determined by the
glued target, so the declarations here must be applied with explicit universes.

## References

* [Stacks Project, Tag 05ER](https://stacks.math.columbia.edu/tag/05ER)
* [Stacks Project, Tag 0EAE](https://stacks.math.columbia.edu/tag/0EAE)
-/

@[expose] public noncomputable section

universe u v w

namespace Stacks.RingHomGluing

open CategoryTheory Cech TensorProduct FormalGlueing

section Subring

variable {A : Type u} [CommRing A] {I : Type w} [Finite I] (m : I → Ideal A)
  [∀ i, (m i).IsMaximal]
  {T : Type max u v w} [CommRing T] [Algebra (∀ i, Localization.AtPrime (m i)) T]
  {r : ℕ} (x : Fin r → A)

attribute [local instance] localPieceRing

/-- The denominator-one map of the glued target into its localization away from `x j`. -/
abbrev genericMk (j : Fin r) (s : T) :
    LocalizedModule.Away (algebraMap A (∀ i, Localization.AtPrime (m i)) (x j)) T :=
  LocalizedModule.mk s 1

/-- The structure map of the base ring into the ambient ring of the glued datum. -/
def ambientRingHom : A →+* T × ∀ j, restrictFromAway (R := A) x j
    (canonicalLocalPiece x (liftedBase.{u, max v w} A) j) :=
  (((algebraMap (∀ i, Localization.AtPrime (m i)) T).comp
    (algebraMap A (∀ i, Localization.AtPrime (m i)))).prod
      (RingHom.pi fun j ↦ localPieceRingHom x j))

omit [Finite I] in
/-- The generic component of the structure map into the ambient ring. -/
theorem ambientRingHom_fst (a : A) :
    (ambientRingHom.{u, v, w} m x (T := T) a).1 =
      algebraMap (∀ i, Localization.AtPrime (m i)) T
        (algebraMap A (∀ i, Localization.AtPrime (m i)) a) := rfl

omit [Finite I] in
/-- The local components of the structure map into the ambient ring. -/
theorem ambientRingHom_snd (a : A) (j : Fin r) :
    (ambientRingHom.{u, v, w} m x (T := T) a).2 j =
      canonicalLocalMk x (liftedBase.{u, max v w} A) j (ULift.up a) := rfl

variable (hψ : ∀ j, Function.Bijective (transportMap (∀ i, Localization.AtPrime (m i)) x
  (baseDatum.{u, v, w} m x) (glueTarget.{u, v, w} m (T := T)) (gluePsi.{u, v, w} m x) j))

omit [Finite I] in
/-- The generic/local condition of the transported datum is the equation between the
denominator-one image of the generic component and the comparison of the local component. -/
theorem transportAlpha_mk_eq_iff (j : Fin r) (s : T)
    (y : restrictFromAway (R := A) x j (canonicalLocalPiece x (liftedBase.{u, max v w} A) j)) :
    transportAlpha (∀ i, Localization.AtPrime (m i)) x (baseDatum.{u, v, w} m x)
          (glueTarget.{u, v, w} m (T := T)) (gluePsi.{u, v, w} m x) hψ j
          (LocalizedModule.mkLinearMap (Submonoid.powers
            (algebraMap A (∀ i, Localization.AtPrime (m i)) (x j))) _ s) =
        (TensorProduct.mk A (∀ i, Localization.AtPrime (m i)) _) 1 y ↔
      genericMk.{u, v, w} m x j s = genericCompare.{u, v, w} m x (T := T) j y := by
  rw [transportAlpha_apply]
  exact Iff.trans (Iff.symm (LinearEquiv.eq_symm_apply _)) (LinearEquiv.symm_apply_eq _)

omit [Finite I] in
/-- **Membership in the module of compatible sections**, as two equations between ring maps out
of the local pieces. -/
theorem mem_glueSections_iff (z : T × ∀ j, restrictFromAway (R := A) x j
    (canonicalLocalPiece x (liftedBase.{u, max v w} A) j)) :
    z ∈ glueSections.{u, v, w} m x hψ ↔
      (∀ j, genericMk.{u, v, w} m x j z.1 =
          genericCompare.{u, v, w} m x (T := T) j (z.2 j)) ∧
        ∀ j k, overlapMkLeft x j k (z.2 j) = overlapMkRight x j k (z.2 k) :=
  and_congr (forall_congr' fun j ↦ transportAlpha_mk_eq_iff m x hψ j z.1 (z.2 j))
    (forall₂_congr fun j k ↦ canonicalAlphaIJ_mk_eq_iff x j k (z.2 j) (z.2 k))

/-- **The glued ring.**  The module of compatible sections of the glued datum is a subring of the
product of the glued target with the local pieces of the base ring. -/
def glueSubring : Subring (T × ∀ j, restrictFromAway (R := A) x j
    (canonicalLocalPiece x (liftedBase.{u, max v w} A) j)) where
  carrier := {z | z ∈ glueSections.{u, v, w} m x hψ}
  mul_mem' := by
    intro z z' hz0 hz0'
    have hz := (mem_glueSections_iff m x hψ z).1 hz0
    have hz' := (mem_glueSections_iff m x hψ z').1 hz0'
    refine (mem_glueSections_iff m x hψ (z * z')).2 ⟨fun j ↦ ?_, fun j k ↦ ?_⟩
    · rw [show (z * z').1 = z.1 * z'.1 from rfl, show (z * z').2 j = z.2 j * z'.2 j from rfl,
        genericCompare_mul, ← hz.1 j, ← hz'.1 j]
      exact (localizedModule_mk_one_mul (Submonoid.powers
        (algebraMap A (∀ i, Localization.AtPrime (m i)) (x j))) z.1 z'.1).symm
    · rw [show (z * z').2 j = z.2 j * z'.2 j from rfl,
        show (z * z').2 k = z.2 k * z'.2 k from rfl, overlapMkLeft_mul, overlapMkRight_mul,
        hz.2 j k, hz'.2 j k]
  one_mem' := by
    refine (mem_glueSections_iff m x hψ 1).2 ⟨fun j ↦ ?_, fun j k ↦ ?_⟩
    · rw [show (1 : T × ∀ j, restrictFromAway (R := A) x j
          (canonicalLocalPiece x (liftedBase.{u, max v w} A) j)).1 = 1 from rfl,
        show (1 : T × ∀ j, restrictFromAway (R := A) x j
          (canonicalLocalPiece x (liftedBase.{u, max v w} A) j)).2 j = 1 from rfl,
        genericCompare_one]
      exact localizedModule_mk_one_one (Submonoid.powers
        (algebraMap A (∀ i, Localization.AtPrime (m i)) (x j)))
    · rw [show (1 : T × ∀ j, restrictFromAway (R := A) x j
          (canonicalLocalPiece x (liftedBase.{u, max v w} A) j)).2 j = 1 from rfl,
        show (1 : T × ∀ j, restrictFromAway (R := A) x j
          (canonicalLocalPiece x (liftedBase.{u, max v w} A) j)).2 k = 1 from rfl,
        overlapMkLeft_one, overlapMkRight_one]
  add_mem' := fun hz hz' ↦ (glueSections.{u, v, w} m x hψ).add_mem hz hz'
  zero_mem' := (glueSections.{u, v, w} m x hψ).zero_mem
  neg_mem' := fun hz ↦ (glueSections.{u, v, w} m x hψ).neg_mem hz

omit [Finite I] in
/-- The subring and the module of compatible sections have the same elements. -/
theorem glueSubring_coe :
    (glueSubring.{u, v, w} m x hψ : Set (T × ∀ j, restrictFromAway (R := A) x j
      (canonicalLocalPiece x (liftedBase.{u, max v w} A) j))) =
      {z | z ∈ glueSections.{u, v, w} m x hψ} := rfl

omit [Finite I] in
/-- The image of an element of the base ring is a compatible section. -/
theorem ambientRingHom_mem (a : A) :
    ambientRingHom.{u, v, w} m x (T := T) a ∈ glueSubring.{u, v, w} m x hψ := by
  refine (mem_glueSections_iff m x hψ _).2 ⟨fun j ↦ ?_, fun j k ↦ ?_⟩
  · rw [ambientRingHom_fst, ambientRingHom_snd, genericCompare_mk]
  · rw [ambientRingHom_snd, ambientRingHom_snd, overlapMkLeft_apply_mk,
      overlapMkRight_apply_mk]

/-- **The structure map of the glued ring.** -/
def glueRingHom : A →+* glueSubring.{u, v, w} m x hψ :=
  (ambientRingHom.{u, v, w} m x).codRestrict (glueSubring.{u, v, w} m x hψ)
    (ambientRingHom_mem m x hψ)

omit [Finite I] in
/-- The generic component of the structure map of the glued ring. -/
theorem glueRingHom_coe_fst (a : A) :
    ((glueRingHom.{u, v, w} m x hψ a : T × ∀ j, restrictFromAway (R := A) x j
        (canonicalLocalPiece x (liftedBase.{u, max v w} A) j))).1 =
      algebraMap (∀ i, Localization.AtPrime (m i)) T
        (algebraMap A (∀ i, Localization.AtPrime (m i)) a) := rfl

omit [Finite I] in
/-- The local components of the structure map of the glued ring. -/
theorem glueRingHom_coe_snd (a : A) (j : Fin r) :
    ((glueRingHom.{u, v, w} m x hψ a : T × ∀ j, restrictFromAway (R := A) x j
        (canonicalLocalPiece x (liftedBase.{u, max v w} A) j))).2 j =
      canonicalLocalMk x (liftedBase.{u, max v w} A) j (ULift.up a) := rfl

end Subring

end Stacks.RingHomGluing

end
