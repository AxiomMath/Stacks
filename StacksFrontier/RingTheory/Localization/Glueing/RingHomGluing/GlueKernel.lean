module

public import StacksFrontier.RingTheory.Localization.Glueing.RingHomGluing.GlueSubring
public import StacksFrontier.RingTheory.Localization.Glueing.RingHomGluing.UniformTorsion

/-!
# The kernel of the structure map of the glued ring

The structure map of the glued ring of Stacks 0EAE carries an element of the base ring to its
denominator-one image in each local piece, so an element of its kernel dies in each of those
localizations — that is, a power of each generator of the intersection annihilates it.  Over a
Noetherian ring that is enough for *one* power of the intersection to annihilate the whole kernel,
which is the kernel clause of the lemma; and if in addition each prescribed local map is injective
then the element is annihilated outside each maximal ideal as well, so it vanishes.

This file records those two clauses, together with the projection of the glued ring onto the
prescribed targets and the commuting square it forms with the structure map.

## Main definitions

* `Stacks.RingHomGluing.glueToTarget` — the projection of the glued ring to the glued target.
* `Stacks.RingHomGluing.glueToComponent` — the induced map to a prescribed target.

## Main results

* `Stacks.RingHomGluing.glueRingHom_eq_zero_pow` — an element of the kernel is annihilated by a
  power of each generator.
* `Stacks.RingHomGluing.kernelIsKilledByIdealPower_glueRingHom` — the kernel clause of Stacks
  0EAE.
* `Stacks.RingHomGluing.injective_glueRingHom` — the injectivity clause of Stacks 0EAE.
* `Stacks.RingHomGluing.glueToComponent_comp_glueRingHom` — the localization of the structure map
  is the prescribed map, as a commuting square.

## References

* [Stacks Project, Tag 0EAE](https://stacks.math.columbia.edu/tag/0EAE)
-/

@[expose] public noncomputable section

universe u v w

namespace Stacks.RingHomGluing

open CategoryTheory Cech TensorProduct FormalGlueing

section Kernel

variable {A : Type u} [CommRing A] {I : Type w} [Finite I] (m : I → Ideal A)
  [∀ i, (m i).IsMaximal] {B : I → Type v} [∀ i, CommRing (B i)]
  {T : Type max u v w} [CommRing T] [Algebra (∀ i, Localization.AtPrime (m i)) T]
  {r : ℕ} (x : Fin r → A)

attribute [local instance] localPieceRing

variable (hψ : ∀ j, Function.Bijective (transportMap (∀ i, Localization.AtPrime (m i)) x
  (baseDatum.{u, v, w} m x) (glueTarget.{u, v, w} m (T := T)) (gluePsi.{u, v, w} m x) j))

omit [Finite I] in
/-- An element of the base ring whose image in the glued ring vanishes already vanishes in the
ambient ring. -/
theorem ambientRingHom_eq_zero_of_glueRingHom_eq_zero {a : A}
    (ha : glueRingHom.{u, v, w} m x hψ a = 0) :
    ambientRingHom.{u, v, w} m x (T := T) a = 0 :=
  congrArg Subtype.val ha

omit [Finite I] in
/-- **An element of the kernel of the structure map is annihilated by a power of each
generator.** -/
theorem glueRingHom_eq_zero_pow (j : Fin r) {a : A}
    (ha : glueRingHom.{u, v, w} m x hψ a = 0) : ∃ k : ℕ, x j ^ k * a = 0 := by
  have hloc := canonicalLocalMk_isLocalized x (liftedBase.{u, max v w} A) j
  have hval := ambientRingHom_eq_zero_of_glueRingHom_eq_zero m x hψ ha
  have h0 : canonicalLocalMk x (liftedBase.{u, max v w} A) j (ULift.up a) = 0 := by
    have h2 := congrArg (fun z : T × ∀ j, restrictFromAway (R := A) x j
      (canonicalLocalPiece x (liftedBase.{u, max v w} A) j) ↦ z.2 j) hval
    simpa [ambientRingHom_snd] using h2
  obtain ⟨⟨s, hs⟩, hsa⟩ := IsLocalizedModule.exists_of_eq (S := Submonoid.powers (x j))
    (f := canonicalLocalMk x (liftedBase.{u, max v w} A) j)
    (h0.trans (map_zero (canonicalLocalMk x (liftedBase.{u, max v w} A) j)).symm)
  obtain ⟨k, rfl⟩ := hs
  exact ⟨k, by simpa [Submonoid.smul_def] using congrArg ULift.down hsa⟩

/-- **The kernel clause of Stacks 0EAE for the glued ring.** -/
theorem kernelIsKilledByIdealPower_glueRingHom [IsNoetherianRing A]
    (hx : Ideal.span (Set.range x) = ⨅ j, m j) :
    KernelIsKilledByIdealPower (glueRingHom.{u, v, w} m x hψ) (⨅ j, m j) :=
  kernelIsKilledByIdealPower_of_forall_pow m x hx (glueRingHom.{u, v, w} m x hψ)
    fun j _ ha ↦ glueRingHom_eq_zero_pow m x hψ j ha

/-! ### The projection to the prescribed targets -/

variable {f : ∀ i, Localization.AtPrime (m i) →+* B i} (ev : ∀ i, T →+* B i)

/-- The projection of the glued ring to the glued target. -/
def glueToTarget : glueSubring.{u, v, w} m x hψ →+* T :=
  (RingHom.fst T _).comp (glueSubring.{u, v, w} m x hψ).subtype

/-- The projection of the glued ring to the `i`-th prescribed target. -/
def glueToComponent (i : I) : glueSubring.{u, v, w} m x hψ →+* B i :=
  (ev i).comp (glueToTarget.{u, v, w} m x hψ)

omit [Finite I] in
/-- **The localization of the structure map is the prescribed map.** -/
theorem glueToComponent_comp_glueRingHom
    (hev : ∀ (a : ∀ i, Localization.AtPrime (m i)) (i : I),
      ev i (algebraMap (∀ i, Localization.AtPrime (m i)) T a) = f i (a i)) (i : I) :
    (glueToComponent.{u, v, w} m x hψ ev i).comp (glueRingHom.{u, v, w} m x hψ) =
      (f i).comp (algebraMap A (Localization.AtPrime (m i))) := by
  ext a
  exact hev (algebraMap A (∀ i, Localization.AtPrime (m i)) a) i

omit [Finite I] in
/-- An element of the kernel of the structure map is annihilated by an element outside each of
the maximal ideals, as soon as the prescribed map there is injective. -/
theorem glueRingHom_eq_zero_notMem
    (hev : ∀ (a : ∀ i, Localization.AtPrime (m i)) (i : I),
      ev i (algebraMap (∀ i, Localization.AtPrime (m i)) T a) = f i (a i)) (i : I)
    (hfinj : Function.Injective (f i)) {a : A}
    (ha : glueRingHom.{u, v, w} m x hψ a = 0) : ∃ s ∈ (m i).primeCompl, s * a = 0 := by
  have hcomp := glueToComponent_comp_glueRingHom m x hψ ev hev i
  have h2 : f i (algebraMap A (Localization.AtPrime (m i)) a) = 0 := by
    rw [← RingHom.comp_apply, ← hcomp, RingHom.comp_apply, ha, map_zero]
  obtain ⟨s, hs⟩ := (IsLocalization.map_eq_zero_iff (m i).primeCompl
    (Localization.AtPrime (m i)) a).1 (hfinj (h2.trans (map_zero (f i)).symm))
  exact ⟨s, s.2, hs⟩

/-- **The injectivity clause of Stacks 0EAE for the glued ring.** -/
theorem injective_glueRingHom (hx : Ideal.span (Set.range x) = ⨅ j, m j)
    (hev : ∀ (a : ∀ i, Localization.AtPrime (m i)) (i : I),
      ev i (algebraMap (∀ i, Localization.AtPrime (m i)) T a) = f i (a i))
    (hfinj : ∀ i, Function.Injective (f i)) :
    Function.Injective (glueRingHom.{u, v, w} m x hψ) :=
  injective_of_forall_pow_of_forall_notMem m x hx (glueRingHom.{u, v, w} m x hψ)
    (fun j _ ha ↦ glueRingHom_eq_zero_pow m x hψ j ha)
    fun i _ ha ↦ glueRingHom_eq_zero_notMem m x hψ ev hev i (hfinj i) ha

end Kernel

end Stacks.RingHomGluing

end
