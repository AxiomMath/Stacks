module

public import StacksFrontier.AlgebraicGeometry.ProEtale.IndZariski.LocalIsomorphism
public import StacksFrontier.AlgebraicGeometry.Morphisms.RingMapProperty.LocalRingIso
public import Mathlib.RingTheory.TensorProduct.Maps
public import StacksCore.Tactic.StacksAttribute

/-!
# Base change of local isomorphisms

Both halves of the local-isomorphism notion are stable under base change. If `A → B` is a
local isomorphism, then so is `A' → A' ⊗[A] B` for every `A`-algebra `A'`; and if `A → B`
identifies local rings, then so does `A' → A' ⊗[A] B`.

## Main results

* `AlgebraicGeometry.ProEtale.identifiesLocalRings_tensorProduct`: identifying local rings is
  stable under base change.
* `Algebra.IsLocalIso.instTensorProduct`: being a local isomorphism is stable under base change.

## Implementation notes

The tensor factors are ordered with the new base ring first, as in Mathlib's algebra structure
on a tensor product. Tensor symmetry identifies this with the tensor product in the opposite
order used in the source.

Stability of the local-ring condition under base change is available for ring maps between rings
in a single universe. The three auxiliary lemmas below transport the condition along ring
isomorphisms with no universe constraint, which is what lets the single-universe statement be
applied to `A`, `B` and `A'` lying in three different universes.

## References

* [Stacks Project, Tag 096F](https://stacks.math.columbia.edu/tag/096F)
-/

@[expose] public section

open scoped TensorProduct

namespace AlgebraicGeometry.ProEtale

universe uA uB uA'

/-- A ring homomorphism induces an isomorphism on the local rings at every prime of its target.
This is `RingHom.LocalRingIso` with the source and target in independent universes. -/
private abbrev HasIsomorphicLocalRings {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) : Prop :=
  ∀ (q : Ideal S) [q.IsPrime],
    Function.Bijective (Localization.localRingHom (Ideal.comap f q) q f rfl)

/-- A ring isomorphism satisfies the local-ring condition. -/
private theorem hasIsomorphicLocalRings_ringEquiv {R S : Type*} [CommRing R] [CommRing S]
    (e : R ≃+* S) : HasIsomorphicLocalRings (e : R →+* S) := fun q _ =>
  (Localization.localRingEquiv (Ideal.comap (e : R →+* S) q) q e rfl).bijective

/-- The local-ring condition is stable under composition. -/
private theorem hasIsomorphicLocalRings_comp {R S T : Type*} [CommRing R] [CommRing S]
    [CommRing T] {f : R →+* S} {g : S →+* T} (hf : HasIsomorphicLocalRings f)
    (hg : HasIsomorphicLocalRings g) : HasIsomorphicLocalRings (g.comp f) := by
  intro q hq
  let p := Ideal.comap g q
  let : p.IsPrime := Ideal.comap_isPrime g q
  have hI : Ideal.comap (g.comp f) q = p.comap f := (Ideal.comap_comap f g).symm
  have hcomp : Localization.localRingHom (Ideal.comap (g.comp f) q) q (g.comp f) hI =
      (Localization.localRingHom p q g rfl).comp
      (Localization.localRingHom (Ideal.comap f p) p f rfl) :=
    Localization.localRingHom_comp (I := Ideal.comap (g.comp f) q) p q f hI g rfl
  exact (congrArg (fun g : _ →+* _ => (g : _ → _)) hcomp).symm ▸ (hg q).comp (hf p)

/-- The local-ring condition transports across a commuting square whose vertical maps are
ring isomorphisms. -/
private theorem hasIsomorphicLocalRings_congr
    {R S R' S' : Type*} [CommRing R] [CommRing S] [CommRing R'] [CommRing S']
    (f : R →+* S) (g : R' →+* S') (eR : R ≃+* R') (eS : S ≃+* S')
    (hfg : g.comp eR.toRingHom = eS.toRingHom.comp f)
    (hf : HasIsomorphicLocalRings f) : HasIsomorphicLocalRings g := by
  have h₂ : HasIsomorphicLocalRings ((eS.toRingHom.comp f).comp eR.symm.toRingHom) :=
    hasIsomorphicLocalRings_comp (hasIsomorphicLocalRings_ringEquiv eR.symm)
      (hasIsomorphicLocalRings_comp hf (hasIsomorphicLocalRings_ringEquiv eS))
  have heq : g = (eS.toRingHom.comp f).comp eR.symm.toRingHom := by
    ext x
    simpa [RingHom.comp_apply] using congrArg (fun k : R →+* S' => k (eR.symm x)) hfg
  simpa only [heq] using h₂

/-- Base change of the local-ring condition, with the three rings in arbitrary universes. -/
private theorem identifiesLocalRings_tensorProduct_general (A : Type uA) (B : Type uB)
    (A' : Type uA') [CommRing A] [CommRing B] [CommRing A'] [Algebra A B] [Algebra A A']
    (h : Algebra.IdentifiesLocalRings A B) :
    Algebra.IdentifiesLocalRings A' (A' ⊗[A] B) := by
  let : Algebra (ULift.{max (max uA uB) uA'} A) (ULift.{max (max uA uB) uA'} B) :=
    ULift.algebra' A (ULift.{max (max uA uB) uA'} B)
  let : Algebra (ULift.{max (max uA uB) uA'} A) (ULift.{max (max uA uB) uA'} A') :=
    ULift.algebra' A (ULift.{max (max uA uB) uA'} A')
  let eA : A ≃+* ULift.{max (max uA uB) uA'} A := ULift.ringEquiv.symm
  let eB : B ≃+* ULift.{max (max uA uB) uA'} B := ULift.ringEquiv.symm
  have hLift : Algebra.IdentifiesLocalRings (ULift.{max (max uA uB) uA'} A)
      (ULift.{max (max uA uB) uA'} B) :=
    hasIsomorphicLocalRings_congr (algebraMap A B)
      (RingHom.ulift.{max (max uA uB) uA', max (max uA uB) uA'} (algebraMap A B)) eA eB
      (by ext x; rfl) h
  have hLifted := RingHom.localRingHom_bijective_isStableUnderBaseChange
    |>.tensorProduct (R := ULift.{max (max uA uB) uA'} A)
      (S := ULift.{max (max uA uB) uA'} B) (ULift.{max (max uA uB) uA'} A') hLift
  let eTensor := Algebra.TensorProduct.uliftEquiv.{max (max uA uB) uA', max (max uA uB) uA',
    max (max uA uB) uA', max (max uA uB) uA'} A A' A' B
  let eTarget : (A' ⊗[A] B) ≃+* (ULift.{max (max uA uB) uA'} A' ⊗[ULift.{max (max uA uB) uA'} A]
      ULift.{max (max uA uB) uA'} B) := ULift.ringEquiv.symm.trans eTensor.toRingEquiv
  refine hasIsomorphicLocalRings_congr
    (algebraMap (ULift.{max (max uA uB) uA'} A')
      (ULift.{max (max uA uB) uA'} A' ⊗[ULift.{max (max uA uB) uA'} A]
        ULift.{max (max uA uB) uA'} B))
    (algebraMap A' (A' ⊗[A] B)) ULift.ringEquiv eTarget.symm ?_ hLifted
  ext x
  show x.down ⊗ₜ[A] (1 : B) =
    (eTensor.symm (x ⊗ₜ[ULift.{max (max uA uB) uA'} A]
      (1 : ULift.{max (max uA uB) uA'} B))).down
  rw [Algebra.TensorProduct.down_uliftEquiv_symm_tmul]
  rfl

/-- **Stacks Project, Tag 096F.** Base change preserves the property of identifying local
rings. -/
@[stacks 096F "identifies_local_rings_base_change"]
theorem identifiesLocalRings_tensorProduct
    (A B A' : Type*) [CommRing A] [CommRing B] [CommRing A']
    [Algebra A B] [Algebra A A']
    (h : Algebra.IdentifiesLocalRings A B) :
    Algebra.IdentifiesLocalRings A' (A' ⊗[A] B) :=
  identifiesLocalRings_tensorProduct_general A B A' h

end AlgebraicGeometry.ProEtale

add_to_stacks 096F "local_isomorphism_base_change" Algebra.IsLocalIso.instTensorProduct
add_to_ega "I 4.5.5" "(iii), special case" Algebra.IsLocalIso.instTensorProduct
