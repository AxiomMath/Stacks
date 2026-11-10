module

public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.RingTheory.Artinian.Algebra
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.KrullDimension.Zero
public import StacksCore.RingTheory.LocalRing.MaximalIdeal.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.Spectrum.Prime.Integral
public import StacksFrontier.RingTheory.Spectrum.Prime.Profinite
public import StacksFrontier.Topology.Dimension.CounterexampleCodimension

/-!
# Integral closure of the ground field in global sections

For a connected reduced scheme over a field, the elements of its ring of global sections which
are integral over the ground field form a field.

## Main results

* `AlgebraicGeometry.integralClosure_globalSections_isField`: the integral closure of the ground
  field in the global sections of a connected reduced scheme is a field.

## Implementation notes

The algebra structure on global sections is the one induced contravariantly by the given
structure morphism to the spectrum of the ground field, using the canonical identification of
the global sections of an affine spectrum with its ring. The integral closure has no strict
inclusions between primes, hence a totally disconnected spectrum; connectedness of the scheme
then makes the induced map to that spectrum constant, which exhibits the integral closure as a
reduced local ring of dimension zero.

## References

* [Stacks Project, Tag 04MI](https://stacks.math.columbia.edu/tag/04MI)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- The integral closure of the ground field in the global sections of a
connected reduced scheme over that field is a field. -/
@[stacks 04MI]
public lemma integralClosure_globalSections_isField
    (k : Type u) [Field k] (X : Scheme.{u})
    (f : X ⟶ Spec (.of k)) [ConnectedSpace X] [IsReduced X] :
    letI : Algebra k Γ(X, ⊤) := ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop).hom.toAlgebra
    IsField (integralClosure k Γ(X, ⊤)) := by
  let _ : Algebra k Γ(X, ⊤) := ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop).hom.toAlgebra
  let A := integralClosure k Γ(X, ⊤)
  let φ : A →+* Γ(X, ⊤) := A.val
  let g : X ⟶ Spec (.of A) :=
    ΓSpec.adjunction.homEquiv X (Opposite.op (.of A)) (CommRingCat.ofHom φ).op
  have hnoincl : ∀ p q : Ideal A, p.IsPrime → q.IsPrime → p ≤ q → p = q := by
    intro p q _ _ hpq
    by_contra hpqne
    exact (not_le_and_not_le_of_comap_eq_of_ne k A p q
      ((Ideal.eq_bot_of_prime _).trans (Ideal.eq_bot_of_prime _).symm) hpqne).1 hpq
  have : TotallyDisconnectedSpace (PrimeSpectrum A) :=
    (spec_profinite_tfae A).out 5 3 |>.mp hnoincl
  have hmax : ∀ q : Ideal A, q.IsPrime → q.IsMaximal :=
    (spec_profinite_tfae A).out 5 6 |>.mp hnoincl
  have hconst : ∀ x y : X, g.base x = g.base y :=
    TotallyDisconnectedSpace.eq_of_continuous
      (fun z : X ↦ show PrimeSpectrum A from g z) g.continuous
  let p : Ideal A := (g.base (Classical.arbitrary X)).asIdeal
  have hp : ∀ x : X, (g.base x).asIdeal = p := fun x ↦
    congrArg PrimeSpectrum.asIdeal (hconst x (Classical.arbitrary X))
  have hlocal : IsLocalRing A := by
    refine (isLocalRing_iff_exists_maximal_isUnit (R := A)).2
      ⟨p, hmax p (g.base (Classical.arbitrary X)).isPrime, fun a ha ↦ ?_⟩
    have ha' : ∀ (x : X) (hx : x ∈ (⊤ : X.Opens)),
        IsUnit (X.presheaf.germ ⊤ x hx (φ a)) := by
      intro x hx
      rw [← X.mem_basicOpen (φ a) x hx]
      have happ : g.appTop ((Scheme.ΓSpecIso (.of A)).inv a) = φ a :=
        congrArg (fun h : CommRingCat.of A ⟶ CommRingCat.of Γ(X, ⊤) ↦ h a)
          (ΓSpecIso_inv_ΓSpec_adjunction_homEquiv (CommRingCat.ofHom φ))
      rw [← happ, ← g.preimage_basicOpen_top]
      change g x ∈ (Spec (.of A)).basicOpen ((Scheme.ΓSpecIso (.of A)).inv a)
      rw [basicOpen_eq_of_affine]
      change a ∉ (g x).asIdeal
      simpa [hp x] using ha
    exact IsArtinianRing.isUnit_of_nonZeroDivisor_of_isIntegral' (R := k)
      (mem_nonZeroDivisors_of_injective Subtype.val_injective
        (X.toRingedSpace.isUnit_of_isUnit_germ ⊤ (φ a) ha').mem_nonZeroDivisors)
  have : _root_.IsReduced A := isReduced_of_injective φ Subtype.val_injective
  have : Ring.KrullDimLE 0 A := Ring.KrullDimLE.mk₀ hmax
  exact Ring.KrullDimLE.isField_of_isReduced (R := A)

end AlgebraicGeometry

end
