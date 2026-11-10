module

public import Mathlib.AlgebraicGeometry.AlgClosed.Basic
public import Mathlib.RingTheory.Etale.Field
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFreeRank.AffineTarget
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteLocallyFreeOfRank

/-!
# Rational points of a finite étale scheme over an algebraically closed field

A scheme `X` finite étale of degree `r` over an algebraically closed field `k` has exactly `r`
`k`-rational points. This is the counting step in the proof of clause (7) of
[Stacks, Tag 03RP](https://stacks.math.columbia.edu/tag/03RP).

## Main results

* `AlgebraicGeometry.nat_card_sections_eq_of_etale_of_isFiniteLocallyFreeOfRank`.

## Implementation notes

`X` is affine; its ring of sections `B` is a finite étale `k`-algebra, of `k`-dimension `r` by
`AlgebraicGeometry.finite_and_finrank_sections_of_isFiniteLocallyFreeOfRank`, hence a finite
product of finite field extensions of `k` (`Algebra.Etale.iff_exists_algEquiv_prod`), each equal
to `k`. Rational points are closed points (`AlgebraicGeometry.pointEquivClosedPoint`), and the
spectrum of a product of `r` fields has `r` points. The same argument appears in the
formalization of Stacks 03RP (prime-to-characteristic torsion).

## References

* [Stacks Project, Tag 03RP](https://stacks.math.columbia.edu/tag/03RP)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- A finite product of finite field extensions of an algebraically closed field `k` has
`k`-dimension the number of factors. -/
private lemma finrank_prod_fields_eq_card
    (k : Type u) [Field k] [IsAlgClosed k] (I : Type u) [Fintype I]
    (K : I → Type u) [∀ i, Field (K i)] [∀ i, Algebra k (K i)]
    [∀ i, Module.Finite k (K i)] :
    Module.finrank k (∀ i, K i) = Fintype.card I := by
  have hdim (i : I) : Module.finrank k (K i) = 1 :=
    (AlgEquiv.ofBijective (Algebra.ofId k (K i))
      (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := k) (K := K i))).symm.toLinearEquiv
        |>.finrank_eq.trans (Module.finrank_self k)
  simp [Module.finrank_pi_fintype, hdim]

/-- The spectrum of a finite product of fields has as many closed points as factors. -/
private lemma card_closedPoints_prod_fields
    (I : Type u) [Fintype I] (K : I → Type u) [∀ i, Field (K i)] :
    Nat.card (closedPoints (Spec (.of (∀ i, K i)))) = Fintype.card I := by
  let P := ∀ i, K i
  have hclosed (x : PrimeSpectrum P) : IsClosed ({x} : Set (PrimeSpectrum P)) :=
    (PrimeSpectrum.isClosed_singleton_iff_isMaximal x).2
      (IsArtinianRing.isMaximal_of_isPrime x.asIdeal)
  let eclosed : closedPoints (Spec (.of P)) ≃ PrimeSpectrum P :=
    { toFun := fun x => x.1
      invFun := fun x => ⟨x, hclosed x⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  calc
    Nat.card (closedPoints (Spec (.of P))) = Nat.card (Σ i, PrimeSpectrum (K i)) :=
      Nat.card_congr (eclosed.trans (PrimeSpectrum.sigmaToPiHomeo K).toEquiv.symm)
    _ = Nat.card I := Nat.card_congr (Equiv.sigmaUnique I fun i => PrimeSpectrum (K i))
    _ = Fintype.card I := by simp

/-- A homeomorphism maps closed points to closed points. -/
private lemma isClosed_singleton_homeomorph {X Y : Type u}
    [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y) (x : closedPoints X) :
    IsClosed ({e x.1} : Set Y) := by
  simpa only [Set.image_singleton] using e.isClosedMap _ x.2

/-- A homeomorphism induces a bijection of closed points. -/
private def closedPointsEquivOfHomeomorph {X Y : Type u}
    [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y) :
    closedPoints X ≃ closedPoints Y where
  toFun x := ⟨e x.1, isClosed_singleton_homeomorph e x⟩
  invFun y := ⟨e.symm y.1, isClosed_singleton_homeomorph e.symm y⟩
  left_inv x := by simp
  right_inv y := by simp

/-- **A finite étale scheme of degree `r` over an algebraically closed field `k` has exactly `r`
rational points.** Its ring of global sections is a finite étale `k`-algebra of dimension `r`,
hence a product of `r` copies of `k`, and rational points are closed points. -/
theorem nat_card_sections_eq_of_etale_of_isFiniteLocallyFreeOfRank
    (k : Type u) [Field k] [IsAlgClosed k]
    (X : Scheme.{u}) (f : X ⟶ Spec (.of k)) (r : ℕ)
    [Stacks.Morphisms.IsFiniteLocallyFreeOfRank f r] [Etale f] :
    Nat.card {p : Spec (.of k) ⟶ X // p ≫ f = 𝟙 _} = r := by
  classical
  have : IsAffine X := isAffine_of_isAffineHom f
  let B := Γ(X, ⊤)
  let φ : k →+* Γ(Spec (.of k), ⊤) := (Scheme.ΓSpecIso (.of k)).inv.hom
  let g : k →+* B := f.appTop.hom.comp φ
  let : Algebra k B := g.toAlgebra
  have hEtale : Algebra.Etale k B := by
    change RingHom.Etale g
    exact RingHom.Etale.stableUnderComposition φ f.appTop.hom
      (RingHom.Etale.of_bijective
        ((ConcreteCategory.isIso_iff_bijective (Scheme.ΓSpecIso (.of k)).inv).mp inferInstance))
      ((HasRingHomProperty.iff_of_isAffine (P := @Etale)).mp inferInstance)
  obtain ⟨I, _, K, _, _, e, hKfinite⟩ := (Algebra.Etale.iff_exists_algEquiv_prod k B).mp hEtale
  let : Fintype I := Fintype.ofFinite I
  let : ∀ i, Module.Finite k (K i) := fun i => (hKfinite i).1
  calc
    Nat.card {p : Spec (.of k) ⟶ X // p ≫ f = 𝟙 _} =
        Nat.card (closedPoints X) := Nat.card_congr (pointEquivClosedPoint f)
    _ = Nat.card (closedPoints (Spec (.of B))) :=
        Nat.card_congr (closedPointsEquivOfHomeomorph
          (TopCat.homeoOfIso (Scheme.forgetToTop.mapIso X.isoSpec)))
    _ = Nat.card (closedPoints (Spec (.of (∀ i, K i)))) :=
        Nat.card_congr (closedPointsEquivOfHomeomorph
          (PrimeSpectrum.homeomorphOfRingEquiv e.toRingEquiv))
    _ = Fintype.card I := card_closedPoints_prod_fields I K
    _ = Module.finrank k (∀ i, K i) := (finrank_prod_fields_eq_card k I K).symm
    _ = Module.finrank k B := e.symm.toLinearEquiv.finrank_eq
    _ = r := (finite_and_finrank_sections_of_isFiniteLocallyFreeOfRank f r).2

end AlgebraicGeometry

end
