module

public import Mathlib.FieldTheory.FinTrdeg
public import StacksFrontier.AlgebraicGeometry.Flatness.FiniteNeighborhood
public import StacksFrontier.AlgebraicGeometry.Flatness.FiniteOverSmooth
public import StacksFrontier.AlgebraicGeometry.Morphisms.FinitePresentation.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.QuasiFinite.Criteria

/-!
# Comparing residue fields across an affine chart

This file identifies the residue field of a point of an affine scheme with the residue field of
the corresponding prime, compatibly with `Spec.map`, and transports pure transcendence of a field
extension along ring isomorphisms and across such identifications.

## Main results

* `Stacks.Flatness.purelyTranscendental_of_ringEquiv_base` and
  `Stacks.Flatness.purelyTranscendental_of_ringEquiv` transport pure transcendence along
  isomorphisms of the base field, respectively of both fields of an extension.
* `Stacks.Flatness.residueFieldIso_square` says that the residue field map of a `Spec.map`
  agrees, after `AlgebraicGeometry.Scheme.Spec.residueFieldIso`, with the ring map on the image
  of the structure maps; `Stacks.Flatness.residueFieldIso_square'` is the same with the
  morphism and its defining equation as separate arguments.
* `Stacks.Flatness.purelyTranscendental_of_factorisation` transfers pure transcendence along a
  factorisation of an algebra map as an isomorphism, a ring map and an isomorphism.

## Implementation notes

Every ring is behind a variable and no residue field is ever written out: instantiating a
written-out conclusion in this area exhausts the heartbeat budget, whereas the same term is
free when its type is inferred.

## References

* [Stacks Project, Tag 052E](https://stacks.math.columbia.edu/tag/052E)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MvPolynomial

universe u

namespace Stacks.Flatness

/-! ### Transport of pure transcendence along isomorphisms -/

/-- Pure transcendence is transported along a ring isomorphism of the base field. -/
theorem purelyTranscendental_of_ringEquiv_base {k k' K : Type*} [Field k] [Field k'] [Field K]
    [Algebra k K] [Algebra k' K] (e : k' ≃+* k)
    (he : ∀ a, algebraMap k' K a = algebraMap k K (e a))
    (h : PurelyTranscendental k K) : PurelyTranscendental k' K := by
  let _ := h
  obtain ⟨s, hind, hgen⟩ := PurelyTranscendental.exists_basis k K
  refine ⟨s, ?_, ?_⟩
  · change AlgebraicIndependent k' (fun i : s ↦ (i : K))
    refine algebraicIndependent_iff.2 fun p hp => ?_
    have hmap : MvPolynomial.aeval (fun i : s ↦ (i : K))
        (MvPolynomial.map e.toRingHom p) = 0 := by
      change MvPolynomial.eval₂ (algebraMap k K) (fun i : s ↦ (i : K))
        (MvPolynomial.map e.toRingHom p) = 0
      calc
        _ = MvPolynomial.eval₂ ((algebraMap k K).comp e.toRingHom)
            (fun i : s ↦ (i : K)) p :=
          MvPolynomial.eval₂_map e.toRingHom (fun i : s ↦ (i : K)) (algebraMap k K) p
        _ = MvPolynomial.eval₂ (algebraMap k' K) (fun i : s ↦ (i : K)) p := by
          congr 1
          ext a
          rw [RingHom.comp_apply]
          exact (he a).symm
        _ = 0 := by simpa [MvPolynomial.aeval_def] using hp
    exact (MvPolynomial.map_injective (f := e.toRingHom) e.injective)
      (by simpa using hind.eq_zero_of_aeval_eq_zero _ hmap)
  · refine eq_top_iff.mpr fun y _ => ?_
    have hy : y ∈ IntermediateField.adjoin k s := by rw [hgen]; trivial
    refine IntermediateField.adjoin_induction (F := k) (E := K) (s := s)
      (motive := fun z _ ↦ z ∈ IntermediateField.adjoin k' s)
      (fun z hz ↦ IntermediateField.subset_adjoin k' s hz)
      (fun a ↦ ?_) (fun _ _ _ _ h₁ h₂ ↦ add_mem h₁ h₂)
      (fun _ _ h₁ ↦ inv_mem h₁) (fun _ _ _ _ h₁ h₂ ↦ mul_mem h₁ h₂) hy
    have hval : algebraMap k K a = algebraMap k' K (e.symm a) := by
      simpa using (he (e.symm a)).symm
    rw [hval]
    exact (IntermediateField.adjoin k' s).algebraMap_mem _

/-- Pure transcendence is transported along ring isomorphisms of both fields. -/
theorem purelyTranscendental_of_ringEquiv {k k' K K' : Type*}
    [Field k] [Field k'] [Field K] [Field K'] [Algebra k K] [Algebra k' K']
    (e : k' ≃+* k) (E : K ≃+* K')
    (he : ∀ a : k', algebraMap k' K' a = E (algebraMap k K (e a)))
    (h : PurelyTranscendental k K) : PurelyTranscendental k' K' := by
  let _ := h
  let _ : Algebra k K' := ((E : K →+* K').comp (algebraMap k K)).toAlgebra
  exact purelyTranscendental_of_ringEquiv_base e he
    (AlgEquiv.purelyTranscendental (AlgEquiv.ofRingEquiv (f := E) (fun _ => rfl)))

/-! ### The residue field of a point of an affine scheme -/

/-- **The residue field comparison square.** The residue field map of `Spec.map χ` at a point `z`
agrees, after the canonical identification of the residue fields of points of affine schemes with
the residue fields of the corresponding primes, with `χ` on the image of the structure maps. -/
theorem residueFieldIso_square {R A : CommRingCat.{u}} (χ : R ⟶ A) (z : Spec A) :
    CommRingCat.ofHom (algebraMap R _) ≫
        (Scheme.Spec.residueFieldIso R ((Spec.map χ) z)).inv ≫
          (Spec.map χ).residueFieldMap z =
      χ ≫ CommRingCat.ofHom (algebraMap A _) ≫ (Scheme.Spec.residueFieldIso A z).inv := by
  rw [reassoc_of% (show _ = (Scheme.ΓSpecIso R).inv ≫ (Spec R).Γevaluation ((Spec.map χ) z) from
      Scheme.Spec.algebraMap_residueFieldIso_inv R _),
    show _ = (Scheme.ΓSpecIso A).inv ≫ (Spec A).Γevaluation z from
      Scheme.Spec.algebraMap_residueFieldIso_inv A z,
    Scheme.Γevaluation_naturality, Scheme.ΓSpecIso_inv_naturality_assoc]

/-- `Stacks.Flatness.residueFieldIso_square` with the morphism and its defining equation as
separate arguments. -/
theorem residueFieldIso_square' {R A : CommRingCat.{u}} (χ : R ⟶ A) (g : Spec A ⟶ Spec R)
    (hg : g = Spec.map χ) (z : Spec A) :
    CommRingCat.ofHom (algebraMap R _) ≫
        (Scheme.Spec.residueFieldIso R (g z)).inv ≫ g.residueFieldMap z =
      χ ≫ CommRingCat.ofHom (algebraMap A _) ≫ (Scheme.Spec.residueFieldIso A z).inv := by
  subst hg
  exact residueFieldIso_square χ z

/-! ### Pure transcendence across a factorisation -/

/-- **Transfer of pure transcendence along a factorisation.** If the algebra map of a field
extension factors as an isomorphism, a morphism `m` of commutative rings, and an isomorphism, and
if `m` is identified with the algebra map of a purely transcendental extension, then the given
extension is purely transcendental. -/
theorem purelyTranscendental_of_factorisation {E₁ E₂ : CommRingCat.{u}} {k L k₁ L₁ : Type u}
    [Field k] [Field L] [Field k₁] [Field L₁] [Algebra k L] [Algebra k₁ L₁]
    (b : CommRingCat.of k ⟶ E₁) (hb : Function.Bijective b.hom) (m : E₁ ⟶ E₂)
    (c : E₂ ⟶ CommRingCat.of L) (hc : Function.Bijective c.hom)
    (e₁ : E₁ ≃+* k₁) (e₂ : E₂ ≃+* L₁)
    (hm : ∀ z : E₁, e₂ (m.hom z) = algebraMap k₁ L₁ (e₁ z))
    (halg : ∀ a : k, algebraMap k L a = c.hom (m.hom (b.hom a)))
    (hPT : PurelyTranscendental k₁ L₁) : PurelyTranscendental k L := by
  refine purelyTranscendental_of_ringEquiv ((RingEquiv.ofBijective b.hom hb).trans e₁)
    (e₂.symm.trans (RingEquiv.ofBijective c.hom hc)) (fun a => ?_) hPT
  have h := hm (b.hom a)
  simp only [RingEquiv.coe_trans, Function.comp_apply, RingEquiv.coe_ofBijective]
  rw [halg a, ← h, e₂.symm_apply_apply]

end Stacks.Flatness

end
