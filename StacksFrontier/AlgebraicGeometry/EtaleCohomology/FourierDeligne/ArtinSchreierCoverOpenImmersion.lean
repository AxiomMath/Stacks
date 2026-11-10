module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FourierDeligne.ArtinSchreierScaledAffineLine
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ArtinSchreierSheaf.BaseChange

/-!
# Artin–Schreier covers over an open of a scheme with an irreducible cover

Let `φ : A → A'` be a morphism of `𝔽_q`-algebras. The Artin–Schreier algebra of `φ(g)` is the
base change of that of `g`: `A' ⊗_A A[T]/(T^q - T - g) ≅ A'[T]/(T^q - T - φ g)`, so
`Spec A'[T]/(T^q - T - φ g)` is the fibre product of the cover of `g` with `Spec A' → Spec A`
(`Stacks.ArtinSchreier.isPushout_ringMap`). When `Spec φ` is an open immersion, the cover of
`φ(g)` is therefore an open of the cover of `g`, and it is connected as soon as the cover of `g`
is irreducible (`Stacks.ArtinSchreier.connectedSpace_cover_of_isOpenImmersion`).

With the cover `T^q - T = σ x` of `𝔸¹_Ω`, an affine line, this shows that the Artin–Schreier
cover of `σ x` on an affine open of `𝔸¹_Ω` is connected; such opens are the fibres `V_Ω` in the
Artin–Schreier half of the generic coinvariant vanishing in Laumon's proof of
[Tag 03VH](https://stacks.math.columbia.edu/tag/03VH). Every open of `𝔸¹_K` is affine
(`AlgebraicGeometry.isAffine_of_isOpenImmersion_polynomial`): its complement is the zero locus
of one polynomial.

## Main results

* `AlgebraicGeometry.isAffine_of_isOpenImmersion_polynomial`.
* `Stacks.ArtinSchreier.isPushout_ringMap`.
* `Stacks.ArtinSchreier.connectedSpace_cover_of_isOpenImmersion`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Polynomial

open scoped TensorProduct

universe u

namespace AlgebraicGeometry

/-- **Every open of the affine line over a field is affine**: the complement of the image of an
open immersion `V ⟶ Spec K[X]` is the zero locus of one polynomial `g` (`K[X]` is a principal
ideal domain), so `V` is the basic open `D(g)`. -/
theorem isAffine_of_isOpenImmersion_polynomial (K : Type u) [Field K] {V : Scheme.{u}}
    (jV : V ⟶ Spec (.of K[X])) [IsOpenImmersion jV] : IsAffine V := by
  let C : Set (PrimeSpectrum K[X]) := (Set.range jV.base)ᶜ
  have hC : IsClosed C := jV.isOpenEmbedding.isOpen_range.isClosed_compl
  obtain ⟨g, hg⟩ := (IsPrincipalIdealRing.principal (PrimeSpectrum.vanishingIdeal C)).principal
  have hZ : PrimeSpectrum.zeroLocus (PrimeSpectrum.vanishingIdeal C : Set K[X]) = C := by
    rw [PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure, hC.closure_eq]
  have h2 : PrimeSpectrum.zeroLocus ({g} : Set K[X]) = C := by
    rw [← PrimeSpectrum.zeroLocus_span, ← hZ, hg]
  let W : (Spec (.of K[X])).Opens := PrimeSpectrum.basicOpen g
  have hrange : Set.range jV.base = (W : Set (Spec (.of K[X]))) := by
    change Set.range jV.base = ((PrimeSpectrum.basicOpen g : _) : Set (PrimeSpectrum K[X]))
    rw [PrimeSpectrum.basicOpen_eq_zeroLocus_compl, h2, compl_compl]
    rfl
  have : IsAffine W.toScheme := IsAffineOpen.Spec_basicOpen (R := .of K[X]) g
  exact IsAffine.of_isIso (IsOpenImmersion.isoOfRangeEq jV W.ι
    (by rw [hrange, Scheme.Opens.range_ι])).hom

end AlgebraicGeometry

namespace Stacks.ArtinSchreier

variable (k : Type u) [Field k] [Fintype k] {A : Type u} [CommRing A] [Algebra k A] (g : A)
  {A' : Type u} [CommRing A'] [Algebra k A'] (φ : A →ₐ[k] A')

/-- **The Artin–Schreier algebra commutes with base change**: the square of rings
`A → A'`, `A → A[T]/(T^q - T - g)`, `A' → A'[T]/(T^q - T - φ g)`, `ringMap` is a pushout. -/
theorem isPushout_ringMap :
    IsPushout (CommRingCat.ofHom φ.toRingHom) (CommRingCat.ofHom (algebraMap A (Ring k g)))
      (CommRingCat.ofHom (algebraMap A' (Ring k (φ g))))
      (CommRingCat.ofHom (ringMap k g φ)) := by
  let : Algebra A A' := φ.toRingHom.toAlgebra
  have hmap : ((poly k g).map
      (Algebra.TensorProduct.includeRight (R := A) (A := A') (B := A)).toRingHom).map
        ((Algebra.TensorProduct.rid A A' A' : A' ⊗[A] A ≃ₐ[A'] A') : A' ⊗[A] A →+* A') =
      poly k (φ g) := by
    rw [Polynomial.map_map, ← map_poly k g φ]
    congr 1
    ext a
    simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.rid_tmul]
    rw [Algebra.smul_def, mul_one]
    rfl
  let e : A' ⊗[A] Ring k g ≃ₐ[A'] Ring k (φ g) :=
    (AdjoinRoot.tensorAlgEquiv (R := A) (T := A') (poly k g) _ rfl).trans
      (AdjoinRoot.mapAlgEquiv (Algebra.TensorProduct.rid A A' A') _ _ (Associated.of_eq hmap))
  refine (CommRingCat.isPushout_tensorProduct A A' (Ring k g)).of_iso (Iso.refl _) (Iso.refl _)
    (Iso.refl _) e.toRingEquiv.toCommRingCatIso rfl rfl ?_ ?_
  · ext a
    exact e.commutes a
  · ext x
    · change e (1 ⊗ₜ AdjoinRoot.of (poly k g) x) =
        ringMap k g φ (algebraMap A (Ring k g) x)
      rw [ringMap_algebraMap]
      simp only [e, AlgEquiv.trans_apply, AdjoinRoot.tensorAlgEquiv_of]
      rw [AdjoinRoot.coe_mapAlgEquiv, AdjoinRoot.map_of]
      change AdjoinRoot.of _ (Algebra.TensorProduct.rid A A' A' (1 ⊗ₜ x)) = _
      rw [Algebra.TensorProduct.rid_tmul, Algebra.smul_def, mul_one]
      rfl
    · change e (1 ⊗ₜ AdjoinRoot.root (poly k g)) = ringMap k g φ (AdjoinRoot.root (poly k g))
      rw [ringMap_root]
      simp only [e, AlgEquiv.trans_apply, AdjoinRoot.tensorAlgEquiv_root]
      rw [AdjoinRoot.coe_mapAlgEquiv, AdjoinRoot.map_root]

/-- **The Artin–Schreier cover of `φ(g)` is the base change of that of `g`.** -/
theorem isPullback_coverHom :
    IsPullback (Spec.map (CommRingCat.ofHom (ringMap k g φ))) (coverHom k A' (φ g))
      (coverHom k A g) (Spec.map (CommRingCat.ofHom φ.toRingHom)) :=
  (isPullback_SpecMap_of_isPushout _ _ _ _ (isPushout_ringMap k g φ)).flip

/-- **Over an open `Spec A' ⊆ Spec A`, the Artin–Schreier cover is connected** when the cover
over `Spec A` is irreducible and `A'` is nonzero: the cover of `φ(g)` is the base change of the
cover of `g` along the open immersion `Spec φ`, an open of an irreducible space, and it is
nonempty, `A'[T]/(T^q - T - φ g)` being free of positive rank over `A'`. -/
theorem connectedSpace_cover_of_isOpenImmersion
    [IsOpenImmersion (Spec.map (CommRingCat.ofHom φ.toRingHom))]
    [IrreducibleSpace (cover k A g).left] [Nontrivial A'] :
    ConnectedSpace (cover k A' (φ g)).left := by
  have : IsOpenImmersion (Spec.map (CommRingCat.ofHom (ringMap k g φ))) :=
    MorphismProperty.of_isPullback (P := @IsOpenImmersion) (isPullback_coverHom k g φ).flip
      inferInstance
  have : IrreducibleSpace (Spec (.of (Ring k g))) := ‹IrreducibleSpace (cover k A g).left›
  have : Nontrivial (Ring k (φ g)) := by
    have h1 : degree (Polynomial.X + C (φ g)) <
        degree (Polynomial.X ^ Fintype.card k : A'[X]) := by
      rw [degree_X_pow]
      exact degree_X_add_C_lt (φ g) (Fintype.one_lt_card (α := k))
    rw [AdjoinRoot.nontrivial_iff_of_monic (monic_poly k (φ g)), poly,
      degree_sub_eq_left_of_degree_lt h1, degree_X_pow]
    exact_mod_cast Fintype.card_pos
  have : IrreducibleSpace (Spec (.of (Ring k (φ g)))) :=
    (Spec.map (CommRingCat.ofHom (ringMap k g φ))).isOpenEmbedding.irreducibleSpace
  exact inferInstanceAs (ConnectedSpace (Spec (.of (Ring k (φ g)))))

end Stacks.ArtinSchreier

end
