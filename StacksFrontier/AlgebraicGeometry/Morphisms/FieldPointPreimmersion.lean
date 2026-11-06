module

public import Mathlib.Algebra.Category.Ring.Epi
public import Mathlib.AlgebraicGeometry.Morphisms.Preimmersion
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import StacksCore.Tactic.StacksAttribute

/-!
# A monomorphism from the spectrum of a field is the residue-field point

A morphism `Spec(K) ⟶ X` from the spectrum of a field factors as
`Spec(K) ⟶ Spec(κ(x)) ⟶ X` through the residue-field point of its image `x`. This file
shows that when the morphism is a *monomorphism* the first factor is an isomorphism, so the
morphism is the residue-field point up to isomorphism; in particular it is a preimmersion,
hence a topological embedding whose base changes are again topological embeddings.

The point of the statement is that a monomorphism of schemes need not be a preimmersion:
the disjoint union `Spec(ℚ(x)) ⊔ Spec(ℚ)` mapping to `Spec(ℚ[x])` by the generic point and
the origin is a monomorphism, is even quasi-compact, and is not an embedding — its source is
discrete while its image carries the Sierpiński topology. What rules this out above is that
the source is the spectrum of a *single* field.

## Main definitions

No new definitions are introduced.

## Main results

* `AlgebraicGeometry.isPreimmersion_of_mono_of_field`: a monomorphism from the spectrum of a
  field is a preimmersion.
* `AlgebraicGeometry.surjective_algebraMap_of_isEpi`: an epimorphic field extension is an
  equality, which is the algebraic content.
* `AlgebraicGeometry.epi_of_mono_specMap`: `Spec` reflects monomorphisms into epimorphisms
  of rings.

## Implementation notes

The factorization through the residue field is Mathlib's
`AlgebraicGeometry.Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField`, and the
residue-field point is a preimmersion in Mathlib. So the work is to show that the induced
`κ(x) ⟶ K` is an isomorphism. Being the left factor of a monomorphism it is a monomorphism
after `Spec`, hence an epimorphism of rings because `Spec` is faithful, hence `Algebra.IsEpi`
by `CommRingCat.epi_iff_epi`.

`AlgebraicGeometry.surjective_algebraMap_of_isEpi` is the field case of
`Algebra.isEpi_iff_surjective_algebraMap_of_finite`, which Mathlib proves only for a finite
algebra. The argument is the same: the quotient `M = L ⧸ K` has `M ⊗[K] M` subsingleton
because every element of `L ⊗[K] L` is of the form `1 ⊗ s`, while a nonzero vector space over
a field has nonzero tensor square. The latter is
`AlgebraicGeometry.nontrivial_tensorProduct_self`, which is deduced from
`TensorProduct.nontrivial_of_linearMap_injective_of_flat_left` applied to the inclusion of the
line spanned by a nonzero vector.

## References

* [Stacks Project, Tag 01L3](https://stacks.math.columbia.edu/tag/01L3)
-/

@[expose] public section

open CategoryTheory TensorProduct

universe u

namespace AlgebraicGeometry

/-! ### Epimorphic field extensions -/

/-- A nonzero vector space over a field has nonzero tensor square: the line spanned by a
nonzero vector gives an injective linear map from the field, and tensoring a flat module with
an injective map out of the base ring keeps the result nonzero. -/
theorem nontrivial_tensorProduct_self (K : Type u) (M : Type u) [Field K] [AddCommGroup M]
    [Module K M] (h : Nontrivial M) : Nontrivial (M ⊗[K] M) := by
  obtain ⟨z, hz⟩ := exists_ne (0 : M)
  have hinj : Function.Injective (LinearMap.toSpanSingleton K M z) := by
    intro a b hab
    simp only [LinearMap.toSpanSingleton_apply] at hab
    have h0 : (a - b) • z = 0 := by rw [sub_smul, hab, sub_self]
    rcases smul_eq_zero.mp h0 with h' | h'
    · exact sub_eq_zero.mp h'
    · exact absurd h' hz
  exact TensorProduct.nontrivial_of_linearMap_injective_of_flat_left K M M
    (LinearMap.toSpanSingleton K M z) hinj

/-- **An epimorphic field extension is an equality.** If `L` is an epimorphic `K`-algebra and
both are fields, then `K ⟶ L` is surjective.

This is the field case of `Algebra.isEpi_iff_surjective_algebraMap_of_finite`, which assumes
the algebra finite. -/
theorem surjective_algebraMap_of_isEpi {K L : Type u} [Field K] [Field L] [Algebra K L]
    [Algebra.IsEpi K L] : Function.Surjective (algebraMap K L) := by
  set R' := (Algebra.linearMap K L).range with hR'
  rcases subsingleton_or_nontrivial (L ⧸ R') with h | h
  · have htop : R' = ⊤ := Submodule.Quotient.subsingleton_iff.mp h
    rw [hR', LinearMap.range_eq_top] at htop
    exact htop
  refine absurd (nontrivial_tensorProduct_self K (L ⧸ R') h)
    (not_nontrivial_iff_subsingleton.mpr ?_)
  refine subsingleton_of_forall_eq 0 fun y ↦ ?_
  induction y with
  | add a b e₁ e₂ => rwa [e₁, zero_add]
  | tmul x y =>
    obtain ⟨x, rfl⟩ := R'.mkQ_surjective x
    obtain ⟨y, rfl⟩ := R'.mkQ_surjective y
    obtain ⟨s, hs⟩ : ∃ s, 1 ⊗ₜ[K] s = x ⊗ₜ[K] y := by
      refine ⟨x * y, ?_⟩
      trans x ⊗ₜ 1 * 1 ⊗ₜ y
      · simp [(Algebra.isEpi_iff_forall_one_tmul_eq K L).mp]
      · simp
    have h1 : R'.mkQ 1 = 0 :=
      (Submodule.Quotient.mk_eq_zero R').mpr ⟨1, map_one (algebraMap K L)⟩
    rw [← map_tmul R'.mkQ R'.mkQ, ← hs, map_tmul, h1, zero_tmul]

/-! ### Monomorphisms out of the spectrum of a field -/

/-- A ring map whose spectrum is a monomorphism of schemes is an epimorphism of rings:
`Spec` is faithful, so it reflects monomorphisms. -/
theorem epi_of_mono_specMap {A C : CommRingCat.{u}} (g : A ⟶ C) (h : Mono (Spec.map g)) :
    Epi g := by
  have h' : Mono (Scheme.Spec.map g.op) := h
  have := Scheme.Spec.mono_of_mono_map h'
  exact unop_epi_of_mono g.op

/-- **A monomorphism from the spectrum of a field is a preimmersion.** Consequently its
underlying map of topological spaces is an embedding, and so is that of each of its base
changes.

The morphism factors through the residue-field point of its image, which is a preimmersion;
the remaining factor is a monomorphism after `Spec`, hence an epimorphism of rings, hence an
isomorphism because an epimorphic field extension is an equality. -/
theorem isPreimmersion_of_mono_of_field (K : Type u) [Field K] {X : Scheme.{u}}
    (f : Spec (CommRingCat.of K) ⟶ X) [Mono f] : IsPreimmersion f := by
  have hfac := Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField K X f
  set φ := Scheme.descResidueField (Scheme.stalkClosedPointTo f) with hφ
  have hmono : Mono (Spec.map φ) := by
    have h2 : Mono (Spec.map φ ≫ X.fromSpecResidueField (f (IsLocalRing.closedPoint K))) := by
      rw [hfac]; infer_instance
    exact mono_of_mono (Spec.map φ) (X.fromSpecResidueField (f (IsLocalRing.closedPoint K)))
  have hepi : Epi φ := epi_of_mono_specMap φ hmono
  have hbij : Function.Bijective φ.hom := by
    algebraize [φ.hom]
    have hae : Algebra.IsEpi (X.residueField (f (IsLocalRing.closedPoint K))) K :=
      CommRingCat.epi_iff_epi.mp hepi
    exact ⟨φ.hom.injective, surjective_algebraMap_of_isEpi⟩
  have : IsIso φ := (ConcreteCategory.isIso_iff_bijective φ).mpr hbij
  rw [← hfac]
  infer_instance

end AlgebraicGeometry

end
