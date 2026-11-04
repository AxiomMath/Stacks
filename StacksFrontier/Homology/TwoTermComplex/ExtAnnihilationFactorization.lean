module

public import StacksFrontier.Homology.TwoTermComplex.ExtAnnihilation
public import StacksFrontier.Homology.TwoTermComplex.Representative

/-!
# Annihilation of `Ext¹` by a single scalar, and its factorization criterion

Let `R` be a commutative ring and let `K` be an object of `D(R)` whose cohomology is
concentrated in degrees `-1` and `0`.  For a *single* scalar `f : R`, this file records that
`f` annihilates `Ext¹_R(K, N)` for every `R`-module `N` exactly when multiplication by `f`
on the degree `-1` term of a two-term representative `L` of `K` with free degree `0` term
factors through the differential of `L`, and that the property transports along a morphism
of `D(R)` which is an isomorphism on `H⁰` and an epimorphism on `H⁻¹`.

Both statements are the single-scalar specializations of results already in this cluster:
the factorization criterion is Stacks 0G9F for the principal ideal `(f)`, and the transport
is Stacks 0G9J for the same ideal.  Neither is a new mathematical assertion; the point is
that the hypotheses of the consumers (rig-smoothness, rig-étaleness, Stacks 0GAL) are stated
for one scalar at a time, and that in the factorization form the representative `L` is
supplied by the user rather than produced existentially, so a geometric construction can be
plugged straight in.

## Main results

* `TwoTermComplex.smul_ext_one_eq_zero_iff_exists_factorization`: the factorization
  criterion for one scalar, against a user-supplied representative.
* `TwoTermComplex.smul_ext_one_eq_zero_of_comparison`: transport along a comparison morphism
  which is an `H⁰`-isomorphism and an `H⁻¹`-epimorphism.

## Implementation notes

The passage from one scalar to the principal ideal it generates is the observation that the
scalars admitting a factorization are closed under multiplication by `R`, which is the
`smul_mem'` half of the ideal constructed inside the proof of Stacks 0G9H.

## References

* [The Stacks Project, Lemma 15.85.6 (0G9F)](https://stacks.math.columbia.edu/tag/0G9F)
* [The Stacks Project, Lemma 15.85.10 (0G9J)](https://stacks.math.columbia.edu/tag/0G9J)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace TwoTermComplex

universe u v

attribute [local instance] HasDerivedCategory.standard

variable {R : Type u} [CommRing R]

/-- A cochain complex concentrated in degrees `-1` and `0` has no cohomology in the derived
category outside those two degrees. -/
public theorem isZero_homology_Q_obj_of_twoTerm (L : CochainComplex (ModuleCat.{v} R) ℤ)
    [L.IsStrictlyGE (-1)] [L.IsStrictlyLE 0] (i : ℤ) (h₁ : i ≠ -1) (h₀ : i ≠ 0) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) i).obj
      (DerivedCategory.Q.obj L)) := by
  apply IsZero.of_iso _ ((DerivedCategory.homologyFunctorFactors _ i).app L)
  rcases lt_or_gt_of_ne h₀ with hi | hi
  · exact (CochainComplex.exactAt_of_isGE L (-1) i (by omega)).isZero_homology
  · exact (CochainComplex.exactAt_of_isLE L 0 i hi).isZero_homology

/-- An object of the derived category isomorphic to a complex concentrated in degrees `-1`
and `0` has no cohomology outside those two degrees. -/
public theorem isZero_homology_of_twoTerm_iso {K : DerivedCategory (ModuleCat.{v} R)}
    (L : CochainComplex (ModuleCat.{v} R) ℤ)
    [L.IsStrictlyGE (-1)] [L.IsStrictlyLE 0] (e : DerivedCategory.Q.obj L ≅ K)
    (i : ℤ) (h₁ : i ≠ -1) (h₀ : i ≠ 0) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) i).obj K) :=
  IsZero.of_iso (isZero_homology_Q_obj_of_twoTerm L i h₁ h₀)
    ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) i).mapIso e.symm)

/-- If `f` kills every element of a module, then so does every element of the ideal `(f)`. -/
private theorem smul_eq_zero_of_mem_span_singleton {M : Type*} [AddCommMonoid M] [Module R M]
    {f a : R} (ha : a ∈ Ideal.span {f}) (h : ∀ x : M, f • x = 0) (x : M) : a • x = 0 := by
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp ha
  rw [mul_comm, mul_smul, h]

variable [Small.{v} R]

/-- A scalar `f` annihilates `Ext¹_R(K, N)` for every `R`-module `N` exactly when
multiplication by `f` on the degree `-1` term of a two-term representative `L` of `K` with
free degree `0` term factors through the differential of `L`.

This is Stacks 0G9F for the principal ideal `(f)`, with the representative supplied rather
than produced existentially. -/
public theorem smul_ext_one_eq_zero_iff_exists_factorization (f : R)
    {K : DerivedCategory (ModuleCat.{v} R)}
    (L : CochainComplex (ModuleCat.{v} R) ℤ)
    [L.IsStrictlyGE (-1)] [L.IsStrictlyLE 0] [Module.Free R (L.X 0)]
    (e : DerivedCategory.Q.obj L ≅ K) :
    (∀ (N : ModuleCat.{v} R) (ξ : DerivedCategory.Ext K
        ((DerivedCategory.singleFunctor (ModuleCat.{v} R) 0).obj N) 1), f • ξ = 0)
      ↔ ∃ h : L.X 0 ⟶ L.X (-1), L.d (-1) 0 ≫ h = f • 𝟙 (L.X (-1)) := by
  have key := ext_one_annihilated_iff_twoTerm_factorization (Ideal.span {f}) K
    (isZero_homology_of_twoTerm_iso L e)
  refine ⟨fun h ↦ ?_, fun ⟨h, hh⟩ N ↦ ?_⟩
  · exact key.2.1.mp (key.1.mp fun N _ ha ↦ smul_eq_zero_of_mem_span_singleton ha (h N))
      L ‹_› ‹_› inferInstance ⟨e⟩ f (Ideal.mem_span_singleton_self f)
  · refine key.1.mpr ⟨L, ‹_›, ‹_›, ‹_›, ⟨e⟩, fun a ha ↦ ?_⟩ N f
      (Ideal.mem_span_singleton_self f)
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp ha
    exact ⟨c • h, by rw [Linear.comp_smul, hh, smul_smul]⟩

/-- If multiplication by `f` on the degree `-1` term of a two-term complex `L` with free
degree `0` term factors through the differential of `L`, and `L` maps into a two-term object
`K` of `D(R)` by a morphism which is an isomorphism on `H⁰` and an epimorphism on `H⁻¹`,
then `f` annihilates `Ext¹_R(K, N)` for every `R`-module `N`.

This is the composite of Stacks 0G9F and Stacks 0G9J for the principal ideal `(f)`. -/
public theorem smul_ext_one_eq_zero_of_comparison (f : R)
    {K : DerivedCategory (ModuleCat.{v} R)}
    (L : CochainComplex (ModuleCat.{v} R) ℤ)
    [L.IsStrictlyGE (-1)] [L.IsStrictlyLE 0] [Module.Free R (L.X 0)]
    (hK : ∀ i : ℤ, i ≠ -1 → i ≠ 0 →
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) i).obj K))
    (α : DerivedCategory.Q.obj L ⟶ K)
    [IsIso ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) 0).map α)]
    [Epi ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) (-1)).map α)]
    (h : L.X 0 ⟶ L.X (-1)) (hh : L.d (-1) 0 ≫ h = f • 𝟙 (L.X (-1))) :
    ∀ (N : ModuleCat.{v} R) (ξ : DerivedCategory.Ext K
      ((DerivedCategory.singleFunctor (ModuleCat.{v} R) 0).obj N) 1), f • ξ = 0 := by
  have hsrc : ∀ (N : ModuleCat.{v} R), ∀ a ∈ Ideal.span {f},
      ∀ ξ : DerivedCategory.Ext (DerivedCategory.Q.obj L)
        ((DerivedCategory.singleFunctor (ModuleCat.{v} R) 0).obj N) 1, a • ξ = 0 := by
    intro N _ ha
    exact smul_eq_zero_of_mem_span_singleton ha
      ((smul_ext_one_eq_zero_iff_exists_factorization f L (Iso.refl _)).mpr ⟨h, hh⟩ N)
  intro N ξ
  exact TwoTermComplexExt.ext_one_annihilated_of_homology_iso_epi (Ideal.span {f}) α
    (isZero_homology_Q_obj_of_twoTerm L) hK hsrc N f (Ideal.mem_span_singleton_self f) ξ

end TwoTermComplex

end
