module

public import StacksFrontier.RingTheory.DiscreteValuationRing.EppNormalFiniteSupport
public import StacksFrontier.RingTheory.DiscreteValuationRing.EppWildCaseReduction

/-!
# Lifting finite normal coefficient support to a DVR base change

The all-conjugates form of Epp's finite-support argument needs one finite normal residue
extension containing a representative of each minimal polynomial occurring in the chosen
coefficient set.  This file constructs that extension and lifts it to a finite weakly
unramified extension of discrete valuation rings.

The minimal polynomials are deduplicated before taking their product.  This is essential:
the product indexed directly by the coefficient set can repeat an equal minimal polynomial,
and a polynomial with a repeated factor is not separable.  The deduplicated product is
separable because its distinct monic irreducible factors are pairwise coprime.

These results are infrastructure for the synchronized all-factor route to Epp's theorem.
They do not by themselves prove Tag 09F9 or descend a weak solution from one distinguished
tensor factor.
-/

@[expose] public section

open Polynomial IsLocalRing

namespace Stacks.EppTheorem

universe u v w z

/-- A finite set of monic irreducible separable polynomials has one finite Galois
extension containing an element with each prescribed minimal polynomial.

This is the polynomial-level normal-closure primitive.  In particular, it does not
require all of the polynomials to be realised in one pre-existing extension field.
That distinction is what permits one shared extension to serve finite support coming
from several different reduced tensor factors. -/
theorem exists_isGalois_finite_polynomial_root_representatives
    {k : Type u} [Field k] (s : Finset k[X])
    (hmonic : ∀ f ∈ s, f.Monic) (hirr : ∀ f ∈ s, Irreducible f)
    (hsep : ∀ f ∈ s, f.Separable) :
    ∃ (N : Type u) (_ : Field N) (_ : Algebra k N) (_ : FiniteDimensional k N)
      (_ : IsGalois k N), ∀ f ∈ s, ∃ y : N, minpoly k y = f := by
  classical
  let p : k[X] := ∏ f ∈ s, f
  have hpsep : p.Separable := by
    apply Polynomial.separable_prod'
    · intro f hf g hg hfg
      refine (hirr f hf).coprime_iff_not_dvd.mpr fun hdvd => hfg ?_
      exact Polynomial.eq_of_monic_of_associated (hmonic f hf) (hmonic g hg)
        ((hirr f hf).associated_of_dvd (hirr g hg) hdvd)
    · exact hsep
  refine ⟨p.SplittingField, inferInstance, inferInstance, inferInstance,
    IsGalois.of_separable_splitting_field hpsep, ?_⟩
  intro f hf
  set N := p.SplittingField
  have hsplit : (f.map (algebraMap k N)).Splits :=
    (Polynomial.IsSplittingField.splits (L := N) p).of_dvd
      (Polynomial.map_ne_zero hpsep.ne_zero)
      (Polynomial.map_dvd _ (Finset.dvd_prod_of_mem _ hf))
  have hdeg : (f.map (algebraMap k N)).degree ≠ 0 := by
    rw [Polynomial.degree_map_eq_of_injective (algebraMap k N).injective]
    exact (hirr f hf).degree_pos.ne'
  obtain ⟨y, hy⟩ := hsplit.exists_eval_eq_zero hdeg
  refine ⟨y, (minpoly.eq_of_irreducible_of_monic (hirr f hf) ?_ (hmonic f hf)).symm⟩
  rwa [Polynomial.aeval_def, ← Polynomial.eval_map]

/-- A finite family of finite sets of monic irreducible separable polynomials has a
single finite Galois extension containing representatives of all of them.

The family is flattened before forming the splitting field, so equal polynomials in
different factors are deduplicated. -/
theorem exists_isGalois_finite_family_polynomial_root_representatives
    {k : Type u} [Field k] {I : Type w} [Finite I]
    (s : I → Finset k[X])
    (hmonic : ∀ i f, f ∈ s i → f.Monic)
    (hirr : ∀ i f, f ∈ s i → Irreducible f)
    (hsep : ∀ i f, f ∈ s i → f.Separable) :
    ∃ (N : Type u) (_ : Field N) (_ : Algebra k N) (_ : FiniteDimensional k N)
      (_ : IsGalois k N), ∀ i f, f ∈ s i → ∃ y : N, minpoly k y = f := by
  classical
  let _ := Fintype.ofFinite I
  obtain ⟨N, hNfield, hNalg, hNfin, hNgal, hrep⟩ :=
    exists_isGalois_finite_polynomial_root_representatives (Finset.univ.biUnion s)
      (by simpa using fun f i => hmonic i f) (by simpa using fun f i => hirr i f)
      (by simpa using fun f i => hsep i f)
  exact ⟨N, hNfield, hNalg, hNfin, hNgal, fun i f hf =>
    hrep f (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, hf⟩)⟩

/-- A finite family of polynomial support can be covered by one weakly-unramified DVR
base change.  Its residue-field extension is finite Galois and contains an element
having each prescribed minimal polynomial, simultaneously for every family member.

This theorem only packages finite normal residue-field support.  It is independent of
Artin--Schreier reduction, dynamic support extraction, completeness, and Epp's final
endpoint. -/
theorem exists_isWeaklyUnramified_isGalois_residue_finite_family_polynomial_root_representatives
    {A : Type u} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    {I : Type w} [Finite I] (s : I → Finset (ResidueField A)[X])
    (hmonic : ∀ i f, f ∈ s i → f.Monic)
    (hirr : ∀ i f, f ∈ s i → Irreducible f)
    (hsep : ∀ i f, f ∈ s i → f.Separable) :
    ∃ (A₁ : Type u) (_ : CommRing A₁) (_ : IsDomain A₁) (_ : IsDiscreteValuationRing A₁)
      (_ : Algebra A A₁) (_ : Module.Finite A A₁)
      (_ : IsDiscreteValuationRing.IsExtension A A₁),
      IsDiscreteValuationRing.IsWeaklyUnramified A A₁ ∧
        IsGalois (ResidueField A) (ResidueField A₁) ∧
        ∀ i f, f ∈ s i → ∃ y : ResidueField A₁, minpoly (ResidueField A) y = f := by
  obtain ⟨N, _, _, _, _, hrep⟩ :=
    exists_isGalois_finite_family_polynomial_root_representatives s hmonic hirr hsep
  obtain ⟨A₁, hA₁comm, hA₁dom, hA₁dvr, hAA₁, hA₁fin, hA₁ext, hweak, ⟨e⟩⟩ :=
    exists_isWeaklyUnramified_residueField_algEquiv (A := A) N
  exact ⟨A₁, hA₁comm, hA₁dom, hA₁dvr, hAA₁, hA₁fin, hA₁ext, hweak, IsGalois.of_algEquiv e.symm,
    fun i f hf => let ⟨y, hy⟩ := hrep i f hf; ⟨e.symm y, (minpoly.algEquiv_eq e.symm y).trans hy⟩⟩

/-- The minimal polynomials of a finite separable set are monic, irreducible and separable. -/
private theorem minpoly_image_monic_irreducible_separable
    {k : Type u} {K : Type v} [Field k] [Field K] [Algebra k K] [DecidableEq k[X]]
    (s : Finset K) (hint : ∀ x ∈ s, IsIntegral k x) (hsep : ∀ x ∈ s, IsSeparable k x) :
    (∀ f ∈ s.image (minpoly k), f.Monic) ∧ (∀ f ∈ s.image (minpoly k), Irreducible f) ∧
      ∀ f ∈ s.image (minpoly k), f.Separable := by
  refine ⟨?_, ?_, ?_⟩ <;> refine Finset.forall_mem_image.mpr fun x hx => ?_
  exacts [minpoly.monic (hint x hx), minpoly.irreducible (hint x hx), hsep x hx]

/-- One weakly-unramified DVR extension transports a finite family of power roots into
every family of common overfields.

For each family member `i`, the elements `root i x` are explicit `p ^ d i`-th roots of
the finite support `s i`.  Their minimal polynomials are assumed separable over the
base residue field.  A single splitting field simultaneously represents all those
minimal polynomials; after lifting it to a DVR extension, normality transports the
chosen roots into every common overfield `Ω i`.

The depth is per family member: `d` is a function on the index type, so members
carrying different Frobenius depths are covered by the same extension without first
being brought to a common depth.

The quantification over `Ω` occurs after the base extension is constructed.  Thus the
same extension works for every later reduced-factor decomposition, rather than being
chosen with knowledge of a distinguished factor. -/
theorem exists_shared_residue_root_power_family
    {A : Type u} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    {I : Type w} [Finite I] (K : I → Type v)
    [∀ i, Field (K i)] [∀ i, Algebra (ResidueField A) (K i)]
    (p : ℕ) (d : I → ℕ) (s : ∀ i, Finset (K i)) (root : ∀ i, K i → K i)
    (hpow : ∀ i x, x ∈ s i → root i x ^ p ^ (d i) = x)
    (hint : ∀ i x, x ∈ s i → IsIntegral (ResidueField A) (root i x))
    (hsep : ∀ i x, x ∈ s i → IsSeparable (ResidueField A) (root i x)) :
    ∃ (A₁ : Type u) (_ : CommRing A₁) (_ : IsDomain A₁) (_ : IsDiscreteValuationRing A₁)
      (_ : Algebra A A₁) (_ : Module.Finite A A₁)
      (_ : IsDiscreteValuationRing.IsExtension A A₁),
      IsDiscreteValuationRing.IsWeaklyUnramified A A₁ ∧
        IsGalois (ResidueField A) (ResidueField A₁) ∧
        ∀ (Ω : I → Type z) [∀ i, Field (Ω i)]
          [∀ i, Algebra (ResidueField A) (Ω i)]
          [∀ i, Algebra (K i) (Ω i)]
          [∀ i, Algebra (ResidueField A₁) (Ω i)]
          [∀ i, IsScalarTower (ResidueField A) (K i) (Ω i)]
          [∀ i, IsScalarTower (ResidueField A) (ResidueField A₁) (Ω i)],
          ∀ i x, x ∈ s i → ∃ z : ResidueField A₁,
            algebraMap (ResidueField A₁) (Ω i) z ^ p ^ (d i) = algebraMap (K i) (Ω i) x := by
  classical
  obtain ⟨A₁, hA₁comm, hA₁dom, hA₁dvr, hAA₁, hA₁fin, hA₁ext, hweak, hgal, hrep⟩ :=
    exists_isWeaklyUnramified_isGalois_residue_finite_family_polynomial_root_representatives
      (fun i => (s i).image fun x => minpoly (ResidueField A) (root i x))
      (fun i => Finset.forall_mem_image.mpr fun x hx => minpoly.monic (hint i x hx))
      (fun i => Finset.forall_mem_image.mpr fun x hx => minpoly.irreducible (hint i x hx))
      (fun i => Finset.forall_mem_image.mpr fun x hx => hsep i x hx)
  refine ⟨A₁, hA₁comm, hA₁dom, hA₁dvr, hAA₁, hA₁fin, hA₁ext, hweak, hgal, ?_⟩
  intro Ω _ _ _ _ _ _ i x hx
  obtain ⟨y, hy⟩ := hrep i (minpoly (ResidueField A) (root i x))
    (Finset.mem_image.mpr ⟨x, hx, rfl⟩)
  exact exists_pow_eq_algebraMap_of_normal p (d i) (root i x) x (hpow i x hx)
    (hint i x hx) y hy

/-- A finite separable coefficient set has one finite Galois extension containing a
representative of every minimal polynomial in the set.

The finite set of minimal polynomials is formed with `Finset.image`, so equal minimal
polynomials occur only once.  Its product is therefore separable: different factors are
distinct monic irreducible polynomials and hence coprime. -/
theorem exists_isGalois_finite_minpoly_representatives
    {k : Type u} {K : Type v} [Field k] [Field K] [Algebra k K]
    (s : Finset K) (hint : ∀ x ∈ s, IsIntegral k x)
    (hsep : ∀ x ∈ s, IsSeparable k x) :
    ∃ (N : Type u) (_ : Field N) (_ : Algebra k N) (_ : FiniteDimensional k N)
      (_ : IsGalois k N), ∀ x ∈ s, ∃ y : N, minpoly k y = minpoly k x := by
  classical
  have h := minpoly_image_monic_irreducible_separable s hint hsep
  obtain ⟨N, hNfield, hNalg, hNfin, hNgal, hrep⟩ :=
    exists_isGalois_finite_polynomial_root_representatives (s.image (minpoly k))
      h.1 h.2.1 h.2.2
  exact ⟨N, hNfield, hNalg, hNfin, hNgal, fun x hx => hrep _ (Finset.mem_image_of_mem _ hx)⟩

/-- A finite separable coefficient set can be realised by a finite weakly unramified DVR
extension whose residue-field extension is Galois and contains representatives of every
minimal polynomial in the set.

This combines `exists_isGalois_finite_minpoly_representatives` with the general lifting theorem
`exists_isWeaklyUnramified_residueField_algEquiv`.  The conclusion is stated directly in the
residue field of the lifted DVR, rather than retaining an auxiliary abstract splitting field. -/
theorem exists_isWeaklyUnramified_isGalois_residue_minpoly_representatives
    {A : Type u} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    {K : Type v} [Field K] [Algebra (ResidueField A) K]
    (s : Finset K) (hint : ∀ x ∈ s, IsIntegral (ResidueField A) x)
    (hsep : ∀ x ∈ s, IsSeparable (ResidueField A) x) :
    ∃ (A₁ : Type u) (_ : CommRing A₁) (_ : IsDomain A₁) (_ : IsDiscreteValuationRing A₁)
      (_ : Algebra A A₁) (_ : Module.Finite A A₁)
      (_ : IsDiscreteValuationRing.IsExtension A A₁),
      IsDiscreteValuationRing.IsWeaklyUnramified A A₁ ∧
        IsGalois (ResidueField A) (ResidueField A₁) ∧
        ∀ x ∈ s, ∃ y : ResidueField A₁,
          minpoly (ResidueField A) y = minpoly (ResidueField A) x := by
  classical
  have h := minpoly_image_monic_irreducible_separable s hint hsep
  obtain ⟨A₁, hA₁comm, hA₁dom, hA₁dvr, hAA₁, hA₁fin, hA₁ext, hweak, hgal, hrep⟩ :=
    exists_isWeaklyUnramified_isGalois_residue_finite_family_polynomial_root_representatives
      (A := A) (I := Unit) (fun _ => s.image (minpoly (ResidueField A)))
      (fun _ => h.1) (fun _ => h.2.1) (fun _ => h.2.2)
  exact ⟨A₁, hA₁comm, hA₁dom, hA₁dvr, hAA₁, hA₁fin, hA₁ext, hweak, hgal,
    fun x hx => hrep () _ (Finset.mem_image_of_mem _ hx)⟩

/-- Under Epp's condition, every finite subset of the perfect core can be realised by a finite
weakly unramified base change whose residue extension is Galois and contains representatives of
all of the subset's minimal polynomials.

Unlike finite-support absorption into `B`, the normal closure constructed here is not asserted to
embed into the one distinguished residue field `ResidueField B`.  Its role is to cover all
conjugate factors after base change. -/
theorem EppCondition.exists_isWeaklyUnramified_isGalois_residue_minpoly_representatives
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [IsDomain A]
    [IsDiscreteValuationRing A] [IsLocalRing B] [Algebra A B]
    [IsLocalHom (algebraMap A B)] {p : ℕ} [ExpChar (ResidueField B) p]
    (h : EppCondition A B p) (s : Finset (ResidueField B))
    (hs : ∀ x ∈ s, x ∈ perfectCore (ResidueField B) p) :
    ∃ (A₁ : Type u) (_ : CommRing A₁) (_ : IsDomain A₁) (_ : IsDiscreteValuationRing A₁)
      (_ : Algebra A A₁) (_ : Module.Finite A A₁)
      (_ : IsDiscreteValuationRing.IsExtension A A₁),
      IsDiscreteValuationRing.IsWeaklyUnramified A A₁ ∧
        IsGalois (ResidueField A) (ResidueField A₁) ∧
        ∀ x ∈ s, ∃ y : ResidueField A₁,
          minpoly (ResidueField A) y = minpoly (ResidueField A) x :=
  _root_.Stacks.EppTheorem.exists_isWeaklyUnramified_isGalois_residue_minpoly_representatives s
    (fun x hx => (h x (hs x hx)).isIntegral) fun x hx => h x (hs x hx)

/-- Under Epp's condition, a finite subset of the perfect core can be covered at any prescribed
Frobenius depth: there is a single finite weakly unramified base change `A ⊆ A₁`, with Galois
residue extension, carrying a minimal-polynomial representative of a chosen `p ^ N`-th root of
every element of the subset.

The roots are available inside the perfect core itself, by `perfectCore.perfectRing`: the perfect
core is a perfect field, so its iterated Frobenius is an automorphism and `r` may be taken to be
`(iterateFrobeniusEquiv _ p N).symm x`.  That `r` again lies in the perfect core is then automatic
— it is by construction an element of that subfield — so Epp's condition applies to `r` and
`EppCondition.exists_isWeaklyUnramified_isGalois_residue_minpoly_representatives` can be invoked on
the finite set of chosen roots.  No perfectness of `ResidueField B` is used or asserted.

The conclusion pairs each `x` with the root `r` actually chosen for it, and with the representative
`y` of `r`.  Both halves of that pairing are needed downstream: the conjugate factors of a
separable base change are indexed by the embeddings of `ResidueField A₁`, so consuming this result
requires knowing which root each representative represents, not merely that some root of each `x`
is represented somewhere.  The extension `A₁` is not claimed to embed into `B`, and `ResidueField
A₁` is not claimed to contain `r`; only the minimal polynomial over `ResidueField A` is matched. -/
theorem EppCondition.exists_isWeaklyUnramified_isGalois_residue_minpoly_root_representatives
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [IsDomain A]
    [IsDiscreteValuationRing A] [IsLocalRing B] [Algebra A B]
    [IsLocalHom (algebraMap A B)] {p : ℕ} [ExpChar (ResidueField B) p]
    (h : EppCondition A B p) (s : Finset (ResidueField B))
    (hs : ∀ x ∈ s, x ∈ perfectCore (ResidueField B) p) (N : ℕ) :
    ∃ (A₁ : Type u) (_ : CommRing A₁) (_ : IsDomain A₁) (_ : IsDiscreteValuationRing A₁)
      (_ : Algebra A A₁) (_ : Module.Finite A A₁)
      (_ : IsDiscreteValuationRing.IsExtension A A₁),
      IsDiscreteValuationRing.IsWeaklyUnramified A A₁ ∧
        IsGalois (ResidueField A) (ResidueField A₁) ∧
        ∀ x ∈ s, ∃ r : ResidueField B, r ^ p ^ N = x ∧
          ∃ y : ResidueField A₁,
            minpoly (ResidueField A) y = minpoly (ResidueField A) r := by
  classical
  -- Choose, for each `x ∈ s`, a `p ^ N`-th root lying in the perfect core.
  have key : ∀ x ∈ s, ∃ r : ResidueField B,
      r ∈ perfectCore (ResidueField B) p ∧ r ^ p ^ N = x := by
    intro x hx
    set C := perfectCore (ResidueField B) p
    -- `perfectCore.perfectRing`: the perfect core is perfect, so its iterated Frobenius is an
    -- automorphism.  Named explicitly rather than left to instance resolution, so that this
    -- proof's one semantic dependency is visible in the source.
    have : PerfectRing C p := perfectCore.perfectRing (F := ResidueField B) (p := p)
    set z : C := (iterateFrobeniusEquiv C p N).symm ⟨x, hs x hx⟩
    refine ⟨(z : ResidueField B), z.property, ?_⟩
    have hzpow : z ^ p ^ N = (⟨x, hs x hx⟩ : C) := by
      have := (iterateFrobeniusEquiv C p N).apply_symm_apply ⟨x, hs x hx⟩
      rwa [iterateFrobeniusEquiv_def] at this
    exact congrArg Subtype.val hzpow
  choose! root hrootmem hrootpow using key
  obtain ⟨A₁, hA₁comm, hA₁dom, hA₁dvr, hAA₁, hA₁fin, hA₁ext, hweak, hgal, hrep⟩ :=
    h.exists_isWeaklyUnramified_isGalois_residue_minpoly_representatives (s.image root)
      (Finset.forall_mem_image.mpr hrootmem)
  exact ⟨A₁, hA₁comm, hA₁dom, hA₁dvr, hAA₁, hA₁fin, hA₁ext, hweak, hgal,
    fun x hx => ⟨root x, hrootpow x hx,
      hrep (root x) (Finset.mem_image_of_mem root hx)⟩⟩

end Stacks.EppTheorem

end
