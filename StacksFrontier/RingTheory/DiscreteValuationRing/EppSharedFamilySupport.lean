module

public import StacksFrontier.RingTheory.DiscreteValuationRing.EppNormalResidueBaseChange

/-!
# One shared residue extension for the whole reduced-factor family

The synchronized bridge `IsDiscreteValuationRing.isWeakSolution_of_forall_reducedFactorPackages`
asks for a weak solution at **every** field factor of `(L ⊗[K] K₁) ⧸ nilradical`, all packaged over
**one** second extension `K₂` fixed before the factors are examined.  Supplying that input has a
forced order, and getting the order wrong is what makes an all-factor argument collapse back into a
one-factor one:

1. gather the finite coefficient support of *every* factor, and the minimal polynomials of the
   chosen `p ^ N`-th roots, and **union them across the entire family**;
2. only then choose the normal/Galois residue extension and lift it to a discrete valuation ring
   `R₂` with fraction field `K₂`;
3. only then build each factor's package, all over that same `K₂`;
4. only then invoke the bridge.

This file supplies step 1 and the residue half of step 2.  The union has to happen somewhere, and
the factors' residue fields are pairwise different types, so there is exactly one place it can
happen: the polynomial ring over the *base* residue field.  `exists_isGalois_splits_finset` is
therefore stated at the level of a `Finset (k[X])`, and
`exists_isGalois_forall_family_minpoly_representatives` takes the union there —
`Finset.univ.biUnion fun i => (s i).image (minpoly k)` — before building anything.

## Why the order is load-bearing

A per-factor choice of extension is not a weaker version of this; it is a different and
insufficient statement.  If each factor `i` picks its own `N i`, the family `{N i}` must afterwards
be amalgamated into a common overfield, and preserving a weak solution across that amalgamation is
precisely what forces the completeness and `IsAlgClosed` hypotheses that confine
`exists_finite_extension_isWeakSolution_of_forall_reducedFactorSolutions` to the setting of Tag
09F8.  Fixing one `K₂` up front is what removes them.  Normality is what lets a single extension
serve all the conjugates at once: once a normal extension contains one root of a minimal polynomial
it contains them all, so the factor indexed by any embedding is covered and not merely the factor
at a distinguished one (`finset_maps_mem_fieldRange_of_normal`).

## What this file does not do, and what is still owed

It does **not** prove Tag 09F9, and it does not descend a weak solution along one embedding.  The
Stacks route to 09F9 goes through clause (3) of Tag 09ET, which is false; nothing here uses it,
and the per-factor hypotheses below are quantified over every index of the family.

Three specific things are *not* claimed:

* no universal containment `perfectCore κ_B ≤ range (κ_{R₂} → κ_B)` — the perfect core need not be
  finite over the base residue field, so it cannot be absorbed by a finite extension.  Only the
  finitely many elements actually handed in are covered, at one prescribed Frobenius depth;
* no completeness and no algebraically closed residue field anywhere in this file;
* no transport of Epp's condition from `A → B` to the factors `R → S i`.  That transport is a real
  obligation and it is taken as a hypothesis (`h : ∀ i, EppCondition R (S i) p`) rather than
  asserted.

Steps 3 and 4 of the order above are **not** implemented here, because the upstream theorem they
need does not exist yet.  Every available per-factor endgame — the finite Artin–Schreier and
degree-`p` reductions in `EppAlgClosedResidue` and `ArtinSchreier` — *produces* its own extension
`F` of `K₁` and returns a package over that `F`.  What step 3 needs is the same endgame run against
a **prescribed** `K₂`: given `K₂ / K₁` finite containing the residue representatives this file
constructs, a package `IntegralClosureBaseChange R (S i) K₁ (E i) K₂`.  Until it exists, the
honest state of this route is that step 1 and the residue half of step 2 are proved and steps 2b, 3
and 4 are open.

## Main results

* `Stacks.EppTheorem.exists_isGalois_splits_finset`: one finite Galois extension realising every
  polynomial in a finite set of monic separable irreducibles as a minimal polynomial.  This is the
  polynomial-level core, and it is the form the family union needs.
* `Stacks.EppTheorem.exists_isGalois_forall_family_minpoly_representatives`: the same for a finite
  **family** of finite subsets of pairwise different extension fields — the union step.
* `exists_isWeaklyUnramified_isGalois_residue_family_root_representatives`:
  the union step applied to perfect-core subsets of every factor's residue field at a prescribed
  Frobenius depth, and lifted to a single finite weakly unramified extension `R ⊆ R₂` with Galois
  residue extension.

## References

* [The Stacks Project, Tag 09F9](https://stacks.math.columbia.edu/tag/09F9)
-/

@[expose] public section

open Polynomial IsLocalRing

namespace Stacks.EppTheorem

universe u v w

/-- **One finite Galois extension realises a whole finite set of polynomials as minimal
polynomials.**

Let `t` be a finite set of monic separable irreducible polynomials over `k`.  Their product is
separable — distinct monic irreducibles are coprime — so its splitting field `N` is finite Galois
over `k`, and each `f ∈ t`, dividing the product, splits in `N` and is therefore the minimal
polynomial of one of its roots there.

This is stated at the level of polynomials rather than of field elements on purpose.  The elements
whose minimal polynomials are being realised live, in the intended application, in the residue
fields of the different factors of a reduced base change — pairwise different types, which cannot
be unioned.  Their minimal polynomials all live in the single ring `k[X]`, which can; see
`exists_isGalois_forall_family_minpoly_representatives`.

The same argument appears inline in `exists_isGalois_finite_minpoly_representatives` and in
`exists_normal_finite_minpoly_representatives`, each specialised to one field; those two should be
re-derived from this lemma rather than repeating it. -/
theorem exists_isGalois_splits_finset {k : Type u} [Field k] (t : Finset k[X])
    (hmonic : ∀ f ∈ t, f.Monic) (hirr : ∀ f ∈ t, Irreducible f)
    (hsep : ∀ f ∈ t, f.Separable) :
    ∃ (N : Type u) (_ : Field N) (_ : Algebra k N) (_ : FiniteDimensional k N)
      (_ : IsGalois k N), ∀ f ∈ t, ∃ y : N, minpoly k y = f := by
  classical
  have hpsep : (∏ f ∈ t, f).Separable := by
    apply Polynomial.separable_prod'
    · intro f hf g hg hfg
      refine (hirr f hf).coprime_iff_not_dvd.mpr fun hdvd => hfg ?_
      exact Polynomial.eq_of_monic_of_associated (hmonic f hf) (hmonic g hg)
        ((hirr f hf).associated_of_dvd (hirr g hg) hdvd)
    · exact hsep
  refine ⟨(∏ f ∈ t, f).SplittingField, inferInstance, inferInstance, inferInstance,
    IsGalois.of_separable_splitting_field hpsep, ?_⟩
  intro f hf
  set N := (∏ f ∈ t, f).SplittingField
  have hsplit : (f.map (algebraMap k N)).Splits :=
    (Polynomial.IsSplittingField.splits (L := N) (∏ f ∈ t, f)).of_dvd
      (Polynomial.map_ne_zero hpsep.ne_zero)
      (Polynomial.map_dvd _ (Finset.dvd_prod_of_mem _ hf))
  have hdeg : (f.map (algebraMap k N)).degree ≠ 0 := by
    rw [Polynomial.degree_map_eq_of_injective (algebraMap k N).injective]
    intro h0
    exact (hirr f hf).not_isUnit (Polynomial.isUnit_iff_degree_eq_zero.mpr h0)
  obtain ⟨y, hy⟩ := hsplit.exists_eval_eq_zero hdeg
  refine ⟨y, (minpoly.eq_of_irreducible_of_monic (hirr f hf) ?_ (hmonic f hf)).symm⟩
  rwa [Polynomial.aeval_def, ← Polynomial.eval_map]

/-- **The union step: one finite Galois extension for a whole finite family of coefficient sets.**

Given finitely many extension fields `K i` of `k`, each with a finite set `s i` of separable
integral elements, there is a *single* finite Galois `N / k` containing a minimal-polynomial
representative of every element of every `s i`.

The fields `K i` are unrelated to one another — in the application they are the residue fields of
the different factors of a reduced base change — so the sets `s i` cannot be combined directly.
The union is taken one level up, among minimal polynomials over `k`:
`Finset.univ.biUnion fun i => (s i).image (minpoly k)`.  Everything after the union sees a single
`Finset (k[X])`, and `exists_isGalois_splits_finset` handles it.

This is step 1 of the shared-family order, and it must precede the construction of the extension.
Choosing an extension per factor and amalgamating afterwards is the alternative this replaces; see
the module docstring for why that alternative carries completeness hypotheses this one does not. -/
theorem exists_isGalois_forall_family_minpoly_representatives
    {k : Type u} [Field k] {ι : Type w} [Finite ι] (K : ι → Type v)
    [∀ i, Field (K i)] [∀ i, Algebra k (K i)]
    (s : ∀ i, Finset (K i))
    (hint : ∀ i, ∀ x ∈ s i, IsIntegral k x)
    (hsep : ∀ i, ∀ x ∈ s i, IsSeparable k x) :
    ∃ (N : Type u) (_ : Field N) (_ : Algebra k N) (_ : FiniteDimensional k N)
      (_ : IsGalois k N), ∀ i, ∀ x ∈ s i, ∃ y : N, minpoly k y = minpoly k x := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  set t : Finset k[X] := Finset.univ.biUnion fun i => (s i).image (minpoly k) with ht
  have hmem : ∀ i, ∀ x ∈ s i, minpoly k x ∈ t := fun i x hx =>
    Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, Finset.mem_image_of_mem _ hx⟩
  have hall : ∀ P : k[X] → Prop, (∀ i, ∀ x ∈ s i, P (minpoly k x)) → ∀ f ∈ t, P f := by
    intro P hP f hf
    obtain ⟨i, -, hf'⟩ := Finset.mem_biUnion.mp hf
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hf'
    exact hP i x hx
  obtain ⟨N, hNfield, hNalg, hNfin, hNgal, hrep⟩ :=
    exists_isGalois_splits_finset t
      (hall Monic fun i x hx => minpoly.monic (hint i x hx))
      (hall Irreducible fun i x hx => minpoly.irreducible (hint i x hx))
      (hall Separable hsep)
  exact ⟨N, hNfield, hNalg, hNfin, hNgal,
    fun i x hx => hrep (minpoly k x) (hmem i x hx)⟩

/-- **Step 1 and the residue half of step 2, for the reduced-factor family.**

Let `R` be a discrete valuation ring and `S i`, `i` ranging over a finite index set, local rings
receiving `R` locally — in the application, the discrete valuation rings of the field factors of
`(L ⊗[K] K₁) ⧸ nilradical`.  Given, for each factor, a finite subset `s i` of the perfect core of
its residue field, and a prescribed Frobenius depth `N`, there is **one** finite weakly unramified
extension `R ⊆ R₂` whose residue extension is Galois and which carries a minimal-polynomial
representative of a chosen `p ^ N`-th root of every element of every `s i`.

The order is the point.  The roots are chosen factor by factor, but their minimal polynomials are
unioned over the whole family before `R₂` is built, so `R₂` serves all the factors simultaneously
and no factor is distinguished.  A per-factor `R₂` would not do: it is what forces the amalgamation
step whose cost is the completeness and `IsAlgClosed` hypotheses of the unsynchronized bridge.

The roots exist inside the perfect core itself, without any perfectness assumption on
`ResidueField (S i)`: the perfect core is a perfect field (`perfectCore.perfectRing`), so its
iterated Frobenius is an automorphism and the root may be taken to be
`(iterateFrobeniusEquiv _ p N).symm x`.  That the root again lies in the perfect core is automatic,
so Epp's condition applies to it.

The conclusion pairs each `x` with the root actually chosen for it and with that root's
representative.  Both halves are needed downstream: the conjugate factors of a separable base
change are indexed by the embeddings of `ResidueField R₂`, so a consumer must know which root each
representative represents, not merely that some root of each `x` is represented somewhere.

Epp's condition for the factors is a **hypothesis**, not a consequence drawn here.  Transporting it
from the original extension to the factors of a base change is a separate obligation, and asserting
it would be assuming part of what the shared-family route has to establish.  Nothing is claimed
about `R₂` embedding into any `S i`, nor about `ResidueField R₂` containing any root; only the
minimal polynomial over `ResidueField R` is matched. -/
theorem EppCondition.exists_isWeaklyUnramified_isGalois_residue_family_root_representatives
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {ι : Type w} [Finite ι] (S : ι → Type v) [∀ i, CommRing (S i)] [∀ i, IsLocalRing (S i)]
    [∀ i, Algebra R (S i)] [∀ i, IsLocalHom (algebraMap R (S i))]
    {p : ℕ} [∀ i, ExpChar (ResidueField (S i)) p]
    (h : ∀ i, EppCondition R (S i) p)
    (s : ∀ i, Finset (ResidueField (S i)))
    (hs : ∀ i, ∀ x ∈ s i, x ∈ perfectCore (ResidueField (S i)) p) (N : ℕ) :
    ∃ (R₂ : Type u) (_ : CommRing R₂) (_ : IsDomain R₂) (_ : IsDiscreteValuationRing R₂)
      (_ : Algebra R R₂) (_ : Module.Finite R R₂)
      (_ : IsDiscreteValuationRing.IsExtension R R₂),
      IsDiscreteValuationRing.IsWeaklyUnramified R R₂ ∧
        IsGalois (ResidueField R) (ResidueField R₂) ∧
        ∀ i, ∀ x ∈ s i, ∃ r : ResidueField (S i), r ^ p ^ N = x ∧
          ∃ y : ResidueField R₂,
            minpoly (ResidueField R) y = minpoly (ResidueField R) r := by
  classical
  -- Choose, factor by factor, a `p ^ N`-th root of each prescribed element, inside the perfect
  -- core where the iterated Frobenius is bijective.
  have key : ∀ i, ∀ x ∈ s i, ∃ r : ResidueField (S i),
      r ∈ perfectCore (ResidueField (S i)) p ∧ r ^ p ^ N = x := by
    intro i x hx
    set C := perfectCore (ResidueField (S i)) p
    set z : C := (iterateFrobeniusEquiv C p N).symm ⟨x, hs i x hx⟩
    refine ⟨(z : ResidueField (S i)), z.property, ?_⟩
    have hzpow : z ^ p ^ N = (⟨x, hs i x hx⟩ : C) := by
      have := (iterateFrobeniusEquiv C p N).apply_symm_apply ⟨x, hs i x hx⟩
      rwa [iterateFrobeniusEquiv_def] at this
    simpa using congrArg Subtype.val hzpow
  choose! root hrootmem hrootpow using key
  -- Union the chosen roots' minimal polynomials over the whole family, then build one extension.
  obtain ⟨F, hFfield, hFalg, hFfin, hFgal, hrep⟩ :=
    exists_isGalois_forall_family_minpoly_representatives
      (k := ResidueField R) (fun i => ResidueField (S i)) (fun i => (s i).image (root i))
      (fun i => Finset.forall_mem_image.2 fun x hx => (h i _ (hrootmem i x hx)).isIntegral)
      (fun i => Finset.forall_mem_image.2 fun x hx => h i _ (hrootmem i x hx))
  obtain ⟨R₂, hR₂comm, hR₂dom, hR₂dvr, hRR₂, hR₂fin, hR₂ext, hweak, ⟨e⟩⟩ :=
    exists_isWeaklyUnramified_residueField_algEquiv (A := R) F
  refine ⟨R₂, hR₂comm, hR₂dom, hR₂dvr, hRR₂, hR₂fin, hR₂ext, hweak,
    IsGalois.of_algEquiv e.symm, ?_⟩
  intro i x hx
  refine ⟨root i x, hrootpow i x hx, ?_⟩
  obtain ⟨y, hy⟩ := hrep i (root i x) (Finset.mem_image_of_mem _ hx)
  exact ⟨e.symm y, (minpoly.algEquiv_eq e.symm y).trans hy⟩

end Stacks.EppTheorem

end
