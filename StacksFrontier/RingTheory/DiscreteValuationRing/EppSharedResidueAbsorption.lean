module

public import StacksFrontier.RingTheory.DiscreteValuationRing.EppConditionAscent
public import StacksFrontier.RingTheory.DiscreteValuationRing.EppSharedFamilySupport

/-!
# One shared base change absorbing every factor's deep roots, read in residue overfields

`StacksFrontier.RingTheory.DiscreteValuationRing.EppWildFamilyPreparation` handles the branch of the
degree-`p` equal-characteristic endgame in which some Laurent coefficient of the layer lies
*outside* the perfect core of its own residue field.  That branch needs no residue hypothesis at
all, because the wild data is intrinsic.

This file is about the complementary branch: **every** coefficient lies in the perfect core.  There
the endgame is the constant-numerator argument, and it genuinely interrogates the base residue
field — it asks, at each coefficient `x` and at a prescribed Frobenius depth `N`, for an element of
the *base* whose `p ^ N`-th power is `x`.  Under Epp's condition a `p ^ N`-th root of a
perfect-core coefficient is separable algebraic over the base residue field but need not lie in its
image, so the demand is met only after a finite base change, and for a family of conjugate factors
it must be met by **one** base change serving all of them.

## The shape of the conclusion, and why it is an overfield statement

`exists_isWeaklyUnramified_isGalois_residue_family_root_representatives`
already builds the single base change `R ⊆ R₂`: it chooses a `p ^ N`-th root factor by factor,
unions the roots' minimal polynomials over the whole family *before* `R₂` is built, and returns a
finite weakly unramified `R₂` with Galois residue extension carrying a representative of each.
What it deliberately does **not** claim is any map from `ResidueField R₂` into a factor's residue
field, and that restraint is not a gap — the claim would be false.  A conjugate factor can contain
the chosen root of one coefficient without containing the normal closure of its minimal
polynomial, so there is in general no embedding of `ResidueField R₂` into `ResidueField (S i)`.

What is true, and is what the layer actually consumes, is the statement in a **common overfield**:
in any field `Ω` receiving both `ResidueField (S i)` and `ResidueField R₂` compatibly over
`ResidueField R` — in the application, the residue field of the factor's ring after the base change
to `R₂` — the image of each coefficient acquires a `p ^ N`-th root *from `ResidueField R₂`*.  That
is `Stacks.EppTheorem.finset_exists_pow_eq_algebraMap_of_normal`, whose mechanism is normality:
  once a
normal extension contains one root of a minimal polynomial it contains every conjugate, so the
representative chosen without reference to the factor serves in every factor.

`Stacks.EppTheorem.exists_finite_normal_baseChange_forall_reducedFactor_mem_fieldRange` in
`EppDegreePrimeBridge` is the same pattern at the level of field ranges.

## Main result

* `exists_isWeaklyUnramified_forall_exists_pow_eq_of_residueOverfield`:
  from Epp's condition at every factor and a finite perfect-core coefficient set per factor, one
  finite weakly unramified `R ⊆ R₂` with Galois residue extension such that, in **every** common
  residue overfield of a factor and of `R₂`, every one of that factor's coefficients has a
  `p ^ N`-th root coming from `ResidueField R₂`.

The quantifier order is the content: `R₂` is fixed before any overfield is named, and the overfield
is universally quantified afterwards, so one base change serves every factor and every choice of
ambient residue field.  No factor is distinguished and no factor's root is transported to another:
each factor's conclusion is derived from its own representative.

## What this does and does not settle

It settles the **residue** half of the all-perfect-core branch, uniformly over the family, which is
the half that Epp's condition is for.

It does not produce a shared *solution*.  In this branch the endgame is
`IsDiscreteValuationRing.isWeakSolution_of_constant_artinSchreier_parameter`, whose extension is
pinned by `Algebra.adjoin K {w} = ⊤` to be the Artin--Schreier extension of the member's own
constant parameter `a / π ^ n`.  Distinct members have distinct parameters, so unlike the wild
branch — where the shared object is an orbit extension of a rank chosen from the family as a whole
— there is no single extension of this shape serving the family, and producing one is a further
obligation.  It is recorded here rather than hidden: the wild branch is closed over one shared
extension, this branch is closed on the residue side only.

Nothing here is tagged and there is still no unconditional Tag 09F9.

## References

* [The Stacks Project, Tag 09F1](https://stacks.math.columbia.edu/tag/09F1)
* [The Stacks Project, Tag 09F9](https://stacks.math.columbia.edu/tag/09F9)
-/

@[expose] public section

open IsLocalRing

namespace Stacks.EppTheorem

universe u v w uΩ

/-- **One weakly unramified base change supplying every factor's deep roots, in every common
residue overfield.**

Let `R` be a discrete valuation ring and `S i`, over a finite index set, local rings receiving `R`
locally — in the application the valuation rings of the field factors of a reduced base change.
Assume Epp's condition at each factor, and fix for each a finite set `s i` of elements of the
perfect core of its residue field together with a depth `N`.  Then there is a single finite weakly
unramified `R ⊆ R₂`, with Galois residue extension, such that for **every** factor `i` and
**every** field `Ω` receiving `ResidueField (S i)` and `ResidueField R₂` compatibly over
`ResidueField R`, each `x ∈ s i` satisfies

`∃ z : ResidueField R₂, algebraMap _ Ω z ^ p ^ N = algebraMap _ Ω x`.

This is exactly the antecedent the degree-`p` layer demands in its all-perfect-core branch, for the
whole family at once: a base element whose `p ^ N`-th power is the coefficient, read where both
sides live.

**Why an overfield and not an embedding.**  The roots are chosen factor by factor, but the
extension is built from the union of their minimal polynomials over the whole family, so
`ResidueField R₂` contains a *conjugate* of each root, not the root itself.  Claiming an embedding
of `ResidueField R₂` into `ResidueField (S i)` would be false — a factor may contain one root
without containing the normal closure — and it is not needed: normality of `ResidueField R₂` over
`ResidueField R` means that in any common overfield the conjugate and the root generate the same
subfield, which is all the `p ^ N`-th power equation requires.  This is
`finset_exists_pow_eq_algebraMap_of_normal`, and `Ω` is quantified after `R₂` precisely so that one
`R₂` serves every ambient choice.

**Where Epp's condition enters.**  Only to make each chosen root integral, hence to give its
minimal polynomial over `ResidueField R` a meaning worth matching.  That the chosen root is again a
perfect-core element — which is what lets Epp's condition apply to it — is automatic and is
`mem_perfectCore_of_pow_eq`: the iterated Frobenius of a field is injective, so the root supplied
by the family construction is *the* root, whatever way it was obtained.

No factor is distinguished, no completeness is assumed, and no residue field is assumed perfect,
separably closed or algebraically closed. -/
theorem EppCondition.exists_isWeaklyUnramified_forall_exists_pow_eq_of_residueOverfield
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
        ∀ (i : ι) (Ω : Type uΩ) [Field Ω] [Algebra (ResidueField R) Ω]
          [Algebra (ResidueField (S i)) Ω] [Algebra (ResidueField R₂) Ω]
          [IsScalarTower (ResidueField R) (ResidueField (S i)) Ω]
          [IsScalarTower (ResidueField R) (ResidueField R₂) Ω],
          ∀ x ∈ s i, ∃ z : ResidueField R₂,
            algebraMap (ResidueField R₂) Ω z ^ p ^ N =
              algebraMap (ResidueField (S i)) Ω x := by
  classical
  obtain ⟨R₂, hR₂comm, hR₂dom, hR₂dvr, hRR₂, hR₂fin, hR₂ext, hweak, hgal, hrep⟩ :=
    EppCondition.exists_isWeaklyUnramified_isGalois_residue_family_root_representatives S h s hs N
  let := hR₂comm
  let := hR₂dom
  let := hR₂dvr
  let := hRR₂
  let := hR₂fin
  let := hR₂ext
  refine ⟨R₂, hR₂comm, hR₂dom, hR₂dvr, hRR₂, hR₂fin, hR₂ext, hweak, hgal, ?_⟩
  intro i Ω _ _ _ _ _ _
  have := hgal
  have : Normal (ResidueField R) (ResidueField R₂) := hgal.to_normal
  -- Each factor's own representative, promoted to a root equation in `Ω` by normality.  The
  -- representative was chosen from the family's union, so it is a conjugate of the factor's root
  -- rather than that root; normality is what makes the difference invisible in `Ω`.
  -- Every field parameter is named.  Only `k` is genuinely undetermined -- it occurs solely in
  -- this lemma's hypotheses, never in its conclusion, so passing `hrep` as a lambda leaves it a
  -- metavariable and the `Normal k N` instance search gets stuck.  `K`, `N` and `Ω` are already
  -- fixed by unification with the goal; they are written out for uniformity with the other
  -- prepared call sites.  Note the named type parameter `N` is the extension field, distinct from
  -- the positional natural-number depth `N` passed as the lemma's `d`.
  refine finset_exists_pow_eq_algebraMap_of_normal (k := ResidueField R)
    (K := ResidueField (S i)) (N := ResidueField R₂) (Ω := Ω) p N (s i) (fun x hx => ?_)
  obtain ⟨r, hrpow, y, hy⟩ := hrep i x hx
  exact ⟨r, hrpow, (h i r (mem_perfectCore_of_pow_eq (hs i x hx) hrpow)).isIntegral, y, hy⟩

/-- **Depth-zero shared absorption puts every displayed coefficient in the new base range.**

This is the specialization of
`EppCondition.exists_isWeaklyUnramified_forall_exists_pow_eq_of_residueOverfield` at Frobenius
depth zero.  At that depth the equation returned there is simply

`algebraMap (ResidueField R₂) Ω z = algebraMap (ResidueField (S i)) Ω x`,

so it is exactly membership of the image of `x` in the field range of the new base.  The
quantifier over the common overfield remains outside the construction of `R₂`; consequently the
same normal weakly-unramified base change works in every conjugate factor formed afterwards.

This is the residue-field hypothesis consumed by mixed-level factor re-entry.  Keeping it as a
named theorem avoids asking that re-entry code to unfold a `p ^ 0`-th-root statement and, more
importantly, records that no embedding of the new residue field into the original factor is being
claimed. -/
theorem EppCondition.exists_isWeaklyUnramified_forall_mem_fieldRange_of_residueOverfield
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {I : Type w} [Finite I] (S : I → Type v) [∀ i, CommRing (S i)] [∀ i, IsLocalRing (S i)]
    [∀ i, Algebra R (S i)] [∀ i, IsLocalHom (algebraMap R (S i))]
    {p : ℕ} [∀ i, ExpChar (ResidueField (S i)) p]
    (h : ∀ i, EppCondition R (S i) p)
    (s : ∀ i, Finset (ResidueField (S i)))
    (hs : ∀ i, ∀ x ∈ s i, x ∈ perfectCore (ResidueField (S i)) p) :
    ∃ (R₂ : Type u) (_ : CommRing R₂) (_ : IsDomain R₂) (_ : IsDiscreteValuationRing R₂)
      (_ : Algebra R R₂) (_ : Module.Finite R R₂)
      (_ : IsDiscreteValuationRing.IsExtension R R₂),
      IsDiscreteValuationRing.IsWeaklyUnramified R R₂ ∧
        IsGalois (ResidueField R) (ResidueField R₂) ∧
        ∀ (i : I) (Ω : Type uΩ) [Field Ω] [Algebra (ResidueField R) Ω]
          [Algebra (ResidueField (S i)) Ω] [Algebra (ResidueField R₂) Ω]
          [IsScalarTower (ResidueField R) (ResidueField (S i)) Ω]
          [IsScalarTower (ResidueField R) (ResidueField R₂) Ω],
          ∀ x ∈ s i,
            algebraMap (ResidueField (S i)) Ω x ∈
              (algebraMap (ResidueField R₂) Ω).fieldRange := by
  obtain ⟨R₂, hR₂comm, hR₂dom, hR₂dvr, hRR₂, hR₂fin, hR₂ext,
      hweak, hgal, habs⟩ :=
    EppCondition.exists_isWeaklyUnramified_forall_exists_pow_eq_of_residueOverfield S h s hs 0
  refine ⟨R₂, hR₂comm, hR₂dom, hR₂dvr, hRR₂, hR₂fin, hR₂ext,
    hweak, hgal, ?_⟩
  intro i Ω _ _ _ _ _ _ x hx
  obtain ⟨z, hz⟩ := habs i Ω x hx
  refine RingHom.mem_fieldRange.mpr ⟨z, ?_⟩
  simpa using hz

end Stacks.EppTheorem

end
