module

public import StacksFrontier.AlgebraicGeometry.Spaces.CoproductCutoff
public import StacksFrontier.AlgebraicGeometry.Size.Monomorphism
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.SpacesOverSpaces.CoproductUniformAtlasSite

/-!
# The cofinality bound on a coproduct index is sharp, and what it costs to remove it

`AlgebraicGeometry.BigFppfSite.contains_sigma_of_lt_cof` — Stacks 000R (2) at an arbitrary
index type — puts `∐ Z` in the site when the index type is **strictly below** the cofinality
`B.cutoff.ord.cof` of the size cutoff. This file shows that the strict inequality cannot be
relaxed, and measures exactly what would have to be assumed instead.

Three statements.

* `AlgebraicGeometry.BigFppfSite.exists_family_not_contains_sigma_of_cof_lt`: as soon as the
  cutoff is **singular** there is a family of objects of the site indexed by a type of
  cardinality exactly `B.cutoff.ord.cof` — hence below the cutoff, so the index type is no
  obstacle to forming the coproduct — whose coproduct is not an object of the site. The sizes
  of the members are cofinal in the cutoff, and a coproduct dominates each of its members
  because the coprojections are monomorphisms
  (`AlgebraicGeometry.Scheme.size_le_of_mono`), so one cardinal below the cutoff would have to
  bound them all.
* `AlgebraicGeometry.BigFppfSite.isRegular_cutoff_iff_contains_sigma`: closure of the site
  under coproducts indexed by *any* type of cardinality below the cutoff is **equivalent** to
  `B.cutoff.IsRegular`. So the closure is not a lemma one can hope to prove from the axioms of
  `AlgebraicGeometry.BigFppfSite`; it is precisely the missing field.
* `AlgebraicGeometry.exists_bigFppfSite_family_not_contains_sigma`: the failure is not
  hypothetical. Feeding `AlgebraicGeometry.singularCutoff = ℶ_{ω₁}`, whose cofinality is `ℵ₁`,
  to `AlgebraicGeometry.BigFppfSite.exists_cutoff_eq` produces an actual big fppf site, and in
  it an actual family below the cutoff whose coproduct is not in the site.

And the price of that field: by
`AlgebraicGeometry.BigFppfSite.isInaccessible_cutoff_of_isRegular`, together with the two
axioms `AlgebraicGeometry.BigFppfSite.aleph0_lt_cutoff` and
`AlgebraicGeometry.BigFppfSite.cutoff_isStrongPrelimit` the regularity of the cutoff makes it
an inaccessible cardinal, which no construction in `Type u` provides — whereas
`AlgebraicGeometry.exists_size_cutoff` (Stacks 000J) produces a cutoff outright, and the
cutoff it produces is `ℶ_{μ.ord + ω₁}`, of cofinality `ℵ₁`, which is singular. Hence
`AlgebraicGeometry.BigFppfSite.isInaccessible_cutoff_of_contains_sigma`: a site closed under
coproducts below its cutoff carries an inaccessible cardinal.

## Where this bites, and whether the model is to blame

It is not. The source builds its category of schemes as `Sch_α`, "the full subcategory of
category of schemes whose objects are elements of `V_α`" (Stacks 000H), for a limit ordinal `α`
whose closure properties are those of Stacks 000J: it contains the prescribed initial set,
it is closed under `Bound(κ) = max {κ ^ ℵ₀, κ⁺}` applied to the size of an object, and it is
closed under *countable* limits and colimits. The library models that category as
`{S | size S < κ}` for a strong prelimit `κ` of uncountable cofinality, clause for clause:
`Bound`-closure is `AlgebraicGeometry.BigFppfSite.cutoff_isStrongPrelimit` and
countable-diagram closure is `AlgebraicGeometry.BigFppfSite.aleph0_lt_cutoff_cof`, the source
asking of its cofinality only `cf(β₁) > ℵ₀`; see the modelling discussion in
`StacksFrontier.AlgebraicGeometry.Size.Cutoff`.

Neither category has a largest object, and the obstruction is the same on both sides. A family
of objects of `Sch_α` indexed by a set of cardinality `cf(α)` can have ranks cofinal in `α`, so
a scheme glued from it need not lie in `V_α`; a family of objects of `Sch_κ` indexed by a type
of cardinality `κ.ord.cof` can have sizes cofinal in `κ`, which is the theorem above. The only
clause of Stacks 000R covering an arbitrary open covering is (6), and it asks for a single
`T ∈ Sch_α` with `size(T) ^ ℵ₀` bounding both the index set and every piece — precisely the
uniform bound that
`AlgebraicGeometry.BigFppfSite.contains_of_openCover_of_size_le` asks for here, and precisely
what a cofinal family does not admit.

So an assembly step which glues representing objects indexed by the affine opens of an
arbitrary object of the site, with no uniform bound on their sizes, is as far beyond the
source's set-theoretic toolkit as beyond this model's. The implication (3) ⟹ (2) of Stacks 0AN5
is one such step; see the discussion in
`StacksFrontier.AlgebraicGeometry.FormalSpace.TautRepresentability`, where
the one missing input is the uniform bound `⨆ K, size (Spec (C ⧸ K)) < B.cutoff` over the weak
ideals of definition `K` of the target ring. The index type of that gluing is never the
problem: `AlgebraicGeometry.BigFppfSite.mk_opens_lt_cutoff` bounds the affine opens of any
object of the site below the cutoff unconditionally, and
`AlgebraicGeometry.BigFppfSite.contains_of_openCover_of_iSup_size_lt` asks for nothing more
about it.

## References

* [Stacks Project, Tag 000J](https://stacks.math.columbia.edu/tag/000J)
* [Stacks Project, Tag 000Q](https://stacks.math.columbia.edu/tag/000Q)
* [Stacks Project, Tag 000R](https://stacks.math.columbia.edu/tag/000R)
* [Stacks Project, Tag 0AN5](https://stacks.math.columbia.edu/tag/0AN5)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Cardinal Ordinal

universe u

namespace Cardinal

/-- **A limit cardinal is approached from below by a family indexed by its cofinality.** For a
cardinal `κ` which is not a successor there are a type `I` of cardinality `κ.ord.cof` and
cardinals `ν i < κ` which are cofinal in `κ`: every cardinal below `κ` is strictly below some
`ν i`.

The family is a cofinal subset of `κ.ord.ToType` of cardinality `κ.ord.cof`
(`Order.exists_cof_eq`), read through `Ordinal.ToType.mk` and `Ordinal.card`. Cofinality is where
the hypothesis enters: a cardinal `c < κ` has `Order.succ c < κ`, and an ordinal below `κ.ord` is
bounded by a member of the cofinal subset. -/
theorem exists_cofinal_family_mk_eq_cof {κ : Cardinal.{u}} (hlim : Order.IsSuccPrelimit κ) :
    ∃ (I : Type u) (ν : I → Cardinal.{u}), #I = κ.ord.cof ∧ (∀ i, ν i < κ) ∧
      ∀ c < κ, ∃ i, c < ν i := by
  obtain ⟨s, hs, hs'⟩ := Order.exists_cof_eq κ.ord.ToType
  refine ⟨s, fun i => ((Ordinal.ToType.mk.symm i.1 : Set.Iio κ.ord) : Ordinal).card,
    by rw [hs', Ordinal.cof_toType], fun i => Cardinal.lt_ord.1 (Ordinal.ToType.mk.symm i.1).2,
    fun c hc => ?_⟩
  have h : (Order.succ c).ord < κ.ord := Cardinal.ord_lt_ord.2 (hlim.succ_lt hc)
  obtain ⟨b, hb, hle⟩ := hs (Ordinal.ToType.mk ⟨_, h⟩)
  have hle' : (Order.succ c).ord ≤ ((Ordinal.ToType.mk.symm b : Set.Iio κ.ord) : Ordinal) := by
    have := Ordinal.ToType.mk.symm.monotone hle
    rw [OrderIso.symm_apply_apply] at this
    exact this
  exact ⟨⟨b, hb⟩, (Order.lt_succ c).trans_le (by simpa using Ordinal.card_le_card hle')⟩

end Cardinal

namespace AlgebraicGeometry

/-- The spectrum of `ℤ` has size below any cardinal above `ℵ₀`. -/
private theorem size_spec_ulift_int_lt {κ : Cardinal.{u}} (h : ℵ₀ < κ) :
    (Spec (CommRingCat.of (ULift.{u} ℤ))).size < κ := by
  rw [Scheme.size_Spec]
  exact (max_le le_rfl Cardinal.mk_le_aleph0).trans_lt h

/-- **A singular cutoff is not closed under coproducts indexed by its cofinality.** If the size
cutoff of a big fppf site is singular, there are a type `I` of cardinality exactly
`B.cutoff.ord.cof` and a family `Z : I → Scheme` of objects of the site whose coproduct is not
an object of the site.

So the strict inequality in `AlgebraicGeometry.BigFppfSite.contains_sigma_of_lt_cof` is sharp:
it cannot be weakened to `#I ≤ B.cutoff.ord.cof`, let alone to `#I < B.cutoff`. The members
are the objects of size at least `ν i` supplied by
`AlgebraicGeometry.BigFppfOver.exists_size_ge` for a family `ν` of cardinals cofinal in the
cutoff, which exists by `Cardinal.exists_cofinal_family_mk_eq_cof` because a singular cardinal
is the supremum of `cof`-many smaller ones. Were the coproduct in the site, the monomorphism
bound `AlgebraicGeometry.Scheme.size_le_of_mono` on its coprojections would bound every
member's size by the single cardinal `max (2 ^ #(∐ Z)) (size (∐ Z))`, which is below the
cutoff by `AlgebraicGeometry.Scheme.max_two_pow_mk_size_lt_of_isStrongPrelimit` and so cannot
bound a cofinal family. -/
theorem BigFppfSite.exists_family_not_contains_sigma_of_cof_lt (B : BigFppfSite.{u})
    (hsing : B.cutoff.ord.cof < B.cutoff) :
    ∃ (I : Type u) (Z : I → Scheme.{u}), #I = B.cutoff.ord.cof ∧ #I < B.cutoff ∧
      (∀ i, B.Contains (Z i)) ∧ ¬ B.Contains (∐ Z) := by
  classical
  obtain ⟨I, ν, hI, hν, hcofinal⟩ :=
    Cardinal.exists_cofinal_family_mk_eq_cof B.cutoff_isStrongPrelimit.isSuccPrelimit
  have hbase := size_spec_ulift_int_lt B.aleph0_lt_cutoff
  choose T hT using fun i : I =>
    BigFppfOver.exists_size_ge B (Spec (CommRingCat.of (ULift.{u} ℤ))) hbase inferInstance
      (max (Spec (CommRingCat.of (ULift.{u} ℤ))).size (ν i)) (le_max_left _ _)
      (max_lt hbase (hν i))
  let Z : I → Scheme.{u} := fun i =>
    (BigFppfOver.toScheme B (Spec (CommRingCat.of (ULift.{u} ℤ))) hbase).obj (T i)
  refine ⟨I, Z, hI, hI.trans_lt hsing, fun i => (T i).left.2, fun hsigma => ?_⟩
  obtain ⟨i, hi⟩ := hcofinal _
    (Scheme.max_two_pow_mk_size_lt_of_isStrongPrelimit B.cutoff_isStrongPrelimit hsigma)
  exact absurd (((le_max_right _ _).trans (hT i)).trans (Scheme.size_le_of_mono (Sigma.ι Z i)))
    (not_le.2 hi)

/-- **Closure under coproducts below the cutoff forces a regular cutoff.** If the coproduct of
every family of objects of a big fppf site indexed by a type of cardinality below the cutoff is
again an object of the site, then the cutoff is a regular cardinal.

This is `AlgebraicGeometry.BigFppfSite.exists_family_not_contains_sigma_of_cof_lt`
contrapositively: a singular cutoff has a family indexed by its cofinality — a cardinal below
the cutoff — violating the closure. -/
theorem BigFppfSite.isRegular_cutoff_of_contains_sigma (B : BigFppfSite.{u})
    (h : ∀ (I : Type u) (Z : I → Scheme.{u}), #I < B.cutoff →
      (∀ i, B.Contains (Z i)) → B.Contains (∐ Z)) :
    B.cutoff.IsRegular := by
  refine ⟨B.aleph0_lt_cutoff.le, ?_⟩
  by_contra hle
  obtain ⟨I, Z, -, hI, hZ, hnot⟩ :=
    B.exists_family_not_contains_sigma_of_cof_lt (not_le.1 hle)
  exact hnot (h I Z hI hZ)

/-- **Closure under coproducts below the cutoff is exactly regularity of the cutoff.** A big
fppf site is closed under coproducts indexed by types of cardinality below its size cutoff if
and only if that cutoff is a regular cardinal.

The forward implication is `AlgebraicGeometry.BigFppfSite.contains_sigma_of_lt_cof`, the
cofinality of a regular cardinal being the cardinal itself; the converse is
`AlgebraicGeometry.BigFppfSite.isRegular_cutoff_of_contains_sigma`. -/
theorem BigFppfSite.isRegular_cutoff_iff_contains_sigma (B : BigFppfSite.{u}) :
    B.cutoff.IsRegular ↔ ∀ (I : Type u) (Z : I → Scheme.{u}), #I < B.cutoff →
      (∀ i, B.Contains (Z i)) → B.Contains (∐ Z) :=
  ⟨fun hreg _ Z hI hZ => B.contains_sigma_of_lt_cof (by rwa [hreg.cof_ord]) Z hZ,
    B.isRegular_cutoff_of_contains_sigma⟩

/-- **A site closed under coproducts below its cutoff carries an inaccessible cardinal.** The
cutoff of a big fppf site is uncountable and a strong prelimit by its axioms, so the regularity
that the closure forces makes it inaccessible.

This is the price of the field whose absence
`AlgebraicGeometry.BigFppfSite.exists_family_not_contains_sigma_of_cof_lt` exhibits: closure of
the site under coproducts indexed below the cutoff is not a missing lemma but a large cardinal
assumption. -/
theorem BigFppfSite.isInaccessible_cutoff_of_contains_sigma (B : BigFppfSite.{u})
    (h : ∀ (I : Type u) (Z : I → Scheme.{u}), #I < B.cutoff →
      (∀ i, B.Contains (Z i)) → B.Contains (∐ Z)) :
    Cardinal.IsInaccessible B.cutoff :=
  B.isInaccessible_cutoff_of_isRegular (B.isRegular_cutoff_of_contains_sigma h)

/-- **A big fppf site, and in it a family below the cutoff whose coproduct is not in the
site.** The cutoff is `AlgebraicGeometry.singularCutoff = ℶ_{ω₁}`, of cofinality `ℵ₁`, which
satisfies all three cardinal axioms of `AlgebraicGeometry.BigFppfSite`
(`AlgebraicGeometry.exists_cutoff_isSingular`) and is the cutoff of a site by
`AlgebraicGeometry.BigFppfSite.exists_cutoff_eq`.

So the failure of closure is realized, not merely permitted: no appeal to the axioms of a big
fppf site can discharge a containment whose index type is only known to be below the
cutoff. -/
theorem exists_bigFppfSite_family_not_contains_sigma :
    ∃ (B : BigFppfSite.{u}) (I : Type u) (Z : I → Scheme.{u}), #I < B.cutoff ∧
      (∀ i, B.Contains (Z i)) ∧ ¬ B.Contains (∐ Z) := by
  obtain ⟨B, hcut, -⟩ := BigFppfSite.exists_cutoff_eq singularCutoff.{u}
    aleph0_lt_singularCutoff isStrongPrelimit_singularCutoff
    (cof_ord_singularCutoff.{u} ▸ Cardinal.aleph0_lt_aleph_one)
    {Spec (CommRingCat.of (ULift.{u} ℤ))}
    (by rintro X rfl; exact size_spec_ulift_int_lt aleph0_lt_singularCutoff)
  have hsing : B.cutoff.ord.cof < B.cutoff := by
    rw [hcut, cof_ord_singularCutoff]
    exact aleph_one_lt_singularCutoff
  obtain ⟨I, Z, -, h⟩ := B.exists_family_not_contains_sigma_of_cof_lt hsing
  exact ⟨B, I, Z, h⟩

end AlgebraicGeometry

end
