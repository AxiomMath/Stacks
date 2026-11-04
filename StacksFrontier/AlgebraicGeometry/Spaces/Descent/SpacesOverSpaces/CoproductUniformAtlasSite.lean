module

public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.SpacesOverSpaces.CoproductUniformAtlas
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.SpacesOverSpaces.CoproductUniformAtlasCutoff
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.ContainingSet
public import StacksFrontier.CategoryTheory.Sites.Pretopology.SmallSubsite

/-!
# A big fppf site in which the coproduct hypothesis of Stacks 0ADK genuinely bites

`AlgebraicGeometry.Space.not_exists_uniform_atlas_size_bound` rules out the one route that would
replace the cofinality bound `AlgebraicGeometry.BigFppfSite.AdmitsCoproductIndex` by the weaker
`#I < B.cutoff`. This file settles the question outright, by exhibiting a big fppf site, a base
scheme, and a family of algebraic spaces over it indexed by a type of cardinality *below* the
cutoff which has no sheaf coproduct that is an algebraic space at all.

The site is built with a prescribed singular cutoff. The construction of
`AlgebraicGeometry.BigFppfSite.exists_containing` chooses its cutoff through Stacks 000J and so
says nothing about which cardinals occur;
`AlgebraicGeometry.BigFppfSite.exists_cutoff_eq` is the same construction with the cutoff
supplied, which is legitimate because the chosen covering system of
`exists_covBounded_isSite` and the site axioms `AlgebraicGeometry.isSite_fppfCutoff` hold for
every cardinal. Feeding it `AlgebraicGeometry.singularCutoff = ℶ_{ω₁}` gives a site whose cutoff
has cofinality `ℵ₁`.

Over the spectrum of the integers in that site, the polynomial constructions of
`AlgebraicGeometry.BigFppfOver.exists_size_ge` provide, for each `a < ω₁`, an object of size at
least `ℶ_a`. The resulting family is indexed by a type of cardinality `ℵ₁`, which is below the
cutoff but equal to its cofinality, and its members' sizes are cofinal in the cutoff; so
`AlgebraicGeometry.Space.Descent.not_nonempty_algebraicSheafCoproduct_of_cofinal_size` applies.

Hence the hypothesis of
`AlgebraicGeometry.Space.Descent.familyCoproductEquivalenceOfAdmitsCoproductIndex` cannot be
weakened to `#I < B.cutoff`: at that hypothesis the category of descent data relative to the
coproduct does not exist, because the coproduct is not an algebraic space over the base. What a
regular cutoff would buy is recorded in
`AlgebraicGeometry.BigFppfSite.admitsCoproductIndex_of_isRegular_cutoff`, at the price measured
by `AlgebraicGeometry.BigFppfSite.isInaccessible_cutoff_of_isRegular`.

## Main results

* `AlgebraicGeometry.BigFppfSite.exists_cutoff_eq`: a big fppf site with a prescribed cutoff.
* `AlgebraicGeometry.exists_family_lt_cutoff_not_nonempty_algebraicSheafCoproduct`: a site, a
  base, and a family indexed below the cutoff with no algebraic sheaf coproduct.

## References

* [Stacks Project, Tag 000J](https://stacks.math.columbia.edu/tag/000J)
* [Stacks Project, Tag 000X](https://stacks.math.columbia.edu/tag/000X)
* [Stacks Project, Tag 021R](https://stacks.math.columbia.edu/tag/021R)
* [Stacks Project, Tag 02WQ](https://stacks.math.columbia.edu/tag/02WQ)
* [Stacks Project, Tag 0ADK](https://stacks.math.columbia.edu/tag/0ADK)
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Cardinal Ordinal

universe u

namespace AlgebraicGeometry

/-- **A big fppf site with a prescribed cutoff.** Any cardinal satisfying the three cardinal
axioms of `AlgebraicGeometry.BigFppfSite` — uncountable, a strong prelimit, of uncountable
cofinality — is the cutoff of a big fppf site containing any prescribed small set of schemes of
size below it.

This is `AlgebraicGeometry.BigFppfSite.exists_containing` with the cutoff an argument instead of
being chosen by Stacks 000J: the chosen covering system comes from `exists_covBounded_isSite`
applied to the fppf covering families of `Sch_κ`, whose site axioms
`AlgebraicGeometry.isSite_fppfCutoff` provides for every cardinal, and the set of initially
prescribed coverings is empty. -/
public theorem BigFppfSite.exists_cutoff_eq (κ : Cardinal.{u}) (hκ₀ : ℵ₀ < κ)
    (hκ₁ : Cardinal.IsStrongPrelimit κ) (hκ₂ : ℵ₀ < κ.ord.cof)
    (S₀ : Set Scheme.{u}) [Small.{u} S₀] (hκS₀ : ∀ X ∈ S₀, X.size < κ) :
    ∃ B : BigFppfSite.{u}, B.cutoff = κ ∧ ∀ X ∈ S₀, B.Contains X := by
  let Cov₀ : Set.{u + 2} (Covering.{u + 1, u, u + 1} (AlgebraicGeometry.SchemeBelow κ)) := ∅
  obtain ⟨κc, α, hα, -, hsiteκ, hrep⟩ := _root_.exists_covBounded_isSite
    (AlgebraicGeometry.IsFppfCovering (κ := κ)) (isSite_fppfCutoff κ) Cov₀ (fun _ h ↦ h.elim)
  exact ⟨{
    initialSchemes := S₀
    initialSchemes_small := inferInstance
    cutoff := κ
    aleph0_lt_cutoff := hκ₀
    cutoff_isStrongPrelimit := hκ₁
    aleph0_lt_cutoff_cof := hκ₂
    initialSchemes_mem := hκS₀
    initialCoverings := Cov₀
    initialCoverings_small := inferInstance
    initialCoverings_supported := by simp [Cov₀]
    coveringBound := κc
    coveringOrdinal := α
    coveringOrdinal_isSuccLimit := hα
    initialCoverings_mem := by simp [Cov₀]
    coverings_isSite := hsiteκ
    fppf_has_representative := hrep
  }, rfl, hκS₀⟩

/-- **The cofinality bound on a coproduct index cannot be weakened to a bound by the cutoff.**
There are a big fppf site `B`, a scheme `S` it contains, and a family of algebraic spaces over
`S` — all of them representable — indexed by a type of cardinality strictly below `B.cutoff`,
which is not admissible as a coproduct index and whose coproduct in sheaves is not an algebraic
space over `S`: it has no algebraic sheaf coproduct whatever.

The site has cutoff `AlgebraicGeometry.singularCutoff = ℶ_{ω₁}`, of cofinality `ℵ₁`, and the
family is the one indexed by `ω₁` whose `a`-th member is an object of size at least `ℶ_a`, so
that the members' sizes are cofinal in the cutoff. No atlas inside the site can cover such a
family, by
`AlgebraicGeometry.Space.Descent.not_nonempty_algebraicSheafCoproduct_of_cofinal_size`. -/
public theorem exists_family_lt_cutoff_not_nonempty_algebraicSheafCoproduct :
    ∃ (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (I : Type u)
      (T : I → BigFppfOver B S hS),
      #I < B.cutoff ∧ ¬ B.AdmitsCoproductIndex I ∧
        ¬ Nonempty (Space.Descent.AlgebraicSheafCoproduct (fun i => yoneda.obj (T i))
          (fun i => isAlgebraicSpace_yoneda B S hS (T i))) := by
  classical
  have hbase : (Spec (CommRingCat.of (ULift.{u} ℤ))).size < singularCutoff.{u} := by
    rw [Scheme.size_Spec]
    exact (max_le le_rfl (Cardinal.mk_le_aleph0)).trans_lt aleph0_lt_singularCutoff
  obtain ⟨B, hcut, hcontains⟩ := BigFppfSite.exists_cutoff_eq singularCutoff.{u}
    aleph0_lt_singularCutoff isStrongPrelimit_singularCutoff
    (cof_ord_singularCutoff.{u} ▸ Cardinal.aleph0_lt_aleph_one)
    {Spec (CommRingCat.of (ULift.{u} ℤ))} (by rintro X rfl; exact hbase)
  have hS : B.Contains (Spec (CommRingCat.of (ULift.{u} ℤ))) := hcontains _ rfl
  have hne : Nonempty (Spec (CommRingCat.of (ULift.{u} ℤ))) := inferInstance
  have hlt : ∀ a : Set.Iio (ω₁ : Ordinal.{u}),
      Cardinal.preBeth (a : Ordinal.{u}) < B.cutoff := by
    intro a
    rw [hcut, singularCutoff]
    exact Cardinal.preBeth_strictMono a.2
  choose T hT using fun i : Shrink.{u} (Set.Iio (ω₁ : Ordinal.{u})) =>
    BigFppfOver.exists_size_ge B _ hS hne
      (max (Spec (CommRingCat.of (ULift.{u} ℤ))).size
        (Cardinal.preBeth (((equivShrink.{u} (Set.Iio (ω₁ : Ordinal.{u}))).symm i :
          Set.Iio (ω₁ : Ordinal.{u})) : Ordinal.{u})))
      (le_max_left _ _) (max_lt hS (hlt _))
  have hmkI : #(Shrink.{u} (Set.Iio (ω₁ : Ordinal.{u}))) = ℵ₁ := mk_shrink_Iio_omega_one
  refine ⟨B, _, hS, Shrink.{u} (Set.Iio (ω₁ : Ordinal.{u})), T, ?_, ?_, ?_⟩
  · rw [hmkI, hcut]
    exact aleph_one_lt_singularCutoff
  · rintro ⟨hadm⟩
    rw [Cardinal.mk_congr (equivShrink.{u} (Shrink.{u} (Set.Iio (ω₁ : Ordinal.{u})))).symm,
      hmkI, hcut, cof_ord_singularCutoff] at hadm
    exact absurd hadm (lt_irrefl _)
  · refine Space.Descent.not_nonempty_algebraicSheafCoproduct_of_cofinal_size T ?_
    intro ν hν
    rw [hcut] at hν
    obtain ⟨a, ha⟩ := exists_lt_preBeth_of_lt_singularCutoff hν
    refine ⟨equivShrink.{u} (Set.Iio (ω₁ : Ordinal.{u})) a, ha.trans_le (le_trans ?_ (hT _))⟩
    simp

end AlgebraicGeometry

end
