module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.KummerTheory.BaseLocalRoots
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.KummerTheory.ComparisonBijective
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.KummerTheory.ComparisonCompatibilities
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.KummerTheory.ExactSequence

/-!
# Stacks 040Q: the group of pairs is the first cohomology of the roots of unity

**Tag 040Q is proved here.**  It identifies the isomorphism classes of pairs `(ℒ, α)` on a scheme
`S` — an invertible `𝒪_S`-module with a trivialization of its `n`-th tensor power — with
`H¹((Sch/S)_τ, μ_n)`, as abelian groups: étale for `n` invertible on `S`, and fppf and syntomic
for every positive `n` with no invertibility hypothesis.

Both groups are extensions of the `n`-torsion of `Pic(S)` by the global units modulo `n`-th
powers, the comparison `AlgebraicGeometry.basePairCohomologyClassHom` is a homomorphism of
abelian groups, and `Stacks.Kummer.bijective_of_comparison` turns a compatibility with both ends
into bijectivity.  Its six hypotheses are discharged from the library:

* `hrc`, the compatibility with the right-hand end, is
  `AlgebraicGeometry.basePairPicardHom_basePairCohomologyClassHom`;
* `hci`, the compatibility with the left-hand end, is
  `AlgebraicGeometry.basePairCohomologyClass_unitPair`;
* `hker`, that a class of pairs with trivial Picard class comes from a global unit, is
  `AlgebraicGeometry.pairSheafClassHom_eq_zero_iff`;
* `hinj`, that a unit with vanishing Kummer boundary gives the zero class of pairs, is
  `AlgebraicGeometry.kummerBoundary_eq_zero_iff` and
  `AlgebraicGeometry.unitPairHom_eq_zero_iff`;
* `hkerH`, that a cohomology class with vanishing Picard class is a Kummer boundary, is
  `AlgebraicGeometry.exists_kummerBoundary_iff`;
* `himg`, that the Picard class of a cohomology class is `n`-torsion and so comes from a pair,
  is `AlgebraicGeometry.exists_kummerFirstCohomologyMap_iff` and
  `AlgebraicGeometry.exists_pairSheafClassHom_eq_iff`.

## Main results

* `AlgebraicGeometry.basePairCohomologyClassHom_bijective`: the comparison homomorphism of
  Tag 040Q is bijective.
* `AlgebraicGeometry.basePairClassesAddEquivH1`: hence **the canonical identification of the
  group of pairs with `H¹((Sch/S)_τ, μ_n)`**, as abelian groups.
* `AlgebraicGeometry.pairClassesAddEquivH1Etale`,
  `AlgebraicGeometry.pairClassesAddEquivH1Fppf` and
  `AlgebraicGeometry.pairClassesAddEquivH1Syntomic`: **the three statements of Tag 040Q**, with
  the local-roots, short-exactness and terminal-object hypotheses discharged.

## Implementation notes

The `HasSheafify` and `HasExt` binders are instance arguments, as everywhere in this chapter:
the universe of the `Ext`-groups is a parameter of `HasExt` and is not determined by the scheme.

## References

* [Stacks Project, Tag 03P8](https://stacks.math.columbia.edu/tag/03P8)
* [Stacks Project, Tag 040Q](https://stacks.math.columbia.edu/tag/040Q)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Cohomology.Torsors.Generators (LocalRoots)
open Stacks.SheafOfModules.Picard (PicardGroup)

universe u

namespace AlgebraicGeometry

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (τ : SiteKind) (n : ℕ)

attribute [local instance] baseSchemeFunctions_hasWeakSheafify
  baseSchemeFunctions_wEqualsLocallyBijective

variable [∀ σ : SiteKind, HasSheafify (BigFppfOver.baseOverTopology B S hS σ) AddCommGrpCat.{u}]
  [∀ σ : SiteKind, HasExt.{u} (Sheaf (BigFppfOver.baseOverTopology B S hS σ) AddCommGrpCat.{u})]

/-- **The comparison homomorphism of Tag 040Q is bijective.**

All six hypotheses of `Stacks.Kummer.bijective_of_comparison` are discharged from the library;
see the head of this file. -/
@[stacks 040Q "the comparison homomorphism from the isomorphism classes of pairs to H^1 of the \
roots of unity is bijective. The group isomorphism the tag asserts is read off from this in \
AlgebraicGeometry.basePairClassesAddEquivH1, and the three statements of the tag -- etale for n \
invertible on the base, fppf and syntomic for n positive -- in the three declarations after it"]
public theorem basePairCohomologyClassHom_bijective
    (hroot : LocalRoots (BigFppfOver.baseRingedSite B S hS τ) n)
    (hSE : (kummerSequence (BigFppfOver.baseOverTopology B S hS τ)
      (BigFppfOver.toScheme B S hS) (unitsPresheaf_isSheaf_base B S hS τ) n).ShortExact)
    (hT : IsTerminal (C := BigFppfOver B S hS) (Over.mk (𝟙 (B.obj hS)))) :
    Function.Bijective (basePairCohomologyClassHom B S hS τ n hroot) := by
  refine Stacks.Kummer.bijective_of_comparison
    (basePairCohomologyClassHom B S hS τ n hroot) (pairSheafClassHom S n)
    (basePairPicardHom B S hS τ n) (unitPairHom S n)
    (fun u => -kummerBoundary (BigFppfOver.baseOverTopology B S hS τ)
      (BigFppfOver.toScheme B S hS) (unitsPresheaf_isSheaf_base B S hS τ) n hSE hT
        (Additive.toMul u))
    (basePairPicardHom_basePairCohomologyClassHom B S hS τ n hroot)
    (fun u => basePairCohomologyClass_unitPair B S hS τ n hroot hSE hT (Additive.toMul u))
    (fun a ha => (pairSheafClassHom_eq_zero_iff S n a).1 ha) ?_ ?_ ?_
  · intro u hu
    refine (unitPairHom_eq_zero_iff S n u).2 ?_
    exact (kummerBoundary_eq_zero_iff (BigFppfOver.baseOverTopology B S hS τ)
      (BigFppfOver.toScheme B S hS) (unitsPresheaf_isSheaf_base B S hS τ) n hSE hT
      (Additive.toMul u)).1 (neg_eq_zero.1 hu)
  · intro y hy
    have hy' : Sheaf.H.map (kernel.ι (powerSheaf (BigFppfOver.baseOverTopology B S hS τ)
        (BigFppfOver.toScheme B S hS) (unitsPresheaf_isSheaf_base B S hS τ) n)) 1 y = 0 :=
      (AddEquiv.map_eq_zero_iff
        (Stacks.Picard.AllTopologies.baseH1UnitsAddEquivSchemePicardGroup B S hS τ)).1 hy
    obtain ⟨a, ha⟩ := (exists_kummerBoundary_iff (BigFppfOver.baseOverTopology B S hS τ)
      (BigFppfOver.toScheme B S hS) (unitsPresheaf_isSheaf_base B S hS τ) n hSE hT (-y)).2
      ((map_neg (Sheaf.H.map (kernel.ι (powerSheaf (BigFppfOver.baseOverTopology B S hS τ)
        (BigFppfOver.toScheme B S hS) (unitsPresheaf_isSheaf_base B S hS τ) n)) 1) y).trans
        (neg_eq_zero.2 hy'))
    exact ⟨Additive.ofMul a, (congrArg Neg.neg ha).trans (neg_neg y)⟩
  · intro y
    refine (exists_pairSheafClassHom_eq_iff S n (basePairPicardHom B S hS τ n y)).2 ?_
    have hzero : n • Sheaf.H.map (kernel.ι (powerSheaf
        (BigFppfOver.baseOverTopology B S hS τ) (BigFppfOver.toScheme B S hS)
        (unitsPresheaf_isSheaf_base B S hS τ) n)) 1 y = 0 :=
      (exists_kummerFirstCohomologyMap_iff (BigFppfOver.baseOverTopology B S hS τ)
        (BigFppfOver.toScheme B S hS) (unitsPresheaf_isSheaf_base B S hS τ) n hSE _).1 ⟨y, rfl⟩
    refine Eq.trans (map_nsmul
      (Stacks.Picard.AllTopologies.baseH1UnitsAddEquivSchemePicardGroup B S hS τ) n _).symm ?_
    exact (congrArg (fun z =>
      Stacks.Picard.AllTopologies.baseH1UnitsAddEquivSchemePicardGroup B S hS τ z) hzero).trans
      (map_zero _)

/-- **The canonical identification of Tag 040Q**, on the big `τ`-site of `S`: the group of pairs
`(ℒ, α)` up to isomorphism is `H¹((Sch/S)_τ, μ_n)`.

`AlgebraicGeometry.basePairCohomologyClassHom` is a homomorphism of abelian groups and
`AlgebraicGeometry.basePairCohomologyClassHom_bijective` says it is bijective, so it is an
isomorphism. -/
public noncomputable def basePairClassesAddEquivH1
    (hroot : LocalRoots (BigFppfOver.baseRingedSite B S hS τ) n)
    (hSE : (kummerSequence (BigFppfOver.baseOverTopology B S hS τ)
      (BigFppfOver.toScheme B S hS) (unitsPresheaf_isSheaf_base B S hS τ) n).ShortExact)
    (hT : IsTerminal (C := BigFppfOver B S hS) (Over.mk (𝟙 (B.obj hS)))) :
    PairClasses S n ≃+
      Sheaf.H (rootsOfUnitySheaf (BigFppfOver.baseOverTopology B S hS τ)
        (BigFppfOver.toScheme B S hS) (unitsPresheaf_isSheaf_base B S hS τ) n) 1 :=
  AddEquiv.ofBijective (basePairCohomologyClassHom B S hS τ n hroot)
    (basePairCohomologyClassHom_bijective B S hS τ n hroot hSE hT)

/-! ### Stacks 040Q

The three statements of the tag.  The hypotheses of
`AlgebraicGeometry.basePairClassesAddEquivH1` are discharged from the library: `hroot` by
`AlgebraicGeometry.BaseLocalRoots`, `hSE` by `AlgebraicGeometry.BaseSites`, and `hT` by
`CategoryTheory.Over.mkIdTerminal`, the big `τ`-site over `S` being a category of objects over
`S` in which `S / S` is terminal. -/

/-- **Stacks Project, Tag 040Q, the étale statement.**  For `n` invertible on `S`,
`H¹_étale(S, μ_n)` is the group of pairs `(ℒ, α)` — an invertible `𝒪_S`-module with a
trivialization of its `n`-th tensor power — up to isomorphism. -/
@[stacks 040Q "the etale statement: for n invertible on S, H^1_etale(S, mu_n) is the group of \
pairs (L, alpha) up to isomorphism, as an isomorphism of abelian groups"]
public noncomputable def pairClassesAddEquivH1Etale
    (hn : IsUnit (n : Scheme.Γ.obj (op S))) :
    PairClasses S n ≃+
      Sheaf.H (rootsOfUnitySheaf (BigFppfOver.baseOverTopology B S hS .etale)
        (BigFppfOver.toScheme B S hS) (unitsPresheaf_isSheaf_base B S hS .etale) n) 1 :=
  basePairClassesAddEquivH1 B S hS .etale n (localRoots_baseRingedSite_etale B S hS n hn)
    (kummerSequence_shortExact_base_etale B S hS n hn) Over.mkIdTerminal

/-- **Stacks Project, Tag 040Q, the fppf statement.**  For every positive `n`, with no
invertibility hypothesis, `H¹_fppf(S, μ_n)` is the group of pairs `(ℒ, α)` up to
isomorphism. -/
@[stacks 040Q "the fppf statement: for every positive n, with no invertibility hypothesis, \
H^1_fppf(S, mu_n) is the group of pairs (L, alpha) up to isomorphism, as an isomorphism of \
abelian groups"]
public noncomputable def pairClassesAddEquivH1Fppf (hn : 0 < n) :
    PairClasses S n ≃+
      Sheaf.H (rootsOfUnitySheaf (BigFppfOver.baseOverTopology B S hS .fppf)
        (BigFppfOver.toScheme B S hS) (unitsPresheaf_isSheaf_base B S hS .fppf) n) 1 :=
  basePairClassesAddEquivH1 B S hS .fppf n (localRoots_baseRingedSite_fppf B S hS n hn)
    (kummerSequence_shortExact_base_fppf B S hS n hn) Over.mkIdTerminal

/-- **Stacks Project, Tag 040Q, the syntomic statement.**  The same with fppf replaced by
syntomic. -/
@[stacks 040Q "the syntomic statement: for every positive n, with no invertibility hypothesis, \
H^1_syntomic(S, mu_n) is the group of pairs (L, alpha) up to isomorphism, as an isomorphism of \
abelian groups"]
public noncomputable def pairClassesAddEquivH1Syntomic (hn : 0 < n) :
    PairClasses S n ≃+
      Sheaf.H (rootsOfUnitySheaf (BigFppfOver.baseOverTopology B S hS .syntomic)
        (BigFppfOver.toScheme B S hS) (unitsPresheaf_isSheaf_base B S hS .syntomic) n) 1 :=
  basePairClassesAddEquivH1 B S hS .syntomic n
    (localRoots_baseRingedSite_syntomic B S hS n hn)
    (kummerSequence_shortExact_base_syntomic B S hS n hn) Over.mkIdTerminal

end AlgebraicGeometry

end
