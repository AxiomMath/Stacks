module

public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.ChowCohomologyCompositionRing
public import StacksFrontier.AlgebraicGeometry.Chow.BabyLocalizedChern.ClosedCoverClass
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassArbitraryRank.TopChernClass
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassDerived.Centrality
public import StacksFrontier.AlgebraicGeometry.Chow.ClopenDecomposition.Coproduct
public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.BivariantChernCentral
public import StacksFrontier.AlgebraicGeometry.Chow.SectionZeroScheme.ArbitraryRankDual
public import StacksFrontier.AlgebraicGeometry.Chow.SubbundleTopChern.ArbitraryRank

/-!
# Chern classes and rank of a finite locally free module of arbitrary rank

Let `(S, δ)` be as in Situation 02QL, let `X` be locally of finite type over `S` and let `ℰ` be a
finite locally free `𝒪_X`-module whose rank need not be constant. Write
`X = X_0 ⊔ X_1 ⊔ X_2 ⊔ …` for the decomposition into the open and closed loci `X_r` where the
rank of `ℰ` is `r`. **Stacks 0ESW** observes:

* by Stacks 0FDZ, `A^p(X) = ∏_r A^p(X_r)`;
* hence `c_p(ℰ) ∈ A^p(X)` may be defined as the class with components `c_p(ℰ|_{X_r})`, and it is
  the bivariant class acting on each `X'_r` by the operation `c_p(ℰ|_{X'_r}) ∩ -`;
* the total Chern class `c(ℰ) = c_0(ℰ) + c_1(ℰ) + …` lies in the completed bivariant ring
  `A^*(X)^∧` of Stacks 0FE0;
* the rank `r(ℰ) ∈ A^0(X)` is the operation `(α_r) ↦ (r α_r)`;
* `c_p(ℰ)` and `r(ℰ)` lie in the center of `A^*(X)`.

Everything is at the Gysin system `Stacks.Chow.gysinSystemOfInvertible` of the first Chern class
of an invertible module, for which the compatibilities used by Stacks 0FDZ are theorems, and the
constant-rank classes are the bivariant Chern classes `Stacks.Chow.GenuineChern.chernClass` of
Stacks 0B7H.

## Main definitions

* `Stacks.Chow.SectionZeroScheme.rankLocusChowCohomologyEquivOfInvertible` —
  `A^p(X) = ∏_r A^p(X_r)`.
* `Stacks.Chow.SectionZeroScheme.totalChernComponent` — the degree `p` part of `c(ℰ)`, for
  `p ∈ ℤ`.
* `Stacks.Chow.SectionZeroScheme.totalChernClassCompleted` — `c(ℰ) ∈ A^*(X)^∧`.
* `Stacks.Chow.SectionZeroScheme.rankClassOfLocallyFree` — `r(ℰ) ∈ A^0(X)`.

## Main results

* `Stacks.Chow.SectionZeroScheme.chernClassOfLocallyFree_spec` — `c_p(ℰ)` is the unique class
  whose restriction to `X_r` is `c_p(ℰ|_{X_r})`, and `0` when `p > r`.
* `Stacks.Chow.SectionZeroScheme.idRule_chernClassOfLocallyFree_of_rank` — on a test scheme
  `f : X' ⟶ X` along which `f^*ℰ` has constant rank `r`, `c_p(ℰ) ∩ - = c_p(f^*ℰ) ∩ -`.
* `Stacks.Chow.SectionZeroScheme.rankClassOfLocallyFree_spec`,
  `Stacks.Chow.SectionZeroScheme.idRule_rankClassOfLocallyFree_of_rank` — `r(ℰ)` restricts to
  `r · 1` on `X_r` and acts by multiplication by `r` on every test scheme along which `ℰ` has rank
  `r`.
* `Stacks.Chow.SectionZeroScheme.chernClassOfLocallyFree_mem_center`,
  `Stacks.Chow.SectionZeroScheme.rankClassOfLocallyFree_mem_center` — centrality in `A^*(X)`.

## References

* [Stacks Project, Tag 0ESW](https://stacks.math.columbia.edu/tag/0ESW)
* [Stacks Project, Tag 0FDZ](https://stacks.math.columbia.edu/tag/0FDZ)
* [Stacks Project, Tag 0FE0](https://stacks.math.columbia.edu/tag/0FE0)
* [Stacks Project, Tag 0B7H](https://stacks.math.columbia.edu/tag/0B7H)
* [Stacks Project, Tag 02UA](https://stacks.math.columbia.edu/tag/02UA)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow.SectionZeroScheme

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  (E : X.Modules) [hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E]

/-! ### Restriction to the rank loci -/

/-- **Stacks 0ESW, the decomposition of Chow cohomology.** `A^p(X) = ∏_{r ≥ 0} A^p(X_r)` for the
decomposition of `X` by the rank of `ℰ`: restriction to the rank loci is an isomorphism onto the
product (Stacks 0FDZ). -/
@[stacks 0ESW "A^p(X) = ∏_r A^p(X_r) for the rank decomposition X = ∐ X_r of a finite locally \
free module (via 0FDZ), at the Gysin system of the first Chern class rule, nothing assumed"]
def rankLocusChowCohomologyEquivOfInvertible (p : ℤ) :
    chowCohomologyComponent C (gysinSystemOfInvertible C) sX p ≃+
      ∀ r : ℕ, chowCohomologyComponent C (gysinSystemOfInvertible C) ((rankLocus E r).ι ≫ sX) p :=
  rankLocusChowCohomologyEquiv C (gysinSystemOfInvertible C) sX E
    (gysinSystemOfInvertible_isNaturalUnderOpenImmersion C)
    (gysinSystemOfInvertible_isNaturalUnderOpensRestriction C)
    (gysinSystemOfInvertible_isNaturalUnderPullbackComp C) p

/-- The components of `A^p(X) = ∏_r A^p(X_r)` are the restrictions to the rank loci. -/
theorem rankLocusChowCohomologyEquivOfInvertible_apply {p : ℤ}
    (c : chowCohomologyComponent C (gysinSystemOfInvertible C) sX p) (r : ℕ) :
    rankLocusChowCohomologyEquivOfInvertible C sX E p c r =
      chowCohomologyRestriction C (gysinSystemOfInvertible C) sX (rankLocus E r).ι p
        (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C) c :=
  rankLocusRestriction_eq_chowCohomologyRestriction C sX E c r

/-- A Chow cohomology class of `X` is determined by its restrictions to the rank loci. -/
theorem eq_of_chowCohomologyRestriction_rankLocus_eq {p : ℤ}
    {c d : chowCohomologyComponent C (gysinSystemOfInvertible C) sX p}
    (h : ∀ r : ℕ, chowCohomologyRestriction C (gysinSystemOfInvertible C) sX (rankLocus E r).ι p
      (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C) c =
      chowCohomologyRestriction C (gysinSystemOfInvertible C) sX (rankLocus E r).ι p
        (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C) d) : c = d :=
  (rankLocusChowCohomologyEquivOfInvertible C sX E p).injective <| funext fun r ↦ by
    rw [rankLocusChowCohomologyEquivOfInvertible_apply,
      rankLocusChowCohomologyEquivOfInvertible_apply, h r]

/-! ### The operation on a test scheme along which the rank is constant -/

/-- **The operation of a class on a test scheme factoring through `π`** is the operation of its
restriction along `π`. -/
theorem idRule_heq_of_chowCohomologyRestriction_eq {W : Scheme.{u}} (π : W ⟶ X)
    [LocallyOfFiniteType π] {p : ℤ}
    (c : chowCohomologyComponent C (gysinSystemOfInvertible C) sX p)
    (d : chowCohomologyComponent C (gysinSystemOfInvertible C) (π ≫ sX) p)
    (hcd : chowCohomologyRestriction C (gysinSystemOfInvertible C) sX π p
      (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C) c = d)
    {V : Scheme.{u}} (t : V ⟶ X) [LocallyOfFiniteType t] (v : V ⟶ W) [LocallyOfFiniteType v]
    (hv : v ≫ π = t) (k : ℤ) (y : chowGroup C (t ≫ sX) k)
    (y' : chowGroup C (v ≫ (π ≫ sX)) k) (hy : y' ≍ y) :
    c.idRule C sX (gysinSystemOfInvertible C) t k y ≍
      d.idRule C (π ≫ sX) (gysinSystemOfInvertible C) v k y' := by
  subst hv hcd
  exact (BivariantClass.idRule_chowCohomologyRestriction_heq π c v k y' y hy).symm

/-- The zero classes for two equal structure morphisms are heterogeneously equal. -/
theorem zero_heq_zero_of_eq {T : Scheme.{u}} {q q' : T ⟶ C.S} [LocallyOfFiniteType q]
    [LocallyOfFiniteType q'] (h : q = q') (k : ℤ) :
    (0 : chowGroup C q k) ≍ (0 : chowGroup C q' k) := by
  subst h
  rfl

/-- A test scheme along which `ℰ` has constant rank `r` maps into the rank locus `X_r`. -/
theorem range_subset_range_rankLocus_ι {X' : Scheme.{u}} (f : X' ⟶ X) (r : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Modules.pullback f).obj E) r] :
    Set.range f ⊆ Set.range (rankLocus E r).ι := by
  rintro _ ⟨x', rfl⟩
  rw [Scheme.Opens.range_ι]
  exact mem_rankLocus_of_isFiniteLocallyFreeOfRank_pullback E f r x'

/-- If `f^*ℰ` has constant rank `r` and `c` restricts to `d` on the rank locus `X_r`, then `f`
factors through `X_r` as `f'` and the operation of `c` on `f` is that of `d` on `f'`. -/
private theorem exists_factorization_idRule_heq_of_rank (r : ℕ) {X' : Scheme.{u}} (f : X' ⟶ X)
    [LocallyOfFiniteType f]
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Modules.pullback f).obj E) r] {p : ℤ}
    (c : chowCohomologyComponent C (gysinSystemOfInvertible C) sX p)
    (d : chowCohomologyComponent C (gysinSystemOfInvertible C) ((rankLocus E r).ι ≫ sX) p)
    (hcd : chowCohomologyRestriction C (gysinSystemOfInvertible C) sX (rankLocus E r).ι p
      (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C) c = d) (k : ℤ)
    (α : chowGroup C (f ≫ sX) k) :
    ∃ (f' : X' ⟶ rankLocus E r) (_ : LocallyOfFiniteType f')
      (hf' : f' ≫ (rankLocus E r).ι = f),
        c.idRule C sX (gysinSystemOfInvertible C) f k α ≍
          d.idRule C ((rankLocus E r).ι ≫ sX) (gysinSystemOfInvertible C) f' k
            (chowGroupCongr C (by rw [← hf', Category.assoc]) k α) := by
  set f' := IsOpenImmersion.lift (rankLocus E r).ι f (range_subset_range_rankLocus_ι E f r)
    with hf'def
  have hf' : f' ≫ (rankLocus E r).ι = f := IsOpenImmersion.lift_fac _ f _
  have : LocallyOfFiniteType f' := by
    have : LocallyOfFiniteType (f' ≫ (rankLocus E r).ι) := hf' ▸ inferInstance
    exact locallyOfFiniteType_of_comp f' (rankLocus E r).ι
  refine ⟨f', this, hf', ?_⟩
  clear_value f'
  subst hf'
  exact idRule_heq_of_chowCohomologyRestriction_eq C sX _ c d hcd (f' ≫ _) f' rfl k α _
    (chowGroupCongr_heq C _ k α)

/-- **Stacks 0ESW, the operation of `c_p(ℰ)`.** On a test scheme `f : X' ⟶ X` along which `f^*ℰ`
has constant rank `r` — for instance the part `X'_r` of any test scheme lying over `X_r` — the
class `c_p(ℰ)` acts by the already defined operation `c_p(f^*ℰ) ∩ -` of Stacks 0B7H, which is zero
when `p > r`. -/
@[stacks 0ESW "c_p(E) acts on the factors X'_r by the already defined operations \
c_p(E|_{X'_r}) ∩ -: on every test scheme along which E has constant rank r the operation of \
c_p(E) is the cap product c_p(f^*E) ∩ - of 0B7H (zero for p > r)"]
theorem idRule_chernClassOfLocallyFree_of_rank (r p : ℕ) {X' : Scheme.{u}} (f : X' ⟶ X)
    [LocallyOfFiniteType f]
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Modules.pullback f).obj E) r] (k : ℤ) (α : chowGroup C (f ≫ sX) k) :
    (chernClassOfLocallyFree E C sX p).idRule C sX (gysinSystemOfInvertible C) f k α =
      if h : p ≤ r then
        GenuineChern.chernCap C r (f ≫ sX) ((Scheme.Modules.pullback f).obj E) k
          ⟨p, Nat.lt_succ_of_le h⟩ α
      else 0 := by
  have hEU := isFiniteLocallyFreeOfRank_pullback_rankLocus E r
  have hres := chowCohomologyRestriction_chernClassOfLocallyFree E C sX r p (rankLocus E r) rfl
  set U := rankLocus E r with hU
  obtain ⟨f', _, hf', hh⟩ := exists_factorization_idRule_heq_of_rank C sX E r f
    (chernClassOfLocallyFree E C sX p) _ hres k α
  subst hf'
  have : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Modules.pullback f').obj ((Scheme.Modules.pullback U.ι).obj E)) r :=
    AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback _ _ r
  set β : chowGroup C (f' ≫ (U.ι ≫ sX)) k :=
    chowGroupCongr C (Category.assoc f' U.ι sX).symm k α with hβ
  have hβα : β ≍ α := chowGroupCongr_heq C _ k α
  split_ifs with h
  · rw [dite_eq_left h] at hh
    rw [GenuineChern.idRule_chernClass] at hh
    refine eq_of_heq (hh.trans ?_)
    refine (heq_of_eq (GenuineChern.chernCap_congr C (f' ≫ U.ι ≫ sX)
      (E := (Scheme.Modules.pullback f').obj ((Scheme.Modules.pullback U.ι).obj E))
      (E' := (Scheme.Modules.pullback (f' ≫ U.ι)).obj E) r
      ((Scheme.Modules.pullbackComp f' U.ι).app E) k ⟨p, Nat.lt_succ_of_le h⟩ β)).trans ?_
    exact chernCap_heq_of_base_eq C (Category.assoc f' U.ι sX).symm _ r k _ hβα
  · rw [dite_eq_right h, BivariantClass.idRule_zero] at hh
    exact eq_of_heq (hh.trans (zero_heq_zero_of_eq C (Category.assoc f' U.ι sX).symm _))

/-- On the part `X'_r = g⁻¹(X_r)` of a test scheme `g : X' ⟶ X` lying over the rank locus `X_r`,
the pullback of `ℰ` has constant rank `r`. -/
theorem isFiniteLocallyFreeOfRank_pullback_preimage_rankLocus {X' : Scheme.{u}} (g : X' ⟶ X)
    (r : ℕ) :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Modules.pullback ((g ⁻¹ᵁ rankLocus E r).ι ≫ g)).obj E) r := by
  have := isFiniteLocallyFreeOfRank_pullback_rankLocus E r
  have : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Modules.pullback (g ∣_ rankLocus E r)).obj
        ((Scheme.Modules.pullback (rankLocus E r).ι).obj E)) r :=
    AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback _ _ r
  exact AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso.{u, u, u}
    (((Scheme.Modules.pullbackComp (g ∣_ rankLocus E r) (rankLocus E r).ι).app E) ≪≫
      ((Scheme.Modules.pullbackCongr (morphismRestrict_ι g (rankLocus E r))).app E)) ‹_›

/-- The operation of a class on a test scheme, at heterogeneously equal arguments in equal
degrees. -/
theorem idRule_heq_of_heq {p : ℤ} (c : chowCohomologyComponent C (gysinSystemOfInvertible C) sX p)
    {T : Scheme.{u}} (t : T ⟶ X) [LocallyOfFiniteType t] {k k' : ℤ} (hk : k = k')
    {y : chowGroup C (t ≫ sX) k} {y' : chowGroup C (t ≫ sX) k'} (hy : y ≍ y') :
    c.idRule C sX (gysinSystemOfInvertible C) t k y ≍
      c.idRule C sX (gysinSystemOfInvertible C) t k' y' := by
  subst hk
  cases hy
  rfl

/-- Restriction to an open subscheme is heterogeneously equal to the flat pullback of relative
dimension `0`. -/
private theorem chowGroupRestrict_heq_flatPullbackChow {Y Z : Scheme.{u}} {sZ : Z ⟶ C.S}
    {sY : Y ⟶ C.S} [LocallyOfFiniteType sZ] [LocallyOfFiniteType sY] (j : Y ⟶ Z)
    [IsOpenImmersion j] (hj : j ≫ sZ = sY) (m : ℤ) (x : chowGroup C sZ m) :
    chowGroupRestrict C sZ sY j hj m x ≍
      flatPullbackChow C sY sZ j hj 0 (relativeDimension_of_isOpenImmersion j) m
        (flatPullbackFactorsThroughRationalEquivalence_general C _ _ j _ 0 _ m) x := by
  rw [← cast_flatPullbackChow_eq_chowGroupRestrict C sZ sY j hj m (by simp)]
  exact eqRec_heq _ _

/-- **Stacks 0ESW, explicitly.** For a test scheme `g : X' ⟶ X` locally of finite type, with the
induced decomposition `X' = ∐ X'_r`, `X'_r = g⁻¹(X_r)`, the class `c_p(ℰ)` preserves the
decomposition `CH_*(X') = ∏_r CH_*(X'_r)` and acts on the factor `CH_*(X'_r)` by the already
defined operation `c_p(ℰ|_{X'_r}) ∩ -` of Stacks 0B7H (zero for `p > r`): restricting
`c_p(ℰ) ∩ α` to `X'_r` gives `c_p(ℰ|_{X'_r}) ∩ (α|_{X'_r})`. -/
@[stacks 0ESW "explicit form: for every X' → X locally of finite type, c_p(E) preserves the \
decomposition CH_*(X') = ∏_r CH_*(X'_r) and acts on the factor X'_r by c_p(E|_{X'_r}) ∩ -"]
theorem chowGroupRestrict_idRule_chernClassOfLocallyFree (r p : ℕ) {X' : Scheme.{u}}
    (g : X' ⟶ X) [LocallyOfFiniteType g] (k : ℤ) (α : chowGroup C (g ≫ sX) k) :
    haveI := isFiniteLocallyFreeOfRank_pullback_preimage_rankLocus E g r
    chowGroupRestrict C (g ≫ sX) (((g ⁻¹ᵁ rankLocus E r).ι ≫ g) ≫ sX) (g ⁻¹ᵁ rankLocus E r).ι
        (Category.assoc _ _ _).symm ((k : ℤ) - (p : ℤ))
        ((chernClassOfLocallyFree E C sX p).idRule C sX (gysinSystemOfInvertible C) g k α) =
      if h : p ≤ r then
        GenuineChern.chernCap C r (((g ⁻¹ᵁ rankLocus E r).ι ≫ g) ≫ sX)
          ((Scheme.Modules.pullback ((g ⁻¹ᵁ rankLocus E r).ι ≫ g)).obj E) k
          ⟨p, Nat.lt_succ_of_le h⟩
          (chowGroupRestrict C (g ≫ sX) (((g ⁻¹ᵁ rankLocus E r).ι ≫ g) ≫ sX)
            (g ⁻¹ᵁ rankLocus E r).ι (Category.assoc _ _ _).symm k α)
      else 0 := by
  have := isFiniteLocallyFreeOfRank_pullback_preimage_rankLocus E g r
  set W := g ⁻¹ᵁ rankLocus E r
  have hr := relativeDimension_of_isOpenImmersion W.ι
  have h0 : ∀ m : ℤ, m + ((0 : ℕ) : ℤ) = m := fun m ↦ by simp
  have hflat := idRule_flatPullbackChow_heq C sX (chernClassOfLocallyFree E C sX p) g (W.ι ≫ g)
    W.ι 0 hr rfl k α
  have hres := chowGroupRestrict_heq_flatPullbackChow C (sZ := g ≫ sX) (sY := (W.ι ≫ g) ≫ sX)
    W.ι (Category.assoc _ _ _).symm
  rw [← idRule_chernClassOfLocallyFree_of_rank C sX E r p (W.ι ≫ g) k]
  refine eq_of_heq ((hres _ _).trans (hflat.symm.trans ?_))
  exact idRule_heq_of_heq C sX _ (W.ι ≫ g) (h0 k) (hres k α).symm

/-! ### The Chern classes as the unique classes with the given restrictions -/

/-- **Stacks 0ESW, the Chern classes of a module of non-constant rank.** `c_p(ℰ) ∈ A^p(X)` is the
class whose restriction to every rank locus `X_r` is the Chern class `c_p(ℰ|_{X_r})` of
Stacks 0B7H (zero when `p > r`), and it is the only such class: under
`A^p(X) = ∏_r A^p(X_r)` it is the product of the classes `c_p(ℰ|_{X_r})`. -/
@[stacks 0ESW "c_p(E) ∈ A^p(X) as the product of the classes c_p(E|_{X_r}) ∈ A^p(X_r) of 0B7H \
under A^p(X) = ∏_r A^p(X_r): existence and uniqueness of the class with these restrictions"]
theorem chernClassOfLocallyFree_spec (p : ℕ) :
    (∀ r : ℕ, haveI := isFiniteLocallyFreeOfRank_pullback_rankLocus E r
      chowCohomologyRestriction C (gysinSystemOfInvertible C) sX (rankLocus E r).ι (p : ℤ)
          (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C)
          (chernClassOfLocallyFree E C sX p) =
        if h : p ≤ r then
          GenuineChern.chernClass C ((rankLocus E r).ι ≫ sX)
            ((Scheme.Modules.pullback (rankLocus E r).ι).obj E) r ⟨p, Nat.lt_succ_of_le h⟩
        else 0) ∧
    ∀ c : chowCohomologyComponent C (gysinSystemOfInvertible C) sX (p : ℤ),
      (∀ r : ℕ, haveI := isFiniteLocallyFreeOfRank_pullback_rankLocus E r
        chowCohomologyRestriction C (gysinSystemOfInvertible C) sX (rankLocus E r).ι (p : ℤ)
            (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C) c =
          if h : p ≤ r then
            GenuineChern.chernClass C ((rankLocus E r).ι ≫ sX)
              ((Scheme.Modules.pullback (rankLocus E r).ι).obj E) r ⟨p, Nat.lt_succ_of_le h⟩
          else 0) →
      c = chernClassOfLocallyFree E C sX p := by
  refine (fun hres ↦ ⟨hres, fun c hc ↦ eq_of_chowCohomologyRestriction_rankLocus_eq C sX E
    fun r ↦ (hc r).trans (hres r).symm⟩) fun r ↦ ?_
  have := isFiniteLocallyFreeOfRank_pullback_rankLocus E r
  exact chowCohomologyRestriction_chernClassOfLocallyFree E C sX r p _ rfl

/-! ### The total Chern class in the completed bivariant ring -/

/-- The degree `p` part of the total Chern class `c(ℰ)`, for `p ∈ ℤ`: the Chern class `c_p(ℰ)`
for `p ≥ 0` and zero in negative degrees. -/
def totalChernComponent : ∀ p : ℤ, chowCohomologyComponent C (gysinSystemOfInvertible C) sX p
  | .ofNat n => chernClassOfLocallyFree E C sX n
  | .negSucc _ => 0

/-- In degree `n ≥ 0` the total Chern class has the component `c_n(ℰ)`. -/
theorem totalChernComponent_natCast (n : ℕ) :
    totalChernComponent C sX E (n : ℤ) = chernClassOfLocallyFree E C sX n :=
  rfl

/-- A class restricting to zero on the rank locus `X_r` restricts to zero on every connected
component of `X` on which `ℰ` has rank `r`. -/
theorem bivariantConnectedComponentRestriction_eq_zero_of_chowCohomologyRestriction_eq_zero
    [IsLocallyNoetherian X] {p : ℤ}
    (c : chowCohomologyComponent C (gysinSystemOfInvertible C) sX p)
    (i : _root_.ConnectedComponents X)
    (hc : chowCohomologyRestriction C (gysinSystemOfInvertible C) sX
      (rankLocus E (Scheme.Modules.rankOnConnectedComponent E i)).ι p
      (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C) c = 0) :
    bivariantConnectedComponentRestriction C (gysinSystemOfInvertible C) sX sX (𝟙 X)
        (Category.id_comp sX) p (gysinSystemOfInvertible_isNaturalUnderOpenImmersion C) c i =
      0 := by
  set r := Scheme.Modules.rankOnConnectedComponent E i
  have h1 : rankLocusRestriction C (gysinSystemOfInvertible C) sX E
      (gysinSystemOfInvertible_isNaturalUnderOpenImmersion C) p c r = 0 := by
    rw [rankLocusRestriction_eq_chowCohomologyRestriction]
    exact hc
  have h2 := (AddEquiv.map_eq_zero_iff (pieceIdentityCongr C (gysinSystemOfInvertible C) sX
    (rankLociFamily E) (rankLociFamily_le_preimage E) p (ULift.up r)
    (pieceMap_comp_structureMorphism C sX sX (𝟙 X) (Category.id_comp sX) _ _ _ _ _))).1 h1
  have hX : X.connectedComponentOpens i ≤ rankLociFamily E (ULift.up r) :=
    connectedComponentOpens_le_rankLocus E i
  have hY : X.connectedComponentOpens ((Scheme.Hom.continuous (𝟙 X)).connectedComponentsMap i) ≤
      rankLociFamily E (id (ULift.up r)) := by
    rw [connectedComponentsMap_id_apply]
    exact hX
  exact bivariantPieceRestriction_eq_zero_of_le (𝟙 X) X.connectedComponentOpens
    X.connectedComponentOpens (Scheme.Hom.continuous (𝟙 X)).connectedComponentsMap
    (Scheme.Hom.connectedComponentOpens_le_preimage (𝟙 X)) i (rankLociFamily E)
    (rankLociFamily E) id (rankLociFamily_le_preimage E) (ULift.up r) hX hY C
    (gysinSystemOfInvertible C) sX sX (Category.id_comp sX) p
    (gysinSystemOfInvertible_isNaturalUnderOpenImmersion C) _ h2

/-- On a connected component on which `ℰ` has rank `r`, the degree `p` part of `c(ℰ)` vanishes
unless `0 ≤ p ≤ r`. -/
theorem bivariantConnectedComponentRestriction_totalChernComponent [IsLocallyNoetherian X]
    (i : _root_.ConnectedComponents X) {p : ℤ}
    (hp : p ∉ Finset.Icc (0 : ℤ) (Scheme.Modules.rankOnConnectedComponent E i)) :
    bivariantConnectedComponentRestriction C (gysinSystemOfInvertible C) sX sX (𝟙 X)
        (Category.id_comp sX) p (gysinSystemOfInvertible_isNaturalUnderOpenImmersion C)
        (totalChernComponent C sX E p) i = 0 := by
  rcases p with n | n
  · refine bivariantConnectedComponentRestriction_eq_zero_of_chowCohomologyRestriction_eq_zero
      C sX E _ i ?_
    have hn : ¬ n ≤ Scheme.Modules.rankOnConnectedComponent E i := fun h ↦
      hp (by
        simp only [Int.ofNat_eq_natCast, Finset.mem_Icc]
        exact ⟨Int.natCast_nonneg n, by exact_mod_cast h⟩)
    have := (chernClassOfLocallyFree_spec C sX E n).1 (Scheme.Modules.rankOnConnectedComponent E i)
    rw [dite_eq_right hn] at this
    exact this
  · change (bivariantConnectedComponentRestriction C (gysinSystemOfInvertible C) sX sX (𝟙 X)
        (Category.id_comp sX) _ (gysinSystemOfInvertible_isNaturalUnderOpenImmersion C)) 0 i = 0
    rw [map_zero]
    rfl

/-- The family `(c_p(ℰ))_p` lies in the completed group of Stacks 0FE0: on each connected
component it vanishes in all but finitely many degrees. -/
theorem totalChernComponent_mem_completedBivariantSubgroup [IsLocallyNoetherian X] :
    totalChernComponent C sX E ∈
      completedBivariantSubgroupOfInvertible C sX sX (𝟙 X) (Category.id_comp sX) :=
  (mem_completedBivariantSubgroup C (gysinSystemOfInvertible C) sX sX (𝟙 X) (Category.id_comp sX)
    (gysinSystemOfInvertible_isNaturalUnderOpenImmersion C) _).2 fun i ↦
  (Finset.Icc (0 : ℤ) (Scheme.Modules.rankOnConnectedComponent E i)).finite_toSet.subset
    fun p hp ↦ by
      by_contra hne
      exact hp (bivariantConnectedComponentRestriction_totalChernComponent C sX E i hne)

/-- **Stacks 0ESW, the total Chern class.** The total Chern class
`c(ℰ) = c_0(ℰ) + c_1(ℰ) + c_2(ℰ) + … ∈ A^*(X)^∧` of a finite locally free module of arbitrary
rank: the element of the completed bivariant group of Stacks 0FE0 whose degree `p` part is the
Chern class `c_p(ℰ)` for `p ≥ 0` (and zero for `p < 0`). -/
@[stacks 0ESW "the total Chern class c(E) = c_0(E) + c_1(E) + ... as an element of the completed \
bivariant cohomology ring A^*(X)^∧ of 0FE0"]
def totalChernClassCompleted :
    letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
    {c : completedBivariantGroup C (gysinSystemOfInvertible C) sX sX (𝟙 X) (Category.id_comp sX) //
      completedBivariantSequenceOfInvertible C sX sX (𝟙 X) (Category.id_comp sX) c =
        totalChernComponent C sX E} :=
  letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  ⟨(completedBivariantGroupEquivOfInvertible C sX sX (𝟙 X) (Category.id_comp sX)).symm
      ⟨totalChernComponent C sX E, totalChernComponent_mem_completedBivariantSubgroup C sX E⟩,
    congrArg Subtype.val
      ((completedBivariantGroupEquivOfInvertible C sX sX (𝟙 X)
        (Category.id_comp sX)).apply_symm_apply
        ⟨totalChernComponent C sX E, totalChernComponent_mem_completedBivariantSubgroup C sX E⟩)⟩

/-- The degree `n ≥ 0` part of the completed total Chern class is `c_n(ℰ)`. -/
theorem completedBivariantSequenceOfInvertible_totalChernClassCompleted (n : ℕ) :
    letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
    completedBivariantSequenceOfInvertible C sX sX (𝟙 X) (Category.id_comp sX)
        (totalChernClassCompleted C sX E).1 (n : ℤ) =
      chernClassOfLocallyFree E C sX n :=
  congrFun (totalChernClassCompleted C sX E).2 (n : ℤ)

/-! ### The rank -/

/-- **Stacks 0ESW, the rank.** The rank `r(ℰ) ∈ A^0(X)` of a finite locally free module of
arbitrary rank: the class whose component on the rank locus `X_r` is `r` times the unit
`1 ∈ A^0(X_r)`, that is, the operation sending `(α_r) ∈ ∏_r CH_*(X'_r)` to `(r α_r)`. -/
def rankClassOfLocallyFree : chowCohomologyComponent C (gysinSystemOfInvertible C) sX 0 :=
  rankLocusAssembly C (gysinSystemOfInvertible C) sX E
    (gysinSystemOfInvertible_isNaturalUnderOpenImmersion C)
    (gysinSystemOfInvertible_isNaturalUnderOpensRestriction C)
    (gysinSystemOfInvertible_isNaturalUnderPullbackComp C) 0
    fun r ↦ (r : ℤ) • bivariantIdentityClassOfInvertible C ((rankLocus E r).ι ≫ sX)

/-- The restriction of `r(ℰ)` to the rank locus `X_r` is `r · 1`. -/
theorem chowCohomologyRestriction_rankClassOfLocallyFree (r : ℕ) :
    chowCohomologyRestriction C (gysinSystemOfInvertible C) sX (rankLocus E r).ι 0
        (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C) (rankClassOfLocallyFree C sX E) =
      (r : ℤ) • bivariantIdentityClassOfInvertible C ((rankLocus E r).ι ≫ sX) :=
  (rankLocusRestriction_eq_chowCohomologyRestriction C sX E _ r).symm.trans
    (rankLocusRestriction_rankLocusAssembly C (gysinSystemOfInvertible C) sX E _ _ _ 0 _ r)

/-- **Stacks 0ESW, the rank as the unique class with the given restrictions.** `r(ℰ)` restricts
to `r · 1` on each rank locus `X_r`, and it is the only class of `A^0(X)` doing so. -/
@[stacks 0ESW "the rank r(E) ∈ A^0(X): the class whose restriction to each X_r is r times the \
unit of A^0(X_r), existence and uniqueness"]
theorem rankClassOfLocallyFree_spec :
    (∀ r : ℕ, chowCohomologyRestriction C (gysinSystemOfInvertible C) sX (rankLocus E r).ι 0
        (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C) (rankClassOfLocallyFree C sX E) =
      (r : ℤ) • bivariantIdentityClassOfInvertible C ((rankLocus E r).ι ≫ sX)) ∧
    ∀ c : chowCohomologyComponent C (gysinSystemOfInvertible C) sX 0,
      (∀ r : ℕ, chowCohomologyRestriction C (gysinSystemOfInvertible C) sX (rankLocus E r).ι 0
          (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C) c =
        (r : ℤ) • bivariantIdentityClassOfInvertible C ((rankLocus E r).ι ≫ sX)) →
      c = rankClassOfLocallyFree C sX E :=
  ⟨chowCohomologyRestriction_rankClassOfLocallyFree C sX E, fun _ hc ↦
    eq_of_chowCohomologyRestriction_rankLocus_eq C sX E fun r ↦
      (hc r).trans (chowCohomologyRestriction_rankClassOfLocallyFree C sX E r).symm⟩

/-- Integer multiples of heterogeneously equal Chow classes are heterogeneously equal. -/
theorem zsmul_heq_zsmul {T : Scheme.{u}} {q q' : T ⟶ C.S} [LocallyOfFiniteType q]
    [LocallyOfFiniteType q'] (hq : q = q') {k k' : ℤ} (hk : k = k') (n : ℤ)
    {x : chowGroup C q k} {y : chowGroup C q' k'} (h : x ≍ y) : n • x ≍ n • y := by
  subst hq hk
  cases h
  rfl

/-- **Stacks 0ESW, the operation of the rank.** On a test scheme `f : X' ⟶ X` along which
`f^*ℰ` has constant rank `r` — for instance the part `X'_r` of any test scheme lying over `X_r` —
the class `r(ℰ)` acts as multiplication by `r`. -/
@[stacks 0ESW "the rank r(E) ∈ A^0(X) is the bivariant operation sending (α_r) to (r α_r): on \
every test scheme along which E has constant rank r it acts as multiplication by r"]
theorem idRule_rankClassOfLocallyFree_of_rank (r : ℕ) {X' : Scheme.{u}} (f : X' ⟶ X)
    [LocallyOfFiniteType f]
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Modules.pullback f).obj E) r] (k : ℤ) (α : chowGroup C (f ≫ sX) k) :
    (rankClassOfLocallyFree C sX E).idRule C sX (gysinSystemOfInvertible C) f k α =
      (r : ℤ) • identityCapRule C sX f k α := by
  set U := rankLocus E r with hU
  obtain ⟨f', _, hf', hh⟩ := exists_factorization_idRule_heq_of_rank C sX E r f
    (rankClassOfLocallyFree C sX E) _ (chowCohomologyRestriction_rankClassOfLocallyFree C sX E r)
    k α
  subst hf'
  set β : chowGroup C (f' ≫ (U.ι ≫ sX)) k :=
    chowGroupCongr C (Category.assoc f' U.ι sX).symm k α with hβ
  have hβα : β ≍ α := chowGroupCongr_heq C _ k α
  rw [BivariantClass.idRule_zsmul] at hh
  refine eq_of_heq (hh.trans (zsmul_heq_zsmul C (Category.assoc f' U.ι sX).symm rfl _ ?_))
  exact (idRule_bivariantIdentityClassOfInvertible_heq C (U.ι ≫ sX) f' k β).trans
    (hβα.trans (identityCapRule_heq C sX (f' ≫ U.ι) k α).symm)

/-- **Stacks 0ESW, the rank explicitly.** For a test scheme `g : X' ⟶ X` locally of finite type,
with the induced decomposition `X' = ∐ X'_r`, the class `r(ℰ)` sends `(α_r) ∈ ∏_r CH_*(X'_r)` to
`(r α_r)`: restricting `r(ℰ) ∩ α` to `X'_r` gives `r · (α|_{X'_r})`. -/
@[stacks 0ESW "explicit form of the rank: r(E) is the bivariant operation sending \
(α_r) ∈ ∏_r CH_*(X'_r) to (r α_r), for every X' → X locally of finite type"]
theorem chowGroupRestrict_idRule_rankClassOfLocallyFree (r : ℕ) {X' : Scheme.{u}}
    (g : X' ⟶ X) [LocallyOfFiniteType g] (k : ℤ) (α : chowGroup C (g ≫ sX) k) :
    chowGroupRestrict C (g ≫ sX) (((g ⁻¹ᵁ rankLocus E r).ι ≫ g) ≫ sX) (g ⁻¹ᵁ rankLocus E r).ι
        (Category.assoc _ _ _).symm (k - 0)
        ((rankClassOfLocallyFree C sX E).idRule C sX (gysinSystemOfInvertible C) g k α) ≍
      (r : ℤ) • chowGroupRestrict C (g ≫ sX) (((g ⁻¹ᵁ rankLocus E r).ι ≫ g) ≫ sX)
        (g ⁻¹ᵁ rankLocus E r).ι (Category.assoc _ _ _).symm k α := by
  have := isFiniteLocallyFreeOfRank_pullback_preimage_rankLocus E g r
  set W := g ⁻¹ᵁ rankLocus E r
  have hr := relativeDimension_of_isOpenImmersion W.ι
  have h0 : ∀ m : ℤ, m + ((0 : ℕ) : ℤ) = m := fun m ↦ by simp
  have hflat := idRule_flatPullbackChow_heq C sX (rankClassOfLocallyFree C sX E) g (W.ι ≫ g)
    W.ι 0 hr rfl k α
  have hres := chowGroupRestrict_heq_flatPullbackChow C (sZ := g ≫ sX) (sY := (W.ι ≫ g) ≫ sX)
    W.ι (Category.assoc _ _ _).symm
  refine (hres _ _).trans (hflat.symm.trans ?_)
  refine (idRule_heq_of_heq C sX _ (W.ι ≫ g) (h0 k) (hres k α).symm).trans ?_
  rw [idRule_rankClassOfLocallyFree_of_rank C sX E r (W.ι ≫ g) k]
  exact zsmul_heq_zsmul C rfl (sub_zero k) _ (identityCapRule_heq C sX (W.ι ≫ g) k _)

/-! ### Centrality -/

section Center

attribute [local instance] chowCohomologyGRingOfInvertible

/-- The graded restriction map of Stacks 0B7F at the Gysin system of the first Chern class rule is
multiplicative for the ring structure of Stacks 0B7E on `A^*(X)`. -/
theorem chowCohomologyTotalRestrictionOfInvertible_mul {Y : Scheme.{u}} (f : Y ⟶ X)
    [LocallyOfFiniteType f] (x y : chowCohomology C (gysinSystemOfInvertible C) sX) :
    chowCohomologyTotalRestrictionOfInvertible C sX f (x * y) =
      chowCohomologyTotalRestrictionOfInvertible C sX f x *
        chowCohomologyTotalRestrictionOfInvertible C sX f y := by
  induction x using DirectSum.induction_on with
  | zero => rw [zero_mul, map_zero, zero_mul]
  | of p a =>
    induction y using DirectSum.induction_on with
    | zero => rw [mul_zero, map_zero, mul_zero]
    | of q b =>
      rw [DirectSum.of_mul_of, chowCohomologyTotalRestrictionOfInvertible_of,
        chowCohomologyTotalRestrictionOfInvertible_of,
        chowCohomologyTotalRestrictionOfInvertible_of, DirectSum.of_mul_of]
      exact congrArg (DirectSum.of _ (p + q))
        (chowCohomologyRestrictionOfInvertible_mul C sX f p q a b)
    | add y y' hy hy' => rw [mul_add, map_add, map_add, hy, hy', mul_add]
  | add x x' hx hx' => rw [add_mul, map_add, map_add, hx, hx', add_mul]

/-- Two elements of `A^*(X)` with the same restrictions to all the rank loci of `ℰ` are equal. -/
theorem eq_of_chowCohomologyTotalRestrictionOfInvertible_rankLocus_eq
    {x y : chowCohomology C (gysinSystemOfInvertible C) sX}
    (h : ∀ r : ℕ, chowCohomologyTotalRestrictionOfInvertible C sX (rankLocus E r).ι x =
      chowCohomologyTotalRestrictionOfInvertible C sX (rankLocus E r).ι y) : x = y := by
  refine DFinsupp.ext fun p ↦ eq_of_chowCohomologyRestriction_rankLocus_eq C sX E fun r ↦ ?_
  have hr := congrArg (fun z ↦ z p) (h r)
  simp only [chowCohomologyTotalRestrictionOfInvertible] at hr
  rwa [chowCohomologyTotalRestriction_apply, chowCohomologyTotalRestriction_apply] at hr

/-- An element of `A^*(X)` whose restriction to every rank locus of `ℰ` is central is central. -/
theorem mem_center_of_chowCohomologyTotalRestrictionOfInvertible_rankLocus_mem_center
    {x : chowCohomology C (gysinSystemOfInvertible C) sX}
    (h : ∀ r : ℕ, chowCohomologyTotalRestrictionOfInvertible C sX (rankLocus E r).ι x ∈
      Subring.center (chowCohomology C (gysinSystemOfInvertible C) ((rankLocus E r).ι ≫ sX))) :
    x ∈ Subring.center (chowCohomology C (gysinSystemOfInvertible C) sX) := by
  rw [Subring.mem_center_iff]
  intro y
  refine eq_of_chowCohomologyTotalRestrictionOfInvertible_rankLocus_eq C sX E fun r ↦ ?_
  rw [chowCohomologyTotalRestrictionOfInvertible_mul,
    chowCohomologyTotalRestrictionOfInvertible_mul]
  exact ((Subring.mem_center_iff.1 (h r)) _)

/-- **Stacks 0ESW, centrality of the Chern classes.** For a finite locally free module `ℰ` of
arbitrary rank, `c_p(ℰ) ∈ A^p(X)` lies in the center of the Chow cohomology ring `A^*(X)` of
Stacks 0B7E: on each rank locus it restricts to a Chern class of Stacks 0B7H, which is central by
Stacks 02UA, or to zero. -/
@[stacks 0ESW "c_p(E) is in the center of A^*(X), for E of non-constant rank"]
theorem chernClassOfLocallyFree_mem_center (p : ℕ) :
    DirectSum.of (fun q : ℤ ↦ chowCohomologyComponent C (gysinSystemOfInvertible C) sX q) (p : ℤ)
        (chernClassOfLocallyFree E C sX p) ∈
      Subring.center (chowCohomology C (gysinSystemOfInvertible C) sX) := by
  refine mem_center_of_chowCohomologyTotalRestrictionOfInvertible_rankLocus_mem_center C sX E
    fun r ↦ ?_
  have := isFiniteLocallyFreeOfRank_pullback_rankLocus E r
  rw [chowCohomologyTotalRestrictionOfInvertible_of]
  have hres := (chernClassOfLocallyFree_spec C sX E p).1 r
  change chowCohomologyRestriction C (gysinSystemOfInvertible C) sX (rankLocus E r).ι (p : ℤ)
    (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C) (chernClassOfLocallyFree E C sX p) =
      _ at hres
  change DirectSum.of _ (p : ℤ) (chowCohomologyRestriction C (gysinSystemOfInvertible C) sX
    (rankLocus E r).ι (p : ℤ) (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C)
    (chernClassOfLocallyFree E C sX p)) ∈ _
  rw [hres]
  split_ifs with h
  · exact GenuineChern.chernClass_mem_center _ r ⟨p, Nat.lt_succ_of_le h⟩
  · rw [map_zero]
    exact Subring.zero_mem _

/-- **Stacks 0ESW, centrality of the rank.** `r(ℰ) ∈ A^0(X)` lies in the center of `A^*(X)`: on
each rank locus `X_r` it restricts to `r · 1`. -/
@[stacks 0ESW "r(E) is in the center of A^*(X)"]
theorem rankClassOfLocallyFree_mem_center :
    DirectSum.of (fun q : ℤ ↦ chowCohomologyComponent C (gysinSystemOfInvertible C) sX q) 0
        (rankClassOfLocallyFree C sX E) ∈
      Subring.center (chowCohomology C (gysinSystemOfInvertible C) sX) := by
  refine mem_center_of_chowCohomologyTotalRestrictionOfInvertible_rankLocus_mem_center C sX E
    fun r ↦ ?_
  rw [chowCohomologyTotalRestrictionOfInvertible_of]
  change DirectSum.of _ 0 (chowCohomologyRestriction C (gysinSystemOfInvertible C) sX
    (rankLocus E r).ι 0 (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C)
    (rankClassOfLocallyFree C sX E)) ∈ _
  rw [chowCohomologyRestriction_rankClassOfLocallyFree, map_zsmul,
    ← chowCohomologyGradedOne_eq, ← DirectSum.one_def]
  exact zsmul_mem (Subring.one_mem _) _

end Center

end Stacks.Chow.SectionZeroScheme

end
