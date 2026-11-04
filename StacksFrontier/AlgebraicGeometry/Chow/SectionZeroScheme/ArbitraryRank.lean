module

public import StacksFrontier.AlgebraicGeometry.Chow.SectionZeroScheme.Main
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassArbitraryRank.RankLocusChernClass
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassDerived.TotalClassPieces
public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.CapRuleTwist
public import StacksFrontier.AlgebraicGeometry.Divisors.Reflexive.FiberRankIsomorphismInvariant
public import StacksFrontier.AlgebraicGeometry.FiberRank.ConstantRank

/-!
# The Chern classes of a finite locally free module of arbitrary rank, on a test scheme

Let `ℰ` be a finite locally free module on `X`, locally of finite type over the base of chapter
42, whose rank need not be constant. [Stacks, Tag 0ESW] defines `c_p(ℰ) ∈ A^p(X)` as the class
whose component on the rank-`r` locus `X_r` is `c_p(ℰ|_{X_r})` of [Stacks, Tag 0B7H]. This file
names that class, with the bivariant Chern classes `Stacks.Chow.GenuineChern.chernClass` on the
rank loci, and computes its operation on a test scheme `f : X' ⟶ X` along which `f^*ℰ` has
constant rank `r`: then `f` maps into `X_r`, and `c_p(ℰ) ∩ -` on `X'` is `c_p(f^*ℰ) ∩ -`.

## Main definitions

* `Stacks.Chow.SectionZeroScheme.chernClassOfLocallyFree` — `c_p(ℰ) ∈ A^p(X)` of Stacks 0ESW.

## Main results

* `Stacks.Chow.SectionZeroScheme.mem_rankLocus_of_isFiniteLocallyFreeOfRank_pullback` — if `f^*ℰ`
  has constant rank `r`, then `f` maps into the rank-`r` locus.
* `Stacks.Chow.SectionZeroScheme.idRule_chernClassOfLocallyFree` — on such a test scheme,
  `c_p(ℰ) ∩ - = c_p(f^*ℰ) ∩ -`.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.Chow.SectionZeroScheme

variable {X X' : Scheme.{u}} (E : X.Modules)
  [hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E]

/-- **If `f^*ℰ` has constant rank `r`, then `f` maps into the rank-`r` locus of `ℰ`.** At a point
`x'`, both `f^*ℰ` and the pullback of `ℰ|_{X_m}` along `f⁻¹(X_m) ⟶ X_m`, `m` the rank of `ℰ` at
`f x'`, compute the restriction of `f^*ℰ` to `f⁻¹(X_m)`, which therefore has fibre rank `r` and
`m` at `x'`. -/
theorem mem_rankLocus_of_isFiniteLocallyFreeOfRank_pullback (f : X' ⟶ X) (r : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Modules.pullback f).obj E) r] (x' : X') :
    f x' ∈ rankLocus E r := by
  set m := moduleRank E (f x') with hm
  set U := rankLocus E m
  have hx' : x' ∈ f ⁻¹ᵁ U := (mem_rankLocus E).2 hm.symm
  have := isFiniteLocallyFreeOfRank_pullback_rankLocus E m
  have := AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback (f ∣_ U)
    ((Scheme.Modules.pullback U.ι).obj E) m
  have := AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback (f ⁻¹ᵁ U).ι
    ((Scheme.Modules.pullback f).obj E) r
  let e : (Scheme.Modules.pullback (f ∣_ U)).obj ((Scheme.Modules.pullback U.ι).obj E) ≅
      (Scheme.Modules.pullback (f ⁻¹ᵁ U).ι).obj ((Scheme.Modules.pullback f).obj E) :=
    ((Scheme.Modules.pullbackComp (f ∣_ U) U.ι).app E) ≪≫
      ((Scheme.Modules.pullbackCongr (morphismRestrict_ι f U)).app E) ≪≫
      ((Scheme.Modules.pullbackComp (f ⁻¹ᵁ U).ι f).app E).symm
  exact (mem_rankLocus E).2 ((Scheme.Modules.fiberRank_eq_of_isFiniteLocallyFreeOfRank
    ((Scheme.Modules.pullback (f ∣_ U)).obj ((Scheme.Modules.pullback U.ι).obj E)) m
      ⟨x', hx'⟩).symm.trans ((Scheme.Modules.fiberRank_eq_of_iso e ⟨x', hx'⟩).trans
    (Scheme.Modules.fiberRank_eq_of_isFiniteLocallyFreeOfRank
      ((Scheme.Modules.pullback (f ⁻¹ᵁ U).ι).obj ((Scheme.Modules.pullback f).obj E)) r
      ⟨x', hx'⟩)))

variable (C : ChowSituation.{u}) (sX : X ⟶ C.S) [LocallyOfFiniteType sX]

/-- **The Chern class `c_p(ℰ) ∈ A^p(X)` of a finite locally free module of arbitrary rank**
([Stacks, Tag 0ESW]): the class whose component on the rank-`r` locus `X_r` is the bivariant
Chern class `c_p(ℰ|_{X_r})` of [Stacks, Tag 0B7H], `Stacks.Chow.GenuineChern.chernClass`, and zero
when `p > r`. -/
def chernClassOfLocallyFree (p : ℕ) :
    chowCohomologyComponent C (gysinSystemOfInvertible C) sX (p : ℤ) :=
  chernClassArbitraryRank C (gysinSystemOfInvertible C) sX E
    (gysinSystemOfInvertible_isNaturalUnderOpenImmersion C)
    (gysinSystemOfInvertible_isNaturalUnderOpensRestriction C)
    (gysinSystemOfInvertible_isNaturalUnderPullbackComp C)
    (fun r j =>
      haveI := isFiniteLocallyFreeOfRank_pullback_rankLocus E r
      GenuineChern.chernClass C ((rankLocus E r).ι ≫ sX)
        ((Scheme.Modules.pullback (rankLocus E r).ι).obj E) r j) p

/-- The component of `c_r(ℰ)` on the rank-`r` locus is `c_r(ℰ|_{X_r})`. -/
theorem rankLocusRestriction_chernClassOfLocallyFree (r : ℕ) :
    haveI := isFiniteLocallyFreeOfRank_pullback_rankLocus E r
    rankLocusRestriction C (gysinSystemOfInvertible C) sX E
        (gysinSystemOfInvertible_isNaturalUnderOpenImmersion C) (r : ℤ)
        (chernClassOfLocallyFree E C sX r) r =
      GenuineChern.chernClass C ((rankLocus E r).ι ≫ sX)
        ((Scheme.Modules.pullback (rankLocus E r).ι).obj E) r (Fin.last r) :=
  (rankLocusRestriction_chernClassArbitraryRank C (gysinSystemOfInvertible C) sX E _ _ _ _
      r r).trans
    (rankLocusChernFamily_of_le C (gysinSystemOfInvertible C) sX E _ r r le_rfl)

/-- The Chern class cap products over equal base morphisms, at heterogeneously equal arguments. -/
theorem chernCap_heq_of_base_eq {T : Scheme.{u}} {q q' : T ⟶ C.S} [LocallyOfFiniteType q]
    [LocallyOfFiniteType q'] (hq : q = q') (M : T.Modules) (r : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} M r] (k : ℤ)
    (j : Fin (r + 1)) {α : chowGroup C q k} {α' : chowGroup C q' k} (hα : α ≍ α') :
    GenuineChern.chernCap C r q M k j α ≍ GenuineChern.chernCap C r q' M k j α' := by
  subst hq
  cases hα
  rfl

/-- **On a test scheme along which `ℰ` has constant rank `r`, `c_r(ℰ) ∩ -` is `c_r(f^*ℰ) ∩ -`.**
The test morphism maps into the rank-`r` locus, on which `c_r(ℰ)` restricts to `c_r(ℰ|_{X_r})`
([Stacks, Tag 0ESW]), whose operation is the cap product with the Chern class of the pullback
([Stacks, Tag 0B7H]). -/
theorem idRule_chernClassOfLocallyFree (r : ℕ) (f : X' ⟶ X) [LocallyOfFiniteType f]
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Modules.pullback f).obj E) r] (k : ℤ) (α : chowGroup C (f ≫ sX) k) :
    (chernClassOfLocallyFree E C sX r).idRule C sX (gysinSystemOfInvertible C) f k α =
      GenuineChern.chernCap C r (f ≫ sX) ((Scheme.Modules.pullback f).obj E) k (Fin.last r) α := by
  set U := rankLocus E r
  have hrange : Set.range f ⊆ Set.range U.ι := by
    rintro _ ⟨x', rfl⟩
    rw [Scheme.Opens.range_ι]
    exact mem_rankLocus_of_isFiniteLocallyFreeOfRank_pullback E f r x'
  set f' := IsOpenImmersion.lift U.ι f hrange
  have hf' : f' ≫ U.ι = f := IsOpenImmersion.lift_fac U.ι f hrange
  have : LocallyOfFiniteType f' := by
    have : LocallyOfFiniteType (f' ≫ U.ι) := hf' ▸ inferInstance
    exact locallyOfFiniteType_of_comp f' U.ι
  clear_value f'
  subst hf'
  have hEU := isFiniteLocallyFreeOfRank_pullback_rankLocus E r
  have := AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback f'
    ((Scheme.Modules.pullback U.ι).obj E) r
  set β : chowGroup C (f' ≫ (U.ι ≫ sX)) k :=
    chowGroupCongr C (Category.assoc f' U.ι sX).symm k α
  have hβα : β ≍ α := chowGroupCongr_heq C _ k α
  have h2 := BivariantClass.idRule_chowCohomologyRestriction_heq U.ι
    (chernClassOfLocallyFree E C sX r) f' k β α hβα
  have h3 : chowCohomologyRestriction C (gysinSystemOfInvertible C) sX U.ι (r : ℤ)
      (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C)
      (chernClassOfLocallyFree E C sX r) =
      GenuineChern.chernClass C (U.ι ≫ sX) ((Scheme.Modules.pullback U.ι).obj E) r
        (Fin.last r) :=
    (chowCohomologyRestriction_eq_pieceIdentityCongr (rankLociFamily E)
      (chernClassOfLocallyFree E C sX r) (ULift.up r)).trans
      (rankLocusRestriction_chernClassOfLocallyFree E C sX r)
  rw [h3, GenuineChern.idRule_chernClass] at h2
  refine eq_of_heq (h2.symm.trans ?_)
  refine (heq_of_eq (GenuineChern.chernCap_congr C (f' ≫ U.ι ≫ sX)
    (E := (Scheme.Modules.pullback f').obj ((Scheme.Modules.pullback U.ι).obj E))
    (E' := (Scheme.Modules.pullback (f' ≫ U.ι)).obj E) r
    ((Scheme.Modules.pullbackComp f' U.ι).app E) k (Fin.last r) β)).trans ?_
  exact chernCap_heq_of_base_eq C (Category.assoc f' U.ι sX).symm _ r k (Fin.last r) hβα

end Stacks.Chow.SectionZeroScheme

end
