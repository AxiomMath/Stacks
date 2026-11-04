module

public import StacksFrontier.AlgebraicGeometry.Curves.GenusCurve.GeometricGenusDisjointCover
public import StacksFrontier.AlgebraicGeometry.Picard.NormalizationComponents.SmoothCurveBridge
public import StacksFrontier.AlgebraicGeometry.Picard.TorsionRankReducedBaseChange
public import StacksFrontier.AlgebraicGeometry.Picard.TorsionReducedProperCurve

/-!
# The `ℓ`-torsion of the Picard group of a proper scheme of dimension at most one

[Stacks, Tag 0CE6](https://stacks.math.columbia.edu/tag/0CE6): let `k` be a field, let `X` be a
proper scheme of dimension at most one over `k` and let `ℓ` be a prime invertible in `k`.  Then
the `ℓ`-torsion of `Pic(X)` is finite-dimensional over `F_ℓ` and

`dim_{F_ℓ} Pic(X)[ℓ] ≤ dim_k H¹(X, 𝒪_X) + g_geom(X/k)`.

This file carries out the source's proof. Clause (1) of [Stacks, Tag 0C1Z] for smooth projective
curves over `k̄`, at the prime `ℓ`, enters through [Stacks, Tag 0C20]
(`AlgebraicGeometry.finrank_picardTorsion_le_genus_add_geometricGenus_of_isReduced_dim_one`),
which uses `Stacks.Picard.nonempty_torsionBy_addEquiv_pi_zmod_of_smoothProjectiveCurve`.
Tag 0CE6 is registered below.

## Main results

* `AlgebraicGeometry.picardTorsion_bound_of_connectedComponents`: for a *reduced* proper scheme of
  dimension at most one over an algebraically closed field, the bound, by decomposition into
  connected components and [Stacks, Tag 0C20] on the one-dimensional ones.
* `AlgebraicGeometry.finrank_picardTorsion_le_genus_add_geometricGenus`: the statement of
  [Stacks, Tag 0CE6] (registered).

## Implementation notes

**The decomposition.**  A proper scheme over a field is Noetherian, so it has finitely many
connected components and each of them is clopen
(`TopologicalSpace.NoetherianSpace.finite_connectedComponents` and
`TopologicalSpace.isClopen_connectedComponent_of_finite_connectedComponents`).  The inclusion of
a clopen open subscheme is a closed immersion as well as an open one, so the components form a
finite partition of the scheme into pieces that are open and closed, and the three invariants in
play are additive over such a partition:

* the Picard group — `AlgebraicGeometry.finrank_picardTorsion_le_sum_of_pairwise_disjoint`, which
  is only the inequality `dim_{F_ℓ} Pic(Y)[ℓ] ≤ ∑ dim_{F_ℓ} Pic(Y_c)[ℓ]`, all that an upper bound
  needs;
* the genus — `AlgebraicGeometry.genus_eq_sum_of_disjoint_cover`;
* the geometric genus — `AlgebraicGeometry.geometricGenus_eq_sum_of_isClopen_cover`.

A connected component of a reduced scheme is reduced, and its dimension is at most that of the
whole scheme.  Its dimension is therefore either one, where [Stacks, Tag 0C20] applies, or at
most zero, where the component has discrete underlying space and its Picard group vanishes
(`AlgebraicGeometry.finrank_picardTorsion_eq_zero_of_topologicalKrullDim_le_zero`).

**Tag 0C20.**  This development's form of [Stacks, Tag 0C20],
`AlgebraicGeometry.finrank_picardTorsion_le_genus_add_geometricGenus_of_isReduced_dim_one`, needs
`dim_{F_ℓ} Pic(X^ν)[ℓ] = 2 g_geom(X/k)` at the normalization.  That identity is derived from
clause (1) of [Stacks, Tag 0C1Z] by
`AlgebraicGeometry.rank_picardTorsion_normalizationSchemeOverField_eq_two_mul_geometricGenus`:
the normalization is the disjoint union of its connected components, each of dimension one being
a smooth projective curve over the algebraically closed field.

**The reductions.**  The passage from an arbitrary field to an algebraic closure and from the base
change to its reduction is `AlgebraicGeometry.picardTorsion_bound_of_reducedBaseChange`, which is
Tag 0CC5 and Tag 02KH for the first step and Tag 0CE2 (1), Tag 0CE3 and the corrected form of
Tag 0C6S for the second.  So the final theorem is that reduction composed with the component
decomposition proved here.

## References

* [Stacks Project, Tag 0CE6](https://stacks.math.columbia.edu/tag/0CE6)
* [Stacks Project, Tag 0C20](https://stacks.math.columbia.edu/tag/0C20)
* [Stacks Project, Tag 0C1Z](https://stacks.math.columbia.edu/tag/0C1Z)
* [Stacks Project, Tag 0CC5](https://stacks.math.columbia.edu/tag/0CC5)
* [Stacks Project, Tag 02KH](https://stacks.math.columbia.edu/tag/02KH)
* [Stacks Project, Tag 0CE2](https://stacks.math.columbia.edu/tag/0CE2)
* [Stacks Project, Tag 0CE3](https://stacks.math.columbia.edu/tag/0CE3)
* [Stacks Project, Tag 0BY9](https://stacks.math.columbia.edu/tag/0BY9)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open Stacks.Picard (ofScheme)

universe u

namespace AlgebraicGeometry

attribute [local instance] AddSubgroup.torsionBy.zmodModule

/-! ### The decomposition into connected components -/

/-- **The component-decomposition step of [Stacks, Tag 0CE6].**  Let `K` be an algebraically
closed field, let `Y` be a *reduced* proper scheme of dimension at most one over `K` and let `ℓ`
be a prime invertible in `K`.  Then the `ℓ`-torsion of
`Pic(Y)` is finite-dimensional over `F_ℓ` and

`dim_{F_ℓ} Pic(Y)[ℓ] ≤ dim_K H¹(Y, 𝒪_Y) + g_geom(Y/K)`.

`Y` has finitely many connected components, each clopen, hence each a closed as well as open
subscheme; the Picard group, the genus and the geometric genus are additive over them.  A
component is reduced and has dimension at most one, so either its dimension is one and
[Stacks, Tag 0C20] applies
(`AlgebraicGeometry.finrank_picardTorsion_le_genus_add_geometricGenus_of_isReduced_dim_one`, its
input at the normalization supplied from clause (1) of [Stacks, Tag 0C1Z] by
`AlgebraicGeometry.rank_picardTorsion_normalizationSchemeOverField_eq_two_mul_geometricGenus`),
or its dimension is at most zero and its Picard group is trivial. -/
theorem picardTorsion_bound_of_connectedComponents (K : Type u) [Field K] [IsAlgClosed K]
    {Y : Scheme.{u}} (q : Y ⟶ Spec (.of K)) [IsProper q] [IsReduced Y]
    (hdim : topologicalKrullDim (Y : Type u) ≤ 1) (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : IsUnit (ℓ : K)) :
    FiniteDimensional (ZMod ℓ) (AddSubgroup.torsionBy (ofScheme Y) (ℓ : ℤ)) ∧
      Module.finrank (ZMod ℓ) (AddSubgroup.torsionBy (ofScheme Y) (ℓ : ℤ)) ≤
        genus q + geometricGenus K q := by
  classical
  have : IsNoetherian Y :=
    { toIsLocallyNoetherian := LocallyOfFiniteType.isLocallyNoetherian q
      toCompactSpace := QuasiCompact.compactSpace_of_compactSpace q }
  have : NoetherianSpace (Y : Type u) := inferInstance
  have : Finite (_root_.ConnectedComponents (Y : Type u)) :=
    NoetherianSpace.finite_connectedComponents (Y : Type u)
  let : Fintype (_root_.ConnectedComponents (Y : Type u)) := Fintype.ofFinite _
  -- The connected components, as clopen opens of `Y`.
  obtain ⟨U, hUclopen, hUmem, hUmk⟩ :
      ∃ U : _root_.ConnectedComponents (Y : Type u) → Y.Opens,
        (∀ c, IsClopen (U c : Set Y)) ∧
          (∀ x : Y, x ∈ U (_root_.ConnectedComponents.mk x)) ∧
          ∀ (c) (x : Y), x ∈ U c → _root_.ConnectedComponents.mk x = c :=
    ⟨fun c ↦ ⟨connectedComponent c.out,
        (isClopen_connectedComponent_of_finite_connectedComponents c.out).2⟩,
      fun c ↦ isClopen_connectedComponent_of_finite_connectedComponents c.out,
      fun _ ↦ _root_.ConnectedComponents.coe_eq_coe'.mp (Quotient.out_eq _).symm,
      fun c _ hx ↦ (_root_.ConnectedComponents.coe_eq_coe'.mpr hx).trans (Quotient.out_eq c)⟩
  -- The inclusions of the components are closed as well as open immersions.
  have hci : ∀ c, IsClosedImmersion (U c).ι := fun c ↦
    IsClosedImmersion.of_isPreimmersion (U c).ι (by
      rw [Scheme.Opens.range_ι]; exact (hUclopen c).1)
  have hpi : ∀ c, IsProper ((U c).ι ≫ q) := fun _ ↦ inferInstance
  have hred : ∀ c, IsReduced (U c).toScheme := fun c ↦ isReduced_of_isOpenImmersion (U c).ι
  have hUdim : ∀ c, topologicalKrullDim ((U c).toScheme : Type u) ≤ 1 := fun c ↦
    (U c).ι.isOpenEmbedding.isEmbedding.isInducing.topologicalKrullDim_le.trans hdim
  -- The cover by the components is an open cover, pairwise disjoint, in both spellings.
  have hcover : IsOpenCover U := by
    refine eq_top_iff.mpr fun x _ ↦ ?_
    exact Opens.mem_iSup.mpr ⟨_root_.ConnectedComponents.mk x, hUmem x⟩
  have hdisj : Pairwise (Function.onFun Disjoint U) := fun c d hcd ↦
    disjoint_iff.mpr (eq_bot_iff.mpr fun x hx ↦
      absurd ((hUmk c x hx.1).symm.trans (hUmk d x hx.2)) hcd)
  have hrange : ∀ c, Set.range (U c).ι.base = (U c : Set Y) := fun c ↦ Scheme.Opens.range_ι _
  have hdisjset : Pairwise fun c d ↦
      Disjoint (Set.range (U c).ι.base) (Set.range (U d).ι.base) := fun c d hcd ↦ by
    simpa only [hrange, Opens.coe_disjoint] using hdisj hcd
  have hcoverpt : ∀ y : Y, ∃ c x, (U c).ι.base x = y := fun y ↦
    ⟨_root_.ConnectedComponents.mk y, ⟨y, hUmem y⟩, rfl⟩
  have hcoverset : ∀ x : Y, ∃ c, x ∈ Set.range (U c).ι.base := fun x ↦
    have ⟨c, y, hy⟩ := hcoverpt x
    ⟨c, hy ▸ Set.mem_range_self y⟩
  have hopen : ∀ c, IsOpen (Set.range (U c).ι.base) := fun c ↦ by
    rw [hrange]; exact (U c).2
  -- The bound on each component.
  have hbound : ∀ c, FiniteDimensional (ZMod ℓ)
      (AddSubgroup.torsionBy (ofScheme (U c).toScheme) (ℓ : ℤ)) ∧
      Module.finrank (ZMod ℓ) (AddSubgroup.torsionBy (ofScheme (U c).toScheme) (ℓ : ℤ)) ≤
        genus ((U c).ι ≫ q) + geometricGenus K ((U c).ι ≫ q) := by
    intro c
    by_cases hz : topologicalKrullDim ((U c).toScheme : Type u) ≤ 0
    · obtain ⟨h1, h2⟩ := finrank_picardTorsion_eq_zero_of_topologicalKrullDim_le_zero K
        ((U c).ι ≫ q) hz ℓ
      exact ⟨h1, h2.le.trans (Nat.zero_le _)⟩
    · have hone : topologicalKrullDim ((U c).toScheme : Type u) = 1 :=
        le_antisymm (hUdim c) ((WithBot.one_le_iff_pos _).mpr (lt_of_not_ge hz))
      let : ((U c).toScheme).Over (Spec (.of K)) := ⟨(U c).ι ≫ q⟩
      have : IsProper ((U c).toScheme ↘ Spec (.of K)) := hpi c
      exact finrank_picardTorsion_le_genus_add_geometricGenus_of_isReduced_dim_one K
        (U c).toScheme hone ℓ hℓ.ne_zero
  refine ⟨finiteDimensional_picardTorsion_of_pairwise_disjoint U hcover hdisj ℓ
    fun c ↦ (hbound c).1, ?_⟩
  calc Module.finrank (ZMod ℓ) (AddSubgroup.torsionBy (ofScheme Y) (ℓ : ℤ))
      ≤ ∑ c, Module.finrank (ZMod ℓ)
          (AddSubgroup.torsionBy (ofScheme (U c).toScheme) (ℓ : ℤ)) :=
        finrank_picardTorsion_le_sum_of_pairwise_disjoint U hcover hdisj ℓ
          fun c ↦ (hbound c).1
    _ ≤ ∑ c, (genus ((U c).ι ≫ q) + geometricGenus K ((U c).ι ≫ q)) :=
        Finset.sum_le_sum fun c _ ↦ (hbound c).2
    _ = (∑ c, genus ((U c).ι ≫ q)) + ∑ c, geometricGenus K ((U c).ι ≫ q) :=
        Finset.sum_add_distrib
    _ = genus q + geometricGenus K q := by
        rw [← genus_eq_sum_of_disjoint_cover (fun c ↦ (U c).ι) hcoverpt hdisjset q,
          ← geometricGenus_eq_sum_of_isClopen_cover q (fun c ↦ (U c).ι) hopen hdisjset hcoverset]

/-! ### Tag 0CE6 -/

/-- **Stacks Project, Tag 0CE6.**  Let `k` be a field, let `X` be a proper scheme of dimension at
most one over `k` and let `ℓ` be a prime invertible in `k`.  Then the `ℓ`-torsion of `Pic(X)` is
finite-dimensional
over `F_ℓ` and

`dim_{F_ℓ} Pic(X)[ℓ] ≤ dim_k H¹(X, 𝒪_X) + g_geom(X/k)`.

The proof is the source's: extend the ground field to an algebraic closure and pass to the
reduction (`AlgebraicGeometry.picardTorsion_bound_of_reducedBaseChange`, which is Tag 0CC5, Tag
02KH, Tag 0CE2 (1) and Tag 0CE3), then decompose into connected components
(`AlgebraicGeometry.picardTorsion_bound_of_connectedComponents`) and apply Tag 0C20 to the
one-dimensional ones, the zero-dimensional ones having trivial Picard group. -/
@[stacks 0CE6]
theorem finrank_picardTorsion_le_genus_add_geometricGenus (k : Type u) [Field k]
    {X : Scheme.{u}} (g : X ⟶ Spec (.of k)) [IsProper g]
    (hdim : topologicalKrullDim (X : Type u) ≤ 1) (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : IsUnit (ℓ : k)) :
    FiniteDimensional (ZMod ℓ) (AddSubgroup.torsionBy (ofScheme X) (ℓ : ℤ)) ∧
      Module.finrank (ZMod ℓ) (AddSubgroup.torsionBy (ofScheme X) (ℓ : ℤ)) ≤
        genus g + geometricGenus k g := by
  set a := Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k))) with ha
  have hdimY : topologicalKrullDim ((pullback g a : Scheme.{u}) : Type u) ≤ 1 := by
    rw [topologicalKrullDim_baseChange k (AlgebraicClosure k) (pullback.fst g a)
      (pullback.snd g a) g (IsPullback.of_hasPullback g a)]
    exact hdim
  have hdimR : topologicalKrullDim ((pullback g a).reduction : Type u) ≤ 1 :=
    (pullback g a).reductionι.isClosedEmbedding.isEmbedding.isInducing.topologicalKrullDim_le.trans
      hdimY
  have hℓ' : IsUnit ((ℓ : ℕ) : AlgebraicClosure k) := by
    simpa using hℓ.map (algebraMap k (AlgebraicClosure k))
  obtain ⟨hfin, hbound⟩ := picardTorsion_bound_of_connectedComponents (AlgebraicClosure k)
    ((pullback g a).reductionι ≫ pullback.snd g a) hdimR ℓ hℓ'
  exact picardTorsion_bound_of_reducedBaseChange k g hdim ℓ hℓ hfin hbound

end AlgebraicGeometry

end
