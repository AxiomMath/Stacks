module

public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.RingTheory.Smooth.Locus
public import StacksFrontier.FieldTheory.Separable.TFAE
public import StacksFrontier.RingTheory.FormallySmooth.Field
public import StacksFrontier.RingTheory.GeometricallyIntegral.ConstructibleFibreLocus05FT
public import StacksFrontier.RingTheory.GeometricallyIntegral.FibrewiseDense
public import StacksFrontier.RingTheory.GeometricallyReduced.SmoothLocus
public import StacksFrontier.RingTheory.MinimalPrimes.Reduced
public import StacksFrontier.RingTheory.Smooth.LocusBaseChange
public import StacksFrontier.RingTheory.Smooth.Reduced
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The good half of the generic-fibre dichotomy for geometric reducedness

Stacks 0578 says: for `f : X → Y` of finite type with `Y` irreducible with generic point `η`, if
the generic fibre `X_η` is geometrically reduced then the fibres `X_y` are geometrically reduced
for every `y` in a nonempty open of `Y`. This file proves the affine case over a Noetherian
domain, **unconditionally**, and deduces the affine case of Stacks 0579: over a Noetherian ring
the geometrically reduced fibre locus of a finite type algebra is constructible.

Before this file, `StacksFrontier.RingTheory.GeometricallyIntegral.FibrewiseDense` had reduced that
good half to the production of a tuple `g 1, …, g m` of elements of the algebra whose basic opens
are scheme theoretically dense in the generic fibre and have geometrically reduced fibres over
the base. This file produces the tuple.

## The argument

Let `D` be a Noetherian domain with fraction field `F` and `T` a finite type `D`-algebra, which is
then of finite presentation. Suppose the generic fibre is geometrically reduced.

* The generic fibre `F ⊗[D] T` is a geometrically reduced `F`-algebra
  (`Algebra.isGeometricallyReduced_fractionRing_tensorProduct`): geometric reducedness over a
  field is reducedness of the base change to an algebraic closure `L` of `F` (Stacks 030V), `L` is
  a field over `D` with zero kernel, and `L ⊗[F] (F ⊗[D] T)` is the fibre `T ⊗[D] L`.
* The smooth locus of a geometrically reduced algebra over a field is dense
  (`Algebra.dense_smoothLocus_of_isGeometricallyReduced`). This is the affine form of the direction
  of Stacks 056V that the source uses. That the smooth locus contains every minimal prime is
  `Algebra.mem_smoothLocus_of_mem_minimalPrimes`, taken from
  `StacksFrontier.RingTheory.GeometricallyReduced.SmoothLocus`: the algebra is reduced, so at a
  minimal prime the localization is a field; geometric reducedness passes to localizations; and a
  geometrically reduced field extension is formally smooth, by Stacks 0321 and the equivalence of
  separability with geometric reducedness (Stacks 030W). Density follows because every prime lies
  in the closure of a minimal prime below it.
* That smooth locus is the inverse image of the smooth locus of `D → T`, because `D → F` is flat
  and `D → T` is of finite presentation: this is `Algebra.smoothLocus_comap_of_isPushout`,
  Stacks 00TG, which is the content of Stacks 02V4 that the proof of Stacks 0578 needs. The source
  invokes Stacks 02V4 in its case (1), which asks `f` to be flat and therefore costs it an appeal
  to Stacks 052A to shrink the base first; case (2), which asks only that the *base change* be
  flat, applies here with no shrinking because `Spec F → Spec D` is flat for free, and that is why
  Stacks 052A is not needed below.
* The smooth locus of `D → T` is the union of the basic opens `D(g)` with `T_g` smooth over `D`
  (`Algebra.smoothLocus_eq_iUnion_basicOpen`), so the generic-fibre smooth locus is the union of
  the `D(1 ⊗ g)` for those `g`. The generic fibre is a Noetherian ring, so its spectrum is a
  Noetherian space and finitely many of those basic opens already cover; being a cover of a dense
  set they are dense, and a dense union of basic opens of a *reduced* ring is scheme theoretically
  dense (`Algebra.eq_zero_of_forall_mul_eq_zero_of_dense`). That is
  `Algebra.exists_smooth_away_dense_genericFibre`.
* Each such `g` has `(K ⊗[D] T)_{1 ⊗ g} = K ⊗[D] T_g` smooth over `K`, hence reduced by Stacks
  033B, for every field `K` over `D`: `Algebra.isReduced_localizationAway_one_tmul_of_smooth`. This
  is the appeal to Stacks 056T in the source, in its affine form.
* `Algebra.exists_basicOpen_subset_geometricallyReducedFibreLocus_of_mulTuple` then concludes.

## Main results

* `Algebra.IsGeometricallyReduced.of_isLocalization`: geometric reducedness over a field passes to
  localizations.
* `Algebra.dense_smoothLocus_of_isGeometricallyReduced`: **the affine case of the direction of
  Stacks 056V used by Stacks 0578.** The smooth locus of a geometrically reduced algebra over a
  field is dense.
* `Algebra.exists_smooth_away_dense_genericFibre`: **the tuple of Stacks 0578 exists.**
* `Algebra.exists_basicOpen_subset_geometricallyReducedFibreLocus`: **the affine case of
  Stacks 0578 at the generic point, unconditionally.**
* `Algebra.isConstructible_geometricallyReducedFibreLocus'`: **the affine case of Stacks 0579.**
* `Algebra.isConstructible_geometricallyIntegralFibreLocus_of_irreducible_goodGeneric` and
  `Algebra.isConstructible_geometricallyIntegralFibreLocus_of_free_irreducible_half`:
  constructibility of the geometrically integral fibre locus over a Noetherian base now rests on
  the good half of Stacks 055A alone.

## What this does and does not discharge

`Algebra.isConstructible_geometricallyIntegralFibreLocus_of_free_halves` took *two* hypotheses, the
good halves of the affine cases of Stacks 0578 and Stacks 055A at the generic point. The first is
now proved, so the constructibility hypothesis of the dévissage theorems,
```
∀ (R₀ S₀ : Type u) [CommRing R₀] [CommRing S₀] [Algebra R₀ S₀] [IsNoetherianRing R₀]
  [Algebra.FiniteType R₀ S₀] [Module.Flat R₀ S₀],
  Topology.IsConstructible (Algebra.geometricallyIntegralFibreLocus R₀ S₀)
```
— fourteen binders in the library, among them
`Module.CompleteDevissageAt.nonempty_linearEquiv_directSum_of_flat`, which is Stacks 05I4's
decomposition — follows from the good half of Stacks 055A and nothing else. That half is *not*
proved here, so no `@[stacks 05FT]`, `@[stacks 05I4]` or `@[stacks 055A]` tag becomes available.

No Stacks attribute is placed in this file either, for the reason the sibling files give: Stacks
0578, 0579, 056V and 056T are statements about schemes and only their affine cases are reached,
and the affine case of 0579 is proved only over a Noetherian base, whereas the source's 0579 has
no Noetherian hypothesis — it reduces to the Noetherian case through Stacks 01ZM, which is not
used here.

## Implementation notes

`Algebra.TensorProduct.rightAlgebra` is a local instance in the section proving
`Algebra.exists_smooth_away_dense_genericFibre`, because `Algebra.smoothLocus_comap_of_isPushout`
is stated along `S → S'` and so needs `T` to act on `F ⊗[D] T`. It is scoped to that section and
appears in no statement; `algebraMap T (F ⊗[D] T) g` is `1 ⊗ₜ g` by `rfl`.

The locus is neither always empty nor always everything, so the statements have content:
`Algebra.geometricallyReducedFibreLocus_self_eq_univ` gives the one extreme and
`Algebra.notMem_geometricallyReducedFibreLocus_quotient_span_X_sq` the other, with the dual
numbers `k[X]/(X²)` over a field. The latter also shows that the hypothesis of the good half
cannot be dropped: a nonzero element of a field has basic open all of `Spec k`, so for that
algebra the *conclusion* of
`Algebra.exists_basicOpen_subset_geometricallyReducedFibreLocus` is false.

## References

* [Stacks Project, Tag 0578](https://stacks.math.columbia.edu/tag/0578)
* [Stacks Project, Tag 0579](https://stacks.math.columbia.edu/tag/0579)
* [Stacks Project, Tag 056V](https://stacks.math.columbia.edu/tag/056V)
* [Stacks Project, Tag 056T](https://stacks.math.columbia.edu/tag/056T)
* [Stacks Project, Tag 02V4](https://stacks.math.columbia.edu/tag/02V4)
* [Stacks Project, Tag 00TG](https://stacks.math.columbia.edu/tag/00TG)
* [Stacks Project, Tag 030V](https://stacks.math.columbia.edu/tag/030V)
* [Stacks Project, Tag 030W](https://stacks.math.columbia.edu/tag/030W)
* [Stacks Project, Tag 0321](https://stacks.math.columbia.edu/tag/0321)
* [Stacks Project, Tag 033B](https://stacks.math.columbia.edu/tag/033B)
* [Stacks Project, Tag 05FT](https://stacks.math.columbia.edu/tag/05FT)
* [Stacks Project, Tag 055A](https://stacks.math.columbia.edu/tag/055A)
-/

@[expose] public section

open PrimeSpectrum Topology

open scoped TensorProduct

universe u

namespace Algebra

section DenseSmoothLocus

/-- **Geometric reducedness passes to a localization.** If `A` is a geometrically reduced algebra
over a field `k` and `B` is a localization of `A`, then `B` is geometrically reduced over `k`.

By Stacks 030V geometric reducedness over a field is reducedness of the base change to an
algebraic closure `Ω`, and `Ω ⊗[k] B` is a localization of `Ω ⊗[k] A` by
`IsLocalization.tensorProduct_tensorProduct_right`; a localization of a reduced ring is
reduced. -/
theorem IsGeometricallyReduced.of_isLocalization (k A : Type u) [Field k] [CommRing A]
    [Algebra k A] [IsGeometricallyReduced k A] (M : Submonoid A) (B : Type u) [CommRing B]
    [Algebra A B] [Algebra k B] [IsScalarTower k A B] [IsLocalization M B] :
    IsGeometricallyReduced k B := by
  have hA : IsReduced (AlgebraicClosure k ⊗[k] A) := (isGeometricallyReduced_field_iff k A).mp ‹_›
  let : Algebra (AlgebraicClosure k ⊗[k] A) (AlgebraicClosure k ⊗[k] B) :=
    (Algebra.TensorProduct.map (AlgHom.id k (AlgebraicClosure k))
      (IsScalarTower.toAlgHom k A B)).toAlgebra
  have : IsScalarTower (AlgebraicClosure k) (AlgebraicClosure k ⊗[k] A)
      (AlgebraicClosure k ⊗[k] B) :=
    .of_algebraMap_eq fun x => by simp [RingHom.algebraMap_toAlgebra]
  have := IsLocalization.tensorProduct_tensorProduct_right k (AlgebraicClosure k) M B
    (by ext x; simp [RingHom.algebraMap_toAlgebra])
  exact (isGeometricallyReduced_field_iff k B).mpr
    (isReduced_localizationPreserves
      (M.map (Algebra.TensorProduct.includeRight (R := k) (A := AlgebraicClosure k)))
      (AlgebraicClosure k ⊗[k] B) hA)

/-- **A geometrically reduced field extension is formally smooth.** This is Stacks 0321 composed
with the equivalence of separability and geometric reducedness of Stacks 030W. -/
@[ega "0 19.6.1" "Sufficiency", ega "0 21.5.1" "special case"]
theorem FormallySmooth.of_isGeometricallyReduced (k L : Type u) [Field k] [Field L] [Algebra k L]
    [IsGeometricallyReduced k L] : FormallySmooth k L :=
  (FormallySmooth.iff_isSeparableExtension k L).mpr
    (((isSeparableExtension_tfae k L (ringExpChar k)).out 1 4).mpr ‹_›)

/-- **The smooth locus of a geometrically reduced algebra over a field is dense.** This is the
affine form of the easy direction of Stacks 056V: every prime contains a minimal prime, the
minimal primes lie in the smooth locus by
`Algebra.mem_smoothLocus_of_mem_minimalPrimes`, and a prime lies in the closure of every prime
below it. -/
theorem dense_smoothLocus_of_isGeometricallyReduced (k A : Type u) [Field k] [CommRing A]
    [Algebra k A] [IsGeometricallyReduced k A] : Dense (smoothLocus k A) := by
  intro p
  obtain ⟨q, hqmin, hqle⟩ := Ideal.exists_minimalPrimes_le (I := (⊥ : Ideal A)) (J := p.asIdeal)
    bot_le
  have hqprime : q.IsPrime := hqmin.1.1
  refine closure_mono (Set.singleton_subset_iff.mpr
    (mem_smoothLocus_of_mem_minimalPrimes k A ⟨q, hqprime⟩ hqmin)) ?_
  exact (PrimeSpectrum.le_iff_mem_closure (⟨q, hqprime⟩ : PrimeSpectrum A) p).mp hqle

/-- **The smooth locus is the union of the basic opens of the elements with smooth
localization.** For an algebra of finite presentation, a prime lies in the smooth locus exactly
when some element outside it has smooth localization away from it. -/
theorem smoothLocus_eq_iUnion_basicOpen (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]
    [FinitePresentation R A] :
    smoothLocus R A =
      ⋃ g : {g : A // Smooth R (Localization.Away g)},
        (basicOpen (g : A) : Set (PrimeSpectrum A)) :=
  Set.Subset.antisymm
    (fun p hp => by
      have : IsSmoothAt R p.asIdeal := hp
      obtain ⟨g, hgp, hg⟩ := IsSmoothAt.exists_notMem_smooth R p.asIdeal
      exact Set.mem_iUnion.mpr ⟨⟨g, hg⟩, (mem_basicOpen g p).mpr hgp⟩)
    (Set.iUnion_subset fun g =>
      basicOpen_subset_smoothLocus_iff_smooth.mpr g.2)

end DenseSmoothLocus

section SchemeTheoreticDensity

/-- **A topologically dense union of basic opens of a reduced ring is scheme theoretically
dense.** If the basic opens of a family `g` cover a dense subset of `Spec A` and `A` is reduced,
then no nonzero element of `A` is annihilated by every `g i`.

A nonzero element `z` of a reduced ring is not nilpotent, so `D(z)` is a nonempty open; density
puts a prime `p` in `D(z)` and in some `D(g i)`, and then `g i * z = 0` lies in `p` while neither
factor does. -/
theorem eq_zero_of_forall_mul_eq_zero_of_dense {A : Type u} [CommRing A] [IsReduced A]
    {ι : Type*} (g : ι → A)
    (hd : Dense (⋃ i, (basicOpen (g i) : Set (PrimeSpectrum A)))) (z : A)
    (hz : ∀ i, g i * z = 0) : z = 0 := by
  by_contra hz0
  have hne : (basicOpen z : Set (PrimeSpectrum A)).Nonempty := by
    refine Set.nonempty_iff_ne_empty.mpr fun h => hz0 ?_
    exact IsReduced.eq_zero z (basicOpen_eq_bot_iff z |>.mp (TopologicalSpace.Opens.ext h))
  obtain ⟨p, hpz, hpU⟩ := hd.inter_open_nonempty _ (basicOpen z).isOpen hne
  obtain ⟨i, hpi⟩ := Set.mem_iUnion.mp hpU
  rw [SetLike.mem_coe, mem_basicOpen] at hpz hpi
  rcases p.isPrime.mem_or_mem (hz i ▸ p.asIdeal.zero_mem) with h | h
  · exact hpi h
  · exact hpz h

end SchemeTheoreticDensity

section GenericFibre

/-- **The generic fibre of a geometrically reduced generic point is geometrically reduced.** If
the generic point of `Spec D`, for a domain `D`, lies in the geometrically reduced fibre locus of
`T`, then the base change of `T` to the fraction field of `D` is a geometrically reduced algebra
over that fraction field.

By Stacks 030V geometric reducedness over a field is reducedness of the base change to an
algebraic closure `L` of the fraction field; `L` is a field over `D` with zero kernel, so the
fibre `T ⊗[D] L` is reduced by hypothesis, and that fibre is the base change of the generic fibre
by `Algebra.fibreTensorEquiv`. -/
theorem isGeometricallyReduced_fractionRing_tensorProduct {D T : Type u} [CommRing D]
    [IsDomain D] [CommRing T] [Algebra D T]
    (hgen : (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum D) ∈ geometricallyReducedFibreLocus D T) :
    IsGeometricallyReduced (FractionRing D) (FractionRing D ⊗[D] T) := by
  rw [isGeometricallyReduced_field_iff]
  have hinj : Function.Injective (algebraMap D (AlgebraicClosure (FractionRing D))) := by
    rw [IsScalarTower.algebraMap_eq D (FractionRing D) (AlgebraicClosure (FractionRing D))]
    exact (algebraMap (FractionRing D) (AlgebraicClosure (FractionRing D))).injective.comp
      (IsFractionRing.injective D (FractionRing D))
  exact (isReduced_congr
    (fibreTensorEquiv D T (FractionRing D) (AlgebraicClosure (FractionRing D)))).mp
      (hgen _ ((RingHom.injective_iff_ker_eq_bot _).mp hinj))

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- **The tuple of Stacks 0578 exists.** Let `D` be a Noetherian domain and `T` a finite type
`D`-algebra whose generic fibre is geometrically reduced. Then there are finitely many elements
`g 1, …, g m` of `T` such that `T` is smooth over `D` away from each `g j` and such that the
basic opens of the `g j` are scheme theoretically dense in the generic fibre.

This is the step of the proof of Stacks 0578 that produces the data consumed by
`Algebra.exists_basicOpen_subset_geometricallyReducedFibreLocus_of_mulTuple`. The generic fibre is
reduced and geometrically reduced, so its smooth locus over the fraction field `F` is dense
(`Algebra.dense_smoothLocus_of_isGeometricallyReduced`, the affine case of Stacks 056V). By
Stacks 00TG — the affine content of Stacks 02V4, flatness of `D → F` standing in for flatness of
`T` — that smooth locus is the inverse image of the smooth locus of `D → T`, hence is the union
of the basic opens of the `1 ⊗ g` with `T_g` smooth over `D`. The generic fibre is Noetherian, so
finitely many of them suffice, and a dense union of basic opens of a reduced ring is scheme
theoretically dense. -/
theorem exists_smooth_away_dense_genericFibre (D T : Type u) [CommRing D] [IsDomain D]
    [IsNoetherianRing D] [CommRing T] [Algebra D T] [FiniteType D T]
    (hgen : (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum D) ∈ geometricallyReducedFibreLocus D T) :
    ∃ (m : ℕ) (g : Fin m → T), (∀ j, Smooth D (Localization.Away (g j))) ∧
      ∀ z : FractionRing D ⊗[D] T,
        (∀ j, ((1 : FractionRing D) ⊗ₜ g j) * z = 0) → z = 0 := by
  classical
  have : FinitePresentation D T := FinitePresentation.of_finiteType.mp inferInstance
  have hgr : IsGeometricallyReduced (FractionRing D) (FractionRing D ⊗[D] T) :=
    isGeometricallyReduced_fractionRing_tensorProduct hgen
  have : IsNoetherianRing (FractionRing D ⊗[D] T) :=
    FiniteType.isNoetherianRing (FractionRing D) (FractionRing D ⊗[D] T)
  have : IsReduced (FractionRing D ⊗[D] T) := isReduced_of_isGeometricallyReduced (FractionRing D)
  have hcover : smoothLocus (FractionRing D) (FractionRing D ⊗[D] T) =
      ⋃ g : {g : T // Smooth D (Localization.Away g)},
        (basicOpen ((1 : FractionRing D) ⊗ₜ[D] (g : T)) :
          Set (PrimeSpectrum (FractionRing D ⊗[D] T))) := by
    rw [← smoothLocus_comap_of_isPushout D T (FractionRing D) (FractionRing D ⊗[D] T),
      smoothLocus_eq_iUnion_basicOpen D T, Set.preimage_iUnion]
    rfl
  obtain ⟨t, ht⟩ := (TopologicalSpace.NoetherianSpace.isCompact _).elim_finite_subcover _
    (fun _ => (basicOpen _).isOpen) hcover.subset
  refine ⟨t.card, fun j => (t.equivFin.symm j).1.1, fun j => (t.equivFin.symm j).1.2,
    fun z hz => ?_⟩
  refine eq_zero_of_forall_mul_eq_zero_of_dense _
    ((dense_smoothLocus_of_isGeometricallyReduced (FractionRing D)
      (FractionRing D ⊗[D] T)).mono fun p hp => ?_) z hz
  obtain ⟨i, hit, hpi⟩ := Set.mem_iUnion₂.mp (ht hp)
  exact Set.mem_iUnion.mpr ⟨t.equivFin ⟨i, hit⟩, by simpa using hpi⟩

end GenericFibre

section GoodHalf

/-- **A smooth basic open has reduced geometric fibres.** If `T` is smooth over `D` away from `g`
then `(K ⊗[D] T)_{1 ⊗ g}` is reduced for every field `K` over `D`.

That ring is `K ⊗[D] T_g` by `IsLocalization.Away.tensorProductEquivTMulRight`, which is smooth
over `K` because smoothness is stable under base change, hence reduced by Stacks 033B. -/
theorem isReduced_localizationAway_one_tmul_of_smooth {D T : Type u} [CommRing D] [CommRing T]
    [Algebra D T] (g : T) [Smooth D (Localization.Away g)] (K : Type u) [Field K] [Algebra D K] :
    IsReduced (Localization.Away ((1 : K) ⊗ₜ[D] g : K ⊗[D] T)) :=
  (isReduced_congr (IsLocalization.Away.tensorProductEquivTMulRight D K g
    (Localization.Away g)).toRingEquiv).mp
      (isReduced_of_smooth K (K ⊗[D] Localization.Away g))

/-- **The affine case of Stacks 0578 at the generic point, unconditionally.** Let `D` be a
Noetherian domain and `T` a finite type `D`-algebra whose generic fibre is geometrically reduced.
Then a nonempty basic open of `Spec D` is contained in the geometrically reduced fibre locus
of `T`.

This is the *good half* of the generic-fibre dichotomy for geometric reducedness, the hypothesis
`hred` of `Algebra.isConstructible_geometricallyIntegralFibreLocus_of_free_halves` and the
hypothesis `hgood` of `Algebra.isConstructible_geometricallyReducedFibreLocus_of_goodGeneric`. The
tuple is produced by `Algebra.exists_smooth_away_dense_genericFibre` and consumed by
`Algebra.exists_basicOpen_subset_geometricallyReducedFibreLocus_of_mulTuple`; the smooth basic
opens have reduced geometric fibres by
`Algebra.isReduced_localizationAway_one_tmul_of_smooth`. No freeness of `T` over `D` is
needed. -/
theorem exists_basicOpen_subset_geometricallyReducedFibreLocus (D T : Type u) [CommRing D]
    [IsDomain D] [IsNoetherianRing D] [CommRing T] [Algebra D T] [FiniteType D T]
    (hgen : (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum D) ∈ geometricallyReducedFibreLocus D T) :
    ∃ f : D, f ≠ 0 ∧ (basicOpen f : Set (PrimeSpectrum D)) ⊆
      geometricallyReducedFibreLocus D T := by
  obtain ⟨m, g, hsmooth, hdense⟩ := exists_smooth_away_dense_genericFibre D T hgen
  exact exists_basicOpen_subset_geometricallyReducedFibreLocus_of_mulTuple g hdense
    fun K _ _ j => have := hsmooth j; isReduced_localizationAway_one_tmul_of_smooth (g j) K

/-- **The affine case of Stacks 0579.** Over a Noetherian ring `A` the set of points of `Spec A`
whose fibre of a finite type algebra `C` is geometrically reduced is constructible.

The two halves of the generic-fibre dichotomy are
`Algebra.exists_basicOpen_subset_geometricallyReducedFibreLocus` (Stacks 0578) and the already
proved `Algebra.exists_ne_zero_disjoint_geometricallyReducedFibreLocus` (Stacks 0577), combined by
`Algebra.isConstructible_geometricallyReducedFibreLocus_of_goodGeneric`.

The primed name is because the unprimed one is taken by the form of this statement conditional on
the dichotomy, `Algebra.isConstructible_geometricallyReducedFibreLocus`. -/
theorem isConstructible_geometricallyReducedFibreLocus' (A C : Type u) [CommRing A]
    [IsNoetherianRing A] [CommRing C] [Algebra A C] [FiniteType A C] :
    IsConstructible (geometricallyReducedFibreLocus A C) :=
  isConstructible_geometricallyReducedFibreLocus_of_goodGeneric
    (fun D T _ _ _ _ _ _ => exists_basicOpen_subset_geometricallyReducedFibreLocus D T) A C

/-- **Constructibility of the geometrically integral fibre locus rests on the irreducible good
half alone.** Over a Noetherian ring `A` the geometrically integral fibre locus of a finite type
algebra `C` is constructible, granted only the affine case of Stacks 055A at the generic point.

Compare `Algebra.isConstructible_geometricallyIntegralFibreLocus_of_free_halves`, which assumes
both good halves: the reduced one is now
`Algebra.exists_basicOpen_subset_geometricallyReducedFibreLocus` and is no longer a hypothesis. -/
theorem isConstructible_geometricallyIntegralFibreLocus_of_irreducible_goodGeneric
    (hirr : ∀ (D T : Type u) [CommRing D] [IsDomain D] [IsNoetherianRing D] [CommRing T]
      [Algebra D T] [Algebra.FiniteType D T],
      (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum D) ∈ geometricallyIrreducibleFibreLocus D T →
        ∃ f : D, f ≠ 0 ∧ (basicOpen f : Set (PrimeSpectrum D)) ⊆
          geometricallyIrreducibleFibreLocus D T)
    (A C : Type u) [CommRing A] [IsNoetherianRing A] [CommRing C] [Algebra A C]
    [Algebra.FiniteType A C] :
    IsConstructible (geometricallyIntegralFibreLocus A C) :=
  isConstructible_geometricallyIntegralFibreLocus A C
    (isConstructible_geometricallyIrreducibleFibreLocus_of_goodGeneric hirr A C)
    (isConstructible_geometricallyReducedFibreLocus' A C)

/-- The same statement with the irreducible good half restricted to algebras that are free
modules over the base, which is what
`Algebra.exists_basicOpen_subset_geometricallyIrreducibleFibreLocus_of_free` reduces it to. This
is `Algebra.isConstructible_geometricallyIntegralFibreLocus_of_free_halves` with its first
hypothesis discharged. -/
theorem isConstructible_geometricallyIntegralFibreLocus_of_free_irreducible_half
    (hirr : ∀ (D T : Type u) [CommRing D] [IsDomain D] [IsNoetherianRing D] [CommRing T]
      [Algebra D T] [Algebra.FiniteType D T] [Module.Free D T],
      (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum D) ∈ geometricallyIrreducibleFibreLocus D T →
        ∃ f : D, f ≠ 0 ∧ (basicOpen f : Set (PrimeSpectrum D)) ⊆
          geometricallyIrreducibleFibreLocus D T)
    (A C : Type u) [CommRing A] [IsNoetherianRing A] [CommRing C] [Algebra A C]
    [Algebra.FiniteType A C] :
    IsConstructible (geometricallyIntegralFibreLocus A C) :=
  isConstructible_geometricallyIntegralFibreLocus_of_free_halves
    (fun D T _ _ _ _ _ _ _ => exists_basicOpen_subset_geometricallyReducedFibreLocus D T) hirr A C

end GoodHalf

section Content

/-- The algebra of dual numbers over a field, presented as `k[X]/(X²)`, is not reduced. -/
theorem not_isReduced_quotient_span_X_sq (k : Type u) [Field k] :
    ¬ IsReduced (Polynomial k ⧸ Ideal.span {(Polynomial.X : Polynomial k) ^ 2}) := by
  intro h
  have hmem : (Polynomial.X : Polynomial k) ^ 2 ∈
      Ideal.span {(Polynomial.X : Polynomial k) ^ 2} := Ideal.mem_span_singleton_self _
  have hnil : IsNilpotent
      (Ideal.Quotient.mk (Ideal.span {(Polynomial.X : Polynomial k) ^ 2}) Polynomial.X) := by
    refine ⟨2, ?_⟩
    rw [← map_pow]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hmem
  have h0 := h.eq_zero _ hnil
  rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton] at h0
  have := Polynomial.natDegree_le_of_dvd h0 (Polynomial.X_ne_zero (R := k))
  simp at this

/-- **The geometrically reduced fibre locus is not always everything.** Over a field `k` the
dual-number algebra `k[X]/(X²)` has a non-reduced fibre at the only point of `Spec k`, so the
generic point does not lie in its geometrically reduced fibre locus and that locus is empty.

Together with `Algebra.geometricallyReducedFibreLocus_self_eq_univ` this shows the locus takes
both extreme values, so neither the constructibility statement
`Algebra.isConstructible_geometricallyReducedFibreLocus'` nor the good half
`Algebra.exists_basicOpen_subset_geometricallyReducedFibreLocus` is vacuously true; and since a
nonzero element of a field has basic open the whole of `Spec k`, the conclusion of the good half
*fails* for this algebra, so its hypothesis cannot be dropped. -/
theorem notMem_geometricallyReducedFibreLocus_quotient_span_X_sq (k : Type u) [Field k] :
    (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum k) ∉
      geometricallyReducedFibreLocus k
        (Polynomial k ⧸ Ideal.span {(Polynomial.X : Polynomial k) ^ 2}) := by
  intro h
  refine not_isReduced_quotient_span_X_sq k ?_
  have hk : RingHom.ker (algebraMap k k) = (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum k).asIdeal := by
    rw [Algebra.algebraMap_self]
    exact (RingHom.injective_iff_ker_eq_bot _).mp Function.injective_id
  exact (isReduced_congr (Algebra.TensorProduct.rid k k
    (Polynomial k ⧸ Ideal.span {(Polynomial.X : Polynomial k) ^ 2})).toRingEquiv).mp (h k hk)

/-- **The geometrically reduced fibre locus is not always empty**: the base itself has every
fibre a field. -/
theorem geometricallyReducedFibreLocus_self_eq_univ (D : Type u) [CommRing D] :
    geometricallyReducedFibreLocus D D = Set.univ := by
  refine Set.eq_univ_of_forall fun p => ?_
  intro K _ _ _
  exact (isReduced_congr (Algebra.TensorProduct.lid D K).toRingEquiv).mpr inferInstance

end Content

end Algebra

end
