module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.MvPowerSeries.Equiv
public import Mathlib.RingTheory.MvPowerSeries.Inverse
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.MittagLeffler.MvPowerSeries
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.LocalConnectedness.DenseOpen
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.PurityBranchLocus.ExtendFiniteEtale
public import StacksFrontier.RingTheory.Depth.FlatLocalHom
public import StacksFrontier.RingTheory.LocalCohomology.HartshorneConnectednessHenselian

/-!
# Ramanujam--Samuel for finite étale covers of a power series ring

Let `(A, 𝔪)` be a Noetherian local ring of depth at least two and let `B = A[[x_1, …, x_d]]`
with `d ≥ 1`. For an open `V ⊆ Y = Spec B` which contains every prime `𝔮` of `B` with
`𝔮 ∩ A ≠ 𝔪` and contains the prime `𝔪B`, the functor `FÉt_Y ⟶ FÉt_V` is an equivalence; in
particular purity holds for `B`. This is [Stacks, Tag 0EYA].

The source's first paragraph is proved here. A prime `𝔮` of `B` outside `V` lies over `𝔪`, so
`A ⟶ B_𝔮` is a flat local homomorphism — flatness of `B` over `A` being [Stacks, Tag 059T] —
and therefore `depth(B_𝔮) ≥ 2` by [Stacks, Tag 0337]. That is
`two_le_depth_of_isLocalization_atPrime_mvPowerSeries`, which is what feeds the local hypothesis
of [Stacks, Tag 0BQF].

## Main results

* `Stacks.FundamentalGroup.two_le_depth_of_isLocalization_atPrime_mvPowerSeries` — the local ring
  of `B` at a prime lying over `𝔪` has depth at least two.
* `Stacks.FundamentalGroup.two_le_depth_stalk_of_notMem_mvPowerSeries` — the same statement for
  the stalk of `Spec B` at a point outside such an open `V`.
* `Stacks.FundamentalGroup.isConnectedPuncturedStrictHenselization_of_two_le_depth` —
  [Stacks, Tag 0BLR] in the spelling [Stacks, Tag 0BQF] consumes.
* `Stacks.FundamentalGroup.isEquivalence_finiteEtaleBaseChange_mvPowerSeries` —
  **[Stacks, Tag 0EYA]**; the fully faithful half is proved, essential surjectivity is carried.
* `Stacks.FundamentalGroup.dense_puncturedSpectrum_mvPowerSeries` and the two
  `mem_puncturedSpectrum_of_*` lemmas — the punctured spectrum of `B` is dense and satisfies the
  tag's two conditions on `V`.
* The tag's final assertion, that purity holds for `B`, is part of
  `Stacks.FundamentalGroup.isEquivalence_finiteEtaleBaseChange_and_hasPurity_mvPowerSeries`
  in `StacksFrontier.AlgebraicGeometry.FundamentalGroup.PurityPowerSeries`.

## What is carried

Only essential surjectivity, the source's second paragraph. In
`isEquivalence_finiteEtaleBaseChange_mvPowerSeries` it is the hypothesis `hessSurj` at the given
`V`, and the density of `V` that [Stacks, Tag 0BQF] requires — and that the source does not
verify when it appeals to that tag — is the hypothesis `hdense`. Both are discharged in
`Stacks.FundamentalGroup.isEquivalence_finiteEtaleBaseChange_and_hasPurity_mvPowerSeries`.

The fully faithful half is proved: see the docstring of
`isEquivalence_finiteEtaleBaseChange_mvPowerSeries`.

## References

* [Stacks Project, Tag 0337](https://stacks.math.columbia.edu/tag/0337)
* [Stacks Project, Tag 059T](https://stacks.math.columbia.edu/tag/059T)
* [Stacks Project, Tag 0BLR](https://stacks.math.columbia.edu/tag/0BLR)
* [Stacks Project, Tag 0BQF](https://stacks.math.columbia.edu/tag/0BQF)
* [Stacks Project, Tag 0EY6](https://stacks.math.columbia.edu/tag/0EY6)
* [Stacks Project, Tag 0EY9](https://stacks.math.columbia.edu/tag/0EY9)
* [Stacks Project, Tag 0EYA](https://stacks.math.columbia.edu/tag/0EYA)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory IsLocalRing

universe u

namespace Stacks.FundamentalGroup

/-! ### Depth at a prime lying over the maximal ideal -/

/-- **Depth two at a prime of `B = A[[x_1, …, x_d]]` lying over `𝔪`.** Let `(A, 𝔪)` be a
Noetherian local ring of depth at least two and let `𝔮` be a prime of `B` whose contraction to
`A` is `𝔪`. Then any localization of `B` at `𝔮` has depth at least two.

Indeed `B` is flat over `A` by the flatness half of [Stacks, Tag 059T], so `A ⟶ B_𝔮` is a flat
local homomorphism, and [Stacks, Tag 0337] writes `depth(B_𝔮)` as `depth(A)` plus the depth of
the fibre ring. -/
public theorem two_le_depth_of_isLocalization_atPrime_mvPowerSeries (A : Type u) [CommRing A]
    [IsLocalRing A] [IsNoetherianRing A] (d : ℕ)
    (hdepth : (2 : ℕ∞) ≤ Module.depth A (maximalIdeal A) A)
    (q : Ideal (MvPowerSeries (Fin d) A)) [q.IsPrime]
    (hq : q.comap (MvPowerSeries.C : A →+* MvPowerSeries (Fin d) A) = maximalIdeal A)
    (Bq : Type u) [CommRing Bq] [IsLocalRing Bq]
    [Algebra (MvPowerSeries (Fin d) A) Bq] [IsLocalization.AtPrime Bq q] :
    (2 : ℕ∞) ≤ Module.depth Bq (maximalIdeal Bq) Bq := by
  have hCA : (algebraMap A (MvPowerSeries (Fin d) A)) =
      (MvPowerSeries.C : A →+* MvPowerSeries (Fin d) A) := by
    ext a; simp [MvPowerSeries.algebraMap_apply]
  have : IsNoetherianRing Bq :=
    IsLocalization.isNoetherianRing q.primeCompl Bq inferInstance
  let : Algebra A Bq :=
    ((algebraMap (MvPowerSeries (Fin d) A) Bq).comp
      (algebraMap A (MvPowerSeries (Fin d) A))).toAlgebra
  have : IsScalarTower A (MvPowerSeries (Fin d) A) Bq :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : Module.Flat A (MvPowerSeries (Fin d) A) :=
    (Module.flat_and_mittagLeffler_mvPowerSeries A d).1
  have : Module.Flat (MvPowerSeries (Fin d) A) Bq := IsLocalization.flat Bq q.primeCompl
  have : Module.Flat A Bq := Module.Flat.trans A (MvPowerSeries (Fin d) A) Bq
  have : IsLocalHom (algebraMap A Bq) := by
    refine ⟨fun a ha => ?_⟩
    by_contra hu
    have hmem : (MvPowerSeries.C a : MvPowerSeries (Fin d) A) ∈ q := by
      have h : a ∈ maximalIdeal A := (mem_maximalIdeal a).2 hu
      rw [← hq, Ideal.mem_comap] at h
      exact h
    have hmax : algebraMap A Bq a ∈ maximalIdeal Bq := by
      have h := (IsLocalization.AtPrime.to_map_mem_maximal_iff Bq q
        (MvPowerSeries.C a : MvPowerSeries (Fin d) A)).2 hmem
      rwa [show algebraMap A Bq a =
        algebraMap (MvPowerSeries (Fin d) A) Bq (MvPowerSeries.C a) from by
          rw [← hCA]; rfl]
    exact (mem_maximalIdeal _).1 hmax ha
  rw [Module.depth_self_eq_depth_self_add_depth_quotient_map_maximalIdeal A Bq]
  exact hdepth.trans le_self_add

/-- **Depth two at the stalks outside `V`.** Let `(A, 𝔪)` be a Noetherian local ring of depth at
least two and let `V` be an open of `Spec B`, `B = A[[x_1, …, x_d]]`, containing every prime of
`B` whose contraction to `A` is not `𝔪`. Then the local ring of `Spec B` at a point outside `V`
has depth at least two. -/
public theorem two_le_depth_stalk_of_notMem_mvPowerSeries (A : Type u) [CommRing A]
    [IsLocalRing A] [IsNoetherianRing A] (d : ℕ)
    (hdepth : (2 : ℕ∞) ≤ Module.depth A (maximalIdeal A) A)
    (V : (Spec (.of (MvPowerSeries (Fin d) A))).Opens)
    (hV₁ : ∀ q : PrimeSpectrum (MvPowerSeries (Fin d) A),
      q.asIdeal.comap (MvPowerSeries.C : A →+* MvPowerSeries (Fin d) A) ≠ maximalIdeal A →
        q ∈ V)
    (x : Spec (.of (MvPowerSeries (Fin d) A))) (hx : x ∉ V) :
    (2 : ℕ∞) ≤ Module.depth ((Spec (.of (MvPowerSeries (Fin d) A))).presheaf.stalk x)
      (maximalIdeal ((Spec (.of (MvPowerSeries (Fin d) A))).presheaf.stalk x))
      ((Spec (.of (MvPowerSeries (Fin d) A))).presheaf.stalk x) := by
  have : x.asIdeal.IsPrime := x.isPrime
  let : Algebra (MvPowerSeries (Fin d) A)
      ((Spec (.of (MvPowerSeries (Fin d) A))).presheaf.stalk x) :=
    StructureSheaf.stalkAlgebra (CommRingCat.of (MvPowerSeries (Fin d) A)) x
  have : IsLocalization.AtPrime
      ((Spec (.of (MvPowerSeries (Fin d) A))).presheaf.stalk x) x.asIdeal :=
    StructureSheaf.IsLocalization.to_stalk (CommRingCat.of (MvPowerSeries (Fin d) A)) x
  exact two_le_depth_of_isLocalization_atPrime_mvPowerSeries A d hdepth x.asIdeal
    (not_ne_iff.1 fun h => hx (hV₁ x h)) _

/-! ### Local connectedness from depth -/

/-- **[Stacks, Tag 0BLR] in the spelling [Stacks, Tag 0BQF] consumes.** The punctured spectrum of
every strict henselization of a Noetherian local ring of depth at least two is connected.

The library's form of Tag 0BLR,
`Stacks.PuncturedSpectrum.isConnected_puncturedSpectrum_strictHenselization_of_two_le_depth`, is
stated for a ring carrying an `IsLocalRing.IsHenselization` instance, whereas
`AlgebraicGeometry.IsConnectedPuncturedStrictHenselization` quantifies over the strict
henselizations recognized by `Stacks.StrictHenselization.IsStrictHenselization`. The three fields
of the former are read off the latter once the separable algebraic closure of `R ⧸ 𝔪` is
transported to one of `κ(𝔪)` along the canonical isomorphism between them. -/
public theorem isConnectedPuncturedStrictHenselization_of_two_le_depth (R : Type u) [CommRing R]
    [IsLocalRing R] [IsNoetherianRing R]
    (hdepth : (2 : ℕ∞) ≤ Module.depth R (maximalIdeal R) R) :
    IsConnectedPuncturedStrictHenselization R := by
  intro κsep _ _ _ Rsh _ _ _ h
  let quotientEquiv := AlgEquiv.ofBijective
    (Algebra.ofId (ResidueField R) (maximalIdeal R).ResidueField)
    (Ideal.bijective_algebraMap_quotient_residueField (maximalIdeal R))
  let : Algebra.IsSeparable (ResidueField R) (maximalIdeal R).ResidueField :=
    AlgEquiv.Algebra.isSeparable quotientEquiv
  let : Algebra (ResidueField R) κsep :=
    ((algebraMap (maximalIdeal R).ResidueField κsep).comp
      (algebraMap (ResidueField R) (maximalIdeal R).ResidueField)).toAlgebra
  let : IsScalarTower (ResidueField R) (maximalIdeal R).ResidueField κsep :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  let : IsSepClosure (ResidueField R) κsep :=
    ⟨IsSepClosure.sep_closed (maximalIdeal R).ResidueField,
      Algebra.IsSeparable.trans (ResidueField R) (maximalIdeal R).ResidueField κsep⟩
  let quotientEquivSh := AlgEquiv.ofBijective
    (Algebra.ofId (ResidueField Rsh) (maximalIdeal Rsh).ResidueField)
    (Ideal.bijective_algebraMap_quotient_residueField (maximalIdeal Rsh))
  let : IsLocalHom (algebraMap R Rsh) := h.isLocalHom
  let : IsLocalRing.IsHenselization R κsep Rsh :=
    ⟨h.henselian, h.isFilteredColimitEtale,
      ⟨h.residueFieldEquiv.trans quotientEquivSh.symm.toRingEquiv, fun x => by
        have hc := RingHom.congr_fun h.residueFieldEquiv_comp
          (algebraMap (ResidueField R) (maximalIdeal R).ResidueField (residue R x))
        have hm := Ideal.ResidueField.map_algebraMap (maximalIdeal R) (maximalIdeal Rsh)
          (algebraMap R Rsh) (IsLocalRing.maximalIdeal_comap (algebraMap R Rsh)).symm x
        simp only [RingHom.coe_comp, Function.comp_apply] at hc
        have htower : (algebraMap (ResidueField R) (maximalIdeal R).ResidueField)
              ((residue R) x) = algebraMap R (maximalIdeal R).ResidueField x :=
          (IsScalarTower.algebraMap_apply R (ResidueField R)
            (maximalIdeal R).ResidueField x).symm
        have hmap : (Ideal.ResidueField.map (maximalIdeal R) (maximalIdeal Rsh)
              (algebraMap R Rsh) (IsLocalRing.maximalIdeal_comap (algebraMap R Rsh)).symm)
              ((algebraMap (ResidueField R) (maximalIdeal R).ResidueField) ((residue R) x))
            = algebraMap Rsh (maximalIdeal Rsh).ResidueField ((algebraMap R Rsh) x) := by
          rw [htower]; exact hm
        have hfinal : h.residueFieldEquiv ((algebraMap (ResidueField R) κsep) ((residue R) x))
            = quotientEquivSh ((residue Rsh) ((algebraMap R Rsh) x)) :=
          hc.trans (hmap.trans (IsScalarTower.algebraMap_apply Rsh (ResidueField Rsh)
            (maximalIdeal Rsh).ResidueField ((algebraMap R Rsh) x)))
        calc (h.residueFieldEquiv.trans quotientEquivSh.symm.toRingEquiv)
              ((algebraMap (ResidueField R) κsep) ((residue R) x))
            = quotientEquivSh.symm (h.residueFieldEquiv
                ((algebraMap (ResidueField R) κsep) ((residue R) x))) := rfl
          _ = quotientEquivSh.symm (quotientEquivSh ((residue Rsh) ((algebraMap R Rsh) x))) :=
              congrArg _ hfinal
          _ = (residue Rsh) ((algebraMap R Rsh) x) := quotientEquivSh.symm_apply_apply _⟩⟩
  exact Stacks.PuncturedSpectrum.isConnected_puncturedSpectrum_strictHenselization_of_two_le_depth
    R Rsh κsep hdepth

/-! ### Tag 0EYA -/

/-- **[Stacks, Tag 0EYA]** (Ramanujam--Samuel for finite étale covers). Let `(A, 𝔪)` be a
Noetherian local ring of depth at least two and let `B = A[[x_1, …, x_d]]` with `d ≥ 1`. Let
`V ⊆ Y = Spec B` be an open which contains every prime `𝔮` of `B` with `𝔮 ∩ A ≠ 𝔪` and contains
the prime `𝔪B`. Then the restriction functor `FÉt_Y ⟶ FÉt_V` is an equivalence.

The two conditions on `V` are `hV₁` and `hV₂`. `hV₂` is phrased as a condition on the points of
`Spec B` rather than on the ideal `𝔪B`, so that the primality of `𝔪B` need not be produced.

The fully faithful half is proved: a point of `Spec B` outside `V` lies over `𝔪` by `hV₁`, so its
local ring has depth at least two by `two_le_depth_stalk_of_notMem_mvPowerSeries`, which is
flatness of `B` over `A` ([Stacks, Tag 059T]) fed to [Stacks, Tag 0337];
`isConnectedPuncturedStrictHenselization_of_two_le_depth` ([Stacks, Tag 0BLR]) turns that into
the local hypothesis of [Stacks, Tag 0BQF], which concludes. That is the source's first
paragraph.

Two hypotheses are carried.

* `hdense` is the density of `V` in `Spec B`, which [Stacks, Tag 0BQF] requires and which the
  source does not verify when it appeals to that tag.
* `hessSurj` is essential surjectivity, the source's second paragraph: the unique finite
  extension `Spec C ⟶ Y` of a finite étale `W ⟶ V` from [Stacks, Tag 0EY6], the isomorphism
  `C ≅ C₀ ⊗_A B` obtained from [Stacks, Tag 0EY9] over `U ×_X Y` through the compatibility of
  that construction with flat base change and with change of opens, and the deduction that
  `A ⟶ C₀` is finite étale — a step at which the source itself writes "small detail omitted". -/
@[stacks 0EYA "the fully faithful half unconditionally: a point of `Spec B` outside `V` lies \
over `𝔪` by the tag's condition (1), hence its local ring has depth at least two, by flatness \
of `B` over `A` (Tag 059T) fed to Tag 0337, which is the source's first paragraph; Tag 0BLR \
through `isConnectedPuncturedStrictHenselization_of_two_le_depth` turns that into the local \
hypothesis of Tag 0BQF, which gives full faithfulness. Two hypotheses are carried. `hessSurj` \
is the essential surjectivity half, that is the whole of the source's second paragraph, \
standing for Tag 0EY6 and Tag 0EY9 together with the step the source itself marks `small \
detail omitted`. `hdense` is the density of `V` in `Spec B`, which Tag 0BQF requires and which \
the source does not verify. The tag's condition (2) on `V` and its hypothesis `d ≥ 1` are \
stated; they are used by the purity corollary `hasPurity_mvPowerSeries` below rather than by \
the equivalence itself."]
public theorem isEquivalence_finiteEtaleBaseChange_mvPowerSeries (A : Type u) [CommRing A]
    [IsLocalRing A] [IsNoetherianRing A] (d : ℕ) (hd : 0 < d)
    (hdepth : (2 : ℕ∞) ≤ Module.depth A (maximalIdeal A) A)
    (V : (Spec (.of (MvPowerSeries (Fin d) A))).Opens)
    (hV₁ : ∀ q : PrimeSpectrum (MvPowerSeries (Fin d) A),
      q.asIdeal.comap (MvPowerSeries.C : A →+* MvPowerSeries (Fin d) A) ≠ maximalIdeal A →
        q ∈ V)
    (hV₂ : ∀ q : PrimeSpectrum (MvPowerSeries (Fin d) A),
      q.asIdeal = Ideal.map (MvPowerSeries.C : A →+* MvPowerSeries (Fin d) A)
        (maximalIdeal A) → q ∈ V)
    (hdense : Dense (V : Set (Spec (.of (MvPowerSeries (Fin d) A)))))
    (hessSurj : (finiteEtaleBaseChange V.ι).EssSurj) :
    (finiteEtaleBaseChange V.ι).IsEquivalence := by
  -- The tag's `d ≥ 1` and its condition (2) on `V` are stated but are consumed only by the
  -- purity corollary below.
  have : 0 < d := hd
  have : ∀ q : PrimeSpectrum (MvPowerSeries (Fin d) A),
      q.asIdeal = Ideal.map (MvPowerSeries.C : A →+* MvPowerSeries (Fin d) A)
        (maximalIdeal A) → q ∈ V := hV₂
  have : IsNoetherian (Spec (.of (MvPowerSeries (Fin d) A))) := inferInstance
  obtain ⟨hff⟩ := fullyFaithful_finiteEtaleBaseChange_of_dense_of_noetherianSpace
    (Spec (.of (MvPowerSeries (Fin d) A))) V hdense fun x hx => by
      have : IsNoetherianRing ((Spec (.of (MvPowerSeries (Fin d) A))).presheaf.stalk x) :=
        inferInstance
      exact isConnectedPuncturedStrictHenselization_of_two_le_depth _
        (two_le_depth_stalk_of_notMem_mvPowerSeries A d hdepth V hV₁ x hx)
  exact { faithful := hff.faithful, full := hff.full, essSurj := hessSurj }

/-! ### The punctured spectrum of `B` -/

/-- The structure map `A ⟶ A[[x_1, …, x_d]]` of a power series ring over a local ring is a local
homomorphism: a power series is a unit exactly when its constant coefficient is. -/
public theorem isLocalHom_mvPowerSeries_C (A : Type u) [CommRing A] [IsLocalRing A] (d : ℕ) :
    IsLocalHom (MvPowerSeries.C : A →+* MvPowerSeries (Fin d) A) :=
  ⟨fun a ha => by simpa using MvPowerSeries.isUnit_iff_constantCoeff.1 ha⟩

/-- **Condition (1) of [Stacks, Tag 0EYA] for the punctured spectrum of `B`.** A prime of
`B = A[[x_1, …, x_d]]` whose contraction to `A` is not `𝔪` is not the closed point of `Spec B`,
because the closed point contracts to `𝔪`. -/
public theorem mem_puncturedSpectrum_of_comap_ne_maximalIdeal (A : Type u) [CommRing A]
    [IsLocalRing A] (d : ℕ) (q : PrimeSpectrum (MvPowerSeries (Fin d) A))
    (hq : q.asIdeal.comap (MvPowerSeries.C : A →+* MvPowerSeries (Fin d) A) ≠ maximalIdeal A) :
    q ∈ Stacks.puncturedSpectrum (MvPowerSeries (Fin d) A) := by
  have := isLocalHom_mvPowerSeries_C A d
  refine (Stacks.mem_puncturedSpectrum _).2 fun hc => hq ?_
  rw [show q.asIdeal = maximalIdeal (MvPowerSeries (Fin d) A) from
    congrArg PrimeSpectrum.asIdeal hc]
  exact IsLocalRing.maximalIdeal_comap (MvPowerSeries.C : A →+* MvPowerSeries (Fin d) A)

/-- The ideal `𝔪B` of `B = A[[x_1, …, x_d]]` consists of power series all of whose coefficients
lie in `𝔪`: it is contained in the kernel of the coefficientwise reduction to the residue field
of `A`. -/
public theorem map_maximalIdeal_le_ker_map_residue (A : Type u) [CommRing A] [IsLocalRing A]
    (d : ℕ) : Ideal.map (MvPowerSeries.C : A →+* MvPowerSeries (Fin d) A) (maximalIdeal A) ≤
      RingHom.ker (MvPowerSeries.map (σ := Fin d) (residue A)) := by
  rw [Ideal.map_le_iff_le_comap]
  intro a ha
  simp only [Ideal.mem_comap, RingHom.mem_ker, MvPowerSeries.map_C]
  rw [show residue A a = 0 from (residue_eq_zero_iff a).2 ha, map_zero]

/-- A variable lies in the maximal ideal of `B = A[[x_1, …, x_d]]`, its constant coefficient
being zero. -/
public theorem X_mem_maximalIdeal_mvPowerSeries (A : Type u) [CommRing A] [IsLocalRing A]
    (d : ℕ) (i : Fin d) :
    (MvPowerSeries.X i : MvPowerSeries (Fin d) A) ∈ maximalIdeal (MvPowerSeries (Fin d) A) := by
  rw [mem_maximalIdeal, mem_nonunits_iff]
  intro hu
  have := MvPowerSeries.isUnit_iff_constantCoeff.1 hu
  simp at this

/-- The first variable of `A[[x_1, …, x_d]]` is not killed by the coefficientwise reduction to the
residue field of `A`, since its coefficient at `x_1` is `1`. -/
private theorem X_notMem_ker_map_residue (A : Type u) [CommRing A] [IsLocalRing A] {d : ℕ}
    (hd : 0 < d) :
    (MvPowerSeries.X ⟨0, hd⟩ : MvPowerSeries (Fin d) A) ∉
      RingHom.ker (MvPowerSeries.map (σ := Fin d) (residue A)) := by
  intro hk
  rw [RingHom.mem_ker, MvPowerSeries.map_X] at hk
  have := congrArg (MvPowerSeries.coeff (R := ResidueField A) (Finsupp.single ⟨0, hd⟩ 1)) hk
  simp at this

/-- **Condition (2) of [Stacks, Tag 0EYA] for the punctured spectrum of `B`.** With `d ≥ 1` the
ideal `𝔪B` is not the maximal ideal of `B = A[[x_1, …, x_d]]`: the variable `x_1` lies in the
latter, while every coefficient of an element of the former lies in `𝔪`. So a prime equal to
`𝔪B` is not the closed point of `Spec B`. -/
public theorem mem_puncturedSpectrum_of_eq_map_maximalIdeal (A : Type u) [CommRing A]
    [IsLocalRing A] (d : ℕ) (hd : 0 < d) (q : PrimeSpectrum (MvPowerSeries (Fin d) A))
    (hq : q.asIdeal = Ideal.map (MvPowerSeries.C : A →+* MvPowerSeries (Fin d) A)
      (maximalIdeal A)) :
    q ∈ Stacks.puncturedSpectrum (MvPowerSeries (Fin d) A) := by
  refine (Stacks.mem_puncturedSpectrum _).2 fun hc => ?_
  have hid : Ideal.map (MvPowerSeries.C : A →+* MvPowerSeries (Fin d) A) (maximalIdeal A)
      = maximalIdeal (MvPowerSeries (Fin d) A) :=
    hq.symm.trans (congrArg PrimeSpectrum.asIdeal hc)
  exact X_notMem_ker_map_residue A hd (map_maximalIdeal_le_ker_map_residue A d
    (hid ▸ X_mem_maximalIdeal_mvPowerSeries A d ⟨0, hd⟩))

/-- **The punctured spectrum of `B = A[[x_1, …, x_d]]` is dense in `Spec B`** when `d ≥ 1`. The
only open of `Spec B` containing the closed point is the whole space, so it suffices that
`Spec B` has a second point; the kernel of the coefficientwise reduction to the residue field of
`A` is one, being prime because `κ(𝔪)[[x_1, …, x_d]]` is a domain, and different from the
maximal ideal because it does not contain `x_1`. -/
public theorem dense_puncturedSpectrum_mvPowerSeries (A : Type u) [CommRing A] [IsLocalRing A]
    (d : ℕ) (hd : 0 < d) :
    Dense ((Stacks.puncturedSpectrum (MvPowerSeries (Fin d) A) :
      Set (Spec (.of (MvPowerSeries (Fin d) A))))) := by
  have hdom : IsDomain (MvPowerSeries (Fin d) (ResidueField A)) := NoZeroDivisors.to_isDomain _
  have hprime : (RingHom.ker (MvPowerSeries.map (σ := Fin d) (residue A))).IsPrime :=
    RingHom.ker_isPrime _
  set p : PrimeSpectrum (MvPowerSeries (Fin d) A) :=
    ⟨RingHom.ker (MvPowerSeries.map (σ := Fin d) (residue A)), hprime⟩ with hp
  have hpne : p ≠ closedPoint (MvPowerSeries (Fin d) A) := by
    intro hcontra
    have hid : RingHom.ker (MvPowerSeries.map (σ := Fin d) (residue A)) =
        maximalIdeal (MvPowerSeries (Fin d) A) := congrArg PrimeSpectrum.asIdeal hcontra
    exact X_notMem_ker_map_residue A hd (hid ▸ X_mem_maximalIdeal_mvPowerSeries A d ⟨0, hd⟩)
  intro y
  by_cases hy : y = closedPoint (MvPowerSeries (Fin d) A)
  · subst hy
    have hcl : closedPoint (MvPowerSeries (Fin d) A) ∈
        closure ({p} : Set (PrimeSpectrum (MvPowerSeries (Fin d) A))) := by
      rw [PrimeSpectrum.closure_singleton]
      exact IsLocalRing.le_maximalIdeal_of_isPrime p.asIdeal
    exact closure_mono (Set.singleton_subset_iff.2 hpne) hcl
  · exact subset_closure hy

end Stacks.FundamentalGroup

end
