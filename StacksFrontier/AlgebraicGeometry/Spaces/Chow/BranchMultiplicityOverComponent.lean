module

public import StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardClosedSubscheme
public import StacksFrontier.AlgebraicGeometry.Chow.RationalEquivalence.IntersectionInvertibleSheaf
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ComponentMultiplicityEtaleInvariance
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.StructureSheafChartStalkLength
public import StacksFrontier.RingTheory.Branches.CompositionLawMinimalPrimes
public import StacksFrontier.RingTheory.Branches.FlatComapMinimalPrimes
public import StacksFrontier.RingTheory.Length.RingEquiv

/-!
# The multiplicity of a branch is the multiplicity of the component it lies on

Let `U` be a scheme, let `u` be a point of it and let `B` be a henselization or a strict
henselization of the local ring `𝒪_{U, u}`. A *branch* of `U` at `u` in the sense of Stacks 0DQ3
is a minimal prime `q` of `B`; it contracts to a minimal prime `p` of `𝒪_{U, u}`, and `p`
corresponds to an irreducible component `W` of `U` through `u`, namely the one whose generic point
is the image of `p` under `Spec 𝒪_{U, u} ⟶ U`. This file proves

  `length_{B_q}(B_q) = length_{𝒪_{U, η_W}}(𝒪_{U, η_W}) = m_{W, U}`,

`m_{W, U}` being the multiplicity of Stacks 02QU of the component `W` in `U`. So the multiplicity
of a branch is the multiplicity of the irreducible component that the branch lies on.

## Main results

* `Scheme.length_localizationAtPrime_eq_length_stalk_fromSpecStalk_of_isHenselization`: the
  length of `B_q` over itself is the length over itself of the local ring of `U` at the point cut
  out by the prime below `q`.
* `Scheme.exists_irreducibleComponents_componentMultiplicity_eq_of_isHenselization`: the prime
  below a branch is a minimal prime, it cuts out the generic point of an irreducible component `W`
  of `U` through `u`, and the multiplicity of `W` in `U` is the length of `B_q`.
* `Space.length_localizationAtPrime_eq_geometricLength_of_isHenselization`: on an étale scheme
  chart of an algebraic space `X`, the length of `B_q` is the length of Stacks 0EE1 of `𝒪_X` at a
  geometric point over the image of the point cut out by the prime below `q`.
* `Space.length_localizationAtPrime_eq_of_chartSchemeToPoints_fromSpecStalk_eq`: two branches
  whose points below have the same image in `|X|` have the same length.

## References

* [Stacks Project, Tag 02M1](https://stacks.math.columbia.edu/tag/02M1)
* [Stacks Project, Tag 02QU](https://stacks.math.columbia.edu/tag/02QU)
* [Stacks Project, Tag 00ET](https://stacks.math.columbia.edu/tag/00ET)
* [Stacks Project, Tag 0DQ3](https://stacks.math.columbia.edu/tag/0DQ3)
* [Stacks Project, Tag 0DRD](https://stacks.math.columbia.edu/tag/0DRD)
* [Stacks Project, Tag 0EE1](https://stacks.math.columbia.edu/tag/0EE1)
* [Stacks Project, Tag 0EE9](https://stacks.math.columbia.edu/tag/0EE9)
* [Stacks Project, Tag 0ENK](https://stacks.math.columbia.edu/tag/0ENK)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe u v w

namespace AlgebraicGeometry.Scheme

/-- **The length at a branch is the length at the point below it.** Let `U` be a scheme, `u` a
point of it, `B` a henselization or a strict henselization of `𝒪_{U, u}`, and `q` a minimal prime
of `B` lying over the prime `p` of `𝒪_{U, u}`. Then

  `length_{B_q}(B_q) = length_{𝒪_{U, v}}(𝒪_{U, v})`

for `v` the point of `U` cut out by `p`, that is the image of `p` under `Spec 𝒪_{U, u} ⟶ U`. -/
theorem length_localizationAtPrime_eq_length_stalk_fromSpecStalk_of_isHenselization
    {U : Scheme.{u}} (u : U) {B : Type w} [CommRing B] [IsLocalRing B]
    [Algebra ↥(U.presheaf.stalk u) B] (L : Type v) [Field L]
    [Algebra (IsLocalRing.ResidueField ↥(U.presheaf.stalk u)) L]
    [IsLocalRing.IsHenselization ↥(U.presheaf.stalk u) L B]
    (p : PrimeSpectrum ↥(U.presheaf.stalk u)) (q : Ideal B) [q.IsPrime]
    [q.LiesOver p.asIdeal] (hq : q ∈ minimalPrimes B) :
    Module.length (Localization.AtPrime q) (Localization.AtPrime q) =
      Module.length ↥(U.presheaf.stalk (U.fromSpecStalk u p))
        ↥(U.presheaf.stalk (U.fromSpecStalk u p)) := by
  have hiso : IsIso ((U.fromSpecStalk u).stalkMap p) := isIso_stalkMap_fromSpecStalk u p
  rw [Ring.length_localizationAtPrime_eq_of_isHenselization L p.asIdeal q hq,
    Module.length_eq_of_ringEquiv
      (asIso ((U.fromSpecStalk u).stalkMap p)).commRingCatIsoToRingEquiv]
  exact Module.length_eq_of_ringEquiv
    (StructureSheaf.stalkIso (U.presheaf.stalk u) p).toRingEquiv

/-- **The multiplicity of a branch is the multiplicity of the component it lies on.** Let `U` be a
scheme, `u` a point of it, `B` a henselization or a strict henselization of `𝒪_{U, u}`, and `q` a
minimal prime of `B` — a branch of `U` at `u`. Then `q` contracts to a minimal prime of
`𝒪_{U, u}`, that prime cuts out the generic point of an irreducible component `W` of `U` through
`u`, and the multiplicity of Stacks 02QU of `W` in `U` is

  `m_{W, U} = length_{B_q}(B_q)`. -/
theorem exists_irreducibleComponents_componentMultiplicity_eq_of_isHenselization
    (U : Scheme.{u}) (u : U) {B : Type w} [CommRing B] [IsLocalRing B]
    [Algebra ↥(U.presheaf.stalk u) B] (L : Type v) [Field L]
    [Algebra (IsLocalRing.ResidueField ↥(U.presheaf.stalk u)) L]
    [IsLocalRing.IsHenselization ↥(U.presheaf.stalk u) L B]
    (q : Ideal B) (hq : q ∈ minimalPrimes B) :
    ∃ (hp : q.under ↥(U.presheaf.stalk u) ∈ minimalPrimes ↥(U.presheaf.stalk u))
      (W : irreducibleComponents U), u ∈ (W : Set U) ∧
      U.fromSpecStalk u ⟨q.under ↥(U.presheaf.stalk u), hp.1.1⟩ =
          (genericPoints.ofComponent W : U) ∧
        Stacks.Chow.componentMultiplicity (𝟙 U) (genericPoints.ofComponent W) =
          letI : q.IsPrime := hq.1.1
          ((Module.length (Localization.AtPrime q) (Localization.AtPrime q)).toNat : ℤ) := by
  have hqp : q.IsPrime := hq.1.1
  have hflat : (algebraMap ↥(U.presheaf.stalk u) B).Flat :=
    RingHom.flat_algebraMap_iff.2 (IsLocalRing.IsHenselization.flat (L := L))
  have hp : q.under ↥(U.presheaf.stalk u) ∈ minimalPrimes ↥(U.presheaf.stalk u) :=
    StacksDraft.comap_mem_minimalPrimes_of_ringHom_flat _ hflat hq
  obtain ⟨W, huW, hW⟩ := exists_irreducibleComponents_fromSpecStalk_eq u
    ⟨q.under ↥(U.presheaf.stalk u), hp.1.1⟩ hp
  refine ⟨hp, W, huW, hW, ?_⟩
  rw [Stacks.Chow.componentMultiplicity_eq_length_stalk, ← hW,
    ← length_localizationAtPrime_eq_length_stalk_fromSpecStalk_of_isHenselization u L
      ⟨q.under ↥(U.presheaf.stalk u), hp.1.1⟩ q hq]

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Space

/-- **The length at a branch of an algebraic space is a length of its structure sheaf at a
geometric point.** Let `X` be an algebraic space, `V` an étale scheme chart of it, `u` a point of
the chart, `Bh` a henselization or a strict henselization of `𝒪_{V, u}`, and `q` a minimal prime
of `Bh` lying over the prime `p` of `𝒪_{V, u}`. Let `x̄` be a geometric point of `X` lying over
the image in `|X|` of the point of the chart cut out by `p`. Then

  `length_{(Bh)_q}((Bh)_q) = length_{𝒪_X, x̄}`,

the right-hand side being the length of Stacks 0EE1 of the structure sheaf at `x̄`. -/
theorem length_localizationAtPrime_eq_geometricLength_of_isHenselization
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (V : SmallEtale B S hS X) (u : chartScheme V)
    {Bh : Type w} [CommRing Bh] [IsLocalRing Bh]
    [Algebra ↥((chartScheme V).presheaf.stalk u) Bh]
    (L : Type v) [Field L]
    [Algebra (IsLocalRing.ResidueField ↥((chartScheme V).presheaf.stalk u)) L]
    [IsLocalRing.IsHenselization ↥((chartScheme V).presheaf.stalk u) L Bh]
    (p : PrimeSpectrum ↥((chartScheme V).presheaf.stalk u)) (q : Ideal Bh) [q.IsPrime]
    [q.LiesOver p.asIdeal] (hq : q ∈ minimalPrimes Bh)
    (xbar : GeometricPoint B S hS X)
    (hxbar : chartSchemeToPoints B S hS X V ((chartScheme V).fromSpecStalk u p) = xbar.image) :
    Module.length (Localization.AtPrime q) (Localization.AtPrime q) =
      geometricLength B S hS ⟨X, hX⟩ xbar (structureSheafModule B S hS ⟨X, hX⟩) := by
  rw [Scheme.length_localizationAtPrime_eq_length_stalk_fromSpecStalk_of_isHenselization u L p q
      hq,
    ← geometricLength_structureSheafModule_eq_length_chartStalk B S hS ⟨X, hX⟩ xbar V
      ((chartScheme V).fromSpecStalk u p) hxbar]

/-- **Two branches lying on the same component have the same multiplicity.** In the situation of
`AlgebraicGeometry.Space.length_localizationAtPrime_eq_geometricLength_of_isHenselization`, let
`q` and `q'` be two minimal primes of `Bh` whose primes `p` and `p'` below cut out points of the
chart with the *same* image in `|X|` — in particular two branches lying on one irreducible
component of `|X|`, by `AlgebraicGeometry.Space.isGenericPoint_componentOfBranch`. Then

  `length_{(Bh)_q}((Bh)_q) = length_{(Bh)_{q'}}((Bh)_{q'})`. -/
theorem length_localizationAtPrime_eq_of_chartSchemeToPoints_fromSpecStalk_eq
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (V : SmallEtale B S hS X) (u : chartScheme V)
    {Bh : Type w} [CommRing Bh] [IsLocalRing Bh]
    [Algebra ↥((chartScheme V).presheaf.stalk u) Bh]
    (L : Type v) [Field L]
    [Algebra (IsLocalRing.ResidueField ↥((chartScheme V).presheaf.stalk u)) L]
    [IsLocalRing.IsHenselization ↥((chartScheme V).presheaf.stalk u) L Bh]
    (p p' : PrimeSpectrum ↥((chartScheme V).presheaf.stalk u)) (q q' : Ideal Bh)
    [q.IsPrime] [q'.IsPrime] [q.LiesOver p.asIdeal] [q'.LiesOver p'.asIdeal]
    (hq : q ∈ minimalPrimes Bh) (hq' : q' ∈ minimalPrimes Bh)
    (h : chartSchemeToPoints B S hS X V ((chartScheme V).fromSpecStalk u p) =
      chartSchemeToPoints B S hS X V ((chartScheme V).fromSpecStalk u p')) :
    Module.length (Localization.AtPrime q) (Localization.AtPrime q) =
      Module.length (Localization.AtPrime q') (Localization.AtPrime q') := by
  have hx : chartSchemeToPoints B S hS X V ((chartScheme V).fromSpecStalk u p) =
      (canonicalGeometricPoint B S hS X
        (chartSchemeToPoints B S hS X V ((chartScheme V).fromSpecStalk u p))).image :=
    (canonicalGeometricPoint_image B S hS X _).symm
  rw [length_localizationAtPrime_eq_geometricLength_of_isHenselization B S hS hX V u L p q hq _ hx,
    length_localizationAtPrime_eq_geometricLength_of_isHenselization B S hS hX V u L p' q' hq' _
      (h.symm.trans hx)]

end AlgebraicGeometry.Space

end
