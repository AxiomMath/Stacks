module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.RingTheory.PowerSeries.Ideal
public import Mathlib.RingTheory.PowerSeries.Inverse
public import StacksCore.Tactic.StacksAttribute
import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.Equidimensional
public import StacksFrontier.AlgebraicGeometry.Divisors.FittingIdeals.SingularLocus
public import StacksFrontier.AlgebraicGeometry.Divisors.Meromorphic.FittingIdealsDifferentials
public import StacksFrontier.AlgebraicGeometry.KerDetected.IdealComap
public import StacksFrontier.AlgebraicGeometry.Morphisms.CohenMacaulay.FibreStalk
public import StacksFrontier.AlgebraicGeometry.Morphisms.CohenMacaulay.Fibres
public import StacksFrontier.AlgebraicGeometry.Morphisms.CohenMacaulay.LocusOpen
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.CohenMacaulayRelativeDimension
public import StacksFrontier.AlgebraicGeometry.NumericalCriterion.Basic
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Dimension.Components
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Fibre
public import StacksFrontier.Topology.Dimension.Equidimensional
import StacksFrontier.AlgebraicGeometry.DivisorFlatPullback.Basic
import StacksFrontier.AlgebraicGeometry.Pullback.AffineOpens

/-!
# A criterion for smoothing a proper flat family over a formal disc

Let `k` be a field and let `S = Spec k⟦t⟧` be the formal disc, with closed point the maximal
ideal `(t)` and generic point the zero ideal. The `n`-th infinitesimal neighbourhood of the
closed point is `Sₙ = Spec (k⟦t⟧/(t^n))`. Let `Y → S` be a proper flat morphism of schemes
whose special fibre `X` is Cohen–Macaulay and equidimensional of dimension `d`, and set
`Xₙ = Y ×_S Sₙ`. The criterion proved here is that if, for some `n ≥ 1`, the `d`-th Fitting
ideal of the sheaf of relative differentials `Ω_{Xₙ/Sₙ}` contains `t^{n-1}`, then the generic
fibre of `Y → S` is smooth.

The argument has six steps. Because the special fibre is Cohen–Macaulay and `Y → S` is flat
and locally of finite presentation, the family is Cohen–Macaulay at every point of the special
fibre; the Cohen–Macaulay locus of such a family is open, and an open subset of `Y` containing
the whole special fibre is all of `Y` because properness makes `Y → S` a closed map and the
base is local. So `Y → S` is a Cohen–Macaulay morphism, and therefore every one of its fibres
is a Cohen–Macaulay scheme. The relative dimension of a Cohen–Macaulay morphism is a locally
constant function on the source; it equals `d` on the special fibre, hence — by the same
properness argument — everywhere, so every nonempty fibre is equidimensional of dimension `d`.
That is exactly the hypothesis under which the `d`-th Fitting ideal `I` of `Ω_{Y/S}` cuts out
the non-smooth locus of `Y → S`, and under which forming it commutes with the base change
`Xₙ → Y`. On an affine open `V` of `Y` the base change identifies the sections of the Fitting
ideal on `Xₙ` with the image of `I(V)` modulo `t^n`, so the hypothesis says
`t^{n-1} ∈ I(V) + (t^n)`; localizing at a point of the special fibre, where `t` is not a unit,
the element `1 - tc` becomes invertible and `t^{n-1}` itself lands in `I(V)` up to a unit. A
point of the generic fibre at which the family were not smooth would lie in the closed set cut
out by `I`; the closure of such a point meets the special fibre, again by properness, and at
such a specialization the previous paragraph produces a section of `I(V)` that is a unit at the
original point — which contradicts the vanishing of `I` there. Hence the family is smooth at
every point of the generic fibre, and the generic fibre is smooth over the residue field of the
generic point.

## Main results

* `Deformation.Examples.SmoothingCriterion.isCohenMacaulay_of_isCohenMacaulay_specialFibre`: a
  proper flat family over the spectrum of a local ring with Cohen–Macaulay special fibre is a
  Cohen–Macaulay morphism.
* `Deformation.Examples.SmoothingCriterion.isCohenMacaulay_fibre`: all of its fibres are then
  Cohen–Macaulay schemes.
* `Deformation.Examples.SmoothingCriterion.relativeDimension_of_specialFibre`: if moreover the
  special fibre is equidimensional of dimension `d`, every nonempty fibre is equidimensional of
  dimension `d`.
* `Deformation.Examples.SmoothingCriterion.exists_mem_basicOpen_mul_pow_mem_fittingIdeal`: the
  Fitting-ideal hypothesis on the thickening descends, near the special fibre, to a section of
  the Fitting ideal of `Ω_{Y/S}` divisible by `t^{n-1}` away from a closed set missing the given
  point.
* `Deformation.Examples.SmoothingCriterion.smooth_genericFibre_of_pow_mem_fittingIdeal`:
  the smoothing criterion itself.

## Implementation notes

The `n`-th infinitesimal neighbourhood of the closed point of the formal disc is taken to be
`Spec (k⟦t⟧/(t^n))` rather than `Spec (k[t]/(t^n))`. The two are canonically isomorphic, but
with the power-series presentation the morphism `Sₙ → S` is literally
`Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {PowerSeries.X ^ n})))`, so no
comparison isomorphism has to be interposed between the thickening and the base.

The thickening is not constructed; it enters as an arbitrary cartesian square over
`Sₙ → S`, which is how the base-change statement for Fitting ideals of relative differentials
is phrased. The parameter `t^{n-1}` is regarded as a section of the structure sheaf of `Xₙ`
through the composite `Xₙ → Y → S`, so that the hypothesis never mentions sections of the
structure sheaf of `Sₙ`.

Containment of `t^{n-1}` in the `d`-th Fitting ideal sheaf is expressed as membership of its
restriction in the ideal of sections over every affine open of `Xₙ`, which is how a
quasi-coherent ideal sheaf is given. The intermediate statement near the special fibre is
phrased with `Scheme.basicOpen`, which records that the auxiliary section produced by
localization is invertible at the chosen point, and which transfers along specialization for
free.

The uniformizer is `PowerSeries.X`; the closed point of the formal disc is
`IsLocalRing.closedPoint` and the generic point is the zero ideal, which is prime because the
ring of formal power series over a field is a domain.

## References

* [Stacks Project, Tag 0E7T](https://stacks.math.columbia.edu/tag/0E7T)
* [Stacks Project, Tag 045U](https://stacks.math.columbia.edu/tag/045U)
* [Stacks Project, Tag 02NM](https://stacks.math.columbia.edu/tag/02NM)
* [Stacks Project, Tag 0C3K](https://stacks.math.columbia.edu/tag/0C3K)
* [Stacks Project, Tag 0C3I](https://stacks.math.columbia.edu/tag/0C3I)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Deformation.Examples.SmoothingCriterion

/-- Every open of the source is contained in the inverse image of the whole target. This
records the containment as a term whose type mentions the inverse image, which is what the
section maps `Scheme.Hom.appLE _ ⊤ _` expect. -/
public theorem le_preimage_top {X Y : Scheme.{u}} (f : X ⟶ Y) (U : X.Opens) :
    U ≤ f ⁻¹ᵁ (⊤ : Y.Opens) :=
  le_top.trans (Scheme.Hom.preimage_top f).ge

/-! ### Dividing out the last power of the parameter -/

/-- In a local ring, an element congruent to `t ^ (n - 1)` modulo `t ^ n` differs from it by a
unit multiple, so membership of `t ^ (n - 1)` in `J + (t ^ n)` already forces membership in `J`
as soon as `t` lies in the maximal ideal. -/
private theorem pow_pred_mem_of_mem_sup {A : Type*} [CommRing A] [IsLocalRing A] (t : A)
    (ht : t ∈ IsLocalRing.maximalIdeal A) {n : ℕ} (hn : 1 ≤ n) (J : Ideal A)
    (h : t ^ (n - 1) ∈ J ⊔ Ideal.span {t ^ n}) :
    t ^ (n - 1) ∈ J := by
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp h
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton.mp hb
  have hu : IsUnit (1 - t * c) := by
    have htc : t * c ∈ nonunits A := by
      simpa only [IsLocalRing.mem_maximalIdeal] using
        (IsLocalRing.maximalIdeal A).mul_mem_right c ht
    exact IsLocalRing.isUnit_one_sub_self_of_mem_nonunits (t * c) htc
  have hfactor : t ^ (n - 1) * (1 - t * c) = a := by
    have hn' : n - 1 + 1 = n := Nat.sub_add_cancel hn
    calc t ^ (n - 1) * (1 - t * c) = t ^ (n - 1) - t ^ (n - 1) * (t * c) := by ring
      _ = t ^ (n - 1) - t ^ n * c := by rw [← mul_assoc, ← pow_succ, hn']
      _ = a := by rw [← hab]; ring
  obtain ⟨v, hv⟩ := hu
  have hmul : t ^ (n - 1) * (v : A) ∈ J := by rw [hv, hfactor]; exact ha
  have hx : t ^ (n - 1) = t ^ (n - 1) * (v : A) * ((v⁻¹ : Aˣ) : A) := by
    rw [mul_assoc]; simp
  rw [hx]
  exact J.mul_mem_right _ hmul

/-- The localization of `pow_pred_mem_of_mem_sup` at a prime containing the parameter: if
`x ^ (n - 1)` lies in `J + (x ^ n)` and `x` lies in the prime, then some element outside the
prime multiplies `x ^ (n - 1)` into `J`. -/
private theorem exists_notMem_mul_pow_pred_mem {A : Type*} [CommRing A] (p : PrimeSpectrum A)
    (x : A) (hx : x ∈ p.asIdeal) {n : ℕ} (hn : 1 ≤ n) (J : Ideal A)
    (h : x ^ (n - 1) ∈ J ⊔ Ideal.span {x ^ n}) :
    ∃ s : A, s ∉ p.asIdeal ∧ s * x ^ (n - 1) ∈ J := by
  have hxB : algebraMap A (Localization.AtPrime p.asIdeal) x ∈
      IsLocalRing.maximalIdeal (Localization.AtPrime p.asIdeal) := by
    rw [← Ideal.mem_under,
      IsLocalization.AtPrime.under_maximalIdeal (Localization.AtPrime p.asIdeal) p.asIdeal]
    exact hx
  have hmap : (algebraMap A (Localization.AtPrime p.asIdeal) x) ^ (n - 1) ∈
      (J.map (algebraMap A (Localization.AtPrime p.asIdeal))) ⊔
        Ideal.span {(algebraMap A (Localization.AtPrime p.asIdeal) x) ^ n} := by
    have hm := Ideal.mem_map_of_mem (algebraMap A (Localization.AtPrime p.asIdeal)) h
    rw [Ideal.map_sup, Ideal.map_span] at hm
    simpa only [Set.image_singleton, map_pow] using hm
  have hloc := pow_pred_mem_of_mem_sup
    (A := Localization.AtPrime p.asIdeal) (t := algebraMap A _ x) hxB hn
    (J.map (algebraMap A (Localization.AtPrime p.asIdeal))) hmap
  have hloc' : algebraMap A (Localization.AtPrime p.asIdeal) (x ^ (n - 1)) ∈
      J.map (algebraMap A (Localization.AtPrime p.asIdeal)) := by
    simpa only [map_pow] using hloc
  obtain ⟨s, hs, hsmul⟩ :=
    (IsLocalization.algebraMap_mem_map_algebraMap_iff p.asIdeal.primeCompl
      (Localization.AtPrime p.asIdeal) J (x ^ (n - 1))).mp hloc'
  exact ⟨s, hs, hsmul⟩

/-! ### Properness over a local base -/

/-- A section of the structure sheaf of an affine open lies in the prime of a point of that
open exactly when the section vanishes at the point, i.e. the point is outside the
corresponding basic open. -/
private theorem mem_primeIdealOf_iff_notMem_basicOpen {X : Scheme.{u}} {V : X.Opens}
    (hV : IsAffineOpen V) {x : X} (hx : x ∈ V) (a : Γ(X, V)) :
    a ∈ (hV.primeIdealOf ⟨x, hx⟩).asIdeal ↔ x ∉ X.basicOpen a := by
  have h : hV.primeIdealOf ⟨x, hx⟩ ∈ PrimeSpectrum.basicOpen a ↔ x ∈ X.basicOpen a := by
    rw [← hV.fromSpec_preimage_basicOpen a]
    change hV.fromSpec (hV.primeIdealOf ⟨x, hx⟩) ∈ (X.basicOpen a : Set X) ↔ _
    rw [hV.fromSpec_primeIdealOf ⟨x, hx⟩]
    exact Iff.rfl
  rw [← h, PrimeSpectrum.mem_basicOpen, not_not]

/-- Every point of the source of a universally closed morphism to the spectrum of a local ring
specializes to a point of the fibre over the closed point. -/
private theorem exists_specializes_closedPoint_of_universallyClosed {R : Type u} [CommRing R]
    [IsLocalRing R] {Y : Scheme.{u}} (f : Y ⟶ Spec (.of R)) [UniversallyClosed f] (x : Y) :
    ∃ y, x ⤳ y ∧ f y = IsLocalRing.closedPoint R := by
  let _ : (f x).asIdeal.IsPrime := (f x).isPrime
  obtain ⟨y, hy, hfy⟩ : IsLocalRing.closedPoint R ∈ f '' closure ({x} : Set Y) :=
    (f.isClosedMap _ isClosed_closure).closure_subset_iff.mpr
      (Set.singleton_subset_iff.mpr ⟨x, subset_closure (Set.mem_singleton x), rfl⟩)
      (specializes_iff_mem_closure.mp ((PrimeSpectrum.le_iff_specializes _ _).mp
        (IsLocalRing.le_maximalIdeal_of_isPrime _)))
  exact ⟨y, specializes_iff_mem_closure.mpr hy, hfy⟩

/-- An open subset of the source of a universally closed morphism to the spectrum of a local
ring which contains the whole fibre over the closed point is everything: the image of its
closed complement is closed, so if it were nonempty it would contain the closed point. -/
public theorem mem_of_isOpen_of_specialFibre_subset {R : Type u} [CommRing R] [IsLocalRing R]
    {Y : Scheme.{u}} (f : Y ⟶ Spec (.of R)) [UniversallyClosed f] (U : Set Y) (hopen : IsOpen U)
    (hU : ∀ y : Y, f y = IsLocalRing.closedPoint R → y ∈ U) (x : Y) :
    x ∈ U := by
  obtain ⟨y, hxy, hy⟩ := exists_specializes_closedPoint_of_universallyClosed f x
  exact hxy.mem_open hopen (hU y hy)

/-! ### Cohen–Macaulay morphisms from a Cohen–Macaulay special fibre -/

/-- A flat morphism locally of finite presentation is Cohen–Macaulay at a point whose fibre is
a Cohen–Macaulay scheme. -/
public theorem isCohenMacaulayAt_of_isCohenMacaulay_fiber {X S : Scheme.{u}} (f : X ⟶ S)
    [Flat f] [LocallyOfFinitePresentation f] (x : X)
    (hCM : IsCohenMacaulay (f.fiber (f x))) :
    Scheme.Hom.IsCohenMacaulayAt f
      (fun y => isLocallyNoetherian_fiber_of_locallyOfFinitePresentation f y) x := by
  refine ⟨Flat.stalkMap f x, ?_⟩
  let _ : IsLocallyNoetherian (f.fiber (f x)) :=
    isLocallyNoetherian_fiber_of_locallyOfFinitePresentation f (f x)
  exact isCohenMacaulayLocalRing_stalk (f.fiber (f x)) hCM (f.asFiber x)

/-- **Step one of the smoothing criterion.** A proper flat morphism to the spectrum of a local
ring whose fibre over the closed point is a Cohen–Macaulay scheme is a Cohen–Macaulay
morphism. The Cohen–Macaulay locus is open and contains the special fibre, so properness makes
it everything. -/
public theorem isCohenMacaulay_of_isCohenMacaulay_specialFibre {R : Type u} [CommRing R]
    [IsLocalRing R] {Y : Scheme.{u}} (f : Y ⟶ Spec (.of R)) [UniversallyClosed f] [Flat f]
    [LocallyOfFinitePresentation f]
    (hCM : IsCohenMacaulay (f.fiber (IsLocalRing.closedPoint R))) :
    Scheme.Hom.IsCohenMacaulay f
      (fun y => isLocallyNoetherian_fiber_of_locallyOfFinitePresentation f y) := by
  have hopen : IsOpen {x : Y | Scheme.Hom.IsCohenMacaulayAt f
      (fun y => isLocallyNoetherian_fiber_of_locallyOfFinitePresentation f y) x} :=
    isOpen_setOf_isCohenMacaulayAt f
  intro x
  exact mem_of_isOpen_of_specialFibre_subset f _ hopen
    (fun y hy => isCohenMacaulayAt_of_isCohenMacaulay_fiber f y (by rwa [hy])) x

/-- **Step two of the smoothing criterion.** Every fibre of a proper flat morphism to the
spectrum of a local ring whose special fibre is Cohen–Macaulay is a Cohen–Macaulay scheme. -/
public theorem isCohenMacaulay_fibre {R : Type u} [CommRing R] [IsLocalRing R] {Y : Scheme.{u}}
    (f : Y ⟶ Spec (.of R)) [UniversallyClosed f] [Flat f] [LocallyOfFinitePresentation f]
    (hCM : IsCohenMacaulay (f.fiber (IsLocalRing.closedPoint R)))
    (s : Spec (.of R)) : IsCohenMacaulay (f.fiber s) :=
  ((isCohenMacaulay_iff_flat_and_fibers f _).mp
    (isCohenMacaulay_of_isCohenMacaulay_specialFibre f hCM)).2 s

/-! ### Constant fibre dimension -/

/-- A scheme locally of finite type over a field whose local dimension is the constant `d` is
equidimensional. -/
private theorem equidimensional_of_topologicalKrullDimAt_eq (k : Type u) [Field k]
    (Z : Scheme.{u}) (q : Z ⟶ Spec (.of k)) [LocallyOfFiniteType q] {d : ℕ}
    (hd : ∀ z : Z, topologicalKrullDimAt Z z = (d : WithBot ℕ∞)) :
    TopologicalSpace.Equidimensional Z := by
  intro C hC D hD
  have hcomponent (W : Set Z) (hW : W ∈ irreducibleComponents Z) :
      topologicalKrullDim W = (d : WithBot ℕ∞) := by
    obtain ⟨E, hE, hzE, hEdim⟩ :=
      exists_mem_irreducibleComponents_topologicalKrullDim_eq_topologicalKrullDimAt k Z q
        (genericPoints.ofComponent (⟨W, hW⟩ : irreducibleComponents Z)).1
    have hcl : closure ({(genericPoints.ofComponent (⟨W, hW⟩ : irreducibleComponents Z)).1} :
        Set Z) = W := genericPoints.isGenericPoint_ofComponent ⟨W, hW⟩
    have hWE : W ⊆ E := by
      rw [← hcl]
      exact (isClosed_of_mem_irreducibleComponents E hE).closure_subset_iff.mpr
        (Set.singleton_subset_iff.mpr hzE)
    rw [Set.Subset.antisymm hWE (hW.2 hE.1 hWE), hEdim, hd _]
  exact (hcomponent C hC).trans (hcomponent D hD).symm

/-- The local dimension of the fibre at a point of the source, computed from an
equidimensional fibre of known dimension. -/
private theorem topologicalKrullDimAt_asFiber_eq {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] {d : ℕ} (x : X)
    (he : TopologicalSpace.Equidimensional (f.fiber (f x)))
    (hd : topologicalKrullDim (f.fiber (f x)) = (d : WithBot ℕ∞)) :
    topologicalKrullDimAt (f.fiber (f x)) (f.asFiber x) = (d : WithBot ℕ∞) :=
  topologicalKrullDimAt_eq_of_equidimensional (S.residueField (f x)) (f.fiber (f x))
    (f.fiberToSpecResidueField (f x)) he hd (f.asFiber x)

/-- Transport of a local-dimension computation from a point of the source to the corresponding
point of the fibre. -/
private theorem topologicalKrullDimAt_fiber_of_fiberι {X S : Scheme.{u}} (f : X ⟶ S) (s : S)
    (z : f.fiber s) (x : X) (hx : f.fiberι s z = x) (hfx : f x = s) :
    topologicalKrullDimAt (f.fiber (f x)) (f.asFiber x) =
      topologicalKrullDimAt (f.fiber s) z := by
  subst hfx
  have hz : f.asFiber x = z :=
    (f.fiberι (f x)).isEmbedding.injective (by rw [f.fiberι_asFiber, hx])
  rw [hz]

/-- **Steps three and four of the smoothing criterion.** A proper flat morphism to the spectrum
of a local ring whose special fibre is Cohen–Macaulay and equidimensional of dimension `d` has
relative dimension `d`: every nonempty fibre is equidimensional of dimension `d`. The relative
dimension function of a Cohen–Macaulay morphism is locally constant, so properness propagates
its value on the special fibre to the whole source. -/
public theorem relativeDimension_of_specialFibre {R : Type u} [CommRing R] [IsLocalRing R]
    {Y : Scheme.{u}} (f : Y ⟶ Spec (.of R)) [UniversallyClosed f] [Flat f]
    [LocallyOfFinitePresentation f] (d : ℕ)
    (hCM : IsCohenMacaulay (f.fiber (IsLocalRing.closedPoint R)))
    (hequi : TopologicalSpace.Equidimensional (f.fiber (IsLocalRing.closedPoint R)))
    (hdim : topologicalKrullDim (f.fiber (IsLocalRing.closedPoint R)) = (d : WithBot ℕ∞)) :
    RelativeDimension f d := by
  have hCMall : ∀ s : Spec (.of R), IsCohenMacaulay (f.fiber s) := isCohenMacaulay_fibre f hCM
  have hopen : IsOpen {x : Y | relativeDimensionFunction f hCMall x = d} :=
    (relativeDimensionFunction f hCMall).isLocallyConstant.isOpen_fiber d
  have hspecial : ∀ x : Y, f x = IsLocalRing.closedPoint R →
      x ∈ {x : Y | relativeDimensionFunction f hCMall x = d} := by
    intro x hx
    have h : ((relativeDimensionFunction f hCMall x : ℕ) : WithBot ℕ∞) = (d : WithBot ℕ∞) :=
      (relativeDimensionFunction_apply f hCMall x).symm.trans
        (topologicalKrullDimAt_asFiber_eq f (d := d) x (by rwa [hx]) (by rwa [hx]))
    exact_mod_cast h
  have hall : ∀ x : Y, topologicalKrullDimAt (f.fiber (f x)) (f.asFiber x) =
      (d : WithBot ℕ∞) := by
    intro x
    have hv : relativeDimensionFunction f hCMall x = d :=
      mem_of_isOpen_of_specialFibre_subset f _ hopen hspecial x
    rw [relativeDimensionFunction_apply f hCMall x, hv]
  intro s hs
  have _ : Nonempty (f.fiber s) := hs
  have hlocal : ∀ z : f.fiber s, topologicalKrullDimAt (f.fiber s) z = (d : WithBot ℕ∞) :=
    fun z => (topologicalKrullDimAt_fiber_of_fiberι f s z (f.fiberι s z) rfl
      ((f.range_fiberι s).le ⟨z, rfl⟩)).symm.trans (hall (f.fiberι s z))
  refine ⟨equidimensional_of_topologicalKrullDimAt_eq ((Spec (.of R)).residueField s)
    (f.fiber s) (f.fiberToSpecResidueField s) hlocal, ?_⟩
  rw [TopologicalSpace.topologicalKrullDim_eq_iSup_localKrullDim]
  simp_rw [← TopologicalSpace.topologicalKrullDimAt_eq_localKrullDim, hlocal]
  simp

/-! ### Descending the Fitting-ideal hypothesis along the thickening -/

/-- For a base change `X → Y` of `Y → Spec R` along `Spec (R ⧸ I) → Spec R`, the kernel of the
restriction from an affine open `V` of `Y` to its inverse image in `X` is generated by the image
of `I`. -/
private theorem ker_appLE_eq_map_of_isPullback {R : Type u} [CommRing R] (I : Ideal R)
    {Y : Scheme.{u}} (f : Y ⟶ Spec (.of R)) {X : Scheme.{u}} {pr : X ⟶ Y}
    {g : X ⟶ Spec (.of (R ⧸ I))}
    (hcart : IsPullback pr g f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))))
    (V : Y.affineOpens) :
    RingHom.ker (pr.appLE V.1 (pr ⁻¹ᵁ V.1) le_rfl).hom =
      Ideal.map ((f.appLE ⊤ V.1 (le_preimage_top f V.1)).hom.comp
        (Scheme.ΓSpecIso (.of R)).inv.hom) I := by
  set ψ : Γ(Spec (.of R), ⊤) ⟶ Γ(Spec (.of (R ⧸ I)), ⊤) :=
    (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))).appLE ⊤ ⊤ (le_preimage_top _ ⊤)
    with hψdef
  have hψapp : ψ = (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))).appTop := by
    rw [hψdef]
    exact Scheme.Hom.appLE_eq_app _
  have hψsurj : Function.Surjective ψ.hom := by
    have _ : IsClosedImmersion (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) :=
      IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
    rw [hψapp]
    exact Scheme.Hom.app_surjective _ ⊤ (isAffineOpen_top _)
  have hPO : IsPushout (f.appLE ⊤ V.1 (le_preimage_top f V.1)) ψ
      (pr.appLE V.1 (pr ⁻¹ᵁ V.1) le_rfl) (g.appLE ⊤ (pr ⁻¹ᵁ V.1) (le_preimage_top g _)) := by
    rw [hψdef]
    exact AlgebraicGeometry.isPushout_appLE_of_isPullback (V := ⊤) (U := V.1) (V' := ⊤)
      (U' := pr ⁻¹ᵁ V.1) hcart (isAffineOpen_top _) V.2 (le_preimage_top f V.1)
      (isAffineOpen_top _) (le_preimage_top _ ⊤) (by simp)
  have hkerψ : RingHom.ker (ψ.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom) = I := by
    have h : ψ.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom =
        (Scheme.ΓSpecIso (.of (R ⧸ I))).inv.hom.comp (Ideal.Quotient.mk I) := by
      rw [hψapp]
      simpa only [CommRingCat.hom_comp, CommRingCat.hom_ofHom] using congrArg
        CommRingCat.Hom.hom (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom
          (Ideal.Quotient.mk I))).symm
    rw [h, RingHom.ker_comp_of_injective, Ideal.mk_ker]
    exact (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of (R ⧸ I))).inv).1
  rw [AlgebraicGeometry.GoodDiagramKer.ker_eq_map_of_isPushout_of_surjective ψ.hom
      (f.appLE ⊤ V.1 (le_preimage_top f V.1)).hom (g.appLE ⊤ (pr ⁻¹ᵁ V.1) (le_preimage_top g _)).hom
      (pr.appLE V.1 (pr ⁻¹ᵁ V.1) le_rfl).hom
      (by simpa only [CommRingCat.ofHom_hom] using hPO.flip) hψsurj,
    ← Ideal.map_comap_of_surjective _
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of R)).inv).2 (RingHom.ker ψ.hom),
    RingHom.comap_ker, hkerψ, Ideal.map_map]

/-- A point of an affine open lies in the non-vanishing locus of the pullback of the parameter `t`
of `k⟦t⟧` exactly when `t` is outside the prime of its image in `Spec k⟦t⟧`. -/
private theorem mem_basicOpen_appLE_X_iff (k : Type u) [Field k] {Y : Scheme.{u}}
    (f : Y ⟶ Spec (.of (PowerSeries k))) (V : Y.affineOpens) {y : Y} (hyV : y ∈ V.1) :
    y ∈ Y.basicOpen (f.appLE ⊤ V.1 (le_preimage_top f V.1)
        ((Scheme.ΓSpecIso (.of (PowerSeries k))).inv PowerSeries.X)) ↔
      (PowerSeries.X : PowerSeries k) ∉ (f y).asIdeal := by
  rw [Scheme.basicOpen_appLE, AlgebraicGeometry.basicOpen_eq_of_affine]
  exact ⟨fun h => h.2, fun h => ⟨hyV, h⟩⟩

/-- The parameter `t` of `k⟦t⟧`, pulled back to an affine open, lies in the prime of every point
of that open over the closed point. -/
private theorem appLE_X_mem_primeIdealOf (k : Type u) [Field k] {Y : Scheme.{u}}
    (f : Y ⟶ Spec (.of (PowerSeries k))) (V : Y.affineOpens) {y : Y} (hyV : y ∈ V.1)
    (hy : f y = IsLocalRing.closedPoint (PowerSeries k)) :
    f.appLE ⊤ V.1 (le_preimage_top f V.1)
        ((Scheme.ΓSpecIso (.of (PowerSeries k))).inv PowerSeries.X) ∈
      (V.2.primeIdealOf ⟨y, hyV⟩).asIdeal := by
  rw [mem_primeIdealOf_iff_notMem_basicOpen V.2 hyV, mem_basicOpen_appLE_X_iff k f V hyV, hy,
    not_not]
  exact (PowerSeries.maximalIdeal_eq_span_X (k := k)).ge (Ideal.subset_span rfl)

/-- **Step five of the smoothing criterion.** Suppose the `d`-th Fitting ideal of
`Ω_{Xₙ/Sₙ}` contains `t ^ (n - 1)`, where `Xₙ → Sₙ` is obtained from `Y → S` by the base change
`Sₙ = Spec (k⟦t⟧/(t^n)) → S = Spec k⟦t⟧`. Then near any point of the special fibre the `d`-th
Fitting ideal of `Ω_{Y/S}` contains a multiple of `t ^ (n - 1)` by a section invertible at that
point: on an affine open the base change makes the sections of the Fitting ideal on `Xₙ` the
reduction modulo `t ^ n` of those on `Y`, and `1 - tc` is invertible at a point where `t`
vanishes. -/
public theorem exists_mem_basicOpen_mul_pow_mem_fittingIdeal (k : Type u) [Field k]
    {Y : Scheme.{u}} (f : Y ⟶ Spec (.of (PowerSeries k))) [LocallyOfFiniteType f]
    (d n : ℕ) (hn : 1 ≤ n) {Xₙ : Scheme.{u}} {pr : Xₙ ⟶ Y}
    {gₙ : Xₙ ⟶ Spec (.of (PowerSeries k ⧸ Ideal.span
      {(PowerSeries.X : PowerSeries k) ^ n}))}
    (hcart : IsPullback pr gₙ f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk
      (Ideal.span {(PowerSeries.X : PowerSeries k) ^ n})))))
    (hfit : ∀ U : Xₙ.affineOpens,
      (pr ≫ f).appLE ⊤ U.1 (le_preimage_top (pr ≫ f) U.1)
          ((Scheme.ΓSpecIso (.of (PowerSeries k))).inv (PowerSeries.X ^ (n - 1))) ∈
        (fittingIdeal (Scheme.Hom.relativeDifferentials gₙ) (d : ℤ)).ideal U)
    (V : Y.affineOpens) {y : Y} (hyV : y ∈ V.1)
    (hy : f y = IsLocalRing.closedPoint (PowerSeries k)) :
    ∃ s : Γ(Y, V.1), y ∈ Y.basicOpen s ∧
      s * (f.appLE ⊤ V.1 (le_preimage_top f V.1)
            ((Scheme.ΓSpecIso (.of (PowerSeries k))).inv PowerSeries.X)) ^ (n - 1) ∈
        (fittingIdeal (Scheme.Hom.relativeDifferentials f) (d : ℤ)).ideal V := by
  have _ : IsClosedImmersion pr :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback hcart.flip
      (IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective)
  set U : Xₙ.affineOpens := ⟨pr ⁻¹ᵁ V.1, V.2.preimage pr⟩ with hUdef
  have hVU : (U.1 : Xₙ.Opens) ≤ pr ⁻¹ᵁ (V.1 : Y.Opens) := le_rfl
  set ε : CommRingCat.of (PowerSeries k) ⟶ Γ(Spec (.of (PowerSeries k)), ⊤) :=
    (Scheme.ΓSpecIso (.of (PowerSeries k))).inv with hεdef
  set φ : Γ(Spec (.of (PowerSeries k)), ⊤) ⟶ Γ(Y, V.1) :=
    f.appLE ⊤ V.1 (le_preimage_top f V.1) with hφdef
  set α : Γ(Y, V.1) ⟶ Γ(Xₙ, U.1) := pr.appLE V.1 U.1 hVU with hαdef
  set tV : Γ(Y, V.1) := φ (ε PowerSeries.X) with htVdef
  have hcomp : ∀ e : (U.1 : Xₙ.Opens) ≤ (pr ≫ f) ⁻¹ᵁ (⊤ : (Spec
      (.of (PowerSeries k))).Opens), (pr ≫ f).appLE ⊤ U.1 e = φ ≫ α := fun _ => by
    rw [hφdef, hαdef]
    exact (Scheme.Hom.appLE_comp_appLE pr f ⊤ V.1 U.1 (le_preimage_top f V.1) hVU).symm
  have hfitU := hfit U
  rw [← fittingIdeal_relativeDifferentials_comap pr gₙ f _ hcart (d : ℤ),
    Stacks.IdealSheaf.ideal_comap_appLE _ pr V U hVU, hcomp, CommRingCat.comp_apply] at hfitU
  have hαsurj : Function.Surjective α.hom := by
    rw [hαdef, show pr.appLE V.1 U.1 hVU = pr.app V.1 from Scheme.Hom.appLE_eq_app pr]
    exact pr.app_surjective V.1 V.2
  have hkerα : RingHom.ker α.hom = Ideal.map (φ.hom.comp ε.hom)
      (Ideal.span {(PowerSeries.X : PowerSeries k) ^ n}) :=
    ker_appLE_eq_map_of_isPullback _ f hcart V
  have hkerspan : RingHom.ker α.hom = Ideal.span {tV ^ n} := by
    rw [hkerα, Ideal.map_span]
    simp only [Set.image_singleton, RingHom.coe_comp, Function.comp_apply]
    congr 1
    simp [htVdef, map_pow]
  obtain ⟨a₀, ha₀, ha₀eq⟩ := (Ideal.mem_map_iff_of_surjective α.hom hαsurj).mp hfitU
  have hpow : φ (ε (PowerSeries.X ^ (n - 1))) = tV ^ (n - 1) := by
    simp [htVdef, map_pow]
  have hsub : tV ^ (n - 1) - a₀ ∈ RingHom.ker α.hom := by
    rw [RingHom.mem_ker, map_sub, ← hpow]
    exact sub_eq_zero.mpr ha₀eq.symm
  have hrel : tV ^ (n - 1) ∈
      (fittingIdeal (Scheme.Hom.relativeDifferentials f) (d : ℤ)).ideal V ⊔
        Ideal.span {tV ^ n} :=
    Submodule.mem_sup.mpr ⟨a₀, ha₀, tV ^ (n - 1) - a₀, hkerspan ▸ hsub, by ring⟩
  obtain ⟨s, hs, hsmem⟩ := exists_notMem_mul_pow_pred_mem (V.2.primeIdealOf ⟨y, hyV⟩) tV
    (appLE_X_mem_primeIdealOf k f V hyV hy) hn _ hrel
  refine ⟨s, ?_, hsmem⟩
  by_contra hcon
  exact hs ((mem_primeIdealOf_iff_notMem_basicOpen V.2 hyV s).mpr hcon)

/-! ### The smoothing criterion -/

/-- Transport of smoothness of the fibre from a point of the source to the corresponding point
of the fibre. -/
private theorem smoothAt_fiberToSpecResidueField_of_fiberι {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFinitePresentation f] (s : S) (z : f.fiber s) (x : X)
    (hx : f.fiberι s z = x) (hfx : f x = s)
    (h : InfinitesimalLifting.SmoothAt (f.fiberToSpecResidueField (f x)) (f.asFiber x)) :
    InfinitesimalLifting.SmoothAt (f.fiberToSpecResidueField s) z := by
  subst hfx
  have hz : f.asFiber x = z :=
    (f.fiberι (f x)).isEmbedding.injective (by rw [f.fiberι_asFiber, hx])
  rwa [hz] at h

/-- Under the Fitting-ideal hypothesis of the smoothing criterion, a flat universally closed
morphism of relative dimension `d` to `Spec k⟦t⟧` is smooth at every point of the generic fibre:
the closure of a non-smooth point would meet the special fibre, where the Fitting ideal contains
a section invertible at the original point. -/
private theorem smoothAt_of_pow_mem_fittingIdeal (k : Type u) [Field k]
    {Y : Scheme.{u}} (f : Y ⟶ Spec (.of (PowerSeries k))) [UniversallyClosed f] [Flat f]
    [LocallyOfFinitePresentation f] (d n : ℕ) (hn : 1 ≤ n) (hRD : RelativeDimension f d)
    {Xₙ : Scheme.{u}} {pr : Xₙ ⟶ Y}
    {gₙ : Xₙ ⟶ Spec (.of (PowerSeries k ⧸ Ideal.span
      {(PowerSeries.X : PowerSeries k) ^ n}))}
    (hcart : IsPullback pr gₙ f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk
      (Ideal.span {(PowerSeries.X : PowerSeries k) ^ n})))))
    (hfit : ∀ U : Xₙ.affineOpens,
      (pr ≫ f).appLE ⊤ U.1 (le_preimage_top (pr ≫ f) U.1)
          ((Scheme.ΓSpecIso (.of (PowerSeries k))).inv (PowerSeries.X ^ (n - 1))) ∈
        (fittingIdeal (Scheme.Hom.relativeDifferentials gₙ) (d : ℤ)).ideal U)
    (x : Y) (hfx : f x = (⟨⊥, inferInstance⟩ : PrimeSpectrum (PowerSeries k))) :
    InfinitesimalLifting.SmoothAt f x := by
  set I : Y.IdealSheafData := fittingIdeal (Scheme.Hom.relativeDifferentials f) (d : ℤ)
  by_contra hns
  have hxs : x ∈ Set.range I.subschemeι :=
    (mem_fittingIdeal_relativeDifferentials_iff_not_smoothAt f d hRD x).mpr hns
  obtain ⟨y, hxy, hyf⟩ := exists_specializes_closedPoint_of_universallyClosed f x
  obtain ⟨-, ⟨V₀, hV₀, rfl⟩, hyV, -⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ y) isOpen_univ
  have hxV : x ∈ V₀ := hxy.mem_open V₀.isOpen hyV
  obtain ⟨s, hsy, hsmem⟩ := exists_mem_basicOpen_mul_pow_mem_fittingIdeal k f d n hn
    hcart hfit ⟨V₀, hV₀⟩ hyV hyf
  have hxsupp : x ∈ (I.support : Set Y) := I.range_subschemeι ▸ hxs
  have hxzero : x ∈ Y.zeroLocus (U := V₀) (I.ideal ⟨V₀, hV₀⟩) :=
    (Scheme.IdealSheafData.mem_support_iff_of_mem (U := ⟨V₀, hV₀⟩) hxV).mp hxsupp
  have hxnot := (Y.mem_zeroLocus_iff _ x).mp hxzero _ hsmem
  have hxt := (mem_basicOpen_appLE_X_iff k f ⟨V₀, hV₀⟩ hxV).mpr (by
    rw [hfx]
    exact fun hcon => PowerSeries.X_ne_zero (R := k) (Ideal.mem_bot.mp hcon))
  refine hxnot ?_
  have hprod : x ∈ Y.basicOpen s ⊓ Y.basicOpen ((f.appLE ⊤ V₀ (le_preimage_top f V₀)
      ((Scheme.ΓSpecIso (.of (PowerSeries k))).inv PowerSeries.X)) ^ (n - 1)) := by
    refine ⟨hxy.mem_open (Y.basicOpen s).isOpen hsy, (Scheme.mem_basicOpen _ _ x hxV).mpr ?_⟩
    rw [map_pow]
    exact ((Scheme.mem_basicOpen _ _ x hxV).mp hxt).pow _
  rwa [← Scheme.basicOpen_mul] at hprod

/-- Let `k` be a field, `S = Spec k⟦t⟧` and `Sₙ = Spec (k⟦t⟧/(t^n))`. Let `f : Y ⟶ S` be
proper and flat with Cohen–Macaulay special fibre, equidimensional of dimension `d`, and let
`Xₙ = Y ×_S Sₙ` with projections `pr` and `gₙ`. If for some `n ≥ 1` the `d`-th Fitting ideal of
`Ω_{Xₙ/Sₙ}` contains `t ^ (n - 1)`, then the generic fibre of `f`, taken over the residue field
of the generic point of `S`, is smooth. -/
@[stacks 0E7T]
public theorem smooth_genericFibre_of_pow_mem_fittingIdeal (k : Type u) [Field k]
    {Y : Scheme.{u}} (f : Y ⟶ Spec (.of (PowerSeries k))) [IsProper f] [Flat f]
    (d n : ℕ) (hn : 1 ≤ n)
    (hCM : IsCohenMacaulay (f.fiber (IsLocalRing.closedPoint (PowerSeries k))))
    (hequi : TopologicalSpace.Equidimensional
      (f.fiber (IsLocalRing.closedPoint (PowerSeries k))))
    (hdim : topologicalKrullDim (f.fiber (IsLocalRing.closedPoint (PowerSeries k))) =
      (d : WithBot ℕ∞))
    {Xₙ : Scheme.{u}} {pr : Xₙ ⟶ Y}
    {gₙ : Xₙ ⟶ Spec (.of (PowerSeries k ⧸ Ideal.span
      {(PowerSeries.X : PowerSeries k) ^ n}))}
    (hcart : IsPullback pr gₙ f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk
      (Ideal.span {(PowerSeries.X : PowerSeries k) ^ n})))))
    (hfit : ∀ U : Xₙ.affineOpens,
      (pr ≫ f).appLE ⊤ U.1 (le_preimage_top (pr ≫ f) U.1)
          ((Scheme.ΓSpecIso (.of (PowerSeries k))).inv (PowerSeries.X ^ (n - 1))) ∈
        (fittingIdeal (Scheme.Hom.relativeDifferentials gₙ) (d : ℤ)).ideal U) :
    Smooth (f.fiberToSpecResidueField
      (⟨⊥, inferInstance⟩ : PrimeSpectrum (PowerSeries k))) := by
  set η : PrimeSpectrum (PowerSeries k) := ⟨⊥, inferInstance⟩
  have hRD : RelativeDimension f d := relativeDimension_of_specialFibre f d hCM hequi hdim
  refine InfinitesimalLifting.smooth_of_forall_smoothAt _ fun z => ?_
  have hfz : f (f.fiberι η z) = η := (f.range_fiberι η).le ⟨z, rfl⟩
  exact smoothAt_fiberToSpecResidueField_of_fiberι f η z _ rfl hfz
    (((Stacks.Tag01V9NumericalCriterion.smoothAt_tfae f (f.fiberι η z)).out 1 2 rfl rfl).mp
      (smoothAt_of_pow_mem_fittingIdeal k f d n hn hRD hcart hfit _ hfz)).2

end Deformation.Examples.SmoothingCriterion

end
