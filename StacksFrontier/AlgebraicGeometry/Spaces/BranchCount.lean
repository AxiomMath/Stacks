module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.EtaleNeighbourhood.SmoothBranches
public import StacksFrontier.AlgebraicGeometry.Spaces.GermPropertyAtPoint
public import StacksFrontier.AlgebraicGeometry.Spaces.LocalRingDimension
public import StacksFrontier.AlgebraicGeometry.Spaces.UnibranchCriteria

/-!
# Branch counts at a point of an algebraic space

Let `x` be a point of an algebraic space `F` over `S`. Five numbers attached to `x` agree: the
largest number of minimal primes of the local ring of an étale scheme chart of `F` at a point
above `x`, the largest number of irreducible components of such a chart through such a point,
the largest number of branches there, the number of geometric branches there — which is the
same on every chart — and the number of minimal primes of the étale local ring of `F` at a
geometric point above `x`, which is again the same at every geometric point.

The first three conditions say that the count is bounded by `n` and attained, because the local
quantity they bound genuinely varies from chart to chart; the last two say that the count equals
`n` at every chart point, respectively at every geometric point, because those quantities do not
vary.

## Main definitions

* `AlgebraicGeometry.Space.HasMinimalPrimeCount`, `AlgebraicGeometry.Space.HasComponentCount`
  and `AlgebraicGeometry.Space.HasBranchCount` are conditions (1), (2) and (3).
* `AlgebraicGeometry.Space.HasGeometricBranchCount` and
  `AlgebraicGeometry.Space.HasEtaleLocalRingMinimalPrimeCount` are conditions (4) and (5).

## Main results

* `AlgebraicGeometry.Space.minimalPrimeCount_iff_componentCount`,
  `AlgebraicGeometry.Space.componentCount_iff_branchCount`,
  `AlgebraicGeometry.Space.branchCount_iff_geometricBranchCount` and
  `AlgebraicGeometry.Space.geometricBranchCount_iff_etaleLocalRingMinimalPrimeCount`: the four
  equivalences of consecutive conditions.
* `AlgebraicGeometry.GermOfScheme.isEtaleLocal_numberOfGeometricBranches_eq`: having a
  prescribed number of geometric branches is an étale-local property of germs of schemes.
* `AlgebraicGeometry.encard_irreducibleComponentsThrough_le_numberOfBranches` and
  `AlgebraicGeometry.numberOfBranches_le_numberOfGeometricBranches`: the three scheme-level
  counts at a point are increasing.
* `encard_minimalPrimes_eq_numberOfGeometricBranchesOfLocalRing`: the number of geometric
  branches of a local ring may be computed from any strict henselization of it.

## Implementation notes

A point above `x` on an étale scheme chart `a : yoneda.obj U ⟶ F` is recorded by
`AlgebraicGeometry.Space.ChartPoint`, as for the dimension of the local ring in Tag 04NA: the
source's quantifiers over schemes étale over `F` and over their points above `x` become
quantifiers over the étale charts of the chosen big fppf site and over the points of the
representing scheme that a field-valued point above `x` selects.

All five counts take values in `ℕ∞`, so a chart whose local ring at a point above `x` has
infinitely many minimal primes does not accidentally satisfy a condition for a natural
number `n`.

Conditions (1) and (2) agree chart by chart, by the correspondence of Tag 00ET between the
irreducible components through a point and the minimal primes of the local ring there.
Conditions (2) and (3) agree because the number of branches of a scheme at a point is the
supremum, over its elementary étale neighbourhoods, of the number of irreducible components
through the distinguished point (Tag 0CB4), and because every étale neighbourhood of a point of
a chart is refined by an open subscheme of a smaller chart. Conditions (3) and (4) agree
because the number of geometric branches is that same supremum taken over all étale
neighbourhoods, and because having a prescribed number of geometric branches is an étale-local
property of germs (Tag 0DQ2), hence takes the same value on every chart above `x` (Tag 04N2).
Conditions (4) and (5) agree through Tag 04KF: the étale local ring at a geometric point is a
strict henselization of the local ring of a chart at the point the geometric point selects.

Although the source states the equivalences for a positive `n`, they also hold for `n = 0`: a
chart above a point always exists, and the local ring of a scheme at a point always has a
minimal prime.

## References

* [Stacks Project, Tag 0DQ3](https://stacks.math.columbia.edu/tag/0DQ3)
-/

@[expose] public noncomputable section

open CategoryTheory IsLocalRing

universe u v w

/-! ### The geometric branch count of a local ring from an arbitrary strict henselization -/

/-- A ring isomorphism matches up minimal primes, so the two rings have the same number of
them. -/
private theorem encard_minimalPrimes_ringEquiv {R : Type v} {T : Type w} [CommRing R]
    [CommRing T] (e : R ≃+* T) :
    Set.encard (minimalPrimes R) = Set.encard (minimalPrimes T) :=
  (Set.encard_congr (bijOn_minimalPrimes_ringEquiv e).equiv).symm

/-- The number of geometric branches of a local ring is the number of minimal primes of *any*
strict henselization of it, not only of the chosen one: two strict henselizations are
isomorphic as algebras over the ring, both being ind-étale henselian local algebras with
separably closed residue field. -/
theorem encard_minimalPrimes_eq_numberOfGeometricBranchesOfLocalRing (R : Type u) [CommRing R]
    [IsLocalRing R] (L : Type u) [Field L] [Algebra (ResidueField R) L]
    [IsSepClosure (ResidueField R) L] (A : Type u) [CommRing A] [IsLocalRing A] [Algebra R A]
    [IsHenselization R L A] :
    Set.encard (minimalPrimes A) = numberOfGeometricBranchesOfLocalRing R := by
  let D := (strictHenselizationData R).carrier
  let : HenselianLocalRing A := IsHenselization.henselian (R := R) (L := L) (Rh := A)
  let : HenselianLocalRing D := (strictHenselizationDataIsHenselization R).henselian
  obtain ⟨eA, heA⟩ := IsHenselization.exists_residueFieldEquiv (R := R) (L := L) (Rh := A)
  obtain ⟨eD, heD⟩ := (strictHenselizationDataIsHenselization R).exists_residueFieldEquiv
  let eL := IsSepClosure.equiv (ResidueField R) L (SeparableClosure (ResidueField R))
  let : Algebra R L := ((algebraMap (ResidueField R) L).comp (residue R)).toAlgebra
  let pA : A →ₐ[R] L :=
    { toRingHom := eA.symm.toRingHom.comp (residue A)
      commutes' := fun r ↦ by
        show eA.symm (residue A (algebraMap R A r)) =
          algebraMap (ResidueField R) L (residue R r)
        rw [← heA, RingEquiv.symm_apply_apply] }
  let pD : D →ₐ[R] L :=
    { toRingHom := eL.symm.toRingHom.comp (eD.symm.toRingHom.comp (residue D))
      commutes' := fun r ↦ by
        show eL.symm (eD.symm (residue D (algebraMap R D r))) =
          algebraMap (ResidueField R) L (residue R r)
        rw [← heD, RingEquiv.symm_apply_apply, AlgEquiv.commutes] }
  obtain ⟨e, -⟩ := HenselianLocalRing.existsUnique_algEquiv_of_ind_etale
    (IsHenselization.ind_etale_of_universe_le (R := R) (L := L) (Rh := A))
    (IsHenselization.ind_etale_of_universe_le
      (R := R) (L := SeparableClosure (ResidueField R)) (Rh := D))
    pA pD (eA.symm.surjective.comp residue_surjective)
    (eL.symm.surjective.comp (eD.symm.surjective.comp residue_surjective))
  exact encard_minimalPrimes_ringEquiv e.toRingEquiv

namespace AlgebraicGeometry

/-! ### The three counts attached to a point of a scheme -/

/-- Having a prescribed number of geometric branches is an étale-local property of germs of
schemes: a smooth, in particular an étale, morphism of schemes preserves the number of
geometric branches at a point, which is Tag 0DQ2. -/
theorem GermOfScheme.isEtaleLocal_numberOfGeometricBranches_eq (n : ℕ∞) :
    GermOfScheme.IsEtaleLocal fun X : GermOfScheme.{u} ↦
      numberOfGeometricBranches X.scheme X.point = n := by
  intro X Y f hf
  obtain ⟨g, -, hg⟩ := hf
  have : Etale g.hom := hg
  have h := (numberOfGeometricBranches_eq_of_smooth (Scheme.Opens.ι g.source)
      ⟨X.point, g.mem_source⟩).symm.trans
    (numberOfGeometricBranches_eq_of_smooth g.hom ⟨X.point, g.mem_source⟩)
  rw [show Scheme.Opens.ι g.source ⟨X.point, g.mem_source⟩ = X.point from rfl, g.map_point] at h
  show (numberOfGeometricBranches Y.scheme Y.point = n) ↔
    (numberOfGeometricBranches X.scheme X.point = n)
  rw [h]

/-- The number of irreducible components of a scheme through a point is at most its number of
branches there: the scheme itself, with the identity structure morphism, is an elementary étale
neighbourhood of the point, and the number of branches is the supremum of the component counts
of all of them. -/
theorem encard_irreducibleComponentsThrough_le_numberOfBranches (X : Scheme.{u}) (x : X) :
    Set.encard {Z ∈ irreducibleComponents X | x ∈ Z} ≤ numberOfBranches X x := by
  rw [numberOfBranches_eq_iSup_encard_irreducibleComponentsThrough]
  exact le_iSup_of_le (EtaleNeighborhood.self X x)
    (le_iSup_of_le (EtaleNeighborhood.isElementary_self X x) le_rfl)

/-- The number of branches of a scheme at a point is at most its number of geometric branches
there: both are suprema of the number of irreducible components through the distinguished point
of an étale neighbourhood, and the branch count restricts that supremum to the elementary
neighbourhoods. -/
theorem numberOfBranches_le_numberOfGeometricBranches (X : Scheme.{u}) (x : X) :
    numberOfBranches X x ≤ numberOfGeometricBranches X x := by
  rw [numberOfBranches_eq_iSup_encard_irreducibleComponentsThrough,
    numberOfGeometricBranches_eq_iSup_encard]
  exact iSup_le fun U ↦ iSup_le fun _ ↦ le_iSup_of_le U le_rfl

/-- The irreducible components of a scheme through a point correspond to the minimal primes of
its local ring there: on an affine open around the point this is the correspondence of Tag 00ET
between the irreducible components through a prime and the minimal primes of the
localization. -/
theorem encard_irreducibleComponentsThrough_eq_minimalPrimes_stalk (X : Scheme.{u}) (x : X) :
    Set.encard {Z ∈ irreducibleComponents X | x ∈ Z} =
      Set.encard (minimalPrimes (X.presheaf.stalk x)) := by
  classical
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  have : IsOpenImmersion hU.fromSpec := hU.isOpenImmersion_fromSpec
  let p : PrimeSpectrum Γ(X, U) := hU.primeIdealOf ⟨x, hxU⟩
  have hp : hU.fromSpec p = x := hU.fromSpec_primeIdealOf ⟨x, hxU⟩
  let : p.asIdeal.IsPrime := p.isPrime
  let : Algebra Γ(X, U) (X.presheaf.stalk x) := (X.presheaf.germ U x hxU).hom.toAlgebra
  let : IsLocalization.AtPrime (X.presheaf.stalk x) p.asIdeal :=
    hU.isLocalization_stalk ⟨x, hxU⟩
  refine Set.encard_congr ((Equiv.subtypeEquivRight fun C ↦ ?_).trans
    ((Space.componentsThroughEquivOfIsOpenEmbedding hU.fromSpec.isOpenEmbedding p).symm.trans
      (PrimeSpectrum.irreducibleComponentsThroughEquiv Γ(X, U) p.asIdeal
        (X.presheaf.stalk x))))
  simp only [Set.mem_ofPred_eq, hp]

namespace Space

/-! ### The five conditions -/

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- **Stacks 0DQ3, condition (1).** The local ring of an étale scheme chart of `F` at a point
above `x` has at most `n` minimal primes, and at some such point it has exactly `n`. -/
def HasMinimalPrimeCount (x : points B S hS F) (n : ℕ) : Prop :=
  (∀ (U : BigFppfOver B S hS) (a : yoneda.obj U ⟶ F)
      (u : (BigFppfOver.toScheme B S hS).obj U),
      IsEtale B S hS a → ChartPoint B S hS U a u x →
      Set.encard (minimalPrimes (((BigFppfOver.toScheme B S hS).obj U).presheaf.stalk u)) ≤
        (n : ℕ∞)) ∧
    ∃ (U : BigFppfOver B S hS) (a : yoneda.obj U ⟶ F)
      (u : (BigFppfOver.toScheme B S hS).obj U),
      IsEtale B S hS a ∧ ChartPoint B S hS U a u x ∧
      Set.encard (minimalPrimes (((BigFppfOver.toScheme B S hS).obj U).presheaf.stalk u)) =
        (n : ℕ∞)

/-- **Stacks 0DQ3, condition (2).** At most `n` irreducible components of an étale scheme chart
of `F` pass through a point above `x`, and through some such point exactly `n` pass. -/
def HasComponentCount (x : points B S hS F) (n : ℕ) : Prop :=
  (∀ (U : BigFppfOver B S hS) (a : yoneda.obj U ⟶ F)
      (u : (BigFppfOver.toScheme B S hS).obj U),
      IsEtale B S hS a → ChartPoint B S hS U a u x →
      Set.encard {Z ∈ irreducibleComponents ((BigFppfOver.toScheme B S hS).obj U) | u ∈ Z} ≤
        (n : ℕ∞)) ∧
    ∃ (U : BigFppfOver B S hS) (a : yoneda.obj U ⟶ F)
      (u : (BigFppfOver.toScheme B S hS).obj U),
      IsEtale B S hS a ∧ ChartPoint B S hS U a u x ∧
      Set.encard {Z ∈ irreducibleComponents ((BigFppfOver.toScheme B S hS).obj U) | u ∈ Z} =
        (n : ℕ∞)

/-- **Stacks 0DQ3, condition (3).** An étale scheme chart of `F` has at most `n` branches at a
point above `x`, and at some such point it has exactly `n`. -/
def HasBranchCount (x : points B S hS F) (n : ℕ) : Prop :=
  (∀ (U : BigFppfOver B S hS) (a : yoneda.obj U ⟶ F)
      (u : (BigFppfOver.toScheme B S hS).obj U),
      IsEtale B S hS a → ChartPoint B S hS U a u x →
      numberOfBranches ((BigFppfOver.toScheme B S hS).obj U) u ≤ (n : ℕ∞)) ∧
    ∃ (U : BigFppfOver B S hS) (a : yoneda.obj U ⟶ F)
      (u : (BigFppfOver.toScheme B S hS).obj U),
      IsEtale B S hS a ∧ ChartPoint B S hS U a u x ∧
      numberOfBranches ((BigFppfOver.toScheme B S hS).obj U) u = (n : ℕ∞)

/-- **Stacks 0DQ3, condition (4).** Every étale scheme chart of `F` has exactly `n` geometric
branches at every point above `x`. -/
def HasGeometricBranchCount (x : points B S hS F) (n : ℕ) : Prop :=
  ∀ (U : BigFppfOver B S hS) (a : yoneda.obj U ⟶ F)
      (u : (BigFppfOver.toScheme B S hS).obj U),
    IsEtale B S hS a → ChartPoint B S hS U a u x →
    numberOfGeometricBranches ((BigFppfOver.toScheme B S hS).obj U) u = (n : ℕ∞)

/-- **Stacks 0DQ3, condition (5).** The étale local ring of `F` at every geometric point above
`x` has exactly `n` minimal primes. -/
def HasEtaleLocalRingMinimalPrimeCount (x : points B S hS F) (n : ℕ) : Prop :=
  ∀ p : GeometricPoint B S hS F, GeometricPoint.LiesOver p x →
    Set.encard (minimalPrimes (etaleLocalRing B S hS F p)) = (n : ℕ∞)

/-! ### Conditions (1) and (2) -/

/-- **Stacks 0DQ3, conditions (1) and (2).** A point of a presheaf on the big fppf site has
minimal-prime count `n` on its étale scheme charts exactly when it has irreducible-component
count `n` on them: the two counts agree at each chart point separately. -/
@[stacks 0DQ3 "conditions (1) and (2)"]
theorem minimalPrimeCount_iff_componentCount (x : points B S hS F) (n : ℕ) :
    HasMinimalPrimeCount B S hS x n ↔ HasComponentCount B S hS x n := by
  simp only [HasMinimalPrimeCount, HasComponentCount,
    encard_irreducibleComponentsThrough_eq_minimalPrimes_stalk]

/-! ### Refining an étale neighbourhood of a chart point by a chart -/

/-- An étale neighbourhood of a point of an étale scheme chart of `F` above `x` has the same
number of irreducible components through its distinguished point as some étale scheme chart of
`F` has through some point above `x`: the neighbourhood is refined by an open subscheme of a
smaller chart, and an open immersion matches the irreducible components through corresponding
points. -/
private theorem exists_chartPoint_encard_irreducibleComponentsThrough_eq
    (x : points B S hS F) (U : BigFppfOver B S hS) (a : yoneda.obj U ⟶ F)
    (ha : IsEtale B S hS a) (p : FieldValuedPoint B S hS (yoneda.obj U))
    (hp : pointsMap B S hS (yoneda.obj U) a (p.class B S hS (yoneda.obj U)) = x)
    (N : _root_.AlgebraicGeometry.EtaleNeighborhood
      ((BigFppfOver.toScheme B S hS).obj U) (schemePoint B S hS U p)) :
    ∃ (V : BigFppfOver B S hS) (b : yoneda.obj V ⟶ F)
      (v : (BigFppfOver.toScheme B S hS).obj V),
      IsEtale B S hS b ∧ ChartPoint B S hS V b v x ∧
      Set.encard {Z ∈ irreducibleComponents N.scheme | N.point ∈ Z} =
        Set.encard
          {Z ∈ irreducibleComponents ((BigFppfOver.toScheme B S hS).obj V) | v ∈ Z} := by
  obtain ⟨V, q, j, hj, hjq, hclass⟩ :=
    exists_smallEtale_refinement_of_etaleNeighborhood B S hS F
      ⟨CostructuredArrow.mk a, (isEtale_iff_presheaf_of_yoneda B S hS a).mp ha⟩ p N
  have : _root_.AlgebraicGeometry.IsOpenImmersion j := hj
  have hcomp := Set.encard_congr (componentsThroughEquivOfIsOpenEmbedding j.isOpenEmbedding
    (schemePoint B S hS V.1.left q))
  rw [hjq] at hcomp
  exact ⟨V.1.left, V.1.hom, schemePoint B S hS V.1.left q,
    (isEtale_iff_presheaf_of_yoneda B S hS V.1.hom).mpr V.2, ⟨q, rfl, hclass.trans hp⟩,
    hcomp.symm⟩

/-! ### Conditions (2) and (3) -/

/-- A bound on the number of irreducible components through every chart point above `x` bounds
the number of branches of every chart at every point above `x`: that number is the supremum of
the component counts of the elementary étale neighbourhoods of the point, and each of those is
refined by a chart above `x`. -/
private theorem numberOfBranches_le_of_forall_chartPoint (x : points B S hS F) (n : ℕ)
    (hall : ∀ (V : BigFppfOver B S hS) (b : yoneda.obj V ⟶ F)
      (v : (BigFppfOver.toScheme B S hS).obj V), IsEtale B S hS b →
      ChartPoint B S hS V b v x →
      Set.encard {Z ∈ irreducibleComponents ((BigFppfOver.toScheme B S hS).obj V) | v ∈ Z} ≤
        (n : ℕ∞))
    (U : BigFppfOver B S hS) (a : yoneda.obj U ⟶ F)
    (u : (BigFppfOver.toScheme B S hS).obj U) (ha : IsEtale B S hS a)
    (hu : ChartPoint B S hS U a u x) :
    numberOfBranches ((BigFppfOver.toScheme B S hS).obj U) u ≤ (n : ℕ∞) := by
  obtain ⟨p, rfl, hp⟩ := hu
  rw [numberOfBranches_eq_iSup_encard_irreducibleComponentsThrough]
  refine iSup_le fun N ↦ iSup_le fun _ ↦ ?_
  obtain ⟨V, b, v, hb, hv, heq⟩ :=
    exists_chartPoint_encard_irreducibleComponentsThrough_eq B S hS x U a ha p hp N
  exact heq.trans_le (hall V b v hb hv)

/-- The same bound for the number of geometric branches, which is the supremum of the component
counts over *all* étale neighbourhoods of the point. -/
private theorem numberOfGeometricBranches_le_of_forall_chartPoint (x : points B S hS F) (n : ℕ)
    (hall : ∀ (V : BigFppfOver B S hS) (b : yoneda.obj V ⟶ F)
      (v : (BigFppfOver.toScheme B S hS).obj V), IsEtale B S hS b →
      ChartPoint B S hS V b v x →
      Set.encard {Z ∈ irreducibleComponents ((BigFppfOver.toScheme B S hS).obj V) | v ∈ Z} ≤
        (n : ℕ∞))
    (U : BigFppfOver B S hS) (a : yoneda.obj U ⟶ F)
    (u : (BigFppfOver.toScheme B S hS).obj U) (ha : IsEtale B S hS a)
    (hu : ChartPoint B S hS U a u x) :
    numberOfGeometricBranches ((BigFppfOver.toScheme B S hS).obj U) u ≤ (n : ℕ∞) := by
  obtain ⟨p, rfl, hp⟩ := hu
  rw [numberOfGeometricBranches_eq_iSup_encard]
  refine iSup_le fun N ↦ ?_
  obtain ⟨V, b, v, hb, hv, heq⟩ :=
    exists_chartPoint_encard_irreducibleComponentsThrough_eq B S hS x U a ha p hp N
  exact heq.trans_le (hall V b v hb hv)

/-- A chart whose branch count at a point above `x` is the natural number `n` has a refinement,
again a chart above `x`, with exactly `n` irreducible components through its point: the
supremum defining the branch count is finite, so it is attained at an elementary étale
neighbourhood, which a chart above `x` refines. -/
private theorem exists_chartPoint_encard_eq_of_numberOfBranches_eq (x : points B S hS F)
    (U : BigFppfOver B S hS) (a : yoneda.obj U ⟶ F)
    (u : (BigFppfOver.toScheme B S hS).obj U) (ha : IsEtale B S hS a)
    (hu : ChartPoint B S hS U a u x) (n : ℕ)
    (hn : numberOfBranches ((BigFppfOver.toScheme B S hS).obj U) u = (n : ℕ∞)) :
    ∃ (V : BigFppfOver B S hS) (b : yoneda.obj V ⟶ F)
      (v : (BigFppfOver.toScheme B S hS).obj V),
      IsEtale B S hS b ∧ ChartPoint B S hS V b v x ∧
      Set.encard
          {Z ∈ irreducibleComponents ((BigFppfOver.toScheme B S hS).obj V) | v ∈ Z} =
        (n : ℕ∞) := by
  classical
  obtain ⟨p, rfl, hp⟩ := hu
  let X := (BigFppfOver.toScheme B S hS).obj U
  let I := {N : _root_.AlgebraicGeometry.EtaleNeighborhood X (schemePoint B S hS U p) //
    N.IsElementary}
  let c : I → ℕ∞ := fun N ↦
    Set.encard {Z ∈ irreducibleComponents N.1.scheme | N.1.point ∈ Z}
  have : Nonempty I :=
    ⟨⟨_root_.AlgebraicGeometry.EtaleNeighborhood.self X (schemePoint B S hS U p),
      _root_.AlgebraicGeometry.EtaleNeighborhood.isElementary_self X
        (schemePoint B S hS U p)⟩⟩
  have hsup : (⨆ N : I, c N) = (n : ℕ∞) := by
    rw [← hn, numberOfBranches_eq_iSup_encard_irreducibleComponentsThrough]
    exact (iSup_subtype'
      (p := fun N : _root_.AlgebraicGeometry.EtaleNeighborhood X (schemePoint B S hS U p) ↦
        N.IsElementary)
      (f := fun N _ ↦ Set.encard {Z ∈ irreducibleComponents N.scheme | N.point ∈ Z})).symm
  obtain ⟨N, hN⟩ := ENat.exists_eq_iSup_of_lt_top (hsup.trans_lt (ENat.natCast_lt_top n))
  obtain ⟨V, b, v, hb, hv, heq⟩ :=
    exists_chartPoint_encard_irreducibleComponentsThrough_eq B S hS x U a ha p hp N.1
  exact ⟨V, b, v, hb, hv, heq.symm.trans (hN.trans hsup)⟩

/-- **Stacks 0DQ3, conditions (2) and (3).** A point of a presheaf on the big fppf site has
irreducible-component count `n` on its étale scheme charts exactly when it has branch count `n`
on them.

No algebraicity hypothesis is needed: both directions only use that an étale neighbourhood of a
point of a chart above `x` is refined by an open subscheme of a chart above `x`. -/
@[stacks 0DQ3 "conditions (2) and (3)"]
theorem componentCount_iff_branchCount (x : points B S hS F) (n : ℕ) :
    HasComponentCount B S hS x n ↔ HasBranchCount B S hS x n := by
  constructor
  · rintro ⟨hall, U, a, u, ha, hu, hex⟩
    exact ⟨numberOfBranches_le_of_forall_chartPoint B S hS x n hall, U, a, u, ha, hu,
      le_antisymm (numberOfBranches_le_of_forall_chartPoint B S hS x n hall U a u ha hu)
        (hex.symm.trans_le (encard_irreducibleComponentsThrough_le_numberOfBranches _ u))⟩
  · rintro ⟨hall, U, a, u, ha, hu, hex⟩
    exact ⟨fun V b v hb hv ↦
        (encard_irreducibleComponentsThrough_le_numberOfBranches _ v).trans (hall V b v hb hv),
      exists_chartPoint_encard_eq_of_numberOfBranches_eq B S hS x U a u ha hu n hex⟩

/-! ### Conditions (3) and (4) -/

/-- **Stacks 0DQ3, conditions (3) and (4).** A point of an algebraic space has branch count `n`
on its étale scheme charts exactly when every chart has exactly `n` geometric branches at every
point above it. -/
@[stacks 0DQ3 "conditions (3) and (4)"]
theorem branchCount_iff_geometricBranchCount (hF : IsAlgebraicSpace B S hS F)
    (x : points B S hS F) (n : ℕ) :
    HasBranchCount B S hS x n ↔ HasGeometricBranchCount B S hS x n := by
  classical
  constructor
  · intro hb
    obtain ⟨hcall, -⟩ := (componentCount_iff_branchCount B S hS x n).mpr hb
    obtain ⟨U, a, u, ha, hu, hex⟩ := hb.2
    have hgeo : numberOfGeometricBranches ((BigFppfOver.toScheme B S hS).obj U) u = (n : ℕ∞) :=
      le_antisymm
        (numberOfGeometricBranches_le_of_forall_chartPoint B S hS x n hcall U a u ha hu)
        (hex.symm.trans_le (numberOfBranches_le_numberOfGeometricBranches _ u))
    obtain ⟨p, rfl, hp⟩ := hu
    have hall := (forall_etale_chart_iff_exists_etale_chart B S hS F hF x
      (fun G : GermOfScheme.{u} ↦ numberOfGeometricBranches G.scheme G.point = (n : ℕ∞))
      (GermOfScheme.isEtaleLocal_numberOfGeometricBranches_eq (n : ℕ∞))).mpr
      ⟨U, a, (isEtale_iff_presheaf_of_yoneda B S hS a).mp ha, p, hp, hgeo⟩
    intro V b v hb' hv
    obtain ⟨q, rfl, hq⟩ := hv
    exact hall V b ((isEtale_iff_presheaf_of_yoneda B S hS b).mp hb') q hq
  · intro hgeo
    refine (componentCount_iff_branchCount B S hS x n).mp ⟨fun V b v hb hv ↦ ?_, ?_⟩
    · exact (encard_irreducibleComponentsThrough_le_numberOfBranches _ v).trans
        ((numberOfBranches_le_numberOfGeometricBranches _ v).trans_eq (hgeo V b v hb hv))
    · obtain ⟨U, a, ha, p, hp⟩ := exists_etale_chart_at_point B S hS F hF x
      have ha' : IsEtale B S hS a := (isEtale_iff_presheaf_of_yoneda B S hS a).mpr ha
      have hs := hgeo U a (schemePoint B S hS U p) ha' ⟨p, rfl, hp⟩
      rw [numberOfGeometricBranches_eq_iSup_encard] at hs
      have : Nonempty (_root_.AlgebraicGeometry.EtaleNeighborhood
          ((BigFppfOver.toScheme B S hS).obj U) (schemePoint B S hS U p)) :=
        ⟨_root_.AlgebraicGeometry.EtaleNeighborhood.self _ _⟩
      obtain ⟨N, hN⟩ := ENat.exists_eq_iSup_of_lt_top (hs.trans_lt (ENat.natCast_lt_top n))
      obtain ⟨V, b, v, hb, hv, heq⟩ :=
        exists_chartPoint_encard_irreducibleComponentsThrough_eq B S hS x U a ha' p hp N
      exact ⟨V, b, v, hb, hv, heq.symm.trans (hN.trans hs)⟩

/-! ### Conditions (4) and (5) -/

/-- **Stacks 0DQ3 through 04KF.** The number of minimal primes of the étale local ring of an
algebraic space at a geometric point is the number of geometric branches of the chart of any
small étale neighbourhood of that point, at the point the neighbourhood selects: the étale local
ring is a strict henselization of the local ring of the chart there. -/
theorem encard_minimalPrimes_etaleLocalRing_eq (hF : IsAlgebraicSpace B S hS F)
    {g : GeometricPoint B S hS F} (V : SmallEtaleNeighborhood g) :
    Set.encard (minimalPrimes (etaleLocalRing B S hS F g)) =
      numberOfGeometricBranches (chartScheme V.chart)
        ((chartGeometricPoint V).hom (closedPoint (chartGeometricPoint V).residueField)) := by
  have hV : (bigEtaleSiteOfFppfSite B).Contains (chartScheme V.chart) :=
    V.chart.obj.left.left.property
  let R := (chartScheme V.chart).presheaf.stalk
    ((chartGeometricPoint V).hom (closedPoint (chartGeometricPoint V).residueField))
  let κ := separableClosure (ResidueField R) (chartGeometricPoint V).residueField
  let T := IsLocalRing.henselizationTower R κ
  exact (encard_minimalPrimes_ringEquiv
      (strictHenselizationEquivEtaleLocalRing hF V (bigEtaleSiteOfFppfSite B) hV T)).symm.trans
    (encard_minimalPrimes_eq_numberOfGeometricBranchesOfLocalRing R κ T.strictHenselization)

/-- A point of an étale scheme chart of `F` above `x` is the point selected by a small étale
neighbourhood of a geometric point above `x`, with the same number of geometric branches: an
algebraic closure of the field of a field-valued representative is again small enough for the
chosen big fppf site, and the chart becomes a small étale neighbourhood of the resulting
geometric point. -/
private theorem exists_geometricPoint_numberOfGeometricBranches_eq (x : points B S hS F)
    (U : BigFppfOver B S hS) (a : yoneda.obj U ⟶ F)
    (ha : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))) a)
    (p : FieldValuedPoint B S hS (yoneda.obj U))
    (hp : pointsMap B S hS (yoneda.obj U) a (p.class B S hS (yoneda.obj U)) = x) :
    ∃ (g : GeometricPoint B S hS F) (_ : GeometricPoint.LiesOver g x)
      (V : SmallEtaleNeighborhood g),
      numberOfGeometricBranches ((BigFppfOver.toScheme B S hS).obj U)
          (schemePoint B S hS U p) =
        numberOfGeometricBranches (chartScheme V.chart)
          ((chartGeometricPoint V).hom
            (closedPoint (chartGeometricPoint V).residueField)) := by
  let K := AlgebraicClosure p.carrier
  let e : Spec (.of K) ⟶ Spec (.of p.carrier) :=
    Spec.map (CommRingCat.ofHom (algebraMap p.carrier K))
  have hK : B.Contains (Spec (.of K)) :=
    contains_specAlgebraicClosure B p.carrier p.contained
  let e' : B.obj hK ⟶ p.siteObject.left := B.inclusion.preimage e
  let q : FieldValuedPoint B S hS (yoneda.obj U) :=
    { carrier := K
      contained := hK
      toBase := B.inclusion.map (e' ≫ p.siteObject.hom)
      value := Over.homMk (e' ≫ p.value.left) (by rw [Category.assoc, p.value.w]; rfl) }
  have hdom : FieldValuedPoint.Dominates B S hS (yoneda.obj U) q p :=
    ⟨Over.homMk e' (by rfl), rfl⟩
  have hclass : q.class B S hS (yoneda.obj U) = p.class B S hS (yoneda.obj U) :=
    FieldValuedPoint.class_eq_class_of_hasCommonExtension B S hS (yoneda.obj U)
      ⟨q, FieldValuedPoint.dominates_refl B S hS (yoneda.obj U) q, hdom⟩
  let g : GeometricPoint B S hS F :=
    ⟨FieldValuedPoint.map B S hS (yoneda.obj U) a q, AlgebraicClosure.isAlgClosed p.carrier⟩
  have hg : GeometricPoint.LiesOver g x := by
    show (FieldValuedPoint.map B S hS (yoneda.obj U) a q).class B S hS F = x
    rwa [← pointsMap_class, hclass]
  let V : SmallEtaleNeighborhood g :=
    { chart := ⟨CostructuredArrow.mk a, ha⟩
      point := q.value
      point_comp := rfl }
  refine ⟨g, hg, V, ?_⟩
  have he : e (closedPoint K) = closedPoint p.carrier := Subsingleton.elim _ _
  have hmap : B.inclusion.map e' = e :=
    B.inclusion.map_preimage
      (show B.inclusion.obj (B.obj hK) ⟶ B.inclusion.obj p.siteObject.left from e)
  show numberOfGeometricBranches ((BigFppfOver.toScheme B S hS).obj U)
      (schemePoint B S hS U p) =
    numberOfGeometricBranches ((BigFppfOver.toScheme B S hS).obj U)
      (B.inclusion.map (e' ≫ p.value.left) (closedPoint K))
  have hpoint : B.inclusion.map (e' ≫ p.value.left) (closedPoint K) =
      schemePoint B S hS U p := by
    show (B.inclusion.map p.value.left) ((B.inclusion.map e') (closedPoint K)) = _
    rw [hmap, he]
    rfl
  exact congrArg _ hpoint.symm

/-- **Stacks 0DQ3, conditions (4) and (5).** Every étale scheme chart of an algebraic space has
exactly `n` geometric branches at every point above `x` exactly when the étale local ring at
every geometric point above `x` has exactly `n` minimal primes. -/
@[stacks 0DQ3 "conditions (4) and (5)"]
theorem geometricBranchCount_iff_etaleLocalRingMinimalPrimeCount
    (hF : IsAlgebraicSpace B S hS F) (x : points B S hS F) (n : ℕ) :
    HasGeometricBranchCount B S hS x n ↔
      HasEtaleLocalRingMinimalPrimeCount B S hS x n := by
  constructor
  · intro h g hg
    obtain ⟨U, a, hsurj, hetale⟩ := hF.exists_atlas
    obtain ⟨⟨V, -⟩⟩ := exists_pointed_smallEtaleNeighborhood B S hS F hF g a hsurj hetale
    rw [encard_minimalPrimes_etaleLocalRing_eq B S hS hF V]
    exact h V.chart.obj.left V.chart.obj.hom _
      ((isEtale_iff_presheaf_of_yoneda B S hS V.chart.obj.hom).mpr V.chart.property)
      ⟨chartFieldValuedPoint V, rfl, (chartFieldValuedPoint_pointsMap V).trans hg⟩
  · intro h U a u ha hu
    obtain ⟨p, rfl, hp⟩ := hu
    obtain ⟨g, hg, V, heq⟩ := exists_geometricPoint_numberOfGeometricBranches_eq B S hS x U a
      ((isEtale_iff_presheaf_of_yoneda B S hS a).mp ha) p hp
    rw [heq, ← encard_minimalPrimes_etaleLocalRing_eq B S hS hF V]
    exact h g hg

end Space

end AlgebraicGeometry

end
