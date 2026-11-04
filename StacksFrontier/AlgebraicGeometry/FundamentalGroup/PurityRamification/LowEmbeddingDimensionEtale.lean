module

public import
  StacksFrontier.AlgebraicGeometry.FundamentalGroup.PurityRamification.LowEmbeddingDimensionUnramified
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.PurityRamification.QuasiFiniteCase
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.PurityRamificationLocus.CutByParameter
public import StacksFrontier.AlgebraicGeometry.Morphisms.Unramified.Properties
public import StacksFrontier.AlgebraicGeometry.Scheme.Points.StalkSpecialization
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.UnramifiedLocusBaseChange
public import StacksFrontier.RingTheory.RegularRing.GlobalDimension

/-!
# Purity at a normal surface point of embedding dimension at most three

[Stacks, Tag 0EA3] says: let `A` be an excellent regular local ring, `f : X ⟶ Spec A` of finite
type and `x ∈ X` with `𝒪_{X, x}` normal of dimension two; if `f` is étale outside the closure of
`x`, then `f` is étale at `x`.  This file proves that statement when in addition `𝒪_{X, x}` has
embedding dimension at most three.

Every prime of `B = 𝒪_{X, x}` other than the maximal ideal is the image of a proper generization
`z` of `x`, with `𝒪_{X, z}` the localization of `B` at it
(`Stacks.StalkSpecialization.isLocalization_atPrime_stalkSpecializes`); such a `z` lies outside
the closure of `x`, so `f` is unramified at `z` and the localization is formally unramified over
`A`.  As `B` is essentially of finite type over `A` and `A → B` is injective (`f` is étale at a
generization of `x`), `IsLocalRing.formallyUnramified_of_spanFinrank_maximalIdeal_le_three` shows
that `B` is formally unramified over `A`, i.e. `f` is unramified at `x`.  Then `f` is
quasi-finite at `x` and `AlgebraicGeometry.etaleAt_of_quasiFiniteAt_of_etaleAt_outside_closure`
applies.

## Main results

* `AlgebraicGeometry.unramifiedAt_of_spanFinrank_le_three_of_etaleAt_outside_closure` — under
  the hypotheses of [Stacks, Tag 0EA3] and embedding dimension at most three, `f` is unramified
  at `x`.
* `AlgebraicGeometry.etaleAt_of_spanFinrank_le_three_of_etaleAt_outside_closure` — the
  conclusion of [Stacks, Tag 0EA3] under its hypotheses, when `𝒪_{X, x}` has embedding dimension
  at most three.

## References

* [Stacks Project, Tag 0EA3](https://stacks.math.columbia.edu/tag/0EA3)
-/

@[expose] public section

open CategoryTheory TopologicalSpace IsLocalRing

universe u

namespace AlgebraicGeometry

/-- The localization of `𝒪_{X, x}` at a prime other than the maximal ideal is the local ring at a
proper generization `z` of `x`: namely `z` is the image of that prime under
`Spec 𝒪_{X, x} ⟶ X`, and the comparison `𝒪_{X, x} ⟶ 𝒪_{X, z}` is a localization at the
contraction of the maximal ideal of `𝒪_{X, z}`, which is the given prime because
`Spec 𝒪_{X, x} ⟶ X` is injective. -/
theorem exists_specializes_isLocalization_atPrime_stalk {X : Scheme.{u}} (x : X)
    (q : Ideal (X.presheaf.stalk x)) [q.IsPrime] (hq : q ≠ maximalIdeal _) :
    ∃ (z : X) (h : z ⤳ x), z ≠ x ∧
      letI : Algebra (X.presheaf.stalk x) (X.presheaf.stalk z) :=
        (X.presheaf.stalkSpecializes h).hom.toAlgebra
      IsLocalization.AtPrime (X.presheaf.stalk z) q := by
  let qpt : Spec (X.presheaf.stalk x) := ⟨q, inferInstance⟩
  have hinj : Function.Injective (X.fromSpecStalk x) := (X.fromSpecStalk x).isEmbedding.injective
  let z := X.fromSpecStalk x qpt
  have hz : z ⤳ x := by
    have := (X.fromSpecStalk x).base.hom.map_specializes (IsLocalRing.specializes_closedPoint qpt)
    rwa [Scheme.fromSpecStalk_closedPoint] at this
  refine ⟨z, hz, fun hzx => hq ?_, ?_⟩
  · have : qpt = closedPoint _ := hinj (hzx.trans Scheme.fromSpecStalk_closedPoint.symm)
    exact congrArg PrimeSpectrum.asIdeal this
  let : Algebra (X.presheaf.stalk x) (X.presheaf.stalk z) :=
    (X.presheaf.stalkSpecializes hz).hom.toAlgebra
  refine Stacks.StalkSpecialization.isLocalization_atPrime_of_eq ?_
    (Stacks.StalkSpecialization.isLocalization_atPrime_stalkSpecializes hz)
  have h1 : X.fromSpecStalk x
      ((Spec.map (X.presheaf.stalkSpecializes hz)) (closedPoint (X.presheaf.stalk z))) = z := by
    show (Spec.map (X.presheaf.stalkSpecializes hz) ≫ X.fromSpecStalk x)
      (closedPoint (X.presheaf.stalk z)) = z
    rw [Scheme.SpecMap_stalkSpecializes_fromSpecStalk hz, Scheme.fromSpecStalk_closedPoint]
  exact congrArg PrimeSpectrum.asIdeal (hinj h1)

/-- The local ring at a point `z` of unramifiedness of `f : X ⟶ Spec A` is formally unramified
over `A`: it is formally unramified over the localization `𝒪_{Spec A, f z}` of `A`. -/
theorem formallyUnramified_baseToStalk_of_unramifiedAt {A : Type u} [CommRing A]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) [LocallyOfFiniteType f] (z : X)
    (hz : UnramifiedAt f z) :
    letI := (toStalkStalkMap f z).toAlgebra
    Algebra.FormallyUnramified A (X.presheaf.stalk z) := by
  let R := (Spec (.of A)).presheaf.stalk (f z)
  let T := X.presheaf.stalk z
  let : Algebra A R := (StructureSheaf.toStalk A (f z)).hom.toAlgebra
  let : Algebra R T := (f.stalkMap z).hom.toAlgebra
  let : Algebra A T := (toStalkStalkMap f z).toAlgebra
  have : IsScalarTower A R T := IsScalarTower.of_algebraMap_eq' rfl
  have : (f z).asIdeal.IsPrime := (f z).isPrime
  have : IsLocalization.AtPrime R (f z).asIdeal := StructureSheaf.IsLocalization.to_stalk A (f z)
  have : Algebra.FormallyUnramified A R :=
    Algebra.FormallyUnramified.of_isLocalization (f z).asIdeal.primeCompl
  have : Algebra.FormallyUnramified R T := (unramifiedAt_iff_formallyUnramified_stalkMap f z).mp hz
  exact Algebra.FormallyUnramified.comp A R T

/-- **Unramifiedness at a normal surface point of embedding dimension at most three.** Let `A`
be an excellent regular local ring, `f : X ⟶ Spec A` locally of finite type and `x ∈ X` with
`𝒪_{X, x}` normal of dimension two and of embedding dimension at most three.  If `f` is étale
outside the closure of `x`, then `f` is unramified at `x`.

Every non-maximal prime of `B = 𝒪_{X, x}` comes from a proper generization `z` of `x`
(`AlgebraicGeometry.exists_specializes_isLocalization_atPrime_stalk`), at which `f` is étale; so
the localization of `B` there is formally unramified over `A`.  `B` is the localization of a
finitely generated `A`-subalgebra, `A → B` is injective, and
`IsLocalRing.formallyUnramified_of_spanFinrank_maximalIdeal_le_three` shows that `B` is formally
unramified over `A`, hence over `𝒪_{Spec A, f x}`. -/
theorem unramifiedAt_of_spanFinrank_le_three_of_etaleAt_outside_closure {A : Type u}
    [CommRing A] [IsRegularLocalRing A] (hA : IsExcellent A) {X : Scheme.{u}}
    (f : X ⟶ Spec (.of A)) [LocallyOfFiniteType f] (x : X)
    (hX : IsNormalRing (X.presheaf.stalk x)) (hdim : ringKrullDim (X.presheaf.stalk x) = 2)
    (hemb : (maximalIdeal (X.presheaf.stalk x)).spanFinrank ≤ 3)
    (het : ∀ z : X, z ∉ closure ({x} : Set X) → EtaleAt f z) : UnramifiedAt f x := by
  have _ : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have _ : IsDomain A := IsRegularLocalRing.isDomain A
  have _ : IsRegularRing A := ((IsLocalRing.isRegularRing_tfae (R := A)).out 1 3).mp ‹_›
  have hcat : IsUniversallyCatenary A :=
    Ring.isUniversallyCatenary_iff_isUniversallyCatenary.mp hA.2
  let B := X.presheaf.stalk x
  have _ : IsDomain B := hX.of_isLocalRing.1
  let R := (Spec (.of A)).presheaf.stalk (f x)
  let : Algebra A R := (StructureSheaf.toStalk A (f x)).hom.toAlgebra
  let : Algebra R B := (f.stalkMap x).hom.toAlgebra
  let : Algebra A B := (toStalkStalkMap f x).toAlgebra
  have : IsScalarTower A R B := IsScalarTower.of_algebraMap_eq' rfl
  have : (f x).asIdeal.IsPrime := (f x).isPrime
  have : IsLocalization.AtPrime R (f x).asIdeal := StructureSheaf.IsLocalization.to_stalk A (f x)
  have : Algebra.EssFiniteType A R := .of_isLocalization R (f x).asIdeal.primeCompl
  have : Algebra.EssFiniteType R B := LocallyOfFiniteType.stalkMap f x
  have hEFT : Algebra.EssFiniteType A B := Algebra.EssFiniteType.comp A R B
  -- `A → B` is injective: `f` is étale at a generization of `x`
  have hone : 1 ≤ ringKrullDim B := by
    rw [hdim]
    norm_num
  obtain ⟨z₀, hz₀, hdz₀⟩ := exists_specializes_ringKrullDim_stalk_eq_one x hone
  have hz₀x : z₀ ≠ x := by
    rintro rfl
    rw [hdim] at hdz₀
    norm_num at hdz₀
  have hinj : Function.Injective (algebraMap A B) :=
    baseToStalk_injective_of_etaleAt_generization f hz₀
      (het z₀ (notMem_closure_singleton_of_specializes hz₀ hz₀x))
  -- `B` is the localization of the image of a polynomial ring
  obtain ⟨σ, hσ⟩ := (Algebra.essFiniteType_iff A B).mp hEFT
  let v : Fin σ.card → B := fun i => (σ.equivFin.symm i : B)
  let ψ₀ : MvPolynomial (Fin σ.card) A →ₐ[A] B := MvPolynomial.aeval v
  have hrange : Algebra.adjoin A (σ : Set B) = ψ₀.range := by
    rw [← Algebra.adjoin_range_eq_range_aeval]
    congr 1
    ext b
    refine ⟨fun hb => ⟨σ.equivFin ⟨b, hb⟩, by simp [v]⟩, ?_⟩
    rintro ⟨i, rfl⟩
    exact (σ.equivFin.symm i).2
  have hsurj : ∀ b : B, ∃ a s, IsUnit (ψ₀ s) ∧ b * ψ₀ s = ψ₀ a := by
    intro b
    obtain ⟨t, ht, htu, hbt⟩ := hσ b
    rw [hrange] at ht hbt
    obtain ⟨s, rfl⟩ := ht
    obtain ⟨a, ha⟩ := hbt
    exact ⟨a, s, htu, ha.symm⟩
  -- the localizations at the non-maximal primes are formally unramified
  have hloc : ∀ (q : Ideal B) [q.IsPrime], q ≠ maximalIdeal B →
      Algebra.FormallyUnramified A (Localization.AtPrime q) := by
    intro q _ hq
    obtain ⟨z, hz, hzx, hT⟩ := exists_specializes_isLocalization_atPrime_stalk x q hq
    let T := X.presheaf.stalk z
    let : Algebra B T := (X.presheaf.stalkSpecializes hz).hom.toAlgebra
    let : Algebra A T := (toStalkStalkMap f z).toAlgebra
    have : IsScalarTower A B T :=
      IsScalarTower.of_algebraMap_eq' (baseToStalk_specializes f hz).symm
    have hFU : Algebra.FormallyUnramified A T :=
      formallyUnramified_baseToStalk_of_unramifiedAt f z
        (Stacks.Discriminant.unramifiedAt_of_etaleAt f z
          (het z (notMem_closure_singleton_of_specializes hz hzx)))
    exact Algebra.FormallyUnramified.of_equiv
      ((IsLocalization.algEquiv q.primeCompl T (Localization.AtPrime q)).restrictScalars A)
  have hB : Algebra.FormallyUnramified A B :=
    IsLocalRing.formallyUnramified_of_spanFinrank_maximalIdeal_le_three hcat hinj hdim hemb ψ₀
      hsurj hloc
  exact (unramifiedAt_iff_formallyUnramified_stalkMap f x).mpr
    (Algebra.FormallyUnramified.of_restrictScalars A R B)

/-- **[Stacks, Tag 0EA3] in embedding dimension at most three.**  Let `A` be an excellent regular
local ring, `f : X ⟶ Spec A` locally of finite type and `x ∈ X` with `𝒪_{X, x}` normal of
dimension two and of embedding dimension at most three.  If `f` is étale outside the closure of
`x`, then `f` is étale at `x`.

By `AlgebraicGeometry.unramifiedAt_of_spanFinrank_le_three_of_etaleAt_outside_closure` `f` is
unramified, hence quasi-finite, at `x`, and
`AlgebraicGeometry.etaleAt_of_quasiFiniteAt_of_etaleAt_outside_closure` applies. -/
theorem etaleAt_of_spanFinrank_le_three_of_etaleAt_outside_closure {A : Type u} [CommRing A]
    [IsRegularLocalRing A] (hA : IsExcellent A) {X : Scheme.{u}} (f : X ⟶ Spec (.of A))
    [LocallyOfFiniteType f] (x : X) (hX : IsNormalRing (X.presheaf.stalk x))
    (hdim : ringKrullDim (X.presheaf.stalk x) = 2)
    (hemb : (maximalIdeal (X.presheaf.stalk x)).spanFinrank ≤ 3)
    (het : ∀ z : X, z ∉ closure ({x} : Set X) → EtaleAt f z) : EtaleAt f x :=
  etaleAt_of_quasiFiniteAt_of_etaleAt_outside_closure hA f x hX hdim het
    (quasiFiniteAt_of_unramifiedAt f
      (unramifiedAt_of_spanFinrank_le_three_of_etaleAt_outside_closure hA f x hX hdim hemb het))

end AlgebraicGeometry

end
