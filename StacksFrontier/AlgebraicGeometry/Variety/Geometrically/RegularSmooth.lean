module

public import StacksFrontier.AlgebraicGeometry.Smooth.InfinitesimalLifting
public import StacksFrontier.AlgebraicGeometry.Variety.Geometrically.Regular
public import StacksFrontier.RingTheory.GeometricallyRegular.FormalSmoothness
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Geometric regularity and smoothness over a field

A scheme locally of finite type over a field is geometrically regular at a point exactly when
its structure morphism is smooth at that point.

## Main results

* `AlgebraicGeometry.isGeometricallyRegularAt_iff_smoothAt` characterizes geometric regularity
  at a point as smoothness there.

## Implementation notes

Local finite type is expressed by the typeclass `AlgebraicGeometry.LocallyOfFiniteType` for the
chosen morphism to the spectrum of the field. Geometric regularity is the pointwise predicate
`AlgebraicGeometry.IsGeometricallyRegularAt`, and smoothness at a point is
`InfinitesimalLifting.SmoothAt`.

## References

* [Stacks Project, Tag 038X](https://stacks.math.columbia.edu/tag/038X)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry

open scoped TensorProduct

universe u


/-- For a Noetherian local algebra over a field, geometric regularity is formal smoothness for
the adic topology of the maximal ideal. -/
@[ega "0 19.0.2",
  ega "0 19.6.5" "more general",
  ega "0 19.6.6" "more general",
  ega "0 19.6.7",
  ega "0 22.5.8",
  ega "0 22.6.7" "more general",
  ega "IV 7.5.4" "special case"]
private lemma isGeometricallyRegular_iff_formallySmoothNAdic
    (k : Type u) (A : Type u) [Field k] [CommRing A] [Algebra k A]
    [IsNoetherianRing A] [IsLocalRing A] :
    Algebra.IsGeometricallyRegular k A ↔
      RingHom.FormallySmoothNAdic.{u} (algebraMap k A) (IsLocalRing.maximalIdeal A) := by
  let : TopologicalSpace k := ⊥
  have : DiscreteTopology k := ⟨rfl⟩
  let : TopologicalSpace A := (IsLocalRing.maximalIdeal A).adicTopology
  have : IsTopologicalRing A := (IsLocalRing.maximalIdeal A).ringFilterBasis.isTopologicalRing
  have : IsLinearTopology A A := (IsLocalRing.maximalIdeal A).isLinearTopology
  rw [← isFormallySmooth_iff_formallySmoothNAdic (algebraMap k A) (IsLocalRing.maximalIdeal A)
    rfl]
  obtain hk | ⟨p, hp, hkp⟩ := CharP.exists' k
  · have : CharZero k := hk
    rw [← (formalSmoothness_maximalIdeal_characterizations k A).1]
    refine ⟨fun h => ?_, fun h => ?_⟩
    · have : IsRegularRing (k ⊗[k] A) := h.isRegularRing_tensorProduct k
      have : IsRegularRing A :=
        IsRegularRing.of_ringEquiv (Algebra.TensorProduct.lid k A).toRingEquiv
      exact IsRegularLocalRing.of_isRegularRing_of_isLocalRing A
    · have : IsRegularLocalRing A := h
      have : IsRegularRing A := ((IsLocalRing.isRegularRing_tfae (R := A)).out 1 3).mp h
      exact isGeometricallyRegular_of_isRegularRing_of_charZero k A
  · have := hp
    have := hkp
    exact ((formalSmoothness_maximalIdeal_characterizations k A).2 p).out 1 2

/-- For an essentially finite type Noetherian local algebra, adic formal smoothness gives
formal smoothness. -/
@[ega "0 22.6.7" "(i), b)⇒a), case k = k₀"]
private lemma formallySmooth_of_formallySmoothNAdic_of_essFiniteType
    (k : Type u) (A : Type u) [Field k] [CommRing A] [Algebra k A]
    [IsNoetherianRing A] [IsLocalRing A] [Algebra.EssFiniteType k A]
    (h : RingHom.FormallySmoothNAdic.{u} (algebraMap k A)
      (IsLocalRing.maximalIdeal A)) : Algebra.FormallySmooth k A := by
  apply InfinitesimalLifting.formallySmooth_of_algLifts_essFiniteType k A
  intro B' B _ _ _ _ _ _ _ _ φ hφ hsq _ a ha
  have : IsLocalHom a.toRingHom := ha.isLocalHom
  obtain ⟨n, hn⟩ := (isArtinianRing_iff_isNilpotent_maximalIdeal B).mp inferInstance
  have hker : (IsLocalRing.maximalIdeal A) ^ n ≤ RingHom.ker a.toRingHom := by
    intro z hz
    rw [RingHom.mem_ker]
    have hz' : a z ∈ (IsLocalRing.maximalIdeal B) ^ n := by
      have hzmap := Ideal.mem_map_of_mem a.toRingHom hz
      rw [Ideal.map_pow] at hzmap
      exact pow_le_pow_left' (IsLocalRing.map_maximalIdeal_le a.toRingHom) n hzmap
    simpa [hn] using hz'
  let e := φ.toRingHom.quotientKerEquivOfSurjective hφ
  let ψ : A →+* B' ⧸ RingHom.ker φ.toRingHom := e.symm.toRingHom.comp a.toRingHom
  obtain ⟨g, hg, hgk⟩ :=
    h B' (RingHom.ker φ.toRingHom) hsq (algebraMap k B') ψ
      (by
        show (e.symm.toRingHom.comp a.toRingHom).comp (algebraMap k A) =
          (Ideal.Quotient.mk _).comp (algebraMap k B')
        rw [RingHom.comp_assoc,
          show a.toRingHom.comp (algebraMap k A) = algebraMap k B from RingHom.ext a.commutes,
          show algebraMap k B = φ.toRingHom.comp (algebraMap k B') from
            RingHom.ext fun r => (φ.commutes r).symm,
          ← RingHom.comp_assoc]
        exact congrArg (fun q => q.comp (algebraMap k B'))
          (RingHom.quotientKerEquivOfSurjective_symm_comp hφ))
      ⟨n + 1, by omega, by
        intro z hz
        show e.symm (a z) = 0
        rw [show a z = 0 from hker (Ideal.pow_le_pow_right n.le_succ hz), map_zero]⟩
  refine ⟨⟨g, RingHom.congr_fun hgk⟩, ?_⟩
  ext z
  apply e.symm.injective
  show e.symm (φ (g z)) = e.symm (a z)
  exact (RingHom.congr_fun (RingHom.quotientKerEquivOfSurjective_symm_comp hφ) (g z)).trans
    (RingHom.congr_fun hg z)

/-- Formal smoothness gives adic formal smoothness for every ideal. -/
private lemma formallySmoothNAdic_of_formallySmooth
    (k : Type u) (A : Type u) [Field k] [CommRing A] [Algebra k A]
    (h : Algebra.FormallySmooth k A) (I : Ideal A) :
    RingHom.FormallySmoothNAdic.{u} (algebraMap k A) I := by
  intro B _ J hJ f ψ hcomm _
  let : Algebra k B := f.toAlgebra
  let ψₐ : A →ₐ[k] B ⧸ J := ⟨ψ, RingHom.congr_fun hcomm⟩
  obtain ⟨g, hg⟩ := h.exists_lift J ⟨2, hJ⟩ ψₐ
  exact ⟨g.toRingHom, congrArg AlgHom.toRingHom hg, g.comp_algebraMap⟩

/-- **Stacks Project, Tag 038X.** For a scheme locally of finite type over a field, geometric
regularity at a point is equivalent to smoothness of the structure morphism at that point. -/
@[stacks 038X,
  ega "IV 17.5.2" "base a field, pointwise",
  ega "IV 17.5.5" "base = Spec k",
  ega "IV 17.15.2" "more general", sga "1 II 5.4" "more general"]
public lemma isGeometricallyRegularAt_iff_smoothAt
    {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    [LocallyOfFiniteType f] (x : X) :
    IsGeometricallyRegularAt f x ↔ InfinitesimalLifting.SmoothAt f x := by
  let R := (Spec (.of k)).presheaf.stalk (f.base x)
  let A := X.presheaf.stalk x
  let : Algebra k R := StructureSheaf.stalkAlgebra k (f.base x)
  let : Algebra R A := (f.stalkMap x).hom.toAlgebra
  let : Algebra k A := ((f.stalkMap x).hom.comp (algebraMap k R)).toAlgebra
  have : IsScalarTower k R A := IsScalarTower.of_algebraMap_eq' rfl
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have hgeo := (geometricallyRegularAt_tfae k X f x).out 1 3
  have : (f.base x).asIdeal.IsPrime := (f.base x).isPrime
  have : IsLocalization.AtPrime R (f.base x).asIdeal :=
    StructureSheaf.IsLocalization.to_stalk k (f.base x)
  have : Algebra.FormallyEtale k R :=
    Algebra.FormallyEtale.of_isLocalization (f.base x).asIdeal.primeCompl
  have : Algebra.EssFiniteType R A := LocallyOfFiniteType.stalkMap f x
  have : Algebra.EssFiniteType k R :=
    Algebra.EssFiniteType.of_isLocalization (R := k) (S := R) (f.base x).asIdeal.primeCompl
  have : Algebra.EssFiniteType k A := Algebra.EssFiniteType.comp k R A
  refine ⟨fun h => ?_, fun h => ?_⟩
  · exact InfinitesimalLifting.formallySmooth_stalkMap_smoothAt f x
      (Algebra.FormallySmooth.iff_restrictScalars.mp
        (formallySmooth_of_formallySmoothNAdic_of_essFiniteType k A
          ((isGeometricallyRegular_iff_formallySmoothNAdic k A).mp (hgeo.mp h))))
  · exact hgeo.mpr ((isGeometricallyRegular_iff_formallySmoothNAdic k A).mpr
      (formallySmoothNAdic_of_formallySmooth k A
        (Algebra.FormallySmooth.iff_restrictScalars.mpr
          (InfinitesimalLifting.SmoothAt.formallySmooth_stalkMap f x h)) _))

end AlgebraicGeometry
