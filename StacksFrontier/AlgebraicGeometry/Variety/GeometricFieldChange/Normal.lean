module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyInjective
public import Mathlib.Data.List.TFAE
public import Mathlib.FieldTheory.PurelyInseparable.Basic
public import Mathlib.FieldTheory.PurelyInseparable.PerfectClosure
public import Mathlib.RingTheory.Spectrum.Prime.Homeomorph
public import StacksCore.RingTheory.Flat.FaithfullyFlat.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Morphisms.CohenMacaulay.FieldExtensionStalk
public import StacksFrontier.AlgebraicGeometry.Variety.Geometrically.BaseChange
public import StacksFrontier.AlgebraicGeometry.Variety.Geometrically.Normal
public import StacksFrontier.RingTheory.GeometricallyNormal.Defs
public import StacksFrontier.RingTheory.GeometricallyNormal.TFAE
public import StacksFrontier.RingTheory.IntegrallyClosed.FaithfullyFlatDescent

/-!
# Geometric normality at a point, and change of base field

Geometric normality of a scheme over a field at a point can be tested after finite purely
inseparable extensions of the ground field, or on the local ring at the point; and it is
unchanged by passing to any point above it after an arbitrary extension of the ground field.

Base change is the scheme-theoretic pullback, and a point lies over `x` when its image under the
first pullback projection is `x`. The `k`-algebra structure on the local ring at `x` is the
composite of the canonical map from `k` to the stalk of `Spec k` and the stalk map of the
structure morphism.

## Main results

* `AlgebraicGeometry.geometricallyNormalAt_tfae`: the three equivalent characterizations of
  geometric normality at a point.
* `AlgebraicGeometry.isGeometricallyNormalAt_iff_baseChange`: geometric normality at a point is
  invariant under extension of the base field.
* `AlgebraicGeometry.isGeometricallyNormal_iff_baseChange_of_isGeometricallyNormalAt`: a scheme
  is geometrically normal exactly when its base change along any extension of the base field is.

## References

* [Stacks Project, Tag 038N](https://stacks.math.columbia.edu/tag/038N)
* [Stacks Project, Tag 038P](https://stacks.math.columbia.edu/tag/038P)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CommRingCat
open scoped TensorProduct

universe u

namespace AlgebraicGeometry

private lemma fieldToStalk_eq (k : Type u) [Field k] (X : Scheme.{u})
    (f : X ⟶ Spec (.of k)) (x : X) :
    letI : Algebra k (X.presheaf.stalk x) :=
      letI : Algebra k ((Spec (.of k)).presheaf.stalk (f.base x)) :=
        StructureSheaf.stalkAlgebra k (f.base x)
      ((f.stalkMap x).hom.comp
        (algebraMap k ((Spec (.of k)).presheaf.stalk (f.base x)))).toAlgebra
    fieldToStalk f x =
      CommRingCat.ofHom (algebraMap k (X.presheaf.stalk x)) := by
  let z : PrimeSpectrum.Top k := f.base x
  let Rk := (Spec (.of k)).presheaf.stalk z
  let : Algebra k Rk := StructureSheaf.stalkAlgebra k z
  ext a
  show (X.presheaf.germ ⊤ x trivial)
      (f.appTop ((Scheme.ΓSpecIso (.of k)).inv a)) =
    (f.stalkMap x).hom (algebraMap k Rk a)
  rw [show algebraMap k Rk a = StructureSheaf.toStalk k z a by rfl]
  show (X.presheaf.germ ⊤ x trivial)
      (f.appTop ((Scheme.ΓSpecIso (.of k)).inv a)) =
    (f.stalkMap x).hom
      ((Spec (.of k)).presheaf.germ ⊤ z trivial ((Scheme.ΓSpecIso (.of k)).inv a))
  exact (Scheme.Hom.germ_stalkMap_apply (f := f) (U := ⊤) (x := x)
    (hx := by simp) ((Scheme.ΓSpecIso (.of k)).inv a)).symm

private lemma stalkBaseChange_isPushout (k K : Type u) [Field k] [Field K]
    [Algebra k K] (X : Scheme.{u}) (f : X ⟶ Spec (.of k)) (x : X)
    [Algebra k (X.presheaf.stalk x)]
    (hfieldCat : fieldToStalk f x =
      CommRingCat.ofHom (algebraMap k (X.presheaf.stalk x))) :
    IsPushout (fieldToStalk f x)
      (CommRingCat.ofHom (algebraMap k K))
      (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom :
        X.presheaf.stalk x →+* X.presheaf.stalk x ⊗[k] K))
      (CommRingCat.ofHom (Algebra.TensorProduct.includeRight.toRingHom :
        K →+* X.presheaf.stalk x ⊗[k] K)) := by
  let R := X.presheaf.stalk x
  let eR : CommRingCat.of R ≅ R := eqToIso (CommRingCat.of_carrier R)
  refine (CommRingCat.isPushout_tensorProduct k R K).of_iso'
    (Iso.refl _) eR.symm (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
  · rw [← hfieldCat]; exact (Category.comp_id _).symm
  · simp
  · ext a; rfl
  · simp

/-- The local ring of the base change at `y` over `x` is a localization of `𝒪_{X,x} ⊗_k K` at a
prime lying over the maximal ideal of `𝒪_{X,x}`. -/
private lemma exists_isLocalization_stalkBaseChange (k K : Type u) [Field k] [Field K] [Algebra k K]
    (X : Scheme.{u}) (f : X ⟶ Spec (.of k)) (x : X)
    (y : (pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K))) : Scheme.{u}))
    (hy : (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k K)))).base y = x) :
    ∃ (p : Ideal (stalkBaseChangeRing (K := K) f x)) (_ : p.IsPrime)
      (_ : Algebra (stalkBaseChangeRing (K := K) f x)
        ((pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K))) :
          Scheme.{u}).presheaf.stalk y)),
      IsLocalization.AtPrime ((pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K))) :
          Scheme.{u}).presheaf.stalk y) p ∧
      p.comap (pushout.inl (fieldToStalk f x) (CommRingCat.ofHom (algebraMap k K))).hom =
        IsLocalRing.maximalIdeal (X.presheaf.stalk x) := by
  obtain ⟨θ, ψ, φ, hθ₁, hθ₂, hψ₁, hψ₂, hφ₁, hφ₂, hcomm, hloc⟩ :=
    stalkOfBaseChange_isLocalization f x y hy
  let : Algebra (stalkBaseChangeRing (K := K) f x) _ := φ.hom.toAlgebra
  let : (RingHom.ker ψ.hom).IsPrime := RingHom.ker_isPrime _
  let : (stalkBaseChangePrime f x θ (RingHom.ker ψ.hom)).IsPrime := Ideal.comap_isPrime _ _
  refine ⟨stalkBaseChangePrime f x θ (RingHom.ker ψ.hom), inferInstance, φ.hom.toAlgebra, hloc, ?_⟩
  have hle : IsLocalRing.maximalIdeal (X.presheaf.stalk x) ≤ Ideal.comap
      (pushout.inl (fieldToStalk f x) (CommRingCat.ofHom (algebraMap k K))).hom
      (stalkBaseChangePrime f x θ (RingHom.ker ψ.hom)) := by
    intro r hr
    refine (DFunLike.congr_fun (congrArg CommRingCat.Hom.hom
      (congrArg (fun g ↦ g ≫ ψ) hθ₁)) r).trans ?_
    erw [Category.assoc, CommRingCat.hom_comp, RingHom.comp_apply,
      show (X.residue x).hom r = 0 from (IsLocalRing.residue_eq_zero_iff _).2 hr, map_zero]
  exact ((IsLocalRing.maximalIdeal.isMaximal _).eq_of_le
    (Ideal.comap_isPrime _ _).ne_top hle).symm

/-- Geometric normality at a point is equivalent both to normality at every point above it after
every finite purely inseparable field extension and to geometric normality of its local ring over
the ground field. -/
@[stacks 038N]
lemma geometricallyNormalAt_tfae
    (k : Type u) [Field k] (X : Scheme.{u}) (f : X ⟶ Spec (.of k)) (x : X) :
    List.TFAE [
      IsGeometricallyNormalAt f x,
      ∀ (K : Type u) [Field K] [Algebra k K] [Module.Finite k K]
        [IsPurelyInseparable k K],
        ∀ (x' : (pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K))) : Scheme.{u})),
          pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k K))) x' = x →
            IsNormalRing
              ((pullback f
                (Spec.map (CommRingCat.ofHom (algebraMap k K))) : Scheme.{u}).presheaf.stalk x'),
      letI : Algebra k (X.presheaf.stalk x) :=
        letI : Algebra k ((Spec (.of k)).presheaf.stalk (f.base x)) :=
          StructureSheaf.stalkAlgebra k (f.base x)
        ((f.stalkMap x).hom.comp
          (algebraMap k ((Spec (.of k)).presheaf.stalk (f.base x)))).toAlgebra
      Algebra.IsGeometricallyNormal k (X.presheaf.stalk x)] := by
  tfae_have 1 → 2 := fun h K _ _ _ _ y hy ↦
    (isGeometricallyNormalAt_iff f x).mp h K y hy
  tfae_have 2 → 3 := by
    intro h
    let R := X.presheaf.stalk x
    let : Algebra k R :=
      let : Algebra k ((Spec (.of k)).presheaf.stalk (f.base x)) :=
        StructureSheaf.stalkAlgebra k (f.base x)
      ((f.stalkMap x).hom.comp
        (algebraMap k ((Spec (.of k)).presheaf.stalk (f.base x)))).toAlgebra
    show Algebra.IsGeometricallyNormal k R
    obtain ⟨p, _⟩ := ExpChar.exists k
    have : ExpChar (AlgebraicClosure k) p := expChar_of_injective_algebraMap
      (algebraMap k (AlgebraicClosure k)).injective p
    have : PerfectRing (AlgebraicClosure k) p := PerfectField.toPerfectRing p
    set kp := (perfectClosure k (AlgebraicClosure k) : IntermediateField k (AlgebraicClosure k))
    have : ExpChar kp p := expChar_of_injective_algebraMap (algebraMap k kp).injective p
    have : IsPerfectClosure (algebraMap k kp) p := IsPurelyInseparable.isPRadical k kp p
    refine ⟨((Algebra.isNormalRing_tensorProduct_tfae k p R kp).out 3 1).mp ?_⟩
    intro K hKf hKa hKfin hKpi
    let A := stalkBaseChangeRing (K := K) f x
    let iR : CommRingCat.of R ⟶ A :=
      pushout.inl (fieldToStalk f x)
        (CommRingCat.ofHom (algebraMap k K))
    let : Algebra R A := iR.hom.toAlgebra
    let hpo := stalkBaseChange_isPushout k K X f x (fieldToStalk_eq k X f x)
    let e : A ≃+* (R ⊗[k] K) := hpo.isoPushout.symm.commRingCatIsoToRingEquiv
    have heR (r : R) : e (algebraMap R A r) =
        Algebra.TensorProduct.includeLeftRingHom r := by
      show (CommRingCat.Hom.hom
        (pushout.inl (fieldToStalk f x)
          (CommRingCat.ofHom (algebraMap k K)) ≫ hpo.isoPushout.inv)) r =
          Algebra.TensorProduct.includeLeftRingHom r
      exact DFunLike.congr_fun (congrArg CommRingCat.Hom.hom hpo.inl_isoPushout_inv) r
    let : IsLocalRing (R ⊗[k] K) := by
      obtain ⟨m, hm⟩ := Ideal.exists_maximal (α := R ⊗[k] K)
      have : m.IsMaximal := hm
      refine IsLocalRing.of_unique_max_ideal ⟨m, hm, fun q hq ↦ ?_⟩
      have : q.IsMaximal := hq
      apply congrArg PrimeSpectrum.asIdeal
        ((PrimeSpectrum.isHomeomorph_comap_of_isPurelyInseparable k K R).injective
          (a₁ := ⟨q, inferInstance⟩) (a₂ := ⟨m, inferInstance⟩) ?_)
      exact PrimeSpectrum.ext <| ((IsLocalRing.isMaximal_iff R).mp
          (Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := R) q)).trans
        ((IsLocalRing.isMaximal_iff R).mp
          (Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := R) m)).symm
    let : IsLocalRing A := e.symm.isLocalRing
    let Y : Scheme := pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K)))
    let z : Spec (.of K) := Classical.choice inferInstance
    have hz : f x = Spec.map (CommRingCat.ofHom (algebraMap k K)) z := Subsingleton.elim _ _
    obtain ⟨y, hyx, _⟩ := Scheme.Pullback.exists_preimage_pullback x z hz
    have hy : (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k K)))) y = x := hyx
    obtain ⟨p, _, _, hloc, hcontract⟩ := exists_isLocalization_stalkBaseChange k K X f x y hy
    let eAlg : A ≃ₐ[R] (R ⊗[k] K) := AlgEquiv.ofRingEquiv (f := e) heR
    let : Algebra.IsIntegral R A := eAlg.isIntegral_iff.mpr inferInstance
    have hpmax : p.IsMaximal :=
      Ideal.isMaximal_of_isIntegral_of_isMaximal_under (R := R) p
        (by rw [Ideal.under]; exact hcontract ▸ IsLocalRing.maximalIdeal.isMaximal R)
    have hunit : p.primeCompl ≤ IsUnit.submonoid A := by
      intro a ha
      apply (IsLocalRing.notMem_maximalIdeal).mp
      simpa [IsLocalRing.eq_maximalIdeal hpmax] using ha
    let eAB : A ≃ₐ[A] (Y.presheaf.stalk y) := IsLocalization.atUnits A p.primeCompl hunit
    exact IsNormalRing.congr (Algebra.TensorProduct.comm k R K).toRingEquiv
      (IsNormalRing.congr e (IsNormalRing.congr eAB.symm.toRingEquiv (h K y hy)))
  tfae_have 3 → 1 := by
    intro h K hKf hKa y hy
    let R := X.presheaf.stalk x
    let : Algebra k R :=
      let : Algebra k ((Spec (.of k)).presheaf.stalk (f.base x)) :=
        StructureSheaf.stalkAlgebra k (f.base x)
      ((f.stalkMap x).hom.comp
        (algebraMap k ((Spec (.of k)).presheaf.stalk (f.base x)))).toAlgebra
    let A := stalkBaseChangeRing (K := K) f x
    let hpo := stalkBaseChange_isPushout k K X f x (fieldToStalk_eq k X f x)
    let e : A ≃+* (R ⊗[k] K) := hpo.isoPushout.symm.commRingCatIsoToRingEquiv
    let Y : Scheme := pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K)))
    obtain ⟨p, _, _, _, -⟩ := exists_isLocalization_stalkBaseChange k K X f x y hy
    exact (IsNormalRing.congr e.symm
      (IsNormalRing.congr (Algebra.TensorProduct.comm k R K).symm.toRingEquiv
        (h.isNormalRing_tensorProduct K))).isLocalization p.primeCompl (Y.presheaf.stalk y)
  tfae_finish

private lemma normalRing_of_flat_stalkMap {A B : Scheme.{u}} (r : A ⟶ B)
    (hr : Flat r) (z : A) (h : IsNormalRing (A.presheaf.stalk z)) :
    IsNormalRing (B.presheaf.stalk (r z)) := by
  let : Flat r := hr
  let : Algebra (B.presheaf.stalk (r z)) (A.presheaf.stalk z) :=
    (r.stalkMap z).hom.toAlgebra
  let : Module.FaithfullyFlat (B.presheaf.stalk (r z)) (A.presheaf.stalk z) :=
    @Module.FaithfullyFlat.of_flat_of_isLocalHom _ _ _ _ _ _ _
      (Flat.stalkMap r z) (r.toLRSHom.prop z)
  exact isDomain_and_isIntegrallyClosed_atPrime_of_faithfullyFlat h

private theorem pointwise_backward
    (k : Type u) [Field k] (X : Scheme.{u}) (f : X ⟶ Spec (.of k))
    (K : Type u) [Field K] [Algebra k K]
    (x : X) (x' : (pullback f (Spec.map (ofHom (algebraMap k K))) : Scheme.{u}))
    (hx' : (pullback.fst f (Spec.map (ofHom (algebraMap k K)))).base x' = x) :
    IsGeometricallyNormalAt
      (pullback.snd f (Spec.map (ofHom (algebraMap k K)))) x' →
      IsGeometricallyNormalAt f x := by
  let φ : Spec (.of K) ⟶ Spec (.of k) :=
    Spec.map (CommRingCat.ofHom (algebraMap k K))
  show IsGeometricallyNormalAt (pullback.snd f φ) x' →
      IsGeometricallyNormalAt f x
  intro h
  apply ((geometricallyNormalAt_tfae k X f x).out 2 1).mp
  intro E hE hKE hfinite hpi xE hxE
  let : IsPurelyInseparable k E := hpi
  let ψ : Spec (.of E) ⟶ Spec (.of k) :=
    Spec.map (CommRingCat.ofHom (algebraMap k E))
  let : UniversallyInjective (pullback.fst f ψ) :=
    CategoryTheory.MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (IsPullback.of_hasPullback f ψ).flip
      (universallyInjective_specMap_of_isPurelyInseparable k E)
  obtain ⟨M, _, _, _, _, hKM, hEM⟩ := exists_common_extension k K E
  let : IsScalarTower k K M := hKM
  let : IsScalarTower k E M := hEM
  let χK : Spec (.of M) ⟶ Spec (.of K) :=
    Spec.map (CommRingCat.ofHom (algebraMap K M))
  let χE : Spec (.of M) ⟶ Spec (.of E) :=
    Spec.map (CommRingCat.ofHom (algebraMap E M))
  let μ : Spec (.of M) ⟶ Spec (.of k) :=
    Spec.map (CommRingCat.ofHom (algebraMap k M))
  have hcompK : χK ≫ φ = μ := specMap_algebraMap_comp k K M
  have hcompE : χE ≫ ψ = μ := specMap_algebraMap_comp k E M
  let A : Scheme.{u} := pullback (pullback.snd f φ) χK
  obtain ⟨z, hz⟩ := (pullback.fst (pullback.snd f φ) χK).surjective x'
  have hnA : IsNormalRing (A.presheaf.stalk z) := h M z hz
  let r : A ⟶ pullback f ψ :=
    iteratedBaseChangeComparison f φ ψ χK χE μ hcompK hcompE
  have hrflat : Flat r := by dsimp [r, iteratedBaseChangeComparison]; infer_instance
  have hrx : (pullback.fst f ψ) (r z) = x := by
    rw [← Scheme.Hom.comp_apply,
      iteratedBaseChangeComparison_fst f φ ψ χK χE μ hcompK hcompE,
      Scheme.Hom.comp_apply, hz, hx']
  rw [← (pullback.fst f ψ).injective (hrx.trans hxE.symm)]
  exact normalRing_of_flat_stalkMap r hrflat z hnA

/-- Geometric normality at a point is invariant under extension of the base field. -/
@[stacks 038P "pointwise equivalence", ega "IV 6.7.8" "(vi)"]
theorem isGeometricallyNormalAt_iff_baseChange
    (k : Type u) [Field k] (X : Scheme.{u}) (f : X ⟶ Spec (.of k))
    (K : Type u) [Field K] [Algebra k K]
    (x : X) (x' : (pullback f (Spec.map (ofHom (algebraMap k K))) : Scheme.{u}))
    (hx' : (pullback.fst f (Spec.map (ofHom (algebraMap k K)))).base x' = x) :
    IsGeometricallyNormalAt f x ↔
      IsGeometricallyNormalAt
        (pullback.snd f (Spec.map (ofHom (algebraMap k K)))) x' := by
  let φ : Spec (.of K) ⟶ Spec (.of k) :=
    Spec.map (CommRingCat.ofHom (algebraMap k K))
  show IsGeometricallyNormalAt f x ↔
      IsGeometricallyNormalAt (pullback.snd f φ) x'
  constructor
  · intro h L hL hKL z hz
    let : Algebra k L := RingHom.toAlgebra ((algebraMap K L).comp (algebraMap k K))
    let : IsScalarTower k K L := .of_algebraMap_eq' rfl
    let ψ : Spec (.of L) ⟶ Spec (.of K) :=
      Spec.map (CommRingCat.ofHom (algebraMap K L))
    let μ : Spec (.of L) ⟶ Spec (.of k) :=
      Spec.map (CommRingCat.ofHom (algebraMap k L))
    have hcomp : ψ ≫ φ = μ := specMap_algebraMap_comp k K L
    let e := iteratedBaseChangeIso f φ ψ μ hcomp
    have hz' : pullback.fst f μ (e.hom z) = x := by
      rw [← hx', ← hz]
      exact congrArg (fun g ↦ g.base.hom z) (iteratedBaseChangeIso_fst f φ ψ μ hcomp)
    exact IsNormalRing.congr (asIso (e.hom.stalkMap z)).commRingCatIsoToRingEquiv
      (h L (e.hom z) hz')
  · exact pointwise_backward k X f K x x' hx'

/-- A scheme is geometrically normal exactly when any base field extension is. -/
@[stacks 038P "global equivalence", ega "IV 6.7.8" "(vi) global", ega "IV 7.3.8" "partial"]
theorem isGeometricallyNormal_iff_baseChange_of_isGeometricallyNormalAt
    (k : Type u) [Field k] (X : Scheme.{u}) (f : X ⟶ Spec (.of k))
    (K : Type u) [Field K] [Algebra k K] :
    IsGeometricallyNormal f ↔
      IsGeometricallyNormal
        (pullback.snd f (Spec.map (ofHom (algebraMap k K)))) := by
  let φ : Spec (.of K) ⟶ Spec (.of k) :=
    Spec.map (CommRingCat.ofHom (algebraMap k K))
  show IsGeometricallyNormal f ↔
      IsGeometricallyNormal (pullback.snd f φ)
  rw [isGeometricallyNormal_iff, isGeometricallyNormal_iff]
  constructor
  · intro h y'
    let x := (pullback.fst f φ).base y'
    exact (isGeometricallyNormalAt_iff_baseChange k X f K x y' rfl).mp (h x)
  · intro h x
    obtain ⟨y', hy'⟩ := (pullback.fst f φ).surjective x
    exact (isGeometricallyNormalAt_iff_baseChange k X f K x y' hy').mpr (h y')

end AlgebraicGeometry

end
