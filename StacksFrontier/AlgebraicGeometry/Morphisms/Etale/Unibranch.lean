module

public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Morphisms.Etale.Defs
public import StacksFrontier.AlgebraicGeometry.Morphisms.Unramified.Defs
public import StacksFrontier.AlgebraicGeometry.Properties.PrincipalOpens.GeometricBranches
public import StacksFrontier.RingTheory.Branches.Miscellaneous

/-!
# Unramified morphisms over a geometrically unibranch base are étale

Let `f : X ⟶ Y` be locally of finite type with `Y` integral. If `Y` is geometrically unibranch at
the image of a point `x` of `X`, if `f` is unramified at `x`, and if `x` is a specialization of a
point lying over the generic point of `Y`, then `f` is étale at `x`.

## Main results

* `AlgebraicGeometry.etaleAt_of_unramifiedAt_of_specializes_genericPoint`: such a morphism,
  unramified at `x`, is étale at `x`.

## References

* [Stacks Project, Tag 0GS8](https://stacks.math.columbia.edu/tag/0GS8)
-/

public section

open CategoryTheory

namespace AlgebraicGeometry

universe u

/-- Let `f : X ⟶ Y` be locally of finite type with `Y` integral,
and let `x : X` be a point whose image is a point where `Y` is geometrically unibranch. If `f`
is unramified at `x` and `x` is a specialization of a point lying over the generic point of `Y`,
then `f` is étale at `x`. -/
@[stacks 0GS8, ega "IV 18.10.1" "suff.; generic pt in"]
theorem etaleAt_of_unramifiedAt_of_specializes_genericPoint
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIntegral Y] [LocallyOfFiniteType f] {x x' : X}
    (hy : IsGeometricallyUnibranchAt Y (f x))
    (hxx' : x' ⤳ x) (hx' : f x' = genericPoint Y)
    (hunramified : UnramifiedAt f x) :
    EtaleAt f x := by
  obtain ⟨U, hUaff, hxU, V, hVaff, hVU, hUnram⟩ := hunramified
  have hx'U : x' ∈ U := (specializes_iff_forall_open.mp hxx') U U.2 hxU
  have hfxV : f x ∈ V := hVU hxU
  have hfx'V : f x' ∈ V := hVU hx'U
  let A := Γ(Y, V)
  let B := Γ(X, U)
  let p := (hVaff.primeIdealOf ⟨f x, hfxV⟩).asIdeal
  let q := (hUaff.primeIdealOf ⟨x, hxU⟩).asIdeal
  let q' := (hUaff.primeIdealOf ⟨x', hx'U⟩).asIdeal
  let φ := (f.appLE V U hVU).hom
  have : Nonempty V := ⟨⟨f x, hfxV⟩⟩
  have : IsDomain A := inferInstance
  have : p.IsPrime := (hVaff.primeIdealOf ⟨f x, hfxV⟩).isPrime
  have : q.IsPrime := (hUaff.primeIdealOf ⟨x, hxU⟩).isPrime
  have : q'.IsPrime := (hUaff.primeIdealOf ⟨x', hx'U⟩).isPrime
  let : Algebra A B := φ.toAlgebra
  have : q.LiesOver p :=
    ⟨(congrArg PrimeSpectrum.asIdeal
      (IsAffineOpen.comap_primeIdealOf_appLE V hVaff U hUaff hVU hxU)).symm⟩
  have hq'bot : q'.comap φ = ⊥ := by
    have hp'bot : (hVaff.primeIdealOf ⟨f x', hfx'V⟩).asIdeal = ⊥ := by
      have hpoint : (⟨f x', hfx'V⟩ : V) =
          ⟨genericPoint Y, by simpa [hx'] using hfx'V⟩ := Subtype.ext hx'
      rw [hpoint, hVaff.primeIdealOf_genericPoint]
      simp
    exact (congrArg PrimeSpectrum.asIdeal
      (IsAffineOpen.comap_primeIdealOf_appLE V hVaff U hUaff hVU hx'U)).trans hp'bot
  have hq'leq : q' ≤ q := by
    refine (PrimeSpectrum.asIdeal_le_asIdeal _ _).2 ?_
    rw [PrimeSpectrum.le_iff_specializes]
    refine hUaff.fromSpec.isOpenEmbedding.isInducing.specializes_iff.mp ?_
    rw [hUaff.fromSpec_primeIdealOf, hUaff.fromSpec_primeIdealOf]
    exact hxx'
  have hgeom : _root_.IsGeometricallyUnibranch (Localization.AtPrime p) := by
    let : Algebra A (Y.presheaf.stalk (f x)) :=
      Y.presheaf.algebra_section_stalk ⟨f x, hfxV⟩
    let : IsLocalization.AtPrime (Y.presheaf.stalk (f x)) p :=
      hVaff.isLocalization_stalk ⟨f x, hfxV⟩
    let e : Y.presheaf.stalk (f x) ≃+* Localization.AtPrime p :=
      (IsLocalization.algEquiv p.primeCompl (Y.presheaf.stalk (f x))
        (Localization.AtPrime p)).toRingEquiv
    exact (isGeometricallyUnibranch_iff_isGeometricallyUnibranchRing _).mpr
      (isGeometricallyUnibranchRing_of_ringEquiv e hy)
  let : Algebra.Unramified A B := hUnram
  have hqUnram : ∃ g : B, g ∉ q ∧ Algebra.Unramified A (Localization.Away g) := by
    have : Algebra.IsUnramifiedAt A q := by
      simpa [q] using
        (Algebra.unramified_iff_forall (R := A) (A := B)).mp hUnram
          (hUaff.primeIdealOf ⟨x, hxU⟩)
    exact Algebra.exists_unramified_of_isUnramifiedAt (R := A) q
  have hinj : let := Localization.AtPrime.algebraOfLiesOver p q
      Function.Injective
        (algebraMap (Localization.AtPrime p) (Localization.AtPrime q)) := by
    let := Localization.AtPrime.algebraOfLiesOver p q
    refine IsLocalization.injective_of_map_algebraMap_zero (M := p.primeCompl) _ _ fun a ha ↦ ?_
    have hEq : algebraMap B (Localization.AtPrime q) (φ a) =
        algebraMap (Localization.AtPrime p) (Localization.AtPrime q)
          (algebraMap A (Localization.AtPrime p) a) := by
      calc
        algebraMap B (Localization.AtPrime q) (φ a) =
            algebraMap B (Localization.AtPrime q) (algebraMap A B a) := by
              simp [RingHom.algebraMap_toAlgebra]
        _ = algebraMap A (Localization.AtPrime q) a :=
          (IsScalarTower.algebraMap_apply A B (Localization.AtPrime q) a).symm
        _ = _ :=
          IsScalarTower.algebraMap_apply A (Localization.AtPrime p) (Localization.AtPrime q) a
    have haq : algebraMap B (Localization.AtPrime q) (φ a) =
        algebraMap B (Localization.AtPrime q) 0 := by simpa using hEq.trans ha
    obtain ⟨⟨t, htq⟩, hmul⟩ :=
      (IsLocalization.eq_iff_exists q.primeCompl (Localization.AtPrime q)).mp haq
    have hmul' : t * φ a ∈ q' := by simp [hmul]
    have ha' : φ a ∈ q' :=
      (‹q'.IsPrime›.mem_or_mem hmul').resolve_left fun ht ↦ htq (hq'leq ht)
    have ha0 : a = 0 := by simpa [hq'bot] using show a ∈ q'.comap φ from ha'
    simp [ha0]
  obtain ⟨g, hgq, hEtaleAway⟩ :=
    exists_etale_away_of_isGeometricallyUnibranch_of_isUnramifiedAt p q hgeom hqUnram hinj
  let U' : X.Opens := X.basicOpen g
  have hU'aff : IsAffineOpen U' := hUaff.basicOpen g
  have hxU' : x ∈ U' := by
    rw [Scheme.mem_basicOpen X g x hxU]
    refine IsLocalRing.notMem_maximalIdeal.mp fun hmax ↦ hgq ?_
    show g ∈ (hUaff.primeIdealOf ⟨x, hxU⟩).asIdeal
    rwa [hUaff.primeIdealOf_eq_map_closedPoint]
  have hU'V : U' ≤ f ⁻¹ᵁ V := (X.basicOpen_le g).trans hVU
  let : IsLocalization.Away g Γ(X, U') := hUaff.isLocalization_basicOpen g
  let : Algebra B Γ(X, U') :=
    (X.presheaf.map (homOfLE (X.basicOpen_le g)).op).hom.toAlgebra
  let : Algebra A Γ(X, U') := (f.appLE V U' hU'V).hom.toAlgebra
  have : IsScalarTower A B Γ(X, U') := by
    refine IsScalarTower.of_algebraMap_eq' ?_
    ext a
    show (f.appLE V U' hU'V).hom a =
      ((X.presheaf.map (homOfLE (X.basicOpen_le g)).op).hom) ((f.appLE V U hVU).hom a)
    exact (congrArg (fun k : Γ(Y, V) ⟶ Γ(X, U') ↦ k.hom a)
      (f.appLE_map hVU (homOfLE (X.basicOpen_le g)).op)).symm
  let : Algebra.Etale A (Localization.Away g) := hEtaleAway
  have hEtale : (f.appLE V U' hU'V).hom.Etale :=
    Algebra.Etale.of_equiv
      ((IsLocalization.algEquiv (Submonoid.powers g) (Localization.Away g)
        Γ(X, U')).restrictScalars A)
  exact ⟨U', hU'aff, hxU', V, hVaff, hU'V, hEtale⟩

end AlgebraicGeometry

end
