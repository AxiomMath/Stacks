module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Curves.ClassicalLinearSystem
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.Normal
public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartierWeilDivisor
public import StacksFrontier.AlgebraicGeometry.Divisors.WeilDivisorClass.CanonicalSectionOrder
public import StacksFrontier.AlgebraicGeometry.Divisors.WeilDivisorClass.FirstChernClass
public import StacksFrontier.AlgebraicGeometry.Divisors.WeilDivisorClass.FirstChernClassInjective
public import StacksFrontier.AlgebraicGeometry.Divisors.WeilDivisorClass.GenericPoint
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.Defs
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Projective

/-!
# Linear equivalence through the Weil divisor class group

Let `X` be a smooth projective curve over an algebraically closed field `k`. Two effective
Cartier divisors `D, D' ⊆ X` are linearly equivalent, `𝒪_X(D) ≅ 𝒪_X(D')`, exactly when the Weil
divisors `[D]` and `[D']` associated to them have the same class in `Cl(X)`.

The source deduces this from `Pic(X) = Cl(X)` ([Stacks, Tag 0BE9]). The two ingredients are that
the first Chern class `Pic(X) → Cl(X)` is injective on a normal scheme ([Stacks, Tag 0BE8], the
half of Tag 0BE9 that is used), and that it sends the class of `𝒪_X(D)` to the class of `[D]`:
the canonical section `1_D` of `𝒪_X(D)` vanishes along a prime divisor `Z` to the order of the
local equation of `D` at the generic point of `Z`, which is the multiplicity of `Z` in `[D]`.

## Main results

* `AlgebraicGeometry.weilDivisorClassOfInvertibleSheaf_modulesInvertibleSheaf`: the Weil divisor
  class of `𝒪_X(D)` is the class of the Weil divisor `[D]`, on any Noetherian integral scheme.
* `Stacks.Divisors.linearlyEquivalent_iff_weilDivisorClass_eq_of_isNormal`: on a normal
  Noetherian integral scheme, `D` and `D'` are linearly equivalent exactly when `[D]` and `[D']`
  have the same class in `Cl(X)`.
* `Stacks.Divisors.linearlyEquivalent_iff_weilDivisorClass_eq`: the same for a smooth projective
  curve over an algebraically closed field, the setting of [Stacks, Tag 0CCT].

## Implementation notes

The Weil divisor of an effective Cartier divisor is `AlgebraicGeometry.effectiveCartierWeilDivisor`
([Stacks, Tag 02AR]), whose coefficient at a prime divisor is the length of the quotient of the
local ring at its generic point by the local equation, and the order of vanishing in
`AlgebraicGeometry.weilDivisorClassOfInvertibleSheaf_eq_of_forall_ord` is Mathlib's
`AlgebraicGeometry.Scheme.ord`; the two agree because `Scheme.ord` is defined through
`Ring.ordMonoidWithZeroHom`, which is that length.

## References

* [Stacks Project, Tag 0CCT](https://stacks.math.columbia.edu/tag/0CCT)
* [Stacks Project, Tag 0BE9](https://stacks.math.columbia.edu/tag/0BE9)
* [Stacks Project, Tag 0BE8](https://stacks.math.columbia.edu/tag/0BE8)
* [Stacks Project, Tag 02AR](https://stacks.math.columbia.edu/tag/02AR)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry

variable {X : Scheme.{u}}

/-- The order of vanishing along a prime divisor of a local equation of an effective Cartier
divisor is the length of the quotient of the local ring by it. -/
theorem ord_algebraMap_eq_length_quotient [IsLocallyNoetherian X] [IsIntegral X]
    (Z : PrimeDivisor X) {c : X.presheaf.stalk Z.genericPoint}
    (hc : c ∈ nonZeroDivisors (X.presheaf.stalk Z.genericPoint)) :
    X.ord (algebraMap (X.presheaf.stalk Z.genericPoint) X.functionField c) Z.genericPoint =
      ((Module.length (X.presheaf.stalk Z.genericPoint)
        ((X.presheaf.stalk Z.genericPoint) ⧸ Ideal.span {c})).toNat : ℤ) := by
  have hz : Order.coheight Z.genericPoint = 1 := PrimeDivisor.coheight_genericPoint Z
  have : Ring.KrullDimLE 1 (X.presheaf.stalk Z.genericPoint) :=
    krullDimLE_of_coheight_le hz.le
  have hc0 : c ≠ 0 := nonZeroDivisors.ne_zero hc
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp (Ring.ord_ne_top hc)
  have hne : algebraMap (X.presheaf.stalk Z.genericPoint) X.functionField c ≠ 0 := by
    rwa [ne_eq, map_eq_zero_iff _ (IsFractionRing.injective _ _)]
  rw [Scheme.ord_eq_iff hz hne]
  change Ring.ordFrac _ _ = _
  rw [Ring.ordFrac_eq_ord _ hc0, Ring.ordMonoidWithZeroHom_eq_coe _ hc hn.symm]
  have hlen : (Module.length (X.presheaf.stalk Z.genericPoint)
      ((X.presheaf.stalk Z.genericPoint) ⧸ Ideal.span {c})).toNat = n := by
    change (Ring.ord (X.presheaf.stalk Z.genericPoint) c).toNat = n
    rw [← hn, ENat.toNat_natCast]
  rw [hlen]

/-- **The Weil divisor class of `𝒪_X(D)` is the class of `[D]`.** On a Noetherian integral
scheme the first Chern class of the invertible module of an effective Cartier divisor `D` is the
class in `Cl(X)` of the Weil divisor `[D]` associated to `D`. -/
theorem weilDivisorClassOfInvertibleSheaf_modulesInvertibleSheaf [IsNoetherian X] [IsIntegral X]
    (D : X.IdealSheafData) [hD : Stacks.Divisors.IsEffectiveCartierDivisor D] :
    weilDivisorClassOfInvertibleSheaf X (Stacks.Divisors.modulesInvertibleSheaf D) =
      (effectiveCartierWeilDivisor D hD : weilDivisorClassGroup X) := by
  refine weilDivisorClassOfInvertibleSheaf_eq_of_forall_ord D _ fun Z c hc => ?_
  obtain ⟨g, hg, hgreg⟩ := exists_stalk_eq_span_of_isEffectiveCartierDivisor hD Z.genericPoint
  have hassoc : Associated c g := by
    rw [← Ideal.span_singleton_eq_span_singleton, ← hc, hg]
  have hcreg : c ∈ nonZeroDivisors (X.presheaf.stalk Z.genericPoint) := by
    obtain ⟨u, rfl⟩ := hassoc.symm
    exact mul_mem_nonZeroDivisors.mpr ⟨hgreg, u.isUnit.mem_nonZeroDivisors⟩
  rw [effectiveCartierWeilDivisor_apply_of_stalk_eq_span D hD Z c hc,
    ord_algebraMap_eq_length_quotient Z hcreg]

/-- A variety over a field is a Noetherian scheme: it is quasi-compact and locally of finite type
over a Noetherian base. -/
theorem isNoetherian_of_isVariety (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    [IsVariety k f] : IsNoetherian X := by
  have : CompactSpace X := (quasiCompact_iff_compactSpace f).mp inferInstance
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  exact ⟨⟩

end AlgebraicGeometry

namespace Stacks.Divisors

/-- The abelian group structure of the Picard group of a scheme, at the spelling of the structure
sheaf that `AlgebraicGeometry.picardToWeilDivisorClassGroup` is written over. -/
noncomputable local instance picardGroupAddCommGroup (X : Scheme.{u}) :
    AddCommGroup (Stacks.SheafOfModules.PicardGroup X.sheaf.obj X.ringCatSheaf.property) :=
  Stacks.SheafOfModules.instAddCommGroupPicardGroup X.sheaf.obj X.ringCatSheaf.property

/-- **Linear equivalence is equality of Weil divisor classes**, on a normal Noetherian integral
scheme: two effective Cartier divisors `D, D'` satisfy `𝒪_X(D) ≅ 𝒪_X(D')` exactly when the Weil
divisors `[D]` and `[D']` define the same element of `Cl(X)`. -/
theorem linearlyEquivalent_iff_weilDivisorClass_eq_of_isNormal {X : Scheme.{u}} [IsNoetherian X]
    [IsIntegral X] [IsNormal X] (D D' : X.IdealSheafData) [hD : IsEffectiveCartierDivisor D]
    [hD' : IsEffectiveCartierDivisor D'] :
    LinearlyEquivalent D D' ↔
      (effectiveCartierWeilDivisor D hD : weilDivisorClassGroup X) =
        (effectiveCartierWeilDivisor D' hD' : weilDivisorClassGroup X) := by
  rw [← weilDivisorClassOfInvertibleSheaf_modulesInvertibleSheaf D,
    ← weilDivisorClassOfInvertibleSheaf_modulesInvertibleSheaf D']
  refine ⟨fun ⟨e⟩ => weilDivisorClassOfInvertibleSheaf_congr _ _ e, fun h => ?_⟩
  have h' := (weilDivisorClassOfPicardClass_picardClass X (modulesInvertibleSheaf D)).trans
    (h.trans (weilDivisorClassOfPicardClass_picardClass X (modulesInvertibleSheaf D')).symm)
  exact (Stacks.SheafOfModules.picardClass_eq_iff X.sheaf.obj X.ringCatSheaf.property _ _
    (isTensorInvertible_invertibleSheaf D) (isTensorInvertible_invertibleSheaf D')).mp
    (picardToWeilDivisorClassGroup_injective X h')

/-- **Stacks Project, Tag 0CCT.** Let `X` be a smooth projective curve over an algebraically
closed field `k`. Two effective Cartier divisors `D, D' ⊆ X` are linearly equivalent exactly
when the Weil divisors `[D]` and `[D']` associated to them define the same element of the Weil
divisor class group `Cl(X)`. -/
@[stacks 0CCT "D and D' are linearly equivalent iff their Weil divisors have the same class \
in Cl(X)"]
theorem linearlyEquivalent_iff_weilDivisorClass_eq (k : Type u) [Field k] [IsAlgClosed k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsCurve k f] [IsProjectiveVariety k f] [Smooth f]
    (D D' : X.IdealSheafData) [hD : IsEffectiveCartierDivisor D]
    [hD' : IsEffectiveCartierDivisor D'] :
    haveI : IsNoetherian X := isNoetherian_of_isVariety k f
    haveI : IsIntegral X := (inferInstance : IsVariety k f).toIsIntegral
    LinearlyEquivalent D D' ↔
      (effectiveCartierWeilDivisor D hD : weilDivisorClassGroup X) =
        (effectiveCartierWeilDivisor D' hD' : weilDivisorClassGroup X) := by
  have : IsNormal (Spec (.of k)) :=
    isNormal_spec_of_isNormalRing (IsNormalRing.of_isIntegrallyClosed k)
  have : IsNormal X := isNormal_of_smooth f
  have : IsNoetherian X := isNoetherian_of_isVariety k f
  have : IsIntegral X := (inferInstance : IsVariety k f).toIsIntegral
  exact linearlyEquivalent_iff_weilDivisorClass_eq_of_isNormal D D'

end Stacks.Divisors

end
