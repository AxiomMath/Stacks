module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.KeyFormulaLocal.ClosedImmersionStalk
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.KeyFormulaLocal.HeightOnePoints
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.KeyFormulaLocal.PrimeDivisorChart
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The local ring of `W ×_X Z` at a point over a codimension-two point

Let `X` be a decent algebraic space, `Z ⊂ X` a prime divisor with generic point `ξ`, `W` an étale
scheme chart of `X`, `u` a point of its scheme lying over a point of `|Z|`, and `y` a point of
the chart `W ×_X Z` of `Z` over `u` (`AlgebraicGeometry.Space.PrimeDivisor.baseChangeChart`).
Write `A = 𝒪_{W, u}` and `π : W ×_X Z → W` for the projection, a closed immersion. The third step
of the proof of Stacks 0EQV uses that

* the stalk map `A → 𝒪_{W ×_X Z, y}` is surjective, with kernel `I_Z`;
* the minimal primes of `𝒪_{W ×_X Z, y}` correspond, by pulling back, exactly to the primes `𝔮`
  of `A` whose point of `W` lies over `ξ` — these are height-one primes of `A`;
* `I_Z` is the intersection of those primes, so `𝒪_{W ×_X Z, y} = A ⧸ I_Z`.

So the order of vanishing along a closed subspace of `Z` computed on the chart `W ×_X Z` as a sum
over the minimal primes of its local ring is a sum over the height-one primes of `A` over `ξ`.

The minimal primes of `𝒪_{W ×_X Z, y}` are the points of `W ×_X Z` of coheight zero which
generalize `y`; a point of a chart of `Z` has coheight the codimension of the closure of its
image in `|Z|` (`AlgebraicGeometry.Space.coheight_eq_codimension_chartSchemeToPoints`), which is
zero exactly at the generic point of the irreducible space `|Z|`.

## Main results

* `TopologicalSpace.codimension_closureSingleton_eq_zero_iff`: in an irreducible sober space the
  closure of a point has codimension zero exactly when the point is generic.
* `AlgebraicGeometry.Space.PrimeDivisor.image_comap_minimalPrimes_stalk_baseChangeChart`: the
  pullbacks of the minimal primes of `𝒪_{W ×_X Z, y}` are the primes of `A` over `ξ`.
* `AlgebraicGeometry.Space.PrimeDivisor.minimalPrimesStalkBaseChangeChartEquiv`: the
  corresponding bijection.
* `AlgebraicGeometry.Space.PrimeDivisor.ker_stalkMap_baseChangeChartProj_eq_sInf`: `I_Z` is the
  intersection of the primes of `A` over `ξ`.
* `AlgebraicGeometry.Space.PrimeDivisor.height_eq_one_of_fromSpecStalk_eq_genericPoint`: such a
  prime has height one.

## References

* [Stacks Project, Tag 0EQV](https://stacks.math.columbia.edu/tag/0EQV)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

open TopologicalSpace.IrreducibleCloseds (closureSingleton coe_closureSingleton)

universe u

namespace TopologicalSpace

/-- **In an irreducible quasi-sober `T₀` space the closure of a point has codimension zero
exactly when the point is the generic point.** -/
@[ega "0 14.2.2" "(iv), special case"]
theorem codimension_closureSingleton_eq_zero_iff {A : Type*} [TopologicalSpace A] [T0Space A]
    [QuasiSober A] [IrreducibleSpace A] (z : A) :
    codimension (closureSingleton z) = 0 ↔ z = genericPoint A := by
  rw [codimension_eq_coheight, Order.coheight_eq_zero]
  have hg : closure ({genericPoint A} : Set A) = Set.univ := genericPoint_spec A
  have hle (b : IrreducibleCloseds A) : b ≤ closureSingleton (genericPoint A) := by
    show (b : Set A) ⊆ closure ({genericPoint A} : Set A)
    exact hg ▸ Set.subset_univ _
  constructor
  · intro h
    have hge := h (hle _)
    change closure ({genericPoint A} : Set A) ⊆ closure ({z} : Set A) at hge
    exact ((specializes_iff_mem_closure.mpr (hge (subset_closure rfl))).antisymm
      (specializes_iff_mem_closure.mpr (hg ▸ Set.mem_univ z))).eq
  · rintro rfl b _
    exact hle b

end TopologicalSpace

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
variable {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (Z : PrimeDivisor B S hS X)

include hX in
/-- The generic point of `|Z|`, as a point of `Z`, maps to the generic point of the prime
divisor. -/
theorem PrimeDivisor.pointsMap_genericPoint_toIntegralClosedSubspace :
    pointsMap B S hS Z.subspace.toFunctor Z.subspace.ι
        ((Z.toIntegralClosedSubspace B S hS).genericPoint B S hS) =
      Z.genericPoint B S hS X :=
  (eq_pointsMap_genericPoint_of_isGenericPoint B S hS hX (Z.toIntegralClosedSubspace B S hS)
    (Z.genericPoint B S hS X) (Z.isGenericPoint_genericPoint B S hS X)).symm

/-- **A point of `W ×_X Z` has coheight zero exactly when it lies over the generic point of
`|Z|`.** -/
theorem PrimeDivisor.coheight_eq_zero_iff_baseChangeChart (W : SmallEtale B S hS X)
    (y : chartScheme (Z.baseChangeChart B S hS hX W)) :
    Order.coheight y = 0 ↔
      chartSchemeToPoints B S hS Z.subspace.toFunctor (Z.baseChangeChart B S hS hX W) y =
        (Z.toIntegralClosedSubspace B S hS).genericPoint B S hS := by
  have : QuasiSober (points B S hS Z.subspace.toFunctor) :=
    (Z.toIntegralClosedSubspace B S hS).quasiSober_points B S hS
  have : IrreducibleSpace (points B S hS Z.subspace.toFunctor) :=
    (Z.toIntegralClosedSubspace B S hS).irreducibleSpace_points B S hS
  have : T0Space (points B S hS Z.subspace.toFunctor) :=
    (Z.toIntegralClosedSubspace B S hS).t0Space_points B S hS
  rw [coheight_eq_codimension_chartSchemeToPoints B S hS Z.closed.1 Z.integral.2.1]
  exact codimension_closureSingleton_eq_zero_iff _

/-- A point of `W ×_X Z` has coheight zero exactly when its image in `W` lies over the generic
point of `Z`. -/
private theorem PrimeDivisor.coheight_eq_zero_iff_chartSchemeToPoints_baseChangeChartProj
    (W : SmallEtale B S hS X) (y : chartScheme (Z.baseChangeChart B S hS hX W)) :
    Order.coheight y = 0 ↔
      chartSchemeToPoints B S hS X W (Z.baseChangeChartProj B S hS hX W y) =
        Z.genericPoint B S hS X := by
  rw [Z.coheight_eq_zero_iff_baseChangeChart B S hS hX W,
    Z.chartSchemeToPoints_baseChangeChartProj B S hS hX W,
    ← Z.pointsMap_genericPoint_toIntegralClosedSubspace B S hS hX]
  exact ((Z.toIntegralClosedSubspace B S hS).isClosedEmbedding_pointsMap B S hS hX).injective
    |>.eq_iff.symm

/-- **The pullbacks of the minimal primes of the local ring of `W ×_X Z` are the primes of
`A = 𝒪_{W, u}` over the generic point of `Z`.** For a point `y` of `W ×_X Z` with image `u` in
`W`, pulling back along the (surjective) stalk map `A → 𝒪_{W ×_X Z, y}` carries the minimal
primes of `𝒪_{W ×_X Z, y}` onto the primes `𝔮` of `A` whose point of `W` maps to the generic
point of `Z` in `|X|`. -/
theorem PrimeDivisor.image_comap_minimalPrimes_stalk_baseChangeChart (W : SmallEtale B S hS X)
    (y : chartScheme (Z.baseChangeChart B S hS hX W)) :
    Ideal.comap ((Z.baseChangeChartProj B S hS hX W).stalkMap y).hom ''
        minimalPrimes ((chartScheme (Z.baseChangeChart B S hS hX W)).presheaf.stalk y) =
      {𝔮 : Ideal ((chartScheme W).presheaf.stalk (Z.baseChangeChartProj B S hS hX W y)) |
        ∃ h : 𝔮.IsPrime, chartSchemeToPoints B S hS X W
          ((chartScheme W).fromSpecStalk (Z.baseChangeChartProj B S hS hX W y) ⟨𝔮, h⟩) =
            Z.genericPoint B S hS X} := by
  have := Z.isClosedImmersion_baseChangeChartProj B S hS hX W
  set π := Z.baseChangeChartProj B S hS hX W
  ext 𝔮
  constructor
  · rintro ⟨𝔭, h𝔭, rfl⟩
    have : 𝔭.IsPrime := h𝔭.1.1
    refine ⟨Ideal.comap_isPrime _ _, ?_⟩
    refine (congrArg (chartSchemeToPoints B S hS X W)
      (Scheme.Hom.fromSpecStalk_comap_stalkMap π y ⟨𝔭, inferInstance⟩)).trans ?_
    exact (Z.coheight_eq_zero_iff_chartSchemeToPoints_baseChangeChartProj B S hS hX W _).mp
      ((Stacks.Chow.coheight_fromSpecStalk_eq_height y _).trans (Ideal.height_eq_zero_iff.mpr h𝔭))
  · rintro ⟨h𝔮, hq⟩
    set q := (chartScheme W).fromSpecStalk (π y) ⟨𝔮, h𝔮⟩
    have hqZ : chartSchemeToPoints B S hS X W q ∈ Z.support B S hS X :=
      hq ▸ (Z.isGenericPoint_genericPoint B S hS X).mem
    obtain ⟨y', hy'⟩ := Z.exists_baseChangeChartProj_eq B S hS hX W q hqZ
    have hy'y : y' ⤳ y := by
      rw [← π.isClosedEmbedding.isInducing.specializes_iff, hy']
      exact Stacks.Chow.specializes_fromSpecStalk (π y) ⟨𝔮, h𝔮⟩
    obtain ⟨P, hP⟩ := Stacks.Chow.exists_fromSpecStalk_eq hy'y
    have hcoh0 : Order.coheight y' = 0 :=
      (Z.coheight_eq_zero_iff_chartSchemeToPoints_baseChangeChartProj B S hS hX W y').mpr
        (by rwa [hy'])
    have hmin : P.asIdeal ∈ minimalPrimes
        ((chartScheme (Z.baseChangeChart B S hS hX W)).presheaf.stalk y) := by
      have := P.isPrime
      exact Ideal.height_eq_zero_iff.mp
        ((Stacks.Chow.coheight_fromSpecStalk_eq_height y P).symm.trans (hP ▸ hcoh0))
    refine ⟨P.asIdeal, hmin, ?_⟩
    have heq : (chartScheme W).fromSpecStalk (π y) (PrimeSpectrum.comap (π.stalkMap y).hom P) =
        (chartScheme W).fromSpecStalk (π y) ⟨𝔮, h𝔮⟩ :=
      (Scheme.Hom.fromSpecStalk_comap_stalkMap π y P).trans (by rw [hP, hy'])
    exact congrArg PrimeSpectrum.asIdeal
      (((chartScheme W).fromSpecStalk (π y)).isEmbedding.injective heq)

/-- **The minimal primes of the local ring of `W ×_X Z` are the primes of `A = 𝒪_{W, u}` over the
generic point of `Z`**, as a bijection given by pulling back along the stalk map. -/
def PrimeDivisor.minimalPrimesStalkBaseChangeChartEquiv (W : SmallEtale B S hS X)
    (y : chartScheme (Z.baseChangeChart B S hS hX W)) :
    minimalPrimes ((chartScheme (Z.baseChangeChart B S hS hX W)).presheaf.stalk y) ≃
      {𝔮 : Ideal ((chartScheme W).presheaf.stalk (Z.baseChangeChartProj B S hS hX W y)) //
        ∃ h : 𝔮.IsPrime, chartSchemeToPoints B S hS X W
          ((chartScheme W).fromSpecStalk (Z.baseChangeChartProj B S hS hX W y) ⟨𝔮, h⟩) =
            Z.genericPoint B S hS X} :=
  haveI := Z.isClosedImmersion_baseChangeChartProj B S hS hX W
  Equiv.ofBijective
    (fun 𝔭 => ⟨Ideal.comap ((Z.baseChangeChartProj B S hS hX W).stalkMap y).hom 𝔭.1,
      (Z.image_comap_minimalPrimes_stalk_baseChangeChart B S hS hX W y).subset ⟨𝔭.1, 𝔭.2, rfl⟩⟩)
    ⟨fun 𝔭 𝔭' h => Subtype.ext (Ideal.comap_injective_of_surjective _
        ((Z.baseChangeChartProj B S hS hX W).stalkMap_surjective y) (congrArg Subtype.val h)),
      fun 𝔮 => by
        obtain ⟨𝔭, h𝔭, h'⟩ :=
          (Z.image_comap_minimalPrimes_stalk_baseChangeChart B S hS hX W y).superset 𝔮.2
        exact ⟨⟨𝔭, h𝔭⟩, Subtype.ext h'⟩⟩

/-- The bijection `AlgebraicGeometry.Space.PrimeDivisor.minimalPrimesStalkBaseChangeChartEquiv`
is pulling back along the stalk map. -/
theorem PrimeDivisor.coe_minimalPrimesStalkBaseChangeChartEquiv (W : SmallEtale B S hS X)
    (y : chartScheme (Z.baseChangeChart B S hS hX W))
    (𝔭 : minimalPrimes ((chartScheme (Z.baseChangeChart B S hS hX W)).presheaf.stalk y)) :
    (Z.minimalPrimesStalkBaseChangeChartEquiv B S hS hX W y 𝔭 : Ideal _) =
      Ideal.comap ((Z.baseChangeChartProj B S hS hX W).stalkMap y).hom 𝔭 :=
  rfl

/-- **The kernel `I_Z` of the stalk map `A → 𝒪_{W ×_X Z, y}` is the intersection of the primes
of `A` over the generic point of `Z`.** -/
theorem PrimeDivisor.ker_stalkMap_baseChangeChartProj_eq_sInf (W : SmallEtale B S hS X)
    (y : chartScheme (Z.baseChangeChart B S hS hX W)) :
    RingHom.ker ((Z.baseChangeChartProj B S hS hX W).stalkMap y).hom =
      sInf {𝔮 : Ideal ((chartScheme W).presheaf.stalk (Z.baseChangeChartProj B S hS hX W y)) |
        ∃ h : 𝔮.IsPrime, chartSchemeToPoints B S hS X W
          ((chartScheme W).fromSpecStalk (Z.baseChangeChartProj B S hS hX W y) ⟨𝔮, h⟩) =
            Z.genericPoint B S hS X} := by
  have := Z.isClosedImmersion_baseChangeChartProj B S hS hX W
  have := Z.isReduced_chartScheme_baseChangeChart B S hS hX W
  rw [← Z.image_comap_minimalPrimes_stalk_baseChangeChart B S hS hX W y,
    ← Ideal.comap_minimalPrimes_eq_of_surjective
      ((Z.baseChangeChartProj B S hS hX W).stalkMap_surjective y),
    ← RingHom.ker_eq_comap_bot, Ideal.sInf_minimalPrimes,
    (Scheme.Hom.isRadical_ker_stalkMap_of_isClosedImmersion _ y).radical]

variable (hdec : IsDecentSpace B S hS X)

include hX hdec in
/-- **A prime of a chart local ring over the generic point of a prime divisor has height one.** -/
theorem PrimeDivisor.height_eq_one_of_fromSpecStalk_eq_genericPoint (W : SmallEtale B S hS X)
    (u : chartScheme W) (𝔮 : Ideal ((chartScheme W).presheaf.stalk u)) [𝔮.IsPrime]
    (h : chartSchemeToPoints B S hS X W ((chartScheme W).fromSpecStalk u ⟨𝔮, inferInstance⟩) =
      Z.genericPoint B S hS X) :
    𝔮.height = 1 := by
  refine (Stacks.Chow.coheight_fromSpecStalk_eq_height u ⟨𝔮, inferInstance⟩).symm.trans ?_
  rw [coheight_eq_codimension_chartSchemeToPoints B S hS hX hdec, h]
  exact Z.codimension_genericPoint B S hS X

end AlgebraicGeometry.Space

end
