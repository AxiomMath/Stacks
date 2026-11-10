module

public import StacksFrontier.AlgebraicGeometry.Intersection.TorFormula.CycleIntersectionProduct
public import StacksFrontier.AlgebraicGeometry.Intersection.TorFormula.DivisorFibreCycle
public import StacksFrontier.AlgebraicGeometry.Intersection.TorFormulaMultiplicities.TransversalSubschemes

/-!
# The coefficient of a transversal component of an intersection product

Let `X` be a nonsingular variety, let `W`, `V ⊆ X` be closed subvarieties, and let `T` be an
irreducible component of `W ∩ V` with generic point `ξ`. The intersection product `W · V` of
Section 43.14 is the alternating sum `∑ᵢ (-1)ⁱ [Torᵢ^{𝒪_X}(𝒪_W, 𝒪_V)]_k` of the cycles of the
`Tor` sheaves, and the coefficient of a cycle of a coherent sheaf at a point is the length of the
stalk there. So the coefficient of `[T]` in `W · V` is

`∑ᵢ (-1)ⁱ length_{𝒪_{X, ξ}} Torᵢ^{𝒪_{X, ξ}}(𝒪_{X, ξ} ⧸ I, 𝒪_{X, ξ} ⧸ J)`,

with `I` and `J` the ideals of `W` and `V` in `A = 𝒪_{X, ξ}`: the stalk of a `Tor` sheaf is the
`Tor` module of the stalks, and the stalk of the structure sheaf of a closed subscheme is the
quotient of `A` by the ideal of that subscheme. That alternating sum is exactly the Tor-formula
intersection multiplicity `Ideal.localIntersectionMultiplicity` of the pair `(I, A ⧸ J)`, so the
coefficient of `[T]` in `W · V` is a purely local invariant of the two ideals of `A`.

When the intersection is transversal along `T` — when `A ⧸ (I ⊔ J)` is the residue field and the
intersection is proper — that local multiplicity is `1`, so `[T]` occurs in `W · V` with
coefficient one.

Only finitely many terms of the alternating sum are nonzero: on a scheme of dimension at most `d`
all of whose local rings are regular the `Tor` sheaves vanish above degree `d`, which bounds the
sum by `d` and simultaneously makes the unbounded alternating sum defining the local
multiplicity converge.

## Main results

* `AlgebraicGeometry.TorFormula.sheafMultiplicity_torSheaf_structureSheafAt` — the multiplicity
  of `Torᵢ^{𝒪_X}(𝒪_W, 𝒪_V)` at a point of both subvarieties is the length of
  `Torᵢ^{𝒪_{X, ξ}}(𝒪_{X, ξ} ⧸ I, 𝒪_{X, ξ} ⧸ J)`.
* `AlgebraicGeometry.TorFormula.torSubvarietyProductOfBound_apply_eq_localIntersectionMultiplicity`
  — the coefficient of `W · V` at a point is the Tor-formula local intersection multiplicity of
  the two local ideals there.
* `AlgebraicGeometry.TorFormula.torSubvarietyProductOfBound_apply_eq_one` — along a component of
  a transversal proper intersection that coefficient is one.
* `AlgebraicGeometry.TorFormula.torSubvarietyProductOfBound_apply_eq_zero_of_notMem_inter` and
  `AlgebraicGeometry.TorFormula.torFormulaSubvarietyProductTotal_apply_eq_zero_of_notMem_inter`
  — off the intersection the product has no coefficients.
* `AlgebraicGeometry.TorFormula.torSubvarietyProductOfBound_apply_eq_zero_of_relativeDimension_ne`
  — away from the expected delta-dimension the product has no coefficients either.
* `AlgebraicGeometry.TorFormula.torFormulaCycleIntersectionProduct_apply_eq_one` — the
  coefficient-one statement for the intersection product of the two prime cycles `[W] · [V]`.
* `AlgebraicGeometry.TorFormula.torFormulaCycleIntersectionProduct_apply_eq_mul` — for two
  cycles, a component of a transversal proper intersection lying on no other pair of components
  occurs in the product with the product of the two coefficients.

## Implementation notes

Closed subvarieties are indexed by their generic points, as cycles are, and the structure sheaf
of the reduced closure of a point `x` is `AlgebraicGeometry.TorFormula.structureSheafAt x`, which
is the structure sheaf of the closed subscheme cut out by the vanishing ideal of `closure {x}`.
Its local ideal at a point `z` of that closure is `IdealSheafData.stalk (integralComponentAt x) z`
and the four ideals of the local statement at the generic point of `T` are read off from these.

Each product `W · V` is formed from the delta-dimension bound of Section 43.14 for its own pair of
points, `AlgebraicGeometry.TorFormula.TorSupportBound`, as
`AlgebraicGeometry.TorFormula.torSubvarietyProductOfBound`: that bound holds for a pair of
properly intersecting subvarieties, but not for every pair of points at once, so nothing here
assumes it for all pairs.

The coefficient of a cycle is an integer whereas the local multiplicity is a rational, the
alternating sum of lengths being formed in `ℚ`; the comparison is therefore stated after the cast
`ℤ → ℚ`, which loses nothing.

## References

* [Stacks Project, Tag 0B1J](https://stacks.math.columbia.edu/tag/0B1J)
* [Stacks Project, Tag 0B1I](https://stacks.math.columbia.edu/tag/0B1I)
* [Stacks Project, Tag 0B08](https://stacks.math.columbia.edu/tag/0B08)
* [Stacks Project, Tag 0AZR](https://stacks.math.columbia.edu/tag/0AZR)
* [Stacks Project, Tag 0AZT](https://stacks.math.columbia.edu/tag/0AZT)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

attribute [local instance 100000] HasDerivedCategory.standard

namespace AlgebraicGeometry.TorFormula

variable {X : Scheme.{u}}

/-! ### The local ideal of a closed subvariety -/

/-- The structure sheaf of the reduced closure of a point is the structure sheaf of the closed
subscheme cut out by the vanishing ideal of that closure. -/
theorem structureSheafAt_eq_subschemeStructureSheaf (x : X) :
    structureSheafAt x = subschemeStructureSheaf (Stacks.Chow.integralComponentAt x) :=
  rfl

/-- The ideal of the reduced closure of a point `x` in the local ring at a point `z`: the stalk
at `z` of the vanishing ideal of `closure {x}`. -/
abbrev localIdealAt (x z : X) : Ideal (X.presheaf.stalk z) :=
  IdealSheafData.stalk (Stacks.Chow.integralComponentAt x) z

/-- A point of the closure of `x` lies in the support of the closed subscheme attached to `x`. -/
theorem mem_support_integralComponentAt {x z : X} (hzx : z ∈ closure ({x} : Set X)) :
    z ∈ (Stacks.Chow.integralComponentAt x).support := by
  rwa [← SetLike.mem_coe, Stacks.Chow.coe_support_integralComponentAt]

/-! ### The multiplicity of a `Tor` sheaf of two closed subvarieties -/

/-- **The multiplicity of `Torᵢ^{𝒪_X}(𝒪_W, 𝒪_V)` at a point of both subvarieties.** For `W` and
`V` the reduced closures of `x` and `y` and `z` a point of both, it is the length of
`Torᵢ^{𝒪_{X, z}}(𝒪_{X, z} ⧸ I, 𝒪_{X, z} ⧸ J)`, with `I` and `J` the local ideals of `W` and `V`
at `z`. -/
theorem sheafMultiplicity_torSheaf_structureSheafAt (x y : X) (i : ℕ) {z : X}
    (hzx : z ∈ closure ({x} : Set X)) (hzy : z ∈ closure ({y} : Set X)) :
    Stacks.Chow.sheafMultiplicity (torSheaf X (structureSheafAt x) (structureSheafAt y) i) z =
      (Module.length (X.presheaf.stalk z)
        (((Tor (ModuleCat.{u} (X.presheaf.stalk z)) i).obj
            (ModuleCat.of (X.presheaf.stalk z)
              (X.presheaf.stalk z ⧸ localIdealAt x z))).obj
          (ModuleCat.of (X.presheaf.stalk z)
            (X.presheaf.stalk z ⧸ localIdealAt y z)))).toNat := by
  rw [structureSheafAt_eq_subschemeStructureSheaf x, structureSheafAt_eq_subschemeStructureSheaf y]
  exact sheafMultiplicity_torSheaf_subschemeStructureSheaf _ _ i z
    (mem_support_integralComponentAt hzx) (mem_support_integralComponentAt hzy)

/-- **The `Tor` modules of the two local rings vanish above the dimension of the ambient
scheme.** On a scheme of dimension at most `d` all of whose local rings are regular, the length
of `Torᵢ^{𝒪_{X, z}}(𝒪_{X, z} ⧸ I, 𝒪_{X, z} ⧸ J)` is zero for `i > d`. -/
theorem length_tor_localIdealAt_toNat_eq_zero_of_lt
    (hreg : ∀ w : X, IsRegularLocalRing (X.presheaf.stalk w)) (x y : X) (d i : ℕ)
    (hd : topologicalKrullDim X ≤ (d : WithBot ℕ∞)) (hdi : d < i) {z : X}
    (hzx : z ∈ closure ({x} : Set X)) (hzy : z ∈ closure ({y} : Set X)) :
    (Module.length (X.presheaf.stalk z)
      (((Tor (ModuleCat.{u} (X.presheaf.stalk z)) i).obj
          (ModuleCat.of (X.presheaf.stalk z)
            (X.presheaf.stalk z ⧸ localIdealAt x z))).obj
        (ModuleCat.of (X.presheaf.stalk z)
          (X.presheaf.stalk z ⧸ localIdealAt y z)))).toNat = 0 := by
  have hzero := isZero_torSheaf_of_lt X hreg (structureSheafAt x) (structureSheafAt y) d i hd hdi
  have hnot : z ∉ SheafOfModules.supp (torSheaf X (structureSheafAt x) (structureSheafAt y) i) :=
    (Scheme.Modules.notMem_supp_iff_isZero_stalk _ z).mpr
      (Functor.map_isZero (Scheme.Modules.stalkFunctor X z) hzero)
  have h := Stacks.Chow.sheafMultiplicity_eq_zero_of_notMem_supp _ hnot
  rw [sheafMultiplicity_torSheaf_structureSheafAt x y i hzx hzy] at h
  exact_mod_cast h

/-! ### The coefficient of the product of two closed subvarieties -/

/-- **The coefficient of `W · V` at a point, as a finite alternating sum** of the multiplicities
of the `Tor` sheaves of the two structure sheaves. The product is formed from the
delta-dimension bound `h` for the one pair of points it is taken at. -/
theorem torSubvarietyProductOfBound_apply (C : Stacks.Chow.ChowSituation.{u}) (f : X ⟶ C.S)
    [LocallyOfFiniteType f] [IsLocallyNoetherian X] (hX : IsRegular X) (k : ℤ) {x y : X}
    (h : TorSupportBound C f hX k x y) (d : ℕ)
    (hd : topologicalKrullDim X ≤ (d : WithBot ℕ∞)) (z : X) :
    torSubvarietyProductOfBound C f hX k h z =
      ∑ i ∈ Finset.range (d + 2), ((-1 : ℤ) ^ i) *
        (haveI := isCoherent_torSheaf_of_isRegular X hX (structureSheafAt x) (structureSheafAt y)
          (isCoherent_structureSheafAt x) (isCoherent_structureSheafAt y) i
         Stacks.Chow.sheafCycleCoeff C f
           (torSheaf X (structureSheafAt x) (structureSheafAt y) i) k z) :=
  intersectionProductCycle_apply C f hX (structureSheafAt x) (structureSheafAt y)
    (isCoherent_structureSheafAt x) (isCoherent_structureSheafAt y) k h
    (fun w => AlgebraicGeometry.IsRegular.isRegularLocalRing_stalk hX w) d hd z

/-- At a point of both subvarieties whose closure has delta-dimension `k`, the summand of the
coefficient of `W · V` indexed by `i` is the length of `Torᵢ` of the two local rings. -/
theorem sheafCycleCoeff_torSheaf_structureSheafAt (C : Stacks.Chow.ChowSituation.{u})
    (f : X ⟶ C.S) [LocallyOfFiniteType f] [IsLocallyNoetherian X] (hX : IsRegular X) (k : ℤ)
    {x y : X} (h : TorSupportBound C f hX k x y) (i : ℕ) {z : X}
    (hz : Stacks.Chow.relativeDimension C.dimensionFunction f z = k)
    (hzx : z ∈ closure ({x} : Set X)) (hzy : z ∈ closure ({y} : Set X)) :
    (haveI := isCoherent_torSheaf_of_isRegular X hX (structureSheafAt x) (structureSheafAt y)
      (isCoherent_structureSheafAt x) (isCoherent_structureSheafAt y) i
     Stacks.Chow.sheafCycleCoeff C f
       (torSheaf X (structureSheafAt x) (structureSheafAt y) i) k z) =
      ((Module.length (X.presheaf.stalk z)
        (((Tor (ModuleCat.{u} (X.presheaf.stalk z)) i).obj
            (ModuleCat.of (X.presheaf.stalk z)
              (X.presheaf.stalk z ⧸ localIdealAt x z))).obj
          (ModuleCat.of (X.presheaf.stalk z)
            (X.presheaf.stalk z ⧸ localIdealAt y z)))).toNat : ℤ) := by
  have := isCoherent_torSheaf_of_isRegular X hX (structureSheafAt x) (structureSheafAt y)
    (isCoherent_structureSheafAt x) (isCoherent_structureSheafAt y) i
  exact (Stacks.Chow.cycleAssociatedToCoherentSheaf_apply_of_relativeDimension_eq
    C f (torSheaf X (structureSheafAt x) (structureSheafAt y) i) k (h i) hz).trans
    (sheafMultiplicity_torSheaf_structureSheafAt x y i hzx hzy)

/-- **The coefficient of `W · V` at a point of both subvarieties whose closure has
delta-dimension `k`** is the finite alternating sum of the lengths of the `Tor` modules of the
two local rings. -/
theorem torSubvarietyProductOfBound_apply_eq_sum_length (C : Stacks.Chow.ChowSituation.{u})
    (f : X ⟶ C.S) [LocallyOfFiniteType f] [IsLocallyNoetherian X] (hX : IsRegular X) (k : ℤ)
    {x y : X} (h : TorSupportBound C f hX k x y) (d : ℕ)
    (hd : topologicalKrullDim X ≤ (d : WithBot ℕ∞)) {z : X}
    (hz : Stacks.Chow.relativeDimension C.dimensionFunction f z = k)
    (hzx : z ∈ closure ({x} : Set X)) (hzy : z ∈ closure ({y} : Set X)) :
    torSubvarietyProductOfBound C f hX k h z =
      ∑ i ∈ Finset.range (d + 2), ((-1 : ℤ) ^ i) *
        ((Module.length (X.presheaf.stalk z)
          (((Tor (ModuleCat.{u} (X.presheaf.stalk z)) i).obj
              (ModuleCat.of (X.presheaf.stalk z)
                (X.presheaf.stalk z ⧸ localIdealAt x z))).obj
            (ModuleCat.of (X.presheaf.stalk z)
              (X.presheaf.stalk z ⧸ localIdealAt y z)))).toNat : ℤ) := by
  rw [torSubvarietyProductOfBound_apply C f hX k h d hd z]
  exact Finset.sum_congr rfl fun i _ => by
    rw [sheafCycleCoeff_torSheaf_structureSheafAt C f hX k h i hz hzx hzy]

/-- **The coefficient of `W · V` at a point is the Tor-formula local intersection multiplicity of
the two local ideals there.** For `W` and `V` the reduced closures of `x` and `y` on a regular
scheme of dimension at most `d`, and `z` a point of both whose closure has delta-dimension `k`,
the coefficient of `W · V` at `z` is `∑ᵢ (-1)ⁱ length Torᵢ^A(A ⧸ I, A ⧸ J)` for `A = 𝒪_{X, z}`
and `I`, `J` the local ideals of `W` and `V`. -/
theorem torSubvarietyProductOfBound_apply_eq_localIntersectionMultiplicity
    (C : Stacks.Chow.ChowSituation.{u}) (f : X ⟶ C.S) [LocallyOfFiniteType f]
    [IsLocallyNoetherian X] (hX : IsRegular X) (k : ℤ) {x y : X}
    (h : TorSupportBound C f hX k x y) (d : ℕ)
    (hd : topologicalKrullDim X ≤ (d : WithBot ℕ∞)) {z : X}
    (hz : Stacks.Chow.relativeDimension C.dimensionFunction f z = k)
    (hzx : z ∈ closure ({x} : Set X)) (hzy : z ∈ closure ({y} : Set X)) :
    ((torSubvarietyProductOfBound C f hX k h z : ℤ) : ℚ) =
      (localIdealAt x z).localIntersectionMultiplicity
        (X.presheaf.stalk z ⧸ localIdealAt y z) := by
  have hreg : ∀ w : X, IsRegularLocalRing (X.presheaf.stalk w) :=
    fun w => AlgebraicGeometry.IsRegular.isRegularLocalRing_stalk hX w
  have htail : ∀ i : ℕ, i ∉ Finset.range (d + 2) →
      (-1 : ℚ) ^ i * ((Module.length (X.presheaf.stalk z)
        (((Tor (ModuleCat.{u} (X.presheaf.stalk z)) i).obj
            (ModuleCat.of (X.presheaf.stalk z)
              (X.presheaf.stalk z ⧸ localIdealAt x z))).obj
          (ModuleCat.of (X.presheaf.stalk z)
            (X.presheaf.stalk z ⧸ localIdealAt y z)))).toNat : ℚ) = 0 := by
    intro i hi
    rw [Finset.mem_range, not_lt] at hi
    rw [length_tor_localIdealAt_toNat_eq_zero_of_lt hreg x y d i hd (by omega) hzx hzy]
    simp
  rw [Ideal.localIntersectionMultiplicity, tsum_eq_sum htail,
    torSubvarietyProductOfBound_apply_eq_sum_length C f hX k h d hd hz hzx hzy]
  push_cast
  rfl

/-- **The product of two closed subvarieties is supported on their intersection.** Off
`W ∩ V` every coefficient of `W · V` vanishes, because every `Tor` sheaf of the two structure
sheaves is supported on that intersection. -/
theorem torSubvarietyProductOfBound_apply_eq_zero_of_notMem_inter
    (C : Stacks.Chow.ChowSituation.{u}) (f : X ⟶ C.S) [LocallyOfFiniteType f]
    [IsLocallyNoetherian X] (hX : IsRegular X) (k : ℤ) {x y : X}
    (h : TorSupportBound C f hX k x y) (d : ℕ)
    (hd : topologicalKrullDim X ≤ (d : WithBot ℕ∞)) {z : X}
    (hz : z ∉ closure ({x} : Set X) ∩ closure ({y} : Set X)) :
    torSubvarietyProductOfBound C f hX k h z = 0 := by
  rw [torSubvarietyProductOfBound_apply C f hX k h d hd z]
  refine Finset.sum_eq_zero fun i _ => ?_
  have := isCoherent_torSheaf_of_isRegular X hX (structureSheafAt x) (structureSheafAt y)
    (isCoherent_structureSheafAt x) (isCoherent_structureSheafAt y) i
  refine mul_eq_zero_of_right _ ?_
  have hnot : z ∉ SheafOfModules.supp (torSheaf X (structureSheafAt x) (structureSheafAt y) i) :=
    fun h => hz (supp_torSheaf_structureSheafAt_subset x y i h)
  simp [Stacks.Chow.sheafCycleCoeff, hnot]

/-- **The product of two closed subvarieties is a cycle in the expected dimension.** At a point
whose closure does not have delta-dimension `k` every coefficient of `W · V` vanishes, because
each cycle `[Torᵢ]_k` in the alternating sum does. -/
theorem torSubvarietyProductOfBound_apply_eq_zero_of_relativeDimension_ne
    (C : Stacks.Chow.ChowSituation.{u}) (f : X ⟶ C.S) [LocallyOfFiniteType f]
    [IsLocallyNoetherian X] (hX : IsRegular X) (k : ℤ) {x y : X}
    (h : TorSupportBound C f hX k x y) (d : ℕ)
    (hd : topologicalKrullDim X ≤ (d : WithBot ℕ∞)) {z : X}
    (hz : Stacks.Chow.relativeDimension C.dimensionFunction f z ≠ k) :
    torSubvarietyProductOfBound C f hX k h z = 0 := by
  rw [torSubvarietyProductOfBound_apply C f hX k h d hd z]
  refine Finset.sum_eq_zero fun i _ => ?_
  have := isCoherent_torSheaf_of_isRegular X hX (structureSheafAt x) (structureSheafAt y)
    (isCoherent_structureSheafAt x) (isCoherent_structureSheafAt y) i
  exact mul_eq_zero_of_right _ (by simp [Stacks.Chow.sheafCycleCoeff, hz])

/-- **The product read at every pair is supported on the intersection.** Off `W ∩ V` the
coefficient of the product of Section 43.14 read at the pair `(x, y)` vanishes, whether or not
the pair satisfies the delta-dimension bound. -/
theorem torFormulaSubvarietyProductTotal_apply_eq_zero_of_notMem_inter
    (C : Stacks.Chow.ChowSituation.{u}) (f : X ⟶ C.S) [LocallyOfFiniteType f]
    [IsLocallyNoetherian X] (hX : IsRegular X) (k : ℤ) (x y : X) (d : ℕ)
    (hd : topologicalKrullDim X ≤ (d : WithBot ℕ∞)) {z : X}
    (hz : z ∉ closure ({x} : Set X) ∩ closure ({y} : Set X)) :
    torFormulaSubvarietyProductTotal C f hX k x y z = 0 := by
  by_cases h : TorSupportBound C f hX k x y
  · rw [torFormulaSubvarietyProductTotal_eq_of_bound C f hX k h]
    exact torSubvarietyProductOfBound_apply_eq_zero_of_notMem_inter C f hX k h d hd hz
  · rw [torFormulaSubvarietyProductTotal_eq_zero C f hX k h]
    rfl

/-! ### Transversal components -/

/-- **The coefficient of a transversal component in the product of two closed subvarieties.**
Let `X` be a regular scheme of dimension at most `d`, let `W` and `V` be the reduced closures of
points `x` and `y` satisfying the delta-dimension bound `h`, and let `z` be a point of both whose
closure has delta-dimension `k`. Suppose the local ideals `I` of `W` and `J` of `V` at `z` are
contained in ideals `I₀`, `J₀` with `dim (A ⧸ I) = dim (A ⧸ I₀)` and
`dim (A ⧸ J) = dim (A ⧸ J₀)` and `dim A ≤ dim (A ⧸ I₀) + dim (A ⧸ J₀)`, and that `A ⧸ (I ⊔ J)`
has length one. Then the coefficient of `z` in the intersection product `W · V` of Section 43.14
is `1`.

Geometrically: `z` is the generic point of an irreducible component `T` of `W ∩ V` along which
the intersection has multiplicity one, and the dimension hypotheses are proper intersection; the
conclusion is that `T` occurs in `W · V` with coefficient one. -/
theorem torSubvarietyProductOfBound_apply_eq_one (C : Stacks.Chow.ChowSituation.{u})
    (f : X ⟶ C.S) [LocallyOfFiniteType f] [IsLocallyNoetherian X] (hX : IsRegular X) (k : ℤ)
    {x y : X} (h : TorSupportBound C f hX k x y) (d : ℕ)
    (hd : topologicalKrullDim X ≤ (d : WithBot ℕ∞)) {z : X}
    (hz : Stacks.Chow.relativeDimension C.dimensionFunction f z = k)
    (hzx : z ∈ closure ({x} : Set X)) (hzy : z ∈ closure ({y} : Set X))
    (I₀ J₀ : Ideal (X.presheaf.stalk z))
    (hI : localIdealAt x z ≤ I₀) (hJ : localIdealAt y z ≤ J₀)
    (hmult : Module.length (X.presheaf.stalk z)
      (X.presheaf.stalk z ⧸ (localIdealAt x z ⊔ localIdealAt y z)) = 1)
    (hdimI : ringKrullDim (X.presheaf.stalk z ⧸ localIdealAt x z) =
      ringKrullDim (X.presheaf.stalk z ⧸ I₀))
    (hdimJ : ringKrullDim (X.presheaf.stalk z ⧸ localIdealAt y z) =
      ringKrullDim (X.presheaf.stalk z ⧸ J₀))
    (hproper : ringKrullDim (X.presheaf.stalk z) ≤
      ringKrullDim (X.presheaf.stalk z ⧸ I₀) + ringKrullDim (X.presheaf.stalk z ⧸ J₀)) :
    torSubvarietyProductOfBound C f hX k h z = 1 := by
  have _ : IsRegularLocalRing (X.presheaf.stalk z) :=
    AlgebraicGeometry.IsRegular.isRegularLocalRing_stalk hX z
  obtain ⟨-, -, -, -, -, -, hone⟩ :=
    IsRegularLocalRing.eq_and_isRegularLocalRing_quotient_and_localIntersectionMultiplicity_eq_one
      (localIdealAt x z) I₀ (localIdealAt y z) J₀ hI hJ hmult hdimI hdimJ hproper
  have hcoeff := torSubvarietyProductOfBound_apply_eq_localIntersectionMultiplicity
    C f hX k h d hd hz hzx hzy
  rw [hone] at hcoeff
  exact_mod_cast hcoeff

/-- **Stacks 0B1J, clause (1), for the intersection product of two prime cycles.** In the
situation of `AlgebraicGeometry.TorFormula.torSubvarietyProductOfBound_apply_eq_one`, the
coefficient of `z` in the intersection product `[W] · [V]` of the prime cycles of the two closed
subvarieties is `1`.

The delta-dimension bound is taken at the one pair `(x, y)` the conclusion is about; the product
itself is total in that bound, so no bound at any other pair is needed. -/
theorem torFormulaCycleIntersectionProduct_apply_eq_one [DecidableEq X]
    (C : Stacks.Chow.ChowSituation.{u}) (f : X ⟶ C.S) [LocallyOfFiniteType f]
    [IsLocallyNoetherian X] (hX : IsRegular X) (k : ℤ) {x y : X}
    (hb : TorSupportBound C f hX k x y) (d : ℕ)
    (hd : topologicalKrullDim X ≤ (d : WithBot ℕ∞)) {z : X}
    (hz : Stacks.Chow.relativeDimension C.dimensionFunction f z = k)
    (hzx : z ∈ closure ({x} : Set X)) (hzy : z ∈ closure ({y} : Set X))
    (I₀ J₀ : Ideal (X.presheaf.stalk z))
    (hI : localIdealAt x z ≤ I₀) (hJ : localIdealAt y z ≤ J₀)
    (hmult : Module.length (X.presheaf.stalk z)
      (X.presheaf.stalk z ⧸ (localIdealAt x z ⊔ localIdealAt y z)) = 1)
    (hdimI : ringKrullDim (X.presheaf.stalk z ⧸ localIdealAt x z) =
      ringKrullDim (X.presheaf.stalk z ⧸ I₀))
    (hdimJ : ringKrullDim (X.presheaf.stalk z ⧸ localIdealAt y z) =
      ringKrullDim (X.presheaf.stalk z ⧸ J₀))
    (hproper : ringKrullDim (X.presheaf.stalk z) ≤
      ringKrullDim (X.presheaf.stalk z ⧸ I₀) + ringKrullDim (X.presheaf.stalk z ⧸ J₀)) :
    torFormulaCycleIntersectionProduct C f hX k
        (Function.locallyFinsuppWithin.single x 1)
        (Function.locallyFinsuppWithin.single y 1) z = 1 := by
  change cycleIntersectionProduct (torFormulaSubvarietyProductTotal C f hX k)
    (Function.locallyFinsuppWithin.single x 1)
    (Function.locallyFinsuppWithin.single y 1) z = 1
  rw [cycleIntersectionProduct_single_single,
    torFormulaSubvarietyProductTotal_eq_of_bound C f hX k hb]
  simpa using torSubvarietyProductOfBound_apply_eq_one C f hX k hb d hd hz hzx hzy I₀ J₀
    hI hJ hmult hdimI hdimJ hproper

/-- **The coefficient of a transversal component in the product of two cycles.** Let `X` be a
regular scheme of dimension at most `d`, let `α` and `β` be cycles with finitely many components,
and let `z` be a point of delta-dimension `k` lying on the components `W` and `V` of `α` and `β`
with generic points `x` and `y` and on no other pair of components. If the pair `(x, y)`
satisfies the delta-dimension bound and the local ideals of `W` and `V` at `z` satisfy the
transversality and proper-intersection hypotheses of
`AlgebraicGeometry.TorFormula.torSubvarietyProductOfBound_apply_eq_one`, then the coefficient of
`z` in `α · β` is the product `n m` of the coefficients of `W` in `α` and of `V` in `β`.

Geometrically `z` is the generic point of an irreducible component `T` of `W ∩ V` along which the
intersection has multiplicity one, the separation hypothesis says that no other component of
either cycle contains `T`, and the conclusion is that `T` occurs in `α · β` with coefficient
`n m`. -/
theorem torFormulaCycleIntersectionProduct_apply_eq_mul (C : Stacks.Chow.ChowSituation.{u})
    (f : X ⟶ C.S) [LocallyOfFiniteType f] [IsLocallyNoetherian X] (hX : IsRegular X) (k : ℤ)
    {α β : AlgebraicCycle X ℤ} (hα : (Function.support α).Finite)
    (hβ : (Function.support β).Finite) {x y : X} (h : TorSupportBound C f hX k x y) (d : ℕ)
    (hd : topologicalKrullDim X ≤ (d : WithBot ℕ∞)) {z : X}
    (hz : Stacks.Chow.relativeDimension C.dimensionFunction f z = k)
    (hzx : z ∈ closure ({x} : Set X)) (hzy : z ∈ closure ({y} : Set X))
    (hx : α x ≠ 0) (hy : β y ≠ 0)
    (hsep : ∀ x' ∈ Function.support α, ∀ y' ∈ Function.support β, (x', y') ≠ (x, y) →
      z ∉ closure ({x'} : Set X) ∩ closure ({y'} : Set X))
    (I₀ J₀ : Ideal (X.presheaf.stalk z))
    (hI : localIdealAt x z ≤ I₀) (hJ : localIdealAt y z ≤ J₀)
    (hmult : Module.length (X.presheaf.stalk z)
      (X.presheaf.stalk z ⧸ (localIdealAt x z ⊔ localIdealAt y z)) = 1)
    (hdimI : ringKrullDim (X.presheaf.stalk z ⧸ localIdealAt x z) =
      ringKrullDim (X.presheaf.stalk z ⧸ I₀))
    (hdimJ : ringKrullDim (X.presheaf.stalk z ⧸ localIdealAt y z) =
      ringKrullDim (X.presheaf.stalk z ⧸ J₀))
    (hproper : ringKrullDim (X.presheaf.stalk z) ≤
      ringKrullDim (X.presheaf.stalk z ⧸ I₀) + ringKrullDim (X.presheaf.stalk z ⧸ J₀)) :
    torFormulaCycleIntersectionProduct C f hX k α β z = α x * β y := by
  have hone : torFormulaSubvarietyProductTotal C f hX k x y z = 1 := by
    rw [torFormulaSubvarietyProductTotal_eq_of_bound C f hX k h]
    exact torSubvarietyProductOfBound_apply_eq_one C f hX k h d hd hz hzx hzy I₀ J₀
      hI hJ hmult hdimI hdimJ hproper
  change cycleIntersectionProduct (torFormulaSubvarietyProductTotal C f hX k) α β z = α x * β y
  rw [cycleIntersectionProduct_apply _ hα hβ z]
  refine Eq.trans (Finset.sum_eq_single_of_mem x (hα.mem_toFinset.2 hx) fun x' hx' hne => ?_)
    (Eq.trans (Finset.sum_eq_single_of_mem y (hβ.mem_toFinset.2 hy) fun y' hy' hne => ?_) ?_)
  · refine Finset.sum_eq_zero fun y' hy' => mul_eq_zero_of_right _ ?_
    exact torFormulaSubvarietyProductTotal_apply_eq_zero_of_notMem_inter C f hX k x' y' d hd
      (hsep x' (hα.mem_toFinset.1 hx') y' (hβ.mem_toFinset.1 hy') (by simp [Prod.ext_iff, hne]))
  · refine mul_eq_zero_of_right _ ?_
    exact torFormulaSubvarietyProductTotal_apply_eq_zero_of_notMem_inter C f hX k x y' d hd
      (hsep x hx y' (hβ.mem_toFinset.1 hy') (by simp [Prod.ext_iff, hne]))
  · rw [hone, mul_one]

end AlgebraicGeometry.TorFormula

end
