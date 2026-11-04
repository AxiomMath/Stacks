module

public import StacksFrontier.AlgebraicGeometry.Intersection.TorFormula.IntersectionMultiplicity
public import StacksFrontier.AlgebraicGeometry.Intersection.TorFormula.IntersectionProductCycle
public import StacksFrontier.AlgebraicGeometry.Intersection.TorFormula.TorSheafMultiplicity
public import StacksFrontier.AlgebraicGeometry.Morphisms.Support.TestModuleStalk
public import StacksFrontier.AlgebraicGeometry.Picard.SmoothCurveLocalDimension
import StacksCore.Tactic.StacksAttribute

/-!
# The cycle of the fibre of an effective Cartier divisor

Let `Y` be a regular scheme, let `D ⊆ Y` be an effective Cartier divisor and let `W ⊆ Y` be a
closed subvariety meeting it properly. The scheme-theoretic intersection `W ∩ D` is cut out by
the join `W ⊔ D` of the two sheaves of ideals, and its cycle in dimension `k` is the
intersection product of `W` and `D` by the Tor formula of Section 43.14:

`[W ∩ D]_k = W · D`.

For `Y = X × P¹`, `D = X × a` the effective Cartier divisor cut out by a closed point `a` of
`P¹` and `W` a closed subvariety of dimension `k + 1` meeting `X × a` properly, `W ∩ D` is the
scheme-theoretic fibre `W_a` and this is part (1)(a) of Tag 0B07.

The proof compares the two sides coefficient by coefficient. Away from the points of
delta-dimension `k` both coefficients vanish. At a point `z` of delta-dimension `k` the
coefficient of the left-hand side is the length of `𝒪_{Y, z} ⧸ (W ⊔ D)_z`, and the coefficient of
the right-hand side is the alternating sum of the lengths of the stalks of the `Tor` sheaves,
which `AlgebraicGeometry.TorFormula.sheafMultiplicity_torSheaf_eq_length_tor_stalk` turns into
the alternating sum of the lengths of the `Tor` modules of the two local rings. That alternating
sum is the Tor-formula intersection multiplicity of the pair at `z`, and the local computation
against an effective Cartier divisor identifies it with the length of
`𝒪_{Y, z} ⧸ (W ⊔ D)_z`.

## Main definitions

* `AlgebraicGeometry.TorFormula.subschemeStructureSheaf` — the structure sheaf of the closed
  subscheme cut out by a sheaf of ideals, as an `𝒪_Y`-module.

## Main results

* `AlgebraicGeometry.TorFormula.sheafMultiplicity_subschemeStructureSheaf` — the multiplicity of
  that structure sheaf at a point of the subscheme is the length of the local ring there.
* `AlgebraicGeometry.TorFormula.sheafMultiplicity_torSheaf_subschemeStructureSheaf` — the
  multiplicity of a `Tor` sheaf of two such structure sheaves is the length of the `Tor` module
  of the two local rings.
* `AlgebraicGeometry.TorFormula.intersectionProductCycle_apply` — the coefficient of the
  intersection product at a point, as a finite alternating sum.
* `AlgebraicGeometry.TorFormula.subschemeCycle_sup_eq_intersectionProductCycle` — **Tag 0B07
  part (1)(a)**, the cycle identity.

## References

* [Stacks Project, Tag 0B07](https://stacks.math.columbia.edu/tag/0B07)
* [Stacks Project, Tag 0AZR](https://stacks.math.columbia.edu/tag/0AZR)
* [Stacks Project, Tag 02QX](https://stacks.math.columbia.edu/tag/02QX)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

attribute [local instance 100000] HasDerivedCategory.standard

namespace AlgebraicGeometry.TorFormula

variable {Y : Scheme.{u}}

/-- The structure sheaf of the closed subscheme cut out by a sheaf of ideals, pushed forward to
an `𝒪_Y`-module on the ambient scheme. -/
def subschemeStructureSheaf (J : Y.IdealSheafData) : Y.Modules :=
  (Scheme.Modules.pushforward J.subschemeι).obj (Stacks.Ample.unitModule _)

/-- On a locally noetherian scheme, the structure sheaf of a closed subscheme is a coherent
`𝒪_Y`-module. -/
instance isCoherent_subschemeStructureSheaf [IsLocallyNoetherian Y] (J : Y.IdealSheafData) :
    (subschemeStructureSheaf J).IsCoherent :=
  Stacks.Chow.isCoherent_pushforwardStructureSheaf _

/-- The support of the structure sheaf of a closed subscheme is that subscheme. -/
theorem supp_subschemeStructureSheaf (J : Y.IdealSheafData) :
    SheafOfModules.supp (subschemeStructureSheaf J) = (J.support : Set Y) := by
  rw [subschemeStructureSheaf, Stacks.Chow.supp_pushforwardStructureSheaf,
    Scheme.IdealSheafData.range_subschemeι]

/-- **The multiplicity of the structure sheaf of a closed subscheme at a point of it** is the
length of the local ring of the subscheme there, that is, of `𝒪_{Y, z} ⧸ J_z`. -/
theorem sheafMultiplicity_subschemeStructureSheaf (J : Y.IdealSheafData) (z : Y)
    (hz : z ∈ J.support) :
    Stacks.Chow.sheafMultiplicity (subschemeStructureSheaf J) z =
      (Module.length (Y.presheaf.stalk z)
        (Y.presheaf.stalk z ⧸ IdealSheafData.stalk J z)).toNat := by
  unfold Stacks.Chow.sheafMultiplicity
  congr 2
  exact (IdealSheafData.stalkPushforwardSubschemeQuotEquiv J
    (IdealSheafData.subschemePoint J z hz)).length_eq

/-- The stalk of the structure sheaf of a closed subscheme at a point of it, read over the local
ring of the ambient scheme, is `𝒪_{Y, z} ⧸ J_z`. -/
def stalkSubschemeStructureSheafIso (J : Y.IdealSheafData) (z : Y) (hz : z ∈ J.support) :
    stalkModuleCat Y (subschemeStructureSheaf J) z ≅
      ModuleCat.of (Y.presheaf.stalk z) (Y.presheaf.stalk z ⧸ IdealSheafData.stalk J z) :=
  LinearEquiv.toModuleIso
    (IdealSheafData.stalkPushforwardSubschemeQuotEquiv J
      (IdealSheafData.subschemePoint J z hz))

/-- **The multiplicity of a `Tor` sheaf of two subscheme structure sheaves** at a point of both
subschemes is the length of the `Tor` module of the two local rings over the local ring of the
ambient scheme. -/
theorem sheafMultiplicity_torSheaf_subschemeStructureSheaf (I J : Y.IdealSheafData) (p : ℕ)
    (z : Y) (hzI : z ∈ I.support) (hzJ : z ∈ J.support) :
    Stacks.Chow.sheafMultiplicity
        (torSheaf Y (subschemeStructureSheaf I) (subschemeStructureSheaf J) p) z =
      (Module.length (Y.presheaf.stalk z)
        (((Tor (ModuleCat.{u} (Y.presheaf.stalk z)) p).obj
            (ModuleCat.of (Y.presheaf.stalk z)
              (Y.presheaf.stalk z ⧸ IdealSheafData.stalk I z))).obj
          (ModuleCat.of (Y.presheaf.stalk z)
            (Y.presheaf.stalk z ⧸ IdealSheafData.stalk J z)))).toNat := by
  have key : Module.length (Y.presheaf.stalk z)
        (((Tor (ModuleCat.{u} (Y.presheaf.stalk z)) p).obj
            (stalkModuleCat Y (subschemeStructureSheaf I) z)).obj
          (stalkModuleCat Y (subschemeStructureSheaf J) z))
      = Module.length (Y.presheaf.stalk z)
        (((Tor (ModuleCat.{u} (Y.presheaf.stalk z)) p).obj
            (ModuleCat.of (Y.presheaf.stalk z)
              (Y.presheaf.stalk z ⧸ IdealSheafData.stalk I z))).obj
          (ModuleCat.of (Y.presheaf.stalk z)
            (Y.presheaf.stalk z ⧸ IdealSheafData.stalk J z))) :=
    (((Tor (ModuleCat.{u} (Y.presheaf.stalk z)) p).mapIso
          (stalkSubschemeStructureSheafIso I z hzI)).app
        (stalkModuleCat Y (subschemeStructureSheaf J) z) ≪≫
      ((Tor (ModuleCat.{u} (Y.presheaf.stalk z)) p).obj
        (ModuleCat.of (Y.presheaf.stalk z)
          (Y.presheaf.stalk z ⧸ IdealSheafData.stalk I z))).mapIso
        (stalkSubschemeStructureSheafIso J z hzJ)).toLinearEquiv.length_eq
  rw [sheafMultiplicity_torSheaf_eq_length_tor_stalk, key]

/-- **The coefficient of the intersection product at a point** is the finite alternating sum of
the multiplicities of the `Tor` sheaves: on a regular scheme of dimension at most `d` the
summands with `i > d` vanish. -/
theorem intersectionProductCycle_apply (C : Stacks.Chow.ChowSituation.{u}) (f : Y ⟶ C.S)
    [LocallyOfFiniteType f] (hY : IsRegular Y) (F G : Y.Modules)
    (hF : SheafOfModules.IsCoherent F) (hG : SheafOfModules.IsCoherent G) (k : ℤ)
    (hFk : ∀ i : ℕ,
      haveI := isCoherent_torSheaf_of_isRegular Y hY F G hF hG i
      Stacks.Chow.schemeDeltaDimension C
        ((Stacks.Chow.reducedSupport (torSheaf Y F G i)).subschemeι ≫ f) ≤ WithBotTop.coe k)
    (hreg : ∀ y : Y, IsRegularLocalRing (Y.presheaf.stalk y)) (d : ℕ)
    (hd : topologicalKrullDim Y ≤ (d : WithBot ℕ∞)) (z : Y) :
    intersectionProductCycle C f hY F G hF hG k hFk z =
      ∑ i ∈ Finset.range (d + 2), ((-1 : ℤ) ^ i) *
        (haveI := isCoherent_torSheaf_of_isRegular Y hY F G hF hG i
         Stacks.Chow.sheafCycleCoeff C f (torSheaf Y F G i) k z) := by
  rw [intersectionProductCycle,
    finsum_eq_sum_of_support_subset _ (s := Finset.range (d + 2)) ?_]
  · simp only [Function.locallyFinsuppWithin.coe_sum, Finset.sum_apply,
      Stacks.Chow.coherentSheafCycle]
    rfl
  · intro i hi
    simp only [Finset.coe_range, Set.mem_Iio]
    by_contra hle
    exact hi (torSheafCycle_eq_zero_of_lt C f hY F G hF hG k hFk hreg d hd i (by omega))

/-- **Stacks 0B07, part (1)(a): the cycle identity.** Let `Y` be a regular scheme of dimension
at most `d`, let `D` be a sheaf of ideals which at each point of delta-dimension `k` is cut out
by a one-element regular sequence, and let `W` be a sheaf of ideals whose local ring at such a
point is a domain of dimension one meeting `D` properly there. Then the cycle of the
scheme-theoretic intersection `W ∩ D`, cut out by `W ⊔ D`, is the Tor-formula intersection
product of `W` and `D`.

For `Y = X × P¹`, `D = X × a` and `W` a closed subvariety of dimension `k + 1` meeting `X × a`
properly, the left-hand side is `[W_a]_k` and the right-hand side is `W · X × a`. -/
theorem subschemeCycle_sup_eq_intersectionProductCycle (C : Stacks.Chow.ChowSituation.{u})
    (f : Y ⟶ C.S) [LocallyOfFiniteType f] [IsLocallyNoetherian Y] (hY : IsRegular Y)
    (W D : Y.IdealSheafData) (k : ℤ)
    (d : ℕ) (hd : topologicalKrullDim Y ≤ (d : WithBot ℕ∞))
    (hWD : Stacks.Chow.schemeDeltaDimension C
      ((Stacks.Chow.reducedSupport (subschemeStructureSheaf (W ⊔ D))).subschemeι ≫ f) ≤
        WithBotTop.coe k)
    (hFk : ∀ i : ℕ,
      haveI := isCoherent_torSheaf_of_isRegular Y hY (subschemeStructureSheaf W)
        (subschemeStructureSheaf D) (isCoherent_subschemeStructureSheaf W)
        (isCoherent_subschemeStructureSheaf D) i
      Stacks.Chow.schemeDeltaDimension C
        ((Stacks.Chow.reducedSupport
          (torSheaf Y (subschemeStructureSheaf W) (subschemeStructureSheaf D) i)).subschemeι ≫ f)
        ≤ WithBotTop.coe k)
    (hpt : ∀ z : Y, Stacks.Chow.relativeDimension C.dimensionFunction f z = k →
      z ∈ (W ⊔ D).support ∧
        IsDomain (Y.presheaf.stalk z ⧸ IdealSheafData.stalk W z) ∧
        (∃ g : Fin 1 → Y.presheaf.stalk z,
          RingTheory.Sequence.IsRegular (Y.presheaf.stalk z) (List.ofFn g) ∧
            IdealSheafData.stalk D z = Ideal.span (Set.range g)) ∧
        ringKrullDim (Y.presheaf.stalk z ⧸ IdealSheafData.stalk (D ⊔ W) z) = 0 ∧
        ringKrullDim (Y.presheaf.stalk z ⧸ IdealSheafData.stalk W z) = 1) :
    Stacks.Chow.coherentSheafCycle C f (subschemeStructureSheaf (W ⊔ D)) k hWD =
      intersectionProductCycle C f hY (subschemeStructureSheaf W) (subschemeStructureSheaf D)
        (isCoherent_subschemeStructureSheaf W) (isCoherent_subschemeStructureSheaf D) k hFk := by
  classical
  have hreg : ∀ y : Y, IsRegularLocalRing (Y.presheaf.stalk y) :=
    fun y => AlgebraicGeometry.IsRegular.isRegularLocalRing_stalk hY y
  have hcoh : ∀ i : ℕ, (torSheaf Y (subschemeStructureSheaf W)
      (subschemeStructureSheaf D) i).IsCoherent := fun i =>
    isCoherent_torSheaf_of_isRegular Y hY (subschemeStructureSheaf W)
      (subschemeStructureSheaf D) (isCoherent_subschemeStructureSheaf W)
      (isCoherent_subschemeStructureSheaf D) i
  apply Function.locallyFinsuppWithin.ext
  intro z
  rw [intersectionProductCycle_apply C f hY (subschemeStructureSheaf W)
    (subschemeStructureSheaf D) (isCoherent_subschemeStructureSheaf W)
    (isCoherent_subschemeStructureSheaf D) k hFk hreg d hd z]
  by_cases hz : Stacks.Chow.relativeDimension C.dimensionFunction f z = k
  · obtain ⟨hzWD, hdom, ⟨g, hg, hDg⟩, h0, hW1⟩ := hpt z hz
    have hzWD' := hzWD
    rw [Scheme.IdealSheafData.support_sup] at hzWD
    obtain ⟨hzW, hzD⟩ := hzWD
    have hlhs : Stacks.Chow.coherentSheafCycle C f (subschemeStructureSheaf (W ⊔ D)) k hWD z =
        (Module.length (Y.presheaf.stalk z)
          (Y.presheaf.stalk z ⧸ IdealSheafData.stalk (W ⊔ D) z)).toNat := by
      refine Eq.trans ?_ (sheafMultiplicity_subschemeStructureSheaf (W ⊔ D) z hzWD')
      exact Stacks.Chow.cycleAssociatedToCoherentSheaf_apply_of_relativeDimension_eq C f
        (subschemeStructureSheaf (W ⊔ D)) k hWD hz
    rw [hlhs]
    have hrhs : ∀ i : ℕ,
        (have := isCoherent_torSheaf_of_isRegular Y hY (subschemeStructureSheaf W)
          (subschemeStructureSheaf D) (isCoherent_subschemeStructureSheaf W)
          (isCoherent_subschemeStructureSheaf D) i
         Stacks.Chow.sheafCycleCoeff C f
           (torSheaf Y (subschemeStructureSheaf W) (subschemeStructureSheaf D) i) k z)
        = (Module.length (Y.presheaf.stalk z)
            (((Tor (ModuleCat.{u} (Y.presheaf.stalk z)) i).obj
                (ModuleCat.of (Y.presheaf.stalk z)
                  (Y.presheaf.stalk z ⧸ IdealSheafData.stalk D z))).obj
              (ModuleCat.of (Y.presheaf.stalk z)
                (Y.presheaf.stalk z ⧸ IdealSheafData.stalk W z)))).toNat := by
      intro i
      refine Eq.trans (Stacks.Chow.cycleAssociatedToCoherentSheaf_apply_of_relativeDimension_eq
        C f (torSheaf Y (subschemeStructureSheaf W) (subschemeStructureSheaf D) i) k
        (hFk i) hz) ?_
      rw [sheafMultiplicity_torSheaf_subschemeStructureSheaf W D i z hzW hzD,
        Module.length_tor_comm]
    rw [Finset.sum_congr rfl (fun i _ => by rw [hrhs i])]
    have hQ : ((∑ i ∈ Finset.range (d + 2), ((-1 : ℤ) ^ i) *
          ((Module.length (Y.presheaf.stalk z)
            (((Tor (ModuleCat.{u} (Y.presheaf.stalk z)) i).obj
                (ModuleCat.of (Y.presheaf.stalk z)
                  (Y.presheaf.stalk z ⧸ IdealSheafData.stalk D z))).obj
              (ModuleCat.of (Y.presheaf.stalk z)
                (Y.presheaf.stalk z ⧸ IdealSheafData.stalk W z)))).toNat : ℤ) : ℤ) : ℚ)
        = (((Module.length (Y.presheaf.stalk z)
            (Y.presheaf.stalk z ⧸ IdealSheafData.stalk (W ⊔ D) z)).toNat : ℤ) : ℚ) := by
      push_cast
      rw [sup_comm W D]
      refine Eq.trans ?_ (Stacks.Intersection.intersectionMultiplicity_eq_length_stalk_sup
        D W z g hg hDg h0 hW1)
      rw [Stacks.Intersection.intersectionMultiplicity_eq, Ideal.localIntersectionMultiplicity]
      refine (tsum_eq_sum (f := fun i : ℕ => (-1 : ℚ) ^ i *
        ((Module.length (Y.presheaf.stalk z)
          (((Tor (ModuleCat.{u} (Y.presheaf.stalk z)) i).obj
              (ModuleCat.of (Y.presheaf.stalk z)
                (Y.presheaf.stalk z ⧸ IdealSheafData.stalk D z))).obj
            (ModuleCat.of (Y.presheaf.stalk z)
              (Y.presheaf.stalk z ⧸ IdealSheafData.stalk W z)))).toNat : ℚ))
        (fun i hi => ?_)).symm
      rw [Finset.mem_range, not_lt] at hi
      rw [Ideal.length_tor_quotient_span_eq_zero_of_lt g hg (IdealSheafData.stalk D z) hDg
        (Y.presheaf.stalk z ⧸ IdealSheafData.stalk W z) (by omega)]
      simp
    exact_mod_cast hQ.symm
  · refine Eq.trans (Stacks.Chow.cycleAssociatedToCoherentSheaf_apply_of_relativeDimension_ne C f
      (subschemeStructureSheaf (W ⊔ D)) k hWD hz) ?_
    refine (Finset.sum_eq_zero fun i _ => ?_).symm
    exact mul_eq_zero_of_right _
      (Stacks.Chow.cycleAssociatedToCoherentSheaf_apply_of_relativeDimension_ne C f
        (torSheaf Y (subschemeStructureSheaf W) (subschemeStructureSheaf D) i) k (hFk i) hz)

end AlgebraicGeometry.TorFormula

end
