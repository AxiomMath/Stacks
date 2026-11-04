module

public import StacksFrontier.AlgebraicGeometry.Chow.CoherentCycle.ClosedSubscheme
public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartierWeilDivisor
public import StacksFrontier.AlgebraicGeometry.Intersection.ComputingIntersectionMultiplicities.CohenMacaulayMultiplicity
public import StacksFrontier.AlgebraicGeometry.Intersection.TorFormula.DivisorFibreCycle
import StacksCore.Tactic.StacksAttribute

/-!
# The intersection product of two Cohen-Macaulay subvarieties is the intersection cycle

Let `X` be a nonsingular variety and let `V`, `W ⊆ X` be closed subvarieties which intersect
properly, and suppose both are Cohen-Macaulay. Then the Tor-formula intersection product of
Section 43.14 is the cycle of the scheme-theoretic intersection,

`V · W = [V ∩ W]_{dim V + dim W - dim X}`,

which is the final clause of Tag 0B02. The pointwise multiplicity formula underlying it,
`e(X, V · W, Z) = length_{𝒪_{X, ξ}}(𝒪_{V ∩ W, ξ})`, is
`Ideal.localIntersectionMultiplicity_eq_length_of_isCohenMacaulayLocalRing`.

The two cycles are compared coefficient by coefficient, as in Tag 0B07 part (1)(a). At a point
`z` of delta-dimension `k` lying on both subvarieties the coefficient of the right-hand side is
the alternating sum of the lengths of the `Tor` modules of the two local rings
`𝒪_{V, z} = 𝒪_{X, z} ⧸ V_z` and `𝒪_{W, z} = 𝒪_{X, z} ⧸ W_z`; the Cohen-Macaulay hypotheses make
every term above degree zero vanish, by `Ideal.tor_subsingleton_of_isCohenMacaulayLocalRing`, and
the degree zero term is the length of `𝒪_{X, z} ⧸ (V_z ⊔ W_z)`, the local ring of the
scheme-theoretic intersection. At a point of delta-dimension `k` off one of the two subvarieties
both coefficients vanish, since the `Tor` sheaves are supported on the intersection of the two
supports, and at a point of delta-dimension other than `k` both coefficients vanish by
construction.

## Main results

* `TorFormula.subschemeCycle_sup_eq_intersectionProductCycle_of_isCohenMacaulay`
  — the cycle identity, with the scheme-theoretic intersection read through its structure sheaf.
* `TorFormula.cycleAssociatedToClosedSubscheme_eq_intersectionProductCycle_of_isCohenMacaulay`
  — the same identity with the left-hand side the cycle `[V ∩ W]_k` of the closed subscheme
  `V ∩ W`.
* `TorFormula.cohenMacaulayIntersectionFormula` — **Tag 0B02**, both clauses: the multiplicity
  formula at the generic point of each component of `V ∩ W` and the cycle identity.

## Implementation notes

The hypotheses of Tag 0B02 are local at the generic point of a component, so they are imposed
here at each point `z` of delta-dimension `k` lying on both subvarieties: `𝒪_{V, z}` and
`𝒪_{W, z}` are Cohen-Macaulay local rings, proper intersection is the dimension inequality
`dim 𝒪_{X, z} ≤ dim 𝒪_{V, z} + dim 𝒪_{W, z}` of Tag 0B1I, and that `z` is a generic point of
`V ∩ W` is the radical condition `√(V_z ⊔ W_z) = 𝔪_z`. Nothing is assumed at a point of
delta-dimension `k` lying off `V` or off `W`: there both sides are zero.

The `IsLocalRing` instance on `𝒪_{X, z} ⧸ V_z` that the Cohen-Macaulay predicate needs is not
available from the typeclass system, since it depends on `V_z` being a proper ideal; it is
supplied in the statement by `AlgebraicGeometry.TorFormula.isLocalRing_quotient_stalk` from the
hypothesis that `z` lies in the support.

## References

* [Stacks Project, Tag 0B02](https://stacks.math.columbia.edu/tag/0B02)
* [Stacks Project, Tag 0AZR](https://stacks.math.columbia.edu/tag/0AZR)
* [Stacks Project, Tag 02QX](https://stacks.math.columbia.edu/tag/02QX)
* [Stacks Project, Tag 02QY](https://stacks.math.columbia.edu/tag/02QY)
* [Stacks Project, Tag 0B07](https://stacks.math.columbia.edu/tag/0B07)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

attribute [local instance 100000] HasDerivedCategory.standard

namespace AlgebraicGeometry.TorFormula

variable {Y : Scheme.{u}}

/-- At a point of the support of a sheaf of ideals the induced ideal in the local ring is proper,
so the local ring of the closed subscheme there is again a local ring. -/
theorem isLocalRing_quotient_stalk (V : Y.IdealSheafData) (z : Y) (hz : z ∈ V.support) :
    IsLocalRing (Y.presheaf.stalk z ⧸ IdealSheafData.stalk V z) :=
  have : Nontrivial (Y.presheaf.stalk z ⧸ IdealSheafData.stalk V z) :=
    Ideal.Quotient.nontrivial_iff.mpr fun h =>
      (IdealSheafData.stalk_eq_top_iff_notMem_support V z).mp h hz
  IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective

/-- **The degree zero term of the Tor formula when the higher Tor modules vanish.** If
`Tor_i^A(A ⧸ I, A ⧸ J) = 0` for every `i > 0`, the length of `Tor_0^A(A ⧸ I, A ⧸ J)` is the length
of `A ⧸ (I ⊔ J)`: the alternating sum of `Ideal.localIntersectionMultiplicity` reduces to its first
term, which is that length. -/
theorem length_tor_zero_toNat_eq_length_quotient_sup_of_tor_subsingleton {A : Type u}
    [CommRing A] (I J : Ideal A)
    (hTor : ∀ i : ℕ, 0 < i → Subsingleton
      (((Tor (ModuleCat.{u} A) i).obj (ModuleCat.of A (A ⧸ I))).obj
        (ModuleCat.of A (A ⧸ J)))) :
    (Module.length A (((Tor (ModuleCat.{u} A) 0).obj (ModuleCat.of A (A ⧸ I))).obj
        (ModuleCat.of A (A ⧸ J)))).toNat =
      (Module.length A (A ⧸ (I ⊔ J))).toNat := by
  have hsum : I.localIntersectionMultiplicity (A ⧸ J) =
      ((Module.length A (((Tor (ModuleCat.{u} A) 0).obj (ModuleCat.of A (A ⧸ I))).obj
        (ModuleCat.of A (A ⧸ J)))).toNat : ℚ) := by
    rw [Ideal.localIntersectionMultiplicity, tsum_eq_single 0]
    · simp
    · intro i hi
      rw [Module.length_eq_zero_iff.mpr (hTor i (Nat.pos_of_ne_zero hi))]
      simp
  have := (hsum.symm.trans
    (Ideal.localIntersectionMultiplicity_eq_length_quotient_sup_of_tor_subsingleton I J hTor))
  exact_mod_cast this

/-- **The degree zero term of the Tor formula at a Cohen-Macaulay proper intersection.** Under
the hypotheses of Tag 0B02 the length of `Tor_0^A(A ⧸ I, A ⧸ J)` is the length of
`A ⧸ (I ⊔ J)`: the higher `Tor` modules vanish, so the alternating sum of
`Ideal.localIntersectionMultiplicity` reduces to its first term. -/
theorem length_tor_zero_toNat_eq_length_quotient_sup_of_isCohenMacaulay {A : Type u} [CommRing A]
    [IsRegularLocalRing A] (I J : Ideal A) [IsLocalRing (A ⧸ I)] [IsLocalRing (A ⧸ J)]
    (hI : IsCohenMacaulayLocalRing (A ⧸ I)) (hJ : IsCohenMacaulayLocalRing (A ⧸ J))
    (hproper : ringKrullDim A ≤ ringKrullDim (A ⧸ I) + ringKrullDim (A ⧸ J))
    (hcomponent : (I ⊔ J).radical = IsLocalRing.maximalIdeal A) :
    (Module.length A (((Tor (ModuleCat.{u} A) 0).obj (ModuleCat.of A (A ⧸ I))).obj
        (ModuleCat.of A (A ⧸ J)))).toNat =
      (Module.length A (A ⧸ (I ⊔ J))).toNat :=
  length_tor_zero_toNat_eq_length_quotient_sup_of_tor_subsingleton I J
    (Ideal.tor_subsingleton_of_isCohenMacaulayLocalRing I J hI hJ hproper hcomponent)

/-- **The cycle identity of Tag 0B02 under vanishing of the higher Tor modules.** Let `Y` be a
regular scheme of dimension at most `d` and let `V`, `W` be sheaves of ideals such that at each
point `z` of delta-dimension `k` lying on both of them `Tor_i^{𝒪_{Y, z}}(𝒪_{V, z}, 𝒪_{W, z}) = 0`
for every `i > 0`. Then the `k`-cycle of the structure sheaf of the scheme-theoretic
intersection, cut out by `V ⊔ W`, is the Tor-formula intersection product of `V` and `W`: only
`Tor_0 = 𝒪_{V ∩ W}` contributes. The Cohen-Macaulay hypotheses of Tag 0B02 are one way of
getting the vanishing (`subschemeCycle_sup_eq_intersectionProductCycle_of_isCohenMacaulay`);
Tor independence of the two closed subschemes is another. -/
theorem subschemeCycle_sup_eq_intersectionProductCycle_of_tor_subsingleton
    (C : Stacks.Chow.ChowSituation.{u}) (f : Y ⟶ C.S) [LocallyOfFiniteType f]
    [IsLocallyNoetherian Y] (hY : IsRegular Y) (V W : Y.IdealSheafData) (k : ℤ)
    (d : ℕ) (hd : topologicalKrullDim Y ≤ (d : WithBot ℕ∞))
    (hVW : Stacks.Chow.schemeDeltaDimension C
      ((Stacks.Chow.reducedSupport (subschemeStructureSheaf (V ⊔ W))).subschemeι ≫ f) ≤
        WithBotTop.coe k)
    (hFk : ∀ i : ℕ,
      haveI := isCoherent_torSheaf_of_isRegular Y hY (subschemeStructureSheaf V)
        (subschemeStructureSheaf W) (isCoherent_subschemeStructureSheaf V)
        (isCoherent_subschemeStructureSheaf W) i
      Stacks.Chow.schemeDeltaDimension C
        ((Stacks.Chow.reducedSupport
          (torSheaf Y (subschemeStructureSheaf V) (subschemeStructureSheaf W) i)).subschemeι ≫ f)
        ≤ WithBotTop.coe k)
    (hTor : ∀ z : Y, Stacks.Chow.relativeDimension C.dimensionFunction f z = k →
      z ∈ V.support → z ∈ W.support → ∀ i : ℕ, 0 < i →
        Subsingleton (((Tor (ModuleCat.{u} (Y.presheaf.stalk z)) i).obj
          (ModuleCat.of (Y.presheaf.stalk z)
            (Y.presheaf.stalk z ⧸ IdealSheafData.stalk V z))).obj
          (ModuleCat.of (Y.presheaf.stalk z)
            (Y.presheaf.stalk z ⧸ IdealSheafData.stalk W z)))) :
    Stacks.Chow.coherentSheafCycle C f (subschemeStructureSheaf (V ⊔ W)) k hVW =
      intersectionProductCycle C f hY (subschemeStructureSheaf V) (subschemeStructureSheaf W)
        (isCoherent_subschemeStructureSheaf V) (isCoherent_subschemeStructureSheaf W) k hFk := by
  classical
  have hreg : ∀ y : Y, IsRegularLocalRing (Y.presheaf.stalk y) :=
    fun y => AlgebraicGeometry.IsRegular.isRegularLocalRing_stalk hY y
  apply Function.locallyFinsuppWithin.ext
  intro z
  rw [intersectionProductCycle_apply C f hY (subschemeStructureSheaf V)
    (subschemeStructureSheaf W) (isCoherent_subschemeStructureSheaf V)
    (isCoherent_subschemeStructureSheaf W) k hFk hreg d hd z]
  by_cases hz : Stacks.Chow.relativeDimension C.dimensionFunction f z = k
  · by_cases hmem : z ∈ V.support ∧ z ∈ W.support
    · obtain ⟨hzV, hzW⟩ := hmem
      have hTz := hTor z hz hzV hzW
      have hzVW : z ∈ (V ⊔ W).support := by
        rw [Scheme.IdealSheafData.support_sup]; exact ⟨hzV, hzW⟩
      -- the left-hand coefficient
      have hlhs : Stacks.Chow.coherentSheafCycle C f (subschemeStructureSheaf (V ⊔ W)) k hVW z =
          (Module.length (Y.presheaf.stalk z)
            (Y.presheaf.stalk z ⧸ IdealSheafData.stalk (V ⊔ W) z)).toNat := by
        refine Eq.trans ?_ (sheafMultiplicity_subschemeStructureSheaf (V ⊔ W) z hzVW)
        exact Stacks.Chow.cycleAssociatedToCoherentSheaf_apply_of_relativeDimension_eq C f
          (subschemeStructureSheaf (V ⊔ W)) k hVW hz
      -- the right-hand coefficients
      have hrhs : ∀ i : ℕ,
          (have := isCoherent_torSheaf_of_isRegular Y hY (subschemeStructureSheaf V)
            (subschemeStructureSheaf W) (isCoherent_subschemeStructureSheaf V)
            (isCoherent_subschemeStructureSheaf W) i
           Stacks.Chow.sheafCycleCoeff C f
             (torSheaf Y (subschemeStructureSheaf V) (subschemeStructureSheaf W) i) k z)
          = (Module.length (Y.presheaf.stalk z)
              (((Tor (ModuleCat.{u} (Y.presheaf.stalk z)) i).obj
                  (ModuleCat.of (Y.presheaf.stalk z)
                    (Y.presheaf.stalk z ⧸ IdealSheafData.stalk V z))).obj
                (ModuleCat.of (Y.presheaf.stalk z)
                  (Y.presheaf.stalk z ⧸ IdealSheafData.stalk W z)))).toNat := by
        intro i
        have := isCoherent_torSheaf_of_isRegular Y hY (subschemeStructureSheaf V)
          (subschemeStructureSheaf W) (isCoherent_subschemeStructureSheaf V)
          (isCoherent_subschemeStructureSheaf W) i
        refine Eq.trans (Stacks.Chow.cycleAssociatedToCoherentSheaf_apply_of_relativeDimension_eq
          C f (torSheaf Y (subschemeStructureSheaf V) (subschemeStructureSheaf W) i) k
          (hFk i) hz) ?_
        exact sheafMultiplicity_torSheaf_subschemeStructureSheaf V W i z hzV hzW
      rw [hlhs, Finset.sum_congr rfl (fun i _ => by rw [hrhs i]),
        AlgebraicGeometry.IdealSheafData.stalk_sup]
      rw [Finset.sum_eq_single 0]
      · rw [length_tor_zero_toNat_eq_length_quotient_sup_of_tor_subsingleton
          (IdealSheafData.stalk V z) (IdealSheafData.stalk W z) hTz]
        simp
      · intro i _ hi0
        rw [Module.length_eq_zero_iff.mpr (hTz i (Nat.pos_of_ne_zero hi0))]
        simp
      · intro h
        exact absurd (Finset.mem_range.mpr (by omega)) h
    · -- a point of delta-dimension `k` off `V` or off `W`: both coefficients vanish
      have hnot : z ∉ SheafOfModules.supp (subschemeStructureSheaf V) ∨
          z ∉ SheafOfModules.supp (subschemeStructureSheaf W) := by
        rw [supp_subschemeStructureSheaf, supp_subschemeStructureSheaf]
        exact not_and_or.mp hmem
      have hlhs : Stacks.Chow.coherentSheafCycle C f (subschemeStructureSheaf (V ⊔ W)) k hVW z
          = 0 := by
        refine Eq.trans (Stacks.Chow.cycleAssociatedToCoherentSheaf_apply_of_relativeDimension_eq
          C f (subschemeStructureSheaf (V ⊔ W)) k hVW hz) ?_
        refine Stacks.Chow.sheafMultiplicity_eq_zero_of_notMem_supp _ ?_
        rw [supp_subschemeStructureSheaf, Scheme.IdealSheafData.support_sup]
        exact hmem
      rw [hlhs]
      refine (Finset.sum_eq_zero fun i _ => ?_).symm
      have := isCoherent_torSheaf_of_isRegular Y hY (subschemeStructureSheaf V)
        (subschemeStructureSheaf W) (isCoherent_subschemeStructureSheaf V)
        (isCoherent_subschemeStructureSheaf W) i
      refine mul_eq_zero_of_right _ ?_
      refine Eq.trans (Stacks.Chow.cycleAssociatedToCoherentSheaf_apply_of_relativeDimension_eq
        C f (torSheaf Y (subschemeStructureSheaf V) (subschemeStructureSheaf W) i) k
        (hFk i) hz) ?_
      refine Stacks.Chow.sheafMultiplicity_eq_zero_of_notMem_supp _ fun hsupp => ?_
      have hinter := supp_torSheaf_subset_inter Y (subschemeStructureSheaf V)
        (subschemeStructureSheaf W) i hsupp
      exact hnot.elim (fun h => h hinter.1) fun h => h hinter.2
  · refine Eq.trans (Stacks.Chow.cycleAssociatedToCoherentSheaf_apply_of_relativeDimension_ne C f
      (subschemeStructureSheaf (V ⊔ W)) k hVW hz) ?_
    refine (Finset.sum_eq_zero fun i _ => ?_).symm
    have := isCoherent_torSheaf_of_isRegular Y hY (subschemeStructureSheaf V)
      (subschemeStructureSheaf W) (isCoherent_subschemeStructureSheaf V)
      (isCoherent_subschemeStructureSheaf W) i
    exact mul_eq_zero_of_right _
      (Stacks.Chow.cycleAssociatedToCoherentSheaf_apply_of_relativeDimension_ne C f
        (torSheaf Y (subschemeStructureSheaf V) (subschemeStructureSheaf W) i) k (hFk i) hz)

/-- **Stacks 0B02, the cycle identity, through the structure sheaf of the intersection.** Let `Y`
be a regular scheme of dimension at most `d` and let `V`, `W` be sheaves of ideals which at each
point `z` of delta-dimension `k` lying on both of them cut out Cohen-Macaulay local rings
meeting properly, with `z` a generic point of `V ∩ W`. Then the `k`-cycle of the structure sheaf
of the scheme-theoretic intersection, cut out by `V ⊔ W`, is the Tor-formula intersection
product of `V` and `W`. -/
theorem subschemeCycle_sup_eq_intersectionProductCycle_of_isCohenMacaulay
    (C : Stacks.Chow.ChowSituation.{u}) (f : Y ⟶ C.S) [LocallyOfFiniteType f]
    [IsLocallyNoetherian Y] (hY : IsRegular Y) (V W : Y.IdealSheafData) (k : ℤ)
    (d : ℕ) (hd : topologicalKrullDim Y ≤ (d : WithBot ℕ∞))
    (hVW : Stacks.Chow.schemeDeltaDimension C
      ((Stacks.Chow.reducedSupport (subschemeStructureSheaf (V ⊔ W))).subschemeι ≫ f) ≤
        WithBotTop.coe k)
    (hFk : ∀ i : ℕ,
      haveI := isCoherent_torSheaf_of_isRegular Y hY (subschemeStructureSheaf V)
        (subschemeStructureSheaf W) (isCoherent_subschemeStructureSheaf V)
        (isCoherent_subschemeStructureSheaf W) i
      Stacks.Chow.schemeDeltaDimension C
        ((Stacks.Chow.reducedSupport
          (torSheaf Y (subschemeStructureSheaf V) (subschemeStructureSheaf W) i)).subschemeι ≫ f)
        ≤ WithBotTop.coe k)
    (hpt : ∀ z : Y, Stacks.Chow.relativeDimension C.dimensionFunction f z = k →
      ∀ (hzV : z ∈ V.support) (hzW : z ∈ W.support),
        haveI := isLocalRing_quotient_stalk V z hzV
        haveI := isLocalRing_quotient_stalk W z hzW
        IsCohenMacaulayLocalRing (Y.presheaf.stalk z ⧸ IdealSheafData.stalk V z) ∧
        IsCohenMacaulayLocalRing (Y.presheaf.stalk z ⧸ IdealSheafData.stalk W z) ∧
        ringKrullDim (Y.presheaf.stalk z) ≤
          ringKrullDim (Y.presheaf.stalk z ⧸ IdealSheafData.stalk V z) +
            ringKrullDim (Y.presheaf.stalk z ⧸ IdealSheafData.stalk W z) ∧
        (IdealSheafData.stalk V z ⊔ IdealSheafData.stalk W z).radical =
          IsLocalRing.maximalIdeal (Y.presheaf.stalk z)) :
    Stacks.Chow.coherentSheafCycle C f (subschemeStructureSheaf (V ⊔ W)) k hVW =
      intersectionProductCycle C f hY (subschemeStructureSheaf V) (subschemeStructureSheaf W)
        (isCoherent_subschemeStructureSheaf V) (isCoherent_subschemeStructureSheaf W) k hFk := by
  refine subschemeCycle_sup_eq_intersectionProductCycle_of_tor_subsingleton C f hY V W k d hd hVW
    hFk fun z hz hzV hzW => ?_
  have := AlgebraicGeometry.IsRegular.isRegularLocalRing_stalk hY z
  have := isLocalRing_quotient_stalk V z hzV
  have := isLocalRing_quotient_stalk W z hzW
  obtain ⟨hCMV, hCMW, hproper, hcomponent⟩ := hpt z hz hzV hzW
  exact Ideal.tor_subsingleton_of_isCohenMacaulayLocalRing (IdealSheafData.stalk V z)
    (IdealSheafData.stalk W z) hCMV hCMW hproper hcomponent

/-- **Stacks 0B02, the final clause: `V · W = [V ∩ W]_{dim V + dim W - dim X}`.** Let `Y` be a
regular scheme of dimension at most `d` and let `V`, `W` be sheaves of ideals which at each point
`z` of delta-dimension `k` lying on both of them cut out Cohen-Macaulay local rings meeting
properly, with `z` a generic point of `V ∩ W`. Then the `k`-cycle of the closed subscheme
`V ∩ W`, the scheme-theoretic intersection cut out by `V ⊔ W`, is the Tor-formula intersection
product of `V` and `W`.

For `Y` a nonsingular variety, `V` and `W` closed subvarieties intersecting properly which are
Cohen-Macaulay, and `k = dim V + dim W - dim Y`, the left-hand side is
`[V ∩ W]_{dim V + dim W - dim Y}` and the right-hand side is `V · W`.

This is the final `In particular` clause of Tag 0B02 on its own, as an identity of algebraic
cycles. The right-hand side is the Section 43.14 product of Tag 0AZR,
`AlgebraicGeometry.TorFormula.intersectionProductCycle`, which takes the delta-dimension bounds
`hFk` on the supports of the `Tor` sheaves exactly as the definition of that tag does. The
source's hypotheses are local at the generic point of a component of `V ∩ W`, and that is where
they are read here: at a point `z` of delta-dimension `k` lying on both subvarieties — which
under `hVW` is exactly a generic point of a component of `V ∩ W` — `𝒪_{V, z}` and `𝒪_{W, z}`
are Cohen-Macaulay, proper intersection is the dimension inequality of Tag 0B1I, and that `z`
is a generic point of `V ∩ W` is the radical condition. The tag is registered on the statement
of both of its clauses, this one together with the multiplicity formula
`e(X, V · W, Z) = length_{𝒪_{X, ξ}}(𝒪_{V ∩ W, ξ})`, in
`AlgebraicGeometry.TorFormula.cohenMacaulayIntersectionFormula`. -/
theorem cycleAssociatedToClosedSubscheme_eq_intersectionProductCycle_of_isCohenMacaulay
    (C : Stacks.Chow.ChowSituation.{u}) (f : Y ⟶ C.S) [LocallyOfFiniteType f]
    [IsLocallyNoetherian Y] (hY : IsRegular Y) (V W : Y.IdealSheafData) (k : ℤ)
    (d : ℕ) (hd : topologicalKrullDim Y ≤ (d : WithBot ℕ∞))
    (hVW : Stacks.Chow.schemeDeltaDimension C ((V ⊔ W).subschemeι ≫ f) ≤ (k : EInt))
    (hFk : ∀ i : ℕ,
      haveI := isCoherent_torSheaf_of_isRegular Y hY (subschemeStructureSheaf V)
        (subschemeStructureSheaf W) (isCoherent_subschemeStructureSheaf V)
        (isCoherent_subschemeStructureSheaf W) i
      Stacks.Chow.schemeDeltaDimension C
        ((Stacks.Chow.reducedSupport
          (torSheaf Y (subschemeStructureSheaf V) (subschemeStructureSheaf W) i)).subschemeι ≫ f)
        ≤ WithBotTop.coe k)
    (hpt : ∀ z : Y, Stacks.Chow.relativeDimension C.dimensionFunction f z = k →
      ∀ (hzV : z ∈ V.support) (hzW : z ∈ W.support),
        haveI := isLocalRing_quotient_stalk V z hzV
        haveI := isLocalRing_quotient_stalk W z hzW
        IsCohenMacaulayLocalRing (Y.presheaf.stalk z ⧸ IdealSheafData.stalk V z) ∧
        IsCohenMacaulayLocalRing (Y.presheaf.stalk z ⧸ IdealSheafData.stalk W z) ∧
        ringKrullDim (Y.presheaf.stalk z) ≤
          ringKrullDim (Y.presheaf.stalk z ⧸ IdealSheafData.stalk V z) +
            ringKrullDim (Y.presheaf.stalk z ⧸ IdealSheafData.stalk W z) ∧
        (IdealSheafData.stalk V z ⊔ IdealSheafData.stalk W z).radical =
          IsLocalRing.maximalIdeal (Y.presheaf.stalk z)) :
    (Stacks.Chow.cycleAssociatedToClosedSubscheme C f (V ⊔ W).subschemeι k).1 =
      intersectionProductCycle C f hY (subschemeStructureSheaf V) (subschemeStructureSheaf W)
        (isCoherent_subschemeStructureSheaf V) (isCoherent_subschemeStructureSheaf W) k hFk := by
  rw [Stacks.Chow.cycleAssociatedToClosedSubscheme_eq_cycleAssociatedToCoherentSheaf C f
    (V ⊔ W).subschemeι k hVW]
  exact subschemeCycle_sup_eq_intersectionProductCycle_of_isCohenMacaulay C f hY V W k d hd
    (Stacks.Chow.schemeDeltaDimension_reducedSupport_pushforwardStructureSheaf_le C f
      (V ⊔ W).subschemeι hVW) hFk hpt

/-- **The cycle identity of Tag 0B02 under vanishing of the higher Tor modules, with the
closed subscheme `V ∩ W`.** Let `Y` be a regular scheme of dimension at most `d` and let `V`, `W`
be sheaves of ideals such that at each point `z` of delta-dimension `k` lying on both of them
`Tor_i^{𝒪_{Y, z}}(𝒪_{V, z}, 𝒪_{W, z}) = 0` for every `i > 0`. Then the `k`-cycle of the closed
subscheme `V ∩ W` cut out by `V ⊔ W` is the Tor-formula intersection product of `V` and `W`. -/
theorem cycleAssociatedToClosedSubscheme_eq_intersectionProductCycle_of_tor_subsingleton
    (C : Stacks.Chow.ChowSituation.{u}) (f : Y ⟶ C.S) [LocallyOfFiniteType f]
    [IsLocallyNoetherian Y] (hY : IsRegular Y) (V W : Y.IdealSheafData) (k : ℤ)
    (d : ℕ) (hd : topologicalKrullDim Y ≤ (d : WithBot ℕ∞))
    (hVW : Stacks.Chow.schemeDeltaDimension C ((V ⊔ W).subschemeι ≫ f) ≤ (k : EInt))
    (hFk : ∀ i : ℕ,
      haveI := isCoherent_torSheaf_of_isRegular Y hY (subschemeStructureSheaf V)
        (subschemeStructureSheaf W) (isCoherent_subschemeStructureSheaf V)
        (isCoherent_subschemeStructureSheaf W) i
      Stacks.Chow.schemeDeltaDimension C
        ((Stacks.Chow.reducedSupport
          (torSheaf Y (subschemeStructureSheaf V) (subschemeStructureSheaf W) i)).subschemeι ≫ f)
        ≤ WithBotTop.coe k)
    (hTor : ∀ z : Y, Stacks.Chow.relativeDimension C.dimensionFunction f z = k →
      z ∈ V.support → z ∈ W.support → ∀ i : ℕ, 0 < i →
        Subsingleton (((Tor (ModuleCat.{u} (Y.presheaf.stalk z)) i).obj
          (ModuleCat.of (Y.presheaf.stalk z)
            (Y.presheaf.stalk z ⧸ IdealSheafData.stalk V z))).obj
          (ModuleCat.of (Y.presheaf.stalk z)
            (Y.presheaf.stalk z ⧸ IdealSheafData.stalk W z)))) :
    (Stacks.Chow.cycleAssociatedToClosedSubscheme C f (V ⊔ W).subschemeι k).1 =
      intersectionProductCycle C f hY (subschemeStructureSheaf V) (subschemeStructureSheaf W)
        (isCoherent_subschemeStructureSheaf V) (isCoherent_subschemeStructureSheaf W) k hFk := by
  rw [Stacks.Chow.cycleAssociatedToClosedSubscheme_eq_cycleAssociatedToCoherentSheaf C f
    (V ⊔ W).subschemeι k hVW]
  exact subschemeCycle_sup_eq_intersectionProductCycle_of_tor_subsingleton C f hY V W k d hd
    (Stacks.Chow.schemeDeltaDimension_reducedSupport_pushforwardStructureSheaf_le C f
      (V ⊔ W).subschemeι hVW) hFk hTor

/-! ### The whole of Stacks 0B02 -/

/-- **Stacks Project, Tag 0B02.** Let `X` be a nonsingular variety and `V`, `W ⊆ X` closed
subvarieties which intersect properly, let `Z` be an irreducible component of `V ∩ W` with
generic point `ξ`, and assume `𝒪_{V, ξ}` and `𝒪_{W, ξ}` are Cohen-Macaulay. Then

`e(X, V · W, Z) = length_{𝒪_{X, ξ}}(𝒪_{V ∩ W, ξ})`,

where `V ∩ W` is the scheme-theoretic intersection; and in particular, if both `V` and `W` are
Cohen-Macaulay, then `V · W = [V ∩ W]_{dim V + dim W - dim X}`.

The nonsingular variety is a regular scheme `Y` of dimension at most `d`, the two closed
subvarieties are sheaves of ideals `V` and `W`, and `ξ` is a point `z` of delta-dimension `k`
lying on both of them, which under `hVW` is exactly the generic point of a component of
`V ∩ W`. The multiplicity `e(X, V · W, Z)` is `Ideal.localIntersectionMultiplicity`, the
alternating sum of lengths of `Tor` modules by which Section 43.14 computes it, and
`𝒪_{V ∩ W, ξ}` is the stalk of the scheme-theoretic intersection, cut out by `V ⊔ W`. The
product `V · W` is the cycle `AlgebraicGeometry.TorFormula.intersectionProductCycle` of
Tag 0AZR. -/
@[stacks 0B02 "the whole lemma: both the multiplicity formula \
`e(X, V · W, Z) = length_{𝒪_{X, ξ}}(𝒪_{V ∩ W, ξ})` at the generic point of each component of \
`V ∩ W` and the source's final `In particular` clause, \
`V · W = [V ∩ W]_{dim V + dim W - dim X}`, as an identity of algebraic cycles. The nonsingular \
variety is a regular scheme `Y` of dimension at most `d`, the two closed subvarieties are \
sheaves of ideals `V` and `W`, and `V · W` is the Section 43.14 product of Tag 0AZR, \
`AlgebraicGeometry.TorFormula.intersectionProductCycle`, which takes the delta-dimension bounds \
`hFk` on the supports of the `Tor` sheaves exactly as the definition of that tag does. The \
source's hypotheses are local at the generic point `ξ` of a component of `V ∩ W`, and that is \
where they are read: at a point `z` of delta-dimension `k` lying on both subvarieties — which \
under `hVW` is exactly such a generic point — `𝒪_{V, z}` and `𝒪_{W, z}` are Cohen-Macaulay, \
proper intersection is the dimension inequality of Tag 0B1I, and that `z` is a generic point of \
`V ∩ W` is the radical condition. `e(X, V · W, Z)` is `Ideal.localIntersectionMultiplicity`, \
the alternating sum of lengths of `Tor` modules by which Section 43.14 computes the \
multiplicity, and `𝒪_{V ∩ W, ξ}` is the stalk at `z` of the scheme-theoretic intersection, cut \
out by `V ⊔ W`. `WithBot ℕ∞` has no subtraction, so the source's dimension index \
`dim V + dim W - dim X` is generalised to an arbitrary `k`, the index at which the two cycles \
are formed and whose relation to `V ∩ W` is the delta-dimension bound `hVW`."]
theorem cohenMacaulayIntersectionFormula
    (C : Stacks.Chow.ChowSituation.{u}) (f : Y ⟶ C.S) [LocallyOfFiniteType f]
    [IsLocallyNoetherian Y] (hY : IsRegular Y) (V W : Y.IdealSheafData) (k : ℤ)
    (d : ℕ) (hd : topologicalKrullDim Y ≤ (d : WithBot ℕ∞))
    (hVW : Stacks.Chow.schemeDeltaDimension C ((V ⊔ W).subschemeι ≫ f) ≤ (k : EInt))
    (hFk : ∀ i : ℕ,
      haveI := isCoherent_torSheaf_of_isRegular Y hY (subschemeStructureSheaf V)
        (subschemeStructureSheaf W) (isCoherent_subschemeStructureSheaf V)
        (isCoherent_subschemeStructureSheaf W) i
      Stacks.Chow.schemeDeltaDimension C
        ((Stacks.Chow.reducedSupport
          (torSheaf Y (subschemeStructureSheaf V) (subschemeStructureSheaf W) i)).subschemeι ≫ f)
        ≤ WithBotTop.coe k)
    (hpt : ∀ z : Y, Stacks.Chow.relativeDimension C.dimensionFunction f z = k →
      ∀ (hzV : z ∈ V.support) (hzW : z ∈ W.support),
        haveI := isLocalRing_quotient_stalk V z hzV
        haveI := isLocalRing_quotient_stalk W z hzW
        IsCohenMacaulayLocalRing (Y.presheaf.stalk z ⧸ IdealSheafData.stalk V z) ∧
        IsCohenMacaulayLocalRing (Y.presheaf.stalk z ⧸ IdealSheafData.stalk W z) ∧
        ringKrullDim (Y.presheaf.stalk z) ≤
          ringKrullDim (Y.presheaf.stalk z ⧸ IdealSheafData.stalk V z) +
            ringKrullDim (Y.presheaf.stalk z ⧸ IdealSheafData.stalk W z) ∧
        (IdealSheafData.stalk V z ⊔ IdealSheafData.stalk W z).radical =
          IsLocalRing.maximalIdeal (Y.presheaf.stalk z)) :
    (∀ z : Y, Stacks.Chow.relativeDimension C.dimensionFunction f z = k →
        z ∈ V.support → z ∈ W.support →
          (IdealSheafData.stalk V z).localIntersectionMultiplicity
              (Y.presheaf.stalk z ⧸ IdealSheafData.stalk W z) =
            ((Module.length (Y.presheaf.stalk z)
              (Y.presheaf.stalk z ⧸ IdealSheafData.stalk (V ⊔ W) z)).toNat : ℚ)) ∧
      (Stacks.Chow.cycleAssociatedToClosedSubscheme C f (V ⊔ W).subschemeι k).1 =
        intersectionProductCycle C f hY (subschemeStructureSheaf V) (subschemeStructureSheaf W)
          (isCoherent_subschemeStructureSheaf V) (isCoherent_subschemeStructureSheaf W) k hFk := by
  refine ⟨fun z hz hzV hzW => ?_,
    cycleAssociatedToClosedSubscheme_eq_intersectionProductCycle_of_isCohenMacaulay C f hY V W k
      d hd hVW hFk hpt⟩
  have := AlgebraicGeometry.IsRegular.isRegularLocalRing_stalk hY z
  have := isLocalRing_quotient_stalk V z hzV
  have := isLocalRing_quotient_stalk W z hzW
  obtain ⟨hCMV, hCMW, hproper, hcomponent⟩ := hpt z hz hzV hzW
  rw [AlgebraicGeometry.IdealSheafData.stalk_sup]
  exact Ideal.localIntersectionMultiplicity_eq_length_of_isCohenMacaulayLocalRing
    (IdealSheafData.stalk V z) (IdealSheafData.stalk W z) hCMV hCMW hproper hcomponent

end AlgebraicGeometry.TorFormula

end
