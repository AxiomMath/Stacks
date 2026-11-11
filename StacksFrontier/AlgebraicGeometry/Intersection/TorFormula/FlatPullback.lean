module

public import StacksFrontier.AlgebraicGeometry.Chow.CoherentCycle.ClosedSubscheme
public import StacksFrontier.AlgebraicGeometry.Chow.FieldSituation.FlatPullbackVariety
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.ModuleComposition
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.ModuleRestriction
public import StacksFrontier.AlgebraicGeometry.Intersection.ProperIntersections.FlatPullbackCycles
public import StacksFrontier.AlgebraicGeometry.Intersection.ReductionToDiagonal.ProperIntersection
public import StacksFrontier.AlgebraicGeometry.Intersection.TorFormula.IntersectionProductCycle

/-!
# Flat pullback and the intersection product of coherent sheaves

Let `f : X ⟶ Y` be a flat morphism of nonsingular varieties over a field and let
`e = dim X - dim Y`. For coherent `𝒪_Y`-modules `ℱ` and `𝒢` whose supports have dimension at
most `r` and `s` and meet in dimension at most `r + s - dim Y`, the cycles `[f^*ℱ]_{r+e}` and
`[f^*𝒢]_{s+e}` intersect properly, and the flat pullback of the intersection product of `ℱ` and
`𝒢` is the intersection product of their pullbacks:

`f^*(∑ᵢ (-1)ⁱ [Torᵢ^{𝒪_Y}(ℱ, 𝒢)]_k) = ∑ᵢ (-1)ⁱ [Torᵢ^{𝒪_X}(f^*ℱ, f^*𝒢)]_{k+e}`.

For `k = r + s - dim Y` the two sides are `f^*([ℱ]_r · [𝒢]_s)` and `[f^*ℱ]_{r+e} · [f^*𝒢]_{s+e}`.

## Main definitions

* `AlgebraicGeometry.TorFormula.intersectionProductCycleGroup` — the intersection product of two
  coherent sheaves as an element of the group `Z_k(X)` of `k`-cycles.

## Main results

* `Stacks.Chow.coherentSheafCycle_eq_of_iso` — isomorphic coherent sheaves have the same cycle.
* `AlgebraicGeometry.TorFormula.intersectionProductCycle_mem_cyclesOfDimension` — the
  intersection product is a `k`-cycle.
* `Stacks.Intersection.FlatPullback.intersectProperly_coherentSheafCycle_pullback` —
  the properness clause of Tag 0B0Y, the pulled-back cycles intersect properly.
* `Stacks.Intersection.FlatPullback.flatPullback_intersectionProductCycleGroup` — flat pullback
  commutes with the intersection product, given the Tor comparison `hTor`.

The whole of Tag 0B0Y is
`Stacks.Intersection.CycleFlatPullback.flatPullback_coherentSheafCycleProduct_integerDimension`.

## Implementation notes

Proper intersection is a condition on topological dimensions, so the properness clause needs the
dimension of an inverse image read topologically. That is the topological form of Stacks 02RE
part (1), `Stacks.Intersection.CycleFlatPullback.topologicalKrullDim_preimage_le`, imported from
`StacksFrontier.AlgebraicGeometry.Intersection.ProperIntersections.FlatPullbackCycles`. The
dimension of a possibly empty inverse image is `⊥`, which is why the empty case is separated.

The intersection product is `AlgebraicGeometry.TorFormula.intersectionProductCycle`, the
alternating sum of the cycles of the `Tor` sheaves; it is a `finsum` over `ℕ` whose support is
finite because the `Tor` sheaves vanish above the dimension of the ambient scheme. Flat pullback
is the homomorphism `Z_k(Y) ⟶ Z_{k+e}(X)` of `Stacks.Chow.flatPullback`, so it passes through
that finite sum, and on each summand it is the cycle identity
`Stacks.Chow.flatPullback_cycleAssociatedToCoherentSheaf_of_isVariety`. What remains after those
two steps is the comparison of `f^*Torᵢ^{𝒪_Y}(ℱ, 𝒢)` with `Torᵢ^{𝒪_X}(f^*ℱ, f^*𝒢)`, which is an
input `hTor` here: it is the monoidality of derived pullback together with the exactness of `f^*`
for flat `f`, proved as `AlgebraicGeometry.TorFormula.pullbackTorSheafIso` in
`StacksFrontier.AlgebraicGeometry.Intersection.TorFormula.FlatPullbackTorSheaf` and supplied in
`StacksFrontier.AlgebraicGeometry.Intersection.TorFormula.FlatPullbackTorComparison`. Given the
comparison, the cycles of the two sheaves agree because the cycle of a coherent sheaf depends only
on its support and on the lengths of its stalks, both invariant under isomorphism.

The relative dimension `e` is a natural number together with `dim X = dim Y + e`, as in
`Stacks.Chow.flatPullback_cycleAssociatedToCoherentSheaf_of_isVariety`, so that no subtraction of
extended dimensions occurs.

## References

* [Stacks Project, Lemma 43.21.1 (Tag 0B0Y)](https://stacks.math.columbia.edu/tag/0B0Y)
* [Stacks Project, Tag 079U](https://stacks.math.columbia.edu/tag/079U)
* [Stacks Project, Tag 02RE](https://stacks.math.columbia.edu/tag/02RE)
* [Stacks Project, Tag 0AZF](https://stacks.math.columbia.edu/tag/0AZF)
* [Stacks Project, Tag 0AZR](https://stacks.math.columbia.edu/tag/0AZR)
* [Stacks Project, Tag 0AZT](https://stacks.math.columbia.edu/tag/0AZT)
* [Stacks Project, Tag 0B0W](https://stacks.math.columbia.edu/tag/0B0W)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Stacks.Chow

/-! ### Cycles of isomorphic sheaves -/

/-- Isomorphic coherent sheaves have the same support, hence the same bound on its
delta-dimension. -/
theorem schemeDeltaDimension_reducedSupport_le_of_iso (C : ChowSituation.{u}) {X : Scheme.{u}}
    (p : X ⟶ C.S) [LocallyOfFiniteType p] {M N : X.Modules} [M.IsCoherent] [N.IsCoherent]
    (i : M ≅ N) (k : ℤ)
    (hM : schemeDeltaDimension C ((reducedSupport M).subschemeι ≫ p) ≤ (k : EInt)) :
    schemeDeltaDimension C ((reducedSupport N).subschemeι ≫ p) ≤ (k : EInt) := by
  rw [schemeDeltaDimension_reducedSupport_le_iff] at hM ⊢
  intro x hx
  exact hM x (by rwa [SheafOfModules.supp_eq_of_iso i])

/-- Isomorphic coherent sheaves have the same cycle: the coefficient of the cycle at a point is
determined by the support of the sheaf and by the length of its stalk, and an isomorphism changes
neither. -/
theorem coherentSheafCycle_eq_of_iso (C : ChowSituation.{u}) {X : Scheme.{u}} (p : X ⟶ C.S)
    [LocallyOfFiniteType p] {M N : X.Modules} [M.IsCoherent] [N.IsCoherent] (i : M ≅ N) (k : ℤ)
    (hM : schemeDeltaDimension C ((reducedSupport M).subschemeι ≫ p) ≤ (k : EInt))
    (hN : schemeDeltaDimension C ((reducedSupport N).subschemeι ≫ p) ≤ (k : EInt)) :
    coherentSheafCycle C p M k hM = coherentSheafCycle C p N k hN := by
  classical
  apply Function.locallyFinsuppWithin.ext
  intro x
  change sheafCycleCoeff C p M k x = sheafCycleCoeff C p N k x
  simp only [sheafCycleCoeff, SheafOfModules.supp_eq_of_iso i, sheafMultiplicity_eq_of_iso i]

/-- Isomorphic coherent sheaves have the same associated `k`-cycle. -/
theorem cycleAssociatedToCoherentSheaf_eq_of_iso (C : ChowSituation.{u}) {X : Scheme.{u}}
    (p : X ⟶ C.S) [LocallyOfFiniteType p] {M N : X.Modules} [M.IsCoherent] [N.IsCoherent]
    (i : M ≅ N) (k : ℤ)
    (hM : schemeDeltaDimension C ((reducedSupport M).subschemeι ≫ p) ≤ (k : EInt))
    (hN : schemeDeltaDimension C ((reducedSupport N).subschemeι ≫ p) ≤ (k : EInt)) :
    cycleAssociatedToCoherentSheaf C p M k hM = cycleAssociatedToCoherentSheaf C p N k hN :=
  Subtype.ext (coherentSheafCycle_eq_of_iso C p i k hM hN)

end Stacks.Chow

namespace AlgebraicGeometry.TorFormula

open Stacks.Chow

attribute [local instance 100000] HasDerivedCategory.standard

/-! ### The intersection product as a `k`-cycle -/

/-- **Stacks 0AZR.** The intersection product of two coherent sheaves is a `k`-cycle: each of its
summands is one, and the `k`-cycles form a subgroup. -/
theorem intersectionProductCycle_mem_cyclesOfDimension (C : Stacks.Chow.ChowSituation.{u})
    {X : Scheme.{u}} (p : X ⟶ C.S) [LocallyOfFiniteType p] (hX : IsRegular X) (F G : X.Modules)
    (hF : SheafOfModules.IsCoherent F) (hG : SheafOfModules.IsCoherent G) (k : ℤ)
    (hFk : ∀ i : ℕ,
      haveI := isCoherent_torSheaf_of_isRegular X hX F G hF hG i
      schemeDeltaDimension C
        ((reducedSupport (torSheaf X F G i)).subschemeι ≫ p) ≤ (k : EInt)) :
    intersectionProductCycle C p hX F G hF hG k hFk ∈ cyclesOfDimension C p k := by
  rw [intersectionProductCycle]
  refine finsum_induction _ (AddSubgroup.zero_mem _)
    (fun a b ha hb ↦ AddSubgroup.add_mem _ ha hb) fun i ↦ ?_
  have := isCoherent_torSheaf_of_isRegular X hX F G hF hG i
  exact AddSubgroup.zsmul_mem _
    (coherentSheafCycle_mem_cyclesOfDimension C p (torSheaf X F G i) k (hFk i)) _

/-- **Stacks 0AZR.** The intersection product `∑ᵢ (-1)ⁱ [Torᵢ^{𝒪_X}(ℱ, 𝒢)]_k` of two coherent
sheaves on a regular scheme, as an element of the group `Z_k(X)` of `k`-cycles. -/
def intersectionProductCycleGroup (C : Stacks.Chow.ChowSituation.{u}) {X : Scheme.{u}}
    (p : X ⟶ C.S) [LocallyOfFiniteType p] (hX : IsRegular X) (F G : X.Modules)
    (hF : SheafOfModules.IsCoherent F) (hG : SheafOfModules.IsCoherent G) (k : ℤ)
    (hFk : ∀ i : ℕ,
      haveI := isCoherent_torSheaf_of_isRegular X hX F G hF hG i
      schemeDeltaDimension C
        ((reducedSupport (torSheaf X F G i)).subschemeι ≫ p) ≤ (k : EInt)) :
    CycleGroup C p k :=
  ⟨intersectionProductCycle C p hX F G hF hG k hFk,
    intersectionProductCycle_mem_cyclesOfDimension C p hX F G hF hG k hFk⟩

/-- The intersection product, read in `Z_k(X)`, is the alternating sum of the `k`-cycles of the
`Tor` sheaves. -/
theorem intersectionProductCycleGroup_eq_finsum (C : Stacks.Chow.ChowSituation.{u})
    {X : Scheme.{u}} (p : X ⟶ C.S) [LocallyOfFiniteType p] (hX : IsRegular X) (F G : X.Modules)
    (hF : SheafOfModules.IsCoherent F) (hG : SheafOfModules.IsCoherent G) (k : ℤ)
    (hFk : ∀ i : ℕ,
      haveI := isCoherent_torSheaf_of_isRegular X hX F G hF hG i
      schemeDeltaDimension C
        ((reducedSupport (torSheaf X F G i)).subschemeι ≫ p) ≤ (k : EInt))
    (hfin : Function.HasFiniteSupport fun i : ℕ => ((-1 : ℤ) ^ i) •
      (haveI := isCoherent_torSheaf_of_isRegular X hX F G hF hG i
       cycleAssociatedToCoherentSheaf C p (torSheaf X F G i) k (hFk i))) :
    intersectionProductCycleGroup C p hX F G hF hG k hFk =
      ∑ᶠ i : ℕ, ((-1 : ℤ) ^ i) •
        (haveI := isCoherent_torSheaf_of_isRegular X hX F G hF hG i
         cycleAssociatedToCoherentSheaf C p (torSheaf X F G i) k (hFk i)) :=
  Subtype.ext (AddMonoidHom.map_finsum (cyclesOfDimension C p k).subtype hfin).symm

end AlgebraicGeometry.TorFormula

namespace Stacks.Intersection.FlatPullback

open Stacks.Chow AlgebraicGeometry.TorFormula

attribute [local instance 100000] HasDerivedCategory.standard

/-! ### The dimension of an inverse image -/

/-- Solving for a natural number: a value of `WithBot ℕ∞` which is not `⊥` and is bounded by a
natural number is a natural number no larger than that bound. -/
theorem exists_natCast_eq_of_le_natCast {x : WithBot ℕ∞} {m : ℕ} (hbot : x ≠ ⊥)
    (hle : x ≤ (m : WithBot ℕ∞)) : ∃ nx : ℕ, x = (nx : WithBot ℕ∞) ∧ nx ≤ m := by
  obtain ⟨y, hy⟩ := WithBot.ne_bot_iff_exists.mp hbot
  have hy' : y ≤ (m : ℕ∞) := by rw [← hy] at hle; exact_mod_cast hle
  have hytop : y ≠ ⊤ := fun h => by simp [h] at hy'
  obtain ⟨nx, hnx⟩ := WithTop.ne_top_iff_exists.mp hytop
  refine ⟨nx, by rw [← hy, ← hnx]; rfl, ?_⟩
  rw [← hnx] at hy'
  exact Nat.cast_le.mp hy'

/-! ### Tag 0B0Y: proper intersection after pullback -/

/-- **The properness clause of Stacks 0B0Y.** Let `f : X ⟶ Y` be a flat morphism of varieties over a
field with `dim X = dim Y + e`, and let `ℱ` and `𝒢` be coherent `𝒪_Y`-modules whose supports have
dimension at most `r` and `s` and meet in dimension at most `r + s - dim Y`. Then the cycles
`[f^*ℱ]_{r+e}` and `[f^*𝒢]_{s+e}` intersect properly. The whole of Tag 0B0Y is
`Stacks.Intersection.CycleFlatPullback.flatPullback_coherentSheafCycleProduct_integerDimension`. -/
theorem intersectProperly_coherentSheafCycle_pullback (K : Type u) [Field K] {X Y : Scheme.{u}}
    (sX : X ⟶ Spec (.of K)) (sY : Y ⟶ Spec (.of K)) [IsVariety K sX] [IsVariety K sY]
    (f : X ⟶ Y) [Flat f] (hbase : f ≫ sY = sX) (e : ℕ)
    (he : topologicalKrullDim X = topologicalKrullDim Y + (e : WithBot ℕ∞))
    (F G : Y.Modules) [hF : F.IsCoherent] [hG : G.IsCoherent] (r s : ℕ)
    (hFr : schemeDeltaDimension (fieldChowSituation K)
      ((reducedSupport F).subschemeι ≫ sY) ≤ ((r : ℤ) : EInt))
    (hGs : schemeDeltaDimension (fieldChowSituation K)
      ((reducedSupport G).subschemeι ≫ sY) ≤ ((s : ℤ) : EInt))
    (hFG : topologicalKrullDim (SheafOfModules.supp F ∩ SheafOfModules.supp G : Set Y) +
      topologicalKrullDim Y ≤ (r : WithBot ℕ∞) + (s : WithBot ℕ∞)) :
    haveI : LocallyOfFiniteType f := locallyOfFiniteType_of_isVariety_comp K sX sY f hbase
    haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
    haveI : ((Scheme.Modules.pullback f).obj F).IsCoherent := isCoherent_pullback f F
    haveI : ((Scheme.Modules.pullback f).obj G).IsCoherent := isCoherent_pullback f G
    AlgebraicCycle.IntersectProperly
      (coherentSheafCycle (fieldChowSituation K) sX ((Scheme.Modules.pullback f).obj F)
        ((r + e : ℕ) : ℤ)
        (schemeDeltaDimension_support_pullback_le (fieldChowSituation K) sX sY f hbase e
          (relativeDimension_of_flat_of_isVariety K sX sY f hbase e he) F (r : ℤ) hFr))
      (coherentSheafCycle (fieldChowSituation K) sX ((Scheme.Modules.pullback f).obj G)
        ((s + e : ℕ) : ℤ)
        (schemeDeltaDimension_support_pullback_le (fieldChowSituation K) sX sY f hbase e
          (relativeDimension_of_flat_of_isVariety K sX sY f hbase e he) G (s : ℤ) hGs)) := by
  have hlft : LocallyOfFiniteType f := locallyOfFiniteType_of_isVariety_comp K sX sY f hbase
  have hlnX : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  have hcF : ((Scheme.Modules.pullback f).obj F).IsCoherent := isCoherent_pullback f F
  have hcG : ((Scheme.Modules.pullback f).obj G).IsCoherent := isCoherent_pullback f G
  have hftF : F.IsFiniteType := isFiniteType_of_isCoherent F
  have hftG : G.IsFiniteType := isFiniteType_of_isCoherent G
  refine Stacks.Intersection.ReductionToDiagonal.intersectProperly_coherentSheafCycle K sX
    ((Scheme.Modules.pullback f).obj F) ((Scheme.Modules.pullback f).obj G) (r + e) (s + e)
    _ _ ?_
  have hinter : (SheafOfModules.supp ((Scheme.Modules.pullback f).obj F) ∩
      SheafOfModules.supp ((Scheme.Modules.pullback f).obj G) : Set X) =
      f.base ⁻¹' (SheafOfModules.supp F ∩ SheafOfModules.supp G : Set Y) := by
    rw [Stacks.Modules.supp_pullback f F, Stacks.Modules.supp_pullback f G, Set.preimage_inter]
  rw [hinter]
  obtain ⟨dY, hdY⟩ := exists_topologicalKrullDim_eq_natCast_of_isVariety K sY
  have hTclosed : IsClosed (SheafOfModules.supp F ∩ SheafOfModules.supp G : Set Y) :=
    (SheafOfModules.isClosed_supp F).inter (SheafOfModules.isClosed_supp G)
  by_cases hempty : IsEmpty (SheafOfModules.supp F ∩ SheafOfModules.supp G : Set Y)
  · have hpre : IsEmpty ↥(f.base ⁻¹' (SheafOfModules.supp F ∩ SheafOfModules.supp G : Set Y)) :=
      ⟨fun x => hempty.elim ⟨f.base x.1, x.2⟩⟩
    rw [(topologicalKrullDim_eq_bot_iff_isEmpty _).2 hpre]
    simp
  · have hTbot : topologicalKrullDim
        (SheafOfModules.supp F ∩ SheafOfModules.supp G : Set Y) ≠ ⊥ := fun h =>
      hempty ((topologicalKrullDim_eq_bot_iff_isEmpty _).1 h)
    have hTle : topologicalKrullDim
        (SheafOfModules.supp F ∩ SheafOfModules.supp G : Set Y) ≤ (dY : WithBot ℕ∞) := by
      rw [← hdY]
      exact topologicalKrullDim_subspace_le Y _
    obtain ⟨nT, hnT, hnTle⟩ := exists_natCast_eq_of_le_natCast hTbot hTle
    have hsum : nT + dY ≤ r + s := by
      rw [hnT, hdY] at hFG
      exact_mod_cast hFG
    have hdimX : topologicalKrullDim X = ((dY + e : ℕ) : WithBot ℕ∞) := by
      rw [he, hdY]; push_cast; rfl
    have hpre : topologicalKrullDim
        (f.base ⁻¹' (SheafOfModules.supp F ∩ SheafOfModules.supp G : Set Y)) ≤
          ((nT + e : ℕ) : WithBot ℕ∞) :=
      CycleFlatPullback.topologicalKrullDim_preimage_le K sX sY f hbase e he
        ⟨(SheafOfModules.supp F ∩ SheafOfModules.supp G : Set Y), hTclosed⟩ nT (le_of_eq hnT)
    rw [hdimX]
    refine le_trans (add_le_add hpre (le_refl _)) ?_
    rw [← Nat.cast_add, ← Nat.cast_add]
    exact Nat.cast_le.mpr (by omega)

/-! ### Tag 0B0Y: flat pullback of the intersection product -/

/-- The dimension bound that the intersection product of the pulled-back sheaves needs: the
support of `Torᵢ^{𝒪_X}(f^*ℱ, f^*𝒢)` has delta-dimension at most `k + e`. It is the bound for the
support of `f^*Torᵢ^{𝒪_Y}(ℱ, 𝒢)`, which is Stacks 02RE part (2), transported along `hTor`. -/
theorem schemeDeltaDimension_reducedSupport_torSheaf_pullback_le (K : Type u) [Field K]
    {X Y : Scheme.{u}} (sX : X ⟶ Spec (.of K)) (sY : Y ⟶ Spec (.of K))
    [IsVariety K sX] [IsVariety K sY] (hX : AlgebraicGeometry.IsRegular X)
    (hY : AlgebraicGeometry.IsRegular Y) (f : X ⟶ Y) [Flat f] (hbase : f ≫ sY = sX) (e : ℕ)
    (he : topologicalKrullDim X = topologicalKrullDim Y + (e : WithBot ℕ∞))
    (F G : Y.Modules) (hF : _root_.SheafOfModules.IsCoherent F)
    (hG : _root_.SheafOfModules.IsCoherent G) (k : ℤ)
    (hFk : ∀ i : ℕ,
      haveI := isCoherent_torSheaf_of_isRegular Y hY F G hF hG i
      schemeDeltaDimension (fieldChowSituation K)
        ((reducedSupport (torSheaf Y F G i)).subschemeι ≫ sY) ≤ (k : EInt))
    (hTor : ∀ i : ℕ,
      haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
      (Scheme.Modules.pullback f).obj (torSheaf Y F G i) ≅
        torSheaf X ((Scheme.Modules.pullback f).obj F)
          ((Scheme.Modules.pullback f).obj G) i)
    (i : ℕ) :
    haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
    haveI := isCoherent_torSheaf_of_isRegular X hX ((Scheme.Modules.pullback f).obj F)
      ((Scheme.Modules.pullback f).obj G) (isCoherent_pullback f F) (isCoherent_pullback f G) i
    schemeDeltaDimension (fieldChowSituation K)
      ((reducedSupport (torSheaf X ((Scheme.Modules.pullback f).obj F)
        ((Scheme.Modules.pullback f).obj G) i)).subschemeι ≫ sX)
        ≤ ((k + (e : ℤ) : ℤ) : EInt) := by
  have : LocallyOfFiniteType f := locallyOfFiniteType_of_isVariety_comp K sX sY f hbase
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  have := isCoherent_torSheaf_of_isRegular Y hY F G hF hG i
  have := AlgebraicGeometry.isCoherent_pullback f (torSheaf Y F G i)
  have := isCoherent_torSheaf_of_isRegular X hX ((Scheme.Modules.pullback f).obj F)
    ((Scheme.Modules.pullback f).obj G) (isCoherent_pullback f F) (isCoherent_pullback f G) i
  exact schemeDeltaDimension_reducedSupport_le_of_iso (fieldChowSituation K) sX (hTor i)
    (k + (e : ℤ))
    (schemeDeltaDimension_support_pullback_le (fieldChowSituation K) sX sY f hbase e
      (relativeDimension_of_flat_of_isVariety K sX sY f hbase e he) (torSheaf Y F G i) k (hFk i))

/-- **Flat pullback of the intersection product, from the Tor comparison.** Let `f : X ⟶ Y` be a
flat morphism of nonsingular varieties over a field and let `e = dim X - dim Y`. For coherent
`𝒪_Y`-modules `ℱ` and `𝒢`, given the comparison `hTor`, the flat pullback of their intersection
product is the intersection product of their pullbacks:

`f^*(∑ᵢ (-1)ⁱ [Torᵢ^{𝒪_Y}(ℱ, 𝒢)]_k) = ∑ᵢ (-1)ⁱ [Torᵢ^{𝒪_X}(f^*ℱ, f^*𝒢)]_{k+e}`.

Taking `k = r + s - dim Y`, for supports of dimension at most `r` and `s`, this is
`f^*([ℱ]_r · [𝒢]_s) = [f^*ℱ]_{r+e} · [f^*𝒢]_{s+e}`. The comparison is
`AlgebraicGeometry.TorFormula.pullbackTorSheafIso`, and the identity with it supplied is
`Stacks.Intersection.FlatPullback.flatPullback_intersectionProductCycleGroup_eq_pullbackSheaves`. -/
theorem flatPullback_intersectionProductCycleGroup (K : Type u) [Field K] {X Y : Scheme.{u}}
    (sX : X ⟶ Spec (.of K)) (sY : Y ⟶ Spec (.of K)) [IsVariety K sX] [IsVariety K sY]
    (hX : AlgebraicGeometry.IsRegular X) (hY : AlgebraicGeometry.IsRegular Y) (f : X ⟶ Y)
    [Flat f] (hbase : f ≫ sY = sX) (e : ℕ)
    (he : topologicalKrullDim X = topologicalKrullDim Y + (e : WithBot ℕ∞))
    (F G : Y.Modules) (hF : _root_.SheafOfModules.IsCoherent F)
    (hG : _root_.SheafOfModules.IsCoherent G) (k : ℤ)
    (hFk : ∀ i : ℕ,
      haveI := isCoherent_torSheaf_of_isRegular Y hY F G hF hG i
      schemeDeltaDimension (fieldChowSituation K)
        ((reducedSupport (torSheaf Y F G i)).subschemeι ≫ sY) ≤ (k : EInt))
    (hTor : ∀ i : ℕ,
      haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
      (Scheme.Modules.pullback f).obj (torSheaf Y F G i) ≅
        torSheaf X ((Scheme.Modules.pullback f).obj F)
          ((Scheme.Modules.pullback f).obj G) i) :
    haveI : LocallyOfFiniteType f := locallyOfFiniteType_of_isVariety_comp K sX sY f hbase
    haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
    flatPullback (fieldChowSituation K) sX sY f hbase e
        (relativeDimension_of_flat_of_isVariety K sX sY f hbase e he) k
        (intersectionProductCycleGroup (fieldChowSituation K) sY hY F G hF hG k hFk) =
      intersectionProductCycleGroup (fieldChowSituation K) sX hX
        ((Scheme.Modules.pullback f).obj F) ((Scheme.Modules.pullback f).obj G)
        (isCoherent_pullback f F) (isCoherent_pullback f G) (k + (e : ℤ))
        (schemeDeltaDimension_reducedSupport_torSheaf_pullback_le K sX sY hX hY f hbase e he
          F G hF hG k hFk hTor) := by
  have hlft : LocallyOfFiniteType f := locallyOfFiniteType_of_isVariety_comp K sX sY f hbase
  have hln : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  have hregY : ∀ y : Y, IsRegularLocalRing (Y.presheaf.stalk y) :=
    ((isRegular_iff_regular_stalks Y).1 hY).2
  obtain ⟨dY, hdY⟩ := exists_topologicalKrullDim_eq_natCast_of_isVariety K sY
  have hFk' := schemeDeltaDimension_reducedSupport_torSheaf_pullback_le K sX sY hX hY f hbase e he
    F G hF hG k hFk hTor
  -- the two alternating sums have finitely many nonzero terms
  have hβfin : Function.HasFiniteSupport (fun i : ℕ => ((-1 : ℤ) ^ i) •
      (haveI := isCoherent_torSheaf_of_isRegular Y hY F G hF hG i
       cycleAssociatedToCoherentSheaf (fieldChowSituation K) sY (torSheaf Y F G i) k
         (hFk i))) := by
    refine Set.Finite.subset (Set.finite_Iic dY) fun i hi ↦ ?_
    by_contra hle
    refine hi (Subtype.ext ?_)
    exact torSheafCycle_eq_zero_of_lt (fieldChowSituation K) sY hY F G hF hG k hFk hregY dY
      (le_of_eq hdY) i (by simpa using hle)
  -- flat pullback of a summand is the corresponding summand upstairs
  have hterm : ∀ i : ℕ,
      flatPullback (fieldChowSituation K) sX sY f hbase e
          (relativeDimension_of_flat_of_isVariety K sX sY f hbase e he) k
          (((-1 : ℤ) ^ i) •
            (haveI := isCoherent_torSheaf_of_isRegular Y hY F G hF hG i
             cycleAssociatedToCoherentSheaf (fieldChowSituation K) sY (torSheaf Y F G i) k
               (hFk i))) =
        ((-1 : ℤ) ^ i) •
          (haveI := isCoherent_torSheaf_of_isRegular X hX ((Scheme.Modules.pullback f).obj F)
            ((Scheme.Modules.pullback f).obj G) (isCoherent_pullback f F)
            (isCoherent_pullback f G) i
           cycleAssociatedToCoherentSheaf (fieldChowSituation K) sX
             (torSheaf X ((Scheme.Modules.pullback f).obj F)
               ((Scheme.Modules.pullback f).obj G) i) (k + (e : ℤ)) (hFk' i)) := by
    intro i
    have hcY := isCoherent_torSheaf_of_isRegular Y hY F G hF hG i
    have hcP := AlgebraicGeometry.isCoherent_pullback f (torSheaf Y F G i)
    have hcX := isCoherent_torSheaf_of_isRegular X hX ((Scheme.Modules.pullback f).obj F)
      ((Scheme.Modules.pullback f).obj G) (isCoherent_pullback f F) (isCoherent_pullback f G) i
    rw [map_zsmul, flatPullback_cycleAssociatedToCoherentSheaf_of_isVariety K sX sY f hbase e he
      (torSheaf Y F G i) k (hFk i)]
    exact congrArg _ (cycleAssociatedToCoherentSheaf_eq_of_iso (fieldChowSituation K) sX
      (hTor i) (k + (e : ℤ)) _ (hFk' i))
  have hγfin : Function.HasFiniteSupport (fun i : ℕ => ((-1 : ℤ) ^ i) •
      (haveI := isCoherent_torSheaf_of_isRegular X hX ((Scheme.Modules.pullback f).obj F)
        ((Scheme.Modules.pullback f).obj G) (isCoherent_pullback f F)
        (isCoherent_pullback f G) i
       cycleAssociatedToCoherentSheaf (fieldChowSituation K) sX
         (torSheaf X ((Scheme.Modules.pullback f).obj F)
           ((Scheme.Modules.pullback f).obj G) i) (k + (e : ℤ)) (hFk' i))) := by
    refine Set.Finite.subset hβfin fun i hi ↦ ?_
    simp only [Function.mem_support] at hi ⊢
    intro h
    exact hi (by rw [← hterm i, h, map_zero])
  rw [intersectionProductCycleGroup_eq_finsum (fieldChowSituation K) sY hY F G hF hG k hFk hβfin,
    AddMonoidHom.map_finsum _ hβfin,
    intersectionProductCycleGroup_eq_finsum (fieldChowSituation K) sX hX
      ((Scheme.Modules.pullback f).obj F) ((Scheme.Modules.pullback f).obj G)
      (isCoherent_pullback f F) (isCoherent_pullback f G) (k + (e : ℤ)) hFk' hγfin]
  exact finsum_congr hterm

end Stacks.Intersection.FlatPullback

end
