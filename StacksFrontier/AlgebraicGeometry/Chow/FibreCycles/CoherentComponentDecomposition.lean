module

public import StacksFrontier.AlgebraicGeometry.Chow.CoherentCycle.ClosedSubscheme
public import StacksFrontier.AlgebraicGeometry.Chow.FibreCycles.CoherentFibreStalk
public import StacksFrontier.AlgebraicGeometry.Chow.FibreCycles.ComponentDecomposition

/-!
# The family of components of the support of a coherent sheaf on the family of projective lines

Let `f : X ⟶ S` be locally of finite type and let `F` be a coherent sheaf on `X ×_S 𝐏¹_S`. The
claim in the proof of Stacks Tag 02S6 compares the cycle of the restriction of `F` to a section
of the family with the cycles of the restrictions of the irreducible components of `Supp(F)` of
relative dimension `k + 1`, each repeated as often as its multiplicity in `[F]_{k+1}`.

This file constructs that family and proves the comparison for an arbitrary closed immersion
`g : X ⟶ X ×_S 𝐏¹_S` which is a section of the projection and whose ideal sheaf is locally
principal; the zero and the infinity section are the two instances the tag uses.

## Main definitions

* `Stacks.Chow.coherentComponentIndex` — the index type of the family: a generic point of a
  component of `Supp(F)` of relative dimension `k + 1`, together with a repetition index running
  over the multiplicity of `F` there.
* `Stacks.Chow.coherentComponentFamily` — the family itself, the reduced induced structure on the
  closure of the indexing point.

## Main results

* `Stacks.Chow.isIntegral_coherentComponentFamily`,
  `Stacks.Chow.relativeDimension_coherentComponentFamily`,
  `Stacks.Chow.locallyFinite_support_coherentComponentFamily`,
  `Stacks.Chow.not_range_coherentComponentFamily_subset_range` — the structural conditions of the
  decomposition for this family.
* `Stacks.Chow.cycleAssociatedToCoherentPullback_apply_eq_finsum_coherentComponentFamily` — the
  coefficient identity at a point of relative dimension `k`.

## Implementation notes

The index type reuses `Stacks.Chow.componentPoints` at the reduced support of `F`, so the local
finiteness of the closures of the indexing points is
`Stacks.Chow.locallyFinite_closure_componentPoints`, and the two reindexings of the local
identity are the ones Stacks Tag 02S5 uses: `Stacks.Chow.bijOn_fromSpecStalk_minimalPrimes` on
the side of the minimal primes of the stalk and
`Stacks.Chow.mem_componentGenericPointsThrough_subschemeι` with
`Stacks.Chow.exists_genericPoints_subschemeι_eq_of_mem_componentGenericPointsThrough` on the side
of the components. Only the local identity itself changes: the coefficient of the restricted
sheaf is the colength of a local equation on the stalk of `F`, which is
`Stacks.Chow.sheafMultiplicity_pullback_eq_toNat_finsum_minimal_support`, and the multiplicity of
a component is the length of a localized stalk, which is
`Stacks.Chow.length_localizedModule_stalk_eq_sheafMultiplicity`.

That the two fibres of `F` have delta-dimension at most `k` is used twice: to know that the point
where the coefficient is computed is a generic point of a component of the support of the
restriction, hence that the restricted stalk has finite length, and to know that no member of the
family lies inside the section.

## References

* [Stacks Project, Tag 02S6](https://stacks.math.columbia.edu/tag/02S6)
* [Stacks Project, Tag 02S5](https://stacks.math.columbia.edu/tag/02S5)
* [Stacks Project, Tag 02QG](https://stacks.math.columbia.edu/tag/02QG)
* [Stacks Project, Tag 02QW](https://stacks.math.columbia.edu/tag/02QW)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.Chow

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (f : X ⟶ C.S) [LocallyOfFiniteType f] (k : ℤ)
  (F : (projectiveLineProduct f).Modules) [F.IsCoherent]

/-! ### The family of components of the support -/

/-- The index type of the family of components of `Supp(F)` the proof of Stacks Tag 02S6 uses: a
generic point of an irreducible component of `Supp(F)` whose relative dimension over the base is
`k + 1`, together with a repetition index running over the multiplicity of `F` there.

A component where the multiplicity vanishes indexes an empty `Fin 0` and so contributes no
member, which is right: it does not occur in `[F]_{k+1}`. -/
abbrev coherentComponentIndex : Type u :=
  Σ η : componentPoints C f k (reducedSupport F),
    Fin (sheafMultiplicity F ((reducedSupport F).subschemeι η.1.1)).toNat

/-- The family of components of `Supp(F)` the proof of Stacks Tag 02S6 uses: at the index `η` it
is the reduced induced structure on the closure of `η`, an integral closed subscheme of
`X ×_S 𝐏¹_S`. -/
def coherentComponentFamily (j : coherentComponentIndex C f k F) :
    (projectiveLineProduct f).IdealSheafData :=
  integralComponentAt ((reducedSupport F).subschemeι j.1.1.1)

omit [LocallyOfFiniteType f] in
/-- The support of a member of the family is the closure of the point indexing it. -/
theorem coe_support_coherentComponentFamily (j : coherentComponentIndex C f k F) :
    ((coherentComponentFamily C f k F j).support : Set (projectiveLineProduct f)) =
      closure {(reducedSupport F).subschemeι j.1.1.1} :=
  coe_support_integralComponentAt _

omit [LocallyOfFiniteType f] in
/-- **Condition (1) of the decomposition.** Every member of the family is an integral closed
subscheme. -/
theorem isIntegral_coherentComponentFamily (j : coherentComponentIndex C f k F) :
    IsIntegral (coherentComponentFamily C f k F j).subscheme :=
  isIntegral_integralComponentAt _

omit [LocallyOfFiniteType f] in
/-- The canonical closed immersion of the reduced induced structure on the closure of a point
carries the generic point to that point. -/
theorem subschemeι_integralComponentAt_genericPoint {Y : Scheme.{u}} (y : Y)
    (ξ : genericPoints (integralComponentAt y).subscheme) :
    (integralComponentAt y).subschemeι ξ.1 = y := by
  have := isIntegral_integralComponentAt y
  have hcl : closure ({ξ.1} : Set (integralComponentAt y).subscheme) ∈
    irreducibleComponents (integralComponentAt y).subscheme := ξ.2
  rw [irreducibleComponents_eq_singleton, Set.mem_singleton_iff] at hcl
  have hg : IsGenericPoint ξ.1 (Set.univ : Set (integralComponentAt y).subscheme) := hcl
  rw [hg.eq (genericPoint_spec (integralComponentAt y).subscheme)]
  exact genericPointOf_integralComponentAt y

omit [LocallyOfFiniteType f] in
  /-- The relative dimension over the base at the point indexing a family member is `k + 1`. -/
  private theorem relativeDimension_subschemeι_componentPoints
      (η : componentPoints C f k (reducedSupport F)) :
      relativeDimension C.dimensionFunction
        (pullback.fst f (relativeProjectiveLine C.S ↘ C.S) ≫ f)
          ((reducedSupport F).subschemeι η.1.1) = k + 1 := by
    rw [← relativeDimension_comp_closedImmersion C.dimensionFunction (reducedSupport F).subschemeι
      (pullback.fst f (relativeProjectiveLine C.S ↘ C.S) ≫ f)]
    exact η.2

omit [LocallyOfFiniteType f] in
/-- **Condition (2) of the decomposition.** Every member of the family has relative dimension
`k + 1` over the base at each of its generic points: it is integral, so its only generic point
maps to the point indexing it, where the relative dimension of the support is `k + 1`. -/
theorem relativeDimension_coherentComponentFamily (j : coherentComponentIndex C f k F)
    (ξ : genericPoints (coherentComponentFamily C f k F j).subscheme) :
    relativeDimension C.dimensionFunction
      (familyBase f (coherentComponentFamily C f k F j)) ξ.1 = k + 1 := by
  rw [show familyBase f (coherentComponentFamily C f k F j) =
      (coherentComponentFamily C f k F j).subschemeι ≫
        pullback.fst f (relativeProjectiveLine C.S ↘ C.S) ≫ f from rfl,
    relativeDimension_comp_closedImmersion C.dimensionFunction
      (coherentComponentFamily C f k F j).subschemeι
      (pullback.fst f (relativeProjectiveLine C.S ↘ C.S) ≫ f) ξ.1,
    show (coherentComponentFamily C f k F j).subschemeι ξ.1 =
        (reducedSupport F).subschemeι j.1.1.1 from
      subschemeι_integralComponentAt_genericPoint _ ξ]
  exact relativeDimension_subschemeι_componentPoints C f k F j.1

omit [LocallyOfFiniteType f] in
/-- The point indexing a member of the family lies in the range of the canonical closed immersion
of that member. -/
theorem mem_range_subschemeι_coherentComponentFamily (j : coherentComponentIndex C f k F) :
    (reducedSupport F).subschemeι j.1.1.1 ∈
      Set.range (coherentComponentFamily C f k F j).subschemeι := by
  rw [Scheme.IdealSheafData.range_subschemeι, coe_support_coherentComponentFamily C f k F j]
  exact subset_closure rfl

omit [LocallyOfFiniteType f] in
  /-- Every point of the reduced support of `F` maps into the support of `F`. -/
  private theorem subschemeι_reducedSupport_mem_supp (ζ : (reducedSupport F).subscheme) :
      (reducedSupport F).subschemeι ζ ∈ SheafOfModules.supp F := by
    rw [← coe_support_reducedSupport F, ← Scheme.IdealSheafData.range_subschemeι]
    exact ⟨ζ, rfl⟩

omit [LocallyOfFiniteType f] in
/-- The point indexing a member of the family lies in the support of `F`. -/
theorem mem_support_subschemeι_coherentComponentFamily (j : coherentComponentIndex C f k F) :
    (reducedSupport F).subschemeι j.1.1.1 ∈
      ((reducedSupport F).support : Set (projectiveLineProduct f)) := by
  rw [← Scheme.IdealSheafData.range_subschemeι]
  exact ⟨j.1.1.1, rfl⟩

omit [LocallyOfFiniteType f] in
/-- The point indexing a member of the family lies in the support of `F`. -/
theorem mem_supp_subschemeι_coherentComponentFamily (j : coherentComponentIndex C f k F) :
    (reducedSupport F).subschemeι j.1.1.1 ∈ SheafOfModules.supp F :=
  subschemeι_reducedSupport_mem_supp C f F _

omit [LocallyOfFiniteType f] in
/-- The support of a member of the family is contained in the support of `F`. -/
theorem coe_support_coherentComponentFamily_subset (j : coherentComponentIndex C f k F) :
    ((coherentComponentFamily C f k F j).support : Set (projectiveLineProduct f)) ⊆
      SheafOfModules.supp F := by
  rw [coe_support_coherentComponentFamily C f k F j, ← coe_support_reducedSupport F]
  exact (reducedSupport F).support.2.closure_subset_iff.mpr (Set.singleton_subset_iff.mpr
    (mem_support_subschemeι_coherentComponentFamily C f k F j))

/-- **Condition (4) of the decomposition.** The family is locally finite: its supports are the
closures of the points indexing it, and the `Fin n` fibres of the index type are finite. -/
theorem locallyFinite_support_coherentComponentFamily :
    LocallyFinite fun j : coherentComponentIndex C f k F =>
      ((coherentComponentFamily C f k F j).support : Set (projectiveLineProduct f)) := by
  intro p
  obtain ⟨U, hU, hfin⟩ := locallyFinite_closure_componentPoints C f k (reducedSupport F) p
  refine ⟨U, hU, Set.Finite.subset (Set.Finite.biUnion
    (t := fun η : componentPoints C f k (reducedSupport F) => Set.range (Sigma.mk η)) hfin
    fun η _ => Set.finite_range _) ?_⟩
  intro j hj
  have hj' : (((coherentComponentFamily C f k F j).support :
      Set (projectiveLineProduct f)) ∩ U).Nonempty := hj
  refine Set.mem_iUnion₂.mpr ⟨j.1, ?_, j.2, rfl⟩
  show (closure {(reducedSupport F).subschemeι j.1.1.1} ∩ U).Nonempty
  rwa [← coe_support_coherentComponentFamily C f k F j]

/-- If the coefficient at `x` of the cycle of the inverse image of `W` along `g` is nonzero, then
`g x` lies in the support of `W`. -/
private theorem mem_support_of_cycleAssociatedToComap_apply_ne_zero
    (g : X ⟶ projectiveLineProduct f) (W : (projectiveLineProduct f).IdealSheafData) (x : X)
    (h : (cycleAssociatedToClosedSubscheme C f (W.comap g).subschemeι k).1 x ≠ 0) :
    g x ∈ (W.support : Set (projectiveLineProduct f)) := by
  have h1 : x ∈ ((W.comap g).support : Set X) := by
    rw [← Scheme.IdealSheafData.range_subschemeι]
    by_contra h'
    exact h (cycleAssociatedToClosedSubscheme_apply_eq_zero_of_notMem_range C f _ k h')
  rwa [Scheme.IdealSheafData.support_comap, Closeds.coe_preimage] at h1

/-! ### A delta-dimension bound on the support is a pointwise bound -/

/-- A bound on the delta-dimension of the reduced support of a coherent sheaf on `X` bounds the
relative dimension at every point of the support. -/
theorem relativeDimension_le_of_schemeDeltaDimension_reducedSupport_le {G : X.Modules}
    [G.IsCoherent] (h : schemeDeltaDimension C ((reducedSupport G).subschemeι ≫ f) ≤ (k : EInt))
    {y : X} (hy : y ∈ SheafOfModules.supp G) :
    relativeDimension C.dimensionFunction f y ≤ k := by
  obtain ⟨z, rfl⟩ : y ∈ Set.range (reducedSupport G).subschemeι := by
    rwa [Scheme.IdealSheafData.range_subschemeι, coe_support_reducedSupport]
  exact relativeDimension_le_of_schemeDeltaDimension_le C f _ h z

/-! ### The restriction of the family along a section of the projection -/

section Section

variable (g : X ⟶ projectiveLineProduct f) [IsClosedImmersion g]

omit [LocallyOfFiniteType f] [F.IsCoherent] in
/-- The relative dimension over the base at a point of the image of a section of the projection
is the relative dimension at the point below. -/
theorem relativeDimension_apply_of_section
    (hgf : g ≫ pullback.fst f (relativeProjectiveLine C.S ↘ C.S) ≫ f = f) (x : X) :
    relativeDimension C.dimensionFunction
        (pullback.fst f (relativeProjectiveLine C.S ↘ C.S) ≫ f) (g x) =
      relativeDimension C.dimensionFunction f x := by
  rw [← relativeDimension_comp_closedImmersion C.dimensionFunction g
    (pullback.fst f (relativeProjectiveLine C.S ↘ C.S) ≫ f) x, hgf]

omit [IsClosedImmersion g] in
/-- A member of the family attached to a point of the support of `F` inherits the bound on the
relative dimension of the support of the restriction of `F`: its points lie over points of that
support. -/
theorem schemeDeltaDimension_comap_integralComponentAt_le
    (hfib : ∀ y : X, y ∈ SheafOfModules.supp ((Scheme.Modules.pullback g).obj F) →
      relativeDimension C.dimensionFunction f y ≤ k)
    {η : projectiveLineProduct f} (hη : η ∈ SheafOfModules.supp F) :
    schemeDeltaDimension C (((integralComponentAt η).comap g).subschemeι ≫ f) ≤ (k : EInt) := by
  have _ : F.IsFiniteType := isFiniteType_of_isCoherent F
  refine schemeDeltaDimension_le_of_forall_relativeDimension_le C f _ fun z => ?_
  refine hfib _ ?_
  have hz : ((integralComponentAt η).comap g).subschemeι z ∈
      (((integralComponentAt η).comap g).support : Set X) := by
    rw [← Scheme.IdealSheafData.range_subschemeι]
    exact ⟨z, rfl⟩
  rw [Scheme.IdealSheafData.support_comap, Closeds.coe_preimage] at hz
  rw [Stacks.Modules.supp_pullback g F]
  refine coe_support_integralComponentAt_subset C f (reducedSupport F) ?_ hz
  rwa [coe_support_reducedSupport]

/-- The coefficient at `x` of the cycle of the inverse image of a closed subscheme `W` along `g`,
at a point `x` of relative dimension `k` whose image lies in the support of `W`: it is the
colength, in the local ring at that image, of the kernel of the stalk map of `g` together with
the stalk of the ideal sheaf of `W`. -/
theorem cycleAssociatedToComap_apply_eq_length_of_mem_support
    (W : (projectiveLineProduct f).IdealSheafData)
    (hW : schemeDeltaDimension C ((W.comap g).subschemeι ≫ f) ≤ (k : EInt))
    {x : X} (hx : relativeDimension C.dimensionFunction f x = k)
    (hxW : g x ∈ (W.support : Set (projectiveLineProduct f))) :
    (cycleAssociatedToClosedSubscheme C f (W.comap g).subschemeι k).1 x =
      ((Module.length ((projectiveLineProduct f).presheaf.stalk (g x))
        ((projectiveLineProduct f).presheaf.stalk (g x) ⧸
          (RingHom.ker (g.stalkMap x).hom ⊔ IdealSheafData.stalk W (g x)))).toNat : ℤ) := by
  have hxmem : x ∈ ((W.comap g).support : Set X) := by
    rwa [Scheme.IdealSheafData.support_comap, Closeds.coe_preimage]
  rw [← Scheme.IdealSheafData.range_subschemeι] at hxmem
  obtain ⟨y, hy⟩ := hxmem
  obtain ⟨ζ, hζ⟩ := exists_genericPoints_of_relativeDimension_eq C f
    (W.comap g).subschemeι k hW y (by rwa [hy])
  obtain rfl : (W.comap g).subschemeι ζ.1 = x := by rw [hζ, hy]
  exact cycleAssociatedToComap_apply_eq_length C f g W k ζ hx

/-- **The first factor of the local identity is a fibre coefficient of a component.** For a prime
`Q` of the local ring at `g x` containing the stalk of the ideal sheaf of the reduced support of
`F`, the colength of the kernel of the stalk map of `g` together with `Q` is the coefficient at
`x` of the cycle of the restriction along `g` of the integral closed subscheme supported on the
closure of the point corresponding to `Q`. -/
theorem length_quotient_ker_sup_eq_cycleAssociatedToComap_integralComponentAt
    (hfib : ∀ y : X, y ∈ SheafOfModules.supp ((Scheme.Modules.pullback g).obj F) →
      relativeDimension C.dimensionFunction f y ≤ k)
    {x : X} (hx : relativeDimension C.dimensionFunction f x = k)
    (Q : PrimeSpectrum ((projectiveLineProduct f).presheaf.stalk (g x)))
    (hQ : IdealSheafData.stalk (reducedSupport F) (g x) ≤ Q.asIdeal) :
    ((Module.length ((projectiveLineProduct f).presheaf.stalk (g x))
        ((projectiveLineProduct f).presheaf.stalk (g x) ⧸
          (RingHom.ker (g.stalkMap x).hom ⊔ Q.asIdeal))).toNat : ℤ) =
      (cycleAssociatedToClosedSubscheme C f
        ((integralComponentAt ((projectiveLineProduct f).fromSpecStalk (g x) Q)).comap
          g).subschemeι k).1 x := by
  have hηZ := (le_iff_fromSpecStalk_mem_support (reducedSupport F) (g x) Q).mp hQ
  have hηF : (projectiveLineProduct f).fromSpecStalk (g x) Q ∈ SheafOfModules.supp F := by
    rwa [coe_support_reducedSupport] at hηZ
  have hspec : (projectiveLineProduct f).fromSpecStalk (g x) Q ⤳ g x := by
    have hr : (projectiveLineProduct f).fromSpecStalk (g x) Q ∈
        Set.range ⇑((projectiveLineProduct f).fromSpecStalk (g x)) := ⟨Q, rfl⟩
    rwa [Scheme.range_fromSpecStalk] at hr
  have hxV : g x ∈ ((integralComponentAt
      ((projectiveLineProduct f).fromSpecStalk (g x) Q)).support :
        Set (projectiveLineProduct f)) := by
    rw [coe_support_integralComponentAt]
    exact hspec.mem_closure
  rw [cycleAssociatedToComap_apply_eq_length_of_mem_support C f k g _
    (schemeDeltaDimension_comap_integralComponentAt_le C f k F g hfib hηF) hx hxV,
    idealStalk_integralComponentAt_fromSpecStalk]

omit [LocallyOfFiniteType f] in
/-- **Condition (3) of the decomposition.** No member of the family is contained in the image of
`g`: the point `η` indexing it would then lie on that image, so the relative dimension of the
support of `F` at `η` would be the relative dimension of `X` at the point below, which the bound
on the restriction caps at `k`, contradicting `k + 1`. -/
theorem not_range_coherentComponentFamily_subset_range
    (hgf : g ≫ pullback.fst f (relativeProjectiveLine C.S ↘ C.S) ≫ f = f)
    (hfib : ∀ y : X, y ∈ SheafOfModules.supp ((Scheme.Modules.pullback g).obj F) →
      relativeDimension C.dimensionFunction f y ≤ k)
    (j : coherentComponentIndex C f k F) :
    ¬ Set.range (coherentComponentFamily C f k F j).subschemeι ⊆ Set.range g := by
  have _ : F.IsFiniteType := isFiniteType_of_isCoherent F
  intro hsub
  obtain ⟨y, hy⟩ := hsub (mem_range_subschemeι_coherentComponentFamily C f k F j)
  have hysupp : y ∈ SheafOfModules.supp ((Scheme.Modules.pullback g).obj F) := by
    rw [Stacks.Modules.supp_pullback g F, Set.mem_preimage, hy]
    exact mem_supp_subschemeι_coherentComponentFamily C f k F j
  have hle := hfib y hysupp
  have hdim := relativeDimension_subschemeι_componentPoints C f k F j.1
  rw [← hy, relativeDimension_apply_of_section C f g hgf y] at hdim
  omega

/-- A component generic point of the support of `F` through `g x`, for `x` of relative dimension
`k`, has relative dimension `k + 1` over the base.

It cannot be `g x` itself: that point would then be a maximal point of the support of `F`, hence
an associated point of `F`, which the hypothesis forbids. So it is a proper generalization, and
the dimension function drops strictly. -/
theorem relativeDimension_of_mem_componentGenericPointsThrough
    (hgf : g ≫ pullback.fst f (relativeProjectiveLine C.S ↘ C.S) ≫ f = f)
    (hSupp : ∀ ξ : projectiveLineProduct f, ξ ∈ SheafOfModules.supp F →
      relativeDimension C.dimensionFunction
        (pullback.fst f (relativeProjectiveLine C.S ↘ C.S) ≫ f) ξ ≤ k + 1)
    {x : X} (hx : relativeDimension C.dimensionFunction f x = k)
    (hassoc : g x ∉ Stacks.Divisors.associatedPoints F)
    {η : projectiveLineProduct f}
    (hη : η ∈ componentGenericPointsThrough (reducedSupport F) (g x))
    (w : genericPoints (reducedSupport F).subscheme)
    (hw : (reducedSupport F).subschemeι w.1 = η) :
    relativeDimension C.dimensionFunction (familyBase f (reducedSupport F)) w.1 = k + 1 := by
  have _ : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have _ : IsLocallyNoetherian (projectiveLineProduct f) :=
    LocallyOfFiniteType.isLocallyNoetherian
      (pullback.fst f (relativeProjectiveLine C.S ↘ C.S))
  have _ : F.IsQuasicoherent := isQuasicoherent_of_isCoherent F
  have hZ : ∀ ζ : (reducedSupport F).subscheme,
      relativeDimension C.dimensionFunction (familyBase f (reducedSupport F)) ζ ≤ k + 1 := by
    intro ζ
    rw [show familyBase f (reducedSupport F) = (reducedSupport F).subschemeι ≫
        pullback.fst f (relativeProjectiveLine C.S ↘ C.S) ≫ f from rfl,
      relativeDimension_comp_closedImmersion C.dimensionFunction (reducedSupport F).subschemeι
        (pullback.fst f (relativeProjectiveLine C.S ↘ C.S) ≫ f) ζ]
    exact hSupp _ (subschemeι_reducedSupport_mem_supp C f F ζ)
  have hηgx : η ≠ g x := by
    intro hηgx
    have hgxsupp : g x ∈ SheafOfModules.supp F := by
      simpa only [coe_support_reducedSupport, hηgx] using hη.1
    refine hassoc (mem_associatedPoints_of_mem_supp_of_specialization _ F (g x) hgxsupp ?_)
    intro y hy hyx
    have hy' : y ∈ ((reducedSupport F).support : Set (projectiveLineProduct f)) := by
      rwa [coe_support_reducedSupport]
    have := hη.2.2 y hy' (hηgx ▸ hyx)
    rwa [hηgx] at this
  have hne : (reducedSupport F).subschemeι w.1 ≠ g x := fun heq => hηgx (hw.symm.trans heq)
  exact relativeDimension_eq_succ_of_specializes C f k (reducedSupport F) hZ
    (by rwa [relativeDimension_apply_of_section C f g hgf x]) w.1
    (by rw [hw]; exact hη.2.1) hne

/-! ### The decomposition of the coefficient of the restriction -/

/-- The summand of the decomposition, as a function of the point of `X ×_S 𝐏¹_S` indexing a
component of the support of `F`: the multiplicity of `F` at that point times the coefficient at
`x` of the cycle of the restriction of that component along `g`.

Both reindexings of the local identity — along the minimal primes of the stalk and along the
generic points of the components — land on this one function, which is why it is written as a
function of a point of the family rather than of either index. -/
private def coherentComponentSummand (x : X) (η : projectiveLineProduct f) : ℤ :=
  sheafMultiplicity F η *
    (cycleAssociatedToClosedSubscheme C f ((integralComponentAt η).comap g).subschemeι k).1 x

/-- **The claim in the proof of Stacks Tag 02S6, along one section.** At every point `x` of `X`
of relative dimension `k` whose image is not an associated point of `F`, the coefficient of the
cycle of the restriction of `F` along `g` is the sum, over the family of components of `Supp(F)`
of relative dimension `k + 1`, of the coefficients of the cycles of their restrictions.

If `g x` lies outside the support of `F` then every term vanishes, the support of a member of the
family being contained in that of `F`. Otherwise the coefficient is the sum over the minimal
points of the support of the stalk of `F` at `g x`, and that sum is reindexed by the components
of `Supp(F)` through `g x`: each summand's first factor is the coefficient of the restriction of
the corresponding component and its second factor is the multiplicity of `F` there, which the
`Fin n` fibres of the index type turn into that many copies of the first. -/
theorem cycleAssociatedToCoherentPullback_apply_eq_finsum_coherentComponentFamily
    [((Scheme.Modules.pullback g).obj F).IsCoherent]
    (hgf : g ≫ pullback.fst f (relativeProjectiveLine C.S ↘ C.S) ≫ f = f)
    (hprin : ∀ y : X, ∃ t : (projectiveLineProduct f).presheaf.stalk (g y),
      RingHom.ker (g.stalkMap y).hom = Ideal.span {t})
    (hSupp : ∀ ξ : projectiveLineProduct f, ξ ∈ SheafOfModules.supp F →
      relativeDimension C.dimensionFunction
        (pullback.fst f (relativeProjectiveLine C.S ↘ C.S) ≫ f) ξ ≤ k + 1)
    (h₀ : schemeDeltaDimension C
      ((reducedSupport ((Scheme.Modules.pullback g).obj F)).subschemeι ≫ f) ≤ (k : EInt))
    {x : X} (hx : relativeDimension C.dimensionFunction f x = k)
    (hassoc : g x ∉ Stacks.Divisors.associatedPoints F) :
    (cycleAssociatedToCoherentSheaf C f ((Scheme.Modules.pullback g).obj F) k h₀).1 x =
      ∑ᶠ j : coherentComponentIndex C f k F,
        (cycleAssociatedToClosedSubscheme C f
          ((coherentComponentFamily C f k F j).comap g).subschemeι k).1 x := by
  classical
  have _ : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have _ : IsLocallyNoetherian (projectiveLineProduct f) :=
    LocallyOfFiniteType.isLocallyNoetherian
      (pullback.fst f (relativeProjectiveLine C.S ↘ C.S))
  have _ : F.IsFiniteType := isFiniteType_of_isCoherent F
  have _ : F.IsQuasicoherent := isQuasicoherent_of_isCoherent F
  have hfib : ∀ y : X, y ∈ SheafOfModules.supp ((Scheme.Modules.pullback g).obj F) →
      relativeDimension C.dimensionFunction f y ≤ k := fun _ hy =>
    relativeDimension_le_of_schemeDeltaDimension_reducedSupport_le C f k h₀ hy
  have hV : ∀ η : componentPoints C f k (reducedSupport F),
      (cycleAssociatedToClosedSubscheme C f
          ((integralComponentAt ((reducedSupport F).subschemeι η.1.1)).comap
            g).subschemeι k).1 x ≠ 0 →
      g x ∈ (closure {(reducedSupport F).subschemeι η.1.1} :
        Set (projectiveLineProduct f)) := by
    intro η hne
    have h2 := mem_support_of_cycleAssociatedToComap_apply_ne_zero C f k g _ x hne
    rwa [coe_support_integralComponentAt] at h2
  have hfam : ∀ j : coherentComponentIndex C f k F,
      (cycleAssociatedToClosedSubscheme C f
          ((coherentComponentFamily C f k F j).comap g).subschemeι k).1 x =
        (cycleAssociatedToClosedSubscheme C f
          ((integralComponentAt ((reducedSupport F).subschemeι j.1.1.1)).comap
            g).subschemeι k).1 x := fun _ => rfl
  by_cases hxF : g x ∈ SheafOfModules.supp F
  · have hxG : x ∈ SheafOfModules.supp ((Scheme.Modules.pullback g).obj F) := by
      rwa [Stacks.Modules.supp_pullback g F]
    obtain ⟨t, ht⟩ := hprin x
    obtain ⟨Zc, hZc⟩ := isGenericPoint_component_supp_of_relativeDimension_eq C f
      ((Scheme.Modules.pullback g).obj F) k x h₀ hxG hx
    have hfinlen := isFiniteLength_stalk_of_isGenericPoint_component_supp
      ((Scheme.Modules.pullback g).obj F) Zc x hZc
    have hcc : (Function.support fun η : componentPoints C f k (reducedSupport F) =>
        ((sheafMultiplicity F ((reducedSupport F).subschemeι η.1.1)).toNat : ℤ) *
          (cycleAssociatedToClosedSubscheme C f
            ((integralComponentAt ((reducedSupport F).subschemeι η.1.1)).comap
              g).subschemeι k).1 x).Finite :=
      ((locallyFinite_closure_componentPoints C f k (reducedSupport F)).point_finite
        (g x)).subset fun η hη => hV η (right_ne_zero_of_mul hη)
    have hmul : ∀ η : componentPoints C f k (reducedSupport F),
        ((sheafMultiplicity F ((reducedSupport F).subschemeι η.1.1)).toNat : ℤ) *
            (cycleAssociatedToClosedSubscheme C f
              ((integralComponentAt ((reducedSupport F).subschemeι η.1.1)).comap
                g).subschemeι k).1 x =
          coherentComponentSummand C f k F g x ((reducedSupport F).subschemeι η.1.1) := by
      intro η
      rw [coherentComponentSummand, sheafMultiplicity, Int.toNat_natCast]
    have hsigma : (∑ᶠ j : coherentComponentIndex C f k F,
          (cycleAssociatedToClosedSubscheme C f
            ((coherentComponentFamily C f k F j).comap g).subschemeι k).1 x) =
        ∑ᶠ η : componentPoints C f k (reducedSupport F),
          coherentComponentSummand C f k F g x ((reducedSupport F).subschemeι η.1.1) :=
      (finsum_congr hfam).trans
        ((finsum_sigma_fin_eq_finsum_mul _ hcc).trans (finsum_congr hmul))
    have hGsupp : ∀ η ∈ Function.support fun η : componentPoints C f k (reducedSupport F) =>
        coherentComponentSummand C f k F g x ((reducedSupport F).subschemeι η.1.1),
        (reducedSupport F).subschemeι η.1.1 ∈
          componentGenericPointsThrough (reducedSupport F) (g x) := by
      intro η hη
      refine mem_componentGenericPointsThrough_subschemeι C f (reducedSupport F) η.1
        (specializes_iff_mem_closure.mpr (hV η ?_))
      have hη' : coherentComponentSummand C f k F g x
        ((reducedSupport F).subschemeι η.1.1) ≠ 0 := hη
      rw [← hmul η] at hη'
      exact right_ne_zero_of_mul hη'
    have hstep₀ : (∑ᶠ η : componentPoints C f k (reducedSupport F),
          coherentComponentSummand C f k F g x ((reducedSupport F).subschemeι η.1.1)) =
        ∑ᶠ η ∈ {η : componentPoints C f k (reducedSupport F) |
            (reducedSupport F).subschemeι η.1.1 ∈
              componentGenericPointsThrough (reducedSupport F) (g x)},
          coherentComponentSummand C f k F g x ((reducedSupport F).subschemeι η.1.1) := by
      rw [← finsum_mem_univ fun η : componentPoints C f k (reducedSupport F) =>
        coherentComponentSummand C f k F g x ((reducedSupport F).subschemeι η.1.1)]
      exact finsum_mem_inter_support_eq' _ Set.univ _
        fun η hη => ⟨fun _ => hGsupp η hη, fun _ => trivial⟩
    have hbij₂ : Set.BijOn (fun η : componentPoints C f k (reducedSupport F) =>
        (reducedSupport F).subschemeι η.1.1)
        {η : componentPoints C f k (reducedSupport F) |
          (reducedSupport F).subschemeι η.1.1 ∈
            componentGenericPointsThrough (reducedSupport F) (g x)}
        (componentGenericPointsThrough (reducedSupport F) (g x)) := by
      refine ⟨fun η hη => hη, fun a _ b _ hab => Subtype.ext (Subtype.ext
        ((reducedSupport F).subschemeι.isClosedEmbedding.injective hab)), fun p hp => ?_⟩
      obtain ⟨w, hw⟩ :=
        exists_genericPoints_subschemeι_eq_of_mem_componentGenericPointsThrough C f
          (reducedSupport F) hp
      refine ⟨⟨w, relativeDimension_of_mem_componentGenericPointsThrough C f k F g hgf hSupp hx
        hassoc hp w hw⟩, ?_, hw⟩
      show (reducedSupport F).subschemeι w.1 ∈
        componentGenericPointsThrough (reducedSupport F) (g x)
      rwa [hw]
    have hstep₂ : (∑ᶠ η ∈ {η : componentPoints C f k (reducedSupport F) |
          (reducedSupport F).subschemeι η.1.1 ∈
            componentGenericPointsThrough (reducedSupport F) (g x)},
          coherentComponentSummand C f k F g x ((reducedSupport F).subschemeι η.1.1)) =
        ∑ᶠ p ∈ componentGenericPointsThrough (reducedSupport F) (g x),
          coherentComponentSummand C f k F g x p :=
      finsum_mem_eq_of_bijOn (fun η : componentPoints C f k (reducedSupport F) =>
        (reducedSupport F).subschemeι η.1.1) hbij₂ fun η _ => rfl
    have hval₁ : ∀ Q ∈ {Q : PrimeSpectrum ((projectiveLineProduct f).presheaf.stalk (g x)) |
          Q.asIdeal ∈ (IdealSheafData.stalk (reducedSupport F) (g x)).minimalPrimes},
        ((Module.length ((projectiveLineProduct f).presheaf.stalk (g x))
            ((projectiveLineProduct f).presheaf.stalk (g x) ⧸
              (Ideal.span {t} ⊔ Q.asIdeal))).toNat : ℤ) *
          ((Module.length (Localization.AtPrime Q.asIdeal)
            (LocalizedModule Q.asIdeal.primeCompl (F.presheaf.stalk (g x)))).toNat : ℤ) =
        coherentComponentSummand C f k F g x
          ((projectiveLineProduct f).fromSpecStalk (g x) Q) := by
      intro Q hQ
      have hQ' : IdealSheafData.stalk (reducedSupport F) (g x) ≤ Q.asIdeal := hQ.1.2
      have h2 := length_localizedModule_stalk_eq_sheafMultiplicity F Q
      rw [coherentComponentSummand, ← ht,
        length_quotient_ker_sup_eq_cycleAssociatedToComap_integralComponentAt C f k F g hfib hx
          Q hQ', ← h2]
      exact mul_comm _ _
    have hstep₁ := finsum_mem_eq_of_bijOn
      ⇑((projectiveLineProduct f).fromSpecStalk (g x))
      (bijOn_fromSpecStalk_minimalPrimes (reducedSupport F) (g x)) hval₁
    have hset : {Q : PrimeSpectrum ((projectiveLineProduct f).presheaf.stalk (g x)) |
          Minimal (· ∈ Module.support ((projectiveLineProduct f).presheaf.stalk (g x))
            (F.presheaf.stalk (g x))) Q} =
        {Q : PrimeSpectrum ((projectiveLineProduct f).presheaf.stalk (g x)) |
          Q.asIdeal ∈ (IdealSheafData.stalk (reducedSupport F) (g x)).minimalPrimes} :=
      Set.ext fun Q => minimal_moduleSupport_stalk_iff_mem_minimalPrimes_reducedSupport F Q
    rw [cycleAssociatedToCoherentSheaf_apply_of_relativeDimension_eq C f _ k h₀ hx,
      sheafMultiplicity_pullback_eq_toNat_finsum_minimal_support g F x t ht hassoc hxG hfinlen,
      hset]
    exact hstep₁.trans (hstep₂.symm.trans (hstep₀.symm.trans hsigma.symm))
  · have hxnot : x ∉ SheafOfModules.supp ((Scheme.Modules.pullback g).obj F) := by
      rwa [Stacks.Modules.supp_pullback g F]
    rw [cycleAssociatedToCoherentSheaf_apply]
    simp only [hxnot, false_and, ite_false]
    refine (finsum_eq_zero_of_forall_eq_zero fun j => ?_).symm
    refine cycleAssociatedToClosedSubscheme_apply_eq_zero_of_notMem_range C f _ k ?_
    rw [Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.support_comap,
      Closeds.coe_preimage]
    exact fun hmem => hxF (coe_support_coherentComponentFamily_subset C f k F j hmem)

omit [IsClosedImmersion g] in
/-- At every point of `X` the coefficients of the restrictions along `g` of the family have
finite support: a nonzero coefficient puts the image of the point in the support of that member,
and the family is locally finite. -/
theorem hasFiniteSupport_cycleAssociatedToComap_coherentComponentFamily (x : X) :
    Function.HasFiniteSupport fun j : coherentComponentIndex C f k F =>
      (cycleAssociatedToClosedSubscheme C f
        ((coherentComponentFamily C f k F j).comap g).subschemeι k).1 x := by
  refine ((locallyFinite_support_coherentComponentFamily C f k F).point_finite (g x)).subset
    fun j hj => ?_
  exact mem_support_of_cycleAssociatedToComap_apply_ne_zero C f k g _ x hj

end Section

end Stacks.Chow

end
