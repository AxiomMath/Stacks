module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ClosedPushforwardRationalEquivalenceCarrierCanonical
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.FlatPullbackPrincipalDivisorComponents
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.FlatPullbackRationalEquivalenceSummand
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.PrincipalDivisorCanonical
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.PrincipalDivisorCycleMultiple
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.RationalEquivalenceSumsCanonical

/-!
# Flat pullback of cycles rationally equivalent to zero, at the canonical embeddings

In Situation 0EDT let `X, Y/B` be good and let `f : X ⟶ Y` be flat of relative dimension `r`.
With rational equivalence read at the canonical embeddings `R(W) → Q(𝒪^h_{W,ξ})` of Stacks 0ENK
(`AlgebraicGeometry.Space.IsRationallyEquivalentToZeroCanonical`), the flat pullback `f^*` carries
cycles rationally equivalent to zero on `Y` to cycles rationally equivalent to zero on `X`, and so
induces a map of Chow groups.

## Main definitions

* `AlgebraicGeometry.Space.flatPullbackChowMapCanonical`: the flat pullback
  `f^* : CH_m(Y) → CH_n(X)`, `m + r = n`, on the Chow groups at the canonical embeddings.

## Main results

* `AlgebraicGeometry.Space.IsRationallyEquivalentToZeroWithinCanonical.uliftIndex` and
  `AlgebraicGeometry.Space.IsRationallyEquivalentToZeroCanonical.uliftIndex`: a rational
  equivalence presented by a family indexed in a universe `v` is one presented in any larger
  universe.
* `AlgebraicGeometry.Space.isRationallyEquivalentToZeroCanonical_flatPullbackMap_of_summand`: if
  `f^*` of every pushed-forward principal divisor is rationally equivalent to zero within the
  inverse image of its support, then `f^*` preserves rational equivalence to zero.
* `isRationallyEquivalentToZeroWithinCanonical_flatPullbackMap_pushforward` (in namespace
  `AlgebraicGeometry.Space`): `f^*((i_V)_* d)` is rationally equivalent to zero within
  `f^{-1}(|V|)` when the flat pullback of `d` to `V ×_Y X` is rationally equivalent to zero.
* `AlgebraicGeometry.Space.isRationallyEquivalentToZeroCanonical_of_eq_finsum_components`: a
  locally finite sum of multiples of pushed-forward principal divisors over the irreducible
  components is rationally equivalent to zero.
* `AlgebraicGeometry.Space.isRationallyEquivalentToZeroCanonical_flatPullbackMap`: the flat
  pullback of a cycle rationally equivalent to zero is rationally equivalent to zero.
* `AlgebraicGeometry.Space.rationallyEquivalentCanonical_flatPullbackMap`: if `α ∼_rat β` on `Y`
  then `f^*α ∼_rat f^*β` on `X`.

## References

* [Stacks Project, Tag 0EDT](https://stacks.math.columbia.edu/tag/0EDT)
* [Stacks Project, Tag 0EP6](https://stacks.math.columbia.edu/tag/0EP6)
* [Stacks Project, Tag 0EPD](https://stacks.math.columbia.edu/tag/0EPD)
* [Stacks Project, Tag 0EQ6](https://stacks.math.columbia.edu/tag/0EQ6)
* [Stacks Project, Tag 0EQ8](https://stacks.math.columbia.edu/tag/0EQ8)
* [Stacks Project, Tag 0EQB](https://stacks.math.columbia.edu/tag/0EQB)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe w v u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

/-! ### Enlarging the index universe -/

section Universe

variable {D : BaseSpaceDimensionSituation.{u}}
    {X : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u} {sX : X ⟶ D.space}
    {hX : D.IsGood sX} {k : ℤ} {α : CycleGroup D sX k}

/-- A rational equivalence to zero within a carrier, presented by a family indexed in the
universe `v`, is one presented by a family indexed in `max v w`. -/
theorem IsRationallyEquivalentToZeroWithinCanonical.uliftIndex
    {T : Set (points D.site D.base D.base_mem X)}
    (h : IsRationallyEquivalentToZeroWithinCanonical.{v} D sX hX k α T) :
    IsRationallyEquivalentToZeroWithinCanonical.{max v w} D sX hX k α T := by
  obtain ⟨J, W, hWfin, c, hsub, hdim, hprin, rfl⟩ := h
  have hfin : LocallyFinite fun j : ULift.{w} J =>
      subspacePointSet D.site D.base D.base_mem X (W j.down).subspace :=
    hWfin.comp_injective ULift.down_injective
  refine ⟨ULift.{w} J, fun j => W j.down, hfin, fun j => c j.down, fun j => hsub j.down,
    fun j => hdim j.down, fun j => hprin j.down, Subtype.ext (funext fun Z => ?_)⟩
  exact (finsum_comp_equiv (Equiv.ulift.{w} (α := J))
    (f := fun j => (integralClosedSubspacePushforward D sX hX (W j) k (c j)).1 Z)).symm

/-- A rational equivalence to zero presented by a family indexed in the universe `v` is one
presented by a family indexed in `max v w`. -/
theorem IsRationallyEquivalentToZeroCanonical.uliftIndex
    (h : IsRationallyEquivalentToZeroCanonical.{v} D sX hX k α) :
    IsRationallyEquivalentToZeroCanonical.{max v w} D sX hX k α :=
  ((isRationallyEquivalentToZeroWithinCanonical_univ_iff.{v} D sX hX k α).2
    h).uliftIndex.isRationallyEquivalentToZeroCanonical

end Universe

/-! ### The reassembly -/

section Reassembly

variable (D : BaseSpaceDimensionSituation.{u})
    {X Y : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (sX : X ⟶ D.space) (hX : D.IsGood sX) (sY : Y ⟶ D.space) (hY : D.IsGood sY)
    (f : X ⟶ Y) (hbase : f ≫ sY = sX) (r : ℕ) (hflat : IsFlat D.site D.base D.base_mem f)
    (hr : HasRelativeDimension r D.site D.base D.base_mem f)

/-- Let `α ∈ Z_m(Y)` be rationally equivalent to zero, and suppose that for every integral
closed subspace `V ⊆ Y` of δ-dimension `m + 1` and every principal divisor `d = div(g)` on `V` the
flat pullback `f^*((i_V)_* d)` is rationally equivalent to zero on `X` by a family of integral
closed subspaces lying in `f^{-1}(|V|)`. Then `f^*α` is rationally equivalent to zero on `X`. -/
theorem isRationallyEquivalentToZeroCanonical_flatPullbackMap_of_summand (m n : ℤ)
    (hmn : m + (r : ℤ) = n)
    (hdiv : ∀ V : IntegralClosedSubspace D.site D.base D.base_mem Y,
      deltaDimension D sY V = m + 1 →
      ∀ d : CycleGroup D (V.subspace.ι ≫ sY) m,
        IsPrincipalDivisorCycleOfGood D (V.subspace.ι ≫ sY)
          (isGood_integralClosedSubspace D sY hY V) V.isIntegralSpace m d →
          IsRationallyEquivalentToZeroWithinCanonical.{w} D sX hX n
            (flatPullbackMap D sX hX sY hY f hbase r hflat hr m n hmn
              (integralClosedSubspacePushforward D sY hY V m d))
            (pointsMap D.site D.base D.base_mem X f ⁻¹'
              subspacePointSet D.site D.base D.base_mem Y V.subspace))
    {α : CycleGroup D sY m} (hα : IsRationallyEquivalentToZeroCanonical.{v} D sY hY m α) :
    IsRationallyEquivalentToZeroCanonical.{max v w} D sX hX n
      (flatPullbackMap D sX hX sY hY f hbase r hflat hr m n hmn α) := by
  obtain ⟨J, W, hWfin, c, hdim, hprin, rfl⟩ := hα
  refine isRationallyEquivalentToZeroCanonical_finsum.{max v w} D sX hX n
    (J := ULift.{w} J)
    (fun j => flatPullbackMap D sX hX sY hY f hbase r hflat hr m n hmn
      (integralClosedSubspacePushforward D sY hY (W j.down) m (c j.down)))
    (fun j => pointsMap D.site D.base D.base_mem X f ⁻¹'
      subspacePointSet D.site D.base D.base_mem Y (W j.down).subspace)
    ((locallyFinite_preimage_pointsMap D.site D.base D.base_mem hX.1 hY.1 f
      (fun j => subspacePointSet D.site D.base D.base_mem Y (W j).subspace) hWfin).comp_injective
        ULift.down_injective)
    (fun j => (hdiv (W j.down) (hdim j.down) (c j.down) (hprin j.down)).uliftIndex) ?_
  intro T
  rw [flatPullbackMap_cycleFamilySum_apply D sX hX sY hY f hbase r hflat hr W hWfin m n hmn c T]
  exact (finsum_comp_equiv (Equiv.ulift.{w} (α := J))
    (f := fun j => (flatPullbackMap D sX hX sY hY f hbase r hflat hr m n hmn
      (integralClosedSubspacePushforward D sY hY (W j) m (c j))).1 T)).symm

end Reassembly

/-! ### The summand -/

section Summand

variable (D : BaseSpaceDimensionSituation.{u})
    {X Y : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (sX : X ⟶ D.space) (hX : D.IsGood sX) (sY : Y ⟶ D.space) (hY : D.IsGood sY)
    (f : X ⟶ Y) (hbase : f ≫ sY = sX) (r : ℕ) (hflat : IsFlat D.site D.base D.base_mem f)
    (hr : HasRelativeDimension r D.site D.base D.base_mem f)

/-- Let `V ⊆ Y` be an integral closed subspace, `V' = V ×_Y X ⊆ X` its inverse image
(Stacks 083Q) and `g : V' ⟶ V` the projection, flat of relative dimension `r`. If the flat
pullback `g^*d` of a cycle `d ∈ Z_m(V)` is rationally equivalent to zero on `V'`, then
`f^*((i_V)_* d)` is rationally equivalent to zero on `X` by a family of integral closed subspaces
lying in `f^{-1}(|V|)`. -/
theorem isRationallyEquivalentToZeroWithinCanonical_flatPullbackMap_pushforward (m n : ℤ)
    (hmn : m + (r : ℤ) = n) (V : IntegralClosedSubspace D.site D.base D.base_mem Y)
    (d : CycleGroup D (V.subspace.ι ≫ sY) m)
    (hd : IsRationallyEquivalentToZeroCanonical.{w} D ((V.subspace.preimage f).ι ≫ sX)
      (isGood_ι_preimage_integralClosedSubspace D sX hX sY hY f V) n
      (flatPullbackMap D ((V.subspace.preimage f).ι ≫ sX)
        (isGood_ι_preimage_integralClosedSubspace D sX hX sY hY f V)
        (V.subspace.ι ≫ sY) (isGood_integralClosedSubspace D sY hY V)
        (V.subspace.fromPreimage f) (fromPreimage_comp_ι_comp D sX sY f hbase V) r
        (isFlat_and_hasRelativeDimension_fromPreimage D sX hX sY hY f hbase r hflat hr V).1
        (isFlat_and_hasRelativeDimension_fromPreimage D sX hX sY hY f hbase r hflat hr V).2
        m n hmn d)) :
    IsRationallyEquivalentToZeroWithinCanonical.{w} D sX hX n
      (flatPullbackMap D sX hX sY hY f hbase r hflat hr m n hmn
        (integralClosedSubspacePushforward D sY hY V m d))
      (pointsMap D.site D.base D.base_mem X f ⁻¹'
        subspacePointSet D.site D.base D.base_mem Y V.subspace) := by
  obtain ⟨K, U, hUfin, e, hsub, hdim, hprin, heq⟩ :=
    exists_cycleFamilySum_subset_of_isRationallyEquivalentToZeroCanonical_closedPushforward.{w}
      D sX hX (V.subspace.preimage f)
      (isClosedSubspace_preimage_integralClosedSubspace D sX hX sY hY f V) n hd
  refine ⟨K, U, hUfin, e, fun l => (hsub l).trans
    (subspacePointSet_preimage D.site D.base D.base_mem f V.subspace).subset, hdim, hprin, ?_⟩
  rwa [flatPullbackMap_integralClosedSubspacePushforward_eq_closedPushforward D sX hX sY hY f
    hbase r hflat hr V m n hmn d]

end Summand

/-! ### A sum of multiples of principal divisors over the irreducible components -/

section Components

variable (D : BaseSpaceDimensionSituation.{u})

/-- An integer multiple of a principal divisor at the canonical embeddings is a principal
divisor at the canonical embeddings: `a · div(f) = div(f^a)`. -/
theorem isPrincipalDivisorCycleOfGood_zsmul {Y : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (sY : Y ⟶ D.space) (hY : D.IsGood sY) (hint : IsIntegralSpace D.site D.base D.base_mem Y)
    (k : ℤ) {c : CycleGroup D sY k} (h : IsPrincipalDivisorCycleOfGood D sY hY hint k c)
    (a : ℤ) : IsPrincipalDivisorCycleOfGood D sY hY hint k (a • c) := by
  have : ∀ W : PrimeDivisor D.site D.base D.base_mem Y,
      Nontrivial ↥(W.genericHenselianLocalRing D.site D.base D.base_mem hY.1
        hint.isDecentSpace) := fun W =>
    W.nontrivial_genericHenselianLocalRing D.site D.base D.base_mem hY.1 hint.isDecentSpace hint
      (hasEtaleLocalProperty_isLocallyNoetherian_of_isGood D sY hY)
  have : ∀ W : PrimeDivisor D.site D.base D.base_mem Y,
      IsNoetherianRing ↥(W.genericHenselianLocalRing D.site D.base D.base_mem hY.1
        hint.isDecentSpace) := fun W =>
    W.isNoetherianRing_genericHenselianLocalRing D.site D.base D.base_mem hY.1
      hint.isDecentSpace hint (hasEtaleLocalProperty_isLocallyNoetherian_of_isGood D sY hY)
  have : ∀ W : PrimeDivisor D.site D.base D.base_mem Y,
      Ring.KrullDimLE 1 ↥(W.genericHenselianLocalRing D.site D.base D.base_mem hY.1
        hint.isDecentSpace) := fun W =>
    W.krullDimLE_genericHenselianLocalRing D.site D.base D.base_mem hY.1 hint.isDecentSpace hint
      (hasEtaleLocalProperty_isLocallyNoetherian_of_isGood D sY hY)
  obtain ⟨f, ⟨g, rfl⟩, heq⟩ := h
  set emb := (genericFractionEmbedding D.site D.base D.base_mem hY.1 hint.isDecentSpace hint
    (hasEtaleLocalProperty_isLocallyNoetherian_of_isGood D sY hY)).emb
  refine ⟨((g ^ a : (rationalFunctions D.site D.base D.base_mem hY.1)ˣ) :
      rationalFunctions D.site D.base D.base_mem hY.1), (g ^ a).isUnit, ?_⟩
  have hcoe : ((a • c : CycleGroup D sY k) :
      IntegralClosedSubspace D.site D.base D.base_mem Y → ℤ) =
      a • (c : IntegralClosedSubspace D.site D.base D.base_mem Y → ℤ) := rfl
  rw [hcoe, heq]
  funext Z
  change a • principalDivisorCycleCoefficients D sY hY hint.isDecentSpace emb _ _ Z = _
  by_cases hcod : codimension
      (integralClosedSubspaceSupport D.site D.base D.base_mem hY.1 Z) = 1
  · simp only [principalDivisorCycleCoefficients, dite_eq_left hcod]
    exact (PrimeDivisor.ord_zpow_of_ringHom D.site D.base D.base_mem hY.1 hint.isDecentSpace
      (Z.toPrimeDivisor D.site D.base D.base_mem hY.1 hcod)
      (emb (Z.toPrimeDivisor D.site D.base D.base_mem hY.1 hcod)) g a).symm
  · simp only [principalDivisorCycleCoefficients, dite_eq_right hcod, smul_zero]

/-- Being a principal divisor at the canonical embeddings depends only on the coefficients, and
not on the degree the cycle is read in. -/
theorem IsPrincipalDivisorCycleOfGood.of_coe_eq
    {Y : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u} {sY : Y ⟶ D.space}
    {hY : D.IsGood sY} {hint : IsIntegralSpace D.site D.base D.base_mem Y} {k k' : ℤ}
    {c : CycleGroup D sY k} {c' : CycleGroup D sY k'}
    (h : IsPrincipalDivisorCycleOfGood D sY hY hint k c)
    (hcc : (c' : IntegralClosedSubspace D.site D.base D.base_mem Y → ℤ) = c) :
    IsPrincipalDivisorCycleOfGood D sY hY hint k' c' := by
  obtain ⟨f, hf, heq⟩ := h
  exact ⟨f, hf, hcc.trans heq⟩

/-- The principal divisor `div(f)` of Stacks 0EQ1 is a principal divisor at the canonical
embeddings. -/
theorem isPrincipalDivisorCycleOfGood_rationalFunctionPrincipalDivisorCycle
    {Y : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u} (sY : Y ⟶ D.space)
    (hY : D.IsGood sY) (hint : IsIntegralSpace D.site D.base D.base_mem Y) {k : ℤ}
    (hk : deltaDimensionClosed D sY hY Set.univ isClosed_univ = (k : EInt))
    (g : (rationalFunctions D.site D.base D.base_mem hY.1)ˣ) :
    IsPrincipalDivisorCycleOfGood D sY hY hint (k - 1)
      (rationalFunctionPrincipalDivisorCycle D sY hY hint hk g) :=
  ⟨g, g.isUnit, rationalFunctionPrincipalDivisorCycle_coe D sY hY hint hk g⟩

/-- A principal divisor at the canonical embeddings is, coefficientwise, the cycle `div(g)` of
Stacks 0EQ1 of a unit `g`, in whatever degree the latter is read. -/
theorem IsPrincipalDivisorCycleOfGood.exists_eq_rationalFunctionPrincipalDivisorCycle
    {Y : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u} {sY : Y ⟶ D.space}
    {hY : D.IsGood sY} {hint : IsIntegralSpace D.site D.base D.base_mem Y} {m k : ℤ}
    {d : CycleGroup D sY m} (h : IsPrincipalDivisorCycleOfGood D sY hY hint m d)
    (hk : deltaDimensionClosed D sY hY Set.univ isClosed_univ = (k : EInt)) :
    ∃ g : (rationalFunctions D.site D.base D.base_mem hY.1)ˣ,
      (d : IntegralClosedSubspace D.site D.base D.base_mem Y → ℤ) =
        rationalFunctionPrincipalDivisorCycle D sY hY hint hk g := by
  obtain ⟨f, ⟨g, rfl⟩, heq⟩ := h
  exact ⟨g, heq⟩

/-- A cycle read in an equal degree. -/
def cycleOfDegreeEq {Y : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    {sY : Y ⟶ D.space} {k k' : ℤ} (h : k = k') (c : CycleGroup D sY k) : CycleGroup D sY k' :=
  ⟨c.1, h ▸ c.2⟩

/-- The cycle `cycleOfDegreeEq D h c` has the same coefficients as `c`. -/
@[simp]
theorem coe_cycleOfDegreeEq {Y : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    {sY : Y ⟶ D.space} {k k' : ℤ} (h : k = k') (c : CycleGroup D sY k) :
    ((cycleOfDegreeEq D h c : CycleGroup D sY k') :
      IntegralClosedSubspace D.site D.base D.base_mem Y → ℤ) = c :=
  rfl

/-- Pushing forward from an integral closed subspace does not see the degree a cycle is read
in. -/
theorem integralClosedSubspacePushforward_cycleOfDegreeEq
    {X : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u} (sX : X ⟶ D.space)
    (hX : D.IsGood sX) (W : IntegralClosedSubspace D.site D.base D.base_mem X) {k k' : ℤ}
    (h : k = k') (c : CycleGroup D (W.subspace.ι ≫ sX) k)
    (Z : IntegralClosedSubspace D.site D.base D.base_mem X) :
    (integralClosedSubspacePushforward D sX hX W k' (cycleOfDegreeEq D h c)).1 Z =
      (integralClosedSubspacePushforward D sX hX W k c).1 Z := by
  subst h
  rfl

variable {X : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (sX : X ⟶ D.space) (hX : D.IsGood sX)

include hX in
/-- The point sets of the irreducible components of a good algebraic space, as integral closed
subspaces, form a locally finite family. -/
theorem locallyFinite_irreducibleComponentSubspace :
    LocallyFinite fun W : IrreducibleComponentSubspace D.site D.base D.base_mem hX.1 =>
      subspacePointSet D.site D.base D.base_mem X W.1.subspace := by
  let e : IrreducibleComponentSubspace D.site D.base D.base_mem hX.1 →
      irreducibleComponents (points D.site D.base D.base_mem X) := fun W =>
    ⟨subspacePointSet D.site D.base D.base_mem X W.1.subspace, W.2.2.2⟩
  have he : Function.Injective e := fun W W' h => Subtype.ext
    (injective_integralClosedSubspaceSupport D.site D.base D.base_mem hX.1
      (IrreducibleCloseds.ext (congrArg Subtype.val h)))
  exact (locallyFinite_irreducibleComponents_points D sX hX).comp_injective he

/-- Let `X/B` be good, and suppose every irreducible component `W` of `X` has δ-dimension
`n + 1` and carries a principal divisor `c_W` at the canonical embeddings. Then any `n`-cycle with
coefficients `∑_W a_W · ((i_W)_* c_W)_Z` is rationally equivalent to zero on `X`, presented by the
family of irreducible components with summands `a_W · c_W`. -/
theorem isRationallyEquivalentToZeroCanonical_of_eq_finsum_components (n : ℤ)
    (a : IrreducibleComponentSubspace D.site D.base D.base_mem hX.1 → ℤ)
    (hdim : ∀ W : IrreducibleComponentSubspace D.site D.base D.base_mem hX.1,
      deltaDimension D sX W.1 = n + 1)
    (c : ∀ W : IrreducibleComponentSubspace D.site D.base D.base_mem hX.1,
      CycleGroup D (W.1.subspace.ι ≫ sX) n)
    (hprin : ∀ W : IrreducibleComponentSubspace D.site D.base D.base_mem hX.1,
      IsPrincipalDivisorCycleOfGood D (W.1.subspace.ι ≫ sX)
        (isGood_integralClosedSubspace D sX hX W.1) W.1.isIntegralSpace n (c W))
    {β : CycleGroup D sX n}
    (hβ : ∀ Z : IntegralClosedSubspace D.site D.base D.base_mem X,
      β.1 Z = ∑ᶠ W : IrreducibleComponentSubspace D.site D.base D.base_mem hX.1,
        a W * (integralClosedSubspacePushforward D sX hX W.1 n (c W)).1 Z) :
    IsRationallyEquivalentToZeroCanonical.{u + 1} D sX hX n β := by
  refine ⟨IrreducibleComponentSubspace D.site D.base D.base_mem hX.1, fun W => W.1,
    locallyFinite_irreducibleComponentSubspace D sX hX, fun W => a W • c W, hdim,
    fun W => isPrincipalDivisorCycleOfGood_zsmul D _ _ _ n (hprin W) (a W),
    Subtype.ext (funext fun Z => ?_)⟩
  rw [hβ Z]
  refine finsum_congr fun W => ?_
  rw [map_zsmul]
  rfl

end Components

/-! ### The flat pullback of a principal divisor, from its expansion over the components -/

section FlatPrincipal

variable (D : BaseSpaceDimensionSituation.{u})
    {X Y : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (sX : X ⟶ D.space) (hX : D.IsGood sX) (sY : Y ⟶ D.space) (hY : D.IsGood sY)
    (f : X ⟶ Y) (hbase : f ≫ sY = sX) (r : ℕ) (hflat : IsFlat D.site D.base D.base_mem f)
    (hr : HasRelativeDimension r D.site D.base D.base_mem f)

/-- Let `Y/B` be good and integral with `dim_δ(Y) = k`, let `f : X ⟶ Y` be flat of relative
dimension `r` and let `g ∈ R(Y)^*`. Suppose that every irreducible component `W` of `X` has
δ-dimension `k + r`, and that `f^* div_Y(g)` is, coefficientwise,
`∑_W a_W · (i_W)_* div_W(h_W)` for integers `a_W` and units `h_W ∈ R(W)^*`, as in the identity of
Stacks 0EQA. Then the flat pullback of any cycle `d` with the coefficients of `div_Y(g)`, read in
degree `m = k - 1`, is rationally equivalent to zero on `X` in degree `n = m + r`. -/
theorem isRationallyEquivalentToZeroCanonical_flatPullbackMap_of_eq_finsum_components
    (hintY : IsIntegralSpace D.site D.base D.base_mem Y) {k : ℤ}
    (hk : deltaDimensionClosed D sY hY Set.univ isClosed_univ = (k : EInt))
    (g : (rationalFunctions D.site D.base D.base_mem hY.1)ˣ)
    (a : IrreducibleComponentSubspace D.site D.base D.base_mem hX.1 → ℤ)
    (hW : ∀ W : IrreducibleComponentSubspace D.site D.base D.base_mem hX.1,
      deltaDimensionClosed D (W.1.subspace.ι ≫ sX) (isGood_integralClosedSubspace D sX hX W.1)
        Set.univ isClosed_univ = ((k + r : ℤ) : EInt))
    (h : ∀ W : IrreducibleComponentSubspace D.site D.base D.base_mem hX.1,
      (rationalFunctions D.site D.base D.base_mem (isGood_integralClosedSubspace D sX hX W.1).1)ˣ)
    (hkr : k - 1 + (r : ℤ) = k + r - 1)
    (heq : ∀ Z : IntegralClosedSubspace D.site D.base D.base_mem X,
      (flatPullbackMap D sX hX sY hY f hbase r hflat hr (k - 1) (k + r - 1) hkr
          (rationalFunctionPrincipalDivisorCycle D sY hY hintY hk g)).1 Z =
        ∑ᶠ W : IrreducibleComponentSubspace D.site D.base D.base_mem hX.1,
          a W * (properCyclePushforward D (W.1.subspace.ι ≫ sX)
            (isGood_integralClosedSubspace D sX hX W.1) sX hX (f := W.1.subspace.ι) rfl
            (isQuasiCompact_of_isClosedImmersion' D.site D.base D.base_mem
              W.1.isClosedSubspace.2) (k + r - 1)
            (rationalFunctionPrincipalDivisorCycle D (W.1.subspace.ι ≫ sX)
              (isGood_integralClosedSubspace D sX hX W.1) W.1.isIntegralSpace (hW W)
              (h W))).1 Z)
    (m n : ℤ) (hmn : m + (r : ℤ) = n) (hkm : k = m + 1) (d : CycleGroup D sY m)
    (hd : (d : IntegralClosedSubspace D.site D.base D.base_mem Y → ℤ) =
      rationalFunctionPrincipalDivisorCycle D sY hY hintY hk g) :
    IsRationallyEquivalentToZeroCanonical.{u + 1} D sX hX n
      (flatPullbackMap D sX hX sY hY f hbase r hflat hr m n hmn d) := by
  have hdeg : k + r - 1 = n := by omega
  refine isRationallyEquivalentToZeroCanonical_of_eq_finsum_components D sX hX n a
    (fun W => ?_)
    (fun W => cycleOfDegreeEq D hdeg
      (rationalFunctionPrincipalDivisorCycle D (W.1.subspace.ι ≫ sX)
        (isGood_integralClosedSubspace D sX hX W.1) W.1.isIntegralSpace (hW W) (h W)))
    (fun W => IsPrincipalDivisorCycleOfGood.of_coe_eq D
      (isPrincipalDivisorCycleOfGood_rationalFunctionPrincipalDivisorCycle D
        (W.1.subspace.ι ≫ sX) (isGood_integralClosedSubspace D sX hX W.1) W.1.isIntegralSpace
        (hW W) (h W)) rfl) (fun Z => ?_)
  · have h1 := (deltaDimensionClosed_univ_integralClosedSubspace D sX hX W.1).symm.trans (hW W)
    have h2 : deltaDimension D sX W.1 = k + r := WithBotTop.coe_injective h1
    omega
  · have hL : (flatPullbackMap D sX hX sY hY f hbase r hflat hr m n hmn d).1 Z =
        (flatPullbackMap D sX hX sY hY f hbase r hflat hr (k - 1) (k + r - 1) hkr
          (rationalFunctionPrincipalDivisorCycle D sY hY hintY hk g)).1 Z := by
      rw [flatPullbackMap_apply, flatPullbackMap_apply, hd]
    rw [hL, heq Z]
    refine finsum_congr fun W => ?_
    rw [properCyclePushforward_ι_eq_integralClosedSubspacePushforward,
      integralClosedSubspacePushforward_cycleOfDegreeEq]

end FlatPrincipal

/-! ### Stacks 0EQB -/

section Main

variable (D : BaseSpaceDimensionSituation.{u})
    {X Y : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (sX : X ⟶ D.space) (hX : D.IsGood sX) (sY : Y ⟶ D.space) (hY : D.IsGood sY)
    (f : X ⟶ Y) (hbase : f ≫ sY = sX) (r : ℕ) (hflat : IsFlat D.site D.base D.base_mem f)
    (hr : HasRelativeDimension r D.site D.base D.base_mem f)

/-- In Situation 0EDT let `X, Y/B` be good and `f : X ⟶ Y` flat of relative dimension `r`.
If `α ∈ Z_m(Y)` is rationally equivalent to zero, presented by a family indexed in a universe
`v`, then `f^*α ∈ Z_n(X)`, `m + r = n`, is rationally equivalent to zero, presented by a family
indexed in `max v (u + 1)`. -/
theorem isRationallyEquivalentToZeroCanonical_flatPullbackMap (m n : ℤ) (hmn : m + (r : ℤ) = n)
    {α : CycleGroup D sY m} (hα : IsRationallyEquivalentToZeroCanonical.{v} D sY hY m α) :
    IsRationallyEquivalentToZeroCanonical.{max v (u + 1)} D sX hX n
      (flatPullbackMap D sX hX sY hY f hbase r hflat hr m n hmn α) := by
  refine isRationallyEquivalentToZeroCanonical_flatPullbackMap_of_summand D sX hX sY hY f hbase
    r hflat hr m n hmn (fun V hV d hd => ?_) hα
  refine isRationallyEquivalentToZeroWithinCanonical_flatPullbackMap_pushforward D sX hX sY hY f
    hbase r hflat hr m n hmn V d ?_
  have hk : deltaDimensionClosed D (V.subspace.ι ≫ sY) (isGood_integralClosedSubspace D sY hY V)
      Set.univ isClosed_univ = ((m + 1 : ℤ) : EInt) := by
    rw [deltaDimensionClosed_univ_integralClosedSubspace D sY hY V, hV]
  obtain ⟨g, hg⟩ := hd.exists_eq_rationalFunctionPrincipalDivisorCycle D hk
  have hV'good := isGood_ι_preimage_integralClosedSubspace D sX hX sY hY f V
  have hpr := isFlat_and_hasRelativeDimension_fromPreimage D sX hX sY hY f hbase r hflat hr V
  exact isRationallyEquivalentToZeroCanonical_flatPullbackMap_of_eq_finsum_components D
    ((V.subspace.preimage f).ι ≫ sX) hV'good (V.subspace.ι ≫ sY)
    (isGood_integralClosedSubspace D sY hY V) (V.subspace.fromPreimage f)
    (fromPreimage_comp_ι_comp D sX sY f hbase V) r hpr.1 hpr.2 V.isIntegralSpace hk g
    (fun W => spaceMultiplicity D (V.subspace.preimage f).toFunctor hV'good.1 W.1)
    (fun W => W.deltaDimensionClosed_univ_of_isFlat D ((V.subspace.preimage f).ι ≫ sX) hV'good
      (V.subspace.ι ≫ sY) (isGood_integralClosedSubspace D sY hY V)
      (V.subspace.fromPreimage f) (fromPreimage_comp_ι_comp D sX sY f hbase V) r hpr.2 hpr.1
      V.isIntegralSpace hk)
    (fun W => W.flatPullbackRationalFunction D ((V.subspace.preimage f).ι ≫ sX) hV'good
      (V.subspace.ι ≫ sY) (isGood_integralClosedSubspace D sY hY V)
      (V.subspace.fromPreimage f) hpr.1 V.isIntegralSpace g) _
    (flatPullbackMap_rationalFunctionPrincipalDivisorCycle_eq_finsum_components D
      ((V.subspace.preimage f).ι ≫ sX) hV'good (V.subspace.ι ≫ sY)
      (isGood_integralClosedSubspace D sY hY V) (V.subspace.fromPreimage f)
      (fromPreimage_comp_ι_comp D sX sY f hbase V) r hpr.2 hpr.1 V.isIntegralSpace hk g)
    m n hmn rfl d hg

/-- In Situation 0EDT let `X, Y/B` be good and let `f : X ⟶ Y` be a morphism over `B` which is
flat of relative dimension `r`. If `α ∼_rat β` are rationally equivalent `m`-cycles on `Y`, then
`f^*α ∼_rat f^*β` as `n`-cycles on `X`, where `m + r = n`.

Rational equivalence is that of Stacks 0EQ6 with `div(g)` read at the canonical embeddings of
Stacks 0ENK (`AlgebraicGeometry.Space.RationallyEquivalentCanonical`), and `f^*` is the flat
pullback of cycles of Stacks 0EP8 (`AlgebraicGeometry.Space.flatPullbackMap`). The family
presenting `α - β` is indexed in a universe `v`, the one presenting `f^*α - f^*β` in
`max v (u + 1)`. -/
@[stacks 0EQB "f^*α ∼_rat f^*β in Z_{m+r}(X) for α ∼_rat β in Z_m(Y), f flat of relative
  dimension r between good spaces over B; rational equivalence at the canonical embeddings of
  0ENK, the presenting family on X indexed in max v (u+1) when the one on Y is indexed in v"]
theorem rationallyEquivalentCanonical_flatPullbackMap (m n : ℤ) (hmn : m + (r : ℤ) = n)
    {α β : CycleGroup D sY m} (h : RationallyEquivalentCanonical.{v} D sY hY m α β) :
    RationallyEquivalentCanonical.{max v (u + 1)} D sX hX n
      (flatPullbackMap D sX hX sY hY f hbase r hflat hr m n hmn α)
      (flatPullbackMap D sX hX sY hY f hbase r hflat hr m n hmn β) := by
  unfold RationallyEquivalentCanonical at h ⊢
  rw [← map_sub]
  exact isRationallyEquivalentToZeroCanonical_flatPullbackMap D sX hX sY hY f hbase r hflat hr
    m n hmn h

/-- The flat pullback `f^* : CH_m(Y) → CH_n(X)`, `m + r = n`, induced on the Chow groups of
Stacks 0EQ6, part (4), at the canonical embeddings. -/
def flatPullbackChowMapCanonical (m n : ℤ) (hmn : m + (r : ℤ) = n) :
    chowGroupCanonical.{v} D sY hY m →+ chowGroupCanonical.{max v (u + 1)} D sX hX n :=
  QuotientAddGroup.map _ _ (flatPullbackMap D sX hX sY hY f hbase r hflat hr m n hmn)
    fun _ hα => isRationallyEquivalentToZeroCanonical_flatPullbackMap D sX hX sY hY f hbase r
      hflat hr m n hmn hα

/-- The flat pullback on Chow groups sends the class of a cycle to the class of its flat
pullback. -/
theorem flatPullbackChowMapCanonical_chowClassCanonical (m n : ℤ) (hmn : m + (r : ℤ) = n)
    (α : CycleGroup D sY m) :
    flatPullbackChowMapCanonical D sX hX sY hY f hbase r hflat hr m n hmn
        (chowClassCanonical.{v} D sY hY m α) =
      chowClassCanonical.{max v (u + 1)} D sX hX n
        (flatPullbackMap D sX hX sY hY f hbase r hflat hr m n hmn α) :=
  rfl

end Main

end AlgebraicGeometry.Space

end
