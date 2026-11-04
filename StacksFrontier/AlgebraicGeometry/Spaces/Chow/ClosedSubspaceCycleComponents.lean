module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ClosedSubspaceCycle
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.EffectiveCartierIntersection
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.MultiplicityAtPoint
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.PropertyGammaPermanence
public import StacksFrontier.AlgebraicGeometry.Spaces.GeometricLengthPointIndependence
public import StacksFrontier.AlgebraicGeometry.Spaces.GeometricRepresentative

/-!
# The cycle of a closed subspace is the sum over its irreducible components

In Situation 0EDT let `X/B` be good and let `Y ⊆ X` be a closed subspace with `dim_δ(Y) ≤ k`.
**Stacks 0EE9** writes the `k`-cycle associated to `Y` as

`[Y]_k = ∑ m_{Z, Y} [Z]`,

the sum over the irreducible components `Z` of `Y` of δ-dimension `k`, with `m_{Z, Y}` the
multiplicity of part (1) — the length of `𝒪_Y` at the generic point of `Z`, read inside `Y`.

This file *proves* that identity, in the form in which the scheme side already has it: the
coefficient of `[Y]_k` at an integral closed subspace `Z ⊆ X` equals the corresponding sum of
the coefficients of the fundamental cycles `[Z_i]` of the components, weighted by their
multiplicities. **The additivity is proved, not assumed:** no component rule, no multiplicity
family and no decomposition of the cycle is taken as a hypothesis. The two inputs are the
definition of `AlgebraicGeometry.Space.cycleCoeffOfClosedSubspace` and the injectivity of
`AlgebraicGeometry.Space.IntegralClosedSubspace.pushforward`, which together make the
displayed sum collapse, at each coefficient, to a single term.

The scheme-level statement this is modelled on is
`Stacks.ChernCap42.cycleAssociatedToClosedSubscheme_apply_eq_finsum`, which is coefficientwise
for the same reason as here (see the implementation notes).

## Main definitions

* `AlgebraicGeometry.Space.closedSubspaceMultiplicity`: **Stacks 0EE9, part (1)**, the
  multiplicity `m_{W, Y}` of an integral closed subspace `W ⊆ Y` in `Y`, at a chosen geometric
  point.
* `AlgebraicGeometry.Space.topComponentSubspaces`: the index set of the sum — the integral
  closed subspaces of `Y` whose image in `X` has δ-dimension `k`. Under `dim_δ(Y) ≤ k` these
  are exactly the irreducible components of `|Y|` of δ-dimension `k`, which is what the two
  results below record.

## Main results

* `AlgebraicGeometry.Space.closedSubspaceCycle_apply_eq_finsum`: **the additivity.** The
  coefficient of `[Y]_k` at an integral closed subspace of `X` is
  `∑ m_{W, Y} · [W]_Z`, the sum running over the index set above.
* `AlgebraicGeometry.Space.closedSubspaceCycle_coe_eq_finsum`: the same as an equality of
  coefficient families, that is of cycles in `Z_k(X)`.
* `AlgebraicGeometry.Space.exists_irreducibleComponents_closedSubspaceComponentImage`: every
  index of the sum is an irreducible component of `|Y|`. This is where Stacks 0EE6 enters.
* `AlgebraicGeometry.Space.exists_closedSubspaceComponentImage_eq_closedSetComponent`:
  conversely, every irreducible component of `|Y|` is the image of an index. So the sum runs
  over exactly the components of `|Y|` of δ-dimension `k`, as in the source.

## Implementation notes

**Why the identity is stated coefficientwise.** The components of `|Y|` of δ-dimension `k`
form a locally finite, not finite, collection — that is the content of Stacks 0EE5, which is
`AlgebraicGeometry.Space.locallyFinite_cycleCoeffOfClosedSubspace` — so the sum of the cycles
`m_{W, Y} [W]` cannot be formed as a `finsum` in `Z_k(X)`: a `finsum` over an infinite support
is zero. At a *fixed* coefficient the sum is genuinely finite, indeed has at most one nonzero
term, because `AlgebraicGeometry.Space.IntegralClosedSubspace.pushforward` is injective; so the
identity is stated at each coefficient, and
`AlgebraicGeometry.Space.closedSubspaceCycle_coe_eq_finsum` then assembles the coefficients
into the equality of cycles. This is the shape of the whole chapter, and of the scheme-level
`Stacks.ChernCap42.cycleAssociatedToClosedSubscheme_apply_eq_finsum`.

**The index set.** The sum of Stacks 0EE9 runs over the irreducible components of `Y` of
δ-dimension `k`. Here it runs over the integral closed subspaces `W ⊆ Y` whose image in `X`
has δ-dimension `k`, which is the same collection: every such image is a component of `|Y|` by
Stacks 0EE6, and conversely every component of `|Y|` is such an image because an integral
closed subspace of `X` carried by `|Y|` descends to one of `Y`,
`AlgebraicGeometry.Space.IntegralClosedSubspace.exists_pushforward_eq`. Indexing by the
subspaces of `Y` rather than by the components is what makes the multiplicity available
without choice: `m_{W, Y}` is a length read at the generic point of `W` *inside* `Y`, and that
generic point comes with `W`.

**The δ-dimension of the index is tested on the image.** The two readings agree, by
`AlgebraicGeometry.Space.deltaDimension_closedSubspaceComponentImage`; the image is used
because that is the form `AlgebraicGeometry.Space.integralCycle` and
`AlgebraicGeometry.Space.cycleCoeffOfClosedSubspace` ask for.

**The choice of geometric point is not a parameter.** The multiplicity is a length at a
*geometric* point, and the independence of that choice is Stacks 0EE1,
`AlgebraicGeometry.Space.geometricLength_eq_of_image_eq`.
`AlgebraicGeometry.Space.closedSubspaceMultiplicity` therefore takes no geometric
representative as a parameter: it reads the length at the canonical representative
`AlgebraicGeometry.Space.canonicalGeometricPoint`, and
`AlgebraicGeometry.Space.closedSubspaceMultiplicity_eq_toNat_geometricLength` records that the
same value is obtained at *any* geometric representative of the generic point, by Stacks 0EE1.

**Positivity of the multiplicity.** Part (1) of Stacks 0EE9 records that `m_{Z, Y}` is a
positive integer, by Lemma 0EE4. `AlgebraicGeometry.Space.closedSubspaceMultiplicity_pos` proves
this, for the hypotheses of the structure-sheaf case of Stacks 0EE4,
`AlgebraicGeometry.Space.geometricLength_structureSheafModule_ne_top_and_pos`: that `Y`, as an
algebraic space in its own right, is decent and locally Noetherian, and that `W`'s generic point
is a generic point of an irreducible component of `|Y|`.

**What this does not give.** The second assertion of Stacks 0EPA, `(g ∘ f)^* = f^* ∘ g^*`, does
*not* follow from the identity below. Substituting it into the defining sum of the flat
pullback turns the right-hand side into a double sum whose comparison with the left-hand side
is the identity `f^*[Y']_{k+s} = [f^{-1}(Y')]_{k+s+r}` for the *closed* subspace
`Y' = g^{-1}(W)`, that is Stacks 0EP3, a separate statement.
The source's own proof of Stacks 0EPA (2) is not a component decomposition either: it chooses
an étale chart `U → V → W` of schemes, reads off two flat local homomorphisms of local rings
and compares a single length with a product of two lengths by Algebra, Lemma 10.52.14.

## References

* [Stacks Project, Tag 0EE9](https://stacks.math.columbia.edu/tag/0EE9)
* [Stacks Project, Tag 0EDT](https://stacks.math.columbia.edu/tag/0EDT)
* [Stacks Project, Tag 0EDZ](https://stacks.math.columbia.edu/tag/0EDZ)
* [Stacks Project, Tag 0EE1](https://stacks.math.columbia.edu/tag/0EE1)
* [Stacks Project, Tag 0EE4](https://stacks.math.columbia.edu/tag/0EE4)
* [Stacks Project, Tag 0EE5](https://stacks.math.columbia.edu/tag/0EE5)
* [Stacks Project, Tag 0EE6](https://stacks.math.columbia.edu/tag/0EE6)
* [Stacks Project, Tag 0ENF](https://stacks.math.columbia.edu/tag/0ENF)
* [Stacks Project, Tag 0EP3](https://stacks.math.columbia.edu/tag/0EP3)
* [Stacks Project, Tag 0EPA](https://stacks.math.columbia.edu/tag/0EPA)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (D : BaseSpaceDimensionSituation.{u})
    {X : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}

/-! ### The multiplicity of a component -/

/-- **Stacks 0EE9, part (1).** The multiplicity `m_{W, Y}` of an integral closed subspace
`W ⊆ Y` in a closed subspace `Y ⊆ X`: the length of `𝒪_Y` at the generic point of `W`, read
inside `Y`, at a geometric representative of that generic point.

This is the coefficient the sum of part (2) attaches to `W`, as
`AlgebraicGeometry.Space.closedSubspaceCycle_apply_eq_finsum` records. The representative used
is `AlgebraicGeometry.Space.canonicalGeometricPoint`, but by Stacks 0EE1
(`AlgebraicGeometry.Space.closedSubspaceMultiplicity_eq_toNat_geometricLength`) the value does
not depend on this choice. -/
@[stacks 0EE9 "part (1): the multiplicity m_{Z,Y}, together with its positivity
  (closedSubspaceMultiplicity_pos, Lemma 0EE4)"]
def closedSubspaceMultiplicity (Y : Subfunctor X)
    (hY : IsClosedSubspace D.site D.base D.base_mem Y)
    (W : IntegralClosedSubspace D.site D.base D.base_mem Y.toFunctor) : ℤ :=
  ((geometricLength D.site D.base D.base_mem ⟨Y.toFunctor, hY.1⟩
    (canonicalGeometricPoint D.site D.base D.base_mem Y.toFunctor
      (W.ambientGenericPoint D.site D.base D.base_mem)) (SheafOfModules.unit _)).toNat : ℤ)

/-- **Point-independence of the multiplicity, Stacks 0EE1.** The multiplicity `m_{W, Y}` is the
(cast of the) length of `𝒪_Y` at *any* geometric point lying over the generic point of `W`, not
only at the canonical representative used to define it. -/
theorem closedSubspaceMultiplicity_eq_toNat_geometricLength (Y : Subfunctor X)
    (hY : IsClosedSubspace D.site D.base D.base_mem Y)
    (W : IntegralClosedSubspace D.site D.base D.base_mem Y.toFunctor)
    (x : GeometricPoint D.site D.base D.base_mem Y.toFunctor)
    (hx : x.image = W.ambientGenericPoint D.site D.base D.base_mem) :
    closedSubspaceMultiplicity D Y hY W =
      ((geometricLength D.site D.base D.base_mem ⟨Y.toFunctor, hY.1⟩ x
        (SheafOfModules.unit _)).toNat : ℤ) := by
  unfold closedSubspaceMultiplicity
  rw [geometricLength_eq_of_image_eq D.site D.base D.base_mem hY.1
    (canonicalGeometricPoint D.site D.base D.base_mem Y.toFunctor
      (W.ambientGenericPoint D.site D.base D.base_mem)) x
    ((canonicalGeometricPoint_image D.site D.base D.base_mem Y.toFunctor
      (W.ambientGenericPoint D.site D.base D.base_mem)).trans hx.symm) (SheafOfModules.unit _)]

/-- **Positivity of the multiplicity, part of Stacks 0EE4.** If `Y`, regarded as an algebraic
space in its own right, is decent and locally Noetherian, and the generic point of `W` is a
generic point of an irreducible component of `|Y|`, then the multiplicity `m_{W, Y}` is
positive. -/
theorem closedSubspaceMultiplicity_pos (Y : Subfunctor X)
    (hY : IsClosedSubspace D.site D.base D.base_mem Y)
    (hNloc : HasEtaleLocalProperty D.site D.base D.base_mem Y.toFunctor
      (fun T : Scheme.{u} => IsLocallyNoetherian T))
    (hdec : IsDecentSpace D.site D.base D.base_mem Y.toFunctor)
    (W : IntegralClosedSubspace D.site D.base D.base_mem Y.toFunctor)
    (hW : W.ambientGenericPoint D.site D.base D.base_mem ∈
      genericPoints (points D.site D.base D.base_mem Y.toFunctor)) :
    0 < closedSubspaceMultiplicity D Y hY W := by
  obtain ⟨h1, h2⟩ := geometricLength_structureSheafModule_ne_top_and_pos D.site D.base D.base_mem
    ⟨Y.toFunctor, hY.1⟩ hNloc hdec
    (canonicalGeometricPoint D.site D.base D.base_mem Y.toFunctor
      (W.ambientGenericPoint D.site D.base D.base_mem))
    (by rw [canonicalGeometricPoint_image]; exact hW)
  unfold closedSubspaceMultiplicity
  cases hn : geometricLength D.site D.base D.base_mem ⟨Y.toFunctor, hY.1⟩
      (canonicalGeometricPoint D.site D.base D.base_mem Y.toFunctor
        (W.ambientGenericPoint D.site D.base D.base_mem)) (SheafOfModules.unit _) with
  | top => exact absurd hn h1
  | coe m =>
    rw [hn] at h2
    simp only [ENat.toNat_natCast]
    exact_mod_cast h2

/-- The coefficient of `[Y]_k` at the image of an integral closed subspace `W ⊆ Y` of
δ-dimension `k` is the multiplicity of `W` in `Y`, provided `γ` is read at a geometric
representative of the generic point of `W`. -/
theorem cycleCoeffOfClosedSubspace_eq_closedSubspaceMultiplicity (sX : X ⟶ D.space)
    (hX : D.IsGood sX) (Y : Subfunctor X)
    (hY : IsClosedSubspace D.site D.base D.base_mem Y) (k : ℤ)
    (γ : points D.site D.base D.base_mem Y.toFunctor →
      GeometricPoint D.site D.base D.base_mem Y.toFunctor)
    (W : IntegralClosedSubspace D.site D.base D.base_mem Y.toFunctor)
    (hγ : (γ (W.ambientGenericPoint D.site D.base D.base_mem)).image =
      W.ambientGenericPoint D.site D.base D.base_mem)
    (hW : deltaDimension D sX (closedSubspaceComponentImage D sX hX Y hY W) = k) :
    cycleCoeffOfClosedSubspace D sX hX Y hY k γ
        (closedSubspaceComponentImage D sX hX Y hY W) =
      closedSubspaceMultiplicity D Y hY W := by
  rw [cycleCoeffOfClosedSubspace_closedSubspaceComponentImage, ite_eq_left hW]
  exact (closedSubspaceMultiplicity_eq_toNat_geometricLength D Y hY W
    (γ (W.ambientGenericPoint D.site D.base D.base_mem)) hγ).symm

/-! ### The index set of the sum -/

/-- The index set of the sum of Stacks 0EE9, part (2): the integral closed subspaces of the
closed subspace `Y ⊆ X` whose image in `X` has δ-dimension `k`.

Under `dim_δ(Y) ≤ k` these are exactly the irreducible components of `|Y|` of δ-dimension `k`,
by `AlgebraicGeometry.Space.exists_irreducibleComponents_closedSubspaceComponentImage` and
`AlgebraicGeometry.Space.exists_closedSubspaceComponentImage_eq_closedSetComponent`. -/
abbrev topComponentSubspaces (sX : X ⟶ D.space) (hX : D.IsGood sX) (Y : Subfunctor X)
    (hY : IsClosedSubspace D.site D.base D.base_mem Y) (k : ℤ) :=
  {W : IntegralClosedSubspace D.site D.base D.base_mem Y.toFunctor //
    deltaDimension D sX (closedSubspaceComponentImage D sX hX Y hY W) = k}

/-- **Where Stacks 0EE6 enters.** Let `Y ⊆ X` be a closed subspace of a good algebraic space
`X/B` with `dim_δ(Y) ≤ k`. The image in `X` of an integral closed subspace of `Y` of
δ-dimension `k` has for its point set an irreducible component of `|Y|`.

So every index of the sum of Stacks 0EE9, part (2) is one of the components the source sums
over. The generic point `ξ` of the image lies in `|Y|`, and its δ-dimension attains the bound,
so Stacks 0EE6 makes `ξ` a generic point of an irreducible component of `|Y|`; that component
is the closure of `ξ`, which is the point set of the image. -/
theorem exists_irreducibleComponents_closedSubspaceComponentImage (sX : X ⟶ D.space)
    (hX : D.IsGood sX) (Y : Subfunctor X)
    (hY : IsClosedSubspace D.site D.base D.base_mem Y) (k : ℤ)
    (hdim : deltaDimensionSubspace D sX hX Y hY ≤ (k : EInt))
    (W : IntegralClosedSubspace D.site D.base D.base_mem Y.toFunctor)
    (hW : deltaDimension D sX (closedSubspaceComponentImage D sX hX Y hY W) = k) :
    ∃ C : irreducibleComponents (subspacePointSet D.site D.base D.base_mem X Y),
      subspacePointSet D.site D.base D.base_mem X
          (closedSubspaceComponentImage D sX hX Y hY W).subspace =
        Subtype.val '' (C : Set (subspacePointSet D.site D.base D.base_mem X Y)) := by
  have hTcl : IsClosed (subspacePointSet D.site D.base D.base_mem X Y) :=
    isClosed_subspacePointSet_of_isClosedSubspace D hX.1 Y hY
  set Z := closedSubspaceComponentImage D sX hX Y hY W with hZ
  have hsub : subspacePointSet D.site D.base D.base_mem X Z.subspace ⊆
      subspacePointSet D.site D.base D.base_mem X Y := by
    rw [hZ, IntegralClosedSubspace.subspacePointSet_pushforward]
    exact Set.image_subset_range _ _
  have hmem : Z.ambientGenericPoint D.site D.base D.base_mem ∈
      subspacePointSet D.site D.base D.base_mem X Y := hsub ⟨_, rfl⟩
  have hdimval : inducedDimensionValue D.site D.base D.base_mem D.delta sX
      (Z.ambientGenericPoint D.site D.base D.base_mem) = k := hW
  obtain ⟨C, hC⟩ := isGenericPoint_of_deltaDimensionClosed_le D sX hX
    (subspacePointSet D.site D.base D.base_mem X Y) hTcl
    (Z.ambientGenericPoint D.site D.base D.base_mem) hmem k hdim hdimval
  refine ⟨C, ?_⟩
  have himg := hTcl.isClosedEmbedding_subtypeVal.closure_image_eq
    ({⟨Z.ambientGenericPoint D.site D.base D.base_mem, hmem⟩} :
      Set (subspacePointSet D.site D.base D.base_mem X Y))
  rw [Set.image_singleton, hC] at himg
  exact (Z.isGenericPoint_ambientGenericPoint D.site D.base D.base_mem hX.1).symm.trans himg

/-- Conversely, every irreducible component of `|Y|` is the image of an integral closed
subspace of `Y`: the reduced closed subspace on the component is carried by `|Y|`, and an
integral closed subspace of `X` carried by `|Y|` descends to one of `Y`.

Together with
`AlgebraicGeometry.Space.exists_irreducibleComponents_closedSubspaceComponentImage` this says
that the index set of the sum is exactly the collection of irreducible components of `|Y|` of
δ-dimension `k`, which is the index set of Stacks 0EE9, part (2). -/
theorem exists_closedSubspaceComponentImage_eq_closedSetComponent (sX : X ⟶ D.space)
    (hX : D.IsGood sX) (Y : Subfunctor X)
    (hY : IsClosedSubspace D.site D.base D.base_mem Y)
    (C : irreducibleComponents (subspacePointSet D.site D.base D.base_mem X Y)) :
    ∃ W : IntegralClosedSubspace D.site D.base D.base_mem Y.toFunctor,
      closedSubspaceComponentImage D sX hX Y hY W =
        closedSetComponent D.site D.base D.base_mem hX.1
          (D.isDecentSpace_of_isGood sX hX) (subspacePointSet D.site D.base D.base_mem X Y)
          (isClosed_subspacePointSet_of_isClosedSubspace D hX.1 Y hY) C := by
  refine IntegralClosedSubspace.exists_pushforward_eq D.site D.base D.base_mem hX.1 hY.1
    (D.isDecentSpace_of_isGood sX hX)
    (isDecentSpace_of_isClosedSubspace D.site D.base D.base_mem
      (D.isDecentSpace_of_isGood sX hX) hY) hY.2 _ ?_
  rw [subspacePointSet_closedSetComponent]
  exact Subtype.coe_image_subset _ _

/-! ### The additivity -/

/-- **Stacks 0EE9, part (2), as a sum over the irreducible components.** In Situation 0EDT let
`X/B` be good, let `Y ⊆ X` be a closed subspace and assume `dim_δ(Y) ≤ k`. Then

`[Y]_k = ∑ m_{W, Y} [W]`,

the sum over the integral closed subspaces `W ⊆ Y` whose image in `X` has δ-dimension `k` —
which by Stacks 0EE6 are exactly the irreducible components of `|Y|` of δ-dimension `k` — read
at each coefficient.

**The additivity is proved here, not assumed.** The sum collapses: at a fixed integral closed
subspace `Z ⊆ X` at most one index contributes, because
`AlgebraicGeometry.Space.IntegralClosedSubspace.pushforward` is injective, and the surviving
term is the defining value of
`AlgebraicGeometry.Space.cycleCoeffOfClosedSubspace`. If `Z` is not the image of an integral
closed subspace of `Y`, or has δ-dimension other than `k`, both sides vanish. -/
theorem closedSubspaceCycle_apply_eq_finsum (sX : X ⟶ D.space) (hX : D.IsGood sX)
    (Y : Subfunctor X) (hY : IsClosedSubspace D.site D.base D.base_mem Y) (k : ℤ)
    (hdim : deltaDimensionSubspace D sX hX Y hY ≤ (k : EInt))
    (Z : IntegralClosedSubspace D.site D.base D.base_mem X) :
    (closedSubspaceCycle D sX hX Y hY k hdim).1 Z =
      ∑ᶠ W : topComponentSubspaces D sX hX Y hY k,
        closedSubspaceMultiplicity D Y hY W.1 *
          (integralCycle D sX k (closedSubspaceComponentImage D sX hX Y hY W.1) W.2).1 Z := by
  classical
  set γ := canonicalGeometricPoint D.site D.base D.base_mem Y.toFunctor
  have hinj := IntegralClosedSubspace.injective_pushforward D.site D.base D.base_mem hX.1 hY.1
    (D.isDecentSpace_of_isGood sX hX) hY.2
  have hzero : ∀ W' : topComponentSubspaces D sX hX Y hY k,
      closedSubspaceComponentImage D sX hX Y hY W'.1 ≠ Z →
      closedSubspaceMultiplicity D Y hY W'.1 *
        (integralCycle D sX k (closedSubspaceComponentImage D sX hX Y hY W'.1) W'.2).1 Z = 0 :=
    fun W' hne => by simp [integralCycle_coe, integralCycleCoeff, Ne.symm hne]
  rw [closedSubspaceCycle_coe]
  by_cases hex : ∃ W : topComponentSubspaces D sX hX Y hY k,
      closedSubspaceComponentImage D sX hX Y hY W.1 = Z
  · obtain ⟨⟨W, hk⟩, rfl⟩ := hex
    rw [finsum_eq_single _ (⟨W, hk⟩ : topComponentSubspaces D sX hX Y hY k) ?_]
    · rw [integralCycle_coe, integralCycleCoeff_self, mul_one]
      exact cycleCoeffOfClosedSubspace_eq_closedSubspaceMultiplicity D sX hX Y hY k γ W
        (canonicalGeometricPoint_image D.site D.base D.base_mem Y.toFunctor _) hk
    · exact fun W' hW' => hzero W' fun h => hW' (Subtype.ext (hinj h))
  · refine Eq.trans ?_
      (finsum_eq_zero_of_forall_eq_zero fun W' => hzero W' fun h => hex ⟨W', h⟩).symm
    by_cases hk : deltaDimension D sX Z = k
    · exact cycleCoeffOfClosedSubspace_eq_zero D sX hX Y hY k γ Z
        fun W hW => hex ⟨⟨W, hW ▸ hk⟩, hW⟩
    · rw [cycleCoeffOfClosedSubspace, ite_eq_right hk]

/-- **Stacks 0EE9, part (2), as an equality of cycles.** The coefficient family of `[Y]_k` is
the componentwise sum of
`AlgebraicGeometry.Space.closedSubspaceCycle_apply_eq_finsum`; since a `k`-cycle is a
coefficient family, this is the identity `[Y]_k = ∑ m_{W, Y} [W]` in `Z_k(X)`.

The sum is not formed as a `finsum` of cycles, which would be zero whenever the collection of
components is infinite; see the implementation notes. -/
theorem closedSubspaceCycle_coe_eq_finsum (sX : X ⟶ D.space) (hX : D.IsGood sX)
    (Y : Subfunctor X) (hY : IsClosedSubspace D.site D.base D.base_mem Y) (k : ℤ)
    (hdim : deltaDimensionSubspace D sX hX Y hY ≤ (k : EInt)) :
    (closedSubspaceCycle D sX hX Y hY k hdim).1 =
      fun Z => ∑ᶠ W : topComponentSubspaces D sX hX Y hY k,
        closedSubspaceMultiplicity D Y hY W.1 *
          (integralCycle D sX k (closedSubspaceComponentImage D sX hX Y hY W.1) W.2).1 Z :=
  funext fun Z => closedSubspaceCycle_apply_eq_finsum D sX hX Y hY k hdim Z

end AlgebraicGeometry.Space

end
