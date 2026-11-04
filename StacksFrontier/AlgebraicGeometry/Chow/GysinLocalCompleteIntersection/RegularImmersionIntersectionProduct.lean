module

public import StacksFrontier.AlgebraicGeometry.Chow.BivariantDisjoint.SquarePushforward
public import StacksFrontier.AlgebraicGeometry.Chow.GysinLocalCompleteIntersection.SmoothIntersectionProductMixed
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.LocalCompleteIntersection.RegularImmersion

/-!
# The intersection product with the class of a regularly embedded closed subscheme

Let `k` be a field, let `X` be a scheme smooth over `k` and let `i : Y ⟶ X` be a regular closed
immersion with `Y` equidimensional of dimension `e`. **Stacks 0FFE** asserts that

  `α · [Y]_e = i_*(i^!(α))`   in   `CH_*(X)`

for every `α ∈ CH_*(X)`, where `·` is the intersection product of Section 0FC0, `[Y]_e` is read on
`X` as `i_*[Y]_e`, and `i^!` is the Gysin map of the regular immersion `i` (Stacks 0FF3; a
regular immersion is a local complete intersection morphism, Stacks 069L, and its Gysin map
exists because it is an immersion).

`X` is not required to be equidimensional. It is the disjoint union `X = ∐_d X_d` of its open and
closed parts of dimension `d` (Stacks 02NM, `Stacks.WeilCohomology.dimPart`), and the product of
Section 0FC0 is formed part by part, exactly as that section says. On `X_d` the closed immersion
`Y_d = Y ×_X X_d ⟶ X_d` has codimension `d - e`, so the Gysin map `i^!` of `i`, which lies in the
completed group `A^*(Y ⟶ X)^∧` of Stacks 0FE0, acts on `CH_*(X_d)` through its term of degree
`d - e`. A class `α` with `α|_{X_d} ∈ CH_{d-j}(X_d)` for every `d` (that is, `α ∈ CH^j(X)`, the
codimension grading of `Stacks.Chow.codimensionChowGroup`) is therefore carried to
`i^!α ∈ CH_{e-j}(Y)`, the class whose restriction to `Y_d` is `i^!(α|_{X_d})`
(`Stacks.Chow.regularImmersionGysin`), and both sides of the identity lie in `CH_{e-j}(X)`.

The proof is the source's, on each part `X_d`. By Stacks 0FC2 write `α|_{X_d} = c ∩ [X_d]_d` with
`c ∈ A^j(X_d)`. Then

  `i^!(c ∩ [X_d]_d) = res(c) ∩ i^![X_d]_d = res(c) ∩ [Y_d]_e`

by Stacks 0FF6 (`Stacks.Chow.completedCommutesAfterBaseChange_lciGysinMap`) and Stacks 0FF7
(`Stacks.Chow.regularImmersionPartGysinClass_capTargetHom_fundamentalChowClass`), and

  `i_*(res(c) ∩ [Y_d]_e) = c ∩ i_*[Y_d]_e = (c ∩ [X_d]_d) · i_*[Y_d]_e`

because bivariant classes commute with proper pushforward
(`Stacks.Chow.chowCohomologyCap_properChowPushforward_restriction`) and by Stacks 0FC2 again
(`Stacks.WeilCohomology.canonicalDiagonalClassFamily_capEqProduct`). Restriction to the open
subscheme `X_d` commutes with proper pushforward (Stacks 02RG for an open immersion,
`Stacks.Chow.chowGroupRestrict_properChowPushforward`) and carries `[Y]_e` to `[Y_d]_e`.

## Main definitions

* `Stacks.Chow.codimensionDimensionIntersectionProduct` — the intersection product
  `CH^j(X) × CH_n(X) ⟶ CH_{n-j}(X)` of Section 0FC0, formed part by part.
* `Stacks.Chow.regularImmersionPartGysinClass` — the Gysin map of `i`, restricted along
  `X_d ⟶ X` (Stacks 0F9Z), in its degree `d - e` there.
* `Stacks.Chow.regularImmersionGysin` — the Gysin map `i^! : CH^j(X) ⟶ CH_{e-j}(Y)`.

## Main results

* `Stacks.Chow.intersectionProduct_fundamentalChowClass_eq_pushforward_regularImmersionGysin` —
  **Stacks 0FFE**, `α · i_*[Y]_e = i_*(i^!α)`.
* `Stacks.Chow.regularImmersionPartGysinClass_capTargetHom_fundamentalChowClass` — Stacks 0FF7
  for the restriction of `i^!` to `X_d`: `i^![X_d]_d = [Y_d]_e`.

## Implementation notes

The source states the lemma for `α ∈ CH_*(X)` graded by dimension. When `X` has parts of several
dimensions, neither side is homogeneous for that grading: on `X_d` both lie in `CH_{n+e-d}(X_d)`
for `α ∈ CH_n(X)`. Both sides are determined by their restrictions to the parts `X_d`, where they
depend on `α|_{X_d}` alone, and a class on one part is homogeneous for the codimension grading; so
the statement for every `α ∈ CH^j(X)` and every `j` is the statement for every `α`, part by part,
and it is what is proved. For `X` equidimensional of dimension `d` the two gradings agree,
`CH^j(X) = CH_{d-j}(X)`.

"`Y` is equidimensional of dimension `e`" is `RelativeDimension (i ≫ sX) e`: the fibre of
`Y ⟶ Spec k` is `Y` itself, equidimensional of dimension `e`.

The pieces of `Y` are the base changes `Y ×_X X_d`, decomposing `Y` along the open immersions
`Y ×_X X_d ⟶ Y`, so that the cap operation of `i^!` at the test scheme `X_d ⟶ X` lands on them
directly. The pieces are indexed by `ULift ℕ` where a decomposition of Chow groups needs an index
type in the universe of the schemes (`Stacks.Chow.chowGroupClopenRestrictEquiv`).

## References

* [Stacks Project, Tag 0FFE](https://stacks.math.columbia.edu/tag/0FFE)
* [Stacks Project, Section 0FC0](https://stacks.math.columbia.edu/tag/0FC0)
* [Stacks Project, Tag 0FC2](https://stacks.math.columbia.edu/tag/0FC2)
* [Stacks Project, Tag 0FF3](https://stacks.math.columbia.edu/tag/0FF3)
* [Stacks Project, Tag 0FF6](https://stacks.math.columbia.edu/tag/0FF6)
* [Stacks Project, Tag 0FF7](https://stacks.math.columbia.edu/tag/0FF7)
* [Stacks Project, Tag 069L](https://stacks.math.columbia.edu/tag/069L)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

open Stacks.WeilCohomology (dimPart partBase relativeDimension_partBase
  isClopenDecomposition_dimPart canonicalDiagonalClassFamily
  fieldGysinSystem capFundamentalClassSurjective canonicalDiagonalClassFamily_capEqProduct
  selfIntersectionProduct_heq_of_heq)

section Product

variable (k : Type u) [Field k] {X : Scheme.{u}} (sX : X ⟶ (fieldChowSituation k).S) [Smooth sX]

/-- **The intersection product of Section 0FC0** of a class `α ∈ CH^j(X)` graded by codimension
with a class `β ∈ CH_n(X)` graded by dimension: the class of `CH_{n-j}(X)` whose restriction to
the part `X_d` is `α_d · β|_{X_d} ∈ CH_{(d-j)+n-d}(X_d)`. -/
def codimensionDimensionIntersectionProduct (j n : ℤ) :
    codimensionChowGroup k sX j →ₗ[ℤ] chowGroup (fieldChowSituation k) sX n →ₗ[ℤ]
      chowGroup (fieldChowSituation k) sX (n - j) :=
  LinearMap.mk₂ ℤ
    (fun α β ↦ (chowGroupDimPartEquiv k sX (n - j)).symm fun d ↦
      chowGroupDegreeEquiv _ _ (by ring : ((d.down : ℤ) - j) + n - d.down = n - j)
        (dimPartIntersectionProduct k sX d.down (d.down - j) n (α d.down)
          (chowGroupDimPartEquiv k sX n β d)))
    (fun _ _ _ ↦ by rw [← map_add]; congr 1; funext d; simp)
    (fun _ _ _ ↦ by rw [← map_zsmul]; congr 1; funext d; simp)
    (fun _ _ _ ↦ by rw [← map_add]; congr 1; funext d; simp)
    (fun _ _ _ ↦ by rw [← map_zsmul]; congr 1; funext d; simp)

/-- The restriction of `α · β` to the part `X_d` is `α_d · β|_{X_d}`. -/
theorem chowGroupRestrict_codimensionDimensionIntersectionProduct (j n : ℤ)
    (α : codimensionChowGroup k sX j) (β : chowGroup (fieldChowSituation k) sX n) (d : ℕ) :
    chowGroupRestrict (fieldChowSituation k) sX (partBase sX d) (dimPart sX d).ι rfl (n - j)
        (codimensionDimensionIntersectionProduct k sX j n α β) =
      chowGroupDegreeEquiv _ _ (by ring : ((d : ℤ) - j) + n - d = n - j)
        (dimPartIntersectionProduct k sX d (d - j) n (α d)
          (chowGroupRestrict (fieldChowSituation k) sX (partBase sX d) (dimPart sX d).ι rfl n
            β)) := by
  rw [← chowGroupDimPartEquiv_apply k sX (n - j) _ ⟨d⟩]
  refine (congrFun ((chowGroupDimPartEquiv k sX (n - j)).apply_symm_apply _) ⟨d⟩).trans ?_
  rw [chowGroupDimPartEquiv_apply]

end Product

section Gysin

variable {k : Type u} [Field k] {X Y : Scheme.{u}} (sX : X ⟶ (fieldChowSituation k).S)
  [Smooth sX] (i : Y ⟶ X) [IsClosedImmersion i]
  (hreg : Stacks.AlgebraicGeometry.RegularIdealSheaf.IsRegularImmersion i)

/-- A scheme over `S` which is equidimensional of dimension `e` has `δ`-dimension at most `e`. -/
private theorem schemeDeltaDimension_le_of_relativeDimension {k : Type u} [Field k]
    {Y : Scheme.{u}} (f : Y ⟶ (fieldChowSituation k).S) [LocallyOfFiniteType f] (e : ℕ)
    (hY : RelativeDimension f e) :
    schemeDeltaDimension (fieldChowSituation k) f ≤ ((e : ℤ) : EInt) :=
  WeilCohomology.schemeDeltaDimension_le_of_forall_irreducibleComponent _
    (WeilCohomology.deltaDimension_irreducibleComponent_of_relativeDimension k f e hY)

omit [IsClosedImmersion i] in
/-- The pieces `Y ×_X X_d` of `Y` form a decomposition of `Y` into open and closed subschemes:
they are the preimages of the parts `X_d` of `X`. -/
theorem isClopenDecomposition_pullbackFst_dimPart :
    IsClopenDecomposition fun d : ULift.{u} ℕ ↦
      (pullback.fst i (dimPart sX d.down).ι).opensRange := by
  have h := ((isClopenDecomposition_dimPart sX).preimage i).opensRange_ι_equiv Equiv.ulift
  simpa only [Scheme.Hom.opensRange_pullbackFst, Scheme.Opens.opensRange_ι, Equiv.ulift_apply]
    using h

/-- **The Gysin map of `i` on the part `X_d`**, in degree `d - e`: the degree `d - e` term of the
Gysin map `i^! ∈ A^*(Y ⟶ X)^∧` of Stacks 0FF3 (`Stacks.Chow.lciGysinMapComponent`), restricted
along `X_d ⟶ X` (Stacks 0F9Z) to a class of `A^{d-e}(Y ×_X X_d ⟶ X_d)`. -/
def regularImmersionPartGysinClass (e d : ℕ) :
    BivariantClass (fieldChowSituation k) (gysinSystemOfInvertible (fieldChowSituation k))
      (pullback.fst i (dimPart sX d).ι ≫ i ≫ sX) (partBase sX d) (pullback.snd i (dimPart sX d).ι)
      (pullbackSnd_comp_structureMorphism_eq _ (i ≫ sX) sX i rfl _) ((d : ℤ) - e) :=
  bivariantRestriction _ _ (i ≫ sX) sX i rfl (dimPart sX d).ι ((d : ℤ) - e)
    (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso _)
    (lciGysinMapComponent _ (i ≫ sX) sX rfl
      (isLocalCompleteIntersectionMorphism_of_isRegularImmersion i hreg)
      (GysinMapExists.of_isImmersion i) ((d : ℤ) - e))

/-- **Stacks 0FF6 for the Gysin map of `i` on a part.** The restriction of `i^!` to `X_d` commutes
with every bivariant class: the Gysin map commutes with every class after every base change. -/
theorem regularImmersionPartGysinClass_commutesWithEveryClass (e d : ℕ) :
    (regularImmersionPartGysinClass sX i hreg e d).CommutesWithEveryClass := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian (i ≫ sX)
  exact completedCommutesAfterBaseChange_lciGysinMap _ (i ≫ sX) sX rfl _ _ ((d : ℤ) - e)
    (dimPart sX d).ι

/-- **Stacks 0FF7 for the Gysin map of `i` on a part.** If `Y` is equidimensional of dimension
`e`, the degree `d - e` term of `i^!`, capped at the test scheme `X_d ⟶ X`, carries `[X_d]_d` to
`[Y ×_X X_d]_e`, written `[Y ×_X X_d]_{d-(d-e)}`.

`Y` need not be connected, so this is checked on the preimage of each connected component `Y_w`
of `Y`. The Gysin map of `i` is homogeneous on `Y_w` and satisfies the cap formula for fundamental
classes there (`Stacks.Chow.SmoothFactorization.exists_hasCapFundamentalFormula_gysinMap`); when
`Y_w` meets `Y ×_X X_d` it lies over `X_d`, so the connected component of `X` containing `i(Y_w)`
lies in `X_d`, of pure dimension `d`, while the generic points of `Y_w` have `δ = e`: the degree
on `Y_w` is `d - e`, and
`Stacks.Chow.chowGroupRestrict_cap_fundamentalChowClass_of_capFundamentalFormula` applies, every
local ring of `X_d` being Cohen–Macaulay. -/
theorem cap_lciGysinMapComponent_dimPart_fundamentalChowClass (e : ℕ)
    (hY : RelativeDimension (i ≫ sX) e) (d : ℕ) :
    (lciGysinMapComponent (fieldChowSituation k) (i ≫ sX) sX rfl
        (isLocalCompleteIntersectionMorphism_of_isRegularImmersion i hreg)
        (GysinMapExists.of_isImmersion i) ((d : ℤ) - e)).cap (dimPart sX d).ι d
        (fundamentalChowClass (fieldChowSituation k) (partBase sX d) d) =
      fundamentalChowClass (fieldChowSituation k) (pullback.fst i (dimPart sX d).ι ≫ i ≫ sX)
        ((d : ℤ) - ((d : ℤ) - e)) := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian (i ≫ sX)
  have hlci := isLocalCompleteIntersectionMorphism_of_isRegularImmersion i hreg
  have hex := GysinMapExists.of_isImmersion i
  set π := pullback.fst i (dimPart sX d).ι
  have hXd := relativeDimension_partBase sX d
  have hT := WeilCohomology.deltaDimension_irreducibleComponent_of_relativeDimension k
    (partBase sX d) d hXd
  have hYδ := WeilCohomology.deltaDimension_irreducibleComponent_of_relativeDimension k
    (i ≫ sX) e hY
  have hdimY := schemeDeltaDimension_le_of_relativeDimension (i ≫ sX) e hY
  have hdimπ : ∀ ξ : (pullback i (dimPart sX d).ι : Scheme.{u}),
      relativeDimension (fieldChowSituation k).dimensionFunction (π ≫ i ≫ sX) ξ ≤
        (d : ℤ) - ((d : ℤ) - e) := fun ξ ↦ by
    rw [relativeDimension_comp_isOpenImmersion, show (d : ℤ) - ((d : ℤ) - e) = e by ring]
    exact relativeDimension_le_of_schemeDeltaDimension_le' _ _ hdimY _
  have hdimV : schemeDeltaDimension (fieldChowSituation k) (π ≫ i ≫ sX) ≤
      (((d : ℤ) - ((d : ℤ) - e) : ℤ) : EInt) := by
    simpa using schemeDeltaDimension_le_of_forall_relativeDimension_le _ _ (𝟙 _)
      (by simpa using hdimπ)
  -- the Gysin map of `i` is that of its chosen factorization
  obtain ⟨dd, hd, hdeg⟩ := (Classical.choice ((gysinMapExists_iff_nonempty i).1 hex) :
    SmoothFactorization i).exists_hasCapFundamentalFormula_gysinMap (fieldChowSituation k)
      (i ≫ sX) sX rfl hlci
  refine chowGroup_eq_of_chowGroupRestrict_preimage_connectedComponent_eq
    (C := fieldChowSituation k) _ π _ fun w ↦ ?_
  rw [chowGroupRestrict_fundamentalChowClass (fieldChowSituation k) _ _ _ rfl _ hdimV]
  rcases isEmpty_or_nonempty (π ⁻¹ᵁ Y.connectedComponentOpens w).toScheme with hw | ⟨⟨x, hx⟩⟩
  · have := subsingleton_chowGroup_of_isEmpty (fieldChowSituation k)
      ((π ⁻¹ᵁ Y.connectedComponentOpens w).ι ≫ π ≫ i ≫ sX) ((d : ℤ) - ((d : ℤ) - e))
    exact Subsingleton.elim _ _
  -- the connected component `Y_w` lies over `X_d`
  have hXdc : IsClopen ((dimPart sX d : X.Opens) : Set X) :=
    (isClopenDecomposition_dimPart sX).isClopen d
  have hUc : IsClopen (((i ⁻¹ᵁ dimPart sX d : Y.Opens)) : Set Y) := hXdc.preimage i.continuous
  have hxd : π x ∈ i ⁻¹ᵁ dimPart sX d := by
    have h : π x ∈ (pullback.fst i (dimPart sX d).ι).opensRange := ⟨x, rfl⟩
    rwa [Scheme.Hom.opensRange_pullbackFst, Scheme.Opens.opensRange_ι] at h
  have hsub : ∀ y ∈ Y.connectedComponentOpens w, y ∈ i ⁻¹ᵁ dimPart sX d := by
    intro y hy
    refine hUc.connectedComponent_subset hxd ?_
    rw [← ConnectedComponents.coe_eq_coe']
    exact hy.trans hx.symm
  -- the Gysin map has degree `d - e` on `Y_w`
  have hdw : dd w = (d : ℤ) - e := by
    obtain ⟨ξ, hξ, hξw⟩ := exists_mem_genericPoints_mk_eq w
    have hξd : i ξ ∈ dimPart sX d := hsub ξ hξw
    have hV : X.connectedComponentOpens (i.continuous.connectedComponentsMap
        (ConnectedComponents.mk ξ)) ≤ dimPart sX d := by
      intro y hy
      refine hXdc.connectedComponent_subset hξd ?_
      rw [← ConnectedComponents.coe_eq_coe']
      exact hy
    have hδ : relativeDimension (fieldChowSituation k).dimensionFunction (i ≫ sX) ξ = e := by
      rw [← hYδ ⟨_, hξ⟩, deltaDimension_eq_of_isGenericPoint _ _ _ ξ isGenericPoint_closure]
    rw [← hξw, hdeg ξ hξ d fun W ↦ ?_, hδ]
    rw [← WeilCohomology.deltaDimension_congr (X.homOfLE_ι_assoc hV sX)]
    exact deltaDimension_irreducibleComponents_of_isOpenImmersion (fieldChowSituation k)
      (partBase sX d) hT _ W
  have hres := restriction_completedBivariantSequence (fieldChowSituation k)
    (gysinSystemOfInvertible (fieldChowSituation k)) (i ≫ sX) sX i rfl
    (gysinSystemOfInvertible_isNaturalUnderOpenImmersion (fieldChowSituation k))
    (gysinSystemOfInvertible_isNaturalUnderOpensRestriction (fieldChowSituation k))
    (gysinSystemOfInvertible_isNaturalUnderPullbackComp (fieldChowSituation k))
    (lciGysinMap (fieldChowSituation k) (i ≫ sX) sX rfl hlci hex) ((d : ℤ) - e) w
  have hca := (hd w).2 d
  rw [hdw] at hca
  exact chowGroupRestrict_cap_fundamentalChowClass_of_capFundamentalFormula
    (fieldChowSituation k) (i ≫ sX) sX i rfl (completedBivariantSequenceOfInvertible _ (i ≫ sX)
      sX i rfl (lciGysinMap (fieldChowSituation k) (i ≫ sX) sX rfl hlci hex) ((d : ℤ) - e)) w
    (hres ▸ hca) (dimPart sX d).ι hT (fun ξ _ ↦ hdimπ ξ)
    (fun ξ _ _ ↦ WeilCohomology.isCohenMacaulayLocalRing_stalk_of_smooth k (partBase sX d) _)
    _ _ _ (π.resLE (Y.connectedComponentOpens w) (π ⁻¹ᵁ Y.connectedComponentOpens w) le_rfl)
    (Scheme.Hom.resLE_comp_ι _ _)

/-- **Stacks 0FF7 for the Gysin map of `i` on a part.** If `Y` is equidimensional of dimension
`e`, the restriction of `i^!` to `X_d` carries `[X_d]_d` to `[Y ×_X X_d]_e`, written
`[Y ×_X X_d]_{d-(d-e)}`. -/
theorem regularImmersionPartGysinClass_capTargetHom_fundamentalChowClass (e : ℕ)
    (hY : RelativeDimension (i ≫ sX) e) (d : ℕ) :
    (regularImmersionPartGysinClass sX i hreg e d).capTargetHom _ _ _ _ _ _ ((d : ℤ) - e) d
        (fundamentalChowClass (fieldChowSituation k) (partBase sX d) d) =
      fundamentalChowClass (fieldChowSituation k) (pullback.fst i (dimPart sX d).ι ≫ i ≫ sX)
        ((d : ℤ) - ((d : ℤ) - e)) := by
  rw [BivariantClass.capTargetHom_apply, regularImmersionPartGysinClass,
    bivariantRestriction_capTarget (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso _)]
  exact cap_lciGysinMapComponent_dimPart_fundamentalChowClass sX i hreg e hY d

/-- The Gysin map `i^! : CH_{d-j}(X_d) ⟶ CH_{e-j}(Y ×_X X_d)` of `i` on the part `X_d`: cap product
with the restriction of the degree `d - e` term of the Gysin map of `i` to `X_d`
(`Stacks.Chow.regularImmersionPartGysinClass`), which lands in `CH_{(d-j)-(d-e)}(Y ×_X X_d)`. -/
def regularImmersionPartGysin (e d : ℕ) (j : ℤ) :
    chowGroup (fieldChowSituation k) (partBase sX d) (d - j) →+
      chowGroup (fieldChowSituation k) (pullback.fst i (dimPart sX d).ι ≫ i ≫ sX) (e - j) :=
  (chowGroupDegreeEquiv _ _ (by ring : (d : ℤ) - j - ((d : ℤ) - e) = e - j)).toAddMonoidHom.comp
    ((regularImmersionPartGysinClass sX i hreg e d).capTargetHom _ _ _ _ _ _ ((d : ℤ) - e)
      ((d : ℤ) - j))

/-- **The Gysin map of Stacks 0FF3** of a regular closed immersion `i : Y ⟶ X`, with `X` smooth
over `k` and `Y` of dimension `e`, on classes graded by codimension:
`i^! : CH^j(X) ⟶ CH_{e-j}(Y)`, `α ↦ i^!α`, where `i^!α` is the class whose restriction to each
piece `Y ×_X X_d` of `Y` is `i^!(α_d)` (`Stacks.Chow.chowGroupRestrict_regularImmersionGysin`),
for `i^!` the Gysin map of `i` restricted to `X_d` (`Stacks.Chow.regularImmersionPartGysin`). -/
def regularImmersionGysin (e : ℕ) (j : ℤ) :
    codimensionChowGroup k sX j →+ chowGroup (fieldChowSituation k) (i ≫ sX) (e - j) :=
  (chowGroupClopenRestrictEquiv (fieldChowSituation k) (i ≫ sX)
      (fun d : ULift.{u} ℕ ↦ pullback.fst i (dimPart sX d.down).ι ≫ i ≫ sX)
      (fun d : ULift.{u} ℕ ↦ pullback.fst i (dimPart sX d.down).ι) (fun _ ↦ rfl)
      (isClopenDecomposition_pullbackFst_dimPart sX i) (e - j)).symm.toAddMonoidHom.comp
    (AddMonoidHom.pi fun d : ULift.{u} ℕ ↦ (regularImmersionPartGysin sX i hreg e d.down j).comp
      (Pi.evalAddMonoidHom (fun d : ℕ ↦ chowGroup (fieldChowSituation k) (partBase sX d)
        (d - j)) d.down))

/-- **The restriction of `i^!α` to the piece `Y ×_X X_d` is `i^!(α_d)`.** -/
theorem chowGroupRestrict_regularImmersionGysin (e : ℕ) (j : ℤ) (α : codimensionChowGroup k sX j)
    (d : ℕ) :
    chowGroupRestrict (fieldChowSituation k) (i ≫ sX)
        (pullback.fst i (dimPart sX d).ι ≫ i ≫ sX) (pullback.fst i (dimPart sX d).ι) rfl (e - j)
        (regularImmersionGysin sX i hreg e j α) =
      regularImmersionPartGysin sX i hreg e d j (α d) := by
  have h := congrFun ((chowGroupClopenRestrictEquiv (fieldChowSituation k) (i ≫ sX)
      (fun d : ULift.{u} ℕ ↦ pullback.fst i (dimPart sX d.down).ι ≫ i ≫ sX)
      (fun d : ULift.{u} ℕ ↦ pullback.fst i (dimPart sX d.down).ι) (fun _ ↦ rfl)
      (isClopenDecomposition_pullbackFst_dimPart sX i) (e - j)).apply_symm_apply
    fun d : ULift.{u} ℕ ↦ regularImmersionPartGysin sX i hreg e d.down j (α d.down)) ⟨d⟩
  rw [chowGroupClopenRestrictEquiv_apply] at h
  exact h

end Gysin

section Main

variable {k : Type u} [Field k] {X Y : Scheme.{u}} (sX : X ⟶ (fieldChowSituation k).S)
  [Smooth sX] (i : Y ⟶ X) [IsClosedImmersion i]

/-- **Stacks 0FFE: `α · [Y]_e = i_*(i^!α)`.** Let `k` be a field, let `X` be a scheme smooth over
`k`, of arbitrary and not necessarily constant dimension, and let `i : Y ⟶ X` be a regular closed
immersion with `Y` equidimensional of dimension `e`. Then for every `α ∈ CH^j(X)`

  `α · i_*[Y]_e = i_*(i^!α)`   in   `CH_{e-j}(X)`,

for `·` the intersection product of Section 0FC0, formed part by part on the open and closed parts
`X_d` of `X` of constant dimension (`Stacks.Chow.codimensionDimensionIntersectionProduct`),
`[Y]_e` the fundamental class of Stacks 0FE4, `i_*` proper pushforward, and `i^!` the Gysin map of
Stacks 0FF3 of `i` acting part by part (`Stacks.Chow.regularImmersionGysin`).

Both sides are compared on each part `X_d`. Writing `α_d = c ∩ [X_d]_d` (Stacks 0FC2), the
source's chain `i_*(i^!(c ∩ [X_d]_d)) = i_*(c ∩ i^![X_d]_d) = i_*(c ∩ [Y_d]_e) = c ∩ i_*[Y_d]_e =
α_d · [Y_d]_e` is Stacks 0FF6
(`Stacks.Chow.regularImmersionPartGysinClass_commutesWithEveryClass`), Stacks 0FF7
(`Stacks.Chow.regularImmersionPartGysinClass_capTargetHom_fundamentalChowClass`), the projection
formula of a bivariant class (`Stacks.Chow.chowCohomologyCap_properChowPushforward_restriction`)
and Stacks 0FC2 (`Stacks.WeilCohomology.canonicalDiagonalClassFamily_capEqProduct`). See the
module documentation for the grading. -/
@[stacks 0FFE "the whole statement for a regular closed immersion i : Y → X with X smooth over a \
field, of arbitrary dimension, and Y equidimensional of dimension e: α · [Y]_e = i_*(i^!(α)) \
for every j and every α ∈ CH^j(X), the classes graded by codimension on the open and closed parts \
X_d of X of constant dimension, both sides in CH_{e-j}(X); i^! is the Gysin map of i itself \
acting part by part, and the product is formed part by part on the X_d"]
theorem intersectionProduct_fundamentalChowClass_eq_pushforward_regularImmersionGysin
    (hreg : Stacks.AlgebraicGeometry.RegularIdealSheaf.IsRegularImmersion i) (e : ℕ)
    (hY : RelativeDimension (i ≫ sX) e) (j : ℤ) (α : codimensionChowGroup k sX j) :
    codimensionDimensionIntersectionProduct k sX j e α
        (properChowPushforward (fieldChowSituation k) (i ≫ sX) sX i rfl e
          (properPushforwardDescends _ _ _ _ _ _)
          (fundamentalChowClass (fieldChowSituation k) (i ≫ sX) e)) =
      properChowPushforward (fieldChowSituation k) (i ≫ sX) sX i rfl (e - j)
        (properPushforwardDescends _ _ _ _ _ _) (regularImmersionGysin sX i hreg e j α) := by
  refine (chowGroupDimPartEquiv k sX (e - j)).injective (funext fun d ↦ ?_)
  obtain ⟨d⟩ := d
  have hXd := relativeDimension_partBase sX d
  have hgys : (fieldGysinSystem k).IsNaturalUnderBaseChangeIso :=
    gysinSystemOfInvertible_isNaturalUnderBaseChangeIso _
  have hq : pullback.snd i (dimPart sX d).ι ≫ partBase sX d =
      pullback.fst i (dimPart sX d).ι ≫ i ≫ sX :=
    pullbackSnd_comp_structureMorphism_eq _ (i ≫ sX) sX i rfl (dimPart sX d).ι
  have hdimY := schemeDeltaDimension_le_of_relativeDimension (i ≫ sX) e hY
  -- restriction to `X_d` commutes with `i_*` (Stacks 02RG for an open immersion)
  have hpush : ∀ (m : ℤ) (γ : chowGroup (fieldChowSituation k) (i ≫ sX) m),
      chowGroupRestrict (fieldChowSituation k) sX (partBase sX d) (dimPart sX d).ι rfl m
          (properChowPushforward (fieldChowSituation k) (i ≫ sX) sX i rfl m
            (properPushforwardDescends _ _ _ _ _ _) γ) =
        properChowPushforward (fieldChowSituation k) (pullback.fst i (dimPart sX d).ι ≫ i ≫ sX)
          (partBase sX d) (pullback.snd i (dimPart sX d).ι) hq m
          (properPushforwardDescends _ _ _ _ _ _)
          (chowGroupRestrict (fieldChowSituation k) (i ≫ sX)
            (pullback.fst i (dimPart sX d).ι ≫ i ≫ sX) (pullback.fst i (dimPart sX d).ι) rfl m
            γ) :=
    fun m γ ↦ chowGroupRestrict_properChowPushforward _ (i ≫ sX) sX
      (pullback.fst i (dimPart sX d).ι ≫ i ≫ sX) (partBase sX d) i rfl
      (pullback.fst i (dimPart sX d).ι) rfl (dimPart sX d).ι rfl
      (pullback.snd i (dimPart sX d).ι) hq (IsPullback.of_hasPullback i (dimPart sX d).ι) m
      (properPushforwardDescends _ _ _ _ _ _) (properPushforwardDescends _ _ _ _ _ _) γ
  rw [chowGroupDimPartEquiv_apply, chowGroupDimPartEquiv_apply,
    chowGroupRestrict_codimensionDimensionIntersectionProduct, hpush, hpush,
    chowGroupRestrict_fundamentalChowClass (fieldChowSituation k) _ _ _ rfl _ hdimY,
    chowGroupRestrict_regularImmersionGysin]
  obtain ⟨c, hc⟩ := capFundamentalClassSurjective k (partBase sX d) d hXd j (α d)
  -- `i_*(res(c) ∩ [Y_d]_e) = c ∩ i_*[Y_d]_e = α_d · i_*[Y_d]_e`
  have hproj := chowCohomologyCap_properChowPushforward_restriction (fieldChowSituation k)
    (fieldGysinSystem k) hgys (pullback.fst i (dimPart sX d).ι ≫ i ≫ sX) (partBase sX d) hq j c e
    (fundamentalChowClass (fieldChowSituation k) (pullback.fst i (dimPart sX d).ι ≫ i ≫ sX) e)
  rw [canonicalDiagonalClassFamily_capEqProduct k _ d hXd j c e, hc,
    chowCohomologyCap_fundamentalChowClass] at hproj
  -- `i^!(α_d) = res(c) ∩ [Y_d]_e`, by Stacks 0FF6 and Stacks 0FF7
  have hβ : regularImmersionPartGysin sX i hreg e d j (α d) =
      chowCohomologyCapFundamentalClass (fieldChowSituation k) (fieldGysinSystem k)
        (pullback.fst i (dimPart sX d).ι ≫ i ≫ sX) e j
        (chowCohomologyRestrictionOfEq (fieldChowSituation k)
          (pullback.fst i (dimPart sX d).ι ≫ i ≫ sX) (partBase sX d) hq (fieldGysinSystem k) hgys
          j c) := by
    rw [← hc]
    exact eq_of_heq ((chowGroupDegreeEquiv_heq _ _ _ _).trans
      (BivariantClass.capTargetHom_chowCohomologyCapFundamentalClass_heq _ _ hgys _ _ j hq
        ((d : ℤ) - e) (regularImmersionPartGysinClass sX i hreg e d) c
        (regularImmersionPartGysinClass_commutesWithEveryClass sX i hreg e d (𝟙 _) j _) d
        (regularImmersionPartGysinClass_capTargetHom_fundamentalChowClass sX i hreg e hY d)
        (by ring)))
  rw [hβ]
  exact hproj

end Main

end Stacks.Chow

end
