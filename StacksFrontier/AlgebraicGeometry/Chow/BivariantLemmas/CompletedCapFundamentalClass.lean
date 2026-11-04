module

public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.CompletedGroup
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.CapFundamentalClass
public import StacksFrontier.AlgebraicGeometry.Chow.Codimension.FundamentalClass
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.Vanishing
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant42.FlatPullbackComponent
public import StacksFrontier.AlgebraicGeometry.Chow.ExteriorProductAssociativity
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantDisjoint.PieceAssembly
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassHigher.Transport
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantComposition.Basic
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.ExcessIntersection
public import StacksFrontier.AlgebraicGeometry.Chow.GysinLocalCompleteIntersection.LciGysinFundamentalClass
public import StacksFrontier.AlgebraicGeometry.Chow.GysinAtInfinity.FundamentalClass
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantDisjoint.OpenPieceDimension

/-!
# Capping a completed bivariant class with the fundamental class

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project and let `Y` be a scheme
locally of finite type over `S` satisfying the equivalent conditions of Stacks 0FE3, so that
`Y = ∐_n Y_n` with every irreducible component of `Y_n` of `δ`-dimension `n`. Stacks 0FE4 defines
its fundamental class `[Y] = ∑_n [Y_n]_n`. A connected component `Y_b` of `Y` lies in exactly one
piece `Y_{n_b}`, and the restriction of `[Y_{n_b}]_{n_b}` to it is `[Y_b]_{n_b}`
(`Stacks.Chow.chowGroupRestrict_fundamentalClass`). As `Y` may have infinitely many connected
components, the fundamental class is recorded componentwise
(`Stacks.Chow.componentFundamentalClassDirectSum`), in `∏_b ⊕_k CH_k(Y_b)`.

For `f : X ⟶ Y` and a completed class `c ∈ A^*(X ⟶ Y)^∧` (Stacks 0FE0), the cap product `c ∩ [Y]`
(`Stacks.Chow.completedCapFundamentalClass`) is computed on each connected component `X_w` of `X`,
lying over `Y_b`: it is `∑_p c_{w,p} ∩ [Y_b]_{n_b}`, a finite sum since `c` has finite degree
support on `X_w`, the term of degree `p` lying in `CH_{n_b - p}(X_w)`. This is the cap product
`f^![Y']` of Stacks 0FF7.

The fundamental class `Stacks.Chow.totalFundamentalClass` of a Noetherian scheme is not used: a
scheme locally of finite type need not have finitely many irreducible components, nor need its
connected components be quasi-compact.

## Main definitions

* `Stacks.Chow.componentDeltaDimension` — the `δ`-dimension `n_b` of the piece of the dimension
  decomposition containing a connected component.
* `Stacks.Chow.componentFundamentalClassDirectSum` — `[Y]`, read on the connected components of
  `Y`.
* `Stacks.Chow.completedCapFundamentalClass` — `c ↦ c ∩ [Y]` for completed classes.

## Main results

* `Stacks.Chow.chowGroupRestrict_fundamentalClass` — the restriction of the fundamental class of
  Stacks 0FE4 to a connected component is the component's fundamental class.

## References

* [Stacks Project, Tag 0FE3](https://stacks.math.columbia.edu/tag/0FE3)
* [Stacks Project, Tag 0FE4](https://stacks.math.columbia.edu/tag/0FE4)
* [Stacks Project, Tag 0FE0](https://stacks.math.columbia.edu/tag/0FE0)
* [Stacks Project, Tag 0FF7](https://stacks.math.columbia.edu/tag/0FF7)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

section Fundamental

variable (C : ChowSituation.{u}) {Y : Scheme.{u}} (sY : Y ⟶ C.S) [LocallyOfFiniteType sY]
  [IsLocallyNoetherian Y]
  (hY : HasDimensionDecomposition (relativeDimension C.dimensionFunction sY))

omit [LocallyOfFiniteType sY] [IsLocallyNoetherian Y] in
/-- A connected component lies in some piece of a dimension decomposition. -/
theorem exists_connectedComponent_mem_dimensionDecomposition (b : _root_.ConnectedComponents Y) :
    ∃ n : ℤ, (_root_.ConnectedComponents.surjective_coe b).choose ∈ Classical.choose hY n := by
  have h := (Classical.choose_spec hY).1.iSup_eq_top
  have hx : (_root_.ConnectedComponents.surjective_coe b).choose ∈ (⊤ : Y.Opens) := trivial
  rw [← h] at hx
  exact TopologicalSpace.Opens.mem_iSup.1 hx

/-- **The `δ`-dimension of a connected component**: the index `n_b` of the piece `Y_{n_b}` of the
dimension decomposition of Stacks 0FE3 containing the connected component `Y_b`. -/
def componentDeltaDimension (b : _root_.ConnectedComponents Y) : ℤ :=
  (exists_connectedComponent_mem_dimensionDecomposition C sY hY b).choose

omit [LocallyOfFiniteType sY] in
/-- A connected component is contained in the piece of the dimension decomposition indexed by its
`δ`-dimension: the piece is open and closed, and meets the component. -/
theorem connectedComponentOpens_le_dimensionDecomposition (b : _root_.ConnectedComponents Y) :
    Y.connectedComponentOpens b ≤ Classical.choose hY (componentDeltaDimension C sY hY b) := by
  set x₀ := (_root_.ConnectedComponents.surjective_coe b).choose
  have hx₀ : (x₀ : _root_.ConnectedComponents Y) = b :=
    (_root_.ConnectedComponents.surjective_coe b).choose_spec
  have hmem := (exists_connectedComponent_mem_dimensionDecomposition C sY hY b).choose_spec
  set U := Classical.choose hY (componentDeltaDimension C sY hY b)
  have hclopen : IsClopen (U : Set Y) := (Classical.choose_spec hY).1.isClopen _
  intro x hx
  have hxc : x ∈ connectedComponent x₀ := by
    rw [← connectedComponents_preimage_singleton]
    exact ((Scheme.mem_connectedComponentOpens Y).1 hx).trans hx₀.symm
  exact hclopen.connectedComponent_subset hmem hxc

/-- **Stacks 0FE4, on connected components.** The fundamental class `[Y] = ∑_n [Y_n]_n` of a scheme
satisfying the conditions of Stacks 0FE3, read on its connected components: on `Y_b` it is the
fundamental class `[Y_b]_{n_b}`, placed in degree `n_b`
(`Stacks.Chow.chowGroupRestrict_fundamentalClass`). -/
def componentFundamentalClassDirectSum :
    ∀ b : _root_.ConnectedComponents Y,
      DirectSum ℤ fun k ↦ chowGroup C ((Y.connectedComponentOpens b).ι ≫ sY) k :=
  fun b ↦ DirectSum.of _ (componentDeltaDimension C sY hY b)
    (fundamentalChowClass C ((Y.connectedComponentOpens b).ι ≫ sY)
      (componentDeltaDimension C sY hY b))

/-- **The fundamental class of Stacks 0FE4 restricts to the fundamental class of a connected
component.** The `n_b`-th coordinate `[Y_{n_b}]_{n_b}` of `[Y]`, restricted to the connected
component `Y_b ⊆ Y_{n_b}`, is `[Y_b]_{n_b}`. -/
theorem chowGroupRestrict_fundamentalClass (b : _root_.ConnectedComponents Y) :
    chowGroupRestrict C ((Classical.choose hY (componentDeltaDimension C sY hY b)).ι ≫ sY)
        ((Y.connectedComponentOpens b).ι ≫ sY)
        (Y.homOfLE (connectedComponentOpens_le_dimensionDecomposition C sY hY b))
        (by rw [← Category.assoc, Scheme.homOfLE_ι]) (componentDeltaDimension C sY hY b)
        (fundamentalClass C sY hY (componentDeltaDimension C sY hY b)) =
      fundamentalChowClass C ((Y.connectedComponentOpens b).ι ≫ sY)
        (componentDeltaDimension C sY hY b) := by
  set n := componentDeltaDimension C sY hY b
  set U := Classical.choose hY n
  have hdim : schemeDeltaDimension C (U.ι ≫ sY) ≤ (n : EInt) := by
    refine iSup_le fun Z ↦ ?_
    have hgen := Z.2.1.isGenericPoint_genericPoint (isClosed_of_mem_irreducibleComponents _ Z.2)
    rw [deltaDimension_eq_of_isGenericPoint C _ _ _ hgen, relativeDimension_opensι_comp]
    exact le_of_eq (congrArg _ ((Classical.choose_spec hY).2 n Z Z.2 _ hgen))
  exact chowGroupRestrict_fundamentalChowClass C _ _ _ _ n hdim

end Fundamental

section Cap

variable (C : ChowSituation.{u}) (G : GysinSystem C) {X Y : Scheme.{u}} (sX : X ⟶ C.S)
  [LocallyOfFiniteType sX] (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (f : X ⟶ Y)
  [LocallyOfFiniteType f] (hf : f ≫ sY = sX) [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
  (hY : HasDimensionDecomposition (relativeDimension C.dimensionFunction sY))

open scoped Classical in
/-- **The cap product `c ∩ [Y]` of a completed class with the fundamental class of Stacks 0FE4.**
For `c ∈ A^*(X ⟶ Y)^∧` (Stacks 0FE0) and `Y` satisfying the conditions of Stacks 0FE3, on the
connected component `X_w` of `X`, lying over `Y_b`, it is the finite sum
`∑_p c_{w,p} ∩ [Y_b]_{n_b} ∈ ⊕_k CH_k(X_w)`, the term of degree `p` lying in `CH_{n_b - p}(X_w)`
(`Stacks.Chow.capFundamentalClassAt`). -/
def completedCapFundamentalClass (c : completedBivariantGroup C G sX sY f hf) :
    ∀ w : _root_.ConnectedComponents X,
      DirectSum ℤ fun k ↦ chowGroup C ((X.connectedComponentOpens w).ι ≫ sX) k :=
  fun w ↦ ∑ p ∈ (c w).support, DirectSum.of _
    (componentDeltaDimension C sY hY (f.continuous.connectedComponentsMap w) - p)
    (capFundamentalClassAt C G _ _ (f.resConnectedComponent w)
      (f.resConnectedComponent_comp_ι_comp hf w) p
      (componentDeltaDimension C sY hY (f.continuous.connectedComponentsMap w)) (c w p))

end Cap

end Stacks.Chow

end
