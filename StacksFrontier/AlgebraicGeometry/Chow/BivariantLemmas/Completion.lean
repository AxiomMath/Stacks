module

public import StacksFrontier.AlgebraicGeometry.Chow.BivariantComposition.Class
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantComposition.GysinSystemOfInvertible
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantDisjoint.PieceGysinSystemOfInvertible
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.CompletedGroup
public import Mathlib.Algebra.Group.Subgroup.Ker

/-!
# The completed bivariant group as a group of sequences, and composition on completions

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project and let `f : X ⟶ Y` be a
morphism of schemes locally of finite type over `S`. Writing `X = ∐_{i ∈ I} X_i` and
`Y = ∐_{j ∈ J} Y_j` for the decompositions into connected components and `a : I → J` for the map
with `f(X_i) ⊆ Y_{a(i)}`, the completed bivariant group of Stacks 0FE0 is

  `A^*(X ⟶ Y)^∧ = ∏_i A^*(X_i ⟶ Y_{a(i)})`,

which is `Stacks.Chow.completedBivariantGroup`. Stacks 0FE0 makes two further assertions about it,
and this file proves both.

First, the tag reads `A^*(X ⟶ Y)^∧` as a *subgroup of the product of the bivariant groups of
`f` itself*: through the decomposition `A^p(X ⟶ Y) = ∏_i A^p(X_i ⟶ Y_{a(i)})` of Stacks 0FDZ it is
the set of tuples `c = (c_0, c_1, c_2, …)` in `∏_p A^p(X ⟶ Y)` such that, for every connected
component `X_i` of `X`, the image of `c_p` in `A^p(X_i ⟶ Y_{a(i)})` vanishes for almost all `p`.
That subgroup is `Stacks.Chow.completedBivariantSubgroup`, and the identification is
`Stacks.Chow.completedBivariantGroupEquiv`.

Second, given a further morphism `g : Y ⟶ Z` the composition
`A^p(X ⟶ Y) × A^q(Y ⟶ Z) ⟶ A^{p+q}(X ⟶ Z)` of Stacks 0B75 extends to the completions,

  `A^*(X ⟶ Y)^∧ × A^*(Y ⟶ Z)^∧ ⟶ A^*(X ⟶ Z)^∧`.

That extension is `Stacks.Chow.completedBivariantComposite`: on the component `X_i` it is the
convolution of the composition of Stacks 0B75 for the restrictions `X_i ⟶ Y_{a(i)}` and
`Y_{a(i)} ⟶ Z_{b(a(i))}`, which is defined because each factor has finite degree support there.

Taking `Y = X` and `f = 𝟙 X` the group is the *completed bivariant cohomology ring* `A^*(X)^∧` of
the tag, and its multiplication is the composition above at `f = g = 𝟙 X`.

## Main definitions

* `Stacks.Chow.completedBivariantSubgroup` — the subgroup of `∏_p A^p(X ⟶ Y)` of tuples whose
  component in `A^p(X_i ⟶ Y_{a(i)})` vanishes for almost all `p`, for each `i`.
* `Stacks.Chow.completedBivariantSubgroupOfInvertible` — **Stacks 0FE0**, that subgroup at the
  Gysin system of the first Chern class rule, where nothing is assumed.
* `Stacks.Chow.completedBivariantGroupEquiv` — the identification of `A^*(X ⟶ Y)^∧` with that
  subgroup.
* `Stacks.Chow.completedBivariantGroupEquivOfInvertible` — **Stacks 0FE0**, the same
  identification at the Gysin system of the first Chern class rule, where nothing is assumed.
* `Stacks.Chow.completedBivariantComposite` — the composition on the completions.
* `Stacks.Chow.completedBivariantCompositeOfInvertible` — **Stacks 0FE0**, that composition at the
  Gysin system of the first Chern class rule, where nothing is assumed.
* `Stacks.Chow.completedChowCohomology` — **Stacks 0FE0**, the completed bivariant cohomology
  ring `A^*(X)^∧ = A^*(X ⟶ X)^∧`.

## Main results

* `Stacks.Chow.completedBivariantSequence` and
  `Stacks.Chow.completedBivariantSequence_injective` — the map `A^*(X ⟶ Y)^∧ ⟶ ∏_p A^p(X ⟶ Y)`
  that realizes the completed group inside the product, and its injectivity.
* `Stacks.Chow.range_completedBivariantSequence` and
  `Stacks.Chow.range_completedBivariantSequenceOfInvertible` — its image is exactly
  `Stacks.Chow.completedBivariantSubgroup`, which is the content of the inclusion the tag writes;
  the second is the same equality at the Gysin system of the first Chern class rule, where
  nothing is assumed.
* `Stacks.Chow.completedBivariantComposite_of_of` and
  `Stacks.Chow.completedBivariantCompositeOfInvertible_of_of` — on classes concentrated in
  degrees `p` and `q`, the composition on the completions is the composite of Stacks 0B75 in
  degree `p + q`; this is what makes it an extension of the given composition rather than a new
  operation.

## Implementation notes

### The two Gysin parametricities, and which declaration carries which

Both halves of the tag are stated twice: once for an arbitrary `Stacks.Chow.GysinSystem` `G`,
carrying the Gysin compatibilities that an arbitrary such system does not satisfy, and once for
the *constructed* system `Stacks.Chow.gysinSystemOfInvertible`, where every one of them is a
theorem and nothing is assumed.

* The identification uses Stacks 0FDZ, which `Stacks.Chow.bivariantPieceEquiv` states carrying
  `Stacks.Chow.GysinSystem.IsNaturalUnderOpenImmersion`,
  `Stacks.Chow.GysinSystem.IsNaturalUnderOpensRestriction` and
  `Stacks.Chow.GysinSystem.IsNaturalUnderPullbackComp`. For `Stacks.Chow.gysinSystemOfInvertible`
  all three are theorems, so `Stacks.Chow.completedBivariantGroupEquivOfInvertible` states the
  identification with no hypothesis at all. Only the first of the three is needed to *restrict* a
  class to a component, so `Stacks.Chow.completedBivariantSubgroup` carries only that one, and
  `Stacks.Chow.completedBivariantSubgroupOfInvertible` is that subgroup with it discharged.
* The composition uses Stacks 0B75, which `Stacks.Chow.bivariantComposite` states carrying
  `Stacks.Chow.GysinSystem.IsNaturalUnderBaseChangeIso` and
  `Stacks.Chow.GysinSystem.IsNaturalUnderPullbackCompPushforward`; see the implementation notes of
  `StacksFrontier.AlgebraicGeometry.Chow.BivariantComposition.Class`. Both are theorems for
  `Stacks.Chow.gysinSystemOfInvertible`, by
  `Stacks.Chow.gysinSystemOfInvertible_isNaturalUnderBaseChangeIso` and
  `Stacks.Chow.gysinSystemOfInvertible_isNaturalUnderPullbackCompPushforward`, so
  `Stacks.Chow.completedBivariantCompositeOfInvertible` states the composition on the completions
  with no hypothesis either. `Stacks.Chow.completedBivariantComposite` keeps the two hypotheses,
  for a system supplied from outside.

### Degrees range over `ℤ`

A bivariant class has a degree `p ∈ ℤ` throughout this repository, and
`Stacks.Chow.completedBivariantGroup` accordingly sums over `ℤ`. The product the tag writes is
`∏_{p ≥ 0} A^p(X ⟶ Y)`; what is proved here is the statement over all of `ℤ`, of which that is the
part in nonnegative degrees. The same convention is used by
`Stacks.Chow.chowCohomology`.

### Why the composition needs a transport

The completed group of `f ≫ g` is indexed by the connected components of `X`, its `i`-th factor
being built from the component of `Z` selected by `f ≫ g` and from
`AlgebraicGeometry.Scheme.Hom.resConnectedComponent (f ≫ g) i`, whereas composing restriction by
restriction produces a class for the component selected by `g` after `f` and for the composite of
the two restrictions. The two indices agree by
`AlgebraicGeometry.Scheme.Hom.connectedComponentsMap_comp` and the two morphisms then agree by
`AlgebraicGeometry.Scheme.Hom.heq_resConnectedComponent_comp`, the inclusion of a connected
component being a monomorphism; `Stacks.Chow.bivariantClassComponentCongr` turns that pair of
equalities into the identification of the two groups of bivariant classes, by substituting them.

### The convolution

Composition is bilinear (`Stacks.Chow.bivariantCompositeBilinear`), so the convolution of two
families of finite degree support is the general construction
`Stacks.Chow.directSumBilinear` applied to it: no choice of support enters, and
`Stacks.Chow.directSumBilinear_of_of` evaluates it on homogeneous classes.

Local Noetherianity of the three schemes — which is what makes the connected components open — is
assumed as an instance rather than derived in each declaration. It follows from local finite type
over the base by `AlgebraicGeometry.LocallyOfFiniteType.isLocallyNoetherian`, so it is no extra
hypothesis, and being a `Prop` class it agrees with the instance
`Stacks.Chow.completedBivariantGroup` supplies internally.

## References

* [Stacks Project, Tag 0FE0](https://stacks.math.columbia.edu/tag/0FE0)
* [Stacks Project, Tag 0FDZ](https://stacks.math.columbia.edu/tag/0FDZ)
* [Stacks Project, Tag 0B75](https://stacks.math.columbia.edu/tag/0B75)
* [Stacks Project, Tag 0B76](https://stacks.math.columbia.edu/tag/0B76)
* [Stacks Project, Tag 02TA](https://stacks.math.columbia.edu/tag/02TA)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u v

namespace AlgebraicGeometry.Scheme.Hom

/-- Taking the connected component of the image is functorial: the component of `Z` that a
component of `X` lands in under `f ≫ g` is the one it lands in after `f` and then `g`. -/
theorem connectedComponentsMap_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (i : ConnectedComponents X) :
    (f ≫ g).continuous.connectedComponentsMap i =
      g.continuous.connectedComponentsMap (f.continuous.connectedComponentsMap i) := by
  obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe i
  rw [(f ≫ g).continuous.connectedComponentsMap_mk x, f.continuous.connectedComponentsMap_mk x,
    g.continuous.connectedComponentsMap_mk (f.base x)]
  rfl

variable {X Y Z : Scheme.{u}} [LocallyConnectedSpace X] [LocallyConnectedSpace Y]
  [LocallyConnectedSpace Z]

/-- Two morphisms into connected components of `Z` indexed by equal components agree, up to the
transport of their targets, as soon as they agree after the component inclusions: those
inclusions are open immersions, hence monomorphisms. -/
theorem heq_of_comp_connectedComponentOpens_ι {W : Scheme.{u}}
    {j₁ j₂ : ConnectedComponents Z} (hj : j₁ = j₂)
    (u₁ : W ⟶ (Z.connectedComponentOpens j₁ : Scheme.{u}))
    (u₂ : W ⟶ (Z.connectedComponentOpens j₂ : Scheme.{u}))
    (h : u₁ ≫ (Z.connectedComponentOpens j₁).ι = u₂ ≫ (Z.connectedComponentOpens j₂).ι) :
    u₁ ≍ u₂ := by
  subst hj
  exact heq_of_eq ((cancel_mono _).1 h)

/-- The restriction of a composite to a connected component of its source is the composite of the
restrictions, up to the transport along the equality of target components of
`AlgebraicGeometry.Scheme.Hom.connectedComponentsMap_comp`. -/
theorem heq_resConnectedComponent_comp (f : X ⟶ Y) (g : Y ⟶ Z) (i : ConnectedComponents X) :
    (f ≫ g).resConnectedComponent i ≍
      f.resConnectedComponent i ≫
        g.resConnectedComponent (f.continuous.connectedComponentsMap i) := by
  refine heq_of_comp_connectedComponentOpens_ι (connectedComponentsMap_comp f g i) _ _ ?_
  rw [resConnectedComponent_comp_ι, Category.assoc, resConnectedComponent_comp_ι,
    resConnectedComponent_comp_ι_assoc]

end AlgebraicGeometry.Scheme.Hom

namespace Stacks.Chow

/-! ### Convolution of two graded groups along a bilinear pairing -/

/-- The convolution of a bilinear pairing `m` of two `ℤ`-graded abelian groups: the bilinear map
`(⊕_p A_p) × (⊕_q B_q) ⟶ ⊕_n D_n` whose value on homogeneous elements `a` of degree `p` and `b`
of degree `q` is `m p q a b`, placed in degree `p + q`. -/
def directSumBilinear {A B D : ℤ → Type v} [∀ p, AddCommGroup (A p)] [∀ q, AddCommGroup (B q)]
    [∀ n, AddCommGroup (D n)] (m : ∀ p q, A p →+ B q →+ D (p + q)) :
    DirectSum ℤ A →+ DirectSum ℤ B →+ DirectSum ℤ D :=
  DirectSum.toAddMonoid fun p ↦ AddMonoidHom.mk'
    (fun a ↦ DirectSum.toAddMonoid fun q ↦ (DirectSum.of D (p + q)).comp (m p q a))
    (fun _ _ ↦ DirectSum.addHom_ext fun _ _ ↦ by simp)

/-- The convolution of a bilinear pairing, on homogeneous elements. -/
@[simp]
theorem directSumBilinear_of_of {A B D : ℤ → Type v} [∀ p, AddCommGroup (A p)]
    [∀ q, AddCommGroup (B q)] [∀ n, AddCommGroup (D n)] (m : ∀ p q, A p →+ B q →+ D (p + q))
    (p q : ℤ) (a : A p) (b : B q) :
    directSumBilinear m (DirectSum.of A p a) (DirectSum.of B q b) =
      DirectSum.of D (p + q) (m p q a b) := by
  rw [directSumBilinear, DirectSum.toAddMonoid_of]
  simp

/-- A degreewise isomorphism of graded groups carries a homogeneous element to a homogeneous
element of the same degree. -/
theorem mapRange_addEquiv_of {A B : ℤ → Type v} [∀ n, AddCommGroup (A n)]
    [∀ n, AddCommGroup (B n)] (e : ∀ n, A n ≃+ B n) (n : ℤ) (x : A n) :
    DFinsupp.mapRange.addEquiv e (DirectSum.of A n x) = DirectSum.of B n (e n x) := by
  refine DirectSum.ext fun m ↦ ?_
  rcases eq_or_ne m n with rfl | hm <;>
    simp [DFinsupp.mapRange.addEquiv_apply, DFinsupp.mapRange_apply, DirectSum.of_eq_of_ne, *]

/-- A family of elements of a graded group, almost all of them zero, as an element of the direct
sum. -/
def directSumOfFinite {ι : Type*} [DecidableEq ι] {β : ι → Type*} [∀ i, AddCommMonoid (β i)]
    (x : ∀ i, β i) (hx : {i | x i ≠ 0}.Finite) : DirectSum ι β :=
  DirectSum.mk β hx.toFinset fun i ↦ x i

/-- The components of `Stacks.Chow.directSumOfFinite` are the given family. -/
@[simp]
theorem directSumOfFinite_apply {ι : Type*} [DecidableEq ι] {β : ι → Type*}
    [∀ i, AddCommMonoid (β i)] (x : ∀ i, β i) (hx : {i | x i ≠ 0}.Finite) (i : ι) :
    directSumOfFinite x hx i = x i := by
  by_cases h : x i = 0
  · rw [directSumOfFinite, DirectSum.mk_apply_of_notMem, h]
    simpa [hx.mem_toFinset] using h
  · exact DirectSum.mk_apply_of_mem (hx.mem_toFinset.2 h)

/-! ### Transport along an equality of target connected components -/

section Congr

variable (C : ChowSituation.{u}) (G : GysinSystem C) {W Z : Scheme.{u}} (sW : W ⟶ C.S)
  [LocallyOfFiniteType sW] (sZ : Z ⟶ C.S) [LocallyOfFiniteType sZ] [LocallyConnectedSpace Z]

/-- Bivariant classes for two morphisms into connected components of `Z` indexed by equal
components, which agree up to the transport along that equality, are the same group. -/
def bivariantClassComponentCongr {j₁ j₂ : ConnectedComponents Z} (hj : j₁ = j₂)
    (u₁ : W ⟶ (Z.connectedComponentOpens j₁ : Scheme.{u})) [LocallyOfFiniteType u₁]
    (u₂ : W ⟶ (Z.connectedComponentOpens j₂ : Scheme.{u})) [LocallyOfFiniteType u₂]
    (hu : u₁ ≍ u₂)
    (h₁ : u₁ ≫ ((Z.connectedComponentOpens j₁).ι ≫ sZ) = sW)
    (h₂ : u₂ ≫ ((Z.connectedComponentOpens j₂).ι ≫ sZ) = sW) (n : ℤ) :
    BivariantClass C G sW ((Z.connectedComponentOpens j₁).ι ≫ sZ) u₁ h₁ n ≃+
      BivariantClass C G sW ((Z.connectedComponentOpens j₂).ι ≫ sZ) u₂ h₂ n := by
  subst hj
  obtain rfl := eq_of_heq hu
  exact AddEquiv.refl _

end Congr

/-! ### Stacks 0FDZ at the connected components -/

section Components

variable (C : ChowSituation.{u}) (G : GysinSystem C) {X Y : Scheme.{u}} (sX : X ⟶ C.S)
  [LocallyOfFiniteType sX] (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (f : X ⟶ Y)
  [LocallyOfFiniteType f] (hf : f ≫ sY = sX) [IsLocallyNoetherian X] [IsLocallyNoetherian Y]

/-- **Stacks 0FDZ** at the decomposition into connected components: the map
`A^p(X ⟶ Y) ⟶ ∏_i A^p(X_i ⟶ Y_{a(i)})` restricting a bivariant class of degree `p` for
`f : X ⟶ Y` to the connected components of `X`. -/
def bivariantConnectedComponentRestriction (p : ℤ) (hgysO : G.IsNaturalUnderOpenImmersion) :
    BivariantClass C G sX sY f hf p →+
      ∀ i : ConnectedComponents X,
        BivariantClass C G ((X.connectedComponentOpens i).ι ≫ sX)
          ((Y.connectedComponentOpens (f.continuous.connectedComponentsMap i)).ι ≫ sY)
          (f.resConnectedComponent i) (f.resConnectedComponent_comp_ι_comp hf i) p :=
  bivariantPieceRestrictionHom C G sX sY f hf p X.connectedComponentOpens
    Y.connectedComponentOpens f.continuous.connectedComponentsMap
    f.connectedComponentOpens_le_preimage hgysO

/-- **Stacks 0FDZ** at the decomposition into connected components:
`A^p(X ⟶ Y) = ∏_i A^p(X_i ⟶ Y_{a(i)})`, the connected components of a locally Noetherian scheme
being open and closed. -/
def bivariantConnectedComponentEquiv (p : ℤ) (hgysO : G.IsNaturalUnderOpenImmersion)
    (hgysR : G.IsNaturalUnderOpensRestriction) (hgysC : G.IsNaturalUnderPullbackComp) :
    BivariantClass C G sX sY f hf p ≃+
      ∀ i : ConnectedComponents X,
        BivariantClass C G ((X.connectedComponentOpens i).ι ≫ sX)
          ((Y.connectedComponentOpens (f.continuous.connectedComponentsMap i)).ι ≫ sY)
          (f.resConnectedComponent i) (f.resConnectedComponent_comp_ι_comp hf i) p :=
  bivariantPieceEquiv C G sX sY f hf X.connectedComponentOpens Y.connectedComponentOpens
    f.continuous.connectedComponentsMap f.connectedComponentOpens_le_preimage
    ⟨fun _ _ h ↦ X.disjoint_connectedComponentOpens h, X.iSup_connectedComponentOpens⟩ p
    hgysO hgysR hgysC

/-- **Stacks 0FDZ.** The identification at the connected components is restriction. -/
@[simp]
theorem bivariantConnectedComponentEquiv_apply (p : ℤ) (hgysO : G.IsNaturalUnderOpenImmersion)
    (hgysR : G.IsNaturalUnderOpensRestriction) (hgysC : G.IsNaturalUnderPullbackComp)
    (c : BivariantClass C G sX sY f hf p) (i : ConnectedComponents X) :
    bivariantConnectedComponentEquiv C G sX sY f hf p hgysO hgysR hgysC c i =
      bivariantConnectedComponentRestriction C G sX sY f hf p hgysO c i :=
  rfl

/-! ### The completed group as a group of almost-vanishing sequences -/

/-- **Stacks 0FE0.** The subgroup of `∏_{p} A^p(X ⟶ Y)` the tag describes: the tuples
`c = (c_0, c_1, c_2, …)` such that for every connected component `X_i` of `X` the image of `c_p`
in `A^p(X_i ⟶ Y_{a(i)})` vanishes for almost all `p`. No bound on the degree is required
uniformly in `i`, which is what makes this larger than the graded group `⊕_p A^p(X ⟶ Y)`.

Restricting a class to a connected component needs
`Stacks.Chow.GysinSystem.IsNaturalUnderOpenImmersion`, so for an arbitrary Gysin system that is a
hypothesis here; `Stacks.Chow.completedBivariantSubgroupOfInvertible` is the same subgroup at the
Gysin system of the first Chern class rule, where it is a theorem. -/
def completedBivariantSubgroup (hgysO : G.IsNaturalUnderOpenImmersion) :
    AddSubgroup (∀ p : ℤ, BivariantClass C G sX sY f hf p) where
  carrier := {c | ∀ i : ConnectedComponents X,
    {p : ℤ | bivariantConnectedComponentRestriction C G sX sY f hf p hgysO (c p) i ≠ 0}.Finite}
  zero_mem' i := by
    simp only [Pi.zero_apply, map_zero, ne_eq, not_true_eq_false, Set.ofPred_false]
    exact Set.finite_empty
  add_mem' {c} {d} hc hd i := ((hc i).union (hd i)).subset fun p hp ↦ by
    by_contra hcon
    simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, ne_eq, not_not] at hcon
    exact hp (by simp [Pi.add_apply, map_add, hcon.1, hcon.2])
  neg_mem' {c} hc i := (hc i).subset fun p hp ↦ by
    simpa only [Set.mem_ofPred_eq, Pi.neg_apply, map_neg, ne_eq, neg_eq_zero] using hp

/-- **Stacks 0FE0.** Membership in the subgroup is the almost-vanishing condition, component by
component. -/
@[simp]
theorem mem_completedBivariantSubgroup (hgysO : G.IsNaturalUnderOpenImmersion)
    (c : ∀ p : ℤ, BivariantClass C G sX sY f hf p) :
    c ∈ completedBivariantSubgroup C G sX sY f hf hgysO ↔
      ∀ i : ConnectedComponents X,
        {p : ℤ |
          bivariantConnectedComponentRestriction C G sX sY f hf p hgysO (c p) i ≠ 0}.Finite :=
  Iff.rfl

variable (hgysO : G.IsNaturalUnderOpenImmersion) (hgysR : G.IsNaturalUnderOpensRestriction)
  (hgysC : G.IsNaturalUnderPullbackComp)

/-- The map `A^*(X ⟶ Y)^∧ ⟶ ∏_p A^p(X ⟶ Y)` of Stacks 0FE0: the degree `p` term of the tuple
attached to a family `(c_i)` of graded classes on the connected components is the class of degree
`p` whose restriction to `X_i` is the degree `p` part of `c_i`, which exists and is unique by
Stacks 0FDZ. -/
def completedBivariantSequence :
    completedBivariantGroup C G sX sY f hf →+ ∀ p : ℤ, BivariantClass C G sX sY f hf p where
  toFun c p :=
    (bivariantConnectedComponentEquiv C G sX sY f hf p hgysO hgysR hgysC).symm fun i ↦ c i p
  map_zero' := funext fun p ↦ by
    simp only [Pi.zero_apply, DirectSum.zero_apply]
    exact map_zero _
  map_add' c d := funext fun p ↦ by
    simp only [Pi.add_apply, DirectSum.add_apply]
    rw [← map_add]
    congr 1

/-- The degree `p` term of the tuple attached to an element of the completed group. -/
@[simp]
theorem completedBivariantSequence_apply (c : completedBivariantGroup C G sX sY f hf) (p : ℤ) :
    completedBivariantSequence C G sX sY f hf hgysO hgysR hgysC c p =
      (bivariantConnectedComponentEquiv C G sX sY f hf p hgysO hgysR hgysC).symm
        fun i ↦ c i p :=
  rfl

/-- The restriction to `X_i` of the degree `p` term of the tuple attached to `c` is the degree `p`
part of `c_i`: this is what it means for the tuple to realize `c`. -/
theorem restriction_completedBivariantSequence (c : completedBivariantGroup C G sX sY f hf)
    (p : ℤ) (i : ConnectedComponents X) :
    bivariantConnectedComponentRestriction C G sX sY f hf p hgysO
        (completedBivariantSequence C G sX sY f hf hgysO hgysR hgysC c p) i = c i p :=
  congrFun ((bivariantConnectedComponentEquiv C G sX sY f hf p hgysO hgysR
    hgysC).apply_symm_apply fun i ↦ c i p) i

/-- The completed group injects into `∏_p A^p(X ⟶ Y)`. -/
theorem completedBivariantSequence_injective :
    Function.Injective (completedBivariantSequence C G sX sY f hf hgysO hgysR hgysC) := by
  intro c d h
  funext i
  refine DirectSum.ext fun p ↦ ?_
  rw [← restriction_completedBivariantSequence C G sX sY f hf hgysO hgysR hgysC c p i,
    ← restriction_completedBivariantSequence C G sX sY f hf hgysO hgysR hgysC d p i, h]

/-- The tuple attached to an element of the completed group is almost vanishing on every
connected component: the degree support of its `i`-th factor is finite. -/
theorem completedBivariantSequence_mem (c : completedBivariantGroup C G sX sY f hf) :
    completedBivariantSequence C G sX sY f hf hgysO hgysR hgysC c ∈
      completedBivariantSubgroup C G sX sY f hf hgysO :=
  fun i ↦ (DFinsupp.finite_support (c i)).subset fun p hp ↦ by
    rwa [Set.mem_ofPred_eq,
      restriction_completedBivariantSequence C G sX sY f hf hgysO hgysR hgysC c p i] at hp

/-- Every almost-vanishing tuple comes from the completed group: its restrictions to a connected
component form a family of finite degree support, hence an element of `A^*(X_i ⟶ Y_{a(i)})`. -/
theorem exists_completedBivariantSequence_eq
    (c : ∀ p : ℤ, BivariantClass C G sX sY f hf p)
    (hc : c ∈ completedBivariantSubgroup C G sX sY f hf hgysO) :
    ∃ b, completedBivariantSequence C G sX sY f hf hgysO hgysR hgysC b = c := by
  refine ⟨(fun i ↦ directSumOfFinite
      (fun p ↦ bivariantConnectedComponentRestriction C G sX sY f hf p hgysO (c p) i) (hc i) :
    completedBivariantGroup C G sX sY f hf), funext fun p ↦ ?_⟩
  rw [completedBivariantSequence_apply]
  refine (AddEquiv.symm_apply_eq _).2 (funext fun i ↦ ?_).symm
  exact (directSumOfFinite_apply
    (fun p ↦ bivariantConnectedComponentRestriction C G sX sY f hf p hgysO (c p) i)
    (hc i) p).symm

/-- **Stacks 0FE0.** The image of `A^*(X ⟶ Y)^∧` in `∏_p A^p(X ⟶ Y)` is exactly the subgroup of
tuples that vanish in almost all degrees on each connected component.

This is the statement for an arbitrary Gysin system, carrying the three Gysin compatibilities of
Stacks 0FDZ; `Stacks.Chow.range_completedBivariantSequenceOfInvertible` is the same equality at
the Gysin system of the first Chern class rule, where all three are theorems. -/
theorem range_completedBivariantSequence :
    (completedBivariantSequence C G sX sY f hf hgysO hgysR hgysC).range =
      completedBivariantSubgroup C G sX sY f hf hgysO := by
  ext c
  exact ⟨fun ⟨b, hb⟩ ↦ hb ▸ completedBivariantSequence_mem C G sX sY f hf hgysO hgysR hgysC b,
    exists_completedBivariantSequence_eq C G sX sY f hf hgysO hgysR hgysC c⟩

/-- **Stacks 0FE0.** The completed bivariant group `A^*(X ⟶ Y)^∧` *is* the subgroup
`A^*(X ⟶ Y)^∧ ⊆ ∏_p A^p(X ⟶ Y)` of tuples `c = (c_0, c_1, c_2, …)` whose image in
`A^p(X_i ⟶ Y_{a(i)})` vanishes for almost all `p`, for every connected component `X_i`.

This is the identification for an arbitrary Gysin system, carrying the three Gysin
compatibilities of Stacks 0FDZ; `Stacks.Chow.completedBivariantGroupEquivOfInvertible` is the same
identification at the Gysin system of the first Chern class rule, where all three are
theorems. -/
def completedBivariantGroupEquiv :
    completedBivariantGroup C G sX sY f hf ≃+
      completedBivariantSubgroup C G sX sY f hf hgysO :=
  AddEquiv.ofBijective
    ((completedBivariantSequence C G sX sY f hf hgysO hgysR hgysC).codRestrict
      (completedBivariantSubgroup C G sX sY f hf hgysO)
      (completedBivariantSequence_mem C G sX sY f hf hgysO hgysR hgysC))
    ⟨fun _ _ h ↦ completedBivariantSequence_injective C G sX sY f hf hgysO hgysR hgysC
        (congrArg Subtype.val h),
      fun x ↦ (exists_completedBivariantSequence_eq C G sX sY f hf hgysO hgysR hgysC
        x.1 x.2).imp fun _ hb ↦ Subtype.ext hb⟩

/-- **Stacks 0FE0.** The identification is the map taking a family of graded classes on the
connected components to the tuple of its degreewise assemblies. -/
@[simp]
theorem completedBivariantGroupEquiv_apply (c : completedBivariantGroup C G sX sY f hf) :
    (completedBivariantGroupEquiv C G sX sY f hf hgysO hgysR hgysC c : ∀ _ : ℤ, _) =
      completedBivariantSequence C G sX sY f hf hgysO hgysR hgysC c :=
  rfl

end Components

/-! ### The identification with nothing assumed -/

section Invertible

variable (C : ChowSituation.{u}) {X Y : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (f : X ⟶ Y) [LocallyOfFiniteType f]
  (hf : f ≫ sY = sX) [IsLocallyNoetherian X] [IsLocallyNoetherian Y]

/-- **Stacks 0FE0.** The subgroup of `∏_p A^p(X ⟶ Y)` the tag describes — the tuples
`c = (c_0, c_1, c_2, …)` such that for every connected component `X_i` of `X` the image of `c_p`
in `A^p(X_i ⟶ Y_{a(i)})` vanishes for almost all `p` — at the Gysin system of the first Chern
class rule of an invertible module.

This is `Stacks.Chow.completedBivariantSubgroup` with the Gysin compatibility it carries
discharged, by `Stacks.Chow.gysinSystemOfInvertible_isNaturalUnderOpenImmersion`. Nothing remains
assumed: the Gysin system itself carries no hypothesis either. -/
@[stacks 0FE0 "the almost-vanishing tuples inside the product of the bivariant groups, at the \
Gysin system of the first Chern class rule, with the Gysin compatibility discharged"]
abbrev completedBivariantSubgroupOfInvertible :
    AddSubgroup (∀ p : ℤ, BivariantClass C (gysinSystemOfInvertible C) sX sY f hf p) :=
  completedBivariantSubgroup C (gysinSystemOfInvertible C) sX sY f hf
    (gysinSystemOfInvertible_isNaturalUnderOpenImmersion C)

/-- The map `A^*(X ⟶ Y)^∧ ⟶ ∏_p A^p(X ⟶ Y)` of Stacks 0FE0 at the Gysin system of the first Chern
class rule: `Stacks.Chow.completedBivariantSequence` with the three Gysin compatibilities of
Stacks 0FDZ discharged. -/
def completedBivariantSequenceOfInvertible :
    completedBivariantGroup C (gysinSystemOfInvertible C) sX sY f hf →+
      ∀ p : ℤ, BivariantClass C (gysinSystemOfInvertible C) sX sY f hf p :=
  completedBivariantSequence C (gysinSystemOfInvertible C) sX sY f hf
    (gysinSystemOfInvertible_isNaturalUnderOpenImmersion C)
    (gysinSystemOfInvertible_isNaturalUnderOpensRestriction C)
    (gysinSystemOfInvertible_isNaturalUnderPullbackComp C)

/-- **Stacks 0FE0.** The image of `A^*(X ⟶ Y)^∧` in `∏_p A^p(X ⟶ Y)` is exactly the subgroup of
tuples that vanish in almost all degrees on each connected component, at the Gysin system of the
first Chern class rule of an invertible module.

This is `Stacks.Chow.range_completedBivariantSequence` with the three Gysin compatibilities of
Stacks 0FDZ discharged, by `Stacks.Chow.gysinSystemOfInvertible_isNaturalUnderOpenImmersion`,
`Stacks.Chow.gysinSystemOfInvertible_isNaturalUnderOpensRestriction` and
`Stacks.Chow.gysinSystemOfInvertible_isNaturalUnderPullbackComp`. Nothing remains assumed: the
Gysin system itself carries no hypothesis either. -/
@[stacks 0FE0 "the image of the completed group is the almost-vanishing tuples, at the Gysin \
system of the first Chern class rule, with all three Gysin compatibilities discharged"]
theorem range_completedBivariantSequenceOfInvertible :
    (completedBivariantSequenceOfInvertible C sX sY f hf).range =
      completedBivariantSubgroupOfInvertible C sX sY f hf :=
  range_completedBivariantSequence C (gysinSystemOfInvertible C) sX sY f hf
    (gysinSystemOfInvertible_isNaturalUnderOpenImmersion C)
    (gysinSystemOfInvertible_isNaturalUnderOpensRestriction C)
    (gysinSystemOfInvertible_isNaturalUnderPullbackComp C)

/-- **Stacks 0FE0.** The completed bivariant group is the group of almost-vanishing tuples in
`∏_p A^p(X ⟶ Y)`, at the Gysin system of the first Chern class rule of an invertible module.

This is `Stacks.Chow.completedBivariantGroupEquiv` with the three Gysin compatibilities of Stacks
0FDZ discharged, by `Stacks.Chow.gysinSystemOfInvertible_isNaturalUnderOpenImmersion`,
`Stacks.Chow.gysinSystemOfInvertible_isNaturalUnderOpensRestriction` and
`Stacks.Chow.gysinSystemOfInvertible_isNaturalUnderPullbackComp`. Nothing remains assumed: the
Gysin system itself carries no hypothesis either. -/
@[stacks 0FE0 "the completed group is the group of almost-vanishing tuples, at the Gysin system \
of the first Chern class rule, with all three Gysin compatibilities discharged"]
def completedBivariantGroupEquivOfInvertible :
    completedBivariantGroup C (gysinSystemOfInvertible C) sX sY f hf ≃+
      completedBivariantSubgroup C (gysinSystemOfInvertible C) sX sY f hf
        (gysinSystemOfInvertible_isNaturalUnderOpenImmersion C) :=
  completedBivariantGroupEquiv C (gysinSystemOfInvertible C) sX sY f hf
    (gysinSystemOfInvertible_isNaturalUnderOpenImmersion C)
    (gysinSystemOfInvertible_isNaturalUnderOpensRestriction C)
    (gysinSystemOfInvertible_isNaturalUnderPullbackComp C)

end Invertible

/-! ### Composition on the completions -/

section Composition

variable (C : ChowSituation.{u}) (G : GysinSystem C) {X Y Z : Scheme.{u}} (sX : X ⟶ C.S)
  [LocallyOfFiniteType sX] (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (sZ : Z ⟶ C.S)
  [LocallyOfFiniteType sZ] (f : X ⟶ Y) [LocallyOfFiniteType f] (g : Y ⟶ Z)
  [LocallyOfFiniteType g] (hf : f ≫ sY = sX) (hg : g ≫ sZ = sY)
  [IsLocallyNoetherian X] [IsLocallyNoetherian Y] [IsLocallyNoetherian Z]
  (hgys : G.IsNaturalUnderBaseChangeIso) (hgysc : G.IsNaturalUnderPullbackCompPushforward)

/-- The group of bivariant classes of degree `n` for the composite `X_i ⟶ Y_{a(i)} ⟶ Z_{b(a(i))}`
of the restrictions is the `i`-th factor of the completed group of `f ≫ g` in degree `n`: the two
target components agree by `AlgebraicGeometry.Scheme.Hom.connectedComponentsMap_comp` and the two
morphisms then agree by `AlgebraicGeometry.Scheme.Hom.heq_resConnectedComponent_comp`. -/
def completedBivariantCompositeTransport (i : ConnectedComponents X) (n : ℤ) :
    BivariantClass C G ((X.connectedComponentOpens i).ι ≫ sX)
        ((Z.connectedComponentOpens (g.continuous.connectedComponentsMap
          (f.continuous.connectedComponentsMap i))).ι ≫ sZ)
        (f.resConnectedComponent i ≫
          g.resConnectedComponent (f.continuous.connectedComponentsMap i))
        (comp_comp_structureMorphism_eq (f.resConnectedComponent_comp_ι_comp hf i)
          (g.resConnectedComponent_comp_ι_comp hg
            (f.continuous.connectedComponentsMap i))) n ≃+
      BivariantClass C G ((X.connectedComponentOpens i).ι ≫ sX)
        ((Z.connectedComponentOpens ((f ≫ g).continuous.connectedComponentsMap i)).ι ≫ sZ)
        ((f ≫ g).resConnectedComponent i)
        ((f ≫ g).resConnectedComponent_comp_ι_comp
          (comp_comp_structureMorphism_eq hf hg) i) n :=
  bivariantClassComponentCongr C G ((X.connectedComponentOpens i).ι ≫ sX) sZ
    (Scheme.Hom.connectedComponentsMap_comp f g i).symm _ _
    (Scheme.Hom.heq_resConnectedComponent_comp f g i).symm _ _ n

/-- **Stacks 0FE0.** The composition
`A^*(X ⟶ Y)^∧ × A^*(Y ⟶ Z)^∧ ⟶ A^*(X ⟶ Z)^∧` extending the composition of Stacks 0B75 to the
completions: on the connected component `X_i` of `X` it is the convolution, degree by degree, of
the composition of bivariant classes for the restrictions `X_i ⟶ Y_{a(i)}` and
`Y_{a(i)} ⟶ Z_{b(a(i))}`.

It carries the two Gysin compatibilities that Stacks 0B75 carries for an arbitrary Gysin system,
and nothing else; `Stacks.Chow.completedBivariantCompositeOfInvertible` is the same composition at
the Gysin system of the first Chern class rule, where both are discharged. See the implementation
notes of `StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.Completion`. -/
def completedBivariantComposite (c : completedBivariantGroup C G sX sY f hf)
    (d : completedBivariantGroup C G sY sZ g hg) :
    completedBivariantGroup C G sX sZ (f ≫ g) (comp_comp_structureMorphism_eq hf hg) :=
  fun i ↦ DFinsupp.mapRange.addEquiv
    (completedBivariantCompositeTransport C G sX sY sZ f g hf hg i)
    (directSumBilinear
      (fun p q ↦ bivariantCompositeBilinear C G _ _ _ _ _ _ _ p q hgys hgysc)
      (c i) (d (f.continuous.connectedComponentsMap i)))

/-- **Stacks 0FE0.** The composition on the completions, on a connected component. -/
@[simp]
theorem completedBivariantComposite_apply (c : completedBivariantGroup C G sX sY f hf)
    (d : completedBivariantGroup C G sY sZ g hg) (i : ConnectedComponents X) :
    completedBivariantComposite C G sX sY sZ f g hf hg hgys hgysc c d i =
      DFinsupp.mapRange.addEquiv
        (completedBivariantCompositeTransport C G sX sY sZ f g hf hg i)
        (directSumBilinear
          (fun p q ↦ bivariantCompositeBilinear C G _ _ _ _ _ _ _ p q hgys hgysc)
          (c i) (d (f.continuous.connectedComponentsMap i))) :=
  rfl

/-- **Stacks 0FE0.** The composition on the completions extends the composition of Stacks 0B75:
if `c` is concentrated in degree `p` on the component `X_i` and `d` is concentrated in degree `q`
on the component `Y_{a(i)}`, then the composite is concentrated in degree `p + q` on `X_i` and is
there the composite bivariant class of Stacks 0B75.

It carries the two Gysin compatibilities that Stacks 0B75 carries for an arbitrary Gysin system;
`Stacks.Chow.completedBivariantCompositeOfInvertible_of_of` is the same statement at the Gysin
system of the first Chern class rule, where both are discharged. -/
theorem completedBivariantComposite_of_of (c : completedBivariantGroup C G sX sY f hf)
    (d : completedBivariantGroup C G sY sZ g hg) (i : ConnectedComponents X) (p q : ℤ)
    (hc : c i = DirectSum.of _ p (c i p))
    (hd : d (f.continuous.connectedComponentsMap i) =
      DirectSum.of _ q (d (f.continuous.connectedComponentsMap i) q)) :
    completedBivariantComposite C G sX sY sZ f g hf hg hgys hgysc c d i =
      DirectSum.of _ (p + q)
        (completedBivariantCompositeTransport C G sX sY sZ f g hf hg i (p + q)
          (bivariantComposite C G _ _ _ _ _ _ _ p q (c i p)
            (d (f.continuous.connectedComponentsMap i) q) hgys hgysc)) := by
  rw [completedBivariantComposite_apply]
  conv_lhs => rw [hc, hd]
  rw [directSumBilinear_of_of, mapRange_addEquiv_of, bivariantCompositeBilinear_apply]

end Composition

/-! ### Composition on the completions with nothing assumed -/

section CompositionInvertible

variable (C : ChowSituation.{u}) {X Y Z : Scheme.{u}} (sX : X ⟶ C.S)
  [LocallyOfFiniteType sX] (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (sZ : Z ⟶ C.S)
  [LocallyOfFiniteType sZ] (f : X ⟶ Y) [LocallyOfFiniteType f] (g : Y ⟶ Z)
  [LocallyOfFiniteType g] (hf : f ≫ sY = sX) (hg : g ≫ sZ = sY)
  [IsLocallyNoetherian X] [IsLocallyNoetherian Y] [IsLocallyNoetherian Z]

/-- **Stacks 0FE0.** The composition
`A^*(X ⟶ Y)^∧ × A^*(Y ⟶ Z)^∧ ⟶ A^*(X ⟶ Z)^∧` extending the composition of Stacks 0B75 to the
completions, at the Gysin system of the first Chern class rule of an invertible module.

This is `Stacks.Chow.completedBivariantComposite` with both Gysin compatibilities of Stacks 0B75
discharged, by `Stacks.Chow.gysinSystemOfInvertible_isNaturalUnderBaseChangeIso` and
`Stacks.Chow.gysinSystemOfInvertible_isNaturalUnderPullbackCompPushforward`. Nothing remains
assumed: the Gysin system itself carries no hypothesis either. -/
@[stacks 0FE0 "the composition extended to the completed bivariant groups, at the Gysin system \
of the first Chern class rule, with both Gysin compatibilities discharged"]
def completedBivariantCompositeOfInvertible
    (c : completedBivariantGroup C (gysinSystemOfInvertible C) sX sY f hf)
    (d : completedBivariantGroup C (gysinSystemOfInvertible C) sY sZ g hg) :
    completedBivariantGroup C (gysinSystemOfInvertible C) sX sZ (f ≫ g)
      (comp_comp_structureMorphism_eq hf hg) :=
  completedBivariantComposite C (gysinSystemOfInvertible C) sX sY sZ f g hf hg
    (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C)
    (gysinSystemOfInvertible_isNaturalUnderPullbackCompPushforward C) c d

/-- **Stacks 0FE0.** The composition on the completions extends the composition of Stacks 0B75,
with nothing assumed: at the Gysin system of the first Chern class rule, if `c` is concentrated in
degree `p` on the component `X_i` and `d` is concentrated in degree `q` on the component
`Y_{a(i)}`, then the composite is concentrated in degree `p + q` on `X_i` and is there the
composite bivariant class `Stacks.Chow.bivariantCompositeOfInvertible` of Stacks 0B75. -/
@[stacks 0FE0 "the composition on the completions extends the composition of homogeneous \
classes, at the Gysin system of the first Chern class rule, with both Gysin compatibilities \
discharged"]
theorem completedBivariantCompositeOfInvertible_of_of
    (c : completedBivariantGroup C (gysinSystemOfInvertible C) sX sY f hf)
    (d : completedBivariantGroup C (gysinSystemOfInvertible C) sY sZ g hg)
    (i : ConnectedComponents X) (p q : ℤ) (hc : c i = DirectSum.of _ p (c i p))
    (hd : d (f.continuous.connectedComponentsMap i) =
      DirectSum.of _ q (d (f.continuous.connectedComponentsMap i) q)) :
    completedBivariantCompositeOfInvertible C sX sY sZ f g hf hg c d i =
      DirectSum.of _ (p + q)
        (completedBivariantCompositeTransport C (gysinSystemOfInvertible C) sX sY sZ f g hf hg
          i (p + q)
          (bivariantCompositeOfInvertible C _ _ _ _ _ _ _ p q (c i p)
            (d (f.continuous.connectedComponentsMap i) q))) :=
  completedBivariantComposite_of_of C (gysinSystemOfInvertible C) sX sY sZ f g hf hg
    (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C)
    (gysinSystemOfInvertible_isNaturalUnderPullbackCompPushforward C) c d i p q hc hd

end CompositionInvertible

/-! ### The completed bivariant cohomology ring -/

/-- **Stacks 0FE0.** The *completed bivariant cohomology ring* `A^*(X)^∧ = A^*(X ⟶ X)^∧` of a
scheme `X` locally of finite type over the base: the completed bivariant group of the identity
of `X`. Its multiplication is `Stacks.Chow.completedBivariantComposite` at `f = g = 𝟙 X`, and
`Stacks.Chow.completedBivariantGroupEquiv` reads it as the group of tuples in `∏_p A^p(X)` that
vanish in almost all degrees on each connected component of `X`. -/
@[stacks 0FE0 "the completed bivariant cohomology ring A^*(X)^∧ of a scheme"]
abbrev completedChowCohomology (C : ChowSituation.{u}) (G : GysinSystem C) {X : Scheme.{u}}
    (sX : X ⟶ C.S) [LocallyOfFiniteType sX] : Type (u + 1) :=
  completedBivariantGroup C G sX sX (𝟙 X) (Category.id_comp sX)

end Stacks.Chow

end
