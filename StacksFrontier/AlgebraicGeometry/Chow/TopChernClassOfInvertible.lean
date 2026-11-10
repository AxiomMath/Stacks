module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Chow.TopChernClass
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.Completion
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.EnvelopeDescent
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassDerived.ArbitraryRankChern

/-!
# The top Chern class of a finite locally free module, from its Chern classes

Let `(S, δ)` be the base situation of chapter 42, let `X` be locally of finite type over `S` and
let `E` be a finite locally free `𝒪_X`-module. The rank of `E` is locally constant, so `X` is the
disjoint union `X = ∐_r X_r` of the open and closed loci on which the rank is `r`, and the *top*
Chern class of `E` is the class whose component on `X_r` is the `r`-th Chern class
`c_r(E|_{X_r})` of Stacks 0ESW:

  `c_top(E) = Σ_r c_r(E|_{X_r})`.

The Chern classes are those of Stacks 0ESW, `Stacks.Chow.totalChernOfFiniteLocallyFree`, at the
Gysin system `Stacks.Chow.gysinSystemOfInvertible` of the first Chern class of an invertible
module, and the components are glued along the rank decomposition by Stacks 0FDZ
(`Stacks.Chow.TotalChowClass.glue`).

The class is an element of the product `∏_{p ≥ 0} A^p(X)`, whose degree-`p` component is the
class equal to `c_p(E|_{X_p})` on `X_p` and to zero on every other rank locus; and it is an
element of the completed bivariant group `A^*(X)^∧` of Stacks 0FE0, the product over the connected
components of `X` of the graded bivariant groups of the components. The rank is constant on a
connected component, so the top Chern class is homogeneous there, of degree that rank. When only
finitely many of the loci `X_r` are nonempty, only finitely many degrees occur in total and the
class lies in the ordinary graded group `A^*(X) = ⊕_p A^p(X)`, where it is the finite sum
displayed above.

A rank locus `X_r` is the union of the connected components of `X` on which `E` has rank `r`
(`AlgebraicGeometry.Scheme.Modules.rankStratum_eq_iSup_connectedComponentOpens`), and Stacks 0FDZ
identifies `A^*(X_r)` with the product of the `A^*(X_i)` over those components; the rank loci
`Stacks.Chow.rankLocus` and the strata `AlgebraicGeometry.Scheme.Modules.rankStratum` are the same
open subschemes (`Stacks.Chow.rankStratum_eq_rankLocus`).

## Main definitions

* `Stacks.Chow.topChernTotalClass`: the top Chern class in `∏_{p ≥ 0} A^p(X)`.
* `Stacks.Chow.topChernClassOfInvertible`: the top Chern class, in the completed bivariant group.
* `Stacks.Chow.topChernClassDegreeOfInvertible`: its degree-`p` part, as a bivariant class on `X`.
* `Stacks.Chow.topChernCap`: the cap product `c_top(E) ∩ -` in degree `e`, on `CH_k(X)`.
* `Stacks.Chow.topChernClassFiniteOfInvertible`: the top Chern class as an ordinary
  nonhomogeneous bivariant class, when only finitely many rank loci are nonempty.

## Main results

* `Stacks.Chow.idRule_topChernTotalClass_of_mem` and
  `Stacks.Chow.idRule_topChernTotalClass_self`: on a scheme over the locus where `E` has rank
  `s`, the degree-`p` component of `c_top(E)` operates as `c_s(E)` if `p = s` and as zero
  otherwise; in degree `s` it operates by the cap product with `c_s` of the pulled back module.
* `Stacks.Chow.topChernClassOfInvertible_rankStratum` and
  `Stacks.Chow.topChernClassOfInvertible_of_ne_rank`: on a connected component on which the rank
  is `r`, the completed top Chern class is the restriction of `c_r(E)` in degree `r`, and it
  vanishes in every other degree.
* `Stacks.Chow.topChernClassDegreeOfInvertible_natCast`: the degree-`p` part of the completed
  class is the degree-`p` component of the class in `∏_{p ≥ 0} A^p(X)`.
* `Stacks.Chow.finite_degrees_topChernClassOfInvertible`: if only finitely many rank loci are
  nonempty, only finitely many degrees occur.
* `Stacks.Chow.topChernClassFiniteOfInvertible_component`,
  `Stacks.Chow.topChernClassFiniteOfInvertible_rankStratum` and
  `Stacks.Chow.topChernClassFiniteOfInvertible_of_ne_rank`: the finite sum has the completed top
  Chern class as its image, and the componentwise formula for it.

## References

* [Stacks Project, Tag 0FA4](https://stacks.math.columbia.edu/tag/0FA4)
* [Stacks Project, Tag 0ESW](https://stacks.math.columbia.edu/tag/0ESW)
* [Stacks Project, Tag 0FDZ](https://stacks.math.columbia.edu/tag/0FDZ)
* [Stacks Project, Tag 0FE0](https://stacks.math.columbia.edu/tag/0FE0)
* [Stacks Project, Tag 0B7H](https://stacks.math.columbia.edu/tag/0B7H)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Stacks.Chow

/-- The strata of the rank of a finite locally free module used for the connected components and
the rank loci of the rank decomposition of Stacks 0ESW are the same open subschemes. -/
theorem rankStratum_eq_rankLocus {X : Scheme.{u}} (E : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E] (r : ℕ) :
    Scheme.Modules.rankStratum E r = rankLocus E r :=
  rfl

/-! ### The restriction of a class to a connected component -/

section ComponentRestriction

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  [IsLocallyNoetherian X]

/-- **The restriction of a Chow cohomology class to a connected component `X_i` only depends on
its operation on the schemes over `X_i`**: two classes of `A^p(X)` operating alike on every
`T ⟶ X_i ⟶ X` have the same restriction to `X_i` (Stacks 0FDZ). -/
theorem bivariantConnectedComponentRestriction_eq_of_idRule_eq {p : ℤ}
    (c d : chowCohomologyComponent C (gysinSystemOfInvertible C) sX p)
    (i : _root_.ConnectedComponents X)
    (h : ∀ {T : Scheme.{u}} (t : T ⟶ (X.connectedComponentOpens
        ((Scheme.Hom.continuous (𝟙 X)).connectedComponentsMap i) : Scheme.{u}))
      [LocallyOfFiniteType t] (k : ℤ) (α : chowGroup C ((t ≫ (X.connectedComponentOpens
        ((Scheme.Hom.continuous (𝟙 X)).connectedComponentsMap i)).ι) ≫ sX) k),
      c.idRule C sX (gysinSystemOfInvertible C) _ k α =
        d.idRule C sX (gysinSystemOfInvertible C) _ k α) :
    bivariantConnectedComponentRestriction C (gysinSystemOfInvertible C) sX sX (𝟙 X)
        (Category.id_comp sX) p (gysinSystemOfInvertible_isNaturalUnderOpenImmersion C) c i =
      bivariantConnectedComponentRestriction C (gysinSystemOfInvertible C) sX sX (𝟙 X)
        (Category.id_comp sX) p (gysinSystemOfInvertible_isNaturalUnderOpenImmersion C) d i := by
  refine BivariantClass.ext C _ _ _ _ _ p fun {T} g _ k β ↦ ?_
  change bivariantPieceRestrictionCap C _ sX sX (𝟙 X) (Category.id_comp sX) p _ _ _ _ i c g k β =
    bivariantPieceRestrictionCap C _ sX sX (𝟙 X) (Category.id_comp sX) p _ _ _ _ i d g k β
  rw [bivariantPieceRestrictionCap_apply, bivariantPieceRestrictionCap_apply]
  refine congrArg _ ?_
  have hc := h g k (chowGroupCongr C (Category.assoc g _ sX).symm k β)
  rw [BivariantClass.idRule_apply, BivariantClass.idRule_apply] at hc
  exact chowPushforwardOfIso_injective C _ _ _ _ _ hc

end ComponentRestriction

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  (E : X.Modules) [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E]

/-! ### The top Chern class as a total class -/

/-- The top Chern class `c_top(E) = Σ_r c_r(E|_{X_r})` of a finite locally free module `E` on `X`,
as an element of `∏_{p ≥ 0} A^p(X)`: its degree-`p` component is the class equal, on the locus
`X_p` where `E` has rank `p`, to the `p`-th Chern class of Stacks 0ESW, and to zero on every other
rank locus. It is assembled along the rank decomposition by Stacks 0FDZ. -/
@[stacks 0FA4 "top Chern class in the product of the Chow cohomology groups"]
def topChernTotalClass : TotalChowClass C sX :=
  TotalChowClass.glue (isClopenDecomposition_rankLociFamily E) fun r p ↦
    if p = r.down then
      TotalChowClass.res (rankLociFamily E r).ι rfl (totalChernOfFiniteLocallyFree C sX E) p
    else 0

/-- On the locus `X_r` where `E` has rank `r`, the top Chern class is `c_r(E|_{X_r})` in degree
`r` and zero in every other degree. -/
theorem res_topChernTotalClass_rankLocus (r : ULift.{u} ℕ) (p : ℕ) :
    TotalChowClass.res (rankLociFamily E r).ι rfl (topChernTotalClass C sX E) p =
      if p = r.down then
        TotalChowClass.res (rankLociFamily E r).ι rfl (totalChernOfFiniteLocallyFree C sX E) p
      else 0 :=
  congrFun (TotalChowClass.res_glue (isClopenDecomposition_rankLociFamily E) _ r) p

/-- **The operation of the top Chern class over a rank locus.** On a scheme `m : T ⟶ X` lying
over the locus where `E` has rank `s`, the degree-`p` component of `c_top(E)` operates as the
Chern class `c_p(E)` of Stacks 0ESW if `p = s`, and as zero otherwise. -/
theorem idRule_topChernTotalClass_of_mem (s p : ℕ) {T : Scheme.{u}} (m : T ⟶ X)
    [LocallyOfFiniteType m] (hm : ∀ t : T, m.base t ∈ rankLocus E s) (k : ℤ)
    (α : chowGroup C (m ≫ sX) k) :
    (topChernTotalClass C sX E p).idRule C sX (gysinSystemOfInvertible C) m k α =
      if p = s then
        (totalChernOfFiniteLocallyFree C sX E p).idRule C sX (gysinSystemOfInvertible C) m k α
      else 0 := by
  have hrange : Set.range m.base ⊆ Set.range (rankLociFamily E ⟨s⟩).ι.base := by
    rw [Scheme.Opens.range_ι, Set.range_subset_iff]
    exact hm
  set h := IsOpenImmersion.lift (rankLociFamily E ⟨s⟩).ι m hrange
  have hfac : h ≫ (rankLociFamily E ⟨s⟩).ι = m := IsOpenImmersion.lift_fac _ _ _
  have : LocallyOfFiniteType (h ≫ (rankLociFamily E ⟨s⟩).ι) := hfac ▸ inferInstance
  have : LocallyOfFiniteType h := locallyOfFiniteType_of_comp h (rankLociFamily E ⟨s⟩).ι
  have hzero : ∀ {q q' : T ⟶ C.S} [LocallyOfFiniteType q] [LocallyOfFiniteType q'] (n : ℤ),
      q = q' → (0 : chowGroup C q n) ≍ (0 : chowGroup C q' n) := by
    rintro q q' _ _ n rfl
    rfl
  set α' := chowGroupCongr C (by rw [← hfac, Category.assoc]) k α with hα'
  have hαα' : α' ≍ α := chowGroupCongr_heq C _ k α
  have hres : ∀ c : TotalChowClass C sX,
      (TotalChowClass.res (rankLociFamily E ⟨s⟩).ι rfl c p).idRule C _
          (gysinSystemOfInvertible C) h k α' ≍
        (c p).idRule C sX (gysinSystemOfInvertible C) m k α := by
    intro c
    rw [TotalChowClass.res_rfl_apply]
    refine (BivariantClass.idRule_chowCohomologyRestriction_heq _ (c p) h k α'
      (chowGroupCongr C (Category.assoc h _ sX).symm k α')
      (chowGroupCongr_heq C _ k α').symm).trans ?_
    exact IdentityCapRule.heq_congr C sX _ hfac rfl
      ((chowGroupCongr_heq C _ k α').trans hαα')
  refine eq_of_heq ((hres (topChernTotalClass C sX E)).symm.trans ?_)
  rw [res_topChernTotalClass_rankLocus]
  by_cases hp : p = s
  · subst hp
    rw [ite_eq_left rfl, ite_eq_left rfl]
    exact hres _
  · rw [ite_eq_right hp, ite_eq_right hp, BivariantClass.idRule_zero]
    exact hzero _ (by rw [← hfac, Category.assoc])

/-- **The top Chern class in degree `s` over the locus of rank `s`** operates by the cap product
with the `s`-th Chern class, of Stacks 0B7H, of the pulled back module: on a scheme
`m : T ⟶ X` lying over the locus where `E` has rank `s`,
`c_top(E) ∩ α = c_s(m^*E) ∩ α`. -/
theorem idRule_topChernTotalClass_self (s : ℕ) {T : Scheme.{u}} (m : T ⟶ X)
    [LocallyOfFiniteType m] (hm : ∀ t : T, m.base t ∈ rankLocus E s)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Modules.pullback m).obj E) s] (k : ℤ) (α : chowGroup C (m ≫ sX) k) :
    (topChernTotalClass C sX E s).idRule C sX (gysinSystemOfInvertible C) m k α =
      GenuineChern.chernCap C s (m ≫ sX) ((Scheme.Modules.pullback m).obj E) k (Fin.last s)
        α := by
  rw [idRule_topChernTotalClass_of_mem C sX E s s m hm k α, ite_eq_left rfl,
    ← TotalChowClass.op_apply, op_totalChernOfFiniteLocallyFree_of_rank C sX E m s,
    GenuineChern.chernFamily, chernCapFamilyOnChow_of_le _ _ _ _ _ _ le_rfl]
  rfl

/-- On a scheme over the locus of rank `s`, the components of the top Chern class in degrees other
than `s` operate as zero. -/
theorem idRule_topChernTotalClass_of_ne (s p : ℕ) (hp : p ≠ s) {T : Scheme.{u}} (m : T ⟶ X)
    [LocallyOfFiniteType m] (hm : ∀ t : T, m.base t ∈ rankLocus E s) (k : ℤ)
    (α : chowGroup C (m ≫ sX) k) :
    (topChernTotalClass C sX E p).idRule C sX (gysinSystemOfInvertible C) m k α = 0 := by
  rw [idRule_topChernTotalClass_of_mem C sX E s p m hm k α, ite_eq_right hp]

/-- **The cap product with the top Chern class, in degree `e`**, on the Chow groups of `X`: the
operation `CH_k(X) ⟶ CH_{k-e}(X)` of the degree-`e` component of `c_top(E)`. It is the cap
product `c_top(E) ∩ -` of Stacks 0FA4 on the part of `CH_*(X)` lying over the locus where `E` has
rank `e`, and it is the operation of the degree-`e` part of the completed top Chern class
(`Stacks.Chow.topChernCap_eq`). -/
def topChernCap (k : ℤ) (e : ℕ) : chowGroup C sX k →+ chowGroup C sX (k - e) :=
  (chowGroupCongr C (Category.id_comp sX) (k - e)).toAddMonoidHom.comp
    (((topChernTotalClass C sX E e).idRule C sX (gysinSystemOfInvertible C) (𝟙 X) k).comp
      (chowGroupCongr C (Category.id_comp sX).symm k).toAddMonoidHom)

/-- The cap product with the top Chern class in degree `e` is the operation of the degree-`e`
component of the top Chern class on the identity test scheme. -/
theorem topChernCap_heq (k : ℤ) (e : ℕ) (α : chowGroup C sX k)
    (α' : chowGroup C (𝟙 X ≫ sX) k) (hα : α ≍ α') :
    topChernCap C sX E k e α ≍
      (topChernTotalClass C sX E e).idRule C sX (gysinSystemOfInvertible C) (𝟙 X) k α' := by
  have h : chowGroupCongr C (Category.id_comp sX).symm k α = α' :=
    eq_of_heq ((chowGroupCongr_heq C _ k α).trans hα)
  rw [topChernCap, AddMonoidHom.comp_apply, AddMonoidHom.comp_apply,
    AddEquiv.coe_toAddMonoidHom, AddEquiv.coe_toAddMonoidHom, h]
  exact chowGroupCongr_heq C (Category.id_comp sX) (k - e) _

/-! ### The top Chern class in the completed bivariant group -/

variable [IsLocallyNoetherian X]

/-- The connected component of `X` over which the restriction of the identity to a connected
component `X_i` lands lies in the locus of the rank of `E` on `X_i`. -/
theorem connectedComponentOpens_connectedComponentsMap_le_rankLocus
    (i : _root_.ConnectedComponents X) :
    X.connectedComponentOpens ((Scheme.Hom.continuous (𝟙 X)).connectedComponentsMap i) ≤
      rankLocus E (Scheme.Modules.rankOnConnectedComponent E i) := by
  obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe i
  exact Scheme.Modules.connectedComponentOpens_le_rankStratum E (ConnectedComponents.mk x)

/-- The degree-`p` component of the top Chern class restricted to a connected component `X_i`:
the restriction of `c_p(E)` if `E` has rank `p` on `X_i`, and zero otherwise. -/
theorem bivariantConnectedComponentRestriction_topChernTotalClass (p : ℕ)
    (i : _root_.ConnectedComponents X) :
    bivariantConnectedComponentRestriction C (gysinSystemOfInvertible C) sX sX (𝟙 X)
        (Category.id_comp sX) p (gysinSystemOfInvertible_isNaturalUnderOpenImmersion C)
        (topChernTotalClass C sX E p) i =
      if p = Scheme.Modules.rankOnConnectedComponent E i then
        bivariantConnectedComponentRestriction C (gysinSystemOfInvertible C) sX sX (𝟙 X)
          (Category.id_comp sX) p (gysinSystemOfInvertible_isNaturalUnderOpenImmersion C)
          (totalChernOfFiniteLocallyFree C sX E p) i
      else 0 := by
  have hmem : ∀ {T : Scheme.{u}} (t : T ⟶ (X.connectedComponentOpens
      ((Scheme.Hom.continuous (𝟙 X)).connectedComponentsMap i) : Scheme.{u})) (y : T),
      (t ≫ (X.connectedComponentOpens
        ((Scheme.Hom.continuous (𝟙 X)).connectedComponentsMap i)).ι).base y ∈
        rankLocus E (Scheme.Modules.rankOnConnectedComponent E i) := fun t y ↦
    connectedComponentOpens_connectedComponentsMap_le_rankLocus E i (t.base y).2
  refine (bivariantConnectedComponentRestriction_eq_of_idRule_eq C sX _
    (if p = Scheme.Modules.rankOnConnectedComponent E i then totalChernOfFiniteLocallyFree C sX E p
      else 0) i fun {T} t _ k α ↦ ?_).trans ?_
  · rw [idRule_topChernTotalClass_of_mem C sX E _ p _ (hmem t) k α]
    split_ifs
    · rfl
    · rw [BivariantClass.idRule_zero]
  · split_ifs
    · rfl
    · rw [map_zero]
      rfl

/-- The top Chern class `c_top(E) = Σ_r c_r(E|_{X_r})` of a finite locally free module `E` on `X`,
as an element of the completed bivariant group `A^*(X)^∧`: on a connected component `X_i` of `X`
the rank of `E` is a constant `r`, and there the class is the restriction to `X_i` of the
degree-`r` component of `c_top(E)` — that is, of the `r`-th Chern class of Stacks 0ESW, by
`Stacks.Chow.topChernClassOfInvertible_rankStratum` — placed in degree `r`. -/
@[stacks 0FA4 "completed top Chern class"]
def topChernClassOfInvertible :
    completedBivariantGroup C (gysinSystemOfInvertible C) sX sX (𝟙 X) (Category.id_comp sX) :=
  fun i ↦ DirectSum.of _ (Scheme.Modules.rankOnConnectedComponent E i : ℤ)
    (bivariantConnectedComponentRestriction C (gysinSystemOfInvertible C) sX sX (𝟙 X)
      (Category.id_comp sX) _ (gysinSystemOfInvertible_isNaturalUnderOpenImmersion C)
      (topChernTotalClass C sX E (Scheme.Modules.rankOnConnectedComponent E i)) i)

/-- On the locus where `E` has rank `r` the top Chern class is the `r`-th Chern class, in degree
`r`: a connected component `X_i` lies in the locus of the rank `r` of `E` on it, and the degree-`r`
part of `c_top(E)` there is the restriction to `X_i` of the Chern class `c_r(E)` of Stacks 0ESW,
that is `c_r(E|_{X_i})`. -/
@[stacks 0FA4 "rank-locus Chern component"]
theorem topChernClassOfInvertible_rankStratum (i : _root_.ConnectedComponents X) :
    X.connectedComponentOpens i ≤
        Scheme.Modules.rankStratum E (Scheme.Modules.rankOnConnectedComponent E i) ∧
      topChernClassOfInvertible C sX E i (Scheme.Modules.rankOnConnectedComponent E i : ℤ) =
        bivariantConnectedComponentRestriction C (gysinSystemOfInvertible C) sX sX (𝟙 X)
          (Category.id_comp sX) _ (gysinSystemOfInvertible_isNaturalUnderOpenImmersion C)
          (totalChernOfFiniteLocallyFree C sX E (Scheme.Modules.rankOnConnectedComponent E i))
          i := by
  refine ⟨Scheme.Modules.connectedComponentOpens_le_rankStratum E i, ?_⟩
  rw [topChernClassOfInvertible, DirectSum.of_eq_same,
    bivariantConnectedComponentRestriction_topChernTotalClass, ite_eq_left rfl]

/-- The top Chern class has no component in a degree other than the rank: on a connected component
on which `E` has rank `r`, the degree-`p` part of `c_top(E)` vanishes for every `p ≠ r`. -/
@[stacks 0FA4 "off-rank vanishing"]
theorem topChernClassOfInvertible_of_ne_rank (i : _root_.ConnectedComponents X) (p : ℤ)
    (h : p ≠ (Scheme.Modules.rankOnConnectedComponent E i : ℤ)) :
    topChernClassOfInvertible C sX E i p = 0 :=
  DirectSum.of_eq_of_ne (Scheme.Modules.rankOnConnectedComponent E i : ℤ) p _ h

/-- If only finitely many of the loci `X_r` are nonempty, then only finitely many degrees occur in
the top Chern class, so it lies in the ordinary graded group `A^*(X)` inside its completion. -/
@[stacks 0FA4 "finite-rank-locus case"]
theorem finite_degrees_topChernClassOfInvertible
    (hfin : {r : ℕ | (Scheme.Modules.rankStratum E r : Set X).Nonempty}.Finite) :
    {p : ℤ | ∃ i : _root_.ConnectedComponents X,
      topChernClassOfInvertible C sX E i p ≠ 0}.Finite := by
  refine (hfin.image (fun r : ℕ ↦ (r : ℤ))).subset ?_
  rintro p ⟨i, hp⟩
  refine ⟨Scheme.Modules.rankOnConnectedComponent E i,
    Scheme.Modules.nonempty_rankStratum_rankOnConnectedComponent E i, ?_⟩
  by_contra hne
  exact hp (topChernClassOfInvertible_of_ne_rank C sX E i p (Ne.symm hne))

/-! ### The degreewise parts of the top Chern class -/

/-- The degree-`p` part of the top Chern class, as a bivariant class of degree `p` on `X`: the
class whose restriction to each connected component of `X` is the degree-`p` part of the top Chern
class there (Stacks 0FDZ). -/
def topChernClassDegreeOfInvertible (p : ℤ) :
    BivariantClass C (gysinSystemOfInvertible C) sX sX (𝟙 X) (Category.id_comp sX) p :=
  completedBivariantSequenceOfInvertible C sX sX (𝟙 X) (Category.id_comp sX)
    (topChernClassOfInvertible C sX E) p

/-- The restriction of the degree-`p` part of the top Chern class to a connected component is the
degree-`p` part of the top Chern class there. -/
theorem bivariantConnectedComponentRestriction_topChernClassDegreeOfInvertible (p : ℤ)
    (i : _root_.ConnectedComponents X) :
    bivariantConnectedComponentRestriction C (gysinSystemOfInvertible C) sX sX (𝟙 X)
        (Category.id_comp sX) p (gysinSystemOfInvertible_isNaturalUnderOpenImmersion C)
        (topChernClassDegreeOfInvertible C sX E p) i =
      topChernClassOfInvertible C sX E i p :=
  restriction_completedBivariantSequence C _ sX sX (𝟙 X) (Category.id_comp sX) _ _ _
    (topChernClassOfInvertible C sX E) p i

/-- **The degree-`p` part of the completed top Chern class is the degree-`p` component of the top
Chern class in `∏_{p ≥ 0} A^p(X)`.** Both restrict, on every connected component, to the
restriction of `c_p(E)` if `E` has rank `p` there and to zero otherwise (Stacks 0FDZ). -/
theorem topChernClassDegreeOfInvertible_natCast (p : ℕ) :
    topChernClassDegreeOfInvertible C sX E p = topChernTotalClass C sX E p := by
  refine (bivariantConnectedComponentEquiv C _ sX sX (𝟙 X) (Category.id_comp sX) p
    (gysinSystemOfInvertible_isNaturalUnderOpenImmersion C)
    (gysinSystemOfInvertible_isNaturalUnderOpensRestriction C)
    (gysinSystemOfInvertible_isNaturalUnderPullbackComp C)).injective (funext fun i ↦ ?_)
  rw [bivariantConnectedComponentEquiv_apply, bivariantConnectedComponentEquiv_apply,
    bivariantConnectedComponentRestriction_topChernClassDegreeOfInvertible,
    bivariantConnectedComponentRestriction_topChernTotalClass]
  by_cases hp : p = Scheme.Modules.rankOnConnectedComponent E i
  · subst hp
    rw [ite_eq_left rfl, (topChernClassOfInvertible_rankStratum C sX E i).2]
  · rw [ite_eq_right hp, topChernClassOfInvertible_of_ne_rank C sX E i p (by exact_mod_cast hp)]

/-- The cap product with the top Chern class in degree `e` is the operation of the degree-`e`
part of the completed top Chern class on the identity test scheme. -/
theorem topChernCap_eq (k : ℤ) (e : ℕ) (α : chowGroup C sX k) :
    topChernCap C sX E k e α =
      chowGroupCongr C (Category.id_comp sX) (k - e)
        ((topChernClassDegreeOfInvertible C sX E e).idRule C sX (gysinSystemOfInvertible C) (𝟙 X) k
          (chowGroupCongr C (Category.id_comp sX).symm k α)) := by
  rw [topChernClassDegreeOfInvertible_natCast]
  rfl

section Finite

/-- The top Chern class `c_top(E) = Σ_r c_r(E|_{X_r})` as an ordinary nonhomogeneous bivariant
class on `X`, when only finitely many of the loci `X_r` are nonempty: the sum, over the ranks `r`
that occur, of the degree-`r` part of the top Chern class. -/
@[stacks 0FA4 "ordinary finite top Chern class"]
def topChernClassFiniteOfInvertible
    (hfin : {r : ℕ | (Scheme.Modules.rankStratum E r : Set X).Nonempty}.Finite) :
    nonhomogeneousBivariantGroup C (gysinSystemOfInvertible C) sX sX (𝟙 X)
      (Category.id_comp sX) :=
  ∑ r ∈ hfin.toFinset, DirectSum.of _ (r : ℤ) (topChernClassDegreeOfInvertible C sX E (r : ℤ))

/-- If the locus `X_r` is nonempty, the degree-`r` component of the finite top Chern class is the
degree-`r` part of the top Chern class. -/
theorem topChernClassFiniteOfInvertible_natCast
    (hfin : {r : ℕ | (Scheme.Modules.rankStratum E r : Set X).Nonempty}.Finite) (r : ℕ)
    (hr : (Scheme.Modules.rankStratum E r : Set X).Nonempty) :
    topChernClassFiniteOfInvertible C sX E hfin (r : ℤ) =
      topChernClassDegreeOfInvertible C sX E (r : ℤ) := by
  rw [topChernClassFiniteOfInvertible, DirectSum.sum_apply, Finset.sum_eq_single r]
  · exact DirectSum.of_eq_same (r : ℤ) _
  · exact fun b _ hb ↦
      DirectSum.of_eq_of_ne (b : ℤ) (r : ℤ) _ fun he ↦ hb (Nat.cast_injective he).symm
  · exact absurd (hfin.mem_toFinset.2 hr)

/-- The degree-`p` component of the finite top Chern class vanishes when `p` is not the rank `r`
of any nonempty locus `X_r`. -/
theorem topChernClassFiniteOfInvertible_eq_zero
    (hfin : {r : ℕ | (Scheme.Modules.rankStratum E r : Set X).Nonempty}.Finite) (p : ℤ)
    (hp : ∀ r : ℕ, (Scheme.Modules.rankStratum E r : Set X).Nonempty → (r : ℤ) ≠ p) :
    topChernClassFiniteOfInvertible C sX E hfin p = 0 := by
  rw [topChernClassFiniteOfInvertible, DirectSum.sum_apply]
  exact Finset.sum_eq_zero fun b hb ↦
    DirectSum.of_eq_of_ne (b : ℤ) p _ (Ne.symm (hp b (hfin.mem_toFinset.1 hb)))

/-- The finite sum `Σ_r c_r(E|_{X_r})` has the completed top Chern class as its image under the
identification of Stacks 0FDZ: in every degree and on every connected component, its restriction is
the corresponding part of `c_top(E)`. -/
@[stacks 0FA4 "finite-class canonical image"]
theorem topChernClassFiniteOfInvertible_component
    (hfin : {r : ℕ | (Scheme.Modules.rankStratum E r : Set X).Nonempty}.Finite) (p : ℤ)
    (i : _root_.ConnectedComponents X) :
    bivariantConnectedComponentRestriction C (gysinSystemOfInvertible C) sX sX (𝟙 X)
        (Category.id_comp sX) p (gysinSystemOfInvertible_isNaturalUnderOpenImmersion C)
        (topChernClassFiniteOfInvertible C sX E hfin p) i =
      topChernClassOfInvertible C sX E i p := by
  by_cases hp : ∃ r : ℕ, (Scheme.Modules.rankStratum E r : Set X).Nonempty ∧ (r : ℤ) = p
  · obtain ⟨r, hr, rfl⟩ := hp
    rw [topChernClassFiniteOfInvertible_natCast C sX E hfin r hr]
    exact bivariantConnectedComponentRestriction_topChernClassDegreeOfInvertible C sX E (r : ℤ) i
  · have hp' : ∀ r : ℕ, (Scheme.Modules.rankStratum E r : Set X).Nonempty → (r : ℤ) ≠ p :=
      fun r hr hrp ↦ hp ⟨r, hr, hrp⟩
    rw [topChernClassFiniteOfInvertible_eq_zero C sX E hfin p hp', map_zero, Pi.zero_apply,
      topChernClassOfInvertible_of_ne_rank C sX E i p
        (Ne.symm (hp' _ (Scheme.Modules.nonempty_rankStratum_rankOnConnectedComponent E i)))]

/-- On the locus where `E` has rank `r`, the component of the finite sum `Σ_r c_r(E|_{X_r})` in
degree `r` is the `r`-th Chern class: a connected component `X_i` lies in the locus of the rank `r`
of `E` on it, and the degree-`r` component of the sum there is the restriction of `c_r(E)`, that is
`c_r(E|_{X_i})`. -/
@[stacks 0FA4 "finite-sum rank component"]
theorem topChernClassFiniteOfInvertible_rankStratum
    (hfin : {r : ℕ | (Scheme.Modules.rankStratum E r : Set X).Nonempty}.Finite)
    (i : _root_.ConnectedComponents X) :
    X.connectedComponentOpens i ≤
        Scheme.Modules.rankStratum E (Scheme.Modules.rankOnConnectedComponent E i) ∧
      bivariantConnectedComponentRestriction C (gysinSystemOfInvertible C) sX sX (𝟙 X)
          (Category.id_comp sX) _ (gysinSystemOfInvertible_isNaturalUnderOpenImmersion C)
          (topChernClassFiniteOfInvertible C sX E hfin
            (Scheme.Modules.rankOnConnectedComponent E i : ℤ)) i =
        bivariantConnectedComponentRestriction C (gysinSystemOfInvertible C) sX sX (𝟙 X)
          (Category.id_comp sX) _ (gysinSystemOfInvertible_isNaturalUnderOpenImmersion C)
          (totalChernOfFiniteLocallyFree C sX E (Scheme.Modules.rankOnConnectedComponent E i))
          i :=
  ⟨Scheme.Modules.connectedComponentOpens_le_rankStratum E i,
    (topChernClassFiniteOfInvertible_component C sX E hfin _ i).trans
      (topChernClassOfInvertible_rankStratum C sX E i).2⟩

/-- The finite sum `Σ_r c_r(E|_{X_r})` has no component in a degree other than the rank: on a
connected component on which `E` has rank `r`, its degree-`p` component vanishes for every
`p ≠ r`. -/
@[stacks 0FA4 "finite-sum off-rank component"]
theorem topChernClassFiniteOfInvertible_of_ne_rank
    (hfin : {r : ℕ | (Scheme.Modules.rankStratum E r : Set X).Nonempty}.Finite)
    (i : _root_.ConnectedComponents X) (p : ℤ)
    (h : p ≠ (Scheme.Modules.rankOnConnectedComponent E i : ℤ)) :
    bivariantConnectedComponentRestriction C (gysinSystemOfInvertible C) sX sX (𝟙 X)
        (Category.id_comp sX) p (gysinSystemOfInvertible_isNaturalUnderOpenImmersion C)
        (topChernClassFiniteOfInvertible C sX E hfin p) i = 0 :=
  (topChernClassFiniteOfInvertible_component C sX E hfin p i).trans
    (topChernClassOfInvertible_of_ne_rank C sX E i p h)

end Finite

end Stacks.Chow

end
