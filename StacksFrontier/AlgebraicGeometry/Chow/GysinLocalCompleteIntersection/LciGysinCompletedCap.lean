module

public import StacksFrontier.AlgebraicGeometry.Chow.GysinLocalCompleteIntersection.CompletedCapFundamental
public import StacksFrontier.AlgebraicGeometry.Chow.GysinLocalCompleteIntersection.LciGysinDimension
public import StacksFrontier.AlgebraicGeometry.Chow.Codimension.Equidimensional
public import StacksFrontier.AlgebraicGeometry.Chow.Codimension.FundamentalClass
public import StacksFrontier.AlgebraicGeometry.Chow.ClopenDecomposition.OpenImmersionPieces
public import StacksFrontier.AlgebraicGeometry.Chow.ClopenDecomposition.Coproduct
public import StacksFrontier.AlgebraicGeometry.Chow.GysinAtInfinity.FundamentalClass

/-!
# The cap of a completed bivariant class on componentwise classes

Let `f : X ⟶ Y` be a morphism of schemes locally of finite type over the base of Situation 02QL
and `c ∈ A^*(X ⟶ Y)^∧` an element of the completed bivariant group of Stacks 0FE0: on each
connected component `X_k` of `X`, lying over the connected component `Y_{a(k)}` of `Y`, it is a
finite sum `c_k = ∑_p c_{k,p}` with `c_{k,p} ∈ A^p(X_k ⟶ Y_{a(k)})`. A family
`α = (α_{j,m})` of classes `α_{j,m} ∈ CH_m(Y_j)` on the connected components of `Y` in every degree
(for instance the fundamental class `[Y] = ∑_m [Y_m]_m ∈ CH^0(Y)` of Stacks 0FE4, read on the
components) is capped to the family

  `(c ∩ α)_{k,n} = ∑_p c_{k,p} ∩ α_{a(k), n+p} ∈ CH_n(X_k)`,

which is `Stacks.Chow.completedCap`: the cap product of Stacks 0B76 is taken degree by degree, the
degree-`p` part of `c` lowering degrees by `p`. For `f` a local complete intersection morphism with
Gysin map `f^!` of Stacks 0FF3 this is how `f^![Y]` is read.

## Main definitions

* `Stacks.Chow.completedCap` — `c ∩ α`.
* `Stacks.Chow.componentFundamentalClass` — the family `([X_k]_n)_{k,n}` of fundamental classes of
  the connected components in every degree; for `X` satisfying the conditions of Stacks 0FE3 it is
  `[X] = ∑_n [X_n]_n`, a connected component lying in a single piece `X_n` and having fundamental
  class zero in every other degree.
* `Stacks.Chow.degreeZeroComponentRestrict`, `Stacks.Chow.degreeZeroAssemble` — a class in
  `CH^0(X) = ∏_n CH_n(X_n)` read on the connected components of `X`, and back.
* `Stacks.Chow.completedCapDegreeZero` — the cap product `c ∩ β ∈ CH^0(X)` of a class
  `β ∈ CH^0(Y)`.

## Main results

* `Stacks.Chow.completedCapDegreeZero_fundamentalClass_of`: if `c` caps the fundamental classes
  of the connected components of `Y` to those of `X`, then `c ∩ [Y] = [X]`.
* `Stacks.Chow.completedCap_regularSmooth_componentFundamentalClass`: `(i^! ∘ g^*)[Y] = [X]` on
  the connected components of `X`, for `i` a regular closed immersion and `g` smooth.

## References

* [Stacks Project, Tag 0FE0](https://stacks.math.columbia.edu/tag/0FE0)
* [Stacks Project, Tag 0FE4](https://stacks.math.columbia.edu/tag/0FE4)
* [Stacks Project, Tag 0B76](https://stacks.math.columbia.edu/tag/0B76)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Order

universe u

namespace Stacks.Chow

section Generic

/-- A point of a scheme is a generic point of an irreducible component exactly when it has no
proper generalization. -/
theorem mem_genericPoints_iff_coheight_eq_zero {T : Scheme.{u}} (t : T) :
    t ∈ genericPoints T ↔ coheight t = 0 := by
  rw [Order.coheight_eq_zero]
  constructor
  · intro ht y hy
    have hsp : y ⤳ t := hy
    exact specializes_iff_mem_closure.2 (ht.2 isIrreducible_singleton.closure
      (closure_minimal (Set.singleton_subset_iff.2 (specializes_iff_mem_closure.1 hsp))
        isClosed_closure) (subset_closure rfl))
  · intro ht
    have key : ∀ η : T, η ⤳ t → t = η := fun η hsp =>
      (Specializes.antisymm (ht (show t ≤ η from hsp)) hsp).eq
    obtain ⟨η, -, hsp⟩ := AlgebraicGeometry.exists_coheight_eq_zero_specializes t
    obtain rfl := key η hsp
    obtain ⟨W, hW, hxW⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible
      (closure ({t} : Set T)) isIrreducible_singleton.closure
    have hgen := hW.1.isGenericPoint_genericPoint (isClosed_of_mem_irreducibleComponents W hW)
    have hsp' : hW.1.genericPoint ⤳ t := hgen.specializes (hxW (subset_closure rfl))
    change closure ({t} : Set T) ∈ irreducibleComponents T
    rw [key _ hsp', hgen.def]
    exact hW

/-- **A fundamental class vanishes in every degree that is not the δ-dimension of a generic
point.** -/
theorem fundamentalChowClass_eq_zero_of_forall (C : ChowSituation.{u}) {T : Scheme.{u}}
    (sT : T ⟶ C.S) [LocallyOfFiniteType sT] (n : ℤ)
    (h : ∀ ξ : T, coheight ξ = 0 → relativeDimension C.dimensionFunction sT ξ ≠ n) :
    fundamentalChowClass C sT n = 0 := by
  have h0 : fundamentalCycle C sT n = 0 := by
    apply Subtype.ext
    apply Function.locallyFinsuppWithin.ext
    intro y
    change (cycleAssociatedToClosedSubscheme C sT (𝟙 T) n).1 y = 0
    refine cycleAssociatedToClosedSubscheme_apply_eq_zero C sT (𝟙 T) n y ?_
    rintro ⟨ξ, hξ, hd⟩
    have hy : (ξ : T) = y := hξ
    exact h ξ ((mem_genericPoints_iff_coheight_eq_zero _).1 ξ.2) (hy ▸ hd)
  rw [fundamentalChowClass, h0, map_zero]

/-- A bound on the δ-dimension of every point bounds the δ-dimension of the scheme. -/
theorem schemeDeltaDimension_le_of_forall_point_le (C : ChowSituation.{u})
    {T : Scheme.{u}} (s : T ⟶ C.S) [LocallyOfFiniteType s] {n : ℤ}
    (h : ∀ t : T, relativeDimension C.dimensionFunction s t ≤ n) :
    schemeDeltaDimension C s ≤ (n : EInt) := by
  have h2 := schemeDeltaDimension_le_of_forall_point C s (𝟙 T) (k := n) fun z => by simpa using h z
  exact (schemeDeltaDimension_congr C (Category.id_comp _)).symm.trans_le h2

/-- If every generic point of an irreducible component lying in the open `V` has δ-dimension at
most `m`, then `V` has δ-dimension at most `m`. -/
private theorem schemeDeltaDimension_opens_le (C : ChowSituation.{u}) {T : Scheme.{u}}
    (s : T ⟶ C.S) [LocallyOfFiniteType s] (V : T.Opens) {m : ℤ}
    (hm : ∀ y : T, coheight y = 0 → y ∈ V → relativeDimension C.dimensionFunction s y ≤ m) :
    schemeDeltaDimension C (V.ι ≫ s) ≤ (m : EInt) :=
  schemeDeltaDimension_le_of_forall_point_le C _ fun z => by
    rw [relativeDimension_comp_isOpenImmersion]
    obtain ⟨η, hη, hsp⟩ := exists_coheight_eq_zero_specializes (V.ι z)
    exact (relativeDimension_le_of_specializes C s hsp).trans
      (hm η hη ((specializes_iff_forall_open.1 hsp) _ V.isOpen z.2))

/-- **The fundamental class of an open subscheme vanishes in a degree** that is not the
δ-dimension of a generic point of an irreducible component of the ambient scheme meeting it. -/
theorem fundamentalChowClass_eq_zero_of_isOpenImmersion (C : ChowSituation.{u})
    {T W : Scheme.{u}} (sW : W ⟶ C.S) [LocallyOfFiniteType sW] (j : T ⟶ W) [IsOpenImmersion j]
    (s : T ⟶ C.S) [LocallyOfFiniteType s] (hs : j ≫ sW = s) (n : ℤ)
    (h : ∀ t : T, coheight (j t) = 0 → relativeDimension C.dimensionFunction sW (j t) ≠ n) :
    fundamentalChowClass C s n = 0 := by
  subst hs
  refine fundamentalChowClass_eq_zero_of_forall C _ n fun t ht => ?_
  rw [relativeDimension_comp_isOpenImmersion]
  exact h t (by rwa [coheight_eq_of_isOpenImmersion])

/-- The fundamental class of an open subscheme of a connected component on whose generic points
the δ-dimension is `m` vanishes in every degree other than `m`. -/
private theorem fundamentalChowClass_eq_zero_of_mem_connectedComponentOpens
    (C : ChowSituation.{u})
    {T W : Scheme.{u}} [LocallyConnectedSpace W] (sW : W ⟶ C.S) [LocallyOfFiniteType sW]
    (j : _root_.ConnectedComponents W) (m : ℤ)
    (hm : ∀ y : W, coheight y = 0 → y ∈ W.connectedComponentOpens j →
      relativeDimension C.dimensionFunction sW y = m)
    (e : T ⟶ W) [IsOpenImmersion e] (he : ∀ t, e t ∈ W.connectedComponentOpens j)
    (s : T ⟶ C.S) [LocallyOfFiniteType s] (hs : e ≫ sW = s) {N : ℤ} (hN : N ≠ m) :
    fundamentalChowClass C s N = 0 :=
  fundamentalChowClass_eq_zero_of_isOpenImmersion C sW e s hs N fun t ht =>
    (hm _ ht (he t)).trans_ne hN.symm

end Generic

section Cap

variable (C : ChowSituation.{u}) {X Y : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (f : X ⟶ Y) [LocallyOfFiniteType f] (hf : f ≫ sY = sX)
  [IsLocallyNoetherian X] [IsLocallyNoetherian Y]

/-- The fundamental classes `[X_k]_n` of the connected components of `X`, in every degree `n`. For
`X` satisfying the equivalent conditions of Stacks 0FE3 this family is the fundamental class
`[X] = ∑_n [X_n]_n ∈ CH^0(X)` of Stacks 0FE4: each connected component lies in one piece `X_n`, and
its fundamental class vanishes in every degree other than `n`. -/
def componentFundamentalClass :
    ∀ (k : _root_.ConnectedComponents X) (n : ℤ),
      chowGroup C ((X.connectedComponentOpens k).ι ≫ sX) n :=
  fun k n => fundamentalChowClass C ((X.connectedComponentOpens k).ι ≫ sX) n

/-- **The cap product of a completed bivariant class with a componentwise family of classes**:
`(c ∩ α)_{k,n} = ∑_p c_{k,p} ∩ α_{a(k), n+p} ∈ CH_n(X_k)`, the sum over the finitely many degrees
`p` in which the entry `c_k` of `c` on the connected component `X_k` is nonzero. Each
`c_{k,p} ∩ α_{a(k), n+p}` is the cap product of Stacks 0B76 at the test scheme `𝟙 : Y_{a(k)} ⟶
Y_{a(k)}`, a class on `X_k ×_{Y_{a(k)}} Y_{a(k)}`, read on `X_k` along the projection, which is an
isomorphism. -/
def completedCap (c : completedBivariantGroup C (gysinSystemOfInvertible C) sX sY f hf)
    (α : ∀ (j : _root_.ConnectedComponents Y) (m : ℤ),
      chowGroup C ((Y.connectedComponentOpens j).ι ≫ sY) m)
    (k : _root_.ConnectedComponents X) (n : ℤ) :
    chowGroup C ((X.connectedComponentOpens k).ι ≫ sX) n := by
  classical
  exact chowPushforwardOfIso C _ _ (pullback.fst (f.resConnectedComponent k) (𝟙 _)) rfl n
    (∑ p ∈ (c k).support, chowGroupDegreeEquiv C _ (by ring : (n + p) - p = n)
      ((c k p).cap (𝟙 _) (n + p)
        (chowGroupCongr C (Category.id_comp _).symm (n + p) (α _ (n + p)))))

/-- On an entry concentrated in a single degree `q`, the cap product is the cap product of that
degree. -/
theorem completedCap_of_eq_of (c : completedBivariantGroup C (gysinSystemOfInvertible C) sX sY f hf)
    (α : ∀ (j : _root_.ConnectedComponents Y) (m : ℤ),
      chowGroup C ((Y.connectedComponentOpens j).ι ≫ sY) m)
    (k : _root_.ConnectedComponents X) (q : ℤ) (hc : c k = DirectSum.of _ q (c k q)) (n : ℤ) :
    completedCap C sX sY f hf c α k n =
      chowPushforwardOfIso C _ _ (pullback.fst (f.resConnectedComponent k) (𝟙 _)) rfl n
        (chowGroupDegreeEquiv C _ (by ring : (n + q) - q = n)
          ((c k q).cap (𝟙 _) (n + q)
            (chowGroupCongr C (Category.id_comp _).symm (n + q) (α _ (n + q))))) := by
  classical
  unfold completedCap
  congr 1
  rw [Finset.sum_eq_single q]
  · intro p _ hpq
    have : c k p = 0 := by rw [hc, DirectSum.of_eq_of_ne (i := q) (j := p) _ hpq]
    rw [this, BivariantClass.zero_cap, map_zero]
  · intro hq
    rw [DFinsupp.notMem_support_iff.mp hq, BivariantClass.zero_cap]
    simp

/-- On an entry concentrated in a single degree `q` which caps every `α_{a(k), N}` to the
fundamental class in degree `N - q`, the cap product is the fundamental class. -/
theorem completedCap_eq_fundamentalChowClass_of
    (c : completedBivariantGroup C (gysinSystemOfInvertible C) sX sY f hf)
    (α : ∀ (j : _root_.ConnectedComponents Y) (m : ℤ),
      chowGroup C ((Y.connectedComponentOpens j).ι ≫ sY) m)
    (k : _root_.ConnectedComponents X) (q : ℤ) (hc : c k = DirectSum.of _ q (c k q))
    (h : ∀ N : ℤ, (c k q).cap (𝟙 _) N (chowGroupCongr C (Category.id_comp _).symm N (α _ N)) =
      fundamentalChowClass C (pullback.fst (f.resConnectedComponent k) (𝟙 _) ≫
        ((X.connectedComponentOpens k).ι ≫ sX)) (N - q)) (n : ℤ) :
    completedCap C sX sY f hf c α k n = componentFundamentalClass C sX k n := by
  rw [completedCap_of_eq_of C sX sY f hf c α k q hc n, h,
    chowGroupDegreeEquiv_fundamentalChowClass, componentFundamentalClass,
    chowPushforwardOfIso_fundamentalChowClass]

end Cap

section Pieces

variable (C : ChowSituation.{u}) {Y : Scheme.{u}} (sY : Y ⟶ C.S) [LocallyOfFiniteType sY]
  [IsLocallyNoetherian Y]

/-- The open and closed piece `Y_m` of a dimension decomposition `Y = ⨿_m Y_m` (Stacks 0FE3 (1)),
the one chosen in the fundamental class `[Y] = ∑_m [Y_m]_m` of Stacks 0FE4. -/
abbrev dimensionPiece (hY : HasDimensionDecomposition (relativeDimension C.dimensionFunction sY))
    (m : ℤ) : Y.Opens :=
  Classical.choose hY m

variable (hY : HasDimensionDecomposition (relativeDimension C.dimensionFunction sY))

omit [LocallyOfFiniteType sY] [IsLocallyNoetherian Y] in
/-- The open pieces `Y_m` are pairwise disjoint and cover `Y`. -/
theorem isClopenDecomposition_dimensionPiece : IsClopenDecomposition (dimensionPiece C sY hY) :=
  (Classical.choose_spec hY).1

omit [LocallyOfFiniteType sY] [IsLocallyNoetherian Y] in
/-- **A generic point of an irreducible component of `Y` lying in the piece `Y_m` has
δ-dimension `m`.** -/
theorem relativeDimension_eq_of_mem_dimensionPiece {y : Y} (hy : coheight y = 0) {m : ℤ}
    (hym : y ∈ dimensionPiece C sY hY m) : relativeDimension C.dimensionFunction sY y = m := by
  have hpure := (Classical.choose_spec hY).2
  have hZ := (mem_genericPoints_iff_coheight_eq_zero y).2 hy
  have hgen : IsGenericPoint (⟨y, hym⟩ : (dimensionPiece C sY hY m : Set Y))
      (Subtype.val ⁻¹' closure ({y} : Set Y)) := by
    change closure ({(⟨y, hym⟩ : (dimensionPiece C sY hY m : Set Y))} :
      Set (dimensionPiece C sY hY m : Set Y)) = _
    ext z
    rw [closure_subtype]
    simp [Set.image_singleton]
  exact hpure m _ (preimage_mem_irreducibleComponents hZ
    (dimensionPiece C sY hY m).isOpen.isOpenEmbedding_subtypeVal
    ⟨y, subset_closure rfl, ⟨⟨y, hym⟩, rfl⟩⟩) ⟨y, hym⟩ hgen

omit [LocallyOfFiniteType sY] in
/-- A connected component of `Y` meeting the piece `Y_m` lies in it. -/
theorem connectedComponentOpens_le_dimensionPiece {j : _root_.ConnectedComponents Y} {y : Y}
    (hyj : y ∈ Y.connectedComponentOpens j) {m : ℤ} (hym : y ∈ dimensionPiece C sY hY m) :
    Y.connectedComponentOpens j ≤ dimensionPiece C sY hY m := by
  obtain rfl : ConnectedComponents.mk y = j := hyj
  exact fun z hz =>
    ((isClopenDecomposition_dimensionPiece C sY hY).isClopen m).connectedComponent_subset hym
      (ConnectedComponents.coe_eq_coe'.mp hz)

omit [IsLocallyNoetherian Y] in
/-- **The piece `Y_m` has δ-dimension at most `m`.** -/
theorem schemeDeltaDimension_dimensionPiece_le (m : ℤ) :
    schemeDeltaDimension C ((dimensionPiece C sY hY m).ι ≫ sY) ≤ (m : EInt) :=
  schemeDeltaDimension_opens_le C sY (dimensionPiece C sY hY m) fun _ hy hym =>
    (relativeDimension_eq_of_mem_dimensionPiece C sY hY hy hym).le

omit [LocallyOfFiniteType sY] in
include hY in
/-- **On a connected component of a scheme satisfying the conditions of Stacks 0FE3 the generic
points have one δ-dimension.** -/
theorem exists_relativeDimension_eq_of_hasDimensionDecomposition
    (j : _root_.ConnectedComponents Y) :
    ∃ m : ℤ, ∀ y : Y, coheight y = 0 → y ∈ Y.connectedComponentOpens j →
      relativeDimension C.dimensionFunction sY y = m := by
  obtain ⟨y₀, rfl⟩ := ConnectedComponents.surjective_coe j
  obtain ⟨m, hm⟩ := (isClopenDecomposition_dimensionPiece C sY hY).exists_mem y₀
  have hle := connectedComponentOpens_le_dimensionPiece C sY hY (j := ConnectedComponents.mk y₀)
    (y := y₀) rfl hm
  exact ⟨m, fun y hy hyj => relativeDimension_eq_of_mem_dimensionPiece C sY hY hy (hle hyj)⟩

/-- A generalization of a point of a connected component lies in that connected component. -/
theorem mem_connectedComponentOpens_of_specializes {T : Scheme.{u}} [LocallyConnectedSpace T]
    {y x : T} (h : y ⤳ x) {j : _root_.ConnectedComponents T}
    (hx : x ∈ T.connectedComponentOpens j) : y ∈ T.connectedComponentOpens j := by
  have hx' : ConnectedComponents.mk x = j := hx
  change ConnectedComponents.mk y = j
  rw [← hx', ConnectedComponents.coe_eq_coe']
  have h2 : x ∈ connectedComponent y :=
    isPreconnected_singleton.closure.subset_connectedComponent (subset_closure rfl)
      (specializes_iff_mem_closure.1 h)
  rw [← connectedComponent_eq h2]
  exact mem_connectedComponent

end Pieces

section DegreeZero

/-! ### Classes in `CH^0` read on the connected components -/

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  [IsLocallyNoetherian X]
  (hX : HasDimensionDecomposition (relativeDimension C.dimensionFunction sX))

omit [LocallyOfFiniteType sX] in
/-- If the connected component `X_k` lies in the piece `X_n`, the inclusion `X_k ⊆ X_n` followed
by the structure morphism of `X_n` is the structure morphism of `X_k`. -/
theorem homOfLE_comp_dimensionPiece {k : _root_.ConnectedComponents X} {n : ℤ}
    (h : X.connectedComponentOpens k ≤ dimensionPiece C sX hX n) :
    X.homOfLE h ≫ (dimensionPiece C sX hX n).ι ≫ sX = (X.connectedComponentOpens k).ι ≫ sX := by
  rw [← Category.assoc, Scheme.homOfLE_ι]

/-- **The restriction of a class `β = (β_n)_n ∈ CH^0(X) = ∏_n CH_n(X_n)` to the connected
components of `X`**: on the connected component `X_k`, in degree `n`, the restriction of `β_n`
from `X_n` to `X_k` when `X_k ⊆ X_n`, and zero otherwise (then `X_k` is disjoint from `X_n`). -/
def degreeZeroComponentRestrict (β : degreeZeroChowGroup C sX hX) :
    ∀ (k : _root_.ConnectedComponents X) (n : ℤ),
      chowGroup C ((X.connectedComponentOpens k).ι ≫ sX) n := by
  classical
  exact fun k n => if h : X.connectedComponentOpens k ≤ dimensionPiece C sX hX n then
    chowGroupRestrict C ((dimensionPiece C sX hX n).ι ≫ sX) ((X.connectedComponentOpens k).ι ≫ sX)
      (X.homOfLE h) (homOfLE_comp_dimensionPiece C sX hX h) n (β n)
  else 0

omit [LocallyOfFiniteType sX] in
/-- **The connected components of `X` contained in the piece `X_n` decompose it** into open and
closed subschemes. -/
theorem isClopenDecomposition_dimensionPiece_connectedComponents (n : ℤ) :
    IsClopenDecomposition fun i : {k : _root_.ConnectedComponents X //
        X.connectedComponentOpens k ≤ dimensionPiece C sX hX n} => (X.homOfLE i.2).opensRange := by
  refine isClopenDecomposition_of_isOpenImmersion_cover _ (fun x => ?_) fun i l hil => ?_
  · have hle := connectedComponentOpens_le_dimensionPiece C sX hX
      (j := ConnectedComponents.mk x.1) (y := x.1) rfl x.2
    exact ⟨⟨_, hle⟩, ⟨⟨x.1, rfl⟩, Subtype.ext (Scheme.homOfLE_apply _ _)⟩⟩
  · refine Set.disjoint_left.2 ?_
    rintro _ ⟨⟨a, ha⟩, rfl⟩ ⟨⟨b, hb⟩, h⟩
    rw [Scheme.homOfLE_apply', Scheme.homOfLE_apply'] at h
    obtain rfl : b = a := congrArg Subtype.val h
    exact Set.disjoint_left.1 (TopologicalSpace.Opens.coe_disjoint.2
      (X.disjoint_connectedComponentOpens (fun he => hil (Subtype.ext he)))) ha hb

/-- **A family of classes on the connected components of `X` assembled into `CH^0(X)`**: in
degree `n`, the class on `X_n` whose restriction to each connected component `X_k ⊆ X_n` is the
given class `γ_{k,n}`, by `CH_n(X_n) = ∏_{X_k ⊆ X_n} CH_n(X_k)`
(`Stacks.Chow.chowGroupClopenRestrictEquiv`). -/
def degreeZeroAssemble (γ : ∀ (k : _root_.ConnectedComponents X) (n : ℤ),
    chowGroup C ((X.connectedComponentOpens k).ι ≫ sX) n) : degreeZeroChowGroup C sX hX :=
  fun n => (chowGroupClopenRestrictEquiv C ((dimensionPiece C sX hX n).ι ≫ sX)
    (fun i : {k : _root_.ConnectedComponents X //
      X.connectedComponentOpens k ≤ dimensionPiece C sX hX n} =>
        (X.connectedComponentOpens i.1).ι ≫ sX)
    (fun i => X.homOfLE i.2) (fun i => homOfLE_comp_dimensionPiece C sX hX i.2)
    (isClopenDecomposition_dimensionPiece_connectedComponents C sX hX n) n).symm
    (fun i => γ i.1 n)

/-- **`[X]` read on the connected components is the family of their fundamental classes.** -/
theorem degreeZeroComponentRestrict_fundamentalClass :
    degreeZeroComponentRestrict C sX hX (fundamentalClass C sX hX) =
      componentFundamentalClass C sX := by
  funext k n
  unfold degreeZeroComponentRestrict
  split_ifs with h
  · exact chowGroupRestrict_fundamentalChowClass C _ _ _ _ n
      (schemeDeltaDimension_dimensionPiece_le C sX hX n)
  · refine (fundamentalChowClass_eq_zero_of_isOpenImmersion C sX _ _ rfl n fun t ht => ?_).symm
    obtain ⟨n', hn'⟩ := (isClopenDecomposition_dimensionPiece C sX hX).exists_mem
      ((X.connectedComponentOpens k).ι t)
    rw [relativeDimension_eq_of_mem_dimensionPiece C sX hX ht hn']
    rintro rfl
    exact h (connectedComponentOpens_le_dimensionPiece C sX hX t.2 hn')

/-- **The family of fundamental classes of the connected components assembles to `[X]`.** -/
theorem degreeZeroAssemble_componentFundamentalClass :
    degreeZeroAssemble C sX hX (componentFundamentalClass C sX) = fundamentalClass C sX hX := by
  funext n
  refine (AddEquiv.symm_apply_eq _).2 (funext fun i => ?_)
  rw [chowGroupClopenRestrictEquiv_apply]
  exact (chowGroupRestrict_fundamentalChowClass C _ _ _ _ n
    (schemeDeltaDimension_dimensionPiece_le C sX hX n)).symm

variable {Y : Scheme.{u}} (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (f : X ⟶ Y)
  [LocallyOfFiniteType f] (hf : f ≫ sY = sX) [IsLocallyNoetherian Y]
  (hY : HasDimensionDecomposition (relativeDimension C.dimensionFunction sY))

/-- **The cap product of a completed bivariant class with a class in `CH^0`**, for `X` and `Y`
satisfying the conditions of Stacks 0FE3: the codimension-zero part
`(c ∩ β)_n ∈ CH_n(X_n)` of `c ∩ β`, i.e. the class on `X_n` whose restriction to each connected
component `X_k ⊆ X_n` is `(c ∩ β|_{Y_{a(k)}})_{k,n} = ∑_p c_{k,p} ∩ β|_{Y_{a(k)}, n+p}`
(`Stacks.Chow.completedCap`). Here `CH^0(X) = ∏_n CH_n(X_n)` as in Stacks 0FE4. -/
def completedCapDegreeZero (c : completedBivariantGroup C (gysinSystemOfInvertible C) sX sY f hf)
    (β : degreeZeroChowGroup C sY hY) : degreeZeroChowGroup C sX hX :=
  degreeZeroAssemble C sX hX (completedCap C sX sY f hf c (degreeZeroComponentRestrict C sY hY β))

/-- If `c` caps the fundamental classes of the connected components of `Y` to those of `X`, then
`c ∩ [Y] = [X]` in `CH^0(X)`. -/
theorem completedCapDegreeZero_fundamentalClass_of
    (c : completedBivariantGroup C (gysinSystemOfInvertible C) sX sY f hf)
    (h : ∀ k n, completedCap C sX sY f hf c (componentFundamentalClass C sY) k n =
      componentFundamentalClass C sX k n) :
    completedCapDegreeZero C sX hX sY f hf hY c (fundamentalClass C sY hY) =
      fundamentalClass C sX hX := by
  unfold completedCapDegreeZero
  rw [degreeZeroComponentRestrict_fundamentalClass]
  have : completedCap C sX sY f hf c (componentFundamentalClass C sY) =
      componentFundamentalClass C sX := funext fun k => funext fun n => h k n
  rw [this, degreeZeroAssemble_componentFundamentalClass]

end DegreeZero

section Gysin

open Stacks.AlgebraicGeometry.RegularIdealSheaf

variable (C : ChowSituation.{u}) {X U Y : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] [IsLocallyNoetherian X] [IsLocallyNoetherian U]
  [IsLocallyNoetherian Y] (i : X ⟶ U) [IsClosedImmersion i] (hi : IsRegularImmersion i)
  (g : U ⟶ Y) [Smooth g] [LocallyOfFiniteType g] (hX : i ≫ (g ≫ sY) = sX)

omit [LocallyOfFiniteType sX] in
include hi hX in
/-- **The δ-dimension of a generic point of a connected component of `X`**, for `X ⟶ U ⟶ Y` a
regular closed immersion followed by a smooth morphism and `Y` satisfying the conditions of
Stacks 0FE3: `m + d - r`, with `m` the δ-dimension of the component of `Y` below, `d` the relative
dimension of `g` and `r` the rank of the normal sheaf. -/
theorem relativeDimension_genericPoint_eq (k : _root_.ConnectedComponents X) (m : ℤ)
    (hm : ∀ y : Y, coheight y = 0 →
      y ∈ Y.connectedComponentOpens (g.continuous.connectedComponentsMap
        (i.continuous.connectedComponentsMap k)) →
      relativeDimension C.dimensionFunction sY y = m)
    (ξ : X) (hξ : coheight ξ = 0) (hξk : ξ ∈ X.connectedComponentOpens k) :
    relativeDimension C.dimensionFunction sX ξ =
      m + g.smoothComponentDimension (i.continuous.connectedComponentsMap k) -
        (VirtualNormalBundle.ofIsRegularImmersion i hi).componentRank k := by
  have hk : ConnectedComponents.mk ξ = k := hξk
  have hr := coheight_eq_componentRank_ofIsRegularImmersion i hi hξ
  rw [hk] at hr
  have hiξ : i ξ ∈ U.connectedComponentOpens (i.continuous.connectedComponentsMap k) :=
    i.connectedComponentOpens_le_preimage k hξk
  have hd := g.fiberDimensionAt_eq_smoothComponentDimension
    (i.continuous.connectedComponentsMap k) (i ξ) hiξ
  have h := relativeDimension_eq_of_closedImmersion_of_smooth C sY i g hr m (fun y hy hsp => hm y hy
    (mem_connectedComponentOpens_of_specializes hsp
      (g.connectedComponentOpens_le_preimage _ hiξ))) _ hd
  rwa [hX] at h

/-- The completed class of the smooth pullback along `g`, on a connected component `U_a`: the flat
pullback of relative dimension `d_a`, in degree `-d_a`. -/
private theorem smoothPullbackCompletedClass_apply (a : _root_.ConnectedComponents U) :
    smoothPullbackCompletedClass C (g ≫ sY) sY g rfl a =
      DirectSum.of _ (-(g.smoothComponentDimension a : ℤ))
        (flatPullbackBivariantClassOfInvertible C ((U.connectedComponentOpens a).ι ≫ g ≫ sY)
          ((Y.connectedComponentOpens (g.continuous.connectedComponentsMap a)).ι ≫ sY)
          (g.resConnectedComponent a) (g.resConnectedComponent_comp_ι_comp rfl a)
          (g.smoothComponentDimension a) (g.relativeDimension_resConnectedComponent_of_smooth a)) :=
  rfl

/-- For `g` smooth, if the generic points of the connected component of `Y` below `U_a` have
δ-dimension `m`, then `U_a` has δ-dimension at most `m + d_a`. -/
private theorem schemeDeltaDimension_connectedComponentOpens_le_of_smooth
    (a : _root_.ConnectedComponents U)
    (m : ℤ) (hm : ∀ y : Y, coheight y = 0 →
      y ∈ Y.connectedComponentOpens (g.continuous.connectedComponentsMap a) →
      relativeDimension C.dimensionFunction sY y = m) :
    schemeDeltaDimension C ((U.connectedComponentOpens a).ι ≫ g ≫ sY) ≤
      ((m - -(g.smoothComponentDimension a : ℤ) : ℤ) : EInt) :=
  schemeDeltaDimension_opens_le C (g ≫ sY) _ fun v hv hva => by
    rw [relativeDimension_eq_add_of_coheight_eq_zero C sY g hv _
      (g.fiberDimensionAt_eq_smoothComponentDimension a v hva),
      hm _ (coheight_eq_zero_map_of_flat g hv) (g.connectedComponentOpens_le_preimage a hva)]
    omega

include hi in
/-- **`(i^! ∘ g^*)[Y] = [X]`** on the connected components of `X`, for `i` a regular closed
immersion, `g` smooth and `Y` satisfying the conditions of Stacks 0FE3; `i^!` is the class of
Stacks 0FBK of the normal sheaf of `i` and `g^*` flat pullback (Stacks 0B78), both in the completed
groups of Stacks 0FE0. -/
theorem completedCap_regularSmooth_componentFundamentalClass
    (hY : HasDimensionDecomposition (relativeDimension C.dimensionFunction sY))
    (k : _root_.ConnectedComponents X) (n : ℤ) :
    completedCap C sX sY (i ≫ g) (comp_comp_structureMorphism_eq hX rfl)
        (completedBivariantCompositeOfInvertible C sX (g ≫ sY) sY i g hX rfl
          ((VirtualNormalBundle.ofIsRegularImmersion i hi).completedClass C (g ≫ sY) sX hX)
          (smoothPullbackCompletedClass C (g ≫ sY) sY g rfl))
        (componentFundamentalClass C sY) k n = componentFundamentalClass C sX k n := by
  obtain ⟨m, hm⟩ := exists_relativeDimension_eq_of_hasDimensionDecomposition C sY hY
    (g.continuous.connectedComponentsMap (i.continuous.connectedComponentsMap k))
  have hgen := relativeDimension_genericPoint_eq C sX sY i hi g hX k m hm
  set 𝒩 := VirtualNormalBundle.ofIsRegularImmersion i hi
  set a := i.continuous.connectedComponentsMap k
  set r := 𝒩.componentRank k
  set d := g.smoothComponentDimension a
  have hck := completedBivariantCompositeOfInvertible_of_of C sX (g ≫ sY) sY i g hX rfl
    (𝒩.completedClass C (g ≫ sY) sX hX) (smoothPullbackCompletedClass C (g ≫ sY) sY g rfl) k
    r (-(d : ℤ)) (𝒩.completedClass_apply_eq_of C (g ≫ sY) sX hX k)
    (by rw [smoothPullbackCompletedClass_apply, DirectSum.of_eq_same])
  have hZk : schemeDeltaDimension C ((X.connectedComponentOpens k).ι ≫ sX) ≤
      ((m - -(d : ℤ) - r : ℤ) : EInt) :=
    schemeDeltaDimension_opens_le C sX _ fun x hx hxk => by
      have := hgen x hx hxk
      omega
  have ha := 𝒩.completedClass_rank_cap_fundamentalChowClass hi C (g ≫ sY) sX hX k
    (m - -(d : ℤ)) (schemeDeltaDimension_connectedComponentOpens_le_of_smooth C sY g a m hm) hZk
  have hcomp := bivariantCompositeOfInvertible_flatPullback_cap_fundamentalChowClass C
    ((X.connectedComponentOpens k).ι ≫ sX) ((U.connectedComponentOpens a).ι ≫ g ≫ sY)
    ((Y.connectedComponentOpens (g.continuous.connectedComponentsMap a)).ι ≫ sY)
    (i.resConnectedComponent k) (i.resConnectedComponent_comp_ι_comp hX k)
    (g.resConnectedComponent a) (g.resConnectedComponent_comp_ι_comp rfl a) d
    (g.relativeDimension_resConnectedComponent_of_smooth a)
    (𝒩.completedClass C (g ≫ sY) sX hX k r) m
    (schemeDeltaDimension_opens_le C sY _ fun y hy hya => (hm y hy hya).le) ha
  refine completedCap_eq_fundamentalChowClass_of C sX sY (i ≫ g) _ _ _ k ((r : ℤ) + -(d : ℤ))
    (by rw [hck, DirectSum.of_eq_same]) (fun N => ?_) n
  rw [hck, DirectSum.of_eq_same, smoothPullbackCompletedClass_apply, DirectSum.of_eq_same]
  unfold componentFundamentalClass
  rw [chowGroupCongr_fundamentalChowClass]
  by_cases hN : N = m
  · subst hN
    unfold completedBivariantCompositeTransport
    exact bivariantClassComponentCongr_cap_fundamentalChowClass C _ sY _ _ _ _ _ _ _ _ _ hcomp
  · have h0L : fundamentalChowClass C (𝟙 _ ≫
        ((Y.connectedComponentOpens ((i ≫ g).continuous.connectedComponentsMap k)).ι ≫ sY)) N =
          0 :=
      fundamentalChowClass_eq_zero_of_mem_connectedComponentOpens C sY _ m hm _
        (fun t => by rw [← Scheme.Hom.connectedComponentsMap_comp]; exact t.2) _
        (Category.id_comp _).symm hN
    have h0R : fundamentalChowClass C (pullback.fst ((i ≫ g).resConnectedComponent k) (𝟙 _) ≫
        ((X.connectedComponentOpens k).ι ≫ sX)) (N - ((r : ℤ) + -(d : ℤ))) = 0 :=
      fundamentalChowClass_eq_zero_of_mem_connectedComponentOpens C sX k _ hgen
        (pullback.fst ((i ≫ g).resConnectedComponent k) (𝟙 _) ≫ (X.connectedComponentOpens k).ι)
        (fun t => by
          rw [Scheme.Hom.comp_apply]
          exact (pullback.fst ((i ≫ g).resConnectedComponent k) (𝟙 _) t).2) _
        (Category.assoc _ _ _) (by omega)
    rw [h0L, map_zero, h0R]

end Gysin

end Stacks.Chow

end
