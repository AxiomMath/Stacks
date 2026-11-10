module

public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.Data.List.TFAE
public import StacksFrontier.AlgebraicGeometry.Size.Cutoff
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartLocality
public import StacksFrontier.AlgebraicGeometry.Spaces.ImmersionFppfLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Stacks.AlgebraicSpaceStackPresentation
public import StacksFrontier.AlgebraicGeometry.Stacks.FinitenessComposition
public import StacksFrontier.AlgebraicGeometry.Stacks.FlatOpenPointsAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.ImmersionBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.ImmersionPointsAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.NoetherianPointsAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.ProperAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiCompactPointRepresentative
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertySchemeMap
public import StacksFrontier.AlgebraicGeometry.Stacks.SchemeAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.SchemeStack
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothAlgebraicStackBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalPropertyAtlasBridges
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalPropertyAtlasSpace
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothPresentationQuasiCompact
public import StacksFrontier.AlgebraicGeometry.Stacks.SurjectiveBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.UnderlyingTwoFibreProduct
public import StacksFrontier.AlgebraicGeometry.Stacks.UniversallyClosedBaseChange
public import StacksFrontier.CategoryTheory.TwoFibreProduct.CospanReindex
public import StacksFrontier.CategoryTheory.TwoFibreProduct.Pasting
public import StacksFrontier.Topology.Maps.OpenSurjectiveDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothLocalityFiniteness
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentationFppfLocality
public import StacksFrontier.CategoryTheory.FiberedCategory.IsoOver

/-!
# Universal closedness of a 1-morphism of algebraic stacks is smooth local on the target

Let `f : 𝒳 ⟶ 𝒴` be a 1-morphism of algebraic stacks over `S`. **Stacks 0CL3** says that `f` is
universally closed (Stacks 0513) exactly when every base change of `f` to a scheme of the site
is closed on points, exactly when every base change of `f` to an *affine* scheme of the site is
closed on points, and exactly when the base change of `f` along *one* smooth surjective
1-morphism from an algebraic space is universally closed.

**Stacks 0H2A** is the finite-presentation refinement of this for a *quasi-compact* `f`: universal
closedness is equivalent to closedness of the base change to every affine scheme of the site
which is locally of finite presentation over `𝒴`, and to closedness of the base change to affine
`n`-space over one smooth surjective chart of `𝒴`, for every `n ≥ 0`. Three of its implications
are proved here, together with three steps of the proof of the two converse ones: closedness of a
base change descends along an immersion of the base, the implication (3) implies (2) at a target
represented by a scheme, and the reduction of (2) implies (1) to such a target. See the
implementation notes for what the two converse implications still need.

## Main results

* `AlgebraicGeometry.Stack.AlgebraicStacks.universallyClosed_tfae`: **Stacks 0CL3**.
* `AlgebraicGeometry.Stack.AlgebraicStacks.isClosed_baseChange_of_isImmersion`: **Stacks 0H2A**,
  the step which descends closedness of a base change along an immersion of the base.
* `AlgebraicGeometry.Stack.AlgebraicStacks.affineSpaceChart`: affine `n`-space over a scheme of
  the site, as a scheme of the site.
* `AlgebraicGeometry.Stack.AlgebraicStacks.isLocallyOfFinitePresentation_schemeStackMap`: a
  morphism of the site locally of finite presentation induces a 1-morphism of the represented
  algebraic stacks locally of finite presentation.
* `AlgebraicGeometry.Stack.AlgebraicStacks`
  `.isClosed_baseChange_affine_isLocallyOfFinitePresentation_of_universallyClosed`:
  **Stacks 0H2A**, (1) implies (2).
* `AlgebraicGeometry.Stack.AlgebraicStacks`
  `.exists_chart_forall_isClosed_baseChange_affineSpaceChart_of_universallyClosed`:
  **Stacks 0H2A**, (1) implies (3).
* `AlgebraicGeometry.Stack.AlgebraicStacks`
  `.exists_chart_forall_isClosed_baseChange_affineSpaceChart_of_isClosed_affine_lfp`:
  **Stacks 0H2A**, (2) implies (3).
* `AlgebraicGeometry.Stack.AlgebraicStacks.isImmersion_schemeStackMap`: a morphism of the site
  which is an immersion of schemes induces an immersion of the represented algebraic stacks.
* `AlgebraicGeometry.Stack.AlgebraicStacks`
  `.isClosed_baseChange_schemeStackMap_of_forall_isClosed_baseChange_affineSpaceChart`:
  **Stacks 0H2A**, the step of (3) implies (2) at a target represented by a scheme.
* `AlgebraicGeometry.Stack.AlgebraicStacks`
  `.isClosed_baseChange_affine_isLocallyOfFinitePresentation_baseChange`: **Stacks 0H2A**, clause
  (2) is inherited by a base change along a 1-morphism locally of finite presentation.
* `AlgebraicGeometry.Stack.AlgebraicStacks`
  `.universallyClosed_of_forall_schemeStack_target_of_isClosed_affine_lfp`: **Stacks 0H2A**, the
  reduction of (2) implies (1) to a target represented by a scheme.

## Implementation notes

The source's clause (3) reads `|𝐀^n × (𝒳 ×_𝒴 V)| → |𝐀^n × V|`. Over `V` the left-hand stack is
`(𝒳 ×_𝒴 V) ×_V 𝐀^n_V = 𝒳 ×_𝒴 𝐀^n_V`, so the clause is closedness of the base change of `f`
along the composite `𝐀^n_V ⟶ V ⟶ 𝒴`, which is how it is written here. Affine `n`-space over a
scheme of the site is again a scheme of the site because its structure morphism is affine and
locally of finite type, hence quasi-compact.

The two converse implications of Stacks 0H2A are *not* proved here, and both are short of one
and the same input: the separation lemma of **Stacks 0H29** for algebraic stacks.

(2) implies (1) is the limit argument. Its two ends are available: the reduction to a target
represented by a scheme is
`universallyClosed_of_forall_schemeStack_target_of_isClosed_affine_lfp` below, built from clause
(2) base changing along a 1-morphism locally of finite presentation and the smooth-surjective
descent of universal closedness; and the scheme-level engine of Stacks 0H29 is
`AlgebraicGeometry.exists_affine_locallyFinitePresentation_separation_isClosed`, the
closed-subset form of **Stacks 05BD**, while the two point-set steps which read its conclusion
back up to the stack are `AlgebraicGeometry.Stack.AlgebraicStacks`
`.image_preimage_eq_preimage_image_of_isTwoFibreProduct` and
`.image_closure_image_subset_of_isTwoFibreProduct`. What is missing is Stacks 0H29 for algebraic
stacks itself, and the input it needs is the identification, at the level of the 2-category of
algebraic stacks, of the fibre product of two objects of the site with the 2-fibre product of
the stacks they represent: the engine's closed subset lives in a fibre product of *schemes*,
while hypothesis (2) speaks about closed subsets of a 2-fibre product of *stacks*. Only the
presheaf-level shadow of that identification exists, namely
`AlgebraicGeometry.Stack.isPullback_representingMap_twoFibreProduct`.

(3) implies (1) factors through (2) implies (1), and its own step is proved here. The immersion
`Z ⟶ 𝐀ⁿ_V` of **Stacks 04II** induces an immersion of the represented stacks by
`isImmersion_schemeStackMap` below, which transports the scheme-level immersion using that being
an immersion is fppf local on the target for morphisms of algebraic spaces (**Stacks 042U**) and
stable under base change; feeding it to `isClosed_baseChange_of_isImmersion` gives
`isClosed_baseChange_schemeStackMap_of_forall_isClosed_baseChange_affineSpaceChart`, which is
clause (2) at a target represented by a scheme for the bases that clause (3) reaches, namely the
quasi-affine ones locally of finite type over the chart.

## References

* [Stacks Project, Tag 042U](https://stacks.math.columbia.edu/tag/042U)
* [Stacks Project, Tag 04II](https://stacks.math.columbia.edu/tag/04II)
* [Stacks Project, Tag 0CL3](https://stacks.math.columbia.edu/tag/0CL3)
* [Stacks Project, Tag 0DNP](https://stacks.math.columbia.edu/tag/0DNP)
* [Stacks Project, Tag 0H29](https://stacks.math.columbia.edu/tag/0H29)
* [Stacks Project, Tag 0H2A](https://stacks.math.columbia.edu/tag/0H2A)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack.AlgebraicStacks

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Topological input -/

/-- **Closedness descends along a jointly surjective family of open base changes.** Let
`f : A → B` be a map of topological spaces and let `e i : D' i → B` be a family of open maps
whose images cover `B`; suppose each `q i : A' i → D' i` sits in a commutative square over
`f` whose canonical map to the fibre product is surjective. Then `f` is closed as soon as every
`q i` is.

This is the family form of `isClosedMap_of_isClosedMap_comm_of_isOpenMap_surjective`, which is
the case of a single index. -/
private theorem isClosedMap_of_isClosedMap_family {A C : Type*} [TopologicalSpace A]
    [TopologicalSpace C] {I : Type*} {A' D' : I → Type*}
    [∀ i, TopologicalSpace (A' i)] [∀ i, TopologicalSpace (D' i)]
    (f : A → C) (g : ∀ i, A' i → A) (e : ∀ i, D' i → C) (q : ∀ i, A' i → D' i)
    (hcomm : ∀ i a', f (g i a') = e i (q i a'))
    (hcart : ∀ i a d', f a = e i d' → ∃ a', g i a' = a ∧ q i a' = d')
    (hg : ∀ i, Continuous (g i)) (ho : ∀ i, IsOpenMap (e i))
    (hcover : ∀ c, ∃ i d', e i d' = c) (hq : ∀ i, IsClosedMap (q i)) : IsClosedMap f := by
  intro s hs
  have hcompl : (f '' s)ᶜ = ⋃ i, e i '' (q i '' (g i ⁻¹' s))ᶜ := by
    ext c
    simp only [Set.mem_compl_iff, Set.mem_iUnion, Set.mem_image]
    constructor
    · intro hc
      obtain ⟨i, d, hdc⟩ := hcover c
      refine ⟨i, d, ?_, hdc⟩
      rintro ⟨a', ha', hq'⟩
      exact hc ⟨g i a', ha', ((hcomm i a').trans (congrArg (e i) hq')).trans hdc⟩
    · rintro ⟨i, d, hd, hdc⟩ ⟨a, ha, hfa⟩
      obtain ⟨a', hga, hqa⟩ := hcart i a d (hfa.trans hdc.symm)
      exact hd ⟨a', by simpa [hga] using ha, hqa⟩
  rw [← isOpen_compl_iff, hcompl]
  exact isOpen_iUnion fun i => (ho i) _ (hq i _ (hs.preimage (hg i))).isOpen_compl

/-! ### Closedness of a base change depends only on the cospan -/

/-- The two maps on points out of the apex of a 2-commutative square of algebraic stacks over `S`
commute with its two legs: a 2-morphism does not change the induced map on points. -/
private theorem pointsMap_comm_of_twoCommSq {𝒳 𝒴 𝒵 : Stack.AlgebraicStacks.{u, w} B S hS}
    {g : 𝒵 ⟶ 𝒴} {f : 𝒳 ⟶ 𝒴} (P : Bicategory.TwoCommSq g f) (x : points B S hS P.pt) :
    pointsMap B S hS g (pointsMap B S hS P.fst x) =
      pointsMap B S hS f (pointsMap B S hS P.snd x) := by
  have h := pointsMap_eq_of_hom₂ B S hS P.iso.hom
  rw [pointsMap_comp, pointsMap_comp] at h
  exact congrFun h x

/-- **Closedness of a base change is a property of the cospan.** If one 2-fibre product of the
cospan `(g, f)` of algebraic stacks over `S` has closed first projection, then the canonical one
of Stacks 04T2 has too. -/
private theorem isClosed_twoFibreProductSquare_of_isTwoFibreProduct
    {𝒳 𝒴 𝒵 : Stack.AlgebraicStacks.{u, w} B S hS} {g : 𝒵 ⟶ 𝒴} {f : 𝒳 ⟶ 𝒴}
    (P : Bicategory.TwoCommSq g f) (hP : Bicategory.IsTwoFibreProduct P)
    (h : IsClosed B S hS P.fst) :
    IsClosed B S hS (Stack.twoFibreProductSquareAlgebraicStacks B S hS g f).fst :=
  Stack.isClosedMap_pointsMap_fst_congr B S hS P.underlying
    (Stack.twoFibreProductSquareAlgebraicStacks B S hS g f).underlying
    (Stack.isTwoFibreProduct_underlying_algebraicStacks B S hS _ hP)
    (Stack.isTwoFibreProduct_underlying_algebraicStacks B S hS _
      (Stack.isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS g f))
    h

/-- **Base changing twice is base changing once.** The base change of the base change of `f`
along `g` by `k` is closed exactly when the base change of `f` along `k ≫ g` is. -/
private theorem isClosed_baseChange_comp_iff
    {𝒳 𝒴 𝒵 𝒯 : Stack.AlgebraicStacks.{u, w} B S hS}
    (f : 𝒳 ⟶ 𝒴) (g : 𝒵 ⟶ 𝒴) (k : 𝒯 ⟶ 𝒵) :
    IsClosed B S hS (Stack.twoFibreProductSquareAlgebraicStacks B S hS k
        (Stack.twoFibreProductSquareAlgebraicStacks B S hS g f).fst).fst ↔
      IsClosed B S hS
        (Stack.twoFibreProductSquareAlgebraicStacks B S hS (k ≫ g) f).fst := by
  set P := Stack.twoFibreProductSquareAlgebraicStacks B S hS g f with hPdef
  have hP := Stack.isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS g f
  set Q := Stack.twoFibreProductSquareAlgebraicStacks B S hS k P.fst with hQdef
  have hQ := Stack.isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS k P.fst
  have hpaste := Bicategory.isTwoFibreProduct_pasteFst P hP Q hQ
  constructor
  · exact fun h => isClosed_twoFibreProductSquare_of_isTwoFibreProduct B S hS
      (P.pasteFst Q) hpaste h
  · exact fun h => Stack.isClosedMap_pointsMap_fst_congr B S hS
      (Stack.twoFibreProductSquareAlgebraicStacks B S hS (k ≫ g) f).underlying
      (P.pasteFst Q).underlying
      (Stack.isTwoFibreProduct_underlying_algebraicStacks B S hS _
        (Stack.isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS (k ≫ g) f))
      (Stack.isTwoFibreProduct_underlying_algebraicStacks B S hS _ hpaste) h

/-- **Closedness descends to a base change along an embedding.** Let
```text
A --k--> B
|        |
q        F
|        |
C --j--> D
```
commute and be cartesian on elements, with `F` a closed map, `j` continuous and `k` a topological
embedding. Then `q` is a closed map.

A closed `T ⊆ A` is `k ⁻¹' D₀` for some closed `D₀ ⊆ B`, because `k` is an embedding; cartesianness
then identifies `q '' T` with `j ⁻¹' (F '' D₀)`, which is closed. This is the point-set content of
the step of Stacks 0H2A which writes a closed subset of `|𝒳 ×_𝒴 Z|` as the pullback of a closed
subset of `|𝐀ⁿ × 𝒳|`; note that only the embedding property of `k` is used, not the local
closedness of its range. -/
private theorem isClosedMap_of_isEmbedding_of_cartesian {A C D E : Type*}
    [TopologicalSpace A] [TopologicalSpace C] [TopologicalSpace D] [TopologicalSpace E]
    {k : A → C} {q : A → D} {F : C → E} {j : D → E}
    (hk : Topology.IsEmbedding k) (hF : IsClosedMap F) (hj : Continuous j)
    (hcomm : ∀ a, F (k a) = j (q a))
    (hcart : ∀ (c : C) (d : D), F c = j d → ∃ a, k a = c ∧ q a = d) :
    IsClosedMap q := by
  intro T hT
  obtain ⟨D₀, hD₀, hpre⟩ := hk.isInducing.isClosed_iff.1 hT
  have himage : q '' T = j ⁻¹' (F '' D₀) := by
    refine Set.Subset.antisymm ?_ ?_
    · rintro _ ⟨a, ha, rfl⟩
      exact ⟨k a, hpre.symm.subset ha, hcomm a⟩
    · rintro d ⟨c, hc, hcd⟩
      obtain ⟨a, hac, had⟩ := hcart c d hcd
      exact ⟨a, hpre.subset (show k a ∈ D₀ from hac ▸ hc), had⟩
  rw [himage]
  exact (hF _ hD₀).preimage hj

/-- **Closedness of a base change only depends on the 2-isomorphism class of the base.** -/
private theorem isClosed_baseChange_of_iso {𝒳 𝒴 𝒵 : Stack.AlgebraicStacks.{u, w} B S hS}
    (f : 𝒳 ⟶ 𝒴) {g g' : 𝒵 ⟶ 𝒴} (θ : g ≅ g')
    (h : IsClosed B S hS (Stack.twoFibreProductSquareAlgebraicStacks B S hS g f).fst) :
    IsClosed B S hS (Stack.twoFibreProductSquareAlgebraicStacks B S hS g' f).fst :=
  isClosed_twoFibreProductSquare_of_isTwoFibreProduct B S hS
    ((Stack.twoFibreProductSquareAlgebraicStacks B S hS g f).reindexFst θ)
    (Bicategory.isTwoFibreProduct_reindexFst θ
      (Stack.isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS g f)) h

/-! ### Descending closedness along a smooth surjective base change -/

/-- **Closedness descends along an open surjective base change.** If `g : 𝒵 ⟶ 𝒴` is open and
surjective on points and the first projection of a 2-fibre product of `(g, f)` is closed, then
`f` is closed. -/
private theorem isClosed_of_isClosed_fst {𝒳 𝒴 𝒵 : Stack.AlgebraicStacks.{u, w} B S hS}
    {g : 𝒵 ⟶ 𝒴} {f : 𝒳 ⟶ 𝒴} (P : Bicategory.TwoCommSq g f)
    (hP : Bicategory.IsTwoFibreProduct P)
    (hopen : @IsOpenMap _ _ (Stack.pointTopology B S hS 𝒵.val)
      (Stack.pointTopology B S hS 𝒴.val) (pointsMap B S hS g))
    (hsurj : Stack.IsSurjective B S hS g) (hfst : IsClosed B S hS P.fst) :
    IsClosed B S hS f := by
  let _ := Stack.pointTopology B S hS 𝒳.val
  let _ := Stack.pointTopology B S hS 𝒴.val
  let _ := Stack.pointTopology B S hS 𝒵.val
  let _ := Stack.pointTopology B S hS P.pt.val
  exact isClosedMap_of_isClosedMap_comm_of_isOpenMap_surjective
    (p := pointsMap B S hS P.fst) (a := pointsMap B S hS P.snd)
    (q := pointsMap B S hS f) (b := pointsMap B S hS g)
    (pointsMap_comm_of_twoCommSq B S hS P) hopen hsurj
    (Stack.continuous_pointsMap B S hS P.pt.val 𝒳.val P.snd.hom.hom)
    (fun y c hyc => AlgebraicStacks.exists_point_of_isTwoFibreProduct B S hS P hP y c hyc)
    hfst

/-- **Closedness descends along a jointly surjective family of smooth base changes.** If a family
of smooth 1-morphisms `g i : 𝒵 i ⟶ 𝒴` covers the points of `𝒴` and every base change of `f`
along a `g i` is closed, then `f` is closed: each `g i` is open on points by Stacks 06R7, each
base-change square is surjective onto the fibre product of point spaces by Stacks 04XH, and
closedness of a map can be read on an open cover of its target. -/
private theorem isClosed_of_isClosed_smooth_cover
    {𝒳 𝒴 : Stack.AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴)
    {I : Type*} (𝒵 : I → Stack.AlgebraicStacks.{u, w} B S hS) (g : ∀ i, 𝒵 i ⟶ 𝒴)
    (hg : ∀ i, IsSmooth B S hS (g i))
    (hcover : ∀ y : points B S hS 𝒴,
      ∃ (i : I) (z : points B S hS (𝒵 i)), pointsMap B S hS (g i) z = y)
    (hclosed : ∀ i, IsClosed B S hS
      (Stack.twoFibreProductSquareAlgebraicStacks B S hS (g i) f).fst) :
    IsClosed B S hS f := by
  let P : ∀ i, Bicategory.TwoCommSq (g i) f :=
    fun i => Stack.twoFibreProductSquareAlgebraicStacks B S hS (g i) f
  let _ := Stack.pointTopology B S hS 𝒳.val
  let _ := Stack.pointTopology B S hS 𝒴.val
  change IsClosedMap
    (Stack.pointsMap B S hS 𝒳.val.val 𝒳.val.property 𝒴.val.property f.hom.hom)
  refine @isClosedMap_of_isClosedMap_family _ _ _ _ _ _ _
    (fun i => Stack.pointTopology B S hS (P i).pt.val)
    (fun i => Stack.pointTopology B S hS (𝒵 i).val) _
    (fun i => Stack.pointsMap B S hS (P i).pt.val.val (P i).pt.val.property
      𝒳.val.property (P i).snd.hom.hom)
    (fun i => Stack.pointsMap B S hS (𝒵 i).val.val (𝒵 i).val.property
      𝒴.val.property (g i).hom.hom)
    (fun i => Stack.pointsMap B S hS (P i).pt.val.val (P i).pt.val.property
      (𝒵 i).val.property (P i).fst.hom.hom)
    (fun i p => (pointsMap_comm_of_twoCommSq B S hS (P i) p).symm) ?_ ?_ ?_ ?_ ?_
  · intro i x d hxd
    obtain ⟨p, h₁, h₂⟩ := AlgebraicStacks.exists_point_of_isTwoFibreProduct B S hS (P i)
      (Stack.isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS (g i) f) d x hxd.symm
    exact ⟨p, h₂, h₁⟩
  · exact fun i => Stack.continuous_pointsMap B S hS (P i).pt.val 𝒳.val (P i).snd.hom.hom
  · exact fun i => isOpenMap_pointsMap B S hS (g i) (isFlat_of_isSmooth B S hS (g i) (hg i))
      (isLocallyOfFinitePresentation_of_isSmooth B S hS (g i) (hg i))
  · exact hcover
  · exact hclosed

/-! ### Open charts of a scheme of the site -/

section Charts

variable {B S hS}

/-- An affine open of a scheme of the site, as an object of the site over that scheme. -/
private noncomputable def affineChart (U : BigFppfOver B S hS)
    (i : ((BigFppfOver.toScheme B S hS).obj U).affineOpens) : BigFppfOver B S hS :=
  Over.mk (⟨i.1.ι ≫ B.inclusion.map U.hom⟩ :
    B.obj (Scheme.size_lt_of_isOpenImmersion i.1.ι U.left.property) ⟶ B.obj hS)

/-- The inclusion of an affine open of a scheme of the site, as a morphism of the site. -/
private noncomputable def affineChartHom (U : BigFppfOver B S hS)
    (i : ((BigFppfOver.toScheme B S hS).obj U).affineOpens) : affineChart U i ⟶ U :=
  Over.homMk ⟨i.1.ι⟩ (by rfl)

/-- The morphism of schemes underlying the inclusion of an affine open chart is the inclusion of
that open subscheme. -/
private theorem affineChartHom_toScheme (U : BigFppfOver B S hS)
    (i : ((BigFppfOver.toScheme B S hS).obj U).affineOpens) :
    (BigFppfOver.toScheme B S hS).map (affineChartHom U i) = i.1.ι := rfl

/-- An affine open chart of a scheme of the site is affine. -/
private theorem isAffine_affineChart (U : BigFppfOver B S hS)
    (i : ((BigFppfOver.toScheme B S hS).obj U).affineOpens) :
    IsAffine ((BigFppfOver.toScheme B S hS).obj (affineChart U i)) := i.2

/-- The inclusion of an affine open chart is smooth, being an open immersion. -/
private theorem smooth_affineChartHom (U : BigFppfOver B S hS)
    (i : ((BigFppfOver.toScheme B S hS).obj U).affineOpens) :
    Smooth ((BigFppfOver.toScheme B S hS).map (affineChartHom U i)) := by
  rw [affineChartHom_toScheme]
  exact (inferInstance :
    Smooth (i : ((BigFppfOver.toScheme B S hS).obj U).Opens).ι)

end Charts

/-- **The affine charts of a scheme of the site cover the points of the algebraic stack it
represents.** The point space of the algebraic stack of a scheme of the site is that scheme
(`AlgebraicGeometry.Stack.pointsHomeomorphScheme`), naturally in the scheme, and the affine opens
cover the scheme. -/
private theorem exists_affineChart_point (U : BigFppfOver B S hS)
    (z : points B S hS (Stack.schemeStack.{u, w} B S hS U)) :
    ∃ (i : ((BigFppfOver.toScheme B S hS).obj U).affineOpens)
      (y : points B S hS (Stack.schemeStack.{u, w} B S hS (affineChart U i))),
      pointsMap B S hS (Stack.schemeStackMap.{u, w} B S hS (affineChartHom U i)) y = z := by
  let _ := Stack.pointTopology B S hS (Stack.schemeFibredCategory B S hS U)
  let _ : ∀ i : ((BigFppfOver.toScheme B S hS).obj U).affineOpens,
      TopologicalSpace (Stack.points B S hS
        (Stack.schemeFibredCategory B S hS (affineChart U i)).val
        (Stack.schemeFibredCategory B S hS (affineChart U i)).property) :=
    fun i => Stack.pointTopology B S hS (Stack.schemeFibredCategory B S hS (affineChart U i))
  obtain ⟨-, ⟨V₀, hV₀, rfl⟩, hxV₀, -⟩ :=
    ((BigFppfOver.toScheme B S hS).obj U).isBasis_affineOpens.exists_subset_of_mem_open
      (Set.mem_univ (Stack.pointsHomeomorphScheme B S hS U z)) isOpen_univ
  refine ⟨⟨V₀, hV₀⟩, (Stack.pointsHomeomorphScheme B S hS
    (affineChart U ⟨V₀, hV₀⟩)).symm ⟨Stack.pointsHomeomorphScheme B S hS U z, hxV₀⟩, ?_⟩
  refine (Stack.pointsHomeomorphScheme B S hS U).injective ?_
  have hnat := Stack.pointsHomeomorphScheme_naturality B S hS (affineChartHom U ⟨V₀, hV₀⟩)
    ((Stack.pointsHomeomorphScheme B S hS (affineChart U ⟨V₀, hV₀⟩)).symm
      ⟨Stack.pointsHomeomorphScheme B S hS U z, hxV₀⟩)
  exact hnat.trans (congrArg _
    ((Stack.pointsHomeomorphScheme B S hS (affineChart U ⟨V₀, hV₀⟩)).apply_symm_apply _))

/-! ### The two hard implications -/

/-- **Closedness of a base change along a scheme of the site is read on its affine charts.** The
affine opens of the scheme give a jointly surjective family of smooth, hence open, base changes. -/
private theorem isClosed_baseChange_of_forall_affineChart
    {𝒳 𝒴 : Stack.AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴) (T : BigFppfOver B S hS)
    (g : Stack.schemeStack.{u, w} B S hS T ⟶ 𝒴)
    (h : ∀ i, IsClosed B S hS (Stack.twoFibreProductSquareAlgebraicStacks B S hS
      (Stack.schemeStackMap.{u, w} B S hS (affineChartHom T i) ≫ g) f).fst) :
    IsClosed B S hS (Stack.twoFibreProductSquareAlgebraicStacks B S hS g f).fst := by
  refine isClosed_of_isClosed_smooth_cover B S hS
    (Stack.twoFibreProductSquareAlgebraicStacks B S hS g f).fst
    (fun i => Stack.schemeStack.{u, w} B S hS (affineChart T i))
    (fun i => Stack.schemeStackMap.{u, w} B S hS (affineChartHom T i)) (fun i => ?_) ?_
        (fun i => ?_)
  · exact isSmooth_schemeStackMap B S hS _ (smooth_affineChartHom T i)
  · exact exists_affineChart_point.{u, w} B S hS T
  · exact (isClosed_baseChange_comp_iff B S hS f g _).2 (h i)

/-- **From affine charts to all schemes of the site.** If every base change of `f` to an affine
scheme of the site is closed, then so is every base change of `f` to a scheme of the site. -/
private theorem isClosed_baseChange_of_forall_affine
    {𝒳 𝒴 : Stack.AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴)
    (h : ∀ (U : BigFppfOver B S hS), IsAffine ((BigFppfOver.toScheme B S hS).obj U) →
      ∀ (g : Stack.schemeStack.{u, w} B S hS U ⟶ 𝒴),
        IsClosed B S hS (Stack.twoFibreProductSquareAlgebraicStacks B S hS g f).fst)
    (T : BigFppfOver B S hS) (g : Stack.schemeStack.{u, w} B S hS T ⟶ 𝒴) :
    IsClosed B S hS (Stack.twoFibreProductSquareAlgebraicStacks B S hS g f).fst :=
  isClosed_baseChange_of_forall_affineChart B S hS f T g fun i =>
    h (affineChart T i) (isAffine_affineChart T i) _

/-- **From schemes of the site to universal closedness.** Every algebraic stack over `S` has a
smooth surjective chart by a scheme of the site, so closedness of every base change of `f` to a
scheme of the site descends to closedness of every base change of `f`. -/
private theorem universallyClosed_of_forall_schemeStack
    {𝒳 𝒴 : Stack.AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴)
    (h : ∀ (U : BigFppfOver B S hS) (g : Stack.schemeStack.{u, w} B S hS U ⟶ 𝒴),
      IsClosed B S hS (Stack.twoFibreProductSquareAlgebraicStacks B S hS g f).fst) :
    UniversallyClosed B S hS f := by
  intro 𝒵 g
  obtain ⟨U, a, hasm, hasu⟩ := Stack.exists_smooth_surjective_schemeStack.{u, w} B S hS 𝒵
  refine isClosed_of_isClosed_fst B S hS
    (Stack.twoFibreProductSquareAlgebraicStacks B S hS a
      (Stack.twoFibreProductSquareAlgebraicStacks B S hS g f).fst)
    (Stack.isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS a _)
    (isOpenMap_pointsMap_of_isSmooth B S hS a hasm) hasu ?_
  exact (isClosed_baseChange_comp_iff B S hS f g a).2 (h U (a ≫ g))

/-- **Universal closedness descends along a smooth surjective base change.** -/
private theorem universallyClosed_of_baseChange
    {𝒳 𝒴 𝒱 : Stack.AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴) (g : 𝒱 ⟶ 𝒴)
    (hgsu : Stack.IsSurjective B S hS g) (hgsm : IsSmooth B S hS g)
    (h : UniversallyClosed B S hS
      (Stack.twoFibreProductSquareAlgebraicStacks B S hS g f).fst) :
    UniversallyClosed B S hS f := by
  intro 𝒵 k
  set R := Stack.twoFibreProductSquareAlgebraicStacks B S hS k g with hR
  have hRsm : IsSmooth B S hS R.fst :=
    isSmooth_baseChange B S hS g k R
      (Stack.isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS k g) hgsm
  have hRsu : Stack.IsSurjective B S hS R.fst := by
    intro z
    obtain ⟨v, hv⟩ := hgsu (pointsMap B S hS k z)
    obtain ⟨r, hr, -⟩ := AlgebraicStacks.exists_point_of_isTwoFibreProduct B S hS R
      (Stack.isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS k g) z v hv.symm
    exact ⟨r, hr⟩
  refine isClosed_of_isClosed_fst B S hS
    (Stack.twoFibreProductSquareAlgebraicStacks B S hS R.fst
      (Stack.twoFibreProductSquareAlgebraicStacks B S hS k f).fst)
    (Stack.isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS R.fst _)
    (isOpenMap_pointsMap_of_isSmooth B S hS R.fst hRsm) hRsu ?_
  refine (isClosed_baseChange_comp_iff B S hS f k R.fst).2 ?_
  refine isClosed_baseChange_of_iso B S hS f R.iso.symm ?_
  exact (isClosed_baseChange_comp_iff B S hS f g R.snd).1 (h R.pt R.snd)

/-! ### Stacks 0CL3 -/

/-- **Stacks 0CL3.** For a 1-morphism `f : 𝒳 ⟶ 𝒴` of algebraic stacks over `S` the following are
equivalent: `f` is universally closed; every base change of `f` to a scheme of the site is closed
on points; every base change of `f` to an affine scheme of the site is closed on points; and
there is a smooth surjective 1-morphism from the algebraic stack of an algebraic space to `𝒴`
along which the base change of `f` is universally closed. -/
@[stacks 0CL3]
theorem universallyClosed_tfae {𝒳 𝒴 : Stack.AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴) :
    List.TFAE
      [UniversallyClosed B S hS f,
        ∀ (U : BigFppfOver B S hS) (g : Stack.schemeStack.{u, w} B S hS U ⟶ 𝒴),
          IsClosed B S hS (Stack.twoFibreProductSquareAlgebraicStacks B S hS g f).fst,
        ∀ (U : BigFppfOver B S hS), IsAffine ((BigFppfOver.toScheme B S hS).obj U) →
          ∀ (g : Stack.schemeStack.{u, w} B S hS U ⟶ 𝒴),
            IsClosed B S hS (Stack.twoFibreProductSquareAlgebraicStacks B S hS g f).fst,
        ∃ (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)
            (g : Stack.algebraicSpaceStack.{u, w} B S hS F hF ⟶ 𝒴),
          Stack.IsSurjective B S hS g ∧ IsSmooth B S hS g ∧
            UniversallyClosed B S hS
              (Stack.twoFibreProductSquareAlgebraicStacks B S hS g f).fst] := by
  tfae_have 1 → 2 := fun hf U g => hf (Stack.schemeStack.{u, w} B S hS U) g
  tfae_have 2 → 3 := fun h U _ g => h U g
  tfae_have 3 → 1 := fun h =>
    universallyClosed_of_forall_schemeStack B S hS f
      (isClosed_baseChange_of_forall_affine B S hS f h)
  tfae_have 1 → 4 := by
    intro hf
    obtain ⟨U, a, hasm, hasu⟩ := Stack.exists_smooth_surjective_schemeStack.{u, w} B S hS 𝒴
    obtain ⟨e, hesm, hesu⟩ :=
      Stack.exists_smooth_surjective_algebraicSpaceStack_hom.{u, w} B S hS U
    refine ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U, e ≫ a,
      Stack.isSurjective_comp B S hS e a hesu hasu, ?_, ?_⟩
    · exact Stack.isSmooth_comp_of_isRepresentableByAlgebraicSpace B S hS
        (Space.isSmoothLocalOnSourceAndTarget_smooth B S hS)
        (yoneda.obj U) (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U)
        (isAlgebraicSpace_yoneda B S hS U)
        (StacksRepresentableCFG.EquivalenceOver.refl _)
        (PresheafOfCategories.sliceElementsEquivalenceOver U) e a hesm hasm
    · exact universallyClosed_baseChange_of_isTwoFibreProduct B S hS
        (Stack.twoFibreProductSquareAlgebraicStacks B S hS (e ≫ a) f)
        (Stack.isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS (e ≫ a) f) hf
  tfae_have 4 → 1 := by
    rintro ⟨F, hF, g, hgsu, hgsm, h⟩
    exact universallyClosed_of_baseChange B S hS f g hgsu hgsm h
  tfae_finish

/-- **Stacks 0H2A: closedness of a base change descends along an immersion of the base.** Let
`F : 𝒬 ⟶ ℬ` be closed on points and let `ι : 𝒞 ⟶ ℬ` be an immersion of algebraic stacks over `S`.
Then the base change of `F` along `ι` — the map `|𝒬 ×_ℬ 𝒞| → |𝒞|` — is closed on points.

This is the step of the proof of Stacks 0H2A which writes a closed subset of `|𝒳 ×_𝒴 Z|` as the
pullback of a closed subset of `|𝐀ⁿ × 𝒳|` along the immersion `Z ⟶ 𝐀ⁿ_V` of Stacks 04II. The base
change of `ι` is an immersion by Stacks 045C at the immersion property, hence a topological
embedding on points by **Stacks 0H20**; the square is cartesian on points by **Stacks 04XH**; and
`isClosedMap_of_isEmbedding_of_cartesian` concludes. Only the embedding property of Stacks 0H20
is used, not the local closedness of the range. -/
@[stacks 0H2A "closedness of a base change descends along an immersion of the base"]
theorem isClosed_baseChange_of_isImmersion
    {𝒬 𝒞 ℬ : Stack.AlgebraicStacks.{u, w} B S hS} (F : 𝒬 ⟶ ℬ) (ι : 𝒞 ⟶ ℬ)
    (hι : IsImmersion B S hS ι) (hF : IsClosed B S hS F) :
    IsClosed B S hS (Stack.twoFibreProductSquareAlgebraicStacks B S hS ι F).fst := by
  set P := Stack.twoFibreProductSquareAlgebraicStacks B S hS ι F with hPdef
  have hP := Stack.isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS ι F
  let _ := Stack.pointTopology B S hS P.pt.val
  let _ := Stack.pointTopology B S hS 𝒬.val
  let _ := Stack.pointTopology B S hS 𝒞.val
  let _ := Stack.pointTopology B S hS ℬ.val
  refine isClosedMap_of_isEmbedding_of_cartesian
    (k := pointsMap B S hS P.snd) (q := pointsMap B S hS P.fst)
    (F := pointsMap B S hS F) (j := pointsMap B S hS ι)
    (isEmbedding_pointsMap_of_isImmersion B S hS P.snd
      (Stack.AlgebraicStacks.isImmersion_snd_of_isTwoFibreProduct B S hS P hP hι)) hF
    (Stack.continuous_pointsMap B S hS 𝒞.val ℬ.val ι.hom.hom)
    (fun p => (pointsMap_comm_of_twoCommSq B S hS P p).symm) (fun b c h => ?_)
  obtain ⟨p, h₁, h₂⟩ :=
    AlgebraicStacks.exists_point_of_isTwoFibreProduct B S hS P hP c b h.symm
  exact ⟨p, h₂, h₁⟩

/-! ### Affine space over a scheme of the site -/

/-- **Affine `n`-space over a scheme of the site is again a scheme of the site.** Its structure
morphism to that scheme is affine and locally of finite type, hence quasi-compact, so the size
bound of the base carries over. -/
theorem contains_affineSpaceChart (U : BigFppfOver B S hS) (n : ℕ) :
    B.Contains (AffineSpace (ULift.{u} (Fin n)) ((BigFppfOver.toScheme B S hS).obj U)) :=
  Scheme.size_lt_of_locallyOfFiniteType_of_quasiCompact
    (AffineSpace (ULift.{u} (Fin n)) ((BigFppfOver.toScheme B S hS).obj U) ↘
      (BigFppfOver.toScheme B S hS).obj U) U.left.property

/-- Affine `n`-space over a scheme of the site, as an object of the site over `S`. -/
noncomputable def affineSpaceChart (U : BigFppfOver B S hS) (n : ℕ) :
    BigFppfOver B S hS :=
  Over.mk (⟨(AffineSpace (ULift.{u} (Fin n)) ((BigFppfOver.toScheme B S hS).obj U) ↘
      (BigFppfOver.toScheme B S hS).obj U) ≫ B.inclusion.map U.hom⟩ :
    B.obj (contains_affineSpaceChart B S hS U n) ⟶ B.obj hS)

/-- The projection of affine `n`-space over a scheme of the site, as a morphism of the site. -/
noncomputable def affineSpaceChartHom (U : BigFppfOver B S hS) (n : ℕ) :
    affineSpaceChart B S hS U n ⟶ U :=
  Over.homMk ⟨AffineSpace (ULift.{u} (Fin n)) ((BigFppfOver.toScheme B S hS).obj U) ↘
    (BigFppfOver.toScheme B S hS).obj U⟩ (by rfl)

/-- The morphism of schemes underlying the projection of an affine-space chart is the projection
of affine `n`-space. -/
theorem affineSpaceChartHom_toScheme (U : BigFppfOver B S hS) (n : ℕ) :
    (BigFppfOver.toScheme B S hS).map (affineSpaceChartHom B S hS U n) =
      (AffineSpace (ULift.{u} (Fin n)) ((BigFppfOver.toScheme B S hS).obj U) ↘
        (BigFppfOver.toScheme B S hS).obj U) := rfl

/-- **A morphism of the site locally of finite presentation induces a 1-morphism of the
represented algebraic stacks locally of finite presentation.** Local finite presentation is
smooth local on the source-and-target (Stacks 06FC), so the universal smooth-diagram test of
Stacks 06Q2 follows from the existential one, and the latter follows from the relative property
of Stacks 03YK at a represented source and target (Stacks 03XP, part (1)). -/
theorem isLocallyOfFinitePresentation_schemeStackMap {U V : BigFppfOver B S hS} (g : U ⟶ V)
    (hg : LocallyOfFinitePresentation ((BigFppfOver.toScheme B S hS).map g)) :
    IsLocallyOfFinitePresentation B S hS (Stack.schemeStackMap.{u, w} B S hS g) := by
  let P : MorphismProperty ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
    fun _ _ h => Space.IsLocallyOfFinitePresentation B S hS h
  have hsm : Space.IsSmoothLocalOnSourceAndTarget B S hS P :=
    Space.isSmoothLocalOnSourceAndTarget_locallyOfFinitePresentation B S hS
  let _ : (Stack.spaceProperty B S hS P).IsStableUnderBaseChange :=
    Space.isLocallyOfFinitePresentation_isStableUnderBaseChange B S hS
  let _ : (Stack.spaceProperty B S hS P).IsLocalAtTarget
      (Space.Topology.fppf.precoverage.{u, u + 1} B S hS) :=
    Space.isLocallyOfFinitePresentation_isLocalAtTarget_fppf B S hS
  refine (Stack.hasPropertyOnEverySmoothDiagram_iff_some.{u, w} B S hS P hsm
    (Stack.schemeStack.{u, w} B S hS U).property
    (Stack.schemeStack.{u, w} B S hS V).property
    (Stack.schemeStackMap.{u, w} B S hS g).hom).2 ?_
  exact Stack.hasPropertyOnSomeSmoothDiagram_of_hasRelativeProperty.{u, w, u + 1} B S hS P
    (Stack.schemeStack.{u, w} B S hS V).property _
    (Stack.isRepresentableByAlgebraicSpaces_schemeFibredCategoryMap B S hS g)
    (Stack.hasRelativeProperty_schemeFibredCategoryMap.{u, u + 1} B S hS
      (Stack.spaceProperty B S hS P) g
      (Space.isLocallyOfFinitePresentation_yoneda_map B S hS g hg))

/-! ### Stacks 0H2A, the implications out of universal closedness -/

/-- **Stacks 0H2A, (1) implies (2).** If `f` is universally closed then, for every object `Z` of
the site whose scheme is *affine* and every 1-morphism `Stack.schemeStack Z ⟶ 𝒴` which is
*locally of finite presentation*, the map `|𝒳 ×_𝒴 Z| → |Z|` is closed. Neither adjective is
used: the clause is the restriction of universal closedness to those bases. -/
@[stacks 0H2A "(1) implies (2)"]
theorem isClosed_baseChange_affine_isLocallyOfFinitePresentation_of_universallyClosed
    {𝒳 𝒴 : Stack.AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴)
    (hf : UniversallyClosed B S hS f) :
    ∀ (Z : BigFppfOver B S hS), IsAffine ((BigFppfOver.toScheme B S hS).obj Z) →
      ∀ (g : Stack.schemeStack.{u, w} B S hS Z ⟶ 𝒴),
        IsLocallyOfFinitePresentation B S hS g →
          IsClosed B S hS (Stack.twoFibreProductSquareAlgebraicStacks B S hS g f).fst :=
  fun Z _ g _ => hf (Stack.schemeStack.{u, w} B S hS Z) g

/-- **Stacks 0H2A, (1) implies (3).** If `f` is universally closed then there are a scheme `V` of
the site and a smooth surjective 1-morphism `Stack.schemeStack V ⟶ 𝒴` such that, for *every*
`n ≥ 0`, the base change of `f` to affine `n`-space over `V` — the map
`|𝐀^n × (𝒳 ×_𝒴 V)| → |𝐀^n × V|` — is closed.

Any smooth surjective chart of `𝒴` by a scheme of the site serves, and every one of the base
changes is closed because `f` is universally closed. -/
@[stacks 0H2A "(1) implies (3)"]
theorem exists_chart_forall_isClosed_baseChange_affineSpaceChart_of_universallyClosed
    {𝒳 𝒴 : Stack.AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴)
    (hf : UniversallyClosed B S hS f) :
    ∃ (V : BigFppfOver B S hS) (a : Stack.schemeStack.{u, w} B S hS V ⟶ 𝒴),
      Stack.IsSurjective B S hS a ∧ IsSmooth B S hS a ∧
        ∀ n : ℕ, IsClosed B S hS (Stack.twoFibreProductSquareAlgebraicStacks B S hS
          (Stack.schemeStackMap.{u, w} B S hS (affineSpaceChartHom B S hS V n) ≫ a) f).fst := by
  obtain ⟨V, a, hasm, hasu⟩ := Stack.exists_smooth_surjective_schemeStack.{u, w} B S hS 𝒴
  exact ⟨V, a, hasu, hasm, fun n => hf _ _⟩

/-- **Stacks 0H2A, (2) implies (3).** Suppose every base change of `f` to an affine scheme of the
site along a 1-morphism locally of finite presentation is closed. Then the conclusion of (3)
holds for *any* smooth surjective chart `a : Stack.schemeStack V ⟶ 𝒴` of `𝒴` by a scheme of the
site.

Fix `n`. The target of the base change is the stack of affine `n`-space over `V`; its affine
opens cover it and their inclusions are open immersions, hence smooth, so closedness can be read
on that cover. Over one affine open `W` the base change of `f` is the base change along the
composite `W ⟶ 𝐀^n_V ⟶ V ⟶ 𝒴`, whose scheme `W` is affine and which is locally of finite
presentation — the inclusion of an open is, the projection of affine `n`-space is, and `a` is
smooth hence locally of finite presentation by Stacks 0DNP. So (2) applies to it. -/
@[stacks 0H2A "(2) implies (3)"]
theorem exists_chart_forall_isClosed_baseChange_affineSpaceChart_of_isClosed_affine_lfp
    {𝒳 𝒴 : Stack.AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴)
    (h : ∀ (Z : BigFppfOver B S hS), IsAffine ((BigFppfOver.toScheme B S hS).obj Z) →
      ∀ (g : Stack.schemeStack.{u, w} B S hS Z ⟶ 𝒴),
        IsLocallyOfFinitePresentation B S hS g →
          IsClosed B S hS (Stack.twoFibreProductSquareAlgebraicStacks B S hS g f).fst) :
    ∃ (V : BigFppfOver B S hS) (a : Stack.schemeStack.{u, w} B S hS V ⟶ 𝒴),
      Stack.IsSurjective B S hS a ∧ IsSmooth B S hS a ∧
        ∀ n : ℕ, IsClosed B S hS (Stack.twoFibreProductSquareAlgebraicStacks B S hS
          (Stack.schemeStackMap.{u, w} B S hS (affineSpaceChartHom B S hS V n) ≫ a) f).fst := by
  obtain ⟨V, a, hasm, hasu⟩ := Stack.exists_smooth_surjective_schemeStack.{u, w} B S hS 𝒴
  refine ⟨V, a, hasu, hasm, fun n => ?_⟩
  have hlfpa : IsLocallyOfFinitePresentation B S hS a :=
    isLocallyOfFinitePresentation_of_isSmooth B S hS a hasm
  have hlfpπ : IsLocallyOfFinitePresentation B S hS
      (Stack.schemeStackMap.{u, w} B S hS (affineSpaceChartHom B S hS V n)) := by
    refine isLocallyOfFinitePresentation_schemeStackMap B S hS _ ?_
    rw [affineSpaceChartHom_toScheme]
    have : Finite (ULift.{u, 0} (Fin n)) := Finite.of_equiv _ Equiv.ulift.symm
    have hsm : Smooth (𝔸(ULift.{u, 0} (Fin n); (BigFppfOver.toScheme B S hS).obj V) ↘
        (BigFppfOver.toScheme B S hS).obj V) := inferInstance
    exact AlgebraicGeometry.instLocallyOfFinitePresentationOfSmooth (hf := hsm)
  refine isClosed_baseChange_of_forall_affineChart B S hS f (affineSpaceChart B S hS V n) _
    fun i => ?_
  refine h (affineChart (affineSpaceChart B S hS V n) i)
    (isAffine_affineChart (affineSpaceChart B S hS V n) i) _ ?_
  refine isLocallyOfFinitePresentation_comp B S hS _ _ ?_
    (isLocallyOfFinitePresentation_comp B S hS _ _ hlfpπ hlfpa)
  exact isLocallyOfFinitePresentation_of_isSmooth B S hS _
    (isSmooth_schemeStackMap B S hS _
      (smooth_affineChartHom (affineSpaceChart B S hS V n) i))

/-! ### Morphisms of the site as 1-morphisms of the represented algebraic stacks -/

/-- **The 2-Yoneda construction on morphisms of the site is functorial.** The 1-morphism of
represented algebraic stacks induced by a composite of morphisms of the site is the composite of
the induced 1-morphisms.

Both sides are the based functor `CategoryTheory.Over.map` of the composite, read in the
2-category of algebraic stacks: the 1-morphisms and 2-morphisms of a full sub-2-category are
those of the ambient one, so the claim is `CategoryTheory.Over.mapComp_eq` together with the
fact that a based functor is determined by its underlying functor. -/
private theorem schemeStackMap_comp {U V W : BigFppfOver B S hS} (a : U ⟶ V) (b : V ⟶ W) :
    Stack.schemeStackMap.{u, w} B S hS a ≫ Stack.schemeStackMap.{u, w} B S hS b =
      Stack.schemeStackMap.{u, w} B S hS (a ≫ b) :=
  Bicategory.InducedBicategory.hom_ext (Bicategory.InducedBicategory.hom_ext
    (BasedCategory.BasedFunctor.ext' (Over.mapComp_eq a b).symm))

/-- **An immersion of the site induces an immersion of the represented algebraic stacks.** Being
an immersion is stable under base change for morphisms of algebraic spaces and is fppf local on
the target (**Stacks 042U**), so the relative property of Stacks 03YK at the immersion property
of Stacks 02YU holds for the induced 1-morphism as soon as it holds for the morphism of
representable algebraic spaces that the morphism of the site induces, which is Stacks 03XP,
part (1). -/
theorem isImmersion_schemeStackMap {U V : BigFppfOver B S hS} (g : U ⟶ V)
    (hg : AlgebraicGeometry.IsImmersion ((BigFppfOver.toScheme B S hS).map g)) :
    IsImmersion B S hS (Stack.schemeStackMap.{u, w} B S hS g) := by
  let _ : (Space.immersionProperty B S hS).IsLocalAtTarget
      (Space.Topology.fppf.precoverage.{u, u + 1} B S hS) :=
    Space.isImmersion_isLocalAtTarget_fppf.{u, u + 1} B S hS
  refine ⟨Stack.isRepresentableByAlgebraicSpaces_schemeFibredCategoryMap B S hS g, ?_⟩
  exact Stack.hasRelativeProperty_schemeFibredCategoryMap.{u, u + 1} B S hS
    (Space.immersionProperty B S hS) g
    ((Space.presheaf_yoneda_map_iff B S hS
      (P := @AlgebraicGeometry.IsImmersion.{u}) inferInstance g).2 hg)

/-- A morphism of schemes from a scheme of the site to affine `n`-space over another scheme of
the site, compatible with the two structure morphisms to `S`, as a morphism of the site. -/
noncomputable def affineSpaceChartLift {Z W : BigFppfOver B S hS} {n : ℕ}
    (i : (BigFppfOver.toScheme B S hS).obj Z ⟶
      AffineSpace (ULift.{u} (Fin n)) ((BigFppfOver.toScheme B S hS).obj W))
    (hi : i ≫ (AffineSpace (ULift.{u} (Fin n)) ((BigFppfOver.toScheme B S hS).obj W) ↘
        (BigFppfOver.toScheme B S hS).obj W) ≫ B.inclusion.map W.hom =
      B.inclusion.map Z.hom) :
    Z ⟶ affineSpaceChart B S hS W n :=
  Over.homMk (ObjectProperty.homMk i) (by apply ObjectProperty.hom_ext; exact hi)

/-- The morphism of schemes underlying `AlgebraicGeometry.Stack.AlgebraicStacks`
`.affineSpaceChartLift` is the morphism of schemes it was built from. -/
theorem affineSpaceChartLift_toScheme {Z W : BigFppfOver B S hS} {n : ℕ}
    (i : (BigFppfOver.toScheme B S hS).obj Z ⟶
      AffineSpace (ULift.{u} (Fin n)) ((BigFppfOver.toScheme B S hS).obj W))
    (hi : i ≫ (AffineSpace (ULift.{u} (Fin n)) ((BigFppfOver.toScheme B S hS).obj W) ↘
        (BigFppfOver.toScheme B S hS).obj W) ≫ B.inclusion.map W.hom =
      B.inclusion.map Z.hom) :
    (BigFppfOver.toScheme B S hS).map (affineSpaceChartLift B S hS i hi) = i := rfl

/-! ### Stacks 0H2A, from affine space to a quasi-affine base locally of finite type -/

/-- **Stacks 0H2A, the step of (3) implies (2) at a target represented by a scheme.** Let
`f : 𝒳 ⟶ Stack.schemeStack W` be a 1-morphism of algebraic stacks over `S` whose base change to
affine `n`-space over `W` is closed on points for every `n ≥ 0`. Then for every morphism
`p : Z ⟶ W` of the site whose source scheme is quasi-affine and which is locally of finite type,
the base change of `f` along the 1-morphism that `p` induces is closed on points.

By **Stacks 04II** such a `Z` immerses over `W` into affine `n`-space over `W` for some `n`. That
immersion of schemes induces an immersion of the represented algebraic stacks, and closedness of
a base change descends along an immersion of the base. -/
@[stacks 0H2A "(3) implies (2), the step at a target represented by a scheme, stated at the
hypotheses of Tag 04II: a quasi-affine source and a morphism locally of finite type"]
theorem isClosed_baseChange_schemeStackMap_of_forall_isClosed_baseChange_affineSpaceChart
    {𝒳 : Stack.AlgebraicStacks.{u, w} B S hS} {W : BigFppfOver B S hS}
    (f : 𝒳 ⟶ Stack.schemeStack.{u, w} B S hS W)
    (h : ∀ n : ℕ, IsClosed B S hS (Stack.twoFibreProductSquareAlgebraicStacks B S hS
      (Stack.schemeStackMap.{u, w} B S hS (affineSpaceChartHom B S hS W n)) f).fst)
    {Z : BigFppfOver B S hS} (p : Z ⟶ W)
    (hZ : ((BigFppfOver.toScheme B S hS).obj Z).IsQuasiAffine)
    (hp : LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map p)) :
    IsClosed B S hS (Stack.twoFibreProductSquareAlgebraicStacks B S hS
      (Stack.schemeStackMap.{u, w} B S hS p) f).fst := by
  obtain ⟨n, i, hi, hcomp⟩ :=
    exists_immersion_affineSpace ((BigFppfOver.toScheme B S hS).map p)
  obtain ⟨ι, hι⟩ : ∃ ι : Z ⟶ affineSpaceChart B S hS W n,
      (BigFppfOver.toScheme B S hS).map ι = i := by
    refine ⟨affineSpaceChartLift B S hS i ?_, affineSpaceChartLift_toScheme B S hS i _⟩
    rw [← Category.assoc, hcomp]
    exact (Functor.map_comp B.inclusion p.left W.hom).symm.trans
      (congrArg B.inclusion.map (Over.w p))
  have hιp : ι ≫ affineSpaceChartHom B S hS W n = p :=
    BigFppfOver.map_toScheme_injective B S hS
      (show (BigFppfOver.toScheme B S hS).map (ι ≫ affineSpaceChartHom B S hS W n) =
          (BigFppfOver.toScheme B S hS).map p by
        rw [Functor.map_comp, hι, affineSpaceChartHom_toScheme]
        exact hcomp)
  have hclosed := isClosed_baseChange_of_isImmersion B S hS
    (Stack.twoFibreProductSquareAlgebraicStacks B S hS
      (Stack.schemeStackMap.{u, w} B S hS (affineSpaceChartHom B S hS W n)) f).fst
    (Stack.schemeStackMap.{u, w} B S hS ι)
    (isImmersion_schemeStackMap.{u, w} B S hS ι (by rw [hι]; exact hi)) (h n)
  rw [← hιp, ← schemeStackMap_comp]
  exact (isClosed_baseChange_comp_iff B S hS f
    (Stack.schemeStackMap.{u, w} B S hS (affineSpaceChartHom B S hS W n))
    (Stack.schemeStackMap.{u, w} B S hS ι)).1 hclosed

/-! ### Stacks 0H2A, reducing clause (2) to a target represented by a scheme -/

/-- **Clause (2) of Stacks 0H2A is inherited by a base change along a 1-morphism locally of
finite presentation.** Suppose every base change of `f : 𝒳 ⟶ 𝒴` to an affine scheme of the site
along a 1-morphism locally of finite presentation is closed on points, and let `b : 𝒴' ⟶ 𝒴` be
locally of finite presentation. Then the same holds for the base change of `f` along `b`: a
1-morphism `Stack.schemeStack Z ⟶ 𝒴'` locally of finite presentation composes with `b` to one
locally of finite presentation, and base changing twice is base changing once. -/
@[stacks 0H2A "clause (2) is inherited by a base change along a 1-morphism locally of finite
presentation"]
theorem isClosed_baseChange_affine_isLocallyOfFinitePresentation_baseChange
    {𝒳 𝒴 𝒴' : Stack.AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴) (b : 𝒴' ⟶ 𝒴)
    (hb : IsLocallyOfFinitePresentation B S hS b)
    (h : ∀ (Z : BigFppfOver B S hS), IsAffine ((BigFppfOver.toScheme B S hS).obj Z) →
      ∀ (g : Stack.schemeStack.{u, w} B S hS Z ⟶ 𝒴), IsLocallyOfFinitePresentation B S hS g →
        IsClosed B S hS (Stack.twoFibreProductSquareAlgebraicStacks B S hS g f).fst)
    (Z : BigFppfOver B S hS) (hZ : IsAffine ((BigFppfOver.toScheme B S hS).obj Z))
    (g : Stack.schemeStack.{u, w} B S hS Z ⟶ 𝒴') (hg : IsLocallyOfFinitePresentation B S hS g) :
    IsClosed B S hS (Stack.twoFibreProductSquareAlgebraicStacks B S hS g
      (Stack.twoFibreProductSquareAlgebraicStacks B S hS b f).fst).fst :=
  (isClosed_baseChange_comp_iff B S hS f b g).2
    (h Z hZ (g ≫ b) (isLocallyOfFinitePresentation_comp B S hS g b hg hb))

/-- **Stacks 0H2A, the reduction of (2) implies (1) to a target represented by a scheme.** If
clause (2) implies universal closedness whenever the target is the algebraic stack of a scheme of
the site, then it implies universal closedness for an arbitrary target.

Every algebraic stack over `S` has a smooth surjective chart by a scheme of the site, universal
closedness descends along it, and it is locally of finite presentation by Stacks 0DNP, so clause
(2) for `f` gives clause (2) for the base change of `f` to that chart. -/
@[stacks 0H2A "(2) implies (1), the reduction to a target represented by a scheme; the
remaining input is Tag 0H29 for algebraic stacks, carried as `hred`"]
theorem universallyClosed_of_forall_schemeStack_target_of_isClosed_affine_lfp
    (hred : ∀ (V : BigFppfOver B S hS) (𝒲 : Stack.AlgebraicStacks.{u, w} B S hS)
      (f' : 𝒲 ⟶ Stack.schemeStack.{u, w} B S hS V),
        (∀ (Z : BigFppfOver B S hS), IsAffine ((BigFppfOver.toScheme B S hS).obj Z) →
          ∀ (g : Stack.schemeStack.{u, w} B S hS Z ⟶ Stack.schemeStack.{u, w} B S hS V),
            IsLocallyOfFinitePresentation B S hS g →
              IsClosed B S hS (Stack.twoFibreProductSquareAlgebraicStacks B S hS g f').fst) →
        UniversallyClosed B S hS f')
    {𝒳 𝒴 : Stack.AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴)
    (h : ∀ (Z : BigFppfOver B S hS), IsAffine ((BigFppfOver.toScheme B S hS).obj Z) →
      ∀ (g : Stack.schemeStack.{u, w} B S hS Z ⟶ 𝒴), IsLocallyOfFinitePresentation B S hS g →
        IsClosed B S hS (Stack.twoFibreProductSquareAlgebraicStacks B S hS g f).fst) :
    UniversallyClosed B S hS f := by
  obtain ⟨V, a, hasm, hasu⟩ := Stack.exists_smooth_surjective_schemeStack.{u, w} B S hS 𝒴
  refine universallyClosed_of_baseChange B S hS f a hasu hasm (hred V _ _ ?_)
  exact fun Z hZ g hg =>
    isClosed_baseChange_affine_isLocallyOfFinitePresentation_baseChange B S hS f a
      (isLocallyOfFinitePresentation_of_isSmooth B S hS a hasm) h Z hZ g hg

end AlgebraicGeometry.Stack.AlgebraicStacks

end
