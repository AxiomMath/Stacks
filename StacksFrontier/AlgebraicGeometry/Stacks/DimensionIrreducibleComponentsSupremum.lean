module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.DimensionIrreducibleComponents
public import StacksFrontier.AlgebraicGeometry.Stacks.DimensionSchemeChart
public import StacksFrontier.AlgebraicGeometry.Stacks.DimensionSchemeTheoreticImage
public import StacksFrontier.AlgebraicGeometry.Stacks.ReducedClosedSubstackExistence
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalPropertyAtlasBridges
public import StacksFrontier.Topology.Dimension.LocalDimensionComponents

/-!
# Stacks 0DRZ: the dimension at a point is the supremum over the components through it

**Stacks 0DRZ** says that for a locally Noetherian algebraic stack `𝒳` over `S` and a point
`x ∈ |𝒳|`,

`dim_x(𝒳) = sup_𝒯 dim_x(𝒯)`,

the supremum running over the irreducible components `𝒯` of `|𝒳|` through `x`, each endowed with
its induced reduced structure. This file proves it with no hypotheses beyond the source's.

## Main results

* `AlgebraicGeometry.Space.topologicalKrullDimAt_le_dimensionAtPoint_of_isImmersion`: along an
  immersion `V ⟶ W₀` into the algebraic space of a scheme, the local Krull dimension of a set of
  points of `W₀` covered by `|V|` is at most the dimension of `V` at a point over it.
* `AlgebraicGeometry.Stack.exists_mem_irreducibleComponents_topologicalKrullDimAt_eq_of_isSmooth`
  is the middle equality `dim_u(U) = sup_T dim_u(T)` of **Stacks 0DS0** at a smooth scheme chart,
  in the form its proof uses it: the supremum is attained at one irreducible component.
* `AlgebraicGeometry.Stack.exists_dimensionAtPoint_le_of_isClosedImmersion_of_image_subset`: the
  reverse inequality of **Stacks 0DS0** along a closed immersion `𝒵 ⟶ 𝒳` whose image contains the
  image of a set of points of a smooth chart on which the chart's local dimension is attained.
* `AlgebraicGeometry.Stack.dimensionAtPoint_eq_sSup_irreducibleComponents` is **Stacks 0DRZ**.
* `AlgebraicGeometry.Stack.exists_dimensionAtPoint_mem_componentDimensionsAt`: every irreducible
  component through `x`, with its reduced induced structure, contributes to that supremum.

## Implementation notes

The right-hand side is `sSup` of `AlgebraicGeometry.Stack.componentDimensionsAt`
(`StacksFrontier/AlgebraicGeometry/Stacks/DimensionIrreducibleComponents.lean`), the set of values
`dim_t(𝒯)` at points `t` over `x` of the reduced closed substacks `𝒯 ⟶ 𝒳` whose points are an
irreducible component of `|𝒳|` through `x`; by the uniqueness half of **Stacks 0509** each
component carries at most one such substack, and by its existence half
(`AlgebraicGeometry.Stack.exists_isClosedSubstack_isReducedStack_range_pointsMap_eq`) exactly one,
so this is the source's family of values. The inequality `≤ dim_x(𝒳)` is Stacks 0DRY
(`AlgebraicGeometry.Stack.sSup_componentDimensionsAt_le`).

The reverse inequality follows the source. Choose a smooth surjective chart `f : U ⟶ 𝒳` by a
scheme and `u ∈ U` over `x`, and an irreducible component `T'` of `U` through `u` with
`dim_u(T') = dim_u(U)`. The closure `T` of the image of `T'` is an irreducible component of `|𝒳|`
through `x` (Stacks 0DR5); let `𝒯` be its reduced induced closed substack (Stacks 0509). The
source then writes `dim_x(𝒯) = dim_u(T') - dim_u(T'_x)` and compares fibres; here the comparison
is made with the chart `V = 𝒯 ×_𝒳 U ⟶ 𝒯` of `𝒯` instead of with `T'`, which need carry no chart
structure: `V ⟶ U` is a closed immersion whose image contains `T'`, so
`dim_u(U) = dim_u(T') ≤ dim_v(V)`, and the relative dimensions of the two charts agree by
Stacks 0DRN, exactly as in the proof of Stacks 0DRY
(`AlgebraicGeometry.Stack.dimensionAtPoint_le_of_isClosedImmersion`). This gives
`dim_x(𝒳) ≤ dim_t(𝒯)` for a point `t` of `𝒯` over `x`, and `dim_t(𝒯)` is one of the values in the
supremum.

## References

* [Stacks Project, Tag 03H4](https://stacks.math.columbia.edu/tag/03H4)
* [Stacks Project, Tag 04N5](https://stacks.math.columbia.edu/tag/04N5)
* [Stacks Project, Tag 04XH](https://stacks.math.columbia.edu/tag/04XH)
* [Stacks Project, Tag 0509](https://stacks.math.columbia.edu/tag/0509)
* [Stacks Project, Tag 0AFN](https://stacks.math.columbia.edu/tag/0AFN)
* [Stacks Project, Tag 0DR5](https://stacks.math.columbia.edu/tag/0DR5)
* [Stacks Project, Tag 0DRN](https://stacks.math.columbia.edu/tag/0DRN)
* [Stacks Project, Tag 0DRP](https://stacks.math.columbia.edu/tag/0DRP)
* [Stacks Project, Tag 0DRY](https://stacks.math.columbia.edu/tag/0DRY)
* [Stacks Project, Tag 0DRZ](https://stacks.math.columbia.edu/tag/0DRZ)
* [Stacks Project, Tag 0DS0](https://stacks.math.columbia.edu/tag/0DS0)
-/

@[expose] public section

open CategoryTheory

universe u w

namespace AlgebraicGeometry.Space

/-- **The local dimension of a scheme along the image of an immersion is bounded by the source.**
Let `φ : V ⟶ W₀` be an immersion from an algebraic space to the algebraic space represented by a
scheme `W₀` of the site, and let `A ⊆ W₀` be a set of points of the scheme lying in the image of
`|V|`. If `v ∈ |V|` has its image in `A`, then the local Krull dimension of the subspace `A` at
that image is at most the dimension of Stacks 04N5 of `V` at `v`.

The base change of `φ` along the identity of `W₀` is an immersion of schemes `j : R ⟶ W₀` with
`R` an étale chart of `V`, so the dimension of `V` at `v` is the local Krull dimension of `R` at a
point over `v` (Stacks 04N5). Every point of `A` lifts to `R` (Stacks 03H4), so `A` embeds in `R`
through the topological embedding `j`, and the local Krull dimension does not rise along an
inducing map. -/
theorem topologicalKrullDimAt_le_dimensionAtPoint_of_isImmersion
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hV : IsAlgebraicSpace B S hS V)
    {W₀ : BigFppfOver B S hS} (φ : V ⟶ yoneda.obj W₀) (hφ : IsImmersion B S hS φ)
    (A : Set ((BigFppfOver.toScheme B S hS).obj W₀))
    (hA : A ⊆ pointsToScheme B S hS W₀ '' Set.range (pointsMap B S hS V φ))
    (v : points B S hS V) (hv : pointsToScheme B S hS W₀ (pointsMap B S hS V φ v) ∈ A) :
    topologicalKrullDimAt A ⟨_, hv⟩ ≤ dimensionAtPoint B S hS V hV v := by
  classical
  set R := hφ.rep.pullback (𝟙 (yoneda.obj W₀))
  set j := hφ.rep.snd (𝟙 (yoneda.obj W₀))
  have hsq : IsPullback (hφ.rep.fst (𝟙 (yoneda.obj W₀))) (yoneda.map j) φ
      (𝟙 (yoneda.obj W₀)) :=
    hφ.rep.isPullback (𝟙 (yoneda.obj W₀))
  have hci : AlgebraicGeometry.IsImmersion ((BigFppfOver.toScheme B S hS).map j) :=
    hφ.property_snd (𝟙 (yoneda.obj W₀))
  have hid : IsEtale B S hS (𝟙 (yoneda.obj W₀)) := fun _ _ h => by simpa using h
  have hEt := (isEtale_iff_presheaf_of_yoneda B S hS (hφ.rep.fst (𝟙 (yoneda.obj W₀)))).1
    (isEtale_of_isPullback_yoneda B S hS hsq.flip hid)
  have hlift : ∀ v' : points B S hS V, ∃ r : FieldValuedPoint B S hS (yoneda.obj R),
      pointsMap B S hS (yoneda.obj R) (hφ.rep.fst (𝟙 (yoneda.obj W₀)))
          (r.class B S hS (yoneda.obj R)) = v' ∧
        (BigFppfOver.toScheme B S hS).map j (schemePoint B S hS R r) =
          pointsToScheme B S hS W₀ (pointsMap B S hS V φ v') := by
    intro v'
    obtain ⟨w, hw₁, hw₂⟩ := exists_point_of_isPullback_presheaf B S hS hsq v'
      (pointsMap B S hS V φ v') (by rw [pointsMap_id]; rfl)
    obtain ⟨r, rfl⟩ := Quot.exists_rep w
    refine ⟨r, hw₁, ?_⟩
    rw [← schemePoint_map_yoneda, ← hw₂]
    rfl
  obtain ⟨r, hr₁, hr₂⟩ := hlift v
  rw [dimensionAtPoint_eq_of_etale_chart B S hS V hV v R _ hEt r hr₁]
  have he := ((BigFppfOver.toScheme B S hS).map j).isEmbedding
  have hAR : ∀ a ∈ A, ∃ y, (BigFppfOver.toScheme B S hS).map j y = a := by
    rintro a ha
    obtain ⟨_, ⟨v', rfl⟩, rfl⟩ := hA ha
    obtain ⟨r', -, hr'⟩ := hlift v'
    exact ⟨_, hr'⟩
  let g : A → (BigFppfOver.toScheme B S hS).obj R := fun a => (hAR a.1 a.2).choose
  have hg : (BigFppfOver.toScheme B S hS).map j ∘ g = Subtype.val :=
    funext fun a => (hAR a.1 a.2).choose_spec
  have hgi : Topology.IsInducing g := by
    refine (he.isInducing.of_comp_iff).1 ?_
    rw [hg]
    exact Topology.IsInducing.subtypeVal
  have hgv : g ⟨_, hv⟩ = schemePoint B S hS R r :=
    he.injective ((hAR _ hv).choose_spec.trans hr₂.symm)
  rw [← hgv]
  exact Stacks.AlgebraicGeometry.LimitFibreDimensionBound.topologicalKrullDimAt_le_of_isInducing
    hgi _

end AlgebraicGeometry.Space

namespace AlgebraicGeometry.Stack

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 0DS0, the attainment of `dim_u(U)` on an irreducible component of the chart.** Let
`f : U ⟶ 𝒳` be a smooth 1-morphism from the algebraic stack of a scheme `U` of the site to a
locally Noetherian algebraic stack, and let `u ∈ U`. Then some irreducible component `T'` of `U`
through `u` has `dim_u(T') = dim_u(U)`, which is the middle equality `dim_u(U) = sup_T dim_u(T)`
of **Stacks 0DS0** in the form its proof uses it.

The chart is locally Noetherian as a topological space by
`AlgebraicGeometry.Stack.AlgebraicStacks.isLocallyNoetherianSpace_of_isSmooth`, so `u` has a
Noetherian open neighbourhood and the attainment is the purely topological
`exists_mem_irreducibleComponents_topologicalKrullDimAt_eq`. -/
theorem exists_mem_irreducibleComponents_topologicalKrullDimAt_eq_of_isSmooth
    (𝒳 : AlgebraicStacks.{u, w} B S hS)
    (h𝒳 : IsLocallyNoetherianStack.{u, w} B S hS 𝒳)
    (U : BigFppfOver B S hS) (f : schemeStack.{u, w} B S hS U ⟶ 𝒳)
    (hf : AlgebraicStacks.IsSmooth B S hS f)
    (u : (BigFppfOver.toScheme B S hS).obj U) :
    ∃ T' : Set ((BigFppfOver.toScheme B S hS).obj U),
      ∃ _ : T' ∈ irreducibleComponents ((BigFppfOver.toScheme B S hS).obj U),
      ∃ huT' : u ∈ T',
        topologicalKrullDimAt ((BigFppfOver.toScheme B S hS).obj U) u =
          topologicalKrullDimAt ↥T' ⟨u, huT'⟩ := by
  obtain ⟨N, hNopen, huN, hNnoeth⟩ :=
    AlgebraicStacks.isLocallyNoetherianSpace_of_isSmooth B S hS U 𝒳 h𝒳 f hf u
  have := hNnoeth
  obtain ⟨T', hT', huT', hdim⟩ :=
    exists_mem_irreducibleComponents_topologicalKrullDimAt_eq hNopen huN
  exact ⟨T', hT', huT', hdim.symm⟩

/-- **The reverse inequality of Stacks 0DS0 along a closed immersion.** Let `i : 𝒵 ⟶ 𝒳` be a
closed immersion of locally Noetherian algebraic stacks over `S`, let `f : U ⟶ 𝒳` be a smooth
1-morphism from the algebraic stack of a scheme `U` of the site, and let `A ⊆ U` be a set of points
whose image in `|𝒳|` lies in the image of `|𝒵|`. If `u ∈ A` and the local Krull dimension of `U`
at `u` is attained on `A`, then some point `z ∈ |𝒵|` over `f(u)` has `dim_{f(u)}(𝒳) ≤ dim_z(𝒵)`.

This is the argument of Stacks 0DRY run backwards. With `V = 𝒵 ×_𝒳 U`, an algebraic space with a
closed immersion `V ⟶ U`, the smooth dimension formula of Stacks 0DRP and the equality of relative
dimensions of Stacks 0DRN give `dim_z(𝒵) + c = dim_v(V)` and `dim_{f(u)}(𝒳) + c = dim_u(U)` for one
finite integer `c`; and `dim_u(U) ≤ dim_u(A) ≤ dim_v(V)` because every point of `A` lies in the
image of `V` (Stacks 04XH), by
`AlgebraicGeometry.Space.topologicalKrullDimAt_le_dimensionAtPoint_of_isImmersion`. -/
theorem exists_dimensionAtPoint_le_of_isClosedImmersion_of_image_subset
    {𝒵 𝒳 : AlgebraicStacks.{u, w} B S hS} (i : 𝒵 ⟶ 𝒳)
    (hi : AlgebraicStacks.IsClosedImmersion B S hS i)
    (h𝒵 : IsLocallyNoetherianStack.{u, w} B S hS 𝒵)
    (h𝒳 : IsLocallyNoetherianStack.{u, w} B S hS 𝒳)
    (U : BigFppfOver B S hS) (f : schemeStack.{u, w} B S hS U ⟶ 𝒳)
    (hf : AlgebraicStacks.IsSmooth B S hS f)
    (A : Set ((BigFppfOver.toScheme B S hS).obj U))
    (hA : AlgebraicStacks.chartPointMap B S hS U 𝒳 f '' A ⊆
      Set.range (pointsMap B S hS 𝒵.val.val 𝒵.val.property 𝒳.val.property i.hom.hom))
    (u : (BigFppfOver.toScheme B S hS).obj U) (hu : u ∈ A)
    (hdim : topologicalKrullDimAt ((BigFppfOver.toScheme B S hS).obj U) u ≤
      topologicalKrullDimAt ↥A ⟨u, hu⟩) :
    ∃ z : points B S hS 𝒵.val.val 𝒵.val.property,
      pointsMap B S hS 𝒵.val.val 𝒵.val.property 𝒳.val.property i.hom.hom z =
          AlgebraicStacks.chartPointMap B S hS U 𝒳 f u ∧
        dimensionAtPoint B S hS 𝒳 h𝒳 (AlgebraicStacks.chartPointMap B S hS U 𝒳 f u) ≤
          dimensionAtPoint B S hS 𝒵 h𝒵 z := by
  classical
  have hW := isAlgebraicSpace_yoneda B S hS U
  obtain ⟨a, hsma, hapt⟩ :=
    exists_smooth_algebraicSpaceStack_hom_pointsMap_eq.{u, w} B S hS 𝒳 U f hf
  have hchart : ∀ w : (BigFppfOver.toScheme B S hS).obj U,
      AlgebraicStacks.chartPointMap B S hS U 𝒳 f w =
        pointsMap B S hS (fibredCategory B S hS (yoneda.obj U)).val
          (fibredCategory B S hS (yoneda.obj U)).property 𝒳.val.property a.hom.hom
          (stackPointOfSpacePoint B S hS (yoneda.obj U)
            ((Space.pointsEquivScheme B S hS U).symm w)) := fun w => by
    rw [hapt]
    exact (congrArg _ ((Space.pointsEquivScheme B S hS U).apply_symm_apply w).symm).trans
      (chartPointMap_pointsToScheme B S hS 𝒳 U f _)
  set q := (Space.pointsEquivScheme B S hS U).symm u
  have hqu : Space.pointsToScheme B S hS U q = u :=
    (Space.pointsEquivScheme B S hS U).apply_symm_apply u
  obtain ⟨z, hz⟩ := hA ⟨u, hu, rfl⟩
  have hzx : pointsMap B S hS (fibredCategory B S hS (yoneda.obj U)).val
      (fibredCategory B S hS (yoneda.obj U)).property 𝒳.val.property a.hom.hom
      (stackPointOfSpacePoint B S hS (yoneda.obj U) q) =
        pointsMap B S hS 𝒵.val.val 𝒵.val.property 𝒳.val.property i.hom.hom z := by
    rw [← hchart, hz]
  have hfta := AlgebraicStacks.isLocallyOfFiniteType_of_isSmooth B S hS a hsma
  have h𝒰 : IsLocallyNoetherianStack.{u, w} B S hS
      (algebraicSpaceStack.{u, w} B S hS (yoneda.obj U) hW) :=
    AlgebraicStacks.isLocallyNoetherian_of_isLocallyOfFiniteType B S hS a hfta h𝒳
  have hQ := isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS i a
  have hQc : Bicategory.IsTwoFibreProduct
      (twoFibreProductSquareAlgebraicStacks B S hS i a).underlying :=
    CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1}
      i.hom a.hom
  have hsmfst : AlgebraicStacks.IsSmooth B S hS
      (twoFibreProductSquareAlgebraicStacks B S hS i a).fst :=
    AlgebraicStacks.isSmooth_baseChange B S hS a i
      (twoFibreProductSquareAlgebraicStacks B S hS i a) hQ hsma
  have hftfst := AlgebraicStacks.isLocallyOfFiniteType_of_isSmooth B S hS _ hsmfst
  have hQN : IsLocallyNoetherianStack.{u, w} B S hS
      (twoFibreProductSquareAlgebraicStacks B S hS i a).pt :=
    AlgebraicStacks.isLocallyNoetherian_of_isLocallyOfFiniteType B S hS _ hftfst h𝒵
  obtain ⟨V, hV, ⟨eV⟩⟩ := isRepresentableByAlgebraicSpace_of_isTwoFibreProduct.{u, u, u + 1}
    B S hS 𝒵.val 𝒳.val (algebraicSpaceStack.{u, w} B S hS (yoneda.obj U) hW).val i.hom a.hom
    (twoFibreProductSquareAlgebraicStacks B S hS i a).underlying.swap
    (Bicategory.isTwoFibreProduct_swap hQc) hi.1
    (isRepresentableByAlgebraicSpace_fibredCategory B S hS (yoneda.obj U) hW)
  let φ := representingMap B S hS (twoFibreProductSquareAlgebraicStacks B S hS i a).pt.val
    (algebraicSpaceStack.{u, w} B S hS (yoneda.obj U) hW).val V (yoneda.obj U) eV
    (StacksRepresentableCFG.EquivalenceOver.refl _)
    (twoFibreProductSquareAlgebraicStacks B S hS i a).snd.hom
  let : (Space.immersionProperty B S hS).IsLocalAtTarget
      (Space.Topology.fppf.precoverage.{u, u} B S hS) :=
    Space.isImmersion_isLocalAtTarget_fppf B S hS
  have himm : Space.IsImmersion B S hS φ :=
    prop_representingMap_of_hasRelativeProperty B S hS (Space.immersionProperty B S hS)
      i.hom hi.1
      ((isImmersion_iff_hasRelativeProperty B S hS i.hom hi.1).1
        (fun U' y hy F hF he =>
          Space.isImmersion_of_isClosedImmersion B S hS (hi.2 U' y hy F hF he)))
      (algebraicSpaceStack.{u, w} B S hS (yoneda.obj U) hW).val a.hom
      (twoFibreProductSquareAlgebraicStacks B S hS i a).underlying.swap
      (Bicategory.isTwoFibreProduct_swap hQc) V (yoneda.obj U) hV hW eV
      (StacksRepresentableCFG.EquivalenceOver.refl _)
  -- a point of `V` whose image in the 2-fibre product lies over `q` maps to `q` along `φ`
  have hφpt : ∀ (v' : Space.points B S hS V) (q' : Space.points B S hS (yoneda.obj U)),
      pointsMap B S hS (twoFibreProductSquareAlgebraicStacks B S hS i a).pt.val.val
          (twoFibreProductSquareAlgebraicStacks B S hS i a).pt.val.property
          (fibredCategory B S hS (yoneda.obj U)).property
          (twoFibreProductSquareAlgebraicStacks B S hS i a).snd.hom.hom
          (spacePointMap B S hS V (twoFibreProductSquareAlgebraicStacks B S hS i a).pt.val
            (representingEquivalence B S hS V
              (twoFibreProductSquareAlgebraicStacks B S hS i a).pt.val eV).functor v') =
        stackPointOfSpacePoint B S hS (yoneda.obj U) q' →
      Space.pointsMap B S hS V φ v' = q' := by
    intro v' q' h
    refine (bijective_spacePointMap_representing B S hS (yoneda.obj U)
      (fibredCategory B S hS (yoneda.obj U))
      (StacksRepresentableCFG.EquivalenceOver.refl _)).injective ?_
    rw [spacePointMap_representing_naturality B S hS V (yoneda.obj U)
      (twoFibreProductSquareAlgebraicStacks B S hS i a).pt.val
      (algebraicSpaceStack.{u, w} B S hS (yoneda.obj U) hW).val eV
      (StacksRepresentableCFG.EquivalenceOver.refl _)
      (twoFibreProductSquareAlgebraicStacks B S hS i a).snd.hom v', h]
    rfl
  -- every point of `A` is the image of a point of `V`
  have hAV : A ⊆ Space.pointsToScheme B S hS U '' Set.range (Space.pointsMap B S hS V φ) := by
    intro w hw
    obtain ⟨z', hz'⟩ := hA ⟨w, hw, rfl⟩
    set q' := (Space.pointsEquivScheme B S hS U).symm w
    have hq'w : Space.pointsToScheme B S hS U q' = w :=
      (Space.pointsEquivScheme B S hS U).apply_symm_apply w
    have hz'x : pointsMap B S hS 𝒵.val.val 𝒵.val.property 𝒳.val.property i.hom.hom z' =
        pointsMap B S hS (fibredCategory B S hS (yoneda.obj U)).val
          (fibredCategory B S hS (yoneda.obj U)).property 𝒳.val.property a.hom.hom
          (stackPointOfSpacePoint B S hS (yoneda.obj U) q') := by
      rw [← hchart, hz']
    obtain ⟨ζ', -, hζ'₂⟩ := exists_point_of_isTwoFibreProduct B S hS
      (twoFibreProductSquareAlgebraicStacks B S hS i a).underlying hQc z'
      (stackPointOfSpacePoint B S hS (yoneda.obj U) q') hz'x
    obtain ⟨v', hv'⟩ := (bijective_spacePointMap_representing B S hS V
      (twoFibreProductSquareAlgebraicStacks B S hS i a).pt.val eV).surjective ζ'
    exact ⟨q', ⟨v', hφpt v' q' (by rwa [hv'])⟩, hq'w⟩
  obtain ⟨ζ, hζ₁, hζ₂⟩ := exists_point_of_isTwoFibreProduct B S hS
    (twoFibreProductSquareAlgebraicStacks B S hS i a).underlying hQc z
    (stackPointOfSpacePoint B S hS (yoneda.obj U) q) hzx.symm
  obtain ⟨v, hv⟩ := (bijective_spacePointMap_representing B S hS V
    (twoFibreProductSquareAlgebraicStacks B S hS i a).pt.val eV).surjective ζ
  have hζ₁' : pointsMap B S hS (twoFibreProductSquareAlgebraicStacks B S hS i a).pt.val.val
      (twoFibreProductSquareAlgebraicStacks B S hS i a).pt.val.property 𝒵.val.property
      (twoFibreProductSquareAlgebraicStacks B S hS i a).fst.hom.hom ζ = z := hζ₁
  have hζ₂' : pointsMap B S hS (twoFibreProductSquareAlgebraicStacks B S hS i a).pt.val.val
      (twoFibreProductSquareAlgebraicStacks B S hS i a).pt.val.property
      (fibredCategory B S hS (yoneda.obj U)).property
      (twoFibreProductSquareAlgebraicStacks B S hS i a).snd.hom.hom ζ =
      stackPointOfSpacePoint B S hS (yoneda.obj U) q := hζ₂
  have hp : Space.pointsMap B S hS V φ v = q := hφpt v q (by rwa [hv])
  have hvA : Space.pointsToScheme B S hS U (Space.pointsMap B S hS V φ v) ∈ A := by
    rwa [hp, hqu]
  have hsub : (⟨u, hu⟩ : A) = ⟨_, hvA⟩ := Subtype.ext (by
    change u = Space.pointsToScheme B S hS U (Space.pointsMap B S hS V φ v)
    rw [hp, hqu])
  have hle : Space.dimensionAtPoint B S hS (yoneda.obj U) hW q ≤
      Space.dimensionAtPoint B S hS V hV v := by
    rw [dimensionAtPoint_yoneda_eq_topologicalKrullDimAt, hqu]
    refine hdim.trans ?_
    rw [hsub]
    exact Space.topologicalKrullDimAt_le_dimensionAtPoint_of_isImmersion B S hS hV φ himm A hAV
      v hvA
  have hQP := dimensionAtPoint_eq_add_relativeStackDimensionAt_of_isSmooth B S hS
    (twoFibreProductSquareAlgebraicStacks B S hS i a).fst hsmfst hftfst hQN h𝒵 ζ
  have haP := dimensionAtPoint_eq_add_relativeStackDimensionAt_of_isSmooth B S hS a hsma hfta
    h𝒰 h𝒳 (stackPointOfSpacePoint B S hS (yoneda.obj U) q)
  have hDRN := relativeStackDimensionAt_fst_eq_relativeStackDimensionAt.{u, w} B S hS i a
    (twoFibreProductSquareAlgebraicStacks B S hS i a) hQ hfta hftfst hQN h𝒰 h𝒵 h𝒳 ζ
  rw [hζ₁'] at hQP
  rw [hζ₂'] at hDRN
  rw [hzx] at haP
  obtain ⟨c, hc⟩ := exists_relativeStackDimensionAt_eq_intCast B S hS a hfta h𝒰 h𝒳
    (stackPointOfSpacePoint B S hS (yoneda.obj U) q)
  refine ⟨z, hz, ?_⟩
  rw [← hz]
  refine le_of_add_intCast_le_add_intCast (c := c) ?_
  calc dimensionAtPoint B S hS 𝒳 h𝒳
        (pointsMap B S hS 𝒵.val.val 𝒵.val.property 𝒳.val.property i.hom.hom z) +
          ((c : ℤ) : EInt)
      = dimensionAtPoint B S hS (algebraicSpaceStack.{u, w} B S hS (yoneda.obj U) hW) h𝒰
          (stackPointOfSpacePoint B S hS (yoneda.obj U) q) := by rw [haP, hc]
    _ = dimensionSubNat (Space.dimensionAtPoint B S hS (yoneda.obj U) hW q) 0 :=
        dimensionAtPoint_eq_dimensionSubNat_zero_of_representing.{u, w} B S hS _ h𝒰
          (yoneda.obj U) hW (StacksRepresentableCFG.EquivalenceOver.refl _) q _ rfl
    _ ≤ dimensionSubNat (Space.dimensionAtPoint B S hS V hV v) 0 := dimensionSubNat_mono 0 hle
    _ = dimensionAtPoint B S hS (twoFibreProductSquareAlgebraicStacks B S hS i a).pt hQN ζ :=
        (dimensionAtPoint_eq_dimensionSubNat_zero_of_representing.{u, w} B S hS _ hQN V hV eV v
          ζ hv).symm
    _ = dimensionAtPoint B S hS 𝒵 h𝒵 z + ((c : ℤ) : EInt) := by rw [hQP, hDRN, hc]

/-- A closed set of points of a locally Noetherian stack is the image of a reduced locally
Noetherian closed substack. -/
private theorem exists_isReducedStack_isLocallyNoetherianStack_range_pointsMap_eq
    (𝒳 : AlgebraicStacks.{u, w} B S hS) (h𝒳 : IsLocallyNoetherianStack.{u, w} B S hS 𝒳)
    (C : Set (points B S hS 𝒳.val.val 𝒳.val.property)) (hC : IsClosed C) :
    ∃ (𝒯 : AlgebraicStacks.{u, w} B S hS) (i : 𝒯 ⟶ 𝒳)
      (_ : AlgebraicStacks.IsClosedImmersion B S hS i) (_ : IsReducedStack B S hS 𝒯)
      (_ : IsLocallyNoetherianStack.{u, w} B S hS 𝒯),
      Set.range (pointsMap B S hS 𝒯.val.val 𝒯.val.property 𝒳.val.property i.hom.hom) = C := by
  obtain ⟨P, ⟨hPiso, hA, hAi⟩, hPT⟩ :=
    exists_isClosedSubstack_isReducedStack_range_pointsMap_eq 𝒳 C hC
  obtain ⟨hrange, hred⟩ := hPT hA
  exact ⟨_, fullSubcategoryInclusion 𝒳 P hA, hAi, hred,
    isLocallyNoetherianStack_of_isClosedSubstack B S hS 𝒳 P ⟨hPiso, hA, hAi⟩ hA h𝒳, hrange⟩

/-- **Stacks 0DRZ.** For a locally Noetherian algebraic stack `𝒳` over `S` and a point
`x ∈ |𝒳|`, the dimension of Stacks 0AFN at `x` is the supremum of the dimensions at `x` of the
irreducible components of `|𝒳|` through `x`, each endowed with its induced reduced structure:

`dim_x(𝒳) = sup_𝒯 dim_x(𝒯)`.

The inequality `sup_𝒯 dim_x(𝒯) ≤ dim_x(𝒳)` is Stacks 0DRY
(`AlgebraicGeometry.Stack.sSup_componentDimensionsAt_le`). For the reverse inequality, the
source's equation Stacks 0DS0, choose a smooth surjective chart `f : U ⟶ 𝒳` by a scheme and a
point `u` over `x`; some irreducible component `T'` of `U` through `u` has `dim_u(T') = dim_u(U)`
(`AlgebraicGeometry.Stack.exists_mem_irreducibleComponents_topologicalKrullDimAt_eq_of_isSmooth`).
The closure `T` of its image is an irreducible component of `|𝒳|` through `x` (Stacks 0DR5), and it
carries a reduced closed substack `𝒯` with `|𝒯| = T` (the existence half of Stacks 0509,
`AlgebraicGeometry.Stack.exists_isClosedSubstack_isReducedStack_range_pointsMap_eq`). Then
`AlgebraicGeometry.Stack.exists_dimensionAtPoint_le_of_isClosedImmersion_of_image_subset`, applied
to `A = T'`, produces a point of `𝒯` over `x` at which `dim_x(𝒳) ≤ dim(𝒯)`. -/
@[stacks 0DRZ]
theorem dimensionAtPoint_eq_sSup_irreducibleComponents (𝒳 : AlgebraicStacks.{u, w} B S hS)
    (h𝒳 : IsLocallyNoetherianStack.{u, w} B S hS 𝒳)
    (x : points B S hS 𝒳.val.val 𝒳.val.property) :
    dimensionAtPoint B S hS 𝒳 h𝒳 x = sSup (componentDimensionsAt B S hS 𝒳 x) := by
  classical
  refine le_antisymm ?_ (sSup_componentDimensionsAt_le B S hS 𝒳 h𝒳 x)
  obtain ⟨U, f, hf, hfs⟩ := exists_smooth_surjective_schemeStack.{u, w} B S hS 𝒳
  let := pointTopology B S hS (schemeFibredCategory B S hS U)
  obtain ⟨u, hu⟩ : ∃ u, AlgebraicStacks.chartPointMap B S hS U 𝒳 f u = x :=
    (hfs.comp (pointsHomeomorphScheme B S hS U).symm.surjective) x
  obtain ⟨T', hT', huT', hatt⟩ :=
    exists_mem_irreducibleComponents_topologicalKrullDimAt_eq_of_isSmooth B S hS 𝒳 h𝒳 U f hf u
  obtain ⟨𝒯, i, hi, hred, h𝒯, hrange⟩ :=
    exists_isReducedStack_isLocallyNoetherianStack_range_pointsMap_eq B S hS 𝒳 h𝒳
      (closure (AlgebraicStacks.chartPointMap B S hS U 𝒳 f '' T')) isClosed_closure
  obtain ⟨z, hz, hle⟩ := exists_dimensionAtPoint_le_of_isClosedImmersion_of_image_subset B S hS
    i hi h𝒯 h𝒳 U f hf T'
    (by
      rintro _ ⟨w, hw, rfl⟩
      rw [hrange]
      exact subset_closure ⟨w, hw, rfl⟩)
    u huT' hatt.le
  rw [hu] at hz hle
  exact hle.trans (le_sSup (mem_componentDimensionsAt_of_isSmooth_chart B S hS 𝒳 h𝒳 U f hf u x
    hu T' hT' huT' _ i hi hred h𝒯 z hrange hz))

/-- **Every irreducible component through `x` contributes to the supremum of Stacks 0DRZ.** For a
locally Noetherian algebraic stack `𝒳` over `S`, an irreducible component `T` of `|𝒳|` and a point
`x ∈ T`, the component endowed with its induced reduced structure — a reduced algebraic stack `𝒯`
with a closed immersion `i : 𝒯 ⟶ 𝒳` whose points are exactly `T`, which exists by the existence
half of Stacks 0509 — is locally Noetherian, has a point `t` over `x`, and `dim_t(𝒯)` belongs to
`AlgebraicGeometry.Stack.componentDimensionsAt`. So the supremum of Stacks 0DRZ runs over all the
irreducible components through `x`, none being left out for want of a reduced structure. -/
theorem exists_dimensionAtPoint_mem_componentDimensionsAt (𝒳 : AlgebraicStacks.{u, w} B S hS)
    (h𝒳 : IsLocallyNoetherianStack.{u, w} B S hS 𝒳)
    (x : points B S hS 𝒳.val.val 𝒳.val.property)
    (T : Set (points B S hS 𝒳.val.val 𝒳.val.property))
    (hT : T ∈ irreducibleComponents (points B S hS 𝒳.val.val 𝒳.val.property)) (hxT : x ∈ T) :
    ∃ (𝒯 : AlgebraicStacks.{u, w} B S hS) (i : 𝒯 ⟶ 𝒳)
      (_ : AlgebraicStacks.IsClosedImmersion B S hS i) (_ : IsReducedStack B S hS 𝒯)
      (h𝒯 : IsLocallyNoetherianStack.{u, w} B S hS 𝒯)
      (t : points B S hS 𝒯.val.val 𝒯.val.property),
      Set.range (pointsMap B S hS 𝒯.val.val 𝒯.val.property 𝒳.val.property i.hom.hom) = T ∧
        pointsMap B S hS 𝒯.val.val 𝒯.val.property 𝒳.val.property i.hom.hom t = x ∧
          dimensionAtPoint B S hS 𝒯 h𝒯 t ∈ componentDimensionsAt B S hS 𝒳 x := by
  obtain ⟨𝒯, i, hi, hred, h𝒯, hrange⟩ :=
    exists_isReducedStack_isLocallyNoetherianStack_range_pointsMap_eq B S hS 𝒳 h𝒳 T
      (isClosed_of_mem_irreducibleComponents T hT)
  obtain ⟨t, ht⟩ : x ∈ Set.range (pointsMap B S hS 𝒯.val.val 𝒯.val.property 𝒳.val.property
      i.hom.hom) := hrange ▸ hxT
  exact ⟨𝒯, i, hi, hred, h𝒯, t, hrange, ht,
    T, hT, hxT, _, i, hi, hred, h𝒯, t, hrange, ht, rfl⟩

end AlgebraicGeometry.Stack

end
