module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.FiniteTypePointSmoothChart
public import StacksFrontier.AlgebraicGeometry.Stacks.ImmersionPointsAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.PointsFibreProduct
public import StacksFrontier.AlgebraicGeometry.Stacks.PointsFibreProductAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.PointsTopology
public import StacksFrontier.AlgebraicGeometry.Stacks.SchemeTheoreticImage
public import StacksFrontier.AlgebraicGeometry.Stacks.SchemeTheoreticImageFlatBaseChange

/-!
# The points of the scheme theoretic image of a morphism of algebraic stacks (Stacks 0CML)

Let `f : 𝒳 ⟶ 𝒴` be a quasi-compact 1-morphism of algebraic stacks over `S` and let `𝒵 ⊆ 𝒴` be
its scheme theoretic image in the sense of **Stacks 0CMI**. **Stacks 0CML** asserts that `|𝒵|` is
the closure of the image of `|f|`.

The containment of the closure in `|𝒵|` needs no quasi-compactness: `f` factors through the
scheme theoretic image, so the image of `|f|` lies in `|𝒵|`, and `|𝒵|` is closed in `|𝒴|`
because the inclusion of a closed substack is a closed map on points by **Stacks 0H20**.

The reverse containment is the source's argument along a smooth affine chart `V ⟶ 𝒴`: a point of
`|𝒵|` lifts to `𝒵 ×_𝒴 V` (**Stacks 04XH**), the scheme theoretic image of `f` restricted to `V`
is that of the base change `𝒳 ×_𝒴 V ⟶ V` (the descent of the proof of **Stacks 0CMK**), which is
the scheme theoretic image of a quasi-compact morphism `A ⟶ V` of affines out of a smooth
presentation of `𝒳 ×_𝒴 V` (**Stacks 0CMJ**), and the support of the latter is the closure of its
image (**Stacks 082Z**, read on schemes as `AlgebraicGeometry.Scheme.Hom.support_ker`). The map
`|V| ⟶ |𝒴|` is continuous, which carries the closure back to `|𝒴|`.

Quasi-compactness is doing real work in the reverse containment: without it the coproduct of the
`Spec k[t]/(t^n)` over `Spec k[t]` has image closure a single point while its scheme theoretic
image is all of `Spec k[t]`.

## Main results

* `AlgebraicGeometry.Stack.range_pointsMap_subset_of_factorsThroughSubstack`: the image of the
  point map of a 1-morphism factoring through a substack lies in the points of that substack.
* `AlgebraicGeometry.Stack.isClosed_range_pointsMap_fullSubcategoryInclusion`: the points of a
  closed substack form a closed subset of the points of the ambient stack.
* `AlgebraicGeometry.Stack.range_pointsMap_eq_closure_of_isSchemeTheoreticImage`:
  **Stacks 0CML**.

## Implementation notes

A closed substack is a property of the objects of `𝒴` satisfying
`AlgebraicGeometry.Stack.IsClosedSubstack`, and being the scheme theoretic image is
`AlgebraicGeometry.Stack.IsSchemeTheoreticImage`; the scheme theoretic image is the property `P`
of the statement, which exists by Stacks 0CPU
(`AlgebraicGeometry.Stack.isSchemeTheoreticImage_schemeTheoreticImageCandidate`). The full
subcategory it cuts out is an algebraic stack by
`AlgebraicGeometry.Stack.IsSchemeTheoreticImage.isAlgebraicStack`.

The point sets and point maps are those of **Stacks 04XG** read through
`AlgebraicGeometry.Stack.AlgebraicStacks.pointsMap`, and the topology is
`AlgebraicGeometry.Stack.pointTopology` of **Stacks 04XL**, written out with `@` because it is
not an instance.

## References

* [Stacks Project, Tag 0CMI](https://stacks.math.columbia.edu/tag/0CMI)
* [Stacks Project, Tag 0CMJ](https://stacks.math.columbia.edu/tag/0CMJ)
* [Stacks Project, Tag 0CMK](https://stacks.math.columbia.edu/tag/0CMK)
* [Stacks Project, Tag 0CML](https://stacks.math.columbia.edu/tag/0CML)
* [Stacks Project, Tag 04XH](https://stacks.math.columbia.edu/tag/04XH)
* [Stacks Project, Tag 082Z](https://stacks.math.columbia.edu/tag/082Z)
* [Stacks Project, Tag 0H20](https://stacks.math.columbia.edu/tag/0H20)
-/

@[expose] public section

open CategoryTheory Opposite

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **A 1-morphism factoring through a substack has its image on points inside it.** A
factorization over the big fppf site of `S` and up to a 2-isomorphism makes the point map of the
1-morphism the point map of the inclusion composed with the point map of the factorization. -/
theorem range_pointsMap_subset_of_factorsThroughSubstack
    {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴)
    {P : ObjectProperty 𝒴.val.val.obj}
    (hA : IsAlgebraicStack.{u, w} B S hS (fullSubcategoryBased 𝒴 P))
    (hfac : FactorsThroughSubstack f P) :
    Set.range (AlgebraicStacks.pointsMap B S hS f) ⊆
      Set.range (AlgebraicStacks.pointsMap B S hS (fullSubcategoryInclusion 𝒴 P hA)) := by
  obtain ⟨g, ⟨e⟩⟩ := hfac
  rintro q ⟨x, rfl⟩
  exact ⟨pointsMap B S hS 𝒳.val.val (Classical.choose 𝒳.property) (Classical.choose hA) g x,
    (pointsMap_comp B S hS 𝒳.val.val (Classical.choose 𝒳.property) (Classical.choose hA)
      (Classical.choose 𝒴.property) g (fullSubcategoryBasedInclusion 𝒴 P) x).trans
      (congrFun (pointsMap_eq_of_basedNatTrans B S hS 𝒳.val.val (Classical.choose 𝒳.property)
        (Classical.choose 𝒴.property) e.hom) x)⟩

/-- **The points of a closed substack are a closed subset of the points of the ambient stack.**
The inclusion of a closed substack is a closed map on points by **Stacks 0H20**, and the image of
the whole point space is the range. -/
theorem isClosed_range_pointsMap_fullSubcategoryInclusion
    {𝒴 : AlgebraicStacks.{u, w} B S hS} {P : ObjectProperty 𝒴.val.val.obj}
    (hA : IsAlgebraicStack.{u, w} B S hS (fullSubcategoryBased 𝒴 P))
    (hci : AlgebraicStacks.IsClosedImmersion B S hS (fullSubcategoryInclusion 𝒴 P hA)) :
    @IsClosed _ (pointTopology B S hS 𝒴.val)
      (Set.range (AlgebraicStacks.pointsMap B S hS (fullSubcategoryInclusion 𝒴 P hA))) :=
  Set.image_univ ▸ AlgebraicStacks.isClosedMap_pointsMap_of_isClosedImmersion B S hS
    (fullSubcategoryInclusion 𝒴 P hA) hci Set.univ
    (@isClosed_univ _ (pointTopology B S hS (fullSubcategoryAlgebraicStack 𝒴 P hA).val))

/-- **Stacks 0CML.** Let `f : 𝒳 ⟶ 𝒴` be a quasi-compact 1-morphism of algebraic stacks over `S`
and let `P` cut out its scheme theoretic image `𝒵 ⊆ 𝒴` (Stacks 0CMI). Then the points of `𝒵` are
the closure in `|𝒴|` of the image of `|f|`.

The closure lies in `|𝒵|` for any `f`: `f` factors through `𝒵`, whose points are closed by
**Stacks 0H20**. Conversely, let `z` be a point of `𝒵`, and choose a smooth chart
`v : (Sch/V)_fppf ⟶ 𝒴` with `V` affine through its image, and a point `η` of `V` over it. The
point `(z, η)` lifts to `𝒵 ×_𝒴 V` (**Stacks 04XH**), so `η` comes from a field-valued point
`t : Spec K ⟶ V` at which `P` holds. As `f` is quasi-compact, `𝒳 ×_𝒴 V` is quasi-compact and has
a smooth surjective presentation by an affine `A`, with composite `g : A ⟶ V`. The scheme
theoretic image of `f` lies in the closed substack cut out by the scheme theoretic images of the
base changes of `f` to the smooth affine charts (the descent of the proof of **Stacks 0CMK**), and
that image along `v` lies in the scheme theoretic image of `g` (**Stacks 0CMJ**, in the form of
Stacks 06QA). So `t` factors through the scheme theoretic image of the quasi-compact `g`, and `η`
lies in the closure of the image of `g` (**Stacks 082Z**, read on schemes). The map
`|V| ⟶ |𝒴|` is continuous and carries the image of `g` into the image of `|f|`, the square
`A ⟶ 𝒳 ×_𝒴 V` commuting, so it carries `η` into the closure of the image of `|f|`. -/
@[stacks 0CML]
theorem range_pointsMap_eq_closure_of_isSchemeTheoreticImage
    {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴) (hf : IsQuasiCompactMorphism B S hS f)
    {P : ObjectProperty 𝒴.val.val.obj} (hP : IsSchemeTheoreticImage f P) :
    Set.range (AlgebraicStacks.pointsMap B S hS
        (fullSubcategoryInclusion 𝒴 P hP.isAlgebraicStack)) =
      @closure _ (pointTopology B S hS 𝒴.val)
        (Set.range (AlgebraicStacks.pointsMap B S hS f)) := by
  let _ := pointTopology B S hS 𝒴.val
  refine le_antisymm ?_ (closure_minimal
    (range_pointsMap_subset_of_factorsThroughSubstack B S hS f _ hP.2.1)
    (isClosed_range_pointsMap_fullSubcategoryInclusion B S hS _ hP.1.2.choose_spec))
  rintro _ ⟨ζ, rfl⟩
  have : P.IsClosedUnderIsomorphisms := hP.1.1
  have hPflat : P ≤ flatLocalImage f :=
    hP.2.2 _ (isClosedSubstack_flatLocalImage f hf) (factorsThroughSubstack_flatLocalImage f)
  set ι := fullSubcategoryInclusion 𝒴 P hP.isAlgebraicStack
  -- a smooth affine chart through the point
  obtain ⟨V, v, hV, hv, η, hη⟩ :=
    exists_affine_smooth_chart 𝒴 (AlgebraicStacks.pointsMap B S hS ι ζ)
  -- an affine presentation of `𝒳 ×_𝒴 V`
  set sq := twoFibreProductSquareAlgebraicStacks B S hS v f
  have hqc : IsQuasiCompactStack.{u, w} B S hS sq.pt.val sq.pt.property :=
    hf (schemeStack.{u, w} B S hS V) v
      (isQuasiCompactStack_schemeStack_of_compactSpace.{u, w} B S hS V inferInstance)
  obtain ⟨A, hA, ρ, hρs, hρsm⟩ := exists_affineAtlas_of_isQuasiCompactStack B S hS sq.pt hqc
  set g : A ⟶ V := siteMap B S hS (ρ ≫ sq.fst)
  -- the point of `V` lies in the closure of the image of `g`
  have hηg : pointsHomeomorphScheme B S hS V η ∈
      closure (Set.range ((BigFppfOver.toScheme B S hS).map g)) := by
    obtain ⟨p, -, hp⟩ := exists_point_of_isTwoFibreProduct_algebraicStacks B S hS
      (twoFibreProductSquareAlgebraicStacks B S hS ι v)
      (isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS ι v) ζ η hη.symm
    obtain ⟨q, rfl⟩ := Quotient.exists_rep p
    rw [← hp]
    set q' := fieldValuedPointMap B S hS _
      (twoFibreProductSquareAlgebraicStacks B S hS ι v).snd.hom.hom q
    have hs : fieldValuedPointSchemeArrow B S hS q' ∈
        (Space.schemeTheoreticImageSubfunctor B S hS (yoneda.map g)).obj (op q'.base) :=
      chartImageSubfunctor_le_schemeTheoreticImageSubfunctor f v ρ hρs hρsm _
        ((chartImageSubfunctor f v).map (eqToHom q'.over.symm).op
          (chartSubfunctor_flatLocalImage_le f v hV hv _
            (hPflat _ (P.prop_of_iso q.obj.iso q.obj.x.property))))
    exact Space.range_subset_closure_range_of_mem_schemeTheoreticImageSubfunctor B S hS g hs
      ⟨_, (pointsHomeomorphScheme_pointClass B S hS V q').symm⟩
  -- the continuous map `|V| ⟶ |𝒴|` carries the image of `g` into the image of `|f|`
  let _ := reprPointTopology B S hS V
  let Φ : (BigFppfOver.toScheme B S hS).obj V → AlgebraicStacks.points B S hS 𝒴 :=
    fun x => AlgebraicStacks.pointsMap B S hS v ((pointsHomeomorphScheme B S hS V).symm x)
  have hΦ : Continuous Φ :=
    (continuous_pointsMap B S hS (schemeStack.{u, w} B S hS V).val 𝒴.val v.hom.hom).comp
      (pointsHomeomorphScheme B S hS V).symm.continuous
  have hΦη : Φ (pointsHomeomorphScheme B S hS V η) = AlgebraicStacks.pointsMap B S hS ι ζ := by
    simpa only [Φ, Homeomorph.symm_apply_apply] using hη
  have hsq : AlgebraicStacks.pointsMap B S hS v ∘ AlgebraicStacks.pointsMap B S hS sq.fst =
      AlgebraicStacks.pointsMap B S hS f ∘ AlgebraicStacks.pointsMap B S hS sq.snd := by
    rw [← AlgebraicStacks.pointsMap_comp, ← AlgebraicStacks.pointsMap_comp]
    exact AlgebraicStacks.pointsMap_eq_of_hom₂ B S hS sq.iso.hom
  have hΦg : Φ '' Set.range ((BigFppfOver.toScheme B S hS).map g) ⊆
      Set.range (AlgebraicStacks.pointsMap B S hS f) := by
    let _ := reprPointTopology B S hS A
    rintro _ ⟨_, ⟨a, rfl⟩, rfl⟩
    obtain ⟨y, rfl⟩ := (pointsHomeomorphScheme B S hS A).surjective a
    have h₁ : (pointsHomeomorphScheme B S hS V).symm
        ((BigFppfOver.toScheme B S hS).map g (pointsHomeomorphScheme B S hS A y)) =
          AlgebraicStacks.pointsMap B S hS (ρ ≫ sq.fst) y := by
      rw [Homeomorph.symm_apply_eq, pointsHomeomorphScheme_pointsMap]
    refine ⟨AlgebraicStacks.pointsMap B S hS (ρ ≫ sq.snd) y, ?_⟩
    simp only [Φ, h₁, AlgebraicStacks.pointsMap_comp, Function.comp_apply]
    exact (congrFun hsq _).symm
  exact hΦη ▸ closure_mono hΦg (image_closure_subset_closure_image hΦ ⟨_, hηg, rfl⟩)

end AlgebraicGeometry.Stack

end
