module

public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupSpaces.ConstantDimension
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.Quotient.QuotientStackDiagonal
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Fibres.Dimension
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeDimensionBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.DimensionChartIndependence
public import StacksFrontier.AlgebraicGeometry.Stacks.PointsTopologyRepresentable
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeDimensionFiniteness
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothQuotientStack
public import StacksFrontier.AlgebraicGeometry.Stacks.TwoFibreProductSquareAlgebraicStack

/-!
# The relative dimension of the atlas `U ⟶ [U/R]`

Let `G = (U, R, s, t, c)` be a groupoid in algebraic spaces and let `𝒬` be a model of its quotient
stack `[U/R]`. The fibre of the atlas `U ⟶ [U/R]` of Stacks 044R over a point of `[U/R]` is a
fibre of the source map `s : R ⟶ U`: the self-intersection `U ×_{[U/R]} U` is `R` by Stacks 04M9,
its two projections being `s` and `t`. So the relative dimension of the atlas at a point `u ∈ |U|`,
in the sense of Stacks 0DRG, is the relative dimension of `s` at every point of `R` whose target is
`u`. For the quotient `[X/G]` of a group `G` over a field acting on `X` this is the dimension of
`G`, and that is what makes the dimension of `[X/G]` equal to `dim(X) - dim(G)` (Stacks 0AFR).

## Main results

* `AlgebraicGeometry.Stack.hasRelativeDimensionAt_source_of_relativeDimensionAt`: the relative
  dimension of the atlas at the target of a point `r ∈ |R|` is the relative dimension of the
  source map at `r`.
* `AlgebraicGeometry.Stack.relativeDimensionAt_quotientStackModelProjection_eq_dimension`: for the
  action of a group `G` locally of finite type over a field on an algebraic space `X`, the atlas
  `X ⟶ [X/G]` has relative dimension `dim(G)` at every point of `X`.

## Implementation notes

The first result is the base-change step of the proof of Stacks 0AFM,
`AlgebraicGeometry.Stack.hasRelativeDimensionAt_representingMap_fst_of_fieldFibreDimensionAt`,
read on the self-intersection of the atlas with its representation by the arrow space,
`AlgebraicGeometry.Stack.quotientStackModelArrowEquivalenceOver`, whose two projections induce
the source and the target of the groupoid.

For an action groupoid the source map is the second projection `G ×_A X ⟶ X`, a base change of
the structure morphism `G ⟶ A`, so Stacks 04NS identifies its relative dimension at a point with
that of `G ⟶ A` at the image point. When `A` is the spectrum of a field that relative dimension is
the dimension of `G` at the point (Stacks 0D4M), which is the dimension of `G` by Stacks 06FE.
Every point of `X` is the target of a point of `G ×_A X`, namely of its identity arrow.

## References

* [Stacks Project, Tag 0AFR](https://stacks.math.columbia.edu/tag/0AFR)
* [Stacks Project, Tag 0AFM](https://stacks.math.columbia.edu/tag/0AFM)
* [Stacks Project, Tag 0DRG](https://stacks.math.columbia.edu/tag/0DRG)
* [Stacks Project, Tag 044R](https://stacks.math.columbia.edu/tag/044R)
* [Stacks Project, Tag 04M9](https://stacks.math.columbia.edu/tag/04M9)
* [Stacks Project, Tag 04NS](https://stacks.math.columbia.edu/tag/04NS)
* [Stacks Project, Tag 0D4M](https://stacks.math.columbia.edu/tag/0D4M)
* [Stacks Project, Tag 06FE](https://stacks.math.columbia.edu/tag/06FE)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The relative dimension of the atlas `U ⟶ [U/R]` is that of the source map.** Let `𝒬` be a
model of the quotient stack of a groupoid `(U, R, s, t, c)` whose source is locally of finite type.
If the atlas of Stacks 044R has relative dimension `d` (Stacks 0DRG) at the target `t(r)` of a
point `r ∈ |R|`, then the source map `s : R ⟶ U` has relative dimension `d` at `r` (Stacks 04NM).

The self-intersection of the atlas is represented by `R`, its first projection inducing `s` and
its second `t` (Stacks 04M9), so this is the base-change step of Stacks 0AFM. -/
theorem hasRelativeDimensionAt_source_of_relativeDimensionAt
    (A : AlgebraicSpaces B S hS) (H : GroupoidInAlgebraicSpaces B S hS A)
    (𝒬 : AlgebraicStacks.{u, w} B S hS)
    (e : StacksRepresentableCFG.EquivalenceOver (quotientStack H).p 𝒬.val.val.p)
    (hs : Space.IsLocallyOfFiniteType B S hS H.source.hom)
    (hf : AlgebraicStacks.IsLocallyOfFiniteType B S hS
      (quotientStackModelProjection.{u, w} B S hS A H 𝒬 e))
    (r : Space.points B S hS H.arrows.obj) (d : ℕ)
    (hd : relativeDimensionAt.{u, w} B S hS H.objects.obj H.objects.property 𝒬
      (quotientStackModelProjection.{u, w} B S hS A H 𝒬 e) hf
      (Space.pointsMap B S hS H.arrows.obj H.target.hom r) = (d : WithBot ℕ∞)) :
    Space.HasRelativeDimensionAt (d : ℕ∞) B S hS H.source.hom r := by
  let f := quotientStackModelProjection.{u, w} B S hS A H 𝒬 e
  have hUrep := isRepresentableByAlgebraicSpace_fibredCategory B S hS H.objects.obj
    H.objects.property
  have hQc :
      Bicategory.IsTwoFibreProduct (twoFibreProductSquareAlgebraicStacks B S hS f f).underlying :=
    CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1}
      f.hom f.hom
  let eP := quotientStackModelArrowEquivalenceOver H 𝒬 e
  have hQpt : IsRepresentableByAlgebraicSpace B S hS
      (twoFibreProductSquareAlgebraicStacks B S hS f f).underlying.pt :=
    ⟨H.arrows.obj, H.arrows.property, ⟨eP⟩⟩
  have hpr : representingMap B S hS
      (twoFibreProductSquareAlgebraicStacks B S hS f f).underlying.pt
      (fibredCategory B S hS H.objects.obj) H.arrows.obj H.objects.obj eP
      (StacksRepresentableCFG.EquivalenceOver.refl _)
      (twoFibreProductSquareAlgebraicStacks B S hS f f).underlying.fst = H.source.hom :=
    representingMap_eq_source_of_obj_eq H 𝒬 e _ (fun _ => rfl)
  have hpr' : representingMap B S hS
      (twoFibreProductSquareAlgebraicStacks B S hS f f).underlying.pt
      (fibredCategory B S hS H.objects.obj) H.arrows.obj H.objects.obj eP
      (StacksRepresentableCFG.EquivalenceOver.refl _)
      (twoFibreProductSquareAlgebraicStacks B S hS f f).underlying.snd = H.target.hom :=
    representingMap_eq_target_of_obj_eq H 𝒬 e _ (fun _ => rfl)
  let ζ := spacePointMap B S hS H.arrows.obj
    (twoFibreProductSquareAlgebraicStacks B S hS f f).underlying.pt
    (representingEquivalence B S hS H.arrows.obj _ eP).functor r
  have hsnd : pointsMap B S hS
      (twoFibreProductSquareAlgebraicStacks B S hS f f).underlying.pt.val
      (twoFibreProductSquareAlgebraicStacks B S hS f f).underlying.pt.property
      (fibredCategory B S hS H.objects.obj).property
      (twoFibreProductSquareAlgebraicStacks B S hS f f).underlying.snd.hom ζ =
      stackPointOfSpacePoint B S hS H.objects.obj
        (Space.pointsMap B S hS H.arrows.obj H.target.hom r) := by
    have h := spacePointMap_representing_naturality B S hS H.arrows.obj H.objects.obj
      (twoFibreProductSquareAlgebraicStacks B S hS f f).underlying.pt
      (fibredCategory B S hS H.objects.obj) eP (StacksRepresentableCFG.EquivalenceOver.refl _)
      (twoFibreProductSquareAlgebraicStacks B S hS f f).underlying.snd r
    rw [hpr'] at h
    exact h.symm
  obtain ⟨p', q', -, hq', hval⟩ := exists_eq_fieldFibreDimensionAt B S hS H.objects.obj
    H.objects.property 𝒬 f hf (Space.pointsMap B S hS H.arrows.obj H.target.hom r)
  exact hasRelativeDimensionAt_representingMap_fst_of_fieldFibreDimensionAt.{u, w} B S hS f f
    hUrep hf hQc hQpt H.objects.obj H.arrows.obj H.objects.property H.arrows.property
    (StacksRepresentableCFG.EquivalenceOver.refl _) eP hs hpr ζ r rfl p' q'
    (hq'.trans hsnd.symm) (d : ℕ∞) (by rw [← hval, hd]; rfl)

/-- **Every point of the object space of a groupoid is a target**, namely of its identity
arrow: the identity `e : U ⟶ R` of the groupoid satisfies `e ≫ t = 𝟙`. -/
theorem exists_pointsMap_target_eq {A : AlgebraicSpaces B S hS}
    (H : GroupoidInAlgebraicSpaces B S hS A) (u : Space.points B S hS H.objects.obj) :
    ∃ r : Space.points B S hS H.arrows.obj,
      Space.pointsMap B S hS H.arrows.obj H.target.hom r = u := by
  obtain ⟨e, he, -⟩ := Deformation.existsUnique_identity H.toGroupoidInFunctors
  let e' : H.objects.obj ⟶ H.arrows.obj := e
  have het : e' ≫ H.target.hom = 𝟙 _ := by
    ext T x
    show H.target.hom.app T (e.app T x) = x
    let x' : H.toGroupoidInFunctors.Evaluation T := x
    exact (congrArg (fun a => H.target.hom.app T a) (he T x')).trans
      (H.toGroupoidInFunctors.evaluationArrowEquiv T x' x' (𝟙 x')).property.2
  refine ⟨Space.pointsMap B S hS H.objects.obj e' u, ?_⟩
  rw [← Space.pointsMap_comp_apply, het, Space.pointsMap_id_apply]

section Action

variable {k : Type u} [Field k] (C : BigFppfSite.{u}) (hk : C.Contains (Spec (.of k)))
  (G : Space.GroupAlgebraicSpace C (Spec (.of k)) hk
    (Space.terminalSpace C (Spec (.of k)) hk).obj
    (Space.terminalSpace C (Spec (.of k)) hk).property)
  (X : Over (Space.terminalSpace C (Spec (.of k)) hk).obj) [ModObj G.obj.X X]
  (hX : IsAlgebraicSpace C (Spec (.of k)) hk X.left)

/-- The source map `G ×_k X ⟶ X` of the action groupoid of a group locally of finite type over
a field is locally of finite type, being a base change of the structure morphism of the group. -/
theorem isLocallyOfFiniteType_source_groupoidOfAction
    (hGft : Space.IsLocallyOfFiniteType C (Spec (.of k)) hk G.obj.X.hom) :
    Space.IsLocallyOfFiniteType C (Spec (.of k)) hk
      (Space.groupoidOfAction (Space.terminalSpace C (Spec (.of k)) hk) G.obj.X X G.property
        hX).groupoid.source.hom :=
  Space.IsLocallyOfFiniteType.of_isPullback C (Spec (.of k)) hk
    (IsPullback.of_hasPullback G.obj.X.hom X.hom).flip G.property
    (Space.terminalSpace C (Spec (.of k)) hk).property hGft

/-- A group algebraic space locally of finite type over a field `k` has dimension `m` as soon
as its structure morphism has relative dimension `m` at some point. -/
private theorem dimension_eq_of_hasRelativeDimensionAt
    (hGft : Space.IsLocallyOfFiniteType C (Spec (.of k)) hk G.obj.X.hom) (m : ℕ∞)
    (g : Space.points C (Spec (.of k)) hk G.obj.X.left)
    (hm : Space.HasRelativeDimensionAt m C (Spec (.of k)) hk G.obj.X.hom g) :
    Space.dimension C (Spec (.of k)) hk G.obj.X.left G.property = (m : WithBot ℕ∞) := by
  let p : Space.FieldValuedPoint C (Spec (.of k)) hk
      (Space.terminalSpace C (Spec (.of k)) hk).obj :=
    { carrier := k, contained := hk, toBase := 𝟙 _, value := 𝟙 _ }
  rw [Space.dimension_eq_dimensionAtPoint_of_groupAlgebraicSpace C hk G hGft g]
  exact (Space.relativeDimensionAt_fieldTarget_iff_dimensionAtPoint C (Spec (.of k)) hk
    G.property p G.obj.X.hom g m).mp hm

/-- **The atlas `X ⟶ [X/G]` has relative dimension `dim(G)` at every point.** Let a group
algebraic space `G`, locally of finite type over a field `k`, act on an algebraic space `X` over
`k`, and let `𝒬` be a model of the quotient stack `[X/G]`. Then the relative dimension of
Stacks 0DRG of the atlas of Stacks 044R at every point of `X` is the dimension of `G`.

The fibre of the atlas is a fibre of the source map `G ×_k X ⟶ X`, which is a base change of
`G ⟶ Spec k` (Stacks 04NS); over a field relative dimension is dimension (Stacks 0D4M), and a
group over a field has the same dimension at each of its points (Stacks 06FE). -/
theorem relativeDimensionAt_quotientStackModelProjection_eq_dimension
    (hGft : Space.IsLocallyOfFiniteType C (Spec (.of k)) hk G.obj.X.hom)
    (𝒬 : AlgebraicStacks.{u, w} C (Spec (.of k)) hk)
    (e : StacksRepresentableCFG.EquivalenceOver
      (quotientStack (Space.groupoidOfAction (Space.terminalSpace C (Spec (.of k)) hk) G.obj.X X
        G.property hX).groupoid).p 𝒬.val.val.p)
    (hf : AlgebraicStacks.IsLocallyOfFiniteType C (Spec (.of k)) hk
      (quotientStackModelProjection.{u, w} C (Spec (.of k)) hk
        (Space.terminalSpace C (Spec (.of k)) hk)
        (Space.groupoidOfAction (Space.terminalSpace C (Spec (.of k)) hk) G.obj.X X G.property
          hX).groupoid 𝒬 e))
    (t : Space.points C (Spec (.of k)) hk X.left) :
    relativeDimensionAt.{u, w} C (Spec (.of k)) hk X.left hX 𝒬
        (quotientStackModelProjection.{u, w} C (Spec (.of k)) hk
          (Space.terminalSpace C (Spec (.of k)) hk)
          (Space.groupoidOfAction (Space.terminalSpace C (Spec (.of k)) hk) G.obj.X X G.property
            hX).groupoid 𝒬 e) hf t =
      Space.dimension C (Spec (.of k)) hk G.obj.X.left G.property := by
  let H := (Space.groupoidOfAction (Space.terminalSpace C (Spec (.of k)) hk) G.obj.X X
    G.property hX).groupoid
  obtain ⟨d, hd⟩ := exists_relativeDimensionAt_eq_natCast.{u, w} C (Spec (.of k)) hk X.left hX
    𝒬 _ hf t
  obtain ⟨r, hr⟩ := exists_pointsMap_target_eq C (Spec (.of k)) hk H t
  have h₁ := hasRelativeDimensionAt_source_of_relativeDimensionAt.{u, w} C (Spec (.of k)) hk
    (Space.terminalSpace C (Spec (.of k)) hk) H 𝒬 e
    (isLocallyOfFiniteType_source_groupoidOfAction C hk G X hX hGft) hf r d (hr ▸ hd)
  have h₂ := (Space.hasRelativeDimensionAt_iff_of_isPullback' C (Spec (.of k)) hk (d : ℕ∞)
    (IsPullback.of_hasPullback G.obj.X.hom X.hom).flip G.property
    (Space.terminalSpace C (Spec (.of k)) hk).property hX hGft r).mp h₁
  rw [hd]
  exact (dimension_eq_of_hasRelativeDimensionAt C hk G hGft _ _ h₂).symm

/-- **A group algebraic space locally of finite type over a field has finite dimension.** Its
identity is a point, at which its dimension is its relative dimension over the field
(Stacks 0D4M), a natural number because the structure morphism is locally of finite type; and
that is its dimension by Stacks 06FE. -/
theorem exists_dimension_eq_natCast_of_groupAlgebraicSpace
    (hGft : Space.IsLocallyOfFiniteType C (Spec (.of k)) hk G.obj.X.hom) :
    ∃ m : ℕ, Space.dimension C (Spec (.of k)) hk G.obj.X.left G.property =
      (m : WithBot ℕ∞) := by
  let p : Space.FieldValuedPoint C (Spec (.of k)) hk
      (Space.terminalSpace C (Spec (.of k)) hk).obj :=
    { carrier := k, contained := hk, toBase := 𝟙 _, value := 𝟙 _ }
  let g : Space.points C (Spec (.of k)) hk G.obj.X.left :=
    Space.pointsMap C (Spec (.of k)) hk _ (MonObj.one (X := G.obj.X)).left
      (p.class C (Spec (.of k)) hk _)
  obtain ⟨m, hm⟩ := Space.exists_hasRelativeDimensionAt_natCast C (Spec (.of k)) hk G.property
    (Space.terminalSpace C (Spec (.of k)) hk).property G.obj.X.hom hGft g
  exact ⟨m, dimension_eq_of_hasRelativeDimensionAt C hk G hGft _ g hm⟩

end Action

end AlgebraicGeometry.Stack

end
