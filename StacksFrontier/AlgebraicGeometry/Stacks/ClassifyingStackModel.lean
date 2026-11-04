module

public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.Quotient.QuotientStackDiagonal
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.SmoothActionGroupoid
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatFieldCover
public import StacksFrontier.AlgebraicGeometry.Spaces.Representable.Bootstrap.Unconditional
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothFlat
public import StacksFrontier.AlgebraicGeometry.Stacks.AlgebraicStackSmallModel
public import StacksFrontier.AlgebraicGeometry.Stacks.ClosedSubsetSeparationAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.FiniteTypePointSmoothChart
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeDimensionFiniteness
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeDimensionLocalConstancyStack
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupSpaces.ConstantDimension
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Fibres.Dimension
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothQuotientStack
public import StacksFrontier.Examples.Stacks.ClassifyingStackSmoothCovering

/-!
# The classifying stack of a smooth group over a field, and its tautological chart

Let `k` be a field and let `G` be a group algebraic space over `Spec k` which is smooth over
`Spec k`. The classifying stack `BG = [Spec k/G]` of Stacks 044Q (the quotient stack of the
trivial action of `G` on `Spec k`, `AlgebraicGeometry.Stack.classifyingStack`) is an algebraic
stack (Stacks 04TK, the bootstrap theorem Stacks 04S6 being a theorem of the library), and its
tautological chart `Spec k ⟶ BG` of Stacks 044R is smooth and surjective.

The classifying stack is a stackification, whose morphisms live one universe above those of the
2-category `AlgebraicGeometry.Stack.AlgebraicStacks`; as everywhere in the library, statements
about it are made at an arbitrary *model*: an object `𝒬` of `AlgebraicStacks` together with an
equivalence over the site between `BG` and `𝒬`. Such a model exists
(`AlgebraicGeometry.Stack.algebraicStackModel`).

## Main definitions

* `AlgebraicGeometry.Stack.classifyingGroupoid`: the action groupoid of the trivial action of
  `G` on `Spec k`, whose quotient stack is `BG`.
* `AlgebraicGeometry.Stack.classifyingChart`: the tautological chart `Spec k ⟶ BG`, read on a
  model.

## Main results

* `AlgebraicGeometry.Stack.isAlgebraicStack_classifyingStack`: `BG` is an algebraic stack.
* `AlgebraicGeometry.Stack.isSmooth_classifyingChart`,
  `AlgebraicGeometry.Stack.isSurjective_classifyingChart`: the chart is smooth and surjective.
* `AlgebraicGeometry.Stack.subsingleton_points_classifyingModel`: `|BG|` has at most one point.

## References

* [Stacks Project, Tag 044Q](https://stacks.math.columbia.edu/tag/044Q)
* [Stacks Project, Tag 044R](https://stacks.math.columbia.edu/tag/044R)
* [Stacks Project, Tag 04TK](https://stacks.math.columbia.edu/tag/04TK)
* [Stacks Project, Tag 04X0](https://stacks.math.columbia.edu/tag/04X0)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory

universe u w

namespace AlgebraicGeometry.Stack

variable {k : Type u} [Field k] (C : BigFppfSite.{u}) (hk : C.Contains (Spec (.of k)))
  (G : Space.GroupAlgebraicSpace C (Spec (.of k)) hk
    (Space.terminalSpace C (Spec (.of k)) hk).obj
    (Space.terminalSpace C (Spec (.of k)) hk).property)

/-- The action groupoid of the trivial action of `G` on the base `Spec k`, whose quotient stack is
the classifying stack `BG = [Spec k/G]`. -/
abbrev classifyingGroupoid :
    GroupoidInAlgebraicSpaces C (Spec (.of k)) hk (Space.terminalSpace C (Spec (.of k)) hk) :=
  letI : ModObj G.obj.X (𝟙_ (Over (Space.terminalSpace C (Spec (.of k)) hk).obj)) :=
    ModObj.trivialAction _ _
  (Space.groupoidOfAction (Space.terminalSpace C (Spec (.of k)) hk) G.obj.X
    (𝟙_ (Over (Space.terminalSpace C (Spec (.of k)) hk).obj)) G.property
    (Space.terminalSpace C (Spec (.of k)) hk).property).groupoid

/-- The object space of the action groupoid of the trivial action is the base. -/
theorem classifyingGroupoid_objects_obj :
    (classifyingGroupoid C hk G).objects.obj = (Space.terminalSpace C (Spec (.of k)) hk).obj :=
  let : ModObj G.obj.X (𝟙_ (Over (Space.terminalSpace C (Spec (.of k)) hk).obj)) :=
    ModObj.trivialAction _ _
  congrArg (fun Z => Z.obj) (Space.groupoidOfAction (Space.terminalSpace C (Spec (.of k)) hk)
    G.obj.X (𝟙_ (Over (Space.terminalSpace C (Spec (.of k)) hk).obj)) G.property
    (Space.terminalSpace C (Spec (.of k)) hk).property).objects_eq

/-- If `G` is smooth over `Spec k`, the action groupoid of its trivial action is smooth. -/
theorem isSmooth_classifyingGroupoid (hG : Space.IsSmooth C (Spec (.of k)) hk G.obj.X.hom) :
    GroupoidInAlgebraicSpaces.IsSmooth C (Spec (.of k)) hk (classifyingGroupoid C hk G) :=
  let : ModObj G.obj.X (𝟙_ (Over (Space.terminalSpace C (Spec (.of k)) hk).obj)) :=
    ModObj.trivialAction _ _
  Space.isSmooth_groupoidOfAction (Space.terminalSpace C (Spec (.of k)) hk) G.obj.X
    (𝟙_ (Over (Space.terminalSpace C (Spec (.of k)) hk).obj)) G.property
    (Space.terminalSpace C (Spec (.of k)) hk).property hG

/-- **The classifying stack of a smooth group over a field is an algebraic stack**: Stacks 04TK for
the action groupoid of the trivial action, with the bootstrap theorem Stacks 04S6 of the
library. -/
theorem isAlgebraicStack_classifyingStack (hG : Space.IsSmooth C (Spec (.of k)) hk G.obj.X.hom) :
    IsAlgebraicStack.{u, w} C (Spec (.of k)) hk (classifyingStack C hk G).val :=
  let : ModObj G.obj.X (𝟙_ (Over (Space.terminalSpace C (Spec (.of k)) hk).obj)) :=
    ModObj.trivialAction _ _
  isAlgebraicStack_quotientStackOfAction (Space.terminalSpace C (Spec (.of k)) hk) G.obj.X
    (𝟙_ (Over (Space.terminalSpace C (Spec (.of k)) hk).obj)) G.property
    (Space.terminalSpace C (Spec (.of k)) hk).property hG

variable (𝒬 : AlgebraicStacks.{u, w} C (Spec (.of k)) hk)
  (e : StacksRepresentableCFG.EquivalenceOver (classifyingStack C hk G).val.p 𝒬.val.val.p)

/-- **The tautological chart `Spec k ⟶ BG`** of Stacks 044R, read on a model `𝒬` of the classifying
stack. -/
abbrev classifyingChart :
    algebraicSpaceStack.{u, w} C (Spec (.of k)) hk (classifyingGroupoid C hk G).objects.obj
        (classifyingGroupoid C hk G).objects.property ⟶ 𝒬 :=
  quotientStackModelProjection.{u, w} C (Spec (.of k)) hk
    (Space.terminalSpace C (Spec (.of k)) hk) (classifyingGroupoid C hk G) 𝒬 e

/-- **The tautological chart of the classifying stack of a smooth group is smooth** (Stacks 04X0):
the source map of the action groupoid is smooth, and relative smoothness passes from it to the
chart. -/
theorem isSmooth_classifyingChart (hG : Space.IsSmooth C (Spec (.of k)) hk G.obj.X.hom) :
    AlgebraicStacks.IsSmooth C (Spec (.of k)) hk (classifyingChart C hk G 𝒬 e) :=
  isSmooth_of_isRelativelySmooth C (Spec (.of k)) hk _
    ⟨isRepresentableByAlgebraicSpaces_quotientStackModelProjection _ 𝒬 e,
      hasRelativeProperty_quotientStackModelProjection _ 𝒬 e
        (Space.smoothMorphismProperty C (Spec (.of k)) hk)
        (isSmooth_classifyingGroupoid C hk G hG).1⟩

/-- The tautological chart of the classifying stack of a smooth group is locally of finite
type. -/
theorem isLocallyOfFiniteType_classifyingChart
    (hG : Space.IsSmooth C (Spec (.of k)) hk G.obj.X.hom) :
    AlgebraicStacks.IsLocallyOfFiniteType C (Spec (.of k)) hk (classifyingChart C hk G 𝒬 e) :=
  AlgebraicStacks.isLocallyOfFiniteType_of_isSmooth C (Spec (.of k)) hk _
    (isSmooth_classifyingChart C hk G 𝒬 e hG)

/-- **The tautological chart of the classifying stack is surjective** (Stacks 06FH, Stacks 04X0):
the identity arrow at a point of the object space is a preimage under the source map. -/
theorem isSurjective_classifyingChart (hG : Space.IsSmooth C (Spec (.of k)) hk G.obj.X.hom) :
    IsSurjective C (Spec (.of k)) hk (classifyingChart C hk G 𝒬 e) :=
  have hsm := isSmooth_classifyingGroupoid C hk G hG
  (quotientModelAtlasFppf (classifyingGroupoid C hk G) 𝒬 e
    (Space.isFlat_of_isSmooth C (Spec (.of k)) hk _ hsm.1)
    (Space.isFlat_of_isSmooth C (Spec (.of k)) hk _ hsm.2)
    (Space.isLocallyOfFinitePresentation_of_isSmooth C (Spec (.of k)) hk hsm.1)
    (Space.isLocallyOfFinitePresentation_of_isSmooth C (Spec (.of k)) hk hsm.2)).2.1

/-- The canonical field-valued point `Spec k ⟶ Spec k` of the algebraic space `Spec k`. -/
abbrev terminalFieldPoint :
    Space.FieldValuedPoint C (Spec (.of k)) hk (Space.terminalSpace C (Spec (.of k)) hk).obj where
  carrier := k
  contained := hk
  toBase := 𝟙 _
  value := 𝟙 _

/-- The algebraic space `Spec k`, represented by the base of the big fppf site of `Spec k`, has
exactly one point. -/
noncomputable instance unique_points_terminalSpace :
    Unique (Space.points C (Spec (.of k)) hk (Space.terminalSpace C (Spec (.of k)) hk).obj) where
  default := (terminalFieldPoint C hk).class C _ hk _
  uniq _x := (Space.subsingleton_points_yoneda_fieldSpec C (Spec (.of k)) hk k hk (𝟙 _)).elim _ _

/-- The points of an algebraic space equal to `Spec k` form a singleton. -/
theorem subsingleton_points_of_eq_terminalSpace {F : (BigFppfOver C (Spec (.of k)) hk)ᵒᵖ ⥤ Type u}
    (h : F = (Space.terminalSpace C (Spec (.of k)) hk).obj) :
    Subsingleton (Space.points C (Spec (.of k)) hk F) := by
  subst h; infer_instance

/-- The points of an algebraic space equal to `Spec k` are nonempty. -/
theorem nonempty_points_of_eq_terminalSpace {F : (BigFppfOver C (Spec (.of k)) hk)ᵒᵖ ⥤ Type u}
    (h : F = (Space.terminalSpace C (Spec (.of k)) hk).obj) :
    Nonempty (Space.points C (Spec (.of k)) hk F) := by
  subst h; infer_instance

/-- **Over the algebraic space `Spec k`, the relative dimension at a point is the dimension
there** (Stacks 0D4M), for any algebraic space equal to `Spec k`. -/
theorem hasRelativeDimensionAt_iff_dimensionAtPoint_of_eq_terminalSpace
    {F U : (BigFppfOver C (Spec (.of k)) hk)ᵒᵖ ⥤ Type u}
    (hF : IsAlgebraicSpace C (Spec (.of k)) hk F)
    (hU : U = (Space.terminalSpace C (Spec (.of k)) hk).obj) (f : F ⟶ U)
    (x : Space.points C (Spec (.of k)) hk F) (d : ℕ∞) :
    Space.HasRelativeDimensionAt d C (Spec (.of k)) hk f x ↔
      Space.dimensionAtPoint C (Spec (.of k)) hk F hF x = (d : WithBot ℕ∞) := by
  subst hU
  exact Space.relativeDimensionAt_fieldTarget_iff_dimensionAtPoint C (Spec (.of k)) hk hF
    (terminalFieldPoint C hk) f x d

/-- The dimension of an algebraic space is unchanged along an equality of presheaves. -/
theorem _root_.AlgebraicGeometry.Space.dimension_congr {B : BigFppfSite.{u}} {S : Scheme.{u}}
    {hS : B.Contains S} {F F' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (h : F = F')
    (hF : IsAlgebraicSpace B S hS F) (hF' : IsAlgebraicSpace B S hS F') :
    Space.dimension B S hS F hF = Space.dimension B S hS F' hF' := by
  subst h; rfl

/-- **The arrow space of the trivial action groupoid has, at every point, the dimension of the
group**: it is the group `G ×_{Spec k} Spec k`, and a group locally of finite type over a field
has constant dimension (Stacks 06FD). -/
theorem dimensionAtPoint_classifyingGroupoid_arrows
    (hG : Space.IsSmooth C (Spec (.of k)) hk G.obj.X.hom)
    (r : Space.points C (Spec (.of k)) hk (classifyingGroupoid C hk G).arrows.obj) :
    Space.dimensionAtPoint C (Spec (.of k)) hk (classifyingGroupoid C hk G).arrows.obj
        (classifyingGroupoid C hk G).arrows.property r =
      Space.dimension C (Spec (.of k)) hk G.obj.X.left G.property := by
  let : ModObj G.obj.X (𝟙_ (Over (Space.terminalSpace C (Spec (.of k)) hk).obj)) :=
    ModObj.trivialAction _ _
  let T := Space.terminalSpace C (Spec (.of k)) hk
  let H := Space.groupoidOfAction T G.obj.X (𝟙_ (Over T.obj)) G.property T.property
  have hsm := isSmooth_classifyingGroupoid C hk G hG
  have hd := Space.dimension_eq_dimensionAtPoint C (Spec (.of k)) hk hk (𝟙 (Spec (.of k)))
    H.groupoid H.objects_eq
    (Space.isLocallyOfFiniteType_of_isSmooth C (Spec (.of k)) hk hsm.1)
    (Space.isLocallyOfFiniteType_of_isSmooth C (Spec (.of k)) hk hsm.2) r
  rw [← hd]
  have harr : IsAlgebraicSpace C (Spec (.of k)) hk (pullback G.obj.X.hom (𝟙 T.obj)) :=
    isAlgebraicSpace_pullback C (Spec (.of k)) hk G.obj.X.hom (𝟙 T.obj) G.property
      T.property T.property
  have hars : H.groupoid.arrows.obj = pullback G.obj.X.hom (𝟙 T.obj) :=
    congrArg (fun Z => Z.obj) H.arrows_eq
  rw [Space.dimension_congr hars _ harr]
  exact Space.dimension_eq_of_iso C (Spec (.of k)) hk harr G.property
    (asIso (pullback.fst G.obj.X.hom (𝟙 T.obj)))

/-- **The tautological chart of the classifying stack has relative dimension `dim G`** at every
point, when `G` is smooth over `k` of dimension `n`. The self-intersection of the chart is the
arrow space `R = G` of the trivial action groupoid, with first projection the source map
(Stacks 04M9), so the relative dimension of the chart is that of the source map `R ⟶ Spec k`, which
over the field `k` is the dimension of `R`. -/
theorem relativeDimensionAt_classifyingChart
    (hG : Space.IsSmooth C (Spec (.of k)) hk G.obj.X.hom) (n : ℕ)
    (hn : Space.dimension C (Spec (.of k)) hk G.obj.X.left G.property = (n : WithBot ℕ∞))
    (s : Space.points C (Spec (.of k)) hk (classifyingGroupoid C hk G).objects.obj) :
    relativeDimensionAt.{u, w} C (Spec (.of k)) hk _ _ 𝒬 (classifyingChart C hk G 𝒬 e)
        (isLocallyOfFiniteType_classifyingChart C hk G 𝒬 e hG) s = (n : WithBot ℕ∞) := by
  classical
  let H := classifyingGroupoid C hk G
  let π := classifyingChart C hk G 𝒬 e
  have hπ := isLocallyOfFiniteType_classifyingChart C hk G 𝒬 e hG
  have hU := classifyingGroupoid_objects_obj C hk G
  have := subsingleton_points_of_eq_terminalSpace C hk hU
  obtain ⟨d, hd⟩ := exists_relativeDimensionAt_eq_natCast.{u, w} C (Spec (.of k)) hk _ _ 𝒬 π hπ s
  rw [hd]
  let Q := CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} π.hom π.hom
  have hQ := CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1}
    π.hom π.hom
  let eP := quotientStackModelArrowEquivalenceOver H 𝒬 e
  have hsrc : representingMap C (Spec (.of k)) hk Q.pt (fibredCategory C (Spec (.of k)) hk
      H.objects.obj) H.arrows.obj H.objects.obj eP
      (StacksRepresentableCFG.EquivalenceOver.refl _) Q.fst = H.source.hom :=
    representingMap_eq_source_of_obj_eq H 𝒬 e Q.fst (fun _ => rfl)
  have hsm := isSmooth_classifyingGroupoid C hk G hG
  have hlft : Space.IsLocallyOfFiniteType C (Spec (.of k)) hk H.source.hom :=
    Space.isLocallyOfFiniteType_of_isSmooth C (Spec (.of k)) hk hsm.1
  obtain ⟨z⟩ : Nonempty (Space.points C (Spec (.of k)) hk H.arrows.obj) := by
    obtain ⟨u⟩ := nonempty_points_of_eq_terminalSpace C hk hU
    obtain ⟨z, -⟩ := QuotientAtlas.isSurjective_source H u
    exact ⟨z⟩
  have h₁ := hasRelativeDimensionAt_representingMap_fst_of_relativeDimensionAt.{u, w}
    C (Spec (.of k)) hk H.objects.obj H.objects.obj H.objects.property H.objects.property 𝒬 π π
    hπ hQ ⟨H.arrows.obj, H.arrows.property, ⟨eP⟩⟩ H.arrows.obj H.arrows.property eP
    (hsrc ▸ hlft) z s (Subsingleton.elim _ _) d hd
  rw [hsrc] at h₁
  have h₂ : Space.HasRelativeDimensionAt (n : ℕ∞) C (Spec (.of k)) hk H.source.hom z :=
    (hasRelativeDimensionAt_iff_dimensionAtPoint_of_eq_terminalSpace C hk H.arrows.property hU
      H.source.hom z n).2 ((dimensionAtPoint_classifyingGroupoid_arrows C hk G hG z).trans hn)
  have := Space.eq_of_hasRelativeDimensionAt C (Spec (.of k)) hk H.arrows.property
    H.objects.property H.source.hom z h₁ h₂
  exact_mod_cast this

end AlgebraicGeometry.Stack

end
