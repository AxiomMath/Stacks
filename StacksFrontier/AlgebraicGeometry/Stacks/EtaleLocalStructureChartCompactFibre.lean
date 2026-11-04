module

public import StacksFrontier.AlgebraicGeometry.Groupoids.Slicing.GroupoidInverse
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.Quotient.QuotientStackSeparation
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.QuasiCompact
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleRepresentableBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.EtaleLocalStructureResidualGerbe
public import StacksFrontier.AlgebraicGeometry.Stacks.EtaleLocalStructureStabilizerFinite
public import StacksFrontier.AlgebraicGeometry.Stacks.FiniteTypePointsMorphism
public import StacksFrontier.AlgebraicGeometry.Stacks.MonomorphismDeligneMumford
public import StacksFrontier.AlgebraicGeometry.Stacks.QuotientStackSubgroupoidSelfProduct
public import StacksFrontier.AlgebraicGeometry.Stacks.SitePullbackStackSquare
public import StacksFrontier.CategoryTheory.TwoFibreProduct.CospanReindex

/-!
# The fibre of a quotient chart over a residue field point is quasi-compact

The step of the proof of **Stacks 0DU5** which reads "consider the cartesian diagram
`F = U ×_𝒳 u`; since `U` is an affine scheme and `F ⟶ U` is quasi-compact, we see that `F` is
quasi-compact". Here `[U/R] ⟶ 𝒳` is a quotient chart of an algebraic stack
(`AlgebraicGeometry.Stack.EtaleLocalStructure.ChartGroupoid`), `u ∈ U` is a point of the affine
object scheme and `u = Spec κ(u) ⟶ 𝒳` is quasi-compact by the hypothesis of Stacks 0DU5 read
through **Stacks 0DTK**. The scheme `F` is the fibre of the target map `t : R ⟶ U` of the
groupoid over `u`, so what the step delivers is the `CompactSpace` instance that Situation 04RL
(`AlgebraicGeometry.Space.exists_isAffine_strongSplitting_of_compactSpace_targetFibre`) consumes.

## Main definitions

* `AlgebraicGeometry.Stack.EtaleLocalStructure.ChartGroupoid.residuePointObj` and
  `...residuePointMap`: the spectrum of the residue field at the chart point, and the point
  itself, as an object and a morphism of the site over `S`.
* `AlgebraicGeometry.Stack.EtaleLocalStructure.ChartGroupoid.targetFibreObj` and
  `...targetFibreToObjects`: the fibre of the target map over that point, as an object of the
  site, together with its morphism to the object scheme through the source map.

## Main results

* `Stack.EtaleLocalStructure.ChartGroupoid.compactSpace_targetFibre_of_isQuasiCompact`:
  the reduction of the step to quasi-compactness of `F ⟶ U` as a morphism of algebraic spaces.
* `AlgebraicGeometry.Stack.exists_chartGroupoid_compactSpace_targetFibre_of_isTwoFibreProduct`:
  the conclusion the proof of Stacks 0DU5 consumes, from a presentation of `F` as the 2-fibre
  product of the chart against a field-valued representative of the point.
* `Stack.exists_chartGroupoid_compactSpace_targetFibre_of_isTwoFibreProduct_of_isMonomorphism`:
  the same, asking for the 2-fibre product only over an algebraic stack admitting a
  monomorphism to `𝒳` — which is where the chart construction of Stacks 0DU3 lands, the image
  open substack of the affine chart of `𝒳`.
* `AlgebraicGeometry.compactSpace_pullback_target_of_source`: the fibre of the target map of a
  groupoid scheme over a point is compact as soon as the fibre of the source map is, the
  groupoid inverse exchanging the two.
* `AlgebraicGeometry.Stack.isQuasiCompactFieldValuedPoint_of_isMonomorphism`: **Stacks 050Y** at
  a monomorphism — a field-valued point of the source of a monomorphism of algebraic stacks is
  quasi-compact as soon as its image is.
* `AlgebraicGeometry.Stack.isQuasiCompactMorphism_congr`: quasi-compactness of a 1-morphism of
  algebraic stacks is invariant under 2-isomorphism.
* `Stack.EtaleLocalStructure.ChartGroupoid.isTwoFibreProduct_targetFibreStackSquare`:
  the fibre is the 2-fibre product of the residue field point with the target map, which is the
  inner square of the pasting that presents `F` as `U ×_𝒳 Spec κ(u)`.

## Implementation notes

The object of the site presenting `F` is `AlgebraicGeometry.Stack.sitePullbackObj` at the
residue field point and the target map, whose underlying scheme is the fibre product of the
underlying schemes *on the nose*; so the `CompactSpace` statement about
`CategoryTheory.Limits.pullback` that the consumer asks for needs no transport along an
isomorphism of schemes, and neither does the identification of the underlying scheme of `U` with
`K.groupoid.objects.left`.

Quasi-compactness of morphisms of schemes is **not** étale local on the source — the tree has no
`AlgebraicGeometry.IsEtaleLocalOnSourceAndTarget` instance for it, and cannot have one — so
`AlgebraicGeometry.Space.holdsOnEveryEtaleChart_yoneda_map_iff` is unavailable at it. The passage
from the morphism of representable algebraic spaces to the morphism of schemes is instead
**Stacks 03HD**, `AlgebraicGeometry.Space.presheaf_quasiCompact_of_isQuasiCompact` followed by
`AlgebraicGeometry.BigFppfOver.presheaf_inverseImage_yoneda_map_iff`, the representability
hypothesis of the first being `AlgebraicGeometry.Space.relativelyRepresentable_yoneda_map`.

## References

* [Stacks Project, Tag 03HD](https://stacks.math.columbia.edu/tag/03HD)
* [Stacks Project, Tag 04RL](https://stacks.math.columbia.edu/tag/04RL)
* [Stacks Project, Tag 0DTK](https://stacks.math.columbia.edu/tag/0DTK)
* [Stacks Project, Tag 0DU5](https://stacks.math.columbia.edu/tag/0DU5)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u w

namespace AlgebraicGeometry

/-- **Replacing the second leg of a fibre product by an isomorphic one.** If `i` is an
isomorphism then `X ×_Z W` along `i ≫ g` is `X ×_Z Y` along `g`, by transporting the second
projection along `i`. -/
noncomputable def pullbackCompIsoOfIsIso {X Z W Y : Scheme.{u}} (y : X ⟶ Z) (i : W ⟶ Y)
    [IsIso i] (g : Y ⟶ Z) : pullback y (i ≫ g) ≅ pullback y g where
  hom := pullback.lift (pullback.fst y (i ≫ g)) (pullback.snd y (i ≫ g) ≫ i)
    (by rw [Category.assoc]; exact pullback.condition)
  inv := pullback.lift (pullback.fst y g) (pullback.snd y g ≫ inv i)
    (by rw [Category.assoc, IsIso.inv_hom_id_assoc]; exact pullback.condition)
  hom_inv_id := by
    refine pullback.hom_ext ?_ ?_
    · simp only [Category.assoc, pullback.lift_fst, Category.id_comp]
    · simp only [Category.assoc, pullback.lift_snd, Category.id_comp]
      rw [← Category.assoc, pullback.lift_snd, Category.assoc, IsIso.hom_inv_id,
        Category.comp_id]
  inv_hom_id := by
    refine pullback.hom_ext ?_ ?_
    · simp only [Category.assoc, pullback.lift_fst, Category.id_comp]
    · simp only [Category.assoc, pullback.lift_snd, Category.id_comp]
      rw [← Category.assoc, pullback.lift_snd, Category.assoc, IsIso.inv_hom_id,
        Category.comp_id]

/-- **The fibre of the target map of a groupoid scheme over a point is compact as soon as the
fibre of the source map over that point is.** The inverse of the groupoid is an isomorphism of
the arrow scheme (`AlgebraicGeometry.groupoidInverse_left_isIso`) and the groupoid identity
`Stacks.Groupoids.GroupoidScheme.source_inverse` writes the target map as that isomorphism
followed by the source map, so the two fibres are isomorphic schemes.

This is what makes the source and the target version of the quasi-compactness step of
Stacks 0DU5 interchangeable: whichever of the two legs a presentation of the fibre as a 2-fibre
product happens to produce, the statement Situation 04RL
(`AlgebraicGeometry.Space.exists_isAffine_strongSplitting_of_compactSpace_targetFibre`) asks for
is available. -/
theorem compactSpace_pullback_target_of_source {S : Scheme.{u}}
    (G : Stacks.Groupoids.GroupoidScheme S) (u : G.objects.left)
    (h : CompactSpace ↑(pullback (G.objects.left.fromSpecResidueField u) G.source.left)) :
    CompactSpace ↑(pullback (G.objects.left.fromSpecResidueField u) G.target.left) := by
  have := groupoidInverse_left_isIso G
  rw [show G.target.left = G.inverse.left ≫ G.source.left by
    rw [← Over.comp_left, G.source_inverse]]
  exact @QuasiCompact.compactSpace_of_compactSpace _ _
    (pullbackCompIsoOfIsIso (G.objects.left.fromSpecResidueField u) G.inverse.left
      G.source.left).hom inferInstance h

end AlgebraicGeometry

namespace AlgebraicGeometry.Stack.EtaleLocalStructure.ChartGroupoid

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {𝒳 : AlgebraicStacks.{u, w} B S hS} (K : ChartGroupoid B S hS 𝒳)
  (z : Space.points B S hS (yoneda.obj K.U))

/-- The spectrum of the residue field of the object scheme of a quotient chart at the point
underlying `z`, as an object of the site over `S`. It is contained in the site because the
morphism from it is a quasi-compact monomorphism. -/
noncomputable def residuePointObj : BigFppfOver B S hS :=
  Space.schemeSiteObject B hS
    (X := Over.mk (K.groupoid.objects.left.fromSpecResidueField
      (Space.pointsToScheme B S hS K.U z) ≫ K.groupoid.objects.hom))
    (BigFppfSite.residueField_spec_contains B K.contains_objects _)

/-- The residue field point of the object scheme of a quotient chart at the point underlying `z`,
as a morphism of the site over `S`. -/
noncomputable def residuePointMap : residuePointObj K z ⟶ K.U :=
  Space.schemeSiteMap B hS _ K.contains_objects
    (Over.homMk (K.groupoid.objects.left.fromSpecResidueField
      (Space.pointsToScheme B S hS K.U z)))

/-- The underlying morphism of schemes of
`AlgebraicGeometry.Stack.EtaleLocalStructure.ChartGroupoid.residuePointMap` is the canonical
morphism from the spectrum of the residue field. -/
theorem toScheme_map_residuePointMap :
    (BigFppfOver.toScheme B S hS).map (residuePointMap K z) =
      K.groupoid.objects.left.fromSpecResidueField
        (Space.pointsToScheme B S hS K.U z) := rfl

/-- The fibre `F = Spec κ(u) ×_{U, t} R` of the target map of a quotient chart over the residue
field point at `z`, as an object of the site over `S`. -/
noncomputable def targetFibreObj : BigFppfOver B S hS :=
  sitePullbackObj B S hS (residuePointMap K z) K.t

/-- The underlying scheme of
`AlgebraicGeometry.Stack.EtaleLocalStructure.ChartGroupoid.targetFibreObj` is the fibre product
of the underlying schemes, which is the shape in which Situation 04RL asks for it. -/
theorem toScheme_obj_targetFibreObj :
    (BigFppfOver.toScheme B S hS).obj (targetFibreObj K z) =
      pullback (K.groupoid.objects.left.fromSpecResidueField
        (Space.pointsToScheme B S hS K.U z)) K.groupoid.target.left := rfl

/-- **The fibre of the target map over the residue field point is the 2-fibre product of the
residue field point with the target map, in the 2-category of algebraic stacks over `S`.** The
apex of the square is `schemeStack` of
`AlgebraicGeometry.Stack.EtaleLocalStructure.ChartGroupoid.targetFibreObj` on the nose, so this
is the inner square of the pasting that presents `F` as `U ×_𝒳 Spec κ(u)`, and it costs nothing:
the fibre product of objects of the site represents the 2-fibre product of the stacks they
represent. -/
noncomputable def isTwoFibreProduct_targetFibreStackSquare :
    Bicategory.IsTwoFibreProduct
      (schemeStackSquare.{u, w} B S hS
        (isPullback_sitePullback B S hS (residuePointMap K z) K.t).w) :=
  isTwoFibreProduct_schemeStackSquare.{u, w} B S hS
    (isPullback_sitePullback B S hS (residuePointMap K z) K.t)

/-- The apex of `...isTwoFibreProduct_targetFibreStackSquare` is the algebraic stack of
`...targetFibreObj`. -/
theorem pt_targetFibreStackSquare :
    (schemeStackSquare.{u, w} B S hS
        (isPullback_sitePullback B S hS (residuePointMap K z) K.t).w).pt =
      schemeStack.{u, w} B S hS (targetFibreObj K z) := rfl

/-- The morphism from the fibre of the target map to the object scheme of a quotient chart, given
by the second projection followed by the source map. This is the morphism `F ⟶ U` of the proof of
Stacks 0DU5. -/
noncomputable def targetFibreToObjects : targetFibreObj K z ⟶ K.U :=
  sitePullbackSnd B S hS (residuePointMap K z) K.t ≫ K.s

/-- **The fibre of the target map over a residue field point is quasi-compact as soon as its
morphism to the object scheme is.** The object scheme of a quotient chart is affine, hence a
compact space, and quasi-compactness of a morphism of schemes with compact target gives a compact
source.

This is the reduction of the step "since `U` is an affine scheme and `F ⟶ U` is quasi-compact, we
see that `F` is quasi-compact" of the proof of Stacks 0DU5 to the quasi-compactness of `F ⟶ U`.
The morphism of representable algebraic spaces is read on the underlying schemes by
**Stacks 03HD**. -/
theorem compactSpace_targetFibre_of_isQuasiCompact
    (h : Space.IsQuasiCompact B S hS (yoneda.map (targetFibreToObjects K z))) :
    CompactSpace ↑(pullback (K.groupoid.objects.left.fromSpecResidueField
      (Space.pointsToScheme B S hS K.U z)) K.groupoid.target.left) := by
  have := K.isAffine_U
  have hqc : QuasiCompact ((BigFppfOver.toScheme B S hS).map (targetFibreToObjects K z)) :=
    (BigFppfOver.presheaf_inverseImage_yoneda_map_iff B S hS
      (@AlgebraicGeometry.QuasiCompact.{u}) (targetFibreToObjects K z)).1
      (Space.presheaf_quasiCompact_of_isQuasiCompact B S hS
        (Space.relativelyRepresentable_yoneda_map B S hS _) h)
  exact @QuasiCompact.compactSpace_of_compactSpace _ _
    ((BigFppfOver.toScheme B S hS).map (targetFibreToObjects K z)) hqc
    (Scheme.compactSpace_of_isAffine _)

end AlgebraicGeometry.Stack.EtaleLocalStructure.ChartGroupoid

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **A quotient chart with quasi-compact fibre over its chart point, from quasi-compactness of
the fibre's morphism to the object scheme.** This is
`AlgebraicGeometry.Stack.EtaleLocalStructure.exists_chartGroupoid` — the quotient chart of
Stacks 0DU3 through a given point — strengthened by the conclusion of
`EtaleLocalStructure.ChartGroupoid.compactSpace_targetFibre_of_isQuasiCompact`,
which is the shape in which the proof of Stacks 0DU5 consumes it.

The hypothesis `hQcFibre` is the step of the proof of Stacks 0DU5 that says `F ⟶ U` is
quasi-compact because `u = Spec κ(u) ⟶ 𝒳` is: it is *not* a Stacks result taken for granted here
but the one input this statement still carries, and
`AlgebraicGeometry.Stack.exists_chartGroupoid_compactSpace_targetFibre` is the form with it
discharged. -/
theorem exists_chartGroupoid_compactSpace_targetFibre_of_isQuasiCompact
    (𝒳 : AlgebraicStacks.{u, w} B S hS)
    (hQ : AlgebraicStacks.IsAbsolutelyQuasiDM B S hS B.contains_terminal 𝒳)
    (hΔ : Stack.IsSeparated.{u, u, u + 1} B S hS
      (relativeDiagonal.{u, u, u + 1} B S hS 𝒳.val
        (schemeStack.{u, w} B S hS (Over.mk (𝟙 (B.obj hS)))).val
        (structureMorphism B S hS 𝒳).hom))
    (x : AlgebraicStacks.points B S hS 𝒳)
    (hQcFibre : ∀ (K : EtaleLocalStructure.ChartGroupoid B S hS 𝒳)
      (z : Space.points B S hS (yoneda.obj K.U)),
      AlgebraicStacks.pointsMap B S hS K.map (K.point z) = x →
      Space.IsQuasiCompact B S hS
        (yoneda.map (EtaleLocalStructure.ChartGroupoid.targetFibreToObjects K z))) :
    ∃ (K : EtaleLocalStructure.ChartGroupoid B S hS 𝒳)
      (z : Space.points B S hS (yoneda.obj K.U)),
      AlgebraicStacks.pointsMap B S hS K.map (K.point z) = x ∧
      CompactSpace ↑(pullback (K.groupoid.objects.left.fromSpecResidueField
        (Space.pointsToScheme B S hS K.U z)) K.groupoid.target.left) := by
  obtain ⟨K, z, hz⟩ := EtaleLocalStructure.exists_chartGroupoid 𝒳 hQ hΔ x
  exact ⟨K, z, hz,
    EtaleLocalStructure.ChartGroupoid.compactSpace_targetFibre_of_isQuasiCompact K z
      (hQcFibre K z hz)⟩

/-- The fibre of the target map over the chart point is compact once the representing map of
the first leg of a 2-fibre product square over a quasi-compact field-valued point is
`targetFibreToObjects`. -/
private theorem compactSpace_targetFibre_of_representingMap
    {𝒴 𝒳 : AlgebraicStacks.{u, w} B S hS} {K : EtaleLocalStructure.ChartGroupoid B S hS 𝒳}
    {z : Space.points B S hS (yoneda.obj K.U)} {p : FieldValuedPoint B S hS 𝒴.val.val}
    (hqcp : IsQuasiCompactFieldValuedPoint B S hS 𝒴.val p)
    {g : schemeFibredCategory B S hS K.U ⟶ 𝒴.val}
    {Q : Bicategory.TwoCommSq g (fieldValuedPointMorphism B S hS 𝒴.val p)}
    (hQ : Bicategory.IsTwoFibreProduct Q)
    {eF : StacksRepresentableCFG.EquivalenceOver Q.pt.val.p
      (presheafOfCategories
        (yoneda.obj (EtaleLocalStructure.ChartGroupoid.targetFibreObj K z) ⋙ typeToCat)).p}
    (hrep : representingMap B S hS Q.pt (schemeFibredCategory B S hS K.U)
          (yoneda.obj (EtaleLocalStructure.ChartGroupoid.targetFibreObj K z))
          (yoneda.obj K.U) eF (representedChart B S hS K.U) Q.fst
        = yoneda.map (EtaleLocalStructure.ChartGroupoid.targetFibreToObjects K z)) :
    CompactSpace ↑(pullback (K.groupoid.objects.left.fromSpecResidueField
      (Space.pointsToScheme B S hS K.U z)) K.groupoid.target.left) := by
  refine EtaleLocalStructure.ChartGroupoid.compactSpace_targetFibre_of_isQuasiCompact K z ?_
  rw [← hrep]
  exact prop_representingMap_of_hasRelativeProperty.{u, u + 1} B S hS
    (Space.quasiCompactProperty B S hS) (fieldValuedPointMorphism B S hS 𝒴.val p)
    (isRepresentableByAlgebraicSpaces_fieldValuedPointMorphism.{u, w} B S hS 𝒴 p) hqcp.2
    (schemeFibredCategory B S hS K.U) g Q hQ _ _
    (isAlgebraicSpace_yoneda B S hS _) (isAlgebraicSpace_yoneda B S hS _)
    eF (representedChart B S hS K.U)

/-- **A quotient chart with quasi-compact fibre over its chart point, from a presentation of the
fibre as a 2-fibre product.** This is the conclusion the proof of Stacks 0DU5 consumes, derived
from the hypothesis `hSq` that the fibre of the groupoid's target map over the chart point
presents the 2-fibre product `U ×_𝒳 Spec κ(u)` of the chart against a field-valued
representative of `x`.

The field-valued representative `p` of `hSq` need not be the quasi-compact one: **Stacks 0DTK**
(`AlgebraicGeometry.Stack.exists_isQuasiCompactFieldValuedPoint_iff_forall`) makes
quasi-compactness a property of the point rather than of the representative, so the
representative supplied by `hqc` and the one appearing in the square need not agree. **Stacks
04XC** (`AlgebraicGeometry.Stack.prop_representingMap_of_hasRelativeProperty`) then reads the
Stacks 04XB property of that representative's 1-morphism off the morphism of representing
presheaves of the square's first leg, which `hSq` identifies with the Yoneda image of
`AlgebraicGeometry.Stack.EtaleLocalStructure.ChartGroupoid.targetFibreToObjects`. -/
theorem exists_chartGroupoid_compactSpace_targetFibre_of_isTwoFibreProduct
    (𝒳 : AlgebraicStacks.{u, w} B S hS)
    (x : AlgebraicStacks.points B S hS 𝒳)
    (hqc : ∃ p : FieldValuedPoint B S hS 𝒳.val.val,
      pointClass B S hS 𝒳.val.val 𝒳.val.isFiberedInGroupoids p = x ∧
        IsQuasiCompactFieldValuedPoint B S hS 𝒳.val p)
    (hSq : ∃ (K : EtaleLocalStructure.ChartGroupoid B S hS 𝒳)
      (z : Space.points B S hS (yoneda.obj K.U))
      (p : FieldValuedPoint B S hS 𝒳.val.val)
      (g : schemeFibredCategory B S hS K.U ⟶ 𝒳.val)
      (Q : Bicategory.TwoCommSq g (fieldValuedPointMorphism B S hS 𝒳.val p))
      (_hQ : Bicategory.IsTwoFibreProduct Q)
      (eF : StacksRepresentableCFG.EquivalenceOver Q.pt.val.p
        (presheafOfCategories
          (yoneda.obj (EtaleLocalStructure.ChartGroupoid.targetFibreObj K z) ⋙ typeToCat)).p),
      AlgebraicStacks.pointsMap B S hS K.map (K.point z) = x ∧
      pointClass B S hS 𝒳.val.val 𝒳.val.isFiberedInGroupoids p = x ∧
      representingMap B S hS Q.pt (schemeFibredCategory B S hS K.U)
          (yoneda.obj (EtaleLocalStructure.ChartGroupoid.targetFibreObj K z))
          (yoneda.obj K.U) eF (representedChart B S hS K.U) Q.fst
        = yoneda.map (EtaleLocalStructure.ChartGroupoid.targetFibreToObjects K z)) :
    ∃ (K : EtaleLocalStructure.ChartGroupoid B S hS 𝒳)
      (z : Space.points B S hS (yoneda.obj K.U)),
      AlgebraicStacks.pointsMap B S hS K.map (K.point z) = x ∧
      CompactSpace ↑(pullback (K.groupoid.objects.left.fromSpecResidueField
        (Space.pointsToScheme B S hS K.U z)) K.groupoid.target.left) := by
  obtain ⟨K, z, p, g, Q, hQ, eF, hz, hp, hrep⟩ := hSq
  have hqcp : IsQuasiCompactFieldValuedPoint B S hS 𝒳.val p :=
    (exists_isQuasiCompactFieldValuedPoint_iff_forall.{u, w} B S hS 𝒳 x).1 hqc p hp
  exact ⟨K, z, hz, compactSpace_targetFibre_of_representingMap B S hS hqcp hQ hrep⟩

/-- **Quasi-compactness of a 1-morphism of algebraic stacks over `S` is invariant under
2-isomorphism.** Reindexing the second leg of a cospan by an invertible 2-cell
(`CategoryTheory.Bicategory.isTwoFibreProduct_reindexSnd`) leaves the apex of the canonical
2-fibre product square unchanged, and quasi-compactness of an algebraic stack passes between any
two 2-fibre products of one cospan. -/
theorem isQuasiCompactMorphism_congr {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} {f f' : 𝒳 ⟶ 𝒴}
    (e : f ≅ f') (h : IsQuasiCompactMorphism.{u, w} B S hS f) :
    IsQuasiCompactMorphism.{u, w} B S hS f' := by
  intro 𝒵 k h𝒵
  exact isQuasiCompactStack_of_isTwoFibreProduct B S hS
    (Bicategory.isTwoFibreProduct_reindexSnd e
      (isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS k f))
    (isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS k f')
    (h 𝒵 k h𝒵)

/-- **A field-valued point of the source of a monomorphism of algebraic stacks is quasi-compact
as soon as its image is.** A monomorphism is separated, hence quasi-separated (**Stacks 06MY**
and **Stacks 050E** part (1), through
`AlgebraicGeometry.Stack.AlgebraicStacks.isQuasiSeparated_of_isMonomorphism`), and the
1-morphism of the image of a field-valued point is the composite of the point's own 1-morphism
with the monomorphism (`AlgebraicGeometry.Stack.fieldValuedPointStackMorphism_comp_iso`), so
**Stacks 050Y** removes the second factor.

This is what lets a presentation of the chart fibre over an open substack of `𝒳` serve a
hypothesis of quasi-compactness stated at a point of `𝒳` itself: the quasi-compact
representative lives on `𝒳`, the 2-fibre product square lives on the substack, and this moves
the former to where the latter is. -/
theorem isQuasiCompactFieldValuedPoint_of_isMonomorphism
    {𝒴 𝒳 : AlgebraicStacks.{u, w} B S hS} (m : 𝒴 ⟶ 𝒳)
    (hm : AlgebraicStacks.IsMonomorphism B S hS m)
    (p : FieldValuedPoint B S hS 𝒴.val.val)
    (h : IsQuasiCompactFieldValuedPoint B S hS 𝒳.val
      (fieldValuedPointMap B S hS 𝒴.val.val m.hom.hom p)) :
    IsQuasiCompactFieldValuedPoint B S hS 𝒴.val p := by
  refine (isQuasiCompactFieldValuedPoint_iff_isQuasiCompactMorphism.{u, w} B S hS 𝒴 p).2
    (isQuasiCompactMorphism_of_comp_of_isQuasiSeparated B S hS
      (fieldValuedPointStackMorphism.{u, w} B S hS 𝒴 p) m ?_
      (AlgebraicStacks.isQuasiSeparated_of_isMonomorphism B S hS m hm))
  exact isQuasiCompactMorphism_congr B S hS
    (Bicategory.InducedBicategory.isoMk
      (fieldValuedPointStackMorphism_comp_iso.{u, w} B S hS m p)).symm
    ((isQuasiCompactFieldValuedPoint_iff_isQuasiCompactMorphism.{u, w} B S hS 𝒳 _).1 h)

/-- **A quotient chart with quasi-compact fibre over its chart point, from a presentation of the
fibre as a 2-fibre product over a substack.** The conclusion the proof of Stacks 0DU5 consumes,
stated over `𝒳` and with `x` a point of `𝒳`, but asking for the 2-fibre product only over an
algebraic stack `𝒴` admitting a monomorphism to `𝒳` — which is where the chart construction of
Stacks 0DU3 lands, the image open substack of the affine chart.

The quasi-compact representative supplied by `hqc` lives on `𝒳`. **Stacks 0DTK** moves
quasi-compactness to the image under `m` of the representative `p` appearing in the square, and
`AlgebraicGeometry.Stack.isQuasiCompactFieldValuedPoint_of_isMonomorphism` — **Stacks 050Y** at
a monomorphism — then moves it down to `p` itself, after which **Stacks 04XC** reads it off the
morphism of representing presheaves exactly as in
`AlgebraicGeometry.Stack.exists_chartGroupoid_compactSpace_targetFibre_of_isTwoFibreProduct`. -/
theorem exists_chartGroupoid_compactSpace_targetFibre_of_isTwoFibreProduct_of_isMonomorphism
    (𝒳 : AlgebraicStacks.{u, w} B S hS)
    (x : AlgebraicStacks.points B S hS 𝒳)
    (hqc : ∃ p : FieldValuedPoint B S hS 𝒳.val.val,
      pointClass B S hS 𝒳.val.val 𝒳.val.isFiberedInGroupoids p = x ∧
        IsQuasiCompactFieldValuedPoint B S hS 𝒳.val p)
    (hSq : ∃ (𝒴 : AlgebraicStacks.{u, w} B S hS) (m : 𝒴 ⟶ 𝒳)
      (_hm : AlgebraicStacks.IsMonomorphism B S hS m)
      (K : EtaleLocalStructure.ChartGroupoid B S hS 𝒳)
      (z : Space.points B S hS (yoneda.obj K.U))
      (p : FieldValuedPoint B S hS 𝒴.val.val)
      (g : schemeFibredCategory B S hS K.U ⟶ 𝒴.val)
      (Q : Bicategory.TwoCommSq g (fieldValuedPointMorphism B S hS 𝒴.val p))
      (_hQ : Bicategory.IsTwoFibreProduct Q)
      (eF : StacksRepresentableCFG.EquivalenceOver Q.pt.val.p
        (presheafOfCategories
          (yoneda.obj (EtaleLocalStructure.ChartGroupoid.targetFibreObj K z) ⋙ typeToCat)).p),
      AlgebraicStacks.pointsMap B S hS K.map (K.point z) = x ∧
      pointClass B S hS 𝒳.val.val 𝒳.val.isFiberedInGroupoids
          (fieldValuedPointMap B S hS 𝒴.val.val m.hom.hom p) = x ∧
      representingMap B S hS Q.pt (schemeFibredCategory B S hS K.U)
          (yoneda.obj (EtaleLocalStructure.ChartGroupoid.targetFibreObj K z))
          (yoneda.obj K.U) eF (representedChart B S hS K.U) Q.fst
        = yoneda.map (EtaleLocalStructure.ChartGroupoid.targetFibreToObjects K z)) :
    ∃ (K : EtaleLocalStructure.ChartGroupoid B S hS 𝒳)
      (z : Space.points B S hS (yoneda.obj K.U)),
      AlgebraicStacks.pointsMap B S hS K.map (K.point z) = x ∧
      CompactSpace ↑(pullback (K.groupoid.objects.left.fromSpecResidueField
        (Space.pointsToScheme B S hS K.U z)) K.groupoid.target.left) := by
  obtain ⟨𝒴, m, hm, K, z, p, g, Q, hQ, eF, hz, hp, hrep⟩ := hSq
  have hqcp : IsQuasiCompactFieldValuedPoint B S hS 𝒴.val p :=
    isQuasiCompactFieldValuedPoint_of_isMonomorphism.{u, w} B S hS m hm p
      ((exists_isQuasiCompactFieldValuedPoint_iff_forall.{u, w} B S hS 𝒳 x).1 hqc _ hp)
  exact ⟨K, z, hz, compactSpace_targetFibre_of_representingMap B S hS hqcp hQ hrep⟩

end AlgebraicGeometry.Stack

end
