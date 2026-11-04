module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.PointsOfFibresFiniteDecent
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeDimensionFiniteness
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeEtale
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeEtaleComposition
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertySpaceBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.DeligneMumfordStack
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalPropertyAtlasSpace
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalMorphismRelative
public import StacksFrontier.AlgebraicGeometry.Stacks.SurjectiveProperties
public import StacksFrontier.AlgebraicGeometry.Stacks.PointsSurjective
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeNormalization
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.GenericPointsAndDimension
public import StacksFrontier.AlgebraicGeometry.Spaces.DimensionEtaleInvariance
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.EtaleLocalProperty
public import StacksFrontier.AlgebraicGeometry.Descent.LocalProperties.Noetherian
public import StacksFrontier.AlgebraicGeometry.Stacks.PointsQuotientOfAtlas
public import StacksFrontier.AlgebraicGeometry.Stacks.FiniteTypePointSmoothChart
public import StacksFrontier.AlgebraicGeometry.Stacks.DecentStackKolmogorov
public import StacksFrontier.AlgebraicGeometry.Stacks.NoetherianPointsAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.SpecializationSmoothChart
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.Dimension
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.PropertyGammaPermanence
public import StacksFrontier.Topology.Dimension.OpenGeneralizingMap
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiSeparatedDecent

/-!
# The dimension of a Deligne-Mumford stack is the dimension of its point space

Stacks Remark 0DRK records that for Deligne-Mumford stacks which are suitably decent, for
instance quasi-separated, the dimension `dim_x(𝒳)` of Stacks 0AFN at a point `x ∈ |𝒳|` coincides
with the topologically defined quantity `dim_x |𝒳|`, the local Krull dimension of the space of
points; this is the analogue for stacks of Stacks 0A4J for decent algebraic spaces. This file
proves that assertion for a locally Noetherian Deligne-Mumford stack which is decent in the sense
of Stacks 0GW1, and hence (Stacks 0GW2) for one which is quasi-separated.

The proof runs along an étale chart `c : W ⟶ 𝒳` by a scheme. Its fibres over field-valued points
are étale over a field, so its relative dimension (Stacks 0DRG) vanishes, and the dimension
formula of Stacks 0DRJ identifies `dim_x(𝒳)` with `dim_t(W) = dim_t |W|` for any `t` above `x`.
The map `|W| ⟶ |𝒳|` is then compared with the topology of `|𝒳|` exactly as in the proof of
Stacks 0A4J: it is continuous and open, generizations lift along it, and it collapses no
specialization, and these properties identify local Krull dimensions on sober spaces.

## Main results

* `AlgebraicGeometry.Stack.relativeDimensionAt_eq_zero_of_isRelativelyEtale`: an étale
  1-morphism from an algebraic space has relative dimension `0` at every point.
* `AlgebraicGeometry.Stack.exists_etale_chart_of_isDeligneMumfordStack`: a Deligne-Mumford stack
  has an étale, smooth chart by the algebraic space of a scheme, surjective on points.
* `AlgebraicGeometry.Stack.eq_of_specializes_of_spacePointMap_eq_of_isRelativelyEtale`: the
  analogue for locally Noetherian algebraic stacks of Stacks 03K5 and Stacks 0H1Q, that an étale
  chart carries no nontrivial specialization inside a fibre.
* `AlgebraicGeometry.Stack.dimensionAtPoint_eq_topologicalKrullDimAt_of_isDeligneMumfordStack`:
  **Stacks 0DRK**, the Deligne-Mumford assertion, for decent stacks.
* `Stack.dimensionAtPoint_eq_topologicalKrullDimAt_of_isDeligneMumfordStack_of_quasiSeparated`:
  **Stacks 0DRK**, the same for quasi-separated stacks, the example the remark names.

## Implementation notes

The remark gives no proof; the decency hypothesis is the one Stacks 0A4J uses for spaces, and it
enters twice, through Stacks 0GVZ (lifting of generizations, which needs quasi-compact
representatives of points) and Stacks 0GW7 (the Kolmogorov property of `|𝒳|`). The collapse of
specializations is excluded through local Noetherianity rather than through finiteness of
fibres: two points of `W` with one image are the two projections of a point of `W ×_𝒳 W`, whose
projections are étale, so their local rings have the same dimension (Stacks 04N8), and on a
locally Noetherian scheme a specialization between such points is trivial. Local Noetherianity
is in any case presupposed by Stacks 0AFN.

`AlgebraicGeometry.Stack.dimensionAtPoint` takes values in the extended integers while the local
Krull dimension takes values in `WithBot ℕ∞`; the comparison is through
`AlgebraicGeometry.Stack.dimensionSubNat` at `0`, which is the inclusion.

## References

* [Stacks Project, Tag 0DRK](https://stacks.math.columbia.edu/tag/0DRK)
* [Stacks Project, Tag 0A4J](https://stacks.math.columbia.edu/tag/0A4J)
* [Stacks Project, Tag 03K5](https://stacks.math.columbia.edu/tag/03K5)
* [Stacks Project, Tag 0H1Q](https://stacks.math.columbia.edu/tag/0H1Q)
* [Stacks Project, Tag 0AFN](https://stacks.math.columbia.edu/tag/0AFN)
* [Stacks Project, Tag 0DRG](https://stacks.math.columbia.edu/tag/0DRG)
* [Stacks Project, Tag 0DRJ](https://stacks.math.columbia.edu/tag/0DRJ)
* [Stacks Project, Tag 0GVZ](https://stacks.math.columbia.edu/tag/0GVZ)
* [Stacks Project, Tag 0GW1](https://stacks.math.columbia.edu/tag/0GW1)
* [Stacks Project, Tag 0GW2](https://stacks.math.columbia.edu/tag/0GW2)
* [Stacks Project, Tag 0GW7](https://stacks.math.columbia.edu/tag/0GW7)
* [Stacks Project, Tag 0GW8](https://stacks.math.columbia.edu/tag/0GW8)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

attribute [local instance] Space.pointTopology pointTopology

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Mapping the stack point of a space point along `g` is the canonical map of space points. -/
private theorem pointsMap_stackPoint_eq_spacePointMap
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS))
    (g : (fibredCategory B S hS F).val ⥤ᵇ 𝒳.val) (y : Space.points B S hS F) :
    pointsMap B S hS (fibredCategory B S hS F).val (fibredCategory B S hS F).property
        𝒳.property g (stackPointOfSpacePoint B S hS F y) = spacePointMap B S hS F 𝒳 g y := by
  have hcomp := congrFun (spacePointMap_comp B S hS F (fibredCategory B S hS F) 𝒳
    (BasedFunctor.id (fibredCategory B S hS F).val) g) y
  rw [BasedFunctor.id_comp] at hcomp
  exact hcomp.symm

/-- An étale 1-morphism from an algebraic space to an algebraic stack has relative dimension
`0` at every point. -/
theorem relativeDimensionAt_eq_zero_of_isRelativelyEtale
    (T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hT : IsAlgebraicSpace B S hS T)
    (𝒳 : AlgebraicStacks.{u, w} B S hS)
    (f : algebraicSpaceStack.{u, w} B S hS T hT ⟶ 𝒳)
    (hf : AlgebraicStacks.IsLocallyOfFiniteType B S hS f)
    (het : IsRelativelyEtale B S hS f.hom)
    (t : Space.points B S hS T) :
    relativeDimensionAt.{u, w} B S hS T hT 𝒳 f hf t = ((0 : ℕ) : WithBot ℕ∞) := by
  classical
  obtain ⟨p, q, -, -, hval⟩ := exists_eq_fieldFibreDimensionAt B S hS T hT 𝒳 f hf t
  obtain ⟨W, hW, ⟨eW⟩⟩ := isRepresentableByAlgebraicSpace_fieldFibreSquare.{u, w} B S hS
    f.hom 𝒳.property (isRepresentableByAlgebraicSpace_fibredCategory B S hS T hT) p
  obtain ⟨x, hx⟩ := (bijective_spacePointMap_representing B S hS W
    (fieldFibreSquare B S hS f.hom p).pt eW).surjective q
  have hdim : fieldFibreDimensionAt.{u, w} B S hS f.hom 𝒳.property
      (isRepresentableByAlgebraicSpace_fibredCategory B S hS T hT) p q =
      Space.dimensionAtPoint B S hS W hW x := by
    rw [← hx]
    exact fieldFibreDimensionAt_eq_dimensionAtPoint.{u, w} B S hS _ _ _ p W hW eW x
  have hgft : Space.IsLocallyOfFiniteType B S hS
      (representingMap B S hS (fieldFibreSquare B S hS f.hom p).pt
        (schemeFibredCategory B S hS p.base) W (yoneda.obj p.base) eW
        (PresheafOfCategories.sliceElementsEquivalenceOver p.base)
        (fieldFibreSquare B S hS f.hom p).snd) :=
    isLocallyOfFiniteType_representingMap_fieldFibreSquare_snd.{u, w} B S hS f hf p
      W (yoneda.obj p.base) hW (isAlgebraicSpace_yoneda B S hS p.base) eW
      (PresheafOfCategories.sliceElementsEquivalenceOver p.base)
  obtain ⟨hrep, hrel⟩ := het
  have hget : Space.IsEtale B S hS
      (representingMap B S hS (fieldFibreSquare B S hS f.hom p).pt
        (schemeFibredCategory B S hS p.base) W (yoneda.obj p.base) eW
        (PresheafOfCategories.sliceElementsEquivalenceOver p.base)
        (fieldFibreSquare B S hS f.hom p).snd) :=
    prop_representingMap_of_hasRelativeProperty.{u, u} B S hS (Space.etaleMorphisms B S hS)
      f.hom hrep hrel (schemeFibredCategory B S hS p.base)
      (fieldValuedPointMorphism B S hS 𝒳.val p) (fieldFibreSquare B S hS f.hom p).swap
      (Bicategory.isTwoFibreProduct_swap
        (CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1}
          f.hom (fieldValuedPointMorphism B S hS 𝒳.val p)))
      W (yoneda.obj p.base) hW (isAlgebraicSpace_yoneda B S hS p.base) eW
      (PresheafOfCategories.sliceElementsEquivalenceOver p.base)
  have hd0 := (Space.isLocallyQuasiFinite_iff_forall_hasRelativeDimensionAt_zero B S hS _
    hgft).mp (Space.isLocallyQuasiFinite_of_isEtale' B S hS hget) x
  rw [hval, hdim]
  exact (dimensionAtPoint_eq_iff_hasRelativeDimensionAt_of_isPullback B S hS p
    IsPullback.of_id_snd hW hW (isAlgebraicSpace_yoneda B S hS p.base) hgft x 0).mpr
    (by simpa using hd0)

/-- **An étale chart of a Deligne-Mumford stack by the algebraic space of a scheme.** A
Deligne-Mumford algebraic stack `𝒳` over `S` receives a 1-morphism from the algebraic stack of the
algebraic space represented by a scheme `W` of the site which is étale in the sense of
Stacks 04XB, smooth in the sense of Stacks 075U, and surjective on points. -/
theorem exists_etale_chart_of_isDeligneMumfordStack (𝒳 : AlgebraicStacks.{u, w} B S hS)
    (hDM : IsDeligneMumfordStack.{u, w} B S hS 𝒳.val.val) :
    ∃ (W : BigFppfOver B S hS)
      (c : algebraicSpaceStack.{u, w} B S hS (yoneda.obj W) (isAlgebraicSpace_yoneda B S hS W) ⟶
        𝒳),
      IsRelativelyEtale B S hS c.hom ∧ AlgebraicStacks.IsSmooth B S hS c ∧
        Function.Surjective (spacePointMap B S hS (yoneda.obj W) 𝒳.val c.hom.hom) := by
  obtain ⟨-, h𝒳fib, W, pres, hrep, hprop⟩ := hDM
  let c₀ : schemeStack.{u, w} B S hS W ⟶ 𝒳 := Bicategory.InducedBicategory.mkHom pres
  have hc₀et : IsRelativelyEtale B S hS c₀.hom :=
    ⟨hrep, fun V y hy G hG hE => (hprop V y hy G hG hE).2⟩
  have hc₀surj : IsSurjective B S hS c₀ :=
    (pointsMap_surjective_iff_isRelativelySurjective.{u, w, u} B S hS c₀ hrep).mpr
      (fun V y hy G hG hE => (hprop V y hy G hG hE).1)
  obtain ⟨e, he⟩ := exists_oneMorphism_representingMap_eq B S hS
    (𝒳 := algebraicSpaceStack.{u, w} B S hS (yoneda.obj W) (isAlgebraicSpace_yoneda B S hS W))
    (𝒴 := schemeStack.{u, w} B S hS W)
    (yoneda.obj W) (yoneda.obj W) (StacksRepresentableCFG.EquivalenceOver.refl _)
    (PresheafOfCategories.sliceElementsEquivalenceOver W) (𝟙 (yoneda.obj W))
  have hrepe : IsRepresentableByAlgebraicSpaces B S hS e.hom.hom :=
    isRepresentableByAlgebraicSpaces_of_isRepresentableByAlgebraicSpace B S hS e.hom
      (isRepresentableByAlgebraicSpace_fibredCategory B S hS _ (isAlgebraicSpace_yoneda B S hS W))
      (isRepresentableByAlgebraicSpace_schemeFibredCategory B S hS W)
  have heet : IsRelativelyEtale B S hS e.hom := by
    refine isRelativelyEtale_of_isEtale_representingMap B S hS e.hom hrepe (yoneda.obj W)
      (yoneda.obj W) (isAlgebraicSpace_yoneda B S hS W) (isAlgebraicSpace_yoneda B S hS W)
      (StacksRepresentableCFG.EquivalenceOver.refl _)
      (PresheafOfCategories.sliceElementsEquivalenceOver W) ?_
    rw [he]
    exact Space.isEtale_id B S hS (yoneda.obj W)
  have hesurj : IsSurjective B S hS e := by
    refine isSurjective_of_isSurjective_representingMap B S hS (yoneda.obj W) (yoneda.obj W)
      (isAlgebraicSpace_yoneda B S hS W) (isAlgebraicSpace_yoneda B S hS W)
      (StacksRepresentableCFG.EquivalenceOver.refl _)
      (PresheafOfCategories.sliceElementsEquivalenceOver W) e ?_
    rw [he]
    exact Space.isSurjective_id B S hS (yoneda.obj W)
  have hcet : IsRelativelyEtale B S hS (e ≫ c₀).hom :=
    isRelativelyEtale_comp B S hS e.hom c₀.hom heet hc₀et
  refine ⟨W, e ≫ c₀, hcet, ?_, ?_⟩
  · obtain ⟨hcrep, hcrel⟩ := hcet
    exact hasPropertyOnSomeSmoothDiagram_of_hasRelativeProperty.{u, w, u} B S hS
      (fun _ _ k => Space.IsSmooth B S hS k) 𝒳.property _ hcrep
      (fun V y hy G hG hE => Space.isSmooth_of_isEtale B S hS
        (isAlgebraicSpace_yoneda B S hS V) (hcrel V y hy G hG hE))
  · intro x
    obtain ⟨z, hz⟩ := isSurjective_comp B S hS e c₀ hesurj hc₀surj x
    obtain ⟨t, ht⟩ := (spacePointMap_id_bijective B S hS (yoneda.obj W)).surjective z
    refine ⟨t, ?_⟩
    rw [← pointsMap_stackPoint_eq_spacePointMap B S hS _ 𝒳.val (e ≫ c₀).hom.hom t]
    rw [← ht] at hz
    exact hz

/-- **An étale chart of a locally Noetherian algebraic stack collapses no specialization.** Let
`c : W ⟶ 𝒳` be an étale 1-morphism from the algebraic space of a scheme `W` to a locally
Noetherian algebraic stack. If `a ⤳ b` in `|W|` and `a`, `b` have the same image in `|𝒳|`, then
`a = b`.

The two points are the images of one point `z` of `R = W ×_𝒳 W` under its two projections, which
are étale, so the local rings of `W` at `a` and at `b` have the dimension of the local ring of
`R` at `z` (Stacks 04N8 through Stacks 04NA). A specialization between points of a locally
Noetherian scheme whose local rings have equal dimension is trivial. -/
theorem eq_of_specializes_of_spacePointMap_eq_of_isRelativelyEtale
    (𝒳 : AlgebraicStacks.{u, w} B S hS) (h𝒳 : IsLocallyNoetherianStack.{u, w} B S hS 𝒳)
    (W : BigFppfOver B S hS)
    (c : algebraicSpaceStack.{u, w} B S hS (yoneda.obj W) (isAlgebraicSpace_yoneda B S hS W) ⟶
      𝒳)
    (hcet : IsRelativelyEtale B S hS c.hom) (hsm : AlgebraicStacks.IsSmooth B S hS c)
    {a b : Space.points B S hS (yoneda.obj W)} (hab : a ⤳ b)
    (heq : spacePointMap B S hS (yoneda.obj W) 𝒳.val c.hom.hom a =
      spacePointMap B S hS (yoneda.obj W) 𝒳.val c.hom.hom b) : a = b := by
  classical
  have hW : IsAlgebraicSpace B S hS (yoneda.obj W) := isAlgebraicSpace_yoneda B S hS W
  obtain ⟨hrep, hrel⟩ := hcet
  -- the self-intersection `R = W ×_𝒳 W` and a point of it above `(a, b)`
  set Q := twoFibreProductSquareAlgebraicStacks B S hS c c with hQdef
  have hQ := isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS c c
  set Qc := CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} c.hom c.hom
    with hQcdef
  have hQc := CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1}
    c.hom c.hom
  have hmem : (stackPointOfSpacePoint B S hS (yoneda.obj W) a,
      stackPointOfSpacePoint B S hS (yoneda.obj W) b) ∈ Set.range
        (fun r : points B S hS Q.pt.val.val (Classical.choose Q.pt.property) =>
          (pointsMap B S hS Q.pt.val.val (Classical.choose Q.pt.property)
              (Classical.choose (algebraicSpaceStack.{u, w} B S hS (yoneda.obj W) hW).property)
              Q.fst.hom.hom r,
            pointsMap B S hS Q.pt.val.val (Classical.choose Q.pt.property)
              (Classical.choose (algebraicSpaceStack.{u, w} B S hS (yoneda.obj W) hW).property)
              Q.snd.hom.hom r)) := by
    rw [range_pointsMap_prod_eq B S hS c Q hQ]
    change pointsMap B S hS (fibredCategory B S hS (yoneda.obj W)).val
          (fibredCategory B S hS (yoneda.obj W)).property 𝒳.val.property c.hom.hom
          (stackPointOfSpacePoint B S hS (yoneda.obj W) a) =
        pointsMap B S hS (fibredCategory B S hS (yoneda.obj W)).val
          (fibredCategory B S hS (yoneda.obj W)).property 𝒳.val.property c.hom.hom
          (stackPointOfSpacePoint B S hS (yoneda.obj W) b)
    rw [pointsMap_stackPoint_eq_spacePointMap, pointsMap_stackPoint_eq_spacePointMap, heq]
  obtain ⟨r, hr⟩ := hmem
  -- the representing algebraic space of `R` and the point above `r`
  have hRrep : IsRepresentableByAlgebraicSpace B S hS Qc.pt :=
    isRepresentableByAlgebraicSpace_of_isTwoFibreProduct.{u, u, u + 1} B S hS
      (fibredCategory B S hS (yoneda.obj W)) 𝒳.val (fibredCategory B S hS (yoneda.obj W))
      c.hom c.hom Qc hQc hrep (isRepresentableByAlgebraicSpace_fibredCategory B S hS _ hW)
  obtain ⟨P, hP, ⟨eP⟩⟩ := hRrep
  obtain ⟨z, hz⟩ := (bijective_spacePointMap_representing B S hS P Qc.pt eP).surjective r
  -- the two projections of `R` are étale
  have hs : Space.IsEtale B S hS (representingMap B S hS Qc.pt
      (fibredCategory B S hS (yoneda.obj W)) P (yoneda.obj W) eP
      (StacksRepresentableCFG.EquivalenceOver.refl _) Qc.fst) :=
    prop_representingMap_of_hasRelativeProperty.{u, u} B S hS (Space.etaleMorphisms B S hS)
      c.hom hrep hrel (fibredCategory B S hS (yoneda.obj W)) c.hom Qc hQc P (yoneda.obj W) hP hW
      eP (StacksRepresentableCFG.EquivalenceOver.refl _)
  have ht : Space.IsEtale B S hS (representingMap B S hS Qc.pt
      (fibredCategory B S hS (yoneda.obj W)) P (yoneda.obj W) eP
      (StacksRepresentableCFG.EquivalenceOver.refl _) Qc.snd) :=
    prop_representingMap_of_hasRelativeProperty.{u, u} B S hS (Space.etaleMorphisms B S hS)
      c.hom hrep hrel (fibredCategory B S hS (yoneda.obj W)) c.hom Qc.swap
      (Bicategory.isTwoFibreProduct_swap hQc) P (yoneda.obj W) hP hW
      eP (StacksRepresentableCFG.EquivalenceOver.refl _)
  -- the images of `z` are `a` and `b`
  have himage : ∀ (k : Qc.pt ⟶ fibredCategory B S hS (yoneda.obj W))
      (y : Space.points B S hS (yoneda.obj W)),
      pointsMap B S hS Qc.pt.val Qc.pt.property
          (fibredCategory B S hS (yoneda.obj W)).property k.hom r =
        stackPointOfSpacePoint B S hS (yoneda.obj W) y →
      Space.pointsMap B S hS P (representingMap B S hS Qc.pt
        (fibredCategory B S hS (yoneda.obj W)) P (yoneda.obj W) eP
        (StacksRepresentableCFG.EquivalenceOver.refl _) k) z = y := by
    intro k y hk
    refine (spacePointMap_id_bijective B S hS (yoneda.obj W)).injective ?_
    have hnat := spacePointMap_representing_naturality B S hS P (yoneda.obj W) Qc.pt
      (fibredCategory B S hS (yoneda.obj W)) eP
      (StacksRepresentableCFG.EquivalenceOver.refl _) k z
    refine Eq.trans ?_ ((hnat.trans (by rw [hz])).trans hk)
    rfl
  have hza := himage Qc.fst a (congrArg Prod.fst hr)
  have hzb := himage Qc.snd b (congrArg Prod.snd hr)
  -- equal local ring dimensions at `a` and `b`
  have hloc : Space.localRingDimension B S hS a = Space.localRingDimension B S hS b := by
    rw [← hza, ← hzb, Space.localRingDimension_pointsMap_of_etale B S hS hP hW _ hs,
      Space.localRingDimension_pointsMap_of_etale B S hS hP hW _ ht]
  -- `W` is locally Noetherian
  have hNW : Space.HasEtaleLocalProperty B S hS (yoneda.obj W)
      (fun Z : Scheme.{u} => IsLocallyNoetherian Z) :=
    hasEtaleLocalProperty_isLocallyNoetherian_of_chart.{u, w} B S hS 𝒳 h𝒳 hW c
      (AlgebraicStacks.isLocallyOfFiniteType_of_isSmooth B S hS c hsm)
  have : IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj W) :=
    (Space.exists_atlas_iff_forall_etale B S hS (yoneda.obj W)
      (fun Z : Scheme.{u} => IsLocallyNoetherian Z) hW).mp hNW W (𝟙 _)
      (Space.presheaf_etale_id B S hS W)
  -- the local ring dimensions on the scheme `W`
  have hstalk : ∀ y : Space.points B S hS (yoneda.obj W),
      ringKrullDim (((BigFppfOver.toScheme B S hS).obj W).presheaf.stalk
        (Space.pointsToScheme B S hS W y)) =
        ((Space.localRingDimension B S hS y : ℕ∞) : WithBot ℕ∞) := by
    intro y
    have hchart : Space.ChartPoint B S hS W (𝟙 (yoneda.obj W))
        (Space.pointsToScheme B S hS W y) y := by
      have h := Space.chartPoint_pointsToScheme B S hS W (𝟙 (yoneda.obj W)) y
      rwa [Space.pointsMap_id] at h
    exact (Space.hasChartLocalRingDimension_iff_ringKrullDim_stalk B S hS W _ y hchart _).mp
      ((Space.localRingDimension_eq_iff_hasChartLocalRingDimension B S hS hW y _).mp rfl)
  have hspec : Space.pointsToScheme B S hS W a ⤳ Space.pointsToScheme B S hS W b :=
    hab.map (Space.schemePointsHomeomorph B S hS W).continuous
  have hpt := eq_of_specializes_of_ringKrullDim_stalk_eq _ hspec
    (by rw [hstalk, hstalk, hloc])
  exact ((Space.pointsEquivScheme B S hS W).injective hpt).symm

/-- **Stacks 0DRK, the Deligne-Mumford case.** Let `𝒳` be a locally Noetherian Deligne-Mumford
algebraic stack over `S` which is decent. Then at every point `x ∈ |𝒳|` the dimension of `𝒳`
(Stacks 0AFN) agrees with the local Krull dimension `dim_x |𝒳|` of its point space.

An étale chart `c : W ⟶ 𝒳` by a scheme has relative dimension `0` everywhere, so by Stacks 0DRJ
the dimension of `𝒳` at `x = c(t)` is the dimension of `W` at `t`, which is `dim_t |W|`. The map
`|W| ⟶ |𝒳|` is continuous and open (Stacks 06R7), generizations lift along it (Stacks 0GVZ,
decency supplying the quasi-compact representatives), and it collapses no specialization
(`AlgebraicGeometry.Stack.eq_of_specializes_of_spacePointMap_eq_of_isRelativelyEtale`); `|W|` is
sober and `|𝒳|` is sober by Stacks 0GW8, so the two local dimensions agree. -/
@[stacks 0DRK "Deligne-Mumford stacks which are decent: `dim_x(𝒳) = dim_x |𝒳|`"]
theorem dimensionAtPoint_eq_topologicalKrullDimAt_of_isDeligneMumfordStack
    (𝒳 : AlgebraicStacks.{u, w} B S hS) (h𝒳 : IsLocallyNoetherianStack.{u, w} B S hS 𝒳)
    (hDM : IsDeligneMumfordStack.{u, w} B S hS 𝒳.val.val) (hdec : IsDecent B S hS 𝒳.val)
    (x : points B S hS 𝒳.val.val 𝒳.val.property) :
    dimensionAtPoint B S hS 𝒳 h𝒳 x =
      dimensionSubNat (topologicalKrullDimAt (points B S hS 𝒳.val.val 𝒳.val.property) x) 0 := by
  classical
  obtain ⟨W, c, hcet, hsm, hsurj⟩ := exists_etale_chart_of_isDeligneMumfordStack B S hS 𝒳 hDM
  have hW : IsAlgebraicSpace B S hS (yoneda.obj W) := isAlgebraicSpace_yoneda B S hS W
  obtain ⟨t, rfl⟩ := hsurj x
  have hf := AlgebraicStacks.isLocallyOfFiniteType_of_isSmooth B S hS c hsm
  have hd := relativeDimensionAt_eq_zero_of_isRelativelyEtale B S hS _ hW 𝒳 c hf hcet t
  rw [dimensionAtPoint_eq_dimensionSubNat_of_isSmooth.{u, w} B S hS 𝒳 h𝒳 _ hW c hsm hf t
    (pointsMap_stackPoint_eq_spacePointMap B S hS _ 𝒳.val c.hom.hom t) 0 hd]
  congr 1
  rw [← Space.topologicalKrullDimAt_points_eq_dimensionAtPoint_of_isDecentSpace B S hS hW
    (Space.isDecentSpace_yoneda B S hS W) t]
  -- the topology of the chart
  have : T0Space (points B S hS 𝒳.val.val 𝒳.val.property) :=
    t0Space_points_of_isDecent.{u, w} B S hS 𝒳.val 𝒳.property hdec
  have : QuasiSober (points B S hS 𝒳.val.val 𝒳.val.property) :=
    AlgebraicStacks.quasiSober_points_of_isLocallyNoetherian B S hS 𝒳 h𝒳
  have : QuasiSober (Space.points B S hS (yoneda.obj W)) :=
    (Space.schemePointsHomeomorph B S hS W).isOpenEmbedding.quasiSober
  have hcont : Continuous (spacePointMap B S hS (yoneda.obj W) 𝒳.val c.hom.hom) :=
    continuous_spacePointMap B S hS (yoneda.obj W) hW 𝒳.val c.hom.hom
  have hopen : IsOpenMap (spacePointMap B S hS (yoneda.obj W) 𝒳.val c.hom.hom) := by
    obtain ⟨-, hrel⟩ := hcet
    refine isOpenMap_spacePointMap B S hS (yoneda.obj W) hW 𝒳.val 𝒳.property c.hom.hom
      fun V y hy G hG hE => ?_
    have hsmV := Space.isSmooth_of_isEtale B S hS (isAlgebraicSpace_yoneda B S hS V)
      (hrel V y hy G hG hE)
    exact ⟨Space.isFlat_of_isSmooth B S hS _ hsmV,
      Space.isLocallyOfFinitePresentation_of_isSmooth B S hS hsmV⟩
  have hlift : GeneralizingMap (spacePointMap B S hS (yoneda.obj W) 𝒳.val c.hom.hom) := by
    intro a y hya
    obtain ⟨a', ha'a, ha'⟩ := exists_specializes_spacePointMap_eq.{u, w} B S hS 𝒳.val 𝒳.property
      (yoneda.obj W) hW c.hom hsm hya (hdec y) a rfl
    exact ⟨a', ha'a, ha'⟩
  exact Topology.topologicalKrullDimAt_eq_of_isOpenMap_of_generalizingMap _ hcont hopen hlift
    (fun a b hab heq => eq_of_specializes_of_spacePointMap_eq_of_isRelativelyEtale B S hS 𝒳 h𝒳
      W c hcet hsm hab heq) t

/-- **Stacks 0DRK, the quasi-separated Deligne-Mumford case.** At every point of a locally
Noetherian, quasi-separated Deligne-Mumford algebraic stack `𝒳` the dimension of `𝒳` agrees with
the local Krull dimension of `|𝒳|`. A quasi-separated algebraic stack is decent (Stacks 0GW2). -/
@[stacks 0DRK "quasi-separated Deligne-Mumford stacks: `dim_x(𝒳) = dim_x |𝒳|`"]
theorem dimensionAtPoint_eq_topologicalKrullDimAt_of_isDeligneMumfordStack_of_quasiSeparated
    (hZ : B.Contains (⊤_ Scheme.{u}))
    (𝒳 : AlgebraicStacks.{u, w} B S hS) (h𝒳 : IsLocallyNoetherianStack.{u, w} B S hS 𝒳)
    (hDM : IsDeligneMumfordStack.{u, w} B S hS 𝒳.val.val)
    (hqs : AlgebraicStacks.IsAbsolutelyQuasiSeparated.{u, w} B S hS hZ 𝒳)
    (x : points B S hS 𝒳.val.val 𝒳.val.property) :
    dimensionAtPoint B S hS 𝒳 h𝒳 x =
      dimensionSubNat (topologicalKrullDimAt (points B S hS 𝒳.val.val 𝒳.val.property) x) 0 :=
  dimensionAtPoint_eq_topologicalKrullDimAt_of_isDeligneMumfordStack B S hS 𝒳 h𝒳 hDM
    (isDecent_of_isQuasiSeparated B S hS hZ 𝒳 hqs) x

end AlgebraicGeometry.Stack

end
