module

public import StacksFrontier.AlgebraicGeometry.Stacks.ReducedClosedSubstackExistence
public import StacksFrontier.AlgebraicGeometry.Spaces.StrictTransformFlatClosedSubspace
public import StacksFrontier.AlgebraicGeometry.Stacks.DenseOpenGerbe
public import StacksFrontier.AlgebraicGeometry.Stacks.LocalRingDimensionVersal
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalPropertyAtlasBridges
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalMorphismBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeSmooth
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatComposition
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.FlatIsomorphismLocusOnBase
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartComposition
public import StacksFrontier.AlgebraicGeometry.Spaces.CoveringComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.FpqcOpenSubspaceDescent
public import StacksFrontier.CategoryTheory.FiberedCategory.ElementsMap

/-!
# Flat closed substacks over the complement of an effective Cartier divisor

Let `g : 𝒳 ⟶ A'` be a 1-morphism from an algebraic stack to an algebraic space over `S`, let
`c : P ⟶ 𝒳` be a smooth surjection from an algebraic space with `c ≫ g ≅ π` for a morphism
`π : P ⟶ A'`, let `D ⊆ A'` be an effective Cartier divisor, and let `C ⊆ P` be a closed subspace
containing `P ∖ π⁻¹D` which is flat and locally of finite presentation over `A'`. Then there is a
closed substack of `𝒳` containing every object lying over `A' ∖ D` which is flat and locally of
finite presentation over `A'`. In the proof of **Stacks 0CQ4** this is the step producing the
closed substack `𝒳' ⊆ 𝒳_{Y'}` from the strict transform `U'` of a smooth chart.

Refine `c` by a smooth surjective chart `U ⟶ P` by a scheme, inducing `w : U ⟶ P`, and set
`Z = w⁻¹C ⊆ U`. The two inverse images of `Z` in the self-intersection `R = U ×_𝒳 U` are closed
subspaces flat over `A'` along the common map `R ⟶ A'` and containing the complement of the
inverse image of `D`, hence equal (`AlgebraicGeometry.Space.eq_of_isFlat_of_openComplement_le`).
So `Z` is invariant and its locus is a closed substack (**Stacks 0507**), and the base change of
the chart to the locus is a smooth surjection from the algebraic stack of `Z`, which is flat and
locally of finite presentation over `A'`.

## Main results

* `AlgebraicGeometry.Space.openComplementOfClosedSubspace_preimageClosedSubspace`: the open
  complement of an inverse image is the inverse image of the open complement.
* `AlgebraicGeometry.Stack.relationSourceMap_comp_eq_relationTargetMap_comp`: the two ends of a
  section of the self-intersection of the chart have the same image in `A'`.
* `AlgebraicGeometry.Stack.isChartInvariant_preimage_of_isFlat`: `w⁻¹C` is invariant.
* `AlgebraicGeometry.Stack.isFlat_and_isLocallyOfFinitePresentation_chartLocus`: the locus of
  `w⁻¹C` is flat and locally of finite presentation over `A'`.
* `exists_isClosedSubstack_isFlat_isLocallyOfFinitePresentation_of_openComplement_le`: the
  closed substack, in `AlgebraicGeometry.Stack`.

## Implementation notes

An object `x` of `𝒳` lies over `A' ∖ D` when the section of `A'` named by its image under `g`
lies in the open complement of `D`. The source's equality `s⁻¹U' = t⁻¹U'` is proved for the
chart refined to a scheme `U`, so that the locus construction for invariant closed subspaces of
scheme charts applies; the common map `R ⟶ A'` holds because a section of `R` names a vertical
isomorphism between two objects of `𝒳`, and `𝒮_{A'}` is fibred in sets.

## References

* [Stacks Project, Tag 0CQ4](https://stacks.math.columbia.edu/tag/0CQ4)
* [Stacks Project, Tag 0507](https://stacks.math.columbia.edu/tag/0507)
* [Stacks Project, Tag 04T5](https://stacks.math.columbia.edu/tag/04T5)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u w

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The open complement of the inverse image `q⁻¹D` is the inverse image of `X ∖ D`. -/
theorem openComplementOfClosedSubspace_preimageClosedSubspace {X Y : AlgebraicSpaces B S hS}
    (q : Y ⟶ X) (D : ClosedSubspaces B S hS X.1) :
    (openComplementOfClosedSubspace B S hS Y (preimageClosedSubspace q D)).1 =
      (openComplementOfClosedSubspace B S hS X D).1.preimage q.hom := by
  have hpts : Set.range (pointsMap B S hS
        (openComplementOfClosedSubspace B S hS Y (preimageClosedSubspace q D)).1.toFunctor
        (openComplementOfClosedSubspace B S hS Y (preimageClosedSubspace q D)).1.ι) =
      Set.range (pointsMap B S hS
        ((openComplementOfClosedSubspace B S hS X D).1.preimage q.hom).toFunctor
        ((openComplementOfClosedSubspace B S hS X D).1.preimage q.hom).ι) := by
    rw [range_pointsMap_preimage_ι]
    change subspacePointSet B S hS Y.1
        (openComplementOfClosedSubspace B S hS Y (preimageClosedSubspace q D)).1 =
      pointsMap B S hS Y.1 q.hom ⁻¹' subspacePointSet B S hS X.1
        (openComplementOfClosedSubspace B S hS X D).1
    rw [subspacePointSet_openComplement, subspacePointSet_openComplement, Set.preimage_compl]
    exact congrArg (fun s => sᶜ) (range_pointsMap_preimage_ι B S hS _ _)
  have hO₁ := (openComplementOfClosedSubspace B S hS Y (preimageClosedSubspace q D)).2
  have hO₂ := isOpenSubspace_preimage B S hS q.hom _ X.2 Y.2
    (openComplementOfClosedSubspace B S hS X D).2
  exact le_antisymm (le_of_range_pointsMap_ι_subset B S hS hO₂ hpts.le)
    (le_of_range_pointsMap_ι_subset B S hS hO₁ hpts.ge)

/-- If `Z ⊆ X` contains `X ∖ p⁻¹D`, then `q⁻¹Z` contains `Y ∖ (q ≫ p)⁻¹D`. -/
theorem openComplement_le_preimageClosedSubspace {X Y A : AlgebraicSpaces B S hS}
    (q : Y ⟶ X) (p : X ⟶ A) (D : ClosedSubspaces B S hS A.1) (Z : ClosedSubspaces B S hS X.1)
    (hZ : (openComplementOfClosedSubspace B S hS X (preimageClosedSubspace p D)).1 ≤ Z.1) :
    (openComplementOfClosedSubspace B S hS Y (preimageClosedSubspace (q ≫ p) D)).1 ≤
      (preimageClosedSubspace q Z).1 := by
  rw [openComplementOfClosedSubspace_preimageClosedSubspace,
    show (q ≫ p).hom = q.hom ≫ p.hom from rfl, Subfunctor.preimage_comp,
    ← openComplementOfClosedSubspace_preimageClosedSubspace]
  exact fun T x hx => hZ T hx

/-- If `Z ⊆ X` is flat over `A` along `p` and `q : Y ⟶ X` is flat, then `q⁻¹Z` is flat over `A`
along `q ≫ p`: `q⁻¹Z ⟶ Z` is a base change of `q`. -/
theorem isFlat_preimageClosedSubspace_ι_comp {X Y A : AlgebraicSpaces B S hS}
    (q : Y ⟶ X) (p : X ⟶ A) (Z : ClosedSubspaces B S hS X.1) (hq : IsFlat B S hS q.hom)
    (hZ : IsFlat B S hS (Z.1.ι ≫ p.hom)) :
    IsFlat B S hS ((preimageClosedSubspace q Z).1.ι ≫ (q ≫ p).hom) := by
  change IsFlat B S hS ((Z.1.preimage q.hom).ι ≫ q.hom ≫ p.hom)
  rw [← Category.assoc, ← Subfunctor.fromPreimage_ι, Category.assoc]
  exact isFlat_comp B S hS (preimageClosedSubspace q Z).2.1 Z.2.1 A.2 _ _
    (isFlat_of_isPullback_of_isAlgebraicSpace B S hS (Subfunctor.isPullback_preimage q.hom Z.1)
      Y.2 X.2 hq) hZ

/-- If `Z ⊆ X` is locally of finite presentation over `A` along `p` and so is `q : Y ⟶ X`, then
so is `q⁻¹Z` over `A` along `q ≫ p`. -/
theorem isLocallyOfFinitePresentation_preimageClosedSubspace_ι_comp
    {X Y A : AlgebraicSpaces B S hS}
    (q : Y ⟶ X) (p : X ⟶ A) (Z : ClosedSubspaces B S hS X.1)
    (hq : IsLocallyOfFinitePresentation B S hS q.hom)
    (hZ : IsLocallyOfFinitePresentation B S hS (Z.1.ι ≫ p.hom)) :
    IsLocallyOfFinitePresentation B S hS ((preimageClosedSubspace q Z).1.ι ≫ (q ≫ p).hom) := by
  change IsLocallyOfFinitePresentation B S hS ((Z.1.preimage q.hom).ι ≫ q.hom ≫ p.hom)
  rw [← Category.assoc, ← Subfunctor.fromPreimage_ι, Category.assoc]
  refine isLocallyOfFinitePresentation_comp B S hS (preimageClosedSubspace q Z).2.1 Z.2.1 A.2 _ _
    ?_ hZ
  let Y' : AlgebraicSpaces B S hS := ⟨(Z.1.preimage q.hom).toFunctor,
    (preimageClosedSubspace q Z).2.1⟩
  let Z' : AlgebraicSpaces B S hS := ⟨Z.1.toFunctor, Z.2.1⟩
  exact (isLocallyOfFinitePresentation_isStableUnderBaseChange B S hS).of_isPullback
    (show IsPullback (ObjectProperty.homMk (Z.1.preimage q.hom).ι : Y' ⟶ Y)
      (ObjectProperty.homMk (Z.1.fromPreimage q.hom) : Y' ⟶ Z') q
      (ObjectProperty.homMk Z.1.ι : Z' ⟶ X) from IsPullback.of_map_of_faithful
      (F := ObjectProperty.ι (fun T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u =>
        IsAlgebraicSpace B S hS T)) (Subfunctor.isPullback_preimage q.hom Z.1).flip) hq

end AlgebraicGeometry.Space

namespace AlgebraicGeometry.Stack

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

section ChartSections

variable {𝒳 : AlgebraicStacks.{u, w} B S hS} {A' P : AlgebraicSpaces B S hS}
  (g : 𝒳 ⟶ algebraicSpaceStack.{u, w} B S hS A'.1 A'.2)
  (c : algebraicSpaceStack.{u, w} B S hS P.1 P.2 ⟶ 𝒳) (π : P ⟶ A')
  {U : BigFppfOver B S hS}
  (a : schemeStack.{u, w} B S hS U ⟶ algebraicSpaceStack.{u, w} B S hS P.1 P.2)
  (wU : yoneda.obj U ⟶ P.1)

/-- The value of a chart `(Sch/S)/U ⟶ 𝒮_P` on an object `z : T ⟶ U` is the pair of `T` and the
image of `z` under the morphism of presheaves the chart induces. -/
theorem schemeStackHom_obj_eq
    (hw : representingMap B S hS (schemeFibredCategory B S hS U) (fibredCategory B S hS P.1)
      (yoneda.obj U) P.1 (PresheafOfCategories.sliceElementsEquivalenceOver U)
      (StacksRepresentableCFG.EquivalenceOver.refl _) a.hom = wU) (z : Over U) :
    a.hom.hom.obj z = ⟨z.left, Discrete.mk (wU.app (op z.left) z.hom)⟩ := by
  subst hw
  refine PresheafOfCategories.obj_eq_of_elementOf_eq (Functor.congr_obj a.hom.hom.w z) rfl ?_
  exact (representingMap_app_hom B S hS (fibredCategory B S hS P.1) P.1
    (StacksRepresentableCFG.EquivalenceOver.refl _) U a.hom z).symm

variable {g c π a wU}

/-- Under `c ≫ g ≅ 𝒮_π`, the image in `𝒮_{A'}` of the value of the chart at `z : T ⟶ U` is the
pair of `T` and `π (w z)`. -/
theorem comp_obj_schemeStackHom_obj_eq
    (hw : representingMap B S hS (schemeFibredCategory B S hS U) (fibredCategory B S hS P.1)
      (yoneda.obj U) P.1 (PresheafOfCategories.sliceElementsEquivalenceOver U)
      (StacksRepresentableCFG.EquivalenceOver.refl _) a.hom = wU)
    (hcg : (c ≫ g).hom = (associatedMap B S hS π.hom).1) (z : Over U) :
    g.hom.hom.obj (c.hom.hom.obj (a.hom.hom.obj z)) =
      ⟨z.left, Discrete.mk (π.hom.app (op z.left) (wU.app (op z.left) z.hom))⟩ := by
  have h := congrArg (fun k => k.hom.obj (a.hom.hom.obj z)) hcg
  change g.hom.hom.obj (c.hom.hom.obj (a.hom.hom.obj z)) = _ at h
  rw [h, associatedMap_obj, schemeStackHom_obj_eq a wU hw z]

/-- The section of `A'` over `T` named by the image in `𝒮_{A'}` of the value of the chart at an
object `z` of `(Sch/S)/U` over `T` is `π (w z)`. -/
theorem sectionOfObj_comp_obj_schemeStackHom_obj
    (hw : representingMap B S hS (schemeFibredCategory B S hS U) (fibredCategory B S hS P.1)
      (yoneda.obj U) P.1 (PresheafOfCategories.sliceElementsEquivalenceOver U)
      (StacksRepresentableCFG.EquivalenceOver.refl _) a.hom = wU)
    (hcg : (c ≫ g).hom = (associatedMap B S hS π.hom).1) (z : Over U) {T : BigFppfOver B S hS}
    (h : z.left = T)
    (H : (fibredCategory B S hS A'.1).val.p.obj
      (g.hom.hom.obj (c.hom.hom.obj (a.hom.hom.obj z))) = T) :
    PresheafOfCategories.sectionOfObj (StacksRepresentableCFG.EquivalenceOver.refl _)
        (g.hom.hom.obj (c.hom.hom.obj (a.hom.hom.obj z))) H =
      π.hom.app (op T) (wU.app (op T)
        (PresheafOfCategories.sectionOfObj (PresheafOfCategories.sliceElementsEquivalenceOver U)
          z h)) := by
  subst h
  exact PresheafOfCategories.sectionOfObj_eq_of_obj_eq
    (StacksRepresentableCFG.EquivalenceOver.refl (presheafOfCategories (A'.1 ⋙ typeToCat)).p)
    (StacksRepresentableCFG.EquivalenceOver.refl (presheafOfCategories (A'.1 ⋙ typeToCat)).p) _
    (⟨z.left, Discrete.mk (π.hom.app (op z.left) (wU.app (op z.left) z.hom))⟩ :
      (presheafOfCategories (A'.1 ⋙ typeToCat)).obj) H rfl
    (comp_obj_schemeStackHom_obj_eq hw hcg z)

/-- **A vertical morphism between two values of the chart does not change their images in `A'`**:
`𝒮_{A'}` is fibred in sets. -/
theorem app_sectionOfObj_eq_of_isHomLift
    (hw : representingMap B S hS (schemeFibredCategory B S hS U) (fibredCategory B S hS P.1)
      (yoneda.obj U) P.1 (PresheafOfCategories.sliceElementsEquivalenceOver U)
      (StacksRepresentableCFG.EquivalenceOver.refl _) a.hom = wU)
    (hcg : (c ≫ g).hom = (associatedMap B S hS π.hom).1) (z z' : Over U)
    {T : BigFppfOver B S hS} (h : z.left = T) (h' : z'.left = T)
    (φ : c.hom.hom.obj (a.hom.hom.obj z) ⟶ c.hom.hom.obj (a.hom.hom.obj z'))
    (hφ : 𝒳.val.val.p.IsHomLift (𝟙 T) φ) :
    π.hom.app (op T) (wU.app (op T)
        (PresheafOfCategories.sectionOfObj (PresheafOfCategories.sliceElementsEquivalenceOver U)
          z h)) =
      π.hom.app (op T) (wU.app (op T)
        (PresheafOfCategories.sectionOfObj (PresheafOfCategories.sliceElementsEquivalenceOver U)
          z' h')) := by
  have H : ∀ y : Over U, y.left = T → (fibredCategory B S hS A'.1).val.p.obj
      (g.hom.hom.obj (c.hom.hom.obj (a.hom.hom.obj y))) = T := fun y hy =>
    (Functor.congr_obj g.hom.hom.w _).trans ((Functor.congr_obj c.hom.hom.w _).trans
      ((Functor.congr_obj a.hom.hom.w y).trans hy))
  rw [← sectionOfObj_comp_obj_schemeStackHom_obj hw hcg z h (H z h),
    ← sectionOfObj_comp_obj_schemeStackHom_obj hw hcg z' h' (H z' h')]
  exact PresheafOfCategories.sectionOfObj_eq_of_hom _ (H z h) (H z' h') (g.hom.hom.map φ)
    (BasedFunctor.preserves_isHomLift g.hom.hom (𝟙 T) φ)

/-- **The two ends of a section of the self-intersection have the same image in `A'`**: for
`R = U ×_𝒳 U`, the source and target maps `R ⟶ U` agree after `π ∘ w : U ⟶ A'`. -/
theorem relationSourceMap_comp_eq_relationTargetMap_comp
    (hw : representingMap B S hS (schemeFibredCategory B S hS U) (fibredCategory B S hS P.1)
      (yoneda.obj U) P.1 (PresheafOfCategories.sliceElementsEquivalenceOver U)
      (StacksRepresentableCFG.EquivalenceOver.refl _) a.hom = wU)
    (hcg : (c ≫ g).hom = (associatedMap B S hS π.hom).1) {R : AlgebraicSpaces B S hS}
    (eR : StacksRepresentableCFG.EquivalenceOver
      (SelfIntersection.relation B S hS (schemeFibredCategory B S hS U) 𝒳.val
        (a ≫ c).hom.hom).val.p
      (presheafOfCategories (R.obj ⋙ typeToCat)).p) :
    SelfIntersection.relationSourceMap (U := chartSpace U)
        (PresheafOfCategories.sliceElementsEquivalenceOver U) eR ≫ wU ≫ π.hom =
      SelfIntersection.relationTargetMap (U := chartSpace U)
        (PresheafOfCategories.sliceElementsEquivalenceOver U) eR ≫ wU ≫ π.hom := by
  refine NatTrans.ext (funext fun T => ?_)
  obtain ⟨T⟩ := T
  ext r
  obtain ⟨ρ, hρ, rfl⟩ := PresheafOfCategories.exists_sectionOfObj eR r
  have hs := SelfIntersection.relationSourceMap_sectionOfObj (U := chartSpace U)
    (PresheafOfCategories.sliceElementsEquivalenceOver U) eR ρ hρ
  have ht := SelfIntersection.relationTargetMap_sectionOfObj (U := chartSpace U)
    (PresheafOfCategories.sliceElementsEquivalenceOver U) eR ρ hρ
  have hv : 𝒳.val.val.p.IsHomLift (𝟙 T) ρ.iso.inv := by
    subst hρ
    exact @IsHomLift.lift_id_inv _ _ _ _ 𝒳.val.val.p _ _ _ ρ.iso ρ.vertical
  have key := app_sectionOfObj_eq_of_isHomLift hw hcg ρ.y ρ.x
    (SelfIntersection.relation_obj_y hρ) (SelfIntersection.relation_obj_x hρ) ρ.iso.inv hv
  exact (congrArg (fun t => π.hom.app _ (wU.app _ t)) hs).trans
    (key.trans (congrArg (fun t => π.hom.app _ (wU.app _ t)) ht).symm)

/-- **`w⁻¹C` is invariant for the chart.** Its two inverse images in `R = U ×_𝒳 U` are flat over
`A'` and contain the complement of the inverse image of the effective Cartier divisor `D`, hence
are equal. -/
theorem isChartInvariant_preimage_of_isFlat
    (hw : representingMap B S hS (schemeFibredCategory B S hS U) (fibredCategory B S hS P.1)
      (yoneda.obj U) P.1 (PresheafOfCategories.sliceElementsEquivalenceOver U)
      (StacksRepresentableCFG.EquivalenceOver.refl _) a.hom = wU)
    (hcg : (c ≫ g).hom = (associatedMap B S hS π.hom).1)
    (hfS : AlgebraicStacks.IsSmooth B S hS (a ≫ c)) (hwsm : Space.IsSmooth B S hS wU)
    (D : Space.ClosedSubspaces B S hS A'.1) (hD : Space.IsEffectiveCartierDivisor B S hS A' D)
    (C : Space.ClosedSubspaces B S hS P.1)
    (hCD : (Space.openComplementOfClosedSubspace B S hS P
      (Space.preimageClosedSubspace π D)).1 ≤ C.1)
    (hflat : Space.IsFlat B S hS (C.1.ι ≫ π.hom)) :
    IsChartInvariant (a ≫ c).hom.hom (C.1.preimage wU) := by
  intro b₁ b₂ φ k hφ hb
  obtain ⟨hrep, hsmooth⟩ := isRelativelySmooth_of_isSmooth_schemeStack B S hS U (a ≫ c) hfS
  let f := (a ≫ c).hom.hom
  let eU : StacksRepresentableCFG.EquivalenceOver (schemeFibredCategory B S hS U).val.p
      (presheafOfCategories ((chartSpace U).obj ⋙ typeToCat)).p :=
    PresheafOfCategories.sliceElementsEquivalenceOver U
  obtain ⟨Rsp, hRsp, ⟨eR⟩⟩ :=
    SelfIntersection.isRepresentableByAlgebraicSpace_relation_of_isAlgebraicStack B S hS
      (schemeFibredCategory B S hS U) 𝒳.val f 𝒳.property
      (isRepresentableByAlgebraicSpace_schemeFibredCategory B S hS U)
  let R : AlgebraicSpaces B S hS := ⟨Rsp, hRsp⟩
  let sR := SelfIntersection.relationSource (U := chartSpace U) (R := R) eU eR
  let tR := SelfIntersection.relationTarget (U := chartSpace U) (R := R) eU eR
  have hsm_s : Space.IsSmooth B S hS sR.hom :=
    SelfIntersection.isSmooth_selfIntersectionPresentation_source (𝒳 := 𝒳.val)
      (F := (a ≫ c).hom) (U := chartSpace U) (R := R) eU eR hrep hsmooth 𝒳.property
  have hsm_t : Space.IsSmooth B S hS tR.hom :=
    SelfIntersection.isSmooth_selfIntersectionPresentation_target (𝒳 := 𝒳.val)
      (F := (a ≫ c).hom) (U := chartSpace U) (R := R) eU eR hrep hsmooth 𝒳.property
  let wS : chartSpace U ⟶ P := ObjectProperty.homMk wU
  let Zc : Space.ClosedSubspaces B S hS (chartSpace U).1 := Space.preimageClosedSubspace wS C
  have hZD : (Space.openComplementOfClosedSubspace B S hS (chartSpace U)
      (Space.preimageClosedSubspace (wS ≫ π) D)).1 ≤ Zc.1 :=
    Space.openComplement_le_preimageClosedSubspace B S hS wS π D C hCD
  have hZf : Space.IsFlat B S hS (Zc.1.ι ≫ (wS ≫ π).hom) :=
    Space.isFlat_preimageClosedSubspace_ι_comp B S hS wS π C
      (Space.isFlat_of_isSmooth B S hS _ hwsm) hflat
  have hkey : sR ≫ wS ≫ π = tR ≫ wS ≫ π :=
    ObjectProperty.hom_ext _ (relationSourceMap_comp_eq_relationTargetMap_comp (R := R) hw hcg eR)
  have heq : Space.preimageClosedSubspace sR Zc = Space.preimageClosedSubspace tR Zc := by
    refine Space.eq_of_isFlat_of_openComplement_le B S hS (sR ≫ wS ≫ π) D hD _ _
      (Space.openComplement_le_preimageClosedSubspace B S hS sR (wS ≫ π) D Zc hZD) ?_
      (Space.isFlat_preimageClosedSubspace_ι_comp B S hS sR (wS ≫ π) Zc
        (Space.isFlat_of_isSmooth B S hS _ hsm_s) hZf) ?_
    · rw [hkey]
      exact Space.openComplement_le_preimageClosedSubspace B S hS tR (wS ≫ π) D Zc hZD
    · rw [hkey]
      exact Space.isFlat_preimageClosedSubspace_ι_comp B S hS tR (wS ≫ π) Zc
        (Space.isFlat_of_isSmooth B S hS _ hsm_t) hZf
  have hinv : (C.1.preimage wU).preimage sR.hom = (C.1.preimage wU).preimage tR.hom :=
    congrArg Subtype.val heq
  -- the restriction of `b₂` along `k`, and the vertical comparison of `f b₁` with its image
  let a' : Over U := Over.mk (k ≫ b₂.hom)
  have hfib : 𝒳.val.val.p.IsFiberedInGroupoids := 𝒳.val.property
  have hm := isHomLift_overHomMk b₂ k
  have hψ : 𝒳.val.val.p.IsHomLift k (f.map (Over.homMk k rfl : a' ⟶ b₂)) :=
    BasedFunctor.preserves_isHomLift f k _
  have hcart : 𝒳.val.val.p.IsStronglyCartesian k (f.map (Over.homMk k rfl : a' ⟶ b₂)) :=
    hfib.isStronglyCartesian_homLift k _
  let χ : f.obj b₁ ⟶ f.obj a' :=
    Functor.IsStronglyCartesian.map 𝒳.val.val.p k (f.map (Over.homMk k rfl : a' ⟶ b₂))
      (f' := k) (g := 𝟙 b₁.left) (by simp) φ
  have hχ : 𝒳.val.val.p.IsHomLift (𝟙 b₁.left) χ := inferInstance
  let αF : (Functor.Fiber.mk (SelfIntersection.fObj_over (U := chartSpace U) (f := f) eU b₁.hom) :
      𝒳.val.val.p.Fiber b₁.left) ⟶
      Functor.Fiber.mk (SelfIntersection.fObj_over (U := chartSpace U) (f := f) eU a'.hom) :=
    ⟨χ, hχ⟩
  let r := SelfIntersection.arrowOfFiberHom (U := chartSpace U) (R := R) eU eR a'.hom b₁.hom αF
  have hr_s : sR.hom.app (op b₁.left) r = a'.hom :=
    SelfIntersection.relationSourceMap_arrowOfFiberHom (U := chartSpace U) (R := R) eU eR
      a'.hom b₁.hom αF
  have hr_t : tR.hom.app (op b₁.left) r = b₁.hom :=
    SelfIntersection.relationTargetMap_arrowOfFiberHom (U := chartSpace U) (R := R) eU eR
      a'.hom b₁.hom αF
  have hrs : r ∈ ((C.1.preimage wU).preimage sR.hom).obj (op b₁.left) := by
    change sR.hom.app (op b₁.left) r ∈ (C.1.preimage wU).obj (op b₁.left)
    rwa [hr_s]
  rw [hinv] at hrs
  change tR.hom.app (op b₁.left) r ∈ (C.1.preimage wU).obj (op b₁.left) at hrs
  rwa [hr_t] at hrs

/-- **An object whose image in `A'` lies in `A' ∖ D` is in the locus of `w⁻¹C`**, for `C`
containing `P ∖ π⁻¹D`. -/
theorem chartLocus_preimage_of_mem_openComplement
    (hw : representingMap B S hS (schemeFibredCategory B S hS U) (fibredCategory B S hS P.1)
      (yoneda.obj U) P.1 (PresheafOfCategories.sliceElementsEquivalenceOver U)
      (StacksRepresentableCFG.EquivalenceOver.refl _) a.hom = wU)
    (hcg : (c ≫ g).hom = (associatedMap B S hS π.hom).1)
    (D : Space.ClosedSubspaces B S hS A'.1) (C : Space.ClosedSubspaces B S hS P.1)
    (hCD : (Space.openComplementOfClosedSubspace B S hS P
      (Space.preimageClosedSubspace π D)).1 ≤ C.1)
    (x : 𝒳.val.val.obj)
    (hx : (g.hom.hom.obj x).fiber.as ∈
      (Space.openComplementOfClosedSubspace B S hS A' D).1.obj (op (g.hom.hom.obj x).base)) :
    chartLocus (a ≫ c).hom.hom (C.1.preimage wU) x := by
  intro u φ
  have h1 : (g.hom.hom.obj ((a ≫ c).hom.hom.obj u)).fiber.as =
      A'.1.map (g.hom.hom.map φ).base.op (g.hom.hom.obj x).fiber.as :=
    Discrete.eq_of_hom (g.hom.hom.map φ).fiber
  have h2 : (g.hom.hom.obj ((a ≫ c).hom.hom.obj u)).fiber.as ∈
      (Space.openComplementOfClosedSubspace B S hS A' D).1.obj
        (op (g.hom.hom.obj ((a ≫ c).hom.hom.obj u)).base) := by
    rw [h1]
    exact (Space.openComplementOfClosedSubspace B S hS A' D).1.map _ hx
  rw [show g.hom.hom.obj ((a ≫ c).hom.hom.obj u) = _ from
    comp_obj_schemeStackHom_obj_eq hw hcg u] at h2
  refine hCD (op u.left) ?_
  rwa [Space.openComplementOfClosedSubspace_preimageClosedSubspace B S hS π D]

/-- **The locus of an invariant `w⁻¹C` is flat and locally of finite presentation over `A'`**:
the base change of the chart to the locus is a smooth surjection from the stack of `w⁻¹C`. -/
theorem isFlat_and_isLocallyOfFinitePresentation_chartLocus
    (hw : representingMap B S hS (schemeFibredCategory B S hS U) (fibredCategory B S hS P.1)
      (yoneda.obj U) P.1 (PresheafOfCategories.sliceElementsEquivalenceOver U)
      (StacksRepresentableCFG.EquivalenceOver.refl _) a.hom = wU)
    (hcg : (c ≫ g).hom = (associatedMap B S hS π.hom).1)
    (hfS : AlgebraicStacks.IsSmooth B S hS (a ≫ c)) (hfSs : IsSurjective B S hS (a ≫ c))
    (hwsm : Space.IsSmooth B S hS wU) (C : Space.ClosedSubspaces B S hS P.1)
    (hZ : IsChartInvariant (a ≫ c).hom.hom (C.1.preimage wU))
    (hflat : Space.IsFlat B S hS (C.1.ι ≫ π.hom))
    (hlfp : Space.IsLocallyOfFinitePresentation B S hS (C.1.ι ≫ π.hom))
    (hQ : IsAlgebraicStack.{u, w} B S hS
      (fullSubcategoryBased 𝒳 (chartLocus (a ≫ c).hom.hom (C.1.preimage wU)))) :
    AlgebraicStacks.IsFlat B S hS
        (fullSubcategoryInclusion 𝒳 (chartLocus (a ≫ c).hom.hom (C.1.preimage wU)) hQ ≫ g) ∧
      AlgebraicStacks.IsLocallyOfFinitePresentation B S hS
        (fullSubcategoryInclusion 𝒳 (chartLocus (a ≫ c).hom.hom (C.1.preimage wU)) hQ ≫ g) := by
  let f := (a ≫ c).hom.hom
  let Z := C.1.preimage wU
  let L := chartLocus f Z
  let wS : chartSpace U ⟶ P := ObjectProperty.homMk wU
  let Zc : Space.ClosedSubspaces B S hS (chartSpace U).1 := Space.preimageClosedSubspace wS C
  have hZf : Space.IsFlat B S hS (Zc.1.ι ≫ (wS ≫ π).hom) :=
    Space.isFlat_preimageClosedSubspace_ι_comp B S hS wS π C
      (Space.isFlat_of_isSmooth B S hS _ hwsm) hflat
  have hZl : Space.IsLocallyOfFinitePresentation B S hS (Zc.1.ι ≫ (wS ≫ π).hom) :=
    Space.isLocallyOfFinitePresentation_preimageClosedSubspace_ι_comp B S hS wS π C
      (Space.isLocallyOfFinitePresentation_of_isSmooth B S hS hwsm) hlfp
  let incl := fullSubcategoryInclusion 𝒳 L hQ
  let Qc := CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} incl.hom (a ≫ c).hom
  have hQc := CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1}
    incl.hom (a ≫ c).hom
  -- the comparison from the algebraic stack of `Z`
  let K := subspaceToSlice U Z
  have hmem : ∀ z, L (f.obj (K.obj z)) := fun z => (chartLocus_obj_iff hZ _).2 z.fiber.as.2
  let H : (fibredCategory B S hS Z.toFunctor).val.obj ⥤ L.FullSubcategory :=
    L.lift (K.toFunctor ⋙ f.toFunctor) hmem
  have hH : H ⋙ (fullSubcategoryBased 𝒳 L).p = (fibredCategory B S hS Z.toFunctor).val.p := by
    change (K.toFunctor ⋙ f.toFunctor) ⋙ 𝒳.val.val.p = _
    rw [Functor.assoc, f.w]
    exact K.w
  let t : H ⋙ (fullSubcategoryBasedInclusion 𝒳 L).toFunctor ≅ K.toFunctor ⋙ f.toFunctor :=
    Iso.refl _
  have ht : ∀ z, 𝒳.val.val.p.IsHomLift (𝟙 ((fibredCategory B S hS Z.toFunctor).val.p.obj z))
      (t.hom.app z) := fun z => IsHomLift.id (Functor.congr_obj hH z)
  let eF := TwoFibreProductOver.lift (fullSubcategoryBased 𝒳 L).p
    (schemeFibredCategory B S hS U).val.p 𝒳.val.val.p
    (fullSubcategoryBasedInclusion 𝒳 L).toFunctor f.toFunctor
    (fibredCategory B S hS Z.toFunctor).val.p H K.toFunctor hH K.w t ht
  have hZm : ∀ {x : 𝒳.val.val.obj} {u : Over U} (α : f.obj u ⟶ x), L x →
      u.hom ∈ Z.obj (op u.left) := fun α hx =>
    (chartLocus_obj_iff hZ _).1 (chartLocus_of_hom f Z α hx)
  have hess : eF.EssSurj := by
    refine ⟨fun Y => ?_⟩
    obtain ⟨V, x, y, hx, hy, iso, vert⟩ := Y
    change y.left = V at hy
    subst hy
    have hyZ := hZm iso.inv x.property
    let z : (fibredCategory B S hS Z.toFunctor).val.obj := ⟨y.left, Discrete.mk ⟨y.hom, hyZ⟩⟩
    have hvi : 𝒳.val.val.p.IsHomLift (𝟙 y.left) iso.inv := by
      simpa using IsHomLift.inv 𝒳.val.val.p (𝟙 y.left) iso.hom
    let φ : eF.obj z ⟶ ⟨y.left, x, y, hx, rfl, iso, vert⟩ :=
      { hbase := 𝟙 y.left
        a := ObjectProperty.homMk iso.inv
        b := 𝟙 y
        ha := (Functor.isHomLift_comp_iff L.ι 𝒳.val.val.p _ _).2 hvi
        hb := IsHomLift.id rfl
        w := by
          change iso.inv ≫ iso.hom = 𝟙 _ ≫ f.map (𝟙 y)
          simp }
    have : IsIso φ := TwoFibreProductOver.isIso_of_isIso_components _ _ _ _ _ φ
      (by
        change IsIso (ObjectProperty.homMk iso.inv : (⟨_, hmem z⟩ : L.FullSubcategory) ⟶ x)
        have : IsIso (L.ι.map (ObjectProperty.homMk iso.inv :
            (⟨_, hmem z⟩ : L.FullSubcategory) ⟶ x)) := by
          change IsIso iso.inv
          infer_instance
        exact isIso_of_reflects_iso _ L.ι)
      (by change IsIso (𝟙 y); infer_instance)
    exact ⟨z, ⟨asIso φ⟩⟩
  let eB : (fibredCategory B S hS Z.toFunctor).val ⥤ᵇ Qc.pt.val :=
    ⟨eF, TwoFibreProductOver.lift_comp_structureFunctor ..⟩
  let eBc : fibredCategory B S hS Z.toFunctor ⟶ Qc.pt := Bicategory.InducedBicategory.mkHom eB
  have hfa : eF.Faithful := TwoFibreProductOver.faithful_lift _ _ _ _ _ _ _ _ _ _ _ _
  have : (fullSubcategoryBasedInclusion 𝒳 L).toFunctor.Faithful :=
    (inferInstance : L.ι.Faithful)
  have hfu : eF.Full := TwoFibreProductOver.full_lift _ _ _ _ _ _ _ _ _ _ _ _
  have he : Functor.IsEquivalence (CatFiberedInGroupoids.homFunctor eBc) :=
    { faithful := hfa, full := hfu, essSurj := hess }
  let aZ := eBc ≫ Qc.fst
  have ha : IsRelativelySmooth B S hS aZ :=
    isRelativelySmooth_of_isEquivalence_comp B S hS eBc Qc.fst he
      (isRelativelySmooth_baseChange.{u, u, u + 1} B S hS _ _ _ (a ≫ c).hom incl.hom Qc hQc
        (isRelativelySmooth_of_isSmooth_schemeStack B S hS U (a ≫ c) hfS))
  have hasurj : IsSurjectiveOnObjects B S hS (fibredCategory B S hS Z.toFunctor).val.p
      (fullSubcategoryAlgebraicStack 𝒳 L hQ).val.val.p (CatFiberedInGroupoids.homFunctor aZ) := by
    intro V hV y hy
    obtain ⟨V', hV', k, u, hu, α, hα⟩ :=
      isSurjectiveOnObjects_of_pointsMap_surjective B S hS (a ≫ c) hfSs V hV y.obj hy
    exact ⟨V', hV', k, ⟨u.left, Discrete.mk ⟨u.hom, hZm α y.property⟩⟩, hu, ObjectProperty.homMk α,
      (Functor.isHomLift_comp_iff L.ι 𝒳.val.val.p _ _).2 hα⟩
  let b := (associatedMap B S hS (𝟙 A'.1)).1
  have hb : IsRelativelySmooth B S hS b :=
    isRelativelySmooth_associatedMap B S hS A'.2 A'.2 (𝟙 _) (Space.isSmooth_id B S hS A'.2)
  have hiso : (associatedMap B S hS (Zc.1.ι ≫ (wS ≫ π).hom)).1 ≫ b = aZ ≫ (incl ≫ g).hom := by
    refine hom_ext_of_obj B S hS fun z => ?_
    change b.hom.obj ((associatedMap B S hS _).1.hom.obj z) =
      g.hom.hom.obj (c.hom.hom.obj (a.hom.hom.obj (Over.mk z.fiber.as.1)))
    rw [associatedMap_obj, associatedMap_obj, comp_obj_schemeStackHom_obj_eq hw hcg]
    rfl
  exact AlgebraicStacks.isFlat_and_isLocallyOfFinitePresentation_of_smoothDiagram B S hS
    (incl ≫ g) Zc.2.1 A'.2 aZ b _ (eqToIso hiso) ha hasurj hb hZf hZl

end ChartSections

/-- **A smooth surjective chart by a scheme is locally essentially surjective.** -/
theorem isChartLocallyEssSurj_of_isSmooth_of_isSurjective {𝒳 : AlgebraicStacks.{u, w} B S hS}
    {U : BigFppfOver B S hS} (f : schemeStack.{u, w} B S hS U ⟶ 𝒳)
    (hsm : AlgebraicStacks.IsSmooth B S hS f) (hsu : IsSurjective B S hS f) :
    IsChartLocallyEssSurj f.hom.hom := by
  obtain ⟨hrep, hsmooth⟩ := isRelativelySmooth_of_isSmooth_schemeStack B S hS U f hsm
  have hsurj := (pointsMap_surjective_iff_isRelativelySurjective.{u, w, u} B S hS f hrep).mp hsu
  exact localEssSurj_of_isSurjective_isSmooth B S hS f.hom hrep
    (fun V y hy G hG he => ⟨hsurj V y hy G hG he, hsmooth V y hy G hG he⟩)

/-- **A flat closed subspace of a chart containing `P ∖ π⁻¹D` descends to a closed substack**
of `𝒳` containing every object over `A' ∖ D`, flat and locally of finite presentation over `A'`
(the descent step of **Stacks 0CQ4**, via **Stacks 0507**). -/
theorem exists_isClosedSubstack_isFlat_isLocallyOfFinitePresentation_of_openComplement_le
    {𝒳 : AlgebraicStacks.{u, w} B S hS} {A' P : AlgebraicSpaces B S hS}
    (g : 𝒳 ⟶ algebraicSpaceStack.{u, w} B S hS A'.1 A'.2)
    (c : algebraicSpaceStack.{u, w} B S hS P.1 P.2 ⟶ 𝒳) (hc : AlgebraicStacks.IsSmooth B S hS c)
    (hcs : IsSurjective B S hS c) (π : P ⟶ A')
    (e : Nonempty (c ≫ g ≅ algebraicSpaceStackMap.{u, w} B S hS P.2 A'.2 π.hom))
    (D : Space.ClosedSubspaces B S hS A'.1) (hD : Space.IsEffectiveCartierDivisor B S hS A' D)
    (C : Space.ClosedSubspaces B S hS P.1)
    (hCD : (Space.openComplementOfClosedSubspace B S hS P
      (Space.preimageClosedSubspace π D)).1 ≤ C.1)
    (hflat : Space.IsFlat B S hS (C.1.ι ≫ π.hom))
    (hlfp : Space.IsLocallyOfFinitePresentation B S hS (C.1.ι ≫ π.hom)) :
    ∃ Q : ObjectProperty 𝒳.val.val.obj, IsClosedSubstack 𝒳 Q ∧
      (∀ x : 𝒳.val.val.obj, (g.hom.hom.obj x).fiber.as ∈
          (Space.openComplementOfClosedSubspace B S hS A' D).1.obj (op (g.hom.hom.obj x).base) →
        Q x) ∧
      ∀ hQ : IsAlgebraicStack.{u, w} B S hS (fullSubcategoryBased 𝒳 Q),
        AlgebraicStacks.IsFlat B S hS (fullSubcategoryInclusion 𝒳 Q hQ ≫ g) ∧
          AlgebraicStacks.IsLocallyOfFinitePresentation B S hS
            (fullSubcategoryInclusion 𝒳 Q hQ ≫ g) := by
  obtain ⟨e⟩ := e
  have hcg : (c ≫ g).hom = (associatedMap B S hS π.hom).1 := hom_eq_of_hom₂ B S hS e.hom.hom
  obtain ⟨U, a, ham, has⟩ :=
    exists_smooth_surjective_schemeStack.{u, w} B S hS (algebraicSpaceStack.{u, w} B S hS P.1 P.2)
  let wU := representingMap B S hS (schemeFibredCategory B S hS U) (fibredCategory B S hS P.1)
    (yoneda.obj U) P.1 (PresheafOfCategories.sliceElementsEquivalenceOver U)
    (StacksRepresentableCFG.EquivalenceOver.refl _) a.hom
  have hsm : Space.IsSmoothLocalOnSourceAndTarget B S hS
      (fun _ _ k => Space.IsSmooth B S hS k) := Space.isSmoothLocalOnSourceAndTarget_smooth B S hS
  have hwsm : Space.IsSmooth B S hS wU :=
    isSmooth_representingMap_of_isSmooth B S hS hsm
      (𝒳 := schemeStack.{u, w} B S hS U) (𝒴 := algebraicSpaceStack.{u, w} B S hS P.1 P.2)
      (yoneda.obj U) P.1 (isAlgebraicSpace_yoneda B S hS U) P.2
      (PresheafOfCategories.sliceElementsEquivalenceOver U)
      (StacksRepresentableCFG.EquivalenceOver.refl _) a ham
  have hfS : AlgebraicStacks.IsSmooth B S hS (a ≫ c) :=
    AlgebraicStacks.isSmooth_comp B S hS a c ham hc
  have hfSs : IsSurjective B S hS (a ≫ c) := isSurjective_comp B S hS a c has hcs
  have hZ := isChartInvariant_preimage_of_isFlat (wU := wU) rfl hcg hfS hwsm D hD C hCD hflat
  have hZc : Space.IsClosedSubspace B S hS (C.1.preimage wU) :=
    (Space.preimageClosedSubspace (ObjectProperty.homMk wU : chartSpace U ⟶ P) C).2
  exact ⟨chartLocus (a ≫ c).hom.hom (C.1.preimage wU),
    isClosedSubstack_chartLocus hZ hZc
      (isChartLocallyEssSurj_of_isSmooth_of_isSurjective _ hfS hfSs),
    fun x hx => chartLocus_preimage_of_mem_openComplement (wU := wU) rfl hcg D C hCD x hx,
    fun hQ => isFlat_and_isLocallyOfFinitePresentation_chartLocus (wU := wU) rfl hcg hfS hfSs hwsm C
      hZ hflat hlfp hQ⟩

end AlgebraicGeometry.Stack

end
