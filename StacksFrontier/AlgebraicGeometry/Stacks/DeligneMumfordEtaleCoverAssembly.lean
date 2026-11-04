module

public import StacksFrontier.AlgebraicGeometry.Stacks.BaseChangeRepresentableBySpace
public import StacksFrontier.AlgebraicGeometry.Stacks.ClosureImageValuativePoint
public import StacksFrontier.AlgebraicGeometry.Stacks.DeligneMumfordStack
public import StacksFrontier.AlgebraicGeometry.Stacks.EtaleChartDiagramTest
public import StacksFrontier.AlgebraicGeometry.Stacks.FiniteTypePointsLocallyClosedChart
public import StacksFrontier.AlgebraicGeometry.Stacks.OpenImageSubstack
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentableDeligneMumford
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalPropertyAtlasBridges

/-!
# An étale 1-morphism from a scheme hitting every finite type point is a DM presentation

Let `𝒳` be an algebraic stack and `f : Z ⟶ 𝒳` an étale 1-morphism (Stacks 04XB) from a scheme
of the site. If every finite type point of `|𝒳|` is in the image of `|Z| ⟶ |𝒳|`, then `f` is
surjective, so `𝒳` is a Deligne–Mumford stack (Stacks 03YO).

This is the final step of the proof of Stacks 06N3: the image of `|Z|` is open, because an étale
1-morphism is smooth and smooth 1-morphisms are open on points, and an open subset of `|𝒳|`
containing every finite type point is everything (Stacks 06G2).

## Main results

* `AlgebraicGeometry.Stack.isDeligneMumfordStack_of_isRelativelyEtale_of_finiteTypePoints`.
* `AlgebraicGeometry.Stack.exists_smoothChart_etaleChart_twoFibreProduct`: a smooth surjective
  scheme chart `W ⟶ 𝒳` together with an étale scheme chart `E` of `W ×_𝒳 W` whose two
  projections are induced by smooth morphisms of the site; the data the étale slices are cut
  from.
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **An étale 1-morphism from a scheme whose image contains every finite type point is a
surjective étale presentation.** Let `𝒳` be an algebraic stack over `S` and `f` a 1-morphism
from the category represented by a scheme `Z` of the site, étale in the sense of Stacks 04XB. If
every finite type point of `|𝒳|` lies in the image of `|Z|`, then `𝒳` is Deligne–Mumford. -/
theorem isDeligneMumfordStack_of_isRelativelyEtale_of_finiteTypePoints
    (𝒳 : AlgebraicStacks.{u, w} B S hS) (Z : BigFppfOver B S hS)
    (f : schemeFibredCategory B S hS Z ⟶ 𝒳.val) (hf : IsRelativelyEtale B S hS f)
    (hft : finiteTypePoints.{u, w} B S hS 𝒳 ⊆ Set.range (AlgebraicStacks.pointsMap B S hS
      (Bicategory.InducedBicategory.mkHom f : schemeStack.{u, w} B S hS Z ⟶ 𝒳))) :
    IsDeligneMumfordStack.{u, w} B S hS 𝒳.val.val := by
  let f' : schemeStack.{u, w} B S hS Z ⟶ 𝒳 := Bicategory.InducedBicategory.mkHom f
  have hsmooth : IsRelativelySmooth B S hS f := isRelativelySmooth_of_isRelativelyEtale B S hS f hf
  have hsm : AlgebraicStacks.IsSmooth B S hS f' :=
    hasPropertyOnSomeSmoothDiagram_of_hasRelativeProperty.{u, w, u} B S hS
      (fun _ _ k => Space.IsSmooth B S hS k) 𝒳.property f hf.1
      (fun V y hy G hG he => hsmooth.2 V y hy G hG he)
  have hopen := isOpen_range_pointsMap_of_isSmooth B S hS f' hsm
  have huniv := eq_univ_of_isOpen_of_finiteTypePoints_subset.{u, w} B S hS 𝒳 _ hopen hft
  have hsurj : Function.Surjective (AlgebraicStacks.pointsMap B S hS f') :=
    fun x => (Set.ext_iff.1 huniv x).2 (Set.mem_univ x)
  have hrel := (pointsMap_surjective_iff_isRelativelySurjective.{u, w, u} B S hS f' hf.1).1 hsurj
  exact ⟨𝒳.property, 𝒳.val.property, Z, f, hf.1,
    fun V y hy F hF he => ⟨hrel V y hy F hF he, hf.2 V y hy F hF he⟩⟩

/-- **A 1-morphism between represented categories is 2-isomorphic to the one induced by its
underlying morphism of the site** (the 2-Yoneda lemma, at the level of categories fibred in
groupoids). -/
theorem nonempty_iso_schemeFibredCategoryMap {U V : BigFppfOver B S hS}
    (x : schemeFibredCategory B S hS U ⟶ schemeFibredCategory B S hS V) :
    Nonempty (schemeFibredCategoryMap B S hS (schemeMapOfFunctor B S hS x.hom) ≅ x) := by
  let η : x ⟶ schemeFibredCategoryMap B S hS (schemeMapOfFunctor B S hS x.hom) :=
    Bicategory.InducedBicategory.mkHom₂
      (basedNatTransOfSchemeMapEq B S hS x.hom
        (overMapBased B S hS (schemeMapOfFunctor B S hS x.hom))
        (schemeMapOfFunctor_overMapBased B S hS (schemeMapOfFunctor B S hS x.hom)).symm)
  exact ⟨(@asIso _ _ _ _ η ((CatFiberedInGroupoids.homGroupoid _ _).all_isIso η)).symm⟩

/-- **A morphism of the site inducing a smooth 1-morphism is smooth**: the bridge of Stacks 04XB
at the smooth property, with the induced morphism of representable algebraic spaces computed by
`AlgebraicGeometry.Stack.representingMap_schemeFibredCategoryMap`. -/
theorem smooth_of_isRelativelySmooth_schemeFibredCategoryMap {U V : BigFppfOver B S hS}
    (g : U ⟶ V) (h : IsRelativelySmooth B S hS (schemeFibredCategoryMap B S hS g)) :
    Smooth ((BigFppfOver.toScheme B S hS).map g) := by
  have h' := (isRelativelySmooth_iff_isSmooth_representingMap B S hS _ h.1 (yoneda.obj U)
    (yoneda.obj V) (isAlgebraicSpace_yoneda B S hS U) (isAlgebraicSpace_yoneda B S hS V)
    (PresheafOfCategories.sliceElementsEquivalenceOver U)
    (PresheafOfCategories.sliceElementsEquivalenceOver V)).1 h
  rw [representingMap_schemeFibredCategoryMap] at h'
  exact Space.smooth_of_isSmooth_yonedaMap B S hS g h'

/-- **A smooth 1-morphism composed with an étale one is induced by a smooth morphism of the
site.** -/
private theorem exists_smooth_map_iso_comp {W E : BigFppfOver B S hS}
    {X : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
    {c : schemeFibredCategory B S hS E ⟶ X} {P : X ⟶ schemeFibredCategory B S hS W}
    (hc : IsRelativelyEtale B S hS c)
    (hP : IsRelativelySmooth B S hS P) :
    ∃ s : E ⟶ W, Nonempty (schemeFibredCategoryMap B S hS s ≅ c ≫ P) ∧
      Smooth ((BigFppfOver.toScheme B S hS).map s) := by
  obtain ⟨e⟩ := nonempty_iso_schemeFibredCategoryMap B S hS (c ≫ P)
  exact ⟨_, ⟨e⟩, smooth_of_isRelativelySmooth_schemeFibredCategoryMap B S hS _
    (isRelativelySmooth_congr_twoIso B S hS e.symm (isRelativelySmooth_comp B S hS _ _
      (isRelativelySmooth_of_isRelativelyEtale B S hS c hc) hP))⟩

/-- **The charts the étale slices of Stacks 06N3 are cut from.** Every algebraic stack `𝒳` over
`S` has a smooth surjective 1-morphism `b` from (the category represented by) a scheme `W` of the
site, and the canonical 2-fibre product `W ×_𝒳 W` has an étale 1-morphism `c` from a scheme `E`
of the site, surjective on objects, whose composites with the two projections are induced by
morphisms `s, t : E ⟶ W` of the site. -/
theorem exists_smoothChart_etaleChart_twoFibreProduct (𝒳 : AlgebraicStacks.{u, w} B S hS) :
    ∃ (W : BigFppfOver B S hS) (b : schemeFibredCategory B S hS W ⟶ 𝒳.val),
      IsRelativelySmooth B S hS b ∧
      Function.Surjective (AlgebraicStacks.pointsMap B S hS
        (Bicategory.InducedBicategory.mkHom b : schemeStack.{u, w} B S hS W ⟶ 𝒳)) ∧
      ∃ (E : BigFppfOver B S hS) (c : schemeFibredCategory B S hS E ⟶
          (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} b b).pt),
        IsRelativelyEtale B S hS c ∧
        IsSurjectiveOnObjects B S hS (schemeFibredCategory B S hS E).val.p
          (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} b b).pt.val.p
          (CatFiberedInGroupoids.homFunctor c) ∧
        ∃ (s t : E ⟶ W), Nonempty (schemeFibredCategoryMap B S hS s ≅
            c ≫ (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} b b).fst) ∧
          Nonempty (schemeFibredCategoryMap B S hS t ≅
            c ≫ (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} b b).snd) ∧
          Smooth ((BigFppfOver.toScheme B S hS).map s) ∧
          Smooth ((BigFppfOver.toScheme B S hS).map t) := by
  obtain ⟨hfib, -, -, W, a, hrep, ha⟩ := 𝒳.property
  let b : schemeFibredCategory B S hS W ⟶ 𝒳.val := Bicategory.InducedBicategory.mkHom a
  have hb : IsRelativelySmooth B S hS b := ⟨hrep, fun V y hy G hG he => (ha V y hy G hG he).2⟩
  let b' : schemeStack.{u, w} B S hS W ⟶ 𝒳 := Bicategory.InducedBicategory.mkHom b
  have hbsurj : Function.Surjective (AlgebraicStacks.pointsMap B S hS b') :=
    (pointsMap_surjective_iff_isRelativelySurjective.{u, w, u} B S hS b' hrep).2
      (fun V y hy G hG he => (ha V y hy G hG he).1)
  set Q₀ := CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} b b with hQ₀def
  have hQ₀ : Bicategory.IsTwoFibreProduct Q₀ :=
    CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1} b b
  have hrepQ : IsRepresentableByAlgebraicSpace B S hS Q₀.pt :=
    isRepresentableByAlgebraicSpace_of_isTwoFibreProduct.{u, u, u + 1} B S hS
      (schemeFibredCategory B S hS W) 𝒳.val (schemeFibredCategory B S hS W) b b Q₀ hQ₀ hrep
      (isRepresentableByAlgebraicSpace_schemeFibredCategory B S hS W)
  obtain ⟨E, c, hc, hcsurj⟩ := exists_etalePresentation_of_isDeligneMumfordStack.{u, w} B S hS
    (isDeligneMumfordStack_of_isRepresentableByAlgebraicSpace.{u, w} B S hS Q₀.pt hrepQ)
  obtain ⟨s, hs, hsm⟩ := exists_smooth_map_iso_comp B S hS hc
    (isRelativelySmooth_baseChange.{u, u, u + 1} B S hS _ _ _ b b Q₀ hQ₀ hb)
  obtain ⟨t, ht, htm⟩ := exists_smooth_map_iso_comp B S hS hc
    (isRelativelySmooth_baseChange.{u, u, u + 1} B S hS _ _ _ b b Q₀.swap
      (Bicategory.isTwoFibreProduct_swap hQ₀) hb)
  exact ⟨W, b, hb, hbsurj, E, c, hc, hcsurj, s, t, hs, ht, hsm, htm⟩

end AlgebraicGeometry.Stack

end
