module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.LocallyCompactPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothFlat
public import StacksFrontier.AlgebraicGeometry.Stacks.PointsSurjective
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiCompactStack
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertyInvariance
public import StacksFrontier.AlgebraicGeometry.Stacks.SchemeStack
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothPresentationQuasiCompact

/-!
# Local quasi-compactness of the point space of an algebraic stack

Every point of the space of points `|𝒳|` of an algebraic stack `𝒳` has a fundamental system of
quasi-compact open neighbourhoods. In particular `|𝒳|` is locally quasi-compact, that is, a
`LocallyCompactSpace`.

## Main results

* `AlgebraicGeometry.Stack.exists_spaceChart_isOpenMap_surjective`: an algebraic stack admits a
  chart by an algebraic space whose canonical map on points is a continuous open surjection.
* `AlgebraicGeometry.Stack.hasBasis_nhds_isOpen_isCompact`: the quasi-compact open
  neighbourhoods of a point of `|𝒳|` are a fundamental system of neighbourhoods.
* `AlgebraicGeometry.Stack.locallyCompactSpace`: `|𝒳|` is locally quasi-compact.

## Implementation notes

`AlgebraicGeometry.Stack.pointTopology` and `AlgebraicGeometry.Space.pointTopology` are plain
definitions rather than instances and are made local instances here.

## References

* [Stacks Project, Tag 0068](https://stacks.math.columbia.edu/tag/0068)
* [Stacks Project, Tag 026O](https://stacks.math.columbia.edu/tag/026O)
* [Stacks Project, Tag 04NN](https://stacks.math.columbia.edu/tag/04NN)
* [Stacks Project, Tag 04XG](https://stacks.math.columbia.edu/tag/04XG)
* [Stacks Project, Tag 04XL](https://stacks.math.columbia.edu/tag/04XL)
* [Stacks Project, Tag 04Y9](https://stacks.math.columbia.edu/tag/04Y9)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

attribute [local instance] Space.pointTopology pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS))

/-- An algebraic stack `𝒳` over `S` admits a chart `f` by an algebraic space `F` whose map on
points `|F| → |𝒳|` is continuous, open and surjective. -/
theorem exists_spaceChart_isOpenMap_surjective
    (h𝒳 : IsAlgebraicStack.{u, w} B S hS 𝒳.val) :
    ∃ (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (_hF : IsAlgebraicSpace B S hS F)
      (f : (fibredCategory B S hS F).val ⥤ᵇ 𝒳.val),
      Continuous (spacePointMap B S hS F 𝒳 f) ∧ IsOpenMap (spacePointMap B S hS F 𝒳 f) ∧
        Function.Surjective (spacePointMap B S hS F 𝒳 f) := by
  obtain ⟨_hFib, -, -, U, fU, hfU, hAtlas⟩ := id h𝒳
  have hU := isAlgebraicSpace_yoneda B S hS U
  let Ucfg := schemeFibredCategory B S hS U
  let e := schemeFibredCategoryEquivalence B S hS U
  let aU := e.inverse
  have haU : Functor.IsEquivalence aU.toFunctor := e.equiv.isEquivalence_inverse
  have hid : Functor.IsEquivalence (BasedFunctor.id 𝒳.val).toFunctor :=
    inferInstanceAs (Functor.IsEquivalence (𝟭 𝒳.val.obj))
  refine ⟨yoneda.obj U, hU, aU.comp fU, continuous_spacePointMap B S hS _ hU 𝒳 _, ?_, ?_⟩
  · refine isOpenMap_spacePointMap B S hS (yoneda.obj U) hU 𝒳 h𝒳 (aU.comp fU) ?_
    refine relativeProperty_of_equivalences B S hS
      (fun _ _ k ↦ Space.IsFlat B S hS k.hom ∧
        Space.IsLocallyOfFinitePresentation B S hS k.hom)
      (aU.comp fU) fU aU (BasedFunctor.id 𝒳.val) (Iso.refl _) ?_
    intro V y hy G hG hE
    have hsm := (hAtlas V y hy G hG hE).2
    exact ⟨Space.isFlat_of_isSmooth B S hS _ hsm,
      Space.isLocallyOfFinitePresentation_of_isSmooth B S hS hsm⟩
  · let Xalg : AlgebraicStacks.{u, w} B S hS := ⟨𝒳, h𝒳⟩
    let Ualg : AlgebraicStacks.{u, w} B S hS :=
      ⟨Ucfg, isAlgebraicStack_schemeFibredCategory B S hS U⟩
    let falg : Ualg ⟶ Xalg := Bicategory.InducedBicategory.mkHom
      (Bicategory.InducedBicategory.mkHom fU)
    have hfUsurj := (pointsMap_surjective_iff_isRelativelySurjective.{u, w, u} B S hS
      falg hfU).2 fun V y hy G hG hE ↦ (hAtlas V y hy G hG hE).1
    rw [spacePointMap_comp B S hS (yoneda.obj U) Ucfg 𝒳 aU fU]
    exact hfUsurj.comp ((spacePointMap_surjective_iff_pointsMap_surjective B S hS
      (yoneda.obj U) Ucfg aU).2
      (pointsMap_surjective_of_basedEquivalence B S hS
        (𝒜 := fibredCategory B S hS (yoneda.obj U)) (𝒞 := Ucfg) e.symm))

/-- The quasi-compact open neighbourhoods of a point of the space of points of an algebraic
stack over `S` are a fundamental system of neighbourhoods of that point. -/
@[stacks 04Y9 "fundamental system of quasi-compact open neighbourhoods"]
theorem hasBasis_nhds_isOpen_isCompact (h𝒳 : IsAlgebraicStack.{u, w} B S hS 𝒳.val)
    (x : points B S hS 𝒳.val 𝒳.property) :
    (nhds x).HasBasis
      (fun W : Set (points B S hS 𝒳.val 𝒳.property) ↦ IsOpen W ∧ IsCompact W ∧ x ∈ W) id := by
  obtain ⟨F, hF, f, hcont, hopen, hsurj⟩ :=
    exists_spaceChart_isOpenMap_surjective B S hS 𝒳 h𝒳
  exact hopen.hasBasis_nhds_isOpen_isCompact hcont hsurj
    (Space.hasBasis_nhds_isOpen_isCompact B S hS F hF) x

/-- The space of points of an algebraic stack over `S` is locally quasi-compact, that is, a
`LocallyCompactSpace`. -/
@[stacks 04Y9 "local quasi-compactness"]
theorem locallyCompactSpace (h𝒳 : IsAlgebraicStack.{u, w} B S hS 𝒳.val) :
    LocallyCompactSpace (points B S hS 𝒳.val 𝒳.property) :=
  LocallyCompactSpace.of_hasBasis
    (hasBasis_nhds_isOpen_isCompact B S hS 𝒳 h𝒳) fun _ _ h ↦ h.2.1

end AlgebraicGeometry.Stack

end
