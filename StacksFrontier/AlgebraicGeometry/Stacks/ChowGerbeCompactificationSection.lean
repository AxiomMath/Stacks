module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ProperFlatBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.FpqcOpenSubspaceDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.InvariantSubspace
public import StacksFrontier.AlgebraicGeometry.Stacks.ChowGerbeCompactification
public import StacksFrontier.AlgebraicGeometry.Stacks.PresheafFibredCategoryHomGluing
public import StacksFrontier.AlgebraicGeometry.Stacks.PresheafFibredCategoryTwoFibreProduct
public import StacksFrontier.AlgebraicGeometry.Stacks.ProperCancellation
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeDiagonalMonomorphism

/-!
# Proper compactifiable covers from a section over a preimage

Let `f : 𝒳 ⟶ Y` be a separated 1-morphism from an algebraic stack to an algebraic space whose
values lie in an open subspace `W ⊆ Y`, let `p : Y' ⟶ Y` be a proper morphism of algebraic spaces
and let `x : p⁻¹(W) ⟶ 𝒳` be a 1-morphism with `x ≫ f` 2-isomorphic to `p⁻¹(W) ⟶ Y' ⟶ Y`. Then
`Z̄ = Y'`, `Z = p⁻¹(W)` and `h = x` solve Stacks 0CQ7 for every `V ⊆ Y` whose points are images of
points of `p⁻¹(W)`.

## Main definitions

* `AlgebraicGeometry.Stack.AlgebraicStacks.corestrictAlgebraicSpaceStack`: the corestriction
  of a 1-morphism into the stack of an algebraic space to a subspace containing its values.

## Main results

* `AlgebraicGeometry.Stack.AlgebraicStacks.exists_algebraicSpaceStack_hom_of_cocycle`: gluing
  1-morphisms out of an algebraic space along a covering family of algebraic subspaces.
* `AlgebraicGeometry.Stack.AlgebraicStacks.HasProperCompactifiableCover.of_section_preimage`:
  a 1-morphism `x : p⁻¹(W) ⟶ 𝒳` over `Y` from the preimage of `W` under a proper `p : Y' ⟶ Y`
  solves Stacks 0CQ7 over every `V ⊆ Y` covered by the image of `p⁻¹(W)`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite CategoryTheory.PresheafOfCategories

universe u w

namespace AlgebraicGeometry.Stack.AlgebraicStacks

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- The element of `Y` named by a 1-morphism `f : 𝒳 ⟶ Y` at an object of `𝒳`. -/
abbrev algebraicSpaceStackSection {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {hY : IsAlgebraicSpace B S hS Y} {𝒳 : AlgebraicStacks.{u, w} B S hS}
    (f : 𝒳 ⟶ algebraicSpaceStack.{u, w} B S hS Y hY) (ξ : 𝒳.val.val.obj) :
    Y.obj (op (𝒳.val.val.p.obj ξ)) :=
  sectionOfBasedFunctor f.hom.hom.toFunctor f.hom.hom.w ξ

/-- **The corestriction of a 1-morphism into the stack of an algebraic space** to a subspace `W`
containing all the elements it names. -/
def corestrictAlgebraicSpaceStack {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {hY : IsAlgebraicSpace B S hS Y} {𝒳 : AlgebraicStacks.{u, w} B S hS}
    (f : 𝒳 ⟶ algebraicSpaceStack.{u, w} B S hS Y hY) (W : Subfunctor Y)
    (hW : IsAlgebraicSpace B S hS W.toFunctor)
    (hfW : ∀ ξ, algebraicSpaceStackSection f ξ ∈ W.obj (op (𝒳.val.val.p.obj ξ))) :
    𝒳 ⟶ algebraicSpaceStack.{u, w} B S hS W.toFunctor hW :=
  Bicategory.InducedBicategory.mkHom
    (basedFunctorOfSections (𝒳 := 𝒳.val) (fun ξ => ⟨algebraicSpaceStackSection f ξ, hfW ξ⟩)
      (fun u => Subtype.ext (sectionOfBasedFunctor_map f.hom.hom.toFunctor f.hom.hom.w u)))

/-- The corestriction followed by the inclusion of `W` is the 1-morphism it corestricts. -/
theorem corestrictAlgebraicSpaceStack_comp {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {hY : IsAlgebraicSpace B S hS Y} {𝒳 : AlgebraicStacks.{u, w} B S hS}
    (f : 𝒳 ⟶ algebraicSpaceStack.{u, w} B S hS Y hY) (W : Subfunctor Y)
    (hW : IsAlgebraicSpace B S hS W.toFunctor)
    (hfW : ∀ ξ, algebraicSpaceStackSection f ξ ∈ W.obj (op (𝒳.val.val.p.obj ξ))) :
    corestrictAlgebraicSpaceStack f W hW hfW ≫ algebraicSpaceStackMap.{u, w} B S hS hW hY W.ι =
      f := by
  refine Bicategory.InducedBicategory.hom_ext (hom_ext_of_section B S hS _ _ fun ξ => ?_)
  refine (section_comp_associatedMap W.ι (corestrictAlgebraicSpaceStack f W hW hfW).hom ξ).trans ?_
  have h := section_basedFunctorOfSections (𝒳 := 𝒳.val) (T := W.toFunctor)
    (fun ξ => (⟨algebraicSpaceStackSection f ξ, hfW ξ⟩ : W.toFunctor.obj (op (𝒳.val.val.p.obj ξ))))
    (fun u => Subtype.ext (sectionOfBasedFunctor_map f.hom.hom.toFunctor f.hom.hom.w u)) ξ
  exact congrArg (W.ι.app _) h

/-- **Gluing 1-morphisms out of an algebraic space into an algebraic stack** along a covering
family of algebraic subspaces `U i ⊆ Z`: the form of
`AlgebraicGeometry.Stack.exists_hom_associatedMap_comp_iso_of_cocycle` in the 2-category of
algebraic stacks. -/
theorem exists_algebraicSpaceStack_hom_of_cocycle {Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hZ : IsAlgebraicSpace B S hS Z) {ι : Type*} (U : ι → Subfunctor Z)
    (hU : ∀ i, IsAlgebraicSpace B S hS (U i).toFunctor) {𝒳 : AlgebraicStacks.{u, w} B S hS}
    (x : ∀ i, algebraicSpaceStack.{u, w} B S hS (U i).toFunctor (hU i) ⟶ 𝒳)
    (φ : ∀ i j (a : (fibredCategory B S hS Z).val.obj) (hi : a.fiber.as ∈ (U i).obj (op a.base))
      (hj : a.fiber.as ∈ (U j).obj (op a.base)),
      (x i).hom.hom.obj (fibredCategorySubfunctorObj (U i) a hi) ⟶
        (x j).hom.hom.obj (fibredCategorySubfunctorObj (U j) a hj))
    (hlift : ∀ i j a hi hj, 𝒳.val.val.p.IsHomLift (𝟙 a.base) (φ i j a hi hj))
    (hnat : ∀ i j {a b : (fibredCategory B S hS Z).val.obj} (m : a ⟶ b) hai haj hbi hbj,
      (x i).hom.hom.map (fibredCategorySubfunctorHom (U i) m hai hbi) ≫ φ i j b hbi hbj =
        φ i j a hai haj ≫ (x j).hom.hom.map (fibredCategorySubfunctorHom (U j) m haj hbj))
    (hcoc : ∀ i j k a hi hj hk, φ i j a hi hj ≫ φ j k a hj hk = φ i k a hi hk)
    (hcov : ∀ (T : BigFppfOver B S hS) (z : Z.obj (op T)), ∃ R ∈ BigFppfOver.topology B S hS T,
      ∀ ⦃V : BigFppfOver B S hS⦄ ⦃f : V ⟶ T⦄, R.arrows f → ∃ i, Z.map f.op z ∈ (U i).obj (op V)) :
    ∃ y : algebraicSpaceStack.{u, w} B S hS Z hZ ⟶ 𝒳,
      ∀ i, Nonempty (algebraicSpaceStackMap.{u, w} B S hS (hU i) hZ (U i).ι ≫ y ≅ x i) := by
  obtain ⟨y, hy⟩ := exists_hom_associatedMap_comp_iso_of_cocycle U (fun i => (x i).hom) φ hlift
    hnat hcoc (isStack_fibredCategory B S hS Z hZ) 𝒳.property.choose_spec.1.1 hcov
  exact ⟨Bicategory.InducedBicategory.mkHom y,
    fun i => ⟨Bicategory.InducedBicategory.isoMk (hy i).some⟩⟩

/-- Postcomposition with the 1-morphism of the inclusion of a subspace is injective. -/
theorem eq_of_comp_algebraicSpaceStackMap_ι {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hY : IsAlgebraicSpace B S hS Y) {W : Subfunctor Y} (hW : IsAlgebraicSpace B S hS W.toFunctor)
    {𝒳 : AlgebraicStacks.{u, w} B S hS}
    {g g' : 𝒳 ⟶ algebraicSpaceStack.{u, w} B S hS W.toFunctor hW}
    (h : g ≫ algebraicSpaceStackMap.{u, w} B S hS hW hY W.ι =
      g' ≫ algebraicSpaceStackMap.{u, w} B S hS hW hY W.ι) : g = g' := by
  refine Bicategory.InducedBicategory.hom_ext (hom_ext_of_section B S hS _ _ fun ξ => ?_)
  have h' := congrArg (fun t => sectionOfBasedFunctor t.hom.hom.toFunctor t.hom.hom.w ξ) h
  exact Subtype.ext ((section_comp_associatedMap W.ι g.hom ξ).symm.trans
    (h'.trans (section_comp_associatedMap W.ι g'.hom ξ)))

/-- Let `f : 𝒳 ⟶ Y` be a separated 1-morphism from an algebraic stack to an algebraic space all
of whose values lie in an open subspace `W ⊆ Y`, let `p : Y' ⟶ Y` be a proper morphism of
algebraic spaces, and let `x : p⁻¹(W) ⟶ 𝒳` be a 1-morphism with `x ≫ f` 2-isomorphic to
`p⁻¹(W) ⟶ Y' ⟶ Y`. Then the conclusion of Stacks 0CQ7 holds for every `V ⊆ Y` whose points are
images of points of `p⁻¹(W)`, with `Z̄ = Y'`, `Z = p⁻¹(W)` and `h = x`. -/
theorem HasProperCompactifiableCover.of_section_preimage {Y Y' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hY : IsAlgebraicSpace B S hS Y) (hY' : IsAlgebraicSpace B S hS Y')
    {𝒳 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ algebraicSpaceStack.{u, w} B S hS Y hY)
    (hf : IsSeparated B S hS f) (W : Subfunctor Y) (hW : Space.IsOpenSubspace B S hS W)
    (hfW : ∀ ξ, algebraicSpaceStackSection f ξ ∈ W.obj (op (𝒳.val.val.p.obj ξ)))
    (p : Y' ⟶ Y) (hp : Space.IsProper B S hS p)
    (x : algebraicSpaceStack.{u, w} B S hS (W.preimage p).toFunctor
      (Space.isOpenSubspace_preimage B S hS p W hY hY' hW).1 ⟶ 𝒳)
    (hx : Nonempty (x ≫ f ≅ algebraicSpaceStackMap.{u, w} B S hS
      (Space.isOpenSubspace_preimage B S hS p W hY hY' hW).1 hY ((W.preimage p).ι ≫ p)))
    (V : Subfunctor Y)
    (hV : Set.range (Space.pointsMap B S hS V.toFunctor V.ι) ⊆
      Set.range (Space.pointsMap B S hS (W.preimage p).toFunctor ((W.preimage p).ι ≫ p))) :
    HasProperCompactifiableCover.{u, w} B S hS hY f V := by
  have hW' := Space.isOpenSubspace_preimage B S hS p W hY hY' hW
  obtain ⟨e⟩ := hx
  let fW := corestrictAlgebraicSpaceStack f W hW.1 hfW
  have hfWsep : IsSeparated B S hS fW :=
    isSeparated_of_comp_of_isSeparated_diagonal B S hS fW _
      (by rwa [corestrictAlgebraicSpaceStack_comp])
      (Stack.isSeparated_of_isProper B S hS _
        ((isSeparated_algebraicSpaceStackMap_iff.{u, w} B S hS hW.1 hY W.ι).2
          (Space.isSeparated_of_mono W.ι inferInstance)))
  have hcomp : x ≫ fW = algebraicSpaceStackMap.{u, w} B S hS hW'.1 hW.1 (W.fromPreimage p) := by
    refine eq_of_comp_algebraicSpaceStackMap_ι hY hW.1 ?_
    have h2 : algebraicSpaceStackMap.{u, w} B S hS hW'.1 hW.1 (W.fromPreimage p) ≫
        algebraicSpaceStackMap.{u, w} B S hS hW.1 hY W.ι =
          algebraicSpaceStackMap.{u, w} B S hS hW'.1 hY ((W.preimage p).ι ≫ p) := by
      rw [← Subfunctor.fromPreimage_ι]
      simp only [algebraicSpaceStackMap, associatedMap_comp]
      rfl
    rw [Category.assoc, corestrictAlgebraicSpaceStack_comp, h2]
    exact Bicategory.InducedBicategory.hom_ext (hom_eq_of_hom₂ B S hS e.hom.hom)
  have hpW : Space.IsProper B S hS (W.fromPreimage p) :=
    Space.isProper_of_isPullback B S hS hW'.1 hY' hW.1 hY
      (Subfunctor.isPullback_fromPreimage W p).flip hp
  have hxp : IsProper B S hS x :=
    isProper_of_comp_of_isSeparated B S hS x fW
      (by rw [hcomp]; exact (isProper_algebraicSpaceStackMap_iff.{u, w} B S hS _ _ _).2 hpW)
      hfWsep
  exact ⟨Y', (W.preimage p).toFunctor, hY', hW'.1, (W.preimage p).ι, p, x, hW'.2, hp, hxp, ⟨e⟩, hV⟩

end AlgebraicGeometry.Stack.AlgebraicStacks

end
