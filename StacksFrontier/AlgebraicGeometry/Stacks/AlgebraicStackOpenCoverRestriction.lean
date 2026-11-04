module

public import StacksFrontier.AlgebraicGeometry.Stacks.AlgebraicStackBoundedCharts
public import StacksFrontier.AlgebraicGeometry.Stacks.ProductRepresentableBySpace
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertyBaseChange

/-!
# An algebraic stack from algebraic restrictions over an open covering of the base

Let `𝒳` be a stack in groupoids over the big fppf site of `S` with diagonal representable by
algebraic spaces, and let `{U i ⟶ S}` be an open covering. The restriction of `𝒳` to `U i` is the
2-fibre product `𝒳 ×_{(Sch/S)_fppf} (Sch/U i)_fppf` of Section 04X4, formed here with the
canonical 2-fibre product of categories fibred in groupoids (`restrictSquare`). If every
restriction is an algebraic stack with an atlas locally of finite type over `S`, and the
isomorphism classes of objects of `𝒳` over the spectra of fields of cardinality at most `size S`
are boundedly many, then `𝒳` is an algebraic stack. This is the paragraph "Choose an affine open
covering `S = ⋃ U_i` ... we set `W = ∐ W_i`" of the proof of Stacks 0DLN, for an arbitrary stack.

## Main definitions

* `AlgebraicGeometry.Stack.toTopOver`: the 1-morphism `𝒳 ⟶ (Sch/S)_fppf`.
* `AlgebraicGeometry.Stack.restrictSquare`: the 2-fibre product square of
  `𝒳 ⟶ (Sch/S)_fppf ⟵ (Sch/U)_fppf`.

## Main results

* `AlgebraicGeometry.Stack.isRelativelySmooth_restrictSquare_fst`: for `U ⟶ S` an open immersion
  the projection of the restriction to `𝒳` is smooth (base change of an open immersion,
  Stacks 045C).
* `AlgebraicGeometry.Stack.exists_restrictSquare_obj`: an object of `𝒳` whose points lie over `U`
  comes from the restriction.
* `AlgebraicGeometry.Stack.isAlgebraicStack_of_restrictSquare_openCover`: the assembly, through
  `AlgebraicGeometry.Stack.isAlgebraicStack_of_boundedCharts`.

## Implementation notes

`(Sch/S)_fppf` is the category represented by the final object `S/S` of the site,
`schemeFibredCategory B S hS (Over.mk (𝟙 _))`, so that the open immersion `(Sch/U) ⟶ (Sch/S)` is
the 1-morphism of a morphism of the site and its smoothness is Stacks 03ZF for that morphism.

## References

* [Stacks Project, Tag 045C](https://stacks.math.columbia.edu/tag/045C)
* [Stacks Project, Tag 04X4](https://stacks.math.columbia.edu/tag/04X4)
* [Stacks Project, Tag 0DLN](https://stacks.math.columbia.edu/tag/0DLN)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The final object `S/S` of the big fppf site of `S`. -/
abbrev topOver : BigFppfOver B S hS := Over.mk (𝟙 (B.obj hS))

/-- The 1-morphism `𝒳 ⟶ (Sch/S)_fppf` of a category fibred in groupoids over the big fppf site
of `S` to the stack represented by the final object `S/S`: an object over `T` goes to `T/S`. -/
def toTopOver (𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)) :
    𝒳 ⟶ schemeFibredCategory B S hS (topOver B S hS) :=
  Bicategory.InducedBicategory.mkHom
    { toFunctor := 𝒳.val.p ⋙ Over.iteratedSliceBackward (topOver B S hS)
      w := by
        change (𝒳.val.p ⋙ Over.iteratedSliceBackward (topOver B S hS)) ⋙
          Over.forget (topOver B S hS) = 𝒳.val.p
        rw [Functor.assoc, Over.iteratedSliceBackward_forget_id, Functor.comp_id] }

/-- The structure morphism of an object of the big fppf site of `S`, as a morphism to `S/S`. -/
def homTopOver (U : BigFppfOver B S hS) : U ⟶ topOver B S hS :=
  Over.homMk U.hom (by simp)

/-- **The restriction `𝒳 ×_{(Sch/S)_fppf} (Sch/U)_fppf` of `𝒳` to a scheme `U` over `S`**, as
the canonical 2-fibre product square of the cospan `𝒳 ⟶ (Sch/S)_fppf ⟵ (Sch/U)_fppf`. Its first
projection is the 1-morphism to `𝒳`. -/
def restrictSquare (𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS))
    (U : BigFppfOver B S hS) :=
  CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} (toTopOver B S hS 𝒳)
    (schemeFibredCategoryMap B S hS (homTopOver B S hS U))

/-- **The restriction of `𝒳` to an open of `S` maps to `𝒳` by a smooth 1-morphism**: it is the
base change of the open immersion `(Sch/U)_fppf ⟶ (Sch/S)_fppf` (Stacks 045C). -/
theorem isRelativelySmooth_restrictSquare_fst
    (𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS))
    (U : BigFppfOver B S hS) (hU : IsOpenImmersion (B.inclusion.map U.hom)) :
    IsRelativelySmooth B S hS (restrictSquare B S hS 𝒳 U).fst := by
  let j := schemeFibredCategoryMap B S hS (homTopOver B S hS U)
  have hj := isRepresentableByAlgebraicSpaces_schemeFibredCategoryMap B S hS
    (homTopOver B S hS U)
  have hPj : HasRelativeProperty.{u, u, u + 1, u} B S hS (Space.smoothMorphismProperty B S hS)
      j hj := by
    refine hasRelativeProperty_schemeFibredCategoryMap B S hS
      (Space.smoothMorphismProperty B S hS) _ ?_
    apply Space.isSmooth_yoneda_map
    show Smooth (B.inclusion.map U.hom)
    infer_instance
  exact ⟨_, hasRelativeProperty_baseChange.{u, u, u} B S hS
    (Space.smoothMorphismProperty B S hS) _ _ _ j (toTopOver B S hS 𝒳)
    (restrictSquare B S hS 𝒳 U)
    (CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1} _ _)
    hj hPj⟩

/-- **A field-valued object of `𝒳` whose point lies in an open `U` of `S` comes from the
restriction of `𝒳` to `U`.** -/
theorem exists_restrictSquare_obj
    (𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS))
    (U : BigFppfOver B S hS) [IsOpenImmersion (B.inclusion.map U.hom)] (y : 𝒳.val.obj)
    (hmem : ∀ v, B.inclusion.map (𝒳.val.p.obj y).hom v ∈
      Set.range (B.inclusion.map U.hom)) :
    ∃ d : (restrictSquare B S hS 𝒳 U).pt.val.obj,
      (restrictSquare B S hS 𝒳 U).pt.val.p.obj d = 𝒳.val.p.obj y ∧
        (CatFiberedInGroupoids.homFunctor (restrictSquare B S hS 𝒳 U).fst).obj d = y := by
  let V := 𝒳.val.p.obj y
  have hrange : Set.range (B.inclusion.map V.hom) ⊆ Set.range (B.inclusion.map U.hom) :=
    Set.range_subset_iff.2 hmem
  let ℓ := IsOpenImmersion.lift (B.inclusion.map U.hom) (B.inclusion.map V.hom) hrange
  have hℓ : ℓ ≫ B.inclusion.map U.hom = B.inclusion.map V.hom :=
    IsOpenImmersion.lift_fac _ _ hrange
  let ℓ' : V ⟶ U := Over.homMk (ObjectProperty.homMk ℓ) (ObjectProperty.hom_ext _ hℓ)
  have hhom : ((toTopOver B S hS 𝒳).hom.toFunctor.obj y).hom =
      ((Over.map (homTopOver B S hS U)).obj (Over.mk ℓ')).hom :=
    Over.OverMorphism.ext (Over.w ℓ').symm
  let iso : (toTopOver B S hS 𝒳).hom.toFunctor.obj y ≅
      (Over.map (homTopOver B S hS U)).obj (Over.mk ℓ') :=
    Over.isoMk (Iso.refl _) ((Category.id_comp _).trans hhom.symm)
  exact ⟨⟨V, y, Over.mk ℓ', rfl, rfl, iso, IsHomLift.map (Over.forget (topOver B S hS)) iso.hom⟩,
    rfl, rfl⟩

/-- **Stacks 0DLN, the reduction to an affine base, for an arbitrary stack.** Let `𝒳` be a stack
in groupoids over the big fppf site of `S` with diagonal representable by algebraic spaces, and
let `U i ⟶ S` be open immersions covering `S`. Suppose each restriction
`𝒳 ×_{(Sch/S)_fppf} (Sch/U i)_fppf` is an algebraic stack with an atlas from a scheme locally of
finite type over `S` (equivalently over `U i`, which is open in `S`), and that the isomorphism
classes of objects of `𝒳` over the spectra of fields of cardinality at most `size S` are bounded
by a cardinal below the cutoff of the site. Then `𝒳` is an algebraic stack.

The atlases followed by the projections to `𝒳` are smooth, the projections being base changes of
open immersions, and they are jointly surjective on field objects because a field-valued object
lies over a point of `S`, which lies in some `U i`; so
`AlgebraicGeometry.Stack.isAlgebraicStack_of_boundedCharts` applies. -/
theorem isAlgebraicStack_of_restrictSquare_openCover
    {𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
    (hstack : 𝒳.val.p.IsStack (BigFppfOver.topology B S hS))
    (hdiag : HasRepresentableDiagonal B S hS 𝒳)
    {ι : Type u} (U : ι → BigFppfOver B S hS)
    (hopen : ∀ i, IsOpenImmersion (B.inclusion.map (U i).hom))
    (hcover : ∀ s : S, ∃ i, s ∈ Set.range (B.inclusion.map (U i).hom))
    (hatlas : ∀ i, ∃ (W : BigFppfOver B S hS)
      (c : schemeFibredCategory B S hS W ⟶ (restrictSquare B S hS 𝒳 (U i)).pt),
      IsRelativelySmooth B S hS c ∧
      (∃ hc : IsRepresentableByAlgebraicSpaces B S hS c.hom,
        HasRelativeProperty.{u, u, u + 1, u} B S hS (Space.surjectiveMorphismProperty B S hS)
          c hc) ∧
      LocallyOfFiniteType (B.inclusion.map W.hom))
    (hsize : ∃ κ : Cardinal.{u}, κ < B.cutoff ∧
      ∀ (V : BigFppfOver B S hS) (k : Type u) [Field k], V.left.1 = Spec (.of k) →
        Cardinal.mk k ≤ S.size →
        Cardinal.lift.{u, u + 1} (Cardinal.mk (Quotient (isIsomorphicSetoid (𝒳.val.p.Fiber V)))) ≤
          Cardinal.lift.{u + 1, u} κ) :
    IsAlgebraicStack.{u, w} B S hS 𝒳.val := by
  choose W c hsm hsu hlft using hatlas
  refine isAlgebraicStack_of_boundedCharts B S hS hstack hdiag W
    (fun i => c i ≫ (restrictSquare B S hS 𝒳 (U i)).fst)
    (fun i => isRelativelySmooth_comp B S hS _ _ (hsm i)
      (isRelativelySmooth_restrictSquare_fst B S hS 𝒳 (U i) (hopen i))) hlft ?_ hsize
  intro V0 hV0 y hy
  subst hy
  obtain ⟨K, hK, ⟨eV⟩⟩ := id hV0
  let : Field K := hK
  let v := B.inclusion.map (𝒳.val.p.obj y).hom (eV.inv (IsLocalRing.closedPoint K))
  obtain ⟨i, hi⟩ := hcover v
  have := hopen i
  have hmem : ∀ z, B.inclusion.map (𝒳.val.p.obj y).hom z ∈
      Set.range (B.inclusion.map (U i).hom) := by
    intro z
    have hz : z = eV.inv (IsLocalRing.closedPoint K) := by
      have h1 : eV.inv (eV.hom z) = z := by
        rw [← Scheme.Hom.comp_apply, Iso.hom_inv_id]; rfl
      rw [← h1, Subsingleton.elim (eV.hom z) (IsLocalRing.closedPoint K)]
    rw [hz]
    exact hi
  obtain ⟨d, hd, hdy⟩ := exists_restrictSquare_obj B S hS 𝒳 (U i) y hmem
  subst hdy
  obtain ⟨hcrep, hcsu⟩ := hsu i
  have hsoo := (isSurjectiveOnObjects_iff_isRelativelySurjective.{u, u, u + 1, u} B S hS
    (c i) hcrep).mpr hcsu
  obtain ⟨V, hV, f, x, hx, β, hβ⟩ := hsoo _ hV0 d hd
  exact ⟨i, V, hV, f, x, hx, _,
    BasedFunctor.preserves_isHomLift (restrictSquare B S hS 𝒳 (U i)).fst.hom f β⟩

end AlgebraicGeometry.Stack

end
