module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.FibreProduct
public import StacksFrontier.AlgebraicGeometry.Spaces.RestrictSmallerBase
public import StacksFrontier.AlgebraicGeometry.Stacks.DiagonalCriteria
public import StacksFrontier.AlgebraicGeometry.Stacks.DiagonalCriteriaProductsToDiagonal
public import StacksFrontier.AlgebraicGeometry.Stacks.PresheafFibredCategory
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentabilityPostcomp
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentabilityTransport
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentableStackInSetoids
public import StacksFrontier.AlgebraicGeometry.Stacks.SecondDiagonal
public import StacksFrontier.CategoryTheory.FiberedCategory.DiscreteTwoFibreProduct
public import StacksFrontier.CategoryTheory.FiberedCategory.SliceAsElements
public import StacksFrontier.CategoryTheory.TwoFibreProduct.OverFunctoriality

/-!
# A 1-morphism of categories represented by algebraic spaces (Stacks 02ZZ)

Let `S` be a scheme contained in a big fppf site `B`. A 1-morphism of categories fibred in
groupoids over the big fppf site of `S` whose source and target are both representable by
algebraic spaces over `S` is representable by algebraic spaces: this is **Stacks 02ZZ**, whose
proof in the source is omitted with the remark that it rests only on the existence of fibre
products in the category of algebraic spaces over `S` (Stacks 02X2).

The proof here makes that remark precise. Both source and target are transported to categories
of *elements* of presheaves, where a 2-fibre product is computed presheaf-theoretically: for a
1-morphism `θ : 𝒮_X ⟶ 𝒮_Y` of categories of elements and a scheme-valued point `y` of `𝒮_Y`
over a scheme `V` over `S`, the 2-fibre product `(Sch/V)_{fppf} ×_{𝒮_Y} 𝒮_X` is the category of
elements of the subpresheaf `{x | θ x = y}` of the restriction of `X` to the big fppf site of
`V` (`CategoryTheory.PresheafOfCategories.isEquivalence_toTwoFibreProduct`). That subpresheaf is
the fibre product of the restriction of `X` with the final presheaf over the restriction of `Y`
(`CategoryTheory.PresheafOfCategories.isPullback_fibrePresheaf`), the restrictions are algebraic
spaces over `V` by Stacks 03I5 (1) and the final presheaf is one by Stacks 025Z, so Stacks 04T9
makes the subpresheaf an algebraic space over `V`.

Two consequences for an arbitrary category fibred in groupoids `𝒳` representable by an algebraic
space are recorded, both needed by Stacks 03YS (2) — that the stack attached to an algebraic
space is Deligne-Mumford: `𝒳` satisfies condition (3) of Stacks 045G, hence also its condition
(1), so the diagonal of `𝒳` is representable by algebraic spaces.

## Main results

* `AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpaces_of_isRepresentableByAlgebraicSpace`:
  **Stacks 02ZZ**.
* `AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpaces_fibredCategory`: Stacks 02ZZ for
  categories of elements, which is where the content is.
* `AlgebraicGeometry.Stack.nonempty_equivalenceOver_fst_of_equivalence_source`: the first
  projections of two 2-fibre products whose second factors are identified by an equivalence over
  the site are equivalent over the site of the point.
* `AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpace_fibredCategory` and
  `AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpace_schemeFibredCategory`: **Stacks 04SV**
  for the stack of an algebraic space and for a slice of the site.
* `AlgebraicGeometry.Stack.isStackInGroupoids_fibredCategory`: the stack condition of
  Stacks 03YS (2).
* `AlgebraicGeometry.Stack.isRepresentableFromSchemes_of_isRepresentableByAlgebraicSpace`:
  condition (3) of Stacks 045G for a category representable by an algebraic space.
* `AlgebraicGeometry.Stack.hasRepresentableDiagonal_of_isRepresentableByAlgebraicSpace` and
  `AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpaces_diagonalBasedFunctor`: condition (1)
  of Stacks 045G for such a category, in its two spellings. This is the diagonal condition of
  Stacks 03YS (2).

## Implementation notes

The transport of Stacks 02ZW along an equivalence of the *source* is done through
`AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpaces_of_forall_nonempty_equivalenceOver_fst`
rather than through Stacks 0457: the target and the scheme-valued point do not move, so the
comparison is `CategoryTheory.TwoFibreProductOver.precomposeSnd`, which commutes with the first
projection on the nose, and `StacksRepresentableCFG.nonempty_equivalenceOver_of_isEquivalence`
turns it into an equivalence over the site. Going through
`AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpaces_iff_of_equivalenceOver_source` instead
elaborates but does not typecheck in the kernel's budget, because the 2-isomorphism it asks for
is `Iso.refl` at a spelling whose two sides are equal only after unfolding the slice
equivalence. The *target* is moved by Stacks 0457, which it genuinely needs, since changing the
target changes the family of scheme-valued points the predicate quantifies over.

Stacks 02ZZ is stated at free universes for the two categories, as the source states it. The
intermediate step is at `CategoryTheory.CatFiberedInGroupoids.{u, u, u + 1, u + 1}`, the
universes of a category of elements of a presheaf of `Type u` on the big fppf site: its objects
are pairs of an object of the site and a section, so they live in `Type (u + 1)`, and its
morphisms live over morphisms of the site.

## References

* [Stacks Project, Tag 02ZZ](https://stacks.math.columbia.edu/tag/02ZZ)
* [Stacks Project, Tag 04SV](https://stacks.math.columbia.edu/tag/04SV)
* [Stacks Project, Tag 045G](https://stacks.math.columbia.edu/tag/045G)
* [Stacks Project, Tag 03YS](https://stacks.math.columbia.edu/tag/03YS)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.PresheafOfCategories

namespace AlgebraicGeometry.Stack

universe u v w v₁ w₁ v₂ w₂ v₃ w₃

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 04SV for the stack of an algebraic space.** The category of elements of an algebraic
space over `S`, viewed as a category fibred in groupoids over the big fppf site of `S`, is
representable by that algebraic space: the comparison is the identity. -/
theorem isRepresentableByAlgebraicSpace_fibredCategory
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F) :
    IsRepresentableByAlgebraicSpace B S hS (fibredCategory B S hS F) :=
  ⟨F, hF, ⟨StacksRepresentableCFG.EquivalenceOver.refl _⟩⟩

/-- **Stacks 04SV for a slice of the site.** The slice of the big fppf site of `S` over a scheme
`U` over `S` is representable by the algebraic space `yoneda.obj U` of Stacks 025Z: the slice
*is* the category of elements of that representable presheaf
(`CategoryTheory.PresheafOfCategories.sliceElementsEquivalenceOver`). -/
theorem isRepresentableByAlgebraicSpace_schemeFibredCategory (U : BigFppfOver B S hS) :
    IsRepresentableByAlgebraicSpace B S hS (schemeFibredCategory B S hS U) :=
  ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U, ⟨sliceElementsEquivalenceOver U⟩⟩

/-- **The stack condition of Stacks 03YS (2), sieve-indexed.** The category of elements of an
algebraic space over `S` is a stack for the fppf topology in the sense of Stacks 026F: an
algebraic space is an fppf sheaf, so its category of elements is a stack in sets. -/
theorem isStack_fibredCategory
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F) :
    (fibredCategory B S hS F).val.p.IsStack (BigFppfOver.topology B S hS) :=
  isStack_of_isRepresentableByAlgebraicSpace B S hS _
    (isRepresentableByAlgebraicSpace_fibredCategory B S hS F hF)

/-- **The stack condition of Stacks 03YS (2).** The category of elements of an algebraic space
over `S` is a stack in groupoids for the fppf topology, at every descent universe: an algebraic
space is an fppf sheaf, so its category of elements is a stack in sets. -/
theorem isStackInGroupoids_fibredCategory
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F) :
    (fibredCategory B S hS F).val.p.IsStackInGroupoids.{w}
      (BigFppfOver.topology B S hS) :=
  isStackInGroupoids_of_isRepresentableByAlgebraicSpace B S hS _
    (isRepresentableByAlgebraicSpace_fibredCategory B S hS F hF)

/-- **Transport of a 2-fibre product along an equivalence of its second factor.** For a
1-morphism `a : 𝒳' ⟶ 𝒳` over the big fppf site of `S` whose underlying functor is an equivalence
of categories, and a 1-morphism `f : 𝒳 ⟶ 𝒴`, the first projections of
`(Sch/V)_{fppf} ×_{y, 𝒴, a ≫ f} 𝒳'` and of `(Sch/V)_{fppf} ×_{y, 𝒴, f} 𝒳` are equivalent over
the big fppf site of `V`, for every scheme-valued point `y` of `𝒴` over `V`.

The comparison is `CategoryTheory.TwoFibreProductOver.precomposeSnd`, which commutes with the
first projection on the nose; this is the cheap half of Stacks 0457, and it is what feeds the
pointwise transport of Stacks 02ZW in the source. -/
theorem nonempty_equivalenceOver_fst_of_equivalence_source
    {𝒳' : CatFiberedInGroupoids.{u, v₁, u + 1, w₁} (BigFppfOver B S hS)}
    {𝒳 : CatFiberedInGroupoids.{u, v₂, u + 1, w₂} (BigFppfOver B S hS)}
    {𝒴 : CatFiberedInGroupoids.{u, v₃, u + 1, w₃} (BigFppfOver B S hS)}
    (a : 𝒳'.val ⥤ᵇ 𝒳.val) [Functor.IsEquivalence a.toFunctor]
    (f : 𝒳.val ⥤ᵇ 𝒴.val) (V : BigFppfOver B S hS)
    (y : BigFppfOver B V.left.1 V.left.2 ⥤ 𝒴.val.obj)
    (hy : y ⋙ 𝒴.val.p = Over.map V.hom) :
    Nonempty (StacksRepresentableCFG.EquivalenceOver
      (TwoFibreProductOver.fst (Over.map V.hom) 𝒳'.val.p 𝒴.val.p y
        (BasedFunctor.comp a f).toFunctor)
      (TwoFibreProductOver.fst (Over.map V.hom) 𝒳.val.p 𝒴.val.p y f.toFunctor)) :=
  StacksRepresentableCFG.nonempty_equivalenceOver_of_isEquivalence
    (fst_isFiberedInGroupoids_overMap V.hom 𝒳'.val.p 𝒴.val.p y
      (BasedFunctor.comp a f).toFunctor 𝒳'.isFiberedInGroupoids 𝒴.isFiberedInGroupoids hy
      (BasedFunctor.comp a f).w)
    (fst_isFiberedInGroupoids_overMap V.hom 𝒳.val.p 𝒴.val.p y f.toFunctor
      𝒳.isFiberedInGroupoids 𝒴.isFiberedInGroupoids hy f.w)
    (TwoFibreProductOver.precomposeSnd y f.toFunctor a.toFunctor a.w)
    (TwoFibreProductOver.precomposeSnd_comp_fst y f.toFunctor a.toFunctor a.w)
    (TwoFibreProductOver.isEquivalence_precomposeSnd
      (overMap_isFiberedInGroupoids V.hom) 𝒳'.isFiberedInGroupoids
      𝒳.isFiberedInGroupoids a.w f.w)

/-- **Stacks 02ZZ for categories of elements**, which is where its content lies. A 1-morphism
over the big fppf site of `S` between the categories of elements of two algebraic spaces over
`S` is representable by algebraic spaces.

For a scheme-valued point `y` of the target over a scheme `V` over `S`, the 2-fibre product is
the category of elements of the subpresheaf `{x | f x = y}` of the restriction of the source to
the big fppf site of `V`, and that subpresheaf is the fibre product of the two restrictions over
the final presheaf, hence an algebraic space over `V` by Stacks 04T9. -/
theorem isRepresentableByAlgebraicSpaces_fibredCategory
    (X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (f : (fibredCategory B S hS X).val ⥤ᵇ (fibredCategory B S hS Y).val) :
    IsRepresentableByAlgebraicSpaces B S hS f := by
  intro U
  dsimp only
  intro y hy
  refine ⟨twoFibreProductPresheaf y hy f.toFunctor f.w, ?_, ?_⟩
  · have hT : IsTerminal (⊤_ (BigFppfOver B U.left.1 U.left.2)) := terminalIsTerminal
    have hY' := isAlgebraicSpace_relocalizeRestrict B U.left.1 S U.left.2 hS U.hom Y hY
    exact isAlgebraicSpace_of_isPullback
      (isAlgebraicSpace_relocalizeRestrict B U.left.1 S U.left.2 hS U.hom X hX)
      (isAlgebraicSpace_yoneda B U.left.1 U.left.2 _) hY'.isSheaf hY'.diagonal_representable
      (isPullback_fibrePresheaf _ _ _ hT)
  · refine Nonempty.map StacksRepresentableCFG.EquivalenceOver.symm ?_
    exact StacksRepresentableCFG.nonempty_equivalenceOver_of_isEquivalence
      (fibredCategory B U.left.1 U.left.2
        (twoFibreProductPresheaf y hy f.toFunctor f.w)).isFiberedInGroupoids
      (fst_isFiberedInGroupoids_overMap U.hom _ _ y f.toFunctor
        (fibredCategory B S hS X).isFiberedInGroupoids
        (fibredCategory B S hS Y).isFiberedInGroupoids hy f.w)
      (toTwoFibreProduct y hy f.toFunctor f.w)
      (toTwoFibreProduct_comp_fst y hy f.toFunctor f.w)
      (isEquivalence_toTwoFibreProduct y hy f.toFunctor f.w)

/-- **Stacks 02ZZ.** A 1-morphism of categories fibred in groupoids over the big fppf site of
`S` whose source and target are both representable by algebraic spaces over `S` is representable
by algebraic spaces.

Both source and target are transported to categories of elements, where
`AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpaces_fibredCategory` applies: the source by
`AlgebraicGeometry.Stack.nonempty_equivalenceOver_fst_of_equivalence_source`, the target by
Stacks 0457. -/
@[stacks 02ZZ]
theorem isRepresentableByAlgebraicSpaces_of_isRepresentableByAlgebraicSpace
    {𝒳 𝒴 : CatFiberedInGroupoids.{u, v, u + 1, w} (BigFppfOver B S hS)}
    (f : 𝒳 ⟶ 𝒴)
    (h𝒳 : IsRepresentableByAlgebraicSpace B S hS 𝒳)
    (h𝒴 : IsRepresentableByAlgebraicSpace B S hS 𝒴) :
    IsRepresentableByAlgebraicSpaces B S hS f.hom := by
  obtain ⟨X, hX, ⟨eX⟩⟩ := h𝒳
  obtain ⟨Y, hY, ⟨eY⟩⟩ := h𝒴
  have : Functor.IsEquivalence
      (⟨eX.inv.functor, eX.inv.w⟩ : (fibredCategory B S hS X).val ⥤ᵇ 𝒳.val).toFunctor :=
    eX.isEquivalence_inv_functor
  have : Functor.IsEquivalence
      (⟨eY.inv.functor, eY.inv.w⟩ : (fibredCategory B S hS Y).val ⥤ᵇ 𝒴.val).toFunctor :=
    eY.isEquivalence_inv_functor
  refine isRepresentableByAlgebraicSpaces_of_forall_nonempty_equivalenceOver_fst
    (f := BasedFunctor.comp ⟨eX.inv.functor, eX.inv.w⟩ f.hom) (f' := f.hom)
    (fun V y hy => (nonempty_equivalenceOver_fst_of_equivalence_source B S hS
      (𝒳' := fibredCategory B S hS X) ⟨eX.inv.functor, eX.inv.w⟩ f.hom V y hy).map
      StacksRepresentableCFG.EquivalenceOver.symm) ?_
  refine (isRepresentableByAlgebraicSpaces_iff_of_equivalence_target B S hS
    (𝒳 := fibredCategory B S hS X) (𝒴 := 𝒴) (𝒴' := fibredCategory B S hS Y)
    (BasedFunctor.comp ⟨eX.inv.functor, eX.inv.w⟩ f.hom)
    (BasedFunctor.comp (BasedFunctor.comp ⟨eX.inv.functor, eX.inv.w⟩ f.hom)
      ⟨eY.hom.functor, eY.hom.w⟩)
    ⟨eY.inv.functor, eY.inv.w⟩ (BasedNatIso.mkNatIso ?_ ?_)).2 ?_
  · exact Functor.isoWhiskerLeft (eX.inv.functor ⋙ f.hom.toFunctor) eY.unitIso
  · intro x
    have h := eY.isHomLift_unitIso_hom_app ((eX.inv.functor ⋙ f.hom.toFunctor).obj x)
    have hx : 𝒴.val.p.obj ((eX.inv.functor ⋙ f.hom.toFunctor).obj x)
        = (fibredCategory B S hS X).val.p.obj x :=
      congrArg (fun k : (fibredCategory B S hS X).val.obj ⥤ BigFppfOver B S hS => k.obj x)
        (BasedFunctor.comp
          (⟨eX.inv.functor, eX.inv.w⟩ : (fibredCategory B S hS X).val ⥤ᵇ 𝒳.val) f.hom).w
    rw [hx] at h
    exact h
  · exact isRepresentableByAlgebraicSpaces_fibredCategory B S hS X Y hX hY _

/-- **Condition (3) of Stacks 045G for a category representable by an algebraic space.** Every
1-morphism to `𝒳` from the category represented by a scheme over `S` is representable by
algebraic spaces, as soon as `𝒳` is representable by an algebraic space over `S`.

Both source and target are then representable by algebraic spaces, so this is Stacks 02ZZ. -/
theorem isRepresentableFromSchemes_of_isRepresentableByAlgebraicSpace
    (𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS))
    (h𝒳 : IsRepresentableByAlgebraicSpace B S hS 𝒳) :
    IsRepresentableFromSchemes B S hS 𝒳 := fun U x =>
  isRepresentableByAlgebraicSpaces_of_isRepresentableByAlgebraicSpace B S hS
    (Bicategory.InducedBicategory.mkHom x)
    (isRepresentableByAlgebraicSpace_schemeFibredCategory B S hS U) h𝒳

/-- **Condition (1) of Stacks 045G for a category representable by an algebraic space.** The
diagonal of a category fibred in groupoids over the big fppf site of `S` which is representable
by an algebraic space over `S` is representable by algebraic spaces.

This is condition (3), which Stacks 02ZZ supplies, carried to condition (2) and then to
condition (1) along the equivalences of Stacks 045G. It is the diagonal condition of
Stacks 03YS (2). -/
theorem hasRepresentableDiagonal_of_isRepresentableByAlgebraicSpace
    (𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS))
    (h𝒳 : IsRepresentableByAlgebraicSpace B S hS 𝒳) :
    HasRepresentableDiagonal B S hS 𝒳 :=
  (hasRepresentableDiagonal_iff_isAlgebraicSpaceIsomPresheaf B S hS 𝒳).2
    (isAlgebraicSpaceIsomPresheaf_of_isRepresentableFromSchemes B S hS 𝒳
      (isRepresentableFromSchemes_of_isRepresentableByAlgebraicSpace B S hS 𝒳 h𝒳))

/-- `AlgebraicGeometry.Stack.hasRepresentableDiagonal_of_isRepresentableByAlgebraicSpace` at the
spelling `AlgebraicGeometry.Stack.diagonalBasedFunctor`, which is the one the fourth clause of
`AlgebraicGeometry.Stack.IsAlgebraicStack` and Stacks 03YS (2) are stated with. -/
theorem isRepresentableByAlgebraicSpaces_diagonalBasedFunctor
    (𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS))
    (h𝒳 : IsRepresentableByAlgebraicSpace B S hS 𝒳) :
    IsRepresentableByAlgebraicSpaces B S hS (diagonalBasedFunctor B S hS 𝒳) :=
  (hasRepresentableDiagonal_iff B S hS 𝒳).1
    (hasRepresentableDiagonal_of_isRepresentableByAlgebraicSpace B S hS 𝒳 h𝒳)

end AlgebraicGeometry.Stack

end
