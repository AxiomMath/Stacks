module

public import StacksFrontier.CategoryTheory.Sites.Stack.SlicePointIsomPresheaf

/-!
# Two points of a category fibred in groupoids with the same value are isomorphic

Let `p : 𝒵 ⥤ 𝒟/X` be fibred in groupoids and let `U` be an object of `𝒟/X`. A *point of `p` with
values in `U`* is a functor `W : 𝒟/U.left ⥤ 𝒵` with `W ⋙ p = Over.map U.hom`; the value of such a
point at the terminal object `1_{U.left}` of `𝒟/U.left` is an object of the fibre of `p` over `U`
(`CategoryTheory.Functor.sliceValue`). This file extends a morphism of the values at the terminal
object to a 2-morphism of the points themselves, and records that it is an isomorphism.

This is the 2-Yoneda lemma (Stacks 004B) in the form the independence-of-choice statements of
Stacks 06CK need: the scheme-valued point of `𝒴` through which an object of the relative finite
Hilbert category is read is not canonical, and two choices of it carry the *same* object of the
fibre, so they are isomorphic as points, compatibly with the identifications of that object.

`CategoryTheory.Functor.sliceValueNatIso` says the same thing with the second point replaced by
the chosen-pullback point of the value; what is added here is the extension of a *given* morphism
of values, together with the factorisation characterising it, which is what a computation with the
2-morphism needs.

## Main definitions

* `CategoryTheory.Functor.slicePointApp`: the component at an object of `𝒟/U.left` of the
  2-morphism extending a morphism of the values at the terminal object.
* `CategoryTheory.Functor.slicePointHom`: those components as a natural transformation.
* `CategoryTheory.Functor.slicePointIso`: the natural transformation attached to an isomorphism
  of the values, as a natural isomorphism.

## Main results

* `CategoryTheory.Functor.slicePointApp_fac`: the factorisation characterising the components —
  the component at `a` followed by the image of the canonical arrow `a ⟶ 1_{U.left}` under the
  second point is the image of that arrow under the first point followed by the given morphism.
* `CategoryTheory.Functor.isHomLift_slicePointApp`: every component is vertical.
* `CategoryTheory.Functor.slicePointIso_hom_app`: the components of the natural isomorphism are
  the ones constructed.

## Implementation notes

The construction is the universal property of the strongly cartesian arrow `W₂(a ⟶ 1_{U.left})`,
which is strongly cartesian because in a category fibred in groupoids every lift is
(`CategoryTheory.Functor.IsFiberedInGroupoids.isStronglyCartesian_homLift`), applied to the
composite `W₁(a ⟶ 1_{U.left}) ≫ m`. Naturality is the uniqueness half of the same universal
property, and invertibility of the components is the fact that a vertical morphism of a category
fibred in groupoids is an isomorphism.

The same construction for a point on the slice `(𝒟/X)/U` rather than on `𝒟/U.left` is
`CategoryTheory.Functor.TwoYoneda.homOfUnitHom`. It is not specialised to the present setting,
because `CategoryTheory.Over.map U.hom` is `CategoryTheory.Over.forget U` only after the
iterated-slice identification and inserting that identification costs more than carrying out the
universal property again — the same trade-off as in
`StacksFrontier.CategoryTheory.TwoFibreProductOverRelocalize`.

## References

* [Stacks Project, Tag 004B](https://stacks.math.columbia.edu/tag/004B)
* [Stacks Project, Tag 06CK](https://stacks.math.columbia.edu/tag/06CK)
-/

@[expose] public section

open CategoryTheory

universe v₁ u₁ v₂ u₂

namespace CategoryTheory.Functor

variable {D : Type u₁} [Category.{v₁} D] {X : D} {Z : Type u₂} [Category.{v₂} Z]
  (p : Z ⥤ Over X) (U : Over X) (W₁ W₂ : Over U.left ⥤ Z)

section Comparison

variable (hp : p.IsFiberedInGroupoids) (h₁ : W₁ ⋙ p = Over.map U.hom)
  (h₂ : W₂ ⋙ p = Over.map U.hom)
  (m : W₁.obj (Over.mk (𝟙 U.left)) ⟶ W₂.obj (Over.mk (𝟙 U.left)))
  (hm : p.IsHomLift (𝟙 U) m)

/-- The image under a point of the canonical arrow `a ⟶ 1_{U.left}` is strongly cartesian over
the structure morphism of `a`: in a category fibred in groupoids every lift is. -/
theorem isStronglyCartesian_map_toMkId
    (p : Z ⥤ Over X) (U : Over X) (W : Over U.left ⥤ Z) (hp : p.IsFiberedInGroupoids)
    (hW : W ⋙ p = Over.map U.hom) (a : Over U.left) :
    p.IsStronglyCartesian (structHom U a) (W.map (toMkId U a)) :=
  have := isHomLift_map_toMkId p U W hW a
  hp.isStronglyCartesian_homLift _ _

/-- The image under the first point of the canonical arrow `a ⟶ 1_{U.left}`, followed by the given
morphism of the values at the terminal object, lies over the structure morphism of `a`. -/
theorem isHomLift_map_toMkId_comp
    (p : Z ⥤ Over X) (U : Over X) (W₁ W₂ : Over U.left ⥤ Z)
    (h₁ : W₁ ⋙ p = Over.map U.hom)
    (m : W₁.obj (Over.mk (𝟙 U.left)) ⟶ W₂.obj (Over.mk (𝟙 U.left)))
    (hm : p.IsHomLift (𝟙 U) m) (a : Over U.left) :
    p.IsHomLift (structHom U a) (W₁.map (toMkId U a) ≫ m) :=
  have := isHomLift_map_toMkId p U W₁ h₁ a
  have := hm
  IsHomLift.comp_lift_id_right' p (structHom U a) (W₁.map (toMkId U a)) U m

/-- The component at `a` of the 2-morphism extending a morphism `m` of the values at the terminal
object: the unique morphism over the identity whose composite with the image under `W₂` of the
canonical arrow `a ⟶ 1_{U.left}` is the image under `W₁` of that arrow followed by `m`. -/
noncomputable def slicePointApp (a : Over U.left) : W₁.obj a ⟶ W₂.obj a :=
  have := isStronglyCartesian_map_toMkId p U W₂ hp h₂ a
  have := isHomLift_map_toMkId_comp p U W₁ W₂ h₁ m hm a
  IsStronglyCartesian.map p (structHom U a) (W₂.map (toMkId U a))
    (Category.id_comp (structHom U a)).symm (W₁.map (toMkId U a) ≫ m)

/-- The factorisation characterising `CategoryTheory.Functor.slicePointApp`. -/
theorem slicePointApp_fac (a : Over U.left) :
    slicePointApp p U W₁ W₂ hp h₁ h₂ m hm a ≫ W₂.map (toMkId U a) =
      W₁.map (toMkId U a) ≫ m :=
  have := isStronglyCartesian_map_toMkId p U W₂ hp h₂ a
  have := isHomLift_map_toMkId_comp p U W₁ W₂ h₁ m hm a
  IsStronglyCartesian.fac p (structHom U a) (W₂.map (toMkId U a))
    (Category.id_comp (structHom U a)).symm (W₁.map (toMkId U a) ≫ m)

/-- Every component of the 2-morphism is vertical. -/
theorem isHomLift_slicePointApp (a : Over U.left) :
    p.IsHomLift (𝟙 ((Over.map U.hom).obj a)) (slicePointApp p U W₁ W₂ hp h₁ h₂ m hm a) :=
  have := isStronglyCartesian_map_toMkId p U W₂ hp h₂ a
  have := isHomLift_map_toMkId_comp p U W₁ W₂ h₁ m hm a
  IsStronglyCartesian.map_isHomLift p (structHom U a) (W₂.map (toMkId U a))
    (Category.id_comp (structHom U a)).symm (W₁.map (toMkId U a) ≫ m)

/-- The components assemble into a natural transformation of the two points. Naturality is the
uniqueness half of the universal property defining the components: both sides lie over the image
of the given arrow and have the same composite with the strongly cartesian arrow. -/
noncomputable def slicePointHom : W₁ ⟶ W₂ where
  app := slicePointApp p U W₁ W₂ hp h₁ h₂ m hm
  naturality a' a k := by
    have := isStronglyCartesian_map_toMkId p U W₂ hp h₂ a
    have hl : p.IsHomLift ((Over.map U.hom).map k)
        (W₁.map k ≫ slicePointApp p U W₁ W₂ hp h₁ h₂ m hm a) := by
      have hk : p.IsHomLift ((Over.map U.hom).map k) (W₁.map k) :=
        TwoFibreProductOver.DiagonalFibre.VertHom.isHomLift_map h₁ k
      have hv := isHomLift_slicePointApp p U W₁ W₂ hp h₁ h₂ m hm a
      exact IsHomLift.comp_lift_id_right p ((Over.map U.hom).map k) (W₁.map k) _
    have hr : p.IsHomLift ((Over.map U.hom).map k)
        (slicePointApp p U W₁ W₂ hp h₁ h₂ m hm a' ≫ W₂.map k) := by
      have hk : p.IsHomLift ((Over.map U.hom).map k) (W₂.map k) :=
        TwoFibreProductOver.DiagonalFibre.VertHom.isHomLift_map h₂ k
      have hv := isHomLift_slicePointApp p U W₁ W₂ hp h₁ h₂ m hm a'
      exact IsHomLift.comp_lift_id_left p ((Over.map U.hom).map k) (W₂.map k) _
    refine IsStronglyCartesian.ext p (structHom U a) (W₂.map (toMkId U a))
      ((Over.map U.hom).map k) ?_
    rw [Category.assoc, slicePointApp_fac, Category.assoc, ← W₂.map_comp, comp_toMkId,
      slicePointApp_fac, ← Category.assoc, ← W₁.map_comp, comp_toMkId]

/-- The components of `CategoryTheory.Functor.slicePointHom` are the morphisms
`CategoryTheory.Functor.slicePointApp`. -/
@[simp]
theorem slicePointHom_app (a : Over U.left) :
    (slicePointHom p U W₁ W₂ hp h₁ h₂ m hm).app a =
      slicePointApp p U W₁ W₂ hp h₁ h₂ m hm a := rfl

/-- Every component of the 2-morphism is an isomorphism, being vertical: it is strongly
cartesian over an identity, hence invertible. -/
theorem isIso_slicePointApp (a : Over U.left) :
    IsIso (slicePointApp p U W₁ W₂ hp h₁ h₂ m hm a) :=
  have := isHomLift_slicePointApp p U W₁ W₂ hp h₁ h₂ m hm a
  have := hp.isStronglyCartesian_homLift (𝟙 ((Over.map U.hom).obj a))
    (slicePointApp p U W₁ W₂ hp h₁ h₂ m hm a)
  IsStronglyCartesian.isIso_of_base_isIso p (𝟙 ((Over.map U.hom).obj a)) _

/-- **Two points of a category fibred in groupoids with isomorphic values at the terminal object
are isomorphic.** The natural transformation extending a morphism of the values is an
isomorphism: its components are vertical, and a vertical morphism of a category fibred in
groupoids is invertible. -/
noncomputable def slicePointIso : W₁ ≅ W₂ :=
  NatIso.ofComponents
    (fun a => @asIso _ _ _ _ (slicePointApp p U W₁ W₂ hp h₁ h₂ m hm a)
      (isIso_slicePointApp p U W₁ W₂ hp h₁ h₂ m hm a))
    (fun k => (slicePointHom p U W₁ W₂ hp h₁ h₂ m hm).naturality k)

/-- The components of `CategoryTheory.Functor.slicePointIso` are the morphisms
`CategoryTheory.Functor.slicePointApp`. -/
@[simp]
theorem slicePointIso_hom_app (a : Over U.left) :
    (slicePointIso p U W₁ W₂ hp h₁ h₂ m hm).hom.app a =
      slicePointApp p U W₁ W₂ hp h₁ h₂ m hm a := rfl

end Comparison

end CategoryTheory.Functor

end
