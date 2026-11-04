module

public import StacksFrontier.AlgebraicGeometry.Stacks.Algebraic.RepresentableBySpace.Characterization
public import StacksFrontier.AlgebraicGeometry.Stacks.SchemePointProductPasting
public import Mathlib.CategoryTheory.ShrinkYoneda

/-!
# A `Type u` model for the presheaf of isomorphism classes

For a fibred category `p : 𝒮 ⥤ 𝒞` whose presheaf of isomorphism classes
`CategoryTheory.Functor.isoClassPresheaf` is `w`-small, we construct a `Type w`-valued presheaf
in natural bijection with it, and use it to state the characterization of categories fibred in
groupoids over the big fppf site that are representable by an algebraic space as a condition on
a `Type u`-valued presheaf.

## Main definitions

* `CategoryTheory.Functor.isoClassPresheafModel`: the `Type w`-valued presheaf obtained by
  shrinking the presheaf of isomorphism classes, with
  `CategoryTheory.Functor.isoClassPresheafModelEquiv` the natural bijection to it.

## Main results

* `CategoryTheory.Functor.small_isoClassPresheaf_obj_iff_essentiallySmall`: the value of the
  presheaf of isomorphism classes at `U` is `w`-small exactly when the fibre over `U` is
  `w`-essentially small.
* `AlgebraicGeometry.isAlgebraicSpaceIsoClassPresheaf_iff_isAlgebraicSpace_isoClassPresheafModel`:
  `AlgebraicGeometry.IsAlgebraicSpaceIsoClassPresheaf` holds exactly when the `Type u` model of
  the presheaf of isomorphism classes is an algebraic space.
* `AlgebraicGeometry.isRepresentableByAlgebraicSpace_iff_isAlgebraicSpace_isoClassPresheafModel`:
  a category fibred in groupoids is representable by an algebraic space exactly when it is
  fibred in setoids and the `Type u` model of its presheaf of isomorphism classes is an
  algebraic space.
* `AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpace_twoFibreProduct_iff`: the previous
  result for the 2-fibre product of two scheme-valued points.

## References

* [Stacks Project, Tag 02ZX](https://stacks.math.columbia.edu/tag/02ZX)
* [Stacks Project, Tag 045G](https://stacks.math.columbia.edu/tag/045G)
-/

@[expose] public section

open CategoryTheory Opposite

namespace CategoryTheory.Functor

universe w v₁ v₂ u₁ u₂

variable {𝒞 : Type u₁} [Category.{v₁} 𝒞] {𝒮 : Type u₂} [Category.{v₂} 𝒮]

section Skeleton

variable (p : 𝒮 ⥤ 𝒞) [p.IsFibered]

/-- The value of the presheaf of isomorphism classes at `U` is the skeleton of the fibre over
`U`. -/
theorem isoClassPresheaf_obj_eq_skeleton (U : 𝒞) :
    p.isoClassPresheaf.obj (op U) = Skeleton (p.Fiber U) :=
  rfl

/-- If the fibre over `U` is thin, the value of the presheaf of isomorphism classes at `U` is
`w`-small exactly when the fibre over `U` is `w`-essentially small. -/
theorem small_isoClassPresheaf_obj_iff_essentiallySmall (U : 𝒞)
    (hthin : Quiver.IsThin (p.Fiber U)) :
    Small.{w} (p.isoClassPresheaf.obj (op U)) ↔ EssentiallySmall.{w} (p.Fiber U) := by
  have := hthin
  exact essentiallySmall_iff_of_thin.symm

/-- A presheaf of isomorphism classes that is objectwise in bijection with a `Type w`-valued
presheaf is `w`-small. -/
theorem small_isoClassPresheaf_of_equiv {F : 𝒞ᵒᵖ ⥤ Type w}
    (e : ∀ U, p.isoClassPresheaf.obj U ≃ F.obj U) :
    FunctorToTypes.Small.{w} p.isoClassPresheaf :=
  fun U => ⟨F.obj U, ⟨e U⟩⟩

end Skeleton

section Model

variable (p : 𝒮 ⥤ 𝒞) [p.IsFibered] [FunctorToTypes.Small.{w} p.isoClassPresheaf]

/-- The `Type w` model of the presheaf of isomorphism classes, for a fibred category whose
presheaf of isomorphism classes is `w`-small. -/
noncomputable def isoClassPresheafModel : 𝒞ᵒᵖ ⥤ Type w :=
  FunctorToTypes.shrink.{w} p.isoClassPresheaf

/-- The bijection of the presheaf of isomorphism classes with its `Type w` model. -/
noncomputable def isoClassPresheafModelEquiv (U : 𝒞ᵒᵖ) :
    p.isoClassPresheaf.obj U ≃ (isoClassPresheafModel.{w} p).obj U :=
  equivShrink _

/-- `CategoryTheory.Functor.isoClassPresheafModelEquiv` is natural. -/
theorem isoClassPresheafModelEquiv_naturality {U V : 𝒞ᵒᵖ} (f : U ⟶ V)
    (x : p.isoClassPresheaf.obj U) :
    isoClassPresheafModelEquiv.{w} p V (p.isoClassPresheaf.map f x) =
      (isoClassPresheafModel.{w} p).map f (isoClassPresheafModelEquiv.{w} p U x) := by
  show (equivShrink _) ((ConcreteCategory.hom (p.isoClassPresheaf.map f)) x)
      = (equivShrink _) ((ConcreteCategory.hom (p.isoClassPresheaf.map f))
          ((equivShrink _).symm ((equivShrink _) x)))
  rw [Equiv.symm_apply_apply]

/-- A `Type w`-valued presheaf in natural bijection with the presheaf of isomorphism classes is
isomorphic to the model. -/
noncomputable def isoClassPresheafModelIso {F : 𝒞ᵒᵖ ⥤ Type w}
    (e : ∀ U, p.isoClassPresheaf.obj U ≃ F.obj U)
    (hnat : ∀ ⦃U V⦄ (f : U ⟶ V) (x : p.isoClassPresheaf.obj U),
      e V (p.isoClassPresheaf.map f x) = F.map f (e U x)) :
    isoClassPresheafModel.{w} p ≅ F :=
  NatIso.ofComponents
    (fun U => Equiv.toIso ((isoClassPresheafModelEquiv.{w} p U).symm.trans (e U)))
    fun f ↦ by
      ext z
      obtain ⟨x, rfl⟩ := (isoClassPresheafModelEquiv.{w} p _).surjective z
      simp [← isoClassPresheafModelEquiv_naturality, hnat]

end Model

end CategoryTheory.Functor

namespace AlgebraicGeometry

universe u v w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (𝒳 : CatFiberedInGroupoids.{u, v, u + 1, w} (BigFppfOver B S hS))

/-- If `AlgebraicGeometry.IsAlgebraicSpaceIsoClassPresheaf` holds for `𝒳`, then the presheaf of
isomorphism classes of `𝒳` is `u`-small. -/
public theorem small_isoClassPresheaf_of_isAlgebraicSpaceIsoClassPresheaf
    [𝒳.val.p.IsFibered] (h : IsAlgebraicSpaceIsoClassPresheaf B S hS 𝒳) :
    CategoryTheory.FunctorToTypes.Small.{u} 𝒳.val.p.isoClassPresheaf :=
  let ⟨_, _, e, _⟩ := h
  CategoryTheory.Functor.small_isoClassPresheaf_of_equiv 𝒳.val.p e

/-- `AlgebraicGeometry.IsAlgebraicSpaceIsoClassPresheaf` holds for `𝒳` exactly when the
`Type u` model of its presheaf of isomorphism classes is an algebraic space. -/
public theorem isAlgebraicSpaceIsoClassPresheaf_iff_isAlgebraicSpace_isoClassPresheafModel
    [𝒳.val.p.IsFibered]
    [CategoryTheory.FunctorToTypes.Small.{u} 𝒳.val.p.isoClassPresheaf] :
    IsAlgebraicSpaceIsoClassPresheaf B S hS 𝒳 ↔
      IsAlgebraicSpace B S hS
        (CategoryTheory.Functor.isoClassPresheafModel.{u} 𝒳.val.p) :=
  ⟨fun ⟨_, hF, e, hnat⟩ ↦ Space.isAlgebraicSpace_of_iso B S hS
      (CategoryTheory.Functor.isoClassPresheafModelIso.{u} 𝒳.val.p e hnat).symm hF,
    fun h ↦ ⟨_, h, CategoryTheory.Functor.isoClassPresheafModelEquiv.{u} 𝒳.val.p,
      fun _ _ f x ↦ CategoryTheory.Functor.isoClassPresheafModelEquiv_naturality.{u} 𝒳.val.p f x⟩⟩

/-- A category fibred in groupoids over the big fppf site whose presheaf of isomorphism classes
is `u`-small is representable by an algebraic space exactly when its fibres are setoids and the
`Type u` model of that presheaf is an algebraic space. -/
public theorem isRepresentableByAlgebraicSpace_iff_isAlgebraicSpace_isoClassPresheafModel
    [𝒳.val.p.IsFibered]
    [CategoryTheory.FunctorToTypes.Small.{u} 𝒳.val.p.isoClassPresheaf] :
    IsRepresentableByAlgebraicSpace B S hS 𝒳 ↔
      (𝒳.val.p.IsFiberedInSetoids ∧
        IsAlgebraicSpace B S hS
          (CategoryTheory.Functor.isoClassPresheafModel.{u} 𝒳.val.p)) :=
  (isRepresentableByAlgebraicSpace_iff B S hS 𝒳).trans
    (and_congr_right fun _ =>
      isAlgebraicSpaceIsoClassPresheaf_iff_isAlgebraicSpace_isoClassPresheafModel B S hS 𝒳)

section EquivalenceOver

variable {D : Type v} [Category.{w} D] (p : D ⥤ BigFppfOver B S hS)

/-- The equivalence over the base of a category fibred in setoids with the category of elements
of the `Type u` model of its presheaf of isomorphism classes. -/
public noncomputable def isoClassEquivalenceOverModel
    [p.IsFiberedInSetoids]
    [CategoryTheory.FunctorToTypes.Small.{u} p.isoClassPresheaf] :
    StacksRepresentableCFG.EquivalenceOver p
      (presheafOfCategories
        (CategoryTheory.Functor.isoClassPresheafModel.{u} p ⋙ typeToCat)).p :=
  equivalenceOver_elements_of_setoids p (CategoryTheory.Functor.isoClassPresheafModel.{u} p)
    (CategoryTheory.Functor.isoClassPresheafModelEquiv.{u} p)
    (fun _ _ f x => CategoryTheory.Functor.isoClassPresheafModelEquiv_naturality.{u} p f x)

/-- `AlgebraicGeometry.isoClassEquivalenceOverModel` as a based functor into the category
fibred in groupoids attached to the `Type u` model. -/
public noncomputable def isoClassBasedFunctorModel
    [p.IsFiberedInSetoids]
    [CategoryTheory.FunctorToTypes.Small.{u} p.isoClassPresheaf] :
    (BasedCategory.ofFunctor p) ⥤ᵇ
      (Stack.fibredCategory B S hS
        (CategoryTheory.Functor.isoClassPresheafModel.{u} p)).val :=
  ⟨(isoClassEquivalenceOverModel B S hS p).hom.functor,
    (isoClassEquivalenceOverModel B S hS p).hom.w⟩

/-- `AlgebraicGeometry.isoClassBasedFunctorModel` is an equivalence of categories. -/
public theorem isEquivalence_isoClassBasedFunctorModel
    [p.IsFiberedInSetoids]
    [CategoryTheory.FunctorToTypes.Small.{u} p.isoClassPresheaf] :
    Functor.IsEquivalence (isoClassBasedFunctorModel B S hS p).toFunctor :=
  (isoClassEquivalenceOverModel B S hS p).toEquivalence.isEquivalence_functor

end EquivalenceOver

namespace Stack

variable {B S hS}
variable {𝒴 𝒯₁ 𝒯₂ : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}

/-- The 2-fibre product of two scheme-valued points of `𝒴`, with `u`-small presheaf of
isomorphism classes, is representable by an algebraic space exactly when it is fibred in setoids
and the `Type u` model of its presheaf of isomorphism classes is an algebraic space. -/
public theorem isRepresentableByAlgebraicSpace_twoFibreProduct_iff
    (x : 𝒯₁ ⟶ 𝒴) (y : 𝒯₂ ⟶ 𝒴)
    [hfib : (twoFibreProduct B S hS 𝒴 𝒯₁ 𝒯₂ x.hom y.hom).val.p.IsFibered]
    [CategoryTheory.FunctorToTypes.Small.{u}
      (twoFibreProduct B S hS 𝒴 𝒯₁ 𝒯₂ x.hom y.hom).val.p.isoClassPresheaf] :
    IsRepresentableByAlgebraicSpace B S hS (twoFibreProduct B S hS 𝒴 𝒯₁ 𝒯₂ x.hom y.hom) ↔
      ((twoFibreProduct B S hS 𝒴 𝒯₁ 𝒯₂ x.hom y.hom).val.p.IsFiberedInSetoids ∧
        IsAlgebraicSpace B S hS
          (CategoryTheory.Functor.isoClassPresheafModel.{u}
            (twoFibreProduct B S hS 𝒴 𝒯₁ 𝒯₂ x.hom y.hom).val.p)) :=
  isRepresentableByAlgebraicSpace_iff_isAlgebraicSpace_isoClassPresheafModel B S hS _

end Stack

end AlgebraicGeometry

end
