module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import StacksFrontier.AlgebraicGeometry.Stacks.PresheafFibredCategory

/-!
# The category fibred in sets of Stacks Example 98.12.8

Let `Λ` be a Noetherian ring, `𝔪 ⊂ Λ` a maximal ideal and `C` a finite type `Λ`-algebra.
Put `S = Spec Λ`, `U = S ∖ {𝔪}` and `S' = U ⨿ Spec C`. Stacks Example 98.12.8 (tag 07XI)
considers the functor `F : (Sch/S)_{fppf}^{opp} → Sets` with `F(T) = *` if `T → S` factors
through `S' → S` and `F(T) = ∅` otherwise, and the category `𝒳 = 𝒮_F` fibred in sets
associated to it (Algebraic Stacks, Section 94.7).

This file constructs `S'`, the presheaf `F` on the big fppf site of `S`, and `𝒳`, and proves
that the objects of `𝒳` over `T` exist exactly when `T → S` factors through `S'`. Since the
values of `F` are subsingletons, a morphism of `𝒳` is the same as a morphism of its image in
the site: every morphism between the images of two objects lifts uniquely.

## Main definitions

* `Deformation.Artin.GRingNecessity.puncturedSpec`: the open subscheme `U = S ∖ {𝔪}`.
* `Deformation.Artin.GRingNecessity.puncturedCoprod`: the scheme `S' = U ⨿ Spec C`, with its
  morphism `puncturedCoprodMap` to `S`.
* `Deformation.Artin.GRingNecessity.FactorsThroughPuncturedCoprod`: a morphism to `S` factors
  through `S' → S`.
* `Deformation.Artin.GRingNecessity.factorizationPresheaf`: the presheaf `F`.
* `Deformation.Artin.GRingNecessity.factorizationCategory`: the category `𝒳 = 𝒮_F` fibred in
  sets over the big fppf site of `S`.

## Main results

* `Deformation.Artin.GRingNecessity.nonempty_fiber_iff`: there is an object of `𝒳` over `T`
  if and only if `T → S` factors through `S'`.
* `Deformation.Artin.GRingNecessity.existsUnique_hom_of_map`: every morphism between the
  images of two objects of `𝒳` in schemes over `S` is the image of a unique morphism.
* `Deformation.Artin.GRingNecessity.locallyOfFinitePresentation_puncturedCoprodMap`: `S' → S`
  is locally of finite presentation.

## Implementation notes

`F(T)` is the subtype `{_x : PUnit // T → S factors through S'}`: a one-point set if the
factorization exists and empty otherwise, as in the source. The category `𝒮_F` is the
library's `AlgebraicGeometry.Stack.fibredCategory`, the Grothendieck construction of `F`
regarded as a presheaf of discrete groupoids; its objects are the pairs `(T, x)` with
`x ∈ F(T)` and its morphisms `(T', x') ⟶ (T, x)` the morphisms `f : T' ⟶ T` of the site with
`f^* x = x'`, which is Categories, Example 4.38.5, used in Algebraic Stacks, Section 94.7.
The factorization through `S'` is not required to be unique (`Spec C → S` need not be a
monomorphism), so `F` is the image of `h_{S'} → h_S` rather than `h_{S'}` itself.

## References

* [Stacks Project, Tag 07XI](https://stacks.math.columbia.edu/tag/07XI)
* [Stacks Project, Tag 04SU](https://stacks.math.columbia.edu/tag/04SU)
-/

@[expose] public noncomputable section

namespace Deformation.Artin.GRingNecessity

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u

/-! ### The scheme `S' = U ⨿ Spec C` -/

section Scheme

variable {Λ : Type u} [CommRing Λ] (𝔪 : Ideal Λ) [𝔪.IsMaximal]

/-- The closed point `𝔪` of `S = Spec Λ`. -/
def closedPointOf : Spec (.of Λ) := (⟨𝔪, inferInstance⟩ : PrimeSpectrum Λ)

/-- The open subscheme `U = S ∖ {𝔪}` of `S = Spec Λ`. -/
def puncturedSpec : (Spec (.of Λ)).Opens :=
  ⟨{closedPointOf 𝔪}ᶜ,
    ((PrimeSpectrum.isClosed_singleton_iff_isMaximal (closedPointOf 𝔪)).mpr
      (inferInstanceAs 𝔪.IsMaximal)).isOpen_compl⟩

/-- A point of `S` lies in `U = S ∖ {𝔪}` exactly when it is not the closed point `𝔪`. -/
theorem mem_puncturedSpec_iff (x : Spec (.of Λ)) :
    x ∈ puncturedSpec 𝔪 ↔ x ≠ closedPointOf 𝔪 :=
  Iff.rfl

variable (C : Type u) [CommRing C] [Algebra Λ C]

/-- The scheme `S' = U ⨿ Spec C`, where `U = S ∖ {𝔪}`. -/
abbrev puncturedCoprod : Scheme.{u} :=
  (puncturedSpec 𝔪).toScheme ⨿ Spec (.of C)

/-- The morphism `S' = U ⨿ Spec C ⟶ S`: the open immersion on `U` and the spectrum of the
structure map on `Spec C`. -/
def puncturedCoprodMap : puncturedCoprod 𝔪 C ⟶ Spec (.of Λ) :=
  coprod.desc (puncturedSpec 𝔪).ι (Spec.map (CommRingCat.ofHom (algebraMap Λ C)))

/-- On `U`, the morphism `S' ⟶ S` is the open immersion. -/
@[reassoc (attr := simp)]
theorem inl_puncturedCoprodMap :
    coprod.inl ≫ puncturedCoprodMap 𝔪 C = (puncturedSpec 𝔪).ι :=
  coprod.inl_desc _ _

/-- On `Spec C`, the morphism `S' ⟶ S` is the spectrum of the structure map. -/
@[reassoc (attr := simp)]
theorem inr_puncturedCoprodMap :
    coprod.inr ≫ puncturedCoprodMap 𝔪 C = Spec.map (CommRingCat.ofHom (algebraMap Λ C)) :=
  coprod.inr_desc _ _

/-- A morphism `T ⟶ S` factors through `S' ⟶ S`. -/
def FactorsThroughPuncturedCoprod {T : Scheme.{u}} (f : T ⟶ Spec (.of Λ)) : Prop :=
  ∃ g : T ⟶ puncturedCoprod 𝔪 C, g ≫ puncturedCoprodMap 𝔪 C = f

variable {𝔪 C} in
/-- Factorizations through `S'` restrict along morphisms. -/
theorem FactorsThroughPuncturedCoprod.comp {T T' : Scheme.{u}} {f : T ⟶ Spec (.of Λ)}
    (h : FactorsThroughPuncturedCoprod 𝔪 C f) (e : T' ⟶ T) :
    FactorsThroughPuncturedCoprod 𝔪 C (e ≫ f) := by
  obtain ⟨g, rfl⟩ := h
  exact ⟨e ≫ g, Category.assoc _ _ _⟩

/-- `S' ⟶ S` is locally of finite presentation: `U ⟶ S` is an open immersion and `C` is
finitely presented over the Noetherian ring `Λ`. -/
theorem locallyOfFinitePresentation_puncturedCoprodMap [IsNoetherianRing Λ]
    [Algebra.FiniteType Λ C] : LocallyOfFinitePresentation (puncturedCoprodMap 𝔪 C) := by
  have : IsZariskiLocalAtSource @LocallyOfFinitePresentation.{u} :=
    HasRingHomProperty.instIsZariskiLocalAtSource
  rw [IsZariskiLocalAtSource.iff_of_openCover (P := @LocallyOfFinitePresentation.{u})
    (coprodOpenCover.{u, 0} _ _)]
  rintro (⟨⟩ | ⟨⟩)
  · change LocallyOfFinitePresentation (coprod.inl ≫ puncturedCoprodMap 𝔪 C)
    rw [inl_puncturedCoprodMap]
    infer_instance
  · change LocallyOfFinitePresentation (coprod.inr ≫ puncturedCoprodMap 𝔪 C)
    rw [inr_puncturedCoprodMap, LocallyOfFinitePresentation.SpecMap_iff]
    exact RingHom.finitePresentation_algebraMap.mpr
      (Algebra.FinitePresentation.of_finiteType.mp ‹_›)

end Scheme

/-! ### The presheaf `F` and the category `𝒳 = 𝒮_F` -/

section Presheaf

variable {Λ : Type u} [CommRing Λ] (𝔪 : Ideal Λ) [𝔪.IsMaximal]
  (C : Type u) [CommRing C] [Algebra Λ C]
  (B : BigFppfSite.{u}) (hS : B.Contains (Spec (.of Λ)))

/-- The structure morphism to `S` of an object of the big fppf site of `S`. -/
abbrev structureHom (T : BigFppfOver B (Spec (.of Λ)) hS) :
    ((BigFppfOver.toScheme B (Spec (.of Λ)) hS).obj T) ⟶ Spec (.of Λ) :=
  T.hom.hom

/-- A morphism of the big fppf site of `S` commutes with the structure morphisms. -/
theorem structureHom_comp {T T' : BigFppfOver B (Spec (.of Λ)) hS} (e : T' ⟶ T) :
    e.left.hom ≫ structureHom B hS T = structureHom B hS T' :=
  congrArg InducedCategory.Hom.hom (Over.w e)

/-- **The functor `F` of Stacks Example 98.12.8.** On the big fppf site of `S = Spec Λ`,
`F(T)` is a point if `T → S` factors through `S' = U ⨿ Spec C` and is empty otherwise. -/
def factorizationPresheaf : (BigFppfOver B (Spec (.of Λ)) hS)ᵒᵖ ⥤ Type u where
  obj T := {_x : PUnit.{u + 1} // FactorsThroughPuncturedCoprod 𝔪 C (structureHom B hS T.unop)}
  map {T T'} e := TypeCat.ofHom
    (fun x : {_x : PUnit.{u + 1} //
        FactorsThroughPuncturedCoprod 𝔪 C (structureHom B hS T.unop)} =>
      (⟨x.1, (structureHom_comp B hS e.unop) ▸ x.2.comp e.unop.left.hom⟩ :
        {_x : PUnit.{u + 1} //
          FactorsThroughPuncturedCoprod 𝔪 C (structureHom B hS T'.unop)}))
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The values of `F` are subsingletons. -/
instance (T : (BigFppfOver B (Spec (.of Λ)) hS)ᵒᵖ) :
    Subsingleton ((factorizationPresheaf 𝔪 C B hS).obj T) :=
  inferInstanceAs (Subsingleton {_x : PUnit.{u + 1} // _})

/-- **The category `𝒳 = 𝒮_F` of Stacks Example 98.12.8**, fibred in sets over the big fppf
site of `S = Spec Λ`: its objects over `T` are the elements of `F(T)`, that is, the witnesses
that `T → S` factors through `S' = (S ∖ {𝔪}) ⨿ Spec C`. -/
def factorizationCategory :
    CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B (Spec (.of Λ)) hS) :=
  AlgebraicGeometry.Stack.fibredCategory B (Spec (.of Λ)) hS (factorizationPresheaf 𝔪 C B hS)

/-- The functor from `𝒳` to schemes over `S`. -/
abbrev factorizationFunctor :
    (factorizationCategory 𝔪 C B hS).val.obj ⥤ Over (Spec (.of Λ)) :=
  (factorizationCategory 𝔪 C B hS).val.p ⋙ Over.post B.inclusion

/-- The object of `𝒳` over `T` given by a factorization of `T → S` through `S'`. -/
def mkObj (T : BigFppfOver B (Spec (.of Λ)) hS)
    (h : FactorsThroughPuncturedCoprod 𝔪 C (structureHom B hS T)) :
    (factorizationCategory 𝔪 C B hS).val.obj :=
  ⟨T, ⟨⟨PUnit.unit, h⟩⟩⟩

/-- The object `mkObj T h` of `𝒳` lies over `T`. -/
@[simp]
theorem p_obj_mkObj (T : BigFppfOver B (Spec (.of Λ)) hS)
    (h : FactorsThroughPuncturedCoprod 𝔪 C (structureHom B hS T)) :
    (factorizationCategory 𝔪 C B hS).val.p.obj (mkObj 𝔪 C B hS T h) = T :=
  rfl

variable {𝔪 C B hS} in
/-- The base of an object of `𝒳` factors through `S'`. -/
theorem factors_of_obj (X : (factorizationCategory 𝔪 C B hS).val.obj) :
    FactorsThroughPuncturedCoprod 𝔪 C
      (structureHom B hS ((factorizationCategory 𝔪 C B hS).val.p.obj X)) :=
  X.fiber.as.2

/-- **Objects of `𝒳 = 𝒮_F`.** There is an object of `𝒳` over `T` exactly when `T → S`
factors through `S' = (S ∖ {𝔪}) ⨿ Spec C`. -/
theorem nonempty_fiber_iff (T : BigFppfOver B (Spec (.of Λ)) hS) :
    Nonempty ((factorizationCategory 𝔪 C B hS).val.p.Fiber T) ↔
      FactorsThroughPuncturedCoprod 𝔪 C (structureHom B hS T) := by
  refine ⟨?_, fun h ↦ ⟨⟨mkObj 𝔪 C B hS T h, rfl⟩⟩⟩
  rintro ⟨X, rfl⟩
  exact factors_of_obj X

variable {𝔪 C B hS}

/-- The morphism of `𝒳` lying over a given morphism of the site. -/
def homOfBase {X Y : (factorizationCategory 𝔪 C B hS).val.obj}
    (f : (factorizationCategory 𝔪 C B hS).val.p.obj X ⟶
      (factorizationCategory 𝔪 C B hS).val.p.obj Y) : X ⟶ Y :=
  ⟨f, Discrete.eqToHom
    (Subsingleton.elim (α := (factorizationPresheaf 𝔪 C B hS).obj (op X.base)) _ _)⟩

/-- The morphism `homOfBase f` of `𝒳` lies over `f`. -/
@[simp]
theorem p_map_homOfBase {X Y : (factorizationCategory 𝔪 C B hS).val.obj}
    (f : (factorizationCategory 𝔪 C B hS).val.p.obj X ⟶
      (factorizationCategory 𝔪 C B hS).val.p.obj Y) :
    (factorizationCategory 𝔪 C B hS).val.p.map (homOfBase f) = f :=
  rfl

/-- Morphisms of `𝒳` are determined by their images in the site. -/
theorem hom_ext_of_map {X Y : (factorizationCategory 𝔪 C B hS).val.obj} {f g : X ⟶ Y}
    (h : (factorizationCategory 𝔪 C B hS).val.p.map f =
      (factorizationCategory 𝔪 C B hS).val.p.map g) : f = g :=
  Pseudofunctor.CoGrothendieck.Hom.ext f g h (by apply Discrete.hom_eq)

/-- Morphisms of `𝒳` are determined by their images in schemes over `S`. -/
theorem hom_ext_of_post {X Y : (factorizationCategory 𝔪 C B hS).val.obj} {f g : X ⟶ Y}
    (h : ((factorizationCategory 𝔪 C B hS).val.p ⋙ Over.post B.inclusion).map f =
      ((factorizationCategory 𝔪 C B hS).val.p ⋙ Over.post B.inclusion).map g) : f = g :=
  hom_ext_of_map ((Over.post B.inclusion).map_injective h)

/-- Every morphism between the images of two objects of `𝒳` in schemes over `S` is the image
of a unique morphism of `𝒳`. -/
theorem existsUnique_hom_of_map {X Y : (factorizationCategory 𝔪 C B hS).val.obj}
    (f : ((factorizationCategory 𝔪 C B hS).val.p ⋙ Over.post B.inclusion).obj X ⟶
      ((factorizationCategory 𝔪 C B hS).val.p ⋙ Over.post B.inclusion).obj Y) :
    ∃! g : X ⟶ Y,
      ((factorizationCategory 𝔪 C B hS).val.p ⋙ Over.post B.inclusion).map g = f :=
  ⟨homOfBase ((Over.post B.inclusion).preimage f), (Over.post B.inclusion).map_preimage f,
    fun _ hg => hom_ext_of_post (hg.trans ((Over.post B.inclusion).map_preimage f).symm)⟩

end Presheaf

end Deformation.Artin.GRingNecessity

end
