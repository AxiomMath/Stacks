module

public import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseRightDerived
public import Mathlib.CategoryTheory.Triangulated.Orthogonal
public import StacksFrontier.CategoryTheory.Functor.Derived.Computing

/-!
# Derived functors from resolutions by orthogonal objects

Let `𝒞` be a triangulated category, let `𝒩` be a triangulated subcategory of `𝒞`, and let
`W = 𝒩.trW` be the associated multiplicative system — the morphisms whose cone lies in `𝒩`.
This file records the two standard criteria that produce the left, resp. right, derived functor
of an *arbitrary* functor `F : 𝒞 ⥤ ℋ` out of a supply of resolutions:

* if every object `X` receives a morphism `s : P ⟶ X` of `W` with `P` in the left orthogonal
  `⊥𝒩` of `𝒩`, then `LF` exists;
* dually, if every object `X` admits a morphism `s : X ⟶ I` of `W` with `I` in the right
  orthogonal `𝒩⊥`, then `RF` exists.

Both conclusions are drawn in two inequivalent senses: Deligne's everywhere-definedness
(essential constancy of the pro-, resp. ind-object on `W/X`, resp. `X/W`), which is
`CategoryTheory.Functor.IsLeftDerivable`, resp. `IsRightDerivable`; and Mathlib's Kan extension
condition `Functor.HasLeftDerivedFunctor`, resp. `HasRightDerivedFunctor`.

## Main results

* `CategoryTheory.ObjectProperty.isIso_of_trW_of_leftOrthogonal`, and its dual
  `isIso_of_trW_of_rightOrthogonal`: a morphism of `𝒩.trW` between two objects of `⊥𝒩` is
  already an isomorphism of `𝒞`.
* `ObjectProperty.isLeftDerivable_and_computesLeftDerived_of_leftOrthogonal_resolutions` and
  `isRightDerivable_and_computesRightDerived_of_rightOrthogonal_resolutions`: the resolution
  hypothesis gives everywhere-definedness in the sense of Stacks 05SV, and every orthogonal object
  computes the derived functor in the sense of Stacks 05SX.
* `CategoryTheory.ObjectProperty.hasPointwiseLeftDerivedFunctor_of_leftOrthogonal_resolutions`
  and `hasPointwiseRightDerivedFunctor_of_rightOrthogonal_resolutions`, with the corollaries
  `hasLeftDerivedFunctor_of_leftOrthogonal_resolutions` and
  `hasRightDerivedFunctor_of_rightOrthogonal_resolutions`: the resolution hypothesis gives the
  Kan extension along any localization functor for `𝒩.trW`.
* `CategoryTheory.ObjectProperty.leftOrthogonal_of_jointlyEpi` and
  `rightOrthogonal_of_jointlyMono`, with the corollaries `leftOrthogonal_sigma` and
  `rightOrthogonal_pi`: the left orthogonal is closed under any jointly epimorphic presentation,
  in particular under coproducts, and dually for the right orthogonal.
* `CategoryTheory.structuredArrowMkIdIsInitial` and `costructuredArrowMkIdIsTerminal`: if
  `L` is bijective on the morphisms out of `P`, resp. into `I`, then the identity of `L.obj P`,
  resp. `L.obj I`, is an initial, resp. terminal, object of the index category computing the
  pointwise Kan extension there.

## Implementation notes

The saturation hypothesis `MorphismProperty.IsSaturatedMultiplicative` is taken as an explicit
argument rather than derived from `𝒩`, since that is the form `Stacks.DerivedFunctor.Computing`
consumes; for a saturated triangulated subcategory it is supplied by
`MorphismProperty.IsSaturated.isSaturatedMultiplicative`.

## References

* [Stacks Project, Tag 06XN](https://stacks.math.columbia.edu/tag/06XN); everywhere-definedness
  is Tag 05SV, "computes" is Tag 05SX, and the situation is Tag 05S8.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {H : Type u₃} [Category.{v₃} H]

/-- If the localization functor `L` is bijective on the morphisms out of `P`, then the identity
of `L.obj P` is an initial object of the category `StructuredArrow (L.obj P) L` indexing the
limit that computes a pointwise right Kan extension of any functor along `L` at `L.obj P`. -/
noncomputable def structuredArrowMkIdIsInitial (L : C ⥤ D) (P : C)
    (h : ∀ Y : C, Function.Bijective (L.map : (P ⟶ Y) → (L.obj P ⟶ L.obj Y))) :
    IsInitial (StructuredArrow.mk (𝟙 (L.obj P)) : StructuredArrow (L.obj P) L) :=
  IsInitial.ofUniqueHom
    (fun g => StructuredArrow.homMk ((Equiv.ofBijective _ (h g.right)).symm g.hom) (by
      simpa using Equiv.ofBijective_apply_symm_apply _ (h g.right) g.hom))
    (fun g m => StructuredArrow.hom_ext _ _ (by
      change StructuredArrow.Hom.right m = (Equiv.ofBijective _ (h g.right)).symm g.hom
      rw [Equiv.eq_symm_apply]
      simpa using m.w))

/-- Dually to `CategoryTheory.structuredArrowMkIdIsInitial`: if `L` is bijective on the
morphisms into `I`, then the identity of `L.obj I` is a terminal object of
`CostructuredArrow L (L.obj I)`. -/
noncomputable def costructuredArrowMkIdIsTerminal (L : C ⥤ D) (I : C)
    (h : ∀ Y : C, Function.Bijective (L.map : (Y ⟶ I) → (L.obj Y ⟶ L.obj I))) :
    IsTerminal (CostructuredArrow.mk (𝟙 (L.obj I)) : CostructuredArrow L (L.obj I)) :=
  IsTerminal.ofUniqueHom
    (fun g => CostructuredArrow.homMk ((Equiv.ofBijective _ (h g.left)).symm g.hom) (by
      simpa using Equiv.ofBijective_apply_symm_apply _ (h g.left) g.hom))
    (fun g m => CostructuredArrow.hom_ext _ _ (by
      change CostructuredArrow.Hom.left m = (Equiv.ofBijective _ (h g.left)).symm g.hom
      rw [Equiv.eq_symm_apply]
      simpa using m.w))

/-- A functor has a pointwise right Kan extension along `L` at `L.obj P` as soon as `L` is
bijective on the morphisms out of `P`. -/
lemma hasPointwiseRightKanExtensionAt_of_bijective (L : C ⥤ D) (F : C ⥤ H) (P : C)
    (h : ∀ Y : C, Function.Bijective (L.map : (P ⟶ Y) → (L.obj P ⟶ L.obj Y))) :
    Functor.HasPointwiseRightKanExtensionAt L F (L.obj P) :=
  ⟨_, limitOfDiagramInitial (structuredArrowMkIdIsInitial L P h) _⟩

/-- A functor has a pointwise left Kan extension along `L` at `L.obj I` as soon as `L` is
bijective on the morphisms into `I`. -/
lemma hasPointwiseLeftKanExtensionAt_of_bijective (L : C ⥤ D) (F : C ⥤ H) (I : C)
    (h : ∀ Y : C, Function.Bijective (L.map : (Y ⟶ I) → (L.obj Y ⟶ L.obj I))) :
    Functor.HasPointwiseLeftKanExtensionAt L F (L.obj I) :=
  ⟨_, colimitOfDiagramTerminal (costructuredArrowMkIdIsTerminal L I h) _⟩

namespace ObjectProperty

section Sums

variable [HasZeroMorphisms C] (𝒩 : ObjectProperty C)

/-- If a family of morphisms into `S` is jointly epimorphic and every source lies in the left
orthogonal of `𝒩`, then `S` lies in the left orthogonal of `𝒩`. Joint epimorphy is all that is
used, so this applies to any presentation of `S` as a sum, not only to a coproduct. -/
lemma leftOrthogonal_of_jointlyEpi {ι : Type*} {X : ι → C} {S : C} (p : ∀ i, X i ⟶ S)
    (hp : ∀ {Y : C} (f g : S ⟶ Y), (∀ i, p i ≫ f = p i ≫ g) → f = g)
    (hX : ∀ i, 𝒩.leftOrthogonal (X i)) : 𝒩.leftOrthogonal S := fun Y f hY =>
  hp f 0 fun i => by rw [comp_zero]; exact hX i _ hY

/-- If a family of morphisms out of `S` is jointly monomorphic and every target lies in the
right orthogonal of `𝒩`, then `S` lies in the right orthogonal of `𝒩`. -/
lemma rightOrthogonal_of_jointlyMono {ι : Type*} {X : ι → C} {S : C} (p : ∀ i, S ⟶ X i)
    (hp : ∀ {Y : C} (f g : Y ⟶ S), (∀ i, f ≫ p i = g ≫ p i) → f = g)
    (hX : ∀ i, 𝒩.rightOrthogonal (X i)) : 𝒩.rightOrthogonal S := fun Y f hY =>
  hp f 0 fun i => by rw [zero_comp]; exact hX i _ hY

/-- A coproduct of objects of the left orthogonal of `𝒩` lies in the left orthogonal of `𝒩`:
a morphism out of the coproduct into an object of `𝒩` vanishes on every coprojection. -/
lemma leftOrthogonal_sigma {ι : Type*} (X : ι → C) [HasCoproduct X]
    (hX : ∀ i, 𝒩.leftOrthogonal (X i)) : 𝒩.leftOrthogonal (∐ X) :=
  𝒩.leftOrthogonal_of_jointlyEpi (fun i => Sigma.ι X i) (fun _ _ h => Sigma.hom_ext _ _ h) hX

/-- A product of objects of the right orthogonal of `𝒩` lies in the right orthogonal of `𝒩`:
a morphism from an object of `𝒩` into the product vanishes in every projection. -/
lemma rightOrthogonal_pi {ι : Type*} (X : ι → C) [HasProduct X]
    (hX : ∀ i, 𝒩.rightOrthogonal (X i)) : 𝒩.rightOrthogonal (∏ᶜ X) :=
  𝒩.rightOrthogonal_of_jointlyMono (fun i => Pi.π X i) (fun _ _ h => Pi.hom_ext _ _ h) hX

end Sums

/-- A morphism whose image under `L` is invertible is invertible, provided `L` is injective on the
endomorphisms of its source and target and hits the inverse of its image. -/
private theorem isIso_of_map_injective_of_surjective {L : C ⥤ D} {X Y : C} (f : X ⟶ Y)
    [IsIso (L.map f)] (hs : Function.Surjective (L.map : (Y ⟶ X) → _))
    (hX : Function.Injective (L.map : (X ⟶ X) → _))
    (hY : Function.Injective (L.map : (Y ⟶ Y) → _)) : IsIso f := by
  obtain ⟨g, hg⟩ := hs (inv (L.map f))
  exact ⟨g, hX (by simp [hg]), hY (by simp [hg])⟩

variable [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] [IsTriangulated C]
  (𝒩 : ObjectProperty C) [𝒩.IsTriangulated]

/-- A morphism of `𝒩.trW` between two objects of the left orthogonal of `𝒩` is an isomorphism
of `C`. -/
lemma isIso_of_trW_of_leftOrthogonal {X Y : C} (f : X ⟶ Y) (hf : 𝒩.trW f)
    (hX : 𝒩.leftOrthogonal X) (hY : 𝒩.leftOrthogonal Y) : IsIso f :=
  have : IsIso (𝒩.trW.Q.map f) := Localization.inverts 𝒩.trW.Q 𝒩.trW f hf
  isIso_of_map_injective_of_surjective (L := 𝒩.trW.Q) f
    (leftOrthogonal.map_bijective_of_isTriangulated hY 𝒩.trW.Q X).surjective
    (leftOrthogonal.map_bijective_of_isTriangulated hX 𝒩.trW.Q X).injective
    (leftOrthogonal.map_bijective_of_isTriangulated hY 𝒩.trW.Q Y).injective

/-- A morphism of `𝒩.trW` between two objects of the right orthogonal of `𝒩` is an isomorphism
of `C`. -/
lemma isIso_of_trW_of_rightOrthogonal {X Y : C} (f : X ⟶ Y) (hf : 𝒩.trW f)
    (hX : 𝒩.rightOrthogonal X) (hY : 𝒩.rightOrthogonal Y) : IsIso f :=
  have : IsIso (𝒩.trW.Q.map f) := Localization.inverts 𝒩.trW.Q 𝒩.trW f hf
  isIso_of_map_injective_of_surjective (L := 𝒩.trW.Q) f
    (rightOrthogonal.map_bijective_of_isTriangulated hX 𝒩.trW.Q Y).surjective
    (rightOrthogonal.map_bijective_of_isTriangulated hX 𝒩.trW.Q X).injective
    (rightOrthogonal.map_bijective_of_isTriangulated hY 𝒩.trW.Q Y).injective

section Left

variable (F : C ⥤ H)
  (hres : ∀ X : C, ∃ (P : C) (s : P ⟶ X), 𝒩.trW s ∧ 𝒩.leftOrthogonal P)

include hres

/-- **Stacks 06XN(2)** for a resolving left orthogonal. If every object of `C` receives a
morphism of `𝒩.trW` from an object of the left orthogonal of `𝒩`, then the left derived functor
of any `F` is everywhere defined, and every object of the left orthogonal computes it. -/
lemma isLeftDerivable_and_computesLeftDerived_of_leftOrthogonal_resolutions
    (hSat : 𝒩.trW.IsSaturatedMultiplicative) :
    F.IsLeftDerivable 𝒩.trW ∧
      ∀ P : C, 𝒩.leftOrthogonal P → F.ComputesLeftDerived 𝒩.trW P :=
  Stacks.DerivedFunctor.Computing.leftDerived_everywhereDefined_and_computes F 𝒩.trW hSat
    {P | 𝒩.leftOrthogonal P} hres
    (fun {_ _} s hs hX hX' =>
      have := 𝒩.isIso_of_trW_of_leftOrthogonal s hs hX hX'; inferInstance)

/-- The left derived functor of any `F` is everywhere defined in the sense of Stacks 05SV as
soon as the left orthogonal of `𝒩` is resolving. -/
lemma isLeftDerivable_of_leftOrthogonal_resolutions
    (hSat : 𝒩.trW.IsSaturatedMultiplicative) : F.IsLeftDerivable 𝒩.trW :=
  (𝒩.isLeftDerivable_and_computesLeftDerived_of_leftOrthogonal_resolutions F hres hSat).1

/-- Any `F` has a pointwise left derived functor with respect to `𝒩.trW` as soon as the left
orthogonal of `𝒩` is resolving. -/
lemma hasPointwiseLeftDerivedFunctor_of_leftOrthogonal_resolutions :
    F.HasPointwiseLeftDerivedFunctor 𝒩.trW := by
  intro X
  obtain ⟨P, s, hs, hP⟩ := hres X
  rw [← F.hasPointwiseLeftDerivedFunctorAt_iff_of_mem 𝒩.trW s hs,
    F.hasPointwiseLeftDerivedFunctorAt_iff 𝒩.trW.Q 𝒩.trW P]
  exact hasPointwiseRightKanExtensionAt_of_bijective 𝒩.trW.Q F P
    (leftOrthogonal.map_bijective_of_isTriangulated hP 𝒩.trW.Q)

/-- Any `F` has a left derived functor with respect to `𝒩.trW`, i.e. a right Kan extension
along a localization functor, as soon as the left orthogonal of `𝒩` is resolving. -/
lemma hasLeftDerivedFunctor_of_leftOrthogonal_resolutions :
    F.HasLeftDerivedFunctor 𝒩.trW :=
  have := 𝒩.hasPointwiseLeftDerivedFunctor_of_leftOrthogonal_resolutions F hres
  F.hasLeftDerivedFunctor_of_hasPointwiseLeftDerivedFunctor 𝒩.trW

end Left

section Right

variable (F : C ⥤ H)
  (hres : ∀ X : C, ∃ (I : C) (s : X ⟶ I), 𝒩.trW s ∧ 𝒩.rightOrthogonal I)

include hres

/-- **Stacks 06XN(1)** for a resolving right orthogonal. If every object of `C` admits a
morphism of `𝒩.trW` into an object of the right orthogonal of `𝒩`, then the right derived
functor of any `F` is everywhere defined, and every object of the right orthogonal computes
it. -/
lemma isRightDerivable_and_computesRightDerived_of_rightOrthogonal_resolutions
    (hSat : 𝒩.trW.IsSaturatedMultiplicative) :
    F.IsRightDerivable 𝒩.trW ∧
      ∀ I : C, 𝒩.rightOrthogonal I → F.ComputesRightDerived 𝒩.trW I :=
  Stacks.DerivedFunctor.Computing.rightDerived_everywhereDefined_and_computes F 𝒩.trW hSat
    {I | 𝒩.rightOrthogonal I} hres
    (fun {_ _} s hs hX hX' =>
      have := 𝒩.isIso_of_trW_of_rightOrthogonal s hs hX hX'; inferInstance)

/-- The right derived functor of any `F` is everywhere defined in the sense of Stacks 05SV as
soon as the right orthogonal of `𝒩` is resolving. -/
lemma isRightDerivable_of_rightOrthogonal_resolutions
    (hSat : 𝒩.trW.IsSaturatedMultiplicative) : F.IsRightDerivable 𝒩.trW :=
  (𝒩.isRightDerivable_and_computesRightDerived_of_rightOrthogonal_resolutions F hres hSat).1

/-- Any `F` has a pointwise right derived functor with respect to `𝒩.trW` as soon as the right
orthogonal of `𝒩` is resolving. -/
lemma hasPointwiseRightDerivedFunctor_of_rightOrthogonal_resolutions :
    F.HasPointwiseRightDerivedFunctor 𝒩.trW := by
  intro X
  obtain ⟨I, s, hs, hI⟩ := hres X
  rw [F.hasPointwiseRightDerivedFunctorAt_iff_of_mem 𝒩.trW s hs,
    F.hasPointwiseRightDerivedFunctorAt_iff 𝒩.trW.Q 𝒩.trW I]
  exact hasPointwiseLeftKanExtensionAt_of_bijective 𝒩.trW.Q F I
    (rightOrthogonal.map_bijective_of_isTriangulated hI 𝒩.trW.Q)

/-- Any `F` has a right derived functor with respect to `𝒩.trW`, i.e. a left Kan extension
along a localization functor, as soon as the right orthogonal of `𝒩` is resolving. -/
lemma hasRightDerivedFunctor_of_rightOrthogonal_resolutions :
    F.HasRightDerivedFunctor 𝒩.trW :=
  have := 𝒩.hasPointwiseRightDerivedFunctor_of_rightOrthogonal_resolutions F hres
  F.hasRightDerivedFunctor_of_hasPointwiseRightDerivedFunctor 𝒩.trW

end Right

end ObjectProperty

end CategoryTheory

end
