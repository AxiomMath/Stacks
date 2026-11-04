module

public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.CategoryTheory.Sites.PreservesLocallyBijective
public import StacksFrontier.AlgebraicGeometry.ProEtale.DerivedCompleteSlicedSituation
public import StacksFrontier.AlgebraicGeometry.ProEtale.WeaklyContractible.Slice
public import StacksFrontier.AlgebraicGeometry.ProEtale.WeaklyContractible.TestingFamily

/-!
# Testing families tested on the slice sites, in a chosen value universe

`Stacks.WeaklyContractible.WeaklyContractibleTestingFamily` is a covering collection of weakly
contractible objects of a `Type v`-small site, weak contractibility being tested on sheaves of sets
in the morphism universe. On a site whose objects form a large type, such as the small pro-étale
site of a scheme, weak contractibility depends on the universe the sheaves of sets take values
in, and the universe transfer of the small case is not available.

A *slice testing family* fixes a value universe `t` instead, and asks each member `U` to be weakly
contractible for sheaves of sets in `Type t` on the slice site `C/U`, at its final object `U ⟶ U`.
Asking it on the slice is what makes the notion stable under passing to slice sites, with no
sheafification in `Type t`; it implies the same statement on `C` itself by restriction to the
slice. No smallness of the site is assumed.

## Main definitions

* `Stacks.WeaklyContractible.SliceTestingFamily`: the family.
* `Stacks.WeaklyContractible.SliceTestingFamily.over`: the family it induces on a slice site.
* `Stacks.WeaklyContractible.SliceTestingFamily.ofIsWeaklyContractible`: on a small site, a
  covering collection of weakly contractible objects is a slice testing family in every value
  universe.
* `Stacks.WeaklyContractible.SliceTestingFamily.toSlicedObjectsSituation`: the
  `Stacks.WeaklyContractible.SlicedObjectsSituation` of a slice testing family and a sheaf of
  rings.

## Main results

* `Stacks.WeaklyContractible.SliceTestingFamily.surjective_app`: a locally surjective morphism of
  sheaves of sets in `Type t` is surjective on sections over a member.
* `Stacks.WeaklyContractible.SliceTestingFamily.exact_sheafSections`: evaluation on a member is
  exact.
* `Stacks.WeaklyContractible.SliceTestingFamily.exact_iff_exact_sections`: a short complex of
  sheaves of modules is exact exactly when its sections on every member are exact.

## References

* [Stacks Project, Tag 0946](https://stacks.math.columbia.edu/tag/0946)
* [Stacks Project, Tag 0947](https://stacks.math.columbia.edu/tag/0947)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe t w v u

namespace Stacks.WeaklyContractible

attribute [local instance] smallOverOfSmall wEqualsLocallyBijective_types

/-- A covering collection of objects of a site, each weakly contractible for sheaves of sets in
the value universe `t` on its slice site: on the slice site over a member `U`, a locally
surjective morphism of sheaves of sets in `Type t` is surjective on sections over the final object
`U ⟶ U`. -/
structure SliceTestingFamily (C : Type u) [Category.{v} C] (J : GrothendieckTopology C) where
  /-- The chosen collection of testing objects. -/
  B : ObjectProperty C
  /-- Every testing object is weakly contractible on its slice site, in the universe `t`. -/
  surjective_app_over : ∀ ⦃U : C⦄, B U → ∀ {F G : Sheaf (J.over U) (Type t)} (φ : F ⟶ G),
    Sheaf.IsLocallySurjective φ → Function.Surjective (φ.hom.app (op (Over.mk (𝟙 U))))
  /-- Every object of the site is covered by testing objects. -/
  hasEnoughObjects : J.HasEnoughObjects B

/-- Surjectivity of a morphism of presheaves of types on sections over an object depends only on
the object up to isomorphism. -/
private theorem surjective_presheaf_app_of_iso {C : Type u} [Category.{v} C]
    {F G : Cᵒᵖ ⥤ Type t} (φ : F ⟶ G) {X Y : C} (e : X ≅ Y)
    (h : Function.Surjective (φ.app (op X))) : Function.Surjective (φ.app (op Y)) := by
  intro s
  obtain ⟨x, hx⟩ := h (G.map e.hom.op s)
  refine ⟨F.map e.inv.op x, ?_⟩
  rw [NatTrans.naturality_apply, hx, ← Functor.map_comp_apply, ← op_comp,
    Iso.inv_hom_id, op_id, Functor.map_id_apply]

/-- The final object of the slice of a slice: the arrow `W ⟶ W` of `(C/U)/W` is the image of
the arrow `W.left ⟶ W.left` of `C/W.left` under the iterated slice equivalence. -/
def iteratedSliceBackwardObjMkIdIso {C : Type u} [Category.{v} C] {U : C} (W : Over U) :
    (Over.iteratedSliceBackward W).obj (Over.mk (𝟙 W.left)) ≅ Over.mk (𝟙 W) :=
  Over.isoMk (Over.isoMk (Iso.refl _) (by rfl)) (by ext; simp; rfl)

namespace SliceTestingFamily

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (h : SliceTestingFamily.{t} C J)

/-- A locally surjective morphism of sheaves of sets in `Type t` is surjective on sections over
a member of a slice testing family: restrict it to the slice site over the member. -/
theorem surjective_app {U : C} (hU : h.B U) {F G : Sheaf J (Type t)} (φ : F ⟶ G)
    (hφ : Sheaf.IsLocallySurjective φ) : Function.Surjective (φ.hom.app (op U)) := by
  have : Presheaf.IsLocallySurjective J φ.hom := hφ
  exact h.surjective_app_over hU
    (((Over.forget U).sheafPushforwardContinuous (Type t) (J.over U) J).map φ)
    (Presheaf.isLocallySurjective_whisker (J.over U) J (Over.forget U) φ.hom)

/-- The standing situation of a slice testing family and a sheaf of rings. -/
def toSituation (O : Sheaf J RingCat.{w}) :
    WeaklyContractibleObjectsSituation.{w, v, u, t} C J where
  B := h.B
  isWeaklyContractible _ hU _ _ φ hφ := h.surjective_app hU φ hφ
  hasEnoughObjects := h.hasEnoughObjects
  O := O

variable (J) in
/-- A slice testing family on a site induces one on every slice site: the arrows whose source
belongs to the family. Weak contractibility on the slice of the slice is transported along the
iterated slice equivalence `(C/U)/W ≌ C/W.left`. -/
def over (U : C) : SliceTestingFamily.{t} (Over U) (J.over U) where
  B := fun W => h.B W.left
  surjective_app_over W hW F G φ hφ := by
    have : Presheaf.IsLocallySurjective _ φ.hom := hφ
    exact surjective_presheaf_app_of_iso φ.hom (iteratedSliceBackwardObjMkIdIso W)
      (h.surjective_app_over hW
        (((Over.iteratedSliceBackward W).sheafPushforwardContinuous (Type t) (J.over W.left)
          ((J.over U).over W)).map φ)
        (Presheaf.isLocallySurjective_whisker (J.over W.left) ((J.over U).over W)
          (Over.iteratedSliceBackward W) φ.hom))
  hasEnoughObjects := hasEnoughObjects_over h.hasEnoughObjects U

/-- The `Stacks.WeaklyContractible.SlicedObjectsSituation` of a slice testing family and a sheaf
of rings: the surjectivity on the slice site over `U` is that of the family `h.over J U`. -/
def toSlicedObjectsSituation (O : Sheaf J RingCat.{w}) :
    SlicedObjectsSituation.{w, v, u, t} C J where
  toWeaklyContractibleObjectsSituation := h.toSituation O
  isWeaklyContractibleOver U _ hZ _ _ φ hφ := (h.over J U).surjective_app hZ φ hφ

end SliceTestingFamily

/-- On a small site, a covering collection of weakly contractible objects is a slice testing
family in every value universe: an arrow `U ⟶ U` with weakly contractible source is weakly
contractible on the slice site, which is small, and weak contractibility there passes to every
value universe. -/
def SliceTestingFamily.ofIsWeaklyContractible {C : Type u} [Category.{v} C] [Small.{v} C]
    (J : GrothendieckTopology C) [HasSheafify J (Type v)]
    (B : ObjectProperty C) (hB : ∀ ⦃U : C⦄, B U → J.IsWeaklyContractible U)
    (hE : J.HasEnoughObjects B) : SliceTestingFamily.{t} C J where
  B := B
  surjective_app_over U hU F G φ hφ :=
    have : HasSheafify (J.over U) (Type v) :=
      CategoryTheory.hasSheafifyEssentiallySmallSite (J.over U) (Type v)
    surjective_sections_of_isWeaklyContractible (J.over U) (Over.mk (𝟙 U))
      (weaklyContractible_over J (𝟙 U) (hB hU)) F G φ hφ
  hasEnoughObjects := hE

namespace SliceTestingFamily

/-- Evaluation on a member of a slice testing family is exact. -/
theorem exact_sheafSections {C : Type u} [Category.{v} C]
    (J : GrothendieckTopology C) [HasSheafify J AddCommGrpCat.{t}]
    (h : SliceTestingFamily.{t} C J) (U : C) (hU : h.B U) :
    exactFunctor (Sheaf J AddCommGrpCat.{t}) AddCommGrpCat.{t}
      ((sheafSections J AddCommGrpCat.{t}).obj (op U)) :=
  exact_sheafSections_of_isWeaklyContractible.{t} J U
    (fun _ _ φ hφ ↦ h.surjective_app hU φ hφ)

/-- A short complex of sheaves of modules is exact exactly when its sections on every member of
a slice testing family are exact. The ring universe is independent of the site and of the module
universe. -/
theorem exact_iff_exact_sections {C : Type u} [Category.{v} C]
    (J : GrothendieckTopology C) [HasSheafify J AddCommGrpCat.{t}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{t}]
    (h : SliceTestingFamily.{t} C J) (O : Sheaf J RingCat.{w})
    (S : ShortComplex (SheafOfModules.{t} O)) :
    S.Exact ↔ ∀ {U : C}, h.B U →
      Function.Exact (S.f.val.app (op U)) (S.g.val.app (op U)) :=
  exact_iff_exact_sections_of_weaklyContractibleObjectsSituation J (h.toSituation O) S

end SliceTestingFamily

end Stacks.WeaklyContractible

end
