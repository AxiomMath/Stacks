module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.Preimmersion
public import Mathlib.AlgebraicGeometry.ResidueField
public import StacksFrontier.AlgebraicGeometry.Scheme.BaseChange.Points
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Scheme.ResidueFieldMapFromSpec

/-!
# Completely decomposed morphisms

A morphism of schemes is completely decomposed if every point of the target lifts to a point
whose induced residue field extension is trivial. A family with a fixed target is completely
decomposed when the morphism from the coproduct of its sources is completely decomposed.

Both conditions are closed under composition — for families, the second family may depend on
the member of the first, and the composite family is indexed by the dependent sum — and both are
stable under arbitrary base change.

## Main definitions

* `AlgebraicGeometry.IsCompletelyDecomposed` is the completely decomposed condition for a
  morphism.
* `AlgebraicGeometry.IsCompletelyDecomposedFamily` is the completely decomposed condition for
  a family of morphisms with a common target.

## Main results

* `AlgebraicGeometry.isCompletelyDecomposed_iff` is the pointwise characterization for one
  morphism.
* `AlgebraicGeometry.isCompletelyDecomposedFamily_iff` is the pointwise characterization for a
  family.
* `AlgebraicGeometry.isCompletelyDecomposed_id` says that an identity morphism is completely
  decomposed.
* `AlgebraicGeometry.isCompletelyDecomposed_comp` and
  `AlgebraicGeometry.isCompletelyDecomposedFamily_comp` prove closure under composition.
* `AlgebraicGeometry.isCompletelyDecomposed_pullback` and
  `AlgebraicGeometry.isCompletelyDecomposedFamily_pullback` prove stability under base change.

## References

* [Stacks Project, Tag 0GTI](https://stacks.math.columbia.edu/tag/0GTI)
* [Stacks Project, Tag 0GTJ](https://stacks.math.columbia.edu/tag/0GTJ)
* [Stacks Project, Tag 0GTK](https://stacks.math.columbia.edu/tag/0GTK)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v w

namespace AlgebraicGeometry

/-- A morphism of schemes is **completely decomposed** if every point of the target is the
image of a point at which the induced map on residue fields is an isomorphism. -/
@[stacks 0GTI "morphism"]
def IsCompletelyDecomposed {X Y : Scheme.{u}} (f : X ⟶ Y) : Prop :=
  ∀ y : Y, ∃ x : X, f x = y ∧ IsIso (f.residueFieldMap x)

/-- A family of morphisms of schemes with a common target is **completely decomposed** if the
induced morphism from the coproduct of the source schemes is completely decomposed. -/
@[stacks 0GTI "family"]
def IsCompletelyDecomposedFamily {I : Type v} [Small.{u} I]
    {X : I → Scheme.{u}} {Y : Scheme.{u}} (f : ∀ i, X i ⟶ Y) : Prop :=
  IsCompletelyDecomposed (Sigma.desc f)

/-- The pointwise characterization of a completely decomposed morphism. -/
theorem isCompletelyDecomposed_iff {X Y : Scheme.{u}} (f : X ⟶ Y) :
    IsCompletelyDecomposed f ↔
      ∀ y : Y, ∃ x : X, f x = y ∧ IsIso (f.residueFieldMap x) :=
  Iff.rfl

/-- Composites of morphisms inducing isomorphisms of residue fields at the relevant points induce
an isomorphism of residue fields. -/
private lemma isIso_residueFieldMap_comp_of_isIso {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    {x : X} (hf : IsIso (f.residueFieldMap x)) (hg : IsIso (g.residueFieldMap (f x))) :
    IsIso ((f ≫ g).residueFieldMap x) := by
  rw [Scheme.residueFieldMap_comp]; exact IsIso.comp_isIso' hg hf

/-- A family is completely decomposed exactly when every point of the target lifts to one of
its members with unchanged residue field. -/
theorem isCompletelyDecomposedFamily_iff {I : Type v} [Small.{u} I]
    {X : I → Scheme.{u}} {Y : Scheme.{u}} (f : ∀ i, X i ⟶ Y) :
    IsCompletelyDecomposedFamily f ↔
      ∀ y : Y, ∃ i, ∃ x : X i, f i x = y ∧ IsIso ((f i).residueFieldMap x) := by
  constructor
  · intro h y
    obtain ⟨z, hz, hzIso⟩ := h y
    have ⟨i, x, hzx⟩ : ∃ i, ∃ x : X i, Sigma.ι X i x = z := by
      have hcov := (sigmaOpenCover X).exists_eq z
      dsimp only [sigmaOpenCover, Scheme.Cover.copy] at hcov; exact hcov
    rw [← hzx] at hz hzIso
    refine ⟨i, x, ?_, ?_⟩
    · simpa [← Scheme.Hom.comp_apply] using hz
    · exact IsIso.of_isIso_fac_left
        (hh := isIso_residueFieldMap_comp_of_isIso inferInstance hzIso)
        (Scheme.Hom.residueFieldMap_congr (Sigma.ι_desc f i) x).symm
  · intro h y
    obtain ⟨i, x, hxy, hxIso⟩ := h y
    refine ⟨Sigma.ι X i x, ?_, ?_⟩
    · simpa [← Scheme.Hom.comp_apply] using hxy
    · have htotal : IsIso ((Sigma.ι X i ≫ Sigma.desc f).residueFieldMap x) := by
        rw [Scheme.Hom.residueFieldMap_congr (Sigma.ι_desc f i) x]
        exact IsIso.comp_isIso' (by infer_instance) hxIso
      exact IsIso.of_isIso_fac_right (hh := htotal)
        (Scheme.residueFieldMap_comp (Sigma.ι X i) (Sigma.desc f) x).symm

/-- Every identity morphism of schemes is completely decomposed. -/
@[simp]
theorem isCompletelyDecomposed_id (X : Scheme.{u}) :
    IsCompletelyDecomposed (𝟙 X) := by
  intro x; refine ⟨x, rfl, ?_⟩
  rw [Scheme.residueFieldMap_id]; exact IsIso.id _

/-- The composite of two completely decomposed morphisms of
schemes is completely decomposed. -/
@[stacks 0GTJ "morphisms"]
lemma isCompletelyDecomposed_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : IsCompletelyDecomposed f) (hg : IsCompletelyDecomposed g) :
    IsCompletelyDecomposed (f ≫ g) := by
  intro z; obtain ⟨y, rfl, hyIso⟩ := hg z
  obtain ⟨x, rfl, hxIso⟩ := hf y
  exact ⟨x, Scheme.Hom.comp_apply f g x,
    isIso_residueFieldMap_comp_of_isIso hxIso hyIso⟩

/-- Composing a completely decomposed family with a completely
decomposed family over each of its sources gives a completely decomposed family indexed by the
dependent sum. -/
@[stacks 0GTJ "families"]
lemma isCompletelyDecomposedFamily_comp {I : Type v} [Small.{u} I]
    {J : I → Type w} [∀ i, Small.{u} (J i)] {X : I → Scheme.{u}}
    {X' : ∀ i, J i → Scheme.{u}} {Y : Scheme.{u}} (f : ∀ i, X i ⟶ Y)
    (g : ∀ i j, X' i j ⟶ X i) (hf : IsCompletelyDecomposedFamily f)
    (hg : ∀ i, IsCompletelyDecomposedFamily (g i)) :
    IsCompletelyDecomposedFamily
      (fun ij : Σ i, J i => g ij.1 ij.2 ≫ f ij.1) := by
  rw [isCompletelyDecomposedFamily_iff] at hf ⊢; intro y
  obtain ⟨i, x, rfl, hxIso⟩ := hf y
  obtain ⟨j, x', rfl, hx'Iso⟩ :=
    (isCompletelyDecomposedFamily_iff (g i)).mp (hg i) x
  exact ⟨⟨i, j⟩, x', Scheme.Hom.comp_apply _ _ _,
    isIso_residueFieldMap_comp_of_isIso hx'Iso hxIso⟩

/-- A point of the source with trivial residue field extension lifts to a point of a base
change with trivial residue field extension. -/
private lemma exists_pullback_point_with_isIso_residueFieldMap
    {X Y Y' : Scheme.{u}} (f : X ⟶ Y) (g : Y' ⟶ Y) (y : Y') (x : X)
    (hx : f x = g y) (hfx : IsIso (f.residueFieldMap x)) :
    ∃ x' : (pullback f g : Scheme).carrier, pullback.snd f g x' = y ∧
      IsIso ((pullback.snd f g).residueFieldMap x') := by
  let := hfx
  let T : Scheme.Pullback.Triplet f g := .mk' x y hx
  let : IsIso (Y.residueFieldCongr hx).hom := (Y.residueFieldCongr hx).isIso_hom
  let : IsIso (Y.residueFieldCongr T.hx).hom := by infer_instance
  let : IsIso ((Y.residueFieldCongr T.hx).inv ≫ f.residueFieldMap T.x) := by
    show IsIso ((Y.residueFieldCongr hx).inv ≫ f.residueFieldMap x)
    infer_instance
  let : IsIso T.tensorInr := by
    show IsIso (pushout.inr
      ((Y.residueFieldCongr hx).inv ≫ f.residueFieldMap x)
      (g.residueFieldMap y))
    apply CategoryTheory.Limits.pushout_inr_iso_of_left_iso
  let : Field T.tensor := (MulEquiv.isField (Field.toIsField (Y'.residueField y))
    (asIso T.tensorInr).symm.commRingCatIsoToRingEquiv.toMulEquiv).toField
  let : IsOpenImmersion (Spec.map T.tensorInr) := by infer_instance
  let p : Spec T.tensor := by
    rw [Spec_carrier]
    exact ⊥
  refine ⟨T.SpecTensorTo p, T.snd_SpecTensorTo_apply p, ?_⟩
  have := Scheme.Pullback.isIso_residueFieldMap_specTensorTo_comp_residueFieldIso T p
  have : IsIso (T.SpecTensorTo.residueFieldMap p) :=
    IsIso.of_isIso_comp_right _ (Scheme.Spec.residueFieldIso T.tensor p).hom
  have hptComp : (T.SpecTensorTo ≫ pullback.snd f g) p =
      (Spec.map T.tensorInr ≫ Y'.fromSpecResidueField T.y) p := by
    rw [T.specTensorTo_snd]
  let : IsIso (Y'.residueFieldCongr hptComp).hom :=
    (Y'.residueFieldCongr hptComp).isIso_hom
  let : IsIso ((pullback.snd f g).residueFieldMap (T.SpecTensorTo p) ≫
      T.SpecTensorTo.residueFieldMap p) := by
    rw [← Scheme.residueFieldMap_comp, Scheme.Hom.residueFieldMap_congr T.specTensorTo_snd p,
      Scheme.residueFieldMap_comp]
    have hIsoFrom :=
      isIso_residueFieldMap_fromSpecResidueField Y' T.y (Spec.map T.tensorInr p)
    have : IsIso ((Spec.map T.tensorInr).residueFieldMap p) := by infer_instance
    show IsIso ((Y'.residueFieldCongr hptComp).hom ≫
      (Y'.fromSpecResidueField T.y).residueFieldMap ((Spec.map T.tensorInr) p) ≫
      (Spec.map T.tensorInr).residueFieldMap p)
    exact IsIso.comp_isIso' (Y'.residueFieldCongr hptComp).isIso_hom
      (IsIso.comp_isIso' hIsoFrom (by infer_instance))
  exact IsIso.of_isIso_comp_right _ (T.SpecTensorTo.residueFieldMap p)

/-- A completely decomposed morphism remains completely
decomposed after arbitrary base change. -/
@[stacks 0GTK "morphism"]
lemma isCompletelyDecomposed_pullback
    {X Y Y' : Scheme.{u}} (f : X ⟶ Y) (g : Y' ⟶ Y)
    (hf : IsCompletelyDecomposed f) :
    IsCompletelyDecomposed (pullback.snd f g) := by
  intro y
  obtain ⟨x, hx, hfx⟩ := hf (g y)
  exact exists_pullback_point_with_isIso_residueFieldMap f g y x hx hfx

/-- A completely decomposed family of morphisms remains completely decomposed after arbitrary
base change. -/
@[stacks 0GTK "family"]
lemma isCompletelyDecomposedFamily_pullback
    {I : Type v} [Small.{u} I] {X : I → Scheme.{u}} {Y Y' : Scheme.{u}}
    (f : ∀ i, X i ⟶ Y) (g : Y' ⟶ Y)
    (hf : IsCompletelyDecomposedFamily f) :
    IsCompletelyDecomposedFamily (fun i ↦ pullback.snd (f i) g) := by
  rw [isCompletelyDecomposedFamily_iff] at hf ⊢
  intro y
  obtain ⟨i, x, hx, hfx⟩ := hf (g y)
  exact ⟨i, exists_pullback_point_with_isIso_residueFieldMap (f i) g y x hx hfx⟩

end AlgebraicGeometry
