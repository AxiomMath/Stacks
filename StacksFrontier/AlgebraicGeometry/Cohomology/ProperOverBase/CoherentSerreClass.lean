module

public import StacksCore.CategoryTheory.Abelian.SerreClass.Basic
public import StacksFrontier.AlgebraicGeometry.CoherentAbelian.Basic
public import StacksFrontier.AlgebraicGeometry.Cohomology.ProperOverBase.ModuleSupport
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionProper.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.Support.Functoriality

/-!
# Coherent modules with support proper over the base form a Serre subcategory

Let `f : X ⟶ S` be locally of finite type with `S` locally Noetherian. Inside the abelian
category of coherent `𝒪_X`-modules, those whose support is proper over `S` form a Serre
subcategory.

## Main results

* `AlgebraicGeometry.isSerreClass_hasProperSupport_coherentModules`: the Serre subcategory, as
  a property of objects of `AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf`.
  It is the property cutting out `Stacks.Algebraization.CoherentModulesProperOver f`.

## Implementation notes

A Serre class is characterised by a single condition — the middle term of an exact sequence
whose outer terms belong to it belongs to it — and that is the form in which the source proves
it, so the proof goes through `CategoryTheory.ObjectProperty.isSerreClass_iff_prop_X₂_of_exact`
rather than through the three closure clauses separately.

The inclusion of the coherent modules into all sheaves of modules is exact, so an exact short
complex of coherent modules is exact as a short complex of sheaves of modules and
`SheafOfModules.supp_subset_union_of_exact` applies to it: the support of the middle term is
contained in the union of the outer two supports, which is proper over `S` because a union of
two closed subsets proper over the base is. Closedness of the middle support, which is the
other half of `Stacks.Algebraization.HasProperSupport`, comes from coherence through finite
type.

The hypothesis that `S` is locally Noetherian is the source's and is kept, but the proof does
not use it. In the source it is what makes the coherent modules an abelian category, via local
Noetherianity of `X`; in this library that abelian structure is
`AlgebraicGeometry.CoherentAbelian.coherentModulesAbelian`, which holds over an arbitrary
ringed space, so the ambient category of the statement exists without it.

## References

* [Stacks Project, Tag 0CYU](https://stacks.math.columbia.edu/tag/0CYU)
* [Stacks Project, Tag 02MP](https://stacks.math.columbia.edu/tag/02MP)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open scoped ZeroObject

universe u

namespace AlgebraicGeometry

variable {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]

/-- **Stacks Project, Tag 0CYU, part (2).** For `f : X ⟶ S` locally of finite type with `S`
locally Noetherian, the coherent `𝒪_X`-modules whose support is proper over `S` form a Serre
subcategory of the abelian category of coherent `𝒪_X`-modules.

The zero module has empty support, which is proper over `S`; and the support of the middle term
of an exact sequence of coherent modules is contained in the union of the supports of the outer
two, a union of two closed subsets proper over `S` being proper over `S`. -/
@[stacks 0CYU "part (2)"]
theorem isSerreClass_hasProperSupport_coherentModules [IsLocallyNoetherian S] :
    ObjectProperty.IsSerreClass
      (C := SheafOfModules.CoherentModules X.ringCatSheaf)
      (fun F => Stacks.Algebraization.HasProperSupport f F.obj) := by
  refine (ObjectProperty.isSerreClass_iff_prop_X₂_of_exact _).2 ⟨⟨0, ?_⟩, ?_⟩
  · have hzero : IsZero (0 : SheafOfModules.CoherentModules X.ringCatSheaf).obj :=
      Functor.map_isZero (ObjectProperty.ι _) (isZero_zero _)
    exact ⟨⊥, by rw [_root_.SheafOfModules.supp_eq_empty_of_isZero hzero]; rfl,
      isProperOver_bot f⟩
  · intro T hT h₁ h₃
    obtain ⟨Z₁, hZ₁, hP₁⟩ := h₁
    obtain ⟨Z₃, hZ₃, hP₃⟩ := h₃
    have hft : T.X₂.obj.IsFiniteType := _root_.SheafOfModules.IsCoherent.isFiniteType
    refine ⟨⟨_root_.SheafOfModules.supp T.X₂.obj,
      _root_.SheafOfModules.isClosed_supp T.X₂.obj⟩, rfl,
      isProperOver_of_le f ?_ (isProperOver_sup f Z₁ Z₃ hP₁ hP₃)⟩
    have hsub := _root_.SheafOfModules.supp_subset_union_of_exact
      (T.map (ObjectProperty.ι
        (fun M : _root_.SheafOfModules.{u} X.ringCatSheaf => M.IsCoherent))) (hT.map _)
    have hle : _root_.SheafOfModules.supp T.X₂.obj ⊆ ((Z₁ ⊔ Z₃ : Closeds X) : Set X) := by
      rw [Closeds.coe_sup, hZ₁, hZ₃]
      exact hsub
    exact hle

end AlgebraicGeometry

end
