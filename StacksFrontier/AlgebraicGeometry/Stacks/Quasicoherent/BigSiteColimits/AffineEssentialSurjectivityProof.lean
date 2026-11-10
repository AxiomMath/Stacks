module

public import
  StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.BigSiteColimits.AffineCechSheafCondition
public import
  StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.BigSiteColimits.AffineEssentialSurjectivity
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.BigSiteColimits.AffineIteratedSlicePresentation

/-!
# The span at the affine objects over a member of a covering family

The essential surjectivity of Stacks 03DX is assembled from two span conditions at the affine
objects of a slice of the fppf site associated with a category fibred in groupoids: that the
sections over the members of a covering family of the terminal object are spanned by the
restrictions of the sections over the terminal object, and that the sections over an affine object
lying over a member are spanned by the restrictions of the sections over that member.  This file
proves the second, which is the hypothesis `haff` of
`AlgebraicGeometry.FibredSite.isGeneratedByUnit_over_of_sectionSpan_eq_top`, from what
quasi-coherence supplies at a member: a global presentation on the iterated slice there.

Quasi-coherence of a module on the slice at an object presents the module on the *iterated* slices
at the members of a covering family, whereas the span at the affine objects,
`AlgebraicGeometry.FibredSite.globalSectionSpan_eq_top_of_hasGlobalPresentation_of_isAffineOver`,
is about a slice at an object of the fibred category.  The two are the same site, by
`CategoryTheory.Over.iteratedSliceEquiv`, and
`Stacks.SheafOfModules.hasGlobalPresentation_iteratedSliceLeft` carries the presentation across.
Reading the span condition back at the morphism asked about is not an identity:
`CategoryTheory.Over.iteratedSliceBackward` produces, from an object of the slice at `f.left`, an
object whose left component is `CategoryTheory.Over.mk (a.left ≫ f.hom)` and not the source of
`a`, the two being isomorphic over the ambient object by an isomorphism which is the identity on
underlying objects.  Spanning by restricted sections is insensitive to composing the morphism with
an isomorphism on either side, which is the first half of this file.

## Main results

* `SheafOfModules.sectionSpan_eq_top_of_isIso`: the sections over an object are spanned by the
  restrictions of the sections over another along an isomorphism.
* `SheafOfModules.sectionSpan_eq_top_of_isIso_comp` and
  `SheafOfModules.sectionSpan_comp_isIso`: spanning by restricted sections is unchanged by
  composing the morphism with an isomorphism, before it or after it.
* `SheafOfModules.iteratedSliceLeft_sectionSpan_mk`: the span of the sections of the
  iterated-slice reading of a module, at the canonical objects, as a span of the sections of the
  module itself; a definitional identity.
* `SheafOfModules.sectionSpan_eq_top_of_iteratedSliceLeft`: the span of the sections over an
  object of a slice, from the span of the global sections of the iterated-slice reading of the
  module.
* `AlgebraicGeometry.FibredSite.sectionSpan_eq_top_of_hasGlobalPresentation_over`: the sections
  of a module over an affine object of a slice of the associated fppf site are spanned by the
  restrictions of its sections over an object it lies over, as soon as the module has a global
  presentation on the iterated slice at that object.

## References

* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 03DW](https://stacks.math.columbia.edu/tag/03DW)
* [Stacks Project, Tag 03DN](https://stacks.math.columbia.edu/tag/03DN)
* [Stacks Project, Tag 023M](https://stacks.math.columbia.edu/tag/023M)
-/

@[expose] public section

open CategoryTheory Opposite

namespace SheafOfModules

universe uC vC r m

variable {C : Type uC} [Category.{vC} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{r}}

/-- Restricting along an isomorphism and then along its inverse is the identity on sections. -/
private theorem restrictₛₗ_restrictₛₗ_inv (N : SheafOfModules.{m} R) {V W : C} (h : W ⟶ V)
    [IsIso h] (n : N.val.obj (op W)) :
    N.val.restrictₛₗ h.op (N.val.restrictₛₗ (inv h).op n) = n := by
  rw [← N.restrictₛₗ_comp_apply (inv h) h n, IsIso.hom_inv_id]
  simp

/-- The sections over an object are spanned by the restrictions of the sections over another along
an isomorphism: every section over the source is the restriction of its own image under
restriction along the inverse. -/
theorem sectionSpan_eq_top_of_isIso (N : SheafOfModules.{m} R) {V W : C} (h : W ⟶ V) [IsIso h] :
    N.sectionSpan h = ⊤ := by
  refine _root_.Submodule.eq_top_iff'.2 fun n => ?_
  exact N.restrictₛₗ_restrictₛₗ_inv h n ▸
    N.restrictₛₗ_mem_sectionSpan h (N.val.restrictₛₗ (inv h).op n)

/-- Spanning by restricted sections is insensitive to precomposition with an isomorphism: if the
sections over `V` are spanned by the restrictions of the sections over `U` along `k`, and `e` is
an isomorphism onto `V`, then the sections over the source of `e` are spanned by the restrictions
of the sections over `U` along the composite. -/
theorem sectionSpan_eq_top_of_isIso_comp (N : SheafOfModules.{m} R) {U V W : C} (k : V ⟶ U)
    (e : W ⟶ V) [IsIso e] (hk : N.sectionSpan k = ⊤) : N.sectionSpan (e ≫ k) = ⊤ :=
  N.sectionSpan_eq_top_comp k e hk (N.sectionSpan_eq_top_of_isIso e)

/-- Spanning by restricted sections is unchanged by postcomposing the morphism with an
isomorphism: restriction along an isomorphism is a bijection, so the two sets of restricted
sections whose spans are compared are the same set. -/
theorem sectionSpan_comp_isIso (N : SheafOfModules.{m} R) {U V W : C} (k : W ⟶ V) (ε : V ⟶ U)
    [IsIso ε] : N.sectionSpan (k ≫ ε) = N.sectionSpan k := by
  refine le_antisymm (_root_.Submodule.span_le.2 ?_) (_root_.Submodule.span_le.2 ?_)
  · rintro z ⟨n, rfl⟩
    rw [N.restrictₛₗ_comp_apply ε k n]
    exact N.restrictₛₗ_mem_sectionSpan k _
  · rintro z ⟨n, rfl⟩
    refine _root_.Submodule.subset_span ⟨N.val.restrictₛₗ (inv ε).op n, ?_⟩
    rw [N.restrictₛₗ_comp_apply ε k, N.restrictₛₗ_restrictₛₗ_inv ε n]

/-- The span of the sections over an affine object of a slice, as the span of the global sections
of the iterated-slice reading of the module: for `a : W ⟶ f` in the slice at `U`, the sections of
`Stacks.SheafOfModules.iteratedSliceLeft` over `CategoryTheory.Over.mk a.left` and the sections of
`N` over `CategoryTheory.Over.mk (a.left ≫ f.hom)` have the same span, both being the span of the
range of one restriction map. -/
lemma iteratedSliceLeft_sectionSpan_mk (R' : Sheaf J RingCat.{r}) (U : C) (f : Over U)
    (N : SheafOfModules.{m} (R'.over U)) {W : Over U} (a : W ⟶ f) :
    (Stacks.SheafOfModules.iteratedSliceLeft R' U f (N.over f)).sectionSpan
        (Over.homMk a.left (by simp) : (Over.mk a.left : Over f.left) ⟶ Over.mk (𝟙 f.left)) =
      N.sectionSpan (Over.homMk a.left (by simp) :
        (Over.mk (a.left ≫ f.hom) : Over U) ⟶ Over.mk (𝟙 f.left ≫ f.hom)) :=
  rfl

/-- The span of the sections over an object of a slice, from the span of the global sections of
the iterated-slice reading of the module: for `a : W ⟶ f` in the slice at `U`, if the restriction
of `N` to the slice at `f`, read on the slice site at `f.left`, has spanning global sections at
`CategoryTheory.Over.mk a.left`, then the sections of `N` over `W` are spanned by the restrictions
of its sections over `f` along `a`. -/
theorem sectionSpan_eq_top_of_iteratedSliceLeft (R' : Sheaf J RingCat.{r}) (U : C) (f : Over U)
    (N : SheafOfModules.{m} (R'.over U)) {W : Over U} (a : W ⟶ f)
    (h : (Stacks.SheafOfModules.iteratedSliceLeft R' U f (N.over f)).globalSectionSpan
      (Over.mkIdTerminal (X := f.left)) (Over.mk a.left) = ⊤) :
    N.sectionSpan a = ⊤ := by
  rw [globalSectionSpan_eq_sectionSpan,
    (Over.mkIdTerminal (X := f.left)).hom_ext (Over.mkIdTerminal.from (Over.mk a.left))
      (Over.homMk a.left (by simp)),
    iteratedSliceLeft_sectionSpan_mk] at h
  let ei : W ≅ (Over.mk (a.left ≫ f.hom) : Over U) := Over.isoMk (Iso.refl W.left) (by simp)
  let εi : (Over.mk (𝟙 f.left ≫ f.hom) : Over U) ≅ f := Over.isoMk (Iso.refl f.left) (by simp)
  have hfac : a = ei.hom ≫ ((Over.homMk a.left (by simp) :
      (Over.mk (a.left ≫ f.hom) : Over U) ⟶ Over.mk (𝟙 f.left ≫ f.hom)) ≫ εi.hom) := by
    ext
    simp [ei, εi]
  rw [hfac]
  exact N.sectionSpan_eq_top_of_isIso_comp _ ei.hom
    (by rw [N.sectionSpan_comp_isIso]; exact h)

end SheafOfModules

namespace AlgebraicGeometry.FibredSite

universe u v w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : Type v} [Category.{w} 𝒳] (p : 𝒳 ⥤ BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids)

include hp in
/-- The sections of a module over an affine object of a slice of the associated fppf site are
spanned by the restrictions of its sections over an affine object `V` the object lies over, as
soon as the module has a global presentation on the iterated slice at `V`.  This is the
hypothesis `haff` of
`AlgebraicGeometry.FibredSite.isGeneratedByUnit_over_of_sectionSpan_eq_top`, at one member of a
covering family. -/
theorem sectionSpan_eq_top_of_hasGlobalPresentation_over {x : 𝒳}
    {N : SheafOfModules.{u} ((ringStructureSheafCore B S hS p hp .fppf).over x)}
    (V : Over x) (hV : IsAffineOver B S hS (p.obj V.left))
    (hN : (N.over V).HasGlobalPresentation)
    (W : Over x) (hW : IsAffineOver B S hS (p.obj W.left)) (a : W ⟶ V) :
    N.sectionSpan a = ⊤ :=
  SheafOfModules.sectionSpan_eq_top_of_iteratedSliceLeft
    (ringStructureSheafCore B S hS p hp .fppf) x V N a
    (globalSectionSpan_eq_top_of_hasGlobalPresentation_of_isAffineOver B S hS p hp hV
      (Stacks.SheafOfModules.iteratedSliceLeft (ringStructureSheafCore B S hS p hp .fppf) x V
        (N.over V))
      (Stacks.SheafOfModules.hasGlobalPresentation_iteratedSliceLeft
        (ringStructureSheafCore B S hS p hp .fppf) x V (N.over V) hN)
      (Over.mk a.left) hW)

end AlgebraicGeometry.FibredSite

end
