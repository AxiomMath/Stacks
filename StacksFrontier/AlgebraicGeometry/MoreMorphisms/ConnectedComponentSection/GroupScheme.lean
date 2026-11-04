module

public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
public import StacksFrontier.AlgebraicGeometry.Morphisms.Fibres.Section
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Connected components meeting a section, and the neutral section of a group scheme

For a morphism of schemes `f : X ⟶ Y` with a section `s : Y ⟶ X`, let `X⁰_y` be the connected
component of the fibre `X_y` containing `s(y)` and `X⁰ = ⋃_y X⁰_y ⊆ X`. This file describes `X⁰`
pointwise, and treats a group scheme `G ⟶ S` with its neutral section `e : S ⟶ G` as an instance
of this situation, with locus `G⁰ = ⋃_s G⁰_s`.

## Main definitions

* `AlgebraicGeometry.ConnectedAlongSection.ofGrpObj` is a group scheme `G ⟶ S` together with its
  neutral section `e : S ⟶ G`, viewed as a morphism of schemes with a section.
* `AlgebraicGeometry.GroupScheme.neutralLocus` is the subset `G⁰ ⊆ G` which is the union over
  `s : S` of the connected components of the fibres `G_s` containing `e(s)`.

## Main results

* `AlgebraicGeometry.ConnectedAlongSection.mem_locus_iff_asFiber_mem` says that a point `x` of
  `X` lies in `X⁰` exactly when, as a point of its own fibre `X_{f(x)}`, it lies in `X⁰_{f(x)}`.
* `AlgebraicGeometry.GroupScheme.fiberι_preimage_neutralLocus` identifies the trace of `G⁰` on
  the fibre `G_s` with the connected component of `G_s` containing the point `e(s)`.

## Implementation notes

A group scheme over `S` is a group object `G` in the cartesian monoidal category `Over S`. Its
neutral section is the underlying morphism of schemes `η[G].left : S ⟶ G.left` of the unit
`η[G] : 𝟙_ (Over S) ⟶ G`; it is a section of the structure morphism `G.hom : G.left ⟶ S`
because `η[G]` is a morphism over `S` out of the terminal object `𝟙_ (Over S) = Over.mk (𝟙 S)`.

## References

* [Stacks Project, Tag 055K](https://stacks.math.columbia.edu/tag/055K)
* [Stacks Project, Tag 055L](https://stacks.math.columbia.edu/tag/055L)
-/

@[expose] public section

open CategoryTheory MonObj

universe u

namespace AlgebraicGeometry

namespace ConnectedAlongSection

/-- For a morphism `f : X ⟶ Y` with a section `s`, the subset `X⁰ = ⋃_y X⁰_y` of `X` consists of
the points `x` which, viewed as points of their own fibre `X_{f(x)}`, lie in the connected
component `X⁰_{f(x)}` of that fibre containing `s(f(x))`. -/
@[stacks 055K "Situation 055L: X⁰ = ⋃_y X⁰_y, pointwise"]
theorem mem_locus_iff_asFiber_mem (D : ConnectedAlongSection.{u}) (x : D.X) :
    x ∈ D.locus ↔ D.f.asFiber x ∈ D.fiberComponent (D.f x) := by
  rw [← D.fiberι_preimage_locus (D.f x), Set.mem_preimage, Scheme.Hom.fiberι_asFiber]

variable {S : Scheme.{u}} (G : Over S) [GrpObj G]

/-- A group scheme `G ⟶ S` together with its neutral section `e : S ⟶ G`, as a morphism of
schemes with a section. The neutral section is the morphism of schemes underlying the unit
`η[G] : 𝟙_ (Over S) ⟶ G` of the group object `G`. -/
@[stacks 055K "a group scheme G → S with its neutral section e : S → G"]
noncomputable def ofGrpObj : ConnectedAlongSection.{u} where
  X := G.left
  Y := S
  f := G.hom
  s := η[G].left
  section_fac := Over.w η[G]

/-- The source of `ofGrpObj G` is the underlying scheme of `G`. -/
@[simp] lemma ofGrpObj_X : (ofGrpObj G).X = G.left := rfl

/-- The target of `ofGrpObj G` is the base scheme `S`. -/
@[simp] lemma ofGrpObj_Y : (ofGrpObj G).Y = S := rfl

/-- The morphism of `ofGrpObj G` is the structure morphism `G ⟶ S`. -/
@[simp] lemma ofGrpObj_f : (ofGrpObj G).f = G.hom := rfl

/-- The section of `ofGrpObj G` is the neutral section underlying the unit of `G`. -/
@[simp] lemma ofGrpObj_s : (ofGrpObj G).s = η[G].left := rfl

end ConnectedAlongSection

namespace GroupScheme

variable {S : Scheme.{u}} (G : Over S) [GrpObj G]

/-- For a group scheme `G ⟶ S` with neutral section `e`, the subset `G⁰ ⊆ G`: the union over
`s : S` of the connected components `G⁰_s` of the fibres `G_s` containing `e(s)`, that is, the
locus `X⁰` for `f = (G ⟶ S)` and the section `e`. -/
@[stacks 055K "G⁰ = ⋃_s G⁰_s for the neutral section",
  ega "IV 15.6.8" "special case",
  ega "IV 9.7.12" "special case", sga "3 XIX 5.10"]
noncomputable def neutralLocus : Set G.left :=
  (ConnectedAlongSection.ofGrpObj G).locus

/-- For a group scheme `G ⟶ S` with neutral section `e` and a point `s : S`, the trace of `G⁰` on
the fibre `G_s` is the connected component of `G_s` containing the point `e(s)`. -/
@[stacks 055K "the trace of G⁰ on G_s is the component of G_s containing e(s)"]
theorem fiberι_preimage_neutralLocus (s : S) (z : G.hom.fiber s)
    (hz : G.hom.fiberι s z = η[G].left s) :
    (G.hom.fiberι s) ⁻¹' neutralLocus G = connectedComponent z := by
  obtain rfl : z = (ConnectedAlongSection.ofGrpObj G).sectionPoint s :=
    (G.hom.fiberι s).isEmbedding.injective
      (hz.trans ((ConnectedAlongSection.ofGrpObj G).fiberι_sectionPoint s).symm)
  exact (ConnectedAlongSection.ofGrpObj G).fiberι_preimage_locus s

/-- A point `x` of a group scheme `G ⟶ S` lies in `G⁰` exactly when, viewed as a point of its
own fibre `G_{f(x)}`, it lies in the connected component of that fibre containing the value of
the neutral section. -/
theorem mem_neutralLocus_iff (x : G.left) :
    x ∈ neutralLocus G ↔
      G.hom.asFiber x ∈ (ConnectedAlongSection.ofGrpObj G).fiberComponent (G.hom x) :=
  (ConnectedAlongSection.ofGrpObj G).mem_locus_iff_asFiber_mem x

end GroupScheme

end AlgebraicGeometry

end
