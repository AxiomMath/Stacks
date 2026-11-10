module

public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import StacksFrontier.Algebra.Homology.StupidTruncationLE
public import StacksFrontier.Algebra.Homology.StupidTruncationFunctorial

/-!
# The triangles of the stupid filtrations with explicit connecting maps

For a cochain complex `K` the two families of short exact sequences of the stupid filtrations,

`0 ⟶ Kᵖ[-p] ⟶ σ^{≤p}K ⟶ σ^{≤p'}K ⟶ 0` (`p' + 1 = p`) and `0 ⟶ σ^{≥p+1}K ⟶ σ^{≥p}K ⟶ Kᵖ[-p] ⟶ 0`,

are degreewise split. This file records the canonical splittings of the first family (those of
the second are `StacksDraft.StupidTruncation.stupidTruncGESplitting`) and the distinguished
triangles of the derived category that the splittings define. Their third morphisms are the
images of the explicit cochain maps `CochainComplex.homOfDegreewiseSplit`, whose only nonzero
component is the differential `Kᵖ' ⟶ Kᵖ` of `K`; this is how the proof of [Stacks, Tag 0G8K]
reads the connecting maps of these triangles ("given by actual maps of complexes, namely using
the differential").

## Main definitions

* `StacksDraft.StupidTruncation.stupidTruncLESplitting`: the splittings of the first family.
* `StacksDraft.StupidTruncation.stupidTruncLESplitTriangle` and
  `StacksDraft.StupidTruncation.stupidTruncGESplitTriangle`: the triangles in the derived
  category.

## Main results

* `StacksDraft.StupidTruncation.stupidTruncLESplitTriangle_distinguished` and
  `StacksDraft.StupidTruncation.stupidTruncGESplitTriangle_distinguished`.

## References

* [Stacks Project, Tag 0G8K](https://stacks.math.columbia.edu/tag/0G8K)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits HomologicalComplex ComplexShape

namespace StacksDraft.StupidTruncation

noncomputable section

section Splitting

variable {C : Type*} [Category* C] [Abelian C] (K : CochainComplex C ℤ)

/-- The inclusion `σ^{≤p}K ⟶ K` is an isomorphism in degree `p`. -/
theorem isIso_stupidTruncLEι_f_self (p : ℤ) : IsIso ((stupidTruncLEι K p).f p) := by
  rw [stupidTruncLEι_f]
  infer_instance

/-- For `p' + 1 = p`, the comparison map `σ^{≤p}K ⟶ σ^{≤p'}K` is an isomorphism in every degree
`n ≠ p`. -/
theorem isIso_stupidTruncLEMapLE_f_of_ne (p p' : ℤ) (hp : p' + 1 = p) (n : ℤ) (hn : n ≠ p) :
    IsIso ((stupidTruncLEMapLE K (show p' ≤ p by omega)).f n) := by
  by_cases hpn : n < p
  · exact isIso_stupidTruncLEMapLE_f K _ n (by omega)
  · exact IsZero.isIso
      (CochainComplex.isZero_of_isStrictlyLE (K.stupidTrunc (embeddingUpIntLE p)) p n (by omega))
      (CochainComplex.isZero_of_isStrictlyLE (K.stupidTrunc (embeddingUpIntLE p')) p' n
        (by omega)) _

open Classical in
/-- The canonical degreewise splitting of the short exact sequence
`Kᵖ[-p] ⟶ σ^{≤p}K ⟶ σ^{≤p'}K`: in degree `p` the last term vanishes and the inclusion of the
top term is an isomorphism, in every other degree the first term vanishes and the comparison of
truncations is an isomorphism. -/
def stupidTruncLESplitting (p p' : ℤ) (hp : p' + 1 = p) (n : ℤ) :
    ((stupidTruncLEShortComplex K p p' hp).map (eval C (.up ℤ) n)).Splitting :=
  if hn : n = p then
    ShortComplex.Splitting.ofIsIsoOfIsZero _
      (by
        subst hn
        exact isIso_stupidTruncLEι_f_self K n)
      (CochainComplex.isZero_of_isStrictlyLE (K.stupidTrunc (embeddingUpIntLE p')) p' n
        (by omega))
  else
    ShortComplex.Splitting.ofIsZeroOfIsIso _ (isZero_single_obj_X (.up ℤ) p (K.X p) n hn)
      (isIso_stupidTruncLEMapLE_f_of_ne K p p' hp n hn)

/-- In degree `p` the retraction of the canonical splitting inverts the inclusion of the top
term. -/
theorem stupidTruncLESplitting_r_self (p p' : ℤ) (hp : p' + 1 = p) :
    (stupidTruncLESplitting K p p' hp p).r =
      @inv _ _ _ _ ((stupidTruncLEι K p).f p) (isIso_stupidTruncLEι_f_self K p) := by
  simp only [stupidTruncLESplitting, dite_eq_left rfl, ShortComplex.Splitting.ofIsIsoOfIsZero]
  rfl

/-- In degree `p` the section of the canonical splitting vanishes. -/
theorem stupidTruncLESplitting_s_self (p p' : ℤ) (hp : p' + 1 = p) :
    (stupidTruncLESplitting K p p' hp p).s = 0 := by
  simp only [stupidTruncLESplitting, dite_eq_left rfl, ShortComplex.Splitting.ofIsIsoOfIsZero]

/-- Away from degree `p` the section of the canonical splitting inverts the comparison of
truncations. -/
theorem stupidTruncLESplitting_s_of_ne (p p' : ℤ) (hp : p' + 1 = p) (n : ℤ) (hn : n ≠ p) :
    (stupidTruncLESplitting K p p' hp n).s =
      @inv _ _ _ _ ((stupidTruncLEMapLE K (show p' ≤ p by omega)).f n)
        (isIso_stupidTruncLEMapLE_f_of_ne K p p' hp n hn) := by
  simp only [stupidTruncLESplitting, dite_eq_right hn, ShortComplex.Splitting.ofIsZeroOfIsIso]
  rfl

/-- Away from degree `p` the retraction of the canonical splitting vanishes. -/
theorem stupidTruncLESplitting_r_of_ne (p p' : ℤ) (hp : p' + 1 = p) (n : ℤ) (hn : n ≠ p) :
    (stupidTruncLESplitting K p p' hp n).r = 0 := by
  simp only [stupidTruncLESplitting, dite_eq_right hn, ShortComplex.Splitting.ofIsZeroOfIsIso]

end Splitting

section Triangles

variable {C : Type*} [Category* C] [Abelian C] [HasDerivedCategory C] (K : CochainComplex C ℤ)

/-- **The triangle `Kᵖ[-p] ⟶ σ^{≤p}K ⟶ σ^{≤p'}K ⟶ Kᵖ[-p][1]`** of the derived category, for
`p' + 1 = p`, attached to the canonical degreewise splitting: its third morphism is the image of
the cochain map `CochainComplex.homOfDegreewiseSplit`, built from the differential of `K`. -/
abbrev stupidTruncLESplitTriangle (p p' : ℤ) (hp : p' + 1 = p) :
    Pretriangulated.Triangle (DerivedCategory C) :=
  DerivedCategory.Qh.mapTriangle.obj (CochainComplex.trianglehOfDegreewiseSplit
    (stupidTruncLEShortComplex K p p' hp) (stupidTruncLESplitting K p p' hp))

/-- The triangle `stupidTruncLESplitTriangle K p p' hp` is distinguished. -/
theorem stupidTruncLESplitTriangle_distinguished (p p' : ℤ) (hp : p' + 1 = p) :
    stupidTruncLESplitTriangle K p p' hp ∈ distTriang (DerivedCategory C) :=
  DerivedCategory.Qh.map_distinguished _
    (CochainComplex.trianglehOfDegreewiseSplit_distinguished _ _)

/-- **The triangle `σ^{≥p+1}K ⟶ σ^{≥p}K ⟶ Kᵖ[-p] ⟶ σ^{≥p+1}K[1]`** of the derived category
attached to the canonical degreewise splitting: its third morphism is the image of the cochain
map `CochainComplex.homOfDegreewiseSplit`, built from the differential of `K`. -/
abbrev stupidTruncGESplitTriangle (p : ℤ) : Pretriangulated.Triangle (DerivedCategory C) :=
  DerivedCategory.Qh.mapTriangle.obj (CochainComplex.trianglehOfDegreewiseSplit
    (stupidTruncGEShortComplex K p) (stupidTruncGESplitting K p))

/-- The triangle `stupidTruncGESplitTriangle K p` is distinguished. -/
theorem stupidTruncGESplitTriangle_distinguished (p : ℤ) :
    stupidTruncGESplitTriangle K p ∈ distTriang (DerivedCategory C) :=
  DerivedCategory.Qh.map_distinguished _
    (CochainComplex.trianglehOfDegreewiseSplit_distinguished _ _)

end Triangles

section QTriangles

variable {C : Type*} [Category* C] [Abelian C] [HasDerivedCategory C]

/-- **The image under `Q` of the triangle of a degreewise split short exact sequence of cochain
complexes is distinguished**: it is isomorphic, through `quotient ⋙ Qh ≅ Q`, to the image under
`Qh` of the corresponding distinguished triangle of the homotopy category. -/
theorem _root_.CochainComplex.Q_mapTriangle_triangleOfDegreewiseSplit_distinguished
    (S : ShortComplex (CochainComplex C ℤ)) (σ : ∀ n, (S.map (eval C _ n)).Splitting) :
    DerivedCategory.Q.mapTriangle.obj (CochainComplex.triangleOfDegreewiseSplit S σ) ∈
      distTriang (DerivedCategory C) :=
  Pretriangulated.isomorphic_distinguished _ (DerivedCategory.Qh.map_distinguished _
      (CochainComplex.trianglehOfDegreewiseSplit_distinguished S σ)) _
    ((Functor.mapTriangleIso (DerivedCategory.quotientCompQhIso C)).symm.app _ ≪≫
      (Functor.mapTriangleCompIso _ _).app _)

variable (K : CochainComplex C ℤ)

/-- **The triangle `Kᵖ[-p] ⟶ σ^{≤p}K ⟶ σ^{≤p'}K ⟶ Kᵖ[-p][1]` with vertices `Q` of complexes**, for
`p' + 1 = p`: the image under `Q` of the triangle of cochain complexes attached to the canonical
degreewise splitting. -/
abbrev stupidTruncLESplitTriangleQ (p p' : ℤ) (hp : p' + 1 = p) :
    Pretriangulated.Triangle (DerivedCategory C) :=
  DerivedCategory.Q.mapTriangle.obj (CochainComplex.triangleOfDegreewiseSplit
    (stupidTruncLEShortComplex K p p' hp) (stupidTruncLESplitting K p p' hp))

/-- The triangle `stupidTruncLESplitTriangleQ K p p' hp` is distinguished. -/
theorem stupidTruncLESplitTriangleQ_distinguished (p p' : ℤ) (hp : p' + 1 = p) :
    stupidTruncLESplitTriangleQ K p p' hp ∈ distTriang (DerivedCategory C) :=
  CochainComplex.Q_mapTriangle_triangleOfDegreewiseSplit_distinguished _ _

/-- **The triangle `σ^{≥p+1}K ⟶ σ^{≥p}K ⟶ Kᵖ[-p] ⟶ σ^{≥p+1}K[1]` with vertices `Q` of
complexes**: the image under `Q` of the triangle of cochain complexes attached to the canonical
degreewise splitting. -/
abbrev stupidTruncGESplitTriangleQ (p : ℤ) : Pretriangulated.Triangle (DerivedCategory C) :=
  DerivedCategory.Q.mapTriangle.obj (CochainComplex.triangleOfDegreewiseSplit
    (stupidTruncGEShortComplex K p) (stupidTruncGESplitting K p))

/-- The triangle `stupidTruncGESplitTriangleQ K p` is distinguished. -/
theorem stupidTruncGESplitTriangleQ_distinguished (p : ℤ) :
    stupidTruncGESplitTriangleQ K p ∈ distTriang (DerivedCategory C) :=
  CochainComplex.Q_mapTriangle_triangleOfDegreewiseSplit_distinguished _ _

end QTriangles

end

end StacksDraft.StupidTruncation

end
