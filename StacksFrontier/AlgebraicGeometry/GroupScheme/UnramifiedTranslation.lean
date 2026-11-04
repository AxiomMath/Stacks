module

public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
public import StacksFrontier.AlgebraicGeometry.Morphisms.Unramified.BaseChangeLocus
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The unramified locus of a homomorphism of group schemes

A homomorphism of group schemes `f : G ⟶ H` over a base `S`, locally of finite type, which is
unramified at every point of the unit section of `G` is unramified at every point of `G`. This
is the "translation" step of the proof of [Stacks, Tag 0BFH], carried out without rational
points, so that it holds over any base and in particular over any field.

## Main results

* `AlgebraicGeometry.isPullback_grpHomGraph_left`: the morphism `(g, x) ↦ (g, f x)` from
  `G × G` to `G × H` is the base change of `f` along the second projection `G × H ⟶ H`.
* `AlgebraicGeometry.grpShear_comp_grpHomGraph`: it intertwines the shear
  `(g, x) ↦ (g, g x)` of `G × G` with the automorphism `(g, h) ↦ (g, f(g) h)` of `G × H`.
* `AlgebraicGeometry.unramifiedAt_of_forall_unramifiedAt_unit`: **the conclusion**.

## Implementation notes

The argument uses only that the unramified locus commutes with arbitrary base change, in both
directions (`AlgebraicGeometry.unramifiedAt_iff_of_isPullback`). A point `x` of `G` is the second
coordinate of the image under the shear of a point `z` of `G × G` lying over `(x, e)`, where `e`
is the unit. The point `z` lies over the unit in the second factor, so the base change of `f` is
unramified at `z`; the shear and its partner on `G × H` are isomorphisms which intertwine the
base change of `f` with itself, so the base change is unramified at the image of `z`; and that
image lies over `x`.

Multiplicativity of `f` is the hypothesis
`(fst G G * snd G G) ≫ f = (fst G G ≫ f) * (snd G G ≫ f)` in the group `G ⊗ G ⟶ H`, rather than
`IsMonHom f`, because it is what the computation uses and is immediate for multiplication by an
integer on a commutative group object.

## References

* [Stacks Project, Tag 0BFH](https://stacks.math.columbia.edu/tag/0BFH)
* [Stacks Project, Tag 0475](https://stacks.math.columbia.edu/tag/0475)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

universe u

namespace AlgebraicGeometry

variable {S : Scheme.{u}} {G H : Over S} [GrpObj G] [GrpObj H] (f : G ⟶ H)

/-- The morphism `G × G ⟶ G × H`, `(g, x) ↦ (g, f x)`. -/
noncomputable abbrev grpHomGraph : G ⊗ G ⟶ G ⊗ H := lift (fst G G) (snd G G ≫ f)

/-- The shear `G × G ⟶ G × G`, `(g, x) ↦ (g, g x)`. -/
noncomputable abbrev grpShear : G ⊗ G ⟶ G ⊗ G := lift (fst G G) (fst G G * snd G G)

/-- The shear `G × H ⟶ G × H`, `(g, h) ↦ (g, f(g) h)`. -/
noncomputable abbrev grpHomShear : G ⊗ H ⟶ G ⊗ H := lift (fst G H) ((fst G H ≫ f) * snd G H)

omit [GrpObj H] in
/-- The shear `(g, x) ↦ (g, g x)` is an isomorphism, with inverse `(g, x) ↦ (g, g⁻¹ x)`. -/
theorem isIso_grpShear : IsIso (grpShear (G := G)) := by
  refine ⟨lift (fst G G) ((fst G G)⁻¹ * snd G G), ?_, ?_⟩
  · apply CartesianMonoidalCategory.hom_ext
    · simp
    · simp [MonObj.comp_mul, GrpObj.comp_inv]
  · apply CartesianMonoidalCategory.hom_ext
    · simp
    · simp [MonObj.comp_mul]

omit [GrpObj G] in
/-- The morphism `(g, h) ↦ (g, f(g) h)` is an isomorphism, with inverse
`(g, h) ↦ (g, f(g)⁻¹ h)`. -/
theorem isIso_grpHomShear : IsIso (grpHomShear f) := by
  refine ⟨lift (fst G H) ((fst G H ≫ f)⁻¹ * snd G H), ?_, ?_⟩
  · apply CartesianMonoidalCategory.hom_ext
    · simp
    · simp [MonObj.comp_mul, GrpObj.comp_inv]
  · apply CartesianMonoidalCategory.hom_ext
    · simp
    · simp [MonObj.comp_mul]

/-- For a multiplicative `f`, the shear of `G × G` followed by `(g, x) ↦ (g, f x)` is
`(g, x) ↦ (g, f x)` followed by `(g, h) ↦ (g, f(g) h)`. -/
theorem grpShear_comp_grpHomGraph
    (hf : (fst G G * snd G G) ≫ f = (fst G G ≫ f) * (snd G G ≫ f)) :
    grpShear ≫ grpHomGraph f = grpHomGraph f ≫ grpHomShear f := by
  apply CartesianMonoidalCategory.hom_ext
  · simp
  · simp [MonObj.comp_mul, hf]

omit [GrpObj G] [GrpObj H] in
/-- The graph map is the base change of `f` along the second projection `G × H ⟶ H`. -/
theorem isPullback_grpHomGraph_left :
    IsPullback (snd G G).left (grpHomGraph f).left f.left (snd G H).left := by
  refine IsPullback.flip (IsPullback.of_right (h₁₂ := pullback.fst G.hom H.hom)
    (v₁₂ := pullback.snd G.hom H.hom) (h₂₂ := H.hom) (v₁₃ := G.hom) ?_ ?_
    (IsPullback.of_hasPullback G.hom H.hom))
  · have h : (grpHomGraph f).left ≫ pullback.fst G.hom H.hom = pullback.fst G.hom G.hom := by
      show (grpHomGraph f ≫ fst G H).left = _
      simp
    rw [h, Over.w f]
    exact IsPullback.of_hasPullback G.hom G.hom
  · show (grpHomGraph f ≫ snd G H).left = (snd G G ≫ f).left
    simp

/-- **A homomorphism of group schemes which is unramified along the unit section is
unramified.** Let `f : G ⟶ H` be a morphism of group schemes over `S`, locally of finite type,
which is multiplicative. If `f` is unramified at every point of the unit section of `G`, then it
is unramified at every point of `G`. -/
@[sga "3 VIB 1.3" "(i)⇒(ii), special case"]
theorem unramifiedAt_of_forall_unramifiedAt_unit [LocallyOfFiniteType f.left]
    (hf : (fst G G * snd G G) ≫ f = (fst G G ≫ f) * (snd G G ≫ f))
    (h : ∀ s : S, UnramifiedAt f.left ((η[G]).left s)) (x : G.left) :
    UnramifiedAt f.left x := by
  have sq := isPullback_grpHomGraph_left f
  have : LocallyOfFiniteType (grpHomGraph f).left :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback sq ‹LocallyOfFiniteType f.left›
  let z := (lift (𝟙 G) (toUnit G ≫ η[G])).left x
  have hz : (snd G G).left z = (η[G]).left (G.hom x) := by
    show (lift (𝟙 G) (toUnit G ≫ η[G]) ≫ snd G G).left x = _
    rw [lift_snd, Over.comp_left, Over.toUnit_left]
    rfl
  have h1 : UnramifiedAt (grpHomGraph f).left z :=
    (unramifiedAt_iff_of_isPullback sq z).1 (hz ▸ h (G.hom x))
  have := isIso_grpShear (G := G)
  have := isIso_grpHomShear f
  have : IsIso (grpShear (G := G)).left :=
    (Over.forget S).map_isIso (grpShear (G := G))
  have : IsIso (grpHomShear f).left := (Over.forget S).map_isIso (grpHomShear f)
  have sq2 : IsPullback (grpShear (G := G)).left (grpHomGraph f).left (grpHomGraph f).left
      (grpHomShear f).left :=
    IsPullback.of_horiz_isIso ⟨by
      rw [← Over.comp_left, grpShear_comp_grpHomGraph f hf, Over.comp_left]⟩
  have h2 : UnramifiedAt (grpHomGraph f).left ((grpShear (G := G)).left z) :=
    (unramifiedAt_iff_of_isPullback sq2 z).2 h1
  have hσ : lift (𝟙 G) (toUnit G ≫ η[G]) ≫ grpShear = lift (𝟙 G) (𝟙 G) := by
    apply CartesianMonoidalCategory.hom_ext
    · simp
    · simp [MonObj.comp_mul, ← CategoryTheory.Hom.one_def]
  have hx : (snd G G).left ((grpShear (G := G)).left z) = x := by
    show (lift (𝟙 G) (toUnit G ≫ η[G]) ≫ grpShear ≫ snd G G).left x = x
    rw [← Category.assoc, hσ, lift_snd]
    rfl
  have h3 := (unramifiedAt_iff_of_isPullback sq _).2 h2
  rwa [hx] at h3

end AlgebraicGeometry
