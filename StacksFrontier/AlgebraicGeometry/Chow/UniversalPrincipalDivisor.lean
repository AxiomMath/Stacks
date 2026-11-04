module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
public import StacksFrontier.AlgebraicGeometry.Chow.FibreCycles.DisjointSections
public import StacksFrontier.AlgebraicGeometry.Chow.RationalFunctions
public import StacksFrontier.AlgebraicGeometry.Scheme.Glueing.ProjectiveLineProper

/-!
# The graph of a rational function in `X ×_S ℙ¹_S`

Let `f : X ⟶ S` and let `s` be a section of `𝒪_X` over an open `U ⊆ X`. Because the first
affine chart of the projective line is `Spec ℤ[T]`, the section `s` is the coordinate of a
morphism `U ⟶ 𝔸¹_S ⟶ ℙ¹_S` over `S`, and pairing it with the inclusion `U ⟶ X` gives the
*graph* `U ⟶ X ×_S ℙ¹_S`. The scheme-theoretic image `Y` of the graph is the closure of the
graph, and this file constructs it together with its two projections `p : Y ⟶ X`,
`q : Y ⟶ ℙ¹_S`, the open `p⁻¹(U) ⊆ Y`, and the pullbacks `Y₀ = q⁻¹D₀`, `Y_∞ = q⁻¹D_∞` of the
two distinguished divisors of `ℙ¹_S`.

The divisors themselves are the kernel ideal sheaves of the zero and the infinity section
`S ⟶ ℙ¹_S`; since `ℙ¹_S ⟶ S` is separated, those sections are closed immersions, so `D₀` and
`D_∞` are genuinely the images of the sections and each is isomorphic to `S`.

Tag 02RQ asserts, for `X` integral locally of finite type over a Chow base and `s` a unit
section on a dense open, that `p` is proper, that it restricts to an isomorphism over `U`, that
the pullbacks of `D₀` and `D_∞` along `q` are defined, and that the resulting cycles compute
the principal divisor `div(s) = [Y₀] - [Y_∞]` on `Y` and, after proper pushforward along `p`,
on `X`. What is proved here is the geometry those statements are about, together with parts (1)
and (2). Part (1) holds for an arbitrary section of an arbitrary open, because `Y` is closed in
`X ×_S ℙ¹_S` and `X ×_S ℙ¹_S ⟶ X` is proper, being a base change of `ℙ¹_ℤ ⟶ Spec ℤ`. Part (2)
is proved here for `U ⟶ X` quasi-compact, which is what makes `Y` the *closure* of the graph
rather than a larger closed subscheme, and which holds in a Chow situation; see the
implementation notes.

## Main definitions

* `Stacks.Chow.lineConstantSection`: the section `S ⟶ ℙ¹_S` cut out by an integral point of
  `ℙ¹_ℤ`, with `Stacks.Chow.lineZeroSection` and `Stacks.Chow.lineInfinitySection` its two
  distinguished instances. These are the sections of `ℙ¹_S` over `S`; the sections of
  `X ×_S ℙ¹_S` over `X` of `Stacks.Chow.FibreCycles` are their pullbacks, by
  `Stacks.Chow.zeroSection_comp_snd`.
* `Stacks.AlgebraicGeometry.GenericPointDecomposition.affineLineOver`, `Stacks.Chow.affineChart`
  and `Stacks.Chow.affineCoordinate`: the affine line `𝔸¹_S`, its canonical open immersion into
  `ℙ¹_S`, and its coordinate `T₁/T₀`.
* `Stacks.Chow.lineZeroDivisor` and `Stacks.Chow.lineInfinityDivisor`: the divisors
  `D₀, D_∞ ⊆ ℙ¹_S`, as the kernel ideal sheaves of the two sections.
* `Stacks.Chow.sectionToLine`: the morphism `U ⟶ ℙ¹_S` whose coordinate is a given section,
  and `Stacks.Chow.sectionGraph` its graph in `X ×_S ℙ¹_S`.
* `Stacks.Chow.graphClosure`: the closure `Y` of that graph, with its projections
  `Stacks.Chow.graphProjection` to `X` and `Stacks.Chow.graphLineProjection` to `ℙ¹_S`, and
  `Stacks.Chow.graphZeroFiber`, `Stacks.Chow.graphInfinityFiber` the pullbacks `Y₀`, `Y_∞`.
* `Stacks.Chow.graphRationalFunction`: the rational function on `Y` obtained from a unit
  section on `U`, on the open `p⁻¹(U)` where that open is dense.

## Main results

* `Stacks.Chow.isProper_relativeProjectiveLine_over` and
  `Stacks.Chow.isProper_projectiveLineProduct_fst`: `ℙ¹_S ⟶ S` and `X ×_S ℙ¹_S ⟶ X` are
  proper.
* `Stacks.Chow.isOpenImmersion_affineChart`: `𝔸¹_S ⟶ ℙ¹_S` is an open immersion, being a base
  change of the chart `𝔸¹_ℤ ⟶ ℙ¹_ℤ`.
* `Stacks.Chow.isClosedImmersion_lineConstantSection`: a constant section of `ℙ¹_S ⟶ S` is a
  closed immersion, and `Stacks.Chow.isIso_lineZeroDivisor_over`,
  `Stacks.Chow.isIso_lineInfinityDivisor_over`: consequently `D₀ ⟶ S` and `D_∞ ⟶ S` are
  isomorphisms.
* `Stacks.Chow.sectionToAffineLine_appTop_affineCoordinate`: the coordinate of the morphism
  `U ⟶ 𝔸¹_S` attached to a section is that section. This is what makes `sectionToLine` the
  morphism Tag 02RQ asks for rather than some other map to `ℙ¹_S`.
* `Stacks.Chow.graphProjection_isProper`: **part (1) of Tag 02RQ**, the projection `Y ⟶ X` is
  proper.
* `Stacks.Chow.isIso_graphProjection_restrict`: for `U ⟶ X` quasi-compact, the restriction
  `p⁻¹(U) ⟶ U` is an isomorphism; via `Stacks.Chow.isIso_graphRestrictLift`, which identifies
  `U` with `p⁻¹(U)`. Part (2) of Tag 02RQ in a Chow situation, where the quasi-compactness is
  automatic, is `Stacks.Chow.isIso_graphProjection_morphismRestrict`.
* `AlgebraicGeometry.ker_toImage_eq_bot`: for a quasi-compact morphism, the map onto its
  scheme-theoretic image has trivial kernel ideal sheaf. This is a general statement that
  Mathlib does not have; it is the input to part (2).
* `Stacks.Chow.coe_support_lineZeroDivisor`,
  `Stacks.Chow.disjoint_support_lineZeroDivisor_lineInfinityDivisor` and their fibre
  counterparts: the supports of `D₀`, `D_∞`, `Y₀` and `Y_∞`, and the disjointness of each
  pair.
* `Stacks.Chow.lineInfinityDivisor_ideal_comap_affineChart`: `D_∞` is cut out by the unit
  ideal on the affine chart, i.e. it is disjoint from it.
* `Stacks.Chow.locallyOfFiniteType_graphBaseMorphism`, `Stacks.Chow.dense_graphPreimage` and
  `Stacks.Chow.isIntegral_graphClosure`: the facts about `Y` that parts (4)-(6) of the tag
  quantify over — `Y` is locally of finite type over the base, `p⁻¹(U)` is dense in `Y`, and
  `Y` is integral when `X` is and `U` is dense.

## Implementation notes

The model of the relative projective line is the glued one, `ℙ¹_S = S ×_{Spec ℤ} ℙ¹_ℤ` with
`ℙ¹_ℤ` the two-chart gluing of Tag 01JE, as constructed in
`StacksFrontier/AlgebraicGeometry/Chow/FibreCycles.lean`. This is the model every neighbouring
chapter-42 statement (Tags 02S4, 02S5, 02S6) is written against, and the one Tag 02RQ needs:
nothing in the chapter uses the `Proj` model of the projective line, and no comparison between
the two models is required for any statement here.

`Y` is the scheme-theoretic image `Scheme.Hom.image` of the graph morphism. For `X` integral
the graph is reduced, so its scheme-theoretic image is its closure, which is the `Y` of the
source.

The constructions are stated for an arbitrary section of an arbitrary open; the integrality of
`X`, the density of `U` and the invertibility of the section are needed only from part (3)
onwards. In particular part (1) holds at that generality.

Part (2) is proved here for `U ⟶ X` quasi-compact. Every statement identifying `Scheme.Hom.ker`
with the sectionwise kernel — `Scheme.Hom.ker_apply`, `Scheme.Hom.support_ker`,
`Scheme.Hom.toImage_app_injective`, `AlgebraicGeometry.ker_morphismRestrict_eq_comap` — assumes the
morphism is quasi-compact, and without it `Scheme.Hom.image` need not be the closure of the range.
In a Chow situation the hypothesis is automatic, `X` being locally of finite type over a locally
Noetherian base, so that every open of `X` has quasi-compact inclusion (Tag 01OX); the statements
of Tag 02RQ in that situation are in
`StacksFrontier.AlgebraicGeometry.Chow.UniversalPrincipalDivisorCycles.GraphConstruction`. From the
hypothesis, `Stacks.Chow.quasiCompact_sectionGraph` derives quasi-compactness of the graph morphism
itself.

Properness of `p` is *not* proved by exhibiting a valuative criterion: the projection
`X ×_S ℙ¹_S ⟶ X` is a base change of `ℙ¹_ℤ ⟶ Spec ℤ`, whose properness is
`AlgebraicGeometry.projectiveLine_isProper`, and `Y ⟶ X ×_S ℙ¹_S` is a closed immersion, hence
finite, hence proper.

## References

* [Stacks Project, Tag 02RQ](https://stacks.math.columbia.edu/tag/02RQ)
* [Stacks Project, Tag 02S5](https://stacks.math.columbia.edu/tag/02S5)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.Chow

/-! ### Properness of the relative projective line -/

/-- The relative projective line is proper over its base. -/
instance isProper_relativeProjectiveLine_over (S : Scheme.{u}) :
    IsProper (relativeProjectiveLine S ↘ S) := by
  rw [relativeProjectiveLine_over_hom]
  infer_instance

/-- The family `X ×_S ℙ¹_S` is proper over `X`. -/
instance isProper_projectiveLineProduct_fst {X S : Scheme.{u}} (f : X ⟶ S) :
    IsProper (pullback.fst f (relativeProjectiveLine S ↘ S)) :=
  inferInstance

/-! ### The sections of `ℙ¹_S` over `S` -/

/-- The section `S ⟶ ℙ¹_S` determined by an integral point `e` of `ℙ¹_ℤ`. -/
def lineConstantSection (S : Scheme.{u})
    (e : (⊤_ Scheme.{u}) ⟶ projectiveLine (ULift.{u} ℤ)) :
    S ⟶ relativeProjectiveLine S :=
  pullback.lift (𝟙 S) (terminal.from S ≫ e) (by simp)

/-- A constant section really is a section of `ℙ¹_S ⟶ S`. -/
@[simp]
theorem lineConstantSection_comp (S : Scheme.{u})
    (e : (⊤_ Scheme.{u}) ⟶ projectiveLine (ULift.{u} ℤ)) :
    lineConstantSection S e ≫ (relativeProjectiveLine S ↘ S) = 𝟙 S := by
  show lineConstantSection S e ≫ pullback.fst _ _ = _
  exact pullback.lift_fst _ _ _

/-- The zero section `S ⟶ ℙ¹_S`. -/
abbrev lineZeroSection (S : Scheme.{u}) : S ⟶ relativeProjectiveLine S :=
  lineConstantSection S integralZeroSection

/-- The infinity section `S ⟶ ℙ¹_S`. -/
abbrev lineInfinitySection (S : Scheme.{u}) : S ⟶ relativeProjectiveLine S :=
  lineConstantSection S integralInfinitySection

/-- The zero section is a section of `ℙ¹_S ⟶ S`. -/
@[simp]
theorem lineZeroSection_comp (S : Scheme.{u}) :
    lineZeroSection S ≫ (relativeProjectiveLine S ↘ S) = 𝟙 S :=
  lineConstantSection_comp S _

/-- The infinity section is a section of `ℙ¹_S ⟶ S`. -/
@[simp]
theorem lineInfinitySection_comp (S : Scheme.{u}) :
    lineInfinitySection S ≫ (relativeProjectiveLine S ↘ S) = 𝟙 S :=
  lineConstantSection_comp S _

/-- A constant section of `X ×_S ℙ¹_S ⟶ X` projects to `ℙ¹_S` as `f` followed by the constant
section of `ℙ¹_S ⟶ S`. -/
private theorem constantSection_comp_snd {X S : Scheme.{u}} (f : X ⟶ S)
    (e : (⊤_ Scheme.{u}) ⟶ projectiveLine (ULift.{u} ℤ)) :
    constantSection f e ≫ pullback.snd f (relativeProjectiveLine S ↘ S) =
      f ≫ lineConstantSection S e := by
  rw [constantSection, pullback.lift_snd]
  refine pullback.hom_ext ?_ ?_
  · rw [pullback.lift_fst, Category.assoc, lineConstantSection, pullback.lift_fst,
      Category.comp_id]
  · rw [pullback.lift_snd, Category.assoc, lineConstantSection, pullback.lift_snd]
    simp

/-- The zero section of `X ×_S ℙ¹_S ⟶ X` is the base change of the zero section of
`ℙ¹_S ⟶ S`: projecting it to `ℙ¹_S` gives `f` followed by the zero section. -/
theorem zeroSection_comp_snd {X S : Scheme.{u}} (f : X ⟶ S) :
    zeroSection f ≫ pullback.snd f (relativeProjectiveLine S ↘ S) =
      f ≫ lineZeroSection S :=
  constantSection_comp_snd f _

/-- The infinity section of `X ×_S ℙ¹_S ⟶ X` is the base change of the infinity section of
`ℙ¹_S ⟶ S`. -/
theorem infinitySection_comp_snd {X S : Scheme.{u}} (f : X ⟶ S) :
    infinitySection f ≫ pullback.snd f (relativeProjectiveLine S ↘ S) =
      f ≫ lineInfinitySection S :=
  constantSection_comp_snd f _

/-- A constant section of `ℙ¹_S ⟶ S` is a closed immersion: it is a section of a separated
morphism. -/
instance isClosedImmersion_lineConstantSection (S : Scheme.{u})
    (e : (⊤_ Scheme.{u}) ⟶ projectiveLine (ULift.{u} ℤ)) :
    IsClosedImmersion (lineConstantSection S e) := by
  have hsep : IsSeparated (relativeProjectiveLine S ↘ S) := inferInstance
  have : IsClosedImmersion (lineConstantSection S e ≫ (relativeProjectiveLine S ↘ S)) := by
    rw [lineConstantSection_comp]
    infer_instance
  exact IsClosedImmersion.of_comp _ (relativeProjectiveLine S ↘ S)

/-! ### The affine chart of `ℙ¹_S` and its coordinate -/

/-- The affine line `𝔸¹_S` over `S`, as the base change of the coordinate chart of `ℙ¹_ℤ`. -/
abbrev affineLineOver (S : Scheme.{u}) : Scheme.{u} :=
  pullback (terminal.from S) (terminal.from (Spec (.of (Polynomial (ULift.{u} ℤ)))))

/-- The canonical morphism `𝔸¹_S ⟶ ℙ¹_S`, the base change of the first chart of the two-chart
gluing of `ℙ¹_ℤ`. -/
def affineChart (S : Scheme.{u}) : affineLineOver S ⟶ relativeProjectiveLine S :=
  pullback.lift (pullback.fst _ _)
    (pullback.snd _ _ ≫ projectiveLineXChart (ULift.{u} ℤ)) (by simp)

/-- The affine chart lies over `S`. -/
@[simp]
theorem affineChart_comp (S : Scheme.{u}) :
    affineChart S ≫ (relativeProjectiveLine S ↘ S) = pullback.fst _ _ := by
  show affineChart S ≫ pullback.fst _ _ = _
  exact pullback.lift_fst _ _ _

/-- The affine chart is the base change of the chart `𝔸¹_ℤ ⟶ ℙ¹_ℤ` along the projection of
`ℙ¹_S` to `ℙ¹_ℤ`. -/
theorem isPullback_affineChart (S : Scheme.{u}) :
    IsPullback (affineChart S)
      (pullback.snd (terminal.from S) (terminal.from (Spec (.of (Polynomial (ULift.{u} ℤ))))))
      (pullback.snd (terminal.from S) (terminal.from (projectiveLine (ULift.{u} ℤ))))
      (projectiveLineXChart (ULift.{u} ℤ)) := by
  refine IsPullback.of_right (h₁₂ := pullback.fst (terminal.from S)
      (terminal.from (projectiveLine (ULift.{u} ℤ)))) ?_ (pullback.lift_snd _ _ _)
    (IsPullback.of_hasPullback _ _)
  rw [show affineChart S ≫ pullback.fst (terminal.from S)
      (terminal.from (projectiveLine (ULift.{u} ℤ))) = pullback.fst _ _ from affineChart_comp S,
    show projectiveLineXChart (ULift.{u} ℤ) ≫ terminal.from (projectiveLine (ULift.{u} ℤ)) =
      terminal.from (Spec (.of (Polynomial (ULift.{u} ℤ)))) from terminal.hom_ext _ _]
  exact IsPullback.of_hasPullback _ _

/-- The affine chart is an open immersion. -/
instance isOpenImmersion_affineChart (S : Scheme.{u}) : IsOpenImmersion (affineChart S) :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @IsOpenImmersion)
    (isPullback_affineChart S).flip inferInstance

/-- In a pullback square, the image of the first projection is the preimage of the image of the
second structure morphism. -/
private theorem range_eq_preimage_range_of_isPullback {P X Y Z : Scheme.{u}} {fst : P ⟶ X}
    {snd : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z} (h : IsPullback fst snd f g) :
    Set.range fst = f ⁻¹' Set.range g := by
  rw [← h.isoPullback_hom_fst, range_comp_scheme, (surjective_of_isIso h.isoPullback.hom).range_eq,
    Set.image_univ, Scheme.Pullback.range_fst]

/-- The image of the affine chart is the preimage of the first chart of `ℙ¹_ℤ`. -/
theorem range_affineChart (S : Scheme.{u}) :
    Set.range (affineChart S) =
      pullback.snd (terminal.from S) (terminal.from (projectiveLine (ULift.{u} ℤ))) ⁻¹'
        Set.range (projectiveLineXChart (ULift.{u} ℤ)) :=
  range_eq_preimage_range_of_isPullback (isPullback_affineChart S)

/-- The point `∞` of `ℙ¹_ℤ` does not lie on the first chart: it is the origin of the second
chart, and the coordinate of the first chart vanishes there. -/
theorem disjoint_range_integralInfinitySection_projectiveLineXChart :
    Disjoint (Set.range (integralInfinitySection.{u}))
      (Set.range (projectiveLineXChart (ULift.{u} ℤ))) := by
  rw [Set.disjoint_left]
  rintro p hp hx
  rw [range_integralInfinitySection] at hp
  obtain ⟨y, hy, rfl⟩ := hp
  exact notMem_range_ι_of_X_mem (ULift.{u} ℤ) _ _
    (fun h => projectiveLineXIndex_ne_projectiveLineYIndex (ULift.{u} ℤ) h.symm) y
    (X_mem_of_mem_range_specMap_evalRingHom_zero hy) hx

/-- The canonical coordinate `T₁/T₀` on `𝔸¹_S`, pulled back from the coordinate of
`Spec ℤ[T]`. -/
def affineCoordinate (S : Scheme.{u}) : Γ(affineLineOver S, ⊤) :=
  (pullback.snd (terminal.from S)
      (terminal.from (Spec (.of (Polynomial (ULift.{u} ℤ)))))).appTop
    ((Scheme.ΓSpecIso (.of (Polynomial (ULift.{u} ℤ)))).inv Polynomial.X)

/-! ### The two distinguished divisors of `ℙ¹_S` -/

/-- The zero divisor `D₀ ⊆ ℙ¹_S`: the closed subscheme cut out by the kernel ideal sheaf of
the zero section, equivalently the scheme-theoretic image of that section. -/
@[stacks 0F93 "the divisor D₀ ⊆ ℙ¹_S"]
def lineZeroDivisor (S : Scheme.{u}) : (relativeProjectiveLine S).IdealSheafData :=
  (lineZeroSection S).ker

/-- The infinity divisor `D_∞ ⊆ ℙ¹_S`: the closed subscheme cut out by the kernel ideal sheaf
of the infinity section. -/
@[stacks 0F93 "the divisor D₀ ⊆ ℙ¹_S"]
def lineInfinityDivisor (S : Scheme.{u}) : (relativeProjectiveLine S).IdealSheafData :=
  (lineInfinitySection S).ker

/-- A constant section of `ℙ¹_S ⟶ S` is the base change of the corresponding integral point of
`ℙ¹_ℤ` along the projection of `ℙ¹_S` to `ℙ¹_ℤ`. -/
theorem isPullback_lineConstantSection (S : Scheme.{u})
    (e : (⊤_ Scheme.{u}) ⟶ projectiveLine (ULift.{u} ℤ)) :
    IsPullback (lineConstantSection S e) (terminal.from S)
      (pullback.snd (terminal.from S) (terminal.from (projectiveLine (ULift.{u} ℤ)))) e := by
  refine IsPullback.of_right (h₁₂ := pullback.fst (terminal.from S)
      (terminal.from (projectiveLine (ULift.{u} ℤ)))) ?_ (pullback.lift_snd _ _ _)
    (IsPullback.of_hasPullback _ _)
  rw [show lineConstantSection S e ≫ pullback.fst (terminal.from S)
      (terminal.from (projectiveLine (ULift.{u} ℤ))) = 𝟙 S from lineConstantSection_comp S e,
    show e ≫ terminal.from (projectiveLine (ULift.{u} ℤ)) = 𝟙 (⊤_ Scheme.{u}) from
      terminal.hom_ext _ _]
  exact IsPullback.of_horiz_isIso ⟨terminal.hom_ext _ _⟩

/-- The image of a constant section of `ℙ¹_S ⟶ S` is the preimage of the image of the
corresponding integral point of `ℙ¹_ℤ`. -/
theorem range_lineConstantSection (S : Scheme.{u})
    (e : (⊤_ Scheme.{u}) ⟶ projectiveLine (ULift.{u} ℤ)) :
    Set.range (lineConstantSection S e) =
      pullback.snd (terminal.from S) (terminal.from (projectiveLine (ULift.{u} ℤ))) ⁻¹'
        Set.range e :=
  range_eq_preimage_range_of_isPullback (isPullback_lineConstantSection S e)

/-- The zero and the infinity section of `ℙ¹_S ⟶ S` have disjoint images. -/
theorem disjoint_range_lineZeroSection_lineInfinitySection (S : Scheme.{u}) :
    Disjoint (Set.range (lineZeroSection S)) (Set.range (lineInfinitySection S)) := by
  rw [lineZeroSection, lineInfinitySection, range_lineConstantSection,
    range_lineConstantSection]
  exact Disjoint.preimage _ disjoint_range_integralZeroSection_integralInfinitySection

/-- The support of the kernel of a closed immersion is its image. -/
private theorem coe_support_ker_of_isClosedImmersion {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsClosedImmersion f] : (f.ker.support : Set Y) = Set.range f := by
  rw [Scheme.Hom.support_ker, f.isClosedEmbedding.isClosed_range.closure_eq]

/-- The support of `D₀` is the image of the zero section. -/
@[simp]
theorem coe_support_lineZeroDivisor (S : Scheme.{u}) :
    ((lineZeroDivisor S).support : Set (relativeProjectiveLine S)) =
      Set.range (lineZeroSection S) := by
  exact coe_support_ker_of_isClosedImmersion _

/-- The support of `D_∞` is the image of the infinity section. -/
@[simp]
theorem coe_support_lineInfinityDivisor (S : Scheme.{u}) :
    ((lineInfinityDivisor S).support : Set (relativeProjectiveLine S)) =
      Set.range (lineInfinitySection S) := by
  exact coe_support_ker_of_isClosedImmersion _

/-- `D₀` and `D_∞` are disjoint closed subschemes of `ℙ¹_S`. -/
theorem disjoint_support_lineZeroDivisor_lineInfinityDivisor (S : Scheme.{u}) :
    Disjoint ((lineZeroDivisor S).support : Set (relativeProjectiveLine S))
      ((lineInfinityDivisor S).support : Set (relativeProjectiveLine S)) := by
  rw [coe_support_lineZeroDivisor, coe_support_lineInfinityDivisor]
  exact disjoint_range_lineZeroSection_lineInfinitySection S

/-- `D_∞` does not meet the affine chart, so it pulls back to the empty closed subscheme
of `𝔸¹_S`. -/
theorem comap_lineInfinityDivisor_affineChart (S : Scheme.{u}) :
    (lineInfinityDivisor S).comap (affineChart S) = ⊤ := by
  have hc : affineChart S ≫ pullback.snd (terminal.from S)
      (terminal.from (projectiveLine (ULift.{u} ℤ))) =
      pullback.snd (terminal.from S)
        (terminal.from (Spec (.of (Polynomial (ULift.{u} ℤ))))) ≫
        projectiveLineXChart (ULift.{u} ℤ) := pullback.lift_snd _ _ _
  rw [← Scheme.IdealSheafData.support_eq_bot_iff]
  apply SetLike.coe_injective
  rw [Scheme.IdealSheafData.support_comap, TopologicalSpace.Closeds.coe_preimage,
    coe_support_lineInfinityDivisor, range_lineConstantSection]
  refine (Set.eq_empty_iff_forall_notMem.2 ?_).trans rfl
  intro x hx
  rw [Set.mem_preimage, Set.mem_preimage, ← Scheme.Hom.comp_apply, hc,
    Scheme.Hom.comp_apply] at hx
  exact Set.disjoint_right.mp
    disjoint_range_integralInfinitySection_projectiveLineXChart
    (Set.mem_range_self _) hx

/-- In the affine coordinate, `D_∞` is cut out by the unit ideal: the infinity divisor is
disjoint from the chart. -/
theorem lineInfinityDivisor_ideal_comap_affineChart (S : Scheme.{u})
    (V : (affineLineOver S).affineOpens) :
    ((lineInfinityDivisor S).comap (affineChart S)).ideal V = ⊤ := by
  rw [comap_lineInfinityDivisor_affineChart]
  rfl

/-- The image of a constant section of `ℙ¹_S ⟶ S`, as a closed subscheme, maps isomorphically
to `S`. -/
theorem isIso_lineConstantSection_ker_over (S : Scheme.{u})
    (e : (⊤_ Scheme.{u}) ⟶ projectiveLine (ULift.{u} ℤ)) :
    IsIso ((lineConstantSection S e).ker.subschemeι ≫ (relativeProjectiveLine S ↘ S)) := by
  have h : IsIso (lineConstantSection S e).toImage := inferInstance
  exact IsIso.of_isIso_fac_left (f := (lineConstantSection S e).toImage)
    (h := 𝟙 S) (by rw [← Category.assoc, Scheme.Hom.toImage_imageι, lineConstantSection_comp])

/-- `D₀ ⟶ S` is an isomorphism. -/
theorem isIso_lineZeroDivisor_over (S : Scheme.{u}) :
    IsIso ((lineZeroDivisor S).subschemeι ≫ (relativeProjectiveLine S ↘ S)) :=
  isIso_lineConstantSection_ker_over S _

/-- `D_∞ ⟶ S` is an isomorphism. -/
theorem isIso_lineInfinityDivisor_over (S : Scheme.{u}) :
    IsIso ((lineInfinityDivisor S).subschemeι ≫ (relativeProjectiveLine S ↘ S)) :=
  isIso_lineConstantSection_ker_over S _

/-! ### The morphism to `ℙ¹_S` attached to a section, and its graph -/

/-- The morphism `U ⟶ 𝔸¹_ℤ` whose coordinate is a given section of `U`. -/
def sectionChartHom {X : Scheme.{u}} (U : X.Opens) (s : Γ(X, U)) :
    U.toScheme ⟶ Spec (.of (Polynomial (ULift.{u} ℤ))) :=
  U.toScheme.toSpecΓ ≫ Spec.map (CommRingCat.ofHom
    (Polynomial.eval₂RingHom
      ((Int.castRingHom Γ(U.toScheme, ⊤)).comp ULift.ringEquiv.toRingHom)
      (U.topIso.inv s)))

/-- The morphism `U ⟶ 𝔸¹_S` over `S` whose coordinate is a given section of `U`. -/
def sectionToAffineLine {X S : Scheme.{u}} (sX : X ⟶ S) (U : X.Opens) (s : Γ(X, U)) :
    U.toScheme ⟶ affineLineOver S :=
  pullback.lift (U.ι ≫ sX) (sectionChartHom U s) (by simp)

/-- The coordinate of the morphism `U ⟶ 𝔸¹_S` attached to a section is that section. -/
theorem sectionToAffineLine_appTop_affineCoordinate {X S : Scheme.{u}} (sX : X ⟶ S)
    (U : X.Opens) (s : Γ(X, U)) :
    (sectionToAffineLine sX U s).appTop (affineCoordinate S) = U.topIso.inv s := by
  have h : (pullback.snd (terminal.from S)
        (terminal.from (Spec (.of (Polynomial (ULift.{u} ℤ)))))).appTop ≫
      (sectionToAffineLine sX U s).appTop =
      (Scheme.ΓSpecIso (.of (Polynomial (ULift.{u} ℤ)))).hom ≫
        CommRingCat.ofHom (Polynomial.eval₂RingHom
          ((Int.castRingHom Γ(U.toScheme, ⊤)).comp ULift.ringEquiv.toRingHom)
          (U.topIso.inv s)) := by
    rw [← Scheme.Hom.comp_appTop, sectionToAffineLine, pullback.lift_snd, sectionChartHom,
      Scheme.Hom.comp_appTop, Scheme.toSpecΓ_appTop]
    exact Scheme.ΓSpecIso_naturality _
  have h' := congrArg (fun m : _ ⟶ _ => (ConcreteCategory.hom m)
    ((Scheme.ΓSpecIso (.of (Polynomial (ULift.{u} ℤ)))).inv Polynomial.X)) h
  simpa [affineCoordinate] using h'

/-- The morphism `U ⟶ ℙ¹_S` determined by a section of `U`, through the affine chart. -/
def sectionToLine {X S : Scheme.{u}} (sX : X ⟶ S) (U : X.Opens) (s : Γ(X, U)) :
    U.toScheme ⟶ relativeProjectiveLine S :=
  sectionToAffineLine sX U s ≫ affineChart S

/-- The morphism `U ⟶ ℙ¹_S` determined by a section lies over `S`. -/
theorem sectionToLine_comp {X S : Scheme.{u}} (sX : X ⟶ S) (U : X.Opens) (s : Γ(X, U)) :
    sectionToLine sX U s ≫ (relativeProjectiveLine S ↘ S) = U.ι ≫ sX := by
  rw [sectionToLine, Category.assoc, affineChart_comp, sectionToAffineLine, pullback.lift_fst]

/-- The graph of the morphism `U ⟶ ℙ¹_S` determined by a section, inside `X ×_S ℙ¹_S`. -/
def sectionGraph {X S : Scheme.{u}} (sX : X ⟶ S) (U : X.Opens) (s : Γ(X, U)) :
    U.toScheme ⟶ projectiveLineProduct sX :=
  pullback.lift U.ι (sectionToLine sX U s) (sectionToLine_comp sX U s).symm

/-- `Y`, the closure of the graph of the morphism `U ⟶ ℙ¹_S` determined by a section, taken as
the scheme-theoretic image of the graph. -/
abbrev graphClosure {X S : Scheme.{u}} (sX : X ⟶ S) (U : X.Opens) (s : Γ(X, U)) : Scheme.{u} :=
  (sectionGraph sX U s).image

/-- The closed immersion `Y ⟶ X ×_S ℙ¹_S`. -/
abbrev graphClosureι {X S : Scheme.{u}} (sX : X ⟶ S) (U : X.Opens) (s : Γ(X, U)) :
    graphClosure sX U s ⟶ projectiveLineProduct sX :=
  (sectionGraph sX U s).imageι

/-- The morphism `U ⟶ Y` onto the graph. -/
abbrev graphInclusion {X S : Scheme.{u}} (sX : X ⟶ S) (U : X.Opens) (s : Γ(X, U)) :
    U.toScheme ⟶ graphClosure sX U s :=
  (sectionGraph sX U s).toImage

/-- The projection `p : Y ⟶ X`. -/
abbrev graphProjection {X S : Scheme.{u}} (sX : X ⟶ S) (U : X.Opens) (s : Γ(X, U)) :
    graphClosure sX U s ⟶ X :=
  graphClosureι sX U s ≫ pullback.fst sX (relativeProjectiveLine S ↘ S)

/-- The projection `q : Y ⟶ ℙ¹_S`. -/
abbrev graphLineProjection {X S : Scheme.{u}} (sX : X ⟶ S) (U : X.Opens) (s : Γ(X, U)) :
    graphClosure sX U s ⟶ relativeProjectiveLine S :=
  graphClosureι sX U s ≫ pullback.snd sX (relativeProjectiveLine S ↘ S)

/-- The structure morphism of `Y` over the base. -/
abbrev graphBaseMorphism {X S : Scheme.{u}} (sX : X ⟶ S) (U : X.Opens) (s : Γ(X, U)) :
    graphClosure sX U s ⟶ S :=
  graphProjection sX U s ≫ sX

/-- The open `p⁻¹(U) ⊆ Y`. -/
abbrev graphPreimage {X S : Scheme.{u}} (sX : X ⟶ S) (U : X.Opens) (s : Γ(X, U)) :
    (graphClosure sX U s).Opens :=
  (graphProjection sX U s) ⁻¹ᵁ U

/-- Density of `p⁻¹(U)` in `Y`: the hypothesis under which a section on `U` becomes a rational
function on `Y`. -/
abbrev GraphPreimageDense {X S : Scheme.{u}} (sX : X ⟶ S) (U : X.Opens) (s : Γ(X, U)) : Prop :=
  Dense ((graphPreimage sX U s : Set (graphClosure sX U s)))

/-- The graph is a section of `p` over `U`. -/
theorem graphInclusion_comp_graphProjection {X S : Scheme.{u}} (sX : X ⟶ S) (U : X.Opens)
    (s : Γ(X, U)) : graphInclusion sX U s ≫ graphProjection sX U s = U.ι := by
  show (sectionGraph sX U s).toImage ≫
      ((sectionGraph sX U s).imageι ≫ pullback.fst sX (relativeProjectiveLine S ↘ S)) = U.ι
  rw [← Category.assoc, Scheme.Hom.toImage_imageι, sectionGraph, pullback.lift_fst]

/-- **Part (1) of Stacks Project, Tag 02RQ.** The projection `p : Y ⟶ X` is proper. No
hypothesis on `X`, on `U` or on the section is needed: `Y` is closed in `X ×_S ℙ¹_S`, which is
proper over `X`. -/
@[stacks 02RQ "part (1): properness of the projection"]
theorem graphProjection_isProper {X S : Scheme.{u}} (sX : X ⟶ S) (U : X.Opens)
    (s : Γ(X, U)) : IsProper (graphProjection sX U s) := by
  show IsProper (graphClosureι sX U s ≫ pullback.fst sX (relativeProjectiveLine S ↘ S))
  infer_instance

/-! ### Part (2): the projection is an isomorphism over `U` -/

/-- The scheme-theoretic image of a quasi-compact morphism is cut out by exactly the kernel of
the morphism: the induced map onto the image has trivial kernel ideal sheaf. Equivalently, that
map is scheme-theoretically dominant. -/
theorem _root_.AlgebraicGeometry.ker_toImage_eq_bot {A B : Scheme.{u}} (f : A ⟶ B)
    [QuasiCompact f] : f.toImage.ker = ⊥ := by
  apply Scheme.IdealSheafData.ext
  funext V
  rw [Scheme.Hom.ker_apply, Scheme.IdealSheafData.ideal_bot, Pi.bot_apply,
    ← RingHom.injective_iff_ker_eq_bot]
  exact TopCat.Presheaf.app_injective_of_stalkFunctor_map_injective
    (F := f.image.sheaf) f.toImage.c (V : f.image.Opens)
    (fun x _ => f.stalkFunctor_toImage_injective x)

/-- The graph morphism is quasi-compact as soon as the open immersion of `U` is: the graph is a
section of the projection `X ×_S ℙ¹_S ⟶ X`, which is proper and so quasi-separated. The
hypothesis holds automatically when `X` is locally Noetherian, which is the case throughout
chapter 42. -/
instance quasiCompact_sectionGraph {X S : Scheme.{u}} (sX : X ⟶ S) (U : X.Opens)
    (s : Γ(X, U)) [QuasiCompact U.ι] : QuasiCompact (sectionGraph sX U s) := by
  have : QuasiCompact (sectionGraph sX U s ≫
      pullback.fst sX (relativeProjectiveLine S ↘ S)) := by
    rw [sectionGraph, pullback.lift_fst]
    infer_instance
  exact QuasiCompact.of_comp (sectionGraph sX U s)
    (pullback.fst sX (relativeProjectiveLine S ↘ S))

/-- The map from `U` onto the graph is scheme-theoretically dominant. -/
private theorem isSchemeTheoreticallyDominant_graphInclusion {X S : Scheme.{u}} (sX : X ⟶ S)
    (U : X.Opens) (s : Γ(X, U)) [QuasiCompact U.ι] :
    IsSchemeTheoreticallyDominant (graphInclusion sX U s) :=
  ⟨AlgebraicGeometry.ker_toImage_eq_bot (sectionGraph sX U s)⟩

/-- The morphism `U ⟶ p⁻¹(U)` induced by the graph: it is the graph on the first factor and the
identity on the second. -/
def graphRestrictLift {X S : Scheme.{u}} (sX : X ⟶ S) (U : X.Opens) (s : Γ(X, U)) :
    U.toScheme ⟶ pullback (graphProjection sX U s) U.ι :=
  pullback.lift (graphInclusion sX U s) (𝟙 U.toScheme)
    ((graphInclusion_comp_graphProjection sX U s).trans (Category.id_comp _).symm)

/-- Composed with the first projection of `p⁻¹(U)`, the morphism `U ⟶ p⁻¹(U)` is the graph
inclusion. -/
@[simp]
theorem graphRestrictLift_fst {X S : Scheme.{u}} (sX : X ⟶ S) (U : X.Opens) (s : Γ(X, U)) :
    graphRestrictLift sX U s ≫ pullback.fst (graphProjection sX U s) U.ι =
      graphInclusion sX U s :=
  pullback.lift_fst _ _ _

/-- Composed with the second projection of `p⁻¹(U)`, the morphism `U ⟶ p⁻¹(U)` is the
identity of `U`. -/
@[simp]
theorem graphRestrictLift_snd {X S : Scheme.{u}} (sX : X ⟶ S) (U : X.Opens) (s : Γ(X, U)) :
    graphRestrictLift sX U s ≫ pullback.snd (graphProjection sX U s) U.ι = 𝟙 _ :=
  pullback.lift_snd _ _ _

/-- `U ⟶ p⁻¹(U)` is a closed immersion, being a section of the proper, hence separated,
morphism `p⁻¹(U) ⟶ U`. -/
theorem isClosedImmersion_graphRestrictLift {X S : Scheme.{u}} (sX : X ⟶ S) (U : X.Opens)
    (s : Γ(X, U)) : IsClosedImmersion (graphRestrictLift sX U s) := by
  have hp := graphProjection_isProper sX U s
  have : IsClosedImmersion (graphRestrictLift sX U s ≫
      pullback.snd (graphProjection sX U s) U.ι) := by
    rw [graphRestrictLift_snd]
    infer_instance
  exact IsClosedImmersion.of_comp _ (pullback.snd (graphProjection sX U s) U.ι)

/-- `U ⟶ p⁻¹(U)` has trivial kernel ideal sheaf: it is the base change, along the open immersion
`p⁻¹(U) ⟶ Y`, of the scheme-theoretically dominant morphism `U ⟶ Y`. -/
theorem ker_graphRestrictLift {X S : Scheme.{u}} (sX : X ⟶ S) (U : X.Opens) (s : Γ(X, U))
    [QuasiCompact U.ι] : (graphRestrictLift sX U s).ker = ⊥ := by
  have hpb : IsPullback (𝟙 U.toScheme) (graphRestrictLift sX U s)
      (graphInclusion sX U s) (pullback.fst (graphProjection sX U s) U.ι) :=
    IsPullback.of_horiz_isIso_mono ⟨by simp⟩
  have := isSchemeTheoreticallyDominant_graphInclusion sX U s
  exact (IsSchemeTheoreticallyDominant.of_isPullback hpb).ker_eq_bot

/-- `U ⟶ p⁻¹(U)` is an isomorphism. -/
theorem isIso_graphRestrictLift {X S : Scheme.{u}} (sX : X ⟶ S) (U : X.Opens) (s : Γ(X, U))
    [QuasiCompact U.ι] : IsIso (graphRestrictLift sX U s) :=
  have := isClosedImmersion_graphRestrictLift sX U s
  IsClosedImmersion.isIso_iff_ker_eq_bot.mpr (ker_graphRestrictLift sX U s)

/-- For a quasi-compact open immersion `U ⟶ X`, the restriction `p⁻¹(U) ⟶ U` of the projection
is an isomorphism. In a Chow situation this is part (2) of Tag 02RQ,
`Stacks.Chow.isIso_graphProjection_morphismRestrict`. -/
theorem isIso_graphProjection_restrict {X S : Scheme.{u}} (sX : X ⟶ S) (U : X.Opens)
    (s : Γ(X, U)) [QuasiCompact U.ι] :
    IsIso (pullback.snd (graphProjection sX U s) U.ι) := by
  have := isIso_graphRestrictLift sX U s
  exact IsIso.of_isIso_fac_left (graphRestrictLift_snd sX U s)

/-! ### The geometry of `Y` that parts (4)-(6) quantify over -/

/-- `Y` is locally of finite type over the base, being proper over `X`. -/
theorem locallyOfFiniteType_graphBaseMorphism {X S : Scheme.{u}} (sX : X ⟶ S)
    [LocallyOfFiniteType sX] (U : X.Opens) (s : Γ(X, U)) :
    LocallyOfFiniteType (graphBaseMorphism sX U s) := by
  have hp := graphProjection_isProper sX U s
  have : LocallyOfFiniteType (graphProjection sX U s) := inferInstance
  exact inferInstanceAs (LocallyOfFiniteType (graphProjection sX U s ≫ sX))

/-- The image of `U` in `Y` is exactly `p⁻¹(U)`. -/
theorem range_graphInclusion {X S : Scheme.{u}} (sX : X ⟶ S) (U : X.Opens) (s : Γ(X, U))
    [QuasiCompact U.ι] :
    Set.range (graphInclusion sX U s) =
      (graphPreimage sX U s : Set (graphClosure sX U s)) := by
  have hiso := isIso_graphRestrictLift sX U s
  rw [← graphRestrictLift_fst sX U s, range_comp_scheme,
    (surjective_of_isIso (graphRestrictLift sX U s)).range_eq, Set.image_univ,
    Scheme.Pullback.range_fst, Scheme.Opens.range_ι]
  rfl

/-- `p⁻¹(U)` is dense in `Y`: it is the image of `U`, which is dense because `Y` is the
scheme-theoretic image of the graph. -/
theorem dense_graphPreimage {X S : Scheme.{u}} (sX : X ⟶ S) (U : X.Opens) (s : Γ(X, U))
    [QuasiCompact U.ι] : GraphPreimageDense sX U s := by
  have hd : IsDominant (graphInclusion sX U s) := inferInstance
  rw [GraphPreimageDense, ← range_graphInclusion sX U s]
  exact hd.denseRange

/-- `Y` is integral when `X` is and `U` is dense: `Y` is reduced because it is the
scheme-theoretic image of the reduced scheme `U`, and irreducible because that image is
dense and `U` is irreducible. -/
theorem isIntegral_graphClosure {X S : Scheme.{u}} (sX : X ⟶ S) (U : X.Opens) (s : Γ(X, U))
    [IsIntegral X] [QuasiCompact U.ι] (hU : Dense (U : Set X)) :
    IsIntegral (graphClosure sX U s) := by
  have hne : Nonempty U.toScheme := by
    obtain ⟨x, hx⟩ := hU.nonempty
    exact ⟨⟨x, hx⟩⟩
  have hUirr : IrreducibleSpace U.toScheme :=
    Topology.IsOpenEmbedding.irreducibleSpace (f := U.ι.base) U.isOpenEmbedding
  have hUred : IsReduced U.toScheme := inferInstance
  have := isSchemeTheoreticallyDominant_graphInclusion sX U s
  have hred : IsReduced (graphClosure sX U s) :=
    IsSchemeTheoreticallyDominant.isReduced (graphInclusion sX U s)
  have hdom : IsDominant (graphInclusion sX U s) := inferInstance
  have hd : DenseRange (graphInclusion sX U s).base := hdom.denseRange
  have himg : IsIrreducible (Set.range (graphInclusion sX U s)) := by
    have := (IrreducibleSpace.isIrreducible_univ U.toScheme).image
      (graphInclusion sX U s).base (Continuous.continuousOn (by continuity))
    rwa [Set.image_univ] at this
  have hirr : IrreducibleSpace (graphClosure sX U s) := by
    rw [irreducibleSpace_def]
    have := himg.closure
    rwa [hd.closure_eq] at this
  rw [isIntegral_iff_irreducibleSpace_and_isReduced]
  exact ⟨hirr, hred⟩

/-! ### The fibres of the two divisors on `Y`, and the rational function on `Y` -/

/-- `Y₀ = q⁻¹D₀`, the pullback of the zero divisor to `Y`. -/
def graphZeroFiber {X S : Scheme.{u}} (sX : X ⟶ S) (U : X.Opens) (s : Γ(X, U)) :
    (graphClosure sX U s).IdealSheafData :=
  (lineZeroDivisor S).comap (graphLineProjection sX U s)

/-- `Y_∞ = q⁻¹D_∞`, the pullback of the infinity divisor to `Y`. -/
def graphInfinityFiber {X S : Scheme.{u}} (sX : X ⟶ S) (U : X.Opens) (s : Γ(X, U)) :
    (graphClosure sX U s).IdealSheafData :=
  (lineInfinityDivisor S).comap (graphLineProjection sX U s)

/-- The support of `Y₀` is the part of `Y` that `q` sends into the zero section. -/
@[simp]
theorem coe_support_graphZeroFiber {X S : Scheme.{u}} (sX : X ⟶ S) (U : X.Opens)
    (s : Γ(X, U)) :
    ((graphZeroFiber sX U s).support : Set (graphClosure sX U s)) =
      graphLineProjection sX U s ⁻¹' Set.range (lineZeroSection S) := by
  rw [graphZeroFiber, Scheme.IdealSheafData.support_comap,
    TopologicalSpace.Closeds.coe_preimage, coe_support_lineZeroDivisor]

/-- The support of `Y_∞` is the part of `Y` that `q` sends into the infinity section. -/
@[simp]
theorem coe_support_graphInfinityFiber {X S : Scheme.{u}} (sX : X ⟶ S) (U : X.Opens)
    (s : Γ(X, U)) :
    ((graphInfinityFiber sX U s).support : Set (graphClosure sX U s)) =
      graphLineProjection sX U s ⁻¹' Set.range (lineInfinitySection S) := by
  rw [graphInfinityFiber, Scheme.IdealSheafData.support_comap,
    TopologicalSpace.Closeds.coe_preimage, coe_support_lineInfinityDivisor]

/-- `Y₀` and `Y_∞` are disjoint closed subschemes of `Y`. -/
theorem disjoint_support_graphZeroFiber_graphInfinityFiber {X S : Scheme.{u}} (sX : X ⟶ S)
    (U : X.Opens) (s : Γ(X, U)) :
    Disjoint ((graphZeroFiber sX U s).support : Set (graphClosure sX U s))
      ((graphInfinityFiber sX U s).support : Set (graphClosure sX U s)) := by
  rw [coe_support_graphZeroFiber, coe_support_graphInfinityFiber]
  exact Disjoint.preimage _ (disjoint_range_lineZeroSection_lineInfinitySection S)

/-- The rational function on `Y` obtained from a unit section on `U` by pulling it back along
`p` to the dense open `p⁻¹(U)`. -/
def graphRationalFunction {X S : Scheme.{u}} (sX : X ⟶ S) (U : X.Opens) (g : (Γ(X, U))ˣ)
    (hd : GraphPreimageDense sX U ↑g) :
    (rationalFunctions (graphClosure sX U ↑g))ˣ :=
  Units.map (ofSectionRingHom (graphClosure sX U ↑g)
      ⟨graphPreimage sX U ↑g, hd⟩).toMonoidHom
    (Units.map ((graphProjection sX U ↑g).app U).hom.toMonoidHom g)

end Stacks.Chow

end
