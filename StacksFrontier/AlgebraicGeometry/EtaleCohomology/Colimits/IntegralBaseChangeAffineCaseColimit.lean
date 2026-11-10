module

public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.SmallEtaleSetsVerticalPasting
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.IntegralBaseChangeAffineCase

/-!
# Étale base change along an integral morphism: the affine case

Consider a cartesian square

```
X' --g'--> X
|f'        |f
v          v
Y' --g---> Y
```

of schemes with `f` integral and `Y`, `Y'` affine, a limit presentation
`Stacks.EtaleCohomology.IntegralSquareLimitData` of it by cartesian squares with finite vertical
morphisms, and a sheaf of sets `F` on the small étale site of `X`. This file closes the chain

```
g⁻¹ f_* F = g⁻¹ (colim_i f_{i,*}F_i) = colim_i g⁻¹ f_{i,*}F_i
          = colim_i f'_{i,*}(g'_i)⁻¹F_i = f'_* (g')⁻¹ F
```

of [Stacks, Tag 0EYP] whose links are assembled in
`StacksFrontier/AlgebraicGeometry/EtaleCohomology/Colimits/IntegralBaseChangeAffineCase.lean`.

The link that file left open is the identity
`Stacks.EtaleCohomology.stageComparison_comp_stageLeg` below: the vertical pasting law for the
base change comparison, applied to the splitting of the given square into the upper square over
`g'_i` and the stage square over `g`. With it, the comparison of the given square differs from
`Stacks.EtaleCohomology.stageLeg S F i` by two isomorphisms — the inverse image of
`Stacks.EtaleCohomology.stageDirectImageIso` and the stagewise comparison
`Stacks.EtaleCohomology.stageComparison` — so the whole remaining content of the tag sits in the
colimit statement, the second half of [Stacks, Tag 0EYN] together with the interchange of `f'_*`
with the colimit, and that is what is taken as a hypothesis here.

## Main results

* `Stacks.EtaleCohomology.stageComparison_comp_stageLeg` — **the vertical pasting law at the
  splitting of the given square**, the identity the preceding file left open.
* `Stacks.EtaleCohomology.stageTargetIso_hom_comp` —
  `Stacks.EtaleCohomology.stageLeg` is the base change comparison of the given square, read
  through the isomorphism `Stacks.EtaleCohomology.stageTargetIso`.
* `Stacks.EtaleCohomology.isIso_smallEtaleSetsBaseChange_app_iff_isIso_stageLeg` — **the
  comparison of the given square is invertible if and only if one leg
  `Stacks.EtaleCohomology.stageLeg` is**, with no hypothesis beyond the limit presentation.
* `Stacks.EtaleCohomology.isIso_smallEtaleSetsBaseChange_app_of_isColimit` — **[Stacks, Tag
  0EYP] for sheaves of sets in the all-affine case**, granted that the cocone
  `Stacks.EtaleCohomology.stageTargetCocone` is a colimit cocone.

## Main definitions

* `Stacks.EtaleCohomology.stageComparisonIso` — the stagewise comparison as an isomorphism,
  which is [Stacks, Tag 0959] at the stage.
* `Stacks.EtaleCohomology.stageTarget` — the sheaf `f'_{i,*}(g'_i)⁻¹F_i` on `Y'`, the source of
  `Stacks.EtaleCohomology.stageLeg`.
* `Stacks.EtaleCohomology.stageTargetIso` — its identification with `g⁻¹ f_* F`, the inverse of
  `Stacks.EtaleCohomology.stageComparison` followed by the inverse image of
  `Stacks.EtaleCohomology.stageDirectImageIso`.
* `Stacks.EtaleCohomology.stageTargetTransition` and
  `Stacks.EtaleCohomology.stageTargetDiagram` — the transition morphisms of the diagram
  `i ↦ f'_{i,*}(g'_i)⁻¹F_i` on `Y'` whose colimit the source takes, and that diagram.
* `Stacks.EtaleCohomology.stageTargetCocone` — the cocone on it with vertex `f'_*(g')⁻¹F` whose
  legs are `Stacks.EtaleCohomology.stageLeg`.

## Implementation notes

**How the pasting law is instantiated.** `stageComparison_comp_stageLeg` is
`Stacks.EtaleCohomology.smallEtaleSetsBaseChange_vpaste_app'` at the limit presentation, and the
whole cost of that instance is paid in making it *syntactically* the goal. Three things are
needed, each to avoid a `(kernel) deterministic timeout`.

*The six corners are explicit, and are given.* They are explicit arguments of that lemma and are
passed as `X`, `X'`, `S.diagram.obj i`, `S.diagram'.obj i`, `Y`, `Y'`. Left implicit, unification
reads them off the types of the morphisms supplied, which is not where the goal's own corners came
from.

*Every stage morphism is in plain-corner form.* The structure morphisms and projections of the
presentation are components of natural transformations to and from constant functors, so the
target of `S.structureMap.app i` is `((Functor.const _).obj Y).obj i` rather than `Y`. A
construction elaborated against that spelling carries it in the implicit corners of everything it
is substituted into, `Stacks.EtaleCohomology.smallEtaleSetsBaseChange` among them; the instance
and the goal then differ *inside* the arguments of that natural transformation, and deciding them
sends the kernel into its definition — the mate of the square comparison of composite direct
images — which does not terminate within budget. So
`Stacks.EtaleCohomology.IntegralSquareLimitData.structureMapAt` and its three companions are used
throughout, on both sides.

*The morphisms are NOT given; `apply` recovers them.* This is the part that is easy to get wrong,
because supplying them looks harmless. The two sides of the identity meet across the `.app` of
`smallEtaleSetsBaseChange`, and the kernel will compare two such values only when the natural
transformation and its argument are *already syntactically equal*: it has no cheap route from one
spelling to another, since reducing the `.app` means putting the mate in constructor form. A
hand-written argument list is a second copy of what the definitions already carry, and a second
copy is exactly what cannot be reconciled — even when it is the same source text, and even when
the definitions' bodies are written out to match. `apply` leaves the morphisms as metavariables
and lets unification read them off the goal through the reducible abbreviations, so every argument
of the instance is literally the subterm the goal carries and the final check is an identity.
With the corners explicit, plain corners throughout, and the morphisms written out, this
declaration times out in the kernel whether the proof is `rw`-then-`exact` or a bare term, and so
does `stageComparison S F i = <its own body>` by `rfl`; with `apply` it checks in seconds.

**What is assumed, exactly.** The only hypothesis of
`Stacks.EtaleCohomology.isIso_smallEtaleSetsBaseChange_app_of_isColimit` beyond the limit
presentation and the square being cartesian is
`CategoryTheory.Limits.IsColimit (stageTargetCocone S F sq)`: that the cocone on the diagram
`i ↦ f'_{i,*}(g'_i)⁻¹F_i` with legs `Stacks.EtaleCohomology.stageLeg S F i` and vertex
`f'_*(g')⁻¹F` is a colimit cocone. This is the last equality of the chain above — the conjunction
of the second half of [Stacks, Tag 0EYN] with the interchange of a direct image and such a
colimit — and neither half is carried by the library, so it is a hypothesis.

**Where the transition morphisms come from.** The source's diagram `i ↦ f'_{i,*}(g'_i)⁻¹F_i` is
the diagram `i ↦ g⁻¹ f_{i,*}F_i` read through the stagewise base change comparison, which is an
isomorphism by [Stacks, Tag 0959] (`Stacks.EtaleCohomology.isIso_stageBaseChange`).
`Stacks.EtaleCohomology.stageTargetTransition` is defined that way, as the transport of
`Stacks.EtaleCohomology.stageDirectImageTransition` along
`Stacks.EtaleCohomology.stageComparison`; this is the unique choice making the stagewise
comparison an isomorphism of diagrams, and it makes every transition invertible
(`Stacks.EtaleCohomology.isIso_stageTargetTransition`), the system of direct images along the
stages being constant by `Stacks.EtaleCohomology.isIso_stageDirectImageTransition`. The diagram
is indexed by `Stacks.EtaleCohomology.IntegralSquareLimitData.indexType` rather than by its
opposite: the inverse system of schemes is contravariant, so the system of direct images of a
fixed sheaf on the limit is covariant.

**Why invertibility of a single leg suffices.** `..._iff_isIso_stageLeg` needs no colimit
statement at all: the pasting identity exhibits every leg as the comparison of the given square
composed with an isomorphism. The colimit hypothesis is what supplies a leg that *is* invertible,
and it does so because the diagram's transitions are, so that its colimit is attained at every
index.

**No `@[stacks 0EYP]` attribute is attached.** Every statement here is conditional on the colimit
hypothesis, so none of them proves that tag; and the passage from the all-affine case to an
arbitrary cartesian square, which is
`Stacks.EtaleCohomology.isIso_smallEtaleSetsBaseChange_app_of_isIntegralHom_of_affine_case`, is
not performed here. Whoever discharges the colimit hypothesis and assembles the chain end to end
should assess the covering set and place the attribute.

## References

* [Stacks Project, Tag 0EYP](https://stacks.math.columbia.edu/tag/0EYP)
* [Stacks Project, Tag 0EYN](https://stacks.math.columbia.edu/tag/0EYN)
* [Stacks Project, Tag 0959](https://stacks.math.columbia.edu/tag/0959)

Tags covered: none.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology

section AffineCase

variable {X X' Y Y' : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
  (S : IntegralSquareLimitData g' f' f g) (F : Sheaf (smallEtaleTopology X) (Type (u + 1)))

/-- **The base change comparison at a stage, as an isomorphism.** The componentwise form of
`Stacks.EtaleCohomology.isIso_stageBaseChange`, obtained through
`CategoryTheory.NatIso.isIso_app_of_isIso` as the docstring of that instance prescribes.

It is packaged as an isomorphism, with the two `IsIso` facts consumed inside the body, rather
than exported as an `instance` on `Stacks.EtaleCohomology.stageComparison`: that abbreviation
unfolds to the value of a natural transformation at a sheaf, so an instance whose subject is the
abbreviation sends instance search looking for the invertibility of an `.app`, and the consumers
below need the isomorphism itself in any case. Its `hom` is the comparison by `rfl`
(`Stacks.EtaleCohomology.stageComparisonIso_hom`). -/
def stageComparisonIso (i : S.indexTypeᵒᵖ) :
    (smallEtaleDirectImage.{u, 0} (S.structureMapAt i) ⋙
        smallEtaleInverseImage.{u, 0} g).obj (stageSheaf S F i) ≅
      (smallEtaleInverseImage.{u, 0} (S.horizontal.app i) ⋙
        smallEtaleDirectImage.{u, 0} (S.structureMapAt' i)).obj (stageSheaf S F i) :=
  have := isIso_stageBaseChange S i
  have : IsIso (stageComparison S F i) := NatIso.isIso_app_of_isIso _ _
  asIso (stageComparison S F i)

/-- The forward map of `Stacks.EtaleCohomology.stageComparisonIso S F i` is the base change
comparison `Stacks.EtaleCohomology.stageComparison S F i`. -/
@[simp]
theorem stageComparisonIso_hom (i : S.indexTypeᵒᵖ) :
    (stageComparisonIso S F i).hom = stageComparison S F i :=
  rfl

/-! ### The vertical pasting law at the splitting of the given square -/

/-- **The vertical pasting law for the base change comparison, at the splitting of the given
square.** The given cartesian square splits into the upper square

```
X' ----g'----> X
|p'_i          |p_i
v              v
X'_i --g'_i--> X_i
```

over `g'_i` and the stage square over `g`; the base change comparison of the given square,
precomposed with the inverse image of the identification
`Stacks.EtaleCohomology.stageDirectImageIso` of `f_{i,*}F_i` with `f_* F`, is the comparison
`Stacks.EtaleCohomology.stageComparison` of the stage square followed by the leg
`Stacks.EtaleCohomology.stageLeg` built from the comparison of the upper square.

This is the identity that closes the chain of [Stacks, Tag 0EYP] in the all-affine case. It is
`Stacks.EtaleCohomology.smallEtaleSetsBaseChange_vpaste_app'` at the limit presentation: the two
factorizations `f = p_i ≫ st_i` and `f' = p'_i ≫ st'_i` are the fields
`Stacks.EtaleCohomology.IntegralSquareLimitData.projectionAt_comp_structureMapAt` and
`Stacks.EtaleCohomology.IntegralSquareLimitData.projectionAt'_comp_structureMapAt'`, and the
commutativity of the upper
square is
`Stacks.EtaleCohomology.IntegralSquareLimitData.projectionAt'_comp_horizontal`.

**The proof is `apply` with the six corners and nothing else.** The corners have to be given —
unification does not recover them from the morphisms — but the morphisms must *not* be, and the
implementation notes of this file say why: written out by hand they are a second copy of what the
definitions already contain, and the kernel will not reconcile two copies across the `.app` of
`Stacks.EtaleCohomology.smallEtaleSetsBaseChange`. `apply` reads them off the goal instead, so
every argument of the instance is literally the subterm the goal carries. -/
theorem stageComparison_comp_stageLeg (sq : IsPullback g' f' f g) (i : S.indexTypeᵒᵖ) :
    (smallEtaleInverseImage.{u, 0} g).map (stageDirectImageIso S (Type (u + 1)) F i).hom ≫
        (smallEtaleSetsBaseChange.{u, 0} g' f' f g sq.w).app F =
      stageComparison S F i ≫ stageLeg S F i := by
  apply smallEtaleSetsBaseChange_vpaste_app'.{u, 0} X X' (S.diagram.obj i) (S.diagram'.obj i) Y Y'

/-! ### The diagram whose colimit the source takes, and its cocone -/

/-- The sheaf `f'_{i,*}(g'_i)⁻¹F_i` on the small étale site of `Y'`, the source of
`Stacks.EtaleCohomology.stageLeg` and the target of
`Stacks.EtaleCohomology.stageComparison`: the `i`-th term of the diagram whose colimit the last
equality of the chain of [Stacks, Tag 0EYP] computes. -/
abbrev stageTarget (i : S.indexTypeᵒᵖ) : Sheaf (smallEtaleTopology Y') (Type (u + 1)) :=
  (smallEtaleInverseImage.{u, 0} (S.horizontal.app i) ⋙
    smallEtaleDirectImage.{u, 0} (S.structureMapAt' i)).obj (stageSheaf S F i)

/-- **The identification `f'_{i,*}(g'_i)⁻¹F_i ≅ g⁻¹ f_* F`.** The stagewise base change
comparison `Stacks.EtaleCohomology.stageComparison` is an isomorphism by [Stacks, Tag 0959], and
the system of direct images along the stages is constant at `f_* F` by
`Stacks.EtaleCohomology.stageDirectImageIso`; composing the two identifies every term of the
diagram whose colimit the source takes with `g⁻¹ f_* F`. -/
def stageTargetIso (i : S.indexTypeᵒᵖ) :
    stageTarget S F i ≅
      (smallEtaleDirectImage.{u, 0} f ⋙ smallEtaleInverseImage.{u, 0} g).obj F :=
  (stageComparisonIso S F i).symm ≪≫
    (smallEtaleInverseImage.{u, 0} g).mapIso (stageDirectImageIso S (Type (u + 1)) F i)

/-- The transition morphism `f'_{j,*}(g'_j)⁻¹F_j ⟶ f'_{i,*}(g'_i)⁻¹F_i` of the diagram whose
colimit the source takes, for a transition `a : i ⟶ j` of the index category: the transition
`Stacks.EtaleCohomology.stageDirectImageTransition` of the system of direct images along the
stages, read through the stagewise base change comparison.

This is the unique choice making `Stacks.EtaleCohomology.stageComparison` an isomorphism of
diagrams, which is the compatibility of [Stacks, Tag 0959] with the system. -/
def stageTargetTransition {i j : S.indexTypeᵒᵖ} (a : i ⟶ j) :
    stageTarget S F j ⟶ stageTarget S F i :=
  (stageComparisonIso S F j).inv ≫
    (smallEtaleInverseImage.{u, 0} g).map (stageDirectImageTransition S (Type (u + 1)) F a) ≫
      (stageComparisonIso S F i).hom

/-- **Every transition of the diagram is the identity of `g⁻¹ f_* F` conjugated by
`Stacks.EtaleCohomology.stageTargetIso`.** The system of direct images along the stages is
constant, which is `Stacks.EtaleCohomology.stageDirectImageTransition_eq`; transporting that
along the stagewise comparison gives this. -/
theorem stageTargetTransition_eq {i j : S.indexTypeᵒᵖ} (a : i ⟶ j) :
    stageTargetTransition S F a = (stageTargetIso S F j).hom ≫ (stageTargetIso S F i).inv := by
  simp only [stageTargetTransition, stageTargetIso, stageDirectImageTransition_eq, Iso.trans_hom,
    Iso.trans_inv, Iso.symm_hom, Iso.symm_inv, Functor.mapIso_hom, Functor.mapIso_inv,
    Functor.map_comp, Category.assoc]

/-- Every transition morphism of the diagram whose colimit the source takes is an isomorphism. -/
instance isIso_stageTargetTransition {i j : S.indexTypeᵒᵖ} (a : i ⟶ j) :
    IsIso (stageTargetTransition S F a) := by
  rw [stageTargetTransition_eq]
  infer_instance

/-- **The transitions are compatible with the identification with the constant diagram.** -/
theorem stageTargetTransition_comp_iso {i j : S.indexTypeᵒᵖ} (a : i ⟶ j) :
    stageTargetTransition S F a ≫ (stageTargetIso S F i).hom = (stageTargetIso S F j).hom := by
  rw [stageTargetTransition_eq, Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- **The diagram `i ↦ f'_{i,*}(g'_i)⁻¹F_i` on `Y'`**, indexed by the directed index of the limit
presentation. Its transitions are `Stacks.EtaleCohomology.stageTargetTransition`, and
functoriality is `Stacks.EtaleCohomology.stageTargetTransition_eq`: each transition is the
identity of `g⁻¹ f_* F` conjugated by `Stacks.EtaleCohomology.stageTargetIso`. -/
def stageTargetDiagram : S.indexType ⥤ Sheaf (smallEtaleTopology Y') (Type (u + 1)) where
  obj i := stageTarget S F (Opposite.op i)
  map {_ _} h := stageTargetTransition S F h.op
  map_id _ := by rw [stageTargetTransition_eq]; simp
  map_comp _ _ := by
    rw [stageTargetTransition_eq, stageTargetTransition_eq, stageTargetTransition_eq]
    simp

/-- Every transition morphism of `Stacks.EtaleCohomology.stageTargetDiagram` is an
isomorphism. -/
instance isIso_stageTargetDiagram_map {i j : S.indexType} (h : i ⟶ j) :
    IsIso ((stageTargetDiagram S F).map h) :=
  isIso_stageTargetTransition S F h.op

/-- **`Stacks.EtaleCohomology.stageLeg` is the base change comparison of the given square, read
through `Stacks.EtaleCohomology.stageTargetIso`.** This is
`Stacks.EtaleCohomology.stageComparison_comp_stageLeg` solved for the leg, and it is what reduces
[Stacks, Tag 0EYP] in the all-affine case to the invertibility of a single leg. -/
theorem stageTargetIso_hom_comp (sq : IsPullback g' f' f g) (i : S.indexTypeᵒᵖ) :
    (stageTargetIso S F i).hom ≫ (smallEtaleSetsBaseChange.{u, 0} g' f' f g sq.w).app F =
      stageLeg S F i := by
  rw [stageTargetIso, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Category.assoc,
    stageComparison_comp_stageLeg S F sq i]
  exact (stageComparisonIso S F i).inv_hom_id_assoc _

/-- The legs `Stacks.EtaleCohomology.stageLeg` form a cocone on the diagram
`i ↦ f'_{i,*}(g'_i)⁻¹F_i` with vertex `f'_*(g')⁻¹F`. The cocone identity is
`Stacks.EtaleCohomology.stageTargetTransition_comp_iso` read through
`Stacks.EtaleCohomology.stageTargetIso_hom_comp`. -/
def stageTargetCocone (sq : IsPullback g' f' f g) : Cocone (stageTargetDiagram S F) where
  pt := (smallEtaleInverseImage.{u, 0} g' ⋙ smallEtaleDirectImage.{u, 0} f').obj F
  ι :=
    { app := fun i => stageLeg S F (Opposite.op i)
      naturality := fun i j h => by
        change stageTargetTransition S F h.op ≫ stageLeg S F (Opposite.op j) =
          stageLeg S F (Opposite.op i) ≫ 𝟙 _
        rw [Category.comp_id, ← stageTargetIso_hom_comp S F sq (Opposite.op j),
          ← stageTargetIso_hom_comp S F sq (Opposite.op i), ← Category.assoc,
          stageTargetTransition_comp_iso] }

/-! ### The affine case -/

/-- **The base change comparison of the given square is invertible if and only if one leg of the
target cocone is.** Nothing beyond the limit presentation enters: by
`Stacks.EtaleCohomology.stageTargetIso_hom_comp` the two morphisms differ by the isomorphism
`Stacks.EtaleCohomology.stageTargetIso`. -/
theorem isIso_smallEtaleSetsBaseChange_app_iff_isIso_stageLeg (sq : IsPullback g' f' f g)
    (i : S.indexTypeᵒᵖ) :
    IsIso ((smallEtaleSetsBaseChange.{u, 0} g' f' f g sq.w).app F) ↔ IsIso (stageLeg S F i) := by
  rw [← stageTargetIso_hom_comp S F sq i]
  exact (isIso_comp_left_iff (stageTargetIso S F i).hom _).symm

/-- **[Stacks, Tag 0EYP] for sheaves of sets, in the all-affine case.** For a cartesian square
with `f` integral and `Y`, `Y'` affine, given a limit presentation of the square by cartesian
squares with finite vertical morphisms, the base change comparison `g⁻¹ f_* F ⟶ f'_*(g')⁻¹F` on
Mathlib's small étale sites is an isomorphism as soon as the cocone
`Stacks.EtaleCohomology.stageTargetCocone` is a colimit cocone.

That colimit hypothesis is the last equality of the chain
`g⁻¹ f_*F = colim_i g⁻¹ f_{i,*}F_i = colim_i f'_{i,*}(g'_i)⁻¹F_i = f'_*(g')⁻¹F`, that is, the
conjunction of the second half of [Stacks, Tag 0EYN] with the interchange of `f'_*` and the
colimit. Everything else — the limit presentation, [Stacks, Tag 0959] at each stage, the
constancy of the system of direct images along the stages, and the vertical pasting law relating
the three comparisons — is discharged.

The proof does not use that the index category is connected or the transitions invertible: the
comparison of the given square is inverted by the map the colimit property produces out of the
cocone whose legs are `Stacks.EtaleCohomology.stageTargetIso`, which is a cocone precisely
because the diagram is constant up to that isomorphism. -/
theorem isIso_smallEtaleSetsBaseChange_app_of_isColimit (sq : IsPullback g' f' f g)
    (hc : IsColimit (stageTargetCocone S F sq)) :
    IsIso ((smallEtaleSetsBaseChange.{u, 0} g' f' f g sq.w).app F) := by
  obtain ⟨i₀⟩ := S.indexNonempty
  let c₀ : Cocone (stageTargetDiagram S F) :=
    { pt := (smallEtaleDirectImage.{u, 0} f ⋙ smallEtaleInverseImage.{u, 0} g).obj F
      ι :=
        { app := fun i => (stageTargetIso S F (Opposite.op i)).hom
          naturality := fun i j h => by
            change stageTargetTransition S F h.op ≫ (stageTargetIso S F (Opposite.op j)).hom =
              (stageTargetIso S F (Opposite.op i)).hom ≫ 𝟙 _
            rw [Category.comp_id, stageTargetTransition_comp_iso] } }
  obtain ⟨φ, hφ⟩ :
      ∃ φ : (smallEtaleInverseImage.{u, 0} g' ⋙ smallEtaleDirectImage.{u, 0} f').obj F ⟶
          (smallEtaleDirectImage.{u, 0} f ⋙ smallEtaleInverseImage.{u, 0} g).obj F,
        ∀ i : S.indexType, stageLeg S F (Opposite.op i) ≫ φ =
          (stageTargetIso S F (Opposite.op i)).hom :=
    ⟨hc.desc c₀, fun i => hc.fac c₀ i⟩
  refine ⟨φ, ?_, ?_⟩
  · refine (cancel_epi (stageTargetIso S F (Opposite.op i₀)).hom).1 ?_
    rw [Category.comp_id, ← Category.assoc, stageTargetIso_hom_comp S F sq, hφ i₀]
  · refine hc.hom_ext fun i => ?_
    change stageLeg S F (Opposite.op i) ≫ φ ≫
        (smallEtaleSetsBaseChange.{u, 0} g' f' f g sq.w).app F =
      stageLeg S F (Opposite.op i) ≫
        𝟙 ((smallEtaleInverseImage.{u, 0} g' ⋙ smallEtaleDirectImage.{u, 0} f').obj F)
    rw [← Category.assoc, hφ i, stageTargetIso_hom_comp S F sq]
    exact (Category.comp_id _).symm

end AffineCase

end Stacks.EtaleCohomology

end
