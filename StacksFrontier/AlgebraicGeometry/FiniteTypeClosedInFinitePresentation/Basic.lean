module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Limits.DescendingMorphisms.Immersion
public import StacksFrontier.AlgebraicGeometry.Morphisms.FinitePresentationPoint

/-!
# Replacing an immersion into a scheme of finite presentation by a closed immersion

A scheme quasi-compact over a quasi-separated base which admits an immersion into a scheme of
finite presentation over that base admits a *closed* immersion into one. The passage from the
immersion to the closed immersion is the content of Tag 01ZG once Tag 01ZE has produced the
immersion, and it is proved here.

An immersion factors as a closed immersion into an open subscheme of its target, namely the
coborder of its range. The source is quasi-compact, so its image inside that open subscheme is
covered by finitely many affine opens, and the closed immersion restricts to a closed immersion
into their union. That union is a quasi-compact open of a quasi-separated scheme, so its
inclusion is quasi-compact, hence of finite presentation, and the composition with the
finitely-presented morphism to the base is again of finite presentation.

## Main results

* `AlgebraicGeometry.FinitePresentation.comp`: morphisms of finite presentation are closed under
  composition.
* `AlgebraicGeometry.locallyOfFinitePresentation_comp_and_finitePresentation_comp`: Tag 01TR,
  composition for both the local and the global notion of finite presentation.
* `AlgebraicGeometry.exists_qcqs_finitePresentation_isClosedImmersion_of_exists_immersion`: the
  passage from an immersion to a closed immersion described above, recording that the scheme
  constructed is quasi-compact and quasi-separated.
* `AlgebraicGeometry.exists_finitePresentation_isClosedImmersion_of_exists_immersion`: the same
  statement with those two properties forgotten.

## Implementation notes

"Of finite presentation" is `AlgebraicGeometry.FinitePresentation`, the conjunction of
`AlgebraicGeometry.LocallyOfFinitePresentation`, `AlgebraicGeometry.QuasiCompact` and
`AlgebraicGeometry.QuasiSeparated` from
`StacksFrontier/AlgebraicGeometry/Morphisms/FinitePresentationPoint.lean`. Mathlib carries only the
local notion as a class, so the three constituents are introduced by hand wherever a bundled
hypothesis has to be unpacked.

The main theorems take the existence of the immersion as a hypothesis. They are therefore
**not** a proof of Tag 01ZG: the attribute for that tag is withheld from both, because Tag 01ZG
asserts the conclusion from local finiteness of type alone, whereas these statements assume the
immersion. The missing input is Tag 01ZE.

The conclusion is stated twice because its two consumers want different amounts of it. The
forgetful form is exactly the shape of the `h01ZG` hypothesis of
`AlgebraicGeometry.LimitNoetherianSituation.nonempty_goodDiagram_of_exists_model`, which is
where Tag 0CNN uses this result. Tag 09ZQ instead presents the closed subscheme as a limit by
way of Tag 09ZP, which assumes the ambient scheme quasi-compact and quasi-separated; both hold
for the scheme built here, so they are recorded rather than reproved.

The quasi-compact open containing the image is produced by
`AlgebraicGeometry.exists_compactOpen_covering_range`, and the coborder factorisation of an
immersion by `AlgebraicGeometry.Scheme.Hom.liftCoborder`.

## References

* [Stacks Project, Tag 01ZG](https://stacks.math.columbia.edu/tag/01ZG)
* [Stacks Project, Tag 01ZE](https://stacks.math.columbia.edu/tag/01ZE)
* [Stacks Project, Tag 01TR](https://stacks.math.columbia.edu/tag/01TR)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

add_to_sga "6 III 1.14" "special case" AlgebraicGeometry.locallyOfFinitePresentation_comp
add_to_ega "IV 1.4.3" AlgebraicGeometry.locallyOfFinitePresentation_comp

/-- The composition of two morphisms of finite presentation is of finite presentation.

Mathlib has no bundled `FinitePresentation` predicate for schemes, so this statement is not one
it can make; its three components compose in Mathlib, by
`AlgebraicGeometry.locallyOfFinitePresentation_comp` and the
`MorphismProperty.IsStableUnderComposition` instances for `QuasiCompact` and `QuasiSeparated`,
which is all the proof below uses. Tag 01TR, which asserts both this and the statement for the
local notion, is carried by
`AlgebraicGeometry.locallyOfFinitePresentation_comp_and_finitePresentation_comp` below. -/
@[ega "I 6.6.4" "(ii), special case",
  ega "IV 1.4.3" "(ii), special case",
  ega "IV 1.6.2",
  sga "1 VIII 3.6"]
theorem FinitePresentation.comp {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    (hf : FinitePresentation f) (hg : FinitePresentation g) : FinitePresentation (f ≫ g) :=
  have := hf.1; have := hf.2.1; have := hf.2.2
  have := hg.1; have := hg.2.1; have := hg.2.2
  ⟨inferInstance, inferInstance, inferInstance⟩

/-- The composition of two morphisms locally of finite presentation is locally of finite
presentation, and the composition of two morphisms of finite presentation is of finite
presentation.

The first assertion is Mathlib's instance `AlgebraicGeometry.locallyOfFinitePresentation_comp`;
the second is `AlgebraicGeometry.FinitePresentation.comp`, for the Stacks notion
`AlgebraicGeometry.FinitePresentation` (locally of finite presentation, quasi-compact and
quasi-separated). -/
@[stacks 01TR "Both assertions: the first is Mathlib's
  `AlgebraicGeometry.locallyOfFinitePresentation_comp`, the second
  `AlgebraicGeometry.FinitePresentation.comp`."]
theorem locallyOfFinitePresentation_comp_and_finitePresentation_comp {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    (LocallyOfFinitePresentation f → LocallyOfFinitePresentation g →
        LocallyOfFinitePresentation (f ≫ g)) ∧
      (FinitePresentation f → FinitePresentation g → FinitePresentation (f ≫ g)) :=
  ⟨fun _ _ => inferInstance, FinitePresentation.comp⟩

/-- A quasi-compact scheme which admits an immersion into a scheme of finite presentation over a
quasi-separated base admits a closed immersion into a quasi-compact quasi-separated scheme of
finite presentation over that base, compatibly with the structure morphisms.

This is the passage from an immersion to a closed immersion in Tag 01ZG. The existence of the
immersion is Tag 01ZE and is taken as a hypothesis, so the statement is weaker than Tag 01ZG and
carries no attribute for it. Note that neither local finiteness of type of `f` nor
quasi-separatedness of `X`, both assumed by Tag 01ZG, is needed once the immersion is given. -/
theorem exists_qcqs_finitePresentation_isClosedImmersion_of_exists_immersion {X S : Scheme.{u}}
    (f : X ⟶ S) [CompactSpace X] [QuasiSeparatedSpace S]
    (h01ZE : ∃ (Y : Scheme.{u}) (g : Y ⟶ S) (i : X ⟶ Y),
      FinitePresentation g ∧ IsImmersion i ∧ i ≫ g = f) :
    ∃ (X' : Scheme.{u}) (p : X' ⟶ S) (ι : X ⟶ X'),
      FinitePresentation p ∧ IsClosedImmersion ι ∧ ι ≫ p = f ∧
        CompactSpace X' ∧ QuasiSeparatedSpace X' := by
  obtain ⟨Y, g, i, hg, hi, hif⟩ := h01ZE
  have : IsImmersion i := hi
  have := hg.1
  have := hg.2.1
  have := hg.2.2
  have : QuasiSeparatedSpace Y := quasiSeparatedSpace_of_quasiSeparated g
  have hkC : i.liftCoborder ≫ i.coborderRange.ι = i := i.liftCoborder_ι
  obtain ⟨V, hVc, -, hVr⟩ :=
    exists_compactOpen_covering_range i.liftCoborder (W := ⊤) (by simp)
  have hVsub : Set.range i.liftCoborder.base ⊆ Set.range V.ι.base := by
    rw [Scheme.Opens.range_ι]; exact hVr
  have hjV : IsOpenImmersion.lift V.ι i.liftCoborder hVsub ≫ V.ι = i.liftCoborder :=
    IsOpenImmersion.lift_fac _ _ _
  have hjCI : IsClosedImmersion (IsOpenImmersion.lift V.ι i.liftCoborder hVsub) := by
    have : IsClosedImmersion (IsOpenImmersion.lift V.ι i.liftCoborder hVsub ≫ V.ι) := by
      rw [hjV]; infer_instance
    exact IsClosedImmersion.of_comp _ V.ι
  have hVcs : CompactSpace V.toScheme := isCompact_iff_compactSpace.mp hVc
  have hVqs : QuasiSeparatedSpace V.toScheme :=
    quasiSeparatedSpace_of_quasiSeparated (V.ι ≫ i.coborderRange.ι)
  have hfpVC : FinitePresentation (V.ι ≫ i.coborderRange.ι) :=
    ⟨inferInstance, quasiCompact_of_compactSpace _, inferInstance⟩
  refine ⟨V.toScheme, (V.ι ≫ i.coborderRange.ι) ≫ g,
    IsOpenImmersion.lift V.ι i.liftCoborder hVsub, hfpVC.comp hg, hjCI, ?_, hVcs, hVqs⟩
  calc IsOpenImmersion.lift V.ι i.liftCoborder hVsub ≫ (V.ι ≫ i.coborderRange.ι) ≫ g
      = ((IsOpenImmersion.lift V.ι i.liftCoborder hVsub ≫ V.ι) ≫ i.coborderRange.ι) ≫ g := by
        simp only [Category.assoc]
    _ = f := by rw [hjV, hkC, hif]

/-- The conclusion of
`AlgebraicGeometry.exists_qcqs_finitePresentation_isClosedImmersion_of_exists_immersion` with the
quasi-compactness and quasi-separatedness of the constructed scheme forgotten.

This is the shape in which Tag 0CNN consumes the result, through the `h01ZG` hypothesis of
`AlgebraicGeometry.LimitNoetherianSituation.nonempty_goodDiagram_of_exists_model`. Like the
theorem it weakens, it assumes Tag 01ZE and carries no attribute for Tag 01ZG. -/
theorem exists_finitePresentation_isClosedImmersion_of_exists_immersion {X S : Scheme.{u}}
    (f : X ⟶ S) [CompactSpace X] [QuasiSeparatedSpace S]
    (h01ZE : ∃ (Y : Scheme.{u}) (g : Y ⟶ S) (i : X ⟶ Y),
      FinitePresentation g ∧ IsImmersion i ∧ i ≫ g = f) :
    ∃ (X' : Scheme.{u}) (p : X' ⟶ S) (ι : X ⟶ X'),
      FinitePresentation p ∧ IsClosedImmersion ι ∧ ι ≫ p = f :=
  let ⟨X', p, ι, hp, hι, hcomm, _, _⟩ :=
    exists_qcqs_finitePresentation_isClosedImmersion_of_exists_immersion f h01ZE
  ⟨X', p, ι, hp, hι, hcomm⟩

end AlgebraicGeometry

end
