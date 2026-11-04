module

public import StacksFrontier.AlgebraicGeometry.FiniteTypeClosedInFinitePresentation.Glueing
public import StacksFrontier.AlgebraicGeometry.LimitDescentGlueing.Glueing
public import StacksFrontier.AlgebraicGeometry.Limits.AffineNoetherianApproximation
public import StacksFrontier.AlgebraicGeometry.Limits.DescendingMorphisms.FiniteTypeModel
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Good diagrams from the single-affine step of Noetherian approximation

In Situation [Stacks, Tag 0CNM] — a directed inverse system of Noetherian schemes with affine
transition morphisms and a chosen limiting cone with vertex `S` — [Stacks, Tag 0CNN] says that a
quasi-separated morphism `f : X ⟶ S` of finite type fits into a diagram
```
X ⟶ W
↓    ↓
S ⟶ Sᵢ
```
with `W ⟶ Sᵢ` of finite type and `X ⟶ S ×_{Sᵢ} W` a closed immersion. That datum is
`AlgebraicGeometry.LimitNoetherianSituation.GoodDiagram`, and the Stacks proof of Tag 0CNN has
exactly two inputs: [Stacks, Tag 01ZG], which embeds `X` as a closed subscheme of a scheme of
finite presentation over `S`, and part (1) of [Stacks, Tag 01ZM], which descends that scheme to
a finite stage.

`AlgebraicGeometry.LimitNoetherianSituation.nonempty_goodDiagram_of_exists_model` is the Stacks
argument with the two inputs left as hypotheses; this file supplies them:

* Tag 01ZG is
  `AlgebraicGeometry.exists_finitePresentation_isClosedImmersion_of_isOneAffineOpenStep`, whose
  only hypothesis beyond the tag's own is
  `AlgebraicGeometry.Scheme.FiniteTypeApproximation.IsOneAffineOpenStep`, the single-affine step
  of absolute Noetherian approximation ([Stacks, Tag 07RN]), which enters as a hypothesis. Its
  conclusion is the hypothesis `h01ZG` on the nose, with no bridging lemma.
* Part (1) of Tag 01ZM is `AlgebraicGeometry.LimitDescent.hasFinitePresentationModels`, which is
  unconditional. It is stated in the `CategoryTheory.Over` idiom and at an index category in the
  universe of the schemes, while `h01ZM` is stated with explicit pullbacks; the first theorem
  below is that conversion, and it is the only reason the index type here is `Type u` rather than
  an arbitrary `Type v`.

## Main results

* `AlgebraicGeometry.LimitNoetherianSituation.exists_finitePresentationModel_pullbackIso`: part
  (1) of Tag 01ZM in the shape `h01ZM` consumes, for an index type in the universe of the
  schemes.
* `AlgebraicGeometry.LimitNoetherianSituation.nonempty_goodDiagram_of_isOneAffineOpenStep`:
  **Tag 0CNN granted the single-affine step.**
* `AlgebraicGeometry.LimitNoetherianSituation.nonempty_goodDiagram_id`: a good diagram for the
  identity on the limit, unconditionally.
* `nonempty_goodDiagram_of_isOneAffineOpenStep_of_isAffineHom`, in the same namespace: the
  hypothesis set of the theorem above realised at every affine morphism of finite type into an
  affine scheme.

## Implementation notes

**Tag 0CNN is proved here only conditionally.** The tag asserts the existence of the diagram
outright, while the theorem below carries the single-affine step as a hypothesis. Nothing here
states a clause of Tag 07RN either, which asserts the whole of absolute Noetherian approximation.

**The two argument orders of the pullback.** Part (1) of Tag 01ZM produces an isomorphism of
objects of `CategoryTheory.Over S`, whose underlying object is `pullback Xᵢ.hom (c.π.app i)` with
`CategoryTheory.Limits.pullback.snd` as its structure morphism, while `h01ZM` asks for
`pullback (c.π.app i) Xᵢ.hom` with `CategoryTheory.Limits.pullback.fst`. The two are crossed by
`CategoryTheory.Limits.pullbackSymmetry`, whose compatibility
`CategoryTheory.Limits.pullbackSymmetry_hom_comp_fst` turns the `Over`-morphism condition
`CategoryTheory.Over.w` into the required equation. There is no comparison of schemes to make.

**Why the index universe is restricted, and why nothing else is.** The smallness that
`AlgebraicGeometry.LimitNoetherianSituation.quasiSeparatedSpace_limitScheme` and its siblings
carry is free here, because an index type in the universe of the schemes is essentially small;
so the restriction to `Type u` is imposed by part (1) of Tag 01ZM alone, and the limit scheme's
quasi-compactness and quasi-separatedness cost nothing. The affine Noetherian approximation of
`AlgebraicGeometry.specLimitNoetherianSituation` produces its situation at precisely this index
shape, which is why the realisation corollary below can be stated at all.

**Non-vacuity.** `AlgebraicGeometry.LimitNoetherianSituation.GoodDiagram` is quantified over by
many declarations, so an inhabitant matters: `nonempty_goodDiagram_id` supplies one with no
hypothesis at all, by taking the model to be the stage itself. It is degenerate — the closed
immersion it exhibits is an isomorphism — so it establishes only that the structure is inhabited,
and exercises none of the content of Tag 0CNN. The realisation corollary is the non-degenerate
statement, and it is conditional on the single-affine step.
-/

universe u

open CategoryTheory Limits Opposite

@[expose] public section

namespace AlgebraicGeometry.LimitNoetherianSituation

variable {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]

/-- **Part (1) of [Stacks, Tag 01ZM], in the shape the proof of [Stacks, Tag 0CNN] consumes.**
Every scheme of finite presentation over the limit of a limit-Noetherian situation is, up to
isomorphism over the limit, the base change of one of finite presentation over a stage.

This is `AlgebraicGeometry.LimitDescent.hasFinitePresentationModels` rewritten from the
`CategoryTheory.Over` idiom into explicit pullbacks; see the implementation notes for the
argument order. The content is that theorem's; this is a restatement of it. -/
@[sga "3 VIB 10.0" "(ii), special case", sga "4 VII 5.2" "b: noetherian stages"]
theorem exists_finitePresentationModel_pullbackIso (D : LimitNoetherianSituation.{u, u} I)
    (X' : Scheme.{u}) (p : X' ⟶ D.limitScheme) (hp : FinitePresentation p) :
    ∃ (j : I) (W : Scheme.{u}) (w : W ⟶ D.system.obj (op j)) (_ : FinitePresentation w)
      (e : X' ≅ pullback (D.limitCone.π.app (op j)) w),
      e.hom ≫ pullback.fst (D.limitCone.π.app (op j)) w = p := by
  have haff : ∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (D.system.map a) := fun a ↦
    D.transition_affine a
  have hcs : ∀ i : Iᵒᵖ, CompactSpace (D.system.obj i) := fun i ↦
    have := D.noetherian i.unop; inferInstance
  have hqs : ∀ i : Iᵒᵖ, QuasiSeparatedSpace (D.system.obj i) := fun i ↦
    have := D.noetherian i.unop; inferInstance
  obtain ⟨i, Xi, hXi, ⟨e⟩⟩ :=
    LimitDescent.hasFinitePresentationModels.{u} D.system D.limitCone D.isLimit (Over.mk p) hp
  refine ⟨i.unop, Xi.left, Xi.hom, hXi,
    (Over.forget _).mapIso e ≪≫ pullbackSymmetry Xi.hom (D.limitCone.π.app i), ?_⟩
  show ((Over.forget _).mapIso e).hom ≫
      (pullbackSymmetry Xi.hom (D.limitCone.π.app i)).hom ≫
      pullback.fst (D.limitCone.π.app i) Xi.hom = p
  rw [pullbackSymmetry_hom_comp_fst]
  exact Over.w e.hom

/-- **[Stacks, Tag 0CNN], granted the single-affine step of Noetherian approximation.** In
Situation [Stacks, Tag 0CNM], a quasi-separated morphism of finite type from `X` to the limit
scheme fits into a diagram over a finite stage whose model is of finite type and for which the
induced morphism to the base change is a closed immersion.

The single hypothesis beyond those of the tag is
`AlgebraicGeometry.Scheme.FiniteTypeApproximation.IsOneAffineOpenStep`, which enters through
[Stacks, Tag 01ZG] and nowhere else; part (1) of [Stacks, Tag 01ZM] is unconditional. The
tag itself asserts the conclusion outright. -/
theorem nonempty_goodDiagram_of_isOneAffineOpenStep
    (hstep : Scheme.FiniteTypeApproximation.IsOneAffineOpenStep.{u})
    (D : LimitNoetherianSituation.{u, u} I) {X : Scheme.{u}} (f : X ⟶ D.limitScheme)
    [LocallyOfFiniteType f] [QuasiCompact f] [QuasiSeparated f] :
    Nonempty (GoodDiagram D f) := by
  have : CompactSpace X := D.compactSpace_of_quasiCompact_toLimitScheme f
  have : QuasiSeparatedSpace X := D.quasiSeparatedSpace_of_quasiSeparated_toLimitScheme f
  have : QuasiSeparatedSpace D.limitScheme := D.quasiSeparatedSpace_limitScheme
  exact nonempty_goodDiagram_of_exists_model D
    (exists_finitePresentation_isClosedImmersion_of_isOneAffineOpenStep hstep f)
    (fun X' p hp ↦ D.exists_finitePresentationModel_pullbackIso X' p hp)

/-- **A good diagram exists for the identity on the limit scheme**, with no hypothesis beyond
Situation [Stacks, Tag 0CNM]: take any stage, let the model be that stage with its identity
morphism, and observe that the first projection out of `S ×_{Sᵢ} Sᵢ` is an isomorphism.

This is the non-vacuity witness for `AlgebraicGeometry.LimitNoetherianSituation.GoodDiagram`.
It is deliberately degenerate and exercises none of the content of [Stacks, Tag 0CNN]; the
realisation corollary below is the non-degenerate statement. -/
theorem nonempty_goodDiagram_id (D : LimitNoetherianSituation.{u, u} I) :
    Nonempty (GoodDiagram D (𝟙 D.limitScheme)) := by
  obtain ⟨j⟩ : Nonempty I := inferInstance
  refine nonempty_goodDiagram_of_isClosedImmersion D j (𝟙 (D.system.obj (op j)))
    inferInstance inferInstance
    (inv (pullback.fst (D.limitCone.π.app (op j)) (𝟙 (D.system.obj (op j))))) ?_ ?_
  · infer_instance
  · exact IsIso.inv_hom_id _

/-- **The hypothesis set of `nonempty_goodDiagram_of_isOneAffineOpenStep` is realised at every
affine morphism of finite type into an affine scheme.** The situation is the affine Noetherian
approximation `AlgebraicGeometry.specLimitNoetherianSituation`, whose limit scheme is `Spec R`
by definition; an affine morphism is quasi-compact and quasi-separated, so the three instances
the theorem asks for are supplied by `[IsAffineHom f]` alone.

Granted the single-affine step, therefore, every such morphism has a good diagram. The source
need not be affine and the morphism need not be an immersion, so this realisation is not the
degenerate one of `nonempty_goodDiagram_id`. -/
theorem nonempty_goodDiagram_of_isOneAffineOpenStep_of_isAffineHom
    (hstep : Scheme.FiniteTypeApproximation.IsOneAffineOpenStep.{u})
    (R : Type u) [CommRing R] {X : Scheme.{u}}
    (f : X ⟶ (specLimitNoetherianSituation R).limitScheme)
    [IsAffineHom f] [LocallyOfFiniteType f] :
    Nonempty (GoodDiagram (specLimitNoetherianSituation R) f) :=
  nonempty_goodDiagram_of_isOneAffineOpenStep hstep (specLimitNoetherianSituation R) f

end AlgebraicGeometry.LimitNoetherianSituation

end
