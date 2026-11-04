module

public import StacksFrontier.AlgebraicGeometry.Descent.Finiteness.ClosedImmersionLimit
public import StacksFrontier.AlgebraicGeometry.Descent.Finiteness.ImmersionIntoFinitePresentation
public import StacksFrontier.AlgebraicGeometry.FiniteTypeClosedInFinitePresentation.Glueing
public import StacksFrontier.AlgebraicGeometry.ProperFinitePresentationLimit.Basic
public import StacksFrontier.AlgebraicGeometry.Limits.EventuallySeparatedOverBase

/-!
# A morphism of finite type as a limit of morphisms of finite presentation

Let `f : X ⟶ S` be locally of finite type with `X` quasi-compact and quasi-separated and `S`
quasi-separated. Limits, Tag 09ZQ writes `X` as the limit of an inverse system of
quasi-compact quasi-separated schemes of finite presentation over `S` whose transition morphisms,
and whose projections from `X`, are closed immersions. If moreover `f` is separated and `S` is
quasi-compact, Limits, Proposition 01ZJ says that one of those stages is *separated* over `S`,
so that `f` factors as a closed immersion into a separated morphism of finite presentation.

Both are assembled here out of pieces already in the library, on the single hypothesis
`AlgebraicGeometry.Scheme.FiniteTypeApproximation.IsOneAffineOpenStep` — the single-affine step of
Noetherian approximation, Limits, Tag 07RN — which is what the library's form of Tag 01ZG carries.
The three pieces are:

* Tag 01ZG, `AlgebraicGeometry.exists_finitePresentation_isClosedImmersion_of_isOneAffineOpenStep`,
  for the closed immersion `X ⟶ Y` into a scheme of finite presentation over `S`;
* Tag 09ZP, `AlgebraicGeometry.isLimit_finitePresentationCone_of_qcqs`, read through the diagram
  of `StacksFrontier/AlgebraicGeometry/ProperFinitePresentationLimit/Basic.lean`, for the system
  of finite-presentation closed subschemes of `Y` containing `X`;
* Tag 01ZH, `AlgebraicGeometry.eventually_isSeparated_app`, for the separatedness of a late stage.

## Main definitions

* `AlgebraicGeometry.properStageSituation`: the system of Tag 09ZP packaged as an
  `AlgebraicGeometry.DescentSituation`, which is the shape Tag 01ZH consumes.

## Main results

* `AlgebraicGeometry.exists_qcqs_finitePresentation_isClosedImmersion_of_isOneAffineOpenStep`:
  Tag 01ZG with the quasi-compactness and quasi-separatedness of the constructed scheme
  **retained**; see the implementation notes.
* `AlgebraicGeometry.exists_finitePresentation_isLimit_of_isOneAffineOpenStep`: the conclusion of
  **Limits, Tag 09ZQ**.
* `AlgebraicGeometry.exists_isLimit_finitePresentation_isClosedImmersion`: **Limits, Tag 09ZQ**
  itself, with the index of the system exhibited as a directed preorder.
* `exists_isSeparated_finitePresentation_isClosedImmersion_of_isOneAffineOpenStep`, in the
  `AlgebraicGeometry` namespace: the conclusion of **Limits, Proposition 01ZJ**.

## Implementation notes

**The library's form of Tag 01ZG drops two fields its own proof produces, and Tag 09ZP needs both
of them.** `AlgebraicGeometry.exists_finitePresentation_isClosedImmersion_of_exists_immersion`
forgets the `CompactSpace` and `QuasiSeparatedSpace` of the scheme it constructs; its predecessor
`AlgebraicGeometry.exists_qcqs_finitePresentation_isClosedImmersion_of_exists_immersion` returns
them; Tag 09ZP asks for a quasi-compact quasi-separated ambient scheme, so the first result below
goes back to the predecessor. That is also why no quasi-compact open of `Y` has to be carved out,
as the Stacks proof of Tag 09ZQ does: the construction already returns a quasi-compact `Y`.

`AlgebraicGeometry.isDirected_finitePresentationSubscheme` is declared here because the fact was
only available as a `have` inside the proof of
`Stacks.Flatness.finitePresentationSubscheme_isFiltered`, and
`AlgebraicGeometry.DescentSituation` takes it as an instance argument of its *type*, so no
tactic-level `haveI` can supply it.

**No Stacks attribute is attached to the three `_of_isOneAffineOpenStep` statements.** Each
carries `AlgebraicGeometry.Scheme.FiniteTypeApproximation.IsOneAffineOpenStep` as a hypothesis,
which none of the three tags has, and withholding is the same decision — for the same reason — as
`StacksFrontier/AlgebraicGeometry/FiniteTypeClosedInFinitePresentation/Glueing.lean` makes for
Tags 01ZE and 01ZG. With that step proved these statements give the tags with the hypothesis
deleted and nothing else changed.

Tag 09ZQ itself is proved unconditionally by
`AlgebraicGeometry.exists_isLimit_finitePresentation_isClosedImmersion`, which goes instead
through the hypothesis-free Tag 01ZE,
`AlgebraicGeometry.exists_finitePresentation_isImmersion`, and reads the system off Tag 09ZP in
the form `AlgebraicGeometry.exists_isLimit_closedImmersion_finitePresentation`. Its conclusion
presents the index as a directed preorder, as the tag does, rather than as an abstract cofiltered
category, which is all the `_of_isOneAffineOpenStep` form above records; in every other respect
the two statements agree.

## References

* [Stacks Project, Tag 09ZQ](https://stacks.math.columbia.edu/tag/09ZQ)
* [Stacks Project, Tag 01ZJ](https://stacks.math.columbia.edu/tag/01ZJ)
* [Stacks Project, Tag 01ZG](https://stacks.math.columbia.edu/tag/01ZG)
* [Stacks Project, Tag 09ZP](https://stacks.math.columbia.edu/tag/09ZP)
* [Stacks Project, Tag 01ZH](https://stacks.math.columbia.edu/tag/01ZH)
* [Stacks Project, Tag 07RN](https://stacks.math.columbia.edu/tag/07RN)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Stacks.Flatness

universe u

namespace AlgebraicGeometry

/-- **The finite-presentation closed enlargements of a closed subscheme are a directed set.**
This is the `IsDirected` half of `Stacks.Flatness.finitePresentationSubscheme_isFiltered`, which
proves it as a step inside its own proof and so does not make it available to instance search. -/
instance isDirected_finitePresentationSubscheme {Y : Scheme.{u}} (K : Y.IdealSheafData) :
    IsDirected (FinitePresentationSubscheme K) (· ≤ ·) :=
  ⟨fun J H ↦ ⟨⟨J.1 ⊔ H.1, finitePresentation_subschemeι_sup J.2.1 H.2.1, sup_le J.2.2 H.2.2⟩,
    Subtype.coe_le_coe.mp le_sup_left, Subtype.coe_le_coe.mp le_sup_right⟩⟩

variable {X Y S : Scheme.{u}}

/-- **The system of [Stacks, Tag 09ZP] as a descent situation.** For a closed immersion
`j : X ⟶ Y` with `Y` quasi-compact and quasi-separated, the inverse system of the
finite-presentation closed subschemes of `Y` containing `X`, with its limit cone at `X`.

The transition morphisms are closed immersions, hence affine; every stage is a closed subscheme
of `Y` and so inherits quasi-compactness and quasi-separatedness from it; and the limit is
[Stacks, Tag 09ZP]. The base point is the zero ideal sheaf, i.e. `Y` itself. -/
def properStageSituation (j : X ⟶ Y) [IsClosedImmersion j] [CompactSpace Y]
    [QuasiSeparatedSpace Y] : DescentSituation.{u, u} (FinitePresentationSubscheme j.ker) where
  system := properStageDiagram j
  transition_affine {_ _} g :=
    have := isClosedImmersion_subschemeDiagram_map j.ker g
    inferInstanceAs (IsAffineHom ((subschemeDiagram j.ker).map g).left)
  quasiCompact i :=
    QuasiCompact.compactSpace_of_compactSpace ((subschemeDiagram j.ker).obj (op i)).hom
  quasiSeparated i :=
    quasiSeparatedSpace_of_quasiSeparated ((subschemeDiagram j.ker).obj (op i)).hom
  limitCone := Cone.mk X (properStageCone j)
  isLimit := isLimit_properStageCone j
  base := ⟨⊥, finitePresentation_subschemeι_bot, bot_le⟩

/-- Each leg of the cone of `AlgebraicGeometry.properStageSituation`, followed by the structure
morphism of its stage over `S`, is the composite `j ≫ p`. This is
`AlgebraicGeometry.properStageCone_comp_properStageStructure` read at one object. -/
theorem properStageCone_app_comp_properStageStructure_app (j : X ⟶ Y) [IsClosedImmersion j]
    (p : Y ⟶ S) (i : (FinitePresentationSubscheme j.ker)ᵒᵖ) :
    (properStageCone j).app i ≫ (properStageStructure j p).app i = j ≫ p := by
  simpa using NatTrans.congr_app (properStageCone_comp_properStageStructure j p) i

/-- **The conclusion of [Stacks, Tag 01ZG] with the quasi-compactness and quasi-separatedness of
the constructed scheme retained**, granted the single-affine step of Noetherian approximation.

This is `AlgebraicGeometry.exists_finitePresentation_isImmersion_of_isOneAffineOpenStep` fed to
`AlgebraicGeometry.exists_qcqs_finitePresentation_isClosedImmersion_of_exists_immersion` rather
than to the weaker `…_isClosedImmersion_of_exists_immersion`, which forgets the two topological
conclusions; [Stacks, Tag 09ZP] needs them. -/
theorem exists_qcqs_finitePresentation_isClosedImmersion_of_isOneAffineOpenStep
    (hstep : Scheme.FiniteTypeApproximation.IsOneAffineOpenStep.{u})
    (f : X ⟶ S) [LocallyOfFiniteType f]
    [CompactSpace X] [QuasiSeparatedSpace X] [QuasiSeparatedSpace S] :
    ∃ (X' : Scheme.{u}) (p : X' ⟶ S) (ι : X ⟶ X'),
      FinitePresentation p ∧ IsClosedImmersion ι ∧ ι ≫ p = f ∧
        CompactSpace X' ∧ QuasiSeparatedSpace X' :=
  exists_qcqs_finitePresentation_isClosedImmersion_of_exists_immersion f
    (exists_finitePresentation_isImmersion_of_isOneAffineOpenStep hstep f)

/-- **The conclusion of [Stacks, Tag 09ZQ]**, granted the single-affine step of Noetherian
approximation. A morphism `f : X ⟶ S` locally of finite type, with `X` quasi-compact and
quasi-separated and `S` quasi-separated, presents `X` as the limit of an inverse system of
quasi-compact quasi-separated schemes of finite presentation over `S` whose transition morphisms
and whose projections from `X` are closed immersions.

The system is the finite-presentation closed subschemes of the ambient scheme of Tag 01ZG which
contain `X`, and the limit is [Stacks, Tag 09ZP]. No attribute is attached; see the
implementation notes. -/
theorem exists_finitePresentation_isLimit_of_isOneAffineOpenStep
    (hstep : Scheme.FiniteTypeApproximation.IsOneAffineOpenStep.{u})
    (f : X ⟶ S) [LocallyOfFiniteType f]
    [CompactSpace X] [QuasiSeparatedSpace X] [QuasiSeparatedSpace S] :
    ∃ (I : Type u) (_ : SmallCategory I) (_ : IsCofiltered I) (D : I ⥤ Scheme.{u})
      (t : D ⟶ (Functor.const I).obj S) (π : (Functor.const I).obj X ⟶ D)
      (_ : IsLimit (Cone.mk X π)),
      (∀ i : I, FinitePresentation (t.app i)) ∧ (∀ i : I, CompactSpace (D.obj i)) ∧
        (∀ i : I, QuasiSeparatedSpace (D.obj i)) ∧
        (∀ (i i' : I) (g : i ⟶ i'), IsClosedImmersion (D.map g)) ∧
        (∀ i : I, IsClosedImmersion (π.app i)) ∧ π ≫ t = (Functor.const I).map f := by
  obtain ⟨Y, p, ι, hp, hι, hfac, hYc, hYq⟩ :=
    exists_qcqs_finitePresentation_isClosedImmersion_of_isOneAffineOpenStep hstep f
  have := hι
  have := hYc
  have := hYq
  refine ⟨(FinitePresentationSubscheme ι.ker)ᵒᵖ, inferInstance,
    isCofiltered_finitePresentationSubscheme_op ι.ker, properStageDiagram ι,
    properStageStructure ι p, properStageCone ι, isLimit_properStageCone ι,
    fun i => finitePresentation_properStageStructure_app ι p hp i,
    fun i => QuasiCompact.compactSpace_of_compactSpace ((subschemeDiagram ι.ker).obj i).hom,
    fun i => quasiSeparatedSpace_of_quasiSeparated ((subschemeDiagram ι.ker).obj i).hom,
    fun _ _ g => isClosedImmersion_subschemeDiagram_map ι.ker g,
    fun i => isClosedImmersion_properStageCone_app ι i, ?_⟩
  rw [properStageCone_comp_properStageStructure ι p, hfac]

/-- **Stacks, Tag 09ZQ.** A morphism `f : X ⟶ S` locally of finite type, with `X` quasi-compact
and quasi-separated and `S` quasi-separated, presents `X` as the limit of a directed inverse
system of quasi-compact quasi-separated schemes of finite presentation over `S` whose transition
morphisms, and whose projections from `X`, are closed immersions.

[Stacks, Tag 01ZE] immerses `X` over `S` into a scheme of finite presentation over `S`, and
`AlgebraicGeometry.exists_qcqs_finitePresentation_isClosedImmersion_of_exists_immersion` converts
that immersion into a closed immersion `j : X ⟶ Y` with `Y` quasi-compact, quasi-separated and of
finite presentation over `S`. [Stacks, Tag 09ZP] then writes `X` as the directed inverse limit
over `Y` of those closed subschemes of `Y` containing `X` whose closed immersion into `Y` is of
finite presentation. Composing the structure morphisms of that system with `Y ⟶ S` leaves them of
finite presentation; every stage, being a closed subscheme of `Y`, inherits quasi-compactness and
quasi-separatedness from `Y`; and both the transition morphisms and the projections from `X` are
closed immersions because their composites with the closed immersions into `Y` are. -/
@[stacks 09ZQ]
theorem exists_isLimit_finitePresentation_isClosedImmersion (f : X ⟶ S) [LocallyOfFiniteType f]
    [CompactSpace X] [QuasiSeparatedSpace X] [QuasiSeparatedSpace S] :
    ∃ (I : Type u) (_ : Preorder I) (_ : Nonempty I) (_ : IsDirected I (· ≤ ·))
      (D : Iᵒᵖ ⥤ Scheme.{u}) (t : D ⟶ (Functor.const Iᵒᵖ).obj S)
      (p : (Functor.const Iᵒᵖ).obj X ⟶ D) (_ : IsLimit (Cone.mk X p)),
      p ≫ t = (Functor.const Iᵒᵖ).map f ∧
        (∀ i, FinitePresentation (t.app i) ∧ CompactSpace (D.obj i) ∧
          QuasiSeparatedSpace (D.obj i)) ∧
        (∀ (i i' : Iᵒᵖ) (g : i ⟶ i'), IsClosedImmersion (D.map g)) ∧
        ∀ i, IsClosedImmersion (p.app i) := by
  obtain ⟨Y, q, j, hq, hj, hjq, hYc, hYq⟩ :=
    exists_qcqs_finitePresentation_isClosedImmersion_of_exists_immersion f
      (exists_finitePresentation_isImmersion f)
  have := hj
  have := hYc
  have := hYq
  obtain ⟨I, hpre, hne, hdir, D, tY, p, hlim, hbase, hstage⟩ :=
    exists_isLimit_closedImmersion_finitePresentation j
  have hproj (i : Iᵒᵖ) : p.app i ≫ tY.app i = j := by
    simpa using congrArg (fun α ↦ α.app i) hbase
  have hcancel : ∀ {A B : Scheme.{u}} (a : A ⟶ B) (b : B ⟶ Y) (c : A ⟶ Y), a ≫ b = c →
      IsClosedImmersion b → IsClosedImmersion c → IsClosedImmersion a := by
    rintro A B a b _ rfl _ _
    exact IsClosedImmersion.of_comp a b
  refine ⟨I, hpre, hne, hdir, D, tY ≫ (Functor.const Iᵒᵖ).map q, p, hlim, ?_, ?_, ?_, ?_⟩
  · ext i
    show p.app i ≫ tY.app i ≫ q = f
    rw [← Category.assoc, hproj, hjq]
  · intro i
    have hfp : FinitePresentation (tY.app i) := (hstage i).2
    refine ⟨?_, ?_, ?_⟩
    · show FinitePresentation (tY.app i ≫ q)
      exact hfp.comp hq
    · exact @QuasiCompact.compactSpace_of_compactSpace _ _ (tY.app i) hfp.quasiCompact hYc
    · exact @quasiSeparatedSpace_of_quasiSeparated _ _ (tY.app i) hYq hfp.quasiSeparated
  · intro i i' g
    exact hcancel _ _ _ (by simp [tY.naturality g]) (hstage i').1 (hstage i).1
  · intro i
    exact hcancel _ _ _ (hproj i) (hstage i).1 hj

/-- **The conclusion of [Stacks, Proposition 01ZJ]**, granted the single-affine step of
Noetherian approximation. A separated morphism of finite type onto a quasi-compact
quasi-separated scheme factors as a closed immersion followed by a *separated* morphism of
finite presentation.

The system of Tag 09ZQ is `AlgebraicGeometry.properStageSituation`; [Stacks, Tag 01ZH],
`AlgebraicGeometry.eventually_isSeparated_app`, makes a late stage separated over `S`, and the
first such stage is the scheme asked for. No attribute is attached; see the implementation
notes. -/
theorem exists_isSeparated_finitePresentation_isClosedImmersion_of_isOneAffineOpenStep
    (hstep : Scheme.FiniteTypeApproximation.IsOneAffineOpenStep.{u})
    (f : X ⟶ S) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [CompactSpace S] [QuasiSeparatedSpace S] :
    ∃ (X' : Scheme.{u}) (p : X' ⟶ S) (ι : X ⟶ X'),
      FinitePresentation p ∧ IsSeparated p ∧ IsClosedImmersion ι ∧ ι ≫ p = f := by
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated f
  obtain ⟨Y, p, ι, hp, hι, hfac, hYc, hYq⟩ :=
    exists_qcqs_finitePresentation_isClosedImmersion_of_isOneAffineOpenStep hstep f
  have := hι
  have := hYc
  have := hYq
  have hsep : IsSeparated ((properStageCone ι).app (op (properStageSituation ι).base) ≫
      (properStageStructure ι p).app (op (properStageSituation ι).base)) := by
    rw [properStageCone_app_comp_properStageStructure_app ι p, hfac]
    infer_instance
  obtain ⟨i₀, hi₀⟩ :=
    eventually_isSeparated_app (properStageSituation ι) (properStageStructure ι p) hsep
  refine ⟨(properStageDiagram ι).obj (op i₀), (properStageStructure ι p).app (op i₀),
    (properStageCone ι).app (op i₀),
    finitePresentation_properStageStructure_app ι p hp _, hi₀ i₀ le_rfl,
    isClosedImmersion_properStageCone_app ι _, ?_⟩
  rw [properStageCone_app_comp_properStageStructure_app ι p, hfac]

end AlgebraicGeometry

end
