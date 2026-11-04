module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Limits.AbsoluteNoetherianApproximation
public import StacksFrontier.AlgebraicGeometry.Limits.GoodDiagramFromStep
public import StacksFrontier.AlgebraicGeometry.Limits.ImageSystemLimit
public import StacksFrontier.AlgebraicGeometry.Limits.ProperFinitePresentationLimit
public import StacksFrontier.AlgebraicGeometry.Limits.ProperImageSystemModels

/-!
# A proper morphism as a limit of proper morphisms over bases of finite type over the integers

A proper morphism onto a quasi-compact and quasi-separated scheme is the inverse limit of a
directed system of proper morphisms whose targets are of finite type over `ℤ` and whose
transition morphisms are affine on both sources and targets.

## Main results

* `AlgebraicGeometry.exists_isLimit_isProper_finiteType_arrow`: **Stacks 0A0P**.
* `AlgebraicGeometry.LimitNoetherianSituation.eventually_isProper_morphismAt`: the conclusion of
  [Stacks, Tag 0CNV] with no hypothesis beyond the tag's own, the factorisation it needs being
  supplied by [Stacks, Tag 09ZR].
* `AlgebraicGeometry.LimitNoetherianSituation.GoodDiagram.finiteType_terminalFrom_image`: the
  stages of the image system of a good diagram are of finite type over `ℤ` whenever the stages of
  the base system are.

## Implementation notes

The inverse system is the pair of image systems of two good diagrams over one absolute Noetherian
approximation of the base. Writing `S = lim Sⱼ` with every `Sⱼ` of finite type over `ℤ` and every
transition affine ([Stacks, Tag 01ZA]), a good diagram ([Stacks, Tag 0CNN]) for `f : X ⟶ S` and
the degenerate good diagram for `𝟙 S` have image systems with limits `X` and `S`
([Stacks, Tag 0CNQ]); [Stacks, Tag 0CNR] produces a morphism between those systems inducing `f`,
and [Stacks, Tag 0CNV] makes its components proper from some stage onwards. Restricting to that
tail and reindexing it by a directed preorder gives the system, and the two image cones are
jointly a limiting cone in the arrow category.

**Tag 0CNV is unconditional here.** The library's
`AlgebraicGeometry.LimitNoetherianSituation.eventually_isProper_morphismAt_of_exists_factorisation`
asks for the factorisation of `f` as a closed immersion followed by a proper morphism of finite
presentation, and does not carry `@[stacks 0CNV]` itself. [Stacks, Tag 09ZR] is available as
`AlgebraicGeometry.exists_isClosedImmersion_isProper_finitePresentation`, which supplies the
factorisation over a quasi-compact quasi-separated target and so discharges the hypothesis
outright.

The three order-theoretic auxiliaries below — that the opposite of a directed preorder is
cofiltered, that `CategoryTheory.Over.map` along a transition is initial, and that a cofiltered
essentially small category is the target of an initial functor out of the opposite of a directed
preorder — are proved here rather than reused because the available forms are stated for the over
categories of a *scheme* system rather than of the index preorder itself.

Each stage of the image system of a good diagram is a closed subscheme of a base change of the
diagram's model, which is of finite type over the base stage, so finite type over `ℤ` propagates
from the base system to the image system by composition; that is
`GoodDiagram.finiteType_terminalFrom_image`. Affineness of the transition morphisms is already
`AlgebraicGeometry.LimitNoetherianSituation.GoodDiagram.isAffineHom_imageSystem`.

## References

* [Stacks Project, Tag 0A0P](https://stacks.math.columbia.edu/tag/0A0P)
* [Stacks Project, Tag 01ZA](https://stacks.math.columbia.edu/tag/01ZA)
* [Stacks Project, Tag 09ZR](https://stacks.math.columbia.edu/tag/09ZR)
* [Stacks Project, Tag 0CNM](https://stacks.math.columbia.edu/tag/0CNM)
* [Stacks Project, Tag 0CNN](https://stacks.math.columbia.edu/tag/0CNN)
* [Stacks Project, Tag 0CNQ](https://stacks.math.columbia.edu/tag/0CNQ)
* [Stacks Project, Tag 0CNR](https://stacks.math.columbia.edu/tag/0CNR)
* [Stacks Project, Tag 0CNV](https://stacks.math.columbia.edu/tag/0CNV)
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry

/-! ### Order-theoretic auxiliaries -/

/-- The opposite of a directed preorder is cofiltered, or empty. -/
theorem isCofilteredOrEmpty_opposite_of_isDirected {I : Type u} [Preorder I]
    [IsDirected I (· ≤ ·)] : IsCofilteredOrEmpty Iᵒᵖ where
  cone_objs A B := by
    obtain ⟨k, hA, hB⟩ := @IsDirected.directed I (· ≤ ·) inferInstance A.unop B.unop
    exact ⟨op k, (homOfLE hA).op, (homOfLE hB).op, trivial⟩
  cone_maps A B g h := by
    refine ⟨A, 𝟙 A, ?_⟩
    simp only [Category.id_comp]
    exact Subsingleton.elim _ _

/-- Pushing forward along a transition morphism of a directed preorder is an initial functor
between the over categories of its opposite. -/
theorem initial_overMap_of_isDirected {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    {i j : I} (hij : i ≤ j) :
    (Over.map ((homOfLE hij).op) : Over (op j) ⥤ Over (op i)).Initial := by
  let : IsCofilteredOrEmpty Iᵒᵖ := isCofilteredOrEmpty_opposite_of_isDirected
  let : IsCofiltered (Over (op j)) := inferInstance
  refine Functor.initial_of_exists_of_isCofiltered
    (F := (Over.map ((homOfLE hij).op) : Over (op j) ⥤ Over (op i))) ?_ ?_
  · intro Y
    obtain ⟨k, hjk, hYk⟩ := @IsDirected.directed I (· ≤ ·) inferInstance j Y.left.unop
    exact ⟨Over.mk ((homOfLE hjk).op), ⟨Over.homMk ((homOfLE hYk).op)⟩⟩
  · intro Y Z g h
    refine ⟨Z, 𝟙 Z, ?_⟩
    simpa only [Functor.map_id, Category.id_comp] using
      Over.OverMorphism.ext (Subsingleton.elim _ _)

/-- A cofiltered category whose objects and morphisms live in one universe receives an initial
functor from the opposite of a directed preorder in that universe. -/
theorem exists_isDirectedOrder_initial {C : Type u} [Category.{u} C] [IsCofiltered C] :
    ∃ (K : Type u) (_ : Preorder K) (_ : Nonempty K) (_ : IsDirectedOrder K)
      (F : Kᵒᵖ ⥤ C), F.Initial := by
  let : IsFiltered Cᵒᵖ := inferInstance
  obtain ⟨K, hpo, hdir, hne, F, hfinal⟩ := IsFiltered.exists_directed Cᵒᵖ
  let : PartialOrder K := hpo
  let : IsDirected K (· ≤ ·) := hdir
  let : Nonempty K := hne
  let : F.Final := hfinal
  exact ⟨K, inferInstance, hne, IsFiltered.isDirectedOrder K,
    F.op ⋙ (opOpEquivalence C).functor,
    Functor.initial_comp_equivalence F.op (opOpEquivalence C).functor⟩

/-! ### Finite type over the integers for the stages of an image system -/

namespace LimitNoetherianSituation

namespace GoodDiagram

/-- **The stages of the image system of a good diagram are of finite type over `ℤ`** as soon as
the stages of the base system are. A stage is a closed subscheme of a base change of the
diagram's model, which is of finite type over a stage of the base system. -/
theorem finiteType_terminalFrom_image {I : Type u} [Preorder I] [Nonempty I]
    [IsDirected I (· ≤ ·)] (D : LimitNoetherianSituation.{u, u} I) {X : Scheme.{u}}
    {f : X ⟶ D.limitScheme} (G : GoodDiagram D f)
    (hlft : ∀ i : I, LocallyOfFiniteType (terminal.from (D.system.obj (op i))))
    (hqc : ∀ i : I, QuasiCompact (terminal.from (D.system.obj (op i))))
    (j : Over (op G.index)) :
    LocallyOfFiniteType (terminal.from ((stageMap G j).image)) ∧
      QuasiCompact (terminal.from ((stageMap G j).image)) := by
  have _hmlft : LocallyOfFiniteType G.modelMap := G.locallyOfFiniteType
  have _hmqc : QuasiCompact G.modelMap := G.quasiCompact
  have _hblft : LocallyOfFiniteType (terminal.from (D.system.obj j.left)) := hlft j.left.unop
  have _hbqc : QuasiCompact (terminal.from (D.system.obj j.left)) := hqc j.left.unop
  have hP : terminal.from (pullback (D.system.map j.hom) G.modelMap) =
      pullback.fst (D.system.map j.hom) G.modelMap ≫ terminal.from (D.system.obj j.left) :=
    terminalIsTerminal.hom_ext _ _
  have _hPlft : LocallyOfFiniteType
      (terminal.from (pullback (D.system.map j.hom) G.modelMap)) := by
    rw [hP]; infer_instance
  have _hPqc : QuasiCompact (terminal.from (pullback (D.system.map j.hom) G.modelMap)) := by
    rw [hP]; infer_instance
  have hι : terminal.from ((stageMap G j).image) =
      (stageMap G j).imageι ≫ terminal.from (pullback (D.system.map j.hom) G.modelMap) :=
    terminalIsTerminal.hom_ext _ _
  exact ⟨by rw [hι]; infer_instance, by rw [hι]; infer_instance⟩

end GoodDiagram

/-! ### Tag 0CNV -/

/-- **[Stacks, Tag 0CNV].** In Situation [Stacks, Tag 0CNM], the components of a morphism of the
image systems of two good diagrams which induces a proper morphism on the limits are proper from
some stage onwards.

The factorisation of `f` as a closed immersion followed by a proper morphism of finite
presentation, which is the input
`AlgebraicGeometry.LimitNoetherianSituation.eventually_isProper_morphismAt_of_exists_factorisation`
asks for, is [Stacks, Tag 09ZR]. -/
theorem eventually_isProper_morphismAt {I : Type u} [Preorder I] [Nonempty I]
    [IsDirected I (· ≤ ·)] (D : LimitNoetherianSituation.{u, u} I)
    {X Y : Scheme.{u}} {pX : X ⟶ D.limitScheme} {pY : Y ⟶ D.limitScheme}
    (f : X ⟶ Y) (hf : f ≫ pY = pX)
    [QuasiSeparated pX] [LocallyOfFiniteType pX] [QuasiCompact pX]
    [QuasiSeparated pY] [LocallyOfFiniteType pY] [QuasiCompact pY]
    [IsProper f] [CompactSpace D.limitScheme] [QuasiSeparatedSpace D.limitScheme]
    (GX : GoodDiagram D pX) (GY : GoodDiagram D pY)
    (i₀ : I) (hX : GX.index ≤ i₀) (hY : GY.index ≤ i₀)
    (F : MorphismAt D f GX GY i₀ hX hY) :
    ∃ (i₃ : I) (_ : i₀ ≤ i₃),
      ∀ (j : Over (op i₀)), i₃ ≤ unop j.left → IsProper (F.maps.app j) := by
  have _hFS : FinallySmall.{u} I := finallySmall_of_essentiallySmall I
  have _hYc : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace pY
  have _hYq : QuasiSeparatedSpace Y := quasiSeparatedSpace_of_quasiSeparated pY
  exact eventually_isProper_morphismAt_of_exists_factorisation D f hf GX GY i₀ hX hY F
    (exists_isClosedImmersion_isProper_finitePresentation f)

/-- **[Stacks, Tag 0CNV].** In Situation [Stacks, Tag 0CNM], the components of a morphism of the
image systems of two good diagrams which induces a proper morphism on the limits are proper from
some stage onwards.

The limit of the system is quasi-compact and quasi-separated because its stages are Noetherian
and its transition morphisms affine, so no hypothesis on its underlying space is needed. -/
@[stacks 0CNV]
theorem eventually_isProper_morphismAt' {I : Type u} [Preorder I] [Nonempty I]
    [IsDirected I (· ≤ ·)] (D : LimitNoetherianSituation.{u, u} I)
    {X Y : Scheme.{u}} {pX : X ⟶ D.limitScheme} {pY : Y ⟶ D.limitScheme}
    (f : X ⟶ Y) (hf : f ≫ pY = pX)
    [QuasiSeparated pX] [LocallyOfFiniteType pX] [QuasiCompact pX]
    [QuasiSeparated pY] [LocallyOfFiniteType pY] [QuasiCompact pY] [IsProper f]
    (GX : GoodDiagram D pX) (GY : GoodDiagram D pY)
    (i₀ : I) (hX : GX.index ≤ i₀) (hY : GY.index ≤ i₀)
    (F : MorphismAt D f GX GY i₀ hX hY) :
    ∃ (i₃ : I) (_ : i₀ ≤ i₃),
      ∀ (j : Over (op i₀)), i₃ ≤ unop j.left → IsProper (F.maps.app j) :=
  have : EssentiallySmall.{u} I := ⟨⟨I, inferInstance, ⟨CategoryTheory.Equivalence.refl⟩⟩⟩
  have := D.compactSpace_limitScheme
  have := D.quasiSeparatedSpace_limitScheme
  eventually_isProper_morphismAt D f hf GX GY i₀ hX hY F

end LimitNoetherianSituation

/-! ### Tag 0A0P -/

/-- The image cone of a good diagram stays limiting after whiskering by an initial functor. -/
private def isLimit_whisker_imageCone {I : Type u} [Preorder I] [Nonempty I]
    [IsDirected I (· ≤ ·)] (D : LimitNoetherianSituation.{u, u} I) {X : Scheme.{u}}
    (f : X ⟶ D.limitScheme) [QuasiSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (G : LimitNoetherianSituation.GoodDiagram D f)
    {K : Type u} [Category.{u} K] (F : K ⥤ Over (op G.index)) [F.Initial] :
    IsLimit ((LimitNoetherianSituation.GoodDiagram.imageCone G).whisker F) :=
  (Functor.Initial.isLimitWhiskerEquiv F _).symm
    (LimitNoetherianSituation.GoodDiagram.isLimit_imageCone D f G)

/-- **Stacks 0A0P.** A proper morphism onto a quasi-compact and quasi-separated scheme is the
inverse limit, over a directed set, of an inverse system of proper morphisms whose targets are of
finite type over `ℤ` and whose transition morphisms are affine on both sources and targets. -/
@[stacks 0A0P]
theorem exists_isLimit_isProper_finiteType_arrow
    {X S : Scheme.{u}} (f : X ⟶ S) [IsProper f]
    [CompactSpace S] [QuasiSeparatedSpace S] :
    ∃ (I : Type u) (_ : Preorder I) (_ : Nonempty I) (_ : IsDirectedOrder I)
      (D : Iᵒᵖ ⥤ Arrow Scheme.{u}) (c : Cone D),
      (∀ i, IsProper (D.obj i).hom) ∧
      (∀ i,
        LocallyOfFiniteType (terminal.from (D.obj i).right) ∧
          QuasiCompact (terminal.from (D.obj i).right)) ∧
      (∀ {i j : Iᵒᵖ} (g : i ⟶ j),
        IsAffineHom (D.map g).left ∧ IsAffineHom (D.map g).right) ∧
      Nonempty (IsLimit c) ∧ Nonempty (c.pt ≅ Arrow.mk f) := by
  classical
  -- **Step 1** ([Stacks, Tag 01ZA]): an absolute Noetherian approximation of the base.
  obtain ⟨J, _, _, _, B, hBS, hBlft⟩ :=
    Scheme.FiniteTypeApproximation.exists_limitNoetherianSituation_of_isOneAffineOpenStep
      Scheme.FiniteTypeApproximation.isOneAffineOpenStep S
  subst hBS
  have hBqc : ∀ i : J, QuasiCompact (terminal.from (B.system.obj (op i))) := by
    intro i
    have _hn : IsNoetherian (B.system.obj (op i)) := B.noetherian i
    have _hc : CompactSpace (B.system.obj (op i)) := inferInstance
    infer_instance
  let : IsCofilteredOrEmpty (Jᵒᵖ) := isCofilteredOrEmpty_opposite_of_isDirected
  -- **Step 2** ([Stacks, Tag 0CNN]): good diagrams for `f` and for the identity.
  obtain ⟨GX⟩ := LimitNoetherianSituation.nonempty_goodDiagram_of_isOneAffineOpenStep
    Scheme.FiniteTypeApproximation.isOneAffineOpenStep B f
  obtain ⟨GY⟩ := LimitNoetherianSituation.nonempty_goodDiagram_id B
  have hf : f ≫ 𝟙 B.limitScheme = f := Category.comp_id f
  -- **Step 3** ([Stacks, Tag 0CNR]): a morphism of the two image systems inducing `f`.
  obtain ⟨i₀, hX, hY, ⟨M⟩⟩ :=
    LimitNoetherianSituation.exists_morphismAt_of_isLimit B f hf GX GY
      (LimitNoetherianSituation.GoodDiagram.isLimit_imageCone B f GX)
  -- **Step 4** ([Stacks, Tag 0CNV]): its components are proper from some stage onwards.
  obtain ⟨i₃, hi₃, hproper⟩ :=
    LimitNoetherianSituation.eventually_isProper_morphismAt B f hf GX GY i₀ hX hY M
  -- **Step 5**: reindex the tail above `i₃` by a directed preorder.
  let : IsCofiltered (Over (op i₃)) := inferInstance
  obtain ⟨K, _, hKne, hKdir, E, hE⟩ := exists_isDirectedOrder_initial (C := Over (op i₃))
  let : E.Initial := hE
  let R : Over (op i₃) ⥤ Over (op i₀) := Over.map ((homOfLE hi₃).op)
  let : R.Initial := initial_overMap_of_isDirected hi₃
  let HX : Over (op i₀) ⥤ Over (op GX.index) := Over.map ((homOfLE hX).op)
  let HY : Over (op i₀) ⥤ Over (op GY.index) := Over.map ((homOfLE hY).op)
  let : HX.Initial := initial_overMap_of_isDirected hX
  let : HY.Initial := initial_overMap_of_isDirected hY
  let KX : Kᵒᵖ ⥤ Over (op GX.index) := E ⋙ R ⋙ HX
  let KY : Kᵒᵖ ⥤ Over (op GY.index) := E ⋙ R ⋙ HY
  have hER : (E ⋙ R).Initial := Functor.initial_comp E R
  let : (E ⋙ R).Initial := hER
  have hKX : KX.Initial := Functor.initial_comp (E ⋙ R) HX
  have hKY : KY.Initial := Functor.initial_comp (E ⋙ R) HY
  let : KX.Initial := hKX
  let : KY.Initial := hKY
  let SX : Kᵒᵖ ⥤ Scheme.{u} := KX ⋙ LimitNoetherianSituation.GoodDiagram.imageSystem GX
  let SY : Kᵒᵖ ⥤ Scheme.{u} := KY ⋙ LimitNoetherianSituation.GoodDiagram.imageSystem GY
  -- **Step 6**: the system of arrows and its cone.
  let AA : Kᵒᵖ ⥤ Arrow Scheme.{u} :=
    { obj j := Arrow.mk (M.maps.app (R.obj (E.obj j)))
      map := fun {j k} g => Arrow.homMk' (SX.map g) (SY.map g) (by
        simpa [SX, SY, KX, KY, Functor.comp_map] using M.maps.naturality (R.map (E.map g)))
      map_id := fun j => by
        refine Arrow.hom_ext _ _ ?_ ?_
        · exact SX.map_id j
        · exact SY.map_id j
      map_comp := fun {j k l} g h => by
        refine Arrow.hom_ext _ _ ?_ ?_
        · exact SX.map_comp g h
        · exact SY.map_comp g h }
  let cX : Cone SX := (LimitNoetherianSituation.GoodDiagram.imageCone GX).whisker KX
  let cY : Cone SY := (LimitNoetherianSituation.GoodDiagram.imageCone GY).whisker KY
  let c : Cone AA :=
    { pt := Arrow.mk f
      π :=
        { app := fun j => Arrow.homMk' (cX.π.app j) (cY.π.app j) (M.induces (R.obj (E.obj j)))
          naturality := fun j k g => by
            refine Arrow.hom_ext _ _ ?_ ?_
            · exact (Category.id_comp (cX.π.app k)).trans (cX.w g).symm
            · exact (Category.id_comp (cY.π.app k)).trans (cY.w g).symm } }
  have hcX : IsLimit cX := isLimit_whisker_imageCone B f GX KX
  have hcY : IsLimit cY := isLimit_whisker_imageCone B (𝟙 B.limitScheme) GY KY
  have hleft : Arrow.leftFunc.mapCone c = cX := rfl
  have hright : Arrow.rightFunc.mapCone c = cY := rfl
  have hc : IsLimit c := by
    refine Comma.fstSndJointlyReflectLimit ?_ ?_
    · exact hleft.symm ▸ hcX
    · exact hright.symm ▸ hcY
  refine ⟨K, inferInstance, hKne, hKdir, AA, c, ?_, ?_, ?_, ⟨hc⟩, ⟨Iso.refl _⟩⟩
  · intro j
    exact hproper (R.obj (E.obj j)) (leOfHom (E.obj j).hom.unop)
  · intro j
    exact LimitNoetherianSituation.GoodDiagram.finiteType_terminalFrom_image B GY hBlft hBqc
      (KY.obj j)
  · intro j k g
    exact ⟨LimitNoetherianSituation.GoodDiagram.isAffineHom_imageSystem GX hX
        (R.map (E.map g)),
      LimitNoetherianSituation.GoodDiagram.isAffineHom_imageSystem GY hY (R.map (E.map g))⟩

end AlgebraicGeometry

end

end
