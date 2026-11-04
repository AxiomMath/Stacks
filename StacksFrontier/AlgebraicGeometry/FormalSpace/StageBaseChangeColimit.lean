module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.FormalSpectrum
public import StacksFrontier.AlgebraicGeometry.FormalSpace.McQuillan
public import StacksFrontier.CategoryTheory.Sites.FilteredUniversalColimit

/-!
# A sheaf over a formal spectrum is the colimit of its base changes to the stages

Let `R` be a weakly pre-admissible topological ring over `S` and let `V ⟶ Spf R` be a morphism
of fppf sheaves. Then

`V = colim_J (Spec (R ⧸ J) ×_{Spf R} V)`,

the colimit over the weak ideals of definition `J ⊆ R` ordered by reverse inclusion. This is
the step that lets a morphism into a formal spectrum be reconstructed from its stagewise base
changes; Stacks 0AIA is the same phenomenon for a *quasi-compact* source, where a single stage
already suffices.

## Main definitions

* `CategoryTheory.Limits.baseChangeDiagram`: the base change `i ↦ F i ×_{c.pt} V` of a diagram
  along a morphism `V ⟶ c.pt` into the vertex of a cocone over it.
* `CategoryTheory.Limits.baseChangeCocone`: the cocone on that diagram with vertex `V`.
* `CategoryTheory.Limits.coconePointIsoColimitBaseChange`: for a universal colimit cocone,
  `V ≅ colim_i (F i ×_{c.pt} V)`.
* `AlgebraicGeometry.FormalSpace.stageBaseChangeDiagram`: the diagram
  `J ↦ Spec (R ⧸ J) ×_{Spf R} V`.
* `AlgebraicGeometry.FormalSpace.isoColimitStageBaseChange`:
  `V ≅ colim_J (Spec (R ⧸ J) ×_{Spf R} V)`.
* `AlgebraicGeometry.FormalSpace.isoColimitPresentationBaseChange`: the same for an affine
  formal algebraic space given by an arbitrary presentation, in the index shape of Stacks 0AIA.

## Main results

* `CategoryTheory.Limits.isColimitBaseChangeCocone`: the base change of a universal colimit
  cocone along any morphism into its vertex is a colimit cocone.
* `AlgebraicGeometry.FormalSpace.isDirectedOrder_weakIdeals`: the weak ideals of definition of
  a topological ring are directed under reverse inclusion.
* `AlgebraicGeometry.FormalSpace.isUniversalColimit_formalSpectrumDiagram` and
  `AlgebraicGeometry.FormalSpace.isUniversalColimit_presentationDiagram`: the colimit cocones
  presenting a formal spectrum, respectively an arbitrary presented affine formal algebraic
  space, are universal.

## Implementation notes

A colimit cocone is *universal* (`CategoryTheory.Limits.IsUniversalColimit`) exactly when it
stays a colimit after base change, but the definition quantifies over an arbitrary diagram
sitting over the original one by pullback squares. The content of this file is to produce that
diagram for a given morphism `v : V ⟶ c.pt`, as the chosen pullbacks `F i ×_{c.pt} V` with the
first projections as the natural transformation to `F`. Those first projections are equifibered
by the pasting lemma `CategoryTheory.IsPullback.of_right`: the square over `g : i ⟶ j` pastes
with the pullback square defining `F j ×_{c.pt} V` to the pullback square defining
`F i ×_{c.pt} V`.

The canonical diagram of a formal spectrum is filtered — the weak ideals of definition are
directed under reverse inclusion, the intersection of two of them being one again — so its
colimit cocone is universal by
`CategoryTheory.Limits.sheaf_filteredColimit_isUniversalColimit`, and the general statement
applies.

This file is untagged substrate. The source uses the displayed identity inside the proof of
Stacks 0AN8 without giving it a number of its own; it is stated here at the generality that
proof needs — for the canonical quotient system of a weakly pre-admissible topological ring,
and for an arbitrary presentation by affine stages, in both cases against an arbitrary sheaf
over the formal space.

## References

* [Stacks Project, Tag 0AIF](https://stacks.math.columbia.edu/tag/0AIF)
* [Stacks Project, Tag 0AIA](https://stacks.math.columbia.edu/tag/0AIA)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe v₁ v₂ w₁ w₂ u

namespace CategoryTheory.Limits

section BaseChange

variable {Q : Type w₁} [Category.{w₂} Q] [HasPullbacks Q] {I : Type v₁} [Category.{v₂} I]
  {F : I ⥤ Q} (c : Cocone F) {V : Q} (v : V ⟶ c.pt)

/-- The base change of a diagram along a morphism `v : V ⟶ c.pt` into the vertex of a cocone
over it: the stage at `i` is the fibre product `F i ×_{c.pt} V`. -/
noncomputable def baseChangeDiagram : I ⥤ Q where
  obj i := pullback (c.ι.app i) v
  map {i _j} g := pullback.lift (pullback.fst (c.ι.app i) v ≫ F.map g)
    (pullback.snd (c.ι.app i) v)
    (by rw [Category.assoc, c.w g]; exact pullback.condition)
  map_id _ := by
    refine pullback.hom_ext ?_ ?_ <;> simp
  map_comp _ _ := by
    refine pullback.hom_ext ?_ ?_ <;>
      simp [pullback.lift_fst, pullback.lift_snd, pullback.lift_fst_assoc]

/-- The stage of `baseChangeDiagram c v` at `i` is the fibre product `F i ×_{c.pt} V`. -/
@[simp]
theorem baseChangeDiagram_obj (i : I) :
    (baseChangeDiagram c v).obj i = pullback (c.ι.app i) v := rfl

/-- The transition map of `baseChangeDiagram c v` along `g` commutes with the first
projections and `F.map g`. -/
@[reassoc (attr := simp)]
theorem baseChangeDiagram_map_fst {i j : I} (g : i ⟶ j) :
    (baseChangeDiagram c v).map g ≫ pullback.fst (c.ι.app j) v =
      pullback.fst (c.ι.app i) v ≫ F.map g :=
  pullback.lift_fst _ _ _

/-- The transition maps of `baseChangeDiagram c v` commute with the second projections
to `V`. -/
@[reassoc (attr := simp)]
theorem baseChangeDiagram_map_snd {i j : I} (g : i ⟶ j) :
    (baseChangeDiagram c v).map g ≫ pullback.snd (c.ι.app j) v =
      pullback.snd (c.ι.app i) v :=
  pullback.lift_snd _ _ _

/-- The first projections of a base-changed diagram, as a natural transformation to the
original diagram. -/
noncomputable def baseChangeπ : baseChangeDiagram c v ⟶ F where
  app i := pullback.fst (c.ι.app i) v
  naturality _ _ _ := baseChangeDiagram_map_fst c v _

/-- The component of `baseChangeπ c v` at `i` is the first projection. -/
@[simp]
theorem baseChangeπ_app (i : I) :
    (baseChangeπ c v).app i = pullback.fst (c.ι.app i) v := rfl

/-- The second projections of a base-changed diagram, as a cocone with vertex `V`. -/
noncomputable def baseChangeCocone : Cocone (baseChangeDiagram c v) where
  pt := V
  ι :=
  { app := fun i ↦ pullback.snd (c.ι.app i) v
    naturality := fun _ _ g ↦ by
      simpa using baseChangeDiagram_map_snd c v g }

/-- The vertex of `baseChangeCocone c v` is `V`. -/
@[simp]
theorem baseChangeCocone_pt : (baseChangeCocone c v).pt = V := rfl

/-- The leg of `baseChangeCocone c v` at `i` is the second projection. -/
@[simp]
theorem baseChangeCocone_ι_app (i : I) :
    (baseChangeCocone c v).ι.app i = pullback.snd (c.ι.app i) v := rfl

/-- Each stage of a base-changed diagram sits in a pullback square over the corresponding leg
of the original cocone. -/
theorem isPullback_baseChangeCocone_ι (i : I) :
    IsPullback ((baseChangeCocone c v).ι.app i) ((baseChangeπ c v).app i) v (c.ι.app i) :=
  (IsPullback.of_hasPullback (c.ι.app i) v).flip

/-- The square formed by `baseChangeπ c v`, the cocone `c`, the cocone `baseChangeCocone c v`
and `v` commutes. -/
theorem baseChangeπ_comp_ι :
    baseChangeπ c v ≫ c.ι = (baseChangeCocone c v).ι ≫ (Functor.const I).map v := by
  ext i
  exact pullback.condition

/-- The first projections of a base-changed diagram are equifibered: the square over
`g : i ⟶ j` pastes with the pullback square defining `F j ×_{c.pt} V` to the one defining
`F i ×_{c.pt} V`. -/
theorem equifibered_baseChangeπ : NatTrans.Equifibered (baseChangeπ c v) := by
  intro i j g
  have hs : IsPullback ((baseChangeDiagram c v).map g ≫ pullback.snd (c.ι.app j) v)
      (pullback.fst (c.ι.app i) v) v (F.map g ≫ c.ι.app j) := by
    rw [baseChangeDiagram_map_snd c v g, c.w g]
    exact isPullback_baseChangeCocone_ι c v i
  exact IsPullback.of_right hs (baseChangeDiagram_map_fst c v g)
    (isPullback_baseChangeCocone_ι c v j)

/-- **The base change of a universal colimit cocone along any morphism into its vertex is a
colimit cocone.** -/
noncomputable def isColimitBaseChangeCocone (hc : IsUniversalColimit c) :
    IsColimit (baseChangeCocone c v) :=
  (hc (baseChangeCocone c v) (baseChangeπ c v) v (baseChangeπ_comp_ι c v)
    (equifibered_baseChangeπ c v) (isPullback_baseChangeCocone_ι c v)).some

/-- **The vertex of a universal colimit cocone receiving `v : V ⟶ c.pt` exhibits `V` as the
colimit of the base changes `F i ×_{c.pt} V`.** -/
noncomputable def coconePointIsoColimitBaseChange (hc : IsUniversalColimit c)
    [HasColimit (baseChangeDiagram c v)] : V ≅ colimit (baseChangeDiagram c v) :=
  (isColimitBaseChangeCocone c v hc).coconePointUniqueUpToIso (colimit.isColimit _)

end BaseChange

end CategoryTheory.Limits

namespace AlgebraicGeometry.FormalSpace

attribute [local instance] sheaf_hasColimits

variable {𝔅 : BigFppfSite.{u}} {S : Scheme.{u}} {hS : 𝔅.Contains S}
  {R : Type u} [CommRing R] [TopologicalSpace R]

/-- The weak ideals of definition of a topological ring are directed under reverse inclusion:
the intersection of two of them is again one. -/
theorem isDirectedOrder_weakIdeals (R : Type u) [CommRing R] [TopologicalSpace R] :
    IsDirectedOrder (WeakIdeals R) :=
  ⟨fun J K ↦ ⟨OrderDual.toDual ⟨(OrderDual.ofDual J).1 ⊓ (OrderDual.ofDual K).1,
      TopologicalRing.isWeakIdealOfDefinition_inf_of_isOpen_right
        (OrderDual.ofDual J).2 (OrderDual.ofDual K).2.1⟩,
    (inf_le_left : (OrderDual.ofDual J).1 ⊓ (OrderDual.ofDual K).1 ≤ (OrderDual.ofDual J).1),
    (inf_le_right : (OrderDual.ofDual J).1 ⊓ (OrderDual.ofDual K).1 ≤ (OrderDual.ofDual K).1)⟩⟩

/-- A ring with a weak ideal of definition has a nonempty index of quotient stages. -/
theorem nonempty_weakIdeals (hR : TopologicalRing.IsWeaklyPreAdmissible R) :
    Nonempty (WeakIdeals R) :=
  ⟨OrderDual.toDual ⟨hR.choose, hR.choose_spec⟩⟩

/-- The canonical diagram of quotient stages of a formal spectrum is filtered. -/
theorem isFiltered_weakIdeals (hR : TopologicalRing.IsWeaklyPreAdmissible R) :
    IsFiltered (WeakIdeals R) :=
  let _ : Nonempty (WeakIdeals R) := TopologicalRing.nonempty_weakIdealOfDefinitionIndex hR
  let _ : IsDirectedOrder (WeakIdeals R) := isDirectedOrder_weakIdeals R
  inferInstance

/-- **The canonical colimit cocone presenting a formal spectrum is universal**: it is a
filtered colimit of sheaves of sets. -/
theorem isUniversalColimit_formalSpectrumDiagram
    (hR : TopologicalRing.IsWeaklyPreAdmissible R) (D : QuotientSystem 𝔅 S hS R) :
    IsUniversalColimit (colimit.cocone (formalSpectrumDiagram D)) :=
  let _ : IsFiltered (WeakIdeals R) := isFiltered_weakIdeals hR
  sheaf_filteredColimit_isUniversalColimit (BigFppfOver.topology 𝔅 S hS)
    (formalSpectrumDiagram D)

variable (D : QuotientSystem 𝔅 S hS R)
  {V : Sheaf (BigFppfOver.topology 𝔅 S hS) (Type (u + 1))} (v : V ⟶ formalSpectrum D)

/-- The diagram `J ↦ Spec (R ⧸ J) ×_{Spf R} V` of base changes of a sheaf over a formal
spectrum to the quotient stages. -/
noncomputable abbrev stageBaseChangeDiagram :
    WeakIdeals R ⥤ Sheaf (BigFppfOver.topology 𝔅 S hS) (Type (u + 1)) :=
  baseChangeDiagram (colimit.cocone (formalSpectrumDiagram D)) v

/-- The stage of `stageBaseChangeDiagram D v` at `J` is `Spec (R ⧸ J) ×_{Spf R} V`. -/
@[simp]
theorem stageBaseChangeDiagram_obj (J : WeakIdeals R) :
    (stageBaseChangeDiagram D v).obj J = pullback (formalSpectrumInclusion D J) v := rfl

/-- **A sheaf over a formal spectrum is the colimit of its base changes to the quotient
stages**: `V ≅ colim_J (Spec (R ⧸ J) ×_{Spf R} V)`, the colimit over the weak ideals of
definition of `R` ordered by reverse inclusion. -/
noncomputable def isoColimitStageBaseChange
    (hR : TopologicalRing.IsWeaklyPreAdmissible R) :
    V ≅ colimit (stageBaseChangeDiagram D v) :=
  coconePointIsoColimitBaseChange _ v (isUniversalColimit_formalSpectrumDiagram hR D)

/-- The leg of the colimit cocone of
`AlgebraicGeometry.FormalSpace.isoColimitStageBaseChange` at `J` is the projection
`Spec (R ⧸ J) ×_{Spf R} V ⟶ V`. -/
theorem ι_isoColimitStageBaseChange_inv
    (hR : TopologicalRing.IsWeaklyPreAdmissible R) (J : WeakIdeals R) :
    colimit.ι (stageBaseChangeDiagram D v) J ≫ (isoColimitStageBaseChange D v hR).inv =
      pullback.snd (formalSpectrumInclusion D J) v :=
  IsColimit.comp_coconePointUniqueUpToIso_inv
    (isColimitBaseChangeCocone _ v (isUniversalColimit_formalSpectrumDiagram hR D))
    (colimit.isColimit _) J

section Presentation

variable {I : Type (u + 1)} [Preorder I] (E : I ⥤ BigAffineFppf 𝔅 S hS)

/-- The represented diagram of a presentation of an affine formal algebraic space, in the index
shape of Stacks 0AIA. -/
noncomputable abbrev presentationDiagram :
    I ⥤ Sheaf (BigFppfOver.topology 𝔅 S hS) (Type (u + 1)) :=
  E ⋙ BigAffineFppf.inclusion 𝔅 S hS ⋙
    Sheaf.sheafifiedYoneda (BigFppfOver.topology 𝔅 S hS)

variable [Nonempty I] [IsDirected I (· ≤ ·)]

/-- **The colimit cocone of a presentation of an affine formal algebraic space is universal**:
the index is directed, hence filtered, and the values are sheaves of sets. -/
theorem isUniversalColimit_presentationDiagram :
    IsUniversalColimit (colimit.cocone (presentationDiagram E)) :=
  sheaf_filteredColimit_isUniversalColimit (BigFppfOver.topology 𝔅 S hS)
    (presentationDiagram E)

/-- **A sheaf over a presented affine formal algebraic space is the colimit of its base changes
to the stages of the presentation**: `V ≅ colim_i (X_i ×_X V)`, for `X = colim_i X_i` a
presentation in the index shape of Stacks 0AIA. Stacks 0AIA is the sharper statement for a
quasi-compact source, where a single stage already receives the morphism. -/
noncomputable def isoColimitPresentationBaseChange
    {V : Sheaf (BigFppfOver.topology 𝔅 S hS) (Type (u + 1))}
    (v : V ⟶ colimit (presentationDiagram E)) :
    V ≅ colimit (baseChangeDiagram (colimit.cocone (presentationDiagram E)) v) :=
  coconePointIsoColimitBaseChange _ v (isUniversalColimit_presentationDiagram E)

end Presentation

end AlgebraicGeometry.FormalSpace

end
