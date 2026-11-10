module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.DiagonalChartRepresentable
public import StacksFrontier.AlgebraicGeometry.FormalSpace.SiteRepresentableFromAffinePoints
public import StacksFrontier.AlgebraicGeometry.FormalSpace.TautRepresentability
public import StacksFrontier.AlgebraicGeometry.FormalSpace.ThickeningOpenTransport
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineAtlas
public import StacksFrontier.AlgebraicGeometry.Spaces.Representability
public import StacksFrontier.CategoryTheory.Filtered.UpSetCofinal
public import StacksFrontier.CategoryTheory.Sites.FilteredUniversalColimit
public import StacksFrontier.CategoryTheory.Sites.QuasiCompact.ObjectsAndColimits

/-!
# A directed colimit of schemes along thickenings is a formal algebraic space

Let `S` be a scheme contained in a big fppf site `B` and let `D : Λ ⥤ (Sch/S)_fppf` be a
diagram in the big fppf site over `S`, indexed by a directed preorder, whose transition
morphisms are **thickenings** of the underlying schemes. Then a sheaf isomorphic to
`colim_λ h_{D λ}` and satisfying the set-theoretic condition of **Stacks 0AIS** is a formal
algebraic space over `S`.

This is the case of **Stacks 0AIU** in which the stages are *schemes* rather than arbitrary
algebraic spaces, and unlike
`AlgebraicGeometry.FormalSpace.isFormalAlgebraicSpace_of_colimit_thickenings` it carries no
chart system as a hypothesis: the chart system is constructed. The construction is the one the
implementation notes of that statement name as available for scheme stages — a thickening of
schemes induces an order isomorphism of the lattices of opens, so an affine open of one stage
has a canonical affine open counterpart in every later stage, and those counterparts assemble
into a chart diagram by `AlgebraicGeometry.FormalSpace.transportedOpenDiagram`. Only the
set-theoretic condition is left as data, exactly as in Stacks 0GVM
(`AlgebraicGeometry.FormalSpace.isAffineFormalAlgebraicSpace_colimit`).

## Main results

* `AlgebraicGeometry.FormalSpace.isAffineFormalAlgebraicSpace_sheafifiedYoneda`: the sheaf
  represented by an affine object of the site is an affine formal algebraic space -- the
  constant presentation.
* `AlgebraicGeometry.FormalSpace.isFormalAlgebraicSpace_of_colimit_siteThickenings`: the
  statement above.

## Implementation notes

The transported charts of an affine open of the stage `D o` are defined only at the stages
*above* `o`, so the chart system lives over the up-set `{j // o ≤ j}` rather than over `Λ`.
That costs nothing: the up-set of a point of a directed preorder is cofinal
(`CategoryTheory.final_upSetInclusion`), so the restricted diagram has the same colimit, and
the restriction has `o` as a least element, which is what
`AlgebraicGeometry.FormalSpace.transportedOpenDiagram` asks for.

The chart index is the type of affine opens of the scheme underlying `D o`, universe-lifted:
`AlgebraicGeometry.FormalSpace.isFormalAlgebraicSpace_of_openChartSystem_of_affineStages` wants
its chart index in `Type (u + 1)` while the affine opens of a scheme in `Scheme.{u}` form a type
in `Type u`.

No hypothesis says that `Z` is a formal algebraic space, nor that it admits an atlas: the atlas
is built out of the transported affine opens of a single stage.

## References

* [Stacks Project, Tag 0AI7](https://stacks.math.columbia.edu/tag/0AI7)
* [Stacks Project, Tag 0AIS](https://stacks.math.columbia.edu/tag/0AIS)
* [Stacks Project, Tag 0AIU](https://stacks.math.columbia.edu/tag/0AIU)
* [Stacks Project, Tag 0GVM](https://stacks.math.columbia.edu/tag/0GVM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Stacks.Thickenings
open AlgebraicGeometry.FormalSpace.CartesianColimit (constantColimitIso)

namespace AlgebraicGeometry.FormalSpace

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The sheaf represented by an affine object of the site -/

/-- **The set-theoretic condition of Stacks 0AIS holds for a representable sheaf.** The identity
surjects onto it and its kernel pair is the sheaf itself, so both presentations asked for are
the representable sheaf. -/
theorem satisfiesSetTheoreticCondition_sheafifiedYoneda (U : BigFppfOver B S hS) :
    SatisfiesSetTheoreticCondition B S hS
      ((Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj U) := by
  let J := BigFppfOver.topology B S hS
  set X := (Sheaf.sheafifiedYoneda J).obj U
  have hpre : X.obj ≅ (uliftYoneda.{u + 1}).obj U :=
    (sheafifiedYonedaPresheafIso B S hS).app U
  refine ⟨U, U, X, X, ⟨hpre⟩, ⟨hpre⟩, 𝟙 X, inferInstance, ?_⟩
  exact ⟨(IsPullback.of_id_fst : IsPullback (𝟙 X) (𝟙 X) (𝟙 X) (𝟙 X)).isoPullback.hom,
    inferInstance⟩

/-- **The sheaf represented by an affine object of the big fppf site over `S` is an affine
formal algebraic space.** Its presentation is the constant one on a one-point index: the
identity is a thickening, and the colimit of a constant diagram over a connected index is its
value. -/
theorem isAffineFormalAlgebraicSpace_sheafifiedYoneda (U : BigFppfOver B S hS)
    (hU : IsAffine ((BigFppfOver.toScheme B S hS).obj U)) :
    IsAffineFormalAlgebraicSpace B S hS
      ((Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj U) := by
  let J := BigFppfOver.topology B S hS
  let : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
  refine ⟨satisfiesSetTheoreticCondition_sheafifiedYoneda B S hS U,
    PUnit.{u + 2}, inferInstance, inferInstance, inferInstance,
    (Functor.const PUnit.{u + 2}).obj
      (⟨U, hU⟩ : BigAffineFppf B S hS), ?_, ⟨?_⟩⟩
  · intro i j f
    change IsThickening ((BigAffineFppf.toScheme B S hS).map (𝟙 _))
    rw [CategoryTheory.Functor.map_id]
    exact ⟨inferInstance, fun x ↦ ⟨x, rfl⟩⟩
  · refine ?_ ≪≫ (HasColimit.isoOfNatIso
      (Functor.constComp PUnit.{u + 2} (⟨U, hU⟩ : BigAffineFppf B S hS)
        (BigAffineFppf.inclusion B S hS ⋙ Sheaf.sheafifiedYoneda J))).symm
    exact (constantColimitIso PUnit.{u + 2} ((Sheaf.sheafifiedYoneda J).obj U)).symm

/-! ### The colimit -/

/-- Every point lies in a member of a family of opens whose supremum is `⊤`. -/
private theorem exists_mem_of_iSup_eq_top {X : Scheme.{u}} {ι : Sort*} {V : ι → X.Opens}
    (h : ⨆ k, V k = ⊤) (x : X) : ∃ k, x ∈ V k :=
  TopologicalSpace.Opens.mem_iSup.mp (h ▸ trivial)

/-- **A directed colimit of schemes along thickenings is a formal algebraic space**, granting
only the set-theoretic condition of **Stacks 0AIS** for the colimit.

This is the scheme-stage case of **Stacks 0AIU**, with the chart system *constructed* rather
than assumed: the affine opens of one stage transport along the thickenings to affine opens of
every later stage (`AlgebraicGeometry.FormalSpace.transportedOpenDiagram`), the transported
diagrams are chart diagrams by representable open immersions, and
`AlgebraicGeometry.FormalSpace.isFormalAlgebraicSpace_of_openChartSystem_of_affineStages`
assembles them.

NO TAG IS ATTACHED. Stacks 0AIU states the conclusion for stages which are arbitrary
*algebraic spaces*, and the transport of a chart across a thickening of algebraic spaces is
Stacks 05ZH at arbitrary order, which this library does not carry; so this is a special case of
the tag rather than the tag. -/
theorem isFormalAlgebraicSpace_of_colimit_siteThickenings
    {Λ : Type (u + 1)} [Preorder Λ] [Nonempty Λ] [IsDirected Λ (· ≤ ·)]
    (D : Λ ⥤ BigFppfOver B S hS)
    (hD : ∀ ⦃i j : Λ⦄ (f : i ⟶ j),
      IsThickening ((BigFppfOver.toScheme B S hS).map (D.map f)))
    (Z : FppfSheaf B S hS) (hZset : SatisfiesSetTheoreticCondition B S hS Z)
    (hZ : letI : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) :=
        Sheaf.instHasColimitsOfSize
      Nonempty (Z ≅ colimit (D ⋙ Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)))) :
    IsFormalAlgebraicSpace B S hS Z := by
  classical
  let J := BigFppfOver.topology B S hS
  let : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
  have : J.Subcanonical := bigFppfOver_subcanonical B S hS
  have : PreservesLimitsOfShape WalkingCospan (Sheaf.sheafifiedYoneda J) :=
    preservesLimitsOfShape_walkingCospan_sheafifiedYoneda B S hS
  obtain ⟨eZ⟩ := hZ
  have o : Λ := Nonempty.some ‹Nonempty Λ›
  -- the up-set of `o`, over which the transported charts live
  set Λ' := {j : Λ // o ≤ j}
  set D' : Λ' ⥤ BigFppfOver B S hS := CategoryTheory.upSetInclusion o ⋙ D
  have hD'thick : ∀ ⦃i j : Λ'⦄ (f : i ⟶ j),
      IsThickening ((BigFppfOver.toScheme B S hS).map (D'.map f)) := fun _ _ f ↦ hD _
  set o' : Λ' := ⟨o, le_refl o⟩
  have ho' : ∀ i : Λ', o' ≤ i := fun i ↦ i.2
  set E : Λ' ⥤ FppfSheaf B S hS := D' ⋙ Sheaf.sheafifiedYoneda J
  -- the colimit over the up-set is the colimit over `Λ`
  have hcolim : Nonempty (Z ≅ colimit E) := by
    obtain ⟨hc⟩ := CategoryTheory.nonempty_isColimit_whiskerLeft_upSetInclusion o
      (colimit.isColimit (D ⋙ Sheaf.sheafifiedYoneda J))
    exact ⟨eZ.trans (hc.coconePointUniqueUpToIso (colimit.isColimit E))⟩
  -- the chart index: the affine opens of the least stage
  set W : Scheme.{u} := (BigFppfOver.toScheme B S hS).obj (D'.obj o')
  set V : ULift.{u + 1, u} W.affineOpens → W.Opens := fun k ↦ (k.down.1 : W.Opens)
  have hVaff : ∀ k, IsAffineOpen (V k) := fun k ↦ k.down.2
  have hVtop : (⨆ k, V k) = ⊤ := by
    refine eq_top_iff.mpr fun x _ ↦ ?_
    obtain ⟨A, hA⟩ := exists_mem_of_iSup_eq_top (iSup_affineOpens_eq_top W) x
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨ULift.up A, hA⟩
  refine isFormalAlgebraicSpace_of_openChartSystem_of_affineStages B S hS E ?_
    (fun k : ULift.{u + 1, u} W.affineOpens ↦
      transportedOpenDiagram B S hS D' hD'thick o' ho' (V k) ⋙ Sheaf.sheafifiedYoneda J)
    (fun k ↦ Functor.whiskerRight
      (transportedOpenInclusion B S hS D' hD'thick o' ho' (V k)) (Sheaf.sheafifiedYoneda J))
    ?_ ?_ ?_ ?_ ?_ Z hZset hcolim
  · -- the transitions of `E` are monomorphisms
    intro i j f
    have hci : _root_.AlgebraicGeometry.IsClosedImmersion
        ((BigFppfOver.toScheme B S hS).map (D'.map f)) := (hD'thick f).1
    have _ := hci
    have : Mono ((BigFppfOver.toScheme B S hS).map (D'.map f)) := inferInstance
    have : Mono (D'.map f) :=
      (BigFppfOver.toScheme B S hS).mono_of_mono_map inferInstance
    change Mono ((Sheaf.sheafifiedYoneda J).map (D'.map f))
    exact CategoryTheory.preserves_mono_of_preservesLimit _ (D'.map f)
  · -- the stages of each chart diagram are affine formal algebraic spaces
    intro k i
    exact isAffineFormalAlgebraicSpace_sheafifiedYoneda B S hS _
      (isAffine_transportedOpenDiagram_obj B S hS D' hD'thick o' ho' (hVaff k) i)
  · -- the transitions of each chart diagram are representable thickenings
    intro k i j g
    have := BigFppfOver.isStableUnderBaseChange_inverseImage B S hS
      (@IsThickening : MorphismProperty Scheme.{u})
    exact MorphismProperty.relative_map
      (isThickening_transportedOpenDiagram_map B S hS D' hD'thick o' ho' (V k) g)
  · -- each chart morphism base changes to an open subscheme over every point of its stage
    intro k i U ξ
    have := BigFppfOver.isStableUnderBaseChange_inverseImage B S hS
      (@_root_.AlgebraicGeometry.IsOpenImmersion : MorphismProperty Scheme.{u})
    have hrel : (MorphismProperty.inverseImage
        (@_root_.AlgebraicGeometry.IsOpenImmersion : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).relative (Sheaf.sheafifiedYoneda J)
        ((Sheaf.sheafifiedYoneda J).map
          (transportedOpenι B S hS D' hD'thick o' ho' (V k) i)) :=
      MorphismProperty.relative_map
        (isOpenImmersion_transportedOpenι B S hS D' hD'thick o' ho' (V k) i)
    set eG := Sheaf.sheafifiedYonedaIsoUliftYoneda' J
    obtain ⟨Wk, pr, c, hpb⟩ := hrel.rep (eG.hom.app U ≫ ξ)
    refine ⟨Wk, pr, (eG.app Wk).inv ≫ c, ?_, hrel.property _ c pr hpb⟩
    refine hpb.of_iso (eG.app Wk) (Iso.refl _) (eG.app U) (Iso.refl _) ?_ ?_ ?_ ?_
    · exact (Category.comp_id c).trans ((eG.app Wk).hom_inv_id_assoc c).symm
    · exact eG.hom.naturality pr
    · cat_disch
    · cat_disch
  · -- each chart diagram is equifibered over the diagram of stages
    intro k i j f
    exact ((isPullback_transportedOpenInclusion B S hS D' hD'thick o' ho' (V k)
      f).map (Sheaf.sheafifiedYoneda J))
  · -- the charts cover each stage
    intro i
    refine
      (Stacks.Sites.QuasiCompactCriterion.isLocallySurjective_sigmaDesc_sheafifiedYoneda_map_iff
        (J := J) (fun k ↦ transportedOpenι B S hS D' hD'thick o' ho' (V k) i)).mpr ?_
    refine BigFppfOver.ofArrows_mem_topology_of_isOpenImmersion B S hS
      (fun k ↦ transportedOpenι B S hS D' hD'thick o' ho' (V k) i)
      (fun k ↦ isOpenImmersion_transportedOpenι B S hS D' hD'thick o' ho' (V k) i) ?_
    intro x
    obtain ⟨k, hk⟩ := exists_mem_of_iSup_eq_top
      (iSup_transportedOpen_eq_top B S hS D' hD'thick o' ho' V hVtop i) x
    exact ⟨k, ⟨x, hk⟩, rfl⟩

end AlgebraicGeometry.FormalSpace

end
