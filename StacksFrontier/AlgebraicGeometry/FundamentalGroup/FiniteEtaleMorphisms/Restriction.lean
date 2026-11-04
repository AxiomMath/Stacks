module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Morphisms.Etale.Defs
public import StacksFrontier.AlgebraicGeometry.Scheme.Immersion.Basic
public import StacksFrontier.Topology.Connected.FiniteFibres

/-!
# Faithfulness of finite étale restriction to a closed subscheme

Let `Y` be a closed subscheme of a scheme `X`.  If every connected component of `X` meets `Y`,
then restriction of finite étale schemes from `X` to `Y` is faithful.

## Main results

* `Stacks.FundamentalGroup.faithful_finiteEtaleRestriction_of_components_meet` states
  faithfulness of the canonical base-change functor.

## Implementation notes

Finite étale schemes over a scheme form the category `MorphismProperty.Over` for the
intersection of the finite and the étale morphism property.  The component condition says that
every connected component contains the image of a point of the closed subscheme.  Faithfulness
is proved by showing that the equalizer of two parallel maps is a clopen subscheme meeting every
connected component, hence all of the source.

## References

* [Stacks Project, Tag 0EJX](https://stacks.math.columbia.edu/tag/0EJX)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory.Limits

universe u

namespace Stacks.FundamentalGroup

/-- A clopen set meeting every connected component of a topological space is everything. -/
private theorem range_eq_univ_of_clopen_meets_components
    {T : Type u} [TopologicalSpace T] (s : Set T) (hs : IsClopen s)
    (h : ∀ x : T, ∃ y ∈ s, ConnectedComponents.mk y = ConnectedComponents.mk x) :
    s = Set.univ := by
  refine Set.eq_univ_of_forall fun x => ?_
  obtain ⟨y, hy, hxy⟩ := h x
  exact hs.connectedComponent_subset hy (ConnectedComponents.coe_eq_coe'.mp hxy.symm)

/-- For an open, closed map with finite fibres, a point of the target in the connected component
of the image of `z` has a preimage in the connected component of `z`. -/
private theorem exists_preimage_sameComponent
    {U X : Type u} [TopologicalSpace U] [TopologicalSpace X]
    (p : U → X) (hp_open : IsOpenMap p) (hp_closed : IsClosedMap p)
    (hp_fiber : ∀ x, (p ⁻¹' {x}).Finite) (z : U) (y : X)
    (hy : ConnectedComponents.mk y = ConnectedComponents.mk (p z)) :
    ∃ w : U, p w = y ∧ ConnectedComponents.mk w = ConnectedComponents.mk z := by
  let V : Set X := connectedComponent (p z)
  have hzV : p z ∈ V := mem_connectedComponent
  have hyV : y ∈ V := by
    obtain ⟨s, hs, hys⟩ := ConnectedComponents.coe_eq_coe'.mp hy
    exact hs.1.subset_connectedComponent hs.2 hys
  let q : p ⁻¹' V → V := V.restrictPreimage p
  have hqfiber (v : V) : (q ⁻¹' {v}).Finite := by
    let : Finite (p ⁻¹' {v.1}) := hp_fiber v.1
    exact Finite.of_injective (fun w : q ⁻¹' {v} =>
      (⟨w.1.1, by simpa [q, Set.restrictPreimage] using congrArg Subtype.val w.2⟩ :
        p ⁻¹' {v.1})) fun _ _ h =>
      Subtype.ext (Subtype.ext (congrArg (fun t : p ⁻¹' {v.1} => t.1) h))
  let : Nonempty V := ⟨⟨p z, hzV⟩⟩
  let : Nonempty (p ⁻¹' V) := ⟨⟨z, hzV⟩⟩
  have hsurj := connectedComponent_clopen_and_image_eq_univ q
    (isConnected_iff_connectedSpace.mp isConnected_connectedComponent)
    (hp_open.restrictPreimage V) (hp_closed.restrictPreimage V)
    ⟨y, hyV⟩ (hqfiber ⟨y, hyV⟩)
    (connectedComponent ⟨z, hzV⟩) ⟨⟨z, hzV⟩, rfl⟩
  have hy_image : (⟨y, hyV⟩ : V) ∈ q '' connectedComponent ⟨z, hzV⟩ := by
    rw [hsurj.2.2.2.2.2]; simp
  obtain ⟨w, hw, hwy⟩ := hy_image
  refine ⟨w.1, congrArg Subtype.val hwy, ?_⟩
  let i : p ⁻¹' V → U := fun t => t.1
  have hconn : IsConnected (Subtype.val '' connectedComponent (⟨z, hzV⟩ : p ⁻¹' V)) :=
    isConnected_connectedComponent.image (f := i) continuous_subtype_val.continuousOn
  have hzimg : z ∈ Subtype.val '' connectedComponent (⟨z, hzV⟩ : p ⁻¹' V) :=
    ⟨⟨z, hzV⟩, mem_connectedComponent, rfl⟩
  exact ConnectedComponents.coe_eq_coe.mpr
    (connectedComponent_eq (hconn.subset_connectedComponent hzimg ⟨w, hw, rfl⟩)).symm

/-- Being both finite and étale is stable under base change. -/
local instance : MorphismProperty.IsStableUnderBaseChange
    ((@IsFinite ⊓ @Etale) : MorphismProperty Scheme.{u}) :=
  MorphismProperty.IsStableUnderBaseChange.inf

/-- **Stacks Project, Tag 0EJX.** Restriction of finite étale schemes to a closed subscheme
meeting every connected component is faithful. -/
@[stacks 0EJX]
public lemma faithful_finiteEtaleRestriction_of_components_meet
    {X Y : Scheme.{u}} (f : Y ⟶ X) [IsClosedImmersion f]
    (h : ∀ c : ConnectedComponents X,
      ∃ y : Y, ConnectedComponents.mk (f.base y) = c) :
    (MorphismProperty.Over.pullback
      ((@IsFinite ⊓ @Etale) : MorphismProperty Scheme.{u}) ⊤ f).Faithful := by
  classical
  constructor
  intro A B a b hab
  apply MorphismProperty.Over.Hom.ext
  let A' : Over X := (MorphismProperty.Over.forget
    ((@IsFinite ⊓ @Etale) : MorphismProperty Scheme.{u}) ⊤ X).obj A
  let B' : Over X := (MorphismProperty.Over.forget
    ((@IsFinite ⊓ @Etale) : MorphismProperty Scheme.{u}) ⊤ X).obj B
  let a' : A' ⟶ B' := Over.homMk a.left (MorphismProperty.Over.w a)
  let b' : A' ⟶ B' := Over.homMk b.left (MorphismProperty.Over.w b)
  let G := Over.pullback f
  have hab' : G.map a' = G.map b' := by
    ext
    exact congrArg (fun q => q.left) hab
  let E : Over X := equalizer a' b'
  let e : E ⟶ A' := equalizer.ι a' b'
  have hlim : IsLimit
      (Fork.ofι (G.map e) (by
        rw [← G.map_comp, ← G.map_comp]
        exact congrArg G.map (equalizer.condition a' b')) :
        Fork (G.map a') (G.map b')) :=
    (isLimitMapConeForkEquiv G (equalizer.condition a' b'))
      (isLimitOfPreserves G (equalizerIsEqualizer a' b'))
  have htriv : IsLimit
      (Fork.ofι (𝟙 (G.obj A')) (by rw [hab']) : Fork (G.map a') (G.map b')) := by
    exact Fork.IsLimit.mk _ (fun s => s.ι) (fun _ => rfl) fun s m hm => by simpa using hm
  let j := hlim.conePointUniqueUpToIso htriv
  have hj : j.hom = G.map e := by
    simpa [j, Fork.ι] using
      hlim.conePointUniqueUpToIso_hom_comp htriv WalkingParallelPair.zero
  let : IsIso (G.map e) := hj ▸ Iso.isIso_hom j
  have hOpen : IsOpenImmersion e.left := by
    let : Etale B'.hom := B.prop.2
    let : FormallyUnramified B'.hom := inferInstance
    let : LocallyOfFiniteType B'.hom := inferInstance
    refine MorphismProperty.of_isPullback
      ((Limits.isPullback_equalizer_prod a' b').map (Over.forget X)).flip ?_
    rw [← MorphismProperty.cancel_right_of_respectsIso @IsOpenImmersion _
      (Over.prodLeftIsoPullback B' B').hom]
    convert! (inferInstance : IsOpenImmersion (pullback.diagonal B'.hom))
    ext1 <;> simp [← Over.comp_left]
  have hClosed : IsClosedImmersion e.left := by
    let : IsFinite B'.hom := B.prop.1
    infer_instance
  have hClopen : IsClopen (Set.range e.left) :=
    ⟨e.left.isClosedEmbedding.isClosed_range, e.left.isOpenEmbedding.isOpen_range⟩
  have hRange : Set.range e.left = Set.univ := by
    apply range_eq_univ_of_clopen_meets_components (Set.range e.left) hClopen
    intro x
    obtain ⟨y, hy⟩ := h (ConnectedComponents.mk (A'.hom x))
    let : Etale A'.hom := A.prop.2
    let : Flat A'.hom := inferInstance
    let : LocallyOfFinitePresentation A'.hom := inferInstance
    let : IsFinite A'.hom := A.prop.1
    obtain ⟨w, hwy, hwcomp⟩ := exists_preimage_sameComponent A'.hom.base
      A'.hom.isOpenMap A'.hom.isClosedMap A'.hom.finite_preimage_singleton x (f.base y) hy
    obtain ⟨z, hzw, hzy⟩ := Scheme.Pullback.exists_preimage_pullback
      (f := A'.hom) (g := f) w y hwy
    let z' := (asIso (G.map e)).inv.left z
    have hz' : (G.map e).left z' = z := by
      show (asIso (G.map e)).hom.left ((asIso (G.map e)).inv.left z) = z
      rw [← Scheme.Hom.comp_apply, ← Over.comp_left, Iso.inv_hom_id]; rfl
    have hfirst : e.left (Limits.pullback.fst E.hom f z') = w := by
      have := congrArg (fun q => Limits.pullback.fst A'.hom f q) hz'
      have hcomm : (G.map e).left ≫ Limits.pullback.fst A'.hom f =
          Limits.pullback.fst E.hom f ≫ e.left :=
        Limits.pullback.lift_fst _ _ _
      rw [← Scheme.Hom.comp_apply, hcomm] at this
      exact this.trans hzw
    exact ⟨w, ⟨Limits.pullback.fst E.hom f z', hfirst⟩, hwcomp⟩
  have hsurj : Surjective e.left := (surjective_iff _).mpr (Set.range_eq_univ.mp hRange)
  have hIso : IsIso e.left := (isIso_iff_isOpenImmersion_and_surjective e.left).2
    ⟨hOpen, hsurj⟩
  let : IsIso ((Over.forget X).map e) := hIso
  let : IsIso e := isIso_of_reflects_iso e (Over.forget X)
  have hab'' : a' = b' := (cancel_epi e).1 (equalizer.condition a' b')
  exact congrArg (fun q : A' ⟶ B' => q.left) hab''

end Stacks.FundamentalGroup
