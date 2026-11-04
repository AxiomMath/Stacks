module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicTopology.CechNerve
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Equifibered
public import Mathlib.CategoryTheory.Limits.Shapes.WidePullbacks
public import StacksFrontier.AlgebraicGeometry.GroupScheme.Relations.PreRelations
public import StacksFrontier.AlgebraicGeometry.Simplicial.CechNerveEquivalenceRelation
import StacksCore.Tactic.StacksAttribute

/-!
# Equivalence classes of points of a cartesian simplicial scheme

Let `f : X ⟶ S` be a morphism of schemes and let `Y` be a simplicial scheme with a cartesian
morphism to the Čech nerve of `f`. For a point `y` of `Y₀`, the points of `Y₀` reachable from
`y` by a one-simplex form its equivalence class: every point lies in its own class, and two
classes that meet are equal. When `f` is quasi-compact, each such class is a quasi-compact
subset of `Y₀`.

Both statements come from the equivalence relation of
`CategoryTheory.SimplicialObject.isEquivalenceRelation_faceMaps_of_equifibered`: the two face
maps `Y.δ 1, Y.δ 0 : Y₁ ⟶ Y₀` form an internal equivalence relation, hence a pre-equivalence
relation in the sense of Stacks 022P, and therefore induce an honest equivalence relation on the
underlying points by Stacks 022Q. Quasi-compactness is separate: the class of `y` is the image
of the fibre of `Y.δ 1` over `y` under `Y.δ 0`, and `Y.δ 1` is quasi-compact because it is a
base change of the degree-one face map of the Čech nerve, which is a base change of `f` up to an
isomorphism.

## Main definitions

* `AlgebraicGeometry.Simplicial.pointClass`: the set of points of `Y₀` reached from a given
  point by a one-simplex.

## Main results

* `AlgebraicGeometry.Simplicial.mem_pointClass_self`: a point belongs to its own class.
* `AlgebraicGeometry.Simplicial.pointClass_eq_of_nonempty_inter`: two classes that meet are
  equal.
* `AlgebraicGeometry.Simplicial.isCompact_relatedPoints`: over a quasi-compact morphism, the
  class of a point is quasi-compact.

## Implementation notes

The relation defining `pointClass` is `Function.SourceTargetRel` for the two face maps on
underlying points, with the first coordinate given by `Y.δ 1` and the second by `Y.δ 0`. The
Čech nerve and the cartesian morphism to it are `CategoryTheory.Arrow.cechNerve` and
`CategoryTheory.NatTrans.Equifibered`. Quasi-compactness of a subset is `IsCompact`.

The pre-relation attached to the two face maps is formed in the slice category over the
terminal scheme, which is where `Stacks.Groupoids.PreRelation` and Stacks 022Q live; the two
coordinates of that pre-relation are the two face maps by construction.

## References

* [Stacks Project, Tag 024G](https://stacks.math.columbia.edu/tag/024G)
* [Stacks Project, Tag 024H](https://stacks.math.columbia.edu/tag/024H)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Simplicial

universe u v

namespace AlgebraicGeometry.Simplicial

private noncomputable abbrev terminalOver (Z : Scheme.{v}) : Over (⊤_ Scheme.{v}) :=
  Over.mk (Limits.terminal.from Z)

private noncomputable def faceRelation (Y : SimplicialObject Scheme.{v}) :
    Stacks.Groupoids.PreRelation (terminalOver (Y _⦋1⦌)) (terminalOver (Y _⦋0⦌)) :=
  prod.lift (Over.homMk (Y.δ (1 : Fin 2))) (Over.homMk (Y.δ (0 : Fin 2)))

private lemma faceRelation_target (Y : SimplicialObject Scheme.{v}) :
    (faceRelation Y).target.left = Y.δ (1 : Fin 2) := by
  simp [Stacks.Groupoids.PreRelation.target, faceRelation]

private lemma faceRelation_source (Y : SimplicialObject Scheme.{v}) :
    (faceRelation Y).source.left = Y.δ (0 : Fin 2) := by
  simp [Stacks.Groupoids.PreRelation.source, faceRelation]

private lemma faceRelation_target_left {Y : SimplicialObject Scheme.{v}} {T : Over (⊤_ Scheme.{v})}
    {r : T ⟶ terminalOver (Y _⦋1⦌)} {x : T ⟶ terminalOver (Y _⦋0⦌)}
    (h : r ≫ (faceRelation Y).target = x) : r.left ≫ Y.δ (1 : Fin 2) = x.left := by
  simpa [Stacks.Groupoids.PreRelation.target, faceRelation_target Y] using congrArg Over.Hom.left h

private lemma faceRelation_source_left {Y : SimplicialObject Scheme.{v}} {T : Over (⊤_ Scheme.{v})}
    {r : T ⟶ terminalOver (Y _⦋1⦌)} {x : T ⟶ terminalOver (Y _⦋0⦌)}
    (h : r ≫ (faceRelation Y).source = x) : r.left ≫ Y.δ (0 : Fin 2) = x.left := by
  simpa [Stacks.Groupoids.PreRelation.source, faceRelation_source Y] using congrArg Over.Hom.left h

private lemma faceRelation_isPreEquivalenceRelation (Y : SimplicialObject Scheme.{v})
    (h : IsEquivalenceRelation (Y.δ (1 : Fin 2)) (Y.δ (0 : Fin 2))) :
    Stacks.Groupoids.IsPreEquivalenceRelation (faceRelation Y) := by
  let e : EquivalenceRelation (Y.δ (1 : Fin 2)) (Y.δ (0 : Fin 2)) :=
    Classical.choice h.nonempty_equivalenceRelation
  intro T
  constructor
  · intro x
    refine ⟨x ≫ Over.homMk e.r, ?_, ?_⟩ <;>
      apply Over.OverMorphism.ext <;>
      simp [Stacks.Groupoids.PreRelation.target, Stacks.Groupoids.PreRelation.source,
        faceRelation, Category.assoc]
  · rintro x y ⟨r, hr₁, hr₂⟩
    refine ⟨r ≫ Over.homMk e.s, ?_, ?_⟩ <;>
      apply Over.OverMorphism.ext <;>
      simp [Stacks.Groupoids.PreRelation.target, Stacks.Groupoids.PreRelation.source,
        faceRelation, Category.assoc, e.symmetry₁, e.symmetry₂,
        faceRelation_target_left hr₁, faceRelation_source_left hr₂]
  · rintro x y z ⟨r₁, hr₁₁, hr₁₂⟩ ⟨r₂, hr₂₁, hr₂₂⟩
    let q : T.left ⟶ e.c.pt := PullbackCone.IsLimit.lift e.isLimit r₁.left r₂.left
      ((faceRelation_source_left hr₁₂).trans (faceRelation_target_left hr₂₁).symm)
    refine ⟨Over.homMk (q ≫ e.t), ?_, ?_⟩
    · apply Over.OverMorphism.ext
      simp only [faceRelation_target Y, Over.comp_left, Over.homMk_left]
      rw [Category.assoc, e.transitivity₁, ← Category.assoc,
        PullbackCone.IsLimit.lift_fst, faceRelation_target_left hr₁₁]
    · apply Over.OverMorphism.ext
      simp only [faceRelation_source Y, Over.comp_left, Over.homMk_left]
      rw [Category.assoc, e.transitivity₂, ← Category.assoc,
        PullbackCone.IsLimit.lift_snd, faceRelation_source_left hr₂₂]

private lemma facePoints_equivalence (Y : SimplicialObject Scheme.{v})
    (h : IsEquivalenceRelation (Y.δ (1 : Fin 2)) (Y.δ (0 : Fin 2))) :
    Equivalence (Function.SourceTargetRel (Y.δ (0 : Fin 2)).base
      (Y.δ (1 : Fin 2)).base) := by
  simpa only [faceRelation_source, faceRelation_target] using
    AlgebraicGeometry.PreRelation.equivalence_sourceTargetRel (faceRelation Y)
      (faceRelation_isPreEquivalenceRelation Y h)

/-- The points reached from `y` by a one-simplex whose first face is `y`. -/
@[stacks 024G "the subset T_y"]
def pointClass (Y : SimplicialObject Scheme.{u}) (y : Y _⦋0⦌) :
    Set (Y _⦋0⦌) :=
  {y' | Function.SourceTargetRel (Y.δ (0 : Fin 2)).base
    (Y.δ (1 : Fin 2)).base y y'}

/-- A point belongs to the subset of points reachable from it. -/
@[stacks 024G "membership of y in T_y"]
theorem mem_pointClass_self {X S : Scheme.{u}} (f : X ⟶ S)
    {Y : SimplicialObject Scheme.{u}} (π : Y ⟶ (Arrow.mk f).cechNerve)
    (hπ : NatTrans.Equifibered π) (y : Y _⦋0⦌) :
    y ∈ pointClass Y y :=
  (facePoints_equivalence Y
    (SimplicialObject.isEquivalenceRelation_faceMaps_of_equifibered f π hπ)).refl y

/-- If two subsets of reachable points meet, they are the same subset. -/
@[stacks 024G "intersecting classes are equal"]
theorem pointClass_eq_of_nonempty_inter {X S : Scheme.{u}} (f : X ⟶ S)
    {Y : SimplicialObject Scheme.{u}} (π : Y ⟶ (Arrow.mk f).cechNerve)
    (hπ : NatTrans.Equifibered π) (y y' : Y _⦋0⦌)
    (h : (pointClass Y y ∩ pointClass Y y').Nonempty) :
    pointClass Y y = pointClass Y y' := by
  have e := facePoints_equivalence Y
    (SimplicialObject.isEquivalenceRelation_faceMaps_of_equifibered f π hπ)
  obtain ⟨z, hyz, hy'z⟩ := h
  have hyy' := e.trans hyz (e.symm hy'z)
  ext w
  exact ⟨e.trans (e.symm hyy'), e.trans hyy'⟩

/-- The two projections of the wide pullback of two copies of `f` form a pullback square. -/
private lemma isPullback_widePullback_π_one_π_zero {C : Type*} [Category C] {X S : C} (f : X ⟶ S)
    [HasWidePullback S (fun _ : Fin 2 => X) (fun _ => f)] :
    IsPullback (WidePullback.π (fun _ : Fin 2 => f) 1)
      (WidePullback.π (fun _ : Fin 2 => f) 0) f f := by
  apply IsPullback.mk'
  · simp [WidePullback.π_arrow]
  · intro T φ ψ h0 h1
    apply WidePullback.hom_ext
    · intro j
      fin_cases j
      · simpa using h1
      · simpa using h0
    · simpa [WidePullback.π_arrow] using h0 =≫ f
  · intro T φ ψ h
    let fs : Fin 2 → (T ⟶ X) := fun j => if j = (0 : Fin 2) then ψ else φ
    have hw : ∀ j, fs j ≫ f = ψ ≫ f := by
      intro j
      fin_cases j <;> simp [fs, h]
    refine ⟨WidePullback.lift (ψ ≫ f) fs hw, ?_, ?_⟩
    · simpa [fs] using (WidePullback.lift_π (fun _ : Fin 2 => f) (ψ ≫ f) fs hw (1 : Fin 2))
    · simpa [fs] using (WidePullback.lift_π (fun _ : Fin 2 => f) (ψ ≫ f) fs hw (0 : Fin 2))

private theorem quasiCompact_cechNerve_face_one {X S : Scheme.{u}} (f : X ⟶ S)
    [QuasiCompact f] :
    QuasiCompact ((Arrow.mk f).cechNerve.map (SimplexCategory.δ (1 : Fin 2)).op) := by
  let Q := Limits.widePullback S (fun _ : Fin 1 => X) (fun _ => f)
  let i : X ⟶ Q := WidePullback.lift f (fun _ : Fin 1 => 𝟙 X) (by simp)
  let p0 := WidePullback.π (fun _ : Fin 2 => f) 0
  let d := (Arrow.mk f).cechNerve.map (SimplexCategory.δ (1 : Fin 2)).op
  have hidx : (SimplexCategory.δ (1 : Fin 2)).toOrderHom (0 : Fin 1) = (0 : Fin 2) := by decide
  have hpi : i ≫ WidePullback.π (fun _ : Fin 1 => f) 0 = 𝟙 X := by
    simp only [i, WidePullback.lift_π]
  have hfac : d = p0 ≫ i := by
    apply WidePullback.hom_ext
    · intro j
      fin_cases j
      simp [d, p0, i, hidx, WidePullback.lift_π, Category.assoc]
    · simp [d, i, p0, WidePullback.lift_base, WidePullback.π_arrow]
  have : QuasiCompact p0 :=
    MorphismProperty.of_isPullback (isPullback_widePullback_π_one_π_zero f) inferInstance
  have hip : WidePullback.π (fun _ : Fin 1 => f) 0 ≫ i = 𝟙 Q := by
    apply WidePullback.hom_ext
    · intro j
      obtain rfl : j = 0 := Subsingleton.elim j 0
      rw [Category.assoc, hpi, Category.comp_id, Category.id_comp]
    · dsimp [i]
      rw [Category.assoc, WidePullback.lift_base, WidePullback.π_arrow]
      exact (Category.id_comp _).symm
  have : IsIso i := ⟨⟨WidePullback.π (fun _ : Fin 1 => f) 0, hpi, hip⟩⟩
  change QuasiCompact d
  rw [hfac]
  infer_instance

/-- The vertices connected to a fixed vertex in a cartesian simplicial scheme
over the Čech nerve of a quasi-compact morphism form a quasi-compact set. -/
@[stacks 024H]
theorem isCompact_relatedPoints {X S : Scheme.{u}} (f : X ⟶ S)
    [QuasiCompact f] {Y : SimplicialObject Scheme.{u}}
    (π : Y ⟶ (Arrow.mk f).cechNerve) (hπ : NatTrans.Equifibered π)
    (y : (Y _⦋0⦌)) :
    IsCompact {y' : (Y _⦋0⦌) | ∃ y₁ : (Y _⦋1⦌),
      (Y.δ (1 : Fin 2)).base y₁ = y ∧ (Y.δ (0 : Fin 2)).base y₁ = y'} := by
  let d₁ := Y.δ (1 : Fin 2)
  let d₀ := Y.δ (0 : Fin 2)
  have : QuasiCompact d₁ := MorphismProperty.of_isPullback
    (hπ ((SimplexCategory.δ (1 : Fin 2)).op)).flip
    (quasiCompact_cechNerve_face_one f)
  have hset : {y' : (Y _⦋0⦌) | ∃ y₁ : (Y _⦋1⦌),
      d₁.base y₁ = y ∧ d₀.base y₁ = y'} = Set.range (d₁.fiberι y ≫ d₀).base := by
    rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, d₁.range_fiberι]
    ext y'
    simp
  rw [hset]
  exact isCompact_range (d₁.fiberι y ≫ d₀).continuous

end AlgebraicGeometry.Simplicial

end
