module

public import Mathlib.AlgebraicGeometry.Fiber
public import StacksFrontier.AlgebraicGeometry.Groupoids.Stabilizer.ModObj
public import StacksFrontier.AlgebraicGeometry.Groupoids.Stabilizer.PairPseudotorsor
public import StacksFrontier.AlgebraicGeometry.GroupScheme.OverField.Torsor
public import StacksCore.Tactic.StacksAttribute

/-!
# Fibres of the arrow scheme of a groupoid

The nonempty fibre of the arrow scheme over a pair of objects is a torsor under the fibre of
the stabilizer at the first object.

## Main definitions

* `AlgebraicGeometry.stabilizerActionOnFiber` is the action obtained by base change from the
  stabilizer action over the pair scheme.

## Main results

* `AlgebraicGeometry.fiber_isFpqcTorsor` gives the torsor property of a nonempty fibre.

## References

* [Stacks Project, Tag 04Q3](https://stacks.math.columbia.edu/tag/04Q3)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CartesianMonoidalCategory MonoidalCategory MonObj
open Stacks.Groupoids

universe u

namespace AlgebraicGeometry

/-- The fibre of the base-changed stabilizer over a point of the pair scheme, as a scheme over the
spectrum of the residue field at that point. -/
abbrev fiberGroup {S : Scheme.{u}} (G : GroupoidScheme S)
    (p : (G.objects ⊗ G.objects).left) :
    Over (Scheme.Spec.obj (.op ((G.objects ⊗ G.objects).left.residueField p))) :=
  (Over.pullback ((G.objects ⊗ G.objects).left.fromSpecResidueField p)).obj
    (stabilizerOverPairs G)

/-- The fibre of the arrow scheme over a point of the pair scheme, as a scheme over the spectrum of
the residue field at that point. -/
abbrev fiberArrows {S : Scheme.{u}} (G : GroupoidScheme S)
    (p : (G.objects ⊗ G.objects).left) :
    Over (Scheme.Spec.obj (.op ((G.objects ⊗ G.objects).left.residueField p))) :=
  (Over.pullback ((G.objects ⊗ G.objects).left.fromSpecResidueField p)).obj
    (arrowsOverPairs G)

/-- The group structure on the fibre of the stabilizer, the base change of the group structure of
the stabilizer over the pair scheme. -/
instance fiberGroupGrpObj {S : Scheme.{u}} (G : GroupoidScheme S)
    (p : (G.objects ⊗ G.objects).left) : GrpObj (fiberGroup G p) := by
  let : GrpObj (Over.mk (stabilizerOverPairs G).hom) :=
    inferInstanceAs (GrpObj (stabilizerOverPairs G))
  exact Over.grpObjMkPullbackSnd

/-- A `ModObj` structure on the fibre is the base change of the action over the pair scheme when
its action morphism is the image of that action morphism under the pullback functor. -/
def IsFiberAction {S : Scheme.{u}} (G : GroupoidScheme S)
    (p : (G.objects ⊗ G.objects).left)
    (h : ModObj (fiberGroup G p) (fiberArrows G p)) : Prop :=
  let := h
  γ[fiberGroup G p, fiberArrows G p] =
    (prodComparisonIso
      (Over.pullback ((G.objects ⊗ G.objects).left.fromSpecResidueField p))
      (stabilizerOverPairs G) (arrowsOverPairs G)).inv ≫
      (Over.pullback ((G.objects ⊗ G.objects).left.fromSpecResidueField p)).map
        γ[stabilizerOverPairs G, arrowsOverPairs G]

/-- The canonical action on the fibre, induced from the action over pairs. -/
@[stacks 04Q3 "action on the fibre"]
def stabilizerActionOnFiber {S : Scheme.{u}} (G : GroupoidScheme S)
    (p : (G.objects ⊗ G.objects).left) :
    { h : ModObj (fiberGroup G p) (fiberArrows G p) // IsFiberAction G p h } := by
  classical
  let f := Over.pullback ((G.objects ⊗ G.objects).left.fromSpecResidueField p)
  let : ModObj (stabilizerOverPairs G) (arrowsOverPairs G) :=
    stabilizerActionOverPairs G
  let : f.Monoidal := Functor.Monoidal.ofChosenFiniteProducts f
  let : ModObj (fiberGroup G p) (fiberArrows G p) :=
    Functor.LaxMonoidal.modObj f (fiberGroupGrpObj G p).toMonObj (by rfl) (by rfl)
  refine ⟨inferInstance, ?_⟩
  change Functor.LaxMonoidal.μ f (stabilizerOverPairs G) (arrowsOverPairs G) ≫
      f.map γ[stabilizerOverPairs G, arrowsOverPairs G] = _
  rw [Functor.Monoidal.μ_of_cartesianMonoidalCategory]

/-- The action of the fibre of the stabilizer on the fibre of the arrow scheme given by
`stabilizerActionOnFiber`. -/
instance fiberArrowsModObj {S : Scheme.{u}} (G : GroupoidScheme S)
    (p : (G.objects ⊗ G.objects).left) :
    ModObj (fiberGroup G p) (fiberArrows G p) :=
  (stabilizerActionOnFiber G p).1

/-- A nonempty fibre of the arrows over a pair is a torsor under the corresponding
stabilizer group over the residue field. -/
@[stacks 04Q3 "torsor property"]
theorem fiber_isFpqcTorsor {S : Scheme.{u}} (G : GroupoidScheme S)
    (p : (G.objects ⊗ G.objects).left) (h : Nonempty (fiberArrows G p).left) :
    IsFpqcTorsor
      (Scheme.Spec.obj (.op ((G.objects ⊗ G.objects).left.residueField p)))
      (fiberGroup G p) (fiberArrows G p) := by
  let B := Scheme.Spec.obj (.op ((G.objects ⊗ G.objects).left.residueField p))
  change IsPseudoTorsor (fiberGroup G p) (fiberArrows G p) ∧
    ∃ (I : Type (u + 1)) (T : I → Scheme.{u}) (f : ∀ i, T i ⟶ B),
      Presieve.ofArrows T f ∈ Scheme.fpqcPrecoverage B ∧
        ∀ i, Nonempty (𝟙_ (Over (T i)) ⟶ (Over.pullback (f i)).obj (fiberArrows G p))
  constructor
  · let f := Over.pullback ((G.objects ⊗ G.objects).left.fromSpecResidueField p)
    let _ : ModObj (stabilizerOverPairs G) (arrowsOverPairs G) :=
      stabilizerActionOverPairs G
    let M' : MonObj (f.obj (stabilizerOverPairs G)) :=
      (fiberGroupGrpObj G p).toMonObj
    let _ : MonObj (fiberGroup G p) := M'
    let _ : ModObj (fiberGroup G p) (fiberArrows G p) :=
      Functor.LaxMonoidal.modObj f M' (by rfl) (by rfl)
    have hBridge := Functor.LaxMonoidal.mapModObj_leftSMul (M := stabilizerOverPairs G)
      (X := arrowsOverPairs G) f M' (by rfl) (by rfl)
    change IsIso (ModObj.leftSMul (fiberGroup G p) (fiberArrows G p))
    rw [hBridge]
    have hPair : IsPseudoTorsor (stabilizerOverPairs G) (arrowsOverPairs G) :=
      stabilizerActionOverPairs_pseudoTorsor G
    let _ : IsIso (ModObj.leftSMul (stabilizerOverPairs G) (arrowsOverPairs G)) := hPair
    infer_instance
  · obtain ⟨x⟩ := h
    let X := (fiberArrows G p).left
    let K := (G.objects ⊗ G.objects).left.residueField p
    let L := X.residueField x
    let T := Scheme.Spec.obj (.op (CommRingCat.of L))
    let q : T ⟶ X := X.fromSpecResidueField x
    let f : T ⟶ B := q ≫ (fiberArrows G p).hom
    let φ : CommRingCat.of K ⟶ CommRingCat.of L :=
      (Spec.homEquiv (R := CommRingCat.of K) (S := CommRingCat.of L)) f
    have hSpec : Spec.map φ = f :=
      (Spec.homEquiv (R := CommRingCat.of K) (S := CommRingCat.of L)).symm_apply_apply f
    have hFF : φ.hom.FaithfullyFlat := by
      let _ : Module K L := φ.hom.toModule
      change Module.FaithfullyFlat K L
      infer_instance
    have hFlatSurj := (AlgebraicGeometry.flat_and_surjective_SpecMap_iff φ).2 hFF
    let _ : Flat f := hSpec ▸ hFlatSurj.1
    let _ : Surjective f := hSpec ▸ hFlatSurj.2
    let _ : QuasiCompact f := by
      rw [← hSpec]
      infer_instance
    refine ⟨PUnit, fun _ => T, fun _ => f, ?_, ?_⟩
    · rw [Presieve.ofArrows_pUnit]
      exact Scheme.Hom.singleton_mem_fpqcPrecoverage f
    · intro i
      let qOver : (Over.map f).obj (𝟙_ (Over T)) ⟶ fiberArrows G p :=
        Over.homMk q (by
          change q ≫ (fiberArrows G p).hom = q ≫ (fiberArrows G p).hom
          rfl)
      exact ⟨(Over.mapPullbackAdj f).homEquiv (𝟙_ (Over T))
        (fiberArrows G p) qOver⟩


end AlgebraicGeometry

end
