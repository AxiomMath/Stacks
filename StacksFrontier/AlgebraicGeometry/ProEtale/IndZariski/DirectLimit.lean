module

public import Mathlib.Algebra.Colimit.Ring
public import StacksFrontier.AlgebraicGeometry.ProEtale.IndZariski.Basic
public import StacksFrontier.AlgebraicGeometry.ProEtale.IndZariski.FilteredColimit

/-!
# A directed colimit of ind-Zariski algebras is ind-Zariski

Tag 096S says that a filtered colimit of ind-Zariski algebras is ind-Zariski. This file records
the form of that statement which applies to a directed system of `A`-algebras indexed by a
directed order and glued by `Ring.DirectLimit`, the shape in which the source's constructions
produce ind-Zariski algebras.

## Main results

* `AlgebraicGeometry.ProEtale.isIndZariski_directLimit`: the colimit of a directed system of
  ind-Zariski `A`-algebras with `A`-algebra transition maps is ind-Zariski over `A`.

## Implementation notes

The work is to turn the directed system into a filtered diagram in `CommAlgCat A` whose colimit
is the direct limit: the transition maps are algebra maps because they commute with the structure
maps, the canonical maps out of the stages form a cocone by `Ring.DirectLimit.of_f`, and it is
colimiting because `Ring.DirectLimit.lift` is the unique factorization. Tag 096S is then applied
through `AlgebraicGeometry.ProEtale.ind_ind_localIso`.

The structure map `A → Ring.DirectLimit G f` is not constructed here, since a caller that has
already named the colimit algebra needs the statement for its own instance; it is taken as an
`Algebra` instance together with the hypothesis `hof` that it agrees with the composites through
the stages.

## References

* [Stacks Project, Tag 096S](https://stacks.math.columbia.edu/tag/096S)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.ProEtale

variable {A : Type u} [CommRing A] {ι : Type u} [Preorder ι] [IsDirectedOrder ι] [Nonempty ι]
  (G : ι → Type u) [∀ i, CommRing (G i)] [∀ i, Algebra A (G i)]
  (f : ∀ i j, i ≤ j → G i →+* G j)
  [DirectedSystem G fun i j h ↦ f i j h]
  (hf : ∀ i j (h : i ≤ j), (f i j h).comp (algebraMap A (G i)) = algebraMap A (G j))

/-- A transition map of a directed system of `A`-algebras, as a map of `A`-algebras. -/
def directLimitAlgHom (i j : ι) (h : i ≤ j) : G i →ₐ[A] G j where
  toRingHom := f i j h
  commutes' a := DFunLike.congr_fun (hf i j h) a

/-- A directed system of `A`-algebras, as a filtered diagram of `A`-algebras. -/
def directLimitDiagram : ι ⥤ CommAlgCat A where
  obj i := CommAlgCat.of A (G i)
  map {i j} u := CommAlgCat.ofHom (directLimitAlgHom G f hf i j u.le)
  map_id _ := CommAlgCat.hom_ext <| AlgHom.ext fun x ↦
    DirectedSystem.map_self (f := fun i j h ↦ f i j h) x
  map_comp u v := CommAlgCat.hom_ext <| AlgHom.ext fun x ↦
    (DirectedSystem.map_map (f := fun i j h ↦ f i j h) u.le v.le x).symm

section

variable [Algebra A (Ring.DirectLimit G fun i j h ↦ f i j h)]
  (hof : ∀ i, (Ring.DirectLimit.of G (fun i j h ↦ f i j h) i).comp (algebraMap A (G i)) =
    algebraMap A (Ring.DirectLimit G fun i j h ↦ f i j h))

/-- The canonical map from a stage to the direct limit, as a map of `A`-algebras. -/
def directLimitColimitAlgHom (i : ι) :
    G i →ₐ[A] Ring.DirectLimit G fun i j h ↦ f i j h where
  toRingHom := Ring.DirectLimit.of G (fun i j h ↦ f i j h) i
  commutes' a := DFunLike.congr_fun (hof i) a

/-- The direct limit, as the vertex of a cocone on the diagram of the stages. -/
def directLimitCocone : Cocone (directLimitDiagram G f hf) where
  pt := CommAlgCat.of A (Ring.DirectLimit G fun i j h ↦ f i j h)
  ι.app i := CommAlgCat.ofHom (directLimitColimitAlgHom G f hof i)
  ι.naturality _ _ u := CommAlgCat.hom_ext <| AlgHom.ext fun x ↦ Ring.DirectLimit.of_f u.le x

/-- The cocone of the canonical maps to the direct limit is colimiting: `Ring.DirectLimit.lift`
is the unique factorization through it. -/
def directLimitCocone_isColimit : IsColimit (directLimitCocone G f hf hof) := by
  refine IsColimit.ofExistsUnique fun t ↦ ?_
  have hcompat (i j : ι) (h : i ≤ j) (x : G i) :
      (t.ι.app j).hom (f i j h x) = (t.ι.app i).hom x :=
    AlgHom.congr_fun (congrArg CommAlgCat.Hom.hom (t.w (homOfLE h))) x
  let g : ∀ i : ι, G i →+* (t.pt : Type u) := fun i ↦ (t.ι.app i).hom.toRingHom
  let F : ∀ i j, i ≤ j → G i → G j := fun i j h ↦ f i j h
  let desc : (Ring.DirectLimit G F) →ₐ[A] t.pt :=
    { toRingHom := Ring.DirectLimit.lift G F t.pt g hcompat
      commutes' := fun a ↦ by
        rw [← DFunLike.congr_fun (hof (Classical.arbitrary ι)) a]
        exact (Ring.DirectLimit.lift_of (G := G) (f := F) t.pt g hcompat _ _).trans
          ((t.ι.app (Classical.arbitrary ι)).hom.commutes a) }
  refine ⟨CommAlgCat.ofHom desc, fun i ↦ CommAlgCat.hom_ext <| AlgHom.ext fun x ↦
    Ring.DirectLimit.lift_of (G := G) (f := F) t.pt g hcompat i x, fun m hm ↦
    CommAlgCat.hom_ext <| AlgHom.ext fun x ↦ ?_⟩
  obtain ⟨i, y, rfl⟩ := Ring.DirectLimit.exists_of x
  exact (AlgHom.congr_fun (congrArg CommAlgCat.Hom.hom (hm i)) y).trans
    (Ring.DirectLimit.lift_of (G := G) (f := F) t.pt g hcompat i y).symm

include hf hof in
/-- If every stage of a directed system of `A`-algebras with `A`-algebra transition maps is
ind-Zariski over `A`, so is its direct limit. This is the directed-system form of Tag 096S,
`AlgebraicGeometry.ProEtale.isIndZariski_of_colimitPresentation`. -/
theorem isIndZariski_directLimit (hstage : ∀ i, Algebra.IsIndZariski A (G i)) :
    Algebra.IsIndZariski A (Ring.DirectLimit G fun i j h ↦ f i j h) := by
  have hind : ((CommAlgCat.localIso.{u, u} A).ind.{u}).ind.{u}
      (CommAlgCat.of A (Ring.DirectLimit G fun i j h ↦ f i j h)) :=
    ObjectProperty.of_essentiallySmall_index
      ⟨directLimitDiagram G f hf, (directLimitCocone G f hf hof).ι,
        directLimitCocone_isColimit G f hf hof⟩
      fun i ↦ Algebra.isIndZariski_iff.mp (hstage i)
  rw [ind_ind_localIso.{u, u}] at hind
  exact Algebra.isIndZariski_iff.mpr hind

end

end AlgebraicGeometry.ProEtale

end
