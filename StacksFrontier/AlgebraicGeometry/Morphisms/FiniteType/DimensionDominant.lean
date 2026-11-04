module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.SetTheory.Cardinal.ENat
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FunctionField.DominantMap
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteType.DimensionFormula
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Dimension.ClosedPoint
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Dimension.NonemptyOpen
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Dimension.Trdeg
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Fibre
public import StacksFrontier.Topology.Dimension.SpecializingSurjection

/-!
# Dimension of a dominant morphism of integral schemes locally of finite type

Let `f : X ⟶ Y` be a dominant morphism of integral schemes, locally of finite type, with `Y`
locally Noetherian. Then

* `dim X ≤ dim Y + trdeg_{R(Y)} R(X)`, and
* equality holds as soon as `f` is a closed map — in particular when `f` is proper.

## Main results

* `AlgebraicGeometry.topologicalKrullDim_le_add_trdeg` — the inequality.
* `AlgebraicGeometry.topologicalKrullDim_eq_add_trdeg_of_isClosedMap` — the equality for a
  closed morphism.

Two facts about the fibre over the generic point are proved along the way and are of independent
use:

* `AlgebraicGeometry.Scheme.Hom.isGenericPoint_asFiber_genericPoint` — the fibre through the
  generic point of an irreducible source has a generic point, namely the image of that point.
* `AlgebraicGeometry.ringKrullDim_stalk_fiber_eq_residueFieldTrdeg` — at a closed point of that
  fibre the local ring has dimension `trdeg_{κ(f η)} κ(η)`.

## Implementation notes

The inequality is not reproved from the dimension formula: it is the general bound
`AlgebraicGeometry.topologicalKrullDim_le_add_iSup_residueFieldTrdeg` (Stacks 0BAG), whose
supremum over the generic points of the irreducible components of `X` collapses to a single term
because `X` is irreducible, together with the identification of that term with the
transcendence degree of the function-field extension.

The equality needs the lower bound `dim Y + r ≤ dim X`, where `r` is that transcendence degree.
It is obtained at one point `x₀` of `X`: a closed point of the fibre over the generic point of
`Y`, which exists because that fibre is a Jacobson space. Such a point has

* coheight at least `r`, because the local ring of the fibre at it is a quotient of the local
  ring of `X` (the fibre inclusion is a preimmersion, hence surjective on stalks) and has
  dimension exactly `r` by the dimension formula for a scheme over a field (Stacks 0A21); and
* height at least `dim Y`, because `f` is closed, so specializations lift along it and any chain
  in `Y` lifts to a chain of specializations of `x₀`
  (`Topology.topologicalKrullDim_le_height_closureSingleton_of_specializingMap`).

Since height plus coheight at any point is at most the dimension, the two bounds add up. The
transcendence degree is cardinal-valued and the dimensions live in `WithBot ℕ∞`, so the
comparison goes through `Cardinal.toENat`; the function-field extension is
`AlgebraicGeometry.functionFieldMap`, and the residue-field transcendence degree at the generic
point is `AlgebraicGeometry.residueFieldTranscendenceDegree`.

## References

* [Stacks Project, Tag 02JX](https://stacks.math.columbia.edu/tag/02JX)
* [Stacks Project, Tag 0BAG](https://stacks.math.columbia.edu/tag/0BAG)
* [Stacks Project, Tag 0A21](https://stacks.math.columbia.edu/tag/0A21)
* [Stacks Project, Tag 0066](https://stacks.math.columbia.edu/tag/0066)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

attribute [local instance] specializationOrder

namespace AlgebraicGeometry

variable {X Y : Scheme.{u}}

/-- The image of the generic point of an irreducible scheme is a generic point of the
scheme-theoretic fibre through it: the fibre inclusion is an embedding, and the generic point of
`X` specializes to the image of every point of the fibre. -/
@[sga "7 VIII 5.2" "more general"]
theorem Scheme.Hom.isGenericPoint_asFiber_genericPoint (f : X ⟶ Y) [IrreducibleSpace X] :
    IsGenericPoint (f.asFiber (genericPoint X))
      (Set.univ : Set (f.fiber (f (genericPoint X)))) := by
  refine isGenericPoint_iff_specializes.mpr fun z => iff_of_true ?_ (Set.mem_univ z)
  refine (f.fiberι (f (genericPoint X))).isEmbedding.specializes_iff.mp ?_
  rw [f.fiberι_asFiber]
  exact genericPoint_specializes _

/-- The scheme-theoretic fibre through the generic point of an irreducible scheme is
irreducible. -/
theorem Scheme.Hom.irreducibleSpace_fiber_genericPoint (f : X ⟶ Y) [IrreducibleSpace X] :
    IrreducibleSpace (f.fiber (f (genericPoint X))) := by
  have hirr : IsIrreducible (Set.univ : Set (f.fiber (f (genericPoint X)))) := by
    rw [← f.isGenericPoint_asFiber_genericPoint]
    exact isIrreducible_singleton.closure
  exact { toPreirreducibleSpace := ⟨hirr.2⟩
          toNonempty := ⟨f.asFiber (genericPoint X)⟩ }

/-- At a closed point of the fibre through the generic point `η` of `X`, the local ring of the
fibre has dimension `trdeg_{κ(f η)} κ(η)`.

The fibre is irreducible with generic point the image of `η`, so its dimension is that
transcendence degree by the dimension formula for a scheme over a field (Stacks 0A21); being
irreducible and locally of finite type over a field, it has that same dimension at every point,
and at a closed point the local dimension is the dimension of the local ring. -/
@[ega "II 7.4.1" "(a) ⇔ (b), special case",
  ega "IV 13.3.4" "special case",
  ega "IV 5.5.8" "special case"]
theorem ringKrullDim_stalk_fiber_eq_residueFieldTrdeg (f : X ⟶ Y) [IrreducibleSpace X]
    [LocallyOfFiniteType f] (q : f.fiber (f (genericPoint X)))
    (hq : IsClosed ({q} : Set (f.fiber (f (genericPoint X))))) :
    ringKrullDim ((f.fiber (f (genericPoint X))).presheaf.stalk q) =
      (residueFieldTranscendenceDegree f (genericPoint X) : WithBot ℕ∞) := by
  have _ : IrreducibleSpace (f.fiber (f (genericPoint X))) :=
    f.irreducibleSpace_fiber_genericPoint
  rw [← topologicalKrullDimAt_eq_krullDimOfRing_stalk (Y.residueField (f (genericPoint X)))
      (f.fiber (f (genericPoint X))) (f.fiberToSpecResidueField (f (genericPoint X))) q hq,
    ← topologicalKrullDim_eq_topologicalKrullDimAt_of_irreducible
      (Y.residueField (f (genericPoint X))) (f.fiber (f (genericPoint X)))
      (f.fiberToSpecResidueField (f (genericPoint X))) q,
    topologicalKrullDim_eq_trdeg_residueField (Y.residueField (f (genericPoint X)))
      (f.fiber (f (genericPoint X))) (f.fiberToSpecResidueField (f (genericPoint X)))
      (f.asFiber (genericPoint X)) f.isGenericPoint_asFiber_genericPoint,
    f.trdeg_residueField_fiber (genericPoint X)]
  rfl

/-- The transcendence degree of the function-field extension of a dominant morphism of integral
schemes is the transcendence degree of the residue-field extension at the generic point. -/
private theorem toENat_trdeg_functionField_eq_residueFieldTrdeg (f : X ⟶ Y)
    [IsIntegral X] [IsIntegral Y] [IsDominant f] :
    letI := (functionFieldMap f).toAlgebra
    Cardinal.toENat (Algebra.trdeg Y.functionField X.functionField) =
      residueFieldTranscendenceDegree f (genericPoint X) := by
  let _ : Algebra Y.functionField X.functionField := (functionFieldMap f).toAlgebra
  let _ : Algebra (Y.residueField (f (genericPoint X))) (X.residueField (genericPoint X)) :=
    (f.residueFieldMap (genericPoint X)).hom.toAlgebra
  exact congrArg Cardinal.toENat (Algebra.trdeg_eq_of_ringEquiv
    (genericResidueEquivOfDominant f) (genericResidueEquiv X) fun a =>
      (DFunLike.congr_fun (residueFieldMap_comp_genericResidueEquivOfDominant f) a).symm)

/-- On an irreducible scheme the supremum defining the quantity `E` of Stacks 0BAE has a single
term, the one at the generic point. -/
private theorem iSup_residueFieldTrdeg_genericPoints (f : X ⟶ Y) [IrreducibleSpace X] :
    (⨆ ξ : genericPoints X, residueFieldTranscendenceDegree f ξ.1) =
      residueFieldTranscendenceDegree f (genericPoint X) := by
  have hsingle : genericPoints X = {genericPoint X} := genericPoints_eq_singleton
  have hmem : genericPoint X ∈ genericPoints X := by simp [hsingle]
  refine le_antisymm (iSup_le ?_) (le_iSup_of_le ⟨genericPoint X, hmem⟩ le_rfl)
  rintro ⟨ξ, hξ⟩
  obtain rfl : ξ = genericPoint X := by simpa [hsingle] using hξ
  exact le_rfl

/-- **Stacks Project, Tag 02JX.** For a dominant morphism of integral schemes locally of finite
type over a locally Noetherian base, the dimension of the source is at most the dimension of the
target plus the transcendence degree of the extension of function fields. -/
@[stacks 02JX "dimension inequality"]
theorem topologicalKrullDim_le_add_trdeg (f : X ⟶ Y) [IsLocallyNoetherian Y]
    [IsIntegral X] [IsIntegral Y] [IsDominant f] [LocallyOfFiniteType f] :
    letI := (functionFieldMap f).toAlgebra
    topologicalKrullDim X ≤ topologicalKrullDim Y +
      (Cardinal.toENat (Algebra.trdeg Y.functionField X.functionField) : WithBot ℕ∞) := by
  let _ : Algebra Y.functionField X.functionField := (functionFieldMap f).toAlgebra
  rw [toENat_trdeg_functionField_eq_residueFieldTrdeg f,
    ← iSup_residueFieldTrdeg_genericPoints f]
  exact topologicalKrullDim_le_add_iSup_residueFieldTrdeg f

/-- The coheight of a point of a scheme is the coheight of the closure of that point in the
poset of irreducible closed subsets. -/
private theorem coheight_closureSingleton (x : X) :
    Order.coheight (IrreducibleCloseds.closureSingleton x) = Order.coheight x := by
  have h : IrreducibleCloseds.closureSingleton x = irreducibleSetEquivPoints.symm x :=
    IrreducibleCloseds.ext (by
      rw [IrreducibleCloseds.coe_closureSingleton, coe_irreducibleEquivPoints_symm_apply])
  rw [h]
  exact Order.coheight_orderIso irreducibleSetEquivPoints.symm x

/-- The lower bound behind the equality of Stacks 02JX: for a closed dominant morphism of
integral schemes locally of finite type, the dimension of the target plus the residue-field
transcendence degree at the generic point is at most the dimension of the source.

Both terms are realised at a single point `x₀` of `X`, a closed point of the fibre over the
generic point of `Y`: the first as a lower bound for its height, the second for its coheight. -/
@[ega "IV 5.6.8" "partial, special case", sga "3 VIB 1.5" "partial"]
private theorem add_residueFieldTrdeg_le_topologicalKrullDim (f : X ⟶ Y)
    [IsIntegral X] [IsIntegral Y] [IsDominant f] [LocallyOfFiniteType f] (hf : IsClosedMap f) :
    topologicalKrullDim Y + (residueFieldTranscendenceDegree f (genericPoint X) : WithBot ℕ∞) ≤
      topologicalKrullDim X := by
  set η := genericPoint X
  set F := f.fiber (f η)
  have _ : IrreducibleSpace F := f.irreducibleSpace_fiber_genericPoint
  -- A closed point of the fibre over the generic point of `Y`: the fibre is Jacobson.
  obtain ⟨q, hq⟩ : ∃ q : F, IsClosed ({q} : Set F) := by
    obtain ⟨q, hq⟩ := nonempty_inter_closedPoints (X := F) (Z := (Set.univ : Set F))
      ⟨f.asFiber η, Set.mem_univ _⟩ isOpen_univ.isLocallyClosed
    exact ⟨q, hq.2⟩
  set x₀ : X := f.fiberι (f η) q
  set Q := IrreducibleCloseds.closureSingleton x₀ with hQdef
  -- The local ring of `X` at `x₀` surjects onto that of the fibre at `q`, whose dimension is
  -- the transcendence degree.
  have hco : (residueFieldTranscendenceDegree f η : WithBot ℕ∞) ≤
      (Order.coheight Q : WithBot ℕ∞) := by
    rw [← ringKrullDim_stalk_fiber_eq_residueFieldTrdeg f q hq, hQdef,
      coheight_closureSingleton, ← ringKrullDim_stalk_eq_coheight]
    exact ringKrullDim_le_of_surjective _ ((f.fiberι (f η)).stalkMap_surjective q)
  -- Chains in `Y` lift to chains of specializations of `x₀`, as `f` is closed.
  have hx₀ : f x₀ = genericPoint Y := by
    have hmem : x₀ ∈ f ⁻¹' {f η} := by
      rw [← Scheme.Hom.range_fiberι f (f η)]
      exact ⟨q, rfl⟩
    exact hmem.trans (map_genericPoint_of_isDominant f)
  have hheight : topologicalKrullDim Y ≤ (Order.height Q : WithBot ℕ∞) :=
    Topology.topologicalKrullDim_le_height_closureSingleton_of_specializingMap
      (fun z : X => f z) f.continuous hf.specializingMap
      (Set.top_eq_univ (α := Y) ▸ genericPoint_spec Y) hx₀
  have hsum : (Order.height Q : WithBot ℕ∞) + (Order.coheight Q : WithBot ℕ∞) ≤
      topologicalKrullDim X := by
    have _ : Nonempty (IrreducibleCloseds X) := ⟨Q⟩
    show _ ≤ Order.krullDim (IrreducibleCloseds X)
    rw [Order.krullDim_eq_iSup_height_add_coheight_of_nonempty]
    exact WithBot.coe_mono
      (le_iSup (fun Z : IrreducibleCloseds X => Order.height Z + Order.coheight Z) Q)
  exact (add_le_add hheight hco).trans hsum

/-- **Stacks Project, Tag 02JX.** For a *closed* dominant morphism of integral schemes locally of
finite type over a locally Noetherian base — in particular for a proper one — the bound on the
dimension of the source is an equality. -/
@[stacks 02JX "equality for closed morphisms"]
theorem topologicalKrullDim_eq_add_trdeg_of_isClosedMap (f : X ⟶ Y) [IsLocallyNoetherian Y]
    [IsIntegral X] [IsIntegral Y] [IsDominant f] [LocallyOfFiniteType f] (hf : IsClosedMap f) :
    letI := (functionFieldMap f).toAlgebra
    topologicalKrullDim X = topologicalKrullDim Y +
      (Cardinal.toENat (Algebra.trdeg Y.functionField X.functionField) : WithBot ℕ∞) := by
  let _ : Algebra Y.functionField X.functionField := (functionFieldMap f).toAlgebra
  refine le_antisymm (topologicalKrullDim_le_add_trdeg f) ?_
  rw [toENat_trdeg_functionField_eq_residueFieldTrdeg f]
  exact add_residueFieldTrdeg_le_topologicalKrullDim f hf

end AlgebraicGeometry

end
