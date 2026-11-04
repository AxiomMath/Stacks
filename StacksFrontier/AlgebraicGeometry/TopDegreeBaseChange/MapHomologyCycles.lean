module

public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Algebra.Homology.Additive
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels

/-!
# The cycle-level homology comparison for a right exact functor

Let `G : A ⥤ B` be an additive functor of abelian categories and `K` a cochain complex in `A`.
There is no canonical morphism between `G(H^i K)` and `H^i(G K)` for a general `G`: what
additivity alone supplies is the comparison on **cycles**,

> `mapCycles : G(Z^i K) ⟶ Z^i(G K)`,

obtained from the kernel universal property of the target. It does not descend to homology, since
the descent needs `G` to preserve the cokernel which defines `H^i`. For a **left exact** `G` the
cycles comparison is invertible and one obtains `H^i(G K) ⟶ G(H^i K)`.

This file treats the **right exact** direction: for `G` preserving finite colimits,

> `mapHomology : G(H^i K) ⟶ H^i(G K)`,

characterized by the cycle-class equation

> `G(π) ≫ mapHomology = mapCycles ≫ π`

that determines it, `G(π)` being an epimorphism for exactly the same reason.

## Main definitions

* `Stacks.MapHomologyCycles.mapCycles`: the cycles comparison, for a merely additive `G`.
* `Stacks.MapHomologyCycles.mapHomology`: the homology comparison for a right exact `G`.

## Main results

* `Stacks.MapHomologyCycles.mapCycles_i` and `mapCycles_naturality` characterize `mapCycles`.
* `Stacks.MapHomologyCycles.homologyπ_comp_mapHomology`: the defining cycle-class equation.
* `Stacks.MapHomologyCycles.epi_map_homologyπ`: `G(π)` is an epimorphism.
* `Stacks.MapHomologyCycles.mapHomology_eq`: the cycle-class equation determines `mapHomology`
  uniquely.
* `Stacks.MapHomologyCycles.mapHomology_naturality`: `mapHomology` is natural in the complex.

## Implementation notes

No boundedness hypothesis on `K` is needed: the comparison exists in every degree, and only its
invertibility requires a bound (see
`Stacks.AlgebraicGeometry.TopDegreeBaseChange.mapTopHomologyIso`).
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Stacks.MapHomologyCycles

variable {A : Type*} [Category A] [Abelian A] {B : Type*} [Category B] [Abelian B]

section Cycles

variable (G : A ⥤ B) [G.Additive]

/-- **The comparison `G(Z^i K) ⟶ Z^i(G K)` an additive functor supplies with no exactness
hypothesis.** The cycles of the image complex are a kernel, and `G` applied to the inclusion of
the cycles of `K` is killed by the differential out of degree `i`. -/
def mapCycles (K : CochainComplex A ℤ) (i : ℤ) :
    G.obj (K.cycles i) ⟶
      ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj K).cycles i :=
  ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj K).liftCycles
    (G.map (K.iCycles i)) (i + 1) (by simp)
    (by
      rw [show ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj K).d i (i + 1) =
            G.map (K.d i (i + 1)) from rfl, ← G.map_comp, K.iCycles_d, G.map_zero])

/-- `mapCycles` followed by the inclusion of the cycles of `G K` is `G` applied to the inclusion
of the cycles of `K`. -/
@[reassoc (attr := simp)]
theorem mapCycles_i (K : CochainComplex A ℤ) (i : ℤ) :
    mapCycles G K i ≫
        ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj K).iCycles i =
      G.map (K.iCycles i) :=
  HomologicalComplex.liftCycles_i _ _ _ _ _

/-- `mapCycles` is natural in the complex `K`. -/
@[reassoc]
theorem mapCycles_naturality {K L : CochainComplex A ℤ} (φ : K ⟶ L) (i : ℤ) :
    G.map (HomologicalComplex.cyclesMap φ i) ≫ mapCycles G L i =
      mapCycles G K i ≫ HomologicalComplex.cyclesMap
        ((G.mapHomologicalComplex (ComplexShape.up ℤ)).map φ) i := by
  rw [← cancel_mono (((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj L).iCycles i),
    Category.assoc, Category.assoc, mapCycles_i, HomologicalComplex.cyclesMap_i,
    mapCycles_i_assoc, ← G.map_comp, HomologicalComplex.cyclesMap_i, G.map_comp]
  rfl

/-- **`mapCycles` carries `G` of the boundary map to the boundary map.** -/
@[reassoc]
theorem map_toCycles_comp_mapCycles (K : CochainComplex A ℤ) (i j : ℤ) :
    G.map (K.toCycles i j) ≫ mapCycles G K j =
      ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj K).toCycles i j := by
  rw [← cancel_mono (((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj K).iCycles j),
    Category.assoc, mapCycles_i, ← G.map_comp, K.toCycles_i,
    HomologicalComplex.toCycles_i]
  rfl

end Cycles

section RightExact

variable (G : A ⥤ B) [G.Additive] [PreservesFiniteColimits G]

/-- **`G` carries the cokernel presentation of `H^i K` to one.** `H^i K` is the cokernel of the
boundary map `K.X (i-1) ⟶ K.cycles i`, by `HomologicalComplex.homologyIsCokernel`, and `G`
preserves that cokernel. -/
def mapHomologyIsCokernel (K : CochainComplex A ℤ) (i : ℤ) :
    IsColimit (CokernelCofork.ofπ (G.map (K.homologyπ i))
      (by simp only [← G.map_comp, K.toCycles_comp_homologyπ (i - 1) i, G.map_zero]) :
        Cofork (G.map (K.toCycles (i - 1) i)) 0) :=
  isColimitCoforkMapOfIsColimit' G (K.toCycles_comp_homologyπ (i - 1) i)
    (K.homologyIsCokernel (i - 1) i (by simp))

/-- **`G` applied to the projection from the cycles onto the homology is an epimorphism**, being a
cokernel projection. -/
theorem epi_map_homologyπ (K : CochainComplex A ℤ) (i : ℤ) :
    Epi (G.map (K.homologyπ i)) :=
  epi_of_isColimit_cofork (mapHomologyIsCokernel G K i)

/-- **The comparison `G(H^i K) ⟶ H^i(G K)` for a right exact additive functor**, together with the
cycle-class equation that defines it: `G` of the projection from the cycles, followed by the
comparison, is the cycles comparison followed by the projection. -/
def mapHomologyData (K : CochainComplex A ℤ) (i : ℤ) :
    { e : G.obj (K.homology i) ⟶
        ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj K).homology i //
      G.map (K.homologyπ i) ≫ e =
        mapCycles G K i ≫
          ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj K).homologyπ i } :=
  CokernelCofork.IsColimit.desc' (mapHomologyIsCokernel G K i)
    (mapCycles G K i ≫
      ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj K).homologyπ i)
    (by
      rw [← Category.assoc, map_toCycles_comp_mapCycles,
        HomologicalComplex.toCycles_comp_homologyπ])

/-- **The comparison `G(H^i K) ⟶ H^i(G K)` for a right exact additive functor.** -/
def mapHomology (K : CochainComplex A ℤ) (i : ℤ) :
    G.obj (K.homology i) ⟶
      ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj K).homology i :=
  (mapHomologyData G K i).1

/-- **The cycle-class equation defining `mapHomology`.** -/
@[reassoc]
theorem homologyπ_comp_mapHomology (K : CochainComplex A ℤ) (i : ℤ) :
    G.map (K.homologyπ i) ≫ mapHomology G K i =
      mapCycles G K i ≫
        ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj K).homologyπ i :=
  (mapHomologyData G K i).2

/-- **The cycle-class equation determines `mapHomology`.** Any map out of `G(H^i K)` satisfying it
is `mapHomology`. -/
theorem mapHomology_eq (K : CochainComplex A ℤ) (i : ℤ)
    (e : G.obj (K.homology i) ⟶
      ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj K).homology i)
    (he : G.map (K.homologyπ i) ≫ e =
      mapCycles G K i ≫
        ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj K).homologyπ i) :
    e = mapHomology G K i := by
  have := epi_map_homologyπ G K i
  rw [← cancel_epi (G.map (K.homologyπ i)), he, homologyπ_comp_mapHomology]

/-- `mapHomology` is natural in the complex `K`. -/
@[reassoc]
theorem mapHomology_naturality {K L : CochainComplex A ℤ} (φ : K ⟶ L) (i : ℤ) :
    G.map (HomologicalComplex.homologyMap φ i) ≫ mapHomology G L i =
      mapHomology G K i ≫ HomologicalComplex.homologyMap
        ((G.mapHomologicalComplex (ComplexShape.up ℤ)).map φ) i := by
  have := epi_map_homologyπ G K i
  rw [← cancel_epi (G.map (K.homologyπ i)), ← G.map_comp_assoc,
    HomologicalComplex.homologyπ_naturality, G.map_comp_assoc, homologyπ_comp_mapHomology,
    mapCycles_naturality_assoc, homologyπ_comp_mapHomology_assoc,
    HomologicalComplex.homologyπ_naturality]

end RightExact

end Stacks.MapHomologyCycles

end
