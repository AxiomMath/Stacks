module

public import StacksFrontier.Algebra.Homology.RightDerivedCoEdge

/-!
# The homology comparison of a left exact functor, under composition and adjunction

For a left exact additive functor `Q` between abelian categories and a homological complex `C`,
`Stacks.Cohomology.RightDerivedCoEdge.homologyToMapHomology Q C i` is the canonical comparison
`Hⁱ(Q C) ⟶ Q(Hⁱ C)`; it is an isomorphism when `Q` is exact. This file records how it behaves
under composition of functors and under an adjunction `L ⊣ R` with `L` exact.

## Main definitions

* `Stacks.Cohomology.HomologyAdjunction.adjointHom`: for an adjunction `L ⊣ R` and a morphism of
  complexes `χ : C ⟶ R K`, the adjoint morphism `L C ⟶ K`, degreewise.

## Main results

* `Stacks.Cohomology.HomologyAdjunction.homologyToMapHomology_comp`: the comparison of a
  composite `Q₁ ⋙ Q₂` is the comparison of `Q₂` followed by `Q₂` applied to that of `Q₁`.
* `Stacks.Cohomology.HomologyAdjunction.homologyMap_comp_homologyToMapHomology_eq`: for
  `L ⊣ R` with `L` exact, the map `Hⁱ C ⟶ Hⁱ(R K) ⟶ R(Hⁱ K)` induced by `χ : C ⟶ R K` is the
  adjoint of `L(Hⁱ C) ≅ Hⁱ(L C) ⟶ Hⁱ K`, the map induced by the adjoint of `χ`.
-/

@[expose] public noncomputable section

open CategoryTheory Category Limits

universe w v₁ v₂ v₃ u₁ u₂ u₃

namespace Stacks.Cohomology.HomologyAdjunction

open RightDerivedCoEdge

variable {ι : Type w} {c : ComplexShape ι}
  {A : Type u₁} [Category.{v₁} A] [Abelian A]
  {B : Type u₂} [Category.{v₂} B] [Abelian B]
  {D : Type u₃} [Category.{v₃} D] [Abelian D]

section Comp

variable (Q₁ : A ⥤ B) (Q₂ : B ⥤ D) [Q₁.Additive] [Q₂.Additive]
  [PreservesFiniteLimits Q₁] [PreservesFiniteLimits Q₂]

omit [PreservesFiniteLimits Q₁] [PreservesFiniteLimits Q₂] in
/-- The comparison of cycles of a composite is the comparison of the second functor after the
second functor applied to that of the first. -/
lemma mapCycles_comp (C : HomologicalComplex A c) (i : ι) :
    mapCycles (Q₁ ⋙ Q₂) C i =
      Q₂.map (mapCycles Q₁ C i) ≫ mapCycles Q₂ ((Q₁.mapHomologicalComplex c).obj C) i := by
  rw [← cancel_mono (((Q₂.mapHomologicalComplex c).obj
    ((Q₁.mapHomologicalComplex c).obj C)).iCycles i), assoc, mapCycles_i]
  change mapCycles (Q₁ ⋙ Q₂) C i ≫ (((Q₁ ⋙ Q₂).mapHomologicalComplex c).obj C).iCycles i = _
  rw [mapCycles_i, ← Q₂.map_comp, mapCycles_i]
  rfl

/-- **The comparison of a composite.** -/
lemma homologyToMapHomology_comp (C : HomologicalComplex A c) (i : ι) :
    homologyToMapHomology (Q₁ ⋙ Q₂) C i =
      homologyToMapHomology Q₂ ((Q₁.mapHomologicalComplex c).obj C) i ≫
        Q₂.map (homologyToMapHomology Q₁ C i) := by
  rw [← cancel_epi ((((Q₁ ⋙ Q₂).mapHomologicalComplex c).obj C).homologyπ i),
    ← cancel_epi (mapCycles (Q₁ ⋙ Q₂) C i), mapCycles_comp_homologyπ_comp_homologyToMapHomology,
    mapCycles_comp Q₁ Q₂ C i, assoc]
  change Q₂.map (Q₁.map (C.homologyπ i)) = Q₂.map (mapCycles Q₁ C i) ≫
    mapCycles Q₂ ((Q₁.mapHomologicalComplex c).obj C) i ≫
    (((Q₂.mapHomologicalComplex c).obj ((Q₁.mapHomologicalComplex c).obj C)).homologyπ i) ≫
      homologyToMapHomology Q₂ ((Q₁.mapHomologicalComplex c).obj C) i ≫
        Q₂.map (homologyToMapHomology Q₁ C i)
  rw [mapCycles_comp_homologyπ_comp_homologyToMapHomology_assoc, ← Q₂.map_comp,
    ← Q₂.map_comp, mapCycles_comp_homologyπ_comp_homologyToMapHomology]

end Comp

section Adjunction

variable {L : B ⥤ D} {R : D ⥤ B} (adj : L ⊣ R) [L.Additive] [R.Additive]

/-- The adjoint `L C ⟶ K` of a morphism of complexes `C ⟶ R K`, degreewise. -/
def adjointHom {C : HomologicalComplex B c} {K : HomologicalComplex D c}
    (χ : C ⟶ (R.mapHomologicalComplex c).obj K) :
    (L.mapHomologicalComplex c).obj C ⟶ K where
  f n := (adj.homEquiv _ _).symm (χ.f n)
  comm' n m _ :=
    calc (adj.homEquiv _ _).symm (χ.f n) ≫ K.d n m
        = (adj.homEquiv _ _).symm (χ.f n ≫ R.map (K.d n m)) :=
          (Adjunction.homEquiv_naturality_right_symm adj _ _).symm
      _ = (adj.homEquiv _ _).symm (C.d n m ≫ χ.f m) := congrArg _ (χ.comm n m)
      _ = L.map (C.d n m) ≫ (adj.homEquiv _ _).symm (χ.f m) :=
          Adjunction.homEquiv_naturality_left_symm adj _ _

/-- In degree `n`, the adjoint of `χ : C ⟶ R K` is the adjoint of the component `χ.f n`. -/
@[simp]
lemma adjointHom_f {C : HomologicalComplex B c} {K : HomologicalComplex D c}
    (χ : C ⟶ (R.mapHomologicalComplex c).obj K) (n : ι) :
    (adjointHom adj χ).f n = (adj.homEquiv _ _).symm (χ.f n) := rfl

variable [PreservesFiniteLimits L] [PreservesFiniteColimits L] [PreservesFiniteLimits R]

omit [PreservesFiniteLimits L] [PreservesFiniteColimits L] in
/-- On cycles, a morphism `C ⟶ R K` is the unit followed by `R` applied to the cycles of its
adjoint. -/
lemma cyclesMap_comp_mapCyclesIso_inv {C : HomologicalComplex B c}
    {K : HomologicalComplex D c} (χ : C ⟶ (R.mapHomologicalComplex c).obj K) (i : ι) :
    HomologicalComplex.cyclesMap χ i ≫ (mapCyclesIso R K i).inv =
      adj.unit.app (C.cycles i) ≫
        R.map (mapCycles L C i ≫ HomologicalComplex.cyclesMap (adjointHom adj χ) i) := by
  have hR : (mapCyclesIso R K i).inv ≫ R.map (K.iCycles i) =
      ((R.mapHomologicalComplex c).obj K).iCycles i := by
    rw [Iso.inv_comp_eq, mapCyclesIso_hom, mapCycles_i]
  rw [← cancel_mono (R.map (K.iCycles i)), assoc, hR, HomologicalComplex.cyclesMap_i, assoc,
    ← R.map_comp, assoc, HomologicalComplex.cyclesMap_i, mapCycles_i_assoc, R.map_comp,
    ← assoc, adj.unit_naturality, assoc, ← Adjunction.homEquiv_unit, adjointHom_f,
    Equiv.apply_symm_apply]

/-- **The homology comparison under an adjunction with exact left adjoint.** For
`χ : C ⟶ R K`, the map `Hⁱ C ⟶ Hⁱ(R K) ⟶ R(Hⁱ K)` is the unit followed by `R` applied to
`L(Hⁱ C) ≅ Hⁱ(L C) ⟶ Hⁱ K`, the map on homology of the adjoint of `χ`. -/
lemma homologyMap_comp_homologyToMapHomology_eq {C : HomologicalComplex B c}
    {K : HomologicalComplex D c} (χ : C ⟶ (R.mapHomologicalComplex c).obj K) (i : ι) :
    HomologicalComplex.homologyMap χ i ≫ homologyToMapHomology R K i =
      adj.unit.app (C.homology i) ≫
        R.map (inv (homologyToMapHomology L C i) ≫
          HomologicalComplex.homologyMap (adjointHom adj χ) i) := by
  rw [← cancel_epi (C.homologyπ i), HomologicalComplex.homologyπ_naturality_assoc,
    homologyπ_comp_homologyToMapHomology]
  have hu := adj.unit.naturality (C.homologyπ i)
  dsimp only [Functor.id_map, Functor.comp_map] at hu
  rw [reassoc_of% hu, ← R.map_comp]
  have h₁ : L.map (C.homologyπ i) ≫ inv (homologyToMapHomology L C i) =
      mapCycles L C i ≫ ((L.mapHomologicalComplex c).obj C).homologyπ i := by
    rw [IsIso.comp_inv_eq, assoc, mapCycles_comp_homologyπ_comp_homologyToMapHomology]
  rw [reassoc_of% h₁, HomologicalComplex.homologyπ_naturality, R.map_comp, R.map_comp,
    ← assoc, cyclesMap_comp_mapCyclesIso_inv adj χ i, R.map_comp, assoc, assoc]

end Adjunction

end Stacks.Cohomology.HomologyAdjunction

end
