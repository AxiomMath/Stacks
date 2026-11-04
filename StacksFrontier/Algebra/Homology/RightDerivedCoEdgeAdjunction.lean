module

public import StacksFrontier.Algebra.Homology.RightDerivedCoEdge
public import StacksFrontier.Algebra.Homology.DerivedCategory.ExactFunctorExtendHomology

/-!
# The comparison `Hⁱ(Q C) ⟶ Q(Hⁱ C)` for a composite and across an adjunction

`Stacks.Cohomology.RightDerivedCoEdge.homologyToMapHomology` is the comparison
`Hⁱ(Q C) ⟶ Q(Hⁱ C)` of a left exact functor `Q` with homology.  This file proves two of its
formal properties.

* For a composite of two left exact functors it is the composite of the two comparisons.
* For an adjunction `G ⊣ P` with `G` exact, a morphism of complexes `Q : G(C) ⟶ D` induces on
  homology a morphism `G(Hⁱ C) ⟶ Hⁱ D` (through the inverse of the comparison of the exact `G`);
  its transpose `Hⁱ C ⟶ P(Hⁱ D)` across the adjunction is the homology of the transposed morphism
  of complexes `C ⟶ P(D)`, followed by the comparison of `P`.

## Main results

* `Stacks.Cohomology.RightDerivedCoEdge.homologyToMapHomology_comp`
* `Stacks.Cohomology.RightDerivedCoEdge.unit_comp_map_inv_homologyToMapHomology_comp_homologyMap`
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Stacks.Cohomology.RightDerivedCoEdge

variable {ι : Type*} {c : ComplexShape ι}
  {B D E : Type*} [Category* B] [Category* D] [Category* E] [Abelian B] [Abelian D] [Abelian E]

/-- The comparison of cycles for a composite of two additive functors is the composite of the
two comparisons. -/
theorem mapCycles_comp (Q₁ : B ⥤ D) (Q₂ : D ⥤ E) [Q₁.Additive] [Q₂.Additive]
    (C : HomologicalComplex B c) (i : ι) :
    mapCycles (Q₁ ⋙ Q₂) C i =
      Q₂.map (mapCycles Q₁ C i) ≫ mapCycles Q₂ ((Q₁.mapHomologicalComplex c).obj C) i := by
  rw [← cancel_mono ((((Q₁ ⋙ Q₂).mapHomologicalComplex c).obj C).iCycles i), mapCycles_i]
  show _ = (Q₂.map (mapCycles Q₁ C i) ≫ mapCycles Q₂ ((Q₁.mapHomologicalComplex c).obj C) i) ≫
    ((Q₂.mapHomologicalComplex c).obj ((Q₁.mapHomologicalComplex c).obj C)).iCycles i
  rw [Category.assoc, mapCycles_i, ← Q₂.map_comp, mapCycles_i]
  rfl

/-- **The comparison of a composite of left exact functors with homology is the composite of
the two comparisons.** -/
theorem homologyToMapHomology_comp (Q₁ : B ⥤ D) (Q₂ : D ⥤ E) [Q₁.Additive] [Q₂.Additive]
    [PreservesFiniteLimits Q₁] [PreservesFiniteLimits Q₂]
    (C : HomologicalComplex B c) (i : ι) :
    homologyToMapHomology (Q₁ ⋙ Q₂) C i =
      homologyToMapHomology Q₂ ((Q₁.mapHomologicalComplex c).obj C) i ≫
        Q₂.map (homologyToMapHomology Q₁ C i) := by
  rw [← cancel_epi (mapCycles (Q₁ ⋙ Q₂) C i ≫
    (((Q₁ ⋙ Q₂).mapHomologicalComplex c).obj C).homologyπ i), Category.assoc,
    mapCycles_comp_homologyπ_comp_homologyToMapHomology, mapCycles_comp, Category.assoc,
    Category.assoc]
  show _ = Q₂.map (mapCycles Q₁ C i) ≫ mapCycles Q₂ ((Q₁.mapHomologicalComplex c).obj C) i ≫
    ((Q₂.mapHomologicalComplex c).obj ((Q₁.mapHomologicalComplex c).obj C)).homologyπ i ≫
      homologyToMapHomology Q₂ ((Q₁.mapHomologicalComplex c).obj C) i ≫
        Q₂.map (homologyToMapHomology Q₁ C i)
  rw [mapCycles_comp_homologyπ_comp_homologyToMapHomology_assoc, ← Q₂.map_comp, ← Q₂.map_comp,
    mapCycles_comp_homologyπ_comp_homologyToMapHomology]
  rfl

/-- The comparison of cycles of a left exact functor cancels against its inverse. -/
theorem mapCyclesIso_inv_comp_eq_aux {P : D ⥤ B} [P.Additive] [PreservesFiniteLimits P]
    (Dc : HomologicalComplex D c) (i : ι) :
    mapCycles P Dc i ≫ (mapCyclesIso P Dc i).inv ≫ P.map (Dc.homologyπ i) =
      P.map (Dc.homologyπ i) := by
  rw [← mapCyclesIso_hom, Iso.hom_inv_id_assoc]

/-- The unit of an adjunction `G ⊣ P`, applied termwise to a complex, as a morphism of complexes
`C ⟶ P(G(C))`. -/
def unitHomologicalComplex {G : B ⥤ D} {P : D ⥤ B} [G.Additive] [P.Additive] (adj : G ⊣ P)
    (C : HomologicalComplex B c) :
    C ⟶ (P.mapHomologicalComplex c).obj ((G.mapHomologicalComplex c).obj C) where
  f i := adj.unit.app (C.X i)
  comm' i j _ := (adj.unit.naturality (C.d i j)).symm

/-- **The transpose of a morphism of homology objects induced by a morphism of complexes.**  Let
`G ⊣ P` with `G` exact, and let `Q : G(C) ⟶ D` be a morphism of complexes.  The morphism
`G(Hⁱ C) ⟶ Hⁱ D` it induces — the inverse of the comparison of `G` with homology followed by
`Hⁱ(Q)` — transposes across the adjunction to the homology of the transposed morphism of
complexes `C ⟶ P(D)` followed by the comparison of the left exact `P` with homology. -/
theorem unit_comp_map_inv_homologyToMapHomology_comp_homologyMap {G : B ⥤ D} {P : D ⥤ B}
    [G.Additive] [P.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits P] (adj : G ⊣ P) (C : HomologicalComplex B c)
    (Dc : HomologicalComplex D c) (Q : (G.mapHomologicalComplex c).obj C ⟶ Dc) (i : ι) :
    adj.unit.app (C.homology i) ≫
        P.map (inv (homologyToMapHomology G C i) ≫ HomologicalComplex.homologyMap Q i) =
      HomologicalComplex.homologyMap
          (unitHomologicalComplex adj C ≫ (P.mapHomologicalComplex c).map Q) i ≫
        homologyToMapHomology P Dc i := by
  have hG : G.map (C.homologyπ i) ≫ inv (homologyToMapHomology G C i) =
      mapCycles G C i ≫ ((G.mapHomologicalComplex c).obj C).homologyπ i := by
    rw [IsIso.comp_inv_eq, Category.assoc, mapCycles_comp_homologyπ_comp_homologyToMapHomology]
  have hcyc : adj.unit.app (C.cycles i) ≫ P.map (mapCycles G C i ≫
        HomologicalComplex.cyclesMap Q i) ≫ mapCycles P Dc i =
      HomologicalComplex.cyclesMap (unitHomologicalComplex adj C ≫
        (P.mapHomologicalComplex c).map Q) i := by
    rw [← cancel_mono (((P.mapHomologicalComplex c).obj Dc).iCycles i), Category.assoc,
      Category.assoc, mapCycles_i, ← P.map_comp, Category.assoc, HomologicalComplex.cyclesMap_i,
      mapCycles_i_assoc, HomologicalComplex.cyclesMap_i, P.map_comp, ← Category.assoc,
      ← Functor.comp_map G P, ← adj.unit.naturality, Functor.id_map, Category.assoc]
    rfl
  have hR : C.homologyπ i ≫ HomologicalComplex.homologyMap
        (unitHomologicalComplex adj C ≫
          (P.mapHomologicalComplex c).map Q) i ≫ homologyToMapHomology P Dc i =
      adj.unit.app (C.cycles i) ≫ P.map (mapCycles G C i ≫
        HomologicalComplex.cyclesMap Q i) ≫ P.map (Dc.homologyπ i) := by
    rw [HomologicalComplex.homologyπ_naturality_assoc, homologyπ_comp_homologyToMapHomology,
      ← hcyc, Category.assoc, Category.assoc, mapCyclesIso_inv_comp_eq_aux]
  rw [← cancel_epi (C.homologyπ i), hR]
  have hn := adj.unit.naturality (C.homologyπ i)
  simp only [Functor.id_map, Functor.comp_map] at hn
  rw [← Category.assoc, hn, Category.assoc, ← P.map_comp, ← P.map_comp, ← Category.assoc,
    hG, Category.assoc, HomologicalComplex.homologyπ_naturality, Category.assoc]

/-- **For an exact functor the comparison with homology is the homology isomorphism of the
exact functor.** -/
theorem homologyToMapHomology_eq_mapExactHomologyIso_hom (G : B ⥤ D) [G.Additive]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] (C : HomologicalComplex B c) (i : ι) :
    homologyToMapHomology G C i = (Stacks.DerivedIndexing.mapExactHomologyIso G C i).hom := by
  rw [← cancel_epi (mapCycles G C i ≫ ((G.mapHomologicalComplex c).obj C).homologyπ i),
    Category.assoc, mapCycles_comp_homologyπ_comp_homologyToMapHomology, Category.assoc,
    Stacks.DerivedIndexing.homologyπ_mapExactHomologyIso_hom, ← Category.assoc]
  convert (Category.id_comp (G.map (C.homologyπ i))).symm
  rw [← cancel_mono (G.map (C.iCycles i)), Category.assoc,
    Stacks.DerivedIndexing.mapExactCyclesIso_hom_iCycles, mapCycles_i, Category.id_comp]

/-- The comparison of cycles is natural in the complex. -/
theorem mapCycles_comp_cyclesMap (Q : B ⥤ D) [Q.Additive] {C C' : HomologicalComplex B c}
    (φ : C ⟶ C') (i : ι) :
    mapCycles Q C i ≫ HomologicalComplex.cyclesMap ((Q.mapHomologicalComplex c).map φ) i =
      Q.map (HomologicalComplex.cyclesMap φ i) ≫ mapCycles Q C' i := by
  rw [← cancel_mono (((Q.mapHomologicalComplex c).obj C').iCycles i), Category.assoc,
    HomologicalComplex.cyclesMap_i, mapCycles_i_assoc, Category.assoc, mapCycles_i,
    ← Q.map_comp, HomologicalComplex.cyclesMap_i, Q.map_comp]
  rfl

/-- **The comparison `Hⁱ(Q C) ⟶ Q(Hⁱ C)` is natural in the complex.** -/
theorem homologyMap_comp_homologyToMapHomology (Q : B ⥤ D) [Q.Additive]
    [PreservesFiniteLimits Q] {C C' : HomologicalComplex B c} (φ : C ⟶ C') (i : ι) :
    HomologicalComplex.homologyMap ((Q.mapHomologicalComplex c).map φ) i ≫
        homologyToMapHomology Q C' i =
      homologyToMapHomology Q C i ≫ Q.map (HomologicalComplex.homologyMap φ i) := by
  rw [← cancel_epi (mapCycles Q C i ≫ ((Q.mapHomologicalComplex c).obj C).homologyπ i),
    Category.assoc, HomologicalComplex.homologyπ_naturality_assoc, ← Category.assoc,
    mapCycles_comp_cyclesMap, Category.assoc, mapCycles_comp_homologyπ_comp_homologyToMapHomology,
    Category.assoc, mapCycles_comp_homologyπ_comp_homologyToMapHomology_assoc, ← Q.map_comp,
    ← Q.map_comp, HomologicalComplex.homologyπ_naturality]

/-- The comparison of cycles is natural in the functor. -/
theorem mapCycles_comp_cyclesMap_natTrans {Q₁ Q₂ : B ⥤ D} [Q₁.Additive] [Q₂.Additive]
    (α : Q₁ ⟶ Q₂) (C : HomologicalComplex B c) (i : ι) :
    mapCycles Q₁ C i ≫
        HomologicalComplex.cyclesMap ((NatTrans.mapHomologicalComplex α c).app C) i =
      α.app (C.cycles i) ≫ mapCycles Q₂ C i := by
  rw [← cancel_mono (((Q₂.mapHomologicalComplex c).obj C).iCycles i), Category.assoc,
    HomologicalComplex.cyclesMap_i, mapCycles_i_assoc, Category.assoc, mapCycles_i]
  exact α.naturality (C.iCycles i)

/-- **The comparison `Hⁱ(Q C) ⟶ Q(Hⁱ C)` is natural in the functor.** -/
theorem homologyMap_natTrans_comp_homologyToMapHomology {Q₁ Q₂ : B ⥤ D} [Q₁.Additive]
    [Q₂.Additive] [PreservesFiniteLimits Q₁] [PreservesFiniteLimits Q₂] (α : Q₁ ⟶ Q₂)
    (C : HomologicalComplex B c) (i : ι) :
    HomologicalComplex.homologyMap ((NatTrans.mapHomologicalComplex α c).app C) i ≫
        homologyToMapHomology Q₂ C i =
      homologyToMapHomology Q₁ C i ≫ α.app (C.homology i) := by
  rw [← cancel_epi (mapCycles Q₁ C i ≫ ((Q₁.mapHomologicalComplex c).obj C).homologyπ i)]
  simp only [Category.assoc]
  rw [HomologicalComplex.homologyπ_naturality_assoc, ← Category.assoc (mapCycles Q₁ C i),
    mapCycles_comp_cyclesMap_natTrans, Category.assoc,
    mapCycles_comp_homologyπ_comp_homologyToMapHomology,
    mapCycles_comp_homologyπ_comp_homologyToMapHomology_assoc]
  exact (α.naturality (C.homologyπ i)).symm

/-- **The transpose of a morphism of cohomology objects, read on the global sections of the
right adjoint.**  Let `G ⊣ P` with `G` exact, `T : B ⥤ E` and `T' : D ⥤ E'` left exact,
`r : E' ⥤ E` exact, and `e : P ⋙ T ≅ T' ⋙ r`.  For a morphism of complexes `Q : G(C) ⟶ D`, the
morphism `θ : G(Hⁱ C) ⟶ Hⁱ D` it induces satisfies

`Hⁱ(T C) ⟶ T(Hⁱ C) ⟶ T(P G Hⁱ C) ⟶ r(T'(G Hⁱ C)) ⟶ r(T'(Hⁱ D))`
  `= Hⁱ(T C) ⟶ Hⁱ(T P D) ⟶ Hⁱ(r T' D) ⟶ r(Hⁱ(T' D)) ⟶ r(T'(Hⁱ D))`,

the first composite being `T` of the unit followed by `e` and `r T'(θ)`, the second the cohomology
of the transposed morphism of complexes followed by `e` on complexes and the two comparisons. -/
theorem homologyToMapHomology_comp_unit_comp_natIso_comp_map {E E' : Type*} [Category* E]
    [Category* E'] [Abelian E] [Abelian E'] {G : B ⥤ D} {P : D ⥤ B} [G.Additive] [P.Additive]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] [PreservesFiniteLimits P]
    (adj : G ⊣ P) (T : B ⥤ E) (T' : D ⥤ E') (r : E' ⥤ E) [T.Additive] [T'.Additive]
    [r.Additive] [PreservesFiniteLimits T] [PreservesFiniteLimits T'] [PreservesFiniteLimits r]
    (e : P ⋙ T ≅ T' ⋙ r) (C : HomologicalComplex B c) (Dc : HomologicalComplex D c)
    (Q : (G.mapHomologicalComplex c).obj C ⟶ Dc) (i : ι) :
    homologyToMapHomology T C i ≫ T.map (adj.unit.app (C.homology i)) ≫
        e.hom.app (G.obj (C.homology i)) ≫
        r.map (T'.map (inv (homologyToMapHomology G C i) ≫
          HomologicalComplex.homologyMap Q i)) =
      HomologicalComplex.homologyMap ((T.mapHomologicalComplex c).map
          (unitHomologicalComplex adj C ≫ (P.mapHomologicalComplex c).map Q)) i ≫
        HomologicalComplex.homologyMap ((NatTrans.mapHomologicalComplex e.hom c).app Dc) i ≫
        homologyToMapHomology r ((T'.mapHomologicalComplex c).obj Dc) i ≫
        r.map (homologyToMapHomology T' Dc i) := by
  have hnat : T.map (P.map (inv (homologyToMapHomology G C i) ≫
        HomologicalComplex.homologyMap Q i)) ≫ e.hom.app (Dc.homology i) =
      e.hom.app (G.obj (C.homology i)) ≫ r.map (T'.map (inv (homologyToMapHomology G C i) ≫
        HomologicalComplex.homologyMap Q i)) :=
    e.hom.naturality _
  calc homologyToMapHomology T C i ≫ T.map (adj.unit.app (C.homology i)) ≫
        e.hom.app (G.obj (C.homology i)) ≫
        r.map (T'.map (inv (homologyToMapHomology G C i) ≫
          HomologicalComplex.homologyMap Q i))
      = homologyToMapHomology T C i ≫ T.map (adj.unit.app (C.homology i) ≫
          P.map (inv (homologyToMapHomology G C i) ≫ HomologicalComplex.homologyMap Q i)) ≫
          e.hom.app (Dc.homology i) := by
        rw [← hnat, T.map_comp, Category.assoc]
    _ = (homologyToMapHomology T C i ≫ T.map (HomologicalComplex.homologyMap
          (unitHomologicalComplex adj C ≫ (P.mapHomologicalComplex c).map Q) i)) ≫
          T.map (homologyToMapHomology P Dc i) ≫ e.hom.app (Dc.homology i) := by
        rw [unit_comp_map_inv_homologyToMapHomology_comp_homologyMap adj C Dc Q i, T.map_comp,
          Category.assoc, Category.assoc]
    _ = HomologicalComplex.homologyMap ((T.mapHomologicalComplex c).map
          (unitHomologicalComplex adj C ≫ (P.mapHomologicalComplex c).map Q)) i ≫
          homologyToMapHomology (P ⋙ T) Dc i ≫ e.hom.app (Dc.homology i) := by
        rw [← homologyMap_comp_homologyToMapHomology T, homologyToMapHomology_comp P T Dc i,
          Category.assoc, Category.assoc]
    _ = _ := by
        rw [← homologyMap_natTrans_comp_homologyToMapHomology e.hom Dc i,
          homologyToMapHomology_comp T' r Dc i]

/-- **Moving the cohomology of a morphism of complexes across a square of exact functors.**

Let `σ : r₁ ⋙ r₂ ≅ r₃ ⋙ r₄` be a square of left exact functors, `a : C₁ ≅ r₂(C₂)` and
`b : D₁ ≅ r₃(D₂)` isomorphisms of complexes, `P : C₂ ⟶ r₁(D₂)` a morphism of complexes and
`T : C₁ ⟶ r₄(D₁)` one with `T ≫ r₄(b) = a ≫ r₂(P) ≫ σ`.  If `c : R₂ ⟶ r₁(R)` is identified with
`Hⁱ(P)` through isomorphisms `R₂ ≅ Hⁱ(C₂)` and `R ≅ Hⁱ(D₂)`, then `Hⁱ(T)`, followed by the
comparison of `r₄` with cohomology, is `r₂(c) ≫ σ` up to isomorphisms on both sides — and the
isomorphism on the right is `r₄` of one. -/
theorem homologyMap_comp_homologyToMapHomology_of_square {E₁ E₂ E₃ E₄ : Type*} [Category* E₁]
    [Category* E₂] [Category* E₃] [Category* E₄] [Abelian E₁] [Abelian E₂] [Abelian E₃]
    [Abelian E₄] {r₁ : E₁ ⥤ E₂} {r₂ : E₂ ⥤ E₃} {r₃ : E₁ ⥤ E₄} {r₄ : E₄ ⥤ E₃}
    [r₁.Additive] [r₂.Additive] [r₃.Additive] [r₄.Additive]
    [PreservesFiniteLimits r₁] [PreservesFiniteLimits r₂] [PreservesFiniteLimits r₃]
    [PreservesFiniteColimits r₃] [PreservesFiniteLimits r₄]
    (σ : r₁ ⋙ r₂ ≅ r₃ ⋙ r₄) {C₁ : HomologicalComplex E₃ c} {C₂ : HomologicalComplex E₂ c}
    {D₁ : HomologicalComplex E₄ c} {D₂ : HomologicalComplex E₁ c}
    (a : C₁ ≅ (r₂.mapHomologicalComplex c).obj C₂) (b : D₁ ≅ (r₃.mapHomologicalComplex c).obj D₂)
    (P : C₂ ⟶ (r₁.mapHomologicalComplex c).obj D₂) (T : C₁ ⟶ (r₄.mapHomologicalComplex c).obj D₁)
    (hT : T ≫ (r₄.mapHomologicalComplex c).map b.hom =
      a.hom ≫ (r₂.mapHomologicalComplex c).map P ≫
        (NatTrans.mapHomologicalComplex σ.hom c).app D₂)
    {R₂ : E₂} {R : E₁} (i : ι) (iX : R₂ ≅ C₂.homology i) (jX : R ≅ D₂.homology i)
    (cP : R₂ ⟶ r₁.obj R)
    (hc : iX.inv ≫ cP = HomologicalComplex.homologyMap P i ≫ homologyToMapHomology r₁ D₂ i ≫
      r₁.map jX.inv) :
    HomologicalComplex.homologyMap T i ≫ homologyToMapHomology r₄ D₁ i =
      (HomologicalComplex.homologyMap a.hom i ≫ homologyToMapHomology r₂ C₂ i ≫ r₂.map iX.inv) ≫
        (r₂.map cP ≫ σ.hom.app R) ≫
        r₄.map (r₃.map jX.hom ≫ inv (homologyToMapHomology r₃ D₂ i) ≫
          HomologicalComplex.homologyMap b.inv i) := by
  have hT' : T = a.hom ≫ (r₂.mapHomologicalComplex c).map P ≫
      (NatTrans.mapHomologicalComplex σ.hom c).app D₂ ≫ (r₄.mapHomologicalComplex c).map b.inv := by
    rw [← reassoc_of% hT, ← Functor.map_comp, b.hom_inv_id, CategoryTheory.Functor.map_id,
      Category.comp_id]
  have hc' : HomologicalComplex.homologyMap P i ≫ homologyToMapHomology r₁ D₂ i =
      iX.inv ≫ cP ≫ r₁.map jX.hom := by
    rw [reassoc_of% hc, ← r₁.map_comp, jX.inv_hom_id, CategoryTheory.Functor.map_id,
      Category.comp_id]
  have hσ := σ.hom.naturality jX.hom
  simp only [Functor.comp_map] at hσ
  have h2' : HomologicalComplex.homologyMap ((NatTrans.mapHomologicalComplex σ.hom c).app D₂) i ≫
      homologyToMapHomology r₄ ((r₃.mapHomologicalComplex c).obj D₂) i =
        homologyToMapHomology r₂ ((r₁.mapHomologicalComplex c).obj D₂) i ≫
          r₂.map (homologyToMapHomology r₁ D₂ i) ≫ σ.hom.app (D₂.homology i) ≫
          r₄.map (inv (homologyToMapHomology r₃ D₂ i)) := by
    rw [← reassoc_of% (homologyToMapHomology_comp r₁ r₂ D₂ i),
      ← reassoc_of% (homologyMap_natTrans_comp_homologyToMapHomology σ.hom D₂ i),
      homologyToMapHomology_comp r₃ r₄ D₂ i, Category.assoc, ← r₄.map_comp, IsIso.hom_inv_id,
      CategoryTheory.Functor.map_id, Category.comp_id]
  rw [hT', HomologicalComplex.homologyMap_comp, HomologicalComplex.homologyMap_comp,
    HomologicalComplex.homologyMap_comp, Category.assoc, Category.assoc, Category.assoc,
    homologyMap_comp_homologyToMapHomology r₄ b.inv i, reassoc_of% h2',
    reassoc_of% (homologyMap_comp_homologyToMapHomology r₂ P i), ← r₂.map_comp_assoc, hc',
    r₂.map_comp, r₂.map_comp, Category.assoc, Category.assoc, reassoc_of% hσ]
  simp only [Category.assoc, Functor.map_comp]

end Stacks.Cohomology.RightDerivedCoEdge

end
