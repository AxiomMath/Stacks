module

public import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import Mathlib.CategoryTheory.Limits.Preserves.Filtered
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import StacksFrontier.RingTheory.Flat.LazardDiagram

/-!
# Dévissage along Lazard's theorem

Let `R` be a commutative ring, let `𝒞` be a preadditive category with finite biproducts, and let
`α : F ⟶ G` be a natural transformation between two additive functors
`ModuleCat.{u} R ⥤ 𝒞` which both preserve filtered colimits.  If `α` is invertible at the free
module of rank one then it is invertible at **every flat** `R`-module.

This is the dévissage the source of **Stacks 073K** performs in the proof of its part (2): the
comparison map it has to invert is, in each cohomological degree, the component at `B` of such a
natural transformation, and `B` is flat over `A`.  Writing the flat module as a filtered colimit
of free finite modules is **Stacks 058G**, available here as
`exists_isFiltered_diagram_free_finite_colimit_eq_of_flat`.

## Main results

* `Stacks.FlatDevissage.isIso_app_of_iso`: invertibility of a component transports along an
  isomorphism of the argument.
* `Stacks.FlatDevissage.isIso_app_biproduct`: a component at a finite biproduct is invertible as
  soon as the components at the summands are; this is where additivity is used.
* `Stacks.FlatDevissage.isIso_app_of_free_of_finite`: invertibility at the free module of rank one
  propagates to every free finite module.
* `Stacks.FlatDevissage.isIso_app_of_isColimit`: invertibility propagates along a colimit both
  functors preserve.
* `Stacks.FlatDevissage.isIso_app_of_flat`: **the dévissage.** Invertibility at `R` implies
  invertibility at every flat `R`-module.

## Implementation notes

The index category produced by Lazard's theorem for a module in `Type u` lies in `Type u`, so
preservation of filtered colimits is asked for in the form
`CategoryTheory.Limits.PreservesFilteredColimitsOfSize.{u, u}`, which is exactly what the
colimits appearing here need and is implied by preservation of all colimits — in particular by
being a left adjoint.

Additivity is used only through Mathlib's instance
`CategoryTheory.Functor.preservesFiniteBiproductsOfAdditive`, so the biproduct step needs no
hypothesis beyond `CategoryTheory.Functor.Additive` on the two functors and finite biproducts in
`𝒞`.

The statement is about a *fixed* natural transformation rather than about a pair of functors being
isomorphic: the content of Stacks 073K part (2) is that a particular canonical map is invertible,
not merely that its source and target are isomorphic.

## References

* [Stacks Project, Tag 073K](https://stacks.math.columbia.edu/tag/073K)
* [Stacks Project, Tag 058G](https://stacks.math.columbia.edu/tag/058G)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Stacks.FlatDevissage

universe w v u

variable {R : Type u} [CommRing R] {𝒞 : Type w} [Category.{v} 𝒞] [Preadditive 𝒞]
  {F G : ModuleCat.{u} R ⥤ 𝒞} (α : F ⟶ G)

omit [Preadditive 𝒞] in
/-- **Invertibility of a component transports along an isomorphism of the argument.**  If
`α.app M` is invertible and `M ≅ N`, then `α.app N` is invertible, being the composite of
`α.app M` with the images of the isomorphism under the two functors. -/
theorem isIso_app_of_iso {M N : ModuleCat.{u} R} (e : M ≅ N) (h : IsIso (α.app M)) :
    IsIso (α.app N) := by
  have := h
  have hnat : F.map e.hom ≫ α.app N = α.app M ≫ G.map e.hom := α.naturality e.hom
  have heq : α.app N = F.map e.inv ≫ α.app M ≫ G.map e.hom := by
    rw [← hnat, ← Category.assoc, ← F.map_comp, e.inv_hom_id, F.map_id, Category.id_comp]
  rw [heq]
  infer_instance

/-- **A component at a finite biproduct is invertible as soon as the components at the summands
are.**  Both functors being additive, they preserve the biproduct, and under the two resulting
identifications the component at the biproduct is the biproduct of the components at the
summands. -/
theorem isIso_app_biproduct [HasFiniteBiproducts 𝒞] [F.Additive] [G.Additive] {ι : Type}
    [Finite ι] (f : ι → ModuleCat.{u} R) (h : ∀ i, IsIso (α.app (f i))) :
    IsIso (α.app (⨁ f)) := by
  have := h
  have : IsIso (biproduct.map fun i ↦ α.app (f i)) :=
    (biproduct.mapIso fun i ↦ asIso (α.app (f i))).isIso_hom
  have key : (Functor.mapBiproduct F f).inv ≫ α.app (⨁ f) =
      (biproduct.map fun i ↦ α.app (f i)) ≫ (Functor.mapBiproduct G f).inv := by
    refine biproduct.hom_ext' _ _ fun i ↦ ?_
    rw [← Category.assoc, ← Category.assoc, Functor.mapBiproduct_inv, biproduct.ι_desc,
      α.naturality, biproduct.ι_map, Category.assoc, Functor.mapBiproduct_inv, biproduct.ι_desc]
  have : IsIso ((Functor.mapBiproduct F f).inv ≫ α.app (⨁ f)) := by
    rw [key]; infer_instance
  exact IsIso.of_isIso_comp_left (Functor.mapBiproduct F f).inv (α.app (⨁ f))

/-- The free module of rank one as an object of `ModuleCat`. -/
abbrev unitModule (R : Type u) [CommRing R] : ModuleCat.{u} R := ModuleCat.of R R

/-- A free finite `R`-module is a finite biproduct of copies of the free module of rank one.

The index is taken to be a `Fin n` rather than the chosen basis index, because finite biproducts
are indexed by types in the lowest universe. -/
theorem nonempty_iso_biproduct_of_free_of_finite (M : ModuleCat.{u} R) [Module.Free R M]
    [Module.Finite R M] :
    ∃ n : ℕ, Nonempty (M ≅ ⨁ fun _ : Fin n ↦ unitModule R) := by
  classical
  refine ⟨Fintype.card (Module.Free.ChooseBasisIndex R M), ⟨?_⟩⟩
  refine ((Module.Free.chooseBasis R M).reindex
      (Fintype.equivFin (Module.Free.ChooseBasisIndex R M))).repr.toModuleIso ≪≫ ?_ ≪≫
    (ModuleCat.biproductIsoPi
      fun _ : Fin (Fintype.card (Module.Free.ChooseBasisIndex R M)) ↦ unitModule R).symm
  exact (Finsupp.linearEquivFunOnFinite R R
    (Fin (Fintype.card (Module.Free.ChooseBasisIndex R M)))).toModuleIso

/-- **Invertibility at the free module of rank one propagates to every free finite module.** -/
theorem isIso_app_of_free_of_finite [HasFiniteBiproducts 𝒞] [F.Additive] [G.Additive]
    (h : IsIso (α.app (unitModule R))) (M : ModuleCat.{u} R) [Module.Free R M]
    [Module.Finite R M] : IsIso (α.app M) := by
  obtain ⟨n, ⟨e⟩⟩ := nonempty_iso_biproduct_of_free_of_finite M
  exact isIso_app_of_iso α e.symm (isIso_app_biproduct α _ fun _ ↦ h)

omit [Preadditive 𝒞] in
/-- **Invertibility propagates along a colimit both functors preserve.**  If `α` is invertible at
every value of a diagram and both functors send a colimit cocone on it to a colimit cocone, then
`α` is invertible at the colimit. -/
theorem isIso_app_of_isColimit {J : Type u} [SmallCategory J] (D : J ⥤ ModuleCat.{u} R)
    {c : Cocone D} (hc : IsColimit c) [PreservesColimit D F] [PreservesColimit D G]
    (h : ∀ j, IsIso (α.app (D.obj j))) : IsIso (α.app c.pt) := by
  have : ∀ j, IsIso ((Functor.whiskerLeft D α).app j) := h
  have : IsIso (Functor.whiskerLeft D α) := NatIso.isIso_of_isIso_app _
  have heq : α.app c.pt =
      (IsColimit.coconePointsIsoOfNatIso (isColimitOfPreserves F hc)
        (isColimitOfPreserves G hc) (asIso (Functor.whiskerLeft D α))).hom := by
    refine (isColimitOfPreserves F hc).hom_ext fun j ↦ ?_
    rw [IsColimit.comp_coconePointsIsoOfNatIso_hom]
    exact α.naturality (c.ι.app j)
  rw [heq]
  infer_instance

/-- **The dévissage.**  Let `α : F ⟶ G` be a natural transformation of additive functors
`ModuleCat.{u} R ⥤ 𝒞` which both preserve filtered colimits.  If `α` is invertible at the free
module of rank one, then it is invertible at every flat `R`-module.

The flat module is written as a filtered colimit of free finite modules by Lazard's theorem
(**Stacks 058G**); `isIso_app_of_free_of_finite` handles the terms of the diagram and
`isIso_app_of_isColimit` the colimit. -/
theorem isIso_app_of_flat [HasFiniteBiproducts 𝒞] [F.Additive] [G.Additive]
    [PreservesFilteredColimitsOfSize.{u, u} F] [PreservesFilteredColimitsOfSize.{u, u} G]
    (h : IsIso (α.app (unitModule R))) (M : Type u) [AddCommGroup M] [Module R M]
    [Module.Flat R M] : IsIso (α.app (ModuleCat.of R M)) := by
  obtain ⟨J, _, _, D, c, hc, hfree, hfin, hpt⟩ :=
    exists_isFiltered_diagram_free_finite_colimit_eq_of_flat (R := R) M
  have := hfree
  have := hfin
  have : PreservesColimitsOfShape J F :=
    PreservesFilteredColimitsOfSize.preserves_filtered_colimits (F := F) J
  have : PreservesColimitsOfShape J G :=
    PreservesFilteredColimitsOfSize.preserves_filtered_colimits (F := G) J
  have := isIso_app_of_isColimit α D hc fun j ↦ isIso_app_of_free_of_finite α h (D.obj j)
  rwa [hpt] at this

/-- **The dévissage, for a flat module already presented as an object of `ModuleCat`.**  This is
`Stacks.FlatDevissage.isIso_app_of_flat` read at `M` itself rather than at `ModuleCat.of R M`. -/
theorem isIso_app_of_flat' [HasFiniteBiproducts 𝒞] [F.Additive] [G.Additive]
    [PreservesFilteredColimitsOfSize.{u, u} F] [PreservesFilteredColimitsOfSize.{u, u} G]
    (h : IsIso (α.app (unitModule R))) (M : ModuleCat.{u} R) [Module.Flat R M] :
    IsIso (α.app M) :=
  isIso_app_of_flat α h M

end Stacks.FlatDevissage

end
