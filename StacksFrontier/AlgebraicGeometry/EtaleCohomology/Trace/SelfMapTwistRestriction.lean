module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.SelfMapFixedPointTrace
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.ClosedImmersionTwistCompat

/-!
# Restricting the self-map twist to a stable subscheme

Let `f : Y ⟶ S` be a morphism of schemes, `φ : Y ⟶ Y` an endomorphism over `S`, and
`i : W ⟶ Y` a morphism with an endomorphism `φ_W` of `W` such that `φ_W ≫ i = i ≫ φ`. Put
`f_W = i ≫ f`. For a sheaf `C` of `Λ`-modules on `S_étale` the restriction map

`g₀ : f^{-1} C ⟶ i_* i^{-1} f^{-1} C ≅ i_* f_W^{-1} C`

intertwines the self-map twist `f^{-1} C ⟶ φ_* f^{-1} C` of
`Stacks.EtaleCohomology.selfMapTwist` with `i_*` of the self-map twist of `f_W^{-1} C` followed
by the comparison `i_* φ_{W,*} ⟶ φ_* i_*`. Both sides are adjoint, under `f^{-1} ⊣ f_*`, to the
unit `C ⟶ f_{W,*} f_W^{-1} C` followed by the identifications of direct images.

For `W` the complement of a `φ`-stable open of a curve this is the compatibility of the twist
`(g^{-1}π)^*` with the closed piece of the open/closed short exact sequence used in Step 9 of
the proof of [Stacks, Tag 03UG].

## Main definitions

* `Stacks.EtaleCohomology.selfMapRestrictionIso`: `i^{-1} f^{-1} ≅ f_W^{-1}`.
* `Stacks.EtaleCohomology.selfMapRestriction`: the restriction map `f^{-1} ⟶ f_W^{-1} ⋙ i_*`.

## Main results

* `Stacks.EtaleCohomology.unit_comp_map_selfMapRestriction`: the adjoint of the restriction map.
* `Stacks.EtaleCohomology.selfMapTwist_comp_map_selfMapRestriction`: the restriction map
  intertwines the two self-map twists.

## References

* [Stacks Project, Tag 03UG](https://stacks.math.columbia.edu/tag/03UG), Step 9.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

universe u r

namespace Stacks.EtaleCohomology

variable (Λ : Type r) [Ring Λ] {Y W S : Scheme.{u}} (f : Y ⟶ S) (i : W ⟶ Y) (fW : W ⟶ S)
  (hW : fW = i ≫ f)

/-- The identification `f^{-1} ⋙ i^{-1} ≅ f_W^{-1}` for `f_W = i ≫ f`. -/
abbrev selfMapRestrictionIso :
    etaleModuleInverseImage.{u, r} Λ f ⋙ etaleModuleInverseImage.{u, r} Λ i ≅
      etaleModuleInverseImage.{u, r} Λ fW :=
  (etaleModuleInverseImageCompIso.{u, r} Λ i f).symm ≪≫
    eqToIso (congrArg (fun m => etaleModuleInverseImage.{u, r} Λ m) hW.symm)

/-- **The restriction map** `f^{-1} C ⟶ i_* i^{-1} f^{-1} C ≅ i_* f_W^{-1} C`: the unit of
`i^{-1} ⊣ i_*` followed by `i_*` of `Stacks.EtaleCohomology.selfMapRestrictionIso`. -/
def selfMapRestriction :
    etaleModuleInverseImage.{u, r} Λ f ⟶
      etaleModuleInverseImage.{u, r} Λ fW ⋙ etaleModuleDirectImage.{u, r} Λ i :=
  Functor.whiskerLeft (etaleModuleInverseImage.{u, r} Λ f)
      (etaleModuleInverseImageAdj.{u, r} Λ i).unit ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight (selfMapRestrictionIso.{u, r} Λ f i fW hW).hom
      (etaleModuleDirectImage.{u, r} Λ i)

/-- The component of `selfMapRestriction` at `C`: the unit of `i^{-1} ⊣ i_*` at `f^{-1} C`
followed by `i_*` of the component of `selfMapRestrictionIso` at `C`. -/
lemma selfMapRestriction_app (C : EtaleModules.{u, r} Λ S) :
    (selfMapRestriction.{u, r} Λ f i fW hW).app C =
      (etaleModuleInverseImageAdj.{u, r} Λ i).unit.app
          ((etaleModuleInverseImage.{u, r} Λ f).obj C) ≫
        (etaleModuleDirectImage.{u, r} Λ i).map
          ((selfMapRestrictionIso.{u, r} Λ f i fW hW).hom.app C) := by
  simp [selfMapRestriction]

/-- **The adjoint of the restriction map**: under `f^{-1} ⊣ f_*` it is the unit of
`f_W^{-1} ⊣ f_{W,*}` followed by `f_{W,*} ≅ f_* i_*`. -/
lemma unit_comp_map_selfMapRestriction (C : EtaleModules.{u, r} Λ S) :
    (etaleModuleInverseImageAdj.{u, r} Λ f).unit.app C ≫
        (etaleModuleDirectImage.{u, r} Λ f).map ((selfMapRestriction.{u, r} Λ f i fW hW).app C) =
      (etaleModuleInverseImageAdj.{u, r} Λ fW).unit.app C ≫
        (etaleModuleDirectImageComp.{u, r} Λ i f fW hW).inv.app
          ((etaleModuleInverseImage.{u, r} Λ fW).obj C) := by
  have h := unit_conjugateEquiv (etaleModuleInverseImageAdj.{u, r} Λ fW)
    ((etaleModuleInverseImageAdj.{u, r} Λ f).comp (etaleModuleInverseImageAdj.{u, r} Λ i))
    (selfMapRestrictionIso.{u, r} Λ f i fW hW).hom C
  have hc : conjugateEquiv (etaleModuleInverseImageAdj.{u, r} Λ fW)
      ((etaleModuleInverseImageAdj.{u, r} Λ f).comp (etaleModuleInverseImageAdj.{u, r} Λ i))
      (selfMapRestrictionIso.{u, r} Λ f i fW hW).hom =
        (etaleModuleDirectImageComp.{u, r} Λ i f fW hW).inv :=
    conjugateEquiv_etaleModuleInverseImageCompIso_inv' Λ i f fW hW
  rw [hc] at h
  rw [h, selfMapRestriction_app, Functor.map_comp]
  simp [Adjunction.comp_unit_app]

/-- **The adjoint of the self-map twist**: the unit of `f^{-1} ⊣ f_*` followed by `f_*` of the
twist is the unit followed by `f_* ≅ f_* φ_*`. -/
lemma unit_comp_map_selfMapTwist {T S : Scheme.{u}} (g : T ⟶ S) (ψ : T ⟶ T) (v : ψ ≫ g = g)
    (C : EtaleModules.{u, r} Λ S) :
    (etaleModuleInverseImageAdj.{u, r} Λ g).unit.app C ≫
        (etaleModuleDirectImage.{u, r} Λ g).map ((selfMapTwist.{u, r} Λ g ψ v).app C) =
      (etaleModuleInverseImageAdj.{u, r} Λ g).unit.app C ≫
        (selfMapDirectImageComp.{u, r} Λ g ψ v).inv.app
          ((etaleModuleInverseImage.{u, r} Λ g).obj C) := by
  refine (Adjunction.homEquiv_unit _ _ _ _).symm.trans ?_
  rw [selfMapTwist_app, Equiv.apply_symm_apply]
  simp [selfMapTwistAdj]

variable (φ : Y ⟶ Y) (w : φ ≫ f = f) (φW : W ⟶ W) (wW : φW ≫ fW = fW) (hi : φW ≫ i = i ≫ φ)

/-- If `t ≫ a ≫ b = c ≫ d` with `a`, `b`, `c` and `d` isomorphisms, then
`inv d ≫ inv c ≫ t = inv b ≫ inv a`. -/
private lemma inv_coherence {D : Type*} [Category D] {A B E F G : D}
    (t : A ⟶ B) (a : B ⟶ E) (b : E ⟶ F) (c : A ⟶ G) (d : G ⟶ F) [IsIso a] [IsIso b] [IsIso c]
    [IsIso d] (h : t ≫ a ≫ b = c ≫ d) : inv d ≫ inv c ≫ t = inv b ≫ inv a := by
  rw [IsIso.inv_comp_eq, IsIso.inv_comp_eq, ← Category.assoc c, ← h]
  simp

include hW in
/-- **The restriction map intertwines the self-map twists.**  For `φ_W ≫ i = i ≫ φ`, the
self-map twist of `f^{-1} C` followed by `φ_*` of the restriction map is the restriction map
followed by `i_*` of the self-map twist of `f_W^{-1} C` and the comparison
`i_* φ_{W,*} ⟶ φ_* i_*`. -/
theorem selfMapTwist_comp_map_selfMapRestriction (C : EtaleModules.{u, r} Λ S) :
    (selfMapTwist.{u, r} Λ f φ w).app C ≫
        (etaleModuleDirectImage.{u, r} Λ φ).map ((selfMapRestriction.{u, r} Λ f i fW hW).app C) =
      (selfMapRestriction.{u, r} Λ f i fW hW).app C ≫
        (etaleModuleDirectImage.{u, r} Λ i).map ((selfMapTwist.{u, r} Λ fW φW wW).app C) ≫
        (directImageTwistTransfer Λ i φW φ hi).app
          ((etaleModuleInverseImage.{u, r} Λ fW).obj C) := by
  apply ((etaleModuleInverseImageAdj.{u, r} Λ f).homEquiv _ _).injective
  have hR := unit_comp_map_selfMapRestriction Λ f i fW hW C
  have hθ := (selfMapDirectImageComp.{u, r} Λ f φ w).inv.naturality
    ((selfMapRestriction.{u, r} Λ f i fW hW).app C)
  have hc := (etaleModuleDirectImageComp.{u, r} Λ i f fW hW).inv.naturality
    ((selfMapTwist.{u, r} Λ fW φW wW).app C)
  have hcoh := inv_coherence _ _ _ _ _ (directImageTwistTransfer_compat Λ i φW φ f fW hi hW
    w.symm wW.symm ((etaleModuleInverseImage.{u, r} Λ fW).obj C))
  simp only [← Iso.app_hom, IsIso.Iso.inv_hom, Iso.app_inv] at hcoh
  dsimp only [Functor.comp_obj, Functor.comp_map, Functor.id_obj] at hθ hc hcoh ⊢
  simp only [Adjunction.homEquiv_unit, Functor.map_comp]
  rw [reassoc_of% (unit_comp_map_selfMapTwist Λ f φ w C), ← hθ, reassoc_of% hR, reassoc_of% hR,
    ← reassoc_of% hc, reassoc_of% (unit_comp_map_selfMapTwist Λ fW φW wW C)]
  exact congrArg (fun z => (etaleModuleInverseImageAdj.{u, r} Λ fW).unit.app C ≫ z) hcoh.symm

end Stacks.EtaleCohomology

end
