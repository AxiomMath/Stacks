module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EtaSheafPullbackTransport
public import StacksFrontier.Topology.Sheaves.Modules.StalkAcyclic
public import StacksFrontier.Topology.Sheaves.RingedSpace.StalkModulePullback
public import StacksFrontier.Topology.Sheaves.Cohomology.SupportedComplexes.ClosedSubsetPullbackLeftExact

/-!
# Being a quasi-isomorphism is local, along pullbacks that are isomorphisms on stalks

Let `ψ : K^• ⟶ L^•` be a map of complexes of sheaves of modules on a ringed space `Y`.  If every
point `y` of `Y` is the image of a point `x` of a ringed space `V` under a morphism `j : V ⟶ Y`
which is an isomorphism on the stalks at `x`, such that `j^* ψ` is a quasi-isomorphism, then `ψ`
is a quasi-isomorphism.  The case of interest is a family of open immersions covering `Y`.

Quasi-isomorphy is stalkwise (Stacks 08TL), the stalk at `x` of `j^* ψ` is the base change of the
stalk at `y` of `ψ` along the germ map `𝒪_{Y,y} ⟶ 𝒪_{V,x}` (Stacks 0098), and base change along
a ring isomorphism is an equivalence of module categories, so it reflects quasi-isomorphisms.

## Main results

* `Stacks.IdealTorsion.Eta.quasiIso_of_forall_exists_quasiIso_pullbackComplexMap`.
* `Stacks.IdealTorsion.Eta.quasiIso_pullbackComplexMap_of_isIso_stalkMap`: conversely, such a
  pullback preserves quasi-isomorphisms.
* `Stacks.IdealTorsion.Eta.nonempty_iso_Q_pullbackComplex_of_isIso_stalkMap`: and isomorphisms
  in the derived category.
-/

@[expose] public noncomputable section

attribute [local instance_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.SheafedSpace.sheaf Stacks.SheafOfModules.TensorSheafification.structureSheaf

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

open Stacks.RingedSpace (pullbackFunctor)

universe u

namespace Stacks.IdealTorsion.Eta

variable {V Y : RingedSpace.{u}} (j : V ⟶ Y) (x : V.carrier)

/-- A morphism of ringed spaces which is an isomorphism on the stalks at `x` is an isomorphism on
the `RingCat`-valued stalks at `x`. -/
theorem isIso_stalkRingMap_of_isIso_stalkMap [IsIso (j.hom.stalkMap x)] :
    IsIso (Stacks.RingedSpace.stalkRingMap j x) := by
  have h := Stacks.RingedSpace.stalkRingMap_comp_ringStalkCommIso j x
  have h' : Stacks.RingedSpace.stalkRingMap j x =
      (Stacks.RingedSpace.ringStalkCommIso Y (j.hom.base x)).hom ≫
        (forget₂ CommRingCat.{u} RingCat.{u}).map (j.hom.stalkMap x) ≫
          (Stacks.RingedSpace.ringStalkCommIso V x).inv := by
    rw [← Category.assoc, ← h, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rw [h']
  infer_instance

/-- **Base change of stalk modules along a germ map that is an isomorphism is an equivalence.** -/
theorem isEquivalence_stalkBaseChange [IsIso (Stacks.RingedSpace.stalkRingMap j x)] :
    (Stacks.RingedSpace.stalkBaseChange j x).IsEquivalence := by
  let _ := Stacks.RingedSpace.structureStalkCommRing Y (j.hom.base x)
  let _ := Stacks.RingedSpace.structureStalkCommRing V x
  let e := (asIso (Stacks.RingedSpace.stalkRingMap j x)).ringCatIsoToRingEquiv
  have _h1 : (ModuleCat.restrictScalars.{u, u, u} e.toRingHom).IsEquivalence :=
    ModuleCat.restrictScalars_isEquivalence_of_ringEquiv e
  exact (ModuleCat.extendRestrictScalarsAdj.{u, u, u}
    e.toRingHom).isEquivalence_left_of_isEquivalence_right

/-- On stalks, pulling back along `j` is base change along a ring isomorphism, so it preserves and
reflects quasi-isomorphisms. -/
private theorem quasiIso_stalk_pullback_iff [IsIso (j.hom.stalkMap x)]
    {K L : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf)) ℤ}
    (ψ : K ⟶ L) :
    QuasiIso (((AlgebraicGeometry.SheafOfModules.stalkFunctor
        (structureSheafRing V) x).mapHomologicalComplex (ComplexShape.up ℤ)).map
          (((RingedSpaceModuleAdjunction.modulePullback j).mapHomologicalComplex
            (ComplexShape.up ℤ)).map ψ)) ↔
      QuasiIso (((AlgebraicGeometry.SheafOfModules.stalkFunctor
          (structureSheafRing Y) (j.hom.base x)).mapHomologicalComplex
            (ComplexShape.up ℤ)).map ψ) := by
  let E := Stacks.RingedSpace.stalkModulePullbackComplexIso j x (ComplexShape.up ℤ)
  have harrow : Arrow.mk (((AlgebraicGeometry.SheafOfModules.stalkFunctor
        (structureSheafRing V) x).mapHomologicalComplex (ComplexShape.up ℤ)).map
          (((RingedSpaceModuleAdjunction.modulePullback j).mapHomologicalComplex
            (ComplexShape.up ℤ)).map ψ)) ≅
      Arrow.mk (((Stacks.RingedSpace.stalkBaseChange j x).mapHomologicalComplex
        (ComplexShape.up ℤ)).map (((AlgebraicGeometry.SheafOfModules.stalkFunctor
          (structureSheafRing Y) (j.hom.base x)).mapHomologicalComplex
            (ComplexShape.up ℤ)).map ψ)) :=
    Arrow.isoMk (E.app K) (E.app L) (E.hom.naturality ψ).symm
  have := isIso_stalkRingMap_of_isIso_stalkMap j x
  have := isEquivalence_stalkBaseChange j x
  rw [quasiIso_iff_of_arrow_mk_iso _ _ harrow]
  exact HomologicalComplex.quasiIso_map_iff_of_preservesHomology _
    (Stacks.RingedSpace.stalkBaseChange j x)

/-- **Being a quasi-isomorphism is local along stalkwise isomorphisms.** -/
theorem quasiIso_of_forall_exists_quasiIso_pullbackComplexMap
    {K L : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf)) ℤ}
    (ψ : K ⟶ L)
    (h : ∀ y : Y.carrier, ∃ (V : RingedSpace.{u}) (j : V ⟶ Y) (x : V.carrier),
      j.hom.base x = y ∧ IsIso (j.hom.stalkMap x) ∧ QuasiIso (pullbackComplexMap j ψ)) :
    QuasiIso ψ := by
  refine (AlgebraicGeometry.SheafOfModules.quasiIso_iff_forall_stalk_quasiIso
    (Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf) ψ).2 (fun y => ?_)
  obtain ⟨V, j, x, rfl, hiso, hq⟩ := h y
  have hq' := (AlgebraicGeometry.SheafOfModules.quasiIso_iff_forall_stalk_quasiIso
    (Stacks.SheafOfModules.Tensor.ringSheaf V.sheaf) (pullbackComplexMap j ψ)).1 hq x
  have := hiso
  exact (quasiIso_stalk_pullback_iff j x ψ).1 hq'

/-- **Pulling back along a morphism which is an isomorphism on every stalk preserves
quasi-isomorphisms**: on stalks the pullback is base change along a ring isomorphism, an
equivalence of module categories. -/
theorem quasiIso_pullbackComplexMap_of_isIso_stalkMap
    (hj : ∀ x : V.carrier, IsIso (j.hom.stalkMap x))
    {K L : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf)) ℤ}
    (ψ : K ⟶ L) [QuasiIso ψ] : QuasiIso (pullbackComplexMap j ψ) := by
  refine (AlgebraicGeometry.SheafOfModules.quasiIso_iff_forall_stalk_quasiIso
    (Stacks.SheafOfModules.Tensor.ringSheaf V.sheaf) (pullbackComplexMap j ψ)).2 (fun x => ?_)
  have hq := (AlgebraicGeometry.SheafOfModules.quasiIso_iff_forall_stalk_quasiIso
    (Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf) ψ).1 inferInstance (j.hom.base x)
  have := hj x
  exact (quasiIso_stalk_pullback_iff j x ψ).2 hq

/-- **An isomorphism in the derived category survives pullback along a stalkwise isomorphism**:
it is a roof of quasi-isomorphisms, and those pull back to quasi-isomorphisms.  The two models of
the derived categories are arbitrary. -/
theorem nonempty_iso_Q_pullbackComplex_of_isIso_stalkMap
    (hj : ∀ x : V.carrier, IsIso (j.hom.stalkMap x))
    [HasDerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf))]
    [HasDerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf V.sheaf))]
    {K L : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf)) ℤ}
    (e : DerivedCategory.Q.obj K ≅ DerivedCategory.Q.obj L) :
    Nonempty ((DerivedCategory.Q (C := SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf V.sheaf))).obj (pullbackComplex j K) ≅
      DerivedCategory.Q.obj (pullbackComplex j L)) := by
  obtain ⟨X', s, hs, g, hfac⟩ := DerivedCategory.right_fac e.hom
  have hs' : QuasiIso s := (DerivedCategory.isIso_Q_map_iff_quasiIso (φ := s)).1 hs
  have hg : IsIso (DerivedCategory.Q.map g) := by
    have : DerivedCategory.Q.map g = DerivedCategory.Q.map s ≫ e.hom := by
      rw [hfac, IsIso.hom_inv_id_assoc]
    rw [this]; infer_instance
  have hg' : QuasiIso g := (DerivedCategory.isIso_Q_map_iff_quasiIso (φ := g)).1 hg
  have h1 := quasiIso_pullbackComplexMap_of_isIso_stalkMap j hj s
  have h2 := quasiIso_pullbackComplexMap_of_isIso_stalkMap j hj g
  exact ⟨(asIso (DerivedCategory.Q.map (pullbackComplexMap j s))).symm ≪≫
    asIso (DerivedCategory.Q.map (pullbackComplexMap j g))⟩

end Stacks.IdealTorsion.Eta

end
