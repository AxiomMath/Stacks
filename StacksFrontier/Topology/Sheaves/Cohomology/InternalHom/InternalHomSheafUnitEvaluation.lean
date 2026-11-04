module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafHomPrecomposition
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.InternalHomSheafAsSheafHom
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.InternalHomSheafFromStructureSheaf

/-!
# The trivialised internal Hom sheaf, evaluated on a section

`Stacks.SheafOfModules.internalHomSheafIsoOfIsoUnit` identifies `Hom_{O_X}(F, G)` with `G` for `F`
trivialised by an isomorphism `e : F ≅ O_X`. This file computes it on sections: **the
identification evaluates a homomorphism at the image of the unit section.** A section of
`Hom_{O_X}(F, G)` over `U` is a natural family of maps out of `F` restricted over `U`; the
identification returns its value, at the identity object of the slice site, on `e.inv` of the unit
section.

## Main results

* `Stacks.SheafOfModules.internalHomSheafIsoOfIsoUnit_hom_val_app`: the identification evaluates a
  homomorphism at the image of the unit section.
* `Stacks.SheafOfModules.internalHomSheafUnitIso_inv_sectionsEquiv`: the inverse trivialisation
  `G ≅ Hom_{O_X}(O_X, G)` attaches to a section of `G` the morphism it names, and
  `Stacks.SheafOfModules.unitOverAddEquiv_symm_one`: the morphism named by the unit section is
  the identity.
* `Stacks.SheafOfModules.isPrecomp_internalHomPre`: the contravariant functoriality of the
  internal Hom sheaf of a space is a precomposition map in the sense of Stacks 01CO.
* `Stacks.SheafOfModules.over_val_app_id`: at the identity object of the slice site, a restricted
  morphism acts as the morphism.
* `Stacks.SheafOfModules.eqToHom_over_val_app`: a type-level transport of sections is the
  sheaf-level transport applied.

## Implementation notes

The unit section is taken at the identity object of the slice site, where
`AlgebraicGeometry.RingedSite.unitOverHomEquiv` reads a morphism off and where
`Stacks.SheafOfModules.unitOverAddEquiv_symm_app_one_top` puts a section back.

## References

* [Stacks Project, Tag 01CO](https://stacks.math.columbia.edu/tag/01CO)
* [Stacks Project, Tag 0BQY](https://stacks.math.columbia.edu/tag/0BQY)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf Opposite TopologicalSpace
open AlgebraicGeometry

universe u

namespace Stacks.SheafOfModules

variable {X : TopCat.{u}} (Rc : TopCat.Sheaf CommRingCat.{u} X)
  (G : SheafOfModules.{u} (structureSheaf Rc))
  {F : SheafOfModules.{u} (structureSheaf Rc)}

/-- **The trivialised internal Hom sheaf evaluates a homomorphism at the image of the unit
section.** For `e : F ≅ O_X` and a section `s` of `Hom_{O_X}(F, G)` over `U`, the section of `G`
that `internalHomSheafIsoOfIsoUnit` attaches to `s` is the value of `s` on `e.inv` of the unit
section, taken at the identity object of the slice site over `U`. -/
theorem internalHomSheafIsoOfIsoUnit_hom_val_app
    (e : F ≅ SheafOfModules.unit (structureSheaf Rc)) (U : Opens ↥X)
    (s : (RingedSite.internalHomSheaf (ringedSite Rc) F G).val.obj (op U)) :
    (internalHomSheafIsoOfIsoUnit Rc G e).hom.val.app (op U) s =
      s.app (op (Over.mk (𝟙 U)))
        ((e.inv.over U).val.app (op (Over.mk (𝟙 U)))
          (1 : ((structureSheaf Rc).over U).obj.obj (op (Over.mk (𝟙 U))))) := by
  exact (AddEquiv.symm_apply_eq (unitOverAddEquiv Rc G U)).1
    (SheafHom.isPrecomp_precomp e.inv (internalHomSheafHom Rc F G) (unitSheafHom Rc G) U s)

/-- **The inverse of the trivialisation `Hom_{O_X}(O_X, G) ≅ G` attaches to a section `b` of `G`
over `U` the morphism `O_U ⟶ G|_U` that `b` names.** -/
theorem internalHomSheafUnitIso_inv_sectionsEquiv (U : Opens ↥X) (b : G.val.obj (op U)) :
    (internalHomSheafHom Rc (SheafOfModules.unit (structureSheaf Rc)) G).sectionsEquiv U
        ((internalHomSheafUnitIso Rc G).inv.val.app (op U) b) =
      (unitOverAddEquiv Rc G U).symm b := by
  refine (SheafHom.isPostcomp_postcomp (𝟙 G) (unitSheafHom Rc G)
    (internalHomSheafHom Rc (SheafOfModules.unit (structureSheaf Rc)) G) U b).trans ?_
  have h : SheafOfModules.Hom.over (𝟙 G) U = 𝟙 (G.over U) :=
    (SheafOfModules.overFunctor (structureSheaf Rc) U).map_id G
  rw [h, Category.comp_id]
  rfl

/-- **The morphism `O_U ⟶ O_U` named by the unit section is the identity.** -/
theorem unitOverAddEquiv_symm_one (U : Opens ↥X) :
    (unitOverAddEquiv Rc (SheafOfModules.unit (structureSheaf Rc)) U).symm
        (1 : (structureSheaf Rc).obj.obj (op U)) =
      𝟙 ((SheafOfModules.unit (structureSheaf Rc)).over U) :=
  (unitOverAddEquiv Rc _ U).injective
    (((unitOverAddEquiv Rc _ U).apply_symm_apply _).trans rfl)

/-- **The inverse trivialisation `O_X ≅ Hom_{O_X}(O_X, O_X)` carries the unit section to the
identity.** -/
theorem internalHomSheafUnitIso_inv_sectionsEquiv_one (U : Opens ↥X) :
    (internalHomSheafHom Rc (SheafOfModules.unit (structureSheaf Rc))
          (SheafOfModules.unit (structureSheaf Rc))).sectionsEquiv U
        ((internalHomSheafUnitIso Rc (SheafOfModules.unit (structureSheaf Rc))).inv.val.app
          (op U) (1 : (structureSheaf Rc).obj.obj (op U))) =
      𝟙 ((SheafOfModules.unit (structureSheaf Rc)).over U) :=
  (internalHomSheafUnitIso_inv_sectionsEquiv Rc _ U _).trans (unitOverAddEquiv_symm_one Rc U)

/-- **Precomposition on the internal Hom sheaf of a space is a precomposition map** in the sense
of the characterisation of Stacks 01CO: under the identification of sections of `Hom_{O_X}(A, C)`
with morphisms `A|_U ⟶ C|_U`, the map `AlgebraicGeometry.RingedSite.internalHomPre` induced by
`f : A ⟶ B` acts by precomposition with the restriction of `f`. -/
theorem isPrecomp_internalHomPre {A B : SheafOfModules.{u} (structureSheaf Rc)} (f : A ⟶ B)
    (C : SheafOfModules.{u} (structureSheaf Rc)) :
    SheafHom.IsPrecomp Rc f (internalHomSheafHom Rc B C) (internalHomSheafHom Rc A C)
      (RingedSite.internalHomPre (ringedSite Rc) f) :=
  fun _ _ => rfl

/-- **At the identity object of the slice site, the restriction of a morphism acts as the
morphism.** -/
theorem over_val_app_id {F' G' : SheafOfModules.{u} (structureSheaf Rc)} (ψ : F' ⟶ G')
    (U : Opens ↥X) (m : (F'.over U).val.obj (op (Over.mk (𝟙 U)))) :
    (ψ.over U).val.app (op (Over.mk (𝟙 U))) m = ψ.val.app (op U) m := rfl

/-- **A type-level transport of sections is the sheaf-level transport applied to the section.**
For an equality `h : M = N` of sheaves of modules, transporting a section along the induced
equality of section *types* agrees with applying the morphism `eqToHom h`. -/
theorem eqToHom_over_val_app {M N : SheafOfModules.{u} (structureSheaf Rc)} (h : M = N)
    (U : Opens ↥X) (W : (CategoryTheory.Over U)ᵒᵖ) (z : (M.over U).val.obj W) :
    ((eqToHom h).over U).val.app W z =
      eqToHom (congrArg (fun Z : SheafOfModules.{u} (structureSheaf Rc) =>
        (Z.over U).val.obj W) h) z := by
  subst h
  rfl

end Stacks.SheafOfModules

end
