module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafHomPostcomposition
public import StacksFrontier.CategoryTheory.Sites.Cohomology.StrictlyPerfect.InternalHomUnitSource
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.InternalHomSheafAsSheafHom

/-!
# The internal Hom sheaf out of the structure sheaf

Let `(X, O_X)` be a topological space carrying a sheaf of commutative rings and let `G` be a
sheaf of `O_X`-modules. A morphism of `O_U`-modules `O_U ⟶ G|_U` is its value at the unit
section, so the sections of the internal Hom sheaf `Hom_{O_X}(O_X, G)` over `U` are the sections
of `G` over `U`, naturally in `U` and compatibly with the action of `O_X`:

`Hom_{O_X}(O_X, G) ≅ G`.

More generally the same holds for the internal Hom sheaf out of any sheaf of modules
trivialised by an isomorphism with the structure sheaf.

## Main definitions

* `Stacks.SheafOfModules.unitOverAddEquiv`: a morphism `O_U ⟶ G|_U` is its value at the unit
  section, as an isomorphism of additive groups.
* `Stacks.SheafOfModules.unitSheafHom`: **`G` itself is the internal Hom sheaf out of the
  structure sheaf**, in the sense of the characterising structure of Stacks 01CO.
* `Stacks.SheafOfModules.internalHomSheafUnitIso`: **`Hom_{O_X}(O_X, G) ≅ G`**.
* `Stacks.SheafOfModules.internalHomSheafIsoOfIsoUnit`: **`Hom_{O_X}(F, G) ≅ G` for `F`
  isomorphic to the structure sheaf**, the isomorphism being precomposition with the
  trivialisation.

## Main results

* `Stacks.SheafOfModules.unitOverAddEquiv_symm_app_one`: the morphism attached to a section `b`
  of `G` over `U` sends the unit section over an open of the slice over `U` to the restriction of
  `b` to that open.
* `Stacks.SheafOfModules.unitOverAddEquiv_symm_restrict` and
  `Stacks.SheafOfModules.unitOverAddEquiv_symm_smul`: that assignment is compatible with
  restriction and with the action of the structure sheaf, as equalities of morphisms of
  restrictions.

## Implementation notes

The compatibilities with restriction and with the action of `O_X` are proved as equalities of
morphisms of restrictions, which are determined by their value at the unit section; stated
componentwise, the scalar action on a restricted section is not found by the elaborator without a
transport.

## References

* [Stacks Project, Tag 01CO](https://stacks.math.columbia.edu/tag/01CO)
* [Stacks Project, Tag 03EM](https://stacks.math.columbia.edu/tag/03EM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf Opposite TopologicalSpace
open AlgebraicGeometry

universe u

namespace Stacks.SheafOfModules

variable {X : TopCat.{u}} (Rc : TopCat.Sheaf CommRingCat.{u} X)
  (G : SheafOfModules.{u} (structureSheaf Rc))

/-- **A morphism `O_U ⟶ G|_U` is its value at the unit section**, as an isomorphism of additive
groups. -/
def unitOverAddEquiv (U : Opens ↥X) :
    ((SheafOfModules.unit (structureSheaf Rc)).over U ⟶ G.over U) ≃+ G.val.obj (op U) :=
  { RingedSite.unitOverHomEquiv (ringedSite Rc) G U with map_add' := fun _ _ => rfl }

/-- **The morphism attached to a section sends the unit section to a restriction of it.** For `b`
a section of `G` over `U`, the morphism `O_U ⟶ G|_U` it names sends the unit section over an
object of the slice over `U` to the restriction of `b` along the structure morphism of that
object. -/
theorem unitOverAddEquiv_symm_app_one (U : Opens ↥X) (b : G.val.obj (op U)) (V : (Over U)ᵒᵖ) :
    ((unitOverAddEquiv Rc G U).symm b).val.app V
        (1 : ((structureSheaf Rc).over U).obj.obj V) =
      G.val.map V.unop.hom.op b :=
  congrFun (congrArg Subtype.val ((G.over U).unitHomEquiv.apply_symm_apply
    ((G.over U).val.sectionsMk (fun V => G.val.map V.unop.hom.op b) (by
      intro V W f
      show G.val.map f.unop.left.op (G.val.map V.unop.hom.op b) = G.val.map W.unop.hom.op b
      rw [← G.val.map_comp_apply]
      congr 1)))) V

/-- At the terminal object of the slice site, the morphism attached to a section takes the unit
section to that section. -/
theorem unitOverAddEquiv_symm_app_one_top (U : Opens ↥X) (b : G.val.obj (op U)) :
    ((unitOverAddEquiv Rc G U).symm b).val.app (op (Over.mk (𝟙 U)))
        (1 : ((structureSheaf Rc).over U).obj.obj (op (Over.mk (𝟙 U)))) = b :=
  (unitOverAddEquiv Rc G U).apply_symm_apply b

/-- **The identification is compatible with restriction.** The morphism attached to the
restriction of a section is the restriction of the morphism attached to it. -/
theorem unitOverAddEquiv_symm_restrict {U V : Opens ↥X} (hVU : V ≤ U) (s : G.val.obj (op U)) :
    (unitOverAddEquiv Rc G V).symm (G.val.map (homOfLE hVU).op s) =
      restrictOverHom (SheafOfModules.unit (structureSheaf Rc)) G hVU
        ((unitOverAddEquiv Rc G U).symm s) := by
  refine (unitOverAddEquiv Rc G V).injective
    (((unitOverAddEquiv Rc G V).apply_symm_apply _).trans ?_)
  refine Eq.trans ?_ (unitOverAddEquiv_symm_app_one Rc G U s
    ((Over.map (homOfLE hVU)).op.obj (op (Over.mk (𝟙 V))))).symm
  exact congrArg (fun f : V ⟶ U => (G.val.map f.op) s) (Subsingleton.elim _ _)

/-- **The identification is compatible with the action of the structure sheaf.** The morphism
attached to a scalar multiple of a section is the morphism attached to the section, followed by
multiplication by that scalar. -/
theorem unitOverAddEquiv_symm_smul (U : Opens ↥X)
    (r : (structureSheaf Rc).obj.obj (op U)) (b : G.val.obj (op U)) :
    (unitOverAddEquiv Rc G U).symm (r • b) =
      (unitOverAddEquiv Rc G U).symm b ≫ overSmul G U r := by
  refine (unitOverAddEquiv Rc G U).injective
    (((unitOverAddEquiv Rc G U).apply_symm_apply _).trans ?_)
  refine ((overSmul_app_top G U r b).symm).trans ?_
  exact congrArg (fun t => (overSmul G U r).val.app (op (Over.mk (𝟙 U))) t)
    (unitOverAddEquiv_symm_app_one_top Rc G U b).symm

/-- **`G` is the internal Hom sheaf out of the structure sheaf**, in the sense of the
characterising structure of Stacks 01CO: its sections over `U` are the morphisms `O_U ⟶ G|_U`,
by evaluation at the unit section, compatibly with restriction and with the action of `O_X`. -/
def unitSheafHom : SheafHom Rc (SheafOfModules.unit (structureSheaf Rc)) G where
  obj := G
  sectionsEquiv U := (unitOverAddEquiv Rc G U).symm
  restrict_natural := by
    intro U V hVU s W hWV x
    exact (congrArg (fun f : (SheafOfModules.unit (structureSheaf Rc)).over V ⟶ G.over V =>
      f.val.app (op (Over.mk (homOfLE hWV))) x)
      (unitOverAddEquiv_symm_restrict Rc G hVU s)).symm
  smul_natural := by
    intro U r s W hWU x
    exact congrArg (fun f : (SheafOfModules.unit (structureSheaf Rc)).over U ⟶ G.over U =>
      f.val.app (op (Over.mk (homOfLE hWU))) x) (unitOverAddEquiv_symm_smul Rc G U r s)

/-- **The internal Hom sheaf out of the structure sheaf is the target:**
`Hom_{O_X}(O_X, G) ≅ G`. -/
def internalHomSheafUnitIso :
    RingedSite.internalHomSheaf (ringedSite Rc) (SheafOfModules.unit (structureSheaf Rc)) G ≅ G :=
  SheafHom.objIso (internalHomSheafHom Rc (SheafOfModules.unit (structureSheaf Rc)) G)
    (unitSheafHom Rc G)

variable {F : SheafOfModules.{u} (structureSheaf Rc)}

/-- **The internal Hom sheaf out of a trivialised sheaf of modules is the target:**
`Hom_{O_X}(F, G) ≅ G` for `F` isomorphic to the structure sheaf. The isomorphism is
precomposition with the trivialisation. -/
def internalHomSheafIsoOfIsoUnit (e : F ≅ SheafOfModules.unit (structureSheaf Rc)) :
    RingedSite.internalHomSheaf (ringedSite Rc) F G ≅ G where
  hom := SheafHom.precomp e.inv (internalHomSheafHom Rc F G) (unitSheafHom Rc G)
  inv := SheafHom.precomp e.hom (unitSheafHom Rc G) (internalHomSheafHom Rc F G)
  hom_inv_id := by
    refine ((SheafHom.precomp_comp e.hom e.inv (internalHomSheafHom Rc F G) (unitSheafHom Rc G)
      (internalHomSheafHom Rc F G)).symm).trans ?_
    exact (congrArg (fun β => SheafHom.precomp β (internalHomSheafHom Rc F G)
      (internalHomSheafHom Rc F G)) e.hom_inv_id).trans
      (SheafHom.precomp_id (internalHomSheafHom Rc F G))
  inv_hom_id := by
    refine ((SheafHom.precomp_comp e.inv e.hom (unitSheafHom Rc G)
      (internalHomSheafHom Rc F G) (unitSheafHom Rc G)).symm).trans ?_
    exact (congrArg (fun β => SheafHom.precomp β (unitSheafHom Rc G) (unitSheafHom Rc G))
      e.inv_hom_id).trans (SheafHom.precomp_id (unitSheafHom Rc G))

end Stacks.SheafOfModules

end
