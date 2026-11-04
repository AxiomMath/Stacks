module

public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.InternalHomSections

/-!
# The internal hom out of the unit

Let `O` be a presheaf of commutative rings on a category `C` and let `G` be a presheaf of
`O`-modules.  The internal hom `𝓗om_O(O, G)` out of the unit object has, over an object `U`, the
morphisms `O|_U ⟶ G|_U` of presheaves of modules on the slice `C/U` as its sections, and such a
morphism is determined by the image of the section `1`: that is Mathlib's
`PresheafOfModules.unitHomEquiv` on the slice, read at the terminal object `U / U`.  So the
sections of `𝓗om_O(O, G)` over `U` are the sections of `G` over `U`, naturally in `U`.

The identification is only an additive bijection, not an isomorphism of presheaves of modules:
the sections of the internal hom live one universe up, being morphisms of presheaves on the
slice, while the sections of `G` live in the module universe.  That is exactly the shape
consumed by `Stacks.Cohomology.Torsors.subsingleton_sheafH_one_of_natAddEquiv`, which compares
the first cohomology of two abelian sheaves whose sections live in different universes.

## Main definitions

* `Stacks.PresheafOfModules.InternalHom.unitSectionsAddEquiv`: the additive bijection between the
  sections of `𝓗om_O(O, G)` over an object and the sections of `G` there.

## Main results

* `Stacks.PresheafOfModules.InternalHom.unitSectionsAddEquiv_apply`: the bijection is evaluation
  of a local morphism at the section `1`.
* `Stacks.PresheafOfModules.InternalHom.unitSectionsAddEquiv_naturality`: it is natural in the
  object.

## Implementation notes

`Stacks.PresheafOfModules.InternalHom.unitInternalHomIso` (in
`StacksFrontier.AlgebraicGeometry.InternalHomCokernel.Unit`) is the same statement as an
isomorphism of presheaves of modules, but it is available only when the module universe is
`max u v`, which is what makes the internal hom land in the universe of its arguments.  Here the
module universe is arbitrary, so no isomorphism of presheaves of modules can be expected and the
statement is made on sections.

Naturality is `Stacks.PresheafOfModules.InternalHom.internalHomEval_naturality` together with
`PresheafOfModules.unit_map_one`; no computation with the relocalization maps of the internal hom
is needed, because the bijection is evaluation at `1` on the nose.

## References

* [Stacks Project, Tag 03EM](https://stacks.math.columbia.edu/tag/03EM)
* [Stacks Project, Tag 04TT](https://stacks.math.columbia.edu/tag/04TT)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe v u t

namespace Stacks.PresheafOfModules.InternalHom

variable {C : Type u} [Category.{v} C] (O : Cᵒᵖ ⥤ CommRingCat)
  (G : PresheafOfModules.{t} (Oforget O))

/-- The sections of the localization `G|_U` over the slice `C/U` are the sections of `G` over
`U`: a compatible family is determined by its value at the terminal object `U / U`, and any
section of `G` over `U` restricts to a compatible family. -/
public def restrSectionsEquiv (U : C) :
    ((restrFun O U).obj G).sections ≃ G.obj (op U) where
  toFun s := s.val (op (Over.mk (𝟙 U)))
  invFun x := PresheafOfModules.sectionsMk (fun V => G.map V.unop.hom.op x) (by
    intro V W i
    change G.map i.unop.left.op (G.map V.unop.hom.op x) = G.map W.unop.hom.op x
    rw [← G.map_comp_apply]
    exact congrArg (fun j : W.unop.left ⟶ U => G.map j.op x) i.unop.w)
  left_inv s := PresheafOfModules.sections_ext _ _ fun V =>
    ((restrFun O U).obj G).sections_property s (Over.homMk V.unop.hom : V.unop ⟶ Over.mk (𝟙 U)).op
  right_inv x := by
    change G.map (𝟙 (op U)) x = x
    rw [G.map_id]
    rfl

/-- **The sections of the internal hom out of the unit are the sections of the target.**  A
morphism `O|_U ⟶ G|_U` of presheaves of modules on the slice `C/U` is determined by the image of
the section `1`, and every section of `G` over `U` arises that way. -/
public def unitSectionsAddEquiv (U : C) :
    (internalHom O (PresheafOfModules.unit (Oforget O)) G).presheaf.obj (op U) ≃+
      G.presheaf.obj (op U) where
  __ := (((restrFun O U).obj G).unitHomEquiv).trans (restrSectionsEquiv O G U)
  map_add' _ _ := rfl

/-- The bijection of `unitSectionsAddEquiv` is evaluation of a local morphism at the section
`1`. -/
public theorem unitSectionsAddEquiv_apply (U : C)
    (α : (internalHom O (PresheafOfModules.unit (Oforget O)) G).presheaf.obj (op U)) :
    unitSectionsAddEquiv O G U α =
      internalHomEval O (PresheafOfModules.unit (Oforget O)) G (op U) α
        (1 : (Oforget O).obj (op U)) := rfl

/-- **The identification of the sections of the internal hom out of the unit with the sections
of the target is natural in the object.** -/
public theorem unitSectionsAddEquiv_naturality {U V : C} (i : V ⟶ U)
    (α : (internalHom O (PresheafOfModules.unit (Oforget O)) G).presheaf.obj (op U)) :
    unitSectionsAddEquiv O G V
        ((internalHom O (PresheafOfModules.unit (Oforget O)) G).presheaf.map i.op α) =
      G.presheaf.map i.op (unitSectionsAddEquiv O G U α) := by
  have h := internalHomEval_naturality O (PresheafOfModules.unit (Oforget O)) G i.op α
    (1 : (Oforget O).obj (op U))
  rwa [PresheafOfModules.unit_map_one] at h

/-- **The naturality of `unitSectionsAddEquiv`, read in the other direction**: a section of `G`
over `U` is turned into a local morphism `O|_U ⟶ G|_U` compatibly with restriction. -/
public theorem unitSectionsAddEquiv_symm_naturality {U V : C} (i : V ⟶ U)
    (x : G.presheaf.obj (op U)) :
    (unitSectionsAddEquiv O G V).symm (G.presheaf.map i.op x) =
      (internalHom O (PresheafOfModules.unit (Oforget O)) G).presheaf.map i.op
        ((unitSectionsAddEquiv O G U).symm x) := by
  refine (unitSectionsAddEquiv O G V).injective ?_
  rw [AddEquiv.apply_symm_apply,
    unitSectionsAddEquiv_naturality O G i ((unitSectionsAddEquiv O G U).symm x),
    AddEquiv.apply_symm_apply]

end Stacks.PresheafOfModules.InternalHom

end
