module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafHom

/-!
# Invertibility from local trivializations

Let `𝒪` be a sheaf of commutative rings on a site `(C, J)` and let `L` be a sheaf of
`𝒪`-modules. This file records that `L` is invertible as soon as it is trivial on each member of
a family covering the final object, where *trivial on `U`* means that the restriction of `L` to
the localized site `C/U` is isomorphic, as a presheaf of `𝒪|_U`-modules, to `𝒪|_U` itself.

This is the unconditional direction of
[Stacks, Tag 0B8M](https://stacks.math.columbia.edu/tag/0B8M) in the shape that the gluing
constructions for one-dimensional Noetherian schemes produce their output: those constructions
do not hand over a `SheafOfModules.LocalGeneratorsData`, they hand over an explicit natural
family of linear equivalences on each patch. The step performed here is purely formal — read a
rank-one dual basis off the trivialization and feed it to
`Stacks.SheafOfModules.isInvertible_of_dualBasisOne`. The basis section is the preimage of the
unit section and the dual coordinate is the trivialization itself.

## Main definitions

* `Stacks.SheafOfModules.Trivialized.Trivialization`: a trivialization of `L` over an object of
  the site.
* `Stacks.SheafOfModules.Trivialized.unitRestr`: the unit section of the structure sheaf, read on
  the localized site.
* `Stacks.SheafOfModules.Trivialized.coord`: the coordinate of a section of `L` in a
  trivialization.
* `Stacks.SheafOfModules.Trivialized.basisAt`: the basis section of a trivialization, namely the
  preimage of the unit section.
* `Stacks.SheafOfModules.Trivialized.dualBasisOneOfIso`: the rank-one dual basis determined by a
  trivialization.

## Main results

* `Stacks.SheafOfModules.Trivialized.coord_smul_basisAt`: the basis section spans, with `coord`
  as the coordinate.
* `Stacks.SheafOfModules.Trivialized.isInvertible_of_coversTop_trivialization`: a sheaf of
  modules trivial on each member of a covering family of the final object is invertible.

## Implementation notes

The trivialization is phrased with `restrFun`, the restriction of a presheaf of modules to the
localized site of Tag 03EM, rather than with Mathlib's `SheafOfModules.over`: `restrFun` is the
spelling in which the sections of the dual sheaf `L^∨` are stated, so no comparison of the two
restrictions is needed.

Every identification between the two spellings of a section holds by `rfl`, but only at default
transparency: `Stacks.SheafOfModules.TensorSheafification.structureSheaf` is a plain `def`, so the
  carrier of
`((restrFun 𝒪 U).obj L.val).obj V` is *not reducibly* `L.val.obj (op V.left)`. Consequently
typeclass synthesis cannot find `One` or `HSMul` across the identification, and `coord`,
`basisAt` and `unitRestr` exist to fix a spelling for each element once: each is a type
ascription, so the equations relating them hold by `rfl`, while every scalar action is written
at a spelling where instance search succeeds.

## References

* [Stacks Project, Tag 0B8M](https://stacks.math.columbia.edu/tag/0B8M)
* [Stacks Project, Tag 03EM](https://stacks.math.columbia.edu/tag/03EM)
-/

@[expose] public section

open CategoryTheory Opposite

universe v u

namespace Stacks.SheafOfModules.Trivialized

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

section Spellings

variable (𝒪 : Cᵒᵖ ⥤ CommRingCat.{max u v})
  (h𝒪 : Presheaf.IsSheaf J (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf 𝒪))

/-- A *trivialization* of a sheaf of modules `L` over an object `U` of the site: an isomorphism
between the restriction of `L` to the localized site `C/U` and the structure sheaf restricted
there. -/
noncomputable abbrev Trivialization
    (L : SheafOfModules.{max u v} (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪))
      (U : C) :=
  ((restrFun 𝒪 U).obj L.val) ≅
    ((restrFun 𝒪 U).obj (SheafOfModules.unit
      (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪)).val)

/-- The unit section of the structure sheaf, read as a section of `𝒪|_U` over an object `V` of
the localized site `C/U`. -/
noncomputable def unitRestr (U : C) (V : (Over U)ᵒᵖ) :
    ((restrFun 𝒪 U).obj (SheafOfModules.unit
      (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪)).val).obj V :=
  (1 : ToType ((Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪).obj.obj (op
    V.unop.left)))

/-- Restriction maps of `𝒪|_U` preserve the unit section. -/
lemma map_unitRestr {U : C} {V W : (Over U)ᵒᵖ} (k : V ⟶ W) :
    (((restrFun 𝒪 U).obj
          (SheafOfModules.unit (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪
            h𝒪)).val).map k).hom
        (unitRestr 𝒪 h𝒪 U V) = unitRestr 𝒪 h𝒪 U W :=
  map_one ((Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪).obj.map ((Over.forget
    U).map k.unop).op).hom

/-- Scaling the unit section of `𝒪|_U` by a section gives back that section. -/
lemma smul_unitRestr {U : C} (V : (Over U)ᵒᵖ) (r : (ORestr 𝒪 U).obj V) :
    r • unitRestr 𝒪 h𝒪 U V =
      (r : ToType ((Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪).obj.obj (op
        V.unop.left))) :=
  mul_one (M := ToType ((Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪).obj.obj (op
    V.unop.left))) r

end Spellings

variable {𝒪 : Cᵒᵖ ⥤ CommRingCat.{max u v}}
  {h𝒪 : Presheaf.IsSheaf J (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf 𝒪)}
  {L : SheafOfModules.{max u v} (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪)}

/-- The coordinate of a section of `L` over an object `V` of the localized site `C/U` in a
trivialization `α`, as a section of the structure sheaf over `V.left`. -/
noncomputable def coord {U : C} (α : Trivialization 𝒪 h𝒪 L U) (V : (Over U)ᵒᵖ)
    (g : L.val.obj (op V.unop.left)) :
    (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪).obj.obj (op V.unop.left) :=
  (α.hom.app V).hom g

/-- The basis section of a trivialization `α` over an object `V` of the localized site `C/U`:
the preimage of the unit section. -/
noncomputable def basisAt {U : C} (α : Trivialization 𝒪 h𝒪 L U) (V : (Over U)ᵒᵖ) :
    L.val.obj (op V.unop.left) :=
  (α.inv.app V).hom (unitRestr 𝒪 h𝒪 U V)

/-- The components of a trivialization are mutually inverse. -/
lemma inv_hom_app_apply {U : C} (α : Trivialization 𝒪 h𝒪 L U) (V : (Over U)ᵒᵖ)
    (x : ((restrFun 𝒪 U).obj L.val).obj V) :
    (α.inv.app V).hom ((α.hom.app V).hom x) = x := by
  have happ : α.hom.app V ≫ α.inv.app V = 𝟙 (((restrFun 𝒪 U).obj L.val).obj V) :=
    congrArg
      (fun φ : ((restrFun 𝒪 U).obj L.val) ⟶ ((restrFun 𝒪 U).obj L.val) =>
        PresheafOfModules.Hom.app φ V) α.hom_inv_id
  simpa using ConcreteCategory.congr_hom happ x

/-- The components of a trivialization are mutually inverse, the other way round. -/
lemma hom_inv_app_apply {U : C} (α : Trivialization 𝒪 h𝒪 L U) (V : (Over U)ᵒᵖ)
    (x : ((restrFun 𝒪 U).obj
        (SheafOfModules.unit (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪
          h𝒪)).val).obj V) :
    (α.hom.app V).hom ((α.inv.app V).hom x) = x := by
  have happ : α.inv.app V ≫ α.hom.app V =
      𝟙 (((restrFun 𝒪 U).obj
        (SheafOfModules.unit (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪
          h𝒪)).val).obj V) :=
    congrArg
      (fun φ : ((restrFun 𝒪 U).obj
            (SheafOfModules.unit (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪
              h𝒪)).val) ⟶
          ((restrFun 𝒪 U).obj
            (SheafOfModules.unit (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪
              h𝒪)).val) =>
        PresheafOfModules.Hom.app φ V) α.inv_hom_id
  simpa using ConcreteCategory.congr_hom happ x

/-- The basis section is compatible with restriction inside the localized site. -/
lemma resSection_basisAt {U : C} (α : Trivialization 𝒪 h𝒪 L U) (V : (Over U)ᵒᵖ) :
    resSection (L := L) V (basisAt α (op (Over.mk (𝟙 U)))) = basisAt α V := by
  have hnat := PresheafOfModules.naturality_apply α.inv
    (Over.homMk V.unop.hom (Category.comp_id _) : V.unop ⟶ Over.mk (𝟙 U)).op
    (unitRestr 𝒪 h𝒪 U (op (Over.mk (𝟙 U))))
  have hone := map_unitRestr 𝒪 h𝒪
    (Over.homMk V.unop.hom (Category.comp_id _) : V.unop ⟶ Over.mk (𝟙 U)).op
  exact hnat.symm.trans (congrArg (fun y => (α.inv.app V).hom y) hone)

/-- **The basis section spans.** Every section of `L` over an object of the localized site is
its own coordinate times the basis section there. -/
lemma coord_smul_basisAt {U : C} (α : Trivialization 𝒪 h𝒪 L U) (V : (Over U)ᵒᵖ)
    (g : L.val.obj (op V.unop.left)) : coord α V g • basisAt α V = g := by
  have hsmul : ∀ r : (ORestr 𝒪 U).obj V,
      (α.inv.app V).hom (r • unitRestr 𝒪 h𝒪 U V) =
        r • (α.inv.app V).hom (unitRestr 𝒪 h𝒪 U V) := fun r => map_smul _ _ _
  have h : coord α V g • basisAt α V = (α.inv.app V).hom (coord α V g) :=
    (hsmul (coord α V g)).symm.trans
      (congrArg (fun y => (α.inv.app V).hom y) (smul_unitRestr 𝒪 h𝒪 V (coord α V g)))
  rw [h]
  exact inv_hom_app_apply α V g

/-- The coordinate of the basis section is the unit section. -/
lemma coord_basisAt {U : C} (α : Trivialization 𝒪 h𝒪 L U) (V : (Over U)ᵒᵖ) :
    coord α V (basisAt α V) =
      (1 : ToType ((Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪).obj.obj (op
        V.unop.left))) :=
  hom_inv_app_apply α V (unitRestr 𝒪 h𝒪 U V)

/-- The rank-one dual basis determined by a trivialization of `L` over `U`: the basis section is
the preimage of the unit section and the dual coordinate is the trivialization itself. -/
noncomputable def dualBasisOneOfIso {U : C} (α : Trivialization 𝒪 h𝒪 L U) :
    DualBasisOne 𝒪 h𝒪 L U where
  e := basisAt α (op (Over.mk (𝟙 U)))
  lam := α.hom
  span V g := by
    rw [resSection_basisAt]
    exact coord_smul_basisAt α V g
  eval_self := coord_basisAt α (op (Over.mk (𝟙 U)))

variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
  [HasWeakSheafify J AddCommGrpCat.{max u v}]

/-- **A sheaf of modules trivial on a covering family of the final object is invertible.**

This is the unconditional direction of Tag 0B8M, with local freeness of rank one presented as a
trivialization on each member of the covering family. -/
theorem isInvertible_of_coversTop_trivialization {I : Type*} {X : I → C} (hX : J.CoversTop X)
    (α : ∀ i, Trivialization 𝒪 h𝒪 L (X i)) : IsInvertible 𝒪 h𝒪 L :=
  isInvertible_of_dualBasisOne 𝒪 h𝒪 hX (fun i => dualBasisOneOfIso (α i))

end Stacks.SheafOfModules.Trivialized

end
