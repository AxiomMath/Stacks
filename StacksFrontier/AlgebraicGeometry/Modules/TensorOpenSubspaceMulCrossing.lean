module

public import StacksFrontier.AlgebraicGeometry.Modules.TensorOpenSubspaceUnitCrossing
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorPowerRestrictOpenFunctorial

/-!
# The tensor crossing of a restriction, on a morphism out of the tensor product

Let `X` be a ringed space and `U ⊆ X` open. `SheafOfModules.openSubspaceTensorBifunctorIso`
identifies `(M ⊗ L)|_U` with `M|_U ⊗ L|_U`. This file computes where that identification sends
the sheafification unit of a local section, and reads on it the composite

```
(M|_U ⊗ L|_U) --inv--> (M ⊗ L)|_U --(φ|_U)--> N|_U
```

for a morphism `φ` out of the tensor product `M ⊗ L`.

## Main results

* `SheafOfModules.openSubspaceTensorIso_hom_val_app_tensorSheafUnit`: the identification
  `(M ⊗ L)|_U ≅ M|_U ⊗ L|_U` carries the sheafification unit over the image open of `V` to the
  sheafification unit over `V`, on an arbitrary local section of the objectwise tensor product.
* `SheafOfModules.openSubspaceTensorBifunctorIso_inv_val_app_tensorSheafUnit`: the same statement
  for the inverse, in the `PresheafOfModules.tensorSheafBifunctor` spelling.
* `SheafOfModules.openSubspaceTensorBifunctorIso_inv_comp_map_val_app_tensorSheafUnit`: the
  restriction of a morphism out of a tensor product, precomposed with the identification, is the
  morphism read at the image open, on the sheafification unit of a local section.
* `SheafOfModules.tensorSheafMap_openSubspaceComparison_inv_val_app_tensorSheafUnit`: the third
  leg of `SheafOfModules.openSubspaceTensorIso_hom` carries the sheafification unit of the
  `Stacks.Cohomology.HigherDirectImage.moduleRestriction` spelling to the sheafification unit of
  the `SheafOfModules.openSubspaceRestriction` spelling, on an arbitrary local section.
* `SheafOfModules.openSubspaceRestriction_map_val_app`: the restriction of a morphism acts on a
  local section over `V` as the morphism over the image of `V` in `X`.
* `SheafOfModules.tensorSheafUnit_openSubspaceAlg_piece`: the sheafification unit of the tensor
  product of two pieces of the restricted algebra is the unit of the tensor product of the
  restrictions of those pieces.
* `SheafOfModules.eq_tensorSheafDesc_of_unit_eq`: a morphism out of a tensor product sheaf which
  agrees with a morphism `φ` out of the objectwise tensor product on the sheafification unit of
  every pure tensor is `PresheafOfModules.tensorSheafDesc φ`.
* `SheafOfModules.mulSheaf_openSubspaceAlg_eq_tensorSheafDesc`: the multiplication of the
  restricted graded algebra `SheafOfModules.openSubspaceAlg`, read at the restricted pieces
  rather than at its own.

## Implementation notes

The two spellings of the restricted structure sheaf make the `CategoryTheory.Category` instance
of a composition in a statement differ syntactically from the one rewriting produces, so
`simp only [Category.assoc]` does not fire and `rw` is refused as not type-correct at `implicit`
transparency. The file therefore works in term mode, evaluating composites on a local section
with `tripleCompSection` and `compSection`, stated at a variable site.

The crossings are stated with the local section typed on the **large** site, as a section of
`Stacks.SheafOfModules.TensorSheafification.tensorPresheaf X.presheaf M.val L.val` over the image
open of `V`. The small side is spelled `tensorPresheaf (restrictToOpen X U).presheaf …` and never
`PresheafOfModules.tensorObj ((openSubspaceRestriction U).obj M).val …`: the monoidal structure
is visible to instance search only at the
`Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf` spelling of the indexing
presheaf of rings.

## References

* [Stacks Project, Tag 01AD](https://stacks.math.columbia.edu/tag/01AD)
* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA)
* [Stacks Project, Tag 05NA](https://stacks.math.columbia.edu/tag/05NA)
* [Stacks Project, Section 0FMK](https://stacks.math.columbia.edu/tag/0FMK)
-/


@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf AlgebraicGeometry
open TopologicalSpace PresheafOfModules Opposite
open Stacks.Cohomology.HigherDirectImage (moduleRestriction restrictToOpen)
open Stacks.SheafOfModules.TensorPower (restrictTensorSheafIso ringedSpaceIsSheaf)
open scoped TensorProduct

universe u

namespace SheafOfModules

/-! ### Evaluating a composite of morphisms of sheaves of modules on a local section

Stated at a variable site and at generic objects, so that they can be applied by `exact` to
composites whose intermediate objects agree only up to unfolding the structure sheaf of the open
subspace. -/

section Generic

variable {C : Type*} [Category C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}

/-- A triple composite of morphisms of sheaves of modules, evaluated on a local section, given
the three values. -/
private theorem tripleCompSection {A B D E : SheafOfModules.{u} R} {e : A ⟶ E}
    (f : A ⟶ B) (g : B ⟶ D) (h : D ⟶ E) (he : e = f ≫ g ≫ h)
    (V : Cᵒᵖ) {x : A.val.obj V} {b : B.val.obj V} {d : D.val.obj V} {y : E.val.obj V}
    (h1 : f.val.app V x = b) (h2 : g.val.app V b = d) (h3 : h.val.app V d = y) :
    e.val.app V x = y := by
  subst he h1 h2 h3; rfl

/-- A composite of two morphisms of sheaves of modules, evaluated on a local section, given the
two values. -/
private theorem compSection {A B E : SheafOfModules.{u} R} (f : A ⟶ B) (g : B ⟶ E)
    (V : Cᵒᵖ) {x : A.val.obj V} {b : B.val.obj V} {y : E.val.obj V}
    (h1 : f.val.app V x = b) (h2 : g.val.app V b = y) :
    (f ≫ g).val.app V x = y := by
  subst h1 h2; rfl

/-- The inverse of an isomorphism of sheaves of modules on a local section, read off the value of
the isomorphism itself. -/
private theorem invSection {A B : SheafOfModules.{u} R} (e : A ≅ B) (V : Cᵒᵖ)
    {x : A.val.obj V} {y : B.val.obj V} (h : e.hom.val.app V x = y) :
    e.inv.val.app V y = x := by
  subst h
  exact congrArg (fun φ : A ⟶ A => φ.val.app V x) e.hom_inv_id

section TensorDesc

variable [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  {Osharp : Sheaf J CommRingCat.{u}}
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasWeakSheafify J AddCommGrpCat.{u}]
  {F G Q : SheafOfModules.{u} (toRingCat J Osharp)}

/-- **A morphism out of a tensor product sheaf is the descent of a morphism out of the objectwise
tensor product as soon as the two agree on the sheafification unit of a pure tensor.** -/
theorem eq_tensorSheafDesc_of_unit_eq
    {ψ : ((Stacks.SheafOfModules.Tensor.sheafTensor Osharp).obj F).obj G ⟶ Q}
    (φ : tensorObj F.val G.val ⟶ Q.val)
    (h : ∀ (V : Cᵒᵖ) (x : F.val.obj V) (y : G.val.obj V),
      ψ.val.app V ((tensorSheafUnit F G).app V (x ⊗ₜ y)) =
        PresheafOfModules.Hom.app φ V (x ⊗ₜ y)) :
    ψ = PresheafOfModules.tensorSheafDesc φ :=
  PresheafOfModules.tensorSheaf_hom_ext fun V x y =>
    (h V x y).trans (PresheafOfModules.tensorSheafDesc_unit φ V x y).symm

/-- **The descent of a morphism out of the objectwise tensor product, read on the sheafification
unit of an arbitrary local section**: `PresheafOfModules.tensorSheafDesc φ` sends the unit of `z`
to the value of `φ` on `z`. -/
theorem tensorSheafDesc_val_app_tensorSheafUnit (φ : tensorObj F.val G.val ⟶ Q.val) (V : Cᵒᵖ)
    (z : (tensorObj F.val G.val).obj V) :
    (PresheafOfModules.tensorSheafDesc φ).val.app V ((tensorSheafUnit F G).app V z) =
      PresheafOfModules.Hom.app φ V z :=
  (PresheafOfModules.tensorSheafificationHomEquiv_app_apply
      (PresheafOfModules.tensorSheafDesc φ) V z).symm.trans
    (congrArg (fun h : tensorObj F.val G.val ⟶ Q.val => PresheafOfModules.Hom.app h V z)
      ((PresheafOfModules.sheafificationHomEquiv (𝟙 (toRingCat J Osharp).obj)).apply_symm_apply φ))

/-- **The sheafification bijection carries the multiplication of a sheaf of graded algebras back
to the bilinear multiplication it descends from.** -/
theorem GradedAlgebra.sheafificationHomEquiv_mulSheaf
    (A : GradedAlgebra.{u, u} (toRingCat J Osharp)) (i j : ℤ) :
    PresheafOfModules.sheafificationHomEquiv (𝟙 (toRingCat J Osharp).obj)
        (GradedAlgebra.mulSheaf A i j) = GradedAlgebra.mulPresheaf A i j :=
  (PresheafOfModules.sheafificationHomEquiv (𝟙 (toRingCat J Osharp).obj)).apply_symm_apply _

end TensorDesc

/-- Two equal morphisms of sheaves of modules agree on every local section. -/
theorem val_app_congr_fun {P Q : SheafOfModules.{u} R} {f g : P ⟶ Q} (h : f = g) (V : Cᵒᵖ)
    (x : P.val.obj V) : f.val.app V x = g.val.app V x :=
  congrArg (fun φ : P ⟶ Q => φ.val.app V x) h

end Generic

section RingedSpace

variable {X : RingedSpace.{u, u}} (U : Opens X.carrier)

/-- **The restriction of a morphism of sheaves of modules to an open subspace acts on a local
section over `V` as the morphism itself over the image of `V` in `X`.** -/
theorem openSubspaceRestriction_map_val_app
    {M L : SheafOfModules.{u} (structureSheafRing X)} (φ : M ⟶ L) (V : (Opens ↥U)ᵒᵖ)
    (z : ((openSubspaceRestriction U).obj M).val.obj V) :
    ((openSubspaceRestriction U).map φ).val.app V z =
      φ.val.app (op (U.isOpenEmbedding.functor.obj V.unop)) z :=
  rfl

/-- **The third leg of `SheafOfModules.openSubspaceTensorIso_hom` carries the sheafification
unit of the `Stacks.Cohomology.HigherDirectImage.moduleRestriction` spelling to the
sheafification unit of the `SheafOfModules.openSubspaceRestriction` spelling**, on an arbitrary
local section of the objectwise tensor product. -/
theorem tensorSheafMap_openSubspaceComparison_inv_val_app_tensorSheafUnit
    (M L : SheafOfModules.{u} (structureSheafRing X)) (V : (Opens ↥U)ᵒᵖ)
    (z : (tensorObj (O := (restrictToOpen X U).presheaf)
      ((moduleRestriction X U).obj M).val ((moduleRestriction X U).obj L).val).obj V) :
    (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          ⟨(restrictToOpen X U).presheaf, (restrictToOpen X U).IsSheaf⟩).map
        ((openSubspaceRestrictionIsoModuleRestriction U).inv.app M)).app
          ((moduleRestriction X U).obj L) ≫
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          ⟨(restrictToOpen X U).presheaf, (restrictToOpen X U).IsSheaf⟩).obj
          ((openSubspaceRestriction U).obj M)).map
        ((openSubspaceRestrictionIsoModuleRestriction U).inv.app L)).val.app V
        ((tensorSheafUnit
          (Osharp := ⟨(restrictToOpen X U).presheaf, (restrictToOpen X U).IsSheaf⟩)
          ((moduleRestriction X U).obj M) ((moduleRestriction X U).obj L)).app V z) =
      (tensorSheafUnit (Osharp := (restrictToOpen X U).sheaf)
        ((openSubspaceRestriction U).obj M) ((openSubspaceRestriction U).obj L)).app V z  :=
  (val_app_congr_fun (sheafTensorMap_openSubspaceComparison_inv_eq U M L) V _).trans
    ((PresheafOfModules.unit_naturality_apply
        (α := 𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf
          ⟨(restrictToOpen X U).presheaf, (restrictToOpen X U).IsSheaf⟩).obj) _ V z).trans
      (congrArg (fun w => (tensorSheafUnit (Osharp := (restrictToOpen X U).sheaf)
          ((openSubspaceRestriction U).obj M) ((openSubspaceRestriction U).obj L)).app V w)
        (congrArg (fun φ => PresheafOfModules.Hom.app φ V z)
          (tensorHom_openSubspaceComparison_inv_eq_id U M L))))

/-- **`(M ⊗ L)|_U ≅ M|_U ⊗ L|_U` carries the sheafification unit over the image open of `V` to
the sheafification unit over `V`**, on an arbitrary local section of the objectwise tensor
product. -/
theorem openSubspaceTensorIso_hom_val_app_tensorSheafUnit
    (M L : SheafOfModules.{u} (structureSheafRing X)) (V : (Opens ↥U)ᵒᵖ)
    (z : (tensorObj (O := X.presheaf) M.val L.val).obj
      (op (U.isOpenEmbedding.functor.obj V.unop))) :
    (openSubspaceTensorIso U M L).hom.val.app V
        ((tensorSheafUnit M L).app (op (U.isOpenEmbedding.functor.obj V.unop)) z) =
      (tensorSheafUnit (Osharp := (restrictToOpen X U).sheaf)
        ((openSubspaceRestriction U).obj M) ((openSubspaceRestriction U).obj L)).app V z :=
  tripleCompSection _ _ _ (openSubspaceTensorIso_hom U M L) V
    (openSubspaceRestrictionIsoModuleRestriction_hom_app_val_app U
      (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} ⟨X.presheaf, X.IsSheaf⟩).obj
          M).obj L) V
      ((tensorSheafUnit M L).app (op (U.isOpenEmbedding.functor.obj V.unop)) z))
    (Stacks.SheafOfModules.TensorPower.restrictTensorSheafIso_hom_val_app_tensorSheafUnit
      U M L V z)
    (tensorSheafMap_openSubspaceComparison_inv_val_app_tensorSheafUnit U M L V z)

/-- **The inverse identification `M|_U ⊗ L|_U ≅ (M ⊗ L)|_U` carries the sheafification unit over
`V` to the sheafification unit over the image open of `V`**, in the
`PresheafOfModules.tensorSheafBifunctor` spelling. -/
theorem openSubspaceTensorBifunctorIso_inv_val_app_tensorSheafUnit
    (M L : SheafOfModules.{u} (structureSheafRing X)) (V : (Opens ↥U)ᵒᵖ)
    (z : (tensorObj (O := X.presheaf) M.val L.val).obj
      (op (U.isOpenEmbedding.functor.obj V.unop))) :
    (openSubspaceTensorBifunctorIso U M L).inv.val.app V
        ((tensorSheafUnit (Osharp := (restrictToOpen X U).sheaf)
          ((openSubspaceRestriction U).obj M) ((openSubspaceRestriction U).obj L)).app V z) =
      (tensorSheafUnit M L).app (op (U.isOpenEmbedding.functor.obj V.unop)) z :=
  invSection (openSubspaceTensorBifunctorIso U M L) V
    (openSubspaceTensorIso_hom_val_app_tensorSheafUnit U M L V z)

/-- **The restriction to `U` of a morphism out of a tensor product, precomposed with the
identification `M|_U ⊗ L|_U ≅ (M ⊗ L)|_U`, is the morphism itself read at the image open**, on
the sheafification unit of a local section. -/
theorem openSubspaceTensorBifunctorIso_inv_comp_map_val_app_tensorSheafUnit
    (M L N : SheafOfModules.{u} (structureSheafRing X))
    (φ : (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf)).obj (M, L) ⟶ N) (V
        : (Opens ↥U)ᵒᵖ)
    (z : (tensorObj (O := X.presheaf) M.val L.val).obj
      (op (U.isOpenEmbedding.functor.obj V.unop))) :
    ((openSubspaceTensorBifunctorIso U M L).inv ≫ (openSubspaceRestriction U).map φ).val.app V
        ((tensorSheafUnit (Osharp := (restrictToOpen X U).sheaf)
          ((openSubspaceRestriction U).obj M) ((openSubspaceRestriction U).obj L)).app V z) =
      φ.val.app (op (U.isOpenEmbedding.functor.obj V.unop))
        ((tensorSheafUnit M L).app (op (U.isOpenEmbedding.functor.obj V.unop)) z) :=
  compSection _ _ V (openSubspaceTensorBifunctorIso_inv_val_app_tensorSheafUnit U M L V z)
    (openSubspaceRestriction_map_val_app U φ V _)

/-- **The restriction to `U` of a morphism out of a tensor product, precomposed with the
identification, is the morphism it descends from, read at the image open** — on the
sheafification unit of a local section, with the morphism out of the objectwise tensor product
given by `PresheafOfModules.sheafificationHomEquiv` on the right. -/
theorem openSubspaceTensorBifunctorIso_inv_comp_map_val_app_sheafificationHomEquiv
    (M L N : SheafOfModules.{u} (structureSheafRing X))
    (φ : (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf)).obj (M, L) ⟶ N) (V
        : (Opens ↥U)ᵒᵖ)
    (z : (tensorObj (O := X.presheaf) M.val L.val).obj
      (op (U.isOpenEmbedding.functor.obj V.unop))) :
    ((openSubspaceTensorBifunctorIso U M L).inv ≫ (openSubspaceRestriction U).map φ).val.app V
        ((tensorSheafUnit (Osharp := (restrictToOpen X U).sheaf)
          ((openSubspaceRestriction U).obj M) ((openSubspaceRestriction U).obj L)).app V z) =
      PresheafOfModules.Hom.app
        (PresheafOfModules.sheafificationHomEquiv
          (𝟙 (toRingCat (Opens.grothendieckTopology X.carrier) X.sheaf).obj) φ)
        (op (U.isOpenEmbedding.functor.obj V.unop)) z :=
  (openSubspaceTensorBifunctorIso_inv_comp_map_val_app_tensorSheafUnit U M L N φ V z).trans
    (PresheafOfModules.tensorSheafificationHomEquiv_app_apply φ _ z).symm

/-- **The multiplication of the restricted graded algebra, read at the restricted pieces rather
than at its own.** `(SheafOfModules.openSubspaceAlg A U).piece n` and
`(openSubspaceRestriction U).obj (A.piece n)` are definitionally equal
(`SheafOfModules.openSubspaceAlg_piece_openSubspaceRestriction`), and this is the identification
of the multiplication across them, with the multiplication written as the morphism out of the
tensor product sheaf that the objectwise bilinear map descends to. -/
theorem mulSheaf_openSubspaceAlg_eq_tensorSheafDesc
    (A : GradedAlgebra.{u, u} (structureSheafRing X)) (i j : ℤ) :
    GradedAlgebra.mulSheaf (Osharp := (restrictToOpen X U).sheaf) (openSubspaceAlg A U) i j =
      PresheafOfModules.tensorSheafDesc
        (Osharp := (restrictToOpen X U).sheaf)
        (F := (openSubspaceRestriction U).obj (A.piece i))
        (G := (openSubspaceRestriction U).obj (A.piece j))
        (Q := (openSubspaceRestriction U).obj (A.piece (i + j)))
        (GradedAlgebra.mulPresheaf (Osharp := (restrictToOpen X U).sheaf)
          (openSubspaceAlg A U) i j) :=
  rfl

/-- **The sheafification unit of the tensor product of two homogeneous pieces of the restricted
graded algebra is the sheafification unit of the tensor product of the restrictions of those
pieces.** The two spellings `(SheafOfModules.openSubspaceAlg A U).piece n` and
`(openSubspaceRestriction U).obj (A.piece n)` are definitionally equal
(`SheafOfModules.openSubspaceAlg_piece_openSubspaceRestriction`), and this is that identification
carried inside a `PresheafOfModules.tensorSheafUnit`. -/
theorem tensorSheafUnit_openSubspaceAlg_piece
    (A : GradedAlgebra.{u, u} (structureSheafRing X)) (i j : ℤ) :
    tensorSheafUnit (Osharp := (restrictToOpen X U).sheaf)
        ((openSubspaceAlg A U).piece i) ((openSubspaceAlg A U).piece j) =
      tensorSheafUnit (Osharp := (restrictToOpen X U).sheaf)
        ((openSubspaceRestriction U).obj (A.piece i))
        ((openSubspaceRestriction U).obj (A.piece j)) :=
  rfl

end RingedSpace

end SheafOfModules

end
