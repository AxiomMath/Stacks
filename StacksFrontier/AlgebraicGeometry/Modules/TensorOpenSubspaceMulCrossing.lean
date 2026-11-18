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
with the helper lemmas `tripleCompImageSection`, `invImageSection` and `compMapImageSection`,
applied by term.

**Reading a section across the restriction.** The tensor product sheafifies with the sealed
`Stacks.SheafOfModules.Tensor.sheafification`, so a section of a tensor product sheaf over `X`
does not unfold, and reading it as a section of its restriction to `U` makes the unifier compare
the stuck module with the restricted one (`Module.compHom`) field by field. Done naively, the
statements of the first two crossings below exceed the default `maxHeartbeats` on their own, and
the third does with its proof. Two devices bring each of them to about 60% of the budget, kernel
check included.

* The helper lemmas take a section over the image open as a section of the *unrestricted*
  module and are stated for an arbitrary sheaf of modules `N`, where reading it across the
  restriction is cheap; instantiating them at a tensor product sheaf does not repeat that
  reading.
* In the statements, a section over the image open is ascribed the type of the sections over
  `openSubspaceSiteImage U V`, the same open as the slice site spells it. Elaboration erases the
  ascription, so the statement is the one written without it, but the unifier then crosses the
  two spellings of the open before it crosses the restriction, which costs roughly half as much.
  `openSubspaceTensorBifunctorIso_inv_val_app_tensorSheafUnit` applies `Eq` rather than writing
  `=`, so that its right-hand side is elaborated against the type of its left-hand side;
  unifying the two types afterwards, as `=` does, costs about 80,000 heartbeats more.

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
open Stacks.SheafOfModules (openSubspaceSiteFunctor)
open Stacks.SheafOfModules.PushforwardSheafification (pushforwardRingSheaf)
open scoped TensorProduct

universe u

namespace SheafOfModules

/-! ### Morphisms of sheaves of modules on a local section -/

section Generic

variable {C : Type*} [Category C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}

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
      (((Stacks.SheafOfModules.Tensor.sheafificationAdjunction Osharp).homEquiv
        (tensorObj F.val G.val) Q).apply_symm_apply φ))

/-- **The sheafification bijection carries the multiplication of a sheaf of graded algebras back
to the bilinear multiplication it descends from.** -/
theorem GradedAlgebra.sheafificationHomEquiv_mulSheaf
    (A : GradedAlgebra.{u, u} (toRingCat J Osharp)) (i j : ℤ) :
    (Stacks.SheafOfModules.Tensor.sheafificationAdjunction Osharp).homEquiv
        (tensorObj (A.piece i).val (A.piece j).val) (A.piece (i + j))
        (GradedAlgebra.mulSheaf A i j) = GradedAlgebra.mulPresheaf A i j :=
  ((Stacks.SheafOfModules.Tensor.sheafificationAdjunction Osharp).homEquiv _ _).apply_symm_apply _

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
    ((Stacks.SheafOfModules.Tensor.unit_naturality_apply
        (R := ⟨(restrictToOpen X U).presheaf, (restrictToOpen X U).IsSheaf⟩) _ V z).trans
      (congrArg (fun w => (tensorSheafUnit (Osharp := (restrictToOpen X U).sheaf)
          ((openSubspaceRestriction U).obj M) ((openSubspaceRestriction U).obj L)).app V w)
        (congrArg (fun φ => PresheafOfModules.Hom.app φ V z)
          (tensorHom_openSubspaceComparison_inv_eq_id U M L))))

/-! ### Reading a section over the image open as a section of the restriction

A section of `N` over the image in `X` of an open `V` of `U` is, definitionally, a section of
`(openSubspaceRestriction U).obj N` over `V`. The lemmas below take it in the first form and are
stated for an arbitrary `N`; see the implementation notes. -/

/-- The image in `X` of an open `V` of `U`, spelled as the slice site of `U` spells it:
definitionally `op (U.isOpenEmbedding.functor.obj V.unop)`. The crossings below ascribe sections
to it, so that the unifier crosses the two spellings of the open before the restriction. -/
abbrev openSubspaceSiteImage (V : (Opens ↥U)ᵒᵖ) : (Opens X.carrier)ᵒᵖ :=
  op ((openSubspaceSiteFunctor U).obj V.unop).left

/-- The comparison `openSubspaceRestriction U ≅ moduleRestriction X U` is the identity on a
section over the image open, taken as a section of the unrestricted module. -/
private theorem openSubspaceRestrictionIsoModuleRestriction_hom_app_val_app_image
    (N : SheafOfModules.{u} (structureSheafRing X)) (V : (Opens ↥U)ᵒᵖ)
    (x : N.val.obj (op (U.isOpenEmbedding.functor.obj V.unop))) :
    ((openSubspaceRestrictionIsoModuleRestriction U).hom.app N).val.app V x = x :=
  rfl

/-- A triple composite out of the restriction of `N`, evaluated on a section of `N` over the image
open of `V`, given the three values. -/
private theorem tripleCompImageSection {N : SheafOfModules.{u} (structureSheafRing X)}
    {B D E : SheafOfModules.{u} (pushforwardRingSheaf (Opens.grothendieckTopology ↥U)
      (openSubspaceSiteFunctor U) ((structureSheafRing X).over U))}
    {e : (openSubspaceRestriction U).obj N ⟶ E} (f : (openSubspaceRestriction U).obj N ⟶ B)
    (g : B ⟶ D) (h : D ⟶ E) (he : e = f ≫ g ≫ h) (V : (Opens ↥U)ᵒᵖ)
    {x : N.val.obj (op (U.isOpenEmbedding.functor.obj V.unop))} {b : B.val.obj V}
    {d : D.val.obj V} {y : E.val.obj V}
    (h1 : f.val.app V x = b) (h2 : g.val.app V b = d) (h3 : h.val.app V d = y) :
    e.val.app V x = y := by
  subst he h1 h2 h3; rfl

/-- The inverse of an isomorphism out of the restriction of `N`, read off the value of the
isomorphism itself on a section of `N` over the image open of `V`. -/
private theorem invImageSection {N : SheafOfModules.{u} (structureSheafRing X)}
    {E : SheafOfModules.{u} (pushforwardRingSheaf (Opens.grothendieckTopology ↥U)
      (openSubspaceSiteFunctor U) ((structureSheafRing X).over U))}
    (e : (openSubspaceRestriction U).obj N ≅ E) (V : (Opens ↥U)ᵒᵖ)
    {x : N.val.obj (op (U.isOpenEmbedding.functor.obj V.unop))} {y : E.val.obj V}
    (h : e.hom.val.app V x = y) : e.inv.val.app V y = x := by
  subst h
  exact congrArg (fun φ : (openSubspaceRestriction U).obj N ⟶ _ => φ.val.app V x) e.hom_inv_id

/-- A composite ending in the restriction of a morphism `φ : N ⟶ P`, evaluated on a local
section, given the value of the first factor as a section of `N` over the image open of `V`. -/
private theorem compMapImageSection
    {A : SheafOfModules.{u} (pushforwardRingSheaf (Opens.grothendieckTopology ↥U)
      (openSubspaceSiteFunctor U) ((structureSheafRing X).over U))}
    {N P : SheafOfModules.{u} (structureSheafRing X)}
    (f : A ⟶ (openSubspaceRestriction U).obj N) (φ : N ⟶ P) (V : (Opens ↥U)ᵒᵖ)
    {s : A.val.obj V} {x : N.val.obj (op (U.isOpenEmbedding.functor.obj V.unop))}
    (h : f.val.app V s = x) :
    (f ≫ (openSubspaceRestriction U).map φ).val.app V s =
      φ.val.app (op (U.isOpenEmbedding.functor.obj V.unop)) x := by
  subst h; rfl

/-- **`(M ⊗ L)|_U ≅ M|_U ⊗ L|_U` carries the sheafification unit over the image open of `V` to
the sheafification unit over `V`**, on an arbitrary local section of the objectwise tensor
product. -/
theorem openSubspaceTensorIso_hom_val_app_tensorSheafUnit
    (M L : SheafOfModules.{u} (structureSheafRing X)) (V : (Opens ↥U)ᵒᵖ)
    (z : (tensorObj (O := X.presheaf) M.val L.val).obj
      (op (U.isOpenEmbedding.functor.obj V.unop))) :
    (openSubspaceTensorIso U M L).hom.val.app V
        ((tensorSheafUnit M L).app (op (U.isOpenEmbedding.functor.obj V.unop)) z :
          (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} ⟨X.presheaf, X.IsSheaf⟩).obj
            M).obj L).val.obj (openSubspaceSiteImage U V)) =
      (tensorSheafUnit (Osharp := (restrictToOpen X U).sheaf)
        ((openSubspaceRestriction U).obj M) ((openSubspaceRestriction U).obj L)).app V
        (z : (tensorObj (O := X.presheaf) M.val L.val).obj (openSubspaceSiteImage U V)) :=
  tripleCompImageSection U _ _ _ (openSubspaceTensorIso_hom U M L) V
    (openSubspaceRestrictionIsoModuleRestriction_hom_app_val_app_image U _ V _)
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
    Eq
      ((openSubspaceTensorBifunctorIso U M L).inv.val.app V
        ((tensorSheafUnit (Osharp := (restrictToOpen X U).sheaf)
          ((openSubspaceRestriction U).obj M) ((openSubspaceRestriction U).obj L)).app V
          (z : (tensorObj (O := X.presheaf) M.val L.val).obj (openSubspaceSiteImage U V))))
      ((tensorSheafUnit M L).app (op (U.isOpenEmbedding.functor.obj V.unop)) z :
        (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} ⟨X.presheaf, X.IsSheaf⟩).obj
          M).obj L).val.obj (openSubspaceSiteImage U V)) :=
  invImageSection U (openSubspaceTensorBifunctorIso U M L) V
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
          ((openSubspaceRestriction U).obj M) ((openSubspaceRestriction U).obj L)).app V
          (z : (tensorObj (O := X.presheaf) M.val L.val).obj (openSubspaceSiteImage U V))) =
      φ.val.app (op (U.isOpenEmbedding.functor.obj V.unop))
        ((tensorSheafUnit M L).app (op (U.isOpenEmbedding.functor.obj V.unop)) z) :=
  compMapImageSection U _ φ V (openSubspaceTensorBifunctorIso_inv_val_app_tensorSheafUnit U M L V z)

/-- **The restriction to `U` of a morphism out of a tensor product, precomposed with the
identification, is the morphism it descends from, read at the image open** — on the
sheafification unit of a local section, with the morphism out of the objectwise tensor product
given by the bijection of `Stacks.SheafOfModules.Tensor.sheafificationAdjunction` on the
right. -/
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
        ((Stacks.SheafOfModules.Tensor.sheafificationAdjunction X.sheaf).homEquiv
          (tensorObj M.val L.val) N φ)
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
