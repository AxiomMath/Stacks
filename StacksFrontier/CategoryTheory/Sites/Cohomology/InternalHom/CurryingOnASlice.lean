module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.EvaluatingSections
public import StacksFrontier.CategoryTheory.Sites.Cohomology.TensorComplex.MorphismsOnASlice
import StacksCore.Tactic.StacksAttribute

/-! # The curried cochain of a section of an iterated internal Hom complex

Let `(C, O)` be a ringed site and let `K`, `L` and `M` be complexes of `O`-modules. The currying
isomorphism of Stacks 0A90 identifies

`SheafHom(K, SheafHom(L, M))` with `SheafHom(Tot(K ⊗_O L), M)`,

and on sections over an object `U` of the site it is a map from the degree-`n` cochains
`K|_U ⟶ SheafHom(L, M)|_U` to the degree-`n` cochains `Tot(K ⊗_O L)|_U ⟶ M|_U`. This file
constructs that map and characterises it: a degree-`n` section `α` of
`SheafHom(K, SheafHom(L, M))` over `U` goes to the cochain whose value on the restricted pure
tensor of a section `k` of `K^t` and a section `l` of `L^r` is obtained by evaluating `α` on `k`
and then evaluating the result on `l`, with no sign.

Only this direction is built here. The inverse map, the compatibility with the Hom-complex
differential, and the assembly into the isomorphism of complexes of `O`-modules are separate
steps; the differential is where the Koszul signs of the total complex meet those of the
Hom-complex differential.

## Main definitions

* `AlgebraicGeometry.RingedSite.curryRule`: evaluate a section of
  `SheafHom(K, SheafHom(L, M))` on a section of `K` and then on a section of `L`.
* `AlgebraicGeometry.RingedSite.curryTensorMap`: the resulting morphism of presheaves of
  `O|_U`-modules out of the restricted objectwise tensor product `(K^t ⊗ L^r)|_U`.
* `AlgebraicGeometry.RingedSite.curryComponent` and
  `AlgebraicGeometry.RingedSite.curryCochain`: the components of the curried cochain, and the
  cochain itself.

## Main results

* `AlgebraicGeometry.RingedSite.curryRule_add_left`,
  `curryRule_smul_left`, `curryRule_add_right`, `curryRule_smul_right`: the rule is `O`-bilinear.
* `AlgebraicGeometry.RingedSite.curryRule_restrict`: it is compatible with restriction along an
  arrow of the slice site.
* `AlgebraicGeometry.RingedSite.curryCochain_v_section`: the curried cochain takes the restricted
  pure tensor of `k` and `l` to `curryRule`, which pins it down, since by
  `AlgebraicGeometry.RingedSite.tensorComplexOverSection_hom_ext` a morphism out of the
  restricted total tensor complex is determined by its values on those sections.

## Implementation notes

Everything is phrased in the evaluation vocabulary of
`StacksDraft.Ch21.Sec34.HomSectionEvaluation`, because the internal Hom complex is only
available through its characterising data. The outer evaluation is taken at the object `W`
itself rather than along an arrow, so that `applyHomSection_smul_left` applies and the scalar
is not restricted; the inner evaluation is along the arrow `g : W ⟶ U` of the slice site.

`curryRule` is an abbreviation, as `applyHomSection` and `applyHomSectionOver` are: the
bilinearity statements then close by a single rewrite, where a semireducible definition would
leave a residual goal.

`curryRule_restrict` is proved in term mode rather than by chaining rewrites. Restricting a
section is spelled `(H.obj.X n).val.map g.op α`, whose type is a restriction of scalars rather
than the plain module of sections; the two are definitionally equal, so each lemma
elaborates on its own, but a `rw` leaves the goal ill-typed at the `implicit` transparency level
and the next rewrite then fails to find its pattern. Composing the three restriction
lemmas with `Eq.trans` and one `congrArg` avoids that entirely.

The commutative-ring structure on the sections of the restricted structure sheaf is
`AlgebraicGeometry.RingedSite.ringSheafOverSectionsCommRing`, switched on file-locally together
with the monoidal structure on presheaves of modules; `ModuleCat.MonoidalCategory.tensorLift`
and `tensor_ext` are stated over a commutative ring and the restricted objectwise tensor
products are read at that spelling.

## References

* [Stacks Project, Tag 0A90](https://stacks.math.columbia.edu/tag/0A90)
* [Stacks Project, Tag 0A8Z](https://stacks.math.columbia.edu/tag/0A8Z)
* [Stacks Project, Tag 06YM](https://stacks.math.columbia.edu/tag/06YM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite CochainComplex.HomComplex

namespace AlgebraicGeometry.RingedSite

universe u

attribute [local instance] ringSheafSectionsCommRing presheafOfModulesMonoidalCategory
  ringSheafOverSectionsCommRing

variable (X : RingedSite.{u, u, u}) (U : X.C)
  (K L M : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
  (n : ℤ)

/-- Evaluate a degree-`n` section `α` of `SheafHom(K, SheafHom(L, M))` over `U` on a degree-`t`
section `k` of `K` over an object `g : W ⟶ U` of the slice site, and then evaluate the resulting
degree-`t + n` section of `SheafHom(L, M)` over `W` on a degree-`r` section `l` of `L` over `W`.
This is the value of the curried cochain on the pure tensor of `k` and `l`. -/
abbrev curryRule
    (α : ((sheafHomComplex X K (sheafHomComplex X L M).obj).obj.X n).val.obj (op U))
    (t r d : ℤ) (hd : r + (t + n) = d) {W : X.C} (g : W ⟶ U)
    (k : (K.X t).val.obj (op W)) (l : (L.X r).val.obj (op W)) :
    (M.X d).val.obj (op W) :=
  applyHomSection X (sheafHomComplex X L M) W (t + n) r d hd
    (applyHomSectionOver X (sheafHomComplex X K (sheafHomComplex X L M).obj) U W g n t (t + n)
      rfl α k) l

variable {X U K L M n}
variable (α : ((sheafHomComplex X K (sheafHomComplex X L M).obj).obj.X n).val.obj (op U))

section Rule

variable (t r d : ℤ) (hd : r + (t + n) = d)

/-- `curryRule` is additive in the section of `K`. -/
lemma curryRule_add_left {W : X.C} (g : W ⟶ U)
    (k k' : (K.X t).val.obj (op W)) (l : (L.X r).val.obj (op W)) :
    curryRule X U K L M n α t r d hd g (k + k') l =
      curryRule X U K L M n α t r d hd g k l + curryRule X U K L M n α t r d hd g k' l := by
  rw [curryRule, applyHomSectionOver_add_right, applyHomSection_add_left]

/-- `curryRule` is linear in the section of `K`. -/
lemma curryRule_smul_left {W : X.C} (g : W ⟶ U)
    (s : (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op W)) (k : (K.X t).val.obj (op W))
    (l : (L.X r).val.obj (op W)) :
    curryRule X U K L M n α t r d hd g (s • k) l =
      s • curryRule X U K L M n α t r d hd g k l := by
  rw [curryRule, applyHomSectionOver_smul_right, applyHomSection_smul_left]

/-- `curryRule` is additive in the section of `L`. -/
lemma curryRule_add_right {W : X.C} (g : W ⟶ U)
    (k : (K.X t).val.obj (op W)) (l l' : (L.X r).val.obj (op W)) :
    curryRule X U K L M n α t r d hd g k (l + l') =
      curryRule X U K L M n α t r d hd g k l + curryRule X U K L M n α t r d hd g k l' :=
  applyHomSection_add_right X (sheafHomComplex X L M) W (t + n) r d hd _ l l'

/-- `curryRule` is linear in the section of `L`. -/
lemma curryRule_smul_right {W : X.C} (g : W ⟶ U)
    (s : (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op W)) (k : (K.X t).val.obj (op W))
    (l : (L.X r).val.obj (op W)) :
    curryRule X U K L M n α t r d hd g k (s • l) =
      s • curryRule X U K L M n α t r d hd g k l :=
  applyHomSection_smul_right X (sheafHomComplex X L M) W (t + n) r d hd _ s l

/-- `curryRule` is compatible with restriction along an arrow of the slice site over `U`. -/
lemma curryRule_restrict {W W' : X.C} (g : W ⟶ U) (h : W' ⟶ W)
    (k : (K.X t).val.obj (op W)) (l : (L.X r).val.obj (op W)) :
    curryRule X U K L M n α t r d hd (h ≫ g) ((K.X t).val.map h.op k)
        ((L.X r).val.map h.op l) =
      (M.X d).val.map h.op (curryRule X U K L M n α t r d hd g k l) := by
  have hinner :
      applyHomSectionOver X (sheafHomComplex X K (sheafHomComplex X L M).obj) U W' (h ≫ g) n t
          (t + n) rfl α ((K.X t).val.map h.op k) =
        ((sheafHomComplex X L M).obj.X (t + n)).val.map h.op
          (applyHomSectionOver X (sheafHomComplex X K (sheafHomComplex X L M).obj) U W g n t
            (t + n) rfl α k) :=
    (applyHomSectionOver_restrict_comp X (sheafHomComplex X K (sheafHomComplex X L M).obj)
        U W W' g h n t (t + n) rfl α ((K.X t).val.map h.op k)).trans
      ((applyHomSectionOver_map X (sheafHomComplex X K (sheafHomComplex X L M).obj) W W' h n t
            (t + n) rfl
            (((sheafHomComplex X K (sheafHomComplex X L M).obj).obj.X n).val.map g.op α) k).trans
        (congrArg (fun z ↦ ((sheafHomComplex X L M).obj.X (t + n)).val.map h.op z)
          (applyHomSectionOver_restrict X (sheafHomComplex X K (sheafHomComplex X L M).obj) U W g
            n t (t + n) rfl α k).symm))
  refine (congrArg (fun z ↦ applyHomSection X (sheafHomComplex X L M) W' (t + n) r d hd z
    ((L.X r).val.map h.op l)) hinner).trans ?_
  exact (applyHomSectionOver_restrict X (sheafHomComplex X L M) W W' h (t + n) r d hd
      (applyHomSectionOver X (sheafHomComplex X K (sheafHomComplex X L M).obj) U W g n t (t + n)
        rfl α k) ((L.X r).val.map h.op l)).symm.trans
    (applyHomSectionOver_map X (sheafHomComplex X L M) W W' h (t + n) r d hd
      (applyHomSectionOver X (sheafHomComplex X K (sheafHomComplex X L M).obj) U W g n t (t + n)
        rfl α k) l)

variable [HasWeakSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- The morphism of presheaves of `O|_U`-modules out of the restricted objectwise tensor product
`(K^t ⊗ L^r)|_U` determined by `curryRule`. It is the presheaf-level datum from which the
corresponding component of the curried cochain is obtained by
`AlgebraicGeometry.RingedSite.tensorComplexOverMk`. -/
def curryTensorMap :
    overPresheaf X U ((K.X t).val ⊗ (L.X r).val) ⟶ ((M.X d).over U).val where
  app V := ModuleCat.MonoidalCategory.tensorLift
    (fun k l ↦ curryRule X U K L M n α t r d hd V.unop.hom k l)
    (fun k k' l ↦ curryRule_add_left α t r d hd V.unop.hom k k' l)
    (fun s k l ↦ curryRule_smul_left α t r d hd V.unop.hom s k l)
    (fun k l l' ↦ curryRule_add_right α t r d hd V.unop.hom k l l')
    (fun s k l ↦ curryRule_smul_right α t r d hd V.unop.hom s k l)
  naturality {V V'} f := by
    apply ModuleCat.MonoidalCategory.tensor_ext
    intro k l
    have hw : V'.unop.hom = f.unop.left ≫ V.unop.hom := (Over.w f.unop).symm
    change curryRule X U K L M n α t r d hd V'.unop.hom
        ((K.X t).val.map f.unop.left.op k) ((L.X r).val.map f.unop.left.op l) =
      (M.X d).val.map f.unop.left.op (curryRule X U K L M n α t r d hd V.unop.hom k l)
    rw [hw]
    exact curryRule_restrict α t r d hd V.unop.hom f.unop.left k l

omit [HasWeakSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- `curryTensorMap` is `curryRule` on pure tensors of sections. -/
lemma curryTensorMap_tmul (V : (Over U)ᵒᵖ)
    (k : (K.X t).val.obj (op V.unop.left)) (l : (L.X r).val.obj (op V.unop.left)) :
    (curryTensorMap α t r d hd).app V
        (k ⊗ₜ[(Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op V.unop.left)] l) =
      curryRule X U K L M n α t r d hd V.unop.hom k l := rfl

end Rule

section Cochain

variable [HasWeakSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ A, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj A).Additive]
  [∀ (K₁ K₂ : HomologicalComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u,
    u} X.O))
      (ComplexShape.up ℤ)),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)]

/-- The degree-`(c, d)` component of the curried cochain: the morphism of sheaves of
`O|_U`-modules from the degree-`c` term of the restricted total tensor complex to `(M^d)|_U`
whose value on the restricted pure tensor of `k` and `l` is `curryRule`. -/
def curryComponent (c d : ℤ) (hcd : c + n = d) :
    (restrictComplex X (((Stacks.SheafOfModules.Tensor.tensorComplex X.O).obj K).obj L) U).X c ⟶
      (restrictComplex X M U).X d :=
  tensorComplexOverMk (fun t r htr ↦ curryTensorMap α t r d (by omega))

/-- `curryComponent` takes the restricted pure tensor of `k` and `l` to `curryRule`. -/
lemma curryComponent_section (c d : ℤ) (hcd : c + n = d) (t r : ℤ) (htr : t + r = c)
    {W : X.C} (g : W ⟶ U)
    (k : (K.X t).val.obj (op W)) (l : (L.X r).val.obj (op W)) :
    (curryComponent α c d hcd).val.app (op (Over.mk g))
        (tensorComplexOverSection t r c htr g k l) =
      curryRule X U K L M n α t r d (by omega) g k l :=
  (tensorComplexOverMk_section (fun t r htr ↦ curryTensorMap α t r d (by omega))
      t r htr g k l).trans
    (curryTensorMap_tmul α t r d (by omega) (op (Over.mk g)) k l)

/-- The curried cochain of a degree-`n` section `α` of `SheafHom(K, SheafHom(L, M))` over `U`:
the degree-`n` cochain from the restricted total tensor complex `Tot(K ⊗_O L)|_U` to `M|_U`
obtained by evaluating `α` on a section of `K` and then on a section of `L`. -/
def curryCochain :
    Cochain (restrictComplex X (((Stacks.SheafOfModules.Tensor.tensorComplex X.O).obj K).obj L) U)
      (restrictComplex X M U) n :=
  Cochain.mk fun c e hce ↦ curryComponent α c e hce

/-- The curried cochain takes the restricted pure tensor of `k` and `l` to `curryRule`. Together
with `AlgebraicGeometry.RingedSite.tensorComplexOverSection_hom_ext` this pins it down. -/
lemma curryCochain_v_section (c d : ℤ) (hcd : c + n = d) (t r : ℤ) (htr : t + r = c)
    {W : X.C} (g : W ⟶ U)
    (k : (K.X t).val.obj (op W)) (l : (L.X r).val.obj (op W)) :
    ((curryCochain α).v c d hcd).val.app (op (Over.mk g))
        (tensorComplexOverSection t r c htr g k l) =
      curryRule X U K L M n α t r d (by omega) g k l :=
  curryComponent_section α c d hcd t r htr g k l

end Cochain

end AlgebraicGeometry.RingedSite

end
