module

public import Mathlib.Algebra.Category.ModuleCat.Products
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafHomPrecomposition

/-!
# The sheaf-hom out of a free sheaf of modules is a product

Let `O_X` be a sheaf of commutative rings on a topological space `X`, let `G` be a sheaf of
`O_X`-modules and let `I` be a type. The internal hom out of the free module on `I`,

`SheafHom_{O_X}(O_X^{(I)}, G) ≅ ∏_{i ∈ I} G`,

is the `I`-indexed product of copies of `G`: an `O_U`-linear map `O_U^{(I)} ⟶ G|_U` is the same
thing as an `I`-indexed family of sections of `G` over `U`, and so is a section of the product
over `U`.

This file proves that identification in the form the characterising structure `SheafHom` of
Stacks 01CO asks for: the product `∏_{i ∈ I} G` is equipped with the section identification, the
restriction naturality and the compatibility with the action of `O_X` which exhibit it as the
internal hom of the free module.

## Main definitions

* `Stacks.SheafOfModules.freeOverHomEquiv`: a map `O_U^{(I)} ⟶ G|_U` is an `I`-indexed family of
  sections of `G` over `U`.
* `Stacks.SheafOfModules.productSectionIso`: the sections of `∏_{i ∈ I} G` over `U` are the
  `I`-indexed families of sections of `G` over `U`.
* `Stacks.SheafOfModules.sheafHomFree`: the product `∏_{i ∈ I} G` as the internal hom of the
  free module on `I`, in the sense of Stacks 01CO.

## Main results

* `Stacks.SheafOfModules.freeOverHomEquiv_apply_generator`: the family attached to a map out of
  the free module is its family of values on the tautological generators.
* `Stacks.SheafOfModules.freeOverHomEquiv_restrict` and
  `Stacks.SheafOfModules.freeOverHomEquiv_symm_smul`: that identification is compatible with
  restriction, and turns multiplication of a family by a scalar into composition with
  `overSmul`.

## Implementation notes

The restriction `G|_U` is `SheafOfModules.over`, whose site is the over-category of `U`; the
component of a map `F|_U ⟶ G|_U` at an open `W ≤ U` is its value at the object
`Over.mk (homOfLE hWU)`, definitionally. Because the morphisms of `Opens X` are
proof-irrelevant, that is also the component of a restricted map, which is what makes the
restriction axiom of `SheafHom` hold with no transport.

The free module on the slice site is identified with the restriction of the free module by
`SheafOfModules.mapFreeIso`, the restriction functor being a left adjoint and so preserving the
coproduct that defines a free module.

## References

* [Stacks Project, Tag 01CO](https://stacks.math.columbia.edu/tag/01CO)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace Stacks.SheafOfModules

variable {X : TopCat.{u}} {Rc : TopCat.Sheaf CommRingCat.{u} X}

section Free

variable (G : SheafOfModules.{u} (structureSheaf Rc)) (I : Type u)

/-- The restriction of the free module on `I` is the free module on `I` over the slice site:
restriction is a left adjoint, so it preserves the coproduct defining a free module. -/
def overFreeIso (U : Opens X) :
    (SheafOfModules.free (R := structureSheaf Rc) I).over U ≅
      SheafOfModules.free (R := (structureSheaf Rc).over U) I := by
  let Q := SheafOfModules.overFunctor (structureSheaf Rc) U
  let : Q.IsLeftAdjoint :=
    (SheafOfModules.overPushforwardOverAdj (R := structureSheaf Rc) U).isLeftAdjoint
  let : PreservesColimitsOfShape (Discrete I) Q :=
    (Adjunction.ofIsLeftAdjoint Q).leftAdjoint_preservesColimits.preservesColimitsOfShape
  exact (SheafOfModules.mapFreeIso Q I (Iso.refl _)).symm

/-- **A map out of a free module is a family of sections.** An `O_U`-linear map
`O_U^{(I)} ⟶ G|_U` is the same thing as an `I`-indexed family of sections of `G` over `U`. -/
def freeOverHomEquiv (U : Opens X) :
    ((SheafOfModules.free (R := structureSheaf Rc) I).over U ⟶ G.over U) ≃
      (I → G.val.obj (op U)) := by
  let e := overFreeIso (Rc := Rc) I U
  let e₁ : ((SheafOfModules.free (R := structureSheaf Rc) I).over U ⟶ G.over U) ≃
      (SheafOfModules.free (R := (structureSheaf Rc).over U) I ⟶ G.over U) :=
    { toFun := fun f => e.inv ≫ f
      invFun := fun f => e.hom ≫ f
      left_inv f := by simp
      right_inv f := by simp }
  exact e₁.trans (((G.over U).freeHomEquiv (I := I)).trans
    (Equiv.piCongrRight fun _ => overSectionsEquiv U))

/-- The family attached to a map out of the free module is its family of values on the
tautological generators. -/
lemma freeOverHomEquiv_apply_generator (U : Opens X)
    (f : (SheafOfModules.free (R := structureSheaf Rc) I).over U ⟶ G.over U) (j : I) :
    freeOverHomEquiv G I U f j =
      f.val.app (op (Over.mk (𝟙 U)))
        (((SheafOfModules.ιFree (R := structureSheaf Rc) j).over U).val.app
          (op (Over.mk (𝟙 U))) (1 : (structureSheaf Rc).obj.obj (op U))) := by
  let W : (Over U)ᵒᵖ := op (Over.mk (𝟙 U))
  let e := overFreeIso (Rc := Rc) I U
  have hι : SheafOfModules.ιFree (R := (structureSheaf Rc).over U) j ≫ e.inv =
      (SheafOfModules.ιFree (R := structureSheaf Rc) j).over U := by
    let Q := SheafOfModules.overFunctor (structureSheaf Rc) U
    let _ : Q.IsLeftAdjoint :=
      (SheafOfModules.overPushforwardOverAdj (R := structureSheaf Rc) U).isLeftAdjoint
    let _ : PreservesColimitsOfShape (Discrete I) Q :=
      (Adjunction.ofIsLeftAdjoint Q).leftAdjoint_preservesColimits.preservesColimitsOfShape
    exact SheafOfModules.ιFree_mapFreeIso_hom Q I (Iso.refl _) j
  change ((G.over U).unitHomEquiv
    (SheafOfModules.ιFree (R := (structureSheaf Rc).over U) j ≫ e.inv ≫ f)).val W = _
  rw [SheafOfModules.unitHomEquiv_apply_coe]
  change f.val.app W ((SheafOfModules.ιFree (R := (structureSheaf Rc).over U) j ≫ e.inv).val.app W
    (1 : (structureSheaf Rc).obj.obj (op U))) = _
  rw [hι]
  rfl

/-- The identification of maps out of the free module with families of sections is additive. -/
lemma freeOverHomEquiv_add (U : Opens X)
    (f g : (SheafOfModules.free (R := structureSheaf Rc) I).over U ⟶ G.over U) (j : I) :
    freeOverHomEquiv G I U (f + g) j =
      freeOverHomEquiv G I U f j + freeOverHomEquiv G I U g j := by
  simp only [freeOverHomEquiv_apply_generator, SheafOfModules.add_val,
    PresheafOfModules.add_app, ModuleCat.hom_add, LinearMap.add_apply]
  rfl

/-- Restricting a map out of the free module restricts the family of sections attached to it. -/
lemma freeOverHomEquiv_restrict {U V : Opens X} (hVU : V ≤ U)
    (f : (SheafOfModules.free (R := structureSheaf Rc) I).over U ⟶ G.over U) (j : I) :
    freeOverHomEquiv G I V (restrictOverHom (SheafOfModules.free I) G hVU f) j =
      G.val.map (homOfLE hVU).op (freeOverHomEquiv G I U f j) := by
  let b := SheafOfModules.ιFree (R := structureSheaf Rc) j
  let m : op (Over.mk (𝟙 U)) ⟶ op (Over.mk (homOfLE hVU)) :=
    (Over.homMk (homOfLE hVU) (by simp)).op
  have hb := PresheafOfModules.naturality_apply b.val (homOfLE hVU).op
    (1 : (structureSheaf Rc).obj.obj (op U))
  have hf := PresheafOfModules.naturality_apply f.val m
    (b.val.app (op U) (1 : (structureSheaf Rc).obj.obj (op U)))
  rw [freeOverHomEquiv_apply_generator, freeOverHomEquiv_apply_generator]
  have hone : (SheafOfModules.unit (structureSheaf Rc)).val.map (homOfLE hVU).op
      (1 : (structureSheaf Rc).obj.obj (op U)) =
      (1 : (structureSheaf Rc).obj.obj (op V)) :=
    PresheafOfModules.unit_map_one (R := (structureSheaf Rc).obj) (homOfLE hVU).op
  rw [hone] at hb
  change f.val.app (op (Over.mk (homOfLE hVU)))
      (b.val.app (op V) (1 : (structureSheaf Rc).obj.obj (op V))) =
    G.val.map (homOfLE hVU).op (f.val.app (op (Over.mk (𝟙 U)))
      (b.val.app (op U) (1 : (structureSheaf Rc).obj.obj (op U))))
  change f.val.app (op (Over.mk (homOfLE hVU)))
      ((SheafOfModules.free (R := structureSheaf Rc) I).val.map (homOfLE hVU).op
        (b.val.app (op U) (1 : (structureSheaf Rc).obj.obj (op U)))) =
    G.val.map (homOfLE hVU).op (f.val.app (op (Over.mk (𝟙 U)))
      (b.val.app (op U) (1 : (structureSheaf Rc).obj.obj (op U)))) at hf
  exact (congrArg (fun z : ((SheafOfModules.free (R := structureSheaf Rc) I).over U).val.obj
    (op (Over.mk (homOfLE hVU))) => f.val.app (op (Over.mk (homOfLE hVU))) z) hb).trans hf

/-- The map out of the free module attached to a restricted family is the restriction of the map
attached to the family. -/
lemma restrictOverHom_free_symm {U V : Opens X} (hVU : V ≤ U) (a : I → G.val.obj (op U)) :
    restrictOverHom (SheafOfModules.free I) G hVU ((freeOverHomEquiv G I U).symm a) =
      (freeOverHomEquiv G I V).symm (fun j => G.val.map (homOfLE hVU).op (a j)) := by
  apply (freeOverHomEquiv G I V).injective
  funext j
  rw [freeOverHomEquiv_restrict, Equiv.apply_symm_apply]
  exact (congrFun ((freeOverHomEquiv G I V).apply_symm_apply
    (fun k => G.val.map (homOfLE hVU).op (a k))) j).symm

/-- Composing a map out of the free module with multiplication by a scalar multiplies the
attached family of sections by that scalar. -/
lemma freeOverHomEquiv_comp_overSmul (U : Opens X) (r : (structureSheaf Rc).obj.obj (op U))
    (f : (SheafOfModules.free (R := structureSheaf Rc) I).over U ⟶ G.over U) (j : I) :
    freeOverHomEquiv G I U (f ≫ overSmul G U r) j = r • freeOverHomEquiv G I U f j := by
  rw [freeOverHomEquiv_apply_generator, freeOverHomEquiv_apply_generator]
  exact overSmul_app_top G U r _

/-- Multiplying a family of sections by a scalar composes the attached map out of the free module
with multiplication by that scalar. -/
lemma freeOverHomEquiv_symm_smul (U : Opens X) (r : (structureSheaf Rc).obj.obj (op U))
    (a : I → G.val.obj (op U)) :
    (freeOverHomEquiv G I U).symm (fun j => r • a j) =
      (freeOverHomEquiv G I U).symm a ≫ overSmul G U r := by
  apply (freeOverHomEquiv G I U).injective
  funext j
  simp only [freeOverHomEquiv_comp_overSmul, Equiv.apply_symm_apply]

end Free

section Product

variable (G : SheafOfModules.{u} (structureSheaf Rc)) (I : Type u)

/-- **Sections of a product are families of sections.** The sections over `U` of an `I`-indexed
product of copies of `G` are the `I`-indexed families of sections of `G` over `U`, because
evaluation at `U` preserves products. -/
def productSectionIso (U : Opens X) :
    ((∏ᶜ fun _ : I => G).val.obj (op U)) ≅
      ModuleCat.of ((structureSheaf Rc).obj.obj (op U)) (I → G.val.obj (op U)) :=
  PreservesProduct.iso (SheafOfModules.evaluation (structureSheaf Rc) (op U)) (fun _ : I => G) ≪≫
    ModuleCat.piIsoPi (fun _ : I =>
      (SheafOfModules.evaluation (structureSheaf Rc) (op U)).obj G)

/-- The family attached to a section of the product is its family of components. -/
lemma productSectionIso_hom_apply (U : Opens X) (s : (∏ᶜ fun _ : I => G).val.obj (op U)) (j : I) :
    (productSectionIso G I U).hom s j = (Pi.π (fun _ : I => G) j).val.app (op U) s := by
  let E := SheafOfModules.evaluation (structureSheaf Rc) (op U)
  have h : ((PreservesProduct.iso E (fun _ : I => G)).hom ≫
      (ModuleCat.piIsoPi (fun _ : I => E.obj G)).hom) ≫
      ModuleCat.ofHom (LinearMap.proj j) = E.map (Pi.π (fun _ : I => G) j) := by
    rw [Category.assoc, ModuleCat.piIsoPi_hom_ker_subtype]
    exact piComparison_comp_π E (fun _ : I => G) j
  exact congrArg (fun f : E.obj (∏ᶜ fun _ : I => G) ⟶ E.obj G => f s) h

/-- The identification of sections of the product with families of sections is compatible with
the restriction maps. -/
lemma productSectionIso_hom_restrict {U V : Opens X} (hVU : V ≤ U)
    (s : (∏ᶜ fun _ : I => G).val.obj (op U)) (j : I) :
    (productSectionIso G I V).hom ((∏ᶜ fun _ : I => G).val.map (homOfLE hVU).op s) j =
      G.val.map (homOfLE hVU).op ((productSectionIso G I U).hom s j) :=
  (productSectionIso_hom_apply G I V _ j).trans
    ((PresheafOfModules.naturality_apply (Pi.π (fun _ : I => G) j).val (homOfLE hVU).op s).trans
      (congrArg (G.val.map (homOfLE hVU).op) (productSectionIso_hom_apply G I U s j).symm))

/-- The identification of sections of the product with families of sections is linear. -/
lemma productSectionIso_hom_smul (U : Opens X) (r : (structureSheaf Rc).obj.obj (op U))
    (s : (∏ᶜ fun _ : I => G).val.obj (op U)) (j : I) :
    (productSectionIso G I U).hom (r • s) j = r • (productSectionIso G I U).hom s j :=
  congrFun ((productSectionIso G I U).hom.hom.map_smul r s) j

end Product

section SheafHomFree

variable (G : SheafOfModules.{u} (structureSheaf Rc)) (I : Type u)

/-- The identification of maps out of the free module with families of sections, as an additive
equivalence. -/
def freeOverHomAddEquiv (U : Opens X) :
    ((SheafOfModules.free (R := structureSheaf Rc) I).over U ⟶ G.over U) ≃+
      (I → G.val.obj (op U)) :=
  { freeOverHomEquiv G I U with
    map_add' := fun f g => funext fun j => freeOverHomEquiv_add G I U f g j }

/-- The identification of sections of the product with families of sections, as an additive
equivalence. -/
def productSectionAddEquiv (U : Opens X) :
    ((∏ᶜ fun _ : I => G).val.obj (op U)) ≃+ (I → G.val.obj (op U)) :=
  (productSectionIso G I U).toLinearEquiv.toAddEquiv

variable (Rc)

/-- **The internal hom out of a free module is a product.** The `I`-indexed product of copies of
`G`, together with the identification of its sections over `U` with the `O_U`-linear maps
`O_U^{(I)} ⟶ G|_U`, is the internal hom `SheafHom_{O_X}(O_X^{(I)}, G)` in the sense of
Stacks 01CO. -/
def sheafHomFree : SheafHom Rc (SheafOfModules.free I) G where
  obj := ∏ᶜ fun _ : I => G
  sectionsEquiv U := (productSectionAddEquiv G I U).trans (freeOverHomAddEquiv G I U).symm
  restrict_natural {U V} hVU s {W} hWV x := by
    have h := restrictOverHom_free_symm G I hVU ((productSectionIso G I U).hom s)
    have hr := restrictOverHom_app (SheafOfModules.free I) G hVU
      ((freeOverHomEquiv G I U).symm ((productSectionIso G I U).hom s))
      (op (Over.mk (homOfLE hWV))) x
    have ha : (fun j => G.val.map (homOfLE hVU).op ((productSectionIso G I U).hom s j)) =
        (productSectionIso G I V).hom ((∏ᶜ fun _ : I => G).val.map (homOfLE hVU).op s) :=
      funext fun j => (productSectionIso_hom_restrict G I hVU s j).symm
    rw [ha] at h
    exact hr.symm.trans (congrArg
      (fun f : (SheafOfModules.free (R := structureSheaf Rc) I).over V ⟶ G.over V =>
        f.val.app (op (Over.mk (homOfLE hWV))) x) h)
  smul_natural U r s {W} hWU x := by
    have ht : (productSectionIso G I U).hom (r • s) =
        fun j => r • (productSectionIso G I U).hom s j :=
      funext (productSectionIso_hom_smul G I U r s)
    change ((freeOverHomEquiv G I U).symm ((productSectionIso G I U).hom (r • s))).val.app
      (op (Over.mk (homOfLE hWU))) x = _
    rw [ht, freeOverHomEquiv_symm_smul]
    exact overSmul_app G U r (op (Over.mk (homOfLE hWU))) _

end SheafHomFree

end Stacks.SheafOfModules

end
