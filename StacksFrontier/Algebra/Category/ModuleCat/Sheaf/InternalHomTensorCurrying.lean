module

public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.InternalHomSectionwiseCurrying
public import StacksFrontier.CategoryTheory.Sites.Modules.InternalHomAndFlatness.InternalHomFirstVariable
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorLocallyFree
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.BifunctorReductionMachinery
public import StacksFrontier.CategoryTheory.Sites.Modules.InternalHomAndFlatness.SheafTensorHom

/-!
# Internal Hom out of a tensor product of sheaves of modules

Let `O` be a sheaf of commutative rings on a site `(C, J)` and let `F`, `G`, `H` be sheaves of
`O`-modules. This file proves the sheaf half of Stacks 03EO in its isomorphism form:

`Hom_O(F ⊗_O G, H) ≅ Hom_O(F, Hom_O(G, H))`,

an isomorphism of sheaves of `O`-modules, natural contravariantly in each tensor factor and
covariantly in the target.

The tensor product of sheaves of modules is the sheafification of the sectionwise tensor
product of the underlying presheaves, so the morphism is built in two steps. Precomposition
with the sheafification unit `F ⊗ G ⟶ (F ⊗_O G)ᵛ` identifies internal Hom out of the tensor
sheaf with internal Hom out of the sectionwise tensor product, and the currying isomorphism of
the presheaf half of the same tag finishes. The step specific to sheaves is the first one, and
it is an isomorphism because the unit is locally bijective and the target is a sheaf: sections
of an internal Hom sheaf over `U` are morphisms of `O|_U`-modules, and on the slice site a
locally bijective morphism induces a bijection on morphisms into a sheaf.

## Main definitions

* `Stacks.SheafOfModules.InternalHom.sheafTensorUnit`: the sheafification unit at the
  sectionwise tensor product, with its naturality in each factor.
* `Stacks.SheafOfModules.InternalHom.sheafTensorMap`: the induced morphism of tensor sheaves.
* `Stacks.SheafOfModules.InternalHom.internalHomTensorSheafifyIso`: internal Hom out of the
  tensor sheaf is internal Hom out of the sectionwise tensor product.
* `Stacks.SheafOfModules.InternalHom.sheafCurryIso`: the currying isomorphism.

## Main results

* `Stacks.SheafOfModules.InternalHom.internalHomMapLeft_sheafTensorUnit_bijective`: the
  sheafification step is bijective on sections, which is what makes it an isomorphism.
* `Stacks.SheafOfModules.InternalHom.sheafCurryIso_hom_app_tmul`: the isomorphism is tensor
  currying on every local pure tensor, which pins it down.
* `Stacks.SheafOfModules.InternalHom.sheafCurryIso_natural_left`,
  `..._natural_middle`, `..._natural_right`: naturality in all three variables.

## Implementation notes

A sheaf of `O`-modules carries its module structure for the presheaf of rings
`(underlyingRingSheaf J O).obj`, whereas `internalHom` and the presheaf currying isomorphism
are stated for `Oforget O.obj`. The two are definitionally equal, but the check is expensive
and is not available at `implicit` transparency at all, so neither `rw` nor `simp only` will
fire on a goal that mixes the spellings. Each naturality statement is therefore reduced to the
presheaf-level lemma of
`StacksFrontier.Algebra.Category.ModuleCat.Presheaf.InternalHomSectionwiseCurrying` by rewriting
with
`sheafCurryIso_hom_val`, `sheafInternalHomMapLeft_val` and `sheafInternalHomMapRight_val`,
which pay for the identification once each, in a statement small enough for the kernel. A
single `exact` of the presheaf lemma against the sheaf-level goal exhausts the kernel's budget
instead; that is the whole reason this file is split from
`StacksFrontier/Algebra/Category/ModuleCat/Presheaf/InternalHomSectionwiseCurrying.lean`, where `ε`
is arbitrary and the ring presheaf has one spelling.

## References

* [Stacks Project, Tag 03EO](https://stacks.math.columbia.edu/tag/03EO)
* [Stacks Project, Tag 03EM](https://stacks.math.columbia.edu/tag/03EM), the internal Hom
  presheaf of a sheaf target is a sheaf.
* [Stacks Project, Tag 05NB](https://stacks.math.columbia.edu/tag/05NB), the tensor product of
  sheaves of modules.
-/

@[expose] public section

open CategoryTheory MonoidalCategory Opposite
open Stacks.PresheafOfModules.InternalHom

namespace Stacks.SheafOfModules.InternalHom

universe v u

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable (O : Sheaf J CommRingCat.{max u v})
variable (F G H :
    _root_.SheafOfModules.{max u v} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := J)) O))

/-- The sheafification unit at the sectionwise tensor product. -/
noncomputable def sheafTensorUnit : (F.val ⊗ G.val) ⟶
    (((Stacks.SheafOfModules.Tensor.sheafTensor O).obj F).obj G).val :=
  Stacks.SheafOfModules.TensorLocalProperties.sheafificationUnit
    (R := (Stacks.SheafOfModules.Tensor.ringSheaf (J := J)) O) (F.val ⊗ G.val)

/-- The sheafification unit at the sectionwise tensor product is locally injective. -/
instance sheafTensorUnit_isLocallyInjective :
    _root_.PresheafOfModules.IsLocallyInjective J (sheafTensorUnit O F G) :=
  inferInstanceAs (Presheaf.IsLocallyInjective J
    (CategoryTheory.toSheafify J (F.val ⊗ G.val).presheaf))

/-- The sheafification unit at the sectionwise tensor product is locally surjective. -/
instance sheafTensorUnit_isLocallySurjective :
    _root_.PresheafOfModules.IsLocallySurjective J (sheafTensorUnit O F G) :=
  inferInstanceAs (Presheaf.IsLocallySurjective J
    (CategoryTheory.toSheafify J (F.val ⊗ G.val).presheaf))

/-- The sheafification unit of presheaves of modules is natural. -/
theorem sheafificationUnit_naturality
    {P Q :
      _root_.PresheafOfModules.{max u v} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := J)) O).obj}
    (φ : P ⟶ Q) :
    φ ≫ Stacks.SheafOfModules.TensorLocalProperties.sheafificationUnit
        (R := (Stacks.SheafOfModules.Tensor.ringSheaf (J := J)) O) Q =
      Stacks.SheafOfModules.TensorLocalProperties.sheafificationUnit
        (R := (Stacks.SheafOfModules.Tensor.ringSheaf (J := J)) O) P ≫
        ((_root_.PresheafOfModules.sheafification
          (𝟙 ((Stacks.SheafOfModules.Tensor.ringSheaf (J := J)) O).obj)).map φ).val := by
  apply (_root_.PresheafOfModules.toPresheaf _).map_injective
  rw [Functor.map_comp, Functor.map_comp]
  exact CategoryTheory.toSheafify_naturality J
    ((_root_.PresheafOfModules.toPresheaf
      ((Stacks.SheafOfModules.Tensor.ringSheaf (J := J)) O).obj).map φ)

/-- The image of a sectionwise tensor in the sheafified tensor product. -/
noncomputable def toSheafTensorSection (U : C) (t : (F.val ⊗ G.val).obj (op U)) :
    (((Stacks.SheafOfModules.Tensor.sheafTensor O).obj F).obj G).val.obj (op U) :=
  ((sheafTensorUnit O F G).app (op U)).hom t

/-- The induced map of sheafified tensor products. -/
noncomputable def sheafTensorMap
    {F F' G G' :
      _root_.SheafOfModules.{max u v} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := J)) O)}
    (f : F ⟶ F') (g : G ⟶ G') :
    ((Stacks.SheafOfModules.Tensor.sheafTensor O).obj F).obj G ⟶
      ((Stacks.SheafOfModules.Tensor.sheafTensor O).obj F').obj G' :=
  ((Stacks.SheafOfModules.Tensor.sheafTensor O).map f).app G ≫
    ((Stacks.SheafOfModules.Tensor.sheafTensor O).obj F').map g

/-- The induced map of tensor sheaves is the sheafification of the sectionwise one. -/
theorem sheafTensorMap_eq
    {F F' G G' :
      _root_.SheafOfModules.{max u v} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := J)) O)}
    (f : F ⟶ F') (g : G ⟶ G') :
    sheafTensorMap O f g =
      (_root_.PresheafOfModules.sheafification
        (𝟙 ((Stacks.SheafOfModules.Tensor.ringSheaf (J := J)) O).obj)).map (f.val ⊗ₘ g.val) := by
  rw [tensorHom_def, Functor.map_comp]
  rfl

/-- Naturality of the sheafification unit in the first tensor factor. -/
theorem sheafTensorUnit_naturality_left
    {F F' :
      _root_.SheafOfModules.{max u v} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := J)) O)}
    (f : F' ⟶ F) :
    (f.val ⊗ₘ 𝟙 G.val) ≫ sheafTensorUnit O F G =
      sheafTensorUnit O F' G ≫ (sheafTensorMap O f (𝟙 G)).val := by
  rw [sheafTensorMap_eq, _root_.SheafOfModules.id_val]
  exact sheafificationUnit_naturality O (f.val ⊗ₘ 𝟙 G.val)

/-- Naturality of the sheafification unit in the second tensor factor. -/
theorem sheafTensorUnit_naturality_middle
    {G G' :
      _root_.SheafOfModules.{max u v} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := J)) O)}
    (g : G' ⟶ G) :
    (𝟙 F.val ⊗ₘ g.val) ≫ sheafTensorUnit O F G =
      sheafTensorUnit O F G' ≫ (sheafTensorMap O (𝟙 F) g).val := by
  rw [sheafTensorMap_eq, _root_.SheafOfModules.id_val]
  exact sheafificationUnit_naturality O (𝟙 F.val ⊗ₘ g.val)

/-- Postcomposition in the second variable of the internal Hom sheaf. -/
noncomputable def sheafInternalHomMapRight
    {F G G' :
      _root_.SheafOfModules.{max u v} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := J)) O)}
    (g : G ⟶ G') :
    siteSheafInternalHom J O F G ⟶ siteSheafInternalHom J O F G' :=
  ⟨internalHomMapRight O.obj F.val g.val⟩

/-- Precomposition with the sheafification unit is bijective on internal-Hom sections. -/
theorem internalHomMapLeft_sheafTensorUnit_bijective (X : Cᵒᵖ) :
    Function.Bijective
      ((internalHomMapLeft O.obj (sheafTensorUnit O F G) (G := H.val)).app X).hom := by
  have hH : Presheaf.IsSheaf (J.over X.unop)
      (((restrFun O.obj X.unop).obj H.val).presheaf) :=
    (Over.forget X.unop).op_comp_isSheaf_of_isSheaf (J.over X.unop) J H.val.presheaf H.isSheaf
  have hi : _root_.PresheafOfModules.IsLocallyInjective (J.over X.unop)
      ((restrFun O.obj X.unop).map (sheafTensorUnit O F G)) :=
    Presheaf.isLocallyInjective_whisker (J.over X.unop) J (Over.forget X.unop)
      ((_root_.PresheafOfModules.toPresheaf
        ((Stacks.SheafOfModules.Tensor.ringSheaf (J := J)) O).obj).map (sheafTensorUnit O F G))
  have hs : _root_.PresheafOfModules.IsLocallySurjective (J.over X.unop)
      ((restrFun O.obj X.unop).map (sheafTensorUnit O F G)) :=
    Presheaf.isLocallySurjective_whisker (J.over X.unop) J (Over.forget X.unop)
      ((_root_.PresheafOfModules.toPresheaf
        ((Stacks.SheafOfModules.Tensor.ringSheaf (J := J)) O).obj).map (sheafTensorUnit O F G))
  exact (Stacks.SheafOfModules.TensorLocalProperties.moduleHomEquiv_of_locallyBijective
    (J := J.over X.unop) ((restrFun O.obj X.unop).map (sheafTensorUnit O F G)) hH).bijective

/-- Internal Hom out of the tensor sheaf is internal Hom out of the sectionwise tensor
product. -/
noncomputable def internalHomTensorSheafifyIso :
    internalHom O.obj (((Stacks.SheafOfModules.Tensor.sheafTensor O).obj F).obj G).val H.val ≅
      internalHom O.obj (F.val ⊗ G.val) H.val :=
  _root_.PresheafOfModules.isoMk
    (fun X ↦ (LinearEquiv.ofBijective
      ((internalHomMapLeft O.obj (sheafTensorUnit O F G) (G := H.val)).app X).hom
      (internalHomMapLeft_sheafTensorUnit_bijective O F G H X)).toModuleIso)
    (fun {_ _} f ↦
      (internalHomMapLeft O.obj (sheafTensorUnit O F G) (G := H.val)).naturality f)

/-- The forward morphism of `internalHomTensorSheafifyIso` is precomposition with the
sheafification unit `sheafTensorUnit`. -/
theorem internalHomTensorSheafifyIso_hom :
    (internalHomTensorSheafifyIso O F G H).hom =
      internalHomMapLeft O.obj (sheafTensorUnit O F G) (G := H.val) :=
  rfl

/-- The currying morphism of the sheaf clause: precompose with the sheafification unit, then
curry at the presheaf level. -/
noncomputable def sheafCurryHom :
    siteSheafInternalHom J O (((Stacks.SheafOfModules.Tensor.sheafTensor O).obj F).obj G) H ⟶
      siteSheafInternalHom J O F (siteSheafInternalHom J O G H) :=
  ⟨internalHomMapLeft O.obj (sheafTensorUnit O F G) (G := H.val) ≫
    (presheafInternalHomTensorIso O.obj F.val G.val H.val).hom⟩

/-- The currying morphism `sheafCurryHom` is an isomorphism. -/
instance sheafCurryHom_isIso : IsIso (sheafCurryHom O F G H) := by
  let := (_root_.SheafOfModules.fullyFaithfulForget.{max u v}
    (Stacks.SheafOfModules.Tensor.ringSheaf O)).full
  let := (_root_.SheafOfModules.fullyFaithfulForget.{max u v}
    (Stacks.SheafOfModules.Tensor.ringSheaf O)).faithful
  have h1 : IsIso (internalHomMapLeft O.obj (sheafTensorUnit O F G) (G := H.val)) :=
    inferInstanceAs (IsIso (internalHomTensorSheafifyIso O F G H).hom)
  have h2 : IsIso ((_root_.SheafOfModules.forget
      ((Stacks.SheafOfModules.Tensor.ringSheaf (J := J)) O)).map (sheafCurryHom O F G H)) :=
    inferInstanceAs (IsIso (internalHomMapLeft O.obj (sheafTensorUnit O F G) (G := H.val) ≫
      (presheafInternalHomTensorIso O.obj F.val G.val H.val).hom))
  exact isIso_of_reflects_iso _ (_root_.SheafOfModules.forget _)

/-- **Stacks 03EO, sheaf case.** The canonical currying isomorphism for the sheafified tensor
product and the internal Hom sheaf. -/
@[stacks 03EO "sheaf_internal_hom_tensor_iso"]
noncomputable def sheafCurryIso :
    siteSheafInternalHom J O (((Stacks.SheafOfModules.Tensor.sheafTensor O).obj F).obj G) H ≅
      siteSheafInternalHom J O F (siteSheafInternalHom J O G H) :=
  asIso (sheafCurryHom O F G H)

omit [HasWeakSheafify J AddCommGrpCat.{max u v}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}] in
/-- Precomposition in the first variable of the internal Hom sheaf is the presheaf-level
precomposition on underlying presheaves of modules. -/
theorem sheafInternalHomMapLeft_val
    {F F' G :
      _root_.SheafOfModules.{max u v} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := J)) O)}
    (f : F' ⟶ F) :
    (sheafInternalHomMapLeft J O (G := G) f).val = internalHomMapLeft O.obj f.val :=
  rfl

omit [HasWeakSheafify J AddCommGrpCat.{max u v}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}] in
/-- Postcomposition in the second variable of the internal Hom sheaf is the presheaf-level
postcomposition on underlying presheaves of modules. -/
theorem sheafInternalHomMapRight_val
    {F G G' :
      _root_.SheafOfModules.{max u v} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := J)) O)}
    (g : G ⟶ G') :
    (sheafInternalHomMapRight O (F := F) g).val = internalHomMapRight O.obj F.val g.val :=
  rfl

/-- The underlying morphism of presheaves of modules of the currying isomorphism: precompose
with the sheafification unit, then curry at the presheaf level.

Every statement about `sheafCurryIso` is reduced to its presheaf-level counterpart through this
equation and `SheafOfModules.comp_val`, rather than by a defeq check across the composite. The
two sides are spelled over different presheaves of rings — `(underlyingRingSheaf J O).obj` on
the left and `Oforget O.obj` on the right — and although those are definitionally equal, the
check is expensive enough that doing it once here and rewriting with the result is the
difference between a proof the kernel accepts and one it does not. -/
theorem sheafCurryIso_hom_val :
    (sheafCurryIso O F G H).hom.val =
      internalHomMapLeft O.obj (sheafTensorUnit O F G) ≫
        (presheafInternalHomTensorIso O.obj F.val G.val H.val).hom :=
  rfl

/-- **Stacks 03EO, sheaf case.** The canonical isomorphism is tensor currying on every local
pure tensor. -/
@[stacks 03EO "sheaf_internal_hom_tensor_iso"]
theorem sheafCurryIso_hom_app_tmul (U : C)
    (s : (siteSheafInternalHom J O
      (((Stacks.SheafOfModules.Tensor.sheafTensor O).obj F).obj G) H).val.obj (op U))
    (f : F.val.obj (op U)) (g : G.val.obj (op U)) :
    ((((((sheafCurryIso O F G H).hom.val.app (op U)).hom s).app
        (op (Over.mk (𝟙 U)))).hom f).app (op (Over.mk (𝟙 U)))).hom g =
      (s.app (op (Over.mk (𝟙 U)))).hom
        (toSheafTensorSection O F G U (f ⊗ₜ[O.obj.obj (op U)] g)) := by
  refine (curryAlong_hom_app_plain O.obj F.val G.val H.val
    (sheafTensorUnit O F G) U s (𝟙 U) f (𝟙 U) g).trans ?_
  refine (app_over_mk_congr O.obj U (Category.comp_id (𝟙 U)) s _).trans ?_
  exact congrArg (fun z ↦ (s.app (op (Over.mk (𝟙 U)))).hom
      (((sheafTensorUnit O F G).app (op U)).hom (z ⊗ₜ[O.obj.obj (op U)] g)))
    (congrArg (fun φ ↦ (ConcreteCategory.hom φ) f) (F.val.map_id (op U)))

/-- **Stacks 03EO, sheaf case.** Currying is contravariantly natural in the first tensor
factor. -/
@[stacks 03EO "sheaf_internal_hom_tensor_iso"]
theorem sheafCurryIso_natural_left
    {F F' :
      _root_.SheafOfModules.{max u v} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := J)) O)}
    (f : F' ⟶ F) :
    (sheafCurryIso O F G H).hom ≫ sheafInternalHomMapLeft J O f =
      sheafInternalHomMapLeft J O (sheafTensorMap O f (𝟙 G)) ≫
        (sheafCurryIso O F' G H).hom := by
  refine _root_.SheafOfModules.hom_ext ?_
  rw [_root_.SheafOfModules.comp_val, _root_.SheafOfModules.comp_val, sheafCurryIso_hom_val,
    sheafCurryIso_hom_val, sheafInternalHomMapLeft_val, sheafInternalHomMapLeft_val]
  exact curryAlong_natural_left O.obj F.val G.val H.val f.val (sheafTensorUnit O F G)
    (sheafTensorUnit O F' G) (sheafTensorMap O f (𝟙 G)).val
    (sheafTensorUnit_naturality_left O G f)

/-- **Stacks 03EO, sheaf case.** Currying is contravariantly natural in the second tensor
factor. -/
@[stacks 03EO "sheaf_internal_hom_tensor_iso"]
theorem sheafCurryIso_natural_middle
    {G G' :
      _root_.SheafOfModules.{max u v} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := J)) O)}
    (g : G' ⟶ G) :
    (sheafCurryIso O F G H).hom ≫
        sheafInternalHomMapRight O (sheafInternalHomMapLeft J O g) =
      sheafInternalHomMapLeft J O (sheafTensorMap O (𝟙 F) g) ≫
        (sheafCurryIso O F G' H).hom := by
  refine _root_.SheafOfModules.hom_ext ?_
  rw [_root_.SheafOfModules.comp_val, _root_.SheafOfModules.comp_val, sheafCurryIso_hom_val,
    sheafCurryIso_hom_val, sheafInternalHomMapRight_val, sheafInternalHomMapLeft_val,
    sheafInternalHomMapLeft_val]
  exact curryAlong_natural_middle O.obj F.val G.val H.val g.val (sheafTensorUnit O F G)
    (sheafTensorUnit O F G') (sheafTensorMap O (𝟙 F) g).val
    (sheafTensorUnit_naturality_middle O F g)

/-- **Stacks 03EO, sheaf case.** Currying is covariantly natural in the target. -/
@[stacks 03EO "sheaf_internal_hom_tensor_iso"]
theorem sheafCurryIso_natural_right
    {H H' :
      _root_.SheafOfModules.{max u v} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := J)) O)}
    (h : H ⟶ H') :
    sheafInternalHomMapRight O h ≫ (sheafCurryIso O F G H').hom =
      (sheafCurryIso O F G H).hom ≫
        sheafInternalHomMapRight O (sheafInternalHomMapRight O h) := by
  refine _root_.SheafOfModules.hom_ext ?_
  rw [_root_.SheafOfModules.comp_val, _root_.SheafOfModules.comp_val, sheafCurryIso_hom_val,
    sheafCurryIso_hom_val, sheafInternalHomMapRight_val, sheafInternalHomMapRight_val,
    sheafInternalHomMapRight_val]
  exact curryAlong_natural_right O.obj F.val G.val H.val (sheafTensorUnit O F G) h.val

end Stacks.SheafOfModules.InternalHom

end
