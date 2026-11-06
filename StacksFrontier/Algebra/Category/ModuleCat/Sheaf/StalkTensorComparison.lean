module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SitePointStalkTensor
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.StalkTensor
public import StacksCore.Tactic.StacksAttribute

/-!
# The tensor–stalk comparison on a site, and flatness on stalks

Let `(C, J)` be a site, `O` a presheaf of commutative rings on it and `Φ` a point of the site.
The stalk at `Φ` of the objectwise tensor product of two presheaves of `O`-modules is the
tensor product of the stalks over the stalk of `O`:

`(A ⊗_O F)_Φ ≅ A_Φ ⊗_{O_Φ} F_Φ`.

This is the identification that the converse half of **Stacks 05VC** is proved from — a sheaf of
modules whose stalks at a conservative family of points are flat is flat. The Stacks Project
obtains it by specialising its Lemma 03EL, which says that the pullback along a morphism of
ringed topoi commutes with the tensor product, to the morphism of ringed topoi given by `Φ`;
the proof here is direct, and for that reason the comparison below does **not** carry the
`@[stacks 03EL]` attribute: it is not a statement about an arbitrary morphism of ringed topoi,
which is what 03EL says. The tag carried here is `05VC`, on the final equivalence.

## Main definitions

* `Stacks.moduleFiberGerm`, `Stacks.ringFiberGerm`, `Stacks.tensorObjGerm` : the germ maps into
  the stalk `Stacks.moduleFiber Φ O M` of a presheaf of `O`-modules, read as a module over the
  `CommRingCat`-valued stalk of `O`. The three of them, with `Stacks.restrAddHom` and
  `Stacks.tensorObjRestr`, are retypings of existing maps; see the implementation notes.
* `Stacks.moduleFiber_val` : on a sheaf of modules the stalk `Stacks.moduleFiber` is the stalk
  module `Stacks.moduleStalk` of Stacks 05VB.
* `Stacks.tensorFiberCompare` and `Stacks.tensorFiberCompareInv` : the two directions of the
  comparison, sending the germ of a pure tensor to the tensor product of the germs and back.
* `Stacks.tensorFiberLinearEquiv` : the comparison as an `O_Φ`-linear equivalence.
* `Stacks.moduleFiberMap` : the stalk functor on a morphism, as an `O_Φ`-linear map.

## Main results

* `Stacks.tensorFiberLinearEquiv` : **the tensor–stalk comparison**,
  `(A ⊗_O F)_Φ ≅ A_Φ ⊗_{O_Φ} F_Φ`, for presheaves of modules.
* `Stacks.tensorFiberCompare_naturality` : it is natural in the first variable.
* `Stacks.injective_moduleFiberMap_tensorRight_map` : if the stalk of `F` at `Φ` is flat, then
  tensoring with `F` keeps a stalkwise-injective morphism stalkwise injective.
* `Stacks.mono_presheafModuleFiber_map_sheafification` : monomorphy of a stalk map is not
  changed by sheafification, so the sheaf-level tensor product may be replaced by the
  presheaf-level one.
* `Stacks.isFlat_of_forall_isFlatModuleStalk` : the **converse half of Stacks 05VC**.
* `Stacks.isFlat_iff_forall_isFlatModuleStalk` : **Stacks 05VC** itself, the forward half being
  `Stacks.isFlatModuleStalk_of_isFlat` (Stacks 05VB) via Stacks 08FC.

## Implementation notes

**Why the comparison is built by hand.** Mathlib's
`CategoryTheory.GrothendieckTopology.Point.presheafFiber` is monoidal
(`Mathlib/CategoryTheory/Sites/Point/Monoidal.lean`) for a *fixed* monoidal coefficient
category. That does not apply here: the stalk of a sheaf of modules is a module over the stalk
of the structure sheaf, so the base ring varies with the point and there is no single monoidal
category to work in. Mathlib's filtered-colimit tensor API (`Mathlib/Algebra/Colimit/Module.lean`,
`Mathlib/Algebra/Colimit/TensorProduct.lean` and
`Mathlib/LinearAlgebra/TensorProduct/DirectLimit.lean`) likewise fixes the base ring in its
headers. What is proved here is the varying-base-ring
statement: for a cofiltered system of rings `R` with modules `M`, `N`,
`colim (M ⊗_R N) ≅ (colim M) ⊗_{colim R} (colim N)`, in the shape the stalk functor needs.

**The shape of the proof.** `Stacks.tensorFiberCompare` is assembled from the germs of pure
tensors by the universal property `Point.presheafFiberDesc` of the stalk, which is available
because the underlying abelian group of `Stacks.presheafModuleFiber` *is* Mathlib's
`presheafFiber` (`Stacks.presheafModuleFiberCompForget₂` is `Iso.refl`). The inverse direction
cannot be built that way — there is no canonical common neighbourhood for a germ of `A` and a
germ of `F` — so it is defined on representatives and shown independent of them
(`Stacks.tensorObjGerm_tmul_congr`): two representatives are compared over a common neighbourhood
obtained from `IsCofiltered`, and then the `A`-sections and the `F`-sections are made to agree
by *two successive refinements*, which avoids having to coequalise a pair of parallel
morphisms.

**Where the stalk itself comes from.** `Stacks.moduleFiber` is
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SitePointStalkTensor`'s: the stalk
`Stacks.presheafModuleFiber` with its scalars restricted along
`Stacks.commRingPresheafFiberIso`, so that it is a module over the `CommRingCat`-valued stalk of
`O`. This file states that base ring as `Stacks.commRingFiber Φ O` and that file as
`Stacks.ringFiber Φ O`; both are reducible abbreviations for
`(Φ.presheafFiber (A := CommRingCat)).obj O`, so the two spellings are the same term.

**Retypings, and why they are `def`s with ascribed types.** Three types that are equal but not
syntactically equal appear throughout, and in each case a type ascription is not enough,
because instance search and `rw` both look at the syntactic spelling:

* the value of `M.map f.op` is typed in `(ModuleCat.restrictScalars _).obj (M.obj (op U))`,
  whose `Module` instance is a different one from that of `M.obj (op U)`, so a tensor product
  formed at the first spelling is not the one a statement about the second expects. Hence
  `Stacks.restrAddHom`.
* the carrier of `(Stacks.tensorObj A F).obj (op X)` is the bare tensor product, but not
  syntactically, so `map_add`, `map_zero` and `TensorProduct.induction_on` are unusable on an
  argument of the germ map as it stands — the goal stops being type-correct at `implicit`
  transparency. Hence `Stacks.tensorObjGerm` and `Stacks.tensorObjRestr`.
* the germ-restriction compatibility is stated with the neighbourhood equality as an explicit
  hypothesis (`Stacks.moduleFiberGerm_w'`) rather than with `Φ.fiber.map f x` in the subscript,
  so that it composes with `Eq.trans` instead of needing a rewrite under a germ map.

**Universes.** All three of the site universes `u`, `v` and the section universe `w` are
independent, and the only size hypothesis is `LocallySmall.{w} C`, which
`Stacks.presheafModuleFiber` requires. Nothing here is narrowed: the stalk is a filtered
colimit indexed by `Φ.fiber.Elements`, and the `InitiallySmall.{w}`/`IsCofiltered` instances
that `PresheafOfModules.colimitFunctor` needs for it are supplied by Mathlib for every point,
so no smallness of the point family and no collapse `w = max v w` is used. In particular the
`max v w` appearing in the tagged form of Stacks 05VB
(`Stacks.isFlatModuleStalk_of_isFlat`) is *not* inherited here; it comes from the free presheaf
of modules used by Stacks 08FC and enters only the forward half.

**The sheafification hypothesis.** `Stacks.isFlat_of_forall_isFlatModuleStalk` assumes
`HasSheafify J AddCommGrpCat.{w}` and not merely `HasWeakSheafify`. That is forced and not
chosen: `Abelian (SheafOfModules (Stacks.commRingSheafToRingSheaf O))` does not synthesize from
`HasWeakSheafify` alone, and without it `Stacks.SheafOfModules.IsFlat` — exactness of the
tensor functor — cannot be reduced to the preservation of a monomorphism. It is the Lean form
of the Stacks Project's standing convention that `Mod(O)` is an abelian category.

## References

* [Stacks Project, Tag 05VC](https://stacks.math.columbia.edu/tag/05VC)
* [Stacks Project, Tag 03EL](https://stacks.math.columbia.edu/tag/03EL)
* [Stacks Project, Tag 05V3](https://stacks.math.columbia.edu/tag/05V3)
* [Stacks Project, Tag 05VB](https://stacks.math.columbia.edu/tag/05VB)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TensorProduct

universe w v u

namespace Stacks

variable {C : Type u} [Category.{v} C] [LocallySmall.{w} C] {J : GrothendieckTopology C}
  (Φ : J.Point.{w}) (O : Cᵒᵖ ⥤ CommRingCat.{w})

/-! ### The stalk of a presheaf of modules over the `CommRingCat`-valued stalk -/

/-- The stalk at `Φ` of a presheaf of commutative rings. -/
noncomputable abbrev commRingFiber : CommRingCat.{w} :=
  (Φ.presheafFiber (A := CommRingCat.{w})).obj O

/-- The germ map `M(U) →+ M_Φ` of `Stacks.moduleFiber`. -/
noncomputable def moduleFiberGerm (M : PresheafOfModules.{w} (ringPresheaf O)) (U : C)
    (x : Φ.fiber.obj U) : M.obj (op U) →+ moduleFiber Φ O M :=
  toPresheafModuleFiber Φ M U x

/-- The germ map `O(U) →+* O_Φ` into the `CommRingCat`-valued stalk. -/
noncomputable def ringFiberGerm (U : C) (x : Φ.fiber.obj U) :
    (ringPresheaf O).obj (op U) →+* commRingFiber Φ O :=
  (commRingPresheafFiberIso Φ O).hom.hom.comp (Φ.toPresheafFiber U x (ringPresheaf O)).hom

variable {Φ O}

/-- The restriction map of a presheaf of modules, as an additive map between the plain
section groups. The ascribed result type is load-bearing: the value of `M.map f.op` is typed
as an element of `(ModuleCat.restrictScalars _).obj (M.obj (op U))`, which is the same type
as `M.obj (op U)` with a *different* `Module` instance found by typeclass search, so a tensor
product formed at the first spelling is not the one a statement about the second expects. -/
noncomputable def restrAddHom (M : PresheafOfModules.{w} (ringPresheaf O)) {U V : C}
    (f : U ⟶ V) : M.obj (op V) →+ M.obj (op U) :=
  (M.map f.op).hom.toAddMonoidHom

omit [LocallySmall.{w} C] in
/-- `Stacks.restrAddHom M f` sends a section `m` to its restriction `M.map f.op m`. -/
@[simp]
lemma restrAddHom_apply (M : PresheafOfModules.{w} (ringPresheaf O)) {U V : C} (f : U ⟶ V)
    (m : M.obj (op V)) : restrAddHom M f m = M.map f.op m :=
  rfl

/-- The germ map of `Stacks.moduleFiber` is compatible with the action of scalars. -/
lemma moduleFiberGerm_smul {M : PresheafOfModules.{w} (ringPresheaf O)} (U : C)
    (x : Φ.fiber.obj U) (r : (ringPresheaf O).obj (op U)) (m : M.obj (op U)) :
    moduleFiberGerm Φ O M U x (r • m) =
      ringFiberGerm Φ O U x r • moduleFiberGerm Φ O M U x m := by
  show toPresheafModuleFiber Φ M U x (r • m) = _
  rw [toPresheafModuleFiber_smul]
  exact congrArg (fun t => t • toPresheafModuleFiber Φ M U x m)
    ((commRingPresheafFiberIso Φ O).hom_inv_id_apply _).symm

/-- The germ maps of `Stacks.moduleFiber` are compatible with restriction. -/
lemma moduleFiberGerm_w {M : PresheafOfModules.{w} (ringPresheaf O)} {U V : C} (f : U ⟶ V)
    (x : Φ.fiber.obj U) (m : M.obj (op V)) :
    moduleFiberGerm Φ O M V (Φ.fiber.map f x) m =
      moduleFiberGerm Φ O M U x (restrAddHom M f m) :=
  toPresheafModuleFiber_w Φ M f x m

/-- The germ-restriction compatibility with the neighbourhood equality as a hypothesis. This
is the form that composes: stating it with `Φ.fiber.map f x` in the subscript makes every use
a rewrite under a germ map, where the two spellings of a section group defeat `rw`. -/
lemma moduleFiberGerm_w' {M : PresheafOfModules.{w} (ringPresheaf O)} {U V : C} (f : U ⟶ V)
    (x : Φ.fiber.obj U) (y : Φ.fiber.obj V) (h : Φ.fiber.map f x = y) (m : M.obj (op V)) :
    moduleFiberGerm Φ O M V y m = moduleFiberGerm Φ O M U x (restrAddHom M f m) := by
  subst h
  exact moduleFiberGerm_w f x m

/-- The ring germ maps are compatible with restriction. -/
lemma ringFiberGerm_w {U V : C} (f : U ⟶ V) (x : Φ.fiber.obj U)
    (r : (ringPresheaf O).obj (op V)) :
    ringFiberGerm Φ O V (Φ.fiber.map f x) r =
      ringFiberGerm Φ O U x ((ringPresheaf O).map f.op r) :=
  congrArg (commRingPresheafFiberIso Φ O).hom.hom
    (Φ.toPresheafFiber_w_apply f x (ringPresheaf O) r).symm

/-- Every element of `Stacks.moduleFiber` is a germ. -/
lemma moduleFiberGerm_jointly_surjective {M : PresheafOfModules.{w} (ringPresheaf O)}
    (m : moduleFiber Φ O M) :
    ∃ (U : C) (x : Φ.fiber.obj U) (s : M.obj (op U)), moduleFiberGerm Φ O M U x s = m :=
  toPresheafModuleFiber_jointly_surjective Φ M m

/-- Two sections over one neighbourhood have the same germ exactly when they agree after
restriction to a smaller neighbourhood. -/
lemma moduleFiberGerm_eq_iff {M : PresheafOfModules.{w} (ringPresheaf O)} (U : C)
    (x : Φ.fiber.obj U) (s t : M.obj (op U)) :
    moduleFiberGerm Φ O M U x s = moduleFiberGerm Φ O M U x t ↔
      ∃ (V : C) (f : V ⟶ U) (y : Φ.fiber.obj V), Φ.fiber.map f y = x ∧
        M.map f.op s = M.map f.op t :=
  toPresheafModuleFiber_eq_iff Φ M U x s t

/-- The germ maps of `Stacks.moduleFiber` are natural in the presheaf of modules. -/
lemma moduleFiberGerm_naturality {M M' : PresheafOfModules.{w} (ringPresheaf O)} (g : M ⟶ M')
    (U : C) (x : Φ.fiber.obj U) (m : M.obj (op U)) :
    (presheafModuleFiber Φ (ringPresheaf O)).map g (moduleFiberGerm Φ O M U x m) =
      moduleFiberGerm Φ O M' U x (g.app (op U) m) :=
  toPresheafModuleFiber_naturality Φ g U x m

/-! ### The comparison map from the stalk of the tensor product -/

section Compare

variable (A F : PresheafOfModules.{w} (ringPresheaf O))

/-- The germ of a pure tensor with a fixed first factor, as an additive map on the second. -/
noncomputable def tensorFiberLegAux (X : C) (x : Φ.fiber.obj X) (a : A.obj (op X)) :
    F.obj (op X) →+ (moduleFiber Φ O A ⊗[commRingFiber Φ O] moduleFiber Φ O F) :=
  (TensorProduct.mk (commRingFiber Φ O) (moduleFiber Φ O A) (moduleFiber Φ O F)
    (moduleFiberGerm Φ O A X x a)).toAddMonoidHom.comp (moduleFiberGerm Φ O F X x)

/-- `Stacks.tensorFiberLegAux` sends `s` to the tensor product of the germs of `a` and `s`. -/
@[simp]
lemma tensorFiberLegAux_apply (X : C) (x : Φ.fiber.obj X) (a : A.obj (op X))
    (s : F.obj (op X)) :
    tensorFiberLegAux A F X x a s =
      moduleFiberGerm Φ O A X x a ⊗ₜ moduleFiberGerm Φ O F X x s :=
  rfl

/-- The germ of a pure tensor, as a biadditive map. -/
noncomputable def tensorFiberLegHom (X : C) (x : Φ.fiber.obj X) :
    A.obj (op X) →+
      (F.obj (op X) →+ (moduleFiber Φ O A ⊗[commRingFiber Φ O] moduleFiber Φ O F)) :=
  AddMonoidHom.mk' (tensorFiberLegAux A F X x) (fun a a' =>
    AddMonoidHom.ext fun s => by
      rw [AddMonoidHom.add_apply, tensorFiberLegAux_apply, tensorFiberLegAux_apply,
        tensorFiberLegAux_apply, map_add, TensorProduct.add_tmul])

/-- The germ of a pure tensor, as an additive map out of the sections of the objectwise tensor
product over a neighbourhood of `Φ`. This is the family of maps out of which the comparison
`Stacks.tensorFiberCompare` is assembled. -/
noncomputable def tensorFiberLeg (X : C) (x : Φ.fiber.obj X) :
    (A.obj (op X) ⊗[(ringPresheaf O).obj (op X)] F.obj (op X)) →+
      (moduleFiber Φ O A ⊗[commRingFiber Φ O] moduleFiber Φ O F) :=
  TensorProduct.liftAddHom (tensorFiberLegHom A F X x) (fun r a s => by
    change tensorFiberLegAux A F X x (r • a) s = tensorFiberLegAux A F X x a (r • s)
    rw [tensorFiberLegAux_apply, tensorFiberLegAux_apply, moduleFiberGerm_smul,
      moduleFiberGerm_smul, TensorProduct.smul_tmul])

/-- `Stacks.tensorFiberLeg` sends a pure tensor `a ⊗ₜ s` to the tensor product of the germs of
`a` and `s`. -/
@[simp]
lemma tensorFiberLeg_tmul (X : C) (x : Φ.fiber.obj X) (a : A.obj (op X)) (s : F.obj (op X)) :
    tensorFiberLeg A F X x (a ⊗ₜ[(ringPresheaf O).obj (op X)] s) =
      moduleFiberGerm Φ O A X x a ⊗ₜ moduleFiberGerm Φ O F X x s :=
  TensorProduct.liftAddHom_tmul _ _ a s

/-- The restriction map of the objectwise tensor product, as an additive map between the bare
tensor products. The ascribed result type is what lets `TensorProduct.induction_on` be used on
its argument: the carrier of `(Stacks.tensorObj A F).obj (op Y)` is the same type, but not
syntactically, and `rw` then strands the goal at `implicit` transparency. -/
noncomputable def tensorObjRestr {X Y : C} (f : X ⟶ Y) :
    (A.obj (op Y) ⊗[(ringPresheaf O).obj (op Y)] F.obj (op Y)) →+
      (A.obj (op X) ⊗[(ringPresheaf O).obj (op X)] F.obj (op X)) :=
  ((tensorObj A F).map f.op).hom.toAddMonoidHom

omit [LocallySmall.{w} C] in
/-- Restriction in the objectwise tensor product sends a pure tensor to the pure tensor of the
restrictions. -/
@[simp]
lemma tensorObjRestr_tmul {X Y : C} (f : X ⟶ Y) (a : A.obj (op Y)) (s : F.obj (op Y)) :
    tensorObjRestr A F f (a ⊗ₜ[(ringPresheaf O).obj (op Y)] s) =
      restrAddHom A f a ⊗ₜ[(ringPresheaf O).obj (op X)] restrAddHom F f s :=
  rfl

/-- The germ map of the objectwise tensor product `Stacks.tensorObj A F`, with its domain
ascribed as the bare tensor product. Without this the germ map's domain is spelled
`(tensorObj A F).obj (op X)`, which is the same type but makes `map_add`, `map_zero` and
`TensorProduct.induction_on` unusable on its argument: the goal stops being type-correct at
`implicit` transparency.

`Stacks.tensorGerm` is the same retyping for Mathlib's monoidal product `A ⊗ F` instead of
`Stacks.tensorObj A F`. The two presheaves of modules are definitionally equal, so the two germ
maps are the same map; but they are *not* interchangeable, because the whole point of either
declaration is which of the two spellings its codomain carries. Substituting
`Stacks.tensorGerm` here makes the goals of this file read
`moduleFiber Φ O (MonoidalCategoryStruct.tensorObj A F)` while the rest of the development is
stated over `moduleFiber Φ O (tensorObj A F)`, and `map_add`/`map_zero` then fail with
"the target expression is not type-correct under the `implicit` transparency level". -/
noncomputable def tensorObjGerm (X : C) (u : Φ.fiber.obj X) :
    (A.obj (op X) ⊗[(ringPresheaf O).obj (op X)] F.obj (op X)) →+
      moduleFiber Φ O (tensorObj A F) :=
  moduleFiberGerm Φ O (tensorObj A F) X u

/-- `Stacks.tensorObjGerm` is the germ map of `Stacks.tensorObj A F`. -/
lemma tensorObjGerm_apply (X : C) (u : Φ.fiber.obj X)
    (t : A.obj (op X) ⊗[(ringPresheaf O).obj (op X)] F.obj (op X)) :
    tensorObjGerm A F X u t = moduleFiberGerm Φ O (tensorObj A F) X u t :=
  rfl

/-- The germs of pure tensors are compatible with restriction along a morphism of
neighbourhoods. -/
lemma tensorFiberLeg_comp_restr {X Y : C} (f : X ⟶ Y) (x : Φ.fiber.obj X)
    (t : A.obj (op Y) ⊗[(ringPresheaf O).obj (op Y)] F.obj (op Y)) :
    tensorFiberLeg A F X x (tensorObjRestr A F f t) =
      tensorFiberLeg A F Y (Φ.fiber.map f x) t := by
  induction t using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero, map_zero]
  | tmul a s =>
    rw [tensorObjRestr_tmul, tensorFiberLeg_tmul, tensorFiberLeg_tmul,
      moduleFiberGerm_w f x a, moduleFiberGerm_w f x s]
  | add t t' h h' => rw [map_add, map_add, map_add, h, h']

/-- The cocone condition that `Stacks.tensorFiberCompare` needs. -/
lemma tensorFiberLeg_w {X Y : C} (f : X ⟶ Y) (x : Φ.fiber.obj X) :
    (tensorObj A F).presheaf.map f.op ≫
        AddCommGrpCat.ofHom (tensorFiberLeg A F X x) =
      AddCommGrpCat.ofHom (tensorFiberLeg A F Y (Φ.fiber.map f x)) :=
  AddCommGrpCat.hom_ext (AddMonoidHom.ext fun t => tensorFiberLeg_comp_restr A F f x t)

/-- **The comparison map of Stacks 03EL for a site.** The stalk of the objectwise tensor
product of two presheaves of modules maps to the tensor product of the stalks, by sending the
germ of a pure tensor to the tensor product of the germs. -/
noncomputable def tensorFiberCompare :
    moduleFiber Φ O (tensorObj A F) →+
      (moduleFiber Φ O A ⊗[commRingFiber Φ O] moduleFiber Φ O F) :=
  (Φ.presheafFiberDesc (P := (tensorObj A F).presheaf)
    (T := AddCommGrpCat.of (moduleFiber Φ O A ⊗[commRingFiber Φ O] moduleFiber Φ O F))
    (fun X x => AddCommGrpCat.ofHom (tensorFiberLeg A F X x))
    (fun _ _ f x => tensorFiberLeg_w A F f x)).hom

/-- `Stacks.tensorFiberCompare` sends the germ of a pure tensor `a ⊗ₜ s` to the tensor product
of the germs of `a` and `s`. -/
@[simp]
lemma tensorFiberCompare_germ_tmul (X : C) (x : Φ.fiber.obj X) (a : A.obj (op X))
    (s : F.obj (op X)) :
    tensorFiberCompare A F (tensorObjGerm A F X x (a ⊗ₜ[(ringPresheaf O).obj (op X)] s)) =
      moduleFiberGerm Φ O A X x a ⊗ₜ moduleFiberGerm Φ O F X x s :=
  DFunLike.congr_fun (congrArg AddCommGrpCat.Hom.hom
    (Φ.toPresheafFiber_presheafFiberDesc
      (P := (tensorObj A F).presheaf)
      (T := AddCommGrpCat.of (moduleFiber Φ O A ⊗[commRingFiber Φ O] moduleFiber Φ O F))
      (fun X x => AddCommGrpCat.ofHom (tensorFiberLeg A F X x))
      (fun _ _ f x => tensorFiberLeg_w A F f x) X x)) (a ⊗ₜ s)

/-! ### Common neighbourhoods -/

omit [LocallySmall.{w} C] in
/-- Restriction along a composite is the composite of the restrictions. -/
lemma restrAddHom_comp (M : PresheafOfModules.{w} (ringPresheaf O)) {U V W : C} (f : U ⟶ V)
    (g : V ⟶ W) (m : M.obj (op W)) :
    restrAddHom M (f ≫ g) m = restrAddHom M f (restrAddHom M g m) :=
  M.map_comp_apply g.op f.op m

/-- A finite family of elements of the stalks of two presheaves of modules and of the stalk of
the structure presheaf consists of germs of sections over one common neighbourhood of `Φ`. -/
lemma exists_germ_families {l k j : ℕ} (m : Fin l → moduleFiber Φ O A)
    (n : Fin k → moduleFiber Φ O F) (c : Fin j → commRingFiber Φ O) :
    ∃ (X : C) (u : Φ.fiber.obj X) (a : Fin l → A.obj (op X)) (s : Fin k → F.obj (op X))
      (r : Fin j → (ringPresheaf O).obj (op X)),
      (∀ i, moduleFiberGerm Φ O A X u (a i) = m i) ∧
        (∀ i, moduleFiberGerm Φ O F X u (s i) = n i) ∧
          (∀ i, ringFiberGerm Φ O X u (r i) = c i) := by
  obtain ⟨@⟨X₀, x₀⟩⟩ := IsCofiltered.nonempty (C := Φ.fiber.Elements)
  obtain ⟨X₁, x₁, -, -, a, ha⟩ := exists_toPresheafModuleFiber_family Φ A X₀ x₀ m
  obtain ⟨X₂, x₂, g₂, hg₂, s, hs⟩ := exists_toPresheafModuleFiber_family Φ F X₁ x₁ n
  obtain ⟨X, u, g, hg, r, hr⟩ := exists_toPresheafFiber_family Φ (ringPresheaf O) X₂ x₂
    (fun i => (commRingPresheafFiberIso Φ O).inv.hom (c i))
  have hgg : Φ.fiber.map (g ≫ g₂) u = x₁ := by
    rw [Φ.fiber.map_comp]
    exact (congrArg (Φ.fiber.map g₂) hg).trans hg₂
  refine ⟨X, u, fun i => restrAddHom A (g ≫ g₂) (a i), fun i => restrAddHom F g (s i), r,
    fun i => ?_, fun i => ?_, fun i => ?_⟩
  · exact (moduleFiberGerm_w' (g ≫ g₂) u x₁ hgg (a i)).symm.trans (ha i)
  · exact (moduleFiberGerm_w' g u x₂ hg (s i)).symm.trans (hs i)
  · show (commRingPresheafFiberIso Φ O).hom.hom _ = _
    rw [hr i]
    exact (commRingPresheafFiberIso Φ O).inv_hom_id_apply _

/-- The germ of a pure tensor computed over a smaller neighbourhood. -/
lemma tensorObjGerm_tmul_w {X Y : C} (f : X ⟶ Y) (u : Φ.fiber.obj X) (v : Φ.fiber.obj Y)
    (h : Φ.fiber.map f u = v) (c : A.obj (op Y)) (d : F.obj (op Y)) :
    tensorObjGerm A F Y v (c ⊗ₜ[(ringPresheaf O).obj (op Y)] d) =
      tensorObjGerm A F X u
        (restrAddHom A f c ⊗ₜ[(ringPresheaf O).obj (op X)] restrAddHom F f d) :=
  (moduleFiberGerm_w' f u v h _).trans (congrArg _ (tensorObjRestr_tmul A F f c d))

/-- Equal germs over two neighbourhoods have equal germs of the restrictions to a common smaller
neighbourhood. -/
private lemma moduleFiberGerm_restr_eq_of_eq {M : PresheafOfModules.{w} (ringPresheaf O)}
    {X Y V : C} (p : V ⟶ X) (q : V ⟶ Y) (u : Φ.fiber.obj X) (v : Φ.fiber.obj Y)
    (w : Φ.fiber.obj V) (hp : Φ.fiber.map p w = u) (hq : Φ.fiber.map q w = v)
    (a : M.obj (op X)) (b : M.obj (op Y))
    (h : moduleFiberGerm Φ O M X u a = moduleFiberGerm Φ O M Y v b) :
    moduleFiberGerm Φ O M V w (restrAddHom M p a) = moduleFiberGerm Φ O M V w (restrAddHom M q b) :=
  ((moduleFiberGerm_w' p w u hp a).symm.trans h).trans (moduleFiberGerm_w' q w v hq b)

/-- **Well-definedness of the inverse comparison.** The germ of a pure tensor depends only on
the germs of its two factors, not on the neighbourhood they are taken over. -/
lemma tensorObjGerm_tmul_congr {X Y : C} (u : Φ.fiber.obj X) (v : Φ.fiber.obj Y)
    (a : A.obj (op X)) (s : F.obj (op X)) (b : A.obj (op Y)) (t : F.obj (op Y))
    (ha : moduleFiberGerm Φ O A X u a = moduleFiberGerm Φ O A Y v b)
    (hs : moduleFiberGerm Φ O F X u s = moduleFiberGerm Φ O F Y v t) :
    tensorObjGerm A F X u (a ⊗ₜ[(ringPresheaf O).obj (op X)] s) =
      tensorObjGerm A F Y v (b ⊗ₜ[(ringPresheaf O).obj (op Y)] t) := by
  obtain ⟨W, ⟨p, hp⟩, ⟨q, hq⟩, -⟩ :=
    IsCofilteredOrEmpty.cone_objs (Φ.fiber.elementsMk X u) (Φ.fiber.elementsMk Y v)
  -- move both pairs of factors to the common neighbourhood `W`
  have ha' := moduleFiberGerm_restr_eq_of_eq p q u v W.2 hp hq a b ha
  have hs' := moduleFiberGerm_restr_eq_of_eq p q u v W.2 hp hq s t hs
  -- refine once so that the `A`-sections agree, then again so that the `F`-sections do
  obtain ⟨V₁, f₁, y₁, hy₁, hA⟩ := (moduleFiberGerm_eq_iff W.1 W.2 _ _).1 ha'
  replace hs' := moduleFiberGerm_restr_eq_of_eq f₁ f₁ W.2 W.2 y₁ hy₁ hy₁ _ _ hs'
  obtain ⟨V₂, f₂, y₂, hy₂, hF⟩ := (moduleFiberGerm_eq_iff V₁ y₁ _ _).1 hs'
  -- the two restrictions to `V₂` of the two pure tensors now agree
  have comp_eq : ∀ (M : PresheafOfModules.{w} (ringPresheaf O)) (m : M.obj (op X))
      (n : M.obj (op Y)),
      restrAddHom M f₂ (restrAddHom M f₁ (restrAddHom M p m)) =
        restrAddHom M f₂ (restrAddHom M f₁ (restrAddHom M q n)) →
      restrAddHom M (f₂ ≫ f₁ ≫ p) m = restrAddHom M (f₂ ≫ f₁ ≫ q) n := fun M m n h => by
    simp only [restrAddHom_comp]
    exact h
  have hA' := comp_eq A a b (congrArg (restrAddHom A f₂) hA)
  have hF' := comp_eq F s t hF
  have hu : Φ.fiber.map (f₂ ≫ f₁ ≫ p) y₂ = u := by
    simp only [Φ.fiber.map_comp, CategoryTheory.comp_apply, hy₂, hy₁, hp]
  have hv : Φ.fiber.map (f₂ ≫ f₁ ≫ q) y₂ = v := by
    simp only [Φ.fiber.map_comp, CategoryTheory.comp_apply, hy₂, hy₁, hq]
  refine (tensorObjGerm_tmul_w A F _ y₂ u hu a s).trans
    (Eq.trans (congrArg _ ?_) (tensorObjGerm_tmul_w A F _ y₂ v hv b t).symm)
  rw [hA', hF']

/-! ### The inverse comparison -/

/-- A germ of `A` and a germ of `F` are germs of sections over one common neighbourhood. -/
lemma exists_tensorFiberRep (x : moduleFiber Φ O A) (y : moduleFiber Φ O F) :
    ∃ P : Σ (P : Φ.fiber.Elements), A.obj (op P.1) × F.obj (op P.1),
      moduleFiberGerm Φ O A P.1.1 P.1.2 P.2.1 = x ∧
        moduleFiberGerm Φ O F P.1.1 P.1.2 P.2.2 = y := by
  obtain ⟨X, u, a, s, -, ha, hs, -⟩ := exists_germ_families A F (fun _ : Fin 1 => x)
    (fun _ : Fin 1 => y) (fun i : Fin 0 => i.elim0)
  exact ⟨⟨Φ.fiber.elementsMk X u, a 0, s 0⟩, ha 0, hs 0⟩

/-- **The inverse comparison of Stacks 03EL for a site, on pure tensors.** The tensor product
of a germ of `A` and a germ of `F` is sent to the germ of the pure tensor of representatives
over a common neighbourhood; `Stacks.tensorObjGerm_tmul_congr` is what makes this independent of
the representatives chosen. -/
noncomputable def tensorFiberBack (x : moduleFiber Φ O A) (y : moduleFiber Φ O F) :
    moduleFiber Φ O (tensorObj A F) :=
  tensorObjGerm A F (exists_tensorFiberRep A F x y).choose.1.1
    (exists_tensorFiberRep A F x y).choose.1.2
    ((exists_tensorFiberRep A F x y).choose.2.1 ⊗ₜ (exists_tensorFiberRep A F x y).choose.2.2)

/-- `Stacks.tensorFiberBack` sends the germs of `a` and `s` over a common neighbourhood to the
germ of the pure tensor `a ⊗ₜ s`. -/
@[simp]
lemma tensorFiberBack_germ (X : C) (u : Φ.fiber.obj X) (a : A.obj (op X)) (s : F.obj (op X)) :
    tensorFiberBack A F (moduleFiberGerm Φ O A X u a) (moduleFiberGerm Φ O F X u s) =
      tensorObjGerm A F X u (a ⊗ₜ[(ringPresheaf O).obj (op X)] s) :=
  tensorObjGerm_tmul_congr A F _ _ _ _ _ _
    (exists_tensorFiberRep A F (moduleFiberGerm Φ O A X u a)
      (moduleFiberGerm Φ O F X u s)).choose_spec.1
    (exists_tensorFiberRep A F (moduleFiberGerm Φ O A X u a)
      (moduleFiberGerm Φ O F X u s)).choose_spec.2

/-- `Stacks.tensorFiberBack` is additive in its first argument. -/
lemma tensorFiberBack_add_left (x x' : moduleFiber Φ O A) (y : moduleFiber Φ O F) :
    tensorFiberBack A F (x + x') y = tensorFiberBack A F x y + tensorFiberBack A F x' y := by
  obtain ⟨X, u, a, s, -, ha, hs, -⟩ := exists_germ_families A F
    ![x, x'] (fun _ : Fin 1 => y) (fun i : Fin 0 => i.elim0)
  have hx : moduleFiberGerm Φ O A X u (a 0) = x := by simpa using ha 0
  have hx' : moduleFiberGerm Φ O A X u (a 1) = x' := by simpa using ha 1
  have hy : moduleFiberGerm Φ O F X u (s 0) = y := hs 0
  clear ha hs
  subst hx hx' hy
  rw [show moduleFiberGerm Φ O A X u (a 0) + moduleFiberGerm Φ O A X u (a 1) =
      moduleFiberGerm Φ O A X u (a 0 + a 1) from (map_add _ _ _).symm,
    tensorFiberBack_germ, tensorFiberBack_germ, tensorFiberBack_germ]
  exact (congrArg (tensorObjGerm A F X u) (TensorProduct.add_tmul (a 0) (a 1) (s 0))).trans
    (map_add _ _ _)

/-- `Stacks.tensorFiberBack` is additive in its second argument. -/
lemma tensorFiberBack_add_right (x : moduleFiber Φ O A) (y y' : moduleFiber Φ O F) :
    tensorFiberBack A F x (y + y') = tensorFiberBack A F x y + tensorFiberBack A F x y' := by
  obtain ⟨X, u, a, s, -, ha, hs, -⟩ := exists_germ_families A F (fun _ : Fin 1 => x)
    ![y, y'] (fun i : Fin 0 => i.elim0)
  have hx : moduleFiberGerm Φ O A X u (a 0) = x := ha 0
  have hy : moduleFiberGerm Φ O F X u (s 0) = y := by simpa using hs 0
  have hy' : moduleFiberGerm Φ O F X u (s 1) = y' := by simpa using hs 1
  clear ha hs
  subst hx hy hy'
  rw [show moduleFiberGerm Φ O F X u (s 0) + moduleFiberGerm Φ O F X u (s 1) =
      moduleFiberGerm Φ O F X u (s 0 + s 1) from (map_add _ _ _).symm,
    tensorFiberBack_germ, tensorFiberBack_germ, tensorFiberBack_germ]
  exact (congrArg (tensorObjGerm A F X u) (TensorProduct.tmul_add (a 0) (s 0) (s 1))).trans
    (map_add _ _ _)

/-- `Stacks.tensorFiberBack` is balanced over the stalk of `O`. -/
lemma tensorFiberBack_smul (c : commRingFiber Φ O) (x : moduleFiber Φ O A)
    (y : moduleFiber Φ O F) :
    tensorFiberBack A F (c • x) y = tensorFiberBack A F x (c • y) := by
  obtain ⟨X, u, a, s, r, ha, hs, hr⟩ := exists_germ_families A F (fun _ : Fin 1 => x)
    (fun _ : Fin 1 => y) (fun _ : Fin 1 => c)
  have hx : moduleFiberGerm Φ O A X u (a 0) = x := ha 0
  have hy : moduleFiberGerm Φ O F X u (s 0) = y := hs 0
  have hc : ringFiberGerm Φ O X u (r 0) = c := hr 0
  clear ha hs hr
  subst hx hy hc
  rw [← moduleFiberGerm_smul, ← moduleFiberGerm_smul, tensorFiberBack_germ,
    tensorFiberBack_germ]
  exact congrArg (tensorObjGerm A F X u) (TensorProduct.smul_tmul (r 0) (a 0) (s 0))

/-- `Stacks.tensorFiberBack` as a biadditive map. -/
noncomputable def tensorFiberBackHom :
    moduleFiber Φ O A →+ (moduleFiber Φ O F →+ moduleFiber Φ O (tensorObj A F)) :=
  AddMonoidHom.mk'
    (fun x => AddMonoidHom.mk' (tensorFiberBack A F x) (tensorFiberBack_add_right A F x))
    (fun x x' => AddMonoidHom.ext fun y => tensorFiberBack_add_left A F x x' y)

/-- **The inverse comparison of Stacks 03EL for a site.** -/
noncomputable def tensorFiberCompareInv :
    (moduleFiber Φ O A ⊗[commRingFiber Φ O] moduleFiber Φ O F) →+
      moduleFiber Φ O (tensorObj A F) :=
  TensorProduct.liftAddHom (tensorFiberBackHom A F)
    (fun c x y => tensorFiberBack_smul A F c x y)

/-- `Stacks.tensorFiberCompareInv` sends `x ⊗ₜ y` to `Stacks.tensorFiberBack A F x y`. -/
@[simp]
lemma tensorFiberCompareInv_tmul (x : moduleFiber Φ O A) (y : moduleFiber Φ O F) :
    tensorFiberCompareInv A F (x ⊗ₜ y) = tensorFiberBack A F x y :=
  TensorProduct.liftAddHom_tmul _ _ x y

/-! ### The two comparisons are mutually inverse -/

/-- `Stacks.tensorFiberCompareInv` is a left inverse of `Stacks.tensorFiberCompare` on germs. -/
lemma tensorFiberCompareInv_compare_germ (X : C) (u : Φ.fiber.obj X)
    (τ : A.obj (op X) ⊗[(ringPresheaf O).obj (op X)] F.obj (op X)) :
    tensorFiberCompareInv A F (tensorFiberCompare A F (tensorObjGerm A F X u τ)) =
      tensorObjGerm A F X u τ := by
  induction τ using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero, map_zero]
  | tmul a s =>
    rw [tensorFiberCompare_germ_tmul, tensorFiberCompareInv_tmul, tensorFiberBack_germ]
  | add τ τ' h h' => rw [map_add, map_add, map_add, h, h']

/-- `Stacks.tensorFiberCompareInv` is a left inverse of `Stacks.tensorFiberCompare`. -/
lemma tensorFiberCompareInv_compare (z : moduleFiber Φ O (tensorObj A F)) :
    tensorFiberCompareInv A F (tensorFiberCompare A F z) = z := by
  obtain ⟨X, u, τ, rfl⟩ := moduleFiberGerm_jointly_surjective (M := tensorObj A F) z
  exact tensorFiberCompareInv_compare_germ A F X u τ

/-- `Stacks.tensorFiberCompareInv` is a right inverse of `Stacks.tensorFiberCompare`. -/
lemma tensorFiberCompare_compareInv
    (z : moduleFiber Φ O A ⊗[commRingFiber Φ O] moduleFiber Φ O F) :
    tensorFiberCompare A F (tensorFiberCompareInv A F z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | tmul x y =>
    obtain ⟨⟨@⟨X, u⟩, a, s⟩, rfl, rfl⟩ := exists_tensorFiberRep A F x y
    rw [tensorFiberCompareInv_tmul, tensorFiberBack_germ, tensorFiberCompare_germ_tmul]
  | add z z' h h' => rw [map_add, map_add, h, h']

/-! ### The comparison is linear and natural -/

/-- `Stacks.tensorFiberCompare` is compatible with the action of sections of `O` on germs. -/
lemma tensorFiberCompare_smul_germ (X : C) (u : Φ.fiber.obj X)
    (r : (ringPresheaf O).obj (op X))
    (τ : A.obj (op X) ⊗[(ringPresheaf O).obj (op X)] F.obj (op X)) :
    tensorFiberCompare A F (tensorObjGerm A F X u (r • τ)) =
      ringFiberGerm Φ O X u r • tensorFiberCompare A F (tensorObjGerm A F X u τ) := by
  induction τ using TensorProduct.induction_on with
  | zero => simp only [smul_zero, map_zero]
  | tmul a s =>
    rw [TensorProduct.smul_tmul', tensorFiberCompare_germ_tmul, tensorFiberCompare_germ_tmul,
      moduleFiberGerm_smul]
    exact (TensorProduct.smul_tmul' _ _ _).symm
  | add τ τ' h h' => simp only [smul_add, map_add, h, h']

/-- `Stacks.tensorFiberCompare` is linear over the stalk of `O`. -/
lemma tensorFiberCompare_smul (c : commRingFiber Φ O) (z : moduleFiber Φ O (tensorObj A F)) :
    tensorFiberCompare A F (c • z) = c • tensorFiberCompare A F z := by
  obtain ⟨X, u, a, -, r, ha, -, hr⟩ := exists_germ_families (tensorObj A F) F
    (fun _ : Fin 1 => z) (fun i : Fin 0 => i.elim0) (fun _ : Fin 1 => c)
  have hz : moduleFiberGerm Φ O (tensorObj A F) X u (a 0) = z := ha 0
  have hc : ringFiberGerm Φ O X u (r 0) = c := hr 0
  clear ha hr
  subst hz hc
  rw [← moduleFiberGerm_smul]
  exact tensorFiberCompare_smul_germ A F X u (r 0) (a 0)

/-- **The tensor–stalk comparison for a site.** The stalk at a point `Φ` of a site of the
objectwise tensor product of two presheaves of modules is the tensor product of the stalks,
over the stalk of the structure presheaf:
`(A ⊗_O F)_Φ ≅ A_Φ ⊗_{O_Φ} F_Φ`.

This is the specialisation to the morphism of ringed topoi given by `Φ` of Stacks 03EL, and it
is the identification that the converse half of Stacks 05VC is proved from. It is stated here
for *presheaves* of modules; sheaves are reduced to this case by
`Stacks.isIso_presheafModuleFiber_map_sheafificationAdjunction_unit`, since the stalk does not
see sheafification. -/
noncomputable def tensorFiberAddEquiv :
    moduleFiber Φ O (tensorObj A F) ≃+
      (moduleFiber Φ O A ⊗[commRingFiber Φ O] moduleFiber Φ O F) where
  toFun := tensorFiberCompare A F
  invFun := tensorFiberCompareInv A F
  left_inv := tensorFiberCompareInv_compare A F
  right_inv := tensorFiberCompare_compareInv A F
  map_add' x y := map_add (tensorFiberCompare A F) x y

/-- `Stacks.tensorFiberAddEquiv` as a linear equivalence over the stalk of `O`. -/
noncomputable def tensorFiberLinearEquiv :
    moduleFiber Φ O (tensorObj A F) ≃ₗ[commRingFiber Φ O]
      (moduleFiber Φ O A ⊗[commRingFiber Φ O] moduleFiber Φ O F) :=
  (tensorFiberAddEquiv A F).toLinearEquiv (tensorFiberCompare_smul A F)

/-- `Stacks.tensorFiberCompare` is injective. -/
lemma tensorFiberCompare_injective :
    Function.Injective (tensorFiberCompare (Φ := Φ) A F) := fun z z' h => by
  rw [← tensorFiberCompareInv_compare A F z, h, tensorFiberCompareInv_compare A F z']

/-- The stalk functor on a morphism of presheaves of modules, as a linear map over the stalk of
the structure presheaf. -/
noncomputable def moduleFiberMap {M M' : PresheafOfModules.{w} (ringPresheaf O)} (g : M ⟶ M') :
    moduleFiber Φ O M →ₗ[commRingFiber Φ O] moduleFiber Φ O M' :=
  ((ModuleCat.restrictScalars (commRingPresheafFiberIso Φ O).inv.hom).map
    ((presheafModuleFiber Φ (ringPresheaf O)).map g)).hom

/-- `Stacks.moduleFiberMap g` sends the germ of `m` to the germ of `g.app (op U) m`. -/
lemma moduleFiberMap_germ {M M' : PresheafOfModules.{w} (ringPresheaf O)} (g : M ⟶ M') (U : C)
    (x : Φ.fiber.obj U) (m : M.obj (op U)) :
    moduleFiberMap g (moduleFiberGerm Φ O M U x m) =
      moduleFiberGerm Φ O M' U x (g.app (op U) m) :=
  moduleFiberGerm_naturality g U x m

/-- **Functoriality of the tensor–stalk comparison.** -/
lemma tensorFiberCompare_naturality_germ {A' : PresheafOfModules.{w} (ringPresheaf O)}
    (g : A ⟶ A') (X : C) (u : Φ.fiber.obj X)
    (τ : A.obj (op X) ⊗[(ringPresheaf O).obj (op X)] F.obj (op X)) :
    tensorFiberCompare A' F (moduleFiberMap ((tensorRight F).map g) (tensorObjGerm A F X u τ)) =
      LinearMap.rTensor (moduleFiber Φ O F) (moduleFiberMap g)
        (tensorFiberCompare A F (tensorObjGerm A F X u τ)) := by
  induction τ using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul a s =>
    have h1 : moduleFiberMap ((tensorRight F).map g)
          (tensorObjGerm A F X u (a ⊗ₜ[(ringPresheaf O).obj (op X)] s)) =
        tensorObjGerm A' F X u (g.app (op X) a ⊗ₜ[(ringPresheaf O).obj (op X)] s) :=
      (moduleFiberMap_germ ((tensorRight F).map g) X u _).trans
        (congrArg (tensorObjGerm A' F X u) (tensorRight_map_app_tmul F g (op X) a s))
    rw [h1, tensorFiberCompare_germ_tmul, tensorFiberCompare_germ_tmul,
      LinearMap.rTensor_tmul, moduleFiberMap_germ]
  | add τ τ' h h' => simp only [map_add, h, h']

/-- `Stacks.tensorFiberCompare` is natural in the first factor: it intertwines the stalk map of
`(tensorRight F).map g` with `LinearMap.rTensor` of the stalk map of `g`. -/
lemma tensorFiberCompare_naturality {A' : PresheafOfModules.{w} (ringPresheaf O)} (g : A ⟶ A')
    (z : moduleFiber Φ O (tensorObj A F)) :
    tensorFiberCompare A' F (moduleFiberMap ((tensorRight F).map g) z) =
      LinearMap.rTensor (moduleFiber Φ O F) (moduleFiberMap g) (tensorFiberCompare A F z) := by
  obtain ⟨X, u, τ, rfl⟩ := moduleFiberGerm_jointly_surjective (M := tensorObj A F) z
  exact tensorFiberCompare_naturality_germ A F g X u τ

/-- **The stalkwise criterion for the tensor functor to preserve a monomorphism.** If the stalk
of `F` at `Φ` is a flat module over the stalk of `O`, then tensoring with `F` keeps a
sectionwise-injective morphism injective on stalks. -/
lemma injective_moduleFiberMap_tensorRight_map
    {A' : PresheafOfModules.{w} (ringPresheaf O)} (g : A ⟶ A')
    (hg : Function.Injective (moduleFiberMap (Φ := Φ) (O := O) g))
    (hF : Module.Flat (commRingFiber Φ O) (moduleFiber Φ O F)) :
    Function.Injective (moduleFiberMap (Φ := Φ) (O := O) ((tensorRight F).map g)) := by
  intro z z' h
  refine tensorFiberCompare_injective A F ?_
  refine Module.Flat.rTensor_preserves_injective_linearMap (M := moduleFiber Φ O F)
    (moduleFiberMap (Φ := Φ) (O := O) g) hg ?_
  rw [← tensorFiberCompare_naturality A F g, ← tensorFiberCompare_naturality A F g]
  exact congrArg (tensorFiberCompare A' F) h

end Compare

/-! ### The converse half of Stacks 05VC -/

section Sheaf

variable [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify J AddCommGrpCat.{w}]
  (O : Sheaf J CommRingCat.{w})

omit [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify J AddCommGrpCat.{w}] in
/-- The stalk of a sheaf of modules over the `CommRingCat`-valued stalk, as computed by
`Stacks.moduleFiber`, is the stalk module `Stacks.moduleStalk` of Stacks 05VB and 05VC. -/
lemma moduleFiber_val (Φ : J.Point.{w}) (M : SheafOfModules.{w} (commRingSheafToRingSheaf O)) :
    moduleFiber Φ O.obj M.val = moduleStalk Φ O M :=
  rfl

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify J AddCommGrpCat.{w}] in
/-- Monomorphy of the stalk map, as injectivity of `Stacks.moduleFiberMap`. -/
lemma mono_iff_injective_moduleFiberMap (Φ : J.Point.{w})
    {M M' : PresheafOfModules.{w} (ringPresheaf O.obj)} (g : M ⟶ M') :
    Mono ((presheafModuleFiber Φ (ringPresheaf O.obj)).map g) ↔
      Function.Injective (moduleFiberMap (Φ := Φ) (O := O.obj) g) :=
  ModuleCat.mono_iff_injective _

variable (F : SheafOfModules.{w} (commRingSheafToRingSheaf O))

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- **Monomorphy of a stalk map is not changed by sheafification.** The stalk functor inverts
the sheafification unit, so a morphism of presheaves of modules whose stalk map is a
monomorphism has the same property after sheafification. -/
lemma mono_presheafModuleFiber_map_sheafification (Φ : J.Point.{w}) (R : Sheaf J RingCat.{w})
    {M N : PresheafOfModules.{w} R.obj} (ψ : M ⟶ N)
    (h : Mono ((presheafModuleFiber Φ R.obj).map ψ)) :
    Mono ((presheafModuleFiber Φ R.obj).map
      ((PresheafOfModules.sheafification (R := R) (𝟙 R.obj) ⋙
        SheafOfModules.forget R ⋙ PresheafOfModules.restrictScalars (𝟙 R.obj)).map ψ)) := by
  have h₁ := isIso_presheafModuleFiber_map_sheafificationAdjunction_unit Φ R M
  have h₂ := isIso_presheafModuleFiber_map_sheafificationAdjunction_unit Φ R N
  have h' : Mono ((presheafModuleFiber Φ R.obj).map
    ((𝟭 (PresheafOfModules.{w} R.obj)).map ψ)) := h
  refine ((MorphismProperty.monomorphisms _).cancel_left_of_respectsIso
    ((presheafModuleFiber Φ R.obj).map
      ((PresheafOfModules.sheafificationAdjunction (R := R) (𝟙 R.obj)).unit.app M)) _).1 ?_
  rw [← CategoryTheory.Functor.map_comp,
    ← (PresheafOfModules.sheafificationAdjunction (R := R) (𝟙 R.obj)).unit.naturality ψ,
    CategoryTheory.Functor.map_comp]
  exact mono_comp _ _

/-- Tensoring with `F` keeps a monomorphism of sheaves of modules a monomorphism on the stalk
at a point where the stalk of `F` is flat. This is the content of the converse half of
Stacks 05VC at a single point: the tensor–stalk comparison turns the question into flatness of
the stalk module, and the stalk does not see the sheafification in the definition of the tensor
product of sheaves of modules. -/
lemma mono_sheafModuleFiber_map_sheafTensorRight_map (Φ : J.Point.{w})
    (hF : IsFlatModuleStalk Φ O F)
    {M N : SheafOfModules.{w} (commRingSheafToRingSheaf O)} (f : M ⟶ N) [Mono f] :
    Mono ((sheafModuleFiber Φ (commRingSheafToRingSheaf O)).map
      (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} O).flip.obj F).map f)) := by
  have hflat : Module.Flat (commRingFiber Φ O.obj) (moduleFiber Φ O.obj F.val) := hF
  -- the stalk map of the *presheaf*-level tensor map is a monomorphism, by flatness
  have hinj : Function.Injective (moduleFiberMap (Φ := Φ) (O := O.obj)
      ((SheafOfModules.forget (commRingSheafToRingSheaf O)).map f)) :=
    (mono_iff_injective_moduleFiberMap O Φ
      ((SheafOfModules.forget (commRingSheafToRingSheaf O)).map f)).1
      (inferInstanceAs (Mono ((sheafModuleFiber Φ (commRingSheafToRingSheaf O)).map f)))
  have hmono : Mono ((presheafModuleFiber Φ (ringPresheaf O.obj)).map
      ((tensorRight F.val).map
        ((SheafOfModules.forget (commRingSheafToRingSheaf O)).map f))) :=
    (mono_iff_injective_moduleFiberMap O Φ _).2
      (injective_moduleFiberMap_tensorRight_map _ F.val _ hinj hflat)
  -- the sheaf-level tensor map is the sheafification of the presheaf-level one
  have hbridge : (sheafModuleFiber Φ (commRingSheafToRingSheaf O)).map
        (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} O).flip.obj F).map f) =
      (presheafModuleFiber Φ (ringPresheaf O.obj)).map
        ((PresheafOfModules.sheafification (R := commRingSheafToRingSheaf O)
            (𝟙 (commRingSheafToRingSheaf O).obj) ⋙
          SheafOfModules.forget (commRingSheafToRingSheaf O) ⋙
            PresheafOfModules.restrictScalars (𝟙 (commRingSheafToRingSheaf O).obj)).map
          ((tensorRight F.val).map
            ((SheafOfModules.forget (commRingSheafToRingSheaf O)).map f))) :=
    rfl
  rw [hbridge]
  exact mono_presheafModuleFiber_map_sheafification Φ (commRingSheafToRingSheaf O) _ hmono

/-- **The converse half of Stacks 05VC.** A sheaf of modules whose stalks at a conservative
family of points are flat modules over the stalks of the structure sheaf is flat. -/
theorem isFlat_of_forall_isFlatModuleStalk {t : Type*} (p : t → J.Point.{w})
    (hp : (ObjectProperty.ofObj p).IsConservativeFamilyOfPoints)
    (h : ∀ i, IsFlatModuleStalk (p i) O F) :
    SheafOfModules.IsFlat F := by
  refine SheafOfModules.isFlat_of_mono_sheafTensorRight_map O F (fun S hS => ?_)
  have : Mono (C := SheafOfModules.{w} (commRingSheafToRingSheaf O)) S.f := hS.mono_f
  refine mono_of_mono_sheafModuleFiber (commRingSheafToRingSheaf O) hp _ (fun Φ => ?_)
  obtain ⟨i, hi⟩ := (ObjectProperty.ofObj_iff p Φ.obj).1 Φ.property
  exact mono_sheafModuleFiber_map_sheafTensorRight_map O F Φ.obj (hi ▸ h i) S.f

/-- **Stacks 05VC.** A sheaf of modules on a ringed site is flat if and only if its stalk at
every point of a conservative family of points is a flat module over the stalk of the
structure sheaf. -/
@[sga "4 V 1.6" "special case"]
theorem isFlat_iff_forall_isFlatModuleStalk {t : Type*} (p : t → J.Point.{w})
    (hp : (ObjectProperty.ofObj p).IsConservativeFamilyOfPoints) :
    SheafOfModules.IsFlat F ↔ ∀ i, IsFlatModuleStalk (p i) O F :=
  ⟨fun hFlat i => isFlatModuleStalk_of_hasLocalSingleRelationFactorizations (p i) O F
    (SheafOfModules.hasLocalSingleRelationFactorizations_of_isFlat_freeUniverse hFlat),
   isFlat_of_forall_isFlatModuleStalk O F p hp⟩

end Sheaf

end Stacks
