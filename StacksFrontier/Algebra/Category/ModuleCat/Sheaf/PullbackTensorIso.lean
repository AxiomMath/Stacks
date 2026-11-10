module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafificationTensor

public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.CategoryTheory.Monoidal.FunctorCategory
public import Mathlib.CategoryTheory.Monoidal.Limits.Colimits
public import Mathlib.CategoryTheory.Filtered.Final
public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.PullbackColimit
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackTensorComparison
public import StacksCore.Tactic.StacksAttribute

/-!
# The pullback of presheaves of modules commutes with the objectwise tensor product

Let `F : C ⥤ D` be a functor between small categories, `α : S ⟶ F.op ⋙ R` a morphism of
presheaves of commutative rings, and `M`, `N` presheaves of `S`-modules.  This file proves

`pullback α (M ⊗_S N) ≅ pullback α M ⊗_R pullback α N`,

naturally in `M` and `N`, for `PresheafOfModules.pullback` and the objectwise tensor product
`PresheafOfModules.tensorObj`, under the hypothesis `RepresentablyFlat F` that makes the index
category of the colimit computing the pullback filtered.  This is the presheaf-level half of
Stacks 01CD, and the two steps that
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackTensorComparison` lists as missing for
Tag 01CD itself.  Combined with Tag 0GMW and with Mathlib's comparison of the sheaf-level and
presheaf-level pullbacks, it yields `pullbackTensorSheafObjIso`,
`f^*(A ⊗_{𝒪_Y} B) ≅ f^*A ⊗_{𝒪_X} f^*B` for a morphism of ringed spaces.  **Tag 01CD is still
not proved**: that isomorphism is not yet identified with the canonical comparison morphism.
See the final section of this docstring for exactly what is owed.

The proof uses the concrete model of the pullback built in
`StacksFrontier.Algebra.Category.ModuleCat.Presheaf.PullbackColimit`,

`pullback α ≅ extendScalars α ⋙ colimitPullback F R`,

and treats its two factors separately.

* Extension of scalars: objectwise, `(R'(V) ⊗_{R(V)} -)` distributes over the tensor product,
  which is `TensorProduct.AlgebraTensorModule.distribBaseChange` in Mathlib.
* The colimit: the diagram whose colimit is the pullback of `M ⊗ N` is objectwise the tensor
  product of the two diagrams, and a tensor product of *filtered* colimits is the colimit of
  the pointwise tensor product, because the diagonal of a filtered category is final
  (`CategoryTheory.Functor.final_diag_of_isFiltered`) and `ModuleCat` is monoidal closed, so
  tensoring preserves colimits in each variable.

## Main definitions

* `Stacks.PullbackTensor.extendScalarsTensorIso`: base change distributes over the tensor
  product, `B ⊗_A (M ⊗_A N) ≅ (B ⊗_A M) ⊗_B (B ⊗_A N)`, as an isomorphism of `ModuleCat B`
  objects between `ModuleCat.extendScalars`-images.
* `Stacks.PullbackTensor.germTmul` and `Stacks.PullbackTensor.tmulGerm`: the germ of the pure
  tensor `r ⊗ (a ⊗ b)` in the colimit computing the pullback of `A ⊗ B`, and the pure tensor of
  the germs of `r ⊗ a` and `1 ⊗ b` in the tensor product of the two pullbacks.  These are the
  two elements the isomorphism matches, and they are definitions rather than notation for the
  reason given in the implementation notes.
* `Stacks.PullbackTensor.diagramTensorIso`: the diagram computing the pullback of `A ⊗ B` is the
  tensor product, in the functor category, of the two diagrams.
* `Stacks.PullbackTensor.tensorCocone` and `Stacks.PullbackTensor.isColimit_tensorCocone`: the
  tensor product of the two colimit cocones, and the proof that it is a colimit cocone.
* `Stacks.PullbackTensor.modelPullbackTensorObjIso`: the two steps composed, for the concrete
  model `extendScalars α ⋙ colimitPullback F R`.

## Main results

* `Stacks.PullbackTensor.extendScalarsTensorObjIso` and
  `Stacks.PullbackTensor.extendScalarsTensorIsoBifunctor`: **extension of scalars commutes with
  the objectwise tensor product** of presheaves of modules, objectwise and as an isomorphism of
  bifunctors; `extendScalarsTensorObjIso_hom_tmul` and `extendScalarsTensorObjIso_inv_tmul`
  compute both directions on pure tensors.
* `Stacks.PullbackTensor.colimitTensorIso`, `Stacks.PullbackTensor.objTensorIso` and
  `Stacks.PullbackTensor.colimitPullbackTensorIso`: **the objectwise tensor product commutes
  with the filtered colimit computing the pullback**, on sections, on objects and as an
  isomorphism of bifunctors.  `colimitTensorIso_hom_germTmul` and `objTensorIso_hom_germTmul`
  compute it: the germ of `r ⊗ (a ⊗ b)` goes to the tensor of the germ of `r ⊗ a` and the germ
  of `1 ⊗ b`.
* `Stacks.PullbackTensor.modelPullbackTensorIso` and
  `Stacks.PullbackTensor.pullbackTensorIso`: **the pullback of presheaves of modules commutes
  with the objectwise tensor product**, as an isomorphism of bifunctors, for the concrete model
  and for Mathlib's `PresheafOfModules.pullback`.
* `Stacks.PullbackTensor.pullbackTensorSheafObjIso`: **the pullback of sheaves of modules on a
  ringed space commutes with the tensor product**, `f^*(A ⊗ B) ≅ f^*A ⊗ f^*B`.  This has the
  type of Stacks 01CD but is not yet known to be the canonical comparison; see below.
* `Stacks.PullbackTensor.sheafificationTensorObjIso`: Tag 0GMW on a ringed space, obtained from
  `PresheafOfModules.sheafificationTensorIso` by transporting along
  `Stacks.PullbackTensor.moduleSheafification_id_eq`.
* `Stacks.PullbackTensor.colimitPullback_map_germ_one`: the functoriality of the colimit
  pullback in the module argument, computed on germs.  `colimitPullback F R` is produced by
  `CategoryTheory.Adjunction.leftAdjointOfEquiv`, so this is the only description of its action
  on morphisms available.

## Implementation notes

Two spelling difficulties recur and both are handled by fixing one spelling in a definition,
never by a transparency option.

The first is the one `PullbackModel` and `PullbackColimit` describe: `(ModuleCat.extendScalars
f).obj M` has underlying type `B ⊗[A] M` only for the `Module A B` structure that
`ModuleCat.restrictScalars f` installs.  Every statement about it here is phrased through
`Stacks.PullbackModel.tmul`.  The one place where Mathlib's own `Algebra`-based spelling is
needed is `extendScalarsTensorIso`, which installs `RingHom.toAlgebra` with a `letI` so that
`TensorProduct.AlgebraTensorModule.distribBaseChange` applies; the resulting map is then
*never* rewritten with a `TensorProduct` lemma — its action on pure tensors is recorded once, in
the `tmul` spelling, by `extendScalarsTensorIso_hom_tmul` (which is `rfl`) and
`extendScalarsTensorIso_inv_tmul`.

The second is that a pure tensor `a ⊗ₜ b` of sections has type `A(V) ⊗ B(V)`, which is only
definitionally and not syntactically `(tensorObj A B)(V)`, so a rewrite rule whose left-hand
side mentions `germ F R (tensorObj A B) T r (a ⊗ₜ b)` cannot be applied by `rw`: building the
motive requires checking that assignment at `implicit` transparency, which fails.  `germTmul`
and `tmulGerm` give the two sides a single head symbol, and `germTmul_restrict`,
`tmulGerm_restrict`, `colimitPullback_map_germTmul`, `tensorHom_tmulGerm`,
`colimitTensorIso_hom_germTmul` are then ordinary rewrite rules, which is how the naturality of
`objTensorIso` and of `colimitPullbackTensorIso` is proved.

For the same reason `colimitPullback_map_germ_one` fixes the first tensor factor to `1`: the
germ lives in `colimit (diagram F R A U)`, a `ModuleCat ↑(R.obj U)` whose ring carries the
`CommRingCat`-derived `Ring` instance, whereas the sections of `colimitPullback F R` are a
`ModuleCat ↑((R ⋙ forget₂ CommRingCat RingCat).obj U)` whose ring carries the `RingCat` one, and
a statement mentioning `•` fixes the wrong one of the two definitionally equal `Module`
structures.  Germ extensionality only ever needs the value at `1`, so nothing is lost.

On a ringed space, the two sheafification functors that have to be matched are spelled
differently: `PresheafOfModules.moduleSheafification J a`, which Tag 0GMW is stated for, is
sheafification along `toRingCatMap J a = Functor.whiskerRight a (forget₂ CommRingCat RingCat)`,
while `Stacks.SheafOfModules.Tensor.sheafTensor`, `SheafOfModules.pullbackIso` and
`SheafOfModules.sheafificationCompPullback` are stated for `𝟙 (toRingCat J Osharp).obj`.  For
`a = 𝟙` these agree by `Functor.map_id`, which is not a definitional equality, so
`moduleSheafification_id_eq` transports between them; `sheafificationTensorObjIso` is the one
place where that transport is used.

`RepresentablyFlat F` is the hypothesis, not `∀ U, IsFiltered (CostructuredArrow F.op U)`,
because it is Mathlib's spelling and because it is what
`Stacks.PullbackModel.representablyFlat_opensMap` proves for `Opens.map f`, which is the case
Stacks 01CD needs.  It is genuinely needed: a tensor product of colimits over a non-sifted index
category is not the colimit of the pointwise tensor product.

**`CategoryTheory.IsFiltered.isSifted` is a `local` instance here, and must stay local.**  The
step above needs the index category sifted, and Mathlib proves exactly that — but as a
*theorem*, with the comment "adding this instance causes performance problems elsewhere, even
with low priority", and for the same reason Mathlib makes `CategoryTheory.IsSifted.nonempty` a
*scoped* instance ("it applies unconditionally, infers a very generic typeclass, and does so
from a very specialised class").  Composing the two globally is worse than either: every
`Nonempty J` goal for a filtered `J` is then solved through
`IsSifted.nonempty ← isSifted ← IsFiltered.of_hasTerminal ← …` instead of through the
one-step `instNonemptyOfInhabited`, which inflates the *size* of every solution containing it.
When this file exported such an instance globally, the solution for
`HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}` grew by that whole chain, so the
composite goal `Abelian (SheafOfModules.{u} (structureSheaf Rc))` — which has that as a subgoal
— overran the default `synthInstance.maxSize` of 128 and failed outright, while each of its
subgoals still succeeded in isolation and applying `SheafOfModules.instAbelian` by name still
worked.  The symptom therefore looked like a missing instance and was neither: raising
`synthInstance.maxHeartbeats` did not help and raising `synthInstance.maxSize` did.  It made the
derived category of modules on a ringed space unspellable in any file importing this one
together with `StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.LeftDualOnARingedSpace`.

Universes are not narrowed relative to `PullbackColimit`: everything is stated for
`C D : Type u` with `[SmallCategory C] [SmallCategory D]`, presheaves of `CommRingCat.{w}`
and `PresheafOfModules.{w}` with `w` free, so the rings and the module sections may live
in any universe at least as large as the sites'.  The three constraints behind that shape — the
module universe at least the site universe, the ring universe equal to the module universe, and
the two sites in one universe — are the ones `PullbackColimit` records, and each is explained
there.  `CommRingCat` rather than `RingCat` is forced by `ModuleCat.extendScalars`.  The
extension-of-scalars section is stated for an arbitrary `C : Type u₁` with `[Category.{v₁} C]`,
since no colimit is involved there.

## What remains for Tag 01CD

Tag 01CD is invertibility of `Stacks.RingedSpace.comparison`:
`f^*(A ⊗_{𝒪_Y} B) ⟶ f^*A ⊗_{𝒪_X} f^*B` for a morphism of ringed spaces, whose construction,
pure-tensor characterisation and uniqueness (`Stacks.RingedSpace.comparison_unique`) are proved
in `StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackTensorComparison`.

`Stacks.PullbackTensor.pullbackTensorSheafObjIso` is an isomorphism of exactly that type.  It is
the composite of four links:

1. `SheafOfModules.sheafificationCompPullback` (Mathlib,
   `Mathlib/Algebra/Category/ModuleCat/Sheaf/PullbackContinuous.lean`): the sheaf-level pullback
   of a sheafification is the sheafification of the presheaf-level pullback.  Since
   `Stacks.SheafOfModules.Tensor.sheafTensor` *is* `tensorBifunctor` followed by sheafification,
   this rewrites `f^*(A ⊗ B)` as the sheafification of `pullback (A.val ⊗ B.val)`.
2. `Stacks.PullbackTensor.pullbackTensorIso` (this file): that is the sheafification of
   `pullback A.val ⊗ pullback B.val`.
3. `Stacks.PullbackTensor.sheafificationTensorObjIso`, which is Tag 0GMW
   (`PresheafOfModules.sheafificationTensorIso`, proved in
   `StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafificationTensor`) transported along
   `moduleSheafification_id_eq`: that is the tensor product of the sheafifications.
4. `SheafOfModules.pullbackIso` (Mathlib, same file as 1): each of those sheafifications is
   `f^*A`, resp. `f^*B`.

**Tag 01CD is closed.**  What this paragraph used to call still owed — identifying the
isomorphism below with the canonical `Stacks.RingedSpace.comparison` — is proved in
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackTensorCanonical`.  The tag sits on
`Stacks.RingedSpace.comparisonBifunctorIso`, in
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackTensorComparisonIso`, which is
`Stacks.RingedSpace.comparisonIso` with its invertibility hypothesis discharged.

Nothing in THIS file carries the `@[stacks 01CD]` attribute, which remains correct for the
original reason: an isomorphism of the right type is not Tag 01CD unless it is *the* canonical
comparison, and `comparison_unique` exists precisely so that this cannot be fudged.

## References

* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
* [Stacks Project, Tag 0GMW](https://stacks.math.columbia.edu/tag/0GMW)
-/

@[expose] public section

open CategoryTheory Limits Opposite TopologicalSpace
open scoped TensorProduct ChangeOfRings

universe w u u₁ v₁

namespace Stacks.PullbackTensor

open PresheafOfModules Stacks.PullbackModel

-- A filtered category is sifted: `CategoryTheory.IsFiltered.isSifted`.  Mathlib keeps it a
-- theorem rather than an instance on purpose, so it is activated here for this file only.
attribute [local instance] CategoryTheory.IsFiltered.isSifted

section Algebra

variable {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B)

/-- Base change distributes over the tensor product. -/
noncomputable def extendScalarsTensorIso (M N : ModuleCat.{u} A) :
    (ModuleCat.extendScalars f).obj (ModuleCat.of A (M ⊗[A] N)) ≅
      ModuleCat.of B ((ModuleCat.extendScalars f).obj M ⊗[B]
        (ModuleCat.extendScalars f).obj N) :=
  letI : Algebra A B := f.toAlgebra
  (TensorProduct.AlgebraTensorModule.distribBaseChange A B M N).toModuleIso

/-- The isomorphism `extendScalarsTensorIso` sends `b ⊗ (m ⊗ n)` to `(b ⊗ m) ⊗ (1 ⊗ n)`. -/
lemma extendScalarsTensorIso_hom_tmul (M N : ModuleCat.{u} A) (b : B) (m : M) (n : N) :
    (extendScalarsTensorIso f M N).hom (tmul f b (m ⊗ₜ[A] n))
      = tmul f b m ⊗ₜ[B] tmul f 1 n := rfl

/-- The inverse of `extendScalarsTensorIso` sends `(b ⊗ m) ⊗ (b' ⊗ n)` to `bb' ⊗ (m ⊗ n)`. -/
lemma extendScalarsTensorIso_inv_tmul (M N : ModuleCat.{u} A) (b b' : B) (m : M) (n : N) :
    (extendScalarsTensorIso f M N).inv (tmul f b m ⊗ₜ[B] tmul f b' n)
      = tmul f (b * b') (m ⊗ₜ[A] n) := by
  let _ : Algebra A B := f.toAlgebra
  exact TensorProduct.AlgebraTensorModule.distribBaseChange_symm_tmul A B m n b b'

/-- Two maps out of the base change of a tensor product agree as soon as they agree on the
pure tensors `1 ⊗ (m ⊗ n)`. -/
lemma extendScalars_tensor_hom_ext {M N : ModuleCat.{u} A} {P : ModuleCat.{u} B}
    {x y : (ModuleCat.extendScalars f).obj (ModuleCat.of A (M ⊗[A] N)) ⟶ P}
    (h : ∀ (m : M) (n : N), x (tmul f 1 (m ⊗ₜ[A] n)) = y (tmul f 1 (m ⊗ₜ[A] n))) : x = y := by
  refine ((ModuleCat.extendRestrictScalarsAdj f).homEquiv _ P).injective
    (ModuleCat.tensor_ext fun m n => ?_)
  rw [homEquiv_apply_tmul, homEquiv_apply_tmul]
  exact h m n

end Algebra

section Presheaf

variable {C : Type u₁} [Category.{v₁} C] {R R' : Cᵒᵖ ⥤ CommRingCat.{u}} (α : R ⟶ R')
  (M N : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat))

/-- **Extension of scalars commutes with the objectwise tensor product** of presheaves of
modules. -/
noncomputable def extendScalarsTensorObjIso :
    (extendScalars α).obj (tensorObj M N) ≅
      tensorObj ((extendScalars α).obj M) ((extendScalars α).obj N) :=
  PresheafOfModules.isoMk
    (fun V => extendScalarsTensorIso (α.app V).hom (M.obj V) (N.obj V))
    (fun {V W} g => by
      refine extendScalars_tensor_hom_ext (α.app V).hom fun m n => ?_
      change tmul (α.app W).hom ((R'.map g).hom 1) (M.restrictₛₗ g m) ⊗ₜ
            tmul (α.app W).hom 1 (N.restrictₛₗ g n)
          = tmul (α.app W).hom ((R'.map g).hom 1) (M.restrictₛₗ g m) ⊗ₜ
            tmul (α.app W).hom ((R'.map g).hom 1) (N.restrictₛₗ g n)
      rw [map_one])

/-- On sections over `V`, the isomorphism `extendScalarsTensorObjIso` sends `b ⊗ (m ⊗ n)` to
`(b ⊗ m) ⊗ (1 ⊗ n)`. -/
lemma extendScalarsTensorObjIso_hom_tmul (V : Cᵒᵖ) (b : R'.obj V) (m : M.obj V) (n : N.obj V) :
    Hom.app (extendScalarsTensorObjIso α M N).hom V (tmul (α.app V).hom b (m ⊗ₜ n))
      = tmul (α.app V).hom b m ⊗ₜ tmul (α.app V).hom 1 n := rfl

/-- On sections over `V`, the inverse of `extendScalarsTensorObjIso` sends `(b ⊗ m) ⊗ (b' ⊗ n)` to
`bb' ⊗ (m ⊗ n)`. -/
lemma extendScalarsTensorObjIso_inv_tmul (V : Cᵒᵖ) (b b' : R'.obj V) (m : M.obj V)
    (n : N.obj V) :
    Hom.app (extendScalarsTensorObjIso α M N).inv V
        (tmul (α.app V).hom b m ⊗ₜ tmul (α.app V).hom b' n)
      = tmul (α.app V).hom (b * b') (m ⊗ₜ n) :=
  extendScalarsTensorIso_inv_tmul (α.app V).hom (M.obj V) (N.obj V) b b' m n

variable (R R') in
/-- **Extension of scalars commutes with the objectwise tensor product**, as an isomorphism of
bifunctors: naturality in both presheaves of modules is part of the statement. -/
noncomputable def extendScalarsTensorIsoBifunctor :
    (Functor.uncurry.obj (PresheafOfModules.tensorBifunctor.{v₁, u₁, u, u, u} R)) ⋙ extendScalars α
        ≅
      Functor.prod (extendScalars α) (extendScalars α) ⋙ (Functor.uncurry.obj
          (PresheafOfModules.tensorBifunctor.{v₁, u₁, u, u, u} R')) :=
  NatIso.ofComponents (fun P => extendScalarsTensorObjIso α P.1 P.2)
    (fun _ => PresheafOfModules.hom_ext fun V =>
      extendScalars_tensor_hom_ext (α.app V).hom fun _ _ => rfl)

end Presheaf

section Colimit

open Stacks.PullbackColimit
open scoped MonoidalCategory

variable {C D : Type u} [SmallCategory C] [SmallCategory D]
  (F : C ⥤ D) (R : Dᵒᵖ ⥤ CommRingCat.{w})
  (A B : PresheafOfModules.{w} ((F.op ⋙ R) ⋙ forget₂ CommRingCat RingCat))
  [hUL : UnivLE.{u, w}]

include hUL

section Map

variable {A B}

/-- The functoriality of `L₀` in the module argument, on germs with first factor `1`.
`colimitPullback F R` is produced by `Adjunction.leftAdjointOfEquiv`, so its action on morphisms
is the inverse adjoint transpose of `ψ`; this unwinds that description.  The first factor is
fixed to `1` because `germ`, whose scalars are spelled through `R.obj U` as a `CommRingCat`,
and the sections of `colimitPullback F R`, whose scalars are spelled through
`(R ⋙ forget₂ CommRingCat RingCat).obj U` as a `RingCat`, carry two definitionally equal but
syntactically different `Module` structures, and a statement mentioning `•` would fix the wrong
one.  Germ extensionality (`germ_tensor_hom_ext`, `PullbackColimit.hom_ext`) only ever needs the
value at `1`. -/
lemma colimitPullback_map_germ_one (ψ : A ⟶ B) {U : Dᵒᵖ} (T : CostructuredArrow F.op U)
    (a : A.obj T.left) :
    Hom.app ((colimitPullback F R).map ψ) U (germ F R A T 1 a)
      = germ F R B T 1 (Hom.app ψ T.left a) := by
  change descMap F R (ψ ≫ homEquiv F R B (obj F R B) (𝟙 _)) U (germ F R A T 1 a) = _
  rw [descMap_germ]
  change (obj F R B).map T.hom (PullbackColimit.unit F R B T.left (Hom.app ψ T.left a)) = _
  rw [PullbackColimit.unit, obj_map_germ, map_one]
  exact germ_congr F R B (Category.id_comp T.hom) 1 (Hom.app ψ T.left a)

end Map

/-- The germ of the pure tensor `r ⊗ (a ⊗ b)` in the colimit computing the pullback of an
objectwise tensor product.  The spelling matters: `a ⊗ₜ b` has type `A(V) ⊗ B(V)` rather than
syntactically `(tensorObj A B)(V)`, so a rewrite rule mentioning it directly cannot be applied
by `rw`.  Through this single head symbol the lemmas below are ordinary rewrite rules. -/
noncomputable def germTmul (U : Dᵒᵖ) (T : CostructuredArrow F.op U) (r : ↑(R.obj U))
    (a : A.obj T.left) (b : B.obj T.left) :
    ↑(colimit (diagram F R (tensorObj A B) U)) :=
  germ F R (tensorObj A B) T r (a ⊗ₜ b)

/-- The pure tensor of the germ of `r ⊗ a` and the germ of `1 ⊗ b`, as a section over `U` of the
objectwise tensor product of the two pullbacks.  This is the counterpart of
`Stacks.PullbackTensor.germTmul` on the other side of the isomorphism, and it is spelled as a
definition for the same reason. -/
noncomputable def tmulGerm (U : Dᵒᵖ) (T : CostructuredArrow F.op U) (r : ↑(R.obj U))
    (a : A.obj T.left) (b : B.obj T.left) :
    ↑((tensorObj (obj F R A) (obj F R B)).obj U) :=
  germ F R A T r a ⊗ₜ germ F R B T 1 b

section Functoriality

variable {A B} (A' B' : PresheafOfModules.{w} ((F.op ⋙ R) ⋙ forget₂ CommRingCat RingCat))

/-- `L₀` applied to the objectwise tensor product of two morphisms, on the germ of a pure
tensor. -/
lemma colimitPullback_map_germTmul (u : A ⟶ A') (v : B ⟶ B') (U : Dᵒᵖ)
    (T : CostructuredArrow F.op U) (a : A.obj T.left) (b : B.obj T.left) :
    Hom.app ((colimitPullback F R).map (tensorHom u v)) U (germTmul F R A B U T 1 a b)
      = germTmul F R A' B' U T 1 (Hom.app u T.left a) (Hom.app v T.left b) :=
  (colimitPullback_map_germ_one F R (tensorHom u v) T (a ⊗ₜ b)).trans
    (congrArg (germ F R (tensorObj A' B') T 1) (tensorHom_tmul u v T.left a b))

/-- The objectwise tensor product of `L₀` applied to two morphisms, on a pure tensor of
germs. -/
lemma tensorHom_tmulGerm (u : A ⟶ A') (v : B ⟶ B') (U : Dᵒᵖ)
    (T : CostructuredArrow F.op U) (a : A.obj T.left) (b : B.obj T.left) :
    Hom.app (tensorHom ((colimitPullback F R).map u) ((colimitPullback F R).map v)) U
        (tmulGerm F R A B U T 1 a b)
      = tmulGerm F R A' B' U T 1 (Hom.app u T.left a) (Hom.app v T.left b) := by
  refine (tensorHom_tmul ((colimitPullback F R).map u) ((colimitPullback F R).map v) U
    (germ F R A T 1 a) (germ F R B T 1 b)).trans ?_
  rw [colimitPullback_map_germ_one, colimitPullback_map_germ_one]
  rfl

end Functoriality

/-- A morphism out of the colimit computing the pullback of an objectwise tensor product is
determined by its values on the germs of `1 ⊗ (a ⊗ b)`. -/
lemma germ_tensor_hom_ext {U : Dᵒᵖ} {P : ModuleCat.{w} ↑(R.obj U)}
    {x y : colimit (diagram F R (tensorObj A B) U) ⟶ P}
    (h : ∀ (T : CostructuredArrow F.op U) (a : A.obj T.left) (b : B.obj T.left),
      x (germTmul F R A B U T 1 a b) = y (germTmul F R A B U T 1 a b)) : x = y :=
  colimit.hom_ext fun T => extendScalars_tensor_hom_ext _ fun a b => h T a b

/-- The restriction maps of the pullback, on the germ of a pure tensor. -/
lemma germTmul_restrict {U U' : Dᵒᵖ} (g : U ⟶ U') (T : CostructuredArrow F.op U)
    (r : ↑(R.obj U)) (a : A.obj T.left) (b : B.obj T.left) :
    (obj F R (tensorObj A B)).map g (germTmul F R A B U T r a b)
      = germTmul F R A B U' (CostructuredArrow.mk (T.hom ≫ g)) ((R.map g).hom r) a b :=
  obj_map_germ F R (tensorObj A B) g T r (a ⊗ₜ b)

/-- The restriction maps of the objectwise tensor product of the two pullbacks, on a pure tensor
of germs. -/
lemma tmulGerm_restrict {U U' : Dᵒᵖ} (g : U ⟶ U') (T : CostructuredArrow F.op U)
    (r : ↑(R.obj U)) (a : A.obj T.left) (b : B.obj T.left) :
    (tensorObj (obj F R A) (obj F R B)).map g (tmulGerm F R A B U T r a b)
      = tmulGerm F R A B U' (CostructuredArrow.mk (T.hom ≫ g)) ((R.map g).hom r) a b := by
  refine Eq.trans (tensorObj_restrictₛₗ_tmul (F := obj F R A) (G := obj F R B) g
    (germ F R A T r a) (germ F R B T 1 b)) ?_
  change (obj F R A).map g (germ F R A T r a) ⊗ₜ (obj F R B).map g (germ F R B T 1 b) = _
  rw [obj_map_germ, obj_map_germ, map_one]
  rfl

/-- The diagram computing the pullback of an objectwise tensor product is the tensor product of
the diagrams computing the two pullbacks. -/
noncomputable def diagramTensorIso (U : Dᵒᵖ) :
    diagram F R (tensorObj A B) U ≅
      MonoidalCategory.tensorObj (diagram F R A U) (diagram F R B U) :=
  NatIso.ofComponents
    (fun T => extendScalarsTensorIso (R.map T.hom).hom (A.obj T.left) (B.obj T.left))
    (fun _ => extendScalars_tensor_hom_ext _ fun _ _ => rfl)

section Filtered

variable [RepresentablyFlat F]

/-- The tensor product of the two colimit cocones, read as a cocone on the diagram computing
the pullback of the objectwise tensor product. -/
noncomputable abbrev tensorCocone (U : Dᵒᵖ) : Cocone (diagram F R (tensorObj A B) U) :=
  (Cocone.precompose (diagramTensorIso F R A B U).hom).obj
    (Cocone.tensor (colimit.cocone (diagram F R A U)) (colimit.cocone (diagram F R B U)))

/-- **The objectwise tensor product commutes with the filtered colimit computing the pullback.**
This is the step for which the index category `CostructuredArrow F.op U` has to be filtered: a
tensor product of colimits is a colimit over the product of the index categories, and the
diagonal of a filtered category is final. -/
noncomputable def isColimit_tensorCocone (U : Dᵒᵖ) :
    IsColimit (tensorCocone F R A B U) :=
  (IsColimit.precomposeHomEquiv (diagramTensorIso F R A B U) _).symm
    (IsColimit.tensor (colimit.isColimit (diagram F R A U))
      (colimit.isColimit (diagram F R B U)))

/-- The sections of the pullback of an objectwise tensor product, over `U`, are the tensor
product of the sections of the two pullbacks. -/
noncomputable def colimitTensorIso (U : Dᵒᵖ) :
    colimit (diagram F R (tensorObj A B) U) ≅
      MonoidalCategory.tensorObj (colimit (diagram F R A U)) (colimit (diagram F R B U)) :=
  IsColimit.coconePointUniqueUpToIso (colimit.isColimit _) (isColimit_tensorCocone F R A B U)

/-- The colimit inclusion at `T` followed by `colimitTensorIso` is the component of
`diagramTensorIso` at `T` followed by the tensor product of the two colimit inclusions at `T`. -/
lemma colimitTensorIso_ι (U : Dᵒᵖ) (T : CostructuredArrow F.op U) :
    colimit.ι (diagram F R (tensorObj A B) U) T ≫ (colimitTensorIso F R A B U).hom =
      (diagramTensorIso F R A B U).hom.app T ≫
        MonoidalCategory.tensorHom (colimit.ι (diagram F R A U) T)
          (colimit.ι (diagram F R B U) T) :=
  IsColimit.comp_coconePointUniqueUpToIso_hom (colimit.isColimit _)
    (isColimit_tensorCocone F R A B U) T

/-- The isomorphism `colimitTensorIso` sends the germ of `r ⊗ (a ⊗ b)` to the pure tensor of the
germ of `r ⊗ a` and the germ of `1 ⊗ b`. -/
lemma colimitTensorIso_hom_germTmul (U : Dᵒᵖ) (T : CostructuredArrow F.op U) (r : ↑(R.obj U))
    (a : A.obj T.left) (b : B.obj T.left) :
    (colimitTensorIso F R A B U).hom (germTmul F R A B U T r a b)
      = tmulGerm F R A B U T r a b :=
  ConcreteCategory.congr_hom (colimitTensorIso_ι F R A B U T)
    (tmul (R.map T.hom).hom r (a ⊗ₜ b))

/-- **The left adjoint `L₀` of `PresheafOfModules.pushforward₀ F R` commutes with the objectwise
tensor product**, on objects. -/
noncomputable def objTensorIso :
    obj F R (tensorObj A B) ≅ tensorObj (obj F R A) (obj F R B) :=
  PresheafOfModules.isoMk (fun U => colimitTensorIso F R A B U)
    (fun {U U'} g => germ_tensor_hom_ext F R A B fun T a b => by
      change (colimitTensorIso F R A B U').hom
            ((obj F R (tensorObj A B)).map g (germTmul F R A B U T 1 a b))
          = (tensorObj (obj F R A) (obj F R B)).map g
            ((colimitTensorIso F R A B U).hom (germTmul F R A B U T 1 a b))
      rw [germTmul_restrict, colimitTensorIso_hom_germTmul, colimitTensorIso_hom_germTmul,
        tmulGerm_restrict])

/-- On sections over `U`, the isomorphism `objTensorIso` sends the germ of `r ⊗ (a ⊗ b)` to the
pure tensor of the germ of `r ⊗ a` and the germ of `1 ⊗ b`. -/
lemma objTensorIso_hom_germTmul (U : Dᵒᵖ) (T : CostructuredArrow F.op U) (r : ↑(R.obj U))
    (a : A.obj T.left) (b : B.obj T.left) :
    Hom.app (objTensorIso F R A B).hom U (germTmul F R A B U T r a b)
      = tmulGerm F R A B U T r a b :=
  colimitTensorIso_hom_germTmul F R A B U T r a b

/-- **The left adjoint `L₀` of `PresheafOfModules.pushforward₀ F R` commutes with the objectwise
tensor product**, as an isomorphism of bifunctors: naturality in both presheaves of modules is
part of the statement. -/
noncomputable def colimitPullbackTensorIso :
    (Functor.uncurry.obj (PresheafOfModules.tensorBifunctor.{u, u, w, w, w} (F.op ⋙ R))) ⋙
        colimitPullback F R ≅
      Functor.prod (colimitPullback F R) (colimitPullback F R) ⋙
        (Functor.uncurry.obj (PresheafOfModules.tensorBifunctor.{u, u, w, w, w} R)) :=
  NatIso.ofComponents (fun P => objTensorIso F R P.1 P.2)
    (fun {P Q} uv => by
      have comparison :
          (colimitPullback F R).map (tensorHom uv.1 uv.2) ≫ (objTensorIso F R Q.1 Q.2).hom =
            (objTensorIso F R P.1 P.2).hom ≫
              tensorHom ((colimitPullback F R).map uv.1) ((colimitPullback F R).map uv.2) :=
        PresheafOfModules.hom_ext fun U =>
          germ_tensor_hom_ext F R P.1 P.2 fun T a b => by
            change Hom.app (objTensorIso F R Q.1 Q.2).hom U
                  (Hom.app ((colimitPullback F R).map (tensorHom uv.1 uv.2)) U
                    (germTmul F R P.1 P.2 U T 1 a b))
                = Hom.app (tensorHom ((colimitPullback F R).map uv.1)
                    ((colimitPullback F R).map uv.2)) U
                  (Hom.app (objTensorIso F R P.1 P.2).hom U
                    (germTmul F R P.1 P.2 U T 1 a b))
            rw [colimitPullback_map_germTmul, objTensorIso_hom_germTmul,
              objTensorIso_hom_germTmul, tensorHom_tmulGerm]
      exact (congrArg (fun morphism ↦
        (colimitPullback F R).map morphism ≫ (objTensorIso F R Q.1 Q.2).hom)
          (PresheafOfModules.tensorBifunctor_uncurry_map (O := F.op ⋙ R) uv.1 uv.2)).trans
        (comparison.trans (congrArg (fun morphism ↦ (objTensorIso F R P.1 P.2).hom ≫ morphism)
          (PresheafOfModules.tensorBifunctor_uncurry_map (O := R)
            ((colimitPullback F R).map uv.1) ((colimitPullback F R).map uv.2)).symm)))

end Filtered

end Colimit

/-! ### The pullback of presheaves of modules and the objectwise tensor product -/

section Pullback

open Stacks.PullbackColimit

variable {C D : Type u} [SmallCategory C] [SmallCategory D]
  {F : C ⥤ D} [RepresentablyFlat F]
  {S : Cᵒᵖ ⥤ CommRingCat.{w}} {R : Dᵒᵖ ⥤ CommRingCat.{w}} (α : S ⟶ F.op ⋙ R)
  [hUL : UnivLE.{u, w}]

include hUL

/-- **The concrete model of the pullback of presheaves of modules commutes with the objectwise
tensor product**: extension of scalars does (`extendScalarsTensorObjIso`) and the filtered
colimit does (`objTensorIso`). -/
noncomputable def modelPullbackTensorObjIso
    (M N : PresheafOfModules.{w} (S ⋙ forget₂ CommRingCat RingCat)) :
    (extendScalars α ⋙ colimitPullback F R).obj (tensorObj M N) ≅
      tensorObj ((extendScalars α ⋙ colimitPullback F R).obj M)
        ((extendScalars α ⋙ colimitPullback F R).obj N) :=
  (colimitPullback F R).mapIso (extendScalarsTensorObjIso α M N) ≪≫
    objTensorIso F R ((extendScalars α).obj M) ((extendScalars α).obj N)

/-- **The concrete model of the pullback commutes with the objectwise tensor product**, as an
isomorphism of bifunctors. -/
noncomputable def modelPullbackTensorIso :
    (Functor.uncurry.obj (PresheafOfModules.tensorBifunctor.{u, u, w, w, w} S)) ⋙ extendScalars α ⋙
        colimitPullback F R ≅
      Functor.prod (extendScalars α ⋙ colimitPullback F R)
          (extendScalars α ⋙ colimitPullback F R) ⋙
        (Functor.uncurry.obj (PresheafOfModules.tensorBifunctor.{u, u, w, w, w} R)) :=
  Functor.isoWhiskerRight (extendScalarsTensorIsoBifunctor S (F.op ⋙ R) α) (colimitPullback F R) ≪≫
    Functor.isoWhiskerLeft (Functor.prod (extendScalars α) (extendScalars α))
      (colimitPullbackTensorIso F R)

/-- **Tag 01CD for presheaves of modules**: `PresheafOfModules.pullback` commutes with the
objectwise tensor product, as an isomorphism of bifunctors.  Transported from
`modelPullbackTensorIso` along `Stacks.PullbackColimit.pullbackIso`. -/
noncomputable def pullbackTensorIso :
    (Functor.uncurry.obj (PresheafOfModules.tensorBifunctor.{u, u, w, w, w} S)) ⋙
        PresheafOfModules.pullback.{w} (toRingCatPullback α) ≅
      Functor.prod (PresheafOfModules.pullback.{w} (toRingCatPullback α))
          (PresheafOfModules.pullback.{w} (toRingCatPullback α)) ⋙
        (Functor.uncurry.obj (PresheafOfModules.tensorBifunctor.{u, u, w, w, w} R)) :=
  Functor.isoWhiskerLeft ((Functor.uncurry.obj (PresheafOfModules.tensorBifunctor.{u, u, w, w, w}
      S))) (pullbackIso α) ≪≫
    modelPullbackTensorIso α ≪≫
      Functor.isoWhiskerRight (NatIso.prod (pullbackIso α) (pullbackIso α)).symm
        ((Functor.uncurry.obj (PresheafOfModules.tensorBifunctor.{u, u, w, w, w} R)))

end Pullback

/-! ### The ringed-space pullback and the tensor product of sheaves of modules -/

section RingedSpace

open AlgebraicGeometry RingedSpaceModuleAdjunction Stacks.RingedSpace Stacks.PullbackColimit
open CategoryTheory.Sheaf

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)

/-- The pushforward of presheaves of modules along the structure morphism of a morphism of
ringed spaces is a right adjoint.  `RingedSpaceModuleAdjunction.modulePushforward_isRightAdjoint`
proves this inline; it is needed as an instance here, to apply
`SheafOfModules.sheafificationCompPullback` and `SheafOfModules.pullbackIso`. -/
noncomputable instance isRightAdjoint_pushforward_structureSheafHom :
    (PresheafOfModules.pushforward.{u} (structureSheafHom f).hom).IsRightAdjoint :=
  PresheafOfModules.instIsRightAdjointPushforward _

variable (X) in
/-- The identity of the structure presheaf, read through `forget₂ CommRingCat RingCat`, is the
identity.  This is `Functor.map_id` for the forgetful functor, and it is needed because
`PresheafOfModules.moduleSheafification` is stated for `toRingCatMap J a` while
`Stacks.SheafOfModules.Tensor.sheafTensor` and `SheafOfModules.pullbackIso` are stated for
`𝟙 (toRingCat J Osharp).obj`; the two are equal but not definitionally so. -/
lemma toRingCatMap_id :
    toRingCatMap (Opens.grothendieckTopology X.carrier) (𝟙 X.sheaf.obj)
      = 𝟙 (structureRingSheaf X).obj := by
  ext V
  simp

variable (X) in
/-- Module sheafification along the identity of the structure presheaf is the sheafification
functor that `Stacks.SheafOfModules.Tensor.sheafTensor` and `SheafOfModules.pullbackIso` use. -/
lemma moduleSheafification_id_eq :
    PresheafOfModules.moduleSheafification.{u, u, u, u}
        (Opens.grothendieckTopology X.carrier) (𝟙 X.sheaf.obj)
      = PresheafOfModules.sheafification (𝟙 (structureRingSheaf X).obj) := by
  congr 1

variable (X) in
/-- **Tag 0GMW on a ringed space**: sheafification commutes with the objectwise tensor product
of presheaves of modules.  This is `PresheafOfModules.sheafificationTensorIso` transported along
`moduleSheafification_id_eq`. -/
noncomputable def sheafificationTensorObjIso
    (P Q : PresheafOfModules.{u} (X.presheaf ⋙ forget₂ CommRingCat RingCat)) :
    (PresheafOfModules.sheafification (𝟙 (structureRingSheaf X).obj)).obj
        (PresheafOfModules.tensorObj P Q) ≅
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        ⟨X.presheaf, X.IsSheaf⟩).obj
          ((PresheafOfModules.sheafification (𝟙 (structureRingSheaf X).obj)).obj P)).obj
            ((PresheafOfModules.sheafification (𝟙 (structureRingSheaf X).obj)).obj Q) := by
  rw [← moduleSheafification_id_eq X]
  exact ((PresheafOfModules.sheafificationTensorIso.{u, u, u, u, u}
    (Opens.grothendieckTopology X.carrier) (𝟙 X.sheaf.obj)).app (P, Q)).symm

/-- **The pullback of sheaves of modules on a ringed space commutes with the tensor product**,
objectwise: `f^*(A ⊗_{𝒪_Y} B) ≅ f^*A ⊗_{𝒪_X} f^*B`.

This has the type of Stacks 01CD, and on its own it is **not** the tag: 01CD requires the
isomorphism to *be* the canonical comparison `Stacks.RingedSpace.comparison`.

That identification **is** proved:
`Stacks.PullbackTensor.pullbackTensorSheafObjIso_hom_eq_comparison`
(`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/PullbackTensorCanonical.lean:315`) establishes it
exactly as described here — through `Stacks.RingedSpace.comparison_unique`, by computing the
composite on the sheafification-unit image of a pure tensor — and `@[stacks 01CD]` sits on
`Stacks.RingedSpace.comparisonBifunctorIso`, the hypothesis-free form of
`Stacks.RingedSpace.comparisonIso`.

The composite is: the sheaf-level pullback of a sheafification is the sheafification of the
presheaf-level pullback (`SheafOfModules.sheafificationCompPullback`); the presheaf-level
pullback commutes with the objectwise tensor product (`pullbackTensorIso`); sheafification
commutes with the objectwise tensor product (Tag 0GMW); and the sheafification of a
presheaf-level pullback is the sheaf-level pullback (`SheafOfModules.pullbackIso`). -/
@[sga "4 IV 13.4" "partial"]
noncomputable def pullbackTensorSheafObjIso
    (A B : SheafOfModules.{u} (structureRingSheaf Y)) :
    (pullbackFunctor f).obj
        (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          ⟨Y.presheaf, Y.IsSheaf⟩).obj A).obj B) ≅
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        ⟨X.presheaf, X.IsSheaf⟩).obj ((pullbackFunctor f).obj A)).obj
          ((pullbackFunctor f).obj B) :=
  (SheafOfModules.sheafificationCompPullback.{u} (structureSheafHom f)).app
      (PresheafOfModules.tensorObj A.val B.val) ≪≫
    (PresheafOfModules.sheafification (𝟙 (structureRingSheaf X).obj)).mapIso
      ((pullbackTensorIso f.hom.c).app (A.val, B.val)) ≪≫
    sheafificationTensorObjIso X
        ((PresheafOfModules.pullback.{u} (structureSheafHom f).hom).obj A.val)
        ((PresheafOfModules.pullback.{u} (structureSheafHom f).hom).obj B.val) ≪≫
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        ⟨X.presheaf, X.IsSheaf⟩).mapIso
          ((SheafOfModules.pullbackIso.{u} (structureSheafHom f)).app A).symm).app _ ≪≫
        ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          ⟨X.presheaf, X.IsSheaf⟩).obj _).mapIso
            ((SheafOfModules.pullbackIso.{u} (structureSheafHom f)).app B).symm

end RingedSpace


end Stacks.PullbackTensor

