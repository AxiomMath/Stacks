module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafificationTensor
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackTensorComparison
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackTensorComparisonIso
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FinitePresentationStalk
public import StacksFrontier.Topology.Sheaves.OpenImmersion.ModuleExtensionByZero

/-!
# Invertibility of the pullback-tensor comparison, on stalks

Let `f : (X, 𝒪_X) ⟶ (Y, 𝒪_Y)` be a morphism of ringed spaces and let `A`, `B` be sheaves of
`𝒪_Y`-modules. [Stacks, Tag 01CD] asserts `f^*(A ⊗_{𝒪_Y} B) = f^*A ⊗_{𝒪_X} f^*B`, functorially
in `A` and `B`. The canonical comparison morphism `Stacks.RingedSpace.comparison` is built in
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/PullbackTensorComparison.lean`, where it is also
shown to be natural in both arguments and to be the unique morphism with its effect on pure
tensors; invertibility is the one clause left open there.

This file supplies the whole of that remaining argument, reduced to a single named input: the
stalk formula of [Stacks, Tag 0098] for the adjunction-defined pullback,

`(f^*G)_x ≅ 𝒪_{X, x} ⊗_{𝒪_{Y, f(x)}} G_{f(x)}`,

carrying the germ at `x` of the image of a section under the pullback-adjunction unit to the
pure tensor `1 ⊗ (germ of the section)`. That statement is packaged here as the predicate
`Stacks.RingedSpace.PullbackStalkFormula`, and the main theorem is that it implies
invertibility of the comparison. The Stacks proof of Tag 01CD is "Omitted"; the route taken is
the one its neighbours use (Tag 01CC: check at stalks, using Tag 01CB for the stalk of a tensor
product and Tag 0098 for the stalk of a pullback).

## Main definitions

* `Stacks.RingedSpace.tensorStalkEquiv`: Tag 01CB for the tensor product of
  `PullbackTensorComparison`, i.e. `((A ⊗_{𝒪_X} B))_x ≅ A_x ⊗_{𝒪_{X, x}} B_x` for the
  `Stacks.SheafOfModules.Tensor.sheafTensor` spelling of the tensor product, together with its
  germ formula `tensorStalkEquiv_germ`.
* `Stacks.RingedSpace.PullbackStalkFormula`: the stalk formula of Tag 0098 for
  `Stacks.RingedSpace.pullbackFunctor`, stated with the Tag 01CB module structure on a stalk,
  and `Stacks.RingedSpace.PullbackStalkFormula'`: the same statement with Mathlib's module
  structure on a stalk.

## Main results

* `Stacks.RingedSpace.isIso_comparison_of_pullbackStalkFormula`: **Tag 01CD**, invertibility.
  Given the stalk formula, every component of the comparison is an isomorphism.
* `Stacks.RingedSpace.isIso_comparisonNatTrans_of_pullbackStalkFormula` and
  `Stacks.RingedSpace.pullbackTensorIso`: the same conclusion as an isomorphism of bifunctors,
  so that naturality in both module arguments is part of the datum.
  `Stacks.RingedSpace.pullbackTensorIso_hom` records that the isomorphism is the canonical
  comparison, so `Stacks.RingedSpace.comparison_unique` applies to it.
* `Stacks.RingedSpace.tensorStalk_addHom_ext`: the stalk of a tensor product is generated, as
  an abelian group, by the germs of the sheafification-unit images of pure tensors.
* `Stacks.RingedSpace.pullbackStalkFormula_of_mathlib`: the two spellings of the stalk formula
  agree, by `Stacks.SheafOfModules.stalkModule_eq`.
* `Stacks.RingedSpace.comparison_pullbackUnit_tmul`: the comparison itself (rather than its
  adjoint transpose) on the pullback-unit image of the unit image of a pure tensor.

## Implementation notes

The tag is **not** placed on anything here: `PullbackStalkFormula` is a hypothesis of every
declaration below, so none of them states Tag 01CD outright. What is proved here is the
implication; the input is exactly Tag 0098 for `RingedSpaceModuleAdjunction.modulePullback` at
universe `u`, which `RingedSpaceModuleAdjunction.exists_modulePullbackStalkLinearEquiv`
provides.

Two module structures on the stalk of a sheaf of modules are in play —
`Stacks.SheafOfModules.TensorStalkRingedSpace.stalkModule` and Mathlib's
`PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier`.
They are equal but not definitionally so, and the type of a base-change linear equivalence
depends on both of them, so transporting across the equality is done through
`Stacks.RingedSpace.BaseChangeEquiv`, which abstracts the two structures into variables that
`Stacks.SheafOfModules.stalkModule_eq` can then be used to substitute.

`stalkModuleStructureRingSheaf` is needed because
`Stacks.SheafOfModules.TensorStalkRingedSpace.stalkModule` is registered for a
`PresheafOfModules (Stacks.SheafOfModules.TensorStalkRingedSpace.O X)`, and a sheaf of modules
over `Stacks.RingedSpace.structureRingSheaf X` — the spelling the comparison morphism uses — is
not recognised as one by instance search, even though the two sheaves of rings are
definitionally equal: `structureRingSheaf X` is `Sheaf.toRingCat _ X.sheaf`, and reaching
`Stacks.SheafOfModules.TensorStalkRingedSpace.O X` from it needs `X.sheaf` unfolded, which
instance search will not do.

That instance is also not *found* on the tensor objects below. A sheaf of modules produced by
`Stacks.SheafOfModules.Tensor.sheafTensor` is indexed by
`Stacks.SheafOfModules.Tensor.ringSheaf`, a plain `def`, so reaching
`Stacks.RingedSpace.structureRingSheaf X` from that index needs an unfolding instance search
does not perform, even though the two sheaves of rings are definitionally equal. Wherever the
stalk of a tensor object carries a module structure — `tensorStalkEquiv`,
`comparisonStalkEquiv`, `comparisonStalkLinearMap`, `comparisonStalkLinearMap_eq` and two steps
inside `comparisonStalkEquiv_germ` — `stalkModuleStructureRingSheaf` is named at that object instead
of being left to search. This is the spelling the canonical API uses itself:
`Stacks.SheafOfModules.TensorStalkRingedSpace.tensorStalkIso` and `tensorStalkIso_natural`
carry the same `letI` in their own statements. Nothing new is assumed and no instance is
declared; the one instance of this file is applied where search cannot reach it.

`congr_distribBaseChange_congr_apply` states the composite of the three base-change
equivalences on a pure tensor at variables. Heartbeats are counted cumulatively over a
declaration, and `comparisonStalkEquiv_germ` does not fit inside the budget while performing
that computation at its own sheaf expressions; taking it once, at variables, is what makes it
fit.

The rewrites below are staged as closed equations proved separately and then rewritten with,
rather than as a chain of `rw`s by the general lemmas. The general lemmas do not match: a
section of a sheafified tensor product carries two definitionally equal but syntactically
different types, and `rw`'s `kabstract` works at reducible transparency, so it fails to find
the pattern. Writing the instance of each lemma out by hand makes the pattern closed and the
match syntactic.

## References

* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
* [Stacks Project, Tag 01CB](https://stacks.math.columbia.edu/tag/01CB)
* [Stacks Project, Tag 0098](https://stacks.math.columbia.edu/tag/0098)
-/

@[expose] public section

attribute [local instance_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.SheafedSpace.sheaf

open AlgebraicGeometry CategoryTheory TopologicalSpace PresheafOfModules Opposite
open scoped TensorProduct
universe u
namespace Stacks.RingedSpace
open Stacks.SheafOfModules.TensorStalkRingedSpace RingedSpaceModuleAdjunction

/-- The `𝒪_{X, x}`-module structure on the stalk at `x` of a sheaf of modules over
`Stacks.RingedSpace.structureRingSheaf X`, given by
`Stacks.SheafOfModules.TensorStalkRingedSpace.stalkModule`. -/
noncomputable instance stalkModuleStructureRingSheaf {X : RingedSpace.{u, u}}
    (A : SheafOfModules.{u} (structureRingSheaf X)) (x : X.carrier) :
    Module (ringStalk X x) (grpStalk X A.val x) :=
  Stacks.SheafOfModules.TensorStalkRingedSpace.stalkModule X A.val x

section Transport
variable {R S T N : Type u} [CommRing R] [CommRing S] [Algebra R S]
  [AddCommGroup T] [AddCommGroup N]
end Transport

section TensorStalk
variable {X : RingedSpace.{u, u}} (x : X.carrier)
  (A B : SheafOfModules.{u} (structureRingSheaf X))

/-- The stalk of a tensor product of sheaves of modules is the tensor product of the stalks:
`(A ⊗_{𝒪_X} B)_x ≃ A_x ⊗_{𝒪_{X, x}} B_x`, as `𝒪_{X, x}`-modules. -/
noncomputable def tensorStalkEquiv :
    letI := stalkModuleStructureRingSheaf (X := X)
      (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        ⟨(X).presheaf, (X).IsSheaf⟩).obj A).obj B) x
    grpStalk X (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ⟨(X).presheaf, (X).IsSheaf⟩).obj A).obj B).val x
      ≃ₗ[ringStalk X x]
      grpStalk X A.val x ⊗[ringStalk X x] grpStalk X B.val x :=
  tensorStalkIso X x A B

/-- `tensorStalkEquiv` sends the germ at `x` of the sheafification-unit image of a pure tensor
`m ⊗ n` to the pure tensor of the germs of `m` and `n`. -/
lemma tensorStalkEquiv_germ (U : Opens X.carrier) (hx : x ∈ U)
    (m : A.val.obj (op U)) (n : B.val.obj (op U)) :
    tensorStalkEquiv x A B
        (grpGerm X (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          ⟨(X).presheaf, (X).IsSheaf⟩).obj A).obj B).val
          x U hx
          (Hom.app ((PresheafOfModules.sheafificationAdjunction
            (R := Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf)
            (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf).obj)).unit.app
            (PresheafOfModules.tensorObj A.val B.val)) (op U) (m ⊗ₜ n))) =
      grpGerm X A.val x U hx m ⊗ₜ[ringStalk X x] grpGerm X B.val x U hx n :=
  tensorStalkIso_germ X x A B U hx m n

/-- Two additive maps out of the stalk of a tensor product of sheaves of modules agree if they
agree on the germs of the sheafification-unit images of pure tensors of sections. -/
lemma tensorStalk_addHom_ext {P : Type u} [AddCommGroup P]
    (l r : grpStalk X (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ⟨(X).presheaf, (X).IsSheaf⟩).obj A).obj
      B).val x →+ P)
    (h : ∀ (U : Opens X.carrier) (hx : x ∈ U) (m : A.val.obj (op U)) (n : B.val.obj (op U)),
      l (grpGerm X (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        ⟨(X).presheaf, (X).IsSheaf⟩).obj A).obj B).val
        x U hx
          (Hom.app ((PresheafOfModules.sheafificationAdjunction
            (R := Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf)
            (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf).obj)).unit.app
            (PresheafOfModules.tensorObj A.val B.val)) (op U) (m ⊗ₜ n))) =
        r (grpGerm X (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          ⟨(X).presheaf, (X).IsSheaf⟩).obj A).obj
          B).val x U hx
          (Hom.app ((PresheafOfModules.sheafificationAdjunction
            (R := Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf)
            (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf).obj)).unit.app
            (PresheafOfModules.tensorObj A.val B.val)) (op U) (m ⊗ₜ n)))) :
    l = r := by
  refine AddMonoidHom.ext fun z ↦ ?_
  obtain ⟨w, rfl⟩ : ∃ w, (tensorStalkEquiv x A B).symm w = z :=
    ⟨tensorStalkEquiv x A B z, (tensorStalkEquiv x A B).symm_apply_apply z⟩
  induction w using TensorProduct.inductionOn with
  | add a b ha hb => simpa only [map_add] using congrArg₂ (· + ·) ha hb
  | tmul p q =>
      obtain ⟨Up, hUp, sp, hsp⟩ := TopCat.Presheaf.exists_germ_eq A.val.presheaf p
      obtain ⟨Uq, hUq, sq, hsq⟩ := TopCat.Presheaf.exists_germ_eq B.val.presheaf q
      have hxU : x ∈ Up ⊓ Uq := ⟨hUp, hUq⟩
      set m : A.val.obj (op (Up ⊓ Uq)) := A.val.presheaf.map (homOfLE inf_le_left).op sp with hm
      set n : B.val.obj (op (Up ⊓ Uq)) := B.val.presheaf.map (homOfLE inf_le_right).op sq with hn
      have hgm : grpGerm X A.val x (Up ⊓ Uq) hxU m = p :=
        (TopCat.Presheaf.germ_res_apply A.val.presheaf (homOfLE inf_le_left) x hxU sp).trans hsp
      have hgn : grpGerm X B.val x (Up ⊓ Uq) hxU n = q :=
        (TopCat.Presheaf.germ_res_apply B.val.presheaf (homOfLE inf_le_right) x hxU sq).trans hsq
      have he : (tensorStalkEquiv x A B).symm (p ⊗ₜ[ringStalk X x] q) =
          grpGerm X (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
            ⟨(X).presheaf, (X).IsSheaf⟩).obj A).obj B).val
            x (Up ⊓ Uq) hxU
            (Hom.app ((PresheafOfModules.sheafificationAdjunction
              (R := Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf)
              (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf).obj)).unit.app
              (PresheafOfModules.tensorObj A.val B.val)) (op (Up ⊓ Uq)) (m ⊗ₜ n)) := by
        refine (tensorStalkEquiv x A B).injective ?_
        rw [LinearEquiv.apply_symm_apply, tensorStalkEquiv_germ, hgm, hgn]
      rw [he]
      exact h (Up ⊓ Uq) hxU m n
end TensorStalk

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)

/-- The stalk formula for the pullback along `f`: for every sheaf of `𝒪_Y`-modules `G` and every
`x`, there is an `𝒪_{X, x}`-linear equivalence `(f^*G)_x ≃ 𝒪_{X, x} ⊗_{𝒪_{Y, f(x)}} G_{f(x)}`
sending the germ of the pullback-unit image of a section `s` to `1 ⊗ (germ of s)`. The module
structures on stalks are those of `stalkModuleStructureRingSheaf`. -/
def PullbackStalkFormula : Prop :=
  ∀ (G : SheafOfModules.{u} (structureRingSheaf Y)) (x : X.carrier),
    letI : Algebra (ringStalk Y (f.hom.base x)) (ringStalk X x) :=
      (f.hom.stalkMap x).hom.toAlgebra
    ∃ e : grpStalk X ((pullbackFunctor f).obj G).val x ≃ₗ[ringStalk X x]
        TensorProduct (ringStalk Y (f.hom.base x)) (ringStalk X x)
          (grpStalk Y G.val (f.hom.base x)),
      ∀ (V : Opens Y.carrier) (hx : f.hom.base x ∈ V) (s : G.val.obj (op V)),
        e (grpGerm X ((pullbackFunctor f).obj G).val x ((opensMap f).obj V) hx
            (pullbackUnit f G (op V) s)) =
          (1 : ringStalk X x) ⊗ₜ[ringStalk Y (f.hom.base x)]
            grpGerm Y G.val (f.hom.base x) V hx s

/-- The stalk formula `PullbackStalkFormula`, stated with Mathlib's module structure on the
stalk of a presheaf of modules. -/
def PullbackStalkFormula' : Prop :=
  ∀ (G : SheafOfModules.{u} (structureRingSheaf Y)) (x : X.carrier),
    letI : Algebra (ringStalk Y (f.hom.base x)) (ringStalk X x) :=
      (f.hom.stalkMap x).hom.toAlgebra
    letI : Module (ringStalk Y (f.hom.base x)) (grpStalk Y G.val (f.hom.base x)) :=
      G.val.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier (f.hom.base x)
    letI : Module (ringStalk X x) (grpStalk X ((pullbackFunctor f).obj G).val x) :=
      ((pullbackFunctor f).obj
        G).val.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier x
    ∃ e : grpStalk X ((pullbackFunctor f).obj G).val x ≃ₗ[ringStalk X x]
        TensorProduct (ringStalk Y (f.hom.base x)) (ringStalk X x)
          (grpStalk Y G.val (f.hom.base x)),
      ∀ (V : Opens Y.carrier) (hx : f.hom.base x ∈ V) (s : G.val.obj (op V)),
        e (grpGerm X ((pullbackFunctor f).obj G).val x ((opensMap f).obj V) hx
            (pullbackUnit f G (op V) s)) =
          (1 : ringStalk X x) ⊗ₜ[ringStalk Y (f.hom.base x)]
            grpGerm Y G.val (f.hom.base x) V hx s

/-- The stalk formula for Mathlib's module structure on stalks implies the stalk formula for
the module structure of `stalkModuleStructureRingSheaf`. -/
theorem pullbackStalkFormula_of_mathlib (h : PullbackStalkFormula' f) :
    PullbackStalkFormula f := by
  intro G x
  let _ : Algebra (ringStalk Y (f.hom.base x)) (ringStalk X x) :=
    (f.hom.stalkMap x).hom.toAlgebra
  obtain ⟨e, he⟩ := h G x
  refine ⟨transportBaseChangeEquiv
    (Stacks.SheafOfModules.stalkModule_eq X ((pullbackFunctor f).obj G).val x).symm
    (Stacks.SheafOfModules.stalkModule_eq Y G.val (f.hom.base x)).symm e, ?_⟩
  intro V hx s
  exact transportBaseChangeEquiv_eq_one_tmul
    (Stacks.SheafOfModules.stalkModule_eq X ((pullbackFunctor f).obj G).val x).symm
    (Stacks.SheafOfModules.stalkModule_eq Y G.val (f.hom.base x)).symm e _ _ (he V hx s)

/-- The comparison morphism on the pullback-unit image of the sheafification-unit image of a
pure tensor: it is the sheafification-unit image on `X` of the tensor of the two pullback-unit
images. -/
lemma comparison_pullbackUnit_tmul (A B : SheafOfModules.{u} (structureRingSheaf Y))
    (U : (Opens Y.carrier)ᵒᵖ) (x : A.val.obj U) (y : B.val.obj U) :
    Hom.app (comparison f A B).val ((opensMap f).op.obj U)
        (pullbackUnit f (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          ⟨(Y).presheaf, (Y).IsSheaf⟩).obj A).obj B) U
          (Hom.app ((PresheafOfModules.sheafificationAdjunction
            (R := Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf)
            (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf).obj)).unit.app
            (PresheafOfModules.tensorObj A.val B.val)) U (x ⊗ₜ y))) =
      Hom.app ((PresheafOfModules.sheafificationAdjunction
        (R := Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf)
        (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf).obj)).unit.app
        (PresheafOfModules.tensorObj ((pullbackFunctor f).obj A).val
          ((pullbackFunctor f).obj B).val))
        ((opensMap f).op.obj U) (pullbackUnit f A U x ⊗ₜ pullbackUnit f B U y) :=
  (homEquiv_val_app f _ _ (comparison f A B) U _).symm.trans
    (comparison_homEquiv_unit_tmul f A B U x y)

section Stalkwise
variable (hf : PullbackStalkFormula f) (A B : SheafOfModules.{u} (structureRingSheaf Y))

private noncomputable def chosenStalkEquiv
    (G : SheafOfModules.{u} (structureRingSheaf Y)) (x : X.carrier) :
    letI : Algebra (ringStalk Y (f.hom.base x)) (ringStalk X x) :=
      (f.hom.stalkMap x).hom.toAlgebra
    grpStalk X ((pullbackFunctor f).obj G).val x ≃ₗ[ringStalk X x]
      TensorProduct (ringStalk Y (f.hom.base x)) (ringStalk X x)
        (grpStalk Y G.val (f.hom.base x)) :=
  (hf G x).choose

private lemma chosenStalkEquiv_germ (G : SheafOfModules.{u} (structureRingSheaf Y))
    (x : X.carrier) (V : Opens Y.carrier) (hx : f.hom.base x ∈ V) (s : G.val.obj (op V)) :
    letI : Algebra (ringStalk Y (f.hom.base x)) (ringStalk X x) :=
      (f.hom.stalkMap x).hom.toAlgebra
    chosenStalkEquiv f hf G x
        (grpGerm X ((pullbackFunctor f).obj G).val x ((opensMap f).obj V) hx
          (pullbackUnit f G (op V) s)) =
      (1 : ringStalk X x) ⊗ₜ[ringStalk Y (f.hom.base x)]
        grpGerm Y G.val (f.hom.base x) V hx s :=
  (hf G x).choose_spec V hx s

private noncomputable def comparisonStalkEquiv (x : X.carrier) :
    letI := stalkModuleStructureRingSheaf (X := X)
      (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} ⟨(X).presheaf, (X).IsSheaf⟩).obj
        ((pullbackFunctor f).obj A)).obj ((pullbackFunctor f).obj B)) x
    grpStalk X ((pullbackFunctor f).obj (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ⟨(Y).presheaf, (Y).IsSheaf⟩).obj A).obj B)).val x ≃ₗ[ringStalk X x]
      grpStalk X (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        ⟨(X).presheaf, (X).IsSheaf⟩).obj
        ((pullbackFunctor f).obj A)).obj ((pullbackFunctor f).obj B)).val x := by
  letI : Algebra (ringStalk Y (f.hom.base x)) (ringStalk X x) :=
    (f.hom.stalkMap x).hom.toAlgebra
  let _ : Module (ringStalk Y (f.hom.base x))
      (grpStalk Y (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        ⟨(Y).presheaf, (Y).IsSheaf⟩).obj A).obj B).val
        (f.hom.base x)) :=
    stalkModuleStructureRingSheaf (X := Y)
      (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        ⟨(Y).presheaf, (Y).IsSheaf⟩).obj A).obj B)
      (f.hom.base x)
  exact (chosenStalkEquiv f hf (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
    ⟨(Y).presheaf, (Y).IsSheaf⟩).obj
    A).obj B) x).trans <|
    (TensorProduct.AlgebraTensorModule.congr
        (LinearEquiv.refl (ringStalk X x) (ringStalk X x))
        (tensorStalkEquiv (f.hom.base x) A B)).trans <|
      (TensorProduct.AlgebraTensorModule.distribBaseChange
          (ringStalk Y (f.hom.base x)) (ringStalk X x)
          (grpStalk Y A.val (f.hom.base x)) (grpStalk Y B.val (f.hom.base x))).trans <|
        (TensorProduct.congr (chosenStalkEquiv f hf A x).symm
            (chosenStalkEquiv f hf B x).symm).trans
          (tensorStalkEquiv x ((pullbackFunctor f).obj A) ((pullbackFunctor f).obj B)).symm

/-- The composite of the three canonical base-change equivalences on a pure tensor
`1 ⊗ z`, stated at variables. The three `rw`s it performs are by the `_tmul` equations of
`TensorProduct.AlgebraTensorModule.congr`,
`TensorProduct.AlgebraTensorModule.distribBaseChange` and `TensorProduct.congr`; taking them
here, once, rather than at the long sheaf expressions of
`Stacks.RingedSpace.comparisonStalkEquiv_germ`, is what keeps that lemma inside the
heartbeat budget, which is counted cumulatively over a declaration. -/
private lemma congr_distribBaseChange_congr_apply {R S M N Z P Q : Type u}
    [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [AddCommGroup Z] [Module R Z]
    [AddCommGroup P] [Module S P] [AddCommGroup Q] [Module S Q]
    (eZ : Z ≃ₗ[R] TensorProduct R M N)
    (eP : P ≃ₗ[S] TensorProduct R S M) (eQ : Q ≃ₗ[S] TensorProduct R S N)
    (w : TensorProduct R S Z) (z : Z) (a : M) (b : N) (p : P) (q : Q)
    (hw : w = (1 : S) ⊗ₜ[R] z) (hz : eZ z = a ⊗ₜ[R] b)
    (hp : p = eP.symm ((1 : S) ⊗ₜ[R] a)) (hq : q = eQ.symm ((1 : S) ⊗ₜ[R] b)) :
    TensorProduct.congr eP.symm eQ.symm
        (TensorProduct.AlgebraTensorModule.distribBaseChange R S M N
          (TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl S S) eZ w))
      = p ⊗ₜ[S] q := by
  rw [hw, TensorProduct.AlgebraTensorModule.congr_tmul, LinearEquiv.refl_apply, hz,
    TensorProduct.AlgebraTensorModule.distribBaseChange_tmul, TensorProduct.congr_tmul, hp, hq]

private lemma comparisonStalkEquiv_germ (x : X.carrier) (V : Opens Y.carrier)
    (hx : f.hom.base x ∈ V) (m : A.val.obj (op V)) (n : B.val.obj (op V)) :
    comparisonStalkEquiv f hf A B x
        (grpGerm X ((pullbackFunctor f).obj
          (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
            ⟨(Y).presheaf, (Y).IsSheaf⟩).obj A).obj B)).val x
          ((opensMap f).obj V) hx
          (pullbackUnit f (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
            ⟨(Y).presheaf, (Y).IsSheaf⟩).obj A).obj
            B) (op V)
            (Hom.app ((PresheafOfModules.sheafificationAdjunction
              (R := Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf)
              (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf).obj)).unit.app
              (PresheafOfModules.tensorObj A.val B.val)) (op V) (m ⊗ₜ n)))) =
      grpGerm X (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        ⟨(X).presheaf, (X).IsSheaf⟩).obj
        ((pullbackFunctor f).obj A)).obj ((pullbackFunctor f).obj B)).val x ((opensMap f).obj V) hx
        (Hom.app ((PresheafOfModules.sheafificationAdjunction
          (R := Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf)
          (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf).obj)).unit.app
          (PresheafOfModules.tensorObj ((pullbackFunctor f).obj A).val
            ((pullbackFunctor f).obj B).val))
          (op ((opensMap f).obj V))
          (pullbackUnit f A (op V) m ⊗ₜ pullbackUnit f B (op V) n)) := by
  let _ : Algebra (ringStalk Y (f.hom.base x)) (ringStalk X x) :=
    (f.hom.stalkMap x).hom.toAlgebra
  have hA := congrArg (chosenStalkEquiv f hf A x).symm
    (chosenStalkEquiv_germ f hf A x V hx m)
  have hB := congrArg (chosenStalkEquiv f hf B x).symm
    (chosenStalkEquiv_germ f hf B x V hx n)
  rw [LinearEquiv.symm_apply_apply] at hA hB
  set T := ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
    ⟨(Y).presheaf, (Y).IsSheaf⟩).obj A).obj B with hT
  let _ : Module (ringStalk Y (f.hom.base x)) (grpStalk Y T.val (f.hom.base x)) :=
    stalkModuleStructureRingSheaf (X := Y) T (f.hom.base x)
  set u : T.val.obj (op V) := Hom.app ((PresheafOfModules.sheafificationAdjunction
    (R := Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf)
    (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf).obj)).unit.app
    (PresheafOfModules.tensorObj A.val B.val)) (op V) (m ⊗ₜ n) with hu
  set gT := grpGerm Y T.val (f.hom.base x) V hx u with hgT
  set gA := grpGerm Y A.val (f.hom.base x) V hx m with hgA
  set gB := grpGerm Y B.val (f.hom.base x) V hx n with hgB
  set e := chosenStalkEquiv f hf T x with he
  have h0 : e (grpGerm X ((pullbackFunctor f).obj T).val x ((opensMap f).obj V) hx
        (pullbackUnit f T (op V) u)) =
      (1 : ringStalk X x) ⊗ₜ[ringStalk Y (f.hom.base x)] gT :=
    chosenStalkEquiv_germ f hf T x V hx u
  have h2 : tensorStalkEquiv (f.hom.base x) A B gT =
      gA ⊗ₜ[ringStalk Y (f.hom.base x)] gB :=
    tensorStalkEquiv_germ (f.hom.base x) A B V hx m n
  have hinner := congr_distribBaseChange_congr_apply (tensorStalkEquiv (f.hom.base x) A B)
    (chosenStalkEquiv f hf A x) (chosenStalkEquiv f hf B x)
    (e (grpGerm X ((pullbackFunctor f).obj T).val x ((opensMap f).obj V) hx
      (pullbackUnit f T (op V) u))) gT gA gB
    (grpGerm X ((pullbackFunctor f).obj A).val x ((opensMap f).obj V) hx
      (pullbackUnit f A (op V) m))
    (grpGerm X ((pullbackFunctor f).obj B).val x ((opensMap f).obj V) hx
      (pullbackUnit f B (op V) n)) h0 h2 hA hB
  exact (congrArg (tensorStalkEquiv x ((pullbackFunctor f).obj A)
      ((pullbackFunctor f).obj B)).symm hinner).trans
    ((LinearEquiv.symm_apply_eq _).mpr
      (tensorStalkEquiv_germ x ((pullbackFunctor f).obj A) ((pullbackFunctor f).obj B)
        ((opensMap f).obj V) hx (pullbackUnit f A (op V) m)
        (pullbackUnit f B (op V) n)).symm)

private noncomputable def comparisonStalkLinearMap (x : X.carrier) :
    letI := stalkModuleStructureRingSheaf (X := X)
      (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} ⟨(X).presheaf, (X).IsSheaf⟩).obj
        ((pullbackFunctor f).obj A)).obj ((pullbackFunctor f).obj B)) x
    grpStalk X ((pullbackFunctor f).obj (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ⟨(Y).presheaf, (Y).IsSheaf⟩).obj A).obj B)).val x →ₗ[ringStalk X x]
      grpStalk X (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        ⟨(X).presheaf, (X).IsSheaf⟩).obj
        ((pullbackFunctor f).obj A)).obj ((pullbackFunctor f).obj B)).val x :=
  stalkMapL X _ _ (comparison f A B).val x

private lemma comparisonStalkLinearMap_germ (x : X.carrier) (V : Opens Y.carrier)
    (hx : f.hom.base x ∈ V) (m : A.val.obj (op V)) (n : B.val.obj (op V)) :
    comparisonStalkLinearMap f A B x
        (grpGerm X ((pullbackFunctor f).obj
          (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
            ⟨(Y).presheaf, (Y).IsSheaf⟩).obj A).obj B)).val x
          ((opensMap f).obj V) hx
          (pullbackUnit f (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
            ⟨(Y).presheaf, (Y).IsSheaf⟩).obj A).obj
            B) (op V)
            (Hom.app ((PresheafOfModules.sheafificationAdjunction
              (R := Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf)
              (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf).obj)).unit.app
              (PresheafOfModules.tensorObj A.val B.val)) (op V) (m ⊗ₜ n)))) =
      grpGerm X (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        ⟨(X).presheaf, (X).IsSheaf⟩).obj
        ((pullbackFunctor f).obj A)).obj ((pullbackFunctor f).obj B)).val x ((opensMap f).obj V) hx
        (Hom.app ((PresheafOfModules.sheafificationAdjunction
          (R := Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf)
          (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf).obj)).unit.app
          (PresheafOfModules.tensorObj ((pullbackFunctor f).obj A).val
            ((pullbackFunctor f).obj B).val))
          (op ((opensMap f).obj V))
          (pullbackUnit f A (op V) m ⊗ₜ pullbackUnit f B (op V) n)) := by
  refine (Stacks.SheafOfModules.stalkMapL_germ X (comparison f A B).val x
    ((opensMap f).obj V) hx _).trans ?_
  exact congrArg _ (comparison_pullbackUnit_tmul f A B (op V) m n)

private lemma comparisonStalkLinearMap_eq (x : X.carrier) :
    letI := stalkModuleStructureRingSheaf (X := X)
      (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} ⟨(X).presheaf, (X).IsSheaf⟩).obj
        ((pullbackFunctor f).obj A)).obj ((pullbackFunctor f).obj B)) x
    comparisonStalkLinearMap f A B x = (comparisonStalkEquiv f hf A B x).toLinearMap := by
  let _ : Algebra (ringStalk Y (f.hom.base x)) (ringStalk X x) :=
    (f.hom.stalkMap x).hom.toAlgebra
  let _ : Module (ringStalk X x)
      (grpStalk X (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        ⟨(X).presheaf, (X).IsSheaf⟩).obj
        ((pullbackFunctor f).obj A)).obj ((pullbackFunctor f).obj B)).val x) :=
    stalkModuleStructureRingSheaf (X := X)
      (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} ⟨(X).presheaf, (X).IsSheaf⟩).obj
        ((pullbackFunctor f).obj A)).obj ((pullbackFunctor f).obj B)) x
  let _ : Module (ringStalk Y (f.hom.base x))
      (grpStalk Y (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        ⟨(Y).presheaf, (Y).IsSheaf⟩).obj A).obj B).val
        (f.hom.base x)) :=
    stalkModuleStructureRingSheaf (X := Y)
      (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        ⟨(Y).presheaf, (Y).IsSheaf⟩).obj A).obj B)
      (f.hom.base x)
  refine linearMap_ext_of_baseChange_generators
    (chosenStalkEquiv f hf (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ⟨(Y).presheaf, (Y).IsSheaf⟩).obj A).obj
      B) x) _ _ fun z ↦ ?_
  let g := (chosenStalkEquiv f hf (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
    ⟨(Y).presheaf, (Y).IsSheaf⟩).obj A).obj B) x).symm.toLinearMap.toAddMonoidHom.comp
    (TensorProduct.mk (ringStalk Y (f.hom.base x)) (ringStalk X x) _ 1).toAddMonoidHom
  let l := (comparisonStalkLinearMap f A B x).toAddMonoidHom.comp g
  let r := (comparisonStalkEquiv f hf A B x).toLinearMap.toAddMonoidHom.comp g
  have hlr : l = r := by
    refine tensorStalk_addHom_ext (f.hom.base x) A B l r fun V hy m n ↦ ?_
    have hx : x ∈ (opensMap f).obj V := hy
    have hsym : g (grpGerm Y (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
              ⟨(Y).presheaf, (Y).IsSheaf⟩).obj A).obj
              B).val (f.hom.base x) V hy
              (Hom.app ((PresheafOfModules.sheafificationAdjunction
                (R := Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf)
                (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf).obj)).unit.app
                (PresheafOfModules.tensorObj A.val B.val)) (op V) (m ⊗ₜ n))) =
        grpGerm X ((pullbackFunctor f).obj
          (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
            ⟨(Y).presheaf, (Y).IsSheaf⟩).obj A).obj B)).val x
          ((opensMap f).obj V) hx
          (pullbackUnit f (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
            ⟨(Y).presheaf, (Y).IsSheaf⟩).obj A).obj
            B) (op V)
            (Hom.app ((PresheafOfModules.sheafificationAdjunction
              (R := Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf)
              (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf).obj)).unit.app
              (PresheafOfModules.tensorObj A.val B.val)) (op V) (m ⊗ₜ n))) :=
      (LinearEquiv.symm_apply_eq _).mpr
        (chosenStalkEquiv_germ f hf (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          ⟨(Y).presheaf, (Y).IsSheaf⟩).obj A).obj B) x V hy _).symm
    change comparisonStalkLinearMap f A B x (g _) = comparisonStalkEquiv f hf A B x (g _)
    rw [hsym, comparisonStalkLinearMap_germ f A B x V hx m n,
      comparisonStalkEquiv_germ f hf A B x V hx m n]
  exact DFunLike.congr_fun hlr z

include hf in
/-- **Stacks 01CD**, invertibility: given the stalk formula of Tag 0098 for the pullback,
the canonical comparison `f^*(A ⊗ B) ⟶ f^*A ⊗ f^*B` is an isomorphism. -/
theorem isIso_comparison_of_pullbackStalkFormula : IsIso (comparison f A B) := by
  refine ExtensionByZeroModules.isIso_of_stalk_isIso _ (comparison f A B) fun x ↦ ?_
  rw [ConcreteCategory.isIso_iff_bijective]
  change Function.Bijective (comparisonStalkLinearMap f A B x)
  rw [comparisonStalkLinearMap_eq f hf A B x]
  exact (comparisonStalkEquiv f hf A B x).bijective

include hf in
/-- **Stacks 01CD**, functoriality: given the stalk formula of Tag 0098 for the pullback, the
comparison is an isomorphism of bifunctors. -/
theorem isIso_comparisonNatTrans_of_pullbackStalkFormula : IsIso (comparisonNatTrans f) := by
  have : ∀ P, IsIso ((comparisonNatTrans f).app P) :=
    fun P ↦ isIso_comparison_of_pullbackStalkFormula f hf P.1 P.2
  exact NatIso.isIso_of_isIso_app _

include hf in
/-- **Stacks 01CD** for a morphism of ringed spaces, given the stalk formula of Tag 0098 for
the pullback: `f^*(A ⊗_{𝒪_Y} B) ≅ f^*A ⊗_{𝒪_X} f^*B`, naturally in both arguments. -/
noncomputable def pullbackTensorIso :
    Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ⟨(Y).presheaf, (Y).IsSheaf⟩) ⋙
        pullbackFunctor f ≅
      Functor.prod (pullbackFunctor f) (pullbackFunctor f) ⋙
        Functor.uncurry.obj
          (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} ⟨(X).presheaf, (X).IsSheaf⟩) :=
  haveI : IsIso (comparisonNatTrans f) :=
    isIso_comparisonNatTrans_of_pullbackStalkFormula f hf
  asIso (comparisonNatTrans f)

include hf in
/-- The isomorphism of `pullbackTensorIso` is the canonical comparison, so by
`Stacks.RingedSpace.comparison_unique` it is the only candidate. -/
lemma pullbackTensorIso_hom : (pullbackTensorIso f hf).hom = comparisonNatTrans f := rfl

end Stalkwise

end Stacks.RingedSpace

end
