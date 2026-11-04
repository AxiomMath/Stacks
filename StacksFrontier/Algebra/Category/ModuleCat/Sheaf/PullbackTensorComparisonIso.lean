module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackTensorComparison
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FinitePresentationStalk
public import StacksFrontier.Topology.Sheaves.RingedSpace.ModulePullbackStalkAdjunction
public import StacksFrontier.Topology.Sheaves.OpenImmersion.ModuleExtensionByZero
public import StacksCore.Tactic.StacksAttribute

/-!
# Stacks 01CD: the pullback comparison for tensor products is an isomorphism

Let `f : (X, 𝒪_X) ⟶ (Y, 𝒪_Y)` be a morphism of ringed spaces and `A`, `B` sheaves of
`𝒪_Y`-modules.  `StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackTensorComparison`
constructs the canonical comparison morphism

`Stacks.RingedSpace.comparison f A B : f^*(A ⊗_{𝒪_Y} B) ⟶ f^*A ⊗_{𝒪_X} f^*B`,

shows it is natural in both arguments, and reduces Stacks 01CD to invertibility of its
components.  This file supplies that invertibility, so Stacks 01CD is unconditional.

## Main results

* `Stacks.RingedSpace.comparison_isIso`: the comparison morphism is an isomorphism.
* `Stacks.RingedSpace.comparisonNatTrans_app_isIso`: the same as an instance for the
  components of `Stacks.RingedSpace.comparisonNatTrans`, which is the hypothesis
  `Stacks.RingedSpace.comparisonIso` and the Stacks 079U file were stated under.
* `Stacks.RingedSpace.comparisonBifunctorIso`: `f^*(- ⊗ -) ≅ f^*(-) ⊗ f^*(-)` as an
  isomorphism of bifunctors, with no hypotheses.

## The argument

Invertibility is checked on stalks.  Writing `R = 𝒪_{Y, f x}` and `S = 𝒪_{X, x}`, the two
stalks are computed by results already in the tree:

* `RingedSpaceModuleAdjunction.exists_modulePullbackStalkLinearEquiv` (Stacks 0098) gives
  `(f^*A)_x ≃ S ⊗_R A_{f x}`, **together with its value on germs**: the germ of the
  pullback-unit image of a section `s` goes to `1 ⊗ (germ of s)`.  That characterisation is
  the whole reason the argument can be run: the pullback is an abstract left adjoint and
  nothing else about its sections is available.
* `Stacks.SheafOfModules.TensorStalkRingedSpace.tensorStalkIso` (Stacks 01CB) gives `(A ⊗ B)_y ≃
  A_y ⊗_R B_y`, characterised
  on germs of pure tensors.

Composing those with `TensorProduct.AlgebraTensorModule.distribBaseChange` produces an
`S`-linear equivalence `stalkComparisonEquiv` between the two stalks, and
`comparison_stalkMapL_eq` identifies it with the stalk map of the comparison.  Both sides are
`S`-linear maps out of a base change `S ⊗_R (A ⊗ B)_y`, so they agree as soon as they agree on
the elements `1 ⊗ z`; and `(A ⊗ B)_y` is generated, as an abelian group, by the germs of pure
tensors, so they agree as soon as they agree on `1 ⊗ (germ of a pure tensor)`.  There the
comparison's own characterisation `comparison_homEquiv_unit_tmul` computes both.

Finally `ExtensionByZeroModules.isIso_of_stalk_isIso` turns a stalkwise isomorphism of sheaves
of modules into an isomorphism.

## Implementation notes

Every statement about stalks is written at the `Stacks.SheafOfModules.TensorStalkRingedSpace`
  spelling of the structure
sheaf, `structureSheafRing`, because that is where
`Stacks.SheafOfModules.TensorStalkRingedSpace.stalkModule` — the `𝒪_{X,x}`-module structure on a
  stalk that
`Stacks.SheafOfModules.TensorStalkRingedSpace.tensorStalkIso` is stated over — is found by instance
  search.  With a
sheaf of modules typed over `Stacks.RingedSpace.structureRingSheaf`, the goal
`Module ↑(ringStalk X x) ↑(grpStalk X A.val x)` does **not** synthesize, because
`(structureRingSheaf X).obj` reaches `Stacks.SheafOfModules.TensorStalkRingedSpace.O X` only
  through `RingedSpace.sheaf`,
which is not reducible, and instance search works at `instances` transparency.  The two
spellings are `rfl`-equal (`structureSheafRing X =
  structureRingSheaf X`), and
`pullbackSheaf` and `comparisonAt` are reducible retypings across that equality, so the
instances are found at the retyped spelling without any transparency option.

Two structures must still be seated by hand, each by a `letI` naming the canonical term, never
by a new instance:

* the `Algebra` instance on the stalk rings, `(f.hom.stalkMap x).hom.toAlgebra`, which is not
  an instance anywhere in the tree;
* `Stacks.SheafOfModules.TensorStalkRingedSpace.stalkModule` on the stalk of a
  `Stacks.SheafOfModules.Tensor.sheafTensor` value.  That value is typed over
  `(Stacks.SheafOfModules.Tensor.ringSheaf ⟨X.presheaf, _⟩).obj` rather than over
  `structureSheafRing X`, and `Stacks.SheafOfModules.Tensor.ringSheaf` is a plain `def`, so —
  unlike `structureSheafRing`, which carries `@[instance_reducible]` — the two spellings are
  not defeq at `instances` transparency and the `stalkModule` candidate is rejected during
  unification.  `tensorStalkIso` and `tensorStalkIso_natural` carry the same `letI` in their
  own statements for the same reason.  Since the bound value is term-identical to theirs, no
  second module structure is created and the `letI` zeta-reduces, so the statements it appears
  in are unchanged.

For the same reason, `rw` cannot instantiate `pullbackStalkEquiv_germ` and
`pullbackStalkEquiv_symm_one_tmul` at a `sheafTensor` value by matching: their sheaf argument
is typed over `structureSheafRing`, which `rw`'s keyed matching cannot see through.  Those two
rewrites are therefore given their arguments explicitly, which elaborates the retyping at
default transparency and leaves a closed pattern to match.

The tensor product is the native `Stacks.SheafOfModules.Tensor.sheafTensor`, and its map
from the presheaf tensor is the generic sheafification-adjunction unit. The local-section
construction `Stacks.SheafOfModules.TensorStalkRingedSpace.toTensorSheafSection` evaluates
that unit, so no bridge between tensor constructions is needed.

The module structures on the two stalks that
`exists_modulePullbackStalkLinearEquiv` is stated over are Mathlib's, not Tag 01CB's.  They
are equal (`Stacks.SheafOfModules.stalkModule_eq`) but not syntactically so, and
`transportBaseChangeEquiv` carries the equivalence and its germ formula across that equality
by `cases` on the equality of instances.  This is why `pullbackStalkEquiv` is defined rather
than used directly.

## References

* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
* [Stacks Project, Tag 01CB](https://stacks.math.columbia.edu/tag/01CB)
* [Stacks Project, Tag 0098](https://stacks.math.columbia.edu/tag/0098)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open scoped TensorProduct

universe u

namespace Stacks.RingedSpace

open RingedSpaceModuleAdjunction _root_.PresheafOfModules CategoryTheory.Sheaf
open Stacks.SheafOfModules.TensorStalkRingedSpace

/-! ### Transporting a base-change equivalence across equal module structures -/

section Transport

variable {R S T N : Type u} [CommRing R] [CommRing S] [Algebra R S] [AddCommGroup T]
  [AddCommGroup N]

/-- The type of a base-change linear equivalence `T ≃ₗ[S] S ⊗[R] N`, read as a function of the
two module structures it mentions. -/
abbrev BaseChangeEquiv (iT : Module S T) (iN : Module R N) : Type u :=
  letI : Module S T := iT
  letI : Module R N := iN
  T ≃ₗ[S] S ⊗[R] N

/-- Transport a base-change linear equivalence along equalities of the two module structures
it is stated over. -/
noncomputable def transportBaseChangeEquiv {iT jT : Module S T} {iN jN : Module R N}
    (hT : iT = jT) (hN : iN = jN) (e : BaseChangeEquiv iT iN) : BaseChangeEquiv jT jN := by
  cases hT; cases hN; exact e

/-- The transported equivalence takes the same values `1 ⊗ n` as the original. -/
lemma transportBaseChangeEquiv_eq_one_tmul {iT jT : Module S T} {iN jN : Module R N}
    (hT : iT = jT) (hN : iN = jN) (e : BaseChangeEquiv iT iN) (t : T) (n : N)
    (h : e t = (letI := iN; (1 : S) ⊗ₜ[R] n)) :
    transportBaseChangeEquiv hT hN e t = (letI := jN; (1 : S) ⊗ₜ[R] n) := by
  cases hT; cases hN; exact h

end Transport

/-! ### The comparison morphism on sections of a pullback -/

section Sections

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)

variable (A B : SheafOfModules.{u} (structureRingSheaf Y))

/-- **The comparison morphism on sections.**  It carries the pullback-unit image of the
sheafification-unit image of a pure tensor to the sheafification-unit image on `X` of the
tensor of the two pullback-unit images.  This is the untransposed form of
`Stacks.RingedSpace.comparison_homEquiv_unit_tmul`, and it is the only thing used about the
comparison below. -/
lemma comparison_pullbackUnit_unit_tmul (U : (Opens Y.carrier)ᵒᵖ) (a : A.val.obj U)
    (b : B.val.obj U) :
    Hom.app (comparison f A B).val ((opensMap f).op.obj U)
        (pullbackUnit f (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          ⟨Y.presheaf, Y.IsSheaf⟩).obj A).obj B) U
          (Hom.app ((PresheafOfModules.sheafificationAdjunction
            (R := Stacks.SheafOfModules.Tensor.ringSheaf ⟨Y.presheaf, Y.IsSheaf⟩)
            (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf ⟨Y.presheaf, Y.IsSheaf⟩).obj)).unit.app
              (_root_.PresheafOfModules.tensorObj A.val B.val)) U (a ⊗ₜ b))) =
      Hom.app ((PresheafOfModules.sheafificationAdjunction
        (R := Stacks.SheafOfModules.Tensor.ringSheaf ⟨X.presheaf, X.IsSheaf⟩)
        (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf ⟨X.presheaf, X.IsSheaf⟩).obj)).unit.app
          (_root_.PresheafOfModules.tensorObj ((pullbackFunctor f).obj A).val
            ((pullbackFunctor f).obj B).val))
        ((opensMap f).op.obj U) (pullbackUnit f A U a ⊗ₜ pullbackUnit f B U b) :=
  (homEquiv_val_app f _ _ (comparison f A B) U _).symm.trans
    (comparison_homEquiv_unit_tmul f A B U a b)

end Sections

/-! ### The stalk of a pullback, at the Tag 01CB module structure -/

section PullbackStalk

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)

/-- The pullback `f^*A`, retyped over
  `structureSheafRing`.  This is a reducible
retyping across the `rfl`-equality `structureSheafRing
  X = structureRingSheaf X`,
and its only purpose is that instance search then finds
  `Stacks.SheafOfModules.TensorStalkRingedSpace.stalkModule` on its
stalks. -/
noncomputable abbrev pullbackSheaf (A : SheafOfModules.{u} (structureSheafRing Y)) :
    SheafOfModules.{u} (structureSheafRing X) :=
  (pullbackFunctor f).obj A

variable (A : SheafOfModules.{u} (structureSheafRing Y)) (x : X.carrier)

/-- **Stacks 0098 at the Tag 01CB module structure.** The stalk of `f^*A` at `x` is the base
change along the germ map of the stalk of `A` at `f x`.  This is
`RingedSpaceModuleAdjunction.exists_modulePullbackStalkLinearEquiv`, transported from
Mathlib's module structure on a stalk to
`Stacks.SheafOfModules.TensorStalkRingedSpace.stalkModule`.
-/
noncomputable def pullbackStalkEquiv :
    letI : Algebra ↑(ringStalk Y (f.hom.base x)) ↑(ringStalk X x) :=
      (f.hom.stalkMap x).hom.toAlgebra
    ↑(grpStalk X (pullbackSheaf f A).val x) ≃ₗ[↑(ringStalk X x)]
      ↑(ringStalk X x) ⊗[↑(ringStalk Y (f.hom.base x))] ↑(grpStalk Y A.val (f.hom.base x)) :=
  letI : Algebra ↑(ringStalk Y (f.hom.base x)) ↑(ringStalk X x) :=
    (f.hom.stalkMap x).hom.toAlgebra
  transportBaseChangeEquiv
    (Stacks.SheafOfModules.stalkModule_eq X (pullbackSheaf f A).val x).symm
    (Stacks.SheafOfModules.stalkModule_eq Y A.val (f.hom.base x)).symm
    (RingedSpaceModuleAdjunction.exists_modulePullbackStalkLinearEquiv f A x).choose

/-- **The characterisation of `pullbackStalkEquiv`:** the germ of the pullback-unit image of a
section `s` of `A` over `V` goes to `1 ⊗ (germ of s)`. -/
lemma pullbackStalkEquiv_germ (V : Opens Y.carrier) (hx : f.hom.base x ∈ V)
    (s : A.val.obj (op V)) :
    letI : Algebra ↑(ringStalk Y (f.hom.base x)) ↑(ringStalk X x) :=
      (f.hom.stalkMap x).hom.toAlgebra
    pullbackStalkEquiv f A x
        (grpGerm X (pullbackSheaf f A).val x ((opensMap f).obj V) hx
          (pullbackUnit f A (op V) s)) =
      (1 : ↑(ringStalk X x)) ⊗ₜ[↑(ringStalk Y (f.hom.base x))]
        grpGerm Y A.val (f.hom.base x) V hx s :=
  let : Algebra ↑(ringStalk Y (f.hom.base x)) ↑(ringStalk X x) :=
    (f.hom.stalkMap x).hom.toAlgebra
  transportBaseChangeEquiv_eq_one_tmul _ _ _ _ _
    ((RingedSpaceModuleAdjunction.exists_modulePullbackStalkLinearEquiv f A x).choose_spec
      V hx s)

/-- The inverse form of `pullbackStalkEquiv_germ`. -/
lemma pullbackStalkEquiv_symm_one_tmul (V : Opens Y.carrier) (hx : f.hom.base x ∈ V)
    (s : A.val.obj (op V)) :
    letI : Algebra ↑(ringStalk Y (f.hom.base x)) ↑(ringStalk X x) :=
      (f.hom.stalkMap x).hom.toAlgebra
    (pullbackStalkEquiv f A x).symm
        ((1 : ↑(ringStalk X x)) ⊗ₜ[↑(ringStalk Y (f.hom.base x))]
          grpGerm Y A.val (f.hom.base x) V hx s) =
      grpGerm X (pullbackSheaf f A).val x ((opensMap f).obj V) hx
        (pullbackUnit f A (op V) s) :=
  let : Algebra ↑(ringStalk Y (f.hom.base x)) ↑(ringStalk X x) :=
    (f.hom.stalkMap x).hom.toAlgebra
  (LinearEquiv.symm_apply_eq _).2 (pullbackStalkEquiv_germ f A x V hx s).symm

end PullbackStalk

/-! ### The two stalks of the comparison -/

section StalkComparison

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)
  (A B : SheafOfModules.{u} (structureSheafRing Y)) (x : X.carrier)

/-- **The stalkwise comparison equivalence.** Writing `R = 𝒪_{Y, f x}` and `S = 𝒪_{X, x}`, the
two stalks of the comparison morphism are identified by

`(f^*(A ⊗ B))_x ≃ S ⊗_R (A ⊗ B)_{f x} ≃ S ⊗_R (A_{f x} ⊗_R B_{f x})`
`≃ (S ⊗_R A_{f x}) ⊗_S (S ⊗_R B_{f x}) ≃ (f^*A)_x ⊗_S (f^*B)_x ≃ (f^*A ⊗ f^*B)_x`,

using Stacks 0098 twice, Stacks 01CB twice, and base change of a tensor product in the middle.
`comparison_stalkMapL_eq` below says this is the stalk map of the comparison. -/
noncomputable def stalkComparisonEquiv :
    letI : Algebra ↑(ringStalk Y (f.hom.base x)) ↑(ringStalk X x) :=
      (f.hom.stalkMap x).hom.toAlgebra
    letI := stalkModule X ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ⟨X.presheaf, X.IsSheaf⟩).obj ((pullbackSheaf f A))).obj ((pullbackSheaf f B)))).val x
    ↑(grpStalk X (pullbackSheaf f ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ⟨Y.presheaf, Y.IsSheaf⟩).obj (A)).obj (B)))).val x) ≃ₗ[↑(ringStalk X x)]
      ↑(grpStalk X ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ⟨X.presheaf, X.IsSheaf⟩).obj ((pullbackSheaf f A))).obj ((pullbackSheaf f B)))).val x) :=
  letI : Algebra ↑(ringStalk Y (f.hom.base x)) ↑(ringStalk X x) :=
    (f.hom.stalkMap x).hom.toAlgebra
  letI := stalkModule X ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
    ⟨X.presheaf, X.IsSheaf⟩).obj ((pullbackSheaf f A))).obj ((pullbackSheaf f B)))).val x
  letI := stalkModule Y ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
    ⟨Y.presheaf, Y.IsSheaf⟩).obj (A)).obj (B))).val (f.hom.base x)
  (pullbackStalkEquiv f ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ⟨Y.presheaf, Y.IsSheaf⟩).obj (A)).obj (B))) x).trans
    (((TensorProduct.AlgebraTensorModule.congr
            (LinearEquiv.refl ↑(ringStalk X x) ↑(ringStalk X x))
            (tensorStalkIso Y (f.hom.base x) A B)).trans
          (TensorProduct.AlgebraTensorModule.distribBaseChange
            ↑(ringStalk Y (f.hom.base x)) ↑(ringStalk X x)
            ↑(grpStalk Y A.val (f.hom.base x)) ↑(grpStalk Y B.val (f.hom.base x)))).trans
      ((TensorProduct.congr (pullbackStalkEquiv f A x).symm
            (pullbackStalkEquiv f B x).symm).trans
        (tensorStalkIso X x (pullbackSheaf f A) (pullbackSheaf f B)).symm))

/-- `stalkComparisonEquiv` spelled out as the composite it is. -/
lemma stalkComparisonEquiv_apply
    (t : ↑(grpStalk X (pullbackSheaf f ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ⟨Y.presheaf, Y.IsSheaf⟩).obj (A)).obj (B)))).val x)) :
    letI : Algebra ↑(ringStalk Y (f.hom.base x)) ↑(ringStalk X x) :=
      (f.hom.stalkMap x).hom.toAlgebra
    letI := stalkModule X ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ⟨X.presheaf, X.IsSheaf⟩).obj ((pullbackSheaf f A))).obj ((pullbackSheaf f B)))).val x
    letI := stalkModule Y ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ⟨Y.presheaf, Y.IsSheaf⟩).obj (A)).obj (B))).val (f.hom.base x)
    stalkComparisonEquiv f A B x t =
      (tensorStalkIso X x (pullbackSheaf f A) (pullbackSheaf f B)).symm
        (TensorProduct.congr (pullbackStalkEquiv f A x).symm (pullbackStalkEquiv f B x).symm
          (TensorProduct.AlgebraTensorModule.distribBaseChange
            ↑(ringStalk Y (f.hom.base x)) ↑(ringStalk X x)
            ↑(grpStalk Y A.val (f.hom.base x)) ↑(grpStalk Y B.val (f.hom.base x))
            (TensorProduct.AlgebraTensorModule.congr
              (LinearEquiv.refl ↑(ringStalk X x) ↑(ringStalk X x))
              (tensorStalkIso Y (f.hom.base x) A B)
              (pullbackStalkEquiv f ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ⟨Y.presheaf, Y.IsSheaf⟩).obj (A)).obj (B)))
                x t)))) :=
  rfl

/-- **The characterisation of `stalkComparisonEquiv`:** on the germ of the pullback-unit image
of the sheafification-unit image of a pure tensor `m ⊗ n`, it is the germ of the
sheafification-unit image on `X` of the tensor of the two pullback-unit images — which is
exactly what the comparison morphism does, by `comparison_pullbackUnit_unit_tmul`. -/
lemma stalkComparisonEquiv_germ (V : Opens Y.carrier) (hx : f.hom.base x ∈ V)
    (m : A.val.obj (op V)) (n : B.val.obj (op V)) :
    stalkComparisonEquiv f A B x
        (grpGerm X (pullbackSheaf f ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ⟨Y.presheaf, Y.IsSheaf⟩).obj (A)).obj (B)))).val x
          ((opensMap f).obj V) hx
          (pullbackUnit f ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ⟨Y.presheaf, Y.IsSheaf⟩).obj (A)).obj (B))) (op V)
            (toTensorSheafSection Y A B (op V) (m ⊗ₜ n)))) =
      grpGerm X ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ⟨X.presheaf, X.IsSheaf⟩).obj ((pullbackSheaf f A))).obj ((pullbackSheaf f B)))).val x
        ((opensMap f).obj V) hx
        (toTensorSheafSection X (pullbackSheaf f A) (pullbackSheaf f B)
          (op ((opensMap f).obj V))
          (pullbackUnit f A (op V) m ⊗ₜ pullbackUnit f B (op V) n)) := by
  let _ : Algebra ↑(ringStalk Y (f.hom.base x)) ↑(ringStalk X x) :=
    (f.hom.stalkMap x).hom.toAlgebra
  let := stalkModule Y ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
    ⟨Y.presheaf, Y.IsSheaf⟩).obj (A)).obj (B))).val (f.hom.base x)
  rw [stalkComparisonEquiv_apply,
    pullbackStalkEquiv_germ f ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ⟨Y.presheaf, Y.IsSheaf⟩).obj (A)).obj (B))) x V hx
      (toTensorSheafSection Y A B (op V) (m ⊗ₜ n)),
    TensorProduct.AlgebraTensorModule.congr_tmul, LinearEquiv.refl_apply,
    tensorStalkIso_germ, TensorProduct.AlgebraTensorModule.distribBaseChange_tmul,
    TensorProduct.congr_tmul, pullbackStalkEquiv_symm_one_tmul,
    pullbackStalkEquiv_symm_one_tmul]
  exact (LinearEquiv.symm_apply_eq _).2
    (tensorStalkIso_germ X x (pullbackSheaf f A) (pullbackSheaf f B) ((opensMap f).obj V) hx
      (pullbackUnit f A (op V) m) (pullbackUnit f B (op V) n)).symm

/-- The Stacks 01CD comparison morphism, retyped over
  `structureSheafRing` so
that the stalk machinery of Tag 01CB applies to it.  A reducible retyping across the
`rfl`-equality of the two spellings of the structure sheaf. -/
noncomputable abbrev comparisonAt :
    pullbackSheaf f ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ⟨Y.presheaf, Y.IsSheaf⟩).obj (A)).obj (B))) ⟶
      (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ⟨X.presheaf, X.IsSheaf⟩).obj ((pullbackSheaf f A))).obj ((pullbackSheaf
        f B))) :=
  comparison f A B

/-- The stalk map of the comparison morphism, as an `𝒪_{X,x}`-linear map. -/
noncomputable abbrev comparisonStalkMap :
    letI := stalkModule X ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ⟨X.presheaf, X.IsSheaf⟩).obj ((pullbackSheaf f A))).obj ((pullbackSheaf f B)))).val x
    ↑(grpStalk X (pullbackSheaf f ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ⟨Y.presheaf, Y.IsSheaf⟩).obj (A)).obj (B)))).val x) →ₗ[↑(ringStalk X x)]
      ↑(grpStalk X ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ⟨X.presheaf, X.IsSheaf⟩).obj ((pullbackSheaf f A))).obj ((pullbackSheaf f B)))).val x) :=
  stalkMapL X (pullbackSheaf f ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ⟨Y.presheaf, Y.IsSheaf⟩).obj (A)).obj (B)))).val
    ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ⟨X.presheaf, X.IsSheaf⟩).obj ((pullbackSheaf f A))).obj ((pullbackSheaf f
      B)))).val
    (comparisonAt f A B).val x

/-- The stalk map of the comparison morphism on the germ of the pullback-unit image of the
sheafification-unit image of a pure tensor.  This is
`Stacks.SheafOfModules.stalkMapL_germ` fed by `comparison_pullbackUnit_unit_tmul`. -/
lemma comparisonStalkMap_germ (V : Opens Y.carrier) (hx : f.hom.base x ∈ V)
    (m : A.val.obj (op V)) (n : B.val.obj (op V)) :
    comparisonStalkMap f A B x
        (grpGerm X (pullbackSheaf f ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ⟨Y.presheaf, Y.IsSheaf⟩).obj (A)).obj (B)))).val x
          ((opensMap f).obj V) hx
          (pullbackUnit f ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ⟨Y.presheaf, Y.IsSheaf⟩).obj (A)).obj (B))) (op V)
            (toTensorSheafSection Y A B (op V) (m ⊗ₜ n)))) =
      grpGerm X ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ⟨X.presheaf, X.IsSheaf⟩).obj ((pullbackSheaf f A))).obj ((pullbackSheaf f B)))).val x
        ((opensMap f).obj V) hx
        (toTensorSheafSection X (pullbackSheaf f A) (pullbackSheaf f B)
          (op ((opensMap f).obj V))
          (pullbackUnit f A (op V) m ⊗ₜ pullbackUnit f B (op V) n)) :=
  (Stacks.SheafOfModules.stalkMapL_germ X (comparisonAt f A B).val x ((opensMap f).obj V) hx
      _).trans
    (congrArg
      (fun t ↦ grpGerm X ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ⟨X.presheaf, X.IsSheaf⟩).obj ((pullbackSheaf
        f A))).obj ((pullbackSheaf f B)))).val x ((opensMap f).obj V) hx t)
      (comparison_pullbackUnit_unit_tmul f A B (op V) m n))

end StalkComparison

/-! ### Two extensionality principles -/

section Ext

/-- **Two `S`-linear maps out of a base change agree as soon as they agree on `1 ⊗ m`.**  The
elements `1 ⊗ m` generate `S ⊗[R] M` as an `S`-module, since `a ⊗ m = a • (1 ⊗ m)`. -/
lemma linearMap_ext_of_baseChange_generators {R S M N P : Type u} [CommRing R] [CommRing S]
    [Algebra R S] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module S N]
    [AddCommGroup P] [Module S P] (e : N ≃ₗ[S] S ⊗[R] M) (l r : N →ₗ[S] P)
    (h : ∀ m : M, l (e.symm ((1 : S) ⊗ₜ[R] m)) = r (e.symm ((1 : S) ⊗ₜ[R] m))) : l = r := by
  refine LinearMap.ext fun z ↦ ?_
  obtain ⟨t, rfl⟩ : ∃ t, e.symm t = z := ⟨e z, e.symm_apply_apply z⟩
  induction t using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => simpa only [map_add] using congrArg₂ (· + ·) ha hb
  | tmul a m =>
      have ht : (a ⊗ₜ[R] m : S ⊗[R] M) = a • ((1 : S) ⊗ₜ[R] m) := by
        simpa only [smul_eq_mul, mul_one] using (TensorProduct.smul_tmul' a (1 : S) m).symm
      simp only [ht, map_smul, h]

/-- **Two additive maps out of the stalk of a tensor product agree as soon as they agree on the
germs of pure tensors.**  By Stacks 01CB the stalk is `A_z ⊗ B_z`, which is generated by pure
tensors of germs, and two germs can always be represented on a common open. -/
lemma addHom_ext_of_tensor_germ {Z : RingedSpace.{u, u}}
    (A B : SheafOfModules.{u} (structureSheafRing Z)) (z : Z.carrier) {P : Type u}
    [AddCommGroup P]
    (l r : ↑(grpStalk Z ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ⟨Z.presheaf, Z.IsSheaf⟩).obj (A)).obj (B))).val z) →+ P)
    (h : ∀ (U : Opens Z.carrier) (hz : z ∈ U) (m : A.val.obj (op U)) (n : B.val.obj (op U)),
      l (grpGerm Z ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ⟨Z.presheaf, Z.IsSheaf⟩).obj (A)).obj (B))).val z U hz
          (toTensorSheafSection Z A B (op U) (m ⊗ₜ n))) =
        r (grpGerm Z ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ⟨Z.presheaf, Z.IsSheaf⟩).obj (A)).obj (B))).val z U hz
          (toTensorSheafSection Z A B (op U) (m ⊗ₜ n)))) : l = r := by
  refine AddMonoidHom.ext fun t ↦ ?_
  obtain ⟨w, rfl⟩ : ∃ w, (tensorStalkIso Z z A B).symm w = t :=
    ⟨tensorStalkIso Z z A B t, (tensorStalkIso Z z A B).symm_apply_apply t⟩
  induction w using TensorProduct.induction_on with
  | zero =>
      calc
        l ((tensorStalkIso Z z A B).symm 0) = l 0 :=
          congrArg l (map_zero (tensorStalkIso Z z A B).symm)
        _ = 0 := l.map_zero
        _ = r 0 := r.map_zero.symm
        _ = r ((tensorStalkIso Z z A B).symm 0) :=
          (congrArg r (map_zero (tensorStalkIso Z z A B).symm)).symm
  | add a b ha hb => simpa only [map_add] using congrArg₂ (· + ·) ha hb
  | tmul p q =>
      obtain ⟨Up, hUp, sp, hsp⟩ := Stacks.SheafOfModules.exists_grpGerm_eq Z A.val z p
      obtain ⟨Uq, hUq, sq, hsq⟩ := Stacks.SheafOfModules.exists_grpGerm_eq Z B.val z q
      have hz : z ∈ Up ⊓ Uq := ⟨hUp, hUq⟩
      have hgm : grpGerm Z A.val z (Up ⊓ Uq) hz
          (A.val.map (homOfLE (inf_le_left : Up ⊓ Uq ≤ Up)).op sp) = p :=
        (TopCat.Presheaf.germ_res_apply A.val.presheaf
          (homOfLE (inf_le_left : Up ⊓ Uq ≤ Up)) z hz sp).trans hsp
      have hgn : grpGerm Z B.val z (Up ⊓ Uq) hz
          (B.val.map (homOfLE (inf_le_right : Up ⊓ Uq ≤ Uq)).op sq) = q :=
        (TopCat.Presheaf.germ_res_apply B.val.presheaf
          (homOfLE (inf_le_right : Up ⊓ Uq ≤ Uq)) z hz sq).trans hsq
      have hsym : (tensorStalkIso Z z A B).symm
            (grpGerm Z A.val z (Up ⊓ Uq) hz
                (A.val.map (homOfLE (inf_le_left : Up ⊓ Uq ≤ Up)).op sp) ⊗ₜ
              grpGerm Z B.val z (Up ⊓ Uq) hz
                (B.val.map (homOfLE (inf_le_right : Up ⊓ Uq ≤ Uq)).op sq)) =
          grpGerm Z ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ⟨Z.presheaf, Z.IsSheaf⟩).obj (A)).obj (B))).val z (Up ⊓ Uq)
            hz
            (toTensorSheafSection Z A B (op (Up ⊓ Uq))
              (A.val.map (homOfLE (inf_le_left : Up ⊓ Uq ≤ Up)).op sp ⊗ₜ
                B.val.map (homOfLE (inf_le_right : Up ⊓ Uq ≤ Uq)).op sq)) :=
        (LinearEquiv.symm_apply_eq _).2 (tensorStalkIso_germ Z z A B (Up ⊓ Uq) hz _ _).symm
      rw [← hgm, ← hgn, hsym]
      exact h (Up ⊓ Uq) hz _ _

end Ext

/-! ### Invertibility -/

section Main

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)
  (A B : SheafOfModules.{u} (structureSheafRing Y))

/-- **The stalk map of the comparison morphism is the stalkwise comparison equivalence.**  Both
sides are `𝒪_{X,x}`-linear maps out of `(f^*(A ⊗ B))_x ≃ 𝒪_{X,x} ⊗ (A ⊗ B)_{f x}`, so they
agree as soon as they agree on the elements `1 ⊗ w`; and `(A ⊗ B)_{f x}` is generated as an
abelian group by germs of pure tensors, where both sides are computed —
`comparisonStalkMap_germ` and `stalkComparisonEquiv_germ`. -/
lemma comparisonStalkMap_eq (x : X.carrier) :
    letI := stalkModule X ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ⟨X.presheaf, X.IsSheaf⟩).obj ((pullbackSheaf f A))).obj ((pullbackSheaf f B)))).val x
    comparisonStalkMap f A B x = (stalkComparisonEquiv f A B x).toLinearMap := by
  let _ : Algebra ↑(ringStalk Y (f.hom.base x)) ↑(ringStalk X x) :=
    (f.hom.stalkMap x).hom.toAlgebra
  let := stalkModule X ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
    ⟨X.presheaf, X.IsSheaf⟩).obj ((pullbackSheaf f A))).obj ((pullbackSheaf f B)))).val x
  let g : ↑(grpStalk Y ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ⟨Y.presheaf, Y.IsSheaf⟩).obj (A)).obj (B))).val
    (f.hom.base x)) →+
      ↑(grpStalk X (pullbackSheaf f ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ⟨Y.presheaf, Y.IsSheaf⟩).obj (A)).obj (B)))).val x) :=
    { toFun := fun w ↦ (pullbackStalkEquiv f ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u,
          u, u} ⟨Y.presheaf, Y.IsSheaf⟩).obj (A)).obj (B))) x).symm
          ((1 : ↑(ringStalk X x)) ⊗ₜ[↑(ringStalk Y (f.hom.base x))] w)
      map_zero' := by simp
      map_add' := fun a b ↦ by simp only [TensorProduct.tmul_add, map_add] }
  let l := (comparisonStalkMap f A B x).toAddMonoidHom.comp g
  let r := (stalkComparisonEquiv f A B x).toLinearMap.toAddMonoidHom.comp g
  have hlr : l = r := by
    refine addHom_ext_of_tensor_germ A B (f.hom.base x) l r fun U hz m n ↦ ?_
    have key := pullbackStalkEquiv_symm_one_tmul f
      ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        ⟨Y.presheaf, Y.IsSheaf⟩).obj (A)).obj (B))) x U hz
      (toTensorSheafSection Y A B (op U) (m ⊗ₜ n))
    exact (congrArg (comparisonStalkMap f A B x) key).trans
      (((comparisonStalkMap_germ f A B x U hz m n).trans
        (stalkComparisonEquiv_germ f A B x U hz m n).symm).trans
        (congrArg (stalkComparisonEquiv f A B x) key.symm))
  exact linearMap_ext_of_baseChange_generators
    (pullbackStalkEquiv f ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ⟨Y.presheaf, Y.IsSheaf⟩).obj (A)).obj (B))) x) _ _
    fun w ↦ DFunLike.congr_fun hlr w

/-- **Stacks 01CD, the invertibility.**  The canonical comparison morphism
`f^*(A ⊗_{𝒪_Y} B) ⟶ f^*A ⊗_{𝒪_X} f^*B` is an isomorphism: it is one on every stalk by
`comparisonStalkMap_eq`, and a morphism of sheaves of modules that is an isomorphism on every
stalk is an isomorphism. -/
theorem comparison_isIso : IsIso (comparison f A B) := by
  refine ExtensionByZeroModules.isIso_of_stalk_isIso (structureRingSheaf X)
    (comparison f A B) fun x ↦ ?_
  rw [ConcreteCategory.isIso_iff_bijective]
  let := stalkModule X ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
    ⟨X.presheaf, X.IsSheaf⟩).obj ((pullbackSheaf f A))).obj ((pullbackSheaf f B)))).val x
  show Function.Bijective (comparisonStalkMap f A B x)
  rw [comparisonStalkMap_eq]
  exact (stalkComparisonEquiv f A B x).bijective

end Main

section Consequences

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)

/-- The components of `Stacks.RingedSpace.comparisonNatTrans` are isomorphisms.  This is the
hypothesis that `Stacks.RingedSpace.comparisonIso` and the Stacks 079U file are stated under,
so declaring it as an instance discharges them. -/
instance comparisonNatTrans_app_isIso
    (P : SheafOfModules.{u} (structureRingSheaf Y) ×
      SheafOfModules.{u} (structureRingSheaf Y)) :
    IsIso ((comparisonNatTrans f).app P) :=
  comparison_isIso f P.1 P.2

/-- The comparison is an isomorphism of bifunctors. -/
instance comparisonNatTrans_isIso : IsIso (comparisonNatTrans f) :=
  @NatIso.isIso_of_isIso_app _ _ _ _ _ _ (comparisonNatTrans f)
    (fun pair => comparison_isIso f pair.1 pair.2)

/-- **Stacks 01CD**, unconditionally: pulling back the tensor product of two sheaves of modules
on a ringed space is the tensor product of their pullbacks, naturally in both arguments.  This
is `Stacks.RingedSpace.comparisonIso` with its hypothesis discharged, so by
`Stacks.RingedSpace.comparison_unique` it is the only candidate. -/
@[stacks 01CD]
noncomputable def comparisonBifunctorIso :
    Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ⟨Y.presheaf, Y.IsSheaf⟩) ⋙ pullbackFunctor f ≅
      Functor.prod (pullbackFunctor f) (pullbackFunctor f) ⋙
        Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          ⟨X.presheaf, X.IsSheaf⟩) :=
  comparisonIso f

/-- The forward map of `comparisonBifunctorIso` is `comparisonNatTrans`. -/
lemma comparisonBifunctorIso_hom : (comparisonBifunctorIso f).hom = comparisonNatTrans f := rfl

/-- **The canonicality clause of Stacks 01CD.**  The adjoint transpose of the forward map of
`comparisonBifunctorIso` at `(A, B)` carries the sheafification-unit image of a pure tensor to
the image, under the corresponding unit on `X`, of the tensor of the two pullback-unit
images. -/
@[stacks 01CD]
lemma comparisonBifunctorIso_hom_homEquiv_unit_tmul
    (A B : SheafOfModules.{u} (structureRingSheaf Y)) (U : (Opens Y.carrier)ᵒᵖ)
    (a : A.val.obj U) (b : B.val.obj U) :
    Hom.app ((pullbackAdjunction f).homEquiv
          (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
            ⟨Y.presheaf, Y.IsSheaf⟩).obj A).obj B)
          (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
            ⟨X.presheaf, X.IsSheaf⟩).obj ((pullbackFunctor f).obj A)).obj
              ((pullbackFunctor f).obj B))
          ((comparisonBifunctorIso f).hom.app (A, B))).val U
        (Hom.app ((PresheafOfModules.sheafificationAdjunction
          (R := Stacks.SheafOfModules.Tensor.ringSheaf ⟨Y.presheaf, Y.IsSheaf⟩)
          (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf ⟨Y.presheaf, Y.IsSheaf⟩).obj)).unit.app
            (_root_.PresheafOfModules.tensorObj A.val B.val)) U (a ⊗ₜ b)) =
      Hom.app ((PresheafOfModules.sheafificationAdjunction
        (R := Stacks.SheafOfModules.Tensor.ringSheaf ⟨X.presheaf, X.IsSheaf⟩)
        (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf ⟨X.presheaf, X.IsSheaf⟩).obj)).unit.app
          (_root_.PresheafOfModules.tensorObj ((pullbackFunctor f).obj A).val
            ((pullbackFunctor f).obj B).val))
        ((opensMap f).op.obj U) (pullbackUnit f A U a ⊗ₜ pullbackUnit f B U b) :=
  comparison_homEquiv_unit_tmul f A B U a b

end Consequences

end Stacks.RingedSpace
