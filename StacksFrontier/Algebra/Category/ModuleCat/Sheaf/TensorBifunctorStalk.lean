module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafificationTensor

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FinitePresentationStalk
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PowerPresentationSequences
public import StacksCore.Tactic.StacksAttribute

/-!
# The stalk of a tensor product of sheaves of modules, for the tensor bifunctor

Let `X` be a topological space, `O♯` a sheaf of commutative rings on it and `F`, `G` sheaves of
`O♯`-modules. Stacks Tag 01CB asserts that the stalk at `x` of `F ⊗_{O♯} G` is
`F_x ⊗_{O♯_x} G_x`.

That comparison is already on this branch, as
  `Stacks.SheafOfModules.TensorStalkRingedSpace.tensorStalkIso`, but for the
*bespoke* tensor product `Stacks.SheafOfModules.TensorStalkRingedSpace.tensorSheaf` of
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorStalkRingedSpace`. Every statement about
  sheaves of modules on a site in this
development instead uses `Stacks.SheafOfModules.Tensor.sheafTensor`, and this file supplies the
comparison for that bifunctor. It contains **no new mathematics**: the two tensor products are
the same construction, so the comparison is transported, not rebuilt. See the implementation
notes for what the transport actually costs, which is not nothing.

## Main definitions

* `PresheafOfModules.ringedSpaceOfSheaf`: a space together with a sheaf of commutative rings on
  it, read as an `AlgebraicGeometry.RingedSpace`. This is the packaging
  `StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorStalkRingedSpace` states its results over.
* `PresheafOfModules.tensorSheafVal`: the tensor product sheaf
  `((Stacks.SheafOfModules.Tensor.sheafTensor Osharp).obj F).obj G`, read as a presheaf of modules
  over the
  presheaf of
  commutative rings `O♯` rather than over the sheaf of rings — the shape
  `PresheafOfModules.stalkMapL` and Mathlib's stalk module structure consume.
* `PresheafOfModules.tensorSheafGerm`: the germ at `x` of the image, in the tensor product
  sheaf, of a pure tensor `m ⊗ n` of sections over a neighbourhood of `x`. These germs span the
  stalk, so they are what the comparison must be computed on.
* `PresheafOfModules.tensorSheafStalkEquiv`: **the comparison**
  `(((Stacks.SheafOfModules.Tensor.sheafTensor Osharp).obj F).obj G)_x ≃ₗ[O♯_x] F_x ⊗_{O♯_x} G_x`.

## Main results

* `PresheafOfModules.tensorSheafGerm_eq`: `tensorSheafGerm` in the
  `PresheafOfModules.tensorSheafUnit` spelling. That abbreviation is what morphisms out of a
  tensor product sheaf — `PresheafOfModules.tensorSheafDesc`, and hence
  `SheafOfModules.GradedAlgebra.generatorMul` — are stated with, so this lemma is the interface
  between the comparison and those maps. It holds by `rfl`.
* `PresheafOfModules.exists_tensorSheafStalkEquiv_of_moduleEq`: the comparison with the three
  stalk module structures left as variables, which is the form in which the transport is
  performed; see the implementation notes.
* `PresheafOfModules.exists_tensorSheafStalkEquiv`: the comparison together with its
  characterisation on `tensorSheafGerm`, in existence form. `tensorSheafStalkEquiv` and
  `PresheafOfModules.tensorSheafStalkEquiv_tensorSheafGerm` are its two halves, extracted the
  way `Stacks.SheafOfModules.TensorStalkRingedSpace.tensorStalkIso` is extracted from
    `Stacks.SheafOfModules.TensorStalkRingedSpace.exists_tensorStalkIso`.
* `PresheafOfModules.tensorSheafStalkEquiv_tensorSheafGerm`: the comparison carries the germ of
  the image of `m ⊗ n` to `germ m ⊗ germ n`. This pins the comparison down, since those germs
  span the stalk.

## Implementation notes

**This is a transport, and the two tensor products agree on the nose.** With
`Y := ringedSpaceOfSheaf O♯`, both of
`Stacks.SheafOfModules.TensorStalkRingedSpace.presheafTensor Y F G = PresheafOfModules.tensorObj F
  G` and
`Stacks.SheafOfModules.TensorStalkRingedSpace.tensorSheaf Y F G =
((Stacks.SheafOfModules.Tensor.sheafTensor Osharp).obj F).obj G` hold by `rfl`, as does
`structureSheafRing Y = CategoryTheory.Sheaf.toRingCat
  J O♯`. So the hand-built
tensor product of Tag 01CB is the one this development uses, before and after sheafification,
and nothing has to be transported along an isomorphism. This extends the deduplication recorded
in `StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorConstructionsAgree`, which identifies
`Stacks.SheafOfModules.TensorStalkRingedSpace.presheafTensor` with `Stacks.tensorObj` and with
  Mathlib's monoidal product, to
the third of the three objectwise-identical copies, `PresheafOfModules.tensorObj`. No fourth
tensor product and no second stalk comparison is introduced here.

**What the transport nevertheless costs: two module structures on one stalk.** The whole of the
work below is that `Stacks.SheafOfModules.TensorStalkRingedSpace.tensorStalkIso` is an
  `O♯_x`-linear equivalence for
`Stacks.SheafOfModules.TensorStalkRingedSpace.stalkModule`, the module structure Tag 01CB builds by
  choosing representatives on
a neighbourhood, whereas every statement in this development — and in particular
`PresheafOfModules.stalkMapL`, `PresheafOfModules.symPowStalkEquiv` and
`Stacks.SheafOfModules.exact_iff_stalkFunctor_map_exact` — uses Mathlib's instance from
`Mathlib/Algebra/Category/ModuleCat/Stalk.lean`, built from the colimit. The two are *equal*,
by `Stacks.SheafOfModules.stalkModule_eq`, and that equality is reused rather than reproved; but
they are not definitionally equal, and the equivalence's codomain `F_x ⊗_{O♯_x} G_x` depends on
them, so the ascribed Mathlib-instance type does not accept `tensorStalkIso` directly.

The equality is therefore discharged by `subst`, in
`exists_tensorSheafStalkEquiv_of_moduleEq`, whose three module structures are *bound variables*
precisely so that `subst` applies to them: the equalities `stalkModule_eq` provides have a
constant on each side, so they can neither be `subst`ed nor — this was tried — rewritten with
`rw`, which fails on the resulting goal with "the target expression is not type-correct under the
`implicit` transparency level". Both hypotheses of
`exists_tensorSheafStalkEquiv_of_moduleEq` are then supplied by `exact`-level unification, which
is defeq-tolerant, and the whole file contains no rewrite across the two spellings.

**No new `@[stacks 01CB]` attribute.** The tag is already carried by
`Stacks.SheafOfModules.TensorStalkRingedSpace.tensorStalkIso`, which is the comparison; the
  declarations here are a bridge to a
second spelling of its statement, not a second proof of it, so tagging them would register one
result twice.

**Universes.** The space, the sheaf of rings and the module sections all live in a single
universe `u`. This is inherited twice over and is not narrowed here: Tag 01CB's whole
development is stated for `AlgebraicGeometry.RingedSpace.{u, u}` and `SheafOfModules.{u}`,
and independently Mathlib's module structure on the stalk of a presheaf of modules exists only
for `X : TopCat.{u}`, `R : X.Presheaf CommRingCat.{u}` and modules in `u`.
`Stacks.SheafOfModules.Tensor.sheafTensor` keeps its two module universes independent, with the
tensor product in
their maximum; here both are `u`, so the explicit universe arguments `.{u, u, u, u, u}` are
written out — left implicit they default to `0` and silently collapse the statement.

**There are two independent proofs of Tag 01CB on this branch, and this file uses the first.**
Besides `Stacks.SheafOfModules.TensorStalkRingedSpace.exists_presheafTensorStalkIso`, the statement
  that the tensor product
commutes with the filtered colimit defining the stalk is proved a second time, independently, in
`StacksDraft.Ch20.Sec26.Tag08BQ`, as
`AlgebraicGeometry.OXModule.presheafTensor_stalk_iso` — there for Mathlib's monoidal product of
presheaves of modules, and with Mathlib's stalk module structure, so that route would not meet
the instance clash above. It was not used, for two reasons. It produces a `ModuleCat`
isomorphism rather than an `≃ₗ`, and its sheafified form
`AlgebraicGeometry.OXModule.stalk_tensor_iso` is stated as a bare `Nonempty`, with no formula on
germs; a comparison with no germ formula is not pinned down and cannot be composed with
`PresheafOfModules.symPowStalkEquiv`, which is itself characterised only on germs. Rebuilding a
germ-characterised `≃ₗ` from its presheaf-level half plus
`AlgebraicGeometry.OXModule.sheafify_stalk_iso` is comparable work to the transport done here.
The duplication is recorded rather than added to: **a third proof must not be written.**

**The import of Tag 01CB.** `StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorStalkRingedSpace`
  carries a forty-module Mathlib
import list with no business in a foundation module, and it is pulled in here — through
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FinitePresentationStalk`, which is imported for
`Stacks.SheafOfModules.stalkModule_eq`. That is the price of reusing the comparison instead of
reproving it, and reproving it is the alternative: the content of
`Stacks.SheafOfModules.TensorStalkRingedSpace.exists_presheafTensorStalkIso` is that the tensor
  product commutes with the
filtered colimit defining the stalk, in the ring and in both module arguments simultaneously,
and pinned Mathlib has no form of that statement. Tag 01CB imports nothing from `StacksDraft`,
so no import cycle is created by a consumer of this file.

## References

* [Stacks Project, Tag 01CB](https://stacks.math.columbia.edu/tag/01CB)
* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA)
* [Stacks Project, Tag 0GMW](https://stacks.math.columbia.edu/tag/0GMW)
-/

@[expose] public section

open CategoryTheory Opposite CategoryTheory.Sheaf TopologicalSpace
open scoped TensorProduct

universe u

namespace PresheafOfModules

variable {X : TopCat.{u}} (Osharp : Sheaf (Opens.grothendieckTopology ↥X) CommRingCat.{u})

/-- A space with a sheaf of commutative rings, read as a ringed space. -/
@[reducible] noncomputable def ringedSpaceOfSheaf : AlgebraicGeometry.RingedSpace.{u, u} where
  carrier := X
  presheaf := Osharp.obj
  IsSheaf := Osharp.property

variable (F G : SheafOfModules.{u} (toRingCat (Opens.grothendieckTopology ↥X) Osharp)) (x : ↥X)

/-- The tensor product sheaf of `F` and `G`, as a presheaf of `Osharp.obj`-modules. -/
@[reducible] noncomputable def tensorSheafVal :
    PresheafOfModules.{u} (Osharp.obj ⋙ forget₂ CommRingCat.{u} RingCat.{u}) :=
  (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Osharp).obj F).obj G).val

/-- The germ at `x` of the image, in the tensor product sheaf, of a pure tensor of sections. -/
noncomputable def tensorSheafGerm (U : Opens ↥X) (hx : x ∈ U)
    (m : F.val.obj (op U)) (n : G.val.obj (op U)) :
    ↑(TopCat.Presheaf.stalk (tensorSheafVal Osharp F G).presheaf x) :=
  TopCat.Presheaf.germ (tensorSheafVal Osharp F G).presheaf U x hx
    (Hom.app ((PresheafOfModules.sheafificationAdjunction (R :=
        Stacks.SheafOfModules.Tensor.ringSheaf Osharp)
        (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf Osharp).obj)).unit.app
      (PresheafOfModules.tensorObj F.val G.val))
      (op U) (m ⊗ₜ[Osharp.obj.obj (op U)] n))

/-- `tensorSheafGerm` in the `PresheafOfModules.tensorSheafUnit` spelling, which is the one
the maps out of a tensor product sheaf are stated with. -/
theorem tensorSheafGerm_eq (U : Opens ↥X) (hx : x ∈ U)
    (m : F.val.obj (op U)) (n : G.val.obj (op U)) :
    tensorSheafGerm Osharp F G x U hx m n =
      TopCat.Presheaf.germ (tensorSheafVal Osharp F G).presheaf U x hx
        ((tensorSheafUnit F G).app (op U) (m ⊗ₜ[Osharp.obj.obj (op U)] n)) := rfl

/-- The comparison, with the three stalk module structures left as variables. -/
theorem exists_tensorSheafStalkEquiv_of_moduleEq
    (iT : Module ↑(TopCat.Presheaf.stalk Osharp.obj x)
      ↑(TopCat.Presheaf.stalk (tensorSheafVal Osharp F G).presheaf x))
    (iF : Module ↑(TopCat.Presheaf.stalk Osharp.obj x)
      ↑(TopCat.Presheaf.stalk F.val.presheaf x))
    (iG : Module ↑(TopCat.Presheaf.stalk Osharp.obj x)
      ↑(TopCat.Presheaf.stalk G.val.presheaf x))
    (hT : Stacks.SheafOfModules.TensorStalkRingedSpace.stalkModule (ringedSpaceOfSheaf Osharp)
      (tensorSheafVal Osharp F G) x = iT)
    (hF : Stacks.SheafOfModules.TensorStalkRingedSpace.stalkModule (ringedSpaceOfSheaf Osharp) F.val
      x = iF)
    (hG : Stacks.SheafOfModules.TensorStalkRingedSpace.stalkModule (ringedSpaceOfSheaf Osharp) G.val
      x = iG) :
    letI := iT; letI := iF; letI := iG;
    ∃ e : ↑(TopCat.Presheaf.stalk (tensorSheafVal Osharp F G).presheaf x)
        ≃ₗ[↑(TopCat.Presheaf.stalk Osharp.obj x)]
          ↑(TopCat.Presheaf.stalk F.val.presheaf x) ⊗[↑(TopCat.Presheaf.stalk Osharp.obj x)]
            ↑(TopCat.Presheaf.stalk G.val.presheaf x),
      ∀ (U : Opens ↥X) (hx : x ∈ U) (m : F.val.obj (op U)) (n : G.val.obj (op U)),
        e (tensorSheafGerm Osharp F G x U hx m n) =
          TopCat.Presheaf.germ F.val.presheaf U x hx m ⊗ₜ
            TopCat.Presheaf.germ G.val.presheaf U x hx n := by
  subst hT
  subst hF
  subst hG
  exact ⟨Stacks.SheafOfModules.TensorStalkRingedSpace.tensorStalkIso (ringedSpaceOfSheaf Osharp) x F
    G,
    fun U hx m n =>
      Stacks.SheafOfModules.TensorStalkRingedSpace.tensorStalkIso_germ (ringedSpaceOfSheaf Osharp) x
        F G U hx m n⟩

/-- There is a linear equivalence between the stalk at `x` of the tensor product of `F` and `G`
and the tensor product of their stalks, sending the germ of `m ⊗ n` to the tensor product of the
germs of `m` and `n`. -/
theorem exists_tensorSheafStalkEquiv :
    ∃ e : ↑(TopCat.Presheaf.stalk (tensorSheafVal Osharp F G).presheaf x)
        ≃ₗ[↑(TopCat.Presheaf.stalk Osharp.obj x)]
          ↑(TopCat.Presheaf.stalk F.val.presheaf x) ⊗[↑(TopCat.Presheaf.stalk Osharp.obj x)]
            ↑(TopCat.Presheaf.stalk G.val.presheaf x),
      ∀ (U : Opens ↥X) (hx : x ∈ U) (m : F.val.obj (op U)) (n : G.val.obj (op U)),
        e (tensorSheafGerm Osharp F G x U hx m n) =
          TopCat.Presheaf.germ F.val.presheaf U x hx m ⊗ₜ
            TopCat.Presheaf.germ G.val.presheaf U x hx n :=
  exists_tensorSheafStalkEquiv_of_moduleEq Osharp F G x _ _ _
    (Stacks.SheafOfModules.stalkModule_eq (ringedSpaceOfSheaf Osharp)
      (tensorSheafVal Osharp F G) x)
    (Stacks.SheafOfModules.stalkModule_eq (ringedSpaceOfSheaf Osharp) F.val x)
    (Stacks.SheafOfModules.stalkModule_eq (ringedSpaceOfSheaf Osharp) G.val x)

/-- **The stalk of a tensor product of sheaves of modules is the tensor product of the
stalks**, for `Stacks.SheafOfModules.Tensor.sheafTensor`. -/
noncomputable def tensorSheafStalkEquiv :
    ↑(TopCat.Presheaf.stalk (tensorSheafVal Osharp F G).presheaf x)
        ≃ₗ[↑(TopCat.Presheaf.stalk Osharp.obj x)]
      ↑(TopCat.Presheaf.stalk F.val.presheaf x) ⊗[↑(TopCat.Presheaf.stalk Osharp.obj x)]
        ↑(TopCat.Presheaf.stalk G.val.presheaf x) :=
  (exists_tensorSheafStalkEquiv Osharp F G x).choose

/-- The comparison on the germ of a pure tensor of sections. -/
theorem tensorSheafStalkEquiv_tensorSheafGerm (U : Opens ↥X) (hx : x ∈ U)
    (m : F.val.obj (op U)) (n : G.val.obj (op U)) :
    tensorSheafStalkEquiv Osharp F G x (tensorSheafGerm Osharp F G x U hx m n) =
      TopCat.Presheaf.germ F.val.presheaf U x hx m ⊗ₜ
        TopCat.Presheaf.germ G.val.presheaf U x hx n :=
  (exists_tensorSheafStalkEquiv Osharp F G x).choose_spec U hx m n

end PresheafOfModules

end
