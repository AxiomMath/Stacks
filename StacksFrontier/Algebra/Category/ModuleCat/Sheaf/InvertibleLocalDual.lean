module

public import Mathlib.CategoryTheory.Sites.PreservesLocallyBijective
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InternalHomRestriction
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InvertibleDualEvaluation
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafHom
public import StacksFrontier.AlgebraicGeometry.InvertibleLocallyFree.Basic
import StacksCore.Tactic.StacksAttribute

/-!
# Invertibility of a sheaf of modules is local: the dual sheaf on a localized site

Let `(C, 𝒪)` be a ringed site, `U` an object of `C` and `M` a sheaf of `𝒪`-modules. This file
runs the Stacks proof of the descent step of
[Stacks, Tag 0B8M](https://stacks.math.columbia.edu/tag/0B8M): the dual sheaf
`M^∨ = SheafHom(M, 𝒪)` commutes with restriction to the localized site `C/U`, **compatibly
with the evaluation pairing** `M^∨ ⊗_𝒪 M ⟶ 𝒪`; local injectivity and local surjectivity of a
morphism of presheaves descend along a family of objects covering the final object; and
therefore **a sheaf of modules invertible on a covering of the final object is invertible.**

That last statement is `Stacks.InvertibleLocallyFree.InvertibleIsLocal`, which until now the
repository carried as an open hypothesis. It is **discharged here**, on an arbitrary site, by
`Stacks.SheafOfModules.invertibleIsLocal`. Its four sheafification hypotheses are automatic on
the site of opens of a topological space; that instantiation, which is the one Tag 0FJN wants,
is `Stacks.SheafOfModules.invertibleIsLocal_opens` in
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/InvertibleLocalSpace.lean`.

## Main definitions

* `Stacks.SheafOfModules.ringedSiteOf`: the ringed site attached to a presheaf of commutative
  rings which is a sheaf, so that the Tag 0E8H isomorphism becomes available in the spellings
  of the tensor-sheafification development.
* `Stacks.SheafOfModules.restrOver` and `Stacks.SheafOfModules.overModule`: the restriction
  functor of Tag 03EM and the restriction of a sheaf of modules, at those spellings.
* `Stacks.SheafOfModules.restrOverTensorIso`, `restrOverUnitIso` and `overModuleValIso`: **the
  monoidal structure of the restriction functor of Tag 03EM**, stated — it carries a pointwise
  tensor product to the pointwise tensor product of the restrictions and the unit to the unit.
* `Stacks.SheafOfModules.dualOverIso`: **the dual sheaf commutes with restriction to a
  localized site**, `M^∨|_U ≅ (M|_U)^∨`. This is Tag 0E8H, `internalHomOverIso`, read at
  `G = 𝒪`.

## Main results

* `Stacks.SheafOfModules.restrOver_map_evaluationPresheaf_eq`: **the evaluation pairing
  commutes with restriction to a localized site**, phrased through the stated isomorphisms
  above. `Stacks.SheafOfModules.restrOver_map_evaluationPresheaf` is the same fact with them
  left implicit; see the implementation notes for why the implicit form is not usable.
* `CategoryTheory.Presheaf.isLocallyInjective_of_coversTop` and
  `CategoryTheory.Presheaf.isLocallySurjective_of_coversTop`: **local injectivity and local
  surjectivity of a morphism of presheaves descend along a family of objects covering the
  final object.** The converse implications are Mathlib's
  `CategoryTheory.Presheaf.isLocallyInjective_whisker` and `isLocallySurjective_whisker`.
* `Stacks.SheafOfModules.isIso_sheafify_map_of_isLocallyBijective`,
  `isLocallyInjective_of_isIso_sheafify_map` and `isLocallySurjective_of_isIso_sheafify_map`:
  sheafification inverts a morphism of presheaves of modules exactly when that morphism is
  locally bijective. This is the content of Tag 05NE's `WEqualsLocallyBijective` in the
  spellings of the tensor-sheafification development, in both directions.
* `Stacks.SheafOfModules.isIso_sheafify_map_evaluationPresheaf_of_isInvertible`: for an
  invertible sheaf of modules sheafification inverts the evaluation pairing. This is Tag
  040A (2), `Stacks.SheafOfModules.Invertible.isIso_evaluation`, restated for the presheaf-level
  `evaluationPresheaf` (the form Tag 0B8K consumes) instead of the sheaf-level `evaluation`.
* `Stacks.SheafOfModules.isIso_sheafify_map_evaluationPresheaf_of_coversTop_isInvertible`:
  sheafification inverts the evaluation pairing of a sheaf of modules invertible on a covering
  of the final object.
* `Stacks.SheafOfModules.invertibleIsLocal`: **the descent step of Tag 0B8M** —
  `Stacks.InvertibleLocallyFree.InvertibleIsLocal`, proved.

## Implementation notes

**Why the monoidal structure of the restriction functor has to be stated.** The argument is
three lines of mathematics: for each member `U` of the covering, the restriction of the
evaluation pairing of `M` is an isomorphism followed by the evaluation pairing of `M|_U`, which
sheafification inverts because `M|_U` is invertible; so the restriction is locally bijective,
local bijectivity descends, and `Stacks.SheafOfModules.isInvertible_of_pairing`
(Tag 0B8K (2) ⟹ (1)) finishes. What makes it nontrivial to write is the first step, and the
obstruction is a transport rather than any mathematics.

`Stacks.SheafOfModules.restrOver_map_evaluationPresheaf` states the compatibility while leaving
the comparison isomorphisms implicit, and its two sides have hom-types that are definitionally
but not syntactically equal: the source is
`(restrOver 𝒪 h𝒪 U hU).obj ((dualSheaf 𝒪 h𝒪 M).val ⊗ M.val)` on the left and
`(restrOver 𝒪 h𝒪 U hU).obj (dualSheaf 𝒪 h𝒪 M).val ⊗ (overModule 𝒪 h𝒪 M U hU).val` on the
right. *Stating* the equation is cheap, because the right-hand side is elaborated against the
expected type coming from the left. *Transporting* along it is not:

* `rw` succeeds but leaves a goal that is not type-correct at `implicit` transparency — the
  implicit object arguments of `Functor.map` are the stale ones — so the `Functor.map_comp`
  that has to follow is refused with an application type mismatch;
* `congrArg`, `Eq.mpr`, `▸`, and a type ascription `show _ ⟶ _ from _` on the morphism each
  exhaust the heartbeat budget at `whnf` or `isDefEq`, as does passing the morphism explicitly
  to a factorization lemma.

What closes it, and what this file now does, is to *name* the comparison isomorphisms —
`restrOverTensorIso`, `restrOverUnitIso`, `overModuleValIso` — and restate the compatibility
through them as `restrOver_map_evaluationPresheaf_eq`. Every object then occurs in the same
spelling on both sides of the equation, so `rw` followed by `Functor.map_comp` goes through
with nothing to rediscover: the definitional identifications are discharged once, inside the
three definitions, where each of them is `Iso.refl` on every module of sections. This file
uses no `set_option`, no `erw`, no incomplete proof and no raised heartbeat budget.

**The module universe.** Everything is at the module universe `max u v` for a site
`C : Type u` with `Category.{v} C`. That is not a choice: the dual sheaf is an instance of the
internal hom of Tag 03EM, a section of which over `U` is a morphism of presheaves of modules
on the slice site `C/U`, whose arrows live in `max u v`. For the site of opens of a
topological space — which is what Tag 0B8M and Tag 0FJN are about — `max u v = u`, so this is
no restriction on the intended consumers.

**Why a `RingedSite` appears.** Tag 0E8H is formalized over `AlgebraicGeometry.RingedSite`,
whose structure sheaf takes values in `CommRingCat`, whereas the invertibility development is
indexed by a presheaf of commutative rings `𝒪` together with the sheaf condition for its
underlying presheaf of *rings*. The two are the same data, and
`Stacks.SheafOfModules.isSheaf_commRingCat` derives the one from the other — the forgetful
functor `CommRingCat ⥤ RingCat` creates limits, so a presheaf of commutative rings is a sheaf
as soon as its underlying presheaf of rings is. So no extra sheaf hypothesis is carried. The
point of `Stacks.SheafOfModules.ringedSiteOf` is that its `ringSheaf` is
`Stacks.SheafOfModules.TensorSheafification.structureSheaf` on the nose.

**Why the evaluation compatibility is `rfl`.** A section of `SheafHom(M, 𝒪)` over `U` is a
morphism on `C/U`, and evaluation reads off its component at the terminal object
`Over.mk (𝟙 U)` of that slice site. Tag 0E8H's isomorphism restricts a local morphism along
`CategoryTheory.Over.iteratedSliceForward`, which carries the terminal object `Over.mk (𝟙 V)`
of `(C/U)/V` to `Over.mk ((𝟙 V).left) = Over.mk (𝟙 V.left)`, the terminal object of
`C/V.left`. So the two evaluations are literally the same component of the same morphism.

**What is not needed for this route.** No comparison between `tensorLeftFunctor` on `(C, J)`
and on `(Over X, J.over X)`, no pseudofunctor `X ↦ SheafOfModules (𝒪.over X)` and no instance
of `CategoryTheory.Pseudofunctor.IsStack`. The implementation notes of
`StacksFrontier/AlgebraicGeometry/InvertibleLocallyFree/Basic.lean` say that `InvertibleIsLocal`
needs effective descent for sheaves of modules; that is true of the route through the three
properties making a functor an equivalence, and it is why that route was abandoned, but the
dual-sheaf route — the source's own — avoids it, and this file takes it.

**What this does not give.** `Stacks.SheafOfModules.StalkwiseInvertibleDescent` is a different
statement, and nothing here bears on it: it descends invertibility from the *stalks* of a
module of finite presentation, not along a covering, and its own implementation notes say so.
So `invertibleIsLocal` does not discharge the `hstalkDescent` hypothesis of
`SheafOfModules.TensorExteriorSymmetricAlgebras.determinant_isInvertible_of_isFlat`; what it
does is unblock the *other* route to Tag 0FJN, the local description `det(F)|_U ≅ ℱ_{det M}`,
whose last step was the locality of invertibility. See the implementation notes of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/ExteriorDeterminantInvertible.lean`.

## References

* [Stacks Project, Tag 0B8M](https://stacks.math.columbia.edu/tag/0B8M)
* [Stacks Project, Tag 0B8K](https://stacks.math.columbia.edu/tag/0B8K)
* [Stacks Project, Tag 040A](https://stacks.math.columbia.edu/tag/040A)
* [Stacks Project, Tag 0E8H](https://stacks.math.columbia.edu/tag/0E8H)
* [Stacks Project, Tag 03EM](https://stacks.math.columbia.edu/tag/03EM)
* [Stacks Project, Tag 05NA](https://stacks.math.columbia.edu/tag/05NA)
* [Stacks Project, Tag 05NE](https://stacks.math.columbia.edu/tag/05NE)
-/

@[expose] public section

open CategoryTheory MonoidalCategory Opposite AlgebraicGeometry

/-! ### Local injectivity and local surjectivity descend along a covering family -/

namespace CategoryTheory.Presheaf

universe w' v' u' v u

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  {A : Type u'} [Category.{v'} A] {FA : A → A → Type*} {CA : A → Type w'}
  [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory.{w'} A FA]
  {F₁ F₂ : Cᵒᵖ ⥤ A} (φ : F₁ ⟶ F₂)

/-- **Local injectivity descends along a family of objects covering the final object.** If the
restriction of `φ` to the localized site over each `Y i` is locally injective, so is `φ`. The
converse is `CategoryTheory.Presheaf.isLocallyInjective_whisker`. -/
lemma isLocallyInjective_of_coversTop {I : Type*} {Y : I → C} (hY : J.CoversTop Y)
    (h : ∀ i, IsLocallyInjective (J.over (Y i))
      (Functor.whiskerLeft (Over.forget (Y i)).op φ)) :
    IsLocallyInjective J φ where
  equalizerSieve_mem {X} x y hxy := by
    refine J.transitive (hY X.unop) _ ?_
    rintro Z f ⟨i, ⟨g⟩⟩
    have hres : φ.app (op Z) (F₁.map f.op x) = φ.app (op Z) (F₁.map f.op y) := by
      rw [NatTrans.naturality_apply, NatTrans.naturality_apply, hxy]
    have key := equalizerSieve_mem (J.over (Y i))
      (Functor.whiskerLeft (Over.forget (Y i)).op φ)
      (X := op (Over.mk g)) (F₁.map f.op x) (F₁.map f.op y) hres
    refine J.superset_covering ?_ key
    intro W r hr
    have hr' : F₁.map r.op (F₁.map f.op x) = F₁.map r.op (F₁.map f.op y) :=
      (Sieve.overEquiv_iff _ _).1 hr
    show F₁.map (r ≫ f).op x = F₁.map (r ≫ f).op y
    simp only [op_comp, F₁.map_comp, ConcreteCategory.comp_apply]
    exact hr'

/-- **Local surjectivity descends along a family of objects covering the final object.** If the
restriction of `φ` to the localized site over each `Y i` is locally surjective, so is `φ`. The
converse is `CategoryTheory.Presheaf.isLocallySurjective_whisker`. -/
lemma isLocallySurjective_of_coversTop {I : Type*} {Y : I → C} (hY : J.CoversTop Y)
    (h : ∀ i, IsLocallySurjective (J.over (Y i))
      (Functor.whiskerLeft (Over.forget (Y i)).op φ)) :
    IsLocallySurjective J φ where
  imageSieve_mem {X} s := by
    refine J.transitive (hY X) _ ?_
    rintro Z f ⟨i, ⟨g⟩⟩
    have key := imageSieve_mem (J.over (Y i))
      (Functor.whiskerLeft (Over.forget (Y i)).op φ)
      (U := op (Over.mk g)) (F₂.map f.op s)
    refine J.superset_covering ?_ key
    intro W r hr
    obtain ⟨t, ht⟩ := (Sieve.overEquiv_iff _ _).1 hr
    refine ⟨t, ?_⟩
    show φ.app (op W) t = F₂.map (r ≫ f).op s
    simp only [op_comp, F₂.map_comp, ConcreteCategory.comp_apply]
    exact ht

end CategoryTheory.Presheaf

namespace Stacks.SheafOfModules

universe v u

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (𝒪 : Cᵒᵖ ⥤ CommRingCat.{max u v})
  (h𝒪 : Presheaf.IsSheaf J (TensorSheafification.structureRingPresheaf 𝒪))

/-! ### The dual sheaf commutes with restriction to a localized site -/

include h𝒪 in
/-- A presheaf of commutative rings whose underlying presheaf of rings is a sheaf is itself a
sheaf, the forgetful functor `CommRingCat ⥤ RingCat` creating limits. This is what makes the
`CommRingCat`-valued sheaf condition that `AlgebraicGeometry.RingedSite` asks for available
from the `RingCat`-valued one that the tensor-sheafification development carries. -/
theorem isSheaf_commRingCat : Presheaf.IsSheaf J 𝒪 :=
  (Presheaf.isSheaf_iff_isSheaf_comp J 𝒪 (forget₂ CommRingCat RingCat)).mpr h𝒪

/-- The ringed site attached to a presheaf of commutative rings which is a sheaf. Its sheaf of
rings is `Stacks.SheafOfModules.TensorSheafification.structureSheaf` on the nose, which is what
makes the Tag 0E8H isomorphism available in the spellings used here. -/
def ringedSiteOf : RingedSite.{u, v, max u v} := ⟨C, J, ⟨𝒪, isSheaf_commRingCat 𝒪 h𝒪⟩⟩

/-- The sheaf of rings of `Stacks.SheafOfModules.ringedSiteOf` is the structure sheaf of the
tensor-sheafification development. -/
theorem ringedSiteOf_ringSheaf :
    (Stacks.SheafOfModules.Tensor.ringSheaf (ringedSiteOf 𝒪 h𝒪).O) =
      TensorSheafification.structureSheaf 𝒪 h𝒪 := rfl

attribute [local instance] monoidalCategoryPresheafOfModules

/-- The sections of the restricted presheaf of rings form a commutative ring. The restricted
ring presheaf of Tag 03EM is spelled `Stacks03EM.ORestr`, which is a plain `def`, so instance
search does not see the commutativity on its own. -/
noncomputable local instance commRingORestrObj (U : C) (V : (Over U)ᵒᵖ) :
    CommRing ((ORestr 𝒪 U).obj V) :=
  inferInstanceAs (CommRing (𝒪.obj (op V.unop.left)))

/-- The restriction functor `j_U^{-1}` of Tag 03EM, written at the spelling of the sheaf of
rings that the tensor-sheafification development uses. It *is* `Stacks03EM.restrFun`; only the
spelling of the source and target categories differs. -/
noncomputable def restrOver (U : C)
    (hU : Presheaf.IsSheaf (J.over U)
      (TensorSheafification.structureRingPresheaf ((Over.forget U).op ⋙ 𝒪))) :
    PresheafOfModules.{max u v} (TensorSheafification.structureSheaf 𝒪 h𝒪).obj ⥤
      PresheafOfModules.{max u v}
        (TensorSheafification.structureSheaf ((Over.forget U).op ⋙ 𝒪) hU).obj :=
  restrFun 𝒪 U

/-- Restriction along `Over.forget U` of the underlying presheaf of abelian groups is
whiskering: the two readings of `Stacks.SheafOfModules.restrOver` agree on the nose. -/
theorem toPresheaf_map_restrOver (U : C)
    (hU : Presheaf.IsSheaf (J.over U)
      (TensorSheafification.structureRingPresheaf ((Over.forget U).op ⋙ 𝒪)))
    {P Q : PresheafOfModules.{max u v} (TensorSheafification.structureSheaf 𝒪 h𝒪).obj}
    (f : P ⟶ Q) :
    (PresheafOfModules.toPresheaf
        (TensorSheafification.structureSheaf ((Over.forget U).op ⋙ 𝒪) hU).obj).map
        ((restrOver 𝒪 h𝒪 U hU).map f) =
      Functor.whiskerLeft (Over.forget U).op
        ((PresheafOfModules.toPresheaf (TensorSheafification.structureSheaf 𝒪 h𝒪).obj).map f) :=
  rfl

/-- The restriction of a sheaf of modules to the localized site over `U`, with its sheaf of
rings spelled as the structure sheaf of the restricted presheaf of commutative rings. It *is*
`SheafOfModules.over`; `Stacks.InvertibleLocallyFree.structureSheaf_over` is the `rfl` that
makes the two spellings interchangeable, but only at default transparency, which is why the
spelling is fixed once here. -/
noncomputable def overModule
    (M : SheafOfModules.{max u v} (TensorSheafification.structureSheaf 𝒪 h𝒪)) (U : C)
    (hU : Presheaf.IsSheaf (J.over U)
      (TensorSheafification.structureRingPresheaf ((Over.forget U).op ⋙ 𝒪))) :
    SheafOfModules.{max u v}
      (TensorSheafification.structureSheaf ((Over.forget U).op ⋙ 𝒪) hU) :=
  M.over U

/-- **Stacks Project, Tag 0E8H at `G = 𝒪`: the dual sheaf commutes with restriction to a
localized site.** The restriction of `M^∨ = SheafHom(M, 𝒪)` to `C/U` is the dual of the
restriction of `M`. -/
noncomputable def dualOverIso (M : SheafOfModules.{max u v}
      (TensorSheafification.structureSheaf 𝒪 h𝒪)) (U : C)
    (hU : Presheaf.IsSheaf (J.over U)
      (TensorSheafification.structureRingPresheaf ((Over.forget U).op ⋙ 𝒪))) :
    (restrOver 𝒪 h𝒪 U hU).obj (dualSheaf 𝒪 h𝒪 M).val ≅
      (dualSheaf ((Over.forget U).op ⋙ 𝒪) hU (overModule 𝒪 h𝒪 M U hU)).val :=
  InternalHom.internalHomOverIso (ringedSiteOf 𝒪 h𝒪) U M
    (SheafOfModules.unit (TensorSheafification.structureSheaf 𝒪 h𝒪))

/-- **The evaluation pairing commutes with restriction to a localized site.** Under
`Stacks.SheafOfModules.dualOverIso` the restriction of the evaluation pairing of `M` is the
evaluation pairing of `M|_U`.

Both sides read off the component of a local morphism at the terminal object of a slice site,
and `CategoryTheory.Over.iteratedSliceForward` carries the terminal object of `(C/U)/V` to
that of `C/V.left`; so the two sides are the same component of the same morphism. -/
theorem restrOver_map_evaluationPresheaf
    (M : SheafOfModules.{max u v} (TensorSheafification.structureSheaf 𝒪 h𝒪)) (U : C)
    (hU : Presheaf.IsSheaf (J.over U)
      (TensorSheafification.structureRingPresheaf ((Over.forget U).op ⋙ 𝒪))) :
    (restrOver 𝒪 h𝒪 U hU).map (evaluationPresheaf 𝒪 h𝒪 M) =
      (dualOverIso 𝒪 h𝒪 M U hU).hom ▷ (overModule 𝒪 h𝒪 M U hU).val ≫
        evaluationPresheaf ((Over.forget U).op ⋙ 𝒪) hU (overModule 𝒪 h𝒪 M U hU) := by
  refine PresheafOfModules.hom_ext fun V => ?_
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro α x
  rfl

/-! ### The restriction functor is monoidal

The three isomorphisms below are the *stated* monoidal structure of the restriction functor of
Tag 03EM: it carries a pointwise tensor product to the pointwise tensor product of the
restrictions, and the unit to the unit. Each one holds by `Iso.refl` on every section module;
what matters is that it is a named morphism, so that the definitional identifications are
discharged once, here, and every later rewriting happens along a morphism rather than along a
definitional equality the elaborator has to rediscover.

Following Mathlib's `PresheafOfModules.pushforward₀OfCommRingCat`, whose monoidal structure is
built the same way, the components are given by `PresheafOfModules.isoMk` rather than by
`Iso.refl` on the whole presheaf of modules: a single `Iso.refl` at the level of presheaves of
modules is accepted by the elaborator but is expensive for the kernel. -/

/-- **The restriction functor of Tag 03EM commutes with the pointwise tensor product.** This is
the comparison isomorphism of the monoidal structure of
`Stacks.SheafOfModules.restrOver`; it is `Iso.refl` on each module of sections, because both
sides have `A(V) ⊗_{𝒪(V)} B(V)` there. -/
noncomputable def restrOverTensorIso (U : C)
    (hU : Presheaf.IsSheaf (J.over U)
      (TensorSheafification.structureRingPresheaf ((Over.forget U).op ⋙ 𝒪)))
    (A B : PresheafOfModules.{max u v} (TensorSheafification.structureSheaf 𝒪 h𝒪).obj) :
    (restrOver 𝒪 h𝒪 U hU).obj (A ⊗ B) ≅
      (restrOver 𝒪 h𝒪 U hU).obj A ⊗ (restrOver 𝒪 h𝒪 U hU).obj B :=
  PresheafOfModules.isoMk (fun _ => Iso.refl _)
    (fun _ _ _ => ModuleCat.MonoidalCategory.tensor_ext fun _ _ => rfl)

/-- **The restriction functor of Tag 03EM carries the unit to the unit.** The unit of the
pointwise tensor product is the structure sheaf viewed as a module over itself, and restricting
it gives the restricted structure sheaf. -/
noncomputable def restrOverUnitIso (U : C)
    (hU : Presheaf.IsSheaf (J.over U)
      (TensorSheafification.structureRingPresheaf ((Over.forget U).op ⋙ 𝒪))) :
    (restrOver 𝒪 h𝒪 U hU).obj
        (SheafOfModules.unit (TensorSheafification.structureSheaf 𝒪 h𝒪)).val ≅
      (SheafOfModules.unit
        (TensorSheafification.structureSheaf ((Over.forget U).op ⋙ 𝒪) hU)).val :=
  PresheafOfModules.isoMk (fun _ => Iso.refl _) (fun _ _ _ => rfl)

/-- The restriction of a sheaf of modules, read through the restriction functor of Tag 03EM, is
`Stacks.SheafOfModules.overModule`. The two spellings agree on every module of sections. -/
noncomputable def overModuleValIso
    (M : SheafOfModules.{max u v} (TensorSheafification.structureSheaf 𝒪 h𝒪)) (U : C)
    (hU : Presheaf.IsSheaf (J.over U)
      (TensorSheafification.structureRingPresheaf ((Over.forget U).op ⋙ 𝒪))) :
    (restrOver 𝒪 h𝒪 U hU).obj M.val ≅ (overModule 𝒪 h𝒪 M U hU).val :=
  PresheafOfModules.isoMk (fun _ => Iso.refl _) (fun _ _ _ => rfl)

/-- **The restriction of `M^∨ ⊗ M` is `(M|_U)^∨ ⊗ M|_U`**: the monoidal comparison
`Stacks.SheafOfModules.restrOverTensorIso` followed by Tag 0E8H on the left factor and by the
identification of the two spellings of `M|_U` on the right. -/
noncomputable def restrOverDualTensorIso
    (M : SheafOfModules.{max u v} (TensorSheafification.structureSheaf 𝒪 h𝒪)) (U : C)
    (hU : Presheaf.IsSheaf (J.over U)
      (TensorSheafification.structureRingPresheaf ((Over.forget U).op ⋙ 𝒪))) :
    (restrOver 𝒪 h𝒪 U hU).obj ((dualSheaf 𝒪 h𝒪 M).val ⊗ M.val) ≅
      (dualSheaf ((Over.forget U).op ⋙ 𝒪) hU (overModule 𝒪 h𝒪 M U hU)).val ⊗
        (overModule 𝒪 h𝒪 M U hU).val :=
  restrOverTensorIso 𝒪 h𝒪 U hU (dualSheaf 𝒪 h𝒪 M).val M.val ≪≫
    tensorIso (dualOverIso 𝒪 h𝒪 M U hU) (overModuleValIso 𝒪 h𝒪 M U hU)

/-- **The evaluation pairing commutes with restriction to a localized site**, phrased through
the stated isomorphisms rather than through a definitional equality: the restriction of the
evaluation pairing of `M` is `Stacks.SheafOfModules.restrOverDualTensorIso`, the evaluation
pairing of `M|_U`, and the inverse of `Stacks.SheafOfModules.restrOverUnitIso`.

Every object occurring here is spelled the same way on both sides of the equation, so using
this equation — as a rewrite, or through a factorization lemma — needs no transport. That is
the whole point of the stated monoidal structure;
`Stacks.SheafOfModules.restrOver_map_evaluationPresheaf` is the same fact with the
isomorphisms left implicit, and the implementation notes of this file record, with the
measurements, why transporting along that form is not affordable. -/
theorem restrOver_map_evaluationPresheaf_eq
    (M : SheafOfModules.{max u v} (TensorSheafification.structureSheaf 𝒪 h𝒪)) (U : C)
    (hU : Presheaf.IsSheaf (J.over U)
      (TensorSheafification.structureRingPresheaf ((Over.forget U).op ⋙ 𝒪))) :
    (restrOver 𝒪 h𝒪 U hU).map (evaluationPresheaf 𝒪 h𝒪 M) =
      (restrOverDualTensorIso 𝒪 h𝒪 M U hU).hom ≫
        evaluationPresheaf ((Over.forget U).op ⋙ 𝒪) hU (overModule 𝒪 h𝒪 M U hU) ≫
          (restrOverUnitIso 𝒪 h𝒪 U hU).inv := by
  refine PresheafOfModules.hom_ext fun V => ?_
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro α x
  rfl

/-! ### Sheafification inverts a morphism exactly when it is locally bijective -/

section Sheafification

variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
  [HasWeakSheafify J AddCommGrpCat.{max u v}]

/-- Sheafification inverts a locally bijective morphism of presheaves of modules. This is the
argument of `Stacks.SheafOfModules.isIso_sheafify_map_evaluationPresheaf`, for an arbitrary
morphism. -/
theorem isIso_sheafify_map_of_isLocallyBijective
    {P Q : PresheafOfModules.{max u v} (TensorSheafification.structureSheaf 𝒪 h𝒪).obj}
    (f : P ⟶ Q)
    (hinj : Presheaf.IsLocallyInjective J
      ((PresheafOfModules.toPresheaf (TensorSheafification.structureSheaf 𝒪 h𝒪).obj).map f))
    (hsurj : Presheaf.IsLocallySurjective J
      ((PresheafOfModules.toPresheaf (TensorSheafification.structureSheaf 𝒪 h𝒪).obj).map f)) :
    IsIso ((TensorSheafification.sheafify 𝒪 h𝒪).map f) := by
  have := hinj
  have := hsurj
  rw [← isIso_iff_of_reflects_iso _
    (SheafOfModules.toSheaf (TensorSheafification.structureSheaf 𝒪 h𝒪))]
  exact (J.W_iff _).mp (J.W_of_isLocallyBijective
    ((PresheafOfModules.toPresheaf (TensorSheafification.structureSheaf 𝒪 h𝒪).obj).map f))

/-- A morphism of presheaves of modules which sheafification inverts is in `J.W`. -/
private theorem W_of_isIso_sheafify_map
    {P Q : PresheafOfModules.{max u v} (TensorSheafification.structureSheaf 𝒪 h𝒪).obj}
    (f : P ⟶ Q) (h : IsIso ((TensorSheafification.sheafify 𝒪 h𝒪).map f)) :
    J.W
      ((PresheafOfModules.toPresheaf (TensorSheafification.structureSheaf 𝒪 h𝒪).obj).map f) := by
  have h2 : IsIso ((SheafOfModules.toSheaf (TensorSheafification.structureSheaf 𝒪 h𝒪)).map
      ((TensorSheafification.sheafify 𝒪 h𝒪).map f)) := by
    let := h; infer_instance
  exact (J.W_iff _).mpr h2

/-- Conversely, a morphism of presheaves of modules which sheafification inverts is locally
injective. -/
theorem isLocallyInjective_of_isIso_sheafify_map
    {P Q : PresheafOfModules.{max u v} (TensorSheafification.structureSheaf 𝒪 h𝒪).obj}
    (f : P ⟶ Q) (h : IsIso ((TensorSheafification.sheafify 𝒪 h𝒪).map f)) :
    Presheaf.IsLocallyInjective J
      ((PresheafOfModules.toPresheaf (TensorSheafification.structureSheaf 𝒪 h𝒪).obj).map f) :=
  (W_of_isIso_sheafify_map 𝒪 h𝒪 f h).isLocallyInjective

/-- Conversely, a morphism of presheaves of modules which sheafification inverts is locally
surjective. -/
theorem isLocallySurjective_of_isIso_sheafify_map
    {P Q : PresheafOfModules.{max u v} (TensorSheafification.structureSheaf 𝒪 h𝒪).obj}
    (f : P ⟶ Q) (h : IsIso ((TensorSheafification.sheafify 𝒪 h𝒪).map f)) :
    Presheaf.IsLocallySurjective J
      ((PresheafOfModules.toPresheaf (TensorSheafification.structureSheaf 𝒪 h𝒪).obj).map f) :=
  (W_of_isIso_sheafify_map 𝒪 h𝒪 f h).isLocallySurjective

end Sheafification

/-! ### Invertibility makes sheafification invert the evaluation pairing -/

section Evaluation

variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
  [HasWeakSheafify J AddCommGrpCat.{max u v}]
  [∀ V : C, HasWeakSheafify (J.over V) AddCommGrpCat.{max u v}]
  [∀ V : C, (J.over V).WEqualsLocallyBijective AddCommGrpCat.{max u v}]

/-- **Tag 040A (2) in the form Tag 0B8K consumes.** For an invertible sheaf of modules,
sheafification inverts the presheaf-level evaluation pairing `M^∨ ⊗ M ⟶ 𝒪`. The sheaf-level
statement is `Stacks.SheafOfModules.Invertible.isIso_evaluation`; the two differ by the counit
of the sheafification adjunction, which is an isomorphism because sheaves of modules are a
reflective subcategory. -/
@[ega "0 5.4.3" "more general"]
theorem isIso_sheafify_map_evaluationPresheaf_of_isInvertible
    (M : SheafOfModules.{max u v} (TensorSheafification.structureSheaf 𝒪 h𝒪))
    [IsInvertible 𝒪 h𝒪 M] :
    IsIso ((TensorSheafification.sheafify 𝒪 h𝒪).map (evaluationPresheaf 𝒪 h𝒪 M)) := by
  have he : IsIso (evaluation 𝒪 h𝒪 M) := Invertible.isIso_evaluation 𝒪 h𝒪 M
  rw [show evaluation 𝒪 h𝒪 M =
      (TensorSheafification.sheafify 𝒪 h𝒪).map (evaluationPresheaf 𝒪 h𝒪 M) ≫
        (TensorSheafification.sheafifyAdjunction 𝒪 h𝒪).counit.app
          (SheafOfModules.unit (TensorSheafification.structureSheaf 𝒪 h𝒪)) from
    (TensorSheafification.sheafifyAdjunction 𝒪 h𝒪).homEquiv_counit _ _ _] at he
  have hc : IsIso ((TensorSheafification.sheafifyAdjunction 𝒪 h𝒪).counit) :=
    inferInstanceAs (IsIso (PresheafOfModules.sheafificationAdjunction
      (𝟙 (TensorSheafification.structureSheaf 𝒪 h𝒪).obj)).counit)
  have hca : IsIso ((TensorSheafification.sheafifyAdjunction 𝒪 h𝒪).counit.app
      (SheafOfModules.unit (TensorSheafification.structureSheaf 𝒪 h𝒪))) :=
    @NatIso.isIso_app_of_isIso _ _ _ _ _ _ _ hc _
  exact @IsIso.of_isIso_comp_right _ _ _ _ _ _ _ hca he

omit [J.WEqualsLocallyBijective AddCommGrpCat] [HasWeakSheafify J AddCommGrpCat] in
/-- **Sheafification on the localized site inverts the restriction of the evaluation pairing**,
as soon as `M|_U` is invertible. This is Tag 040A (2) on `C/U` transported to `C` along the
stated monoidal structure of the restriction functor. -/
theorem isIso_sheafify_map_restrOver_map_evaluationPresheaf
    (M : SheafOfModules.{max u v} (TensorSheafification.structureSheaf 𝒪 h𝒪)) (U : C)
    (hU : Presheaf.IsSheaf (J.over U)
      (TensorSheafification.structureRingPresheaf ((Over.forget U).op ⋙ 𝒪)))
    (hM : IsInvertible ((Over.forget U).op ⋙ 𝒪) hU (overModule 𝒪 h𝒪 M U hU)) :
    IsIso ((TensorSheafification.sheafify ((Over.forget U).op ⋙ 𝒪) hU).map
      ((restrOver 𝒪 h𝒪 U hU).map (evaluationPresheaf 𝒪 h𝒪 M))) := by
  have := hM
  have h1 : IsIso ((TensorSheafification.sheafify ((Over.forget U).op ⋙ 𝒪) hU).map
      (restrOverDualTensorIso 𝒪 h𝒪 M U hU).hom) :=
    ((TensorSheafification.sheafify ((Over.forget U).op ⋙ 𝒪) hU).mapIso
      (restrOverDualTensorIso 𝒪 h𝒪 M U hU)).isIso_hom
  have h2 : IsIso ((TensorSheafification.sheafify ((Over.forget U).op ⋙ 𝒪) hU).map
      (evaluationPresheaf ((Over.forget U).op ⋙ 𝒪) hU (overModule 𝒪 h𝒪 M U hU))) :=
    isIso_sheafify_map_evaluationPresheaf_of_isInvertible ((Over.forget U).op ⋙ 𝒪) hU
      (overModule 𝒪 h𝒪 M U hU)
  have h3 : IsIso ((TensorSheafification.sheafify ((Over.forget U).op ⋙ 𝒪) hU).map
      (restrOverUnitIso 𝒪 h𝒪 U hU).inv) :=
    ((TensorSheafification.sheafify ((Over.forget U).op ⋙ 𝒪) hU).mapIso
      (restrOverUnitIso 𝒪 h𝒪 U hU)).isIso_inv
  rw [restrOver_map_evaluationPresheaf_eq 𝒪 h𝒪 M U hU, Functor.map_comp, Functor.map_comp]
  exact @IsIso.comp_isIso _ _ _ _ _ _ _ h1 (@IsIso.comp_isIso _ _ _ _ _ _ _ h2 h3)

/-! ### Invertibility is local -/

omit [J.WEqualsLocallyBijective AddCommGrpCat] [HasWeakSheafify J AddCommGrpCat] in
/-- A morphism of presheaves of modules whose restriction to `C/U` is inverted by sheafification
there is locally injective on the localized site, in the form that
`CategoryTheory.Presheaf.isLocallyInjective_of_coversTop` consumes. -/
theorem isLocallyInjective_whiskerLeft_of_isIso_sheafify_map_restrOver (U : C)
    (hU : Presheaf.IsSheaf (J.over U)
      (TensorSheafification.structureRingPresheaf ((Over.forget U).op ⋙ 𝒪)))
    {P Q : PresheafOfModules.{max u v} (TensorSheafification.structureSheaf 𝒪 h𝒪).obj}
    (f : P ⟶ Q)
    (h : IsIso ((TensorSheafification.sheafify ((Over.forget U).op ⋙ 𝒪) hU).map
      ((restrOver 𝒪 h𝒪 U hU).map f))) :
    Presheaf.IsLocallyInjective (J.over U)
      (Functor.whiskerLeft (Over.forget U).op
        ((PresheafOfModules.toPresheaf (TensorSheafification.structureSheaf 𝒪 h𝒪).obj).map f)) :=
  isLocallyInjective_of_isIso_sheafify_map ((Over.forget U).op ⋙ 𝒪) hU
    ((restrOver 𝒪 h𝒪 U hU).map f) h

omit [J.WEqualsLocallyBijective AddCommGrpCat] [HasWeakSheafify J AddCommGrpCat] in
/-- A morphism of presheaves of modules whose restriction to `C/U` is inverted by sheafification
there is locally surjective on the localized site, in the form that
`CategoryTheory.Presheaf.isLocallySurjective_of_coversTop` consumes. -/
theorem isLocallySurjective_whiskerLeft_of_isIso_sheafify_map_restrOver (U : C)
    (hU : Presheaf.IsSheaf (J.over U)
      (TensorSheafification.structureRingPresheaf ((Over.forget U).op ⋙ 𝒪)))
    {P Q : PresheafOfModules.{max u v} (TensorSheafification.structureSheaf 𝒪 h𝒪).obj}
    (f : P ⟶ Q)
    (h : IsIso ((TensorSheafification.sheafify ((Over.forget U).op ⋙ 𝒪) hU).map
      ((restrOver 𝒪 h𝒪 U hU).map f))) :
    Presheaf.IsLocallySurjective (J.over U)
      (Functor.whiskerLeft (Over.forget U).op
        ((PresheafOfModules.toPresheaf (TensorSheafification.structureSheaf 𝒪 h𝒪).obj).map f)) :=
  isLocallySurjective_of_isIso_sheafify_map ((Over.forget U).op ⋙ 𝒪) hU
    ((restrOver 𝒪 h𝒪 U hU).map f) h

/-- **Sheafification inverts the evaluation pairing of a sheaf of modules which is invertible on
a covering of the final object.** For each member `U` of the covering the restriction of the
pairing is inverted by sheafification on `C/U`, by
`Stacks.SheafOfModules.isIso_sheafify_map_restrOver_map_evaluationPresheaf`; so it is locally
bijective there, and local bijectivity descends. -/
theorem isIso_sheafify_map_evaluationPresheaf_of_coversTop_isInvertible
    (M : SheafOfModules.{max u v} (TensorSheafification.structureSheaf 𝒪 h𝒪))
    {I : Type*} {X : I → C} (hX : J.CoversTop X)
    (hU : ∀ i, Presheaf.IsSheaf (J.over (X i))
      (TensorSheafification.structureRingPresheaf ((Over.forget (X i)).op ⋙ 𝒪)))
    (hM : ∀ i, IsInvertible ((Over.forget (X i)).op ⋙ 𝒪) (hU i)
      (overModule 𝒪 h𝒪 M (X i) (hU i))) :
    IsIso ((TensorSheafification.sheafify 𝒪 h𝒪).map (evaluationPresheaf 𝒪 h𝒪 M)) := by
  have key : ∀ i, IsIso ((TensorSheafification.sheafify ((Over.forget (X i)).op ⋙ 𝒪) (hU i)).map
      ((restrOver 𝒪 h𝒪 (X i) (hU i)).map (evaluationPresheaf 𝒪 h𝒪 M))) := fun i =>
    isIso_sheafify_map_restrOver_map_evaluationPresheaf 𝒪 h𝒪 M (X i) (hU i) (hM i)
  refine isIso_sheafify_map_of_isLocallyBijective 𝒪 h𝒪 (evaluationPresheaf 𝒪 h𝒪 M)
    (Presheaf.isLocallyInjective_of_coversTop J _ hX fun i =>
      isLocallyInjective_whiskerLeft_of_isIso_sheafify_map_restrOver 𝒪 h𝒪 (X i) (hU i) _ (key i))
    (Presheaf.isLocallySurjective_of_coversTop J _ hX fun i =>
      isLocallySurjective_whiskerLeft_of_isIso_sheafify_map_restrOver 𝒪 h𝒪 (X i) (hU i) _ (key i))

attribute [local instance] symmetricCategoryPresheafOfModules

/-- **Invertibility of a sheaf of modules is local on the site.** A sheaf of `𝒪`-modules
invertible on every member of a covering of the final object is invertible.

This discharges `Stacks.InvertibleLocallyFree.InvertibleIsLocal`, which until now was carried
as a hypothesis. The proof is the Stacks Project's own, from the proof of Tag 0B8M: the dual
sheaf `M^∨` is a *global* construction, its evaluation pairing `M^∨ ⊗ M ⟶ 𝒪` commutes with
restriction to a localized site (Tag 0E8H, through
`Stacks.SheafOfModules.restrOver_map_evaluationPresheaf_eq`), sheafification inverts the
restricted pairing on each member of the covering because `M|_U` is invertible there (Tag
040A (2)), local bijectivity descends along the covering, and Tag 0B8K (2) ⟹ (1) turns the
resulting pairing into invertibility. No descent theory for sheaves of modules is used.

No Stacks attribute is attached: this is a step inside the proof of Tag 0B8M, not a clause of
it, and clause 1 of that tag is already carried unconditionally by
`StacksFrontier/AlgebraicGeometry/InvertibleLocallyFree/DualBasis.lean`. -/
theorem invertibleIsLocal : Stacks.InvertibleLocallyFree.InvertibleIsLocal 𝒪 h𝒪 := by
  intro M I X hX hM
  have hev : IsIso ((TensorSheafification.sheafify 𝒪 h𝒪).map (evaluationPresheaf 𝒪 h𝒪 M)) :=
    isIso_sheafify_map_evaluationPresheaf_of_coversTop_isInvertible 𝒪 h𝒪 M hX
      (fun i => Stacks.InvertibleLocallyFree.isSheaf_over 𝒪 h𝒪 (X i)) hM
  have hbr : IsIso ((TensorSheafification.sheafify 𝒪 h𝒪).map
    (braidingVal 𝒪 h𝒪 M (dualSheaf 𝒪 h𝒪 M)).inv) := inferInstance
  exact isInvertible_of_pairing M (dualSheaf 𝒪 h𝒪 M) (evaluationPresheaf 𝒪 h𝒪 M)
    ((braidingVal 𝒪 h𝒪 M (dualSheaf 𝒪 h𝒪 M)).inv ≫ evaluationPresheaf 𝒪 h𝒪 M) hev
    (isIso_sheafify_map_comp 𝒪 h𝒪 _ _ hbr hev)

end Evaluation

end Stacks.SheafOfModules

end
