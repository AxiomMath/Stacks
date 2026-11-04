module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InvertibleDualEvaluation
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackTensorComparison
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorPowerCoherence
public import StacksFrontier.AlgebraicGeometry.Descent.PullbackSectionsSheaf.UnitComparison
public import StacksFrontier.AlgebraicGeometry.InvertibleDual.Basic
public import StacksFrontier.AlgebraicGeometry.InvertibleTrivialization.Sheaf

/-!
# The evaluation pairing of an invertible module sheaf, and uniqueness of tensor inverses

Let `(X, 𝒪_X)` be a ringed space and let `L` be an invertible `𝒪_X`-module. This file proves
that the evaluation pairing

`L^∨ ⊗_{𝒪_X} L ⟶ 𝒪_X`

is an isomorphism, which is the second assertion of
[Stacks, Tag 01CT](https://stacks.math.columbia.edu/tag/01CT) (2) and the last clause of
[Stacks, Tag 0B8K](https://stacks.math.columbia.edu/tag/0B8K): the tensor inverse of `L`
supplied by invertibility *is* the dual `SheafHom(L, 𝒪_X)`. It also records the uniqueness of
tensor inverses that turns this into an identification of any two of them.

The pairing is inverted on an arbitrary ringed site by
`Stacks.SheafOfModules.Invertible.isIso_evaluation` of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/InvertibleDualEvaluation.lean`, whose proof
exhibits the dual as a *left dual* of `L` — Tag 0FNV, applied to the finite free splittings
that Tag 0B8N (b) supplies — and inverts the evaluation of a left dual using that `· ⊗ L` is an
equivalence. What the declarations below add is the instantiation of that at the site of opens
of a ringed space, which is the form the scheme-theoretic consumers apply.

## Main definitions

* `Stacks.SheafOfModules.isoOfTensorIsoUnit`: two tensor inverses of an invertible module sheaf
  are canonically isomorphic. The identification is the one induced by the autoequivalence
  `· ⊗ L`, so it is determined by the two trivializing pairings.
* `Stacks.SheafOfModules.evaluationIsoOfIsInvertible` and
  `Stacks.SheafOfModules.Scheme.evaluationIso`: the evaluation pairing `L^∨ ⊗ L ⟶ 𝒪_X` of an
  invertible module sheaf, read as an isomorphism, on a ringed space and on a scheme.
* `Stacks.RingedSpace.tensorIsoUnitPullback`: a trivializing pairing `A ⊗ B ≅ 𝒪_Y` pulls back
  along a morphism of ringed spaces to a trivializing pairing `f^*A ⊗ f^*B ≅ 𝒪_X`, given that
  the comparison morphism of Tag 01CD is invertible at `(A, B)`.

## Main results

* `Stacks.SheafOfModules.isIso_evaluation_of_isInvertible` and
  `Stacks.SheafOfModules.Scheme.isIso_evaluation_of_isInvertible`: the evaluation pairing of an
  invertible module sheaf with its dual is an isomorphism.

## Implementation notes

**No declaration here carries a Stacks attribute, because the tag is carried where the
statement is general.** Tag 01CT is stated for an arbitrary ringed space, and both of its
clauses hold on an arbitrary ringed site, which is where this development states and tags them:
`Stacks.SheafOfModules.tensorProduct_isInvertible` carries part (1), and
`Stacks.SheafOfModules.Invertible.isIso_evaluation`,
`Stacks.SheafOfModules.Invertible.isIso_tensorSheafBraiding_hom_comp_evaluation` and
`Stacks.SheafOfModules.Invertible.isInvertible_dualSheaf` carry part (2). The declarations below
are those results read on the site of opens of a ringed space, and so repeat no tag.

**The stalks need not be local rings.** A route through the converse half of Tag 0B8M —
invertible implies locally free of rank one — would need that hypothesis: Tag 0B8M exhibits a ringed space
where the converse fails (one point, with a ring of nontrivial Picard group), and this
development proves it only for local stalks, as
`Stacks.SheafOfModules.Invertible.isLocallyTrivial_of_isInvertible`. The site-level route uses no
trivialization of `L` at all, only Tag 0B8N (b), so no locality hypothesis appears in
`isIso_evaluation_of_isInvertible`, in `Scheme.isIso_evaluation_of_isInvertible` or in
`evaluationIsoOfIsInvertible`. What the Stacks source proves Tag 01CT
(2) from is a third argument — the stalkwise one of Tag 0B8K, through finite presentation and
Tag 01CP — and that one is not formalized here.

**Which `IsInvertible`.** `Stacks.SheafOfModules.IsInvertible` of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/TensorInvertible.lean`. That is the class in which
Tags 0B8K and 0B8M are stated and the one whose API — `isInvertible_iff_exists_tensor_iso_unit`
and `tensorLeftFunctor_isEquivalence` — this file consumes throughout. The repository also
carries `AlgebraicGeometry.SheafOfModules.IsInvertible` with the same body; nothing here
identifies the two.

**Why `isoOfTensorIsoUnit` is not `isoTensorPowerNegOne`.**
`Stacks.SheafOfModules.Invertible.isoTensorPowerNegOne` of
`StacksFrontier/AlgebraicGeometry/InvertibleQuotient/Basic.lean` identifies a tensor inverse
with the negative first tensor power, and composing two such identifications gives the same
conclusion; but the tensor powers of Tag 01CU are stated for the *other* `IsInvertible`, so that
route cannot be taken from the hypotheses available here without transporting a witness between
the two classes. The direct form below needs only the autoequivalence that invertibility already
provides, and the braiding of the tensor product sheaf to put the invertible factor on the side
`tensorLeftFunctor` expects.

**What `tensorIsoUnitPullback` is for.** A consumer that needs the pulled-back *pairing* needs
Tag 01CD, and this lemma isolates exactly that input.

**Not every consumer of an invertible module sheaf on a pullback needs the pulled-back
pairing.** For **invertibility of the pullback itself** Tag 01CD is not needed: `Stacks.Modules.isInvertible_pullback`
(`StacksFrontier/AlgebraicGeometry/PullbackInvertible/Basic.lean`) proves that `f^*L` is
invertible for an *arbitrary* morphism of schemes, with no Tag 01CD component and with no tensor
product formed anywhere — it trivializes `L` on a cover by the converse half of Tag 0B8M,
transports the trivializations through `Stacks.Modules.restrictPullbackIso` and
`AlgebraicGeometry.Scheme.Modules.pullbackUnitIso`, and concludes by clause 1 of Tag 0B8M.
Only the pulled-back pairing, not invertibility, depends on Tag 01CD. (Tag 01CD is
proved for morphisms of ringed spaces as `Stacks.RingedSpace.comparisonBifunctorIso`,
`StacksFrontier/AlgebraicGeometry/PullbackTensor/StalkFormula.lean`.)

Concretely, the lemma takes the invertibility of a *single component* of
`Stacks.RingedSpace.comparisonNatTrans` as a hypothesis — the morphism itself, with its
canonicality clause, is already constructed in
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/PullbackTensorComparison.lean` — and the rest,
the pullback of the pairing and the triviality of the pullback of the structure sheaf
(`SheafOfModules.pullbackObjUnitToUnit`), is unconditional. It is left untagged for the same
reason the file it draws on is: Tag 01CD is the hypothesis, not the conclusion.

## References

* [Stacks Project, Tag 01CT](https://stacks.math.columbia.edu/tag/01CT)
* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
* [Stacks Project, Tag 040A](https://stacks.math.columbia.edu/tag/040A) — Tag 01CT on a ringed
  site, which is where both of its clauses are proved.
* [Stacks Project, Tag 0B8K](https://stacks.math.columbia.edu/tag/0B8K)
* [Stacks Project, Tag 0B8M](https://stacks.math.columbia.edu/tag/0B8M)
* [Stacks Project, Tag 0B8N](https://stacks.math.columbia.edu/tag/0B8N) — an invertible module
  is locally a direct summand of a finite free module.
* [Stacks Project, Tag 0FNV](https://stacks.math.columbia.edu/tag/0FNV)
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry
open RingedSpaceModuleAdjunction (modulePullback modulePullbackPushforwardAdjunction
  modulePushforward modulePushforward_isRightAdjoint structureSheafHom)

universe v u w

namespace Stacks.SheafOfModules

section Uniqueness

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (O : Cᵒᵖ ⥤ CommRingCat.{w})
  (hO : Presheaf.IsSheaf J (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf O))
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify J AddCommGrpCat.{w}]

/-- **Two tensor inverses of an invertible sheaf of modules are canonically isomorphic.**

Tensoring by `L` is an autoequivalence, so a sheaf `A` with `A ⊗ L ≅ 𝒪` is recovered from `𝒪` by
its quasi-inverse; two such sheaves are therefore identified through the quasi-inverse of the
structure sheaf. The identification is determined by the two pairings, not chosen: it is the
image of `hA ≪≫ hB.symm` under the quasi-inverse, conjugated by the unit of the equivalence. -/
noncomputable def isoOfTensorIsoUnit
    (L A B : SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO))
      [IsInvertible O hO L]
    (hA : (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ (O)
        (forget₂ CommRingCat RingCat) (hO)⟩).obj (A)).obj (L)) ≅
      SheafOfModules.unit (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO))
    (hB : (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ (O)
        (forget₂ CommRingCat RingCat) (hO)⟩).obj (B)).obj (L)) ≅
      SheafOfModules.unit (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)) :
    A ≅ B :=
  let e := ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
    ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ O (forget₂ CommRingCat RingCat) hO⟩).obj L).asEquivalence
  have hA' : e.functor.obj A ≅ SheafOfModules.unit
    (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO) :=
    tensorSheafBraiding O hO L A ≪≫ hA
  have hB' : e.functor.obj B ≅ SheafOfModules.unit
    (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO) :=
    tensorSheafBraiding O hO L B ≪≫ hB
  e.unitIso.app A ≪≫ e.inverse.mapIso (hA' ≪≫ hB'.symm) ≪≫ (e.unitIso.app B).symm

/-- **A sheaf of modules admitting a trivializing pairing with an invertible sheaf is
invertible.** This is Tag 0B8K (2) ⟹ (1) with the two factors in the order the pairings of the
divisor arguments come in; the braiding supplies the other order. -/
theorem isInvertible_of_tensorIsoUnit
    (L A : SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO))
    (hA : (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ (O)
        (forget₂ CommRingCat RingCat) (hO)⟩).obj (A)).obj (L)) ≅
      SheafOfModules.unit (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)) :
    IsInvertible O hO L :=
  (isInvertible_iff_exists_tensor_iso_unit L).mpr
    ⟨A, ⟨tensorSheafBraiding O hO L A ≪≫ hA⟩⟩

end Uniqueness

section RingedSpace

variable {X : RingedSpace.{u, u}} (L : SheafOfModules.{u} (structureSheafRing X))

/-- **The evaluation pairing of an invertible module sheaf with its dual is an isomorphism**, on
an arbitrary ringed space.

This is `Invertible.isIso_evaluation` — Tag 01CT (2) and Tag 040A (2) on a ringed site — read on
the site of opens of `X`: an invertible module sheaf is locally a direct summand of a finite
free one, which makes its dual a left dual of it, and the evaluation of a left dual is inverted
by the equivalence `· ⊗ L`. Neither a hypothesis on the stalks of `𝒪_X` nor a trivializing
cover of `L` is involved. -/
theorem isIso_evaluation_of_isInvertible
    [IsInvertible X.presheaf (structureSheafRing X).property L] :
    IsIso (evaluation X.presheaf (structureSheafRing X).property L) :=
  Invertible.isIso_evaluation X.presheaf (structureSheafRing X).property L

/-- **The evaluation pairing `L^∨ ⊗ L ≅ 𝒪_X` of an invertible module sheaf**, on a ringed space.
This is the trivializing pairing that identifies the dual as *the* tensor inverse of `L`. -/
noncomputable def evaluationIsoOfIsInvertible
    [IsInvertible X.presheaf (structureSheafRing X).property L] :
    (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨X.presheaf,
        Presheaf.isSheaf_of_isSheaf_comp _ (X.presheaf) (forget₂ CommRingCat RingCat)
        ((structureSheafRing X).property)⟩).obj
        ((dualSheaf X.presheaf (structureSheafRing X).property L))).obj (L)) ≅
      SheafOfModules.unit (Stacks.SheafOfModules.TensorSheafification.structureSheaf X.presheaf
        (structureSheafRing X).property) :=
  have := isIso_evaluation_of_isInvertible L
  asIso (evaluation X.presheaf (structureSheafRing X).property L)

/-- The forward map of `evaluationIsoOfIsInvertible L` is the evaluation pairing
`L^∨ ⊗ L ⟶ 𝒪_X`. -/
@[simp]
theorem evaluationIsoOfIsInvertible_hom
    [IsInvertible X.presheaf (structureSheafRing X).property L] :
    (evaluationIsoOfIsInvertible L).hom =
      evaluation X.presheaf (structureSheafRing X).property L :=
  rfl

end RingedSpace

section Scheme

variable (Y : AlgebraicGeometry.Scheme.{u})
  (L : SheafOfModules.{u} (structureSheafRing Y.toRingedSpace))

/-- The evaluation pairing of an invertible module sheaf with its dual is an isomorphism on a
scheme, a scheme being in particular a ringed space. -/
theorem Scheme.isIso_evaluation_of_isInvertible
    [IsInvertible Y.presheaf (structureSheafRing Y.toRingedSpace).property L] :
    IsIso (evaluation Y.presheaf (structureSheafRing Y.toRingedSpace).property L) :=
  _root_.Stacks.SheafOfModules.isIso_evaluation_of_isInvertible L

/-- **The evaluation pairing `L^∨ ⊗ L ≅ 𝒪_Y` of an invertible module sheaf on a scheme.** -/
noncomputable def Scheme.evaluationIso
    [IsInvertible Y.presheaf (structureSheafRing Y.toRingedSpace).property L] :
    (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨Y.presheaf,
        Presheaf.isSheaf_of_isSheaf_comp _ (Y.presheaf) (forget₂ CommRingCat RingCat)
        ((structureSheafRing Y.toRingedSpace).property)⟩).obj
        ((dualSheaf Y.presheaf (structureSheafRing Y.toRingedSpace).property L))).obj (L)) ≅
      SheafOfModules.unit (Stacks.SheafOfModules.TensorSheafification.structureSheaf Y.presheaf
        (structureSheafRing Y.toRingedSpace).property) :=
  have := Scheme.isIso_evaluation_of_isInvertible Y L
  asIso (evaluation Y.presheaf (structureSheafRing Y.toRingedSpace).property L)

end Scheme

end Stacks.SheafOfModules

namespace Stacks.RingedSpace

/-- **A trivializing pairing pulls back**, given Tag 01CD at the pair being paired.

If `A ⊗_{𝒪_Y} B ≅ 𝒪_Y` and the comparison morphism `f^*(A ⊗ B) ⟶ f^*A ⊗ f^*B` of Tag 01CD is
invertible at `(A, B)`, then `f^*A ⊗_{𝒪_X} f^*B ≅ 𝒪_X`: pull the pairing back and compose with
the comparison and with `SheafOfModules.pullbackObjUnitToUnit`, the identification of the
pullback of the structure sheaf with the structure sheaf, which is invertible for any morphism
of ringed spaces.

This is the form in which Tag 01CD is consumed by the invertible-sheaf arguments: together with
`Stacks.SheafOfModules.isInvertible_of_tensorIsoUnit` it gives Tag 0B8L, and together with the
evaluation pairing above it gives the pairing that identifies the dual of a pullback with the
pullback of the dual. -/
noncomputable def tensorIsoUnitPullback {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)
    (A B : SheafOfModules.{u} (structureSheafRing Y))
    (hAB : (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨Y.sheaf.obj,
        Presheaf.isSheaf_of_isSheaf_comp _ (Y.sheaf.obj) (forget₂ CommRingCat RingCat)
        ((structureSheafRing Y).property)⟩).obj (A)).obj (B)) ≅
      SheafOfModules.unit (Stacks.SheafOfModules.TensorSheafification.structureSheaf Y.sheaf.obj
        (structureSheafRing Y).property))
    (hcomp : IsIso (comparison f A B)) :
    (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨X.sheaf.obj,
        Presheaf.isSheaf_of_isSheaf_comp _ (X.sheaf.obj) (forget₂ CommRingCat RingCat)
        ((structureSheafRing X).property)⟩).obj (((modulePullback f).obj A))).obj
        (((modulePullback f).obj B))) ≅
      SheafOfModules.unit (Stacks.SheafOfModules.TensorSheafification.structureSheaf X.sheaf.obj
        (structureSheafRing X).property) := by
  letI : (_root_.SheafOfModules.pushforward (structureSheafHom f)).IsRightAdjoint :=
    modulePushforward_isRightAdjoint f
  letI : (modulePullback f).IsLeftAdjoint :=
    ⟨_, ⟨modulePullbackPushforwardAdjunction f⟩⟩
  letI : (Opens.map f.hom.base).Final := CategoryTheory.final_of_representablyFlat _
  have hu : IsIso (_root_.SheafOfModules.pullbackObjUnitToUnit (structureSheafHom f)) :=
    inferInstance
  exact (@asIso _ _ _ _ (comparison f A B) hcomp).symm ≪≫ (modulePullback f).mapIso hAB ≪≫
    @asIso _ _ _ _ (_root_.SheafOfModules.pullbackObjUnitToUnit (structureSheafHom f)) hu

end Stacks.RingedSpace

end
