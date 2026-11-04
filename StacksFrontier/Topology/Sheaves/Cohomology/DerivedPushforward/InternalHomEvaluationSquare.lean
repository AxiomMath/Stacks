module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedCurryingSourceNaturality
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.InternalHomPushforwardMap
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedCurryingOnARingedSpace
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Modules.CohomologyOfModules

/-!
# The evaluation square for the pushforward of a derived internal hom

Let `f : (X, 𝒪_X) ⟶ (Y, 𝒪_Y)` be a morphism of ringed spaces and let `K, M ∈ D(𝒪_X)`.  The
square

```
Rf_*R𝓗om_{𝒪_X}(K, M) ⊗^L_{𝒪_Y} Rf_*K ⟶ Rf_*(R𝓗om_{𝒪_X}(K, M) ⊗^L_{𝒪_X} K)
            │                                          │
            ▼                                          ▼
R𝓗om_{𝒪_Y}(Rf_*K, Rf_*M) ⊗^L_{𝒪_Y} Rf_*K ⟶            Rf_*M
```

commutes.  The top arrow is the relative cup product of Stacks 0B68, the left arrow is the
canonical map `Rf_*R𝓗om(K, M) ⟶ R𝓗om(Rf_*K, Rf_*M)` of Stacks 0B69 tensored with the identity
of `Rf_*K`, and the two remaining arrows are the evaluation
`R𝓗om(A, B) ⊗^L A ⟶ B` of Stacks 0A8V — on `X`, pushed forward, for the right arrow, and on `Y`
for the bottom arrow.  This is Stacks 0G7A.

The source states the remark for `K, M ∈ D(𝒪_Y)`, which is a slip: the diagram applies both
`R𝓗om_{𝒪_X}` and `Rf_*` to `K` and `M`, so the arrows type-check only for `K, M ∈ D(𝒪_X)`, and
that is the form below.

## Main definitions

* `Stacks.Cohomology.DerivedInternalHomEvaluation.TensorEquivIsEvaluation`: the property of a
  ringed space that the tensor–internal-hom bijection of Stacks 08DI is given by tensoring with
  the identity and then evaluating, i.e. that the bijection is determined by its value at an
  identity map.

## Main results

* `Stacks.Cohomology.DerivedInternalHomEvaluation.tensorEquivIsEvaluation`: every ringed space
  has that property.
* `Stacks.Cohomology.DerivedInternalHomEvaluation.tensorMap_pushforwardSheafHomMap_sheafHomEval`
  (Stacks 0G7A): the square above commutes.

## Implementation notes

*What the square says.*  The top arrow followed by the right one is by construction the
transpose datum `Rf_*R𝓗om(K, M) ⊗^L_{𝒪_Y} Rf_*K ⟶ Rf_*M` from which the map of Stacks 0B69 is
built, namely
`Stacks.Cohomology.DerivedInternalHomPushforward.pushforwardSheafHomDatum`.  So the content of
the square is that transposing that datum and then tensoring with the identity and evaluating
returns it — the triangle expressing that the bijection of Stacks 08DI is an adjunction
isomorphism, specialized to the datum of Stacks 0B69.

*Where the content comes from.*  That triangle is the naturality of the bijection of
Stacks 08DI in its first variable, evaluated at an identity; conversely the naturality follows
from it.  That naturality is the source clause of Stacks 08J8,
`AlgebraicGeometry.RingedSite.derivedCurryHomEquiv_naturality_source`, read at the identity
of `R𝓗om(B, C)` — whose image under the bijection is exactly the evaluation of Stacks 0A8V.
The clause is stated for a ringed site, and a ringed space *is* a ringed site, so it applies
verbatim; what `tensorEquivIsEvaluation` adds is the naturality of the comparison
`Stacks.Cohomology.DerivedKunnethExt.tensorBridge` of the two derived tensor products, which
carries the comparison from the source of the square to its target.

*Which name the bijection is given.*  The statements below name the bijection of Stacks 08DI by
`AlgebraicGeometry.RingedSite.derivedCurryHomEquiv` at the ringed site of opens of the space,
not by `Stacks.SheafOfModules.derivedSheafHomTensorEquiv`.  That is not a different statement:
the space-level name *is* the site-level one, by definition —

`derivedSheafHomTensorEquiv Rc K L M := RingedSite.derivedCurryHomEquiv (ringedSite Rc) K L M`

at `StacksFrontier/Topology/Sheaves/Cohomology/InternalHom/DerivedInternalHom.lean:144-147`, and
`Stacks.SheafOfModules.derivedSheafHomTensorEquiv_eq` is the `rfl` lemma recording it.  The
site-level name is the one written here because the space-level one declares its domain as
`K ⟶ ((derivedSheafHom Rc).obj (op L)).obj M`, a spelling of the morphism group at which the
`Add` instance an `AddEquiv` needs is not found at the transparencies instance search uses,
while the site-level domain `K ⟶ ((derivedSheafHomBifunctor _).obj (op L)).obj M` carries it.
`StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.KunnethMapForExt` names the
bijection the same way, for the same reason, and `Stacks.Cohomology.DerivedKunnethExt.sheafHomEval`
is built from it there.

*Why the proofs pin their implicit objects.*  The hom object `R𝓗om(B, C)` has two spellings
here: `Stacks.Cohomology.DerivedKunnethExt.sheafHomObj`, which `sheafHomEval` is defined from,
and `AlgebraicGeometry.RingedSite.derivedSheafHomBifunctor`, which the site-level bijection
declares.  They are the same object, and deciding that is affordable — but deciding it *inside*
an `AddEquiv` coercion, or inside a morphism group whose category instance is carried along, is
not: it exceeds `maxRecDepth`.  So `tensorEquivIsEvaluation` names the hom object as
`sheafHomObj Z B C` in each hypothesis it builds, passing it as an explicit argument where the
lemma leaves it implicit, and every rewrite then matches a subterm the goal has verbatim.  The
one step that cannot be a rewrite — the composite that carries both spellings at once — is done
by whiskering and an `iff`, which unify only their conclusion with the goal.

*Two derived tensor products meet here*, as they do in Stacks 0B69: the relative cup product of
Stacks 0B68 is stated over
`Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor` and the bijection of Stacks 08DI
over `Stacks.SheafOfModules.derivedTensorProductFunctor`.  Every object and arrow of the square
is spelled at the first, and `Stacks.Cohomology.DerivedKunnethExt.tensorBridge` is the
comparison of the two; it appears in `TensorEquivIsEvaluation` and in
`tensorMap_symm_sheafHomEval`, the two statements mentioning the bijection of Stacks 08DI.

*The evaluation* is `Stacks.Cohomology.DerivedKunnethExt.sheafHomEval`, the transpose of the
identity, which is the evaluation morphism of Stacks 0A8V with `𝒪` in one of its spots and is
the spelling the maps of Stacks 0B69, 08I3 and 0FXP are built from in this development.

## References

* [Stacks Project, Tag 0G7A](https://stacks.math.columbia.edu/tag/0G7A)
* [Stacks Project, Tag 0B69](https://stacks.math.columbia.edu/tag/0B69)
* [Stacks Project, Tag 0B68](https://stacks.math.columbia.edu/tag/0B68)
* [Stacks Project, Tag 0A8V](https://stacks.math.columbia.edu/tag/0A8V)
* [Stacks Project, Tag 08DI](https://stacks.math.columbia.edu/tag/08DI)
* [Stacks Project, Tag 08J8](https://stacks.math.columbia.edu/tag/08J8)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open Stacks.SheafOfModules.DerivedMonoidal
open Stacks.Cohomology.DerivedKunnethExt
open Stacks.Cohomology.DerivedInternalHomPushforward

universe u

namespace Stacks.Cohomology.DerivedInternalHomEvaluation

attribute [local instance] HasDerivedCategory.standard

-- `Stacks.Cohomology.SiteModules.moduleSheavesAbelian` is a second `Abelian` instance on sheaves
-- of modules, reached here through the imports of the bijection of Stacks 08J8.  The maps of
-- Stacks 0B68 and 0B69 are built at the standard instance, so this file uses that one.
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

section OneSpace

variable (Z : RingedSpace.{u, u})
  [HasSheafify (Opens.grothendieckTopology Z.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology Z.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- **The bijection of Stacks 08DI evaluates.**  The property of a ringed space `(Z, 𝒪_Z)` that
for all `A, B, C ∈ D(𝒪_Z)` the bijection

`Hom(A, R𝓗om(B, C)) ≃ Hom(A ⊗^L_{𝒪_Z} B, C)`

of Stacks 08DI is tensoring with the identity of `B` followed by the evaluation
`R𝓗om(B, C) ⊗^L_{𝒪_Z} B ⟶ C`, i.e. is determined by its value at the identity of
`R𝓗om(B, C)`; written in the inverse direction, so that it reads as a formula for the transpose
of a given datum `A ⊗^L_{𝒪_Z} B ⟶ C`.

Every ringed space has this property: that is `tensorEquivIsEvaluation` below. -/
def TensorEquivIsEvaluation : Prop :=
  ∀ (A B C : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Z.sheaf)))
    (d : ((Stacks.SheafOfModules.derivedTensorProductFunctor
      (Stacks.SheafOfModules.ringedSite Z.sheaf)).obj A).obj B ⟶ C),
    tensorMap Z ((AlgebraicGeometry.RingedSite.derivedCurryHomEquiv
            (Stacks.SheafOfModules.ringedSite Z.sheaf) A B C).symm d) (𝟙 B) ≫
        sheafHomEval Z B C =
      ((tensorBridge Z).inv.app A).app B ≫ d

/-- Tensoring with an identity on the right is the map induced in the first variable. -/
private theorem tensorMap_id_right
    {A A' : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Z.sheaf))}
    (x : A ⟶ A')
    (B : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Z.sheaf))) :
    tensorMap Z x (𝟙 B) =
      ((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor Z.sheaf).map x).app B := by
  rw [tensorMap, CategoryTheory.Functor.map_id, Category.comp_id]

/-- **The bijection of Stacks 08DI on a ringed space evaluates.** Every ringed space has the
property `TensorEquivIsEvaluation`: the bijection of Stacks 08DI is tensoring with the identity
followed by the evaluation of Stacks 0A8V.

The content is the naturality of the bijection in its source variable, which is the source
clause of Stacks 08J8,
`AlgebraicGeometry.RingedSite.derivedCurryHomEquiv_naturality_source`, read at the identity of
`R𝓗om(B, C)` — its value under the bijection being the evaluation of Stacks 0A8V. That clause
is stated for a ringed site, and a ringed space *is* a ringed site, so it applies verbatim; the
only thing to add is that the two derived tensor products of this development are compared
naturally, which moves the comparison from the source of the square to its target.

The clause is used in the form with a free object in its evaluation slot, instantiated at
`sheafHomObj Z B C`, rather than as
`AlgebraicGeometry.RingedSite.tensor_evaluation_derivedCurryHomEquiv_symm`, which writes that
object out as `derivedSheafHomBifunctor`: the free form is what lets every step match the
goal's own spelling, as the implementation notes of this file explain. -/
theorem tensorEquivIsEvaluation : TensorEquivIsEvaluation Z := by
  intro A B C d
  -- The comparison of the two derived tensor products, natural in the first variable: it moves
  -- past the transpose of `d`, from the source of the square to its target.  The hom object is
  -- named `sheafHomObj Z B C`, the spelling `sheafHomEval` is built from, so that every step
  -- below rewrites a subterm the goal has verbatim.
  have hb := NatTrans.congr_app ((tensorBridge Z).inv.naturality (X := A)
    (Y := sheafHomObj Z B C)
    ((RingedSite.derivedCurryHomEquiv (Stacks.SheafOfModules.ringedSite Z.sheaf) A B C).symm d)) B
  rw [NatTrans.comp_app, NatTrans.comp_app] at hb
  -- The source clause of Stacks 08J8, read at the identity of `sheafHomObj Z B C`: the
  -- transpose of `d`, tensored with the identity of `B`, followed by the evaluation.
  have hns := RingedSite.derivedCurryHomEquiv_naturality_source
    (Stacks.SheafOfModules.ringedSite Z.sheaf) (A := sheafHomObj Z B C) (B := B) (Z := C)
    ((RingedSite.derivedCurryHomEquiv (Stacks.SheafOfModules.ringedSite Z.sheaf) A B C).symm d)
    (𝟙 (sheafHomObj Z B C))
  refine (tensorMap_id_right Z (A' := sheafHomObj Z B C)
      ((RingedSite.derivedCurryHomEquiv (Stacks.SheafOfModules.ringedSite Z.sheaf) A B C).symm d) B
    =≫ sheafHomEval Z B C).trans ?_
  rw [sheafHomEval, ← Category.assoc, hb, Category.assoc, ← hns]
  -- What is left is that the transpose of `d`, postcomposed with the identity, transposes back
  -- to `d`.  The composite carries the hom object in both spellings at once — the identity is
  -- at `sheafHomObj Z B C` and the bijection's source at `derivedSheafHomBifunctor` — so it is
  -- no `rw` target: `rw` would have to abstract it, and the motive is not type-correct at
  -- `instances` transparency.  Whiskering and the `iff` only unify their conclusions with the
  -- goal, which takes the composite as the goal already has it and needs no abstraction.
  refine ((tensorBridge Z).inv.app A).app B ≫= ?_
  exact (RingedSite.derivedCurryHomEquiv
    (Stacks.SheafOfModules.ringedSite Z.sheaf) A B C).eq_symm_apply.mp (Category.comp_id _)

/-- The comparison of the two derived tensor products of this development cancels against its
inverse at a pair of objects. -/
private theorem tensorBridge_inv_hom_app_app
    (A B : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Z.sheaf))) :
    ((tensorBridge Z).inv.app A).app B ≫ ((tensorBridge Z).hom.app A).app B =
      𝟙 (tensorObj Z A B) := by
  rw [← NatTrans.comp_app, Iso.inv_hom_id_app, NatTrans.id_app]

/-- **The transpose of a datum evaluates back to the datum.**  On a ringed space the transpose
of a datum `d : A ⊗^L_{𝒪_Z} B ⟶ C`, tensored with the identity of `B` and followed by the
evaluation `R𝓗om(B, C) ⊗^L_{𝒪_Z} B ⟶ C`, is `d` again. -/
private theorem tensorMap_symm_sheafHomEval
    (A B C : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Z.sheaf)))
    (d : tensorObj Z A B ⟶ C) :
    tensorMap Z ((AlgebraicGeometry.RingedSite.derivedCurryHomEquiv
              (Stacks.SheafOfModules.ringedSite Z.sheaf) A B C).symm
            (((tensorBridge Z).hom.app A).app B ≫ d)) (𝟙 B) ≫
        sheafHomEval Z B C = d := by
  rw [tensorEquivIsEvaluation Z A B C (((tensorBridge Z).hom.app A).app B ≫ d), ← Category.assoc,
    tensorBridge_inv_hom_app_app, Category.id_comp]

end OneSpace

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)
  [HasSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify (Opens.grothendieckTopology Y.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology Y.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- **Stacks 0G7A.**  For a morphism of ringed spaces `f : (X, 𝒪_X) ⟶ (Y, 𝒪_Y)` and objects
`K, M` of `D(𝒪_X)` the square

`Rf_*R𝓗om_{𝒪_X}(K, M) ⊗^L_{𝒪_Y} Rf_*K ⟶ Rf_*(R𝓗om_{𝒪_X}(K, M) ⊗^L_{𝒪_X} K) ⟶ Rf_*M`,
`Rf_*R𝓗om_{𝒪_X}(K, M) ⊗^L_{𝒪_Y} Rf_*K ⟶ R𝓗om_{𝒪_Y}(Rf_*K, Rf_*M) ⊗^L_{𝒪_Y} Rf_*K ⟶ Rf_*M`

commutes: the map of Stacks 0B69 tensored with the identity of `Rf_*K` followed by the
evaluation on `Y` agrees with the relative cup product of Stacks 0B68 followed by the derived
pushforward of the evaluation on `X`.

That the bijection of Stacks 08DI on `Y` evaluates, which is the content of the square, is
`tensorEquivIsEvaluation`. -/
@[stacks 0G7A "the square commutes, for every morphism of ringed spaces f and all K, M; this is \
the whole of the remark. The source states it for `K, M ∈ D(𝒪_Y)`, which is a slip — the \
diagram applies both `R𝓗om_{𝒪_X}` and `Rf_*` to `K` and `M`, so the arrows type-check only for \
`K, M ∈ D(𝒪_X)`, and that is the form here"]
theorem tensorMap_pushforwardSheafHomMap_sheafHomEval
    (K M : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf))) :
    tensorMap Y (pushforwardSheafHomMap f M K) (𝟙 ((derivedPushforward f).obj K)) ≫
        sheafHomEval Y ((derivedPushforward f).obj K) ((derivedPushforward f).obj M) =
      Stacks.Cohomology.DerivedRelativeCupProduct.relativeCupProduct f (sheafHomObj X K M) K ≫
        (derivedPushforward f).map (sheafHomEval X K M) := by
  unfold pushforwardSheafHomMap pushforwardSheafHomDatum
  apply tensorMap_symm_sheafHomEval Y

end Stacks.Cohomology.DerivedInternalHomEvaluation

end
