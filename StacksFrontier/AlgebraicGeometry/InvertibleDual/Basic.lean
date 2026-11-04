module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafHom
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The evaluation pairing of a locally trivial module sheaf, and the invertibility of its dual

Let `𝒪` be a presheaf of commutative rings on a site `(C, J)` whose underlying presheaf of
rings is a sheaf, and let `L` be a sheaf of `𝒪`-modules carrying a rank-one dual basis on a
family of objects covering the terminal object — that is, `L` is trivialized on a covering.
[Stacks Project, Tag 0B8M] opens its proof with exactly this situation: *"Assume `L` is locally
free of rank 1 and consider the evaluation map `L ⊗ SheafHom(L, 𝒪) ⟶ 𝒪`. Looking over an open
covering trivializing `L`, we see that this map is an isomorphism."*

This file draws that conclusion, and the one [Stacks Project, Tag 01CT] (2) attaches to it: the
evaluation pairing `L^∨ ⊗_𝒪 L ⟶ 𝒪` of `Stacks.SheafOfModules.evaluation` is an isomorphism, and
the dual `L^∨` is itself invertible.

`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/SheafHom.lean` already proves that sheafification
inverts the evaluation pairing *of presheaves of modules* under this hypothesis
(`isIso_sheafify_map_evaluationPresheaf`) and deduces from it that `L` is invertible
(`isInvertible_of_dualBasisOne`). What is added here is the same conclusion about the morphism
of *sheaves* of modules `L^∨ ⊗_𝒪 L ⟶ 𝒪`, which is the shape every consumer of the pairing
wants: the tensor product of sheaves of modules is the sheafification of the pointwise one, so
the two differ by the counit of the sheafification adjunction, and that counit is invertible at
`𝒪` because `𝒪` is a sheaf.

## Main definitions

* `Stacks.SheafOfModules.Invertible.evaluationIso`: the evaluation pairing `L^∨ ⊗_𝒪 L ⟶ 𝒪` read
  as an isomorphism, for a sheaf of modules trivialized on a covering.

## Main results

* `Stacks.SheafOfModules.Invertible.evaluation_eq_sheafifyMap_comp_counit`: the evaluation
  pairing of sheaves of modules is the sheafification of the evaluation pairing of presheaves of
  modules, followed by the counit of the sheafification adjunction at the structure sheaf. This
  is the adjoint-transpose identity, recorded because the two sides are stated over
  definitionally but not syntactically equal presheaves of rings, so `rw` on the definition of
  `evaluation` does not type-check.
* `Stacks.SheafOfModules.Invertible.isIso_evaluation_of_dualBasisOne`: for a sheaf of modules
  trivialized on a covering, the evaluation pairing `L^∨ ⊗_𝒪 L ⟶ 𝒪` is an isomorphism.
* `Stacks.SheafOfModules.Invertible.isInvertible_dualSheaf_of_dualBasisOne`: for such an `L`,
  the dual `L^∨` is invertible. This is the first clause of Tag 01CT (2) under that hypothesis;
  the clause itself, for an arbitrary invertible `L`, is
  `Stacks.SheafOfModules.Invertible.isInvertible_dualSheaf`.

## Implementation notes

**None of these declarations carries a Stacks attribute, and the hypothesis is why.** Tag 01CT
(2) asserts the two conclusions above for an *invertible* `L`, not for a trivialized one, and
the step from the first hypothesis to the second is the converse half of Tag 0B8M: an invertible
module sheaf is locally free of rank one. That converse is false over a general site — Tag 0B8M
says so, with a one-point space whose ring has nontrivial Picard group as the counterexample —
and over a general site it is accordingly unavailable here;
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/SheafHom.lean` records it as
missing. (On a *ringed space* whose structure-sheaf stalks are local rings, which is the case
Tag 0B8M does assert, this development does prove it, as
`Stacks.SheafOfModules.Invertible.isLocallyTrivial_of_isInvertible` of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/InvertibleRankOne/Converse.lean`.) So the
hypothesis here is not a weakening of Tag 01CT chosen for convenience, and the declarations are
stated and named so that they say what they assume.

**Tag 01CT (2) itself no longer waits on any of this.** What the Stacks source proves it from is
the other paragraph of Tag 0B8K's proof: an invertible `L` is locally a direct summand of a
finite free module, hence of finite presentation, and then the evaluation pairing is checked to
be an isomorphism on stalks using Tag 01CP. That route is independent of this file and does not
pass through a trivializing cover, and the development now takes its first step — Tag 0B8N (b),
local splitting off a finite free module — and finishes it not on stalks but by rigidity: the
splittings make `L^∨` a *left dual* of `L` (Tag 0FNV) and the evaluation of a left dual is
inverted by the equivalence `· ⊗ L`. That is
`Stacks.SheafOfModules.Invertible.isIso_evaluation` and
`Stacks.SheafOfModules.Invertible.isInvertible_dualSheaf` of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/InvertibleDualEvaluation.lean`, which carry Tags
01CT (2) and 040A (2) with no hypothesis beyond invertibility. The declarations below remain the
form to use when a trivializing cover is what one has in hand.

**Why the two-step proof.** `Stacks.SheafOfModules.evaluation` is defined as the adjoint
transpose of `evaluationPresheaf` under
  `Stacks.SheafOfModules.TensorSheafification.sheafifyAdjunction`, and
`Adjunction.homEquiv_counit` expresses any such transpose as the left adjoint applied to the
morphism, followed by the counit. Rewriting with the definition of `evaluation` directly fails:
`Stacks.SheafOfModules.TensorSheafification.tensorPresheaf` takes its arguments over
  `Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf 𝒪` while
`(dualSheaf 𝒪 h𝒪 L).val` is stated over `(Stacks.SheafOfModules.TensorSheafification.structureSheaf
  𝒪 h𝒪).obj`, and the two
agree only at default transparency. `evaluation_eq_sheafifyMap_comp_counit` states the
factorization with both sides fully applied, which elaborates, and the rewrite is done with
that.

## References

* [Stacks Project, Tag 01CT](https://stacks.math.columbia.edu/tag/01CT)
* [Stacks Project, Tag 0B8K](https://stacks.math.columbia.edu/tag/0B8K)
* [Stacks Project, Tag 0B8M](https://stacks.math.columbia.edu/tag/0B8M)
* [Stacks Project, Tag 0FNV](https://stacks.math.columbia.edu/tag/0FNV)
-/

@[expose] public section

open CategoryTheory MonoidalCategory

universe v u

namespace Stacks.SheafOfModules.Invertible

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (𝒪 : Cᵒᵖ ⥤ CommRingCat.{max u v})
  (h𝒪 : Presheaf.IsSheaf J (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf 𝒪))
  {L : SheafOfModules.{max u v} (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪)}
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
  [HasWeakSheafify J AddCommGrpCat.{max u v}]

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules

/-- **The evaluation pairing of sheaves of modules factors through sheafification.** The
pairing `L^∨ ⊗_𝒪 L ⟶ 𝒪` is the sheafification of the pairing of presheaves of modules,
followed by the counit of the sheafification adjunction at the structure sheaf. This is the
adjoint-transpose identity of `Adjunction.homEquiv_counit`, stated with both sides fully
applied; see the implementation notes of this file for why the unapplied rewrite fails. -/
theorem evaluation_eq_sheafifyMap_comp_counit :
    Stacks.SheafOfModules.evaluation 𝒪 h𝒪 L =
      (Stacks.SheafOfModules.TensorSheafification.sheafify 𝒪 h𝒪).map
        (Stacks.SheafOfModules.evaluationPresheaf 𝒪 h𝒪 L) ≫
        (Stacks.SheafOfModules.TensorSheafification.sheafifyAdjunction 𝒪 h𝒪).counit.app
          (SheafOfModules.unit (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪)) :=
  Adjunction.homEquiv_counit _ _ _ _

/-- **The evaluation pairing of a trivialized module sheaf with its dual is an isomorphism.**
This is the first paragraph of the proof of [Stacks, Tag 0B8M], and the evaluation clause of
[Stacks, Tag 01CT] (2) under the hypothesis that `L` is trivialized on a covering rather than
merely invertible. Sheafification inverts the pairing of presheaves of modules
(`isIso_sheafify_map_evaluationPresheaf`), and the counit of the sheafification adjunction is
invertible at the structure sheaf because the structure sheaf is a sheaf. -/
@[ega "0 5.4.3" "more general"]
theorem isIso_evaluation_of_dualBasisOne {I : Type*} {X : I → C} (hX : J.CoversTop X)
    (b : ∀ i, Stacks.SheafOfModules.DualBasisOne 𝒪 h𝒪 L (X i)) :
    IsIso (Stacks.SheafOfModules.evaluation 𝒪 h𝒪 L) := by
  have hev := Stacks.SheafOfModules.isIso_sheafify_map_evaluationPresheaf 𝒪 h𝒪 hX b
  have hco : IsIso ((Stacks.SheafOfModules.TensorSheafification.sheafifyAdjunction 𝒪 h𝒪).counit.app
      (SheafOfModules.unit (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪))) :=
        inferInstance
  rw [evaluation_eq_sheafifyMap_comp_counit]
  exact @IsIso.comp_isIso _ _ _ _ _ _ _ hev hco

/-- **The evaluation pairing of a trivialized module sheaf, as an isomorphism**
`L^∨ ⊗_𝒪 L ≅ 𝒪`, whose underlying morphism is `Stacks.SheafOfModules.evaluation`. -/
noncomputable def evaluationIso {I : Type*} {X : I → C} (hX : J.CoversTop X)
    (b : ∀ i, Stacks.SheafOfModules.DualBasisOne 𝒪 h𝒪 L (X i)) :
    (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨𝒪, Presheaf.isSheaf_of_isSheaf_comp _ (𝒪)
        (forget₂ CommRingCat RingCat) (h𝒪)⟩).obj ((Stacks.SheafOfModules.dualSheaf 𝒪
      h𝒪 L))).obj (L)) ≅
      SheafOfModules.unit (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪) :=
  have := isIso_evaluation_of_dualBasisOne 𝒪 h𝒪 hX b
  asIso (Stacks.SheafOfModules.evaluation 𝒪 h𝒪 L)

/-- The forward morphism of `evaluationIso` is the evaluation pairing
`Stacks.SheafOfModules.evaluation`. -/
@[simp]
theorem evaluationIso_hom {I : Type*} {X : I → C} (hX : J.CoversTop X)
    (b : ∀ i, Stacks.SheafOfModules.DualBasisOne 𝒪 h𝒪 L (X i)) :
    (evaluationIso 𝒪 h𝒪 hX b).hom = Stacks.SheafOfModules.evaluation 𝒪 h𝒪 L :=
  rfl

/-- **The dual of a trivialized module sheaf is invertible.** This is the first clause of
[Stacks, Tag 01CT] (2) — "if `L` is an invertible `𝒪_X`-module, then so is
`SheafHom(L, 𝒪_X)`" — under the hypothesis that `L` is trivialized on a covering rather than
merely invertible.

The two pairings that `isInvertible_of_pairing` (Tag 0B8K) requires of `L^∨` are the evaluation
pairing of presheaves of modules and that same pairing composed with the braiding, exactly as
in `isInvertible_of_dualBasisOne`, with the roles of `L` and `L^∨` exchanged. -/
theorem isInvertible_dualSheaf_of_dualBasisOne {I : Type*} {X : I → C} (hX : J.CoversTop X)
    (b : ∀ i, Stacks.SheafOfModules.DualBasisOne 𝒪 h𝒪 L (X i)) :
    Stacks.SheafOfModules.IsInvertible 𝒪 h𝒪 (Stacks.SheafOfModules.dualSheaf 𝒪 h𝒪 L) := by
  have hev := Stacks.SheafOfModules.isIso_sheafify_map_evaluationPresheaf 𝒪 h𝒪 hX b
  have hbr : IsIso ((Stacks.SheafOfModules.TensorSheafification.sheafify 𝒪 h𝒪).map
      (Stacks.SheafOfModules.braidingVal 𝒪 h𝒪 L
        (Stacks.SheafOfModules.dualSheaf 𝒪 h𝒪 L)).inv) := inferInstance
  exact Stacks.SheafOfModules.isInvertible_of_pairing
    (Stacks.SheafOfModules.dualSheaf 𝒪 h𝒪 L) L
    ((Stacks.SheafOfModules.braidingVal 𝒪 h𝒪 L
      (Stacks.SheafOfModules.dualSheaf 𝒪 h𝒪 L)).inv ≫
        Stacks.SheafOfModules.evaluationPresheaf 𝒪 h𝒪 L)
    (Stacks.SheafOfModules.evaluationPresheaf 𝒪 h𝒪 L)
    (Stacks.SheafOfModules.isIso_sheafify_map_comp 𝒪 h𝒪 _ _ hbr hev) hev

end Stacks.SheafOfModules.Invertible

end
