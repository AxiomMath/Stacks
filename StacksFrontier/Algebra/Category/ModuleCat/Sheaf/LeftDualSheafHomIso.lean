module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LeftDualRingedSite
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorAssociatorSections
import StacksCore.Tactic.StacksAttribute

/-!
# A left dual of a sheaf of modules on a ringed site is its sheaf of homomorphisms into `𝒪`

Let `(C, 𝒪)` be a ringed site, let `F` be a sheaf of `𝒪`-modules and let `G`, together with a
coevaluation `η : 𝒪 ⟶ F ⊗_𝒪 G` and an evaluation `ε : G ⊗_𝒪 F ⟶ 𝒪`, be a left dual of `F` in
the monoidal category of `𝒪`-modules of Tag 01CA. [Stacks, Tag
0FNZ](https://stacks.math.columbia.edu/tag/0FNZ) asserts three things about this situation. Its
clause (1), that `F` is locally a direct summand of a finite free module, is
`Stacks.SheafOfModules.exists_cover_retract_finiteFree_of_exactPairing_tensorSheaf`. This file
proves the other two:

* clause (2), that the map `e : SheafHom(F, 𝒪) ⟶ G` sending a local section `λ` to
  `(λ ⊗ 1)(η)` is an isomorphism, and
* clause (3), that `ε(g ⊗ f) = e⁻¹(g)(f)` for local sections `f` of `F` and `g` of `G`.

The argument is the uniqueness of a left dual. Clause (1) is the local hypothesis of [Stacks, Tag
0FNY](https://stacks.math.columbia.edu/tag/0FNY), so the dual `F^∨ = SheafHom(F, 𝒪)` is itself a
left dual of `F`, with the canonical coevaluation and the canonical evaluation
(`Stacks.SheafOfModules.exactPairingDualSheafOfLocalSummand`). Two left duals of one object of a
monoidal category are isomorphic through the adjoint mate of the identity
(`CategoryTheory.rightDualIso`), and that is the map `e`: unfolding
`CategoryTheory.rightAdjointMate` exhibits it as the composite

`F^∨ ≅ F^∨ ⊗ 𝒪 --(F^∨ ◁ η)--> F^∨ ⊗ F ⊗ G --(ε_can ▷ G)--> 𝒪 ⊗ G ≅ G`,

which on a local section `λ` and a local expansion `η(1) = ∑ fᵢ ⊗ gᵢ` evaluates to
`∑ λ(fᵢ) • gᵢ`, i.e. to `(λ ⊗ 1)(η)`. Clause (3) is `rightAdjointMate_comp_evaluation` for the
identity of `F`, read on local sections through the same pure-tensor formulas.

## Main definitions

* `Stacks.SheafOfModules.exactPairingDualSheafOfLeftDual`: the dual sheaf of a module that
  *has* a left dual is itself a left dual of it. This is Tag 0FNY applied to the local
  hypothesis that Tag 0FNZ (1) produces.
* `Stacks.SheafOfModules.dualSheafIsoOfLeftDual`: **Tag 0FNZ (2)**, the isomorphism
  `SheafHom(F, 𝒪) ≅ G`.

## Main results

* `Stacks.SheafOfModules.isLocallyDirectSummandOfFiniteFree_of_exactPairing`: Tag 0FNZ (1) in
  the predicate form that Tag 0FNY consumes.
* `Stacks.SheafOfModules.dualSheafIsoOfLeftDual_hom_eq`: the isomorphism is the composite
  displayed above; this is what identifies it with the map Tag 0FNZ (2) names.
* `Stacks.SheafOfModules.dualSheafIsoOfLeftDual_hom_val_app`: **Tag 0FNZ (2), the formula** —
  on a local section `λ` the isomorphism is `λ ↦ ∑ λ(fᵢ) • gᵢ` for any local expansion
  `η(1) = ∑ fᵢ ⊗ gᵢ` of the coevaluation. Such an expansion exists on a covering of every
  object by `Stacks.SheafOfModules.exists_cover_localDualBasis_tensorSheaf`, so the formula
  determines the isomorphism.
* `Stacks.SheafOfModules.evaluation_eq_dualEval_dualSheafIsoOfLeftDual_inv`: **Tag 0FNZ (3)**,
  the evaluation formula.

## Implementation notes

**No `eqToHom` apparatus is needed.** The monoidal structure used is
`Stacks.SheafOfModules.Strict.monoidalCategory`, whose tensor product *is* the tensor product
sheaf of Tag 01CA and whose unit *is* `SheafOfModules.unit`, both on the nose. So a left dual in
the sense of Stacks is literally a `CategoryTheory.ExactPairing`, the canonical evaluation
`Stacks.SheafOfModules.evaluation` is literally the `ε_` of the canonical pairing, and the
sectionwise formulas for the associator, the unitors and the whiskerings are available as the
`tensorPt` lemmas of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/LeftDualLocalDualBasis.lean`. The ringed-space
analogue, Tag 0FNW in
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/LocallyFiniteFreeSummand/DualSheafIso.lean`, had
to carry an `IsLeftDual` predicate and two ascribing abbreviations for exactly this reason;
here that whole layer collapses.

**Why the isomorphism is produced by `CategoryTheory.rightDualIso` and only then computed.**
Taking the composite above as the *definition* of `e` would leave invertibility to be proved by
hand; taking `rightDualIso` as the definition makes invertibility free and leaves the composite
to be proved, which is one `simp` through `CategoryTheory.rightAdjointMate`. The same choice
makes clause (3) an instance of `CategoryTheory.rightAdjointMate_comp_evaluation` rather than a
second sectionwise computation.

**Universes.** The sections of `𝒪` and of the modules live in `max u v`, where `u` and `v` are
the universes of the objects and the arrows of the site. That is forced by the internal hom of
Tag 03EM, of which `SheafHom(F, 𝒪)` is an instance: a section of it over `U` is a morphism of
presheaves of modules on the slice site `C/U`, whose arrows live in `max u v`. The clause (1)
input is stated at an independent module universe and is instantiated here at `max u v`.

## References

* [Stacks Project, Tag 0FNZ](https://stacks.math.columbia.edu/tag/0FNZ)
* [Stacks Project, Tag 0FNY](https://stacks.math.columbia.edu/tag/0FNY) — the converse, that the
  dual of a module locally a finite free summand is a left dual.
* [Stacks Project, Tag 0FNW](https://stacks.math.columbia.edu/tag/0FNW) — the same statement for
  a ringed space.
* [Stacks Project, Tag 0FFP](https://stacks.math.columbia.edu/tag/0FFP) — left duals in a
  monoidal category.
* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA) — the monoidal structure.
-/

@[expose] public section

open CategoryTheory MonoidalCategory Opposite SheafOfModules

open scoped TensorProduct

universe v u

namespace Stacks.SheafOfModules

attribute [local instance] Strict.monoidalCategory monoidalCategoryPresheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (𝒪 : Cᵒᵖ ⥤ CommRingCat.{max u v})
  (h𝒪 : Presheaf.IsSheaf J (TensorSheafification.structureRingPresheaf 𝒪))
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
  [HasWeakSheafify J AddCommGrpCat.{max u v}]
  [HasSheafify J AddCommGrpCat.{max u v}]
  [∀ V : C, HasWeakSheafify (J.over V) AddCommGrpCat.{max u v}]
  [∀ V : C, (J.over V).WEqualsLocallyBijective AddCommGrpCat.{max u v}]
  (F G : SheafOfModules.{max u v} (TensorSheafification.structureSheaf 𝒪 h𝒪))
  [p : ExactPairing F G]

include p in
/-- **Tag 0FNZ (1), in the predicate form of Tag 0FNY.** A sheaf of modules with a left dual is
locally a direct summand of a finite free sheaf of modules: every object of the site has a
covering on whose members it restricts to a retract of a finite free module. -/
theorem isLocallyDirectSummandOfFiniteFree_of_exactPairing :
    IsLocallyDirectSummandOfFiniteFree 𝒪 h𝒪 F := fun U ↦
  exists_cover_retract_finiteFree_of_exactPairing_tensorSheaf 𝒪 h𝒪 F G p U

include p in
/-- **The dual sheaf of a module that has a left dual is itself a left dual of it.** By Tag
0FNZ (1) the module is locally a direct summand of a finite free module, which is the local
hypothesis of Tag 0FNY, so `SheafHom(F, 𝒪)` with the canonical coevaluation and evaluation
satisfies the two triangle identities. -/
@[instance_reducible]
noncomputable def exactPairingDualSheafOfLeftDual : ExactPairing F (dualSheaf 𝒪 h𝒪 F) :=
  exactPairingDualSheafOfLocalSummand 𝒪 h𝒪 F
    (isLocallyDirectSummandOfFiniteFree_of_exactPairing 𝒪 h𝒪 F G)

include p in
/-- **Stacks Project, Tag 0FNZ (2).** A left dual `G` of a sheaf of `𝒪`-modules `F` on a ringed
site is isomorphic to `SheafHom(F, 𝒪)`.

Both `SheafHom(F, 𝒪)` and `G` are left duals of `F` — the first by
`exactPairingDualSheafOfLeftDual` — and two left duals of one object are isomorphic through the
adjoint mate of the identity. That this isomorphism is the map Tag 0FNZ (2) names, namely
`λ ↦ (λ ⊗ 1)(η)`, is `dualSheafIsoOfLeftDual_hom_val_app`. -/
@[stacks 0FNZ "(2), the isomorphism `𝓗om(ℱ,𝒪) ≅ 𝒢`; that it is the map `λ ↦ (λ ⊗ 1)(η)` of the \
tag is `dualSheafIsoOfLeftDual_hom_val_app`"]
noncomputable def dualSheafIsoOfLeftDual : dualSheaf 𝒪 h𝒪 F ≅ G :=
  rightDualIso (exactPairingDualSheafOfLeftDual 𝒪 h𝒪 F G) p

include p in
/-- The isomorphism of Tag 0FNZ (2) is the composite
`F^∨ ≅ F^∨ ⊗ 𝒪 ⟶ F^∨ ⊗ F ⊗ G ⟶ 𝒪 ⊗ G ≅ G`
built from the given coevaluation `η` and the canonical evaluation of `F^∨`. This is
`CategoryTheory.rightAdjointMate` of the identity of `F`, with the whiskering by the identity
removed. -/
theorem dualSheafIsoOfLeftDual_hom_eq :
    (dualSheafIsoOfLeftDual 𝒪 h𝒪 F G).hom =
      (ρ_ (dualSheaf 𝒪 h𝒪 F)).inv ≫ dualSheaf 𝒪 h𝒪 F ◁ η_ F G ≫
        (α_ (dualSheaf 𝒪 h𝒪 F) F G).inv ≫
          @MonoidalCategoryStruct.whiskerRight
              (SheafOfModules.{max u v} (TensorSheafification.structureSheaf 𝒪 h𝒪)) _ _
              (dualSheaf 𝒪 h𝒪 F ⊗ F)
              (𝟙_ (SheafOfModules.{max u v} (TensorSheafification.structureSheaf 𝒪 h𝒪)))
              (evaluation 𝒪 h𝒪 F) G ≫
            (λ_ G).hom := by
  let pD := exactPairingDualSheafOfLeftDual 𝒪 h𝒪 F G
  change (rightDualIso pD p).hom = _
  dsimp only [rightDualIso, rightAdjointMate]
  have hev : ε_ F (dualSheaf 𝒪 h𝒪 F) = evaluation 𝒪 h𝒪 F := rfl
  simp [hev]

include p in
/-- The inverse of the isomorphism of Tag 0FNZ (2) carries the canonical evaluation of
`SheafHom(F, 𝒪)` to the given evaluation `ε`. This is the morphism-level form of Tag 0FNZ (3),
and it is `CategoryTheory.rightAdjointMate_comp_evaluation` for the identity of `F`. -/
theorem dualSheafIsoOfLeftDual_inv_whiskerRight_comp_evaluation :
    (dualSheafIsoOfLeftDual 𝒪 h𝒪 F G).inv ▷ F ≫ evaluation 𝒪 h𝒪 F = ε_ F G := by
  let pD := exactPairingDualSheafOfLeftDual 𝒪 h𝒪 F G
  change (dualSheafIsoOfLeftDual 𝒪 h𝒪 F G).inv ▷ F ≫ ε_ F (dualSheaf 𝒪 h𝒪 F) = ε_ F G
  have key : (dualSheafIsoOfLeftDual 𝒪 h𝒪 F G).hom ▷ F ≫ ε_ F G
      = ε_ F (dualSheaf 𝒪 h𝒪 F) := by
    have h := @rightAdjointMate_comp_evaluation _ _ _ F F (HasRightDual.mk G)
      (@HasRightDual.mk _ _ _ F (dualSheaf 𝒪 h𝒪 F) pD) (𝟙 F)
    simpa [dualSheafIsoOfLeftDual, rightDualIso] using h
  rw [← key, ← comp_whiskerRight_assoc, Iso.inv_hom_id, id_whiskerRight, Category.id_comp]

omit [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
  [HasWeakSheafify J AddCommGrpCat.{max u v}] [HasSheafify J AddCommGrpCat.{max u v}]
  [∀ V : C, HasWeakSheafify (J.over V) AddCommGrpCat.{max u v}]
  [∀ V : C, (J.over V).WEqualsLocallyBijective AddCommGrpCat.{max u v}] in
/-- A morphism of sheaves of modules is additive on local sections. -/
private lemma val_app_sum
    {A B : SheafOfModules.{max u v} (TensorSheafification.structureSheaf 𝒪 h𝒪)}
    (φ : A ⟶ B) (V : Cᵒᵖ) {ι : Type*} (s : Finset ι) (z : ι → A.val.obj V) :
    φ.val.app V (∑ i ∈ s, z i) = ∑ i ∈ s, φ.val.app V (z i) :=
  map_sum (φ.val.app V).hom _ s

include p in
/-- **Stacks Project, Tag 0FNZ (2), the formula for the isomorphism.** On an object `U` over
which the coevaluation expands as `η(1) = ∑ fᵢ ⊗ gᵢ`, the isomorphism
`SheafHom(F, 𝒪) ≅ G` of Tag 0FNZ (2) sends a local section `λ` to `∑ λ(fᵢ) • gᵢ`, which is
`(λ ⊗ 1)(η)`. In particular that expression does not depend on the chosen expansion.

Such an expansion exists on a covering of every object of the site, by
`Stacks.SheafOfModules.exists_cover_localDualBasis_tensorSheaf`, so these formulas determine the
isomorphism. -/
@[stacks 0FNZ "(2), that the isomorphism is the map `λ ↦ (λ ⊗ 1)(η)` the tag describes"]
theorem dualSheafIsoOfLeftDual_hom_val_app (U : C) {n : ℕ}
    (f : Fin n → F.val.obj (op U)) (g : Fin n → G.val.obj (op U))
    (hη : (η_ F G).val.app (op U)
        (1 : (TensorSheafification.structureSheaf 𝒪 h𝒪).obj.obj (op U)) =
      ∑ i, tensorPt 𝒪 h𝒪 F G (op U) (f i) (g i))
    (lam : (dualSheaf 𝒪 h𝒪 F).val.obj (op U)) :
    (dualSheafIsoOfLeftDual 𝒪 h𝒪 F G).hom.val.app (op U) lam =
      ∑ i, dualEval lam (f i) • g i := by
  have hterm (i : Fin n) :
      (λ_ G).hom.val.app (op U)
        ((@MonoidalCategoryStruct.whiskerRight
            (SheafOfModules.{max u v} (TensorSheafification.structureSheaf 𝒪 h𝒪)) _ _
            (dualSheaf 𝒪 h𝒪 F ⊗ F)
            (𝟙_ (SheafOfModules.{max u v} (TensorSheafification.structureSheaf 𝒪 h𝒪)))
            (evaluation 𝒪 h𝒪 F) G).val.app (op U)
        ((α_ (dualSheaf 𝒪 h𝒪 F) F G).inv.val.app (op U)
          (tensorPt 𝒪 h𝒪 (dualSheaf 𝒪 h𝒪 F) (F ⊗ G) (op U) lam
            (tensorPt 𝒪 h𝒪 F G (op U) (f i) (g i)))))
        = dualEval lam (f i) • g i := by
    have h3 := evaluation_tensorPt 𝒪 h𝒪 F (op U) lam (f i)
    have h4 := tensorPt_leftUnitor_hom 𝒪 h𝒪 (A := G) (op U) (dualEval lam (f i)) (g i)
    rw [tensorPt_associator_inv 𝒪 h𝒪 (dualSheaf 𝒪 h𝒪 F) F G (op U) lam (f i) (g i),
      tensorPt_whiskerRight 𝒪 h𝒪 (A := dualSheaf 𝒪 h𝒪 F ⊗ F)
        (A' := 𝟙_ (SheafOfModules.{max u v} (TensorSheafification.structureSheaf 𝒪 h𝒪)))
        (B := G) (evaluation 𝒪 h𝒪 F) (op U)
        (tensorPt 𝒪 h𝒪 (dualSheaf 𝒪 h𝒪 F) F (op U) lam (f i)) (g i)]
    exact (congrArg (fun z ↦ (λ_ G).hom.val.app (op U)
      (tensorPt 𝒪 h𝒪 (𝟙_ (SheafOfModules.{max u v}
        (TensorSheafification.structureSheaf 𝒪 h𝒪))) G (op U) z (g i))) h3).trans h4
  rw [dualSheafIsoOfLeftDual_hom_eq]
  simp only [comp_val_app_apply]
  rw [rightUnitor_inv_eq_tensorPt 𝒪 h𝒪 (A := dualSheaf 𝒪 h𝒪 F) (op U) lam,
    tensorPt_whiskerLeft 𝒪 h𝒪 (A := dualSheaf 𝒪 h𝒪 F)
      (B := 𝟙_ (SheafOfModules.{max u v} (TensorSheafification.structureSheaf 𝒪 h𝒪)))
      (B' := F ⊗ G) (η_ F G) (op U) lam
      (1 : (TensorSheafification.structureSheaf 𝒪 h𝒪).obj.obj (op U)),
    hη, tensorPt_sum_right, val_app_sum, val_app_sum, val_app_sum]
  exact Finset.sum_congr rfl fun i _ => hterm i

include p in
/-- **Stacks Project, Tag 0FNZ (3).** Pairing a local section `g` of a left dual `G` of `F`
against a local section `f` of `F` under the given evaluation `ε` is the value at `f` of the
local homomorphism `e⁻¹(g) : F ⟶ 𝒪`, where `e` is the isomorphism of Tag 0FNZ (2). -/
@[stacks 0FNZ "(3), the evaluation formula `ε(f, g) = e⁻¹(g)(f)`"]
theorem evaluation_eq_dualEval_dualSheafIsoOfLeftDual_inv (U : C)
    (y : G.val.obj (op U)) (x : F.val.obj (op U)) :
    (ε_ F G).val.app (op U) (tensorPt 𝒪 h𝒪 G F (op U) y x) =
      dualEval ((dualSheafIsoOfLeftDual 𝒪 h𝒪 F G).inv.val.app (op U) y) x := by
  let pD := exactPairingDualSheafOfLeftDual 𝒪 h𝒪 F G
  have key : (dualSheafIsoOfLeftDual 𝒪 h𝒪 F G).inv ▷ F ≫ ε_ F (dualSheaf 𝒪 h𝒪 F) = ε_ F G :=
    dualSheafIsoOfLeftDual_inv_whiskerRight_comp_evaluation 𝒪 h𝒪 F G
  rw [← key, comp_val_app_apply, tensorPt_whiskerRight]
  exact evaluation_tensorPt 𝒪 h𝒪 F (op U)
    ((dualSheafIsoOfLeftDual 𝒪 h𝒪 F G).inv.val.app (op U) y) x

end Stacks.SheafOfModules

end
