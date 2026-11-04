module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocallyFiniteFreeSummand.LeftDualOnSpace
import StacksCore.Tactic.StacksAttribute

/-!
# A left dual of a sheaf of modules is its dual sheaf

Let `(X, O_X)` be a ringed space, let `F` be a sheaf of `O_X`-modules and let `G` be a left dual
of `F` in the monoidal category of `O_X`-modules, with coevaluation `η` and evaluation `ε`.
Stacks 0FNW (2) asserts that `G` is canonically isomorphic to the dual sheaf
`F^∨ = SheafHom(F, O_X)`, by the map sending a local functional `lam` over `U` to
`∑ i, lam (f i) • g i` for any local expansion `η(1) = ∑ i, f i ⊗ g i` of the coevaluation over
`U`; part (3) asserts that the pairing `ε` is, through that isomorphism, ordinary evaluation of
local functionals.

## Main definitions

* `Stacks.SheafOfModules.OnSpace.IsLeftDual` says that `η` and `ε` exhibit `G` as a left dual of
  `F` for the monoidal structure of
  `StacksFrontier/Algebra/Category/ModuleCat/Sheaf/OnSpaceMonoidal.lean`.

## Main results

* `Stacks.SheafOfModules.OnSpace.dualSheafIso`: Stacks 0FNW (2), the isomorphism together with
  the formula characterising it on local functionals.
* `Stacks.SheafOfModules.OnSpace.evaluation_eq_dualSheafIso_inv`: Stacks 0FNW (3), the
  evaluation formula.

## Implementation notes

Uniqueness of a left dual is categorical: for every `Z` the map `f ↦ η ≫ F ◁ f` is a bijection
`(G ⟶ Z) ≃ (O_X ⟶ F ⊗ Z)` (`sheafCoevaluation_bijective`), which is `coevaluation_bijective`
read through the identification of the monoidal tensor product with the sheaf tensor product.
Applying this to both `G` and `F^∨` — the latter is a left dual by `dualSheafExactPairing` —
produces mutually inverse morphisms, and `evaluation_eq_of_coevaluation_eq` transports the
evaluation along them, since in any monoidal category the evaluation of an exact pairing is
determined by its coevaluation. The two displayed formulas then follow from the dual-basis
identities of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/LocallyFiniteFreeSummand/LeftDualOnSpace.lean`
and from the section formula for a
left whiskering.

That `F` is locally a direct summand of a finite free module, which is what makes `F^∨` a left
dual, is not an extra hypothesis: it follows from `η` and `ε` by Stacks 0FNW (1), in the
coherence-hypothesis-free form `isLocallyFiniteFreeSummand_of_exactPairing` of `LeftDual.lean`.

Every morphism out of the monoidal unit, and every morphism into it, is written through the
ascribed abbreviations `coevTensor` and `evalTensor`. This is not cosmetic: a `⊗ₜ` appearing at a
concrete factor whose type mentions `⊗` makes instance synthesis unfold `monoidal`'s `tensorObj`
and produce a second, definitionally equal but not cheaply equal, spelling of the module
structure on local sections, after which `rw` reports the target as not type-correct at
`implicit` transparency. Fixing the spelling once, on variables, makes every later use a
substitution.

## References

* [Stacks Project, Tag 0FNW](https://stacks.math.columbia.edu/tag/0FNW)
-/

@[expose] public section

open CategoryTheory Limits Opposite TopologicalSpace TensorProduct MonoidalCategory

universe u

namespace Stacks.SheafOfModules.OnSpace

open Stacks.SheafOfModules.TensorStalkRingedSpace

attribute [local instance] monoidal

variable (X : AlgebraicGeometry.RingedSpace.{u, u})

/-- A coevaluation `O_X ⟶ F ⊗ G`, with its target written as the tensor product of `monoidal`
rather than as `tensorSheaf`. The two are equal objects by `monoidal_tensorObj`, but only one of
the spellings matches the section formulas of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/OnSpaceMonoidal.lean`; see the
implementation notes. -/
noncomputable abbrev coevTensor (F G : SheafOfModules.{u} (structureSheafRing X))
    (η : SheafOfModules.unit (structureSheafRing X) ⟶
      ((Stacks.SheafOfModules.Tensor.sheafTensor ⟨X.presheaf, X.IsSheaf⟩).obj F).obj G) :
    𝟙_ (SheafOfModules.{u} (structureSheafRing X)) ⟶ F ⊗ G := η

/-- An evaluation `G ⊗ F ⟶ O_X`, with its source written as the tensor product of `monoidal`;
see `coevTensor`. -/
noncomputable abbrev evalTensor (F G : SheafOfModules.{u} (structureSheafRing X))
    (ε : ((Stacks.SheafOfModules.Tensor.sheafTensor ⟨X.presheaf, X.IsSheaf⟩).obj G).obj F ⟶
      SheafOfModules.unit (structureSheafRing X)) :
    G ⊗ F ⟶ 𝟙_ (SheafOfModules.{u} (structureSheafRing X)) := ε

/-- The specified coevaluation `η` and evaluation `ε` exhibit `G` as a **left dual** of `F` in
the monoidal category of `O_X`-modules. -/
def IsLeftDual (F G : SheafOfModules.{u} (structureSheafRing X))
    (η : SheafOfModules.unit (structureSheafRing X) ⟶
      ((Stacks.SheafOfModules.Tensor.sheafTensor ⟨X.presheaf, X.IsSheaf⟩).obj F).obj G)
    (ε : ((Stacks.SheafOfModules.Tensor.sheafTensor ⟨X.presheaf, X.IsSheaf⟩).obj G).obj F ⟶
      SheafOfModules.unit (structureSheafRing X)) : Prop :=
  ∃ p : ExactPairing F G,
    @ExactPairing.coevaluation _ _ _ _ _ p = coevTensor X F G η ∧
      @ExactPairing.evaluation _ _ _ _ _ p = evalTensor X F G ε

/-- The dual sheaf is a left dual, with the canonical coevaluation and evaluation. -/
theorem isLeftDual_dualSheaf (F : SheafOfModules.{u} (structureSheafRing X))
    (hF : IsLocallyFiniteFreeSummand X F) :
    IsLeftDual X F (dualSheaf X F) (coevaluation X F hF) (evaluation X F) :=
  ⟨dualSheafExactPairing X F hF, rfl, rfl⟩

/-- A left dual makes `F` locally a direct summand of a finite free module. -/
theorem isLocallyFiniteFreeSummand_of_isLeftDual
    (F G : SheafOfModules.{u} (structureSheafRing X))
    (η : SheafOfModules.unit (structureSheafRing X) ⟶
      ((Stacks.SheafOfModules.Tensor.sheafTensor ⟨X.presheaf, X.IsSheaf⟩).obj F).obj G)
    (ε : ((Stacks.SheafOfModules.Tensor.sheafTensor ⟨X.presheaf, X.IsSheaf⟩).obj G).obj F ⟶
      SheafOfModules.unit (structureSheafRing X))
    (h : IsLeftDual X F G η ε) : IsLocallyFiniteFreeSummand X F := by
  obtain ⟨p, -, -⟩ := h
  exact isLocallyFiniteFreeSummand_of_exactPairing X F G p

/-- **Uniqueness of a left dual, in Hom-set form.** In any monoidal category, composing the
coevaluation of an exact pairing with a left whiskering is a bijection on Hom-sets. -/
theorem coevaluation_bijective
    {C : Type*} [Category C] [MonoidalCategory C]
    (F G Z : C) [ExactPairing F G] :
    Function.Bijective (fun f : G ⟶ Z => η_ F G ≫ F ◁ f) := by
  let E := ((ρ_ G).symm.homCongr (Iso.refl Z)).trans (tensorLeftHomEquiv (𝟙_ C) F G Z)
  have hE (f : G ⟶ Z) : E f = η_ F G ≫ F ◁ f := by
    apply (tensorLeftHomEquiv (𝟙_ C) F G Z).symm.injective
    simp [E]
  simpa only [← hE] using E.bijective

/-- In any monoidal category, the evaluation of an exact pairing is determined by its
coevaluation: a morphism between two left duals of `F` compatible with the coevaluations is
automatically compatible with the evaluations. -/
theorem evaluation_eq_of_coevaluation_eq
    {C : Type*} [Category C] [MonoidalCategory C]
    (F D G : C) (p₁ : ExactPairing F D) (p₂ : ExactPairing F G) (φ : G ⟶ D)
    (hφ : @ExactPairing.coevaluation _ _ _ F G p₂ ≫ F ◁ φ =
      @ExactPairing.coevaluation _ _ _ F D p₁) :
    φ ▷ F ≫ @ExactPairing.evaluation _ _ _ F D p₁ =
      @ExactPairing.evaluation _ _ _ F G p₂ := by
  have key₁ := @coevaluation_comp_rightAdjointMate C _ _ F F ⟨D⟩ ⟨G⟩ (𝟙 F)
  have key₂ := @rightAdjointMate_comp_evaluation C _ _ F F ⟨D⟩ ⟨G⟩ (𝟙 F)
  rw [id_whiskerRight, Category.comp_id] at key₁
  rw [whiskerLeft_id, Category.id_comp] at key₂
  rw [(@coevaluation_bijective C _ _ F G D p₂).injective (hφ.trans key₁.symm)]
  exact key₂

/-- If the coevaluation of `A` is bijective on endomorphisms, two morphisms `A ⟶ B ⟶ A` compatible
with the coevaluations compose to the identity. -/
private theorem comp_eq_id_of_coevaluation_eq
    {C : Type*} [Category C] [MonoidalCategory C] (F : C) {A B : C}
    {ηA : 𝟙_ C ⟶ F ⊗ A} {ηB : 𝟙_ C ⟶ F ⊗ B}
    (hA : Function.Bijective (fun f : A ⟶ A => ηA ≫ F ◁ f)) (a : A ⟶ B) (b : B ⟶ A)
    (ha : ηA ≫ F ◁ a = ηB) (hb : ηB ≫ F ◁ b = ηA) : a ≫ b = 𝟙 A := by
  apply hA.injective
  dsimp only
  rw [whiskerLeft_comp, ← Category.assoc, ha, hb, whiskerLeft_id, Category.comp_id]

/-- The Hom-set bijection of a left dual, read through the identification of the monoidal
tensor product with the sheaf tensor product. -/
theorem sheafCoevaluation_bijective
    (F G : SheafOfModules.{u} (structureSheafRing X))
    (η : SheafOfModules.unit (structureSheafRing X) ⟶
      ((Stacks.SheafOfModules.Tensor.sheafTensor ⟨X.presheaf, X.IsSheaf⟩).obj F).obj G)
    (ε : ((Stacks.SheafOfModules.Tensor.sheafTensor ⟨X.presheaf, X.IsSheaf⟩).obj G).obj F ⟶
      SheafOfModules.unit (structureSheafRing X))
    (h : IsLeftDual X F G η ε)
    (Z : SheafOfModules.{u} (structureSheafRing X)) :
    Function.Bijective (fun f : G ⟶ Z => coevTensor X F G η ≫ F ◁ f) := by
  obtain ⟨p, hcoe, -⟩ := h
  rw [← hcoe]
  exact @coevaluation_bijective _ _ (monoidal X) F G Z p

/-- Two left duals of `F` are isomorphic, compatibly with their coevaluations and hence with
their evaluations. -/
theorem exists_coevaluation_iso
    (F D G : SheafOfModules.{u} (structureSheafRing X))
    (ηD : SheafOfModules.unit (structureSheafRing X) ⟶
      ((Stacks.SheafOfModules.Tensor.sheafTensor ⟨X.presheaf, X.IsSheaf⟩).obj F).obj D)
    (εD : ((Stacks.SheafOfModules.Tensor.sheafTensor ⟨X.presheaf, X.IsSheaf⟩).obj D).obj F ⟶
      SheafOfModules.unit (structureSheafRing X))
    (hD : IsLeftDual X F D ηD εD)
    (ηG : SheafOfModules.unit (structureSheafRing X) ⟶
      ((Stacks.SheafOfModules.Tensor.sheafTensor ⟨X.presheaf, X.IsSheaf⟩).obj F).obj G)
    (εG : ((Stacks.SheafOfModules.Tensor.sheafTensor ⟨X.presheaf, X.IsSheaf⟩).obj G).obj F ⟶
      SheafOfModules.unit (structureSheafRing X))
    (hG : IsLeftDual X F G ηG εG) :
    ∃ e : D ≅ G, coevTensor X F G ηG ≫ F ◁ e.inv = coevTensor X F D ηD ∧
      e.inv ▷ F ≫ evalTensor X F D εD = evalTensor X F G εG := by
  obtain ⟨pD, hcoeD, hevalD⟩ := id hD
  obtain ⟨pG, hcoeG, hevalG⟩ := id hG
  obtain ⟨f, hf⟩ :=
    (sheafCoevaluation_bijective X F D ηD εD hD G).surjective (coevTensor X F G ηG)
  obtain ⟨g, hg⟩ :=
    (sheafCoevaluation_bijective X F G ηG εG hG D).surjective (coevTensor X F D ηD)
  dsimp only at hf hg
  have hfg := comp_eq_id_of_coevaluation_eq F
    (sheafCoevaluation_bijective X F D ηD εD hD D) f g hf hg
  have hgf := comp_eq_id_of_coevaluation_eq F
    (sheafCoevaluation_bijective X F G ηG εG hG G) g f hg hf
  refine ⟨⟨f, g, hfg, hgf⟩, hg, ?_⟩
  have hev := evaluation_eq_of_coevaluation_eq F D G pD pG g (by rw [hcoeG, hcoeD]; exact hg)
  rw [hevalD, hevalG] at hev
  exact hev

/-- Existence of the isomorphism of Stacks 0FNW (2) together with **both** of its characterising
formulas on local sections. The two formulas are extracted separately by `dualSheafIso` and
`evaluation_eq_dualSheafIso_inv`, which need the same choice of isomorphism; making the choice
once, here, is what lets the second be stated about the first's isomorphism. -/
theorem dualSheafIsoAux
    (F G : SheafOfModules.{u} (structureSheafRing X))
    (η : SheafOfModules.unit (structureSheafRing X) ⟶
      ((Stacks.SheafOfModules.Tensor.sheafTensor ⟨X.presheaf, X.IsSheaf⟩).obj F).obj G)
    (ε : ((Stacks.SheafOfModules.Tensor.sheafTensor ⟨X.presheaf, X.IsSheaf⟩).obj G).obj F ⟶
      SheafOfModules.unit (structureSheafRing X))
    (h : IsLeftDual X F G η ε) :
    Nonempty { e : dualSheaf X F ≅ G //
      (∀ (U : Opens X.carrier) (lam : (dualSheaf X F).val.obj (op U))
        (n : ℕ) (f : Fin n → F.val.obj (op U)) (g : Fin n → G.val.obj (op U)),
        (η.val.app (op U)).hom (1 : X.presheaf.obj (op U)) =
          toTensorSheafSection X F G (op U)
            (∑ i, f i ⊗ₜ[X.presheaf.obj (op U)] g i) →
        (e.hom.val.app (op U)).hom lam =
          ∑ i, dualEval X F lam (f i) • g i) ∧
      ∀ (U : Opens X.carrier) (y : G.val.obj (op U)) (x : F.val.obj (op U)),
        (ε.val.app (op U)).hom
            (toTensorSheafSection X G F (op U) (y ⊗ₜ[X.presheaf.obj (op U)] x)) =
          dualEval X F ((e.inv.val.app (op U)).hom y) x } := by
  classical
  have hF : IsLocallyFiniteFreeSummand X F :=
    isLocallyFiniteFreeSummand_of_isLeftDual X F G η ε h
  have hex := exists_coevaluation_iso X F (dualSheaf X F) G
    (coevaluation X F hF) (evaluation X F) (isLeftDual_dualSheaf X F hF) η ε h
  let e := Classical.choose hex
  have he := (Classical.choose_spec hex).1
  have hev := (Classical.choose_spec hex).2
  refine ⟨⟨e, ?_, ?_⟩⟩
  · intro U lam n f g hη
    let d : Fin n → (dualSheaf X F).val.obj (op U) :=
      fun i => (e.inv.val.app (op U)).hom (g i)
    have hstep : ((coevTensor X F G η).val.app (op U)).hom (unitSection X (op U) 1) =
        ∑ i, tensorObjTmul X F G (op U) (f i) (g i) :=
      hη.trans (tensorSection_sum X F G (op U) Finset.univ
        (fun i => f i ⊗ₜ[X.presheaf.obj (op U)] g i))
    have hterm (i : Fin n) :
        ((F ◁ e.inv).val.app (op U)).hom (tensorObjTmul X F G (op U) (f i) (g i)) =
          toTensorSheafSection X F (dualSheaf X F) (op U)
            (f i ⊗ₜ[X.presheaf.obj (op U)] d i) :=
      whiskerLeft_tmul X F e.inv (op U) (f i) (g i)
    have heU := congrArg (fun q : 𝟙_ (SheafOfModules.{u} (structureSheafRing X)) ⟶
        F ⊗ dualSheaf X F => (q.val.app (op U)).hom (unitSection X (op U) 1)) he
    have hηD : ((coevaluation X F hF).val.app (op U)).hom (1 : X.presheaf.obj (op U)) =
        ∑ i, toTensorSheafSection X F (dualSheaf X F) (op U)
          (f i ⊗ₜ[X.presheaf.obj (op U)] d i) := by
      refine heU.symm.trans ?_
      refine Eq.trans (sheaf_comp_app_apply X (coevTensor X F G η) (F ◁ e.inv) (op U)
        (unitSection X (op U) 1)) ?_
      rw [hstep, map_sum]
      exact Finset.sum_congr rfl fun i _ => hterm i
    have hd := dual_sum_identity X F U f d
      (coevaluation_sum_identity X F hF U f d hηD) lam
    have hfinal := congrArg (fun z : (dualSheaf X F).val.obj (op U) =>
      (e.hom.val.app (op U)).hom z) hd
    rw [map_sum] at hfinal
    refine hfinal.symm.trans ?_
    refine Finset.sum_congr rfl fun i _ => ?_
    refine Eq.trans ((e.hom.val.app (op U)).hom.map_smul
      (dualEval X F lam (f i)) (d i)) ?_
    refine congrArg (fun z : G.val.obj (op U) => dualEval X F lam (f i) • z) ?_
    exact congrArg (fun q : G ⟶ G => (q.val.app (op U)).hom (g i)) e.inv_hom_id
  · intro U y x
    have hcomp : ((e.inv ▷ F ≫ evaluationTensor X F).val.app (op U)).hom
        (tensorObjTmul X G F (op U) y x) =
        unitSection X (op U) (dualEval X F ((e.inv.val.app (op U)).hom y) x) := by
      refine Eq.trans (sheaf_comp_app_apply X (e.inv ▷ F) (evaluationTensor X F) (op U)
        (tensorObjTmul X G F (op U) y x)) ?_
      rw [whiskerRight_tmul]
      exact evaluation_tmul X F U ((e.inv.val.app (op U)).hom y) x
    refine Eq.trans ?_ hcomp
    exact (congrArg (fun q : G ⊗ F ⟶ 𝟙_ (SheafOfModules.{u} (structureSheafRing X)) =>
      (q.val.app (op U)).hom (tensorObjTmul X G F (op U) y x)) hev).symm

/-- The isomorphism of Stacks 0FNW (2), carrying both characterising formulas. -/
noncomputable def dualSheafIsoFull
    (F G : SheafOfModules.{u} (structureSheafRing X))
    (η : SheafOfModules.unit (structureSheafRing X) ⟶
      ((Stacks.SheafOfModules.Tensor.sheafTensor ⟨X.presheaf, X.IsSheaf⟩).obj F).obj G)
    (ε : ((Stacks.SheafOfModules.Tensor.sheafTensor ⟨X.presheaf, X.IsSheaf⟩).obj G).obj F ⟶
      SheafOfModules.unit (structureSheafRing X))
    (h : IsLeftDual X F G η ε) :
    { e : dualSheaf X F ≅ G //
      (∀ (U : Opens X.carrier) (lam : (dualSheaf X F).val.obj (op U))
        (n : ℕ) (f : Fin n → F.val.obj (op U)) (g : Fin n → G.val.obj (op U)),
        (η.val.app (op U)).hom (1 : X.presheaf.obj (op U)) =
          toTensorSheafSection X F G (op U)
            (∑ i, f i ⊗ₜ[X.presheaf.obj (op U)] g i) →
        (e.hom.val.app (op U)).hom lam =
          ∑ i, dualEval X F lam (f i) • g i) ∧
      ∀ (U : Opens X.carrier) (y : G.val.obj (op U)) (x : F.val.obj (op U)),
        (ε.val.app (op U)).hom
            (toTensorSheafSection X G F (op U) (y ⊗ₜ[X.presheaf.obj (op U)] x)) =
          dualEval X F ((e.inv.val.app (op U)).hom y) x } :=
  Classical.choice (dualSheafIsoAux X F G η ε h)

/-- **Stacks Project, Tag 0FNW (2).** A left dual `G` of `F` is canonically isomorphic to the
dual sheaf `F^∨ = SheafHom(F, O_X)`. The isomorphism sends a local functional `lam` over `U` to
`∑ i, lam (f i) • g i` for any expansion `η(1) = ∑ i, f i ⊗ g i` of the coevaluation over `U`;
in particular that expression does not depend on the chosen expansion. -/
@[stacks 0FNW "dual_sheaf_isomorphism"]
noncomputable def dualSheafIso
    (F G : SheafOfModules.{u} (structureSheafRing X))
    (η : SheafOfModules.unit (structureSheafRing X) ⟶
      ((Stacks.SheafOfModules.Tensor.sheafTensor ⟨X.presheaf, X.IsSheaf⟩).obj F).obj G)
    (ε : ((Stacks.SheafOfModules.Tensor.sheafTensor ⟨X.presheaf, X.IsSheaf⟩).obj G).obj F ⟶
      SheafOfModules.unit (structureSheafRing X))
    (h : IsLeftDual X F G η ε) :
    { e : dualSheaf X F ≅ G //
      ∀ (U : Opens X.carrier) (lam : (dualSheaf X F).val.obj (op U))
        (n : ℕ) (f : Fin n → F.val.obj (op U)) (g : Fin n → G.val.obj (op U)),
        (η.val.app (op U)).hom (1 : X.presheaf.obj (op U)) =
          toTensorSheafSection X F G (op U)
            (∑ i, f i ⊗ₜ[X.presheaf.obj (op U)] g i) →
        (e.hom.val.app (op U)).hom lam =
          ∑ i, dualEval X F lam (f i) • g i } :=
  ⟨(dualSheafIsoFull X F G η ε h).val, (dualSheafIsoFull X F G η ε h).property.1⟩

/-- **Stacks Project, Tag 0FNW (3).** Pairing a local section of a left dual `G` with a local
section of `F` under the evaluation `ε` is ordinary evaluation of the corresponding local
functional on `F`, the correspondence being the inverse of the isomorphism of Stacks 0FNW (2). -/
@[stacks 0FNW "evaluation_formula"]
theorem evaluation_eq_dualSheafIso_inv
    (F G : SheafOfModules.{u} (structureSheafRing X))
    (η : SheafOfModules.unit (structureSheafRing X) ⟶
      ((Stacks.SheafOfModules.Tensor.sheafTensor ⟨X.presheaf, X.IsSheaf⟩).obj F).obj G)
    (ε : ((Stacks.SheafOfModules.Tensor.sheafTensor ⟨X.presheaf, X.IsSheaf⟩).obj G).obj F ⟶
      SheafOfModules.unit (structureSheafRing X))
    (h : IsLeftDual X F G η ε)
    (U : Opens X.carrier)
    (g : G.val.obj (op U)) (f : F.val.obj (op U)) :
    (ε.val.app (op U)).hom
        (toTensorSheafSection X G F (op U) (g ⊗ₜ[X.presheaf.obj (op U)] f)) =
      (((((dualSheafIso X F G η ε h).val.inv.val.app (op U)).hom g).app
        (op (Over.mk (𝟙 U)))).hom f) :=
  (dualSheafIsoFull X F G η ε h).property.2 U g f

end Stacks.SheafOfModules.OnSpace
