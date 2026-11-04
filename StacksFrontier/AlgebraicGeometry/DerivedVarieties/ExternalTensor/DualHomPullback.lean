module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackAlgebraIso
public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.ExternalTensor.DualHomPure
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.DualSectionsInfinitesimal

/-!
# The two factor sections of the external-tensor duality bijection are pullbacks

`StacksFrontier.AlgebraicGeometry.DerivedVarieties.ExternalTensor.DualHomPure` computes the value
of the duality bijection

`Hom_{𝒪_{X ×_S Y}}(ℰ ⊠ 𝒢, ℱ) ≃ Γ(X ×_S Y, ℱ ⊗ (ℰ^∨ ⊠ 𝒢^∨))`

at a pure map `a ⊠ b`: it is a product of two *factor sections*, the first built from the
coevaluation of `AlgebraicGeometry.externalTensorProductFirstPairing` and the second from that
of `AlgebraicGeometry.externalTensorProductSecondPairing`.  Those two sections live on
`X ×_S Y`, and its implementation notes record what was then missing: that the first of them is
the pullback along `pr₁` of the `X`-level duality section of `a`.  That is a compatibility of
`Stacks.Chow.pullbackDualMap`, the dual base-change map of [Stacks, Tag 0GMX], with the
*coevaluations*, of which the library had only the invertibility
(`Stacks.Chow.pullbackDualMap_isIso`).  This file proves that compatibility and deduces the
identification.

Everything is proved for an arbitrary morphism of schemes `q : W ⟶ X` and a finite locally free
`𝒪_X`-module `ℰ`; the two factor pairings are the case `q = pr₁` and `q = pr₂`, and the
specialisations are recorded at the end.

## Main results

* `CategoryTheory.coevaluation_eq_of_trace_eq_id`: **a section of `A ⊗ A'` whose trace against
  the evaluation of an exact pairing is the identity of `A` is the coevaluation of that
  pairing.**  This is the uniqueness `CategoryTheory.tensorRightHomEquiv` provides, in the form
  in which a candidate coevaluation can be checked.  It is the mirror of
  `Stacks.SheafOfModules.OnSpace.coevaluation_bijective`, which says that the coevaluation
  determines a morphism out of the dual.
* `Stacks.SheafOfModules.OnSpace.trace_apply_of_sum`: that trace, on a local section, computed
  from a local expansion of the section and the values of the evaluation.
* `AlgebraicGeometry.hom_ext_of_pullbackUnit_locally`: two morphisms out of `q^*ℰ` which agree
  on the canonical images of the local sections of `ℰ` over the members of a covering of `X`
  are equal.
* `AlgebraicGeometry.pullbackCoevaluation_apply_one` and
  `AlgebraicGeometry.pullbackDualPairing_evaluation_tmul`: the two sectionwise computations the
  check consumes — the value at `1` of the pulled-back coevaluation, and the value of the
  evaluation of the transported pairing on a pure tensor of canonical images.
* `AlgebraicGeometry.pullbackDualSheafIso_coevaluation_eq_pullback`: **the dual base-change map
  is compatible with the coevaluations.**  The coevaluation of `q^*(ℰ^∨)` as a left dual of
  `q^*ℰ` is the pullback of the coevaluation of `ℰ^∨` as a left dual of `ℰ`, read through the
  identification `𝒪_W ≅ q^*𝒪_X` of `Stacks.PullbackAlgebra.pullbackUnitIso` and the comparison
  `q^*(ℰ ⊗ ℰ^∨) ≅ q^*ℰ ⊗ q^*(ℰ^∨)` of [Stacks, Tag 01CD].
* `AlgebraicGeometry.pullbackTensorIso_whiskerRight`: the comparison of [Stacks, Tag 01CD] is
  natural in its first argument, in the whiskering spelling.
* `AlgebraicGeometry.pullbackDualSheafIso_dualSection_eq_pullback`: **the factor section is a
  pullback.**  For `a : ℰ ⟶ ℰ₂` the coevaluation of the transported pairing followed by `q^*a`
  is the pullback of `AlgebraicGeometry.dualTensorHomEquiv`'s value at `a`.
* `AlgebraicGeometry.externalTensorProductFirstPairing_coevaluation_eq_pullback`,
  `…_dualSection_eq_pullback` and their `Second` counterparts: the same two statements at the
  two factor pairings of `AlgebraicGeometry.externalTensorProductExactPairing`, which is the
  form `DualHomPure` asks for.
* `AlgebraicGeometry.externalTensorDualTensorHomEquiv_externalTensorProductMap_pullback`:
  **the value of the duality bijection at `a ⊠ b`, with both factor sections written as
  pullbacks** — so that the value depends on `a` and on `b` only through one section on `X` and
  one section on `Y`.

## Implementation notes

**Why the coevaluation is checked and not computed.**  `Stacks.Chow.pullbackDualMap` is defined
by currying the pulled-back evaluation pairing, so its compatibility with the *evaluations* is
close to definitional and is already available on canonical images, as
`Stacks.FundamentalGroup.pullbackDualSheafIso_unit_apply`.  Nothing about the coevaluation
follows from that by unfolding: a coevaluation is extra data.  What makes the deduction possible
is that in an exact pairing the coevaluation is *determined* by the evaluation —
`CategoryTheory.coevaluation_eq_of_trace_eq_id` — so the candidate, the pullback of the
`X`-level coevaluation, only has to be checked, and the check is an identity of morphisms
`q^*ℰ ⟶ q^*ℰ` which may be tested on the canonical images of local sections of `ℰ`.  On those
the two inputs are the local expansion of the coevaluation,
`Stacks.SheafOfModules.OnSpace.coevaluation_locally_sum`, and the dual-basis identity it
satisfies, `Stacks.SheafOfModules.OnSpace.coevaluation_sum_identity`.

*No monoidal structure on `q^*` is used, and none is available at this monoidal structure.*  A
monoidal functor carries an exact pairing to an exact pairing, which would give this statement
at once, and the module pullback of a morphism of ringed spaces is monoidal twice over: for the
*localized* monoidal structure, in
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackMonoidalSheaf`, whose tensorator is not
identified with `Stacks.RingedSpace.comparison`; and — with the comparison of
[Stacks, Tag 01CD] for its tensorator, and braided at that — for
`Stacks.PullbackGradedAlgebra.monoidalCategory`, in
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackTensorCoherence` and
`...PullbackTensorComparisonBraided`.  Neither is the structure the left-duality of a finite
locally free module is stated at, which is `Stacks.SheafOfModules.OnSpace.monoidal`: that is a
third term on the same category, not definitionally equal to
`Stacks.PullbackGradedAlgebra.monoidalCategory`, and nothing identifies their associators — the
situation the implementation notes of
`StacksFrontier.AlgebraicGeometry.DerivedVarieties.ExternalTensor.DualHomPure` describe.  The route
taken here needs no coherence at all: only the comparison of [Stacks, Tag 01CD] on pure tensors
of canonical images, `Stacks.Chow.comparison_tensorSheafPure`.

**The two spellings, and where the crossings are put.**  The sectionwise formulas for the
associator, the unitors and the whiskerings of [Stacks, Tag 01CA] are stated over a *ringed
space* and the category `CategoryTheory.SheafOfModules (structureSheafRing Z)`, while the
duality material here is stated over a *scheme* and `AlgebraicGeometry.Scheme.Modules`.  The two
are definitionally equal but their sites are spelled through different projection chains, and a
`CategoryTheory.Functor.obj` of the module pullback — an abstract left adjoint — sits between
them, so a defeq check that has to cross the two spellings *inside* a term as large as a
five-fold composite applied to a local section exhausts the elaborator's recursion budget.  Two
devices keep every crossing small.  First,
`Stacks.SheafOfModules.OnSpace.trace_apply_of_sum` takes the composite as a variable `chi`
together with the equation defining it, so that its conclusion mentions no structural
morphism: the crossing of the *equation* is a crossing of bare morphisms, which is cheap, and
the crossing of the conclusion is a crossing of a variable.  Second,
`pullbackDualPairing_trace_eq_id` takes the section and the evaluation as variables too, so
that the statement proved by the sectionwise computation and the statement
`CategoryTheory.coevaluation_eq_of_trace_eq_id` asks for are syntactically the same.  For the
same reason no `rw` is used at the scheme level below: a goal mentioning
`AlgebraicGeometry.Scheme.Modules.pullback` is not type-correct at the transparency at which
`rw` re-checks its rewrites, the pattern recorded in
`StacksFrontier.CategoryTheory.Category.CompositionChains`, so the chains are built with
`Eq.trans` and `congrArg`.

**Naturality of the comparison is not re-proved.**  `Stacks.RingedSpace.comparisonNatTrans`
already has it, as a morphism of bifunctors; `AlgebraicGeometry.pullbackTensorIso_whiskerRight`
is that naturality at `(a, 𝟙)` with the bifunctor's action rewritten as a whiskering, which is
`Stacks.SheafOfModules.OnSpace.tensorHom_eq_tensorSheafMap` together with
`CategoryTheory.MonoidalCategory.tensorHom_id`.

## References

* [Stacks Project, Tag 0GMX](https://stacks.math.columbia.edu/tag/0GMX)
* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
* [Stacks Project, Tag 0FNV](https://stacks.math.columbia.edu/tag/0FNV)
* [Stacks Project, Tag 0G46](https://stacks.math.columbia.edu/tag/0G46)
* [Stacks Project, Tag 0G0A](https://stacks.math.columbia.edu/tag/0G0A)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open Stacks.FiniteLocallyFree Stacks.SheafOfModules.TensorStalkRingedSpace
open scoped AlgebraicGeometry

universe v u

namespace CategoryTheory

/-- **A section of `A ⊗ A'` whose trace against the evaluation is the identity is the
coevaluation.**  For an exact pairing `p` between `A` and `A'` and a section
`s : 𝟙_ C ⟶ A ⊗ A'`, the composite `A ≅ 𝟙_ ⊗ A ⟶ (A ⊗ A') ⊗ A ≅ A ⊗ (A' ⊗ A) ⟶ A ⊗ 𝟙_ ≅ A`
formed from `s` and the evaluation of `p` is the identity exactly when `s` is the coevaluation
of `p`.

This is the injectivity half of `CategoryTheory.tensorRightHomEquiv` at the unit object: the
displayed composite is the inverse bijection applied to `s`, read along the left unitor, and
Mathlib's `CategoryTheory.tensorRightHomEquiv_symm_coevaluation_comp_whiskerRight` evaluates it
at the coevaluation.  It is the mirror of
`Stacks.SheafOfModules.OnSpace.coevaluation_bijective`, which says instead that composing with
the coevaluation is a bijection on morphisms out of the dual. -/
theorem coevaluation_eq_of_trace_eq_id {C : Type u} [Category.{v} C] [MonoidalCategory C]
    {A A' : C} (p : ExactPairing A A') (s : 𝟙_ C ⟶ A ⊗ A')
    (h : (λ_ A).inv ≫ s ▷ A ≫ (α_ A A' A).hom ≫
        A ◁ @ExactPairing.evaluation _ _ _ A A' p ≫ (ρ_ A).hom = 𝟙 A) :
    s = @ExactPairing.coevaluation _ _ _ A A' p := by
  refine (@tensorRightHomEquiv C _ _ (𝟙_ C) A A' A p).symm.injective ?_
  have h2 := @tensorRightHomEquiv_symm_coevaluation_comp_whiskerRight C _ _ A A' A p (𝟙 A)
  rw [MonoidalCategory.id_whiskerRight, Category.comp_id, Category.comp_id] at h2
  refine Eq.trans ?_ h2.symm
  exact ((λ_ A).inv_comp_eq).mp h |>.trans (Category.comp_id _)

/-- Reassociation of the composite that the comparison of a pullback of a duality section comes
out as: a first factor which splits as `m₁ ≫ m₂` and a square `m₂ ≫ c₂ = c₁ ≫ w`.  Stated in an
abstract category because that is where `CategoryTheory.Category.assoc` can be rewritten
with. -/
private theorem assoc_comp_eq_of_factor {C : Type u} [Category.{v} C] {A B D F G H : C}
    (k : A ⟶ B) (m₁ : B ⟶ D) (m₂ : D ⟶ F) (mD : B ⟶ F) (c₂ : F ⟶ G) (c₁ : D ⟶ H) (w : H ⟶ G)
    (hmD : mD = m₁ ≫ m₂) (hnat : m₂ ≫ c₂ = c₁ ≫ w) :
    (k ≫ m₁ ≫ c₁) ≫ w = k ≫ mD ≫ c₂ := by
  subst hmD
  simp only [Category.assoc, hnat]

end CategoryTheory

namespace Stacks.SheafOfModules.OnSpace

open Stacks.SheafOfModules.TensorStalkRingedSpace

attribute [local instance] monoidal

/-- **The trace of a section against a pairing, on a local section.**  Let `s : 𝒪_Z ⟶ A ⊗ A'`
be a section whose value at `1` over `V` is the finite sum `∑ j, e j ⊗ l j`, and let
`eps : A' ⊗ A ⟶ 𝒪_Z` be a pairing whose value on `l j ⊗ m` is the function `c j`.  Then the
composite `A ≅ 𝒪_Z ⊗ A ⟶ (A ⊗ A') ⊗ A ≅ A ⊗ (A' ⊗ A) ⟶ A ⊗ 𝒪_Z ≅ A` carries `m` to
`∑ j, c j • e j`.

The composite is taken as a variable `chi` together with the equation `hchi` defining it, so
that the conclusion mentions neither the associator nor a unitor; that is what makes the lemma
usable from a goal written in the scheme-level spelling of this category, where a defeq check
inside a term of that size is not affordable. -/
theorem trace_apply_of_sum (Z : AlgebraicGeometry.RingedSpace.{u, u})
    (A A' : SheafOfModules.{u} (structureSheafRing Z))
    (s : 𝟙_ (SheafOfModules.{u} (structureSheafRing Z)) ⟶ A ⊗ A')
    (eps : A' ⊗ A ⟶ 𝟙_ (SheafOfModules.{u} (structureSheafRing Z))) (chi : A ⟶ A)
    (hchi : chi = (λ_ A).inv ≫ s ▷ A ≫ (α_ A A' A).hom ≫ A ◁ eps ≫ (ρ_ A).hom)
    (V : (TopologicalSpace.Opens Z.carrier)ᵒᵖ) (m : A.val.obj V)
    {I : Type*} [Fintype I] (e : I → A.val.obj V) (l : I → A'.val.obj V)
    (c : I → Z.presheaf.obj V)
    (hs : ((s.val.app V).hom) (unitSection Z V 1) =
      ∑ j, tensorObjTmul Z A A' V (e j) (l j))
    (heps : ∀ j, ((eps.val.app V).hom) (tensorObjTmul Z A' A V (l j) m) =
      unitSection Z V (c j)) :
    ((chi.val.app V).hom) m = ∑ j, c j • e j := by
  classical
  subst hchi
  rw [sheaf_comp_app_apply, leftUnitor_inv_apply, sheaf_comp_app_apply, whiskerRight_tmul, hs,
    tensorObjTmul_sum_left, sheaf_comp_app_apply, map_sum]
  have h1 : ∀ j : I, (((α_ A A' A).hom).val.app V).hom
      (tensorObjTmul Z (A ⊗ A') A V (tensorObjTmul Z A A' V (e j) (l j)) m) =
      tensorObjTmul Z A (A' ⊗ A) V (e j) (tensorObjTmul Z A' A V (l j) m) :=
    fun j => associator_tmul Z A A' A V (e j) (l j) m
  rw [Finset.sum_congr rfl fun j _ => h1 j, sheaf_comp_app_apply, map_sum]
  have h2 : ∀ j : I, ((A ◁ eps).val.app V).hom
      (tensorObjTmul Z A (A' ⊗ A) V (e j) (tensorObjTmul Z A' A V (l j) m)) =
      tensorObjTmul Z A (𝟙_ (SheafOfModules.{u} (structureSheafRing Z))) V (e j)
        (unitSection Z V (c j)) :=
    fun j => (whiskerLeft_tmul Z A eps V (e j) _).trans (by rw [heps j])
  rw [Finset.sum_congr rfl fun j _ => h2 j, map_sum]
  exact Finset.sum_congr rfl fun j _ => rightUnitor_tmul Z A V (e j) (c j)

end Stacks.SheafOfModules.OnSpace

namespace AlgebraicGeometry

open Stacks.AlgebraicGeometry.ReflexiveModules AlgebraicGeometry.VectorBundleKZero
open Stacks.SheafOfModules.OnSpace (tensorObjTmul unitSection sheaf_comp_app_apply
  coevaluation_locally_sum coevaluation_sum_identity dualEval map_id_apply hom_ext_of_locally
  trace_apply_of_sum evaluation_tmul whiskerRight_tmul)

attribute [local instance] onSpaceModulesMonoidal

variable {W X : Scheme.{u}} (q : W ⟶ X)

/-! ### Extensionality for morphisms out of a pullback -/

/-- The identity morphism of a sheaf of modules on a scheme does nothing to a local section. -/
private theorem id_val_app_apply (Z : Scheme.{u}) (N : Z.Modules) (V : Z.Opens)
    (y : N.val.obj (op V)) : (((𝟙 N : N ⟶ N)).val.app (op V)).hom y = y := rfl

/-- **Two morphisms out of `q^*ℰ` which agree on the canonical images of local sections of `ℰ`
over the members of a covering of `X` are equal.**  A morphism out of `q^*ℰ` is determined by
its adjoint transpose, which is a morphism `ℰ ⟶ q_*(−)` of sheaves of modules on `X` and is
determined on the sections of `ℰ`, and a morphism of sheaves of modules is determined locally,
`Stacks.SheafOfModules.OnSpace.hom_ext_of_locally`. -/
theorem hom_ext_of_pullbackUnit_locally (A : X.Modules) (N : W.Modules)
    (φ ψ : (Scheme.Modules.pullback q).obj A ⟶ N)
    (h : ∀ x : X.toRingedSpace.carrier, ∃ V₀ : X.Opens, x ∈ V₀ ∧
      ∀ (V : X.Opens) (_ : V ⟶ V₀) (m : A.val.obj (op V)),
        (φ.val.app (op (q ⁻¹ᵁ V))).hom
            (((Scheme.Modules.pullbackPushforwardAdjunction q).unit.app A).val.app (op V) m) =
          (ψ.val.app (op (q ⁻¹ᵁ V))).hom
            (((Scheme.Modules.pullbackPushforwardAdjunction q).unit.app A).val.app (op V) m)) :
    φ = ψ := by
  refine ((Scheme.Modules.pullbackPushforwardAdjunction q).homEquiv A N).injective ?_
  refine hom_ext_of_locally X.toRingedSpace _ _ fun x => ?_
  obtain ⟨V₀, hx, hV⟩ := h x
  refine ⟨V₀, hx, fun V k => ?_⟩
  ext m
  exact (Stacks.RingedSpace.homEquiv_val_app q.toLRSHom.toShHom A N φ (op V) m).trans
    ((hV V k m).trans
      (Stacks.RingedSpace.homEquiv_val_app q.toLRSHom.toShHom A N ψ (op V) m).symm)

/-! ### The two sectionwise computations -/

/-- **The pullback of the coevaluation of `ℰ`, at the function `1`.**  On an open `U` of `X`
over which the coevaluation of `ℰ` expands as `∑ j, e j ⊗ l j`, the section
`𝒪_W ≅ q^*𝒪_X ⟶ q^*(ℰ ⊗ ℰ^∨) ≅ q^*ℰ ⊗ q^*(ℰ^∨)` carries `1` to the sum of the pure tensors of
the canonical images of `e j` and of `l j`.

The three steps are: the identification `𝒪_W ≅ q^*𝒪_X` carries `1` to the canonical image of
`1`, which is `Stacks.Chow.pullbackObjUnitToUnit_unit_app` read backwards; the pullback of a
morphism acts on canonical images as the morphism does,
`Stacks.Chow.pullback_map_unit_app`; and the comparison of [Stacks, Tag 01CD] carries the
canonical image of a pure tensor to the pure tensor of the canonical images,
`Stacks.Chow.comparison_tensorSheafPure`. -/
theorem pullbackCoevaluation_apply_one (E : X.Modules)
    (hE : IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) E)
    (U : X.Opens) {n : ℕ} (e : Fin n → E.val.obj (op U))
    (l : Fin n → (dualSheaf E).val.obj (op U))
    (hexp : ((@ExactPairing.coevaluation _ _ (onSpaceModulesMonoidal X) E (dualSheaf E)
          (dualSheafExactPairing X E hE)).val.app (op U)).hom (1 : X.presheaf.obj (op U)) =
      ∑ j, tensorObjTmul X.toRingedSpace E (dualSheaf E) (op U) (e j) (l j)) :
    (((Stacks.PullbackAlgebra.pullbackUnitIso q.toLRSHom.toShHom).inv ≫
        (Scheme.Modules.pullback q).map
          (@ExactPairing.coevaluation _ _ (onSpaceModulesMonoidal X) E (dualSheaf E)
            (dualSheafExactPairing X E hE)) ≫
        (Stacks.Chow.pullbackTensorIso q E (dualSheaf E)).hom).val.app
        (op (q ⁻¹ᵁ U))).hom (unitSection W.toRingedSpace (op (q ⁻¹ᵁ U)) 1) =
      ∑ j, tensorObjTmul W.toRingedSpace ((Scheme.Modules.pullback q).obj E)
        ((Scheme.Modules.pullback q).obj (dualSheaf E)) (op (q ⁻¹ᵁ U))
        (((Scheme.Modules.pullbackPushforwardAdjunction q).unit.app E).val.app (op U) (e j))
        (((Scheme.Modules.pullbackPushforwardAdjunction q).unit.app
          (dualSheaf E)).val.app (op U) (l j)) := by
  classical
  have hone : (((Stacks.PullbackAlgebra.pullbackUnitIso q.toLRSHom.toShHom).hom).val.app
      (op (q ⁻¹ᵁ U))).hom (((Scheme.Modules.pullbackPushforwardAdjunction q).unit.app
        (SheafOfModules.unit X.ringCatSheaf)).val.app (op U) (1 : X.presheaf.obj (op U))) =
      unitSection W.toRingedSpace (op (q ⁻¹ᵁ U)) 1 :=
    (Stacks.Chow.pullbackObjUnitToUnit_unit_app q U (unitSection X.toRingedSpace (op U) 1)).trans
      (map_one (q.app U).hom)
  have hk : (((Stacks.PullbackAlgebra.pullbackUnitIso q.toLRSHom.toShHom).inv).val.app
      (op (q ⁻¹ᵁ U))).hom (unitSection W.toRingedSpace (op (q ⁻¹ᵁ U)) 1) =
      ((Scheme.Modules.pullbackPushforwardAdjunction q).unit.app
        (SheafOfModules.unit X.ringCatSheaf)).val.app (op U) (1 : X.presheaf.obj (op U)) :=
    (congrArg (fun z => (((Stacks.PullbackAlgebra.pullbackUnitIso
        q.toLRSHom.toShHom).inv).val.app (op (q ⁻¹ᵁ U))).hom z) hone).symm.trans
      (Stacks.Chow.iso_inv_val_app_hom_val_app
        (Stacks.PullbackAlgebra.pullbackUnitIso q.toLRSHom.toShHom) (q ⁻¹ᵁ U) _)
  have hg : (((Scheme.Modules.pullback q).map
        (@ExactPairing.coevaluation _ _ (onSpaceModulesMonoidal X) E (dualSheaf E)
          (dualSheafExactPairing X E hE))).val.app (op (q ⁻¹ᵁ U))).hom
      (((Scheme.Modules.pullbackPushforwardAdjunction q).unit.app
        (SheafOfModules.unit X.ringCatSheaf)).val.app (op U) (1 : X.presheaf.obj (op U))) =
      ((Scheme.Modules.pullbackPushforwardAdjunction q).unit.app
          ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩).obj E).obj
              (dualSheaf E)))).val.app (op U)
        (∑ j, tensorObjTmul X.toRingedSpace E (dualSheaf E) (op U) (e j) (l j)) :=
    (Stacks.Chow.pullback_map_unit_app q
        (@ExactPairing.coevaluation _ _ (onSpaceModulesMonoidal X) E (dualSheaf E)
          (dualSheafExactPairing X E hE)) U (unitSection X.toRingedSpace (op U) 1)).trans
      (congrArg (fun z => ((Scheme.Modules.pullbackPushforwardAdjunction q).unit.app
        ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩).obj E).obj
              (dualSheaf E)))).val.app (op U) z) hexp)
  have hc : (((Stacks.Chow.pullbackTensorIso q E (dualSheaf E)).hom).val.app
        (op (q ⁻¹ᵁ U))).hom
      (((Scheme.Modules.pullbackPushforwardAdjunction q).unit.app
          ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩).obj E).obj
              (dualSheaf E)))).val.app (op U)
        (∑ j, tensorObjTmul X.toRingedSpace E (dualSheaf E) (op U) (e j) (l j))) =
      ∑ j, tensorObjTmul W.toRingedSpace ((Scheme.Modules.pullback q).obj E)
        ((Scheme.Modules.pullback q).obj (dualSheaf E)) (op (q ⁻¹ᵁ U))
        (((Scheme.Modules.pullbackPushforwardAdjunction q).unit.app E).val.app (op U) (e j))
        (((Scheme.Modules.pullbackPushforwardAdjunction q).unit.app
          (dualSheaf E)).val.app (op U) (l j)) := by
    refine Eq.trans (congrArg (fun z => (((Stacks.Chow.pullbackTensorIso q E
        (dualSheaf E)).hom).val.app (op (q ⁻¹ᵁ U))).hom z) (map_sum _ _ _)) ?_
    refine Eq.trans (map_sum _ _ _) ?_
    exact Finset.sum_congr rfl fun j _ =>
      Stacks.Chow.comparison_tensorSheafPure q E (dualSheaf E) U (e j) (l j)
  exact Stacks.SheafOfModules.OnSpace.sheaf_comp3_app_apply_of W.toRingedSpace _ _ _
    (op (q ⁻¹ᵁ U)) _ hk hg hc

/-- **The evaluation of `q^*(ℰ^∨)` as a left dual of `q^*ℰ`, on a pure tensor of canonical
images.**  It is the pullback of the function the local functional computes.

The pairing is the canonical one of `q^*ℰ` transported along the dual base-change isomorphism
`AlgebraicGeometry.VectorBundleKZero.pullbackDualSheafIso`, so its evaluation is that
isomorphism followed by the canonical evaluation,
`CategoryTheory.exactPairingCongrRight_evaluation`; and on the canonical image of a local
functional the dual base-change map is computed by
`Stacks.FundamentalGroup.pullbackDualSheafIso_unit_apply`. -/
theorem pullbackDualPairing_evaluation_tmul (E : X.Modules)
    (hE : IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) E)
    (U : X.Opens) (lam : (dualSheaf E).val.obj (op U)) (m : E.val.obj (op U)) :
    ((@ExactPairing.evaluation _ _ (onSpaceModulesMonoidal W)
          ((Scheme.Modules.pullback q).obj E)
          ((Scheme.Modules.pullback q).obj (dualSheaf E))
          (@exactPairingCongrRight _ _ (onSpaceModulesMonoidal W)
            ((Scheme.Modules.pullback q).obj E)
            ((Scheme.Modules.pullback q).obj (dualSheaf E))
            (dualSheaf ((Scheme.Modules.pullback q).obj E))
            (dualSheafExactPairing W ((Scheme.Modules.pullback q).obj E)
              (isFiniteLocallyFree_pullback q E hE))
            (pullbackDualSheafIso q E hE))).val.app (op (q ⁻¹ᵁ U))).hom
        (tensorObjTmul W.toRingedSpace ((Scheme.Modules.pullback q).obj (dualSheaf E))
          ((Scheme.Modules.pullback q).obj E) (op (q ⁻¹ᵁ U))
          (((Scheme.Modules.pullbackPushforwardAdjunction q).unit.app
            (dualSheaf E)).val.app (op U) lam)
          (((Scheme.Modules.pullbackPushforwardAdjunction q).unit.app E).val.app (op U) m)) =
      unitSection W.toRingedSpace (op (q ⁻¹ᵁ U))
        ((q.app U).hom (dualEval X.toRingedSpace E lam m)) := by
  refine Eq.trans (congrArg (fun φ => (φ.val.app (op (q ⁻¹ᵁ U))).hom
      (tensorObjTmul W.toRingedSpace ((Scheme.Modules.pullback q).obj (dualSheaf E))
        ((Scheme.Modules.pullback q).obj E) (op (q ⁻¹ᵁ U))
        (((Scheme.Modules.pullbackPushforwardAdjunction q).unit.app
          (dualSheaf E)).val.app (op U) lam)
        (((Scheme.Modules.pullbackPushforwardAdjunction q).unit.app E).val.app (op U) m)))
    (@exactPairingCongrRight_evaluation _ _ (onSpaceModulesMonoidal W)
      ((Scheme.Modules.pullback q).obj E)
      ((Scheme.Modules.pullback q).obj (dualSheaf E))
      (dualSheaf ((Scheme.Modules.pullback q).obj E))
      (dualSheafExactPairing W ((Scheme.Modules.pullback q).obj E)
        (isFiniteLocallyFree_pullback q E hE))
      (pullbackDualSheafIso q E hE))) ?_
  refine Eq.trans (sheaf_comp_app_apply W.toRingedSpace _ _ (op (q ⁻¹ᵁ U)) _) ?_
  refine Eq.trans (congrArg (fun z => ((@ExactPairing.evaluation _ _ (onSpaceModulesMonoidal W)
      ((Scheme.Modules.pullback q).obj E)
      (dualSheaf ((Scheme.Modules.pullback q).obj E))
      (dualSheafExactPairing W ((Scheme.Modules.pullback q).obj E)
        (isFiniteLocallyFree_pullback q E hE))).val.app (op (q ⁻¹ᵁ U))).hom z)
    (whiskerRight_tmul W.toRingedSpace (pullbackDualSheafIso q E hE).hom
      ((Scheme.Modules.pullback q).obj E) (op (q ⁻¹ᵁ U)) _ _)) ?_
  refine Eq.trans (evaluation_tmul W.toRingedSpace ((Scheme.Modules.pullback q).obj E)
    (q ⁻¹ᵁ U) _ _) ?_
  exact congrArg (unitSection W.toRingedSpace (op (q ⁻¹ᵁ U)))
    (Stacks.FundamentalGroup.pullbackDualSheafIso_unit_apply q E
      (@Stacks.StalkFreeBridge.isFiniteLocallyFree_of_finiteLocallyFree X E hE) U lam m)

/-! ### The dual base-change map and the coevaluations -/

/-- The check `CategoryTheory.coevaluation_eq_of_trace_eq_id` asks for, with the candidate
section and the evaluation left as variables and their values on local sections taken as
hypotheses.  Keeping them free is what makes the statement proved here and the statement that
lemma consumes syntactically the same; see the implementation notes. -/
private theorem pullbackDualPairing_trace_eq_id (E : X.Modules)
    (hE : IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) E)
    (s : 𝟙_ W.Modules ⟶ ((Scheme.Modules.pullback q).obj E) ⊗
      ((Scheme.Modules.pullback q).obj (dualSheaf E)))
    (eps : ((Scheme.Modules.pullback q).obj (dualSheaf E)) ⊗
      ((Scheme.Modules.pullback q).obj E) ⟶ 𝟙_ W.Modules)
    (hs : ∀ (V : X.Opens) (n : ℕ) (e : Fin n → E.val.obj (op V))
        (l : Fin n → (dualSheaf E).val.obj (op V)),
        ((@ExactPairing.coevaluation _ _ (onSpaceModulesMonoidal X) E (dualSheaf E)
              (dualSheafExactPairing X E hE)).val.app (op V)).hom
            (1 : X.presheaf.obj (op V)) =
          ∑ j, tensorObjTmul X.toRingedSpace E (dualSheaf E) (op V) (e j) (l j) →
        (s.val.app (op (q ⁻¹ᵁ V))).hom (unitSection W.toRingedSpace (op (q ⁻¹ᵁ V)) 1) =
          ∑ j, tensorObjTmul W.toRingedSpace ((Scheme.Modules.pullback q).obj E)
            ((Scheme.Modules.pullback q).obj (dualSheaf E)) (op (q ⁻¹ᵁ V))
            (((Scheme.Modules.pullbackPushforwardAdjunction q).unit.app E).val.app (op V) (e j))
            (((Scheme.Modules.pullbackPushforwardAdjunction q).unit.app
              (dualSheaf E)).val.app (op V) (l j)))
    (heps : ∀ (V : X.Opens) (lam : (dualSheaf E).val.obj (op V)) (m : E.val.obj (op V)),
        (eps.val.app (op (q ⁻¹ᵁ V))).hom
            (tensorObjTmul W.toRingedSpace ((Scheme.Modules.pullback q).obj (dualSheaf E))
              ((Scheme.Modules.pullback q).obj E) (op (q ⁻¹ᵁ V))
              (((Scheme.Modules.pullbackPushforwardAdjunction q).unit.app
                (dualSheaf E)).val.app (op V) lam)
              (((Scheme.Modules.pullbackPushforwardAdjunction q).unit.app E).val.app
                (op V) m)) =
          unitSection W.toRingedSpace (op (q ⁻¹ᵁ V))
            ((q.app V).hom (dualEval X.toRingedSpace E lam m)))
    (chi : (Scheme.Modules.pullback q).obj E ⟶ (Scheme.Modules.pullback q).obj E)
    (hchi : chi = (λ_ ((Scheme.Modules.pullback q).obj E)).inv ≫
        s ▷ ((Scheme.Modules.pullback q).obj E) ≫
        (α_ ((Scheme.Modules.pullback q).obj E)
          ((Scheme.Modules.pullback q).obj (dualSheaf E))
          ((Scheme.Modules.pullback q).obj E)).hom ≫
        ((Scheme.Modules.pullback q).obj E) ◁ eps ≫
        (ρ_ ((Scheme.Modules.pullback q).obj E)).hom) :
    chi = 𝟙 ((Scheme.Modules.pullback q).obj E) := by
  classical
  refine hom_ext_of_pullbackUnit_locally q E _ _ _ fun x => ?_
  obtain ⟨V₀, hxV₀, hV₀⟩ := coevaluation_locally_sum X.toRingedSpace E
    (isLocallyFiniteFreeSummand_of_isFiniteLocallyFree X E hE) x
  refine ⟨V₀, hxV₀, fun V k m => ?_⟩
  obtain ⟨n, e, l, hexp⟩ := hV₀ V k
  have hdb : ∑ j, dualEval X.toRingedSpace E (l j) m • e j = m :=
    Eq.trans (Finset.sum_congr rfl fun j _ =>
        congrArg (fun z => dualEval X.toRingedSpace E (l j) m • z)
          (map_id_apply X.toRingedSpace E V (e j)).symm)
      (coevaluation_sum_identity X.toRingedSpace E
        (isLocallyFiniteFreeSummand_of_isFiniteLocallyFree X E hE) V e l hexp
        (op (Over.mk (𝟙 V))) m)
  have hT := trace_apply_of_sum W.toRingedSpace
      ((Scheme.Modules.pullback q).obj E) ((Scheme.Modules.pullback q).obj (dualSheaf E))
      s eps chi hchi (op (q ⁻¹ᵁ V))
      (((Scheme.Modules.pullbackPushforwardAdjunction q).unit.app E).val.app (op V) m)
      (fun j => ((Scheme.Modules.pullbackPushforwardAdjunction q).unit.app E).val.app (op V) (e j))
      (fun j => ((Scheme.Modules.pullbackPushforwardAdjunction q).unit.app
        (dualSheaf E)).val.app (op V) (l j))
      (fun j => (q.app V).hom (dualEval X.toRingedSpace E (l j) m))
      (hs V n e l hexp) (fun j => heps V (l j) m)
  refine Eq.trans ?_ (id_val_app_apply W ((Scheme.Modules.pullback q).obj E) (q ⁻¹ᵁ V)
    (((Scheme.Modules.pullbackPushforwardAdjunction q).unit.app E).val.app (op V) m)).symm
  exact hT.trans ((Finset.sum_congr rfl fun j _ =>
      (Stacks.RingedSpace.pullbackUnit_smul q.toLRSHom.toShHom E (op V) _ (e j)).symm).trans
    ((map_sum _ _ _).symm.trans
      (congrArg (fun z => ((Scheme.Modules.pullbackPushforwardAdjunction q).unit.app E).val.app
        (op V) z) hdb)))

/-- **The dual base-change map is compatible with the coevaluations.**  Let `q : W ⟶ X` be a
morphism of schemes and `ℰ` a finite locally free `𝒪_X`-module.  Then `q^*(ℰ^∨)` is a left dual
of `q^*ℰ` — the canonical pairing of `q^*ℰ` transported along the dual base-change isomorphism
`AlgebraicGeometry.VectorBundleKZero.pullbackDualSheafIso` — and its coevaluation is the
pullback of the coevaluation of `ℰ`, read through the identification `𝒪_W ≅ q^*𝒪_X` of
`Stacks.PullbackAlgebra.pullbackUnitIso` and the comparison
`q^*(ℰ ⊗ ℰ^∨) ≅ q^*ℰ ⊗ q^*(ℰ^∨)` of [Stacks, Tag 01CD].

Both sides are sections of `q^*ℰ ⊗ q^*(ℰ^∨)`, and the right-hand side is checked to be the
coevaluation by `CategoryTheory.coevaluation_eq_of_trace_eq_id`; the check is the sectionwise
computation of `AlgebraicGeometry.pullbackCoevaluation_apply_one` and
`AlgebraicGeometry.pullbackDualPairing_evaluation_tmul` together with the dual-basis
identity. -/
theorem pullbackDualSheafIso_coevaluation_eq_pullback (E : X.Modules)
    (hE : IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) E) :
    @ExactPairing.coevaluation _ _ (onSpaceModulesMonoidal W)
        ((Scheme.Modules.pullback q).obj E)
        ((Scheme.Modules.pullback q).obj (dualSheaf E))
        (@exactPairingCongrRight _ _ (onSpaceModulesMonoidal W)
          ((Scheme.Modules.pullback q).obj E)
          ((Scheme.Modules.pullback q).obj (dualSheaf E))
          (dualSheaf ((Scheme.Modules.pullback q).obj E))
          (dualSheafExactPairing W ((Scheme.Modules.pullback q).obj E)
            (isFiniteLocallyFree_pullback q E hE))
          (pullbackDualSheafIso q E hE)) =
      (Stacks.PullbackAlgebra.pullbackUnitIso q.toLRSHom.toShHom).inv ≫
        (Scheme.Modules.pullback q).map
          (@ExactPairing.coevaluation _ _ (onSpaceModulesMonoidal X) E (dualSheaf E)
            (dualSheafExactPairing X E hE)) ≫
        (Stacks.Chow.pullbackTensorIso q E (dualSheaf E)).hom :=
  (coevaluation_eq_of_trace_eq_id
    (@exactPairingCongrRight _ _ (onSpaceModulesMonoidal W)
      ((Scheme.Modules.pullback q).obj E)
      ((Scheme.Modules.pullback q).obj (dualSheaf E))
      (dualSheaf ((Scheme.Modules.pullback q).obj E))
      (dualSheafExactPairing W ((Scheme.Modules.pullback q).obj E)
        (isFiniteLocallyFree_pullback q E hE))
      (pullbackDualSheafIso q E hE)) _
    (pullbackDualPairing_trace_eq_id q E hE _ _
      (fun V _n e l hexp => pullbackCoevaluation_apply_one q E hE V e l hexp)
      (fun V lam m => pullbackDualPairing_evaluation_tmul q E hE V lam m) _ rfl)).symm

/-! ### The factor section -/

/-- Tensoring a morphism with the identity of a fixed second factor is right whiskering, at the
uncurried spelling `Stacks.SheafOfModules.Tensor.sheafTensor` of the tensor product bifunctor on
a ringed space that `Stacks.RingedSpace.comparisonNatTrans` is natural in. -/
private theorem tensorSheaf_map_id_right {Z : Scheme.{u}} {P P₂ : Z.Modules} (Q : Z.Modules)
    (u : P ⟶ P₂) :
    (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        ⟨Z.toRingedSpace.presheaf, Z.toRingedSpace.IsSheaf⟩)).map
        ((u, 𝟙 Q) : ((P, Q) : _ × _) ⟶ (P₂, Q)) =
      MonoidalCategory.whiskerRight u Q :=
  (Stacks.SheafOfModules.OnSpace.tensorHom_eq_tensorSheafMap Z.toRingedSpace u (𝟙 Q)).symm.trans
    (MonoidalCategory.tensorHom_id u Q)

/-- **The comparison of [Stacks, Tag 01CD] is natural in its first argument**, in the whiskering
spelling: for `a : 𝒜 ⟶ 𝒜₂` the pullback of `a ▷ ℬ` followed by the comparison at `(𝒜₂, ℬ)` is
the comparison at `(𝒜, ℬ)` followed by `q^*a ▷ q^*ℬ`.

This is the naturality of `Stacks.RingedSpace.comparisonNatTrans` at `(a, 𝟙 ℬ)`, with the action
of the tensor product bifunctor rewritten as a whiskering by `tensorSheaf_map_id_right`. -/
theorem pullbackTensorIso_whiskerRight {A A₂ : X.Modules} (B : X.Modules) (a : A ⟶ A₂) :
    (Scheme.Modules.pullback q).map (MonoidalCategory.whiskerRight a B) ≫
        (Stacks.Chow.pullbackTensorIso q A₂ B).hom =
      (Stacks.Chow.pullbackTensorIso q A B).hom ≫
        MonoidalCategory.whiskerRight ((Scheme.Modules.pullback q).map a)
          ((Scheme.Modules.pullback q).obj B) := by
  refine Eq.trans (congrArg (fun z => (Scheme.Modules.pullback q).map z ≫
      (Stacks.Chow.pullbackTensorIso q A₂ B).hom) (tensorSheaf_map_id_right B a).symm) ?_
  refine Eq.trans ((Stacks.RingedSpace.comparisonNatTrans q.toLRSHom.toShHom).naturality
    ((a, 𝟙 B) : ((A, B) : _ × _) ⟶ (A₂, B))) ?_
  refine congrArg (fun z => (Stacks.Chow.pullbackTensorIso q A B).hom ≫ z) ?_
  refine Eq.trans (congrArg (fun z => (Functor.uncurry.obj
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        ⟨W.toRingedSpace.presheaf, W.toRingedSpace.IsSheaf⟩)).map
      ((((Scheme.Modules.pullback q).map a), z) :
        ((((Scheme.Modules.pullback q).obj A), ((Scheme.Modules.pullback q).obj B)) : _ × _) ⟶
          (((Scheme.Modules.pullback q).obj A₂), ((Scheme.Modules.pullback q).obj B))))
    ((Scheme.Modules.pullback q).map_id B)) ?_
  exact tensorSheaf_map_id_right ((Scheme.Modules.pullback q).obj B)
    ((Scheme.Modules.pullback q).map a)

/-- **The duality section of `q^*a` is the pullback of the duality section of `a`.**  For
`a : ℰ ⟶ ℰ₂` between modules on `X` with `ℰ` finite locally free, the coevaluation of
`q^*(ℰ^∨)` as a left dual of `q^*ℰ` followed by `q^*a` is the pullback of the value
`AlgebraicGeometry.dualTensorHomEquiv` takes at `a`, read through the same two canonical
comparisons as in `AlgebraicGeometry.pullbackDualSheafIso_coevaluation_eq_pullback`.

This is that theorem, the formula
`AlgebraicGeometry.dualTensorHomEquiv_eq_coevaluation_comp` for the duality section, and
`AlgebraicGeometry.pullbackTensorIso_whiskerRight` to move `a` past the comparison. -/
theorem pullbackDualSheafIso_dualSection_eq_pullback (E E₂ : X.Modules)
    (hE : IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) E) (a : E ⟶ E₂) :
    @ExactPairing.coevaluation _ _ (onSpaceModulesMonoidal W)
          ((Scheme.Modules.pullback q).obj E)
          ((Scheme.Modules.pullback q).obj (dualSheaf E))
          (@exactPairingCongrRight _ _ (onSpaceModulesMonoidal W)
            ((Scheme.Modules.pullback q).obj E)
            ((Scheme.Modules.pullback q).obj (dualSheaf E))
            (dualSheaf ((Scheme.Modules.pullback q).obj E))
            (dualSheafExactPairing W ((Scheme.Modules.pullback q).obj E)
              (isFiniteLocallyFree_pullback q E hE))
            (pullbackDualSheafIso q E hE)) ≫
        MonoidalCategory.whiskerRight ((Scheme.Modules.pullback q).map a)
          ((Scheme.Modules.pullback q).obj (dualSheaf E)) =
      (Stacks.PullbackAlgebra.pullbackUnitIso q.toLRSHom.toShHom).inv ≫
        (Scheme.Modules.pullback q).map (dualTensorHomEquiv X E E₂ hE a) ≫
        (Stacks.Chow.pullbackTensorIso q E₂ (dualSheaf E)).hom :=
  (congrArg (fun z => z ≫ MonoidalCategory.whiskerRight
      ((Scheme.Modules.pullback q).map a)
      ((Scheme.Modules.pullback q).obj (dualSheaf E)))
    (pullbackDualSheafIso_coevaluation_eq_pullback q E hE)).trans
    (assoc_comp_eq_of_factor _ _ _ _ _ _ _
      ((congrArg ((Scheme.Modules.pullback q).map)
          (dualTensorHomEquiv_eq_coevaluation_comp X E E₂ hE a)).trans
        (Functor.map_comp _ _ _))
      (pullbackTensorIso_whiskerRight q (dualSheaf E) a))

/-! ### The two factor pairings of the external tensor product -/

variable {Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)

/-- **The coevaluation of `AlgebraicGeometry.externalTensorProductFirstPairing` is the pullback
along `pr₁` of the coevaluation of `ℰ`.**  This is
`AlgebraicGeometry.pullbackDualSheafIso_coevaluation_eq_pullback` at `q = pr₁`, the first factor
pairing being by definition the canonical pairing of `pr₁^*ℰ` transported along the dual
base-change isomorphism. -/
theorem externalTensorProductFirstPairing_coevaluation_eq_pullback (E : X.Modules)
    (hE : IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) E) :
    @ExactPairing.coevaluation _ _ (onSpaceModulesMonoidal (Limits.pullback f g))
        ((Scheme.Modules.pullback (Limits.pullback.fst f g)).obj E)
        ((Scheme.Modules.pullback (Limits.pullback.fst f g)).obj (dualSheaf E))
        (externalTensorProductFirstPairing f g E hE) =
      (Stacks.PullbackAlgebra.pullbackUnitIso
          (Limits.pullback.fst f g).toLRSHom.toShHom).inv ≫
        (Scheme.Modules.pullback (Limits.pullback.fst f g)).map
          (@ExactPairing.coevaluation _ _ (onSpaceModulesMonoidal X) E (dualSheaf E)
            (dualSheafExactPairing X E hE)) ≫
        (Stacks.Chow.pullbackTensorIso (Limits.pullback.fst f g) E (dualSheaf E)).hom :=
  pullbackDualSheafIso_coevaluation_eq_pullback (Limits.pullback.fst f g) E hE

/-- **The first factor section of the duality bijection is a pullback.**  For `a : ℰ ⟶ ℰ₂` the
section of `AlgebraicGeometry.externalTensorProductFirstPairing` composed with `pr₁^*a` — the
first of the two factor sections of
`AlgebraicGeometry.externalTensorDualTensorHomEquiv_externalTensorProductMap_swapped` — is the
pullback along `pr₁` of the `X`-level duality section of `a`. -/
theorem externalTensorProductFirstPairing_dualSection_eq_pullback (E E₂ : X.Modules)
    (hE : IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) E) (a : E ⟶ E₂) :
    @ExactPairing.coevaluation _ _ (onSpaceModulesMonoidal (Limits.pullback f g))
          ((Scheme.Modules.pullback (Limits.pullback.fst f g)).obj E)
          ((Scheme.Modules.pullback (Limits.pullback.fst f g)).obj (dualSheaf E))
          (externalTensorProductFirstPairing f g E hE) ≫
        MonoidalCategory.whiskerRight
          ((Scheme.Modules.pullback (Limits.pullback.fst f g)).map a)
          ((Scheme.Modules.pullback (Limits.pullback.fst f g)).obj (dualSheaf E)) =
      (Stacks.PullbackAlgebra.pullbackUnitIso
          (Limits.pullback.fst f g).toLRSHom.toShHom).inv ≫
        (Scheme.Modules.pullback (Limits.pullback.fst f g)).map
          (dualTensorHomEquiv X E E₂ hE a) ≫
        (Stacks.Chow.pullbackTensorIso (Limits.pullback.fst f g) E₂ (dualSheaf E)).hom :=
  pullbackDualSheafIso_dualSection_eq_pullback (Limits.pullback.fst f g) E E₂ hE a

/-- **The coevaluation of `AlgebraicGeometry.externalTensorProductSecondPairing` is the pullback
along `pr₂` of the coevaluation of `𝒢`**, the mirror image of
`AlgebraicGeometry.externalTensorProductFirstPairing_coevaluation_eq_pullback`. -/
theorem externalTensorProductSecondPairing_coevaluation_eq_pullback (G : Y.Modules)
    (hG : IsFiniteLocallyFree.{u, u, u} (R := Y.ringCatSheaf) G) :
    @ExactPairing.coevaluation _ _ (onSpaceModulesMonoidal (Limits.pullback f g))
        ((Scheme.Modules.pullback (Limits.pullback.snd f g)).obj G)
        ((Scheme.Modules.pullback (Limits.pullback.snd f g)).obj (dualSheaf G))
        (externalTensorProductSecondPairing f g G hG) =
      (Stacks.PullbackAlgebra.pullbackUnitIso
          (Limits.pullback.snd f g).toLRSHom.toShHom).inv ≫
        (Scheme.Modules.pullback (Limits.pullback.snd f g)).map
          (@ExactPairing.coevaluation _ _ (onSpaceModulesMonoidal Y) G (dualSheaf G)
            (dualSheafExactPairing Y G hG)) ≫
        (Stacks.Chow.pullbackTensorIso (Limits.pullback.snd f g) G (dualSheaf G)).hom :=
  pullbackDualSheafIso_coevaluation_eq_pullback (Limits.pullback.snd f g) G hG

/-- **The second factor section of the duality bijection is a pullback**, the mirror image of
`AlgebraicGeometry.externalTensorProductFirstPairing_dualSection_eq_pullback`. -/
theorem externalTensorProductSecondPairing_dualSection_eq_pullback (G G₂ : Y.Modules)
    (hG : IsFiniteLocallyFree.{u, u, u} (R := Y.ringCatSheaf) G) (b : G ⟶ G₂) :
    @ExactPairing.coevaluation _ _ (onSpaceModulesMonoidal (Limits.pullback f g))
          ((Scheme.Modules.pullback (Limits.pullback.snd f g)).obj G)
          ((Scheme.Modules.pullback (Limits.pullback.snd f g)).obj (dualSheaf G))
          (externalTensorProductSecondPairing f g G hG) ≫
        MonoidalCategory.whiskerRight
          ((Scheme.Modules.pullback (Limits.pullback.snd f g)).map b)
          ((Scheme.Modules.pullback (Limits.pullback.snd f g)).obj (dualSheaf G)) =
      (Stacks.PullbackAlgebra.pullbackUnitIso
          (Limits.pullback.snd f g).toLRSHom.toShHom).inv ≫
        (Scheme.Modules.pullback (Limits.pullback.snd f g)).map
          (dualTensorHomEquiv Y G G₂ hG b) ≫
        (Stacks.Chow.pullbackTensorIso (Limits.pullback.snd f g) G₂ (dualSheaf G)).hom :=
  pullbackDualSheafIso_dualSection_eq_pullback (Limits.pullback.snd f g) G G₂ hG b

/-- **The value of the duality bijection at a pure map `a ⊠ b`, with both factor sections
written as pullbacks.**  This is
`AlgebraicGeometry.externalTensorDualTensorHomEquiv_externalTensorProductMap` with its two
factor sections replaced, by the two theorems above, by the pullbacks along `pr₁` and `pr₂` of
the `X`-level duality section of `a` and the `Y`-level duality section of `b`: the value at
`a ⊠ b` depends on `a` and on `b` only through two sections on `X` and on `Y`. -/
theorem externalTensorDualTensorHomEquiv_externalTensorProductMap_pullback
    (E E₂ : X.Modules) (G G₂ : Y.Modules)
    (hE : IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) E)
    (hG : IsFiniteLocallyFree.{u, u, u} (R := Y.ringCatSheaf) G)
    (a : E ⟶ E₂) (b : G ⟶ G₂) :
    externalTensorDualTensorHomEquiv f g E G (externalTensorProduct f g E₂ G₂) hE hG
        (externalTensorProductMap f g a b) =
      @nestedTensorSection _ _ (onSpaceModulesMonoidal (Limits.pullback f g)) _ _ _ _
          ((Stacks.PullbackAlgebra.pullbackUnitIso
              (Limits.pullback.fst f g).toLRSHom.toShHom).inv ≫
            (Scheme.Modules.pullback (Limits.pullback.fst f g)).map
              (dualTensorHomEquiv X E E₂ hE a) ≫
            (Stacks.Chow.pullbackTensorIso (Limits.pullback.fst f g) E₂ (dualSheaf E)).hom)
          ((Stacks.PullbackAlgebra.pullbackUnitIso
              (Limits.pullback.snd f g).toLRSHom.toShHom).inv ≫
            (Scheme.Modules.pullback (Limits.pullback.snd f g)).map
              (dualTensorHomEquiv Y G G₂ hG b) ≫
            (Stacks.Chow.pullbackTensorIso (Limits.pullback.snd f g) G₂ (dualSheaf G)).hom) ≫
        MonoidalCategory.whiskerLeft (externalTensorProduct f g E₂ G₂)
          (Stacks.SheafOfModules.tensorSheafBraiding
            (Limits.pullback f g).toRingedSpace.presheaf
            (structureSheafRing (Limits.pullback f g).toRingedSpace).property
            ((Scheme.Modules.pullback (Limits.pullback.fst f g)).obj (dualSheaf E))
            ((Scheme.Modules.pullback (Limits.pullback.snd f g)).obj (dualSheaf G))).inv :=
  (externalTensorDualTensorHomEquiv_externalTensorProductMap f g E E₂ G G₂ hE hG a b).trans
    (congrArg (fun z => z ≫ MonoidalCategory.whiskerLeft (externalTensorProduct f g E₂ G₂)
        (Stacks.SheafOfModules.tensorSheafBraiding
          (Limits.pullback f g).toRingedSpace.presheaf
          (structureSheafRing (Limits.pullback f g).toRingedSpace).property
          ((Scheme.Modules.pullback (Limits.pullback.fst f g)).obj (dualSheaf E))
          ((Scheme.Modules.pullback (Limits.pullback.snd f g)).obj (dualSheaf G))).inv)
      (congrArg₂ (fun s t => @nestedTensorSection _ _ (onSpaceModulesMonoidal (Limits.pullback f g))
          _ _ _ _ s t)
        (externalTensorProductFirstPairing_dualSection_eq_pullback f g E E₂ hE a)
        (externalTensorProductSecondPairing_dualSection_eq_pullback f g G G₂ hG b)))

end AlgebraicGeometry

end
