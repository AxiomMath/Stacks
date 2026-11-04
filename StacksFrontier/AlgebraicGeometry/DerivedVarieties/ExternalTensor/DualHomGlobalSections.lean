module

public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.ExternalTensor.DualHomAdditive
public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.ExternalTensor.DualHomInterchange
public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.ExternalTensor.DualHomPullback
public import StacksFrontier.AlgebraicGeometry.Descent.PullbackSectionsSheaf.UnitComparison
public import StacksFrontier.AlgebraicGeometry.FibreProductAffineChart.BoxSectionsGlobalBijective
public import StacksFrontier.AlgebraicGeometry.Modules.OnSpaceMonoidalScheme
public import StacksFrontier.AlgebraicGeometry.Morphisms.Differentials.BoxProductRightSections

/-!
# The duality bijection on global sections, and the box product of two duality sections

`AlgebraicGeometry.externalTensorDualTensorHomEquiv` identifies
`Hom(ℰ ⊠ 𝒢, ℰ' ⊠ 𝒢')` with the morphisms out of the structure sheaf of `X ×_S Y` into
`(ℰ' ⊠ 𝒢') ⊗ (ℰ^∨ ⊠ 𝒢^∨)`, and
`AlgebraicGeometry.externalTensorProductTensorIso` of [Stacks, Tag 0G46] turns the target into
`(ℰ' ⊗ ℰ^∨) ⊠ (𝒢' ⊗ 𝒢^∨)`. What this file adds is the *value on global sections*: a morphism out
of the structure sheaf is a global section, and the value of the composite bijection at a pure
map `a ⊠ b` is the external tensor section of the two one-factor duality sections.

That is the comparison the implementation notes of
`StacksDraft.AlgebraicGeometry.DerivedVarieties.TransformedDiagonal.SituationPairings` record as
missing: "the comparison of `Hom(𝟙, M)` with `Γ(M, ⊤)` under which the monoidal product of two
morphisms out of the unit object is `Stacks.Tag01VSPullbackTensor.externalTensorSection`". Half of
it was there already — `AlgebraicGeometry.Scheme.Modules.unitHomEquivTop` is the comparison, and
`AlgebraicGeometry.unitHomLinearEquiv` below only adds its `k`-linearity — and the other half,
the behaviour of the monoidal product of two unit sections, is
`AlgebraicGeometry.app_leftUnitorInv_tensorHom_one` and
`AlgebraicGeometry.app_box_of_unitHom` below.

## Main definitions

* `AlgebraicGeometry.unitHomLinearEquiv`: morphisms from the structure sheaf of a scheme over a
  field `k` are the global sections, as `k`-vector spaces.
* `AlgebraicGeometry.dualTensorHomLinearEquiv`: `Hom(P, ℱ) ≃ₗ[k] Γ(X, ℱ ⊗ P^∨)`.
* `AlgebraicGeometry.externalTensorDualLinearEquiv`:
  `Hom(ℰ ⊠ 𝒢, ℰ' ⊠ 𝒢') ≃ₗ[k] Γ(X ×_k Y, (ℰ' ⊗ ℰ^∨) ⊠ (𝒢' ⊗ 𝒢^∨))`.

## Main results

* `AlgebraicGeometry.app_leftUnitorInv_one`: the inverse left unitor of the unit object carries
  the unit section to the pure tensor `1 ⊗ 1`.
* `AlgebraicGeometry.app_leftUnitorInv_tensorHom_one` and
  `AlgebraicGeometry.app_leftUnitorInv_tensorHom_comp_one`: **the monoidal product of two
  morphisms out of the unit object is, on global sections, the pure tensor of their two global
  sections.**
* `AlgebraicGeometry.app_pullback_of_unitHom`: the global section of `h^*P` attached to the
  pullback of a morphism out of the structure sheaf is the pullback of its global section.
* `AlgebraicGeometry.app_box_of_unitHom`: **the global section of `P ⊠ Q` attached to the
  monoidal product of two pulled-back unit morphisms is
  `Stacks.Tag01VSPullbackTensor.externalTensorSection` of the two global sections.**
* `AlgebraicGeometry.app_externalTensorDualTensorHomEquiv_externalTensorProductMap`: **the value
  of the duality bijection at a pure map `a ⊠ b`, on global sections, is the pure tensor of the
  two one-factor duality sections.**
* `AlgebraicGeometry.externalTensorDualLinearEquiv_externalTensorProductMap`: the same statement
  with both sides read through the `k`-linear bijections, which is the form a statement about the
  `k`-bilinearity relations consumes.

## Implementation notes

*Why the section formulas are written with `AlgebraicGeometry.Scheme.Modules.Hom.app` and proved
by `Eq.trans`.* The library states its monoidal-section formulas at
`Stacks.SheafOfModules.OnSpace.monoidal` over a ringed space and the duality statements at
`AlgebraicGeometry.onSpaceModulesMonoidal` over a scheme. The two structures are the same by
`rfl` but not the same *term*, and `rw` synthesizes a lemma's instance arguments rather than
reading them off the goal, so a ringed-space formula does not fire on a scheme-level goal even
when every rewrite applies. Term-mode `Eq.trans`/`congrArg` chains check the two spellings up to
definitional equality instead, which is why the proofs below are written that way and why
`AlgebraicGeometry.tensorHom_app_tmul` restates
`Stacks.SheafOfModules.OnSpace.tensorHom_tmul` at the scheme spellings once.

*The two spellings of [Stacks, Tag 01CD].* `Stacks.Chow.pullbackTensorIso` and
`Stacks.AlgebraicGeometry.ModuleLimits.pullbackTensorIso` are the same isomorphism; the first is
what `AlgebraicGeometry.externalTensorProductFirstPairing_dualSection_eq_pullback` produces and
the second is what `AlgebraicGeometry.externalTensorProductTensorIso` is built from, so the proof
of `app_externalTensorDualTensorHomEquiv_externalTensorProductMap` normalises the first into the
second before the two cancel.

## References

* [Stacks Project, Tag 0FNV](https://stacks.math.columbia.edu/tag/0FNV)
* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
* [Stacks Project, Tag 0G45](https://stacks.math.columbia.edu/tag/0G45)
* [Stacks Project, Tag 0G46](https://stacks.math.columbia.edu/tag/0G46)
* [Stacks Project, Tag 0G0A](https://stacks.math.columbia.edu/tag/0G0A)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open Stacks.FiniteLocallyFree
open Stacks.SheafOfModules.OnSpace
open Stacks.SheafOfModules.TensorStalkRingedSpace
open Stacks.Tag01VSPullbackTensor

universe u

namespace AlgebraicGeometry

open Stacks.AlgebraicGeometry.ReflexiveModules AlgebraicGeometry.VectorBundleKZero

attribute [local instance] onSpaceModulesMonoidal

/-! ### Scheme-level section formulas for the sheafified tensor product -/

/-- **The monoidal product of two morphisms, on a local pure tensor**, at the scheme spellings of
the category and of the monoidal structure. This is
`Stacks.SheafOfModules.OnSpace.tensorHom_tmul` at `AlgebraicGeometry.onSpaceModulesMonoidal`; the
two monoidal structures are equal by `rfl` but not as terms, so the restatement is what lets the
formula be used in a chain of scheme-level equalities. -/
theorem tensorHom_app_tmul {W : Scheme.{u}} {A A' B B' : W.Modules} (φ : A ⟶ A') (ψ : B ⟶ B')
    (U : W.Opens) (x : Γ(A, U)) (y : Γ(B, U)) :
    Scheme.Modules.Hom.app (MonoidalCategory.tensorHom φ ψ) U
        (tensorObjTmul W.toRingedSpace A B (op U) x y)
      = tensorObjTmul W.toRingedSpace A' B' (op U)
        (Scheme.Modules.Hom.app φ U x) (Scheme.Modules.Hom.app ψ U y) :=
  tensorHom_tmul W.toRingedSpace φ ψ (op U) x y

/-- **The isomorphism of tensor product sheaves induced by a pair of isomorphisms is their
monoidal product.** -/
theorem tensorSheafMapIso_hom_eq_tensorHom {W : Scheme.{u}} {A A' B B' : W.Modules}
    (e : A ≅ A') (e' : B ≅ B') :
    (tensorSheafMapIso W.toRingedSpace e e').hom = MonoidalCategory.tensorHom e.hom e'.hom :=
  (tensorHom_eq_tensorSheafMap W.toRingedSpace e.hom e'.hom).symm

/-! ### Global sections of a morphism out of the structure sheaf -/

/-- **The inverse left unitor of the unit object carries the unit section to `1 ⊗ 1`.** The left
unitor sends the local pure tensor `r ⊗ s` to `r • s`, so at `r = s = 1` it sends `1 ⊗ 1` to `1`;
the statement is that read through the inverse. -/
theorem app_leftUnitorInv_one (W : Scheme.{u}) :
    Scheme.Modules.Hom.app (λ_ (𝟙_ W.Modules)).inv ⊤ (1 : Γ(W, ⊤))
      = tensorObjTmul W.toRingedSpace (𝟙_ W.Modules) (𝟙_ W.Modules) (op ⊤)
          (1 : Γ(W, ⊤)) (1 : Γ(W, ⊤)) := by
  have h2 : Scheme.Modules.Hom.app (λ_ (𝟙_ W.Modules)).hom ⊤
      (tensorObjTmul W.toRingedSpace (𝟙_ W.Modules) (𝟙_ W.Modules) (op ⊤)
        (1 : Γ(W, ⊤)) (1 : Γ(W, ⊤))) = (1 : Γ(W, ⊤)) :=
    (leftUnitor_tmul W.toRingedSpace (𝟙_ W.Modules) (op ⊤) (1 : Γ(W, ⊤))
      (1 : Γ(W, ⊤))).trans (one_smul (W.presheaf.obj (op ⊤)) _)
  refine Eq.trans (congrArg (Scheme.Modules.Hom.app (λ_ (𝟙_ W.Modules)).inv ⊤) h2.symm) ?_
  exact modulesHomApp_inv_hom (λ_ (𝟙_ W.Modules)) ⊤ _

/-- **The global section of a sum of two morphisms out of the structure sheaf is the sum of their
global sections.** -/
theorem app_one_add {W : Scheme.{u}} {M : W.Modules} (α β : 𝟙_ W.Modules ⟶ M) :
    Scheme.Modules.Hom.app (α + β) ⊤ (1 : Γ(W, ⊤))
      = Scheme.Modules.Hom.app α ⊤ (1 : Γ(W, ⊤))
        + Scheme.Modules.Hom.app β ⊤ (1 : Γ(W, ⊤)) := rfl

/-- **The global section of the negative of a morphism out of the structure sheaf is the
negative of its global section.** -/
theorem app_one_neg {W : Scheme.{u}} {M : W.Modules} (α : 𝟙_ W.Modules ⟶ M) :
    Scheme.Modules.Hom.app (-α) ⊤ (1 : Γ(W, ⊤))
      = -Scheme.Modules.Hom.app α ⊤ (1 : Γ(W, ⊤)) := rfl

/-- **The zero morphism out of the structure sheaf has the zero global section.** -/
theorem app_one_zero {W : Scheme.{u}} {M : W.Modules} :
    Scheme.Modules.Hom.app (0 : 𝟙_ W.Modules ⟶ M) ⊤ (1 : Γ(W, ⊤)) = 0 := rfl

/-- **A morphism out of the structure sheaf is determined by its global section.** This is the
injectivity of `AlgebraicGeometry.Scheme.Modules.unitHomEquivTop` read backwards. -/
theorem injective_app_one (W : Scheme.{u}) (M : W.Modules) :
    Function.Injective (fun φ : 𝟙_ W.Modules ⟶ M =>
      Scheme.Modules.Hom.app φ ⊤ (1 : Γ(W, ⊤))) :=
  (Scheme.Modules.unitHomEquivTop M).symm.injective

/-- **The monoidal product of two morphisms out of the structure sheaf is, on global sections,
the pure tensor of their global sections.** -/
theorem app_leftUnitorInv_tensorHom_one {W : Scheme.{u}} {A B : W.Modules}
    (ca : 𝟙_ W.Modules ⟶ A) (cb : 𝟙_ W.Modules ⟶ B) :
    Scheme.Modules.Hom.app ((λ_ (𝟙_ W.Modules)).inv ≫ MonoidalCategory.tensorHom ca cb) ⊤
        (1 : Γ(W, ⊤))
      = tensorObjTmul W.toRingedSpace A B (op ⊤)
        (Scheme.Modules.Hom.app ca ⊤ (1 : Γ(W, ⊤)))
        (Scheme.Modules.Hom.app cb ⊤ (1 : Γ(W, ⊤))) := by
  exact (congrArg (Scheme.Modules.Hom.app (MonoidalCategory.tensorHom ca cb) ⊤)
    (app_leftUnitorInv_one W)).trans (tensorHom_app_tmul ca cb ⊤ (1 : Γ(W, ⊤)) (1 : Γ(W, ⊤)))

/-- `AlgebraicGeometry.app_leftUnitorInv_tensorHom_one` followed by a further morphism. -/
theorem app_leftUnitorInv_tensorHom_comp_one {W : Scheme.{u}} {A B N : W.Modules}
    (ca : 𝟙_ W.Modules ⟶ A) (cb : 𝟙_ W.Modules ⟶ B) (T : A ⊗ B ⟶ N) :
    Scheme.Modules.Hom.app ((λ_ (𝟙_ W.Modules)).inv ≫
        (MonoidalCategory.tensorHom ca cb ≫ T)) ⊤ (1 : Γ(W, ⊤))
      = Scheme.Modules.Hom.app T ⊤
        (tensorObjTmul W.toRingedSpace A B (op ⊤)
          (Scheme.Modules.Hom.app ca ⊤ (1 : Γ(W, ⊤)))
          (Scheme.Modules.Hom.app cb ⊤ (1 : Γ(W, ⊤)))) := by
  exact congrArg (Scheme.Modules.Hom.app T ⊤) (app_leftUnitorInv_tensorHom_one ca cb)

/-- **The global section attached to the pullback of a morphism out of the structure sheaf is the
pullback of its global section.** This is
`AlgebraicGeometry.Scheme.Modules.pullbackUnitIso_sections_naturality` at the identity, the
transpose of which is the unit of the pullback--pushforward adjunction, that is
`Stacks.Tag01VSPullbackTensor.modulesPullbackUnit`. -/
theorem app_pullback_of_unitHom {A B : Scheme.{u}} (h : A ⟶ B) (P : B.Modules)
    (δ : 𝟙_ B.Modules ⟶ P) :
    Scheme.Modules.Hom.app (M := 𝟙_ A.Modules)
        ((Scheme.Modules.pullbackUnitIso h).inv ≫
          (Scheme.Modules.pullback h).map δ) ⊤ (1 : Γ(A, ⊤))
      = ((Scheme.Modules.pullback h).obj P).presheaf.map
          (homOfLE (show (⊤ : A.Opens) ≤ h ⁻¹ᵁ ⊤ by simp)).op
          (modulesPullbackUnit h P ⊤ (Scheme.Modules.Hom.app δ ⊤ (1 : Γ(B, ⊤)))) := by
  have key := Scheme.Modules.pullbackUnitIso_sections_naturality h P
    ((Scheme.Modules.pullback h).obj P) (𝟙 _)
    (Scheme.Modules.Hom.app δ ⊤ (1 : Γ(B, ⊤)))
  rw [Category.comp_id, show Scheme.Modules.unitHomEquivTop P
      (Scheme.Modules.Hom.app δ ⊤ (1 : Γ(B, ⊤))) = δ from
    (Scheme.Modules.unitHomEquivTop P).apply_symm_apply δ] at key
  have hunit : (Scheme.Modules.pullbackPushforwardAdjunction h).homEquiv P
      ((Scheme.Modules.pullback h).obj P) (𝟙 _)
      = (Scheme.Modules.pullbackPushforwardAdjunction h).unit.app P := by
    rw [Adjunction.homEquiv_unit,
      CategoryTheory.Functor.map_id (Scheme.Modules.pushforward h)]
    exact Category.comp_id _
  rw [hunit] at key
  have key2 : Scheme.Modules.unitHomEquivTop ((Scheme.Modules.pullback h).obj P)
      (((Scheme.Modules.pullback h).obj P).presheaf.map
        (eqToHom (show (⊤ : A.Opens) = h ⁻¹ᵁ ⊤ by simp)).op
        (Scheme.Modules.Hom.app
          ((Scheme.Modules.pullbackPushforwardAdjunction h).unit.app P) ⊤
          (Scheme.Modules.Hom.app δ ⊤ (1 : Γ(B, ⊤)))))
      = (Scheme.Modules.pullbackUnitIso h).inv ≫ (Scheme.Modules.pullback h).map δ := by
    rw [← key, Iso.inv_hom_id_assoc]
  refine Eq.trans (congrArg
    (fun φ : 𝟙_ A.Modules ⟶ (Scheme.Modules.pullback h).obj P =>
      Scheme.Modules.Hom.app φ ⊤ (1 : Γ(A, ⊤))) key2.symm) ?_
  refine Eq.trans ((Scheme.Modules.unitHomEquivTop
    ((Scheme.Modules.pullback h).obj P)).symm_apply_apply _) ?_
  exact congrArg (fun z => ((Scheme.Modules.pullback h).obj P).presheaf.map z
    (modulesPullbackUnit h P ⊤ (Scheme.Modules.Hom.app δ ⊤ (1 : Γ(B, ⊤)))))
    (Subsingleton.elim _ _)

/-- **The global section of `P ⊠ Q` attached to the monoidal product of the two pulled-back
morphisms out of the structure sheaves is the external tensor section of the two global
sections.** -/
theorem app_box_of_unitHom {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    (P : X.Modules) (Q : Y.Modules)
    (σ : 𝟙_ X.Modules ⟶ P) (τ : 𝟙_ Y.Modules ⟶ Q) :
    Scheme.Modules.Hom.app ((λ_ (𝟙_ (Limits.pullback f g).Modules)).inv ≫
          MonoidalCategory.tensorHom
            ((Scheme.Modules.pullbackUnitIso (Limits.pullback.fst f g)).inv ≫
              (Scheme.Modules.pullback (Limits.pullback.fst f g)).map σ)
            ((Scheme.Modules.pullbackUnitIso (Limits.pullback.snd f g)).inv ≫
              (Scheme.Modules.pullback (Limits.pullback.snd f g)).map τ)) ⊤
        (1 : Γ(Limits.pullback f g, ⊤))
      = externalTensorSection f g P Q
          (Scheme.Modules.Hom.app σ ⊤ (1 : Γ(X, ⊤)))
          (Scheme.Modules.Hom.app τ ⊤ (1 : Γ(Y, ⊤))) ⊤
          (Scheme.Hom.preimage_top (Limits.pullback.fst f g)).ge
          (Scheme.Hom.preimage_top (Limits.pullback.snd f g)).ge := by
  refine Eq.trans (app_leftUnitorInv_tensorHom_one _ _) ?_
  refine Eq.trans (congrArg₂ (tensorObjTmul (Limits.pullback f g).toRingedSpace _ _ (op ⊤))
    (app_pullback_of_unitHom (Limits.pullback.fst f g) P σ)
    (app_pullback_of_unitHom (Limits.pullback.snd f g) Q τ)) ?_
  rfl

/-! ### The value of the duality bijection at a pure map, on global sections -/

section DualPure

variable {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)

/-- **The value of the duality bijection at a pure map `a ⊠ b`, on global sections.** Read
through the interchange of [Stacks, Tag 0G46], the global section of
`(ℰ' ⊗ ℰ^∨) ⊠ (𝒢' ⊗ 𝒢^∨)` attached to `a ⊠ b` is the pure tensor of the pullbacks of the two
one-factor duality sections of `a` and of `b`. -/
theorem app_externalTensorDualTensorHomEquiv_externalTensorProductMap
    (E E₂ : X.Modules) (G G₂ : Y.Modules)
    (hE : IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) E)
    (hG : IsFiniteLocallyFree.{u, u, u} (R := Y.ringCatSheaf) G)
    (a : E ⟶ E₂) (b : G ⟶ G₂) :
    Scheme.Modules.Hom.app
        (externalTensorDualTensorHomEquiv f g E G (externalTensorProduct f g E₂ G₂) hE hG
            (externalTensorProductMap f g a b) ≫
          (externalTensorProductTensorIso f g E₂ (dualSheaf E) G₂ (dualSheaf G)).hom) ⊤
        (1 : Γ(Limits.pullback f g, ⊤))
      = Scheme.Modules.Hom.app ((λ_ (𝟙_ (Limits.pullback f g).Modules)).inv ≫
          MonoidalCategory.tensorHom
            ((Scheme.Modules.pullbackUnitIso (Limits.pullback.fst f g)).inv ≫
              (Scheme.Modules.pullback (Limits.pullback.fst f g)).map
                (dualTensorHomEquiv X E E₂ hE a))
            ((Scheme.Modules.pullbackUnitIso (Limits.pullback.snd f g)).inv ≫
              (Scheme.Modules.pullback (Limits.pullback.snd f g)).map
                (dualTensorHomEquiv Y G G₂ hG b))) ⊤
        (1 : Γ(Limits.pullback f g, ⊤)) := by
  have hT : (tensorSheafMapIso (Limits.pullback f g).toRingedSpace
        (Stacks.AlgebraicGeometry.ModuleLimits.pullbackTensorIso
          (Limits.pullback.fst f g) E₂ (dualSheaf E)).symm
        (Stacks.AlgebraicGeometry.ModuleLimits.pullbackTensorIso
          (Limits.pullback.snd f g) G₂ (dualSheaf G)).symm).hom
      = MonoidalCategory.tensorHom
        (Stacks.AlgebraicGeometry.ModuleLimits.pullbackTensorIso
          (Limits.pullback.fst f g) E₂ (dualSheaf E)).inv
        (Stacks.AlgebraicGeometry.ModuleLimits.pullbackTensorIso
          (Limits.pullback.snd f g) G₂ (dualSheaf G)).inv :=
    tensorSheafMapIso_hom_eq_tensorHom _ _
  have h0 := externalTensorDualTensorHomEquiv_externalTensorProductMap_tensorIso
    f g E E₂ G G₂ hE hG a b
  have hc₁ : Stacks.Chow.pullbackTensorIso (Limits.pullback.fst f g) E₂ (dualSheaf E)
      = Stacks.AlgebraicGeometry.ModuleLimits.pullbackTensorIso
        (Limits.pullback.fst f g) E₂ (dualSheaf E) := rfl
  have hc₂ : Stacks.Chow.pullbackTensorIso (Limits.pullback.snd f g) G₂ (dualSheaf G)
      = Stacks.AlgebraicGeometry.ModuleLimits.pullbackTensorIso
        (Limits.pullback.snd f g) G₂ (dualSheaf G) := rfl
  rw [externalTensorProductFirstPairing_dualSection_eq_pullback f g E E₂ hE a,
    externalTensorProductSecondPairing_dualSection_eq_pullback f g G G₂ hG b,
    hc₁, hc₂] at h0
  refine Eq.trans (congrArg
    (fun φ : 𝟙_ (Limits.pullback f g).Modules ⟶
        externalTensorProduct f g (E₂ ⊗ dualSheaf E) (G₂ ⊗ dualSheaf G) =>
      Scheme.Modules.Hom.app φ ⊤ (1 : Γ(Limits.pullback f g, ⊤))) h0) ?_
  refine Eq.trans (app_leftUnitorInv_tensorHom_comp_one _ _ _) ?_
  rw [hT]
  refine Eq.trans (tensorHom_app_tmul _ _ ⊤ _ _) ?_
  refine Eq.trans ?_ (app_leftUnitorInv_tensorHom_one _ _).symm
  exact congrArg₂ (tensorObjTmul (Limits.pullback f g).toRingedSpace _ _ (op ⊤))
    (modulesHomApp_inv_hom (Stacks.AlgebraicGeometry.ModuleLimits.pullbackTensorIso
        (Limits.pullback.fst f g) E₂ (dualSheaf E)) ⊤
      (Scheme.Modules.Hom.app
        ((Scheme.Modules.pullbackUnitIso (Limits.pullback.fst f g)).inv ≫
          (Scheme.Modules.pullback (Limits.pullback.fst f g)).map
            (dualTensorHomEquiv X E E₂ hE a)) ⊤ (1 : Γ(Limits.pullback f g, ⊤))))
    (modulesHomApp_inv_hom (Stacks.AlgebraicGeometry.ModuleLimits.pullbackTensorIso
        (Limits.pullback.snd f g) G₂ (dualSheaf G)) ⊤
      (Scheme.Modules.Hom.app
        ((Scheme.Modules.pullbackUnitIso (Limits.pullback.snd f g)).inv ≫
          (Scheme.Modules.pullback (Limits.pullback.snd f g)).map
            (dualTensorHomEquiv Y G G₂ hG b)) ⊤ (1 : Γ(Limits.pullback f g, ⊤))))

end DualPure

end AlgebraicGeometry

end
