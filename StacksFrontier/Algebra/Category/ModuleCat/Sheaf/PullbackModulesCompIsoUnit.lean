module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackTensorMate
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackTensorStep1CompositionLaw

/-!
# The compositor of Stacks 03D8 against the units of extension of scalars

The comparison `(ψ ∘ φ)^* ≅ ψ^* ⋙ φ^*` of pullbacks of sheaves of modules —
`Stacks.SheafOfModules.pullbackModulesCompAdjIso`, the compositor of **Stacks 03D8** — is defined as
`CategoryTheory.Adjunction.leftAdjointUniq` of the two adjunctions of Stacks 03D7 it compares, so
the only thing it carries is its compatibility with their *units*. This file converts that into the
compatibility with the units of extension of scalars of **Stacks 03CZ**, on underlying sheaves of
sets:

`η^{ψ∘φ}_A ≫ c_A = φ⁻¹(η^ψ_A) ≫ η^φ_{ψ^*A}`,

where `η^h : h⁻¹M ⟶ h^*M` is `Stacks.Sheaves.RingedToposModules.extendScalarsUnitSheafHom`.

That is the compositor analogue of
`Stacks.Sheaves.RingedToposModules.extendScalarsUnitSheafHom_comp_mate`, and it is the identity the
monoidality of the compositor reduces to: the comparison of Stacks 03EL is the preimage of the
identity under the chain of bijections of that tag, and the bottom of the chain pairs two local
sections of the inverse images by the pure tensor of their images under `η`
(`Stacks.SheafOfModules.pairingApp_pullbackTensorBottom`).

## Main results

* `Stacks.SheafOfModules.unit_comp_pushforwardModules_map_pullbackModulesCompAdjIso`: the
  compatibility of the compositor with the unit of Stacks 03D7 for the composite, with the
  comparison of direct images moved to the far side.
* `Stacks.SheafOfModules.extendScalarsUnitSheafHom_comp_pullbackModulesCompAdjIso`: **the
  compositor of Stacks 03D8 against the units of extension of scalars of Stacks 03CZ.**

## Implementation notes

*Why the unit of the topos adjunction can be cancelled.* The identity proved here is an equation
between two morphisms of sheaves of sets out of `(ψ ∘ φ)⁻¹A`, whereas what the compositor carries is
an equation with the unit of `(ψ ∘ φ)⁻¹ ⊣ (ψ ∘ φ)_*` in front of both sides. Those two are
*equivalent*, not merely related, because `CategoryTheory.Adjunction.homEquiv` is a bijection and
`CategoryTheory.Adjunction.homEquiv_unit` says it is precomposition with the unit: so transposing
along the adjunction of Stacks 03D3 for the composite turns the identity below into the identity the
compositor carries. This is exactly how
`Stacks.Sheaves.RingedToposModules.extendScalarsUnitSheafHom_comp_mate` is proved for a mate.

*The step that is abstract.* Moving the comparison of direct images from the adjunction
`CategoryTheory.Adjunction.ofNatIsoRight` that the compositor is defined through to the far side of
the equation is a fact about adjunctions and a natural transformation of left adjoints, with no
sheaf of modules in it; it is `unit_comp_map_of_unit_ofNatIsoRight` below, stated over abstract
categories and applied by `exact`.

## References

* [Stacks Project, Tag 03CZ](https://stacks.math.columbia.edu/tag/03CZ)
* [Stacks Project, Tag 03D3](https://stacks.math.columbia.edu/tag/03D3)
* [Stacks Project, Tag 03D7](https://stacks.math.columbia.edu/tag/03D7)
* [Stacks Project, Tag 03D8](https://stacks.math.columbia.edu/tag/03D8)
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry CategoryTheory.Sheaf
open AlgebraicGeometry.SheafOfModules Stacks.Sheaves.RingedToposModules

namespace Stacks.SheafOfModules

universe w w' w'' v u v' u' v'' u''

/-- **The unit identity of a natural transformation of left adjoints, with the comparison of the
right adjoints moved to the far side.** Let `adj : L ⊣ R` and let `adjc : L₁ ⋙ L₂ ⊣ R₂ ⋙ R₁` be a
second adjunction, let `e : R₂ ⋙ R₁ ≅ R` compare the two right adjoints and let `c : L ⟶ L₁ ⋙ L₂`.
If `c` satisfies the unit identity for `adj` transported along `e` — which is what
`CategoryTheory.Adjunction.unit_leftAdjointUniq_hom_app` supplies — then it satisfies the same
identity for `adj` itself, at the price of the comparison `e` after the unit of `adjc`.

Stated over abstract categories and applied by `exact`: the content is the naturality of `e.inv`
at `c`, and at the concrete adjunctions of Stacks 03D7 a rewrite of it is expensive. -/
private lemma unit_comp_map_of_unit_ofNatIsoRight
    {𝒜 : Type*} [Category 𝒜] {ℬ : Type*} [Category ℬ] {ℰ : Type*} [Category ℰ]
    {L₁ : 𝒜 ⥤ ℬ} {R₁ : ℬ ⥤ 𝒜} {L₂ : ℬ ⥤ ℰ} {R₂ : ℰ ⥤ ℬ} {L : 𝒜 ⥤ ℰ} {R : ℰ ⥤ 𝒜}
    (adj : L ⊣ R) (adjc : L₁ ⋙ L₂ ⊣ R₂ ⋙ R₁) (e : R₂ ⋙ R₁ ≅ R) (c : L ⟶ L₁ ⋙ L₂) (X : 𝒜)
    (h : (adj.ofNatIsoRight e.symm).unit.app X ≫ (R₂ ⋙ R₁).map (c.app X) =
      adjc.unit.app X) :
    adj.unit.app X ≫ R.map (c.app X) =
      adjc.unit.app X ≫ e.hom.app ((L₁ ⋙ L₂).obj X) := by
  have hu : (adj.ofNatIsoRight e.symm).unit.app X =
      adj.unit.app X ≫ e.inv.app (L.obj X) := by simp
  have key : adj.unit.app X ≫ R.map (c.app X) ≫ e.inv.app ((L₁ ⋙ L₂).obj X) =
      adjc.unit.app X := by
    rw [← h, hu, Category.assoc, ← e.inv.naturality (c.app X)]
  rw [← key, Category.assoc, Category.assoc, e.inv_hom_id_app, Category.comp_id]

section Unit

variable {X : RingedTopos.{v, u, w}} {Y : RingedTopos.{v', u', w'}}
  {Z : RingedTopos.{v'', u'', w''}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  [Z.J.HasSheafCompose (forget₂ CommRingCat.{w''} RingCat.{w''})]
  [X.J.HasSheafCompose (forget RingCat.{w})] [Y.J.HasSheafCompose (forget RingCat.{w'})]
  [Z.J.HasSheafCompose (forget RingCat.{w''})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w'})]
  [Z.J.HasSheafCompose (forget AddCommGrpCat.{w''})]
  [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify Y.J AddCommGrpCat.{w'}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w'}]
  (φ : AlgebraicGeometry.RingedToposHom X Y) (ψ : AlgebraicGeometry.RingedToposHom Y Z)
  (A : SheafOfModules.{w''} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O))

/-- **The compositor of Stacks 03D8 against the unit of Stacks 03D7 for the composite.** The unit
for `ψ ∘ φ` followed by the direct image along `ψ ∘ φ` of the compositor is the unit of the
composite of the two adjunctions, followed by the comparison `ψ_*(φ_*M) ≅ (ψ ∘ φ)_*M` of direct
images.

This is `Stacks.Sheaves.RingedToposModules.unit_pullbackModulesCompIso_hom_app` — the identity the
compositor is defined by — with the comparison of direct images moved out of the adjunction it is
stated through. -/
theorem unit_comp_pushforwardModules_map_pullbackModulesCompAdjIso :
    (pullbackAdjPushforwardModules (ψ.comp φ).toModulesHom).unit.app A ≫
        (pushforwardModules (ψ.comp φ).toModulesHom).map
          ((pullbackModulesCompAdjIso φ ψ).hom.app A) =
      ((pullbackAdjPushforwardModules ψ.toModulesHom).comp
            (pullbackAdjPushforwardModules φ.toModulesHom)).unit.app A ≫
        (pushforwardModulesCompIso φ.toModulesHom ψ.toModulesHom (ψ.comp φ).toModulesHom
          (compPushforwardToposIso φ ψ) (compPushforwardToposIso_fSharpSet φ ψ)).hom.app
          ((φ.toModulesHom.pullbackModules).obj
            ((ψ.toModulesHom.pullbackModules).obj A)) :=
  unit_comp_map_of_unit_ofNatIsoRight
    (pullbackAdjPushforwardModules (ψ.comp φ).toModulesHom)
    ((pullbackAdjPushforwardModules ψ.toModulesHom).comp
      (pullbackAdjPushforwardModules φ.toModulesHom))
    (pushforwardModulesCompIso φ.toModulesHom ψ.toModulesHom (ψ.comp φ).toModulesHom
      (compPushforwardToposIso φ ψ) (compPushforwardToposIso_fSharpSet φ ψ))
    (pullbackModulesCompAdjIso φ ψ).hom A
    (unit_pullbackModulesCompIso_hom_app φ.toModulesHom ψ.toModulesHom
      (ψ.comp φ).toModulesHom (compPushforwardToposIso φ ψ)
      (compPushforwardToposIso_fSharpSet φ ψ) A)

omit [X.J.HasSheafCompose (forget AddCommGrpCat)] [Y.J.HasSheafCompose (forget AddCommGrpCat)]
  [Z.J.HasSheafCompose (forget AddCommGrpCat)] [HasWeakSheafify X.J AddCommGrpCat]
  [X.J.WEqualsLocallyBijective AddCommGrpCat] [HasWeakSheafify Y.J AddCommGrpCat]
  [Y.J.WEqualsLocallyBijective AddCommGrpCat] in
/-- **The comparison of the geometric direct images for the composite is the identity.**
`Stacks.SheafOfModules.compPushforwardToposIso` is `CategoryTheory.Iso.refl`, so each of its
components is an identity; the object it is the identity of is written out, which is what lets it
be cancelled against a morphism whose target is spelled that way. -/
lemma compPushforwardToposIso_hom_app (S : Sheaf X.J (Type w)) :
    (compPushforwardToposIso φ ψ).hom.app S =
      𝟙 ((φ.toToposHom.pushforward ⋙ ψ.toToposHom.pushforward).obj S) := rfl

/-- **The unit of the composite of the two adjunctions of Stacks 03D7, on underlying sheaves of
sets.** It is the unit of `(ψ ∘ φ)⁻¹ ⊣ (ψ ∘ φ)_*` followed by the direct image along the composite
of the inverse image along `φ` of the unit of extension of scalars for `ψ` and the unit for `φ`.

This is `CategoryTheory.Adjunction.comp_unit_app` twice — once for the two adjunctions of
Stacks 03D7, once for the two of Stacks 03D3 — with each unit of Stacks 03D7 read on underlying
sheaves of sets and the unit of `φ⁻¹ ⊣ φ_*` moved across the unit of extension of scalars for `ψ`
by its own naturality. -/
private lemma moduleSheafFunctor_map_comp_unit_app :
    (Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)).map
        (((pullbackAdjPushforwardModules ψ.toModulesHom).comp
          (pullbackAdjPushforwardModules φ.toModulesHom)).unit.app A) =
      (ψ.toToposHom.comp φ.toToposHom).adj.unit.app
          (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Z.O) A) ≫
        (ψ.toToposHom.comp φ.toToposHom).pushforward.map
          (φ.toToposHom.inverseImage.map (extendScalarsUnitSheafHom ψ.toModulesHom A) ≫
            extendScalarsUnitSheafHom φ.toModulesHom
              ((ψ.toModulesHom.pullbackModules).obj A)) := by
  refine Eq.trans (congrArg
    (Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)).map
    (Adjunction.comp_unit_app (pullbackAdjPushforwardModules ψ.toModulesHom)
      (pullbackAdjPushforwardModules φ.toModulesHom) A)) ?_
  refine Eq.trans
    ((Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)).map_comp _ _) ?_
  refine Eq.trans (eq_whisker
    (moduleSheafFunctor_map_pullbackAdjPushforwardModules_unit_app ψ.toModulesHom A) _) ?_
  refine Eq.trans (whisker_eq _ (moduleSheafFunctor_map_pushforwardModules_map
    ψ.toModulesHom ((pullbackAdjPushforwardModules φ.toModulesHom).unit.app
      ((ψ.toModulesHom.pullbackModules).obj A)))) ?_
  refine Eq.trans (whisker_eq _ (congrArg ψ.toToposHom.pushforward.map
    (moduleSheafFunctor_map_pullbackAdjPushforwardModules_unit_app φ.toModulesHom
      ((ψ.toModulesHom.pullbackModules).obj A)))) ?_
  refine Eq.trans (whisker_eq _ (ψ.toToposHom.pushforward.map_comp _ _)) ?_
  refine Eq.trans (Category.assoc _ _ _) ?_
  refine Eq.trans (whisker_eq _ (Category.assoc _ _ _).symm) ?_
  refine Eq.trans (whisker_eq _ (eq_whisker
    (ψ.toToposHom.pushforward.map_comp _ _).symm _)) ?_
  refine Eq.trans (whisker_eq _ (eq_whisker (congrArg ψ.toToposHom.pushforward.map
    (φ.toToposHom.adj.unit.naturality (extendScalarsUnitSheafHom ψ.toModulesHom A))) _)) ?_
  refine Eq.trans (whisker_eq _ (eq_whisker (ψ.toToposHom.pushforward.map_comp _ _) _)) ?_
  refine Eq.trans (whisker_eq _ (Category.assoc _ _ _)) ?_
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine Eq.trans (whisker_eq _ ((ψ.toToposHom.pushforward.map_comp _ _).symm.trans
    (congrArg ψ.toToposHom.pushforward.map
      (φ.toToposHom.pushforward.map_comp _ _).symm))) ?_
  exact eq_whisker (Adjunction.comp_unit_app ψ.toToposHom.adj φ.toToposHom.adj
    (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Z.O) A)).symm _

/-- **The transpose of the unit of extension of scalars for the composite followed by the
compositor.** Transposed along the adjunction of Stacks 03D3 for the composite, it is the topos
unit followed by the direct image along the composite of the two units of extension of scalars
taken in turn — which is the transpose of the right-hand side of the identity this file proves. -/
private lemma homEquiv_extendScalarsUnitSheafHom_comp_pullbackModulesCompAdjIso :
    (ψ.toToposHom.comp φ.toToposHom).adj.homEquiv
        (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Z.O) A)
        (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
          ((φ.toModulesHom.pullbackModules).obj ((ψ.toModulesHom.pullbackModules).obj A)))
        (extendScalarsUnitSheafHom (ψ.comp φ).toModulesHom A ≫
          (Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).map
            ((pullbackModulesCompAdjIso φ ψ).hom.app A)) =
      (ψ.toToposHom.comp φ.toToposHom).adj.unit.app
          (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Z.O) A) ≫
        (ψ.toToposHom.comp φ.toToposHom).pushforward.map
          (φ.toToposHom.inverseImage.map (extendScalarsUnitSheafHom ψ.toModulesHom A) ≫
            extendScalarsUnitSheafHom φ.toModulesHom
              ((ψ.toModulesHom.pullbackModules).obj A)) := by
  refine Eq.trans (Adjunction.homEquiv_unit _ _ _ _) ?_
  refine Eq.trans (whisker_eq _
    ((ψ.toToposHom.comp φ.toToposHom).pushforward.map_comp _ _)) ?_
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine Eq.trans (eq_whisker
    (moduleSheafFunctor_map_pullbackAdjPushforwardModules_unit_app
      (ψ.comp φ).toModulesHom A).symm _) ?_
  refine Eq.trans (whisker_eq _ (moduleSheafFunctor_map_pushforwardModules_map
    (ψ.comp φ).toModulesHom ((pullbackModulesCompAdjIso φ ψ).hom.app A)).symm) ?_
  refine Eq.trans
    ((Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)).map_comp _ _).symm ?_
  refine Eq.trans (congrArg
    (Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)).map
    (unit_comp_pushforwardModules_map_pullbackModulesCompAdjIso φ ψ A)) ?_
  refine Eq.trans
    ((Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)).map_comp _ _) ?_
  refine Eq.trans (eq_whisker (moduleSheafFunctor_map_comp_unit_app φ ψ A) _) ?_
  refine Eq.trans (whisker_eq _
    (moduleSheafFunctor_map_pushforwardModulesCompIso_hom_app φ.toModulesHom ψ.toModulesHom
      (ψ.comp φ).toModulesHom (compPushforwardToposIso φ ψ)
      (compPushforwardToposIso_fSharpSet φ ψ)
      ((φ.toModulesHom.pullbackModules).obj ((ψ.toModulesHom.pullbackModules).obj A)))) ?_
  refine Eq.trans (whisker_eq _ (compPushforwardToposIso_hom_app φ ψ
    (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
      ((φ.toModulesHom.pullbackModules).obj ((ψ.toModulesHom.pullbackModules).obj A))))) ?_
  exact Category.comp_id
    ((ψ.toToposHom.comp φ.toToposHom).adj.unit.app
        (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Z.O) A) ≫
      (ψ.toToposHom.comp φ.toToposHom).pushforward.map
        (φ.toToposHom.inverseImage.map (extendScalarsUnitSheafHom ψ.toModulesHom A) ≫
          extendScalarsUnitSheafHom φ.toModulesHom
            ((ψ.toModulesHom.pullbackModules).obj A)))

/-- **The compositor of Stacks 03D8 against the units of extension of scalars of Stacks 03CZ.**

On underlying sheaves of sets, the unit of extension of scalars for the composite followed by the
compositor is the inverse image along `φ` of the unit for `ψ`, followed by the unit for `φ` at
`ψ^*A`:

`η^{ψ∘φ}_A ≫ c_A = φ⁻¹(η^ψ_A) ≫ η^φ_{ψ^*A}`.

This is the compositor analogue of
`Stacks.Sheaves.RingedToposModules.extendScalarsUnitSheafHom_comp_mate`, and it is proved the same
way: both sides are morphisms out of `(ψ ∘ φ)⁻¹A`, so the identity is equivalent — by the bijection
`CategoryTheory.Adjunction.homEquiv` of the adjunction of Stacks 03D3 for the composite, which by
`CategoryTheory.Adjunction.homEquiv_unit` is precomposition with the topos unit — to the identity
with that unit in front, and that one is the unit identity the compositor is defined by, read on
underlying sheaves of sets. -/
theorem extendScalarsUnitSheafHom_comp_pullbackModulesCompAdjIso :
    extendScalarsUnitSheafHom (ψ.comp φ).toModulesHom A ≫
        (Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).map
          ((pullbackModulesCompAdjIso φ ψ).hom.app A) =
      φ.toToposHom.inverseImage.map (extendScalarsUnitSheafHom ψ.toModulesHom A) ≫
        extendScalarsUnitSheafHom φ.toModulesHom
          ((ψ.toModulesHom.pullbackModules).obj A) := by
  refine ((ψ.toToposHom.comp φ.toToposHom).adj.homEquiv
    (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Z.O) A)
    (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
      ((φ.toModulesHom.pullbackModules).obj
        ((ψ.toModulesHom.pullbackModules).obj A)))).injective ?_
  exact (homEquiv_extendScalarsUnitSheafHom_comp_pullbackModulesCompAdjIso φ ψ A).trans
    (Adjunction.homEquiv_unit _ _ _ _).symm

end Unit

end Stacks.SheafOfModules

end
