module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExtendScalarsCompIsoSections
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackTensorChainSections

/-! # Base change of a tensor product of sheaves of modules, in the ring variable

`Stacks.Sheaves.RingedToposModules.extendScalarsTensorIso` is the base-change comparison

`A₂ ⊗_{A₁} (F ⊗_{A₁} G) ≅ (A₂ ⊗_{A₁} F) ⊗_{A₂} (A₂ ⊗_{A₁} G)`

of Tag 03CU, which is step 6 of the chain of Tag 03EL.  It came with its naturality in the two
modules (`…​.extendScalarsTensorIso_hom_naturality`) and with its values on local sections
(`…​.extendScalarsTensorIso_hom_val_app_extendScalarsUnit_tmul`), and with nothing at all in the
*ring* variable: no statement related the comparison for a composite `θ₁ ≫ θ₂` of morphisms of
presheaves of commutative rings to the comparisons for `θ₁` and for `θ₂`.  That law is what this
file supplies.

The transport it needs is `Stacks.Sheaves.RingedToposModules.extendScalarsCompIso`, which
identifies `A₃ ⊗_{A₁} -` with `A₃ ⊗_{A₂} (A₂ ⊗_{A₁} -)`; it enters in three places, once on the
source `A₃ ⊗_{A₁} (F ⊗_{A₁} G)` and once on each of the two tensor factors of the target.  So the
law *is* the coherence between the two comparisons, and it says exactly that
`extendScalarsCompIso` is a monoidal natural isomorphism.

## Main results

* `Stacks.Sheaves.RingedToposModules.extendScalars_tensorSheaf_hom_ext`: **two morphisms out of an
  extension of scalars of a tensor product sheaf agree as soon as they agree on the pure tensors
  of local sections.** This is the extensionality principle the law is proved by: the adjunction
  of Tag 03CZ reduces a morphism out of `A₂ ⊗_{A₁} T` to one out of `T`, and
  `Stacks.SheafOfModules.tensorSheaf_hom_ext` reduces that to its values on pure tensors.
* `Stacks.Sheaves.RingedToposModules.extendScalarsTensorIso_comp_val_app_unit_tmul`: **the two
  sides of the law on a pure tensor of local sections.** Both carry the unit image of `x ⊗ₜ y` to
  the unit image of the pure tensor of the two iterated unit images of `x` and of `y`; this is
  the whole content, and it is a computation with no scalars left over.
* `Stacks.Sheaves.RingedToposModules.extendScalarsCompIso_hom_app_comp_extendScalarsTensorIso`:
  **the composition law in the ring variable, as a commuting square.** Base change along
  `θ₁ ≫ θ₂` followed by the composition comparison on the two factors is the composition
  comparison on the source followed by base change along `θ₁` and then along `θ₂`.
* `Stacks.Sheaves.RingedToposModules.extendScalarsTensorIso_hom_eq_comp`: the same law solved for
  the comparison at the composite, which is the shape a consumer that has to *rewrite* the
  comparison at a composite wants.

## Implementation notes

Every statement here is read on local sections rather than by a universal property, because the
comparison is a three-fold composite of sheafification comparisons and only its sectionwise
behaviour is known. The one piece of genuinely new bookkeeping is the extensionality principle:
the adjunction half of it is isolated as a private lemma over an *abstract* adjunction, since the
right adjoint `SheafOfModules.restrictScalars` has to be crossed and a `rw` whose motive mentions
it is reported ill-typed at the implicit transparency level.

The two algebraic consequences drawn at the end — that a tensor of two retractions is a
retraction, and the rearrangement of one composite into another — are likewise private lemmas over
an abstract (monoidal) category, applied by `exact`. Stated at the sheaf-of-modules level they
would both have to cross the seam between `commRingSheaf J A₃ h₃` and the index of
`Stacks.SheafOfModules.TensorSheafification.tensorSheaf`, and that seam makes the rewrite fail
here.

## References

* [Stacks Project, Tag 03CU](https://stacks.math.columbia.edu/tag/03CU)
* [Stacks Project, Tag 03CZ](https://stacks.math.columbia.edu/tag/03CZ)
* [Stacks Project, Tag 03EL](https://stacks.math.columbia.edu/tag/03EL)
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory
open Stacks.PresheafOfModules.ChangeOfRings
open scoped TensorProduct

universe w v u

namespace Stacks.Sheaves.RingedToposModules

open Stacks.SheafOfModules.TensorSheafification

section Ext

/-- Two morphisms out of a value of a left adjoint agree as soon as their adjoint transposes do.
Stated over an abstract adjunction so that the consumer can apply it by `exact`: the right adjoint
of the adjunction of Tag 03CZ is `SheafOfModules.restrictScalars`, and a rewrite whose motive
mentions it is reported ill-typed at the implicit transparency level. -/
private lemma hom_ext_of_unit_comp {𝒞 : Type u} [Category.{v} 𝒞] {𝒟 : Type*} [Category 𝒟]
    {F : 𝒞 ⥤ 𝒟} {G : 𝒟 ⥤ 𝒞} (adj : F ⊣ G) {X : 𝒞} {Y : 𝒟} {m m' : F.obj X ⟶ Y}
    (h : adj.unit.app X ≫ G.map m = adj.unit.app X ≫ G.map m') : m = m' := by
  refine (adj.homEquiv X Y).injective ?_
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  exact h

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]
  {A₁ A₂ : Cᵒᵖ ⥤ CommRingCat.{w}} (θ : A₁ ⟶ A₂)
  (h₁ : Presheaf.IsSheaf J (ringPresheaf A₁)) (h₂ : Presheaf.IsSheaf J (ringPresheaf A₂))

/-- **Two morphisms out of an extension of scalars of a tensor product sheaf agree as soon as they
agree on the sheafification-unit images of pure tensors.**

The adjunction of Tag 03CZ turns a morphism `A₂ ⊗_{A₁} (F ⊗_{A₁} G) ⟶ N` into a morphism
`F ⊗_{A₁} G ⟶ N|` out of the tensor product sheaf, and
`Stacks.SheafOfModules.tensorSheaf_hom_ext` determines that by its values on pure tensors of local
sections. The elements the hypothesis speaks about are exactly those on which
`Stacks.Sheaves.RingedToposModules.extendScalarsTensorIso_hom_val_app_extendScalarsUnit_tmul`
evaluates the base-change comparison, so this is the principle every statement about the
comparison in the ring variable is proved by. -/
lemma extendScalars_tensorSheaf_hom_ext {F G : SheafOfModules.{w} (commRingSheaf J A₁ h₁)}
    {N : SheafOfModules.{w} (commRingSheaf J A₂ h₂)}
    {m m' : (extendScalars J θ h₁ h₂).obj ((((Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨A₁, Presheaf.isSheaf_of_isSheaf_comp _ A₁
          (forget₂ CommRingCat RingCat) h₁⟩).obj F).obj G)) ⟶ N}
    (hyp : ∀ (V : Cᵒᵖ) (x : F.val.obj V) (y : G.val.obj V),
      m.val.app V
          (((extendRestrictScalarsAdjunction J θ h₁ h₂).unit.app
              ((((Stacks.SheafOfModules.Tensor.sheafTensor
                  ⟨A₁, Presheaf.isSheaf_of_isSheaf_comp _ A₁
                    (forget₂ CommRingCat RingCat) h₁⟩).obj F).obj G))).val.app V
            (((PresheafOfModules.sheafificationAdjunction
                (R := commRingSheaf J A₁ h₁) (𝟙 _)).unit.app (F.val ⊗ G.val)).app V
              (x ⊗ₜ[(ringPresheaf A₁).obj V] y))) =
        m'.val.app V
          (((extendRestrictScalarsAdjunction J θ h₁ h₂).unit.app
              ((((Stacks.SheafOfModules.Tensor.sheafTensor
                  ⟨A₁, Presheaf.isSheaf_of_isSheaf_comp _ A₁
                    (forget₂ CommRingCat RingCat) h₁⟩).obj F).obj G))).val.app V
            (((PresheafOfModules.sheafificationAdjunction
                (R := commRingSheaf J A₁ h₁) (𝟙 _)).unit.app (F.val ⊗ G.val)).app V
              (x ⊗ₜ[(ringPresheaf A₁).obj V] y)))) :
    m = m' :=
  hom_ext_of_unit_comp (extendRestrictScalarsAdjunction J θ h₁ h₂)
    (Stacks.SheafOfModules.tensorSheaf_hom_ext (fun V x y ↦ hyp V x y))

end Ext

section CompositionLaw

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]
  {A₁ A₂ A₃ : Cᵒᵖ ⥤ CommRingCat.{w}} (θ₁ : A₁ ⟶ A₂) (θ₂ : A₂ ⟶ A₃)
  (h₁ : Presheaf.IsSheaf J (ringPresheaf A₁)) (h₂ : Presheaf.IsSheaf J (ringPresheaf A₂))
  (h₃ : Presheaf.IsSheaf J (ringPresheaf A₃))

/-- The four-step chain that evaluates the *left* side of the composition law on a local section,
over abstract types and functions.

Abstract on purpose, and applied by `exact`. The goal it is applied to is not type-correct at the
`implicit` transparency level — `Stacks.SheafOfModules.TensorSheafification.tensorSheaf` is indexed
by `structureSheaf A₃ h₃` while extension of scalars produces sheaves of modules over
`commRingSheaf J A₃ h₃`, and the two agree only by unfolding a `def` — so `rw`, `simp` and `show`
all fail on it, and only a term checked at default transparency gets through. Phrasing the chain
abstractly has a second benefit: every long subexpression is recovered by unification from the
types of the four hypotheses, instead of being written out. -/
private lemma value_chain_left {S₀ S₁ S₂ S₃ T₀ T₁ T₂ : Type*}
    {c : S₀ → S₁} {p : S₁ → S₂} {q : S₂ → S₃}
    {k : T₀ → T₁} {j : T₁ → S₁} {n : T₂ → S₂} {t : T₁ → T₂}
    {e : S₀} {u : T₀} {w : T₂} {ans : S₃}
    (hstep : ∀ v, p (j v) = n (t v)) (hcomp : c e = j (k u)) (hinner : t (k u) = w)
    (houter : q (n w) = ans) :
    q (p (c e)) = ans := by
  rw [hcomp, hstep, hinner, houter]

/-- The three-step chain that evaluates the *right* side of the composition law on a local
section, over abstract types and functions. The binary operation standing for `⊗ₜ` is abstract
too, so that the two comparisons on the tensor factors can be inserted after the pure-tensor
formula without naming the sheafification unit they sit under.

Abstract for the same reason as
`Stacks.Sheaves.RingedToposModules.value_chain_left`; see there. -/
private lemma value_chain_right {S₀ U₁ U₂ X X' Y Y' Z Z' : Type*}
    {t : S₀ → U₁} {s : U₁ → U₂} {sU : Z → U₁} {sU' : Z' → U₂}
    {tm : X → Y → Z} {tm' : X' → Y' → Z'} {φ : X → X'} {ψ : Y → Y'}
    {e : S₀} {cc : X} {dd : Y} {a : X'} {b : Y'}
    (htmul : ∀ cv dv, s (sU (tm cv dv)) = sU' (tm' (φ cv) (ψ dv)))
    (hcomp : t e = sU (tm cc dd)) (hfst : φ cc = a) (hsnd : ψ dd = b) :
    s (t e) = sU' (tm' a b) := by
  rw [hcomp, htmul, hfst, hsnd]

/-- The sheafification of a tensor product of two morphisms of presheaves of modules, on the
sheafification-unit image of a pure tensor: it is the unit image of the pure tensor of the two
values. This is
`Stacks.SheafOfModules.TensorSheafification.sheafification_map_val_app_unit` followed by
`ModuleCat.MonoidalCategory.tensorHom_tmul`. -/
private lemma sheafification_map_tensorHom_val_app_unit_tmul
    (𝒪 : Cᵒᵖ ⥤ CommRingCat.{w}) (h𝒪 : Presheaf.IsSheaf J (ringPresheaf 𝒪))
    {P P' Q Q' : PresheafOfModules.{w} (ringPresheaf 𝒪)} (φ : P ⟶ P') (ψ : Q ⟶ Q')
    (V : Cᵒᵖ) (x : P.obj V) (y : Q.obj V) :
    ((PresheafOfModules.sheafification (R := commRingSheaf J 𝒪 h𝒪) (𝟙 _)).map
          (φ ⊗ₘ ψ)).val.app V
        (((PresheafOfModules.sheafificationAdjunction
            (R := commRingSheaf J 𝒪 h𝒪) (𝟙 _)).unit.app (P ⊗ Q)).app V
          (x ⊗ₜ[(ringPresheaf 𝒪).obj V] y)) =
      ((PresheafOfModules.sheafificationAdjunction
          (R := commRingSheaf J 𝒪 h𝒪) (𝟙 _)).unit.app (P' ⊗ Q')).app V
        (φ.app V x ⊗ₜ[(ringPresheaf 𝒪).obj V] ψ.app V y) :=
  (sheafification_map_val_app_unit 𝒪 h𝒪 (φ ⊗ₘ ψ) V
      (x ⊗ₜ[(ringPresheaf 𝒪).obj V] y)).trans
    (congrArg _ (ModuleCat.MonoidalCategory.tensorHom_tmul (φ.app V) (ψ.app V) x y))

/-- **The two sides of the composition law for base change of a tensor product, on a pure tensor
of local sections.**

Reading from the top: the composition comparison on the source
`A₃ ⊗_{A₁} (F ⊗_{A₁} G)`, then base change along `θ₁`, then base change along `θ₂`, carries the
unit image of a pure tensor `x ⊗ₜ y` to the unit image of
`(η₂ η₁ x) ⊗ₜ (η₂ η₁ y)`, the `η`s being the units of Tag 03CZ.  Reading along the other side:
base change along `θ₁ ≫ θ₂` followed by the composition comparison on the two tensor factors
carries it to the unit image of `(c η x) ⊗ₜ (c η y)`, which is the same thing because the
comparison carries the unit for the composite to the two units in turn
(`Stacks.Sheaves.RingedToposModules.extendScalarsCompIso_hom_app_val_app_unit`).

This is the entire content of the composition law; everything else is extensionality. -/
lemma extendScalarsTensorIso_comp_val_app_unit_tmul
    (F G : SheafOfModules.{w} (commRingSheaf J A₁ h₁)) (V : Cᵒᵖ)
    (x : F.val.obj V) (y : G.val.obj V) :
    (extendScalarsTensorIso θ₂ h₂ h₃ ((extendScalars J θ₁ h₁ h₂).obj F)
            ((extendScalars J θ₁ h₁ h₂).obj G)).hom.val.app V
        (((extendScalars J θ₂ h₂ h₃).map
              (extendScalarsTensorIso θ₁ h₁ h₂ F G).hom).val.app V
          (((extendScalarsCompIso J θ₁ θ₂ h₁ h₂ h₃).hom.app
                ((((Stacks.SheafOfModules.Tensor.sheafTensor
                    ⟨A₁, Presheaf.isSheaf_of_isSheaf_comp _ A₁
                      (forget₂ CommRingCat RingCat) h₁⟩).obj F).obj G))).val.app V
            (((extendRestrictScalarsAdjunction J (θ₁ ≫ θ₂) h₁ h₃).unit.app
                ((((Stacks.SheafOfModules.Tensor.sheafTensor
                    ⟨A₁, Presheaf.isSheaf_of_isSheaf_comp _ A₁
                      (forget₂ CommRingCat RingCat) h₁⟩).obj F).obj G))).val.app V
              (((PresheafOfModules.sheafificationAdjunction
                  (R := commRingSheaf J A₁ h₁) (𝟙 _)).unit.app (F.val ⊗ G.val)).app V
                (x ⊗ₜ[(ringPresheaf A₁).obj V] y))))) =
      ((PresheafOfModules.sheafification (R := commRingSheaf J A₃ h₃) (𝟙 _)).map
            (((extendScalarsCompIso J θ₁ θ₂ h₁ h₂ h₃).hom.app F).val ⊗ₘ
              ((extendScalarsCompIso J θ₁ θ₂ h₁ h₂ h₃).hom.app G).val)).val.app V
        ((extendScalarsTensorIso (θ₁ ≫ θ₂) h₁ h₃ F G).hom.val.app V
          (((extendRestrictScalarsAdjunction J (θ₁ ≫ θ₂) h₁ h₃).unit.app
              ((((Stacks.SheafOfModules.Tensor.sheafTensor
                  ⟨A₁, Presheaf.isSheaf_of_isSheaf_comp _ A₁
                    (forget₂ CommRingCat RingCat) h₁⟩).obj F).obj G))).val.app V
            (((PresheafOfModules.sheafificationAdjunction
                (R := commRingSheaf J A₁ h₁) (𝟙 _)).unit.app (F.val ⊗ G.val)).app V
              (x ⊗ₜ[(ringPresheaf A₁).obj V] y)))) :=
  (value_chain_left
      (extendScalars_map_val_app_unit J θ₂ h₂ h₃
        (extendScalarsTensorIso θ₁ h₁ h₂ F G).hom V)
      (extendScalarsCompIso_hom_app_val_app_unit J θ₁ θ₂ h₁ h₂ h₃
        ((((Stacks.SheafOfModules.Tensor.sheafTensor
            ⟨A₁, Presheaf.isSheaf_of_isSheaf_comp _ A₁
              (forget₂ CommRingCat RingCat) h₁⟩).obj F).obj G)) V
        (((PresheafOfModules.sheafificationAdjunction
            (R := commRingSheaf J A₁ h₁) (𝟙 _)).unit.app (F.val ⊗ G.val)).app V
          (x ⊗ₜ[(ringPresheaf A₁).obj V] y)))
      (extendScalarsTensorIso_hom_val_app_extendScalarsUnit_tmul θ₁ h₁ h₂ F G V x y)
      (extendScalarsTensorIso_hom_val_app_extendScalarsUnit_tmul θ₂ h₂ h₃
        ((extendScalars J θ₁ h₁ h₂).obj F) ((extendScalars J θ₁ h₁ h₂).obj G) V
        (((extendRestrictScalarsAdjunction J θ₁ h₁ h₂).unit.app F).val.app V x)
        (((extendRestrictScalarsAdjunction J θ₁ h₁ h₂).unit.app G).val.app V y))).trans
    (value_chain_right
      (sheafification_map_tensorHom_val_app_unit_tmul A₃ h₃
        ((extendScalarsCompIso J θ₁ θ₂ h₁ h₂ h₃).hom.app F).val
        ((extendScalarsCompIso J θ₁ θ₂ h₁ h₂ h₃).hom.app G).val V)
      (extendScalarsTensorIso_hom_val_app_extendScalarsUnit_tmul (θ₁ ≫ θ₂) h₁ h₃ F G V x y)
      (extendScalarsCompIso_hom_app_val_app_unit J θ₁ θ₂ h₁ h₂ h₃ F V x)
      (extendScalarsCompIso_hom_app_val_app_unit J θ₁ θ₂ h₁ h₂ h₃ G V y)).symm

/-- **The composition law for base change of a tensor product of sheaves of modules, in the ring
variable.**

For `θ₁ : A₁ ⟶ A₂` and `θ₂ : A₂ ⟶ A₃`, the base-change comparison of Tag 03CU for the composite
`θ₁ ≫ θ₂` agrees with the two comparisons for `θ₁` and for `θ₂` applied in turn, once both sides
are transported by the composition comparison
`Stacks.Sheaves.RingedToposModules.extendScalarsCompIso` of extension of scalars — on the source
`A₃ ⊗_{A₁} (F ⊗_{A₁} G)` on the left, and on each of the two tensor factors of the target
`(A₃ ⊗_{A₁} F) ⊗_{A₃} (A₃ ⊗_{A₁} G)` on the right.

Equivalently: `extendScalarsCompIso` is a monoidal natural isomorphism, the monoidal structures
being those of Tag 03CU.  This is the law that step 6 of the chain of Tag 03EL enters the
morphism variable only through. -/
lemma extendScalarsCompIso_hom_app_comp_extendScalarsTensorIso
    (F G : SheafOfModules.{w} (commRingSheaf J A₁ h₁)) :
    (extendScalarsCompIso J θ₁ θ₂ h₁ h₂ h₃).hom.app ((((Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨A₁, Presheaf.isSheaf_of_isSheaf_comp _ A₁
          (forget₂ CommRingCat RingCat) h₁⟩).obj F).obj G)) ≫
        (extendScalars J θ₂ h₂ h₃).map (extendScalarsTensorIso θ₁ h₁ h₂ F G).hom ≫
          (extendScalarsTensorIso θ₂ h₂ h₃ ((extendScalars J θ₁ h₁ h₂).obj F)
            ((extendScalars J θ₁ h₁ h₂).obj G)).hom =
      (extendScalarsTensorIso (θ₁ ≫ θ₂) h₁ h₃ F G).hom ≫
        (PresheafOfModules.sheafification (R := commRingSheaf J A₃ h₃) (𝟙 _)).map
          (((extendScalarsCompIso J θ₁ θ₂ h₁ h₂ h₃).hom.app F).val ⊗ₘ
            ((extendScalarsCompIso J θ₁ θ₂ h₁ h₂ h₃).hom.app G).val) :=
  extendScalars_tensorSheaf_hom_ext (θ₁ ≫ θ₂) h₁ h₃
    (fun V x y ↦
      extendScalarsTensorIso_comp_val_app_unit_tmul θ₁ θ₂ h₁ h₂ h₃ F G V x y)

/-- The image under a functor of a tensor product of two retractions is a retraction. Stated over
an abstract monoidal category and applied by `exact`, for the reason recorded in the module
docstring: at the sheaf-of-modules level the statement crosses the seam between
`commRingSheaf J A₃ h₃` and the index of
`Stacks.SheafOfModules.TensorSheafification.tensorSheaf`, and a rewrite there is reported
ill-typed. -/
private lemma map_tensorHom_comp_map_tensorHom_eq_id {𝒜 : Type*} [Category 𝒜]
    [MonoidalCategory 𝒜] {ℬ : Type*} [Category ℬ] (S : 𝒜 ⥤ ℬ) {P P' Q Q' : 𝒜}
    {φ : P ⟶ P'} {φ' : P' ⟶ P} {ψ : Q ⟶ Q'} {ψ' : Q' ⟶ Q}
    (hφ : φ ≫ φ' = 𝟙 P) (hψ : ψ ≫ ψ' = 𝟙 Q) :
    S.map (φ ⊗ₘ ψ) ≫ S.map (φ' ⊗ₘ ψ') = 𝟙 (S.obj (P ⊗ Q)) := by
  rw [← S.map_comp, MonoidalCategory.tensorHom_comp_tensorHom, hφ, hψ,
    MonoidalCategory.id_tensorHom_id, S.map_id]

/-- A commuting square whose bottom edge has a retraction, solved for the left-hand vertical.
Stated over an abstract category and applied by `exact`; see the module docstring. -/
private lemma eq_comp_of_comp_eq_comp {𝒟 : Type*} [Category 𝒟] {W X Y Z : 𝒟}
    {a : W ⟶ X} {b : X ⟶ Y} {c : W ⟶ Z} {d : Z ⟶ Y} {e : Y ⟶ Z}
    (h : a ≫ b = c ≫ d) (he : d ≫ e = 𝟙 Z) : c = a ≫ b ≫ e := by
  rw [← Category.assoc, h, Category.assoc, he, Category.comp_id]

/-- **The composition law for base change of a tensor product, solved for the comparison at the
composite.**

This is
`Stacks.Sheaves.RingedToposModules.extendScalarsCompIso_hom_app_comp_extendScalarsTensorIso`
rearranged so that the comparison for `θ₁ ≫ θ₂` stands alone: it is the composition comparison on
the source, then base change along `θ₁`, then base change along `θ₂`, then the *inverse* of the
composition comparison on each of the two tensor factors.  This is the shape a consumer that has
to rewrite the base-change comparison at a composite morphism of presheaves of commutative rings
wants, since it eliminates the comparison rather than merely relating it to others. -/
lemma extendScalarsTensorIso_hom_eq_comp
    (F G : SheafOfModules.{w} (commRingSheaf J A₁ h₁)) :
    (extendScalarsTensorIso (θ₁ ≫ θ₂) h₁ h₃ F G).hom =
      (extendScalarsCompIso J θ₁ θ₂ h₁ h₂ h₃).hom.app ((((Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨A₁, Presheaf.isSheaf_of_isSheaf_comp _ A₁
            (forget₂ CommRingCat RingCat) h₁⟩).obj F).obj G)) ≫
        (extendScalars J θ₂ h₂ h₃).map (extendScalarsTensorIso θ₁ h₁ h₂ F G).hom ≫
          (extendScalarsTensorIso θ₂ h₂ h₃ ((extendScalars J θ₁ h₁ h₂).obj F)
              ((extendScalars J θ₁ h₁ h₂).obj G)).hom ≫
            (PresheafOfModules.sheafification (R := commRingSheaf J A₃ h₃) (𝟙 _)).map
              (((extendScalarsCompIso J θ₁ θ₂ h₁ h₂ h₃).inv.app F).val ⊗ₘ
                ((extendScalarsCompIso J θ₁ θ₂ h₁ h₂ h₃).inv.app G).val) :=
  (eq_comp_of_comp_eq_comp
      (extendScalarsCompIso_hom_app_comp_extendScalarsTensorIso θ₁ θ₂ h₁ h₂ h₃ F G)
      (map_tensorHom_comp_map_tensorHom_eq_id _
        (congrArg SheafOfModules.Hom.val
          ((extendScalarsCompIso J θ₁ θ₂ h₁ h₂ h₃).app F).hom_inv_id)
        (congrArg SheafOfModules.Hom.val
          ((extendScalarsCompIso J θ₁ θ₂ h₁ h₂ h₃).app G).hom_inv_id))).trans
    (congrArg (fun z ↦ (extendScalarsCompIso J θ₁ θ₂ h₁ h₂ h₃).hom.app
      ((((Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨A₁, Presheaf.isSheaf_of_isSheaf_comp _ A₁
            (forget₂ CommRingCat RingCat) h₁⟩).obj F).obj G)) ≫ z) (Category.assoc _ _ _))

end CompositionLaw

end Stacks.Sheaves.RingedToposModules

end
