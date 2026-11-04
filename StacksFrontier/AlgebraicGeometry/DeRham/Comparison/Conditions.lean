module

public import StacksFrontier.AlgebraicGeometry.DeRham.Comparison.AbsoluteForms
public import StacksFrontier.AlgebraicGeometry.ConormalAlgebra.GradedPullback
public import StacksFrontier.AlgebraicGeometry.Constructions.PullbackSectionMultiplication
public import StacksFrontier.AlgebraicGeometry.Descent.PullbackSectionsSheaf.UnitComparison
public import StacksFrontier.AlgebraicGeometry.Duality.ProjectionFormulaRestrictionSections

/-!
# The conditions of Stacks Section 0FL7 on maps of sheaves of differential forms

Let `f : Y ⟶ X` be a morphism of schemes and `L` an `𝒪_Y`-module. Section 0FL7 of the Stacks
project studies collections of `𝒪_Y`-linear maps

`c^p : Ω^p_{Y/ℤ} ⟶ f^*Ω^p_{X/ℤ} ⊗_{𝒪_Y} L`,  `p ≥ 0`,

(with `L = det(NL_{Y/X})` there) subject to

* (Tag 0H9C) `c^0(1) = 1 ⊗ δ` for a given global section `δ` of `L`, and
* (Tag 0H9D) `c^{q+p}(ω ∧ η) = ω ∧ c^p(η)` for local sections `ω` of `f^*Ω^q_{X/ℤ}` and `η` of
  `Ω^p_{Y/ℤ}`,

where on the left `ω` acts through the canonical map `f^*Ω^q_{X/ℤ} ⟶ Ω^q_{Y/ℤ}` and the product
of `Ω^•_{Y/ℤ}`, and on the right through the product of the pulled-back algebra
`f^*Ω^•_{X/ℤ}` tensored with the identity of `L`. This file states both conditions as equations
of morphisms of sheaves of modules and proves that they are equivalent to their elementwise
forms; for (0H9D) it also proves that it suffices to check the elementwise form over a basis of
opens and for `ω` in a generating set of each module of sections.

## Main definitions

* `AlgebraicGeometry.Scheme.Hom.pullbackFormsAlgebra`, `pullbackForms`: the graded algebra
  `f^*Ω^•_{X/ℤ}` (`Stacks.Conormal.gradedPullback`) and its pieces `f^*Ω^n_{X/ℤ}`.
* `AlgebraicGeometry.Scheme.Hom.twistedPullbackForms`: `f^*Ω^n_{X/ℤ} ⊗ L`, the tensor product
  sheaf, and `twistedPullbackFormsTmul`, its local pure tensors.
* `AlgebraicGeometry.Scheme.Hom.GarelMaps`: a family of maps `c^p`, `p : ℕ`.
* `AlgebraicGeometry.Scheme.Modules.globalSectionHom`: the morphism `𝒪_Y ⟶ L` of a global
  section.
* `AlgebraicGeometry.Scheme.Hom.GarelMaps.IsNormalized`: condition (0H9C).
* `AlgebraicGeometry.Scheme.Hom.absoluteFormsAction` and `twistedPullbackFormsMul`: the two
  actions of `f^*Ω^q_{X/ℤ}` in condition (0H9D), and `GarelMaps.IsMultiplicative`: condition
  (0H9D).

## Main results

* `AlgebraicGeometry.Scheme.Hom.GarelMaps.isNormalized_iff`: (0H9C) on global sections.
* `AlgebraicGeometry.Scheme.Hom.GarelMaps.isMultiplicative_iff`: (0H9D) on local sections.
* `AlgebraicGeometry.Scheme.Hom.GarelMaps.isMultiplicative_of_isBasis`: (0H9D) follows from its
  elementwise form over the opens of a basis, for `ω` running through generating sets.
* `AlgebraicGeometry.Scheme.Hom.absoluteFormsAction_tmul` and `twistedPullbackFormsMul_tmul`:
  the two actions on local pure tensors.

## Implementation notes

The tensor product is that of `Stacks.PullbackGradedAlgebra.monoidalCategory`, whose tensor
product is the tensor product sheaf `Stacks.SheafOfModules.Tensor.sheafTensor` on the nose
(`twistedPullbackForms_eq`), so local pure tensors are images under
`PresheafOfModules.tensorSheafUnit` (`twistedPullbackFormsTmul_eq`) and the section formulas of
`Stacks.PullbackTensorCoherence` apply. It is registered both at the ringed-space spelling and,
as `Stacks.AlgebraicGeometry.PullbackSectionMul.schemeTensorStrict`, at the `Y.Modules` spelling;
the two are the same term. Statements whose two sides mix the spellings are proved by explicit
`Eq.trans` chains with the extensionality lemmas applied to fully explicit arguments: leaving
those arguments to unification makes the defeq checks cross the boundary and exhaust the
recursion limit.

The degrees of the source are natural numbers, as in the source (`p ≥ 0`), while the graded
algebras are indexed by `ℤ`; the transport `↑q + ↑p = ↑(q + p)` is an `eqToHom` at the end of
each action.

## References

* [Stacks Project, Section 0FL7](https://stacks.math.columbia.edu/tag/0FL7)
* [Stacks Project, Tag 0H9C](https://stacks.math.columbia.edu/tag/0H9C)
* [Stacks Project, Tag 0H9D](https://stacks.math.columbia.edu/tag/0H9D)
-/

@[expose] public section

open CategoryTheory MonoidalCategory TopologicalSpace Opposite
open Stacks.PullbackTensorCoherence

universe u

namespace Stacks.PullbackTensorCoherence

attribute [local instance] Stacks.PullbackGradedAlgebra.monoidalCategory

open _root_.AlgebraicGeometry Stacks.RingedSpace

variable {Z : _root_.AlgebraicGeometry.RingedSpace.{u, u}}

/-- The inverse left unitor of Tag 01CA on local sections: `m ↦ 1 ⊗ m`. -/
theorem leftUnitor_inv_tmul (M : SheafOfModules.{u} (structureRingSheaf Z))
    (V : (Opens Z.carrier)ᵒᵖ) (m : M.val.obj V) :
    (λ_ M).inv.val.app V m =
      tmul Z (𝟙_ (SheafOfModules.{u} (structureRingSheaf Z))) M V
        (oneSec Z V) m :=
  (congrArg ((λ_ M).inv.val.app V)
      ((leftUnitor_hom_tmul V 1 m).trans (one_smul _ m)).symm).trans
    (Stacks.SheafOfModules.inv_val_app_hom_val_app (λ_ M) V _)

/-- The inverse associator of Tag 01CA on a local triple pure tensor, at the `tmul`
spelling. -/
theorem associator_inv_tmul
    {A B D : SheafOfModules.{u} (structureRingSheaf Z)}
    (V : (Opens Z.carrier)ᵒᵖ) (a : A.val.obj V) (b : B.val.obj V) (d : D.val.obj V) :
    (α_ A B D).inv.val.app V (tmul Z A (B ⊗ D) V a (tmul Z B D V b d)) =
      tmul Z (A ⊗ B) D V (tmul Z A B V a b) d :=
  Stacks.TensorSheafWorld.associator_inv_val_app_tensorSheafUnit Z.sheaf
    (structureSheafRing Z).property A B D V a b d

/-- Restriction of a local pure tensor is the pure tensor of the restrictions, at the `tmul`
spelling of `Stacks.AlgebraicGeometry.RestrictionSections.tensorSheafUnit_val_map`. -/
theorem tmul_restrict {A B : SheafOfModules.{u} (structureRingSheaf Z)}
    {U V : (Opens Z.carrier)ᵒᵖ} (g : U ⟶ V) (a : A.val.obj U) (b : B.val.obj U) :
    (A ⊗ B).val.map g (tmul Z A B U a b) = tmul Z A B V (A.val.map g a) (B.val.map g b) :=
  Stacks.AlgebraicGeometry.RestrictionSections.tensorSheafUnit_val_map A B g a b

/-- **Two morphisms out of a tensor product sheaf agreeing on the local pure tensors over the
opens of a basis are equal.** -/
theorem tensor_hom_ext_of_isBasis
    {A B Q : SheafOfModules.{u} (structureRingSheaf Z)} {φ ψ : A ⊗ B ⟶ Q}
    {𝔅 : Set (Opens Z.carrier)} (h𝔅 : Opens.IsBasis 𝔅)
    (h : ∀ V ∈ 𝔅, ∀ (a : A.val.obj (op V)) (b : B.val.obj (op V)),
      φ.val.app (op V) (tmul Z A B (op V) a b) = ψ.val.app (op V) (tmul Z A B (op V) a b)) :
    φ = ψ := by
  refine tensor_hom_ext fun U a b => ?_
  obtain ⟨U⟩ := U
  have hc : ∀ x : U, ∃ V ∈ 𝔅, (x : Z.carrier) ∈ V ∧ V ≤ U := fun x =>
    (Opens.isBasis_iff_nbhd.mp h𝔅) x.2
  choose W hW𝔅 hxW hWU using hc
  have key : ∀ (x : U) (θ : A ⊗ B ⟶ Q),
      Q.val.map (homOfLE (hWU x)).op (θ.val.app (op U) (tmul Z A B (op U) a b)) =
        θ.val.app (op (W x)) (tmul Z A B (op (W x)) (A.val.map (homOfLE (hWU x)).op a)
          (B.val.map (homOfLE (hWU x)).op b)) := fun x θ =>
    (PresheafOfModules.naturality_apply θ.val (homOfLE (hWU x)).op
      (tmul Z A B (op U) a b)).symm.trans
      (congrArg (θ.val.app (op (W x))) (tmul_restrict _ a b))
  exact TopCat.Sheaf.eq_of_locally_eq' ((SheafOfModules.toSheaf _).obj Q) W U
    (fun x => homOfLE (hWU x)) (fun x hx => Opens.mem_iSup.mpr ⟨⟨x, hx⟩, hxW _⟩) _ _
    fun x => (key x φ).trans ((h _ (hW𝔅 x) _ _).trans (key x ψ).symm)

/-- Two morphisms out of a tensor product sheaf agree on all local pure tensors `a ⊗ b` over `V`
with `b` fixed as soon as they agree for `a` in a generating set of the sections over `V`. -/
theorem tmul_eq_of_span
    {A B Q : SheafOfModules.{u} (structureRingSheaf Z)} (φ ψ : A ⊗ B ⟶ Q)
    (V : (Opens Z.carrier)ᵒᵖ) (S : Set (A.val.obj V))
    (hS : Submodule.span ((structureRingSheaf Z).obj.obj V) S = ⊤)
    (b : B.val.obj V)
    (h : ∀ a ∈ S, φ.val.app V (tmul Z A B V a b) = ψ.val.app V (tmul Z A B V a b))
    (a : A.val.obj V) :
    φ.val.app V (tmul Z A B V a b) = ψ.val.app V (tmul Z A B V a b) := by
  have ha : a ∈ Submodule.span ((structureRingSheaf Z).obj.obj V) S :=
    hS ▸ Submodule.mem_top
  have h0 : tmul Z A B V 0 b = 0 :=
    (congrArg ((PresheafOfModules.tensorSheafUnit A B).app V) (TensorProduct.zero_tmul _ b)).trans
      (map_zero _)
  have hadd : ∀ x y : A.val.obj V, tmul Z A B V (x + y) b = tmul Z A B V x b + tmul Z A B V y b :=
    fun x y => (congrArg ((PresheafOfModules.tensorSheafUnit A B).app V)
      (TensorProduct.add_tmul x y b)).trans (map_add _ _ _)
  have hsmul : ∀ (r : (structureRingSheaf Z).obj.obj V) (x : A.val.obj V),
      tmul Z A B V (r • x) b = r • tmul Z A B V x b :=
    fun r x => Stacks.RingedSpace.map_smul_tmul
      ((PresheafOfModules.tensorSheafUnit A B).app V).hom r x b
  induction ha using Submodule.span_induction with
  | mem x hx => exact h x hx
  | zero => rw [h0, map_zero, map_zero]
  | add x y _ _ hx hy => rw [hadd, map_add, map_add, hx, hy]
  | smul r x _ hx => rw [hsmul, map_smul, map_smul, hx]

/-- **Two morphisms out of a tensor product sheaf `A ⊗ B` are equal as soon as they agree on the
local pure tensors `a ⊗ b` over the opens `V` of a basis, for `a` in a generating set of the
sections of `A` over `V`.** -/
theorem tensor_hom_ext_of_isBasis_of_span
    {A B Q : SheafOfModules.{u} (structureRingSheaf Z)} {φ ψ : A ⊗ B ⟶ Q}
    {𝔅 : Set (Opens Z.carrier)} (h𝔅 : Opens.IsBasis 𝔅) (S : ∀ V : Opens Z.carrier,
      Set (A.val.obj (op V)))
    (hS : ∀ V ∈ 𝔅, Submodule.span ((structureRingSheaf Z).obj.obj (op V))
      (S V) = ⊤)
    (h : ∀ V ∈ 𝔅, ∀ a ∈ S V, ∀ b : B.val.obj (op V),
      φ.val.app (op V) (tmul Z A B (op V) a b) = ψ.val.app (op V) (tmul Z A B (op V) a b)) :
    φ = ψ :=
  tensor_hom_ext_of_isBasis h𝔅 fun V hV a b =>
    tmul_eq_of_span φ ψ (op V) (S V) (hS V hV) b (fun a ha => h V hV a ha b) a

end Stacks.PullbackTensorCoherence

namespace AlgebraicGeometry

attribute [local instance] Stacks.PullbackGradedAlgebra.monoidalCategory
  Stacks.AlgebraicGeometry.PullbackSectionMul.schemeTensorStrict

namespace Scheme.Hom

variable {X Y : Scheme.{u}} (f : Y ⟶ X)

/-- The graded algebra `f^*Ω^•_{X/ℤ}`: the pullback along `f` of the algebra of absolute
differential forms of `X`. -/
noncomputable abbrev pullbackFormsAlgebra :
    SheafOfModules.GradedAlgebra.{u, u} Y.ringCatSheaf :=
  Stacks.Conormal.gradedPullback f (absoluteDifferentialFormsAlgebra X)

/-- The sheaf `f^*Ω^n_{X/ℤ}` of pulled-back absolute differential `n`-forms. -/
noncomputable abbrev pullbackForms (n : ℤ) : Y.Modules :=
  (Scheme.Modules.pullback f).obj (absoluteDifferentialForms X n)

/-- The pieces of `f^*Ω^•_{X/ℤ}` are the sheaves `f^*Ω^n_{X/ℤ}`. -/
theorem pullbackFormsAlgebra_piece (n : ℤ) :
    (pullbackFormsAlgebra f).piece n = f.pullbackForms n :=
  rfl

/-- The sheaf `f^*Ω^n_{X/ℤ} ⊗_{𝒪_Y} L`, the target of the maps of Section 0FL7. -/
noncomputable abbrev twistedPullbackForms (L : Y.Modules) (n : ℤ) : Y.Modules :=
  f.pullbackForms n ⊗ L

/-- `f^*Ω^n_{X/ℤ} ⊗ L` is the tensor product sheaf. -/
theorem twistedPullbackForms_eq (L : Y.Modules) (n : ℤ) :
    f.twistedPullbackForms L n =
      ((Stacks.SheafOfModules.Tensor.sheafTensor Y.sheaf).obj (f.pullbackForms n)).obj L :=
  rfl

variable (L : Y.Modules)

/-- The local pure tensor `ω ⊗ t` of a local section `ω` of `f^*Ω^n_{X/ℤ}` and a local section
`t` of `L`. -/
noncomputable abbrev twistedPullbackFormsTmul (n : ℤ) (V : Y.Opens)
    (ω : (f.pullbackForms n).val.obj (op V)) (t : L.val.obj (op V)) :
    (f.twistedPullbackForms L n).val.obj (op V) :=
  tmul Y.toRingedSpace (f.pullbackForms n) L (op V) ω t

/-- Local pure tensors in `f^*Ω^n_{X/ℤ} ⊗ L` are the images of pure tensors under the unit of the
sheafification defining the tensor product sheaf. -/
theorem twistedPullbackFormsTmul_eq (n : ℤ) (V : Y.Opens) (ω : (f.pullbackForms n).val.obj (op V))
    (t : L.val.obj (op V)) :
    f.twistedPullbackFormsTmul L n V ω t =
      PresheafOfModules.Hom.app (PresheafOfModules.tensorSheafUnit (f.pullbackForms n) L) (op V)
        (ω ⊗ₜ t) :=
  rfl

/-- **The maps of Stacks Section 0FL7**: a family of `𝒪_Y`-linear maps
`c^p : Ω^p_{Y/ℤ} ⟶ f^*Ω^p_{X/ℤ} ⊗ L`, one for each `p ≥ 0`. -/
abbrev GarelMaps : Type u :=
  ∀ p : ℕ, absoluteDifferentialForms Y p ⟶ f.twistedPullbackForms L p

end Scheme.Hom

/-- The morphism `𝒪_Y ⟶ L` of a global section `δ` of `L`, carrying `1` to `δ`. -/
noncomputable def Scheme.Modules.globalSectionHom {Y : Scheme.{u}} (L : Y.Modules)
    (δ : Γ(L, ⊤)) : 𝟙_ Y.Modules ⟶ L :=
  L.unitHomEquiv.symm (Scheme.Modules.sectionsTopEquiv L δ)

namespace Scheme.Modules

variable {Y : Scheme.{u}}

/-- The morphism of a global section carries the global unit section to it. -/
theorem globalSectionHom_val_app_oneSec (L : Y.Modules) (δ : Γ(L, ⊤)) :
    (globalSectionHom L δ).val.app (op ⊤) (oneSec Y.toRingedSpace (op ⊤)) = δ := by
  have h : (globalSectionHom L δ).val.app (op ⊤) (oneSec Y.toRingedSpace (op ⊤)) =
      (1 : Y.ringCatSheaf.obj.obj (op ⊤)) • (sectionsTopEquiv L δ).eval (op ⊤) := rfl
  exact h.trans ((one_smul _ _).trans
    ((Stacks.SheafOfModules.FiniteTypeKernel.sectionsEquivOfTerminal L
      (Limits.isTerminalTop (α := Y.Opens))).apply_symm_apply δ))

/-- Two morphisms out of the structure sheaf agreeing on the global unit section are equal. -/
theorem unit_hom_ext {M : Y.Modules} {φ ψ : 𝟙_ Y.Modules ⟶ M}
    (h : φ.val.app (op ⊤) (oneSec Y.toRingedSpace (op ⊤)) =
      ψ.val.app (op ⊤) (oneSec Y.toRingedSpace (op ⊤))) : φ = ψ :=
  M.unitHomEquiv.injective ((sectionsTopEquiv M).symm.injective h)

end Scheme.Modules


namespace Scheme.Hom

variable {X Y : Scheme.{u}} (f : Y ⟶ X) {L : Y.Modules}

variable {f} in
/-- **Condition (0H9C) of Stacks Section 0FL7**: `c^0(1) = 1 ⊗ δ`, as an equation of morphisms
out of the structure sheaf. -/
def GarelMaps.IsNormalized (δ : Γ(L, ⊤)) (c : f.GarelMaps L) : Prop :=
  oneMorphism (absoluteDifferentialFormsAlgebra Y) ≫ c 0 =
    Scheme.Modules.globalSectionHom L δ ≫ (λ_ L).inv ≫
      (oneMorphism (pullbackFormsAlgebra f) ▷ L)

/-- The left action of `f^*Ω^q_{X/ℤ}` on `Ω^p_{Y/ℤ}`: the canonical map
`f^*Ω^q_{X/ℤ} ⟶ Ω^q_{Y/ℤ}` followed by the product of `Ω^•_{Y/ℤ}`, `ω ⊗ η ↦ ω ∧ η`. -/
noncomputable def absoluteFormsAction (q p : ℕ) :
    f.pullbackForms q ⊗ absoluteDifferentialForms Y p ⟶ absoluteDifferentialForms Y (q + p : ℕ) :=
  (f.absoluteFormsMap q ▷ absoluteDifferentialForms Y p) ≫
    mulHom (absoluteDifferentialFormsAlgebra Y) q p ≫
      eqToHom (congrArg (absoluteDifferentialForms Y) (Nat.cast_add q p).symm)

variable (L) in
/-- The left action of `f^*Ω^q_{X/ℤ}` on `f^*Ω^p_{X/ℤ} ⊗ L`: the product of `f^*Ω^•_{X/ℤ}`
tensored with the identity of `L`, `ω ⊗ (α ⊗ t) ↦ (ω ∧ α) ⊗ t`. -/
noncomputable def twistedPullbackFormsMul (q p : ℕ) :
    f.pullbackForms q ⊗ f.twistedPullbackForms L p ⟶ f.twistedPullbackForms L (q + p : ℕ) :=
  (α_ _ _ _).inv ≫ (mulHom (pullbackFormsAlgebra f) q p ▷ L) ≫
    eqToHom (congrArg (f.twistedPullbackForms L) (Nat.cast_add q p).symm)

variable {f} in
/-- **Condition (0H9D) of Stacks Section 0FL7**: `c^{q+p}(ω ∧ η) = ω ∧ c^p(η)`, as an equation
of morphisms out of `f^*Ω^q_{X/ℤ} ⊗ Ω^p_{Y/ℤ}`. -/
def GarelMaps.IsMultiplicative (c : f.GarelMaps L) : Prop :=
  ∀ q p : ℕ, absoluteFormsAction f q p ≫ c (q + p) =
    (f.pullbackForms q ◁ c p) ≫ twistedPullbackFormsMul f L q p

variable {f} in
/-- **Condition (0H9C) on global sections**: the unit of `Ω^•_{Y/ℤ}` is carried to `1 ⊗ δ`. -/
theorem GarelMaps.isNormalized_iff (δ : Γ(L, ⊤)) (c : f.GarelMaps L) :
    c.IsNormalized δ ↔
      (c 0).val.app (op ⊤) ((absoluteDifferentialFormsAlgebra Y).one.eval (op ⊤)) =
        f.twistedPullbackFormsTmul L 0 ⊤ ((pullbackFormsAlgebra f).one.eval (op ⊤)) δ := by
  have hL : (oneMorphism (absoluteDifferentialFormsAlgebra Y) ≫ c 0).val.app (op ⊤)
      (oneSec Y.toRingedSpace (op ⊤)) =
        (c 0).val.app (op ⊤) ((absoluteDifferentialFormsAlgebra Y).one.eval (op ⊤)) :=
    congrArg ((c 0).val.app (op ⊤)) (oneMorphism_val_app_oneSec _ (op ⊤))
  have hR : (Scheme.Modules.globalSectionHom L δ ≫ (λ_ L).inv ≫
      (oneMorphism (pullbackFormsAlgebra f) ▷ L)).val.app (op ⊤)
      (oneSec Y.toRingedSpace (op ⊤)) =
        f.twistedPullbackFormsTmul L 0 ⊤ ((pullbackFormsAlgebra f).one.eval (op ⊤)) δ := by
    refine (congrArg (fun x => (oneMorphism (pullbackFormsAlgebra f) ▷ L).val.app (op ⊤)
      ((λ_ L).inv.val.app (op ⊤) x)) (Scheme.Modules.globalSectionHom_val_app_oneSec L δ)).trans
      ?_
    refine (congrArg (fun x => (oneMorphism (pullbackFormsAlgebra f) ▷ L).val.app (op ⊤) x)
      (leftUnitor_inv_tmul (Z := Y.toRingedSpace) L (op ⊤) δ)).trans ?_
    refine (whiskerRight_tmul _ _ _ _).trans ?_
    exact congrArg (fun x => tmul Y.toRingedSpace (f.pullbackForms 0) L (op ⊤) x δ)
      (oneMorphism_val_app_oneSec _ (op ⊤))
  exact ⟨fun h => hL.symm.trans ((congrArg (fun φ => φ.val.app (op ⊤)
      (oneSec Y.toRingedSpace (op ⊤))) h).trans hR),
    fun h => Scheme.Modules.unit_hom_ext (hL.trans (h.trans hR.symm))⟩

/-- The action of `f^*Ω^q_{X/ℤ}` on `Ω^p_{Y/ℤ}` on a local pure tensor. -/
theorem absoluteFormsAction_tmul (q p : ℕ) (V : Y.Opens) (ω : (f.pullbackForms q).val.obj (op V))
    (η : (absoluteDifferentialForms Y p).val.obj (op V)) :
    (f.absoluteFormsAction q p).val.app (op V)
        (tmul Y.toRingedSpace (f.pullbackForms q) (absoluteDifferentialForms Y p) (op V) ω η) =
      (eqToHom (congrArg (absoluteDifferentialForms Y) (Nat.cast_add q p).symm)).val.app (op V)
        (((absoluteDifferentialFormsAlgebra Y).mul q p).app (op V)
          ((f.absoluteFormsMap q).val.app (op V) ω) η) := by
  have h1 : (f.absoluteFormsMap q ▷ absoluteDifferentialForms Y p).val.app (op V)
      (tmul Y.toRingedSpace (f.pullbackForms q) (absoluteDifferentialForms Y p) (op V) ω η) =
        tmul Y.toRingedSpace (absoluteDifferentialForms Y q) (absoluteDifferentialForms Y p)
          (op V) ((f.absoluteFormsMap q).val.app (op V) ω) η :=
    whiskerRight_tmul (Z := Y.toRingedSpace) (A := f.pullbackForms q)
      (A' := absoluteDifferentialForms Y q) (B := absoluteDifferentialForms Y p)
      (f.absoluteFormsMap q) (op V) ω η
  have h2 := mulHom_tmul (absoluteDifferentialFormsAlgebra Y) q p (op V)
    ((f.absoluteFormsMap q).val.app (op V) ω) η
  have h3 := (congrArg ((mulHom (absoluteDifferentialFormsAlgebra Y) q p).val.app (op V))
    h1).trans h2
  have h4 := congrArg ((eqToHom (congrArg (absoluteDifferentialForms Y)
    (Nat.cast_add q p).symm)).val.app (op V)) h3
  exact h4

variable (L) in
/-- The action of `f^*Ω^q_{X/ℤ}` on `f^*Ω^p_{X/ℤ} ⊗ L` on a local pure tensor. -/
theorem twistedPullbackFormsMul_tmul (q p : ℕ) (V : Y.Opens)
    (ω : (f.pullbackForms q).val.obj (op V)) (α : (f.pullbackForms p).val.obj (op V))
    (t : L.val.obj (op V)) :
    (f.twistedPullbackFormsMul L q p).val.app (op V)
        (tmul Y.toRingedSpace (f.pullbackForms q) (f.twistedPullbackForms L p) (op V) ω
          (f.twistedPullbackFormsTmul L p V α t)) =
      (eqToHom (congrArg (f.twistedPullbackForms L) (Nat.cast_add q p).symm)).val.app (op V)
        (f.twistedPullbackFormsTmul L (q + p) V
          (((pullbackFormsAlgebra f).mul q p).app (op V) ω α) t) := by
  have h1 : (α_ (f.pullbackForms q) (f.pullbackForms p) L).inv.val.app (op V)
      (tmul Y.toRingedSpace (f.pullbackForms q) (f.twistedPullbackForms L p) (op V) ω
          (f.twistedPullbackFormsTmul L p V α t)) =
        tmul Y.toRingedSpace (f.pullbackForms q ⊗ f.pullbackForms p) L (op V)
          (tmul Y.toRingedSpace (f.pullbackForms q) (f.pullbackForms p) (op V) ω α) t :=
    associator_inv_tmul (op V) ω α t
  have h2 : (mulHom (pullbackFormsAlgebra f) q p ▷ L).val.app (op V)
      (tmul Y.toRingedSpace (f.pullbackForms q ⊗ f.pullbackForms p) L (op V)
          (tmul Y.toRingedSpace (f.pullbackForms q) (f.pullbackForms p) (op V) ω α) t) =
        tmul Y.toRingedSpace (f.pullbackForms (q + p)) L (op V)
          ((mulHom (pullbackFormsAlgebra f) q p).val.app (op V)
            (tmul Y.toRingedSpace (f.pullbackForms q) (f.pullbackForms p) (op V) ω α)) t :=
    whiskerRight_tmul (mulHom (pullbackFormsAlgebra f) q p) (op V) _ t
  have h3 := mulHom_tmul (pullbackFormsAlgebra f) q p (op V) ω α
  have h4 := (congrArg ((mulHom (pullbackFormsAlgebra f) q p ▷ L).val.app (op V)) h1).trans
    (h2.trans (congrArg (fun x => tmul Y.toRingedSpace (f.pullbackForms (q + p)) L (op V)
      x t) h3))
  have h5 := congrArg ((eqToHom (congrArg (f.twistedPullbackForms L)
    (Nat.cast_add q p).symm)).val.app (op V)) h4
  exact h5

variable {f} in
/-- **Condition (0H9D) on local sections**: `c^{q+p}(ω ∧ η) = ω ∧ c^p(η)` for all local sections
`ω` of `f^*Ω^q_{X/ℤ}` and `η` of `Ω^p_{Y/ℤ}` over a common open. -/
theorem GarelMaps.isMultiplicative_iff (c : f.GarelMaps L) :
    c.IsMultiplicative ↔ ∀ (q p : ℕ) (V : Y.Opens) (ω : (f.pullbackForms q).val.obj (op V))
      (η : (absoluteDifferentialForms Y p).val.obj (op V)),
      (c (q + p)).val.app (op V) ((f.absoluteFormsAction q p).val.app (op V)
          (tmul Y.toRingedSpace (f.pullbackForms q) (absoluteDifferentialForms Y p) (op V) ω η)) =
        (f.twistedPullbackFormsMul L q p).val.app (op V)
          (tmul Y.toRingedSpace (f.pullbackForms q) (f.twistedPullbackForms L p) (op V) ω
            ((c p).val.app (op V) η)) := by
  refine ⟨fun h q p V ω η => ?_, fun h q p => ?_⟩
  · have h1 := congrArg (fun φ => φ.val.app (op V)
      (tmul Y.toRingedSpace (f.pullbackForms q) (absoluteDifferentialForms Y p) (op V) ω η))
      (h q p)
    exact h1.trans (congrArg ((f.twistedPullbackFormsMul L q p).val.app (op V))
      (whiskerLeft_tmul (c p) (op V) ω η))
  · refine tensor_hom_ext (Z := Y.toRingedSpace) (A := f.pullbackForms q)
      (B := absoluteDifferentialForms Y p) (Q := f.twistedPullbackForms L (q + p : ℕ))
      (φ := f.absoluteFormsAction q p ≫ c (q + p))
      (ψ := (f.pullbackForms q ◁ c p) ≫ f.twistedPullbackFormsMul L q p) fun V ω η => ?_
    exact (h q p V.unop ω η).trans
      (congrArg ((f.twistedPullbackFormsMul L q p).val.app V) (whiskerLeft_tmul (c p) V ω η).symm)

variable {f} in
/-- **Condition (0H9D) is local and may be checked on generators**: it suffices that
`c^{q+p}(ω ∧ η) = ω ∧ c^p(η)` over the opens `V` of a basis, for `ω` in a set generating the
sections of `f^*Ω^q_{X/ℤ}` over `V` as a `Γ(Y, V)`-module and arbitrary `η`. -/
theorem GarelMaps.isMultiplicative_of_isBasis (c : f.GarelMaps L) {𝔅 : Set Y.Opens}
    (h𝔅 : Opens.IsBasis 𝔅) (S : ∀ (q : ℕ) (V : Y.Opens), Set ((f.pullbackForms q).val.obj (op V)))
    (hS : ∀ q : ℕ, ∀ V ∈ 𝔅, Submodule.span (Y.ringCatSheaf.obj.obj (op V)) (S q V) = ⊤)
    (h : ∀ (q p : ℕ), ∀ V ∈ 𝔅, ∀ ω ∈ S q V, ∀ η : (absoluteDifferentialForms Y p).val.obj (op V),
      (c (q + p)).val.app (op V) ((f.absoluteFormsAction q p).val.app (op V)
          (tmul Y.toRingedSpace (f.pullbackForms q) (absoluteDifferentialForms Y p) (op V) ω η)) =
        (f.twistedPullbackFormsMul L q p).val.app (op V)
          (tmul Y.toRingedSpace (f.pullbackForms q) (f.twistedPullbackForms L p) (op V) ω
            ((c p).val.app (op V) η))) :
    c.IsMultiplicative := by
  intro q p
  refine tensor_hom_ext_of_isBasis_of_span (Z := Y.toRingedSpace)
    (A := f.pullbackForms q)
    (B := absoluteDifferentialForms Y p) (Q := f.twistedPullbackForms L (q + p : ℕ))
    (φ := f.absoluteFormsAction q p ≫ c (q + p))
    (ψ := (f.pullbackForms q ◁ c p) ≫ f.twistedPullbackFormsMul L q p) h𝔅 (S q) (hS q)
    fun V hV a ha η => ?_
  refine Eq.trans ?_ ((h q p V hV a ha η).trans ?_)
  · rfl
  · exact congrArg ((f.twistedPullbackFormsMul L q p).val.app (op V))
      (whiskerLeft_tmul (c p) (op V) a η).symm

end Scheme.Hom

end AlgebraicGeometry
