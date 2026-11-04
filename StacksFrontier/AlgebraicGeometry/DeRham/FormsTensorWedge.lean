module

public import StacksFrontier.AlgebraicGeometry.DeRham.StructureSheafTwistedDifferential
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackTensorComparisonBraided
public import StacksFrontier.AlgebraicGeometry.DeRham.CupProduct.GradedCommutativity
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedAlgebraFunctoriality
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorPowerDegreeOne

/-!
# Wedging differential forms into `Ω^•_{Y/S} ⊗ ℱ`, and the switch to `ℱ ⊗ Ω^•_{Y/S}`

Let `g : Y ⟶ S` be a morphism of schemes and `ℱ` a sheaf of `𝒪_Y`-modules.  The first page of
the spectral sequence of [Stacks, Tag 0FMM] in the flat case of [Stacks, Tag 0FMN] is
`Ω^p_{Y/S} ⊗_{𝒪_Y} ℋ^q_dR(X/Y)`, with the forms on the *left*, and its differentials are
compatible with the left action of the algebra `Ω^•_{Y/S}` of relative differential forms.  The
twisted de Rham complex `AlgebraicGeometry.Scheme.Hom.twistedDeRhamComplex` of a connection on
`ℱ`, on the other hand, has the module on the left: its terms are `ℱ ⊗ Ω^q_{Y/S}`.  This file
supplies the sheaf-level operations that pass between the two:

* the **wedge pairing** `Ω^p_{Y/S} ⊗ (Ω^{p'}_{Y/S} ⊗ ℱ) ⟶ Ω^{p+p'}_{Y/S} ⊗ ℱ`,
  `ω ⊗ (η ⊗ s) ↦ (ω ∧ η) ⊗ s`, as a morphism of sheaves of `𝒪_Y`-modules out of the sheafified
  tensor product, together with its section-level form;
* the **twisted wedge pairing** `(ℱ ⊗ Ω_{Y/S}) ⊗ Ω^q_{Y/S} ⟶ ℱ ⊗ Ω^{q+1}_{Y/S}`,
  `(s ⊗ α) ⊗ ω ↦ s ⊗ (α ∧ ω)`, which is the pairing the Leibniz rule of
  `AlgebraicGeometry.Scheme.Hom.TwistedDeRhamDifferential` refers to;
* the **switch** `Ω^1_{Y/S} ⊗ ℱ ≅ ℱ ⊗ Ω_{Y/S}`, the symmetry constraint of the tensor product
  followed by the inverse of the degree-one generator `Ω_{Y/S} ⟶ Ω^1_{Y/S}`;
* the **sign rule** relating the two pairings across the symmetry constraint:
  `ω ∧ y` read in `ℱ ⊗ Ω^{q+1}` is `(-1)^q` times the twisted wedge of the switched `y` with `ω`,
  for `ω` a `q`-form and `y` a section of `Ω^1 ⊗ ℱ` (graded commutativity of `Ω^•_{Y/S}`).

## Main definitions

Everything lives in the namespace `AlgebraicGeometry.Scheme.Hom`.

* `formsTensor` — `Ω^p_{Y/S} ⊗_{𝒪_Y} ℱ`, and `formsTensorTmul` the class of a local pure tensor.
* `formsTensorWedge` / `formsTensorWedgeSection` — the wedge pairing, as a morphism and on local
  sections.
* `twistedFormsWedge` — the twisted wedge pairing.
* `relativeExteriorProductHom` — `Ω_{Y/S} ⊗ Ω^q_{Y/S} ⟶ Ω^{q+1}_{Y/S}`, the morphism form of
  `AlgebraicGeometry.Scheme.Hom.relativeExteriorProduct`.
* `formsTensorConnectionIso` — the switch `Ω^1_{Y/S} ⊗ ℱ ≅ ℱ ⊗ Ω_{Y/S}`.
* `formsTensorSuccIso` — the renaming `Ω^{q+1} ⊗ ℱ` between the degree `q + 1` computed in `ℤ`
  and in `ℕ`.

## Main results

* `formsTensorWedgeSection_tmul` — on a pure tensor the wedge pairing is the exterior product.
* `formsTensorWedgeSection_one` — the unit `1 ∈ Ω^0_{Y/S}` acts as the identity.
* `twistedFormsWedge_tmul` — on a pure tensor the twisted wedge pairing is
  `AlgebraicGeometry.Scheme.Hom.relativeExteriorProduct`.
* `zsmul_formsTensorWedge_comp_braiding` — **the sign rule**, as an equation of morphisms out of
  `Ω^q ⊗ (Ω^1 ⊗ ℱ)`, and `braiding_formsTensorWedgeSection` its form on local sections.

## Implementation notes

All tensor products are `Stacks.SheafOfModules.Tensor.sheafTensor`, the sheafified tensor
product of [Stacks, Tag 01CA], at the monoidal spelling
`Stacks.PullbackGradedAlgebra.monoidalCategory` with the symmetry constraint
`Stacks.PullbackTensorCoherence.braidedCategory`; local pure tensors are
`Stacks.PullbackTensorCoherence.tmul`.  These are, by `rfl`, the tensor products and the pure
tensors `twistedTmul` and `connectionTmul` of
`StacksFrontier.AlgebraicGeometry.DeRham.ModuleConnection` and the module
`Stacks.DeRhamSmooth.deRhamFirstPageFlat` of
`StacksFrontier.AlgebraicGeometry.DeRham.SmoothCohomologySheaves`.  The objects entering a monoidal
constraint are produced by abbreviations whose declared type is the ring-sheaf spelling
`SheafOfModules (Stacks.RingedSpace.structureRingSheaf Y.toRingedSpace)`, since
`AlgebraicGeometry.Scheme.Modules` is a `def` and instance search does not see the monoidal
structure through it.

No tag attribute is carried here: these are tools for [Stacks, Tag 0FMN], whose registration lives
with the remark itself.

## References

* [Stacks Project, Tag 0FMN](https://stacks.math.columbia.edu/tag/0FMN)
* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA)
* [Stacks Project, Tag 07I0](https://stacks.math.columbia.edu/tag/07I0)
-/

@[expose] public section

open CategoryTheory MonoidalCategory TopologicalSpace Opposite
open Stacks.PullbackTensorCoherence (tmul)

universe u

noncomputable section

namespace AlgebraicGeometry.Scheme.Hom

attribute [local instance] Stacks.PullbackGradedAlgebra.monoidalCategory
  Stacks.PullbackTensorCoherence.braidedCategory

variable {Y S : Scheme.{u}} (g : Y ⟶ S) (H : Y.Modules)

/-! ### Local pure tensors -/

section Tmul

variable {Z : RingedSpace.{u, u}}
  {A B : SheafOfModules.{u} (Stacks.RingedSpace.structureRingSheaf Z)}
  (U : (TopologicalSpace.Opens Z.carrier)ᵒᵖ)

private theorem tmul_add_right (a : A.val.obj U) (b b' : B.val.obj U) :
    tmul Z A B U a (b + b') = tmul Z A B U a b + tmul Z A B U a b' := by
  unfold Stacks.PullbackTensorCoherence.tmul
  rw [TensorProduct.tmul_add]
  exact map_add _ _ _

private theorem tmul_add_left (a a' : A.val.obj U) (b : B.val.obj U) :
    tmul Z A B U (a + a') b = tmul Z A B U a b + tmul Z A B U a' b := by
  unfold Stacks.PullbackTensorCoherence.tmul
  rw [TensorProduct.add_tmul]
  exact map_add _ _ _

private theorem tmul_smul_left (r : (Stacks.RingedSpace.structureRingSheaf Z).obj.obj U)
    (a : A.val.obj U) (b : B.val.obj U) :
    tmul Z A B U (r • a) b = r • tmul Z A B U a b := by
  unfold Stacks.PullbackTensorCoherence.tmul
  rw [← TensorProduct.smul_tmul']
  exact map_smul _ _ _

private theorem tmul_smul_right (r : (Stacks.RingedSpace.structureRingSheaf Z).obj.obj U)
    (a : A.val.obj U) (b : B.val.obj U) :
    tmul Z A B U a (r • b) = r • tmul Z A B U a b := by
  unfold Stacks.PullbackTensorCoherence.tmul
  rw [TensorProduct.tmul_smul]
  exact map_smul _ _ _

private theorem tmul_zsmul_right (n : ℤ) (a : A.val.obj U) (b : B.val.obj U) :
    tmul Z A B U a (n • b) = n • tmul Z A B U a b := by
  unfold Stacks.PullbackTensorCoherence.tmul
  rw [show a ⊗ₜ (n • b) = n • (a ⊗ₜ b) from map_zsmul (TensorProduct.mk _ _ _ a) n b]
  exact map_zsmul _ _ _

private theorem tmul_restrict {V : (TopologicalSpace.Opens Z.carrier)ᵒᵖ} (k : U ⟶ V)
    (a : A.val.obj U) (b : B.val.obj U) :
    (A ⊗ B).val.map k (tmul Z A B U a b) = tmul Z A B V (A.val.map k a) (B.val.map k b) :=
  (PresheafOfModules.naturality_apply
    (Stacks.SheafOfModules.TensorStalkRingedSpace.sheafifyUnit Z
      (PresheafOfModules.tensorObj A.val B.val)) k (a ⊗ₜ b)).symm

private theorem leftUnitor_inv_app
    (M : SheafOfModules.{u} (Stacks.RingedSpace.structureRingSheaf Z)) (x : M.val.obj U) :
    (λ_ M).inv.val.app U x =
      tmul Z (𝟙_ (SheafOfModules.{u} (Stacks.RingedSpace.structureRingSheaf Z))) M U
        (Stacks.PullbackTensorCoherence.oneSec Z U) x := by
  have h : (λ_ M).hom.val.app U
      (tmul Z (𝟙_ (SheafOfModules.{u} (Stacks.RingedSpace.structureRingSheaf Z))) M U
        (Stacks.PullbackTensorCoherence.oneSec Z U) x) = x :=
    (Stacks.PullbackTensorCoherence.leftUnitor_hom_tmul U 1 x).trans (one_smul _ _)
  exact (congrArg _ h.symm).trans (Stacks.SheafOfModules.inv_val_app_hom_val_app (λ_ M) U _)

private theorem eqToHom_app_heq {ι : Type*} (F : ι → SheafOfModules.{u}
    (Stacks.RingedSpace.structureRingSheaf Z)) {i j : ι} (e : i = j) (x : (F i).val.obj U) :
    HEq ((eqToHom (congrArg F e)).val.app U x) x := by
  subst e
  rfl

end Tmul

/-! ### The sheaves, at the ring-sheaf spelling -/

/-- `Ω^p_{Y/S}`, at the spelling of sheaves of modules over
`Stacks.RingedSpace.structureRingSheaf`, which is where the monoidal structure is found. -/
abbrev formsOnRing (p : ℤ) :
    SheafOfModules.{u} (Stacks.RingedSpace.structureRingSheaf Y.toRingedSpace) :=
  relativeDifferentialForms g p

/-- `Ω_{Y/S}`, at the ring-sheaf spelling. -/
abbrev differentialsOnRing :
    SheafOfModules.{u} (Stacks.RingedSpace.structureRingSheaf Y.toRingedSpace) :=
  relativeDifferentials g

/-- A sheaf of `𝒪_Y`-modules, at the ring-sheaf spelling. -/
abbrev modulesOnRing :
    SheafOfModules.{u} (Stacks.RingedSpace.structureRingSheaf Y.toRingedSpace) :=
  H

/-- **`Ω^p_{Y/S} ⊗_{𝒪_Y} ℱ`**, the sheafified tensor product with the forms on the left.  For
`ℱ = ℋ^q_dR(X/Y)` this is the first page of [Stacks, Tag 0FMN] in the flat case, before
restriction of scalars. -/
abbrev formsTensor (p : ℤ) :
    SheafOfModules.{u} (Stacks.RingedSpace.structureRingSheaf Y.toRingedSpace) :=
  formsOnRing g p ⊗ modulesOnRing H

/-- The class in `(Ω^p_{Y/S} ⊗ ℱ)(U)` of the local pure tensor `ω ⊗ s`. -/
abbrev formsTensorTmul (p : ℤ) (U : (Y.Opens)ᵒᵖ)
    (ω : (relativeDifferentialForms g p).val.obj U) (s : H.val.obj U) :
    (formsTensor g H p).val.obj U :=
  tmul Y.toRingedSpace (formsOnRing g p) (modulesOnRing H) U ω s

/-- The class of a local pure tensor is additive in the section of `ℱ`. -/
theorem formsTensorTmul_add_right (p : ℤ) (U : (Y.Opens)ᵒᵖ)
    (ω : (relativeDifferentialForms g p).val.obj U) (s s' : H.val.obj U) :
    formsTensorTmul g H p U ω (s + s') =
      formsTensorTmul g H p U ω s + formsTensorTmul g H p U ω s' :=
  tmul_add_right U ω s s'

/-- The class of a local pure tensor is additive in the form. -/
theorem formsTensorTmul_add_left (p : ℤ) (U : (Y.Opens)ᵒᵖ)
    (ω ω' : (relativeDifferentialForms g p).val.obj U) (s : H.val.obj U) :
    formsTensorTmul g H p U (ω + ω') s =
      formsTensorTmul g H p U ω s + formsTensorTmul g H p U ω' s :=
  tmul_add_left U ω ω' s

/-- A local function may be moved across the tensor sign of a local pure tensor. -/
theorem formsTensorTmul_smul_left (p : ℤ) (U : (Y.Opens)ᵒᵖ)
    (r : (Stacks.RingedSpace.structureRingSheaf Y.toRingedSpace).obj.obj U)
    (ω : (formsOnRing g p).val.obj U) (s : (modulesOnRing H).val.obj U) :
    formsTensorTmul g H p U (r • ω) s = formsTensorTmul g H p U ω (r • s) := by
  unfold formsTensorTmul Stacks.PullbackTensorCoherence.tmul
  rw [TensorProduct.smul_tmul]

/-- The class of a local pure tensor is linear over `𝒪_Y` in the form. -/
theorem formsTensorTmul_smul (p : ℤ) (U : (Y.Opens)ᵒᵖ)
    (r : (Stacks.RingedSpace.structureRingSheaf Y.toRingedSpace).obj.obj U)
    (ω : (formsOnRing g p).val.obj U) (s : (modulesOnRing H).val.obj U) :
    formsTensorTmul g H p U (r • ω) s = r • formsTensorTmul g H p U ω s :=
  tmul_smul_left U r ω s

/-- Restricting a local pure tensor restricts its two factors. -/
theorem formsTensorTmul_restrict (p : ℤ) {U V : (Y.Opens)ᵒᵖ} (k : U ⟶ V)
    (ω : (relativeDifferentialForms g p).val.obj U) (s : H.val.obj U) :
    (formsTensor g H p).val.map k (formsTensorTmul g H p U ω s) =
      formsTensorTmul g H p V ((relativeDifferentialForms g p).val.map k ω) (H.val.map k s) :=
  tmul_restrict U k ω s

/-- Pure tensors whose form factors are heterogeneously equal across an equality of degrees are
heterogeneously equal. -/
theorem formsTensorTmul_heq {p₁ p₂ : ℤ} (e : p₁ = p₂) (U : (Y.Opens)ᵒᵖ)
    (x : (relativeDifferentialForms g p₁).val.obj U)
    (y : (relativeDifferentialForms g p₂).val.obj U) (h : HEq x y) (s : H.val.obj U) :
    HEq (formsTensorTmul g H p₁ U x s) (formsTensorTmul g H p₂ U y s) := by
  subst e
  rw [eq_of_heq h]

/-! ### The wedge pairing `Ω^p ⊗ (Ω^{p'} ⊗ ℱ) ⟶ Ω^{p+p'} ⊗ ℱ` -/

/-- **The wedge pairing** `Ω^p_{Y/S} ⊗ (Ω^{p'}_{Y/S} ⊗ ℱ) ⟶ Ω^{p+p'}_{Y/S} ⊗ ℱ`: reassociate,
then multiply the two forms in the algebra `Ω^•_{Y/S}`. -/
def formsTensorWedge (p p' : ℤ) :
    formsOnRing g p ⊗ formsTensor g H p' ⟶ formsTensor g H (p + p') :=
  (α_ (formsOnRing g p) (formsOnRing g p') (modulesOnRing H)).inv ≫
    Stacks.PullbackTensorCoherence.mulHom (relativeDifferentialFormsAlgebra g) p p' ▷
      modulesOnRing H

/-- The wedge `ω ∧ x ∈ (Ω^{p+p'} ⊗ ℱ)(U)` of a local `p`-form with a local section of
`Ω^{p'} ⊗ ℱ`. -/
def formsTensorWedgeSection (p p' : ℤ) (U : (Y.Opens)ᵒᵖ)
    (ω : (relativeDifferentialForms g p).val.obj U) (x : (formsTensor g H p').val.obj U) :
    (formsTensor g H (p + p')).val.obj U :=
  (formsTensorWedge g H p p').val.app U
    (tmul Y.toRingedSpace (formsOnRing g p) (formsTensor g H p') U ω x)

/-- **On a pure tensor the wedge pairing is the exterior product**:
`ω ∧ (η ⊗ s) = (ω ∧ η) ⊗ s`. -/
theorem formsTensorWedgeSection_tmul (p p' : ℤ) (U : (Y.Opens)ᵒᵖ)
    (ω : (relativeDifferentialForms g p).val.obj U)
    (η : (relativeDifferentialForms g p').val.obj U) (s : H.val.obj U) :
    formsTensorWedgeSection g H p p' U ω (formsTensorTmul g H p' U η s) =
      formsTensorTmul g H (p + p') U ((relativeDifferentialFormsAlgebra g).mul p p' |>.app U ω η)
        s := by
  have h₁ := Stacks.PullbackTensorCoherence.associator_hom_tmul (Z := Y.toRingedSpace)
    (A := formsOnRing g p) (B := formsOnRing g p') (D := modulesOnRing H) U ω η s
  have h₂ := Stacks.SheafOfModules.inv_val_app_hom_val_app
    (α_ (formsOnRing g p) (formsOnRing g p') (modulesOnRing H)) U
    (tmul Y.toRingedSpace _ (modulesOnRing H) U
      (tmul Y.toRingedSpace (formsOnRing g p) (formsOnRing g p') U ω η) s)
  rw [h₁] at h₂
  unfold formsTensorWedgeSection formsTensorWedge
  rw [SheafOfModules.comp_val_app_apply, h₂, Stacks.PullbackTensorCoherence.whiskerRight_tmul,
    Stacks.PullbackTensorCoherence.mulHom_tmul]

/-- `formsTensorWedgeSection_tmul`, read on the wedge pairing as a morphism. -/
theorem formsTensorWedge_tmul (p p' : ℤ) (U : (Y.Opens)ᵒᵖ)
    (ω : (relativeDifferentialForms g p).val.obj U)
    (η : (relativeDifferentialForms g p').val.obj U) (s : H.val.obj U) :
    (formsTensorWedge g H p p').val.app U
        (tmul Y.toRingedSpace (formsOnRing g p) (formsTensor g H p') U ω
          (formsTensorTmul g H p' U η s)) =
      formsTensorTmul g H (p + p') U ((relativeDifferentialFormsAlgebra g).mul p p' |>.app U ω η)
        s :=
  formsTensorWedgeSection_tmul g H p p' U ω η s

/-- The wedge pairing is additive in the section of `Ω^{p'} ⊗ ℱ`. -/
theorem formsTensorWedgeSection_add_right (p p' : ℤ) (U : (Y.Opens)ᵒᵖ)
    (ω : (relativeDifferentialForms g p).val.obj U) (x x' : (formsTensor g H p').val.obj U) :
    formsTensorWedgeSection g H p p' U ω (x + x') =
      formsTensorWedgeSection g H p p' U ω x + formsTensorWedgeSection g H p p' U ω x' := by
  unfold formsTensorWedgeSection
  rw [tmul_add_right]
  exact map_add _ _ _

/-- The wedge pairing is additive in the form. -/
theorem formsTensorWedgeSection_add_left (p p' : ℤ) (U : (Y.Opens)ᵒᵖ)
    (ω ω' : (relativeDifferentialForms g p).val.obj U) (x : (formsTensor g H p').val.obj U) :
    formsTensorWedgeSection g H p p' U (ω + ω') x =
      formsTensorWedgeSection g H p p' U ω x + formsTensorWedgeSection g H p p' U ω' x := by
  unfold formsTensorWedgeSection
  rw [tmul_add_left]
  exact map_add _ _ _

/-- The wedge pairing is linear over `𝒪_Y` in the form. -/
theorem formsTensorWedgeSection_smul_left (p p' : ℤ) (U : (Y.Opens)ᵒᵖ)
    (r : (Stacks.RingedSpace.structureRingSheaf Y.toRingedSpace).obj.obj U)
    (ω : (formsOnRing g p).val.obj U) (x : (formsTensor g H p').val.obj U) :
    formsTensorWedgeSection g H p p' U (r • ω) x = r • formsTensorWedgeSection g H p p' U ω x := by
  unfold formsTensorWedgeSection
  rw [tmul_smul_left]
  exact map_smul _ _ _

/-- The wedge pairing commutes with restriction to a smaller open. -/
theorem formsTensorWedgeSection_restrict (p p' : ℤ) {U V : (Y.Opens)ᵒᵖ} (k : U ⟶ V)
    (ω : (relativeDifferentialForms g p).val.obj U) (x : (formsTensor g H p').val.obj U) :
    (formsTensor g H (p + p')).val.map k (formsTensorWedgeSection g H p p' U ω x) =
      formsTensorWedgeSection g H p p' V ((relativeDifferentialForms g p).val.map k ω)
        ((formsTensor g H p').val.map k x) :=
  (PresheafOfModules.naturality_apply (formsTensorWedge g H p p').val k _).symm.trans
    (congrArg _ (tmul_restrict U k ω x))

/-- The class of `1 ⊗ s` in `Ω^0_{Y/S} ⊗ ℱ`, for the unit `1` of `Ω^•_{Y/S}`. -/
abbrev formsTensorUnitTmul (U : (Y.Opens)ᵒᵖ) (s : H.val.obj U) : (formsTensor g H 0).val.obj U :=
  formsTensorTmul g H 0 U ((relativeDifferentialFormsAlgebra g).one.eval U) s

/-- **The unit `1 ∈ Ω^0_{Y/S}` acts as the identity**: `1 ∧ x = x` for every local section `x`
of `Ω^p ⊗ ℱ`, not only for pure tensors. -/
theorem formsTensorWedgeSection_one (p : ℤ) (U : (Y.Opens)ᵒᵖ)
    (x : (formsTensor g H p).val.obj U) :
    HEq (formsTensorWedgeSection g H 0 p U ((relativeDifferentialFormsAlgebra g).one.eval U) x)
      x := by
  have hexp (U : (Y.Opens)ᵒᵖ) (x : (formsTensor g H p).val.obj U) :
      ((λ_ (formsTensor g H p)).inv ≫
        Stacks.PullbackTensorCoherence.oneMorphism (relativeDifferentialFormsAlgebra g) ▷
          formsTensor g H p ≫ formsTensorWedge g H 0 p ≫
            eqToHom (congrArg (formsTensor g H) (zero_add p))).val.app U x =
        (eqToHom (congrArg (formsTensor g H) (zero_add p))).val.app U
          (formsTensorWedgeSection g H 0 p U ((relativeDifferentialFormsAlgebra g).one.eval U)
            x) := by
    rw [SheafOfModules.comp_val_app_apply, SheafOfModules.comp_val_app_apply,
      SheafOfModules.comp_val_app_apply, leftUnitor_inv_app,
      Stacks.PullbackTensorCoherence.whiskerRight_tmul,
      Stacks.PullbackTensorCoherence.oneMorphism_val_app_oneSec]
    rfl
  have key : (λ_ (formsTensor g H p)).inv ≫
      Stacks.PullbackTensorCoherence.oneMorphism (relativeDifferentialFormsAlgebra g) ▷
        formsTensor g H p ≫ formsTensorWedge g H 0 p ≫
          eqToHom (congrArg (formsTensor g H) (zero_add p)) = 𝟙 _ := by
    refine Stacks.PullbackTensorCoherence.tensor_hom_ext fun U a s => ?_
    rw [hexp]
    refine eq_of_heq ((eqToHom_app_heq U (formsTensor g H) (zero_add p) _).trans ?_)
    refine HEq.trans (heq_of_eq (formsTensorWedgeSection_tmul g H 0 p U _ a s)) ?_
    exact formsTensorTmul_heq g H (zero_add p) U _ a
      ((relativeDifferentialFormsAlgebra g).one_mul p U a) s
  have hx := congrArg (fun φ => φ.val.app U x) key
  rw [hexp] at hx
  exact (eqToHom_app_heq U (formsTensor g H) (zero_add p) _).symm.trans (heq_of_eq hx)

/-! ### The twisted wedge pairing `(ℱ ⊗ Ω_{Y/S}) ⊗ Ω^q ⟶ ℱ ⊗ Ω^{q+1}` -/

/-- Transport along an equality of degrees, read through `eqToHom`, is
`AlgebraicGeometry.Scheme.Hom.transportDifferentialForm`. -/
theorem eqToHom_val_app_relativeDifferentialForms {i j : ℤ} (e : i = j) (U : (Y.Opens)ᵒᵖ)
    (x : (relativeDifferentialForms g i).val.obj U) :
    (eqToHom (congrArg (relativeDifferentialFormsAlgebra g).piece e)).val.app U x =
      transportDifferentialForm g e U x := by
  subst e
  rfl

/-- The degree-one generator `Ω_{Y/S} ⟶ Ω^1_{Y/S}`, at the ring-sheaf spelling. -/
abbrev exteriorGeneratorOnRing : differentialsOnRing g ⟶ formsOnRing g 1 :=
  Scheme.Modules.exteriorGenerator (relativeDifferentials g)

/-- The exterior product `Ω_{Y/S} ⊗ Ω^q_{Y/S} ⟶ Ω^{q+1}_{Y/S}`, `α ⊗ ω ↦ α ∧ ω`, of a relative
differential with a relative `q`-form: the morphism form of
`AlgebraicGeometry.Scheme.Hom.relativeExteriorProduct`. -/
def relativeExteriorProductHom (q : ℕ) :
    differentialsOnRing g ⊗ formsOnRing g q ⟶ formsOnRing g ((q + 1 : ℕ) : ℤ) :=
  exteriorGeneratorOnRing g ▷ formsOnRing g q ≫
    Stacks.PullbackTensorCoherence.mulHom (relativeDifferentialFormsAlgebra g) 1 q ≫
      eqToHom (congrArg (relativeDifferentialFormsAlgebra g).piece
        (show (1 : ℤ) + (q : ℤ) = ((q + 1 : ℕ) : ℤ) by push_cast; ring))

/-- On a local pure tensor the exterior product morphism is
`AlgebraicGeometry.Scheme.Hom.relativeExteriorProduct`. -/
theorem relativeExteriorProductHom_tmul (q : ℕ) (U : (Y.Opens)ᵒᵖ)
    (α : (relativeDifferentials g).val.obj U)
    (ω : (relativeDifferentialForms g (q : ℤ)).val.obj U) :
    (relativeExteriorProductHom g q).val.app U
        (tmul Y.toRingedSpace (differentialsOnRing g) (formsOnRing g q) U α ω) =
      relativeExteriorProduct g q U α ω := by
  unfold relativeExteriorProductHom
  rw [SheafOfModules.comp_val_app_apply, SheafOfModules.comp_val_app_apply,
    Stacks.PullbackTensorCoherence.whiskerRight_tmul,
    Stacks.PullbackTensorCoherence.mulHom_tmul]
  exact eqToHom_val_app_relativeDifferentialForms g _ U _

/-- **The twisted wedge pairing** `(ℱ ⊗ Ω_{Y/S}) ⊗ Ω^q_{Y/S} ⟶ ℱ ⊗ Ω^{q+1}_{Y/S}`,
`(s ⊗ α) ⊗ ω ↦ s ⊗ (α ∧ ω)`: reassociate, send `α` to `Ω^1_{Y/S}` by the degree-one generator,
and multiply in `Ω^•_{Y/S}`.  This is the pairing `∇(s) ∧ ω` of the Leibniz rule of
`AlgebraicGeometry.Scheme.Hom.TwistedDeRhamDifferential`, constructed for every `ℱ`. -/
def twistedFormsWedge (q : ℕ) :
    (modulesOnRing H ⊗ differentialsOnRing g) ⊗ formsOnRing g q ⟶
      modulesOnRing H ⊗ formsOnRing g ((q + 1 : ℕ) : ℤ) :=
  (α_ (modulesOnRing H) (differentialsOnRing g) (formsOnRing g q)).hom ≫
    modulesOnRing H ◁ relativeExteriorProductHom g q

/-- The twisted wedge `η ∧ ω ∈ (ℱ ⊗ Ω^{q+1})(U)` of a local section `η` of `ℱ ⊗ Ω_{Y/S}` with a
local `q`-form. -/
def twistedFormsWedgeSection (q : ℕ) (U : (Y.Opens)ᵒᵖ)
    (η : (moduleConnectionTarget g H).val.obj U)
    (ω : (relativeDifferentialForms g (q : ℤ)).val.obj U) :
    (twistedForms g H (q + 1)).val.obj U :=
  (twistedFormsWedge g H q).val.app U
    (tmul Y.toRingedSpace (modulesOnRing H ⊗ differentialsOnRing g) (formsOnRing g q) U η ω)

/-- The twisted wedge pairing is additive in the section of `ℱ ⊗ Ω_{Y/S}`. -/
theorem twistedFormsWedgeSection_add (q : ℕ) (U : (Y.Opens)ᵒᵖ)
    (η η' : (moduleConnectionTarget g H).val.obj U)
    (ω : (relativeDifferentialForms g (q : ℤ)).val.obj U) :
    twistedFormsWedgeSection g H q U (η + η') ω =
      twistedFormsWedgeSection g H q U η ω + twistedFormsWedgeSection g H q U η' ω :=
  (congrArg _ (tmul_add_left U η η' ω)).trans (map_add _ _ _)

/-- The twisted wedge pairing commutes with restriction to a smaller open. -/
theorem twistedFormsWedgeSection_restrict (q : ℕ) {U V : (Y.Opens)ᵒᵖ} (k : U ⟶ V)
    (η : (moduleConnectionTarget g H).val.obj U)
    (ω : (relativeDifferentialForms g (q : ℤ)).val.obj U) :
    (twistedForms g H (q + 1)).val.map k (twistedFormsWedgeSection g H q U η ω) =
      twistedFormsWedgeSection g H q V ((moduleConnectionTarget g H).val.map k η)
        ((relativeDifferentialForms g (q : ℤ)).val.map k ω) :=
  (PresheafOfModules.naturality_apply (twistedFormsWedge g H q).val k _).symm.trans
    (congrArg _ (tmul_restrict U k η ω))

/-- **On a pure tensor the twisted wedge pairing is the exterior product**:
`(s ⊗ α) ∧ ω = s ⊗ (α ∧ ω)`, with `α ∧ ω` the relative exterior product
`AlgebraicGeometry.Scheme.Hom.relativeExteriorProduct`. -/
theorem twistedFormsWedgeSection_tmul (q : ℕ) (U : (Y.Opens)ᵒᵖ) (s : H.val.obj U)
    (α : (relativeDifferentials g).val.obj U)
    (ω : (relativeDifferentialForms g (q : ℤ)).val.obj U) :
    twistedFormsWedgeSection g H q U (connectionTmul g H U s α) ω =
      twistedTmul g H (q + 1) U s (relativeExteriorProduct g q U α ω) := by
  have h₁ := Stacks.PullbackTensorCoherence.associator_hom_tmul (Z := Y.toRingedSpace)
    (A := modulesOnRing H) (B := differentialsOnRing g) (D := formsOnRing g q) U s α ω
  have h₂ : (twistedFormsWedge g H q).val.app U
      (tmul Y.toRingedSpace (modulesOnRing H ⊗ differentialsOnRing g) (formsOnRing g q) U
        (tmul Y.toRingedSpace (modulesOnRing H) (differentialsOnRing g) U s α) ω) =
      tmul Y.toRingedSpace (modulesOnRing H) (formsOnRing g ((q + 1 : ℕ) : ℤ)) U s
        (relativeExteriorProduct g q U α ω) :=
    (congrArg (fun z => (modulesOnRing H ◁ relativeExteriorProductHom g q).val.app U z) h₁).trans
      ((Stacks.PullbackTensorCoherence.whiskerLeft_tmul _ U s _).trans
        (congrArg _ (relativeExteriorProductHom_tmul g q U α ω)))
  exact h₂

/-! ### The switch `Ω^1_{Y/S} ⊗ ℱ ≅ ℱ ⊗ Ω_{Y/S}` -/

/-- The degree-one generator `Ω_{Y/S} ⟶ Ω^1_{Y/S}` is an isomorphism. -/
instance isIso_exteriorGeneratorOnRing : IsIso (exteriorGeneratorOnRing g) :=
  (SheafOfModules.algebras _ (relativeDifferentials g)).isIso_exteriorGenerator

/-- **The switch `Ω^1_{Y/S} ⊗ ℱ ≅ ℱ ⊗ Ω_{Y/S}`**: the symmetry constraint of the tensor product,
followed by the inverse of the degree-one generator `Ω_{Y/S} ⟶ Ω^1_{Y/S}`.  It carries the
first page of [Stacks, Tag 0FMN] in degree one to the target `moduleConnectionTarget` of a
connection on `ℱ`. -/
def formsTensorConnectionIso :
    formsTensor g H 1 ≅ modulesOnRing H ⊗ differentialsOnRing g :=
  β_ (formsOnRing g 1) (modulesOnRing H) ≪≫
    whiskerLeftIso (modulesOnRing H)
      (asIso (exteriorGeneratorOnRing g)).symm

/-- The switch on a pure tensor of a `1`-form with a section: `a ⊗ s ↦ s ⊗ a`, with `a` read back
in `Ω_{Y/S}` through the inverse of the degree-one generator. -/
theorem formsTensorConnectionIso_hom_tmul_inv (U : (Y.Opens)ᵒᵖ)
    (a : (relativeDifferentialForms g 1).val.obj U) (s : H.val.obj U) :
    (formsTensorConnectionIso g H).hom.val.app U (formsTensorTmul g H 1 U a s) =
      tmul Y.toRingedSpace (modulesOnRing H) (differentialsOnRing g) U s
        ((inv (exteriorGeneratorOnRing g)).val.app U a) :=
  (congrArg (fun z => (modulesOnRing H ◁ inv (exteriorGeneratorOnRing g)).val.app U z)
    (Stacks.PullbackTensorCoherence.braiding_tmul Y.toRingedSpace (formsOnRing g 1)
      (modulesOnRing H) U a s)).trans
    (Stacks.PullbackTensorCoherence.whiskerLeft_tmul _ U s _)

/-- The switch on a pure tensor: `d b ⊗ s ↦ s ⊗ d b`, for a relative differential read in
`Ω^1_{Y/S}` through the degree-one generator. -/
theorem formsTensorConnectionIso_hom_tmul (U : (Y.Opens)ᵒᵖ)
    (α : (relativeDifferentials g).val.obj U) (s : H.val.obj U) :
    (formsTensorConnectionIso g H).hom.val.app U
        (formsTensorTmul g H 1 U
          ((Scheme.Modules.exteriorGenerator (relativeDifferentials g)).val.app U α) s) =
      connectionTmul g H U s α :=
  (formsTensorConnectionIso_hom_tmul_inv g H U _ s).trans
    (congrArg (tmul Y.toRingedSpace (modulesOnRing H) (differentialsOnRing g) U s)
      (Stacks.PullbackTensorCoherence.inv_val_app_apply (exteriorGeneratorOnRing g) U α))

/-! ### The sign rule -/

/-- Graded commutativity of `Ω^•_{Y/S}` between a `q`-form and a `1`-form:
`ω ∧ α = (-1)^q · α ∧ ω`. -/
theorem relativeDifferentialForms_mul_one_comm (q : ℕ) (U : (Y.Opens)ᵒᵖ)
    (ω : (relativeDifferentialForms g (q : ℤ)).val.obj U)
    (a : (relativeDifferentialForms g 1).val.obj U) :
    transportDifferentialForm g (show (q : ℤ) + 1 = ((q + 1 : ℕ) : ℤ) by push_cast; rfl) U
        (((relativeDifferentialFormsAlgebra g).mul q 1).app U ω a) =
      (-1 : ℤ) ^ q • transportDifferentialForm g
        (show (1 : ℤ) + (q : ℤ) = ((q + 1 : ℕ) : ℤ) by push_cast; ring) U
        (((relativeDifferentialFormsAlgebra g).mul 1 q).app U a ω) := by
  have h := AlgebraicGeometry.SheafOfModules.formProduct_comm (deRhamAlgebras g) q 1 U ω a
  rw [mul_one] at h
  refine eq_of_heq ((transportDifferentialForm_heq g _ U _).trans (heq_of_eq (h.trans ?_)))
  refine congrArg (fun z => (-1 : ℤ) ^ q • z) (eq_of_heq ?_)
  exact (AlgebraicGeometry.SheafOfModules.reindexForm_heq (deRhamAlgebras g) _ U _).trans
    (transportDifferentialForm_heq g _ U _).symm

/-- The identification `Ω^{q+1} ⊗ ℱ = Ω^{q+1} ⊗ ℱ` between the degree `q + 1` computed in `ℤ`,
which is where the wedge pairing and the first page of [Stacks, Tag 0FMN] put it, and the
degree `q + 1` computed in `ℕ`, which is where the twisted de Rham complex puts it. -/
def formsTensorSuccIso (q : ℕ) :
    formsTensor g H ((q : ℤ) + 1) ≅ formsTensor g H ((q + 1 : ℕ) : ℤ) :=
  eqToIso (congrArg (formsTensor g H) (show (q : ℤ) + 1 = ((q + 1 : ℕ) : ℤ) by push_cast; rfl))

/-- Renaming the degree of `Ω^p ⊗ ℱ` renames the degree of the form in a pure tensor. -/
theorem eqToHom_formsTensor_tmul {p₁ p₂ : ℤ} (e : p₁ = p₂) (U : (Y.Opens)ᵒᵖ)
    (ω : (relativeDifferentialForms g p₁).val.obj U) (s : H.val.obj U) :
    (eqToHom (congrArg (formsTensor g H) e)).val.app U (formsTensorTmul g H p₁ U ω s) =
      formsTensorTmul g H p₂ U (transportDifferentialForm g e U ω) s := by
  subst e
  rfl

/-- `formsTensorSuccIso` on a pure tensor renames the degree of the form. -/
theorem formsTensorSuccIso_hom_tmul (q : ℕ) (U : (Y.Opens)ᵒᵖ)
    (ω : (relativeDifferentialForms g ((q : ℤ) + 1)).val.obj U) (s : H.val.obj U) :
    (formsTensorSuccIso g H q).hom.val.app U (formsTensorTmul g H ((q : ℤ) + 1) U ω s) =
      formsTensorTmul g H ((q + 1 : ℕ) : ℤ) U
        (transportDifferentialForm g (show (q : ℤ) + 1 = ((q + 1 : ℕ) : ℤ) by push_cast; rfl) U ω)
        s :=
  eqToHom_formsTensor_tmul g H _ U ω s

/-- **The sign rule**, as an equation of morphisms out of `(Ω^1 ⊗ ℱ) ⊗ Ω^q`: wedging on the left
with a `q`-form and switching to `ℱ ⊗ Ω^{q+1}` is `(-1)^q` times switching first and then wedging
on the right.  This is graded commutativity of `Ω^•_{Y/S}`, moved across the symmetry constraint
of the tensor product. -/
theorem zsmul_formsTensorWedge_comp_braiding (q : ℕ) :
    (β_ (formsTensor g H 1) (formsOnRing g q)).hom ≫ formsTensorWedge g H q 1 ≫
        (formsTensorSuccIso g H q).hom ≫
        (β_ (formsOnRing g ((q + 1 : ℕ) : ℤ)) (modulesOnRing H)).hom =
      (-1 : ℤ) ^ q •
        ((formsTensorConnectionIso g H).hom ▷ formsOnRing g q ≫ twistedFormsWedge g H q) := by
  refine Stacks.PullbackTensorCoherence.tensor_hom_ext₂ fun U a s ω => ?_
  have hl : ((β_ (formsTensor g H 1) (formsOnRing g q)).hom ≫ formsTensorWedge g H q 1 ≫
        (formsTensorSuccIso g H q).hom ≫
        (β_ (formsOnRing g ((q + 1 : ℕ) : ℤ)) (modulesOnRing H)).hom).val.app U
        (tmul Y.toRingedSpace (formsTensor g H 1) (formsOnRing g q) U
          (formsTensorTmul g H 1 U a s) ω) =
      tmul Y.toRingedSpace (modulesOnRing H) (formsOnRing g ((q + 1 : ℕ) : ℤ)) U s
        (transportDifferentialForm g (show (q : ℤ) + 1 = ((q + 1 : ℕ) : ℤ) by push_cast; rfl) U
          (((relativeDifferentialFormsAlgebra g).mul q 1).app U ω a)) := by
    rw [SheafOfModules.comp_val_app_apply, SheafOfModules.comp_val_app_apply,
      SheafOfModules.comp_val_app_apply, Stacks.PullbackTensorCoherence.braiding_tmul,
      formsTensorWedge_tmul, formsTensorSuccIso_hom_tmul,
      Stacks.PullbackTensorCoherence.braiding_tmul]
  have hr : ((formsTensorConnectionIso g H).hom ▷ formsOnRing g q ≫
        twistedFormsWedge g H q).val.app U
        (tmul Y.toRingedSpace (formsTensor g H 1) (formsOnRing g q) U
          (formsTensorTmul g H 1 U a s) ω) =
      tmul Y.toRingedSpace (modulesOnRing H) (formsOnRing g ((q + 1 : ℕ) : ℤ)) U s
        (transportDifferentialForm g
          (show (1 : ℤ) + (q : ℤ) = ((q + 1 : ℕ) : ℤ) by push_cast; ring) U
          (((relativeDifferentialFormsAlgebra g).mul 1 q).app U a ω)) := by
    rw [SheafOfModules.comp_val_app_apply, Stacks.PullbackTensorCoherence.whiskerRight_tmul,
      formsTensorConnectionIso_hom_tmul_inv]
    refine (twistedFormsWedgeSection_tmul g H q U s _ ω).trans ?_
    refine congrArg (tmul Y.toRingedSpace (modulesOnRing H) (formsOnRing g ((q + 1 : ℕ) : ℤ)) U s)
      (congrArg (transportDifferentialForm g _ U) ?_)
    exact congrArg (fun z => ((relativeDifferentialFormsAlgebra g).mul 1 q).app U z ω)
      (Stacks.PullbackTensorCoherence.val_app_inv_val_app (exteriorGeneratorOnRing g) U a)
  rw [hl, SheafOfModules.zsmul_val_app, hr, ← tmul_zsmul_right]
  exact congrArg _ (relativeDifferentialForms_mul_one_comm g q U ω a)

/-- **The sign rule on local sections**: for a local `q`-form `ω` and a local section `y` of
`Ω^1 ⊗ ℱ`, the wedge `ω ∧ y`, read in `ℱ ⊗ Ω^{q+1}`, is `(-1)^q` times the twisted wedge of the
switched `y` with `ω`. -/
theorem braiding_formsTensorWedgeSection (q : ℕ) (U : (Y.Opens)ᵒᵖ)
    (ω : (relativeDifferentialForms g (q : ℤ)).val.obj U) (y : (formsTensor g H 1).val.obj U) :
    (β_ (formsOnRing g ((q + 1 : ℕ) : ℤ)) (modulesOnRing H)).hom.val.app U
        ((formsTensorSuccIso g H q).hom.val.app U (formsTensorWedgeSection g H q 1 U ω y)) =
      (-1 : ℤ) ^ q •
        twistedFormsWedgeSection g H q U ((formsTensorConnectionIso g H).hom.val.app U y) ω := by
  have h := congrArg (fun φ => φ.val.app U
      (tmul Y.toRingedSpace (formsTensor g H 1) (formsOnRing g q) U y ω))
    (zsmul_formsTensorWedge_comp_braiding g H q)
  refine Eq.trans ?_ (h.trans ?_)
  · exact congrArg (fun z => (β_ (formsOnRing g ((q + 1 : ℕ) : ℤ)) (modulesOnRing H)).hom.val.app
      U ((formsTensorSuccIso g H q).hom.val.app U ((formsTensorWedge g H q 1).val.app U z)))
      (Stacks.PullbackTensorCoherence.braiding_tmul Y.toRingedSpace _ _ U y ω).symm
  · exact (SheafOfModules.zsmul_val_app _ _ U _).trans
      (congrArg (fun z => (-1 : ℤ) ^ q • (twistedFormsWedge g H q).val.app U z)
        (Stacks.PullbackTensorCoherence.whiskerRight_tmul _ U y ω))

end AlgebraicGeometry.Scheme.Hom
