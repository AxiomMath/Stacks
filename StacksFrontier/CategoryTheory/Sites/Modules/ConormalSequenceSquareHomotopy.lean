module

public import StacksFrontier.CategoryTheory.Sites.Modules.ConormalSequenceSquare
public import StacksFrontier.CategoryTheory.Sites.Modules.InternalHomAndFlatness.NaiveCotangentHomotopy

/-!
# Two maps of presentations over one square induce homotopic maps of conormal sequences

Let `φ₁ : A₁ ⟶ B₁` and `φ₂ : A₂ ⟶ B₂` be locally surjective morphisms of sheaves of
commutative rings on a site, let `β : B₁ ⟶ B₂`, and let `ψ, ψ' : A₁ ⟶ A₂` be two morphisms
with `ψ ≫ φ₂ = φ₁ ≫ β = ψ' ≫ φ₂`.  Writing `I₁` and `I₂` for the two kernels, each of `ψ`
and `ψ'` induces maps `I₁/I₁² ⟶ I₂/I₂²` and `B₁ ⊗[A₁] Ω[A₁/R₁] ⟶ B₂ ⊗[A₂] Ω[A₂/R₂]` on the
first two terms of the conormal sequences.  Provided `ψ` and `ψ'` agree on the base ring, the
two pairs of maps differ by the single map of sheaves of `B₁`-modules

`B₁ ⊗[A₁] Ω[A₁/R₁] ⟶ I₂/I₂²`

whose value on the local section `b ⊗ d x` is `b · (ψ(x) - ψ'(x))`.  This is the form for a
commutative square of the homotopy of **Stacks 00S1 (2)**; it is constructed on local sections
in
`StacksFrontier/CategoryTheory/Sites/Modules/InternalHomAndFlatness/NaiveCotangentHomotopy.lean`
and sheafified here, and it is what produces the null homotopy in the exact sequence of naive
cotangent complexes attached to a composition `A ⟶ B ⟶ C` of morphisms of sheaves of rings.

The argument is the one of commutative algebra and is unchanged: `ψ(x) - ψ'(x)` is a section
of `I₂` because both become `φ₁(x)` read in `B₂`, the Leibniz error term
`(ψ(x) - ψ'(x))(ψ(y) - ψ'(y))` lies in `I₂²`, and the two morphisms agree on the image of the
base ring.  So `x ↦ ψ(x) - ψ'(x) mod I₂²` is a derivation, it factors through `Ω[A₁/R₁]`, and
extending scalars gives the homotopy.

The second half of the file records when such a morphism of presentations induces the *zero*
pair of maps: this happens as soon as `ψ'` factors as `φ₁ ≫ γ ≫ a₂` through the base ring
`R₂` of the second presentation, since then `ψ'` kills `I₁` and every differential `d (ψ' x)`
vanishes in `Ω[A₂/R₂]`.

## Main definitions

* `Stacks.Sites.Conormal.conormalHomotopyOfSquare`: the homotopy as a morphism of sheaves of
  `B₁`-modules.

## Main results

* `Stacks.Sites.Conormal.conormalSheafMapOfSquare_eq_add` and
  `Stacks.Sites.Conormal.tensorSheafMapOfSquare_eq_add`: the two homotopy relations, in
  degrees `-1` and `0`.
* `Stacks.Sites.Conormal.conormalSheafMapOfSquare_eq_zero_of_const` and
  `Stacks.Sites.Conormal.tensorSheafMapOfSquare_eq_zero_of_const`: a morphism of
  presentations that factors through the base ring of the target presentation induces the
  zero map of conormal sequences.
* `Stacks.Sites.Conormal.conormalSheafMapOfSquare_eq_comp_homotopy` and
  `Stacks.Sites.Conormal.tensorSheafMapOfSquare_eq_homotopy_comp`: the combination of the
  two, which exhibits the pair of maps induced by `ψ` as a null homotopy.

## Implementation notes

The target of the homotopy is the restriction of scalars along `β` of `I₂/I₂²`, which leaves
sections and restriction maps alone and changes only the module structure, so the family of
maps on sections is turned into a morphism of sheaves of modules by
`Stacks.Sites.Conormal.sheafifyLiftDesc` exactly as for a fixed target.

The homotopy relations are recorded in the additive form `f = d ∘ h + g`, the form that
`Homotopy.comm` consumes.

## References

* [Stacks Project, Tag 00S1](https://stacks.math.columbia.edu/tag/00S1), part (2), the
  commutative algebra statement.
* [Stacks Project, Tag 08TS](https://stacks.math.columbia.edu/tag/08TS), the conormal
  sequence.
* [Stacks Project, Tag 08TX](https://stacks.math.columbia.edu/tag/08TX), the functoriality of
  the naive cotangent complex in a square of sheaves of rings.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TensorProduct

universe v u w z

namespace Stacks.Sites.Conormal

variable {C : Type u} [Category.{v} C]

/-! ### The homotopy as a morphism of sheaves of modules -/

section Sheaves

open AlgebraicGeometry.SheafOfModules (underlyingRingHomOfSite)

variable (J : GrothendieckTopology C) [HasWeakSheafify J CommRingCat.{w}]
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable (R₁ R₂ A₁ A₂ B₁ B₂ : Sheaf J CommRingCat.{w}) (a₁ : R₁ ⟶ A₁) (a₂ : R₂ ⟶ A₂)
  (φ₁ : A₁ ⟶ B₁) (φ₂ : A₂ ⟶ B₂) (ψ ψ' : A₁ ⟶ A₂) (β : B₁ ⟶ B₂) (ρ : R₁ ⟶ R₂)
  (hsq : ψ ≫ φ₂ = φ₁ ≫ β) (hsq' : ψ' ≫ φ₂ = φ₁ ≫ β)
  (ha : ρ ≫ a₂ = a₁ ≫ ψ) (ha' : ρ ≫ a₂ = a₁ ≫ ψ')
  [Presheaf.IsLocallySurjective J φ₁.hom] [Presheaf.IsLocallySurjective J φ₂.hom]

include hsq hsq' ha ha' in
/-- **The homotopy between the two maps of conormal sequences attached to a square.**  Two
morphisms `ψ, ψ' : A₁ ⟶ A₂` of presentations over one commutative square `ψ ≫ φ₂ = φ₁ ≫ β`
and over one square of base rings induce the same map of conormal sequences up to the
homotopy `B₁ ⊗[A₁] Ω[A₁/R₁] ⟶ I₂/I₂²` determined on local sections by
`b ⊗ d x ↦ b · (ψ(x) - ψ'(x))`. -/
noncomputable def conormalHomotopyOfSquare :
    tensorDifferentialsSheaf.{v, u, w, z} J R₁ A₁ B₁ a₁ φ₁ ⟶
      (_root_.SheafOfModules.restrictScalars (underlyingRingHomOfSite β)).obj
        (conormalSheaf.{v, u, w, z} J A₂ B₂ φ₂) := by
  refine sheafifyLiftDesc.{v, u, w, z} J A₁ B₁ φ₁ (tensorPresheaf φ₁.hom a₁.hom) _
    (fun X t ↦ toAssociatedModule.{v, u, w, z} J A₂ B₂ φ₂ (conormalPresheaf φ₂.hom) X
      (tensorHomotopyOfSquare φ₁.hom φ₂.hom ψ.hom ψ'.hom β.hom (hom_of_square hsq)
        (hom_of_square hsq') a₁.hom a₂.hom ρ.hom (hom_of_square ha) (hom_of_square ha') X t))
    ?_ ?_ ?_
  · intro X t t'
    exact (congrArg (toAssociatedModule.{v, u, w, z} J A₂ B₂ φ₂ (conormalPresheaf φ₂.hom) X)
      (map_add (tensorHomotopyOfSquare φ₁.hom φ₂.hom ψ.hom ψ'.hom β.hom (hom_of_square hsq)
        (hom_of_square hsq') a₁.hom a₂.hom ρ.hom (hom_of_square ha) (hom_of_square ha') X)
        t t')).trans
      (toAssociatedModule_add.{v, u, w, z} J A₂ B₂ φ₂ (conormalPresheaf φ₂.hom) X _ _)
  · intro X r t
    refine (congrArg (toAssociatedModule.{v, u, w, z} J A₂ B₂ φ₂ (conormalPresheaf φ₂.hom) X)
      (tensorHomotopyOfSquare_smul φ₁.hom φ₂.hom ψ.hom ψ'.hom β.hom (hom_of_square hsq)
        (hom_of_square hsq') a₁.hom a₂.hom ρ.hom (hom_of_square ha) (hom_of_square ha')
        X r t)).trans ?_
    refine (toAssociatedModule_smul.{v, u, w, z} J A₂ B₂ φ₂
      (conormalPresheaf φ₂.hom) X _ _).trans ?_
    exact congrArg (fun s : (Stacks.SheafOfModules.Tensor.ringSheaf B₂).obj.obj X ↦
      s • toAssociatedModule.{v, u, w, z} J A₂ B₂ φ₂ (conormalPresheaf φ₂.hom) X
        (tensorHomotopyOfSquare φ₁.hom φ₂.hom ψ.hom ψ'.hom β.hom (hom_of_square hsq)
          (hom_of_square hsq') a₁.hom a₂.hom ρ.hom (hom_of_square ha) (hom_of_square ha') X t))
      (quotientToTarget_quotientMapOfSquare φ₁.hom φ₂.hom ψ.hom β.hom (hom_of_square hsq) X r)
  · intro X Y f t
    exact (congrArg (toAssociatedModule.{v, u, w, z} J A₂ B₂ φ₂ (conormalPresheaf φ₂.hom) Y)
      (tensorHomotopyOfSquare_naturality φ₁.hom φ₂.hom ψ.hom ψ'.hom β.hom (hom_of_square hsq)
        (hom_of_square hsq') a₁.hom a₂.hom ρ.hom (hom_of_square ha) (hom_of_square ha')
        f t)).trans
      (toAssociatedModule_map.{v, u, w, z} J A₂ B₂ φ₂ (conormalPresheaf φ₂.hom) f _)

omit [HasWeakSheafify J CommRingCat.{w}] in
include hsq hsq' ha ha' in
/-- The homotopy sends the local section `1 ⊗ d x` to the conormal class of
`ψ(x) - ψ'(x)`. -/
theorem conormalHomotopyOfSquare_tensorDifferential (X : Cᵒᵖ) (x : A₁.obj.obj X) :
    ((conormalHomotopyOfSquare.{v, u, w, z} J R₁ R₂ A₁ A₂ B₁ B₂ a₁ a₂ φ₁ φ₂ ψ ψ' β ρ
        hsq hsq' ha ha').val.app X)
      (tensorDifferential.{v, u, w, z} J R₁ A₁ B₁ a₁ φ₁ X x) =
      conormalClass.{v, u, w, z} J R₂ A₂ B₂ a₂ φ₂ X
        (subOfSquare φ₁.hom φ₂.hom ψ.hom ψ'.hom β.hom (hom_of_square hsq)
          (hom_of_square hsq') X x) := by
  refine (sheafifyLiftDesc_toAssociatedModule.{v, u, w, z} J A₁ B₁ φ₁
    (tensorPresheaf φ₁.hom a₁.hom) _ _ _ _ _ X _).trans ?_
  refine congrArg (toAssociatedModule.{v, u, w, z} J A₂ B₂ φ₂ (conormalPresheaf φ₂.hom) X) ?_
  refine (tensorHomotopyOfSquare_tmul φ₁.hom φ₂.hom ψ.hom ψ'.hom β.hom (hom_of_square hsq)
    (hom_of_square hsq') a₁.hom a₂.hom ρ.hom (hom_of_square ha) (hom_of_square ha')
    X _ _).trans ?_
  rw [differentialsHomotopyOfSquare_d,
    map_one (quotientMapOfSquare φ₁.hom φ₂.hom ψ.hom β.hom (hom_of_square hsq) X).hom]
  exact one_smul _ _

omit [HasWeakSheafify J CommRingCat.{w}] in
include hsq hsq' ha ha' in
/-- **The degree `-1` homotopy relation for a square.**  The two maps of conormal sheaves
induced by two morphisms of presentations over one square differ by the homotopy precomposed
with the left-hand map of the first conormal sequence. -/
theorem conormalSheafMapOfSquare_eq_add :
    conormalSheafMapOfSquare.{v, u, w, z} J A₁ A₂ B₁ B₂ φ₁ φ₂ ψ β hsq =
      (((conormalSequence.{v, u, w, z} J R₁ A₁ B₁ a₁ φ₁).f ≫
            conormalHomotopyOfSquare.{v, u, w, z} J R₁ R₂ A₁ A₂ B₁ B₂ a₁ a₂ φ₁ φ₂ ψ ψ' β ρ
              hsq hsq' ha ha' :
          conormalSheaf.{v, u, w, z} J A₁ B₁ φ₁ ⟶
            (_root_.SheafOfModules.restrictScalars (underlyingRingHomOfSite β)).obj
              (conormalSheaf.{v, u, w, z} J A₂ B₂ φ₂))) +
        conormalSheafMapOfSquare.{v, u, w, z} J A₁ A₂ B₁ B₂ φ₁ φ₂ ψ' β hsq' := by
  apply sheafify_hom_ext.{v, u, w, z} J A₁ B₁ φ₁ (conormalPresheaf φ₁.hom)
  intro X c
  have hf : (conormalSequence.{v, u, w, z} J R₁ A₁ B₁ a₁ φ₁).f.val.app X
        (toAssociatedModule.{v, u, w, z} J A₁ B₁ φ₁ (conormalPresheaf φ₁.hom) X c) =
      toAssociatedModule.{v, u, w, z} J A₁ B₁ φ₁ (tensorPresheaf φ₁.hom a₁.hom) X
        (conormalToTensorApp φ₁.hom a₁.hom X c) :=
    associatedModule_map_unit.{v, u, w, z} J A₁ B₁ φ₁ (conormalToTensor φ₁.hom a₁.hom) X c
  rw [conormalSheafMapOfSquare_toAssociatedModule, SheafOfModules.add_val,
    PresheafOfModules.add_app]
  refine Eq.trans ?_ (congrArg₂ (· + ·) ((congrArg
    ((conormalHomotopyOfSquare.{v, u, w, z} J R₁ R₂ A₁ A₂ B₁ B₂ a₁ a₂ φ₁ φ₂ ψ ψ' β ρ
      hsq hsq' ha ha').val.app X) hf).trans
      (sheafifyLiftDesc_toAssociatedModule.{v, u, w, z} J A₁ B₁ φ₁
        (tensorPresheaf φ₁.hom a₁.hom) _ _ _ _ _ X _))
    (conormalSheafMapOfSquare_toAssociatedModule.{v, u, w, z}
      J A₁ A₂ B₁ B₂ φ₁ φ₂ ψ' β hsq' X c)).symm
  exact (congrArg (toAssociatedModule.{v, u, w, z} J A₂ B₂ φ₂ (conormalPresheaf φ₂.hom) X)
      (by rw [tensorHomotopyOfSquare_conormalToTensorApp]; exact (sub_add_cancel _ _).symm)).trans
    (toAssociatedModule_add.{v, u, w, z} J A₂ B₂ φ₂ (conormalPresheaf φ₂.hom) X _ _)

omit [HasWeakSheafify J CommRingCat.{w}] in
include hsq hsq' ha ha' in
/-- **The degree `0` homotopy relation for a square.**  The two maps of tensor terms induced by
two morphisms of presentations over one square differ by the homotopy postcomposed with the
left-hand map of the second conormal sequence. -/
theorem tensorSheafMapOfSquare_eq_add :
    tensorSheafMapOfSquare.{v, u, w, z} J R₁ R₂ A₁ A₂ B₁ B₂ a₁ a₂ φ₁ φ₂ ψ β ρ hsq ha =
      ((conormalHomotopyOfSquare.{v, u, w, z} J R₁ R₂ A₁ A₂ B₁ B₂ a₁ a₂ φ₁ φ₂ ψ ψ' β ρ
            hsq hsq' ha ha' ≫
          (_root_.SheafOfModules.restrictScalars (underlyingRingHomOfSite β)).map
            (conormalSequence.{v, u, w, z} J R₂ A₂ B₂ a₂ φ₂).f :
          tensorDifferentialsSheaf.{v, u, w, z} J R₁ A₁ B₁ a₁ φ₁ ⟶
            (_root_.SheafOfModules.restrictScalars (underlyingRingHomOfSite β)).obj
              (tensorDifferentialsSheaf.{v, u, w, z} J R₂ A₂ B₂ a₂ φ₂))) +
        tensorSheafMapOfSquare.{v, u, w, z} J R₁ R₂ A₁ A₂ B₁ B₂ a₁ a₂ φ₁ φ₂ ψ' β ρ hsq' ha' := by
  apply sheafify_hom_ext.{v, u, w, z} J A₁ B₁ φ₁ (tensorPresheaf φ₁.hom a₁.hom)
  intro X t
  have hf : (conormalSequence.{v, u, w, z} J R₂ A₂ B₂ a₂ φ₂).f.val.app X
        (toAssociatedModule.{v, u, w, z} J A₂ B₂ φ₂ (conormalPresheaf φ₂.hom) X
          (tensorHomotopyOfSquare φ₁.hom φ₂.hom ψ.hom ψ'.hom β.hom (hom_of_square hsq)
            (hom_of_square hsq') a₁.hom a₂.hom ρ.hom (hom_of_square ha) (hom_of_square ha')
            X t)) =
      toAssociatedModule.{v, u, w, z} J A₂ B₂ φ₂ (tensorPresheaf φ₂.hom a₂.hom) X
        (conormalToTensorApp φ₂.hom a₂.hom X
          (tensorHomotopyOfSquare φ₁.hom φ₂.hom ψ.hom ψ'.hom β.hom (hom_of_square hsq)
            (hom_of_square hsq') a₁.hom a₂.hom ρ.hom (hom_of_square ha) (hom_of_square ha')
            X t)) :=
    associatedModule_map_unit.{v, u, w, z} J A₂ B₂ φ₂ (conormalToTensor φ₂.hom a₂.hom) X _
  have hR : (((conormalHomotopyOfSquare.{v, u, w, z} J R₁ R₂ A₁ A₂ B₁ B₂ a₁ a₂ φ₁ φ₂ ψ ψ' β ρ
          hsq hsq' ha ha' ≫
        (_root_.SheafOfModules.restrictScalars (underlyingRingHomOfSite β)).map
          (conormalSequence.{v, u, w, z} J R₂ A₂ B₂ a₂ φ₂).f :
          tensorDifferentialsSheaf.{v, u, w, z} J R₁ A₁ B₁ a₁ φ₁ ⟶
            (_root_.SheafOfModules.restrictScalars (underlyingRingHomOfSite β)).obj
              (tensorDifferentialsSheaf.{v, u, w, z} J R₂ A₂ B₂ a₂ φ₂))).val.app X)
        (toAssociatedModule.{v, u, w, z} J A₁ B₁ φ₁ (tensorPresheaf φ₁.hom a₁.hom) X t) =
      toAssociatedModule.{v, u, w, z} J A₂ B₂ φ₂ (tensorPresheaf φ₂.hom a₂.hom) X
        (conormalToTensorApp φ₂.hom a₂.hom X
          (tensorHomotopyOfSquare φ₁.hom φ₂.hom ψ.hom ψ'.hom β.hom (hom_of_square hsq)
            (hom_of_square hsq') a₁.hom a₂.hom ρ.hom (hom_of_square ha) (hom_of_square ha')
            X t)) :=
    (congrArg ((conormalSequence.{v, u, w, z} J R₂ A₂ B₂ a₂ φ₂).f.val.app X)
      (sheafifyLiftDesc_toAssociatedModule.{v, u, w, z} J A₁ B₁ φ₁
        (tensorPresheaf φ₁.hom a₁.hom) _ _ _ _ _ X t)).trans hf
  rw [tensorSheafMapOfSquare_toAssociatedModule, SheafOfModules.add_val,
    PresheafOfModules.add_app]
  refine Eq.trans ?_ (congrArg₂ (· + ·) hR
    (tensorSheafMapOfSquare_toAssociatedModule.{v, u, w, z} J R₁ R₂ A₁ A₂ B₁ B₂ a₁ a₂ φ₁ φ₂
      ψ' β ρ hsq' ha' X t)).symm
  refine (congrArg (toAssociatedModule.{v, u, w, z} J A₂ B₂ φ₂ (tensorPresheaf φ₂.hom a₂.hom) X)
      (((sub_add_cancel _ _).symm).trans (congrArg
        (· + tensorMapOfSquareₛₗ φ₁.hom φ₂.hom ψ'.hom β.hom (hom_of_square hsq') a₁.hom a₂.hom
          ρ.hom (hom_of_square ha') X t)
        (conormalToTensorApp_tensorHomotopyOfSquare φ₁.hom φ₂.hom ψ.hom ψ'.hom β.hom
          (hom_of_square hsq) (hom_of_square hsq') a₁.hom a₂.hom ρ.hom (hom_of_square ha)
          (hom_of_square ha') X t).symm))).trans ?_
  exact toAssociatedModule_add.{v, u, w, z} J A₂ B₂ φ₂ (tensorPresheaf φ₂.hom a₂.hom) X _ _

end Sheaves

/-! ### Morphisms of presentations through the base ring induce zero -/

section Const

variable {A₁ A₂ B₁ B₂ R₂ : Cᵒᵖ ⥤ CommRingCat.{w}} (φ₁ : A₁ ⟶ B₁) (φ₂ : A₂ ⟶ B₂)
  (a₂ : R₂ ⟶ A₂) (γ : B₁ ⟶ R₂) (β : B₁ ⟶ B₂)
  (hsq : (φ₁ ≫ γ ≫ a₂) ≫ φ₂ = φ₁ ≫ β)

include hsq in
/-- A morphism of presentations that factors through the target of the first presentation
kills the kernel of that presentation, hence induces zero on conormal modules. -/
theorem conormalMapOfSquare_eq_zero_of_const (X : Cᵒᵖ) (c : (conormalPresheaf φ₁).obj X) :
    conormalMapOfSquare φ₁ φ₂ (φ₁ ≫ γ ≫ a₂) β hsq X c = 0 := by
  obtain ⟨c, rfl⟩ := (kernelIdeal φ₁ X).toCotangent_surjective c
  refine (cotangentMap_toCotangent _ _ _
    (kernelIdeal_le_comap_square φ₁ φ₂ (φ₁ ≫ γ ≫ a₂) β hsq X) c).trans ?_
  refine Eq.trans (congrArg (kernelIdeal φ₂ X).toCotangent (Subtype.ext ?_)) (map_zero _)
  change (φ₁ ≫ γ ≫ a₂).app X (c : A₁.obj X) = ((0 : kernelIdeal φ₂ X) : A₂.obj X)
  change a₂.app X (γ.app X (φ₁.app X (c : A₁.obj X))) = _
  rw [show φ₁.app X (c : A₁.obj X) = 0 from c.2, map_zero, map_zero]
  rfl

section Differentials

variable {R₁ : Cᵒᵖ ⥤ CommRingCat.{w}} (a₁ : R₁ ⟶ A₁) (ρ : R₁ ⟶ R₂)
  (ha : ρ ≫ a₂ = a₁ ≫ (φ₁ ≫ γ ≫ a₂))

include ha in
/-- A morphism of presentations that factors through the base ring of the second presentation
induces zero on relative differentials, since `d (a₂ r) = 0`. -/
theorem differentialsMapOfSquare_eq_zero_of_const (X : Cᵒᵖ)
    (ω : (differentialsPresheaf a₁).obj X) :
    differentialsMapOfSquare (φ₁ ≫ γ ≫ a₂) a₁ a₂ ρ ha X ω = 0 := by
  let := (a₁.app X).hom.toAlgebra
  have mem : ω ∈ Submodule.span (A₁.obj X)
      (Set.range (KaehlerDifferential.D (R₁.obj X) (A₁.obj X))) := by
    rw [KaehlerDifferential.span_range_derivation]; trivial
  induction mem using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨x, rfl⟩ := hx
      change differentialsMapOfSquare (φ₁ ≫ γ ≫ a₂) a₁ a₂ ρ ha X
        (CommRingCat.KaehlerDifferential.d (f := a₁.app X) x) = 0
      rw [differentialsMapOfSquare_d]
      exact ModuleCat.Derivation.d_map (CommRingCat.KaehlerDifferential.D (a₂.app X))
        (γ.app X (φ₁.app X x))
  | zero => rw [map_zero]
  | add x y hx hy ihx ihy => rw [map_add, ihx, ihy, add_zero]
  | smul r ω hω ih => rw [map_smulₛₗ, ih, smul_zero]

include hsq ha in
/-- A morphism of presentations that factors through the base ring of the second presentation
induces zero on the scalar extensions of the differentials. -/
theorem tensorMapOfSquareₛₗ_eq_zero_of_const (X : Cᵒᵖ)
    (t : (A₁.obj X ⧸ kernelIdeal φ₁ X) ⊗[A₁.obj X] ((differentialsPresheaf a₁).obj X)) :
    tensorMapOfSquareₛₗ φ₁ φ₂ (φ₁ ≫ γ ≫ a₂) β hsq a₁ a₂ ρ ha X t = 0 := by
  induction t using TensorProduct.inductionOn with
  | tmul b ω =>
      refine (TensorProduct.map_tmul _ _ b ω).trans ?_
      rw [differentialsMapOfSquare_eq_zero_of_const φ₁ a₂ γ a₁ ρ ha X ω]
      exact TensorProduct.tmul_zero _ _
  | add t t' ht ht' => rw [map_add, ht, ht', add_zero]

end Differentials

end Const

/-! ### The vanishing at the level of sheaves of modules -/

section ConstSheaves

open AlgebraicGeometry.SheafOfModules (underlyingRingHomOfSite)

variable (J : GrothendieckTopology C) [HasWeakSheafify J CommRingCat.{w}]
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable (R₁ R₂ A₁ A₂ B₁ B₂ : Sheaf J CommRingCat.{w}) (a₁ : R₁ ⟶ A₁) (a₂ : R₂ ⟶ A₂)
  (φ₁ : A₁ ⟶ B₁) (φ₂ : A₂ ⟶ B₂) (γ : B₁ ⟶ R₂) (β : B₁ ⟶ B₂) (ρ : R₁ ⟶ R₂)
  (hsq : (φ₁ ≫ γ ≫ a₂) ≫ φ₂ = φ₁ ≫ β) (ha : ρ ≫ a₂ = a₁ ≫ (φ₁ ≫ γ ≫ a₂))
  [Presheaf.IsLocallySurjective J φ₁.hom] [Presheaf.IsLocallySurjective J φ₂.hom]

omit [HasWeakSheafify J CommRingCat.{w}]
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
private theorem toAssociatedModule_zero (A B : Sheaf J CommRingCat.{w}) (φ : A ⟶ B)
    [Presheaf.IsLocallySurjective J φ.hom]
    (M : PresheafOfModules.{w} (quotientPresheaf φ.hom ⋙ forget₂ _ RingCat)) (X : Cᵒᵖ) :
    toAssociatedModule.{v, u, w, z} J A B φ M X 0 = 0 := by
  have h := toAssociatedModule_add.{v, u, w, z} J A B φ M X 0 0
  rw [add_zero] at h
  exact add_right_cancel (b := toAssociatedModule.{v, u, w, z} J A B φ M X 0)
    (h.symm.trans (zero_add _).symm)

omit [HasWeakSheafify J CommRingCat.{w}] in
include hsq in
/-- A morphism of presentations factoring through the target of the first presentation induces
the zero map of conormal sheaves. -/
theorem conormalSheafMapOfSquare_eq_zero_of_const :
    conormalSheafMapOfSquare.{v, u, w, z} J A₁ A₂ B₁ B₂ φ₁ φ₂ (φ₁ ≫ γ ≫ a₂) β hsq = 0 := by
  apply sheafify_hom_ext.{v, u, w, z} J A₁ B₁ φ₁ (conormalPresheaf φ₁.hom)
  intro X c
  refine (conormalSheafMapOfSquare_toAssociatedModule.{v, u, w, z}
    J A₁ A₂ B₁ B₂ φ₁ φ₂ (φ₁ ≫ γ ≫ a₂) β hsq X c).trans ?_
  rw [show conormalMapOfSquare φ₁.hom φ₂.hom (φ₁ ≫ γ ≫ a₂).hom β.hom
      (hom_of_square hsq) X c = 0 from
    conormalMapOfSquare_eq_zero_of_const φ₁.hom φ₂.hom a₂.hom γ.hom β.hom
      (hom_of_square hsq) X c]
  exact toAssociatedModule_zero.{v, u, w, z} J A₂ B₂ φ₂ (conormalPresheaf φ₂.hom) X

omit [HasWeakSheafify J CommRingCat.{w}] in
include hsq ha in
/-- A morphism of presentations factoring through the base ring of the second presentation
induces the zero map on the scalar extensions of the differentials. -/
theorem tensorSheafMapOfSquare_eq_zero_of_const :
    tensorSheafMapOfSquare.{v, u, w, z} J R₁ R₂ A₁ A₂ B₁ B₂ a₁ a₂ φ₁ φ₂
      (φ₁ ≫ γ ≫ a₂) β ρ hsq ha = 0 := by
  apply sheafify_hom_ext.{v, u, w, z} J A₁ B₁ φ₁ (tensorPresheaf φ₁.hom a₁.hom)
  intro X t
  refine (tensorSheafMapOfSquare_toAssociatedModule.{v, u, w, z}
    J R₁ R₂ A₁ A₂ B₁ B₂ a₁ a₂ φ₁ φ₂ (φ₁ ≫ γ ≫ a₂) β ρ hsq ha X t).trans ?_
  rw [show tensorMapOfSquareₛₗ φ₁.hom φ₂.hom (φ₁ ≫ γ ≫ a₂).hom β.hom (hom_of_square hsq)
      a₁.hom a₂.hom ρ.hom (hom_of_square ha) X t = 0 from
    tensorMapOfSquareₛₗ_eq_zero_of_const φ₁.hom φ₂.hom a₂.hom γ.hom β.hom (hom_of_square hsq)
      a₁.hom ρ.hom (hom_of_square ha) X t]
  exact toAssociatedModule_zero.{v, u, w, z} J A₂ B₂ φ₂ (tensorPresheaf φ₂.hom a₂.hom) X

variable (ψ : A₁ ⟶ A₂) (hsqψ : ψ ≫ φ₂ = φ₁ ≫ β) (haψ : ρ ≫ a₂ = a₁ ≫ ψ)

omit [HasWeakSheafify J CommRingCat.{w}] in
include hsq ha hsqψ haψ in
/-- **The null homotopy in degree `-1`.**  When the comparison morphism of presentations is
compared with one factoring through the base ring of the second presentation, the map of
conormal sheaves is the homotopy precomposed with the left-hand map of the first conormal
sequence. -/
theorem conormalSheafMapOfSquare_eq_comp_homotopy :
    conormalSheafMapOfSquare.{v, u, w, z} J A₁ A₂ B₁ B₂ φ₁ φ₂ ψ β hsqψ =
      (conormalSequence.{v, u, w, z} J R₁ A₁ B₁ a₁ φ₁).f ≫
        conormalHomotopyOfSquare.{v, u, w, z} J R₁ R₂ A₁ A₂ B₁ B₂ a₁ a₂ φ₁ φ₂ ψ
          (φ₁ ≫ γ ≫ a₂) β ρ hsqψ hsq haψ ha := by
  rw [conormalSheafMapOfSquare_eq_add.{v, u, w, z} J R₁ R₂ A₁ A₂ B₁ B₂ a₁ a₂ φ₁ φ₂ ψ
      (φ₁ ≫ γ ≫ a₂) β ρ hsqψ hsq haψ ha,
    conormalSheafMapOfSquare_eq_zero_of_const.{v, u, w, z} J R₂ A₁ A₂ B₁ B₂ a₂ φ₁ φ₂ γ β hsq,
    add_zero]
  rfl

omit [HasWeakSheafify J CommRingCat.{w}] in
include hsq ha hsqψ haψ in
/-- **The null homotopy in degree `0`.**  With the same comparison, the map on the scalar
extensions of the differentials is the homotopy postcomposed with the left-hand map of the
second conormal sequence. -/
theorem tensorSheafMapOfSquare_eq_homotopy_comp :
    tensorSheafMapOfSquare.{v, u, w, z} J R₁ R₂ A₁ A₂ B₁ B₂ a₁ a₂ φ₁ φ₂ ψ β ρ hsqψ haψ =
      conormalHomotopyOfSquare.{v, u, w, z} J R₁ R₂ A₁ A₂ B₁ B₂ a₁ a₂ φ₁ φ₂ ψ
          (φ₁ ≫ γ ≫ a₂) β ρ hsqψ hsq haψ ha ≫
        (_root_.SheafOfModules.restrictScalars (underlyingRingHomOfSite β)).map
          (conormalSequence.{v, u, w, z} J R₂ A₂ B₂ a₂ φ₂).f := by
  rw [tensorSheafMapOfSquare_eq_add.{v, u, w, z} J R₁ R₂ A₁ A₂ B₁ B₂ a₁ a₂ φ₁ φ₂ ψ
      (φ₁ ≫ γ ≫ a₂) β ρ hsqψ hsq haψ ha,
    tensorSheafMapOfSquare_eq_zero_of_const.{v, u, w, z} J R₁ R₂ A₁ A₂ B₁ B₂ a₁ a₂ φ₁ φ₂
      γ β ρ hsq ha,
    add_zero]
  rfl

end ConstSheaves

end Stacks.Sites.Conormal

end
