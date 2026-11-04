module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorRestrictScalarsTransitivity
public import StacksFrontier.CategoryTheory.Sites.Modules.Flat
public import StacksFrontier.CategoryTheory.Sites.Modules.Localization.Differentials
import StacksCore.Tactic.EgaSgaAttribute

/-!
# `ρ_*(M ⊗_{A₂} N) ≅ ρ_*M ⊗_{A₁} ρ_*N` for an isomorphism `ρ` of sheaves of rings

Let `θ : A₁ ⟶ A₂` be a morphism of sheaves of commutative rings on a site `(C, J)` whose
underlying morphism of sheaves of rings `ρ` is an **isomorphism**, and let `M` and `N` be sheaves
of `A₂`-modules.  This file proves that restriction of scalars along `ρ` commutes with the
sheafified tensor product,

`ρ_*N ⊗_{A₁} ρ_*M ≅ ρ_*(N ⊗_{A₂} M)`.

## Why this is a corollary and not a new construction

`Stacks.SheafOfModules.TensorTransitivity.tensorRestrictScalarsTransitivityIso` already gives

`ρ_*N ⊗_{A₁} L ≅ ρ_*(N ⊗_{A₂} ρ^*L)`

for *every* `θ` and every sheaf of `A₁`-modules `L`, with nothing assumed.  Taking `L := ρ_*M`
leaves only `ρ^*ρ_*M ≅ M`, and that is the counit of the extension/restriction adjunction of
[Stacks, Tag 03CZ] at `M`: when `ρ` is an isomorphism, restriction of scalars along it is fully
faithful (`SheafOfModules.fullyFaithfulRestrictScalarsOfIsIso`), and the counit of an adjunction
with fully faithful right adjoint is an isomorphism.  No new comparison of tensor products is
built, and no flatness or exactness enters.

## Main definitions

* `Stacks.SheafOfModules.TensorTransitivity.presheafTensorLeftFunctor`: the objectwise tensor
  product `N ⊗ -` of presheaves of modules as a functor, which is `Stacks.tensorMapRight`
  assembled into one.
* `Stacks.SheafOfModules.TensorTransitivity.extendRestrictScalarsCounitIso`: **`ρ^*ρ_*M ≅ M`**
  for an isomorphism `ρ`.
* `Stacks.SheafOfModules.TensorTransitivity.tensorRestrictScalarsAlongIsoIso`:
  **`ρ_*N ⊗_{A₁} ρ_*M ≅ ρ_*(N ⊗_{A₂} M)`.**

## Main results

* `Stacks.SheafOfModules.TensorTransitivity.isIso_commRingSheafMap`: an isomorphism of sheaves of
  commutative rings has an isomorphism of sheaves of rings underlying it.

## What this is for

`StacksFrontier/Cotangent/SheavesOfRings/FibreDifferentials.lean` records, in its module
documentation, that reading
`CategoryTheory.Sheaf.fibrePrincipalPartsX₁Iso` entirely over the degree-`n` term `P_n` of the
standard resolution needs "the transport of a tensor product along the isomorphism
`i_n^{-1}𝒫 ≅ P_n` of sheaves of commutative rings — the analogue for `⊗` of the transport
`AlgebraicGeometry.SheafOfModules.derivationEquivOfRingDataIso` performs for derivations".  That
transport is this file.

## References

* [Stacks Project, Tag 03CZ](https://stacks.math.columbia.edu/tag/03CZ), the extension of
  scalars and its adjunction, whose counit is what the isomorphism of `ρ` makes invertible.
* [Stacks Project, Tag 03D1](https://stacks.math.columbia.edu/tag/03D1), the tensor product of
  sheaves of modules, which is the construction being transported.
-/

@[expose] public noncomputable section

open CategoryTheory TensorProduct
open Stacks.PresheafOfModules.ChangeOfRings (ringPresheaf)
open Stacks.Sheaves.RingedToposModules (commRingSheaf commRingSheafMap extendScalars
  extendRestrictScalarsAdjunction)

universe u

namespace Stacks.SheafOfModules.TensorTransitivity

/-! ### Tensoring on the left as a functor -/

section TensorLeft

variable {C : Type u} [SmallCategory C] {O : Cᵒᵖ ⥤ CommRingCat.{u}}

/-- **The objectwise tensor product `N ⊗ -` of presheaves of modules, as a functor.**  Its
action on morphisms is `Stacks.tensorMapRight`, which `StacksDraft` records only as a morphism;
the two functor laws are checked on pure tensors, where both sides are the same element. -/
@[ega "III 7.2.6" "partial", sga "4 IV 12.10" "special case", sga "4 XVII 4.1.6" "special case"]
def presheafTensorLeftFunctor (N : PresheafOfModules.{u} (ringPresheaf O)) :
    PresheafOfModules.{u} (ringPresheaf O) ⥤ PresheafOfModules.{u} (ringPresheaf O) where
  obj M := Stacks.tensorObj N M
  map α := Stacks.tensorMapRight N α
  map_id M := by
    apply PresheafOfModules.hom_ext
    intro X
    apply ModuleCat.hom_ext
    apply TensorProduct.ext
    ext x y
    rfl
  map_comp α β := by
    apply PresheafOfModules.hom_ext
    intro X
    apply ModuleCat.hom_ext
    apply TensorProduct.ext
    ext x y
    rfl

end TensorLeft

/-! ### The counit of the change-of-rings adjunction along an isomorphism -/

section AlongIso

variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
  {A₁ A₂ : Cᵒᵖ ⥤ CommRingCat.{u}} (θ : A₁ ⟶ A₂)
  (h₁ : Presheaf.IsSheaf J (ringPresheaf A₁)) (h₂ : Presheaf.IsSheaf J (ringPresheaf A₂))
  [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- **An isomorphism of sheaves of commutative rings has an isomorphism of sheaves of rings
underlying it.** -/
instance isIso_commRingSheafMap [IsIso θ] : IsIso (commRingSheafMap J θ h₁ h₂) :=
  ⟨⟨commRingSheafMap J (inv θ) h₂ h₁,
    Sheaf.hom_ext (by
      change Functor.whiskerRight θ (forget₂ CommRingCat.{u} RingCat.{u}) ≫
        Functor.whiskerRight (inv θ) (forget₂ CommRingCat.{u} RingCat.{u}) = 𝟙 _
      rw [← Functor.whiskerRight_comp, IsIso.hom_inv_id]
      simp),
    Sheaf.hom_ext (by
      change Functor.whiskerRight (inv θ) (forget₂ CommRingCat.{u} RingCat.{u}) ≫
        Functor.whiskerRight θ (forget₂ CommRingCat.{u} RingCat.{u}) = 𝟙 _
      rw [← Functor.whiskerRight_comp, IsIso.inv_hom_id]
      simp)⟩⟩

variable [IsIso (commRingSheafMap J θ h₁ h₂)]

/-- **`ρ^*ρ_*M ≅ M` for an isomorphism `ρ` of sheaves of rings.**  Restriction of scalars along
an isomorphism is fully faithful
(`SheafOfModules.fullyFaithfulRestrictScalarsOfIsIso`), and the counit of an adjunction whose
right adjoint is fully faithful is an isomorphism; the adjunction is [Stacks, Tag 03CZ]. -/
def extendRestrictScalarsCounitIso (M : SheafOfModules.{u} (commRingSheaf J A₂ h₂)) :
    (extendScalars J θ h₁ h₂).obj
        ((_root_.SheafOfModules.restrictScalars (commRingSheafMap J θ h₁ h₂)).obj M) ≅ M :=
  haveI := (_root_.SheafOfModules.fullyFaithfulRestrictScalarsOfIsIso
    (commRingSheafMap J θ h₁ h₂)).full
  haveI := (_root_.SheafOfModules.fullyFaithfulRestrictScalarsOfIsIso
    (commRingSheafMap J θ h₁ h₂)).faithful
  asIso ((extendRestrictScalarsAdjunction J θ h₁ h₂).counit.app M)

/-- The functor `M ↦ ρ_*(N ⊗_{A₂} M)` in the shape the right-hand side of
`Stacks.SheafOfModules.TensorTransitivity.tensorRestrictScalarsTransitivityIso` is written in. -/
def restrictScalarsTensorFunctor (N : SheafOfModules.{u} (commRingSheaf J A₂ h₂)) :
    SheafOfModules.{u} (commRingSheaf J A₂ h₂) ⥤ SheafOfModules.{u} (commRingSheaf J A₁ h₁) :=
  _root_.SheafOfModules.forget (commRingSheaf J A₂ h₂) ⋙
    _root_.PresheafOfModules.restrictScalars (𝟙 (commRingSheaf J A₂ h₂).obj) ⋙
    presheafTensorLeftFunctor N.val ⋙
    _root_.PresheafOfModules.sheafification (R := commRingSheaf J A₂ h₂) (𝟙 _) ⋙
    _root_.SheafOfModules.restrictScalars (commRingSheafMap J θ h₁ h₂)

/-- **`ρ_*N ⊗_{A₁} ρ_*M ≅ ρ_*(N ⊗_{A₂} M)` for an isomorphism `ρ` of sheaves of rings.**
Restriction of scalars along an isomorphism of sheaves of rings commutes with the tensor product
of sheaves of modules.

Both sides are written out as sheafifications of objectwise tensor products, matching
`Stacks.SheafOfModules.TensorTransitivity.tensorRestrictScalarsTransitivityIso`, of which this is
the case `L = ρ_*M` with the counit `ρ^*ρ_*M ≅ M` substituted. -/
def tensorRestrictScalarsAlongIsoIso (M N : SheafOfModules.{u} (commRingSheaf J A₂ h₂)) :
    (_root_.PresheafOfModules.sheafification (R := commRingSheaf J A₁ h₁) (𝟙 _)).obj
        (Stacks.tensorObj
          ((_root_.PresheafOfModules.restrictScalars
            (commRingSheafMap J θ h₁ h₂).hom).obj N.val)
          ((_root_.SheafOfModules.restrictScalars
            (commRingSheafMap J θ h₁ h₂)).obj M).val) ≅
      (_root_.SheafOfModules.restrictScalars (commRingSheafMap J θ h₁ h₂)).obj
        ((_root_.PresheafOfModules.sheafification (R := commRingSheaf J A₂ h₂) (𝟙 _)).obj
          (Stacks.tensorObj N.val
            ((_root_.PresheafOfModules.restrictScalars
              (𝟙 (commRingSheaf J A₂ h₂).obj)).obj M.val))) :=
  tensorRestrictScalarsTransitivityIso J θ h₁ h₂
      ((_root_.SheafOfModules.restrictScalars (commRingSheafMap J θ h₁ h₂)).obj M) N ≪≫
    (restrictScalarsTensorFunctor J θ h₁ h₂ N).mapIso
      (extendRestrictScalarsCounitIso J θ h₁ h₂ M)

end AlongIso

/-! ### The same, in the `sheafTensorRight` spelling

Both statements of this section are the preceding ones with their two sides ascribed to
`Stacks.SheafOfModules.Tensor.sheafTensor` with its factors flipped, the spelling in which
the sequence of first principal parts and the Atiyah triangle are formed.  The ascriptions are
definitional equalities, but on the large terms of a concrete application they are not cheap ones:
asking for
them there exhausts the heartbeat budget, while asking for them here, on generic arguments,
costs nothing.  This is the recipe the implementation notes of
`StacksFrontier/CategoryTheory/Sites/Modules/DifferentialsRestriction.lean` set out for the same
tensor spelling. -/

section SheafTensor

variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- **Tensoring by a varying factor, as a functor.**
`(Stacks.SheafOfModules.Tensor.sheafTensor O).flip.obj M` is functorial in the module `M ⊗ -` is
applied to; this is its functoriality in the factor `M` it tensors by, at a fixed module `N`. -/
def sheafTensorRightFactorFunctor (O : Sheaf J CommRingCat.{u})
    (N : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O)) :
    SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O) ⥤
      SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O) := by
  let T : _root_.PresheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O).obj ⥤
      _root_.PresheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O).obj :=
    presheafTensorLeftFunctor (O := O.obj) N.val
  let S : _root_.PresheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O).obj ⥤
      SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O) :=
    _root_.PresheafOfModules.sheafification.{u} (R := Stacks.SheafOfModules.Tensor.ringSheaf O)
      (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf O).obj)
  exact _root_.SheafOfModules.forget.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O) ⋙ T ⋙ S

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat)] in
/-- Tensoring by a varying factor is `Stacks.SheafOfModules.Tensor.sheafTensor` with its
factors flipped and its two arguments exchanged. -/
theorem sheafTensorRightFactorFunctor_obj (O : Sheaf J CommRingCat.{u})
    (N M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O)) :
    (sheafTensorRightFactorFunctor J O N).obj M =
      ((Stacks.SheafOfModules.Tensor.sheafTensor O).flip.obj M).obj N := rfl

/-- **An isomorphism of the factor gives an isomorphism of the tensor product.** -/
def sheafTensorRightFactorIso (O : Sheaf J CommRingCat.{u})
    (N : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O))
    {M M' : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O)} (e : M ≅ M') :
    ((Stacks.SheafOfModules.Tensor.sheafTensor O).flip.obj M).obj N ≅
      ((Stacks.SheafOfModules.Tensor.sheafTensor O).flip.obj M').obj N :=
  (sheafTensorRightFactorFunctor J O N).mapIso e

variable {O₁ O₂ : Sheaf J CommRingCat.{u}} (ρ : O₁ ⟶ O₂)
  [IsIso ((Stacks.forgetCommRingSheaf J).map ρ)]

/-- **`ρ_*N ⊗_{O₁} ρ_*M ≅ ρ_*(N ⊗_{O₂} M)` in the `sheafTensorRight` spelling**, for `ρ` a
homomorphism of sheaves of commutative rings whose underlying homomorphism of sheaves of rings is
an isomorphism.  This is
`Stacks.SheafOfModules.TensorTransitivity.tensorRestrictScalarsAlongIsoIso` with both sides
ascribed. -/
def sheafTensorRightRestrictScalarsIso
    (M N : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O₂)) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor O₁).flip.obj
          ((_root_.SheafOfModules.restrictScalars
            ((Stacks.forgetCommRingSheaf J).map ρ)).obj M)).obj
        ((_root_.SheafOfModules.restrictScalars
          ((Stacks.forgetCommRingSheaf J).map ρ)).obj N) ≅
      (_root_.SheafOfModules.restrictScalars ((Stacks.forgetCommRingSheaf J).map ρ)).obj
        (((Stacks.SheafOfModules.Tensor.sheafTensor O₂).flip.obj M).obj N) :=
  haveI : IsIso (commRingSheafMap J ρ.hom (Stacks.SheafOfModules.Tensor.ringSheaf O₁).cond
      (Stacks.SheafOfModules.Tensor.ringSheaf O₂).cond) :=
    inferInstanceAs (IsIso ((Stacks.forgetCommRingSheaf J).map ρ))
  tensorRestrictScalarsAlongIsoIso J ρ.hom (Stacks.SheafOfModules.Tensor.ringSheaf O₁).cond
    (Stacks.SheafOfModules.Tensor.ringSheaf O₂).cond M N

end SheafTensor

end Stacks.SheafOfModules.TensorTransitivity

end
