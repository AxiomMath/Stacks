module

public import StacksFrontier.CategoryTheory.Sites.Modules.ConormalSequence
public import StacksFrontier.CategoryTheory.Sites.Modules.DifferentialsFunctorial

/-!
# Functoriality of the conormal sequence in a square of sheaves of rings

Let `φ₁ : A₁ ⟶ B₁` and `φ₂ : A₂ ⟶ B₂` be locally surjective morphisms of sheaves of
commutative rings on a site, and let `ψ : A₁ ⟶ A₂` and `β : B₁ ⟶ B₂` satisfy
`ψ ≫ φ₂ = φ₁ ≫ β`.  Writing `I₁` and `I₂` for the two kernels, `ψ` carries `I₁` into `I₂` and
therefore induces maps

`I₁/I₁² ⟶ I₂/I₂²`  and  `B₁ ⊗[A₁] Ω[A₁/R₁] ⟶ B₂ ⊗[A₂] Ω[A₂/R₂]`

on the first two terms of the conormal sequences, the second one for a square of base rings
`ρ : R₁ ⟶ R₂` over `ψ`.  Both are `B₁`-linear once the target is restricted along `β`, and they
commute with the left-hand maps of the two conormal sequences.

## Main definitions

The maps on presheaf sections that these are built from are constructed in
`StacksFrontier/CategoryTheory/Sites/Modules/ConormalSequence.lean`:

* `Stacks.Sites.Conormal.quotientMapOfSquare`: the ring map `A₁(U)/I₁(U) ⟶ A₂(U)/I₂(U)`.
* `Stacks.Sites.Conormal.conormalMapOfSquare`: the map `I₁(U)/I₁(U)² → I₂(U)/I₂(U)²`.
* `Stacks.Sites.Conormal.differentialsMapOfSquare`: the map
  `Ω[A₁(U)/R₁(U)] → Ω[A₂(U)/R₂(U)]`.
* `Stacks.Sites.Conormal.tensorMapOfSquareₛₗ`: the map
  `(A₁(U)/I₁(U)) ⊗[A₁(U)] Ω[A₁(U)/R₁(U)] → (A₂(U)/I₂(U)) ⊗[A₂(U)] Ω[A₂(U)/R₂(U)]`.
* `Stacks.Sites.Conormal.conormalSheafMapOfSquare` and
  `Stacks.Sites.Conormal.tensorSheafMapOfSquare`: the induced maps of sheaves of modules
  `I₁/I₁² ⟶ I₂/I₂²` and `B₁ ⊗[A₁] Ω[A₁/R₁] ⟶ B₂ ⊗[A₂] Ω[A₂/R₂]`, linear over `B₁`.

## Main results

* `Stacks.Sites.Conormal.conormalSheafMapOfSquare_conormalClass` and
  `Stacks.Sites.Conormal.tensorSheafMapOfSquare_tensorDifferential`: the two maps send the
  conormal class of `f` to the conormal class of `ψ f` and `1 ⊗ d f` to `1 ⊗ d (ψ f)`.
* `Stacks.Sites.Conormal.conormalSequence_f_naturality_square`: they commute with the left-hand
  maps of the two conormal sequences.
* `Stacks.Sites.Conormal.conormalSheafMapOfSquare_comp` and
  `Stacks.Sites.Conormal.tensorSheafMapOfSquare_comp`: two squares side by side induce the maps
  of the outer rectangle.
* `Stacks.Sites.Conormal.restrictScalars_comp`: restriction of scalars along a composite is the
  composite of the two restrictions of scalars.

## Implementation notes

The `…OfFac` family of
`StacksFrontier/CategoryTheory/Sites/Modules/ConormalSequence.lean`, which fixes the target `B` of
a presentation and the base `R` of the differentials, is the case `β = 𝟙` of the maps on
presheaf sections used here, whereas the functoriality of the naive cotangent complex in a
square of sheaves of rings needs both to move.  The construction is unchanged: only the
containment `I₁ ≤ ψ⁻¹ I₂`, which is all that the maps on sections depend on, has to be deduced
from the commutative square rather than from a factorisation.

The maps of sheaves are built with `Stacks.Sites.Conormal.sheafifyLiftDesc` from their formulas
on presheaf sections, and the target is the restriction of scalars of the second sheaf along
`β`, which leaves sections and restriction maps alone and changes only the module structure.

## References

* [Stacks Project, Tag 08TS](https://stacks.math.columbia.edu/tag/08TS), the conormal sequence.
* [Stacks Project, Tag 08TR](https://stacks.math.columbia.edu/tag/08TR), the corresponding
  functoriality of the sheaf of relative differentials.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TensorProduct

universe v u w z

namespace Stacks.Sites.Conormal

variable {C : Type u} [Category.{v} C]

/-! ### The maps of sheaves of modules -/

section Sheaves

open AlgebraicGeometry.SheafOfModules (underlyingRingHomOfSite)

/-- The underlying morphisms of presheaves of a commutative square of morphisms of sheaves of
commutative rings. -/
lemma hom_of_square {K : GrothendieckTopology C} {S₁ S₂ T₁ T₂ : Sheaf K CommRingCat.{w}}
    {φ₁ : S₁ ⟶ T₁} {φ₂ : S₂ ⟶ T₂} {ψ : S₁ ⟶ S₂} {β : T₁ ⟶ T₂} (e : ψ ≫ φ₂ = φ₁ ≫ β) :
    ψ.hom ≫ φ₂.hom = φ₁.hom ≫ β.hom :=
  congrArg (fun t : S₁ ⟶ T₂ ↦ t.hom) e

variable (J : GrothendieckTopology C) [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]

variable (R₁ R₂ A₁ A₂ B₁ B₂ : Sheaf J CommRingCat.{w}) (a₁ : R₁ ⟶ A₁) (a₂ : R₂ ⟶ A₂)
  (φ₁ : A₁ ⟶ B₁) (φ₂ : A₂ ⟶ B₂) (ψ : A₁ ⟶ A₂) (β : B₁ ⟶ B₂) (ρ : R₁ ⟶ R₂)
  (hsq : ψ ≫ φ₂ = φ₁ ≫ β) (ha : ρ ≫ a₂ = a₁ ≫ ψ)
  [Presheaf.IsLocallySurjective J φ₁.hom] [Presheaf.IsLocallySurjective J φ₂.hom]

include hsq in
/-- The map of conormal sheaves `I₁/I₁² ⟶ I₂/I₂²` induced by a commutative square
`ψ ≫ φ₂ = φ₁ ≫ β`, linear over `B₁`. -/
noncomputable def conormalSheafMapOfSquare :
    conormalSheaf.{v, u, w, z} J A₁ B₁ φ₁ ⟶
      (_root_.SheafOfModules.restrictScalars (underlyingRingHomOfSite β)).obj
        (conormalSheaf.{v, u, w, z} J A₂ B₂ φ₂) := by
  refine sheafifyLiftDesc.{v, u, w, z} J A₁ B₁ φ₁ (conormalPresheaf φ₁.hom) _
    (fun X c ↦ toAssociatedModule.{v, u, w, z} J A₂ B₂ φ₂ (conormalPresheaf φ₂.hom) X
      (conormalMapOfSquare φ₁.hom φ₂.hom ψ.hom β.hom (hom_of_square hsq) X c)) ?_ ?_ ?_
  · intro X c c'
    exact (congrArg (toAssociatedModule.{v, u, w, z} J A₂ B₂ φ₂ (conormalPresheaf φ₂.hom) X)
      (map_add (conormalMapOfSquare φ₁.hom φ₂.hom ψ.hom β.hom (hom_of_square hsq) X) c c')).trans
      (toAssociatedModule_add.{v, u, w, z} J A₂ B₂ φ₂ (conormalPresheaf φ₂.hom) X _ _)
  · intro X r c
    refine (congrArg (toAssociatedModule.{v, u, w, z} J A₂ B₂ φ₂ (conormalPresheaf φ₂.hom) X)
      (map_smulₛₗ (conormalMapOfSquare φ₁.hom φ₂.hom ψ.hom β.hom
        (hom_of_square hsq) X) r c)).trans ?_
    refine (toAssociatedModule_smul.{v, u, w, z} J A₂ B₂ φ₂
      (conormalPresheaf φ₂.hom) X _ _).trans ?_
    exact congrArg (fun s : (Stacks.SheafOfModules.Tensor.ringSheaf B₂).obj.obj X ↦
      s • toAssociatedModule.{v, u, w, z} J A₂ B₂ φ₂ (conormalPresheaf φ₂.hom) X
        (conormalMapOfSquare φ₁.hom φ₂.hom ψ.hom β.hom (hom_of_square hsq) X c))
      (quotientToTarget_quotientMapOfSquare φ₁.hom φ₂.hom ψ.hom β.hom (hom_of_square hsq) X r)
  · intro X Y f c
    exact (congrArg (toAssociatedModule.{v, u, w, z} J A₂ B₂ φ₂ (conormalPresheaf φ₂.hom) Y)
      (conormalMapOfSquare_naturality φ₁.hom φ₂.hom ψ.hom β.hom (hom_of_square hsq) f c)).trans
      (toAssociatedModule_map.{v, u, w, z} J A₂ B₂ φ₂ (conormalPresheaf φ₂.hom) f _)

include hsq in
/-- The induced map sends the conormal class of `f` to the conormal class of `ψ f`. -/
lemma conormalSheafMapOfSquare_conormalClass (X : Cᵒᵖ) (x : kernelIdeal φ₁.hom X) :
    ((conormalSheafMapOfSquare.{v, u, w, z} J A₁ A₂ B₁ B₂ φ₁ φ₂ ψ β hsq).val.app X)
      (conormalClass.{v, u, w, z} J R₁ A₁ B₁ a₁ φ₁ X x) =
      conormalClass.{v, u, w, z} J R₂ A₂ B₂ a₂ φ₂ X
        ⟨ψ.hom.app X x, kernelIdeal_le_comap_square φ₁.hom φ₂.hom ψ.hom β.hom
          (hom_of_square hsq) X x.2⟩ := by
  apply sheafifyLiftDesc_toAssociatedModule.{v, u, w, z}

include hsq ha in
/-- The map `B₁ ⊗[A₁] Ω[A₁/R₁] ⟶ B₂ ⊗[A₂] Ω[A₂/R₂]` induced by a commutative square
`ψ ≫ φ₂ = φ₁ ≫ β` over a square `ρ ≫ a₂ = a₁ ≫ ψ` of base rings, linear over `B₁`. -/
noncomputable def tensorSheafMapOfSquare :
    tensorDifferentialsSheaf.{v, u, w, z} J R₁ A₁ B₁ a₁ φ₁ ⟶
      (_root_.SheafOfModules.restrictScalars (underlyingRingHomOfSite β)).obj
        (tensorDifferentialsSheaf.{v, u, w, z} J R₂ A₂ B₂ a₂ φ₂) := by
  refine sheafifyLiftDesc.{v, u, w, z} J A₁ B₁ φ₁ (tensorPresheaf φ₁.hom a₁.hom) _
    (fun X t ↦ toAssociatedModule.{v, u, w, z} J A₂ B₂ φ₂ (tensorPresheaf φ₂.hom a₂.hom) X
      (tensorMapOfSquareₛₗ φ₁.hom φ₂.hom ψ.hom β.hom (hom_of_square hsq) a₁.hom a₂.hom ρ.hom
        (hom_of_square ha) X t)) ?_ ?_ ?_
  · intro X t t'
    exact (congrArg (toAssociatedModule.{v, u, w, z} J A₂ B₂ φ₂
        (tensorPresheaf φ₂.hom a₂.hom) X)
      (map_add (tensorMapOfSquareₛₗ φ₁.hom φ₂.hom ψ.hom β.hom (hom_of_square hsq) a₁.hom a₂.hom
        ρ.hom (hom_of_square ha) X) t t')).trans
      (toAssociatedModule_add.{v, u, w, z} J A₂ B₂ φ₂ (tensorPresheaf φ₂.hom a₂.hom) X _ _)
  · intro X r t
    refine (congrArg (toAssociatedModule.{v, u, w, z} J A₂ B₂ φ₂
        (tensorPresheaf φ₂.hom a₂.hom) X)
      (tensorMapOfSquareₛₗ_smul φ₁.hom φ₂.hom ψ.hom β.hom (hom_of_square hsq) a₁.hom a₂.hom
        ρ.hom (hom_of_square ha) X r t)).trans ?_
    refine (toAssociatedModule_smul.{v, u, w, z} J A₂ B₂ φ₂
      (tensorPresheaf φ₂.hom a₂.hom) X _ _).trans ?_
    exact congrArg (fun s : (Stacks.SheafOfModules.Tensor.ringSheaf B₂).obj.obj X ↦
      s • toAssociatedModule.{v, u, w, z} J A₂ B₂ φ₂ (tensorPresheaf φ₂.hom a₂.hom) X
        (tensorMapOfSquareₛₗ φ₁.hom φ₂.hom ψ.hom β.hom (hom_of_square hsq) a₁.hom a₂.hom ρ.hom
          (hom_of_square ha) X t))
      (quotientToTarget_quotientMapOfSquare φ₁.hom φ₂.hom ψ.hom β.hom (hom_of_square hsq) X r)
  · intro X Y f t
    exact (congrArg (toAssociatedModule.{v, u, w, z} J A₂ B₂ φ₂
        (tensorPresheaf φ₂.hom a₂.hom) Y)
      (tensorMapOfSquareₛₗ_naturality φ₁.hom φ₂.hom ψ.hom β.hom (hom_of_square hsq) a₁.hom
        a₂.hom ρ.hom (hom_of_square ha) f t)).trans
      (toAssociatedModule_map.{v, u, w, z} J A₂ B₂ φ₂ (tensorPresheaf φ₂.hom a₂.hom) f _)

include hsq ha in
/-- The induced map sends `1 ⊗ d f` to `1 ⊗ d (ψ f)`. -/
lemma tensorSheafMapOfSquare_tensorDifferential (X : Cᵒᵖ) (x : A₁.obj.obj X) :
    ((tensorSheafMapOfSquare.{v, u, w, z} J R₁ R₂ A₁ A₂ B₁ B₂ a₁ a₂ φ₁ φ₂ ψ β ρ
        hsq ha).val.app X)
      (tensorDifferential.{v, u, w, z} J R₁ A₁ B₁ a₁ φ₁ X x) =
      tensorDifferential.{v, u, w, z} J R₂ A₂ B₂ a₂ φ₂ X (ψ.hom.app X x) := by
  have h : ((tensorSheafMapOfSquare.{v, u, w, z} J R₁ R₂ A₁ A₂ B₁ B₂ a₁ a₂ φ₁ φ₂ ψ β ρ
        hsq ha).val.app X)
      (tensorDifferential.{v, u, w, z} J R₁ A₁ B₁ a₁ φ₁ X x) =
      toAssociatedModule.{v, u, w, z} J A₂ B₂ φ₂ (tensorPresheaf φ₂.hom a₂.hom) X
        (tensorMapOfSquareₛₗ φ₁.hom φ₂.hom ψ.hom β.hom (hom_of_square hsq) a₁.hom a₂.hom ρ.hom
          (hom_of_square ha) X
          ((1 : A₁.obj.obj X ⧸ kernelIdeal φ₁.hom X) ⊗ₜ[A₁.obj.obj X]
            CommRingCat.KaehlerDifferential.d (f := a₁.hom.app X) x)) := by
    apply sheafifyLiftDesc_toAssociatedModule.{v, u, w, z}
  refine h.trans ?_
  refine congrArg (toAssociatedModule.{v, u, w, z} J A₂ B₂ φ₂
    (tensorPresheaf φ₂.hom a₂.hom) X) ?_
  refine (TensorProduct.map_tmul _ _ _ _).trans ?_
  exact congrArg₂ (fun b (ω : (differentialsPresheaf a₂.hom).obj X) ↦
      b ⊗ₜ[A₂.obj.obj X] ω)
    (map_one (quotientMapOfSquare φ₁.hom φ₂.hom ψ.hom β.hom (hom_of_square hsq) X).hom)
    (differentialsMapOfSquare_d ψ.hom a₁.hom a₂.hom ρ.hom (hom_of_square ha) X x)

include hsq ha in
/-- The left-hand maps of the two conormal sequences commute with the maps induced by a
commutative square. -/
lemma conormalSequence_f_naturality_square :
    (conormalSequence.{v, u, w, z} J R₁ A₁ B₁ a₁ φ₁).f ≫
        tensorSheafMapOfSquare.{v, u, w, z} J R₁ R₂ A₁ A₂ B₁ B₂ a₁ a₂ φ₁ φ₂ ψ β ρ hsq ha =
      conormalSheafMapOfSquare.{v, u, w, z} J A₁ A₂ B₁ B₂ φ₁ φ₂ ψ β hsq ≫
        (_root_.SheafOfModules.restrictScalars (underlyingRingHomOfSite β)).map
          (conormalSequence.{v, u, w, z} J R₂ A₂ B₂ a₂ φ₂).f := by
  apply sheafify_hom_ext.{v, u, w, z} J A₁ B₁ φ₁ (conormalPresheaf φ₁.hom)
  intro X c
  obtain ⟨c, rfl⟩ := (kernelIdeal φ₁.hom X).toCotangent_surjective c
  refine Eq.trans (congrArg
    ((tensorSheafMapOfSquare.{v, u, w, z} J R₁ R₂ A₁ A₂ B₁ B₂ a₁ a₂ φ₁ φ₂ ψ β ρ
      hsq ha).val.app X)
    (conormalSequence_f_class.{v, u, w, z} J R₁ A₁ B₁ a₁ φ₁ X c)) ?_
  refine Eq.trans (tensorSheafMapOfSquare_tensorDifferential.{v, u, w, z}
    J R₁ R₂ A₁ A₂ B₁ B₂ a₁ a₂ φ₁ φ₂ ψ β ρ hsq ha X c) ?_
  refine Eq.symm (Eq.trans (congrArg
    ((conormalSequence.{v, u, w, z} J R₂ A₂ B₂ a₂ φ₂).f.val.app X)
    (conormalSheafMapOfSquare_conormalClass.{v, u, w, z} J R₁ R₂ A₁ A₂ B₁ B₂ a₁ a₂
      φ₁ φ₂ ψ β hsq X c)) ?_)
  exact conormalSequence_f_class.{v, u, w, z} J R₂ A₂ B₂ a₂ φ₂ X _

end Sheaves

/-! ### Composition of two squares -/

/-- Two commutative squares side by side compose to the outer rectangle. -/
lemma square_comp {D : Type*} [Category D] {A₁ A₂ A₃ B₁ B₂ B₃ : D} {φ₁ : A₁ ⟶ B₁}
    {φ₂ : A₂ ⟶ B₂} {φ₃ : A₃ ⟶ B₃} {ψ : A₁ ⟶ A₂} {ψ' : A₂ ⟶ A₃} {β : B₁ ⟶ B₂} {β' : B₂ ⟶ B₃}
    (hsq : ψ ≫ φ₂ = φ₁ ≫ β) (hsq' : ψ' ≫ φ₃ = φ₂ ≫ β') :
    (ψ ≫ ψ') ≫ φ₃ = φ₁ ≫ β ≫ β' := by
  rw [Category.assoc, hsq', ← Category.assoc, hsq, Category.assoc]

section PresheafComp

variable {A₁ A₂ A₃ B₁ B₂ B₃ : Cᵒᵖ ⥤ CommRingCat.{w}}
  (φ₁ : A₁ ⟶ B₁) (φ₂ : A₂ ⟶ B₂) (φ₃ : A₃ ⟶ B₃)
  (ψ : A₁ ⟶ A₂) (ψ' : A₂ ⟶ A₃) (β : B₁ ⟶ B₂) (β' : B₂ ⟶ B₃)
  (hsq : ψ ≫ φ₂ = φ₁ ≫ β) (hsq' : ψ' ≫ φ₃ = φ₂ ≫ β')

include hsq hsq' in
/-- The maps `A₁(U)/I₁(U) ⟶ A₂(U)/I₂(U) ⟶ A₃(U)/I₃(U)` attached to two commutative squares
compose to the one attached to the outer rectangle. -/
lemma quotientMapOfSquare_comp (X : Cᵒᵖ) (b : (quotientPresheaf φ₁).obj X) :
    quotientMapOfSquare φ₂ φ₃ ψ' β' hsq' X (quotientMapOfSquare φ₁ φ₂ ψ β hsq X b) =
      quotientMapOfSquare φ₁ φ₃ (ψ ≫ ψ') (β ≫ β') (square_comp hsq hsq') X b := by
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
  rfl

include hsq hsq' in
/-- The maps `I₁(U)/I₁(U)² → I₂(U)/I₂(U)² → I₃(U)/I₃(U)²` attached to two commutative squares
compose to the one attached to the outer rectangle. -/
lemma conormalMapOfSquare_comp (X : Cᵒᵖ) (c : (conormalPresheaf φ₁).obj X) :
    conormalMapOfSquare φ₂ φ₃ ψ' β' hsq' X (conormalMapOfSquare φ₁ φ₂ ψ β hsq X c) =
      conormalMapOfSquare φ₁ φ₃ (ψ ≫ ψ') (β ≫ β') (square_comp hsq hsq') X c := by
  obtain ⟨c, rfl⟩ := (kernelIdeal φ₁ X).toCotangent_surjective c
  rfl

section DifferentialsComp

variable {R₁ R₂ R₃ : Cᵒᵖ ⥤ CommRingCat.{w}} (a₁ : R₁ ⟶ A₁) (a₂ : R₂ ⟶ A₂) (a₃ : R₃ ⟶ A₃)
  (ρ : R₁ ⟶ R₂) (ρ' : R₂ ⟶ R₃) (ha : ρ ≫ a₂ = a₁ ≫ ψ) (ha' : ρ' ≫ a₃ = a₂ ≫ ψ')

include ha ha' in
/-- The maps `Ω[A₁(U)/R₁(U)] → Ω[A₂(U)/R₂(U)] → Ω[A₃(U)/R₃(U)]` attached to two commutative
squares of base rings compose to the one attached to the outer rectangle. -/
lemma differentialsMapOfSquare_comp (X : Cᵒᵖ) (ω : (differentialsPresheaf a₁).obj X) :
    differentialsMapOfSquare ψ' a₂ a₃ ρ' ha' X (differentialsMapOfSquare ψ a₁ a₂ ρ ha X ω) =
      differentialsMapOfSquare (ψ ≫ ψ') a₁ a₃ (ρ ≫ ρ') (square_comp ha ha') X ω := by
  let := (a₁.app X).hom.toAlgebra
  have mem : ω ∈ Submodule.span (A₁.obj X)
      (Set.range (KaehlerDifferential.D (R₁.obj X) (A₁.obj X))) := by
    rw [KaehlerDifferential.span_range_derivation]; trivial
  induction mem using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨x, rfl⟩ := hx
      show differentialsMapOfSquare ψ' a₂ a₃ ρ' ha' X (differentialsMapOfSquare ψ a₁ a₂ ρ ha X
            (CommRingCat.KaehlerDifferential.d (f := a₁.app X) x)) =
          differentialsMapOfSquare (ψ ≫ ψ') a₁ a₃ (ρ ≫ ρ') (square_comp ha ha') X
            (CommRingCat.KaehlerDifferential.d (f := a₁.app X) x)
      rw [differentialsMapOfSquare_d, differentialsMapOfSquare_d, differentialsMapOfSquare_d]
      rfl
  | zero => rw [map_zero, map_zero, map_zero]
  | add x y hx hy ihx ihy => rw [map_add, map_add, map_add, ihx, ihy]
  | smul r ω hω ih => rw [map_smulₛₗ, map_smulₛₗ, map_smulₛₗ, ih]; rfl

include hsq hsq' ha ha' in
/-- The maps on `(A/I) ⊗[A] Ω[A/R]` attached to two commutative squares compose to the one
attached to the outer rectangle. -/
lemma tensorMapOfSquareₛₗ_comp (X : Cᵒᵖ)
    (t : (A₁.obj X ⧸ kernelIdeal φ₁ X) ⊗[A₁.obj X] ((differentialsPresheaf a₁).obj X)) :
    tensorMapOfSquareₛₗ φ₂ φ₃ ψ' β' hsq' a₂ a₃ ρ' ha' X
        (tensorMapOfSquareₛₗ φ₁ φ₂ ψ β hsq a₁ a₂ ρ ha X t) =
      tensorMapOfSquareₛₗ φ₁ φ₃ (ψ ≫ ψ') (β ≫ β') (square_comp hsq hsq') a₁ a₃ (ρ ≫ ρ')
        (square_comp ha ha') X t := by
  induction t using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero, map_zero]
  | tmul b ω =>
    refine (congrArg (tensorMapOfSquareₛₗ φ₂ φ₃ ψ' β' hsq' a₂ a₃ ρ' ha' X)
      (TensorProduct.map_tmul _ _ b ω)).trans ?_
    refine (TensorProduct.map_tmul _ _ _ _).trans ?_
    refine Eq.trans ?_ (TensorProduct.map_tmul _ _ b ω).symm
    exact congrArg₂ (fun b (ω : (differentialsPresheaf a₃).obj X) ↦ b ⊗ₜ[A₃.obj X] ω)
      (quotientMapOfSquare_comp φ₁ φ₂ φ₃ ψ ψ' β β' hsq hsq' X b)
      (differentialsMapOfSquare_comp ψ ψ' a₁ a₂ a₃ ρ ρ' ha ha' X ω)
  | add x y hx hy => rw [map_add, map_add, map_add, hx, hy]

end DifferentialsComp

end PresheafComp

/-! ### Composition of the maps of sheaves of modules -/

section SheavesComp

open AlgebraicGeometry.SheafOfModules (underlyingRingHomOfSite)

variable (J : GrothendieckTopology C) [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- Restriction of scalars along a composite of morphisms of sheaves of rings is the composite
of the two restrictions of scalars. -/
lemma restrictScalars_comp {S₁ S₂ S₃ : Sheaf J RingCat.{w}} (α : S₁ ⟶ S₂) (α' : S₂ ⟶ S₃) :
    _root_.SheafOfModules.restrictScalars.{max w u v z} (α ≫ α') =
      _root_.SheafOfModules.restrictScalars.{max w u v z} α' ⋙
        _root_.SheafOfModules.restrictScalars.{max w u v z} α :=
  rfl

variable (R₁ R₂ R₃ A₁ A₂ A₃ B₁ B₂ B₃ : Sheaf J CommRingCat.{w})
  (a₁ : R₁ ⟶ A₁) (a₂ : R₂ ⟶ A₂) (a₃ : R₃ ⟶ A₃)
  (φ₁ : A₁ ⟶ B₁) (φ₂ : A₂ ⟶ B₂) (φ₃ : A₃ ⟶ B₃)
  (ψ : A₁ ⟶ A₂) (ψ' : A₂ ⟶ A₃) (β : B₁ ⟶ B₂) (β' : B₂ ⟶ B₃) (ρ : R₁ ⟶ R₂) (ρ' : R₂ ⟶ R₃)
  (hsq : ψ ≫ φ₂ = φ₁ ≫ β) (hsq' : ψ' ≫ φ₃ = φ₂ ≫ β')
  (ha : ρ ≫ a₂ = a₁ ≫ ψ) (ha' : ρ' ≫ a₃ = a₂ ≫ ψ')
  [Presheaf.IsLocallySurjective J φ₁.hom] [Presheaf.IsLocallySurjective J φ₂.hom]
  [Presheaf.IsLocallySurjective J φ₃.hom]

include hsq in
/-- On a section of `I₁/I₁²` coming from the presheaf `I₁(U)/I₁(U)²`, the map of conormal
sheaves is the map of conormal modules. -/
lemma conormalSheafMapOfSquare_toAssociatedModule (X : Cᵒᵖ)
    (c : (conormalPresheaf φ₁.hom).obj X) :
    ((conormalSheafMapOfSquare.{v, u, w, z} J A₁ A₂ B₁ B₂ φ₁ φ₂ ψ β hsq).val.app X)
        (toAssociatedModule.{v, u, w, z} J A₁ B₁ φ₁ (conormalPresheaf φ₁.hom) X c) =
      toAssociatedModule.{v, u, w, z} J A₂ B₂ φ₂ (conormalPresheaf φ₂.hom) X
        (conormalMapOfSquare φ₁.hom φ₂.hom ψ.hom β.hom (hom_of_square hsq) X c) := by
  apply sheafifyLiftDesc_toAssociatedModule.{v, u, w, z}

include hsq hsq' in
/-- The maps of conormal sheaves `I₁/I₁² ⟶ I₂/I₂² ⟶ I₃/I₃²` attached to two commutative
squares compose to the one attached to the outer rectangle. -/
lemma conormalSheafMapOfSquare_comp :
    conormalSheafMapOfSquare.{v, u, w, z} J A₁ A₂ B₁ B₂ φ₁ φ₂ ψ β hsq ≫
        (_root_.SheafOfModules.restrictScalars (underlyingRingHomOfSite β)).map
          (conormalSheafMapOfSquare.{v, u, w, z} J A₂ A₃ B₂ B₃ φ₂ φ₃ ψ' β' hsq') =
      conormalSheafMapOfSquare.{v, u, w, z} J A₁ A₃ B₁ B₃ φ₁ φ₃ (ψ ≫ ψ') (β ≫ β')
        (square_comp hsq hsq') := by
  apply sheafify_hom_ext.{v, u, w, z} J A₁ B₁ φ₁ (conormalPresheaf φ₁.hom)
  intro X c
  refine Eq.trans (congrArg
    (fun t ↦ ((conormalSheafMapOfSquare.{v, u, w, z} J A₂ A₃ B₂ B₃ φ₂ φ₃ ψ' β' hsq').val.app X) t)
    (conormalSheafMapOfSquare_toAssociatedModule.{v, u, w, z}
      J A₁ A₂ B₁ B₂ φ₁ φ₂ ψ β hsq X c)) ?_
  refine Eq.trans (conormalSheafMapOfSquare_toAssociatedModule.{v, u, w, z}
    J A₂ A₃ B₂ B₃ φ₂ φ₃ ψ' β' hsq' X
    (conormalMapOfSquare φ₁.hom φ₂.hom ψ.hom β.hom (hom_of_square hsq) X c)) ?_
  refine Eq.trans ?_ (conormalSheafMapOfSquare_toAssociatedModule.{v, u, w, z}
    J A₁ A₃ B₁ B₃ φ₁ φ₃ (ψ ≫ ψ') (β ≫ β') (square_comp hsq hsq') X c).symm
  exact congrArg (toAssociatedModule.{v, u, w, z} J A₃ B₃ φ₃ (conormalPresheaf φ₃.hom) X)
    (conormalMapOfSquare_comp φ₁.hom φ₂.hom φ₃.hom ψ.hom ψ'.hom β.hom β'.hom
      (hom_of_square hsq) (hom_of_square hsq') X c)

include hsq ha in
/-- On a section of `B₁ ⊗[A₁] Ω[A₁/R₁]` coming from the presheaf
`(A₁(U)/I₁(U)) ⊗[A₁(U)] Ω[A₁(U)/R₁(U)]`, the map of tensor sheaves is the map of tensor
products. -/
lemma tensorSheafMapOfSquare_toAssociatedModule (X : Cᵒᵖ)
    (t : (tensorPresheaf φ₁.hom a₁.hom).obj X) :
    ((tensorSheafMapOfSquare.{v, u, w, z} J R₁ R₂ A₁ A₂ B₁ B₂ a₁ a₂ φ₁ φ₂ ψ β ρ
        hsq ha).val.app X)
        (toAssociatedModule.{v, u, w, z} J A₁ B₁ φ₁ (tensorPresheaf φ₁.hom a₁.hom) X t) =
      toAssociatedModule.{v, u, w, z} J A₂ B₂ φ₂ (tensorPresheaf φ₂.hom a₂.hom) X
        (tensorMapOfSquareₛₗ φ₁.hom φ₂.hom ψ.hom β.hom (hom_of_square hsq) a₁.hom a₂.hom ρ.hom
          (hom_of_square ha) X t) := by
  apply sheafifyLiftDesc_toAssociatedModule.{v, u, w, z}

include hsq hsq' ha ha' in
/-- The maps `B₁ ⊗[A₁] Ω[A₁/R₁] ⟶ B₂ ⊗[A₂] Ω[A₂/R₂] ⟶ B₃ ⊗[A₃] Ω[A₃/R₃]` attached to two
commutative squares compose to the one attached to the outer rectangle. -/
lemma tensorSheafMapOfSquare_comp :
    tensorSheafMapOfSquare.{v, u, w, z} J R₁ R₂ A₁ A₂ B₁ B₂ a₁ a₂ φ₁ φ₂ ψ β ρ hsq ha ≫
        (_root_.SheafOfModules.restrictScalars (underlyingRingHomOfSite β)).map
          (tensorSheafMapOfSquare.{v, u, w, z} J R₂ R₃ A₂ A₃ B₂ B₃ a₂ a₃ φ₂ φ₃ ψ' β' ρ'
            hsq' ha') =
      tensorSheafMapOfSquare.{v, u, w, z} J R₁ R₃ A₁ A₃ B₁ B₃ a₁ a₃ φ₁ φ₃ (ψ ≫ ψ') (β ≫ β')
        (ρ ≫ ρ') (square_comp hsq hsq') (square_comp ha ha') := by
  apply sheafify_hom_ext.{v, u, w, z} J A₁ B₁ φ₁ (tensorPresheaf φ₁.hom a₁.hom)
  intro X t
  refine Eq.trans (congrArg
    (fun y ↦ ((tensorSheafMapOfSquare.{v, u, w, z} J R₂ R₃ A₂ A₃ B₂ B₃ a₂ a₃ φ₂ φ₃ ψ' β' ρ'
      hsq' ha').val.app X) y)
    (tensorSheafMapOfSquare_toAssociatedModule.{v, u, w, z}
      J R₁ R₂ A₁ A₂ B₁ B₂ a₁ a₂ φ₁ φ₂ ψ β ρ hsq ha X t)) ?_
  refine Eq.trans (tensorSheafMapOfSquare_toAssociatedModule.{v, u, w, z}
    J R₂ R₃ A₂ A₃ B₂ B₃ a₂ a₃ φ₂ φ₃ ψ' β' ρ' hsq' ha' X
    (tensorMapOfSquareₛₗ φ₁.hom φ₂.hom ψ.hom β.hom (hom_of_square hsq) a₁.hom a₂.hom ρ.hom
      (hom_of_square ha) X t)) ?_
  refine Eq.trans ?_ (tensorSheafMapOfSquare_toAssociatedModule.{v, u, w, z}
    J R₁ R₃ A₁ A₃ B₁ B₃ a₁ a₃ φ₁ φ₃ (ψ ≫ ψ') (β ≫ β') (ρ ≫ ρ') (square_comp hsq hsq')
    (square_comp ha ha') X t).symm
  exact congrArg
    (toAssociatedModule.{v, u, w, z} J A₃ B₃ φ₃ (tensorPresheaf φ₃.hom a₃.hom) X)
    (tensorMapOfSquareₛₗ_comp φ₁.hom φ₂.hom φ₃.hom ψ.hom ψ'.hom β.hom β'.hom
      (hom_of_square hsq) (hom_of_square hsq') a₁.hom a₂.hom a₃.hom ρ.hom ρ'.hom
      (hom_of_square ha) (hom_of_square ha') X t)

end SheavesComp

/-! ### Dependence on the square alone -/

section Congr

open AlgebraicGeometry.SheafOfModules (underlyingRingHomOfSite)

variable (J : GrothendieckTopology C) [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]

/-- The map of conormal sheaves attached to a commutative square depends on the square only
through its four maps. -/
lemma conormalSheafMapOfSquare_congr (A₁ A₂ B₁ B₂ : Sheaf J CommRingCat.{w})
    (φ₁ : A₁ ⟶ B₁) (φ₂ : A₂ ⟶ B₂) {ψ ψ₂ : A₁ ⟶ A₂} (β : B₁ ⟶ B₂)
    [Presheaf.IsLocallySurjective J φ₁.hom] [Presheaf.IsLocallySurjective J φ₂.hom]
    (hsq : ψ ≫ φ₂ = φ₁ ≫ β) (hsq₂ : ψ₂ ≫ φ₂ = φ₁ ≫ β) (h : ψ = ψ₂) :
    conormalSheafMapOfSquare.{v, u, w, z} J A₁ A₂ B₁ B₂ φ₁ φ₂ ψ β hsq =
      conormalSheafMapOfSquare.{v, u, w, z} J A₁ A₂ B₁ B₂ φ₁ φ₂ ψ₂ β hsq₂ := by
  subst h
  rfl

/-- The map on the scalar extensions of the differentials attached to a commutative square
depends on the square only through its maps. -/
lemma tensorSheafMapOfSquare_congr (R₁ R₂ A₁ A₂ B₁ B₂ : Sheaf J CommRingCat.{w})
    (a₁ : R₁ ⟶ A₁) (a₂ : R₂ ⟶ A₂) (φ₁ : A₁ ⟶ B₁) (φ₂ : A₂ ⟶ B₂) {ψ ψ₂ : A₁ ⟶ A₂}
    (β : B₁ ⟶ B₂) {ρ ρ₂ : R₁ ⟶ R₂}
    [Presheaf.IsLocallySurjective J φ₁.hom] [Presheaf.IsLocallySurjective J φ₂.hom]
    (hsq : ψ ≫ φ₂ = φ₁ ≫ β) (ha : ρ ≫ a₂ = a₁ ≫ ψ)
    (hsq₂ : ψ₂ ≫ φ₂ = φ₁ ≫ β) (ha₂ : ρ₂ ≫ a₂ = a₁ ≫ ψ₂) (hψ : ψ = ψ₂) (hρ : ρ = ρ₂) :
    tensorSheafMapOfSquare.{v, u, w, z} J R₁ R₂ A₁ A₂ B₁ B₂ a₁ a₂ φ₁ φ₂ ψ β ρ hsq ha =
      tensorSheafMapOfSquare.{v, u, w, z} J R₁ R₂ A₁ A₂ B₁ B₂ a₁ a₂ φ₁ φ₂ ψ₂ β ρ₂ hsq₂ ha₂ := by
  subst hψ
  subst hρ
  rfl

end Congr

end Stacks.Sites.Conormal
