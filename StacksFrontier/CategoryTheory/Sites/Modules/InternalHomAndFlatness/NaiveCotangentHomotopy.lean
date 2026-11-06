module

public import Mathlib.Algebra.Homology.Homotopy
public import StacksFrontier.CategoryTheory.Sites.Modules.ConormalSequence
public import StacksFrontier.CategoryTheory.Sites.Modules.InternalHomAndFlatness.NaiveCotangent

/-!
# Two morphisms of presentations induce homotopic maps of naive cotangent complexes

Let `A ⟶ B` be a morphism of sheaves of commutative rings on a site and let `α₁ : E₁ ⟶ B` and
`α₂ : E₂ ⟶ B` be two families of generators, presenting `B` as a quotient of the free
`A`-algebras `A[E₁]` and `A[E₂]`. A morphism `h : E₁ ⟶ E₂` of families of generators, that is
one with `h ≫ α₂ = α₁`, induces a chain map `NL(α₁) ⟶ NL(α₂)` of naive cotangent complexes. Two
such morphisms `h` and `h'` induce homotopic chain maps: writing `K₂` for the kernel of
`A[E₂] ⟶ B`, the homotopy is the map of sheaves of `B`-modules

`B ⊗_{A[E₁]} Ω_{A[E₁]/A} ⟶ K₂/K₂²`

whose value on the local section `b ⊗ d x` is `b · (h(x) - h'(x))`. This is the sheaf analogue
of part (2) of Stacks 00S1.

The objectwise constructions are given for two morphisms of presentations over a commutative
square `ψ ≫ φ₂ = φ₁ ≫ β` and a square of base rings `ρ : R₁ ⟶ R₂` (the `…OfSquare` family), and
specialised to `β = 𝟙`, `ρ = 𝟙` (the `…OfFac` family).

## Main definitions

* `Stacks.Sites.Conormal.cotangentDiffOfSquare` and
  `Stacks.Sites.Conormal.tensorHomotopyOfSquare`: the derivation and the homotopy on local
  sections, in general form.
* `Stacks.Sites.Conormal.cotangentDiffOfFac`: the derivation `x ↦ ψ(x) - ψ'(x) mod I₂²`.
* `Stacks.Sites.Conormal.differentialsHomotopyOfFac`: the map `Ω_{A₁/R} ⟶ I₂/I₂²` it
  classifies.
* `Stacks.Sites.Conormal.tensorHomotopyOfFac`: the homotopy on local sections.
* `Stacks.Sites.Conormal.conormalHomotopyOfFac`: the homotopy as a morphism of sheaves of
  `B`-modules.
* `Stacks.SheafOfModules.presentationNullHomotopy` and
  `Stacks.SheafOfModules.presentationNaiveCotangentHomotopyHom`: the same homotopy for two
  morphisms of presentations, and its transport into the complexes `NL(α₁)` and `NL(α₂)`.
* `Stacks.SheafOfModules.presentationNaiveCotangentComplexHomotopy`: the homotopy between the
  chain maps `NL(α₁) ⟶ NL(α₂)` induced by two morphisms of presentations.

## Main results

* `Stacks.Sites.Conormal.conormalSheafMapOfFac_eq_add` and
  `Stacks.Sites.Conormal.tensorSheafMapOfFac_eq_add`: the two homotopy relations, in degrees
  `-1` and `0`.

## References

* [Stacks Project, Tag 00S1](https://stacks.math.columbia.edu/tag/00S1), part (2), the
  commutative algebra statement.
* [Stacks Project, Tag 08TW](https://stacks.math.columbia.edu/tag/08TW), the naive cotangent
  complex of a morphism of sheaves of rings.
* [Stacks Project, Tag 08TS](https://stacks.math.columbia.edu/tag/08TS), the conormal
  sequence.
* [Stacks Project, Tag 07VC](https://stacks.math.columbia.edu/tag/07VC), the ring-level null
  homotopy.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TensorProduct

universe v u w z

namespace Stacks.Sites.Conormal

variable {C : Type u} [Category.{v} C]
variable {B : Cᵒᵖ ⥤ CommRingCat.{w}}
variable {A₁ A₂ : Cᵒᵖ ⥤ CommRingCat.{w}} (φ₁ : A₁ ⟶ B) (φ₂ : A₂ ⟶ B) (ψ ψ' : A₁ ⟶ A₂)

section Objectwise

/-! ### The module structures the two families share -/

/-- The ring map `A₁(U) → A₂(U)/I₂(U)` through which `I₂/I₂²` becomes an `A₁`-module. -/
noncomputable def quotientCompOfFac (X : Cᵒᵖ) : A₁.obj X ⟶ (quotientPresheaf φ₂).obj X :=
  ψ.app X ≫ (toQuotient φ₂).app X

@[simp] theorem quotientCompOfFac_apply (X : Cᵒᵖ) (x : A₁.obj X) :
    quotientCompOfFac φ₂ ψ X x = Ideal.Quotient.mk (kernelIdeal φ₂ X) (ψ.app X x) := rfl

/-- `I₂/I₂²`, regarded as a module over `A₁(U)` through `ψ`. -/
noncomputable abbrev conormalRestrictOfFac (X : Cᵒᵖ) : ModuleCat.{w} (A₁.obj X) :=
  (ModuleCat.restrictScalars (quotientCompOfFac φ₂ ψ X).hom).obj ((conormalPresheaf φ₂).obj X)

/-- The `A₁(U)`-action on `I₂/I₂²` is the action of `A₂(U)/I₂(U)` through `ψ`. -/
theorem smul_conormalRestrictOfFac (X : Cᵒᵖ) (x : A₁.obj X)
    (c : conormalRestrictOfFac φ₂ ψ X) :
    x • c = Ideal.Quotient.mk (kernelIdeal φ₂ X) (ψ.app X x) •
      (show (conormalPresheaf φ₂).obj X from c) :=
  rfl

/-- The conormal class is semilinear for the action of `A₂(U)` on the kernel. -/
theorem mk_smul_toCotangent (X : Cᵒᵖ) (r : A₂.obj X) (uu : kernelIdeal φ₂ X) :
    Ideal.Quotient.mk (kernelIdeal φ₂ X) r • (kernelIdeal φ₂ X).toCotangent uu =
      (kernelIdeal φ₂ X).toCotangent (r • uu) := by
  rw [← Ideal.Quotient.algebraMap_eq, IsScalarTower.algebraMap_smul, ← map_smul]

/-- The universal derivation is additive on differences. -/
theorem kaehlerDifferential_d_sub {A₀ A₀' : CommRingCat.{w}} (g : A₀ ⟶ A₀') (y y' : A₀') :
    CommRingCat.KaehlerDifferential.d (f := g) (y - y') =
      CommRingCat.KaehlerDifferential.d (f := g) y -
        CommRingCat.KaehlerDifferential.d (f := g) y' :=
  eq_sub_of_add_eq (by
    rw [← ModuleCat.Derivation.d_add]
    exact congrArg (ModuleCat.Derivation.d (CommRingCat.KaehlerDifferential.D g))
      (sub_add_cancel y y'))

/-! ### The derivation attached to two morphisms of presentations over a square -/

section Square

variable {A₁ A₂ B₁ B₂ : Cᵒᵖ ⥤ CommRingCat.{w}} (φ₁ : A₁ ⟶ B₁) (φ₂ : A₂ ⟶ B₂)
  (ψ ψ' : A₁ ⟶ A₂) (β : B₁ ⟶ B₂)
  (hsq : ψ ≫ φ₂ = φ₁ ≫ β) (hsq' : ψ' ≫ φ₂ = φ₁ ≫ β)

include hsq hsq' in
/-- Two morphisms of presentations over the same commutative square differ by a section of
the kernel of the second presentation. -/
theorem sub_mem_kernelIdeal_square (X : Cᵒᵖ) (x : A₁.obj X) :
    ψ.app X x - ψ'.app X x ∈ kernelIdeal φ₂ X := by
  have h : φ₂.app X (ψ.app X x) = φ₂.app X (ψ'.app X x) :=
    (congrArg (fun t : A₁ ⟶ B₂ ↦ (t.app X).hom x) hsq).trans
      (congrArg (fun t : A₁ ⟶ B₂ ↦ (t.app X).hom x) hsq').symm
  simp only [kernelIdeal, RingHom.mem_ker, map_sub]
  rw [show (φ₂.app X).hom (ψ.app X x) = φ₂.app X (ψ.app X x) from rfl, h]
  simp

/-- The difference of two morphisms of presentations over a square, as a section of the kernel
of the second presentation. -/
noncomputable def subOfSquare (X : Cᵒᵖ) (x : A₁.obj X) : kernelIdeal φ₂ X :=
  ⟨ψ.app X x - ψ'.app X x, sub_mem_kernelIdeal_square φ₁ φ₂ ψ ψ' β hsq hsq' X x⟩

@[simp] theorem subOfSquare_coe (X : Cᵒᵖ) (x : A₁.obj X) :
    (subOfSquare φ₁ φ₂ ψ ψ' β hsq hsq' X x : A₂.obj X) = ψ.app X x - ψ'.app X x := rfl

/-- The difference of two morphisms of presentations over a square is additive. -/
theorem subOfSquare_add (X : Cᵒᵖ) (x y : A₁.obj X) :
    subOfSquare φ₁ φ₂ ψ ψ' β hsq hsq' X (x + y) =
      subOfSquare φ₁ φ₂ ψ ψ' β hsq hsq' X x + subOfSquare φ₁ φ₂ ψ ψ' β hsq hsq' X y :=
  Subtype.ext (by simp only [subOfSquare_coe, Submodule.coe_add, map_add]; ring)

/-- The conormal class of the difference of two morphisms of presentations over a square, as a
section of `I₂/I₂²` regarded as a module over `A₁(U)` through `ψ`. -/
noncomputable def cotangentDiffOfSquare (X : Cᵒᵖ) (x : A₁.obj X) :
    conormalRestrictOfFac φ₂ ψ X :=
  (kernelIdeal φ₂ X).toCotangent (subOfSquare φ₁ φ₂ ψ ψ' β hsq hsq' X x)

/-- The conormal class of the difference of two morphisms of presentations over a square is
additive. -/
theorem cotangentDiffOfSquare_add (X : Cᵒᵖ) (x y : A₁.obj X) :
    cotangentDiffOfSquare φ₁ φ₂ ψ ψ' β hsq hsq' X (x + y) =
      cotangentDiffOfSquare φ₁ φ₂ ψ ψ' β hsq hsq' X x +
        cotangentDiffOfSquare φ₁ φ₂ ψ ψ' β hsq hsq' X y := by
  rw [cotangentDiffOfSquare, subOfSquare_add, map_add]
  rfl

/-- The Leibniz rule: the conormal class of the difference of two morphisms of presentations
over a square is a derivation into `I₂/I₂²`. -/
theorem cotangentDiffOfSquare_mul (X : Cᵒᵖ) (x y : A₁.obj X) :
    cotangentDiffOfSquare φ₁ φ₂ ψ ψ' β hsq hsq' X (x * y) =
      x • cotangentDiffOfSquare φ₁ φ₂ ψ ψ' β hsq hsq' X y +
        y • cotangentDiffOfSquare φ₁ φ₂ ψ ψ' β hsq hsq' X x := by
  show (kernelIdeal φ₂ X).toCotangent (subOfSquare φ₁ φ₂ ψ ψ' β hsq hsq' X (x * y)) =
    Ideal.Quotient.mk (kernelIdeal φ₂ X) (ψ.app X x) •
        (kernelIdeal φ₂ X).toCotangent (subOfSquare φ₁ φ₂ ψ ψ' β hsq hsq' X y) +
      Ideal.Quotient.mk (kernelIdeal φ₂ X) (ψ.app X y) •
        (kernelIdeal φ₂ X).toCotangent (subOfSquare φ₁ φ₂ ψ ψ' β hsq hsq' X x)
  rw [mk_smul_toCotangent, mk_smul_toCotangent, ← map_add, Ideal.toCotangent_eq]
  have key : ((subOfSquare φ₁ φ₂ ψ ψ' β hsq hsq' X (x * y) : A₂.obj X) -
      (((ψ.app X).hom x • subOfSquare φ₁ φ₂ ψ ψ' β hsq hsq' X y +
        (ψ.app X).hom y • subOfSquare φ₁ φ₂ ψ ψ' β hsq hsq' X x :
          kernelIdeal φ₂ X) : A₂.obj X)) =
      -((ψ.app X x - ψ'.app X x) * (ψ.app X y - ψ'.app X y)) := by
    show (ψ.app X (x * y) - ψ'.app X (x * y)) -
      (ψ.app X x * (ψ.app X y - ψ'.app X y) + ψ.app X y * (ψ.app X x - ψ'.app X x)) = _
    simp only [map_mul]
    ring
  rw [key, pow_two]
  exact neg_mem (Ideal.mul_mem_mul (sub_mem_kernelIdeal_square φ₁ φ₂ ψ ψ' β hsq hsq' X x)
    (sub_mem_kernelIdeal_square φ₁ φ₂ ψ ψ' β hsq hsq' X y))

section Differentials

variable {R₁ R₂ : Cᵒᵖ ⥤ CommRingCat.{w}} (a₁ : R₁ ⟶ A₁) (a₂ : R₂ ⟶ A₂) (ρ : R₁ ⟶ R₂)

/-- Two morphisms of presentations over the same square of base rings agree on the image of
the base ring. -/
theorem subOfSquare_structureMap (ha : ρ ≫ a₂ = a₁ ≫ ψ) (ha' : ρ ≫ a₂ = a₁ ≫ ψ')
    (X : Cᵒᵖ) (r : R₁.obj X) :
    subOfSquare φ₁ φ₂ ψ ψ' β hsq hsq' X (a₁.app X r) = 0 :=
  Subtype.ext (by
    have h : ψ.app X (a₁.app X r) = ψ'.app X (a₁.app X r) :=
      (congrArg (fun t : R₁ ⟶ A₂ ↦ (t.app X).hom r) ha).symm.trans
        (congrArg (fun t : R₁ ⟶ A₂ ↦ (t.app X).hom r) ha')
    show ψ.app X (a₁.app X r) - ψ'.app X (a₁.app X r) = ((0 : kernelIdeal φ₂ X) : A₂.obj X)
    rw [h]
    simp)

/-- The conormal class of the difference of two morphisms of presentations over the same square
of base rings vanishes on the image of the base ring. -/
theorem cotangentDiffOfSquare_structureMap (ha : ρ ≫ a₂ = a₁ ≫ ψ) (ha' : ρ ≫ a₂ = a₁ ≫ ψ')
    (X : Cᵒᵖ) (r : R₁.obj X) :
    cotangentDiffOfSquare φ₁ φ₂ ψ ψ' β hsq hsq' X (a₁.app X r) = 0 := by
  rw [cotangentDiffOfSquare,
    subOfSquare_structureMap φ₁ φ₂ ψ ψ' β hsq hsq' a₁ a₂ ρ ha ha' X r, map_zero]
  rfl

variable (ha : ρ ≫ a₂ = a₁ ≫ ψ) (ha' : ρ ≫ a₂ = a₁ ≫ ψ')

/-- The derivation `A₁(U) → I₂(U)/I₂(U)²`, `b ↦ ψ(b) - ψ'(b) mod I₂²`, attached to two
morphisms of presentations over the same square. -/
noncomputable def derivationOfSquare (X : Cᵒᵖ) :
    (conormalRestrictOfFac φ₂ ψ X).Derivation (a₁.app X) :=
  ModuleCat.Derivation.mk (f := a₁.app X) (cotangentDiffOfSquare φ₁ φ₂ ψ ψ' β hsq hsq' X)
    (cotangentDiffOfSquare_add φ₁ φ₂ ψ ψ' β hsq hsq' X)
    (cotangentDiffOfSquare_mul φ₁ φ₂ ψ ψ' β hsq hsq' X)
    (cotangentDiffOfSquare_structureMap φ₁ φ₂ ψ ψ' β hsq hsq' a₁ a₂ ρ ha ha' X)

/-- The map `Ω[A₁(U)/R₁(U)] → I₂(U)/I₂(U)²` classifying `b ↦ ψ(b) - ψ'(b)`, semilinear over
the composite `A₁(U) → A₂(U) → A₂(U)/I₂(U)`. -/
noncomputable def differentialsHomotopyOfSquare (X : Cᵒᵖ) :
    (differentialsPresheaf a₁).obj X →ₛₗ[(quotientCompOfFac φ₂ ψ X).hom]
      (conormalPresheaf φ₂).obj X where
  toFun := (derivationOfSquare φ₁ φ₂ ψ ψ' β hsq hsq' a₁ a₂ ρ ha ha' X).desc
  map_add' := map_add (derivationOfSquare φ₁ φ₂ ψ ψ' β hsq hsq' a₁ a₂ ρ ha ha' X).desc.hom
  map_smul' := (derivationOfSquare φ₁ φ₂ ψ ψ' β hsq hsq' a₁ a₂ ρ ha ha' X).desc.hom.map_smul

@[simp] theorem differentialsHomotopyOfSquare_d (X : Cᵒᵖ) (x : A₁.obj X) :
    differentialsHomotopyOfSquare φ₁ φ₂ ψ ψ' β hsq hsq' a₁ a₂ ρ ha ha' X
        (CommRingCat.KaehlerDifferential.d x) =
      (kernelIdeal φ₂ X).toCotangent (subOfSquare φ₁ φ₂ ψ ψ' β hsq hsq' X x) :=
  ModuleCat.Derivation.desc_d _ x

/-- The map classifying `b ↦ ψ(b) - ψ'(b)` commutes with the restriction maps. -/
theorem differentialsHomotopyOfSquare_naturality {X Y : Cᵒᵖ} (f : X ⟶ Y)
    (ω : (differentialsPresheaf a₁).obj X) :
    differentialsHomotopyOfSquare φ₁ φ₂ ψ ψ' β hsq hsq' a₁ a₂ ρ ha ha' Y
        ((differentialsPresheaf a₁).restrictₛₗ f ω) =
      (conormalPresheaf φ₂).restrictₛₗ f
        (differentialsHomotopyOfSquare φ₁ φ₂ ψ ψ' β hsq hsq' a₁ a₂ ρ ha ha' X ω) := by
  let := (a₁.app X).hom.toAlgebra
  have mem : ω ∈ Submodule.span (A₁.obj X)
      (Set.range (KaehlerDifferential.D (R₁.obj X) (A₁.obj X))) := by
    rw [KaehlerDifferential.span_range_derivation]; trivial
  induction mem using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨x, rfl⟩ := hx
      have h₁ : (differentialsPresheaf a₁).map f (CommRingCat.KaehlerDifferential.d x) =
          CommRingCat.KaehlerDifferential.d (f := a₁.app Y) (A₁.map f x) :=
        PresheafOfModulesOfCommRing.DifferentialsConstruction.relativeDifferentials'_map_d a₁ f x
      show differentialsHomotopyOfSquare φ₁ φ₂ ψ ψ' β hsq hsq' a₁ a₂ ρ ha ha' Y
          ((differentialsPresheaf a₁).map f
            (CommRingCat.KaehlerDifferential.d (f := a₁.app X) x)) =
        (conormalPresheaf φ₂).map f
          (differentialsHomotopyOfSquare φ₁ φ₂ ψ ψ' β hsq hsq' a₁ a₂ ρ ha ha' X
            (CommRingCat.KaehlerDifferential.d (f := a₁.app X) x))
      rw [h₁, differentialsHomotopyOfSquare_d, differentialsHomotopyOfSquare_d]
      refine Eq.trans ?_ (cotangentMap_toCotangent _ _ (A₂.map f).hom (map_kernel φ₂ f) _).symm
      congr 1
      refine Subtype.ext ?_
      show ψ.app Y (A₁.map f x) - ψ'.app Y (A₁.map f x) = A₂.map f (ψ.app X x - ψ'.app X x)
      rw [map_sub, NatTrans.naturality_apply ψ f x, NatTrans.naturality_apply ψ' f x]
  | zero => rw [map_zero, map_zero, map_zero, map_zero]
  | add x y hx hy ihx ihy => rw [map_add, map_add, map_add, map_add, ihx, ihy]
  | smul r ω hω ih =>
      rw [map_smulₛₗ, map_smulₛₗ, ih, map_smulₛₗ, map_smulₛₗ]
      refine congrArg (fun s : (quotientPresheaf φ₂).obj Y ↦
        s • (conormalPresheaf φ₂).restrictₛₗ f
          (differentialsHomotopyOfSquare φ₁ φ₂ ψ ψ' β hsq hsq' a₁ a₂ ρ ha ha' X ω)) ?_
      show Ideal.Quotient.mk (kernelIdeal φ₂ Y) (ψ.app Y (A₁.map f r)) =
        (quotientPresheaf φ₂).map f (Ideal.Quotient.mk (kernelIdeal φ₂ X) (ψ.app X r))
      exact congrArg (Ideal.Quotient.mk (kernelIdeal φ₂ Y))
        (NatTrans.naturality_apply ψ f r)

/-! ### The homotopy on the tensor term -/

/-- The induced map on the image presheaves, semilinear over the composite
`A₁(U) → A₂(U)/I₂(U)`. -/
noncomputable def quotientMapCompOfSquareₛₗ (X : Cᵒᵖ) :
    (A₁.obj X ⧸ kernelIdeal φ₁ X) →ₛₗ[(quotientCompOfFac φ₂ ψ X).hom]
      (A₂.obj X ⧸ kernelIdeal φ₂ X) where
  toFun := quotientMapOfSquare φ₁ φ₂ ψ β hsq X
  map_add' := map_add (quotientMapOfSquare φ₁ φ₂ ψ β hsq X).hom
  map_smul' r x := by
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    change Ideal.Quotient.mk _ (ψ.app X (r * x)) =
      Ideal.Quotient.mk _ (ψ.app X r) * Ideal.Quotient.mk _ (ψ.app X x)
    rw [map_mul, map_mul]

/-- The homotopy on local sections: the map
`(A₁(U)/I₁(U)) ⊗[A₁(U)] Ω[A₁(U)/R₁(U)] → I₂(U)/I₂(U)²` sending `b ⊗ d x` to
`b · (ψ(x) - ψ'(x))`. -/
noncomputable def tensorHomotopyOfSquare (X : Cᵒᵖ) :
    ((A₁.obj X ⧸ kernelIdeal φ₁ X) ⊗[A₁.obj X] ((differentialsPresheaf a₁).obj X))
      →ₛₗ[(quotientCompOfFac φ₂ ψ X).hom] (conormalPresheaf φ₂).obj X :=
  (TensorProduct.lid (A₂.obj X ⧸ kernelIdeal φ₂ X)
      ((conormalPresheaf φ₂).obj X)).toLinearMap.comp
    (TensorProduct.map (quotientMapCompOfSquareₛₗ φ₁ φ₂ ψ β hsq X)
      (differentialsHomotopyOfSquare φ₁ φ₂ ψ ψ' β hsq hsq' a₁ a₂ ρ ha ha' X))

@[simp] theorem tensorHomotopyOfSquare_tmul (X : Cᵒᵖ) (b : A₁.obj X ⧸ kernelIdeal φ₁ X)
    (ω : (differentialsPresheaf a₁).obj X) :
    tensorHomotopyOfSquare φ₁ φ₂ ψ ψ' β hsq hsq' a₁ a₂ ρ ha ha' X (b ⊗ₜ[A₁.obj X] ω) =
      quotientMapOfSquare φ₁ φ₂ ψ β hsq X b •
        differentialsHomotopyOfSquare φ₁ φ₂ ψ ψ' β hsq hsq' a₁ a₂ ρ ha ha' X ω := by
  simp only [tensorHomotopyOfSquare, LinearMap.coe_comp, Function.comp_apply,
    LinearEquiv.coe_coe, TensorProduct.map_tmul, TensorProduct.lid_tmul]
  rfl

/-- The homotopy on local sections is semilinear over the map induced on the two image
presheaves. -/
theorem tensorHomotopyOfSquare_smul (X : Cᵒᵖ) (r : A₁.obj X ⧸ kernelIdeal φ₁ X)
    (t : (A₁.obj X ⧸ kernelIdeal φ₁ X) ⊗[A₁.obj X] ((differentialsPresheaf a₁).obj X)) :
    tensorHomotopyOfSquare φ₁ φ₂ ψ ψ' β hsq hsq' a₁ a₂ ρ ha ha' X (r • t) =
      quotientMapOfSquare φ₁ φ₂ ψ β hsq X r •
        tensorHomotopyOfSquare φ₁ φ₂ ψ ψ' β hsq hsq' a₁ a₂ ρ ha ha' X t := by
  induction t using TensorProduct.induction_on with
  | zero => rw [smul_zero, map_zero, smul_zero]
  | tmul b ω =>
      rw [TensorProduct.smul_tmul', tensorHomotopyOfSquare_tmul, tensorHomotopyOfSquare_tmul,
        ← mul_smul]
      exact congrArg (fun s : A₂.obj X ⧸ kernelIdeal φ₂ X ↦
        s • differentialsHomotopyOfSquare φ₁ φ₂ ψ ψ' β hsq hsq' a₁ a₂ ρ ha ha' X ω)
        (map_mul (quotientMapOfSquare φ₁ φ₂ ψ β hsq X).hom r b)
  | add t t' ht ht' => rw [smul_add, map_add, map_add, ht, ht', smul_add]

/-- The homotopy on local sections commutes with the restriction maps. -/
theorem tensorHomotopyOfSquare_naturality {X Y : Cᵒᵖ} (f : X ⟶ Y)
    (t : (A₁.obj X ⧸ kernelIdeal φ₁ X) ⊗[A₁.obj X] ((differentialsPresheaf a₁).obj X)) :
    tensorHomotopyOfSquare φ₁ φ₂ ψ ψ' β hsq hsq' a₁ a₂ ρ ha ha' Y (tensorMapₛₗ φ₁ a₁ f t) =
      (conormalPresheaf φ₂).restrictₛₗ f
        (tensorHomotopyOfSquare φ₁ φ₂ ψ ψ' β hsq hsq' a₁ a₂ ρ ha ha' X t) := by
  induction t using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero, map_zero, map_zero]
  | tmul b ω =>
      rw [tensorMapₛₗ, TensorProduct.map_tmul, tensorHomotopyOfSquare_tmul,
        tensorHomotopyOfSquare_tmul, map_smulₛₗ, differentialsHomotopyOfSquare_naturality]
      refine congrArg (fun s : A₂.obj Y ⧸ kernelIdeal φ₂ Y ↦
        s • (conormalPresheaf φ₂).restrictₛₗ f
          (differentialsHomotopyOfSquare φ₁ φ₂ ψ ψ' β hsq hsq' a₁ a₂ ρ ha ha' X ω)) ?_
      exact quotientMapOfSquare_naturality φ₁ φ₂ ψ β hsq f b
  | add t t' ht ht' => rw [map_add, map_add, map_add, map_add, ht, ht']

/-! ### The two homotopy identities on local sections -/

include hsq hsq' in
/-- Two morphisms of presentations over the same square induce the same map on the image
presheaves. -/
theorem quotientMapOfSquare_eq_of_square (X : Cᵒᵖ) (b : A₁.obj X ⧸ kernelIdeal φ₁ X) :
    quotientMapOfSquare φ₁ φ₂ ψ' β hsq' X b = quotientMapOfSquare φ₁ φ₂ ψ β hsq X b := by
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
  refine (Ideal.Quotient.eq).mpr ?_
  simpa only [neg_sub] using neg_mem (sub_mem_kernelIdeal_square φ₁ φ₂ ψ ψ' β hsq hsq' X b)

/-- Precomposing the homotopy with the left-hand map of the first conormal sequence gives the
difference of the two induced maps on conormal modules. -/
theorem tensorHomotopyOfSquare_conormalToTensorApp (X : Cᵒᵖ)
    (c : (conormalPresheaf φ₁).obj X) :
    tensorHomotopyOfSquare φ₁ φ₂ ψ ψ' β hsq hsq' a₁ a₂ ρ ha ha' X
        (conormalToTensorApp φ₁ a₁ X c) =
      conormalMapOfSquare φ₁ φ₂ ψ β hsq X c - conormalMapOfSquare φ₁ φ₂ ψ' β hsq' X c := by
  obtain ⟨c, rfl⟩ := (kernelIdeal φ₁ X).toCotangent_surjective c
  rw [conormalToTensorApp_toCotangent]
  refine (tensorHomotopyOfSquare_tmul φ₁ φ₂ ψ ψ' β hsq hsq' a₁ a₂ ρ ha ha' X _ _).trans ?_
  rw [differentialsHomotopyOfSquare_d, map_one (quotientMapOfSquare φ₁ φ₂ ψ β hsq X).hom]
  refine (one_smul (A₂.obj X ⧸ kernelIdeal φ₂ X) _).trans ?_
  show (kernelIdeal φ₂ X).toCotangent (subOfSquare φ₁ φ₂ ψ ψ' β hsq hsq' X (c : A₁.obj X)) =
    (kernelIdeal φ₂ X).toCotangent
        ⟨ψ.app X (c : A₁.obj X),
          kernelIdeal_le_comap_square φ₁ φ₂ ψ β hsq X c.2⟩ -
      (kernelIdeal φ₂ X).toCotangent
        ⟨ψ'.app X (c : A₁.obj X),
          kernelIdeal_le_comap_square φ₁ φ₂ ψ' β hsq' X c.2⟩
  rw [← map_sub]
  exact congrArg (kernelIdeal φ₂ X).toCotangent (Subtype.ext rfl)

/-- The map classifying `b ↦ ψ(b) - ψ'(b)`, followed by the conormal map of the second
presentation, is the difference of the two induced maps on differentials. -/
theorem conormalToTensorApp_differentialsHomotopyOfSquare (X : Cᵒᵖ)
    (ω : (differentialsPresheaf a₁).obj X) :
    conormalToTensorApp φ₂ a₂ X
        (differentialsHomotopyOfSquare φ₁ φ₂ ψ ψ' β hsq hsq' a₁ a₂ ρ ha ha' X ω) =
      (1 : A₂.obj X ⧸ kernelIdeal φ₂ X) ⊗ₜ[A₂.obj X]
          (differentialsMapOfSquare ψ a₁ a₂ ρ ha X ω) -
        (1 : A₂.obj X ⧸ kernelIdeal φ₂ X) ⊗ₜ[A₂.obj X]
          (differentialsMapOfSquare ψ' a₁ a₂ ρ ha' X ω) := by
  let := (a₁.app X).hom.toAlgebra
  have mem : ω ∈ Submodule.span (A₁.obj X)
      (Set.range (KaehlerDifferential.D (R₁.obj X) (A₁.obj X))) := by
    rw [KaehlerDifferential.span_range_derivation]; trivial
  induction mem using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨x, rfl⟩ := hx
      show conormalToTensorApp φ₂ a₂ X
          (differentialsHomotopyOfSquare φ₁ φ₂ ψ ψ' β hsq hsq' a₁ a₂ ρ ha ha' X
            (CommRingCat.KaehlerDifferential.d (f := a₁.app X) x)) =
        (1 : A₂.obj X ⧸ kernelIdeal φ₂ X) ⊗ₜ[A₂.obj X]
            (differentialsMapOfSquare ψ a₁ a₂ ρ ha X
              (CommRingCat.KaehlerDifferential.d (f := a₁.app X) x)) -
          (1 : A₂.obj X ⧸ kernelIdeal φ₂ X) ⊗ₜ[A₂.obj X]
            (differentialsMapOfSquare ψ' a₁ a₂ ρ ha' X
              (CommRingCat.KaehlerDifferential.d (f := a₁.app X) x))
      rw [differentialsHomotopyOfSquare_d, conormalToTensorApp_toCotangent,
        differentialsMapOfSquare_d, differentialsMapOfSquare_d, subOfSquare_coe,
        kaehlerDifferential_d_sub]
      exact TensorProduct.tmul_sub _ _ _
  | zero =>
      rw [map_zero, map_zero, map_zero, map_zero, TensorProduct.tmul_zero, sub_self]
      rfl
  | add x y hx hy ihx ihy =>
      rw [map_add, map_add, map_add, map_add, ihx, ihy, TensorProduct.tmul_add,
        TensorProduct.tmul_add]
      abel
  | smul r ω hω ih =>
      have key : ∀ (s : A₂.obj X) (y : (A₂.obj X ⧸ kernelIdeal φ₂ X) ⊗[A₂.obj X]
          ((differentialsPresheaf a₂).obj X)),
          Ideal.Quotient.mk (kernelIdeal φ₂ X) s • y = s • y := by
        intro s y
        rw [← Ideal.Quotient.algebraMap_eq]
        exact IsScalarTower.algebraMap_smul _ _ _
      rw [map_smulₛₗ, map_smul, ih, map_smulₛₗ, map_smulₛₗ, TensorProduct.tmul_smul,
        TensorProduct.tmul_smul]
      refine (smul_sub _ _ _).trans (congrArg₂ (· - ·) (key _ _) ?_)
      refine Eq.trans ?_ (key ((ψ'.app X).hom r) _)
      exact congrArg (fun s : A₂.obj X ⧸ kernelIdeal φ₂ X ↦
        s • ((1 : A₂.obj X ⧸ kernelIdeal φ₂ X) ⊗ₜ[A₂.obj X]
          differentialsMapOfSquare ψ' a₁ a₂ ρ ha' X ω))
        ((Ideal.Quotient.eq).mpr (sub_mem_kernelIdeal_square φ₁ φ₂ ψ ψ' β hsq hsq' X r))

/-- Postcomposing the homotopy with the left-hand map of the second conormal sequence gives the
difference of the two induced maps on the tensor terms. -/
theorem conormalToTensorApp_tensorHomotopyOfSquare (X : Cᵒᵖ)
    (t : (A₁.obj X ⧸ kernelIdeal φ₁ X) ⊗[A₁.obj X] ((differentialsPresheaf a₁).obj X)) :
    conormalToTensorApp φ₂ a₂ X
        (tensorHomotopyOfSquare φ₁ φ₂ ψ ψ' β hsq hsq' a₁ a₂ ρ ha ha' X t) =
      tensorMapOfSquareₛₗ φ₁ φ₂ ψ β hsq a₁ a₂ ρ ha X t -
        tensorMapOfSquareₛₗ φ₁ φ₂ ψ' β hsq' a₁ a₂ ρ ha' X t := by
  induction t using TensorProduct.induction_on with
  | zero =>
      rw [map_zero, map_zero, map_zero, map_zero, sub_self]
      rfl
  | tmul b ω =>
      rw [tensorHomotopyOfSquare_tmul, map_smul,
        conormalToTensorApp_differentialsHomotopyOfSquare, tensorMapOfSquareₛₗ,
        tensorMapOfSquareₛₗ, TensorProduct.map_tmul, TensorProduct.map_tmul]
      refine (smul_sub _ _ _).trans (congrArg₂ (· - ·) ?_ ?_)
      · refine ((TensorProduct.smul_tmul' _ _ _).symm).trans ?_
        exact congrArg (fun s : A₂.obj X ⧸ kernelIdeal φ₂ X ↦
          s ⊗ₜ[A₂.obj X] differentialsMapOfSquare ψ a₁ a₂ ρ ha X ω)
          ((smul_eq_mul _ _).trans (mul_one _))
      · refine ((TensorProduct.smul_tmul' _ _ _).symm).trans ?_
        exact congrArg (fun s : A₂.obj X ⧸ kernelIdeal φ₂ X ↦
          s ⊗ₜ[A₂.obj X] differentialsMapOfSquare ψ' a₁ a₂ ρ ha' X ω)
          (((smul_eq_mul _ _).trans (mul_one _)).trans
            (quotientMapOfSquare_eq_of_square φ₁ φ₂ ψ ψ' β hsq hsq' X b).symm)
  | add t t' ht ht' =>
      rw [map_add, map_add, map_add, map_add, ht, ht']
      abel

end Differentials
end Square

/-! ### The specialisation to a fixed target and a fixed base -/

variable (hψ : ψ ≫ φ₂ = φ₁) (hψ' : ψ' ≫ φ₂ = φ₁)

include hψ hψ' in
/-- Two factorisations of the same presentation differ by a section of the kernel. -/
theorem sub_mem_kernelIdeal (X : Cᵒᵖ) (x : A₁.obj X) :
    ψ.app X x - ψ'.app X x ∈ kernelIdeal φ₂ X :=
  sub_mem_kernelIdeal_square φ₁ φ₂ ψ ψ' (𝟙 B) (by simpa using hψ) (by simpa using hψ') X x

/-- The difference of two factorisations, as a section of the kernel of the second
presentation. -/
noncomputable def subOfFac (X : Cᵒᵖ) (x : A₁.obj X) : kernelIdeal φ₂ X :=
  subOfSquare φ₁ φ₂ ψ ψ' (𝟙 B) (by simpa using hψ) (by simpa using hψ') X x

@[simp] theorem subOfFac_coe (X : Cᵒᵖ) (x : A₁.obj X) :
    (subOfFac φ₁ φ₂ ψ ψ' hψ hψ' X x : A₂.obj X) = ψ.app X x - ψ'.app X x :=
  subOfSquare_coe φ₁ φ₂ ψ ψ' (𝟙 B) (by simpa using hψ) (by simpa using hψ') X x

/-- The difference of two factorisations is additive. -/
theorem subOfFac_add (X : Cᵒᵖ) (x y : A₁.obj X) :
    subOfFac φ₁ φ₂ ψ ψ' hψ hψ' X (x + y) =
      subOfFac φ₁ φ₂ ψ ψ' hψ hψ' X x + subOfFac φ₁ φ₂ ψ ψ' hψ hψ' X y :=
  subOfSquare_add φ₁ φ₂ ψ ψ' (𝟙 B) (by simpa using hψ) (by simpa using hψ') X x y

/-- The conormal class of the difference of two factorisations, as a section of `I₂/I₂²`
regarded as a module over `A₁(U)` through `ψ`. -/
noncomputable def cotangentDiffOfFac (X : Cᵒᵖ) (x : A₁.obj X) :
    conormalRestrictOfFac φ₂ ψ X :=
  cotangentDiffOfSquare φ₁ φ₂ ψ ψ' (𝟙 B) (by simpa using hψ) (by simpa using hψ') X x

/-- The conormal class of the difference of two factorisations is additive. -/
theorem cotangentDiffOfFac_add (X : Cᵒᵖ) (x y : A₁.obj X) :
    cotangentDiffOfFac φ₁ φ₂ ψ ψ' hψ hψ' X (x + y) =
      cotangentDiffOfFac φ₁ φ₂ ψ ψ' hψ hψ' X x +
        cotangentDiffOfFac φ₁ φ₂ ψ ψ' hψ hψ' X y :=
  cotangentDiffOfSquare_add φ₁ φ₂ ψ ψ' (𝟙 B) (by simpa using hψ) (by simpa using hψ') X x y

/-- The Leibniz rule: the conormal class of the difference of two factorisations is a
derivation into `I₂/I₂²`. -/
theorem cotangentDiffOfFac_mul (X : Cᵒᵖ) (x y : A₁.obj X) :
    cotangentDiffOfFac φ₁ φ₂ ψ ψ' hψ hψ' X (x * y) =
      x • cotangentDiffOfFac φ₁ φ₂ ψ ψ' hψ hψ' X y +
        y • cotangentDiffOfFac φ₁ φ₂ ψ ψ' hψ hψ' X x :=
  cotangentDiffOfSquare_mul φ₁ φ₂ ψ ψ' (𝟙 B) (by simpa using hψ) (by simpa using hψ') X x y

variable {R : Cᵒᵖ ⥤ CommRingCat.{w}} (a₁ : R ⟶ A₁) (a₂ : R ⟶ A₂)

/-- Two factorisations over the same base agree on the image of the base ring. -/
theorem subOfFac_structureMap (ha : a₁ ≫ ψ = a₂) (ha' : a₁ ≫ ψ' = a₂) (X : Cᵒᵖ)
    (r : R.obj X) : subOfFac φ₁ φ₂ ψ ψ' hψ hψ' X (a₁.app X r) = 0 :=
  subOfSquare_structureMap φ₁ φ₂ ψ ψ' (𝟙 B) (by simpa using hψ) (by simpa using hψ')
    a₁ a₂ (𝟙 R) (by simpa using ha.symm) (by simpa using ha'.symm) X r

/-- The conormal class of the difference of two factorisations over the same base vanishes on
the image of the base ring. -/
theorem cotangentDiffOfFac_structureMap (ha : a₁ ≫ ψ = a₂) (ha' : a₁ ≫ ψ' = a₂) (X : Cᵒᵖ)
    (r : R.obj X) : cotangentDiffOfFac φ₁ φ₂ ψ ψ' hψ hψ' X (a₁.app X r) = 0 :=
  cotangentDiffOfSquare_structureMap φ₁ φ₂ ψ ψ' (𝟙 B) (by simpa using hψ)
    (by simpa using hψ') a₁ a₂ (𝟙 R) (by simpa using ha.symm) (by simpa using ha'.symm) X r

variable (ha : a₁ ≫ ψ = a₂) (ha' : a₁ ≫ ψ' = a₂)

/-- The derivation `A₁(U) → I₂(U)/I₂(U)²`, `b ↦ ψ(b) - ψ'(b) mod I₂²`, attached to two
factorisations of the same presentation over the same base. -/
noncomputable def derivationOfFac (X : Cᵒᵖ) :
    (conormalRestrictOfFac φ₂ ψ X).Derivation (a₁.app X) :=
  derivationOfSquare φ₁ φ₂ ψ ψ' (𝟙 B) (by simpa using hψ) (by simpa using hψ')
    a₁ a₂ (𝟙 R) (by simpa using ha.symm) (by simpa using ha'.symm) X

/-- The map `Ω[A₁(U)/R(U)] → I₂(U)/I₂(U)²` classifying `b ↦ ψ(b) - ψ'(b)`, semilinear over
the composite `A₁(U) → A₂(U) → A₂(U)/I₂(U)`. -/
noncomputable def differentialsHomotopyOfFac (X : Cᵒᵖ) :
    (differentialsPresheaf a₁).obj X →ₛₗ[(quotientCompOfFac φ₂ ψ X).hom]
      (conormalPresheaf φ₂).obj X :=
  differentialsHomotopyOfSquare φ₁ φ₂ ψ ψ' (𝟙 B) (by simpa using hψ) (by simpa using hψ')
    a₁ a₂ (𝟙 R) (by simpa using ha.symm) (by simpa using ha'.symm) X

@[simp] theorem differentialsHomotopyOfFac_d (X : Cᵒᵖ) (x : A₁.obj X) :
    differentialsHomotopyOfFac φ₁ φ₂ ψ ψ' hψ hψ' a₁ a₂ ha ha' X
        (CommRingCat.KaehlerDifferential.d x) =
      (kernelIdeal φ₂ X).toCotangent (subOfFac φ₁ φ₂ ψ ψ' hψ hψ' X x) :=
  differentialsHomotopyOfSquare_d φ₁ φ₂ ψ ψ' (𝟙 B) (by simpa using hψ) (by simpa using hψ')
    a₁ a₂ (𝟙 R) (by simpa using ha.symm) (by simpa using ha'.symm) X x

/-- The map classifying `b ↦ ψ(b) - ψ'(b)` commutes with the restriction maps. -/
theorem differentialsHomotopyOfFac_naturality {X Y : Cᵒᵖ} (f : X ⟶ Y)
    (ω : (differentialsPresheaf a₁).obj X) :
    differentialsHomotopyOfFac φ₁ φ₂ ψ ψ' hψ hψ' a₁ a₂ ha ha' Y
        ((differentialsPresheaf a₁).restrictₛₗ f ω) =
      (conormalPresheaf φ₂).restrictₛₗ f
        (differentialsHomotopyOfFac φ₁ φ₂ ψ ψ' hψ hψ' a₁ a₂ ha ha' X ω) :=
  differentialsHomotopyOfSquare_naturality φ₁ φ₂ ψ ψ' (𝟙 B) (by simpa using hψ)
    (by simpa using hψ') a₁ a₂ (𝟙 R) (by simpa using ha.symm) (by simpa using ha'.symm) f ω


/-! ### The homotopy on the tensor term, for a fixed target -/

/-- The induced map on quotients, semilinear over the composite `A₁(U) → A₂(U)/I₂(U)`. -/
noncomputable def quotientMapCompOfFacₛₗ (X : Cᵒᵖ) :
    (A₁.obj X ⧸ kernelIdeal φ₁ X) →ₛₗ[(quotientCompOfFac φ₂ ψ X).hom]
      (A₂.obj X ⧸ kernelIdeal φ₂ X) :=
  quotientMapCompOfSquareₛₗ φ₁ φ₂ ψ (𝟙 B) (by simpa using hψ) X

/-- The homotopy on local sections: the map
`(A₁(U)/I₁(U)) ⊗[A₁(U)] Ω[A₁(U)/R(U)] → I₂(U)/I₂(U)²` sending `b ⊗ d x` to
`b · (ψ(x) - ψ'(x))`. -/
noncomputable def tensorHomotopyOfFac (X : Cᵒᵖ) :
    ((A₁.obj X ⧸ kernelIdeal φ₁ X) ⊗[A₁.obj X] ((differentialsPresheaf a₁).obj X))
      →ₛₗ[(quotientCompOfFac φ₂ ψ X).hom] (conormalPresheaf φ₂).obj X :=
  tensorHomotopyOfSquare φ₁ φ₂ ψ ψ' (𝟙 B) (by simpa using hψ) (by simpa using hψ')
    a₁ a₂ (𝟙 R) (by simpa using ha.symm) (by simpa using ha'.symm) X

@[simp] theorem tensorHomotopyOfFac_tmul (X : Cᵒᵖ) (b : A₁.obj X ⧸ kernelIdeal φ₁ X)
    (ω : (differentialsPresheaf a₁).obj X) :
    tensorHomotopyOfFac φ₁ φ₂ ψ ψ' hψ hψ' a₁ a₂ ha ha' X (b ⊗ₜ[A₁.obj X] ω) =
      quotientMapOfFac φ₁ φ₂ ψ hψ X b •
        differentialsHomotopyOfFac φ₁ φ₂ ψ ψ' hψ hψ' a₁ a₂ ha ha' X ω :=
  tensorHomotopyOfSquare_tmul φ₁ φ₂ ψ ψ' (𝟙 B) (by simpa using hψ) (by simpa using hψ')
    a₁ a₂ (𝟙 R) (by simpa using ha.symm) (by simpa using ha'.symm) X b ω

/-- The homotopy on local sections is semilinear over the map induced on the two image
presheaves. -/
theorem tensorHomotopyOfFac_smul (X : Cᵒᵖ) (r : A₁.obj X ⧸ kernelIdeal φ₁ X)
    (t : (A₁.obj X ⧸ kernelIdeal φ₁ X) ⊗[A₁.obj X] ((differentialsPresheaf a₁).obj X)) :
    tensorHomotopyOfFac φ₁ φ₂ ψ ψ' hψ hψ' a₁ a₂ ha ha' X (r • t) =
      quotientMapOfFac φ₁ φ₂ ψ hψ X r •
        tensorHomotopyOfFac φ₁ φ₂ ψ ψ' hψ hψ' a₁ a₂ ha ha' X t :=
  tensorHomotopyOfSquare_smul φ₁ φ₂ ψ ψ' (𝟙 B) (by simpa using hψ) (by simpa using hψ')
    a₁ a₂ (𝟙 R) (by simpa using ha.symm) (by simpa using ha'.symm) X r t

/-- The homotopy on local sections commutes with the restriction maps. -/
theorem tensorHomotopyOfFac_naturality {X Y : Cᵒᵖ} (f : X ⟶ Y)
    (t : (A₁.obj X ⧸ kernelIdeal φ₁ X) ⊗[A₁.obj X] ((differentialsPresheaf a₁).obj X)) :
    tensorHomotopyOfFac φ₁ φ₂ ψ ψ' hψ hψ' a₁ a₂ ha ha' Y (tensorMapₛₗ φ₁ a₁ f t) =
      (conormalPresheaf φ₂).restrictₛₗ f
        (tensorHomotopyOfFac φ₁ φ₂ ψ ψ' hψ hψ' a₁ a₂ ha ha' X t) :=
  tensorHomotopyOfSquare_naturality φ₁ φ₂ ψ ψ' (𝟙 B) (by simpa using hψ)
    (by simpa using hψ') a₁ a₂ (𝟙 R) (by simpa using ha.symm) (by simpa using ha'.symm) f t


/-! ### The two homotopy identities on local sections -/

include hψ hψ' in
/-- Two factorisations of the same presentation induce the same map on the image
presheaves. -/
theorem quotientMapOfFac_eq_of_fac (X : Cᵒᵖ) (b : A₁.obj X ⧸ kernelIdeal φ₁ X) :
    quotientMapOfFac φ₁ φ₂ ψ' hψ' X b = quotientMapOfFac φ₁ φ₂ ψ hψ X b :=
  quotientMapOfSquare_eq_of_square φ₁ φ₂ ψ ψ' (𝟙 B) (by simpa using hψ)
    (by simpa using hψ') X b

/-- Precomposing the homotopy with the left-hand map of the first conormal sequence gives the
difference of the two induced maps on conormal modules. -/
theorem tensorHomotopyOfFac_conormalToTensorApp (X : Cᵒᵖ) (c : (conormalPresheaf φ₁).obj X) :
    tensorHomotopyOfFac φ₁ φ₂ ψ ψ' hψ hψ' a₁ a₂ ha ha' X (conormalToTensorApp φ₁ a₁ X c) =
      conormalMapOfFac φ₁ φ₂ ψ hψ X c - conormalMapOfFac φ₁ φ₂ ψ' hψ' X c :=
  tensorHomotopyOfSquare_conormalToTensorApp φ₁ φ₂ ψ ψ' (𝟙 B) (by simpa using hψ)
    (by simpa using hψ') a₁ a₂ (𝟙 R) (by simpa using ha.symm) (by simpa using ha'.symm) X c

/-- The map classifying `b ↦ ψ(b) - ψ'(b)`, followed by the conormal map of the second
presentation, is the difference of the two induced maps on differentials. -/
theorem conormalToTensorApp_differentialsHomotopyOfFac (X : Cᵒᵖ)
    (ω : (differentialsPresheaf a₁).obj X) :
    conormalToTensorApp φ₂ a₂ X
        (differentialsHomotopyOfFac φ₁ φ₂ ψ ψ' hψ hψ' a₁ a₂ ha ha' X ω) =
      (1 : A₂.obj X ⧸ kernelIdeal φ₂ X) ⊗ₜ[A₂.obj X]
          (differentialsMapOfFac ψ a₁ a₂ ha X ω) -
        (1 : A₂.obj X ⧸ kernelIdeal φ₂ X) ⊗ₜ[A₂.obj X]
          (differentialsMapOfFac ψ' a₁ a₂ ha' X ω) :=
  conormalToTensorApp_differentialsHomotopyOfSquare φ₁ φ₂ ψ ψ' (𝟙 B) (by simpa using hψ)
    (by simpa using hψ') a₁ a₂ (𝟙 R) (by simpa using ha.symm) (by simpa using ha'.symm) X ω

/-- Postcomposing the homotopy with the left-hand map of the second conormal sequence gives the
difference of the two induced maps on the tensor terms. -/
theorem conormalToTensorApp_tensorHomotopyOfFac (X : Cᵒᵖ)
    (t : (A₁.obj X ⧸ kernelIdeal φ₁ X) ⊗[A₁.obj X] ((differentialsPresheaf a₁).obj X)) :
    conormalToTensorApp φ₂ a₂ X
        (tensorHomotopyOfFac φ₁ φ₂ ψ ψ' hψ hψ' a₁ a₂ ha ha' X t) =
      tensorMapOfFacₛₗ φ₁ φ₂ ψ hψ a₁ a₂ ha X t -
        tensorMapOfFacₛₗ φ₁ φ₂ ψ' hψ' a₁ a₂ ha' X t :=
  conormalToTensorApp_tensorHomotopyOfSquare φ₁ φ₂ ψ ψ' (𝟙 B) (by simpa using hψ)
    (by simpa using hψ') a₁ a₂ (𝟙 R) (by simpa using ha.symm) (by simpa using ha'.symm) X t


end Objectwise

/-! ### The homotopy as a morphism of sheaves of modules -/

section Sheaves


variable (J : GrothendieckTopology C) [HasWeakSheafify J CommRingCat.{w}]
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable (R B A₁ A₂ : Sheaf J CommRingCat.{w}) (a₁ : R ⟶ A₁) (a₂ : R ⟶ A₂)
  (φ₁ : A₁ ⟶ B) (φ₂ : A₂ ⟶ B) (ψ ψ' : A₁ ⟶ A₂)
  (hψ : ψ ≫ φ₂ = φ₁) (hψ' : ψ' ≫ φ₂ = φ₁) (ha : a₁ ≫ ψ = a₂) (ha' : a₁ ≫ ψ' = a₂)
  [Presheaf.IsLocallySurjective J φ₁.hom] [Presheaf.IsLocallySurjective J φ₂.hom]

include hψ hψ' ha ha' in
/-- The homotopy `B ⊗[A₁] Ω[A₁/R] ⟶ I₂/I₂²` attached to two factorisations `ψ, ψ'` over the
base `R` of a presentation `φ₁ : A₁ ⟶ B` through a presentation `φ₂ : A₂ ⟶ B`, determined on
local sections by `b ⊗ d x ↦ b · (ψ(x) - ψ'(x))`. -/
noncomputable def conormalHomotopyOfFac :
    tensorDifferentialsSheaf.{v, u, w, z} J R A₁ B a₁ φ₁ ⟶
      conormalSheaf.{v, u, w, z} J A₂ B φ₂ := by
  refine sheafifyLiftDesc.{v, u, w, z} J A₁ B φ₁ (tensorPresheaf φ₁.hom a₁.hom)
    (conormalSheaf.{v, u, w, z} J A₂ B φ₂)
    (fun X t ↦ toAssociatedModule.{v, u, w, z} J A₂ B φ₂ (conormalPresheaf φ₂.hom) X
      (tensorHomotopyOfFac φ₁.hom φ₂.hom ψ.hom ψ'.hom (hom_of_comp_eq hψ)
        (hom_of_comp_eq hψ') a₁.hom a₂.hom (hom_of_comp_eq ha) (hom_of_comp_eq ha') X t))
    ?_ ?_ ?_
  · intro X t t'
    exact (congrArg (toAssociatedModule.{v, u, w, z} J A₂ B φ₂ (conormalPresheaf φ₂.hom) X)
      (map_add (tensorHomotopyOfFac φ₁.hom φ₂.hom ψ.hom ψ'.hom (hom_of_comp_eq hψ)
        (hom_of_comp_eq hψ') a₁.hom a₂.hom (hom_of_comp_eq ha) (hom_of_comp_eq ha') X)
        t t')).trans
      (toAssociatedModule_add.{v, u, w, z} J A₂ B φ₂ (conormalPresheaf φ₂.hom) X _ _)
  · intro X r t
    refine (congrArg (toAssociatedModule.{v, u, w, z} J A₂ B φ₂ (conormalPresheaf φ₂.hom) X)
      (tensorHomotopyOfFac_smul φ₁.hom φ₂.hom ψ.hom ψ'.hom (hom_of_comp_eq hψ)
        (hom_of_comp_eq hψ') a₁.hom a₂.hom (hom_of_comp_eq ha) (hom_of_comp_eq ha')
        X r t)).trans ?_
    refine (toAssociatedModule_smul.{v, u, w, z} J A₂ B φ₂
      (conormalPresheaf φ₂.hom) X _ _).trans ?_
    exact congrArg (fun s : (Stacks.SheafOfModules.Tensor.ringSheaf B).obj.obj X ↦
      s • toAssociatedModule.{v, u, w, z} J A₂ B φ₂ (conormalPresheaf φ₂.hom) X
        (tensorHomotopyOfFac φ₁.hom φ₂.hom ψ.hom ψ'.hom (hom_of_comp_eq hψ)
          (hom_of_comp_eq hψ') a₁.hom a₂.hom (hom_of_comp_eq ha) (hom_of_comp_eq ha') X t))
      (quotientToTarget_quotientMapOfFac φ₁.hom φ₂.hom ψ.hom (hom_of_comp_eq hψ) X r)
  · intro X Y f t
    exact (congrArg (toAssociatedModule.{v, u, w, z} J A₂ B φ₂ (conormalPresheaf φ₂.hom) Y)
      (tensorHomotopyOfFac_naturality φ₁.hom φ₂.hom ψ.hom ψ'.hom (hom_of_comp_eq hψ)
        (hom_of_comp_eq hψ') a₁.hom a₂.hom (hom_of_comp_eq ha) (hom_of_comp_eq ha') f t)).trans
      (toAssociatedModule_map.{v, u, w, z} J A₂ B φ₂ (conormalPresheaf φ₂.hom) f _)

omit [HasWeakSheafify J CommRingCat.{w}] in
include hψ hψ' ha ha' in
/-- The homotopy sends the local section `1 ⊗ d x` to the conormal class of
`ψ(x) - ψ'(x)`. -/
theorem conormalHomotopyOfFac_tensorDifferential (X : Cᵒᵖ) (x : A₁.obj.obj X) :
    ((conormalHomotopyOfFac.{v, u, w, z} J R B A₁ A₂ a₁ a₂ φ₁ φ₂ ψ ψ' hψ hψ' ha ha').val.app X)
      (tensorDifferential.{v, u, w, z} J R A₁ B a₁ φ₁ X x) =
      conormalClass.{v, u, w, z} J R A₂ B a₂ φ₂ X
        (subOfFac φ₁.hom φ₂.hom ψ.hom ψ'.hom (hom_of_comp_eq hψ) (hom_of_comp_eq hψ') X x) := by
  have h : ((conormalHomotopyOfFac.{v, u, w, z} J R B A₁ A₂ a₁ a₂ φ₁ φ₂
        ψ ψ' hψ hψ' ha ha').val.app X)
      (tensorDifferential.{v, u, w, z} J R A₁ B a₁ φ₁ X x) =
      toAssociatedModule.{v, u, w, z} J A₂ B φ₂ (conormalPresheaf φ₂.hom) X
        (tensorHomotopyOfFac φ₁.hom φ₂.hom ψ.hom ψ'.hom (hom_of_comp_eq hψ)
          (hom_of_comp_eq hψ') a₁.hom a₂.hom (hom_of_comp_eq ha) (hom_of_comp_eq ha') X
          ((1 : A₁.obj.obj X ⧸ kernelIdeal φ₁.hom X) ⊗ₜ[A₁.obj.obj X]
            CommRingCat.KaehlerDifferential.d (f := a₁.hom.app X) x)) := by
    apply sheafifyLiftDesc_toAssociatedModule.{v, u, w, z}
  refine h.trans ?_
  refine congrArg (toAssociatedModule.{v, u, w, z} J A₂ B φ₂ (conormalPresheaf φ₂.hom) X) ?_
  refine (tensorHomotopyOfFac_tmul φ₁.hom φ₂.hom ψ.hom ψ'.hom (hom_of_comp_eq hψ)
    (hom_of_comp_eq hψ') a₁.hom a₂.hom (hom_of_comp_eq ha) (hom_of_comp_eq ha') X _ _).trans ?_
  rw [differentialsHomotopyOfFac_d,
    map_one (quotientMapOfFac φ₁.hom φ₂.hom ψ.hom (hom_of_comp_eq hψ) X).hom]
  exact one_smul _ _


omit [HasWeakSheafify J CommRingCat.{w}] in
include hψ hψ' ha ha' in
/-- The two maps of conormal sheaves induced by two factorisations of the same presentation
differ by the homotopy precomposed with the left-hand map of the first conormal sequence. -/
theorem conormalSheafMapOfFac_eq_add :
    conormalSheafMapOfFac.{v, u, w, z} J B A₁ A₂ φ₁ φ₂ ψ hψ =
      (((conormalSequence.{v, u, w, z} J R A₁ B a₁ φ₁).f ≫
            conormalHomotopyOfFac.{v, u, w, z} J R B A₁ A₂ a₁ a₂ φ₁ φ₂ ψ ψ' hψ hψ' ha ha' :
          conormalSheaf.{v, u, w, z} J A₁ B φ₁ ⟶ conormalSheaf.{v, u, w, z} J A₂ B φ₂)) +
        conormalSheafMapOfFac.{v, u, w, z} J B A₁ A₂ φ₁ φ₂ ψ' hψ' := by
  apply sheafify_hom_ext.{v, u, w, z} J A₁ B φ₁ (conormalPresheaf φ₁.hom)
  intro X c
  have hsum : ∀ (g₁ g₂ : conormalSheaf.{v, u, w, z} J A₁ B φ₁ ⟶
      conormalSheaf.{v, u, w, z} J A₂ B φ₂)
      (y : (conormalSheaf.{v, u, w, z} J A₁ B φ₁).val.obj X),
      (g₁ + g₂).val.app X y = g₁.val.app X y + g₂.val.app X y := fun _ _ _ ↦ rfl
  have hf : (conormalSequence.{v, u, w, z} J R A₁ B a₁ φ₁).f.val.app X
        (toAssociatedModule.{v, u, w, z} J A₁ B φ₁ (conormalPresheaf φ₁.hom) X c) =
      toAssociatedModule.{v, u, w, z} J A₁ B φ₁ (tensorPresheaf φ₁.hom a₁.hom) X
        (conormalToTensorApp φ₁.hom a₁.hom X c) :=
    associatedModule_map_unit.{v, u, w, z} J A₁ B φ₁ (conormalToTensor φ₁.hom a₁.hom) X c
  have hH : (conormalHomotopyOfFac.{v, u, w, z} J R B A₁ A₂ a₁ a₂ φ₁ φ₂
        ψ ψ' hψ hψ' ha ha').val.app X
        (toAssociatedModule.{v, u, w, z} J A₁ B φ₁ (tensorPresheaf φ₁.hom a₁.hom) X
          (conormalToTensorApp φ₁.hom a₁.hom X c)) =
      toAssociatedModule.{v, u, w, z} J A₂ B φ₂ (conormalPresheaf φ₂.hom) X
        (tensorHomotopyOfFac φ₁.hom φ₂.hom ψ.hom ψ'.hom (hom_of_comp_eq hψ)
          (hom_of_comp_eq hψ') a₁.hom a₂.hom (hom_of_comp_eq ha) (hom_of_comp_eq ha') X
          (conormalToTensorApp φ₁.hom a₁.hom X c)) := by
    apply sheafifyLiftDesc_toAssociatedModule.{v, u, w, z}
  have hR : (((conormalSequence.{v, u, w, z} J R A₁ B a₁ φ₁).f ≫
        conormalHomotopyOfFac.{v, u, w, z} J R B A₁ A₂ a₁ a₂ φ₁ φ₂
          ψ ψ' hψ hψ' ha ha').val.app X)
        (toAssociatedModule.{v, u, w, z} J A₁ B φ₁ (conormalPresheaf φ₁.hom) X c) =
      toAssociatedModule.{v, u, w, z} J A₂ B φ₂ (conormalPresheaf φ₂.hom) X
        (tensorHomotopyOfFac φ₁.hom φ₂.hom ψ.hom ψ'.hom (hom_of_comp_eq hψ)
          (hom_of_comp_eq hψ') a₁.hom a₂.hom (hom_of_comp_eq ha) (hom_of_comp_eq ha') X
          (conormalToTensorApp φ₁.hom a₁.hom X c)) :=
    (congrArg ((conormalHomotopyOfFac.{v, u, w, z} J R B A₁ A₂ a₁ a₂ φ₁ φ₂
      ψ ψ' hψ hψ' ha ha').val.app X) hf).trans hH
  rw [conormalSheafMapOfFac_toAssociatedModule, hsum]
  refine Eq.trans ?_ (congrArg₂ (· + ·) hR
    (conormalSheafMapOfFac_toAssociatedModule.{v, u, w, z} J B A₁ A₂ φ₁ φ₂ ψ' hψ' X c)).symm
  exact (congrArg (toAssociatedModule.{v, u, w, z} J A₂ B φ₂ (conormalPresheaf φ₂.hom) X)
      (by rw [tensorHomotopyOfFac_conormalToTensorApp]; exact (sub_add_cancel _ _).symm)).trans
    (toAssociatedModule_add.{v, u, w, z} J A₂ B φ₂ (conormalPresheaf φ₂.hom) X _ _)

omit [HasWeakSheafify J CommRingCat.{w}] in
include hψ hψ' ha ha' in
/-- The two maps of tensor terms induced by two factorisations of the same presentation differ
by the homotopy postcomposed with the left-hand map of the second conormal sequence. -/
theorem tensorSheafMapOfFac_eq_add :
    tensorSheafMapOfFac.{v, u, w, z} J R B A₁ A₂ a₁ a₂ φ₁ φ₂ ψ hψ ha =
      ((conormalHomotopyOfFac.{v, u, w, z} J R B A₁ A₂ a₁ a₂ φ₁ φ₂ ψ ψ' hψ hψ' ha ha' ≫
            (conormalSequence.{v, u, w, z} J R A₂ B a₂ φ₂).f :
          tensorDifferentialsSheaf.{v, u, w, z} J R A₁ B a₁ φ₁ ⟶
            tensorDifferentialsSheaf.{v, u, w, z} J R A₂ B a₂ φ₂)) +
        tensorSheafMapOfFac.{v, u, w, z} J R B A₁ A₂ a₁ a₂ φ₁ φ₂ ψ' hψ' ha' := by
  apply sheafify_hom_ext.{v, u, w, z} J A₁ B φ₁ (tensorPresheaf φ₁.hom a₁.hom)
  intro X t
  have hsum : ∀ (g₁ g₂ : tensorDifferentialsSheaf.{v, u, w, z} J R A₁ B a₁ φ₁ ⟶
      tensorDifferentialsSheaf.{v, u, w, z} J R A₂ B a₂ φ₂)
      (y : (tensorDifferentialsSheaf.{v, u, w, z} J R A₁ B a₁ φ₁).val.obj X),
      (g₁ + g₂).val.app X y = g₁.val.app X y + g₂.val.app X y := fun _ _ _ ↦ rfl
  have hH : (conormalHomotopyOfFac.{v, u, w, z} J R B A₁ A₂ a₁ a₂ φ₁ φ₂
        ψ ψ' hψ hψ' ha ha').val.app X
        (toAssociatedModule.{v, u, w, z} J A₁ B φ₁ (tensorPresheaf φ₁.hom a₁.hom) X t) =
      toAssociatedModule.{v, u, w, z} J A₂ B φ₂ (conormalPresheaf φ₂.hom) X
        (tensorHomotopyOfFac φ₁.hom φ₂.hom ψ.hom ψ'.hom (hom_of_comp_eq hψ)
          (hom_of_comp_eq hψ') a₁.hom a₂.hom (hom_of_comp_eq ha) (hom_of_comp_eq ha') X t) := by
    apply sheafifyLiftDesc_toAssociatedModule.{v, u, w, z}
  have hf : (conormalSequence.{v, u, w, z} J R A₂ B a₂ φ₂).f.val.app X
        (toAssociatedModule.{v, u, w, z} J A₂ B φ₂ (conormalPresheaf φ₂.hom) X
          (tensorHomotopyOfFac φ₁.hom φ₂.hom ψ.hom ψ'.hom (hom_of_comp_eq hψ)
            (hom_of_comp_eq hψ') a₁.hom a₂.hom (hom_of_comp_eq ha) (hom_of_comp_eq ha') X t)) =
      toAssociatedModule.{v, u, w, z} J A₂ B φ₂ (tensorPresheaf φ₂.hom a₂.hom) X
        (conormalToTensorApp φ₂.hom a₂.hom X
          (tensorHomotopyOfFac φ₁.hom φ₂.hom ψ.hom ψ'.hom (hom_of_comp_eq hψ)
            (hom_of_comp_eq hψ') a₁.hom a₂.hom (hom_of_comp_eq ha) (hom_of_comp_eq ha') X t)) :=
    associatedModule_map_unit.{v, u, w, z} J A₂ B φ₂ (conormalToTensor φ₂.hom a₂.hom) X _
  have hR : (((conormalHomotopyOfFac.{v, u, w, z} J R B A₁ A₂ a₁ a₂ φ₁ φ₂
        ψ ψ' hψ hψ' ha ha' ≫ (conormalSequence.{v, u, w, z} J R A₂ B a₂ φ₂).f :
          tensorDifferentialsSheaf.{v, u, w, z} J R A₁ B a₁ φ₁ ⟶
            tensorDifferentialsSheaf.{v, u, w, z} J R A₂ B a₂ φ₂)).val.app X)
        (toAssociatedModule.{v, u, w, z} J A₁ B φ₁ (tensorPresheaf φ₁.hom a₁.hom) X t) =
      toAssociatedModule.{v, u, w, z} J A₂ B φ₂ (tensorPresheaf φ₂.hom a₂.hom) X
        (conormalToTensorApp φ₂.hom a₂.hom X
          (tensorHomotopyOfFac φ₁.hom φ₂.hom ψ.hom ψ'.hom (hom_of_comp_eq hψ)
            (hom_of_comp_eq hψ') a₁.hom a₂.hom (hom_of_comp_eq ha) (hom_of_comp_eq ha') X t)) :=
    (congrArg ((conormalSequence.{v, u, w, z} J R A₂ B a₂ φ₂).f.val.app X) hH).trans hf
  rw [tensorSheafMapOfFac_toAssociatedModule, hsum]
  refine Eq.trans ?_ (congrArg₂ (· + ·) hR
    (tensorSheafMapOfFac_toAssociatedModule.{v, u, w, z} J R B A₁ A₂ a₁ a₂ φ₁ φ₂
      ψ' hψ' ha' X t)).symm
  refine (congrArg (toAssociatedModule.{v, u, w, z} J A₂ B φ₂ (tensorPresheaf φ₂.hom a₂.hom) X)
      (((sub_add_cancel _ _).symm).trans (congrArg
        (· + tensorMapOfFacₛₗ φ₁.hom φ₂.hom ψ'.hom (hom_of_comp_eq hψ') a₁.hom a₂.hom
          (hom_of_comp_eq ha') X t)
        (conormalToTensorApp_tensorHomotopyOfFac φ₁.hom φ₂.hom ψ.hom ψ'.hom
          (hom_of_comp_eq hψ) (hom_of_comp_eq hψ') a₁.hom a₂.hom (hom_of_comp_eq ha)
          (hom_of_comp_eq ha') X t).symm))).trans ?_
  exact toAssociatedModule_add.{v, u, w, z} J A₂ B φ₂ (tensorPresheaf φ₂.hom a₂.hom) X _ _

end Sheaves

end Stacks.Sites.Conormal

namespace Stacks.SheafOfModules

open Stacks.Sites.Conormal Stacks.Sites.FreeAlgebra

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [HasWeakSheafify J CommRingCat.{w}]
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable (A : Sheaf J CommRingCat.{w}) (E₁ E₂ : Functor Cᵒᵖ (Type w)) (h h' : E₁ ⟶ E₂)
  (B : Sheaf J CommRingCat.{w}) (a : A ⟶ B)
  (α₁ : E₁ ⟶ underlyingPresheaf J B) (α₂ : E₂ ⟶ underlyingPresheaf J B)
  [Presheaf.IsLocallySurjective J (presentation J A B a E₁ α₁).hom]
  [Presheaf.IsLocallySurjective J (presentation J A B a E₂ α₂).hom]
  (hα : h ≫ α₂ = α₁) (hα' : h' ≫ α₂ = α₁)

/-- The homotopy `B ⊗[A[E₁]] Ω[A[E₁]/A] ⟶ K₂/K₂²` attached to two morphisms of
presentations `h, h' : E₁ ⟶ E₂`: on local sections it sends `b ⊗ d x` to
`b · (h(x) - h'(x))`. -/
noncomputable def presentationNullHomotopy :
    (presentationConormalSequence.{v, u, w, z} J A B a E₁ α₁).X₂ ⟶
      (presentationConormalSequence.{v, u, w, z} J A B a E₂ α₂).X₁ :=
  conormalHomotopyOfFac.{v, u, w, z} J A B
    (freeAlgebraSheaf J A E₁) (freeAlgebraSheaf J A E₂)
    (freeAlgebraSheafCoefficientMap J A E₁) (freeAlgebraSheafCoefficientMap J A E₂)
    (presentation J A B a E₁ α₁) (presentation J A B a E₂ α₂)
    (freeAlgebraMap J A E₁ E₂ h) (freeAlgebraMap J A E₁ E₂ h')
    (freeAlgebraMap_comp_presentation J A E₁ E₂ h B a α₁ α₂ hα)
    (freeAlgebraMap_comp_presentation J A E₁ E₂ h' B a α₁ α₂ hα')
    (freeAlgebraSheafCoefficientMap_comp_freeAlgebraMap J A E₁ E₂ h)
    (freeAlgebraSheafCoefficientMap_comp_freeAlgebraMap J A E₁ E₂ h')

/-- The degree `0` to degree `-1` component of the homotopy, read inside the complexes
`NL(α₁)` and `NL(α₂)`. -/
noncomputable def presentationNaiveCotangentHomotopyHom :
    (presentationNaiveCotangentComplex.{v, u, w, z} J A B a E₁ α₁).X 0 ⟶
      (presentationNaiveCotangentComplex.{v, u, w, z} J A B a E₂ α₂).X (-1) :=
  eqToHom (presentationNaiveCotangentComplex_X_zero J A B a E₁ α₁) ≫
    presentationNullHomotopy.{v, u, w, z} J A E₁ E₂ h h' B a α₁ α₂ hα hα' ≫
      eqToHom (presentationNaiveCotangentComplex_X_negOne J A B a E₂ α₂).symm

/-- The two maps of conormal sheaves induced by two morphisms of presentations differ by the
homotopy precomposed with the left-hand map of the first conormal sequence. -/
theorem presentationConormalMap_eq_add :
    presentationConormalMap.{v, u, w, z} J A E₁ E₂ h B a α₁ α₂ hα =
      (((presentationConormalSequence.{v, u, w, z} J A B a E₁ α₁).f ≫
            presentationNullHomotopy.{v, u, w, z} J A E₁ E₂ h h' B a α₁ α₂ hα hα' :
          (presentationConormalSequence.{v, u, w, z} J A B a E₁ α₁).X₁ ⟶
            (presentationConormalSequence.{v, u, w, z} J A B a E₂ α₂).X₁)) +
        presentationConormalMap.{v, u, w, z} J A E₁ E₂ h' B a α₁ α₂ hα' :=
  conormalSheafMapOfFac_eq_add.{v, u, w, z} J A B
    (freeAlgebraSheaf J A E₁) (freeAlgebraSheaf J A E₂)
    (freeAlgebraSheafCoefficientMap J A E₁) (freeAlgebraSheafCoefficientMap J A E₂)
    (presentation J A B a E₁ α₁) (presentation J A B a E₂ α₂)
    (freeAlgebraMap J A E₁ E₂ h) (freeAlgebraMap J A E₁ E₂ h')
    (freeAlgebraMap_comp_presentation J A E₁ E₂ h B a α₁ α₂ hα)
    (freeAlgebraMap_comp_presentation J A E₁ E₂ h' B a α₁ α₂ hα')
    (freeAlgebraSheafCoefficientMap_comp_freeAlgebraMap J A E₁ E₂ h)
    (freeAlgebraSheafCoefficientMap_comp_freeAlgebraMap J A E₁ E₂ h')

/-- The two maps of tensor terms induced by two morphisms of presentations differ by the
homotopy postcomposed with the left-hand map of the second conormal sequence. -/
theorem presentationTensorMap_eq_add :
    presentationTensorMap.{v, u, w, z} J A E₁ E₂ h B a α₁ α₂ hα =
      ((presentationNullHomotopy.{v, u, w, z} J A E₁ E₂ h h' B a α₁ α₂ hα hα' ≫
            (presentationConormalSequence.{v, u, w, z} J A B a E₂ α₂).f :
          (presentationConormalSequence.{v, u, w, z} J A B a E₁ α₁).X₂ ⟶
            (presentationConormalSequence.{v, u, w, z} J A B a E₂ α₂).X₂)) +
        presentationTensorMap.{v, u, w, z} J A E₁ E₂ h' B a α₁ α₂ hα' :=
  tensorSheafMapOfFac_eq_add.{v, u, w, z} J A B
    (freeAlgebraSheaf J A E₁) (freeAlgebraSheaf J A E₂)
    (freeAlgebraSheafCoefficientMap J A E₁) (freeAlgebraSheafCoefficientMap J A E₂)
    (presentation J A B a E₁ α₁) (presentation J A B a E₂ α₂)
    (freeAlgebraMap J A E₁ E₂ h) (freeAlgebraMap J A E₁ E₂ h')
    (freeAlgebraMap_comp_presentation J A E₁ E₂ h B a α₁ α₂ hα)
    (freeAlgebraMap_comp_presentation J A E₁ E₂ h' B a α₁ α₂ hα')
    (freeAlgebraSheafCoefficientMap_comp_freeAlgebraMap J A E₁ E₂ h)
    (freeAlgebraSheafCoefficientMap_comp_freeAlgebraMap J A E₁ E₂ h')

/-- The bigraded map underlying the homotopy: it is concentrated in bidegree `(0, -1)`. -/
noncomputable def presentationNaiveCotangentHomotopyBigraded (i j : ℤ) :
    (presentationNaiveCotangentComplex.{v, u, w, z} J A B a E₁ α₁).X i ⟶
      (presentationNaiveCotangentComplex.{v, u, w, z} J A B a E₂ α₂).X j :=
  if hij : i = 0 ∧ j = -1 then
    eqToHom (congrArg (presentationNaiveCotangentComplex.{v, u, w, z} J A B a E₁ α₁).X hij.1) ≫
      presentationNaiveCotangentHomotopyHom.{v, u, w, z} J A E₁ E₂ h h' B a α₁ α₂ hα hα' ≫
        eqToHom (congrArg (presentationNaiveCotangentComplex.{v, u, w, z} J A B a E₂ α₂).X
          hij.2.symm)
  else 0

/-- The bigraded map underlying the homotopy vanishes outside bidegree `(0, -1)`. -/
theorem presentationNaiveCotangentHomotopyBigraded_eq_zero (i j : ℤ)
    (hij : ¬(i = 0 ∧ j = -1)) :
    presentationNaiveCotangentHomotopyBigraded.{v, u, w, z} J A E₁ E₂ h h' B a α₁ α₂
      hα hα' i j = 0 :=
  dite_eq_right hij

/-- In bidegree `(0, -1)` the bigraded map underlying the homotopy is
`presentationNaiveCotangentHomotopyHom`. -/
theorem presentationNaiveCotangentHomotopyBigraded_zero_negOne :
    presentationNaiveCotangentHomotopyBigraded.{v, u, w, z} J A E₁ E₂ h h' B a α₁ α₂
        hα hα' 0 (-1) =
      presentationNaiveCotangentHomotopyHom.{v, u, w, z} J A E₁ E₂ h h' B a α₁ α₂ hα hα' := by
  rw [presentationNaiveCotangentHomotopyBigraded, dite_eq_left ⟨rfl, rfl⟩]
  simp

/-- Two morphisms `h, h' : E₁ ⟶ E₂` of families of generators presenting the same sheaf of
rings `B` over `A` induce homotopic chain maps `NL(α₁) ⟶ NL(α₂)`, by a homotopy concentrated in
bidegree `(0, -1)`, where it is the map determined on local sections by
`b ⊗ d x ↦ b · (h(x) - h'(x))`. -/
noncomputable def presentationNaiveCotangentComplexHomotopy :
    Homotopy (presentationNaiveCotangentComplexMap.{v, u, w, z} J A E₁ E₂ h B a α₁ α₂ hα)
      (presentationNaiveCotangentComplexMap.{v, u, w, z} J A E₁ E₂ h' B a α₁ α₂ hα') where
  hom := presentationNaiveCotangentHomotopyBigraded.{v, u, w, z} J A E₁ E₂ h h' B a α₁ α₂ hα hα'
  zero i j hij :=
    presentationNaiveCotangentHomotopyBigraded_eq_zero.{v, u, w, z} J A E₁ E₂ h h' B a α₁ α₂
      hα hα' i j (by rintro ⟨rfl, rfl⟩; exact hij (by decide))
  comm i := by
    by_cases h1 : i = -1
    · subst h1
      rw [dNext_eq _ (show (ComplexShape.up ℤ).Rel (-1) 0 from by decide),
        prevD_eq _ (show (ComplexShape.up ℤ).Rel (-2) (-1) from by decide),
        presentationNaiveCotangentHomotopyBigraded_eq_zero _ _ _ _ _ _ _ _ _ _ _ _ (-1) (-2)
          (by rintro ⟨h0, -⟩; exact absurd h0 (by decide)),
        zero_comp, add_zero,
        presentationNaiveCotangentHomotopyBigraded_zero_negOne,
        presentationNaiveCotangentComplexMap_f_negOne,
        presentationNaiveCotangentComplexMap_f_negOne,
        presentationNaiveCotangentComplex_d_negOne_zero,
        presentationNaiveCotangentHomotopyHom,
        presentationConormalMap_eq_add.{v, u, w, z} J A E₁ E₂ h h' B a α₁ α₂ hα hα']
      simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp,
        Preadditive.add_comp, Preadditive.comp_add]
    · by_cases h0 : i = 0
      · subst h0
        rw [dNext_eq _ (show (ComplexShape.up ℤ).Rel 0 1 from by decide),
          prevD_eq _ (show (ComplexShape.up ℤ).Rel (-1) 0 from by decide),
          presentationNaiveCotangentComplex_d_zero, zero_comp, zero_add,
          presentationNaiveCotangentHomotopyBigraded_zero_negOne,
          presentationNaiveCotangentComplexMap_f_zero,
          presentationNaiveCotangentComplexMap_f_zero,
          presentationNaiveCotangentComplex_d_negOne_zero,
          presentationNaiveCotangentHomotopyHom,
          presentationTensorMap_eq_add.{v, u, w, z} J A E₁ E₂ h h' B a α₁ α₂ hα hα']
        simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp,
          Preadditive.add_comp, Preadditive.comp_add]
      · exact (presentationNaiveCotangentComplex_isZero_X J A B a E₁ α₁ i h1 h0).eq_of_src _ _

end Stacks.SheafOfModules

end
