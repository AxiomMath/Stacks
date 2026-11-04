module

public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.HomologySequence
public import Mathlib.Algebra.Homology.ShortComplex.Abelian
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Abelian.Transfer
public import Mathlib.CategoryTheory.DifferentialObject
public import Mathlib.CategoryTheory.Limits.Constructions.FiniteProductsOfBinaryProducts
public import StacksCore.Tactic.StacksAttribute

/-!
# Differential objects in an abelian category

A differential object of an abelian category is an object `A` with an endomorphism `d` such
that `d ≫ d = 0`. Differential objects form an abelian category, each has a homology
`H(A, d) = Ker(d)/Im(d)`, and a short exact sequence of differential objects has a long exact
homology sequence.

## Main definitions

* `StacksDifferentialObject`: an object with an endomorphism squaring to zero.
* `stacksDifferentialObject_abelianStructure`: the abelian structure on differential objects.
* `StacksDifferentialObject.homology`: the homology `H(A, d)`.

## Main results

* `nonempty_abelian_stacksDifferentialObject`: differential objects of an abelian category form
  an abelian category.
* `StacksDifferentialObject.ShortExactSequence.homology_exact_sequence`: the homology sequence of
  a short exact sequence of differential objects is exact.
-/

@[expose] public section

add_to_stacks 011V "object" CategoryTheory.DifferentialObject
add_to_stacks 011V "morphism" CategoryTheory.DifferentialObject.Hom

section

/-!
## Differential objects form an abelian category

For any abelian category `C`, the category of differential objects of `C`
(pairs `(X, d)` with `d ≫ d = 0`) is itself an abelian category.
-/

open CategoryTheory

/-- A differential object of a category `C` with zero morphisms is a pair
`(X, d)` where `X : C` and `d : X ⟶ X` satisfies `d ≫ d = 0`. -/
structure StacksDifferentialObject (C : Type*) [Category C] [Limits.HasZeroMorphisms C] where
  /-- The underlying object. -/
  X : C
  /-- The differential. -/
  d : X ⟶ X
  /-- The differential squares to zero. -/
  d_sq : d ≫ d = 0

namespace StacksDifferentialObject

variable {C : Type*} [Category C] [Limits.HasZeroMorphisms C]

/-- A morphism of differential objects: a morphism in `C` that commutes with
the differentials. -/
@[ext]
structure Hom (M N : StacksDifferentialObject C) where
  /-- The underlying morphism in `C`. -/
  f : M.X ⟶ N.X
  /-- Compatibility with the differential. -/
  comm : f ≫ N.d = M.d ≫ f

/-- The identity morphism of a differential object. -/
@[simps]
def id (M : StacksDifferentialObject C) : Hom M M where
  f := 𝟙 _
  comm := by simp

/-- Composition of morphisms of differential objects. -/
@[simps]
def comp {M N K : StacksDifferentialObject C} (φ : Hom M N) (ψ : Hom N K) : Hom M K where
  f := φ.f ≫ ψ.f
  comm := by
    rw [Category.assoc, ψ.comm, ← Category.assoc, φ.comm, Category.assoc]

/-- Differential objects and their morphisms form a category. -/
instance category : Category (StacksDifferentialObject C) where
  Hom := Hom
  id := id
  comp := comp
  id_comp _ := by ext; simp [id, comp]
  comp_id _ := by ext; simp [id, comp]
  assoc _ _ _ := by ext; simp [comp]

end StacksDifferentialObject

universe v u

private lemma XIsoOfEq_comm_d {C : Type u} [Category.{v} C] [Limits.HasZeroMorphisms C]
    (K : HomologicalComplex C (ComplexShape.refl Unit)) (i j : Unit) :
    (K.XIsoOfEq (Subsingleton.elim () i)).hom ≫ K.d i j =
      K.d () () ≫ (K.XIsoOfEq (Subsingleton.elim () j)).hom := by
  cases i; cases j; simp

/-- A differential object is a complex on the singleton shape with its loop allowed. -/
@[simps, implicit_reducible]
def differentialObjectToComplex
    (C : Type u) [Category.{v} C] [Limits.HasZeroMorphisms C] :
    StacksDifferentialObject C ⥤ HomologicalComplex C (ComplexShape.refl Unit) where
  obj M :=
    { X := fun _ ↦ M.X
      d := fun _ _ ↦ M.d
      shape i j h := (h (by simp)).elim
      d_comp_d' := by intros; exact M.d_sq }
  map φ := { f := fun _ ↦ φ.f, comm' := by intros; exact φ.comm }
  map_id _ := rfl
  map_comp _ _ := rfl

@[simps, implicit_reducible]
private def complexToDifferentialObject
    (C : Type u) [Category.{v} C] [Limits.HasZeroMorphisms C] :
    HomologicalComplex C (ComplexShape.refl Unit) ⥤ StacksDifferentialObject C where
  obj K := ⟨K.X Unit.unit, K.d Unit.unit Unit.unit, K.d_comp_d _ _ _⟩
  map φ := ⟨φ.f Unit.unit, φ.comm _ _⟩
  map_id _ := rfl
  map_comp _ _ := rfl

private def differentialObjectComplexEquivalence
    (C : Type u) [Category.{v} C] [Limits.HasZeroMorphisms C] :
    StacksDifferentialObject C ≌ HomologicalComplex C (ComplexShape.refl Unit) :=
  CategoryTheory.Equivalence.mk (differentialObjectToComplex C) (complexToDifferentialObject C)
    (NatIso.ofComponents (fun _ ↦ Iso.refl _))
    (NatIso.ofComponents
      (fun K ↦ HomologicalComplex.Hom.isoOfComponents
        (fun i ↦ K.XIsoOfEq (Subsingleton.elim _ i)) (fun i j _ ↦ XIsoOfEq_comm_d K i j))
      (by intro K L φ; ext ⟨⟩; simp))

private lemma differentialObjectHasFiniteLimits
    (C : Type*) [Category C] [Abelian C] :
    Limits.HasFiniteLimits (StacksDifferentialObject C) :=
  ⟨fun _ ↦ Adjunction.hasLimitsOfShape_of_equivalence
    (differentialObjectComplexEquivalence C).functor⟩

private lemma differentialObjectHasFiniteColimits
    (C : Type*) [Category C] [Abelian C] :
    Limits.HasFiniteColimits (StacksDifferentialObject C) :=
  ⟨fun _ ↦ Adjunction.hasColimitsOfShape_of_equivalence
    (differentialObjectComplexEquivalence C).functor⟩

/-- Differential objects of an abelian category admit a preadditive structure. -/
lemma nonempty_preadditive_stacksDifferentialObject
    (C : Type*) [Category C] [Abelian C] :
    Nonempty (Preadditive (StacksDifferentialObject C)) :=
  ⟨Preadditive.ofFullyFaithful (differentialObjectComplexEquivalence C).fullyFaithfulFunctor⟩

/-- Differential objects of an abelian category have a zero object. -/
lemma nonempty_hasZeroObject_stacksDifferentialObject
    (C : Type*) [Category C] [Abelian C]
    [Preadditive (StacksDifferentialObject C)] :
    Nonempty (Limits.HasZeroObject (StacksDifferentialObject C)) := by
  let := differentialObjectHasFiniteLimits C
  exact ⟨Limits.hasZeroObject_of_hasTerminal_object⟩

/-- Differential objects of an abelian category have binary biproducts. -/
lemma nonempty_hasBinaryBiproducts_stacksDifferentialObject
    (C : Type*) [Category C] [Abelian C]
    [Preadditive (StacksDifferentialObject C)] :
    Nonempty (Limits.HasBinaryBiproducts (StacksDifferentialObject C)) := by
  let := differentialObjectHasFiniteLimits C
  let := Limits.HasFiniteBiproducts.of_hasFiniteProducts (C := StacksDifferentialObject C)
  exact ⟨Limits.hasBinaryBiproducts_of_finite_biproducts (StacksDifferentialObject C)⟩

/-- Differential objects of an abelian category have kernels. -/
lemma nonempty_hasKernels_stacksDifferentialObject
    (C : Type*) [Category C] [Abelian C]
    [Preadditive (StacksDifferentialObject C)] :
    Nonempty (Limits.HasKernels (StacksDifferentialObject C)) := by
  let := differentialObjectHasFiniteLimits C
  exact ⟨inferInstance⟩

/-- Differential objects of an abelian category have cokernels. -/
lemma nonempty_hasCokernels_stacksDifferentialObject
    (C : Type*) [Category C] [Abelian C]
    [Preadditive (StacksDifferentialObject C)] :
    Nonempty (Limits.HasCokernels (StacksDifferentialObject C)) := by
  let := differentialObjectHasFiniteColimits C
  exact ⟨inferInstance⟩

/-- The abelian structure on differential objects, built from the equivalence with complexes. -/
private noncomputable abbrev abelianOfPreadditive
    (C : Type*) [Category C] [Abelian C] [Preadditive (StacksDifferentialObject C)] :
    Abelian (StacksDifferentialObject C) :=
  have := differentialObjectHasFiniteLimits C
  abelianOfEquivalence (differentialObjectComplexEquivalence C).functor

/-- In the category of differential objects of an abelian category every monomorphism is
normal. -/
lemma nonempty_isNormalMonoCategory_stacksDifferentialObject
    (C : Type*) [Category C] [Abelian C]
    [Preadditive (StacksDifferentialObject C)]
    [Limits.HasKernels (StacksDifferentialObject C)]
    [Limits.HasCokernels (StacksDifferentialObject C)] :
    Nonempty (IsNormalMonoCategory (StacksDifferentialObject C)) := by
  let := abelianOfPreadditive C
  exact ⟨inferInstance⟩

/-- In the category of differential objects of an abelian category every epimorphism is normal. -/
lemma nonempty_isNormalEpiCategory_stacksDifferentialObject
    (C : Type*) [Category C] [Abelian C]
    [Preadditive (StacksDifferentialObject C)]
    [Limits.HasKernels (StacksDifferentialObject C)]
    [Limits.HasCokernels (StacksDifferentialObject C)] :
    Nonempty (IsNormalEpiCategory (StacksDifferentialObject C)) := by
  let := abelianOfPreadditive C
  exact ⟨inferInstance⟩

/-- Differential objects of an abelian category have finite products. -/
lemma nonempty_hasFiniteProducts_stacksDifferentialObject
    (C : Type*) [Category C] [Abelian C]
    [Preadditive (StacksDifferentialObject C)]
    [Limits.HasZeroObject (StacksDifferentialObject C)]
    [Limits.HasBinaryBiproducts (StacksDifferentialObject C)] :
    Nonempty (Limits.HasFiniteProducts (StacksDifferentialObject C)) :=
  ⟨hasFiniteProducts_of_has_binary_and_terminal⟩

/-- Differential objects of an abelian category form an abelian category. -/
lemma nonempty_abelian_stacksDifferentialObject
    (C : Type*) [Category C] [Abelian C] :
    Nonempty (Abelian (StacksDifferentialObject C)) := by
  obtain ⟨_⟩ := nonempty_preadditive_stacksDifferentialObject C
  exact ⟨abelianOfPreadditive C⟩

/-- The abelian structure on the category of differential objects of an abelian category. -/
@[reducible, stacks 011W "structure"]
noncomputable def stacksDifferentialObject_abelianStructure
    (C : Type*) [Category C] [Abelian C] :
    Abelian (StacksDifferentialObject C) :=
  Classical.choice (nonempty_abelian_stacksDifferentialObject C)

@[stacks 011W "nonempty"]
alias stacksDifferentialObject_abelian := nonempty_abelian_stacksDifferentialObject

end


section

/-!
## Homology of a differential object

For a differential object `(A, d)` its *homology* is `H(A, d) = Ker(d)/Im(d)`, the homology of the
short complex `A --d--> A --d--> A`, which is canonically isomorphic to
`cokernel (kernel.lift d d _)`.
-/

open CategoryTheory Limits

namespace StacksDifferentialObject

variable {C : Type*} [Category C]

/-- The short complex `A --d--> A --d--> A` of a differential object `(A, d)`. -/
@[simps!]
def toShortComplex [HasZeroMorphisms C] (A : StacksDifferentialObject C) : ShortComplex C :=
  ShortComplex.mk A.d A.d A.d_sq

/-- A morphism of differential objects induces a morphism of the short complexes. -/
@[simps]
def shortComplexMap [HasZeroMorphisms C] {A B : StacksDifferentialObject C} (φ : A ⟶ B) :
    A.toShortComplex ⟶ B.toShortComplex where
  τ₁ := φ.f
  τ₂ := φ.f
  τ₃ := φ.f
  comm₁₂ := φ.comm
  comm₂₃ := φ.comm

variable [Abelian C]

/-- The homology `H(A, d) = Ker(d)/Im(d)` of a differential object, as the homology of
`A --d--> A --d--> A`. -/
@[stacks 011X]
noncomputable abbrev homology (A : StacksDifferentialObject C) : C :=
  A.toShortComplex.homology

/-- The map on homology induced by a morphism of differential objects. -/
noncomputable def homologyMap {A B : StacksDifferentialObject C} (φ : A ⟶ B) :
    A.homology ⟶ B.homology :=
  ShortComplex.homologyMap (shortComplexMap φ)

/-- The literal `Ker(d)/Im(d)`: the cokernel of the factorisation of `d` through `kernel d`. -/
noncomputable def kerModIm (A : StacksDifferentialObject C) : C :=
  cokernel (kernel.lift A.d A.d A.d_sq)

/-- The homology `H(A, d)` is canonically isomorphic to `cokernel (kernel.lift d d _)`. -/
noncomputable def homologyIsoKerModIm (A : StacksDifferentialObject C) :
    A.homology ≅ A.kerModIm :=
  A.toShortComplex.homologyIsoCokernelLift

/-- An object is isomorphic to `Ker(d)/Im(d)` iff it is isomorphic to `A.homology`. -/
theorem isHomology_iff (A : StacksDifferentialObject C) (H : C) :
    Nonempty (H ≅ A.kerModIm) ↔ Nonempty (H ≅ A.homology) :=
  ⟨fun ⟨f⟩ ↦ ⟨f.trans A.homologyIsoKerModIm.symm⟩, fun ⟨f⟩ ↦ ⟨f.trans A.homologyIsoKerModIm⟩⟩

end StacksDifferentialObject

end

section

/-!
## The long exact homology sequence

Let `𝒜` be an abelian category and `0 → (A, d) → (B, d) → (C, d) → 0` a short exact sequence of
differential objects. Then there is an exact homology sequence

  `… → H(C, d) → H(A, d) → H(B, d) → H(C, d) → …`

encoded as the three exact pieces of the periodic sequence. The connecting map is the one of the
homology sequence of the associated short exact sequence of complexes on the shape
`ComplexShape.refl Unit`.
-/

open CategoryTheory Limits

namespace StacksDifferentialObject

variable {𝒜 : Type*} [Category 𝒜] [Abelian 𝒜]

/-- A short exact sequence of differential objects `0 → (A, d) → (B, d) → (C, d) → 0`: two
morphisms of differential objects whose underlying short complex in `𝒜` is short exact. -/
structure ShortExactSequence (𝒜 : Type*) [Category 𝒜] [Abelian 𝒜] where
  /-- The first (sub) differential object. -/
  A : StacksDifferentialObject 𝒜
  /-- The middle differential object. -/
  B : StacksDifferentialObject 𝒜
  /-- The last (quotient) differential object. -/
  C : StacksDifferentialObject 𝒜
  /-- The inclusion morphism. -/
  f : A ⟶ B
  /-- The projection morphism. -/
  g : B ⟶ C
  /-- The composition of the underlying maps is zero. -/
  zero : f.f ≫ g.f = 0
  /-- The underlying short complex `A.X → B.X → C.X` is short exact. -/
  shortExact : (ShortComplex.mk f.f g.f zero).ShortExact

namespace ShortExactSequence

variable (S : ShortExactSequence 𝒜)

/-- The map `H(A, d) ⟶ H(B, d)` induced by `f : A ⟶ B`. -/
noncomputable def homologyMap₁ : S.A.homology ⟶ S.B.homology :=
  StacksDifferentialObject.homologyMap S.f

/-- The map `H(B, d) ⟶ H(C, d)` induced by `g : B ⟶ C`. -/
noncomputable def homologyMap₂ : S.B.homology ⟶ S.C.homology :=
  StacksDifferentialObject.homologyMap S.g

/-- The short complex of complexes on `ComplexShape.refl Unit` attached to `S`. -/
noncomputable def toComplexes : ShortComplex (HomologicalComplex 𝒜 (ComplexShape.refl Unit)) :=
  ShortComplex.mk ((differentialObjectToComplex 𝒜).map S.f)
    ((differentialObjectToComplex 𝒜).map S.g) (by ext; exact S.zero)

/-- The short complex of complexes attached to `S` is short exact. -/
lemma toComplexes_shortExact : S.toComplexes.ShortExact :=
  HomologicalComplex.shortExact_of_degreewise_shortExact _ fun _ ↦ S.shortExact

/-- The connecting morphism `δ : H(C, d) ⟶ H(A, d)`. -/
noncomputable def δ : S.C.homology ⟶ S.A.homology :=
  S.toComplexes_shortExact.δ () () rfl

/-- The composite `H(A, d) ⟶ H(B, d) ⟶ H(C, d)` is zero. -/
lemma homologyMap₁_comp_homologyMap₂ : S.homologyMap₁ ≫ S.homologyMap₂ = 0 := by
  rw [homologyMap₁, homologyMap₂, homologyMap, homologyMap, ← ShortComplex.homologyMap_comp,
    show shortComplexMap S.f ≫ shortComplexMap S.g = 0 from
      ShortComplex.hom_ext _ _ S.zero S.zero S.zero, ShortComplex.homologyMap_zero]

/-- The composite `H(B, d) ⟶ H(C, d) ⟶ H(A, d)` of `homologyMap₂` and `δ` is zero. -/
lemma homologyMap₂_comp_δ : S.homologyMap₂ ≫ S.δ = 0 :=
  S.toComplexes_shortExact.comp_δ () () rfl

/-- The composite `H(C, d) ⟶ H(A, d) ⟶ H(B, d)` of `δ` and `homologyMap₁` is zero. -/
lemma δ_comp_homologyMap₁ : S.δ ≫ S.homologyMap₁ = 0 :=
  S.toComplexes_shortExact.δ_comp () () rfl

/-- For a short exact sequence `0 → (A, d) → (B, d) → (C, d) → 0` of
differential objects there is a connecting morphism `δ : H(C, d) ⟶ H(A, d)` making the periodic
sequence `H(A, d) → H(B, d) → H(C, d) -δ→ H(A, d) → H(B, d) → ⋯` exact at every spot. -/
@[stacks 011Y]
theorem homology_exact_sequence :
    ∃ (δ : S.C.homology ⟶ S.A.homology)
      (h₁ : S.homologyMap₁ ≫ S.homologyMap₂ = 0)
      (h₂ : S.homologyMap₂ ≫ δ = 0)
      (h₃ : δ ≫ S.homologyMap₁ = 0),
      (ShortComplex.mk S.homologyMap₁ S.homologyMap₂ h₁).Exact ∧
      (ShortComplex.mk S.homologyMap₂ δ h₂).Exact ∧
      (ShortComplex.mk δ S.homologyMap₁ h₃).Exact :=
  ⟨S.δ, S.homologyMap₁_comp_homologyMap₂, S.homologyMap₂_comp_δ, S.δ_comp_homologyMap₁,
    S.toComplexes_shortExact.homology_exact₂ (), S.toComplexes_shortExact.homology_exact₃ () () rfl,
    S.toComplexes_shortExact.homology_exact₁ () () rfl⟩

end ShortExactSequence

end StacksDifferentialObject

end
