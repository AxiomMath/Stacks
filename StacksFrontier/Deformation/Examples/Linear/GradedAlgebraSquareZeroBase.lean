module

public import StacksFrontier.Deformation.Examples.Linear.GradedAlgebrasPieces
public import StacksFrontier.Deformation.TangentSpace.Functor
public import StacksFrontier.Deformation.Terminal

/-!
# The base of a graded deformation over a square-zero extension

Let `P` be a graded `k`-algebra, finite-dimensional in each degree, and let `A` be an object of
`𝒞_Λ`. An object of the fibre over `A` of the deformation category of `P` is a graded algebra
`X` over a base algebra together with a *propositional* equality `X.base = A` and a reduction
`X ⟶ (k, P)`. This file turns that equality into usable algebra data and records what the
reduction map does.

Two things are needed downstream and both are supplied here. The first is the identification of
the base: an equality of objects of `𝒞_Λ` gives a `Λ`-algebra equivalence of the underlying
algebras, which for `A` the square-zero extension `k ⊕ V` identifies `X.base` with
`TrivSqZeroExt k V` compatibly with the reduction of the base to `k`. The second is the
behaviour of the reduction map `X.carrier → P`: it is semilinear for the residue map of
`X.base`, it is surjective, and it lifts homogeneous elements to homogeneous elements of the
same degree.

## Main definitions

* `Deformation.ArtinianLocalAlgCat.algEquivOfIso` and
  `Deformation.ArtinianLocalAlgCat.algEquivOfEq`: an isomorphism, respectively an equality, of
  objects of `𝒞_Λ` as a `Λ`-algebra equivalence of the underlying algebras.
* `Deformation.Examples.ProjectiveGradedAlgebra.baseResidueHom` and
  `Deformation.Examples.ProjectiveGradedAlgebra.reductionHom`: the base map and the map of a
  reduction to the special fibre, named at the ambient types `k` and `P` rather than at the
  carriers of the special-fibre object.
* `Deformation.Examples.ProjectiveGradedAlgebra.deformationFiber`: the fibre of the deformation
  category over an object of `𝒞_Λ`.
* `Deformation.Examples.ProjectiveGradedAlgebra.squareZeroBaseAlgEquiv`: the base of an object
  of the fibre over the square-zero extension `k ⊕ V`, identified with that extension, whose
  underlying type is `TrivSqZeroExt k V`.
* `Deformation.SquareZeroThickening.kerAlgebraMapEquiv`: the square-zero ideal of that base,
  identified with `V` itself.

## Main results

* `Deformation.Examples.hom_residueFieldBase_apply`: a morphism of `𝒞_Λ` into the residue-field
  object is the residue map followed by the chosen identification; in particular there is at
  most one such morphism, and it is surjective.
* `Deformation.Examples.ProjectiveGradedAlgebra.reductionHom_smul`: the reduction map of a
  deformation is semilinear for the residue map of its base.
* `Deformation.Examples.ProjectiveGradedAlgebra.hom_map_surjective`: the reduction map of a
  deformation is surjective, and
  `Deformation.Examples.ProjectiveGradedAlgebra.exists_mem_grading_map_eq`: it lifts a
  homogeneous element to a homogeneous element of the same degree.
* `Deformation.Examples.ProjectiveGradedAlgebra.squareZeroBaseAlgEquiv_fst`: the first
  coordinate of the base identification is the reduction of the base to `k`.
* `Deformation.Examples.ProjectiveGradedAlgebra.hom_map_smul_eq_zero_of_fst_eq_zero`: the
  square-zero ideal of the base annihilates the reduction.
* `Deformation.SquareZeroThickening.algebraMap_retraction` and
  `Deformation.SquareZeroThickening.ker_algebraMap_mul_self`: the square-zero object of `𝒞_Λ`
  is a square-zero thickening of `k`, the retraction being the constant coordinate.

## Implementation notes

No `cases`-on-structure unpacking of the fibre object is needed. The graded algebra data —
the commutative ring structure on the carrier, the algebra structure over the base, the
grading and its degreewise finiteness and projectivity — are instance fields of
`Deformation.Examples.ProjectiveGradedAlgebra` and are therefore already available on
`x.1.left` for an object `x` of the fibre. The only datum that must be moved is the base
equality, and it is moved as an algebra equivalence rather than by transporting the graded
algebra: this is the idiom under which the base algebra of a deformation is described by a ring
equivalence while the deformation itself stays over its own base, so that no scalar structure
has to be transported and no `rfl`-spelling of the base ever has to be matched.

The square-zero object of `𝒞_Λ` is exhibited as a square-zero thickening of `k` — a `k`-algebra
with a retraction onto `k` whose kernel has square zero — in the shape in which
`SquareZeroRetraction` takes that datum: the retraction is `algebraMap A k` for an `Algebra A k`
instance, and the retraction and square-zero conditions are theorems about it rather than
structure fields. Both algebra instances are `scoped`, because neither is canonical: a consumer
writes `open Deformation.SquareZeroThickening` to bring them into scope, and then every module
structure appearing in the statements below — including the `k`-module structure on the kernel of
the retraction — is found by instance search, so no statement carries a `letI` prefix. The two
`Module kᵐᵒᵖ V` and `IsCentralScalar k V` instances that the `k`-algebra structure of a trivial
square-zero extension requires are `scoped` here for the same reason; they are the only place in
this file where an instance is introduced rather than found.

Surjectivity of the reduction map is read off the base-change condition through
`CategoryTheory.IsBaseChange.inductionOn`, using that the reduction of the base to `k` is
surjective, which in turn is the surjectivity of the residue map. Lifting a homogeneous element
then only needs that a base-change morphism commutes with the projections onto graded pieces,
which is `Deformation.Examples.ProjectiveGradedAlgebra.gradedHom_proj_apply`.

## References

* [Stacks Project, Tag 0DVZ](https://stacks.math.columbia.edu/tag/0DVZ)
* [Stacks Project, Tag 0D3L](https://stacks.math.columbia.edu/tag/0D3L)
-/

@[expose] public section

open CategoryTheory IsLocalRing

namespace Deformation

universe u v w m

/-! ### Identifications of objects of `𝒞_Λ` -/

namespace ArtinianLocalAlgCat

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]

/-- An isomorphism of `𝒞_Λ` as a `Λ`-algebra equivalence of the underlying algebras. -/
public def algEquivOfIso {A B : ArtinianLocalAlgCat.{u, v, w} Λ k} (e : A ≅ B) : A ≃ₐ[Λ] B :=
  AlgEquiv.ofAlgHom e.hom.hom e.inv.hom
    (congrArg (fun f : B ⟶ B ↦ f.hom) e.inv_hom_id)
    (congrArg (fun f : A ⟶ A ↦ f.hom) e.hom_inv_id)

/-- The equivalence attached to an isomorphism acts as the underlying algebra map. -/
@[simp]
public theorem algEquivOfIso_apply {A B : ArtinianLocalAlgCat.{u, v, w} Λ k} (e : A ≅ B)
    (a : A) : algEquivOfIso e a = e.hom.hom a := rfl

/-- The equivalence attached to an equality acts as the comparison morphism.

`algEquivOfEq` itself is not defined here: `Deformation.ArtinianLocalAlgCat.algEquivOfEq` already
exists, in `StacksFrontier/Deformation/Terminal.lean`. It is defined there by `subst`, so this
`@[simp]` lemma — not `rfl` — is what gives it the computational content the identifications
below need. -/
@[simp]
public theorem algEquivOfEq_apply {A B : ArtinianLocalAlgCat.{u, v, w} Λ k} (h : A = B)
    (a : A) : algEquivOfEq h a = (eqToHom h).hom a := by
  subst h
  rfl

/-- The equivalence attached to a reflexivity proof is the identity. -/
@[simp]
public theorem algEquivOfEq_refl (A : ArtinianLocalAlgCat.{u, v, w} Λ k) :
    algEquivOfEq (rfl : A = A) = AlgEquiv.refl := by
  ext a
  rfl

/-- The equivalence attached to an equality is compatible with the chosen identifications of
the residue fields. -/
public theorem residueEquiv_residue_algEquivOfEq
    {A B : ArtinianLocalAlgCat.{u, v, w} Λ k} (h : A = B) (a : A) :
    B.residueEquiv (residue B (algEquivOfEq h a)) = A.residueEquiv (residue A a) := by
  rw [algEquivOfEq_apply]
  exact (eqToHom h).residue_comm a

end ArtinianLocalAlgCat

namespace Examples

/-! ### Morphisms into the residue-field object -/

section ResidueFieldBase

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]

/-- A morphism of `𝒞_Λ` into the residue-field object is the residue map followed by the chosen
identification of the residue field with `k`. There is no other candidate: the identification of
the residue field of `residueFieldBase` with `k` is inverse to its residue map, so the
compatibility of a morphism with the two identifications pins it down. -/
public theorem hom_residueFieldBase_apply {A : ArtinianLocalAlgCat.{u, w, w} Λ k}
    (f : A ⟶ residueFieldBase Λ k) (r : A) :
    f.hom r = A.residueEquiv (residue A r) :=
  (residueFieldBase_residueEquiv_residue Λ k (f.hom r)).symm.trans (f.residue_comm r)

/-- A morphism of `𝒞_Λ` into the residue-field object is surjective, being the residue map
followed by an isomorphism. -/
public theorem hom_residueFieldBase_surjective {A : ArtinianLocalAlgCat.{u, w, w} Λ k}
    (f : A ⟶ residueFieldBase Λ k) : Function.Surjective f.hom := by
  intro a
  obtain ⟨r, hr⟩ := residue_surjective (R := A) (A.residueEquiv.symm a)
  refine ⟨r, ?_⟩
  rw [hom_residueFieldBase_apply f r, hr, A.residueEquiv.apply_symm_apply]

/-- There is at most one morphism of `𝒞_Λ` from a given object into the residue-field
object. -/
public theorem hom_residueFieldBase_unique {A : ArtinianLocalAlgCat.{u, w, w} Λ k}
    (f g : A ⟶ residueFieldBase Λ k) : f = g := by
  ext r
  rw [hom_residueFieldBase_apply f r, hom_residueFieldBase_apply g r]

end ResidueFieldBase

/-! ### The reduction map of a graded deformation -/

namespace ProjectiveGradedAlgebra

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]

/-- The reduction map of a base-change morphism of graded algebras whose base map is surjective
is itself surjective: the target is generated over the source by the base, and every base scalar
comes from the source base. -/
public theorem hom_map_surjective_of_base_surjective
    {X Y : ProjectiveGradedAlgebra.{u, w, w, max w m} Λ k}
    (H : ProjectiveGradedAlgebra.Hom X Y) (hbase : Function.Surjective H.base.hom) :
    Function.Surjective H.map := by
  let : Algebra (X.base) (Y.base) := H.base.hom.toAlgebra
  let : Module (X.base) Y.carrier := Module.compHom Y.carrier H.base.hom.toRingHom
  let : IsScalarTower (X.base) (Y.base) Y.carrier :=
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  have hbc : IsBaseChange (Y.base)
      ({ H.map.toAddMonoidHom with map_smul' := H.map_smul } :
        X.carrier →ₗ[X.base] Y.carrier) := H.isBaseChange
  intro y
  induction y using hbc.inductionOn with
  | tmul z => exact ⟨z, rfl⟩
  | smul s n hn =>
      obtain ⟨z, hz⟩ := hn
      obtain ⟨r, rfl⟩ := hbase s
      exact ⟨r • z, by rw [H.map_smul, hz]⟩
  | add n₁ n₂ h₁ h₂ =>
      obtain ⟨z₁, hz₁⟩ := h₁
      obtain ⟨z₂, hz₂⟩ := h₂
      exact ⟨z₁ + z₂, by rw [map_add, hz₁, hz₂]⟩

variable (P : Type (max w m)) [CommRing P] [Algebra k P] (grading : ℕ → Submodule k P)
  [GradedAlgebra grading] [∀ d, Module.Finite k (grading d)]

/-- The base map of the reduction of a deformation, as an algebra homomorphism to `k` itself.
The carrier of the base of the special-fibre object is `k`, but its ring, field and algebra
structures are the fields of that object rather than the ambient ones; naming the map at this
type is what makes a statement about it a statement about `k`. -/
public def baseResidueHom {X : ProjectiveGradedAlgebra.{u, w, w, max w m} Λ k}
    (H : X ⟶ specialFiber (Λ := Λ) P grading) : X.base →ₐ[Λ] k := H.base.hom

/-- The base map to `k` is the base map of the morphism. -/
@[simp]
public theorem baseResidueHom_apply {X : ProjectiveGradedAlgebra.{u, w, w, max w m} Λ k}
    (H : X ⟶ specialFiber (Λ := Λ) P grading) (r : X.base) :
    baseResidueHom P grading H r = H.base.hom r := rfl

/-- The base map of the reduction of a deformation to the special fibre is the residue map of
its base. -/
public theorem baseResidueHom_eq_residueEquiv_residue
    {X : ProjectiveGradedAlgebra.{u, w, w, max w m} Λ k}
    (H : X ⟶ specialFiber (Λ := Λ) P grading) (r : X.base) :
    baseResidueHom P grading H r = X.base.residueEquiv (residue X.base r) :=
  hom_residueFieldBase_apply H.base r

/-- The base map of the reduction of a deformation to the special fibre is surjective. -/
public theorem baseResidueHom_surjective {X : ProjectiveGradedAlgebra.{u, w, w, max w m} Λ k}
    (H : X ⟶ specialFiber (Λ := Λ) P grading) :
    Function.Surjective (baseResidueHom P grading H) :=
  hom_residueFieldBase_surjective H.base

/-- The reduction map of a deformation, as a ring homomorphism into `P` itself. The carrier of
the special-fibre object is `P`, but its ring and module structures are the fields of that
object rather than the ambient ones, so a statement about scalar multiplication on it is not
a statement about the `k`-module `P` until the map is named at this type. -/
public def reductionHom {X : ProjectiveGradedAlgebra.{u, w, w, max w m} Λ k}
    (H : X ⟶ specialFiber (Λ := Λ) P grading) : X.carrier →+* P := H.map

/-- The reduction map into `P` is the map of the morphism. -/
@[simp]
public theorem reductionHom_apply {X : ProjectiveGradedAlgebra.{u, w, w, max w m} Λ k}
    (H : X ⟶ specialFiber (Λ := Λ) P grading) (z : X.carrier) :
    reductionHom P grading H z = H.map z := rfl

/-- The reduction map of a deformation is semilinear for the base map to `k`, hence by
`baseResidueHom_eq_residueEquiv_residue` for the residue map of its base. -/
public theorem reductionHom_smul {X : ProjectiveGradedAlgebra.{u, w, w, max w m} Λ k}
    (H : X ⟶ specialFiber (Λ := Λ) P grading) (r : X.base) (z : X.carrier) :
    reductionHom P grading H (r • z) =
      baseResidueHom P grading H r • reductionHom P grading H z :=
  H.map_smul r z

/-- The reduction map of a deformation to the special fibre is surjective. -/
public theorem hom_map_surjective {X : ProjectiveGradedAlgebra.{u, w, w, max w m} Λ k}
    (H : X ⟶ specialFiber (Λ := Λ) P grading) : Function.Surjective H.map :=
  hom_map_surjective_of_base_surjective H (baseResidueHom_surjective P grading H)

/-- Every homogeneous element of the special fibre is the reduction of a homogeneous element of
the same degree: the reduction map is surjective and commutes with the projections onto graded
pieces, so the degree-`d` part of any preimage is a homogeneous preimage. -/
public theorem exists_mem_grading_map_eq
    {X : ProjectiveGradedAlgebra.{u, w, w, max w m} Λ k}
    (H : X ⟶ specialFiber (Λ := Λ) P grading) (d : ℕ) {p : P} (hp : p ∈ grading d) :
    ∃ z : X.carrier, z ∈ X.grading d ∧ H.map z = p := by
  obtain ⟨z, hz⟩ := hom_map_surjective P grading H p
  refine ⟨GradedAlgebra.proj X.grading d z, ?_, ?_⟩
  · rw [GradedAlgebra.proj_apply]
    exact ((DirectSum.decomposeAlgEquiv X.grading z) d).property
  · have hproj : GradedAlgebra.proj (specialFiber (Λ := Λ) P grading).grading d (H.map z) =
        H.map (GradedAlgebra.proj X.grading d z) := gradedHom_proj_apply H d z
    rw [← hproj, hz]
    change GradedAlgebra.proj grading d p = p
    rw [GradedAlgebra.proj_apply, DirectSum.decompose_of_mem_same _ hp]

/-! ### Objects of the fibre over a square-zero extension -/

/-- The fibre of the deformation category of the graded algebra `(P, grading)` over an object
`A` of `𝒞_Λ`: the deformations of `P` whose base is `A`. -/
public abbrev deformationFiber (A : ArtinianLocalAlgCat.{u, w, w} Λ k) :=
  (objectsOverFunctor (projection.{u, w, w, max w m} (Λ := Λ) (k := k))
    (specialFiber (Λ := Λ) P grading)).Fiber A

/-- The base of a deformation in the fibre over an object `A` of `𝒞_Λ` is `A`. -/
public theorem fiber_left_base_eq {A : ArtinianLocalAlgCat.{u, w, w} Λ k}
    (x : deformationFiber.{u, w, m} P grading A) : x.1.left.base = A := x.2

/-- The base of a deformation in the fibre over the square-zero extension `k ⊕ V`, identified as
a `Λ`-algebra with that square-zero extension. The underlying type of the target is
`TrivSqZeroExt k V`, so the two coordinates of a base scalar are available as
`TrivSqZeroExt.fst` and `TrivSqZeroExt.snd`. -/
public noncomputable def squareZeroBaseAlgEquiv (V : FGModuleCat.{w} k)
    (x : deformationFiber.{u, w, m} P grading ((squareZeroExtensionArtinian Λ k).obj V)) :
    x.1.left.base ≃ₐ[Λ] ((squareZeroExtensionArtinian Λ k).obj V) :=
  ArtinianLocalAlgCat.algEquivOfEq (fiber_left_base_eq P grading x)

/-- Under the identification of the base with the square-zero extension `k ⊕ V`, the first
coordinate of a base scalar is its image under the reduction of the base to `k`. This is what
makes the square-zero structure of the base usable: the kernel of the first coordinate is the
ideal `V`, and it is the kernel of the reduction of the base. -/
public theorem squareZeroBaseAlgEquiv_fst (V : FGModuleCat.{w} k)
    (x : deformationFiber.{u, w, m} P grading ((squareZeroExtensionArtinian Λ k).obj V))
    (r : x.1.left.base) :
    TrivSqZeroExt.fst (squareZeroBaseAlgEquiv P grading V x r) =
      baseResidueHom P grading x.1.hom r := by
  have hres := ArtinianLocalAlgCat.residueEquiv_residue_algEquivOfEq
    (fiber_left_base_eq P grading x) r
  have hfst := squareZeroExtensionArtinian_residue Λ k V
    (squareZeroBaseAlgEquiv P grading V x r)
  exact (hfst.symm.trans hres).trans
    (baseResidueHom_eq_residueEquiv_residue P grading x.1.hom r).symm

/-- A base scalar whose first coordinate vanishes annihilates the reduction: the square-zero
ideal of the base is carried to zero in the special fibre. -/
public theorem hom_map_smul_eq_zero_of_fst_eq_zero (V : FGModuleCat.{w} k)
    (x : deformationFiber.{u, w, m} P grading ((squareZeroExtensionArtinian Λ k).obj V))
    {r : x.1.left.base}
    (hr : TrivSqZeroExt.fst (squareZeroBaseAlgEquiv P grading V x r) = 0)
    (z : x.1.left.carrier) :
    reductionHom P grading x.1.hom (r • z) = 0 := by
  rw [reductionHom_smul P grading x.1.hom r z,
    ← squareZeroBaseAlgEquiv_fst P grading V x r, hr, zero_smul]

end ProjectiveGradedAlgebra

end Examples

/-! ### The square-zero object of `𝒞_Λ` as a square-zero thickening of `k` -/

namespace SquareZeroThickening

variable (Λ : Type u) {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]

/-- The right action of `k` on a finitely generated module over it, needed to see a square-zero
extension of `k` by that module as a `k`-algebra. -/
public scoped instance moduleMulOpposite (V : FGModuleCat.{w} k) : Module kᵐᵒᵖ V :=
  Module.compHom V
    { toFun := MulOpposite.unop
      map_one' := rfl
      map_mul' := by simp [mul_comm]
      map_zero' := rfl
      map_add' := by intros; rfl }

/-- The left and right actions of `k` on a module over it agree. -/
public scoped instance isCentralScalar (V : FGModuleCat.{w} k) : IsCentralScalar k V where
  op_smul_eq_smul _ _ := rfl

/-- The square-zero object of `𝒞_Λ` is a `k`-algebra, the structure map being the inclusion of
the constant coordinate. -/
public noncomputable scoped instance algebraBase (V : FGModuleCat.{w} k) :
    Algebra k ((squareZeroExtensionArtinian Λ k).obj V) :=
  inferInstanceAs (Algebra k (TrivSqZeroExt k V))

/-- The retraction of the square-zero object of `𝒞_Λ` onto `k`: the constant coordinate. It is
the residue map of the object followed by the chosen identification of its residue field, so it
is the map that `Deformation.Examples.ProjectiveGradedAlgebra.squareZeroBaseAlgEquiv_fst`
computes. -/
public noncomputable scoped instance algebraRetraction (V : FGModuleCat.{w} k) :
    Algebra ((squareZeroExtensionArtinian Λ k).obj V) k :=
  (TrivSqZeroExt.fstHom k k V).toRingHom.toAlgebra

/-- The retraction is the constant coordinate. -/
@[simp]
public theorem algebraMap_apply (V : FGModuleCat.{w} k)
    (x : ((squareZeroExtensionArtinian Λ k).obj V)) :
    algebraMap ((squareZeroExtensionArtinian Λ k).obj V) k x = TrivSqZeroExt.fst x := rfl

/-- The structure map from `k` is the inclusion of the constant coordinate. -/
@[simp]
public theorem algebraMap_base_apply (V : FGModuleCat.{w} k) (r : k) :
    algebraMap k ((squareZeroExtensionArtinian Λ k).obj V) r = TrivSqZeroExt.inl r := rfl

/-- The retraction is the residue map of the object followed by the identification of its
residue field with `k`. This is what connects the thickening structure to the deformation
category, whose morphisms see the base only through its residue map. -/
public theorem algebraMap_eq_residueEquiv_residue (V : FGModuleCat.{w} k)
    (x : ((squareZeroExtensionArtinian Λ k).obj V)) :
    algebraMap ((squareZeroExtensionArtinian Λ k).obj V) k x =
      ((squareZeroExtensionArtinian Λ k).obj V).residueEquiv
        (residue ((squareZeroExtensionArtinian Λ k).obj V) x) := rfl

/-- **The retraction condition.** The retraction of the square-zero object onto `k` splits its
structure map from `k`. -/
public theorem algebraMap_retraction (V : FGModuleCat.{w} k) (r : k) :
    algebraMap ((squareZeroExtensionArtinian Λ k).obj V) k
      (algebraMap k ((squareZeroExtensionArtinian Λ k).obj V) r) = r := rfl

/-- The kernel of the retraction is the square-zero ideal of the trivial square-zero
extension. -/
public theorem ker_algebraMap_eq_kerIdeal (V : FGModuleCat.{w} k) :
    RingHom.ker (algebraMap ((squareZeroExtensionArtinian Λ k).obj V) k) =
      TrivSqZeroExt.kerIdeal k V := rfl

/-- **The square-zero condition.** The kernel of the retraction of the square-zero object onto
`k` has square zero. -/
public theorem ker_algebraMap_mul_self (V : FGModuleCat.{w} k) :
    RingHom.ker (algebraMap ((squareZeroExtensionArtinian Λ k).obj V) k) *
        RingHom.ker (algebraMap ((squareZeroExtensionArtinian Λ k).obj V) k) = ⊥ :=
  (pow_two (TrivSqZeroExt.kerIdeal k V)).symm.trans (TrivSqZeroExt.kerIdeal_sq k V)

/-- An element of the kernel of the retraction is the inclusion of its own second coordinate. -/
public theorem eq_inr_snd_of_mem_ker (V : FGModuleCat.{w} k)
    {x : ((squareZeroExtensionArtinian Λ k).obj V)}
    (hx : x ∈ RingHom.ker (algebraMap ((squareZeroExtensionArtinian Λ k).obj V) k)) :
    x = TrivSqZeroExt.inr (TrivSqZeroExt.snd x) :=
  (TrivSqZeroExt.mem_kerIdeal_iff_inr k V x).mp hx

/-- **The square-zero ideal of the base is `V` itself**: the second coordinate identifies the
kernel of the retraction with `V` as a `k`-module. The target is the module the square-zero
extension was formed from, so a first-order discrepancy living in this ideal is an element of
`V` with no further comparison. -/
public noncomputable def kerAlgebraMapEquiv (V : FGModuleCat.{w} k) :
    RingHom.ker (algebraMap ((squareZeroExtensionArtinian Λ k).obj V) k) ≃ₗ[k] V where
  toFun i := TrivSqZeroExt.snd (i : ((squareZeroExtensionArtinian Λ k).obj V))
  map_add' _ _ := TrivSqZeroExt.snd_add _ _
  map_smul' r _ := TrivSqZeroExt.snd_smul r _
  invFun v := ⟨TrivSqZeroExt.inr v,
    (TrivSqZeroExt.mem_kerIdeal_iff_inr k V (TrivSqZeroExt.inr v)).mpr
      (congrArg TrivSqZeroExt.inr (TrivSqZeroExt.snd_inr k v).symm)⟩
  left_inv i := Subtype.ext (eq_inr_snd_of_mem_ker Λ V i.2).symm
  right_inv v := TrivSqZeroExt.snd_inr k v

/-- The identification of the square-zero ideal with `V` is the second coordinate. -/
@[simp]
public theorem kerAlgebraMapEquiv_apply (V : FGModuleCat.{w} k)
    (i : RingHom.ker (algebraMap ((squareZeroExtensionArtinian Λ k).obj V) k)) :
    kerAlgebraMapEquiv Λ V i =
      TrivSqZeroExt.snd (i : ((squareZeroExtensionArtinian Λ k).obj V)) := rfl

/-- Its inverse is the inclusion as the infinitesimal coordinate. -/
@[simp]
public theorem coe_kerAlgebraMapEquiv_symm (V : FGModuleCat.{w} k) (v : V) :
    ((kerAlgebraMapEquiv Λ V).symm v : ((squareZeroExtensionArtinian Λ k).obj V)) =
      TrivSqZeroExt.inr v := rfl

variable (P : Type (max w m)) [CommRing P] [Algebra k P] (grading : ℕ → Submodule k P)
  [GradedAlgebra grading] [∀ d, Module.Finite k (grading d)]

/-- The retraction of the base of a deformation over the square-zero object is the base map of
its reduction to the special fibre. This is `squareZeroBaseAlgEquiv_fst` in the spelling the
thickening uses, and it is what lets the two descriptions of the base be used together. -/
public theorem algebraMap_squareZeroBaseAlgEquiv (V : FGModuleCat.{w} k)
    (x : Examples.ProjectiveGradedAlgebra.deformationFiber.{u, w, m} P grading
      ((squareZeroExtensionArtinian Λ k).obj V))
    (r : x.1.left.base) :
    algebraMap ((squareZeroExtensionArtinian Λ k).obj V) k
        (Examples.ProjectiveGradedAlgebra.squareZeroBaseAlgEquiv P grading V x r) =
      Examples.ProjectiveGradedAlgebra.baseResidueHom P grading x.1.hom r :=
  Examples.ProjectiveGradedAlgebra.squareZeroBaseAlgEquiv_fst P grading V x r

end SquareZeroThickening

end Deformation

end
