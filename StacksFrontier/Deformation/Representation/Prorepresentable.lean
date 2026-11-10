module

public import StacksFrontier.Deformation.Artin.Basic
public import StacksFrontier.Deformation.ClassicalCase
public import StacksFrontier.Deformation.Examples.Linear.ContinuousRepresentationsDenseRestriction
public import StacksFrontier.Deformation.Examples.Linear.ContinuousRepresentationsHull
public import StacksFrontier.Deformation.Predeformation.Associated
public import StacksFrontier.Deformation.Representation.Hull
public import StacksFrontier.Deformation.RimSchlessingerCategory.AutomorphismLifting
public import StacksFrontier.Deformation.Schlessinger.AssociatedFunctor
public import StacksFrontier.Deformation.Schlessinger.Prorepresentable

/-!
# Prorepresentability for the deformations of a representation

Let `Λ → k` be a classical base, `Γ` a finitely generated group and `ρ₀` a finite-dimensional
representation of `Γ` on a `k`-vector space `V`. The functor `F` of fibrewise isomorphism
classes of deformations of `ρ₀` has a hull — that is the first clause of Stacks 0ET1, proved in
`StacksFrontier/Deformation/Representation/Hull.lean`. This file proves the second clause: when the
`Γ`-equivariant endomorphisms of `V` are exactly the scalars, that is when
`H⁰(Γ, End_k(V)) = k`, the functor `F` is prorepresentable.

The route is the one the source takes. By Schlessinger's theorem, Stacks 06JM, it is enough that
`F` be a deformation functor whose tangent space is finite dimensional and on which the
derivation map is injective. The deformations of `ρ₀` satisfy the Rim–Schlessinger condition
unconditionally, so by the automorphism-lifting criterion of Stacks 06J8 the passage to
isomorphism classes preserves that condition exactly when automorphisms of a deformation lift
along surjections of coefficient algebras. The scalar hypothesis supplies the lift: an
automorphism of a deformation lying over the identity is multiplication by a unit of the
coefficient algebra whose residue is `1`, and such a unit lifts along a surjection. Finite
dimensionality of the tangent space is the tangent clause of Stacks 0DVT, and the derivation map
is injective because a classical base has no nonzero `Λ`-derivation of `k`.

## Main results

All in the namespace `Deformation`.

* `automorphismsLiftAlong_deformationCategoryProjection`: automorphisms of deformations of `ρ₀`
  lift along every surjection of coefficient algebras.
* `isDeformationFunctor_isomorphismClasses_representation`: the functor of isomorphism classes is
  a deformation functor.
* `isProrepresentableULift_isomorphismClasses_representation`: **Stacks 0ET1**,
  prorepresentability.

## Implementation notes

The deformation category is `Deformation.deformationCategoryProjection`, the
`Deformation.RepresentationCategory` encoding of Stacks 0D3J, which is the encoding carrying both
the hull clause of this tag and the tangent identification of Stacks 0DVT. The functor of
isomorphism classes is therefore literally the one the hull clause speaks of.

The hypothesis `H⁰(Γ, End_k(V)) = k` is expressed by saying that every `Γ`-equivariant
endomorphism of `V` is a scalar multiple of the identity for a unique scalar. The scalar
description of the equivariant endomorphisms of a deformation is descent from the special fibre,
`Deformation.Examples.FiniteProjectiveRepresentation.exists_scalar_of_residual_scalar`, which
is shared with the continuous case of Stacks 0ET2.

Prorepresentability is stated in the universe-raised form
`Deformation.IsProrepresentableULift`. The values of the functor of isomorphism classes lie in
the universe of the objects of the deformation category, not in the morphism universe of `𝒞_Λ`,
and `Deformation.IsProrepresentable` cannot be stated for such a functor; the two notions agree
whenever both are defined.

Stacks 0DVT gives finite dimensionality of the tangent space of the deformation category,
whereas Schlessinger's theorem asks for that of the category of elements of `F`. The canonical
morphism to the isomorphism classes is essentially surjective on every fibre, so its differential
is a surjection of tangent spaces and
`Deformation.finiteDimensional_artinianTangentSpace_of_essSurj` transports the bound; the two
models of the tangent space, with rank-one module `k` and `ULift k`, are compared by
`Deformation.finiteDimensional_tangentSpaceArtinian_of_artinianTangentSpace`.

## References

* [Stacks Project, Tag 0ET1](https://stacks.math.columbia.edu/tag/0ET1)
* [Stacks Project, Tag 0DVT](https://stacks.math.columbia.edu/tag/0DVT)
* [Stacks Project, Tag 06J8](https://stacks.math.columbia.edu/tag/06J8)
* [Stacks Project, Tag 06JM](https://stacks.math.columbia.edu/tag/06JM)
-/

@[expose] public noncomputable section

open CategoryTheory Representation

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] HasExt.standard

attribute [local instance] ModuleCat.moduleOfAlgebraModule
  ModuleCat.isScalarTower_of_algebra_moduleCat

universe u w g m

namespace Deformation

variable {Λ : Type u} {k : Type w} {Γ : Type g} [CommRing Λ] [Field k] [Algebra Λ k] [Group Γ]

/-- The equivariant endomorphisms of a deformation of `ρ₀` are the scalars, as soon as the
equivariant endomorphisms of `ρ₀` are, and a scalar whose endomorphism preserves the reduction
to `ρ₀` reduces to `1`. -/
private lemma scalar_of_representationDeformation {V : Type m} [AddCommGroup V] [Module k V]
    [Module.Finite k V] (ρ₀ : Representation k Γ V)
    (hscalar : ∀ linear : IntertwiningMap ρ₀ ρ₀,
      ∃! scalar : k, (scalar • LinearMap.id : Module.End k V) = linear.toLinearMap)
    (deformation : RepresentationCategory.deformationCategory (Λ := Λ) V ρ₀)
    (linear : IntertwiningMap deformation.left.action deformation.left.action) :
    ∃ scalar : deformation.left.base,
      (scalar • LinearMap.id : Module.End deformation.left.base
        deformation.left.carrier) = linear.toLinearMap ∧
      ((∀ vector, deformation.hom.map (linear.toLinearMap vector) = deformation.hom.map vector) →
        deformation.hom.base.hom scalar = 1) := by
  let ringMap : deformation.left.base →ₐ[Λ] k := deformation.hom.base.hom
  let : Algebra deformation.left.base k := ringMap.toAlgebra
  let : Module deformation.left.base V := Module.compHom V ringMap.toRingHom
  let : IsScalarTower deformation.left.base k V :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  let reduction : deformation.left.carrier →+ V := deformation.hom.map
  have hsmul : ∀ (coefficient : deformation.left.base) (vector : deformation.left.carrier),
      reduction (coefficient • vector) = ringMap coefficient • reduction vector :=
    deformation.hom.map_smul
  have hequivariant : ∀ (group : Γ) (vector : deformation.left.carrier),
      reduction (deformation.left.action group vector) = ρ₀ group (reduction vector) :=
    deformation.hom.equivariant
  let specialization := restrictAddHom ringMap.toRingHom reduction hsmul
  have hbase : IsBaseChange k specialization := deformation.hom.isBaseChange
  have hring : ∀ scalar, ringMap scalar = deformation.left.base.residueEquiv
      (IsLocalRing.residue deformation.left.base scalar) := by
    intro scalar
    have h := deformation.hom.base.residue_comm scalar
    change (Examples.residueFieldBase Λ k).residueEquiv
      (IsLocalRing.residue k (ringMap scalar)) = _ at h
    rwa [Examples.residueFieldBase_residueEquiv_residue] at h
  let residueEquiv : IsLocalRing.ResidueField deformation.left.base ≃ₗ[
      deformation.left.base] k :=
    { deformation.left.base.residueEquiv.toRingEquiv.toAddEquiv with
      map_smul' := by
        intro scalar value
        change deformation.left.base.residueEquiv
          (IsLocalRing.residue deformation.left.base scalar * value) =
          ringMap scalar * deformation.left.base.residueEquiv value
        rw [map_mul, hring] }
  let : Module.Free deformation.left.base deformation.left.carrier :=
    Module.free_of_flat_of_isLocalRing
  obtain ⟨scalar, hmap⟩ :=
    Deformation.Examples.FiniteProjectiveRepresentation.exists_scalar_of_residual_scalar
      residueEquiv deformation.left.action ρ₀ specialization hbase hequivariant hscalar linear
  refine ⟨scalar, hmap, fun hw => ?_⟩
  have heq : (ringMap scalar • LinearMap.id : Module.End k V) = LinearMap.id := by
    apply hbase.algHom_ext
    intro vector
    have h : reduction (scalar • vector) = reduction vector :=
      (congrArg reduction (LinearMap.congr_fun hmap vector)).trans (hw vector)
    rwa [hsmul] at h
  obtain ⟨_, _, hunique⟩ := hscalar (IntertwiningMap.id ρ₀)
  exact (hunique (ringMap scalar) heq).trans (hunique 1 (by simp)).symm

/-- An endomorphism of a deformation of `ρ₀` lying over the identity of the coefficient algebra
is multiplication by a scalar, and that scalar reduces to `1`. -/
private lemma scalar_of_vertical_representationDeformationHom {V : Type m} [AddCommGroup V]
    [Module k V] [Module.Finite k V] (ρ₀ : Representation k Γ V)
    (hscalar : ∀ linear : IntertwiningMap ρ₀ ρ₀,
      ∃! scalar : k, (scalar • LinearMap.id : Module.End k V) = linear.toLinearMap)
    (deformation : RepresentationCategory.deformationCategory (Λ := Λ) V ρ₀)
    (endomorphism : deformation ⟶ deformation)
    (hbase : endomorphism.left.base = 𝟙 _) :
    ∃ scalar : deformation.left.base,
      (∀ vector, endomorphism.left.map vector = scalar • vector) ∧
      deformation.hom.base.hom scalar = 1 := by
  let linear : IntertwiningMap deformation.left.action deformation.left.action :=
    { toAddHom := endomorphism.left.map
      map_smul' := by
        intro coefficient vector
        simpa [hbase] using endomorphism.left.map_smul coefficient vector
      isIntertwining' := by
        intro group
        ext vector
        exact endomorphism.left.equivariant group vector }
  obtain ⟨scalar, hscalarMap, hresidue⟩ :=
    scalar_of_representationDeformation ρ₀ hscalar deformation linear
  refine ⟨scalar, fun vector => (LinearMap.congr_fun hscalarMap vector).symm,
    hresidue fun vector => ?_⟩
  exact congrArg (fun morphism => morphism.map vector) endomorphism.w

/-- Multiplication by a unit of the coefficient algebra reducing to `1` is an endomorphism of a
deformation of `ρ₀`. -/
private def scalarRepresentationDeformationHom {V : Type m} [AddCommGroup V] [Module k V]
    [Module.Finite k V] (ρ₀ : Representation k Γ V)
    (deformation : RepresentationCategory.deformationCategory (Λ := Λ) V ρ₀)
    (scalar : deformation.left.baseˣ)
    (hscalar : deformation.hom.base.hom scalar = 1) :
    deformation ⟶ deformation := by
  let linear : deformation.left ⟶ deformation.left :=
    { base := 𝟙 _
      map := (LinearEquiv.smulOfUnit scalar).toLinearMap.toAddMonoidHom
      map_smul := fun _ _ => smul_comm _ _ _
      equivariant := fun _ _ => (map_smul _ _ _).symm
      isBaseChange := IsBaseChange.ofEquiv (LinearEquiv.smulOfUnit scalar) }
  refine Over.homMk linear ?_
  apply RepresentationCategory.Hom.ext
  · change (𝟙 _ ≫ deformation.hom.base) = deformation.hom.base
    simp
  · ext vector
    change deformation.hom.map ((scalar : deformation.left.base) • vector) = _
    rw [deformation.hom.map_smul, hscalar, one_smul]

/-- A morphism of deformations of `ρ₀` lying over a surjection of coefficient algebras is
surjective on coefficient algebras. -/
private lemma surjective_left_base_hom_of_isHomLift {V : Type m} [AddCommGroup V] [Module k V]
    [Module.Finite k V] (ρ₀ : Representation k Γ V)
    {source target : ArtinianLocalAlgCat.{u, w, w} Λ k} {ringMap : source ⟶ target}
    (hsurjective : Function.Surjective ringMap.hom)
    {first second : RepresentationCategory.deformationCategory (Λ := Λ) V ρ₀}
    (arrow : first ⟶ second)
    (harrow : (deformationCategoryProjection (Λ := Λ) V ρ₀).IsHomLift ringMap arrow) :
    Function.Surjective arrow.left.base.hom := by
  obtain ⟨⟩ := harrow
  exact hsurjective

/-- An endomorphism of a deformation of `ρ₀` mapping to the identity of its coefficient algebra
is an isomorphism. -/
private lemma isIso_of_deformationCategoryProjection_map_eq_id {V : Type m} [AddCommGroup V]
    [Module k V] [Module.Finite k V] (ρ₀ : Representation k Γ V)
    {deformation : RepresentationCategory.deformationCategory (Λ := Λ) V ρ₀}
    (f : deformation ⟶ deformation)
    (hf : (deformationCategoryProjection (Λ := Λ) V ρ₀).map f = 𝟙 _) : IsIso f := by
  set p := deformationCategoryProjection (Λ := Λ) V ρ₀
  let A := Opposite.op (p.obj deformation)
  let : p.op.IsHomLift (𝟙 A) f.op := by
    apply IsHomLift.of_fac p.op (𝟙 A) f.op rfl rfl
    simp [hf]
  let := (isDeformationCategory_deformationCategoryProjection (Λ := Λ) V
    ρ₀).predeformation.cofibered.isStronglyCartesian_homLift (𝟙 A) f.op
  exact (isIso_op_iff f).mp (Functor.IsStronglyCartesian.isIso_of_base_isIso p.op (𝟙 A) f.op)

/-- **Automorphisms of deformations of `ρ₀` lift along every surjection**, as soon as the
equivariant endomorphisms of `ρ₀` are exactly the scalars: a vertical automorphism is
multiplication by a unit reducing to `1`, and such a unit lifts along a surjection.

This is the hypothesis the criterion of Stacks 06J8 asks for. -/
public theorem automorphismsLiftAlong_deformationCategoryProjection
    (V : Type m) [AddCommGroup V] [Module k V] [Module.Finite k V]
    (ρ₀ : Representation k Γ V)
    (h : ∀ f : IntertwiningMap ρ₀ ρ₀,
      ∃! a : k, (a • LinearMap.id : Module.End k V) = f.toLinearMap) :
    ∀ {source target : ArtinianLocalAlgCat.{u, w, w} Λ k} (ringMap : source ⟶ target),
      Function.Surjective ringMap.hom →
      AutomorphismsLiftAlong (deformationCategoryProjection (Λ := Λ) V ρ₀) ringMap := by
  classical
  set p := deformationCategoryProjection (Λ := Λ) V ρ₀
  intro source target ringMap hsurjective first second arrow harrow automorphism
  let := automorphism.hom.2
  have hvertical : automorphism.hom.1.left.base = 𝟙 _ := by
    have hv := IsHomLift.fac' p (𝟙 target) automorphism.hom.1
    change automorphism.hom.1.left.base =
      eqToHom second.2 ≫ 𝟙 target ≫ eqToHom second.2.symm at hv
    simp only [Category.id_comp, eqToHom_trans, eqToHom_refl] at hv
    exact hv
  obtain ⟨scalar, hmap, hresidue⟩ := scalar_of_vertical_representationDeformationHom
    ρ₀ h second.1 automorphism.hom.1 hvertical
  have hunit : IsUnit scalar := isUnit_of_map_unit second.1.hom.base.hom scalar
    (hresidue.symm ▸ isUnit_one)
  obtain ⟨liftedScalar, hlifted⟩ :=
    surjective_left_base_hom_of_isHomLift ρ₀ hsurjective arrow harrow scalar
  have hliftedUnit : IsUnit liftedScalar :=
    isUnit_of_map_unit arrow.left.base.hom liftedScalar (hlifted.symm ▸ hunit)
  have hliftedResidue : first.1.hom.base.hom liftedScalar = 1 := by
    have hw := congrArg (fun morphism => morphism.base.hom liftedScalar) arrow.w
    change second.1.hom.base.hom (arrow.left.base.hom liftedScalar) =
      first.1.hom.base.hom liftedScalar at hw
    rwa [hlifted, hresidue, eq_comm] at hw
  let liftedHom := scalarRepresentationDeformationHom ρ₀ first.1 hliftedUnit.unit hliftedResidue
  have hprojection : p.map liftedHom = 𝟙 _ := rfl
  let : p.IsHomLift (𝟙 source) liftedHom :=
    IsHomLift.of_fac p (𝟙 source) liftedHom first.2 first.2 (by simp [hprojection])
  let fiberHom : first ⟶ first := ⟨liftedHom, inferInstance⟩
  let : IsIso liftedHom :=
    isIso_of_deformationCategoryProjection_map_eq_id ρ₀ liftedHom hprojection
  let : p.IsHomLift (𝟙 source) (inv liftedHom) := by
    simpa using IsHomLift.inv p (𝟙 source) liftedHom
  let fiberInverse : first ⟶ first := ⟨inv liftedHom, inferInstance⟩
  refine ⟨⟨fiberHom, fiberInverse, Functor.Fiber.hom_ext (IsIso.hom_inv_id liftedHom),
    Functor.Fiber.hom_ext (IsIso.inv_hom_id liftedHom)⟩, ?_⟩
  apply Over.OverMorphism.ext
  apply RepresentationCategory.Hom.ext
  · change (𝟙 _ ≫ arrow.left.base) = arrow.left.base ≫ automorphism.hom.1.left.base
    simp [hvertical]
  · ext vector
    change arrow.left.map (liftedScalar • vector) =
      automorphism.hom.1.left.map (arrow.left.map vector)
    rw [arrow.left.map_smul, hlifted, hmap]

/-- **The functor of isomorphism classes of deformations of a representation is a deformation
functor**, as soon as the equivariant endomorphisms of the representation are exactly the
scalars.

The deformations themselves satisfy the Rim–Schlessinger condition unconditionally; passing to
isomorphism classes preserves it exactly when automorphisms lift along surjections, which is
the criterion of Stacks 06J8 and which the scalar hypothesis provides. -/
public theorem isDeformationFunctor_isomorphismClasses_representation
    (V : Type m) [AddCommGroup V] [Module k V] [Module.Finite k V]
    (ρ₀ : Representation k Γ V)
    (h : ∀ f : IntertwiningMap ρ₀ ρ₀,
      ∃! a : k, (a • LinearMap.id : Module.End k V) = f.toLinearMap) :
    IsDeformationFunctor (isomorphismClasses
      (BasedCategory.ofFunctor (deformationCategoryProjection (Λ := Λ) V ρ₀))
      (isDeformationCategory_deformationCategoryProjection
        (Λ := Λ) V ρ₀).predeformation.cofibered) := by
  let hD := isDeformationCategory_deformationCategoryProjection (Λ := Λ) V ρ₀
  exact ⟨isPredeformationFunctor_isomorphismClasses _ hD.predeformation,
    (associatedSatisfiesRS_iff_gluingClassesInjective _ hD.satisfiesRS).2
      ((gluingClassesInjective_iff_automorphismsLift _ hD.predeformation.cofibered).2
        (automorphismsLiftAlong_deformationCategoryProjection V ρ₀ h))⟩

/-- **Stacks 0ET1**, prorepresentability: the functor of isomorphism classes of deformations of a
finite-dimensional representation of a finitely generated group over a classical base is
prorepresentable, as soon as the `Γ`-equivariant endomorphisms of the representation are exactly
the scalars, that is `H⁰(Γ, End_k(V)) = k`.

Prorepresentability is stated in the universe-raised form `Deformation.IsProrepresentableULift`,
because the values of the functor of isomorphism classes lie in the universe of the objects of
the deformation category rather than in the morphism universe of `𝒞_Λ`. The functor is the one
whose hull is `Deformation.exists_hull_isomorphismClasses_representation`, the other clause of
this tag. -/
@[stacks 0ET1 "prorepresentability"]
public theorem isProrepresentableULift_isomorphismClasses_representation
    (V : Type m) [AddCommGroup V] [Module k V] [Module.Finite k V] [Group.FG Γ]
    (ρ₀ : Representation k Γ V) (hΛ : IsClassical Λ k)
    (h : ∀ f : IntertwiningMap ρ₀ ρ₀,
      ∃! a : k, (a • LinearMap.id : Module.End k V) = f.toLinearMap) :
    IsProrepresentableULift (isomorphismClasses
      (BasedCategory.ofFunctor (deformationCategoryProjection (Λ := Λ) V ρ₀))
      (isDeformationCategory_deformationCategoryProjection
        (Λ := Λ) V ρ₀).predeformation.cofibered) := by
  let : IsNoetherianRing Λ := hΛ.isNoetherianRing
  let : Module.Finite Λ k := hΛ.moduleFinite
  refine (isProrepresentableULift_iff_isDeformationFunctor _).2
    ⟨isDeformationFunctor_isomorphismClasses_representation V ρ₀ h, ?_, ?_⟩
  · let hD := isDeformationCategory_deformationCategoryProjection (Λ := Λ) V ρ₀
    let 𝓕 := BasedCategory.ofFunctor (deformationCategoryProjection (Λ := Λ) V ρ₀)
    let F := isomorphismClasses 𝓕 hD.predeformation.cofibered
    let 𝓖 := BasedCategory.ofFunctor (Functor.Elements.π F)
    let hDel := (isDeformationCategory_iff F).2
      (isDeformationFunctor_isomorphismClasses_representation V ρ₀ h)
    let hS2el := Artin.schlessingerConditionS2_isomorphismClasses_of_isDeformationCategory 𝓖 hDel
    let hS2 := Artin.schlessingerConditionS2_isomorphismClasses_of_isDeformationCategory 𝓕 hD
    exact finiteDimensional_tangentSpaceArtinian_of_artinianTangentSpace 𝓖
      hDel.predeformation hS2el
      (finiteDimensional_artinianTangentSpace_of_essSurj 𝓕 𝓖
        hD.predeformation hDel.predeformation hS2 hS2el
        (toIsomorphismClasses 𝓕 hD.predeformation.cofibered)
        (fun A => (isomorphismClassesData 𝓕
          hD.predeformation.cofibered).quotient.fiber_essSurj A)
        (finiteDimensional_tangentSpace_representation (Λ := Λ) V ρ₀))
  · intro first second _
    ext value
    obtain ⟨scalar, rfl⟩ := hΛ.surjective_algebraMap value
    simp

end Deformation

end
