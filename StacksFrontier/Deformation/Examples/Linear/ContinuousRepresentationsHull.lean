module

public import Mathlib.RepresentationTheory.Intertwining
public import Mathlib.RingTheory.TensorProduct.IsBaseChangeHom
public import Mathlib.RingTheory.TensorProduct.IsBaseChangePi
public import StacksFrontier.Deformation.Artin.Basic
public import StacksFrontier.Deformation.ClassicalCase
public import StacksFrontier.Deformation.Cofibered.Over
public import StacksFrontier.Deformation.Examples.Linear.ContinuousRepresentationsInfinitesimalAutomorphisms
public import StacksFrontier.Deformation.Examples.Linear.ContinuousRepresentationsRimSchlessinger
public import StacksFrontier.Deformation.Formal.VersalObject.IsomorphismClassesHull
public import StacksFrontier.Deformation.InfinitesimalAutomorphism.Tangent
public import StacksFrontier.Deformation.Predeformation.Associated
public import StacksFrontier.Deformation.Predeformation.Basic
public import StacksFrontier.Deformation.RimSchlessingerCategory.AutomorphismLifting
public import StacksFrontier.Deformation.Schlessinger.AssociatedFunctor
public import StacksFrontier.Deformation.Schlessinger.Prorepresentable
public import StacksFrontier.Deformation.Smooth.IsomorphismClasses
public import StacksFrontier.Deformation.Smooth.Versal
public import StacksFrontier.Deformation.TangentSpace.BijectiveDifferential
public import StacksFrontier.Deformation.TangentSpace.LiftedComparison

/-!
# Hulls and prorepresentability for deformations of a continuous representation

Let `Λ → k` be a classical base, `Γ` a topological group and `ρ₀` a finite-dimensional
continuous representation of `Γ` on a `k`-vector space `V`. The deformations of `ρ₀` form a
deformation category — Stacks 0DVV — and this file passes from that category to its functor of
fibrewise isomorphism classes.

When the `Γ`-equivariant endomorphisms of `V` are exactly the scalars, that is when
`H⁰(Γ, End_k(V)) = k`, that functor is itself a deformation functor. By Stacks 06J8 this
amounts to lifting automorphisms along surjections of coefficient algebras, and the scalar
hypothesis supplies the lift: an automorphism of a deformation lying over the identity is
multiplication by a unit of the coefficient algebra whose residue is `1`, and such a unit
lifts along a surjection. When `Γ` is in addition topologically finitely generated the tangent
space of the functor is finite dimensional, so the functor has a hull, and under the scalar
hypothesis it is prorepresentable. These are the two conclusions of Stacks 0ET2.

Topological finite generation of `Γ` is taken in the form of a dense finitely generated
subgroup. It feeds the hull theorem of Stacks 06IZ through the tangent clause of Stacks 0DVW,
`finiteDimensional_continuousTangentSpace`.

## Main results

All in the namespace `Deformation.Examples.FiniteProjectiveRepresentation`.

* `automorphismsLiftAlong_continuousDeformationCategory`: automorphisms of deformations of `ρ₀`
  lift along every surjection of coefficient algebras.
* `isDeformationFunctor_continuousIsomorphismClasses`: the functor of isomorphism classes is a
  deformation functor.
* `schlessingerConditionS2_continuousIsomorphismClasses`: Schlessinger's condition (S2) for
  that functor.
* `exists_hull_continuousIsomorphismClasses`: **Stacks 0ET2**, the hull — it has a versal
  formal object with bijective differential.
* `isProrepresentableULift_continuousIsomorphismClasses`: **Stacks 0ET2**, prorepresentability.

## Implementation notes

The hypothesis `H⁰(Γ, End_k(V)) = k` is expressed by saying that every `Γ`-equivariant
endomorphism of `V` is a scalar multiple of the identity for a unique scalar; for a nonzero
`V` that is exactly bijectivity of the scalar map onto the invariants of the conjugation
representation, which is the `H⁰` computed by Stacks 0DVW.

The scalar description of the equivariant endomorphisms of a deformation `M` over `A` is
descent from the special fibre, `scalar_of_residual_scalar`. Continuity plays no
part in that step, so it is stated for a bare base change of representations and shared with
the discrete case.

Prorepresentability is stated in the universe-raised form
`Deformation.IsProrepresentableULift`. The values of the functor of isomorphism classes lie in
the universe of the objects of the deformation category, not in the morphism universe of
`𝒞_Λ`, and `Deformation.IsProrepresentable` cannot be stated for such a functor; the two
notions agree whenever both are defined.

Stacks 0DVW gives finite-dimensionality in the `Deformation.artinianTangentSpace` model, whose
rank-one module is `k`, whereas Stacks 06IZ asks for the `Deformation.tangentSpaceArtinian`
model, whose rank-one module is `ULift k`;
`Deformation.finiteDimensional_tangentSpaceArtinian_of_artinianTangentSpace` compares the two.
Prorepresentability needs the tangent space of the category of elements of the functor rather
than of the deformation category itself; the canonical morphism to the isomorphism classes is
essentially surjective on every fibre, so its differential is a surjection of tangent spaces
and `Deformation.finiteDimensional_artinianTangentSpace_of_essSurj` transports the bound.

## References

* [Stacks Project, Tag 0ET2](https://stacks.math.columbia.edu/tag/0ET2)
* [Stacks Project, Tag 0DVV](https://stacks.math.columbia.edu/tag/0DVV)
* [Stacks Project, Tag 0DVW](https://stacks.math.columbia.edu/tag/0DVW)
* [Stacks Project, Tag 06J8](https://stacks.math.columbia.edu/tag/06J8)
* [Stacks Project, Tag 06JM](https://stacks.math.columbia.edu/tag/06JM)
-/

@[expose] public noncomputable section

open CategoryTheory Representation

namespace Deformation.Examples.FiniteProjectiveRepresentation

universe u w m

/-- A map of finite modules over a local ring, with the target free, is injective as soon as
its reduction along a presentation of the residue field is. -/
private lemma injective_of_residue_baseChange
    {R K M N : Type*} [CommRing R] [Field K] [Algebra R K]
    [IsLocalRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N]
    [Module.Finite R M] [Module.Finite R N] [Module.Free R N]
    (residueEquiv : IsLocalRing.ResidueField R ≃ₗ[R] K)
    (linear : M →ₗ[R] N) (hinj : Function.Injective (linear.lTensor K)) :
    Function.Injective linear := by
  have hres : Function.Injective (linear.lTensor (IsLocalRing.ResidueField R)) := by
    intro first second heq
    apply (TensorProduct.congr residueEquiv (LinearEquiv.refl R M)).injective
    apply hinj
    have hcomm :
        (linear.lTensor K).restrictScalars R ∘ₗ
          (TensorProduct.congr residueEquiv (LinearEquiv.refl R M)).toLinearMap =
        (TensorProduct.congr residueEquiv (LinearEquiv.refl R N)).toLinearMap ∘ₗ
          (linear.lTensor (IsLocalRing.ResidueField R)).restrictScalars R := by
      ext scalar vector
      rfl
    calc
      (linear.lTensor K)
          (TensorProduct.congr residueEquiv (LinearEquiv.refl R M) first) =
          TensorProduct.congr residueEquiv (LinearEquiv.refl R N)
            ((linear.lTensor (IsLocalRing.ResidueField R)) first) :=
        LinearMap.congr_fun hcomm first
      _ = TensorProduct.congr residueEquiv (LinearEquiv.refl R N)
            ((linear.lTensor (IsLocalRing.ResidueField R)) second) := congrArg _ heq
      _ = (linear.lTensor K)
          (TensorProduct.congr residueEquiv (LinearEquiv.refl R M) second) :=
        (LinearMap.congr_fun hcomm second).symm
  obtain ⟨leftInverse, hleft⟩ :=
    (IsLocalRing.split_injective_iff_lTensor_residueField_injective linear).2 hres
  exact Function.HasLeftInverse.injective ⟨leftInverse, LinearMap.congr_fun hleft⟩

/-- A map of finite modules over a local ring, with the target free, is injective as soon as
the induced map of their base changes to the residue field is. -/
private lemma injective_of_baseChange
    {R K M N P Q : Type*} [CommRing R] [Field K] [Algebra R K]
    [IsLocalRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] [AddCommGroup P] [Module R P]
    [Module K P] [IsScalarTower R K P] [AddCommGroup Q] [Module R Q]
    [Module K Q] [IsScalarTower R K Q]
    [Module.Finite R M] [Module.Finite R N] [Module.Free R N]
    (residueEquiv : IsLocalRing.ResidueField R ≃ₗ[R] K)
    {first : M →ₗ[R] P} {second : N →ₗ[R] Q}
    (hfirst : IsBaseChange K first) (hsecond : IsBaseChange K second)
    (linear : M →ₗ[R] N) (reduced : P →ₗ[K] Q)
    (commutes : reduced.restrictScalars R ∘ₗ first = second ∘ₗ linear)
    (hinj : Function.Injective reduced) : Function.Injective linear := by
  apply injective_of_residue_baseChange residueEquiv linear
  have comparison : reduced.restrictScalars R ∘ₗ hfirst.equiv.toLinearMap.restrictScalars R =
      hsecond.equiv.toLinearMap.restrictScalars R ∘ₗ linear.lTensor K := by
    ext scalar vector
    simpa using congrArg (fun value => scalar • value)
      (LinearMap.congr_fun commutes vector)
  exact fun firstVector secondVector heq => hfirst.equiv.injective <| hinj <|
    (LinearMap.congr_fun comparison firstVector).trans
      ((congrArg hsecond.equiv heq).trans (LinearMap.congr_fun comparison secondVector).symm)

/-- The coefficient of an endomorphism of a free module at one diagonal entry. -/
private def diagonalCoordinate
    {R M ι : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (basis : Module.Basis ι R M) (index : ι) : Module.End R M →ₗ[R] R where
  toFun linear := basis.repr (linear (basis index)) index
  map_add' first second := by simp
  map_smul' scalar linear := by simp

/-- The commutator against a fixed endomorphism, as a linear map in the other argument. -/
private def commutator
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (action : Module.End R M) : Module.End R M →ₗ[R] Module.End R M where
  toFun linear := linear ∘ₗ action - action ∘ₗ linear
  map_add' first second := by
    simp [LinearMap.add_comp, LinearMap.comp_add, add_sub_add_comm]
  map_smul' scalar linear := by
    simp [LinearMap.smul_comp, LinearMap.comp_smul, smul_sub]

/-- If the equivariant endomorphisms of the residual representation are exactly the scalars,
then so are the equivariant endomorphisms of a free deformation of it over a local ring. -/
private lemma scalar_of_residual_scalar
    {R K Γ M V : Type*} [CommRing R] [IsLocalRing R] [Field K] [Algebra R K]
    [Group Γ] [AddCommGroup M] [Module R M] [Module.Finite R M]
    [Module.Free R M] [AddCommGroup V] [Module R V] [Module K V]
    [IsScalarTower R K V] [Module.Finite K V]
    (residueEquiv : IsLocalRing.ResidueField R ≃ₗ[R] K)
    (action : Representation R Γ M) (residual : Representation K Γ V)
    (specialization : M →ₗ[R] V) (hbase : IsBaseChange K specialization)
    (hequiv : ∀ group vector,
      specialization (action group vector) = residual group (specialization vector))
    (hscalar : ∀ linear : IntertwiningMap residual residual,
      ∃! scalar : K, (scalar • LinearMap.id : Module.End K V) = linear.toLinearMap)
    (linear : IntertwiningMap action action) :
    ∃ scalar : R, (scalar • LinearMap.id : Module.End R M) = linear.toLinearMap := by
  classical
  have hid : (LinearMap.id : Module.End K V) ≠ 0 := by
    intro hid
    obtain ⟨scalar, hscalar, hunique⟩ := hscalar 0
    have hzero : (0 : K) = scalar := hunique 0 (by simp)
    have hone : (1 : K) = scalar := hunique 1 (by simp [hid])
    exact one_ne_zero (hone.trans hzero.symm)
  have : Nontrivial V := by
    by_contra htrivial
    have : Subsingleton V := not_nontrivial_iff_subsingleton.mp htrivial
    exact hid (Subsingleton.elim _ _)
  let basis := Module.Free.chooseBasis R M
  let residualBasis := hbase.basis basis
  obtain ⟨index⟩ := residualBasis.index_nonempty
  let coordinate := diagonalCoordinate basis index
  let residualCoordinate := diagonalCoordinate residualBasis index
  let reducedEnd := hbase.endHom
  have hEnd : IsBaseChange K reducedEnd := hbase.end
  have hcoordinate : ∀ endomorphism,
      residualCoordinate (reducedEnd endomorphism) =
        algebraMap R K (coordinate endomorphism) := by
    intro endomorphism
    show residualBasis.repr (hbase.endHom endomorphism (residualBasis index)) index = _
    simp only [coordinate, diagonalCoordinate, residualBasis,
      IsBaseChange.basis_apply, IsBaseChange.endHom_comp_apply,
      IsBaseChange.basis_repr_comp_apply]
    rfl
  have hcommutes : ∀ group endomorphism,
      commutator (residual group) (reducedEnd endomorphism) =
        reducedEnd (commutator (action group) endomorphism) := by
    intro group endomorphism
    apply hbase.algHom_ext
    intro vector
    show (hbase.endHom endomorphism) (residual group (specialization vector)) -
      residual group ((hbase.endHom endomorphism) (specialization vector)) =
        (hbase.endHom (endomorphism ∘ₗ action group - action group ∘ₗ endomorphism))
          (specialization vector)
    simp only [LinearMap.sub_apply,
      LinearMap.comp_apply, ← hequiv, IsBaseChange.endHom_comp_apply, map_sub]
  obtain ⟨indices, hindices⟩ := Finset.exists_inf_le
    (fun group : Γ => LinearMap.ker (commutator (residual group)))
  let detection : Module.End R M →ₗ[R] R × (indices → Module.End R M) :=
    coordinate.prod (LinearMap.pi fun group => commutator (action group))
  let residualDetection : Module.End K V →ₗ[K] K × (indices → Module.End K V) :=
    residualCoordinate.prod (LinearMap.pi fun group => commutator (residual group))
  have hinj : Function.Injective residualDetection := by
    refine (injective_iff_map_eq_zero residualDetection).2 fun endomorphism hzero => ?_
    have hcoordinateZero : residualCoordinate endomorphism = 0 :=
      congrArg Prod.fst hzero
    have hconstraints : ∀ group, commutator (residual group) endomorphism = 0 := fun group =>
      hindices group (Submodule.mem_finsetInf.mpr fun other hother => LinearMap.mem_ker.mpr
        (congrArg (fun value => value.2 ⟨other, hother⟩) hzero))
    let intertwiner : IntertwiningMap residual residual :=
      ⟨endomorphism, fun group => sub_eq_zero.mp (hconstraints group)⟩
    obtain ⟨scalar, hscalar, _⟩ := hscalar intertwiner
    have hscalarZero : scalar = 0 := by
      simpa [diagonalCoordinate, residualCoordinate] using
        (congrArg residualCoordinate hscalar).trans hcoordinateZero
    simpa [hscalarZero] using hscalar.symm
  let targetSpecialization := (Algebra.linearMap R K).prodMap
    (reducedEnd.compLeft indices)
  have htarget : IsBaseChange K targetSpecialization :=
    (IsBaseChange.linearMap R K).prodMap _ _ (hEnd.finitePow indices)
  have hcomparison : residualDetection.restrictScalars R ∘ₗ reducedEnd =
      targetSpecialization ∘ₗ detection :=
    LinearMap.ext fun endomorphism =>
      Prod.ext (hcoordinate endomorphism) (funext fun group => hcommutes group endomorphism)
  refine ⟨coordinate linear.toLinearMap, injective_of_baseChange residueEquiv hEnd htarget
    detection residualDetection hcomparison hinj ?_⟩
  apply Prod.ext
  · simp [detection, coordinate, diagonalCoordinate]
  · funext group
    simp [detection, commutator, linear.isIntertwining']

/-- **The equivariant endomorphisms of a free deformation over a local ring are the scalars**, as
soon as the equivariant endomorphisms of the residual representation are. This is the public form
of `Deformation.Examples.FiniteProjectiveRepresentation.scalar_of_residual_scalar`; continuity
plays no part in it, so it is also what the discrete case of
[Stacks Project, Tag 0ET1] uses, in
`StacksFrontier.Deformation.Representation.Prorepresentable`. -/
public alias exists_scalar_of_residual_scalar := scalar_of_residual_scalar

variable {Λ : Type u} {k : Type w} {Γ : Type*}
  [CommRing Λ] [Field k] [Algebra Λ k] [Group Γ] [TopologicalSpace Γ]

/-- The equivariant endomorphisms of a deformation of `ρ₀` are the scalars, as soon as the
equivariant endomorphisms of `ρ₀` are, and a scalar acting trivially on the special fibre
reduces to `1`. -/
private lemma scalar_of_deformation {V : Type m} [AddCommGroup V] [Module k V]
    [Module.Finite k V] (residual : Representation k Γ V)
    (hcontinuous : IsContinuousRepresentation residual)
    (hscalar : ∀ linear : IntertwiningMap residual residual,
      ∃! scalar : k, (scalar • LinearMap.id : Module.End k V) = linear.toLinearMap)
    (deformation : Over (continuousSpecialFiber (Λ := Λ) V residual hcontinuous))
    (linear : IntertwiningMap deformation.left.obj.action deformation.left.obj.action) :
    ∃ scalar : deformation.left.obj.base,
      (scalar • LinearMap.id : Module.End deformation.left.obj.base
        deformation.left.obj.carrier) = linear.toLinearMap ∧
      ((∀ vector, deformation.hom.hom.map (linear vector) = deformation.hom.hom.map vector) →
        deformation.hom.hom.base.hom scalar = 1) := by
  dsimp only [continuousSpecialFiber, specialFiber] at deformation
  let ringMap : deformation.left.obj.base →ₐ[Λ] k := deformation.hom.hom.base.hom
  let : Algebra deformation.left.obj.base k := ringMap.toAlgebra
  let : Module deformation.left.obj.base V := Module.compHom V ringMap.toRingHom
  let : IsScalarTower deformation.left.obj.base k V :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  let specialization := restrictAddHom ringMap.toRingHom deformation.hom.hom.map
    deformation.hom.hom.map_smul
  have hbase : IsBaseChange k specialization := deformation.hom.hom.isBaseChange
  have hring : ∀ scalar, ringMap scalar = deformation.left.obj.base.residueEquiv
      (IsLocalRing.residue deformation.left.obj.base scalar) := by
    intro scalar
    have h := deformation.hom.hom.base.residue_comm scalar
    change (residueFieldBase Λ k).residueEquiv
      (IsLocalRing.residue k (ringMap scalar)) = _ at h
    rwa [residueFieldBase_residueEquiv_residue] at h
  let residueEquiv : IsLocalRing.ResidueField deformation.left.obj.base ≃ₗ[
      deformation.left.obj.base] k :=
    { deformation.left.obj.base.residueEquiv.toRingEquiv.toAddEquiv with
      map_smul' := by
        intro scalar value
        show deformation.left.obj.base.residueEquiv
          (IsLocalRing.residue deformation.left.obj.base scalar * value) =
          ringMap scalar * deformation.left.obj.base.residueEquiv value
        rw [map_mul, hring] }
  let : Module.Free deformation.left.obj.base deformation.left.obj.carrier :=
    Module.free_of_flat_of_isLocalRing
  obtain ⟨scalar, hscalarMap⟩ := scalar_of_residual_scalar residueEquiv
    deformation.left.obj.action residual specialization hbase
    deformation.hom.hom.equivariant hscalar linear
  refine ⟨scalar, hscalarMap, fun hw => ?_⟩
  have heq : (ringMap scalar • LinearMap.id : Module.End k V) = LinearMap.id := by
    apply hbase.algHom_ext
    intro vector
    have hmap : linear vector = scalar • vector :=
      (LinearMap.congr_fun hscalarMap vector).symm
    have hw := hw vector
    change deformation.hom.hom.map (linear vector) = deformation.hom.hom.map vector at hw
    rwa [hmap, deformation.hom.hom.map_smul] at hw
  obtain ⟨_, _, hunique⟩ := hscalar (IntertwiningMap.id residual)
  exact (hunique (ringMap scalar) heq).trans (hunique 1 (by simp)).symm

/-- An endomorphism of a deformation of `ρ₀` lying over the identity of the coefficient
algebra is multiplication by a scalar, and that scalar reduces to `1`. -/
private lemma scalar_of_vertical_deformationHom {V : Type m} [AddCommGroup V] [Module k V]
    [Module.Finite k V] (residual : Representation k Γ V)
    (hcontinuous : IsContinuousRepresentation residual)
    (hscalar : ∀ linear : IntertwiningMap residual residual,
      ∃! scalar : k, (scalar • LinearMap.id : Module.End k V) = linear.toLinearMap)
    (deformation : Over (continuousSpecialFiber (Λ := Λ) V residual hcontinuous))
    (endomorphism : deformation ⟶ deformation)
    (hbase : endomorphism.left.hom.base = 𝟙 _) :
    ∃ scalar : deformation.left.obj.base,
      (∀ vector, endomorphism.left.hom.map vector = scalar • vector) ∧
      deformation.hom.hom.base.hom scalar = 1 := by
  let linear : IntertwiningMap deformation.left.obj.action deformation.left.obj.action :=
    { toAddHom := endomorphism.left.hom.map
      map_smul' := by
        intro coefficient vector
        simpa [hbase] using endomorphism.left.hom.map_smul coefficient vector
      isIntertwining' := by
        intro group
        ext vector
        exact endomorphism.left.hom.equivariant group vector }
  obtain ⟨scalar, hscalarMap, hresidue⟩ :=
    scalar_of_deformation residual hcontinuous hscalar deformation linear
  refine ⟨scalar, fun vector => (LinearMap.congr_fun hscalarMap vector).symm, hresidue
    fun vector => congrArg (fun morphism => morphism.hom.map vector) endomorphism.w⟩

/-- Multiplication by a unit of the coefficient algebra reducing to `1` is an endomorphism of
a deformation of `ρ₀`. -/
private def scalarDeformationHom {V : Type m} [AddCommGroup V] [Module k V]
    [Module.Finite k V] (residual : Representation k Γ V)
    (hcontinuous : IsContinuousRepresentation residual)
    (deformation : Over (continuousSpecialFiber (Λ := Λ) V residual hcontinuous))
    (scalar : deformation.left.obj.baseˣ)
    (hscalar : deformation.hom.hom.base.hom scalar = 1) :
    deformation ⟶ deformation := by
  let linear : deformation.left.obj ⟶ deformation.left.obj :=
    { base := 𝟙 _
      map := (LinearEquiv.smulOfUnit scalar).toLinearMap.toAddMonoidHom
      map_smul := fun _ _ => smul_comm _ _ _
      equivariant := fun _ _ => (map_smul _ _ _).symm
      isBaseChange := IsBaseChange.ofEquiv (LinearEquiv.smulOfUnit scalar) }
  refine Over.homMk (ObjectProperty.homMk linear) ?_
  apply ObjectProperty.hom_ext
  apply Hom.ext
  · change (𝟙 _ ≫ deformation.hom.hom.base) = deformation.hom.hom.base
    simp
  · ext vector
    change deformation.hom.hom.map ((scalar : deformation.left.obj.base) • vector) = _
    rw [deformation.hom.hom.map_smul, hscalar, one_smul]

/-- Multiplication by a unit reducing to `1` is an automorphism of a deformation of `ρ₀`. -/
private lemma isIso_scalarDeformationHom
    (V : Type m) [AddCommGroup V] [Module k V] [Module.Finite k V]
    (ρ₀ : Representation k Γ V) (hρ₀ : IsContinuousRepresentation ρ₀)
    (deformation : Over (continuousSpecialFiber (Λ := Λ) V ρ₀ hρ₀))
    (scalar : deformation.left.obj.baseˣ)
    (hscalar : deformation.hom.hom.base.hom scalar = 1) :
    IsIso (scalarDeformationHom ρ₀ hρ₀ deformation scalar hscalar) := by
  set p := objectsOverFunctor
    (continuousProjection.{u, w, w, m} (Λ := Λ) (k := k) (Γ := Γ))
    (continuousSpecialFiber (Λ := Λ) V ρ₀ hρ₀)
  let liftedHom := scalarDeformationHom ρ₀ hρ₀ deformation scalar hscalar
  have hprojection : p.map liftedHom = 𝟙 _ := rfl
  let base := 𝟙 (Opposite.op (p.obj deformation))
  let : p.op.IsHomLift base liftedHom.op :=
    IsHomLift.of_fac p.op base liftedHom.op rfl rfl (by simp [base, hprojection])
  let := (isDeformationCategory_continuousDeformationCategory
    (Λ := Λ) V ρ₀ hρ₀).predeformation.cofibered.isStronglyCartesian_homLift base liftedHom.op
  have : IsIso liftedHom.op :=
    Functor.IsStronglyCartesian.isIso_of_base_isIso p.op base liftedHom.op
  exact (isIso_op_iff liftedHom).mp this

/-- **Automorphisms of deformations of `ρ₀` lift along every surjection**, as soon as the
equivariant endomorphisms of `ρ₀` are exactly the scalars: a vertical automorphism is
multiplication by a unit reducing to `1`, and such a unit lifts along a surjection. -/
public theorem automorphismsLiftAlong_continuousDeformationCategory
    (V : Type m) [AddCommGroup V] [Module k V] [Module.Finite k V]
    (ρ₀ : Representation k Γ V) (hρ₀ : IsContinuousRepresentation ρ₀)
    (h : ∀ f : IntertwiningMap ρ₀ ρ₀,
      ∃! a : k, (a • LinearMap.id : Module.End k V) = f.toLinearMap) :
    ∀ {source target : ArtinianLocalAlgCat.{u, w, w} Λ k} (ringMap : source ⟶ target),
      Function.Surjective ringMap.hom →
      AutomorphismsLiftAlong (objectsOverFunctor
        (continuousProjection.{u, w, w, m} (Λ := Λ) (k := k) (Γ := Γ))
        (continuousSpecialFiber (Λ := Λ) V ρ₀ hρ₀)) ringMap := by
  classical
  set p := objectsOverFunctor
    (continuousProjection.{u, w, w, m} (Λ := Λ) (k := k) (Γ := Γ))
    (continuousSpecialFiber (Λ := Λ) V ρ₀ hρ₀)
  intro source target ringMap hsurjective first second arrow harrow automorphism
  let := harrow
  let := automorphism.hom.2
  have hvertical : automorphism.hom.1.left.hom.base = 𝟙 _ := by
    have hv := IsHomLift.fac' p (𝟙 target) automorphism.hom.1
    change automorphism.hom.1.left.hom.base =
      eqToHom second.2 ≫ 𝟙 target ≫ eqToHom second.2.symm at hv
    exact hv.trans (by
      rw [Category.id_comp]
      exact (eqToHom_trans _ _).trans (eqToHom_refl _ _))
  obtain ⟨scalar, hmap, hresidue⟩ := scalar_of_vertical_deformationHom
    ρ₀ hρ₀ h second.1 automorphism.hom.1 hvertical
  have hunit : IsUnit scalar := isUnit_of_map_unit second.1.hom.hom.base.hom scalar
    (hresidue.symm ▸ isUnit_one)
  have hsurj : Function.Surjective arrow.left.hom.base.hom :=
    surjective_map_of_lift p ringMap arrow hsurjective
  obtain ⟨liftedScalar, hlifted⟩ := hsurj scalar
  have hliftedUnit : IsUnit liftedScalar :=
    isUnit_of_map_unit arrow.left.hom.base.hom liftedScalar (hlifted.symm ▸ hunit)
  have hliftedResidue : first.1.hom.hom.base.hom liftedScalar = 1 := by
    have hw := congrArg (fun morphism => morphism.hom.base.hom liftedScalar) arrow.w
    change second.1.hom.hom.base.hom (arrow.left.hom.base.hom liftedScalar) =
      first.1.hom.hom.base.hom liftedScalar at hw
    rw [hlifted, hresidue] at hw
    exact hw.symm
  let liftedHom := scalarDeformationHom ρ₀ hρ₀ first.1 hliftedUnit.unit hliftedResidue
  have hprojection : p.map liftedHom = 𝟙 _ := rfl
  let : p.IsHomLift (𝟙 source) liftedHom :=
    IsHomLift.of_fac p (𝟙 source) liftedHom first.2 first.2 (by simp [hprojection])
  let fiberHom : first ⟶ first := ⟨liftedHom, inferInstance⟩
  have : IsIso liftedHom :=
    isIso_scalarDeformationHom V ρ₀ hρ₀ first.1 hliftedUnit.unit hliftedResidue
  let : p.IsHomLift (𝟙 source) (inv liftedHom) := by
    simpa using IsHomLift.inv p (𝟙 source) liftedHom
  let fiberInverse : first ⟶ first := ⟨inv liftedHom, inferInstance⟩
  refine ⟨⟨fiberHom, fiberInverse, Functor.Fiber.hom_ext (IsIso.hom_inv_id liftedHom),
    Functor.Fiber.hom_ext (IsIso.inv_hom_id liftedHom)⟩, ?_⟩
  apply Over.OverMorphism.ext
  apply ObjectProperty.hom_ext
  apply Hom.ext
  · show (𝟙 _ ≫ arrow.left.hom.base) =
      arrow.left.hom.base ≫ automorphism.hom.1.left.hom.base
    simp [hvertical]
  · ext vector
    show arrow.left.hom.map (liftedScalar • vector) =
      automorphism.hom.1.left.hom.map (arrow.left.hom.map vector)
    rw [arrow.left.hom.map_smul, hlifted, hmap]

/-- **The functor of isomorphism classes of deformations of a continuous representation is a
deformation functor**, as soon as the equivariant endomorphisms of the representation are
exactly the scalars.

The deformations themselves satisfy the Rim–Schlessinger condition unconditionally; passing to
isomorphism classes preserves it exactly when automorphisms lift along surjections, which the
scalar hypothesis provides. -/
public theorem isDeformationFunctor_continuousIsomorphismClasses
    (V : Type m) [AddCommGroup V] [Module k V] [Module.Finite k V]
    (ρ₀ : Representation k Γ V) (hρ₀ : IsContinuousRepresentation ρ₀)
    (h : ∀ f : IntertwiningMap ρ₀ ρ₀,
      ∃! a : k, (a • LinearMap.id : Module.End k V) = f.toLinearMap) :
    IsDeformationFunctor (isomorphismClasses
      (BasedCategory.ofFunctor (objectsOverFunctor
        (continuousProjection.{u, w, w, m} (Λ := Λ) (k := k) (Γ := Γ))
        (continuousSpecialFiber (Λ := Λ) V ρ₀ hρ₀)))
      (isDeformationCategory_continuousDeformationCategory
        (Λ := Λ) V ρ₀ hρ₀).predeformation.cofibered) := by
  let hD := isDeformationCategory_continuousDeformationCategory (Λ := Λ) V ρ₀ hρ₀
  refine ⟨isPredeformationFunctor_isomorphismClasses _ hD.predeformation, ?_⟩
  exact (associatedSatisfiesRS_iff_gluingClassesInjective _ hD.satisfiesRS).2 <|
    (gluingClassesInjective_iff_automorphismsLift _ hD.predeformation.cofibered).2 <|
      automorphismsLiftAlong_continuousDeformationCategory V ρ₀ hρ₀ h

/-- Schlessinger's condition (S2) for the functor of isomorphism classes of deformations of a
finite-dimensional continuous representation. -/
public theorem schlessingerConditionS2_continuousIsomorphismClasses
    (V : Type m) [AddCommGroup V] [Module k V] [Module.Finite k V]
    (ρ₀ : Representation k Γ V) (hρ₀ : IsContinuousRepresentation ρ₀) :
    SchlessingerConditionS2 (CategoryOfElements.π (isomorphismClasses
      (BasedCategory.ofFunctor (objectsOverFunctor
        (continuousProjection.{u, w, w, m} (Λ := Λ) (k := k) (Γ := Γ))
        (continuousSpecialFiber (Λ := Λ) V ρ₀ hρ₀)))
      (isDeformationCategory_continuousDeformationCategory
        (Λ := Λ) V ρ₀ hρ₀).predeformation.cofibered)) :=
  schlessingerConditionS2_of_isIsomorphismClasses _
    (isDeformationCategory_continuousDeformationCategory
      (Λ := Λ) V ρ₀ hρ₀).predeformation.cofibered
    (schlessingerConditionS2_of_satisfiesRS
      (isDeformationCategory_continuousDeformationCategory (Λ := Λ) V ρ₀ hρ₀).satisfiesRS)
    (Or.inl (isDeformationCategory_continuousDeformationCategory
      (Λ := Λ) V ρ₀ hρ₀).predeformation)

/-- **Stacks 0ET2**, the hull: the functor of isomorphism classes of deformations of a
finite-dimensional continuous representation of a topologically finitely generated group over a
classical base has a hull, that is a versal formal object with bijective differential.

Both hypotheses of Stacks 06IZ beyond the Rim–Schlessinger property are discharged: condition
(S1) and (S2) come from the deformation-category property of the continuous deformations of
`ρ₀`, and the finite-dimensionality of the tangent space is the tangent clause of Stacks
0DVW. -/
@[stacks 0ET2 "the functor has a hull"]
public theorem exists_hull_continuousIsomorphismClasses
    (V : Type m) [AddCommGroup V] [Module k V] [Module.Finite k V]
    (ρ₀ : Representation k Γ V) (hρ₀ : IsContinuousRepresentation ρ₀)
    (hΛ : IsClassical Λ k)
    (hΓ : ∃ H : Subgroup Γ, Group.FG ↥H ∧ Dense (H : Set Γ)) :
    let 𝓕 := BasedCategory.ofFunctor (objectsOverFunctor
      (continuousProjection.{u, w, w, m} (Λ := Λ) (k := k) (Γ := Γ))
      (continuousSpecialFiber (Λ := Λ) V ρ₀ hρ₀))
    let hpre := (isDeformationCategory_continuousDeformationCategory
      (Λ := Λ) V ρ₀ hρ₀).predeformation
    let F := isomorphismClasses 𝓕 hpre.cofibered
    ∃ ξ : FormalObject (CategoryOfElements.π F),
      IsVersal (categoryOfElements_projection_isCofibered F) ξ ∧
        HasBijectiveDifferential (categoryOfElements_projection_isCofibered F) ξ := by
  let hD := isDeformationCategory_continuousDeformationCategory (Λ := Λ) V ρ₀ hρ₀
  let hpre := hD.predeformation
  let hS2 := schlessingerConditionS2_continuousIsomorphismClasses (Λ := Λ) V ρ₀ hρ₀
  let : IsNoetherianRing Λ := hΛ.isNoetherianRing
  let : Module.Finite Λ k := hΛ.moduleFinite
  let : Algebra.IsSeparable (residueImageField Λ k) k := hΛ.isSeparable
  let : Fact (IsPredeformationCategory.{u, w, w}
      (BasedCategory.ofFunctor (objectsOverFunctor
        (continuousProjection.{u, w, w, m} (Λ := Λ) (k := k) (Γ := Γ))
        (continuousSpecialFiber (Λ := Λ) V ρ₀ hρ₀))).p) := ⟨hpre⟩
  let : Fact (SchlessingerConditionS2 (CategoryOfElements.π
    (isomorphismClasses (BasedCategory.ofFunctor (objectsOverFunctor
      (continuousProjection.{u, w, w, m} (Λ := Λ) (k := k) (Γ := Γ))
      (continuousSpecialFiber (Λ := Λ) V ρ₀ hρ₀))) hpre.cofibered))) := ⟨hS2⟩
  let : FiniteDimensional k (tangentSpaceArtinian.{u, w, w} Λ k
      (isomorphismClasses (BasedCategory.ofFunctor (objectsOverFunctor
        (continuousProjection.{u, w, w, m} (Λ := Λ) (k := k) (Γ := Γ))
        (continuousSpecialFiber (Λ := Λ) V ρ₀ hρ₀))) hpre.cofibered)) :=
    finiteDimensional_tangentSpaceArtinian_of_artinianTangentSpace _ hpre hS2
      (finiteDimensional_continuousTangentSpace V ρ₀ hρ₀ hΓ)
  obtain ⟨ξ, -, hversal, hbijective⟩ :=
    exists_hull_isomorphismClasses.{u, w, w} Λ k
      (BasedCategory.ofFunctor (objectsOverFunctor
        (continuousProjection.{u, w, w, m} (Λ := Λ) (k := k) (Γ := Γ))
        (continuousSpecialFiber (Λ := Λ) V ρ₀ hρ₀))) hpre
      (schlessingerConditionS1_of_satisfiesRS hD.satisfiesRS)
      (schlessingerConditionS2_of_satisfiesRS hD.satisfiesRS) inferInstance
  exact ⟨imageInIsomorphismClasses _ hpre ξ, hversal, hbijective⟩

/-- **Stacks 0ET2**, prorepresentability: the functor of isomorphism classes of deformations of
a finite-dimensional continuous representation of a topologically finitely generated group over
a classical base is prorepresentable, as soon as the `Γ`-equivariant endomorphisms of the
representation are exactly the scalars, that is `H⁰(Γ, End_k(V)) = k`.

Prorepresentability is stated in the universe-raised form `Deformation.IsProrepresentableULift`,
because the values of the functor of isomorphism classes lie in the universe of the objects of
the deformation category rather than in the morphism universe of `𝒞_Λ`. -/
@[stacks 0ET2 "prorepresentability"]
public theorem isProrepresentableULift_continuousIsomorphismClasses
    (V : Type m) [AddCommGroup V] [Module k V] [Module.Finite k V]
    (ρ₀ : Representation k Γ V) (hρ₀ : IsContinuousRepresentation ρ₀)
    (hΛ : IsClassical Λ k)
    (h : ∀ f : IntertwiningMap ρ₀ ρ₀,
      ∃! a : k, (a • LinearMap.id : Module.End k V) = f.toLinearMap)
    (hΓ : ∃ H : Subgroup Γ, Group.FG ↥H ∧ Dense (H : Set Γ)) :
    IsProrepresentableULift (isomorphismClasses
      (BasedCategory.ofFunctor (objectsOverFunctor
        (continuousProjection.{u, w, w, m} (Λ := Λ) (k := k) (Γ := Γ))
        (continuousSpecialFiber (Λ := Λ) V ρ₀ hρ₀)))
      (isDeformationCategory_continuousDeformationCategory
        (Λ := Λ) V ρ₀ hρ₀).predeformation.cofibered) := by
  let : IsNoetherianRing Λ := hΛ.isNoetherianRing
  let : Module.Finite Λ k := hΛ.moduleFinite
  apply (isProrepresentableULift_iff_isDeformationFunctor _).2
  refine ⟨isDeformationFunctor_continuousIsomorphismClasses V ρ₀ hρ₀ h, ?_, ?_⟩
  · let hDcont := isDeformationCategory_continuousDeformationCategory (Λ := Λ) V ρ₀ hρ₀
    let 𝓕c := BasedCategory.ofFunctor (objectsOverFunctor
      (continuousProjection.{u, w, w, m} (Λ := Λ) (k := k) (Γ := Γ))
      (continuousSpecialFiber (Λ := Λ) V ρ₀ hρ₀))
    let F := isomorphismClasses 𝓕c hDcont.predeformation.cofibered
    let 𝓖 := BasedCategory.ofFunctor (CategoryOfElements.π F)
    let hDel := (isDeformationCategory_iff F).2
      (isDeformationFunctor_continuousIsomorphismClasses V ρ₀ hρ₀ h)
    let hS2el :=
      Artin.schlessingerConditionS2_isomorphismClasses_of_isDeformationCategory 𝓖 hDel
    let hS2c :=
      Artin.schlessingerConditionS2_isomorphismClasses_of_isDeformationCategory 𝓕c hDcont
    exact finiteDimensional_tangentSpaceArtinian_of_artinianTangentSpace 𝓖
      hDel.predeformation hS2el
      (finiteDimensional_artinianTangentSpace_of_essSurj 𝓕c 𝓖
        hDcont.predeformation hDel.predeformation hS2c hS2el
        (toIsomorphismClasses 𝓕c hDcont.predeformation.cofibered)
        (fun A => (isomorphismClassesData 𝓕c
          hDcont.predeformation.cofibered).quotient.fiber_essSurj A)
        (finiteDimensional_continuousTangentSpace V ρ₀ hρ₀ hΓ))
  · intro first second _
    ext value
    obtain ⟨scalar, rfl⟩ := hΛ.surjective_algebraMap value
    simp

end Deformation.Examples.FiniteProjectiveRepresentation

end
