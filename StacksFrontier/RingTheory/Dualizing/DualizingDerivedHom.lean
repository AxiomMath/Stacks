module

public import Mathlib.Algebra.Category.ModuleCat.Ulift
public import Mathlib.CategoryTheory.Linear.Yoneda
public import StacksFrontier.Homology.HomComplex.DerivedAdjunction
public import StacksFrontier.Homology.HomComplex.Evaluation.Iterated
public import StacksFrontier.RingTheory.Dualizing.AdjunctionCoherence
public import StacksFrontier.RingTheory.Dualizing.Complex
public import StacksFrontier.RingTheory.Dualizing.DerivedHomFiniteCohomology

/-!
# Duality from a dualizing complex

Let `A` be a Noetherian ring and let `ω` be a dualizing complex for `A`. Derived Hom into `ω`
is the contravariant functor `D : K ↦ RHom_A(K, ω)` on the derived category of `A`-modules,
built from the canonical derived tensor--Hom adjunction. A dualizing complex has finite
injective dimension, so it is represented by a complex of injectives concentrated in a finite
range of degrees `[a, b]`; consequently `D` carries cohomological bounds to cohomological
bounds, with the two bounds exchanged: an object which is cohomologically `≥ n` is sent to one
which is cohomologically `≤ b - n`, and an object which is cohomologically `≤ n` is sent to one
which is cohomologically `≥ a - n`. In particular `D` preserves cohomological boundedness. It
also preserves finiteness of cohomology, because a dualizing complex is itself of finite
injective dimension with finite cohomology, which is exactly the hypothesis of [stacks 0G4H].

The canonical biduality morphism `K ⟶ RHom_A(RHom_A(K, ω), ω)` is the transpose, under the
tensor--Hom adjunction, of evaluation after interchanging the two tensor factors. This file
factors it: it is the inverse left unitor, followed by tensoring with the derived homothety
`A ⟶ RHom_A(ω, ω)`, followed by the internalized evaluation morphism of [stacks 0A67]. The
factorization holds for an arbitrary derived tensor--Hom adjunction carrying a tensor unit whose
left unitor is natural and satisfies the left-unitor/associator triangle, and uses nothing else.
Since both of those coherence identities are available for the adjunction of [stacks 0A63], the
invertibility of biduality reduces to the invertibility of two canonical morphisms: the derived
homothety, which the dualizing hypothesis of [stacks 0A7B] controls, and the internalized
evaluation at `(K, ω, ω)`, which [stacks 0A69] controls.

## Main definitions

* `Dualizing.dualizingDerivedHomFunctor` is the functor `RHom_A(-, ω)`.
* `Dualizing.extIntoOmegaAt` is the module-valued functor `Ext^i_A(-, ω)`.
* `Dualizing.derivedHomothety` is the transpose of the left unitor at `ω`, i.e. the canonical
  morphism from the tensor unit to `RHom_A(ω, ω)`.
* `Dualizing.bidualityMor`, `Dualizing.dualizingBidualityMor` are the canonical biduality
  morphism, for an abstract adjunction and for the fixed adjunction of [stacks 0A63].

## Main results

* `Dualizing.dualizingDerivedHom_isLE_of_isGE` and
  `Dualizing.dualizingDerivedHom_isGE_of_isLE` are the two bound exchanges.
* `Dualizing.dualizingDerivedHom_bounded` is the preservation of cohomological boundedness.
* `Dualizing.dualizingDerivedHom_finiteCohomology` is the preservation of finiteness of
  cohomology.
* `Dualizing.bidualityMor_eq_internalCurryMor` is the unitor factorization of biduality, and
  `Dualizing.dualizingBidualityMor_eq` is that factorization at the adjunction of [stacks 0A63].
* `Dualizing.isIso_evaluation_of_isIso_derivedHomothety`: an invertible derived homothety makes
  the evaluation morphism `RHom(ω, ω) ⊗ ω ⟶ ω` an isomorphism.
* `Dualizing.isIso_dualizingBidualityMor` is the resulting biduality criterion.
* `Dualizing.derivedHomothety_transport` carries the derived homothety along an additive
  equivalence of derived categories, and `Dualizing.isIso_derivedHomothety_overRing` applies
  this to the scalar equivalence defining the adjunction of [stacks 0A63].

## Implementation notes

The derived-Hom functor is the fixed construction
`StacksDraft.DerivedHom.derivedHomAdjunctionOverRing`, so that the ring universe and the
admissible module universe are independent. That construction is obtained by transporting the
single-universe adjunction over `ULift A` along restriction of scalars, and its K-injective
model comparison `StacksDraft.DerivedHom.derivedHomModelIso` is therefore stated for complexes
of `ULift A`-modules. The bound computations here are carried out on such a model: a cochain
complex over `A` with a strict cohomological bound is moved to `ULift A` by the inverse of the
scalar equivalence, which preserves strict bounds and injectivity of the terms because it is an
equivalence of abelian categories, and the resulting Hom complex vanishes outside the expected
range for elementary reasons (`StacksDraft.DerivedHom.homComplexR_isStrictlyLE`).

The abstract biduality section is stated for a bare `StacksDraft.DerivedHom.DerivedHomAdjunction`
together with a chosen tensor unit and left unitor, because that structure records no unit of its
own; the unit and unitor of the adjunction over a ring are
`StacksDraft.DerivedHom.derivedTensorUnit` and
`StacksDraft.DerivedHom.derivedTensorUnitLeft`. Pairs of morphisms fed to the tensor bifunctor
are written as type ascriptions rather than through `show ... from`, since the latter elaborates
to a `have` which blocks rewriting against the naturality fields; `Dualizing.tensorMap_comp` and
its two companions restate the relevant structure lemmas in that form.

## References

* [Stacks Project, Tag 0A7C](https://stacks.math.columbia.edu/tag/0A7C)
* [Stacks Project, Tag 0A7B](https://stacks.math.columbia.edu/tag/0A7B)
* [Stacks Project, Tag 0A67](https://stacks.math.columbia.edu/tag/0A67)
* [Stacks Project, Tag 0G4H](https://stacks.math.columbia.edu/tag/0G4H)
-/

@[expose] public noncomputable section

open CategoryTheory

attribute [local instance] HasDerivedCategory.standard

namespace Dualizing

open StacksDraft.DerivedHom

universe u v

variable (A : Type u) [CommRing A]

/-! ### The derived-Hom functor against a fixed object -/

/-- The contravariant functor `RHom_A(-, ω)` defined using the canonical derived
tensor--Hom adjunction. -/
-- The `@[stacks 0A7C]` attribute below carries a quoted suffix naming the part of
-- Tag 0A7C that this declaration states. Tag 0A7C is covered by several
-- declarations, one for each of its assertions, and this is one of them;
-- the full statement of the tag is not claimed here, only the assertion
-- named in the suffix.
@[stacks 0A7C "the functor"]
public def dualizingDerivedHomFunctor
    (ω : DerivedCategory (ModuleCat.{max u v} A)) :
    (DerivedCategory (ModuleCat.{max u v} A))ᵒᵖ ⥤
      DerivedCategory (ModuleCat.{max u v} A) :=
  Functor.prod' (Functor.id _) ((Functor.const _).obj ω) ⋙
    (derivedHomAdjunctionOverRing A).hom

/-- The contravariant functor `M ↦ Ext^i_A(M, ω)`, with the usual signed
cohomological degree and precomposition as its action on module maps. -/
public def extIntoOmegaAt
    (ω : DerivedCategory (ModuleCat.{max u v} A)) (i : ℤ) :
    (ModuleCat.{max u v} A)ᵒᵖ ⥤ ModuleCat.{max (u + 1) (v + 1)} A :=
  (DerivedCategory.singleFunctor (ModuleCat.{max u v} A) 0).op ⋙
    (linearYoneda A (DerivedCategory (ModuleCat.{max u v} A))).obj
      ((shiftFunctor (DerivedCategory (ModuleCat.{max u v} A)) i).obj ω)

/-! ### Scalar transport of cochain models -/

section ScalarTransport

/-- An object of `D(A)` with a cohomological lower bound is the scalar transport of a cochain
complex of `ULift A`-modules with the same strict lower bound. -/
theorem exists_scalarModel_isStrictlyGE
    (X : DerivedCategory (ModuleCat.{max u v} A)) (n : ℤ) (hX : X.IsGE n) :
    ∃ F : CochainComplex (ModuleCat.{max u v} (ULift.{v} A)) ℤ, F.IsStrictlyGE n ∧
      Nonempty (X ≅ (derivedScalarEquivalence.{u, v} A).functor.obj
        (DerivedCategory.Q.obj F)) := by
  let := hX
  obtain ⟨F, hF, ⟨iF⟩⟩ := X.exists_iso_Q_obj_of_isGE n
  refine ⟨(scalarComplexEquivalence.{u, v} A).inverse.obj F,
    isStrictlyGE_mapHomologicalComplex
      (uliftModuleEquivalence.{u, max u v, v} A).inverse F n hF, ⟨iF ≪≫ ?_⟩⟩
  exact (DerivedCategory.Q.mapIso
      ((scalarComplexEquivalence.{u, v} A).counitIso.app F)).symm ≪≫
    (scalarFactors.{u, v} A ((scalarComplexEquivalence.{u, v} A).inverse.obj F)).symm

/-- An object of `D(A)` with a cohomological upper bound is the scalar transport of a cochain
complex of `ULift A`-modules with the same strict upper bound. -/
theorem exists_scalarModel_isStrictlyLE
    (X : DerivedCategory (ModuleCat.{max u v} A)) (n : ℤ) (hX : X.IsLE n) :
    ∃ F : CochainComplex (ModuleCat.{max u v} (ULift.{v} A)) ℤ, F.IsStrictlyLE n ∧
      Nonempty (X ≅ (derivedScalarEquivalence.{u, v} A).functor.obj
        (DerivedCategory.Q.obj F)) := by
  let := hX
  obtain ⟨F, hF, ⟨iF⟩⟩ := X.exists_iso_Q_obj_of_isLE n
  refine ⟨(scalarComplexEquivalence.{u, v} A).inverse.obj F,
    isStrictlyLE_mapHomologicalComplex
      (uliftModuleEquivalence.{u, max u v, v} A).inverse F n hF, ⟨iF ≪≫ ?_⟩⟩
  exact (DerivedCategory.Q.mapIso
      ((scalarComplexEquivalence.{u, v} A).counitIso.app F)).symm ≪≫
    (scalarFactors.{u, v} A ((scalarComplexEquivalence.{u, v} A).inverse.obj F)).symm

/-- The scalar transport of a cochain complex with a strict upper bound has the same
cohomological upper bound. -/
theorem isLE_scalarTransport (F : CochainComplex (ModuleCat.{max u v} (ULift.{v} A)) ℤ)
    (n : ℤ) (hF : F.IsStrictlyLE n) :
    ((derivedScalarEquivalence.{u, v} A).functor.obj (DerivedCategory.Q.obj F)).IsLE n := by
  let h : CochainComplex.IsStrictlyLE ((scalarComplexEquivalence.{u, v} A).functor.obj F) n :=
    isStrictlyLE_mapHomologicalComplex
      (uliftModuleEquivalence.{u, max u v, v} A).functor F n hF
  let := h
  exact DerivedCategory.TStructure.t.isLE_of_iso (scalarFactors.{u, v} A F).symm n

/-- The scalar transport of a cochain complex with a strict lower bound has the same
cohomological lower bound. -/
theorem isGE_scalarTransport (F : CochainComplex (ModuleCat.{max u v} (ULift.{v} A)) ℤ)
    (n : ℤ) (hF : F.IsStrictlyGE n) :
    ((derivedScalarEquivalence.{u, v} A).functor.obj (DerivedCategory.Q.obj F)).IsGE n := by
  let h : CochainComplex.IsStrictlyGE ((scalarComplexEquivalence.{u, v} A).functor.obj F) n :=
    isStrictlyGE_mapHomologicalComplex
      (uliftModuleEquivalence.{u, max u v, v} A).functor F n hF
  let := h
  exact DerivedCategory.TStructure.t.isGE_of_iso (scalarFactors.{u, v} A F).symm n

end ScalarTransport

/-! ### Exchange of cohomological bounds -/

/-- Derived Hom out of a cohomologically bounded-below object, into an object of injective
amplitude `[a, b]`, is cohomologically bounded above. -/
theorem dualizingDerivedHom_isLE_of_isGE
    (ω X : DerivedCategory (ModuleCat.{max u v} A)) (n a b : ℤ) (hX : X.IsGE n)
    (hω : StacksDraft.InjectiveDimension.HasInjectiveAmplitude ω a b) :
    ((dualizingDerivedHomFunctor.{u, v} A ω).obj (Opposite.op X)).IsLE (b - n) := by
  obtain ⟨F, hF, ⟨iF⟩⟩ := exists_scalarModel_isStrictlyGE.{u, v} A X n hX
  obtain ⟨J, hJa, hJb, hJK, ⟨iJ⟩⟩ := exists_scalarModel_isKInjective.{u, v} A ω a b hω
  let := hJK
  let key : (dualizingDerivedHomFunctor.{u, v} A ω).obj (Opposite.op X) ≅
      (derivedScalarEquivalence.{u, v} A).functor.obj
        (DerivedCategory.Q.obj (CochainComplex.HomComplexR (ULift.{v} A) F J)) :=
    (derivedHomAdjunctionOverRing A).hom.mapIso (Iso.prod iF.symm.op iJ) ≪≫
      derivedHomModelIso.{u, v} A F J
  let := isLE_scalarTransport.{u, v} A (CochainComplex.HomComplexR (ULift.{v} A) F J) (b - n)
    (homComplexR_isStrictlyLE F J n b hF hJb)
  exact DerivedCategory.TStructure.t.isLE_of_iso key.symm (b - n)

/-- Derived Hom out of a cohomologically bounded-above object, into an object of injective
amplitude `[a, b]`, is cohomologically bounded below. -/
theorem dualizingDerivedHom_isGE_of_isLE
    (ω X : DerivedCategory (ModuleCat.{max u v} A)) (n a b : ℤ) (hX : X.IsLE n)
    (hω : StacksDraft.InjectiveDimension.HasInjectiveAmplitude ω a b) :
    ((dualizingDerivedHomFunctor.{u, v} A ω).obj (Opposite.op X)).IsGE (a - n) := by
  obtain ⟨F, hF, ⟨iF⟩⟩ := exists_scalarModel_isStrictlyLE.{u, v} A X n hX
  obtain ⟨J, hJa, hJb, hJK, ⟨iJ⟩⟩ := exists_scalarModel_isKInjective.{u, v} A ω a b hω
  let := hJK
  let key : (dualizingDerivedHomFunctor.{u, v} A ω).obj (Opposite.op X) ≅
      (derivedScalarEquivalence.{u, v} A).functor.obj
        (DerivedCategory.Q.obj (CochainComplex.HomComplexR (ULift.{v} A) F J)) :=
    (derivedHomAdjunctionOverRing A).hom.mapIso (Iso.prod iF.symm.op iJ) ≪≫
      derivedHomModelIso.{u, v} A F J
  let := isGE_scalarTransport.{u, v} A (CochainComplex.HomComplexR (ULift.{v} A) F J) (a - n)
    (homComplexR_isStrictlyGE F J n a hF hJa)
  exact DerivedCategory.TStructure.t.isGE_of_iso key.symm (a - n)

/-- On objects with finite cohomology, derived Hom into a dualizing complex preserves
cohomological boundedness. -/
-- The `@[stacks 0A7C]` attribute below carries a quoted suffix naming the part of
-- Tag 0A7C that this declaration states. Tag 0A7C is covered by several
-- declarations, one for each of its assertions, and this is one of them;
-- the full statement of the tag is not claimed here, only the assertion
-- named in the suffix.
@[stacks 0A7C "preservation of bounded coherent objects"]
public theorem dualizingDerivedHom_bounded [IsNoetherianRing A]
    (ω : DerivedCategory (ModuleCat.{max u v} A)) (hω : IsDualizingComplex ω)
    (K : DerivedCategory (ModuleCat.{max u v} A))
    (hK : ∀ i : ℤ, Module.Finite A
      ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} A) i).obj K))
    (hK' : (DerivedCategory.TStructure.t).bounded K) :
    (DerivedCategory.TStructure.t).bounded
      ((dualizingDerivedHomFunctor.{u, v} A ω).obj (.op K)) := by
  have := hK
  obtain ⟨⟨n, hn⟩, ⟨m, hm⟩⟩ := hK'
  obtain ⟨a, b, hamp⟩ := hω.finiteInjectiveDimension
  exact ⟨⟨a - m, dualizingDerivedHom_isGE_of_isLE.{u, v} A ω K m a b hm hamp⟩,
    ⟨b - n, dualizingDerivedHom_isLE_of_isGE.{u, v} A ω K n a b hn hamp⟩⟩

/-! ### Preservation of finite cohomology -/

/-- Derived Hom into a dualizing complex has finite cohomology when its argument does.

This is Tag 0G4H specialized to a dualizing complex as target: a dualizing complex has finite
cohomology and finite injective dimension, which are exactly the two hypotheses that tag puts
on its second argument. -/
-- The `@[stacks 0A7C]` attribute below carries a quoted suffix naming the part of
-- Tag 0A7C that this declaration states. Tag 0A7C is covered by several
-- declarations, one for each of its assertions, and this is one of them;
-- the full statement of the tag is not claimed here, only the assertion
-- named in the suffix.
@[stacks 0A7C "preservation of coherent objects"]
public theorem dualizingDerivedHom_finiteCohomology [IsNoetherianRing A]
    (ω : DerivedCategory (ModuleCat.{max u v} A)) (hω : IsDualizingComplex ω)
    (K : DerivedCategory (ModuleCat.{max u v} A))
    (hK : ∀ i : ℤ, Module.Finite A
      ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} A) i).obj K)) :
    ∀ i : ℤ, Module.Finite A
      ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} A) i).obj
        ((dualizingDerivedHomFunctor.{u, v} A ω).obj (.op K))) :=
  derivedHom_finiteCohomology.{u, v} K ω hK hω.finiteCohomology hω.finiteInjectiveDimension

/-! ### Biduality for an abstract derived tensor--Hom adjunction -/

section AbstractBiduality

universe u₁ v₁ w₁

variable {R : Type u₁} [CommRing R] [HasDerivedCategory.{w₁} (ModuleCat.{v₁} R)]
    (d : DerivedHomAdjunction R) (one : DerivedCategory (ModuleCat.{v₁} R))
    (lam : ∀ K : DerivedCategory (ModuleCat.{v₁} R), d.tensor.obj (one, K) ≅ K)

/-- The tensor bifunctor applied to a composite pair of morphisms. This repeats
`DerivedHomAdjunction.tensor_map_comp` with the pair written as a type ascription rather than
through `show ... from`, which is the form the naturality fields present and hence the form
`rw` can match. -/
private theorem tensorMap_comp {A₁ A₂ A₃ B₁ B₂ B₃ : DerivedCategory (ModuleCat.{v₁} R)}
    (f : A₁ ⟶ A₂) (g : A₂ ⟶ A₃) (f' : B₁ ⟶ B₂) (g' : B₂ ⟶ B₃) :
    d.tensor.map ((f, f') : (A₁, B₁) ⟶ (A₂, B₂)) ≫
        d.tensor.map ((g, g') : (A₂, B₂) ⟶ (A₃, B₃)) =
      d.tensor.map ((f ≫ g, f' ≫ g') : (A₁, B₁) ⟶ (A₃, B₃)) :=
  (d.tensor.map_comp _ _).symm

/-- The tensor bifunctor applied to a pair of identities. -/
private theorem tensorMap_id (A B : DerivedCategory (ModuleCat.{v₁} R)) :
    d.tensor.map ((𝟙 A, 𝟙 B) : (A, B) ⟶ (A, B)) = 𝟙 (d.tensor.obj (A, B)) :=
  d.tensor.map_id (A, B)

/-- Splitting a composite in the left slot of a tensored morphism. -/
private theorem tensorMap_fst_comp {A₁ A₂ A₃ : DerivedCategory (ModuleCat.{v₁} R)}
    (f : A₁ ⟶ A₂) (g : A₂ ⟶ A₃) (W : DerivedCategory (ModuleCat.{v₁} R)) :
    d.tensor.map ((f ≫ g, 𝟙 W) : (A₁, W) ⟶ (A₃, W)) =
      d.tensor.map ((f, 𝟙 W) : (A₁, W) ⟶ (A₂, W)) ≫
        d.tensor.map ((g, 𝟙 W) : (A₂, W) ⟶ (A₃, W)) := by
  rw [tensorMap_comp, Category.comp_id]

/-- The derived homothety `1 ⟶ RHom(ω, ω)`: the transpose, under the tensor--Hom adjunction, of
the left unitor at `ω`. -/
def derivedHomothety (ω : DerivedCategory (ModuleCat.{v₁} R)) :
    one ⟶ d.hom.obj (Opposite.op ω, ω) :=
  (d.homEquiv one ω ω).symm (lam ω).hom

/-- Evaluating the derived homothety returns the left unitor: the homothety is by definition the
transpose of the unitor, and evaluation is the transpose of the identity. -/
theorem tensorMap_derivedHomothety_comp_evaluation (ω : DerivedCategory (ModuleCat.{v₁} R)) :
    d.tensor.map ((derivedHomothety d one lam ω, 𝟙 ω) :
        (one, ω) ⟶ (d.hom.obj (Opposite.op ω, ω), ω)) ≫ d.evaluation ω ω =
      (lam ω).hom := by
  rw [DerivedHomAdjunction.evaluation, ← d.homEquiv_naturality_left, Category.comp_id,
    derivedHomothety, AddEquiv.apply_symm_apply]

/-- **An invertible derived homothety makes the evaluation morphism at `(ω, ω)` an
isomorphism.** If the canonical morphism `1 ⟶ RHom(ω, ω)` is invertible then so is the
evaluation morphism `RHom(ω, ω) ⊗ ω ⟶ ω` of the tensor--Hom adjunction.

Only `Dualizing.tensorMap_derivedHomothety_comp_evaluation` is used: the homothety tensored
with the identity of `ω`, followed by the evaluation morphism, *is* the left unitor, so with the
homothety invertible the evaluation morphism is an isomorphism composed after an isomorphism.

This is what connects biduality to the *canonical evaluation*. An isomorphism
`RHom(ω, ω) ≅ 1` assembled from a chosen inverse — such as
`Dualizing.dualizingDerivedHomSelfIsoRing`, which comes out of the biduality anti-equivalence of
[stacks 0A7C] — says nothing about the evaluation morphism; invertibility of the homothety, which
is a *named morphism*, does. It is the half of the evaluation input of [stacks 0ATP] that is not
[stacks 0A68]; see the module documentation of
`StacksFrontier/AlgebraicGeometry/Duality/GlobalDualizingUniqueness.lean`. -/
theorem isIso_evaluation_of_isIso_derivedHomothety (ω : DerivedCategory (ModuleCat.{v₁} R))
    (h : IsIso (derivedHomothety d one lam ω)) :
    IsIso (d.evaluation ω ω) := by
  have : IsIso ((derivedHomothety d one lam ω, 𝟙 ω) :
      (one, ω) ⟶ (d.hom.obj (Opposite.op ω, ω), ω)) :=
    (isIso_prod_iff _ _).2 ⟨h, inferInstance⟩
  have : IsIso (d.tensor.map ((derivedHomothety d one lam ω, 𝟙 ω) :
      (one, ω) ⟶ (d.hom.obj (Opposite.op ω, ω), ω))) := inferInstance
  have : IsIso (d.tensor.map ((derivedHomothety d one lam ω, 𝟙 ω) :
        (one, ω) ⟶ (d.hom.obj (Opposite.op ω, ω), ω)) ≫ d.evaluation ω ω) := by
    rw [tensorMap_derivedHomothety_comp_evaluation]
    infer_instance
  exact IsIso.of_isIso_comp_left
    (d.tensor.map ((derivedHomothety d one lam ω, 𝟙 ω) :
      (one, ω) ⟶ (d.hom.obj (Opposite.op ω, ω), ω))) (d.evaluation ω ω)

/-- The canonical biduality morphism `K ⟶ RHom(RHom(K, ω), ω)`: the transpose, under the
tensor--Hom adjunction, of evaluation after interchanging the two tensor factors. -/
def bidualityMor (ω K : DerivedCategory (ModuleCat.{v₁} R)) :
    K ⟶ d.hom.obj (Opposite.op (d.hom.obj (Opposite.op K, ω)), ω) :=
  (d.homEquiv K (d.hom.obj (Opposite.op K, ω)) ω).symm
    ((d.tensorSwap K (d.hom.obj (Opposite.op K, ω))).hom ≫ d.evaluation K ω)

/-- **The unitor factorization of biduality.** The canonical biduality morphism is the inverse
left unitor, followed by tensoring with the derived homothety, followed by the internalized
evaluation morphism of [stacks 0A67]. Only two coherence properties of the unitor enter: its
naturality and the left-unitor/associator triangle. -/
theorem bidualityMor_eq_internalCurryMor
    (hlam : DerivedHomAdjunction.IsUnitorNatural d one lam)
    (htri : ∀ K X : DerivedCategory (ModuleCat.{v₁} R),
      DerivedHomAdjunction.IsUnitorTriangleAt d one lam K X)
    (ω K : DerivedCategory (ModuleCat.{v₁} R)) :
    bidualityMor d ω K =
      (lam K).inv ≫
        d.tensor.map ((derivedHomothety d one lam ω, 𝟙 K) :
          (one, K) ⟶ (d.hom.obj (Opposite.op ω, ω), K)) ≫
        d.internalCurryMor K ω ω := by
  have hassoc := d.tensorAssoc_naturality (derivedHomothety d one lam ω) (𝟙 K)
    (𝟙 (d.hom.obj (Opposite.op K, ω)))
  rw [d.tensor_map_id] at hassoc
  have hkey : d.tensor.map ((derivedHomothety d one lam ω,
          𝟙 (d.tensor.obj (K, d.hom.obj (Opposite.op K, ω)))) :
        (one, d.tensor.obj (K, d.hom.obj (Opposite.op K, ω))) ⟶
          (d.hom.obj (Opposite.op ω, ω),
            d.tensor.obj (K, d.hom.obj (Opposite.op K, ω)))) ≫
      d.tensor.map ((𝟙 (d.hom.obj (Opposite.op ω, ω)),
          (d.tensorSwap K (d.hom.obj (Opposite.op K, ω))).hom) :
        (d.hom.obj (Opposite.op ω, ω),
            d.tensor.obj (K, d.hom.obj (Opposite.op K, ω))) ⟶
          (d.hom.obj (Opposite.op ω, ω),
            d.tensor.obj (d.hom.obj (Opposite.op K, ω), K))) ≫
      d.tensor.map ((𝟙 (d.hom.obj (Opposite.op ω, ω)), d.evaluation K ω) :
        (d.hom.obj (Opposite.op ω, ω),
            d.tensor.obj (d.hom.obj (Opposite.op K, ω), K)) ⟶
          (d.hom.obj (Opposite.op ω, ω), ω)) =
      d.tensor.map ((𝟙 one,
          (d.tensorSwap K (d.hom.obj (Opposite.op K, ω))).hom ≫ d.evaluation K ω) :
        (one, d.tensor.obj (K, d.hom.obj (Opposite.op K, ω))) ⟶ (one, ω)) ≫
        d.tensor.map ((derivedHomothety d one lam ω, 𝟙 ω) :
          (one, ω) ⟶ (d.hom.obj (Opposite.op ω, ω), ω)) := by
    rw [← Category.assoc, tensorMap_comp, tensorMap_comp, tensorMap_comp]
    simp
  have hnat : d.tensor.map ((𝟙 one,
        (d.tensorSwap K (d.hom.obj (Opposite.op K, ω))).hom ≫ d.evaluation K ω) :
        (one, d.tensor.obj (K, d.hom.obj (Opposite.op K, ω))) ⟶ (one, ω)) ≫
      (lam ω).hom =
      (lam (d.tensor.obj (K, d.hom.obj (Opposite.op K, ω)))).hom ≫
        (d.tensorSwap K (d.hom.obj (Opposite.op K, ω))).hom ≫ d.evaluation K ω :=
    hlam _
  have htri' : (d.tensorAssoc one K (d.hom.obj (Opposite.op K, ω))).hom ≫
      (lam (d.tensor.obj (K, d.hom.obj (Opposite.op K, ω)))).hom =
      d.tensor.map (((lam K).hom, 𝟙 (d.hom.obj (Opposite.op K, ω))) :
        (d.tensor.obj (one, K), d.hom.obj (Opposite.op K, ω)) ⟶
          (K, d.hom.obj (Opposite.op K, ω))) :=
    htri K (d.hom.obj (Opposite.op K, ω))
  apply (d.homEquiv K (d.hom.obj (Opposite.op K, ω)) ω).injective
  rw [bidualityMor, AddEquiv.apply_symm_apply, ← Category.assoc,
    d.homEquiv_naturality_left, DerivedHomAdjunction.internalCurryMor,
    AddEquiv.apply_symm_apply, tensorMap_fst_comp]
  simp only [Category.assoc]
  rw [reassoc_of% hassoc, reassoc_of% hkey, tensorMap_derivedHomothety_comp_evaluation,
    hnat, reassoc_of% htri', ← Category.assoc, tensorMap_comp,
    Category.comp_id, Iso.inv_hom_id, tensorMap_id, Category.id_comp]

/-! ### Transport of the derived homothety along an equivalence -/

section HomothetyTransport

universe u₂ v₂ w₂

variable {S : Type u₂} [CommRing S] [HasDerivedCategory.{w₂} (ModuleCat.{v₂} S)]
    (e : DerivedCategory (ModuleCat.{v₁} R) ≌ DerivedCategory (ModuleCat.{v₂} S))
    [e.functor.Additive]

omit [e.functor.Additive] in
/-- The transpose of the left unitor, read off through the unit of the equivalence. -/
private theorem homEquiv_symm_tensorMap_unitorLeft (ω : DerivedCategory (ModuleCat.{v₂} S)) :
    (d.homEquiv (e.inverse.obj (e.functor.obj one)) (e.inverse.obj ω)
          (e.inverse.obj ω)).symm
        (d.tensor.map ((e.unitIso.inv.app one, 𝟙 (e.inverse.obj ω)) :
            (e.inverse.obj (e.functor.obj one), e.inverse.obj ω) ⟶
              (one, e.inverse.obj ω)) ≫ (lam (e.inverse.obj ω)).hom) =
      e.unitIso.inv.app one ≫ derivedHomothety d one lam (e.inverse.obj ω) := by
  apply (d.homEquiv _ (e.inverse.obj ω) (e.inverse.obj ω)).injective
  rw [AddEquiv.apply_symm_apply, d.homEquiv_naturality_left, derivedHomothety]
  simp only [Functor.id_obj, AddEquiv.apply_symm_apply]

omit [e.functor.Additive] in
/-- A morphism into the image of the inverse equivalence, pushed forward, composed with the
counit and pulled back again, is recovered by the unit. -/
private theorem unit_comp_inverse_map_counit (X : DerivedCategory (ModuleCat.{v₁} R))
    (ω : DerivedCategory (ModuleCat.{v₂} S)) (w : X ⟶ e.inverse.obj ω) :
    e.unit.app X ≫ e.inverse.map (e.functor.map w ≫ e.counitIso.hom.app ω) = w := by
  rw [e.inverse.map_comp, reassoc_of% (Equivalence.unit_naturality e w),
    Equivalence.unit_inverse_comp, Category.comp_id]

/-- **The derived homothety transports.** For an adjunction transported along an additive
equivalence of derived categories, with the unitor carried along by
`DerivedHomAdjunction.transportUnitorLeft`, the derived homothety at `ω` is the image of the
original derived homothety at the preimage of `ω`, conjugated by the unit and the counit of the
equivalence. -/
theorem derivedHomothety_transport (ω : DerivedCategory (ModuleCat.{v₂} S)) :
    derivedHomothety (d.transport e) (e.functor.obj one)
        (DerivedHomAdjunction.transportUnitorLeft d one lam e) ω =
      e.counitInv.app (e.functor.obj one) ≫
        e.functor.map (e.unitIso.inv.app one ≫
          derivedHomothety d one lam (e.inverse.obj ω)) := by
  dsimp only [derivedHomothety, DerivedHomAdjunction.transport,
    DerivedHomAdjunction.transportHomEquiv, DerivedHomAdjunction.transportUnitorLeft,
    DerivedHomAdjunction.transportTensor, DerivedHomAdjunction.transportHom]
  simp only [AddEquiv.symm_trans_apply, AddEquiv.symm_symm, Adjunction.homAddEquiv_apply,
    Adjunction.homEquiv_unit, Equivalence.toAdjunction_unit, Equivalence.symm_functor,
    Equivalence.symm_inverse, Equivalence.symm_unit, Iso.trans_hom, Functor.mapIso_hom,
    Iso.prod_hom, Iso.symm_hom, Iso.app_hom, Iso.app_inv, Iso.refl_hom]
  rw [unit_comp_inverse_map_counit e _ ω,
    homEquiv_symm_tensorMap_unitorLeft d one lam e ω, derivedHomothety]

/-- Invertibility of the derived homothety transports along an additive equivalence. -/
theorem isIso_derivedHomothety_transport (ω : DerivedCategory (ModuleCat.{v₂} S))
    (h : IsIso (derivedHomothety d one lam (e.inverse.obj ω))) :
    IsIso (derivedHomothety (d.transport e) (e.functor.obj one)
      (DerivedHomAdjunction.transportUnitorLeft d one lam e) ω) := by
  have := h
  have h2 : IsIso (e.counitInv.app (e.functor.obj one) ≫
      e.functor.map (e.unitIso.inv.app one ≫
        derivedHomothety d one lam (e.inverse.obj ω))) := inferInstance
  rw [derivedHomothety_transport]
  exact h2

end HomothetyTransport

end AbstractBiduality

/-! ### The biduality criterion at the canonical adjunction over a ring -/

/-- The canonical biduality morphism `K ⟶ RHom_A(RHom_A(K, ω), ω)` for the fixed derived
tensor--Hom adjunction of [stacks 0A63]. -/
public def dualizingBidualityMor (ω K : DerivedCategory (ModuleCat.{max u v} A)) :
    K ⟶ (dualizingDerivedHomFunctor.{u, v} A ω).obj
      (Opposite.op ((dualizingDerivedHomFunctor.{u, v} A ω).obj (Opposite.op K))) :=
  bidualityMor (derivedHomAdjunctionOverRing A) ω K

/-- The canonical biduality morphism of [stacks 0A7C] is the inverse left unitor, followed by
tensoring with the derived homothety `A ⟶ RHom_A(ω, ω)`, followed by the internalized evaluation
morphism of [stacks 0A67]. This is `bidualityMor_eq_internalCurryMor` at the adjunction of
[stacks 0A63], whose left unitor and unitor coherence are
`StacksDraft.DerivedHom.derivedTensorUnitLeft`,
`StacksDraft.DerivedHom.derivedTensorUnitLeft_natural` and
`StacksDraft.DerivedHom.derivedTensorUnitLeft_triangle`. -/
public theorem dualizingBidualityMor_eq (ω K : DerivedCategory (ModuleCat.{max u v} A)) :
    dualizingBidualityMor.{u, v} A ω K =
      (derivedTensorUnitLeft A K).inv ≫
        (derivedHomAdjunctionOverRing A).tensor.map
          ((derivedHomothety (derivedHomAdjunctionOverRing A) (derivedTensorUnit A)
              (derivedTensorUnitLeft A) ω, 𝟙 K) :
            (derivedTensorUnit A, K) ⟶
              ((derivedHomAdjunctionOverRing A).hom.obj (Opposite.op ω, ω), K)) ≫
        (derivedHomAdjunctionOverRing A).internalCurryMor K ω ω :=
  bidualityMor_eq_internalCurryMor _ _ _ (derivedTensorUnitLeft_natural A)
    (derivedTensorUnitLeft_triangle A) ω K

open CategoryTheory.MonoidalCategory in
/-- The derived homothety of the fixed adjunction over a ring is invertible as soon as the
derived homothety of the model-level adjunction over the lifted ring is invertible at the scalar
preimage of `ω`. This is `derivedHomothety_transport` at the scalar equivalence out of which
`StacksDraft.DerivedHom.derivedHomAdjunctionOverRing` is built. -/
public theorem isIso_derivedHomothety_overRing (ω : DerivedCategory (ModuleCat.{max u v} A))
    (h : IsIso (derivedHomothety
      (derivedHomAdjunctionULift.{u, v, max u v + 1} (R := A)).toDerivedHomAdjunction
      (DerivedCategory.Q.obj (𝟙_ (Model.Complex (ULift.{v} A))))
      (derivedHomAdjunctionULift.{u, v, max u v + 1} (R := A)).tensorUnitLeft
      ((derivedScalarEquivalence.{u, v} A).inverse.obj ω))) :
    IsIso (derivedHomothety (derivedHomAdjunctionOverRing A) (derivedTensorUnit A)
      (derivedTensorUnitLeft A) ω) :=
  isIso_derivedHomothety_transport _ _ _ (derivedScalarEquivalence.{u, v} A) ω h

/-- **The evaluation morphism of [stacks 0A63] at `(ω, ω)` is an isomorphism as soon as the
derived homothety is.** This is
`Dualizing.isIso_evaluation_of_isIso_derivedHomothety` at the adjunction of [stacks 0A63], the
tensor unit `A` in degree zero and its left unitor.

It is one of the two inputs the evaluation hypothesis `hev` of
`Stacks.SheafOfModules.exists_isInvertible_tensor_iso_of_affineLocal` ([stacks 0ATP]) needs over
a Noetherian ring; see the module documentation of
`StacksFrontier/AlgebraicGeometry/Duality/GlobalDualizingUniqueness.lean` for the other. -/
public theorem isIso_evaluation_self_overRing (ω : DerivedCategory (ModuleCat.{max u v} A))
    (h : IsIso (derivedHomothety (derivedHomAdjunctionOverRing A) (derivedTensorUnit A)
      (derivedTensorUnitLeft A) ω)) :
    IsIso ((derivedHomAdjunctionOverRing A).evaluation ω ω) :=
  isIso_evaluation_of_isIso_derivedHomothety _ _ _ ω h

/-- **The biduality criterion.** The canonical biduality morphism of [stacks 0A7C] is invertible
as soon as two things are: the derived homothety `A ⟶ RHom_A(ω, ω)`, which is what the dualizing
hypothesis of [stacks 0A7B] controls, and the internalized evaluation morphism of [stacks 0A67]
at `(K, ω, ω)`, which is what [stacks 0A69] controls. -/
public theorem isIso_dualizingBidualityMor (ω K : DerivedCategory (ModuleCat.{max u v} A))
    (hone : IsIso (derivedHomothety (derivedHomAdjunctionOverRing A) (derivedTensorUnit A)
      (derivedTensorUnitLeft A) ω))
    (hcurry : IsIso ((derivedHomAdjunctionOverRing A).internalCurryMor K ω ω)) :
    IsIso (dualizingBidualityMor.{u, v} A ω K) := by
  have htensor : IsIso ((derivedHomAdjunctionOverRing A).tensor.map
      ((derivedHomothety (derivedHomAdjunctionOverRing A) (derivedTensorUnit A)
          (derivedTensorUnitLeft A) ω, 𝟙 K) :
        (derivedTensorUnit A, K) ⟶
          ((derivedHomAdjunctionOverRing A).hom.obj (Opposite.op ω, ω), K))) :=
    DerivedHomAdjunction.isIso_tensor_map _ _
  have hinv : IsIso (derivedTensorUnitLeft A K).inv := inferInstance
  have hall : IsIso ((derivedTensorUnitLeft A K).inv ≫
      (derivedHomAdjunctionOverRing A).tensor.map
          ((derivedHomothety (derivedHomAdjunctionOverRing A) (derivedTensorUnit A)
            (derivedTensorUnitLeft A) ω, 𝟙 K) :
            (derivedTensorUnit A, K) ⟶
              ((derivedHomAdjunctionOverRing A).hom.obj (Opposite.op ω, ω), K)) ≫
        (derivedHomAdjunctionOverRing A).internalCurryMor K ω ω) := inferInstance
  rw [dualizingBidualityMor_eq]
  exact hall

end Dualizing

end
