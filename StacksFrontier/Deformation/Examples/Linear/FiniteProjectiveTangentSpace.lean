module

public import Mathlib.CategoryTheory.FiberedCategory.HomLift
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import StacksFrontier.Algebra.Module.OppositeOfCommSemiring
public import StacksFrontier.Deformation.Artin.Basic
public import StacksFrontier.Deformation.Examples.Linear.DualNumberLift
public import StacksFrontier.Deformation.Examples.Linear.FiniteProjectiveRimSchlessinger
public import StacksFrontier.Deformation.PredeformationTangent.TangentVectorSpace
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The tangent space of the deformations of a finite-dimensional vector space

Let `V` be a finite-dimensional vector space over `k`. The deformations of `V` form a
deformation category, so its functor of fibrewise isomorphism classes carries a canonical
`k`-vector space structure on its value at the dual numbers: the tangent space. This file
proves that this tangent space has exactly one element, hence is the zero vector space, and
is in particular finite-dimensional.

The reason is that a deformation of `V` over `k[ε]` is a finite projective `k[ε]`-module `M`
together with an identification of `M ⊗_{k[ε]} k` with `V`, and any two such are isomorphic
over `V` — that is `Deformation.Examples.DualNumberLift.exists_linearEquiv`. The work here is
to turn such a linear isomorphism into an isomorphism in the fibre of the deformation category
over the dual-number object of `𝒞_Λ`, which is what equality of isomorphism classes means.

## Main results

* `Deformation.Examples.FiniteProjectiveModule.subsingleton_tangentSpace`: the tangent space
  of the deformations of `V` has at most one element, so it is the zero vector space.
* `Deformation.Examples.FiniteProjectiveModule.finiteDimensional_tangentSpace`: that tangent
  space is finite-dimensional.

## Implementation notes

The dual-number object of `𝒞_Λ` at which the tangent space is evaluated is the square-zero
extension of `k` by the rank-one module, `Deformation.artinianSquareZeroExtensionFunctor`
applied to `FGModuleCat.of k k`. Its carrier is `TrivSqZeroExt k M` for `M` the rank-one
module regarded as an object of `ModuleCat k`, which is not syntactically `DualNumber k`; the
private `squareZeroRankOneDualNumberEquiv` is the identification, and it is what lets a
deformation over that object be read as a `Deformation.Examples.DualNumberLift`.

Two deformations over the dual numbers are compared in three steps: each is turned into a
`DualNumberLift` of `V`, the two lifts are identified by
`Deformation.Examples.DualNumberLift.exists_linearEquiv`, and the resulting isomorphism is
assembled into an isomorphism of the slice category whose image under the projection is an
identity up to `eqToHom`. That last clause is what `CategoryTheory.IsHomLift.of_fac'` needs in
order to produce an isomorphism in the fibre.

The vector space structure on the tangent space is the canonical one of
`Deformation.associatedTangentSpaceModuleUnlifted`, supplied through the two `Fact` instances
its construction takes; both are discharged from
`Deformation.Examples.FiniteProjectiveModule.isDeformationCategory_deformationCategory`.

Stacks 93.4 computes the infinitesimal automorphisms of the same deformation category as well,
identifying them with `Module.End k V`. That second computation is
`Deformation.Examples.FiniteProjectiveModule.infinitesimalAutomorphismsEquivEnd` and
`Deformation.Examples.FiniteProjectiveModule.exists_infinitesimalAutomorphismsLinearEquivEnd`,
in `StacksFrontier/Deformation/Examples/Linear/InfinitesimalAutomorphisms/Endomorphisms.lean`; the
two results here are the tangent-space half of the lemma, and they are what the tag below is
recorded against.

## References

* [Stacks Project, Tag 0DVQ](https://stacks.math.columbia.edu/tag/0DVQ)
-/

@[expose] public noncomputable section

open CategoryTheory

namespace Deformation.Examples.FiniteProjectiveModule

universe u w t

/-- The right action of a field on a module over it, used to see a square-zero extension of
the field by that module as a commutative ring. -/
local instance tangentSpaceZeroModuleCatModuleMulOpposite (k : Type w) [Field k]
    (M : ModuleCat.{w} k) : Module kᵐᵒᵖ M :=
  Module.oppositeOfCommSemiring k M

/-- The left and right actions of a field on a module over it agree. -/
local instance tangentSpaceZeroModuleCatIsCentralScalar (k : Type w) [Field k]
    (M : ModuleCat.{w} k) : IsCentralScalar k M :=
  Module.isCentralScalar_oppositeOfCommSemiring k M

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]

/-- A morphism whose conjugate by two identifications of its source and target with one object
is the identity is itself the comparison isomorphism of those identifications. -/
private theorem eqToHom_of_conjugate_eq_id
    {C : Type*} [Category* C] {X Y Z : C} (hX : X = Z) (hY : Y = Z)
    (f : X ⟶ Y) (h : eqToHom hX.symm ≫ f ≫ eqToHom hY = 𝟙 Z) :
    f = eqToHom (hX.trans hY.symm) := by
  subst X
  subst Y
  simpa using h

/-- The rank-one module over a field, regarded as an object of `ModuleCat`: the module
underlying the dual-number object of `𝒞_Λ`. -/
private abbrev rankOneModuleCat (k : Type w) [Field k] : ModuleCat.{w} k :=
  (forget₂ (FGModuleCat.{w} k) (ModuleCat.{w} k)).obj (FGModuleCat.of k k)

/-- The rank-one module is the field itself. -/
private def rankOneModuleCatEquiv (k : Type w) [Field k] : rankOneModuleCat k ≃ₗ[k] k where
  toFun := id
  invFun := id
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl
  map_add' := fun _ _ => rfl
  map_smul' := fun _ _ => rfl

/-- The square-zero extension of a field by its rank-one module is the dual numbers. -/
private def squareZeroRankOneDualNumberEquiv (k : Type w) [Field k] :
    TrivSqZeroExt k (rankOneModuleCat k) ≃ₐ[k] DualNumber k := by
  let f := TrivSqZeroExt.map (rankOneModuleCatEquiv k).toLinearMap
  have hf : Function.Bijective f := by
    constructor
    · intro x y h
      have hfst := congrArg TrivSqZeroExt.fst h
      have hsnd := congrArg TrivSqZeroExt.snd h
      apply TrivSqZeroExt.ext
      · simpa [f] using hfst
      · apply (rankOneModuleCatEquiv k).injective
        simpa [f, TrivSqZeroExt.snd_map] using hsnd
    · intro y
      refine ⟨TrivSqZeroExt.map ((rankOneModuleCatEquiv k).symm.toLinearMap) y, ?_⟩
      apply TrivSqZeroExt.ext
      · simp [f]
      · simp [f, TrivSqZeroExt.snd_map]
  exact AlgEquiv.ofBijective f hf

/-- The dual-number object of `𝒞_Λ`, at which the tangent space is evaluated. -/
@[sga "7 VI 1.3(c)" "special case"]
private abbrev dualNumberBase (Λ : Type u) (k : Type w) [CommRing Λ] [Field k] [Algebra Λ k] :
    ArtinianLocalAlgCat.{u, w, w} Λ k :=
  (artinianSquareZeroExtensionFunctor Λ k).obj (FGModuleCat.of k k)

/-- A morphism of finite projective modules whose target is the special-fibre object of `V` has
base morphism the residue map of its source, because the identification of the residue field of
the special-fibre object with `k` is inverse to its residue map. -/
private theorem base_hom_eq_residue (V : Type t) [AddCommGroup V] [Module k V]
    [Module.Finite k V] {X : FiniteProjectiveModule.{u, w, w, t} (Λ := Λ) (k := k)}
    (H : FiniteProjectiveModule.Hom X (specialFiber (Λ := Λ) (k := k) V)) (r : X.base) :
    H.base.hom r = X.base.residueEquiv (IsLocalRing.residue X.base r) :=
  (residueFieldBase_residueEquiv_residue Λ k (H.base.hom r)).symm.trans
    (H.base.residue_comm r)

/-- A morphism from a finite projective module over the dual-number object to the special-fibre
object of `V` has base morphism the first projection. -/
private theorem base_hom_eq_fst (V : Type t) [AddCommGroup V] [Module k V] [Module.Finite k V]
    {c : Type t} [AddCommGroup c] [Module (dualNumberBase Λ k) c]
    [Module.Finite (dualNumberBase Λ k) c] [Module.Projective (dualNumberBase Λ k) c]
    (H : FiniteProjectiveModule.Hom (⟨dualNumberBase Λ k, c⟩ :
      FiniteProjectiveModule.{u, w, w, t} (Λ := Λ) (k := k)) (specialFiber (Λ := Λ) (k := k) V))
    (r : dualNumberBase Λ k) : H.base.hom r = r.fst :=
  (base_hom_eq_residue V H r).trans
    (squareZeroExtensionArtinian_residue Λ k (FGModuleCat.of k k) r)

/-- A linear equivalence over the target of a ring equivalence, where the modules over the source
are given by restriction along the inverse, is already linear over the source. -/
private theorem exists_linearEquiv_of_compHom {R S M N : Type*} [Semiring R] [Semiring S]
    [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N] (eR : R ≃+* S)
    (e : letI := Module.compHom M eR.symm.toRingHom
      letI := Module.compHom N eR.symm.toRingHom
      M ≃ₗ[S] N) :
    ∃ f : M ≃ₗ[R] N, ∀ m, f m = e m := by
  let := Module.compHom M eR.symm.toRingHom
  let := Module.compHom N eR.symm.toRingHom
  refine ⟨{ e with map_smul' := fun a m => ?_ }, fun _ => rfl⟩
  have h := e.map_smul (eR a) m
  change e (eR.symm (eR a) • m) = eR.symm (eR a) • e m at h
  simpa using h

/-- The morphism of finite projective modules over a fixed base given by a linear equivalence. -/
private def homOfLinearEquiv {R : ArtinianLocalAlgCat.{u, w, w} Λ k} {A B : Type t}
    [AddCommGroup A] [Module R A] [Module.Finite R A] [Module.Projective R A]
    [AddCommGroup B] [Module R B] [Module.Finite R B] [Module.Projective R B] (φ : A ≃ₗ[R] B) :
    FiniteProjectiveModule.Hom (⟨R, A⟩ : FiniteProjectiveModule.{u, w, w, t} (Λ := Λ) (k := k))
      ⟨R, B⟩ where
  base := 𝟙 R
  linear := φ.toLinearMap
  baseChange := ⟨(TensorProduct.lid R A).trans φ, fun m => by
    change φ ((1 : R) • m) = φ m
    simp⟩

/-- The morphism attached to a linear equivalence followed by the one attached to its inverse is
the identity. -/
private theorem comp_homOfLinearEquiv_symm
    (𝓖 : FiniteProjectiveModule.Family.{u, w, t} (Λ := Λ) (k := k))
    {R : ArtinianLocalAlgCat.{u, w, w} Λ k} {A B : Type t}
    [AddCommGroup A] [Module R A] [Module.Finite R A] [Module.Projective R A]
    [AddCommGroup B] [Module R B] [Module.Finite R B] [Module.Projective R B] (φ : A ≃ₗ[R] B) :
    letI := 𝓖.category
    (𝓖.homEquiv _ _).symm (homOfLinearEquiv (Λ := Λ) (k := k) φ) ≫
      (𝓖.homEquiv _ _).symm (homOfLinearEquiv (Λ := Λ) (k := k) φ.symm) =
        𝟙 (⟨R, A⟩ : FiniteProjectiveModule.{u, w, w, t} (Λ := Λ) (k := k)) := by
  let := 𝓖.category
  apply (𝓖.homEquiv _ _).injective
  apply FiniteProjectiveModule.Hom.ext_of_base_eq
  · rw [𝓖.comp_base, 𝓖.id_base]
    simp only [Equiv.apply_symm_apply]
    exact Category.id_comp _
  · intro m
    rw [𝓖.comp_linear, 𝓖.id_linear, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    exact φ.symm_apply_apply m

/-- The morphism attached to a linear equivalence is compatible with two morphisms to a common
target whenever their base morphisms agree and their linear maps are intertwined. -/
private theorem comp_eq_of_homOfLinearEquiv
    (𝓖 : FiniteProjectiveModule.Family.{u, w, t} (Λ := Λ) (k := k))
    {R : ArtinianLocalAlgCat.{u, w, w} Λ k} {A B : Type t}
    [AddCommGroup A] [Module R A] [Module.Finite R A] [Module.Projective R A]
    [AddCommGroup B] [Module R B] [Module.Finite R B] [Module.Projective R B] (φ : A ≃ₗ[R] B)
    {P : FiniteProjectiveModule.{u, w, w, t} (Λ := Λ) (k := k)}
    (a : letI := 𝓖.category; (⟨R, A⟩ : FiniteProjectiveModule.{u, w, w, t} (Λ := Λ) (k := k)) ⟶ P)
    (b : letI := 𝓖.category; (⟨R, B⟩ : FiniteProjectiveModule.{u, w, w, t} (Λ := Λ) (k := k)) ⟶ P)
    (hbase : (𝓖.homEquiv _ _ a).base = (𝓖.homEquiv _ _ b).base)
    (hlin : ∀ m, (𝓖.homEquiv _ _ b).linear (φ m) = (𝓖.homEquiv _ _ a).linear m) :
    letI := 𝓖.category
    (𝓖.homEquiv _ _).symm (homOfLinearEquiv (Λ := Λ) (k := k) φ) ≫ b = a := by
  let := 𝓖.category
  apply (𝓖.homEquiv _ _).injective
  apply FiniteProjectiveModule.Hom.ext_of_base_eq
  · rw [𝓖.comp_base]
    simp only [Equiv.apply_symm_apply]
    change (𝟙 R) ≫ _ = _
    rw [Category.id_comp]
    exact hbase.symm
  · intro m
    rw [𝓖.comp_linear, Equiv.apply_symm_apply]
    exact hlin m

/-- The projection of the morphism attached to a linear equivalence is the comparison of the
two identifications of the base. -/
private theorem projection_map_homOfLinearEquiv
    (𝓖 : FiniteProjectiveModule.Family.{u, w, t} (Λ := Λ) (k := k))
    {R : ArtinianLocalAlgCat.{u, w, w} Λ k} {A B : Type t}
    [AddCommGroup A] [Module R A] [Module.Finite R A] [Module.Projective R A]
    [AddCommGroup B] [Module R B] [Module.Finite R B] [Module.Projective R B] (φ : A ≃ₗ[R] B) :
    letI := 𝓖.category
    𝓖.projection.map ((𝓖.homEquiv _ _).symm (homOfLinearEquiv (Λ := Λ) (k := k) φ)) =
      eqToHom ((𝓖.projection_obj ⟨R, A⟩).trans (𝓖.projection_obj ⟨R, B⟩).symm) := by
  let := 𝓖.category
  apply eqToHom_of_conjugate_eq_id (𝓖.projection_obj ⟨R, A⟩) (𝓖.projection_obj ⟨R, B⟩)
  simpa [homOfLinearEquiv] using 𝓖.projection_map
    ((𝓖.homEquiv _ _).symm (homOfLinearEquiv (Λ := Λ) (k := k) φ))

/-- Any two deformations of `V` over the dual numbers are isomorphic in the slice category, by
an isomorphism whose projection to `𝒞_Λ` is the comparison of the two identifications of their
bases with the dual-number object. This is the content of the tangent space being a point. -/
private theorem exists_iso_of_base_eq_dualNumber
    (𝓖 : FiniteProjectiveModule.Family.{u, w, t} (Λ := Λ) (k := k))
    (V : Type t) [AddCommGroup V] [Module k V] [Module.Finite k V] :
    letI := 𝓖.category
    let p := objectsOverFunctor 𝓖.projection (specialFiber (Λ := Λ) (k := k) V)
    ∀ (A B : Over (specialFiber (Λ := Λ) (k := k) V))
      (hA : p.obj A = dualNumberBase Λ k) (hB : p.obj B = dualNumberBase Λ k),
      ∃ i : A ≅ B,
        p.map i.hom = eqToHom (hA.trans hB.symm) ∧
          p.map i.inv = eqToHom (hB.trans hA.symm) := by
  let := 𝓖.category
  intro p A B hA hB
  let hpoint := specialFiber (Λ := Λ) (k := k) V
  let ε := dualNumberBase Λ k
  let makeLift
      (X : FiniteProjectiveModule.{u, w, w, t} (Λ := Λ) (k := k))
      (H : FiniteProjectiveModule.Hom X hpoint) (hX : X.base = ε) :
      DualNumberLift.{w, t, t} (k := k) V := by
    cases X with
    | @mk base carrier addG srcModule srcFinite srcProjective =>
      change base = ε at hX
      subst base
      letI : AddCommGroup carrier := addG
      letI : Module (↑ε) carrier := srcModule
      letI : Module.Finite (↑ε) carrier := srcFinite
      letI : Module.Projective (↑ε) carrier := srcProjective
      letI : Algebra k (↑ε) := by
        change Algebra k (TrivSqZeroExt k (rankOneModuleCat k))
        infer_instance
      let E : (↑ε) ≃ₐ[k] DualNumber k := by
        change TrivSqZeroExt k (rankOneModuleCat k) ≃ₐ[k] DualNumber k
        exact squareZeroRankOneDualNumberEquiv k
      let eR := E.toRingEquiv
      letI : Module (DualNumber k) carrier := Module.compHom carrier eR.symm.toRingHom
      letI : RingHomInvPair eR.toRingHom eR.symm.toRingHom :=
        RingHomInvPair.of_ringEquiv eR
      letI : RingHomInvPair eR.symm.toRingHom eR.toRingHom :=
        RingHomInvPair.of_ringEquiv eR.symm
      let eM : carrier ≃ₛₗ[eR.toRingHom] carrier := by
        refine LinearEquiv.ofBijective
          ({ toFun := id
             map_add' := fun _ _ => rfl
             map_smul' := ?_ } : carrier →ₛₗ[eR.toRingHom] carrier) ?_
        · intro r m
          change r • m = eR.symm (eR r) • m
          simp
        · exact ⟨fun _ _ h => h, fun m => ⟨m, rfl⟩⟩
      letI : Module.Projective (DualNumber k) carrier := Module.Projective.of_equiv eM
      letI : Module.Finite (DualNumber k) carrier :=
        Module.Finite.of_surjective
          (eM : carrier →ₛₗ[eR.toRingHom] carrier)
          (show Function.Surjective (eM : carrier →ₛₗ[eR.toRingHom] carrier) from eM.surjective)
      have hcompat (r : DualNumber k) : H.base.hom (eR.symm r) = r.fst := by
        have h0 : H.base.hom (eR.symm r) = (eR.symm r).fst := by
          simpa using base_hom_eq_fst V H (eR.symm r)
        have h1 : (eR.symm r).fst = r.fst := by
          have hfst (s : ↑ε) : (eR s).fst = s.fst := by
            change TrivSqZeroExt.fst
              (TrivSqZeroExt.map (rankOneModuleCatEquiv k).toLinearMap s) = s.fst
            exact TrivSqZeroExt.fst_map _ _
          exact (hfst (eR.symm r)).symm.trans
            (congrArg TrivSqZeroExt.fst (eR.apply_symm_apply r))
        exact h0.trans h1
      letI : Module k hpoint.carrier := hpoint.module
      letI : Module k V := hpoint.module
      let red : carrier →ₛₗ[(TrivSqZeroExt.fstHom k k k).toRingHom] V := by
        refine {
          toFun := H.linear
          map_add' := H.linear.map_add'
          map_smul' := ?_ }
        intro r m
        change H.linear (eR.symm r • m) =
          (TrivSqZeroExt.fstHom k k k).toRingHom r • H.linear m
        calc
          H.linear ((eR.symm r) • m) =
              H.base.hom (eR.symm r) • H.linear m := H.linear.map_smulₛₗ (eR.symm r) m
          _ = r.fst • H.linear m := by rw [hcompat r]; rfl
          _ = (TrivSqZeroExt.fstHom k k k).toRingHom r • H.linear m := by
            congr 1
      refine {
        carrier := carrier
        addCommGroup := inferInstance
        module := inferInstance
        finite := inferInstance
        projective := inferInstance
        reduction := red
        baseChange := ?_ }
      let : Algebra (↑ε) (↑hpoint.base) := H.base.hom.toRingHom.toAlgebra
      let : Module (↑ε) (↑hpoint.base) :=
        Module.compHom (↑hpoint.base) H.base.hom.toRingHom
      let : Algebra (DualNumber k) k := TrivSqZeroExt.algebraBase k k
      let : Module (DualNumber k) k :=
        Module.compHom k (TrivSqZeroExt.fstHom k k k).toRingHom
      let : Algebra k (↑hpoint.base) := by
        change Algebra k k
        exact Algebra.id k
      let : Module (↑hpoint.base) V := hpoint.module
      let : Module k hpoint.carrier :=
        Module.compHom hpoint.carrier (algebraMap k (↑hpoint.base))
      let : Module k V :=
        Module.compHom V (algebraMap k (↑hpoint.base))
      obtain ⟨e₀, he₀⟩ := H.baseChange
      let eK : (↑hpoint.base) ≃ₛₗ[eR.toRingHom] k := by
        refine LinearEquiv.ofBijective
          ({ toFun := fun a => a
             map_add' := fun _ _ => rfl
             map_smul' := ?_ } :
               (↑hpoint.base) →ₛₗ[eR.toRingHom] k) ?_
        · intro a z
          change H.base.hom a • z = TrivSqZeroExt.fst (eR a) • (z : k)
          have hh : H.base.hom a = (eR a).fst := by
            simpa using hcompat (eR a)
          rw [hh]
          rfl
        · exact ⟨fun _ _ h => h, fun z => ⟨z, rfl⟩⟩
      let eT := TensorProduct.congr eK eM
      let : SMulCommClass (↑ε) k (↑hpoint.base) := ⟨by
        intro r c z
        simp [Algebra.smul_def, mul_comm, mul_left_comm, mul_assoc]⟩
      let : Module k (TensorProduct (↑ε) (↑hpoint.base) carrier) :=
        Module.compHom _ (algebraMap k (↑hpoint.base))
      let eTlin : (TensorProduct (↑ε) (↑hpoint.base) carrier) ≃ₗ[k]
          (TensorProduct (DualNumber k) k carrier) := by
        refine LinearEquiv.ofBijective
          ({ toFun := eT
             map_add' := eT.map_add
             map_smul' := ?_ } :
               TensorProduct (↑ε) (↑hpoint.base) carrier →ₗ[k]
                 TensorProduct (DualNumber k) k carrier) ?_
        · intro c z
          refine TensorProduct.inductionOn z ?_ ?_
          · intro a m
            change (eK (c • a)) ⊗ₜ[DualNumber k] (eM m) =
              c • ((eK a) ⊗ₜ[DualNumber k] (eM m))
            rw [TensorProduct.smul_tmul']
            congr 1
          · intro z₁ z₂ hz₁ hz₂
            calc
              eT (c • (z₁ + z₂)) = eT (c • z₁ + c • z₂) := by rw [smul_add]
              _ = eT (c • z₁) + eT (c • z₂) := eT.map_add _ _
              _ = c • eT z₁ + c • eT z₂ := by
                change eT (c • z₁) + eT (c • z₂) =
                  (RingHom.id k) c • eT z₁ + (RingHom.id k) c • eT z₂
                exact congrArg₂ (· + ·) hz₁ hz₂
              _ = c • (eT z₁ + eT z₂) := by
                have hadd : c • (eT z₁ + eT z₂) = c • eT z₁ + c • eT z₂ :=
                  TensorProduct.smul_add c _ _
                exact hadd.symm
              _ = c • eT (z₁ + z₂) := by rw [eT.map_add]
        · exact ⟨fun _ _ h => eT.injective h,
            fun z => ⟨eT.symm z, eT.apply_symm_apply z⟩⟩
      let e₀' : (TensorProduct (↑ε) (↑hpoint.base) carrier) ≃ₗ[k] V := by
        refine {
          toFun := e₀
          invFun := e₀.symm
          left_inv := e₀.left_inv
          right_inv := e₀.right_inv
          map_add' := e₀.map_add
          map_smul' := ?_ }
        intro c z
        change e₀ ((algebraMap k (↑hpoint.base) c) • z) =
          (algebraMap k (↑hpoint.base) c) • e₀ z
        exact e₀.map_smul _ _
      let e := eTlin.symm.trans e₀'
      refine ⟨e, ?_⟩
      intro m
      change e₀' (eTlin.symm (1 ⊗ₜ[DualNumber k] m)) = red m
      have htmul : eTlin.symm (1 ⊗ₜ[DualNumber k] m) =
          (1 : ↑hpoint.base) ⊗ₜ[↑ε] m := by
        apply eTlin.injective
        rw [eTlin.apply_symm_apply]
        change (1 : k) ⊗ₜ[DualNumber k] m =
          (eK (1 : ↑hpoint.base)) ⊗ₜ[DualNumber k] (eM m)
        rw [show eK (1 : ↑hpoint.base) = 1 by rfl, show eM m = m by rfl]
      rw [htmul]
      change e₀ ((1 : ↑hpoint.base) ⊗ₜ[↑ε] m) = H.linear m
      exact he₀ m
  have hbase (C : Over hpoint) (hC : p.obj C = ε) : C.left.base = ε := by
    change 𝓖.projection.obj C.left = ε at hC
    rwa [𝓖.projection_obj] at hC
  have hAbase := hbase A hA
  have hBbase := hbase B hB
  let arrowA := A.hom
  let arrowB := B.hom
  cases A with
  | mk leftA rightA =>
    cases leftA with
    | mk baseA carrierA =>
      change baseA = ε at hAbase
      cases hAbase.symm
      let objA : FiniteProjectiveModule.{u, w, w, t} (Λ := Λ) (k := k) := ⟨ε, carrierA⟩
      cases B with
      | mk leftB rightB =>
        cases leftB with
        | mk baseB carrierB =>
          change baseB = ε at hBbase
          cases hBbase.symm
          let objB : FiniteProjectiveModule.{u, w, w, t} (Λ := Λ) (k := k) := ⟨ε, carrierB⟩
          let hAdata := 𝓖.homEquiv objA hpoint arrowA
          let hBdata := 𝓖.homEquiv objB hpoint arrowB
          have hbaseEq : hAdata.base = hBdata.base := by
            ext r
            rw [base_hom_eq_fst V hAdata, base_hom_eq_fst V hBdata]
          let eR : (↑ε) ≃+* DualNumber k :=
            (squareZeroRankOneDualNumberEquiv k).toRingEquiv
          let liftA := makeLift objA hAdata rfl
          let liftB := makeLift objB hBdata rfl
          let : Module (DualNumber k) objA.carrier := liftA.module
          let : Module (DualNumber k) objB.carrier := liftB.module
          obtain ⟨e, he⟩ :
              ∃ e : objA.carrier ≃ₗ[DualNumber k] objB.carrier,
                ∀ m, hBdata.linear (e m) = hAdata.linear m :=
            DualNumberLift.exists_linearEquiv liftA liftB
          obtain ⟨fequiv, hfequiv⟩ : ∃ f : objA.carrier ≃ₗ[↑ε] objB.carrier, ∀ m, f m = e m :=
            exists_linearEquiv_of_compHom eR e
          have hf (m : objA.carrier) : hBdata.linear (fequiv m) = hAdata.linear m := by
            rw [hfequiv]
            exact he m
          have hg (m : objB.carrier) : hAdata.linear (fequiv.symm m) = hBdata.linear m := by
            simpa using (hf (fequiv.symm m)).symm
          let f := (𝓖.homEquiv objA objB).symm (homOfLinearEquiv (Λ := Λ) (k := k) fequiv)
          let g := (𝓖.homEquiv objB objA).symm (homOfLinearEquiv (Λ := Λ) (k := k) fequiv.symm)
          let i : Over.mk arrowA ≅ Over.mk arrowB := {
            hom := Over.homMk f (comp_eq_of_homOfLinearEquiv 𝓖 fequiv _ _ hbaseEq hf)
            inv := Over.homMk g (comp_eq_of_homOfLinearEquiv 𝓖 fequiv.symm _ _ hbaseEq.symm hg)
            hom_inv_id := by
              ext
              exact comp_homOfLinearEquiv_symm 𝓖 fequiv
            inv_hom_id := by
              ext
              exact comp_homOfLinearEquiv_symm 𝓖 fequiv.symm }
          exact ⟨i, projection_map_homOfLinearEquiv 𝓖 fequiv,
            projection_map_homOfLinearEquiv 𝓖 fequiv.symm⟩

/-- The tangent space of the deformation category of a finite-dimensional vector space has at
most one element: it is the zero vector space. -/
@[stacks 0DVQ "tangent_space_zero"]
public theorem subsingleton_tangentSpace
    (V : Type t) [AddCommGroup V] [Module k V] [Module.Finite k V] :
    let 𝓖 := FiniteProjectiveModule.family.{u, w, t} (Λ := Λ) (k := k)
    letI := 𝓖.category
    let p := objectsOverFunctor 𝓖.projection (specialFiber (Λ := Λ) (k := k) V)
    let 𝓕 := BasedCategory.ofFunctor p
    let hD := isDeformationCategory_deformationCategory (Λ := Λ) V
    let hS2 := Artin.schlessingerConditionS2_isomorphismClasses_of_isDeformationCategory 𝓕 hD
    letI : Fact (IsPredeformationCategory 𝓕.p) := ⟨hD.predeformation⟩
    letI : Fact (SchlessingerConditionS2
      (CategoryOfElements.π (isomorphismClasses 𝓕 hD.predeformation.cofibered))) := ⟨hS2⟩
    let T := artinianTangentSpace Λ k (isomorphismClasses 𝓕 hD.predeformation.cofibered)
    letI : AddCommGroup T := associatedTangentSpaceAddCommGroupUnlifted 𝓕
    letI : Module k T := associatedTangentSpaceModuleUnlifted 𝓕
    Subsingleton T := by
  classical
  let 𝓖 := FiniteProjectiveModule.family.{u, w, t} (Λ := Λ) (k := k)
  let := (FiniteProjectiveModule.family.{u, w, t} (Λ := Λ) (k := k)).category
  let p := objectsOverFunctor
    (FiniteProjectiveModule.family.{u, w, t} (Λ := Λ) (k := k)).projection
    (specialFiber (Λ := Λ) (k := k) V)
  let 𝓕 := BasedCategory.ofFunctor p
  let hD := isDeformationCategory_deformationCategory (Λ := Λ) (k := k) V
  let hS2 := Artin.schlessingerConditionS2_isomorphismClasses_of_isDeformationCategory 𝓕 hD
  let : Fact (IsPredeformationCategory 𝓕.p) := ⟨hD.predeformation⟩
  let : Fact (SchlessingerConditionS2
    (CategoryOfElements.π (isomorphismClasses 𝓕 hD.predeformation.cofibered))) := ⟨hS2⟩
  let T := artinianTangentSpace Λ k (isomorphismClasses 𝓕 hD.predeformation.cofibered)
  let : AddCommGroup T := associatedTangentSpaceAddCommGroupUnlifted 𝓕
  let : Module k T := associatedTangentSpaceModuleUnlifted 𝓕
  let ε := dualNumberBase Λ k
  have hC : IsCofiberedInGroupoids 𝓕.p := hD.predeformation.cofibered
  change Subsingleton ((isomorphismClasses 𝓕 hD.predeformation.cofibered).obj ε)
  rw [isomorphismClasses_obj 𝓕 hC ε]
  refine ⟨?_⟩
  intro q r
  refine Quotient.inductionOn₂ q r ?_
  intro x y
  apply Quotient.sound
  change Nonempty (x ≅ y)
  obtain ⟨i, hi, hi'⟩ :=
    exists_iso_of_base_eq_dualNumber 𝓖 V x.val y.val x.property y.property
  have hpx : p.obj x.val = ε := x.property
  have hpy : p.obj y.val = ε := y.property
  have hLift {a b : Over (specialFiber (Λ := Λ) (k := k) V)} (f : a ⟶ b)
      (ha : p.obj a = ε) (hb : p.obj b = ε) (h : p.map f = eqToHom (ha.trans hb.symm)) :
      p.IsHomLift (𝟙 ε) f := by
    apply IsHomLift.of_fac' p (𝟙 ε) f ha hb
    rw [h, Category.id_comp, eqToHom_trans]
  refine ⟨{
    hom := ⟨i.hom, hLift _ hpx hpy hi⟩
    inv := ⟨i.inv, hLift _ hpy hpx hi'⟩
    hom_inv_id := ?_
    inv_hom_id := ?_ }⟩
  · exact Functor.Fiber.hom_ext i.hom_inv_id
  · exact Functor.Fiber.hom_ext i.inv_hom_id

/-- The tangent space of the deformation category of a finite-dimensional vector space is
finite-dimensional, being the zero vector space. -/
@[stacks 0DVQ "tangent_space_zero"]
public theorem finiteDimensional_tangentSpace
    (V : Type t) [AddCommGroup V] [Module k V] [Module.Finite k V] :
    let 𝓖 := FiniteProjectiveModule.family.{u, w, t} (Λ := Λ) (k := k)
    letI := 𝓖.category
    let p := objectsOverFunctor 𝓖.projection (specialFiber (Λ := Λ) (k := k) V)
    let 𝓕 := BasedCategory.ofFunctor p
    let hD := isDeformationCategory_deformationCategory (Λ := Λ) V
    let hS2 := Artin.schlessingerConditionS2_isomorphismClasses_of_isDeformationCategory 𝓕 hD
    letI : Fact (IsPredeformationCategory 𝓕.p) := ⟨hD.predeformation⟩
    letI : Fact (SchlessingerConditionS2
      (CategoryOfElements.π (isomorphismClasses 𝓕 hD.predeformation.cofibered))) := ⟨hS2⟩
    let T := artinianTangentSpace Λ k (isomorphismClasses 𝓕 hD.predeformation.cofibered)
    letI : AddCommGroup T := associatedTangentSpaceAddCommGroupUnlifted 𝓕
    letI : Module k T := associatedTangentSpaceModuleUnlifted 𝓕
    FiniteDimensional k T := by
  let 𝓖 := FiniteProjectiveModule.family.{u, w, t} (Λ := Λ) (k := k)
  let := 𝓖.category
  let p := objectsOverFunctor 𝓖.projection (specialFiber (Λ := Λ) (k := k) V)
  let 𝓕 := BasedCategory.ofFunctor p
  let hD := isDeformationCategory_deformationCategory (Λ := Λ) (k := k) V
  let hS2 := Artin.schlessingerConditionS2_isomorphismClasses_of_isDeformationCategory 𝓕 hD
  let : Fact (IsPredeformationCategory 𝓕.p) := ⟨hD.predeformation⟩
  let : Fact (SchlessingerConditionS2
    (CategoryOfElements.π (isomorphismClasses 𝓕 hD.predeformation.cofibered))) := ⟨hS2⟩
  let T := artinianTangentSpace Λ k (isomorphismClasses 𝓕 hD.predeformation.cofibered)
  let : AddCommGroup T := associatedTangentSpaceAddCommGroupUnlifted 𝓕
  let : Module k T := associatedTangentSpaceModuleUnlifted 𝓕
  change FiniteDimensional k T
  let : Subsingleton T := subsingleton_tangentSpace V
  exact Module.Finite.of_finite

end Deformation.Examples.FiniteProjectiveModule
