module

public import Mathlib.Algebra.Homology.DerivedCategory.KProjective
public import Mathlib.CategoryTheory.Monoidal.Rigid.Braided
public import Mathlib.CategoryTheory.Triangulated.Adjunction
public import Mathlib.CategoryTheory.Triangulated.Generators
public import StacksFrontier.Algebra.Homology.PseudoCoherent
public import StacksFrontier.Homology.HomComplex.Composition
public import StacksFrontier.Homology.HomComplex.Currying
public import StacksFrontier.Homology.HomComplex.DerivedTensorHom
public import StacksFrontier.Homology.HomComplex.KoszulBraiding
public import StacksFrontier.Homology.HomComplex.RHom
public import StacksFrontier.Homology.HomComplex.TensorHom
public import StacksFrontier.Homology.KFlat.BaseChange
public import StacksFrontier.Homology.KFlat.Flat
public import StacksFrontier.Homology.KFlat.Resolution
public import StacksFrontier.Homology.LeftDual
public import StacksFrontier.Homology.Perfect.Defs
public import StacksFrontier.Homology.TensorComplex.Monoidal
public import StacksFrontier.Homology.Tor.DerivedTensor
public import StacksFrontier.Homology.Tor.DerivedTensorFunctorLargeUniverse
public import StacksFrontier.Homology.TorAmplitude.KFlatRepresentative
public import StacksFrontier.Homology.HomComplex.Evaluation.TensorHom.BoundedBelowCase
import StacksCore.Tactic.EgaSgaAttribute
import all StacksFrontier.Homology.HomComplex.Evaluation.TensorHom.BoundedTheta
import all StacksFrontier.Homology.HomComplex.Evaluation.TensorHom.BoundedBelowCase

/-!
# The derived tensor--Hom diagonal: perfect cases and the currying law

Let `R` be a commutative ring and let `K`, `L`, `M` be objects of the derived category `D(R)`.
This file completes the proof that the canonical derived tensor--Hom diagonal
`K ⊗ᴸ RHom(M, L) ⟶ RHom(M, K ⊗ᴸ L)` is an isomorphism when `M` is perfect, when `K` is perfect,
or when `M` is pseudo-coherent, `L` is bounded below and `K` has Tor amplitude in `[a, ∞]`, by
treating the two perfect cases. It also transposes composition of derived internal Homs through
the derived tensor--Hom adjunction.

## Main results

* `Stacks.DerivedTensorHomDiagonal.isIso_derivedTensorHomDiagonal` ([stacks 0ATK]): the derived
  tensor--Hom diagonal is invertible under any of the three hypotheses above.
* `StacksDraft.DerivedHom.DerivedInternalHom.Model.comp_curryingIso_hom` ([stacks 0A65]): the
  currying isomorphism, at an arbitrary test object, is the double transpose through the derived
  tensor--Hom adjunction composed with the reassociation of the tensor product.
* `StacksDraft.DerivedHom.DerivedInternalHom.Model.homEquiv_composition`: composition of derived
  internal Homs uncurries to evaluating twice, which identifies the coevaluation-and-compose
  diagonal with the transpose-of-evaluation diagonal.
* `Stacks.DerivedTensorHomDiagonal.isIso_derivedTensorHomDiagonal_of_relativeKFlat`: a fourth
  situation, in which `M` is pseudo-coherent, `L` is bounded below and the tensor factor is the
  base change along a ring map `A →+* R` of a bounded-below complex of `A`-modules that is
  K-flat over `A`, so that the K-flatness asked of the tensor factor is relative to `A` and no
  Tor amplitude over `R` is bounded.

## Implementation notes

The source statement is for arbitrary rings; the available symmetric derived tensor product is
formulated for commutative rings. Membership of `L` in `D⁺(R)` is expressed by the existence of a
lower cohomological bound. Tor amplitude in `[a, ∞]` is expressed by vanishing of the homology of
`K ⊗ᴸ N[0]` in degrees below `a` for every module `N`, the derived tensor product being the
canonical one of [stacks 0BYI].

## References

* [Stacks Project, Tag 0ATK](https://stacks.math.columbia.edu/tag/0ATK)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory Pretriangulated ZeroObject

attribute [local instance] HasDerivedCategory.standard

universe u v w w'

set_option maxRecDepth 4096
set_option synthInstance.maxHeartbeats 200000

namespace Stacks.DerivedTensorHomDiagonal

open StacksDraft.DerivedHom

variable {R : Type u} [CommRing R]

open CochainComplex HomComplex HomologicalComplex TensorProduct

section PerfectComplexes

set_option backward.isDefEq.respectTransparency false

/-- The explicit tensor–Hom diagonal is the transpose of evaluation after associating. -/
private theorem theta_eq_tensorHomStrength (K L M : CochainComplex (ModuleCat R) ℤ) :
    Stacks.HomComplex.TensorHomComparison.theta K L M = tensorHomStrength (chainTensorHomAdjunction
      M) K L := by
  apply (chainTensorHomEquiv (K ⊗ HomComplexR R M L) M (K ⊗ L)).injective
  rw [transpose_theta]
  dsimp only [tensorHomStrength]
  rw [chainTensorHomAdjunction, Adjunction.mkOfHomEquiv_homEquiv]
  show _ = chainTensorHomEquiv _ _ _ ((chainTensorHomEquiv _ _ _).symm
    ((α_ K (HomComplexR R M L) M).hom ≫
      K ◁ chainTensorHomEquiv (HomComplexR R M L) M L (𝟙 _)))
  rw [Equiv.apply_symm_apply]

/-- A bounded finite-projective complex has a bounded projective left dual. -/
private theorem exists_exactPairing_of_perfect (K : CochainComplex (ModuleCat R) ℤ) (a b : ℤ)
    [K.IsStrictlyGE a] [K.IsStrictlyLE b]
    [∀ i, Module.Finite R (K.X i)] [∀ i, Module.Projective R (K.X i)] :
    ∃ (N : CochainComplex (ModuleCat R) ℤ) (_ : ExactPairing K N),
      (∃ d, N.IsStrictlyLE d) ∧ ∀ i, Module.Projective R (N.X i) := by
  obtain ⟨N, p, hN⟩ := (CochainComplex.LeftDual.exactPairing_iff_bounded_finiteProjective R).2 K
    ⟨a, b, inferInstance, inferInstance⟩ (fun _ ↦ ⟨inferInstance, inferInstance⟩)
  obtain ⟨_, ⟨c, d, hNc, hNd⟩, _, hN, _⟩ :=
    (CochainComplex.LeftDual.exactPairing_iff_bounded_finiteProjective R).1 K N p
  exact ⟨N, p, ⟨d, hNd⟩, fun i ↦ (hN i).2⟩

/-- A bounded finite-projective Hom source makes the chain diagonal invertible. -/
private theorem isIso_theta_of_perfect_source
    (K L M : CochainComplex (ModuleCat R) ℤ) (a b : ℤ)
    [M.IsStrictlyGE a] [M.IsStrictlyLE b]
    [∀ i, Module.Finite R (M.X i)] [∀ i, Module.Projective R (M.X i)] :
    IsIso (Stacks.HomComplex.TensorHomComparison.theta K L M) := by
  obtain ⟨N, p, -⟩ := exists_exactPairing_of_perfect M a b
  let := p
  rw [theta_eq_tensorHomStrength]
  exact isIso_tensorHomStrength_of_source_dual (N := N) (chainTensorHomAdjunction M) K L

/-- A bounded finite-projective tensor factor makes the chain diagonal invertible. -/
private theorem isIso_theta_of_perfect_tensor
    (K L M : CochainComplex (ModuleCat R) ℤ) (a b : ℤ)
    [K.IsStrictlyGE a] [K.IsStrictlyLE b]
    [∀ i, Module.Finite R (K.X i)] [∀ i, Module.Projective R (K.X i)] :
    IsIso (Stacks.HomComplex.TensorHomComparison.theta K L M) := by
  obtain ⟨N, p, -⟩ := exists_exactPairing_of_perfect K a b
  let := p
  rw [theta_eq_tensorHomStrength]
  exact isIso_tensorHomStrength_of_tensor_dual (N := N) (chainTensorHomAdjunction M) L

/-- Tensoring a K-injective complex by a bounded finite-projective complex preserves
K-injectivity. -/
private theorem isKInjective_tensor_of_perfect
    (K I : CochainComplex (ModuleCat R) ℤ) (a b : ℤ)
    [K.IsStrictlyGE a] [K.IsStrictlyLE b]
    [∀ i, Module.Finite R (K.X i)] [∀ i, Module.Projective R (K.X i)]
    [I.IsKInjective] : (K ⊗ I).IsKInjective := by
  obtain ⟨N, p, ⟨d, hNd⟩, hN⟩ := exists_exactPairing_of_perfect K a b
  let := p
  let := CochainComplex.Koszul.koszulSymmetric R
  let := BraidedCategory.exactPairing_swap K N
  let := hNd
  let := hN
  have hNf : N.KFlat := CochainComplex.KFlat.kFlat_of_flat N d
  have := StacksDraft.DerivedHom.homComplex_isKInjective_of_kFlat N I hNf
  let e : K ⊗ I ≅ HomComplexR R N I := (β_ K I) ≪≫
    ((tensorRightAdjunction N K).rightAdjointUniq (chainTensorHomAdjunction N)).app I
  exact CochainComplex.isKInjective_of_iso e.symm

/-- Every derived object has a K-flat representative. -/
private theorem exists_kFlat_model [HasDerivedCategory (ModuleCat R)]
    (X : DerivedCategory (ModuleCat R)) :
    ∃ E : CochainComplex (ModuleCat R) ℤ, E.KFlat ∧ Nonempty (X ≅ DerivedCategory.Q.obj E) := by
  obtain ⟨E, f, hE, _, hf, _⟩ :=
    CochainComplex.KFlat.exists_kFlat_resolution (DerivedCategory.Q.objPreimage X)
  have := hf
  exact ⟨E, hE, ⟨(asIso (DerivedCategory.Q.map f) ≪≫
    DerivedCategory.Q.objObjPreimageIso X).symm⟩⟩

/-- Perfectness of the Hom source makes the canonical derived diagonal invertible. -/
private theorem isIso_diagonal_of_perfect_source
    (K L M : DerivedCategory (ModuleCat R)) (hM : StacksDraft.Perfect.IsPerfect M) :
    IsIso (DerivedInternalHom.Model.diagonal K L M) := by
  obtain ⟨P, a, b, hPa, hPb, hPf, hPp, ⟨eM⟩⟩ := hM
  obtain ⟨E, hE, ⟨eK⟩⟩ := exists_kFlat_model K
  let F := DerivedCategory.Q.objPreimage L
  let := hPa
  let := hPb
  let := hPf
  let := hPp
  have := isIso_theta_of_perfect_source E F P a b
  have := isIso_diagonal_of_projective_quasiIso_theta E F P b hE
  exact isIso_diagonal_of_iso eK (DerivedCategory.Q.objObjPreimageIso L).symm eM

/-- A chain isomorphism computes the derived diagonal on K-flat source representatives
and K-injective target representatives. -/
private theorem isIso_diagonal_of_injective_theta
    (K I M : CochainComplex (ModuleCat R) ℤ) (hK : K.KFlat) (hM : M.KFlat)
    [I.IsKInjective] [(K ⊗ I).IsKInjective] [IsIso (Stacks.HomComplex.TensorHomComparison.theta K I
      M)] :
    IsIso (DerivedInternalHom.Model.diagonal (DerivedCategory.Q.obj K)
      (DerivedCategory.Q.obj I) (DerivedCategory.Q.obj M)) := by
  let T := DerivedInternalHom.Model.tensor R
  let H := DerivedInternalHom.Model.hom R
  let D := DerivedInternalHom.Model.adjunction R
  let e := DerivedInternalHom.Model.tensorLeftIso K I hK
  have : IsIso (𝟙 (Opposite.op (DerivedCategory.Q.obj M)),
      e.hom ≫ DerivedCategory.Q.map (𝟙 (K ⊗ I))) :=
    (isIso_prod_iff _ _).2 ⟨inferInstance, inferInstance⟩
  have : IsIso (𝟙 (DerivedCategory.Q.obj K), (D.homIso M I).hom) :=
    (isIso_prod_iff _ _).2 ⟨inferInstance, inferInstance⟩
  have hc := DerivedInternalHom.Model.diagonal_injective_model K I M (K ⊗ I) hK hM (𝟙 _)
  rw [DerivedInternalHom.Model.postcomp_id, Category.comp_id] at hc
  have : IsIso (DerivedInternalHom.Model.diagonal (DerivedCategory.Q.obj K)
      (DerivedCategory.Q.obj I) (DerivedCategory.Q.obj M) ≫
      H.map (show (Opposite.op (DerivedCategory.Q.obj M),
          T.obj (DerivedCategory.Q.obj K, DerivedCategory.Q.obj I)) ⟶
            (Opposite.op (DerivedCategory.Q.obj M), DerivedCategory.Q.obj (K ⊗ I)) from
        (𝟙 (Opposite.op (DerivedCategory.Q.obj M)),
          e.hom ≫ DerivedCategory.Q.map (𝟙 (K ⊗ I))))) := by
    rw [hc]
    infer_instance
  exact IsIso.of_isIso_comp_right _
    (H.map (show (Opposite.op (DerivedCategory.Q.obj M),
        T.obj (DerivedCategory.Q.obj K, DerivedCategory.Q.obj I)) ⟶
          (Opposite.op (DerivedCategory.Q.obj M), DerivedCategory.Q.obj (K ⊗ I)) from
      (𝟙 (Opposite.op (DerivedCategory.Q.obj M)),
        e.hom ≫ DerivedCategory.Q.map (𝟙 (K ⊗ I)))))

/-- Perfectness of the tensor factor makes the canonical derived diagonal invertible. -/
private theorem isIso_diagonal_of_perfect_tensor
    (K L M : DerivedCategory (ModuleCat R)) (hK : StacksDraft.Perfect.IsPerfect K) :
    IsIso (DerivedInternalHom.Model.diagonal K L M) := by
  obtain ⟨E, a, b, hEa, hEb, hEf, hEp, ⟨eK⟩⟩ := hK
  obtain ⟨P, hP, ⟨eM⟩⟩ := exists_kFlat_model M
  obtain ⟨I, f, hf, hI⟩ :=
    CochainComplex.exists_quasiIso_isKInjective (DerivedCategory.Q.objPreimage L)
  have := hf
  let := hI
  let := hEa
  let := hEb
  let := hEf
  let := hEp
  have hE : E.KFlat := CochainComplex.KFlat.kFlat_of_flat E b
  have := isKInjective_tensor_of_perfect E I a b
  have := isIso_theta_of_perfect_tensor E I P a b
  have := isIso_diagonal_of_injective_theta E I P hE hP
  exact isIso_diagonal_of_iso eK
    ((DerivedCategory.Q.objObjPreimageIso L).symm ≪≫ asIso (DerivedCategory.Q.map f)) eM

end PerfectComplexes

/-! ### A relative K-flat tensor factor

The Tor-amplitude hypothesis of the third case is used for one purpose only: to produce a
representative of the tensor factor that is at once K-flat and bounded below. A tensor factor
may admit no such representative over `R` and still be a base change: if `φ : A →+* R` is a ring
map and `K` is represented by `R ⊗_A P` for a complex `P` of `A`-modules which is bounded below
and K-flat *over `A`*, then `R ⊗_A P` is bounded below, and K-flat over `R` by [stacks 06Y1].
The conjunction is therefore available again, and the third case applies with the K-flatness
demanded only relative to `A`. -/

section RelativeKFlat

/-- Extension of scalars along a ring map preserves a strict lower bound on a complex, being
applied degreewise by an additive functor. -/
public theorem isStrictlyGE_extendScalars {A : Type u} [CommRing A]
    (φ : A →+* R) (P : CochainComplex (ModuleCat.{u} A) ℤ) (a : ℤ) [P.IsStrictlyGE a] :
    ((CochainComplex.extendScalars φ).obj P).IsStrictlyGE a :=
  inferInstanceAs (CochainComplex.IsStrictlyGE
    (((ModuleCat.extendScalars φ).mapHomologicalComplex (ComplexShape.up ℤ)).obj P) a)

/-- The canonical derived tensor--Hom diagonal `K ⊗ᴸ RHom(M, L) ⟶ RHom(M, K ⊗ᴸ L)` is an
isomorphism when `M` is pseudo-coherent, `L` is bounded below, and the tensor factor `K` is the
base change along a ring map `φ : A →+* R` of a complex of `A`-modules that is bounded below and
K-flat over `A`.

This is a fourth situation alongside the three of `isIso_derivedTensorHomDiagonal`: the
K-flatness required of the tensor factor is relative to `A`, and no bound on the Tor amplitude
of `K` over `R` is assumed. Relative K-flatness of a base change is genuinely weaker as a
hypothesis to verify, but not as a mathematical condition: a bounded-below complex that is
K-flat over `A` has a base change which is bounded below and K-flat over `R`, so `K` does in
fact have Tor amplitude in `[a, ∞]` over `R`. The hypothesis cannot be weakened to `K` merely
having a bounded representative over `R` whose terms are flat over `A`, which is the relative
perfectness of [stacks 0DHV]: for `A` a field `k`, `R = k[x]/(x²)` and `K = L = M = k` all
hypotheses of that form hold, while the two sides of the diagonal have cohomology `k^{(ℕ)}` and
`k^ℕ` in every degree. -/
public theorem isIso_derivedTensorHomDiagonal_of_relativeKFlat
    {A : Type u} [CommRing A] (φ : A →+* R)
    (K L M : DerivedCategory (ModuleCat.{u} R)) (a : ℤ)
    (hK : ∃ P : CochainComplex (ModuleCat.{u} A) ℤ, P.IsStrictlyGE a ∧ P.KFlat ∧
      Nonempty (K ≅ DerivedCategory.Q.obj ((CochainComplex.extendScalars φ).obj P)))
    (hM : StacksDraft.PseudoCoherence.IsPseudoCoherent M)
    (hL : ∃ b : ℤ, DerivedCategory.IsGE L b) :
    IsIso (StacksDraft.DerivedHom.derivedTensorHomDiagonal K L M) := by
  obtain ⟨P, hPa, hP, ⟨eK⟩⟩ := hK
  obtain ⟨b, hb⟩ := hL
  have := hb
  obtain ⟨F, hFb, ⟨eL⟩⟩ := DerivedCategory.exists_iso_Q_obj_of_isGE L b
  obtain ⟨N, hN, ⟨eM⟩⟩ := hM
  obtain ⟨d, hNd⟩ := hN.upperBound
  have := hPa
  have := hFb
  have := hNd
  have : ∀ i, Module.Finite R (N.X i) := fun i ↦ (hN.finiteFree i).1
  have : ∀ i, Module.Free R (N.X i) := fun i ↦ (hN.finiteFree i).2
  have : ∀ i, Projective (N.X i) := fun i ↦ ModuleCat.projective_of_categoryTheory_projective _
  have := isStrictlyGE_extendScalars φ P a
  have := isIso_theta_of_boundedBelow ((CochainComplex.extendScalars φ).obj P) F N a b d
  have := isIso_diagonal_of_projective_quasiIso_theta ((CochainComplex.extendScalars φ).obj P)
    F N d (kFlat_baseChange φ P hP)
  exact isIso_diagonal_of_iso eK eL eM.symm

end RelativeKFlat

/-- **Stacks 0ATK.** The canonical derived tensor--Hom diagonal
`K ⊗ᴸ RHom(M, L) ⟶ RHom(M, K ⊗ᴸ L)` is an isomorphism if `M` is perfect, if `K` is perfect, or
if `M` is pseudo-coherent, `L` is bounded below and `K` has Tor amplitude in `[a, ∞]`. -/
@[stacks 0ATK, sga "6 I 7.6" "affine case, E perfect"]
public theorem isIso_derivedTensorHomDiagonal
    {R : Type u} [CommRing R]
    (K L M : DerivedCategory (ModuleCat.{u} R)) (a : ℤ)
    (h : StacksDraft.Perfect.IsPerfect M ∨ StacksDraft.Perfect.IsPerfect K ∨
      (StacksDraft.PseudoCoherence.IsPseudoCoherent M ∧
        (∃ b : ℤ, DerivedCategory.IsGE L b) ∧
        ∀ (N : ModuleCat.{u} R) (i : ℤ), i < a →
          IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).obj
            ((((CochainComplex.DerivedTensor.canonicalDerivedTensorProduct R).tensor.obj K).obj
              ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj N)))))) :
    IsIso (StacksDraft.DerivedHom.derivedTensorHomDiagonal K L M) := by
  rcases h with hM | hK | ⟨hM, ⟨b, hb⟩, hK⟩
  · exact isIso_diagonal_of_perfect_source K L M hM
  · exact isIso_diagonal_of_perfect_tensor K L M hK
  · let := hb
    exact isIso_diagonal_of_boundedBelow K L M a b hM hK

end Stacks.DerivedTensorHomDiagonal

/-! ### Transposing composition of derived internal Homs

The canonical currying isomorphism of Tag 0A65 is pinned down on K-flat/K-injective
representatives and, on degree-zero cohomology, by the derived tensor--Hom adjunction. Neither
description transposes `DerivedInternalHom.Model.composition` through the adjunction, which
needs the currying law at an *arbitrary* test object: the statement that, for every `X`, the
double transpose of `X ⟶ RHom(K, RHom(L, M))` agrees with the transpose of its currying
`X ⟶ RHom(K ⊗ᴸ L, M)` after reassociating the tensor product. That law is proved here by
computing both of its sides on representatives, where currying is the Hom-complex currying map
of Tag 0A5Y and the derived associator is the associator of complexes, and then transporting
the resulting equation along isomorphisms in each of its four variables.

The consequence recorded for later use is `DerivedInternalHom.Model.homEquiv_composition`:
composition of derived internal Homs uncurries to evaluating twice. It identifies the
coevaluation-and-compose diagonal of Tag 0BYN with the transpose-of-evaluation diagonal used by
the base-change criterion of Tag 0E2A. -/

namespace StacksDraft.DerivedHom

namespace DerivedInternalHom.Model

open CochainComplex CochainComplex.HomComplex HomologicalComplex

section CurryingLaw

variable {R : Type u} [CommRing R]

/-! #### The chain-level coherence -/

private lemma uncurry_uncurry {X K L M : CochainComplex (ModuleCat R) ℤ}
    (g : X ⟶ HomComplexR R K (HomComplexR R L M)) :
    uncurry (uncurry g) =
      (α_ X K L).hom ≫ uncurry (g ≫ (Stacks.HomComplex.Currying.curryIso K L M).hom) := by
  ext n : 1
  apply GradedObject.Monoidal.tensorObj₃'_ext
  intro p q r h
  rw [GradedObject.Monoidal.ιTensorObj₃'_eq _ _ _ p q r n h (p + q) rfl]
  show (ιTensorObj X K p q (p + q) rfl ▷ L.X r) ≫
      ιTensorObj (X ⊗ K) L (p + q) r n h ≫ (uncurry (uncurry g)).f n =
    (ιTensorObj X K p q (p + q) rfl ▷ L.X r) ≫
      ιTensorObj (X ⊗ K) L (p + q) r n h ≫
        ((α_ X K L).hom.f n ≫
          (uncurry (g ≫ (Stacks.HomComplex.Currying.curryIso K L M).hom)).f n)
  rw [reassoc_of% (CochainComplex.LeftDual.ι_associator_hom X K L
    p q r (p + q) (q + r) n rfl rfl h)]
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro z y
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => simpa [TensorProduct.add_tmul] using congrArg₂ (· + ·) ha hb
  | tmul x κ =>
    show (uncurry (uncurry g)).f n
        ((ιTensorObj (X ⊗ K) L (p + q) r n h).hom
          ((ιTensorObj X K p q (p + q) rfl).hom (x ⊗ₜ[R] κ) ⊗ₜ[R] y)) =
      (uncurry (g ≫ (Stacks.HomComplex.Currying.curryIso K L M).hom)).f n
        ((ιTensorObj X (K ⊗ L) p (q + r) n (by omega)).hom
          (x ⊗ₜ[R] (ιTensorObj K L q r (q + r) rfl).hom (κ ⊗ₜ[R] y)))
    rw [uncurry_apply, uncurry_apply, uncurry_apply]
    exact (CochainComplex.LeftDual.curryIso_hom_apply_degree K L M
      p q r (q + r) n (p + q) rfl (by omega) (by omega) ((g.f p).hom x) κ y).symm

variable [HasDerivedCategory (ModuleCat R)]

/-- Currying transposed through the adjunction at the test object `X`. -/
private def CurryingLawFor {X K L M : DerivedCategory (ModuleCat R)}
    (χ : X ⟶ (adjunction R).hom.obj (Opposite.op K,
      (adjunction R).hom.obj (Opposite.op L, M))) : Prop :=
  (adjunction R).homEquiv ((adjunction R).tensor.obj (X, K)) L M
      ((adjunction R).homEquiv X K ((adjunction R).hom.obj (Opposite.op L, M)) χ) =
    ((adjunction R).tensorAssoc X K L).hom ≫
      (adjunction R).homEquiv X ((adjunction R).tensor.obj (K, L)) M
        (χ ≫ (curryingIso K L M).hom)

/-- The currying law at every test object. -/
private def CurryingLawAt (X K L M : DerivedCategory (ModuleCat R)) : Prop :=
  ∀ χ : X ⟶ (adjunction R).hom.obj (Opposite.op K,
    (adjunction R).hom.obj (Opposite.op L, M)), CurryingLawFor χ

private lemma CurryingLawFor.comp {X X' K L M : DerivedCategory (ModuleCat R)} (f : X ⟶ X')
    {χ : X' ⟶ (adjunction R).hom.obj (Opposite.op K,
      (adjunction R).hom.obj (Opposite.op L, M))}
    (h : CurryingLawFor χ) : CurryingLawFor (f ≫ χ) := by
  dsimp only [CurryingLawFor] at h ⊢
  rw [Category.assoc,
    (adjunction R).homEquiv_naturality_left f (χ ≫ (curryingIso K L M).hom),
    (adjunction R).homEquiv_naturality_left f χ,
    (adjunction R).homEquiv_naturality_left
      ((adjunction R).tensor.map (show (X, K) ⟶ (X', K) from (f, 𝟙 K)))
      ((adjunction R).homEquiv X' K ((adjunction R).hom.obj (Opposite.op L, M)) χ),
    h, ← Category.assoc, (adjunction R).tensorAssoc_naturality,
    (adjunction R).tensor_map_id, Category.assoc]

private lemma CurryingLawAt.ofIsoTest {X X' K L M : DerivedCategory (ModuleCat R)}
    (e : X ≅ X') (h : CurryingLawAt X' K L M) : CurryingLawAt X K L M := by
  intro χ
  have h' := (h (e.inv ≫ χ)).comp e.hom
  simpa only [← Category.assoc, e.hom_inv_id, Category.id_comp] using h'

private lemma CurryingLawAt.ofIsoFirst {X K K' L M : DerivedCategory (ModuleCat R)}
    (e : K ≅ K') (h : CurryingLawAt X K' L M) : CurryingLawAt X K L M := by
  intro χ
  have h' := h (χ ≫ (adjunction R).hom.map
    (show (Opposite.op K, (adjunction R).hom.obj (Opposite.op L, M)) ⟶
        (Opposite.op K', (adjunction R).hom.obj (Opposite.op L, M)) from
      (e.inv.op, 𝟙 ((adjunction R).hom.obj (Opposite.op L, M)))))
  dsimp only [CurryingLawFor] at h' ⊢
  rw [(adjunction R).homEquiv_dinaturality e.inv χ,
    (adjunction R).homEquiv_naturality_left _
      ((adjunction R).homEquiv X K ((adjunction R).hom.obj (Opposite.op L, M)) χ),
    Category.assoc,
    (StacksDraft.DerivedHom.derivedHomCurrying (R := R)).naturality_left e.inv,
    ← Category.assoc,
    (adjunction R).homEquiv_dinaturality _ (χ ≫ (curryingIso K L M).hom)] at h'
  refine (cancel_epi ((adjunction R).tensor.mapIso
    (((adjunction R).tensor.mapIso ((Iso.refl X).prod e.symm)).prod (Iso.refl L))).hom).mp ?_
  simp only [Functor.mapIso_hom, Iso.prod_hom, Iso.refl_hom, Iso.symm_hom, Prod.mkHom]
  rw [h', (adjunction R).tensorAssoc_naturality_assoc]

private lemma CurryingLawAt.ofIsoSecond {X K L L' M : DerivedCategory (ModuleCat R)}
    (e : L ≅ L') (h : CurryingLawAt X K L' M) : CurryingLawAt X K L M := by
  intro χ
  have h' := h (χ ≫ (adjunction R).hom.map
    (show (Opposite.op K, (adjunction R).hom.obj (Opposite.op L, M)) ⟶
        (Opposite.op K, (adjunction R).hom.obj (Opposite.op L', M)) from
      (𝟙 (Opposite.op K), (adjunction R).hom.map
        (show (Opposite.op L, M) ⟶ (Opposite.op L', M) from (e.inv.op, 𝟙 M)))))
  dsimp only [CurryingLawFor] at h' ⊢
  rw [(adjunction R).homEquiv_naturality_right
      ((adjunction R).hom.map (show (Opposite.op L, M) ⟶ (Opposite.op L', M) from
        (e.inv.op, 𝟙 M))) χ,
    (adjunction R).homEquiv_dinaturality e.inv
      ((adjunction R).homEquiv X K ((adjunction R).hom.obj (Opposite.op L, M)) χ),
    Category.assoc,
    (StacksDraft.DerivedHom.derivedHomCurrying (R := R)).naturality_middle e.inv,
    ← Category.assoc,
    (adjunction R).homEquiv_dinaturality _ (χ ≫ (curryingIso K L M).hom)] at h'
  refine (cancel_epi ((adjunction R).tensor.mapIso
    ((Iso.refl ((adjunction R).tensor.obj (X, K))).prod e.symm)).hom).mp ?_
  simp only [Functor.mapIso_hom, Iso.prod_hom, Iso.refl_hom, Iso.symm_hom, Prod.mkHom]
  rw [h', ← (adjunction R).tensor_map_id X K,
    (adjunction R).tensorAssoc_naturality_assoc]

private lemma CurryingLawAt.ofIsoTarget {X K L M M' : DerivedCategory (ModuleCat R)}
    (e : M ≅ M') (h : CurryingLawAt X K L M') : CurryingLawAt X K L M := by
  intro χ
  have h' := h (χ ≫ (adjunction R).hom.map
    (𝟙 (Opposite.op K), (adjunction R).hom.map (𝟙 (Opposite.op L), e.hom)))
  dsimp only [CurryingLawFor] at h' ⊢
  rw [(adjunction R).homEquiv_naturality_right
      ((adjunction R).hom.map ((𝟙 (Opposite.op L), e.hom) :
        (Opposite.op L, M) ⟶ (Opposite.op L, M'))) χ,
    (adjunction R).homEquiv_naturality_right e.hom
      ((adjunction R).homEquiv X K ((adjunction R).hom.obj (Opposite.op L, M)) χ),
    Category.assoc,
    (StacksDraft.DerivedHom.derivedHomCurrying (R := R)).naturality_right e.hom,
    ← Category.assoc,
    (adjunction R).homEquiv_naturality_right e.hom
      (χ ≫ (curryingIso K L M).hom)] at h'
  rw [← cancel_mono e.hom, h', Category.assoc]

/-! #### Two cancellations of the internal-Hom bifunctor on a pair -/

private lemma hom_map_op_comp' {A A' : DerivedCategory (ModuleCat R)} (ε : A ≅ A')
    (N : DerivedCategory (ModuleCat R)) :
    (adjunction R).hom.map (show (Opposite.op A, N) ⟶ (Opposite.op A', N) from
        (ε.inv.op, 𝟙 N)) ≫
      (adjunction R).hom.map (show (Opposite.op A', N) ⟶ (Opposite.op A, N) from
        (ε.hom.op, 𝟙 N)) = 𝟙 ((adjunction R).hom.obj (Opposite.op A, N)) := by
  rw [← Functor.map_comp]
  convert (adjunction R).hom.map_id (Opposite.op A, N) using 2
  simp only [Prod.mkHom, prod_comp, ← op_comp, Iso.hom_inv_id, op_id, Category.comp_id]
  rfl

private lemma hom_map_snd_comp (A : DerivedCategory (ModuleCat R))
    {N N' : DerivedCategory (ModuleCat R)} (ε : N ≅ N') :
    (adjunction R).hom.map (show (Opposite.op A, N) ⟶ (Opposite.op A, N') from
        (𝟙 (Opposite.op A), ε.hom)) ≫
      (adjunction R).hom.map (show (Opposite.op A, N') ⟶ (Opposite.op A, N) from
        (𝟙 (Opposite.op A), ε.inv)) = 𝟙 ((adjunction R).hom.obj (Opposite.op A, N)) := by
  rw [← Functor.map_comp]
  convert (adjunction R).hom.map_id (Opposite.op A, N) using 2
  simp only [Prod.mkHom, prod_comp, Iso.hom_inv_id, Category.comp_id]
  rfl

/-! #### The law on representatives -/

private lemma curryingLawAt_models (X K L M : CochainComplex (ModuleCat R) ℤ)
    (hX : X.KFlat) (hK : K.KFlat) (hL : L.KFlat) [M.IsKInjective] :
    CurryingLawAt (DerivedCategory.Q.obj X) (DerivedCategory.Q.obj K)
      (DerivedCategory.Q.obj L) (DerivedCategory.Q.obj M) := by
  have hI₁ : (HomComplexR R L M).IsKInjective :=
    StacksDraft.DerivedHom.homComplex_isKInjective_of_kFlat L M hL
  have hI₂ : (HomComplexR R K (HomComplexR R L M)).IsKInjective :=
    StacksDraft.DerivedHom.homComplex_isKInjective_of_kFlat K (HomComplexR R L M) hK
  have hKL : (K ⊗ L).KFlat := CochainComplex.KFlat.tensor R K L hK hL
  intro χ
  dsimp only [CurryingLawFor]
  obtain ⟨g, hg⟩ := Construction.Q_map_surjective_of_isKInjective X
    (HomComplexR R K (HomComplexR R L M))
    (χ ≫ (adjunction R).hom.map
        (show (Opposite.op (DerivedCategory.Q.obj K),
            (adjunction R).hom.obj (Opposite.op (DerivedCategory.Q.obj L),
              DerivedCategory.Q.obj M)) ⟶
          (Opposite.op (DerivedCategory.Q.obj K),
            DerivedCategory.Q.obj (HomComplexR R L M)) from
          (𝟙 (Opposite.op (DerivedCategory.Q.obj K)), ((adjunction R).homIso L M).hom)) ≫
      ((adjunction R).homIso K (HomComplexR R L M)).hom)
  have hχ : χ = DerivedCategory.Q.map g ≫
      ((adjunction R).homIso K (HomComplexR R L M)).inv ≫
      (adjunction R).hom.map
        (show (Opposite.op (DerivedCategory.Q.obj K),
            DerivedCategory.Q.obj (HomComplexR R L M)) ⟶
          (Opposite.op (DerivedCategory.Q.obj K),
            (adjunction R).hom.obj (Opposite.op (DerivedCategory.Q.obj L),
              DerivedCategory.Q.obj M)) from
          (𝟙 (Opposite.op (DerivedCategory.Q.obj K)), ((adjunction R).homIso L M).inv)) := by
    rw [hg]
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    rw [hom_map_snd_comp (DerivedCategory.Q.obj K) ((adjunction R).homIso L M),
      Category.comp_id]
  have hinner : (adjunction R).homEquiv (DerivedCategory.Q.obj X) (DerivedCategory.Q.obj K)
        ((adjunction R).hom.obj (Opposite.op (DerivedCategory.Q.obj L),
          DerivedCategory.Q.obj M)) χ =
      ((adjunction R).tensorIso X K hK).hom ≫ DerivedCategory.Q.map (uncurry g) ≫
        ((adjunction R).homIso L M).inv := by
    rw [hχ, ← Category.assoc,
      (adjunction R).homEquiv_naturality_right ((adjunction R).homIso L M).inv
        (DerivedCategory.Q.map g ≫ ((adjunction R).homIso K (HomComplexR R L M)).inv),
      homEquiv_map_uncurry X K (HomComplexR R L M) hK g, Category.assoc]
  have hLHS : (adjunction R).homEquiv
        ((adjunction R).tensor.obj (DerivedCategory.Q.obj X, DerivedCategory.Q.obj K))
        (DerivedCategory.Q.obj L) (DerivedCategory.Q.obj M)
        ((adjunction R).homEquiv (DerivedCategory.Q.obj X) (DerivedCategory.Q.obj K)
          ((adjunction R).hom.obj (Opposite.op (DerivedCategory.Q.obj L),
            DerivedCategory.Q.obj M)) χ) =
      (adjunction R).tensor.map
          (show ((adjunction R).tensor.obj (DerivedCategory.Q.obj X,
              DerivedCategory.Q.obj K), DerivedCategory.Q.obj L) ⟶
            (DerivedCategory.Q.obj (X ⊗ K), DerivedCategory.Q.obj L) from
            (((adjunction R).tensorIso X K hK).hom, 𝟙 (DerivedCategory.Q.obj L))) ≫
        ((adjunction R).tensorIso (X ⊗ K) L hL).hom ≫
        DerivedCategory.Q.map (uncurry (uncurry g)) := by
    rw [hinner, (adjunction R).homEquiv_naturality_left
        (((adjunction R).tensorIso X K hK).hom)
        (DerivedCategory.Q.map (uncurry g) ≫ ((adjunction R).homIso L M).inv),
      homEquiv_map_uncurry (X ⊗ K) L M hL (uncurry g)]
  have key := currying_inv_comparison K L M hL
  have hstar : (curryingIso (DerivedCategory.Q.obj K) (DerivedCategory.Q.obj L)
          (DerivedCategory.Q.obj M)).hom ≫
        (adjunction R).hom.map
          (show (Opposite.op ((adjunction R).tensor.obj (DerivedCategory.Q.obj K,
              DerivedCategory.Q.obj L)), DerivedCategory.Q.obj M) ⟶
            (Opposite.op (DerivedCategory.Q.obj (K ⊗ L)), DerivedCategory.Q.obj M) from
            ((((adjunction R).tensorIso K L hL).inv).op, 𝟙 (DerivedCategory.Q.obj M))) ≫
        ((adjunction R).homIso (K ⊗ L) M).hom =
      (adjunction R).hom.map
          (show (Opposite.op (DerivedCategory.Q.obj K),
              (adjunction R).hom.obj (Opposite.op (DerivedCategory.Q.obj L),
                DerivedCategory.Q.obj M)) ⟶
            (Opposite.op (DerivedCategory.Q.obj K),
              DerivedCategory.Q.obj (HomComplexR R L M)) from
            (𝟙 (Opposite.op (DerivedCategory.Q.obj K)), ((adjunction R).homIso L M).hom)) ≫
        ((adjunction R).homIso K (HomComplexR R L M)).hom ≫
        DerivedCategory.Q.map (Stacks.HomComplex.Currying.curryIso K L M).hom := by
    rw [← key]
    rw [reassoc_of% (hom_map_op_comp' ((adjunction R).tensorIso K L hL)
      (DerivedCategory.Q.obj M)), Iso.hom_inv_id_assoc]
  have hc : (curryingIso (DerivedCategory.Q.obj K) (DerivedCategory.Q.obj L)
        (DerivedCategory.Q.obj M)).hom =
      (adjunction R).hom.map
          (show (Opposite.op (DerivedCategory.Q.obj K),
              (adjunction R).hom.obj (Opposite.op (DerivedCategory.Q.obj L),
                DerivedCategory.Q.obj M)) ⟶
            (Opposite.op (DerivedCategory.Q.obj K),
              DerivedCategory.Q.obj (HomComplexR R L M)) from
            (𝟙 (Opposite.op (DerivedCategory.Q.obj K)), ((adjunction R).homIso L M).hom)) ≫
        ((adjunction R).homIso K (HomComplexR R L M)).hom ≫
        DerivedCategory.Q.map (Stacks.HomComplex.Currying.curryIso K L M).hom ≫
        ((adjunction R).homIso (K ⊗ L) M).inv ≫
        (adjunction R).hom.map
          (show (Opposite.op (DerivedCategory.Q.obj (K ⊗ L)), DerivedCategory.Q.obj M) ⟶
            (Opposite.op ((adjunction R).tensor.obj (DerivedCategory.Q.obj K,
              DerivedCategory.Q.obj L)), DerivedCategory.Q.obj M) from
            ((((adjunction R).tensorIso K L hL).hom).op, 𝟙 (DerivedCategory.Q.obj M))) := by
    rw [← reassoc_of% hstar, Iso.hom_inv_id_assoc,
      hom_map_op_comp' ((adjunction R).tensorIso K L hL) (DerivedCategory.Q.obj M),
      Category.comp_id]
  have ha : χ ≫ (curryingIso (DerivedCategory.Q.obj K) (DerivedCategory.Q.obj L)
        (DerivedCategory.Q.obj M)).hom =
      (DerivedCategory.Q.map (g ≫ (Stacks.HomComplex.Currying.curryIso K L M).hom) ≫
        ((adjunction R).homIso (K ⊗ L) M).inv) ≫
        (adjunction R).hom.map
          (show (Opposite.op (DerivedCategory.Q.obj (K ⊗ L)), DerivedCategory.Q.obj M) ⟶
            (Opposite.op ((adjunction R).tensor.obj (DerivedCategory.Q.obj K,
              DerivedCategory.Q.obj L)), DerivedCategory.Q.obj M) from
            ((((adjunction R).tensorIso K L hL).hom).op, 𝟙 (DerivedCategory.Q.obj M))) := by
    rw [hc]
    rw [← reassoc_of% hg, Functor.map_comp]
    simp only [Category.assoc]
  have hRHS : (adjunction R).homEquiv (DerivedCategory.Q.obj X)
        ((adjunction R).tensor.obj (DerivedCategory.Q.obj K, DerivedCategory.Q.obj L))
        (DerivedCategory.Q.obj M)
        (χ ≫ (curryingIso (DerivedCategory.Q.obj K) (DerivedCategory.Q.obj L)
          (DerivedCategory.Q.obj M)).hom) =
      (adjunction R).tensor.map
          (show (DerivedCategory.Q.obj X, (adjunction R).tensor.obj
              (DerivedCategory.Q.obj K, DerivedCategory.Q.obj L)) ⟶
            (DerivedCategory.Q.obj X, DerivedCategory.Q.obj (K ⊗ L)) from
            (𝟙 (DerivedCategory.Q.obj X), ((adjunction R).tensorIso K L hL).hom)) ≫
        ((adjunction R).tensorIso X (K ⊗ L) hKL).hom ≫
        DerivedCategory.Q.map (uncurry (g ≫ (Stacks.HomComplex.Currying.curryIso K L M).hom)) := by
    rw [ha, (adjunction R).homEquiv_dinaturality (((adjunction R).tensorIso K L hL).hom)
        (DerivedCategory.Q.map (g ≫ (Stacks.HomComplex.Currying.curryIso K L M).hom) ≫
          ((adjunction R).homIso (K ⊗ L) M).inv),
      homEquiv_map_uncurry X (K ⊗ L) M hKL (g ≫ (Stacks.HomComplex.Currying.curryIso K L M).hom)]
  have hassoc : ((adjunction R).tensorAssoc (DerivedCategory.Q.obj X)
          (DerivedCategory.Q.obj K) (DerivedCategory.Q.obj L)).hom ≫
        (adjunction R).tensor.map
          (show (DerivedCategory.Q.obj X, (adjunction R).tensor.obj
              (DerivedCategory.Q.obj K, DerivedCategory.Q.obj L)) ⟶
            (DerivedCategory.Q.obj X, DerivedCategory.Q.obj (K ⊗ L)) from
            (𝟙 (DerivedCategory.Q.obj X), ((adjunction R).tensorIso K L hL).hom)) ≫
        ((adjunction R).tensorIso X (K ⊗ L) hKL).hom =
      (adjunction R).tensor.map
          (show ((adjunction R).tensor.obj (DerivedCategory.Q.obj X,
              DerivedCategory.Q.obj K), DerivedCategory.Q.obj L) ⟶
            (DerivedCategory.Q.obj (X ⊗ K), DerivedCategory.Q.obj L) from
            (((adjunction R).tensorIso X K hK).hom, 𝟙 (DerivedCategory.Q.obj L))) ≫
        ((adjunction R).tensorIso (X ⊗ K) L hL).hom ≫
        DerivedCategory.Q.map (α_ X K L).hom :=
    StacksDraft.DerivedHom.derivedHomAdjunction_tensorAssoc_comparison X K L hX hK hL hKL
  rw [hLHS, hRHS, uncurry_uncurry, Functor.map_comp, ← reassoc_of% hassoc]

/-! #### The law in general -/

private lemma curryingLawAt_all (X K L M : DerivedCategory (ModuleCat R)) :
    CurryingLawAt X K L M := by
  obtain ⟨E, hE, ⟨eX⟩⟩ := Stacks.DerivedTensorHomDiagonal.exists_kFlat_model X
  obtain ⟨F, hF, ⟨eK⟩⟩ := Stacks.DerivedTensorHomDiagonal.exists_kFlat_model K
  obtain ⟨G, hG, ⟨eL⟩⟩ := Stacks.DerivedTensorHomDiagonal.exists_kFlat_model L
  obtain ⟨I, i, hi, hI⟩ :=
    CochainComplex.exists_quasiIso_isKInjective (DerivedCategory.Q.objPreimage M)
  have := hi
  have := hI
  have eM : M ≅ DerivedCategory.Q.obj I :=
    (DerivedCategory.Q.objObjPreimageIso M).symm ≪≫ asIso (DerivedCategory.Q.map i)
  exact ((((curryingLawAt_models E F G I hE hF hG).ofIsoTest eX).ofIsoFirst eK).ofIsoSecond
    eL).ofIsoTarget eM

/-! #### Currying as a transpose -/

/-- **The currying law of Tag 0A65 at an arbitrary test object.** Postcomposing a map
`X ⟶ RHom(K, RHom(L, M))` with the currying isomorphism `RHom(K, RHom(L, M)) ≅ RHom(K ⊗ᴸ L, M)`
is the same as transposing twice through the derived tensor--Hom adjunction and then
reassociating the tensor product. -/
public theorem comp_curryingIso_hom (X K L M : DerivedCategory (ModuleCat R))
    (a : X ⟶ (hom R).obj (Opposite.op K, (hom R).obj (Opposite.op L, M))) :
    a ≫ (curryingIso K L M).hom =
      (homEquiv X ((tensor R).obj (K, L)) M).symm
        (((adjunction R).tensorAssoc X K L).inv ≫
          homEquiv ((tensor R).obj (X, K)) L M (homEquiv X K _ a)) := by
  rw [curryingLawAt_all X K L M a, ← Category.assoc, Iso.inv_hom_id, Category.id_comp,
    AddEquiv.symm_apply_apply]

/-! #### Transposing composition -/

/-- Composition of derived internal Homs uncurries to evaluating twice: the transpose of
`RHom(L, M) ⊗ᴸ RHom(K, L) ⟶ RHom(K, M)` through the fixed derived tensor--Hom adjunction is
tensor associativity followed by evaluation on the inner factor and then on the outer one. -/
public theorem homEquiv_composition (K L M : DerivedCategory (ModuleCat R)) :
    homEquiv ((tensor R).obj ((hom R).obj (Opposite.op L, M), (hom R).obj (Opposite.op K, L)))
        K M (composition K L M) =
      ((adjunction R).tensorAssoc ((hom R).obj (Opposite.op L, M))
          ((hom R).obj (Opposite.op K, L)) K).hom ≫
        (tensor R).map (𝟙 ((hom R).obj (Opposite.op L, M)), evaluation K L) ≫
        evaluation L M := by
  have h := curryingLawAt_all ((adjunction R).hom.obj (Opposite.op L, M))
    ((adjunction R).hom.obj (Opposite.op K, L)) K M
    ((adjunction R).hom.map
        (show (Opposite.op L, M) ⟶
          (Opposite.op ((adjunction R).tensor.obj
            ((adjunction R).hom.obj (Opposite.op K, L), K)), M) from
          ((evaluation K L).op, 𝟙 M)) ≫
      (curryingIso ((adjunction R).hom.obj (Opposite.op K, L)) K M).inv)
  dsimp only [CurryingLawFor] at h
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id] at h
  have hd := (adjunction R).homEquiv_dinaturality (evaluation K L)
    (𝟙 ((adjunction R).hom.obj (Opposite.op L, M)))
  rw [Category.id_comp] at hd
  rw [hd] at h
  exact h


end CurryingLaw

end DerivedInternalHom.Model

end StacksDraft.DerivedHom

end
