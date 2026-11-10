module

public import StacksFrontier.AlgebraicGeometry.Discriminant.ProductFactorization
public import Mathlib.LinearAlgebra.TensorProduct.Prod

/-!
# The dualizing module of a product factorization

A finite-open factorization `F` of `A → B × C` restricts to factorizations of `A → B` and
`A → C` with the same intermediate algebra, and the relative dualizing module of `F` is the
product of the two restricted dualizing modules. On the right the product ring acts through its
two projections, and the equivalence sends a pure tensor to the pair of pure tensors obtained by
projecting its coefficient.

## Main definitions

* `Stacks.Discriminant.moduleLinearEquivOfSmulEq` is the identity equivalence between two module
  structures with the same scalar action.
* `Stacks.Discriminant.linearEquivCompHom` restricts a linear equivalence along a ring
  homomorphism.
* `Stacks.Discriminant.productFactorizationEquiv` is the equivalence of the dualizing module of
  a product factorization with the product of the two restricted dualizing modules.

## Main results

* `Stacks.Discriminant.moduleLinearEquivOfSmulEq_apply` and
  `Stacks.Discriminant.linearEquivCompHom_apply`: neither transport changes the underlying
  function.
* `Stacks.Discriminant.productFactorizationEquiv_tmul`: the equivalence on pure tensors is the
  pair of projections of the coefficient.

## Implementation notes

The module structure of the intermediate algebra on `B × C` comes from the factorization's own
algebra structure, while `Mathlib.LinearAlgebra.TensorProduct.Prod` states the distribution of a
tensor product over a product for the componentwise structure. The two agree, and
`Stacks.Discriminant.moduleLinearEquivOfSmulEq` transports across that agreement rather than
rewriting the instance.

## References

* [Stacks Project, Tag 0BT5](https://stacks.math.columbia.edu/tag/0BT5)
-/

@[expose] public section

universe u v w x y z

namespace Stacks.Discriminant

open scoped TensorProduct

/-- The identity linear equivalence between module structures with the same scalar action. -/
def moduleLinearEquivOfSmulEq
    {R : Type u} {M : Type v} [Semiring R] [AddCommMonoid M]
    (P Q : Module R M)
    (h : ∀ r m, @SMul.smul R M P.toSMul r m = @SMul.smul R M Q.toSMul r m) :
    @LinearEquiv R R _ _ (RingHom.id R) (RingHom.id R) _ _ M M _ _ P Q := by
  have hPQ : P = Q := Module.ext' P Q h
  subst Q
  exact LinearEquiv.refl R M

/-- The identity equivalence between module structures with the same scalar action is the
identity on elements. -/
theorem moduleLinearEquivOfSmulEq_apply
    {R : Type u} {M : Type v} [Semiring R] [AddCommMonoid M]
    (P Q : Module R M)
    (h : ∀ r m, @SMul.smul R M P.toSMul r m = @SMul.smul R M Q.toSMul r m)
    (m : M) : moduleLinearEquivOfSmulEq P Q h m = m := by
  have hPQ : P = Q := Module.ext' P Q h
  subst Q
  rfl

/-- Restrict a linear equivalence along a ring homomorphism. -/
noncomputable def linearEquivCompHom
    {R : Type u} {S : Type v} {M : Type w} {N : Type x}
    [CommSemiring R] [CommSemiring S] (f : R →+* S)
    [AddCommMonoid M] [AddCommMonoid N] [Module S M] [Module S N]
    (e : M ≃ₗ[S] N) :
    letI : Module R M := Module.compHom M f
    letI : Module R N := Module.compHom N f
    M ≃ₗ[R] N := by
  let : Module R M := Module.compHom M f
  let : Module R N := Module.compHom N f
  let L : M →ₗ[R] N :=
    { toFun := e
      map_add' := e.map_add
      map_smul' := by
        intro r m
        change e ((f r) • m) = (f r) • e m
        exact e.map_smul (f r) m }
  exact LinearEquiv.ofBijective L e.bijective

/-- Restriction of scalars does not change the underlying function of a linear equivalence. -/
theorem linearEquivCompHom_apply
    {R : Type u} {S : Type v} {M : Type w} {N : Type x}
    [CommSemiring R] [CommSemiring S] (f : R →+* S)
    [AddCommMonoid M] [AddCommMonoid N] [Module S M] [Module S N]
    (e : M ≃ₗ[S] N) (m : M) :
    letI : Module R M := Module.compHom M f
    letI : Module R N := Module.compHom N f
    linearEquivCompHom f e m = e m := rfl

/-- **Scalar extension to a product is the product of scalar extensions to its factors.** For a
finite-open factorization of `A → B × C`, the relative dualizing module is the product of the
dualizing modules of the two restricted factorizations. -/
noncomputable def productFactorizationEquiv
    {A : Type u} {B : Type v} {C : Type w}
    [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra A C]
    (F : FiniteOpenFactorization.{u, max v w, x} A (B × C)) :
    let FB := firstFactorization F
    let FC := secondFactorization F
    letI : Module (B × C) (dualizingModule FB) :=
      Module.compHom _ (RingHom.fst B C)
    letI : Module (B × C) (dualizingModule FC) :=
      Module.compHom _ (RingHom.snd B C)
    dualizingModule F ≃ₗ[B × C] (dualizingModule FB × dualizingModule FC) := by
  let FB := firstFactorization F
  let FC := secondFactorization F
  let : CommRing F.middle := F.commRingMiddle
  let : Algebra A F.middle := F.algebraMiddle
  let : CommRing FB.middle := FB.commRingMiddle
  let : Algebra A FB.middle := FB.algebraMiddle
  let : Algebra FB.middle B := FB.algebraTarget
  let : CommRing FC.middle := FC.commRingMiddle
  let : Algebra A FC.middle := FC.algebraMiddle
  let : Algebra FC.middle C := FC.algebraTarget
  let : Algebra F.middle (B × C) := F.algebraTarget
  let : Module F.middle (dualizingModule F) := Module.compHom _ (algebraMap F.middle (B × C))
  let : Module FB.middle (Module.Dual A FB.middle) := algebraDualModule A FB.middle
  let : Module FC.middle (Module.Dual A FC.middle) := algebraDualModule A FC.middle
  let : Module FB.middle B := FB.algebraTarget.toModule
  let : Module FC.middle C := FC.algebraTarget.toModule
  let : Algebra F.middle B := FB.algebraTarget
  let : Algebra F.middle C := FC.algebraTarget
  let : AddCommMonoid (B × C) := (inferInstance : CommRing (B × C)).toAddCommMonoid
  let : Module F.middle B := Algebra.toModule
  let : Module F.middle C := Algebra.toModule
  let : Module F.middle (B × C) := F.algebraTarget.toModule
  let : Module F.middle (Module.Dual A F.middle) := algebraDualModule A F.middle
  let : Module FB.middle (Module.Dual A FB.middle) := algebraDualModule A FB.middle
  let : Module FC.middle (Module.Dual A FC.middle) := algebraDualModule A FC.middle
  let : Module (B × C) (Module.Dual A F.middle ⊗[F.middle] (B × C)) := by
    let : Module (B × C) ((B × C) ⊗[F.middle] Module.Dual A F.middle) :=
      TensorProduct.leftModule
    exact (TensorProduct.comm F.middle (Module.Dual A F.middle) (B × C)).toAddEquiv.module
      (B × C)
  let : Module (B × C) (dualizingModule FB) := Module.compHom _ (RingHom.fst B C)
  let : Module (B × C) (dualizingModule FC) := Module.compHom _ (RingHom.snd B C)
  let : Module B (Module.Dual A F.middle ⊗[F.middle] B) := by
    change Module B (dualizingModule FB)
    infer_instance
  let : Module C (Module.Dual A F.middle ⊗[F.middle] C) := by
    change Module C (dualizingModule FC)
    infer_instance
  let : Module (B × C) (Module.Dual A F.middle ⊗[F.middle] B) :=
    Module.compHom (dualizingModule FB) (RingHom.fst B C)
  let : Module (B × C) (Module.Dual A F.middle ⊗[F.middle] C) :=
    Module.compHom (dualizingModule FC) (RingHom.snd B C)
  have hsmul : ∀ r p,
      @SMul.smul F.middle (B × C) F.algebraTarget.toModule.toSMul r p =
        @SMul.smul F.middle (B × C)
          (@Prod.instModule F.middle B C _ _ _ _ _).toSMul r p := by
    intro r p
    have hsource :
        @SMul.smul F.middle (B × C) F.algebraTarget.toModule.toSMul r p =
          algebraMap F.middle (B × C) r * p := by
      let : Module F.middle (B × C) := F.algebraTarget.toModule
      exact Algebra.smul_def r p
    have hprod : algebraMap F.middle (B × C) r * p =
        @SMul.smul F.middle (B × C)
          (@Prod.instModule F.middle B C _ _ _ _ _).toSMul r p := by
      rcases p with ⟨b, c⟩
      change ((algebraMap F.middle (B × C) r).1 * b,
          (algebraMap F.middle (B × C) r).2 * c) = (r • b, r • c)
      have hmap : algebraMap F.middle (B × C) r =
          (algebraMap F.middle B r, algebraMap F.middle C r) := by
        ext <;> rfl
      rw [hmap]
      simp [Algebra.smul_def]
    exact hsource.trans hprod
  let eMod : @LinearEquiv F.middle F.middle _ _ (RingHom.id F.middle) (RingHom.id F.middle)
      _ _ (B × C) (B × C) _ _ F.algebraTarget.toModule
      (@Prod.instModule F.middle B C _ _ _ _ _) :=
    moduleLinearEquivOfSmulEq F.algebraTarget.toModule
      (@Prod.instModule F.middle B C _ _ _ _ _) hsmul
  let eCongr :
      @TensorProduct F.middle _ (Module.Dual A F.middle) (B × C)
        _ _ (algebraDualModule A F.middle) F.algebraTarget.toModule ≃ₗ[F.middle]
      @TensorProduct F.middle _ (Module.Dual A F.middle) (B × C)
        _ _ (algebraDualModule A F.middle) (@Prod.instModule F.middle B C _ _ _ _ _) :=
    @TensorProduct.congr F.middle F.middle _ _ (RingHom.id F.middle)
      (Module.Dual A F.middle) (B × C) (Module.Dual A F.middle) (B × C)
      _ _ _ _ (algebraDualModule A F.middle) F.algebraTarget.toModule
      (algebraDualModule A F.middle) (@Prod.instModule F.middle B C _ _ _ _ _)
      (RingHom.id F.middle) _ _
      (LinearEquiv.refl F.middle (Module.Dual A F.middle)) eMod
  let e := eCongr.trans
    (TensorProduct.prodRight F.middle F.middle (Module.Dual A F.middle) B C)
  have heMod (p : B × C) : eMod p = p := by
    have hId (P Q : Module F.middle (B × C))
        (h : ∀ r p, @SMul.smul F.middle (B × C) P.toSMul r p =
          @SMul.smul F.middle (B × C) Q.toSMul r p) (p : B × C) :
        moduleLinearEquivOfSmulEq P Q h p = p := by
      have hPQ : P = Q := Module.ext' P Q h
      subst Q
      rfl
    exact hId F.algebraTarget.toModule
      (@Prod.instModule F.middle B C _ _ _ _ _) hsmul p
  have hscalar (r : B × C) :
      ∀ t : Module.Dual A F.middle ⊗[F.middle] (B × C),
        e (r • t) = r • e t := by
    intro t
    induction t using TensorProduct.inductionOn with
    | tmul f bc =>
        rcases bc with ⟨b, c⟩
        have hsource : r • (f ⊗ₜ[F.middle] (b, c)) =
            f ⊗ₜ[F.middle] (r * (b, c)) := by
          change (TensorProduct.comm F.middle (Module.Dual A F.middle) (B × C)).symm
              (r • (TensorProduct.comm F.middle (Module.Dual A F.middle) (B × C)
                (f ⊗ₜ[F.middle] (b, c)))) = _
          rw [TensorProduct.comm_tmul, TensorProduct.smul_tmul',
            TensorProduct.comm_symm_tmul]
          simp
        rw [hsource]
        simp only [e, LinearEquiv.trans_apply, eCongr, TensorProduct.congr_tmul,
          LinearEquiv.refl_apply, heMod, TensorProduct.prodRight_tmul]
        change (f ⊗ₜ[F.middle] (r.1 * b), f ⊗ₜ[F.middle] (r.2 * c)) =
          (r.1 • (f ⊗ₜ[F.middle] b), r.2 • (f ⊗ₜ[F.middle] c))
        apply Prod.ext
        · symm
          change (TensorProduct.comm F.middle (Module.Dual A F.middle) B).symm
              (r.1 • (TensorProduct.comm F.middle (Module.Dual A F.middle) B
                (f ⊗ₜ[F.middle] b))) = _
          rw [TensorProduct.comm_tmul, TensorProduct.smul_tmul',
            TensorProduct.comm_symm_tmul]
          simp
        · symm
          change (TensorProduct.comm F.middle (Module.Dual A F.middle) C).symm
              (r.2 • (TensorProduct.comm F.middle (Module.Dual A F.middle) C
                (f ⊗ₜ[F.middle] c))) = _
          rw [TensorProduct.comm_tmul, TensorProduct.smul_tmul',
            TensorProduct.comm_symm_tmul]
          simp
    | add x y hx hy =>
        rw [smul_add, e.map_add, hx, hy, ← smul_add, e.map_add]
  let L : dualizingModule F →ₗ[B × C]
      (dualizingModule FB × dualizingModule FC) :=
    { toFun := e
      map_add' := by
        intro x y
        exact e.map_add x y
      map_smul' := by
        intro r t
        exact hscalar r t }
  exact LinearEquiv.ofBijective L (by
    change Function.Bijective e
    exact e.bijective)

/-- On a pure tensor, the product equivalence of a product factorization projects the
coefficient to the two factors and keeps the functional. -/
theorem productFactorizationEquiv_tmul
    {A : Type u} {B : Type v} {C : Type w}
    [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra A C]
    (F : FiniteOpenFactorization.{u, max v w, x} A (B × C))
    (f : Module.Dual A F.middle) (b : B) (c : C) :
       productFactorizationEquiv F (dualizingModule.tmul F f (b, c)) =
      (dualizingModule.tmul (firstFactorization F) f b,
       dualizingModule.tmul (secondFactorization F) f c) := by
  let FB := firstFactorization F
  let FC := secondFactorization F
  have hmidB : (firstFactorization F).middle = F.middle := rfl
  have hmidC : (secondFactorization F).middle = F.middle := rfl
  let : CommRing FB.middle := FB.commRingMiddle
  let : Algebra A FB.middle := FB.algebraMiddle
  let : Algebra FB.middle B := FB.algebraTarget
  let : CommRing FC.middle := FC.commRingMiddle
  let : Algebra A FC.middle := FC.algebraMiddle
  let : Algebra FC.middle C := FC.algebraTarget
  let : Algebra F.middle B := FB.algebraTarget
  let : Algebra F.middle C := FC.algebraTarget
  let : Module FB.middle (Module.Dual A FB.middle) := algebraDualModule A FB.middle
  let : Module FC.middle (Module.Dual A FC.middle) := algebraDualModule A FC.middle
  let : Module FB.middle B := FB.algebraTarget.toModule
  let : Module FC.middle C := FC.algebraTarget.toModule
  let : Module F.middle B := Algebra.toModule
  let : Module F.middle C := Algebra.toModule
  let : AddCommMonoid (B × C) := (inferInstance : CommRing (B × C)).toAddCommMonoid
  let : Module F.middle (B × C) := F.algebraTarget.toModule
  let : Module F.middle (Module.Dual A F.middle) := algebraDualModule A F.middle
  let : Module (B × C) (Module.Dual A F.middle ⊗[F.middle] (B × C)) := by
    let : Module (B × C) ((B × C) ⊗[F.middle] Module.Dual A F.middle) :=
      TensorProduct.leftModule
    exact (TensorProduct.comm F.middle (Module.Dual A F.middle) (B × C)).toAddEquiv.module
      (B × C)
  let hsmul : ∀ r p,
      @SMul.smul F.middle (B × C) F.algebraTarget.toModule.toSMul r p =
        @SMul.smul F.middle (B × C)
          (@Prod.instModule F.middle B C _ _ _ _ _).toSMul r p := by
    intro r p
    have hsource :
        @SMul.smul F.middle (B × C) F.algebraTarget.toModule.toSMul r p =
          algebraMap F.middle (B × C) r * p := by
      let : Module F.middle (B × C) := F.algebraTarget.toModule
      exact Algebra.smul_def r p
    have hprod : algebraMap F.middle (B × C) r * p =
        @SMul.smul F.middle (B × C)
          (@Prod.instModule F.middle B C _ _ _ _ _).toSMul r p := by
      rcases p with ⟨b, c⟩
      change ((algebraMap F.middle (B × C) r).1 * b,
          (algebraMap F.middle (B × C) r).2 * c) = (r • b, r • c)
      have hmap : algebraMap F.middle (B × C) r =
          (algebraMap F.middle B r, algebraMap F.middle C r) := by
        ext <;> rfl
      rw [hmap]
      simp [Algebra.smul_def]
    exact hsource.trans hprod
  let eMod : @LinearEquiv F.middle F.middle _ _ (RingHom.id F.middle) (RingHom.id F.middle)
      _ _ (B × C) (B × C) _ _ F.algebraTarget.toModule
      (@Prod.instModule F.middle B C _ _ _ _ _) :=
    moduleLinearEquivOfSmulEq F.algebraTarget.toModule
      (@Prod.instModule F.middle B C _ _ _ _ _) hsmul
  let eCongr :
      @TensorProduct F.middle _ (Module.Dual A F.middle) (B × C)
        _ _ (algebraDualModule A F.middle) F.algebraTarget.toModule ≃ₗ[F.middle]
      @TensorProduct F.middle _ (Module.Dual A F.middle) (B × C)
        _ _ (algebraDualModule A F.middle) (@Prod.instModule F.middle B C _ _ _ _ _) :=
    @TensorProduct.congr F.middle F.middle _ _ (RingHom.id F.middle)
      (Module.Dual A F.middle) (B × C) (Module.Dual A F.middle) (B × C)
      _ _ _ _ (algebraDualModule A F.middle) F.algebraTarget.toModule
      (algebraDualModule A F.middle) (@Prod.instModule F.middle B C _ _ _ _ _)
      (RingHom.id F.middle) _ _
      (LinearEquiv.refl F.middle (Module.Dual A F.middle)) eMod
  let e := eCongr.trans (TensorProduct.prodRight F.middle F.middle (Module.Dual A F.middle) B C)
  change e (f ⊗ₜ[F.middle] (b, c)) = _
  simp [e, eCongr, eMod, TensorProduct.congr_tmul, TensorProduct.prodRight_tmul,
    moduleLinearEquivOfSmulEq_apply, dualizingModule.tmul]
  rfl


end Stacks.Discriminant
