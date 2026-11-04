module

public import StacksFrontier.AlgebraicGeometry.RelativeVeryAmpleTwist.CanonicalSymHom
public import StacksFrontier.AlgebraicGeometry.RelativeProjInvertibleMorphism.Locus

/-!
# Graded-algebra maps out of `Sym(E)`, and precomposing a graded power map

Two pieces of the construction, in the proof of [Stacks, Tag 07RM], of the morphism
`r_{L, ψ} : X ⟶ 𝐏(E)` attached to a module map `E ⟶ f_*L`.

* A morphism `u : E ⟶ 𝒜_1` from a quasi-coherent `𝒪_S`-module into the degree-one piece of a
  quasi-coherent graded `𝒪_S`-algebra `𝒜` extends uniquely to a homomorphism of graded algebras
  `Sym(E) ⟶ 𝒜`, by the universal property of the symmetric algebra; the pairwise commutation the
  universal property asks of `u` is the commutativity of `𝒜`.
* A graded map `ψ : f^*𝒜 ⟶ ⨁_{d ≥ 0} L^{⊗ d}` — the datum of [Stacks, Tag 01O8] — precomposed
  with a homomorphism of graded algebras `𝒜' ⟶ 𝒜` is again such a datum, for `𝒜'`.

## Main definitions

* `Stacks.QuasiProjectiveCompactification.symLift`: the homomorphism `Sym(E) ⟶ 𝒜` extending
  `u : E ⟶ 𝒜_1`.
* `Stacks.AlgebraicGeometry.RelativeProjInvertibleMorphism.GradedPowerMap.precomp`: a graded power
  map precomposed with a homomorphism of graded algebras.

## Main results

* `Stacks.QuasiProjectiveCompactification.symmetricAlgebraGen_comp_symLift_app_one`: `symLift`
  restricts to `u` on the degree-one generators, and
  `Stacks.QuasiProjectiveCompactification.symLift_app_one_symmetricAlgebraGen` is its sectionwise
  form.
* `Stacks.QuasiProjectiveCompactification.symLift_unique`: it is the only such homomorphism.

## References

* [Stacks Project, Tag 07RM](https://stacks.math.columbia.edu/tag/07RM)
* [Stacks Project, Tag 01O8](https://stacks.math.columbia.edu/tag/01O8)
* [Stacks Project, Tag 01CG](https://stacks.math.columbia.edu/tag/01CG)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProjMapDomain

universe u

namespace Stacks.QuasiProjectiveCompactification

variable {S : Scheme.{u}} (E : S.Modules) [E.IsQuasicoherent] (B : SheafGradedAlgebra.{u} S)
  (v : E ⟶ B.piece 1)

omit [E.IsQuasicoherent] in
/-- A morphism into the degree-one piece of a sheaf-level graded algebra is a pairwise-commuting
degree-one generator, because the multiplication of the algebra is commutative. -/
theorem pairwiseCommutes_of_sheafGradedAlgebra :
    SheafOfModules.GradedAlgebra.PairwiseCommutes (A := B.asGradedAlgebra) v :=
  fun U _ _ => eq_of_heq (B.mul_comm 1 1 U.unop _ _)

/-- The extension of `v : E ⟶ 𝒜_1` to a unital homomorphism `Sym(E) ⟶ 𝒜` of sheaves of graded
algebras, by the universal property of the symmetric algebra. -/
def symLiftUnitalHom :
    SheafOfModules.GradedAlgebra.UnitalHom (Scheme.Modules.symmetricAlgebra S E)
      B.asGradedAlgebra :=
  ((Scheme.Modules.isSymmetricAlgebra_symmetricAlgebra S E).2 B.asGradedAlgebra v
    (pairwiseCommutes_of_sheafGradedAlgebra E B v)).choose

/-- **The homomorphism of graded algebras `Sym(E) ⟶ 𝒜` extending `v : E ⟶ 𝒜_1`.** -/
def symLift : SheafGradedAlgebraHom (Stacks.Tag01VMRelativeVeryAmple.symAlgebra E) B :=
  SheafGradedAlgebraHom.ofUnitalHom (symLiftUnitalHom E B v)

/-- **`symLift` restricts to `v` on the degree-one generators.** -/
theorem symmetricAlgebraGen_comp_symLift_app_one :
    Scheme.Modules.symmetricAlgebraGen S E ≫ (symLift E B v).app 1 = v :=
  ((Scheme.Modules.isSymmetricAlgebra_symmetricAlgebra S E).2 B.asGradedAlgebra v
    (pairwiseCommutes_of_sheafGradedAlgebra E B v)).choose_spec.1

/-- `symLift` restricts to `v` on the degree-one generators, sectionwise: over an open `U` it
sends the generator of a section `x` of `E` to `v x`. -/
theorem symLift_app_one_symmetricAlgebraGen (U : S.Opens) (x : Γ(E, U)) :
    ((symLift E B v).app 1).app U
        (Scheme.Modules.Hom.app (Scheme.Modules.symmetricAlgebraGen S E) U x) =
      v.app U x :=
  congrArg (fun g : E ⟶ B.piece 1 => Scheme.Modules.Hom.app g U x)
    (symmetricAlgebraGen_comp_symLift_app_one E B v)

/-- **Uniqueness of `symLift`**: a homomorphism of graded algebras `Sym(E) ⟶ 𝒜` restricting to
`v` on the degree-one generators is `symLift E B v`. -/
theorem symLift_unique
    (ψ : SheafGradedAlgebraHom (Stacks.Tag01VMRelativeVeryAmple.symAlgebra E) B)
    (hψ : Scheme.Modules.symmetricAlgebraGen S E ≫ ψ.app 1 = v) : ψ = symLift E B v :=
  SheafGradedAlgebraHom.ext fun n =>
    congrArg (fun g : SheafOfModules.GradedAlgebra.UnitalHom
        (Scheme.Modules.symmetricAlgebra S E) B.asGradedAlgebra => g.app n)
      (((Scheme.Modules.isSymmetricAlgebra_symmetricAlgebra S E).2 B.asGradedAlgebra v
        (pairwiseCommutes_of_sheafGradedAlgebra E B v)).choose_spec.2
          (SheafGradedAlgebraHom.toUnitalHom ψ) hψ)

end Stacks.QuasiProjectiveCompactification

namespace Stacks.AlgebraicGeometry.RelativeProjInvertibleMorphism.GradedPowerMap

variable {S T : Scheme.{u}} {A B : SheafGradedAlgebra.{u} S} {f : T ⟶ S}

/-- **A graded power map precomposed with a homomorphism of graded algebras.** For
`ψ : f^*𝒜 ⟶ ⨁_{d ≥ 0} L^{⊗ d}` and `φ : 𝒜' ⟶ 𝒜`, the components `φ_n ≫ ψ_n` form a graded power
map for `𝒜'` with the same invertible module; multiplicativity is that of `φ` followed by that
of `ψ`. -/
def precomp (P : GradedPowerMap B f) (φ : SheafGradedAlgebraHom A B) : GradedPowerMap A f where
  L := P.L
  invertible := P.invertible
  ψ n := φ.app n ≫ P.ψ n
  map_mul n m V a b :=
    (congrArg ((P.ψ (n + m)).val.app (op V)) (φ.app_mul n m V a b)).trans
      (P.map_mul n m V _ _)

/-- The precomposed graded power map has the same invertible module. -/
@[simp]
theorem precomp_L (P : GradedPowerMap B f) (φ : SheafGradedAlgebraHom A B) :
    (P.precomp φ).L = P.L := rfl

/-- The components of the precomposed graded power map are `φ_n ≫ ψ_n`. -/
theorem precomp_ψ (P : GradedPowerMap B f) (φ : SheafGradedAlgebraHom A B) (n : ℕ) :
    (P.precomp φ).ψ n = φ.app n ≫ P.ψ n := rfl

/-- The value of the precomposed map at a homogeneous section `a` is the value of the given map
at `φ(a)`. -/
theorem precomp_value (P : GradedPowerMap B f) (φ : SheafGradedAlgebraHom A B) (n : ℕ)
    (V : S.Opens) (a : Γ(A.piece (n : ℤ), V)) :
    (P.precomp φ).value n V a = P.value n V ((φ.app n).app V a) := rfl

end Stacks.AlgebraicGeometry.RelativeProjInvertibleMorphism.GradedPowerMap

end
