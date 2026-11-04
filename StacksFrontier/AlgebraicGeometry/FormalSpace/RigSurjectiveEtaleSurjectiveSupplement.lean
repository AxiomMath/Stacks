module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.RigSurjectiveEtaleSurjective
import all StacksFrontier.AlgebraicGeometry.FormalSpace.RigSurjectiveEtaleSurjective
public import StacksFrontier.AlgebraicGeometry.FormalSpace.EtaleSourceFormalSpace
public import StacksFrontier.AlgebraicGeometry.FormalSpace.SpectrumEssentiallySurjective
public import StacksFrontier.AlgebraicGeometry.FormalSpace.EssentiallySurjectiveSpf

/-!
# Étale morphisms to `Spf R` from affine formal algebraic spaces

For a McQuillan affine formal algebraic space `Spf R` whose quotient system has a large site, every
affine formal algebraic space with a morphism to `Spf R` which is representable by algebraic spaces
and étale is `Spf` of the completion of an étale `R`-algebra.

## Main definitions

* `AlgebraicGeometry.FormalSpace.IsEssentiallySurjectiveSpfOfHasLargeSite`: the
  essential-surjectivity clause of Stacks 0AN8, for quotient systems with a large site.

## Main results

* `AlgebraicGeometry.FormalSpace.isEssentiallySurjectiveSpf'`: the clause
  `AlgebraicGeometry.FormalSpace.IsEssentiallySurjectiveSpfOfHasLargeSite` holds.
-/

@[expose] public noncomputable section

open Cardinal

universe u

section Lift

open TopologicalRing TopologicalRing.CompletionOver

variable {R : Type u} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
  {A : Type u} [CommRing A]
  {W : Type u} [CommRing W] [IsLocalRing W]

end Lift

section Geometry

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.FormalSpace

namespace AlgebraicGeometry.FormalSpace

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

end AlgebraicGeometry.FormalSpace

end Geometry

section Nontriviality

open AlgebraicGeometry AlgebraicGeometry.FormalSpace

end Nontriviality

section Main

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace AlgebraicGeometry.FormalSpace

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The essential-surjectivity clause of Stacks 0AN8**, for quotient systems on a large site.
For a McQuillan affine formal algebraic space `Spf R` over `S`, every affine formal algebraic
space `V` over `S` carrying a morphism `V ⟶ Spf R` which is representable by algebraic spaces and
étale is `Spf` of the completion `A^∧` of an étale `R`-algebra `A`, compatibly with the morphisms
to `Spf R`.

This differs from `AlgebraicGeometry.FormalSpace.IsEssentiallySurjectiveSpf` in its size
condition: the quotient system `D` is asked to satisfy `D.HasLargeSite` instead of the cardinal
bound `#R < B.cutoff`. -/
abbrev IsEssentiallySurjectiveSpfOfHasLargeSite : Prop :=
  ∀ (R : Type u) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [IsLinearTopology R R]
    (hR : TopologicalRing.IsWeaklyAdmissible R)
    (D : QuotientSystem B S hS R) (_hD : D.HasLargeSite)
    (V : FppfSheaf B S hS) (v : V ⟶ formalSpectrum D),
    IsAffineFormalAlgebraicSpace B S hS V → IsRepresentableEtale B S hS v →
      ∃ (A : Type u) (_ : CommRing A) (_ : Algebra R A) (_ : Algebra.Etale R A)
        (E : QuotientSystem B S hS (TopologicalRing.CompletionOver (algebraMap R A)))
        (c : ContinuousHom D E) (ε : V ≅ formalSpectrum E),
        c.toRingHom = TopologicalRing.CompletionOver.canonicalMap (algebraMap R A) ∧
          ε.hom ≫ formalSpectrumMap hR c = v


/-- **The essential-surjectivity clause of Stacks 0AN8 holds.** An affine formal algebraic space
over `S` with a morphism to `Spf R` which is representable by algebraic spaces and étale is
`Spf` of the completion of an étale `R`-algebra, compatibly with the morphisms to `Spf R`. -/
theorem isEssentiallySurjectiveSpf' : IsEssentiallySurjectiveSpfOfHasLargeSite B S hS := by
  intro R _ _ _ _ hR D hD V v hV hvet
  obtain ⟨A, instA, f, hf, E, g, hg, ε, hε⟩ :=
    exists_etale_completion_formalSpectrum hR D hD v hV hvet
  let := instA
  refine ⟨A, instA, f.toAlgebra, ?_, E, g, ε, hg, hε⟩
  let : Algebra R A := f.toAlgebra
  exact RingHom.etale_algebraMap.mp hf

end AlgebraicGeometry.FormalSpace

end Main

end
