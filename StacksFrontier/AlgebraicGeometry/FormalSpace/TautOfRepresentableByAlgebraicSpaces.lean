module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Affine.Factorization
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Affine.MorphismOfAffines
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Affine.RepresentableAffine
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Affine.ThickeningStage
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Representable
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.ClosedImmersionFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactSurjection
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints
public import StacksFrontier.CategoryTheory.Sites.Representable.SheafifiedYonedaSubcanonical
public import StacksFrontier.CategoryTheory.Sites.SubcanonicalSheafifiedYoneda
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RepresentableFormalSpectrumTaut
public import StacksFrontier.AlgebraicGeometry.FormalSpace.SpectrumFiniteTypeRefined
public import StacksFrontier.AlgebraicGeometry.FormalSpace.TautOfRepresentable

/-!
# Tautness from representability by algebraic spaces, and the finite type case

Let `φ : A ⟶ C` be a continuous homomorphism of weakly admissible topological rings over a
scheme `S`, so that `Spf A` and `Spf C` are affine formal algebraic spaces (**Stacks 0AIF**).
If `Spf φ` is representable by algebraic spaces — condition (1) of **Stacks 0AN5** — then over
a test object of the site whose underlying scheme is affine it is representable by an object of
the site, which is **Stacks 0AKN**. The thickening stages of `Spf A` are such test objects, so
the implication (2) ⟹ (3) of Stacks 0AN5 in
`StacksFrontier.AlgebraicGeometry.FormalSpace.TautOfRepresentable` applies and `φ` is taut.

Being of finite type includes that representability, so this discharges the tautness
hypothesis of the stagewise computation of
`StacksFrontier.AlgebraicGeometry.FormalSpace.SpectrumFiniteType` and gives the implication
(1) ⟹ (2) of **Stacks 0ANT** outright: for a finite type `Spf φ`, the homomorphism `φ` is taut
and `C` is topologically of finite type over `A`. That is part (4) of **Stacks 0AJK**.

## Main results

* `isTaut_and_isTopologicallyOfFiniteType_of_isFiniteType_formalSpectrumMap`: for a finite type
  `Spf φ`, the homomorphism `φ` is taut and `C` is topologically of finite type over `A`.

## References

* [Stacks Project, Tag 0AJK](https://stacks.math.columbia.edu/tag/0AJK)
* [Stacks Project, Tag 0AIF](https://stacks.math.columbia.edu/tag/0AIF)
* [Stacks Project, Tag 0AKN](https://stacks.math.columbia.edu/tag/0AKN)
* [Stacks Project, Tag 0AN5](https://stacks.math.columbia.edu/tag/0AN5)
* [Stacks Project, Tag 0ANT](https://stacks.math.columbia.edu/tag/0ANT)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.FormalSpace

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

variable {A C : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [IsLinearTopology A A] [CommRing C] [TopologicalSpace C] [IsTopologicalRing C]
  [IsLinearTopology C C]

/-- Let `φ : A ⟶ C` be a continuous homomorphism of weakly admissible topological rings over
`S`, so that `Spf A` and `Spf C` are affine formal algebraic spaces. If `Spf (φ)` is of finite
type, then `φ` is taut and `C` is topologically of finite type over `A`. -/
theorem isTaut_and_isTopologicallyOfFiniteType_of_isFiniteType_formalSpectrumMap
    (hA : TopologicalRing.IsWeaklyAdmissible A) (hC : TopologicalRing.IsWeaklyAdmissible C)
    (D : QuotientSystem B S hS A) (E : QuotientSystem B S hS C) (f : ContinuousHom D E)
    (hD : IsAffineFormalAlgebraicSpace B S hS (formalSpectrum D))
    (hE : IsAffineFormalAlgebraicSpace B S hS (formalSpectrum E))
    (hFT : IsFiniteType B S hS (formalSpectrumMap hA f)) :
    RingHom.IsTaut f.toRingHom ∧
      TopologicalRing.IsTopologicallyOfFiniteType f.toRingHom := by
  obtain ⟨hrep, -⟩ := id hFT
  have htaut : RingHom.IsTaut f.toRingHom :=
    isTaut_of_isRepresentableByAlgebraicSpacesULift_formalSpectrumMap_of_isAffine B S hS hA hC D E
      hD hE f hrep
  exact ⟨htaut, isTopologicallyOfFiniteType_of_isFiniteType_formalSpectrumMap
    hA hC D E f htaut hFT⟩

add_to_stacks 0AJK "part (4) in full. For a finite type `f : Y → X` with `Y` McQuillan, the \
homomorphism `φ : A → B` presenting `f` is taut and `B` is topologically of finite type over \
`A`, which are part (4)'s two conclusions; and with the second comes part (4)'s restatement \
that `f` factors as `Y → A^r_X → X` with the first arrow a closed immersion of McQuillan \
affine formal algebraic spaces, since `TopologicalRing.IsTopologicallyOfFiniteType` produces \
the integer `r` together with a homomorphism `A[x_1, ..., x_r] → B` restricting to `φ` on \
constants and having dense image, which is that factorization and the dense image of its \
first arrow. Part (4) closes by observing that questions (1) and (2) are then in force for \
`Y → A^r_X`; those are questions and are asserted nowhere."
  isTaut_and_isTopologicallyOfFiniteType_of_isFiniteType_formalSpectrumMap

end AlgebraicGeometry.FormalSpace

end
