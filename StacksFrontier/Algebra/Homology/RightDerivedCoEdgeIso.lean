module

public import StacksFrontier.Algebra.Homology.RightDerivedCoEdge

/-!
# Invertibility of the co-edge morphism in degree zero

Let `P : A ⥤ B` be additive and preserve injective objects, and let `Q : B ⥤ D` be additive and
left exact.  The co-edge morphism `Stacks.Cohomology.RightDerivedCoEdge.secondEdge` of the pair
`(P, Q)` is the natural transformation

  `Rⁿ(Q ∘ P) ⟶ Q ∘ RⁿP`,

the edge `H^n ⟶ E₂^{0,n}` of the Grothendieck spectral sequence of `(P, Q)`.  This file proves
that it is an isomorphism in degree zero, with no vanishing hypothesis whatsoever.  It is the
counterpart, for the second edge, of
`Stacks.Cohomology.RightDerivedEdgeIso.isIso_edge_app_zero`, and the two together say that the
canonical comparison `R⁰Q (P X) ⟶ Q (R⁰P X)` of the pair is invertible.

The reason is elementary and has nothing to do with the spectral sequence.  The co-edge morphism
in degree `n` is, at an injective resolution `I` of `X` and for `K = P I`, the comparison
`Hⁿ(Q K) ⟶ Q (Hⁿ K)` of
`Stacks.Cohomology.RightDerivedCoEdge.homologyToMapHomology`, read through the identifications of
the two right derived functors with the homology of `K`.  An `ℕ`-indexed cochain complex has no
incoming differential in degree zero, so there homology *is* cycles, both for `K` and for `Q K`;
and left exactness of `Q` makes `Q (Z⁰K) ⟶ Z⁰(Q K)` invertible
(`Stacks.Cohomology.RightDerivedCoEdge.isIso_mapCycles`).  So the comparison is a composite of
three isomorphisms.

In positive degrees the statement is false without further hypotheses: the failure of
`Hⁿ(Q K) ⟶ Q (Hⁿ K)` to be invertible is the presence of the terms `E₂^{p,q}` with `p > 0` on
the second page, and controlling it is what degeneration arguments are for.

## Main results

* `Stacks.Cohomology.RightDerivedCoEdge.isIso_homologyToMapHomology_zero`: the comparison
  `H⁰(Q C) ⟶ Q (H⁰ C)` is an isomorphism for every `ℕ`-indexed cochain complex `C`.
* `Stacks.Cohomology.RightDerivedCoEdge.isIso_secondEdge_app_zero` and
  `Stacks.Cohomology.RightDerivedCoEdge.isIso_secondEdge_zero`: the co-edge morphism is an
  isomorphism in degree zero.

## References

* [Stacks Project, Tag 015M](https://stacks.math.columbia.edu/tag/015M)
* [Stacks Project, Tag 01F2](https://stacks.math.columbia.edu/tag/01F2)
* [Stacks Project, Tag 0EZA](https://stacks.math.columbia.edu/tag/0EZA)
-/

@[expose] public noncomputable section

open CategoryTheory Category Limits

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace Stacks.Cohomology.RightDerivedCoEdge

variable {A : Type u₁} [Category.{v₁} A] [Abelian A]
  {B : Type u₂} [Category.{v₂} B] [Abelian B]
  {D : Type u₃} [Category.{v₃} D] [Abelian D]

section Homology

variable (Q : B ⥤ D) [Q.Additive] [PreservesFiniteLimits Q]

/-- **The comparison `H⁰(Q C) ⟶ Q (H⁰ C)` is an isomorphism** for every `ℕ`-indexed cochain
complex, with no hypothesis beyond left exactness of `Q`.  In degree zero there is no incoming
differential, so homology is cycles for `C` and for `Q C` alike, and `Q` preserves cycles. -/
instance isIso_homologyToMapHomology_zero (C : CochainComplex B ℕ) :
    IsIso (homologyToMapHomology Q C 0) := by
  have key : inv (((Q.mapHomologicalComplex (ComplexShape.up ℕ)).obj C).homologyπ 0) ≫
      (mapCyclesIso Q C 0).inv ≫ Q.map (C.homologyπ 0) = homologyToMapHomology Q C 0 := by
    rw [← homologyπ_comp_homologyToMapHomology Q C 0, IsIso.inv_hom_id_assoc]
  rw [← key]
  exact IsIso.comp_isIso' inferInstance (IsIso.comp_isIso' inferInstance inferInstance)

/-- `isIso_homologyToMapHomology_zero` in the spelling of `homologyFunctorToMapHomology`. -/
instance isIso_homologyFunctorToMapHomology_zero (C : CochainComplex B ℕ) :
    IsIso (homologyFunctorToMapHomology Q C 0) :=
  inferInstanceAs (IsIso (homologyToMapHomology Q C 0))

end Homology

section CoEdge

variable [HasInjectiveResolutions A] [HasInjectiveResolutions B]
  (P : A ⥤ B) [P.Additive] [P.PreservesInjectiveObjects]
  (Q : B ⥤ D) [Q.Additive] [PreservesFiniteLimits Q]

/-- **The co-edge morphism is an isomorphism in degree zero**, with no vanishing hypothesis.  Its
component at `X` is the degree-zero comparison on homology of `P` applied to an injective
resolution of `X`, read through the two identifications of right derived functors with homology;
all three factors are invertible.  For `P = f_*` and `Q = Γ(Y, -)` this is the identification of
a global section of `f_* F` over `Y` with a global section of `F` over `X`. -/
instance isIso_secondEdge_app_zero (X : A) : IsIso ((secondEdge P Q 0).app X) := by
  have h₁ : IsIso (homologyFunctorToMapHomology Q
      ((P.mapHomologicalComplex (ComplexShape.up ℕ)).obj
        (injectiveResolution X).cocomplex) 0) := inferInstance
  have h₂ : IsIso (Q.map ((injectiveResolution X).isoRightDerivedObj P 0).inv) := inferInstance
  have h₃ : IsIso ((RightDerivedEdge.isoRightDerivedObjComp P Q
      (injectiveResolution X) 0).hom) := inferInstance
  change IsIso (secondEdgeApp P Q 0 X)
  rw [secondEdgeApp]
  exact IsIso.comp_isIso' h₃ (IsIso.comp_isIso' h₁ h₂)

/-- The co-edge morphism in degree zero is a natural isomorphism. -/
instance isIso_secondEdge_zero : IsIso (secondEdge P Q 0) :=
  NatIso.isIso_of_isIso_app _

end CoEdge

end Stacks.Cohomology.RightDerivedCoEdge

end
