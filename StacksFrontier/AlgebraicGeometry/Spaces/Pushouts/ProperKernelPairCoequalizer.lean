module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteAffineProper
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.CoequalizerGlueing
public import StacksFrontier.AlgebraicGeometry.Spaces.UnramifiedMonoCriteria

/-!
# The coequalizer of the kernel pair of a proper morphism

Let `g : Y ⟶ X` be a proper morphism of algebraic spaces over a scheme `S` contained in a big
fppf site `B`, with `X` locally Noetherian, and let `R = Y ×_X Y` with its two projections
`s, t : R ⟶ Y`. Then `s` and `t` have a coequalizer `X'` in the category of algebraic spaces
over `S`, the morphism `X' ⟶ X` is finite and universally injective, the morphism `Y ⟶ X'` is
proper and surjective, and `X' ⟶ X` is a universal homeomorphism when `g` is surjective. This
is **Stacks 0AGG**.

This file proves clause (5) from the existence of the coequalizer and clauses (1) to (4), which
are bundled as `AlgebraicGeometry.Space.ProperKernelPairCoequalizerCore`.

## Main definitions

* `AlgebraicGeometry.Space.ProperKernelPairCoequalizerCore`: existence of the coequalizer of the
  kernel pair of a proper morphism together with clauses (1) to (4) of Stacks 0AGG.

## Main results

* `AlgebraicGeometry.Space.universalHomeomorphism_of_universallyClosed`: a surjective,
  universally injective, universally closed morphism of algebraic spaces over `S` is a
  universal homeomorphism.
* `AlgebraicGeometry.Space.isSurjective_toTarget_of_isSurjective`: the morphism from a
  coequalizer of a kernel pair to the target is surjective as soon as the morphism itself is.
* `AlgebraicGeometry.Space.properKernelPairCoequalizers_of_core`: Stacks 0AGG, given the
  existence of the coequalizer and clauses (1) to (4).

## References

* [Stacks Project, Tag 0AGG](https://stacks.math.columbia.edu/tag/0AGG)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Universal homeomorphisms from universal bijectivity and universal closedness -/

/-- A surjective, universally injective and universally closed morphism of algebraic spaces
over `S` is a universal homeomorphism. -/
theorem universalHomeomorphism_of_universallyClosed
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : F ⟶ G)
    (hsurj : IsSurjective B S hS f) (hinj : UniversallyInjective B S hS f)
    (hclosed : UniversallyClosed B S hS f) :
    UniversalHomeomorphism B S hS f := fun Z hZ g =>
  isHomeomorph_iff_continuous_isClosedMap_bijective.mpr
    ⟨continuous_pointsMap B S hS _, hclosed Z hZ g, hinj Z hZ g,
      surjective_pointsMap_of_isPullback B S hS (IsPullback.of_hasPullback g f).flip hsurj⟩

/-! ### Surjectivity of the morphism to the target -/

/-- The morphism from a coequalizer of the kernel pair of `g : Y ⟶ X` to `X` is surjective as
soon as `g` is. -/
theorem isSurjective_toTarget_of_isSurjective {X Y : AlgebraicSpaces B S hS} {g : Y ⟶ X}
    (D : KernelPairCoequalizer B S hS g) (hg : IsSurjective B S hS g.hom) :
    IsSurjective B S hS D.toTarget.hom := by
  have hfac : D.π.hom ≫ D.toTarget.hom = g.hom :=
    congrArg (fun k : Y ⟶ X => k.hom) D.fac
  have hcomp : Function.Surjective
      (pointsMap B S hS D.space.obj D.toTarget.hom ∘ pointsMap B S hS Y.obj D.π.hom) := by
    rwa [← pointsMap_comp, hfac]
  exact hcomp.of_comp

/-! ### The coequalizer of the kernel pair of a proper morphism -/

/-- Existence of the coequalizer of the kernel pair of a proper morphism onto a locally
Noetherian algebraic space, together with clauses (1) to (4) of Stacks 0AGG: the morphism from
the coequalizer to the target is finite and universally injective, and the quotient morphism is
proper and surjective. -/
structure ProperKernelPairCoequalizerCore : Prop where
  /-- A coequalizer of the kernel pair exists. -/
  nonempty_coequalizer : ∀ {X Y : AlgebraicSpaces B S hS} (g : Y ⟶ X),
    HasEtaleLocalProperty B S hS X.obj (fun W : Scheme.{u} => IsLocallyNoetherian W) →
    IsProper B S hS g.hom → Nonempty (KernelPairCoequalizer B S hS g)
  /-- Clause (1): the morphism from the coequalizer to the target is finite. -/
  isFinite_toTarget : ∀ {X Y : AlgebraicSpaces B S hS} (g : Y ⟶ X),
    HasEtaleLocalProperty B S hS X.obj (fun W : Scheme.{u} => IsLocallyNoetherian W) →
    IsProper B S hS g.hom → ∀ D : KernelPairCoequalizer B S hS g,
      IsFinite B S hS D.toTarget.hom
  /-- Clause (2): the quotient morphism is proper. -/
  isProper_π : ∀ {X Y : AlgebraicSpaces B S hS} (g : Y ⟶ X),
    HasEtaleLocalProperty B S hS X.obj (fun W : Scheme.{u} => IsLocallyNoetherian W) →
    IsProper B S hS g.hom → ∀ D : KernelPairCoequalizer B S hS g,
      IsProper B S hS D.π.hom
  /-- Clause (3): the quotient morphism is surjective. -/
  isSurjective_π : ∀ {X Y : AlgebraicSpaces B S hS} (g : Y ⟶ X),
    HasEtaleLocalProperty B S hS X.obj (fun W : Scheme.{u} => IsLocallyNoetherian W) →
    IsProper B S hS g.hom → ∀ D : KernelPairCoequalizer B S hS g,
      IsSurjective B S hS D.π.hom
  /-- Clause (4): the morphism from the coequalizer to the target is universally injective. -/
  universallyInjective_toTarget : ∀ {X Y : AlgebraicSpaces B S hS} (g : Y ⟶ X),
    HasEtaleLocalProperty B S hS X.obj (fun W : Scheme.{u} => IsLocallyNoetherian W) →
    IsProper B S hS g.hom → ∀ D : KernelPairCoequalizer B S hS g,
      UniversallyInjective B S hS D.toTarget.hom

/-- Let `g : Y ⟶ X` be a proper morphism of algebraic spaces over `S` with `X` locally
Noetherian and let `R = Y ×_X Y` with its two projections `s, t : R ⟶ Y`. Then `s` and `t` have a
coequalizer `X'` in the category of algebraic spaces over `S`, and: (1) the morphism `X' ⟶ X` is
finite; (2) the morphism `Y ⟶ X'` is proper; (3) the morphism `Y ⟶ X'` is surjective; (4) the
morphism `X' ⟶ X` is universally injective; (5) if `g` is surjective, the morphism `X' ⟶ X` is a
universal homeomorphism. Existence of the coequalizer and clauses (1) to (4) are the hypothesis
`hcore`. -/
@[stacks 0AGG "all six clauses; clause (5) is proved from the others, while existence of the \
coequalizer and clauses (1) to (4) are carried in the hypothesis"]
theorem properKernelPairCoequalizers_of_core
    (hcore : ProperKernelPairCoequalizerCore B S hS) :
    ProperKernelPairCoequalizers B S hS where
  nonempty_coequalizer := hcore.nonempty_coequalizer
  isFinite_toTarget := hcore.isFinite_toTarget
  isProper_π := hcore.isProper_π
  isSurjective_π := hcore.isSurjective_π
  universallyInjective_toTarget := hcore.universallyInjective_toTarget
  universalHomeomorphism_toTarget := by
    intro X Y g hN hproper hsurj D
    exact universalHomeomorphism_of_universallyClosed B S hS D.toTarget.hom
      (isSurjective_toTarget_of_isSurjective B S hS D hsurj)
      (hcore.universallyInjective_toTarget g hN hproper D)
      ((isFinite_iff_isAffineHom_and_isProper B S hS D.space.property X.property
        D.toTarget.hom).mp (hcore.isFinite_toTarget g hN hproper D)).2.2.2

end AlgebraicGeometry.Space

end
