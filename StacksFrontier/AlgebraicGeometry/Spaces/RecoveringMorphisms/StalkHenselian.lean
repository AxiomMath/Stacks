module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.StrictlyHenselianTransport
public import StacksFrontier.AlgebraicGeometry.Spaces.RecoveringMorphisms.InverseImageStalk
public import StacksFrontier.AlgebraicGeometry.Spaces.RecoveringMorphisms.StructureSheafHenselian

/-!
# The stalks at a geometric point through a morphism of small étale topoi are strictly henselian

Let `(g, g♯)` be a morphism of the small étale ringed topoi of two algebraic spaces and `x̄` a
geometric point of `X`.  The functor `F ↦ (g⁻¹F)_x̄` is left exact and a left adjoint, and the
structure sheaf of `Y` is locally local and has étale-local roots of standard étale polynomials,
so the transported ring `R = (g⁻¹𝒪_Y)_x̄` is a strictly henselian local ring; the same argument
for the stalk functor at `x̄` alone shows that `𝒪_{X,x̄}` is.  These are the two hypotheses on
rings of Stacks 04GX that the proof of Stacks 04KL uses, the first being the point where the
abstract morphism `g` has to be dealt with: no geometric point of `Y` corresponds to the point
`g ∘ x̄` of the topos of `Y` a priori.

## Main results

* `AlgebraicGeometry.Space.strictlyHenselianLocalRing_invStalkRing`: the ring `(g⁻¹𝒪_Y)_x̄` is
  a strictly henselian local ring.
* `AlgebraicGeometry.Space.strictlyHenselianLocalRing_structureStalk`: the ring `𝒪_{X,x̄}` is a
  strictly henselian local ring.

## References

* [Stacks Project, Tag 04KL](https://stacks.math.columbia.edu/tag/04KL)
* [Stacks Project, Tag 04GX](https://stacks.math.columbia.edu/tag/04GX)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {X Y : AlgebraicSpaces B S hS}
  (g : RingedToposHom (smallEtaleRingedTopos B S hS X) (smallEtaleRingedTopos B S hS Y))
  (x : GeometricPoint B S hS X.1)

/-- The functor `F ↦ (g⁻¹F)_x̄` is a left adjoint. -/
instance : (invStalk g x).IsLeftAdjoint := by
  have : g.toToposHom.inverseImage.IsLeftAdjoint := g.toToposHom.adj.isLeftAdjoint
  exact Functor.isLeftAdjoint_comp _ _

/-- The category of sheaves of sets on the small étale site of `Z` has binary coproducts. -/
instance (Z : AlgebraicSpaces B S hS) :
    HasColimitsOfShape (Discrete WalkingPair) (Sheaf (SmallEtale.topology B S hS Z.1) (Type u)) :=
  have : HasSheafify (SmallEtale.topology B S hS Z.1) (Type u) :=
    SmallEtale.instHasSheafify B S hS Z.1 (Type u)
  have : HasWeakSheafify (SmallEtale.topology B S hS Z.1) (Type u) := inferInstance
  have : HasColimitsOfShape (Discrete WalkingPair) (Type u) := inferInstance
  Sheaf.instHasColimitsOfShape

/-- The sheaf of units of the structure sheaf of `Z` has a binary coproduct with itself. -/
instance (Z : AlgebraicSpaces B S hS) :
    HasBinaryCoproduct (RingedTopos.units (smallEtaleRingedTopos B S hS Z))
      (RingedTopos.units (smallEtaleRingedTopos B S hS Z)) :=
  HasColimitsOfShape.has_colimit _

/-- **`R = (g⁻¹𝒪_Y)_x̄` is a strictly henselian local ring.** -/
instance strictlyHenselianLocalRing_invStalkRing :
    StrictlyHenselianLocalRing (invStalkRing g x) :=
  RingedTopos.strictlyHenselianLocalRing_map (smallEtaleRingedTopos B S hS Y) (invStalk g x)
    (structureSheaf_locallyEitherUnit Y) (structureSheaf_exists_root Y)

/-- **`𝒪_{X,x̄}` is a strictly henselian local ring.** -/
instance strictlyHenselianLocalRing_structureStalk :
    StrictlyHenselianLocalRing (structureStalk x) :=
  RingedTopos.strictlyHenselianLocalRing_map (smallEtaleRingedTopos B S hS X) (sitePt x).sheafFiber
    (structureSheaf_locallyEitherUnit X) (structureSheaf_exists_root X)

end AlgebraicGeometry.Space
