module

public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjPoint.Algebra
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjPoint.Shrink
public import StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.GluedRepresents
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedAlgebraHomUnital

/-!
# The shrunk situation agrees with the original one at the universe `u`

`AlgebraicGeometry.Space.RelativeProjSituation.shrink` replaces the graded algebra `𝒜` of
Situation 0849 by its re-presentation with sections in the universe `u` of the site. When the
sections of `𝒜` already lie in `u`, the re-presentation is isomorphic to `𝒜` as a sheaf of graded
algebras, and so the restrictions of the two to every scheme point `f : T → X` are isomorphic
sheaves of graded algebras on the scheme of `T`.

## Main definitions

* `AlgebraicGeometry.Space.RelativeProjSituation.smallAlgebraIso`: the isomorphism of the
  re-presentation with `𝒜`.
* `AlgebraicGeometry.Space.RelativeProjSituation.zariskiReadingSmallAlgebraIso` and
  `AlgebraicGeometry.Space.RelativeProjSituation.shrinkPointAlgebraIso`: the isomorphism of their
  restrictions to a scheme point.

## References

* [Stacks Project, Tag 0849](https://stacks.math.columbia.edu/tag/0849)
-/

@[expose] public noncomputable section

universe u

open CategoryTheory Opposite
open Stacks.Sheaves.GradedAlgebraEssentiallySmall (gradedPull)
open Stacks.AlgebraicGeometry.RelativeProjQcohSheaf

namespace AlgebraicGeometry.Space.RelativeProjSituation

variable (s : RelativeProjSituation.{u, u})

/-- When the module universe is already `u`, the comparison of the re-presented algebra with the
algebra is, in each degree, an isomorphism of sheaves of modules. -/
def smallAlgebraPieceIso (n : ℤ) : s.smallAlgebra.piece n ≅ s.algebra.piece n :=
  (SheafOfModules.fullyFaithfulForget _).preimageIso
    (PresheafOfModules.isoMk (fun U => (s.smallAlgebraEquiv.equiv n U).toModuleIso)
      (fun _ _ f => by ext x; exact s.smallAlgebraEquiv.naturality n f x))

/-- The isomorphism in degree `n` is the comparison on sections. -/
theorem smallAlgebraPieceIso_hom_val_app_apply (n : ℤ)
    (U : (SmallEtale s.site s.base s.containsBase s.space.1)ᵒᵖ)
    (x : (s.smallAlgebra.piece n).val.obj U) :
    (s.smallAlgebraPieceIso n).hom.val.app U x = s.smallAlgebraEquiv.equiv n U x := rfl

/-- **When the module universe is already `u`, the re-presented algebra is isomorphic to the
algebra**, as sheaves of graded algebras. -/
def smallAlgebraIso : s.smallAlgebra ≅ s.algebra :=
  SheafOfModules.GradedAlgebra.isoOfPieceIso s.smallAlgebraPieceIso
    (fun i j U x y => s.smallAlgebraEquiv_mul_app i j U x y)

/-- The restriction of the re-presented algebra to a scheme point, before forgetting to the scheme:
`f^*` of `smallAlgebra` is isomorphic to `f^*𝒜`, as the inverse image of `smallAlgebraIso`. -/
def zariskiReadingSmallAlgebraIso (T : BigFppfOver s.site s.base s.containsBase)
    (f : yoneda.obj T ⟶ s.space.1) :
    zariskiReading T (etalePointAlgebra s.smallAlgebra T f) ≅
      zariskiReading T (etalePointAlgebra s.algebra T f) :=
  haveI := isContinuous_selfOpensFunctor s.site s.base s.containsBase T
  SheafOfModules.GradedAlgebra.Iso.pushforward
    (selfOpensStructureMap s.site s.base s.containsBase T)
    ((gradedPull (X := smallEtaleRingedTopos s.site s.base s.containsBase
      (yonedaSpace s.site s.base s.containsBase T))
    (Y := smallEtaleRingedTopos s.site s.base s.containsBase s.space)
    (smallEtaleRingedToposHom s.site s.base s.containsBase (pointHom f))).mapIso s.smallAlgebraIso)

/-- The underlying graded algebra of the restriction `f^*𝒜` to a scheme point. -/
theorem situationAlgebra_pointAlgebra {t : RelativeProjSituation.{u, u}}
    (T : BigFppfOver t.site t.base t.containsBase) (f : yoneda.obj T ⟶ t.space.1) :
    situationAlgebra (t.pointAlgebra T f) = zariskiReading T (etalePointAlgebra t.algebra T f) := by
  rw [pointAlgebra_def]
  rfl

/-- **The restriction of the re-presented algebra to a scheme point is the restriction of the
algebra itself**, when the module universe is already `u`: for `f : T → X` an isomorphism of
sheaves of graded algebras on the scheme of `T` between the restriction of `smallAlgebra`, which
is the algebra at `f` of the shrunk situation, and `f^*𝒜`. -/
def shrinkPointAlgebraIso (T : BigFppfOver s.site s.base s.containsBase)
    (f : yoneda.obj T ⟶ s.space.1) :
    situationAlgebra (s.shrink.pointAlgebra T f) ≅ situationAlgebra (s.pointAlgebra T f) :=
  eqToIso (situationAlgebra_pointAlgebra (t := s.shrink) T f) ≪≫
    s.zariskiReadingSmallAlgebraIso T f ≪≫
      eqToIso (situationAlgebra_pointAlgebra (t := s) T f).symm

end AlgebraicGeometry.Space.RelativeProjSituation
