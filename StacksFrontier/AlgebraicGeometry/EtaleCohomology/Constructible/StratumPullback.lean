module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.StratificationRefinement
public import StacksFrontier.CategoryTheory.Sites.LocallyConstant.InverseImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtalePullbackFunctoriality

/-!
# Local constancy on the strata of a refined stratification

Inverse image along small étale base change preserves finite local constancy, and consequently a
sheaf which is finite locally constant on each stratum of one constructible stratification is
finite locally constant on each stratum of any stratification refining it.

This is what makes a common refinement useful: a finite family of constructible sheaves is
trivialized on a single stratification, namely a common refinement of the stratifications the
individual sheaves provide.

## Main results

* `AlgebraicGeometry.smallEtaleSheafPullback` — inverse image of sheaves along small étale base
  change.
* `AlgebraicGeometry.isFiniteLocallyConstant_smallEtaleSheafPullback` — it preserves finite local
  constancy.
* `AlgebraicGeometry.ConstructibleStratification.isFiniteLocallyConstant_of_refines` — local
  constancy on the strata passes to a refinement.

## References

* [Stacks Project, Tag 03RW](https://stacks.math.columbia.edu/tag/03RW)
* [Stacks Project, Tag 093Q](https://stacks.math.columbia.edu/tag/093Q)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Stacks.ConstantSheaf

namespace AlgebraicGeometry

universe v' u' u

variable (B : BigEtaleSite.{u}) (A : Type u') [Category.{v'} A]
  {FA : A → A → Type*} {CA : A → Type*} [∀ P Q, FunLike (FA P Q) (CA P) (CA Q)]
  [ConcreteCategory A FA]
  [∀ (T : B.Scheme) (V : SmallEtale B T.obj T.property),
    HasWeakSheafify ((SmallEtale.topology B T.obj T.property).over V) A]
  [∀ (S T : B.Scheme) (f : T ⟶ S),
    ((smallEtaleBaseChange B f).sheafPushforwardContinuous A
      (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]
  [∀ (S T : B.Scheme) (f : T ⟶ S) (V : SmallEtale B S.obj S.property),
    ((Over.post (X := V) (smallEtaleBaseChange B f)).sheafPushforwardContinuous A
      ((SmallEtale.topology B S.obj S.property).over V)
      ((SmallEtale.topology B T.obj T.property).over
        ((smallEtaleBaseChange B f).obj V))).IsRightAdjoint]

/-- Inverse image of sheaves along small étale base change: the functor on sheaves induced by
`AlgebraicGeometry.smallEtaleBaseChange`. -/
public abbrev smallEtaleSheafPullback {S T : B.Scheme} (f : T ⟶ S) :
    Sheaf (SmallEtale.topology B S.obj S.property) A ⥤
      Sheaf (SmallEtale.topology B T.obj T.property) A :=
  (smallEtaleBaseChange B f).sheafPullback A
    (SmallEtale.topology B S.obj S.property) (SmallEtale.topology B T.obj T.property)

/-- **Inverse image along small étale base change preserves finite local constancy.** Base change
is a continuous left exact functor between small étale sites, which have all finite limits, so
this is the general statement about inverse image along such a functor. -/
public theorem isFiniteLocallyConstant_smallEtaleSheafPullback {S T : B.Scheme} (f : T ⟶ S)
    (G : Sheaf (SmallEtale.topology B S.obj S.property) A)
    (hG : IsFiniteLocallyConstant (SmallEtale.topology B S.obj S.property) G) :
    IsFiniteLocallyConstant (SmallEtale.topology B T.obj T.property)
      ((smallEtaleSheafPullback B A f).obj G) :=
  isFiniteLocallyConstant_sheafPullback _ _ (smallEtaleBaseChange B f) G hG

/-- Inverse image along a composite of two base changes preserves finite local constancy, stated
with the composite written out, which is the form a refinement of stratifications produces. -/
public theorem isFiniteLocallyConstant_smallEtaleSheafPullback_comp {S T R : B.Scheme}
    (f : T ⟶ S) (g : R ⟶ T) (G : Sheaf (SmallEtale.topology B S.obj S.property) A)
    (hG : IsFiniteLocallyConstant (SmallEtale.topology B T.obj T.property)
      ((smallEtaleSheafPullback B A f).obj G)) :
    IsFiniteLocallyConstant (SmallEtale.topology B R.obj R.property)
      ((smallEtaleSheafPullback B A (g ≫ f)).obj G) := by
  have : IsFiniteLocallyConstant (SmallEtale.topology B R.obj R.property)
      ((smallEtaleSheafPullback B A f ⋙ smallEtaleSheafPullback B A g).obj G) :=
    isFiniteLocallyConstant_smallEtaleSheafPullback B A g _ hG
  exact isFiniteLocallyConstant_congr _ ((smallEtaleSheafPullbackCompIso B R T S g f A).app G)

namespace ConstructibleStratification

variable {B} {X : B.Scheme} {U : X.obj.Opens}

/-- **Local constancy on the strata passes to a refinement.** If a sheaf becomes finite locally
constant after restriction to each stratum of `s`, and `r` refines `s`, then it becomes finite
locally constant after restriction to each stratum of `r`: a stratum of `r` factors through a
stratum of `s`, and inverse image preserves finite local constancy. -/
public theorem isFiniteLocallyConstant_of_refines {r s : ConstructibleStratification B X U}
    (F : Sheaf (SmallEtale.topology B X.obj X.property) A)
    (hs : ∀ l, IsFiniteLocallyConstant
      (SmallEtale.topology B (s.piece l).obj (s.piece l).property)
      ((smallEtaleSheafPullback B A (s.inclusion l)).obj F))
    (hrs : FactorsThroughStrata r s) (k : Fin r.n) :
    IsFiniteLocallyConstant (SmallEtale.topology B (r.piece k).obj (r.piece k).property)
      ((smallEtaleSheafPullback B A (r.inclusion k)).obj F) := by
  obtain ⟨l, g, hg⟩ := hrs k
  have hbase := isFiniteLocallyConstant_smallEtaleSheafPullback_comp B A (s.inclusion l) g F
    (hs l)
  rw [hg] at hbase
  exact hbase

end ConstructibleStratification

end AlgebraicGeometry

end
