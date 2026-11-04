module

public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.CategoryTheory.Abelian.ShortExact
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import Mathlib.CategoryTheory.Sites.EpiMono
public import StacksFrontier.Algebra.Homology.DerivedCategory.AcyclicObjects
public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedFunctorInjective
public import StacksFrontier.AlgebraicGeometry.Spaces.Finite
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleToposMorphism
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.CokernelFinitePresentation
public import StacksFrontier.CategoryTheory.Sites.Modules.InverseImage.AbelianSheaf
public import StacksFrontier.CategoryTheory.Sites.Topos.AbelianInverseImageExact
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleCohomology
public import StacksFrontier.CategoryTheory.Sites.Topos.AbelianPushforwardExact
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Exactness of the small étale direct image on abelian sheaves

Let `f : X ⟶ Y` be an integral morphism of algebraic spaces over a scheme `S` contained in a
big fppf site `B`.  Stacks 0A4K asserts that the direct image
`f_* : Ab(X_étale) ⥤ Ab(Y_étale)` on the small étale sites is exact, and that consequently
`R^p f_* = 0` for `p > 0`.

The source proves this by reducing, along an étale covering of `Y`, to the case of schemes
(Stacks 03LR part (2) and Stacks 03ZQ) and then quoting Étale Cohomology Lemma 59.43.5
(Stacks 04C2).  What 04C2 actually supplies is its part (1): the small étale direct image along
an integral morphism *transforms surjections into surjections*.  Its part (4), exactness on
abelian sheaves, is then formally deduced from part (1) by Modules on Sites Lemma 18.15.2
(Stacks 04DB).

Everything on this side of 04C2 part (1) is proved here, unconditionally and in general:

* the direct image of *abelian* sheaves along a morphism of topoi, its unconditional left
  exactness and additivity, and the implication of **Stacks 04DB** from its condition (1) are
  `Stacks.Topos.AbelianPushforward.abelianPushforward` and its siblings in
  `StacksFrontier.CategoryTheory.Sites.Topos.AbelianPushforwardExact`;
* the vanishing of the higher right derived functors of an exact functor is proved;
* the small étale abelian sheaves on an algebraic space are shown to have enough injectives,
  which is what makes `R^p f_*` meaningful at all.

The single missing input, 04C2 part (1) transported to algebraic spaces, is carried as the
explicit named hypothesis `hepi` of the two main theorems.  Because they carry it, they do not
carry the `@[stacks 0A4K]` attribute.

## Main results

* `CategoryTheory.Functor.isZero_rightDerivedPlus_of_exact`: an exact additive functor out of an
  abelian category with enough injectives has vanishing higher right derived functors.
* `AlgebraicGeometry.Space.smallEtaleAbelianPushforward_exact` and
  `AlgebraicGeometry.Space.smallEtaleAbelianPushforward_rightDerivedPlus_isZero` are the two
  conclusions of Stacks 0A4K, each carrying `hepi`.

## Implementation notes

The abelian direct image itself, its unconditional left exactness and additivity, and the
passage from surjectivity on sheaves of sets to surjectivity on abelian sheaves — the only
non-formal step of 04DB — are all in
`StacksFrontier.CategoryTheory.Sites.Topos.AbelianPushforwardExact`.  This module transports them
to the small étale site of an algebraic space, where the vanishing of `R^p f_*` becomes
meaningful.

`HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso` is given a raised priority,
as in `StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedFunctorInjective`; without it
the search for the `HasRightDerivedFunctor` instance needed by
`CategoryTheory.Functor.le_rightAcyclic` does not terminate within the default budget.

The general statements assume `HasSheafify` for the coefficient category rather than `Abelian`
for the sheaf category, and that is not a matter of taste.  An abstract hypothesis
`[Abelian (Sheaf J AddCommGrpCat)]` does *not* yield `HasBinaryBiproducts (Sheaf J
AddCommGrpCat)`: the `HasZeroMorphisms` instance that search finds for a sheaf category comes
from the coefficient category, not from that hypothesis, so `Abelian.hasBinaryBiproducts` does
not match the goal and additivity cannot be derived.  With `HasSheafify` the canonical
`CategoryTheory.sheafIsAbelian` is in play and everything lines up.

The free universe of the coefficient category does not bite here: every instance the statements
need — `HasSheafify`, `WEqualsLocallyBijective` and `HasDerivedCategory` — resolves by instance
search for `Sheaf (SmallEtale.topology B S hS Z.obj) AddCommGrpCat.{u + 1}`.

## References

* [Stacks Project, Tag 0A4K](https://stacks.math.columbia.edu/tag/0A4K)
* [Stacks Project, Tag 04C2](https://stacks.math.columbia.edu/tag/04C2)
* [Stacks Project, Tag 04DB](https://stacks.math.columbia.edu/tag/04DB)
* [Stacks Project, Tag 04JC](https://stacks.math.columbia.edu/tag/04JC)
* [Stacks Project, Tag 03LR](https://stacks.math.columbia.edu/tag/03LR)
* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2)
* [Stacks Project, Tag 015A](https://stacks.math.columbia.edu/tag/015A)
* [Stacks Project, Tag 015C](https://stacks.math.columbia.edu/tag/015C)
* [Stacks Project, Tag 05T8](https://stacks.math.columbia.edu/tag/05T8)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

attribute [local instance] HasDerivedCategory.standard

attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

/-! ### Higher right derived functors of an exact functor -/

namespace CategoryTheory.Functor

/-- An exact additive functor between abelian categories, out of a category with enough
injectives, has vanishing higher right derived functors.

Every object is right acyclic, by Stacks 05T8 applied to the class of *all* objects: a short
exact sequence is carried to a short exact sequence precisely because the functor is exact.
Stacks 015C then converts right acyclicity into the vanishing, the comparison in degree zero
being automatic for a left exact functor. -/
@[sga "4 V 0.4" "special case"]
theorem isZero_rightDerivedPlus_of_exact {A B : Type*} [Category* A] [Category* B]
    [Abelian A] [Abelian B] [HasDerivedCategory A] [HasDerivedCategory B]
    (F : A ⥤ B) [F.Additive] [EnoughInjectives A]
    (hF : exactFunctor A B F) (X : A) (p : ℤ) (hp : 0 < p) :
    IsZero ((F.rightDerivedPlus p).obj X) := by
  rw [exactFunctor_iff] at hF
  have hlim : PreservesFiniteLimits F := hF.1
  have hcolim : PreservesFiniteColimits F := hF.2
  have hac : (⊤ : ObjectProperty A) ≤ F.rightAcyclic :=
    F.le_rightAcyclic ⊤ (fun Z => ⟨Z, trivial, 𝟙 Z, inferInstance⟩)
      (fun S hS _ _ => ⟨trivial, hS.map_of_exact F⟩)
  exact ((F.rightAcyclic_iff_isIso_and_isZero_rightDerivedPlus X).2 hlim).1
    (hac X trivial) p hp

end CategoryTheory.Functor

/-! ### The small étale direct image along an integral morphism -/

namespace AlgebraicGeometry.Space

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X Y : AlgebraicSpaces B S hS}

/-- **Stacks 0A4K, exactness**, with the input owed to Étale Cohomology carried as the explicit
hypothesis `hepi`.

For an integral morphism `f : X ⟶ Y` of algebraic spaces the direct image on the abelian
sheaves of the small étale sites is exact, *given* that the direct image on sheaves of sets
transforms surjections into surjections.  That last statement is Stacks 04C2 part (1) for
schemes, transported to algebraic spaces along an étale covering of `Y` by Stacks 03LR and
Stacks 03ZQ; it is not available, and it is the whole mathematical content left.  The step from
it to exactness, which is Stacks 04DB, is
  `Stacks.Topos.AbelianPushforward.abelianPushforward_exact`. -/
theorem smallEtaleAbelianPushforward_exact (f : X ⟶ Y)
    (hf : IsIntegralHom B S hS f.hom)
    (hepi : IsIntegralHom B S hS f.hom →
      (smallToposMorphism B S hS f).pushforward.PreservesEpimorphisms) :
    exactFunctor (Sheaf (SmallEtale.topology B S hS X.obj) AddCommGrpCat.{u + 1})
      (Sheaf (SmallEtale.topology B S hS Y.obj) AddCommGrpCat.{u + 1})
      (Stacks.Topos.AbelianPushforward.abelianPushforward (SmallEtale.topology B S hS X.obj)
        (smallToposMorphism B S hS f)) :=
  Stacks.Topos.AbelianPushforward.abelianPushforward_exact_of_preservesEpimorphisms
    (SmallEtale.topology B S hS X.obj) (smallToposMorphism B S hS f)
    (Stacks.Topos.AbelianPushforward.preservesEpimorphisms_abelianPushforward
      (SmallEtale.topology B S hS X.obj) (smallToposMorphism B S hS f) (hepi hf))

/-- **Stacks 0A4K, vanishing of the positive-degree higher direct images**, with the same
explicit hypothesis `hepi` as `AlgebraicGeometry.Space.smallEtaleAbelianPushforward_exact`.

Given exactness, the vanishing is formal: it is
`CategoryTheory.Functor.isZero_rightDerivedPlus_of_exact`, since the abelian sheaves on the
small étale site of `X` have enough injectives.  The `Functor.Additive` instance the statement
needs is `Stacks.Topos.AbelianPushforward.abelianPushforward_additive`, which holds
  unconditionally. -/
theorem smallEtaleAbelianPushforward_rightDerivedPlus_isZero (f : X ⟶ Y)
    (hf : IsIntegralHom B S hS f.hom)
    (hepi : IsIntegralHom B S hS f.hom →
      (smallToposMorphism B S hS f).pushforward.PreservesEpimorphisms)
    (F : Sheaf (SmallEtale.topology B S hS X.obj) AddCommGrpCat.{u + 1})
    (p : ℤ) (hp : 0 < p) :
    IsZero (((Stacks.Topos.AbelianPushforward.abelianPushforward (SmallEtale.topology B S hS X.obj)
      (smallToposMorphism B S hS f)).rightDerivedPlus p).obj F) :=
  Functor.isZero_rightDerivedPlus_of_exact _
    (smallEtaleAbelianPushforward_exact B S hS f hf hepi) F p hp

end AlgebraicGeometry.Space

end
