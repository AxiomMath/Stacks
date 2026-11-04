module

public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPushforward.AdjunctionForRingedTopoi
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPushforward.Existence
public import StacksFrontier.CategoryTheory.Sites.Simplicial.RingedToposMorphism
public import StacksFrontier.CategoryTheory.Sites.Simplicial.RingedToposMorphismComponentPushforward
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPushforward.DerivedUnitAfterAnExactFaithfulFunctor
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedCategory.CohomologyOnAnOpenSubspace

/-!
# The derived direct image of sheaves of modules along a morphism of ringed simplicial sites

With the notation and hypotheses of Stacks 0DH0 — two simplicial sites in the cocontinuous case
of Stacks 09WE, sheaves of rings `𝒪` and `𝒪'` on their total sites, a morphism `(h, h♯)` of
ringed simplicial sites, the induced morphisms of ringed topoi `h_{total}` and `h_n`, and the
canonical morphisms `g_n` and `g'_n` from the ringed topoi of the simplicial components of
degree `n` — Stacks 0DH1 asserts that for `K` in the unbounded derived category of
`𝒪`-modules,

`(g'_n)^* Rh_{total,*} K = Rh_{n,*} g_n^* K`.

## Main definitions

* `Stacks.Cohomology.DerivedPushforward.derivedPushforwardUnit`: the canonical comparison from
  the degreewise direct image of sheaves of modules along a morphism of ringed topoi into the
  derived direct image `Rf_*` of
  `Stacks.Cohomology.DerivedPushforward.derivedPushforward`, with
  `.hasPointwiseRightDerivedFunctor_pushforwardOnHomotopy` and
  `.isIso_derivedPushforwardUnit_app_of_isKInjective` saying that K-injective resolutions
  compute it.
* `CategoryTheory.SimplicialSiteSituation.derivedComponentPullbackModules`: the functor `Lg_n^*`
  on unbounded derived categories of sheaves of modules. Since `g_n^*` is exact, it is the
  degreewise pullback, which is the source's first step.
* `CategoryTheory.CocontinuousSimplicialSite.RingedMorphism.derivedTotalPushforwardModulesUnit`
  and `.derivedComponentPushforwardModulesUnit`: the canonical comparisons from degreewise
  direct image into `Rh_{total,*}` and into `Rh_{n,*}`.
* In `CategoryTheory.CocontinuousSimplicialSite.RingedMorphism`,
  `derivedTotalPushforwardRestrictModulesUnit` and
  `derivedRestrictTotalPushforwardModulesUnit`: the comparisons exhibiting the two sides of the
  source's identity as right derived functors of the two underived composites.

## Main results

* `CategoryTheory.SimplicialSiteSituation.componentPullbackModules_preservesFiniteLimits` and
  `.componentPullbackModules_preservesFiniteColimits`: **pullback of sheaves of modules to a
  simplicial component is exact**. This is the source's opening observation, that
  `g_n^* = g_n^{-1}` because the component structure sheaf is the restriction of the total one,
  so that `Lg_n^*` is computed by applying `g_n^*` to any representative complex.
* In `CategoryTheory.CocontinuousSimplicialSite.RingedMorphism`,
  `isIso_derivedComponentPushforwardModulesUnit_app_componentPullback`: the pullback to a
  component of a K-injective complex of `𝒪`-modules computes `Rh_{n,*}`. This is where the
  source passes to abelian sheaves through Stacks 0D6J and invokes Stacks 0D97.
* In `CategoryTheory.CocontinuousSimplicialSite.RingedMorphism`,
  `isRightDerivedFunctor_derivedTotalPushforwardRestrictModulesUnit` and
  `isRightDerivedFunctor_derivedRestrictTotalPushforwardModulesUnit`: both sides of the source's
  identity are right derived functors of the corresponding underived composite.
* `CategoryTheory.CocontinuousSimplicialSite.RingedMorphism.derivedComponentPushforwardModulesIso`:
  **Stacks 0DH1**, case (B), with `.derivedComponentPushforwardModulesIso_fac` pinning the
  isomorphism down.

## Implementation notes

This file treats case (B) of Stacks 09WE. Case (A) is
`StacksFrontier/CategoryTheory/Sites/Simplicial/RingedToposMorphismContinuousDerivedPushforward.lean`,
which runs the same argument.

### The equality of the source is an isomorphism of functors

The two sides are built by different constructions — a right derived functor of a direct image
on one side, the same preceded and followed by different exact functors on the other — so the
source's `=` is read here, as it is for the abelian statement of Stacks 0D97 in
`StacksFrontier/CategoryTheory/Sites/Simplicial/TotalMorphismDerivedPushforward.lean`, as a natural
isomorphism of functors on the unbounded derived category.

The isomorphism is not an arbitrary one. Both sides are exhibited as right derived functors of
one and the same functor on the unbounded homotopy category of `𝒪`-modules, identified through
the canonical comparison of Stacks 0DH0,
`CategoryTheory.CocontinuousSimplicialSite.RingedMorphism.componentPushforwardModulesIso` — the
mate of the degreewise square of direct images, which is invertible — and the isomorphism is the
induced comparison of two right derived functors, `rightDerivedNatIso`.
`derivedComponentPushforwardModulesIso_fac` records what that means: the isomorphism is the
unique morphism of functors whose composite with the canonical comparison into the first right
derived functor is the underived comparison followed by the canonical comparison into the
second. Uniqueness is the universal property of a right derived functor, so this determines the
isomorphism completely.

### The source's argument

That `Rh_{total,*}` followed by `Lg'_n^*` is a right derived functor is formal: the direct image
is computed by K-injective complexes and the pullback is exact. For the other side one needs that
`g_n^* I` computes `Rh_{n,*}` for a K-injective complex `I` of `𝒪`-modules. Pullback of modules to
a component need not preserve K-injectivity — its left adjoint, the lower shriek of Stacks 0D72,
is exact only under a flatness condition that Stacks 0DH0 does not impose — and the source does
not claim it: it forgets the module structure (Stacks 0D6J) and invokes the abelian statement
(Stacks 0D97). The same is done here, on the unit of `Rh_{n,*}` at `g_n^* I`:

* forgetting the module structure is exact and reflects isomorphisms, and carries `h_{n,*}` to
  the degreewise direct image of abelian sheaves and `g_n^*` to restriction to the component
  (`componentPushforwardModulesToSheafIso`, `componentPullbackModulesToSheafIso`), so the unit may
  be checked on underlying abelian complexes
  (`Stacks.Cohomology.UnboundedComplexes.isIso_rightDerivedUnit_of_forget`);
* there, the underlying complex of a K-injective complex of `𝒪_n`-modules computes the abelian
  `Rh_{n,*}`, by Stacks 0D6J for the cocontinuous functor of degree `n`;
* and the restriction `I_ab|_{𝒞_n}` computes the abelian `Rh_{n,*}` by the argument of
  Stacks 0D97: a K-injective resolution `I_ab ⟶ J` restricts to one (Stacks 09WH), and
  `h_{n,*}` of the restriction is the restriction of `h_{total,*}(I_ab ⟶ J)` (Stacks 0D96),
  which is a quasi-isomorphism by Stacks 0D6J for the cocontinuous total functor
  (`isIso_derivedAbelianPushforwardUnit_app_abelianComponent` in
  `CategoryTheory.CocontinuousSimplicialSite.Morphism`).

### Exactness of the pullback to a component

That `g_n^*` is exact is proved unconditionally. Right exactness is the general fact that a
pullback of sheaves of modules is a left adjoint, Stacks 03DC part (2). Left exactness uses the
special feature of a component inclusion: its structure map is invertible, so by
`CategoryTheory.SimplicialSiteSituation.componentPullbackUnderlyingIso` the underlying sheaf of
`g_n^* ℱ` is `g_n^{-1}` of the underlying sheaf of `ℱ`, which is left exact because `g_n` is a
morphism of topoi; the underlying-sheaf functor on sheaves of modules preserves finite limits
and reflects isomorphisms, hence reflects finite limits.

### Derived direct images

`Rh_{total,*}` and `Rh_{n,*}` are the unbounded derived direct images of sheaves of modules of
`Stacks.Cohomology.DerivedPushforward.derivedPushforward`, which exist for every morphism of
ringed topoi with no further hypothesis: sheaves of modules on a ringed topos form a
Grothendieck abelian category, so every complex admits a quasi-isomorphism into a K-injective
one and Stacks 070K applies. The two instances that this requires of the degreewise direct
image are supplied locally here rather than taken from the ambient instance set, since the
derived category is pinned by the local instance `HasDerivedCategory.standard`.

## References

* [Stacks Project, Tag 0DH1](https://stacks.math.columbia.edu/tag/0DH1)
* [Stacks Project, Tag 0DH0](https://stacks.math.columbia.edu/tag/0DH0)
* [Stacks Project, Tag 0D97](https://stacks.math.columbia.edu/tag/0D97)
* [Stacks Project, Tag 0D96](https://stacks.math.columbia.edu/tag/0D96)
* [Stacks Project, Tag 0D72](https://stacks.math.columbia.edu/tag/0D72)
* [Stacks Project, Tag 09WE](https://stacks.math.columbia.edu/tag/09WE)
* [Stacks Project, Tag 09WH](https://stacks.math.columbia.edu/tag/09WH)
* [Stacks Project, Tag 07A7](https://stacks.math.columbia.edu/tag/07A7)
* [Stacks Project, Tag 03DC](https://stacks.math.columbia.edu/tag/03DC)
* [Stacks Project, Tag 0D6J](https://stacks.math.columbia.edu/tag/0D6J)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Cohomology.DerivedPushforward

universe u

attribute [local instance] HasDerivedCategory.standard

namespace Stacks.Cohomology.DerivedPushforward

/-! ### The derived direct image of sheaves of modules along a morphism of ringed topoi

The degreewise direct image, followed by localization, has a pointwise right derived functor on
the whole unbounded derived category, because sheaves of modules on a ringed topos form a
Grothendieck abelian category. Both halves of that statement — existence, and invertibility of
the canonical comparison on a K-injective complex — are recorded here at the single universe at
which the simplicial ringed topoi of Stacks 0D72 live. -/

section DerivedPushforwardOfModules

variable (X Y : RingedTopos.{u, u, u})
  [X.J.HasSheafCompose (forget RingCat.{u})] [Y.J.HasSheafCompose (forget RingCat.{u})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [HasSheafify X.J AddCommGrpCat.{u}] [HasSheafify Y.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]

omit [Y.J.HasSheafCompose (forget AddCommGrpCat.{u})] in
/-- K-injective resolutions compute the derived direct image of sheaves of modules along a
morphism of ringed topoi pointwise. -/
theorem hasPointwiseRightDerivedFunctor_pushforwardOnHomotopy (f : RingedToposHom X Y) :
    (pushforwardOnHomotopy.{u, u, u, u, u, u} f).HasPointwiseRightDerivedFunctor
      (HomotopyCategory.quasiIso (SheafOfModules.{u} (SheafOfModules.Tensor.ringSheaf X.O))
        (ComplexShape.up ℤ)) :=
  (Functor.hasPointwiseRightDerivedFunctor_and_isIso_app_of_exists_quasiIso_isKInjective.{u,
      u + 1, u + 1, u + 1, u + 1, u + 1} _
    (Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.exists_quasiIso_isKInjective X)).1

attribute [local instance] hasPointwiseRightDerivedFunctor_pushforwardOnHomotopy

/-- The canonical comparison from the degreewise direct image of sheaves of modules into the
derived direct image `Rf_*`. -/
abbrev derivedPushforwardUnit (f : RingedToposHom X Y) :
    pushforwardOnHomotopy.{u, u, u, u, u, u} f ⟶
      DerivedCategory.Qh ⋙ derivedPushforward.{u, u, u, u, u, u} f :=
  (pushforwardOnHomotopy.{u, u, u, u, u, u} f).totalRightDerivedUnit DerivedCategory.Qh
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (SheafOfModules.Tensor.ringSheaf X.O))
      (ComplexShape.up ℤ))

omit [Y.J.HasSheafCompose (forget AddCommGrpCat.{u})] in
/-- A K-injective complex of sheaves of modules computes the derived direct image: on it the
canonical comparison `f_* I ⟶ Rf_* I` is invertible. -/
theorem isIso_derivedPushforwardUnit_app_of_isKInjective (f : RingedToposHom X Y)
    (I : CochainComplex (SheafOfModules.{u} (SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (hI : I.IsKInjective) :
    IsIso ((derivedPushforwardUnit X Y f).app
      ((HomotopyCategory.quotient (SheafOfModules.{u} (SheafOfModules.Tensor.ringSheaf X.O))
        (ComplexShape.up ℤ)).obj I)) :=
  (Functor.hasPointwiseRightDerivedFunctor_and_isIso_app_of_exists_quasiIso_isKInjective.{u,
      u + 1, u + 1, u + 1, u + 1, u + 1} _
      (Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.exists_quasiIso_isKInjective X)).2
    DerivedCategory.Qh (derivedPushforward.{u, u, u, u, u, u} f)
    (derivedPushforwardUnit X Y f) I hI

end DerivedPushforwardOfModules

end Stacks.Cohomology.DerivedPushforward

namespace CategoryTheory

attribute [local instance]
  Stacks.Cohomology.DerivedPushforward.hasPointwiseRightDerivedFunctor_pushforwardOnHomotopy

namespace SimplicialSiteSituation

/-! ### Pullback of sheaves of modules to a simplicial component is exact -/

variable (S : SimplicialSiteSituation.{u}) (O : Sheaf S.totalTopology CommRingCat.{u})
  (n : SimplexCategory)

/-- **Pullback of sheaves of modules to the simplicial component of degree `n` is left exact.**
The component structure sheaf is the restriction of the total one, so the component structure
map is invertible and the pullback of modules has the inverse image of sheaves of sets as its
underlying sheaf, by
`CategoryTheory.SimplicialSiteSituation.componentPullbackUnderlyingIso`; the inverse image is
left exact because `g_n` is a morphism of topoi, and the underlying-sheaf functor on sheaves of
modules preserves finite limits and reflects isomorphisms, hence reflects finite limits.

This is the source's observation that `g_n^* = g_n^{-1}` is exact, which is what makes `Lg_n^*`
computable on any representative complex. -/
@[stacks 0DH1 "exactness of the pullback of modules to a component", sga "4 IV 13.7" "special case"]
theorem componentPullbackModules_preservesFiniteLimits :
    PreservesFiniteLimits (componentRingedToposHom S O n).toModulesHom.pullbackModules := by
  have := Sheaf.moduleSheafFunctor_preservesFiniteLimits
    ((Stacks.SheafOfModules.Tensor.ringSheaf (J := (S.totalRingedTopos O).J))
        (S.totalRingedTopos O).O)
  have := Sheaf.moduleSheafFunctor_preservesFiniteLimits
    ((Stacks.SheafOfModules.Tensor.ringSheaf (J := (S.componentRingedTopos O n).J))
        (S.componentRingedTopos O n).O)
  have := (componentRingedToposHom S O n).toToposHom.preservesFiniteLimits
  have : PreservesFiniteLimits ((componentRingedToposHom S O n).toModulesHom.pullbackModules ⋙
      Sheaf.moduleSheafFunctor ((Stacks.SheafOfModules.Tensor.ringSheaf
          (J := (S.componentRingedTopos O n).J))
        (S.componentRingedTopos O n).O)) :=
    preservesFiniteLimits_of_natIso (componentPullbackUnderlyingIso S O n).symm
  exact preservesFiniteLimits_of_reflects_of_preserves _
    (Sheaf.moduleSheafFunctor ((Stacks.SheafOfModules.Tensor.ringSheaf
        (J := (S.componentRingedTopos O n).J))
      (S.componentRingedTopos O n).O))

/-- **Pullback of sheaves of modules to the simplicial component of degree `n` is right exact**,
being a left adjoint. This is the finite case of Stacks 03DC part (2). -/
@[stacks 0DH1 "exactness of the pullback of modules to a component"]
theorem componentPullbackModules_preservesFiniteColimits :
    PreservesFiniteColimits (componentRingedToposHom S O n).toModulesHom.pullbackModules := by
  have := RingedToposHom.pullbackModules_preservesColimitsOfSize.{_, _, _, _, _, _, u, u}
    (componentRingedToposHom S O n)
  exact PreservesColimitsOfSize.preservesFiniteColimits _

attribute [local instance] componentPullbackModules_preservesFiniteLimits
  componentPullbackModules_preservesFiniteColimits

/-- `Lg_n^*`: pullback of sheaves of modules to the simplicial component of degree `n`, read on
unbounded derived categories. The pullback being exact, this is the degreewise pullback and no
resolution is involved. -/
abbrev derivedComponentPullbackModules :
    DerivedCategory (SheafOfModules.{u}
        ((Stacks.SheafOfModules.Tensor.ringSheaf (J := (S.totalRingedTopos O).J))
        (S.totalRingedTopos O).O)) ⥤
      DerivedCategory (SheafOfModules.{u}
          ((Stacks.SheafOfModules.Tensor.ringSheaf (J := (S.componentRingedTopos O n).J))
        (S.componentRingedTopos O n).O)) :=
  (componentRingedToposHom S O n).toModulesHom.pullbackModules.mapDerivedCategory

end SimplicialSiteSituation

attribute [local instance]
  SimplicialSiteSituation.componentPullbackModules_preservesFiniteLimits
  SimplicialSiteSituation.componentPullbackModules_preservesFiniteColimits

namespace CocontinuousSimplicialSite.RingedMorphism

variable {C C' : CocontinuousSimplicialSite.{u}}
  {O : Sheaf C.situation.totalTopology CommRingCat.{u}}
  {O' : Sheaf C'.situation.totalTopology CommRingCat.{u}}
  (h : RingedMorphism C C' ((Stacks.SheafOfModules.Tensor.ringSheaf
      (J := C.situation.totalTopology)) O)
    ((Stacks.SheafOfModules.Tensor.ringSheaf (J := C'.situation.totalTopology)) O'))
  (n : SimplexCategory)

/-! ### The two derived direct images -/

/-- `Rh_{total,*}`: the unbounded derived direct image of sheaves of modules along the morphism
of total ringed topoi of Stacks 0DH0. -/
abbrev derivedTotalPushforwardModules :
    DerivedCategory (SheafOfModules.{u}
        ((Stacks.SheafOfModules.Tensor.ringSheaf (J := (C.situation.totalRingedTopos O).J))
        (C.situation.totalRingedTopos O).O)) ⥤
      DerivedCategory (SheafOfModules.{u}
          ((Stacks.SheafOfModules.Tensor.ringSheaf (J := (C'.situation.totalRingedTopos O').J))
        (C'.situation.totalRingedTopos O').O)) :=
  derivedPushforward.{u, u, u, u, u, u} h.totalRingedToposHom

/-- The canonical comparison from the degreewise direct image along the total morphism into
`Rh_{total,*}`. -/
abbrev derivedTotalPushforwardModulesUnit :
    pushforwardOnHomotopy.{u, u, u, u, u, u} h.totalRingedToposHom ⟶
      DerivedCategory.Qh ⋙ derivedTotalPushforwardModules h :=
  derivedPushforwardUnit _ _ h.totalRingedToposHom

/-- `Rh_{n,*}`: the unbounded derived direct image of sheaves of modules along the morphism of
component ringed topoi of simplicial degree `n` of Stacks 0DH0. -/
abbrev derivedComponentPushforwardModules :
    DerivedCategory (SheafOfModules.{u}
        ((Stacks.SheafOfModules.Tensor.ringSheaf (J := (C.situation.componentRingedTopos O n).J))
            (C.situation.componentRingedTopos O n).O)) ⥤
      DerivedCategory (SheafOfModules.{u}
          ((Stacks.SheafOfModules.Tensor.ringSheaf
              (J := (C'.situation.componentRingedTopos O' n).J))
        (C'.situation.componentRingedTopos O' n).O)) :=
  derivedPushforward.{u, u, u, u, u, u} (h.componentRingedToposHom n)

/-- The canonical comparison from the degreewise direct image in simplicial degree `n` into
`Rh_{n,*}`. -/
abbrev derivedComponentPushforwardModulesUnit :
    pushforwardOnHomotopy.{u, u, u, u, u, u} (h.componentRingedToposHom n) ⟶
      DerivedCategory.Qh ⋙ derivedComponentPushforwardModules h n :=
  derivedPushforwardUnit _ _ (h.componentRingedToposHom n)

/-! ### The two sides of the source's identity as right derived functors -/

/-- The comparison from the degreewise direct image along the total morphism followed by the
degreewise pullback to the component of degree `n`, into `Rh_{total,*}` followed by `Lg'_n^*`. -/
def derivedTotalPushforwardRestrictModulesUnit :
    h.totalRingedToposHom.pushforwardModules.mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        (C'.situation.componentRingedToposHom O' n).toModulesHom.pullbackModules.mapHomotopyCategory
          (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ (derivedTotalPushforwardModules h ⋙
        C'.situation.derivedComponentPullbackModules O' n) :=
  Functor.whiskerLeft
      (h.totalRingedToposHom.pushforwardModules.mapHomotopyCategory (ComplexShape.up ℤ))
      (C'.situation.componentRingedToposHom O' n
        ).toModulesHom.pullbackModules.mapDerivedCategoryFactorsh.inv ≫
    Functor.whiskerRight (derivedTotalPushforwardModulesUnit h)
      (C'.situation.derivedComponentPullbackModules O' n)

/-- The comparison from the degreewise pullback to the component of degree `n` followed by the
degreewise direct image of that degree, into `Lg_n^*` followed by `Rh_{n,*}`. -/
def derivedRestrictTotalPushforwardModulesUnit :
    (C.situation.componentRingedToposHom O n).toModulesHom.pullbackModules.mapHomotopyCategory
          (ComplexShape.up ℤ) ⋙
        (h.componentRingedToposHom n).pushforwardModules.mapHomotopyCategory
          (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ (C.situation.derivedComponentPullbackModules O n ⋙
        derivedComponentPushforwardModules h n) :=
  Functor.whiskerLeft
      ((C.situation.componentRingedToposHom O n).toModulesHom.pullbackModules.mapHomotopyCategory
        (ComplexShape.up ℤ))
      (derivedComponentPushforwardModulesUnit h n) ≫
    Functor.whiskerRight
      ((C.situation.componentRingedToposHom O n).toModulesHom.pullbackModules
        |>.mapDerivedCategoryFactorsh).inv
      (derivedComponentPushforwardModules h n)

/-- **Pullback to a component of a K-injective complex of modules computes `Rh_{n,*}`.** This is
the source's reduction to abelian sheaves through Stacks 0D6J: forgetting the module structure
is exact and reflects isomorphisms and carries `h_{n,*}` to the degreewise direct image of
abelian sheaves (`componentPushforwardModulesToSheafIso`); the abelian comparison is invertible
at the underlying complex of every K-injective complex of `𝒪_n`-modules, by Stacks 0D6J for the
cocontinuous functor of degree `n`, and at the underlying complex of `g_n^* I`, which is the
restriction of the underlying complex of `I` (`componentPullbackModulesToSheafIso`) and so
computes the abelian `Rh_{n,*}` by the argument of Stacks 0D97
(`Morphism.isIso_derivedAbelianPushforwardUnit_app_abelianComponent`). -/
theorem isIso_derivedComponentPushforwardModulesUnit_app_componentPullback
    (I : CochainComplex (SheafOfModules.{u}
        ((Stacks.SheafOfModules.Tensor.ringSheaf (J := (C.situation.totalRingedTopos O).J))
      (C.situation.totalRingedTopos O).O)) ℤ) (hI : I.IsKInjective) :
    IsIso ((derivedComponentPushforwardModulesUnit h n).app
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
        (((C.situation.componentRingedToposHom O n).toModulesHom.pullbackModules
            |>.mapHomologicalComplex (ComplexShape.up ℤ)).obj I))) := by
  let : (h.hom.hom.app (Opposite.op n)).toFunctor.IsCocontinuous
      (topologyOfCoverings (C.coverage (Opposite.op n)))
      (topologyOfCoverings (C'.coverage (Opposite.op n))) :=
    h.hom.isCocontinuous (Opposite.op n)
  have := hI
  have := Morphism.additive_abelianComponentPushforward h.hom n
  let ι : ((SheafOfModules.toSheaf
      ((Stacks.SheafOfModules.Tensor.ringSheaf (J := (C.situation.componentRingedTopos O n).J))
          (C.situation.componentRingedTopos O n).O)).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (((C.situation.componentRingedToposHom O n).toModulesHom.pullbackModules
            |>.mapHomologicalComplex (ComplexShape.up ℤ)).obj I) ≅
      ((C.situation.abelianComponent n).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (((SheafOfModules.toSheaf ((Stacks.SheafOfModules.Tensor.ringSheaf
            (J := (C.situation.totalRingedTopos O).J))
          (C.situation.totalRingedTopos O).O)).mapHomologicalComplex (ComplexShape.up ℤ)).obj I) :=
    HomologicalComplex.Hom.isoOfComponents
      (fun i => (SimplicialSiteSituation.componentPullbackModulesToSheafIso C.situation O n).app
        (I.X i))
      (fun i j _ => ((SimplicialSiteSituation.componentPullbackModulesToSheafIso C.situation O
        n).hom.naturality (I.d i j)).symm)
  have h3 := @Morphism.isIso_derivedAbelianPushforwardUnit_app_abelianComponent _ _ h.hom n
    ((Stacks.SheafOfModules.Tensor.ringSheaf (J := (C.situation.totalRingedTopos O).J))
        (C.situation.totalRingedTopos O).O) I hI
  have hab : IsIso ((Stacks.Cohomology.CocontinuousForgetModule.derivedAbelianPushforwardUnit
      (topologyOfCoverings (C.coverage (Opposite.op n)))
      (topologyOfCoverings (C'.coverage (Opposite.op n)))
      (h.hom.hom.app (Opposite.op n)).toFunctor).app
        (((SheafOfModules.toSheaf ((Stacks.SheafOfModules.Tensor.ringSheaf
            (J := (C.situation.componentRingedTopos O n).J))
          (C.situation.componentRingedTopos O n).O)).mapHomotopyCategory (ComplexShape.up ℤ)).obj
          ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
            (((C.situation.componentRingedToposHom O n).toModulesHom.pullbackModules
                |>.mapHomologicalComplex (ComplexShape.up ℤ)).obj I)))) :=
    (NatTrans.isIso_app_iff_of_iso _ ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).mapIso
      ι)).mpr h3
  open Stacks.Cohomology.CocontinuousForgetModule in
  exact @Stacks.Cohomology.UnboundedComplexes.isIso_rightDerivedUnit_of_forget
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (h.componentRingedToposHom n).pushforwardModules
    ((h.hom.hom.app (Opposite.op n)).toFunctor.sheafPushforwardCocontinuous Ab.{u}
      (topologyOfCoverings (C.coverage (Opposite.op n)))
      (topologyOfCoverings (C'.coverage (Opposite.op n))))
    (SheafOfModules.toSheaf.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf
        (J := (C.situation.componentRingedTopos O n).J))
      (C.situation.componentRingedTopos O n).O))
    (SheafOfModules.toSheaf.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf
        (J := (C'.situation.componentRingedTopos O' n).J))
      (C'.situation.componentRingedTopos O' n).O))
    _ _ ⟨fun {_ _ f g} => (SheafOfModules.toSheaf _).map_add (f := f) (g := g)⟩
    ⟨fun {_ _ f g} => (SheafOfModules.toSheaf _).map_add (f := f) (g := g)⟩
    (inferInstance : PreservesFiniteLimits (SheafOfModules.toSheaf.{u}
        ((Stacks.SheafOfModules.Tensor.ringSheaf (J := (C.situation.componentRingedTopos O n).J))
            (C.situation.componentRingedTopos O n).O)))
    (Stacks.SheafOfModules.instPreservesFiniteColimitsToSheaf _)
    (inferInstance : PreservesFiniteLimits (SheafOfModules.toSheaf.{u}
        ((Stacks.SheafOfModules.Tensor.ringSheaf (J := (C'.situation.componentRingedTopos O' n).J))
            (C'.situation.componentRingedTopos O' n).O)))
    (Stacks.SheafOfModules.instPreservesFiniteColimitsToSheaf _)
    (inferInstance : (SheafOfModules.toSheaf.{u}
        ((Stacks.SheafOfModules.Tensor.ringSheaf (J := (C'.situation.componentRingedTopos O' n).J))
      (C'.situation.componentRingedTopos O' n).O)).ReflectsIsomorphisms)
    (componentPushforwardModulesToSheafIso h n) (derivedComponentPushforwardModules h n)
    (Stacks.Cohomology.CocontinuousForgetModule.derivedAbelianPushforward
      (topologyOfCoverings (C.coverage (Opposite.op n)))
      (topologyOfCoverings (C'.coverage (Opposite.op n)))
      (h.hom.hom.app (Opposite.op n)).toFunctor)
    (derivedComponentPushforwardModulesUnit h n)
    (Stacks.Cohomology.CocontinuousForgetModule.derivedAbelianPushforwardUnit
      (topologyOfCoverings (C.coverage (Opposite.op n)))
      (topologyOfCoverings (C'.coverage (Opposite.op n)))
      (h.hom.hom.app (Opposite.op n)).toFunctor) _
    (fun I' hI' => have := hI'
      @abelianPushforwardUnit_isIso_at_underlying_kInjective
        _ _ _ _ (topologyOfCoverings (C.coverage (Opposite.op n)))
        (topologyOfCoverings (C'.coverage (Opposite.op n)))
        (h.hom.hom.app (Opposite.op n)).toFunctor (h.hom.isCocontinuous (Opposite.op n)) _ _ _
        ((Stacks.SheafOfModules.Tensor.ringSheaf (J := (C.situation.componentRingedTopos O n).J))
          (C.situation.componentRingedTopos O n).O) I' hI')
    _ hab

/-- `Rh_{total,*}` followed by `Lg'_n^*` is a right derived functor of the degreewise direct
image along the total morphism followed by the degreewise pullback to the component of degree
`n`: the comparison for the direct image is invertible on a K-injective complex, and the one for
the pullback is invertible everywhere because the pullback is exact. -/
theorem isRightDerivedFunctor_derivedTotalPushforwardRestrictModulesUnit :
    (derivedTotalPushforwardModules h ⋙
        C'.situation.derivedComponentPullbackModules O' n).IsRightDerivedFunctor
      (derivedTotalPushforwardRestrictModulesUnit h n)
      (HomotopyCategory.quasiIso
        (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf
            (J := (C.situation.totalRingedTopos O).J))
          (C.situation.totalRingedTopos O).O)) (ComplexShape.up ℤ)) := by
  apply Stacks.Cohomology.Localization.rightDerived_of_kInjectives
  intro I hI
  have := isIso_derivedPushforwardUnit_app_of_isKInjective _ _ h.totalRingedToposHom I hI
  rw [derivedTotalPushforwardRestrictModulesUnit, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app]
  infer_instance

/-- `Lg_n^*` followed by `Rh_{n,*}` is a right derived functor of the degreewise pullback to the
component of degree `n` followed by the degreewise direct image of that degree: the pullback is
exact, so its comparison is invertible everywhere, and the pullback of a K-injective complex
computes `Rh_{n,*}` by
`isIso_derivedComponentPushforwardModulesUnit_app_componentPullback`. -/
theorem isRightDerivedFunctor_derivedRestrictTotalPushforwardModulesUnit :
    (C.situation.derivedComponentPullbackModules O n ⋙
        derivedComponentPushforwardModules h n).IsRightDerivedFunctor
      (derivedRestrictTotalPushforwardModulesUnit h n)
      (HomotopyCategory.quasiIso
        (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf
            (J := (C.situation.totalRingedTopos O).J))
          (C.situation.totalRingedTopos O).O)) (ComplexShape.up ℤ)) := by
  apply Stacks.Cohomology.Localization.rightDerived_of_kInjectives
  intro I hI
  rw [derivedRestrictTotalPushforwardModulesUnit, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app]
  exact IsIso.comp_isIso' (isIso_derivedComponentPushforwardModulesUnit_app_componentPullback
    h n I hI) inferInstance

/-! ### Stacks 0DH1 -/

/-- The module-level identity of Stacks 0DH0 read on unbounded homotopy categories: the canonical
comparison `componentPushforwardModulesIso` of the two underived composites around the
degreewise square, applied degreewise to complexes. -/
def homotopyComponentPushforwardModulesIso :
    h.totalRingedToposHom.pushforwardModules.mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        (C'.situation.componentRingedToposHom O' n).toModulesHom.pullbackModules.mapHomotopyCategory
          (ComplexShape.up ℤ) ≅
      (C.situation.componentRingedToposHom O n).toModulesHom.pullbackModules.mapHomotopyCategory
          (ComplexShape.up ℤ) ⋙
        (h.componentRingedToposHom n).pushforwardModules.mapHomotopyCategory
          (ComplexShape.up ℤ) :=
  Functor.mapHomotopyCategoryCompIso (componentPushforwardModulesIso h n) (ComplexShape.up ℤ) ≪≫
    (Functor.mapHomotopyCategoryCompIso
      (Iso.refl ((C.situation.componentRingedToposHom O n).toModulesHom.pullbackModules ⋙
        (h.componentRingedToposHom n).pushforwardModules)) (ComplexShape.up ℤ)).symm

/-- **Stacks 0DH1**, case (B). With notation and hypotheses as in Stacks 0DH0: for `K` in the
unbounded derived category of sheaves of `𝒪`-modules on the total site,

`(g'_n)^* Rh_{total,*} K = Rh_{n,*} g_n^* K`.

The source's equality is read as a natural isomorphism of functors on the derived category.
Both sides are right derived functors of one and the same functor on the unbounded homotopy
category of `𝒪`-modules, by
`isRightDerivedFunctor_derivedTotalPushforwardRestrictModulesUnit` and
`isRightDerivedFunctor_derivedRestrictTotalPushforwardModulesUnit` of this namespace, the two
being identified by the canonical comparison of Stacks 0DH0, `componentPushforwardModulesIso`.
The isomorphism is the induced comparison of the two right derived functors, pinned down by
`derivedComponentPushforwardModulesIso_fac`. -/
@[stacks 0DH1 "case (B)"]
def derivedComponentPushforwardModulesIso :
    derivedTotalPushforwardModules h ⋙
        C'.situation.derivedComponentPullbackModules O' n ≅
      C.situation.derivedComponentPullbackModules O n ⋙
        derivedComponentPushforwardModules h n :=
  have := isRightDerivedFunctor_derivedTotalPushforwardRestrictModulesUnit h n
  have := isRightDerivedFunctor_derivedRestrictTotalPushforwardModulesUnit h n
  Functor.rightDerivedNatIso _ _ (derivedTotalPushforwardRestrictModulesUnit h n)
    (derivedRestrictTotalPushforwardModulesUnit h n)
    (HomotopyCategory.quasiIso
      (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf
          (J := (C.situation.totalRingedTopos O).J))
        (C.situation.totalRingedTopos O).O)) (ComplexShape.up ℤ))
    (Functor.isoWhiskerRight (homotopyComponentPushforwardModulesIso h n) DerivedCategory.Qh)

/-- **Stacks 0DH1**, the isomorphism is the canonical one. Composing the canonical comparison
into the first right derived functor with the isomorphism gives the canonical underived
comparison of Stacks 0DH0, applied degreewise to complexes, followed by the canonical comparison
into the second. Since a morphism out of a right derived functor is determined by that
identity, this pins the isomorphism down completely. -/
theorem derivedComponentPushforwardModulesIso_fac :
    derivedTotalPushforwardRestrictModulesUnit h n ≫
        Functor.whiskerLeft DerivedCategory.Qh (derivedComponentPushforwardModulesIso h n).hom =
      (Functor.isoWhiskerRight (homotopyComponentPushforwardModulesIso h n)
            DerivedCategory.Qh).hom ≫
        derivedRestrictTotalPushforwardModulesUnit h n :=
  have := isRightDerivedFunctor_derivedTotalPushforwardRestrictModulesUnit h n
  have := isRightDerivedFunctor_derivedRestrictTotalPushforwardModulesUnit h n
  Functor.rightDerivedNatTrans_fac _ _ (derivedTotalPushforwardRestrictModulesUnit h n)
    (derivedRestrictTotalPushforwardModulesUnit h n)
    (HomotopyCategory.quasiIso
      (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf
          (J := (C.situation.totalRingedTopos O).J))
        (C.situation.totalRingedTopos O).O)) (ComplexShape.up ℤ))
    (Functor.isoWhiskerRight (homotopyComponentPushforwardModulesIso h n)
      DerivedCategory.Qh).hom

end CocontinuousSimplicialSite.RingedMorphism

namespace CocontinuousSimplicialSite.Morphism

variable {C C' : CocontinuousSimplicialSite.{u}}
  {O : Sheaf C.situation.totalTopology CommRingCat.{u}}
  {O' : Sheaf C'.situation.totalTopology CommRingCat.{u}}
  (h : Morphism C C')
  (φ : h.totalInverseImageRing ((Stacks.SheafOfModules.Tensor.ringSheaf
      (J := C'.situation.totalTopology) O')) ⟶
    (Stacks.SheafOfModules.Tensor.ringSheaf (J := C.situation.totalTopology) O))
  (n : SimplexCategory)

/-! ### The two derived direct images -/

/-- `Rh_{total,*}`: the unbounded derived direct image of sheaves of modules along the morphism
of total ringed topoi of Stacks 0DH0. -/
abbrev derivedTotalPushforwardModules :
    DerivedCategory (SheafOfModules.{u}
        ((Stacks.SheafOfModules.Tensor.ringSheaf (J := (C.situation.totalRingedTopos O).J)
            (C.situation.totalRingedTopos O).O))) ⥤
      DerivedCategory (SheafOfModules.{u}
          ((Stacks.SheafOfModules.Tensor.ringSheaf (J := (C'.situation.totalRingedTopos O').J)
              (C'.situation.totalRingedTopos O').O))) :=
  derivedPushforward.{u, u, u, u, u, u} (h.totalRingedToposHom φ)

/-- The canonical comparison from the degreewise direct image along the total morphism into
`Rh_{total,*}`. -/
abbrev derivedTotalPushforwardModulesUnit :
    pushforwardOnHomotopy.{u, u, u, u, u, u} (h.totalRingedToposHom φ) ⟶
      DerivedCategory.Qh ⋙ derivedTotalPushforwardModules h φ :=
  derivedPushforwardUnit _ _ (h.totalRingedToposHom φ)

/-- `Rh_{n,*}`: the unbounded derived direct image of sheaves of modules along the morphism of
component ringed topoi of simplicial degree `n` of Stacks 0DH0. -/
abbrev derivedComponentPushforwardModules :
    DerivedCategory (SheafOfModules.{u}
        ((Stacks.SheafOfModules.Tensor.ringSheaf (J := (C.situation.componentRingedTopos O n).J)
            (C.situation.componentRingedTopos O n).O))) ⥤
      DerivedCategory (SheafOfModules.{u}
          ((Stacks.SheafOfModules.Tensor.ringSheaf (J := (C'.situation.componentRingedTopos O' n).J)
              (C'.situation.componentRingedTopos O' n).O))) :=
  derivedPushforward.{u, u, u, u, u, u} ((h.componentRingedToposHom φ) n)

/-- The canonical comparison from the degreewise direct image in simplicial degree `n` into
`Rh_{n,*}`. -/
abbrev derivedComponentPushforwardModulesUnit :
    pushforwardOnHomotopy.{u, u, u, u, u, u} ((h.componentRingedToposHom φ) n) ⟶
      DerivedCategory.Qh ⋙ derivedComponentPushforwardModules h φ n :=
  derivedPushforwardUnit _ _ ((h.componentRingedToposHom φ) n)

/-! ### The two sides of the source's identity as right derived functors -/

/-- The comparison from the degreewise direct image along the total morphism followed by the
degreewise pullback to the component of degree `n`, into `Rh_{total,*}` followed by `Lg'_n^*`. -/
def derivedTotalPushforwardRestrictModulesUnit :
    (h.totalRingedToposHom φ).pushforwardModules.mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        (C'.situation.componentRingedToposHom O' n).toModulesHom.pullbackModules.mapHomotopyCategory
          (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ (derivedTotalPushforwardModules h φ ⋙
        C'.situation.derivedComponentPullbackModules O' n) :=
  Functor.whiskerLeft
      ((h.totalRingedToposHom φ).pushforwardModules.mapHomotopyCategory (ComplexShape.up ℤ))
      (C'.situation.componentRingedToposHom O' n
        ).toModulesHom.pullbackModules.mapDerivedCategoryFactorsh.inv ≫
    Functor.whiskerRight (derivedTotalPushforwardModulesUnit h φ)
      (C'.situation.derivedComponentPullbackModules O' n)

/-- The comparison from the degreewise pullback to the component of degree `n` followed by the
degreewise direct image of that degree, into `Lg_n^*` followed by `Rh_{n,*}`. -/
def derivedRestrictTotalPushforwardModulesUnit :
    (C.situation.componentRingedToposHom O n).toModulesHom.pullbackModules.mapHomotopyCategory
          (ComplexShape.up ℤ) ⋙
        ((h.componentRingedToposHom φ) n).pushforwardModules.mapHomotopyCategory
          (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ (C.situation.derivedComponentPullbackModules O n ⋙
        derivedComponentPushforwardModules h φ n) :=
  Functor.whiskerLeft
      ((C.situation.componentRingedToposHom O n).toModulesHom.pullbackModules.mapHomotopyCategory
        (ComplexShape.up ℤ))
      (derivedComponentPushforwardModulesUnit h φ n) ≫
    Functor.whiskerRight
      ((C.situation.componentRingedToposHom O n).toModulesHom.pullbackModules
        |>.mapDerivedCategoryFactorsh).inv
      (derivedComponentPushforwardModules h φ n)

/-- `Rh_{total,*}` followed by `Lg'_n^*` is a right derived functor of the degreewise direct
image along the total morphism followed by the degreewise pullback to the component of degree
`n`: the comparison for the direct image is invertible on a K-injective complex, and the one for
the pullback is invertible everywhere because the pullback is exact. -/
theorem isRightDerivedFunctor_derivedTotalPushforwardRestrictModulesUnit :
    (derivedTotalPushforwardModules h φ ⋙
        C'.situation.derivedComponentPullbackModules O' n).IsRightDerivedFunctor
      (derivedTotalPushforwardRestrictModulesUnit h φ n)
      (HomotopyCategory.quasiIso
        (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf
            (J := (C.situation.totalRingedTopos O).J) (C.situation.totalRingedTopos O).O)))
              (ComplexShape.up ℤ)) := by
  apply Stacks.Cohomology.Localization.rightDerived_of_kInjectives
  intro I hI
  have := isIso_derivedPushforwardUnit_app_of_isKInjective _ _ (h.totalRingedToposHom φ) I hI
  rw [derivedTotalPushforwardRestrictModulesUnit, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app]
  infer_instance

/-- `Lg_n^*` followed by `Rh_{n,*}` is a right derived functor of the degreewise pullback to the
component of degree `n` followed by the degreewise direct image of that degree: the pullback is
exact, so its comparison is invertible everywhere, and by the hypothesis `hK` — Stacks 09WH for
sheaves of modules — it carries a K-injective complex to a K-injective complex, so the
comparison for the direct image of degree `n` is invertible there. -/
theorem isRightDerivedFunctor_derivedRestrictTotalPushforwardModulesUnit
    (hK : ∀ I : CochainComplex (SheafOfModules.{u}
        ((Stacks.SheafOfModules.Tensor.ringSheaf (J := (C.situation.totalRingedTopos O).J)
            (C.situation.totalRingedTopos O).O))) ℤ,
      I.IsKInjective →
        CochainComplex.IsKInjective
          (((C.situation.componentRingedToposHom O n).toModulesHom.pullbackModules
              |>.mapHomologicalComplex (ComplexShape.up ℤ)).obj I)) :
    (C.situation.derivedComponentPullbackModules O n ⋙
        derivedComponentPushforwardModules h φ n).IsRightDerivedFunctor
      (derivedRestrictTotalPushforwardModulesUnit h φ n)
      (HomotopyCategory.quasiIso
        (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf
            (J := (C.situation.totalRingedTopos O).J) (C.situation.totalRingedTopos O).O)))
              (ComplexShape.up ℤ)) := by
  apply Stacks.Cohomology.Localization.rightDerived_of_kInjectives
  intro I hI
  rw [derivedRestrictTotalPushforwardModulesUnit, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app]
  exact IsIso.comp_isIso' (isIso_derivedPushforwardUnit_app_of_isKInjective _ _
    (h.componentRingedToposHom φ n) _ (hK I hI)) inferInstance

/-! ### Stacks 0DH1 -/

/-- The module-level comparison of Stacks 0DH0 read on unbounded homotopy categories: the two
underived composites around the degreewise square, applied degreewise to complexes. -/
def homotopyComponentPushforwardModulesIso
    (e : (h.totalRingedToposHom φ).pushforwardModules ⋙
        (C'.situation.componentRingedToposHom O' n).toModulesHom.pullbackModules ≅
      (C.situation.componentRingedToposHom O n).toModulesHom.pullbackModules ⋙
        ((h.componentRingedToposHom φ) n).pushforwardModules) :
    (h.totalRingedToposHom φ).pushforwardModules.mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        (C'.situation.componentRingedToposHom O' n).toModulesHom.pullbackModules.mapHomotopyCategory
          (ComplexShape.up ℤ) ≅
      (C.situation.componentRingedToposHom O n).toModulesHom.pullbackModules.mapHomotopyCategory
          (ComplexShape.up ℤ) ⋙
        ((h.componentRingedToposHom φ) n).pushforwardModules.mapHomotopyCategory
          (ComplexShape.up ℤ) :=
  Functor.mapHomotopyCategoryCompIso e (ComplexShape.up ℤ) ≪≫
    (Functor.mapHomotopyCategoryCompIso
      (Iso.refl ((C.situation.componentRingedToposHom O n).toModulesHom.pullbackModules ⋙
        ((h.componentRingedToposHom φ) n).pushforwardModules)) (ComplexShape.up ℤ)).symm

/-- **Stacks 0DH1**, case (B). With notation and hypotheses as in Stacks 0DH0: for `K` in the
unbounded derived category of sheaves of `𝒪`-modules on the total site,

`(g'_n)^* Rh_{total,*} K = Rh_{n,*} g_n^* K`.

The source's equality is read as a natural isomorphism of functors on the derived category.
Both sides are right derived functors of one and the same functor on the unbounded homotopy
category of `𝒪`-modules, by
`isRightDerivedFunctor_derivedTotalPushforwardRestrictModulesUnit` and
`isRightDerivedFunctor_derivedRestrictTotalPushforwardModulesUnit` of this namespace, the two
being identified by the underived comparison `e`.

The hypothesis `e` is the last assertion of Stacks 0DH0 at the level of sheaves of modules, and
`hK` is Stacks 09WH for sheaves of modules; see the implementation notes of this file for why
both are deferred. -/
@[stacks 0DH1 "case (B)"]
def derivedComponentPushforwardModulesIso
    (e : (h.totalRingedToposHom φ).pushforwardModules ⋙
        (C'.situation.componentRingedToposHom O' n).toModulesHom.pullbackModules ≅
      (C.situation.componentRingedToposHom O n).toModulesHom.pullbackModules ⋙
        ((h.componentRingedToposHom φ) n).pushforwardModules)
    (hK : ∀ I : CochainComplex (SheafOfModules.{u}
        ((Stacks.SheafOfModules.Tensor.ringSheaf (J := (C.situation.totalRingedTopos O).J)
            (C.situation.totalRingedTopos O).O))) ℤ,
      I.IsKInjective →
        CochainComplex.IsKInjective
          (((C.situation.componentRingedToposHom O n).toModulesHom.pullbackModules
              |>.mapHomologicalComplex (ComplexShape.up ℤ)).obj I)) :
    derivedTotalPushforwardModules h φ ⋙
        C'.situation.derivedComponentPullbackModules O' n ≅
      C.situation.derivedComponentPullbackModules O n ⋙
        derivedComponentPushforwardModules h φ n :=
  have := isRightDerivedFunctor_derivedTotalPushforwardRestrictModulesUnit h φ n
  have := isRightDerivedFunctor_derivedRestrictTotalPushforwardModulesUnit h φ n hK
  Functor.rightDerivedNatIso _ _ (derivedTotalPushforwardRestrictModulesUnit h φ n)
    (derivedRestrictTotalPushforwardModulesUnit h φ n)
    (HomotopyCategory.quasiIso
      (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf
          (J := (C.situation.totalRingedTopos O).J) (C.situation.totalRingedTopos O).O)))
            (ComplexShape.up ℤ))
    (Functor.isoWhiskerRight (homotopyComponentPushforwardModulesIso h φ n e) DerivedCategory.Qh)

/-- **Stacks 0DH1**, the isomorphism is the canonical one. Composing the canonical comparison
into the first right derived functor with the isomorphism gives the underived comparison
followed by the canonical comparison into the second. Since a morphism out of a right derived
functor is determined by that identity, this pins the isomorphism down completely. -/
@[stacks 0DH1 "case (B), the canonical comparison"]
theorem derivedComponentPushforwardModulesIso_fac
    (e : (h.totalRingedToposHom φ).pushforwardModules ⋙
        (C'.situation.componentRingedToposHom O' n).toModulesHom.pullbackModules ≅
      (C.situation.componentRingedToposHom O n).toModulesHom.pullbackModules ⋙
        ((h.componentRingedToposHom φ) n).pushforwardModules)
    (hK : ∀ I : CochainComplex (SheafOfModules.{u}
        ((Stacks.SheafOfModules.Tensor.ringSheaf (J := (C.situation.totalRingedTopos O).J)
            (C.situation.totalRingedTopos O).O))) ℤ,
      I.IsKInjective →
        CochainComplex.IsKInjective
          (((C.situation.componentRingedToposHom O n).toModulesHom.pullbackModules
              |>.mapHomologicalComplex (ComplexShape.up ℤ)).obj I)) :
    derivedTotalPushforwardRestrictModulesUnit h φ n ≫
        Functor.whiskerLeft DerivedCategory.Qh
          (derivedComponentPushforwardModulesIso h φ n e hK).hom =
      (Functor.isoWhiskerRight (homotopyComponentPushforwardModulesIso h φ n e)
            DerivedCategory.Qh).hom ≫
        derivedRestrictTotalPushforwardModulesUnit h φ n :=
  have := isRightDerivedFunctor_derivedTotalPushforwardRestrictModulesUnit h φ n
  have := isRightDerivedFunctor_derivedRestrictTotalPushforwardModulesUnit h φ n hK
  Functor.rightDerivedNatTrans_fac _ _ (derivedTotalPushforwardRestrictModulesUnit h φ n)
    (derivedRestrictTotalPushforwardModulesUnit h φ n)
    (HomotopyCategory.quasiIso
      (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf
          (J := (C.situation.totalRingedTopos O).J) (C.situation.totalRingedTopos O).O)))
            (ComplexShape.up ℤ))
    (Functor.isoWhiskerRight (homotopyComponentPushforwardModulesIso h φ n e)
      DerivedCategory.Qh).hom

/-! ### Stacks 0DH1 over the canonical comparison of the degreewise square

The isomorphism `e` above is an arbitrary one. The degreewise square of ringed topoi of
Stacks 0DH0 supplies a *canonical* comparison of the two underived composites,
`CategoryTheory.CocontinuousSimplicialSite.Morphism.componentPushforwardModulesComparison`
— the mate of the square of direct images of sheaves of modules — and the source's last
assertion is that it is invertible. Stated over that comparison the conclusion below is
canonical: no isomorphism is chosen anywhere, and the only input not carried by this
development, besides `hK`, is the invertibility of one canonical natural transformation. -/

/-- **Stacks 0DH1**, case (B), over the canonical comparison of the degreewise square. With
notation and hypotheses as in Stacks 0DH0: for `K` in the unbounded derived category of sheaves
of `𝒪`-modules on the total site,

`(g'_n)^* Rh_{total,*} K = Rh_{n,*} g_n^* K`.

This is `derivedComponentPushforwardModulesIso` with the underived comparison taken to be the
canonical one of
`CategoryTheory.CocontinuousSimplicialSite.Morphism.componentPushforwardModulesIso`,
rather than an arbitrary isomorphism. The only hypothesis is `hK`, Stacks 09WH for sheaves of
modules; see the implementation notes of this file. -/
@[stacks 0DH1 "case (B), over the canonical comparison of the degreewise square"]
def derivedComponentPushforwardModulesIsoOfSquare
    (hK : ∀ I : CochainComplex (SheafOfModules.{u}
        ((Stacks.SheafOfModules.Tensor.ringSheaf (J := (C.situation.totalRingedTopos O).J)
            (C.situation.totalRingedTopos O).O))) ℤ,
      I.IsKInjective →
        CochainComplex.IsKInjective
          (((C.situation.componentRingedToposHom O n).toModulesHom.pullbackModules
              |>.mapHomologicalComplex (ComplexShape.up ℤ)).obj I)) :
    derivedTotalPushforwardModules h φ ⋙
        C'.situation.derivedComponentPullbackModules O' n ≅
      C.situation.derivedComponentPullbackModules O n ⋙
        derivedComponentPushforwardModules h φ n :=
  derivedComponentPushforwardModulesIso h φ n (componentPushforwardModulesIso h φ n) hK

/-- **Stacks 0DH1**, case (B) over the canonical comparison: the isomorphism is pinned by the
canonical comparison of the degreewise square. Composing the canonical comparison into the
first right derived functor with it gives the canonical underived comparison, applied
degreewise to complexes, followed by the canonical comparison into the second right derived
functor. Since a morphism out of a right derived functor is determined by that identity, this
determines the isomorphism completely from the square of ringed topoi. -/
@[stacks 0DH1 "case (B), the canonical comparison of the degreewise square pins the
  isomorphism"]
theorem derivedComponentPushforwardModulesIsoOfSquare_fac
    (hK : ∀ I : CochainComplex (SheafOfModules.{u}
        ((Stacks.SheafOfModules.Tensor.ringSheaf (J := (C.situation.totalRingedTopos O).J)
            (C.situation.totalRingedTopos O).O))) ℤ,
      I.IsKInjective →
        CochainComplex.IsKInjective
          (((C.situation.componentRingedToposHom O n).toModulesHom.pullbackModules
              |>.mapHomologicalComplex (ComplexShape.up ℤ)).obj I)) :
    derivedTotalPushforwardRestrictModulesUnit h φ n ≫
        Functor.whiskerLeft DerivedCategory.Qh
          (derivedComponentPushforwardModulesIsoOfSquare h φ n hK).hom =
      (Functor.isoWhiskerRight
            (homotopyComponentPushforwardModulesIso h φ n
              (componentPushforwardModulesIso h φ n)) DerivedCategory.Qh).hom ≫
        derivedRestrictTotalPushforwardModulesUnit h φ n :=
  derivedComponentPushforwardModulesIso_fac h φ n (componentPushforwardModulesIso h φ n) hK

end CocontinuousSimplicialSite.Morphism

end CategoryTheory

end
