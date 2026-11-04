module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.CategoryTheory.Adjunction.CompositionIso
public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
public import StacksFrontier.Algebra.Homology.HomotopyCategory.MapCompIsoCommShift
public import StacksFrontier.CategoryTheory.Localization.LeftDerivedByResolutions
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.PullbackPushforwardAdjunction
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.Composition
public import StacksFrontier.Topology.Sheaves.Functors.Module.RingedSpace

/-!
# Composition of derived pullbacks along morphisms of ringed spaces

Let `f : (X, 𝒪_X) ⟶ (Y, 𝒪_Y)` and `g : (Y, 𝒪_Y) ⟶ (Z, 𝒪_Z)` be morphisms of ringed spaces.
Write `Lf^*`, `Lg^*` and `L(f ≫ g)^*` for left derived functors of the three degreewise
pullbacks followed by localization, each presented by a functor on derived categories together
with its canonical comparison.  The ordinary pullback-composition isomorphism and the universal
property of `L(f ≫ g)^*` produce a canonical comparison

`Lg^* ⋙ Lf^* ⟶ L(f ≫ g)^*`

and the assertion that it is invertible is the composition formula for derived pullback.

The comparison is invertible as soon as there is a class of complexes of `𝒪_Z`-modules which
resolves every complex, on which the comparison for `Lg^*` is invertible, which degreewise
pullback along `f ≫ g` carries quasi-isomorphisms to isomorphisms of `D(𝒪_X)`, and whose
image under degreewise pullback along `g` lies in a class of complexes of `𝒪_Y`-modules on
which the comparison for `Lf^*` is invertible.  The intended classes are the K-flat complexes
on `Z` and on `Y`; stability of K-flatness under pullback is Tag 06YC.

## Main definitions

* `ModuleSheaves` is the category of sheaves of modules on a
  ringed space.
* `Stacks.DerivedPullback.Composition.modulePullbackComp` is the pullback-composition isomorphism
  `g^* ⋙ f^* ≅ (f ≫ g)^*` for sheaves of modules.
* `Stacks.DerivedPullback.Composition.pullbackOnHomotopyCompIso` is the same isomorphism on cochain
  complexes, read
  on the homotopy categories.
* `Stacks.DerivedPullback.Composition.derivedPullbackCompCounit` is the comparison from the
  composite of the two
  derived pullbacks to degreewise pullback along `f ≫ g`.
* `Stacks.DerivedPullback.Composition.derivedPullbackCompComparison` is the induced canonical
  comparison
  `Lg^* ⋙ Lf^* ⟶ L(f ≫ g)^*`.
* `Stacks.DerivedPullback.Composition.derivedPullbackCompIso` is the resulting natural isomorphism.

## Main results

* `Stacks.DerivedPullback.Composition.commShift_pullbackOnHomotopyCompIso_hom`: the
  pullback-composition isomorphism on the homotopy categories commutes with the shift, an
  instance of `CategoryTheory.Functor.commShift_mapHomotopyCategoryCompIso_hom`.
* `Stacks.DerivedPullback.Composition.isIso_derivedPullbackCompCounit_app`: the comparison is
  invertible at a
  complex of the resolving class.
* `Stacks.DerivedPullback.Composition.isLeftDerivedFunctor_comp`: the composite `Lg^* ⋙ Lf^*`, with
  `derivedPullbackCompCounit`, is a left derived functor of degreewise pullback along `f ≫ g`.
* `Stacks.DerivedPullback.Composition.isIso_derivedPullbackCompComparison`: the canonical
  comparison is an
  isomorphism.  This is the composition formula.
* `Stacks.DerivedPullback.Composition.isIso_app_of_resolving`: a comparison of a derived pullback
  is invertible on a
  class whose quasi-isomorphisms degreewise pullback inverts, which is how the hypotheses on
  the two comparisons are met in practice.
* `Stacks.DerivedPullback.Composition.isIso_derivedPullbackCompComparison_of_exact`: the
  composition formula for two
  morphisms along which degreewise pullback is exact, where no resolving class is left over.
* `Stacks.DerivedPullback.Composition.preservesFiniteLimits_modulePullback_comp` and
  `Stacks.DerivedPullback.Composition.preservesFiniteColimits_modulePullback_comp`: exactness of
    pullback along a
  composite, which is what that case needs of the third morphism.

## Implementation notes

*Where the pullback-composition isomorphism comes from.*  Degreewise pullback is defined as an
abstract left adjoint, so there is no sectionwise formula to compare; the isomorphism is
obtained from the pushforward-composition isomorphism `(f ≫ g)_* ≅ f_* ⋙ g_*` by uniqueness of
left adjoints, `CategoryTheory.Adjunction.leftAdjointCompIso`.  Its orientation is the one that
reads left to right along the composite, `g^* ⋙ f^* ≅ (f ≫ g)^*`, rather than the opposite.

*Why the resolving class is a hypothesis.*  Both `L(f ≫ g)^*` and `Lg^* ⋙ Lf^*` are left
derived functors, of *different* functors on the homotopy category, and the map between those
two sources is invertible only where the two factor comparisons are.  For the intended class of
K-flat complexes that is Tag 06YJ together with stability of K-flatness under pullback, Tag
06YC; neither is available, so the class is carried as a parameter.  The shape of the
hypotheses is the one of Tag 079W, which carries a resolving datum for the same reason.

*One spelling for the comparison at an object.*  `derivedPullbackCompCounit_app` evaluates the
three-fold composite once, in term mode, and every proof below works against that single
spelling.  The components of the whiskerings are definitional, but a tactic looking at the
unevaluated composite cannot see through them.

## References

* [Stacks Project, Tag 0D5S](https://stacks.math.columbia.edu/tag/0D5S)
* [Stacks Project, Tag 079W](https://stacks.math.columbia.edu/tag/079W)
* [Stacks Project, Tag 06YJ](https://stacks.math.columbia.edu/tag/06YJ)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open RingedSpaceModuleAdjunction

namespace Stacks.DerivedPullback.Composition

universe w₁ w₂ w₃ u


/-- The canonical natural isomorphism from the composite of the two pullback functors to
pullback along a composite of ringed-space morphisms.

Pullback is an abstract left adjoint, so the isomorphism is produced from the
pushforward-composition isomorphism by uniqueness of left adjoints. -/
noncomputable def modulePullbackComp {X Y Z : RingedSpace.{u, u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    modulePullback g ⋙ modulePullback f ≅ modulePullback (f ≫ g) :=
  Adjunction.leftAdjointCompIso (modulePullbackPushforwardAdjunction g)
    (modulePullbackPushforwardAdjunction f) (modulePullbackPushforwardAdjunction (f ≫ g))
    (RingedSpaceModuleAdjunction.modulePushforwardComp f g)

/-- The pullback-composition isomorphism on the unbounded homotopy categories. -/
noncomputable def pullbackOnHomotopyCompIso {X Y Z : RingedSpace.{u, u}} (f : X ⟶ Y)
    (g : Y ⟶ Z) :
    (modulePullback g).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        (modulePullback f).mapHomotopyCategory (ComplexShape.up ℤ) ≅
      (modulePullback (f ≫ g)).mapHomotopyCategory (ComplexShape.up ℤ) :=
  Functor.mapHomotopyCategoryCompIso (modulePullbackComp f g) (ComplexShape.up ℤ)

/-- **The pullback-composition isomorphism on the homotopy categories commutes with the shift.**
An instance of `CategoryTheory.Functor.commShift_mapHomotopyCategoryCompIso_hom`. -/
instance commShift_pullbackOnHomotopyCompIso_hom {X Y Z : RingedSpace.{u, u}} (f : X ⟶ Y)
    (g : Y ⟶ Z) :
    NatTrans.CommShift (pullbackOnHomotopyCompIso f g).hom ℤ :=
  Functor.commShift_mapHomotopyCategoryCompIso_hom (modulePullbackComp f g)

section

variable {X Y Z : RingedSpace.{u, u}} (f : X ⟶ Y) (g : Y ⟶ Z)
  [HasDerivedCategory.{w₁} (ModuleSheaves X)] [HasDerivedCategory.{w₂} (ModuleSheaves Y)]
  [HasDerivedCategory.{w₃} (ModuleSheaves Z)]
  (Lf : DerivedCategory (ModuleSheaves Y) ⥤ DerivedCategory (ModuleSheaves X))
  (Lg : DerivedCategory (ModuleSheaves Z) ⥤ DerivedCategory (ModuleSheaves Y))
  (εf : DerivedCategory.Qh ⋙ Lf ⟶
    Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.pullbackOnHomotopy f)
  (εg : DerivedCategory.Qh ⋙ Lg ⟶
    Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.pullbackOnHomotopy g)

/-- The comparison from the composite of the derived pullbacks along `g` and `f` to degreewise
pullback along `f ≫ g`.

It is the comparison for `Lg^*`, then the comparison for `Lf^*`, then the
pullback-composition isomorphism, in that order. -/
noncomputable def derivedPullbackCompCounit :
    DerivedCategory.Qh ⋙ (Lg ⋙ Lf) ⟶
      Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.pullbackOnHomotopy (f ≫ g) :=
  Functor.whiskerRight εg Lf ≫
    Functor.whiskerLeft ((modulePullback g).mapHomotopyCategory (ComplexShape.up ℤ)) εf ≫
    Functor.whiskerRight (pullbackOnHomotopyCompIso f g).hom DerivedCategory.Qh

/-- The value of `derivedPullbackCompCounit` at an object of the homotopy category, written out
as a composite of three maps.  Each whiskering contributes its component on the nose, so this
holds by definition; it is recorded once so that the three factors can be reasoned about
separately. -/
theorem derivedPullbackCompCounit_app
    (K : HomotopyCategory (ModuleSheaves Z) (ComplexShape.up ℤ)) :
    (derivedPullbackCompCounit f g Lf Lg εf εg).app K =
      Lf.map (εg.app K) ≫
        εf.app (((modulePullback g).mapHomotopyCategory (ComplexShape.up ℤ)).obj K) ≫
        DerivedCategory.Qh.map ((pullbackOnHomotopyCompIso f g).hom.app K) :=
  rfl

end

section

variable {X Y Z : RingedSpace.{u, u}} (f : X ⟶ Y) (g : Y ⟶ Z)
  [HasDerivedCategory.{w₁} (ModuleSheaves X)] [HasDerivedCategory.{w₂} (ModuleSheaves Y)]
  [HasDerivedCategory.{w₃} (ModuleSheaves Z)]
  (Lf : DerivedCategory (ModuleSheaves Y) ⥤ DerivedCategory (ModuleSheaves X))
  (Lg : DerivedCategory (ModuleSheaves Z) ⥤ DerivedCategory (ModuleSheaves Y))
  (Lgf : DerivedCategory (ModuleSheaves Z) ⥤ DerivedCategory (ModuleSheaves X))
  (εf : DerivedCategory.Qh ⋙ Lf ⟶
    Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.pullbackOnHomotopy f)
  (εg : DerivedCategory.Qh ⋙ Lg ⟶
    Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.pullbackOnHomotopy g)
  (εgf : DerivedCategory.Qh ⋙ Lgf ⟶
    Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.pullbackOnHomotopy (f ≫ g))
  (P : ObjectProperty (HomotopyCategory (ModuleSheaves Z) (ComplexShape.up ℤ)))
  (Q : ObjectProperty (HomotopyCategory (ModuleSheaves Y) (ComplexShape.up ℤ)))

/-- A comparison of a derived pullback is invertible at a complex of a class which resolves
every complex and whose quasi-isomorphisms degreewise pullback inverts.

This is how the hypotheses `hεg` and `hεf` of the composition formula are met: for the intended
class of K-flat complexes, the resolving property is Tag 06YS and the inversion property is the
exactness of pullback on K-flat complexes. -/
theorem isIso_app_of_resolving
    [Lf.IsLeftDerivedFunctor εf
      (HomotopyCategory.quasiIso (ModuleSheaves Y) (ComplexShape.up ℤ))]
    (hQ : Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.HasResolutions Q)
    (hinv : Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.PullbackInvertsQuasiIso f Q)
    (M : HomotopyCategory (ModuleSheaves Y) (ComplexShape.up ℤ)) (hM : Q M) :
    IsIso (εf.app M) :=
  LeftDerivedByResolutions.isIso_app_of_resolutions
    (HomotopyCategory.quasiIso (ModuleSheaves Y) (ComplexShape.up ℤ)) Q
    hQ (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.pullbackOnHomotopy f) hinv
    DerivedCategory.Qh Lf εf M hM

/-- The comparison from the composite of the two derived pullbacks to degreewise pullback along
`f ≫ g` is invertible at a complex of the resolving class.

Of its three factors the first is the image under `Lf^*` of the comparison for `Lg^*`, the
second is the comparison for `Lf^*` at the degreewise pullback along `g`, which lies in the
class `Q` by hypothesis, and the third is the image of an isomorphism. -/
theorem isIso_derivedPullbackCompCounit_app
    (hstab : ∀ K : HomotopyCategory (ModuleSheaves Z) (ComplexShape.up ℤ), P K →
      Q (((modulePullback g).mapHomotopyCategory (ComplexShape.up ℤ)).obj K))
    (hεg : ∀ K : HomotopyCategory (ModuleSheaves Z) (ComplexShape.up ℤ), P K →
      IsIso (εg.app K))
    (hεf : ∀ M : HomotopyCategory (ModuleSheaves Y) (ComplexShape.up ℤ), Q M →
      IsIso (εf.app M))
    (K : HomotopyCategory (ModuleSheaves Z) (ComplexShape.up ℤ)) (hK : P K) :
    IsIso ((derivedPullbackCompCounit f g Lf Lg εf εg).app K) := by
  rw [derivedPullbackCompCounit_app]
  have h₁ := hεg K hK
  have h₂ := hεf _ (hstab K hK)
  infer_instance

/-- **The composite of two derived pullbacks is a derived pullback along the composite.**  The
composite `Lg^* ⋙ Lf^*`, with the comparison `derivedPullbackCompCounit`, is a left derived
functor of degreewise pullback along `f ≫ g`.

A comparison invertible on a class that resolves every complex, and whose quasi-isomorphisms the
underived functor inverts, exhibits its functor as a left derived functor. -/
theorem isLeftDerivedFunctor_comp
    (hP : Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.HasResolutions P)
    (hinvgf : Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.PullbackInvertsQuasiIso (f ≫ g) P)
    (hstab : ∀ K : HomotopyCategory (ModuleSheaves Z) (ComplexShape.up ℤ), P K →
      Q (((modulePullback g).mapHomotopyCategory (ComplexShape.up ℤ)).obj K))
    (hεg : ∀ K : HomotopyCategory (ModuleSheaves Z) (ComplexShape.up ℤ), P K →
      IsIso (εg.app K))
    (hεf : ∀ M : HomotopyCategory (ModuleSheaves Y) (ComplexShape.up ℤ), Q M →
      IsIso (εf.app M)) :
    (Lg ⋙ Lf).IsLeftDerivedFunctor (derivedPullbackCompCounit f g Lf Lg εf εg)
      (HomotopyCategory.quasiIso (ModuleSheaves Z) (ComplexShape.up ℤ)) :=
  LeftDerivedByResolutions.isLeftDerivedFunctor_of_isIso_on_resolutions
    (HomotopyCategory.quasiIso (ModuleSheaves Z) (ComplexShape.up ℤ)) P
    hP (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.pullbackOnHomotopy (f ≫ g)) hinvgf
    DerivedCategory.Qh (Lg ⋙ Lf) (derivedPullbackCompCounit f g Lf Lg εf εg)
    (fun K hK => isIso_derivedPullbackCompCounit_app f g Lf Lg εf εg P Q hstab hεg hεf K hK)

/-- The canonical comparison from the composite of derived pullbacks along `g` and `f` to a
derived pullback along `f ≫ g`, obtained from the universal property of the latter.

By `CategoryTheory.Functor.leftDerived_fac`, postcomposing it with `εgf` returns
`derivedPullbackCompCounit f g Lf Lg εf εg`, which characterizes it. -/
noncomputable def derivedPullbackCompComparison
    [Lgf.IsLeftDerivedFunctor εgf
      (HomotopyCategory.quasiIso (ModuleSheaves Z) (ComplexShape.up ℤ))] :
    Lg ⋙ Lf ⟶ Lgf :=
  Lgf.leftDerivedLift εgf
    (HomotopyCategory.quasiIso (ModuleSheaves Z) (ComplexShape.up ℤ)) _
    (derivedPullbackCompCounit f g Lf Lg εf εg)

/-- **Stacks 0D5S, the composition formula.**  The canonical comparison from the composite of
derived pullbacks along `g` and `f` to a derived pullback along `f ≫ g` is an isomorphism.

Both functors are left derived functors of degreewise pullback along `f ≫ g`, and a map between
left derived functors induced by the universal property is invertible exactly then. -/
theorem isIso_derivedPullbackCompComparison
    [Lgf.IsLeftDerivedFunctor εgf
      (HomotopyCategory.quasiIso (ModuleSheaves Z) (ComplexShape.up ℤ))]
    (hP : Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.HasResolutions P)
    (hinvgf : Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.PullbackInvertsQuasiIso (f ≫ g) P)
    (hstab : ∀ K : HomotopyCategory (ModuleSheaves Z) (ComplexShape.up ℤ), P K →
      Q (((modulePullback g).mapHomotopyCategory (ComplexShape.up ℤ)).obj K))
    (hεg : ∀ K : HomotopyCategory (ModuleSheaves Z) (ComplexShape.up ℤ), P K →
      IsIso (εg.app K))
    (hεf : ∀ M : HomotopyCategory (ModuleSheaves Y) (ComplexShape.up ℤ), Q M →
      IsIso (εf.app M)) :
    IsIso (derivedPullbackCompComparison f g Lf Lg Lgf εf εg εgf) :=
  (Lgf.isLeftDerivedFunctor_iff_isIso_leftDerivedLift εgf
      (HomotopyCategory.quasiIso (ModuleSheaves Z) (ComplexShape.up ℤ)) (Lg ⋙ Lf)
      (derivedPullbackCompCounit f g Lf Lg εf εg)).1
    (isLeftDerivedFunctor_comp f g Lf Lg εf εg P Q hP hinvgf hstab hεg hεf)

/-- The natural isomorphism `Lg^* ⋙ Lf^* ≅ L(f ≫ g)^*` obtained by inverting the canonical
comparison. -/
noncomputable def derivedPullbackCompIso
    [Lgf.IsLeftDerivedFunctor εgf
      (HomotopyCategory.quasiIso (ModuleSheaves Z) (ComplexShape.up ℤ))]
    (hP : Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.HasResolutions P)
    (hinvgf : Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.PullbackInvertsQuasiIso (f ≫ g) P)
    (hstab : ∀ K : HomotopyCategory (ModuleSheaves Z) (ComplexShape.up ℤ), P K →
      Q (((modulePullback g).mapHomotopyCategory (ComplexShape.up ℤ)).obj K))
    (hεg : ∀ K : HomotopyCategory (ModuleSheaves Z) (ComplexShape.up ℤ), P K →
      IsIso (εg.app K))
    (hεf : ∀ M : HomotopyCategory (ModuleSheaves Y) (ComplexShape.up ℤ), Q M →
      IsIso (εf.app M)) :
    Lg ⋙ Lf ≅ Lgf :=
  haveI := isIso_derivedPullbackCompComparison f g Lf Lg Lgf εf εg εgf P Q hP hinvgf hstab hεg
    hεf
  asIso (derivedPullbackCompComparison f g Lf Lg Lgf εf εg εgf)

end

section Exact

variable {X Y Z : RingedSpace.{u, u}} (f : X ⟶ Y) (g : Y ⟶ Z)
  [HasDerivedCategory.{w₁} (ModuleSheaves X)] [HasDerivedCategory.{w₂} (ModuleSheaves Y)]
  [HasDerivedCategory.{w₃} (ModuleSheaves Z)]
  (Lf : DerivedCategory (ModuleSheaves Y) ⥤ DerivedCategory (ModuleSheaves X))
  (Lg : DerivedCategory (ModuleSheaves Z) ⥤ DerivedCategory (ModuleSheaves Y))
  (Lgf : DerivedCategory (ModuleSheaves Z) ⥤ DerivedCategory (ModuleSheaves X))
  (εf : DerivedCategory.Qh ⋙ Lf ⟶
    Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.pullbackOnHomotopy f)
  (εg : DerivedCategory.Qh ⋙ Lg ⟶
    Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.pullbackOnHomotopy g)
  (εgf : DerivedCategory.Qh ⋙ Lgf ⟶
    Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.pullbackOnHomotopy (f ≫ g))
  [PreservesFiniteLimits (modulePullback f)] [PreservesFiniteColimits (modulePullback f)]
  [PreservesFiniteLimits (modulePullback g)] [PreservesFiniteColimits (modulePullback g)]

omit [HasDerivedCategory.{w₁} (ModuleSheaves X)] [HasDerivedCategory.{w₂} (ModuleSheaves Y)]
  [HasDerivedCategory.{w₃} (ModuleSheaves Z)]
  [PreservesFiniteColimits (modulePullback f)] [PreservesFiniteColimits (modulePullback g)] in
/-- Pullback along a composite of morphisms along which pullback is exact is itself exact, for
finite limits.  The pullback-composition isomorphism transports exactness of the composite of
the two factors. -/
theorem preservesFiniteLimits_modulePullback_comp :
    PreservesFiniteLimits (modulePullback (f ≫ g)) :=
  preservesFiniteLimits_of_natIso (modulePullbackComp f g)

omit [HasDerivedCategory.{w₁} (ModuleSheaves X)] [HasDerivedCategory.{w₂} (ModuleSheaves Y)]
  [HasDerivedCategory.{w₃} (ModuleSheaves Z)]
  [PreservesFiniteLimits (modulePullback f)] [PreservesFiniteLimits (modulePullback g)] in
/-- Pullback along a composite of morphisms along which pullback is exact is itself exact, for
finite colimits. -/
theorem preservesFiniteColimits_modulePullback_comp :
    PreservesFiniteColimits (modulePullback (f ≫ g)) :=
  preservesFiniteColimits_of_natIso (modulePullbackComp f g)

/-- **Stacks 0D5S for exact pullbacks.**  Along morphisms of ringed spaces for which degreewise
pullback is exact, the canonical comparison from the composite of the derived pullbacks to a
derived pullback along the composite is an isomorphism, with no resolving class left over.

An exact pullback inverts every quasi-isomorphism, so the class of all complexes is a resolving
class for all three morphisms and the hypotheses of the composition formula are met by it. -/
theorem isIso_derivedPullbackCompComparison_of_exact
    [Lf.IsLeftDerivedFunctor εf
      (HomotopyCategory.quasiIso (ModuleSheaves Y) (ComplexShape.up ℤ))]
    [Lg.IsLeftDerivedFunctor εg
      (HomotopyCategory.quasiIso (ModuleSheaves Z) (ComplexShape.up ℤ))]
    [Lgf.IsLeftDerivedFunctor εgf
      (HomotopyCategory.quasiIso (ModuleSheaves Z) (ComplexShape.up ℤ))] :
    IsIso (derivedPullbackCompComparison f g Lf Lg Lgf εf εg εgf) :=
  have := preservesFiniteLimits_modulePullback_comp f g
  have := preservesFiniteColimits_modulePullback_comp f g
  isIso_derivedPullbackCompComparison f g Lf Lg Lgf εf εg εgf ⊤ ⊤
    (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.hasResolutions_top Z)
      (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.pullbackInvertsQuasiIso_top (f ≫ g))
    (fun _ _ => trivial)
    (fun K _ => isIso_app_of_resolving g Lg εg ⊤
      (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.hasResolutions_top Z)
      (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.pullbackInvertsQuasiIso_top g) K trivial)
    (fun M _ => isIso_app_of_resolving f Lf εf ⊤
      (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.hasResolutions_top Y)
      (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.pullbackInvertsQuasiIso_top f) M trivial)

end Exact

end Stacks.DerivedPullback.Composition

end
