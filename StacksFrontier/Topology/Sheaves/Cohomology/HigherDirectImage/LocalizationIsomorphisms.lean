module

public import Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.SheafOfModules
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.CategoryTheory.Preadditive.Injective.Preserves
public import StacksFrontier.Topology.Sheaves.Cohomology.HigherDirectImage.LocalizationComparison
public import StacksFrontier.CategoryTheory.Sites.Cohomology.HigherDirectImage.CompositeRightDerivedFunctors
public import StacksFrontier.Topology.Sheaves.OpenImmersion.ModuleExtensionByZeroExact
public import StacksCore.Tactic.StacksAttribute

/-!
# Localization of higher direct images: the two displayed isomorphisms

Let `f : (X, 𝒪_X) ⟶ (Y, 𝒪_Y)` be a morphism of ringed spaces, let `V ⊆ Y` be open and let
`U = f⁻¹(V)`.  Stacks 01E5 asserts that higher direct images commute with restriction to `V`:

  `(R^p f_* ℱ)|_V = R^p (f|_U)_* (ℱ|_U)`,

and that the same holds for the total right derived pushforward of a bounded below complex.

`StacksFrontier.Topology.Sheaves.Cohomology.HigherDirectImage.LocalizationComparison` constructs
  everything around these statements — the restricted
morphism `f|_U`, the undeived comparison `modulePushforwardRestrictIso`, the exactness of
restriction, and `rightDerivedPushforwardRestrictIso`, which derives the *composite*
`ℱ ↦ (f|_U)_*(ℱ|_U)`.  The one missing input there was Stacks 01E1, that restriction to an open
subspace preserves injectives.  That is proved here, now that extension by zero is known to be
exact (`StacksFrontier.Topology.Sheaves.OpenImmersion.ModuleExtensionByZeroExact`), and the two
displayed isomorphisms follow.

## Main results

* `jStar_preservesInjectiveObjects` and `jStar_injective_obj` are **Stacks 01E1**: restriction of
  a sheaf of modules to an open subspace takes injectives to injectives.  This is the
  right-adjoint half of `ExtensionByZeroModules.jShriekAdjunction`, whose left adjoint `j_!`
  preserves monomorphisms.  `moduleRestriction_preservesInjectiveObjects` is the form for a
  ringed space.
* `higherDirectImageRestrictIso` is the first displayed isomorphism of **Stacks 01E5**: for every
  `p`, restricting the `p`-th higher direct image along `f` to `V` is the `p`-th higher direct
  image along `f|_U` of the restriction to `U`, naturally in the sheaf of modules.
* `higherDirectImageRestrictIso_zero_compatibility` pins the former down in degree zero: it is
  the undeived comparison, after the canonical maps to the zeroth right derived functors.
* `derivedPushforwardPlusRestrictIso` is the second displayed isomorphism of **Stacks 01E5**, on
  bounded below derived categories.
* `derivedPushforwardPlusRestrictIso_unit_compatibility` pins the latter down: it is the
  isomorphism of right derived functors induced by the undeived comparison.

## Implementation notes

For the first isomorphism, `rightDerivedPushforwardRestrictIso` says that
`(R^p f_*) ⋙ (-)|_V` computes the right derived functors of the composite
`ℱ ↦ (f|_U)_*(ℱ|_U)`, because restriction to `V` is exact.  Stacks 01E1 turns those into
`(-)|_U ⋙ R^p (f|_U)_*`: an exact functor preserving injectives carries an injective resolution
to an injective resolution, which is
  `Stacks.Cohomology.CompositeRightDerived.compRightDerivedNatIso`.  That is
`higherDirectImageRestrictIsoSucc`, and it is what `higherDirectImageRestrictIso` uses in
positive degree.  In degree zero both pushforwards are left exact, so the comparison is
normalized to the undeived one, `higherDirectImageRestrictIsoZero`; that is forced, since the
positive-degree construction is not visibly compatible with `Functor.toRightDerivedZero`.

For the second isomorphism both sides are right derived functors, along
`DerivedCategory.Plus.Qh` and relative to quasi-isomorphisms, of the two composites of termwise
functors on bounded below homotopy categories, with units
`successiveRightDerivedFunctorPlusUnit`.  The two reasons differ:
`isRightDerivedFunctor_successiveUnit_of_preservesInjectiveObjects` uses that restriction to `U`
is exact and preserves injectives, so that it carries complexes of injectives to complexes of
injectives; `isRightDerivedFunctor_successiveUnit_of_isIso_unit` uses that restriction to `V` is
exact, so that *its* derived-functor unit is an isomorphism everywhere.  The isomorphism is then
`Functor.rightDerivedNatIso` applied to `modulePushforwardRestrictHomotopyIso`, and the
compatibility with the units is `Functor.rightDerivedNatTrans_fac`.

One clause of the tag is **not** proved here, namely
`higherDirectImageRestrictIso_injectiveResolution`, which characterizes the first isomorphism on
an *arbitrary* injective resolution `I` of the sheaf, an arbitrary injective resolution `J` of
its restriction, and an arbitrary comparison `φ : J ⟶ ℱ|_U`-resolution lifting the identity.
Both `Stacks.Cohomology.CompositeRightDerived.compRightDerivedNatIso` and
`Stacks.Cohomology.ModuleComparison.rightDerivedCompIso` are built on the *chosen* resolution
`injectiveResolution M`, so that clause needs the transport of
`CategoryTheory.InjectiveResolution.isoRightDerivedObj` from the chosen resolution to `(I, J, φ)`
in both variables at once, which is not available.

## References

* [The Stacks Project, Tag 01E5](https://stacks.math.columbia.edu/tag/01E5)
* [The Stacks Project, Tag 01E1](https://stacks.math.columbia.edu/tag/01E1)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open RingedSpaceModuleAdjunction

universe u

namespace Stacks.Cohomology.HigherDirectImage

/-! ### Stacks 01E1: restriction to an open subspace preserves injectives -/

section Injectives

variable {T : TopCat.{u}} (U : Opens T)
  (O : Sheaf (Opens.grothendieckTopology T) RingCat.{u})

/-- **Stacks 01E1: restriction to an open subspace preserves injective objects.**  Restriction
`j^{-1}` is the right adjoint of extension by zero `j_!` (Stacks 00A7 (2)), and `j_!` preserves
monomorphisms — indeed it is exact — so the general adjunction criterion applies.

This is stated for a sheaf of (not necessarily commutative) rings on a topological space, which
is where extension by zero lives; the ringed-space form is
`moduleRestriction_preservesInjectiveObjects`. -/
theorem jStar_preservesInjectiveObjects :
    (ExtensionByZeroModules.jStar U O).PreservesInjectiveObjects :=
  Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
    (ExtensionByZeroModules.jShriekAdjunction U O)

/-- **Stacks 01E1.**  The restriction to an open subspace of an injective sheaf of modules is
injective. -/
theorem jStar_injective_obj (I : SheafOfModules.{u} O) [Injective I] :
    Injective ((ExtensionByZeroModules.jStar U O).obj I) :=
  (jStar_preservesInjectiveObjects U O).injective_obj inferInstance

end Injectives

section RingedSpaceInjectives

variable (X : RingedSpace.{u, u}) (U : Opens X)

/-- Stacks 01E1 for a ringed space: ordinary restriction of sheaves of modules to an open
subspace preserves injective objects. -/
instance moduleRestriction_preservesInjectiveObjects :
    (moduleRestriction X U).PreservesInjectiveObjects :=
  @Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms _ _ _ _ _ _
    (ExtensionByZeroModules.jShriekAdjunction U (structureSheafRing X))
    (ExtensionByZeroModules.jShriek_preservesMonomorphisms U (structureSheafRing X))

/-- Restriction to an open subspace preserves finite colimits, being a left adjoint. -/
instance moduleRestriction_preservesFiniteColimits :
    PreservesFiniteColimits (moduleRestriction X U) :=
  have := moduleRestriction_isLeftAdjoint X U
  inferInstance

end RingedSpaceInjectives

/-! ### The first displayed isomorphism: higher direct images -/

section HigherDirectImage

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y) (V : Opens Y)

/-- The localization isomorphism in positive degree: restriction to `V` is exact, so by
`rightDerivedPushforwardRestrictIso` the right-hand side is the `p`-th right derived functor of
the composite `ℱ ↦ (f|_U)_*(ℱ|_U)`; restriction to `U` is exact and preserves injectives by
Stacks 01E1, so by `Stacks.Cohomology.CompositeRightDerived.compRightDerivedNatIso` those agree
  with the left-hand
side. -/
noncomputable def higherDirectImageRestrictIsoSucc (p : ℕ) :
    moduleRestriction X (preimageOpen f V) ⋙
          (modulePushforward (restrictedMorphism f V)).rightDerived p ≅
        (modulePushforward f).rightDerived p ⋙ moduleRestriction Y V :=
  (rightDerivedPushforwardRestrictIso f V p ≪≫
    Stacks.Cohomology.CompositeRightDerived.compRightDerivedNatIso (moduleRestriction X
      (preimageOpen f V))
      (modulePushforward (restrictedMorphism f V)) p).symm

/-- The localization isomorphism in degree zero, normalized: the two pushforwards are left
exact, so both zeroth right derived functors are canonically the functors themselves, and the
isomorphism is the undeived comparison `modulePushforwardRestrictIso` read through those
normalizations.  This is what makes `higherDirectImageRestrictIso_zero_compatibility` true. -/
noncomputable def higherDirectImageRestrictIsoZero :
    moduleRestriction X (preimageOpen f V) ⋙
          (modulePushforward (restrictedMorphism f V)).rightDerived 0 ≅
        (modulePushforward f).rightDerived 0 ⋙ moduleRestriction Y V :=
  Functor.isoWhiskerLeft (moduleRestriction X (preimageOpen f V))
      (modulePushforward (restrictedMorphism f V)).rightDerivedZeroIsoSelf ≪≫
    modulePushforwardRestrictIso f V ≪≫
    Functor.isoWhiskerRight (modulePushforward f).rightDerivedZeroIsoSelf.symm
      (moduleRestriction Y V)

/-- **Stacks 01E5, higher direct images.**  Higher direct images commute naturally with
restriction to an open subspace: for `U = f⁻¹(V)`, restricting a sheaf of `𝒪_X`-modules to `U`
and taking the `p`-th higher direct image along `f|_U` agrees with taking the `p`-th higher
direct image along `f` and restricting to `V`.

In positive degree this is `higherDirectImageRestrictIsoSucc`, which rests on Stacks 01E1; in
degree zero it is the normalized comparison `higherDirectImageRestrictIsoZero`, so that the
degree-zero compatibility below holds by construction. -/
@[stacks 01E5 "higher direct images", sga "4 V 5.1" "Clause 3, special case"]
noncomputable def higherDirectImageRestrictIso (p : ℕ) :
    moduleRestriction X (preimageOpen f V) ⋙
          (modulePushforward (restrictedMorphism f V)).rightDerived p ≅
        (modulePushforward f).rightDerived p ⋙ moduleRestriction Y V :=
  match p with
  | 0 => higherDirectImageRestrictIsoZero f V
  | n + 1 => higherDirectImageRestrictIsoSucc f V (n + 1)

/-- **Stacks 01E5, degree-zero compatibility.**  In degree zero the higher-direct-image
comparison is the ordinary restriction comparison, after the canonical maps to the zeroth right
derived functors.  This rules out multiplying the degree-zero comparison by an automorphism. -/
@[stacks 01E5 "degree-zero compatibility"]
theorem higherDirectImageRestrictIso_zero_compatibility :
    Functor.whiskerLeft
          (moduleRestriction X (preimageOpen f V))
          (modulePushforward (restrictedMorphism f V)).toRightDerivedZero ≫
        (higherDirectImageRestrictIso f V 0).hom =
      (modulePushforwardRestrictIso f V).hom ≫
        Functor.whiskerRight (modulePushforward f).toRightDerivedZero
          (moduleRestriction Y V) := by
  dsimp only [higherDirectImageRestrictIso, higherDirectImageRestrictIsoZero]
  rw [Iso.trans_hom, Iso.trans_hom, Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Iso.symm_hom, Functor.rightDerivedZeroIsoSelf_inv, ← Category.assoc,
    ← Functor.whiskerLeft_comp, Functor.rightDerivedZeroIsoSelf_inv_hom_id,
    Functor.whiskerLeft_id', Category.id_comp]

end HigherDirectImage

/-! ### Right derived functors of a composite on bounded below derived categories -/

section DerivedPlus

attribute [local instance] HasDerivedCategory.standard

variable {A B C : Type*} [Category* A] [Category* B] [Category* C]
  [Abelian A] [Abelian B] [Abelian C]
  [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory C]
  (F : CategoryTheory.Functor A B) (G : CategoryTheory.Functor B C)
  [F.Additive] [G.Additive]
  [EnoughInjectives A] [EnoughInjectives B]

/-- The successive units for two standard bounded-below right derived functors: first the unit
of `G`, applied to the image of the termwise functor of `F`, then the unit of `F` pushed through
the right derived functor of `G`. -/
noncomputable def successiveRightDerivedFunctorPlusUnit :
    F.mapHomotopyCategoryPlus ⋙ G.mapHomotopyCategoryPlus ⋙
        DerivedCategory.Plus.Qh ⟶
      DerivedCategory.Plus.Qh ⋙ F.rightDerivedFunctorPlus ⋙
        G.rightDerivedFunctorPlus :=
  Functor.whiskerLeft F.mapHomotopyCategoryPlus G.rightDerivedFunctorPlusUnit ≫
    Functor.whiskerRight F.rightDerivedFunctorPlusUnit G.rightDerivedFunctorPlus

/-- The successive units form a derived-functor unit as soon as `G`'s unit is an isomorphism on the
image under `F` of every bounded below complex of injectives. -/
private theorem isRightDerivedFunctor_successiveUnit_of_isIso_app_map
    (h : ∀ K : HomotopyCategory.Plus (InjectiveObject A),
      IsIso (G.rightDerivedFunctorPlusUnit.app (F.mapHomotopyCategoryPlus.obj
        ((InjectiveObject.ι A).mapHomotopyCategoryPlus.obj K)))) :
    (F.rightDerivedFunctorPlus ⋙ G.rightDerivedFunctorPlus).IsRightDerivedFunctor
      (successiveRightDerivedFunctorPlusUnit F G) (HomotopyCategory.Plus.quasiIso A) := by
  refine (HomotopyCategory.Plus.localizerMorphism_derives _).isRightDerivedFunctor_of_isIso
    _ (fun K => ?_)
  change IsIso ((Functor.whiskerLeft F.mapHomotopyCategoryPlus G.rightDerivedFunctorPlusUnit ≫
    Functor.whiskerRight F.rightDerivedFunctorPlusUnit G.rightDerivedFunctorPlus).app _)
  rw [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app]
  have := h K
  have : IsIso (F.rightDerivedFunctorPlusUnit.app
    ((InjectiveObject.ι A).mapHomotopyCategoryPlus.obj K)) := inferInstance
  infer_instance

/-- **If `F` preserves injectives then the composite of the two bounded below right derived
functors is the right derived functor of the composite of the termwise functors**, with
`successiveRightDerivedFunctorPlusUnit` as its unit.  By the injective derivability structure
it suffices to check that the unit is an isomorphism on a bounded below complex `K` of
injectives; the unit of `F` is an isomorphism there, and `F K` is again a complex of
injectives, so the unit of `G` is an isomorphism on it. -/
theorem isRightDerivedFunctor_successiveUnit_of_preservesInjectiveObjects
    [F.PreservesInjectiveObjects] :
    (F.rightDerivedFunctorPlus ⋙ G.rightDerivedFunctorPlus).IsRightDerivedFunctor
      (successiveRightDerivedFunctorPlusUnit F G) (HomotopyCategory.Plus.quasiIso A) := by
  refine isRightDerivedFunctor_successiveUnit_of_isIso_app_map F G (fun K => ?_)
  set KK := (InjectiveObject.ι A).mapHomotopyCategoryPlus.obj K
  have : ∀ n : ℤ, Injective ((F.mapHomotopyCategoryPlus.obj KK).obj.as.X n) :=
    fun n => F.injective_obj (KK.obj.as.X n)
  infer_instance

/-- **If the derived-functor unit of `G` is an isomorphism — for instance if `G` is exact — then
the composite of the two bounded below right derived functors is the right derived functor of
the composite of the termwise functors**, with `successiveRightDerivedFunctorPlusUnit` as its
unit.  Again it suffices to check the unit on a bounded below complex of injectives, where the
unit of `F` is an isomorphism. -/
theorem isRightDerivedFunctor_successiveUnit_of_isIso_unit
    (hG : IsIso G.rightDerivedFunctorPlusUnit) :
    (F.rightDerivedFunctorPlus ⋙ G.rightDerivedFunctorPlus).IsRightDerivedFunctor
      (successiveRightDerivedFunctorPlusUnit F G) (HomotopyCategory.Plus.quasiIso A) :=
  isRightDerivedFunctor_successiveUnit_of_isIso_app_map F G
    (fun _ => NatIso.isIso_app_of_isIso _ _)

end DerivedPlus

/-! ### The second displayed isomorphism: bounded below derived pushforward -/

section DerivedRestriction

attribute [local instance] HasDerivedCategory.standard

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y) (V : Opens Y)

/-- The undeived comparison `modulePushforwardRestrictIso` induces the corresponding comparison
between the two composites of termwise functors on bounded below homotopy categories. -/
noncomputable def modulePushforwardRestrictHomotopyIso :
    (moduleRestriction X (preimageOpen f V)).mapHomotopyCategoryPlus ⋙
        (modulePushforward (restrictedMorphism f V)).mapHomotopyCategoryPlus ≅
      (modulePushforward f).mapHomotopyCategoryPlus ⋙
        (moduleRestriction Y V).mapHomotopyCategoryPlus :=
  (Functor.mapHomotopyCategoryPlusCompIso (modulePushforwardRestrictIso f V)).trans
    (Functor.mapHomotopyCategoryPlusCompIso
      (Iso.refl (modulePushforward f ⋙ moduleRestriction Y V))).symm

/-- **Stacks 01E5, bounded below derived image.**  The total right derived pushforward of a
bounded below complex commutes naturally with restriction to an open subspace: deriving
restriction to `U = f⁻¹(V)` and then pushforward along `f|_U` agrees with deriving pushforward
along `f` and then restriction to `V`.

Both sides are right derived functors, along `DerivedCategory.Plus.Qh` and relative to
quasi-isomorphisms, of the two composites of termwise functors; the isomorphism is the one
induced by `modulePushforwardRestrictHomotopyIso` through uniqueness of right derived
functors. -/
@[stacks 01E5 "bounded below derived image"]
noncomputable def derivedPushforwardPlusRestrictIso :
    (moduleRestriction X (preimageOpen f V)).rightDerivedFunctorPlus ⋙
          (modulePushforward (restrictedMorphism f V)).rightDerivedFunctorPlus ≅
        (modulePushforward f).rightDerivedFunctorPlus ⋙
          (moduleRestriction Y V).rightDerivedFunctorPlus :=
  have _h₁ := isRightDerivedFunctor_successiveUnit_of_preservesInjectiveObjects
    (moduleRestriction X (preimageOpen f V)) (modulePushforward (restrictedMorphism f V))
  have _h₂ := isRightDerivedFunctor_successiveUnit_of_isIso_unit (modulePushforward f)
    (moduleRestriction Y V) (moduleRestrictionRightDerivedFunctorPlusUnit_isIso Y V)
  Functor.rightDerivedNatIso _ _
    (successiveRightDerivedFunctorPlusUnit (moduleRestriction X (preimageOpen f V))
      (modulePushforward (restrictedMorphism f V)))
    (successiveRightDerivedFunctorPlusUnit (modulePushforward f) (moduleRestriction Y V))
    (HomotopyCategory.Plus.quasiIso _)
    (Functor.isoWhiskerRight (modulePushforwardRestrictHomotopyIso f V)
      DerivedCategory.Plus.Qh)

/-- **Stacks 01E5, compatibility with derived units.**  The derived localization isomorphism is
the one induced by the undeived comparison: after precomposition with the localization functor
its hom intertwines the two composite derived-functor units.  This is the defining
factorization of `Functor.rightDerivedNatTrans`. -/
@[stacks 01E5 "compatibility with derived units"]
theorem derivedPushforwardPlusRestrictIso_unit_compatibility :
    Functor.whiskerRight (modulePushforwardRestrictHomotopyIso f V).hom
          DerivedCategory.Plus.Qh ≫
        successiveRightDerivedFunctorPlusUnit (modulePushforward f) (moduleRestriction Y V) =
      successiveRightDerivedFunctorPlusUnit (moduleRestriction X (preimageOpen f V))
          (modulePushforward (restrictedMorphism f V)) ≫
        Functor.whiskerLeft DerivedCategory.Plus.Qh
          (derivedPushforwardPlusRestrictIso f V).hom :=
  have _h₁ := isRightDerivedFunctor_successiveUnit_of_preservesInjectiveObjects
    (moduleRestriction X (preimageOpen f V)) (modulePushforward (restrictedMorphism f V))
  have _h₂ := isRightDerivedFunctor_successiveUnit_of_isIso_unit (modulePushforward f)
    (moduleRestriction Y V) (moduleRestrictionRightDerivedFunctorPlusUnit_isIso Y V)
  (Functor.rightDerivedNatTrans_fac _ _
    (successiveRightDerivedFunctorPlusUnit (moduleRestriction X (preimageOpen f V))
      (modulePushforward (restrictedMorphism f V)))
    (successiveRightDerivedFunctorPlusUnit (modulePushforward f) (moduleRestriction Y V))
    (HomotopyCategory.Plus.quasiIso _)
    (Functor.whiskerRight (modulePushforwardRestrictHomotopyIso f V).hom
      DerivedCategory.Plus.Qh)).symm

end DerivedRestriction

end Stacks.Cohomology.HigherDirectImage

end
