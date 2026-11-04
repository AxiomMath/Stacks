module

public import StacksFrontier.Topology.Sheaves.Cohomology.HigherDirectImage.LocalizationComparison
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.Composition
public import StacksFrontier.Topology.Sheaves.Cohomology.PseudoCoherence.Defs
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Restriction to an open subspace is pullback along the open immersion

Let `(X, 𝒪_X)` be a ringed space and `U ⊆ X` open.  Restriction of sheaves of modules to the
open subspace `(U, 𝒪_X|_U)` is defined directly, as the pushforward
`CategoryTheory.SheafOfModules.pushforward` along the open-image functor `Opens U ⥤ Opens X`
with the identity map of structure sheaves; pullback along a morphism of ringed spaces is
defined abstractly, as the left adjoint of pushforward.  The two agree: restriction is *also* a
left adjoint of pushforward along the open immersion `j_U : (U, 𝒪_X|_U) ⟶ (X, 𝒪_X)`, and left
adjoints of one functor are canonically isomorphic.

From that identification, the pullback-composition isomorphism of Stacks 0D5S and the equality
`j_{f⁻¹(V)} ≫ f = f|_{f⁻¹(V)} ≫ j_V` of Stacks 01E5 give the compatibility of restriction with
pullback along an arbitrary morphism of ringed spaces, and hence the same compatibility applied
degreewise to a cochain complex.

Everything here is about the *ordinary*, non-derived, functors.

## Main definitions

* `AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.siteRestrictionAdjunction`: restriction to an
  open subspace is left adjoint to
  pushforward along the open immersion of that subspace.
* `AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.restrictModulesIsoPullback`: restriction to
  an open subspace *is* pullback along
  the open immersion.
* `AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.restrictModulesPullbackCompIso`: pullback
  along `f` followed by restriction to
  `f⁻¹(V)` agrees with restriction to `V` followed by pullback along `f|_{f⁻¹(V)}`.
* `AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.restrictComplexPullbackIso`: the same
  comparison applied degreewise to a cochain
  complex of modules.

## Implementation notes

The adjunction is `CategoryTheory.SheafOfModules.pushforwardPushforwardAdj` for Mathlib's
adjunction `U.isOpenEmbedding.functor ⊣ Opens.map (Opens.inclusion' U)` on categories of opens:
the comparison of sheaves of rings on the restriction side is the identity, because the
structure sheaf of the open subspace is by construction the restriction of `𝒪_X`, and on the
pushforward side it is `RingedSpaceModuleAdjunction.structureSheafHom` of the open immersion.
Its two hypotheses are checked sectionwise, where both reduce to restriction maps of `𝒪_X`
along the unit and the counit of the adjunction of opens.

Two definitionally equal spellings of the structure sheaf as a sheaf of rings are in play:
`StrictlyPerfect.structureSheafOfRings X`, through which
  `AlgebraicGeometry.RingedSpace.PseudoCoherence.restrictModules` is stated,
and `structureSheafRing X`, through which
`RingedSpaceModuleAdjunction.modulePullback` is stated.  Statements mixing the two elaborate
fine, the spellings agreeing by `rfl`, but *instance search* does not cross them: it matches at
`instances` transparency, so the `Preadditive` instance of one spelling is not the `Preadditive`
instance of the other, and nothing downstream of `Preadditive` — additivity, preservation of
zero morphisms, `CategoryTheory.Functor.mapHomologicalComplex` — is found for a composite of
one functor of each spelling.  Hence the four preparatory lemmas
`AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.pullbackCompRestrictModules_additive` through
`restrictModulesCompPullback_preservesZeroMorphisms`, each proved by *applying* the
general instance rather than searching for it, and the `@`-application of
`CategoryTheory.NatIso.mapHomologicalComplex` in
  `AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.restrictComplexPullbackIso` that
consumes them.  Building the complex-level isomorphism componentwise instead, with
`HomologicalComplex.Hom.isoOfComponents`, is a dead end: the component maps and the
commuting squares are each cheap on their own, but assembling them into a
`HomologicalComplex.Hom` exceeds the kernel's budget.

## References

* [The Stacks Project, Tag 01E5](https://stacks.math.columbia.edu/tag/01E5)
* [The Stacks Project, Tag 08CB](https://stacks.math.columbia.edu/tag/08CB)
* [The Stacks Project, Tag 0D5S](https://stacks.math.columbia.edu/tag/0D5S)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open RingedSpaceModuleAdjunction Stacks.Cohomology.HigherDirectImage

namespace AlgebraicGeometry.RingedSpace.KFlatDerivedPullback

universe u

/-- **Restriction to an open subspace is left adjoint to pushforward along the open immersion.**

Restriction is `CategoryTheory.SheafOfModules.pushforward` along the open-image functor
`U.isOpenEmbedding.functor : Opens U ⥤ Opens X` with the identity comparison of structure
sheaves, and pushforward along the open immersion `j_U` is the same construction along
`Opens.map j_U : Opens X ⥤ Opens U` with the comparison `structureSheafHom j_U`.  Since the two
functors on opens are adjoint, `CategoryTheory.SheafOfModules.pushforwardPushforwardAdj` applies
once its two compatibilities of the comparisons are checked, and both are checked sectionwise:
the first is a restriction map of `𝒪_X` on either side, and the second is the left triangle
identity of the adjunction of opens. -/
@[sga "4 IV 13.4" "special case", sga "4 Vbis 1.3.6" "special case"]
def siteRestrictionAdjunction (X : RingedSpace.{u, u}) (U : Opens X.carrier) :
    AlgebraicGeometry.RingedSpace.PseudoCoherence.restrictModules.{u, u} X U ⊣
      RingedSpaceModuleAdjunction.modulePushforward (openSubspaceInclusion X U) := by
  let j := openSubspaceInclusion X U
  let F := U.isOpenEmbedding.functor
  let G := Opens.map j.hom.base
  let adj : F ⊣ G := U.isOpenEmbedding.isOpenMap.adjunction
  letI : F.IsContinuous (Opens.grothendieckTopology (restrictToOpen X U : TopCat))
      (Opens.grothendieckTopology (X : TopCat)) := U.isOpenEmbedding.functor_isContinuous
  letI : G.IsContinuous (Opens.grothendieckTopology (X : TopCat))
      (Opens.grothendieckTopology (restrictToOpen X U : TopCat)) := by infer_instance
  let R := structureSheafRing X
  let S := structureSheafRing (restrictToOpen X U)
  let φ : S ⟶ (F.sheafPushforwardContinuous RingCat.{u} _ _).obj R := 𝟙 _
  let ψ : R ⟶ (G.sheafPushforwardContinuous RingCat.{u} _ _).obj S := structureSheafHom j
  have h1 : Functor.whiskerRight (NatTrans.op adj.counit) R.obj =
      ψ.hom ≫ G.op.whiskerLeft φ.hom := by
    ext V x
    rfl
  have h2 : φ.hom ≫ F.op.whiskerLeft ψ.hom ≫
      Functor.whiskerRight (NatTrans.op adj.unit) S.obj = 𝟙 S.obj := by
    ext V x
    change (R.obj.map (adj.counit.app (F.obj V.unop)).op ≫
      R.obj.map (F.map (adj.unit.app V.unop)).op) x = x
    rw [← Functor.map_comp, ← op_comp, adj.left_triangle_components V.unop]
    exact Functor.map_id_apply R.obj (op (F.obj V.unop)) x
  change SheafOfModules.pushforward φ ⊣ SheafOfModules.pushforward ψ
  exact SheafOfModules.pushforwardPushforwardAdj adj φ ψ h1 h2

/-- **Restriction to an open subspace is pullback along the open immersion.**  Both functors are
left adjoints of pushforward along `j_U`, so they are canonically isomorphic. -/
def restrictModulesIsoPullback (X : RingedSpace.{u, u}) (U : Opens X.carrier) :
    AlgebraicGeometry.RingedSpace.PseudoCoherence.restrictModules.{u, u} X U ≅
      RingedSpaceModuleAdjunction.modulePullback
        (Stacks.Cohomology.HigherDirectImage.openSubspaceInclusion X U) :=
  (siteRestrictionAdjunction X U).leftAdjointUniq
    (modulePullbackPushforwardAdjunction (openSubspaceInclusion X U))

/-- **Restriction commutes with pullback.**  Pulling a sheaf of `𝒪_Y`-modules back along `f` and
restricting to `f⁻¹(V)` agrees with restricting to `V` and pulling back along the restricted
morphism `f|_{f⁻¹(V)}`, naturally in the sheaf of modules.

Both restrictions are pullbacks along the two open immersions, by
`AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.restrictModulesIsoPullback`, so the two
  composites are pullbacks along
`j_{f⁻¹(V)} ≫ f` and along `f|_{f⁻¹(V)} ≫ j_V` by the composition formula
`Stacks.DerivedPullback.Composition.modulePullbackComp`; and those two morphisms of ringed spaces
  are equal, by
`Stacks.Cohomology.HigherDirectImage.restrictedMorphism_comp_openSubspaceInclusion`. -/
def restrictModulesPullbackCompIso {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)
    (V : Opens Y.carrier) :
    RingedSpaceModuleAdjunction.modulePullback f ⋙
        AlgebraicGeometry.RingedSpace.PseudoCoherence.restrictModules.{u, u} X
          (Stacks.Cohomology.HigherDirectImage.preimageOpen f V) ≅
      AlgebraicGeometry.RingedSpace.PseudoCoherence.restrictModules.{u, u} Y V ⋙
        RingedSpaceModuleAdjunction.modulePullback
          (Stacks.Cohomology.HigherDirectImage.restrictedMorphism f V) :=
  Functor.isoWhiskerLeft (modulePullback f)
      (restrictModulesIsoPullback X (preimageOpen f V)) ≪≫
    Stacks.DerivedPullback.Composition.modulePullbackComp
      (openSubspaceInclusion X (preimageOpen f V)) f ≪≫
    eqToIso (congrArg (fun m : restrictToOpen X (preimageOpen f V) ⟶ Y => modulePullback m)
      (restrictedMorphism_comp_openSubspaceInclusion f V)) ≪≫
    (Stacks.DerivedPullback.Composition.modulePullbackComp (restrictedMorphism f V)
      (openSubspaceInclusion Y V)).symm ≪≫
    Functor.isoWhiskerRight (restrictModulesIsoPullback Y V).symm
      (modulePullback (restrictedMorphism f V))

/-- Pullback along the restriction `f|_{f⁻¹(V)}` of a morphism of ringed spaces is additive.

This is `RingedSpaceModuleAdjunction.modulePullback_additive` at a morphism between two open
subspaces, where that instance is not found by search: the goal reaches the `Preadditive`
instance of the category of modules on an open subspace through the
`StrictlyPerfect.structureSheafOfRings` spelling of the structure sheaf and the instance
reaches it through the `structureSheafRing` spelling, and the two spellings
are not interchangeable at `instances` transparency.  It is an instance because the statement
of `AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.restrictComplexPullbackIso` needs it. -/
instance pullbackRestrictedMorphism_additive {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)
    (V : Opens Y.carrier) :
    (RingedSpaceModuleAdjunction.modulePullback
      (Stacks.Cohomology.HigherDirectImage.restrictedMorphism f V)).Additive :=
  modulePullback_additive _

/-- Pullback along `f` followed by restriction to `f⁻¹(V)` is additive.  Both factors are, and
the general instance for a composite is *applied* rather than searched for, since the search
would have to cross the two spellings of the structure sheaf. -/
theorem pullbackCompRestrictModules_additive {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)
    (V : Opens Y.carrier) :
    (RingedSpaceModuleAdjunction.modulePullback f ⋙
      AlgebraicGeometry.RingedSpace.PseudoCoherence.restrictModules.{u, u} X
        (Stacks.Cohomology.HigherDirectImage.preimageOpen f V)).Additive :=
  @Functor.instAdditiveComp _ _ _ _ _ _ (modulePullback f) (modulePullback_additive f) _ _ _
    (AlgebraicGeometry.RingedSpace.PseudoCoherence.restrictModules.{u, u} X (preimageOpen f V))
    (moduleRestriction_additive X (preimageOpen f V))

/-- Restriction to `V` followed by pullback along `f|_{f⁻¹(V)}` is additive. -/
theorem restrictModulesCompPullback_additive {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)
    (V : Opens Y.carrier) :
    (AlgebraicGeometry.RingedSpace.PseudoCoherence.restrictModules.{u, u} Y V ⋙
      RingedSpaceModuleAdjunction.modulePullback
        (Stacks.Cohomology.HigherDirectImage.restrictedMorphism f V)).Additive :=
  @Functor.instAdditiveComp _ _ _ _ _ _
    (AlgebraicGeometry.RingedSpace.PseudoCoherence.restrictModules.{u, u} Y V)
    (moduleRestriction_additive Y V) _ _ _ (modulePullback (restrictedMorphism f V))
    (modulePullback_additive _)

/-- Pullback along `f` followed by restriction to `f⁻¹(V)` preserves zero morphisms, being
additive.  The general instance is again applied explicitly. -/
theorem pullbackCompRestrictModules_preservesZeroMorphisms {X Y : RingedSpace.{u, u}}
    (f : X ⟶ Y) (V : Opens Y.carrier) :
    (RingedSpaceModuleAdjunction.modulePullback f ⋙
      AlgebraicGeometry.RingedSpace.PseudoCoherence.restrictModules.{u, u} X
        (Stacks.Cohomology.HigherDirectImage.preimageOpen f V)).PreservesZeroMorphisms :=
  @Functor.preservesZeroMorphisms_of_additive _ _ _ _ _ _ _
    (pullbackCompRestrictModules_additive f V)

/-- Restriction to `V` followed by pullback along `f|_{f⁻¹(V)}` preserves zero morphisms. -/
theorem restrictModulesCompPullback_preservesZeroMorphisms {X Y : RingedSpace.{u, u}}
    (f : X ⟶ Y) (V : Opens Y.carrier) :
    (AlgebraicGeometry.RingedSpace.PseudoCoherence.restrictModules.{u, u} Y V ⋙
      RingedSpaceModuleAdjunction.modulePullback
        (Stacks.Cohomology.HigherDirectImage.restrictedMorphism f V)).PreservesZeroMorphisms :=
  @Functor.preservesZeroMorphisms_of_additive _ _ _ _ _ _ _
    (restrictModulesCompPullback_additive f V)

/-- **Restriction commutes with pullback, degreewise on complexes.**  The restriction to
`f⁻¹(V)` of the degreewise pullback along `f` of a cochain complex of `𝒪_Y`-modules is the
degreewise pullback along `f|_{f⁻¹(V)}` of its restriction to `V`.

This is `AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.restrictModulesPullbackCompIso` carried
  through
`CategoryTheory.NatIso.mapHomologicalComplex` and evaluated at the complex. -/
def restrictComplexPullbackIso {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)
    (V : Opens Y.carrier) (P : CochainComplex (StrictlyPerfect.OXMod.{u} Y) ℤ) :
    AlgebraicGeometry.RingedSpace.PseudoCoherence.restrictComplex
        (((RingedSpaceModuleAdjunction.modulePullback f).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj P)
        (Stacks.Cohomology.HigherDirectImage.preimageOpen f V) ≅
      ((RingedSpaceModuleAdjunction.modulePullback
          (Stacks.Cohomology.HigherDirectImage.restrictedMorphism f V)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj (AlgebraicGeometry.RingedSpace.PseudoCoherence.restrictComplex P V)
          :=
  (@NatIso.mapHomologicalComplex ℤ _ _ _ _ _ _ _ _
    (pullbackCompRestrictModules_preservesZeroMorphisms f V)
    (restrictModulesCompPullback_preservesZeroMorphisms f V)
    (restrictModulesPullbackCompIso f V) (ComplexShape.up ℤ)).app P

end AlgebraicGeometry.RingedSpace.KFlatDerivedPullback

end
