module

public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImage.DerivedIdentityFunctorComparison
public import StacksFrontier.Algebra.Homology.HomotopyCategoryTransition
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.CompositionUnconditional
public import StacksFrontier.Topology.Sheaves.Cohomology.SupportedComplexes.ClosedSubsetPullbackRightExact

/-!
# The two unit laws for the composition isomorphism of derived pullback, for ringed spaces

For composable morphisms `f`, `g` of ringed spaces, [Stacks, Tag 0D5S] provides a canonical
isomorphism `Lg^* ⋙ Lf^* ≅ L(f ≫ g)^*`,
`Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical`. This file proves the two
unit laws for it: taking one of the two morphisms to be an identity returns the identification
`L(𝟙)^* ≅ 𝟭`, whiskered.

Everything is proved at an **arbitrary** model of the derived categories, which is what makes it
usable for schemes: `Stacks.Duality.derivedPullback` is this derived pullback at the locally
small model `AlgebraicGeometry.Scheme.Modules.hasDerivedCategory`, the only one at which
`D_QCoh(𝒪_X)` has the direct sums [Stacks, Tag 0A9E] needs, whereas
`Stacks.Cohomology.DerivedPushforwardAssociativity.derivedPullbackCompIsoCanonical_id_comp` and
`...derivedPullbackCompIsoCanonical_comp_id` are stated only at
`CategoryTheory.HasDerivedCategory.standard`, and `CategoryTheory.HasDerivedCategory` carries
the localization as data. The same situation, and the same remedy, as for the cocycle law of
`StacksFrontier/AlgebraicGeometry/Duality/TwistedInverseImage/DerivedPullbackCocycle.lean`.

The identification of `L(𝟙)^*` with `𝟭` used here is built from degreewise pullback along the
identity rather than by uniqueness of right adjoints, so that it is the one of
`Stacks.Duality.derivedPullbackIdIso`; `Stacks.Duality.derivedPullbackIdIso_eq` records that.

## Main results

All in the namespace `Stacks.DerivedPullback.Composition`.

* `modulePushforwardComp_id_comp` and `modulePushforwardComp_comp_id` — the unit laws for the
  composition isomorphism of degreewise pushforward of sheaves of modules. Its components are
  identity morphisms, so both are `rfl` componentwise.
* `modulePullbackComp_id_comp` and `modulePullbackComp_comp_id` — the unit laws for degreewise
  pullback, obtained from the previous pair by the mates calculus, because
  `Stacks.DerivedPullback.Composition.modulePullbackComp` is defined as a mate.
* `pullbackOnHomotopyCompIso_id_comp` and `pullbackOnHomotopyCompIso_comp_id` — the same on the
  unbounded homotopy categories of cochain complexes.
* `derivedPullbackCompIsoCanonical_id_comp_anyModel` and
  `...derivedPullbackCompIsoCanonical_comp_id_anyModel` — **the two unit laws for
  [Stacks, Tag 0D5S]**, at an arbitrary model of the derived categories.

The scheme-level consequences, at the locally small model, are in
`StacksFrontier/AlgebraicGeometry/Duality/TwistedInverseImage/DerivedPullbackUnitLaws.lean`.

## Implementation notes

*The route.* Both derived laws are proved by `CategoryTheory.Functor.leftDerived_ext`: a natural
transformation out of `L(f ≫ g)^*` is pinned by its composite with the comparison
`Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullbackComparison`, and
`CategoryTheory.Functor.leftDerived_fac_app` computes that composite for the comparison of
Tag 0D5S as the three-factor expression
`Stacks.DerivedPullback.Composition.derivedPullbackCompCounit_app`. Of its three factors the
third is the degreewise unit law read on the homotopy category, and the remaining two are
reduced to the factorization `CategoryTheory.leftDerivedToIdIso_hom_app_Qh` by naturality of the
comparison — on the left by naturality of `derivedPullbackIdIso`, on the right by naturality of
the comparison for `Lf^*`.

*Why the identity morphisms are not cancelled by `simp`.* The derived pullbacks along `f ≫ 𝟙 Y`
and along `f` are definitionally equal but not syntactically so, and a composite whose middle
object is spelled the two ways is well typed and opaque to `rw` and `simp`, whose matching runs
below default transparency. The final steps are therefore `Eq.trans`, `congrArg` and `▸` chains.

## References

* [Stacks Project, Tag 0D5S](https://stacks.math.columbia.edu/tag/0D5S)
* [Stacks Project, Tag 079W](https://stacks.math.columbia.edu/tag/079W)
* [Stacks Project, Tag 0ATY](https://stacks.math.columbia.edu/tag/0ATY)
* [Stacks Project, Tag 0A9E](https://stacks.math.columbia.edu/tag/0A9E)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
open RingedSpaceModuleAdjunction (ModuleSheaves modulePullback modulePushforward
  modulePullbackId modulePushforwardId modulePushforwardComp
  modulePullbackPushforwardAdjunction preservesFiniteColimits_modulePullback)
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPullback derivedPullbackComparison
  pullbackOnHomotopy)

universe w₁ w₂ w₃ u

namespace Stacks.DerivedPullback.Composition

/-! ### Degreewise pullback along an identity morphism -/

section Degreewise

variable {X Y Z : RingedSpace.{u, u}}

/-- **The left unit law for the composition isomorphism of degreewise pushforward.** Every
component of `RingedSpaceModuleAdjunction.modulePushforwardComp` and of
`RingedSpaceModuleAdjunction.modulePushforwardId` is an identity morphism. -/
theorem modulePushforwardComp_id_comp (g : Y ⟶ Z) :
    modulePushforwardComp (𝟙 Y) g =
      isoWhiskerRight (modulePushforwardId Y) (modulePushforward g) ≪≫
        leftUnitor (modulePushforward g) :=
  Iso.ext (NatTrans.ext (funext fun _ => rfl))

/-- **The right unit law for the composition isomorphism of degreewise pushforward.** -/
theorem modulePushforwardComp_comp_id (f : X ⟶ Y) :
    modulePushforwardComp f (𝟙 Y) =
      isoWhiskerLeft (modulePushforward f) (modulePushforwardId Y) ≪≫
        rightUnitor (modulePushforward f) :=
  Iso.ext (NatTrans.ext (funext fun _ => rfl))

/-- **The left unit law for the composition isomorphism of degreewise pullback**, with `(𝟙 Y)^*`
identified with the identity functor by `RingedSpaceModuleAdjunction.modulePullbackId`. -/
theorem modulePullbackComp_id_comp (g : Y ⟶ Z) :
    modulePullbackComp (𝟙 Y) g =
      isoWhiskerLeft (modulePullback g) (modulePullbackId Y) ≪≫
        rightUnitor (modulePullback g) :=
  Adjunction.leftAdjointCompIso_comp_id (modulePullbackPushforwardAdjunction g)
    (modulePullbackPushforwardAdjunction (𝟙 Y)) _ _ (modulePushforwardComp_id_comp g)

/-- **The right unit law for the composition isomorphism of degreewise pullback.** -/
theorem modulePullbackComp_comp_id (f : X ⟶ Y) :
    modulePullbackComp f (𝟙 Y) =
      isoWhiskerRight (modulePullbackId Y) (modulePullback f) ≪≫
        leftUnitor (modulePullback f) :=
  Adjunction.leftAdjointCompIso_id_comp (modulePullbackPushforwardAdjunction (𝟙 Y))
    (modulePullbackPushforwardAdjunction f) _ _ (modulePushforwardComp_comp_id f)

/-- Morphisms of complexes that agree in each degree have equal images in the homotopy
category. -/
private theorem quotient_map_congr {C : Type*} [Category C] [Preadditive C] {c : ComplexShape ℤ}
    {K L : HomologicalComplex C c} {φ ψ : K ⟶ L} (h : ∀ i, φ.f i = ψ.f i) :
    (HomotopyCategory.quotient C c).map φ = (HomotopyCategory.quotient C c).map ψ :=
  congrArg _ (HomologicalComplex.hom_ext _ _ h)

/-- **The left unit law on the unbounded homotopy categories**, for the composition isomorphism
`pullbackOnHomotopyCompIso`. -/
theorem pullbackOnHomotopyCompIso_id_comp (g : Y ⟶ Z)
    (K : HomotopyCategory (ModuleSheaves Z) (ComplexShape.up ℤ)) :
    (pullbackOnHomotopyCompIso (𝟙 Y) g).hom.app K =
      (mapHomotopyCategoryToId (modulePullback (𝟙 Y)) (modulePullbackId Y)).app
        (((modulePullback g).mapHomotopyCategory (ComplexShape.up ℤ)).obj K) := by
  refine Eq.trans (mapHomotopyCategoryCompIso_hom_app _ (ComplexShape.up ℤ) K) ?_
  refine Eq.trans ?_ (mapHomotopyCategoryToId_app_quotient (modulePullback (𝟙 Y))
    (modulePullbackId Y)
    (((modulePullback g).mapHomologicalComplex (ComplexShape.up ℤ)).obj K.as)).symm
  refine quotient_map_congr fun i => ?_
  simpa using NatTrans.congr_app (congrArg Iso.hom (modulePullbackComp_id_comp g)) (K.as.X i)

/-- **The right unit law on the unbounded homotopy categories.** -/
theorem pullbackOnHomotopyCompIso_comp_id (f : X ⟶ Y)
    (K : HomotopyCategory (ModuleSheaves Y) (ComplexShape.up ℤ)) :
    (pullbackOnHomotopyCompIso f (𝟙 Y)).hom.app K =
      ((modulePullback f).mapHomotopyCategory (ComplexShape.up ℤ)).map
        ((mapHomotopyCategoryToId (modulePullback (𝟙 Y)) (modulePullbackId Y)).app K) := by
  have hR : ((modulePullback f).mapHomotopyCategory (ComplexShape.up ℤ)).map
          ((mapHomotopyCategoryToId (modulePullback (𝟙 Y)) (modulePullbackId Y)).app K) =
      (HomotopyCategory.quotient (ModuleSheaves X) (ComplexShape.up ℤ)).map
        (((modulePullback f).mapHomologicalComplex (ComplexShape.up ℤ)).map
          ((NatTrans.mapHomologicalComplex (modulePullbackId Y).hom
              (ComplexShape.up ℤ)).app K.as ≫
            (Functor.mapHomologicalComplexIdIso (ModuleSheaves Y)
              (ComplexShape.up ℤ)).hom.app K.as)) :=
    CategoryTheory.Functor.congr_map ((modulePullback f).mapHomotopyCategory (ComplexShape.up ℤ))
      (mapHomotopyCategoryToId_app_quotient (modulePullback (𝟙 Y)) (modulePullbackId Y) K.as)
  rw [hR]
  refine Eq.trans (mapHomotopyCategoryCompIso_hom_app _ (ComplexShape.up ℤ) K) ?_
  refine quotient_map_congr fun i => ?_
  simpa using NatTrans.congr_app (congrArg Iso.hom (modulePullbackComp_comp_id f)) (K.as.X i)

end Degreewise

/-! ### Derived pullback along an identity morphism -/

section Identity

variable (X : RingedSpace.{u, u}) [HasDerivedCategory.{w₁} (ModuleSheaves X)]

omit [HasDerivedCategory (ModuleSheaves X)] in
/-- Degreewise pullback along the identity of a ringed space is left exact: it is isomorphic to
the identity functor. -/
theorem preservesFiniteLimits_modulePullback_id :
    PreservesFiniteLimits (modulePullback (𝟙 X)) :=
  preservesFiniteLimits_of_natIso (modulePullbackId X).symm

/-- **Derived pullback along the identity is the identity**, at an arbitrary model of the derived
category: this is the ringed-space form of `Stacks.Duality.derivedPullbackIdIso`, which
`derivedPullbackIdIso_eq` records it to be. -/
abbrev derivedPullbackIdIsoOfRingedSpace :
    derivedPullback (𝟙 X) ≅ 𝟭 (DerivedCategory (ModuleSheaves X)) :=
  haveI := preservesFiniteLimits_modulePullback_id X
  haveI := preservesFiniteColimits_modulePullback (𝟙 X)
  CategoryTheory.leftDerivedToIdIso (modulePullback (𝟙 X)) (modulePullbackId X)
    (derivedPullback (𝟙 X)) (derivedPullbackComparison (𝟙 X))

/-- **The factorization of `derivedPullbackIdIsoOfRingedSpace` against the comparison of the
derived pullback**: the comparison followed by the degreewise identification of `(𝟙 X)^*` with
the identity is `derivedPullbackIdIsoOfRingedSpace` on classes of complexes. -/
theorem derivedPullbackComparison_id_comp_map_mapHomotopyCategoryToId
    (M : HomotopyCategory (ModuleSheaves X) (ComplexShape.up ℤ)) :
    (derivedPullbackComparison (𝟙 X)).app M ≫
        DerivedCategory.Qh.map
          ((mapHomotopyCategoryToId (modulePullback (𝟙 X)) (modulePullbackId X)).app M) =
      (derivedPullbackIdIsoOfRingedSpace X).hom.app (DerivedCategory.Qh.obj M) := by
  have := preservesFiniteLimits_modulePullback_id X
  have := preservesFiniteColimits_modulePullback (𝟙 X)
  exact CategoryTheory.leftDerivedToIdIso_hom_app_Qh (modulePullback (𝟙 X))
    (modulePullbackId X) (derivedPullback (𝟙 X)) (derivedPullbackComparison (𝟙 X)) M

end Identity

/-! ### The two unit laws for the composition isomorphism of derived pullback, for ringed spaces -/

section Derived

variable {X Y Z : RingedSpace.{u, u}}
  [HasDerivedCategory.{w₁} (ModuleSheaves X)] [HasDerivedCategory.{w₂} (ModuleSheaves Y)]
  [HasDerivedCategory.{w₃} (ModuleSheaves Z)]

/-- **The left unit law for the composition isomorphism of derived pullback**, at an arbitrary
model of the derived categories: identifying `Lg^* ⋙ L(𝟙 Y)^*` with `L(𝟙 Y ≫ g)^*` is the
identification of `L(𝟙 Y)^*` with the identity functor, whiskered by `Lg^*`. This is the unit
coherence of [Stacks, Tag 0D5S]. -/
theorem derivedPullbackCompIsoCanonical_id_comp_anyModel (g : Y ⟶ Z) :
    derivedPullbackCompIsoCanonical (𝟙 Y) g =
      isoWhiskerLeft (derivedPullback g) (derivedPullbackIdIsoOfRingedSpace Y) ≪≫
        rightUnitor (derivedPullback g) := by
  refine Iso.ext (Functor.leftDerived_ext (LF := derivedPullback (𝟙 Y ≫ g))
    (α := derivedPullbackComparison (𝟙 Y ≫ g))
    (W := HomotopyCategory.quasiIso (ModuleSheaves Z) (ComplexShape.up ℤ)) _ _ _ ?_)
  ext K
  have hL : (derivedPullbackCompIsoCanonical (𝟙 Y) g).hom.app (DerivedCategory.Qh.obj K) ≫
        (derivedPullbackComparison (𝟙 Y ≫ g)).app K =
      (derivedPullback (𝟙 Y)).map ((derivedPullbackComparison g).app K) ≫
        (derivedPullbackComparison (𝟙 Y)).app
            (((modulePullback g).mapHomotopyCategory (ComplexShape.up ℤ)).obj K) ≫
          DerivedCategory.Qh.map ((pullbackOnHomotopyCompIso (𝟙 Y) g).hom.app K) :=
    Functor.leftDerived_fac_app _ _
      (HomotopyCategory.quasiIso (ModuleSheaves Z) (ComplexShape.up ℤ)) _ _ K
  have hfac : (derivedPullbackComparison (𝟙 Y)).app
          (((modulePullback g).mapHomotopyCategory (ComplexShape.up ℤ)).obj K) ≫
        DerivedCategory.Qh.map ((pullbackOnHomotopyCompIso (𝟙 Y) g).hom.app K) =
      (derivedPullbackIdIsoOfRingedSpace Y).hom.app
        (DerivedCategory.Qh.obj
          (((modulePullback g).mapHomotopyCategory (ComplexShape.up ℤ)).obj K)) := by
    rw [pullbackOnHomotopyCompIso_id_comp g K]
    exact derivedPullbackComparison_id_comp_map_mapHomotopyCategoryToId Y _
  refine Eq.trans ?_ (congrArg (fun z => z ≫ (derivedPullbackComparison g).app K)
    (Category.comp_id ((derivedPullbackIdIsoOfRingedSpace Y).hom.app
      ((derivedPullback g).obj (DerivedCategory.Qh.obj K))))).symm
  exact hL.trans (hfac ▸ (derivedPullbackIdIsoOfRingedSpace Y).hom.naturality _)

/-- **The right unit law for the composition isomorphism of derived pullback**, at an arbitrary
model of the derived categories: identifying `L(𝟙 Y)^* ⋙ Lf^*` with `L(f ≫ 𝟙 Y)^*` is the
identification of `L(𝟙 Y)^*` with the identity functor, whiskered by `Lf^*`. -/
theorem derivedPullbackCompIsoCanonical_comp_id_anyModel (f : X ⟶ Y) :
    derivedPullbackCompIsoCanonical f (𝟙 Y) =
      isoWhiskerRight (derivedPullbackIdIsoOfRingedSpace Y) (derivedPullback f) ≪≫
        leftUnitor (derivedPullback f) := by
  refine Iso.ext (Functor.leftDerived_ext (LF := derivedPullback (f ≫ 𝟙 Y))
    (α := derivedPullbackComparison (f ≫ 𝟙 Y))
    (W := HomotopyCategory.quasiIso (ModuleSheaves Y) (ComplexShape.up ℤ)) _ _ _ ?_)
  ext K
  have hL : (derivedPullbackCompIsoCanonical f (𝟙 Y)).hom.app (DerivedCategory.Qh.obj K) ≫
        (derivedPullbackComparison (f ≫ 𝟙 Y)).app K =
      (derivedPullback f).map ((derivedPullbackComparison (𝟙 Y)).app K) ≫
        (derivedPullbackComparison f).app
            (((modulePullback (𝟙 Y)).mapHomotopyCategory (ComplexShape.up ℤ)).obj K) ≫
          DerivedCategory.Qh.map ((pullbackOnHomotopyCompIso f (𝟙 Y)).hom.app K) :=
    Functor.leftDerived_fac_app _ _
      (HomotopyCategory.quasiIso (ModuleSheaves Y) (ComplexShape.up ℤ)) _ _ K
  have hfac : (derivedPullbackComparison f).app
          (((modulePullback (𝟙 Y)).mapHomotopyCategory (ComplexShape.up ℤ)).obj K) ≫
        DerivedCategory.Qh.map ((pullbackOnHomotopyCompIso f (𝟙 Y)).hom.app K) =
      (derivedPullback f).map
          (DerivedCategory.Qh.map
            ((mapHomotopyCategoryToId (modulePullback (𝟙 Y)) (modulePullbackId Y)).app K)) ≫
        (derivedPullbackComparison f).app K := by
    rw [pullbackOnHomotopyCompIso_comp_id f K]
    exact ((derivedPullbackComparison f).naturality _).symm
  have hmap : (derivedPullback f).map ((derivedPullbackComparison (𝟙 Y)).app K) ≫
        (derivedPullback f).map
          (DerivedCategory.Qh.map
            ((mapHomotopyCategoryToId (modulePullback (𝟙 Y)) (modulePullbackId Y)).app K)) =
      (derivedPullback f).map
        ((derivedPullbackIdIsoOfRingedSpace Y).hom.app (DerivedCategory.Qh.obj K)) :=
    Eq.trans ((derivedPullback f).map_comp _ _).symm
      (CategoryTheory.Functor.congr_map (derivedPullback f)
        (derivedPullbackComparison_id_comp_map_mapHomotopyCategoryToId Y K))
  refine Eq.trans ?_ (congrArg (fun z => z ≫ (derivedPullbackComparison f).app K)
    (Category.comp_id ((derivedPullback f).map
      ((derivedPullbackIdIsoOfRingedSpace Y).hom.app (DerivedCategory.Qh.obj K))))).symm
  exact hL.trans (hfac ▸ (Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) hmap))

end Derived

end Stacks.DerivedPullback.Composition

end
