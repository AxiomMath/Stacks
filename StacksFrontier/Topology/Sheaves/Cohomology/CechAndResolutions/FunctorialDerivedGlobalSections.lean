module

public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlusResolution
public import StacksFrontier.Topology.Sheaves.Cohomology.CechAndResolutions.DerivedGlobalSections
public import StacksFrontier.Topology.Sheaves.Cohomology.HigherDirectImage.DerivedSectionsOfAPushforward

/-!
# The map on derived global sections induced by an `f`-map

Let `f : X ⟶ Y` be a morphism of ringed spaces, let `F` be a sheaf of modules on `X`, let `G`
be a sheaf of modules on `Y`, and let `φ : f^* G ⟶ F` be an `f`-map. Restricting scalars along
`Γ(Y, 𝒪_Y) ⟶ Γ(X, 𝒪_X)` puts `RΓ(X, F)` and `RΓ(Y, G)` in the same bounded-below derived
category, and this file constructs the resulting morphism `RΓ(Y, G) ⟶ RΓ(X, F)`. It is obtained
by composing the derived global sections on `Y` of the adjoint `G ⟶ f_* F` of `φ`, read through
the unit of the derived pushforward, with the inverse of the comparison of [Stacks, Tag 01EZ].

## Main definitions

* `Stacks.Cohomology.derivedPushforwardSingleNatTrans`: the unit of the derived pushforward on
  complexes concentrated in degree zero, as a natural transformation in the coefficients.
* `Stacks.Cohomology.derivedModuleGlobalSectionsAlongIso`: the comparison identifying derived
  global sections over `X`, with scalars restricted to `Γ(Y, 𝒪_Y)`, with derived global
  sections over `Y` of the derived pushforward.
* `Stacks.Cohomology.derivedModuleGlobalSectionsMap`: the morphism
  `RΓ(Y, G) ⟶ RΓ(X, F)` attached to an `f`-map. This is the displayed arrow of
  [Stacks, Tag 01F9] and is its whole content, so it carries the tag by itself.

## Main results

* `Stacks.Cohomology.derivedModuleGlobalSectionsMap_naturality_source`: the morphism is
  natural in the sheaf of modules on the target.

## Implementation notes

The `f`-map is kept in its adjoint form `f^* G ⟶ F`, matching
`AlgebraicGeometry.RingedSpaceModuleAdjunction.homEquiv`, and the adjoint `G ⟶ f_* F` is read
off that bijection.

`Stacks.Cohomology.derivedModuleGlobalSectionsAlongIso` is the composite of the canonical
comparison of a right derived functor of a composite with the composite of the right derived
functors ([Stacks, Tag 015M], available because restriction of scalars is exact) and the
comparison of [Stacks, Tag 01EZ] at the open `⊤`. The two spellings of restriction of scalars
along `f` -- along `Γ(Y, 𝒪_Y) ⟶ Γ(X, 𝒪_X)` and along the component of `f^♯` at `⊤` -- agree
definitionally, as do sections over `⊤` and sections over `f⁻¹(⊤)`, so no transport is needed.

`HasDerivedCategory.standard` is a local instance, as in the files this one builds on.

## References

* [Stacks Project, Tag 01F9](https://stacks.math.columbia.edu/tag/01F9)
* [Stacks Project, Tag 01EZ](https://stacks.math.columbia.edu/tag/01EZ)
* [Stacks Project, Tag 015M](https://stacks.math.columbia.edu/tag/015M)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace Stacks.Cohomology

noncomputable section

attribute [local instance] HasDerivedCategory.standard

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)

/-- **The unit of the derived pushforward on complexes concentrated in degree zero**, as a
natural transformation in the coefficient sheaf of modules: it compares `(f_* F)[0]` with
`Rf_*(F[0])`. -/
noncomputable def derivedPushforwardSingleNatTrans [EnoughInjectives (Modules X)] :
    RingedSpaceModuleAdjunction.modulePushforward f ⋙
        DerivedCategory.Plus.singleFunctor (Modules Y) 0 ⟶
      DerivedCategory.Plus.singleFunctor (Modules X) 0 ⋙
        (RingedSpaceModuleAdjunction.modulePushforward f).rightDerivedFunctorPlus :=
  (RingedSpaceModuleAdjunction.modulePushforward f).mapSingleFunctorPlusCompQhIso.inv ≫
    Functor.whiskerLeft (HomotopyCategory.Plus.singleFunctor (Modules X) 0)
      (RingedSpaceModuleAdjunction.modulePushforward f).rightDerivedFunctorPlusUnith ≫
    Functor.whiskerRight (DerivedCategory.Plus.singleFunctorIsoCompQh (Modules X) 0).inv
      (RingedSpaceModuleAdjunction.modulePushforward f).rightDerivedFunctorPlus

variable [EnoughInjectives (Modules X)] [EnoughInjectives (Modules Y)]
  [HasSheafify (Opens.grothendieckTopology (X : TopCat)) AddCommGrpCat]
  [(Opens.grothendieckTopology (X : TopCat)).WEqualsLocallyBijective AddCommGrpCat]
  [HasSheafify (Opens.grothendieckTopology (Y : TopCat)) AddCommGrpCat]
  [(Opens.grothendieckTopology (Y : TopCat)).WEqualsLocallyBijective AddCommGrpCat]

/-- **The canonical derived-sections comparison**: derived global sections on `X`, with scalars
restricted to `Γ(Y, 𝒪_Y)`, agree with derived global sections on `Y` of the derived
pushforward. This is [Stacks, Tag 01EZ] at the open `⊤`, preceded by the canonical comparison
of the right derived functor of a composite with the composite of the right derived
functors. -/
noncomputable def derivedModuleGlobalSectionsAlongIso :
    derivedModuleGlobalSectionsAlong f ≅
      (RingedSpaceModuleAdjunction.modulePushforward f).rightDerivedFunctorPlus ⋙
        derivedModuleGlobalSections Y :=
  DerivedPushforwardSections.compIso (moduleGlobalSections X) (restrictGlobalScalars f)
      (fun _ _ => DerivedPushforwardSections.rightAcyclic_restrictScalars _ _) ≪≫
    DerivedPushforwardSections.rightDerivedSectionsRestrictionIso f ⊤

/-- **[Stacks, Tag 01F9].** An `f`-map `f^* G ⟶ F` induces the functorial morphism
`RΓ(Y, G) ⟶ RΓ(X, F)`, where the target is regarded as a complex of `Γ(Y, 𝒪_Y)`-modules by
restriction of scalars. It is the displayed arrow of the tag: the derived global sections on
`Y` of the morphism `G ⟶ Rf_* F` of [Stacks, Tag 01F8], followed by the inverse of the
comparison `RΓ(X, F) ≅ RΓ(Y, Rf_* F)` of [Stacks, Tag 01EZ]. -/
noncomputable def derivedModuleGlobalSectionsMap {G : Modules Y} {F : Modules X}
    (φ : (RingedSpaceModuleAdjunction.modulePullback f).obj G ⟶ F) :
    (derivedModuleGlobalSections Y).obj
        ((DerivedCategory.Plus.singleFunctor (Modules Y) 0).obj G) ⟶
      (derivedModuleGlobalSectionsAlong f).obj
        ((DerivedCategory.Plus.singleFunctor (Modules X) 0).obj F) :=
  (derivedModuleGlobalSections Y).map
      ((DerivedCategory.Plus.singleFunctor (Modules Y) 0).map
          (RingedSpaceModuleAdjunction.homEquiv f F G φ) ≫
        (derivedPushforwardSingleNatTrans f).app F) ≫
    (derivedModuleGlobalSectionsAlongIso f).inv.app _

/-- **The map on derived global sections is natural in the sheaf of modules on the target.** -/
theorem derivedModuleGlobalSectionsMap_naturality_source {G G' : Modules Y} {F : Modules X}
    (φ : (RingedSpaceModuleAdjunction.modulePullback f).obj G ⟶ F) (v : G' ⟶ G) :
    derivedModuleGlobalSectionsMap f
        ((RingedSpaceModuleAdjunction.modulePullback f).map v ≫ φ) =
      (derivedModuleGlobalSections Y).map
          ((DerivedCategory.Plus.singleFunctor (Modules Y) 0).map v) ≫
        derivedModuleGlobalSectionsMap f φ := by
  have hψ : (RingedSpaceModuleAdjunction.homEquiv f F G')
        ((RingedSpaceModuleAdjunction.modulePullback f).map v ≫ φ) =
      v ≫ (RingedSpaceModuleAdjunction.homEquiv f F G) φ :=
    (RingedSpaceModuleAdjunction.modulePullbackPushforwardAdjunction f).homEquiv_naturality_left
      v φ
  have e1 : (DerivedCategory.Plus.singleFunctor (Modules Y) 0).map
        (v ≫ (RingedSpaceModuleAdjunction.homEquiv f F G) φ) =
      (DerivedCategory.Plus.singleFunctor (Modules Y) 0).map v ≫
        (DerivedCategory.Plus.singleFunctor (Modules Y) 0).map
          ((RingedSpaceModuleAdjunction.homEquiv f F G) φ) :=
    (DerivedCategory.Plus.singleFunctor (Modules Y) 0).map_comp _ _
  dsimp only [derivedModuleGlobalSectionsMap]
  rw [hψ, e1]
  simp only [Functor.map_comp, Category.assoc]

end

end Stacks.Cohomology

end
