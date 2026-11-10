module

public import StacksFrontier.Algebra.Homology.DerivedCategory.ExactIdentityComparison
public import StacksFrontier.Homology.DerivedIndexing.Composite
public import StacksFrontier.Topology.Sheaves.Cohomology.HigherDirectImage.AbelianBaseChangeMapFunctoriality
public import StacksFrontier.Topology.Sheaves.Cohomology.HigherDirectImage.FunctorialityOfCohomology

/-!
# The identity law for the map on cohomology along a morphism of ringed spaces

Let `f : (X, 𝒪_X) ⟶ (Y, 𝒪_Y)` be a morphism of ringed spaces. An `f`-map `φ : 𝒢 ⟶ f_* ℱ`
induces `RΓ(Y, 𝒢) ⟶ RΓ(X, ℱ)` of [Stacks, Tag 01F9] and `H^i(Y, 𝒢) ⟶ H^i(X, ℱ)` of
[Stacks, Tag 01FA]. Both are functorial in the two *module* arguments, which is
`StacksFrontier.Topology.Sheaves.Cohomology.HigherDirectImage.FunctorialityOfCohomology`. The law in
the *morphism* argument is not available, and an obstruction theory needs it: `map_id` of
[Stacks, Tag 07YG] says that the map of obstruction modules along an identity morphism is the
identity, and for the example of [Stacks, Tag 07YH] that map is assembled from the Tag 01FA map.

The arrow of Tag 01F9 is built from two factors. This file proves that **each of them degenerates
at the identity, to the canonical comparison `R𝟭 ≅ 𝟭`**, which is what makes them cancel; both
statements are about an arbitrary abelian category with enough injectives, and
`(𝟙_X)_* = 𝟭` holds on the nose for sheaves of modules on a ringed space
(`RingedSpaceModuleAdjunction.modulePushforwardId`).

## Main results

* `Stacks.Cohomology.moduleCohomologyMap_id`: **the identity law for the map on cohomology of
  [Stacks, Tag 01FA]**, `H^i(𝟙_X, φ) = H^i(X, φ)`, and
  `Stacks.Cohomology.derivedGlobalSectionsMap_id`, the same for the arrow of [Stacks, Tag 01F9].

The two factors of Tag 01F9 degenerate separately, each statement being about an arbitrary
abelian category with enough injectives:

* `Stacks.Cohomology.singleRightDerivedUnit_id_app`: the morphism `M[0] ⟶ R𝟭(M[0])` that
  [Stacks, Tag 01F8] attaches to the identity `f`-map of the identity functor is the canonical
  comparison `CategoryTheory.Functor.rightDerivedFunctorPlusIdIsoOf`, inverted.
* `Stacks.Cohomology.DerivedPushforwardSections.compComparison_id`: the canonical comparison
  `R(G ∘ 𝟭) ⟶ RG ∘ R𝟭` of [Stacks, Tag 05T2] is `RG` applied to that same comparison. For
  `G = Γ(X, -)` this is the identification `RΓ(X, R(𝟙_X)_*(-)) ≅ RΓ(X, -)` of
  [Stacks, Tag 01EZ] at an identity morphism.
* `Stacks.Cohomology.DerivedPushforwardSections.map_singleRightDerivedUnit_comp_compIso_inv`:
  the two combined, in the form the specialization consumes — `RG` of the first cancels the
  second.

The four coherence identities they rest on, each stating that a comparison which the development
only has abstractly is an identity for the identity functor:

* `CategoryTheory.Functor.mapHomotopyCategoryPlusIdIsoOf_refl_inv_app` and
  `CategoryTheory.Functor.singleMapHomologicalComplex_id_inv_app`, degreewise;
* `CategoryTheory.Functor.mapSingleFunctorCompQhIso_id_app_inv`: for the identity functor the
  identification of `Qh(𝟭(M[0]))` with `(𝟭 M)[0]` is
  `CategoryTheory.Functor.singleFunctorPlusIsoCompQh`;
* `CategoryTheory.Functor.rightDerivedFunctorPlusIdIsoOf_refl_inv_app_Qh`: on the image of the
  localization the comparison `R𝟭 ≅ 𝟭` is the derived-functor unit.

## Implementation notes

`compComparison_id` is proved by the uniqueness of a descent along the unit of a right derived
functor, `CategoryTheory.Functor.rightDerived_ext`: both sides satisfy the factorization
`CategoryTheory.Functor.rightDerivedFunctorPlusComp_fac` that pins the canonical
comparison, the comparison side by definition and the other side by the naturality of the unit of
`RG` along the degreewise identity comparison.

`singleRightDerivedUnit_id_app` is the naturality of
`CategoryTheory.Functor.rightDerivedFunctorPlusIdIsoOf` along
`CategoryTheory.Functor.singleFunctorPlusIsoCompQh`, once the two coherence isomorphisms that
`Stacks.Cohomology.singleRightDerivedUnit` is built from are identified. The only non-formal step
in the second of them is `HomologicalComplex.singleMapHomologicalComplex`, and for the identity
functor that is the identity.

Several components below are *definitionally* identity morphisms between objects that are
definitionally but not syntactically equal, so they cannot be rewritten to `𝟙` inside a larger
composite: substituting `𝟙` forces the two ends of the surrounding composite to be the same
object and the ambient term stops being type-correct. The proofs therefore either state those
steps as cancellations, as
`CategoryTheory.Functor.mapHomotopyCategoryPlusCompIso_refl_inv_comp` does, or discharge them in
term mode, where the elaborator may use the full definitional unfolding.

## How the specialization to `f = 𝟙 X` is made

`(𝟙_X)_*` is the identity functor on the nose, and so are the composites and cohomology functors
built from it; those checks are cheap. What is *not* cheap is recognising
`Stacks.Cohomology.singleRightDerivedUnit (modulePushforward (𝟙 X))` as
`Stacks.Cohomology.singleRightDerivedUnit (𝟭 (Modules X))`: that exhausts the heartbeat budget in
`isDefEq`, the single culprit being
`CategoryTheory.Functor.mapSingleFunctorCompQhIso`, which is built by
`CategoryTheory.Functor.fullyFaithfulCancelRight` and so by a `Full`-preimage. The derived
functor, its unit and `mapHomotopyCategoryPlus` all compare cheaply in the two spellings.

`map_singleRightDerivedUnit_comp_compIso_inv` therefore carries the functor as a *variable* with
an equality hypothesis and discharges it by `subst`. Instantiating it at
`Φ := modulePushforward (𝟙 X)` with `hΦ := rfl` then costs only the equality of the two functors.
Its derived-category and additivity instances are passed by name at the point of use, so that
they are the ones `Stacks.Cohomology.derivedGlobalSectionsComparison` was elaborated with rather
than ones synthesized afresh here; and the unfolding of
`Stacks.Cohomology.derivedGlobalSectionsMap` is done on the other side of the import, by
`Stacks.Cohomology.derivedGlobalSectionsMap_id_of_cancel`.

## References

* [Stacks Project, Tag 01FA](https://stacks.math.columbia.edu/tag/01FA)
* [Stacks Project, Tag 01F9](https://stacks.math.columbia.edu/tag/01F9)
* [Stacks Project, Tag 01F8](https://stacks.math.columbia.edu/tag/01F8)
* [Stacks Project, Tag 01EZ](https://stacks.math.columbia.edu/tag/01EZ)
* [Stacks Project, Tag 05T2](https://stacks.math.columbia.edu/tag/05T2)
* [Stacks Project, Tag 07YG](https://stacks.math.columbia.edu/tag/07YG)
* [Stacks Project, Tag 07YH](https://stacks.math.columbia.edu/tag/07YH)
-/
@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe w v u u₂ v₂

/-! ### The degreewise comparisons at the identity functor -/

namespace CategoryTheory.Functor

attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

section Degreewise

variable {A : Type u} [Category.{v} A] [Abelian A]

/-- **The degreewise identity comparison of the identity functor has identity components.** It is
`Stacks.Cohomology.BaseChange.mapPlus` of `𝟙`. -/
theorem mapHomotopyCategoryPlusIdIsoOf_refl_inv_app (K : HomotopyCategory.Plus A) :
    (mapHomotopyCategoryPlusIdIsoOf (𝟭 A) (Iso.refl (𝟭 A))).inv.app K = 𝟙 _ := by
  rw [mapHomotopyCategoryPlusIdIsoOf_inv_app, Iso.refl_inv,
    Stacks.Cohomology.BaseChange.mapPlus_id]
  rfl

/-- **The identity functor does not move the complex `M[0]`.** The comparison
`HomologicalComplex.singleMapHomologicalComplex` of `M[0]` with `(𝟭 M)[0]` is the identity: in
degree `0` both of its components are the identity of `M`, and in every other degree the source
is a zero object. -/
theorem singleMapHomologicalComplex_id_inv_app (M : A) :
    (HomologicalComplex.singleMapHomologicalComplex (𝟭 A) (ComplexShape.up ℤ) 0).inv.app M =
      𝟙 _ := by
  ext i
  by_cases h : i = 0
  · subst h
    simp [HomologicalComplex.singleMapHomologicalComplex, NatIso.ofComponents]
  · exact (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 M i h).eq_of_src _ _

end Degreewise

section SingleFunctor

variable {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]

/-- The forward half of `Stacks.DerivedIndexing.ι_map_singleFunctorPlusIsoCompQh_inv_app`: the
components of `CategoryTheory.Functor.singleFunctorPlusIsoCompQh` are the `Plus.ι`-preimages of
those of `DerivedCategory.singleFunctorIsoCompQh` in the forward direction too. -/
theorem ι_map_singleFunctorPlusIsoCompQh_hom_app (M : A) :
    DerivedCategory.Plus.ι.map ((singleFunctorPlusIsoCompQh (A := A) 0).hom.app M) =
      (DerivedCategory.singleFunctorIsoCompQh A 0).hom.app M := by
  have h1 : DerivedCategory.Plus.ι.map ((singleFunctorPlusIsoCompQh (A := A) 0).inv.app M) =
      (DerivedCategory.singleFunctorIsoCompQh A 0).inv.app M :=
    Stacks.DerivedIndexing.ι_map_singleFunctorPlusIsoCompQh_inv_app M
  have h2 : (singleFunctorPlusIsoCompQh (A := A) 0).hom.app M ≫
      (singleFunctorPlusIsoCompQh (A := A) 0).inv.app M = 𝟙 _ := by
    rw [← NatTrans.comp_app, Iso.hom_inv_id, NatTrans.id_app]
  have h3 := congrArg DerivedCategory.Plus.ι.map h2
  rw [Functor.map_comp, h1, CategoryTheory.Functor.map_id] at h3
  exact ((Iso.comp_inv_eq ((DerivedCategory.singleFunctorIsoCompQh A 0).app M)).1 h3).trans
    (Category.id_comp _)

variable [EnoughInjectives A]

omit [EnoughInjectives A] in
/-- **For the identity functor the two coherence isomorphisms agree.** The identification of
`Qh(𝟭(M[0]))` with `(𝟭 M)[0]` is the identification of `M[0]` in `D⁺(𝒜)` with `Qh(M[0])`: the
only non-formal step in `CategoryTheory.Functor.mapSingleFunctorCompQhIso`, the comparison
`HomologicalComplex.singleMapHomologicalComplex`, is the identity for `𝟭`. -/
theorem mapSingleFunctorCompQhIso_id_app_inv (M : A) :
    ((mapSingleFunctorCompQhIso (𝟭 A)).app M).inv =
      (singleFunctorPlusIsoCompQh (A := A) 0).hom.app M :=
  have e1 : DerivedCategory.Qh.map ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).map
        ((HomologicalComplex.singleMapHomologicalComplex (𝟭 A) (ComplexShape.up ℤ) 0).inv.app M))
      = 𝟙 _ :=
    (congrArg (fun t => DerivedCategory.Qh.map
        ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).map t))
      (singleMapHomologicalComplex_id_inv_app M)).trans
      ((congrArg DerivedCategory.Qh.map (CategoryTheory.Functor.map_id
            (HomotopyCategory.quotient A (ComplexShape.up ℤ)) _)).trans
        (CategoryTheory.Functor.map_id DerivedCategory.Qh _))
  DerivedCategory.Plus.ι.map_injective
    ((Stacks.DerivedIndexing.ι_map_mapSingleFunctorCompQhIso_inv_app (𝟭 A) M).trans
      ((congrArg (fun t =>
            (DerivedCategory.singleFunctorIsoCompQh A 0).hom.app ((𝟭 A).obj M) ≫ t) e1).trans
        ((Category.comp_id _).trans (ι_map_singleFunctorPlusIsoCompQh_hom_app M).symm)))

/-- **The comparison `R𝟭 ≅ 𝟭` on the image of the localization is the derived-functor unit.**
This is `CategoryTheory.Functor.rightDerivedFunctorPlusIdIsoOf_inv_app` with the degreewise
comparison, which is an identity, cancelled. -/
theorem rightDerivedFunctorPlusIdIsoOf_refl_inv_app_Qh (K : HomotopyCategory.Plus A) :
    (rightDerivedFunctorPlusIdIsoOf (𝟭 A) (Iso.refl (𝟭 A))).inv.app
        (DerivedCategory.Plus.Qh.obj K) =
      (𝟭 A).rightDerivedFunctorPlusUnith.app K :=
  (rightDerivedFunctorPlusIdIsoOf_inv_app (𝟭 A) (Iso.refl (𝟭 A)) K).trans
    ((congrArg (fun t => DerivedCategory.Plus.Qh.map t ≫
          (𝟭 A).rightDerivedFunctorPlusUnith.app K)
        (mapHomotopyCategoryPlusIdIsoOf_refl_inv_app K)).trans
      ((congrArg (fun t => t ≫ (𝟭 A).rightDerivedFunctorPlusUnith.app K)
          (DerivedCategory.Plus.Qh.map_id _)).trans (Category.id_comp _)))

end SingleFunctor

end CategoryTheory.Functor

/-! ### The two factors of Stacks 01F9 at an identity -/

namespace Stacks.Cohomology

attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

section Abstract

variable {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
  [EnoughInjectives A]

/-- **Stacks 01F8 for the identity functor.** The canonical map `M[0] ⟶ R𝟭(M[0])` attached to
the identity functor is the canonical comparison `R𝟭 ≅ 𝟭` of
`CategoryTheory.Functor.rightDerivedFunctorPlusIdIsoOf`, inverted, read at `M[0]`.

So the first factor of the arrow of [Stacks, Tag 01F9] degenerates at the identity: it is
invertible there, with the canonical inverse, and not merely isomorphic to such a map. -/
theorem singleRightDerivedUnit_id_app (M : A) :
    (singleRightDerivedUnit (𝟭 A)).app M =
      (Functor.rightDerivedFunctorPlusIdIsoOf (𝟭 A) (Iso.refl (𝟭 A))).inv.app
        ((DerivedCategory.Plus.singleFunctor A 0).obj M) := by
  have hnat : (Functor.singleFunctorPlusIsoCompQh (A := A) 0).hom.app M ≫
        (𝟭 A).rightDerivedFunctorPlusUnith.app ((HomotopyCategory.Plus.singleFunctor A 0).obj M) =
      (Functor.rightDerivedFunctorPlusIdIsoOf (𝟭 A) (Iso.refl (𝟭 A))).inv.app
          ((DerivedCategory.Plus.singleFunctor A 0).obj M) ≫
        (𝟭 A).rightDerivedFunctorPlus.map
          ((Functor.singleFunctorPlusIsoCompQh (A := A) 0).hom.app M) :=
    Functor.rightDerivedFunctorPlusIdIsoOf_refl_inv_app_Qh
        ((HomotopyCategory.Plus.singleFunctor A 0).obj M) ▸
      ((Functor.rightDerivedFunctorPlusIdIsoOf (𝟭 A) (Iso.refl (𝟭 A))).inv.naturality
        ((Functor.singleFunctorPlusIsoCompQh (A := A) 0).hom.app M))
  rw [singleRightDerivedUnit_app, Functor.mapSingleFunctorCompQhIso_id_app_inv]
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine Eq.trans (congrArg (fun t => t ≫ (𝟭 A).rightDerivedFunctorPlus.map
      ((Functor.singleFunctorPlusIsoCompQh (A := A) 0).inv.app M)) hnat) ?_
  refine Eq.trans (Category.assoc _ _ _) ?_
  refine Eq.trans (congrArg (fun t =>
      (Functor.rightDerivedFunctorPlusIdIsoOf (𝟭 A) (Iso.refl (𝟭 A))).inv.app
        ((DerivedCategory.Plus.singleFunctor A 0).obj M) ≫ t)
    ((𝟭 A).rightDerivedFunctorPlus.mapIso
      ((Functor.singleFunctorPlusIsoCompQh (A := A) 0).app M)).hom_inv_id) ?_
  exact Category.comp_id _

namespace DerivedPushforwardSections

variable {C : Type*} [Category* C] [Abelian C] [HasDerivedCategory C] (G : A ⥤ C) [G.Additive]

/-- **Stacks 05T2 at the identity first factor.** The canonical comparison
`R(G ∘ 𝟭) ⟶ RG ∘ R𝟭` is `RG` applied to the canonical comparison `𝟭 ⟶ R𝟭`.

For `G = Γ(X, -)` this is the identification `RΓ(X, R𝟭(-)) ≅ RΓ(X, -)` of [Stacks, Tag 01EZ] at
an identity morphism of ringed spaces, which is one of the two factors of the arrow of
[Stacks, Tag 01F9]. -/
theorem compComparison_id :
    Functor.rightDerivedFunctorPlusComp (𝟭 A) G =
      Functor.whiskerRight
        (Functor.rightDerivedFunctorPlusIdIsoOf (𝟭 A) (Iso.refl (𝟭 A))).inv
        G.rightDerivedFunctorPlus := by
  refine Functor.rightDerived_ext ((𝟭 A ⋙ G).rightDerivedFunctorPlus)
    (𝟭 A ⋙ G).rightDerivedFunctorPlusUnith (HomotopyCategory.Plus.quasiIso A) _ _ _ ?_
  rw [Functor.rightDerivedFunctorPlusComp_fac]
  refine NatTrans.ext (funext fun K => ?_)
  have hnat : DerivedCategory.Plus.Qh.map (G.mapHomotopyCategoryPlus.map
          ((Functor.mapHomotopyCategoryPlusIdIsoOf (𝟭 A) (Iso.refl (𝟭 A))).inv.app K)) ≫
        G.rightDerivedFunctorPlusUnith.app ((𝟭 A).mapHomotopyCategoryPlus.obj K) =
      G.rightDerivedFunctorPlusUnith.app K ≫
        G.rightDerivedFunctorPlus.map (DerivedCategory.Plus.Qh.map
          ((Functor.mapHomotopyCategoryPlusIdIsoOf (𝟭 A) (Iso.refl (𝟭 A))).inv.app K)) :=
    G.rightDerivedFunctorPlusUnith.naturality _
  have hkey : (Functor.mapHomotopyCategoryPlusCompIso (Iso.refl ((𝟭 A) ⋙ G))).inv.app K =
      G.mapHomotopyCategoryPlus.map
        ((Functor.mapHomotopyCategoryPlusIdIsoOf (𝟭 A) (Iso.refl (𝟭 A))).inv.app K) :=
    Eq.trans (show _ = 𝟙 _ from rfl)
      (Eq.symm (Eq.trans (congrArg G.mapHomotopyCategoryPlus.map
          (Functor.mapHomotopyCategoryPlusIdIsoOf_refl_inv_app K))
        (G.mapHomotopyCategoryPlus.map_id _)))
  change DerivedCategory.Plus.Qh.map ((Functor.mapHomotopyCategoryPlusCompIso
          (Iso.refl ((𝟭 A) ⋙ G))).inv.app K) ≫
        G.rightDerivedFunctorPlusUnith.app ((𝟭 A).mapHomotopyCategoryPlus.obj K) ≫
          G.rightDerivedFunctorPlus.map ((𝟭 A).rightDerivedFunctorPlusUnith.app K) =
      G.rightDerivedFunctorPlusUnith.app K ≫
        G.rightDerivedFunctorPlus.map
          ((Functor.rightDerivedFunctorPlusIdIsoOf (𝟭 A) (Iso.refl (𝟭 A))).inv.app
            (DerivedCategory.Plus.Qh.obj K))
  rw [Functor.rightDerivedFunctorPlusIdIsoOf_inv_app, Functor.map_comp]
  conv_rhs => rw [← Category.assoc, ← hnat]
  rw [← Category.assoc, ← hkey]

/-- The two objects that the identity law compares. For a functor equal to the identity,
`RG(M[0])` taken at `Φ M` and `R(G ∘ Φ)(M[0])` are the same object; the law below is an equation
between morphisms with those as source and target. -/
theorem rightDerivedObj_eq_of_eq_id {A : Type u} [Category.{v} A] {C : Type u₂}
    [Category.{v₂} C] (Φ : A ⥤ A) (G : A ⥤ C) [Abelian A]
    [instA : HasDerivedCategory.{max u v} A] [EnoughInjectives A] [Abelian C]
    [instC : HasDerivedCategory.{max u₂ v₂} C] [instΦ : Φ.Additive] [instG : G.Additive]
    (hΦ : Φ = 𝟭 A) (M : A) :
    G.rightDerivedFunctorPlus.obj
        ((DerivedCategory.Plus.singleFunctor A 0).obj (Φ.obj M)) =
      (Φ ⋙ G).rightDerivedFunctorPlus.obj
        ((DerivedCategory.Plus.singleFunctor A 0).obj M) := by
  subst hΦ
  rfl

/-- **The identity law for the two factors of [Stacks, Tag 01F9], combined.** For a functor `Φ`
*equal* to the identity, `RG` of the morphism of [Stacks, Tag 01F8] cancels against the
comparison of [Stacks, Tag 015M]:
```
RG(M[0] ⟶ RΦ(M[0])) ≫ (R(G ∘ Φ) ≅ RΦ ⋙ RG)⁻¹ = 𝟙.
```

The functor is carried as a variable with an equality hypothesis rather than written as `𝟭`
outright. That is what makes the statement usable: `(𝟙_X)_*` is the identity functor on the nose,
but recognising `Stacks.Cohomology.singleRightDerivedUnit (modulePushforward (𝟙 X))` as
`Stacks.Cohomology.singleRightDerivedUnit (𝟭 (Modules X))` exhausts the heartbeat budget in
`isDefEq`, whereas instantiating `Φ := modulePushforward (𝟙 X)` and `hΦ := rfl` costs only the
equality of the two functors, which is cheap. The `eqToHom` on the right is `𝟙` whenever the two
objects of `rightDerivedObj_eq_of_eq_id` are cheaply definitionally equal, which is the case for
a ringed space. -/
theorem map_singleRightDerivedUnit_comp_compIso_inv {A : Type u} [Category.{v} A]
    {C : Type u₂} [Category.{v₂} C] (Φ : A ⥤ A) (G : A ⥤ C) [Abelian A]
    [instA : HasDerivedCategory.{max u v} A] [EnoughInjectives A] [Abelian C]
    [instC : HasDerivedCategory.{max u₂ v₂} C] [instΦ : Φ.Additive] [instG : G.Additive]
    (hΦ : Φ = 𝟭 A)
    (hFG : ∀ I : A, Injective I → G.rightAcyclic (Φ.obj I)) (M : A) :
    G.rightDerivedFunctorPlus.map ((singleRightDerivedUnit Φ).app M) ≫
        (compIso Φ G hFG).inv.app ((DerivedCategory.Plus.singleFunctor A 0).obj M) =
      eqToHom (rightDerivedObj_eq_of_eq_id Φ G hΦ M) := by
  subst hΦ
  have h1 : (compIso (𝟭 A) G hFG).hom.app
        ((DerivedCategory.Plus.singleFunctor A 0).obj M) =
      G.rightDerivedFunctorPlus.map ((singleRightDerivedUnit (𝟭 A)).app M) := by
    rw [compIso_hom, compComparison_id]
    exact congrArg (fun t => G.rightDerivedFunctorPlus.map t)
      (singleRightDerivedUnit_id_app M).symm
  rw [← h1]
  exact ((compIso (𝟭 A) G hFG).hom_inv_id_app _).trans (eqToHom_refl _ _).symm

end DerivedPushforwardSections

end Abstract

/-! ### The identity law for Stacks 01F9 and Stacks 01FA -/

section RingedSpace

open RingedSpaceModuleAdjunction
open Stacks.Cohomology.DerivedPushforwardSections

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] abelianModules enoughInjectivesModules
  Stacks.Cohomology.DerivedDirectImageComposition.pushforward_additive additiveEvaluation

variable (X : RingedSpace.{u, u})

/-- **The arrow of [Stacks, Tag 01F9] along an identity morphism.** For `f = 𝟙 X` an `f`-map is a
morphism `φ : 𝒢 ⟶ ℱ` of `𝒪_X`-modules, and the induced arrow `RΓ(X, 𝒢) ⟶ RΓ(X, ℱ)` is `RΓ(X, -)`
applied to `φ[0]`: both factors of the arrow degenerate, by
`Stacks.Cohomology.DerivedPushforwardSections.map_singleRightDerivedUnit_comp_compIso_inv`, and
cancel. -/
theorem derivedGlobalSectionsMap_id {G F : Modules X} (phi : G ⟶ F) :
    derivedGlobalSectionsMap (𝟙 X) phi =
      (derivedModuleGlobalSections X).map
        ((DerivedCategory.Plus.singleFunctor (Modules X) 0).map phi) := by
  refine derivedGlobalSectionsMap_id_of_cancel phi ?_
  exact map_singleRightDerivedUnit_comp_compIso_inv (modulePushforward (𝟙 X))
    (moduleGlobalSections X) (instA := HasDerivedCategory.standard _)
    (instC := HasDerivedCategory.standard _)
    (instΦ := Stacks.Cohomology.DerivedDirectImageComposition.pushforward_additive (𝟙 X))
    (instG := moduleGlobalSections_additive X) rfl
    (rightAcyclic_modulePushforward_obj (𝟙 X) ⊤) F

/-- **The identity law for the map on cohomology of [Stacks, Tag 01FA].** The map
`H^i(Y, 𝒢) ⟶ H^i(X, ℱ)` attached to an `f`-map, taken at `f = 𝟙 X`, is `H^i(X, φ)`.

This is the law that `map_id` of an obstruction theory ([Stacks, Tag 07YG], clause (2),
condition (i)) rests on where the map of obstruction modules is built from the Tag 01FA map, as
it is for the example of [Stacks, Tag 07YH]. -/
theorem moduleCohomologyMap_id (i : ℤ) {G F : Modules X} (phi : G ⟶ F) :
    moduleCohomologyMap (𝟙 X) i phi = (spaceModuleCohomology X i).map phi := by
  change (DerivedCategory.Plus.homologyFunctor
      (ModuleCat ((ringCatSheaf X).obj.obj (op ⊤))) i).map
        (derivedGlobalSectionsMap (𝟙 X) phi) = _
  rw [derivedGlobalSectionsMap_id]
  rfl

end RingedSpace

end Stacks.Cohomology

end
