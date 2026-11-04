module

public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.AdjunctionAlongAComposite
import StacksCore.Tactic.StacksAttribute

/-!
# The composition formula for derived pushforward, with nothing left over

Let `f : (X, 𝒪_X) ⟶ (Y, 𝒪_Y)` and `g : (Y, 𝒪_Y) ⟶ (Z, 𝒪_Z)` be morphisms of ringed spaces.
`StacksDraft.Ch20.Sec28Composition.Tag0D5T` builds the canonical comparison

`R(f ≫ g)_* ⟶ Rf_* ⋙ Rg_*`

from the universal property of the right derived functor along `f ≫ g`, and proves it invertible
exactly when `Stacks.Cohomology.DerivedPushforwardComposition.PushforwardComputesDerived` holds.
`StacksDraft.Ch20.Sec28.Tag079WComposition` builds a *second* isomorphism between the same pair of
functors, `Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforwardCompIso`, from
  uniqueness of right adjoints, and carries
no hypothesis — but it is not the same map by construction, and the two are characterized by
different factorizations.

This file identifies them, and so proves Tag 0D5T with no hypothesis beyond the two morphisms.

## Main results

* `derivedPushforwardCompUnit_comp_derivedPushforwardCompIso`: the comparison from
  degreewise pushforward along `f ≫ g`, followed by
    `Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforwardCompIso`, is
  the canonical comparison of `R(f ≫ g)_*`.  This is the identification of the two isomorphisms.
* `quasiIso_mapHomotopyCategory_pushforward_of_isKInjective`: degreewise `g_*`
  carries a K-injective resolution of `f_* I` to a quasi-isomorphism, for `I` K-injective.  This
  is the content of the composition formula in a form that mentions no derived category, and it is
  what carries the result across the choices of derived category.
* `Stacks.Cohomology.DerivedPushforwardComposition.pushforwardComputesDerived`:
  `PushforwardComputesDerived` holds unconditionally.
* `isIso_derivedPushforwardComparison_unconditional`: **Stacks 0D5T**, for arbitrary
  presentations of the three derived pushforwards.

## Implementation notes

*The shape of the argument.*
  `Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforwardCompIso` is the uniqueness
isomorphism of right adjoints of `L(f ≫ g)^*`, so the only handle on it is the coherence of the
three derived adjunctions with it,
  `Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedAdjunction_comp_homEquiv`.  Transposing
the desired equation twice under `Lg^* ⊣ Rg_*` and `Lf^* ⊣ Rf_*` turns it into an equation between
maps out of `Lf^*(Lg^*(Q((f ≫ g)_* K)))`, where both sides are built from the *counits*: the
compatibility of each derived counit with the degreewise one
(`Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedAdjunction_counit_fac`), the
  factorization of the derived pullback
composition isomorphism through the degreewise one (Tag 0D5S), and finally a single identity on the
homotopy categories.  That identity is induced degreewise from the defining property of
`CategoryTheory.Adjunction.leftAdjointCompIso`, which is exactly how
`Stacks.DerivedPullback.Composition.modulePullbackComp` was defined, so the mates lemma
`CategoryTheory.conjugateEquiv_counit_symm` closes it.

*Why the chase is carried out abstractly.*  `compUnit_comp_compIso_of_adjunctions` states the
transposition argument for arbitrary categories, functors and adjunctions.  Run directly
on the ringed-space functors, a single `rw` of counit naturality exhausts the heartbeat budget on
the `isDefEq` check, because `derivedPushforward` and `derivedPullback` are reducible abbreviations
of total derived functors and `kabstract` unfolds them.  At the abstract statement every term is
small and the same chase is immediate.

*Crossing the choices of derived category.*  Every statement below that mentions
`Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforward` is relative to
  `HasDerivedCategory.standard`, because that is
what Tags 079W and 0D5S fix.  The passage to an arbitrary `HasDerivedCategory` instance is made
through `quasiIso_mapHomotopyCategory_pushforward_of_isKInjective`, which mentions no derived
category at all: by `isIso_app_iff_quasiIso_mapHomotopyCategory`, invertibility of a comparison of
a right derived functor at an object of the homotopy category is equivalent to a statement about
quasi-isomorphisms of complexes, and that statement does not depend on the presentation or on the
chosen localized category.

## References

* [Stacks Project, Tag 0D5T](https://stacks.math.columbia.edu/tag/0D5T)
* [Stacks Project, Tag 0D5S](https://stacks.math.columbia.edu/tag/0D5S)
* [Stacks Project, Tag 079W](https://stacks.math.columbia.edu/tag/079W)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces

namespace Stacks.Cohomology.DerivedPushforwardComposition

universe v₁ v₂ v₃ v₄ v₅ v₆ u₁ u₂ u₃ u₄ u₅ u₆ u wX wY wZ

section Abstract

variable {KX : Type u₁} [Category.{v₁} KX] {KY : Type u₂} [Category.{v₂} KY]
  {KZ : Type u₃} [Category.{v₃} KZ] {DX : Type u₄} [Category.{v₄} DX]
  {DY : Type u₅} [Category.{v₅} DY] {DZ : Type u₆} [Category.{v₆} DZ]
  {QX : KX ⥤ DX} {QY : KY ⥤ DY} {QZ : KZ ⥤ DZ}
  {pf : KX ⥤ KY} {pg : KY ⥤ KZ} {pgf : KX ⥤ KZ}
  {ppf : KY ⥤ KX} {ppg : KZ ⥤ KY} {ppgf : KZ ⥤ KX}
  {Rf : DX ⥤ DY} {Rg : DY ⥤ DZ} {Rgf : DX ⥤ DZ}
  {Lf : DY ⥤ DX} {Lg : DZ ⥤ DY} {Lgf : DZ ⥤ DX}
  (af : ppf ⊣ pf) (ag : ppg ⊣ pg) (agf : ppgf ⊣ pgf)
  (Af : Lf ⊣ Rf) (Ag : Lg ⊣ Rg) (Agf : Lgf ⊣ Rgf)
  {ηf : pf ⋙ QY ⟶ QX ⋙ Rf} {ηg : pg ⋙ QZ ⟶ QY ⋙ Rg} {ηgf : pgf ⋙ QZ ⟶ QX ⋙ Rgf}
  {εf : QY ⋙ Lf ⟶ ppf ⋙ QX} {εg : QZ ⋙ Lg ⟶ ppg ⋙ QY} {εgf : QZ ⋙ Lgf ⟶ ppgf ⋙ QX}
  (c : pf ⋙ pg ≅ pgf) (d : ppg ⋙ ppf ≅ ppgf)
  (Dpb : Lg ⋙ Lf ≅ Lgf) (Dpf : Rf ⋙ Rg ≅ Rgf)

/-- **The transposition argument behind the composition formula for derived pushforward.**
Suppose given three adjunctions `ppf ⊣ pf`, `ppg ⊣ pg`, `ppgf ⊣ pgf` on the underlying
categories and three adjunctions `Lf ⊣ Rf`, `Lg ⊣ Rg`, `Lgf ⊣ Rgf` on the localized ones, each
derived adjunction compatible with its underlying one through the comparison maps `ηf, εf, …`
(`hf`, `hg`, `hgf`).  Suppose the composition isomorphism `Dpb` of the left adjoints factors the
comparison for `Lgf` through the underlying composition isomorphism `d` (`hDpb`), and that the
composition isomorphism `Dpf` of the right adjoints is coherent for transposition (`hDpf`).  Then
the comparison `pgf ⋙ QZ ⟶ QX ⋙ Rgf` built from `c`, `ηg` and `ηf`, followed by `Dpf`, is `ηgf` —
provided the two composition isomorphisms agree on the underlying categories (`hdeg`).

Transposing twice replaces the two sides by maps out of `Lf (Lg (QZ (pgf K)))`; there the
hypotheses are all that is needed, and `hdeg` is where the two composition isomorphisms meet. -/
theorem compUnit_comp_compIso_of_adjunctions
    (hf : ∀ K : KX, Lf.map (ηf.app K) ≫ Af.counit.app (QX.obj K) =
      εf.app (pf.obj K) ≫ QX.map (af.counit.app K))
    (hg : ∀ M : KY, Lg.map (ηg.app M) ≫ Ag.counit.app (QY.obj M) =
      εg.app (pg.obj M) ≫ QY.map (ag.counit.app M))
    (hgf : ∀ K : KX, Lgf.map (ηgf.app K) ≫ Agf.counit.app (QX.obj K) =
      εgf.app (pgf.obj K) ≫ QX.map (agf.counit.app K))
    (hDpb : ∀ W : KZ, Dpb.hom.app (QZ.obj W) ≫ εgf.app W =
      Lf.map (εg.app W) ≫ εf.app (ppg.obj W) ≫ QX.map (d.hom.app W))
    (hDpf : ∀ (M : DZ) (N : DX) (φ : Lgf.obj M ⟶ N),
      Ag.homEquiv _ _ (Af.homEquiv _ _ (Dpb.hom.app M ≫ φ)) ≫ Dpf.hom.app N =
        Agf.homEquiv M N φ)
    (hdeg : ∀ K : KX, ppf.map (ppg.map (c.inv.app K) ≫ ag.counit.app (pf.obj K)) ≫
      af.counit.app K = d.hom.app (pgf.obj K) ≫ agf.counit.app K)
    (K : KX) :
    (QZ.map (c.inv.app K) ≫ ηg.app (pf.obj K) ≫ Rg.map (ηf.app K)) ≫
        Dpf.hom.app (QX.obj K) = ηgf.app K := by
  have hηgf : ηgf.app K = Agf.homEquiv (QZ.obj (pgf.obj K)) (QX.obj K)
      ((εgf.app (pgf.obj K) ≫ QX.map (agf.counit.app K) :
        Lgf.obj (QZ.obj (pgf.obj K)) ⟶ QX.obj K)) :=
    (Equiv.symm_apply_eq _).mp (by rw [Adjunction.homEquiv_counit]; exact hgf K)
  have hmain : QZ.map (c.inv.app K) ≫ ηg.app (pf.obj K) ≫ Rg.map (ηf.app K) =
      Ag.homEquiv (QZ.obj (pgf.obj K)) (Rf.obj (QX.obj K))
        (Af.homEquiv (Lg.obj (QZ.obj (pgf.obj K))) (QX.obj K)
          (Dpb.hom.app (QZ.obj (pgf.obj K)) ≫
            (εgf.app (pgf.obj K) ≫ QX.map (agf.counit.app K) :
              Lgf.obj (QZ.obj (pgf.obj K)) ⟶ QX.obj K))) := by
    refine (Equiv.symm_apply_eq _).mp ((Equiv.symm_apply_eq _).mp ?_)
    rw [Adjunction.homEquiv_counit, Adjunction.homEquiv_counit]
    have hεg := εg.naturality (c.inv.app K)
    have hεf := εf.naturality (ppg.map (c.inv.app K) ≫ ag.counit.app (pf.obj K))
    have hcn := Ag.counit.naturality (ηf.app K)
    dsimp only [Functor.comp_map, Functor.id_map, Functor.comp_obj, Functor.id_obj] at hεg hεf hcn
    have step : Lg.map (QZ.map (c.inv.app K) ≫ ηg.app (pf.obj K) ≫ Rg.map (ηf.app K)) ≫
        Ag.counit.app (Rf.obj (QX.obj K)) =
      εg.app (pgf.obj K) ≫
        QY.map (ppg.map (c.inv.app K) ≫ ag.counit.app (pf.obj K)) ≫ ηf.app K := by
      rw [Functor.map_comp, Functor.map_comp, Category.assoc, Category.assoc, hcn,
        reassoc_of% (hg (pf.obj K)), reassoc_of% hεg, Functor.map_comp, Category.assoc]
    rw [step, Functor.map_comp, Functor.map_comp, Category.assoc, Category.assoc,
      hf K, reassoc_of% hεf, ← Functor.map_comp, hdeg K, Functor.map_comp,
      reassoc_of% (hDpb (pgf.obj K))]
  rw [hmain, hDpf, hηgf]

end Abstract

section Degreewise

variable {X Y Z : RingedSpace.{u, u}} (f : X ⟶ Y) (g : Y ⟶ Z)

/-- **The two composition isomorphisms agree, on sheaves of modules.**  Reading the
pushforward-composition isomorphism through `g^*` and the counit of `g`, then through `f^*` and the
counit of `f`, is the same as reading the pullback-composition isomorphism through the counit of
`f ≫ g`.

This is the defining property of `CategoryTheory.Adjunction.leftAdjointCompIso`, which is how
`Stacks.DerivedPullback.Composition.modulePullbackComp` is built from
`RingedSpaceModuleAdjunction.modulePushforwardComp`; the mates lemma
`CategoryTheory.conjugateEquiv_counit_symm` is that property. -/
theorem modulePullbackComp_hom_app_comp_counit (A : SheafOfModules.{u} (structureSheafRing X)) :
    (modulePullback f).map ((modulePullback g).map ((modulePushforwardComp f g).inv.app A) ≫
          (modulePullbackPushforwardAdjunction g).counit.app ((modulePushforward f).obj A)) ≫
        (modulePullbackPushforwardAdjunction f).counit.app A =
      (Stacks.DerivedPullback.Composition.modulePullbackComp f g).hom.app ((modulePushforward (f ≫
        g)).obj A) ≫
        (modulePullbackPushforwardAdjunction (f ≫ g)).counit.app A := by
  have h := CategoryTheory.conjugateEquiv_counit_symm
    (modulePullbackPushforwardAdjunction (f ≫ g))
    ((modulePullbackPushforwardAdjunction g).comp (modulePullbackPushforwardAdjunction f))
    (modulePushforwardComp f g).inv A
  -- `modulePushforwardComp_inv_app` would replace the component by an identity morphism written
  -- at the other spelling of its target, after which `Functor.map_id` no longer applies.
  dsimp [-RingedSpaceModuleAdjunction.modulePushforwardComp_inv_app] at h
  rw [Stacks.DerivedPullback.Composition.modulePullbackComp, Adjunction.leftAdjointCompIso_hom,
    Adjunction.leftAdjointCompNatTrans]
  simpa [Adjunction.comp_counit_app] using h

/-- `modulePullbackComp_hom_app_comp_counit` on cochain complexes.  Every map in sight is
degreewise, so the identity holds degree by degree. -/
theorem mapHomologicalComplex_pullbackComp_hom_app_comp_counit
    (K : CochainComplex (SheafOfModules.{u} (structureSheafRing X)) ℤ) :
    ((modulePullback f).mapHomologicalComplex (ComplexShape.up ℤ)).map
          (((modulePullback g).mapHomologicalComplex (ComplexShape.up ℤ)).map
              ((Functor.mapHomologicalComplexCompIso (modulePushforwardComp f g)
                (ComplexShape.up ℤ)).inv.app K) ≫
            (Adjunction.mapHomologicalComplexAdjunction
                (modulePullbackPushforwardAdjunction g) (ComplexShape.up ℤ)).counit.app
              (((modulePushforward f).mapHomologicalComplex (ComplexShape.up ℤ)).obj K)) ≫
        (Adjunction.mapHomologicalComplexAdjunction
            (modulePullbackPushforwardAdjunction f) (ComplexShape.up ℤ)).counit.app K =
      (Functor.mapHomologicalComplexCompIso (Stacks.DerivedPullback.Composition.modulePullbackComp f
        g)
            (ComplexShape.up ℤ)).hom.app
          (((modulePushforward (f ≫ g)).mapHomologicalComplex (ComplexShape.up ℤ)).obj K) ≫
        (Adjunction.mapHomologicalComplexAdjunction
            (modulePullbackPushforwardAdjunction (f ≫ g)) (ComplexShape.up ℤ)).counit.app K :=
  HomologicalComplex.hom_ext _ _ fun n => modulePullbackComp_hom_app_comp_counit f g (K.X n)

/-- `modulePullbackComp_hom_app_comp_counit` on the unbounded homotopy categories.  This is the
one input of `compUnit_comp_compIso_of_adjunctions` that is not formal. -/
theorem mapHomotopyCategory_pullbackComp_hom_app_comp_counit
    (K : HomotopyCategory (SheafOfModules.{u} (structureSheafRing X)) (ComplexShape.up ℤ)) :
    ((modulePullback f).mapHomotopyCategory (ComplexShape.up ℤ)).map
          (((modulePullback g).mapHomotopyCategory (ComplexShape.up ℤ)).map
              ((Functor.mapHomotopyCategoryCompIso (modulePushforwardComp f g)
                (ComplexShape.up ℤ)).inv.app K) ≫
            (homotopyPullbackPushforwardAdjunction g).counit.app
              (((modulePushforward f).mapHomotopyCategory (ComplexShape.up ℤ)).obj K)) ≫
        (homotopyPullbackPushforwardAdjunction f).counit.app K =
      (Stacks.DerivedPullback.Composition.pullbackOnHomotopyCompIso f g).hom.app
          (((modulePushforward (f ≫ g)).mapHomotopyCategory (ComplexShape.up ℤ)).obj K) ≫
        (homotopyPullbackPushforwardAdjunction (f ≫ g)).counit.app K := by
  obtain ⟨K⟩ := K
  exact congrArg (HomotopyCategory.quotient _ _).map
    (mapHomologicalComplex_pullbackComp_hom_app_comp_counit f g K)

end Degreewise

section Resolution

variable {Y Z : RingedSpace.{u, u}} [HasDerivedCategory.{wY} (ModuleSheaves.{u} Y)]
  [HasDerivedCategory.{wZ} (ModuleSheaves.{u} Z)] (g : Y ⟶ Z)
  (Rg : DerivedCategory (ModuleSheaves.{u} Y) ⥤ DerivedCategory (ModuleSheaves.{u} Z))
  (αg : Stacks.Cohomology.DerivedPushforwardComposition.pushforwardToDerivedCategory g ⟶
    DerivedCategory.Qh ⋙ Rg)

/-- **Invertibility of a comparison, read on complexes.**  For a right derived functor of
degreewise pushforward along `g`, the comparison is invertible at an object `M` of `K(𝒪_Y)`
exactly when degreewise `g_*` carries one K-injective resolution of `M` to a quasi-isomorphism.

The right-hand side mentions neither the presentation `(Rg, αg)` nor the chosen derived
categories, which is what lets a statement proved for one choice be transported to any other.
The proof is the naturality square of `αg` along the resolution: its other three edges are
invertible, the comparison at a K-injective complex by Tag 070K and the image of the resolution
because localization inverts quasi-isomorphisms. -/
theorem isIso_app_iff_quasiIso_mapHomotopyCategory
    [Rg.IsRightDerivedFunctor αg
      (HomotopyCategory.quasiIso (ModuleSheaves.{u} Y) (ComplexShape.up ℤ))]
    (M : HomotopyCategory (ModuleSheaves.{u} Y) (ComplexShape.up ℤ))
    (J : CochainComplex (ModuleSheaves.{u} Y) ℤ) (hJ : J.IsKInjective)
    (s : M ⟶ (HomotopyCategory.quotient (ModuleSheaves.{u} Y) (ComplexShape.up ℤ)).obj J)
    (hs : HomotopyCategory.quasiIso (ModuleSheaves.{u} Y) (ComplexShape.up ℤ) s) :
    IsIso (αg.app M) ↔
      HomotopyCategory.quasiIso (ModuleSheaves.{u} Z) (ComplexShape.up ℤ)
        (((modulePushforward g).mapHomotopyCategory (ComplexShape.up ℤ)).map s) := by
  have hnat := αg.naturality s
  dsimp only [Functor.comp_map] at hnat
  have := isIso_app_of_isKInjective.{u, wY, wZ} g Rg αg J hJ
  have : IsIso (DerivedCategory.Qh.map s) :=
    Localization.inverts DerivedCategory.Qh
      (HomotopyCategory.quasiIso (ModuleSheaves.{u} Y) (ComplexShape.up ℤ)) s hs
  rw [← DerivedCategory.isIso_Qh_map_iff]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have := h
    have : IsIso (DerivedCategory.Qh.map
        (((modulePushforward g).mapHomotopyCategory (ComplexShape.up ℤ)).map s) ≫
          αg.app ((HomotopyCategory.quotient (ModuleSheaves.{u} Y)
            (ComplexShape.up ℤ)).obj J)) := by
      rw [hnat]; infer_instance
    exact IsIso.of_isIso_comp_right _ (αg.app _)
  · have := h
    have : IsIso (αg.app M ≫ Rg.map (DerivedCategory.Qh.map s)) := by
      rw [← hnat]; infer_instance
    exact IsIso.of_isIso_comp_right _ (Rg.map (DerivedCategory.Qh.map s))

end Resolution

/-- `Functor.leftDerived_fac_app` for `L(f ≫ g)^*`, at arbitrary derived categories. -/
private theorem derivedPullbackCompIsoCanonical_hom_app_comp_comparison_aux
    {X Y Z : RingedSpace.{u, u}} [HasDerivedCategory.{wX} (ModuleSheaves.{u} X)]
    [HasDerivedCategory.{wY} (ModuleSheaves.{u} Y)] [HasDerivedCategory.{wZ} (ModuleSheaves.{u} Z)]
    (f : X ⟶ Y) (g : Y ⟶ Z)
    (W : HomotopyCategory (SheafOfModules.{u} (structureSheafRing Z)) (ComplexShape.up ℤ)) :
    (Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical f g).hom.app
      (DerivedCategory.Qh.obj W) ≫
        (derivedPullbackComparison (f ≫ g)).app W =
      (derivedPullback f).map ((derivedPullbackComparison g).app W) ≫
        (derivedPullbackComparison f).app
            (((modulePullback g).mapHomotopyCategory (ComplexShape.up ℤ)).obj W) ≫
          DerivedCategory.Qh.map ((Stacks.DerivedPullback.Composition.pullbackOnHomotopyCompIso f
            g).hom.app W) :=
  (Functor.leftDerived_fac_app (derivedPullback (f ≫ g)) (derivedPullbackComparison (f ≫ g))
      (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing Z)) (ComplexShape.up ℤ))
      (derivedPullback g ⋙ derivedPullback f)
      (Stacks.DerivedPullback.Composition.derivedPullbackCompCounit f g (derivedPullback f)
        (derivedPullback g)
        (derivedPullbackComparison f) (derivedPullbackComparison g)) W).trans
    (Stacks.DerivedPullback.Composition.derivedPullbackCompCounit_app f g (derivedPullback f)
      (derivedPullback g)
      (derivedPullbackComparison f) (derivedPullbackComparison g) W)

noncomputable section Canonical

attribute [local instance] HasDerivedCategory.standard

variable {X Y Z : RingedSpace.{u, u}} (f : X ⟶ Y) (g : Y ⟶ Z)

/-- The canonical comparison of Tag 0D5S factors the comparison for `L(f ≫ g)^*` through the
degreewise pullback-composition isomorphism.  This is `CategoryTheory.Functor.leftDerived_fac_app`
for the left derived functor `L(f ≫ g)^*`, read through
`Stacks.DerivedPullback.Composition.derivedPullbackCompCounit_app`. -/
theorem derivedPullbackCompIsoCanonical_hom_app_comp_comparison
    (W : HomotopyCategory (SheafOfModules.{u} (structureSheafRing Z)) (ComplexShape.up ℤ)) :
    (Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical f g).hom.app
      (DerivedCategory.Qh.obj W) ≫
        (derivedPullbackComparison (f ≫ g)).app W =
      (derivedPullback f).map ((derivedPullbackComparison g).app W) ≫
        (derivedPullbackComparison f).app
            (((modulePullback g).mapHomotopyCategory (ComplexShape.up ℤ)).obj W) ≫
          DerivedCategory.Qh.map ((Stacks.DerivedPullback.Composition.pullbackOnHomotopyCompIso f
            g).hom.app W) :=
  derivedPullbackCompIsoCanonical_hom_app_comp_comparison_aux f g W

/-- **The two composition isomorphisms for derived pushforward agree.**  The comparison from
degreewise pushforward along `f ≫ g` to `Rf_* ⋙ Rg_*` of Tag 0D5T, followed by the composition
isomorphism `Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforwardCompIso` of Tag
  079W, is the canonical comparison of
`R(f ≫ g)_*`.

Both maps `R(f ≫ g)_* ⟶ Rf_* ⋙ Rg_*` are therefore the same, and so the first is invertible. -/
theorem derivedPushforwardCompUnit_comp_derivedPushforwardCompIso
    (K : HomotopyCategory (SheafOfModules.{u} (structureSheafRing X)) (ComplexShape.up ℤ)) :
    (derivedPushforwardCompUnit f g (derivedPushforward f) (derivedPushforward g)
            (derivedPushforwardUnit f) (derivedPushforwardUnit g)).app K ≫
        (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforwardCompIso f g).hom.app
          (DerivedCategory.Qh.obj K) =
      (derivedPushforwardUnit (f ≫ g)).app K := by
  rw [derivedPushforwardCompUnit_app.{u, u + 1, u + 1, u + 1} f g (derivedPushforward f)
    (derivedPushforward g) (derivedPushforwardUnit f) (derivedPushforwardUnit g) K]
  exact compUnit_comp_compIso_of_adjunctions
    (homotopyPullbackPushforwardAdjunction f) (homotopyPullbackPushforwardAdjunction g)
    (homotopyPullbackPushforwardAdjunction (f ≫ g)) (derivedAdjunction f) (derivedAdjunction g)
    (derivedAdjunction (f ≫ g))
    (Functor.mapHomotopyCategoryCompIso (modulePushforwardComp f g) (ComplexShape.up ℤ))
    (Stacks.DerivedPullback.Composition.pullbackOnHomotopyCompIso f g)
    (Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical f g)
    (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforwardCompIso f g)
    (derivedAdjunction_counit_fac f) (derivedAdjunction_counit_fac g)
    (derivedAdjunction_counit_fac (f ≫ g))
    (derivedPullbackCompIsoCanonical_hom_app_comp_comparison f g)
    (derivedAdjunction_comp_homEquiv f g)
    (mapHomotopyCategory_pullbackComp_hom_app_comp_counit f g) K

/-- The composite `Rf_* ⋙ Rg_*`, with the comparison `derivedPushforwardCompUnit`, is a right
derived functor of degreewise pushforward along `f ≫ g`: it is `R(f ≫ g)_*` read through the
composition isomorphism of Tag 079W. -/
theorem isRightDerivedFunctor_comp_canonical :
    (derivedPushforward f ⋙ derivedPushforward g).IsRightDerivedFunctor
      (derivedPushforwardCompUnit f g (derivedPushforward f) (derivedPushforward g)
        (derivedPushforwardUnit f) (derivedPushforwardUnit g))
      (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing X))
        (ComplexShape.up ℤ)) := by
  refine (Functor.isRightDerivedFunctor_iff_of_iso (derivedPushforwardUnit (f ≫ g)) _ _
    (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforwardCompIso f g).symm ?_).1
      inferInstance
  refine NatTrans.ext (funext fun K => ?_)
  dsimp only [NatTrans.comp_app, Functor.whiskerLeft_app, Iso.symm_hom]
  rw [← derivedPushforwardCompUnit_comp_derivedPushforwardCompIso f g K, Category.assoc,
    Iso.hom_inv_id_app]
  simp

/-- **`PushforwardComputesDerived` holds for the canonical derived pushforward along `g`.**  This
is the hypothesis that the whole of Tag 0D5T was reduced to, now discharged. -/
theorem pushforwardComputesDerived_canonical :
    PushforwardComputesDerived.{u, u + 1, u + 1} f g (derivedPushforward g)
      (derivedPushforwardUnit g) :=
  (isIso_derivedPushforwardComparison_iff.{u, u + 1, u + 1, u + 1} f g (derivedPushforward f)
      (derivedPushforward g)
      (derivedPushforward (f ≫ g)) (derivedPushforwardUnit f) (derivedPushforwardUnit g)
      (derivedPushforwardUnit (f ≫ g))).1
    ((Functor.isRightDerivedFunctor_iff_isIso_rightDerivedDesc (derivedPushforward (f ≫ g))
        (derivedPushforwardUnit (f ≫ g))
        (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing X)) (ComplexShape.up ℤ))
        (derivedPushforward f ⋙ derivedPushforward g)
        (derivedPushforwardCompUnit f g (derivedPushforward f) (derivedPushforward g)
          (derivedPushforwardUnit f) (derivedPushforwardUnit g))).1
      (isRightDerivedFunctor_comp_canonical f g))

/-- **The composition formula, with no derived category in the statement.**  If `I` is a
K-injective complex of `𝒪_X`-modules and `s` is a quasi-isomorphism from `f_* I` to a K-injective
complex of `𝒪_Y`-modules, then `g_* s` is a quasi-isomorphism.

This is `pushforwardComputesDerived_canonical` read through
`isIso_app_iff_quasiIso_mapHomotopyCategory`.  Because it mentions no derived category, it is the
form in which the result holds for *every* choice of derived categories, which is what
`pushforwardComputesDerived` then uses. -/
theorem quasiIso_mapHomotopyCategory_pushforward_of_isKInjective
    (I : CochainComplex (SheafOfModules.{u} (structureSheafRing X)) ℤ) (hI : I.IsKInjective)
    (J : CochainComplex (SheafOfModules.{u} (structureSheafRing Y)) ℤ) (hJ : J.IsKInjective)
    (s : ((modulePushforward f).mapHomotopyCategory (ComplexShape.up ℤ)).obj
          ((HomotopyCategory.quotient (SheafOfModules.{u} (structureSheafRing X))
            (ComplexShape.up ℤ)).obj I) ⟶
        (HomotopyCategory.quotient (SheafOfModules.{u} (structureSheafRing Y))
          (ComplexShape.up ℤ)).obj J)
    (hs : HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing Y))
      (ComplexShape.up ℤ) s) :
    HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing Z)) (ComplexShape.up ℤ)
      (((modulePushforward g).mapHomotopyCategory (ComplexShape.up ℤ)).map s) := by
  rw [← isIso_app_iff_quasiIso_mapHomotopyCategory.{u, u + 1, u + 1} g (derivedPushforward g)
    (derivedPushforwardUnit g) _ J hJ s hs]
  exact pushforwardComputesDerived_canonical f g I hI

end Canonical

section General

variable {X Y Z : RingedSpace.{u, u}}
  [HasDerivedCategory.{wX} (ModuleSheaves.{u} X)]
  [HasDerivedCategory.{wY} (ModuleSheaves.{u} Y)]
  [HasDerivedCategory.{wZ} (ModuleSheaves.{u} Z)]
  (f : X ⟶ Y) (g : Y ⟶ Z)
  (Rf : DerivedCategory (ModuleSheaves.{u} X) ⥤ DerivedCategory (ModuleSheaves.{u} Y))
  (Rg : DerivedCategory (ModuleSheaves.{u} Y) ⥤ DerivedCategory (ModuleSheaves.{u} Z))
  (Rgf : DerivedCategory (ModuleSheaves.{u} X) ⥤ DerivedCategory (ModuleSheaves.{u} Z))
  (αf : Stacks.Cohomology.DerivedPushforwardComposition.pushforwardToDerivedCategory f ⟶
    DerivedCategory.Qh ⋙ Rf)
  (αg : Stacks.Cohomology.DerivedPushforwardComposition.pushforwardToDerivedCategory g ⟶
    DerivedCategory.Qh ⋙ Rg)
  (αgf : Stacks.Cohomology.DerivedPushforwardComposition.pushforwardToDerivedCategory (f ≫ g) ⟶
    DerivedCategory.Qh ⋙ Rgf)

omit [HasDerivedCategory.{wX} (ModuleSheaves.{u} X)] in
/-- **The hypothesis of Tag 0D5T holds unconditionally.**  Degreewise pushforward along `f` carries
every K-injective complex of `𝒪_X`-modules to a complex computing any derived pushforward along
`g`, for every choice of derived categories and every presentation of that derived pushforward.

A K-injective resolution of `f_* I` exists, and
`quasiIso_mapHomotopyCategory_pushforward_of_isKInjective` says that `g_*` carries it to a
quasi-isomorphism; `isIso_app_iff_quasiIso_mapHomotopyCategory` turns that back into invertibility
of the comparison. -/
theorem pushforwardComputesDerived
    [Rg.IsRightDerivedFunctor αg
      (HomotopyCategory.quasiIso (ModuleSheaves.{u} Y) (ComplexShape.up ℤ))] :
    PushforwardComputesDerived f g Rg αg := by
  intro I hI
  obtain ⟨J, s, hJ, hs⟩ :=
    Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.exists_quasiIso_isKInjective Y
    (((modulePushforward f).mapHomologicalComplex (ComplexShape.up ℤ)).obj I)
  have hmem : HomotopyCategory.quasiIso (ModuleSheaves.{u} Y) (ComplexShape.up ℤ)
      ((HomotopyCategory.quotient (ModuleSheaves.{u} Y) (ComplexShape.up ℤ)).map s) := by
    rw [HomotopyCategory.quotient_map_mem_quasiIso_iff]; exact hs
  exact (isIso_app_iff_quasiIso_mapHomotopyCategory.{u, wY, wZ} g Rg αg _ J hJ
      ((HomotopyCategory.quotient (ModuleSheaves.{u} Y) (ComplexShape.up ℤ)).map s) hmem).2
    (quasiIso_mapHomotopyCategory_pushforward_of_isKInjective f g I hI J hJ _ hmem)

/-- **Stacks 0D5T.**  For composable morphisms `f : X ⟶ Y` and `g : Y ⟶ Z` of ringed spaces, the
canonical comparison from a right derived pushforward along `f ≫ g` to the composite of right
derived pushforwards along `f` and `g` is an isomorphism.

No hypothesis beyond the two morphisms and the three derived functors: the condition
`PushforwardComputesDerived`, which `isIso_derivedPushforwardComparison_iff` shows to be
equivalent to this statement, is discharged by `pushforwardComputesDerived`. -/
@[stacks 0D5T]
theorem isIso_derivedPushforwardComparison_unconditional
    [Rf.IsRightDerivedFunctor αf
      (HomotopyCategory.quasiIso (ModuleSheaves.{u} X) (ComplexShape.up ℤ))]
    [Rg.IsRightDerivedFunctor αg
      (HomotopyCategory.quasiIso (ModuleSheaves.{u} Y) (ComplexShape.up ℤ))]
    [Rgf.IsRightDerivedFunctor αgf
      (HomotopyCategory.quasiIso (ModuleSheaves.{u} X) (ComplexShape.up ℤ))] :
    IsIso (derivedPushforwardComparison f g Rf Rg Rgf αf αg αgf) :=
  isIso_derivedPushforwardComparison f g Rf Rg Rgf αf αg αgf
    (pushforwardComputesDerived f g Rg αg)

end General

noncomputable section CanonicalFree

variable {X Y Z : RingedSpace.{u, u}} [HasDerivedCategory.{wX} (ModuleSheaves.{u} X)]
  [HasDerivedCategory.{wY} (ModuleSheaves.{u} Y)] [HasDerivedCategory.{wZ} (ModuleSheaves.{u} Z)]
  (f : X ⟶ Y) (g : Y ⟶ Z)

/-- The canonical comparison of Tag 0D5S factors the comparison for `L(f ≫ g)^*` through the
degreewise pullback-composition isomorphism, at arbitrary models of the three derived categories.
`derivedPullbackCompIsoCanonical_hom_app_comp_comparison` is the same statement at
`HasDerivedCategory.standard`; a consumer computing the derived stalk of an iterated derived
pullback works at the locally small model of `StacksFrontier.Homology.DerivedCategory.LocallySmall`,
where that statement says nothing.  This is `CategoryTheory.Functor.leftDerived_fac_app`
for the left derived functor `L(f ≫ g)^*`, read through
`Stacks.DerivedPullback.Composition.derivedPullbackCompCounit_app`. -/
theorem derivedPullbackCompIsoCanonical_hom_app_comp_comparison_general
    (W : HomotopyCategory (SheafOfModules.{u} (structureSheafRing Z)) (ComplexShape.up ℤ)) :
    (Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical f g).hom.app
      (DerivedCategory.Qh.obj W) ≫
        (derivedPullbackComparison (f ≫ g)).app W =
      (derivedPullback f).map ((derivedPullbackComparison g).app W) ≫
        (derivedPullbackComparison f).app
            (((modulePullback g).mapHomotopyCategory (ComplexShape.up ℤ)).obj W) ≫
          DerivedCategory.Qh.map ((Stacks.DerivedPullback.Composition.pullbackOnHomotopyCompIso f
            g).hom.app W) :=
  derivedPullbackCompIsoCanonical_hom_app_comp_comparison_aux f g W

end CanonicalFree

end Stacks.Cohomology.DerivedPushforwardComposition

end
