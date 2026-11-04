module

public import StacksFrontier.Algebra.Homology.ShortComplex.InverseLimit
public import StacksFrontier.Algebra.Module.FourTermLimitComparison
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.AlgebraizationLocalCohomologyLimit
public import StacksFrontier.CategoryTheory.Abelian.DeltaFunctor.FilteredColimit
public import StacksFrontier.RingTheory.AdicCompletion.TateModule.FiniteComplete
public import StacksFrontier.RingTheory.LocalCohomology.LowDegree.CechSectionsComparison
public import StacksFrontier.RingTheory.LocalCohomology.SectionsIso.Naturality

/-!
# The sections on `Spec A ∖ V(J)` of a complete module are the limit of those of its quotients

Let `A` be a Noetherian local ring, `I` an ideal with `A` `I`-adically complete, `M` a finite
`A`-module, and `J` an ideal with `V(J) ∩ V(I) = {𝔪}` and `J ⊆ J₀` for the ideal `J₀` of
Stacks 0DXP. This file proves that the canonical map

`Γ(Spec A ∖ V(J), M̃) ⟶ lim_n Γ(Spec A ∖ V(J), (M/IⁿM)~)`

is surjective. It is the comparison clause of Stacks 0DXQ at `i = 0`, read on the affine
complement, and the only thing the conclusion of Stacks 0DXR still lacked.

## The diagram chase

The four-term sequence of Stacks 0BK0 gives, for every `A`-module `N`, an exact sequence

`0 ⟶ H⁰_J(N) ⟶ N ⟶ Γ(Spec A ∖ V(J), Ñ) ⟶ H¹_J(N) ⟶ 0`,

natural in `N`. Applying it to `N = M` and to the tower `N = M/IⁿM`, and taking the inverse limit
of the latter, gives a map of three-term sequences

```
M                  ⟶  Γ(Spec A ∖ V(J), M̃)                ⟶  H¹_J(M)              ⟶ 0
↓                      ↓                                     ↓
lim_n M/IⁿM        ⟶  lim_n Γ(Spec A ∖ V(J), (M/IⁿM)~)   ⟶  lim_n H¹_J(M/IⁿM)
```

to which `Stacks.LimitComparison.surjective_middle` applies: the middle comparison is surjective
once the left one is, the right one is, the top boundary is onto and the bottom row is exact in
the middle. The four inputs are:

* the top boundary `Γ ⟶ H¹_J(M)` is onto, by
  `Stacks.LocalCohomology.localizationBoundary_surjective`;
* the left comparison `M ⟶ lim_n M/IⁿM` is onto, because a finite module over a Noetherian
  `I`-adically complete ring is `I`-adically complete;
* the right comparison `H¹_J(M) ⟶ lim_n H¹_J(M/IⁿM)` is onto, by
  `Stacks.Algebraization.surjective_localCohomologyAdicQuotientToLimit`, which is where
  Stacks 0DXP and the pinned Stacks 0DXJ enter;
* the bottom row is exact at the middle by Stacks 070B, the inverse limit of a four-term exact
  sequence of towers whose first term is Mittag-Leffler. The first term here is
  `n ↦ H⁰_J(M/IⁿM)`, Mittag-Leffler by
  `Stacks.LocalCohomology.isMittagLeffler_forget_adicQuotientLocalCohomologySystem`.

## Main definitions

* `Stacks.Algebraization.affineComplementSectionsFunctor` — the functor `N ↦ Γ(Spec A ∖ V(J), Ñ)`.
* `Stacks.Algebraization.complementRestrictionNat`,
  `Stacks.Algebraization.complementBoundaryNat`,
  `Stacks.Algebraization.localCohomologyZeroNat` — the three maps of the four-term sequence, as
  natural transformations of functors on `A`-modules.
* `Stacks.Algebraization.complementSectionsAdicTower` and the three other towers obtained by
  composing with `n ↦ M/IⁿM`, together with the comparison maps into their limits.

## Main results

* `Stacks.Algebraization.surjective_complementSectionsToLimit` — the surjectivity above.

## References

* [Stacks Project, Tag 0BK0](https://stacks.math.columbia.edu/tag/0BK0)
* [Stacks Project, Tag 070B](https://stacks.math.columbia.edu/tag/070B)
* [Stacks Project, Tag 0DXP](https://stacks.math.columbia.edu/tag/0DXP)
* [Stacks Project, Tag 0DXQ](https://stacks.math.columbia.edu/tag/0DXQ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite IsLocalRing
open TopologicalSpace
open AlgebraicGeometry.ProEtale

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Stacks.Algebraization

open Stacks.LocalCohomology

variable (A : Type u) [CommRing A]

/-! ### The sections on the affine complement as a functor of the module -/

/-- The functor `N ↦ Γ(Spec A ∖ V(J), Ñ)` on `A`-modules: the sheaf associated to `N`,
restricted to the open subscheme `Spec A ∖ V(J)`, and its global sections there. -/
public def affineComplementSectionsFunctor (J : Ideal A) : ModuleCat.{u} A ⥤ ModuleCat.{u} A :=
  tilde.functor (CommRingCat.of A) ⋙ restrictFunctor (complementZeroLocus A J).ι ⋙
    complementGlobalSectionsFunctor A J

/-- The value of `Stacks.Algebraization.affineComplementSectionsFunctor` is the module of global
sections of `Stacks.LocalCohomology.complementTilde` that the four-term sequence of Stacks 0BK0
is phrased with. -/
public theorem affineComplementSectionsFunctor_obj (J : Ideal A) (N : ModuleCat.{u} A) :
    (affineComplementSectionsFunctor A J).obj N =
      complementGlobalSections A J (complementTilde A J N) :=
  rfl

/-- The functor acts on sections by applying the module map to the numerators. -/
public theorem affineComplementSectionsFunctor_map_apply (J : Ideal A) {M N : ModuleCat.{u} A}
    (f : M ⟶ N) (s : moduleSections M ((complementZeroLocus A J).ι ''ᵁ ⊤)) :
    ConcreteCategory.hom ((affineComplementSectionsFunctor A J).map f) s =
      moduleSectionsMap f ((complementZeroLocus A J).ι ''ᵁ ⊤) s :=
  rfl

/-! ### The three maps of the four-term sequence, as natural transformations -/

variable {A} in
/-- A linear map between the carriers of two objects of `ModuleCat A`, as a morphism of that
category. Unlike `ModuleCat.ofHom`, the two objects are named, so no instance of
`Module A` has to be synthesized for a carrier presented as the value of a functor. -/
public def ofLinearMap {X Y : ModuleCat.{u} A} (f : X →ₗ[A] Y) : X ⟶ Y :=
  ModuleCat.ofHom f

variable {A} in
public theorem ofLinearMap_apply {X Y : ModuleCat.{u} A} (f : X →ₗ[A] Y) (x : X) :
    ConcreteCategory.hom (ofLinearMap f) x = f x :=
  rfl

variable {A} in
/-- The restriction map `N ⟶ Γ(Spec A ∖ V(J), Ñ)` of the four-term sequence is the constant
fraction `m ↦ m/1`. -/
public theorem restrictionToComplement_refl_apply {J : Ideal A} {hJ : J.FG}
    (D : LocalizationTriangleData.{u, u} A J hJ) (N : ModuleCat.{u} A) (m : N) :
    restrictionToComplement D N (complementTilde A J N) (Iso.refl _) m =
      moduleSectionsMk N ((complementZeroLocus A J).ι ''ᵁ ⊤) m := by
  rw [restrictionToComplement_apply]
  rfl

/-- **The restriction map of the four-term sequence is natural in the module**: a module map
carries the constant fraction `m/1` to the constant fraction `f m / 1`. -/
public theorem affineComplementSectionsFunctor_map_restrictionToComplement (J : Ideal A) (hJ : J.FG)
    (D : LocalizationTriangleData.{u, u} A J hJ) {M N : ModuleCat.{u} A} (f : M ⟶ N) (m : M) :
    ConcreteCategory.hom ((affineComplementSectionsFunctor A J).map f)
        (restrictionToComplement D M (complementTilde A J M) (Iso.refl _) m) =
      restrictionToComplement D N (complementTilde A J N) (Iso.refl _) (f m) := by
  show moduleSectionsMap f ((complementZeroLocus A J).ι ''ᵁ ⊤)
      (restrictionToComplement D M (complementTilde A J M) (Iso.refl _) m) =
    restrictionToComplement D N (complementTilde A J N) (Iso.refl _) (f m)
  rw [restrictionToComplement_refl_apply D M m,
    restrictionToComplement_refl_apply D N (ConcreteCategory.hom f m)]
  exact LinearMap.congr_fun (moduleSectionsMap_comp_moduleSectionsMk f
    ((complementZeroLocus A J).ι ''ᵁ ⊤)) m

/-- **The boundary map of the four-term sequence is natural in the module**: this is
`Stacks.LocalCohomology.localizationBoundary_naturality` with the action of a module map on
sections written as the functor
`Stacks.Algebraization.affineComplementSectionsFunctor`. -/
public theorem localizationBoundary_affineComplementSectionsFunctor_map (J : Ideal A) (hJ : J.FG)
    (D : LocalizationTriangleData.{u, u} A J hJ) {M N : ModuleCat.{u} A} (f : M ⟶ N)
    (s : (affineComplementSectionsFunctor A J).obj M) :
    localizationBoundary D N (complementTilde A J N) (Iso.refl _)
        (ConcreteCategory.hom ((affineComplementSectionsFunctor A J).map f) s) =
      ConcreteCategory.hom ((localCohomologyOnModules A J hJ ⋙
          DerivedCategory.homologyFunctor (ModuleCat.{u} A) 1).map f)
        (localizationBoundary D M (complementTilde A J M) (Iso.refl _) s) :=
  localizationBoundary_naturality D f s

/-- **The restriction map of the four-term sequence, as a natural transformation.** Its component
at `N` is the map `N ⟶ Γ(Spec A ∖ V(J), Ñ)` of Stacks 0BK0; naturality is the statement that a
module map carries the constant fraction `m/1` to the constant fraction `f m / 1`. -/
public def complementRestrictionNat (J : Ideal A) (hJ : J.FG)
    (D : LocalizationTriangleData.{u, u} A J hJ) :
    𝟭 (ModuleCat.{u} A) ⟶ affineComplementSectionsFunctor A J where
  app N := ofLinearMap (X := (𝟭 (ModuleCat.{u} A)).obj N)
    (Y := (affineComplementSectionsFunctor A J).obj N)
    (restrictionToComplement D N (complementTilde A J N) (Iso.refl _))
  naturality _ _ f := ModuleCat.hom_ext (LinearMap.ext fun m =>
    (affineComplementSectionsFunctor_map_restrictionToComplement A J hJ D f m).symm)

public theorem complementRestrictionNat_app_apply (J : Ideal A) (hJ : J.FG)
    (D : LocalizationTriangleData.{u, u} A J hJ) (N : ModuleCat.{u} A) (m : N) :
    ConcreteCategory.hom ((complementRestrictionNat A J hJ D).app N) m =
      restrictionToComplement D N (complementTilde A J N) (Iso.refl _) m :=
  ofLinearMap_apply _ m

/-- **The boundary map of the four-term sequence, as a natural transformation.** Its component at
`N` is the connecting map `Γ(Spec A ∖ V(J), Ñ) ⟶ H¹_J(N)`; naturality is
`Stacks.LocalCohomology.localizationBoundary_naturality`. -/
public def complementBoundaryNat (J : Ideal A) (hJ : J.FG)
    (D : LocalizationTriangleData.{u, u} A J hJ) :
    affineComplementSectionsFunctor A J ⟶
      localCohomologyOnModules A J hJ ⋙ DerivedCategory.homologyFunctor (ModuleCat.{u} A) 1 where
  app N := ofLinearMap (X := (affineComplementSectionsFunctor A J).obj N)
    (Y := (localCohomologyOnModules A J hJ ⋙
      DerivedCategory.homologyFunctor (ModuleCat.{u} A) 1).obj N)
    (localizationBoundary D N (complementTilde A J N) (Iso.refl _))
  naturality _ _ f := ModuleCat.hom_ext (LinearMap.ext fun s =>
    localizationBoundary_affineComplementSectionsFunctor_map A J hJ D f s)

public theorem complementBoundaryNat_app_apply (J : Ideal A) (hJ : J.FG)
    (D : LocalizationTriangleData.{u, u} A J hJ) (N : ModuleCat.{u} A)
    (s : (affineComplementSectionsFunctor A J).obj N) :
    ConcreteCategory.hom ((complementBoundaryNat A J hJ D).app N) s =
      localizationBoundary D N (complementTilde A J N) (Iso.refl _) s :=
  ofLinearMap_apply _ s

/-- The degree-zero cohomology of the counit of the local-cohomology adjunction, as a natural
transformation `H⁰_J(-) ⟶ H⁰((-)[0])`. -/
public def localCohomologyZeroCounitNat (J : Ideal A) (hJ : J.FG) :
    localCohomologyOnModules A J hJ ⋙ DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0 ⟶
      DerivedCategory.singleFunctor (ModuleCat.{u} A) 0 ⋙
        DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0 where
  app N := (DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).map
    ((Dualizing.localCohomologyAdjunction A J hJ).counit.app
      ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj N))
  naturality _ _ f :=
    (((DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).map_comp _ _).symm.trans
        (congrArg (DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).map
          ((Dualizing.localCohomologyAdjunction A J hJ).counit.naturality
            ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).map f)))).trans
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).map_comp _ _)

/-- **The map `H⁰_J(N) ⟶ N` of the four-term sequence, as a natural transformation.** It is the
degree-zero cohomology of the counit of the local-cohomology adjunction followed by the
identification `H⁰(N[0]) ≅ N`, which is exactly how
`Stacks.LocalCohomology.localCohomologyZeroToModule` is defined. -/
public def localCohomologyZeroNat (J : Ideal A) (hJ : J.FG) :
    localCohomologyOnModules A J hJ ⋙ DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0 ⟶
      𝟭 (ModuleCat.{u} A) :=
  localCohomologyZeroCounitNat A J hJ ≫
    (DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat.{u} A) 0).hom

public theorem localCohomologyZeroNat_app (J : Ideal A) (hJ : J.FG) (N : ModuleCat.{u} A) :
    (localCohomologyZeroNat A J hJ).app N = localCohomologyZeroToModule A J hJ N :=
  rfl

/-! ### The four towers and the comparison maps into their limits -/

variable (I J : Ideal A) (hJ : J.FG) (D : LocalizationTriangleData.{u, u} A J hJ)
  (M : ModuleCat.{u} A)

/-- The tower `n ↦ Γ(Spec A ∖ V(J), (M/IⁿM)~)` of sections of the adic quotients. -/
public abbrev complementSectionsAdicTower : ℕᵒᵖ ⥤ ModuleCat.{u} A :=
  adicQuotientModuleSystem A I M ⋙ affineComplementSectionsFunctor A J

/-- The map `H⁰_J(M/IⁿM) ⟶ M/IⁿM` of the four-term sequence, along the whole tower. -/
public def adicLocalCohomologyZeroNat :
    Dualizing.adicQuotientLocalCohomologySystem A I J hJ M ⋙
        DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0 ⟶
      adicQuotientModuleSystem A I M :=
  Functor.whiskerLeft (adicQuotientModuleSystem A I M) (localCohomologyZeroNat A J hJ) ≫
    (Functor.rightUnitor (adicQuotientModuleSystem A I M)).hom

/-- The map `M/IⁿM ⟶ Γ(Spec A ∖ V(J), (M/IⁿM)~)` of the four-term sequence, along the whole
tower. -/
public def adicComplementRestrictionNat :
    adicQuotientModuleSystem A I M ⟶ complementSectionsAdicTower A I J M :=
  (Functor.rightUnitor (adicQuotientModuleSystem A I M)).inv ≫
    Functor.whiskerLeft (adicQuotientModuleSystem A I M) (complementRestrictionNat A J hJ D)

/-- The boundary map `Γ(Spec A ∖ V(J), (M/IⁿM)~) ⟶ H¹_J(M/IⁿM)` of the four-term sequence, along
the whole tower. -/
public def adicComplementBoundaryNat :
    complementSectionsAdicTower A I J M ⟶
      Dualizing.adicQuotientLocalCohomologySystem A I J hJ M ⋙
        DerivedCategory.homologyFunctor (ModuleCat.{u} A) 1 :=
  Functor.whiskerLeft (adicQuotientModuleSystem A I M) (complementBoundaryNat A J hJ D)

public theorem adicLocalCohomologyZeroNat_app (n : ℕᵒᵖ) :
    (adicLocalCohomologyZeroNat A I J hJ M).app n =
      localCohomologyZeroToModule A J hJ ((adicQuotientModuleSystem A I M).obj n) :=
  Category.comp_id _

public theorem adicComplementRestrictionNat_app (n : ℕᵒᵖ) :
    (adicComplementRestrictionNat A I J hJ D M).app n =
      (complementRestrictionNat A J hJ D).app ((adicQuotientModuleSystem A I M).obj n) :=
  Category.id_comp _

public theorem adicComplementBoundaryNat_app (n : ℕᵒᵖ) :
    (adicComplementBoundaryNat A I J hJ D M).app n =
      (complementBoundaryNat A J hJ D).app ((adicQuotientModuleSystem A I M).obj n) :=
  rfl

public theorem adicComplementRestrictionNat_app_apply (n : ℕᵒᵖ)
    (x : (adicQuotientModuleSystem A I M).obj n) :
    ConcreteCategory.hom ((adicComplementRestrictionNat A I J hJ D M).app n) x =
      restrictionToComplement D ((adicQuotientModuleSystem A I M).obj n)
        (complementTilde A J ((adicQuotientModuleSystem A I M).obj n)) (Iso.refl _) x := by
  show ConcreteCategory.hom ((𝟙 _ : (adicQuotientModuleSystem A I M).obj n ⟶ _) ≫
    (complementRestrictionNat A J hJ D).app ((adicQuotientModuleSystem A I M).obj n)) x = _
  rw [Category.id_comp]
  exact complementRestrictionNat_app_apply A J hJ D _ x

public theorem adicComplementBoundaryNat_app_apply (n : ℕᵒᵖ)
    (s : (complementSectionsAdicTower A I J M).obj n) :
    ConcreteCategory.hom ((adicComplementBoundaryNat A I J hJ D M).app n) s =
      localizationBoundary D ((adicQuotientModuleSystem A I M).obj n)
        (complementTilde A J ((adicQuotientModuleSystem A I M).obj n)) (Iso.refl _) s :=
  complementBoundaryNat_app_apply A J hJ D _ s

/-- The cone of reductions `Γ(Spec A ∖ V(J), M̃) ⟶ Γ(Spec A ∖ V(J), (M/IⁿM)~)`. -/
public def complementSectionsAdicCone :
    Cone (complementSectionsAdicTower A I J M) :=
  natCone _ ((affineComplementSectionsFunctor A J).obj M)
    (fun n => (affineComplementSectionsFunctor A J).map (Dualizing.adicQuotientProjection A I M n))
    (fun {n m} h => by
      rw [Functor.comp_map, ← (affineComplementSectionsFunctor A J).map_comp,
        Dualizing.adicQuotientProjection_comp_map A I M h])

/-- The canonical map `Γ(Spec A ∖ V(J), M̃) ⟶ lim_n Γ(Spec A ∖ V(J), (M/IⁿM)~)`, the map whose
surjectivity is the comparison clause of Stacks 0DXQ at `i = 0`. -/
public def complementSectionsToLimit :
    (affineComplementSectionsFunctor A J).obj M ⟶ limit (complementSectionsAdicTower A I J M) :=
  limit.lift _ (complementSectionsAdicCone A I J M)

@[reassoc]
public theorem complementSectionsToLimit_π (n : ℕ) :
    complementSectionsToLimit A I J M ≫ limit.π (complementSectionsAdicTower A I J M) (op n) =
      (affineComplementSectionsFunctor A J).map (Dualizing.adicQuotientProjection A I M n) :=
  limit.lift_π _ _

/-- The cone of quotient maps `M ⟶ M/IⁿM`. -/
public def adicQuotientModuleCone : Cone (adicQuotientModuleSystem A I M) :=
  natCone _ M (Dualizing.adicQuotientProjection A I M)
    (fun {_ _} h => Dualizing.adicQuotientProjection_comp_map A I M h)

/-- The canonical map `M ⟶ lim_n M/IⁿM`. -/
public def adicQuotientModuleToLimit : M ⟶ limit (adicQuotientModuleSystem A I M) :=
  limit.lift _ (adicQuotientModuleCone A I M)

@[reassoc]
public theorem adicQuotientModuleToLimit_π (n : ℕ) :
    adicQuotientModuleToLimit A I M ≫ limit.π (adicQuotientModuleSystem A I M) (op n) =
      Dualizing.adicQuotientProjection A I M n :=
  limit.lift_π _ _

/-- **The canonical map `M ⟶ lim_n M/IⁿM` is onto for an `I`-adically complete module.** A
compatible family of classes is an element of Mathlib's `AdicCompletion`, which the completeness
of `M` presents as the class family of a single element. -/
public theorem surjective_adicQuotientModuleToLimit [IsAdicComplete I M] :
    Function.Surjective (ConcreteCategory.hom (adicQuotientModuleToLimit A I M)) := by
  intro z
  have hcompat : ∀ {m n : ℕ} (h : m ≤ n),
      AdicCompletion.transitionMap I M h
          (ConcreteCategory.hom (limit.π (adicQuotientModuleSystem A I M) (op n)) z) =
        ConcreteCategory.hom (limit.π (adicQuotientModuleSystem A I M) (op m)) z := by
    intro m n h
    have hw := limit.w (adicQuotientModuleSystem A I M) (homOfLE h).op
    rw [Dualizing.adicQuotientModuleSystem_map A I M h] at hw
    exact congrArg (fun φ : limit (adicQuotientModuleSystem A I M) ⟶
      (adicQuotientModuleSystem A I M).obj (op m) => ConcreteCategory.hom φ z) hw
  obtain ⟨x, hx⟩ := (AdicCompletion.of_bijective I M).2
    (⟨fun n => ConcreteCategory.hom (limit.π (adicQuotientModuleSystem A I M) (op n)) z,
      fun {m n} h => hcompat h⟩ : AdicCompletion I M)
  refine ⟨x, Concrete.limit_ext _ _ _ fun j => ?_⟩
  obtain ⟨n⟩ := j
  have hxn : (Submodule.Quotient.mk x : M ⧸ (I ^ n • (⊤ : Submodule A M))) =
      ConcreteCategory.hom (limit.π (adicQuotientModuleSystem A I M) (op n)) z :=
    congrFun (congrArg Subtype.val hx) n
  rw [← ConcreteCategory.comp_apply, adicQuotientModuleToLimit_π]
  exact hxn

/-! ### The four-term sequence along the tower, and the chase -/

/-- The composite `H⁰_J(M/IⁿM) ⟶ M/IⁿM ⟶ Γ(Spec A ∖ V(J), (M/IⁿM)~)` of the four-term sequence
vanishes. -/
public theorem adicLocalCohomologyZeroNat_comp_restriction :
    adicLocalCohomologyZeroNat A I J hJ M ≫ adicComplementRestrictionNat A I J hJ D M = 0 := by
  refine NatTrans.ext (funext fun n => ModuleCat.hom_ext (LinearMap.ext fun x => ?_))
  show ConcreteCategory.hom ((adicComplementRestrictionNat A I J hJ D M).app n)
      (ConcreteCategory.hom ((adicLocalCohomologyZeroNat A I J hJ M).app n) x) = 0
  rw [adicComplementRestrictionNat_app_apply, adicLocalCohomologyZeroNat_app]
  exact (exact_localCohomologyZeroToModule_restrictionToComplement D
    ((adicQuotientModuleSystem A I M).obj n) _ (Iso.refl _)).apply_apply_eq_zero x

/-- The composite `M/IⁿM ⟶ Γ(Spec A ∖ V(J), (M/IⁿM)~) ⟶ H¹_J(M/IⁿM)` of the four-term sequence
vanishes. -/
public theorem adicComplementRestriction_comp_boundary :
    adicComplementRestrictionNat A I J hJ D M ≫ adicComplementBoundaryNat A I J hJ D M = 0 := by
  refine NatTrans.ext (funext fun n => ModuleCat.hom_ext (LinearMap.ext fun x => ?_))
  show ConcreteCategory.hom ((adicComplementBoundaryNat A I J hJ D M).app n)
      (ConcreteCategory.hom ((adicComplementRestrictionNat A I J hJ D M).app n) x) = 0
  rw [adicComplementBoundaryNat_app_apply, adicComplementRestrictionNat_app_apply]
  exact (exact_restrictionToComplement_localizationBoundary D
    ((adicQuotientModuleSystem A I M).obj n) _ (Iso.refl _)).apply_apply_eq_zero x

/-- The four-term sequence is exact at `M/IⁿM`, at every index of the tower. -/
public theorem exact_evaluation_adicLocalCohomologyZeroNat (n : ℕᵒᵖ) :
    ((ShortComplex.mk (adicLocalCohomologyZeroNat A I J hJ M)
          (adicComplementRestrictionNat A I J hJ D M)
          (adicLocalCohomologyZeroNat_comp_restriction A I J hJ D M)).map
      ((evaluation ℕᵒᵖ (ModuleCat.{u} A)).obj n)).Exact := by
  rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact]
  exact exact_localCohomologyZeroToModule_restrictionToComplement D _ _ (Iso.refl _)

/-- The four-term sequence is exact at `Γ(Spec A ∖ V(J), (M/IⁿM)~)`, at every index. -/
public theorem exact_evaluation_adicComplementRestrictionNat (n : ℕᵒᵖ) :
    ((ShortComplex.mk (adicComplementRestrictionNat A I J hJ D M)
          (adicComplementBoundaryNat A I J hJ D M)
          (adicComplementRestriction_comp_boundary A I J hJ D M)).map
      ((evaluation ℕᵒᵖ (ModuleCat.{u} A)).obj n)).Exact := by
  rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact]
  exact exact_restrictionToComplement_localizationBoundary D _ _ (Iso.refl _)

variable [IsLocalRing A] [IsNoetherianRing A]

/-- **The limit of the four-term sequences is exact in the middle**, by Stacks 070B: the tower
`n ↦ H⁰_J(M/IⁿM)` of their first terms is Mittag-Leffler when `V(J) ∩ V(I) = {𝔪}`. -/
public theorem exact_lim_adicComplementRestriction_boundary [Module.Finite A M]
    (hV : PrimeSpectrum.zeroLocus (J : Set A) ∩ PrimeSpectrum.zeroLocus (I : Set A) =
      {closedPoint A}) :
    Function.Exact
      (ConcreteCategory.hom (limMap (adicComplementRestrictionNat A I J hJ D M)))
      (ConcreteCategory.hom (limMap (adicComplementBoundaryNat A I J hJ D M))) :=
  (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1
    (ModuleCat.exact_lim_map_of_isMittagLeffler
      (adicLocalCohomologyZeroNat A I J hJ M)
      (adicComplementRestrictionNat A I J hJ D M)
      (adicComplementBoundaryNat A I J hJ D M)
      (adicLocalCohomologyZeroNat_comp_restriction A I J hJ D M)
      (adicComplementRestriction_comp_boundary A I J hJ D M)
      (ShortComplex.exact_of_exact_evaluation _
        (exact_evaluation_adicLocalCohomologyZeroNat A I J hJ D M))
      (ShortComplex.exact_of_exact_evaluation _
        (exact_evaluation_adicComplementRestrictionNat A I J hJ D M))
      (isMittagLeffler_forget_adicQuotientLocalCohomologySystem A I J M hV 0))

omit [IsLocalRing A] [IsNoetherianRing A] in
/-- **The square on the left of the chase**: reducing a section modulo `Iⁿ` after restricting a
module element is restricting the reduction of that element. -/
public theorem complementRestrictionNat_comp_complementSectionsToLimit :
    (complementRestrictionNat A J hJ D).app M ≫ complementSectionsToLimit A I J M =
      adicQuotientModuleToLimit A I M ≫
        limMap (adicComplementRestrictionNat A I J hJ D M) := by
  refine limit.hom_ext fun j => ?_
  obtain ⟨n⟩ := j
  simp only [Category.assoc, complementSectionsToLimit_π, limMap_π,
    adicComplementRestrictionNat_app]
  refine ((complementRestrictionNat A J hJ D).naturality
    (Dualizing.adicQuotientProjection A I M n)).symm.trans ?_
  exact (congrArg (fun φ : M ⟶ (adicQuotientModuleSystem A I M).obj (op n) =>
      φ ≫ (complementRestrictionNat A J hJ D).app
        ((adicQuotientModuleSystem A I M).obj (op n)))
    (adicQuotientModuleToLimit_π A I M n).symm).trans (Category.assoc _ _ _)

omit [IsLocalRing A] [IsNoetherianRing A] in
public theorem complementSectionsToLimit_restrictionToComplement (x : M) :
    ConcreteCategory.hom (complementSectionsToLimit A I J M)
        (restrictionToComplement D M (complementTilde A J M) (Iso.refl _) x) =
      ConcreteCategory.hom (limMap (adicComplementRestrictionNat A I J hJ D M))
        (ConcreteCategory.hom (adicQuotientModuleToLimit A I M) x) :=
  congrArg (fun φ : M ⟶ limit (complementSectionsAdicTower A I J M) =>
      ConcreteCategory.hom φ x)
    (complementRestrictionNat_comp_complementSectionsToLimit A I J hJ D M)

omit [IsLocalRing A] [IsNoetherianRing A] in
/-- **The square on the right of the chase**: the boundary map of the four-term sequence is
natural in the module. -/
public theorem complementBoundaryNat_comp_localCohomologyAdicQuotientToLimit :
    (complementBoundaryNat A J hJ D).app M ≫ localCohomologyAdicQuotientToLimit A I J hJ M 1 =
      complementSectionsToLimit A I J M ≫
        limMap (adicComplementBoundaryNat A I J hJ D M) := by
  refine limit.hom_ext fun j => ?_
  obtain ⟨n⟩ := j
  simp only [Category.assoc, localCohomologyAdicQuotientToLimit_π, limMap_π,
    adicComplementBoundaryNat_app]
  refine ((complementBoundaryNat A J hJ D).naturality
    (Dualizing.adicQuotientProjection A I M n)).symm.trans ?_
  exact (congrArg (fun φ : (affineComplementSectionsFunctor A J).obj M ⟶
      (complementSectionsAdicTower A I J M).obj (op n) =>
      φ ≫ (complementBoundaryNat A J hJ D).app
        ((adicQuotientModuleSystem A I M).obj (op n)))
    (complementSectionsToLimit_π A I J M n).symm).trans (Category.assoc _ _ _)

omit [IsLocalRing A] [IsNoetherianRing A] in
public theorem localCohomologyAdicQuotientToLimit_localizationBoundary
    (s : (affineComplementSectionsFunctor A J).obj M) :
    ConcreteCategory.hom (localCohomologyAdicQuotientToLimit A I J hJ M 1)
        (localizationBoundary D M (complementTilde A J M) (Iso.refl _) s) =
      ConcreteCategory.hom (limMap (adicComplementBoundaryNat A I J hJ D M))
        (ConcreteCategory.hom (complementSectionsToLimit A I J M) s) :=
  congrArg (fun φ : (affineComplementSectionsFunctor A J).obj M ⟶
      limit (Dualizing.adicQuotientLocalCohomologySystem A I J hJ M ⋙
        DerivedCategory.homologyFunctor (ModuleCat.{u} A) 1) =>
      ConcreteCategory.hom φ s)
    (complementBoundaryNat_comp_localCohomologyAdicQuotientToLimit A I J hJ D M)

include D in
/-- **The comparison clause of Stacks 0DXQ at `i = 0`, read on the affine complement
`Spec A ∖ V(J)`.** The canonical map

`Γ(Spec A ∖ V(J), M̃) ⟶ lim_n Γ(Spec A ∖ V(J), (M/IⁿM)~)`

is surjective, provided the canonical map `H¹_J(M) ⟶ lim_n H¹_J(M/IⁿM)` is. The latter is
supplied by Stacks 0DXP together with the pinned form of Stacks 0DXJ, in
`Stacks.Algebraization.surjective_localCohomologyAdicQuotientToLimit`.

This is the diagram chase of `Stacks.LimitComparison.surjective_middle`, applied to the map from
the four-term sequence of `M` to the inverse limit of the four-term sequences of the `M/IⁿM`. -/
public theorem surjective_complementSectionsToLimit [Module.Finite A M] [IsAdicComplete I M]
    (hV : PrimeSpectrum.zeroLocus (J : Set A) ∩ PrimeSpectrum.zeroLocus (I : Set A) =
      {closedPoint A})
    (hcD : Function.Surjective (ConcreteCategory.hom
      (localCohomologyAdicQuotientToLimit A I J hJ M 1))) :
    Function.Surjective (ConcreteCategory.hom (complementSectionsToLimit A I J M)) :=
  Stacks.LimitComparison.surjective_middle _ _ _ _ _ _ _
    (complementSectionsToLimit_restrictionToComplement A I J hJ D M)
    (localCohomologyAdicQuotientToLimit_localizationBoundary A I J hJ D M)
    (localizationBoundary_surjective D M (complementTilde A J M) (Iso.refl _))
    (surjective_adicQuotientModuleToLimit A I M)
    (exact_lim_adicComplementRestriction_boundary A I J hJ D M hV) hcD

end Stacks.Algebraization

end
