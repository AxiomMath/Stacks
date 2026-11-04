module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleCounit
public import StacksFrontier.AlgebraicGeometry.Modules.QuasicoherentPullbackScheme
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.SmallEtaleAssociatedModuleBaseChangeComposition

/-!
# Restriction to the small Zariski site commutes with pullback, on quasi-coherent modules

`AlgebraicGeometry.SmallEtale.associatedModuleBaseChangeIso` is the identification
`(r^*𝓕)^a ≅ ε_a^*(𝓕^a)` of **Stacks 03LC (1)** for a morphism `a : X ⟶ Y` of a big étale site,
and `AlgebraicGeometry.SmallEtale.associatedModuleObjBaseChangeIso_comp` says that those
identifications compose.  This file reads that square in the opposite direction, along the right
adjoint `𝒢 ↦ 𝒢|_{X_Zar}` of `𝓕 ↦ 𝓕^a`, on the quasi-coherent modules where the two functors are
mutually inverse:

`r^*(𝒢|_{Y_Zar}) ≅ (ε_a^*𝒢)|_{X_Zar}`

for a quasi-coherent `𝒪`-module `𝒢` on the small étale site of `Y`, together with its
composition law.  This is the comparison that transports a descent datum of quasi-coherent
modules on the small étale sites of the schemes of a family to a descent datum of quasi-coherent
`𝒪`-modules on those schemes, where the effectivity of Stacks 023T can consume it.

Nothing here inverts a functor.  The comparison is built out of the unit and the counit of
`AlgebraicGeometry.SmallEtale.associatedModuleAdjunction`, both of which are isomorphisms in the
situation at hand — the unit at a quasi-coherent `𝒪_X`-module by Stacks 0GN7
(`AlgebraicGeometry.SmallEtale.unitIsoOnQuasicoherent`) and the counit at a quasi-coherent module
on the small étale site by `AlgebraicGeometry.SmallEtale.isIso_counit` — so the comparison is a
named composite of named isomorphisms, and the quasi-inverse of Stacks 03DX (2) is never used.

## Main results

* `AlgebraicGeometry.SmallEtale.isQuasicoherentOnSite_pullback`: **the pullback along `ε_a` of a
  quasi-coherent module on the small étale site of `Y` is quasi-coherent on the small étale site
  of `X`.**
* `AlgebraicGeometry.SmallEtale.restrictModulePullbackObjIso`:
  **`r^*(𝒢|_{Y_Zar}) ≅ (ε_a^*𝒢)|_{X_Zar}`**, for `𝒢` quasi-coherent on the site.
* `AlgebraicGeometry.SmallEtale.associatedModule_map_restrictModulePullbackObjIso_hom`: the
  transpose of that comparison across the adjunction is
  `AlgebraicGeometry.SmallEtale.associatedModuleObjBaseChangeIso` followed by the pullback of the
  counit.  This pins the comparison, and is the only thing the composition law uses about it.
* `AlgebraicGeometry.SmallEtale.restrictModulePullbackObjIso_naturality`: the comparison is
  natural in the module.
* `AlgebraicGeometry.SmallEtale.restrictModulePullbackObjIso_comp`: **the comparisons compose**,
  through `AlgebraicGeometry.Scheme.Modules.pullbackComp` on the modules on the schemes and
  `AlgebraicGeometry.SmallEtale.smallEtalePullbackCompIso` on the small étale sites.

## Implementation notes

The composition law is proved by transposing both sides across
`AlgebraicGeometry.SmallEtale.associatedModuleAdjunction` at `X`, where the transpose of the
comparison is the characterisation above: the transposed identity is then the naturality of
`AlgebraicGeometry.SmallEtale.associatedModuleBaseChangeIso` in the module, the naturality of
`AlgebraicGeometry.SmallEtale.smallEtalePullbackCompIso` in the module, and
`AlgebraicGeometry.SmallEtale.associatedModuleObjBaseChangeIso_comp` itself.  **No associativity
pentagon for `AlgebraicGeometry.SmallEtale.smallEtalePullbackCompIso` is used, and none is
needed**: only two pullbacks are ever contracted at once, and the three-fold contraction that a
cocycle condition reads over a triple fibre product is handled, on the side of the modules on the
schemes, by the pseudofunctor coherence of `AlgebraicGeometry.Scheme.Modules.pseudofunctor`.

No `stacks` attribute is registered.  Stacks 03LC (1) is tagged where
`AlgebraicGeometry.SmallEtale.associatedModuleBaseChangeIso` is built and Stacks 03DX (2) where
its clauses are proved; what is added here is the reading of the first along the right adjoint of
the second, which is a step in the proof of Stacks 04W8 and not a clause of any of them.

## References

* [Stacks Project, Tag 03LC](https://stacks.math.columbia.edu/tag/03LC)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 0GN7](https://stacks.math.columbia.edu/tag/0GN7)
* [Stacks Project, Tag 023T](https://stacks.math.columbia.edu/tag/023T)
* [Stacks Project, Tag 04W8](https://stacks.math.columbia.edu/tag/04W8)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u}) {X Y Z : B.Scheme} (a : X ⟶ Y) (b : Y ⟶ Z)

/-- **The pullback along `ε_a` of a quasi-coherent module on the small étale site of `Y` is
quasi-coherent on the small étale site of `X`.**

The restriction `𝒢|_{Y_Zar}` is quasi-coherent by
`AlgebraicGeometry.SmallEtale.isQuasicoherent_restrictModule`, its pullback along `r` is
quasi-coherent by Stacks 01BG, hence its associated module is quasi-coherent on the site by
Stacks 03DV (2); and `AlgebraicGeometry.SmallEtale.associatedModuleObjBaseChangeIso` followed by
the pullback of the counit identifies that associated module with `ε_a^*𝒢`. -/
public theorem isQuasicoherentOnSite_pullback
    (N : SheafOfModules.{u} (structureSheaf B Y.obj Y.property))
    (hN : N.IsQuasicoherentOnSite) :
    ((SheafOfModules.pullback.{u} (smallEtaleStructureMapRing B a)).obj
      N).IsQuasicoherentOnSite :=
  have h₁ : SheafOfModules.IsQuasicoherent (R := Y.obj.ringCatSheaf)
      ((restrictModule B Y.obj Y.property).obj N) :=
    isQuasicoherent_restrictModule B Y.obj Y.property N hN
  have _h₂ : IsIso ((associatedModuleAdjunction B Y.obj Y.property).counit.app N) :=
    isIso_counit B Y.obj Y.property N hN h₁
  SheafOfModules.IsQuasicoherentOnSite.of_iso
    (associatedModuleObjBaseChangeIso B a ((restrictModule B Y.obj Y.property).obj N) ≪≫
      (SheafOfModules.pullback.{u} (smallEtaleStructureMapRing B a)).mapIso
        (asIso ((associatedModuleAdjunction B Y.obj Y.property).counit.app N)))
    (isQuasicoherentOnSite_associatedModule_of_isQuasicoherent B X.obj X.property _
      (Stacks.Modules.isQuasicoherent_pullback (schemeHom B a) _ h₁))

/-- **Restriction to the small Zariski site commutes with pullback, on a module which is
quasi-coherent on the small étale site.**  For `a : X ⟶ Y` of a big étale site, with `r` the
underlying morphism of schemes and `ε_a` the morphism of ringed sites of Stacks 070R (2), and for
a quasi-coherent `𝒪`-module `𝒢` on the small étale site of `Y`,

`r^*(𝒢|_{Y_Zar}) ≅ (ε_a^*𝒢)|_{X_Zar}`.

It is the unit of `AlgebraicGeometry.SmallEtale.associatedModuleAdjunction` at `r^*(𝒢|_{Y_Zar})`
— an isomorphism, that module being quasi-coherent — followed by the restriction of
`AlgebraicGeometry.SmallEtale.associatedModuleObjBaseChangeIso` and of the pullback of the
counit, which is an isomorphism by `AlgebraicGeometry.SmallEtale.isIso_counit`. -/
public noncomputable def restrictModulePullbackObjIso
    (N : SheafOfModules.{u} (structureSheaf B Y.obj Y.property))
    (hN : N.IsQuasicoherentOnSite) :
    (Scheme.Modules.pullback (schemeHom B a)).obj
        ((restrictModule B Y.obj Y.property).obj N) ≅
      (restrictModule B X.obj X.property).obj
        ((SheafOfModules.pullback.{u} (smallEtaleStructureMapRing B a)).obj N) :=
  have h₁ : SheafOfModules.IsQuasicoherent (R := Y.obj.ringCatSheaf)
      ((restrictModule B Y.obj Y.property).obj N) :=
    isQuasicoherent_restrictModule B Y.obj Y.property N hN
  have _hu : IsIso ((associatedModuleAdjunction B X.obj X.property).unit.app
      ((Scheme.Modules.pullback (schemeHom B a)).obj
        ((restrictModule B Y.obj Y.property).obj N))) :=
    unitIsoOnQuasicoherent B X.obj X.property
      ⟨_, Stacks.Modules.isQuasicoherent_pullback (schemeHom B a) _ h₁⟩
  have _hc : IsIso ((associatedModuleAdjunction B Y.obj Y.property).counit.app N) :=
    isIso_counit B Y.obj Y.property N hN h₁
  asIso ((associatedModuleAdjunction B X.obj X.property).unit.app
      ((Scheme.Modules.pullback (schemeHom B a)).obj
        ((restrictModule B Y.obj Y.property).obj N))) ≪≫
    (restrictModule B X.obj X.property).mapIso
      (associatedModuleObjBaseChangeIso B a ((restrictModule B Y.obj Y.property).obj N) ≪≫
        (SheafOfModules.pullback.{u} (smallEtaleStructureMapRing B a)).mapIso
          (asIso ((associatedModuleAdjunction B Y.obj Y.property).counit.app N)))

/-- **The transpose of `AlgebraicGeometry.SmallEtale.restrictModulePullbackObjIso` across the
associated-module adjunction.**  Taking the associated module of the comparison and following it
with the counit gives `AlgebraicGeometry.SmallEtale.associatedModuleObjBaseChangeIso` followed by
the pullback of the counit.

Since the transposition is a bijection this determines the comparison, and it is the only fact
about it that the composition law below uses. -/
public theorem associatedModule_map_restrictModulePullbackObjIso_hom
    (N : SheafOfModules.{u} (structureSheaf B Y.obj Y.property))
    (hN : N.IsQuasicoherentOnSite) :
    (associatedModule B X.obj X.property).map
          (restrictModulePullbackObjIso B a N hN).hom ≫
        (associatedModuleAdjunction B X.obj X.property).counit.app
          ((SheafOfModules.pullback.{u} (smallEtaleStructureMapRing B a)).obj N) =
      (associatedModuleObjBaseChangeIso B a
            ((restrictModule B Y.obj Y.property).obj N)).hom ≫
        (SheafOfModules.pullback.{u} (smallEtaleStructureMapRing B a)).map
          ((associatedModuleAdjunction B Y.obj Y.property).counit.app N) := by
  rw [show (restrictModulePullbackObjIso B a N hN).hom =
      (associatedModuleAdjunction B X.obj X.property).unit.app
          ((Scheme.Modules.pullback (schemeHom B a)).obj
            ((restrictModule B Y.obj Y.property).obj N)) ≫
        (restrictModule B X.obj X.property).map
          ((associatedModuleObjBaseChangeIso B a
              ((restrictModule B Y.obj Y.property).obj N)).hom ≫
            (SheafOfModules.pullback.{u} (smallEtaleStructureMapRing B a)).map
              ((associatedModuleAdjunction B Y.obj Y.property).counit.app N)) from rfl]
  exact ((associatedModuleAdjunction B X.obj X.property).homEquiv _ _).symm_apply_apply _

/-- `AlgebraicGeometry.SmallEtale.associatedModule_map_restrictModulePullbackObjIso_hom` read as
the value of the inverse transposition, which is the shape in which the composition law below
peels the comparison off a composite. -/
public theorem homEquiv_symm_restrictModulePullbackObjIso_hom
    (N : SheafOfModules.{u} (structureSheaf B Y.obj Y.property))
    (hN : N.IsQuasicoherentOnSite) :
    ((associatedModuleAdjunction B X.obj X.property).homEquiv _ _).symm
          (restrictModulePullbackObjIso B a N hN).hom =
      (associatedModuleObjBaseChangeIso B a
            ((restrictModule B Y.obj Y.property).obj N)).hom ≫
        (SheafOfModules.pullback.{u} (smallEtaleStructureMapRing B a)).map
          ((associatedModuleAdjunction B Y.obj Y.property).counit.app N) := by
  rw [Adjunction.homEquiv_counit]
  exact associatedModule_map_restrictModulePullbackObjIso_hom B a N hN

/-- `AlgebraicGeometry.SmallEtale.associatedModuleObjBaseChangeIso` is natural in the module. -/
private theorem associatedModuleObjBaseChangeIso_naturality
    {M M' : Scheme.Modules Y.obj} (f : M ⟶ M') :
    (associatedModule B X.obj X.property).map ((Scheme.Modules.pullback (schemeHom B a)).map f) ≫
        (associatedModuleObjBaseChangeIso B a M').hom =
      (associatedModuleObjBaseChangeIso B a M).hom ≫
        (SheafOfModules.pullback.{u} (smallEtaleStructureMapRing B a)).map
          ((associatedModule B Y.obj Y.property).map f) :=
  (associatedModuleBaseChangeIso B a).hom.naturality f

/-- **The comparison is natural in the module.**  For a morphism `k : 𝒢 ⟶ 𝒢'` of modules on the
small étale site of `Y`, both quasi-coherent, the comparison intertwines `r^*(k|_{Y_Zar})` with
`(ε_a^*k)|_{X_Zar}`.

As for the composition law, the equality is checked after transposing across the
associated-module adjunction, where it becomes the naturality of
`AlgebraicGeometry.SmallEtale.associatedModuleObjBaseChangeIso` in the module together with the
naturality of the counit. -/
public theorem restrictModulePullbackObjIso_naturality
    {N N' : SheafOfModules.{u} (structureSheaf B Y.obj Y.property)}
    (hN : N.IsQuasicoherentOnSite) (hN' : N'.IsQuasicoherentOnSite) (k : N ⟶ N') :
    (Scheme.Modules.pullback (schemeHom B a)).map
          ((restrictModule B Y.obj Y.property).map k) ≫
        (restrictModulePullbackObjIso B a N' hN').hom =
      (restrictModulePullbackObjIso B a N hN).hom ≫
        (restrictModule B X.obj X.property).map
          ((SheafOfModules.pullback.{u} (smallEtaleStructureMapRing B a)).map k) := by
  refine ((associatedModuleAdjunction B X.obj X.property).homEquiv _ _).symm.injective ?_
  rw [Adjunction.homEquiv_naturality_left_symm,
    homEquiv_symm_restrictModulePullbackObjIso_hom B a N' hN',
    Adjunction.homEquiv_naturality_right_symm,
    homEquiv_symm_restrictModulePullbackObjIso_hom B a N hN]
  have hcounit : (associatedModule B Y.obj Y.property).map
        ((restrictModule B Y.obj Y.property).map k) ≫
      (associatedModuleAdjunction B Y.obj Y.property).counit.app N' =
      (associatedModuleAdjunction B Y.obj Y.property).counit.app N ≫ k :=
    (associatedModuleAdjunction B Y.obj Y.property).counit.naturality k
  rw [reassoc_of% (associatedModuleObjBaseChangeIso_naturality B a
    ((restrictModule B Y.obj Y.property).map k)), ← Functor.map_comp, hcounit,
    Functor.map_comp, Category.assoc]

/-- **The comparisons `r^*(𝒢|_{Y_Zar}) ≅ (ε_a^*𝒢)|_{X_Zar}` compose.**  For `a : X ⟶ Y` and
`b : Y ⟶ Z` of a big étale site and `𝒢` quasi-coherent on the small étale site of `Z`, the
comparison below `b` pulled back along `r_a`, followed by the comparison below `a` and by the
restriction of the contraction of the two pullbacks along the morphisms of ringed sites, is the
contraction of the two pullbacks of modules on the schemes followed by the comparison below
`a ∘ b`.

Both sides are morphisms out of a pullback of a restriction, so the equality is checked after
transposing across the associated-module adjunction at `X`, where
`AlgebraicGeometry.SmallEtale.associatedModule_map_restrictModulePullbackObjIso_hom` turns each
comparison into `AlgebraicGeometry.SmallEtale.associatedModuleObjBaseChangeIso` followed by a
pullback of the counit; what is left is the naturality of that identification and of
`AlgebraicGeometry.SmallEtale.smallEtalePullbackCompIso` in the module, and
`AlgebraicGeometry.SmallEtale.associatedModuleObjBaseChangeIso_comp`. -/
public theorem restrictModulePullbackObjIso_comp
    (M : SheafOfModules.{u} (structureSheaf B Z.obj Z.property))
    (hM : M.IsQuasicoherentOnSite) :
    (Scheme.Modules.pullback (schemeHom B a)).map
          (restrictModulePullbackObjIso B b M hM).hom ≫
        (restrictModulePullbackObjIso B a
          ((SheafOfModules.pullback.{u} (smallEtaleStructureMapRing B b)).obj M)
          (isQuasicoherentOnSite_pullback B b M hM)).hom ≫
        (restrictModule B X.obj X.property).map
          ((smallEtalePullbackCompIso B a b).hom.app M) =
      (Scheme.Modules.pullbackComp (schemeHom B a) (schemeHom B b)).hom.app
          ((restrictModule B Z.obj Z.property).obj M) ≫
        (restrictModulePullbackObjIso B (a ≫ b) M hM).hom := by
  refine ((associatedModuleAdjunction B X.obj X.property).homEquiv _ _).symm.injective ?_
  rw [← Category.assoc ((Scheme.Modules.pullback (schemeHom B a)).map
      (restrictModulePullbackObjIso B b M hM).hom),
    Adjunction.homEquiv_naturality_right_symm, Adjunction.homEquiv_naturality_left_symm,
    homEquiv_symm_restrictModulePullbackObjIso_hom B a _
      (isQuasicoherentOnSite_pullback B b M hM),
    Adjunction.homEquiv_naturality_left_symm, Adjunction.homEquiv_counit,
    associatedModule_map_restrictModulePullbackObjIso_hom B (a ≫ b) M hM]
  have hcomp : (SheafOfModules.pullback.{u} (smallEtaleStructureMapRing B a)).map
        ((SheafOfModules.pullback.{u} (smallEtaleStructureMapRing B b)).map
          ((associatedModuleAdjunction B Z.obj Z.property).counit.app M)) ≫
      (smallEtalePullbackCompIso B a b).hom.app M =
      (smallEtalePullbackCompIso B a b).hom.app
          ((associatedModule B Z.obj Z.property).obj
            ((restrictModule B Z.obj Z.property).obj M)) ≫
        (SheafOfModules.pullback.{u} (smallEtaleStructureMapRing B (a ≫ b))).map
          ((associatedModuleAdjunction B Z.obj Z.property).counit.app M) :=
    (smallEtalePullbackCompIso B a b).hom.naturality
      ((associatedModuleAdjunction B Z.obj Z.property).counit.app M)
  rw [Category.assoc, Category.assoc, reassoc_of% (associatedModuleObjBaseChangeIso_naturality B a
      (restrictModulePullbackObjIso B b M hM).hom), ← Functor.map_comp_assoc,
    associatedModule_map_restrictModulePullbackObjIso_hom B b M hM, Functor.map_comp_assoc,
    hcomp, reassoc_of% (associatedModuleObjBaseChangeIso_comp B a b
      ((restrictModule B Z.obj Z.property).obj M))]

end AlgebraicGeometry.SmallEtale

end
