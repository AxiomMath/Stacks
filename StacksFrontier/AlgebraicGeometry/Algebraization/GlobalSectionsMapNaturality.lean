module

public import StacksFrontier.AlgebraicGeometry.Algebraization.CoherentTripleSectionPairClosedFibre
public import StacksFrontier.AlgebraicGeometry.Algebraization.CoherentTripleTriviality
public import StacksFrontier.AlgebraicGeometry.Algebraization.CoherentTripleZeroSupport

import all StacksFrontier.AlgebraicGeometry.Algebraization.CoherentTripleInvertible

/-!
# Naturality of the global-sections map of a coherent triple

Let `A` be a local ring, let `f ∈ A`, let `U` be the punctured spectrum of `A`, let `X₀` be the
closed fibre `Spec(A/fA)` and let `U₀` be the punctured closed fibre. For a coherent triple `T`
for `(A, f)` the map `Stacks.Algebraization.globalSectionsMap A f T` carries a global section of
the punctured-spectrum member `T.F` to its restriction to `U₀`, read through the triple's
identification as a global section of `j₀^* T.F₀`, where `j₀ : U₀ ⟶ X₀` is the inclusion. This
file shows that the map is natural in the triple: a morphism of coherent triples `T ⟶ S` induces
a commuting square

```
Γ(T.F, ⊤)       --Γ(φ.onPunctured)-->       Γ(S.F, ⊤)
   |  globalSectionsMap A f T                  |  globalSectionsMap A f S
Γ(j₀^* T.F₀, ⊤) --Γ(j₀^* φ.onClosedFibre)--> Γ(j₀^* S.F₀, ⊤)
```

of `A`-modules. The horizontal maps are the maps on global sections of the two members of the
morphism; they are `A`-linear for the module structures the two structure morphisms induce, and
this file packages them as `Stacks.Algebraization.puncturedSectionsMap` and
`Stacks.Algebraization.puncturedClosedFibreSectionsMap`.

On the `U₀` side of the square: for an invertible module `F₀` on the closed fibre and
`depth(A) ≥ 3`, the global sections of `j₀^* F₀` are `A/fA` as an `A`-module, hence a finite
`A`-module, and their depth is that of `A/fA`.

## Main definitions

* `Stacks.Algebraization.sectionsMapOfScalars`: the map on global sections of a morphism of
  modules on a scheme `X`, as an `A`-linear map for the module structures a ring map
  `A →+* Γ(X, ⊤)` induces.
* `Stacks.Algebraization.puncturedSectionsMap` and
  `Stacks.Algebraization.puncturedClosedFibreSectionsMap`: the map on global sections of a
  morphism of modules on the punctured spectrum, resp. on the punctured closed fibre, as an
  `A`-linear map for the module structures of
  `Stacks.Algebraization.puncturedSectionsModule` and
  `Stacks.Algebraization.puncturedClosedFibreSectionsModule`.

## Main results

* `Stacks.Algebraization.globalSectionsMap_naturality` and its pointwise form
  `Stacks.Algebraization.globalSectionsMap_naturality_apply`: **the square above commutes**.
* `Stacks.Algebraization.nonempty_linearEquiv_closedFibreSections`: the global sections of an
  invertible module on the closed fibre are `A/fA` as an `A`-module.
* `Stacks.Algebraization.nonempty_linearEquiv_puncturedClosedFibreSections`: the same for the
  global sections over the punctured closed fibre, when `depth(A) ≥ 3`.
* `Stacks.Algebraization.finite_puncturedClosedFibreSections` and
  `Stacks.Algebraization.two_le_depth_puncturedClosedFibreSections`: those global sections form
  a finite `A`-module, of the same depth as `A/fA`.

## Implementation notes

The two packaging definitions are both instances of one construction,
`Stacks.Algebraization.sectionsMapOfScalars`, which turns a ring map `A →+* Γ(X, ⊤)` and a
morphism of modules on `X` into an `A`-linear map on global sections. The module structures are
supplied by `letI` in the statements rather than declared as instances, following
`Stacks.Algebraization.globalSectionsMap`: the sheaves involved live on two different schemes and
no canonical `A`-action is intended globally.

`AlgebraicGeometry.globalSectionsAsBaseModule` packages the same `A`-module of global sections
differently, as the restriction of scalars of a `ModuleCat` along a morphism `X ⟶ Spec A`, with
`AlgebraicGeometry.globalSectionsMapAsBaseModule` for the induced map. That packaging is not used
here because `Stacks.Algebraization.globalSectionsMap` is stated for the `Module.compHom`
structures on `Γ(F, ⊤)` itself, and the square has to be an equation of maps between exactly
those modules.

Naturality in a composite of morphisms of coherent triples is free: it is
`Stacks.Algebraization.globalSectionsMap_naturality` applied to
`Stacks.Algebraization.CoherentTriple.Hom.comp`, whose two members are the composites of the
members by `Stacks.Algebraization.CoherentTriple.Hom.comp_onPunctured` and
`Stacks.Algebraization.CoherentTriple.Hom.comp_onClosedFibre`. So no separate statement is given
for it.

`Stacks.Algebraization.nonempty_linearEquiv_closedFibreSections` is stated for an arbitrary
invertible module on the closed fibre rather than for the closed-fibre member of a coherent
triple, since the triple plays no part in it.

## References

* [Stacks Project, Tag 0F28](https://stacks.math.columbia.edu/tag/0F28)
* [Stacks Project, Tag 0F2B](https://stacks.math.columbia.edu/tag/0F2B)
* [Stacks Project, Tag 090R](https://stacks.math.columbia.edu/tag/090R)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits IsLocalRing

universe u

namespace Stacks.Algebraization

/-! ### Global sections of a morphism of modules, linearly over the base ring -/

/-- **The map on global sections of a morphism of modules on `X`**, read as a map of `A`-modules
for the module structures that a ring map `q : A →+* Γ(X, ⊤)` induces on both sides. -/
public noncomputable def sectionsMapOfScalars {X : Scheme.{u}} (A : Type u) [CommRing A]
    (q : A →+* Γ(X, ⊤)) {F G : X.Modules} (φ : F ⟶ G) :
    letI := Module.compHom Γ(F, ⊤) q
    letI := Module.compHom Γ(G, ⊤) q
    Γ(F, ⊤) →ₗ[A] Γ(G, ⊤) :=
  letI := Module.compHom Γ(F, ⊤) q
  letI := Module.compHom Γ(G, ⊤) q
  { toFun := φ.app ⊤
    map_add' := map_add _
    map_smul' := fun a x => by
      change φ.app ⊤ (q a • x) = q a • φ.app ⊤ x
      exact Scheme.Modules.Hom.app_smul φ (q a) x }

/-- The map on global sections induced by a morphism of modules is the morphism's own map on
global sections. -/
public theorem sectionsMapOfScalars_apply {X : Scheme.{u}} (A : Type u) [CommRing A]
    (q : A →+* Γ(X, ⊤)) {F G : X.Modules} (φ : F ⟶ G) (x : Γ(F, ⊤)) :
    sectionsMapOfScalars A q φ x = φ.app ⊤ x :=
  rfl

/-- **The map on global sections of a morphism of modules on the punctured spectrum**, as a map
of `A`-modules for the structures of `Stacks.Algebraization.puncturedSectionsModule`. -/
public noncomputable def puncturedSectionsMap (A : Type u) [CommRing A] [IsLocalRing A]
    {F G : (Stacks.Divisors.puncturedSpectrum A).toScheme.Modules} (φ : F ⟶ G) :
    letI := puncturedSectionsModule A F
    letI := puncturedSectionsModule A G
    Γ(F, ⊤) →ₗ[A] Γ(G, ⊤) :=
  sectionsMapOfScalars A (puncturedScalars A) φ

/-- The map on global sections of a morphism of modules on the punctured spectrum is the
morphism's own map on global sections. -/
public theorem puncturedSectionsMap_apply (A : Type u) [CommRing A] [IsLocalRing A]
    {F G : (Stacks.Divisors.puncturedSpectrum A).toScheme.Modules} (φ : F ⟶ G) (x : Γ(F, ⊤)) :
    puncturedSectionsMap A φ x = φ.app ⊤ x :=
  rfl

/-- The identity induces the identity on global sections. -/
public theorem puncturedSectionsMap_id (A : Type u) [CommRing A] [IsLocalRing A]
    (F : (Stacks.Divisors.puncturedSpectrum A).toScheme.Modules) (x : Γ(F, ⊤)) :
    puncturedSectionsMap A (𝟙 F) x = x := by
  rfl

/-- A composite induces the composite on global sections. -/
public theorem puncturedSectionsMap_comp (A : Type u) [CommRing A] [IsLocalRing A]
    {F G H : (Stacks.Divisors.puncturedSpectrum A).toScheme.Modules} (φ : F ⟶ G) (ψ : G ⟶ H)
    (x : Γ(F, ⊤)) :
    puncturedSectionsMap A (φ ≫ ψ) x =
      puncturedSectionsMap A ψ (puncturedSectionsMap A φ x) := by
  rfl

/-- **The map on global sections of a morphism of modules on the punctured closed fibre**, as a
map of `A`-modules for the structures of
`Stacks.Algebraization.puncturedClosedFibreSectionsModule`. -/
public noncomputable def puncturedClosedFibreSectionsMap (A : Type u) [CommRing A]
    [IsLocalRing A] (f : A) {F G : (puncturedClosedFibre A f).toScheme.Modules} (φ : F ⟶ G) :
    letI := puncturedClosedFibreSectionsModule A f F
    letI := puncturedClosedFibreSectionsModule A f G
    Γ(F, ⊤) →ₗ[A] Γ(G, ⊤) :=
  sectionsMapOfScalars A (puncturedClosedFibreScalars A f) φ

/-- The map on global sections of a morphism of modules on the punctured closed fibre is the
morphism's own map on global sections. -/
public theorem puncturedClosedFibreSectionsMap_apply (A : Type u) [CommRing A] [IsLocalRing A]
    (f : A) {F G : (puncturedClosedFibre A f).toScheme.Modules} (φ : F ⟶ G) (x : Γ(F, ⊤)) :
    puncturedClosedFibreSectionsMap A f φ x = φ.app ⊤ x :=
  rfl

/-- The identity induces the identity on global sections. -/
public theorem puncturedClosedFibreSectionsMap_id (A : Type u) [CommRing A] [IsLocalRing A]
    (f : A) (F : (puncturedClosedFibre A f).toScheme.Modules) (x : Γ(F, ⊤)) :
    puncturedClosedFibreSectionsMap A f (𝟙 F) x = x := by
  rfl

/-- A composite induces the composite on global sections. -/
public theorem puncturedClosedFibreSectionsMap_comp (A : Type u) [CommRing A] [IsLocalRing A]
    (f : A) {F G H : (puncturedClosedFibre A f).toScheme.Modules} (φ : F ⟶ G) (ψ : G ⟶ H)
    (x : Γ(F, ⊤)) :
    puncturedClosedFibreSectionsMap A f (φ ≫ ψ) x =
      puncturedClosedFibreSectionsMap A f ψ (puncturedClosedFibreSectionsMap A f φ x) := by
  rfl

/-! ### Naturality of the global-sections map -/

/-- **The global-sections map of a coherent triple is natural in the triple**, pointwise. For a
morphism of coherent triples `φ : T ⟶ S`, restricting a global section of `T.F` to the punctured
closed fibre after applying `φ.onPunctured` is applying `j₀^* φ.onClosedFibre` after restricting
it. -/
public theorem globalSectionsMap_naturality_apply (A : Type u) [CommRing A] [IsLocalRing A]
    (f : A) {T S : CoherentTriple A f} (φ : CoherentTriple.Hom T S) (s : Γ(T.F, ⊤)) :
    globalSectionsMap A f S (puncturedSectionsMap A φ.onPunctured s) =
      puncturedClosedFibreSectionsMap A f
        ((Scheme.Modules.pullback (puncturedClosedFibre A f).ι).map φ.onClosedFibre)
        (globalSectionsMap A f T s) := by
  have h := congrArg (fun a => Scheme.Modules.Hom.app a ⊤
    (pullbackGlobalSections (puncturedClosedFibreRestriction A f) T.F s)) φ.compatible
  simp only [Scheme.Modules.Hom.comp_app, AddCommGrpCat.comp_apply] at h
  rw [puncturedSectionsMap_apply, globalSectionsMap_apply, globalSectionsMap_apply,
    puncturedClosedFibreSectionsMap_apply,
    Stacks.AlgebraicGeometry.IdealOfClosedSubscheme.pullbackGlobalSections_naturality]
  exact h

/-- **The global-sections map of a coherent triple is natural in the triple.** For a morphism of
coherent triples `φ : T ⟶ S` the square

```
Γ(T.F, ⊤)       --Γ(φ.onPunctured)-->       Γ(S.F, ⊤)
   |  globalSectionsMap A f T                  |  globalSectionsMap A f S
Γ(j₀^* T.F₀, ⊤) --Γ(j₀^* φ.onClosedFibre)--> Γ(j₀^* S.F₀, ⊤)
```

of `A`-modules commutes, `j₀` being the inclusion of the punctured closed fibre into the closed
fibre. -/
public theorem globalSectionsMap_naturality (A : Type u) [CommRing A] [IsLocalRing A] (f : A)
    {T S : CoherentTriple A f} (φ : CoherentTriple.Hom T S) :
    letI := puncturedSectionsModule A T.F
    letI := puncturedSectionsModule A S.F
    letI := puncturedClosedFibreSectionsModule A f
      ((Scheme.Modules.pullback (puncturedClosedFibre A f).ι).obj T.F₀)
    letI := puncturedClosedFibreSectionsModule A f
      ((Scheme.Modules.pullback (puncturedClosedFibre A f).ι).obj S.F₀)
    (puncturedClosedFibreSectionsMap A f
          ((Scheme.Modules.pullback (puncturedClosedFibre A f).ι).map φ.onClosedFibre)).comp
        (globalSectionsMap A f T) =
      (globalSectionsMap A f S).comp (puncturedSectionsMap A φ.onPunctured) := by
  let := puncturedSectionsModule A T.F
  let := puncturedSectionsModule A S.F
  let := puncturedClosedFibreSectionsModule A f
    ((Scheme.Modules.pullback (puncturedClosedFibre A f).ι).obj T.F₀)
  let := puncturedClosedFibreSectionsModule A f
    ((Scheme.Modules.pullback (puncturedClosedFibre A f).ι).obj S.F₀)
  exact LinearMap.ext fun s => (globalSectionsMap_naturality_apply A f φ s).symm

/-! ### Global sections of an invertible module on the closed fibre -/

/-- **The global sections of an invertible module on the closed fibre are `A/fA`**, as an
`A`-module, for `f` in the maximal ideal of `A`. -/
public theorem nonempty_linearEquiv_closedFibreSections (A : Type u) [CommRing A] [IsLocalRing A]
    (f : A) (hf : f ∈ maximalIdeal A) (F₀ : (closedFibre A f).Modules)
    [Stacks.Ample.IsInvertibleModule (closedFibre A f) F₀] :
    Nonempty (((ModuleCat.restrictScalars (Ideal.Quotient.mk (Ideal.span {f}))).obj
        ((moduleSpecΓFunctor (R := .of (A ⧸ Ideal.span {f}))).obj F₀)) ≃ₗ[A]
      (A ⧸ Ideal.span {f})) := by
  let := isLocalRing_quotient_span (A := A) (f := f) hf
  obtain ⟨e₀⟩ := nonempty_iso_unitModule_closedFibre hf F₀
  let : Module A ((moduleSpecΓFunctor (R := CommRingCat.of (A ⧸ Ideal.span {f}))).obj F₀) :=
    ((ModuleCat.restrictScalars (Ideal.Quotient.mk (Ideal.span {f}))).obj
      ((moduleSpecΓFunctor (R := CommRingCat.of (A ⧸ Ideal.span {f}))).obj F₀)).isModule
  let : IsScalarTower A (A ⧸ Ideal.span {f})
      ((moduleSpecΓFunctor (R := CommRingCat.of (A ⧸ Ideal.span {f}))).obj F₀) :=
    ⟨fun a b m => by rw [Algebra.smul_def, mul_smul]; rfl⟩
  let eB := ((moduleSpecΓFunctor (R := CommRingCat.of (A ⧸ Ideal.span {f}))).mapIso e₀ ≪≫
    (unitSpecSectionsEquiv (A ⧸ Ideal.span {f})).toModuleIso).toLinearEquiv
  exact ⟨eB.restrictScalars A⟩

/-- **The global sections over the punctured closed fibre of an invertible module on the closed
fibre are `A/fA`**, as an `A`-module, for a nonzerodivisor `f` in the maximal ideal of a Noetherian
local ring `A` with `depth(A) ≥ 3`. -/
public theorem nonempty_linearEquiv_puncturedClosedFibreSections (A : Type u) [CommRing A]
    [IsLocalRing A] [IsNoetherianRing A] (f : A) (hf : f ∈ maximalIdeal A) (hreg : IsRegular f)
    (F₀ : (closedFibre A f).Modules)
    [Stacks.Ample.IsInvertibleModule (closedFibre A f) F₀]
    (hdepth : 3 ≤ Module.depth A (maximalIdeal A) A) :
    letI := puncturedClosedFibreSectionsModule A f
      ((Scheme.Modules.pullback (puncturedClosedFibre A f).ι).obj F₀)
    Nonempty (Γ((Scheme.Modules.pullback (puncturedClosedFibre A f).ι).obj F₀, ⊤) ≃ₗ[A]
      (A ⧸ Ideal.span {f})) := by
  let := puncturedClosedFibreSectionsModule A f
    ((Scheme.Modules.pullback (puncturedClosedFibre A f).ι).obj F₀)
  have hbij : Function.Bijective (closedFibreRestriction A f F₀) :=
    bijective_pullbackGlobalSections_puncturedClosedFibre A f hf hreg F₀ hdepth
  obtain ⟨e⟩ := nonempty_linearEquiv_closedFibreSections A f hf F₀
  exact ⟨(LinearEquiv.ofBijective _ hbij).symm.trans e⟩

/-! ### Finiteness and depth of the global sections over the punctured closed fibre -/

/-- **The global sections over the punctured closed fibre of an invertible module on the closed
fibre form a finite `A`-module**, being `A/fA`. -/
public theorem finite_puncturedClosedFibreSections (A : Type u) [CommRing A] [IsLocalRing A]
    [IsNoetherianRing A] (f : A) (hf : f ∈ maximalIdeal A) (hreg : IsRegular f)
    (F₀ : (closedFibre A f).Modules)
    [Stacks.Ample.IsInvertibleModule (closedFibre A f) F₀]
    (hdepth : 3 ≤ Module.depth A (maximalIdeal A) A) :
    letI := puncturedClosedFibreSectionsModule A f
      ((Scheme.Modules.pullback (puncturedClosedFibre A f).ι).obj F₀)
    Module.Finite A Γ((Scheme.Modules.pullback (puncturedClosedFibre A f).ι).obj F₀, ⊤) := by
  let := puncturedClosedFibreSectionsModule A f
    ((Scheme.Modules.pullback (puncturedClosedFibre A f).ι).obj F₀)
  obtain ⟨e⟩ := nonempty_linearEquiv_puncturedClosedFibreSections A f hf hreg F₀ hdepth
  exact Module.Finite.equiv e.symm

/-- **The global sections over the punctured closed fibre of an invertible module on the closed
fibre have depth at least two over `A`** as soon as `A/fA` does. -/
public theorem two_le_depth_puncturedClosedFibreSections (A : Type u) [CommRing A]
    [IsLocalRing A] [IsNoetherianRing A] (f : A) (hf : f ∈ maximalIdeal A) (hreg : IsRegular f)
    (F₀ : (closedFibre A f).Modules)
    [Stacks.Ample.IsInvertibleModule (closedFibre A f) F₀]
    (hdepth : 3 ≤ Module.depth A (maximalIdeal A) A)
    (hb : 2 ≤ Module.depth A (maximalIdeal A) (A ⧸ Ideal.span {f})) :
    letI := puncturedClosedFibreSectionsModule A f
      ((Scheme.Modules.pullback (puncturedClosedFibre A f).ι).obj F₀)
    2 ≤ Module.depth A (maximalIdeal A)
      Γ((Scheme.Modules.pullback (puncturedClosedFibre A f).ι).obj F₀, ⊤) := by
  let := puncturedClosedFibreSectionsModule A f
    ((Scheme.Modules.pullback (puncturedClosedFibre A f).ι).obj F₀)
  obtain ⟨e⟩ := nonempty_linearEquiv_puncturedClosedFibreSections A f hf hreg F₀ hdepth
  rwa [Module.depth_eq_depth_of_linearEquiv (maximalIdeal A) e]

end Stacks.Algebraization

end
