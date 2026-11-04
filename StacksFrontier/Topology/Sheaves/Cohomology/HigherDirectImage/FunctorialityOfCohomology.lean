module

public import StacksFrontier.Algebra.Homology.DerivedCategory.CochainComplexPlusDerivedUnit
public import StacksFrontier.Topology.Sheaves.Cohomology.HigherDirectImage.DerivedGlobalSectionsMap
public import StacksFrontier.Topology.Sheaves.Cohomology.RecoveryA.DerivedDirectImageComposition
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Functoriality of cohomology along a morphism of ringed spaces

Let `f : (X, 𝒪_X) ⟶ (Y, 𝒪_Y)` be a morphism of ringed spaces, let `𝒢^•` be a bounded below
complex of `𝒪_Y`-modules, let `ℱ^•` be a bounded below complex of `𝒪_X`-modules, and let
`φ : 𝒢^• ⟶ f_* ℱ^•` be a morphism of complexes.  Such a datum induces a canonical morphism

```
𝒢^• ⟶ Rf_*(ℱ^•)
```

of `D⁺(Mod 𝒪_Y)`, functorially in the triple `(𝒢^•, ℱ^•, φ)`: this is [Stacks, Tag 01F8].  It is
`φ` read in the derived category, followed by the unit of the bounded-below right derived functor
of `f_*`, which is the localization of the composite `𝒢^• ⟶ f_* ℱ^• ⟶ f_* ℐ^•` through an
injective resolution `ℱ^• ⟶ ℐ^•` that the source uses.

Taking `H^i` of the arrow `RΓ(Y, 𝒢) ⟶ RΓ(X, ℱ)` of [Stacks, Tag 01F9] attached to an `f`-map
`φ : 𝒢 ⟶ f_* ℱ` between single sheaves of modules gives the induced map on cohomology

```
φ : H^i(Y, 𝒢) ⟶ H^i(X, ℱ)
```

of [Stacks, Tag 01FA], the target carrying its `Γ(Y, 𝒪_Y)`-module structure by restriction of
scalars.

## Main definitions

* `Stacks.Cohomology.toDerivedPushforwardPlus` is the morphism `𝒢^• ⟶ Rf_*(ℱ^•)` of
  [Stacks, Tag 01F8] attached to a morphism of bounded below complexes `φ : 𝒢^• ⟶ f_* ℱ^•`.
* `Stacks.Cohomology.spaceModuleCohomology` and `Stacks.Cohomology.moduleCohomologyAlong` are the
  cohomology functors `H^i(Y, -) = H^i(RΓ(Y, -))` and `H^i(X, -)`, the latter with values
  regarded as `Γ(Y, 𝒪_Y)`-modules.
* `Stacks.Cohomology.moduleCohomologyMap` is the map `H^i(Y, 𝒢) ⟶ H^i(X, ℱ)` of
  [Stacks, Tag 01FA].

## Main results

* `Stacks.Cohomology.toDerivedPushforwardPlus_comp_left` and
  `Stacks.Cohomology.toDerivedPushforwardPlus_comp_right`: the morphism of
  [Stacks, Tag 01F8] is functorial in the triple `(𝒢^•, ℱ^•, φ)`.
* `Stacks.Cohomology.isIso_toDerivedPushforwardPlus`: the morphism attached to an invertible
  `φ` with `ℱ^•` termwise injective is itself invertible, so the construction is not
  degenerate.
* `Stacks.Cohomology.moduleCohomologyMap_comp_left` and
  `Stacks.Cohomology.moduleCohomologyMap_comp_right`: the map on cohomology is functorial in
  the pair `(𝒢, ℱ, φ)` as well.

## Implementation notes

The bounded below complexes are the objects of `CochainComplex.Plus`, their images in `D⁺` are
taken by `DerivedCategory.Plus.Q`, and the termwise pushforward of a bounded below complex is
`CategoryTheory.Functor.mapCochainComplexPlus`.  The unit used is
`CategoryTheory.Functor.mapCochainComplexPlusDerivedUnit`, so the whole content of
[Stacks, Tag 01F8] beyond the degree-zero case is the composition with `Q(φ)` and the two
functoriality statements.

`H^i(Y, 𝒢)` is spelled as `H^i` of the derived global sections of `𝒢[0]`, since the source
introduces the map on cohomology as a consequence of the arrow on derived global sections.

The bounded-below derived category of sheaves of modules is a full subcategory, so the same
morphism admits two definitionally equal but syntactically different spellings of its category
instance, which `rw` and instance search match only one of; the invertibility statement
therefore assembles its witness from the four factors explicitly.

Everything is stated for `RingedSpace.{u, u}` and `SheafOfModules.{u}`, the universe constraint
imposed by Mathlib's adjunction for the pushforward of presheaves of modules.

## References

* [Stacks Project, Tag 01F8](https://stacks.math.columbia.edu/tag/01F8)
* [Stacks Project, Tag 01FA](https://stacks.math.columbia.edu/tag/01FA)
* [Stacks Project, Tag 01F9](https://stacks.math.columbia.edu/tag/01F9)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open RingedSpaceModuleAdjunction

universe u

namespace Stacks.Cohomology

attribute [local instance] HasDerivedCategory.standard

-- As in
-- `StacksFrontier.Topology.Sheaves.Cohomology.HigherDirectImage.DerivedGlobalSectionsMap`:
-- this file mentions `Functor.rightDerivedFunctorPlus` throughout, so the cheap instance that
-- gets pointwise right derivability from `EnoughInjectives` is given precedence over the one
-- that would embark on proving termwise injectivity of an unknown complex.
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

-- Abelianness and enough injectives for sheaves of modules, additivity of the pushforward and
-- additivity of sections over an open: the four facts that make the bounded-below right derived
-- functors below exist.
attribute [local instance] abelianModules enoughInjectivesModules additiveEvaluation

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)

/-! ### The morphism of Stacks 01F8 for bounded below complexes -/

/-- **Stacks 01F8.**  A morphism of complexes `φ : 𝒢^• ⟶ f_* ℱ^•` from a bounded below complex
of `𝒪_Y`-modules to the termwise pushforward of a bounded below complex of `𝒪_X`-modules
induces a canonical morphism `𝒢^• ⟶ Rf_*(ℱ^•)` in `D⁺(Mod 𝒪_Y)`, namely `φ` read in the derived
category followed by the unit of the right derived functor of `f_*`. -/
@[stacks 01F8, ega "0 12.4.8" "(12.4.8.1)"]
noncomputable def toDerivedPushforwardPlus {G : CochainComplex.Plus (Modules Y)}
    {F : CochainComplex.Plus (Modules X)}
    (phi : G ⟶ (pushforward f).mapCochainComplexPlus.obj F) :
    DerivedCategory.Plus.Q.obj G ⟶
      (pushforward f).rightDerivedFunctorPlus.obj (DerivedCategory.Plus.Q.obj F) :=
  DerivedCategory.Plus.Q.map phi ≫
    ((pushforward f).mapCochainComplexPlusDerivedUnit).app F

/-- **Functoriality in the complex downstairs.**  Precomposing the morphism of complexes with
`g : 𝒢'^• ⟶ 𝒢^•` precomposes the morphism of [Stacks, Tag 01F8] with `g` read in the derived
category. -/
@[stacks 01F8]
lemma toDerivedPushforwardPlus_comp_left {G G' : CochainComplex.Plus (Modules Y)}
    {F : CochainComplex.Plus (Modules X)} (g : G' ⟶ G)
    (phi : G ⟶ (pushforward f).mapCochainComplexPlus.obj F) :
    DerivedCategory.Plus.Q.map g ≫ toDerivedPushforwardPlus f phi =
      toDerivedPushforwardPlus f (g ≫ phi) := by
  rw [toDerivedPushforwardPlus, toDerivedPushforwardPlus, Functor.map_comp, Category.assoc]

/-- **Functoriality in the complex upstairs.**  Postcomposing the morphism of complexes with the
termwise pushforward of `k : ℱ^• ⟶ ℱ'^•` postcomposes the morphism of [Stacks, Tag 01F8] with
`Rf_*(k)`. -/
@[stacks 01F8]
lemma toDerivedPushforwardPlus_comp_right {G : CochainComplex.Plus (Modules Y)}
    {F F' : CochainComplex.Plus (Modules X)}
    (phi : G ⟶ (pushforward f).mapCochainComplexPlus.obj F) (k : F ⟶ F') :
    toDerivedPushforwardPlus f phi ≫
        (pushforward f).rightDerivedFunctorPlus.map (DerivedCategory.Plus.Q.map k) =
      toDerivedPushforwardPlus f (phi ≫ (pushforward f).mapCochainComplexPlus.map k) := by
  have h : DerivedCategory.Plus.Q.map ((pushforward f).mapCochainComplexPlus.map k) ≫
        ((pushforward f).mapCochainComplexPlusDerivedUnit).app F' =
      ((pushforward f).mapCochainComplexPlusDerivedUnit).app F ≫
        (pushforward f).rightDerivedFunctorPlus.map (DerivedCategory.Plus.Q.map k) :=
    ((pushforward f).mapCochainComplexPlusDerivedUnit).naturality k
  rw [toDerivedPushforwardPlus, toDerivedPushforwardPlus, Functor.map_comp, Category.assoc,
    ← h, Category.assoc]

/-- **The morphism of [Stacks, Tag 01F8] is not degenerate.**  For a bounded below complex `ℱ^•`
of injective `𝒪_X`-modules and an invertible morphism of complexes `φ : 𝒢^• ⟶ f_* ℱ^•`, the
induced morphism `𝒢^• ⟶ Rf_*(ℱ^•)` is an isomorphism. -/
instance isIso_toDerivedPushforwardPlus {G : CochainComplex.Plus (Modules Y)}
    {F : CochainComplex.Plus (Modules X)} [∀ n : ℤ, Injective (F.obj.X n)]
    (phi : G ⟶ (pushforward f).mapCochainComplexPlus.obj F) [IsIso phi] :
    IsIso (toDerivedPushforwardPlus f phi) := by
  have h1 : IsIso ((pushforward f).rightDerivedFunctorPlusUnit.app
      ((HomotopyCategory.Plus.quotient (Modules X)).obj F)) := inferInstance
  have h2 : IsIso ((DerivedCategory.Plus.quotientCompQhIso (Modules Y)).inv.app
      ((pushforward f).mapCochainComplexPlus.obj F)) := inferInstance
  have h3 : IsIso ((pushforward f).rightDerivedFunctorPlus.map
      ((DerivedCategory.Plus.quotientCompQhIso (Modules X)).hom.app F)) := inferInstance
  have h4 : IsIso (DerivedCategory.Plus.Q.map phi) := inferInstance
  rw [toDerivedPushforwardPlus, Functor.mapCochainComplexPlusDerivedUnit_app]
  exact IsIso.comp_isIso' h4 (IsIso.comp_isIso' h2 (IsIso.comp_isIso' h1 h3))

/-! ### The map on cohomology of Stacks 01FA -/

/-- **Cohomology of a sheaf of modules in degree `i`**: `H^i(Z, -)`, the degree-`i` cohomology
of the derived global sections `RΓ(Z, -)`, with values in modules over `Γ(Z, 𝒪_Z)`. -/
noncomputable def spaceModuleCohomology (Z : RingedSpace.{u, u}) (i : ℤ) :
    Modules Z ⥤ ModuleCat ((ringCatSheaf Z).obj.obj (op ⊤)) :=
  DerivedCategory.Plus.singleFunctor (Modules Z) 0 ⋙ derivedModuleGlobalSections Z ⋙
    DerivedCategory.Plus.homologyFunctor (ModuleCat ((ringCatSheaf Z).obj.obj (op ⊤))) i

/-- **Cohomology of a sheaf of modules on `X` in degree `i`, read over `Y`**: `H^i(X, -)` with
its values regarded as modules over `Γ(Y, 𝒪_Y)` by restriction of scalars along
`f : X ⟶ Y`. -/
noncomputable def moduleCohomologyAlong (i : ℤ) :
    Modules X ⥤ ModuleCat ((ringCatSheaf Y).obj.obj (op ⊤)) :=
  DerivedCategory.Plus.singleFunctor (Modules X) 0 ⋙ derivedModuleGlobalSectionsAlong f ⋙
    DerivedCategory.Plus.homologyFunctor (ModuleCat ((ringCatSheaf Y).obj.obj (op ⊤))) i

/-- **Stacks 01FA.**  An `f`-map `φ : 𝒢 ⟶ f_* ℱ` from an `𝒪_Y`-module `𝒢` to an `𝒪_X`-module
`ℱ` induces the map on cohomology

```
φ : H^i(Y, 𝒢) ⟶ H^i(X, ℱ)
```

for every `i`, the target carrying its `Γ(Y, 𝒪_Y)`-module structure by restriction of scalars.
It is `H^i` applied to the arrow `RΓ(Y, 𝒢) ⟶ RΓ(X, ℱ)` of [Stacks, Tag 01F9]. -/
@[stacks 01FA]
noncomputable def moduleCohomologyMap (i : ℤ) {G : Modules Y} {F : Modules X}
    (phi : G ⟶ (pushforward f).obj F) :
    (spaceModuleCohomology Y i).obj G ⟶ (moduleCohomologyAlong f i).obj F :=
  (DerivedCategory.Plus.homologyFunctor (ModuleCat ((ringCatSheaf Y).obj.obj (op ⊤))) i).map
    (derivedGlobalSectionsMap f phi)

/-- **Functoriality of the map on cohomology in the module downstairs.**  Precomposing the
`f`-map with `g : 𝒢' ⟶ 𝒢` precomposes the map of [Stacks, Tag 01FA] with `H^i(Y, g)`. -/
lemma moduleCohomologyMap_comp_left (i : ℤ) {G G' : Modules Y} {F : Modules X} (g : G' ⟶ G)
    (phi : G ⟶ (pushforward f).obj F) :
    (spaceModuleCohomology Y i).map g ≫ moduleCohomologyMap f i phi =
      moduleCohomologyMap f i (g ≫ phi) := by
  rw [moduleCohomologyMap, moduleCohomologyMap, ← derivedGlobalSectionsMap_comp_left,
    Functor.map_comp]
  rfl

/-- **Functoriality of the map on cohomology in the module upstairs.**  Postcomposing the
`f`-map with `f_*(k)` for `k : ℱ ⟶ ℱ'` postcomposes the map of [Stacks, Tag 01FA] with
`H^i(X, k)`. -/
lemma moduleCohomologyMap_comp_right (i : ℤ) {G : Modules Y} {F F' : Modules X}
    (phi : G ⟶ (pushforward f).obj F) (k : F ⟶ F') :
    moduleCohomologyMap f i phi ≫ (moduleCohomologyAlong f i).map k =
      moduleCohomologyMap f i (phi ≫ (pushforward f).map k) := by
  rw [moduleCohomologyMap, moduleCohomologyMap, ← derivedGlobalSectionsMap_comp_right,
    Functor.map_comp]
  rfl

end Stacks.Cohomology

end
