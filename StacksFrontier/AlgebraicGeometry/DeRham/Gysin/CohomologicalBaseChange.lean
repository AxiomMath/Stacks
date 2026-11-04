module

public import StacksFrontier.AlgebraicGeometry.DeRham.Gysin.CohomologicalGysinMap
public import StacksFrontier.AlgebraicGeometry.DeRham.Gysin.Transverse
public import StacksFrontier.Topology.Sheaves.RingedSpace.SheafifyOpens

/-!
# Base change of the Gysin map on cohomology

Let

```
Z' → X' → S'
↓h   ↓g    ↓
Z  → X  → S
```

satisfy the assumptions of [Stacks, Tag 0G89], so that the two closed immersions carry the Gysin
maps `γ^p` of [Stacks, Tag 0G86] and the sheaf-level Gysin square commutes. [Stacks, Tag 0G8D]
asserts that the square

```
H^q(Z, Ω^p_{Z/S}) ----γ^{p,q}----→ H^{q+c}(X, Ω^{p+c}_{X/S})
        ↓                                   ↓
H^q(Z', Ω^p_{Z'/S'}) --γ^{p,q}---→ H^{q+c}(X', Ω^{p+c}_{X'/S'})
```

commutes, the horizontal maps being the cohomological Gysin maps of [Stacks, Tag 0G8A] and the
verticals the pullback maps. This file defines the pullback map on cohomology, the ambient objects
the Gysin map of [Stacks, Tag 0G8A] is built from, and the two squares, in the derived category
and on cohomology, out of which the commutativity is assembled.

The cohomology of the closed subscheme is read on the ambient scheme, as `H^q(X, i_*Ω^p_{Z/S})`;
[Stacks, Tag 089W] identifies it with `H^q(Z, Ω^p_{Z/S})`.

## Main definitions

* `CohomologyPullbackComparison`: the two canonical comparisons that the pullback map on
  cohomology is composed of — the map `(G_*ℳ)[-a] ⟶ RG_*(ℳ[-a])` of [Stacks, Tag 01F8] and the
  Leray identification `RΓ(X, RG_*K) ≅ RΓ(X', K)` of [Stacks, Tag 01EZ].
* `derivedPushforwardMap`: the morphism `ℳ[-a] ⟶ RG_*(ℳ'[-a])` of [Stacks, Tag 01F8] attached to
  a `G`-map `ℳ ⟶ G_*ℳ'`.
* `pullbackHgroup`: the pullback map on cohomology attached to a `G`-map `ℳ ⟶ G_*ℳ'`, the arrow
  of [Stacks, Tag 01F9] read on the cohomology groups `Hgroup`.
* `AmbientVanishing`: the vanishing of `ℋ^j_Z(Ω^{p+c}_{X/S})` for `j < c`.
* `ambientLocalCohomology`, `ambientGysinEdge`: the sheaf `i_*ℋ^c_Z(Ω^{p+c}_{X/S})` on `X` and the
  Gysin edge morphism `i_*ℋ^c_Z(Ω^{p+c}_{X/S})[-c] ⟶ Ω^{p+c}_{X/S}`.

## Main results

* `derivedPushforwardMap_paste`: the derived square for a composite `𝒜[-c] ⟶ ℱ` of a Gysin map
  with an edge morphism, pasted from the sheaf-level square for the Gysin map and the square for
  the edge morphism.
* `cohomologyMapOfSingleHom_pullbackHgroup`: a commuting square in the derived category gives a
  commuting square on cohomology.

## References

* [Stacks Project, Tag 0G8D](https://stacks.math.columbia.edu/tag/0G8D)
* [Stacks Project, Tag 0G8A](https://stacks.math.columbia.edu/tag/0G8A)
* [Stacks Project, Tag 0G89](https://stacks.math.columbia.edu/tag/0G89)
* [Stacks Project, Tag 0G86](https://stacks.math.columbia.edu/tag/0G86)
* [Stacks Project, Tag 0G83](https://stacks.math.columbia.edu/tag/0G83)
* [Stacks Project, Tag 0G79](https://stacks.math.columbia.edu/tag/0G79)
* [Stacks Project, Tag 0G78](https://stacks.math.columbia.edu/tag/0G78)
* [Stacks Project, Tag 0G7P](https://stacks.math.columbia.edu/tag/0G7P)
* [Stacks Project, Tag 0G7Q](https://stacks.math.columbia.edu/tag/0G7Q)
* [Stacks Project, Tag 0G70](https://stacks.math.columbia.edu/tag/0G70)
* [Stacks Project, Tag 01F8](https://stacks.math.columbia.edu/tag/01F8)
* [Stacks Project, Tag 01F9](https://stacks.math.columbia.edu/tag/01F9)
* [Stacks Project, Tag 01EZ](https://stacks.math.columbia.edu/tag/01EZ)
* [Stacks Project, Tag 0D5W](https://stacks.math.columbia.edu/tag/0D5W)
* [Stacks Project, Tag 089W](https://stacks.math.columbia.edu/tag/089W)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.SupportedComplexes
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open Stacks.DeRham.CohomologicalGysin

namespace Stacks.DeRham.GysinCohomologyBaseChange

universe u

open DerivedCategory

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] Stacks.Topology.RingedSpaceSheafifyOpens.opensHasSheafifyAddCommGrpCat
  Stacks.Topology.RingedSpaceSheafifyOpens.opensWEqualsLocallyBijectiveAddCommGrpCat

attribute [local instance] Stacks.DeRham.CohomologicalGysin.moduleSheavesHasDerivedCategory

/-! ### Pullback on cohomology -/

section Pullback

/-- **The two canonical comparisons that the pullback map on cohomology is composed of.**  For a
morphism `G : X' ⟶ X` of ringed spaces, the source's pullback map on cohomology attached to a
`G`-map `φ : ℳ ⟶ G_*ℳ'` is `RΓ(X, -)` applied to `ℳ[-a] ⟶ RG_*(ℳ'[-a])`, the morphism
[Stacks, Tag 01F8] builds out of `φ`, followed by the identification
`RΓ(X, RG_*(ℳ'[-a])) = RΓ(X', ℳ'[-a])` of [Stacks, Tag 01EZ]. -/
structure CohomologyPullbackComparison {X X' : RingedSpace.{u, u}} (G : X' ⟶ X) where
  /-- **[Stacks, Tag 01F8]**: the canonical morphism `(G_*ℳ')[-a] ⟶ RG_*(ℳ'[-a])` of `D(𝒪_X)`,
  natural in `ℳ'`, from the degreewise direct image to the derived one. -/
  singleMap (a : ℤ) :
    modulePushforward G ⋙ singleFunctor (RModules X) a ⟶
      singleFunctor (RModules X') a ⋙ derivedPushforward G
  /-- **[Stacks, Tag 01EZ]**: the Leray identification `RΓ(X, RG_*K) ≅ RΓ(X', K)`, as functors
  `D(𝒪_{X'}) ⥤ D(Ab)`. -/
  leray : derivedPushforward G ⋙ derivedGlobalSections X ≅ derivedGlobalSections X'

variable {X X' : RingedSpace.{u, u}} {G : X' ⟶ X}

/-- **The morphism `ℳ[-a] ⟶ RG_*(ℳ'[-a])` of [Stacks, Tag 01F8] attached to a `G`-map**
`φ : ℳ ⟶ G_*ℳ'`: place `φ` in degree `a` and follow it by the comparison
`CohomologyPullbackComparison.singleMap`. -/
def derivedPushforwardMap (P : CohomologyPullbackComparison G) (a : ℤ)
    {M : RModules X} {M' : RModules X'}
    (φ : M ⟶ (modulePushforward G).obj M') :
    (singleFunctor _ a).obj M ⟶ (derivedPushforward G).obj ((singleFunctor _ a).obj M') :=
  (singleFunctor _ a).map φ ≫ (P.singleMap a).app M'

/-- **The pullback map on cohomology** `H^n(X, ℳ) ⟶ H^n(X', ℳ')` attached to a `G`-map
`φ : ℳ ⟶ G_*ℳ'`, for `n = m - a`: apply derived global sections to the morphism
`derivedPushforwardMap` of [Stacks, Tag 01F8], follow it by the Leray identification, take
cohomology in degree `m` and read both ends as cohomology groups through
`cohomologyDerivedSingleIso`. This is the arrow of [Stacks, Tag 01F9]. -/
def pullbackHgroup (P : CohomologyPullbackComparison G) (a m : ℤ) (n : ℕ) (hn : m - a = n)
    {M : RModules X} {M' : RModules X'}
    (φ : M ⟶ (modulePushforward G).obj M') :
    Hgroup (structureSheafRing X) ⊤ n M ⟶
      Hgroup (structureSheafRing X') ⊤ n M' :=
  (cohomologyDerivedSingleIso X M a m n hn).inv ≫
    (DerivedCategory.homologyFunctor AddCommGrpCat.{u} m).map
      ((derivedGlobalSections X).map (derivedPushforwardMap P a φ) ≫
        P.leray.hom.app ((singleFunctor _ a).obj M')) ≫
    (cohomologyDerivedSingleIso X' M' a m n hn).hom

/-- **Pasting the two halves of the derived square.**  Let `γ : 𝒜 ⟶ 𝒯` be a sheaf-level Gysin
map, let `e : 𝒯 ⟶ 𝒯̃` identify its target with the object an edge morphism `E : 𝒯̃[-c] ⟶ ℱ` comes
out of, and likewise on the primed side.  If the sheaf-level square `hsheaf` for `γ` commutes and
the edge morphisms fit into the square `hedge`, then the composite `γ[-c] ≫ E` — which is the
morphism `gysinCohomologyMap` applies cohomology to — fits into the derived square. -/
theorem derivedPushforwardMap_paste (P : CohomologyPullbackComparison G) (c : ℕ)
    {A T Treal F : RModules X} {A' T' Treal' F' : RModules X'}
    (γ : A ⟶ T) (γ' : A' ⟶ T') (e : T ⟶ Treal) (e' : T' ⟶ Treal')
    (φA : A ⟶ (modulePushforward G).obj A') (φT : T ⟶ (modulePushforward G).obj T')
    (φF : F ⟶ (modulePushforward G).obj F')
    (E : (singleFunctor _ (c : ℤ)).obj Treal ⟶ (singleFunctor _ (0 : ℤ)).obj F)
    (E' : (singleFunctor _ (c : ℤ)).obj Treal' ⟶ (singleFunctor _ (0 : ℤ)).obj F')
    (hsheaf : γ ≫ φT = φA ≫ (modulePushforward G).map γ')
    (hedge : (singleFunctor _ (c : ℤ)).map e ≫ E ≫ derivedPushforwardMap P (0 : ℤ) φF
      = derivedPushforwardMap P (c : ℤ) (φT ≫ (modulePushforward G).map e') ≫
        (derivedPushforward G).map E') :
    ((singleFunctor _ (c : ℤ)).map (γ ≫ e) ≫ E) ≫ derivedPushforwardMap P (0 : ℤ) φF
      = derivedPushforwardMap P (c : ℤ) φA ≫
        (derivedPushforward G).map ((singleFunctor _ (c : ℤ)).map (γ' ≫ e') ≫ E') := by
  have hs : (singleFunctor _ (c : ℤ)).map γ ≫ (singleFunctor _ (c : ℤ)).map φT
      = (singleFunctor _ (c : ℤ)).map φA ≫
        (singleFunctor _ (c : ℤ)).map ((modulePushforward G).map γ') := by
    rw [← Functor.map_comp, ← Functor.map_comp, hsheaf]
  have hnat1 := (P.singleMap (c : ℤ)).naturality γ'
  have hnat2 := (P.singleMap (c : ℤ)).naturality e'
  simp only [Functor.comp_map] at hnat1 hnat2
  simp only [derivedPushforwardMap, Functor.map_comp, Category.assoc] at hedge ⊢
  rw [hedge, reassoc_of% hs, reassoc_of% hnat2, reassoc_of% hnat1]

/-- **A commuting square in the derived category gives a commuting square on cohomology.**  For
`Φ : 𝒜[-c] ⟶ ℱ` on `X` and `Φ' : 𝒜'[-c] ⟶ ℱ'` on `X'` compatible with the derived `G`-maps of two
sheaf-level `G`-maps `φA`, `φF`, the maps `cohomologyMapOfSingleHom` they induce commute with the
pullback maps on cohomology. -/
theorem cohomologyMapOfSingleHom_pullbackHgroup (P : CohomologyPullbackComparison G) (c q : ℕ)
    {A F : RModules X} {A' F' : RModules X'}
    (φA : A ⟶ (modulePushforward G).obj A') (φF : F ⟶ (modulePushforward G).obj F')
    (Φ : (singleFunctor _ (c : ℤ)).obj A ⟶ (singleFunctor _ (0 : ℤ)).obj F)
    (Φ' : (singleFunctor _ (c : ℤ)).obj A' ⟶ (singleFunctor _ (0 : ℤ)).obj F')
    (hsq : Φ ≫ derivedPushforwardMap P (0 : ℤ) φF
      = derivedPushforwardMap P (c : ℤ) φA ≫ (derivedPushforward G).map Φ') :
    cohomologyMapOfSingleHom X A F c q Φ ≫
        pullbackHgroup P (0 : ℤ) ((q : ℤ) + (c : ℤ)) (q + c) (by omega) φF
      = pullbackHgroup P (c : ℤ) ((q : ℤ) + (c : ℤ)) q (by omega) φA ≫
        cohomologyMapOfSingleHom X' A' F' c q Φ' := by
  have hnat := P.leray.hom.naturality Φ'
  simp only [Functor.comp_map] at hnat
  have key : (derivedGlobalSections X).map Φ ≫
        ((derivedGlobalSections X).map (derivedPushforwardMap P (0 : ℤ) φF) ≫
          P.leray.hom.app ((singleFunctor _ (0 : ℤ)).obj F'))
      = ((derivedGlobalSections X).map (derivedPushforwardMap P (c : ℤ) φA) ≫
          P.leray.hom.app ((singleFunctor _ (c : ℤ)).obj A')) ≫
        (derivedGlobalSections X').map Φ' := by
    rw [← Category.assoc, ← Functor.map_comp, hsq, Functor.map_comp, Category.assoc, hnat,
      Category.assoc]
  simp only [cohomologyMapOfSingleHom, pullbackHgroup, Category.assoc, Iso.hom_inv_id_assoc]
  rw [← Functor.map_comp_assoc, key, Functor.map_comp_assoc]

end Pullback

/-! ### Base change of the Gysin map on cohomology -/

section Gysin

open Stacks.Gysin AlgebraicGeometry.Scheme.Hom

variable {Z X S : Scheme.{u}}

/-- **The vanishing hypothesis of [Stacks, Tag 0G8A]**: the local cohomology sheaves
`ℋ^j_Z(Ω^{p+c}_{X/S})` vanish in the degrees `j < c`. -/
abbrev AmbientVanishing (π : X ⟶ S) (Zs : Set X.toRingedSpace.carrier) (hZs : IsClosed Zs)
    (c p : ℕ) : Prop :=
  ∀ j : ℤ, j < (c : ℤ) → IsZero (localCohomologySheafOfComplex X.toRingedSpace Zs hZs j
    ((singleFunctor _ (0 : ℤ)).obj (relativeDifferentialForms π ((p : ℤ) + (c : ℤ)))))

/-- **The sheaf `i_*ℋ^c_Z(Ω^{p+c}_{X/S})`, read on `X`**: the target of the sheaf-level Gysin map
in the shape the construction of [Stacks, Tag 0G8A] consumes. -/
abbrev ambientLocalCohomology (π : X ⟶ S) (Zs : Set X.toRingedSpace.carrier) (hZs : IsClosed Zs)
    (c p : ℕ) : RModules X.toRingedSpace :=
  (modulePushforward (closedSubsetInclusion X.toRingedSpace Zs)).obj
    (localCohomologySheafOfComplex X.toRingedSpace Zs hZs (c : ℤ)
      ((singleFunctor _ (0 : ℤ)).obj (relativeDifferentialForms π ((p : ℤ) + (c : ℤ)))))

/-- **The Gysin edge morphism `i_*ℋ^c_Z(Ω^{p+c}_{X/S})[-c] ⟶ Ω^{p+c}_{X/S}`** of
[Stacks, Tag 0G8A] on the ambient relative differential forms, the morphism
`supportedGysinEdge` for `Ω^{p+c}_{X/S}`. -/
abbrev ambientGysinEdge (π : X ⟶ S) (Zs : Set X.toRingedSpace.carrier) (hZs : IsClosed Zs)
    (c p : ℕ) (hvan : AmbientVanishing π Zs hZs c p) :
    (singleFunctor _ (c : ℤ)).obj (ambientLocalCohomology π Zs hZs c p) ⟶
      (singleFunctor _ (0 : ℤ)).obj (relativeDifferentialForms π ((p : ℤ) + (c : ℤ))) :=
  supportedGysinEdge Zs hZs (c : ℤ)
    ((singleFunctor _ (0 : ℤ)).obj (relativeDifferentialForms π ((p : ℤ) + (c : ℤ)))) hvan

end Gysin

end Stacks.DeRham.GysinCohomologyBaseChange

end
