module

public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.BaseChangeMap
public import StacksFrontier.Topology.Sheaves.Cohomology.SupportedComplexes.SupportedSectionsCanonicalMaps
public import StacksFrontier.AlgebraicGeometry.ClosedImmersion.DerivedPushforwardComparison
public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.ShiftedStructureSheafTensor
public import StacksFrontier.Topology.Sheaves.Cohomology.SupportedComplexes.SupportedSectionsDerivedPullback
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.CompositionUnitCoherence
import StacksCore.Tactic.StacksAttribute

/-!
# Forgetting support commutes with derived pullback

Let `f : (X', 𝒪_{X'}) ⟶ (X, 𝒪_X)` be a morphism of ringed spaces, let `Z ⊆ X` and
`Z' ⊆ X'` be closed subsets and let `f|_{Z'} : (Z', 𝒪_{X'}|_{Z'}) ⟶ (Z, 𝒪_X|_Z)` be a
morphism of ringed spaces making the square with the two inclusions commute. For `K` in
`D(𝒪_X)` the square

```
H^p_Z(X, K) ------> H^p_{Z'}(X', Lf^*K)
    |                      |
    v                      v
H^p(X, K) --------> H^p(X', Lf^*K)
```

commutes, where the verticals forget support, the bottom arrow is pullback along `f` and the
top arrow is pullback along `f|_{Z'}` followed by the canonical map
`L(f|_{Z'})^* R𝓗_Z(K) ⟶ R𝓗_{Z'}(Lf^*K)` of [Stacks, Tag 0G78]. This is
[Stacks, Tag 0G79], whose proof the source omits.

## Main results

* `comp_counit_of_pullbackMate` is the underlying diagram chase, for an abstract pair of
  comparison isomorphisms and an abstract base-change transformation.
* `forgetSupport_pullbackSupportedClass` is [Stacks, Tag 0G79].
* `homEquiv_comp_map_of_transposeCompatible` removes the base-change transformation from the
  hypothesis `hunit` of that chase: when the transformation is a *mate*, as the base-change map
  of [Stacks, Tag 08HY] is, `hunit` is equivalent to a compatibility of the transposes of the
  comparisons with the two composition isomorphisms, in which no right adjoint occurs.
* `shiftedUnitToPushforward` is the comparison `ρ : 𝒪_X[-p] ⟶ i_*𝒪_Z[-p]` in the derived
  category, built as the transpose of `Li^*(𝒪_X[-p]) ≅ 𝒪_Z[-p]`.
* `forgetSupport_pullbackSupportedClass_preimage_shiftedUnit` is [Stacks, Tag 0G79] at the
  canonical corepresenting objects and the canonical comparisons between them, with nothing
  quantified over.

## Implementation notes

**How the groups are presented.** By [Stacks, Tag 0G70] a class in `H^p_Z(X, K)` is a
morphism `𝒪_Z[-p] ⟶ R𝓗_Z(K)` on `Z` and a class in `H^p(X, K)` is a morphism
`𝒪_X[-p] ⟶ K`; the four corepresenting objects and the canonical comparisons between them are
quantified over as `W`, `W'`, `V`, `V'` and `ρ`, `ρ'`, `c`, `d`. Forgetting support is pushing a
class forward from the closed subset — precomposing with `ρ : 𝒪_X[-p] ⟶ i_*𝒪_Z[-p]` and
following with the adjunction map `i_* R𝓗_Z(K) ⟶ K` of [Stacks, Tag 0A3B] — which is the
transpose of the identification `H^p_Z(X, K) = H^p(Z, R𝓗_Z(K))`; pullback on cohomology is
precomposing with the comparison `c`, resp. `d`, and applying the derived pullback.

**Two statements, and what each carries.** `forgetSupport_pullbackSupportedClass` is the
general form: `Z'`, the morphism `g : (Z', 𝒪_{X'}|_{Z'}) ⟶ (Z, 𝒪_X|_Z)` and the commutativity
`sq` of its square are quantified over, the canonical map of [Stacks, Tag 0G78] is the parameter
`t` and the commutative triangle characterizing it is the hypothesis `ht`. Only `sq` is used, so
the statement covers the source's case and any other closed subset over `Z` as well.

`forgetSupport_pullbackSupportedClass_preimage` is that statement at the source's own data:
`Z' = f^{-1}(Z)` is `closedSubsetPreimage`, `g` is `closedSubsetRestriction`, `sq` is
`closedSubsetRestriction_comp_closedSubsetInclusion`, `t` is `supportedPullbackMap` — the
canonical map of [Stacks, Tag 0G78] itself — and `ht` is its `supportedPullbackMap_triangle`.
So `Z'`, `hZ'`, `g`, `sq`, `t` and `ht` all disappear from the statement, which is then about
the map of the source rather than about an arbitrary one.

**What remains carried.** The hypothesis `hunit` is the compatibility of the *canonical
comparisons of the corepresenting objects* with the base-change transformation of
[Stacks, Tag 08HY]: it mentions neither `R𝓗_Z` nor the map of Tag 0G78 nor the adjunction map,
and is the bookkeeping the source performs silently when it writes
`H^p_Z(X, K) = H^p(Z, R𝓗_Z(K))` on both sides of `f`. It is a statement about `ρ`, `ρ'`, `c`,
`d` and the two comparisons of [Stacks, Tag 0E2K] alone, and it is the only hypothesis of the
specialized form beyond the data of a class.

**How `hunit` is discharged.** The base-change map of [Stacks, Tag 08HY] is a mate, so by
`homEquiv_comp_map_of_transposeCompatible` and `hunit_of_derivedPullbackCompatible` the
hypothesis `hunit` is *equivalent* to a compatibility of the four comparisons in which neither
that map, nor `Ri_*`, nor the comparison of [Stacks, Tag 0E2K] occurs: only the derived
pullbacks and the two composition isomorphisms of [Stacks, Tag 0D5S]. Taking the comparisons to
be the canonical ones — `ρ`, `ρ'` the transposes `shiftedUnitToPushforward` of
`Stacks.RingedSpace.derivedPullbackShiftedUnitIso`, and `c`, `d` that isomorphism itself — that
compatibility says the four identifications `Lh^*(𝒪[-p]) ≅ 𝒪[-p]` agree across the square, which
is a pseudofunctoriality of the structure-sheaf comparison of [Stacks, Tag 01CD] with respect to
`Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical` and a statement about
derived pullback alone.

**That pseudofunctoriality is proved, and nothing is assumed.**
`forgetSupport_pullbackSupportedClass_preimage_shiftedUnit` is therefore unconditional: its
binders are the degree `p`, the complex `K` and the class `η`, and no comparison and no
compatibility is quantified over. The pieces live in
`StacksDraft.UnitPullbackComposition`:

* `commShift_derivedPullbackCompComparisonCanonical` is the
  `CategoryTheory.NatTrans.CommShift` for the composition comparison of [Stacks, Tag 0D5S];
* `derivedPullbackCompIsoCanonical_hom_app_singleUnit` is the coherence in degree `0`, where no
  shift occurs;
* `derivedPullbackCompIsoCanonical_hom_app_shiftedUnit` is the coherence in an arbitrary degree
  `p`, the first two assembled;
* `shiftedUnitIso_square` is that coherence read around the square, with the composition
  isomorphism down the left written as
  `derivedPullbackCompIsoCanonical i' f ≪≫ eqToIso (congrArg (derivedPullback ·) sq.symm)`, and
  `shiftedUnitIso_square_left` is the same statement with that composite folded back into
  `Stacks.Cohomology.DerivedBaseChange.derivedPullbackCompIsoLeft gr i' i f sq`, which is the
  spelling this module uses and the one supplied below.

Three earlier claims in this note are obsolete and have been removed: that the development did
not have the pseudofunctoriality, that no coherence of the composition isomorphism with the unit
comparison was stated anywhere, and that the isomorphism carried no
`CategoryTheory.NatTrans.CommShift`. A fourth, that the fold between the two spellings of the
composition isomorphism down the left could not be performed inside the kernel's
per-declaration budget, was also wrong: it can, provided it is not obtained by substituting the
shifted structure sheaf into a lemma whose object is a variable. See the implementation notes of
`StacksFrontier/Topology/Sheaves/Cohomology/DerivedPullback/CompositionUnitCoherence.lean`.

**Two models of pushforward from a closed subset.** The adjunction `i_* ⊣ R𝓗_Z` of
[Stacks, Tag 0A3B] is stated for the functor `(modulePushforward i).mapDerivedCategory` induced
by the exact functor `i_*`, while the base-change transformation is stated for the total right
derived functor `Ri_*`. They are identified by
`Stacks.ClosedImmersion.mapDerivedCategoryIsoTotalRightDerived`, which is [Stacks, Tag 0E2K]
for a closed-subset inclusion, and the composites below pass through it in both directions.

## References

* [Stacks Project, Lemma 20.34.13 (Tag 0G79)](https://stacks.math.columbia.edu/tag/0G79)
* [Stacks Project, Remark 20.34.12 (Tag 0G78)](https://stacks.math.columbia.edu/tag/0G78)
* [Stacks Project, Lemma 20.34.1 (Tag 0A3B)](https://stacks.math.columbia.edu/tag/0A3B)
* [Stacks Project, Lemma 20.34.4 (Tag 0G70)](https://stacks.math.columbia.edu/tag/0G70)
* [Stacks Project, Remark 20.28.3 (Tag 08HY)](https://stacks.math.columbia.edu/tag/08HY)
* [Stacks Project, Tag 0E2K](https://stacks.math.columbia.edu/tag/0E2K)
* [Stacks Project, Tag 0D5S](https://stacks.math.columbia.edu/tag/0D5S)
* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open Stacks.Cohomology.DerivedBaseChange (derivedBaseChangeMap derivedBaseChangeMap_naturality)
open Stacks.ClosedImmersion (mapDerivedCategoryIsoTotalRightDerived)

universe u

namespace Stacks.Cohomology.SupportedComplexes

attribute [local instance] HasDerivedCategory.standard

/-! ### The comparison `ρ` of the corepresenting objects, in the derived category -/

open Stacks.RingedSpace (shiftedUnitObject derivedPullbackShiftedUnitIso)

section ShiftedUnit

/-- Sheafification of abelian-group-valued presheaves on a space, the site of opens being
essentially small. A *local* instance, switched on only in the two sections that mention the
shifted structure sheaf: left on for the diagram chases it enlarges the terms they synthesize
past what the kernel will check. -/
local instance hasSheafifyOpens (T : TopCat.{u}) :
    HasSheafify (Opens.grothendieckTopology T) AddCommGrpCat.{u} :=
  hasSheafifyEssentiallySmallSite _ _

/-- Weak equivalences on a space are the locally bijective maps, the site of opens being
essentially small. Local for the same reason as `hasSheafifyOpens`. -/
local instance wEqualsLocallyBijectiveOpens (T : TopCat.{u}) :
    (Opens.grothendieckTopology T).WEqualsLocallyBijective AddCommGrpCat.{u} :=
  GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall _

variable {X : RingedSpace.{u, u}} (Z : Set X.carrier)
  [PreservesFiniteLimits (modulePushforward (closedSubsetInclusion X Z))]
  [PreservesFiniteColimits (modulePushforward (closedSubsetInclusion X Z))]

/-- **The comparison `ρ : 𝒪_X[-p] ⟶ i_*𝒪_Z[-p]` of the corepresenting objects of
[Stacks, Tag 0G70]**, in the derived category of `𝒪_X`-modules.

The structure-sheaf comparison `SheafOfModules.unitToPushforwardObjUnit` is a morphism of
sheaves of modules and has no derived form on the nose. What replaces it is its transpose: the
derived pullback of a shifted structure sheaf is the shifted structure sheaf, by
`Stacks.RingedSpace.derivedPullbackShiftedUnitIso` — a shift of [Stacks, Tag 01CD] along
[Stacks, Tag 06YJ] — so transposing that identification under the adjunction
`Li^* ⊣ Ri_*` of [Stacks, Tag 079W] gives a map `𝒪_X[-p] ⟶ Ri_*(𝒪_Z[-p])`, and the comparison
of [Stacks, Tag 0E2K] rewrites the target as `i_*(𝒪_Z[-p])`, `i_*` being exact. -/
def shiftedUnitToPushforward (p : ℤ) :
    shiftedUnitObject X p ⟶
      (modulePushforward (closedSubsetInclusion X Z)).mapDerivedCategory.obj
        (shiftedUnitObject (closedSubsetRingedSpace X Z) p) :=
  (derivedAdjunction (closedSubsetInclusion X Z)).homEquiv _ _
      (derivedPullbackShiftedUnitIso (closedSubsetInclusion X Z) p).hom ≫
    (mapDerivedCategoryIsoTotalRightDerived
      (modulePushforward (closedSubsetInclusion X Z))).inv.app _

end ShiftedUnit

/-- **The diagram chase behind [Stacks, Tag 0G79].** Let `cmp : P ≅ RP` and `cmp' : P' ≅ RP'`
be comparison isomorphisms, let `Lf`, `Lg` be functors and let `bc` be a family
`Lf (RP M) ⟶ RP' (Lg M)` natural in `M`. Given `t : Lg N ⟶ N'` through which `bc` factors a
map `e : P N ⟶ K` as in `ht`, and comparisons `ρ`, `ρ'`, `c`, `d` of corepresenting objects
compatible with `bc` as in `hunit`, the square formed by `η ↦ c ≫ Lg η ≫ t`, the two maps
`η ↦ ρ ≫ P η ≫ e` and `θ ↦ ρ' ≫ P' θ ≫ e'`, and `Lf` commutes. -/
theorem comp_counit_of_pullbackMate {A B A' B' : Type*} [Category* A] [Category* B]
    [Category* A'] [Category* B'] {P RP : B ⥤ A} (cmp : P ≅ RP) {P' RP' : B' ⥤ A'}
    (cmp' : P' ≅ RP') {Lf : A ⥤ A'} {Lg : B ⥤ B'}
    (bc : ∀ M : B, Lf.obj (RP.obj M) ⟶ RP'.obj (Lg.obj M))
    (hbc : ∀ {M N : B} (u : M ⟶ N), Lf.map (RP.map u) ≫ bc N = bc M ≫ RP'.map (Lg.map u))
    {K : A} {N : B} {N' : B'} {W : B} {W' : B'} {V : A} {V' : A'}
    (e : P.obj N ⟶ K) (e' : P'.obj N' ⟶ Lf.obj K) (t : Lg.obj N ⟶ N')
    (ht : bc N ≫ cmp'.inv.app (Lg.obj N) ≫ P'.map t ≫ e' =
      Lf.map (cmp.inv.app N) ≫ Lf.map e)
    (c : W' ⟶ Lg.obj W) (d : V' ⟶ Lf.obj V) (ρ : V ⟶ P.obj W) (ρ' : V' ⟶ P'.obj W')
    (hunit : ρ' ≫ P'.map c ≫ cmp'.hom.app (Lg.obj W) =
      d ≫ Lf.map (ρ ≫ cmp.hom.app W) ≫ bc W)
    (η : W ⟶ N) :
    ρ' ≫ P'.map (c ≫ Lg.map η ≫ t) ≫ e' = d ≫ Lf.map (ρ ≫ P.map η ≫ e) := by
  have hunit' : ρ' ≫ P'.map c =
      d ≫ Lf.map (ρ ≫ cmp.hom.app W) ≫ bc W ≫ cmp'.inv.app (Lg.obj W) := by
    have h := congrArg (fun m => m ≫ cmp'.inv.app (Lg.obj W)) hunit
    simpa only [Category.assoc, Iso.hom_inv_id_app, Category.comp_id] using h
  have hinv := (cmp'.inv.naturality (Lg.map η)).symm
  have hcmp := (cmp.hom.naturality η).symm
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% hunit', reassoc_of% hinv, reassoc_of% (hbc η).symm, ht]
  simp only [← Functor.map_comp, Category.assoc]
  rw [reassoc_of% hcmp]
  simp only [Iso.hom_inv_id_app_assoc]

/-- **The hypothesis `hunit` of the diagram chase, with the base-change map eliminated.**

Let `adji : Li ⊣ Ri` and `adji' : Li' ⊣ Ri'` be adjunctions, let `eg : Lf ⋙ Li' ≅ Lc` and
`ef : Li ⋙ Lg ≅ Lc` be two identifications of the same composite, and let `bc` be a family
`Lf (Ri M) ⟶ Ri' (Lg M)` whose transpose under `adji'` is `eg` followed by `ef⁻¹` followed by
`Lg` of the counit of `adji` — that is, `bc` is the *mate* of the square, which is exactly the
adjoint characterization `derivedBaseChangeMap_adjoint` of [Stacks, Tag 08HY].

Then the compatibility of a pair of comparisons of corepresenting objects with `bc` — the left
side of the conclusion, the hypothesis `hunit` of `comp_counit_of_pullbackMate` once the
comparisons are written as the transposes `u`, `u'` of maps out of the left adjoints — is
*equivalent* to `hcompat`, a compatibility in which neither `bc` nor the right adjoints occur:
it is a statement about `u`, `u'`, `c`, `d` and the two composition isomorphisms `eg`, `ef`
alone. Passing `u := adji.homEquiv.symm ρ` loses nothing, `homEquiv` being a bijection. -/
theorem homEquiv_comp_map_of_transposeCompatible {Dx Dz Dx' Dz' : Type*}
    [Category* Dx] [Category* Dz] [Category* Dx'] [Category* Dz']
    {Li : Dx ⥤ Dz} {Ri : Dz ⥤ Dx} (adji : Li ⊣ Ri)
    {Li' : Dx' ⥤ Dz'} {Ri' : Dz' ⥤ Dx'} (adji' : Li' ⊣ Ri')
    {Lf : Dx ⥤ Dx'} {Lg : Dz ⥤ Dz'} {Lc : Dx ⥤ Dz'}
    (eg : Lf ⋙ Li' ≅ Lc) (ef : Li ⋙ Lg ≅ Lc)
    (bc : ∀ M : Dz, Lf.obj (Ri.obj M) ⟶ Ri'.obj (Lg.obj M))
    (hbc : ∀ M : Dz, (adji'.homEquiv (Lf.obj (Ri.obj M)) (Lg.obj M)).symm (bc M) =
      eg.hom.app (Ri.obj M) ≫ ef.inv.app (Ri.obj M) ≫ Lg.map (adji.counit.app M))
    {V : Dx} {V' : Dx'} {W : Dz} {W' : Dz'}
    (u : Li.obj V ⟶ W) (u' : Li'.obj V' ⟶ W')
    (c : W' ⟶ Lg.obj W) (d : V' ⟶ Lf.obj V)
    (hcompat : Li'.map d ≫ eg.hom.app V ≫ ef.inv.app V ≫ Lg.map u = u' ≫ c) :
    adji'.homEquiv V' W' u' ≫ Ri'.map c =
      d ≫ Lf.map (adji.homEquiv V W u) ≫ bc W := by
  apply (adji'.homEquiv V' (Lg.obj W)).symm.injective
  rw [adji'.homEquiv_naturality_right_symm, Equiv.symm_apply_apply,
    adji'.homEquiv_naturality_left_symm, adji'.homEquiv_naturality_left_symm, hbc, ← hcompat]
  have hu : Li.map (adji.homEquiv V W u) ≫ adji.counit.app W = u := by
    simpa only [Adjunction.homEquiv_counit] using (adji.homEquiv V W).symm_apply_apply u
  have h₁ := eg.hom.naturality (adji.homEquiv V W u)
  have h₂ := ef.inv.naturality (adji.homEquiv V W u)
  simp only [Functor.comp_map] at h₁ h₂
  rw [reassoc_of% h₁, reassoc_of% h₂, ← Functor.map_comp, hu]

variable {X' X : RingedSpace.{u, u}} (f : X' ⟶ X)
  (Z : Set X.carrier) (hZ : IsClosed Z) (Z' : Set X'.carrier) (hZ' : IsClosed Z')
  (g : closedSubsetRingedSpace X' Z' ⟶ closedSubsetRingedSpace X Z)
  (sq : g ≫ closedSubsetInclusion X Z = closedSubsetInclusion X' Z' ≫ f)

variable [PreservesFiniteLimits (modulePushforward (closedSubsetInclusion X Z))]
  [PreservesFiniteColimits (modulePushforward (closedSubsetInclusion X Z))]
  [PreservesFiniteLimits (modulePushforward (closedSubsetInclusion X' Z'))]
  [PreservesFiniteColimits (modulePushforward (closedSubsetInclusion X' Z'))]

/-- **The hypothesis `hunit` of [Stacks, Tag 0G79], with the base-change transformation of
[Stacks, Tag 08HY] eliminated.**

Write the two comparisons of corepresenting objects as the transposes of maps out of the derived
pullbacks: `ρ = Rℋ`-side transpose of `u : Li^*V ⟶ W` and `ρ' = ` transpose of
`u' : Li'^*V' ⟶ W'`, read through the comparison of [Stacks, Tag 0E2K]. Since
`Adjunction.homEquiv` is a bijection and that comparison is an isomorphism, every `ρ`, `ρ'` is
of this form, for a unique `u`, `u'`.

In that presentation `hunit` holds as soon as `u`, `u'`, `c` and `d` are compatible with the
two composition isomorphisms of [Stacks, Tag 0D5S] for the square — the hypothesis `hcompat`,
in which the base-change transformation, the two right adjoints `Ri_*`, `Ri'_*` and the
comparison of [Stacks, Tag 0E2K] no longer appear. It says precisely that the two routes

`Li'^*Lf^*V ⟶ L(f|_{Z'} ≫ i)^*V ⟶ Lg^*Li^*V ⟶ Lg^*W`  and  `Li'^*V' ⟶ W' ⟶ Lg^*W`

through `d` and through `u'` agree, i.e. that the four comparisons of the corepresenting
objects are pseudonatural for the square. -/
theorem hunit_of_derivedPullbackCompatible
    {V : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))}
    {V' : DerivedCategory (SheafOfModules.{u} (structureSheafRing X'))}
    {W : DerivedCategory (SheafOfModules.{u}
      (structureSheafRing (closedSubsetRingedSpace X Z)))}
    {W' : DerivedCategory (SheafOfModules.{u}
      (structureSheafRing (closedSubsetRingedSpace X' Z')))}
    (u : (derivedPullback (closedSubsetInclusion X Z)).obj V ⟶ W)
    (u' : (derivedPullback (closedSubsetInclusion X' Z')).obj V' ⟶ W')
    (c : W' ⟶ (derivedPullback g).obj W) (d : V' ⟶ (derivedPullback f).obj V)
    (hcompat : (derivedPullback (closedSubsetInclusion X' Z')).map d ≫
          (Stacks.Cohomology.DerivedBaseChange.derivedPullbackCompIsoLeft g
            (closedSubsetInclusion X' Z') (closedSubsetInclusion X Z) f sq).hom.app V ≫
          (Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical g
            (closedSubsetInclusion X Z)).inv.app V ≫
          (derivedPullback g).map u =
        u' ≫ c) :
    ((derivedAdjunction (closedSubsetInclusion X' Z')).homEquiv V' W' u' ≫
          (mapDerivedCategoryIsoTotalRightDerived
            (modulePushforward (closedSubsetInclusion X' Z'))).inv.app W') ≫
        (modulePushforward (closedSubsetInclusion X' Z')).mapDerivedCategory.map c ≫
          (mapDerivedCategoryIsoTotalRightDerived
            (modulePushforward (closedSubsetInclusion X' Z'))).hom.app
              ((derivedPullback g).obj W) =
      d ≫ (derivedPullback f).map
          (((derivedAdjunction (closedSubsetInclusion X Z)).homEquiv V W u ≫
              (mapDerivedCategoryIsoTotalRightDerived
                (modulePushforward (closedSubsetInclusion X Z))).inv.app W) ≫
            (mapDerivedCategoryIsoTotalRightDerived
              (modulePushforward (closedSubsetInclusion X Z))).hom.app W) ≫
        derivedBaseChangeMap g (closedSubsetInclusion X' Z') (closedSubsetInclusion X Z) f sq
          W := by
  have hnat := ((mapDerivedCategoryIsoTotalRightDerived
    (modulePushforward (closedSubsetInclusion X' Z'))).inv.naturality c).symm
  simp only [Category.assoc, Iso.inv_hom_id_app, Category.comp_id]
  rw [reassoc_of% hnat]
  simp only [Iso.inv_hom_id_app, Category.comp_id]
  exact homEquiv_comp_map_of_transposeCompatible
    (derivedAdjunction (closedSubsetInclusion X Z))
    (derivedAdjunction (closedSubsetInclusion X' Z'))
    (Stacks.Cohomology.DerivedBaseChange.derivedPullbackCompIsoLeft g
      (closedSubsetInclusion X' Z') (closedSubsetInclusion X Z) f sq)
    (Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical g
      (closedSubsetInclusion X Z))
    (derivedBaseChangeMap g (closedSubsetInclusion X' Z') (closedSubsetInclusion X Z) f sq)
    (fun M => Stacks.Cohomology.DerivedBaseChange.derivedBaseChangeMap_adjoint g
      (closedSubsetInclusion X' Z') (closedSubsetInclusion X Z) f sq M)
    u u' c d hcompat

/-- **The forget-support square for an arbitrary map out of the pulled-back local cohomology.**
Let `t : L(f|_{Z'})^* R𝓗_Z(K) ⟶ R𝓗_{Z'}(Lf^*K)` be a map whose composite with the adjunction
map satisfies the triangle `ht` over the base-change transformation of [Stacks, Tag 08HY], and
let the four corepresenting objects and their comparisons satisfy the compatibility `hunit` with
that transformation.  For `K` in `D(𝒪_X)` the square

```
H^p_Z(X, K) ------> H^p_{Z'}(X', Lf^*K)
    |                      |
    v                      v
H^p(X, K) --------> H^p(X', Lf^*K)
```

commutes: a class `η : 𝒪_Z[-p] ⟶ R𝓗_Z(K)` pulled back along `f|_{Z'}`, pushed through `t` and
then stripped of its support agrees with `η` stripped of its support and then pulled back along
`f`.  The statement of [Stacks, Tag 0G79] is
`forgetSupport_pullbackSupportedClass_preimage_shiftedUnit`. -/
theorem forgetSupport_pullbackSupportedClass
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing X)))
    (t : (derivedPullback g).obj ((derivedSupportedSectionsOnClosed X Z hZ).obj K) ⟶
      (derivedSupportedSectionsOnClosed X' Z' hZ').obj ((derivedPullback f).obj K))
    (ht : derivedBaseChangeMap g (closedSubsetInclusion X' Z') (closedSubsetInclusion X Z) f sq
            ((derivedSupportedSectionsOnClosed X Z hZ).obj K) ≫
          (mapDerivedCategoryIsoTotalRightDerived
            (modulePushforward (closedSubsetInclusion X' Z'))).inv.app
              ((derivedPullback g).obj ((derivedSupportedSectionsOnClosed X Z hZ).obj K)) ≫
          (modulePushforward (closedSubsetInclusion X' Z')).mapDerivedCategory.map t ≫
          (derivedPushforwardAdjunction X' Z' hZ').counit.app ((derivedPullback f).obj K) =
        (derivedPullback f).map ((mapDerivedCategoryIsoTotalRightDerived
            (modulePushforward (closedSubsetInclusion X Z))).inv.app
              ((derivedSupportedSectionsOnClosed X Z hZ).obj K)) ≫
          (derivedPullback f).map ((derivedPushforwardAdjunction X Z hZ).counit.app K))
    {V : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))}
    {V' : DerivedCategory (SheafOfModules.{u} (structureSheafRing X'))}
    {W : DerivedCategory (SheafOfModules.{u} (structureSheafRing (closedSubsetRingedSpace X Z)))}
    {W' : DerivedCategory (SheafOfModules.{u} (structureSheafRing (closedSubsetRingedSpace X' Z')))}
    (c : W' ⟶ (derivedPullback g).obj W) (d : V' ⟶ (derivedPullback f).obj V)
    (ρ : V ⟶ (modulePushforward (closedSubsetInclusion X Z)).mapDerivedCategory.obj W)
    (ρ' : V' ⟶ (modulePushforward (closedSubsetInclusion X' Z')).mapDerivedCategory.obj W')
    (hunit : ρ' ≫ (modulePushforward (closedSubsetInclusion X' Z')).mapDerivedCategory.map c ≫
          (mapDerivedCategoryIsoTotalRightDerived
            (modulePushforward (closedSubsetInclusion X' Z'))).hom.app
              ((derivedPullback g).obj W) =
        d ≫ (derivedPullback f).map (ρ ≫ (mapDerivedCategoryIsoTotalRightDerived
            (modulePushforward (closedSubsetInclusion X Z))).hom.app W) ≫
          derivedBaseChangeMap g (closedSubsetInclusion X' Z') (closedSubsetInclusion X Z) f sq W)
    (η : W ⟶ (derivedSupportedSectionsOnClosed X Z hZ).obj K) :
    ρ' ≫ (modulePushforward (closedSubsetInclusion X' Z')).mapDerivedCategory.map
          (c ≫ (derivedPullback g).map η ≫ t) ≫
        (derivedPushforwardAdjunction X' Z' hZ').counit.app ((derivedPullback f).obj K) =
      d ≫ (derivedPullback f).map (ρ ≫
        (modulePushforward (closedSubsetInclusion X Z)).mapDerivedCategory.map η ≫
        (derivedPushforwardAdjunction X Z hZ).counit.app K) :=
  comp_counit_of_pullbackMate
    (mapDerivedCategoryIsoTotalRightDerived (modulePushforward (closedSubsetInclusion X Z)))
    (mapDerivedCategoryIsoTotalRightDerived (modulePushforward (closedSubsetInclusion X' Z')))
    (derivedBaseChangeMap g (closedSubsetInclusion X' Z') (closedSubsetInclusion X Z) f sq)
    (fun u => derivedBaseChangeMap_naturality g (closedSubsetInclusion X' Z')
      (closedSubsetInclusion X Z) f sq u)
    ((derivedPushforwardAdjunction X Z hZ).counit.app K)
    ((derivedPushforwardAdjunction X' Z' hZ').counit.app ((derivedPullback f).obj K))
    t ht c d ρ ρ' hunit η

/-! ### Tag 0G79 at the preimage, for the canonical map of Tag 0G78 -/

section Preimage

variable [PreservesFiniteLimits
    (modulePushforward (closedSubsetInclusion X' (closedSubsetPreimage f Z)))]
  [PreservesFiniteColimits
    (modulePushforward (closedSubsetInclusion X' (closedSubsetPreimage f Z)))]

/-- **The forget-support square for the canonical map of [Stacks, Tag 0G78], at arbitrary
corepresenting objects.**  Let `Z' = f^{-1}(Z)` and let the four corepresenting objects and their
comparisons satisfy the compatibility `hunit` with the base-change transformation of
[Stacks, Tag 08HY].  For `K` in `D(𝒪_X)` the square

```
H^p_Z(X, K) ------> H^p_{Z'}(X', Lf^*K)
    |                      |
    v                      v
H^p(X, K) --------> H^p(X', Lf^*K)
```

commutes: a class `η : 𝒪_Z[-p] ⟶ R𝓗_Z(K)` pulled back along `f|_{Z'}`, pushed through
`supportedPullbackMap` and then stripped of its support agrees with `η` stripped of its support
and then pulled back along `f`.  This is `forgetSupport_pullbackSupportedClass` with `t` and
`ht` supplied by `supportedPullbackMap` and `supportedPullbackMap_triangle`.  The statement of
[Stacks, Tag 0G79] is `forgetSupport_pullbackSupportedClass_preimage_shiftedUnit`. -/
theorem forgetSupport_pullbackSupportedClass_preimage
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing X)))
    {V : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))}
    {V' : DerivedCategory (SheafOfModules.{u} (structureSheafRing X'))}
    {W : DerivedCategory (SheafOfModules.{u}
      (structureSheafRing (closedSubsetRingedSpace X Z)))}
    {W' : DerivedCategory (SheafOfModules.{u} (structureSheafRing
      (closedSubsetRingedSpace X' (closedSubsetPreimage f Z))))}
    (c : W' ⟶ (derivedPullback (closedSubsetRestriction f Z)).obj W)
    (d : V' ⟶ (derivedPullback f).obj V)
    (ρ : V ⟶ (modulePushforward (closedSubsetInclusion X Z)).mapDerivedCategory.obj W)
    (ρ' : V' ⟶ (modulePushforward
      (closedSubsetInclusion X' (closedSubsetPreimage f Z))).mapDerivedCategory.obj W')
    (hunit : ρ' ≫ (modulePushforward
            (closedSubsetInclusion X' (closedSubsetPreimage f Z))).mapDerivedCategory.map c ≫
          (mapDerivedCategoryIsoTotalRightDerived (modulePushforward
            (closedSubsetInclusion X' (closedSubsetPreimage f Z)))).hom.app
              ((derivedPullback (closedSubsetRestriction f Z)).obj W) =
        d ≫ (derivedPullback f).map (ρ ≫ (mapDerivedCategoryIsoTotalRightDerived
            (modulePushforward (closedSubsetInclusion X Z))).hom.app W) ≫
          supportedPullbackBaseChangeMap f Z W)
    (η : W ⟶ (derivedSupportedSectionsOnClosed X Z hZ).obj K) :
    ρ' ≫ (modulePushforward
          (closedSubsetInclusion X' (closedSubsetPreimage f Z))).mapDerivedCategory.map
          (c ≫ (derivedPullback (closedSubsetRestriction f Z)).map η ≫
            supportedPullbackMap f Z hZ (isClosed_closedSubsetPreimage f Z hZ) K) ≫
        (derivedPushforwardAdjunction X' (closedSubsetPreimage f Z)
            (isClosed_closedSubsetPreimage f Z hZ)).counit.app ((derivedPullback f).obj K) =
      d ≫ (derivedPullback f).map (ρ ≫
        (modulePushforward (closedSubsetInclusion X Z)).mapDerivedCategory.map η ≫
        (derivedPushforwardAdjunction X Z hZ).counit.app K) :=
  forgetSupport_pullbackSupportedClass f Z hZ (closedSubsetPreimage f Z)
    (isClosed_closedSubsetPreimage f Z hZ) (closedSubsetRestriction f Z)
    (closedSubsetRestriction_comp_closedSubsetInclusion f Z) K
    (supportedPullbackMap f Z hZ (isClosed_closedSubsetPreimage f Z hZ) K)
    (supportedPullbackMap_triangle f Z hZ (isClosed_closedSubsetPreimage f Z hZ) K)
    c d ρ ρ' hunit η

section CanonicalComparisons

attribute [local instance] hasSheafifyOpens wEqualsLocallyBijectiveOpens

/-- **Stacks Project, Tag 0G79, at the canonical corepresenting objects.** The four groups are
corepresented by the shifted structure sheaves of [Stacks, Tag 0G70] — `𝒪_X[-p]`, `𝒪_{X'}[-p]`,
`𝒪_Z[-p]`, `𝒪_{Z'}[-p]` with `Z' = f^{-1}(Z)` — and the four comparisons between them are the
canonical ones: `ρ`, `ρ'` are `shiftedUnitToPushforward`, and `c`, `d` are the identifications
`Lf^*(𝒪_X[-p]) ≅ 𝒪_{X'}[-p]` of `Stacks.RingedSpace.derivedPullbackShiftedUnitIso`.

Those four identifications agree across the square — that is the
*pseudofunctoriality of the structure-sheaf comparison* of [Stacks, Tag 01CD] with respect to
the composition isomorphism of [Stacks, Tag 0D5S], in which no derived pushforward, no
base-change transformation of [Stacks, Tag 08HY], no `R𝓗_Z` and no adjunction map occur. It is
proved in degree `0`
(`StacksDraft.UnitPullbackComposition.derivedPullbackCompIsoCanonical_hom_app_singleUnit`), in
an arbitrary degree `p`
(`StacksDraft.UnitPullbackComposition.derivedPullbackCompIsoCanonical_hom_app_shiftedUnit`,
which also needed the first `CategoryTheory.NatTrans.CommShift` for the composition comparison
of [Stacks, Tag 0D5S],
`StacksDraft.UnitPullbackComposition.commShift_derivedPullbackCompComparisonCanonical`), and
around the square in the spelling this statement needs
(`StacksDraft.UnitPullbackComposition.shiftedUnitIso_square_left`), which is what is supplied
below. -/
@[stacks 0G79 "the commuting square for the canonical map of Tag 0G78 itself, at the canonical \
  corepresenting objects: the four groups are corepresented by the shifted structure sheaves of \
  Tag 0G70, the four comparisons between them are the canonical ones, and their agreement across \
  the square -- the pseudofunctoriality of the structure-sheaf comparison of Tag 01CD with \
  respect to the composition isomorphism of derived pullbacks of Tag 0D5S -- is \
  StacksDraft.UnitPullbackComposition.shiftedUnitIso_square_left. The binders are the degree p, \
  the complex K and the class eta, which are the data of a class in H^p_Z(X, K)"]
theorem forgetSupport_pullbackSupportedClass_preimage_shiftedUnit (p : ℤ)
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing X)))
    (η : shiftedUnitObject (closedSubsetRingedSpace X Z) p ⟶
      (derivedSupportedSectionsOnClosed X Z hZ).obj K) :
    shiftedUnitToPushforward (X := X') (closedSubsetPreimage f Z) p ≫
        (modulePushforward
            (closedSubsetInclusion X' (closedSubsetPreimage f Z))).mapDerivedCategory.map
          ((derivedPullbackShiftedUnitIso (closedSubsetRestriction f Z) p).inv ≫
            (derivedPullback (closedSubsetRestriction f Z)).map η ≫
            supportedPullbackMap f Z hZ (isClosed_closedSubsetPreimage f Z hZ) K) ≫
        (derivedPushforwardAdjunction X' (closedSubsetPreimage f Z)
            (isClosed_closedSubsetPreimage f Z hZ)).counit.app ((derivedPullback f).obj K) =
      (derivedPullbackShiftedUnitIso f p).inv ≫ (derivedPullback f).map
        (shiftedUnitToPushforward Z p ≫
          (modulePushforward (closedSubsetInclusion X Z)).mapDerivedCategory.map η ≫
          (derivedPushforwardAdjunction X Z hZ).counit.app K) :=
  forgetSupport_pullbackSupportedClass_preimage f Z hZ K
    (derivedPullbackShiftedUnitIso (closedSubsetRestriction f Z) p).inv
    (derivedPullbackShiftedUnitIso f p).inv
    (shiftedUnitToPushforward Z p)
    (shiftedUnitToPushforward (X := X') (closedSubsetPreimage f Z) p)
    (hunit_of_derivedPullbackCompatible f Z (closedSubsetPreimage f Z)
      (closedSubsetRestriction f Z)
      (closedSubsetRestriction_comp_closedSubsetInclusion f Z)
      (derivedPullbackShiftedUnitIso (closedSubsetInclusion X Z) p).hom
      (derivedPullbackShiftedUnitIso
        (closedSubsetInclusion X' (closedSubsetPreimage f Z)) p).hom
      _ _
      (StacksDraft.UnitPullbackComposition.shiftedUnitIso_square_left f
        (closedSubsetInclusion X Z)
        (closedSubsetInclusion X' (closedSubsetPreimage f Z))
        (closedSubsetRestriction f Z)
        (closedSubsetRestriction_comp_closedSubsetInclusion f Z) p))
    η

end CanonicalComparisons

end Preimage

end Stacks.Cohomology.SupportedComplexes

end
