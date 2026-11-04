module

public import StacksFrontier.AlgebraicGeometry.DeRham.Gysin.GysinTargetExcision
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.CompositionUnconditional
public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryHomologyCompIso
public import StacksFrontier.Topology.Sheaves.Cohomology.ModulePushforwardComparison.DerivedCategory

/-!
# Transitivity of the excision for `i_*ℋ ⁿ_T` along a composite of open immersions

`Stacks.Gysin.supportCohomologyPullbackIso` is excision in degree `n` along one open immersion
of ringed spaces.  This file proves that it is **transitive**: for `f : X'' ⟶ X'` and
`g : X' ⟶ X` open immersions and `T ⊆ X` closed, the isomorphism for `f ≫ g` is the one for `g`,
pulled back along `f`, followed by the one for `f`, the two canonical identifications
`(f ≫ g)^* ≅ f^* ∘ g^*` of [Stacks, Tag 0D5S]'s underived companion mediating.  Specialized to
`f` and `g` the canonical inclusions of an open subspace `V` of an open subspace `W` of `X`, this
is the **transitivity over two nested opens** `V ≤ W ≤ X` that the two-chart comparison of
[Stacks, Tag 0G86] needs, and the statement `supportCohomologyPullbackIso_comp` *is* that
instance: the general statement is about an arbitrary composite of open immersions, and the
nested-opens case is read off it at
`f := (X.restrict W.isOpenEmbedding).ofRestrict V.isOpenEmbedding` and
`g := X.ofRestrict W.isOpenEmbedding`, exactly as
`Stacks.Cohomology.DerivedOpenImmersion.derivedPullbackOpenImmersionIso_ofRestrict_comp` is read
off `…_comp`.

The same argument gives the transitivity of the **derived** excision
`Stacks.Perfect.SupportPushExcision.derivedSupportedPushforwardPullbackIso` itself, which is
recorded here as `derivedSupportedPushforwardPullbackIso_comp`.

## Main results

* `Stacks.Gysin.derivedSupportedPushforwardPullback_hom_ext`: **the excision isomorphism for
  `i_* R𝓗_T` is pinned down by its compatibility with the counit of [Stacks, Tag 0A3B].**  Two
  maps `Lf^*(i_* R𝓗_T K) ⟶ i'_* R𝓗_{T'}(Lf^* K)` whose composites with that counit agree are
  equal.
* `Stacks.Gysin.derivedSupportedPushforwardPullbackIso_comp`: **the derived excision along a
  composite of two open immersions** is the composite of the two derived excisions, over the
  composition isomorphism of [Stacks, Tag 0D5S].
* `Stacks.Gysin.supportCohomologyDerivedIso_comp`: the same for the derived isomorphism
  `Stacks.Gysin.supportCohomologyDerivedIso` that `supportCohomologyPullbackIso` is `Hⁿ` of.
* `Stacks.Gysin.supportCohomologyPullbackIso_comp`: **transitivity of the excision in degree
  `n`**, the statement the chart comparison consumes.
* `Stacks.Gysin.mapDerivedCategorySingleFunctor_comp`: an auxiliary coherence of general
  homological algebra — the comparison `D(F)(M[0]) ≅ (F M)[0]` of Mathlib's
  `CategoryTheory.Functor.mapDerivedCategorySingleFunctor` is compatible with composition of
  exact functors.
* `Stacks.Gysin.mapDerivedCategoryHomologyIso_eq`: the copy of "an exact functor commutes with
  `Hⁿ`" that `supportCohomologyPullbackIso` is built from,
  `StacksDraft.DerivedCategoryHomology.mapDerivedCategoryHomologyIso`, is the copy
  `CategoryTheory.Functor.mapDerivedCategoryHomologyFunctorIso` whose composition law the project
  already has.
* `Stacks.Gysin.mapDerivedCategoryHomologyIso_comp`: that composition law, read for the
  degreewise pullbacks along `f`, `g` and `f ≫ g`.
* `Stacks.Gysin.supportCohomologyPullbackIso_naturality`: **excision in degree `n` is natural in
  the coefficient module**, which `GysinTargetExcision.lean` records only at an object.

## Implementation notes

**The route: a uniqueness statement, not a diagram chase.**  The derived excision
`derivedSupportedPushforwardPullbackIso` is a composite of four factors, and comparing its value
on `f ≫ g` with the composite of its values on `f` and on `g` factor by factor would need the
composition coherence of each of them — of the comparison of the exact direct image, of the
base change of [Stacks, Tag 08HY], and of the canonical map of [Stacks, Tag 0G78].  None of that
is needed.  `i'_*` is fully faithful on derived categories — the unit of the adjunction of
[Stacks, Tag 0A3B] is invertible,
`Stacks.Cohomology.SupportedComplexes.isIso_unit_derivedPushforwardAdjunction` — so for `A` in
the image of `i'_*` the map `Hom(A, i'_* R𝓗_{T'} B) ⟶ Hom(A, B)` given by composing with the
counit is a *bijection*: that is `hom_ext_of_comp_counit`.  The source
`Lf^*(i_* R𝓗_T K)` is in that image, by the invertibility of the base-change transformation
along an open immersion
(`Stacks.Cohomology.SupportedComplexes.isIso_supportedPullbackBaseChangeMap_of_isOpenImmersion`),
which is `pullbackPushforwardIso`.  Both routes satisfy the same counit equation — each
factor contributes either a naturality square or the already recorded
`…derivedSupportedPushforwardPullbackIso_hom_comp_counit` — so they are equal.

**What the counit equation looks like in degree `n`.**  `supportCohomologyDerivedIso` is the
derived isomorphism `D(f^*)(i_* R𝓗_T(M[0])) ≅ i'_* R𝓗_{T'}((f^* M)[0])` inside
`supportCohomologyPullbackIso`; `supportCohomologyDerivedIso_hom_comp_counit` says that composing
it with the counit gives `D(f^*)` of the counit on `X`, followed by the single-complex comparison
`CategoryTheory.Functor.mapDerivedCategorySingleFunctor`.  **Every occurrence of the derived
pullback `Lf^*` cancels**: the two copies of
`Stacks.Cohomology.DerivedOpenImmersion.derivedPullbackOpenImmersionIso` that surround the
excision inside `supportCohomologyDerivedIso` are mutually inverse across the counit's
naturality.  This is why the transitivity in degree `n` needs no coherence for `Lf^*` at all —
not the composition coherence of [Stacks, Tag 0D5S], and not its compatibility with the
degreewise comparison
(`Stacks.Cohomology.DerivedOpenImmersion.derivedPullbackIsoMapDerivedCategory_comp`): what is
left is the composition coherence of the *degreewise* pullback, which is
`Stacks.DerivedCategoryComparisons.mapDerivedCategoryCompIso`.

**The two general coherences that were missing.**  Reading the derived statement in degree `n`
needs the comparisons that surround the excision to be compatible with composition.  For
"an exact functor commutes with `Hⁿ`" the project already had it
(`CategoryTheory.Functor.mapDerivedCategoryHomologyFunctorIso_comp_app` and
`…_isoOfNatIso_app`), for a different one of its several copies; `mapDerivedCategoryHomologyIso_eq`
identifies the copy used here with that one.  For the single-complex comparison it did not: the
composition law `mapDerivedCategorySingleFunctor_comp` is proved here, by descending through
`DerivedCategory.Q` to cochain complexes, where the comparison is
`HomologicalComplex.singleMapHomologicalComplex` and both laws —
`mapCochainComplexSingleFunctor_comp` and `mapCochainComplexSingleFunctor_natIso` — hold
degreewise.

**Formal chases are isolated at abstract categories.**  Each of `chase`…`chase6`, `map_comp2`
and `map_comp4` is the formal identity left over once the naturality squares are inserted,
stated for arbitrary categories.  This is deliberate and follows
`StacksFrontier/Topology/Sheaves/Cohomology/DerivedPullback/OpenImmersionRestrictionNaturality.lean`:
`rw` and `simp` re-typecheck their goals at a transparency at which the two spellings
`Stacks.Perfect.SupportedQuasicoherent.derivedSupportedPushforward` and
`R𝓗_T ⋙ i_*` of one functor are not interchangeable, and at which the heartbeat budget of a
single declaration does not survive a long rewrite over derived categories of sheaves of
modules.  Doing the rewriting where no derived category appears avoids both.

**What is *not* here.**  The transitivity is stated for the pullback of modules along the
ringed-space inclusion, that is for `Stacks.Gysin.supportCohomologyPullbackIso`, not for
`Stacks.Gysin.supportCohomologyRestrictIso`, whose source and target are written with
`AlgebraicGeometry.Scheme.Modules.restrictFunctor`.  Transporting it across
`Stacks.Gysin.modulePullbackRestrictFunctorIso` needs **naturality of
`supportCohomologyPullbackIso` in the coefficient module**, because the inner factor of the
composite route is taken at `f^* M` on one side and at `M|_W` on the other;
`GysinTargetExcision.lean` records only the object-level isomorphism, so that naturality is
proved here, as `supportCohomologyPullbackIso_naturality`.  The transport itself is
`GysinTargetExcisionRestrictComp.lean`: `Stacks.Gysin.supportCohomologyConjIso_comp` is this
transitivity conjugated by an arbitrary identification of the two pullback functors, and
`Stacks.Gysin.supportCohomologyRestrictCompIso_hom` is its instance at two nested opens, in the
`restrictFunctor` spelling the equation charts of [Stacks, Tag 0G86] use.

**No declaration here carries a `@[stacks ...]` attribute**: every statement is a transport or a
coherence of one that does.

## References

* [Stacks Project, Remark 20.34.12 (Tag 0G78)](https://stacks.math.columbia.edu/tag/0G78)
* [Stacks Project, Lemma 20.34.1 (Tag 0A3B)](https://stacks.math.columbia.edu/tag/0A3B)
* [Stacks Project, Lemma 20.28.9 (Tag 0D5S)](https://stacks.math.columbia.edu/tag/0D5S)
* [Stacks Project, Tag 0G7Q](https://stacks.math.columbia.edu/tag/0G7Q)
* [Stacks Project, Tag 0G86](https://stacks.math.columbia.edu/tag/0G86)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open Stacks.Cohomology.DerivedOpenImmersion
open Stacks.Cohomology.SupportedComplexes
open Stacks.Perfect.SupportedFraction
open Stacks.Perfect.SupportedQuasicoherent (derivedSupportedPushforward)
open StacksDraft.DerivedCategoryHomology

universe u

namespace Stacks.Gysin

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance] preservesFiniteLimits_modulePullback_of_isOpenImmersion

section Unique

variable {C D : Type*} [Category* C] [Category* D] {P : D ⥤ C} {R : C ⥤ D}

/-- **A map into `P(R B)` is determined by its composite with the counit, on the image of `P`.**
For an adjunction `P ⊣ R` whose unit is invertible — equivalently, with `P` fully faithful — the
map `Hom(P M, P (R B)) ⟶ Hom(P M, B)` given by composing with the counit is injective, because
`R` of the counit is invertible by the triangle identity. -/
theorem hom_ext_of_comp_counit (adj : P ⊣ R) [IsIso adj.unit] {M : D} {B : C}
    (φ ψ : P.obj M ⟶ P.obj (R.obj B))
    (h : φ ≫ adj.counit.app B = ψ ≫ adj.counit.app B) : φ = ψ := by
  have hiso : IsIso (R.map (adj.counit.app B)) := by
    have ht := adj.right_triangle_components (Y := B)
    have h2 : IsIso (adj.unit.app (R.obj B) ≫ R.map (adj.counit.app B)) := by
      rw [ht]
      exact IsIso.id _
    exact IsIso.of_isIso_comp_left (adj.unit.app (R.obj B)) _
  have h1 : adj.homEquiv M _ φ = adj.homEquiv M _ ψ := by
    have e1 := adj.homEquiv_naturality_right (f := φ) (g := adj.counit.app B)
    have e2 := adj.homEquiv_naturality_right (f := ψ) (g := adj.counit.app B)
    rw [h] at e1
    exact (cancel_mono (R.map (adj.counit.app B))).1 (e1.symm.trans e2)
  exact (adj.homEquiv M _).injective h1

end Unique

section Preimage

variable {X'' X' X : RingedSpace.{u, u}} (f : X'' ⟶ X') (g : X' ⟶ X) (Z : Set X.carrier)

/-- The preimage of a closed subset under a composite is the iterated preimage, and the two are
the same term: no transport is needed between them. -/
theorem closedSubsetPreimage_comp :
    closedSubsetPreimage (f ≫ g) Z = closedSubsetPreimage f (closedSubsetPreimage g Z) := rfl

/-- `hom_ext_of_comp_counit` for a source that is only *isomorphic* to an object of the image of
`P`, which is the form the excision isomorphism is used at. -/
theorem hom_ext_of_comp_counit' {C D : Type*} [Category* C] [Category* D] {P : D ⥤ C} {R : C ⥤ D}
    (adj : P ⊣ R) [IsIso adj.unit] {A : C} {M : D} (e : A ≅ P.obj M) {B : C}
    (φ ψ : A ⟶ P.obj (R.obj B)) (h : φ ≫ adj.counit.app B = ψ ≫ adj.counit.app B) : φ = ψ := by
  refine (cancel_epi e.inv).1 (hom_ext_of_comp_counit adj (e.inv ≫ φ) (e.inv ≫ ψ) ?_)
  rw [Category.assoc, Category.assoc, h]

end Preimage

section Image

variable {X' X : RingedSpace.{u, u}} (f : X' ⟶ X) [SheafedSpace.IsOpenImmersion f]
  (Z : Set X.carrier) (hZ : IsClosed Z)

/-- **The derived pullback along an open immersion of a complex pushed forward from a closed
subset is itself pushed forward from the preimage of that subset.**  This is the base-change
transformation of [Stacks, Tag 08HY] for the Cartesian square of the restriction, invertible
along an open immersion by
`Stacks.Cohomology.SupportedComplexes.isIso_supportedPullbackBaseChangeMap_of_isOpenImmersion`,
read across the comparison
`Stacks.Cohomology.SupportedComplexes.closedPushforwardComparison` of the exact direct
image on both sides.  It is what puts the source of the excision isomorphism into the image of
`i'_*`, which is what makes the counit compatibility a characterization. -/
def pullbackPushforwardIso
    (N : DerivedCategory (SheafOfModules.{u}
      (structureSheafRing (closedSubsetRingedSpace X Z)))) :
    letI := pushforward_preservesFiniteLimits X Z
    letI := pushforward_preservesFiniteColimits X Z hZ
    letI := pushforward_preservesFiniteLimits X' (closedSubsetPreimage f Z)
    letI := pushforward_preservesFiniteColimits X' (closedSubsetPreimage f Z)
      (isClosed_closedSubsetPreimage f Z hZ)
    (derivedPullback f).obj
        ((modulePushforward (closedSubsetInclusion X Z)).mapDerivedCategory.obj N) ≅
      (modulePushforward
          (closedSubsetInclusion X' (closedSubsetPreimage f Z))).mapDerivedCategory.obj
        ((derivedPullback (closedSubsetRestriction f Z)).obj N) :=
  letI := pushforward_preservesFiniteLimits X Z
  letI := pushforward_preservesFiniteColimits X Z hZ
  letI := pushforward_preservesFiniteLimits X' (closedSubsetPreimage f Z)
  letI := pushforward_preservesFiniteColimits X' (closedSubsetPreimage f Z)
    (isClosed_closedSubsetPreimage f Z hZ)
  (derivedPullback f).mapIso ((closedPushforwardComparison X Z).app N) ≪≫
    (@asIso _ _ _ _ _ (isIso_supportedPullbackBaseChangeMap_of_isOpenImmersion f Z N)) ≪≫
    ((closedPushforwardComparison X' (closedSubsetPreimage f Z)).symm.app _)

end Image

section ExcisionUnique

open Stacks.Perfect.SupportPushExcision

variable {X' X : RingedSpace.{u, u}} (f : X' ⟶ X) [SheafedSpace.IsOpenImmersion f]
  (Z : Set X.carrier) (hZ : IsClosed Z)

/-- **The excision isomorphism of [Stacks, Tag 0G78] is determined by its compatibility with the
counit of [Stacks, Tag 0A3B].**  Two maps `Lf^*(i_* R𝓗_T K) ⟶ i'_* R𝓗_{T'}(Lf^* K)` whose
composites with the canonical map `i'_* R𝓗_{T'}(Lf^* K) ⟶ Lf^* K` agree are equal.

This is `hom_ext_of_comp_counit'` for the adjunction of [Stacks, Tag 0A3B], whose unit is
invertible, with the source placed in the image of `i'_*` by `pullbackPushforwardIso`. -/
theorem derivedSupportedPushforwardPullback_hom_ext
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing X)))
    (φ ψ : (derivedPullback f).obj ((derivedSupportedPushforward X Z hZ).obj K) ⟶
      (derivedSupportedPushforward X' (closedSubsetPreimage f Z)
        (isClosed_closedSubsetPreimage f Z hZ)).obj ((derivedPullback f).obj K))
    (h : φ ≫ (derivedPushforwardAdjunction X' (closedSubsetPreimage f Z)
            (isClosed_closedSubsetPreimage f Z hZ)).counit.app ((derivedPullback f).obj K) =
        ψ ≫ (derivedPushforwardAdjunction X' (closedSubsetPreimage f Z)
            (isClosed_closedSubsetPreimage f Z hZ)).counit.app ((derivedPullback f).obj K)) :
    φ = ψ :=
  hom_ext_of_comp_counit'
    (derivedPushforwardAdjunction X' (closedSubsetPreimage f Z)
      (isClosed_closedSubsetPreimage f Z hZ))
    (pullbackPushforwardIso f Z hZ ((derivedSupportedSectionsOnClosed X Z hZ).obj K)) φ ψ h

end ExcisionUnique

section ExcisionComp

open Stacks.Perfect.SupportPushExcision
open Stacks.DerivedPullback.Composition

variable {X'' X' X : RingedSpace.{u, u}} (f : X'' ⟶ X') (g : X' ⟶ X)
  [SheafedSpace.IsOpenImmersion f] [SheafedSpace.IsOpenImmersion g]
  (Z : Set X.carrier) (hZ : IsClosed Z)

/-- The formal identity left over in `derivedSupportedPushforwardPullbackIso_comp_counit` once
the four naturality squares are inserted.  Stated at an arbitrary category, so that the
rewriting happens where no derived category appears. -/
private theorem chase {C : Type*} [Category* C] {a b c d : C}
    (p : a ⟶ b) (q : b ⟶ c) (v : c ⟶ d) (u : d ⟶ c) (r : a ⟶ d)
    (h : r ≫ u = p ≫ q) (hu : u ≫ v = 𝟙 d) :
    p ≫ q ≫ v = r := by
  rw [← Category.assoc, ← h, Category.assoc, hu, Category.comp_id]

/-- **The composite route satisfies the counit equation of [Stacks, Tag 0G78].**  Composing the
two derived excisions, with the composition isomorphism of [Stacks, Tag 0D5S] at both ends, and
then the canonical map of [Stacks, Tag 0A3B] on `X''`, gives `L(f ≫ g)^*` of the canonical map on
`X`: the three excision triangles and the naturality of the composition isomorphism, with one
pair of mutually inverse comparisons cancelling. -/
private theorem derivedSupportedPushforwardPullbackIso_comp_counit
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))) :
    ((derivedPullbackCompIsoCanonical f g).inv.app
          ((derivedSupportedPushforward X Z hZ).obj K) ≫
        (derivedPullback f).map
            ((derivedSupportedPushforwardPullbackIso g Z hZ).hom.app K) ≫
          (derivedSupportedPushforwardPullbackIso f (closedSubsetPreimage g Z)
              (isClosed_closedSubsetPreimage g Z hZ)).hom.app ((derivedPullback g).obj K) ≫
            (derivedSupportedPushforward X'' (closedSubsetPreimage f (closedSubsetPreimage g Z))
                (isClosed_closedSubsetPreimage f (closedSubsetPreimage g Z)
                  (isClosed_closedSubsetPreimage g Z hZ))).map
              ((derivedPullbackCompIsoCanonical f g).hom.app K)) ≫
        (derivedPushforwardAdjunction X'' (closedSubsetPreimage f (closedSubsetPreimage g Z))
            (isClosed_closedSubsetPreimage f (closedSubsetPreimage g Z)
              (isClosed_closedSubsetPreimage g Z hZ))).counit.app
          ((derivedPullback (f ≫ g)).obj K) =
      (derivedPullback (f ≫ g)).map ((derivedPushforwardAdjunction X Z hZ).counit.app K) := by
  have hnat := (derivedPushforwardAdjunction X''
    (closedSubsetPreimage f (closedSubsetPreimage g Z))
    (isClosed_closedSubsetPreimage f (closedSubsetPreimage g Z)
      (isClosed_closedSubsetPreimage g Z hZ))).counit.naturality
      ((derivedPullbackCompIsoCanonical f g).hom.app K)
  have hf := derivedSupportedPushforwardPullbackIso_hom_comp_counit f
    (closedSubsetPreimage g Z) (isClosed_closedSubsetPreimage g Z hZ)
    ((derivedPullback g).obj K)
  have hg := derivedSupportedPushforwardPullbackIso_hom_comp_counit g Z hZ K
  have hcc := (derivedPullbackCompIsoCanonical f g).inv.naturality
    ((derivedPushforwardAdjunction X Z hZ).counit.app K)
  dsimp only [derivedSupportedPushforward, Functor.comp_map, Functor.comp_obj,
    Functor.id_map, Functor.id_obj] at hnat hcc hf hg ⊢
  simp only [Category.assoc]
  rw [hnat, reassoc_of% hf, ← Functor.map_comp_assoc, hg]
  exact chase _ _ _ _ _ hcc ((derivedPullbackCompIsoCanonical f g).inv_hom_id_app K)

/-- **The derived excision along a composite of two open immersions is the composite of the two
derived excisions.**  For `f : X'' ⟶ X'` and `g : X' ⟶ X` open immersions of ringed spaces and
`T ⊆ X` closed, the isomorphism
`i_* R𝓗_T ⋙ L(f ≫ g)^* ≅ L(f ≫ g)^* ⋙ i''_* R𝓗_{T''}` of
`Stacks.Perfect.SupportPushExcision.derivedSupportedPushforwardPullbackIso` for `f ≫ g` is the
one for `g`, pulled back along `f`, followed by the one for `f`, with the composition
isomorphism `Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical` of
[Stacks, Tag 0D5S] mediating at both ends.

This is the compatibility of `Stacks.Perfect.SupportPushExcision.supportPushPullbackIso` with a
composite of two open immersions.  It is proved from the uniqueness
`derivedSupportedPushforwardPullback_hom_ext`, not factor by factor. -/
theorem derivedSupportedPushforwardPullbackIso_comp
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))) :
    (derivedSupportedPushforwardPullbackIso (f ≫ g) Z hZ).hom.app K =
      (derivedPullbackCompIsoCanonical f g).inv.app
          ((derivedSupportedPushforward X Z hZ).obj K) ≫
        (derivedPullback f).map
            ((derivedSupportedPushforwardPullbackIso g Z hZ).hom.app K) ≫
          (derivedSupportedPushforwardPullbackIso f (closedSubsetPreimage g Z)
              (isClosed_closedSubsetPreimage g Z hZ)).hom.app ((derivedPullback g).obj K) ≫
            (derivedSupportedPushforward X'' (closedSubsetPreimage f (closedSubsetPreimage g Z))
                (isClosed_closedSubsetPreimage f (closedSubsetPreimage g Z)
                  (isClosed_closedSubsetPreimage g Z hZ))).map
              ((derivedPullbackCompIsoCanonical f g).hom.app K) :=
  derivedSupportedPushforwardPullback_hom_ext (f ≫ g) Z hZ K _ _
    ((derivedSupportedPushforwardPullbackIso_hom_comp_counit (f ≫ g) Z hZ K).trans
      (derivedSupportedPushforwardPullbackIso_comp_counit f g Z hZ K).symm)

end ExcisionComp

section Theta

open Stacks.Perfect.SupportPushExcision

/-- The formal identity left over in `supportCohomologyDerivedIso_hom_comp_counit` once the
three naturality squares are inserted.  Stated at an arbitrary category. -/
private theorem chase2 {C : Type*} [Category* C] {a₀ a₁ a₂ a₃ a₄ a₅ a₆ : C}
    (i : a₀ ⟶ a₁) (ha : a₁ ⟶ a₀) (hi : i ≫ ha = 𝟙 a₀)
    (E : a₁ ⟶ a₂) (Sφ : a₂ ⟶ a₃) (ep : a₃ ⟶ a₄) (ep' : a₂ ⟶ a₅)
    (hb : a₅ ⟶ a₆) (σ : a₆ ⟶ a₄) (Lep : a₁ ⟶ a₅) (Dep : a₀ ⟶ a₆)
    (n1 : Sφ ≫ ep = ep' ≫ hb ≫ σ) (n2 : E ≫ ep' = Lep) (n3 : Lep ≫ hb = ha ≫ Dep) :
    (i ≫ E ≫ Sφ) ≫ ep = Dep ≫ σ := by
  simp only [Category.assoc, n1, reassoc_of% n2, reassoc_of% n3, reassoc_of% hi,
    Category.id_comp]

variable {X' X : RingedSpace.{u, u}} (f : X' ⟶ X) [SheafedSpace.IsOpenImmersion f]
  (T : Set X.carrier) (hT : IsClosed T)

/-- **The derived isomorphism inside `Stacks.Gysin.supportCohomologyPullbackIso`.**  For `f` an
open immersion of ringed spaces, `T ⊆ X` closed and `T' = f^{-1}(T)`, the degreewise pullback
along `f` of `i_* R𝓗_T(M[0])` is `i'_* R𝓗_{T'}((f^* M)[0])`.

It is the derived excision
`Stacks.Perfect.SupportPushExcision.derivedSupportedPushforwardPullbackIso`, conjugated by
`Stacks.Cohomology.DerivedOpenImmersion.derivedPullbackOpenImmersionIso` so that the degreewise
pullback replaces the derived one, and with the single-complex comparison
`CategoryTheory.Functor.mapDerivedCategorySingleFunctor` applied on the inside.  Excision in
degree `n` is `Hⁿ` of this, by `supportCohomologyPullbackIso_eq`. -/
def supportCohomologyDerivedIso (M : SheafOfModules.{u} (structureSheafRing X)) :
    (modulePullback f).mapDerivedCategory.obj
        ((derivedSupportedPushforward X T hT).obj
          ((DerivedCategory.singleFunctor
            (SheafOfModules.{u} (structureSheafRing X)) 0).obj M)) ≅
      (derivedSupportedPushforward X' (closedSubsetPreimage f T)
          (isClosed_closedSubsetPreimage f T hT)).obj
        ((DerivedCategory.singleFunctor
          (SheafOfModules.{u} (structureSheafRing X')) 0).obj ((modulePullback f).obj M)) :=
  (derivedPullbackOpenImmersionIso f).symm.app
      ((derivedSupportedPushforward X T hT).obj
        ((DerivedCategory.singleFunctor
          (SheafOfModules.{u} (structureSheafRing X)) 0).obj M)) ≪≫
    (derivedSupportedPushforwardPullbackIso f T hT).app
        ((DerivedCategory.singleFunctor
          (SheafOfModules.{u} (structureSheafRing X)) 0).obj M) ≪≫
      (derivedSupportedPushforward X' (closedSubsetPreimage f T)
          (isClosed_closedSubsetPreimage f T hT)).mapIso
        ((derivedPullbackOpenImmersionIso f).app
            ((DerivedCategory.singleFunctor
              (SheafOfModules.{u} (structureSheafRing X)) 0).obj M) ≪≫
          ((modulePullback f).mapDerivedCategorySingleFunctor 0).app M)

/-- **Excision in degree `n` is `Hⁿ` of the derived isomorphism.**  True by definition: this
only names the two halves of `Stacks.Gysin.supportCohomologyPullbackIso`. -/
theorem supportCohomologyPullbackIso_eq (n : ℤ)
    (M : SheafOfModules.{u} (structureSheafRing X)) :
    supportCohomologyPullbackIso f T hT n M =
      ((mapDerivedCategoryHomologyIso (modulePullback f) n).app
          ((derivedSupportedPushforward X T hT).obj
            ((DerivedCategory.singleFunctor
              (SheafOfModules.{u} (structureSheafRing X)) 0).obj M))).symm ≪≫
        (DerivedCategory.homologyFunctor
          (SheafOfModules.{u} (structureSheafRing X')) n).mapIso
            (supportCohomologyDerivedIso f T hT M) :=
  rfl

/-- **The counit equation that pins `supportCohomologyDerivedIso` down.**  Composing it with
the canonical map `i'_* R𝓗_{T'}((f^* M)[0]) ⟶ (f^* M)[0]` of [Stacks, Tag 0A3B] gives the
degreewise pullback of the canonical map on `X`, followed by the single-complex comparison.

Note what is *absent* from the right-hand side: the derived pullback `Lf^*`.  The two copies of
`Stacks.Cohomology.DerivedOpenImmersion.derivedPullbackOpenImmersionIso` inside
`supportCohomologyDerivedIso` cancel against each other across the counit's naturality, so no
coherence for `Lf^*` enters the transitivity in degree `n`. -/
theorem supportCohomologyDerivedIso_hom_comp_counit
    (M : SheafOfModules.{u} (structureSheafRing X)) :
    (supportCohomologyDerivedIso f T hT M).hom ≫
        (derivedPushforwardAdjunction X' (closedSubsetPreimage f T)
            (isClosed_closedSubsetPreimage f T hT)).counit.app
          ((DerivedCategory.singleFunctor
            (SheafOfModules.{u} (structureSheafRing X')) 0).obj ((modulePullback f).obj M)) =
      (modulePullback f).mapDerivedCategory.map
          ((derivedPushforwardAdjunction X T hT).counit.app
            ((DerivedCategory.singleFunctor
              (SheafOfModules.{u} (structureSheafRing X)) 0).obj M)) ≫
        (((modulePullback f).mapDerivedCategorySingleFunctor 0).app M).hom := by
  have n1 := (derivedPushforwardAdjunction X' (closedSubsetPreimage f T)
    (isClosed_closedSubsetPreimage f T hT)).counit.naturality
      ((derivedPullbackOpenImmersionIso f).hom.app
          ((DerivedCategory.singleFunctor
            (SheafOfModules.{u} (structureSheafRing X)) 0).obj M) ≫
        (((modulePullback f).mapDerivedCategorySingleFunctor 0).app M).hom)
  have n2 := derivedSupportedPushforwardPullbackIso_hom_comp_counit f T hT
    ((DerivedCategory.singleFunctor (SheafOfModules.{u} (structureSheafRing X)) 0).obj M)
  have n3 := (derivedPullbackOpenImmersionIso f).hom.naturality
    ((derivedPushforwardAdjunction X T hT).counit.app
      ((DerivedCategory.singleFunctor (SheafOfModules.{u} (structureSheafRing X)) 0).obj M))
  dsimp only [derivedSupportedPushforward, Functor.comp_map, Functor.comp_obj,
    Functor.id_map, Functor.id_obj] at n1 n2 n3 ⊢
  exact chase2 _ _ ((derivedPullbackOpenImmersionIso f).inv_hom_id_app _) _ _ _ _ _ _ _ _
    n1 n2 n3

/-- `derivedSupportedPushforwardPullback_hom_ext` at the degreewise pullback: two maps
`D(f^*)(i_* R𝓗_T(M[0])) ⟶ i'_* R𝓗_{T'}((f^* M)[0])` with the same counit composite are
equal. -/
theorem supportCohomologyDerived_hom_ext (M : SheafOfModules.{u} (structureSheafRing X))
    (φ ψ : (modulePullback f).mapDerivedCategory.obj
          ((derivedSupportedPushforward X T hT).obj
            ((DerivedCategory.singleFunctor
              (SheafOfModules.{u} (structureSheafRing X)) 0).obj M)) ⟶
        (derivedSupportedPushforward X' (closedSubsetPreimage f T)
            (isClosed_closedSubsetPreimage f T hT)).obj
          ((DerivedCategory.singleFunctor
            (SheafOfModules.{u} (structureSheafRing X')) 0).obj ((modulePullback f).obj M)))
    (h : φ ≫ (derivedPushforwardAdjunction X' (closedSubsetPreimage f T)
            (isClosed_closedSubsetPreimage f T hT)).counit.app
          ((DerivedCategory.singleFunctor
            (SheafOfModules.{u} (structureSheafRing X')) 0).obj ((modulePullback f).obj M)) =
        ψ ≫ (derivedPushforwardAdjunction X' (closedSubsetPreimage f T)
            (isClosed_closedSubsetPreimage f T hT)).counit.app
          ((DerivedCategory.singleFunctor
            (SheafOfModules.{u} (structureSheafRing X')) 0).obj ((modulePullback f).obj M))) :
    φ = ψ :=
  hom_ext_of_comp_counit'
    (derivedPushforwardAdjunction X' (closedSubsetPreimage f T)
      (isClosed_closedSubsetPreimage f T hT))
    ((derivedPullbackOpenImmersionIso f).symm.app _ ≪≫
      pullbackPushforwardIso f T hT
        ((derivedSupportedSectionsOnClosed X T hT).obj
          ((DerivedCategory.singleFunctor
            (SheafOfModules.{u} (structureSheafRing X)) 0).obj M))) φ ψ h

/-- Pasting two commuting squares.  Stated at an arbitrary category. -/
private theorem paste2 {D : Type*} [Category* D] {a b c0 a' b' c' : D} (x : a ⟶ b) (y : b ⟶ c0)
    (x' : a' ⟶ b') (y' : b' ⟶ c') (p : a ⟶ a') (q : b ⟶ b') (r : c0 ⟶ c')
    (h1 : p ≫ x' = x ≫ q) (h2 : q ≫ y' = y ≫ r) : p ≫ x' ≫ y' = (x ≫ y) ≫ r := by
  simp only [Category.assoc, reassoc_of% h1, h2]

/-- Carrying a commuting square through a functor.  Stated at arbitrary categories, so that the
two applications of `CategoryTheory.Functor.map_comp` happen where no derived category
appears. -/
theorem map_square {D E : Type*} [Category* D] [Category* E] (F : D ⥤ E)
    {a b c0 d0 : D} (x : a ⟶ b) (y : b ⟶ d0) (z : a ⟶ c0) (w : c0 ⟶ d0) (h : x ≫ y = z ≫ w) :
    F.map x ≫ F.map y = F.map z ≫ F.map w := by
  rw [← Functor.map_comp, ← Functor.map_comp, h]

/-- The formal identity left over in `supportCohomologyDerivedIso_naturality` once the three
naturality squares are inserted.  Stated at an arbitrary category. -/
private theorem chase7 {D : Type*} [Category* D] {m0 m1 m2 m3 p0 p1 p2 p3 : D}
    (i : m0 ⟶ m1) (E : m1 ⟶ m2) (Sφ : m2 ⟶ m3) (i' : p0 ⟶ p1) (E' : p1 ⟶ p2) (Sφ' : p2 ⟶ p3)
    (u0 : m0 ⟶ p0) (u1 : m1 ⟶ p1) (u2 : m2 ⟶ p2) (u3 : m3 ⟶ p3)
    (s1 : u0 ≫ i' = i ≫ u1) (s2 : u1 ≫ E' = E ≫ u2) (s3 : u2 ≫ Sφ' = Sφ ≫ u3) :
    u0 ≫ i' ≫ E' ≫ Sφ' = (i ≫ E ≫ Sφ) ≫ u3 := by
  simp only [Category.assoc, reassoc_of% s1, reassoc_of% s2, s3]

/-- **`supportCohomologyDerivedIso` is natural in the coefficient module.**  Each of its three
factors is the component of a natural transformation — the comparison of the derived pullback
with the degreewise one, the derived excision, and the single-complex comparison — so the
composite is natural too. -/
theorem supportCohomologyDerivedIso_naturality
    {M N : SheafOfModules.{u} (structureSheafRing X)} (ψ : M ⟶ N) :
    (modulePullback f).mapDerivedCategory.map
          ((derivedSupportedPushforward X T hT).map
            ((DerivedCategory.singleFunctor
              (SheafOfModules.{u} (structureSheafRing X)) 0).map ψ)) ≫
        (supportCohomologyDerivedIso f T hT N).hom =
      (supportCohomologyDerivedIso f T hT M).hom ≫
        (derivedSupportedPushforward X' (closedSubsetPreimage f T)
            (isClosed_closedSubsetPreimage f T hT)).map
          ((DerivedCategory.singleFunctor
            (SheafOfModules.{u} (structureSheafRing X')) 0).map ((modulePullback f).map ψ)) := by
  have s1 := (derivedPullbackOpenImmersionIso f).inv.naturality
    ((derivedSupportedPushforward X T hT).map
      ((DerivedCategory.singleFunctor (SheafOfModules.{u} (structureSheafRing X)) 0).map ψ))
  have s2 := (derivedSupportedPushforwardPullbackIso f T hT).hom.naturality
    ((DerivedCategory.singleFunctor (SheafOfModules.{u} (structureSheafRing X)) 0).map ψ)
  have h1 := (derivedPullbackOpenImmersionIso f).hom.naturality
    ((DerivedCategory.singleFunctor (SheafOfModules.{u} (structureSheafRing X)) 0).map ψ)
  have h2 := ((modulePullback f).mapDerivedCategorySingleFunctor 0).hom.naturality ψ
  dsimp only [derivedSupportedPushforward, Functor.comp_map, Functor.comp_obj] at s1 s2 h1 h2 ⊢
  have s3 := map_square (derivedSupportedPushforward X' (closedSubsetPreimage f T)
      (isClosed_closedSubsetPreimage f T hT)) _ _ _ _ (paste2 _ _ _ _ _ _ _ h1 h2)
  dsimp only [derivedSupportedPushforward, Functor.comp_map, Functor.comp_obj] at s3
  exact chase7 _ _ _ _ _ _ _ _ _ _ s1 s2 s3

/-- **Excision in degree `n` is natural in the coefficient module.**  This is
`supportCohomologyDerivedIso_naturality` read through `Hⁿ`, with the naturality of
"an exact functor commutes with `Hⁿ`" pasted on.

`GysinTargetExcision.lean` records `Stacks.Gysin.supportCohomologyPullbackIso` only at an object;
this is the naturality that transporting its transitivity onto the `restrictFunctor` spelling
of `Stacks.Gysin.supportCohomologyRestrictIso` needs. -/
theorem supportCohomologyPullbackIso_naturality (n : ℤ)
    {M N : SheafOfModules.{u} (structureSheafRing X)} (ψ : M ⟶ N) :
    (modulePullback f).map
          ((DerivedCategory.homologyFunctor (SheafOfModules.{u} (structureSheafRing X)) n).map
            ((derivedSupportedPushforward X T hT).map
              ((DerivedCategory.singleFunctor
                (SheafOfModules.{u} (structureSheafRing X)) 0).map ψ))) ≫
        (supportCohomologyPullbackIso f T hT n N).hom =
      (supportCohomologyPullbackIso f T hT n M).hom ≫
        (DerivedCategory.homologyFunctor (SheafOfModules.{u} (structureSheafRing X')) n).map
          ((derivedSupportedPushforward X' (closedSubsetPreimage f T)
              (isClosed_closedSubsetPreimage f T hT)).map
            ((DerivedCategory.singleFunctor
              (SheafOfModules.{u} (structureSheafRing X')) 0).map
                ((modulePullback f).map ψ))) := by
  have h1 := (mapDerivedCategoryHomologyIso (modulePullback f) n).inv.naturality
    ((derivedSupportedPushforward X T hT).map
      ((DerivedCategory.singleFunctor (SheafOfModules.{u} (structureSheafRing X)) 0).map ψ))
  dsimp only [Functor.comp_map, Functor.comp_obj] at h1
  have h2 := map_square
    (DerivedCategory.homologyFunctor (SheafOfModules.{u} (structureSheafRing X')) n) _ _ _ _
    (supportCohomologyDerivedIso_naturality f T hT ψ)
  exact paste2 _ _ _ _ _ _ _ h1 h2

end Theta

section Single

variable {A B C : Type*} [Category* A] [Category* B] [Category* C]
  [Abelian A] [Abelian B] [Abelian C]

/-- The formal identity left over in `mapDerivedCategorySingleFunctor_comp` once the
factorizations over `DerivedCategory.Q` are inserted.  Stated at an arbitrary category. -/
private theorem chase3 {D : Type*} [Category* D] {x0 x1 x2 x3 x4 x5 : D}
    (a : x0 ⟶ x1) (b : x1 ⟶ x2) (dq : x1 ⟶ x3) (b' : x3 ⟶ x4) (u : x2 ⟶ x4)
    (T : x2 ⟶ x5) (T' : x4 ⟶ x5) (hn : dq ≫ b' = b ≫ u) (hT : T = u ≫ T') :
    a ≫ b ≫ T = a ≫ dq ≫ b' ≫ T' := by
  rw [hT, ← reassoc_of% hn]

/-- **The comparison `F(M[j]) ≅ (F M)[j]` on cochain complexes is compatible with composition
of additive functors.**  Both sides are computed degreewise by
`HomologicalComplex.singleMapHomologicalComplex`. -/
theorem mapCochainComplexSingleFunctor_comp (F : A ⥤ B) (G : B ⥤ C) [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] (j : ℤ) (M : A) :
    ((F ⋙ G).mapCochainComplexSingleFunctor j).hom.app M =
      (G.mapHomologicalComplex (ComplexShape.up ℤ)).map
          ((F.mapCochainComplexSingleFunctor j).hom.app M) ≫
        (G.mapCochainComplexSingleFunctor j).hom.app (F.obj M) := by
  ext i
  by_cases h : i = j
  · subst h
    simp [Functor.mapCochainComplexSingleFunctor]
  · simp [Functor.mapCochainComplexSingleFunctor, h]

/-- **The comparison `F(M[j]) ≅ (F M)[j]` on cochain complexes is natural in `F`.**  An
isomorphism of additive functors intertwines the two comparisons with itself, read on the single
complexes. -/
theorem mapCochainComplexSingleFunctor_natIso (F H : A ⥤ C) [F.Additive] [H.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H] (e : F ≅ H) (j : ℤ) (M : A) :
    (NatIso.mapHomologicalComplex e (ComplexShape.up ℤ)).hom.app
          ((HomologicalComplex.single A (ComplexShape.up ℤ) j).obj M) ≫
        (H.mapCochainComplexSingleFunctor j).hom.app M =
      (F.mapCochainComplexSingleFunctor j).hom.app M ≫
        (HomologicalComplex.single C (ComplexShape.up ℤ) j).map (e.hom.app M) := by
  ext i
  by_cases h : i = j
  · subst h
    simp [Functor.mapCochainComplexSingleFunctor, HomologicalComplex.single_map_f_self,
      NatTrans.naturality_assoc]
  · simp [Functor.mapCochainComplexSingleFunctor, h]

/-- **The comparison `D(F)(M[0]) ≅ (F M)[0]` at the image of a module**, in terms of the
factorization of the degreewise action of `F` through `DerivedCategory.Q` and the complex-level
comparison.  This is Mathlib's
`CategoryTheory.Functor.mapDerivedCategoryFactors_inv_app_mapDerivedCategorySingleFunctor_hom_app`
with the invertible factor moved to the other side. -/
theorem mapDerivedCategorySingleFunctor_hom_app_eq [HasDerivedCategory A]
    [HasDerivedCategory B] (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F]
    [PreservesFiniteColimits F] (M : A) :
    (F.mapDerivedCategorySingleFunctor 0).hom.app M =
      F.mapDerivedCategoryFactors.hom.app
          ((HomologicalComplex.single A (ComplexShape.up ℤ) 0).obj M) ≫
        DerivedCategory.Q.map ((F.mapCochainComplexSingleFunctor 0).hom.app M) := by
  rw [← F.mapDerivedCategoryFactors_inv_app_mapDerivedCategorySingleFunctor_hom_app M,
    ← Category.assoc, Iso.hom_inv_id_app, Category.id_comp]

/-- **The comparison `D(F)(M[0]) ≅ (F M)[0]` is compatible with composition of exact
functors.**  For an isomorphism `e : F ⋙ G ≅ H` of exact functors, the comparison for `H`,
preceded by the identification of `D(H)` with `D(F) ⋙ D(G)`, is the comparison for `F` read
inside `D(G)`, then the comparison for `G`, then `e` read on single complexes.

Both sides are descended through `DerivedCategory.Q` from cochain complexes, where the statement
is `mapCochainComplexSingleFunctor_comp` followed by
`mapCochainComplexSingleFunctor_natIso`. -/
theorem mapDerivedCategorySingleFunctor_comp [HasDerivedCategory A] [HasDerivedCategory B]
    [HasDerivedCategory C] (F : A ⥤ B) (G : B ⥤ C) (H : A ⥤ C)
    [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [H.Additive] [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    (e : F ⋙ G ≅ H) (M : A) :
    (Stacks.DerivedCategoryComparisons.mapDerivedCategoryCompIso F G).inv.app
          ((DerivedCategory.singleFunctor A 0).obj M) ≫
        (Stacks.DerivedCategoryComparisons.mapDerivedCategoryIsoOfNatIso (F ⋙ G) H e).hom.app
            ((DerivedCategory.singleFunctor A 0).obj M) ≫
          (H.mapDerivedCategorySingleFunctor 0).hom.app M =
      G.mapDerivedCategory.map ((F.mapDerivedCategorySingleFunctor 0).hom.app M) ≫
        (G.mapDerivedCategorySingleFunctor 0).hom.app (F.obj M) ≫
          (DerivedCategory.singleFunctor C 0).map (e.hom.app M) := by
  have hcx : (NatIso.mapHomologicalComplex e (ComplexShape.up ℤ)).hom.app
          ((HomologicalComplex.single A (ComplexShape.up ℤ) 0).obj M) ≫
        (H.mapCochainComplexSingleFunctor 0).hom.app M =
      (G.mapHomologicalComplex (ComplexShape.up ℤ)).map
          ((F.mapCochainComplexSingleFunctor 0).hom.app M) ≫
        (G.mapCochainComplexSingleFunctor 0).hom.app (F.obj M) ≫
          (HomologicalComplex.single C (ComplexShape.up ℤ) 0).map (e.hom.app M) := by
    rw [mapCochainComplexSingleFunctor_natIso (F ⋙ G) H e 0 M,
      mapCochainComplexSingleFunctor_comp F G 0 M, Category.assoc]
  have hs : (DerivedCategory.singleFunctor C 0).map (e.hom.app M) =
      DerivedCategory.Q.map
        ((HomologicalComplex.single C (ComplexShape.up ℤ) 0).map (e.hom.app M)) := rfl
  have hcxQ : DerivedCategory.Q.map
          ((NatIso.mapHomologicalComplex e (ComplexShape.up ℤ)).hom.app
            ((HomologicalComplex.single A (ComplexShape.up ℤ) 0).obj M)) ≫
        DerivedCategory.Q.map ((H.mapCochainComplexSingleFunctor 0).hom.app M) =
      DerivedCategory.Q.map ((G.mapHomologicalComplex (ComplexShape.up ℤ)).map
            ((F.mapCochainComplexSingleFunctor 0).hom.app M)) ≫
        DerivedCategory.Q.map ((G.mapCochainComplexSingleFunctor 0).hom.app (F.obj M)) ≫
          (DerivedCategory.singleFunctor C 0).map (e.hom.app M) := by
    rw [hs]
    simp only [← DerivedCategory.Q.map_comp]
    exact congrArg DerivedCategory.Q.map hcx
  have hnatG := G.mapDerivedCategoryFactors.hom.naturality
    ((F.mapCochainComplexSingleFunctor 0).hom.app M)
  dsimp only [Functor.comp_map] at hnatG
  show (Stacks.DerivedCategoryComparisons.mapDerivedCategoryCompIso F G).inv.app
        (DerivedCategory.Q.obj ((HomologicalComplex.single A (ComplexShape.up ℤ) 0).obj M)) ≫
      (Stacks.DerivedCategoryComparisons.mapDerivedCategoryIsoOfNatIso (F ⋙ G) H e).hom.app
          (DerivedCategory.Q.obj ((HomologicalComplex.single A (ComplexShape.up ℤ) 0).obj M)) ≫
        _ = _
  rw [Stacks.DerivedCategoryComparisons.mapDerivedCategoryCompIso_inv_app_Q,
    Stacks.DerivedCategoryComparisons.mapDerivedCategoryIsoOfNatIso_hom_app_Q,
    mapDerivedCategorySingleFunctor_hom_app_eq, mapDerivedCategorySingleFunctor_hom_app_eq,
    mapDerivedCategorySingleFunctor_hom_app_eq]
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc, Functor.map_comp]
  exact chase3 _ _ _ _ _ _ _ hnatG hcxQ

end Single

section Kappa

open Stacks.DerivedCategoryComparisons

attribute [local instance] CategoryTheory.Limits.comp_preservesFiniteLimits
  CategoryTheory.Limits.comp_preservesFiniteColimits

/-- **The copy of "an exact functor commutes with `Hⁿ`" that
`Stacks.Gysin.supportCohomologyPullbackIso` is built from is the one whose composition law the
project has.**  `StacksDraft.DerivedCategoryHomology.mapDerivedCategoryHomologyIso` and
`CategoryTheory.Functor.mapDerivedCategoryHomologyFunctorIso` are both
`CategoryTheory.Localization.liftNatIso` of the comparison
`CategoryTheory.ShortComplex.mapHomologyIso` through `DerivedCategory.Q`; they are not
`rfl`-equal, and they are equal.

Without this the composition law
`CategoryTheory.Functor.mapDerivedCategoryHomologyFunctorIso_comp_app` cannot be applied to the
isomorphism the Gysin material uses. -/
theorem mapDerivedCategoryHomologyIso_eq {A B : Type*} [Category* A] [Category* B]
    [Abelian A] [Abelian B] [HasDerivedCategory A] [HasDerivedCategory B] (F : A ⥤ B) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] (n : ℤ) :
    mapDerivedCategoryHomologyIso F n = F.mapDerivedCategoryHomologyFunctorIso n := by
  refine Iso.ext (Localization.natTrans_ext DerivedCategory.Q
    (HomologicalComplex.quasiIso A (ComplexShape.up ℤ)) fun P => ?_)
  rw [Functor.mapDerivedCategoryHomologyFunctorIso_hom_app_Q]
  simp [mapDerivedCategoryHomologyIso, mapHomologicalComplexHomologyIso,
    DerivedCategory.liftingHomologyFunctor_iso, Functor.lifting_iso_mapDerivedCategory]
  rfl

/-- Inverting a three-factor factorization of isomorphisms, with the result right-associated.
Used to turn the composition law for `Hⁿ`, which is stated in the forward direction, into the
form `supportCohomologyPullbackIso_comp` consumes. -/
private theorem inv_of_comp3 {D : Type*} [Category* D] {a b c0 d0 e0 : D} (U : a ≅ b)
    (V : b ≅ c0) (X : a ≅ d0) (Y : d0 ≅ e0) (Z : e0 ≅ c0)
    (h : U.hom ≫ V.hom = X.hom ≫ Y.hom ≫ Z.hom) :
    V.inv ≫ U.inv = Z.inv ≫ Y.inv ≫ X.inv := by
  have h2 : U ≪≫ V = X ≪≫ Y ≪≫ Z := Iso.ext h
  simpa [Category.assoc] using congrArg Iso.inv h2

end Kappa

section ThetaComp

open Stacks.Perfect.SupportPushExcision
open Stacks.DerivedPullback.Composition
open Stacks.DerivedCategoryComparisons

attribute [local instance] CategoryTheory.Limits.comp_preservesFiniteLimits
  CategoryTheory.Limits.comp_preservesFiniteColimits

/-- Cancelling an isomorphism against its inverse at the head of a composite.  Stated at an
arbitrary category. -/
private theorem chase4 {D : Type*} [Category* D] {y0 y1 y2 y3 : D} (α : y0 ⟶ y1) (β₁ : y1 ⟶ y2)
    (β₂ : y2 ⟶ y0) (σ : y0 ⟶ y3) (h : α ≫ β₁ ≫ β₂ = 𝟙 y0) : α ≫ β₁ ≫ β₂ ≫ σ = σ := by
  rw [← Category.assoc β₁, ← Category.assoc α, h, Category.id_comp]

variable {X'' X' X : RingedSpace.{u, u}} (f : X'' ⟶ X') (g : X' ⟶ X)
  [SheafedSpace.IsOpenImmersion f] [SheafedSpace.IsOpenImmersion g]

/-- **The degreewise pullback along a composite of open immersions, on derived categories.**
`D((f ≫ g)^*) ≅ D(g^*) ⋙ D(f^*)`: the identification
`Stacks.DerivedCategoryComparisons.mapDerivedCategoryCompIso` of the descent of a composite with
the composite of the descents, read across the underived composition isomorphism
`Stacks.DerivedPullback.Composition.modulePullbackComp`.

This is the only composition coherence for pullback that the transitivity uses; the derived
pullback `Lf^*` and the composition isomorphism of [Stacks, Tag 0D5S] do not enter. -/
def pullbackCompDerivedIso :
    (modulePullback (f ≫ g)).mapDerivedCategory ≅
      (modulePullback g).mapDerivedCategory ⋙ (modulePullback f).mapDerivedCategory :=
  (mapDerivedCategoryIsoOfNatIso (modulePullback g ⋙ modulePullback f)
      (modulePullback (f ≫ g)) (Stacks.DerivedPullback.Composition.modulePullbackComp f g)).symm ≪≫
    mapDerivedCategoryCompIso (modulePullback g) (modulePullback f)

/-- `mapDerivedCategorySingleFunctor_comp` for the pullbacks along `f`, `g` and `f ≫ g`, with
the identification of `D((f ≫ g)^*)` with `D(g^*) ⋙ D(f^*)` on the left rather than its
inverse on the right. -/
theorem mapDerivedCategorySingleFunctor_modulePullback_comp
    (M : SheafOfModules.{u} (structureSheafRing X)) :
    (pullbackCompDerivedIso f g).hom.app
          ((DerivedCategory.singleFunctor
            (SheafOfModules.{u} (structureSheafRing X)) 0).obj M) ≫
        (modulePullback f).mapDerivedCategory.map
            (((modulePullback g).mapDerivedCategorySingleFunctor 0).hom.app M) ≫
          ((modulePullback f).mapDerivedCategorySingleFunctor 0).hom.app
              ((modulePullback g).obj M) ≫
            (DerivedCategory.singleFunctor
              (SheafOfModules.{u} (structureSheafRing X'')) 0).map
                ((Stacks.DerivedPullback.Composition.modulePullbackComp f g).hom.app M) =
      ((modulePullback (f ≫ g)).mapDerivedCategorySingleFunctor 0).hom.app M := by
  rw [← mapDerivedCategorySingleFunctor_comp (modulePullback g) (modulePullback f)
    (modulePullback (f ≫ g)) (Stacks.DerivedPullback.Composition.modulePullbackComp f g) M]
  exact chase4 _ _ _ _ ((pullbackCompDerivedIso f g).hom_inv_id_app _)

/-- The formal identity left over in `supportCohomologyDerivedIso_comp_counit` once the five
naturality squares and counit triangles are inserted.  Stated at an arbitrary category. -/
private theorem chase5 {D : Type*} [Category* D] {z0 z1 z2 z3 z4 z5 z6 z7 z8 z9 : D}
    (A1 : z0 ⟶ z1) (A2 : z1 ⟶ z2) (A3 : z2 ⟶ z3) (A4 : z3 ⟶ z4) (ep : z4 ⟶ z5)
    (epMid : z3 ⟶ z6) (sc : z6 ⟶ z5) (B : z2 ⟶ z7) (σf : z7 ⟶ z6) (De : z1 ⟶ z8)
    (Dσg : z8 ⟶ z7) (Dep : z0 ⟶ z9) (αs : z9 ⟶ z8) (σH : z9 ⟶ z5)
    (ha : A4 ≫ ep = epMid ≫ sc) (hb : A3 ≫ epMid = B ≫ σf) (hc : A2 ≫ B = De ≫ Dσg)
    (hd : A1 ≫ De = Dep ≫ αs) (he : αs ≫ Dσg ≫ σf ≫ sc = σH) :
    (A1 ≫ A2 ≫ A3 ≫ A4) ≫ ep = Dep ≫ σH := by
  have hb' := reassoc_of% hb
  have hc' := reassoc_of% hc
  have hd' := reassoc_of% hd
  simp only [Category.assoc, ha, hb', hc', hd', he]

variable (T : Set X.carrier) (hT : IsClosed T)

/-- **The composite route satisfies the counit equation of `supportCohomologyDerivedIso`.**
The two counit triangles, the naturality of the counit on `X''`, the naturality of the
identification of `D((f ≫ g)^*)` with `D(g^*) ⋙ D(f^*)`, and the composition law
`mapDerivedCategorySingleFunctor_modulePullback_comp` for the single-complex comparison. -/
private theorem supportCohomologyDerivedIso_comp_counit
    (M : SheafOfModules.{u} (structureSheafRing X)) :
    ((pullbackCompDerivedIso f g).hom.app
          ((derivedSupportedPushforward X T hT).obj
            ((DerivedCategory.singleFunctor
              (SheafOfModules.{u} (structureSheafRing X)) 0).obj M)) ≫
        (modulePullback f).mapDerivedCategory.map ((supportCohomologyDerivedIso g T hT M).hom) ≫
          (supportCohomologyDerivedIso f (closedSubsetPreimage g T)
              (isClosed_closedSubsetPreimage g T hT) ((modulePullback g).obj M)).hom ≫
            (derivedSupportedPushforward X'' (closedSubsetPreimage f (closedSubsetPreimage g T))
                (isClosed_closedSubsetPreimage f (closedSubsetPreimage g T)
                  (isClosed_closedSubsetPreimage g T hT))).map
              ((DerivedCategory.singleFunctor
                  (SheafOfModules.{u} (structureSheafRing X'')) 0).map
                ((Stacks.DerivedPullback.Composition.modulePullbackComp f g).hom.app M))) ≫
        (derivedPushforwardAdjunction X''
            (closedSubsetPreimage f (closedSubsetPreimage g T))
            (isClosed_closedSubsetPreimage f (closedSubsetPreimage g T)
              (isClosed_closedSubsetPreimage g T hT))).counit.app
          ((DerivedCategory.singleFunctor
            (SheafOfModules.{u} (structureSheafRing X'')) 0).obj
              ((modulePullback (f ≫ g)).obj M)) =
      (modulePullback (f ≫ g)).mapDerivedCategory.map
          ((derivedPushforwardAdjunction X T hT).counit.app
            ((DerivedCategory.singleFunctor
              (SheafOfModules.{u} (structureSheafRing X)) 0).obj M)) ≫
        ((modulePullback (f ≫ g)).mapDerivedCategorySingleFunctor 0).hom.app M := by
  have ha := (derivedPushforwardAdjunction X''
    (closedSubsetPreimage f (closedSubsetPreimage g T))
    (isClosed_closedSubsetPreimage f (closedSubsetPreimage g T)
      (isClosed_closedSubsetPreimage g T hT))).counit.naturality
      ((DerivedCategory.singleFunctor (SheafOfModules.{u} (structureSheafRing X'')) 0).map
        ((Stacks.DerivedPullback.Composition.modulePullbackComp f g).hom.app M))
  have hb := supportCohomologyDerivedIso_hom_comp_counit f (closedSubsetPreimage g T)
    (isClosed_closedSubsetPreimage g T hT) ((modulePullback g).obj M)
  have hc0 := supportCohomologyDerivedIso_hom_comp_counit g T hT M
  dsimp only [derivedSupportedPushforward, Functor.comp_obj, Functor.comp_map,
    Functor.id_map, Functor.id_obj] at hc0
  have hc := congrArg (fun φ => (modulePullback f).mapDerivedCategory.map φ) hc0
  simp only [Functor.map_comp] at hc
  have hd := ((pullbackCompDerivedIso f g).hom.naturality
    ((derivedPushforwardAdjunction X T hT).counit.app
      ((DerivedCategory.singleFunctor
        (SheafOfModules.{u} (structureSheafRing X)) 0).obj M))).symm
  have he := mapDerivedCategorySingleFunctor_modulePullback_comp f g M
  dsimp only [derivedSupportedPushforward, Functor.comp_map, Functor.comp_obj,
    Functor.id_map, Functor.id_obj] at ha hb hc hd he ⊢
  exact chase5 _ _ _ _ _ _ _ _ _ _ _ _ _ _ ha hb hc hd he

/-- **"An exact functor commutes with `Hⁿ`" along a composite of open immersions.**  The
inverse comparison for `f ≫ g`, followed by `Hⁿ` of the identification of `D((f ≫ g)^*)` with
`D(g^*) ⋙ D(f^*)`, is the underived composition isomorphism followed by the inverse comparisons
for `g` and for `f`.

This is `CategoryTheory.Functor.mapDerivedCategoryHomologyFunctorIso_comp_app` and
`…_isoOfNatIso_app` read through `mapDerivedCategoryHomologyIso_eq` and inverted. -/
theorem mapDerivedCategoryHomologyIso_comp (n : ℤ)
    (A : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))) :
    (mapDerivedCategoryHomologyIso (modulePullback (f ≫ g)) n).inv.app A ≫
        (DerivedCategory.homologyFunctor (SheafOfModules.{u} (structureSheafRing X'')) n).map
          ((pullbackCompDerivedIso f g).hom.app A) =
      (Stacks.DerivedPullback.Composition.modulePullbackComp f g).inv.app
            ((DerivedCategory.homologyFunctor
              (SheafOfModules.{u} (structureSheafRing X)) n).obj A) ≫
        (modulePullback f).map
            ((mapDerivedCategoryHomologyIso (modulePullback g) n).inv.app A) ≫
          (mapDerivedCategoryHomologyIso (modulePullback f) n).inv.app
            ((modulePullback g).mapDerivedCategory.obj A) := by
  refine inv_of_comp3
    ((DerivedCategory.homologyFunctor (SheafOfModules.{u} (structureSheafRing X'')) n).mapIso
      ((pullbackCompDerivedIso f g).app A).symm)
    ((mapDerivedCategoryHomologyIso (modulePullback (f ≫ g)) n).app A)
    ((mapDerivedCategoryHomologyIso (modulePullback f) n).app
      ((modulePullback g).mapDerivedCategory.obj A))
    ((modulePullback f).mapIso ((mapDerivedCategoryHomologyIso (modulePullback g) n).app A))
    ((Stacks.DerivedPullback.Composition.modulePullbackComp f g).app
      ((DerivedCategory.homologyFunctor (SheafOfModules.{u} (structureSheafRing X)) n).obj A)) ?_
  simp only [mapDerivedCategoryHomologyIso_eq, Iso.app_hom, Functor.mapIso_hom]
  show (DerivedCategory.homologyFunctor (SheafOfModules.{u} (structureSheafRing X'')) n).map
        ((mapDerivedCategoryCompIso (modulePullback g) (modulePullback f)).inv.app A ≫
          (mapDerivedCategoryIsoOfNatIso (modulePullback g ⋙ modulePullback f)
              (modulePullback (f ≫ g))
              (Stacks.DerivedPullback.Composition.modulePullbackComp f g)).hom.app A) ≫ _ = _
  rw [Functor.map_comp, Category.assoc,
    Functor.mapDerivedCategoryHomologyFunctorIso_isoOfNatIso_app, ← Category.assoc,
    Functor.mapDerivedCategoryHomologyFunctorIso_comp_app, Category.assoc]

/-- **Transitivity of the derived isomorphism.**  `supportCohomologyDerivedIso` for `f ≫ g` is
the one for `g`, read inside `D(f^*)`, followed by the one for `f` at `g^* M`, with the
identification of `D((f ≫ g)^*)` with `D(g^*) ⋙ D(f^*)` at the source and the underived
composition isomorphism at the target.

Proved from the uniqueness `supportCohomologyDerived_hom_ext`: both sides satisfy the counit
equation of `supportCohomologyDerivedIso_hom_comp_counit`. -/
theorem supportCohomologyDerivedIso_comp (M : SheafOfModules.{u} (structureSheafRing X)) :
    (supportCohomologyDerivedIso (f ≫ g) T hT M).hom =
      (pullbackCompDerivedIso f g).hom.app
          ((derivedSupportedPushforward X T hT).obj
            ((DerivedCategory.singleFunctor
              (SheafOfModules.{u} (structureSheafRing X)) 0).obj M)) ≫
        (modulePullback f).mapDerivedCategory.map ((supportCohomologyDerivedIso g T hT M).hom) ≫
          (supportCohomologyDerivedIso f (closedSubsetPreimage g T)
              (isClosed_closedSubsetPreimage g T hT) ((modulePullback g).obj M)).hom ≫
            (derivedSupportedPushforward X'' (closedSubsetPreimage f (closedSubsetPreimage g T))
                (isClosed_closedSubsetPreimage f (closedSubsetPreimage g T)
                  (isClosed_closedSubsetPreimage g T hT))).map
              ((DerivedCategory.singleFunctor
                  (SheafOfModules.{u} (structureSheafRing X'')) 0).map
                ((Stacks.DerivedPullback.Composition.modulePullbackComp f g).hom.app M)) :=
  supportCohomologyDerived_hom_ext (f ≫ g) T hT M _ _
    ((supportCohomologyDerivedIso_hom_comp_counit (f ≫ g) T hT M).trans
      (supportCohomologyDerivedIso_comp_counit f g T hT M).symm)

/-- The formal identity left over in `supportCohomologyPullbackIso_comp` once the comparison
law for `Hⁿ` and the naturality of that comparison are inserted.  Stated at an arbitrary
category. -/
private theorem chase6 {D : Type*} [Category* D] {z0 z1 z2 z3 z4 z5 y1 y2 y3 : D}
    (a : z0 ⟶ z1) (b : z1 ⟶ z2) (d : z2 ⟶ z3) (e2 : z3 ⟶ z4) (f2 : z4 ⟶ z5)
    (p : z0 ⟶ y1) (q : y1 ⟶ y2) (r : y2 ⟶ y3) (t : y3 ⟶ z3) (u : y2 ⟶ z2)
    (k1 : a ≫ b = p ≫ q ≫ u) (k2 : r ≫ t = u ≫ d) :
    a ≫ b ≫ d ≫ e2 ≫ f2 = p ≫ q ≫ r ≫ t ≫ e2 ≫ f2 := by
  rw [reassoc_of% k1, ← reassoc_of% k2]

/-- Splitting a functor over a two-fold composite given as a hypothesis.  Stated at arbitrary
categories: applied as a term, it is checked at default transparency, where `rw` and `simp`
cannot see through the two spellings of a composite functor. -/
private theorem map_comp2 {D E : Type*} [Category* D] [Category* E] (F : D ⥤ E)
    {a b c0 : D} {m : a ⟶ c0} (x : a ⟶ b) (y : b ⟶ c0) (h : m = x ≫ y) :
    F.map m = F.map x ≫ F.map y := by
  rw [h, Functor.map_comp]

/-- Splitting a functor over a four-fold composite given as a hypothesis.  Stated at arbitrary
categories, for the reason given at `map_comp2`. -/
private theorem map_comp4 {D E : Type*} [Category* D] [Category* E] (F : D ⥤ E)
    {a b c0 d0 e0 : D} {m : a ⟶ e0} (x : a ⟶ b) (y : b ⟶ c0) (z : c0 ⟶ d0) (w : d0 ⟶ e0)
    (h : m = x ≫ y ≫ z ≫ w) :
    F.map m = F.map x ≫ F.map y ≫ F.map z ≫ F.map w := by
  rw [h]
  simp only [Functor.map_comp]

/-- The forward map of `supportCohomologyPullbackIso` is the inverse comparison for `Hⁿ`
followed by `Hⁿ` of `supportCohomologyDerivedIso`. -/
private theorem supportCohomologyPullbackIso_hom_eq {X' X : RingedSpace.{u, u}} (f : X' ⟶ X)
    [SheafedSpace.IsOpenImmersion f] (T : Set X.carrier) (hT : IsClosed T) (n : ℤ)
    (M : SheafOfModules.{u} (structureSheafRing X)) :
    (supportCohomologyPullbackIso f T hT n M).hom =
      (mapDerivedCategoryHomologyIso (modulePullback f) n).inv.app _ ≫
        (DerivedCategory.homologyFunctor (SheafOfModules.{u} (structureSheafRing X')) n).map
          ((supportCohomologyDerivedIso f T hT M).hom) := rfl

/-- **Transitivity of the excision for `i_*ℋ ⁿ_T` along a composite of open immersions.**  For
`f : X'' ⟶ X'` and `g : X' ⟶ X` open immersions of ringed spaces, `T ⊆ X` closed and `M` a sheaf
of modules on `X`, the excision isomorphism

`(f ≫ g)^*(i_*ℋ ⁿ_T(M)) ≅ i''_*ℋ ⁿ_{T''}(((f ≫ g)^* M))`

of `Stacks.Gysin.supportCohomologyPullbackIso` for `f ≫ g` is the one for `g`, pulled back along
`f`, followed by the one for `f` at `g^* M`, with the underived composition isomorphism
`Stacks.DerivedPullback.Composition.modulePullbackComp` of the pullbacks of modules at the source
and at the target.  **This is the transitivity over two nested opens** `V ≤ W ≤ X` that the
two-chart comparison of [Stacks, Tag 0G86] needs: take `g` the inclusion of `W` in `X` and `f`
the inclusion of `V` in `W`.

The two transports are the only identifications in the statement, and both are canonical: the
pullback of modules along a composite is the composite of the pullbacks.  Nothing in the
statement mentions the derived category.

Proved from `supportCohomologyDerivedIso_comp`, which is the same statement one level up in the
derived category, read in degree `n` through `mapDerivedCategoryHomologyIso_comp`. -/
theorem supportCohomologyPullbackIso_comp (n : ℤ)
    (M : SheafOfModules.{u} (structureSheafRing X)) :
    (supportCohomologyPullbackIso (f ≫ g) T hT n M).hom =
      (Stacks.DerivedPullback.Composition.modulePullbackComp f g).inv.app
          ((DerivedCategory.homologyFunctor
              (SheafOfModules.{u} (structureSheafRing X)) n).obj
            ((derivedSupportedPushforward X T hT).obj
              ((DerivedCategory.singleFunctor
                (SheafOfModules.{u} (structureSheafRing X)) 0).obj M))) ≫
        (modulePullback f).map ((supportCohomologyPullbackIso g T hT n M).hom) ≫
          (supportCohomologyPullbackIso f (closedSubsetPreimage g T)
              (isClosed_closedSubsetPreimage g T hT) n ((modulePullback g).obj M)).hom ≫
            (DerivedCategory.homologyFunctor
                (SheafOfModules.{u} (structureSheafRing X'')) n).map
              ((derivedSupportedPushforward X''
                  (closedSubsetPreimage f (closedSubsetPreimage g T))
                  (isClosed_closedSubsetPreimage f (closedSubsetPreimage g T)
                    (isClosed_closedSubsetPreimage g T hT))).map
                ((DerivedCategory.singleFunctor
                    (SheafOfModules.{u} (structureSheafRing X'')) 0).map
                  ((Stacks.DerivedPullback.Composition.modulePullbackComp f g).hom.app M))) := by
  have hsplit := map_comp4 (DerivedCategory.homologyFunctor
    (SheafOfModules.{u} (structureSheafRing X'')) n) _ _ _ _
    (supportCohomologyDerivedIso_comp f g T hT M)
  have hsplit2 := map_comp2 (modulePullback f) _ _ (supportCohomologyPullbackIso_hom_eq g T hT n M)
  have k1 := mapDerivedCategoryHomologyIso_comp f g n
    ((derivedSupportedPushforward X T hT).obj
      ((DerivedCategory.singleFunctor (SheafOfModules.{u} (structureSheafRing X)) 0).obj M))
  have k2 := (mapDerivedCategoryHomologyIso (modulePullback f) n).inv.naturality
    ((supportCohomologyDerivedIso g T hT M).hom)
  dsimp only [Functor.comp_map, Functor.comp_obj] at k2
  rw [supportCohomologyPullbackIso_hom_eq (f ≫ g), hsplit,
    supportCohomologyPullbackIso_hom_eq f, hsplit2]
  simp only [Category.assoc]
  exact chase6 _ _ _ _ _ _ _ _ _ _ k1 k2

end ThetaComp

end Stacks.Gysin

end
