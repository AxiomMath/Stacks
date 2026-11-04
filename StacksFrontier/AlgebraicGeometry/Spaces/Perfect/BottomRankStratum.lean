module

public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.RingedSite
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedModulePullback
public import StacksFrontier.CategoryTheory.Sites.Modules.FiniteLocallyFreeOfRank

/-!
# The locus on an algebraic space where the bottom cohomology of a derived pullback is free

Let `X` be an algebraic space over a scheme `S` contained in a big fppf site `B`, let `E` be an
object of the derived category of `𝒪_X`-modules on the small étale site of `X`, let `a` be an
integer and let `r` be a natural number. A morphism `f : Y ⟶ X` of algebraic spaces is
*universally of bottom rank `r`* when, for every further morphism `g : Y' ⟶ Y`, the
`𝒪_{Y'}`-module `H^a(L(g ∘ f)^* E)` is finite locally free of rank `r` in the sense of the rank
clause of [stacks 0409]. A morphism `j : Z ⟶ X` which is an immersion of algebraic spaces is a
*bottom rank `r` stratum* for `E` in degree `a` when `H^a(Lj^* E)` is finite locally free of rank
`r` and a morphism `f : Y ⟶ X` factors through `j` exactly when it is universally of bottom rank
`r`. These are the two descriptions by which [stacks 0D21] characterises its locally closed
subspace.

Three things are proved about this notion, and all three are unconditional. Being universally of
bottom rank `r` is stable under precomposition, and at the identity it gives back finite local
freeness of rank `r` of `H^a(Lf^* E)`. A bottom rank `r` stratum is itself universally of bottom
rank `r`, because it factors through itself through the identity. And the two descriptions
determine the stratum: any two bottom rank `r` strata for the same data are related by a unique
isomorphism over `X`, because an immersion of algebraic spaces is a monomorphism of presheaves.

The existence of a stratum is not unconditional, and the two inputs it needs are carried as named
hypotheses, in the manner of
`AlgebraicGeometry.Space.isEtaleLocallyConstructible_setOf_eq` and of the derived
pullback-stalk comparison of
`StacksFrontier/AlgebraicGeometry/Spaces/GeometricStalkCohomologyMap.lean`. The first,
`AlgebraicGeometry.Space.BottomRankStratum.HasDerivedModulePullbacks`, is the existence of
`Lf^*` itself: the derived pullback of
`AlgebraicGeometry.Space.smallEtaleDerivedModulePullback` carries
`CategoryTheory.Functor.HasLeftDerivedFunctor` as a premise, which nothing in this development
discharges for a morphism of algebraic spaces, so even the statement needs it. The second,
`AlgebraicGeometry.Space.BottomRankStratum.BottomRankBaseChange`, is the derived-pullback
computation: that rank `r` local freeness of `H^a(Lf^* E)` is inherited by further pullbacks.
Under it the universal condition of description (2) collapses to the plain one, and a subspace
representing the plain condition is a bottom rank `r` stratum.

## Main definitions

* `AlgebraicGeometry.Space.BottomRankStratum.HasDerivedModulePullbacks`: the premise that the
  derived pullback `Lf^*` of [stacks 06YY] exists for every morphism of algebraic spaces.
* `AlgebraicGeometry.Space.BottomRankStratum.pullbackHomology`: the `𝒪_Y`-module
  `H^a(Lf^* E)`.
* `AlgebraicGeometry.Space.BottomRankStratum.IsUniversallyFreeBottom`: the condition on
  `f : Y ⟶ X` that `H^a(L(g ∘ f)^* E)` be finite locally free of rank `r` for every
  `g : Y' ⟶ Y`.
* `AlgebraicGeometry.Space.BottomRankStratum.BottomRankBaseChange`: the derived-pullback
  computation, as the statement that rank `r` local freeness of `H^a(Lf^* E)` passes to
  `H^a(L(g ∘ f)^* E)`.
* `AlgebraicGeometry.Space.BottomRankStratum.IsBottomRankStratum`: the condition on a morphism
  `j : Z ⟶ X` of being an immersion satisfying the two descriptions above.

## Main results

* `AlgebraicGeometry.Space.BottomRankStratum.IsUniversallyFreeBottom.comp` and
  `AlgebraicGeometry.Space.BottomRankStratum.IsUniversallyFreeBottom.self`: the condition is
  stable under precomposition, and implies finite local freeness of rank `r` of `H^a(Lf^* E)`.
* `AlgebraicGeometry.Space.BottomRankStratum.IsBottomRankStratum.isUniversallyFreeBottom`: a
  bottom rank `r` stratum is itself universally of bottom rank `r`.
* `AlgebraicGeometry.Space.BottomRankStratum.IsBottomRankStratum.existsUnique_iso`: two bottom
  rank `r` strata for the same data are related by a unique isomorphism over `X`.
* `AlgebraicGeometry.Space.BottomRankStratum.isUniversallyFreeBottom_iff`: under the
  derived-pullback computation the universal condition is the plain one.
* `AlgebraicGeometry.Space.BottomRankStratum.isBottomRankStratum_id`: the identity of `X` is a
  bottom rank `r` stratum as soon as `H^a(L(𝟙_X)^* E)` is finite locally free of rank `r`.

## Implementation notes

The rank is a natural number, where the source says `r ≥ 0`.

The universal condition quantifies over all morphisms `g : Y' ⟶ Y` out of the source rather than
asking finite local freeness of `H^a(Lf^* E)` alone. That is what the source asks, and on a
general `E` the two are not the same: the bottom cohomology of a derived pullback is not the
pullback of the bottom cohomology. Making them the same is exactly the content of
`BottomRankBaseChange`.

**The two spellings of the structure sheaf.** The derived pullback is stated over
`AlgebraicGeometry.Space.ringedToposStructureRingSheaf`, the structure sheaf of the small étale
*ringed topos* with commutativity forgotten, while the rank clause of [stacks 0409] is stated
over `AlgebraicGeometry.RingedSite.ringSheaf` of
`AlgebraicGeometry.Space.smallEtaleRingedSite`. The two are definitionally equal — the
implementation note of
`StacksFrontier/AlgebraicGeometry/Spaces/SmallEtaleDerivedModulePullback.lean` that denies it is
stale — so a module produced by the first is fed to the second with no bridge. The types here
are written in the first spelling, which is the one the derived pullback and its instances
resolve against.

The derived category model is `CategoryTheory.HasDerivedCategory.standard`, installed as a local
instance, as it is in the file defining the derived pullback; a statement proved at one model of
`HasDerivedCategory` says nothing about another.

**Why `E` carries no hypothesis.** The source takes `E` perfect of Tor amplitude in `[a, b]`.
Nothing below uses either, and the statements are correspondingly stated for an arbitrary object
of `D(𝒪_X)`: perfectness and the Tor amplitude are what power the construction of `Z`, which is
not carried out here.

### Relation to [stacks 0D21]

The tag asserts, for `E` perfect of Tor amplitude in `[a, b]`, the existence of a locally closed
subspace `j : Z ⟶ X` with descriptions (1) and (2), together with its finite presentation, the
base-change formula (3), and, when `β_a ≤ r` everywhere, the closedness of `j` and the
equivalence of (4)(a), (4)(b) and — for `r = 1` — (4)(c). This file registers no part of it; the
tag is proved in `StacksFrontier/AlgebraicGeometry/Spaces/Perfect/BottomRankStratumExistence.lean`
as `AlgebraicGeometry.Space.BottomRankLocus.exists_isBottomRankStratum_isFinitePresentation`.

`IsBottomRankStratum.existsUnique_iso` is the uniqueness carried by the word "characterized"; as
in the scheme case it is a consequence of description (2), not a part of the tag, and is
untagged. `isBottomRankStratum_id` is the degenerate case `Z = X`, an instance of descriptions
(1) and (2) under the derived-pullback computation alone. It is untagged because it omits the finite
presentation of `j`, which for the identity would be quasi-compactness and quasi-separatedness of
`X` over itself and is not proved here.

## References

* [The Stacks Project, Lemma 75.26.6 (0D21)](https://stacks.math.columbia.edu/tag/0D21)
* [The Stacks Project, Lemma 36.31.4 (0BDL)](https://stacks.math.columbia.edu/tag/0BDL)
* [The Stacks Project, Section 03G8](https://stacks.math.columbia.edu/tag/03G8)
* [The Stacks Project, Section 06YY](https://stacks.math.columbia.edu/tag/06YY)
* [The Stacks Project, Definition 0409](https://stacks.math.columbia.edu/tag/0409)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space.BottomRankStratum

attribute [local instance 10000] HasDerivedCategory.standard

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The derived pullback premise -/

/-- **The derived pullback `Lf^*` exists for every morphism of algebraic spaces.**

`AlgebraicGeometry.Space.smallEtaleDerivedModulePullback` carries
`CategoryTheory.Functor.HasLeftDerivedFunctor` as an instance premise, and nothing in this
development discharges it for a morphism of algebraic spaces: what would is a resolving datum at
the K-flat class, which [stacks 06YS] supplies only for a site which is
`CategoryTheory.SmallCategory`, and the small étale site of an algebraic space is only
essentially small. Every statement below about `H^a(Lf^* E)` therefore carries this premise. -/
def HasDerivedModulePullbacks : Prop :=
  ∀ {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y),
    (smallEtaleModulePullbackOnHomotopy B S hS f).HasLeftDerivedFunctor
      (smallEtaleModuleQuasiIso B S hS Y)

variable {B S hS}

/-! ### The bottom cohomology of a derived pullback -/

/-- **The `𝒪_Y`-module `H^a(Lf^* E)`.** The degree-`a` cohomology sheaf of the derived pullback
of `E` along `f : Y ⟶ X`. -/
def pullbackHomology (hL : HasDerivedModulePullbacks B S hS) {X : AlgebraicSpaces B S hS}
    (E : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))) (a : ℤ)
    {Y : AlgebraicSpaces B S hS} (f : Y ⟶ X) :
    SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y) :=
  haveI := hL f
  (DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)) a).obj
    ((smallEtaleDerivedModulePullback B S hS f).obj E)

/-! ### Morphisms universally of bottom rank `r` -/

/-- **A morphism universally of bottom rank `r`.** The morphism `f : Y ⟶ X` is universally of
bottom rank `r` for `E` in degree `a` when, for every morphism `g : Y' ⟶ Y`, the
`𝒪_{Y'}`-module `H^a(L(g ∘ f)^* E)` is finite locally free of rank `r`.

This is the right-hand side of description (2) of [stacks 0D21]. -/
def IsUniversallyFreeBottom (hL : HasDerivedModulePullbacks B S hS)
    {X : AlgebraicSpaces B S hS}
    (E : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)))
    (a : ℤ) (r : ℕ) {Y : AlgebraicSpaces B S hS} (f : Y ⟶ X) : Prop :=
  ∀ (Y' : AlgebraicSpaces B S hS) (g : Y' ⟶ Y),
    RingedSite.IsFiniteLocallyFreeOfRank (smallEtaleRingedSite B S hS Y'.1 Y'.2)
      (pullbackHomology hL E a (g ≫ f)) r

/-- **The derived-pullback computation.** Rank `r` local freeness of `H^a(Lf^* E)` passes to
`H^a(L(g ∘ f)^* E)` for every further `g : Y' ⟶ Y`.

This is the part of the base-change formula (3) of [stacks 0D21] that the characterisation uses.
It is not available in this development: computing `L(g ∘ f)^*` from `Lf^*` needs the
composition isomorphism of [stacks 0D6D], which presents a morphism of ringed topoi by a functor
of the underlying sites, and `AlgebraicGeometry.Space.smallEtaleRingedToposHom` carries no such
presentation. -/
def BottomRankBaseChange (hL : HasDerivedModulePullbacks B S hS)
    {X : AlgebraicSpaces B S hS}
    (E : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)))
    (a : ℤ) (r : ℕ) : Prop :=
  ∀ {Y Y' : AlgebraicSpaces B S hS} (f : Y ⟶ X) (g : Y' ⟶ Y),
    RingedSite.IsFiniteLocallyFreeOfRank (smallEtaleRingedSite B S hS Y.1 Y.2)
      (pullbackHomology hL E a f) r →
    RingedSite.IsFiniteLocallyFreeOfRank (smallEtaleRingedSite B S hS Y'.1 Y'.2)
      (pullbackHomology hL E a (g ≫ f)) r

variable {hL : HasDerivedModulePullbacks B S hS} {X : AlgebraicSpaces B S hS}
  {E : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))}
  {a : ℤ} {r : ℕ}

/-- **Being universally of bottom rank `r` is stable under precomposition.** The condition for
`g ∘ f` quantifies over the morphisms `k` and asks about `(k ∘ g) ∘ f`, so it is the condition
for `f` read at the composites `k ∘ g`. -/
theorem IsUniversallyFreeBottom.comp {Y Y' : AlgebraicSpaces B S hS} {f : Y ⟶ X}
    (h : IsUniversallyFreeBottom hL E a r f) (g : Y' ⟶ Y) :
    IsUniversallyFreeBottom hL E a r (g ≫ f) := by
  intro Y'' k
  simpa only [Category.assoc] using h Y'' (k ≫ g)

/-- **A morphism universally of bottom rank `r` has `H^a(Lf^* E)` finite locally free of rank
`r`.** This is the condition at the identity. -/
theorem IsUniversallyFreeBottom.self {Y : AlgebraicSpaces B S hS} {f : Y ⟶ X}
    (h : IsUniversallyFreeBottom hL E a r f) :
    RingedSite.IsFiniteLocallyFreeOfRank (smallEtaleRingedSite B S hS Y.1 Y.2)
      (pullbackHomology hL E a f) r := by
  simpa only [Category.id_comp] using h Y (𝟙 Y)

/-- **Under the derived-pullback computation the universal condition is the plain one.** The
quantification over further morphisms in description (2) of [stacks 0D21] costs nothing as soon
as rank `r` local freeness of the bottom cohomology is inherited by further pullbacks. -/
theorem isUniversallyFreeBottom_iff (hbc : BottomRankBaseChange hL E a r)
    {Y : AlgebraicSpaces B S hS} (f : Y ⟶ X) :
    IsUniversallyFreeBottom hL E a r f ↔
      RingedSite.IsFiniteLocallyFreeOfRank (smallEtaleRingedSite B S hS Y.1 Y.2)
        (pullbackHomology hL E a f) r :=
  ⟨fun h => h.self, fun h _ g => hbc f g h⟩

/-! ### Bottom rank strata and their uniqueness -/

/-- **A bottom rank `r` stratum.** The morphism `j : Z ⟶ X` is an immersion of algebraic spaces,
`H^a(Lj^* E)` is finite locally free of rank `r`, and a morphism `f : Y ⟶ X` factors through `j`
exactly when it is universally of bottom rank `r`.

These are the two descriptions by which [stacks 0D21] characterises its locally closed subspace;
the tag's assertion that such a `j` exists for `E` perfect of Tor amplitude in `[a, b]` is
`AlgebraicGeometry.Space.BottomRankLocus.exists_isBottomRankStratum_isFinitePresentation`, for
the bottom rank stratum of that namespace. -/
structure IsBottomRankStratum (hL : HasDerivedModulePullbacks B S hS)
    {X : AlgebraicSpaces B S hS}
    (E : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)))
    (a : ℤ) (r : ℕ) {Z : AlgebraicSpaces B S hS} (j : Z ⟶ X) : Prop where
  /-- `j` is an immersion, so `Z` is a locally closed subspace of `X`. -/
  isImmersion : IsImmersion B S hS j.hom
  /-- Description (1): `H^a(Lj^* E)` is finite locally free of rank `r`. -/
  freeRank : RingedSite.IsFiniteLocallyFreeOfRank (smallEtaleRingedSite B S hS Z.1 Z.2)
    (pullbackHomology hL E a j) r
  /-- Description (2): a morphism factors through `j` exactly when it is universally of bottom
  rank `r`. -/
  factorsThrough_iff : ∀ (Y : AlgebraicSpaces B S hS) (f : Y ⟶ X),
    (∃ g : Y ⟶ Z, g ≫ j = f) ↔ IsUniversallyFreeBottom hL E a r f

/-- **A bottom rank `r` stratum is itself universally of bottom rank `r`.** It factors through
itself through the identity, so description (2) applies to it. -/
theorem IsBottomRankStratum.isUniversallyFreeBottom {Z : AlgebraicSpaces B S hS} {j : Z ⟶ X}
    (h : IsBottomRankStratum hL E a r j) : IsUniversallyFreeBottom hL E a r j :=
  (h.factorsThrough_iff Z j).1 ⟨𝟙 Z, Category.id_comp j⟩

/-- **An immersion of algebraic spaces is a monomorphism.** An immersion of schemes is a
monomorphism, so an immersion of the site is one by faithfulness of the passage to schemes, so an
immersion of presheaves is one by
`CategoryTheory.MorphismProperty.presheaf_monomorphisms_le_monomorphisms`, and the category of
algebraic spaces is a full subcategory of presheaves. -/
theorem mono_of_isImmersion {Z : AlgebraicSpaces B S hS} {j : Z ⟶ X}
    (h : IsImmersion B S hS j.hom) : Mono j := by
  have hP : MorphismProperty.inverseImage
      (@AlgebraicGeometry.IsImmersion.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS) ≤
      MorphismProperty.monomorphisms (BigFppfOver B S hS) := by
    intro U V g hg
    have hmono : Mono ((BigFppfOver.toScheme B S hS).map g) := by
      have : AlgebraicGeometry.IsImmersion ((BigFppfOver.toScheme B S hS).map g) := hg
      infer_instance
    exact (BigFppfOver.toScheme B S hS).mono_of_mono_map hmono
  have hmono : Mono j.hom :=
    MorphismProperty.presheaf_monomorphisms_le_monomorphisms _
      (MorphismProperty.relative_monotone hP _ h)
  exact (ObjectProperty.ι _).mono_of_mono_map hmono

/-- **Description (2) determines the stratum.** Two bottom rank `r` strata for the same `E`, `a`
and `r` are related by a unique isomorphism over `X`.

Each stratum is universally of bottom rank `r`, so each factors through the other; the two
factorisations compose to the identity because an immersion is a monomorphism, and that same
monomorphism property makes the morphism over `X`, hence the isomorphism, unique. -/
theorem IsBottomRankStratum.existsUnique_iso {Z₁ Z₂ : AlgebraicSpaces B S hS} {j₁ : Z₁ ⟶ X}
    {j₂ : Z₂ ⟶ X} (h₁ : IsBottomRankStratum hL E a r j₁)
    (h₂ : IsBottomRankStratum hL E a r j₂) :
    ∃! e : Z₁ ≅ Z₂, e.hom ≫ j₂ = j₁ := by
  have m₁ : Mono j₁ := mono_of_isImmersion h₁.isImmersion
  have m₂ : Mono j₂ := mono_of_isImmersion h₂.isImmersion
  obtain ⟨g₁, hg₁⟩ := (h₂.factorsThrough_iff Z₁ j₁).2 h₁.isUniversallyFreeBottom
  obtain ⟨g₂, hg₂⟩ := (h₁.factorsThrough_iff Z₂ j₂).2 h₂.isUniversallyFreeBottom
  have h12 : g₁ ≫ g₂ = 𝟙 Z₁ := by
    refine (cancel_mono j₁).1 ?_
    rw [Category.assoc, hg₂, hg₁, Category.id_comp]
  have h21 : g₂ ≫ g₁ = 𝟙 Z₂ := by
    refine (cancel_mono j₂).1 ?_
    rw [Category.assoc, hg₁, hg₂, Category.id_comp]
  refine ⟨⟨g₁, g₂, h12, h21⟩, hg₁, fun e he => ?_⟩
  exact Iso.ext ((cancel_mono j₂).1 (he.trans hg₁.symm))

/-! ### Strata from the plain rank condition -/

/-- **A subspace representing the plain rank condition is a bottom rank `r` stratum.** Under the
derived-pullback computation the plain condition and the universal condition of description (2)
agree, and description (1) is the plain condition read at `j` itself. -/
theorem isBottomRankStratum_of_factorsThrough_iff (hbc : BottomRankBaseChange hL E a r)
    {Z : AlgebraicSpaces B S hS} {j : Z ⟶ X} (hj : IsImmersion B S hS j.hom)
    (hfactor : ∀ (Y : AlgebraicSpaces B S hS) (f : Y ⟶ X),
      (∃ g : Y ⟶ Z, g ≫ j = f) ↔
        RingedSite.IsFiniteLocallyFreeOfRank (smallEtaleRingedSite B S hS Y.1 Y.2)
          (pullbackHomology hL E a f) r) :
    IsBottomRankStratum hL E a r j where
  isImmersion := hj
  freeRank := (hfactor Z j).1 ⟨𝟙 Z, Category.id_comp j⟩
  factorsThrough_iff Y f := (hfactor Y f).trans (isUniversallyFreeBottom_iff hbc f).symm

/-! ### The degenerate stratum -/

/-- **The identity of an algebraic space is an immersion.** -/
theorem isImmersion_id (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) : IsImmersion B S hS (𝟙 F) := by
  have h₁ : MorphismProperty.ContainsIdentities (@AlgebraicGeometry.IsImmersion.{u}) :=
    (inferInstance :
      MorphismProperty.IsMultiplicative (@AlgebraicGeometry.IsImmersion.{u})).toContainsIdentities
  have h₂ : MorphismProperty.RespectsIso (@AlgebraicGeometry.IsImmersion.{u}) :=
    (inferInstance :
      MorphismProperty.IsStableUnderBaseChange (@AlgebraicGeometry.IsImmersion.{u})).respectsIso
  have h₃ : MorphismProperty.ContainsIdentities (MorphismProperty.inverseImage
      (@AlgebraicGeometry.IsImmersion.{u}) (BigFppfOver.toScheme B S hS)) :=
    MorphismProperty.ContainsIdentities.inverseImage _
  have h₄ : MorphismProperty.RespectsIso (MorphismProperty.inverseImage
      (@AlgebraicGeometry.IsImmersion.{u}) (BigFppfOver.toScheme B S hS)) :=
    MorphismProperty.RespectsIso.inverseImage _ _
  exact MorphismProperty.relative.of_exists
    (fun Y g => ⟨Y, g, 𝟙 Y, by simpa using IsPullback.of_id_snd, h₃.id_mem Y⟩)

/-- **The identity of `X` is a bottom rank `r` stratum as soon as `H^a(L(𝟙_X)^* E)` is finite
locally free of rank `r`.** Every morphism to `X` factors through the identity, and under the
derived-pullback computation every morphism is then universally of bottom rank `r`.

This is the degenerate case `Z = X` of [stacks 0D21]. The hypothesis is phrased at `𝟙 X` rather
than at `E` itself because this development has no identity isomorphism for the derived pullback
of an algebraic space: `H^a(L(𝟙_X)^* E)` is not known here to be `H^a(E)`. -/
theorem isBottomRankStratum_id (hbc : BottomRankBaseChange hL E a r)
    (hE : RingedSite.IsFiniteLocallyFreeOfRank (smallEtaleRingedSite B S hS X.1 X.2)
      (pullbackHomology hL E a (𝟙 X)) r) :
    IsBottomRankStratum hL E a r (𝟙 X) where
  isImmersion := isImmersion_id _
  freeRank := hE
  factorsThrough_iff Y f := by
    refine ⟨fun _ Y' g => ?_, fun _ => ⟨f, Category.comp_id f⟩⟩
    simpa only [Category.comp_id] using hbc (𝟙 X) (g ≫ f) hE

end AlgebraicGeometry.Space.BottomRankStratum

end
