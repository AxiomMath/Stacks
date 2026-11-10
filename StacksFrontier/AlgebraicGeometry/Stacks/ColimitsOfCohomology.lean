module

public import StacksFrontier.AlgebraicGeometry.Stacks.AffineCoveringFamily
public import StacksFrontier.AlgebraicGeometry.Stacks.ColimitsOfCohomologyAffineRefinement
public import StacksFrontier.AlgebraicGeometry.Stacks.ColimitsOfCohomologyAtlasCovers
public import StacksFrontier.AlgebraicGeometry.Stacks.ColimitsOfCohomologyEtaleAffineRefinement
public import StacksFrontier.CategoryTheory.Sites.Cohomology.FilteredColimits.FiniteCoveringCriterionOnALargeSite
public import StacksCore.Tactic.StacksAttribute

/-!
# Colimits and cohomology on an algebraic stack (Stacks 0GQV)

Stacks 0GQV says that on a quasi-compact and quasi-separated algebraic stack `𝒳` the comparison
`colim_i H^p(𝒳, F_i) ⟶ H^p(𝒳, colim_i F_i)` is an isomorphism for every filtered system `(F_i)`
of abelian sheaves, in the fppf topology and in the étale topology alike.

The source proves it by applying Stacks 0GN3 to the site `𝒳_τ`, checking its hypotheses through
Stacks 0GN4 with `B` the collection of objects of `𝒳_τ` lying over affine schemes. The site of a
category fibred in groupoids over the big fppf category of a scheme has objects in `Type (u + 1)`
and morphisms in `Type u`, so the small-site forms of Stacks 0GN3 and Stacks 0GN4 do not apply to
it at all; the forms for an arbitrary site do, the join of those two universes being `u + 1`, and
that is what is used here.

## Main definitions

* `AlgebraicGeometry.Stack.affineObjects`: the collection `B` of the source's proof, the objects
  of the site lying over affine schemes.

## Main results

* `AlgebraicGeometry.Stack.isIso_colimit_post_rightDerived_globalSections_associatedTopology`: the
  conclusion of **Stacks 0GQV** at the site `𝒳` inherits from an *arbitrary* topology on the
  underlying category of schemes, from all four conditions of Stacks 0GN4 on `affineObjects`. This
  is the site-theoretic step of the source's proof, which is the same for every topology.
* `AlgebraicGeometry.Stack.isIso_colimit_post_rightDerived_globalSections_fppf`: its fppf
  instance, from conditions (1), (3) and (4) — condition (2) being proved for the fppf site.
* `AlgebraicGeometry.Stack`
  `.isIso_colimit_post_rightDerived_globalSections_fppf_of_isQuasiCompactStack`: the same for a
  quasi-compact algebraic stack, from conditions (3) and (4) alone.
* `AlgebraicGeometry.Stack.isIso_colimit_post_rightDerived_globalSections_etale`: its étale
  instance, which is the *second* assertion of **Stacks 0GQV**, from conditions (1), (3) and (4)
  — condition (2) being proved for the étale site as well.

## What is proved and what is assumed

The site-theoretic half of Stacks 0GQV is complete, and complete for *both* of the topologies the
source asserts it in: the criterion is instantiated at the site `𝒳` inherits from an arbitrary
topology on the underlying category of schemes of `B`, with `B = affineObjects`, and the
conclusion is exactly the assertion of the source in that topology, for abelian sheaves and
filtered diagrams at the universe `u + 1` of the site's objects. Nothing in that step uses which
topology was chosen, so the fppf and the étale assertions of the source differ only in the four
conditions of Stacks 0GN4 fed to it.

In the **fppf** topology all four conditions of Stacks 0GN4 are now proved; the first two are
discharged in the results below and the last two are hypotheses there, discharged in the two
files named under (3) and (4). The source derives all four as follows.

1. A finite family of objects over affines whose sheafified representables cover the final sheaf.
   The source takes a single `x : U ⟶ 𝒳` with `U` affine and `x` surjective smooth, which
   quasi-compactness of `𝒳` provides by Stacks 04YC. This is **proved**, for a quasi-compact
   algebraic stack, by
   `AlgebraicGeometry.Stack.exists_isAffineObject_isLocallySurjective_terminal_from`.
2. Every covering of an object over an affine is refined by a finite covering family by objects
   over affines. This is Stacks 021P, transported to the inherited topology of Stacks 06TP, and is
   **proved** — for every category fibred in groupoids, no quasi-compactness needed — by
   `AlgebraicGeometry.Stack.hasFiniteCoverRefinementsFrom_fppfTopology`.
3. For `x, x'` over affines, a finite family over affines covering `h_x^# ⨯ h_{x'}^#`. The source
   covers the quasi-compact algebraic space `U ×_{x, 𝒳, x'} U'` by an affine; quasi-compactness of
   that fibre product is where quasi-separatedness of `𝒳` enters, by Stacks 075S, available as
   `AlgebraicGeometry.Stack.isQuasiCompactStack_and_isQuasiSeparatedOver_twoFibreProduct`.
4. For `a, b : x ⟶ x'` over affines, a finite family over affines covering the equalizer of
   `h_a^#` and `h_b^#`. The source identifies that equalizer with the one of the two underlying
   morphisms of schemes; that identification is loose, and what replaces it is the 2-fibre
   product of the two graphs of `a` and `b`, which is quasi-compact by Stacks 075S part (3).

Neither (3) nor (4) is carried out here, but neither needs any theory of representable
*sheaves*: both are reduced to conditions on the hom-sets of the site alone, by
`AlgebraicGeometry.Stack.isLocallySurjective_prodLift_fppfTopology_of_exists_covering` and
`AlgebraicGeometry.Stack.isLocallySurjective_equalizerLift_fppfTopology_of_exists_covering`. After
that reduction (3) asks of the finite family `V_i`, with morphisms `p_i : V_i ⟶ x` and
`q_i : V_i ⟶ x'`, that every *pair* of morphisms `α : y ⟶ x`, `β : y ⟶ x'` of the site factor,
after passing to a covering of `y`, through one `(p_i, q_i)`; and (4) asks of `p_i : V_i ⟶ x`
equalizing `a` and `b` that every `α : y ⟶ x` with `α ≫ a = α ≫ b` factor, after a covering,
through one `p_i`.

What each case then needs is the dictionary between those morphisms of the site and the 2-fibre
products of the source.

**For (3) that dictionary is complete and the condition is proved.** A pair `α : y ⟶ x`,
`β : y ⟶ x'` is the same thing as an object of `U ×_{x, 𝒳, x'} U'` over the scheme that `y` lies
over; that 2-fibre product is `AlgebraicGeometry.Stack.twoFibreProductAlgebraicStack` at the two
2-Yoneda 1-morphisms `AlgebraicGeometry.Stack.objectMorphism` of `x` and of `x'`, the
correspondence on objects is
`CategoryTheory.TwoFibreProductOver.TwoYonedaPair.exists_quadruple_of_hom_pair`, and the 2-fibre
product is quasi-compact by Stacks 075S part (3), hence has an affine smooth presentation by
Stacks 04YC. Condition (3) is
`AlgebraicGeometry.Stack.exists_fin_affineObjects_isLocallySurjective_prodLift`, in
`StacksFrontier/AlgebraicGeometry/Stacks/ColimitsOfCohomologyProductAffineCover.lean`.

**For (4) that dictionary is complete and the condition is proved as well, but the 2-fibre product
is not the one the source names.** The source identifies the equalizer with the one of the two
underlying morphisms of schemes, and that identification is loose: the pullback `ζ` of `x` along
the scheme-level equalizer of `p(a)` and `p(b)` need *not* satisfy `ζ ≫ a = ζ ≫ b`, the two
composites lying over the same base morphism but differing by an automorphism of the source of
`ζ`. The object that does classify the equalizing morphisms is the 2-fibre product
`U ×_{Γ_a, U ×_{x, 𝒳, x'} U', Γ_b} U` of the two graphs of `a` and of `b` over the 2-fibre product
(3) is about — a quasi-compact quasi-separated algebraic stack, not an affine scheme. Its
quasi-compactness genuinely uses the quasi-separatedness of `𝒳` the source never invokes at this
step, through
`AlgebraicGeometry.Stack.isQuasiSeparatedOver_twoFibreProductAlgebraicStack_objectMorphism` and
hence `AlgebraicGeometry.Stack.isQuasiSeparatedOver_schemeStack_of_isAffine`. The dictionary for
that 2-fibre product — the analogue of
`StacksFrontier/CategoryTheory/TwoFibreProduct/TwoYonedaPairs.lean`, on objects and on morphisms
alike — is `StacksFrontier/CategoryTheory/TwoFibreProduct/TwoYonedaGraphs.lean`, and condition
(4) is
`AlgebraicGeometry.Stack.exists_fin_affineObjects_isLocallySurjective_equalizerLift`, in
`StacksFrontier/AlgebraicGeometry/Stacks/ColimitsOfCohomologyEqualizerAffineCover.lean`.

The two hypotheses below are stated in exactly the shape
`Stacks.Cohomology.ColimitsOfCohomology.isIso_colimit_post_rightDerived_globalSections_of_covers`
consumes them, so each is discharged by a local edit at the call site; the fppf assertion of
Stacks 0GQV with both discharged, and so with quasi-compactness and quasi-separatedness as its
only hypotheses, is
`AlgebraicGeometry.Stack.isIso_colimit_post_rightDerived_globalSections_fppf_of_isQuasiCompact` in
that file.

### The étale assertion

The étale assertion of the source is the same statement with `AlgebraicGeometry.Stack`
`.associatedTopology` at the big étale topology `AlgebraicGeometry.etaleTopology` (Stacks 03FF) in
place of the big fppf topology, and it is stated here, as
`AlgebraicGeometry.Stack.isIso_colimit_post_rightDerived_globalSections_etale`. Conditions (1),
(3) and (4) of Stacks 0GN4 are hypotheses there, condition (2) being discharged as it is in the
fppf case. The four stand as follows.

1. **Proved**, in
   `StacksFrontier/AlgebraicGeometry/Stacks/ColimitsOfCohomologyAtlasCovers.lean`, by
   `AlgebraicGeometry.Stack.exists_isAffineObject_isLocallySurjective_terminal_from_etale`. The
   fppf proof reads sections of the affine smooth presentation of Stacks 04YC fppf-locally on the
   base, by Stacks 06QA; the étale proof reads them *étale*-locally, by **Stacks 06XH** part (2),
   `AlgebraicGeometry.Stack.exists_etaleCovering_fibre_lift`, which applies to a surjective
   *smooth* 1-morphism and so needs no more of the presentation than Stacks 04YC supplies.
2. **Proved**, in
   `StacksFrontier/AlgebraicGeometry/Stacks/ColimitsOfCohomologyEtaleAffineRefinement.lean`, by
   `AlgebraicGeometry.Stack.hasFiniteCoverRefinementsFrom_etaleTopology` — for every category
   fibred in groupoids, no quasi-compactness needed, exactly as its fppf counterpart. The fppf
   proof rests on `AlgebraicGeometry.exists_standardFppf_refinement` (Stacks 021P); the étale
   proof rests on **Stacks 0218** in the form
   `AlgebraicGeometry.BigEtaleSite.exists_finite_affine_refinement`, which is stated for a big
   *étale* site and is carried to the étale subcollection
   `AlgebraicGeometry.etaleCovering` of a big fppf site — the site this file works over — through
   `AlgebraicGeometry.BigFppfSite.toBigEtaleSite`.
3. and 4. **Open**, and open for the same reasons as their fppf counterparts below, which are
   about the 2-fibre products the source covers and not about the topology: the covering of those
   2-fibre products by affines would again be read off étale-locally by Stacks 06XH part (2) in
   place of Stacks 06QA.

## Implementation notes

The four facts about abelian sheaves at the join universe that make the conclusion a well-formed
statement — essential smallness of the site, left exact sheafification, enough injectives, and
additivity of global sections — are installed with `attribute [local instance]` from
`StacksFrontier/CategoryTheory/Sites/Cohomology/FilteredColimits/GlobalCohomologyOnALargeSite.lean`,
which is how that file asks a consumer to use them. All four are propositions, so no choice of
instance can clash with another.

## References

* [Stacks Project, Tag 0GQV](https://stacks.math.columbia.edu/tag/0GQV)
* [Stacks Project, Tag 0GN3](https://stacks.math.columbia.edu/tag/0GN3)
* [Stacks Project, Tag 0GN4](https://stacks.math.columbia.edu/tag/0GN4)
* [Stacks Project, Tag 0218](https://stacks.math.columbia.edu/tag/0218)
* [Stacks Project, Tag 021P](https://stacks.math.columbia.edu/tag/021P)
* [Stacks Project, Tag 03FF](https://stacks.math.columbia.edu/tag/03FF)
* [Stacks Project, Tag 04YC](https://stacks.math.columbia.edu/tag/04YC)
* [Stacks Project, Tag 06QA](https://stacks.math.columbia.edu/tag/06QA)
* [Stacks Project, Tag 06TP](https://stacks.math.columbia.edu/tag/06TP)
* [Stacks Project, Tag 06XH](https://stacks.math.columbia.edu/tag/06XH)
* [Stacks Project, Tag 075S](https://stacks.math.columbia.edu/tag/075S)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Cohomology.ColimitsOfCohomology

attribute [local instance] essentiallySmall_join hasSheafify_ab_join enoughInjectives_sheaf_join
  globalSections_additive_join

universe v₀ u₀

namespace AlgebraicGeometry.Stack

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
variable (𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS))

/-- The objects of the site of a category fibred in groupoids over the big fppf category of `S`
which lie over affine schemes. This is the collection `B` of the proof of Stacks 0GQV, and the
objects it collects are a covering family of the fppf site by
`AlgebraicGeometry.Stack.isCoveringFamily_isAffine_fppfTopology`.

The condition is the canonical `AlgebraicGeometry.Stack.IsAffineObject` of
`StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.AffineSite`, which is an
`CategoryTheory.ObjectProperty`; the criterion of Stacks 0GN4 consumes a `Set`, so the predicate is
packaged as one here and nothing else is added to it. -/
def affineObjects : Set 𝒳.val.obj :=
  {x | IsAffineObject B S hS 𝒳.val.p x}

/-- **Stacks 0GQV at any one of the sites of Stacks 06TP, from all four conditions of
Stacks 0GN4.** Let `𝒳` be a category fibred in groupoids over the big fppf category of a scheme
`S` contained in a big fppf site, let `τ` be a topology on the underlying category of schemes of
`B`, give the total category of `𝒳` the topology it inherits from `τ` localized at `S`
(Stacks 06TP), and assume of the collection `affineObjects` of its objects lying over affine
schemes that

1. finitely many of them have sheafified representables jointly covering the final sheaf,
2. every covering sieve of a member of it contains a finite covering family by members of it,
3. the product of the sheafified representables of two of them is covered by a finite coproduct of
   sheafified representables of members of it, and
4. the equalizer of the sheafified representables of two parallel morphisms between members of it
   is covered by such a finite coproduct.

Then `colim_i H^p(𝒳, F_i) ⟶ H^p(𝒳, colim_i F_i)` is an isomorphism in every degree `p`, for every
filtered diagram `F` of abelian sheaves on that site.

This is the site-theoretic step of the source's proof, and the source takes it at two values of
`τ`: the big fppf topology and the big étale topology. Nothing below uses which topology was
chosen — the step is an instance of
`Stacks.Cohomology.ColimitsOfCohomology.isIso_colimit_post_rightDerived_globalSections_of_covers`,
the form of Stacks 0GN4 for a site whose objects and morphisms do not share a universe, and the
site of a category fibred in groupoids over the big fppf category of `S` does not, its objects
lying in `Type (u + 1)` and its morphisms in `Type u`. Coefficients, sheaves of sets and the index
category of the diagram all live at the join `u + 1` of those two universes.

So the two assertions of the source differ only in the four conditions fed to this result. Its
fppf and étale instances are
`AlgebraicGeometry.Stack.isIso_colimit_post_rightDerived_globalSections_fppf`, where condition (2)
is discharged, and
`AlgebraicGeometry.Stack.isIso_colimit_post_rightDerived_globalSections_etale`, where none of the
four is; see "What is proved and what is assumed" in the module docstring for the state of each
condition in each topology. -/
@[stacks 0GQV "the site-theoretic step, at an arbitrary one of the five topologies of Stacks \
06TP, hence for the fppf and the étale assertion alike; all four conditions of 0GN4 are assumed \
here"]
theorem isIso_colimit_post_rightDerived_globalSections_associatedTopology
    (τ : GrothendieckTopology B.Schemes)
    (h_terminal : ∃ (m : ℕ) (U : Fin m → 𝒳.val.obj),
      (∀ i, U i ∈ affineObjects B S hS 𝒳) ∧
        Sheaf.IsLocallySurjective
          (Limits.Sigma.desc fun i => terminal.from
            ((Sheaf.sheafifiedYoneda (associatedTopology B S hS 𝒳.val.p τ)).obj (U i))))
    (h_refine : ∀ x ∈ affineObjects B S hS 𝒳,
      HasFiniteCoverRefinementsFrom (associatedTopology B S hS 𝒳.val.p τ)
        (affineObjects B S hS 𝒳) x)
    (h_product : ∀ U ∈ affineObjects B S hS 𝒳, ∀ U' ∈ affineObjects B S hS 𝒳,
      ∃ (m : ℕ) (V : Fin m → 𝒳.val.obj),
        (∀ i, V i ∈ affineObjects B S hS 𝒳) ∧
          ∃ (p : ∀ i, V i ⟶ U) (q : ∀ i, V i ⟶ U'),
          Sheaf.IsLocallySurjective (Limits.Sigma.desc fun i =>
            prod.lift ((Sheaf.sheafifiedYoneda (associatedTopology B S hS 𝒳.val.p τ)).map (p i))
              ((Sheaf.sheafifiedYoneda (associatedTopology B S hS 𝒳.val.p τ)).map (q i))))
    (h_equalizer : ∀ {U U' : 𝒳.val.obj} (a b : U ⟶ U'),
      U ∈ affineObjects B S hS 𝒳 → U' ∈ affineObjects B S hS 𝒳 →
      ∃ (m : ℕ) (V : Fin m → 𝒳.val.obj),
        (∀ i, V i ∈ affineObjects B S hS 𝒳) ∧
          ∃ (p : ∀ i, V i ⟶ U) (hp : ∀ i, p i ≫ a = p i ≫ b),
          Sheaf.IsLocallySurjective (Limits.Sigma.desc fun i =>
            equalizer.lift
              (f := (Sheaf.sheafifiedYoneda (associatedTopology B S hS 𝒳.val.p τ)).map a)
              (g := (Sheaf.sheafifiedYoneda (associatedTopology B S hS 𝒳.val.p τ)).map b)
              ((Sheaf.sheafifiedYoneda (associatedTopology B S hS 𝒳.val.p τ)).map (p i)) (by
                simpa only [Functor.map_comp] using
                  congrArg (Sheaf.sheafifiedYoneda (associatedTopology B S hS 𝒳.val.p τ)).map
                    (hp i))))
    (p : ℕ) {I : Type (u + 1)} [SmallCategory I] [IsFiltered I]
    (F : I ⥤ Sheaf (associatedTopology B S hS 𝒳.val.p τ) Ab.{u + 1}) :
    IsIso (colimit.post F
      ((Sheaf.Γ (associatedTopology B S hS 𝒳.val.p τ) Ab.{u + 1}).rightDerived p)) :=
  isIso_colimit_post_rightDerived_globalSections_of_covers
    (associatedTopology B S hS 𝒳.val.p τ) (affineObjects B S hS 𝒳) h_terminal h_refine
    h_product h_equalizer p F

/-- **Stacks 0GQV in the fppf topology, from conditions (1), (3) and (4) of Stacks 0GN4.** Let `𝒳`
be a category fibred in groupoids over the big fppf category of a scheme `S` contained in a big
fppf site, give its total category the fppf topology of Stacks 06TP, and assume of the collection
`affineObjects` of its objects lying over affine schemes that

1. finitely many of them have sheafified representables jointly covering the final sheaf,
3. the product of the sheafified representables of two of them is covered by a finite coproduct of
   sheafified representables of members of it, and
4. the equalizer of the sheafified representables of two parallel morphisms between members of it
   is covered by such a finite coproduct.

Then `colim_i H^p(𝒳, F_i) ⟶ H^p(𝒳, colim_i F_i)` is an isomorphism in every degree `p`, for every
filtered diagram `F` of abelian fppf sheaves on `𝒳`.

Condition (2) of Stacks 0GN4 is not assumed: it holds for every category fibred in groupoids, by
`AlgebraicGeometry.Stack.hasFiniteCoverRefinementsFrom_fppfTopology`. Conditions (1), (3) and (4)
are what the source derives from quasi-compactness and quasi-separatedness of an algebraic stack;
see "What is proved and what is assumed" in the module docstring for the state of each, and
`Stack.isIso_colimit_post_rightDerived_globalSections_fppf_of_isQuasiCompactStack` below for the
form of this result in which (1) too is discharged.

This is the fppf instance of
`AlgebraicGeometry.Stack.isIso_colimit_post_rightDerived_globalSections_associatedTopology`, the
site-theoretic step taken at an arbitrary topology; the fppf topology of Stacks 06TP is that
construction at `AlgebraicGeometry.BigFppfSite.topology`. -/
@[stacks 0GQV "the site-theoretic step for the fppf site; conditions (1), (3) and (4) of 0GN4 are \
assumed here"]
theorem isIso_colimit_post_rightDerived_globalSections_fppf
    (h_terminal : ∃ (m : ℕ) (U : Fin m → 𝒳.val.obj),
      (∀ i, U i ∈ affineObjects B S hS 𝒳) ∧
        Sheaf.IsLocallySurjective
          (Limits.Sigma.desc fun i => terminal.from
            ((Sheaf.sheafifiedYoneda (fppfTopology B S hS 𝒳)).obj (U i))))
    (h_product : ∀ U ∈ affineObjects B S hS 𝒳, ∀ U' ∈ affineObjects B S hS 𝒳,
      ∃ (m : ℕ) (V : Fin m → 𝒳.val.obj),
        (∀ i, V i ∈ affineObjects B S hS 𝒳) ∧
          ∃ (p : ∀ i, V i ⟶ U) (q : ∀ i, V i ⟶ U'),
          Sheaf.IsLocallySurjective (Limits.Sigma.desc fun i =>
            prod.lift ((Sheaf.sheafifiedYoneda (fppfTopology B S hS 𝒳)).map (p i))
              ((Sheaf.sheafifiedYoneda (fppfTopology B S hS 𝒳)).map (q i))))
    (h_equalizer : ∀ {U U' : 𝒳.val.obj} (a b : U ⟶ U'),
      U ∈ affineObjects B S hS 𝒳 → U' ∈ affineObjects B S hS 𝒳 →
      ∃ (m : ℕ) (V : Fin m → 𝒳.val.obj),
        (∀ i, V i ∈ affineObjects B S hS 𝒳) ∧
          ∃ (p : ∀ i, V i ⟶ U) (hp : ∀ i, p i ≫ a = p i ≫ b),
          Sheaf.IsLocallySurjective (Limits.Sigma.desc fun i =>
            equalizer.lift
              (f := (Sheaf.sheafifiedYoneda (fppfTopology B S hS 𝒳)).map a)
              (g := (Sheaf.sheafifiedYoneda (fppfTopology B S hS 𝒳)).map b)
              ((Sheaf.sheafifiedYoneda (fppfTopology B S hS 𝒳)).map (p i)) (by
                simpa only [Functor.map_comp] using
                  congrArg (Sheaf.sheafifiedYoneda (fppfTopology B S hS 𝒳)).map (hp i))))
    (p : ℕ) {I : Type (u + 1)} [SmallCategory I] [IsFiltered I]
    (F : I ⥤ Sheaf (fppfTopology B S hS 𝒳) Ab.{u + 1}) :
    IsIso (colimit.post F
      ((Sheaf.Γ (fppfTopology B S hS 𝒳) Ab.{u + 1}).rightDerived p)) :=
  isIso_colimit_post_rightDerived_globalSections_associatedTopology B S hS 𝒳 B.topology
    h_terminal (fun _ hU => hasFiniteCoverRefinementsFrom_fppfTopology B S hS 𝒳 hU)
    h_product h_equalizer p F

/-- **The second assertion of Stacks 0GQV: the same statement in the étale topology**, from
conditions (1), (3) and (4) of Stacks 0GN4. Let `𝒳` be a category fibred in groupoids over the
big fppf category of a scheme `S` contained in a big fppf site, give its total category the
*étale* topology of Stacks 06TP — the one it inherits from the big étale topology
`AlgebraicGeometry.etaleTopology` of Stacks 03FF localized at `S` — and assume of the collection
`affineObjects` of its objects lying over affine schemes those three conditions. Then
`colim_i H^p(𝒳, F_i) ⟶ H^p(𝒳, colim_i F_i)` is an isomorphism in every degree `p`, for every
filtered diagram `F` of abelian étale sheaves on `𝒳`.

This is
`AlgebraicGeometry.Stack.isIso_colimit_post_rightDerived_globalSections_associatedTopology` at the
big étale topology, and it is the shape in which the source's second assertion — "the same is true
for abelian sheaves on `𝒳_étale` taking cohomology in the étale topology" — becomes a statement of
this library.

Condition (2) of Stacks 0GN4 is not assumed, exactly as in the fppf case: it holds for every
category fibred in groupoids, by
`AlgebraicGeometry.Stack.hasFiniteCoverRefinementsFrom_etaleTopology`, whose geometric input is
**Stacks 0218** where the fppf proof uses Stacks 021P. Condition (1) is likewise available for
the étale site, by
`AlgebraicGeometry.Stack.exists_isAffineObject_isLocallySurjective_terminal_from_etale`, and
`AlgebraicGeometry.Stack`
`.isIso_colimit_post_rightDerived_globalSections_etale_of_isQuasiCompactStack`
is the form of this result in which it too is discharged. Conditions (3) and (4) remain open for
the étale site; see "What is proved and what is assumed" in the module docstring for the state of
each of the four. -/
@[stacks 0GQV "the second assertion, in the étale topology: the site-theoretic step for the étale \
site of Stacks 06TP; conditions (1), (3) and (4) of 0GN4 are assumed here"]
theorem isIso_colimit_post_rightDerived_globalSections_etale
    (h_terminal : ∃ (m : ℕ) (U : Fin m → 𝒳.val.obj),
      (∀ i, U i ∈ affineObjects B S hS 𝒳) ∧
        Sheaf.IsLocallySurjective
          (Limits.Sigma.desc fun i => terminal.from
            ((Sheaf.sheafifiedYoneda
              (associatedTopology B S hS 𝒳.val.p (etaleTopology B))).obj (U i))))
    (h_product : ∀ U ∈ affineObjects B S hS 𝒳, ∀ U' ∈ affineObjects B S hS 𝒳,
      ∃ (m : ℕ) (V : Fin m → 𝒳.val.obj),
        (∀ i, V i ∈ affineObjects B S hS 𝒳) ∧
          ∃ (p : ∀ i, V i ⟶ U) (q : ∀ i, V i ⟶ U'),
          Sheaf.IsLocallySurjective (Limits.Sigma.desc fun i =>
            prod.lift ((Sheaf.sheafifiedYoneda
                (associatedTopology B S hS 𝒳.val.p (etaleTopology B))).map (p i))
              ((Sheaf.sheafifiedYoneda
                (associatedTopology B S hS 𝒳.val.p (etaleTopology B))).map (q i))))
    (h_equalizer : ∀ {U U' : 𝒳.val.obj} (a b : U ⟶ U'),
      U ∈ affineObjects B S hS 𝒳 → U' ∈ affineObjects B S hS 𝒳 →
      ∃ (m : ℕ) (V : Fin m → 𝒳.val.obj),
        (∀ i, V i ∈ affineObjects B S hS 𝒳) ∧
          ∃ (p : ∀ i, V i ⟶ U) (hp : ∀ i, p i ≫ a = p i ≫ b),
          Sheaf.IsLocallySurjective (Limits.Sigma.desc fun i =>
            equalizer.lift
              (f := (Sheaf.sheafifiedYoneda
                (associatedTopology B S hS 𝒳.val.p (etaleTopology B))).map a)
              (g := (Sheaf.sheafifiedYoneda
                (associatedTopology B S hS 𝒳.val.p (etaleTopology B))).map b)
              ((Sheaf.sheafifiedYoneda
                (associatedTopology B S hS 𝒳.val.p (etaleTopology B))).map (p i)) (by
                simpa only [Functor.map_comp] using
                  congrArg (Sheaf.sheafifiedYoneda
                    (associatedTopology B S hS 𝒳.val.p (etaleTopology B))).map (hp i))))
    (p : ℕ) {I : Type (u + 1)} [SmallCategory I] [IsFiltered I]
    (F : I ⥤ Sheaf (associatedTopology B S hS 𝒳.val.p (etaleTopology B)) Ab.{u + 1}) :
    IsIso (colimit.post F
      ((Sheaf.Γ (associatedTopology B S hS 𝒳.val.p (etaleTopology B))
        Ab.{u + 1}).rightDerived p)) :=
  isIso_colimit_post_rightDerived_globalSections_associatedTopology B S hS 𝒳 (etaleTopology B)
    h_terminal (fun _ hU => hasFiniteCoverRefinementsFrom_etaleTopology B S hS 𝒳 hU)
    h_product h_equalizer p F

universe w

/-- Condition (1) of Stacks 0GN4 at any one of the sites of Stacks 06TP, in the shape the
criterion consumes: a single affine object whose sheafified representable surjects onto the final
sheaf, read as a family indexed by `Fin 1`.

A map out of a coproduct is a surjection as soon as one of its components is, because a surjection
of sheaves of sets is an epimorphism and an epimorphism factoring through a morphism makes that
morphism an epimorphism. -/
private theorem exists_fin_affineObjects_isLocallySurjective_terminal_of_topology
    (𝒴 : AlgebraicStacks.{u, w} B S hS) (τ : GrothendieckTopology B.Schemes)
    (h : ∃ x : 𝒴.val.val.obj, IsAffineObject B S hS 𝒴.val.val.p x ∧
      Sheaf.IsLocallySurjective (terminal.from
        ((Sheaf.sheafifiedYoneda (associatedTopology B S hS 𝒴.val.val.p τ)).obj x))) :
    ∃ (m : ℕ) (U : Fin m → 𝒴.val.val.obj),
      (∀ i, U i ∈ affineObjects B S hS 𝒴.val) ∧
        Sheaf.IsLocallySurjective
          (Limits.Sigma.desc fun i => terminal.from
            ((Sheaf.sheafifiedYoneda (associatedTopology B S hS 𝒴.val.val.p τ)).obj (U i))) := by
  obtain ⟨x, hxaff, hx⟩ := h
  refine ⟨1, fun _ => x, fun _ => hxaff, (Sheaf.isLocallySurjective_iff_epi _).2 ?_⟩
  have := (Sheaf.isLocallySurjective_iff_epi _).1 hx
  exact epi_of_epi_fac (Limits.Sigma.ι_comp_desc _ 0)

/-- Condition (1) of Stacks 0GN4 for a quasi-compact algebraic stack, in the shape the criterion
consumes: the single affine object of
`AlgebraicGeometry.Stack.exists_isAffineObject_isLocallySurjective_terminal_from`, read as a family
indexed by `Fin 1`.

This is the fppf instance of
`AlgebraicGeometry.Stack.exists_fin_affineObjects_isLocallySurjective_terminal_of_topology` above,
with its hypothesis discharged from quasi-compactness. -/
private theorem exists_fin_affineObjects_isLocallySurjective_terminal
    (𝒴 : AlgebraicStacks.{u, w} B S hS)
    (hqc : IsQuasiCompactStack.{u, w} B S hS 𝒴.val 𝒴.property) :
    ∃ (m : ℕ) (U : Fin m → 𝒴.val.val.obj),
      (∀ i, U i ∈ affineObjects B S hS 𝒴.val) ∧
        Sheaf.IsLocallySurjective
          (Limits.Sigma.desc fun i => terminal.from
            ((Sheaf.sheafifiedYoneda (fppfTopology B S hS 𝒴.val)).obj (U i))) :=
  exists_fin_affineObjects_isLocallySurjective_terminal_of_topology B S hS 𝒴 B.topology
    (exists_isAffineObject_isLocallySurjective_terminal_from B S hS 𝒴 hqc)

/-- **Stacks 0GQV in the fppf topology for a quasi-compact algebraic stack, from conditions (3) and
(4) of Stacks 0GN4.** Let `𝒴` be a quasi-compact algebraic stack over a scheme `S` contained in a
big fppf site and assume of the collection `affineObjects` of the objects of its fppf site lying
over affine schemes that

3. the product of the sheafified representables of two of them is covered by a finite coproduct of
   sheafified representables of members of it, and
4. the equalizer of the sheafified representables of two parallel morphisms between members of it
   is covered by such a finite coproduct.

Then `colim_i H^p(𝒴, F_i) ⟶ H^p(𝒴, colim_i F_i)` is an isomorphism in every degree `p`, for every
filtered diagram `F` of abelian fppf sheaves on `𝒴`.

This is `AlgebraicGeometry.Stack.isIso_colimit_post_rightDerived_globalSections_fppf` with its
condition (1) discharged from quasi-compactness by
`AlgebraicGeometry.Stack.exists_isAffineObject_isLocallySurjective_terminal_from`. The hypothesis
is stated for an `AlgebraicGeometry.Stack.AlgebraicStacks` rather than for a bare category fibred
in groupoids because that is what Stacks 04YC and Stacks 075S are about; the conclusion is the one
of the previous result at the underlying category fibred in groupoids.

Conditions (3) and (4) are the two the source derives from quasi-separatedness of `𝒴`, and both
are available: (3) is
`AlgebraicGeometry.Stack.exists_fin_affineObjects_isLocallySurjective_prodLift` and (4) is
`AlgebraicGeometry.Stack.exists_fin_affineObjects_isLocallySurjective_equalizerLift`, each for a
stack quasi-separated over a quasi-separated base scheme. They are hypotheses here because this
statement asks nothing of quasi-separatedness — no hypothesis of it appears, the two conditions
standing in for it — so this is not the full assertion of Stacks 0GQV, whose hypotheses are
quasi-compactness and quasi-separatedness alone. That assertion is
`AlgebraicGeometry.Stack.isIso_colimit_post_rightDerived_globalSections_fppf_of_isQuasiCompact`,
in `StacksFrontier/AlgebraicGeometry/Stacks/ColimitsOfCohomologyEqualizerAffineCover.lean`. See
"What is proved and what is assumed" in the module docstring. -/
@[stacks 0GQV "for a quasi-compact algebraic stack; conditions (3) and (4) of 0GN4 are assumed"]
theorem isIso_colimit_post_rightDerived_globalSections_fppf_of_isQuasiCompactStack
    (𝒴 : AlgebraicStacks.{u, w} B S hS)
    (hqc : IsQuasiCompactStack.{u, w} B S hS 𝒴.val 𝒴.property)
    (h_product : ∀ U ∈ affineObjects B S hS 𝒴.val, ∀ U' ∈ affineObjects B S hS 𝒴.val,
      ∃ (m : ℕ) (V : Fin m → 𝒴.val.val.obj),
        (∀ i, V i ∈ affineObjects B S hS 𝒴.val) ∧
          ∃ (p : ∀ i, V i ⟶ U) (q : ∀ i, V i ⟶ U'),
          Sheaf.IsLocallySurjective (Limits.Sigma.desc fun i =>
            prod.lift ((Sheaf.sheafifiedYoneda (fppfTopology B S hS 𝒴.val)).map (p i))
              ((Sheaf.sheafifiedYoneda (fppfTopology B S hS 𝒴.val)).map (q i))))
    (h_equalizer : ∀ {U U' : 𝒴.val.val.obj} (a b : U ⟶ U'),
      U ∈ affineObjects B S hS 𝒴.val → U' ∈ affineObjects B S hS 𝒴.val →
      ∃ (m : ℕ) (V : Fin m → 𝒴.val.val.obj),
        (∀ i, V i ∈ affineObjects B S hS 𝒴.val) ∧
          ∃ (p : ∀ i, V i ⟶ U) (hp : ∀ i, p i ≫ a = p i ≫ b),
          Sheaf.IsLocallySurjective (Limits.Sigma.desc fun i =>
            equalizer.lift
              (f := (Sheaf.sheafifiedYoneda (fppfTopology B S hS 𝒴.val)).map a)
              (g := (Sheaf.sheafifiedYoneda (fppfTopology B S hS 𝒴.val)).map b)
              ((Sheaf.sheafifiedYoneda (fppfTopology B S hS 𝒴.val)).map (p i)) (by
                simpa only [Functor.map_comp] using
                  congrArg (Sheaf.sheafifiedYoneda (fppfTopology B S hS 𝒴.val)).map (hp i))))
    (p : ℕ) {I : Type (u + 1)} [SmallCategory I] [IsFiltered I]
    (F : I ⥤ Sheaf (fppfTopology B S hS 𝒴.val) Ab.{u + 1}) :
    IsIso (colimit.post F
      ((Sheaf.Γ (fppfTopology B S hS 𝒴.val) Ab.{u + 1}).rightDerived p)) :=
  isIso_colimit_post_rightDerived_globalSections_fppf B S hS 𝒴.val
    (exists_fin_affineObjects_isLocallySurjective_terminal B S hS 𝒴 hqc)
    h_product h_equalizer p F

/-- **The second assertion of Stacks 0GQV, in the étale topology, for a quasi-compact algebraic
stack, from conditions (3) and (4) of Stacks 0GN4.** Let `𝒴` be a quasi-compact algebraic
stack over a scheme `S` contained in a big fppf site and assume of the collection `affineObjects`
of the objects of its *étale* site lying over affine schemes that

3. the product of the sheafified representables of two of them is covered by a finite coproduct of
   sheafified representables of members of it, and
4. the equalizer of the sheafified representables of two parallel morphisms between members of it
   is covered by such a finite coproduct.

Then `colim_i H^p(𝒴, F_i) ⟶ H^p(𝒴, colim_i F_i)` is an isomorphism in every degree `p`, for every
filtered diagram `F` of abelian étale sheaves on `𝒴`.

This is `AlgebraicGeometry.Stack.isIso_colimit_post_rightDerived_globalSections_etale` with its
condition (1) discharged from quasi-compactness by
`AlgebraicGeometry.Stack.exists_isAffineObject_isLocallySurjective_terminal_from_etale`, exactly as
`Stack.isIso_colimit_post_rightDerived_globalSections_fppf_of_isQuasiCompactStack` discharges it in
the fppf topology — the two use **Stacks 06XH** part (2) and **Stacks 06QA** respectively on the
one affine smooth presentation of **Stacks 04YC**.

Condition (2) is not assumed, as it is not in the fppf case: for the étale site it is
`AlgebraicGeometry.Stack.hasFiniteCoverRefinementsFrom_etaleTopology`, whose geometric input is
Stacks 0218 where the fppf proof uses Stacks 021P. Conditions (3) and (4) are open in both
topologies for the same reasons, about the 2-fibre products the source covers rather than about
the topology; see "What is proved and what is assumed" in the module docstring. So this is *not*
the full second assertion of Stacks 0GQV, whose hypotheses are quasi-compactness and
quasi-separatedness alone; in particular no hypothesis of quasi-separatedness appears here at
all, the two conditions standing in for it. -/
@[stacks 0GQV "the second assertion, in the étale topology, for a quasi-compact algebraic stack; \
conditions (1) and (2) of 0GN4 are now proved for the étale site, conditions (3) and (4) are \
assumed"]
theorem isIso_colimit_post_rightDerived_globalSections_etale_of_isQuasiCompactStack
    (𝒴 : AlgebraicStacks.{u, w} B S hS)
    (hqc : IsQuasiCompactStack.{u, w} B S hS 𝒴.val 𝒴.property)
    (h_product : ∀ U ∈ affineObjects B S hS 𝒴.val, ∀ U' ∈ affineObjects B S hS 𝒴.val,
      ∃ (m : ℕ) (V : Fin m → 𝒴.val.val.obj),
        (∀ i, V i ∈ affineObjects B S hS 𝒴.val) ∧
          ∃ (p : ∀ i, V i ⟶ U) (q : ∀ i, V i ⟶ U'),
          Sheaf.IsLocallySurjective (Limits.Sigma.desc fun i =>
            prod.lift ((Sheaf.sheafifiedYoneda
                (associatedTopology B S hS 𝒴.val.val.p (etaleTopology B))).map (p i))
              ((Sheaf.sheafifiedYoneda
                (associatedTopology B S hS 𝒴.val.val.p (etaleTopology B))).map (q i))))
    (h_equalizer : ∀ {U U' : 𝒴.val.val.obj} (a b : U ⟶ U'),
      U ∈ affineObjects B S hS 𝒴.val → U' ∈ affineObjects B S hS 𝒴.val →
      ∃ (m : ℕ) (V : Fin m → 𝒴.val.val.obj),
        (∀ i, V i ∈ affineObjects B S hS 𝒴.val) ∧
          ∃ (p : ∀ i, V i ⟶ U) (hp : ∀ i, p i ≫ a = p i ≫ b),
          Sheaf.IsLocallySurjective (Limits.Sigma.desc fun i =>
            equalizer.lift
              (f := (Sheaf.sheafifiedYoneda
                (associatedTopology B S hS 𝒴.val.val.p (etaleTopology B))).map a)
              (g := (Sheaf.sheafifiedYoneda
                (associatedTopology B S hS 𝒴.val.val.p (etaleTopology B))).map b)
              ((Sheaf.sheafifiedYoneda
                (associatedTopology B S hS 𝒴.val.val.p (etaleTopology B))).map (p i)) (by
                simpa only [Functor.map_comp] using
                  congrArg (Sheaf.sheafifiedYoneda
                    (associatedTopology B S hS 𝒴.val.val.p (etaleTopology B))).map (hp i))))
    (p : ℕ) {I : Type (u + 1)} [SmallCategory I] [IsFiltered I]
    (F : I ⥤ Sheaf (associatedTopology B S hS 𝒴.val.val.p (etaleTopology B)) Ab.{u + 1}) :
    IsIso (colimit.post F
      ((Sheaf.Γ (associatedTopology B S hS 𝒴.val.val.p (etaleTopology B))
        Ab.{u + 1}).rightDerived p)) :=
  isIso_colimit_post_rightDerived_globalSections_etale B S hS 𝒴.val
    (exists_fin_affineObjects_isLocallySurjective_terminal_of_topology B S hS 𝒴
      (etaleTopology B)
      (exists_isAffineObject_isLocallySurjective_terminal_from_etale B S hS 𝒴 hqc))
    h_product h_equalizer p F

end AlgebraicGeometry.Stack

end
