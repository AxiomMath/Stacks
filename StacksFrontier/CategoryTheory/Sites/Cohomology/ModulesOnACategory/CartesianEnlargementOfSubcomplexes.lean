module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.ModulesOnACategory.CartesianEnlargement
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ModulesOnACategory.DerivedBaseChangeOfSections
public import StacksFrontier.Homology.DerivedCategory.SubcomplexEnlargement

/-!
# The sections of an iterated enlargement, over one object of the site

Let `C` be a category, regarded as a site with the chaotic topology, and let `O` be a presheaf of
rings on `C`. The enlargement claim behind conclusion (1) of Stacks 0GYZ enlarges a small
subcomplex `S^• ⊆ F^•` in stages `S^• = G_0^• ⊆ G_1^• ⊆ ⋯` and takes `H^•` to be their union;
`QuasiCoherentEquivalence.exists_iterated_enlargement_containing_sections` runs that iteration.
What has then to be checked of `H^•` is a statement about its *sections*: for every morphism
`U → V` of `C` the comparison `H^•(V) ⊗^L_{O(V)} O(U) ⟶ H^•(U)` is an isomorphism in `D(O(U))`.

This file supplies the step that turns the union into a colimit of sections: over each object of
`C` the complex of sections of `H^•` is the filtered colimit of the complexes of sections of the
stages. That is what makes
`Stacks.SubcomplexEnlargement.derivedBaseChangeHomology_preservesFilteredColimits_ulift` and
`Stacks.SubcomplexEnlargement.isIso_colimMap_of_stagewise` applicable to the comparison at `H^•`.

## Main definitions

* `Stacks.ModulesOnACategory.QuasiCoherentEquivalence.sectionsComplexFunctor`: evaluation at an
  object of `C`, on complexes of `O`-modules.
* `Stacks.ModulesOnACategory.QuasiCoherentEquivalence.stageSectionsMap` and
  `Stacks.ModulesOnACategory.QuasiCoherentEquivalence.unionSectionsMap`: the maps of the chain and
  the maps into the union, over an object of `C`.

* `Stacks.ModulesOnACategory.QuasiCoherentEquivalence.stageSectionsRangeIso`: the sections of a
  stage, identified with their degreewise image in the sections of the union.

## Main results

* `Stacks.ModulesOnACategory.QuasiCoherentEquivalence.mono_sectionsComplexFunctor_map`: taking
  sections preserves monomorphisms of complexes of `O`-modules.

* `Stacks.ModulesOnACategory.QuasiCoherentEquivalence.comp_stageMap_eq`: the stages of an iterated
  enlargement factor through one another compatibly with their maps into the union.
* `Stacks.ModulesOnACategory.QuasiCoherentEquivalence.stageSectionsRangeIso_hom_ι`: that
  identification, followed by the inclusion of the image, is the map of the stage into the union.
* `Stacks.ModulesOnACategory.QuasiCoherentEquivalence.isColimit_sections_of_stages`: over each
  object of `C`, the sections of the union are the colimit of the sections of the stages.

## Implementation notes

The iteration returns the maps `k_n : G_n^• ⟶ H^•` into the union and the maps
`p_n : G_n^• ⟶ G_{n+1}^•` of the chain separately, compatibly with the inclusions
`γ_n : G_n^• ⟶ F^•`; that `p_n` followed by `k_{n+1}` is `k_n` is not among them, and is obtained
by cancelling the monomorphism `H^• ⟶ F^•`. That identity is the compatibility hypothesis of
`Stacks.SubcomplexEnlargement.isColimit_familyCocone_sequence`, whose other hypothesis, that the
degreewise images of the stages exhaust the union, is returned by the iteration verbatim.

The evaluated maps are named rather than written out, because the index `q` of the chain occurs in
`Stacks.SubcomplexEnlargement.sequenceRangeFamily_monotone` only inside its hypothesis and so is
not inferable from a placeholder. Evaluation at an object of `C` is exact and commutes with the
formation of complexes, so beyond naming nothing has to be transported.

The colimit is indexed by `ULift ℕ` rather than `ℕ`, as it must be: the shape of a colimit in
`ModuleCat.{max u v r w}` lives in `Type (max u v r w)`.

The diagram whose colimit is taken is the one of the degreewise *images* of the stages, not the one
of the stages themselves. `stageSectionsRangeIso` identifies the two stagewise, the maps into the
union being monomorphisms, so the comparison map of sections at a stage transports to its image by
conjugation; what is next needed of the union, that the comparison at it is the colimit of the
comparisons at the stages, is to be obtained that way. Restating the colimit over the diagram of
the stages instead was tried and abandoned: it asks for `Mono` of a leg of an arbitrary cocone,
which reaches the category of complexes by a different path from the one
`Stacks.SubcomplexEnlargement.toRangeFamily_isIso` wants.

Two instance facts cost a build each and are worth knowing. `toRangeFamily_isIso` is a *file-local*
instance where it is proved, so outside that file it has to be applied by hand. And applying it by
hand through a `haveI` whose type is written out does not work: the `IsIso (toRangeFamily …)` so
ascribed and the one `asIso` elaborates print identically and are not the same term, so the
instance is not found. Passing it positionally, `@asIso _ _ _ _ f (toRangeFamily_isIso _)`, lets
the map be elaborated once and ends it.

## References

* [Stacks Project, Tag 0GYZ](https://stacks.math.columbia.edu/tag/0GYZ)
* [Stacks Project, Tag 0GYI](https://stacks.math.columbia.edu/tag/0GYI)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace Stacks.ModulesOnACategory.QuasiCoherentEquivalence

universe w u v r

variable {C : Type u} [Category.{v} C]

/-- Evaluation at an object of `C`, on complexes of `O`-modules: the complex of sections. -/
public abbrev sectionsComplexFunctor (O : Cᵒᵖ ⥤ RingCat.{r}) (V : Cᵒᵖ) :
    CochainComplex (PresheafOfModules.{max u v r w} O) ℤ ⥤
      CochainComplex (ModuleCat.{max u v r w} (O.obj V)) ℤ :=
  (PresheafOfModules.evaluation.{max u v r w} O V).mapHomologicalComplex (ComplexShape.up ℤ)

variable {O : Cᵒᵖ ⥤ RingCat.{r}}

/-- **Taking sections preserves monomorphisms of complexes.** A monomorphism of complexes of
`O`-modules is degreewise a monomorphism, evaluation of a complex in one degree preserving finite
limits, and evaluation of a presheaf of modules over an object of `C` preserves them too; so the
induced map of complexes of sections is again a monomorphism.

This is what makes the degreewise images of the stages of an iterated enlargement isomorphic to the
stages themselves, through `Stacks.SubcomplexEnlargement.toRangeFamily_isIso`, and hence what lets
the comparison maps of the stages be transported to the diagram whose colimit is the union. -/
public lemma mono_sectionsComplexFunctor_map
    {P Q : CochainComplex (PresheafOfModules.{max u v r w} O) ℤ} (φ : P ⟶ Q) [Mono φ] (V : Cᵒᵖ) :
    Mono ((sectionsComplexFunctor.{w} O V).map φ) := by
  refine HomologicalComplex.mono_of_mono_f _ (fun i => ?_)
  have : Mono (φ.f i) :=
    inferInstanceAs (Mono ((HomologicalComplex.eval (PresheafOfModules.{max u v r w} O)
      (ComplexShape.up ℤ) i).map φ))
  exact inferInstanceAs
    (Mono ((PresheafOfModules.evaluation.{max u v r w} O V).map (φ.f i)))

/-- **The stages of an iterated enlargement factor through one another.** The iteration returns
the maps of the chain and the maps into the union separately, each compatible with the inclusions
into the ambient complex; composing a step of the chain with the next map into the union gives the
previous one, because the inclusion of the union is a monomorphism. -/
public lemma comp_stageMap_eq {F H : CochainComplex (PresheafOfModules.{max u v r w} O) ℤ}
    {G : ℕ → CochainComplex (PresheafOfModules.{max u v r w} O) ℤ}
    (h : H ⟶ F) [Mono h] (γ : ∀ n, G n ⟶ F) (p : ∀ n, G n ⟶ G (n + 1)) (k : ∀ n, G n ⟶ H)
    (hp : ∀ n, p n ≫ γ (n + 1) = γ n) (hk : ∀ n, k n ≫ h = γ n) (n : ℕ) :
    p n ≫ k (n + 1) = k n := by
  rw [← cancel_mono h, Category.assoc, hk (n + 1), hp n, hk n]

section Stages

variable {F H : CochainComplex (PresheafOfModules.{max u v r w} O) ℤ}
  {G : ℕ → CochainComplex (PresheafOfModules.{max u v r w} O) ℤ}

/-- A step of the chain of stages, over an object of `C`. -/
public abbrev stageSectionsMap (p : ∀ n, G n ⟶ G (n + 1)) (V : Cᵒᵖ) (n : ℕ) :
    (sectionsComplexFunctor.{w} O V).obj (G n) ⟶ (sectionsComplexFunctor.{w} O V).obj (G (n + 1)) :=
  (sectionsComplexFunctor.{w} O V).map (p n)

/-- The map of a stage into the union, over an object of `C`. -/
public abbrev unionSectionsMap (k : ∀ n, G n ⟶ H) (V : Cᵒᵖ) (n : ℕ) :
    (sectionsComplexFunctor.{w} O V).obj (G n) ⟶ (sectionsComplexFunctor.{w} O V).obj H :=
  (sectionsComplexFunctor.{w} O V).map (k n)

/-- **The maps of the stages into the union are monomorphisms over each object of `C`.** A stage
maps into the union compatibly with the inclusions into the ambient complex, so it is a
monomorphism as soon as its inclusion is, and `mono_sectionsComplexFunctor_map` carries that to the
sections.

That the inclusions `γ_n` of the stages are monomorphisms is a hypothesis here rather than a
consequence of the rest: only the ranges of the composites enter the union, so nothing in the
chain forces it. It is among the conclusions of
`exists_iterated_enlargement_containing_sections`, `BoundedSubcomplex` carrying the monomorphy of
its inclusion. -/
public lemma mono_unionSectionsMap {H' : CochainComplex (PresheafOfModules.{max u v r w} O) ℤ}
    (h : H' ⟶ F) (γ : ∀ n, G n ⟶ F) (k : ∀ n, G n ⟶ H') (hγ : ∀ n, Mono (γ n))
    (hk : ∀ n, k n ≫ h = γ n) (V : Cᵒᵖ) (n : ℕ) :
    Mono (unionSectionsMap.{w} k V n) := by
  have := hγ n
  have : Mono (k n) := mono_of_mono_fac (hk n)
  exact mono_sectionsComplexFunctor_map.{w} (k n) V

/-- **A stage's sections are isomorphic to their image in the sections of the union.** The diagram
whose colimit is the sections of the union is the diagram of degreewise images of the stages; this
is the isomorphism identifying each of its objects with the sections of the corresponding stage.

It is what the comparison maps of the stages are transported along: the comparison at the image is
the comparison at the stage conjugated by this isomorphism at the source and at the target. Taking
this route, rather than restating the colimit over the stages themselves, keeps the monomorphy at
one spelling throughout, the one `mono_unionSectionsMap` produces. -/
public def stageSectionsRangeIso {H' : CochainComplex (PresheafOfModules.{max u v r w} O) ℤ}
    (h : H' ⟶ F) (γ : ∀ n, G n ⟶ F) (k : ∀ n, G n ⟶ H') (hγ : ∀ n, Mono (γ n))
    (hk : ∀ n, k n ≫ h = γ n) (V : Cᵒᵖ) (n : ℕ) :
    (sectionsComplexFunctor.{w} O V).obj (G n) ≅
      (Stacks.SubcomplexEnlargement.sequenceRangeFamily.{r, max u v r w}
        (unionSectionsMap.{w} k V) (ULift.up n)).toComplex :=
  letI := mono_unionSectionsMap.{w} h γ k hγ hk V n
  @asIso _ _ _ _ (Stacks.SubcomplexEnlargement.toRangeFamily (unionSectionsMap.{w} k V n))
    (Stacks.SubcomplexEnlargement.toRangeFamily_isIso _)

/-- **The identification of a stage with its image is the map into the union.** Composing
`stageSectionsRangeIso` with the inclusion of the image into the sections of the union recovers
the map of the stage into the union. -/
public lemma stageSectionsRangeIso_hom_ι
    {H' : CochainComplex (PresheafOfModules.{max u v r w} O) ℤ}
    (h : H' ⟶ F) (γ : ∀ n, G n ⟶ F) (k : ∀ n, G n ⟶ H') (hγ : ∀ n, Mono (γ n))
    (hk : ∀ n, k n ≫ h = γ n) (V : Cᵒᵖ) (n : ℕ) :
    (stageSectionsRangeIso.{w} h γ k hγ hk V n).hom ≫
        (Stacks.SubcomplexEnlargement.sequenceRangeFamily.{r, max u v r w}
          (unionSectionsMap.{w} k V) (ULift.up n)).ι =
      unionSectionsMap.{w} k V n :=
  Stacks.SubcomplexEnlargement.toRangeFamily_ι.{r, max u v r w, 0} _

variable (h : H ⟶ F) [Mono h] (γ : ∀ n, G n ⟶ F) (p : ∀ n, G n ⟶ G (n + 1)) (k : ∀ n, G n ⟶ H)
  (hp : ∀ n, p n ≫ γ (n + 1) = γ n) (hk : ∀ n, k n ≫ h = γ n)

include hp hk

/-- The stages factor through one another over each object of `C`. -/
public lemma comp_unionSectionsMap_eq (V : Cᵒᵖ) (n : ℕ) :
    stageSectionsMap.{w} p V n ≫ unionSectionsMap.{w} k V (n + 1) = unionSectionsMap.{w} k V n := by
  rw [← Functor.map_comp, comp_stageMap_eq.{w} h γ p k hp hk n]

/-- The degreewise images of the stages in the sections of the union increase. -/
public lemma monotone_sequenceRangeFamily_unionSectionsMap (V : Cᵒᵖ) :
    Monotone (Stacks.SubcomplexEnlargement.sequenceRangeFamily.{r, max u v r w}
      (unionSectionsMap.{w} k V)) :=
  Stacks.SubcomplexEnlargement.sequenceRangeFamily_monotone.{r, max u v r w}
    (q := stageSectionsMap.{w} p V) (unionSectionsMap.{w} k V)
    (comp_unionSectionsMap_eq.{w} h γ p k hp hk V)

/-- **The sections of the union are the colimit of the sections of the stages.** Over an object `V`
of `C`, the complex of sections of the union of an iterated enlargement is the filtered colimit of
the complexes of sections of the stages, presented through the degreewise images of the stages.

The hypotheses are the ones the iteration supplies: the compatibility of the chain with the
inclusions into the ambient complex, from which `comp_stageMap_eq` produces the compatibility the
colimit needs, and the statement that every section of the union comes from a stage. -/
public def isColimit_sections_of_stages
    (hexh : ∀ (i : ℤ) (X : Cᵒᵖ) (x : (H.X i).obj X),
      ∃ (n : ℕ) (y : ((G n).X i).obj X), ((k n).f i).app X y = x)
    (V : Cᵒᵖ) :
    IsColimit (Stacks.SubcomplexEnlargement.familyCocone
      (Stacks.SubcomplexEnlargement.sequenceRangeFamily.{r, max u v r w}
        (unionSectionsMap.{w} k V))
      (monotone_sequenceRangeFamily_unionSectionsMap.{w} h γ p k hp hk V)) :=
  Stacks.SubcomplexEnlargement.isColimit_familyCocone_sequence.{r, max u v r w}
    (q := stageSectionsMap.{w} p V) (unionSectionsMap.{w} k V)
    (comp_unionSectionsMap_eq.{w} h γ p k hp hk V) (fun i x => hexh i V x)

end Stages

end Stacks.ModulesOnACategory.QuasiCoherentEquivalence

end
