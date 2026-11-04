module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Homology.Resolution.NatIntBridge
public import StacksFrontier.CategoryTheory.Sites.FunctorialInjectiveEmbeddings
public import StacksFrontier.CategoryTheory.Sites.Hypercovering.SectionsComplexFunctorial
public import StacksFrontier.CategoryTheory.Sites.Hypercovering.ObjectAcyclicity
public import StacksFrontier.Topology.Sheaves.Cohomology.CechSpectralSequence.AbutmentIsCohomology
public import StacksFrontier.CategoryTheory.Sites.Hypercovering.SpectralSequence.Abutment

/-!
# The hypercovering-to-cohomology spectral sequence

Let `C` be a site with fibre products, `X` an object of `C`, `K` a hypercovering of `X` and `F` a
sheaf of abelian groups on `C`.  The third clause of [Stacks, Tag 01GY] asserts that there is a
first-quadrant `E₂` cohomological spectral sequence, functorial in `F`, whose second page is
`Ȟ^p(K, H̲^q(F))` and which converges to `H^{p+q}(X, F)`, and that it is functorial in the
hypercovering `K` as well.  `HypercoveringSpectralSequenceData` bundles the first three of these
and `hypercoveringSpectralSequence` supplies it, from the spectral sequence and second page of
`StacksFrontier.CategoryTheory.Sites.Hypercovering.SpectralSequence.SequenceAndSecondPage` and the
abutment of `StacksFrontier.CategoryTheory.Sites.Hypercovering.SpectralSequence.Abutment`; the
functoriality in `K` is `hypercoverSpectralSequenceHypercoveringFunctor`.

## Main definitions

* `Stacks.CategoryTheory.Hypercovering.hypercoverSpectralSequenceFunctorMap` and
  `Stacks.CategoryTheory.Hypercovering.hypercoverSpectralSequenceHypercoveringFunctor`: the
  morphism of spectral sequences induced by a morphism of hypercoverings, and the resulting
  functor on the opposite category of simplicial semi-representable objects over `X` -- the
  functoriality in `K` of the third clause of [Stacks, Tag 01GY].
* `Stacks.CategoryTheory.Hypercovering.HypercoveringSpectralSequenceData`: the data the third
  clause of [Stacks, Tag 01GY] asserts.
* `Stacks.CategoryTheory.Hypercovering.hypercoveringSpectralSequence`: that data, for a
  hypercovering of an object.

## Implementation notes

The functoriality in the hypercovering takes enough injectives as a hypothesis rather than a local
instance: with the instance a local one, the chosen resolution `injectiveResolution F` unfolds
through it, and the definitional comparisons the construction makes -- between the action of
`HomologicalComplex₂.e₂FunctorOfHomotopyClasses` on a morphism and that of
`HomologicalComplex₂.e₂SpectralSequence₂Functor` -- then exceed the heartbeat limit.  Since
`CategoryTheory.EnoughInjectives` is a proposition, the two spellings of the spectral sequence
agree by proof irrelevance.

What is asserted of the functoriality in `K` is that `K ↦ (the spectral sequence of K)` is a
functor, which is the source's assertion; that the second-page identification
`hypercoverPageTwoIso` and the abutment `hypercoverAbutment` are themselves natural in `K` is a
finer statement and is not proved here.

## Namespace

A second development of clause (3) of [Stacks, Tag 01GY] lives in
`StacksFrontier.CategoryTheory.Sites.Hypercovering.SpectralSequenceSmallSite` and the three modules
that continue it, in the namespace `Stacks.CategoryTheory.Hypercovering.Functorial`: there the
site is assumed small and the spectral sequence is a single functor of the pair `(K, F)`, where
here the site only needs fibre products, the hypercovering is fixed, and the functoriality in it
is a separate statement. Neither subsumes the other and no comparison of the two is formalized.

## References

* [Stacks Project, Tag 01GY](https://stacks.math.columbia.edu/tag/01GY)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.SimplicialObject.Augmented

universe w v u

namespace Stacks.CategoryTheory.Hypercovering

/-! ### Functoriality in the hypercovering -/

section HypercoveringFunctoriality

variable {C : Type u} [Category.{v} C] [HasPullbacks C]
variable (J : Pretopology C) (X : C)

/-- **The complex `s(-(K))` is contravariantly functorial in `K`.** -/
def hypercoverCochainNatFunctorMap
    {K K' : SimplicialObject (FormalCoproduct.{w} (Over X))} (ψ : K ⟶ K') :
    hypercoverCochainNatFunctor.{w} J X K' ⟶ hypercoverCochainNatFunctor.{w} J X K :=
  ((Functor.whiskeringLeft (Sheaf J.toGrothendieck AddCommGrpCat.{max u v w})
    ((Over X)ᵒᵖ ⥤ AddCommGrpCat.{max u v w})
      (CochainComplex AddCommGrpCat.{max u v w} ℕ)).obj
        (sectionsOnOverFunctor.{w} J X)).map (cochainComplexFunctorMap.{w} ψ)

/-- `hypercoverCochainNatFunctorMap` takes an identity to an identity. -/
lemma hypercoverCochainNatFunctorMap_id
    (K : SimplicialObject (FormalCoproduct.{w} (Over X))) :
    hypercoverCochainNatFunctorMap.{w} J X (𝟙 K) = 𝟙 _ := by
  simp only [hypercoverCochainNatFunctorMap, cochainComplexFunctorMap_id,
    CategoryTheory.Functor.map_id]
  rfl

/-- `hypercoverCochainNatFunctorMap` reverses composition. -/
lemma hypercoverCochainNatFunctorMap_comp
    {K K' K'' : SimplicialObject (FormalCoproduct.{w} (Over X))} (ψ : K ⟶ K') (φ : K' ⟶ K'') :
    hypercoverCochainNatFunctorMap.{w} J X (ψ ≫ φ) =
      hypercoverCochainNatFunctorMap.{w} J X φ ≫ hypercoverCochainNatFunctorMap.{w} J X ψ := by
  simp only [hypercoverCochainNatFunctorMap, cochainComplexFunctorMap_comp, Functor.map_comp]
  rfl

/-- **The complex `s(-(K))`, extended by zero, is contravariantly functorial in `K`.** -/
def hypercoverCochainIntFunctorMap
    {K K' : SimplicialObject (FormalCoproduct.{w} (Over X))} (ψ : K ⟶ K') :
    hypercoverCochainIntFunctor.{w} J X K' ⟶ hypercoverCochainIntFunctor.{w} J X K :=
  ((Functor.whiskeringRight (Sheaf J.toGrothendieck AddCommGrpCat.{max u v w})
    (CochainComplex AddCommGrpCat.{max u v w} ℕ)
      (CochainComplex AddCommGrpCat.{max u v w} ℤ)).obj
        (ComplexShape.embeddingUpNat.extendFunctor AddCommGrpCat.{max u v w})).map
    (hypercoverCochainNatFunctorMap.{w} J X ψ)

/-- `hypercoverCochainIntFunctorMap` takes an identity to an identity. -/
lemma hypercoverCochainIntFunctorMap_id
    (K : SimplicialObject (FormalCoproduct.{w} (Over X))) :
    hypercoverCochainIntFunctorMap.{w} J X (𝟙 K) = 𝟙 _ := by
  simp only [hypercoverCochainIntFunctorMap, hypercoverCochainNatFunctorMap_id,
    CategoryTheory.Functor.map_id]
  rfl

/-- `hypercoverCochainIntFunctorMap` reverses composition. -/
lemma hypercoverCochainIntFunctorMap_comp
    {K K' K'' : SimplicialObject (FormalCoproduct.{w} (Over X))} (ψ : K ⟶ K') (φ : K' ⟶ K'') :
    hypercoverCochainIntFunctorMap.{w} J X (ψ ≫ φ) =
      hypercoverCochainIntFunctorMap.{w} J X φ ≫ hypercoverCochainIntFunctorMap.{w} J X ψ := by
  simp only [hypercoverCochainIntFunctorMap, hypercoverCochainNatFunctorMap_comp,
    Functor.map_comp]
  rfl

/-- **The double complex of a complex of abelian sheaves is contravariantly functorial in `K`**,
the sections complex being so degreewise. -/
def hypercoverDoubleFunctorMap
    {K K' : SimplicialObject (FormalCoproduct.{w} (Over X))} (ψ : K ⟶ K') :
    hypercoverDoubleFunctor.{w} J X K' ⟶ hypercoverDoubleFunctor.{w} J X K :=
  NatTrans.mapHomologicalComplex (hypercoverCochainIntFunctorMap.{w} J X ψ)
    (ComplexShape.up ℤ)

/-- `hypercoverDoubleFunctorMap` takes an identity to an identity. -/
lemma hypercoverDoubleFunctorMap_id (K : SimplicialObject (FormalCoproduct.{w} (Over X))) :
    hypercoverDoubleFunctorMap.{w} J X (𝟙 K) = 𝟙 _ := by
  simp only [hypercoverDoubleFunctorMap, hypercoverCochainIntFunctorMap_id,
    NatTrans.mapHomologicalComplex_id]
  rfl

/-- `hypercoverDoubleFunctorMap` reverses composition. -/
lemma hypercoverDoubleFunctorMap_comp
    {K K' K'' : SimplicialObject (FormalCoproduct.{w} (Over X))} (ψ : K ⟶ K') (φ : K' ⟶ K'') :
    hypercoverDoubleFunctorMap.{w} J X (ψ ≫ φ) =
      hypercoverDoubleFunctorMap.{w} J X φ ≫ hypercoverDoubleFunctorMap.{w} J X ψ := by
  simp only [hypercoverDoubleFunctorMap, hypercoverCochainIntFunctorMap_comp,
    NatTrans.mapHomologicalComplex_comp]
  rfl

variable [HasSheafify J.toGrothendieck AddCommGrpCat.{max u v w}]

/-- **The double complex of an `ℕ`-indexed complex is contravariantly functorial in `K`.** -/
def hypercoverDoubleOfNatFunctorMap
    {K K' : SimplicialObject (FormalCoproduct.{w} (Over X))} (ψ : K ⟶ K') :
    hypercoverDoubleOfNatFunctor.{w} J X K' ⟶ hypercoverDoubleOfNatFunctor.{w} J X K :=
  ((Functor.whiskeringLeft
    (CochainComplex (Sheaf J.toGrothendieck AddCommGrpCat.{max u v w}) ℕ)
    (CochainComplex (Sheaf J.toGrothendieck AddCommGrpCat.{max u v w}) ℤ)
      (HomologicalComplex₂ AddCommGrpCat.{max u v w} (ComplexShape.up ℤ)
        (ComplexShape.up ℤ))).obj
          (ComplexShape.embeddingUpNat.extendFunctor
            (Sheaf J.toGrothendieck AddCommGrpCat.{max u v w}))).map
    (hypercoverDoubleFunctorMap.{w} J X ψ)

/-- `hypercoverDoubleOfNatFunctorMap` takes an identity to an identity. -/
lemma hypercoverDoubleOfNatFunctorMap_id
    (K : SimplicialObject (FormalCoproduct.{w} (Over X))) :
    hypercoverDoubleOfNatFunctorMap.{w} J X (𝟙 K) = 𝟙 _ := by
  simp only [hypercoverDoubleOfNatFunctorMap, hypercoverDoubleFunctorMap_id,
    CategoryTheory.Functor.map_id]
  rfl

/-- `hypercoverDoubleOfNatFunctorMap` reverses composition. -/
lemma hypercoverDoubleOfNatFunctorMap_comp
    {K K' K'' : SimplicialObject (FormalCoproduct.{w} (Over X))} (ψ : K ⟶ K') (φ : K' ⟶ K'') :
    hypercoverDoubleOfNatFunctorMap.{w} J X (ψ ≫ φ) =
      hypercoverDoubleOfNatFunctorMap.{w} J X φ ≫ hypercoverDoubleOfNatFunctorMap.{w} J X ψ := by
  simp only [hypercoverDoubleOfNatFunctorMap, hypercoverDoubleFunctorMap_comp,
    Functor.map_comp]
  rfl

variable [EnoughInjectives (Sheaf J.toGrothendieck AddCommGrpCat.{max u v w})]

/-- **The `ℤ × ℤ`-indexed spectral sequence of a hypercovering is contravariantly functorial in
the hypercovering, compatibly with its functoriality in the coefficient sheaf.**

At a sheaf `F` the morphism is the image under `HomologicalComplex₂.e₂SpectralSequence₂Functor`
of the morphism `A^{•,•}(K')(F) ⟶ A^{•,•}(K)(F)` of double complexes, which is why the identity
and composition laws below hold on the nose rather than up to filtered homotopy: it is only the
*coefficient* direction that is functorial merely up to homotopy, the chosen injective resolution
being used there, whereas the hypercovering direction leaves the resolution alone. -/
def hypercoverE₂FunctorMap
    {K K' : SimplicialObject (FormalCoproduct.{w} (Over X))} (ψ : K ⟶ K') :
    hypercoverE₂Functor.{w} J X K' ⟶ hypercoverE₂Functor.{w} J X K where
  app F := (HomologicalComplex₂.e₂SpectralSequence₂Functor AddCommGrpCat.{max u v w}).map
    ((hypercoverDoubleOfNatFunctorMap.{w} J X ψ).app (injectiveResolution F).cocomplex)
  naturality F F' f :=
    (((HomologicalComplex₂.e₂SpectralSequence₂Functor
        AddCommGrpCat.{max u v w}).map_comp _ _).symm.trans
      (congrArg (HomologicalComplex₂.e₂SpectralSequence₂Functor
          AddCommGrpCat.{max u v w}).map
        ((hypercoverDoubleOfNatFunctorMap.{w} J X ψ).naturality
          (InjectiveResolution.desc f (injectiveResolution F')
            (injectiveResolution F))))).trans
      ((HomologicalComplex₂.e₂SpectralSequence₂Functor
        AddCommGrpCat.{max u v w}).map_comp _ _)

/-- `hypercoverE₂FunctorMap` takes an identity to an identity. -/
lemma hypercoverE₂FunctorMap_id (K : SimplicialObject (FormalCoproduct.{w} (Over X))) :
    hypercoverE₂FunctorMap.{w} J X (𝟙 K) = 𝟙 _ := by
  refine NatTrans.ext (funext fun F => ?_)
  simp only [hypercoverE₂FunctorMap, hypercoverDoubleOfNatFunctorMap_id, NatTrans.id_app]
  exact CategoryTheory.Functor.map_id _ _

/-- `hypercoverE₂FunctorMap` reverses composition. -/
lemma hypercoverE₂FunctorMap_comp
    {K K' K'' : SimplicialObject (FormalCoproduct.{w} (Over X))} (ψ : K ⟶ K') (φ : K' ⟶ K'') :
    hypercoverE₂FunctorMap.{w} J X (ψ ≫ φ) =
      hypercoverE₂FunctorMap.{w} J X φ ≫ hypercoverE₂FunctorMap.{w} J X ψ := by
  refine NatTrans.ext (funext fun F => ?_)
  simp only [hypercoverE₂FunctorMap, hypercoverDoubleOfNatFunctorMap_comp, NatTrans.comp_app]
  exact CategoryTheory.Functor.map_comp _ _ _

/-- **The first-quadrant spectral sequence of a hypercovering is contravariantly functorial in the
hypercovering**, the first-quadrant reindexing of `hypercoverE₂FunctorMap`. -/
def hypercoverSpectralSequenceFunctorMap
    {K K' : SimplicialObject (FormalCoproduct.{w} (Over X))} (ψ : K ⟶ K') :
    hypercoverSpectralSequenceFunctor.{w} J X K' ⟶
      hypercoverSpectralSequenceFunctor.{w} J X K where
  app F := CategoryTheory.SpectralSequence.natRestrictMap
    ((hypercoverE₂FunctorMap.{w} J X ψ).app F)
    (isFirstQuadrant_hypercoverE₂Functor.{w} J X K' F)
    (isFirstQuadrant_hypercoverE₂Functor.{w} J X K F)
  naturality F F' f :=
    ((CategoryTheory.SpectralSequence.natRestrictMap_comp _ _
        (isFirstQuadrant_hypercoverE₂Functor.{w} J X K' F)
        (isFirstQuadrant_hypercoverE₂Functor.{w} J X K' F')
        (isFirstQuadrant_hypercoverE₂Functor.{w} J X K F')).symm.trans
      (congrArg (fun z => CategoryTheory.SpectralSequence.natRestrictMap z
          (isFirstQuadrant_hypercoverE₂Functor.{w} J X K' F)
          (isFirstQuadrant_hypercoverE₂Functor.{w} J X K F'))
        ((hypercoverE₂FunctorMap.{w} J X ψ).naturality f))).trans
      (CategoryTheory.SpectralSequence.natRestrictMap_comp _ _
        (isFirstQuadrant_hypercoverE₂Functor.{w} J X K' F)
        (isFirstQuadrant_hypercoverE₂Functor.{w} J X K F)
        (isFirstQuadrant_hypercoverE₂Functor.{w} J X K F'))

/-- `hypercoverSpectralSequenceFunctorMap` takes an identity to an identity. -/
lemma hypercoverSpectralSequenceFunctorMap_id
    (K : SimplicialObject (FormalCoproduct.{w} (Over X))) :
    hypercoverSpectralSequenceFunctorMap.{w} J X (𝟙 K) = 𝟙 _ := by
  refine NatTrans.ext (funext fun F => ?_)
  simp only [hypercoverSpectralSequenceFunctorMap, hypercoverE₂FunctorMap_id, NatTrans.id_app]
  exact CategoryTheory.SpectralSequence.natRestrictMap_id _

/-- `hypercoverSpectralSequenceFunctorMap` reverses composition. -/
lemma hypercoverSpectralSequenceFunctorMap_comp
    {K K' K'' : SimplicialObject (FormalCoproduct.{w} (Over X))} (ψ : K ⟶ K') (φ : K' ⟶ K'') :
    hypercoverSpectralSequenceFunctorMap.{w} J X (ψ ≫ φ) =
      hypercoverSpectralSequenceFunctorMap.{w} J X φ ≫
        hypercoverSpectralSequenceFunctorMap.{w} J X ψ := by
  refine NatTrans.ext (funext fun F => ?_)
  simp only [hypercoverSpectralSequenceFunctorMap, hypercoverE₂FunctorMap_comp, NatTrans.comp_app]
  exact CategoryTheory.SpectralSequence.natRestrictMap_comp _ _ _ _ _

/-- **The spectral sequence of [Stacks, Tag 01GY] is functorial in the hypercovering**, which is
the last sentence of its third clause: the assignment taking a simplicial semi-representable
object `K` over `X` to the functorial spectral sequence
`hypercoverSpectralSequenceFunctor J X K` of `HypercoveringSpectralSequenceData.sequence` is a
functor on the opposite category, contravariance being the direction in which a morphism of
hypercoverings acts on Čech cochains.

Morphisms are taken to be *all* morphisms of simplicial semi-representable objects over `X`, which
is more than the source asks for: a morphism of hypercoverings is in particular one of these, the
hypercovering conditions being conditions on an object and not on a morphism. -/
@[stacks 01GY "spectral sequence functorial in the hypercovering"]
def hypercoverSpectralSequenceHypercoveringFunctor :
    (SimplicialObject (FormalCoproduct.{w} (Over X)))ᵒᵖ ⥤
      (Sheaf J.toGrothendieck AddCommGrpCat.{max u v w} ⥤
        E₂CohomologicalSpectralSequenceNat AddCommGrpCat.{max u v w}) where
  obj K := hypercoverSpectralSequenceFunctor.{w} J X K.unop
  map ψ := hypercoverSpectralSequenceFunctorMap.{w} J X ψ.unop
  map_id K := hypercoverSpectralSequenceFunctorMap_id.{w} J X K.unop
  map_comp ψ φ := hypercoverSpectralSequenceFunctorMap_comp.{w} J X φ.unop ψ.unop

end HypercoveringFunctoriality

/-! ### The assembled statement -/

section Assembled

variable {C : Type u} [Category.{v} C] [HasPullbacks C]
variable (J : Pretopology C) (X : C) (K : SimplicialObject (FormalCoproduct.{w} (Over X)))
  [HasSheafify J.toGrothendieck AddCommGrpCat.{max u v w}]

open Stacks.Cohomology.Leray

/-- **The complete functorial hypercovering-to-cohomology spectral sequence for abelian sheaves on
a site**, which is the third clause of [Stacks, Tag 01GY]: a first-quadrant `E₂` cohomological
spectral sequence, functorial in the coefficient sheaf, whose second page is `Ȟ^p(K, H̲^q(F))` and
which converges to `H^{p+q}(X, F)`.

The hypothesis that `K` be a hypercovering is carried as a parameter: the spectral sequence and its
second page exist for an arbitrary simplicial formal coproduct over `X`, but the abutment is sheaf
cohomology on `X` only because the sections complex of an injective sheaf on a hypercovering is
acyclic ([Stacks, Tag 01GW]) with the expected degree-zero cohomology ([Stacks, Tag 01GV]). -/
structure HypercoveringSpectralSequenceData (hK : IsHypercovering J K) where
  /-- Injective resolutions of abelian sheaves exist, so the construction below is available. -/
  [enoughInjectives : EnoughInjectives (Sheaf J.toGrothendieck AddCommGrpCat.{max u v w})]
  /-- The spectral sequence is functorial in the coefficient sheaf. -/
  sequence : Sheaf J.toGrothendieck AddCommGrpCat.{max u v w} ⥤
    E₂CohomologicalSpectralSequenceNat AddCommGrpCat.{max u v w}
  /-- Its second page is the hypercovering cohomology of the cohomology presheaf. -/
  pageTwoIso (p q : ℕ) :
    sequence ⋙ CategoryTheory.SpectralSequence.pageFunctor _ _ 2 2 ⋙
        HomologicalComplex.eval _ _ (p, q) ≅
      (sectionsOnOverFunctor.{w} J X).rightDerived q ⋙ cechCohomologyOverFunctor.{w} X K p
  /-- The functorial finite filtered abutment is sheaf cohomology on `X`. -/
  abutment : FunctorialFirstQuadrantAbutsTo sequence
    (fun n => (sheafSectionsFunctor.{w} J X).rightDerived n)

/-- **The functorial spectral sequence of a hypercovering**, with second page
`Ȟ^p(K, H̲^q(F))` and abutment `H^{p+q}(X, F)`.

This is the third clause of [Stacks, Tag 01GY]: the four fields are
`CategoryTheory.Sheaf.enoughInjectives_addCommGrpCat`, `hypercoverSpectralSequenceFunctor`,
`hypercoverPageTwoIso` and `hypercoverAbutment`.  The functoriality of this spectral sequence in
the hypercovering, which is the last sentence of that clause, is
`hypercoverSpectralSequenceHypercoveringFunctor`, whose value at `K` is the `sequence` field
below. -/
@[stacks 01GY "spectral sequence"]
def hypercoveringSpectralSequence (hK : IsHypercovering J K) :
    HypercoveringSpectralSequenceData.{w} J X K hK :=
  letI := enoughInjectives_sheafAddCommGrpCat.{w} J
  { enoughInjectives := enoughInjectives_sheafAddCommGrpCat.{w} J
    sequence := hypercoverSpectralSequenceFunctor.{w} J X K
    pageTwoIso p q := hypercoverPageTwoIso.{w} J X K p q
    abutment := hypercoverAbutment.{w} J X K hK }

end Assembled

end Stacks.CategoryTheory.Hypercovering

end
