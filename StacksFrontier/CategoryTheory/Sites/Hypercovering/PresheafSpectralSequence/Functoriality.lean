module

public import StacksFrontier.CategoryTheory.Sites.Hypercovering.PresheafSpectralSequence.AbutmentIsCohomology

/-!
# Functoriality in the hypercovering, and the assembled spectral sequence

The functoriality of the spectral sequence of a hypercovering of a presheaf in the hypercovering,
and the assembled statement of the spectral sequence clause of [Stacks, Tag 09VX].
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.SimplicialObject.Augmented

universe q w v u

namespace Stacks.CategoryTheory.Hypercovering

/-! ### Functoriality in the hypercovering -/

section HypercoveringFunctoriality

namespace SemiRepresentable

variable {C : Type u} [Category.{v} C]

/-- **The complex of sections `s(-(L))` is contravariantly functorial in the simplicial
semi-representable object `L`**, by `cochainComplexFunctorMap` on presheaves. -/
def sectionsComplexFunctorMap (J : GrothendieckTopology C)
    {L L' : SimplicialObject (FormalCoproduct.{w} C)} (ψ : L ⟶ L') :
    sectionsComplexFunctor.{q, w, v, u} J L' ⟶ sectionsComplexFunctor.{q, w, v, u} J L :=
  ((Functor.whiskeringLeft (Sheaf J AddCommGrpCat.{max (max u v) (max q w)})
    (Cᵒᵖ ⥤ AddCommGrpCat.{max (max u v) (max q w)})
      (CochainComplex AddCommGrpCat.{max (max u v) (max q w)} ℕ)).obj
        (sheafToPresheaf J AddCommGrpCat.{max (max u v) (max q w)})).map
    (cochainComplexFunctorMap.{w} ψ)

/-- `sectionsComplexFunctorMap` takes an identity to an identity. -/
lemma sectionsComplexFunctorMap_id (J : GrothendieckTopology C)
    (L : SimplicialObject (FormalCoproduct.{w} C)) :
    sectionsComplexFunctorMap.{q, w, v, u} J (𝟙 L) = 𝟙 _ := by
  simp only [sectionsComplexFunctorMap, cochainComplexFunctorMap_id,
    CategoryTheory.Functor.map_id]
  rfl

/-- `sectionsComplexFunctorMap` reverses composition. -/
lemma sectionsComplexFunctorMap_comp (J : GrothendieckTopology C)
    {L L' L'' : SimplicialObject (FormalCoproduct.{w} C)} (ψ : L ⟶ L') (φ : L' ⟶ L'') :
    sectionsComplexFunctorMap.{q, w, v, u} J (ψ ≫ φ) =
      sectionsComplexFunctorMap.{q, w, v, u} J φ ≫
        sectionsComplexFunctorMap.{q, w, v, u} J ψ := by
  simp only [sectionsComplexFunctorMap, cochainComplexFunctorMap_comp, Functor.map_comp]
  rfl

/-- **The extended complex of sections is contravariantly functorial in the simplicial
semi-representable object.** -/
def sectionsComplexIntFunctorMap (J : GrothendieckTopology C)
    {L L' : SimplicialObject (FormalCoproduct.{w} C)} (ψ : L ⟶ L') :
    sectionsComplexIntFunctor.{q, w, v, u} J L' ⟶ sectionsComplexIntFunctor.{q, w, v, u} J L :=
  ((Functor.whiskeringRight (Sheaf J AddCommGrpCat.{max (max u v) (max q w)})
    (CochainComplex AddCommGrpCat.{max (max u v) (max q w)} ℕ)
      (CochainComplex AddCommGrpCat.{max (max u v) (max q w)} ℤ)).obj
        (ComplexShape.embeddingUpNat.extendFunctor
          AddCommGrpCat.{max (max u v) (max q w)})).map
    (sectionsComplexFunctorMap.{q, w, v, u} J ψ)

/-- `sectionsComplexIntFunctorMap` takes an identity to an identity. -/
lemma sectionsComplexIntFunctorMap_id (J : GrothendieckTopology C)
    (L : SimplicialObject (FormalCoproduct.{w} C)) :
    sectionsComplexIntFunctorMap.{q, w, v, u} J (𝟙 L) = 𝟙 _ := by
  simp only [sectionsComplexIntFunctorMap, sectionsComplexFunctorMap_id,
    CategoryTheory.Functor.map_id]
  rfl

/-- `sectionsComplexIntFunctorMap` reverses composition. -/
lemma sectionsComplexIntFunctorMap_comp (J : GrothendieckTopology C)
    {L L' L'' : SimplicialObject (FormalCoproduct.{w} C)} (ψ : L ⟶ L') (φ : L' ⟶ L'') :
    sectionsComplexIntFunctorMap.{q, w, v, u} J (ψ ≫ φ) =
      sectionsComplexIntFunctorMap.{q, w, v, u} J φ ≫
        sectionsComplexIntFunctorMap.{q, w, v, u} J ψ := by
  simp only [sectionsComplexIntFunctorMap, sectionsComplexFunctorMap_comp, Functor.map_comp]
  rfl

end SemiRepresentable

variable {C : Type u} [Category.{v} C] [HasEqualizers C] [HasPullbacks C]
variable (J : Pretopology C) (G : Cᵒᵖ ⥤ Type q)

/-- **The double complex of a complex of abelian sheaves is contravariantly functorial in the
hypercovering**, the complex of sections being so degreewise. -/
def hypercoverPresheafDoubleFunctorMap {K K' : HypercoveringOf.{q, w} J G}
    (ψ : K.toSimplicialObject ⟶ K'.toSimplicialObject) :
    hypercoverPresheafDoubleFunctor J G K' ⟶ hypercoverPresheafDoubleFunctor J G K :=
  NatTrans.mapHomologicalComplex
    (SemiRepresentable.sectionsComplexIntFunctorMap.{q, w, v, u} J.toGrothendieck ψ)
    (ComplexShape.up ℤ)

/-- `hypercoverPresheafDoubleFunctorMap` takes an identity to an identity. -/
lemma hypercoverPresheafDoubleFunctorMap_id (K : HypercoveringOf.{q, w} J G) :
    hypercoverPresheafDoubleFunctorMap.{q, w, v, u} J G (K := K) (K' := K)
      (𝟙 K.toSimplicialObject) = 𝟙 _ := by
  simp only [hypercoverPresheafDoubleFunctorMap,
    SemiRepresentable.sectionsComplexIntFunctorMap_id, NatTrans.mapHomologicalComplex_id]
  rfl

/-- `hypercoverPresheafDoubleFunctorMap` reverses composition. -/
lemma hypercoverPresheafDoubleFunctorMap_comp {K K' K'' : HypercoveringOf.{q, w} J G}
    (ψ : K.toSimplicialObject ⟶ K'.toSimplicialObject)
    (φ : K'.toSimplicialObject ⟶ K''.toSimplicialObject) :
    hypercoverPresheafDoubleFunctorMap.{q, w, v, u} J G (ψ ≫ φ) =
      hypercoverPresheafDoubleFunctorMap.{q, w, v, u} J G φ ≫
        hypercoverPresheafDoubleFunctorMap.{q, w, v, u} J G ψ := by
  simp only [hypercoverPresheafDoubleFunctorMap,
    SemiRepresentable.sectionsComplexIntFunctorMap_comp, NatTrans.mapHomologicalComplex_comp]
  rfl

variable [HasSheafify J.toGrothendieck AddCommGrpCat.{max (max u v) (max q w)}]

/-- **The double complex of an `ℕ`-indexed complex is contravariantly functorial in the
hypercovering.** -/
def hypercoverPresheafDoubleOfNatFunctorMap {K K' : HypercoveringOf.{q, w} J G}
    (ψ : K.toSimplicialObject ⟶ K'.toSimplicialObject) :
    hypercoverPresheafDoubleOfNatFunctor J G K' ⟶ hypercoverPresheafDoubleOfNatFunctor J G K :=
  ((Functor.whiskeringLeft
    (CochainComplex (Sheaf J.toGrothendieck AddCommGrpCat.{max (max u v) (max q w)}) ℕ)
    (CochainComplex (Sheaf J.toGrothendieck AddCommGrpCat.{max (max u v) (max q w)}) ℤ)
      (HomologicalComplex₂ AddCommGrpCat.{max (max u v) (max q w)} (ComplexShape.up ℤ)
        (ComplexShape.up ℤ))).obj
          (ComplexShape.embeddingUpNat.extendFunctor
            (Sheaf J.toGrothendieck AddCommGrpCat.{max (max u v) (max q w)}))).map
    (hypercoverPresheafDoubleFunctorMap.{q, w, v, u} J G ψ)

/-- `hypercoverPresheafDoubleOfNatFunctorMap` takes an identity to an identity. -/
lemma hypercoverPresheafDoubleOfNatFunctorMap_id (K : HypercoveringOf.{q, w} J G) :
    hypercoverPresheafDoubleOfNatFunctorMap.{q, w, v, u} J G (K := K) (K' := K)
      (𝟙 K.toSimplicialObject) = 𝟙 _ := by
  simp only [hypercoverPresheafDoubleOfNatFunctorMap,
    hypercoverPresheafDoubleFunctorMap_id, CategoryTheory.Functor.map_id]
  rfl

/-- `hypercoverPresheafDoubleOfNatFunctorMap` reverses composition. -/
lemma hypercoverPresheafDoubleOfNatFunctorMap_comp {K K' K'' : HypercoveringOf.{q, w} J G}
    (ψ : K.toSimplicialObject ⟶ K'.toSimplicialObject)
    (φ : K'.toSimplicialObject ⟶ K''.toSimplicialObject) :
    hypercoverPresheafDoubleOfNatFunctorMap.{q, w, v, u} J G (ψ ≫ φ) =
      hypercoverPresheafDoubleOfNatFunctorMap.{q, w, v, u} J G φ ≫
        hypercoverPresheafDoubleOfNatFunctorMap.{q, w, v, u} J G ψ := by
  simp only [hypercoverPresheafDoubleOfNatFunctorMap,
    hypercoverPresheafDoubleFunctorMap_comp, Functor.map_comp]
  rfl

variable [EnoughInjectives (Sheaf J.toGrothendieck AddCommGrpCat.{max (max u v) (max q w)})]

/-- **The `ℤ × ℤ`-indexed spectral sequence is contravariantly functorial in the hypercovering,
compatibly with its functoriality in the coefficient sheaf.**

At a sheaf `F` the morphism is the image under `HomologicalComplex₂.e₂SpectralSequence₂Functor`
of the morphism `A^{•,•}(K')(F) ⟶ A^{•,•}(K)(F)` of double complexes; the identity and
composition laws hold on the nose, not merely up to filtered homotopy, because a morphism of
hypercoverings leaves the chosen injective resolution alone -- it is only the coefficient
direction that uses a chosen descent. -/
def hypercoverPresheafE₂FunctorMap {K K' : HypercoveringOf.{q, w} J G}
    (ψ : K.toSimplicialObject ⟶ K'.toSimplicialObject) :
    hypercoverPresheafE₂Functor J G K' ⟶ hypercoverPresheafE₂Functor J G K where
  app F := (HomologicalComplex₂.e₂SpectralSequence₂Functor
      AddCommGrpCat.{max (max u v) (max q w)}).map
    ((hypercoverPresheafDoubleOfNatFunctorMap.{q, w, v, u} J G ψ).app
      (injectiveResolution F).cocomplex)
  naturality F F' f :=
    (((HomologicalComplex₂.e₂SpectralSequence₂Functor
        AddCommGrpCat.{max (max u v) (max q w)}).map_comp _ _).symm.trans
      (congrArg (HomologicalComplex₂.e₂SpectralSequence₂Functor
          AddCommGrpCat.{max (max u v) (max q w)}).map
        ((hypercoverPresheafDoubleOfNatFunctorMap.{q, w, v, u} J G ψ).naturality
          (InjectiveResolution.desc f (injectiveResolution F')
            (injectiveResolution F))))).trans
      ((HomologicalComplex₂.e₂SpectralSequence₂Functor
        AddCommGrpCat.{max (max u v) (max q w)}).map_comp _ _)

/-- `hypercoverPresheafE₂FunctorMap` takes an identity to an identity. -/
lemma hypercoverPresheafE₂FunctorMap_id (K : HypercoveringOf.{q, w} J G) :
    hypercoverPresheafE₂FunctorMap.{q, w, v, u} J G (K := K) (K' := K)
      (𝟙 K.toSimplicialObject) = 𝟙 _ := by
  refine NatTrans.ext (funext fun F => ?_)
  simp only [hypercoverPresheafE₂FunctorMap, hypercoverPresheafDoubleOfNatFunctorMap_id]
  exact CategoryTheory.Functor.map_id _ _

/-- `hypercoverPresheafE₂FunctorMap` reverses composition. -/
lemma hypercoverPresheafE₂FunctorMap_comp {K K' K'' : HypercoveringOf.{q, w} J G}
    (ψ : K.toSimplicialObject ⟶ K'.toSimplicialObject)
    (φ : K'.toSimplicialObject ⟶ K''.toSimplicialObject) :
    hypercoverPresheafE₂FunctorMap.{q, w, v, u} J G (ψ ≫ φ) =
      hypercoverPresheafE₂FunctorMap.{q, w, v, u} J G φ ≫
        hypercoverPresheafE₂FunctorMap.{q, w, v, u} J G ψ := by
  refine NatTrans.ext (funext fun F => ?_)
  simp only [hypercoverPresheafE₂FunctorMap, hypercoverPresheafDoubleOfNatFunctorMap_comp,
    NatTrans.comp_app]
  exact Functor.map_comp _ _ _

/-- **The first-quadrant spectral sequence is contravariantly functorial in the hypercovering**,
the first-quadrant reindexing of `hypercoverPresheafE₂FunctorMap`. -/
def hypercoverPresheafSpectralSequenceFunctorMap {K K' : HypercoveringOf.{q, w} J G}
    (ψ : K.toSimplicialObject ⟶ K'.toSimplicialObject) :
    hypercoverPresheafSpectralSequenceFunctor J G K' ⟶
      hypercoverPresheafSpectralSequenceFunctor J G K where
  app F := CategoryTheory.SpectralSequence.natRestrictMap
    ((hypercoverPresheafE₂FunctorMap.{q, w, v, u} J G ψ).app F)
    (isFirstQuadrant_hypercoverPresheafE₂Functor J G K' F)
    (isFirstQuadrant_hypercoverPresheafE₂Functor J G K F)
  naturality F F' f :=
    ((CategoryTheory.SpectralSequence.natRestrictMap_comp _ _
        (isFirstQuadrant_hypercoverPresheafE₂Functor J G K' F)
        (isFirstQuadrant_hypercoverPresheafE₂Functor J G K' F')
        (isFirstQuadrant_hypercoverPresheafE₂Functor J G K F')).symm.trans
      (congrArg (fun z => CategoryTheory.SpectralSequence.natRestrictMap z
          (isFirstQuadrant_hypercoverPresheafE₂Functor J G K' F)
          (isFirstQuadrant_hypercoverPresheafE₂Functor J G K F'))
        ((hypercoverPresheafE₂FunctorMap.{q, w, v, u} J G ψ).naturality f))).trans
      (CategoryTheory.SpectralSequence.natRestrictMap_comp _ _
        (isFirstQuadrant_hypercoverPresheafE₂Functor J G K' F)
        (isFirstQuadrant_hypercoverPresheafE₂Functor J G K F)
        (isFirstQuadrant_hypercoverPresheafE₂Functor J G K F'))

/-- `hypercoverPresheafSpectralSequenceFunctorMap` takes an identity to an identity. -/
lemma hypercoverPresheafSpectralSequenceFunctorMap_id (K : HypercoveringOf.{q, w} J G) :
    hypercoverPresheafSpectralSequenceFunctorMap.{q, w, v, u} J G (K := K) (K' := K)
      (𝟙 K.toSimplicialObject) = 𝟙 _ := by
  refine NatTrans.ext (funext fun F => ?_)
  simp only [hypercoverPresheafSpectralSequenceFunctorMap,
    hypercoverPresheafE₂FunctorMap_id]
  exact CategoryTheory.SpectralSequence.natRestrictMap_id _

/-- `hypercoverPresheafSpectralSequenceFunctorMap` reverses composition. -/
lemma hypercoverPresheafSpectralSequenceFunctorMap_comp
    {K K' K'' : HypercoveringOf.{q, w} J G}
    (ψ : K.toSimplicialObject ⟶ K'.toSimplicialObject)
    (φ : K'.toSimplicialObject ⟶ K''.toSimplicialObject) :
    hypercoverPresheafSpectralSequenceFunctorMap.{q, w, v, u} J G (ψ ≫ φ) =
      hypercoverPresheafSpectralSequenceFunctorMap.{q, w, v, u} J G φ ≫
        hypercoverPresheafSpectralSequenceFunctorMap.{q, w, v, u} J G ψ := by
  refine NatTrans.ext (funext fun F => ?_)
  simp only [hypercoverPresheafSpectralSequenceFunctorMap,
    hypercoverPresheafE₂FunctorMap_comp, NatTrans.comp_app]
  exact CategoryTheory.SpectralSequence.natRestrictMap_comp _ _ _ _ _

/-- **The functoriality in the hypercovering of the spectral sequence of a hypercovering of a
presheaf**, which is the last sentence of the spectral sequence clause of [Stacks, Tag 09VX]: the
assignment taking a hypercovering `K` of `G` to the functorial spectral sequence
`hypercoverPresheafSpectralSequenceFunctor J G K` of
`PresheafHypercoveringSpectralSequenceData.sequence` takes a morphism of hypercoverings to a
morphism of spectral sequences, contravariantly, compatibly with identities and composition.

A morphism of hypercoverings of `G` is here any morphism of the underlying simplicial
semi-representable objects, which is more than the source asks for: a morphism of hypercoverings
of `G` -- one compatible with the augmentations to `G` -- is in particular such a morphism, the
hypercovering conditions being conditions on an object and not on a morphism.  The bundling is a
structure rather than a `Functor` because the hypercoverings of `G` carry no category structure
in the library; the three fields are exactly the data and the two laws of one. -/
structure PresheafHypercoveringSpectralSequenceFunctoriality where
  /-- A morphism of hypercoverings induces a morphism of the spectral sequences, contravariantly
  and naturally in the coefficient sheaf. -/
  map : ∀ {K K' : HypercoveringOf.{q, w} J G}
    (_ : K.toSimplicialObject ⟶ K'.toSimplicialObject),
    hypercoverPresheafSpectralSequenceFunctor J G K' ⟶
      hypercoverPresheafSpectralSequenceFunctor J G K
  /-- The identity of a hypercovering induces the identity of its spectral sequence. -/
  map_id : ∀ K : HypercoveringOf.{q, w} J G, map (𝟙 K.toSimplicialObject) = 𝟙 _
  /-- A composition of morphisms of hypercoverings induces the reversed composition. -/
  map_comp : ∀ {K K' K'' : HypercoveringOf.{q, w} J G}
    (ψ : K.toSimplicialObject ⟶ K'.toSimplicialObject)
    (φ : K'.toSimplicialObject ⟶ K''.toSimplicialObject),
    map (ψ ≫ φ) = map φ ≫ map ψ

/-- **The spectral sequence of [Stacks, Tag 09VX] is functorial in the hypercovering**: the data
`PresheafHypercoveringSpectralSequenceFunctoriality`, supplied by
`hypercoverPresheafSpectralSequenceFunctorMap` and its two laws. -/
@[stacks 09VX "spectral sequence functorial in the hypercovering"]
def presheafHypercoveringSpectralSequenceFunctoriality :
    PresheafHypercoveringSpectralSequenceFunctoriality.{q, w, v, u} J G where
  map ψ := hypercoverPresheafSpectralSequenceFunctorMap.{q, w, v, u} J G ψ
  map_id K := hypercoverPresheafSpectralSequenceFunctorMap_id.{q, w, v, u} J G K
  map_comp ψ φ := hypercoverPresheafSpectralSequenceFunctorMap_comp.{q, w, v, u} J G ψ φ

end HypercoveringFunctoriality

/-! ### The assembled statement -/

section Assembled

variable {C : Type u} [Category.{v} C] [HasEqualizers C] [HasPullbacks C]
variable (J : Pretopology C) (G : Cᵒᵖ ⥤ Type q) (K : HypercoveringOf.{q, w} J G)
  [HasSheafify J.toGrothendieck AddCommGrpCat.{max (max u v) (max q w)}]
  [EnoughInjectives (Sheaf J.toGrothendieck AddCommGrpCat.{max (max u v) (max q w)})]

open Stacks.Cohomology.Leray

/-- **The complete functorial spectral sequence of a hypercovering of a presheaf**, which is the
spectral sequence clause of [Stacks, Tag 09VX]: a first-quadrant `E₂` cohomological spectral
sequence, functorial in the coefficient sheaf, whose second page is `Ȟ^p(K, H̲^{q'}(F))` and which
converges to `H^{p+q'}(G, F)`.

The cohomology presheaf `H̲^{q'}` is the `q'`-th right derived functor of the inclusion of abelian
sheaves into presheaves ([Stacks, Tag 01ER]) and cohomology over `G` is the right derived functor
of `Γ(G, -) = Hom(**Z**_G^♯, -)`. -/
structure PresheafHypercoveringSpectralSequenceData where
  /-- The spectral sequence is functorial in the coefficient sheaf. -/
  sequence : Sheaf J.toGrothendieck AddCommGrpCat.{max (max u v) (max q w)} ⥤
    E₂CohomologicalSpectralSequenceNat AddCommGrpCat.{max (max u v) (max q w)}
  /-- Its second page is the Čech cohomology of `K` of the cohomology presheaf. -/
  pageTwoIso (p q' : ℕ) :
    sequence ⋙ CategoryTheory.SpectralSequence.pageFunctor _ _ 2 2 ⋙
        HomologicalComplex.eval _ _ (p, q') ≅
      (sheafToPresheaf J.toGrothendieck
          AddCommGrpCat.{max (max u v) (max q w)}).rightDerived q' ⋙
        presheafCechCohomologyFunctor J G K p
  /-- The functorial finite filtered abutment is cohomology over the presheaf `G`. -/
  abutment : FunctorialFirstQuadrantAbutsTo sequence
    (fun n => (presheafSectionsFunctor J G K).rightDerived n)

/-- **The functorial spectral sequence of a hypercovering of a presheaf**, with second page
`Ȟ^p(K, H̲^{q'}(F))` and abutment `H^{p+q'}(G, F)`.

This is the spectral sequence clause of [Stacks, Tag 09VX]: the three fields are
`hypercoverPresheafSpectralSequenceFunctor`, `hypercoverPresheafPageTwoIso` and
`hypercoverPresheafAbutment`.  The functoriality of this spectral sequence in the hypercovering,
which is the last sentence of that clause, is
`presheafHypercoveringSpectralSequenceFunctoriality`, whose `map` is a morphism between the
`sequence` fields of two hypercoverings. -/
@[stacks 09VX "spectral sequence", sga "4 V 7.4.0" "(7.4.0.3)"]
def presheafHypercoveringSpectralSequence :
    PresheafHypercoveringSpectralSequenceData J G K where
  sequence := hypercoverPresheafSpectralSequenceFunctor J G K
  pageTwoIso p q' := hypercoverPresheafPageTwoIso J G K p q'
  abutment := hypercoverPresheafAbutment J G K

end Assembled

end Stacks.CategoryTheory.Hypercovering

end
