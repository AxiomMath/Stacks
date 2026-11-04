module

public import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Homology.SpectralSequence.DoubleComplexNaturality
public import StacksFrontier.Algebra.Homology.SpectralSequence.FirstQuadrantDoubleComplex
public import StacksFrontier.CategoryTheory.CommutingSquares
public import StacksFrontier.CategoryTheory.Sites.Hypercovering.SpectralSequence
public import StacksFrontier.Homology.CompositeCollapse
public import StacksFrontier.Topology.Sheaves.Cohomology.CechSpectralSequence.SequenceAndSecondPage
public import StacksFrontier.Topology.Simplicial.LowerShriek
public import StacksFrontier.Topology.Simplicial.Resolution

/-!
# The cohomology spectral sequence of a simplicial topological space

Let `X` be a simplicial topological space and let `F` be an abelian sheaf on its total site.
Choosing an injective resolution `F ⟶ I^•` and taking sections over the whole spaces `X_p` gives
the double complex `A^{q,p} = I^q(X_p)`, with the resolution degree outer and the simplicial
degree inner.  Its second spectral sequence is a first-quadrant spectral sequence, functorial in
`F`, whose first page is `E_1^{p,q} = H^q(X_p, F_p)`.

## Main definitions

* `Stacks.Topology.Simplicial.wholeSpaceSectionsComplex`: the complex of sections over the whole
  spaces `X_p`, with the alternating sum of the coface maps as differential.
* `Stacks.Topology.Simplicial.cohomologyDoubleComplex`: the double complex `A^{q,p} = I^q(X_p)`
  of the chosen injective resolution of an abelian sheaf.
* `Stacks.Topology.Simplicial.cohomologySpectralSequence`: the spectral sequence, as a functor of
  the abelian sheaf.
* `Stacks.Topology.Simplicial.componentCohomologyFunctor`: `H^q(X_p, -_p)`, the `q`-th right
  derived functor of global sections on `X_p` composed with restriction to `X_p`.

## Main results

* `Stacks.Topology.Simplicial.cohomologySpectralSequence_pageOneIso`: the first page of the
  spectral sequence is `E_1^{p,q} = H^q(X_p, F_p)`, naturally in `F`.

## Implementation notes

The index orientation is forced: the second spectral sequence of a double complex has
`''E_1^{p,q} = H^q(K^{•,p})`, homology in the outer index of the column with inner index `p`, so
the resolution degree has to be the outer one for the first page to be the cohomology of `X_p`.
Both indices are extended by zero from `ℕ` to `ℤ`, the simplicial index because the sections
complex is `ℕ`-indexed and the resolution index because Mathlib's injective resolutions are.

The double complex is functorial in the sheaf only up to homotopy, an injective resolution being
functorial only into the homotopy category; `HomologicalComplex₂.FilteredHomotopy₂` is what the
spectral sequence construction needs, and homotopy invariance of the induced maps holds from the
first page on, which is why the spectral sequence is presented from its first page.

`H^q(X_p, F_p)` is rendered as the `q`-th right derived functor of the global sections of the
restriction of `F` to `X_p`, which is the source's own definition of sheaf cohomology.  That the
restriction of the chosen resolution is an injective resolution of `F_p` is exactly what the
source cites Stacks 09W0 and 09W1 for: restriction to a degree is exact and preserves injective
abelian sheaves.  Exactness of the restriction is obtained here from its two adjunctions, as the
right adjoint of the exact lower shriek of Stacks 09W0 and, through
`CategoryTheory.Functor.sheafPullbackCocontinuousIsoSheafPushforwardContinuous`, as a left
adjoint; the Kan extension hypotheses this needs are the ones already carried by the Stacks 09W0
and 09W1 declarations.

The convergence clause of Stacks 09W6, that the spectral sequence converges to
`H^{p+q}(X_{Zar}, F)`, functorially in `F`, is
`Stacks.Topology.Simplicial.cohomologySpectralSequence_abutment` of
`StacksFrontier/Topology/Simplicial/CohomologySpectralSequenceAbutment.lean`.

## References

* [Stacks Project, Tag 09W6](https://stacks.math.columbia.edu/tag/09W6)
* [Stacks Project, Tag 09W5](https://stacks.math.columbia.edu/tag/09W5)
* [Stacks Project, Tag 09W0](https://stacks.math.columbia.edu/tag/09W0)
* [Stacks Project, Tag 09W1](https://stacks.math.columbia.edu/tag/09W1)
* [Stacks Project, Tag 0130](https://stacks.math.columbia.edu/tag/0130)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open AlgebraicTopology

universe u w

namespace Stacks.Topology.Simplicial

/-! ### The complex of sections over the whole spaces -/

/-- The cosimplicial object of sections of a presheaf on the site of a simplicial topological
space over the whole space in each simplicial degree. -/
def wholeSpaceSectionsCosimplicial (X : SimplicialObject TopCat.{u}) (A : Type*) [Category A] :
    ((SimplicialOpen X)ᵒᵖ ⥤ A) ⥤ CosimplicialObject A :=
  (Functor.whiskeringLeft _ _ _).obj (wholeSpaceFunctor X).rightOp

/-- The complex of sections of an abelian presheaf on the site of a simplicial topological space
over the whole spaces `X_p`, with the alternating sum of the coface maps as differential. -/
noncomputable def wholeSpaceSectionsComplex (X : SimplicialObject TopCat.{u}) :
    ((SimplicialOpen X)ᵒᵖ ⥤ Ab.{w}) ⥤ CochainComplex Ab.{w} ℕ :=
  wholeSpaceSectionsCosimplicial X Ab.{w} ⋙ alternatingCofaceMapComplex Ab.{w}

/-- The functor `wholeSpaceSectionsComplex` is additive. -/
instance wholeSpaceSectionsComplex_additive (X : SimplicialObject TopCat.{u}) :
    (wholeSpaceSectionsComplex.{u, w} X).Additive where
  map_add := by
    intros
    apply HomologicalComplex.hom_ext
    intro _
    rfl

/-- The degree-`p` term of `wholeSpaceSectionsComplex` is the group of sections over `X_p`. -/
lemma wholeSpaceSectionsComplex_obj_X (X : SimplicialObject TopCat.{u})
    (P : (SimplicialOpen X)ᵒᵖ ⥤ Ab.{w}) (p : ℕ) :
    ((wholeSpaceSectionsComplex.{u, w} X).obj P).X p =
      P.obj (op ⟨op (SimplexCategory.mk p), ⊤⟩) :=
  rfl

section Sheaf

variable (X : SimplicialObject TopCat.{u})
  [HasSheafify (SimplicialOpen.grothendieckTopology X) Ab.{w}]

/-- The complex of sections of an abelian sheaf on the site of a simplicial topological space
over the whole spaces `X_p`, indexed by the natural numbers. -/
noncomputable def sheafWholeSpaceSectionsComplexNat :
    Sheaf (SimplicialOpen.grothendieckTopology X) Ab.{w} ⥤ CochainComplex Ab.{w} ℕ :=
  sheafToPresheaf _ Ab.{w} ⋙ wholeSpaceSectionsComplex.{u, w} X

/-- The functor `sheafWholeSpaceSectionsComplexNat` is additive. -/
instance sheafWholeSpaceSectionsComplexNat_additive :
    (sheafWholeSpaceSectionsComplexNat.{u, w} X).Additive := by
  dsimp only [sheafWholeSpaceSectionsComplexNat]
  infer_instance

/-- The complex of sections of an abelian sheaf over the whole spaces `X_p`, extended by zero to
integer degrees. -/
noncomputable def sheafWholeSpaceSectionsComplex :
    Sheaf (SimplicialOpen.grothendieckTopology X) Ab.{w} ⥤ CochainComplex Ab.{w} ℤ :=
  sheafWholeSpaceSectionsComplexNat.{u, w} X ⋙
    ComplexShape.embeddingUpNat.extendFunctor Ab.{w}

/-- The functor `sheafWholeSpaceSectionsComplex` is additive. -/
instance sheafWholeSpaceSectionsComplex_additive :
    (sheafWholeSpaceSectionsComplex.{u, w} X).Additive := by
  dsimp only [sheafWholeSpaceSectionsComplex]
  infer_instance

/-! ### The double complex -/

/-- The double complex of a complex of abelian sheaves, with the simplicial index in `ℕ`: in
outer degree `q` the complex of sections of the `q`-th term over the whole spaces `X_p`. -/
noncomputable def cohomologyDoubleComplexNatFunctor :
    CochainComplex (Sheaf (SimplicialOpen.grothendieckTopology X) Ab.{w}) ℤ ⥤
      HomologicalComplex (CochainComplex Ab.{w} ℕ) (ComplexShape.up ℤ) :=
  (sheafWholeSpaceSectionsComplexNat.{u, w} X).mapHomologicalComplex (ComplexShape.up ℤ)

/-- The double complex `A^{q,p} = Z^q(X_p)` of a complex `Z^•` of abelian sheaves on the site of
a simplicial topological space, with the degree in `Z^•` outer and the simplicial degree inner,
both extended by zero to integer degrees. -/
noncomputable def cohomologyDoubleComplexFunctor :
    CochainComplex (Sheaf (SimplicialOpen.grothendieckTopology X) Ab.{w}) ℤ ⥤
      HomologicalComplex₂ Ab.{w} (ComplexShape.up ℤ) (ComplexShape.up ℤ) :=
  (sheafWholeSpaceSectionsComplex.{u, w} X).mapHomologicalComplex (ComplexShape.up ℤ)

/-- The functor `cohomologyDoubleComplexFunctor` is additive. -/
instance cohomologyDoubleComplexFunctor_additive :
    (cohomologyDoubleComplexFunctor.{u, w} X).Additive := by
  dsimp only [cohomologyDoubleComplexFunctor]
  infer_instance

omit [HasSheafify (SimplicialOpen.grothendieckTopology X) Ab.{w}] in
/-- `cohomologyDoubleComplexFunctor` is `cohomologyDoubleComplexNatFunctor` with the simplicial
index extended by zero. -/
lemma cohomologyDoubleComplexFunctor_eq :
    cohomologyDoubleComplexFunctor.{u, w} X =
      cohomologyDoubleComplexNatFunctor.{u, w} X ⋙
        (ComplexShape.embeddingUpNat.extendFunctor Ab.{w}).mapHomologicalComplex
          (ComplexShape.up ℤ) :=
  rfl

omit [HasSheafify (SimplicialOpen.grothendieckTopology X) Ab.{w}] in
/-- **First-quadrant vanishing of the double complex.**  For a complex of abelian sheaves
vanishing in negative degrees, the `p`-th term of the homology in the outer degree `q` of the
double complex vanishes as soon as `p < 0` or `q < 0`. -/
lemma isZero_homology_cohomologyDoubleComplexFunctor_X
    (Z : CochainComplex (Sheaf (SimplicialOpen.grothendieckTopology X) Ab.{w}) ℤ)
    (hZ : ∀ q : ℤ, q < 0 → IsZero (Z.X q)) (p q : ℤ) (h : p < 0 ∨ q < 0) :
    IsZero ((((cohomologyDoubleComplexFunctor.{u, w} X).obj Z).homology q).X p) := by
  rcases h with hp | hq
  · refine (Iso.isZero_iff ((HomologicalComplex.eval Ab.{w} (ComplexShape.up ℤ) p).mapIso
      ((Functor.mapHomologicalComplexHomologyIso
        (ComplexShape.embeddingUpNat.extendFunctor Ab.{w}) (ComplexShape.up ℤ) q).app
          ((cohomologyDoubleComplexNatFunctor.{u, w} X).obj Z)))).2 ?_
    exact HomologicalComplex.isZero_extend_X _ ComplexShape.embeddingUpNat p
      fun i => by change ((i : ℕ) : ℤ) ≠ p; omega
  · refine Functor.map_isZero (HomologicalComplex.eval Ab.{w} (ComplexShape.up ℤ) p) ?_
    refine (HomologicalComplex.exactAt_iff_isZero_homology _ q).1
      (ShortComplex.exact_of_isZero_X₂ _ ?_)
    exact (sheafWholeSpaceSectionsComplex.{u, w} X).map_isZero (hZ q hq)

/-- The double complex of an `ℕ`-indexed complex of abelian sheaves: the complex extended by
zero in the negative degrees, fed to `cohomologyDoubleComplexFunctor`.  This is the functor the
chosen injective resolution is plugged into. -/
noncomputable def cohomologyDoubleComplexOfNatFunctor :
    CochainComplex (Sheaf (SimplicialOpen.grothendieckTopology X) Ab.{w}) ℕ ⥤
      HomologicalComplex₂ Ab.{w} (ComplexShape.up ℤ) (ComplexShape.up ℤ) :=
  ComplexShape.embeddingUpNat.extendFunctor
      (Sheaf (SimplicialOpen.grothendieckTopology X) Ab.{w}) ⋙
    cohomologyDoubleComplexFunctor.{u, w} X

variable [EnoughInjectives (Sheaf (SimplicialOpen.grothendieckTopology X) Ab.{w})]

/-- **The double complex `A^{q,p} = I^q(X_p)` of an abelian sheaf** on the site of a simplicial
topological space, for the chosen injective resolution `I^•` of the sheaf. -/
noncomputable def cohomologyDoubleComplex
    (F : Sheaf (SimplicialOpen.grothendieckTopology X) Ab.{w}) :
    HomologicalComplex₂ Ab.{w} (ComplexShape.up ℤ) (ComplexShape.up ℤ) :=
  (cohomologyDoubleComplexOfNatFunctor.{u, w} X).obj (injectiveResolution F).cocomplex

/-- The morphism of double complexes attached to a morphism of abelian sheaves: the double
complex of a chosen descent of that morphism to the chosen injective resolutions. -/
noncomputable def cohomologyDoubleComplexMap
    {F F' : Sheaf (SimplicialOpen.grothendieckTopology X) Ab.{w}} (f : F ⟶ F') :
    cohomologyDoubleComplex.{u, w} X F ⟶ cohomologyDoubleComplex.{u, w} X F' :=
  (cohomologyDoubleComplexOfNatFunctor.{u, w} X).map
    (InjectiveResolution.desc f (injectiveResolution F') (injectiveResolution F))

/-- A homotopy between two descents to the chosen injective resolutions induces a homotopy
between the induced morphisms of double complexes. -/
noncomputable def cohomologyDoubleComplexHomotopy
    {F F' : Sheaf (SimplicialOpen.grothendieckTopology X) Ab.{w}}
    {φ ψ : (injectiveResolution F).cocomplex ⟶ (injectiveResolution F').cocomplex}
    (H : Homotopy φ ψ) :
    Homotopy ((cohomologyDoubleComplexOfNatFunctor.{u, w} X).map φ)
      ((cohomologyDoubleComplexOfNatFunctor.{u, w} X).map ψ) :=
  (sheafWholeSpaceSectionsComplex.{u, w} X).mapHomotopy
    (H.extend ComplexShape.embeddingUpNat)

/-- `cohomologyDoubleComplexMap` sends an identity to a filtered homotopy class of the
identity. -/
lemma filteredHomotopy₂_cohomologyDoubleComplexMap_id
    (F : Sheaf (SimplicialOpen.grothendieckTopology X) Ab.{w}) :
    HomologicalComplex₂.FilteredHomotopy₂ (cohomologyDoubleComplexMap.{u, w} X (𝟙 F)) (𝟙 _) :=
  HomologicalComplex₂.filteredHomotopy₂_of_homotopy
    ((cohomologyDoubleComplexHomotopy.{u, w} X
        (InjectiveResolution.descIdHomotopy F (injectiveResolution F))).trans
      (Homotopy.ofEq ((cohomologyDoubleComplexOfNatFunctor.{u, w} X).map_id _)))

/-- `cohomologyDoubleComplexMap` is multiplicative up to filtered homotopy. -/
lemma filteredHomotopy₂_cohomologyDoubleComplexMap_comp
    {F F' F'' : Sheaf (SimplicialOpen.grothendieckTopology X) Ab.{w}} (f : F ⟶ F')
    (g : F' ⟶ F'') :
    HomologicalComplex₂.FilteredHomotopy₂ (cohomologyDoubleComplexMap.{u, w} X (f ≫ g))
      (cohomologyDoubleComplexMap.{u, w} X f ≫ cohomologyDoubleComplexMap.{u, w} X g) :=
  HomologicalComplex₂.filteredHomotopy₂_of_homotopy
    ((cohomologyDoubleComplexHomotopy.{u, w} X
        (InjectiveResolution.descCompHomotopy f g (injectiveResolution F)
          (injectiveResolution F') (injectiveResolution F''))).trans
      (Homotopy.ofEq ((cohomologyDoubleComplexOfNatFunctor.{u, w} X).map_comp _ _)))

/-! ### The spectral sequence -/

/-- The chosen injective resolution, extended by zero, vanishes in negative degrees. -/
lemma isZero_injectiveResolutionExtend_X
    (F : Sheaf (SimplicialOpen.grothendieckTopology X) Ab.{w}) (q : ℤ) (hq : q < 0) :
    IsZero (((ComplexShape.embeddingUpNat.extendFunctor
      (Sheaf (SimplicialOpen.grothendieckTopology X) Ab.{w})).obj
        (injectiveResolution F).cocomplex).X q) :=
  HomologicalComplex.isZero_extend_X _ ComplexShape.embeddingUpNat q
    fun i => by change ((i : ℕ) : ℤ) ≠ q; omega

/-- **The spectral sequence of a simplicial topological space on `ℤ × ℤ`**, functorial in the
abelian sheaf: the second spectral sequence of the double complex `A^{q,p} = I^q(X_p)` of the
chosen injective resolution, presented from its first page.  The functor laws hold because
filtered homotopic morphisms of double complexes induce the same maps on the pages from the
first on. -/
noncomputable def cohomologySpectralSequenceZ :
    Sheaf (SimplicialOpen.grothendieckTopology X) Ab.{w} ⥤
      CohomologicalSpectralSequence Ab.{w} 1 where
  obj F := (Stacks.Cohomology.CechSpectral.restrictR₀ (show (0 : ℤ) ≤ 1 by omega)).obj
    (cohomologyDoubleComplex.{u, w} X F).spectralSequence₂
  map f := (Stacks.Cohomology.CechSpectral.restrictR₀ (show (0 : ℤ) ≤ 1 by omega)).map
    (HomologicalComplex₂.spectralSequenceMap₂ (cohomologyDoubleComplexMap.{u, w} X f))
  map_id F := by
    refine CategoryTheory.SpectralSequence.hom_ext fun r hr => ?_
    refine Eq.trans (HomologicalComplex₂.spectralSequenceMap₂_hom_eq_of_filteredHomotopy₂
      (filteredHomotopy₂_cohomologyDoubleComplexMap_id.{u, w} X F)
      (show (1 : ℤ) ≤ r by omega)) ?_
    rw [HomologicalComplex₂.spectralSequenceMap₂_id]
    simp
  map_comp f g := by
    refine CategoryTheory.SpectralSequence.hom_ext fun r hr => ?_
    refine Eq.trans (HomologicalComplex₂.spectralSequenceMap₂_hom_eq_of_filteredHomotopy₂
      (filteredHomotopy₂_cohomologyDoubleComplexMap_comp.{u, w} X f g)
      (show (1 : ℤ) ≤ r by omega)) ?_
    rw [HomologicalComplex₂.spectralSequenceMap₂_comp]
    rfl

/-- **The spectral sequence of a simplicial topological space lies in the first quadrant.**  The
first page at `(p, q)` is the `p`-th term of the homology in outer degree `q` of a double complex
concentrated in the first quadrant. -/
lemma isFirstQuadrant_cohomologySpectralSequenceZ
    (F : Sheaf (SimplicialOpen.grothendieckTopology X) Ab.{w}) :
    CategoryTheory.SpectralSequence.IsFirstQuadrant (u := fun r => (r, 1 - r))
      ((cohomologySpectralSequenceZ.{u, w} X).obj F) := by
  refine CategoryTheory.SpectralSequence.isFirstQuadrant_of_isZero_page _ fun x hx => ?_
  refine (Iso.isZero_iff (HomologicalComplex₂.isoOnePageTotalFiltration₂
    (cohomologyDoubleComplex.{u, w} X F) _
    (HomologicalComplex₂.pageIso₂ _) (HomologicalComplex₂.exists_delta₂ _) x.1 x.2)).2 ?_
  exact isZero_homology_cohomologyDoubleComplexFunctor_X.{u, w} X _
    (isZero_injectiveResolutionExtend_X.{u, w} X F) x.1 x.2 hx

/-- **Stacks 09W6.**  For an abelian sheaf `F` on the site of a simplicial topological space `X`
there is a first-quadrant cohomological spectral sequence, functorial in `F`: the second spectral
sequence of the double complex `A^{q,p} = I^q(X_p)` of a chosen injective resolution of `F`,
presented from its first page.  Its first page is `cohomologySpectralSequence_pageOneIso`, and its
convergence to `H^{p+q}(X_Zar, F)` is `cohomologySpectralSequence_abutment`. -/
@[stacks 09W6 "the spectral sequence, functorial in the abelian sheaf"]
noncomputable def cohomologySpectralSequence :
    Sheaf (SimplicialOpen.grothendieckTopology X) Ab.{w} ⥤
      CohomologicalSpectralSequenceNat Ab.{w} 1 :=
  CategoryTheory.SpectralSequence.natRestrictComp (cohomologySpectralSequenceZ.{u, w} X)
    (isFirstQuadrant_cohomologySpectralSequenceZ.{u, w} X)

end Sheaf

/-! ### The first page -/

section Component

variable (X : SimplicialObject TopCat.{u}) (n : ℕ)
  [HasSheafify (SimplicialOpen.grothendieckTopology X) Ab.{w}]
  [HasSheafify (Opens.grothendieckTopology (X.obj (op (SimplexCategory.mk n)))) Ab.{w}]

/-- Restriction of abelian sheaves from the site of a simplicial topological space to the site of
the space in its degree `n`. -/
noncomputable def componentRestriction :
    Sheaf (SimplicialOpen.grothendieckTopology X) Ab.{w} ⥤
      Sheaf (Opens.grothendieckTopology (X.obj (op (SimplexCategory.mk n)))) Ab.{w} :=
  (levelFunctor X (op (SimplexCategory.mk n))).sheafPushforwardContinuous Ab.{w}
    (Opens.grothendieckTopology (X.obj (op (SimplexCategory.mk n))))
    (SimplicialOpen.grothendieckTopology X)

/-- Global sections of an abelian sheaf on the space in degree `n` of a simplicial topological
space. -/
noncomputable def componentGlobalSections :
    Sheaf (Opens.grothendieckTopology (X.obj (op (SimplexCategory.mk n)))) Ab.{w} ⥤ Ab.{w} :=
  (sheafSections (Opens.grothendieckTopology (X.obj (op (SimplexCategory.mk n)))) Ab.{w}).obj
    (op ⊤)

/-- The sections over the whole space `X_n` of an abelian sheaf on the site of a simplicial
topological space: the global sections of its restriction to `X_n`. -/
noncomputable def componentSections :
    Sheaf (SimplicialOpen.grothendieckTopology X) Ab.{w} ⥤ Ab.{w} :=
  componentRestriction.{u, w} X n ⋙ componentGlobalSections.{u, w} X n

/-- The functor `componentGlobalSections` is additive. -/
instance componentGlobalSections_additive : (componentGlobalSections.{u, w} X n).Additive := by
  dsimp only [componentGlobalSections]
  infer_instance

/-! #### Exactness of the restriction to a component -/

variable [∀ F : (Opens (X.obj (op (SimplexCategory.mk n))))ᵒᵖ ⥤ Ab.{w},
    (levelFunctor X (op (SimplexCategory.mk n))).op.HasLeftKanExtension F]
  [∀ F : (Opens (X.obj (op (SimplexCategory.mk n))))ᵒᵖ ⥤ Ab.{w},
    (levelFunctor X (op (SimplexCategory.mk n))).op.HasPointwiseRightKanExtension F]

/-- **Stacks 09W0.**  Restriction of abelian sheaves to a degree of a simplicial topological
space preserves finite limits: it is right adjoint to lower shriek. -/
instance componentRestriction_preservesFiniteLimits :
    PreservesFiniteLimits (componentRestriction.{u, w} X n) := by
  have := (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    (levelFunctor X (op (SimplexCategory.mk n))) Ab.{w}
    (Opens.grothendieckTopology (X.obj (op (SimplexCategory.mk n))))
    (SimplicialOpen.grothendieckTopology X)).rightAdjoint_preservesLimits
  dsimp only [componentRestriction]
  infer_instance

/-- **Stacks 09W0.**  Restriction of abelian sheaves to a degree of a simplicial topological
space preserves finite colimits: the inclusion of the component site is cocontinuous, so
restriction is the inverse image of a morphism of topoi, hence a left adjoint. -/
instance componentRestriction_preservesFiniteColimits :
    PreservesFiniteColimits (componentRestriction.{u, w} X n) := by
  have : PreservesColimitsOfSize.{0, 0} (componentRestriction.{u, w} X n) :=
    ((levelFunctor X (op (SimplexCategory.mk n))).sheafAdjunctionCocontinuous Ab.{w}
      (Opens.grothendieckTopology (X.obj (op (SimplexCategory.mk n))))
      (SimplicialOpen.grothendieckTopology X)).leftAdjoint_preservesColimits
  infer_instance

/-- The functor `componentRestriction` is additive. -/
instance componentRestriction_additive : (componentRestriction.{u, w} X n).Additive :=
  Functor.additive_of_preserves_binary_products _

/-- The functor `componentSections` is additive. -/
instance componentSections_additive : (componentSections.{u, w} X n).Additive := by
  dsimp only [componentSections]
  infer_instance

variable [EnoughInjectives (Sheaf (SimplicialOpen.grothendieckTopology X) Ab.{w})]
  [EnoughInjectives (Sheaf (Opens.grothendieckTopology (X.obj (op (SimplexCategory.mk n))))
    Ab.{w})]

/-- **Stacks 09W1.**  Restriction of abelian sheaves to a degree of a simplicial topological
space preserves injective objects. -/
instance componentRestriction_preservesInjectiveObjects :
    (componentRestriction.{u, w} X n).PreservesInjectiveObjects :=
  componentRestrictionAb_preservesInjectiveObjects.{u, w} X n

omit [EnoughInjectives (Sheaf (Opens.grothendieckTopology (X.obj (op (SimplexCategory.mk n))))
  Ab.{w})] in
/-- Every abelian sheaf is acyclic for the restriction to a degree, restriction being exact. -/
lemma isZero_rightDerived_componentRestriction
    (F : Sheaf (SimplicialOpen.grothendieckTopology X) Ab.{w}) (q : ℕ) (hq : 0 < q) :
    IsZero (((componentRestriction.{u, w} X n).rightDerived q).obj F) := by
  obtain ⟨m, rfl⟩ : ∃ m, q = m + 1 := ⟨q - 1, by omega⟩
  refine (Iso.isZero_iff ((injectiveResolution F).isoRightDerivedObj
    (componentRestriction.{u, w} X n) (m + 1) ≪≫
      (Functor.mapHomologicalComplexHomologyIso (componentRestriction.{u, w} X n)
        (ComplexShape.up ℕ) (m + 1)).app (injectiveResolution F).cocomplex)).2 ?_
  refine Functor.map_isZero (componentRestriction.{u, w} X n) ?_
  refine (HomologicalComplex.exactAt_iff_isZero_homology _ (m + 1)).1 ?_
  exact (quasiIsoAt_iff_exactAt (injectiveResolution F).ι (m + 1)
    (CochainComplex.exactAt_succ_single_obj _ _)).1 inferInstance

/-- **`H^q(X_n, -_n)`**: the `q`-th right derived functor of the global sections on `X_n`, applied
to the restriction to `X_n`.  This is the sheaf cohomology of the degree-`n` component. -/
noncomputable def componentCohomologyFunctor (q : ℕ) :
    Sheaf (SimplicialOpen.grothendieckTopology X) Ab.{w} ⥤ Ab.{w} :=
  componentRestriction.{u, w} X n ⋙ (componentGlobalSections.{u, w} X n).rightDerived q

end Component

/-! #### The first page is the cohomology of the components -/

/-- Extending the inner complexes by zero, taking homology in the outer degree and evaluating in
the simplicial degree `(n : ℤ)` is evaluating in the simplicial degree `n` and then taking
homology in the outer degree.  Both extension by zero and evaluation of a complex in a fixed
degree are exact. -/
noncomputable def extendEvalHomologyNatIso (n q : ℕ) :
    (ComplexShape.embeddingUpNat.extendFunctor Ab.{w}).mapHomologicalComplex
          (ComplexShape.up ℤ) ⋙
        HomologicalComplex.homologyFunctor (CochainComplex Ab.{w} ℤ) (ComplexShape.up ℤ) (q : ℤ) ⋙
          HomologicalComplex.eval Ab.{w} (ComplexShape.up ℤ) (n : ℤ) ≅
      (HomologicalComplex.eval Ab.{w} (ComplexShape.up ℕ) n).mapHomologicalComplex
          (ComplexShape.up ℤ) ⋙
        HomologicalComplex.homologyFunctor Ab.{w} (ComplexShape.up ℤ) (q : ℤ) :=
  Functor.isoWhiskerRight
      (Functor.mapHomologicalComplexHomologyIso
        (ComplexShape.embeddingUpNat.extendFunctor Ab.{w}) (ComplexShape.up ℤ) (q : ℤ))
      (HomologicalComplex.eval Ab.{w} (ComplexShape.up ℤ) (n : ℤ)) ≪≫
    Functor.isoWhiskerLeft
      (HomologicalComplex.homologyFunctor (CochainComplex Ab.{w} ℕ) (ComplexShape.up ℤ) (q : ℤ))
      (ComplexShape.embeddingUpNat.extendFunctorCompEvalIso Ab.{w} (i := n) rfl) ≪≫
    (Functor.mapHomologicalComplexHomologyIso
      (HomologicalComplex.eval Ab.{w} (ComplexShape.up ℕ) n) (ComplexShape.up ℤ) (q : ℤ)).symm


section PageOne

variable (X : SimplicialObject TopCat.{u}) (n : ℕ)
  [HasSheafify (SimplicialOpen.grothendieckTopology X) Ab.{w}]
  [HasSheafify (Opens.grothendieckTopology (X.obj (op (SimplexCategory.mk n)))) Ab.{w}]
  [∀ F : (Opens (X.obj (op (SimplexCategory.mk n))))ᵒᵖ ⥤ Ab.{w},
    (levelFunctor X (op (SimplexCategory.mk n))).op.HasLeftKanExtension F]
  [∀ F : (Opens (X.obj (op (SimplexCategory.mk n))))ᵒᵖ ⥤ Ab.{w},
    (levelFunctor X (op (SimplexCategory.mk n))).op.HasPointwiseRightKanExtension F]

/-- **The columns of the double complex compute the cohomology of the components.**  Taking the
homology in the outer degree `q` of the double complex of a complex of abelian sheaves and then
its term in the simplicial degree `n` is taking the sections over `X_n` degreewise and then the
`q`-th cohomology, naturally in the complex of abelian sheaves. -/
noncomputable def columnHomologyNatIso (q : ℕ) :
    cohomologyDoubleComplexOfNatFunctor.{u, w} X ⋙
        HomologicalComplex.homologyFunctor (CochainComplex Ab.{w} ℤ) (ComplexShape.up ℤ) (q : ℤ) ⋙
          HomologicalComplex.eval Ab.{w} (ComplexShape.up ℤ) (n : ℤ) ≅
      (componentSections.{u, w} X n).mapHomologicalComplex (ComplexShape.up ℕ) ⋙
        HomologicalComplex.homologyFunctor Ab.{w} (ComplexShape.up ℕ) q :=
  Functor.isoWhiskerLeft
      (ComplexShape.embeddingUpNat.extendFunctor
          (Sheaf (SimplicialOpen.grothendieckTopology X) Ab.{w}) ⋙
        cohomologyDoubleComplexNatFunctor.{u, w} X)
      (extendEvalHomologyNatIso.{w} n q) ≪≫
    Stacks.CategoryTheory.Hypercovering.extendUpNatMapHomologyNatIso
      (componentSections.{u, w} X n) q


variable [EnoughInjectives (Sheaf (SimplicialOpen.grothendieckTopology X) Ab.{w})]
  [EnoughInjectives (Sheaf (Opens.grothendieckTopology (X.obj (op (SimplexCategory.mk n))))
    Ab.{w})]

/-- The first page of the spectral sequence at `(n, q)`, as a functor of the abelian sheaf. -/
noncomputable abbrev pageOneFunctor (q : ℕ) :
    Sheaf (SimplicialOpen.grothendieckTopology X) Ab.{w} ⥤ Ab.{w} :=
  cohomologySpectralSequence.{u, w} X ⋙
    CategoryTheory.SpectralSequence.pageFunctor Ab.{w} _ 1 1 ⋙
      HomologicalComplex.eval Ab.{w} _ (n, q)

/-- The identification of the first page of the spectral sequence at `(n, q)` with the `q`-th
cohomology of the complex of sections over `X_n` of the chosen injective resolution. -/
noncomputable def pageOneIsoColumnHomology (q : ℕ)
    (F : Sheaf (SimplicialOpen.grothendieckTopology X) Ab.{w}) :
    (pageOneFunctor.{u, w} X n q).obj F ≅
      (((componentSections.{u, w} X n).mapHomologicalComplex (ComplexShape.up ℕ)).obj
        (injectiveResolution F).cocomplex).homology q :=
  HomologicalComplex₂.isoOnePageTotalFiltration₂ (cohomologyDoubleComplex.{u, w} X F) _
      (HomologicalComplex₂.pageIso₂ _) (HomologicalComplex₂.exists_delta₂ _) (n : ℤ) (q : ℤ) ≪≫
    (columnHomologyNatIso.{u, w} X n q).app (injectiveResolution F).cocomplex

omit [∀ F : (Opens (X.obj (op (SimplexCategory.mk n))))ᵒᵖ ⥤ Ab.{w},
  (levelFunctor X (op (SimplexCategory.mk n))).op.HasPointwiseRightKanExtension F]
  [EnoughInjectives (Sheaf (Opens.grothendieckTopology (X.obj (op (SimplexCategory.mk n))))
    Ab.{w})] in
/-- `pageOneIsoColumnHomology` is the identification of the first page of the second spectral
sequence of the double complex followed by the identification of its columns. -/
lemma pageOneIsoColumnHomology_hom_eq (q : ℕ)
    (F : Sheaf (SimplicialOpen.grothendieckTopology X) Ab.{w}) :
    (pageOneIsoColumnHomology.{u, w} X n q F).hom =
      (HomologicalComplex₂.isoOnePageTotalFiltration₂ (cohomologyDoubleComplex.{u, w} X F) _
          (HomologicalComplex₂.pageIso₂ _) (HomologicalComplex₂.exists_delta₂ _)
          (n : ℤ) (q : ℤ)).hom ≫
        ((columnHomologyNatIso.{u, w} X n q).app (injectiveResolution F).cocomplex).hom :=
  rfl

omit [∀ F : (Opens (X.obj (op (SimplexCategory.mk n))))ᵒᵖ ⥤ Ab.{w},
  (levelFunctor X (op (SimplexCategory.mk n))).op.HasPointwiseRightKanExtension F]
  [EnoughInjectives (Sheaf (Opens.grothendieckTopology (X.obj (op (SimplexCategory.mk n))))
    Ab.{w})] in
/-- `pageOneIsoColumnHomology` is natural in the abelian sheaf, for the chosen descent of a
morphism to the chosen injective resolutions. -/
lemma pageOneIsoColumnHomology_hom_naturality (q : ℕ)
    {F F' : Sheaf (SimplicialOpen.grothendieckTopology X) Ab.{w}} (f : F ⟶ F') :
    (pageOneFunctor.{u, w} X n q).map f ≫ (pageOneIsoColumnHomology.{u, w} X n q F').hom =
      (pageOneIsoColumnHomology.{u, w} X n q F).hom ≫
        HomologicalComplex.homologyMap
          (((componentSections.{u, w} X n).mapHomologicalComplex (ComplexShape.up ℕ)).map
            (InjectiveResolution.desc f (injectiveResolution F') (injectiveResolution F))) q := by
  have h1 : (pageOneFunctor.{u, w} X n q).map f ≫
      (HomologicalComplex₂.isoOnePageTotalFiltration₂ (cohomologyDoubleComplex.{u, w} X F') _
        (HomologicalComplex₂.pageIso₂ _) (HomologicalComplex₂.exists_delta₂ _)
        (n : ℤ) (q : ℤ)).hom =
      (HomologicalComplex₂.isoOnePageTotalFiltration₂ (cohomologyDoubleComplex.{u, w} X F) _
          (HomologicalComplex₂.pageIso₂ _) (HomologicalComplex₂.exists_delta₂ _)
          (n : ℤ) (q : ℤ)).hom ≫
        (HomologicalComplex.homologyMap (cohomologyDoubleComplexMap.{u, w} X f) (q : ℤ)).f
          (n : ℤ) :=
    HomologicalComplex₂.isoOnePageTotalFiltration₂_naturality_functor
      (cohomologyDoubleComplexMap.{u, w} X f) (n : ℤ) (q : ℤ)
  have h2 : (HomologicalComplex.homologyMap (cohomologyDoubleComplexMap.{u, w} X f) (q : ℤ)).f
        (n : ℤ) ≫
      ((columnHomologyNatIso.{u, w} X n q).app (injectiveResolution F').cocomplex).hom =
      ((columnHomologyNatIso.{u, w} X n q).app (injectiveResolution F).cocomplex).hom ≫
        HomologicalComplex.homologyMap
          (((componentSections.{u, w} X n).mapHomologicalComplex (ComplexShape.up ℕ)).map
            (InjectiveResolution.desc f (injectiveResolution F') (injectiveResolution F))) q :=
    (columnHomologyNatIso.{u, w} X n q).hom.naturality
      (InjectiveResolution.desc f (injectiveResolution F') (injectiveResolution F))
  rw [pageOneIsoColumnHomology_hom_eq, pageOneIsoColumnHomology_hom_eq]
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun z => z ≫ ((columnHomologyNatIso.{u, w} X n q).app
          (injectiveResolution F').cocomplex).hom) h1).trans
      ((Category.assoc _ _ _).trans
        ((congrArg (fun z =>
            (HomologicalComplex₂.isoOnePageTotalFiltration₂ (cohomologyDoubleComplex.{u, w} X F) _
              (HomologicalComplex₂.pageIso₂ _) (HomologicalComplex₂.exists_delta₂ _)
              (n : ℤ) (q : ℤ)).hom ≫ z) h2).trans (Category.assoc _ _ _).symm)))

/-- **Stacks 09W0 and 09W1 for the chosen resolution.**  The right derived functors of the
sections over `X_n` are the sheaf cohomology of the restriction to `X_n`: restriction to a degree
is exact and preserves injective abelian sheaves, so the restricted resolution is an injective
resolution of the restriction. -/
noncomputable def rightDerivedSectionsIsoComponentCohomology (q : ℕ)
    (F : Sheaf (SimplicialOpen.grothendieckTopology X) Ab.{w}) :
    ((componentSections.{u, w} X n).rightDerived q).obj F ≅
      (componentCohomologyFunctor.{u, w} X n q).obj F :=
  Stacks.RightDerivedComp.objIso (componentRestriction.{u, w} X n) (injectiveResolution F)
    (isZero_rightDerived_componentRestriction.{u, w} X n F)
    (componentGlobalSections.{u, w} X n) q

/-- `rightDerivedSectionsIsoComponentCohomology` is natural in the abelian sheaf, for the chosen
descent of a morphism to the chosen injective resolutions. -/
lemma rightDerivedSectionsIsoComponentCohomology_hom_naturality (q : ℕ)
    {F F' : Sheaf (SimplicialOpen.grothendieckTopology X) Ab.{w}} (f : F ⟶ F') :
    ((componentSections.{u, w} X n).rightDerived q).map f ≫
        (rightDerivedSectionsIsoComponentCohomology.{u, w} X n q F').hom =
      (rightDerivedSectionsIsoComponentCohomology.{u, w} X n q F).hom ≫
        (componentCohomologyFunctor.{u, w} X n q).map f :=
  Stacks.RightDerivedComp.objIso_hom_naturality_of_desc (componentRestriction.{u, w} X n)
    (componentGlobalSections.{u, w} X n) q (injectiveResolution F) (injectiveResolution F')
    (isZero_rightDerived_componentRestriction.{u, w} X n F)
    (isZero_rightDerived_componentRestriction.{u, w} X n F') f _
    (InjectiveResolution.desc_commutes_zero f (injectiveResolution F') (injectiveResolution F))

/-- The first page of the spectral sequence at `(n, q)` is the sheaf cohomology
`H^q(X_n, F_n)`. -/
noncomputable def pageOneIsoComponentCohomology (q : ℕ)
    (F : Sheaf (SimplicialOpen.grothendieckTopology X) Ab.{w}) :
    (pageOneFunctor.{u, w} X n q).obj F ≅ (componentCohomologyFunctor.{u, w} X n q).obj F :=
  pageOneIsoColumnHomology.{u, w} X n q F ≪≫
    ((injectiveResolution F).isoRightDerivedObj (componentSections.{u, w} X n) q).symm ≪≫
      rightDerivedSectionsIsoComponentCohomology.{u, w} X n q F

/-- `pageOneIsoComponentCohomology` unfolded. -/
lemma pageOneIsoComponentCohomology_hom_eq (q : ℕ)
    (F : Sheaf (SimplicialOpen.grothendieckTopology X) Ab.{w}) :
    (pageOneIsoComponentCohomology.{u, w} X n q F).hom =
      (pageOneIsoColumnHomology.{u, w} X n q F).hom ≫
        ((injectiveResolution F).isoRightDerivedObj (componentSections.{u, w} X n) q).inv ≫
          (rightDerivedSectionsIsoComponentCohomology.{u, w} X n q F).hom :=
  rfl

/-- **Stacks 09W6.**  The first page of the spectral sequence of a simplicial topological space
is `E_1^{p,q} = H^q(X_p, F_p)`, the sheaf cohomology of the restriction of `F` to the space in
simplicial degree `p`, naturally in the abelian sheaf `F`. -/
@[stacks 09W6 "the first page is H^q(X_p, F_p)"]
noncomputable def cohomologySpectralSequence_pageOneIso (q : ℕ) :
    pageOneFunctor.{u, w} X n q ≅ componentCohomologyFunctor.{u, w} X n q :=
  NatIso.ofComponents (pageOneIsoComponentCohomology.{u, w} X n q) (fun {F F'} f => by
    rw [pageOneIsoComponentCohomology_hom_eq, pageOneIsoComponentCohomology_hom_eq]
    exact square_comp₃
      (pageOneIsoColumnHomology_hom_naturality.{u, w} X n q f)
      (InjectiveResolution.isoRightDerivedObj_inv_naturality f (injectiveResolution F)
        (injectiveResolution F') _
        (InjectiveResolution.desc_commutes_zero f (injectiveResolution F')
          (injectiveResolution F)) (componentSections.{u, w} X n) q).symm
      (rightDerivedSectionsIsoComponentCohomology_hom_naturality.{u, w} X n q f))

end PageOne

end Stacks.Topology.Simplicial

end
