module

public import Mathlib.CategoryTheory.Abelian.Injective.Resolution
public import StacksFrontier.CategoryTheory.Sites.GrothendieckAbelianUnivLE
public import StacksFrontier.CategoryTheory.Sites.Hypercovering.Basic
public import StacksFrontier.CategoryTheory.Sites.Hypercovering.SpectralSequencePageTwo
public import StacksFrontier.Topology.Sheaves.Cohomology.CechSpectralSequence.SequenceAndSecondPage
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The hypercovering spectral sequence of a small site: the sequence

Let `C` be a site, `X` an object of `C` and `K` a simplicial object of `FormalCoproduct (Over X)`
-- a simplicial semi-representable object over `X`, `SR(C, X)` in the source. Clause (3) of
[Stacks, Tag 01GY] asserts the existence of a first-quadrant `E₂` cohomological spectral sequence
`E₂^{p,q} = Ȟ^p(K, H^q(F)) ⇒ H^{p+q}(X, F)`, functorial in the coefficient sheaf `F` **and** in
the hypercovering `K`. This file supplies the `sequence` of that assertion and nothing else: the
two-variable functor
```
(SR(C, X)-simplicial objects)ᵒᵖ × Sheaf J AddCommGrp ⥤
  E₂CohomologicalSpectralSequenceNat AddCommGrp
```
together with its restriction to the full subcategory of hypercoverings. The second-page
isomorphism and the filtered abutment are *not* here.

## The site is small

The site of the source is a *literally small* category: a category has a **set** of objects and,
for each pair of objects, a **set** of morphisms ([Stacks, Tag 0005]), and sites are not allowed
to be "big" categories ([Stacks, Tag 00VI]). So `C : Type v` with `SmallCategory C`, and then the
universe `max u v w` in which the Čech complex of a `w`-indexed semi-representable object over an
object of a `Category.{v, u} C` takes its coefficients collapses to `v`, which is also the
universe of the coefficient sheaves. Every universe obstruction described in the implementation
notes of `StacksFrontier/CategoryTheory/Sites/Hypercovering/SpectralSequencePageTwo.lean` disappears
with it: `HasSheafify J AddCommGrpCat.{v}` and `EnoughInjectives (Sheaf J AddCommGrpCat.{v})` are
instances, so the injective resolution may be taken in the coefficient universe itself, and no
universe lift and no comparison of `Ext` groups is needed.

## The index orientation

The double complex whose second spectral sequence this is has the **resolution degree outer and
the Čech degree inner**,
```
A^{i,j}(K, F) = Č^j(K, I^i(F)),
```
for the chosen injective resolution `I^•(F)` of `F` in `Sheaf J AddCommGrpCat.{v}`. That
orientation is forced: the second spectral sequence of a double complex has
`''E_2^{p,q} = H^p_{II}(H^q_I(A^{•,•}))` and `H^q_I` is homology in the *first* (outer) index, so
it is the resolution degree that must be differentiated first for `''E_2^{p,q}` to come out as
Čech cohomology of a derived functor. Both indices are extended by zero from `ℕ` to `ℤ`, which is
what makes the first-quadrant vanishing of `H^p_{II}(H^q_I(-))` immediate, and the orientation is
also what lets a homotopy in the resolution direction be read as a filtered homotopy of total
complexes: its components have degree `(-1, 0)` and so preserve the filtration by the second
coordinate.

An injective resolution is functorial in the sheaf only up to homotopy, so `hypercoverDouble` is
not a functor of the pair `(K, F)`. It is the object part of a functor up to filtered homotopy,
which is exactly the input of `HomologicalComplex₂.e₂FunctorOfHomotopyClasses`; the source
category of that engine is arbitrary, so the two-variable functoriality of [Stacks, Tag 01GY]
costs nothing once the Čech double complex is made a functor of `K` as well -- and in the `K`
direction it is a functor on the nose.

## Main definitions

* `Stacks.CategoryTheory.Hypercovering.Functorial.cechDoubleBifunctor`: `Č^•(K, -)` applied to a
  complex of presheaves of abelian groups, as a double complex over `ℤ × ℤ`, functorial in the
  complex and contravariantly functorial in `K`.
* `Stacks.CategoryTheory.Hypercovering.Functorial.hypercoverDouble`,
  `Stacks.CategoryTheory.Hypercovering.Functorial.hypercoverDoubleMap`: the same at the chosen
  injective resolution of a sheaf, together with the morphism induced by a morphism of the
  pair `(K, F)`.
* `Stacks.CategoryTheory.Hypercovering.Functorial.hypercoverE₂Functor`,
  `Stacks.CategoryTheory.Hypercovering.Functorial.hypercoverSpectralSequenceFunctor`: the resulting
  two-variable `E₂` spectral sequence, on `ℤ × ℤ` and then on `ℕ × ℕ`.
* `Stacks.CategoryTheory.Hypercovering.Functorial.hypercoveringSpectralSequence`: the **`sequence`
  of clause (3) of [Stacks, Tag 01GY]**, the restriction of the previous functor to the full
  subcategory of hypercoverings for a pretopology.

## Main results

* `Stacks.CategoryTheory.Hypercovering.Functorial.cechDoubleBifunctorXIso`:
  `A^{i,j} = Č^j(K, Y^i)`, which records the index orientation.
* `Stacks.CategoryTheory.Hypercovering.Functorial.isZero_homologyIIHomologyI_extend`:
  first-quadrant vanishing of `H^p_{II}(H^q_I(-))` for a double complex extended by zero from
  `ℕ × ℕ`.
* `Stacks.CategoryTheory.Hypercovering.Functorial.isFirstQuadrant_hypercoverE₂Functor`: the
  spectral sequence is first quadrant from its second page on, which is what
  `CategoryTheory.SpectralSequence.natRestrictE₂Comp` needs to reindex it by `ℕ × ℕ`.

## Implementation notes

**Nothing here carries the tag `01GY`, and no `@[stacks ...]` attribute appears in this file.** A
tag lands only when its whole covering set lands, and the covering set of [Stacks, Tag 01GY]
clause (3) also contains the identification of the second page with
`Stacks.CategoryTheory.Hypercovering.pageTwoBifunctor` and the identification of the abutment with
`H^{p+q}(X, F)`; neither is here.

The additivity of the Čech complex functor at a fixed `K` is not found by instance search for an
arbitrary object of the opposite category, because the exactness instances of
`SpectralSequencePageTwo.lean` are stated at `op K`. The two instances at the top of this file
restate them for an arbitrary object, which is the form the bifunctors below need.

## Namespace

The declarations of this file and of the three that continue it --
`StacksFrontier.CategoryTheory.Sites.Hypercovering.SpectralSequenceSecondPage`,
`StacksFrontier.CategoryTheory.Sites.Hypercovering.SpectralSequenceAbutment` and
`StacksFrontier.CategoryTheory.Sites.Hypercovering.SpectralSequenceAbutmentIsCohomology` -- live in
`Stacks.CategoryTheory.Hypercovering.Functorial`.
`StacksFrontier.CategoryTheory.Sites.Hypercovering.SpectralSequence` carries a second development of
clause (3) of [Stacks, Tag 01GY], for one fixed hypercovering of a site with fibre products and
with the functoriality in the hypercovering supplied separately, in the enclosing namespace
`Stacks.CategoryTheory.Hypercovering`. Neither subsumes the other: that one does not assume the
site small, this one is a single functor of the pair `(K, F)` on a small site, and no comparison
of the two is formalized.

## References

* [Stacks Project, Tag 0005](https://stacks.math.columbia.edu/tag/0005)
* [Stacks Project, Tag 00VI](https://stacks.math.columbia.edu/tag/00VI)
* [Stacks Project, Tag 01G5](https://stacks.math.columbia.edu/tag/01G5)
* [Stacks Project, Tag 01GY](https://stacks.math.columbia.edu/tag/01GY)
* [Stacks Project, Tag 0130](https://stacks.math.columbia.edu/tag/0130)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe w v₁ u₁ v

namespace Stacks.CategoryTheory.Hypercovering.Functorial

section Exactness

variable {C : Type u₁} [Category.{v₁} C] (X : C)

/-- `preservesZeroMorphisms_cechComplexOverBifunctor_obj`, restated for an arbitrary object of
the opposite category rather than one of the form `op K`; this is the form instance search needs
when the simplicial semi-representable object is itself a variable of a functor. -/
instance preservesZeroMorphisms_cechComplexOverBifunctor_obj'
    (K : (SimplicialObject (FormalCoproduct.{w} (Over X)))ᵒᵖ) :
    ((cechComplexOverBifunctor.{w} X).obj K).PreservesZeroMorphisms :=
  inferInstanceAs ((cechComplexOverBifunctor.{w} X).obj (op K.unop)).PreservesZeroMorphisms

/-- **The Čech complex functor of a simplicial semi-representable object is additive.** It
preserves finite limits, hence binary products, and a functor between preadditive categories
preserving binary products is additive. -/
instance additive_cechComplexOverBifunctor_obj
    (K : (SimplicialObject (FormalCoproduct.{w} (Over X)))ᵒᵖ) :
    ((cechComplexOverBifunctor.{w} X).obj K).Additive :=
  letI : PreservesFiniteLimits ((cechComplexOverBifunctor.{w} X).obj K) :=
    inferInstanceAs (PreservesFiniteLimits ((cechComplexOverBifunctor.{w} X).obj (op K.unop)))
  Functor.additive_of_preserves_binary_products _

end Exactness

section SmallSite

variable {C : Type v} [SmallCategory C] (X : C) (J : GrothendieckTopology C)

/-- **The Čech double complex of a complex of presheaves of abelian groups, over `ℕ × ℕ`**: in
bidegree `(i, j)` the `j`-th term of the Čech complex of the `i`-th term of the given complex,
contravariantly functorial in the simplicial semi-representable object. The **degree in the given
complex is the outer index and the Čech degree the inner one**; see the module documentation for
why that is forced. -/
def cechDoubleNatBifunctor :
    (SimplicialObject (FormalCoproduct.{v} (Over X)))ᵒᵖ ⥤
      CochainComplex (Cᵒᵖ ⥤ AddCommGrpCat.{v}) ℕ ⥤
        HomologicalComplex (CochainComplex AddCommGrpCat.{v} ℕ) (ComplexShape.up ℕ) where
  obj K := ((cechComplexOverBifunctor.{v} X).obj K).mapHomologicalComplex (ComplexShape.up ℕ)
  map f :=
    NatTrans.mapHomologicalComplex ((cechComplexOverBifunctor.{v} X).map f) (ComplexShape.up ℕ)
  map_id K := by
    rw [CategoryTheory.Functor.map_id]
    exact NatTrans.mapHomologicalComplex_id (ComplexShape.up ℕ)
      ((cechComplexOverBifunctor.{v} X).obj K)
  map_comp f g := by
    rw [CategoryTheory.Functor.map_comp]
    exact NatTrans.mapHomologicalComplex_comp (ComplexShape.up ℕ) _ _

/-- `cechDoubleNatBifunctor` with the outer index extended by zero to `ℤ`. -/
def cechDoubleOuterBifunctor :
    (SimplicialObject (FormalCoproduct.{v} (Over X)))ᵒᵖ ⥤
      CochainComplex (Cᵒᵖ ⥤ AddCommGrpCat.{v}) ℕ ⥤
        HomologicalComplex (CochainComplex AddCommGrpCat.{v} ℕ) (ComplexShape.up ℤ) :=
  cechDoubleNatBifunctor X ⋙
    (Functor.whiskeringRight (CochainComplex (Cᵒᵖ ⥤ AddCommGrpCat.{v}) ℕ) _ _).obj
      (ComplexShape.embeddingUpNat.extendFunctor (CochainComplex AddCommGrpCat.{v} ℕ))

/-- **The Čech double complex of a complex of presheaves of abelian groups**, over `ℤ × ℤ`: both
indices of `cechDoubleNatBifunctor` extended by zero. -/
def cechDoubleBifunctor :
    (SimplicialObject (FormalCoproduct.{v} (Over X)))ᵒᵖ ⥤
      CochainComplex (Cᵒᵖ ⥤ AddCommGrpCat.{v}) ℕ ⥤
        HomologicalComplex₂ AddCommGrpCat.{v} (ComplexShape.up ℤ) (ComplexShape.up ℤ) :=
  cechDoubleOuterBifunctor X ⋙
    (Functor.whiskeringRight (CochainComplex (Cᵒᵖ ⥤ AddCommGrpCat.{v}) ℕ) _ _).obj
      ((ComplexShape.embeddingUpNat.extendFunctor AddCommGrpCat.{v}).mapHomologicalComplex
        (ComplexShape.up ℤ))

/-- **The index convention of `cechDoubleBifunctor`**: in bidegree `((i : ℤ), (j : ℤ))` with
`i j : ℕ` it is the `j`-th term of the Čech complex of the `i`-th term of the complex. -/
def cechDoubleBifunctorXIso (K : (SimplicialObject (FormalCoproduct.{v} (Over X)))ᵒᵖ)
    (Y : CochainComplex (Cᵒᵖ ⥤ AddCommGrpCat.{v}) ℕ) (i j : ℕ) (i' j' : ℤ)
    (hi : (i : ℤ) = i') (hj : (j : ℤ) = j') :
    ((((cechDoubleBifunctor X).obj K).obj Y).X i').X j' ≅
      (((cechComplexOverBifunctor.{v} X).obj K).obj (Y.X i)).X j :=
  HomologicalComplex.extendXIso ((((cechDoubleOuterBifunctor X).obj K).obj Y).X i')
      ComplexShape.embeddingUpNat hj ≪≫
    (HomologicalComplex.eval AddCommGrpCat.{v} (ComplexShape.up ℕ) j).mapIso
      (HomologicalComplex.extendXIso (((cechDoubleNatBifunctor X).obj K).obj Y)
        ComplexShape.embeddingUpNat hi)

/-- The Čech double complex of a complex of **sheaves** of abelian groups: `cechDoubleBifunctor`
applied to the underlying complex of presheaves. -/
def cechDoubleSheafBifunctor :
    (SimplicialObject (FormalCoproduct.{v} (Over X)))ᵒᵖ ⥤
      CochainComplex (Sheaf J AddCommGrpCat.{v}) ℕ ⥤
        HomologicalComplex₂ AddCommGrpCat.{v} (ComplexShape.up ℤ) (ComplexShape.up ℤ) :=
  cechDoubleBifunctor X ⋙
    (Functor.whiskeringLeft (CochainComplex (Sheaf J AddCommGrpCat.{v}) ℕ) _ _).obj
      ((sheafToPresheaf J AddCommGrpCat.{v}).mapHomologicalComplex (ComplexShape.up ℕ))

/-- `cechDoubleSheafBifunctor` as a functor of the pair, so that its functoriality in the
simplicial semi-representable object and in the complex of sheaves are a single statement. -/
def cechDoubleSheaf₂ :
    (SimplicialObject (FormalCoproduct.{v} (Over X)))ᵒᵖ ×
        CochainComplex (Sheaf J AddCommGrpCat.{v}) ℕ ⥤
      HomologicalComplex₂ AddCommGrpCat.{v} (ComplexShape.up ℤ) (ComplexShape.up ℤ) :=
  Functor.uncurry.obj (cechDoubleSheafBifunctor X J)

/-- A homotopy between morphisms of complexes of sheaves induces a homotopy between the induced
morphisms of Čech double complexes, with the simplicial semi-representable object varying as
well: each of the four functors making up `cechDoubleSheafBifunctor` is additive, extension by
zero carries homotopies to homotopies, and the map in the `K` direction is composed on the left,
which a homotopy survives. -/
def cechDoubleSheaf₂Homotopy
    {P Q : (SimplicialObject (FormalCoproduct.{v} (Over X)))ᵒᵖ ×
      CochainComplex (Sheaf J AddCommGrpCat.{v}) ℕ}
    (f : P.1 ⟶ Q.1) {φ ψ : P.2 ⟶ Q.2} (H : Homotopy φ ψ) :
    Homotopy ((cechDoubleSheaf₂ X J).map (f, φ)) ((cechDoubleSheaf₂ X J).map (f, ψ)) :=
  Homotopy.compLeft
    ((ComplexShape.embeddingUpNat.extendFunctor AddCommGrpCat.{v}).mapHomotopy
      ((((cechComplexOverBifunctor.{v} X).obj Q.1).mapHomotopy
        ((sheafToPresheaf J AddCommGrpCat.{v}).mapHomotopy H)).extend
          ComplexShape.embeddingUpNat)) _

/-- **The Čech double complex of a simplicial semi-representable object and a sheaf**:
`A^{i,j}(K, F) = Č^j(K, I^i(F))` for the chosen injective resolution `I^•(F)` of `F`, with the
resolution degree outer. -/
def hypercoverDouble
    (KF : (SimplicialObject (FormalCoproduct.{v} (Over X)))ᵒᵖ × Sheaf J AddCommGrpCat.{v}) :
    HomologicalComplex₂ AddCommGrpCat.{v} (ComplexShape.up ℤ) (ComplexShape.up ℤ) :=
  (cechDoubleSheaf₂ X J).obj (KF.1, (injectiveResolution KF.2).cocomplex)

/-- The morphism of Čech double complexes attached to a morphism of pairs: the Čech pullback
along the morphism of simplicial semi-representable objects, applied to the double complex of a
chosen descent of the morphism of sheaves to the chosen injective resolutions. This is
functorial only up to homotopy, which is all
`HomologicalComplex₂.e₂FunctorOfHomotopyClasses` needs. -/
def hypercoverDoubleMap
    {KF LG : (SimplicialObject (FormalCoproduct.{v} (Over X)))ᵒᵖ × Sheaf J AddCommGrpCat.{v}}
    (fg : KF ⟶ LG) : hypercoverDouble X J KF ⟶ hypercoverDouble X J LG :=
  (cechDoubleSheaf₂ X J).map
    (fg.1, InjectiveResolution.desc fg.2 (injectiveResolution LG.2) (injectiveResolution KF.2))

/-- A homotopy `φ ≃ ψ` yields a filtered homotopy from the map induced by `(f, φ)` to any map
equal to the one induced by `(f, ψ)`. -/
private lemma filteredHomotopy₂_cechDoubleSheaf₂_map
    {P Q : (SimplicialObject (FormalCoproduct.{v} (Over X)))ᵒᵖ ×
      CochainComplex (Sheaf J AddCommGrpCat.{v}) ℕ}
    (f : P.1 ⟶ Q.1) {φ ψ : P.2 ⟶ Q.2} (H : Homotopy φ ψ)
    {g : (cechDoubleSheaf₂ X J).obj P ⟶ (cechDoubleSheaf₂ X J).obj Q}
    (h : (cechDoubleSheaf₂ X J).map (f, ψ) = g) :
    HomologicalComplex₂.FilteredHomotopy₂ ((cechDoubleSheaf₂ X J).map (f, φ)) g :=
  HomologicalComplex₂.filteredHomotopy₂_of_homotopy
    ((cechDoubleSheaf₂Homotopy X J f H).trans (Homotopy.ofEq h))

/-- `hypercoverDoubleMap` sends an identity to a filtered homotopy class of the identity. -/
lemma filteredHomotopy₂_hypercoverDoubleMap_id
    (KF : (SimplicialObject (FormalCoproduct.{v} (Over X)))ᵒᵖ × Sheaf J AddCommGrpCat.{v}) :
    HomologicalComplex₂.FilteredHomotopy₂ (hypercoverDoubleMap X J (𝟙 KF)) (𝟙 _) :=
  filteredHomotopy₂_cechDoubleSheaf₂_map X J (P := (KF.1, (injectiveResolution KF.2).cocomplex))
    (Q := (KF.1, (injectiveResolution KF.2).cocomplex)) (𝟙 KF.1)
    (InjectiveResolution.descIdHomotopy KF.2 (injectiveResolution KF.2))
    ((cechDoubleSheaf₂ X J).map_id _)

/-- `hypercoverDoubleMap` is multiplicative up to filtered homotopy. -/
lemma filteredHomotopy₂_hypercoverDoubleMap_comp
    {KF LG MH : (SimplicialObject (FormalCoproduct.{v} (Over X)))ᵒᵖ × Sheaf J AddCommGrpCat.{v}}
    (fg : KF ⟶ LG) (f'g' : LG ⟶ MH) :
    HomologicalComplex₂.FilteredHomotopy₂ (hypercoverDoubleMap X J (fg ≫ f'g'))
      (hypercoverDoubleMap X J fg ≫ hypercoverDoubleMap X J f'g') :=
  filteredHomotopy₂_cechDoubleSheaf₂_map X J (P := (KF.1, (injectiveResolution KF.2).cocomplex))
    (Q := (MH.1, (injectiveResolution MH.2).cocomplex)) (fg.1 ≫ f'g'.1)
    (InjectiveResolution.descCompHomotopy fg.2 f'g'.2 (injectiveResolution KF.2)
      (injectiveResolution LG.2) (injectiveResolution MH.2))
    ((cechDoubleSheaf₂ X J).map_comp
      (X := (KF.1, (injectiveResolution KF.2).cocomplex))
      (Y := (LG.1, (injectiveResolution LG.2).cocomplex))
      (Z := (MH.1, (injectiveResolution MH.2).cocomplex))
      (fg.1, InjectiveResolution.desc fg.2 (injectiveResolution LG.2) (injectiveResolution KF.2))
      (f'g'.1, InjectiveResolution.desc f'g'.2 (injectiveResolution MH.2)
        (injectiveResolution LG.2)))

/-- **First-quadrant vanishing for a double complex extended by zero from `ℕ × ℕ`.** Both
indices are extended by zero, so `H^p_{II}(H^q_I(-))` vanishes as soon as `p < 0` or `q < 0`: in
the first case the complex `H^q_I(-)` is zero in degree `p`, in the second the outer complex is
exact at `q`. -/
lemma isZero_homologyIIHomologyI_extend
    (A : HomologicalComplex (CochainComplex AddCommGrpCat.{v} ℕ) (ComplexShape.up ℕ))
    (p q : ℤ) (h : p < 0 ∨ q < 0) :
    IsZero ((HomologicalComplex₂.homologyIIHomologyIFunctor AddCommGrpCat.{v} p q).obj
      (((ComplexShape.embeddingUpNat.extendFunctor AddCommGrpCat.{v}).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj
        ((ComplexShape.embeddingUpNat.extendFunctor
          (CochainComplex AddCommGrpCat.{v} ℕ)).obj A))) := by
  refine (Iso.isZero_iff ((HomologicalComplex.homologyFunctor
      AddCommGrpCat.{v} (ComplexShape.up ℤ) p).mapIso
    ((Functor.mapHomologicalComplexHomologyIso
      (ComplexShape.embeddingUpNat.extendFunctor AddCommGrpCat.{v}) (ComplexShape.up ℤ) q).app
      ((ComplexShape.embeddingUpNat.extendFunctor
        (CochainComplex AddCommGrpCat.{v} ℕ)).obj A)))).2 ?_
  rcases h with hp | hq
  · refine (HomologicalComplex.exactAt_iff_isZero_homology
      ((((ComplexShape.embeddingUpNat.extendFunctor
        (CochainComplex AddCommGrpCat.{v} ℕ)).obj A).homology q).extend
          ComplexShape.embeddingUpNat) p).1 (ShortComplex.exact_of_isZero_X₂ _ ?_)
    exact HomologicalComplex.isZero_extend_X _ ComplexShape.embeddingUpNat p
      fun i => by change ((i : ℕ) : ℤ) ≠ p; omega
  · refine Functor.map_isZero (HomologicalComplex.homologyFunctor
      AddCommGrpCat.{v} (ComplexShape.up ℤ) p)
      (Functor.map_isZero (ComplexShape.embeddingUpNat.extendFunctor AddCommGrpCat.{v}) ?_)
    refine (HomologicalComplex.exactAt_iff_isZero_homology
      ((ComplexShape.embeddingUpNat.extendFunctor
        (CochainComplex AddCommGrpCat.{v} ℕ)).obj A) q).1 ?_
    exact HomologicalComplex.extend_exactAt A ComplexShape.embeddingUpNat q
      fun j => by change ((j : ℕ) : ℤ) ≠ q; omega

/-- **The hypercovering spectral sequence on `ℤ × ℤ`**, functorial in the simplicial
semi-representable object and in the sheaf: the second spectral sequence of the Čech double
complex of an injective resolution, presented from its second page. The presentation is from the
second page because homotopy invariance of the induced maps fails on the zeroth one, and an
injective resolution is functorial only up to homotopy. -/
def hypercoverE₂Functor :
    (SimplicialObject (FormalCoproduct.{v} (Over X)))ᵒᵖ × Sheaf J AddCommGrpCat.{v} ⥤
      E₂CohomologicalSpectralSequence AddCommGrpCat.{v} :=
  HomologicalComplex₂.e₂FunctorOfHomotopyClasses (hypercoverDouble X J)
    (hypercoverDoubleMap X J) (filteredHomotopy₂_hypercoverDoubleMap_id X J)
    (fun fg f'g' => filteredHomotopy₂_hypercoverDoubleMap_comp X J fg f'g')

/-- The hypercovering spectral sequence is first quadrant from its second page on. -/
lemma isFirstQuadrant_hypercoverE₂Functor
    (KF : (SimplicialObject (FormalCoproduct.{v} (Over X)))ᵒᵖ × Sheaf J AddCommGrpCat.{v}) :
    CategoryTheory.SpectralSequence.IsFirstQuadrant (u := fun r => (r, 1 - r))
      ((hypercoverE₂Functor X J).obj KF) :=
  HomologicalComplex₂.isFirstQuadrant_e₂SpectralSequence₂Functor _
    (hypercoverDouble X J KF) fun p q h =>
      isZero_homologyIIHomologyI_extend
        (((cechDoubleNatBifunctor X).obj KF.1).obj
          (((sheafToPresheaf J AddCommGrpCat.{v}).mapHomologicalComplex
            (ComplexShape.up ℕ)).obj (injectiveResolution KF.2).cocomplex)) p q h

/-- **The `sequence` of clause (3) of [Stacks, Tag 01GY] for an arbitrary simplicial
semi-representable object**: the functorial first-quadrant `E₂` cohomological spectral sequence
attached to a simplicial semi-representable object over `X` and a sheaf of abelian groups,
carried on `ℕ × ℕ`. -/
def hypercoverSpectralSequenceFunctor :
    (SimplicialObject (FormalCoproduct.{v} (Over X)))ᵒᵖ × Sheaf J AddCommGrpCat.{v} ⥤
      E₂CohomologicalSpectralSequenceNat AddCommGrpCat.{v} :=
  CategoryTheory.SpectralSequence.natRestrictE₂Comp (hypercoverE₂Functor X J)
    (isFirstQuadrant_hypercoverE₂Functor X J)

end SmallSite

section Hypercoverings

variable {C : Type v} [SmallCategory C] [HasPullbacks C] (X : C) (J : Pretopology C)

/-- **The category of hypercoverings of `X`** for the pretopology `J`: the full subcategory of
simplicial semi-representable objects over `X` cut out by
`Stacks.CategoryTheory.Hypercovering.IsHypercovering` ([Stacks, Tag 01G5]). -/
abbrev HypercoveringCat :=
  ObjectProperty.FullSubcategory
    (fun K : SimplicialObject (FormalCoproduct.{v} (Over X)) => IsHypercovering J K)

/-- **The `sequence` of clause (3) of [Stacks, Tag 01GY]**: the first-quadrant `E₂` cohomological
spectral sequence of a hypercovering of `X` and a sheaf of abelian groups, functorial in the
hypercovering (contravariantly) and in the sheaf. It is the restriction of
`hypercoverSpectralSequenceFunctor` along the inclusion of the full subcategory of
hypercoverings, since nothing in the construction of the sequence itself uses the hypercovering
condition -- that is needed only for the abutment, which is not here. -/
@[sga "4 V 7.4.0" "(7.4.0.3)"]
def hypercoveringSpectralSequence :
    (HypercoveringCat X J)ᵒᵖ × Sheaf J.toGrothendieck AddCommGrpCat.{v} ⥤
      E₂CohomologicalSpectralSequenceNat AddCommGrpCat.{v} :=
  (ObjectProperty.ι _).op.prod (𝟭 (Sheaf J.toGrothendieck AddCommGrpCat.{v})) ⋙
    hypercoverSpectralSequenceFunctor X J.toGrothendieck

end Hypercoverings

end Stacks.CategoryTheory.Hypercovering.Functorial

end
