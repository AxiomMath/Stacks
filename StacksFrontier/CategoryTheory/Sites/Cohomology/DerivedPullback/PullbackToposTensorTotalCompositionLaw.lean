module

public import
  StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.PullbackComparisonQCompositionLaw
public import
  StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.PullbackToposTensorCompositionLaw
public import
  StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.PullbackToposUnitorCoherence
public import
  StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.PullbackTensorIsoCompositionLaw
public import
  StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.PullbackToposTensorBraiding
public import
  StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.TotalTensorComplexAlongAComposite

/-!
# The comparison of total tensor complexes along a composite of site-presented morphisms

Let `f : (Sh(C), 𝒪_C) ⟶ (Sh(D), 𝒪_D)` and `g : (Sh(D), 𝒪_D) ⟶ (Sh(E), 𝒪_E)` be morphisms of
ringed topoi presented by functors of the underlying sites which are morphisms of sites, so that
`g ∘ f` is one too (**Stacks 03CC**).  For cochain complexes `P`, `N` of `𝒪_E`-modules,
`Stacks.Sheaves.DerivedPullback.pullbackToposTensorTotalIso` is the comparison

`f^*Tot(P ⊗_{𝒪_E} N) ≅ Tot(f^*P ⊗_{𝒪_C} f^*N)`

of **Stacks 03EL** at the level of total tensor complexes.  This file proves that it is
compatible with composition: the composition isomorphism `g^* ⋙ f^* ≅ (g ∘ f)^*` of
**Stacks 0D6D**, read degreewise on complexes, carries the comparison for `g ∘ f` to the
comparison for `g`, then the comparison for `f`, then the composition isomorphism in each tensor
factor.

## Main definitions

* `Stacks.Sheaves.DerivedPullback.pullbackToposTensorIsoApp`: the module-level comparison
  `f^*(A ⊗_{𝒪_D} B) ≅ f^*A ⊗_{𝒪_C} f^*B` of Stacks 03EL for the site-presented pullback, read as
  an isomorphism.  Its `hom` is `Stacks.Sheaves.DerivedPullback.pullbackToposTensorMap`, by
  `pullbackToposTensorIsoApp_hom`.

## Main results

* `Stacks.Sheaves.DerivedPullback.pullbackToposTensorTotalIso_comp`: **the complex-level
  composition law of Stacks 03EL for the site-presented pullback**, for arbitrary cochain
  complexes `P`, `N` of `𝒪_E`-modules — no K-flatness, no boundedness, no flatness of terms.
* `Stacks.Sheaves.DerivedPullback.map_pullbackToposTensorTotalIso_comp`: the same identity
  carried along `CategoryTheory.DerivedCategory.Q`, with the comparison written through
  `Stacks.Sheaves.DerivedPullback.pullbackTensorComplexIso`.  This is the shape the Stacks 07A4
  composition law consumes as its `htotal` input.

## Implementation notes

*Where the chase is.*  Nowhere here.  The identity is checked on the summands of the total
complex, and that reduction is already available, stated for arbitrary preadditive categories,
bifunctors and additive functors, as
`Stacks.TotalTensorComplexComposite.totalComplexComparison_comp`.  That lemma was written for the
ringed-space development, but its statement mentions no geometry at all, so it is instantiated
here rather than redone.  Its three summandwise descriptions are
`Stacks.Sheaves.DerivedPullback.ι_pullbackToposTensorTotalIso_hom` at `g`, at `f` — applied to
the degreewise pullbacks `g^*P`, `g^*N` — and at `g ∘ f`; its degreewise description of the
composition isomorphism on complexes is
`Stacks.Sheaves.DerivedPullback.CompositionLaw.pullbackComplexCompIso_hom_app_f`; and its
degreewise hypothesis is the module-level composition law of Stacks 03EL,
`pullbackToposTensorMap_comp` of `PullbackToposTensorCompositionLaw.lean` in this directory.  **No
hypothesis is carried**: every input is discharged from the tree, so the two main results below
assume nothing beyond `hmosf`, `hmosg` and the ambient instances.  No boundedness hypothesis
appears because the summandwise reduction needs none: pullback of sheaves of modules is a left
adjoint, so it preserves the coproduct decomposition of each total degree.

*Why the reduction is restated before it is used.*  `totalComplexComparison_comp` asks for its
comparisons of total complexes, and for their summandwise descriptions, at the one pair of
complexes its conclusion is about.  Two of those pairs are the degreewise pullbacks `g^*P`,
`g^*N`, whereas the lemmas of this directory that supply them are stated for *variable*
complexes.  Filling a slot directly therefore means checking a statement about variable complexes
against the same statement about `g^*P` and `g^*N`, and that is a check the *kernel* cannot
complete inside its step budget: the pulled-back complexes are spelled through
`CategoryTheory.Functor.mapHomologicalComplex`, and the check descends through the surrounding
sheaf tensor product carrying them.  It is over budget even in a declaration that does
nothing else, in both spellings of the bidegree and with the two readings handed to each other
directly.

`totalComplexComparison_comp_family` is that lemma with every complex-level input asked for as a
*family*, at all pairs of complexes at once.  Its slots are then filled by this directory's
lemmas **uninstantiated**, so every check is between two statements about variable complexes, and
the instantiation at `g^*P`, `g^*N` happens inside it, where the bifunctors are variables and
there is nothing to descend into.  `ι_respell_degreewise` is the one further step this needs: the
reduction's middle hypothesis wants the module-level comparison at `g^*(P^p)` while the lemma
supplying it has `(g^*P)^p`, and those two readings — definitionally equal, three projections of
a structure literal apart — are identified there, again with the bifunctors still variables.
Both restatements are geometry-free and neither assumes anything new.

*Why the module-level comparison is repackaged as an isomorphism.*  The summandwise reduction
needs the inverses of the three degreewise comparisons in order to cancel them, so it asks for
isomorphisms, whereas `Stacks.Sheaves.DerivedPullback.pullbackToposTensorMap` is a morphism.
`pullbackToposTensorIsoApp` is that morphism read through `CategoryTheory.asIso`, using
`isIso_pullbackToposTensorMap`; `pullbackToposTensorIsoApp_hom` is `rfl`, and no new mathematics
enters.  Writing the isomorphism out instead as the four-factor composite of its factors'
isomorphisms is definitionally the same and is measurably worse: `ι_pullbackToposTensorIsoApp`
below then exceeds the *kernel's* step limit, because deciding the seam between the two spellings
of a bidegree already means unfolding the sheaf tensor product and the four-factor composite has
to be unfolded on top of it.  Through `asIso` the `hom` is one projection away.

*Why `ι_pullbackToposTensorIsoApp` exists.*  It is
`Stacks.Sheaves.DerivedPullback.ι_pullbackToposTensorTotalIso_hom` with the degreewise comparison
respelled from `Stacks.Sheaves.DerivedPullback.pullbackToposTensorMapDeg` to the `hom` of
`pullbackToposTensorIsoApp`.  The two are definitionally equal, and doing the conversion once in
a small declaration keeps it out of the instantiation below, where it would be decided against a
slot that is only half solved when it is reached.

*The morphism-of-sites hypotheses.*  `AlgebraicGeometry.RingedToposSiteHom` asks only that the
underlying functor be continuous; exactness of the inverse image is not a field of it.  `hmosf`
and `hmosg` supply that exactness, and are what the passage to the four-field presentation of
Stacks 03D6 consumes.  The composite needs no third assumption: it is
`AlgebraicGeometry.RingedToposSiteHom.isMorphismOfSites_comp_u`, which is Stacks 03CC.

## References

* [Stacks Project, Tag 03EL](https://stacks.math.columbia.edu/tag/03EL)
* [Stacks Project, Tag 0D6D](https://stacks.math.columbia.edu/tag/0D6D)
* [Stacks Project, Tag 03CC](https://stacks.math.columbia.edu/tag/03CC)
* [Stacks Project, Tag 03D6](https://stacks.math.columbia.edu/tag/03D6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Sheaves.RingedToposModules
open Stacks.Sheaves.DerivedPullback.KFlatPullback
open Stacks.Sheaves.DerivedPullback.CompositionLaw

namespace Stacks.Sheaves.DerivedPullback

universe u

/-! ## The module-level comparison of Stacks 03EL as an isomorphism -/

section ModuleLevel

variable {X Y : RingedTopos.{u, u, u}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify Y.J AddCommGrpCat.{u}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj M).Additive]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O).obj M).Additive]
  [∀ (A B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ),
    HomologicalComplex.HasMapBifunctor A B
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O) (ComplexShape.up ℤ)]
  [∀ (A B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ),
    HomologicalComplex.HasMapBifunctor A B
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O) (ComplexShape.up ℤ)]
  (f : RingedToposSiteHom X Y)

attribute [instance] isIso_pullbackToposTensorMap

/-- **The module-level comparison `f^*(A ⊗_{𝒪_D} B) ≅ f^*A ⊗_{𝒪_C} f^*B` of Stacks 03EL for the
site-presented pullback, read as an isomorphism.**

It is `Stacks.Sheaves.DerivedPullback.pullbackToposTensorMap` together with
`isIso_pullbackToposTensorMap`, and nothing else: `pullbackToposTensorIsoApp_hom` is `rfl`.  The
repackaging is what the summandwise reduction of the composition law needs, since it cancels the
three comparisons and so asks for their inverses.

*Why `CategoryTheory.asIso` and not the four-factor composite of isomorphisms.*  The two are
definitionally equal, but a statement composing the latter's `hom` with a summand inclusion of a
total complex — whose source is spelled with the degrees of the pullback complexes rather than
with the pullbacks of the degrees — is one the *kernel* cannot check inside its step limit:
deciding the equality of the two spellings of that seam means unfolding the sheaf tensor product,
and it then has the four-factor composite to unfold on top of it.  Through `asIso` the `hom` is
reached by a single projection, and the seam is the only thing left to decide. -/
def pullbackToposTensorIsoApp (hmos : f.u.IsMorphismOfSites Y.J X.J)
    (A B : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) :
    f.pullbackTopos.obj
        (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O).obj A).obj B) ≅
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj
          (f.pullbackTopos.obj A)).obj (f.pullbackTopos.obj B) :=
  asIso (pullbackToposTensorMap f hmos A B)

omit [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj M).Additive]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O).obj M).Additive]
  [∀ (A B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ),
    HomologicalComplex.HasMapBifunctor A B
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O) (ComplexShape.up ℤ)]
  [∀ (A B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ),
    HomologicalComplex.HasMapBifunctor A B
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O) (ComplexShape.up ℤ)] in
/-- The isomorphism `pullbackToposTensorIsoApp` has
`Stacks.Sheaves.DerivedPullback.pullbackToposTensorMap` as its underlying morphism. -/
lemma pullbackToposTensorIsoApp_hom (hmos : f.u.IsMorphismOfSites Y.J X.J)
    (A B : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) :
    (pullbackToposTensorIsoApp f hmos A B).hom = pullbackToposTensorMap f hmos A B :=
  rfl

/-- **The comparison of total tensor complexes acts on the summand of bidegree `(p, q)` by the
module-level comparison**, with the latter written as the `hom` of `pullbackToposTensorIsoApp`.

This is `Stacks.Sheaves.DerivedPullback.ι_pullbackToposTensorTotalIso_hom`, whose right-hand side
spells the module-level comparison as
`Stacks.Sheaves.DerivedPullback.pullbackToposTensorMapDeg`.  The two spellings are definitionally
equal; recording the respelling once here keeps the conversion out of the instantiation of the
summandwise reduction below. -/
lemma ι_pullbackToposTensorIsoApp (hmos : f.u.IsMorphismOfSites Y.J X.J)
    (K L : CochainComplex
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ)
    (p q n : ℤ) (hpq : p + q = n) :
    f.pullbackTopos.map (HomologicalComplex.ιMapBifunctor K L
          (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O)
          (ComplexShape.up ℤ) p q n hpq) ≫
        (pullbackToposTensorTotalIso f hmos K L).hom.f n =
      (pullbackToposTensorIsoApp f hmos (K.X p) (L.X q)).hom ≫
        HomologicalComplex.ιMapBifunctor ((pullbackComplex f).obj K) ((pullbackComplex f).obj L)
          (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O)
          (ComplexShape.up ℤ) p q n hpq :=
  ι_pullbackToposTensorTotalIso_hom f hmos K L p q n hpq

/-- `Stacks.Sheaves.DerivedPullback.pullbackToposTensorTotalIso` with the degreewise pullback
functor written as `CategoryTheory.Functor.mapHomologicalComplex` of the module-level pullback.

*Why this respelling is a declaration of its own.*  The summandwise reduction
`Stacks.TotalTensorComplexComposite.totalComplexComparison_comp` states its hypotheses at this
spelling, and this directory states its lemmas at the other.  The two are definitionally equal,
but the equality has to be decided inside statements about total tensor complexes, and deciding
it there means unfolding the sheaf tensor product at every object of them: done for each
hypothesis of the reduction separately it exhausts the *kernel's* step limit, as does doing it
once for the reduction's whole conclusion.  Decided here, for *variable* complexes `K` and `L`,
it is paid once and is cheap, and every instantiation of it below is a substitution. -/
private def pullbackToposTensorTotalIso' (hmos : f.u.IsMorphismOfSites Y.J X.J)
    (K L : CochainComplex
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ) :
    (f.pullbackTopos.mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (HomologicalComplex.mapBifunctor K L
          (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O) (ComplexShape.up ℤ)) ≅
      HomologicalComplex.mapBifunctor
        ((f.pullbackTopos.mapHomologicalComplex (ComplexShape.up ℤ)).obj K)
        ((f.pullbackTopos.mapHomologicalComplex (ComplexShape.up ℤ)).obj L)
        (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O) (ComplexShape.up ℤ) :=
  pullbackToposTensorTotalIso f hmos K L

/-- `ι_pullbackToposTensorIsoApp` with the degreewise pullback functor written as
`CategoryTheory.Functor.mapHomologicalComplex` of the module-level pullback, and with the
bidegree condition written as the total-complex-shape condition.

*Why the restatement is a second declaration.*  Both this respelling and the respelling of the
module-level comparison in `ι_pullbackToposTensorIsoApp` are decided by the *kernel*, each
affordably; performed in one declaration they together exceed its step limit.  Splitting them
gives each its own budget, and this is the spelling the summandwise reduction's hypothesis is
stated at, so no conversion is left for the instantiation below. -/
private lemma ι_pullbackToposTensorIsoApp' (hmos : f.u.IsMorphismOfSites Y.J X.J)
    (K L : CochainComplex
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ)
    (p q n : ℤ) (hpq : ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ)
      (ComplexShape.up ℤ) (p, q) = n) :
    f.pullbackTopos.map (HomologicalComplex.ιMapBifunctor K L
          (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O)
          (ComplexShape.up ℤ) p q n hpq) ≫
        (pullbackToposTensorTotalIso' f hmos K L).hom.f n =
      (pullbackToposTensorIsoApp f hmos (K.X p) (L.X q)).hom ≫
        HomologicalComplex.ιMapBifunctor
          ((f.pullbackTopos.mapHomologicalComplex (ComplexShape.up ℤ)).obj K)
          ((f.pullbackTopos.mapHomologicalComplex (ComplexShape.up ℤ)).obj L)
          (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O)
          (ComplexShape.up ℤ) p q n hpq :=
  ι_pullbackToposTensorIsoApp f hmos K L p q n hpq

end ModuleLevel

/-! ## Reading a bidegree of a degreewise pullback as a pullback of a bidegree -/

section Respelling

variable {A₁ A₂ A₃ : Type*} [Category A₁] [Category A₂] [Category A₃]
  [Preadditive A₁] [Preadditive A₂] [Preadditive A₃]

/-- **The summandwise description of a comparison of total complexes, with the degreewise
comparison read at `Pg (K^p)` instead of `(Pg K)^p`.**  The two readings of the bidegree
`(p, q)` are definitionally equal, and this is the only place in the file where that equality is
decided.

*Why it is decided here, with the bifunctors and the functors as variables.*  The equality to be
decided is `((Pg.mapHomologicalComplex c).obj K).X p = Pg.obj (K.X p)`, which is three
projections of a structure literal.  What makes it expensive is not the equality but its
surroundings: the two readings occur under `F₃.obj`, and when `F₃` is the sheaf tensor product
the definitional check reaches it with two arguments that are not yet syntactically equal and
unfolds it — once per object of the two total complexes involved.  With `F₂`, `F₃`, `Pg` and `Pf`
free variables there is nothing to unfold, so the check is congruence down to the three
projections, and every instantiation of this lemma is a substitution.

This is what the middle hypothesis of
`Stacks.TotalTensorComplexComposite.totalComplexComparison_comp` asks for, and its hypothesis
here is what `ι_pullbackToposTensorIsoApp'` supplies at the degreewise pullbacks along `g`. -/
lemma ι_respell_degreewise (F₂ : A₂ ⥤ A₂ ⥤ A₂) (F₃ : A₃ ⥤ A₃ ⥤ A₃)
    [F₂.PreservesZeroMorphisms] [∀ a, (F₂.obj a).PreservesZeroMorphisms]
    [F₃.PreservesZeroMorphisms] [∀ a, (F₃.obj a).PreservesZeroMorphisms]
    (Pg : A₁ ⥤ A₂) (Pf : A₂ ⥤ A₃) [Pg.Additive] [Pf.Additive]
    (εf : ∀ a b : A₂, Pf.obj ((F₂.obj a).obj b) ≅ (F₃.obj (Pf.obj a)).obj (Pf.obj b))
    (K L : CochainComplex A₁ ℤ)
    [HomologicalComplex.HasMapBifunctor
      ((Pg.mapHomologicalComplex (ComplexShape.up ℤ)).obj K)
      ((Pg.mapHomologicalComplex (ComplexShape.up ℤ)).obj L) F₂ (ComplexShape.up ℤ)]
    [HomologicalComplex.HasMapBifunctor
      ((Pf.mapHomologicalComplex (ComplexShape.up ℤ)).obj
        ((Pg.mapHomologicalComplex (ComplexShape.up ℤ)).obj K))
      ((Pf.mapHomologicalComplex (ComplexShape.up ℤ)).obj
        ((Pg.mapHomologicalComplex (ComplexShape.up ℤ)).obj L)) F₃ (ComplexShape.up ℤ)]
    (βf : (Pf.mapHomologicalComplex (ComplexShape.up ℤ)).obj
          (HomologicalComplex.mapBifunctor
            ((Pg.mapHomologicalComplex (ComplexShape.up ℤ)).obj K)
            ((Pg.mapHomologicalComplex (ComplexShape.up ℤ)).obj L) F₂ (ComplexShape.up ℤ)) ≅
        HomologicalComplex.mapBifunctor
          ((Pf.mapHomologicalComplex (ComplexShape.up ℤ)).obj
            ((Pg.mapHomologicalComplex (ComplexShape.up ℤ)).obj K))
          ((Pf.mapHomologicalComplex (ComplexShape.up ℤ)).obj
            ((Pg.mapHomologicalComplex (ComplexShape.up ℤ)).obj L)) F₃ (ComplexShape.up ℤ))
    (h : ∀ (p q n : ℤ) (hpq : ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ)
        (ComplexShape.up ℤ) (p, q) = n),
      Pf.map (HomologicalComplex.ιMapBifunctor
            ((Pg.mapHomologicalComplex (ComplexShape.up ℤ)).obj K)
            ((Pg.mapHomologicalComplex (ComplexShape.up ℤ)).obj L) F₂
            (ComplexShape.up ℤ) p q n hpq) ≫ βf.hom.f n =
        (εf (((Pg.mapHomologicalComplex (ComplexShape.up ℤ)).obj K).X p)
            (((Pg.mapHomologicalComplex (ComplexShape.up ℤ)).obj L).X q)).hom ≫
          HomologicalComplex.ιMapBifunctor
            ((Pf.mapHomologicalComplex (ComplexShape.up ℤ)).obj
              ((Pg.mapHomologicalComplex (ComplexShape.up ℤ)).obj K))
            ((Pf.mapHomologicalComplex (ComplexShape.up ℤ)).obj
              ((Pg.mapHomologicalComplex (ComplexShape.up ℤ)).obj L)) F₃
            (ComplexShape.up ℤ) p q n hpq) :
    ∀ (p q n : ℤ) (hpq : ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ)
        (ComplexShape.up ℤ) (p, q) = n),
      Pf.map (HomologicalComplex.ιMapBifunctor
            ((Pg.mapHomologicalComplex (ComplexShape.up ℤ)).obj K)
            ((Pg.mapHomologicalComplex (ComplexShape.up ℤ)).obj L) F₂
            (ComplexShape.up ℤ) p q n hpq) ≫ βf.hom.f n =
        (εf (Pg.obj (K.X p)) (Pg.obj (L.X q))).hom ≫
          HomologicalComplex.ιMapBifunctor
            ((Pf.mapHomologicalComplex (ComplexShape.up ℤ)).obj
              ((Pg.mapHomologicalComplex (ComplexShape.up ℤ)).obj K))
            ((Pf.mapHomologicalComplex (ComplexShape.up ℤ)).obj
              ((Pg.mapHomologicalComplex (ComplexShape.up ℤ)).obj L)) F₃
            (ComplexShape.up ℤ) p q n hpq :=
  h

variable (F₁ : A₁ ⥤ A₁ ⥤ A₁) (F₂ : A₂ ⥤ A₂ ⥤ A₂) (F₃ : A₃ ⥤ A₃ ⥤ A₃)
  [F₁.PreservesZeroMorphisms] [∀ a, (F₁.obj a).PreservesZeroMorphisms]
  [F₂.PreservesZeroMorphisms] [∀ a, (F₂.obj a).PreservesZeroMorphisms]
  [F₃.PreservesZeroMorphisms] [∀ a, (F₃.obj a).PreservesZeroMorphisms]
  [∀ (A B : CochainComplex A₁ ℤ),
    HomologicalComplex.HasMapBifunctor A B F₁ (ComplexShape.up ℤ)]
  [∀ (A B : CochainComplex A₂ ℤ),
    HomologicalComplex.HasMapBifunctor A B F₂ (ComplexShape.up ℤ)]
  [∀ (A B : CochainComplex A₃ ℤ),
    HomologicalComplex.HasMapBifunctor A B F₃ (ComplexShape.up ℤ)]
  (Pg : A₁ ⥤ A₂) (Pf : A₂ ⥤ A₃) (Ph : A₁ ⥤ A₃)
  [Pg.Additive] [Pf.Additive] [Ph.Additive]
  (γ : Pg ⋙ Pf ≅ Ph)
  (εg : ∀ a b : A₁, Pg.obj ((F₁.obj a).obj b) ≅ (F₂.obj (Pg.obj a)).obj (Pg.obj b))
  (εf : ∀ a b : A₂, Pf.obj ((F₂.obj a).obj b) ≅ (F₃.obj (Pf.obj a)).obj (Pf.obj b))
  (εh : ∀ a b : A₁, Ph.obj ((F₁.obj a).obj b) ≅ (F₃.obj (Ph.obj a)).obj (Ph.obj b))
  (K L : CochainComplex A₁ ℤ)

/-- **`Stacks.TotalTensorComplexComposite.totalComplexComparison_comp` with each of its
complex-level inputs asked for as a family, at every pair of complexes at once**, and with its
middle summandwise hypothesis asked for at the bidegree of a degreewise pullback rather than at
the pullback of a bidegree.

*Why the inputs are families.*  `totalComplexComparison_comp` asks for its comparisons and their
summandwise descriptions at the one pair of complexes the conclusion is about.  Two of those
pairs are the degreewise pullbacks `Pg K`, `Pg L`, and the lemmas of this directory that supply
them are stated for *variable* complexes.  Filling the slots therefore means checking a
statement about variable complexes against the same statement about `Pg K` and `Pg L` — and the
*kernel* cannot do that inside its step budget: the pulled-back complexes are spelled through
`CategoryTheory.Functor.mapHomologicalComplex`, and the check descends into the sheaf tensor
product carrying them.  Even in a declaration that does nothing else, in both directions and
with the two readings handed to each other directly, it is over budget.  Asked for as
families, the slots are filled by the directory's lemmas *uninstantiated*, so the only check is
between two statements about variable complexes, and the instantiation at `Pg K`, `Pg L` happens
here, where the bifunctors are variables and there is nothing to descend into.

The degreewise composition isomorphism is likewise one family `δ` with one description `hδ`,
rather than three morphisms and three descriptions: it is needed in each tensor factor and at
the total complex, and all three are the same lemma at different complexes.

Nothing is assumed that `totalComplexComparison_comp` does not assume, and the conclusion is
its conclusion. -/
lemma totalComplexComparison_comp_family
    (hε : ∀ a b : A₁,
      Pf.map (εg a b).hom ≫ (εf (Pg.obj a) (Pg.obj b)).hom ≫
          ((F₃.map (γ.hom.app a)).app (Pf.obj (Pg.obj b)) ≫
            (F₃.obj (Ph.obj a)).map (γ.hom.app b)) =
        γ.hom.app ((F₁.obj a).obj b) ≫ (εh a b).hom)
    (βg : ∀ Ka La : CochainComplex A₁ ℤ,
      (Pg.mapHomologicalComplex (ComplexShape.up ℤ)).obj
          (HomologicalComplex.mapBifunctor Ka La F₁ (ComplexShape.up ℤ)) ≅
        HomologicalComplex.mapBifunctor
          ((Pg.mapHomologicalComplex (ComplexShape.up ℤ)).obj Ka)
          ((Pg.mapHomologicalComplex (ComplexShape.up ℤ)).obj La) F₂ (ComplexShape.up ℤ))
    (βf : ∀ Kb Lb : CochainComplex A₂ ℤ,
      (Pf.mapHomologicalComplex (ComplexShape.up ℤ)).obj
          (HomologicalComplex.mapBifunctor Kb Lb F₂ (ComplexShape.up ℤ)) ≅
        HomologicalComplex.mapBifunctor
          ((Pf.mapHomologicalComplex (ComplexShape.up ℤ)).obj Kb)
          ((Pf.mapHomologicalComplex (ComplexShape.up ℤ)).obj Lb) F₃ (ComplexShape.up ℤ))
    (βh : ∀ Ka La : CochainComplex A₁ ℤ,
      (Ph.mapHomologicalComplex (ComplexShape.up ℤ)).obj
          (HomologicalComplex.mapBifunctor Ka La F₁ (ComplexShape.up ℤ)) ≅
        HomologicalComplex.mapBifunctor
          ((Ph.mapHomologicalComplex (ComplexShape.up ℤ)).obj Ka)
          ((Ph.mapHomologicalComplex (ComplexShape.up ℤ)).obj La) F₃ (ComplexShape.up ℤ))
    (hg : ∀ (Ka La : CochainComplex A₁ ℤ) (p q n : ℤ)
        (h : ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ)
          (ComplexShape.up ℤ) (p, q) = n),
      Pg.map (HomologicalComplex.ιMapBifunctor Ka La F₁ (ComplexShape.up ℤ) p q n h) ≫
          (βg Ka La).hom.f n =
        (εg (Ka.X p) (La.X q)).hom ≫
          HomologicalComplex.ιMapBifunctor
            ((Pg.mapHomologicalComplex (ComplexShape.up ℤ)).obj Ka)
            ((Pg.mapHomologicalComplex (ComplexShape.up ℤ)).obj La) F₂
            (ComplexShape.up ℤ) p q n h)
    (hf : ∀ (Kb Lb : CochainComplex A₂ ℤ) (p q n : ℤ)
        (h : ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ)
          (ComplexShape.up ℤ) (p, q) = n),
      Pf.map (HomologicalComplex.ιMapBifunctor Kb Lb F₂ (ComplexShape.up ℤ) p q n h) ≫
          (βf Kb Lb).hom.f n =
        (εf (Kb.X p) (Lb.X q)).hom ≫
          HomologicalComplex.ιMapBifunctor
            ((Pf.mapHomologicalComplex (ComplexShape.up ℤ)).obj Kb)
            ((Pf.mapHomologicalComplex (ComplexShape.up ℤ)).obj Lb) F₃
            (ComplexShape.up ℤ) p q n h)
    (hh : ∀ (Ka La : CochainComplex A₁ ℤ) (p q n : ℤ)
        (h : ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ)
          (ComplexShape.up ℤ) (p, q) = n),
      Ph.map (HomologicalComplex.ιMapBifunctor Ka La F₁ (ComplexShape.up ℤ) p q n h) ≫
          (βh Ka La).hom.f n =
        (εh (Ka.X p) (La.X q)).hom ≫
          HomologicalComplex.ιMapBifunctor
            ((Ph.mapHomologicalComplex (ComplexShape.up ℤ)).obj Ka)
            ((Ph.mapHomologicalComplex (ComplexShape.up ℤ)).obj La) F₃
            (ComplexShape.up ℤ) p q n h)
    (δ : ∀ M : CochainComplex A₁ ℤ,
      (Pf.mapHomologicalComplex (ComplexShape.up ℤ)).obj
          ((Pg.mapHomologicalComplex (ComplexShape.up ℤ)).obj M) ⟶
        (Ph.mapHomologicalComplex (ComplexShape.up ℤ)).obj M)
    (hδ : ∀ (M : CochainComplex A₁ ℤ) (n : ℤ), (δ M).f n = γ.hom.app (M.X n)) :
    (Pf.mapHomologicalComplex (ComplexShape.up ℤ)).map (βg K L).hom ≫
        (βf ((Pg.mapHomologicalComplex (ComplexShape.up ℤ)).obj K)
          ((Pg.mapHomologicalComplex (ComplexShape.up ℤ)).obj L)).hom ≫
          HomologicalComplex.mapBifunctorMap (δ K) (δ L) F₃ (ComplexShape.up ℤ) =
      δ (HomologicalComplex.mapBifunctor K L F₁ (ComplexShape.up ℤ)) ≫ (βh K L).hom :=
  Stacks.TotalTensorComplexComposite.totalComplexComparison_comp F₁ F₂ F₃ Pg Pf Ph γ εg εf εh
    K L hε (βg K L)
    (βf ((Pg.mapHomologicalComplex (ComplexShape.up ℤ)).obj K)
      ((Pg.mapHomologicalComplex (ComplexShape.up ℤ)).obj L))
    (βh K L) (hg K L)
    (ι_respell_degreewise F₂ F₃ Pg Pf εf K L
      (βf ((Pg.mapHomologicalComplex (ComplexShape.up ℤ)).obj K)
        ((Pg.mapHomologicalComplex (ComplexShape.up ℤ)).obj L))
      (hf ((Pg.mapHomologicalComplex (ComplexShape.up ℤ)).obj K)
        ((Pg.mapHomologicalComplex (ComplexShape.up ℤ)).obj L)))
    (hh K L) (δ K) (δ L) (δ (HomologicalComplex.mapBifunctor K L F₁ (ComplexShape.up ℤ)))
    (hδ K) (hδ L) (hδ (HomologicalComplex.mapBifunctor K L F₁ (ComplexShape.up ℤ)))

end Respelling

/-! ## The composition law for the comparison of total tensor complexes -/

section Composite

variable {X Y Z : RingedTopos.{u, u, u}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Z.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify Y.J AddCommGrpCat.{u}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify Z.J AddCommGrpCat.{u}] [Z.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj M).Additive]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O).obj M).Additive]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Z.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Z.O).obj M).Additive]
  [∀ (A B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ),
    HomologicalComplex.HasMapBifunctor A B
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O) (ComplexShape.up ℤ)]
  [∀ (A B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ),
    HomologicalComplex.HasMapBifunctor A B
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O) (ComplexShape.up ℤ)]
  [∀ (A B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)) ℤ),
    HomologicalComplex.HasMapBifunctor A B
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Z.O) (ComplexShape.up ℤ)]
  (f : RingedToposSiteHom X Y) (g : RingedToposSiteHom Y Z)
  (hmosf : f.u.IsMorphismOfSites Y.J X.J) (hmosg : g.u.IsMorphismOfSites Z.J Y.J)

/-- `Stacks.Sheaves.DerivedPullback.CompositionLaw.pullbackComplexCompIso` at a complex, with the
degreewise pullback functors written as `CategoryTheory.Functor.mapHomologicalComplex` of the
module-level pullbacks.

This is the respelling of `pullbackToposTensorTotalIso'` for the composition isomorphism, and it
exists for the same reason: decided here, at a *variable* complex `M`, it is cheap. -/
private def pullbackComplexCompIsoApp' (M : CochainComplex
    (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)) ℤ) :
    (f.pullbackTopos.mapHomologicalComplex (ComplexShape.up ℤ)).obj
        ((g.pullbackTopos.mapHomologicalComplex (ComplexShape.up ℤ)).obj M) ⟶
      ((g.comp f).pullbackTopos.mapHomologicalComplex (ComplexShape.up ℤ)).obj M :=
  (pullbackComplexCompIso f g).hom.app M

omit [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj M).Additive]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O).obj M).Additive]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Z.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Z.O).obj M).Additive]
  [∀ (A B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ),
    HomologicalComplex.HasMapBifunctor A B
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O) (ComplexShape.up ℤ)]
  [∀ (A B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ),
    HomologicalComplex.HasMapBifunctor A B
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O) (ComplexShape.up ℤ)]
  [∀ (A B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)) ℤ),
    HomologicalComplex.HasMapBifunctor A B
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Z.O) (ComplexShape.up ℤ)] in
/-- The respelled composition isomorphism in a single degree: it is the underived composition
isomorphism of Stacks 0D6D at the term of that degree.  This is
`Stacks.Sheaves.DerivedPullback.CompositionLaw.pullbackComplexCompIso_hom_app_f`. -/
private lemma pullbackComplexCompIsoApp'_f (M : CochainComplex
    (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)) ℤ) (n : ℤ) :
    (pullbackComplexCompIsoApp' f g M).f n =
      (AlgebraicGeometry.RingedToposSiteHom.pullbackToposCompIso f g).hom.app (M.X n) :=
  pullbackComplexCompIso_hom_app_f f g M n

omit [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj M).Additive]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O).obj M).Additive]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Z.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Z.O).obj M).Additive]
  [∀ (A B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ),
    HomologicalComplex.HasMapBifunctor A B
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O) (ComplexShape.up ℤ)]
  [∀ (A B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ),
    HomologicalComplex.HasMapBifunctor A B
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O) (ComplexShape.up ℤ)]
  [∀ (A B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)) ℤ),
    HomologicalComplex.HasMapBifunctor A B
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Z.O) (ComplexShape.up ℤ)] in
/-- **The module-level composition law of Stacks 03EL, in the shape the summandwise reduction's
degreewise hypothesis is stated at**: the two sides exchanged, and the comparison read as the
`hom` of `pullbackToposTensorIsoApp` rather than as
`Stacks.Sheaves.DerivedPullback.pullbackToposTensorMap`.

The two readings differ by one projection — `pullbackToposTensorIsoApp_hom` is `rfl` — and
performing it here leaves the instantiation below with nothing to decide in this slot. -/
private lemma hmod_isoApp (A B : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)) :
    f.pullbackTopos.map (pullbackToposTensorIsoApp g hmosg A B).hom ≫
        (pullbackToposTensorIsoApp f hmosf (g.pullbackTopos.obj A)
            (g.pullbackTopos.obj B)).hom ≫
          (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).map
                ((AlgebraicGeometry.RingedToposSiteHom.pullbackToposCompIso f g).hom.app A)).app
                (f.pullbackTopos.obj (g.pullbackTopos.obj B)) ≫
            ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj
                ((g.comp f).pullbackTopos.obj A)).map
              ((AlgebraicGeometry.RingedToposSiteHom.pullbackToposCompIso f g).hom.app B)) =
      (AlgebraicGeometry.RingedToposSiteHom.pullbackToposCompIso f g).hom.app
          (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Z.O).obj A).obj B) ≫
        (pullbackToposTensorIsoApp (g.comp f)
          (RingedToposSiteHom.isMorphismOfSites_comp_u f g hmosf hmosg) A B).hom :=
  (pullbackToposTensorMap_comp f g hmosf hmosg A B).symm

/-- **The summandwise reduction, instantiated.**  This is
`totalComplexComparison_comp_family` at the site-presented pullback, with its conclusion left at
the spelling `Stacks.TotalTensorComplexComposite.totalComplexComparison_comp` states it in: the
degreewise pullback written as `CategoryTheory.Functor.mapHomologicalComplex` of the module-level
pullback rather than as `Stacks.Sheaves.DerivedPullback.KFlatPullback.pullbackComplex`, and the
two sides in the order it produces them.  `pullbackToposTensorTotalIso_comp` is this identity
respelled and reversed.

Every slot is filled by a lemma of this directory *uninstantiated*: the three comparisons of
total tensor complexes by `pullbackToposTensorTotalIso'`, their three summandwise descriptions by
`ι_pullbackToposTensorIsoApp'`, the degreewise composition isomorphism and its reading in a
single degree by `pullbackComplexCompIsoApp'` and `pullbackComplexCompIsoApp'_f`, and the
module-level composition law by `hmod_isoApp`.  That is what makes this one declaration: each
check is between two statements about variable complexes. -/
private lemma pullbackToposTensorTotalIso_comp_aux
    (P N : CochainComplex
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)) ℤ) :
    (f.pullbackTopos.mapHomologicalComplex (ComplexShape.up ℤ)).map
          (pullbackToposTensorTotalIso' g hmosg P N).hom ≫
        (pullbackToposTensorTotalIso' f hmosf
          ((g.pullbackTopos.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)
          ((g.pullbackTopos.mapHomologicalComplex (ComplexShape.up ℤ)).obj N)).hom ≫
          HomologicalComplex.mapBifunctorMap (pullbackComplexCompIsoApp' f g P)
            (pullbackComplexCompIsoApp' f g N)
            (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O) (ComplexShape.up ℤ) =
      pullbackComplexCompIsoApp' f g (HomologicalComplex.mapBifunctor P N
          (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Z.O) (ComplexShape.up ℤ)) ≫
        (pullbackToposTensorTotalIso' (g.comp f)
          (RingedToposSiteHom.isMorphismOfSites_comp_u f g hmosf hmosg) P N).hom :=
  totalComplexComparison_comp_family
    (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Z.O)
    (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O)
    (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O)
    g.pullbackTopos f.pullbackTopos (g.comp f).pullbackTopos
    (AlgebraicGeometry.RingedToposSiteHom.pullbackToposCompIso f g)
    (pullbackToposTensorIsoApp g hmosg) (pullbackToposTensorIsoApp f hmosf)
    (pullbackToposTensorIsoApp (g.comp f)
      (RingedToposSiteHom.isMorphismOfSites_comp_u f g hmosf hmosg))
    P N
    (hmod_isoApp f g hmosf hmosg)
    (pullbackToposTensorTotalIso' g hmosg) (pullbackToposTensorTotalIso' f hmosf)
    (pullbackToposTensorTotalIso' (g.comp f)
      (RingedToposSiteHom.isMorphismOfSites_comp_u f g hmosf hmosg))
    (ι_pullbackToposTensorIsoApp' g hmosg) (ι_pullbackToposTensorIsoApp' f hmosf)
    (ι_pullbackToposTensorIsoApp' (g.comp f)
      (RingedToposSiteHom.isMorphismOfSites_comp_u f g hmosf hmosg))
    (pullbackComplexCompIsoApp' f g) (pullbackComplexCompIsoApp'_f f g)

/-- **The comparison of total tensor complexes of Stacks 03EL is compatible with composition of
site-presented morphisms of ringed topoi.**  For arbitrary cochain complexes `P`, `N` of
`𝒪_E`-modules, the composition isomorphism `g^* ⋙ f^* ≅ (g ∘ f)^*` of Stacks 0D6D read
degreewise on complexes, followed by the comparison

`(g ∘ f)^*Tot(P ⊗_{𝒪_E} N) ≅ Tot((g ∘ f)^*P ⊗_{𝒪_C} (g ∘ f)^*N)`,

is the comparison for `g`, then the comparison for `f`, then the composition isomorphism in each
tensor factor.

There is **no hypothesis on `P` or `N`**: no K-flatness, no boundedness, no flatness of terms.
The identity is checked on the summands of the total complex by
`Stacks.TotalTensorComplexComposite.totalComplexComparison_comp`, and pullback of sheaves of
modules, being a left adjoint, preserves the coproduct decomposition of each total degree.

The one degreewise input of the summandwise reduction is the module-level composition law of
Stacks 03EL, `pullbackToposTensorMap_comp` of `PullbackToposTensorCompositionLaw.lean` in this
directory, which carries no hypothesis beyond the two morphism-of-sites witnesses.  Nothing is
assumed here that is not assumed there. -/
theorem pullbackToposTensorTotalIso_comp
    (P N : CochainComplex
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)) ℤ) :
    (pullbackComplexCompIso f g).hom.app
          (HomologicalComplex.mapBifunctor P N
            (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Z.O)
            (ComplexShape.up ℤ)) ≫
        (pullbackToposTensorTotalIso (g.comp f)
          (RingedToposSiteHom.isMorphismOfSites_comp_u f g hmosf hmosg) P N).hom =
      (pullbackComplex f).map ((pullbackToposTensorTotalIso g hmosg P N).hom) ≫
        (pullbackToposTensorTotalIso f hmosf ((pullbackComplex g).obj P)
          ((pullbackComplex g).obj N)).hom ≫
          HomologicalComplex.mapBifunctorMap
            ((pullbackComplexCompIso f g).hom.app P)
            ((pullbackComplexCompIso f g).hom.app N)
            (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O)
            (ComplexShape.up ℤ) :=
  (pullbackToposTensorTotalIso_comp_aux f g hmosf hmosg P N).symm

attribute [local instance] HasDerivedCategory.standard

/-- **The composition law of Stacks 03EL for the comparison of total tensor complexes, carried
along `CategoryTheory.DerivedCategory.Q`.**

This is `pullbackToposTensorTotalIso_comp` with every factor read in the derived category, with
the comparison written through
`Stacks.Sheaves.DerivedPullback.pullbackTensorComplexIso` — the same isomorphism with its source
and target spelled by the total tensor complex functor
`Stacks.SheafOfModules.Tensor.tensorComplex` — and with the right-hand side right-associated.
It is the shape the Stacks 07A4 composition law
`Stacks.Sheaves.DerivedPullback.derivedPullbackTensorIso_comp` consumes as its `htotal` input,
read at `e := pullbackComplexCompIso f g`.

The passage along `DerivedCategory.Q` is
`Stacks.Cohomology.DerivedPullbackTensor.map_comp_eq_of_comp_eq`: the three `Functor.map_comp`
rewrites it performs by unification cannot be performed directly, since that would require
abstracting a map between total tensor complexes into a rewrite motive. -/
theorem map_pullbackToposTensorTotalIso_comp
    (P N : CochainComplex
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)) ℤ) :
    DerivedCategory.Q.map ((pullbackComplexCompIso f g).hom.app
          (((Stacks.SheafOfModules.Tensor.tensorComplex Z.O).obj P).obj N)) ≫
        DerivedCategory.Q.map (pullbackTensorComplexIso (g.comp f)
          (RingedToposSiteHom.isMorphismOfSites_comp_u f g hmosf hmosg) P N).hom =
      DerivedCategory.Q.map ((pullbackComplex f).map
          (pullbackTensorComplexIso g hmosg P N).hom) ≫
        DerivedCategory.Q.map (pullbackTensorComplexIso f hmosf
            ((pullbackComplex g).obj P) ((pullbackComplex g).obj N)).hom ≫
          DerivedCategory.Q.map (HomologicalComplex.mapBifunctorMap
            ((pullbackComplexCompIso f g).hom.app P)
            ((pullbackComplexCompIso f g).hom.app N)
            (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O)
            (ComplexShape.up ℤ)) :=
  Stacks.Cohomology.DerivedPullbackTensor.map_comp_eq_of_comp_eq DerivedCategory.Q
    (pullbackToposTensorTotalIso_comp f g hmosf hmosg P N).symm rfl

end Composite

end Stacks.Sheaves.DerivedPullback

end
