module

public import Mathlib.Algebra.Homology.Functor
public import Mathlib.Algebra.Homology.SpectralObject.FirstPage
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import Mathlib.CategoryTheory.Triangulated.TStructure.SpectralObject
public import StacksCore.Algebra.Homology.SpectralSequence.PageInfinity
public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedFunctorInjective
public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlusComparisons
public import StacksFrontier.CategoryTheory.Subobject.Butterfly
public import StacksFrontier.Topology.Sheaves.Cohomology.HigherDirectImage.SheafifiedCohomologyPresheaf
public import StacksFrontier.Topology.Sheaves.Cohomology.Leray.FunctorialFirstQuadrantAbutment
public import StacksFrontier.Topology.Sheaves.Cohomology.Leray.FunctorialRightHalfPlaneAbutment
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The functorial Grothendieck spectral sequence of a composition

Let `F : 𝒜 ⥤ ℬ` and `G : ℬ ⥤ 𝒞` be additive functors of abelian categories, with `𝒜` and `ℬ`
having enough injectives. This file constructs, as a *functor* on the bounded below derived
category `D⁺(𝒜)` and on `𝒜` itself, the Grothendieck spectral sequence

`E₂^{p,q} = R^pG(H^q(RF(K)))  ⟹  H^{p+q}(R(G ∘ F)(K))`,

together with its second-page identification and its filtered abutment, all natural in `K`.

`CategoryTheory.Functor.exists_spectralSequence_rightDerivedFunctorPlus_comp`
([Stacks, Tag 015N]) already produces this spectral sequence, but as an *existence* statement:
its proof chooses a bounded below complex representing `RF(K)` and a Cartan-Eilenberg
resolution of it, neither choice being natural in `K`, so no functorial datum can be extracted
from it. The construction here takes a different route and is functorial by construction.

## The route

The truncation spectral object of the `t`-structure on `D⁺(ℬ)`, pushed along `RG` and read
through the homology functor of `D⁺(𝒞)`, is a functor
`D⁺(𝒜) ⥤ CategoryTheory.Abelian.SpectralObject 𝒞 EInt`
(`derivedTruncationSpectralObjectFunctor`). The spectral sequence of a spectral object is a
construction on objects only, so a functor into spectral objects does not immediately give a
functor into spectral sequences. What does give one is to read such a functor as a *single*
spectral object of the functor category `D⁺(𝒜) ⥤ 𝒞` (`spectralObjectInFunctorCategory`, the
functor category being abelian and the exactness conditions being objectwise), form its
spectral sequence there, and uncurry (`spectralSequenceAsFunctor`). Every construction on a
single spectral object then becomes automatically natural: the abutment filtration by the
images of the `H`-terms, and the identification of its graded pieces with the terms of the
infinity page, are built once in the functor category.

What that costs is a comparison between the spectral sequence of the functor-category spectral
object evaluated at an object `K` and the spectral sequence of `K`'s own spectral object. For
the first-quadrant case -- a single object of `𝒜`, placed in degree zero -- nothing is needed:
the page at which the infinity term is reached is uniform. For a bounded below complex the
lower cohomological bound varies with the complex, and `plusNu` is the comparison from the
whole-interval `E`-term to the `(p, q)` spot of a page, a natural transformation for every page
`r > p`, which becomes an isomorphism at a given object once `r` is large enough for it.

## Main definitions

* `Stacks.Cohomology.Grothendieck.derivedTruncationSpectralSequenceFunctor`: the Grothendieck
  spectral sequence of `F` and `G` as a functor
  `D⁺(𝒜) ⥤ E₂CohomologicalSpectralSequence 𝒞`.
* `Stacks.Cohomology.Grothendieck.derivedTruncationSpectralSequenceNatFunctor`: the same for a
  single object of `𝒜`, as a functor `𝒜 ⥤ E₂CohomologicalSpectralSequenceNat 𝒞`.

The intermediate constructions -- the truncation spectral object as a functor, its reading as a
single spectral object of the functor category, the uncurrying of a spectral sequence of a
functor category, and the abutment filtration by the images of the `H`-terms -- are private to
this module; see "The route" above for what they are.

## Main results

* `Stacks.Cohomology.Grothendieck.natPageTwoIso` and
  `Stacks.Cohomology.Grothendieck.plusPageTwoIso`: the second page is `R^qF ⋙ R^pG`,
  respectively `RF ⋙ H^q ⋙ R^pG`, as an isomorphism of functors.
* `Stacks.Cohomology.Grothendieck.natAbutment`: the functorial first-quadrant filtered abutment
  of the spectral sequence of a single object, abutting to `R^n(G ∘ F)`.
* `Stacks.Cohomology.Grothendieck.plusAbutment`: the functorial right-half-plane filtered
  abutment of the spectral sequence of a bounded below complex, abutting to `H^n(R(G ∘ F))`.
* `Stacks.Cohomology.Grothendieck.derivedTruncationSpectralSequenceFunctor_pageTwo_isZero`: the
  second page vanishes in the left half plane.
* `Stacks.Cohomology.Grothendieck.abutsToChangeAbutmentPlus`: a functorial right-half-plane
  abutment transports along an isomorphism of the abutting functors, which is the
  right-half-plane counterpart of
  `Stacks.Cohomology.Leray.FunctorialFirstQuadrantAbutsTo.ofIsoAbutment`.

## Implementation notes

Several steps are deliberately written as term-level `Eq.trans`/`congrArg` chains rather than
with rewriting tactics. The reason is always the same: an identification such as
`((spectralSequenceEvaluate E K).page r hr).X pq = ((E.page r hr).X pq).obj K` holds only at
semireducible transparency, so `rw` and `simp` cannot build a type-correct motive and report
`motive is not type correct` or `simp made no progress`. Naming each equation instead of
letting a tactic pattern-match for it is the technique; the comments at each such step say
which identification is at fault. Where instance search is what fails, the sanctioned
`attribute [local implicit_reducible]` is used instead, scoped to the declarations that need
it.

## References

* [Stacks Project, Tag 015M](https://stacks.math.columbia.edu/tag/015M)
* [Stacks Project, Tag 015N](https://stacks.math.columbia.edu/tag/015N)
* [Stacks Project, Tag 0734](https://stacks.math.columbia.edu/tag/0734)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace Stacks.Cohomology.Grothendieck

open Stacks.Cohomology.HigherDirectImagePresheaf (derivedPlusToStandard)

attribute [local instance] HasDerivedCategory.standard

section Construction

open CategoryTheory.ComposableArrows

attribute [local instance 2000]
  HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

/-- Vanishing at the initial page persists on every subsequent page. -/
@[ega "0 11.1.6" "partial"]
private theorem isZero_page_of_isZero_initial
    {A I : Type*} [Category A] [Abelian A]
    {c : ℤ → ComplexShape I} {r₀ : ℤ}
    (E : SpectralSequence A c r₀) (i : I)
    (h : IsZero ((E.page r₀).X i)) (r : ℤ) (hr : r₀ ≤ r) :
    IsZero ((E.page r hr).X i) := by
  induction r, hr using Int.leInduction with
  | base => exact h
  | succ r hr ih =>
    exact (((E.page r hr).sc i).isZero_homology_of_isZero_X₂ ih).of_iso
      (E.iso r (r + 1) i rfl hr).symm

private theorem exact_pair_of_exact_app
    {D A : Type*} [Category D] [Category A] [Abelian A]
    {P Q R : D ⥤ A} (f : P ⟶ Q) (g : Q ⟶ R)
    (h : ∀ X, (mk₂ (f.app X) (g.app X)).Exact) : (mk₂ f g).Exact := by
  have w : f ≫ g = 0 := by
    ext X
    exact (h X).zero 0
  let T := ShortComplex.mk f g w
  have ht : T.Exact := by
    rw [T.exact_iff_isZero_homology, IsZero.iff_id_eq_zero]
    ext X
    have he : (T.map ((evaluation D A).obj X)).Exact := (h X).exact 0
    have hz := (T.map ((evaluation D A).obj X)).exact_iff_isZero_homology.mp he
    have hz' : IsZero (T.homology.obj X) :=
      hz.of_iso (T.mapHomologyIso ((evaluation D A).obj X)).symm
    exact hz'.eq_of_src _ _
  exact ht.exact_toComposableArrows

private def spectralObjectHomologyFunctor
    {A I : Type*} [Category A] [Abelian A] [Category I] (n : ℤ) :
    Abelian.SpectralObject A I ⥤ (ComposableArrows I 1 ⥤ A) where
  obj S := S.H n
  map f := f.hom n

private noncomputable def spectralObjectInFunctorCategory
    {D A I : Type*} [Category D] [Category A] [Abelian A] [Category I]
    (S : D ⥤ Abelian.SpectralObject A I) : Abelian.SpectralObject (D ⥤ A) I where
  H n := (S ⋙ spectralObjectHomologyFunctor n).flip
  δ' n m h :=
    { app J :=
        { app X := ((S.obj X).δ' n m h).app J
          naturality X Y f := by
            obtain ⟨a, b, c, u, v, rfl⟩ := mk₂_surjective J
            exact ((S.map f).comm n m h u v).symm }
      naturality J K f := by
        ext X
        exact ((S.obj X).δ' n m h).naturality f }
  exact₁' n m h J := exact_pair_of_exact_app _ _ (fun X => (S.obj X).exact₁' n m h J)
  exact₂' n J := exact_pair_of_exact_app _ _ (fun X => (S.obj X).exact₂' n J)
  exact₃' n m h J := exact_pair_of_exact_app _ _ (fun X => (S.obj X).exact₃' n m h J)

private noncomputable def spectralSequenceEvaluate
    {D A I : Type*} [Category D] [Category A] [Abelian A]
    {c : ℤ → ComplexShape I} {r₀ : ℤ}
    (E : SpectralSequence (D ⥤ A) c r₀) (X : D) : SpectralSequence A c r₀ where
  page r hr := (E.page r hr).asFunctor.obj X
  iso r r' i hrr' hr :=
    ((E.page r hr).sc i).mapHomologyIso ((evaluation D A).obj X) ≪≫
      ((evaluation D A).obj X).mapIso (E.iso r r' i hrr' hr)

private noncomputable def spectralSequenceEvaluateMap
    {D A I : Type*} [Category D] [Category A] [Abelian A]
    {c : ℤ → ComplexShape I} {r₀ : ℤ}
    (E : SpectralSequence (D ⥤ A) c r₀) {X Y : D} (f : X ⟶ Y) :
    spectralSequenceEvaluate E X ⟶ spectralSequenceEvaluate E Y where
  hom r hr := (E.page r hr).asFunctor.map f
  comm r r' i hrr' hr := by
    change ShortComplex.homologyMap (((E.page r hr).sc i).mapNatTrans
        ((evaluation D A).map f)) ≫
      (((E.page r hr).sc i).mapHomologyIso ((evaluation D A).obj Y)).hom ≫
        (E.iso r r' i hrr' hr).hom.app Y =
      ((((E.page r hr).sc i).mapHomologyIso ((evaluation D A).obj X)).hom ≫
        (E.iso r r' i hrr' hr).hom.app X) ≫ ((E.page r' _).X i).map f
    -- The chain below is deliberately term-level. No rewriting tactic can be used:
    -- `((evaluation D A).map f).app ((E.page r hr).sc i).homology` and
    -- `((E.page r hr).homology i).map f` agree only at semireducible transparency, so
    -- `simp`/`rw` cannot even cancel `(mapHomologyIso _).inv ≫ (mapHomologyIso _).hom`
    -- here for want of a type-correct motive. Naming each equation avoids the motive.
    refine (congrArg (fun t => t ≫
        (((E.page r hr).sc i).mapHomologyIso ((evaluation D A).obj Y)).hom ≫
          (E.iso r r' i hrr' hr).hom.app Y)
      (ShortComplex.homologyMap_mapNatTrans ((E.page r hr).sc i)
        ((evaluation D A).map f))).trans ?_
    refine (Category.assoc _ _ _).trans (Eq.trans (congrArg (fun t =>
        (((E.page r hr).sc i).mapHomologyIso ((evaluation D A).obj X)).hom ≫ t) ?_)
      (Category.assoc _ _ _).symm)
    refine (Category.assoc _ _ _).trans ?_
    refine (congrArg (fun t => ((evaluation D A).map f).app
        ((E.page r hr).sc i).homology ≫ t) (Iso.inv_hom_id_assoc _ _)).trans ?_
    exact (E.iso r r' i hrr' hr).hom.naturality f

private noncomputable def spectralSequenceAsFunctor
    {D A I : Type*} [Category D] [Category A] [Abelian A]
    {c : ℤ → ComplexShape I} {r₀ : ℤ}
    (E : SpectralSequence (D ⥤ A) c r₀) : D ⥤ SpectralSequence A c r₀ where
  obj := spectralSequenceEvaluate E
  map := spectralSequenceEvaluateMap E
  map_id X := by ext r hr i; exact ((E.page r hr).X i).map_id X
  map_comp f g := by ext r hr i; exact ((E.page r hr).X i).map_comp f g

section EvaluateEdgeMono

/-! ### Evaluation of the edge monomorphism step

`spectralSequenceEvaluate` computes the pages of the evaluated spectral sequence as the
evaluated pages, but its page-to-page isomorphism carries the comparison
`ShortComplex.mapHomologyIso` for the evaluation functor. The three declarations below cancel
that comparison, so that the one-step edge monomorphism of the evaluated spectral sequence is
the evaluation of the one-step edge monomorphism. This is what makes the edge maps of the
right-half-plane spectral sequence of a single object comparable with the structural maps of
the underlying spectral object, which live in the functor category.

Every step is a term-level `Eq.trans`/`congrArg` chain. A rewriting tactic cannot be used:
the identifications `((spectralSequenceEvaluate E X).page r hr).X pq = ((E.page r hr).X pq).obj X`
and `(hl.map F).H = F.obj hl.H` hold only at semireducible transparency, so `rw` and `simp`
fail to build a type-correct motive. Naming each equation instead of letting a tactic
pattern-match for it is the whole technique here.
-/

/-- For a functor preserving homology, the projection to the homology of the image short
complex, followed by the homology comparison and the image of a right inverse of the
projection to homology composed with the inclusion of cycles, is the inclusion of cycles. -/
private theorem mapHomologyIso_hom_comp_map_iCycles
    {A B : Type*} [Category A] [Category B] [Abelian A] [Abelian B]
    (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (S : ShortComplex A) (e : S.homology ≅ S.cycles)
    (he : S.homologyπ ≫ e.hom = 𝟙 _) :
    (S.map F).homologyπ ≫ (S.mapHomologyIso F).hom ≫ F.map (e.hom ≫ S.iCycles) =
      (S.map F).iCycles := by
  have key2 : S.homologyπ ≫ e.hom ≫ S.iCycles = S.iCycles := by
    rw [← Category.assoc, he, Category.id_comp]
  have key : S.leftHomologyData.π ≫ S.leftHomologyData.homologyIso.inv ≫
      e.hom ≫ S.iCycles = S.leftHomologyData.i := by
    rw [ShortComplex.LeftHomologyData.π_comp_homologyIso_inv_assoc, key2,
      ← ShortComplex.LeftHomologyData.cyclesIso_hom_comp_i S.leftHomologyData,
      Iso.inv_hom_id_assoc]
  calc (S.map F).homologyπ ≫ (S.mapHomologyIso F).hom ≫ F.map (e.hom ≫ S.iCycles)
      = (S.map F).homologyπ ≫ ((S.leftHomologyData.map F).homologyIso.hom ≫
          F.map S.leftHomologyData.homologyIso.inv) ≫ F.map (e.hom ≫ S.iCycles) :=
        congrArg (fun t => (S.map F).homologyπ ≫ t ≫ F.map (e.hom ≫ S.iCycles))
          (congrArg Iso.hom (S.leftHomologyData.mapHomologyIso_eq F))
    _ = (S.map F).homologyπ ≫ (S.leftHomologyData.map F).homologyIso.hom ≫
          F.map S.leftHomologyData.homologyIso.inv ≫ F.map (e.hom ≫ S.iCycles) :=
        congrArg (fun t => (S.map F).homologyπ ≫ t)
          (Category.assoc (S.leftHomologyData.map F).homologyIso.hom
            (F.map S.leftHomologyData.homologyIso.inv) (F.map (e.hom ≫ S.iCycles)))
    _ = ((S.map F).homologyπ ≫ (S.leftHomologyData.map F).homologyIso.hom) ≫
          F.map S.leftHomologyData.homologyIso.inv ≫ F.map (e.hom ≫ S.iCycles) :=
        (Category.assoc _ _ _).symm
    _ = ((S.leftHomologyData.map F).cyclesIso.hom ≫ (S.leftHomologyData.map F).π) ≫
          F.map S.leftHomologyData.homologyIso.inv ≫ F.map (e.hom ≫ S.iCycles) :=
        congrArg
          (fun t => t ≫ F.map S.leftHomologyData.homologyIso.inv ≫
            F.map (e.hom ≫ S.iCycles))
          (ShortComplex.LeftHomologyData.homologyπ_comp_homologyIso_hom (S.map F)
            (S.leftHomologyData.map F))
    _ = (S.leftHomologyData.map F).cyclesIso.hom ≫ (S.leftHomologyData.map F).π ≫
          F.map S.leftHomologyData.homologyIso.inv ≫ F.map (e.hom ≫ S.iCycles) :=
        Category.assoc _ _ _
    _ = (S.leftHomologyData.map F).cyclesIso.hom ≫
          F.map S.leftHomologyData.π ≫
            F.map (S.leftHomologyData.homologyIso.inv ≫ e.hom ≫ S.iCycles) :=
        congrArg (fun t => (S.leftHomologyData.map F).cyclesIso.hom ≫
            F.map S.leftHomologyData.π ≫ t)
          (F.map_comp S.leftHomologyData.homologyIso.inv (e.hom ≫ S.iCycles)).symm
    _ = (S.leftHomologyData.map F).cyclesIso.hom ≫
          F.map (S.leftHomologyData.π ≫ S.leftHomologyData.homologyIso.inv ≫
            e.hom ≫ S.iCycles) :=
        congrArg (fun t => (S.leftHomologyData.map F).cyclesIso.hom ≫ t)
          (F.map_comp S.leftHomologyData.π
            (S.leftHomologyData.homologyIso.inv ≫ e.hom ≫ S.iCycles)).symm
    _ = (S.leftHomologyData.map F).cyclesIso.hom ≫ (S.leftHomologyData.map F).i :=
        congrArg (fun t => (S.leftHomologyData.map F).cyclesIso.hom ≫ F.map t) key
    _ = (S.map F).iCycles :=
        ShortComplex.LeftHomologyData.cyclesIso_hom_comp_i (S.leftHomologyData.map F)

/-- Where the differential into `j` vanishes, the homology comparison for the evaluation
functor identifies the evaluation of `homology ≅ cycles ⟶ X j` with the same map formed in the
evaluated complex. -/
private theorem mapHomologyIso_inv_comp_isoHomologyπ_inv
    {D A I : Type*} [Category D] [Category A] [Abelian A] {c : ComplexShape I}
    (K : HomologicalComplex (D ⥤ A) c) (X : D) (i j : I) (hi : c.prev j = i)
    (h : K.d i j = 0) (h' : (K.asFunctor.obj X).d i j = 0) :
    ((K.sc j).mapHomologyIso ((evaluation D A).obj X)).inv ≫
      ((K.asFunctor.obj X).isoHomologyπ i j hi h').inv ≫ (K.asFunctor.obj X).iCycles j =
    ((evaluation D A).obj X).map ((K.isoHomologyπ i j hi h).inv ≫ K.iCycles j) := by
  refine (Iso.inv_comp_eq _).2 ?_
  refine (cancel_epi (((K.asFunctor.obj X).isoHomologyπ i j hi h').hom)).1 ?_
  exact (Iso.hom_inv_id_assoc _ _).trans
    (mapHomologyIso_hom_comp_map_iCycles ((evaluation D A).obj X) (K.sc j)
      (K.isoHomologyπ i j hi h).symm (K.isoHomologyπ_hom_inv_id i j hi h)).symm

/-- Vanishing of the differentials into `pq` on the page `r` passes to the evaluation. -/
private theorem spectralSequenceEvaluate_hasEdgeMonoAt
    {D A I : Type*} [Category D] [Category A] [Abelian A]
    {c : ℤ → ComplexShape I} {r₀ : ℤ}
    (E : SpectralSequence (D ⥤ A) c r₀) (X : D) (pq : I) (r : ℤ)
    [E.HasEdgeMonoAt pq r] : (spectralSequenceEvaluate E X).HasEdgeMonoAt pq r where
  le := E.le₀_of_hasEdgeMonoAt pq r
  zero pq' := by
    change ((E.page r _).d pq' pq).app X = 0
    rw [E.d_eq_zero_of_hasEdgeMonoAt pq' pq r]
    rfl

attribute [local instance] spectralSequenceEvaluate_hasEdgeMonoAt

/-- The one-step edge monomorphism of an evaluated spectral sequence is the evaluation of the
one-step edge monomorphism. -/
private theorem spectralSequenceEvaluate_edgeMonoStep
    {D A I : Type*} [Category D] [Category A] [Abelian A]
    {c : ℤ → ComplexShape I} {r₀ : ℤ}
    (E : SpectralSequence (D ⥤ A) c r₀) (X : D) (pq : I) (r r' : ℤ) (hrr' : r + 1 = r')
    [E.HasEdgeMonoAt pq r] :
    (spectralSequenceEvaluate E X).edgeMonoStep pq r r' hrr' =
      (E.edgeMonoStep pq r r' hrr').app X := by
  have hr := E.le₀_of_hasEdgeMonoAt pq r
  have h : (E.page r hr).d ((c r).prev pq) pq = 0 := E.d_eq_zero_of_hasEdgeMonoAt _ pq r
  have h' : ((E.page r hr).asFunctor.obj X).d ((c r).prev pq) pq = 0 :=
    (spectralSequenceEvaluate E X).d_eq_zero_of_hasEdgeMonoAt ((c r).prev pq) pq r
  exact Eq.trans (Category.assoc _ _ _) (Eq.trans
    (congrArg (fun t => ((evaluation D A).obj X).map (E.iso r r' pq hrr' hr).inv ≫ t)
      (mapHomologyIso_inv_comp_isoHomologyπ_inv (E.page r hr) X ((c r).prev pq) pq rfl h h'))
    ((((evaluation D A).obj X).map_comp _ _).symm))

end EvaluateEdgeMono

private noncomputable def spectralObjectSequenceFunctor
    {D A : Type*} [Category D] [Category A] [Abelian A]
    (S : D ⥤ Abelian.SpectralObject A EInt) : D ⥤ E₂CohomologicalSpectralSequence A :=
  spectralSequenceAsFunctor (spectralObjectInFunctorCategory S).E₂SpectralSequence

private noncomputable def spectralObjectSequenceFunctorPageTwoIso
    {D A : Type*} [Category D] [Category A] [Abelian A]
    (S : D ⥤ Abelian.SpectralObject A EInt) (p q : ℤ) :
    spectralObjectSequenceFunctor S ⋙ SpectralSequence.pageFunctor _ _ 2 2 ⋙
      HomologicalComplex.eval _ _ (p, q) ≅
    (spectralObjectInFunctorCategory S).H (p + q) |>.obj
      (mk₁ (homOfLE (show (q : EInt) ≤ (q + 1 : ℤ) by simp))) :=
  (spectralObjectInFunctorCategory S).spectralSequenceFirstPageXIso
    Abelian.SpectralObject.coreE₂Cohomological (p, q) q (q + 1 : ℤ) rfl rfl (p + q) rfl

/-- The truncation spectral object for a composite of right derived functors. -/
private noncomputable def derivedTruncationSpectralObjectFunctor
    {A B C : Type*} [Category A] [Category B] [Category C]
    [Abelian A] [Abelian B] [Abelian C]
    [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory C]
    [EnoughInjectives A] [EnoughInjectives B]
    (F : A ⥤ B) (G : B ⥤ C) [F.Additive] [G.Additive] :
    DerivedCategory.Plus A ⥤ Abelian.SpectralObject C EInt := by
  letI : G.rightDerivedFunctorPlus.CommShift ℤ :=
    Functor.IsRightDerivedFunctor.commShift _ G.rightDerivedFunctorPlusUnith
      (HomotopyCategory.Plus.quasiIso B) ℤ
  haveI : NatTrans.CommShift G.rightDerivedFunctorPlusUnith ℤ :=
    Functor.IsRightDerivedFunctor.natTrans_commShift G.rightDerivedFunctorPlus
      G.rightDerivedFunctorPlusUnith (HomotopyCategory.Plus.quasiIso B) ℤ
  haveI : G.rightDerivedFunctorPlus.IsTriangulated :=
    Functor.isTriangulated_of_isRightDerivedFunctor_mapHomotopyCategoryPlus G _
      G.rightDerivedFunctorPlusUnith
  exact F.rightDerivedFunctorPlus ⋙
    DerivedCategory.Plus.TStructure.t.spectralObjectFunctor ⋙
    G.rightDerivedFunctorPlus.mapTriangulatedSpectralObject EInt ⋙
    Triangulated.SpectralObject.mapHomologicalFunctorFunctor
      (DerivedCategory.Plus.homologyFunctor C 0) EInt

/-- The functorial spectral sequence of the derived truncation spectral object. -/
@[no_expose] noncomputable def derivedTruncationSpectralSequenceFunctor
    {A B C : Type*} [Category A] [Category B] [Category C]
    [Abelian A] [Abelian B] [Abelian C]
    [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory C]
    [EnoughInjectives A] [EnoughInjectives B]
    (F : A ⥤ B) (G : B ⥤ C) [F.Additive] [G.Additive] :
    DerivedCategory.Plus A ⥤ E₂CohomologicalSpectralSequence C :=
  spectralObjectSequenceFunctor (derivedTruncationSpectralObjectFunctor F G)

private noncomputable def quotientPlusQhIso
    {A : Type*} [Category A] [Abelian A] [HasDerivedCategory A]
    (N : CochainComplex.Plus A) :
    DerivedCategory.Plus.Qh.obj ((HomotopyCategory.Plus.quotient A).obj N) ≅
      DerivedCategory.Plus.Q.obj N :=
  DerivedCategory.Plus.ι.preimageIso
    ((DerivedCategory.Plus.QhCompιIsoιCompQh A).app _ ≪≫
      DerivedCategory.Qh.mapIso ((HomotopyCategory.Plus.quotientCompιIso A).app N) ≪≫
      (DerivedCategory.quotientCompQhIso A).app N.obj)

private theorem rightDerivedFunctorPlus_isGE
    {A B : Type*} [Category A] [Category B] [Abelian A] [Abelian B]
    [HasDerivedCategory A] [HasDerivedCategory B] [EnoughInjectives A]
    (F : A ⥤ B) [F.Additive] (Y : DerivedCategory.Plus A) (a : ℤ) [Y.IsGE a] :
    (F.rightDerivedFunctorPlus.obj Y).IsGE a := by
  obtain ⟨L, hL, ⟨e⟩⟩ := DerivedCategory.Plus.exists_injective_nonempty_iso Y a
  let N := (InjectiveObject.ι A).mapCochainComplexPlus.obj L
  have hN : (F.mapCochainComplexPlus.obj N).obj.IsStrictlyGE a := by
    change CochainComplex.IsStrictlyGE ((F.mapHomologicalComplex _).obj
      (((InjectiveObject.ι A).mapHomologicalComplex _).obj L.obj)) a
    infer_instance
  have hiso : IsIso (F.rightDerivedFunctorPlusUnith.app
      ((HomotopyCategory.Plus.quotient A).obj N)) := by
    have : ∀ i : ℤ, Injective (((HomotopyCategory.Plus.quotient A).obj N).obj.as.X i) :=
      fun _ => inferInstance
    infer_instance
  have : (DerivedCategory.Plus.Q.obj (F.mapCochainComplexPlus.obj N)).IsGE a := by
    rw [← DerivedCategory.Plus.isGE_ι_obj_iff]
    change (DerivedCategory.Q.obj (F.mapCochainComplexPlus.obj N).obj).IsGE a
    infer_instance
  exact DerivedCategory.Plus.TStructure.t.isGE_of_iso
    ((quotientPlusQhIso (F.mapCochainComplexPlus.obj N)).symm ≪≫
      @asIso _ _ _ _ _ hiso ≪≫
      F.rightDerivedFunctorPlus.mapIso (quotientPlusQhIso N ≪≫ e)) a

/-- The homology in degree `n` of `RG` applied to an object that is `≥ a` vanishes for `n < a`. -/
private theorem isZero_homology_rightDerivedFunctorPlus_obj
    {B C : Type*} [Category B] [Category C] [Abelian B] [Abelian C]
    [HasDerivedCategory B] [HasDerivedCategory C] [EnoughInjectives B]
    (G : B ⥤ C) [G.Additive] (Y : DerivedCategory.Plus B) (a n : ℤ) [Y.IsGE a] (h : n < a) :
    IsZero ((DerivedCategory.Plus.homologyFunctor C n).obj (G.rightDerivedFunctorPlus.obj Y)) :=
  have := rightDerivedFunctorPlus_isGE G Y a
  DerivedCategory.Plus.isZero_homology_of_isGE _ a n h

/-- The second page at `(p, q)` vanishes as soon as the corresponding homology of `RG` does. -/
private theorem derivedTruncationSpectralSequenceFunctor_pageTwo_isZero_of_isZero
    {A B C : Type*} [Category A] [Category B] [Category C]
    [Abelian A] [Abelian B] [Abelian C]
    [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory C]
    [EnoughInjectives A] [EnoughInjectives B]
    (F : A ⥤ B) (G : B ⥤ C) [F.Additive] [G.Additive]
    (K : DerivedCategory.Plus A) (p q : ℤ)
    (h : IsZero ((DerivedCategory.Plus.homologyFunctor C (p + q)).obj
      (G.rightDerivedFunctorPlus.obj
        ((DerivedCategory.Plus.TStructure.t.truncGE q).obj
          ((DerivedCategory.Plus.TStructure.t.truncLT (q + 1)).obj
            (F.rightDerivedFunctorPlus.obj K)))))) :
    IsZero (((derivedTruncationSpectralSequenceFunctor F G).obj K).page 2 |>.X (p, q)) :=
  IsZero.of_iso (Y := _) h ((spectralObjectSequenceFunctorPageTwoIso
    (derivedTruncationSpectralObjectFunctor F G) p q).app K)

/-- The second page of the Grothendieck spectral sequence vanishes in negative
first degree. -/
theorem derivedTruncationSpectralSequenceFunctor_pageTwo_isZero
    {A B C : Type*} [Category A] [Category B] [Category C]
    [Abelian A] [Abelian B] [Abelian C]
    [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory C]
    [EnoughInjectives A] [EnoughInjectives B]
    (F : A ⥤ B) (G : B ⥤ C) [F.Additive] [G.Additive]
    (K : DerivedCategory.Plus A) (p q : ℤ) (hp : p < 0) :
    IsZero (((derivedTruncationSpectralSequenceFunctor F G).obj K).page 2 |>.X (p, q)) := by
  refine derivedTruncationSpectralSequenceFunctor_pageTwo_isZero_of_isZero F G K p q ?_
  exact isZero_homology_rightDerivedFunctorPlus_obj G _ q (p + q) (by omega)

/-- A lower cohomological bound on the input is also a lower bound on the second index. -/
private theorem derivedTruncationSpectralSequenceFunctor_pageTwo_isZero_of_lt
    {A B C : Type*} [Category A] [Category B] [Category C]
    [Abelian A] [Abelian B] [Abelian C]
    [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory C]
    [EnoughInjectives A] [EnoughInjectives B]
    (F : A ⥤ B) (G : B ⥤ C) [F.Additive] [G.Additive]
    (K : DerivedCategory.Plus A) (a : ℤ) [K.IsGE a]
    (p q : ℤ) (hq : q < a) :
    IsZero (((derivedTruncationSpectralSequenceFunctor F G).obj K).page 2 |>.X (p, q)) := by
  refine derivedTruncationSpectralSequenceFunctor_pageTwo_isZero_of_isZero F G K p q ?_
  have hF := rightDerivedFunctorPlus_isGE F K a
  have hF' := DerivedCategory.Plus.TStructure.t.isGE_of_ge
    (F.rightDerivedFunctorPlus.obj K) (q + 1) a (by omega)
  have hz := (DerivedCategory.Plus.TStructure.t.truncGE q).map_isZero
    (DerivedCategory.Plus.TStructure.t.isZero_truncLT_obj_of_isGE
      (q + 1) (F.rightDerivedFunctorPlus.obj K))
  have ht := DerivedCategory.Plus.TStructure.t.isGE_of_isZero hz (p + q + 1)
  exact isZero_homology_rightDerivedFunctorPlus_obj G _ (p + q + 1) (p + q) (by omega)

/-- The lower vanishing of the Grothendieck spectral object: over an interval whose upper end
is below the cohomological bound of `K`, the `H`-terms vanish. The first-quadrant case is
`a = 0`; the general `a` is what the bounded below derived category needs, where the bound
varies with the object. -/
private theorem derivedTruncationSpectralObject_isZero₁
    {A B C : Type*} [Category A] [Category B] [Category C]
    [Abelian A] [Abelian B] [Abelian C]
    [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory C]
    [EnoughInjectives A] [EnoughInjectives B]
    (F : A ⥤ B) (G : B ⥤ C) [F.Additive] [G.Additive]
    (K : DerivedCategory.Plus A) (a : ℤ) [K.IsGE a]
    (i j : EInt) (hij : i ≤ j) (hj : j ≤ (a : ℤ)) (n : ℤ) :
    IsZero ((((derivedTruncationSpectralObjectFunctor F G).obj K).H n).obj
      (mk₁ (homOfLE hij))) := by
  have hF := rightDerivedFunctorPlus_isGE F K a
  change IsZero ((DerivedCategory.Plus.homologyFunctor C n).obj
    (G.rightDerivedFunctorPlus.obj
      ((DerivedCategory.Plus.TStructure.t.eTruncGE.obj i).obj
        ((DerivedCategory.Plus.TStructure.t.eTruncLT.obj j).obj
          (F.rightDerivedFunctorPlus.obj K)))))
  have hz := (DerivedCategory.Plus.TStructure.t.eTruncGE.obj i).map_isZero
    (DerivedCategory.Plus.TStructure.t.isZero_eTruncLT_obj_obj
      (F.rightDerivedFunctorPlus.obj K) a j hj)
  have ht := DerivedCategory.Plus.TStructure.t.isGE_of_isZero hz (n + 1)
  exact isZero_homology_rightDerivedFunctorPlus_obj G _ (n + 1) n (by omega)

/-- The upper vanishing of the Grothendieck spectral object: above the total degree, the
`H`-terms vanish. This half uses nothing about `K`, which is why it passes to the functor
category on the whole bounded below derived category. -/
private theorem derivedTruncationSpectralObject_isZero₂
    {A B C : Type*} [Category A] [Category B] [Category C]
    [Abelian A] [Abelian B] [Abelian C]
    [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory C]
    [EnoughInjectives A] [EnoughInjectives B]
    (F : A ⥤ B) (G : B ⥤ C) [F.Additive] [G.Additive]
    (K : DerivedCategory.Plus A)
    (i j : EInt) (hij : i ≤ j) (n : ℤ) (hi : n < i) :
    IsZero ((((derivedTruncationSpectralObjectFunctor F G).obj K).H n).obj
      (mk₁ (homOfLE hij))) := by
  change IsZero ((DerivedCategory.Plus.homologyFunctor C n).obj
    (G.rightDerivedFunctorPlus.obj
      ((DerivedCategory.Plus.TStructure.t.eTruncGE.obj i).obj
        ((DerivedCategory.Plus.TStructure.t.eTruncLT.obj j).obj
          (F.rightDerivedFunctorPlus.obj K)))))
  have hb : ((n + 1 : ℤ) : EInt) ≤ i := by
    induction i using WithBotTop.rec with
    | bot => simp at hi
    | coe i =>
      rw [WithBotTop.coe_le_coe]
      rw [WithBotTop.coe_lt_coe] at hi
      omega
    | top => exact le_top
  have ht := DerivedCategory.Plus.TStructure.t.isGE_eTruncGE_obj_obj (n + 1) i hb
    ((DerivedCategory.Plus.TStructure.t.eTruncLT.obj j).obj
      (F.rightDerivedFunctorPlus.obj K))
  exact isZero_homology_rightDerivedFunctorPlus_obj G _ (n + 1) n (by omega)

private theorem derivedTruncationSpectralObject_isFirstQuadrant
    {A B C : Type*} [Category A] [Category B] [Category C]
    [Abelian A] [Abelian B] [Abelian C]
    [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory C]
    [EnoughInjectives A] [EnoughInjectives B]
    (F : A ⥤ B) (G : B ⥤ C) [F.Additive] [G.Additive]
    (K : DerivedCategory.Plus A) [K.IsGE 0] :
    ((derivedTruncationSpectralObjectFunctor F G).obj K).IsFirstQuadrant where
  isZero₁ i j hij hj n := derivedTruncationSpectralObject_isZero₁ F G K 0 i j hij hj n
  isZero₂ i j hij n hi := derivedTruncationSpectralObject_isZero₂ F G K i j hij n hi

private theorem spectralObjectInFunctorCategory_isFirstQuadrant
    {D A : Type*} [Category D] [Category A] [Abelian A]
    (S : D ⥤ Abelian.SpectralObject A EInt)
    (hS : ∀ X, (S.obj X).IsFirstQuadrant) :
    (spectralObjectInFunctorCategory S).IsFirstQuadrant  where
  isZero₁ i j hij hj n := (Functor.isZero_iff _).mpr fun X =>
    have := hS X; (S.obj X).isZero₁_of_isFirstQuadrant i j hij hj n
  isZero₂ i j hij n hi := (Functor.isZero_iff _).mpr fun X =>
    have := hS X; (S.obj X).isZero₂_of_isFirstQuadrant i j hij n hi

/-- The functorial first-quadrant spectral sequence of the derived truncation spectral
object of a single object, placed in degree zero. -/
@[no_expose] noncomputable def derivedTruncationSpectralSequenceNatFunctor
    {A B C : Type*} [Category A] [Category B] [Category C]
    [Abelian A] [Abelian B] [Abelian C]
    [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory C]
    [EnoughInjectives A] [EnoughInjectives B]
    (F : A ⥤ B) (G : B ⥤ C) [F.Additive] [G.Additive] :
    A ⥤ E₂CohomologicalSpectralSequenceNat C := by
  let S := DerivedCategory.Plus.singleFunctor A 0 ⋙ derivedTruncationSpectralObjectFunctor F G
  have := spectralObjectInFunctorCategory_isFirstQuadrant S
    (fun X => derivedTruncationSpectralObject_isFirstQuadrant F G _)
  exact spectralSequenceAsFunctor (spectralObjectInFunctorCategory S).E₂SpectralSequenceNat

end Construction

end Stacks.Cohomology.Grothendieck

end
