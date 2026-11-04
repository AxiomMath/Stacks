module

public import Mathlib.Algebra.Category.ModuleCat.Products
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.AlgebraicGeometry.Sites.Representability
public import Mathlib.CategoryTheory.Limits.Types.Pullbacks
public import Mathlib.CategoryTheory.Preadditive.Biproducts
public import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FreeProjection
public import StacksFrontier.AlgebraicGeometry.Descent.PullbackSectionsSheaf.UnitComparison
public import StacksFrontier.AlgebraicGeometry.Descent.QuasiCoherent.DescentData
public import StacksFrontier.AlgebraicGeometry.Descent.QuasiCoherent.ZariskiEssSurj
public import StacksFrontier.AlgebraicGeometry.Descent.QuasiCoherent.ZariskiGluing
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.Support
public import StacksFrontier.AlgebraicGeometry.GrassmannianChart.Basic
public import StacksFrontier.AlgebraicGeometry.Modules.FiniteLocallyFreeDescent.Fpqc
public import StacksFrontier.AlgebraicGeometry.Modules.FiniteTypeQuotient
public import StacksFrontier.AlgebraicGeometry.Morphisms.Support.PullbackSkyscraper
public import StacksFrontier.AlgebraicGeometry.Recovery27.Functor
public import StacksFrontier.Topology.Sheaves.Modules.LocallyFree
public import StacksFrontier.Topology.Sheaves.Modules.TensorAndDuals.EpiOfConstantRank
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Representability of the Grassmannian functor

For natural numbers `k` and `n` with `0 < k < n`, the Grassmannian functor `G(k, n)`, which
classifies finite locally free quotients of rank `n - k` of the free module of rank `n`, is
representable by a scheme.

## Main definitions

* `AlgebraicGeometry.Grassmannian.gluedScheme`: the scheme glued from the coordinate charts,
  which is the representing object.

## Main results

* `AlgebraicGeometry.Grassmannian.functor_isRepresentable`: the Grassmannian functor
  `G(k, n)` is representable by a scheme.
* `AlgebraicGeometry.Grassmannian.representableBy`: the universal representation of `G(k, n)`
  by `AlgebraicGeometry.Grassmannian.gluedScheme`, for all `k` and `n`.

## Implementation notes

The functor is a sheaf for the Zariski topology because quotient presentations glue. For every
embedding `ι : Fin (n - k) ↪ Fin n` the locus where the composite of the quotient map with the
coordinate inclusion indexed by `ι` is surjective is an open subfunctor, and on it the quotient is
canonically identified with the free module of rank `n - k`, so that the subfunctor is the functor
of `(n - k) × (n - k)` matrices of global sections and hence is represented by an affine space over
`Spec ℤ`. These subfunctors cover because a surjection onto a finite locally free module of rank
`n - k` over a field splits off `n - k` of the coordinate sections. The conclusion is the gluing
criterion for representability.

## References

* [Stacks Project, Tag 089T](https://stacks.math.columbia.edu/tag/089T)
* [Stacks Project, Tag 089S](https://stacks.math.columbia.edu/tag/089S)
* [Stacks Project, Tag 089Q](https://stacks.math.columbia.edu/tag/089Q)
* [Stacks Project, Tag 01JJ](https://stacks.math.columbia.edu/tag/01JJ)
-/

/-!
This file contains the coordinate chart subfunctors of the Grassmannian functor `G(k, n)`, the
normalised quotients on a chart, and their identification with the functor of points of an affine
space over `Spec ℤ`.
-/

public section

open CategoryTheory AlgebraicGeometry Opposite Limits TopologicalSpace

universe u

namespace AlgebraicGeometry.Grassmannian

attribute [local instance 10000] CategoryTheory.CategoryStruct.toQuiver
attribute [local implicit_reducible] AlgebraicGeometry.Scheme.Modules
attribute [local implicit_reducible] CategoryTheory.Functor.sheafPushforwardContinuous
attribute [local implicit_reducible] TopCat.Sheaf sheafCompose
attribute [local implicit_reducible] SheafOfModules.unit PresheafOfModules.unit
attribute [local implicit_reducible] AlgebraicGeometry.Scheme.Modules.Hom
attribute [local implicit_reducible] CategoryTheory.Subfunctor.toFunctor
attribute [local implicit_reducible] AlgebraicGeometry.Scheme.Modules.pullback
attribute [local implicit_reducible] AlgebraicGeometry.Scheme.Modules.pseudofunctor
attribute [local implicit_reducible] CategoryTheory.Bicategory.Adj.forget₁
attribute [local implicit_reducible] CategoryTheory.Pseudofunctor.comp

/-- The inclusion of the free module of rank `n - k` into the free module of rank `n`
sending the `i`-th basis vector to the `ι i`-th one. -/
private noncomputable def coordinateSubmap (X : Scheme.{u}) (k n : ℕ)
    (ι : Fin (n - k) ↪ Fin n) :
    SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u} (Fin (n - k))) ⟶
      SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u} (Fin n)) :=
  SheafOfModules.freeMap (R := X.ringCatSheaf)
    (fun i : ULift.{u} (Fin (n - k)) => ULift.up (ι i.down))

/-- The free module of rank `m` is finite locally free of rank `m`. -/
private theorem free_isFiniteLocallyFreeOfRank (X : Scheme.{u}) (m : ℕ) :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u} (Fin m))) m := by
  apply AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.mk
  let G := SheafOfModules.free.generatingSections
    (R := X.ringCatSheaf) (ULift.{u} (Fin m))
  let q : SheafOfModules.LocalGeneratorsData.{u, u, u, u}
      (SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u} (Fin m))) :=
    G.localGeneratorsData
  refine ⟨q, ?_, ?_⟩
  · infer_instance
  · intro i
    exact ⟨Equiv.ulift⟩

/-- A surjection from the free module of rank `n - k` onto a module that is finite locally free
of the same rank is an isomorphism. -/
private lemma coordinateSubmap_comp_isIso_of_epi (X : Scheme.{u}) (k n : ℕ)
    (ι : Fin (n - k) ↪ Fin n) (q : QuotientPresentation X k n)
    (h : Epi (coordinateSubmap X k n ι ≫ q.map)) :
    IsIso (coordinateSubmap X k n ι ≫ q.map) :=
  (@Stacks.SheafOfModules.isIso_iff_epi_of_isFiniteLocallyFreeOfRank
    X.toLocallyRingedSpace.toRingedSpace inferInstance inferInstance _ _ (n - k)
    (free_isFiniteLocallyFreeOfRank X (n - k)) q.finiteLocallyFree
    (coordinateSubmap X k n ι ≫ q.map)).2 h

/-- If the quotient map composed with the coordinate inclusion indexed by `ι` is surjective, it
identifies the quotient with the free module of rank `n - k`. -/
private noncomputable def coordinateChartNormalizationIso (X : Scheme.{u})
    (k n : ℕ) (ι : Fin (n - k) ↪ Fin n)
    (q : QuotientPresentation X k n)
    (h : Epi (coordinateSubmap X k n ι ≫ q.map)) :
    q.target ≅ SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u} (Fin (n - k))) := by
  letI : IsIso (coordinateSubmap X k n ι ≫ q.map) :=
    coordinateSubmap_comp_isIso_of_epi X k n ι q h
  exact (asIso (coordinateSubmap X k n ι ≫ q.map)).symm

/-- The normalisation isomorphism splits the coordinate inclusion indexed by `ι`. -/
private lemma coordinateChartNormalizationIso_comp (X : Scheme.{u})
    (k n : ℕ) (ι : Fin (n - k) ↪ Fin n)
    (q : QuotientPresentation X k n)
    (h : Epi (coordinateSubmap X k n ι ≫ q.map)) :
    coordinateSubmap X k n ι ≫ q.map ≫
        (coordinateChartNormalizationIso X k n ι q h).hom = 𝟙 _ := by
  let : IsIso (coordinateSubmap X k n ι ≫ q.map) :=
    coordinateSubmap_comp_isIso_of_epi X k n ι q h
  exact IsIso.hom_inv_id (coordinateSubmap X k n ι ≫ q.map)

/-- The condition cutting out the chart attached to `ι`: some presentation representing the given
point of `G(k, n)` has surjective composite with the coordinate inclusion indexed by `ι`. -/
private def coordinateChartCondition (k n : ℕ) (ι : Fin (n - k) ↪ Fin n)
    (X : Scheme.{u}) (x : (functor.{u} k n).obj (op X)) : Prop :=
  ∃ q : QuotientPresentation X k n,
    (functorData.{u} k n).objEquiv X x = ⟦q⟧ ∧
      Epi (coordinateSubmap X k n ι ≫ q.map)

/-- Composing with an isomorphism does not change surjectivity. -/
private lemma epi_comp_iso_iff {C : Type*} [Category C] {A B D : C}
    (f : A ⟶ B) (e : B ≅ D) : Epi (f ≫ e.hom) ↔ Epi f := by
  constructor
  · intro h
    let : Epi (f ≫ e.hom) := h
    let : Epi e.inv := inferInstance
    have hcomp : Epi ((f ≫ e.hom) ≫ e.inv) := epi_comp (f ≫ e.hom) e.inv
    simpa [Category.assoc] using hcomp
  · intro h
    let : Epi f := h
    let : Epi e.hom := inferInstance
    exact epi_comp f e.hom

/-- Presentations related by the generated equivalence relation are isomorphic. -/
private lemma isomorphic_of_eqvGen {X : Scheme.{u}} {k n : ℕ} {q q' : QuotientPresentation X k n}
    (h : Relation.EqvGen QuotientPresentation.Isomorphic q q') : q.Isomorphic q' := by
  induction h with
  | rel _ _ h => exact h
  | refl q => exact ⟨Iso.refl _, Category.comp_id _⟩
  | symm q q' _ ih =>
    obtain ⟨e, he⟩ := ih
    refine ⟨e.symm, ?_⟩
    rw [← he]
    simp
  | trans q q' q'' _ _ ih ih' =>
    obtain ⟨e, he⟩ := ih
    obtain ⟨e', he'⟩ := ih'
    exact ⟨e ≪≫ e', by simp only [Iso.trans_hom, ← Category.assoc, he, he']⟩

/-- Presentations with the same class in `Points` are isomorphic. -/
private lemma quotientPresentation_isomorphic_of_eq {X : Scheme.{u}} {k n : ℕ}
    {q q' : QuotientPresentation X k n}
    (h : (⟦q⟧ : Points X k n) = ⟦q'⟧) :
    q.Isomorphic q' :=
  isomorphic_of_eqvGen (Quotient.exact h)

/-- The chart condition may be tested on any presentation representing the given point. -/
private lemma coordinateChartCondition_iff_epi (k n : ℕ)
    (ι : Fin (n - k) ↪ Fin n) (X : Scheme.{u})
    (x : (functor.{u} k n).obj (op X))
    (q : QuotientPresentation X k n)
    (hq : (functorData.{u} k n).objEquiv X x = ⟦q⟧) :
    coordinateChartCondition k n ι X x ↔
      Epi (coordinateSubmap X k n ι ≫ q.map) := by
  constructor
  · rintro ⟨q', hq', hEpi⟩
    obtain ⟨e, he⟩ := quotientPresentation_isomorphic_of_eq (hq.symm.trans hq')
    have hcomp : coordinateSubmap X k n ι ≫ q'.map =
        (coordinateSubmap X k n ι ≫ q.map) ≫ e.hom := by
      rw [Category.assoc, he]
    rw [hcomp] at hEpi
    exact (epi_comp_iso_iff _ e).mp hEpi
  · intro hEpi
    exact ⟨q, hq, hEpi⟩

/-- The instances needed to work with the module pullback along a morphism of schemes. -/
private theorem pullback_instances {S T : Scheme.{u}} (f : T ⟶ S) :
    (SheafOfModules.pushforward.{u} f.toRingCatSheafHom).IsRightAdjoint ∧
      (TopologicalSpace.Opens.map f.base).Final :=
  ⟨(Scheme.Modules.pullbackPushforwardAdjunction f).isRightAdjoint,
    CategoryTheory.final_of_representablyFlat _⟩

/-- Pullback of modules along a morphism of schemes preserves surjections. -/
private lemma pullback_preserves_epi {S T : Scheme.{u}} (f : T ⟶ S)
    {A B : S.Modules} (g : A ⟶ B) (hg : Epi g) :
    Epi ((Scheme.Modules.pullback f).map g) := by
  obtain ⟨_, _⟩ := pullback_instances f
  let : Epi g := hg
  let : (Scheme.Modules.pullback f).PreservesEpimorphisms :=
    Functor.preservesEpimorphisms_of_adjunction (Scheme.Modules.pullbackPushforwardAdjunction f)
  exact Functor.map_epi _ g

/-- The coordinate inclusion indexed by `ι` commutes with pullback, through the identifications
of the pullbacks of the free modules. -/
private lemma coordinateSubmap_pullback_naturality {S T : Scheme.{u}} (f : T ⟶ S)
    (k n : ℕ) (ι : Fin (n - k) ↪ Fin n) :
    (Scheme.Modules.pullback f).map (coordinateSubmap S k n ι) ≫
        (pullbackFreeIso f n).hom =
      (pullbackFreeIso f (n - k)).hom ≫ coordinateSubmap T k n ι := by
  obtain ⟨_, _⟩ := pullback_instances f
  have h := SheafOfModules.pullbackObjFreeIso_hom_naturality f.toRingCatSheafHom
    (fun i : ULift.{u} (Fin (n - k)) => ULift.up (ι i.down))
  exact h

/-- The chart condition is stable under pullback along a morphism of schemes. -/
private lemma coordinateChartCondition_map (k n : ℕ)
    (ι : Fin (n - k) ↪ Fin n) {S T : Scheme.{u}} (f : T ⟶ S)
    (x : (functor.{u} k n).obj (op S))
    (hx : coordinateChartCondition k n ι S x) :
    coordinateChartCondition k n ι T
      ((functor.{u} k n).map f.op x) := by
  obtain ⟨q, hq, hqepi⟩ := hx
  let e := (functorData.{u} k n).objEquiv S
  have hx' : x = e.symm ⟦q⟧ := e.injective (by simpa using hq)
  subst x
  obtain ⟨q', hq', ⟨e, he⟩⟩ :=
    (functorData.{u} k n).map_isPullback f q
  refine ⟨q', hq', ?_⟩
  have hp := pullback_preserves_epi f _ hqepi
  have he' : (Scheme.Modules.pullback f).map q.map ≫ e.hom =
      (pullbackFreeIso f n).hom ≫ q'.map := he
  have hnat' := coordinateSubmap_pullback_naturality f k n ι
  have hcomp : Epi
      ((Scheme.Modules.pullback f).map (coordinateSubmap S k n ι) ≫
        ((Scheme.Modules.pullback f).map q.map ≫ e.hom)) := by
    let : Epi e.hom := inferInstance
    have hmapcomp : (Scheme.Modules.pullback f).map (coordinateSubmap S k n ι) ≫
        (Scheme.Modules.pullback f).map q.map =
        (Scheme.Modules.pullback f).map (coordinateSubmap S k n ι ≫ q.map) := by
      simp only [Functor.map_comp]
    have : Epi ((Scheme.Modules.pullback f).map (coordinateSubmap S k n ι) ≫
        (Scheme.Modules.pullback f).map q.map) := hmapcomp ▸ hp
    exact epi_comp
      ((Scheme.Modules.pullback f).map (coordinateSubmap S k n ι) ≫
        (Scheme.Modules.pullback f).map q.map) e.hom
  have heq :
      (Scheme.Modules.pullback f).map (coordinateSubmap S k n ι) ≫
        ((Scheme.Modules.pullback f).map q.map ≫ e.hom) =
        (pullbackFreeIso f (n - k)).hom ≫
          (coordinateSubmap T k n ι ≫ q'.map) := by
    calc
      _ = ((Scheme.Modules.pullback f).map (coordinateSubmap S k n ι) ≫
          (Scheme.Modules.pullback f).map q.map) ≫ e.hom := by simp [Category.assoc]
      _ = (Scheme.Modules.pullback f).map (coordinateSubmap S k n ι) ≫
          ((Scheme.Modules.pullback f).map q.map ≫ e.hom) := by simp [Category.assoc]
      _ = (Scheme.Modules.pullback f).map (coordinateSubmap S k n ι) ≫
          ((pullbackFreeIso f n).hom ≫ q'.map) := by rw [he']
      _ = ((pullbackFreeIso f (n - k)).hom ≫ coordinateSubmap T k n ι) ≫ q'.map := by
        simpa only [← Category.assoc] using
          congrArg (fun g => g ≫ q'.map) hnat'
      _ = (pullbackFreeIso f (n - k)).hom ≫
          (coordinateSubmap T k n ι ≫ q'.map) := by simp [Category.assoc]
  have hright : Epi
      ((pullbackFreeIso f (n - k)).hom ≫
        (coordinateSubmap T k n ι ≫ q'.map)) := by
    rw [← heq]
    exact hcomp
  have : Epi (pullbackFreeIso f (n - k)).hom := inferInstance
  rw [epi_comp_iff_of_epi] at hright
  exact hright

/-- The chart subfunctor of `G(k, n)` attached to an embedding `ι`. -/
private def coordinateChartSubfunctor (k n : ℕ) (ι : Fin (n - k) ↪ Fin n) :
    Subfunctor (functor.{u} k n) where
  obj X := coordinateChartCondition k n ι X.unop
  map {_S _T} f x hx := coordinateChartCondition_map k n ι f.unop x hx


/-- A normalised quotient: a map onto the free module of rank `n - k` splitting the coordinate
inclusion indexed by `ι`. -/
private abbrev NormalizedQuotient (X : Scheme.{u}) (k n : ℕ)
    (ι : Fin (n - k) ↪ Fin n) :=
  {p : SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u} (Fin n)) ⟶
      SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u} (Fin (n - k))) //
    coordinateSubmap X k n ι ≫ p = 𝟙 _}

/-- The quotient presentation underlying a normalised quotient. -/
private noncomputable def normalizedQuotientPresentation (X : Scheme.{u}) (k n : ℕ)
    (ι : Fin (n - k) ↪ Fin n) (p : NormalizedQuotient X k n ι) :
    QuotientPresentation X k n where
  target := SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u} (Fin (n - k)))
  map := p.1
  map_epi := by
    have : Epi (coordinateSubmap X k n ι ≫ p.1) := p.2.symm ▸ inferInstance
    exact epi_of_epi (coordinateSubmap X k n ι) p.1
  finiteLocallyFree := free_isFiniteLocallyFreeOfRank X (n - k)

/-- The point of the chart subfunctor determined by a normalised quotient. -/
private noncomputable def normalizedQuotientPoint (X : Scheme.{u}) (k n : ℕ)
    (ι : Fin (n - k) ↪ Fin n) (p : NormalizedQuotient X k n ι) :
    (coordinateChartSubfunctor.{u} k n ι).obj (op X) := by
  let q := normalizedQuotientPresentation X k n ι p
  let e := (functorData.{u} k n).objEquiv X
  refine ⟨e.symm ⟦q⟧, q, e.apply_symm_apply _, ?_⟩
  change Epi (coordinateSubmap X k n ι ≫ p.1)
  rw [p.2]
  infer_instance

/-- Normalised quotients are exactly the points of the chart subfunctor. -/
private lemma normalizedQuotientPoint_bijective (X : Scheme.{u}) (k n : ℕ)
    (ι : Fin (n - k) ↪ Fin n) :
    Function.Bijective (normalizedQuotientPoint X k n ι) := by
  constructor
  · intro p p' h
    have hclass := congrArg
      (fun x => (functorData.{u} k n).objEquiv X x.1) h
    simp only [normalizedQuotientPoint, Equiv.apply_symm_apply] at hclass
    obtain ⟨e, he⟩ := quotientPresentation_isomorphic_of_eq hclass
    change SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u} (Fin (n - k))) ≅
      SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u} (Fin (n - k))) at e
    change p.1 ≫ e.hom = p'.1 at he
    have heid : e.hom = 𝟙 _ := by
      have h := congrArg (fun f => coordinateSubmap X k n ι ≫ f) he
      simpa only [← Category.assoc, p.2, p'.2, Category.id_comp] using h
    apply Subtype.ext
    simpa only [heid, Category.comp_id] using he
  · rintro ⟨x, q, hq, h⟩
    let e := coordinateChartNormalizationIso X k n ι q h
    let p : NormalizedQuotient X k n ι :=
      ⟨q.map ≫ e.hom, coordinateChartNormalizationIso_comp X k n ι q h⟩
    refine ⟨p, Subtype.ext ?_⟩
    apply ((functorData.{u} k n).objEquiv X).injective
    show _ = (functorData.{u} k n).objEquiv X x
    rw [hq]
    simp only [normalizedQuotientPoint, Equiv.apply_symm_apply]
    apply Quotient.sound
    apply Relation.EqvGen.symm
    exact Relation.EqvGen.rel _ _ ⟨e, rfl⟩

/-- The bijection between normalised quotients and points of the chart subfunctor. -/
private noncomputable def normalizedQuotientEquivChart (X : Scheme.{u}) (k n : ℕ)
    (ι : Fin (n - k) ↪ Fin n) :
    NormalizedQuotient X k n ι ≃ (coordinateChartSubfunctor.{u} k n ι).obj (op X) :=
  Equiv.ofBijective _ (normalizedQuotientPoint_bijective X k n ι)

/-- Two presentations obtained from the same one by pullback along the same morphism are
isomorphic. -/
private lemma quotientPresentation_isomorphic_of_isPullback {S T : Scheme.{u}}
    {k n : ℕ} {f : T ⟶ S} {q : QuotientPresentation S k n}
    {q₁ q₂ : QuotientPresentation T k n}
    (h₁ : q.IsPullback f q₁) (h₂ : q.IsPullback f q₂) : q₁.Isomorphic q₂ := by
  obtain ⟨e₁, h₁⟩ := h₁
  obtain ⟨e₂, h₂⟩ := h₂
  refine ⟨e₁.symm ≪≫ e₂, ?_⟩
  apply (cancel_epi (pullbackFreeIso f n).hom).1
  dsimp only [Iso.trans_hom, Iso.symm_hom]
  rw [← Category.assoc, ← h₁]
  simp only [Category.assoc, Iso.hom_inv_id_assoc, h₂]

/-- The map of `G(k, n)` induced by a morphism of schemes sends the class of a presentation to
the class of any presentation obtained from it by pullback. -/
private lemma points_map_of_isPullback {S T : Scheme.{u}} {k n : ℕ}
    (f : T ⟶ S) (q : QuotientPresentation S k n)
    (q' : QuotientPresentation T k n) (h : q.IsPullback f q') :
    (functorData.{u} k n).objEquiv T
      ((functor.{u} k n).map f.op
        (((functorData.{u} k n).objEquiv S).symm ⟦q⟧)) = ⟦q'⟧ := by
  obtain ⟨q'', hq'', hh⟩ :=
    (functorData.{u} k n).map_isPullback f q
  exact hq''.trans
    (Quotient.sound (.rel _ _ (quotientPresentation_isomorphic_of_isPullback hh h)))

/-- The pullback of a normalised quotient along a morphism of schemes. -/
private noncomputable def normalizedQuotientPullback {S T : Scheme.{u}} (f : T ⟶ S)
    (k n : ℕ) (ι : Fin (n - k) ↪ Fin n) (p : NormalizedQuotient S k n ι) :
    NormalizedQuotient T k n ι := by
  refine ⟨(pullbackFreeIso f n).inv ≫
    (Scheme.Modules.pullback f).map p.1 ≫ (pullbackFreeIso f (n - k)).hom, ?_⟩
  apply (cancel_epi (pullbackFreeIso f (n - k)).hom).1
  rw [← Category.assoc, ← coordinateSubmap_pullback_naturality f k n ι]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [← Functor.map_comp_assoc, p.2, CategoryTheory.Functor.map_id,
    Category.id_comp, Category.comp_id]

/-- The presentation underlying the pullback of a normalised quotient is obtained by pullback
from the presentation underlying it. -/
private lemma normalizedQuotientPullback_isPullback {S T : Scheme.{u}} (f : T ⟶ S)
    (k n : ℕ) (ι : Fin (n - k) ↪ Fin n) (p : NormalizedQuotient S k n ι) :
    (normalizedQuotientPresentation S k n ι p).IsPullback f
      (normalizedQuotientPresentation T k n ι (normalizedQuotientPullback f k n ι p)) := by
  refine ⟨pullbackFreeIso f (n - k), ?_⟩
  show (Scheme.Modules.pullback f).map p.1 ≫ _ = _ ≫
    ((pullbackFreeIso f n).inv ≫ (Scheme.Modules.pullback f).map p.1 ≫ _)
  simp only [Iso.hom_inv_id_assoc]

/-- The point of the chart subfunctor attached to a normalised quotient is natural in the base
scheme. -/
private lemma normalizedQuotientPoint_naturality {S T : Scheme.{u}} (f : T ⟶ S)
    (k n : ℕ) (ι : Fin (n - k) ↪ Fin n) (p : NormalizedQuotient S k n ι) :
    ((coordinateChartSubfunctor.{u} k n ι).toFunctor.map f.op)
        (normalizedQuotientPoint S k n ι p) =
      normalizedQuotientPoint T k n ι (normalizedQuotientPullback f k n ι p) := by
  apply Subtype.ext
  apply ((functorData.{u} k n).objEquiv T).injective
  show (functorData.{u} k n).objEquiv T
    ((functor.{u} k n).map f.op
      (((functorData.{u} k n).objEquiv S).symm
        ⟦normalizedQuotientPresentation S k n ι p⟧)) = _
  rw [points_map_of_isPullback f _ _
    (normalizedQuotientPullback_isPullback f k n ι p)]
  exact (((functorData.{u} k n).objEquiv T).apply_symm_apply _).symm

/-- A function on `J` whose values on the range of an embedding `ι : I ↪ J` are prescribed by
`s : I → A` is the same thing as a function on the complement of that range. -/
private noncomputable def extensionEquiv {I J A : Type*} (ι : I ↪ J) (s : I → A) :
    {f : J → A // ∀ i, f (ι i) = s i} ≃ ({j // j ∉ Set.range ι} → A) := by
  classical
  refine
    { toFun := fun f j => f.1 j.1
      invFun := fun a => ⟨fun j => if h : j ∈ Set.range ι then
        s ((Equiv.ofInjective _ ι.injective).symm ⟨j, h⟩) else a ⟨j, h⟩, ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · intro i
    exact (dite_eq_left (Set.mem_range_self i)).trans
      (congrArg s (ι.injective
        (Equiv.apply_ofInjective_symm ι.injective ⟨ι i, Set.mem_range_self i⟩)))
  · intro f
    apply Subtype.ext
    funext j
    dsimp
    split_ifs with h
    · exact (f.2 _).symm.trans
        (congrArg f.1 (Equiv.apply_ofInjective_symm ι.injective ⟨j, h⟩))
    · rfl
  · intro a
    funext j
    exact dite_eq_right j.2

/-- A normalised quotient is determined by the images of the basis vectors outside the range
of `ι`. -/
private noncomputable def normalizedQuotientEquivSections (X : Scheme.{u}) (k n : ℕ)
    (ι : Fin (n - k) ↪ Fin n) :
    NormalizedQuotient X k n ι ≃
      ({j // j ∉ Set.range ι} →
        (SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u} (Fin (n - k)))).sections) := by
  let M := SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u} (Fin (n - k)))
  let e : (SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u} (Fin n)) ⟶ M) ≃
      (Fin n → M.sections) :=
    M.freeHomEquiv.trans (Equiv.arrowCongr Equiv.ulift (Equiv.refl _))
  have h (p : SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u} (Fin n)) ⟶ M) :
      coordinateSubmap X k n ι ≫ p = 𝟙 _ ↔
        ∀ i, e p (ι i) = SheafOfModules.freeSection (ULift.up i) := by
    have eval (i : Fin (n - k)) :
        M.freeHomEquiv (coordinateSubmap X k n ι ≫ p) (ULift.up i) = e p (ι i) := by
      simp only [coordinateSubmap, SheafOfModules.freeHomEquiv_comp_apply,
        SheafOfModules.freeHomEquiv_freeMap, Function.comp_apply]
      rfl
    constructor
    · intro hp i
      rw [← eval i, hp]
    · intro hp
      apply M.freeHomEquiv.injective
      funext i
      obtain ⟨i⟩ := i
      rw [eval i, hp i]
  exact (Equiv.subtypeEquiv e h).trans
    (extensionEquiv ι (fun i => SheafOfModules.freeSection (R := X.ringCatSheaf) (ULift.up i)))

/-- The sections of the structure sheaf viewed as a module are the global sections of the
structure sheaf. -/
private noncomputable def unitSectionsEquiv (X : Scheme.{u}) :
    (SheafOfModules.unit X.ringCatSheaf).sections ≃ Γ(X, ⊤) where
  toFun s := s.1 (op ⊤)
  invFun s := PresheafOfModules.sectionsMk
    (fun U => X.presheaf.map (homOfLE (show U.unop ≤ ⊤ from le_top)).op s)
    (by
      intro U V f
      change X.presheaf.map f _ = _
      rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
      rfl)
  left_inv s := by
    apply PresheafOfModules.sections_ext
    intro U
    exact s.2 (homOfLE (show U.unop ≤ ⊤ from le_top)).op
  right_inv s := by
    change X.presheaf.map (𝟙 (op ⊤)) s = s
    simp

/-- The free module of rank `m` as a biproduct of `m` copies of the structure sheaf. -/
private noncomputable def freeBicone (X : Scheme.{u}) (m : ℕ) :
    Bicone (fun _ : ULift.{u} (Fin m) => SheafOfModules.unit X.ringCatSheaf) :=
  Bicone.ofColimitCocone (SheafOfModules.isColimitFreeCofan (R := X.ringCatSheaf)
    (ULift.{u} (Fin m)))

/-- The projections of that biproduct are the coordinate projections of the free module. -/
private lemma freeBicone_π (X : Scheme.{u}) (m : ℕ) (i : ULift.{u} (Fin m)) :
    (freeBicone X m).π i = SheafOfModules.freeProjection (R := X.ringCatSheaf) i := by
  classical
  refine Cofan.IsColimit.hom_ext
    (SheafOfModules.isColimitFreeCofan (R := X.ringCatSheaf) (ULift.{u} (Fin m))) _ _ fun j ↦ ?_
  show (freeBicone X m).ι j ≫ (freeBicone X m).π i =
    SheafOfModules.ιFree (R := X.ringCatSheaf) j ≫
      SheafOfModules.freeProjection (R := X.ringCatSheaf) i
  have h := (freeBicone X m).ι_π j i
  by_cases hji : j = i
  · subst j
    rw [SheafOfModules.ιFree_comp_freeProjection_self]
    simpa only [dite_true, eqToHom_refl] using h
  · rw [SheafOfModules.ιFree_comp_freeProjection_of_ne hji]
    simpa only [hji, dite_false] using h

/-- On the `j`-th summand the `i`-th projection of the free module is the identity if `j = i`
and zero otherwise. -/
private lemma ιFree_freeProjection (X : Scheme.{u}) (m : ℕ) (i j : Fin m) :
    SheafOfModules.ιFree (R := X.ringCatSheaf) (ULift.up j) ≫
        SheafOfModules.freeProjection (R := X.ringCatSheaf) (ULift.up i) =
      if j = i then 𝟙 _ else 0 := by
  classical
  rw [SheafOfModules.ιFree_comp_freeProjection]
  exact if_congr ULift.up_inj rfl rfl

/-- Morphisms into the apex of a limit fan are families of morphisms into its legs. -/
private noncomputable def homFanEquiv {C : Type*} [Category C]
    {I : Type*} {F : I → C} (c : Fan F) (hc : IsLimit c) (A : C) :
    (A ⟶ c.pt) ≃ (∀ i, A ⟶ F i) where
  toFun f i := f ≫ c.proj i
  invFun p := hc.lift (Fan.mk A p)
  left_inv f := hc.hom_ext (fun ⟨i⟩ => by simp; rfl)
  right_inv f := by funext i; simp

/-- The sections of the free module of rank `m` are the `m`-tuples of global sections of the
structure sheaf. -/
private noncomputable def freeSectionsEquiv (X : Scheme.{u}) (m : ℕ) :
    (SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u} (Fin m))).sections ≃
      (Fin m → Γ(X, ⊤)) := by
  let U := SheafOfModules.unit X.ringCatSheaf
  let b := freeBicone X m
  let hb := biconeIsBilimitOfColimitCoconeOfIsColimit
    (SheafOfModules.isColimitFreeCofan (R := X.ringCatSheaf) (ULift.{u} (Fin m)))
  exact (SheafOfModules.unitHomEquiv _).symm.trans
    ((homFanEquiv b.toCone hb.isLimit U).trans
      (Equiv.arrowCongr Equiv.ulift
        ((SheafOfModules.unitHomEquiv U).trans (unitSectionsEquiv X))))

/-- The `i`-th coordinate of a section of the free module is its image under the `i`-th
projection. -/
private lemma freeSectionsEquiv_unitHom_apply (X : Scheme.{u}) (m : ℕ)
    (s : SheafOfModules.unit X.ringCatSheaf ⟶
      SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u} (Fin m))) (i : Fin m) :
    freeSectionsEquiv X m ((SheafOfModules.free (R := X.ringCatSheaf)
      (ULift.{u} (Fin m))).unitHomEquiv s) i =
    unitSectionsEquiv X ((SheafOfModules.unit X.ringCatSheaf).unitHomEquiv
      (s ≫ SheafOfModules.freeProjection (R := X.ringCatSheaf) (ULift.up i))) := by
  rw [← freeBicone_π X m (ULift.up i)]
  show unitSectionsEquiv X ((SheafOfModules.unit X.ringCatSheaf).unitHomEquiv
    (((SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u} (Fin m))).unitHomEquiv.symm
      ((SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u} (Fin m))).unitHomEquiv s)) ≫
        (freeBicone X m).π (ULift.up i))) = _
  rw [Equiv.symm_apply_apply]

section

attribute [local instance 10000] CategoryTheory.CategoryStruct.toQuiver

/- `Scheme.Modules.pullbackUnitIso` is stated at the type `Scheme.unitModule X`, while the
free-module machinery used here is stated at the corresponding
`CategoryTheory.SheafOfModules` type.  The two descriptions are definitionally equal, but not
at the transparency at which `rw` and `simp` check that a goal is type-correct, so
`Scheme.unitModule` is made `implicit_reducible` locally. -/
attribute [local implicit_reducible] AlgebraicGeometry.Scheme.unitModule

/-- Transporting an endomorphism of the structure sheaf along pullback computes its sections as
the pullback of its sections. -/
private lemma pullback_unitHom_sections {S T : Scheme.{u}} (f : T ⟶ S)
    (s : SheafOfModules.unit S.ringCatSheaf ⟶ SheafOfModules.unit S.ringCatSheaf) :
    SheafOfModules.pushforwardSections f.toRingCatSheafHom
      ((SheafOfModules.unit T.ringCatSheaf).unitHomEquiv
        ((Scheme.Modules.pullbackUnitIso f).inv ≫ (Scheme.Modules.pullback f).map s ≫
          (Scheme.Modules.pullbackUnitIso f).hom)) =
    SheafOfModules.sectionsMap (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom)
      ((SheafOfModules.unit S.ringCatSheaf).unitHomEquiv s) := by
  obtain ⟨_, _⟩ := pullback_instances f
  let adj := Scheme.Modules.pullbackPushforwardAdjunction f
  let t := (Scheme.Modules.pullbackUnitIso f).inv ≫ (Scheme.Modules.pullback f).map s ≫
    (Scheme.Modules.pullbackUnitIso f).hom
  have key := SheafOfModules.pushforwardSections_unitHomEquiv
    (M := SheafOfModules.unit T.ringCatSheaf) f.toRingCatSheafHom t
  rw [key, ← SheafOfModules.unitHomEquiv_comp_apply]
  congr 1
  have he : adj.homEquiv _ _ (Scheme.Modules.pullbackUnitIso f).hom =
      SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom :=
    SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit _
  calc
    _ = adj.homEquiv (Scheme.unitModule S) (Scheme.unitModule T)
        ((Scheme.Modules.pullbackUnitIso f).hom ≫ t) := by
      rw [adj.homEquiv_naturality_right, he]
      rfl
    _ = adj.homEquiv (Scheme.unitModule S) (Scheme.unitModule T)
        ((Scheme.Modules.pullback f).map s ≫
          (Scheme.Modules.pullbackUnitIso f).hom) := by
      simp only [t, Iso.hom_inv_id_assoc]
    _ = _ := by
      rw [adj.homEquiv_naturality_left]
      exact congrArg (fun g ↦ s ≫ g) he

/-- The projections of the free module commute with pullback. -/
private lemma freeProjection_pullback {S T : Scheme.{u}} (f : T ⟶ S)
    (m : ℕ) (i : Fin m) :
    (Scheme.Modules.pullback f).map
          (SheafOfModules.freeProjection (R := S.ringCatSheaf) (ULift.up i)) ≫
        (Scheme.Modules.pullbackUnitIso f).hom =
      (pullbackFreeIso f m).hom ≫
        SheafOfModules.freeProjection (R := T.ringCatSheaf) (ULift.up i) := by
  obtain ⟨_, _⟩ := pullback_instances f
  apply Cofan.IsColimit.hom_ext
    (isColimitCofanMkObjOfIsColimit (Scheme.Modules.pullback f) _ _
      (SheafOfModules.isColimitFreeCofan (R := S.ringCatSheaf) (ULift.{u} (Fin m))))
  rintro ⟨j⟩
  show (Scheme.Modules.pullback f).map (SheafOfModules.ιFree (ULift.up j)) ≫
    ((Scheme.Modules.pullback f).map
      (SheafOfModules.freeProjection (R := S.ringCatSheaf) (ULift.up i)) ≫ _) = _
  rw [← Category.assoc, ← CategoryTheory.Functor.map_comp, ιFree_freeProjection]
  show _ = (Scheme.Modules.pullback f).map (SheafOfModules.ιFree (ULift.up j)) ≫
    ((SheafOfModules.pullbackObjFreeIso f.toRingCatSheafHom (ULift.{u} (Fin m))).hom ≫ _)
  have h := SheafOfModules.pullback_map_ιFree_comp_pullbackObjFreeIso_hom
    f.toRingCatSheafHom (ULift.up j : ULift.{u} (Fin m))
  have h' := congrArg
    (fun a => a ≫ SheafOfModules.freeProjection (R := T.ringCatSheaf) (ULift.up i)) h
  rw [← Category.assoc]
  refine Eq.trans ?_ h'.symm
  rw [Category.assoc, ιFree_freeProjection]
  by_cases hji : j = i
  · simp [hji, Scheme.Modules.pullbackUnitIso]
  · have hz : (Scheme.Modules.pullback f).map
        (0 : SheafOfModules.unit S.ringCatSheaf ⟶ SheafOfModules.unit S.ringCatSheaf) = 0 :=
      (Scheme.Modules.pullback f).map_zero _ _
    simp only [hji, if_false, hz, Limits.zero_comp]
    rfl

/-- The global section attached to an endomorphism of the structure sheaf pulls back to the
pullback of that section. -/
private lemma unitEnd_pullback_global {S T : Scheme.{u}} (f : T ⟶ S)
    (s : SheafOfModules.unit S.ringCatSheaf ⟶ SheafOfModules.unit S.ringCatSheaf) :
    unitSectionsEquiv T ((SheafOfModules.unit T.ringCatSheaf).unitHomEquiv
      ((Scheme.Modules.pullbackUnitIso f).inv ≫ (Scheme.Modules.pullback f).map s ≫
        (Scheme.Modules.pullbackUnitIso f).hom)) =
      f.appTop (unitSectionsEquiv S ((SheafOfModules.unit S.ringCatSheaf).unitHomEquiv s)) :=
  congrArg (fun t => t.1 (op ⊤)) (pullback_unitHom_sections f s)

/-- The coordinates of a section of the free module pull back coordinatewise. -/
private lemma freeSectionsEquiv_pullback {S T : Scheme.{u}} (f : T ⟶ S) (m : ℕ)
    (s : SheafOfModules.unit S.ringCatSheaf ⟶
      SheafOfModules.free (R := S.ringCatSheaf) (ULift.{u} (Fin m))) (i : Fin m) :
    freeSectionsEquiv T m ((SheafOfModules.free (R := T.ringCatSheaf)
      (ULift.{u} (Fin m))).unitHomEquiv
        ((Scheme.Modules.pullbackUnitIso f).inv ≫ (Scheme.Modules.pullback f).map s ≫
          (pullbackFreeIso f m).hom)) i =
    f.appTop (freeSectionsEquiv S m ((SheafOfModules.free (R := S.ringCatSheaf)
      (ULift.{u} (Fin m))).unitHomEquiv s) i) := by
  rw [freeSectionsEquiv_unitHom_apply, freeSectionsEquiv_unitHom_apply]
  simp only [Category.assoc]
  rw [← freeProjection_pullback f m i, ← CategoryTheory.Functor.map_comp_assoc]
  exact unitEnd_pullback_global f
    (s ≫ SheafOfModules.freeProjection (R := S.ringCatSheaf) (ULift.up i))

/-- The coefficients of a normalised quotient pull back coordinatewise. -/
private lemma normalizedQuotient_coefficients_pullback {S T : Scheme.{u}}
    (f : T ⟶ S) (k n : ℕ) (ι : Fin (n - k) ↪ Fin n)
    (p : NormalizedQuotient S k n ι) (j : {j // j ∉ Set.range ι}) (i : Fin (n - k)) :
    freeSectionsEquiv T (n - k)
      (normalizedQuotientEquivSections T k n ι (normalizedQuotientPullback f k n ι p) j) i =
    f.appTop (freeSectionsEquiv S (n - k)
      (normalizedQuotientEquivSections S k n ι p j) i) := by
  obtain ⟨_, _⟩ := pullback_instances f
  have h := SheafOfModules.pullback_map_ιFree_comp_pullbackObjFreeIso_hom
    f.toRingCatSheafHom (ULift.up j.1 : ULift.{u} (Fin n))
  have hh : SheafOfModules.ιFree (R := T.ringCatSheaf) (ULift.up j.1) ≫
      (pullbackFreeIso f n).inv = (Scheme.Modules.pullbackUnitIso f).inv ≫
        (Scheme.Modules.pullback f).map (SheafOfModules.ιFree (ULift.up j.1)) := by
    apply (cancel_epi (Scheme.Modules.pullbackUnitIso f).hom).1
    apply (cancel_mono (pullbackFreeIso f n).hom).1
    simpa only [Category.assoc, Iso.hom_inv_id_assoc, Iso.inv_hom_id,
      Category.comp_id, Scheme.Modules.pullbackUnitIso, pullbackFreeIso,
      asIso_hom, asIso_inv, Scheme.Modules.pullback,
      IsIso.hom_inv_id_assoc] using h.symm
  show freeSectionsEquiv T (n - k) ((SheafOfModules.free (R := T.ringCatSheaf)
    (ULift.{u} (Fin (n - k)))).unitHomEquiv
      (SheafOfModules.ιFree (ULift.up j.1) ≫ (pullbackFreeIso f n).inv ≫
        (Scheme.Modules.pullback f).map p.1 ≫ (pullbackFreeIso f (n - k)).hom)) i = _
  rw [← Category.assoc _ (pullbackFreeIso f n).inv, hh]
  simp only [Category.assoc]
  rw [← CategoryTheory.Functor.map_comp_assoc]
  exact freeSectionsEquiv_pullback f (n - k) (SheafOfModules.ιFree (ULift.up j.1) ≫ p.1) i

end

/-- The coordinates on the chart attached to an embedding `ι`: for each basis vector of the
free module of rank `n` outside the range of `ι`, its `n - k` coordinates in the normalised
quotient. -/
private abbrev ChartCoordinates {k n : ℕ} (ι : Fin (n - k) ↪ Fin n) :=
  ULift.{u} ({j // j ∉ Set.range ι} × Fin (n - k))

/-- The affine space over `Spec ℤ` on the chart coordinates. -/
private noncomputable abbrev coordinateChartScheme {k n : ℕ}
    (ι : Fin (n - k) ↪ Fin n) : Scheme.{u} :=
  Spec (.of (MvPolynomial (ChartCoordinates.{u} ι) (ULift.{u} ℤ)))

/-- A normalised quotient on `X` is the same thing as a matrix of global sections of `X`
indexed by the chart coordinates. -/
private noncomputable def normalizedQuotientCoefficientsEquiv (X : Scheme.{u}) (k n : ℕ)
    (ι : Fin (n - k) ↪ Fin n) :
    NormalizedQuotient X k n ι ≃ (ChartCoordinates.{u} ι → Γ(X, ⊤)) :=
  (normalizedQuotientEquivSections X k n ι).trans
    ((Equiv.arrowCongr (Equiv.refl _) (freeSectionsEquiv X (n - k))).trans
      ((Equiv.curry _ _ _).symm.trans (Equiv.arrowCongr Equiv.ulift.symm (Equiv.refl _))))

/-- Pulling back a normalised quotient pulls back each of its coefficients. -/
private lemma normalizedQuotientCoefficientsEquiv_pullback {S T : Scheme.{u}} (f : T ⟶ S)
    (k n : ℕ) (ι : Fin (n - k) ↪ Fin n) (p : NormalizedQuotient S k n ι)
    (a : ChartCoordinates.{u} ι) :
    normalizedQuotientCoefficientsEquiv T k n ι (normalizedQuotientPullback f k n ι p) a =
      f.appTop (normalizedQuotientCoefficientsEquiv S k n ι p a) := by
  obtain ⟨j, i⟩ := a
  exact normalizedQuotient_coefficients_pullback f k n ι p j i

/-- A point of the chart subfunctor over `X` is a matrix of global sections of `X`. -/
private noncomputable def chartPointsEquiv (X : Scheme.{u}) (k n : ℕ)
    (ι : Fin (n - k) ↪ Fin n) :
    (ChartCoordinates.{u} ι → Γ(X, ⊤)) ≃
      (coordinateChartSubfunctor.{u} k n ι).obj (op X) :=
  (normalizedQuotientCoefficientsEquiv X k n ι).symm.trans
    (normalizedQuotientEquivChart X k n ι)

/-- The description of the chart subfunctor by matrices of global sections is natural in the
scheme. -/
private lemma chartPointsEquiv_naturality {S T : Scheme.{u}} (f : T ⟶ S)
    (k n : ℕ) (ι : Fin (n - k) ↪ Fin n) (v : ChartCoordinates.{u} ι → Γ(S, ⊤)) :
    chartPointsEquiv T k n ι (fun a => f.appTop (v a)) =
      (coordinateChartSubfunctor.{u} k n ι).toFunctor.map f.op
        (chartPointsEquiv S k n ι v) := by
  have hp : normalizedQuotientCoefficientsEquiv T k n ι
      (normalizedQuotientPullback f k n ι
        ((normalizedQuotientCoefficientsEquiv S k n ι).symm v)) =
      fun a => f.appTop (v a) := by
    funext a
    rw [normalizedQuotientCoefficientsEquiv_pullback, Equiv.apply_symm_apply]
  have h : chartPointsEquiv T k n ι (fun a => f.appTop (v a)) =
      normalizedQuotientPoint T k n ι (normalizedQuotientPullback f k n ι
        ((normalizedQuotientCoefficientsEquiv S k n ι).symm v)) := by
    show normalizedQuotientPoint T k n ι
      ((normalizedQuotientCoefficientsEquiv T k n ι).symm fun a => f.appTop (v a)) = _
    rw [← hp, Equiv.symm_apply_apply]
  rw [h]
  exact (normalizedQuotientPoint_naturality f k n ι _).symm

/-- The chart subfunctor of the Grassmannian functor is isomorphic to the functor of matrices
of global sections indexed by the chart coordinates. -/
private noncomputable def chartSubfunctorIso (k n : ℕ) (ι : Fin (n - k) ↪ Fin n) :
    _root_.Stacks.AlgebraicGeometry.GrassmannianChart.sectionsFunctor
        (ChartCoordinates.{u} ι) ≅
      (coordinateChartSubfunctor.{u} k n ι).toFunctor :=
  NatIso.ofComponents (fun X => (chartPointsEquiv X.unop k n ι).toIso) (by
    intro X Y f
    apply TypeCat.homEquiv.injective
    funext v
    exact chartPointsEquiv_naturality f.unop k n ι v)

/-- The chart subfunctor is representable by the affine space on the chart coordinates. -/
private noncomputable def coordinateChartRepresentableBy (k n : ℕ)
    (ι : Fin (n - k) ↪ Fin n) :
    (coordinateChartSubfunctor.{u} k n ι).toFunctor.RepresentableBy
      (coordinateChartScheme.{u} ι) :=
  (_root_.Stacks.AlgebraicGeometry.GrassmannianChart.sectionsRepresentableBy
    (ChartCoordinates.{u} ι)).ofIso (chartSubfunctorIso k n ι)

/-- The bijection between morphisms into the chart and points of the chart subfunctor. -/
private noncomputable def coordinateChartPointsEquiv (X : Scheme.{u}) (k n : ℕ)
    (ι : Fin (n - k) ↪ Fin n) :
    (X ⟶ coordinateChartScheme.{u} ι) ≃
      (coordinateChartSubfunctor.{u} k n ι).obj (op X) :=
  (coordinateChartRepresentableBy k n ι).homEquiv

/-- The bijection of `coordinateChartPointsEquiv` is natural in the scheme. -/
private lemma coordinateChartPointsEquiv_naturality {S T : Scheme.{u}} (f : T ⟶ S)
    (k n : ℕ) (ι : Fin (n - k) ↪ Fin n) (g : S ⟶ coordinateChartScheme.{u} ι) :
    coordinateChartPointsEquiv T k n ι (f ≫ g) =
      (coordinateChartSubfunctor.{u} k n ι).toFunctor.map f.op
        (coordinateChartPointsEquiv S k n ι g) :=
  (coordinateChartRepresentableBy k n ι).homEquiv_comp f g

end AlgebraicGeometry.Grassmannian

end
