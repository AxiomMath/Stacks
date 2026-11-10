module

public import StacksFrontier.AlgebraicGeometry.ProjectiveFromSections.FreePresentation
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpaceModuli.Basic
public import StacksFrontier.AlgebraicGeometry.Recovery27.GrassmannianScheme
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Projective space is the Grassmannian of hyperplanes

Stacks Tag 089V: the Grassmannian `G(n, n + 1)` over the integers is canonically isomorphic to
projective `n`-space `ℙⁿ_ℤ`. Both schemes represent the same functor on schemes:

* `G(n, n + 1)` represents the functor of finite locally free rank-one quotients of the free
  module of rank `n + 1` (Stacks Tag 089U, `AlgebraicGeometry.Grassmannian.schemeRepresentableBy`);
* `ℙⁿ_ℤ` represents the functor of invertible modules with `n + 1` generating global sections
  (Stacks Tag 01NE, `Stacks.ProjectiveSpaceModuli.pointsEquiv`).

## Main definitions

* `Stacks.ProjectiveSpaceModuli.presentationOfTuple` and
  `Stacks.ProjectiveSpaceModuli.tupleOfPresentation`: the two directions of the dictionary.
* `Stacks.ProjectiveSpaceModuli.pointsBridge`: the resulting bijection on isomorphism classes.
* `Stacks.ProjectiveSpaceModuli.projectiveSpaceRepresentableBy`: projective `n`-space represents
  the Grassmannian functor `G(n, n + 1)`.

## Main results

* `Stacks.ProjectiveSpaceModuli.grassmannianSuccIso`: **Tag 089V**, the isomorphism
  `G(n, n + 1) ≅ ℙⁿ_ℤ`.
* `Stacks.ProjectiveSpaceModuli.homEquiv_comp_grassmannianSuccIso_hom`: **Tag 089V**, the
  isomorphism is the canonical one — it matches the two representations, so composing with it
  sends a rank-one quotient to the invertible module with `n + 1` generating sections that the
  dictionary attaches to it.

## Implementation notes

A generating tuple `(L, (s₀, …, sₙ))` goes to the quotient presentation
`SheafOfModules.freeHomEquiv.symm s : free (ULift (Fin (n + 1))) ⟶ L`; the inverse reads off the
images of the standard basis sections. The statements hold for every `n`, without the bound
`n ≥ 1` of the source.

## References

* [Stacks Project, Tag 089V](https://stacks.math.columbia.edu/tag/089V)
* [Stacks Project, Tag 089U](https://stacks.math.columbia.edu/tag/089U)
* [Stacks Project, Tag 089S](https://stacks.math.columbia.edu/tag/089S)
* [Stacks Project, Tag 01NE](https://stacks.math.columbia.edu/tag/01NE)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace Stacks.ProjectiveSpaceModuli

attribute [local implicit_reducible] AlgebraicGeometry.Scheme.Modules
attribute [local implicit_reducible] AlgebraicGeometry.Scheme.Modules.Hom
attribute [local implicit_reducible] AlgebraicGeometry.Scheme.Modules.pullback
attribute [local implicit_reducible] AlgebraicGeometry.projectiveSpaceAtUniverse
attribute [local implicit_reducible] TopCat.Sheaf sheafCompose
attribute [local implicit_reducible] SheafOfModules.unit PresheafOfModules.unit

open Stacks.ProjectiveFromSections AlgebraicGeometry.Grassmannian

/-! ### The dictionary between generating tuples and rank-one quotient presentations -/

variable {X Y : Scheme.{u}} {n : ℕ}

/-- The rank-one quotient presentation attached to an invertible module with `n + 1` generating
global sections: the map out of the free module of rank `n + 1` given by the sections. -/
def presentationOfTuple (t : GeneratingTuple X n) : QuotientPresentation X n (n + 1) where
  target := t.bundle
  map := t.bundle.freeHomEquiv.symm
    (fun i : ULift.{u} (Fin (n + 1)) =>
      (Stacks.NonvanishingSpelling.sectionsEquiv X t.bundle).symm (t.coord i.down))
  map_epi := epi_freeHomEquiv_symm_of_generatesStalks _
    ((generatesStalks_ulift_iff t.coord).mpr t.generates)
  finiteLocallyFree := by
    rw [show n + 1 - n = 1 by lia]
    exact isFiniteLocallyFreeOfRank_one_of_isInvertibleModule t.bundle

/-- The target of the presentation of a tuple is the tuple's module. -/
@[simp] theorem presentationOfTuple_target (t : GeneratingTuple X n) :
    (presentationOfTuple t).target = t.bundle := rfl

/-- The map of the presentation of a tuple is the one given by the tuple's sections. -/
@[simp] theorem presentationOfTuple_map (t : GeneratingTuple X n) :
    (presentationOfTuple t).map = t.bundle.freeHomEquiv.symm
      (fun i : ULift.{u} (Fin (n + 1)) =>
        (Stacks.NonvanishingSpelling.sectionsEquiv X t.bundle).symm (t.coord i.down)) := rfl

/-- The invertible module with `n + 1` generating global sections attached to a rank-one quotient
presentation: the images of the standard basis sections. -/
def tupleOfPresentation (q : QuotientPresentation X n (n + 1)) : GeneratingTuple X n where
  bundle := q.target
  isInvertible := by
    have h1 : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank
        (R := X.ringCatSheaf) q.target 1 := by simpa using q.finiteLocallyFree
    exact isInvertibleModule_of_isFiniteLocallyFreeOfRank_one q.target
  coord := fun i => Stacks.NonvanishingSpelling.sectionsEquiv X q.target
    (q.target.freeHomEquiv q.map (ULift.up i))
  generates := by
    refine (generatesStalks_ulift_iff _).mp ?_
    have hfun : (fun i : ULift.{u} (Fin (n + 1)) =>
        (Stacks.NonvanishingSpelling.sectionsEquiv X q.target).symm
          (Stacks.NonvanishingSpelling.sectionsEquiv X q.target
            (q.target.freeHomEquiv q.map (ULift.up i.down)))) =
        q.target.freeHomEquiv q.map :=
      funext fun _ =>
        (Stacks.NonvanishingSpelling.sectionsEquiv X q.target).symm_apply_apply _
    have hmap : q.target.freeHomEquiv.symm
        (fun i : ULift.{u} (Fin (n + 1)) =>
          (Stacks.NonvanishingSpelling.sectionsEquiv X q.target).symm
            (Stacks.NonvanishingSpelling.sectionsEquiv X q.target
              (q.target.freeHomEquiv q.map (ULift.up i.down)))) = q.map := by
      rw [hfun, Equiv.symm_apply_apply]
    have hepi : Epi q.map := q.map_epi
    rw [← hmap] at hepi
    exact generatesStalks_of_epi_freeHomEquiv_symm _ hepi

/-- The module of the tuple of a presentation is the presentation's target. -/
@[simp] theorem tupleOfPresentation_bundle (q : QuotientPresentation X n (n + 1)) :
    (tupleOfPresentation q).bundle = q.target := rfl

/-- The sections of the tuple of a presentation are the images of the standard basis sections. -/
@[simp] theorem tupleOfPresentation_coord (q : QuotientPresentation X n (n + 1))
    (i : Fin (n + 1)) :
    (tupleOfPresentation q).coord i = Stacks.NonvanishingSpelling.sectionsEquiv X q.target
      (q.target.freeHomEquiv q.map (ULift.up i)) := rfl

/-- Reading off the basis sections of a presentation and reassembling them gives its map. -/
private theorem freeHomEquiv_symm_sectionsEquiv_symm (q : QuotientPresentation X n (n + 1)) :
    q.target.freeHomEquiv.symm
        (fun i : ULift.{u} (Fin (n + 1)) =>
          (Stacks.NonvanishingSpelling.sectionsEquiv X q.target).symm
            (Stacks.NonvanishingSpelling.sectionsEquiv X q.target
              (q.target.freeHomEquiv q.map (ULift.up i.down)))) = q.map := by
  simp only [Equiv.symm_apply_apply]
  exact Equiv.symm_apply_apply _ _

/-- The presentation of the tuple of a presentation has the same map. -/
theorem presentationOfTuple_tupleOfPresentation_map (q : QuotientPresentation X n (n + 1)) :
    (presentationOfTuple (tupleOfPresentation q)).map = q.map := by
  rw [presentationOfTuple_map]
  exact freeHomEquiv_symm_sectionsEquiv_symm q

/-- The tuple of the presentation of a tuple has the same sections. -/
theorem tupleOfPresentation_presentationOfTuple_coord (t : GeneratingTuple X n)
    (i : Fin (n + 1)) :
    (tupleOfPresentation (presentationOfTuple t)).coord i = t.coord i := by
  change Stacks.NonvanishingSpelling.sectionsEquiv X t.bundle
      (t.bundle.freeHomEquiv (t.bundle.freeHomEquiv.symm
        (fun j : ULift.{u} (Fin (n + 1)) =>
          (Stacks.NonvanishingSpelling.sectionsEquiv X t.bundle).symm (t.coord j.down)))
        (ULift.up i)) = t.coord i
  rw [Equiv.apply_symm_apply]
  exact (Stacks.NonvanishingSpelling.sectionsEquiv X t.bundle).apply_symm_apply (t.coord i)

/-! ### The two equivalence relations correspond -/

/-- Isomorphism of quotient presentations is already an equivalence relation, so the relation it
generates is itself. -/
theorem eqvGen_isomorphic_iff {q q' : QuotientPresentation X n (n + 1)} :
    Relation.EqvGen QuotientPresentation.Isomorphic q q' ↔ q.Isomorphic q' := by
  refine ⟨fun h => ?_, Relation.EqvGen.rel _ _⟩
  induction h with
  | rel _ _ h => exact h
  | refl a => exact ⟨Iso.refl _, Category.comp_id _⟩
  | symm a b _ ih =>
      obtain ⟨e, he⟩ := ih
      refine ⟨e.symm, ?_⟩
      rw [Iso.symm_hom, ← he, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  | trans a b c _ _ ih₁ ih₂ =>
      obtain ⟨e, he⟩ := ih₁
      obtain ⟨f, hf⟩ := ih₂
      refine ⟨e.trans f, ?_⟩
      rw [← hf, ← he, Iso.trans_hom]
      exact (Category.assoc _ _ _).symm

/-- An isomorphism of tuples gives an isomorphism of the associated presentations. -/
theorem isomorphic_presentationOfTuple {t t' : GeneratingTuple X n} (h : Isomorphic t t') :
    (presentationOfTuple t).Isomorphic (presentationOfTuple t') := by
  obtain ⟨β, hβ⟩ := h
  refine ⟨β, ?_⟩
  refine Eq.trans (SheafOfModules.freeHomEquiv_symm_comp _ β.hom) ?_
  refine congrArg t'.bundle.freeHomEquiv.symm (funext fun i => ?_)
  refine (Stacks.NonvanishingSpelling.sectionsEquiv X t'.bundle).injective ?_
  rw [sectionsEquiv_sectionsMap, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  exact hβ i.down

/-- An isomorphism of presentations gives an isomorphism of the associated tuples. -/
theorem isomorphic_tupleOfPresentation {q q' : QuotientPresentation X n (n + 1)}
    (h : q.Isomorphic q') : Isomorphic (tupleOfPresentation q) (tupleOfPresentation q') := by
  obtain ⟨e, he⟩ := h
  refine ⟨e, fun i => ?_⟩
  change Scheme.Modules.Hom.app e.hom ⊤
      (Stacks.NonvanishingSpelling.sectionsEquiv X q.target
        (q.target.freeHomEquiv q.map (ULift.up i))) =
    Stacks.NonvanishingSpelling.sectionsEquiv X q'.target
      (q'.target.freeHomEquiv q'.map (ULift.up i))
  rw [← he]
  exact (sectionsEquiv_sectionsMap e.hom (q.target.freeHomEquiv q.map (ULift.up i))).symm

/-! ### The bijection on points and its naturality -/

/-- The Grassmannian point of a projective-space point. -/
def toGrassPoints (X : Scheme.{u}) (n : ℕ) : Points X n → Grassmannian.Points X n (n + 1) :=
  Quotient.map presentationOfTuple fun _ _ h =>
    Relation.EqvGen.rel _ _ (isomorphic_presentationOfTuple h)

/-- The projective-space point of a Grassmannian point. -/
def ofGrassPoints (X : Scheme.{u}) (n : ℕ) : Grassmannian.Points X n (n + 1) → Points X n :=
  Quotient.map tupleOfPresentation fun _ _ h =>
    isomorphic_tupleOfPresentation (eqvGen_isomorphic_iff.mp h)

/-- The two maps on points are mutually inverse: the tuple side. -/
theorem ofGrassPoints_toGrassPoints (X : Scheme.{u}) (n : ℕ) (x : Points X n) :
    ofGrassPoints X n (toGrassPoints X n x) = x := by
  induction x using Quotient.ind with | _ t => ?_
  change (⟦tupleOfPresentation (presentationOfTuple t)⟧ : Points X n) = ⟦t⟧
  exact Quotient.sound ⟨Iso.refl t.bundle, fun i =>
    (homApp_refl t.bundle ⊤ _).trans (tupleOfPresentation_presentationOfTuple_coord t i)⟩

/-- The two maps on points are mutually inverse: the presentation side. -/
theorem toGrassPoints_ofGrassPoints (X : Scheme.{u}) (n : ℕ)
    (y : Grassmannian.Points X n (n + 1)) :
    toGrassPoints X n (ofGrassPoints X n y) = y := by
  induction y using Quotient.ind with | _ q => ?_
  change (⟦presentationOfTuple (tupleOfPresentation q)⟧ : Grassmannian.Points X n (n + 1)) = ⟦q⟧
  exact Quotient.sound (Relation.EqvGen.rel _ _ ⟨Iso.refl q.target,
    (Category.comp_id _).trans (presentationOfTuple_tupleOfPresentation_map q)⟩)

/-- **The bijection between the two moduli descriptions**: an invertible module with `n + 1`
generating global sections is the same datum as a rank-one quotient of the free module of rank
`n + 1`. -/
def pointsBridge (X : Scheme.{u}) (n : ℕ) : Points X n ≃ Grassmannian.Points X n (n + 1) where
  toFun := toGrassPoints X n
  invFun := ofGrassPoints X n
  left_inv := ofGrassPoints_toGrassPoints X n
  right_inv := toGrassPoints_ofGrassPoints X n

/-- The presentation of a pulled-back tuple is the pullback of the presentation. -/
theorem presentationOfTuple_pullbackTuple_map (h : Y ⟶ X) (t : GeneratingTuple X n) :
    (presentationOfTuple (pullbackTuple h t)).map =
      (Grassmannian.pullbackPresentation h (presentationOfTuple t)).map := by
  change ((Scheme.Modules.pullback h).obj t.bundle).freeHomEquiv.symm
      (fun i : ULift.{u} (Fin (n + 1)) =>
        (Stacks.NonvanishingSpelling.sectionsEquiv Y
          ((Scheme.Modules.pullback h).obj t.bundle)).symm
            (AlgebraicGeometry.pullbackGlobalSections h t.bundle (t.coord i.down))) =
    (AlgebraicGeometry.Grassmannian.pullbackFreeIso h (n + 1)).inv ≫
      (Scheme.Modules.pullback h).map (t.bundle.freeHomEquiv.symm
        (fun i : ULift.{u} (Fin (n + 1)) =>
          (Stacks.NonvanishingSpelling.sectionsEquiv X t.bundle).symm (t.coord i.down)))
  refine ((Scheme.Modules.pullback h).obj t.bundle).freeHomEquiv.symm_apply_eq.mpr ?_
  refine funext fun i => ?_
  refine (Stacks.NonvanishingSpelling.sectionsEquiv Y
    ((Scheme.Modules.pullback h).obj t.bundle)).injective ?_
  rw [Equiv.apply_symm_apply, freeHomEquiv_pullbackFreeIso_inv, Equiv.apply_symm_apply,
    Equiv.apply_symm_apply]

/-- The bijection is natural in the test scheme: it carries pullback of tuples to pullback of
presentations. -/
theorem toGrassPoints_pullbackPoints (h : Y ⟶ X) (x : Points X n) :
    toGrassPoints Y n (pullbackPoints h x) =
      Grassmannian.pullbackPointsMap h n (n + 1) (toGrassPoints X n x) := by
  induction x using Quotient.ind with | _ t => ?_
  change (⟦presentationOfTuple (pullbackTuple h t)⟧ : Grassmannian.Points Y n (n + 1)) =
    ⟦Grassmannian.pullbackPresentation h (presentationOfTuple t)⟧
  exact Quotient.sound (Relation.EqvGen.rel _ _
    ⟨Iso.refl ((Scheme.Modules.pullback h).obj t.bundle),
      (Category.comp_id _).trans (presentationOfTuple_pullbackTuple_map h t)⟩)

/-! ### The Grassmannian functor acts by pullback of presentations -/

/-- The moduli interpretation of the values of the Grassmannian functor, spelled with the
functor itself rather than with its construction data. -/
def grassPointsEquiv (Z : Scheme.{u}) (k N : ℕ) :
    (Grassmannian.functor.{u} k N).obj (op Z) ≃ Grassmannian.Points Z k N :=
  (Grassmannian.functorData.{u} k N).objEquiv Z

/-- A presentation obtained from a fixed one by pullback is determined up to isomorphism. -/
theorem isomorphic_of_isPullback {S T : Scheme.{u}} {k N : ℕ} {f : T ⟶ S}
    {q : QuotientPresentation S k N} {q' q'' : QuotientPresentation T k N}
    (h' : q.IsPullback f q') (h'' : q.IsPullback f q'') : q'.Isomorphic q'' := by
  obtain ⟨e', he'⟩ := h'
  obtain ⟨e'', he''⟩ := h''
  refine ⟨e'.symm.trans e'', ?_⟩
  refine (cancel_epi (Grassmannian.pullbackFreeIso f N).hom).1 ?_
  rw [Iso.trans_hom, Iso.symm_hom, ← Category.assoc, ← he', Category.assoc,
    Iso.hom_inv_id_assoc]
  exact he''

/-- Under the moduli interpretation of the Grassmannian functor, the map it associates to a
morphism of schemes is pullback of quotient presentations. -/
theorem grassPointsEquiv_functor_map {S T : Scheme.{u}} (f : T ⟶ S) (k N : ℕ)
    (y : Grassmannian.Points S k N) :
    grassPointsEquiv T k N ((Grassmannian.functor.{u} k N).map f.op
        ((grassPointsEquiv S k N).symm y)) =
      Grassmannian.pullbackPointsMap f k N y := by
  induction y using Quotient.ind with | _ q => ?_
  obtain ⟨q', hq', hpb⟩ := (Grassmannian.functorData.{u} k N).map_isPullback f q
  have hq'' : grassPointsEquiv T k N ((Grassmannian.functor.{u} k N).map f.op
      ((grassPointsEquiv S k N).symm ⟦q⟧)) = ⟦q'⟧ := hq'
  rw [hq'']
  exact Quotient.sound (Relation.EqvGen.rel _ _
    (isomorphic_of_isPullback hpb (Grassmannian.pullbackPresentation_isPullback f q)))

/-! ### Projective space represents the Grassmannian functor -/

/-- **Projective `n`-space represents the Grassmannian functor `G(n, n + 1)`**, through the
bijection between invertible modules with `n + 1` generating global sections and rank-one
quotients of the free module of rank `n + 1`. -/
@[sga "7 XII 1.1" "special case"]
def projectiveSpaceRepresentableBy (n : ℕ) :
    (Grassmannian.functor.{u} n (n + 1)).RepresentableBy (projectiveSpaceAtUniverse.{u} n) where
  homEquiv {Z} := (pointsEquiv Z n).trans
    ((pointsBridge Z n).trans (grassPointsEquiv Z n (n + 1)).symm)
  homEquiv_comp {Z Z'} f g := by
    refine (grassPointsEquiv Z n (n + 1)).injective ?_
    simp only [Equiv.trans_apply, Equiv.apply_symm_apply]
    rw [grassPointsEquiv_functor_map]
    exact (congrArg (toGrassPoints Z n) (pointsOfHom_comp f g)).trans
      (toGrassPoints_pullbackPoints f (pointsOfHom g))

/-- The isomorphism between two objects representing the same functor, with its two morphisms
written out in terms of the two representations: the morphism `Y ⟶ Y'` is the one that `Y'`'s
representation attaches to the element of `F.obj (op Y)` classifying the identity of `Y`. -/
private def isoOfRepresentableBy {C : Type*} [Category C] {F : Cᵒᵖ ⥤ Type*} {Y Y' : C}
    (e : F.RepresentableBy Y) (e' : F.RepresentableBy Y') : Y ≅ Y' where
  hom := e'.homEquiv.symm (e.homEquiv (𝟙 Y))
  inv := e.homEquiv.symm (e'.homEquiv (𝟙 Y'))
  hom_inv_id := by
    refine e.homEquiv.injective ?_
    rw [e.homEquiv_comp, Equiv.apply_symm_apply, ← e'.homEquiv_eq, Equiv.apply_symm_apply]
  inv_hom_id := by
    refine e'.homEquiv.injective ?_
    rw [e'.homEquiv_comp, Equiv.apply_symm_apply, ← e.homEquiv_eq, Equiv.apply_symm_apply]

/-- The two representations agree through the comparison isomorphism. -/
private theorem homEquiv_comp_isoOfRepresentableBy_hom {C : Type*} [Category C]
    {F : Cᵒᵖ ⥤ Type*} {Y Y' : C} (e : F.RepresentableBy Y) (e' : F.RepresentableBy Y')
    {Z : C} (f : Z ⟶ Y) :
    e'.homEquiv (f ≫ (isoOfRepresentableBy e e').hom) = e.homEquiv f := by
  rw [e'.homEquiv_comp, e.homEquiv_eq f]
  exact congrArg (F.map f.op) (Equiv.apply_symm_apply _ _)

/-! ### The isomorphism -/

/-- The Grassmannian `G(n, n + 1)` over the integers is isomorphic to projective `n`-space, by
the comparison of their representations of the functor of finite locally free rank-one quotients
of the free module of rank `n + 1`. -/
@[stacks 089V]
def grassmannianSuccIso (n : ℕ) :
    Grassmannian.scheme.{u} n (n + 1) ≅ projectiveSpaceAtUniverse.{u} n where
  hom := (projectiveSpaceRepresentableBy.{u} n).homEquiv.symm
    ((Grassmannian.schemeRepresentableBy.{u} n (n + 1)).homEquiv
      (𝟙 (Grassmannian.scheme.{u} n (n + 1))))
  inv := (Grassmannian.schemeRepresentableBy.{u} n (n + 1)).homEquiv.symm
    ((projectiveSpaceRepresentableBy.{u} n).homEquiv (𝟙 (projectiveSpaceAtUniverse.{u} n)))
  hom_inv_id := by
    refine (Grassmannian.schemeRepresentableBy.{u} n (n + 1)).homEquiv.injective ?_
    rw [(Grassmannian.schemeRepresentableBy.{u} n (n + 1)).homEquiv_comp,
      Equiv.apply_symm_apply, ← (projectiveSpaceRepresentableBy.{u} n).homEquiv_eq,
      Equiv.apply_symm_apply]
  inv_hom_id := by
    refine (projectiveSpaceRepresentableBy.{u} n).homEquiv.injective ?_
    rw [(projectiveSpaceRepresentableBy.{u} n).homEquiv_comp, Equiv.apply_symm_apply,
      ← (Grassmannian.schemeRepresentableBy.{u} n (n + 1)).homEquiv_eq, Equiv.apply_symm_apply]

/-- The isomorphism `G(n, n + 1) ≅ ℙⁿ_ℤ` matches the two representations: the rank-one quotient
classified by a morphism `f` to the Grassmannian is classified, after composing with the
isomorphism, by the same point of the Grassmannian functor read through projective space. -/
@[stacks 089V "the isomorphism matches the two moduli descriptions"]
theorem homEquiv_comp_grassmannianSuccIso_hom (n : ℕ) {Z : Scheme.{u}}
    (f : Z ⟶ Grassmannian.scheme.{u} n (n + 1)) :
    (projectiveSpaceRepresentableBy.{u} n).homEquiv (f ≫ (grassmannianSuccIso.{u} n).hom) =
      (Grassmannian.schemeRepresentableBy.{u} n (n + 1)).homEquiv f := by
  exact homEquiv_comp_isoOfRepresentableBy_hom _ _ f

/-- **The isomorphism of Tag 089V on points.** A morphism `f` to the Grassmannian classifies a
rank-one quotient of the free module of rank `n + 1`; composing with the isomorphism gives the
morphism to projective space whose invertible module with `n + 1` generating global sections is
the one the dictionary attaches to that quotient. -/
theorem toGrassPoints_pointsOfHom_comp_grassmannianSuccIso_hom (n : ℕ) {Z : Scheme.{u}}
    (f : Z ⟶ Grassmannian.scheme.{u} n (n + 1)) :
    toGrassPoints Z n (pointsOfHom (f ≫ (grassmannianSuccIso.{u} n).hom)) =
      grassPointsEquiv Z n (n + 1)
        ((Grassmannian.schemeRepresentableBy.{u} n (n + 1)).homEquiv f) := by
  rw [← homEquiv_comp_grassmannianSuccIso_hom n f]
  change _ = grassPointsEquiv Z n (n + 1) ((grassPointsEquiv Z n (n + 1)).symm
    (toGrassPoints Z n (pointsOfHom (f ≫ (grassmannianSuccIso.{u} n).hom))))
  rw [Equiv.apply_symm_apply]

end Stacks.ProjectiveSpaceModuli

end
