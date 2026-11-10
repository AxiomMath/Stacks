module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.CategoryTheory.Limits.IsLimit
public import StacksCore.Tactic.EgaSgaAttribute
public import StacksCore.Tactic.StacksAttribute

/-!
# Finite-type models of a quasi-affine open subscheme

A scheme of finite type over the integers that is open in an affine scheme `Spec R` descends to
an open subscheme of `Spec A` for a finite-type `ℤ`-subalgebra `A ⊆ R`. The subalgebras with
this property are directed under inclusion and their canonical colimit is `R`.

This is Stacks 01Z7, one of the ingredients of absolute Noetherian approximation (Stacks 07RN):
there it is what writes the fibre product `B_i = B ×_R R_i` as a directed colimit of finite-type
`ℤ`-subalgebras over which the quasi-affine open `W_i` is still an open subscheme.

## Main definitions

* `Stacks.FiniteTypeOpenModel.IsOpenModel` records a finite-type subalgebra through which the
  given open immersion factors as an open immersion.
* `Stacks.FiniteTypeOpenModel.OpenModel`, `openModelDiagram` and `openModelCocone` give the
  subalgebras with that property, their inclusion diagram, and its cocone over `R`.

## Main results

* `Stacks.FiniteTypeOpenModel.exists_openModel` supplies a finite-type open model.
* `Stacks.FiniteTypeOpenModel.openModel_directed` says the models are directed under inclusion.
* `Stacks.FiniteTypeOpenModel.openModelCocone_isColimit` identifies `R` as their colimit.
* `Stacks.FiniteTypeOpenModel.openModelDiagram_map_apply` and
  `Stacks.FiniteTypeOpenModel.openModelCocone_ι_apply` pin the diagram and the cocone down to the
  inclusions, so that the colimit statement says what it should.
* `Stacks.FiniteTypeOpenModel.finiteType_localizationAway_of_basicOpen_le_opensRange`: a standard
  open contained in the range of the open immersion has a finite-type coordinate ring.
* `Stacks.FiniteTypeOpenModel.exists_fg_subalgebra_for_finite_charts`,
  `Stacks.FiniteTypeOpenModel.chartNumerators_mono` and
  `Stacks.FiniteTypeOpenModel.awayMap_surjective_of_generators`: the finite-type subalgebra that
  finitely many charts contribute, its monotonicity, and the surjectivity of the localization maps
  it buys.

## Implementation notes

The factorization through `Spec A` is recorded as an equality of scheme morphisms, so
`IsOpenModel` asserts something about the canonical map and not merely the existence of some
open immersion. The source's quasi-affineness hypothesis on `W` is not assumed: it follows from
the given open immersion into an affine scheme. "Finite type over `ℤ`" is expressed, as in Stacks
01T1, by `AlgebraicGeometry.LocallyOfFiniteType` together with
`AlgebraicGeometry.QuasiCompact` for the structural morphism to the terminal scheme; the
translation between that and `RingHom.FiniteType` of `algebraMap ℤ _` runs through
`AlgebraicGeometry.specULiftZIsTerminal`, since the terminal scheme is `Spec (ULift ℤ)`.

The source says "Details omitted" after choosing the subalgebra. The detail that has to be
supplied is that enlarging the subalgebra preserves the open-immersion property, and for that one
must keep the chart data — the covering standard opens and the generators of their coordinate
rings — alongside the subalgebra; `exists_openModel_with_charts` is that strengthened form, and
`openModel_of_chart_data` is the step from chart data to an open immersion.

Six of the pieces of that construction are public rather than private, because a model carrying
*more* than the open-immersion property has to be built from the same ingredients:
`finiteType_localizationAway_of_basicOpen_le_opensRange` bounds the data finitely many charts
contribute, `exists_fg_subalgebra_for_finite_charts` produces it, `chartNumerators_mono` carries
it into a larger subalgebra, and `awayMap_surjective_of_generators` turns it into surjectivity of
a localization map.  The other two are `exists_openModel_with_charts` and
`openModel_of_chart_data` themselves: a model *above a prescribed finitely generated subalgebra*
is obtained by enlarging the model they produce, which needs the chart data and the step that
consumes it, not just the conclusion `exists_openModel`.

## References

* [Stacks Project, Tag 01Z7](https://stacks.math.columbia.edu/tag/01Z7)
* [EGA II, 5.1.9]
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.FiniteTypeOpenModel

/-- A quasi-compact open of an affine scheme is covered by finitely many standard opens each
contained in it. -/
public lemma exists_finite_basicOpen_cover {R : Type u} [CommRing R]
    (U : TopologicalSpace.Opens (PrimeSpectrum R))
    (hU : IsCompact (U : Set (PrimeSpectrum R))) :
    ∃ (n : ℕ) (r : Fin n → R),
      (∀ i, (PrimeSpectrum.basicOpen (r i) : Set (PrimeSpectrum R)) ⊆
        (U : Set (PrimeSpectrum R))) ∧
      (U : Set (PrimeSpectrum R)) ⊆
        ⋃ i, (PrimeSpectrum.basicOpen (r i) : Set (PrimeSpectrum R)) := by
  let I := {r : R // (PrimeSpectrum.basicOpen r : TopologicalSpace.Opens (PrimeSpectrum R)) ≤ U}
  have hcover : (U : Set (PrimeSpectrum R)) ⊆ ⋃ i : I,
      (PrimeSpectrum.basicOpen i.1 : Set (PrimeSpectrum R)) := by
    intro x hx
    obtain ⟨V, ⟨r, rfl⟩, hxr, hrV⟩ :=
      PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hx U.2
    exact Set.mem_iUnion.mpr ⟨⟨r, hrV⟩, hxr⟩
  obtain ⟨t, ht⟩ := hU.elim_finite_subcover
    (fun i : I => (PrimeSpectrum.basicOpen i.1 : Set (PrimeSpectrum R)))
    (fun i => PrimeSpectrum.isOpen_basicOpen) hcover
  refine ⟨t.card, fun j => (t.equivFin.symm j).1.1, fun j => (t.equivFin.symm j).1.2, ?_⟩
  · intro x hx
    obtain ⟨i, hi, hix⟩ := Set.mem_iUnion₂.mp (ht hx)
    exact Set.mem_iUnion.mpr ⟨t.equivFin ⟨i, hi⟩, by simpa using hix⟩

/-- A finite algebra generating set for the target localization, with each generator's numerator
in the subalgebra, makes the map of localizations surjective. -/
public lemma awayMap_surjective_of_generators {R : Type u} [CommRing R] (r : R)
    (A : Subalgebra ℤ R) (hr : r ∈ A)
    (s : Finset (Localization.Away r))
    (hs : Algebra.adjoin ℤ (s : Set (Localization.Away r)) = ⊤)
    (hnum : ∀ x ∈ s, ∃ (a : A) (n : ℕ),
      x * algebraMap R (Localization.Away r) r ^ n =
        algebraMap R (Localization.Away r) a.1) :
    Function.Surjective (Localization.awayMap (A.val : A →+* R) (⟨r, hr⟩ : A)) := by
  let rA : A := ⟨r, hr⟩
  let f : A →ₐ[ℤ] R := { toRingHom := A.val, commutes' := fun _ => rfl }
  have : IsLocalization.Away (f rA) (Localization.Away r) :=
    inferInstanceAs (IsLocalization.Away r (Localization.Away r))
  let g : Localization.Away rA →ₐ[ℤ] Localization.Away r :=
    IsLocalization.Away.mapₐ (Localization.Away rA) (Localization.Away r) f rA
  have hg : g.range = ⊤ := by
    rw [eq_top_iff, ← hs]
    refine Algebra.adjoin_le fun x hx => ?_
    obtain ⟨a, n, hax⟩ := hnum x hx
    change x ∈ g.range
    refine ⟨algebraMap A (Localization.Away rA) a *
      IsLocalization.Away.invSelf rA ^ n, ?_⟩
    have hmap : g.toRingHom (algebraMap A (Localization.Away rA) a *
        IsLocalization.Away.invSelf rA ^ n) =
        algebraMap R (Localization.Away r) a.1 *
          IsLocalization.Away.invSelf r ^ n := by
      simp [g, f, rA, IsLocalization.Away.mapₐ, IsLocalization.Away.invSelf,
        IsLocalization.Away.map, IsLocalization.map_mk']
    rw [hmap, ← hax, mul_assoc, ← mul_pow]
    simp [IsLocalization.Away.mul_invSelf]
  exact (AlgHom.range_eq_top g).mp hg

/-- The two affine charts agree once the finite list of localization numerators has been
adjoined to the subalgebra. -/
public noncomputable def awayAlgEquivOfNumerators {R : Type u} [CommRing R] (r : R)
    (A : Subalgebra ℤ R) (hr : r ∈ A)
    (s : Finset (Localization.Away r))
    (hs : Algebra.adjoin ℤ (s : Set (Localization.Away r)) = ⊤)
    (hnum : ∀ x ∈ s, ∃ (a : A) (n : ℕ),
      x * algebraMap R (Localization.Away r) r ^ n =
        algebraMap R (Localization.Away r) a.1) :
    Localization.Away (⟨r, hr⟩ : A) ≃ₐ[ℤ] Localization.Away r := by
  let f : A →ₐ[ℤ] R :=
    { toRingHom := A.val
      commutes' := fun _ => rfl }
  have : IsLocalization.Away (f (⟨r, hr⟩ : A)) (Localization.Away r) :=
    inferInstanceAs (IsLocalization.Away r (Localization.Away r))
  let g := IsLocalization.Away.mapₐ (Localization.Away (⟨r, hr⟩ : A))
    (Localization.Away r) f (⟨r, hr⟩ : A)
  refine AlgEquiv.ofBijective g ⟨?_, awayMap_surjective_of_generators r A hr s hs hnum⟩
  change Function.Injective (Localization.awayMap (A.val : A →+* R) (⟨r, hr⟩ : A))
  rw [Localization.awayMap_injective_iff]
  exact fun a ha => ⟨0, by simpa using ha⟩

/-- One affine chart contributes finitely many elements to adjoin: its equation and the
numerators of a finite set of generators of its localization. -/
public lemma exists_fg_chart_subalgebra {R : Type u} [CommRing R] (r : R)
    [Algebra.FiniteType ℤ (Localization.Away r)] :
    ∃ A : Subalgebra ℤ R, A.FG ∧ r ∈ A ∧
      ∃ (s : Finset (Localization.Away r)),
        Algebra.adjoin ℤ (s : Set (Localization.Away r)) = ⊤ ∧
        ∀ x ∈ s, ∃ (a : A) (n : ℕ),
          x * algebraMap R (Localization.Away r) r ^ n =
            algebraMap R (Localization.Away r) a.1 := by
  classical
  obtain ⟨s, hs⟩ := (Algebra.FiniteType.out :
    (⊤ : Subalgebra ℤ (Localization.Away r)).FG)
  have hnums := fun (x : Localization.Away r) (_ : x ∈ s) =>
    IsLocalization.Away.surj r x
  let num : {x // x ∈ s} → R := fun x =>
    Classical.choose (Classical.choose_spec (hnums x.1 x.2))
  let t : Finset R := insert r (s.attach.image num)
  let A : Subalgebra ℤ R := Algebra.adjoin ℤ (t : Set R)
  refine ⟨A, Subalgebra.fg_adjoin_finset t, Algebra.subset_adjoin (Finset.mem_insert_self r _),
    s, hs, fun x hx => ?_⟩
  let y : {x // x ∈ s} := ⟨x, hx⟩
  let a : A := ⟨num y, Algebra.subset_adjoin
    (Finset.mem_insert_of_mem (Finset.mem_image_of_mem num (Finset.mem_attach _ y)))⟩
  refine ⟨a, Classical.choose (hnums x hx), ?_⟩
  simpa [a, num, y] using Classical.choose_spec (Classical.choose_spec (hnums x hx))

/-- Finitely many affine charts can use one finite-type subalgebra: take the finite supremum
of the chart subalgebras and transport each chart's numerators into it. -/
public lemma exists_fg_subalgebra_for_finite_charts {R : Type u} [CommRing R]
    (n : ℕ) (r : Fin n → R)
    (hft : ∀ i, Algebra.FiniteType ℤ (Localization.Away (r i))) :
    ∃ A : Subalgebra ℤ R, A.FG ∧ (∀ i, r i ∈ A) ∧
      ∀ i, ∃ (s : Finset (Localization.Away (r i))),
        Algebra.adjoin ℤ (s : Set (Localization.Away (r i))) = ⊤ ∧
        ∀ x ∈ s, ∃ (a : A) (m : ℕ),
          x * algebraMap R (Localization.Away (r i)) (r i) ^ m =
            algebraMap R (Localization.Away (r i)) a.1 := by
  classical
  have hc := fun i => exists_fg_chart_subalgebra (r i)
  let Ai : Fin n → Subalgebra ℤ R := fun i => Classical.choose (hc i)
  let A : Subalgebra ℤ R := Finset.univ.sup Ai
  have hFGi : ∀ i, (Ai i).FG := fun i => (Classical.choose_spec (hc i)).1
  have hr_i : ∀ i, r i ∈ Ai i := fun i => (Classical.choose_spec (hc i)).2.1
  have hFG : A.FG := by
    dsimp [A]
    induction (Finset.univ : Finset (Fin n)) using Finset.induction with
    | empty => exact Subalgebra.fg_bot
    | @insert i s hi ih =>
      rw [Finset.sup_insert]
      exact (hFGi i).sup ih
  have hle : ∀ i, Ai i ≤ A := fun i => Finset.le_sup (Finset.mem_univ i)
  refine ⟨A, hFG, fun i => hle i (hr_i i), fun i => ?_⟩
  obtain ⟨s, hs, hnum⟩ := (Classical.choose_spec (hc i)).2.2
  refine ⟨s, hs, fun x hx => ?_⟩
  obtain ⟨a, m, ham⟩ := hnum x hx
  exact ⟨⟨a.1, hle i a.2⟩, m, ham⟩

/-- On a basic open on which the two localizations agree, the map of spectra induced by a
subalgebra inclusion is an open immersion. This is the scheme-theoretic bridge used below to
assemble the local finite-type models. -/
public lemma basicOpen_comp_specMap_isOpenImmersion {R : Type u} [CommRing R]
    (r : R) (A : Subalgebra ℤ R) (hr : r ∈ A)
    (e : Localization.Away (⟨r, hr⟩ : A) ≃ₐ[ℤ] Localization.Away r)
    (he : ∀ a : A, e (algebraMap A (Localization.Away (⟨r, hr⟩ : A)) a) =
      algebraMap R (Localization.Away r) a.1) :
    IsOpenImmersion
      (Scheme.Opens.ι (X := Spec (.of R)) (PrimeSpectrum.basicOpen r) ≫
        Spec.map (CommRingCat.ofHom (A.val : A →+* R))) := by
  let rA : A := ⟨r, hr⟩
  let eR := basicOpenIsoSpecAway (R := CommRingCat.of R) r
  let eA := basicOpenIsoSpecAway (R := CommRingCat.of A) rA
  let kR : R →+* Localization.Away r := algebraMap R (Localization.Away r)
  let kA : A →+* Localization.Away rA := algebraMap A (Localization.Away rA)
  let qIso : CommRingCat.of (Localization.Away rA) ≅
      CommRingCat.of (Localization.Away r) := e.toRingEquiv.toCommRingCatIso
  have hcomp :
      Scheme.Opens.ι (X := Spec (.of R)) (PrimeSpectrum.basicOpen r) ≫
        Spec.map (CommRingCat.ofHom (A.val : A →+* R)) =
        eR.hom ≫ Spec.map qIso.hom ≫ Spec.map (CommRingCat.ofHom kA) := by
    rw [← basicOpenIsoSpecAway_hom_SpecMap (R := CommRingCat.of R)]
    change eR.hom ≫ (Spec.map (CommRingCat.ofHom kR) ≫
        Spec.map (CommRingCat.ofHom (A.val : A →+* R))) =
      eR.hom ≫ (Spec.map qIso.hom ≫ Spec.map (CommRingCat.ofHom kA))
    refine (cancel_epi eR.hom).mpr ?_
    rw [← Spec.map_comp, ← Spec.map_comp, Spec.map_injective.eq_iff]
    apply CommRingCat.hom_ext
    ext x
    exact (he x).symm
  rw [hcomp]
  infer_instance

/-- A finite-type subalgebra over which the given open immersion remains an open
immersion, with its factorization into the original affine scheme. -/
public def IsOpenModel {R : Type u} [CommRing R] {W : Scheme.{u}}
    (f : W ⟶ Spec (.of R)) (A : Subalgebra ℤ R) : Prop :=
  A.FG ∧ ∃ g : W ⟶ Spec (.of A), IsOpenImmersion g ∧
    f ≫ Spec.map (CommRingCat.ofHom A.subtype) = g

/-- The finite-type subalgebras through which the open immersion remains open. -/
public abbrev OpenModel {R : Type u} [CommRing R] {W : Scheme.{u}}
    (f : W ⟶ Spec (.of R)) := {A : Subalgebra ℤ R // IsOpenModel f A}

/-- The canonical diagram of open models with inclusion transition maps. -/
public abbrev openModelDiagram {R : Type u} [CommRing R] {W : Scheme.{u}}
    (f : W ⟶ Spec (.of R)) : OpenModel f ⥤ CommRingCat.{u} :=
  { obj := fun A => CommRingCat.of A.1
    map := fun {A B} h => CommRingCat.ofHom (Subalgebra.inclusion h.le).toRingHom
    map_id := by intro A; apply CommRingCat.hom_ext; ext x; rfl
    map_comp := by intro A B C h k; apply CommRingCat.hom_ext; ext x; rfl }

/-- The canonical inclusion cocone of open models over the original ring. -/
public abbrev openModelCocone {R : Type u} [CommRing R] {W : Scheme.{u}}
    (f : W ⟶ Spec (.of R)) : Cocone (openModelDiagram f) :=
  { pt := CommRingCat.of R
    ι := { app := fun A => CommRingCat.ofHom A.1.subtype
           naturality := by intro A B h; apply CommRingCat.hom_ext; ext x; rfl } }

/-- The value of `openModelDiagram` at an open model is the subalgebra itself. -/
@[simp]
public theorem openModelDiagram_obj {R : Type u} [CommRing R] {W : Scheme.{u}}
    (f : W ⟶ Spec (.of R)) (A : OpenModel f) :
    (openModelDiagram f).obj A = CommRingCat.of A.1 :=
  rfl

/-- The transition maps of `openModelDiagram` are the subalgebra inclusions. -/
public theorem openModelDiagram_map_apply {R : Type u} [CommRing R] {W : Scheme.{u}}
    (f : W ⟶ Spec (.of R)) {A B : OpenModel f} (h : A ⟶ B) (x : A.1) :
    (((openModelDiagram f).map h).hom x).1 = x.1 :=
  rfl

/-- The apex of `openModelCocone` is `R`. -/
@[simp]
public theorem openModelCocone_pt {R : Type u} [CommRing R] {W : Scheme.{u}}
    (f : W ⟶ Spec (.of R)) : (openModelCocone f).pt = CommRingCat.of R :=
  rfl

/-- The legs of `openModelCocone` are the inclusions of the subalgebras into `R`. This, together
with `openModelDiagram_map_apply`, is what makes `openModelCocone_isColimit` say that `R` is the
directed union of its finite-type open models. -/
public theorem openModelCocone_ι_apply {R : Type u} [CommRing R] {W : Scheme.{u}}
    (f : W ⟶ Spec (.of R)) (A : OpenModel f) (x : A.1) :
    ((openModelCocone f).ι.app A).hom x = x.1 :=
  rfl

/-- A standard open inside the range of an open immersion `f` lifts along `f` by an open
immersion. -/
private lemma exists_isOpenImmersion_lift_basicOpen {R : Type u} [CommRing R] {W : Scheme.{u}}
    (f : W ⟶ Spec (.of R)) [IsOpenImmersion f] (r : R)
    (hrU : (PrimeSpectrum.basicOpen r : Set (PrimeSpectrum R)) ⊆
      (f.opensRange : Set (Spec (.of R)))) :
    ∃ l : Scheme.Opens.toScheme (X := Spec (.of R)) (PrimeSpectrum.basicOpen r) ⟶ W,
      IsOpenImmersion l ∧ l ≫ f = Scheme.Opens.ι _ ∧ ∀ p, f (l p) = p.1 := by
  have hincOpen : IsOpenImmersion
      (Scheme.Opens.ι (X := Spec (.of R)) (PrimeSpectrum.basicOpen r)) := by
    rw [← basicOpenIsoSpecAway_hom_SpecMap (R := CommRingCat.of R)]
    infer_instance
  have hinc : Set.range (Scheme.Opens.ι (X := Spec (.of R)) (PrimeSpectrum.basicOpen r)) ⊆
      Set.range f := by
    rintro _ ⟨z, rfl⟩
    exact hrU z.2
  have hfac := IsOpenImmersion.lift_fac f _ hinc
  have : IsOpenImmersion (IsOpenImmersion.lift f _ hinc ≫ f) := by
    rw [hfac]
    exact hincOpen
  refine ⟨IsOpenImmersion.lift f _ hinc, IsOpenImmersion.of_comp _ f, hfac, fun p => ?_⟩
  exact congrArg (fun k => k p) hfac

/-- Chartwise localization data suffices to make the canonical factorization an open
immersion. -/
public lemma openModel_of_chart_data {R : Type u} [CommRing R] {W : Scheme.{u}}
    (f : W ⟶ Spec (.of R)) [IsOpenImmersion f]
    (A : Subalgebra ℤ R) (hAfg : A.FG) (n : ℕ) (r : Fin n → R)
    (hrU : ∀ i, (PrimeSpectrum.basicOpen (r i) : Set (PrimeSpectrum R)) ⊆
      (f.opensRange : Set (Spec (.of R))))
    (hcover : (f.opensRange : Set (Spec (.of R))) ⊆
      ⋃ i, (PrimeSpectrum.basicOpen (r i) : Set (PrimeSpectrum R)))
    (hrA : ∀ i, r i ∈ A)
    (hnums : ∀ i, ∃ (s : Finset (Localization.Away (r i))),
      Algebra.adjoin ℤ (s : Set (Localization.Away (r i))) = ⊤ ∧
      ∀ x ∈ s, ∃ (a : A) (m : ℕ),
        x * algebraMap R (Localization.Away (r i)) (r i) ^ m =
          algebraMap R (Localization.Away (r i)) a.1) :
    IsOpenModel f A := by
  classical
  let g : W ⟶ Spec (.of A) := f ≫ Spec.map (CommRingCat.ofHom (A.val : A →+* R))
  have key : ∀ i, ∃ l : Scheme.Opens.toScheme (X := Spec (.of R))
      (PrimeSpectrum.basicOpen (r i)) ⟶ W,
      IsOpenImmersion l ∧ IsOpenImmersion (l ≫ g) ∧ ∀ p, f (l p) = p.1 := by
    intro i
    obtain ⟨l, hl, hlf, hlp⟩ := exists_isOpenImmersion_lift_basicOpen f (r i) (hrU i)
    refine ⟨l, hl, ?_, hlp⟩
    obtain ⟨s, hs, hnum⟩ := hnums i
    let e := awayAlgEquivOfNumerators (r i) A (hrA i) s hs hnum
    have he : ∀ a : A, e (algebraMap A (Localization.Away (⟨r i, hrA i⟩ : A)) a) =
        algebraMap R (Localization.Away (r i)) a.1 := by
      intro a
      simp [e, awayAlgEquivOfNumerators, IsLocalization.Away.mapₐ,
        IsLocalization.Away.map]
    have hlocal := basicOpen_comp_specMap_isOpenImmersion (r i) A (hrA i) e he
    have hfactor : l ≫ g = Scheme.Opens.ι _ ≫ Spec.map (CommRingCat.ofHom (A.val : A →+* R)) := by
      rw [← hlf]
      simp [g]
    rw [hfactor]
    exact hlocal
  refine ⟨hAfg, g, ?_, rfl⟩
  apply IsOpenImmersion.of_forall_source_exists g ?_ ?_
  · intro x y hxy
    have hfx : f x ∈ f.opensRange := ⟨x, rfl⟩
    obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp (hcover hfx)
    let rA : A := ⟨r i, hrA i⟩
    have hxy' : PrimeSpectrum.comap (A.val : A →+* R) (f x) =
        PrimeSpectrum.comap (A.val : A →+* R) (f y) := by
      change Spec.map (CommRingCat.ofHom (A.val : A →+* R)) (f x) =
        Spec.map (CommRingCat.ofHom (A.val : A →+* R)) (f y) at hxy
      exact hxy
    have hideal : (f x : PrimeSpectrum R).asIdeal.comap A.val =
        (f y : PrimeSpectrum R).asIdeal.comap A.val :=
      congrArg PrimeSpectrum.asIdeal hxy'
    have hfy : f y ∈ PrimeSpectrum.basicOpen (r i) := by
      change (r i) ∉ (f y : PrimeSpectrum R).asIdeal
      intro hy
      have hnot : (r i) ∉ (f x : PrimeSpectrum R).asIdeal :=
        (PrimeSpectrum.mem_basicOpen (r i) (f x)).mp hxi
      have hyA : rA ∈ (f y : PrimeSpectrum R).asIdeal.comap A.val :=
        Ideal.mem_comap.mpr (by simpa [rA] using hy)
      have hxA : rA ∈ (f x : PrimeSpectrum R).asIdeal.comap A.val :=
        hideal.symm ▸ hyA
      have hxA' : (A.val rA) ∈ (f x : PrimeSpectrum R).asIdeal :=
        Ideal.mem_comap.mp hxA
      exact hnot (by simpa [rA] using hxA')
    obtain ⟨l, hl, hlg, hlp⟩ := key i
    have hlx : l ⟨f x, hxi⟩ = x := f.isOpenEmbedding.injective (hlp _)
    have hly : l ⟨f y, hfy⟩ = y := f.isOpenEmbedding.injective (hlp _)
    have hp : (l ≫ g) ⟨f x, hxi⟩ = (l ≫ g) ⟨f y, hfy⟩ := by
      change g (l _) = g (l _)
      rw [hlx, hly]
      exact hxy
    calc
      x = l ⟨f x, hxi⟩ := hlx.symm
      _ = l ⟨f y, hfy⟩ := congrArg l ((Scheme.Hom.isOpenEmbedding (l ≫ g)).injective hp)
      _ = y := hly
  · intro x
    have hfx : f x ∈ f.opensRange := ⟨x, rfl⟩
    obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp (hcover hfx)
    obtain ⟨l, hl, hlg, hlp⟩ := key i
    refine ⟨_, l, hl, ?_, hlg⟩
    exact Scheme.Hom.mem_opensRange.mpr ⟨⟨f x, hxi⟩, f.isOpenEmbedding.injective (hlp _)⟩

/-- **A standard open inside the range of a finite-type open immersion has a finite-type
coordinate ring.**  If `W` is of finite type over `ℤ` and `f : W ⟶ Spec R` is an open immersion
whose range contains the standard open `D(r)`, then `R_r` is a finite-type `ℤ`-algebra: `D(r)` is
isomorphic to an open subscheme of `W`, hence of finite type over `ℤ`, and it is affine with
coordinate ring `R_r`.

This is what makes `Stacks.FiniteTypeOpenModel.exists_fg_chart_subalgebra` applicable to the
equations of a chart, and hence what bounds the data that has to be adjoined to a subalgebra to
make it an open model. -/
public lemma finiteType_localizationAway_of_basicOpen_le_opensRange {R : Type u} [CommRing R]
    {W : Scheme.{u}} (f : W ⟶ Spec (.of R)) [LocallyOfFiniteType (terminal.from W)]
    [IsOpenImmersion f] (r : R)
    (hrU : (PrimeSpectrum.basicOpen r : Set (PrimeSpectrum R)) ⊆
      (f.opensRange : Set (Spec (.of R)))) :
    Algebra.FiniteType ℤ (Localization.Away r) := by
  obtain ⟨l, hl, -, -⟩ := exists_isOpenImmersion_lift_basicOpen f r hrU
  let eR := basicOpenIsoSpecAway (R := CommRingCat.of R) r
  have hER : LocallyOfFiniteType
      (eR.hom ≫ terminal.from (Spec (.of (Localization.Away r)))) := by
    rw [terminal.comp_from, ← terminal.comp_from l]
    infer_instance
  let zMap : ULift.{u} ℤ →+* Localization.Away r :=
    (algebraMap ℤ (Localization.Away r)).comp ULift.ringEquiv.toRingHom
  let : Algebra (ULift.{u} ℤ) (Localization.Away r) := zMap.toAlgebra
  let zSpec : Spec (.of (Localization.Away r)) ⟶ Spec (.of (ULift.{u} ℤ)) :=
    Spec.map (CommRingCat.ofHom zMap)
  have hzMap : RingHom.FiniteType (algebraMap ℤ (Localization.Away r)) := by
    have hzUL : RingHom.FiniteType (algebraMap (ULift.{u} ℤ) (Localization.Away r)) := by
      let : MorphismProperty.RespectsIso @LocallyOfFiniteType :=
        MorphismProperty.respectsIso_of_isStableUnderComposition
          (P := @LocallyOfFiniteType) (fun _ _ _ _ => inferInstance)
      have hSpecUL : LocallyOfFiniteType zSpec := by
        have hterm : LocallyOfFiniteType
            (terminal.from (Spec (.of (Localization.Away r)))) := by
          exact (MorphismProperty.cancel_left_of_respectsIso
            (P := @LocallyOfFiniteType) eR.hom _).mp hER
        let eZ := specULiftZIsTerminal.uniqueUpToIso terminalIsTerminal
        have heq : zSpec ≫ eZ.hom = terminal.from (Spec (.of (Localization.Away r))) :=
          Subsingleton.elim _ _
        have hZ : LocallyOfFiniteType (zSpec ≫ eZ.hom) := by
          rw [heq]
          exact hterm
        exact (MorphismProperty.cancel_right_of_respectsIso
          (P := @LocallyOfFiniteType) zSpec eZ.hom).mp hZ
      exact (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mp hSpecUL
    let liftZ : ℤ →+* ULift.{u} ℤ := ULift.ringEquiv.symm.toRingHom
    have hLiftZ : RingHom.FiniteType liftZ :=
      RingHom.FiniteType.of_surjective liftZ ULift.ringEquiv.symm.surjective
    have hcomp := RingHom.FiniteType.comp hzUL hLiftZ
    convert hcomp using 1
    ext x
    simp [liftZ]
  exact RingHom.finiteType_algebraMap.mp hzMap

/-- The finite-type open model produced by `exists_openModel`, together with the chart data its
construction goes through: the finitely many standard opens covering the range of `f`, their
equations inside the subalgebra, and generators of each chart's coordinate ring with numerators
in the subalgebra. The chart data is what makes the model enlargeable, which is what
`openModel_directed` and `openModelCocone_isColimit` need. -/
public theorem exists_openModel_with_charts {R : Type u} [CommRing R] {W : Scheme.{u}}
    (f : W ⟶ Spec (.of R))
    [LocallyOfFiniteType (terminal.from W)]
    [QuasiCompact (terminal.from W)] [IsOpenImmersion f] :
    ∃ A : Subalgebra ℤ R, IsOpenModel f A ∧
      ∃ (n : ℕ) (r : Fin n → R),
        (∀ i, (PrimeSpectrum.basicOpen (r i) : Set (PrimeSpectrum R)) ⊆
          (f.opensRange : Set (Spec (.of R)))) ∧
        (f.opensRange : Set (Spec (.of R))) ⊆
          ⋃ i, (PrimeSpectrum.basicOpen (r i) : Set (PrimeSpectrum R)) ∧
        (∀ i, r i ∈ A) ∧
        (∀ i, ∃ (s : Finset (Localization.Away (r i))),
          Algebra.adjoin ℤ (s : Set (Localization.Away (r i))) = ⊤ ∧
          ∀ x ∈ s, ∃ (a : A) (m : ℕ),
            x * algebraMap R (Localization.Away (r i)) (r i) ^ m =
              algebraMap R (Localization.Away (r i)) a.1) := by
  classical
  let U : (Spec (.of R)).Opens := f.opensRange
  have : CompactSpace W :=
    (AlgebraicGeometry.compactSpace_iff_quasiCompact W).mpr inferInstance
  obtain ⟨n, r, hrU, hcover⟩ := exists_finite_basicOpen_cover U (isCompact_range f.continuous)
  obtain ⟨A, hAfg, hrA, hnums⟩ := exists_fg_subalgebra_for_finite_charts n r fun i =>
    finiteType_localizationAway_of_basicOpen_le_opensRange f (r i) (hrU i)
  exact ⟨A, openModel_of_chart_data f A hAfg n r hrU hcover hrA hnums,
    n, r, hrU, hcover, hrA, hnums⟩

/-- Chart data for a subalgebra is chart data for any larger subalgebra. -/
public lemma chartNumerators_mono {R : Type u} [CommRing R]
    {A B : Subalgebra ℤ R} (hAB : A ≤ B) {n : ℕ} {r : Fin n → R}
    (h : ∀ i, ∃ s : Finset (Localization.Away (r i)),
      Algebra.adjoin ℤ (s : Set (Localization.Away (r i))) = ⊤ ∧
      ∀ x ∈ s, ∃ (a : A) (m : ℕ),
        x * algebraMap R (Localization.Away (r i)) (r i) ^ m =
          algebraMap R (Localization.Away (r i)) a.1) :
    ∀ i, ∃ s : Finset (Localization.Away (r i)),
      Algebra.adjoin ℤ (s : Set (Localization.Away (r i))) = ⊤ ∧
      ∀ x ∈ s, ∃ (a : B) (m : ℕ),
        x * algebraMap R (Localization.Away (r i)) (r i) ^ m =
          algebraMap R (Localization.Away (r i)) a.1 := by
  intro i
  obtain ⟨s, hs, hnum⟩ := h i
  refine ⟨s, hs, fun x hx => ?_⟩
  obtain ⟨a, m, ham⟩ := hnum x hx
  exact ⟨⟨a.1, hAB a.2⟩, m, ham⟩

/-- An open immersion of a finite-type scheme into an affine scheme
 descends to a finite-type subalgebra. -/
@[stacks 01Z7 "existence of a finite-type open model", ega "II 5.1.9" "base Spec ℤ, affine"]
public theorem exists_openModel {R : Type u} [CommRing R] {W : Scheme.{u}}
    (f : W ⟶ Spec (.of R))
    [LocallyOfFiniteType (terminal.from W)]
    [QuasiCompact (terminal.from W)] [IsOpenImmersion f] :
    ∃ A : Subalgebra ℤ R, IsOpenModel f A :=
  (exists_openModel_with_charts f).imp (fun _ h => h.1)

/-- Finite-type subalgebras admitting the open model are directed by inclusion. -/
@[stacks 01Z7 "directedness of the finite-type open models"]
public theorem openModel_directed {R : Type u} [CommRing R] {W : Scheme.{u}}
    (f : W ⟶ Spec (.of R))
    [LocallyOfFiniteType (terminal.from W)]
    [QuasiCompact (terminal.from W)] [IsOpenImmersion f] :
    ∀ A B : Subalgebra ℤ R, IsOpenModel f A → IsOpenModel f B →
      ∃ C : Subalgebra ℤ R, IsOpenModel f C ∧ A ≤ C ∧ B ≤ C := by
  classical
  intro A B hA hB
  obtain ⟨A₀, hA₀, n, r, hrU, hcover, hrA₀, hnums⟩ :=
    exists_openModel_with_charts f
  let C : Subalgebra ℤ R := (A ⊔ B) ⊔ A₀
  have hA₀C : A₀ ≤ C := le_sup_right
  exact ⟨C, openModel_of_chart_data f C ((hA.1.sup hB.1).sup hA₀.1) n r hrU hcover
    (fun i => hA₀C (hrA₀ i)) (chartNumerators_mono hA₀C hnums),
    le_trans le_sup_left le_sup_left, le_trans le_sup_right le_sup_left⟩

/-- The canonical cocone of finite-type open models is a colimit cocone. -/
@[stacks 01Z7 "colimit of the finite-type open models"]
public theorem openModelCocone_isColimit {R : Type u} [CommRing R] {W : Scheme.{u}}
    (f : W ⟶ Spec (.of R))
    [LocallyOfFiniteType (terminal.from W)]
    [QuasiCompact (terminal.from W)] [IsOpenImmersion f] :
    Nonempty (IsColimit (openModelCocone f)) := by
  classical
  let : IsDirectedOrder (OpenModel f) := by
    refine ⟨fun A B => ?_⟩
    obtain ⟨C, hC, hAC, hBC⟩ := openModel_directed f A.1 B.1 A.2 B.2
    exact ⟨⟨C, hC⟩, hAC, hBC⟩
  let : Nonempty (OpenModel f) := by
    obtain ⟨A, hA⟩ := exists_openModel f
    exact ⟨⟨A, hA⟩⟩
  let D := openModelDiagram f
  let := reflectsColimit_of_reflectsIsomorphisms D (forget CommRingCat)
  refine ⟨?_⟩
  apply isColimitOfReflects (forget CommRingCat)
  apply Types.FilteredColimit.isColimitOf'
  · intro x
    obtain ⟨A₀, hA₀, n, r, hrU, hcover, hrA₀, hnums⟩ :=
      exists_openModel_with_charts f
    let T : Subalgebra ℤ R := Algebra.adjoin ℤ ({x} : Set R)
    let C : Subalgebra ℤ R := A₀ ⊔ T
    have hTfg : T.FG := by
      simpa [T] using Subalgebra.fg_adjoin_finset ({x} : Finset R)
    have hA₀C : A₀ ≤ C := le_sup_left
    have hC : IsOpenModel f C := openModel_of_chart_data f C (hA₀.1.sup hTfg) n r hrU hcover
      (fun i => hA₀C (hrA₀ i)) (chartNumerators_mono hA₀C hnums)
    have hxC : x ∈ C := (le_sup_right : T ≤ C) (Algebra.subset_adjoin (by simp))
    exact ⟨⟨C, hC⟩, ⟨x, hxC⟩, rfl⟩
  · exact fun i x y h => ⟨i, 𝟙 i, Subtype.ext h⟩

end Stacks.FiniteTypeOpenModel

end
