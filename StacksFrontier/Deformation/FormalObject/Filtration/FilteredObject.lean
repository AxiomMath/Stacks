module

public import Mathlib.CategoryTheory.FiberedCategory.Cocartesian
public import Mathlib.CategoryTheory.FiberedCategory.Fiber
public import StacksFrontier.Deformation.Cofibered
public import StacksFrontier.Deformation.FormalObject.Basic

/-!
# Filtered formal objects

Ideal filtrations of a complete local algebra, and the compatible systems of objects over the
quotients by such a filtration.  This file also constructs the composite transition maps of a
filtration and of the adic truncation, and compares the indices of the two filtrations.

## Main definitions

* `IdealFiltration` is a decreasing filtration cofinal with the maximal-ideal powers.
* `FilteredFormalObject` is a compatible system over the quotients by such a filtration.
* `toAdicIndex` picks, for every `n`, a filtration index at least `n` whose ideal is contained
  in the `n`-th power of the maximal ideal.
* `Deformation.filteredBasePath` is the composite transition map of a filtration from one index
  down to a smaller one.

## Main results

* `Deformation.filteredBasePath_self`, `Deformation.filteredBasePath_succ` and
  `Deformation.filteredBasePath_mk` compute the composite transition map of a filtration.

## Implementation notes

As in Stacks Tag 06H3, levels are indexed by `n : ℕ`.  Cofinality is stated using the positive
powers `n + 1`; requiring every filtration ideal to be proper ensures that all quotient rings
have the prescribed residue field.  The usual category over a fixed ring is represented by the
categorical fibre of the projection from formal objects.

## References

* [Stacks Project, Tag 06H6](https://stacks.math.columbia.edu/tag/06H6)
-/

@[expose] public section

namespace Deformation

/-! ### Formal objects for a different filtration -/

section
open CategoryTheory
open IsLocalRing
universe u v w uF vF


variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]

/-- A decreasing filtration by proper ideals which is cofinal, in both directions, with the
positive powers of the maximal ideal. -/
structure IdealFiltration (R : CompleteLocalAlgCat.{u, v, w} Λ k) where
  /-- The ideals in the filtration. -/
  ideal : ℕ → Ideal R
  /-- The filtration is decreasing. -/
  antitone : Antitone ideal
  /-- Every quotient occurring in the filtration is nonzero. -/
  isProper : ∀ n, ideal n < ⊤
  /-- Every filtration ideal contains a positive power of the maximal ideal. -/
  pow_le : ∀ n, ∃ m, maximalIdeal R ^ (m + 1) ≤ ideal n
  /-- Every positive power of the maximal ideal contains some filtration ideal. -/
  le_pow : ∀ n, ∃ m, ideal m ≤ maximalIdeal R ^ (n + 1)

namespace IdealFiltration

variable {R : CompleteLocalAlgCat.{u, v, w} Λ k} (I : IdealFiltration R)

/-- The map on residue fields induced by `R → R / Iₙ` is bijective. -/
theorem residueMap_bijective (n : ℕ) :
    let J := I.ideal n
    letI : Nontrivial (R ⧸ J) := Ideal.Quotient.nontrivial_iff.mpr (I.isProper n).ne
    letI : IsLocalRing (R ⧸ J) :=
      IsLocalRing.of_surjective' (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective
    let q := Ideal.Quotient.mkₐ Λ J
    letI : IsLocalHom q := ⟨(IsLocalHom.of_surjective q.toRingHom
      Ideal.Quotient.mk_surjective).map_nonunit⟩
    Function.Bijective (ResidueField.mapAlgHom q) := by
  dsimp only
  let J := I.ideal n
  let : Nontrivial (R ⧸ J) := Ideal.Quotient.nontrivial_iff.mpr (I.isProper n).ne
  let : IsLocalRing (R ⧸ J) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective
  let q := Ideal.Quotient.mkₐ Λ J
  let : IsLocalHom q := ⟨(IsLocalHom.of_surjective q.toRingHom
    Ideal.Quotient.mk_surjective).map_nonunit⟩
  constructor
  · exact RingHom.injective _
  · intro y
    obtain ⟨x, rfl⟩ := residue_surjective y
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact ⟨residue R r, by simp⟩

/-- The canonical identification of the residue field of `R / Iₙ` with `k`. -/
noncomputable def residueEquiv (n : ℕ) :
    let J := I.ideal n
    letI : Nontrivial (R ⧸ J) := Ideal.Quotient.nontrivial_iff.mpr (I.isProper n).ne
    letI : IsLocalRing (R ⧸ J) :=
      IsLocalRing.of_surjective' (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective
    ResidueField (R ⧸ J) ≃ₐ[Λ] k := by
  dsimp only
  let J := I.ideal n
  letI : Nontrivial (R ⧸ J) := Ideal.Quotient.nontrivial_iff.mpr (I.isProper n).ne
  letI : IsLocalRing (R ⧸ J) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective
  let q := Ideal.Quotient.mkₐ Λ J
  letI : IsLocalHom q := ⟨(IsLocalHom.of_surjective q.toRingHom
    Ideal.Quotient.mk_surjective).map_nonunit⟩
  exact (AlgEquiv.ofBijective (ResidueField.mapAlgHom q)
    (I.residueMap_bijective n)).symm.trans R.residueEquiv

/-- `residueEquiv` sends the residue of the class of `r` in `R ⧸ I.ideal n` to the image in `k`
of the residue of `r` in `R`. -/
@[simp]
theorem residueEquiv_residue_mk (n : ℕ) (r : R) :
    let J := I.ideal n
    letI : Nontrivial (R ⧸ J) := Ideal.Quotient.nontrivial_iff.mpr (I.isProper n).ne
    letI : IsLocalRing (R ⧸ J) :=
      IsLocalRing.of_surjective' (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective
    I.residueEquiv n (residue (R ⧸ J) (Ideal.Quotient.mk J r)) =
      R.residueEquiv (residue R r) := by
  dsimp only
  let J := I.ideal n
  let : Nontrivial (R ⧸ J) := Ideal.Quotient.nontrivial_iff.mpr (I.isProper n).ne
  let : IsLocalRing (R ⧸ J) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective
  let q := Ideal.Quotient.mkₐ Λ J
  let : IsLocalHom q := ⟨(IsLocalHom.of_surjective q.toRingHom
    Ideal.Quotient.mk_surjective).map_nonunit⟩
  change R.residueEquiv
    ((AlgEquiv.ofBijective (ResidueField.mapAlgHom q) (I.residueMap_bijective n)).symm
      (residue _ (Ideal.Quotient.mk _ r))) = _
  exact congrArg R.residueEquiv
    ((AlgEquiv.ofBijective (ResidueField.mapAlgHom q)
      (I.residueMap_bijective n)).symm_apply_apply (residue R r))

/-- The Artinian local algebra `R / Iₙ`. -/
noncomputable def quotient (n : ℕ) : ArtinianLocalAlgCat.{u, v, w} Λ k := by
  let J := I.ideal n
  letI : Nontrivial (R ⧸ J) := Ideal.Quotient.nontrivial_iff.mpr (I.isProper n).ne
  letI : IsLocalRing (R ⧸ J) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective
  letI : IsArtinianRing (R ⧸ J) := by
    obtain ⟨m, hm⟩ := I.pow_le n
    apply IsLocalRing.quotient_artinian_of_mem_minimalPrimes_of_isLocalRing
    refine ⟨⟨inferInstance, le_maximalIdeal (I.isProper n).ne⟩, fun q hq _ ↦ ?_⟩
    let := hq.1
    exact Ideal.IsPrime.le_of_pow_le (hm.trans hq.2)
  exact { carrier := R ⧸ J, residueEquiv := I.residueEquiv n }

/-- The quotient projection `R / Iₙ₊₁ → R / Iₙ`. -/
noncomputable def transition (n : ℕ) : I.quotient (n + 1) ⟶ I.quotient n := by
  letI : Nontrivial (R ⧸ I.ideal n) :=
    Ideal.Quotient.nontrivial_iff.mpr (I.isProper n).ne
  letI : IsLocalRing (R ⧸ I.ideal n) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk (I.ideal n))
      Ideal.Quotient.mk_surjective
  letI : Nontrivial (R ⧸ I.ideal (n + 1)) :=
    Ideal.Quotient.nontrivial_iff.mpr (I.isProper (n + 1)).ne
  letI : IsLocalRing (R ⧸ I.ideal (n + 1)) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk (I.ideal (n + 1)))
      Ideal.Quotient.mk_surjective
  let h : I.ideal (n + 1) ≤ I.ideal n := I.antitone (Nat.le_succ n)
  let f := Ideal.Quotient.factorₐ Λ h
  refine
    { hom := f
      isLocal := IsLocalHom.of_surjective f.toRingHom (Ideal.Quotient.factor_surjective h)
      residue_comm := ?_ }
  intro x
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
  change I.residueEquiv n (residue _ (f (Ideal.Quotient.mk _ r))) =
    I.residueEquiv (n + 1) (residue _ (Ideal.Quotient.mk _ r))
  simp [f]

end IdealFiltration

/-- A compatible system of objects over the quotients of `R` by an ideal filtration. -/
structure FilteredFormalObject {F : Type uF} [Category.{vF} F]
    (p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k)
    (R : CompleteLocalAlgCat.{u, v, w} Λ k) (I : IdealFiltration R) where
  /-- The object over the `n`-th quotient. -/
  level : ℕ → F
  /-- The level object lies over `R / Iₙ`. -/
  level_eq : ∀ n, p.obj (level n) = I.quotient n
  /-- The transition from level `n + 1` to level `n`. -/
  transition : (n : ℕ) → level (n + 1) ⟶ level n
  /-- Each transition lies over the quotient projection. -/
  transition_lift : ∀ n, p.IsHomLift (I.transition n) (transition n)

namespace FilteredFormalObject

variable {F : Type uF} [Category.{vF} F]
  {p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k}
  {R : CompleteLocalAlgCat.{u, v, w} Λ k} {I : IdealFiltration R}

/-- A morphism of filtered formal objects is a compatible family of morphisms in the fibre over
each quotient `R / Iₙ`. -/
structure Hom (X Y : FilteredFormalObject p R I) where
  /-- Its component at level `n`. -/
  app : (n : ℕ) → X.level n ⟶ Y.level n
  /-- Each component lies over the identity of the corresponding quotient. -/
  app_lift : ∀ n, p.IsHomLift (𝟙 (I.quotient n)) (app n)
  /-- Components commute with transition maps. -/
  naturality : ∀ n, X.transition n ≫ app n = app (n + 1) ≫ Y.transition n

/-- Two morphisms of filtered formal objects agree if all their components agree. -/
@[ext]
theorem Hom.ext {X Y : FilteredFormalObject p R I} {f g : Hom X Y}
    (h : ∀ n, f.app n = g.app n) : f = g := by
  cases f
  cases g
  have := funext h
  cases this
  rfl

/-- Filtered formal objects and their compatible morphisms form a category. -/
instance : Category (FilteredFormalObject p R I) where
  Hom := Hom
  id X :=
    { app := fun n ↦ 𝟙 (X.level n)
      app_lift := fun n ↦ IsHomLift.of_fac p _ _ (X.level_eq n) (X.level_eq n) (by simp)
      naturality := fun n ↦ by simp }
  comp f g :=
    { app := fun n ↦ f.app n ≫ g.app n
      app_lift := fun n ↦ by
        rw [← Category.comp_id (𝟙 (I.quotient n))]
        let := f.app_lift n
        let := g.app_lift n
        infer_instance
      naturality := fun n ↦ by
        rw [← Category.assoc, f.naturality n, Category.assoc, g.naturality n,
          ← Category.assoc] }
  id_comp f := Hom.ext (fun n ↦ by simp)
  comp_id f := Hom.ext (fun n ↦ by simp)
  assoc f g h := Hom.ext (fun n ↦ by simp)

end FilteredFormalObject

def filteredPath {F : Type uF} [Category.{vF} F]
    {p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k}
    {R : CompleteLocalAlgCat.{u, v, w} Λ k} {I : IdealFiltration R}
    (X : FilteredFormalObject p R I) (n m : ℕ) (h : n ≤ m) :
    X.level m ⟶ X.level n :=
  Nat.leRecOn h (fun {_} φ ↦ X.transition _ ≫ φ) (𝟙 (X.level n))

lemma filteredPath_self {F : Type uF} [Category.{vF} F]
    {p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k}
    {R : CompleteLocalAlgCat.{u, v, w} Λ k} {I : IdealFiltration R}
    (X : FilteredFormalObject p R I) (n : ℕ) :
    filteredPath X n n le_rfl = 𝟙 (X.level n) := by unfold filteredPath; exact Nat.leRecOn_self _

lemma filteredPath_succ {F : Type uF} [Category.{vF} F]
    {p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k}
    {R : CompleteLocalAlgCat.{u, v, w} Λ k} {I : IdealFiltration R}
    (X : FilteredFormalObject p R I) (n m : ℕ) (h : n ≤ m) :
    filteredPath X n (m + 1) (h.trans (Nat.le_succ m)) =
      X.transition m ≫ filteredPath X n m h := by unfold filteredPath; exact Nat.leRecOn_succ h _

lemma filteredPath_comp {F : Type uF} [Category.{vF} F]
    {p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k}
    {R : CompleteLocalAlgCat.{u, v, w} Λ k} {I : IdealFiltration R}
    (X : FilteredFormalObject p R I) (n m l : ℕ)
    (hnm : n ≤ m) (hml : m ≤ l) :
    filteredPath X m l hml ≫ filteredPath X n m hnm =
      filteredPath X n l (hnm.trans hml) := by
  induction l, hml using Nat.le_induction with
  | base => simp [filteredPath_self]
  | succ l hl ih =>
      rw [filteredPath_succ X m l hl, Category.assoc, ih,
        filteredPath_succ X n l (hnm.trans hl)]

lemma filteredPath_naturality {F : Type uF} [Category.{vF} F]
    {p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k}
    {R : CompleteLocalAlgCat.{u, v, w} Λ k} {I : IdealFiltration R}
    {X Y : FilteredFormalObject p R I} (f : X ⟶ Y)
    (n m : ℕ) (h : n ≤ m) :
    filteredPath X n m h ≫ f.app n =
      f.app m ≫ filteredPath Y n m h := by
  induction m, h using Nat.le_induction with
  | base => simp [filteredPath_self]
  | succ m hm ih =>
      rw [filteredPath_succ X n m hm, filteredPath_succ Y n m hm,
        Category.assoc, ih, ← Category.assoc, f.naturality m, Category.assoc]

/-- The composite transition map of a filtration from index `m` down to index `n ≤ m`, that is,
the canonical map `R / I m ⟶ R / I n` obtained by composing the one-step transitions. -/
noncomputable def filteredBasePath {R : CompleteLocalAlgCat.{u, v, w} Λ k}
    (I : IdealFiltration R) (n m : ℕ) (h : n ≤ m) :
    I.quotient m ⟶ I.quotient n :=
  Nat.leRecOn h (fun {j} φ ↦ I.transition j ≫ φ) (𝟙 (I.quotient n))

/-- The composite transition map of a filtration at a reflexive inequality is the identity. -/
lemma filteredBasePath_self {R : CompleteLocalAlgCat.{u, v, w} Λ k}
    (I : IdealFiltration R) (n : ℕ) :
    filteredBasePath I n n le_rfl = 𝟙 (I.quotient n) := by
  unfold filteredBasePath
  exact Nat.leRecOn_self _

/-- The composite transition map of a filtration out of a successor index is the one-step
transition followed by the shorter composite. -/
lemma filteredBasePath_succ {R : CompleteLocalAlgCat.{u, v, w} Λ k}
    (I : IdealFiltration R) (n m : ℕ) (h : n ≤ m) :
    filteredBasePath I n (m + 1) (h.trans (Nat.le_succ m)) =
      I.transition m ≫ filteredBasePath I n m h := by
  unfold filteredBasePath
  exact Nat.leRecOn_succ h _

/-- The composite transition map of a filtration is the canonical map of quotients: on the class
of `r : R` it returns the class of `r`. -/
lemma filteredBasePath_mk {R : CompleteLocalAlgCat.{u, v, w} Λ k}
    (I : IdealFiltration R) (n m : ℕ) (h : n ≤ m) (r : R) :
    (filteredBasePath I n m h).hom (Ideal.Quotient.mk (I.ideal m) r) =
      Ideal.Quotient.mk (I.ideal n) r := by
  induction m, h using Nat.le_induction with
  | base =>
      rw [filteredBasePath_self]
      rfl
  | succ m hm ih =>
      rw [filteredBasePath_succ I n m hm, ArtinianLocalAlgCat.comp_hom]
      change (filteredBasePath I n m hm).hom
        ((I.transition m).hom (Ideal.Quotient.mk (I.ideal (m + 1)) r)) = _
      change (filteredBasePath I n m hm).hom (Ideal.Quotient.mk (I.ideal m) r) = _
      exact ih

lemma filteredPath_lift {F : Type uF} [Category.{vF} F]
    {p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k}
    {R : CompleteLocalAlgCat.{u, v, w} Λ k} {I : IdealFiltration R}
    (X : FilteredFormalObject p R I) (n m : ℕ) (h : n ≤ m) :
    p.IsHomLift (filteredBasePath I n m h) (filteredPath X n m h) := by
  induction m, h using Nat.le_induction with
  | base =>
      rw [filteredPath_self, filteredBasePath_self]
      exact IsHomLift.id (X.level_eq n)
  | succ m hm ih =>
      rw [filteredPath_succ X n m hm, filteredBasePath_succ I n m hm]
      let := X.transition_lift m
      let := ih
      infer_instance

def formalPath {F : Type uF} [Category.{vF} F]
    {p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k}
    (X : FormalObject p) (n m : ℕ) (h : n ≤ m) :
    X.level m ⟶ X.level n :=
  Nat.leRecOn h (fun {j} φ ↦ X.transition j ≫ φ) (𝟙 (X.level n))

noncomputable def formalBasePath {R : CompleteLocalAlgCat.{u, v, w} Λ k}
    (n m : ℕ) (h : n ≤ m) :
    AdicTruncation.obj R m ⟶ AdicTruncation.obj R n :=
  Nat.leRecOn h (fun {j} φ ↦ AdicTruncation.transition R j ≫ φ)
    (𝟙 (AdicTruncation.obj R n))

lemma formalPath_self {F : Type uF} [Category.{vF} F]
    {p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k}
    (X : FormalObject p) (n : ℕ) :
    formalPath X n n le_rfl = 𝟙 (X.level n) := by unfold formalPath; exact Nat.leRecOn_self _

lemma formalPath_succ {F : Type uF} [Category.{vF} F]
    {p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k}
    (X : FormalObject p) (n m : ℕ) (h : n ≤ m) :
    formalPath X n (m + 1) (h.trans (Nat.le_succ m)) =
      X.transition m ≫ formalPath X n m h := by unfold formalPath; exact Nat.leRecOn_succ h _

lemma formalPath_comp {F : Type uF} [Category.{vF} F]
    {p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k}
    (X : FormalObject p) (n m l : ℕ)
    (hnm : n ≤ m) (hml : m ≤ l) :
    formalPath X m l hml ≫ formalPath X n m hnm =
      formalPath X n l (hnm.trans hml) := by
  induction l, hml using Nat.le_induction with
  | base => simp [formalPath_self]
  | succ l hl ih =>
      rw [formalPath_succ X m l hl, Category.assoc, ih,
        formalPath_succ X n l (hnm.trans hl)]

lemma formalPath_naturality {F : Type uF} [Category.{vF} F]
    {p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k}
    {X Y : FormalObject p} (f : X ⟶ Y)
    (n m : ℕ) (h : n ≤ m) :
    formalPath X n m h ≫ f.app n =
      f.app m ≫ formalPath Y n m h := by
  induction m, h using Nat.le_induction with
  | base => simp [formalPath_self]
  | succ m hm ih =>
      rw [formalPath_succ X n m hm, formalPath_succ Y n m hm,
        Category.assoc, ih, ← Category.assoc, f.naturality m, Category.assoc]

private lemma formalBasePath_self {R : CompleteLocalAlgCat.{u, v, w} Λ k}
    (n : ℕ) : formalBasePath (R := R) n n le_rfl =
      𝟙 (AdicTruncation.obj R n) := by unfold formalBasePath; exact Nat.leRecOn_self _

private lemma formalBasePath_succ {R : CompleteLocalAlgCat.{u, v, w} Λ k}
    (n m : ℕ) (h : n ≤ m) :
    formalBasePath (R := R) n (m + 1) (h.trans (Nat.le_succ m)) =
      AdicTruncation.transition R m ≫ formalBasePath (R := R) n m h := by
  unfold formalBasePath
  exact Nat.leRecOn_succ h _

lemma formalBasePath_mk {R : CompleteLocalAlgCat.{u, v, w} Λ k}
    (n m : ℕ) (h : n ≤ m) (r : R) :
    (formalBasePath (R := R) n m h).hom
      (Ideal.Quotient.mk (AdicTruncation.ideal R m) r) =
      Ideal.Quotient.mk (AdicTruncation.ideal R n) r := by
  induction m, h using Nat.le_induction with
  | base =>
      rw [formalBasePath_self]
      rfl
  | succ m hm ih =>
      rw [formalBasePath_succ (R := R) n m hm, ArtinianLocalAlgCat.comp_hom]
      change (formalBasePath (R := R) n m hm).hom
        ((AdicTruncation.transition R m).hom
          (Ideal.Quotient.mk (AdicTruncation.ideal R (m + 1)) r)) = _
      change (formalBasePath (R := R) n m hm).hom
        (Ideal.Quotient.mk (AdicTruncation.ideal R m) r) = _
      exact ih

lemma formalPath_lift {F : Type uF} [Category.{vF} F]
    {p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k}
    (X : FormalObject p) (n m : ℕ) (h : n ≤ m) :
    p.IsHomLift (formalBasePath (R := X.base) n m h) (formalPath X n m h) := by
  induction m, h using Nat.le_induction with
  | base =>
      rw [formalPath_self, formalBasePath_self]
      exact IsHomLift.id (X.level_eq n)
  | succ m hm ih =>
      rw [formalPath_succ X n m hm, formalBasePath_succ (R := X.base) n m hm]
      let : p.IsHomLift (AdicTruncation.transition X.base m) (X.transition m) := by
        simpa only [AdicTruncation.transitionNat] using X.transition_lift m
      let := ih
      infer_instance

/-- An index of the filtration whose ideal is contained in the `n`-th power of the maximal ideal
and which is at least `n`. -/
noncomputable def toAdicIndex {R : CompleteLocalAlgCat.{u, v, w} Λ k}
    (I : IdealFiltration R) (n : ℕ) : ℕ := by
  classical exact max n (Nat.find (I.le_pow n))

/-- The ideal at `toAdicIndex I n` is contained in the `n`-th adic ideal. -/
lemma toAdicIndex_le {R : CompleteLocalAlgCat.{u, v, w} Λ k}
    (I : IdealFiltration R) (n : ℕ) :
    I.ideal (toAdicIndex I n) ≤ AdicTruncation.ideal R n := by
  classical
  unfold toAdicIndex
  exact (I.antitone (Nat.le_max_right _ _)).trans (Nat.find_spec (I.le_pow n))

/-- `toAdicIndex I` is monotone. -/
lemma toAdicIndex_mono {R : CompleteLocalAlgCat.{u, v, w} Λ k}
    (I : IdealFiltration R) : Monotone (toAdicIndex I) := by
  classical
  intro n m h
  unfold toAdicIndex
  exact max_le_max h (Nat.find_mono fun j hj ↦
    hj.trans (Ideal.pow_le_pow_right (Nat.add_le_add_right h 1)))

noncomputable def toIdealIndex {R : CompleteLocalAlgCat.{u, v, w} Λ k}
    (I : IdealFiltration R) (n : ℕ) : ℕ := by
  classical exact max n (Nat.find (I.pow_le n))

lemma toIdealIndex_le {R : CompleteLocalAlgCat.{u, v, w} Λ k}
    (I : IdealFiltration R) (n : ℕ) :
    AdicTruncation.ideal R (toIdealIndex I n) ≤ I.ideal n := by
  classical
  unfold toIdealIndex
  exact (Ideal.pow_le_pow_right (Nat.add_le_add_right (Nat.le_max_right _ _) 1)).trans
    (Nat.find_spec (I.pow_le n))

lemma toIdealIndex_mono {R : CompleteLocalAlgCat.{u, v, w} Λ k}
    (I : IdealFiltration R) : Monotone (toIdealIndex I) := by
  classical
  intro n m h
  unfold toIdealIndex
  exact max_le_max h (Nat.find_mono fun j hj ↦ hj.trans (I.antitone h))

noncomputable def idealToAdic {R : CompleteLocalAlgCat.{u, v, w} Λ k}
    (I : IdealFiltration R) {m n : ℕ}
    (h : I.ideal m ≤ AdicTruncation.ideal R n) :
    I.quotient m ⟶ AdicTruncation.obj R n := by
  letI : Nontrivial (R ⧸ I.ideal m) :=
    Ideal.Quotient.nontrivial_iff.mpr (I.isProper m).ne
  letI : IsLocalRing (R ⧸ I.ideal m) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk (I.ideal m))
      Ideal.Quotient.mk_surjective
  letI : Nontrivial (R ⧸ AdicTruncation.ideal R n) :=
    Ideal.Quotient.nontrivial_iff.mpr
      ((Ideal.pow_le_self (Nat.succ_ne_zero n)).trans_lt
        (maximalIdeal.isMaximal R).lt_top).ne
  letI : IsLocalRing (R ⧸ AdicTruncation.ideal R n) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk (AdicTruncation.ideal R n))
      Ideal.Quotient.mk_surjective
  let f := Ideal.Quotient.factorₐ Λ h
  refine
    { hom := f
      isLocal := IsLocalHom.of_surjective f.toRingHom (Ideal.Quotient.factor_surjective h)
      residue_comm := ?_ }
  intro x
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
  change AdicTruncation.residueEquiv R n
      (residue _ (f (Ideal.Quotient.mk _ r))) =
    I.residueEquiv m (residue _ (Ideal.Quotient.mk _ r))
  simp [f]

noncomputable def adicToIdeal {R : CompleteLocalAlgCat.{u, v, w} Λ k}
    (I : IdealFiltration R) {m n : ℕ}
    (h : AdicTruncation.ideal R m ≤ I.ideal n) :
    AdicTruncation.obj R m ⟶ I.quotient n := by
  letI : Nontrivial (R ⧸ I.ideal n) :=
    Ideal.Quotient.nontrivial_iff.mpr (I.isProper n).ne
  letI : IsLocalRing (R ⧸ I.ideal n) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk (I.ideal n))
      Ideal.Quotient.mk_surjective
  letI : Nontrivial (R ⧸ AdicTruncation.ideal R m) :=
    Ideal.Quotient.nontrivial_iff.mpr
      ((Ideal.pow_le_self (Nat.succ_ne_zero m)).trans_lt
        (maximalIdeal.isMaximal R).lt_top).ne
  letI : IsLocalRing (R ⧸ AdicTruncation.ideal R m) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk (AdicTruncation.ideal R m))
      Ideal.Quotient.mk_surjective
  let f := Ideal.Quotient.factorₐ Λ h
  refine
    { hom := f
      isLocal := IsLocalHom.of_surjective f.toRingHom (Ideal.Quotient.factor_surjective h)
      residue_comm := ?_ }
  intro x
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
  change I.residueEquiv n
      (residue _ (f (Ideal.Quotient.mk _ r))) =
    AdicTruncation.residueEquiv R m (residue _ (Ideal.Quotient.mk _ r))
  simp [f]

lemma idealToAdic_mk {R : CompleteLocalAlgCat.{u, v, w} Λ k}
    (I : IdealFiltration R) {m n : ℕ}
    (h : I.ideal m ≤ AdicTruncation.ideal R n) (r : R) :
    (idealToAdic I h).hom (Ideal.Quotient.mk (I.ideal m) r) =
      Ideal.Quotient.mk (AdicTruncation.ideal R n) r := rfl

lemma adicToIdeal_mk {R : CompleteLocalAlgCat.{u, v, w} Λ k}
    (I : IdealFiltration R) {m n : ℕ}
    (h : AdicTruncation.ideal R m ≤ I.ideal n) (r : R) :
    (adicToIdeal I h).hom (Ideal.Quotient.mk (AdicTruncation.ideal R m) r) =
      Ideal.Quotient.mk (I.ideal n) r := rfl

private lemma idealToAdic_square {R : CompleteLocalAlgCat.{u, v, w} Λ k}
    (I : IdealFiltration R) (n m : ℕ) (h : n ≤ m) :
    idealToAdic I (toAdicIndex_le I m) ≫ formalBasePath (R := R) n m h =
      filteredBasePath I (toAdicIndex I n) (toAdicIndex I m)
          (toAdicIndex_mono I h) ≫ idealToAdic I (toAdicIndex_le I n) := by
  apply ArtinianLocalAlgCat.hom_ext
  apply AlgHom.ext
  intro x
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
  change (formalBasePath (R := R) n m h).hom
      ((idealToAdic I (toAdicIndex_le I m)).hom
        (Ideal.Quotient.mk (I.ideal (toAdicIndex I m)) r)) =
    (idealToAdic I (toAdicIndex_le I n)).hom
      ((filteredBasePath I (toAdicIndex I n) (toAdicIndex I m)
        (toAdicIndex_mono I h)).hom
          (Ideal.Quotient.mk (I.ideal (toAdicIndex I m)) r))
  rw [idealToAdic_mk, formalBasePath_mk, filteredBasePath_mk, idealToAdic_mk]

private lemma adicToIdeal_square {R : CompleteLocalAlgCat.{u, v, w} Λ k}
    (I : IdealFiltration R) (n m : ℕ) (h : n ≤ m) :
    adicToIdeal I (toIdealIndex_le I m) ≫ filteredBasePath I n m h =
      formalBasePath (R := R) (toIdealIndex I n) (toIdealIndex I m)
          (toIdealIndex_mono I h) ≫ adicToIdeal I (toIdealIndex_le I n) := by
  apply ArtinianLocalAlgCat.hom_ext
  apply AlgHom.ext
  intro x
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
  change (filteredBasePath I n m h).hom
      ((adicToIdeal I (toIdealIndex_le I m)).hom
        (Ideal.Quotient.mk (AdicTruncation.ideal R (toIdealIndex I m)) r)) =
    (adicToIdeal I (toIdealIndex_le I n)).hom
      ((formalBasePath (R := R) (toIdealIndex I n) (toIdealIndex I m)
        (toIdealIndex_mono I h)).hom
          (Ideal.Quotient.mk (AdicTruncation.ideal R (toIdealIndex I m)) r))
  rw [adicToIdeal_mk, filteredBasePath_mk, formalBasePath_mk, adicToIdeal_mk]

/-- Lifts compose, and the composite lifts any morphism equal to the composite of the bases. -/
private lemma isHomLift_comp_of_eq {F : Type uF} [Category.{vF} F]
    {p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k} {R S T : ArtinianLocalAlgCat.{u, v, w} Λ k}
    {a b c : F} {f : R ⟶ S} {g : S ⟶ T} {h : R ⟶ T} {φ : a ⟶ b} {ψ : b ⟶ c}
    (hφ : p.IsHomLift f φ) (hψ : p.IsHomLift g ψ) (hfg : f ≫ g = h) :
    p.IsHomLift h (φ ≫ ψ) := by
  subst hfg
  infer_instance

lemma toAdicPsi_lift {F : Type uF} [Category.{vF} F]
    (p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k)
    (R : CompleteLocalAlgCat.{u, v, w} Λ k) (I : IdealFiltration R)
    (hp : IsCofiberedInGroupoids p) (X : FilteredFormalObject p R I)
    (n : ℕ) :
    p.IsHomLift (idealToAdic I (toAdicIndex_le I (n + 1)) ≫
        AdicTruncation.transition R n)
      (filteredPath X (toAdicIndex I n) (toAdicIndex I (n + 1))
          (toAdicIndex_mono I (Nat.le_succ n)) ≫
        chosenPushforwardMap hp (idealToAdic I (toAdicIndex_le I n))
          (X.level (toAdicIndex I n)) (X.level_eq (toAdicIndex I n))) := by
  have htr : formalBasePath (R := R) n (n + 1) (Nat.le_succ n) =
      AdicTruncation.transition R n := by
    rw [formalBasePath_succ (R := R) n n le_rfl, formalBasePath_self,
      Category.comp_id]
  have heq := idealToAdic_square I n (n + 1) (Nat.le_succ n)
  rw [htr] at heq
  exact isHomLift_comp_of_eq
    (filteredPath_lift X (toAdicIndex I n) (toAdicIndex I (n + 1))
      (toAdicIndex_mono I (Nat.le_succ n)))
    (chosenPushforwardMap_lift hp (idealToAdic I (toAdicIndex_le I n))
      (X.level (toAdicIndex I n)) (X.level_eq (toAdicIndex I n))) heq.symm

lemma toIdealPsi_lift {F : Type uF} [Category.{vF} F]
    (p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k)
    (R : CompleteLocalAlgCat.{u, v, w} Λ k) (I : IdealFiltration R)
    (hp : IsCofiberedInGroupoids p) (X : FormalObject p)
    (hX : X.base = R) (n : ℕ) :
    p.IsHomLift (adicToIdeal I (toIdealIndex_le I (n + 1)) ≫ I.transition n)
      (formalPath X (toIdealIndex I n) (toIdealIndex I (n + 1))
          (toIdealIndex_mono I (Nat.le_succ n)) ≫
        chosenPushforwardMap hp (adicToIdeal I (toIdealIndex_le I n))
          (X.level (toIdealIndex I n))
          (by simpa only [hX, AdicTruncation.functor] using X.level_eq (toIdealIndex I n))) := by
  cases hX
  have htr : filteredBasePath I n (n + 1) (Nat.le_succ n) = I.transition n := by
    rw [filteredBasePath_succ I n n le_rfl, filteredBasePath_self,
      Category.comp_id]
  have heq := adicToIdeal_square I n (n + 1) (Nat.le_succ n)
  rw [htr] at heq
  exact isHomLift_comp_of_eq
    (formalPath_lift X (toIdealIndex I n) (toIdealIndex I (n + 1))
      (toIdealIndex_mono I (Nat.le_succ n)))
    (chosenPushforwardMap_lift hp (adicToIdeal I (toIdealIndex_le I n))
      (X.level (toIdealIndex I n)) (X.level_eq (toIdealIndex I n))) heq.symm

end

end Deformation
