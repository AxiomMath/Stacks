module

public import Mathlib.CategoryTheory.FiberedCategory.BasedCategory
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
public import StacksFrontier.CategoryTheory.FiberedCategory.HomLift
public import StacksFrontier.Deformation.Basic
public import StacksFrontier.Deformation.Cofibered
public import StacksFrontier.Deformation.Completed.Basic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Formal objects and completion categories

A formal object of a category cofibered in groupoids over the base category is
a compatible system of objects over an inverse system of Artinian quotients. This file defines
formal objects, assembles them into the completion of a cofibered category, and extends a morphism
and a 2-morphism of cofibered categories to the completions.

## Main definitions

* `AdicTruncation.obj` is the Artinian local algebra `R / m_R ^ (n + 1)`.
* `FormalObject` is a compatible system of objects over these truncations.
* `FormalObject.Hom` is a compatible family of morphisms of such systems.
* `completionMap` is the induced based functor on formal objects.
* `completionNatTrans` is the induced based natural
  transformation.

## Main results

* `Deformation.adicTruncationMap_mk` computes the `n`-th adic truncation of a morphism of
  complete local algebras on representatives.
* `formalObjectProjection_isCofiberedInGroupoids` says that the projection from
  formal objects to their complete local base is cofibered in groupoids.
* The componentwise results describe its action on objects and morphisms.
* `completionNatTrans_app_base` and `completionNatTrans_app_level` describe its components.
* `completionMap_id` and `completionMap_comp` say that completion preserves identity morphisms
  and composition of morphisms of cofibered categories.
* `completionNatTrans_id` and `completionNatTrans_comp` say that completion preserves identity
  two-morphisms and vertical composition of two-morphisms. Together with the previous two, these
  are the statement that completion is a functor of two-categories.

## Implementation notes

### Formal objects of a category cofibered in groupoids

Levels are indexed by `n : ℕ` and use the positive power `n + 1`.  Thus level zero is the
source's first nonzero quotient `R / m_R`; the literal zeroth power would give the zero ring,
which is not an object of the category of local algebras with residue field `k`.

An object at each level is accompanied by an equality identifying its image under `p` with the
corresponding truncation. The transition maps and components of morphisms carry
`Functor.IsHomLift`, recording exactly which quotient map they lie over.

### Completion of a category cofibered in groupoids

The completion functor `\widehat p` of the source is the projection
`FormalObject.projection` defined with formal objects.

### Completion of a morphism of cofibered categories

A functor over the base is represented by Mathlib's `BasedFunctor`.  The definition fixes the
complete local algebra and applies its underlying functor to every level and transition map.

### Completion of a two-morphism

The based natural transformation records that each component lies over the identity of the
complete local algebra. The component equations include the equality transports arising from
the levelwise completion functors.

### Completion as a functor of two-categories

Mathlib's two-category of based categories over a fixed base is
`CategoryTheory.BasedCategory`, which is a strict bicategory. Completion is not a morphism inside
one such bicategory: it changes both the base, from Artinian local algebras to complete local
algebras, and the universe of objects, since `FormalObject p` is larger than `F`. So the content
of the statement that completion is a functor of two-categories is recorded as the four
functoriality equations `completionMap_id`, `completionMap_comp`, `completionNatTrans_id` and
`completionNatTrans_comp`, rather than as a single packaged declaration.

## References

* [Stacks Project, Tag 06H3](https://stacks.math.columbia.edu/tag/06H3)
* [Stacks Project, Tag 06H4](https://stacks.math.columbia.edu/tag/06H4)
* [Stacks Project, Tag 06H9](https://stacks.math.columbia.edu/tag/06H9)
-/

@[expose] public section

namespace Deformation

/-! ### Formal objects of a category cofibered in groupoids -/

section
open CategoryTheory
open IsLocalRing
universe u v w uF vF


variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]

namespace AdicTruncation

/-- The positive power of the maximal ideal used at level `n` of a formal object. -/
abbrev ideal (R : CompleteLocalAlgCat.{u, v, w} Λ k) (n : ℕ) : Ideal R :=
  maximalIdeal R ^ (n + 1)

/-- The residue-field map induced by the quotient `R → R / m_R ^ (n + 1)` is bijective. -/
theorem residueMap_bijective (R : CompleteLocalAlgCat.{u, v, w} Λ k) (n : ℕ) :
    let I := ideal R n
    letI : Nontrivial (R ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr
      ((Ideal.pow_le_self (Nat.succ_ne_zero n)).trans_lt (maximalIdeal.isMaximal R).lt_top).ne
    letI : IsLocalRing (R ⧸ I) :=
      IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
    let q := Ideal.Quotient.mkₐ Λ I
    letI : IsLocalHom q := ⟨(IsLocalHom.of_surjective q.toRingHom
      Ideal.Quotient.mk_surjective).map_nonunit⟩
    Function.Bijective (ResidueField.mapAlgHom q) := by
  dsimp only
  let : Nontrivial (R ⧸ ideal R n) := Ideal.Quotient.nontrivial_iff.mpr
    ((Ideal.pow_le_self (Nat.succ_ne_zero n)).trans_lt (maximalIdeal.isMaximal R).lt_top).ne
  let : IsLocalRing (R ⧸ ideal R n) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk (ideal R n)) Ideal.Quotient.mk_surjective
  let q := Ideal.Quotient.mkₐ Λ (ideal R n)
  let : IsLocalHom q := ⟨(IsLocalHom.of_surjective q.toRingHom
    Ideal.Quotient.mk_surjective).map_nonunit⟩
  refine ⟨RingHom.injective _, ?_⟩
  intro y
  obtain ⟨x, rfl⟩ := residue_surjective y
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
  exact ⟨residue R r, by simp⟩

/-- The canonical identification of the residue field of an adic truncation with `k`. -/
noncomputable def residueEquiv (R : CompleteLocalAlgCat.{u, v, w} Λ k) (n : ℕ) :
    let I := ideal R n
    letI : Nontrivial (R ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr
      ((Ideal.pow_le_self (Nat.succ_ne_zero n)).trans_lt (maximalIdeal.isMaximal R).lt_top).ne
    letI : IsLocalRing (R ⧸ I) :=
      IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
    ResidueField (R ⧸ I) ≃ₐ[Λ] k := by
  dsimp only
  letI : Nontrivial (R ⧸ ideal R n) := Ideal.Quotient.nontrivial_iff.mpr
    ((Ideal.pow_le_self (Nat.succ_ne_zero n)).trans_lt (maximalIdeal.isMaximal R).lt_top).ne
  letI : IsLocalRing (R ⧸ ideal R n) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk (ideal R n)) Ideal.Quotient.mk_surjective
  let q := Ideal.Quotient.mkₐ Λ (ideal R n)
  letI : IsLocalHom q := ⟨(IsLocalHom.of_surjective q.toRingHom
    Ideal.Quotient.mk_surjective).map_nonunit⟩
  exact (AlgEquiv.ofBijective (ResidueField.mapAlgHom q)
    (residueMap_bijective R n)).symm.trans R.residueEquiv

/-- `residueEquiv R n` sends the residue of the class of `r` in `R ⧸ ideal R n` to the image of
the residue of `r` under `R.residueEquiv`. -/
@[simp]
theorem residueEquiv_residue_mk (R : CompleteLocalAlgCat.{u, v, w} Λ k) (n : ℕ) (r : R) :
    let I := ideal R n
    letI : Nontrivial (R ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr
      ((Ideal.pow_le_self (Nat.succ_ne_zero n)).trans_lt (maximalIdeal.isMaximal R).lt_top).ne
    letI : IsLocalRing (R ⧸ I) :=
      IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
    residueEquiv R n (residue (R ⧸ I) (Ideal.Quotient.mk I r)) =
      R.residueEquiv (residue R r) := by
  dsimp only
  let : Nontrivial (R ⧸ ideal R n) := Ideal.Quotient.nontrivial_iff.mpr
    ((Ideal.pow_le_self (Nat.succ_ne_zero n)).trans_lt (maximalIdeal.isMaximal R).lt_top).ne
  let : IsLocalRing (R ⧸ ideal R n) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk (ideal R n)) Ideal.Quotient.mk_surjective
  let q := Ideal.Quotient.mkₐ Λ (ideal R n)
  let : IsLocalHom q := ⟨(IsLocalHom.of_surjective q.toRingHom
    Ideal.Quotient.mk_surjective).map_nonunit⟩
  show R.residueEquiv
    ((AlgEquiv.ofBijective (ResidueField.mapAlgHom q) (residueMap_bijective R n)).symm
      (ResidueField.mapAlgHom q (residue R r))) = _
  exact congrArg R.residueEquiv
    ((AlgEquiv.ofBijective (ResidueField.mapAlgHom q)
      (residueMap_bijective R n)).symm_apply_apply (residue R r))

/-- The Artinian local algebra obtained from `R` by quotienting by
`m_R ^ (n + 1)`. -/
@[ega "0 19.5.6.2" "special case"]
noncomputable def obj (R : CompleteLocalAlgCat.{u, v, w} Λ k) (n : ℕ) :
    ArtinianLocalAlgCat.{u, v, w} Λ k := by
  let I := ideal R n
  have hI : I < ⊤ :=
    (Ideal.pow_le_self (Nat.succ_ne_zero n)).trans_lt (maximalIdeal.isMaximal R).lt_top
  letI : Nontrivial (R ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hI.ne
  letI : IsLocalRing (R ⧸ I) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  letI : IsArtinianRing (R ⧸ I) := by
    apply IsLocalRing.quotient_artinian_of_mem_minimalPrimes_of_isLocalRing
    refine ⟨⟨inferInstance, Ideal.pow_le_self (Nat.succ_ne_zero n)⟩, fun q hq _ ↦ ?_⟩
    exact (Ideal.IsPrime.pow_le_iff (hP := hq.1) (Nat.succ_ne_zero n)).mp hq.2
  exact
    { carrier := R ⧸ I
      residueEquiv := residueEquiv R n }

/-- The projection from the `(n + 1)`-st positive adic truncation to the `n`-th one. -/
noncomputable def transition (R : CompleteLocalAlgCat.{u, v, w} Λ k) (n : ℕ) :
    obj R (n + 1) ⟶ obj R n := by
  letI : Nontrivial (R ⧸ ideal R n) := Ideal.Quotient.nontrivial_iff.mpr
    ((Ideal.pow_le_self (Nat.succ_ne_zero n)).trans_lt (maximalIdeal.isMaximal R).lt_top).ne
  letI : IsLocalRing (R ⧸ ideal R n) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk (ideal R n)) Ideal.Quotient.mk_surjective
  letI : Nontrivial (R ⧸ ideal R (n + 1)) := Ideal.Quotient.nontrivial_iff.mpr
    ((Ideal.pow_le_self (Nat.succ_ne_zero (n + 1))).trans_lt
      (maximalIdeal.isMaximal R).lt_top).ne
  letI : IsLocalRing (R ⧸ ideal R (n + 1)) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk (ideal R (n + 1)))
      Ideal.Quotient.mk_surjective
  let h : ideal R (n + 1) ≤ ideal R n :=
    Ideal.pow_le_pow_right (Nat.le_succ (n + 1))
  let f := Ideal.Quotient.factorₐ Λ h
  refine
    { hom := f
      isLocal := IsLocalHom.of_surjective f.toRingHom (Ideal.Quotient.factor_surjective h)
      residue_comm := ?_ }
  intro x
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
  change residueEquiv R n (residue _ (f (Ideal.Quotient.mk _ r))) =
    residueEquiv R (n + 1) (residue _ (Ideal.Quotient.mk _ r))
  simp [f]

/-- A morphism of complete local algebras induces a morphism on every positive adic
truncation. -/
noncomputable def map {R S : CompleteLocalAlgCat.{u, v, w} Λ k} (a : R ⟶ S) (n : ℕ) :
    obj R n ⟶ obj S n := by
  let IR := ideal R n
  let IS := ideal S n
  have h : IR ≤ IS.comap a.hom := by
    let : IsLocalHom a.hom.toRingHom := a.isLocal
    rw [← Ideal.map_le_iff_le_comap, Ideal.map_pow]
    exact Ideal.pow_right_mono (map_maximalIdeal_le a.hom.toRingHom) _
  let f := Ideal.quotientMapₐ IS a.hom h
  letI : Nontrivial (R ⧸ IR) := Ideal.Quotient.nontrivial_iff.mpr
    ((Ideal.pow_le_self (Nat.succ_ne_zero n)).trans_lt (maximalIdeal.isMaximal R).lt_top).ne
  letI : IsLocalRing (R ⧸ IR) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk IR) Ideal.Quotient.mk_surjective
  letI : Nontrivial (S ⧸ IS) := Ideal.Quotient.nontrivial_iff.mpr
    ((Ideal.pow_le_self (Nat.succ_ne_zero n)).trans_lt (maximalIdeal.isMaximal S).lt_top).ne
  letI : IsLocalRing (S ⧸ IS) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk IS) Ideal.Quotient.mk_surjective
  have hf : IsLocalHom f.toRingHom := by
    constructor
    intro x hx
    obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective x
    subst x
    have hqS : IsLocalHom (Ideal.Quotient.mk IS) :=
      IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
    exact (Ideal.Quotient.mk IR).isUnit_map
      (a.isLocal.map_nonunit r (hqS.map_nonunit (a.hom r) hx))
  exact
    { hom := f
      isLocal := hf
      residue_comm := fun x ↦ by
        obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
        change residueEquiv S n (residue _ (Ideal.Quotient.mk IS (a.hom r))) =
          residueEquiv R n (residue _ (Ideal.Quotient.mk IR r))
        dsimp only [IR, IS]
        rw [residueEquiv_residue_mk, residueEquiv_residue_mk]
        exact a.residue_comm r }

/-- Taking the `n`-th positive adic quotient is a functor from complete local algebras to
Artinian local algebras. -/
@[implicit_reducible, ega "0 19.5.6.2" "special case"]
noncomputable def functor (n : ℕ) :
    CompleteLocalAlgCat.{u, v, w} Λ k ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k where
  obj R := obj R n
  map a := map a n
  map_id R := by
    apply ArtinianLocalAlgCat.hom_ext
    apply AlgHom.ext
    intro x
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
    change Ideal.Quotient.mk _ r = Ideal.Quotient.mk _ r
    rfl
  map_comp a b := by
    apply ArtinianLocalAlgCat.hom_ext
    apply AlgHom.ext
    intro x
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
    change Ideal.Quotient.mk _ (b.hom (a.hom r)) =
      Ideal.Quotient.mk _ (b.hom (a.hom r))
    rfl

/-- The quotient projections form a natural transformation between consecutive adic
truncation functors. -/
noncomputable def transitionNat (n : ℕ) : functor (Λ := Λ) (k := k) (n + 1) ⟶ functor n where
  app R := transition R n
  naturality R S a := by
    apply ArtinianLocalAlgCat.hom_ext
    apply AlgHom.ext
    intro x
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
    change Ideal.Quotient.mk _ (a.hom r) = Ideal.Quotient.mk _ (a.hom r)
    rfl

end AdicTruncation

/-- The `n`-th adic truncation of a morphism of complete local algebras, computed on
representatives. -/
theorem adicTruncationMap_mk
    {R S : CompleteLocalAlgCat.{u, v, w} Λ k} (f : R ⟶ S)
    (n : ℕ) (r : R) :
    ((AdicTruncation.functor n).map f).hom
        (Ideal.Quotient.mk (AdicTruncation.ideal R n) r : AdicTruncation.obj R n) =
      (Ideal.Quotient.mk (AdicTruncation.ideal S n) (f.hom r) : AdicTruncation.obj S n) := by
  rfl

/-- A formal object of a category `F` over `𝒞_Λ` consists of a complete local algebra `R`,
an object of `F` over each positive adic truncation of `R`, and transition maps lying over the
quotient projections. -/
@[stacks 06H3 "objects", sga "7 VI 1.15"]
structure FormalObject {F : Type uF} [Category.{vF} F]
    (p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k) where
  /-- The complete local algebra underlying the formal object. -/
  base : CompleteLocalAlgCat.{u, v, w} Λ k
  /-- Its object over `R / m_R ^ (n + 1)`. -/
  level : ℕ → F
  /-- The level object lies over the corresponding adic truncation. -/
  level_eq : ∀ n, p.obj (level n) = (AdicTruncation.functor n).obj base
  /-- The transition from level `n + 1` to level `n`. -/
  transition : (n : ℕ) → level (n + 1) ⟶ level n
  /-- Each transition lies over the corresponding quotient projection. -/
  transition_lift : ∀ n,
    p.IsHomLift ((AdicTruncation.transitionNat n).app base) (transition n)

namespace FormalObject

variable {F : Type uF} [Category.{vF} F]
  {p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k}

/-- A morphism of formal objects is a morphism of their complete local bases together with a
compatible family of morphisms over its maps on all adic truncations. -/
@[stacks 06H3 "morphisms"]
structure Hom (X Y : FormalObject p) where
  /-- The morphism between the underlying complete local algebras. -/
  base : X.base ⟶ Y.base
  /-- The morphism between the objects at level `n`. -/
  app : (n : ℕ) → X.level n ⟶ Y.level n
  /-- The level-`n` component lies over the map induced by `base`. -/
  app_lift : ∀ n, p.IsHomLift ((AdicTruncation.functor n).map base) (app n)
  /-- The level maps commute with the transition maps. -/
  naturality : ∀ n, X.transition n ≫ app n = app (n + 1) ≫ Y.transition n

/-- Two morphisms of formal objects are equal when their base maps and all level maps agree. -/
@[ext]
theorem Hom.ext {X Y : FormalObject p} {f g : Hom X Y} (hbase : f.base = g.base)
    (happ : ∀ n, f.app n = g.app n) : f = g := by
  cases f; cases g; cases hbase; cases funext happ; rfl

/-- **Formal objects agreeing on base, levels and transitions are equal.** The remaining two
fields, `level_eq` and `transition_lift`, are propositions about those three.

Deliberately not `@[ext]`: `Deformation.FormalObject.Hom.ext` carries that attribute, and
tagging the object-level lemma too would change what the `ext` tactic does in every module
downstream of this one. -/
theorem ext {ξ η : FormalObject p} (hbase : ξ.base = η.base)
    (hlevel : ∀ n, ξ.level n = η.level n)
    (htransition : ∀ n, ξ.transition n =
      eqToHom (hlevel (n + 1)) ≫ η.transition n ≫ eqToHom (hlevel n).symm) : ξ = η := by
  cases ξ with
  | mk b l le t tl =>
    cases η with
    | mk b' l' le' t' tl' =>
      dsimp only at hbase hlevel htransition
      subst b'
      have hll := funext hlevel
      subst l'
      simp only [eqToHom_refl, Category.id_comp, Category.comp_id] at htransition
      have htt := funext htransition
      subst t'
      rfl

/-- The identity morphism of a formal object. -/
def Hom.id (X : FormalObject p) : Hom X X :=
  { base := 𝟙 X.base
    app := fun n ↦ 𝟙 (X.level n)
    app_lift := fun n ↦ by
      apply IsHomLift.of_fac p _ _ (X.level_eq n) (X.level_eq n)
      simp
    naturality := fun n ↦ by simp }

/-- Composition of morphisms of formal objects. -/
def Hom.comp {X Y Z : FormalObject p} (f : Hom X Y) (g : Hom Y Z) : Hom X Z :=
  { base := f.base ≫ g.base
    app := fun n ↦ f.app n ≫ g.app n
    app_lift := fun n ↦ by
      rw [Functor.map_comp]
      let := f.app_lift n
      let := g.app_lift n
      infer_instance
    naturality := fun n ↦ by
      rw [← Category.assoc, f.naturality n, Category.assoc, g.naturality n,
        ← Category.assoc] }

/-- Formal objects and their compatible families of morphisms form a category. -/
@[stacks 06H3 "category structure"]
instance instCategory : Category (FormalObject p) where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp
  id_comp f := by
    exact Hom.ext (by simp [Hom.id, Hom.comp]) (fun n ↦ by simp [Hom.id, Hom.comp])
  comp_id f := by
    exact Hom.ext (by simp [Hom.id, Hom.comp]) (fun n ↦ by simp [Hom.id, Hom.comp])
  assoc f g h := by
    exact Hom.ext (by simp [Hom.comp]) (fun n ↦ by simp [Hom.comp])

/-- The canonical functor from formal objects to their underlying complete local algebras. -/
@[implicit_reducible, stacks 06H5 "the completion of a category cofibered in groupoids"]
def projection : FormalObject p ⥤ CompleteLocalAlgCat.{u, v, w} Λ k where
  obj X := X.base
  map f := f.base
  map_id _ := rfl
  map_comp _ _ := rfl

/-- `projection` sends a formal object to its base. -/
@[simp]
theorem projection_obj (X : FormalObject p) : projection.obj X = X.base := rfl

/-- `projection` sends a morphism of formal objects to its base morphism. -/
@[simp]
theorem projection_map {X Y : FormalObject p} (f : X ⟶ Y) : projection.map f = f.base := rfl

end FormalObject

end

/-! ### Completion of a category cofibered in groupoids -/

section
open CategoryTheory
universe u v w uF vF


variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]

/-- Let `φ : a ⟶ x` lift `f : R ⟶ T` and `ψ : b ⟶ x` lift `g : S ⟶ T` along `q`, and let
`d : S ⟶ R` factor `g` through `f`. Transporting `d` along the identifications of the images
of the two domains and composing with `q.map φ` returns `q.map ψ`. -/
public lemma map_comp_eq_of_lifts
    {C D : Type*} [Category C] [Category D] (q : C ⥤ D)
    {R S T : D} {a b x : C} (f : R ⟶ T) (g : S ⟶ T)
    (φ : a ⟶ x) (ψ : b ⟶ x) [q.IsHomLift f φ] [q.IsHomLift g ψ]
    (d : S ⟶ R) (hd : d ≫ f = g) :
    (eqToHom (IsHomLift.domain_eq q g ψ) ≫ d ≫
      eqToHom (IsHomLift.domain_eq q f φ).symm) ≫ q.map φ = q.map ψ := by
  rw [IsHomLift.fac' q f φ, IsHomLift.fac' q g ψ]
  simpa using congrArg (fun e ↦
    eqToHom (IsHomLift.domain_eq q g ψ) ≫ e ≫
      eqToHom (IsHomLift.codomain_eq q g ψ).symm) hd



private lemma hom_ext_of_fibered
    {C D : Type*} [Category C] [Category D] (q : C ⥤ D)
    (hq : q.IsFiberedInGroupoids) {x y z : C} (φ : y ⟶ x)
    (a b : z ⟶ y) (hmap : q.map a = q.map b) (hcomp : a ≫ φ = b ≫ φ) : a = b := by
  obtain ⟨c, hc, huniq⟩ := hq.unique_lift φ (a ≫ φ) (q.map a) (by simp)
  exact huniq a ⟨rfl, rfl⟩ |>.trans (huniq b ⟨hmap.symm, hcomp.symm⟩).symm

/-- A morphism whose `p.op`-lift is `f.op` up to `eqToHom`s itself lies over `f` for `p`. -/
private lemma isHomLift_of_op_eqToHom
    {C D : Type*} [Category C] [Category D] (p : C ⥤ D) {R S : D} (f : R ⟶ S)
    {x y : C} (φ : x ⟶ y) (hx : p.obj x = R) (hy : p.obj y = S)
    (d : Opposite.op (p.obj y) ⟶ Opposite.op (p.obj x))
    (hd : d = eqToHom (congrArg Opposite.op hy) ≫ f.op ≫ eqToHom (congrArg Opposite.op hx).symm)
    [p.op.IsHomLift d φ.op] : p.IsHomLift f φ := by
  have : p.IsHomLift d.unop φ := isHomLift_unop p d φ.op
  refine IsHomLift.of_fac' p f φ hx hy ?_
  simpa [hd] using (IsHomLift.fac p d.unop φ).symm

/-- **Stacks Project, Tag 06H4.** The projection from the category of formal objects of a
category cofibered in groupoids to the category of complete local algebras is cofibered in
groupoids. -/
@[stacks 06H4, sga "7 VI 1.15" "Â is cofibered over Ĉ_{Λ"]
public theorem formalObjectProjection_isCofiberedInGroupoids
    {F : Type uF} [Category.{vF} F]
    (p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k)
    (hp : IsCofiberedInGroupoids p) :
    IsCofiberedInGroupoids (FormalObject.projection (p := p)) := by
  refine { exists_lift := ?_, unique_lift := ?_ }
  · intro V U f X hX
    subst U
    let a : X.unop.base ⟶ V.unop := f.unop
    choose level app happ using fun n ↦
      hp.exists_lift ((AdicTruncation.functor n).map a).op
        (Opposite.op (X.unop.level n)) (congrArg Opposite.op (X.unop.level_eq n))
    let hlevel (n : ℕ) : p.op.obj (level n) =
        Opposite.op ((AdicTruncation.functor n).obj V.unop) :=
      @IsHomLift.domain_eq _ _ _ _ p.op _ _ _ _
        (((AdicTruncation.functor n).map a).op) (app n) (happ n)
    have happUnop (n : ℕ) : p.IsHomLift
        ((AdicTruncation.functor n).map a) (app n).unop := by
      apply IsHomLift.of_fac p _ _ (X.unop.level_eq n)
        (congrArg Opposite.unop (hlevel n))
      simpa using congrArg Quiver.Hom.unop
        (IsHomLift.fac p.op ((AdicTruncation.functor n).map a).op (app n))
    let d (n : ℕ) : p.op.obj (level n) ⟶ p.op.obj (level (n + 1)) :=
      eqToHom (hlevel n) ≫ (AdicTruncation.transition V.unop n).op ≫
        eqToHom (hlevel (n + 1)).symm
    choose transition htransition _ using fun n ↦
      hp.unique_lift (app (n + 1)) (app n ≫ (X.unop.transition n).op)
        (d n) (by
          let := happ n
          let := happ (n + 1)
          have hXt := X.unop.transition_lift n
          have h0 := happUnop n
          have h1 := happUnop (n + 1)
          let := isHomLift_op p
            ((AdicTruncation.transitionNat n).app X.unop.base)
            (X.unop.transition n)
          let : p.op.IsHomLift
              (((AdicTruncation.functor n).map a).op ≫
                ((AdicTruncation.transitionNat n).app X.unop.base).op)
              (app n ≫ (X.unop.transition n).op) := by
            infer_instance
          apply map_comp_eq_of_lifts p.op
            ((AdicTruncation.functor (n + 1)).map a).op
            (((AdicTruncation.functor n).map a).op ≫
              ((AdicTruncation.transitionNat n).app X.unop.base).op)
          apply Quiver.Hom.unop_inj
          exact (AdicTruncation.transitionNat n).naturality a
        )
    let Y : FormalObject p :=
      { base := V.unop
        level := fun n ↦ (level n).unop
        level_eq := fun n ↦ congrArg Opposite.unop (hlevel n)
        transition := fun n ↦ (transition n).unop
        transition_lift := fun n ↦ by
          let : p.op.IsHomLift (d n) (transition n) := by
            rw [← (htransition n).1]
            infer_instance
          let : p.op.IsHomLift (d n) (transition n).unop.op := this
          exact isHomLift_of_op_eqToHom p _ (transition n).unop
            (congrArg Opposite.unop (hlevel (n + 1))) (congrArg Opposite.unop (hlevel n))
            (d n) rfl }
    let φ : X.unop ⟶ Y :=
      { base := a
        app := fun n ↦ (app n).unop
        app_lift := happUnop
        naturality := fun n ↦ by
          simpa [Y] using (congrArg Quiver.Hom.unop (htransition n).2).symm }
    exact ⟨Opposite.op Y, φ.op, by
      show FormalObject.projection.op.IsHomLift f φ.op
      apply IsHomLift.of_fac
      · rfl
      · rfl
      · simp⟩
  · intro X Y Z φ ψ f hf
    let b : Y.unop.base ⟶ Z.unop.base := f.unop
    have hbase : φ.unop.base ≫ b = ψ.unop.base := congrArg Quiver.Hom.unop hf
    let d (n : ℕ) : p.op.obj (Opposite.op (Z.unop.level n)) ⟶
        p.op.obj (Opposite.op (Y.unop.level n)) :=
      eqToHom (congrArg Opposite.op (Z.unop.level_eq n)) ≫
        ((AdicTruncation.functor n).map b).op ≫
        eqToHom (congrArg Opposite.op (Y.unop.level_eq n)).symm
    choose app happ huniq using fun n ↦
      hp.unique_lift (φ.unop.app n).op (ψ.unop.app n).op (d n) (by
        let := φ.unop.app_lift n
        let := ψ.unop.app_lift n
        let := isHomLift_op p
          ((AdicTruncation.functor n).map φ.unop.base) (φ.unop.app n)
        let := isHomLift_op p
          ((AdicTruncation.functor n).map ψ.unop.base) (ψ.unop.app n)
        apply map_comp_eq_of_lifts p.op
          ((AdicTruncation.functor n).map φ.unop.base).op
          ((AdicTruncation.functor n).map ψ.unop.base).op
        apply Quiver.Hom.unop_inj
        simpa [d, b, Functor.map_comp] using
          congrArg (fun e ↦ (AdicTruncation.functor n).map e) hbase)
    let χ : Y.unop ⟶ Z.unop :=
      { base := b
        app := fun n ↦ (app n).unop
        app_lift := fun n ↦ by
          let : p.op.IsHomLift (d n) (app n) := by
            rw [← (happ n).1]
            infer_instance
          let : p.op.IsHomLift (d n) (app n).unop.op := this
          exact isHomLift_of_op_eqToHom p _ (app n).unop (Y.unop.level_eq n)
            (Z.unop.level_eq n) (d n) rfl
        naturality := fun n ↦ by
          apply Quiver.Hom.op_inj
          apply hom_ext_of_fibered p.op hp (φ.unop.app (n + 1)).op
          · apply Quiver.Hom.unop_inj
            show p.map (Y.unop.transition n ≫ (app n).unop) =
              p.map ((app (n + 1)).unop ≫ Z.unop.transition n)
            rw [Functor.map_comp, Functor.map_comp]
            let := Y.unop.transition_lift n
            let := Z.unop.transition_lift n
            rw [IsHomLift.fac' p
                ((AdicTruncation.transitionNat n).app Y.unop.base)
                (Y.unop.transition n),
              IsHomLift.fac' p
                ((AdicTruncation.transitionNat n).app Z.unop.base)
                (Z.unop.transition n)]
            have hn := congrArg Quiver.Hom.unop (happ n).1
            have hn1 := congrArg Quiver.Hom.unop (happ (n + 1)).1
            simp only [Functor.op_obj, Functor.op_map, Quiver.Hom.unop_op, unop_comp, eqToHom_unop,
              Category.assoc, d] at hn hn1
            rw [hn, hn1]
            simp [Category.assoc]
          · apply Quiver.Hom.unop_inj
            show φ.unop.app (n + 1) ≫ (Y.unop.transition n ≫ (app n).unop) =
              φ.unop.app (n + 1) ≫ ((app (n + 1)).unop ≫ Z.unop.transition n)
            have hn : φ.unop.app n ≫ (app n).unop = ψ.unop.app n := by
              simpa using congrArg Quiver.Hom.unop (happ n).2
            have hn1 : φ.unop.app (n + 1) ≫ (app (n + 1)).unop =
                ψ.unop.app (n + 1) := by
              simpa using congrArg Quiver.Hom.unop (happ (n + 1)).2
            rw [← Category.assoc, ← φ.unop.naturality n, Category.assoc,
              hn]
            rw [← Category.assoc, hn1,
              ← ψ.unop.naturality n] }
    refine ⟨χ.op, ?_, ?_⟩
    · constructor
      · rfl
      · apply Quiver.Hom.unop_inj
        apply FormalObject.Hom.ext hbase
        intro n
        exact congrArg Quiver.Hom.unop (happ n).2
    · intro χ' hχ'
      apply Quiver.Hom.unop_inj
      apply FormalObject.Hom.ext
      · exact congrArg Quiver.Hom.unop hχ'.1
      · intro n
        apply Quiver.Hom.op_inj
        apply huniq n
        constructor
        · let := χ'.unop.app_lift n
          have := isHomLift_op p
            ((AdicTruncation.functor n).map χ'.unop.base) (χ'.unop.app n)
          have hb' : χ'.unop.base = b := by
            simpa [b] using congrArg Quiver.Hom.unop hχ'.1
          simpa [d, hb'] using IsHomLift.fac' p.op
            ((AdicTruncation.functor n).map χ'.unop.base).op
            (χ'.unop.app n).op
        · have hc := congrArg (fun e ↦ (e.unop.app n).op) hχ'.2
          change (φ.unop.app n ≫ χ'.unop.app n).op = (ψ.unop.app n).op at hc
          simpa using hc

end

/-! ### Completion of a morphism of cofibered categories -/

section
open CategoryTheory
universe u v w uF vF uG vG uH vH


variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
variable {F : Type uF} [Category.{vF} F] {G : Type uG} [Category.{vG} G]
variable {p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k}
variable {q : G ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k}

/-- The levelwise functor on formal objects associated to a functor whose composite with the
target projection is specified by an equality. -/
public def formalObjectMapOfCompEq (φ : F ⥤ G) (hφ : φ ⋙ q = p) :
    BasedFunctor
      (BasedCategory.ofFunctor (FormalObject.projection (p := p)))
      (BasedCategory.ofFunctor (FormalObject.projection (p := q))) := by
  subst p
  refine { toFunctor := ?_, w := ?_ }
  · exact
      { obj := fun X ↦
          { base := X.base
            level := fun n ↦ φ.obj (X.level n)
            level_eq := X.level_eq
            transition := fun n ↦ φ.map (X.transition n)
            transition_lift := fun n ↦ by
              apply IsHomLift.of_fac q _ _ (X.level_eq (n + 1)) (X.level_eq n)
              let := X.transition_lift n
              simpa only [Functor.comp_map] using
                IsHomLift.fac (φ ⋙ q) ((AdicTruncation.transitionNat n).app X.base)
                  (X.transition n) }
        map := fun {X Y} f ↦
          { base := f.base
            app := fun n ↦ φ.map (f.app n)
            app_lift := fun n ↦ by
              apply IsHomLift.of_fac q _ _ (X.level_eq n) (Y.level_eq n)
              let := f.app_lift n
              simpa only [Functor.comp_map] using
                IsHomLift.fac (φ ⋙ q) ((AdicTruncation.functor n).map f.base) (f.app n)
            naturality := fun n ↦ by rw [← Functor.map_comp, f.naturality, Functor.map_comp] }
        map_id := fun X ↦ by
          apply FormalObject.Hom.ext
          · rfl
          · intro n
            change φ.map (𝟙 (X.level n)) = 𝟙 (φ.obj (X.level n))
            exact φ.map_id (X.level n)
        map_comp := fun f g ↦ by
          apply FormalObject.Hom.ext
          · rfl
          · intro n
            change φ.map (f.app n ≫ g.app n) = φ.map (f.app n) ≫ φ.map (g.app n)
            exact φ.map_comp (f.app n) (g.app n) }
  · refine CategoryTheory.Functor.ext (fun X => ?_) (fun X Y f => ?_)
    · rfl
    · rfl

/-- **Stacks Project, Tag 06H9.** A functor over the category of Artinian local algebras
induces a functor on formal objects by application at every level. -/
@[stacks 06H9 "completion_morphism"]
public def completionMap
    (φ : BasedFunctor (BasedCategory.ofFunctor p) (BasedCategory.ofFunctor q)) :
    BasedFunctor
      (BasedCategory.ofFunctor (FormalObject.projection (p := p)))
      (BasedCategory.ofFunctor (FormalObject.projection (p := q))) :=
  formalObjectMapOfCompEq φ.toFunctor φ.w

private theorem obj_base (ψ : F ⥤ G) (h : ψ ⋙ q = p) (X : FormalObject p) :
    ((formalObjectMapOfCompEq ψ h).obj X).base = X.base := by cases h; rfl

private theorem obj_level (ψ : F ⥤ G) (h : ψ ⋙ q = p) (X : FormalObject p) (n : ℕ) :
    ((formalObjectMapOfCompEq ψ h).obj X).level n = ψ.obj (X.level n) := by cases h; rfl

private theorem obj_transition (ψ : F ⥤ G) (h : ψ ⋙ q = p) (X : FormalObject p)
    (n : ℕ) (hn : ((formalObjectMapOfCompEq ψ h).obj X).level (n + 1) = ψ.obj (X.level (n + 1)))
    (hm : ((formalObjectMapOfCompEq ψ h).obj X).level n = ψ.obj (X.level n)) :
    ((formalObjectMapOfCompEq ψ h).obj X).transition n =
      eqToHom hn ≫ ψ.map (X.transition n) ≫ eqToHom hm.symm := by
  cases h
  exact (Category.comp_id _).symm.trans (Category.id_comp _).symm

private theorem map_base (ψ : F ⥤ G) (h : ψ ⋙ q = p) {X Y : FormalObject p}
    (f : X ⟶ Y) (hx : ((formalObjectMapOfCompEq ψ h).obj X).base = X.base)
    (hy : ((formalObjectMapOfCompEq ψ h).obj Y).base = Y.base) :
    ((formalObjectMapOfCompEq ψ h).map f).base = eqToHom hx ≫ f.base ≫ eqToHom hy.symm := by
  cases h
  exact (Category.comp_id _).symm.trans (Category.id_comp _).symm

private theorem map_app (ψ : F ⥤ G) (h : ψ ⋙ q = p) {X Y : FormalObject p}
    (f : X ⟶ Y) (n : ℕ)
    (hx : ((formalObjectMapOfCompEq ψ h).obj X).level n = ψ.obj (X.level n))
    (hy : ((formalObjectMapOfCompEq ψ h).obj Y).level n = ψ.obj (Y.level n)) :
    ((formalObjectMapOfCompEq ψ h).map f).app n =
      eqToHom hx ≫ ψ.map (f.app n) ≫ eqToHom hy.symm := by
  cases h
  exact (Category.comp_id _).symm.trans (Category.id_comp _).symm

/-- The induced functor does not change the complete local algebra underlying a formal object. -/
@[simp, stacks 06H9 "completion_morphism"]
public theorem completionMap_obj_base
    (φ : BasedFunctor (BasedCategory.ofFunctor p) (BasedCategory.ofFunctor q))
    (X : FormalObject p) :
    ((completionMap φ).obj X).base = X.base := obj_base φ.toFunctor φ.w X

/-- On objects, the induced completion functor applies the original functor at every level. -/
@[simp, stacks 06H9 "completion_morphism"]
public theorem completionMap_obj_level
    (φ : BasedFunctor (BasedCategory.ofFunctor p) (BasedCategory.ofFunctor q))
    (X : FormalObject p) (n : ℕ) :
    ((completionMap φ).obj X).level n = φ.obj (X.level n) := obj_level φ.toFunctor φ.w X n

/-- On objects, the induced completion functor applies the original functor to every transition
map. -/
@[simp, stacks 06H9 "completion_morphism"]
public theorem completionMap_obj_transition
    (φ : BasedFunctor (BasedCategory.ofFunctor p) (BasedCategory.ofFunctor q))
    (X : FormalObject p) (n : ℕ) :
    ((completionMap φ).obj X).transition n =
      eqToHom (completionMap_obj_level φ X (n + 1)) ≫ φ.map (X.transition n) ≫
        eqToHom (completionMap_obj_level φ X n).symm :=
  obj_transition φ.toFunctor φ.w X n
    (completionMap_obj_level φ X (n + 1)) (completionMap_obj_level φ X n)

/-- The induced functor does not change the morphism of complete local algebras underlying a
morphism of formal objects. -/
@[simp, stacks 06H9 "completion_morphism"]
public theorem completionMap_map_base
    (φ : BasedFunctor (BasedCategory.ofFunctor p) (BasedCategory.ofFunctor q))
    {X Y : FormalObject p} (f : X ⟶ Y) :
    ((completionMap φ).map f).base =
      eqToHom (completionMap_obj_base φ X) ≫ f.base ≫
        eqToHom (completionMap_obj_base φ Y).symm :=
  map_base φ.toFunctor φ.w f (completionMap_obj_base φ X) (completionMap_obj_base φ Y)

/-- On morphisms, the induced completion functor applies the original functor to every level
map. -/
@[simp, stacks 06H9 "completion_morphism"]
public theorem completionMap_map_app
    (φ : BasedFunctor (BasedCategory.ofFunctor p) (BasedCategory.ofFunctor q))
    {X Y : FormalObject p} (f : X ⟶ Y) (n : ℕ) :
    ((completionMap φ).map f).app n =
      eqToHom (completionMap_obj_level φ X n) ≫ φ.map (f.app n) ≫
        eqToHom (completionMap_obj_level φ Y n).symm :=
  map_app φ.toFunctor φ.w f n (completionMap_obj_level φ X n)
    (completionMap_obj_level φ Y n)

private theorem mapOfCompEq_comp {H : Type uH} [Category.{vH} H]
    {r : H ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k}
    (φ : F ⥤ G) (hφ : φ ⋙ q = p) (ψ : G ⥤ H) (hψ : ψ ⋙ r = q)
    (h : (φ ⋙ ψ) ⋙ r = p) :
    formalObjectMapOfCompEq (φ ⋙ ψ) h =
      BasedFunctor.comp (formalObjectMapOfCompEq φ hφ) (formalObjectMapOfCompEq ψ hψ) := by
  cases hψ
  cases hφ
  rfl

/-- **Stacks Project, Tag 06H9.** Completion takes the identity morphism of a category cofibered
in groupoids to the identity morphism of its completion. Together with `completionMap_comp`,
`completionNatTrans_id` and `completionNatTrans_comp` this is the statement that completion is a
functor of two-categories; the equality is strict, not merely up to isomorphism. -/
@[stacks 06H9 "completion_two_functor"]
public theorem completionMap_id :
    completionMap (BasedFunctor.id (BasedCategory.ofFunctor p)) =
      BasedFunctor.id (BasedCategory.ofFunctor (FormalObject.projection (p := p))) :=
  rfl

/-- **Stacks Project, Tag 06H9.** Completion takes a composite of morphisms of categories
cofibered in groupoids to the composite of the completions. Together with `completionMap_id`,
`completionNatTrans_id` and `completionNatTrans_comp` this is the statement that completion is a
functor of two-categories; the equality is strict, not merely up to isomorphism. -/
@[stacks 06H9 "completion_two_functor"]
public theorem completionMap_comp {H : Type uH} [Category.{vH} H]
    {r : H ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k}
    (φ : BasedFunctor (BasedCategory.ofFunctor p) (BasedCategory.ofFunctor q))
    (ψ : BasedFunctor (BasedCategory.ofFunctor q) (BasedCategory.ofFunctor r)) :
    completionMap (φ.comp ψ) = (completionMap φ).comp (completionMap ψ) :=
  mapOfCompEq_comp φ.toFunctor φ.w ψ.toFunctor ψ.w (φ.comp ψ).w

end

/-! ### Completion of a two-morphism -/

section
open CategoryTheory
universe u v w uF vF uG vG
set_option backward.isDefEq.respectTransparency false


variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
variable {F : Type uF} [Category.{vF} F] {G : Type uG} [Category.{vG} G]
variable {p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k}
variable {q : G ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k}

/-- **Stacks Project, Tag 06H9.** The natural transformation induced levelwise on formal
objects by a two-morphism over the Artinian base. -/
@[stacks 06H9 "completion_two_morphism"]
public def completionNatTrans
    {φ ψ : BasedFunctor (BasedCategory.ofFunctor p) (BasedCategory.ofFunctor q)}
    (t : BasedNatTrans φ ψ) :
    BasedNatTrans (completionMap φ) (completionMap ψ) := by
  let component : (X : (BasedCategory.ofFunctor (FormalObject.projection (p := p))).obj) →
      (completionMap φ).obj X ⟶ (completionMap ψ).obj X := fun X => by
    change FormalObject p at X
    refine ⟨
      eqToHom (completionMap_obj_base φ X) ≫ 𝟙 X.base ≫
        eqToHom (completionMap_obj_base ψ X).symm,
      (fun n => eqToHom (completionMap_obj_level φ X n) ≫
        t.toNatTrans.app (X.level n) ≫
          eqToHom (completionMap_obj_level ψ X n).symm), ?_, ?_⟩
    · intro n
      have hφbase : q.obj (φ.obj (X.level n)) = p.obj (X.level n) := by
        change (φ.toFunctor ⋙ q).obj (X.level n) = p.obj (X.level n)
        exact Functor.congr_obj φ.w (X.level n)
      have hψbase : q.obj (ψ.obj (X.level n)) = p.obj (X.level n) := by
        change (ψ.toFunctor ⋙ q).obj (X.level n) = p.obj (X.level n)
        exact Functor.congr_obj ψ.w (X.level n)
      have hA : q.obj (((completionMap φ).obj X).level n) =
          (AdicTruncation.functor n).obj ((completionMap φ).obj X).base := by
        calc
          q.obj (((completionMap φ).obj X).level n) = q.obj (φ.obj (X.level n)) :=
            congrArg q.obj (completionMap_obj_level φ X n)
          _ = p.obj (X.level n) := hφbase
          _ = (AdicTruncation.functor n).obj X.base := X.level_eq n
          _ = (AdicTruncation.functor n).obj ((completionMap φ).obj X).base :=
            congrArg (AdicTruncation.functor n).obj (completionMap_obj_base φ X).symm
      have hB : q.obj (((completionMap ψ).obj X).level n) =
          (AdicTruncation.functor n).obj ((completionMap ψ).obj X).base := by
        calc
          q.obj (((completionMap ψ).obj X).level n) = q.obj (ψ.obj (X.level n)) :=
            congrArg q.obj (completionMap_obj_level ψ X n)
          _ = p.obj (X.level n) := hψbase
          _ = (AdicTruncation.functor n).obj X.base := X.level_eq n
          _ = (AdicTruncation.functor n).obj ((completionMap ψ).obj X).base :=
            congrArg (AdicTruncation.functor n).obj (completionMap_obj_base ψ X).symm
      have hDom : (AdicTruncation.functor n).obj ((completionMap φ).obj X).base =
          p.obj (X.level n) :=
        (congrArg (AdicTruncation.functor n).obj (completionMap_obj_base φ X)).trans
          (X.level_eq n).symm
      have hCod : (AdicTruncation.functor n).obj ((completionMap ψ).obj X).base =
          p.obj (X.level n) :=
        (congrArg (AdicTruncation.functor n).obj (completionMap_obj_base ψ X)).trans
          (X.level_eq n).symm
      let : q.IsHomLift (𝟙 (p.obj (X.level n)))
          (t.toNatTrans.app (X.level n)) := t.isHomLift' (X.level n)
      have hfac := IsHomLift.fac q (𝟙 (p.obj (X.level n)))
        (t.toNatTrans.app (X.level n))
      exact IsHomLift.of_fac q
        ((AdicTruncation.functor n).map
          (eqToHom (completionMap_obj_base φ X) ≫ 𝟙 X.base ≫
            eqToHom (completionMap_obj_base ψ X).symm))
        (eqToHom (completionMap_obj_level φ X n) ≫ t.toNatTrans.app (X.level n) ≫
          eqToHom (completionMap_obj_level ψ X n).symm)
        hA hB (by
          simp only [Functor.map_comp, eqToHom_map]
          convert hfac using 1
          · simp [X.level_eq, completionMap_obj_base]
          · have hEq := hDom.trans hCod.symm
            simpa [hEq, eqToHom_trans] using
              (eqToHom_heq_id_cod _ _ hEq).trans
                ((eqToHom_heq_id_dom _ _ hCod).symm.trans
                  (eqToHom_heq_id_cod _ _ hCod))
          · simp [eqToHom_trans])
    · intro n
      rw [completionMap_obj_transition (φ := φ) (X := X) (n := n),
        completionMap_obj_transition (φ := ψ) (X := X) (n := n)]
      simpa only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl,
        Category.id_comp, Category.comp_id] using congrArg
          (fun g => eqToHom (completionMap_obj_level φ X (n + 1)) ≫ g ≫
            eqToHom (completionMap_obj_level ψ X n).symm) (t.toNatTrans.naturality (X.transition n))
  -- `component` is defined by a tactic block, so `simp` cannot see through the
  -- application to reach its fields.  `rfl` can, at default transparency, so the
  -- two projections are recorded once here and used as rewrite rules below.
  have hcomp_base : ∀ X : FormalObject p, (component X).base =
      eqToHom (completionMap_obj_base φ X) ≫ 𝟙 X.base ≫
        eqToHom (completionMap_obj_base ψ X).symm := fun _ => rfl
  have hcomp_app : ∀ (X : FormalObject p) (n : ℕ), (component X).app n =
      eqToHom (completionMap_obj_level φ X n) ≫
        t.toNatTrans.app (X.level n) ≫
          eqToHom (completionMap_obj_level ψ X n).symm := fun _ _ => rfl
  refine ⟨?_, ?_⟩
  · refine { app := component, naturality := ?_ }
    intro X Y f
    change FormalObject p at X
    change FormalObject p at Y
    apply FormalObject.Hom.ext
    · change ((completionMap φ).map f).base ≫ (component Y).base =
        (component X).base ≫ ((completionMap ψ).map f).base
      rw [completionMap_map_base φ f, completionMap_map_base ψ f]
      simp [hcomp_base, Category.assoc, eqToHom_trans_assoc]
    · intro n
      change ((completionMap φ).map f).app n ≫ (component Y).app n =
        (component X).app n ≫ ((completionMap ψ).map f).app n
      rw [completionMap_map_app φ f n, completionMap_map_app ψ f n]
      change (eqToHom (completionMap_obj_level φ X n) ≫ φ.map (f.app n) ≫
          eqToHom (completionMap_obj_level φ Y n).symm) ≫
          (eqToHom (completionMap_obj_level φ Y n) ≫
            t.toNatTrans.app (Y.level n) ≫
              eqToHom (completionMap_obj_level ψ Y n).symm) =
        (eqToHom (completionMap_obj_level φ X n) ≫
            t.toNatTrans.app (X.level n) ≫
              eqToHom (completionMap_obj_level ψ X n).symm) ≫
          (eqToHom (completionMap_obj_level ψ X n) ≫ ψ.map (f.app n) ≫
            eqToHom (completionMap_obj_level ψ Y n).symm)
      simpa only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl,
        Category.id_comp, Category.comp_id] using congrArg
          (fun g => eqToHom (completionMap_obj_level φ X n) ≫ g ≫
            eqToHom (completionMap_obj_level ψ Y n).symm) (t.toNatTrans.naturality (f.app n))
  · intro X
    change FormalObject p at X
    exact IsHomLift.of_fac (p := FormalObject.projection (p := q))
      (f := 𝟙 X.base) (φ := component X)
      (ha := completionMap_obj_base φ X) (hb := completionMap_obj_base ψ X)
      (by
        change 𝟙 X.base =
          eqToHom (completionMap_obj_base φ X).symm ≫
            (component X).base ≫ eqToHom (completionMap_obj_base ψ X)
        simp [hcomp_base, eqToHom_trans, eqToHom_refl])

/-- The induced component is the identity on the complete local algebra. -/
@[stacks 06H9 "completion_two_morphism"]
public theorem completionNatTrans_app_base
    {φ ψ : BasedFunctor (BasedCategory.ofFunctor p) (BasedCategory.ofFunctor q)}
    (t : BasedNatTrans φ ψ) (X : FormalObject p) :
    ((completionNatTrans t).toNatTrans.app X).base =
      eqToHom (completionMap_obj_base φ X) ≫
        eqToHom (completionMap_obj_base ψ X).symm := by
  rfl

/-- At every Artinian quotient, the induced component is the original two-morphism. -/
@[stacks 06H9 "completion_two_morphism"]
public theorem completionNatTrans_app_level
    {φ ψ : BasedFunctor (BasedCategory.ofFunctor p) (BasedCategory.ofFunctor q)}
    (t : BasedNatTrans φ ψ) (X : FormalObject p) (n : ℕ) :
    ((completionNatTrans t).toNatTrans.app X).app n =
      eqToHom (completionMap_obj_level φ X n) ≫
        t.toNatTrans.app (X.level n) ≫
          eqToHom (completionMap_obj_level ψ X n).symm := by
  rfl

/-- **Stacks Project, Tag 06H9.** Levelwise completion takes an identity two-morphism to an
identity. This is half of the statement that completion is a functor of two-categories on
two-morphisms. -/
@[stacks 06H9 "completion_two_functor"]
public theorem completionNatTrans_id
    (φ : BasedFunctor (BasedCategory.ofFunctor p) (BasedCategory.ofFunctor q)) :
    completionNatTrans (𝟙 φ) = 𝟙 (completionMap φ) := by
  refine BasedNatTrans.ext _ _ (NatTrans.ext (funext fun (X : FormalObject p) => ?_))
  refine FormalObject.Hom.ext ?_ (fun n => ?_)
  · rw [completionNatTrans_app_base]
    simp only [eqToHom_trans, eqToHom_refl]
    rfl
  · rw [completionNatTrans_app_level]
    show eqToHom _ ≫ 𝟙 _ ≫ eqToHom _ = _
    simp only [Category.id_comp, eqToHom_trans, eqToHom_refl]
    rfl

/-- **Stacks Project, Tag 06H9.** Levelwise completion is compatible with composition of
two-morphisms. This is the other half of the statement that completion is a functor of
two-categories on two-morphisms. -/
@[stacks 06H9 "completion_two_functor"]
public theorem completionNatTrans_comp
    {φ ψ χ : BasedFunctor (BasedCategory.ofFunctor p) (BasedCategory.ofFunctor q)}
    (t : φ ⟶ ψ) (s : ψ ⟶ χ) :
    completionNatTrans (t ≫ s) =
      BasedNatTrans.comp (completionNatTrans t) (completionNatTrans s) := by
  refine BasedNatTrans.ext _ _ (NatTrans.ext (funext fun (X : FormalObject p) => ?_))
  refine FormalObject.Hom.ext ?_ (fun n => ?_)
  · rw [completionNatTrans_app_base]
    show _ = ((completionNatTrans t).toNatTrans.app X ≫
      (completionNatTrans s).toNatTrans.app X).base
    show _ = ((completionNatTrans t).toNatTrans.app X).base ≫
      ((completionNatTrans s).toNatTrans.app X).base
    rw [completionNatTrans_app_base, completionNatTrans_app_base]
    simp
  · rw [completionNatTrans_app_level]
    show eqToHom _ ≫ (t.toNatTrans.app _ ≫ s.toNatTrans.app _) ≫ eqToHom _ =
      ((completionNatTrans t).toNatTrans.app X ≫
        (completionNatTrans s).toNatTrans.app X).app n
    show _ = ((completionNatTrans t).toNatTrans.app X).app n ≫
      ((completionNatTrans s).toNatTrans.app X).app n
    rw [completionNatTrans_app_level, completionNatTrans_app_level]
    simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]

end

end Deformation
