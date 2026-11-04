module

public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import StacksFrontier.AlgebraicGeometry.Variety.Frobenius.Absolute
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The Frobenius twist and the relative Frobenius

Let `S` be a scheme of prime characteristic `p`. The *Frobenius twist* sends an `S`-scheme
`X ⟶ S` to the fibre product `X ×_S S`, where the second map to `S` is the absolute Frobenius
of `S`; its structure morphism is the second projection. The *relative Frobenius* of `X` is the
unique `S`-morphism from `X` to its Frobenius twist whose first projection is the absolute
Frobenius of `X`.

Both constructions are natural: the Frobenius twist is a functor, and the relative Frobenius
morphisms form a natural transformation from the identity functor to it.

## Main definitions

* `AlgebraicGeometry.frobeniusTwist`: Frobenius base change as an endofunctor on `S`-schemes.
* `AlgebraicGeometry.relativeFrobenius`: the relative Frobenius morphism of an `S`-scheme.

## Main results

* `AlgebraicGeometry.relativeFrobenius_existsUnique`: the two projection equations determine a
  unique morphism to the Frobenius twist.
* `AlgebraicGeometry.relativeFrobenius_fst` and `AlgebraicGeometry.relativeFrobenius_snd`: the
  two projection equations for the relative Frobenius.
* `AlgebraicGeometry.eq_relativeFrobenius`: those equations characterize it.
* `AlgebraicGeometry.relativeFrobenius_naturality`: the relative Frobenius is natural in the
  `S`-scheme.

## Implementation notes

An `S`-scheme is represented by an object of `Over S`, so the twist is the pullback functor
along the absolute Frobenius: its value has underlying scheme `X ×_S S` and structure morphism
the second projection, and the functorial formulation makes the canonical construction on
morphisms together with its identity and composition laws available directly. The relative
Frobenius is chosen from its existence and uniqueness characterization, as a morphism in
`Over S`, so subsequent statements can use both its underlying scheme map and its compatibility
with the structure morphisms.

## References

* [Stacks Project, Tag 0CC9](https://stacks.math.columbia.edu/tag/0CC9)
* [Stacks Project, Tag 0CCA](https://stacks.math.columbia.edu/tag/0CCA)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits
open Stacks.Frobenius

namespace AlgebraicGeometry

/-- **Stacks Project, Tag 0CC9.** Frobenius twisting is base change along the absolute
Frobenius of the base scheme. Its value at `X : Over S` is `X ×_S S`, regarded as an
`S`-scheme through the second projection. -/
@[stacks 0CC9 "frobenius_twist",
  implicit_reducible,
  sga "3 VIIA 4.1" "special case",
  sga "3 VIIA 4.3.2",
  sga "3 VIIB 4.1.1",
  sga "3 XVII 4.3.2" "partial"]
public noncomputable def frobeniusTwist (S : Scheme.{u}) (p : ℕ) [Fact p.Prime]
    (hS : IsInCharacteristic S p) : Over S ⥤ Over S :=
  Over.pullback (absoluteFrobenius S p hS)

/-- The underlying scheme of the Frobenius twist is the stated fibre product. -/
@[simp]
public lemma frobeniusTwist_obj_left (S : Scheme.{u}) (p : ℕ) [Fact p.Prime]
    (hS : IsInCharacteristic S p) (X : Over S) :
    ((frobeniusTwist S p hS).obj X).left =
      (pullback X.hom (absoluteFrobenius S p hS) : Scheme.{u}) := rfl

/-- The structure morphism of the Frobenius twist is the second projection. -/
@[simp]
public lemma frobeniusTwist_obj_hom (S : Scheme.{u}) (p : ℕ) [Fact p.Prime]
    (hS : IsInCharacteristic S p) (X : Over S) :
    ((frobeniusTwist S p hS).obj X).hom = pullback.snd X.hom (absoluteFrobenius S p hS) := rfl

/-- A scheme over a scheme of characteristic `p` is itself of characteristic `p`. -/
public lemma isInCharacteristic_of_hom {X S : Scheme.{u}} (f : X ⟶ S) (p : ℕ)
    (hS : IsInCharacteristic S p) : IsInCharacteristic X p := by
  simpa only [map_natCast, map_zero] using congrArg f.appTop.hom hS

/-- **Stacks Project, Tag 0CC9.** The relative Frobenius is the unique morphism over `S`
whose first projection is the absolute Frobenius of `X` and whose second projection is the
structure morphism of `X`. -/
@[stacks 0CC9 "relative_frobenius_characterization"]
public theorem relativeFrobenius_existsUnique (S : Scheme.{u}) (p : ℕ) [Fact p.Prime]
    (hS : IsInCharacteristic S p) (X : Over S) :
    ∃! g : X ⟶ (frobeniusTwist S p hS).obj X,
      (g.left ≫ pullback.fst X.hom (absoluteFrobenius S p hS) =
          absoluteFrobenius X.left p (isInCharacteristic_of_hom X.hom p hS)) ∧
      (g.left ≫ pullback.snd X.hom (absoluteFrobenius S p hS) = X.hom) := by
  have h := absoluteFrobenius_naturality X.hom p (isInCharacteristic_of_hom X.hom p hS) hS
  exact ⟨Over.homMk (pullback.lift _ X.hom h) (by
      simpa only [frobeniusTwist_obj_hom] using pullback.lift_snd _ _ h),
    ⟨pullback.lift_fst _ _ h, pullback.lift_snd _ _ h⟩, fun g' hg' => Over.OverMorphism.ext
      (pullback.hom_ext (hg'.1.trans (pullback.lift_fst _ _ h).symm)
        (hg'.2.trans (pullback.lift_snd _ _ h).symm))⟩

/-- **Stacks Project, Tag 0CC9.** The relative Frobenius morphism of an `S`-scheme. -/
@[stacks 0CC9 "relative_frobenius",
  sga "5 XV 1.Definition3",
  sga "3 VIIA 4.1" "Fr(X/S) for S-schemes",
  sga "3 VIIA 4.1.3" "Case n=1",
  sga "5 XII 7.3"]
public noncomputable def relativeFrobenius (S : Scheme.{u}) (p : ℕ) [Fact p.Prime]
    (hS : IsInCharacteristic S p) (X : Over S) : X ⟶ (frobeniusTwist S p hS).obj X :=
  Classical.choose (relativeFrobenius_existsUnique S p hS X)

/-- The first projection of the relative Frobenius is the absolute Frobenius of `X`. -/
public theorem relativeFrobenius_fst (S : Scheme.{u}) (p : ℕ) [Fact p.Prime]
    (hS : IsInCharacteristic S p) (X : Over S) :
    (relativeFrobenius S p hS X).left ≫ pullback.fst X.hom (absoluteFrobenius S p hS) =
      absoluteFrobenius X.left p (isInCharacteristic_of_hom X.hom p hS) :=
  (Classical.choose_spec (relativeFrobenius_existsUnique S p hS X)).1.1

/-- The second projection of the relative Frobenius is the structure morphism of `X`. -/
public theorem relativeFrobenius_snd (S : Scheme.{u}) (p : ℕ) [Fact p.Prime]
    (hS : IsInCharacteristic S p) (X : Over S) :
    (relativeFrobenius S p hS X).left ≫ pullback.snd X.hom (absoluteFrobenius S p hS) =
      X.hom :=
  (Classical.choose_spec (relativeFrobenius_existsUnique S p hS X)).1.2

/-- The projection equations characterize the relative Frobenius. -/
public theorem eq_relativeFrobenius (S : Scheme.{u}) (p : ℕ) [Fact p.Prime]
    (hS : IsInCharacteristic S p) (X : Over S) (g : X ⟶ (frobeniusTwist S p hS).obj X)
    (hfst : g.left ≫ pullback.fst X.hom (absoluteFrobenius S p hS) =
      absoluteFrobenius X.left p (isInCharacteristic_of_hom X.hom p hS))
    (hsnd : g.left ≫ pullback.snd X.hom (absoluteFrobenius S p hS) = X.hom) :
    g = relativeFrobenius S p hS X :=
  (Classical.choose_spec (relativeFrobenius_existsUnique S p hS X)).2 g ⟨hfst, hsnd⟩

/-- **Stacks Project, Tag 0CCA.** The relative Frobenius is natural in an `S`-scheme. -/
@[stacks 0CCA,
  sga "3 VIIA 4.1" "special case",
  sga "3 VIIA 4.1.3" "special case",
  sga "4½ Rapport 1.3" "special case",
  sga "5 XV 1.Proposition1" "partial"]
public lemma relativeFrobenius_naturality (S : Scheme.{u}) (p : ℕ) [Fact p.Prime]
    (hS : IsInCharacteristic S p) {X Y : Over S} (f : X ⟶ Y) :
    relativeFrobenius S p hS X ≫ (frobeniusTwist S p hS).map f =
      f ≫ relativeFrobenius S p hS Y := by
  apply Over.OverMorphism.ext
  apply pullback.hom_ext <;> simp only [Over.comp_left, frobeniusTwist, Over.pullback_map_left,
    Category.assoc, pullback.lift_fst, pullback.lift_snd, relativeFrobenius_fst,
    relativeFrobenius_snd, Over.w]
  rw [← Category.assoc, relativeFrobenius_fst, absoluteFrobenius_naturality]

end AlgebraicGeometry

end
