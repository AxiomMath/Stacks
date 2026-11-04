module

public import Mathlib.Algebra.CharP.Frobenius
public import Mathlib.Algebra.Field.ULift
public import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.Endomorphism
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.FieldTheory.Finite.GaloisField
public import Mathlib.FieldTheory.Perfect
public import StacksCore.Tactic.StacksAttribute

/-!
# The absolute and geometric Frobenius of a scheme

A scheme `X` is *in characteristic `p`* when the integer `p` vanishes in its ring of global
sections. For a prime `p` the *absolute Frobenius* of such a scheme is the endomorphism which
is the identity on the underlying topological space and raises local sections to their `p`-th
powers. If `k` is a finite field with `p ^ f` elements, the `f`-fold absolute Frobenius of a
scheme over `k` is a morphism over `Spec k`, and as such it is the *geometric Frobenius*. The
exponent `f` is read off from the base field, so a scheme which is defined over two finite
fields of different cardinalities carries two distinct geometric Frobenius endomorphisms. On
an extension field of `k` the `f`-fold Frobenius of the field is the *arithmetic Frobenius*
`x ↦ x ^ p ^ f`, an element of the Galois group of the extension.

## Main definitions

* `Stacks.Frobenius.IsInCharacteristic` says that `p` vanishes in the ring of global sections
  of a scheme.
* `Stacks.Frobenius.absoluteFrobenius` is the absolute Frobenius endomorphism of a scheme in
  characteristic `p`.
* `Stacks.Frobenius.geometricFrobenius` is the geometric Frobenius endomorphism of a scheme
  over a finite field.
* `Stacks.Frobenius.arithmeticFrobenius` is the arithmetic Frobenius of a finite field, acting
  on a perfect extension field.

## Main results

* `Stacks.Frobenius.absoluteFrobenius_base` identifies the underlying continuous map of the
  absolute Frobenius with the identity.
* `Stacks.Frobenius.absoluteFrobenius_app_apply` identifies its map on sections with
  `g ↦ g ^ p`.
* `Stacks.Frobenius.eq_absoluteFrobenius` characterizes the absolute Frobenius by these two
  properties.
* `Stacks.Frobenius.absoluteFrobenius_pow_appTop_apply` computes the map on global sections of
  an iterate of the absolute Frobenius as `g ↦ g ^ p ^ n`.
* `Stacks.Frobenius.absoluteFrobenius_pow_comp_hom` is the commutation which makes the
  geometric Frobenius a morphism over the base field.
* `Stacks.Frobenius.geometricFrobenius_left` identifies the underlying scheme morphism of the
  geometric Frobenius with the `f`-fold absolute Frobenius.
* `Stacks.Frobenius.arithmeticFrobenius_apply` computes the arithmetic Frobenius as raising to
  the power the cardinality of the base field.
* `Stacks.Frobenius.exists_pow_ne_self` produces an element of a finite field with `p ^ f`
  elements, `1 < f`, which is not fixed by the `p`-th power map.
* `Stacks.Frobenius.absoluteFrobenius_pow_one_ne_absoluteFrobenius_pow` distinguishes the
  absolute Frobenius of the spectrum of a finite field with `p ^ f` elements, `1 < f`, from its
  `f`-fold iterate.
* `Stacks.Frobenius.geometricFrobenius_left_eq_absoluteFrobenius_pow_and_exists_ne` states that
  the `f`-fold absolute Frobenius is the geometric Frobenius of a scheme over a field with
  `p ^ f` elements, and that a scheme over two finite fields can have two distinct geometric
  Frobenius endomorphisms.

## Implementation notes

Vanishing of `p` on global sections implies its vanishing on every open by restriction, so the
`p`-th power maps on the rings of sections assemble into an endomorphism of the structure
presheaf. On a stalk the resulting map is again the `p`-th power map, hence is local, which is
what makes the construction a morphism of schemes. The possibility that a ring of sections is
the zero ring — where `p` need not be the characteristic — is handled by
`Stacks.Frobenius.primePowerEndomorphism`, which falls back on the identity there.

`Stacks.Frobenius.absoluteFrobenius_preimage` and `Stacks.Frobenius.absoluteFrobenius_app_apply`
are not `simp` lemmas: their left-hand sides are already rewritten by
`Stacks.Frobenius.absoluteFrobenius_base`, which identifies the underlying continuous map with
the identity.

A scheme over `k` is represented by an object of `CategoryTheory.Over (Spec (.of k))`.
Accordingly, the geometric Frobenius is bundled as an endomorphism in this over category, so
the assertion that it is a morphism over `Spec k` is part of its type. Its underlying scheme
morphism is definitionally the `f`-th power of the absolute Frobenius in the endomorphism
monoid, and the characteristic of the scheme is obtained from its structure morphism. That the
`f`-fold absolute Frobenius is a morphism over `Spec k` is exactly the identity `a ^ p ^ f = a`
on a field with `p ^ f` elements.

The scheme over two finite fields which separates their geometric Frobenius endomorphisms is the
spectrum of a field with `p ^ 2` elements, taken over the prime field and over itself; such a
field is available in an arbitrary universe as `ULift (GaloisField p 2)`.

## References

* [Stacks Project, Tag 03SM](https://stacks.math.columbia.edu/tag/03SM)
* [Stacks Project, Tag 03SQ](https://stacks.math.columbia.edu/tag/03SQ)
* [Stacks Project, Tag 03SS](https://stacks.math.columbia.edu/tag/03SS)
* [Stacks Project, Tag 03SU](https://stacks.math.columbia.edu/tag/03SU)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u v

namespace Stacks.Frobenius

/-- A scheme is **in characteristic `p`** when `p` vanishes in its ring of global sections. -/
abbrev IsInCharacteristic (X : Scheme.{u}) (p : ℕ) : Prop :=
  (p : Γ(X, ⊤)) = 0

/-- On a scheme in characteristic `p` the integer `p` vanishes in the sections over every
open, by restricting the vanishing on global sections. -/
lemma cast_eq_zero_of_isInCharacteristic {X : Scheme.{u}} {p : ℕ}
    (hX : IsInCharacteristic X p) (U : X.Opens) : (p : Γ(X, U)) = 0 := by
  simpa only [map_natCast, map_zero] using
    congrArg (X.presheaf.map (homOfLE (show U ≤ (⊤ : X.Opens) from le_top)).op) hX

/-- In a commutative ring in which a prime `p` vanishes, taking `p`-th powers is a ring
endomorphism. The zero ring, where `p` need not be the characteristic, is covered as well: the
`p`-th power map is the identity there. -/
@[ega "0 21.1.4"]
noncomputable def primePowerEndomorphism (R : Type u) [CommRing R] (p : ℕ) [Fact p.Prime]
    (hp : (p : R) = 0) : R →+* R := by
  classical
  by_cases hR : Nontrivial R
  · letI := hR
    letI : CharP R p := by
      rw [← ringChar.eq_iff]
      exact ((Nat.dvd_prime Fact.out).mp (ringChar.dvd hp)).resolve_left
        CharP.ringChar_ne_one
    exact frobenius R p
  · letI : Subsingleton R := not_nontrivial_iff_subsingleton.mp hR
    exact RingHom.id R

/-- The prime power endomorphism is given pointwise by taking `p`-th powers. -/
@[simp]
lemma primePowerEndomorphism_apply (R : Type u) [CommRing R] (p : ℕ) [Fact p.Prime]
    (hp : (p : R) = 0) (x : R) : primePowerEndomorphism R p hp x = x ^ p := by
  classical
  rw [primePowerEndomorphism]
  split
  · rfl
  · rename_i hR
    let _ : Subsingleton R := not_nontrivial_iff_subsingleton.mp hR
    exact Subsingleton.elim _ _

/-- **Stacks Project, Tag 03SM.** The absolute Frobenius of a scheme in characteristic `p`: it
is the identity on points and the `p`-th power map on the structure sheaf. -/
@[stacks 03SM,
  implicit_reducible,
  sga "3 VIIA 4.1" "absolute Frobenius fr(X)",
  sga "5 XV 1.Definition2",
  sga "4½ Fonctions_L 3.4" "F_abs definition",
  sga "4½ Rapport 1.1" "q = p",
  sga "3 VIIB 4.1.1",
  sga "7 IX 4.3.2" "special case",
  sga "7 XXI 1.0",
  sga "7 XXII 6.2" "(6.2.1) F_q for q = p"]
noncomputable def absoluteFrobenius (X : Scheme.{u}) (p : ℕ) [Fact p.Prime]
    (hX : IsInCharacteristic X p) : X ⟶ X := by
  let α : X.presheaf ⟶ X.presheaf :=
    { app := fun U ↦ CommRingCat.ofHom <|
        primePowerEndomorphism _ p (cast_eq_zero_of_isInCharacteristic hX U.unop)
      naturality := by
        intro U V f
        ext g
        change primePowerEndomorphism _ p
            (cast_eq_zero_of_isInCharacteristic hX V.unop) ((X.presheaf.map f) g) =
          X.presheaf.map f (primePowerEndomorphism _ p
            (cast_eq_zero_of_isInCharacteristic hX U.unop) g)
        rw [primePowerEndomorphism_apply, primePowerEndomorphism_apply, map_pow] }
  let f : X.toPresheafedSpace ⟶ X.toPresheafedSpace := { base := 𝟙 _, c := α }
  refine Scheme.Hom.mk <| LocallyRingedSpace.homMk (InducedCategory.homMk f) ?_
  rw [InducedCategory.homMk_hom]
  dsimp only [f]
  intro x
  refine ⟨fun a ha ↦ ?_⟩
  obtain ⟨U, hxU, g, rfl⟩ := X.presheaf.exists_germ_eq a
  change IsUnit (X.presheaf.germ U x hxU g)
  apply (isUnit_pow_iff (Fact.out : p.Prime).ne_zero).mp
  rw [PresheafedSpace.stalkMap_germ_apply] at ha
  change IsUnit (X.presheaf.germ U x hxU
    (primePowerEndomorphism _ p (cast_eq_zero_of_isInCharacteristic hX U) g)) at ha
  simpa only [primePowerEndomorphism_apply, map_pow] using ha

/-- The absolute Frobenius is the identity on the underlying topological space. -/
@[simp]
lemma absoluteFrobenius_base (X : Scheme.{u}) (p : ℕ) [Fact p.Prime]
    (hX : IsInCharacteristic X p) :
    (absoluteFrobenius X p hX).base = 𝟙 (X : TopCat) := rfl

/-- The absolute Frobenius fixes every point. -/
@[simp]
lemma absoluteFrobenius_apply (X : Scheme.{u}) (p : ℕ) [Fact p.Prime]
    (hX : IsInCharacteristic X p) (x : X) : absoluteFrobenius X p hX x = x := rfl

/-- Every open set is its own inverse image under the absolute Frobenius. -/
lemma absoluteFrobenius_preimage (X : Scheme.{u}) (p : ℕ) [Fact p.Prime]
    (hX : IsInCharacteristic X p) (U : X.Opens) :
    (absoluteFrobenius X p hX) ⁻¹ᵁ U = U := rfl

/-- On every open set, the map induced by the absolute Frobenius raises sections to their
`p`-th powers. -/
lemma absoluteFrobenius_app_apply (X : Scheme.{u}) (p : ℕ) [Fact p.Prime]
    (hX : IsInCharacteristic X p) (U : X.Opens) (g : Γ(X, U)) :
    (absoluteFrobenius X p hX).app U g = g ^ p :=
  primePowerEndomorphism_apply _ p (cast_eq_zero_of_isInCharacteristic hX U) g

/-- Identifying an open with its inverse image, the map on sections induced by the absolute
Frobenius is the `p`-th power map. -/
@[simp]
lemma absoluteFrobenius_appLE_apply (X : Scheme.{u}) (p : ℕ) [Fact p.Prime]
    (hX : IsInCharacteristic X p) (U : X.Opens)
    (e : U ≤ (absoluteFrobenius X p hX) ⁻¹ᵁ U) (g : Γ(X, U)) :
    (absoluteFrobenius X p hX).appLE U U e g = g ^ p := by
  show X.presheaf.map (𝟙 (op U)) ((absoluteFrobenius X p hX).app U g) = g ^ p
  rw [X.presheaf.map_id, absoluteFrobenius_app_apply]
  simp

/-- An endomorphism which fixes points and raises sections to their `p`-th powers is the
absolute Frobenius. -/
lemma eq_absoluteFrobenius (X : Scheme.{u}) (p : ℕ) [Fact p.Prime]
    (hX : IsInCharacteristic X p) (f : X ⟶ X) (hf : f.base = 𝟙 (X : TopCat))
    (hf' : ∀ (U : X.Opens) (g : Γ(X, U)), f.appLE U U (by simp [hf]) g = g ^ p) :
    f = absoluteFrobenius X p hX := by
  apply Scheme.Hom.ext (hf.trans (absoluteFrobenius_base X p hX).symm)
  intro U
  ext g
  show f.appLE U U (by simp [hf]) g = (absoluteFrobenius X p hX).app U g
  rw [hf', absoluteFrobenius_app_apply]

/-- On global sections, the map induced by the `n`-fold absolute Frobenius raises sections to
their `p ^ n`-th powers. -/
@[simp]
lemma absoluteFrobenius_pow_appTop_apply (X : Scheme.{u}) (p : ℕ) [Fact p.Prime]
    (hX : IsInCharacteristic X p) (n : ℕ) (g : Γ(X, ⊤)) :
    (End.asHom (End.of (absoluteFrobenius X p hX) ^ n)).appTop g = g ^ p ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, End.mul_def, Scheme.Hom.comp_appTop, CommRingCat.comp_apply, ih,
      show (absoluteFrobenius X p hX).appTop (g ^ p ^ n) = (g ^ p ^ n) ^ p from
        absoluteFrobenius_app_apply X p hX ⊤ _, ← pow_mul, ← pow_succ]

/-- A scheme over a ring in which `p` vanishes is in characteristic `p`. -/
lemma isInCharacteristic_of_over {R : Type u} [CommRing R] {p : ℕ} [CharP R p]
    (X : Over (Spec (.of R))) : IsInCharacteristic X.left p := by
  let φ : R →+* Γ(X.left, ⊤) := ((Scheme.ΓSpecIso (.of R)).inv ≫ X.hom.appTop).hom
  show (p : Γ(X.left, ⊤)) = 0
  rw [← map_natCast φ, CharP.cast_eq_zero R p]
  exact map_zero φ

/-- On a scheme over a finite field with `p ^ f` elements, the `f`-fold absolute Frobenius is a
morphism over the field: on global sections it raises to the `p ^ f`-th power, which fixes the
image of the field because `a ^ p ^ f = a` there. -/
lemma absoluteFrobenius_pow_comp_hom {k : Type u} [Field k] [Fintype k]
    (X : Over (Spec (.of k))) (p f : ℕ) [Fact p.Prime] [CharP k p]
    (hcard : Fintype.card k = p ^ f) :
    End.asHom (End.of (absoluteFrobenius X.left p (isInCharacteristic_of_over X)) ^ f) ≫
      X.hom = X.hom := by
  have key (a : k) : ((Scheme.ΓSpecIso (.of k)).inv ≫ X.hom.appTop).hom a ^ p ^ f =
      ((Scheme.ΓSpecIso (.of k)).inv ≫ X.hom.appTop).hom a := by
    rw [← map_pow, ← hcard, FiniteField.pow_card]
  refine ext_to_Spec ?_
  show ((Scheme.ΓSpecIso (.of k)).inv ≫
      (End.asHom (End.of (absoluteFrobenius X.left p (isInCharacteristic_of_over X)) ^ f) ≫
        X.hom).appTop : CommRingCat.of k ⟶ Γ(X.left, ⊤)) =
    (Scheme.ΓSpecIso (.of k)).inv ≫ X.hom.appTop
  rw [Scheme.Hom.comp_appTop, ← Category.assoc]
  ext a
  rw [CommRingCat.comp_apply, absoluteFrobenius_pow_appTop_apply]
  exact key a

/-- **Stacks Project, Tag 03SQ.** The geometric Frobenius of a scheme over a finite field of
characteristic `p` and cardinality `p ^ f`. It is the `f`-fold absolute Frobenius, bundled with
its canonical structure as a morphism over the field. -/
@[stacks 03SQ, implicit_reducible, sga "4½ Rapport 1.1"]
noncomputable def geometricFrobenius {k : Type u} [Field k] [Fintype k]
    (X : Over (Spec (.of k))) (p f : ℕ) [Fact p.Prime] [CharP k p]
    (hcard : Fintype.card k = p ^ f) : X ⟶ X :=
  Over.homMk
    (End.asHom (End.of
      (absoluteFrobenius X.left p (isInCharacteristic_of_over X)) ^ f))
    (absoluteFrobenius_pow_comp_hom X p f hcard)

/-- The underlying scheme morphism of the geometric Frobenius is the `f`-fold absolute
Frobenius. -/
@[simp]
lemma geometricFrobenius_left {k : Type u} [Field k] [Fintype k]
    (X : Over (Spec (.of k))) (p f : ℕ) [Fact p.Prime] [CharP k p]
    (hcard : Fintype.card k = p ^ f) :
    (geometricFrobenius X p f hcard).left =
      End.asHom (End.of
        (absoluteFrobenius X.left p (isInCharacteristic_of_over X)) ^ f) := rfl

section ArithmeticFrobenius

variable (k : Type u) [Field k] [Fintype k] (K : Type v) [Field K] [Algebra k K] (p f : ℕ)
  [ExpChar K p] [PerfectRing K p]

/-- **Stacks Project, Tag 03SU.** The arithmetic Frobenius `x ↦ x ^ q` of a finite field `k`
with `q = p ^ f` elements, acting on a perfect extension field `K` of exponential
characteristic `p`. It is the `f`-fold Frobenius automorphism of `K`, and it fixes `k`
pointwise because every element of a field with `q` elements satisfies `x ^ q = x`. -/
@[stacks 03SU, sga "7 XXI 5.0"]
noncomputable def arithmeticFrobenius (hcard : Fintype.card k = p ^ f) : K ≃ₐ[k] K :=
  AlgEquiv.ofRingEquiv (f := iterateFrobeniusEquiv K p f) fun x ↦ by
    rw [iterateFrobeniusEquiv_def, ← hcard, ← map_pow, FiniteField.pow_card]

/-- The arithmetic Frobenius raises to the power the cardinality of the base field. -/
@[simp]
lemma arithmeticFrobenius_apply (hcard : Fintype.card k = p ^ f) (x : K) :
    arithmeticFrobenius k K p f hcard x = x ^ Fintype.card k := by
  rw [hcard]
  exact iterateFrobeniusEquiv_def K p f x

/-- A `k`-automorphism of `K` raising to the power the cardinality of `k` is the arithmetic
Frobenius. -/
lemma eq_arithmeticFrobenius (hcard : Fintype.card k = p ^ f) (σ : K ≃ₐ[k] K)
    (hσ : ∀ x : K, σ x = x ^ Fintype.card k) : σ = arithmeticFrobenius k K p f hcard := by
  ext x
  rw [hσ, arithmeticFrobenius_apply]

end ArithmeticFrobenius

/-- The spectrum of a commutative ring of characteristic `p` is a scheme in characteristic
`p`. -/
lemma isInCharacteristic_spec (R : Type u) [CommRing R] (p : ℕ) [CharP R p] :
    IsInCharacteristic (Spec (.of R)) p :=
  isInCharacteristic_of_over (Over.mk (𝟙 (Spec (.of R))))

open Polynomial in
/-- In a finite field with `p ^ f` elements and `1 < f` the `p`-th power map is not the identity:
the polynomial `X ^ p - X` has at most `p` roots, whereas the field has `p ^ f > p` elements. -/
lemma exists_pow_ne_self {K : Type u} [Field K] [Fintype K] {p f : ℕ} (hp : p.Prime)
    (hcard : Fintype.card K = p ^ f) (hf : 1 < f) : ∃ x : K, x ^ p ≠ x := by
  by_contra hcon
  simp only [not_exists, not_ne_iff] at hcon
  have hsub := Polynomial.card_le_degree_of_subset_roots (R := K) (p := X ^ p - X)
    (Z := Finset.univ) fun x _ ↦ by
      rw [mem_roots']
      exact ⟨FiniteField.X_pow_card_sub_X_ne_zero K hp.one_lt, by simp [IsRoot, hcon x]⟩
  rw [Finset.card_univ, FiniteField.X_pow_card_sub_X_natDegree_eq K hp.one_lt, hcard] at hsub
  exact absurd hsub (by simpa using Nat.pow_lt_pow_right hp.one_lt hf)

/-- Two iterates of the absolute Frobenius of the spectrum of a ring `K` agree only if the
corresponding power maps agree on `K`. -/
lemma pow_eq_pow_of_absoluteFrobenius_pow_eq {K : Type u} [CommRing K] {p : ℕ} [Fact p.Prime]
    (hK : IsInCharacteristic (Spec (.of K)) p) {m n : ℕ}
    (h : End.asHom (End.of (absoluteFrobenius (Spec (.of K)) p hK) ^ m) =
      End.asHom (End.of (absoluteFrobenius (Spec (.of K)) p hK) ^ n)) (x : K) :
    x ^ p ^ m = x ^ p ^ n := by
  set ι : K →+* Γ(Spec (.of K), ⊤) := (Scheme.ΓSpecIso (.of K)).inv.hom
  set π : Γ(Spec (.of K), ⊤) →+* K := (Scheme.ΓSpecIso (.of K)).hom.hom
  have hπι : ∀ y : K, π (ι y) = y := by
    intro y
    show ((Scheme.ΓSpecIso (.of K)).hom.hom.comp (Scheme.ΓSpecIso (.of K)).inv.hom) y = y
    rw [← CommRingCat.hom_comp, Iso.inv_hom_id, CommRingCat.hom_id, RingHom.id_apply]
  have key : ι x ^ p ^ m = ι x ^ p ^ n := by
    rw [← absoluteFrobenius_pow_appTop_apply (Spec (.of K)) p hK m (ι x),
      ← absoluteFrobenius_pow_appTop_apply (Spec (.of K)) p hK n (ι x), h]
  simpa only [map_pow, hπι] using congrArg π key

/-- On the spectrum of a finite field with `p ^ f` elements and `1 < f`, the absolute Frobenius
differs from its `f`-fold iterate, the latter being the identity on global sections. -/
lemma absoluteFrobenius_pow_one_ne_absoluteFrobenius_pow (K : Type u) [Field K] [Fintype K]
    (p f : ℕ) [Fact p.Prime] [CharP K p] (hcard : Fintype.card K = p ^ f) (hf : 1 < f) :
    End.asHom (End.of (absoluteFrobenius (Spec (.of K)) p (isInCharacteristic_spec K p)) ^ 1) ≠
      End.asHom
        (End.of (absoluteFrobenius (Spec (.of K)) p (isInCharacteristic_spec K p)) ^ f) := by
  intro h
  obtain ⟨x, hx⟩ := exists_pow_ne_self (K := K) Fact.out hcard hf
  have hpow := pow_eq_pow_of_absoluteFrobenius_pow_eq (isInCharacteristic_spec K p) h x
  rw [pow_one] at hpow
  rw [hpow, ← hcard, FiniteField.pow_card] at hx
  exact hx rfl

/-- **Stacks Project, Tag 03SS.** The geometric Frobenius of a scheme over a finite field with
`p ^ f` elements is the `f`-fold absolute Frobenius. The exponent is read off from the base
field, so a scheme over two finite fields `k` and `k'` can have two distinct geometric Frobenius
endomorphisms, as does the spectrum of a field with `p ^ 2` elements over the prime field and
over itself. -/
@[stacks 03SS]
theorem geometricFrobenius_left_eq_absoluteFrobenius_pow_and_exists_ne :
    (∀ (k : Type u) [Field k] [Fintype k] (p f : ℕ) [Fact p.Prime] [CharP k p]
        (hcard : Fintype.card k = p ^ f) (U : Over (Spec (.of k))),
        (geometricFrobenius U p f hcard).left =
          End.asHom (End.of (absoluteFrobenius U.left p (isInCharacteristic_of_over U)) ^ f)) ∧
      ∃ (p f f' : ℕ) (_ : Fact p.Prime) (k k' : Type u) (_ : Field k) (_ : Fintype k)
        (_ : CharP k p) (_ : Field k') (_ : Fintype k') (_ : CharP k' p)
        (hcard : Fintype.card k = p ^ f) (hcard' : Fintype.card k' = p ^ f') (U : Scheme.{u})
        (g : U ⟶ Spec (.of k)) (g' : U ⟶ Spec (.of k')),
        (geometricFrobenius (Over.mk g) p f hcard).left ≠
          (geometricFrobenius (Over.mk g') p f' hcard').left := by
  refine ⟨fun k _ _ p f _ _ hcard U ↦ geometricFrobenius_left U p f hcard, ?_⟩
  have : Fintype (GaloisField 2 2) := Fintype.ofFinite _
  have hcard' : Fintype.card (ULift.{u} (GaloisField 2 2)) = 2 ^ 2 := by
    rw [← Nat.card_eq_fintype_card, Nat.card_ulift, GaloisField.card 2 2 two_ne_zero]
  refine ⟨2, 1, 2, Nat.fact_prime_two, ULift.{u} (ZMod 2), ULift.{u} (GaloisField 2 2),
    inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    by rw [← Nat.card_eq_fintype_card, Nat.card_ulift, Nat.card_zmod, pow_one], hcard',
    Spec (.of (ULift.{u} (GaloisField 2 2))),
    Spec.map (CommRingCat.ofHom (RingHom.ulift (algebraMap (ZMod 2) (GaloisField 2 2)))),
    𝟙 _, ?_⟩
  rw [geometricFrobenius_left, geometricFrobenius_left]
  exact absoluteFrobenius_pow_one_ne_absoluteFrobenius_pow
    (ULift.{u} (GaloisField 2 2)) 2 2 hcard' one_lt_two

end Stacks.Frobenius

end
