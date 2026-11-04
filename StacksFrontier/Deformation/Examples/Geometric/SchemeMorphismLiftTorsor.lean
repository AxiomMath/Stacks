module

public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.InfinitesimalDeformationThickenedBaseAction
public import StacksFrontier.Deformation.Examples.Geometric.SpecialFibreIdealSheaf

/-!
# The torsor of lifts of a morphism of schemes to a pair of deformations

Let `κ` be the residue field of the deformation theory, let `X` and `Y` be schemes over `κ` and
let `f : X ⟶ Y` be a morphism over `κ`. Let `P` be a deformation of `X` and `Q` a deformation of
`Y`, in the sense of `Deformation.Examples.SchemeDeformationCategory`, and let `e` be a morphism
in `𝒞_Λ` from the base of `Q` to the base of `P`, so that the ambient scheme of `P` sits over
the spectrum of the base of `Q`. This file reads
`Stacks.Thickenings.exists_simplyTransitive_addAction_liftsOverBaseOfBase` —
[Stacks Project, Tag 0CK2] — at that data, which is what the six-term exact sequence of a
deformation of a morphism of schemes ([Stacks Project, Tag 0E3V]) needs.

The dictionary with the variables of [Stacks Project, Tag 0CK2] is

| Tag 0CK2        | here                                                 |
| --------------- | ---------------------------------------------------- |
| `i : X ⟶ X'`    | `P.specialMap : X.left ⟶ P.scheme`                   |
| `j : Y ⟶ Y'`    | `Q.specialMap : Y.left ⟶ Q.scheme`                   |
| `k : Z ⟶ Z'`    | `residueSpecMap Q.base : Spec κ ⟶ baseSpec Q.base`   |
| `h : Y ⟶ Z`     | `Y.hom : Y.left ⟶ Spec κ`                            |
| `h' : Y' ⟶ Z'`  | `Q.toBase : Q.scheme ⟶ baseSpec Q.base`              |
| `g' : X' ⟶ Z'`  | `Deformation.Examples.deformationAmbientToBase P e`  |
| `a : X ⟶ Y`     | `f : X.left ⟶ Y.left`                                |
| `sq`            | `Q.specialCartesian`                                 |

**The letter `k`.** Throughout `Deformation.Examples` the letter `k` is the residue field; in
[Stacks Project, Tag 0CK2] it is the immersion of the base thickening. The residue field is
called `κ` in this file, and `k` is kept for the base immersion in the one lemma stated for
abstract schemes (`Deformation.Examples.isBaseCompatibleConormalMap_of_globalLift`), where no
residue field occurs. The field `base` of a deformation and the base *immersion* of
[Stacks Project, Tag 0CK2] are likewise different things: the former is an object of `𝒞_Λ`, the
latter the closed point `residueSpecMap` of its spectrum.

## Main definitions

* `Deformation.Examples.deformationAmbientToBase`: the structure morphism of the ambient scheme
  of a deformation, read over the spectrum of another object of `𝒞_Λ` mapping to its base. This
  is the `g' : X' ⟶ Z'` of [Stacks Project, Tag 0CK2].
* `Deformation.Examples.globalLiftsOverBase`: the morphisms `P.scheme ⟶ Q.scheme` over
  `baseSpec Q.base` whose restriction to the special fibre is `f`.
* `Deformation.Examples.liftsOverBaseTopEquiv` and
  `Deformation.Examples.globalLiftsOverBaseEquiv`: the identification of the elementary lifting
  rule of [Stacks Project, Tag 04FK] at the open `⊤` with those global morphisms.

## Main results

* `Deformation.Examples.specialMap_comp_deformationAmbientToBase`: the commuting square
  `i ≫ g' = (a ≫ h) ≫ k` of [Stacks Project, Tag 0CK2] for a deformation of `X`.
* `Deformation.Examples.ker_specialMap_pow_two_eq_bot`: the special-fibre immersion of a
  deformation is a **first order** thickening as soon as the maximal ideal of the base has square
  zero. This is the hypothesis `i.ker ^ 2 = ⊥` of [Stacks Project, Tag 0CK2].
* `Deformation.Examples.isBaseCompatibleConormalMap_of_globalLift`: the conormal datum of a lift
  defined on all of `X'` is compatible with the base — the unrestricted companion of
  `Stacks.Thickenings.isBaseCompatibleConormalMap_of_lift`.
* `Deformation.Examples.exists_simplyTransitive_addAction_liftsOverBase_deformation`:
  **[Stacks Project, Tag 0CK2] for a pair of deformations.** The group of sections of
  `SheafHom(f^*Ω_{Y/κ}, 𝒞)` acts on the morphisms `V ⟶ Q.scheme` over `baseSpec Q.base`
  restricting to `f`, compatibly with restriction and simply transitively over an open carrying a
  lift.
* `Deformation.Examples.exists_simplyTransitive_addAction_globalLiftsOverBase`: the same action
  at `V = ⊤`, on the global lifts of `f`.
* `Deformation.Examples.isIso_preimage_top_ι`,
  `Deformation.Examples.globalLift_conditions_of_liftsOverBase_top` and
  `Deformation.Examples.liftsOverBase_top_conditions_of_globalLift`: the two conditions of
  `Stacks.Thickenings.liftsOverBase` carried across `AlgebraicGeometry.Scheme.topIso`, which is
  what `Deformation.Examples.liftsOverBaseTopEquiv` is assembled from.

## Implementation notes

The two deformations are *not* required to have equal bases. Asking for `P.base = Q.base` would
force the structure morphism of `P` to be transported along an equality of schemes; instead a
morphism `e : Q.base ⟶ P.base` of `𝒞_Λ` is taken as data and
`Deformation.Examples.deformationAmbientToBase` composes the structure morphism of `P` with
`Deformation.Examples.baseSpecMap e`. The case the six-term sequence needs is the one where the
two bases are the same object and `e = 𝟙`; there `Deformation.Examples.baseSpecMap_id` collapses
the composite.

A lift `f' : P.scheme ⟶ Q.scheme` of `f` is taken as a hypothesis of the action statement: it is
the trivial deformation of `f`, and [Stacks Project, Tag 0CK2] only describes the lifts over an
open that carries one. It is used exactly once, to manufacture the conormal datum `A` of
[Stacks Project, Tag 04FH] and its base compatibility; by
`Stacks.Thickenings.eq_of_isBaseCompatibleConormalMap` that datum does not depend on the choice.

`Stacks.Thickenings.isBaseCompatibleConormalMap_of_lift` produces base compatibility for the
*restricted* thickening `i ∣_ V` and a lift defined on `V`, which is not the shape
[Stacks Project, Tag 0CK2] asks of its hypothesis `hA`. Its argument is insensitive to the
restriction, so `Deformation.Examples.isBaseCompatibleConormalMap_of_globalLift` repeats it for
`i` itself and a lift defined on `X'`.

The square-zero hypothesis travels from the base to the special-fibre immersion through
`Deformation.Examples.ker_eq_baseIdeal_of_isPullback`, which identifies the kernel ideal sheaf of
the special-fibre immersion with `Stacks.BaseAdicFiltration.baseIdeal` of the maximal ideal: a
power of that ideal sheaf is computed on each affine open by
`Stacks.BaseAdicFiltration.baseIdeal_ideal`, where it is the image of the corresponding power of
the maximal ideal.

That the special-fibre immersion of a deformation and the closed point of the spectrum of an
object of `𝒞_Λ` are closed immersions are theorems, not instances, in
`StacksFrontier.Deformation.Examples.Geometric.OpenSubschemes`; they are made `local instance`s here
so that the statements of [Stacks Project, Tag 0CK2] elaborate.

## References

* [Stacks Project, Tag 04FH](https://stacks.math.columbia.edu/tag/04FH)
* [Stacks Project, Tag 04FK](https://stacks.math.columbia.edu/tag/04FK)
* [Stacks Project, Tag 0CK2](https://stacks.math.columbia.edu/tag/0CK2)
* [Stacks Project, Tag 0DY7](https://stacks.math.columbia.edu/tag/0DY7)
* [Stacks Project, Tag 0E3V](https://stacks.math.columbia.edu/tag/0E3V)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open RingedSpaceModuleAdjunction
open AlgebraicGeometry
open Stacks.Immersion
open Stacks.Thickenings

universe u

namespace Deformation.Examples

attribute [local instance] deformationSpecialMap_isClosedImmersion
  residueSpecMap_isClosedImmersion

variable {Λ κ : Type u} [CommRing Λ] [Field κ] [Algebra Λ κ]

/-! ### The base immersion of Tag 0CK2 -/

variable {X Y : Over (Spec (CommRingCat.of κ))}

/-- **The structure morphism of the ambient scheme of a deformation, read over another base.**
For a deformation `P` of `X` and a morphism `e : A ⟶ P.base` of `𝒞_Λ`, this is the composite
`P.scheme ⟶ baseSpec P.base ⟶ baseSpec A`. It is the morphism `g' : X' ⟶ Z'` of
[Stacks Project, Tag 0CK2]; for `A = P.base` and `e = 𝟙` it is the structure morphism itself. -/
abbrev deformationAmbientToBase (P : SchemeDeformationCategory (Λ := Λ) (k := κ) X)
    {A : ArtinianLocalAlgCat.{u, u, u} Λ κ} (e : A ⟶ P.base) : P.scheme ⟶ baseSpec A :=
  P.toBase ≫ baseSpecMap e

/-- **The commuting square `i ≫ g' = (a ≫ h) ≫ k` of [Stacks Project, Tag 0CK2].** The square
identifying the special fibre of a deformation `P` of `X` says that `P.specialMap ≫ P.toBase` is
`X.hom` followed by the closed point; composing with `Spec e` and factoring `X.hom` as
`f ≫ Y.hom` gives the compatibility that [Stacks Project, Tag 0CK2] asks of its data. -/
theorem specialMap_comp_deformationAmbientToBase (f : X.left ⟶ Y.left) (hf : f ≫ Y.hom = X.hom)
    (P : SchemeDeformationCategory (Λ := Λ) (k := κ) X)
    {A : ArtinianLocalAlgCat.{u, u, u} Λ κ} (e : A ⟶ P.base) :
    P.specialMap ≫ deformationAmbientToBase P e = (f ≫ Y.hom) ≫ residueSpecMap A := by
  show P.specialMap ≫ P.toBase ≫ baseSpecMap e = (f ≫ Y.hom) ≫ residueSpecMap A
  rw [← Category.assoc, P.specialCartesian.w, ← hf, Category.assoc,
    residueSpecMap_naturality]

/-! ### The special-fibre immersion is a first order thickening -/

/-- **The special fibre of a deformation over a square-zero base is a first order thickening.**
The kernel ideal sheaf of the special-fibre immersion is the ideal sheaf generated by the maximal
ideal of the base (`Deformation.Examples.ker_eq_baseIdeal_of_isPullback`), and on an affine open
the ideal of that sheaf is the image of the maximal ideal, so its square is the image of the
square of the maximal ideal.

This is the hypothesis `i.ker ^ 2 = ⊥` of [Stacks Project, Tag 0CK2]. For the dual numbers
`Deformation.artinianDualNumbers Λ κ`, the base of the deformations the six-term sequence of
[Stacks Project, Tag 0E3V] is built from, the hypothesis holds. -/
theorem ker_specialMap_pow_two_eq_bot (P : SchemeDeformationCategory (Λ := Λ) (k := κ) X)
    (hm : IsLocalRing.maximalIdeal P.base ^ 2 = ⊥) : P.specialMap.ker ^ 2 = ⊥ := by
  rw [ker_eq_baseIdeal_of_isPullback P.toBase P.specialCartesian]
  refine Scheme.IdealSheafData.ext (funext fun V => ?_)
  show (Stacks.BaseAdicFiltration.baseIdeal P.toBase
    (IsLocalRing.maximalIdeal P.base)).ideal V ^ 2 = ⊥
  rw [Stacks.BaseAdicFiltration.baseIdeal_ideal, ← Ideal.map_pow, hm, Ideal.map_bot]

/-! ### The conormal datum of a lift defined on the whole ambient scheme -/

section Unrestricted

variable {X₀ X' Y₀ Y' Z Z' : Scheme.{u}} {i : X₀ ⟶ X'} {j : Y₀ ⟶ Y'} {k : Z ⟶ Z'}
  [IsImmersion i] [IsImmersion j] [IsImmersion k]
  {h : Y₀ ⟶ Z} {h' : Y' ⟶ Z'} {g' : X' ⟶ Z'} {a : X₀ ⟶ Y₀}

/-- **The conormal datum of a lift defined on all of `X'` is compatible with the base.** This is
`Stacks.Thickenings.isBaseCompatibleConormalMap_of_lift` for the thickening `i` itself rather
than its restriction `i ∣_ V` to an open: stacking the square of the lift `f'` on the cartesian
square gives the square `i ≫ g' = (a ≫ h) ≫ k`, whose canonical map of conormal sheaves does not
involve `f'`.

Here `k : Z ⟶ Z'` is the immersion of the base thickening of [Stacks Project, Tag 0CK2], not a
residue field. -/
theorem isBaseCompatibleConormalMap_of_globalLift (sq : IsPullback j h h' k)
    (ci : i ≫ g' = (a ≫ h) ≫ k) {f' : X' ⟶ Y'} (hf'₁ : f' ≫ h' = g')
    (hf'₂ : i ≫ f' = a ≫ j) :
    IsBaseCompatibleConormalMap i j k h h' g' a sq.w ci
      (immersionConormalSheafMap i j a f' (toShHom_square hf'₂)) := by
  refine Eq.trans ?_ (immersionConormalSheafMap_congr i k (rfl : a ≫ h = a ≫ h) hf'₁
    (toShHom_square (square_comp hf'₂ sq.w)) (toShHom_square ci)).symm
  rw [eqToHom_refl, Category.id_comp]
  exact (immersionConormalSheafMap_comp i j k a f' hf'₂ h h' sq.w).symm

end Unrestricted

/-! ### Tag 0CK2 for a pair of deformations -/

/-- **[Stacks Project, Tag 0CK2] for a pair of deformations of schemes over one base.** Let
`f : X ⟶ Y` be a morphism of schemes over the residue field `κ`, let `P` be a deformation of `X`
and `Q` a deformation of `Y`, let `e : Q.base ⟶ P.base` be a morphism of `𝒞_Λ`, assume the
maximal ideal of `P.base` has square zero, and let `f' : P.scheme ⟶ Q.scheme` be a lift of `f`
over `baseSpec Q.base`. Then the additive group of sections of
`SheafHom_{𝒪_X}(f^*Ω_{Y/κ}, 𝒞_{X/P.scheme})` over `P.specialMap ⁻¹ᵁ V` **acts** on the morphisms
`V ⟶ Q.scheme` over `baseSpec Q.base` restricting to `f` on `P.specialMap ⁻¹ᵁ V`, for every open
`V` of `P.scheme`; the action commutes with the restriction maps, and over an open carrying a
lift it is simply transitive.

This is `Stacks.Thickenings.exists_simplyTransitive_addAction_liftsOverBaseOfBase` at the data
listed in the module docstring. The conormal datum of [Stacks Project, Tag 04FH] is the one
attached to `f'` by `Deformation.Examples.isBaseCompatibleConormalMap_of_globalLift`; it is
determined by `f` and does not appear in the conclusion. -/
theorem exists_simplyTransitive_addAction_liftsOverBase_deformation
    (f : X.left ⟶ Y.left) (hf : f ≫ Y.hom = X.hom)
    (P : SchemeDeformationCategory (Λ := Λ) (k := κ) X)
    (Q : SchemeDeformationCategory (Λ := Λ) (k := κ) Y) (e : Q.base ⟶ P.base)
    (hm : IsLocalRing.maximalIdeal P.base ^ 2 = ⊥) (f' : P.scheme ⟶ Q.scheme)
    (hf'₁ : f' ≫ Q.toBase = deformationAmbientToBase P e)
    (hf'₂ : P.specialMap ≫ f' = f ≫ Q.specialMap) :
    ∃ act : ∀ V : P.scheme.Opens, deformationHomSections P.specialMap f Y.hom V →
        liftsOverBase P.specialMap Q.specialMap (deformationAmbientToBase P e) Q.toBase f V →
          liftsOverBase P.specialMap Q.specialMap (deformationAmbientToBase P e) Q.toBase f V,
      (∀ (V : P.scheme.Opens) (c : liftsOverBase P.specialMap Q.specialMap
          (deformationAmbientToBase P e) Q.toBase f V), act V 0 c = c) ∧
        (∀ (V : P.scheme.Opens) (θ η : deformationHomSections P.specialMap f Y.hom V)
          (c : liftsOverBase P.specialMap Q.specialMap
            (deformationAmbientToBase P e) Q.toBase f V),
          act V (θ + η) c = act V θ (act V η c)) ∧
        (∀ (V V' : P.scheme.Opens) (hV : V' ≤ V)
          (θ : deformationHomSections P.specialMap f Y.hom V)
          (c : liftsOverBase P.specialMap Q.specialMap
            (deformationAmbientToBase P e) Q.toBase f V),
          liftsOverBaseRestrict P.specialMap Q.specialMap (deformationAmbientToBase P e)
              Q.toBase f hV (act V θ c)
            = act V' (moduleHomSections.restrict (P.specialMap.preimage_mono hV) θ)
                (liftsOverBaseRestrict P.specialMap Q.specialMap
                  (deformationAmbientToBase P e) Q.toBase f hV c)) ∧
        ∀ (V : P.scheme.Opens) (b₀ c₀ : liftsOverBase P.specialMap Q.specialMap
            (deformationAmbientToBase P e) Q.toBase f V),
          ∃! θ : deformationHomSections P.specialMap f Y.hom V, act V θ b₀ = c₀ :=
  exists_simplyTransitive_addAction_liftsOverBaseOfBase
    (ker_specialMap_pow_two_eq_bot P hm) Q.specialCartesian
    (specialMap_comp_deformationAmbientToBase f hf P e)
    (isBaseCompatibleConormalMap_of_globalLift Q.specialCartesian
      (specialMap_comp_deformationAmbientToBase f hf P e) hf'₁ hf'₂)

/-! ### The lifts over the whole ambient scheme -/

/-- **The inclusion of the preimage of `⊤` is invertible.** The preimage of the whole of `X'`
under `i` is the whole of `X₀`, whose inclusion is `AlgebraicGeometry.Scheme.topIso`. -/
theorem isIso_preimage_top_ι {X₀ X' : Scheme.{u}} (i : X₀ ⟶ X') :
    IsIso (i ⁻¹ᵁ (⊤ : X'.Opens)).ι := by
  have hpt : (i ⁻¹ᵁ (⊤ : X'.Opens)) = ⊤ := by simp
  rw [hpt]
  exact inferInstanceAs (IsIso X₀.topIso.hom)

/-- Restricting `i` to the preimage of `⊤` and including into `X'` is `i` after the inclusion. -/
private theorem restrict_top_ι_comp {X₀ X' Y' : Scheme.{u}} (i : X₀ ⟶ X') (b : X' ⟶ Y') :
    i ∣_ (⊤ : X'.Opens) ≫ (⊤ : X'.Opens).ι ≫ b = (i ⁻¹ᵁ (⊤ : X'.Opens)).ι ≫ i ≫ b := by
  rw [← Category.assoc, morphismRestrict_ι, Category.assoc]

/-- **A lift over the open `⊤` is a lift over the ambient scheme.** The two conditions of
`Stacks.Thickenings.liftsOverBase` at the open `⊤`, read for `X'.topIso.inv ≫ b`. The second one
is obtained by cancelling the invertible inclusion `(i ⁻¹ᵁ ⊤).ι`. -/
theorem globalLift_conditions_of_liftsOverBase_top {X₀ X' Y₀ Y' S : Scheme.{u}} (i : X₀ ⟶ X')
    (j : Y₀ ⟶ Y') (pX' : X' ⟶ S) (pY' : Y' ⟶ S) (a : X₀ ⟶ Y₀)
    {b : (⊤ : X'.Opens).toScheme ⟶ Y'} (hb₁ : b ≫ pY' = (⊤ : X'.Opens).ι ≫ pX')
    (hb₂ : i ∣_ (⊤ : X'.Opens) ≫ b = ((i ⁻¹ᵁ (⊤ : X'.Opens)).ι ≫ a) ≫ j) :
    (X'.topIso.inv ≫ b) ≫ pY' = pX' ∧ i ≫ X'.topIso.inv ≫ b = a ≫ j := by
  have := isIso_preimage_top_ι i
  refine ⟨?_, (cancel_epi (i ⁻¹ᵁ (⊤ : X'.Opens)).ι).mp ?_⟩
  · rw [Category.assoc, hb₁, ← Category.assoc, Scheme.toIso_inv_ι, Category.id_comp]
  · rw [← restrict_top_ι_comp, ← Category.assoc (⊤ : X'.Opens).ι, Scheme.ι_toIso_inv,
      Category.id_comp, hb₂, Category.assoc]

/-- **A lift over the ambient scheme is a lift over the open `⊤`.** The two conditions of
`Stacks.Thickenings.liftsOverBase` at the open `⊤`, read for `(⊤ : X'.Opens).ι ≫ b`. -/
theorem liftsOverBase_top_conditions_of_globalLift {X₀ X' Y₀ Y' S : Scheme.{u}} (i : X₀ ⟶ X')
    (j : Y₀ ⟶ Y') (pX' : X' ⟶ S) (pY' : Y' ⟶ S) (a : X₀ ⟶ Y₀) {b : X' ⟶ Y'}
    (hb₁ : b ≫ pY' = pX') (hb₂ : i ≫ b = a ≫ j) :
    ((⊤ : X'.Opens).ι ≫ b) ≫ pY' = (⊤ : X'.Opens).ι ≫ pX' ∧
      i ∣_ (⊤ : X'.Opens) ≫ (⊤ : X'.Opens).ι ≫ b = ((i ⁻¹ᵁ (⊤ : X'.Opens)).ι ≫ a) ≫ j := by
  refine ⟨by rw [Category.assoc, hb₁], ?_⟩
  rw [restrict_top_ι_comp, hb₂, Category.assoc]

/-- **The elementary lifting rule of [Stacks Project, Tag 04FK] at the open `⊤`.** A morphism out
of `(⊤ : X'.Opens).toScheme` over `S` extending `a` is the same thing as a morphism out of `X'`
over `S` extending `a`, by composing with the two directions of
`AlgebraicGeometry.Scheme.topIso`. -/
def liftsOverBaseTopEquiv {X₀ X' Y₀ Y' S : Scheme.{u}} (i : X₀ ⟶ X') (j : Y₀ ⟶ Y')
    (pX' : X' ⟶ S) (pY' : Y' ⟶ S) (a : X₀ ⟶ Y₀) :
    liftsOverBase i j pX' pY' a ⊤ ≃
      { b : X' ⟶ Y' // b ≫ pY' = pX' ∧ i ≫ b = a ≫ j } where
  toFun c := ⟨X'.topIso.inv ≫ c.1,
    globalLift_conditions_of_liftsOverBase_top i j pX' pY' a c.2.1 c.2.2⟩
  invFun b := ⟨(⊤ : X'.Opens).ι ≫ b.1,
    liftsOverBase_top_conditions_of_globalLift i j pX' pY' a b.2.1 b.2.2⟩
  left_inv c := Subtype.ext
    (((Category.assoc (⊤ : X'.Opens).ι X'.topIso.inv c.1).symm.trans
      (congrArg (fun z : (⊤ : X'.Opens).toScheme ⟶ (⊤ : X'.Opens).toScheme => z ≫ c.1)
        (Scheme.ι_toIso_inv X'))).trans (Category.id_comp c.1))
  right_inv b := Subtype.ext
    (((Category.assoc X'.topIso.inv (⊤ : X'.Opens).ι b.1).symm.trans
      (congrArg (fun z : X' ⟶ X' => z ≫ b.1) (Scheme.toIso_inv_ι X'))).trans
      (Category.id_comp b.1))

/-- **The global lifts of `f` to a pair of deformations.** The morphisms
`P.scheme ⟶ Q.scheme` over `baseSpec Q.base` whose restriction to the special fibre is `f`. -/
def globalLiftsOverBase (f : X.left ⟶ Y.left)
    (P : SchemeDeformationCategory (Λ := Λ) (k := κ) X)
    (Q : SchemeDeformationCategory (Λ := Λ) (k := κ) Y) (e : Q.base ⟶ P.base) : Type u :=
  { b : P.scheme ⟶ Q.scheme // b ≫ Q.toBase = deformationAmbientToBase P e ∧
    P.specialMap ≫ b = f ≫ Q.specialMap }

/-- **The elementary lifting rule at `⊤` is the set of global lifts.**
`Deformation.Examples.liftsOverBaseTopEquiv` for a pair of deformations, with the codomain named
`Deformation.Examples.globalLiftsOverBase`. -/
def globalLiftsOverBaseEquiv (f : X.left ⟶ Y.left)
    (P : SchemeDeformationCategory (Λ := Λ) (k := κ) X)
    (Q : SchemeDeformationCategory (Λ := Λ) (k := κ) Y) (e : Q.base ⟶ P.base) :
    liftsOverBase P.specialMap Q.specialMap (deformationAmbientToBase P e) Q.toBase f ⊤ ≃
      globalLiftsOverBase f P Q e :=
  liftsOverBaseTopEquiv P.specialMap Q.specialMap (deformationAmbientToBase P e) Q.toBase f

/-- **[Stacks Project, Tag 0CK2] for the global lifts of `f`.** The specialisation of
`Deformation.Examples.exists_simplyTransitive_addAction_liftsOverBase_deformation` to the open
`⊤`, transported along `Deformation.Examples.liftsOverBaseTopEquiv`: the sections over `X` of
`SheafHom_{𝒪_X}(f^*Ω_{Y/κ}, 𝒞_{X/P.scheme})` act simply transitively on the morphisms
`P.scheme ⟶ Q.scheme` over `baseSpec Q.base` restricting to `f`.

The hypotheses are those of the unrestricted statement; the lift `f'` is what makes the set of
global lifts nonempty, so that simple transitivity has content. -/
theorem exists_simplyTransitive_addAction_globalLiftsOverBase
    (f : X.left ⟶ Y.left) (hf : f ≫ Y.hom = X.hom)
    (P : SchemeDeformationCategory (Λ := Λ) (k := κ) X)
    (Q : SchemeDeformationCategory (Λ := Λ) (k := κ) Y) (e : Q.base ⟶ P.base)
    (hm : IsLocalRing.maximalIdeal P.base ^ 2 = ⊥) (f' : P.scheme ⟶ Q.scheme)
    (hf'₁ : f' ≫ Q.toBase = deformationAmbientToBase P e)
    (hf'₂ : P.specialMap ≫ f' = f ≫ Q.specialMap) :
    ∃ act : deformationHomSections P.specialMap f Y.hom ⊤ →
        globalLiftsOverBase f P Q e → globalLiftsOverBase f P Q e,
      (∀ c : globalLiftsOverBase f P Q e, act 0 c = c) ∧
        (∀ (θ η : deformationHomSections P.specialMap f Y.hom ⊤)
          (c : globalLiftsOverBase f P Q e), act (θ + η) c = act θ (act η c)) ∧
        ∀ b₀ c₀ : globalLiftsOverBase f P Q e,
          ∃! θ : deformationHomSections P.specialMap f Y.hom ⊤, act θ b₀ = c₀ := by
  obtain ⟨act, hzero, hadd, -, huniq⟩ :=
    exists_simplyTransitive_addAction_liftsOverBase_deformation f hf P Q e hm f' hf'₁ hf'₂
  set E := globalLiftsOverBaseEquiv f P Q e
  refine ⟨fun θ c => E (act ⊤ θ (E.symm c)), fun c => ?_, fun θ η c => ?_, fun b₀ c₀ => ?_⟩
  · show E (act ⊤ 0 (E.symm c)) = c
    rw [hzero]
    exact E.apply_symm_apply c
  · show E (act ⊤ (θ + η) (E.symm c)) = E (act ⊤ θ (E.symm (E (act ⊤ η (E.symm c)))))
    rw [hadd, Equiv.symm_apply_apply]
  · obtain ⟨θ, hθ, hu⟩ := huniq ⊤ (E.symm b₀) (E.symm c₀)
    refine ⟨θ, ?_, fun η hη => hu η (E.injective ?_)⟩
    · show E (act ⊤ θ (E.symm b₀)) = c₀
      rw [hθ]
      exact E.apply_symm_apply c₀
    · show E (act ⊤ η (E.symm b₀)) = E (E.symm c₀)
      rw [E.apply_symm_apply c₀]
      exact hη

end Deformation.Examples

end
