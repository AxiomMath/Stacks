module

public import StacksFrontier.AlgebraicGeometry.TwistedSectionModule.LocalizationComparison
public import StacksFrontier.AlgebraicGeometry.SectionRingProjQuasicoherent.Multiplication

/-!
# Dividing twisted sections by an invertible section of a tensor power

`Stacks.TwistedSections.localizationLiftOfDegree` builds Stacks Tag 0B5L's comparison map
`Γ_*(X, F, L)_{(s)} ⟶ N` out of a family `D : (n : ℕ) → twistSections F L (d * n) →+ N` of
divisions by the powers of a section `s` of `L ^⊗ d`, power-invariant in the sense of
`Stacks.TwistedSections.IsPowerInvariantOfDegree`. This file constructs such a family, in an
arbitrary monoidal category, from the single assumption that `s` is an isomorphism — which is what
a global section of a tensor power of an invertible module becomes after restriction to an open
inside its nonvanishing locus.

The degree `d` is arbitrary: every statement below is at a section `s : powSections L d` of the
`d`-th tensor power.

The route is the whiskering one: multiplication by `s` on twisted sections is
`t ↦ s ≫ actMap t d`, and the point of the construction is that this map is bijective for purely
formal reasons once `s : 𝟙_ C ⟶ L ^⊗ d` is invertible, with no description of the section of
`F ⊗ L ^⊗ (m + d)` named by `s ≫ actMap t d` as an elementary tensor `t ⊗ s`. The divisions are
then *defined* as the inverse of the `k`-fold multiplication, so power-invariance is not a
computation about fractions but a statement that the `k`-fold multiplication is multiplication by
`sᵏ`, which is `Stacks.TwistedSections.shiftIter_eq_actMap` — one induction over
`Stacks.GradedSections.mulMap`.

## Main definitions

* `Stacks.TwistedSections.unitIsoOfInvertible`: `L ^⊗ d ≅ 𝟙_ C`, from an invertible `s`.
* `Stacks.TwistedSections.twistIsoOfInvertible`: `A ⊗ L ^⊗ d ≅ A` for every `A`.
* `Stacks.TwistedSections.unitIsoEndo`: the resulting automorphism of `𝟙_ C` that multiplication
  by `s` becomes under that identification.
* `Stacks.TwistedSections.shiftBySection`: **multiplication by `s`**, raising the degree of a
  twisted section by `d`.
* `Stacks.TwistedSections.shiftIter`: the `k`-fold multiplication, from any degree.
* `Stacks.TwistedSections.shiftPow`: the `k`-fold multiplication, from degree zero to degree
  `d * k`.
* `Stacks.TwistedSections.shiftPowEquiv`: the same, as an isomorphism of additive groups.
* `Stacks.TwistedSections.powerDivision`: **the divisions by the powers of `s`**, namely the
  inverse of `shiftPow`.
* `Stacks.TwistedSections.localizationLiftOfInvertible`: **Stacks Tag 0B5L's comparison map at an
  invertible section**, `Γ_*(X, F, L)_{(s)} ⟶ Γ(X, F)`, with no hypothesis left over.

## Main results

* `Stacks.TwistedSections.actMap_comp_twistPowAddIso`: the action of a twisted section becomes,
  after the associativity isomorphism, right whiskering by the whole tensor power `L ^⊗ d` at
  once.
* `Stacks.TwistedSections.shiftBySection_comp_twistIso`: multiplication by `s` is, after the
  identification `F ⊙ (m + d) ≅ F ⊙ m`, composition with a fixed automorphism of `𝟙_ C`.
* `Stacks.TwistedSections.bijective_shiftBySection` and
  `Stacks.TwistedSections.bijective_shiftPow`: multiplication by `s` and by `sᵏ` are bijective.
* `Stacks.TwistedSections.mul_sectionPow_self`: `sᵏ · s = s ^ (k + 1)` in the section ring.
* `Stacks.TwistedSections.shiftIter_eq_actMap` and
  `Stacks.TwistedSections.gsmul_sectionPow_eq_shiftIter`: **the `k`-fold multiplication is the
  action of `sᵏ`**, which is what identifies the inverse of `shiftPow` with a division by `sᵏ`.
* `Stacks.TwistedSections.isPowerInvariant_powerDivision`: the divisions are power-invariant.
* `Stacks.TwistedSections.shiftPow_powerDivision`: the division of `t` by `sᵏ` is *the* twisted
  section of degree zero whose product with `sᵏ` is `t`.

## Implementation notes

**The degree is added on the right, and the exponent multiplies on the left.** `shiftBySection`
raises the degree from `m` to `m + d`, which is the codomain `F ⊙ (m + d)` of
`Stacks.TwistedSections.actMap` on the nose, and `shiftPow` lands in degree `d * k` because
`d * (k + 1)` and `d * k + d` *are* definitionally equal while `(k + 1) * d` and `k * d + d` are
not. That choice makes the whole tower of iterated multiplications transport-free. The
one reindexing that survives is `Nat.add_assoc` inside `Stacks.TwistedSections.shiftIter`, which
starts from an arbitrary degree `m`, and the distributivity `d * n + d * k = d * (n + k)`, which
is never definitional; `Stacks.TwistedSections.mul_add_degree` names it and
`Stacks.TwistedSections.twistCongr_trans` collapses the composites.

**`s` is invertible as a morphism, not as a section.** The hypothesis is `IsIso s` for
`s : powSections L d`, i.e. `𝟙_ C ⟶ L ^⊗ d`. On a ringed space, for an invertible module `L`, a
global section `s` of `L ^⊗ d` and an open `W` inside the nonvanishing locus of `s`, that is the
trivialization clause of Stacks Tag 01CY, `Stacks.NonvanishingTrivialize.isIso_over_of_le`.
Phrasing the hypothesis this way is what avoids the section-level formula for the monoidality
isomorphism of sheafification: the elementary tensor `t ⊗ s|_W` never appears.

**No fully-faithfulness of `· ⊗ L` is assumed.** A section of `L ^⊗ d` being invertible does not
trivialize `L` itself when `d > 1`, so the degree-one route — `t ↦ t ▷ L` is bijective because
`· ⊗ L` is isomorphic to the identity — is unavailable. The associativity of the twist
`Stacks.SectionRingProjQuasicoherent.twistPowAddIso`, `F ⊙ (m + d) ≅ (F ⊙ m) ⊗ L ^⊗ d`, replaces
it: it moves the `d` new copies of `L` into a single factor `L ^⊗ d`, which `s` does trivialize,
so only `· ⊗ L ^⊗ d ≅ 𝟭` is ever used and that follows from `IsIso s` alone.

## References

* [Stacks Project, Tag 0B5L](https://stacks.math.columbia.edu/tag/0B5L)
* [Stacks Project, Tag 01M4](https://stacks.math.columbia.edu/tag/01M4)
* [Stacks Project, Tag 01CY](https://stacks.math.columbia.edu/tag/01CY)
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory DirectSum
open Stacks.GradedSections (powSections mul mulMap sectionRing HasTrivialSelfBraiding)
open Stacks.TensorPowers (natTensorPow)
open Stacks.SectionRingProjQuasicoherent (twistPowAddIso twistPowAddIso_zero twistPowAddIso_succ)

universe w v u

namespace Stacks.TwistedSections

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] {F L : C}

section Trivialize

/-- **The action of a twisted section is right whiskering by the whole tensor power.** After the
associativity isomorphism, `Stacks.TwistedSections.actMap t d` — which whiskers `t` by `d` copies
of `L`, one at a time — is `t ▷ L ^⊗ d`. -/
theorem actMap_comp_twistPowAddIso {m : ℕ} (t : twistSections F L m) (d : ℕ) :
    actMap t d ≫ (twistPowAddIso F L m d).hom =
      (λ_ (natTensorPow L d)).inv ≫ t ▷ natTensorPow L d := by
  induction d with
  | zero =>
      rw [twistPowAddIso_zero, actMap_zero]
      change t ≫ (ρ_ (twistPow F L m)).inv = (λ_ (𝟙_ C : C)).inv ≫ t ▷ (𝟙_ C : C)
      rw [MonoidalCategory.whiskerRight_id, ← MonoidalCategory.unitors_equal]
      simp
  | succ d ih =>
      rw [twistPowAddIso_succ, actMap_succ, Iso.trans_hom, whiskerRightIso_hom]
      change actMap t d ▷ L ≫ (twistPowAddIso F L m d).hom ▷ L ≫
          (α_ (twistPow F L m) (natTensorPow L d) L).hom =
        (λ_ (natTensorPow L d ⊗ L)).inv ≫ t ▷ (natTensorPow L d ⊗ L)
      rw [← Category.assoc, ← comp_whiskerRight, ih, comp_whiskerRight, Category.assoc,
        associator_naturality_left t (natTensorPow L d) L]
      show _ = (λ_ (natTensorPow L d ⊗ L)).inv ≫ t ▷ (natTensorPow L d ⊗ L)
      rw [MonoidalCategory.leftUnitor_tensor_inv, Category.assoc]

/-- **An invertible section of `L ^⊗ d` trivializes that tensor power.** A section of `L ^⊗ d` is
a morphism `𝟙_ C ⟶ L ^⊗ d`; if it is an isomorphism then `L ^⊗ d` is isomorphic to the monoidal
unit. -/
def unitIsoOfInvertible {d : ℕ} (s : powSections L d) [IsIso s] : natTensorPow L d ≅ 𝟙_ C :=
  (asIso s).symm

/-- **Tensoring with a trivialized `L ^⊗ d` changes nothing:** `A ⊗ L ^⊗ d ≅ A` for every
object `A`. -/
def twistIsoOfInvertible {d : ℕ} (s : powSections L d) [IsIso s] (A : C) :
    A ⊗ natTensorPow L d ≅ A :=
  whiskerLeftIso A (unitIsoOfInvertible s) ≪≫ ρ_ A

/-- **The automorphism of the monoidal unit that multiplication by `s` becomes.** This is
`twistIsoOfInvertible` at `A = 𝟙_ C`, precomposed with `s` itself. -/
def unitIsoEndo {d : ℕ} (s : powSections L d) [IsIso s] : (𝟙_ C : C) ≅ 𝟙_ C :=
  asIso s ≪≫ (λ_ (natTensorPow L d)).symm ≪≫ twistIsoOfInvertible s (𝟙_ C)

/-- **Multiplication by `s` on twisted sections**, raising the degree by `d`. Concretely
`t ↦ s ≫ actMap t d`; no unitor and no transport appear, because the codomain of
`Stacks.TwistedSections.actMap t d` is `F ⊙ (m + d)` on the nose. -/
def shiftBySection {d : ℕ} (s : powSections L d) {m : ℕ} (t : twistSections F L m) :
    twistSections F L (m + d) :=
  s ≫ actMap t d

/-- Multiplication by `s` sends `t` to `s ≫ actMap t d`. -/
theorem shiftBySection_eq {d : ℕ} (s : powSections L d) {m : ℕ} (t : twistSections F L m) :
    shiftBySection s t = s ≫ actMap t d := rfl

/-- **Multiplication by `s` is composition with a fixed automorphism of the unit**, after the
identifications `F ⊙ (m + d) ≅ (F ⊙ m) ⊗ L ^⊗ d` of
`Stacks.SectionRingProjQuasicoherent.twistPowAddIso` and `A ⊗ L ^⊗ d ≅ A` of
`Stacks.TwistedSections.twistIsoOfInvertible`. Two naturality squares — one instance of
`CategoryTheory.MonoidalCategory.whisker_exchange` and one of
`CategoryTheory.MonoidalCategory.rightUnitor_naturality` — move the twisted section `t` past the
trivialization. -/
theorem shiftBySection_comp_twistIso {d : ℕ} (s : powSections L d) [IsIso s] {m : ℕ}
    (t : twistSections F L m) :
    shiftBySection s t ≫ (twistPowAddIso F L m d).hom ≫
        (twistIsoOfInvertible s (twistPow F L m)).hom = (unitIsoEndo s).hom ≫ t := by
  have h1 : t ▷ natTensorPow L d ≫ twistPow F L m ◁ (unitIsoOfInvertible s).hom =
      𝟙_ C ◁ (unitIsoOfInvertible s).hom ≫ t ▷ 𝟙_ C :=
    (whisker_exchange t (unitIsoOfInvertible s).hom).symm
  have h2 : t ▷ 𝟙_ C ≫ (ρ_ (twistPow F L m)).hom = (ρ_ (𝟙_ C : C)).hom ≫ t :=
    MonoidalCategory.rightUnitor_naturality t
  have key : actMap t d ≫ (twistPowAddIso F L m d).hom ≫
      (twistIsoOfInvertible s (twistPow F L m)).hom =
      (λ_ (natTensorPow L d)).inv ≫ (twistIsoOfInvertible s (𝟙_ C)).hom ≫ t := by
    rw [← Category.assoc, actMap_comp_twistPowAddIso]
    simp only [twistIsoOfInvertible, Iso.trans_hom, whiskerLeftIso_hom, Category.assoc]
    rw [← Category.assoc (t ▷ natTensorPow L d), h1]
    simp only [Category.assoc]
    rw [h2]
  rw [shiftBySection_eq, Category.assoc, key]
  simp only [unitIsoEndo, Iso.trans_hom, Iso.symm_hom, asIso_hom, Category.assoc]

/-- `shiftBySection_comp_twistIso` solved for multiplication by `s`. -/
theorem shiftBySection_eq_comp {d : ℕ} (s : powSections L d) [IsIso s] {m : ℕ}
    (t : twistSections F L m) :
    shiftBySection s t = ((unitIsoEndo s).hom ≫ t) ≫
      (twistIsoOfInvertible s (twistPow F L m)).inv ≫ (twistPowAddIso F L m d).inv := by
  rw [← shiftBySection_comp_twistIso s t]
  simp

/-- **Multiplication by an invertible `s` is bijective on twisted sections of each degree.** -/
theorem bijective_shiftBySection {d : ℕ} (s : powSections L d) [IsIso s] (m : ℕ) :
    Function.Bijective (fun t : twistSections F L m => shiftBySection s t) := by
  refine Function.bijective_iff_has_inverse.mpr
    ⟨fun w => (unitIsoEndo s).inv ≫ w ≫ (twistPowAddIso F L m d).hom ≫
        (twistIsoOfInvertible s (twistPow F L m)).hom,
      fun t => ?_, fun w => ?_⟩
  · simp [shiftBySection_eq_comp]
  · simp [shiftBySection_eq_comp]

end Trivialize

section Powers


/-- **The `k`-fold multiplication by `s`, starting from a twisted section of any degree.** This
is multiplication by `sᵏ`, which is `Stacks.TwistedSections.shiftIter_eq_actMap`. -/
def shiftIter {d : ℕ} (s : powSections L d) {m : ℕ} (t : twistSections F L m) :
    (k : ℕ) → twistSections F L (m + d * k)
  | 0 => t
  | k + 1 => twistCongr (Nat.add_assoc m (d * k) d) (shiftBySection s (shiftIter s t k))

/-- The `0`-fold multiplication by `s` is the identity. -/
@[simp] theorem shiftIter_zero {d : ℕ} (s : powSections L d) {m : ℕ}
    (t : twistSections F L m) : shiftIter s t 0 = t := rfl

/-- The `(k + 1)`-fold multiplication by `s` is multiplication by `s` after the `k`-fold one,
reindexed along `m + d * k + d = m + (d * k + d)`. -/
theorem shiftIter_succ {d : ℕ} (s : powSections L d) {m : ℕ} (t : twistSections F L m) (k : ℕ) :
    shiftIter s t (k + 1) =
      twistCongr (Nat.add_assoc m (d * k) d) (shiftBySection s (shiftIter s t k)) := rfl

/-- **The `k`-fold multiplication by `s`**, from twisted sections of degree zero — that is, from
global sections of `F` — to twisted sections of degree `d * k`. -/
def shiftPow {d : ℕ} (s : powSections L d) :
    (k : ℕ) → twistSections F L 0 → twistSections F L (d * k)
  | 0, u => u
  | k + 1, u => shiftBySection s (shiftPow s k u)

/-- The `0`-fold multiplication by `s` on global sections is the identity. -/
@[simp] theorem shiftPow_zero {d : ℕ} (s : powSections L d) (u : twistSections F L 0) :
    shiftPow s 0 u = u := rfl

/-- The `(k + 1)`-fold multiplication by `s` is multiplication by `s` after the `k`-fold one. -/
theorem shiftPow_succ {d : ℕ} (s : powSections L d) (k : ℕ) (u : twistSections F L 0) :
    shiftPow s (k + 1) u = shiftBySection s (shiftPow s k u) := rfl

/-- Reindexing the exponent commutes with the `k`-fold multiplication. -/
theorem twistCongr_shiftPow {d : ℕ} (s : powSections L d) {k k' : ℕ} (h : k = k')
    (u : twistSections F L 0) :
    twistCongr (congrArg (d * ·) h) (shiftPow s k u) = shiftPow s (F := F) k' u := by
  subst h; exact twistCongr_rfl _

/-- **The `k`-fold multiplication by `s` is bijective** when `s` is an isomorphism. -/
theorem bijective_shiftPow {d : ℕ} (s : powSections L d) [IsIso s] (k : ℕ) :
    Function.Bijective (shiftPow s (F := F) k) := by
  induction k with
  | zero => exact Function.bijective_id
  | succ k ih => exact (bijective_shiftBySection s (d * k)).comp ih

end Powers

section Additive

variable [Preadditive C] [(tensorRight L).Additive]


/-- Multiplication by `s` is additive. -/
theorem shiftBySection_add {d : ℕ} (s : powSections L d) {m : ℕ}
    (t t' : twistSections F L m) :
    shiftBySection s (t + t') = shiftBySection s t + shiftBySection s t' := by
  rw [shiftBySection_eq, shiftBySection_eq, shiftBySection_eq, actMap_add,
    Preadditive.comp_add]

/-- Multiplication by `s` sends the zero twisted section to zero. -/
theorem shiftBySection_zero_section {d : ℕ} (s : powSections L d) (m : ℕ) :
    shiftBySection s (0 : twistSections F L m) = 0 := by
  rw [shiftBySection_eq, actMap_zero_section, Limits.comp_zero]

/-- The `k`-fold multiplication by `s` is additive. -/
theorem shiftPow_add_section {d : ℕ} (s : powSections L d) (k : ℕ)
    (u u' : twistSections F L 0) :
    shiftPow s k (u + u') = shiftPow s (F := F) k u + shiftPow s k u' := by
  induction k with
  | zero => rfl
  | succ k ih => rw [shiftPow_succ, shiftPow_succ, shiftPow_succ, ih, shiftBySection_add]

/-- The `k`-fold multiplication by `s` sends the zero global section to zero. -/
theorem shiftPow_zero_section {d : ℕ} (s : powSections L d) (k : ℕ) :
    shiftPow s k (0 : twistSections F L 0) = (0 : twistSections F L (d * k)) := by
  induction k with
  | zero => rfl
  | succ k ih => rw [shiftPow_succ, ih, shiftBySection_zero_section]

/-- **The `k`-fold multiplication by `s`, as a morphism of additive groups.** -/
def shiftPowHom {d : ℕ} (s : powSections L d) (k : ℕ) :
    twistSections F L 0 →+ twistSections F L (d * k) where
  toFun := shiftPow s k
  map_zero' := shiftPow_zero_section s k
  map_add' := shiftPow_add_section s k

/-- `shiftPowHom s k` applied to `u` is `shiftPow s k u`. -/
@[simp] theorem shiftPowHom_apply {d : ℕ} (s : powSections L d) (k : ℕ)
    (u : twistSections F L 0) : shiftPowHom s k u = shiftPow s (F := F) k u := rfl

/-- **The `k`-fold multiplication by an invertible `s`, as an isomorphism of additive
groups.** -/
noncomputable def shiftPowEquiv {d : ℕ} (s : powSections L d) [IsIso s] (k : ℕ) :
    twistSections F L 0 ≃+ twistSections F L (d * k) :=
  AddEquiv.ofBijective (shiftPowHom s k) (bijective_shiftPow s k)

/-- `shiftPowEquiv s k` applied to `u` is `shiftPow s k u`. -/
@[simp] theorem shiftPowEquiv_apply {d : ℕ} (s : powSections L d) [IsIso s] (k : ℕ)
    (u : twistSections F L 0) : shiftPowEquiv s k u = shiftPow s (F := F) k u := rfl

/-- **Division by `sᵏ`**: the inverse of the `k`-fold multiplication by an invertible `s`, which
exists because that multiplication is bijective. -/
noncomputable def powerDivision {d : ℕ} (s : powSections L d) [IsIso s] (k : ℕ) :
    twistSections F L (d * k) →+ twistSections F L 0 :=
  (shiftPowEquiv s k).symm.toAddMonoidHom

/-- **The division of `t` by `sᵏ` is the unique twisted section of degree zero whose product with
`sᵏ` is `t`.** -/
@[simp] theorem shiftPow_powerDivision {d : ℕ} (s : powSections L d) [IsIso s] (k : ℕ)
    (t : twistSections F L (d * k)) : shiftPow s k (powerDivision s (F := F) k t) = t :=
  (shiftPowEquiv s k).apply_symm_apply t

/-- Dividing the product `sᵏ · u` by `sᵏ` recovers `u`. -/
theorem powerDivision_shiftPow {d : ℕ} (s : powSections L d) [IsIso s] (k : ℕ)
    (u : twistSections F L 0) : powerDivision s k (shiftPow s (F := F) k u) = u :=
  (shiftPowEquiv s k).symm_apply_apply u

/-! ### The powers of `s` in the section ring -/

/-- **`sᵏ · s = s ^ (k + 1)`.** Both sides are homogeneous of degree `d * (k + 1)`, so this is
the image under the injection of that degree of one application of `pow_succ`. -/
theorem mul_sectionPow_self {d : ℕ} (s : powSections L d) (k : ℕ) :
    mul (sectionPowOfDegree s k) s = sectionPowOfDegree s (k + 1) := by
  have h1 : DirectSum.of (powSections L) (d * k) (sectionPowOfDegree s k) *
      DirectSum.of (powSections L) d s =
      DirectSum.of (powSections L) (d * (k + 1)) (mul (sectionPowOfDegree s k) s) :=
    DirectSum.of_mul_of _ _
  have h2 : DirectSum.of (powSections L) (d * k) (sectionPowOfDegree s k) *
      DirectSum.of (powSections L) d s = homogeneousSectionOfDegree s ^ (k + 1) := by
    rw [of_sectionPowOfDegree]
    exact (pow_succ (homogeneousSectionOfDegree s) k).symm
  have h3 : DirectSum.of (powSections L) (d * (k + 1)) (sectionPowOfDegree s (k + 1)) =
      homogeneousSectionOfDegree s ^ (k + 1) := of_sectionPowOfDegree s (k + 1)
  have h : DirectSum.of (powSections L) (d * (k + 1)) (mul (sectionPowOfDegree s k) s) =
      DirectSum.of (powSections L) (d * (k + 1)) (sectionPowOfDegree s (k + 1)) :=
    h1.symm.trans (h2.trans h3.symm)
  simpa using congrArg (fun z : sectionRing L => z (d * (k + 1))) h

/-- `mul_sectionPow_self` with the product written out: `s ≫ mulMap sᵏ d = s ^ (k + 1)`. -/
theorem comp_mulMap_sectionPow {d : ℕ} (s : powSections L d) (k : ℕ) :
    s ≫ mulMap (sectionPowOfDegree s k) d = sectionPowOfDegree s (k + 1) := by
  rw [← mul_sectionPow_self s k, Stacks.GradedSections.mul_def]

/-- **Multiplication by an invertible section is invertible.** `Stacks.GradedSections.mulMap y j`
is `y` whiskered on the right by `j` copies of `L`, and whiskering preserves isomorphisms. -/
instance isIso_mulMap {i : ℕ} (y : powSections L i) [IsIso y] (j : ℕ) :
    IsIso (mulMap y j) := by
  induction j with
  | zero => exact ‹IsIso y›
  | succ j ih => exact (inferInstance : IsIso (mulMap y j ▷ L))

/-- **Every power of an invertible section is invertible.** By `mul_sectionPow_self` the power
`s ^ (k + 1)` is `s` followed by multiplication by `sᵏ`, and both factors are isomorphisms. -/
instance isIso_sectionPow {d : ℕ} (s : powSections L d) [IsIso s] (k : ℕ) :
    IsIso (sectionPowOfDegree s k) := by
  induction k with
  | zero => rw [sectionPowOfDegree_zero]; exact (inferInstance : IsIso (𝟙 (𝟙_ C)))
  | succ k ih => rw [← comp_mulMap_sectionPow]; infer_instance

/-- The zeroth power of a section is the identity of the monoidal unit, read as a morphism out
of `L ^⊗ (d * 0)`'s domain: composing it with anything out of `L ^⊗ (d * 0)` changes nothing. -/
theorem sectionPow_zero_comp {d : ℕ} (s : powSections L d) {Z : C}
    (f : natTensorPow L (d * 0) ⟶ Z) : sectionPowOfDegree s 0 ≫ f = f := by
  rw [sectionPowOfDegree_zero]
  exact Category.id_comp f

/-- **The `k`-fold multiplication by `s` is the action of `sᵏ`**, from a twisted section of any
degree. The degrees are `m + d * k` on both sides, with no reindexing. -/
theorem shiftIter_eq_actMap {d : ℕ} (s : powSections L d) {m : ℕ} (t : twistSections F L m)
    (k : ℕ) : shiftIter s t k = sectionPowOfDegree s k ≫ actMap t (d * k) := by
  induction k with
  | zero =>
      rw [shiftIter_zero, sectionPow_zero_comp]
      rfl
  | succ k ih =>
      rw [shiftIter_succ, shiftBySection_eq, ih, actMap_comp, ← Category.assoc,
        comp_mulMap_sectionPow, twistCongr, Category.assoc, Category.assoc, eqToHom_trans,
        eqToHom_refl, Category.comp_id]
      rfl

/-- **The iterated multiplication is the action of a power of `s`, as `gsmul` spells it.** The
reindexing is the `Nat.add_comm` inside `Stacks.TwistedSections.gsmul`. -/
theorem gsmul_sectionPow_eq_shiftIter {d : ℕ} (s : powSections L d) {m : ℕ}
    (t : twistSections F L m) (k : ℕ) :
    gsmul (sectionPowOfDegree s k) t = twistCongr (Nat.add_comm m (d * k)) (shiftIter s t k) := by
  rw [gsmul_def, shiftIter_eq_actMap]

/-- `shiftPow_add_eq_actMap` is `shiftIter_eq_actMap` at the degree-zero start. The reindexing is
the distributivity `d * n + d * k = d * (n + k)`, which is never definitional. -/
theorem shiftPow_add_eq_actMap {d : ℕ} (s : powSections L d) (u : twistSections F L 0)
    (n k : ℕ) :
    shiftPow s (n + k) u =
      twistCongr ((Nat.add_comm (d * n) (d * k)).trans (mul_add_degree d n k))
        (sectionPowOfDegree s k ≫ actMap (shiftPow s n u) (d * k)) := by
  induction k with
  | zero =>
      rw [sectionPow_zero_comp]
      exact (twistCongr_rfl _).symm
  | succ k ih =>
      change shiftBySection s (shiftPow s (n + k) u) = _
      rw [ih, shiftBySection_eq, actMap_twistCongr, ← Category.assoc, actMap_comp,
        ← Category.assoc, comp_mulMap_sectionPow]
      simp only [twistCongr, Category.assoc, eqToHom_trans]
      rfl

/-- **The divisions by the powers of an invertible `s` are power-invariant.** Dividing `t ⊗ sᵏ`
by `s ^ (n + k)` agrees with dividing `t` by `sⁿ` because the `(n + k)`-fold multiplication by
`s` *is* multiplication by `sᵏ` after the `n`-fold one. -/
theorem isPowerInvariant_powerDivision {d : ℕ} (s : powSections L d) [IsIso s] :
    IsPowerInvariantOfDegree s (powerDivision s (F := F)) := by
  intro n k t
  obtain ⟨u, rfl⟩ := (bijective_shiftPow s (F := F) n).surjective t
  rw [powerDivision_shiftPow, gsmul_def, twistCongr_trans, ← shiftPow_add_eq_actMap,
    powerDivision_shiftPow]

end Additive

section Lift

variable [Preadditive C] [(tensorRight L).Additive] [BraidedCategory C]
  [HasTrivialSelfBraiding L]


/-- **Stacks Tag 0B5L's comparison map at an invertible section**, with nothing left assumed:
the degree-zero localization `Γ_*(X, F, L)_{(s)}` maps to the global sections of `F`, by
restricting a numerator and dividing by the power of `s` in the denominator. -/
noncomputable def localizationLiftOfInvertible {d : ℕ} (s : powSections L d) [IsIso s] :
    sectionAtNonvanishingOpenOfDegree F L s →+ twistSections F L 0 :=
  localizationLiftOfDegree s (powerDivision s) (isPowerInvariant_powerDivision s)

/-- **The value of the comparison map on a fraction** `t / sⁿ` is the division of `t` by `sⁿ`,
that is the unique global section of `F` whose product with `sⁿ` is `t`. -/
theorem localizationLiftOfInvertible_mk {d : ℕ} (s : powSections L d) [IsIso s] (n : ℕ)
    (t : twistSections F L (d * n)) :
    localizationLiftOfInvertible s
        (⟨LocalizedModule.mk (DirectSum.of (twistSections F L) (d * n) t)
            (⟨homogeneousSectionOfDegree s ^ n, ⟨n, rfl⟩⟩ :
              Submonoid.powers (homogeneousSectionOfDegree s)),
          mk_mem_sectionAtNonvanishingOpenOfDegree s n t⟩ :
          sectionAtNonvanishingOpenOfDegree F L s) =
      powerDivision s n t :=
  localizationLiftOfDegree_mk s (powerDivision s) (isPowerInvariant_powerDivision s) n t

/-- **The comparison map inverts multiplication by `sⁿ`**: the fraction `sⁿ · u / sⁿ` goes to
`u`. -/
theorem localizationLiftOfInvertible_mk_shiftPow {d : ℕ} (s : powSections L d) [IsIso s] (n : ℕ)
    (u : twistSections F L 0) :
    localizationLiftOfInvertible s
        (⟨LocalizedModule.mk (DirectSum.of (twistSections F L) (d * n) (shiftPow s n u))
            (⟨homogeneousSectionOfDegree s ^ n, ⟨n, rfl⟩⟩ :
              Submonoid.powers (homogeneousSectionOfDegree s)),
          mk_mem_sectionAtNonvanishingOpenOfDegree s n (shiftPow s n u)⟩ :
          sectionAtNonvanishingOpenOfDegree F L s) = u := by
  rw [localizationLiftOfInvertible_mk, powerDivision_shiftPow]

end Lift

end Stacks.TwistedSections

end
