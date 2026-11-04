module

public import StacksFrontier.AlgebraicGeometry.Smooth.SmoothFormallySmoothTag
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Lifting along nilpotent thickenings of affine schemes

A smooth morphism of schemes `f : X ⟶ S` has the infinitesimal lifting property not only for
first-order thickenings of affine schemes, which is the definition of formal smoothness used in
`Stacks.Smooth.FormallySmoothScheme`, but for every closed immersion of affine schemes defined
by a nilpotent ideal: if `I ⊆ R` is an ideal with `I ^ (n + 1) = 0`, every commutative square

```
Spec (R ⧸ I) --g--> X
     |              |
     v              v f
  Spec R  ----h---> S
```

has a diagonal filler.

## Main results

* `Stacks.Smooth.exists_lift_of_ker_pow_eq_bot`: the lift along `Spec (R ⧸ I) ⟶ Spec R` for
  `I ^ (n + 1) = 0`.
* `Stacks.Smooth.exists_lift_of_isNilpotent`: the same for a nilpotent ideal.
* `Stacks.Smooth.exists_lift_of_surjective`: the same for a surjective ring map with nilpotent
  kernel.
* `Stacks.Smooth.exists_lift_of_isFiniteOrderThickening`: the same for a finite-order thickening
  of affine schemes.

## Implementation notes

The proof is by induction on `n`. With `J = I ^ (n + 1)` the closed immersion
`Spec (R ⧸ J) ⟶ Spec R` is a first-order thickening, because `J ^ 2 ⊆ I ^ (n + 2) = 0`, and
the image of `I` in `R ⧸ J` has vanishing `(n + 1)`st power; so the lift is first extended to
`Spec (R ⧸ J)` by induction, through the canonical identification of `(R ⧸ J) ⧸ I (R ⧸ J)` with
`R ⧸ I`, and then to `Spec R` by formal smoothness,
`Stacks.Smooth.formallySmoothScheme_of_smooth`.

## References

* [Stacks Project, Tag 02H6](https://stacks.math.columbia.edu/tag/02H6)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace Stacks.Smooth

/-- A lift along `Spec.map (π ≫ e.hom)` for an isomorphism `e` follows from lifts along
`Spec.map π`. -/
private theorem exists_lift_of_comp_iso {X S : Scheme.{u}} (f : X ⟶ S)
    {R A B : CommRingCat.{u}} (π : R ⟶ A) (e : A ≅ B) (g : Spec B ⟶ X) (h : Spec R ⟶ S)
    (hgh : g ≫ f = Spec.map (π ≫ e.hom) ≫ h)
    (H : ∀ g₁ : Spec A ⟶ X, g₁ ≫ f = Spec.map π ≫ h →
      ∃ g' : Spec R ⟶ X, g' ≫ f = h ∧ Spec.map π ≫ g' = g₁) :
    ∃ g' : Spec R ⟶ X, g' ≫ f = h ∧ Spec.map (π ≫ e.hom) ≫ g' = g := by
  obtain ⟨g', hg'f, hg'⟩ := H (Spec.map e.inv ≫ g) (by
    rw [Category.assoc, hgh, ← Category.assoc, ← Spec.map_comp, Category.assoc, e.hom_inv_id,
      Category.comp_id])
  refine ⟨g', hg'f, ?_⟩
  rw [Spec.map_comp, Category.assoc, hg', ← Category.assoc, ← Spec.map_comp, e.inv_hom_id,
    Spec.map_id, Category.id_comp]

/-- **Lifting along `Spec (R ⧸ I) ⟶ Spec R` for `I ^ (n + 1) = 0`.** A smooth morphism of
schemes has a diagonal filler for every commutative square whose left side is the closed
immersion defined by an ideal with vanishing `(n + 1)`st power. -/
theorem exists_lift_of_ker_pow_eq_bot {X S : Scheme.{u}} (f : X ⟶ S)
    [AlgebraicGeometry.Smooth f] (n : ℕ) : ∀ {R : CommRingCat.{u}} (I : Ideal R),
    I ^ (n + 1) = ⊥ → ∀ (g : Spec (.of (R ⧸ I)) ⟶ X) (h : Spec R ⟶ S),
      g ≫ f = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ h →
      ∃ g' : Spec R ⟶ X, g' ≫ f = h ∧
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ g' = g := by
  induction n with
  | zero =>
    intro R I hI g h hgh
    obtain rfl : I = ⊥ := by simpa using hI
    let e : R ≅ CommRingCat.of (R ⧸ (⊥ : Ideal R)) :=
      (RingEquiv.quotientBot R).symm.toCommRingCatIso
    have he : CommRingCat.ofHom (Ideal.Quotient.mk (⊥ : Ideal R)) = 𝟙 R ≫ e.hom := rfl
    rw [he] at hgh ⊢
    exact exists_lift_of_comp_iso f (𝟙 R) e g h hgh fun g₁ hg₁ => ⟨g₁, by simpa using hg₁, by simp⟩
  | succ n ih =>
    intro R I hI g h hgh
    let J : Ideal R := I ^ (n + 1)
    have hJ2 : J ^ 2 = ⊥ := by
      rw [← pow_mul, eq_bot_iff, ← hI]
      exact Ideal.pow_le_pow_right (by omega)
    let R₁ : CommRingCat.{u} := .of (R ⧸ J)
    let πJ : R ⟶ R₁ := CommRingCat.ofHom (Ideal.Quotient.mk J)
    let I₁ : Ideal R₁ := I.map (Ideal.Quotient.mk J)
    have hI₁ : I₁ ^ (n + 1) = ⊥ := by
      rw [← Ideal.map_pow]
      exact Ideal.map_quotient_self J
    let φ : R₁ ⧸ I₁ ≃+* R ⧸ I :=
      DoubleQuot.quotQuotEquivQuotOfLE (Ideal.pow_le_self n.succ_ne_zero)
    let e : CommRingCat.of (R₁ ⧸ I₁) ≅ CommRingCat.of (R ⧸ I) := φ.toCommRingCatIso
    have hcomp : CommRingCat.ofHom (Ideal.Quotient.mk I) =
        (πJ ≫ CommRingCat.ofHom (Ideal.Quotient.mk I₁)) ≫ e.hom := by
      ext x
      rfl
    have hfirst : Thickenings.IsFirstOrderThickening (Spec.map πJ) :=
      isFirstOrderThickening_specMap πJ Ideal.Quotient.mk_surjective (by
        change RingHom.ker (Ideal.Quotient.mk J) ^ 2 = ⊥
        rwa [Ideal.mk_ker])
    rw [hcomp] at hgh ⊢
    refine exists_lift_of_comp_iso f _ e g h hgh fun g₂ hg₂ => ?_
    rw [Spec.map_comp, Category.assoc] at hg₂
    obtain ⟨g₁, hg₁f, hg₁⟩ := ih I₁ hI₁ g₂ (Spec.map πJ ≫ h) hg₂
    obtain ⟨g', hg'f, hg'⟩ := formallySmoothScheme_of_smooth f inferInstance inferInstance
      (Spec.map πJ) hfirst g₁ h hg₁f
    exact ⟨g', hg'f, by rw [Spec.map_comp, Category.assoc, hg', hg₁]⟩

/-- **Lifting along a nilpotent closed immersion of affine schemes.** A smooth morphism of
schemes has a diagonal filler for every commutative square whose left side is
`Spec (R ⧸ I) ⟶ Spec R` for a nilpotent ideal `I`. -/
theorem exists_lift_of_isNilpotent {X S : Scheme.{u}} (f : X ⟶ S)
    [AlgebraicGeometry.Smooth f] {R : CommRingCat.{u}} (I : Ideal R) (hI : IsNilpotent I)
    (g : Spec (.of (R ⧸ I)) ⟶ X) (h : Spec R ⟶ S)
    (hgh : g ≫ f = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ h) :
    ∃ g' : Spec R ⟶ X, g' ≫ f = h ∧
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ g' = g := by
  obtain ⟨n, hn⟩ := hI
  exact exists_lift_of_ker_pow_eq_bot f n I
    (eq_bot_iff.2 ((Ideal.pow_le_pow_right n.le_succ).trans hn.le)) g h hgh

/-- **Lifting along a surjection of rings with nilpotent kernel.** A smooth morphism of schemes
has a diagonal filler for every commutative square whose left side is `Spec A ⟶ Spec R` for a
surjective ring map `R ⟶ A` with nilpotent kernel. -/
theorem exists_lift_of_surjective {X S : Scheme.{u}} (f : X ⟶ S)
    [AlgebraicGeometry.Smooth f] {R A : CommRingCat.{u}} (φ : R ⟶ A)
    (hφ : Function.Surjective φ.hom) (hker : IsNilpotent (RingHom.ker φ.hom))
    (g : Spec A ⟶ X) (h : Spec R ⟶ S) (hgh : g ≫ f = Spec.map φ ≫ h) :
    ∃ g' : Spec R ⟶ X, g' ≫ f = h ∧ Spec.map φ ≫ g' = g := by
  let I : Ideal R := RingHom.ker φ.hom
  let e : CommRingCat.of (R ⧸ I) ≅ A :=
    (RingHom.quotientKerEquivOfSurjective hφ).toCommRingCatIso
  have he : φ = CommRingCat.ofHom (Ideal.Quotient.mk I) ≫ e.hom := by
    ext x
    rfl
  rw [he] at hgh ⊢
  exact exists_lift_of_comp_iso f _ e g h hgh fun g₁ hg₁ =>
    exists_lift_of_isNilpotent f I hker g₁ h hg₁

/-- **Lifting along a finite-order thickening of affine schemes.** A smooth morphism of schemes
`f : X ⟶ S` has a diagonal filler for every commutative square whose left side is a
finite-order thickening `i : T ⟶ T'` of affine schemes, i.e. a closed immersion with nilpotent
ideal sheaf. -/
@[sga "3 III 2.5" "(a)", sga "3 IX 3.3" "more general"]
theorem exists_lift_of_isFiniteOrderThickening {X S T T' : Scheme.{u}} (f : X ⟶ S)
    [AlgebraicGeometry.Smooth f] [IsAffine T] [IsAffine T'] (i : T ⟶ T')
    (hi : Thickenings.IsFiniteOrderThickening i) (g : T ⟶ X) (h : T' ⟶ S)
    (hgh : g ≫ f = i ≫ h) :
    ∃ g' : T' ⟶ X, g' ≫ f = h ∧ i ≫ g' = g := by
  have := hi.1
  obtain ⟨n, hn⟩ := hi.2
  obtain ⟨g₀, hg₀f, hg₀⟩ := exists_lift_of_surjective f i.appTop
    (IsClosedImmersion.isAffine_surjective_of_isAffine i).2
    ⟨n + 1, (ker_pow_eq_bot_iff_of_isAffine i (n + 1)).1 hn⟩
    (T.isoSpec.inv ≫ g) (T'.isoSpec.inv ≫ h) (by
      rw [Category.assoc, hgh, Scheme.isoSpec_inv_naturality_assoc])
  refine ⟨T'.isoSpec.hom ≫ g₀, ?_, ?_⟩
  · rw [Category.assoc, hg₀f, Iso.hom_inv_id_assoc]
  · rw [← Scheme.isoSpec_hom_naturality_assoc, hg₀, Iso.hom_inv_id_assoc]

end Stacks.Smooth

end
