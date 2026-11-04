module

public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteLocallyFree.RankCancel
public import StacksFrontier.AlgebraicGeometry.Picard.HilbertAbelMap
public import StacksFrontier.AlgebraicGeometry.Picard.HilbertFunctorSeparated
public import StacksFrontier.AlgebraicGeometry.Picard.HilbertSymmetricPower

/-!
# Addition of divisors on the Hilbert schemes of points of a smooth relative curve

Let `X ⟶ S` be smooth of relative dimension one and let `H^d` represent the degree-`d` Hilbert
functor of `X`. Sending a pair of families `(D₁, D₂)` to their sum `D₁ + D₂` (Tag 0B9E) is a
transformation `Hilb^{d₁} × Hilb^{d₂} ⟶ Hilb^{d₁ + d₂}`, hence a morphism

  `H^{d₁} ×_S H^{d₂} ⟶ H^{d₁ + d₂}`,   `(D₁, D₂) ↦ D₁ + D₂`.

When `X ⟶ S` is separated and all the Hilbert functors are representable, this morphism is finite
locally free of degree `(d₁ + d₂).choose d₁`: precomposed with `π_{d₁} × π_{d₂}`, where
`π_d : X^d ⟶ H^d` is `(x₁, …, x_d) ↦ x₁ + ⋯ + x_d` (finite locally free of degree `d!`), it
becomes `π_{d₁ + d₂}` up to the identification `X^{d₁} ×_S X^{d₂} = X^{d₁ + d₂}`, and degrees
multiply. This is the proof of Stacks Tag 0B9I (3), which holds over any such base.

## Main definitions

* `Stacks.Scheme.fibrePowerAddIso` — `X^m ×_S X^n ≅ X^{m + n}`.
* `Stacks.Hilbert.addDivisors` — the morphism `H^{d₁} ×_S H^{d₂} ⟶ H^{d₁ + d₂}`.

## Main results

* `Stacks.Hilbert.family_comp_addDivisors` — `addDivisors` classifies the sum of the two
  families.
* `Stacks.Hilbert.isFiniteLocallyFreeOfRank_addDivisors` — `addDivisors` is finite locally free
  of degree `(d₁ + d₂).choose d₁`.

## References

* [Stacks Project, Tag 0B9I](https://stacks.math.columbia.edu/tag/0B9I)
* [Stacks Project, Tag 0B9E](https://stacks.math.columbia.edu/tag/0B9E)
* [Stacks Project, Tag 0B9G](https://stacks.math.columbia.edu/tag/0B9G)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Nat

universe u

namespace Stacks.Scheme

variable {S : Scheme.{u}} (X : Over S)

/-- **`X^m ×_S X^n ≅ X^{m + n}`**: the first `m` coordinates come from the first factor and the
last `n` from the second. -/
def fibrePowerAddIso (m n : ℕ) :
    (∏ᶜ fun _ : Fin m => X) ⨯ (∏ᶜ fun _ : Fin n => X) ≅ ∏ᶜ fun _ : Fin (m + n) => X where
  hom := Pi.lift fun i => Fin.addCases
    (motive := fun _ => ((∏ᶜ fun _ : Fin m => X) ⨯ (∏ᶜ fun _ : Fin n => X)) ⟶ X)
    (fun a => prod.fst ≫ Pi.π _ a) (fun b => prod.snd ≫ Pi.π _ b) i
  inv := prod.lift (Pi.lift fun a => Pi.π (fun _ : Fin (m + n) => X) (Fin.castAdd n a))
    (Pi.lift fun b => Pi.π (fun _ : Fin (m + n) => X) (Fin.natAdd m b))
  hom_inv_id := by
    apply prod.hom_ext <;> apply Pi.hom_ext <;> intro a <;> simp
  inv_hom_id := by
    apply Pi.hom_ext
    intro i
    refine Fin.addCases (fun a => ?_) (fun b => ?_) i <;> simp

/-- The `Fin.castAdd n a`-th coordinate of `fibrePowerAddIso` is the `a`-th coordinate of the
first factor. -/
@[reassoc (attr := simp)]
theorem fibrePowerAddIso_hom_π_castAdd (m n : ℕ) (a : Fin m) :
    (fibrePowerAddIso X m n).hom ≫ Pi.π (fun _ : Fin (m + n) => X) (Fin.castAdd n a) =
      prod.fst ≫ Pi.π _ a := by
  simp [fibrePowerAddIso]

/-- The `Fin.natAdd m b`-th coordinate of `fibrePowerAddIso` is the `b`-th coordinate of the
second factor. -/
@[reassoc (attr := simp)]
theorem fibrePowerAddIso_hom_π_natAdd (m n : ℕ) (b : Fin n) :
    (fibrePowerAddIso X m n).hom ≫ Pi.π (fun _ : Fin (m + n) => X) (Fin.natAdd m b) =
      prod.snd ≫ Pi.π _ b := by
  simp [fibrePowerAddIso]

/-- `id × f : X ×_S A ⟶ X ×_S B` is the base change of `f : A ⟶ B` along the second projection,
on underlying schemes. -/
theorem isPullback_prod_snd_prodMap_right {A B : Over S} (f : A ⟶ B) :
    IsPullback (prod.snd : X ⨯ A ⟶ A).left (prod.map (𝟙 X) f).left f.left
      (prod.snd : X ⨯ B ⟶ B).left := by
  have h : IsPullback (prod.map (𝟙 X) f) (prod.snd : X ⨯ A ⟶ A) prod.snd f :=
    IsPullback.of_iso_pullback ⟨by simp⟩ (pullbackProdSndIsoProd f X).symm
      (by rw [pullbackProdSndIsoProd, Iso.symm_hom, pullback.lift_fst])
      (by rw [pullbackProdSndIsoProd, Iso.symm_hom, pullback.lift_snd])
  exact h.flip.map (Over.forget S)

end Stacks.Scheme

namespace Stacks.Hilbert

open Stacks.Scheme

variable {S : Scheme.{u}} {X : Over S} [SmoothOfRelativeDimension 1 X.hom] {d₁ d₂ : ℕ}
  {H₁ H₂ H : Over S}

/-- **The addition morphism `H^{d₁} ×_S H^{d₂} ⟶ H^{d₁ + d₂}`, `(D₁, D₂) ↦ D₁ + D₂`.** For schemes
`H₁`, `H₂`, `H` representing the Hilbert functors of `X` of degrees `d₁`, `d₂` and `d₁ + d₂`,
the morphism classifying the sum (Tag 0B9E) of the pullbacks of the two universal families. Its
characterization is `Stacks.Hilbert.family_comp_addDivisors`. -/
def addDivisors (h₁ : RepresentsHilbertFunctorOfRank X H₁ d₁)
    (h₂ : RepresentsHilbertFunctorOfRank X H₂ d₂)
    (h : RepresentsHilbertFunctorOfRank X H (d₁ + d₂)) : H₁ ⨯ H₂ ⟶ H :=
  h.family.symm ((h₁.family prod.fst).add (h₂.family prod.snd))

variable (h₁ : RepresentsHilbertFunctorOfRank X H₁ d₁)
  (h₂ : RepresentsHilbertFunctorOfRank X H₂ d₂)
  (h : RepresentsHilbertFunctorOfRank X H (d₁ + d₂))

/-- The ideal of the family classified by `g ≫ addDivisors`, for `g = (D₁, D₂) : T ⟶ H₁ ×_S H₂`,
is the product of the ideals of `D₁` and `D₂`. -/
theorem family_comp_addDivisors_ideal {T : Over S} (g : T ⟶ H₁ ⨯ H₂) :
    (h.family (g ≫ addDivisors h₁ h₂ h)).ideal =
      (h₁.family (g ≫ prod.fst)).ideal * (h₂.family (g ≫ prod.snd)).ideal := by
  rw [h.naturality, addDivisors, Equiv.apply_symm_apply, HilbertFamily.add_ideal,
    AlgebraicGeometry.comap_mul, ← h₁.naturality, ← h₂.naturality]

/-- **The characterization of the addition morphism.** For `g = (D₁, D₂) : T ⟶ H₁ ×_S H₂`, the
morphism `g ≫ addDivisors` classifies the family `D₁ + D₂`. -/
theorem family_comp_addDivisors {T : Over S} (g : T ⟶ H₁ ⨯ H₂) :
    h.family (g ≫ addDivisors h₁ h₂ h) =
      (h₁.family (g ≫ prod.fst)).add (h₂.family (g ≫ prod.snd)) :=
  HilbertFamily.ext (family_comp_addDivisors_ideal h₁ h₂ h g)

variable [IsSeparated X.hom]

/-- A comparison morphism between two representing schemes is an isomorphism of schemes. -/
instance isIso_compare_left {d : ℕ} {H' : Over S} (h : RepresentsHilbertFunctorOfRank X H d)
    (h' : RepresentsHilbertFunctorOfRank X H' d) : IsIso (h.compare h').left :=
  inferInstanceAs (IsIso ((Over.forget S).mapIso (h.isoOver h')).hom)

/-- Degrees of finite locally free morphisms multiply under composition in `Over S`. -/
private theorem isFiniteLocallyFreeOfRank_comp_left {A B C : Over S} (f : A ⟶ B) (g : B ⟶ C)
    {m n : ℕ} [Morphisms.IsFiniteLocallyFreeOfRank f.left m]
    [Morphisms.IsFiniteLocallyFreeOfRank g.left n] :
    Morphisms.IsFiniteLocallyFreeOfRank (f ≫ g).left (m * n) :=
  Morphisms.IsFiniteLocallyFreeOfRank.comp _ _ _ _

/-- `π_d : X^d ⟶ H^d`, `(x₁, …, x_d) ↦ x₁ + ⋯ + x_d`, followed by the comparison with another
representing scheme, is finite locally free of degree `d!`. -/
theorem isFiniteLocallyFreeOfRank_symmetricPowerMap_comp_compare {Hs : ℕ → Over S}
    (hH : ∀ d, RepresentsHilbertFunctorOfRank X (Hs d) d) {d : ℕ} {H' : Over S}
    (h' : RepresentsHilbertFunctorOfRank X H' d) :
    Morphisms.IsFiniteLocallyFreeOfRank
      (symmetricPowerMap hH d ≫ (hH d).compare h').left d ! := by
  have := Morphisms.isFiniteLocallyFreeOfRank_one_of_isIso ((hH d).compare h').left
  rw [← mul_one d !]
  exact isFiniteLocallyFreeOfRank_comp_left _ _

/-- A scheme representing a Hilbert functor of a separated smooth relative curve all of whose
Hilbert functors are representable is locally of finite type over the base (it is smooth, Tag
0B9H). -/
theorem locallyOfFiniteType_hom_of_represents {Hs : ℕ → Over S}
    (hH : ∀ d, RepresentsHilbertFunctorOfRank X (Hs d) d) {d : ℕ} {H' : Over S}
    (h' : RepresentsHilbertFunctorOfRank X H' d) : LocallyOfFiniteType H'.hom := by
  have := smoothOfRelativeDimension_of_represents Hs hH d
  have : Smooth (Hs d).hom := SmoothOfRelativeDimension.smooth d _
  rw [← Over.w (h'.isoOver (hH d)).hom]
  infer_instance

/-- **The addition morphism and the symmetric power maps.** Up to the identification
`X^{d₁} ×_S X^{d₂} = X^{d₁ + d₂}`, the composite of `π_{d₁} × π_{d₂}` with the addition morphism
is `π_{d₁ + d₂}`: both send `(x₁, …, x_{d₁ + d₂})` to `x₁ + ⋯ + x_{d₁ + d₂}`. -/
theorem prodMap_comp_addDivisors {Hs : ℕ → Over S}
    (hH : ∀ d, RepresentsHilbertFunctorOfRank X (Hs d) d) :
    prod.map (symmetricPowerMap hH d₁ ≫ (hH d₁).compare h₁)
        (symmetricPowerMap hH d₂ ≫ (hH d₂).compare h₂) ≫ addDivisors h₁ h₂ h =
      (fibrePowerAddIso X d₁ d₂).hom ≫ symmetricPowerMap hH (d₁ + d₂) ≫
        (hH (d₁ + d₂)).compare h := by
  refine h.family.injective (HilbertFamily.ext ?_)
  rw [family_comp_addDivisors_ideal, prod.map_fst, prod.map_snd, ← Category.assoc,
    ← Category.assoc, ← Category.assoc, RepresentsHilbertFunctorOfRank.family_comp_compare,
    RepresentsHilbertFunctorOfRank.family_comp_compare,
    RepresentsHilbertFunctorOfRank.family_comp_compare, family_comp_symmetricPowerMap_ideal,
    family_comp_symmetricPowerMap_ideal, family_comp_symmetricPowerMap_ideal, Fin.prod_univ_add]
  simp only [fibrePowerAddIso_hom_π_castAdd, fibrePowerAddIso_hom_π_natAdd]

/-- **Stacks Project, Tag 0B9I (3), over a general base.** Let `X ⟶ S` be separated and smooth
of relative dimension one, with all its Hilbert functors representable (by the `Hs d`), and let
`H₁`, `H₂`, `H` represent those of degrees `d₁`, `d₂` and `d₁ + d₂`. The addition morphism
`H₁ ×_S H₂ ⟶ H`, `(D₁, D₂) ↦ D₁ + D₂`, is finite locally free of degree `(d₁ + d₂).choose d₁`.

Precomposed with `π_{d₁} × π_{d₂}`, of degree `d₁! * d₂!`, it is `π_{d₁ + d₂}` up to an
isomorphism (`Stacks.Hilbert.prodMap_comp_addDivisors`), of degree `(d₁ + d₂)!`; the degree of the
addition morphism follows by `Stacks.Morphisms.IsFiniteLocallyFreeOfRank.of_comp`. -/
theorem isFiniteLocallyFreeOfRank_addDivisors {Hs : ℕ → Over S}
    (hH : ∀ d, RepresentsHilbertFunctorOfRank X (Hs d) d) :
    Morphisms.IsFiniteLocallyFreeOfRank (addDivisors h₁ h₂ h).left ((d₁ + d₂).choose d₁) := by
  set p₁ := symmetricPowerMap hH d₁ ≫ (hH d₁).compare h₁
  set p₂ := symmetricPowerMap hH d₂ ≫ (hH d₂).compare h₂
  have := isFiniteLocallyFreeOfRank_symmetricPowerMap_comp_compare hH h₁
  have := isFiniteLocallyFreeOfRank_symmetricPowerMap_comp_compare hH h₂
  -- `π_{d₁} × π_{d₂}` has degree `d₁! * d₂!`
  have : Morphisms.IsFiniteLocallyFreeOfRank
      (prod.map p₁ (𝟙 (∏ᶜ fun _ : Fin d₂ => X))).left d₁ ! :=
    Morphisms.IsFiniteLocallyFreeOfRank.of_isPullback
      (isPullback_prod_fst_prodMap_left (∏ᶜ fun _ : Fin d₂ => X) p₁)
  have : Morphisms.IsFiniteLocallyFreeOfRank (prod.map (𝟙 H₁) p₂).left d₂ ! :=
    Morphisms.IsFiniteLocallyFreeOfRank.of_isPullback (isPullback_prod_snd_prodMap_right H₁ p₂)
  have hπ : Morphisms.IsFiniteLocallyFreeOfRank (prod.map p₁ p₂).left (d₁ ! * d₂ !) := by
    have e : prod.map p₁ p₂ = prod.map p₁ (𝟙 _) ≫ prod.map (𝟙 _) p₂ := by simp
    exact e ▸ isFiniteLocallyFreeOfRank_comp_left _ _
  -- the composite is `π_{d₁ + d₂}` up to isomorphism, of degree `(d₁ + d₂)!`
  have : Morphisms.IsFiniteLocallyFreeOfRank
      ((prod.map p₁ p₂).left ≫ (addDivisors h₁ h₂ h).left) (d₁ ! * d₂ ! * (d₁ + d₂).choose d₁) := by
    rw [← Over.comp_left, prodMap_comp_addDivisors, Over.comp_left,
      show d₁ ! * d₂ ! * (d₁ + d₂).choose d₁ = (d₁ + d₂)! by
        rw [← Nat.choose_mul_factorial_mul_factorial (Nat.le_add_right d₁ d₂),
          Nat.add_sub_cancel_left]
        ring]
    exact Morphisms.isFiniteLocallyFreeOfRank_precomp ((Over.forget S).mapIso
      (fibrePowerAddIso X d₁ d₂)) _
      (isFiniteLocallyFreeOfRank_symmetricPowerMap_comp_compare hH h)
  -- the addition morphism is separated and locally of finite type
  have : IsSeparated H.hom := isSeparated_of_representsHilbertFunctorOfRank X H _ h
  have := isSeparated_of_representsHilbertFunctorOfRank X H₁ _ h₁
  have := isSeparated_of_representsHilbertFunctorOfRank X H₂ _ h₂
  have := locallyOfFiniteType_hom_of_represents hH h₁
  have := locallyOfFiniteType_hom_of_represents hH h₂
  have : IsSeparated ((addDivisors h₁ h₂ h).left ≫ H.hom) := by
    rw [Over.w, prod_hom_eq]
    infer_instance
  have : LocallyOfFiniteType ((addDivisors h₁ h₂ h).left ≫ H.hom) := by
    rw [Over.w, prod_hom_eq]
    infer_instance
  have : IsSeparated (addDivisors h₁ h₂ h).left := IsSeparated.of_comp _ H.hom
  have : LocallyOfFiniteType (addDivisors h₁ h₂ h).left := locallyOfFiniteType_of_comp _ H.hom
  exact Morphisms.IsFiniteLocallyFreeOfRank.of_comp (prod.map p₁ p₂).left
    (addDivisors h₁ h₂ h).left (r := d₁ ! * d₂ !) (Nat.mul_ne_zero (Nat.factorial_ne_zero _)
      (Nat.factorial_ne_zero _))

end Stacks.Hilbert

end
