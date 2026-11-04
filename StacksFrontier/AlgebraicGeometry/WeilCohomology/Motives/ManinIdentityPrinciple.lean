module

public import Mathlib.CategoryTheory.HomCongr
public import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
public import Mathlib.CategoryTheory.Retract
public import StacksCore.Tactic.StacksAttribute

/-!
# Manin's identity principle for motives

Let `k` be a base field and let `c : M → N` be a morphism in the category `M_k` of motives. If
for every smooth projective scheme `X` over `k` the morphism `c ⊗ 1 : M ⊗ h(X) → N ⊗ h(X)`
induces an isomorphism on Chow groups in every degree, then `c` is an isomorphism.

## Main definitions

* `Stacks.WeilCohomology.ChowRepresentability`: the Chow groups of motives together with the
  Tate twists `1(m)` of the unit motive, the invertibility of those twists, and the
  representability `CH^i(-) = Hom(1(-i), -)`.
* `Stacks.WeilCohomology.homFromUnitEquiv`: the duality bijection `Hom(X, A) = Hom(1, A ⊗ Y)`,
  for `Y` a left dual of `X`.

## Main results

* `Stacks.WeilCohomology.bijective_comp_whiskerRight_of_retract`: if `L` is a direct summand of
  `L'` and `- ≫ (c ⊗ 1_{L'})` is bijective on morphisms out of the unit, then so is
  `- ≫ (c ⊗ 1_L)`.
* `Stacks.WeilCohomology.bijective_comp_whiskerRight_twist`: the degree shift — the Chow groups
  of `M ⊗ h(X)(m)` are those of `M ⊗ h(X)` shifted by `m`.
* `Stacks.WeilCohomology.isIso_of_bijective_chowMap_tensorUnitHom`: Manin's identity principle.

## Implementation notes

The statement is made in an arbitrary monoidal category `Mot`, read as `M_k`, with a family
`h : D → Mot` of the motives of the smooth projective schemes over `k`, untwisted; the twists
`1(m)` are `Stacks.WeilCohomology.ChowRepresentability.unitTwist`. The theorem takes as
hypotheses:

* the representability of the Chow groups: `CH^i(A) = Hom(1(-i), A)` functorially in `A`, the
  fields `chowEquiv` and `chowEquiv_naturality` of `Stacks.WeilCohomology.ChowRepresentability`;
* the invertibility of the Tate motive: `1(m)` is a left dual of `1(-m)`, the field
  `tateExactPairing`;
* that every object of `M_k` has a left dual — in Mathlib's naming, a right dual,
  `CategoryTheory.HasRightDual`;
* that every object of `M_k` is a direct summand of some twist `h(X)(m)`, in the sense of
  `CategoryTheory.Retract`.

The map on Chow groups induced by a morphism of motives is `ℚ`-linear, so it is an isomorphism
exactly when it is bijective, and the hypothesis is stated as bijectivity in every degree
`i ∈ ℤ`.

## References

* [Stacks Project, Tag 0FGN](https://stacks.math.columbia.edu/tag/0FGN)
* [Stacks Project, Tag 0FGM](https://stacks.math.columbia.edu/tag/0FGM)
* [Stacks Project, Tag 0FFQ](https://stacks.math.columbia.edu/tag/0FFQ)
* [Stacks Project, Tag 0FGJ](https://stacks.math.columbia.edu/tag/0FGJ)
-/

@[expose] public section

open CategoryTheory MonoidalCategory

universe w v u

namespace Stacks.WeilCohomology

/-! ### Transfer of bijectivity along a commuting square of equivalences -/

/-- A map conjugate to a bijective map by two equivalences is bijective. -/
theorem bijective_of_equiv_square {α α' β β' : Type*} (eα : α ≃ α') (eβ : β ≃ β')
    {f : α → β} {f' : α' → β'} (hsq : ∀ x, f' (eα x) = eβ (f x))
    (hf : Function.Bijective f) : Function.Bijective f' := by
  have hcomp : f' = eβ ∘ f ∘ eα.symm := funext fun y ↦ by
    simpa only [Function.comp_apply, Equiv.apply_symm_apply] using hsq (eα.symm y)
  rw [hcomp]
  exact eβ.bijective.comp (hf.comp eα.symm.bijective)

/-! ### The duality bijection out of the unit object -/

variable {Mot : Type u} [Category.{v} Mot] [MonoidalCategory Mot]

/-- If `Y` is a left dual of `X` then `Hom(X, A) = Hom(1, A ⊗ Y)`, functorially in `A`: the
bijection `tensorRightHomEquiv` at the unit object, composed with the left unitor. -/
def homFromUnitEquiv (X Y : Mot) [ExactPairing X Y] (A : Mot) :
    (X ⟶ A) ≃ (𝟙_ Mot ⟶ A ⊗ Y) where
  toFun f := tensorRightHomEquiv (𝟙_ Mot) X Y A ((λ_ X).hom ≫ f)
  invFun g := (λ_ X).inv ≫ (tensorRightHomEquiv (𝟙_ Mot) X Y A).symm g
  left_inv f := by simp
  right_inv g := by simp

/-- The bijection `homFromUnitEquiv X Y A` sends `f : X ⟶ A` to the morphism corresponding to
`(λ_ X).hom ≫ f` under `tensorRightHomEquiv`. -/
theorem homFromUnitEquiv_apply (X Y : Mot) [ExactPairing X Y] {A : Mot} (f : X ⟶ A) :
    homFromUnitEquiv X Y A f = tensorRightHomEquiv (𝟙_ Mot) X Y A ((λ_ X).hom ≫ f) :=
  rfl

/-- The bijection `Hom(X, A) = Hom(1, A ⊗ Y)` is natural in `A`. -/
theorem homFromUnitEquiv_comp (X Y : Mot) [ExactPairing X Y] {A B : Mot} (f : X ⟶ A)
    (u : A ⟶ B) :
    homFromUnitEquiv X Y B (f ≫ u) = homFromUnitEquiv X Y A f ≫ u ▷ Y := by
  rw [homFromUnitEquiv_apply, homFromUnitEquiv_apply, ← Category.assoc,
    tensorRightHomEquiv_naturality]

/-! ### Passing to a direct summand -/

/-- If `L` is a direct summand of `L'` and tensoring `c` with `L'` induces a bijection on
morphisms out of the unit object, then so does tensoring `c` with `L`. -/
theorem bijective_comp_whiskerRight_of_retract {M N : Mot} (c : M ⟶ N) {L L' : Mot}
    (ρ : Retract L L')
    (h : Function.Bijective fun x : 𝟙_ Mot ⟶ M ⊗ L' => x ≫ c ▷ L') :
    Function.Bijective fun x : 𝟙_ Mot ⟶ M ⊗ L => x ≫ c ▷ L := by
  have hret (P : Mot) : P ◁ ρ.i ≫ P ◁ ρ.r = 𝟙 (P ⊗ L) := by
    rw [← MonoidalCategory.whiskerLeft_comp, ρ.retract, MonoidalCategory.whiskerLeft_id]
  have sq {A B : Mot} (f : A ⟶ B) (x : 𝟙_ Mot ⟶ M ⊗ A) :
      (x ≫ M ◁ f) ≫ c ▷ B = (x ≫ c ▷ A) ≫ N ◁ f := by
    rw [Category.assoc, whisker_exchange, Category.assoc]
  refine ⟨fun x y hxy => ?_, fun y => ?_⟩
  · have h₂ : x ≫ M ◁ ρ.i = y ≫ M ◁ ρ.i := h.injective <| by
      rw [sq, sq, show x ≫ c ▷ L = y ≫ c ▷ L from hxy]
    calc x = (x ≫ M ◁ ρ.i) ≫ M ◁ ρ.r := by rw [Category.assoc, hret, Category.comp_id]
      _ = y := by rw [h₂, Category.assoc, hret, Category.comp_id]
  · obtain ⟨z, hz⟩ := h.surjective (y ≫ N ◁ ρ.i)
    refine ⟨z ≫ M ◁ ρ.r, ?_⟩
    show (z ≫ M ◁ ρ.r) ≫ c ▷ L = y
    rw [sq, show z ≫ c ▷ L' = y ≫ N ◁ ρ.i from hz, Category.assoc, hret, Category.comp_id]

/-! ### The degree shift of a Tate twist -/

/-- Twisting shifts degrees: if `T` is a left dual of `T'` and tensoring `c` with `A` induces a
bijection on morphisms out of `T'`, then tensoring `c` with `A ⊗ T` induces a bijection on
morphisms out of the unit object. -/
theorem bijective_comp_whiskerRight_twist {M N : Mot} (c : M ⟶ N) (A T T' : Mot)
    [ExactPairing T' T]
    (hA : Function.Bijective fun x : T' ⟶ M ⊗ A => x ≫ c ▷ A) :
    Function.Bijective fun x : 𝟙_ Mot ⟶ M ⊗ (A ⊗ T) => x ≫ c ▷ (A ⊗ T) := by
  have h1 : Function.Bijective fun x : 𝟙_ Mot ⟶ (M ⊗ A) ⊗ T => x ≫ c ▷ A ▷ T :=
    bijective_of_equiv_square (homFromUnitEquiv T' T (M ⊗ A)) (homFromUnitEquiv T' T (N ⊗ A))
      (fun x => (homFromUnitEquiv_comp T' T x (c ▷ A)).symm) hA
  refine bijective_of_equiv_square ((Iso.refl (𝟙_ Mot)).homCongr (α_ M A T))
    ((Iso.refl (𝟙_ Mot)).homCongr (α_ N A T)) (fun x => ?_) h1
  simp only [Iso.homCongr_apply, Iso.refl_inv, Category.id_comp, Category.assoc]
  rw [associator_naturality_left]

/-! ### Manin's identity principle -/

/-- The Chow groups of motives, together with the Tate twists of the unit motive and the
representability of the Chow groups.

`unitTwist m` is the Tate twist `1(m)` of the unit motive and `tateExactPairing` says that
`1(m)` is a left dual of `1(-m)`, i.e. that the Tate motive is invertible. `chowGroup i A` is the
`i`-th Chow group `CH^i(A)` of a motive `A` and `chowMap i f` is the map it induces, both carried
as data. The last two fields say that the functor `CH^i(-)` is representable by `1(-i)`, that is,
`CH^i(A) = Hom(1(-i), A)` functorially in `A`. -/
structure ChowRepresentability (Mot : Type u) [Category.{v} Mot] [MonoidalCategory Mot] where
  /-- The Tate twist `1(m)` of the unit motive. -/
  unitTwist : ℤ → Mot
  /-- The Tate motive is invertible: `1(m)` is a left dual of `1(-m)`. -/
  tateExactPairing (m : ℤ) : ExactPairing (unitTwist (-m)) (unitTwist m)
  /-- The `i`-th Chow group `CH^i(A)` of a motive `A`. -/
  chowGroup : ℤ → Mot → Type v
  /-- The map `CH^i(A) → CH^i(B)` induced by a morphism of motives `A ⟶ B`. -/
  chowMap {A B : Mot} (i : ℤ) (f : A ⟶ B) : chowGroup i A → chowGroup i B
  /-- The functor `CH^i(-)` is representable by `1(-i)`. -/
  chowEquiv (i : ℤ) (A : Mot) : chowGroup i A ≃ (unitTwist (-i) ⟶ A)
  /-- The identification `CH^i(A) = Hom(1(-i), A)` is functorial in `A`. -/
  chowEquiv_naturality (i : ℤ) {A B : Mot} (f : A ⟶ B) (x : chowGroup i A) :
    chowEquiv i B (chowMap i f x) = chowEquiv i A x ≫ f

/-- **Manin's identity principle.** Let `c : M ⟶ N` be a morphism of motives. If for every
smooth projective scheme `X` over `k` the morphism `c ⊗ 1 : M ⊗ h(X) ⟶ N ⊗ h(X)` induces an
isomorphism on the Chow group `CH^i` in every degree `i ∈ ℤ`, then `c` is an isomorphism.

Here `Mot` stands for the monoidal category `M_k` of motives, `h X` is the motive of a smooth
projective scheme `X` over `k`, and `R` carries the Chow groups together with the
representability `CH^i(-) = Hom(1(-i), -)`. The theorem takes as hypotheses `hdual`, that every
object of `M_k` has a left dual, and `hgen`, that every object of `M_k` is a direct summand of a
twist `h(X)(m)`. -/
@[stacks 0FGN "Manin's identity principle: c is an isomorphism if c tensor 1 is an isomorphism
on the Chow groups of M tensor h(X) for every smooth projective X, over every degree i.
STATED IN AN ABSTRACT MONOIDAL CATEGORY, not on this library's category of motives, because the
monoidal structure on Karoubi S.Obj is Stacks 0FGC, which is only stated, not constructed, in this
library -- so `M ⊗ h(X)` cannot be written on `S.Motive` at all. The statement specialises to the
source's setting as soon as 0FGC is available, and `h : D → Mot` is kept untwisted on purpose so that
quantifying the hypothesis over D does not silently assume it for the twists h(X)(m), which is
what the source's proof has to earn. Four pieces of data are carried rather than used, each
named in the signature: the representability CH^i(-) = Hom(1(-i), -) of Stacks 0FGM (the field
chowEquiv of ChowRepresentability, together with its naturality), invertibility of the Tate
motive in the Stacks 0FFP sense (tateExactPairing), Stacks 0FGJ that every object has a left
dual (hdual), and generation, that every motive is a retract of a twist h(X)(m) (hgen), taken in
the weak Retract sense so the theorem is stronger. Proved here rather than carried: Stacks 0FFQ,
the summand step, the degree shift and the Yoneda step"]
theorem isIso_of_bijective_chowMap_tensorUnitHom (R : ChowRepresentability Mot)
    (hdual : ∀ L : Mot, HasRightDual L) {D : Type w} (h : D → Mot)
    (hgen : ∀ L : Mot, ∃ (X : D) (m : ℤ), Nonempty (Retract L (h X ⊗ R.unitTwist m)))
    {M N : Mot} (c : M ⟶ N)
    (hc : ∀ (X : D) (i : ℤ), Function.Bijective (R.chowMap i (c ⊗ₘ 𝟙 (h X)))) :
    IsIso c := by
  have key1 (X : D) (i : ℤ) :
      Function.Bijective fun x : R.unitTwist (-i) ⟶ M ⊗ h X => x ≫ c ▷ h X :=
    bijective_of_equiv_square (R.chowEquiv i (M ⊗ h X)) (R.chowEquiv i (N ⊗ h X))
      (fun x => (R.chowEquiv_naturality i (c ▷ h X) x).symm)
      (by simpa only [MonoidalCategory.tensorHom_id] using hc X i)
  have key3 (L : Mot) : Function.Bijective fun x : 𝟙_ Mot ⟶ M ⊗ L => x ≫ c ▷ L := by
    obtain ⟨X, m, ⟨ρ⟩⟩ := hgen L
    let _ := R.tateExactPairing m
    exact bijective_comp_whiskerRight_of_retract c ρ
      (bijective_comp_whiskerRight_twist c (h X) (R.unitTwist m) (R.unitTwist (-m)) (key1 X m))
  have key4 (K : Mot) : Function.Bijective fun x : K ⟶ M => x ≫ c := by
    let _ := hdual K
    refine bijective_of_equiv_square (homFromUnitEquiv K (Kᘁ) M).symm
      (homFromUnitEquiv K (Kᘁ) N).symm (fun x => ?_) (key3 (Kᘁ))
    apply (homFromUnitEquiv K (Kᘁ) N).injective
    rw [Equiv.apply_symm_apply, homFromUnitEquiv_comp, Equiv.apply_symm_apply]
  obtain ⟨d, hd⟩ := (key4 N).surjective (𝟙 N)
  refine ⟨d, (key4 M).injective ?_, hd⟩
  rw [Category.assoc, show d ≫ c = 𝟙 N from hd, Category.comp_id, Category.id_comp]

end Stacks.WeilCohomology

end
