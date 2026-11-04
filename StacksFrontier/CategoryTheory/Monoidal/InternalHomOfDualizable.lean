module

public import StacksFrontier.CategoryTheory.Monoidal.InternalHomEvaluationBijection
public import StacksFrontier.CategoryTheory.Monoidal.Rigid

/-!
# A monoidal functor preserves internal Homs out of a dualizable object

Let `C` be a monoidal category and `K` an object of `C`. An **internal Hom** from `K` to `L` is
an object `I` together with an evaluation `e : I ⊗ K ⟶ L` through which every morphism
`T ⊗ K ⟶ L` factors uniquely as `g ▷ K ≫ e`, that is,
`∀ T, Function.Bijective fun g : T ⟶ I => g ▷ K ≫ e`. This is the hypothesis shape of
`StacksFrontier.CategoryTheory.Monoidal.InternalHomEvaluationBijection`, whose uniqueness statement
`CategoryTheory.MonoidalCategory.exists_iso_whiskerRight_comp_of_tensorHomBijective` is reused
here. No closed structure on `C` is assumed: the notion is the universal property alone.

Mathlib's `CategoryTheory.MonoidalClosed` is not used because it does not fit the consumer.
Its `ihom K` is right adjoint to `K ⊗ -`, with `K` on the left, and it is a structure on the
whole category, while the derived internal Hom of a ringed site in this development is the
bifunctor `AlgebraicGeometry.RingedSite.derivedSheafHomBifunctor` together with the pointwise
bijection `AlgebraicGeometry.RingedSite.derivedCurryHomEquiv` of Stacks 08J8,
`(A ⟶ R𝓗om(K, L)) ≃ (A ⊗ K ⟶ L)`, with `K` on the right; no `MonoidalClosed` instance on a
derived category exists. The bijectivity hypothesis is the `Prop`-valued form of Mathlib's
`CategoryTheory.Functor.RepresentableBy` for the functor `T ↦ (T ⊗ K ⟶ L)`, with the
representing bijection given by composition with `e`; it is exactly what that bijection
and its naturality in the source variable supply.

If `K` has a right dual `K'` (an exact pairing `K ⊣ K'`), every internal Hom from `K` to `L` is
`L ⊗ K'` with its standard evaluation, and a monoidal functor `P : C ⥤ D` carries it to an
internal Hom from `P K` to `P L`, the evaluation being `μ ≫ P e`. Consequently any morphism
`φ : P I ⟶ J` into an internal Hom `(J, e')` of `D` with `φ ▷ P K ≫ e' = μ ≫ P e` is an
isomorphism.

This is the formal core of the statement that the canonical map
`P R𝓗om(K, L) ⟶ R𝓗om(P K, P L)` of Stacks 08JF is an isomorphism when `K` is dualizable —
the case of a perfect object `K` (Stacks 0FPV) — for a functor `P` which is monoidal for the
derived tensor products: that map is, by its construction, the morphism compatible with the two
evaluations.

## Main definitions

* `CategoryTheory.MonoidalCategory.pairingEvaluation`: the evaluation `(L ⊗ K') ⊗ K ⟶ L` of an
  exact pairing `K ⊣ K'`.

## Main results

* `CategoryTheory.MonoidalCategory.isIso_of_whiskerRight_comp_of_tensorHomBijective`: a
  morphism between two internal Homs compatible with their evaluations is an isomorphism.
* `CategoryTheory.MonoidalCategory.tensorHomBijective_pairingEvaluation`: `L ⊗ K'` with its
  standard evaluation is an internal Hom from `K` to `L`.
* `CategoryTheory.MonoidalCategory.tensorHomBijective_map`: a monoidal functor carries an
  internal Hom out of a dualizable object to an internal Hom.
* `CategoryTheory.MonoidalCategory.isIso_of_tensorHomBijective_map`: the comparison morphism of
  a monoidal functor with internal Homs out of a dualizable object is an isomorphism.
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory Functor.LaxMonoidal Functor.OplaxMonoidal

namespace CategoryTheory.MonoidalCategory

variable {C : Type*} [Category C] [MonoidalCategory C]

/-- **A morphism between two internal Homs compatible with their evaluations is an
isomorphism.** -/
theorem isIso_of_whiskerRight_comp_of_tensorHomBijective {K L I I' : C}
    {e : I ⊗ K ⟶ L} {e' : I' ⊗ K ⟶ L}
    (h : ∀ T : C, Function.Bijective fun g : T ⟶ I => g ▷ K ≫ e)
    (h' : ∀ T : C, Function.Bijective fun g : T ⟶ I' => g ▷ K ≫ e')
    (f : I ⟶ I') (hf : f ▷ K ≫ e' = e) : IsIso f := by
  obtain ⟨θ, hθ⟩ := exists_iso_whiskerRight_comp_of_tensorHomBijective e e' h h'
  have : f = θ.hom := (h' I).injective (hf.trans hθ.symm)
  rw [this]
  infer_instance

/-- An internal Hom transported along an isomorphism is an internal Hom. -/
theorem tensorHomBijective_of_iso {K L I I' : C} {e : I ⊗ K ⟶ L}
    (h : ∀ T : C, Function.Bijective fun g : T ⟶ I => g ▷ K ≫ e) (θ : I' ≅ I) :
    ∀ T : C, Function.Bijective fun g : T ⟶ I' => g ▷ K ≫ θ.hom ▷ K ≫ e := by
  intro T
  have key : (fun g : T ⟶ I' => g ▷ K ≫ θ.hom ▷ K ≫ e) =
      (fun g : T ⟶ I => g ▷ K ≫ e) ∘ (fun g : T ⟶ I' => g ≫ θ.hom) := by
    funext g
    simp
  rw [key]
  exact (h T).comp ⟨fun a b hab => by simpa using congrArg (· ≫ θ.inv) hab,
    fun g => ⟨g ≫ θ.inv, by simp⟩⟩

/-- The standard evaluation `(L ⊗ K') ⊗ K ⟶ L` of an exact pairing `K ⊣ K'`. -/
def pairingEvaluation (K K' L : C) [ExactPairing K K'] : (L ⊗ K') ⊗ K ⟶ L :=
  (α_ L K' K).hom ≫ L ◁ ε_ K K' ≫ (ρ_ L).hom

/-- **`L ⊗ K'` is an internal Hom from `K` to `L`** for an exact pairing `K ⊣ K'`: this is the
bijection `CategoryTheory.tensorRightHomEquiv`. -/
theorem tensorHomBijective_pairingEvaluation (K K' L : C) [ExactPairing K K'] :
    ∀ T : C, Function.Bijective fun g : T ⟶ L ⊗ K' => g ▷ K ≫ pairingEvaluation K K' L := by
  intro T
  have key : (fun g : T ⟶ L ⊗ K' => g ▷ K ≫ pairingEvaluation K K' L) =
      (tensorRightHomEquiv T K K' L).symm := by
    funext g
    rfl
  rw [key]
  exact (tensorRightHomEquiv T K K' L).symm.bijective

variable {D : Type*} [Category D] [MonoidalCategory D]

/-- **A monoidal functor carries an internal Hom out of a dualizable object to an internal
Hom.** If `K ⊣ K'` is an exact pairing in `C` and `e : I ⊗ K ⟶ L` is the evaluation of an
internal Hom, then `μ ≫ P e : P I ⊗ P K ⟶ P L` is the evaluation of an internal Hom in `D`. -/
theorem tensorHomBijective_map (P : C ⥤ D) [P.Monoidal] (K K' : C) {L I : C}
    [ExactPairing K K'] {e : I ⊗ K ⟶ L}
    (h : ∀ T : C, Function.Bijective fun g : T ⟶ I => g ▷ K ≫ e) :
    ∀ T : D, Function.Bijective fun g : T ⟶ P.obj I => g ▷ P.obj K ≫ μ P I K ≫ P.map e := by
  let := ExactPairing.map P K K'
  have hstd := tensorHomBijective_pairingEvaluation K K' L
  obtain ⟨θ, hθe⟩ := exists_iso_whiskerRight_comp_of_tensorHomBijective e _ h hstd
  let θ' : P.obj I ≅ P.obj L ⊗ P.obj K' := P.mapIso θ ≪≫ (Functor.Monoidal.μIso P L K').symm
  have hP := tensorHomBijective_of_iso
    (tensorHomBijective_pairingEvaluation (P.obj K) (P.obj K') (P.obj L)) θ'
  convert hP using 3
  rw [← hθe]
  simp only [θ', pairingEvaluation, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom,
    Functor.Monoidal.μIso_inv, comp_whiskerRight, Category.assoc, ExactPairing.map_evaluation,
    MonoidalCategory.whiskerLeft_comp, Functor.map_comp]
  rw [← μ_natural_left_assoc]
  congr 1
  rw [Functor.Monoidal.map_associator]
  simp only [Category.assoc, Functor.Monoidal.μ_δ_assoc]
  congr 3
  rw [← Functor.LaxMonoidal.μ_natural_right_assoc, Functor.Monoidal.map_rightUnitor,
    Functor.Monoidal.μ_δ_assoc]

/-- **The comparison of a monoidal functor with internal Homs out of a dualizable object is an
isomorphism.** Let `K ⊣ K'` be an exact pairing in `C`, `e : I ⊗ K ⟶ L` the evaluation of an
internal Hom from `K` to `L`, and `e' : J ⊗ P K ⟶ P L` that of an internal Hom from `P K` to
`P L` in `D`. Any `φ : P I ⟶ J` with `φ ▷ P K ≫ e' = μ ≫ P e` is an isomorphism. -/
theorem isIso_of_tensorHomBijective_map (P : C ⥤ D) [P.Monoidal] (K K' : C) {L I : C}
    [ExactPairing K K'] {e : I ⊗ K ⟶ L}
    (h : ∀ T : C, Function.Bijective fun g : T ⟶ I => g ▷ K ≫ e)
    {J : D} {e' : J ⊗ P.obj K ⟶ P.obj L}
    (h' : ∀ T : D, Function.Bijective fun g : T ⟶ J => g ▷ P.obj K ≫ e')
    (φ : P.obj I ⟶ J) (hφ : φ ▷ P.obj K ≫ e' = μ P I K ≫ P.map e) : IsIso φ :=
  isIso_of_whiskerRight_comp_of_tensorHomBijective (tensorHomBijective_map P K K' h) h' φ hφ

end CategoryTheory.MonoidalCategory
