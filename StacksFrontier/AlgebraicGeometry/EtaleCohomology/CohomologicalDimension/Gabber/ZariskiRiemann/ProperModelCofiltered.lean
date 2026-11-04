module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CohomologicalDimension.Gabber.ZariskiRiemann.ZariskiRiemannLimitStep
public import Mathlib.CategoryTheory.Filtered.Basic

/-!
# The proper models of `Spec (Frac B)` over `Spec B` form a cofiltered category

Travaux de Gabber, Exposé XVIII-A, last remark of §2, passes to the limit over all proper models
`Y ⟶ Spec B` of `η = Spec (Frac B)` (`AlgebraicGeometry.Scheme.ZariskiRiemann.ProperModel`).
The limit is a filtered colimit of the `E₂`-terms `H^p(Y, R^q j_{Y*} F)` because the system of
models is cofiltered, which is what this file proves.

* **Common refinements.** Two models `Y₁`, `Y₂` are refined by the fibre product
  `Y₁ ×_{Spec B} Y₂`, which is proper over `Spec B` as a base change of a proper morphism followed
  by a proper one, with the point `(j₁, j₂) : η ⟶ Y₁ ×_{Spec B} Y₂`.
* **Equalizing refinements.** Two refinements `φ, ψ : Y' ⟶ Y` of the same model are equalized by
  the closed subscheme `E ⊆ Y'` where they agree: the base change of the diagonal
  `Y ⟶ Y ×_{Spec B} Y` along `(φ, ψ) : Y' ⟶ Y ×_{Spec B} Y`. As `Y` is proper, hence separated,
  over `Spec B`, the diagonal is a closed immersion, so `E ⟶ Y'` is a closed immersion and `E` is
  proper over `Spec B`. The point `j' : η ⟶ Y'` factors through `E` because
  `j' ≫ φ = j = j' ≫ ψ`. No reducedness or dominance of `j'` is needed: `E` is the
  scheme-theoretic equalizer, not the closure of the generic point.

## Main definitions

* `AlgebraicGeometry.Scheme.ZariskiRiemann.ProperModel.category` — models and refinements form a
  category, composition being `ProperModel.Refinement.comp`.
* `AlgebraicGeometry.Scheme.ZariskiRiemann.ProperModel.prod` — the fibre product model, with
  its projections `prodFst` and `prodSnd`.
* `AlgebraicGeometry.Scheme.ZariskiRiemann.ProperModel.eqLocus` — the equalizer model of two
  refinements, with its inclusion `eqLocusι`.

## Main results

* `AlgebraicGeometry.Scheme.ZariskiRiemann.ProperModel.eqLocusι_comp` — the inclusion of the
  equalizer model equalizes the two refinements.
* `AlgebraicGeometry.Scheme.ZariskiRiemann.ProperModel.isCofiltered` — **the category of proper
  models is cofiltered**.

## References

* Travaux de Gabber sur l'uniformisation locale et la cohomologie étale des schémas
  quasi-excellents, Exposé XVIII-A (L. Illusie), last remark of §2, Astérisque 363–364 (2014)
* SGA 4, Exposé VI, 8.7.4
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme.ZariskiRiemann

namespace ProperModel

variable {B : Type u} [CommRing B] [IsDomain B]

omit [IsDomain B] in
/-- Two refinements with the same underlying morphism are equal. -/
@[ext]
theorem Refinement.ext {M' M : ProperModel B} {φ ψ : Refinement M' M} (h : φ.π = ψ.π) :
    φ = ψ := by
  cases φ
  cases ψ
  cases h
  rfl

/-- The identity refinement of a model. -/
def Refinement.id (M : ProperModel B) : Refinement M M where
  π := 𝟙 M.Y
  comm := Category.id_comp _
  fac := Category.comp_id _

/-- **Proper models and their refinements form a category**, a morphism `M' ⟶ M` being a
refinement `M'.Y ⟶ M.Y` and composition being `ProperModel.Refinement.comp`. -/
instance category : Category.{u} (ProperModel B) where
  Hom M' M := Refinement M' M
  id M := Refinement.id M
  comp φ' φ := Refinement.comp φ' φ
  id_comp φ := Refinement.ext (Category.id_comp φ.π)
  comp_id φ := Refinement.ext (Category.comp_id φ.π)
  assoc φ'' φ' φ := Refinement.ext (Category.assoc φ''.π φ'.π φ.π)

omit [IsDomain B] in
/-- Morphisms of models are equal once their underlying morphisms of schemes are. -/
@[ext]
theorem hom_ext {M' M : ProperModel B} {φ ψ : M' ⟶ M} (h : φ.π = ψ.π) : φ = ψ :=
  Refinement.ext h

omit [IsDomain B] in
/-- The underlying morphism of the identity of a model `M` is the identity of `M.Y`. -/
@[simp]
theorem id_π (M : ProperModel B) : (𝟙 M : M ⟶ M).π = 𝟙 M.Y := rfl

omit [IsDomain B] in
/-- The underlying morphism of a composite of models is the composite of the underlying morphisms
of schemes. -/
@[simp]
theorem comp_π {M'' M' M : ProperModel B} (φ' : M'' ⟶ M') (φ : M' ⟶ M) :
    (φ' ≫ φ).π = φ'.π ≫ φ.π := rfl

omit [IsDomain B] in
/-- Composition in the category of models is `ProperModel.Refinement.comp`. -/
theorem comp_eq_refinementComp {M'' M' M : ProperModel B} (φ' : M'' ⟶ M') (φ : M' ⟶ M) :
    φ' ≫ φ = Refinement.comp φ' φ := rfl

section Product

variable (M₁ M₂ : ProperModel B)

/-- **The fibre product model** `Y₁ ×_{Spec B} Y₂` of two models, with the point `(j₁, j₂)`. It
is proper over `Spec B`: the first projection is a base change of the proper `Y₂ ⟶ Spec B`, and
`Y₁ ⟶ Spec B` is proper. -/
def prod : ProperModel B where
  Y := pullback M₁.f M₂.f
  f := pullback.fst M₁.f M₂.f ≫ M₁.f
  isProper := inferInstanceAs (IsProper (pullback.fst M₁.f M₂.f ≫ M₁.f))
  j := pullback.lift M₁.j M₂.j (by rw [M₁.fac, M₂.fac])
  fac := by rw [pullback.lift_fst_assoc, M₁.fac]

/-- The first projection of the fibre product model. -/
def prodFst : prod M₁ M₂ ⟶ M₁ where
  π := pullback.fst M₁.f M₂.f
  comm := rfl
  fac := pullback.lift_fst _ _ _

/-- The second projection of the fibre product model. -/
def prodSnd : prod M₁ M₂ ⟶ M₂ where
  π := pullback.snd M₁.f M₂.f
  comm := pullback.condition.symm
  fac := pullback.lift_snd _ _ _

end Product

section Equalizer

variable {M' M : ProperModel B} (φ ψ : M' ⟶ M)

/-- The morphism `(φ, ψ) : Y' ⟶ Y ×_{Spec B} Y` of two refinements. -/
def pairToPullback : M'.Y ⟶ pullback M.f M.f :=
  pullback.lift φ.π ψ.π (by rw [φ.comm, ψ.comm])

/-- **The equalizer model** of two refinements `φ, ψ : Y' ⟶ Y`: the closed subscheme of `Y'`
where they agree, the base change of the diagonal of `Y ⟶ Spec B` along `(φ, ψ)`. It is proper
over `Spec B` because the diagonal of the separated morphism `Y ⟶ Spec B` is a closed immersion,
so its base change `E ⟶ Y'` is a closed immersion, hence proper. The point `j'` factors through
it since `j' ≫ φ = j = j' ≫ ψ`. -/
def eqLocus : ProperModel B where
  Y := pullback (pairToPullback φ ψ) (pullback.diagonal M.f)
  f := pullback.fst (pairToPullback φ ψ) (pullback.diagonal M.f) ≫ M'.f
  isProper := inferInstanceAs
    (IsProper (pullback.fst (pairToPullback φ ψ) (pullback.diagonal M.f) ≫ M'.f))
  j := pullback.lift M'.j (M'.j ≫ φ.π) (by
    unfold pairToPullback
    apply pullback.hom_ext
    · rw [Category.assoc, Category.assoc, pullback.lift_fst, pullback.diagonal_fst,
        Category.comp_id]
    · rw [Category.assoc, Category.assoc, pullback.lift_snd, pullback.diagonal_snd,
        Category.comp_id, φ.fac, ψ.fac])
  fac := by rw [pullback.lift_fst_assoc, M'.fac]

/-- The inclusion of the equalizer model, a refinement. -/
def eqLocusι : eqLocus φ ψ ⟶ M' where
  π := pullback.fst (pairToPullback φ ψ) (pullback.diagonal M.f)
  comm := rfl
  fac := pullback.lift_fst _ _ _

/-- The inclusion of the equalizer model is a closed immersion. -/
instance isClosedImmersion_eqLocusι_π : IsClosedImmersion (eqLocusι φ ψ).π :=
  IsClosedImmersion.isStableUnderBaseChange.of_isPullback (IsPullback.of_hasPullback _ _).flip
    (IsSeparated.isClosedImmersion_diagonal (f := M.f))

omit [IsDomain B] in
/-- **The equalizer model equalizes the two refinements.** -/
theorem eqLocusι_comp : eqLocusι φ ψ ≫ φ = eqLocusι φ ψ ≫ ψ := by
  ext
  have key (p : pullback M.f M.f ⟶ M.Y) (a : M' ⟶ M) (h₁ : pairToPullback φ ψ ≫ p = a.π)
      (h₂ : pullback.diagonal M.f ≫ p = 𝟙 _) :
      pullback.fst (pairToPullback φ ψ) (pullback.diagonal M.f) ≫ a.π =
        pullback.snd (pairToPullback φ ψ) (pullback.diagonal M.f) := by
    rw [← h₁, ← Category.assoc, pullback.condition, Category.assoc, h₂, Category.comp_id]
  exact (key _ φ (pullback.lift_fst _ _ _) (pullback.diagonal_fst _)).trans
    (key _ ψ (pullback.lift_snd _ _ _) (pullback.diagonal_snd _)).symm

end Equalizer

/-- **The category of proper models of `Spec (Frac B)` over `Spec B` is cofiltered**: it contains
the trivial model `Spec B`, two models are refined by their fibre product
(`ProperModel.prod`), and two refinements of one model by another are equalized by the
equalizer model (`ProperModel.eqLocus`). -/
instance isCofiltered : IsCofiltered (ProperModel B) where
  cone_objs M₁ M₂ := ⟨prod M₁ M₂, prodFst M₁ M₂, prodSnd M₁ M₂, trivial⟩
  cone_maps _ _ φ ψ := ⟨eqLocus φ ψ, eqLocusι φ ψ, eqLocusι_comp φ ψ⟩
  nonempty := ⟨base⟩

end ProperModel

end AlgebraicGeometry.Scheme.ZariskiRiemann

end
