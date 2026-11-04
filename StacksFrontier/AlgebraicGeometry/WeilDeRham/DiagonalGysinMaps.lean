module

public import StacksFrontier.AlgebraicGeometry.DeRham.RelativePoincareDuality.DiagonalGysinAmbient

/-!
# The Gysin maps of the diagonal and of the two constant sections, on classes of `X`

Let `f : X ⟶ Spec A` be proper and smooth of relative dimension `n` with a section `σ`, let
`W = X ×_A X` with projections `p₁`, `p₂` and structure morphism `π_W = p₁ ≫ f`. The proof of
[Stacks, Tag 0G8J] applies the Gysin maps `γ^{p,q}` of [Stacks, Tag 0G8A] of three closed
immersions `X ⟶ W` to classes of `Hᵠ(X, Ωᵖ_{X/A})`:

* the diagonal `Δ`, a section of `p₁`;
* `j = (σ ∘ f, id)`, a section of `p₂`;
* `j' = (id, σ ∘ f)`, a section of `p₁`.

A class `θ` of `X` is fed to `γ_i` as its *ambient copy*: pulled back to `W` along a retraction
of `i` and restricted to `i_*Ωᵖ_{X/A}`; by
`Stacks.DeRham.CohomologicalGysin.formRestriction_comp_retraction_eq` this does not depend on the
retraction. This file packages the three composites as maps
`Hᵠ(X, Ωᵖ_{X/A}) ⟶ H^{q+n}(W, Ω^{p+n}_{W/A})`.

## Main definitions

* `Stacks.WeilDeRham.ambientCopy`: the ambient copy along a retraction.
* `Stacks.WeilDeRham.diagonalGysin`, `Stacks.WeilDeRham.sectionFstGysin`,
  `Stacks.WeilDeRham.sectionSndGysin`: the Gysin maps of `Δ`, `j` and `j'` on classes of `X`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open RingedSpaceModuleAdjunction Stacks.Gysin Stacks.DeRham.GysinCohomologyBaseChange
open AlgebraicGeometry.Scheme.Hom Stacks.AlgebraicGeometry.ConormalEquations
open Stacks.AlgebraicGeometry.RegularIdealSheaf Stacks.DeRham.CohomologicalGysin

universe u

namespace Stacks.WeilDeRham

section Ambient

variable {X W S : Scheme.{u}} (f : X ⟶ S) (πW : W ⟶ S)

/-- **The ambient copy of a class of `X` along a retraction.** For a closed immersion `i : X ⟶ W`
and a morphism `G : W ⟶ X` over `S`, the class of `Hᵠ(X, Ωᵖ_{X/S})` pulled back along `G` and
restricted to `i_*Ωᵖ_{X/S}`. -/
def ambientCopy (i : X ⟶ W) (G : W ⟶ X) (wG : G ≫ f = πW ≫ 𝟙 S) (p q : ℕ) :
    Hgroup (structureSheafRing X.toRingedSpace) ⊤ q (relativeDifferentialForms f (p : ℤ)) ⟶
      Hgroup (structureSheafRing W.toRingedSpace) ⊤ q (pushforwardRelativeForms i πW (p : ℤ)) :=
  pullbackHgroup (CohomologyPullbackComparison.canonical G.toLRSHom.toShHom) 0 (q : ℤ) q
      (by simp) (formsBaseChangeHom G f πW (𝟙 S) wG (p : ℤ)) ≫
    (Hfunctor (structureSheafRing W.toRingedSpace) ⊤ q).map (formRestrictionModules i πW (p : ℤ))

end Ambient

variable {A : Type u} [CommRing A] {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) [IsProper f]
  (n : ℕ) [SmoothOfRelativeDimension n f] (σ : Spec (.of A) ⟶ X) (hσ : σ ≫ f = 𝟙 _)

/-- The structure morphism `π_W = p₁ ≫ f` of `W = X ×_A X`. -/
abbrev prodStructure : pullback f f ⟶ Spec (.of A) := pullback.fst f f ≫ f

omit [IsProper f] in
/-- The first projection `p₁ : W ⟶ X` is a morphism over `Spec A`: `p₁ ≫ f = π_W ≫ 𝟙`. -/
theorem fst_comp_eq_prodStructure : pullback.fst f f ≫ f = prodStructure f ≫ 𝟙 _ :=
  (Category.comp_id _).symm

omit [IsProper f] in
/-- The second projection `p₂ : W ⟶ X` is a morphism over `Spec A`: `p₂ ≫ f = π_W ≫ 𝟙`. -/
theorem snd_comp_eq_prodStructure : pullback.snd f f ≫ f = prodStructure f ≫ 𝟙 _ :=
  pullback.condition.symm.trans (Category.comp_id _).symm

/-- The diagonal `Δ : X ⟶ X ×_A X` is locally of finite presentation. -/
instance : LocallyOfFinitePresentation (pullback.diagonal f) := by
  have : LocallyOfFinitePresentation (pullback.diagonal f ≫ pullback.fst f f) := by
    rw [pullback.diagonal_fst]; infer_instance
  exact locallyOfFinitePresentation_of_comp _ (pullback.fst f f)

include n in
/-- The first projection `p₁ : X ×_A X ⟶ X` is smooth. -/
theorem smooth_fst : Smooth (pullback.fst f f) :=
  have := smoothOfRelativeDimension_fst f n
  SmoothOfRelativeDimension.smooth n _

include n in
/-- The second projection `p₂ : X ×_A X ⟶ X` is smooth. -/
theorem smooth_snd : Smooth (pullback.snd f f) :=
  have := smoothOfRelativeDimension_snd f n
  SmoothOfRelativeDimension.smooth n _

include n in
/-- The structure morphism `π_W : X ×_A X ⟶ Spec A` is smooth. -/
theorem smooth_prodStructure : Smooth (prodStructure f) :=
  have := smooth_fst f n
  have : Smooth f := SmoothOfRelativeDimension.smooth n f
  inferInstanceAs (Smooth (pullback.fst f f ≫ f))

/-- **The Gysin map of the diagonal on classes of `X`**: `θ ↦ γ_Δ^{p,q}(p₁^*θ|_Δ)`. -/
def diagonalGysin (p q : ℕ) :
    Hgroup (structureSheafRing X.toRingedSpace) ⊤ q (relativeDifferentialForms f (p : ℤ)) ⟶
      Hgroup (structureSheafRing (pullback f f).toRingedSpace) ⊤ (q + n)
        (relativeDifferentialForms (prodStructure f) ((p : ℤ) + (n : ℤ))) :=
  haveI := smooth_prodStructure f n
  ambientCopy f (prodStructure f) (pullback.diagonal f) (pullback.fst f f)
      (fst_comp_eq_prodStructure f) p q ≫
    formsGysinMap (pullback.diagonal f) (prodStructure f)
      (diagonal_koszul_and_conormalRank f n).1 (diagonal_koszul_and_conormalRank f n).2 p q

section Sections

variable [IsClosedImmersion σ]

/-- `j = (σ ∘ f, id) : X ⟶ X ×_A X` is a closed immersion. -/
instance isClosedImmersion_sectionFst : IsClosedImmersion (sectionFst f σ hσ) :=
  MorphismProperty.of_isPullback (P := @IsClosedImmersion) (isPullback_section_fst f σ hσ)
    inferInstance

/-- `j' = (id, σ ∘ f) : X ⟶ X ×_A X` is a closed immersion. -/
instance isClosedImmersion_sectionSnd : IsClosedImmersion (sectionSnd f σ hσ) :=
  MorphismProperty.of_isPullback (P := @IsClosedImmersion) (isPullback_section_snd f σ hσ)
    inferInstance

variable [LocallyOfFinitePresentation σ]

/-- `j = (σ ∘ f, id) : X ⟶ X ×_A X` is locally of finite presentation. -/
instance locallyOfFinitePresentation_sectionFst :
    LocallyOfFinitePresentation (sectionFst f σ hσ) :=
  MorphismProperty.of_isPullback (P := @LocallyOfFinitePresentation)
    (isPullback_section_fst f σ hσ) inferInstance

/-- `j' = (id, σ ∘ f) : X ⟶ X ×_A X` is locally of finite presentation. -/
instance locallyOfFinitePresentation_sectionSnd :
    LocallyOfFinitePresentation (sectionSnd f σ hσ) :=
  MorphismProperty.of_isPullback (P := @LocallyOfFinitePresentation)
    (isPullback_section_snd f σ hσ) inferInstance

/-- A section `i` of a morphism `π` smooth of relative dimension `n` is Koszul regular with
conormal sheaf locally free of rank `n`. -/
private theorem section_koszul_and_conormalRank {Y : Scheme.{u}} (i : X ⟶ Y) (π : Y ⟶ X)
    (hi : i ≫ π = 𝟙 X) [IsClosedImmersion i]
    [SmoothOfRelativeDimension n π] [Smooth π] :
    IsKoszulRegularImmersion i ∧ ConormalRank i n := by
  have : Smooth (i ≫ π) := by simpa only [hi] using (inferInstance : Smooth (𝟙 X))
  have : FormallyUnramified (i ≫ π) := by
    simpa only [hi] using (inferInstance : FormallyUnramified (𝟙 X))
  exact ⟨isKoszulRegularImmersion_of_smooth_of_smooth _ π,
    conormalRank_of_formallyUnramified _ π n⟩

omit [LocallyOfFinitePresentation σ] in
/-- `j = (σ ∘ f, id)` is Koszul regular with conormal sheaf locally free of rank `n`: it is a
section of the smooth `p₂`. -/
theorem sectionFst_koszul_and_conormalRank :
    IsKoszulRegularImmersion (sectionFst f σ hσ) ∧ ConormalRank (sectionFst f σ hσ) n :=
  have := smoothOfRelativeDimension_snd f n
  have := smooth_snd f n
  section_koszul_and_conormalRank n (sectionFst f σ hσ) (pullback.snd f f) (pullback.lift_snd _ _ _)

omit [LocallyOfFinitePresentation σ] in
/-- `j' = (id, σ ∘ f)` is Koszul regular with conormal sheaf locally free of rank `n`: it is a
section of the smooth `p₁`. -/
theorem sectionSnd_koszul_and_conormalRank :
    IsKoszulRegularImmersion (sectionSnd f σ hσ) ∧ ConormalRank (sectionSnd f σ hσ) n :=
  have := smoothOfRelativeDimension_fst f n
  have := smooth_fst f n
  section_koszul_and_conormalRank n (sectionSnd f σ hσ) (pullback.fst f f) (pullback.lift_fst _ _ _)

/-- **The Gysin map of `j = (σ ∘ f, id)` on classes of `X`**: `θ ↦ γ_j^{p,q}(p₂^*θ|_j)`. -/
def sectionFstGysin (p q : ℕ) :
    Hgroup (structureSheafRing X.toRingedSpace) ⊤ q (relativeDifferentialForms f (p : ℤ)) ⟶
      Hgroup (structureSheafRing (pullback f f).toRingedSpace) ⊤ (q + n)
        (relativeDifferentialForms (prodStructure f) ((p : ℤ) + (n : ℤ))) :=
  haveI := smooth_prodStructure f n
  ambientCopy f (prodStructure f) (sectionFst f σ hσ) (pullback.snd f f)
      (snd_comp_eq_prodStructure f) p q ≫
    formsGysinMap (sectionFst f σ hσ) (prodStructure f)
      (sectionFst_koszul_and_conormalRank f n σ hσ).1
      (sectionFst_koszul_and_conormalRank f n σ hσ).2 p q

/-- **The Gysin map of `j' = (id, σ ∘ f)` on classes of `X`**: `θ ↦ γ_{j'}^{p,q}(p₁^*θ|_{j'})`. -/
def sectionSndGysin (p q : ℕ) :
    Hgroup (structureSheafRing X.toRingedSpace) ⊤ q (relativeDifferentialForms f (p : ℤ)) ⟶
      Hgroup (structureSheafRing (pullback f f).toRingedSpace) ⊤ (q + n)
        (relativeDifferentialForms (prodStructure f) ((p : ℤ) + (n : ℤ))) :=
  haveI := smooth_prodStructure f n
  ambientCopy f (prodStructure f) (sectionSnd f σ hσ) (pullback.fst f f)
      (fst_comp_eq_prodStructure f) p q ≫
    formsGysinMap (sectionSnd f σ hσ) (prodStructure f)
      (sectionSnd_koszul_and_conormalRank f n σ hσ).1
      (sectionSnd_koszul_and_conormalRank f n σ hσ).2 p q

end Sections

end Stacks.WeilDeRham

end
