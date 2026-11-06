module

public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.SubbundleGeometry
public import StacksFrontier.AlgebraicGeometry.Chow.ProjectiveBundleFormula.Formula
public import StacksFrontier.AlgebraicGeometry.AmpleWire.UnitStalk

/-!
# The projective completion of a finite locally free module

Let `X` be a scheme and `ℰ` a finite locally free `𝒪_X`-module of rank `r`. The *projective
completion* of the vector bundle `Spec(Sym(ℰ))` is the projective space bundle

  `π : P = 𝐏(ℰ ⊕ 𝒪_X) = Proj_X(Sym(ℰ ⊕ 𝒪_X)) ⟶ X`

of the rank `r + 1` module `ℰ ⊕ 𝒪_X`, with the conventions of [Stacks, Tag 01O3] and
[Stacks, Tag 02TY]. The split surjection `ℰ ⊕ 𝒪_X ⟶ ℰ` induces a closed immersion

  `i : D = 𝐏(ℰ) ⟶ P`

over `X`, the *divisor at infinity*, along which `𝒪_P(1)` restricts to `𝒪_D(1)`. This file sets up
these objects and the short exact sequence `0 ⟶ 𝒪_X ⟶ ℰ ⊕ 𝒪_X ⟶ ℰ ⟶ 0` they come from.

## Main definitions

* `Stacks.ProjectiveCompletion.completionModule`: the module `ℰ ⊕ 𝒪_X`.
* `Stacks.ProjectiveCompletion.completionSequence`: the short exact sequence
  `0 ⟶ 𝒪_X ⟶ ℰ ⊕ 𝒪_X ⟶ ℰ ⟶ 0`.
* `Stacks.ProjectiveCompletion.projectiveCompletion`, `projectiveCompletionProj`: the projective
  completion `P = 𝐏(ℰ ⊕ 𝒪_X)` and its projection `π : P ⟶ X`.
* `Stacks.ProjectiveCompletion.infinityEmbedding`: the closed immersion `i : 𝐏(ℰ) ⟶ P`.
* `Stacks.ProjectiveCompletion.infinityTwistIso`: the isomorphism `i^*𝒪_P(1) ≅ 𝒪_{𝐏(ℰ)}(1)`.

## Main results

* `Stacks.ProjectiveCompletion.shortExact_completionSequence`: the sequence is short exact.
* `Stacks.ProjectiveCompletion.isFiniteLocallyFreeOfRank_completionModule`: `ℰ ⊕ 𝒪_X` has rank
  `r + 1` when `ℰ` has rank `r`.
* `Stacks.ProjectiveCompletion.flat_projectiveCompletionProj`,
  `locallyOfFiniteType_projectiveCompletionProj`,
  `relativeDimension_projectiveCompletionProj`: `π` is flat, locally of finite type and of
  relative dimension `r`.
* `Stacks.ProjectiveCompletion.infinityEmbedding_comp_projectiveCompletionProj`: `i` lies over `X`.

## References

* [Stacks Project, Tag 02TY](https://stacks.math.columbia.edu/tag/02TY)
* [Stacks Project, Tag 01O3](https://stacks.math.columbia.edu/tag/01O3)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.ProjectiveCompletion

variable {X : Scheme.{u}} (E : X.Modules)

variable (X) in
/-- The section `1` of the structure sheaf over an open `U`, read as a section of `𝒪_X` regarded
as a module over itself. -/
def unitModuleOne (U : X.Opens) : Γ(Stacks.Ample.unitModule X, U) :=
  (1 : Γ(X, U))

variable (X) in
/-- The section `1` restricts to `1`. -/
theorem unitModuleOne_restrict {U V : X.Opens} (h : V ≤ U) :
    (Stacks.Ample.unitModule X).val.map (homOfLE h).op (unitModuleOne X U) = unitModuleOne X V :=
  PresheafOfModules.unit_map_one (R := X.ringCatSheaf.obj) (homOfLE h).op

/-- **The module `ℰ ⊕ 𝒪_X`**, whose projective bundle is the projective completion of the vector
bundle of `ℰ`. -/
abbrev completionModule : X.Modules :=
  E ⊞ Stacks.Ample.unitModule X

/-- **The projection `ℰ ⊕ 𝒪_X ⟶ ℰ`.** -/
abbrev completionProjection : completionModule E ⟶ E :=
  biprod.fst

/-- **The inclusion `𝒪_X ⟶ ℰ ⊕ 𝒪_X` of the section `(0, 1)`.** -/
abbrev completionInclusion : Stacks.Ample.unitModule X ⟶ completionModule E :=
  biprod.inr

/-- The inclusion `ℰ ⟶ ℰ ⊕ 𝒪_X`. -/
abbrev completionInl : E ⟶ completionModule E :=
  biprod.inl

/-- The projection `ℰ ⊕ 𝒪_X ⟶ 𝒪_X`. -/
abbrev completionSnd : completionModule E ⟶ Stacks.Ample.unitModule X :=
  biprod.snd

/-- **The short exact sequence `0 ⟶ 𝒪_X ⟶ ℰ ⊕ 𝒪_X ⟶ ℰ ⟶ 0`** of the second inclusion and the
first projection. -/
def completionSequence : ShortComplex X.Modules :=
  ShortComplex.mk (completionInclusion E) (completionProjection E) biprod.inr_fst

/-- The first term of the completion sequence is `𝒪_X`. -/
@[simp]
theorem completionSequence_X₁ :
    (completionSequence E).X₁ = Stacks.Ample.unitModule X := rfl

/-- The middle term of the completion sequence is `ℰ ⊕ 𝒪_X`. -/
@[simp]
theorem completionSequence_X₂ : (completionSequence E).X₂ = completionModule E := rfl

/-- The last term of the completion sequence is `ℰ`. -/
@[simp]
theorem completionSequence_X₃ : (completionSequence E).X₃ = E := rfl

/-- The first map of the completion sequence is the inclusion `𝒪_X ⟶ ℰ ⊕ 𝒪_X`. -/
@[simp]
theorem completionSequence_f : (completionSequence E).f = completionInclusion E := rfl

/-- The second map of the completion sequence is the projection `ℰ ⊕ 𝒪_X ⟶ ℰ`. -/
@[simp]
theorem completionSequence_g : (completionSequence E).g = completionProjection E := rfl

/-- The splitting of the completion sequence by the first inclusion and the second projection. -/
def completionSequenceSplitting : (completionSequence E).Splitting where
  r := completionSnd E
  s := completionInl E
  f_r := biprod.inr_snd
  s_g := biprod.inl_fst
  id := by
    rw [add_comm]
    exact biprod.total

/-- **The completion sequence is short exact.** -/
theorem shortExact_completionSequence : (completionSequence E).ShortExact :=
  (completionSequenceSplitting E).shortExact

/-- `ℰ ⊕ 𝒪_X` is finite locally free when `ℰ` is. -/
instance isFiniteLocallyFree_completionModule
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E] :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} (completionModule E) :=
  Stacks.Chow.GenuineChern.isFiniteLocallyFree_of_shortExact (completionSequence E)
    (shortExact_completionSequence E)
    (AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree
      (Stacks.Ample.unitModule X) 1)
    (inferInstanceAs (AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E))

/-- **`ℰ ⊕ 𝒪_X` has rank `r + 1` when `ℰ` has rank `r`.** -/
instance isFiniteLocallyFreeOfRank_completionModule (r : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E r] :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (completionModule E)
      (r + 1) := by
  have h := Stacks.Chow.GenuineChern.isFiniteLocallyFreeOfRank_of_shortExact
    (completionSequence E) (shortExact_completionSequence E) 1 r
    (inferInstanceAs (AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (Stacks.Ample.unitModule X) 1))
    (inferInstanceAs (AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E r))
  rw [Nat.add_comm] at h
  exact h

variable [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E]

/-- **The projective completion `P = 𝐏(ℰ ⊕ 𝒪_X)`** of the vector bundle of `ℰ`: the projective
bundle `Proj_X(Sym(ℰ ⊕ 𝒪_X))` of `Stacks.Chow.bundle`. -/
abbrev projectiveCompletion : Scheme.{u} :=
  Stacks.Chow.bundle (completionModule E)

/-- **The projection `π : P ⟶ X`** of the projective completion. -/
abbrev projectiveCompletionProj : projectiveCompletion E ⟶ X :=
  Stacks.Chow.bundleProj (completionModule E)

/-- The projection `ℰ ⊕ 𝒪_X ⟶ ℰ` is an epimorphism (it is split by the first inclusion). -/
instance epi_completionProjection : Epi (completionProjection E) :=
  @IsSplitEpi.epi _ _ _ _ _ (biprod.fst_epi (X := E) (Y := Stacks.Ample.unitModule X))

/-- **The divisor at infinity `i : 𝐏(ℰ) ⟶ P`**: the closed immersion of projective bundles induced
by the projection `ℰ ⊕ 𝒪_X ⟶ ℰ`. -/
abbrev infinityEmbedding : Stacks.Chow.bundle E ⟶ projectiveCompletion E :=
  Stacks.Chow.GenuineChern.bundleEmbedding (completionProjection E)

/-- **The divisor at infinity lies over `X`.** -/
@[reassoc (attr := simp)]
theorem infinityEmbedding_comp_projectiveCompletionProj :
    infinityEmbedding E ≫ projectiveCompletionProj E = Stacks.Chow.bundleProj E :=
  Stacks.Chow.GenuineChern.bundleEmbedding_comp_bundleProj _

/-- **`𝒪_P(1)` restricts to `𝒪_{𝐏(ℰ)}(1)` along the divisor at infinity**: the isomorphism
`i^*𝒪_P(1) ≅ 𝒪_{𝐏(ℰ)}(1)` carrying the pulled-back tautological quotient of `ℰ ⊕ 𝒪_X` to the
tautological quotient of `ℰ` precomposed with the projection. -/
def infinityTwistIso :
    (Scheme.Modules.pullback (infinityEmbedding E)).obj
        (Stacks.Chow.bundleTwist (completionModule E)) ≅ Stacks.Chow.bundleTwist E :=
  Stacks.Chow.GenuineChern.bundleEmbeddingTwistIso _

section Rank

variable (n : ℕ) [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E n]

include n

/-- **The projection of the projective completion is flat.** -/
theorem flat_projectiveCompletionProj : Flat (projectiveCompletionProj E) :=
  Stacks.Chow.flat_bundleProj (completionModule E) n

/-- **The projection of the projective completion is locally of finite type.** -/
theorem locallyOfFiniteType_projectiveCompletionProj :
    LocallyOfFiniteType (projectiveCompletionProj E) :=
  Stacks.Chow.locallyOfFiniteType_bundleProj (completionModule E) n

/-- **The projection of the projective completion of a module of rank `n` has relative
dimension `n`.** -/
theorem relativeDimension_projectiveCompletionProj :
    letI := locallyOfFiniteType_projectiveCompletionProj E n
    AlgebraicGeometry.RelativeDimension (projectiveCompletionProj E) n :=
  Stacks.Chow.relativeDimension_bundleProj (completionModule E) n

end Rank

end Stacks.ProjectiveCompletion

end
