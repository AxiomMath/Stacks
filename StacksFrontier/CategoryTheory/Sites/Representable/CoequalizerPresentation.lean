module

public import StacksFrontier.CategoryTheory.Sites.CoequalizerOfEpi
public import StacksFrontier.CategoryTheory.Sites.Representable.CoveredByRepresentables

/-!
# Every sheaf of sets is a coequalizer of coproducts of sheafified representables

Stacks tag 00WS. Let `E ⊆ Ob(C)` be a covering subset of a site `(C, J)` (every object has a
covering by elements of `E`) and let `F` be a sheaf of sets. Then `F` is a coequalizer
`F₁ ⇉ F₀ → F` in which `F₀` and `F₁` are coproducts, in the category of sheaves, of sheafified
representables `h_U^♯` with `U ∈ E`.

The epimorphism `∐_{(U, s) : E × F(U)} h_U^♯ ⟶ F` is
`Stacks.Sites.CoveredByRepresentables.isLocallySurjective_π`, up to the comparison isomorphism
between the coproduct of sheaves and the sheafification of the presheaf coproduct. Applying it to
`F` and to the kernel pair `F₀ ×_F F₀`, `CategoryTheory.Sheaf.isColimitCoforkOfEpiOfEpi` gives the
coequalizer.

## Main results

* `Stacks.Sites.CoveredByRepresentables.exists_isColimit_cofork_sigma_sheafifiedYoneda` —
  Stacks 00WS.
-/

@[expose] public section

open CategoryTheory Limits Opposite

universe v u

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)

namespace Stacks.Sites.CoveredByRepresentables

/-- The sheaf `h_U^♯`: the sheafification of the (universe-lifted) representable presheaf
`y(U)`. -/
noncomputable abbrev sheafifiedYoneda (U : C) : Sheaf J (Type max v u) :=
  (presheafToSheaf J (Type max v u)).obj (uliftYoneda.{u}.obj U)

/-- The canonical map `∐_{(U, s) : E × F(U)} h_U^♯ ⟶ F` out of a coproduct taken in the
category of sheaves; it is `π` precomposed with the comparison isomorphism
`∐ h_U^♯ ≅ a(∐ y(U))` (sheafification is a left adjoint, so it preserves coproducts). -/
noncomputable def σ (E : Set C) (F00WS : Sheaf J (Type max v u)) :
    (∐ fun p : index J E F00WS => sheafifiedYoneda J p.1.val) ⟶ F00WS :=
  (PreservesCoproduct.iso (presheafToSheaf J (Type max v u)) (indexFamilyPre J E F00WS)).inv ≫
    π J E F00WS

/-- The map `σ : ∐_{(U, s)} h_U^♯ ⟶ F` is an epimorphism of sheaves: it is `π`
(`isLocallySurjective_π`) precomposed with an isomorphism. -/
lemma epi_σ {E : Set C} (hE : IsCoveringSubset J E) (F00WS : Sheaf J (Type max v u)) :
    Epi (σ J E F00WS) := by
  have : Epi (π J E F00WS) :=
    (Sheaf.isLocallySurjective_iff_epi _).mp (isLocallySurjective_π J hE F00WS)
  exact @epi_comp _ _ _ _ _ _ (@IsIso.epi_of_iso _ _ _ _ _ (Iso.isIso_inv _)) _ this

/-- **Stacks 00WS.** Let `(C, J)` be a site and let `E ⊆ Ob(C)` be such that every object of `C`
has a covering by elements of `E` (`IsCoveringSubset J E`). Let `F00WS` be a sheaf of sets.
Then there is a diagram of sheaves of sets `F₁ ⇉ F₀ → F00WS` exhibiting `F00WS` as a
coequalizer, where `F₀ = ∐_{i ∈ I₀} h_{U₀ i}^♯` and `F₁ = ∐_{i ∈ I₁} h_{U₁ i}^♯` are coproducts
(in the category of sheaves) of sheafified representables `h_U^♯` with `U ∈ E`.

Proof as in Stacks: `σ : F₀ ⟶ F00WS` is an epimorphism (`epi_σ`), and so is the analogous map
`F₁ ⟶ F₀ ×_{F00WS} F₀` onto the kernel pair; an epimorphism of sheaves of sets is the
coequalizer of its kernel pair, and precomposing with an epimorphism keeps it a coequalizer. -/
@[stacks 00WS]
theorem exists_isColimit_cofork_sigma_sheafifiedYoneda {E : Set C} (hE : IsCoveringSubset J E)
    (F00WS : Sheaf J (Type max v u)) :
    ∃ (I₀ I₁ : Type max v u) (U₀ : I₀ → E) (U₁ : I₁ → E)
      (f g : (∐ fun i => sheafifiedYoneda J (U₁ i).val) ⟶
        ∐ fun i => sheafifiedYoneda J (U₀ i).val)
      (p : (∐ fun i => sheafifiedYoneda J (U₀ i).val) ⟶ F00WS) (w : f ≫ p = g ≫ p),
      Nonempty (IsColimit (Cofork.ofπ p w)) := by
  let p₀ : (∐ fun q : index J E F00WS => sheafifiedYoneda J q.1.val) ⟶ F00WS := σ J E F00WS
  have hp₀ : Epi p₀ := epi_σ J hE F00WS
  let q₁ : (∐ fun q : index J E (pullback p₀ p₀) => sheafifiedYoneda J q.1.val) ⟶
      pullback p₀ p₀ := σ J E (pullback p₀ p₀)
  have hq₁ : Epi q₁ := epi_σ J hE (pullback p₀ p₀)
  have w : (q₁ ≫ pullback.fst p₀ p₀) ≫ p₀ = (q₁ ≫ pullback.snd p₀ p₀) ≫ p₀ := by
    simp only [Category.assoc, pullback.condition]
  refine ⟨index J E F00WS, index J E (pullback p₀ p₀), fun q => q.1, fun q => q.1,
    q₁ ≫ pullback.fst p₀ p₀, q₁ ≫ pullback.snd p₀ p₀, p₀, w, ⟨?_⟩⟩
  exact @Sheaf.isColimitCoforkOfEpiOfEpi _ _ _ _ _ _ _ p₀ hp₀ _ (pullbackIsPullback p₀ p₀) q₁ hq₁

end Stacks.Sites.CoveredByRepresentables
