module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.CoherentFinitePresentation
public import StacksFrontier.AlgebraicGeometry.AmpleCharacterization.ClauseNineDirect
public import StacksFrontier.AlgebraicGeometry.AmpleGlobalGeneration.Twist
public import StacksFrontier.AlgebraicGeometry.AmpleLocalGeneration.FromExtension
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CoherentAdicSystem.Epi
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CoherentAdicSystem.TransitionTwistLift
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionNegativeTwistSum
public import StacksFrontier.AlgebraicGeometry.RelativeAmpleAffineBase.Basic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Every coherent adic system is a quotient of the completion of a coherent module

The generation statement of [Stacks, Tag 0885]: let `A` be a Noetherian ring, `I ⊆ A` an ideal,
`f : X ⟶ Spec A` proper, `L` an invertible `𝒪_X`-module ample relative to `f`, and `𝓕` an object
of `Coh(X, 𝓘)` for `𝓘 = I · 𝒪_X`. Then `𝓕` receives an epimorphism from the completion of a
coherent `𝒪_X`-module.

This is the source's first paragraph, assembled from the pieces the library already carries:

1. the uniform `H¹`-vanishing of [Stacks, Tag 0884] and the surjectivity of the twisted transition
   maps on global sections it yields, through the lifting of a family of sections of
   `𝓕_0 ⊗ L ^⊗ d` to a family compatible along the whole tower
   (`Stacks.Coherent.exists_compatible_sections_whiskerRight_tensorPowModule`);
2. Serre's global generation, clause (7) of [Stacks, Tag 01Q3]
   (`Stacks.AmpleLocalGeneration.isEventuallyGloballyGenerated_of_isAmple`), which generates
   `𝓕_0 ⊗ L ^⊗ d` by finitely many global sections once `d` is large;
3. the completion of a finite sum of negative twists and the morphism out of it a compatible
   family of sections determines (`Stacks.Algebraization.descCompletionNegativeTwistSumOfSections`);
4. [Stacks, Tag 087Y] (`Stacks.Coherent.epi_iff_epi_app_zero`), which reduces surjectivity of
   that morphism to its lowest level.

With this, `Stacks.Algebraization.isEquivalence_completionFunctor_of_isProjective` and its
H-projective companion in `CompletionProjective.lean` carry **no hypothesis beyond the source's**.

## Main results

* `Stacks.Algebraization.exists_epi_negativeTwistSum_of_generatingSections` — from finitely many
  global sections generating `F ⊗ L ^⊗ d`, an epimorphism `(L ^⊗ (-d)) ^⊕ t ⟶ F`. This is the
  untwisting of [Stacks, Tag 01Q3] (7) ⇒ (8) transported onto the direct sum
  `Stacks.Algebraization.negativeTwistSum` that the completion functor is applied to.
* `Stacks.Algebraization.exists_sections_epi_negativeTwistSumDesc` — the same epimorphism
  presented as the map assembled from `t` global sections of `F ⊗ L ^⊗ d`, which is the form the
  mapping-out property of the completion consumes.
* `Stacks.Algebraization.exists_epi_completionFunctor_of_isRelativelyAmple` — **the generation
  statement of [Stacks, Tag 0885]**, for a proper `f` and an `f`-ample invertible `L`.

## Implementation notes

**The degree.** Two thresholds have to be cleared at once: the `d₀` of the lifting step, which is
that of [Stacks, Tag 0884], and the `n₀` of clause (7) of [Stacks, Tag 01Q3] at the lowest term
`𝓕_0`. The degree used is `max d₀ n₀`; both hypotheses are monotone in the degree, so this is the
only combination needed, and the order of production matters — the generating family fixes `t`,
and the lifting is then applied to that `t`.

**Absolute ampleness, over the affine base.** Clause (7) is stated for an ample invertible module,
while the hypothesis available is relative ampleness over `Spec A`; the two agree over an affine
base by [Stacks, Tag 01VK],
`Stacks.RelativeAmpleAffineBase.isRelativelyAmple_iff_isAmple`. This is the same step
`CoherentAdicSystem/TransitionKernelTwistVanishing.lean` takes for [Stacks, Tag 0884].

**Why the sections are produced from the morphism and not the other way round.** Clause (7)
delivers a family of generating sections of `F ⊗ L ^⊗ d` as Mathlib's
`SheafOfModules.GeneratingSections`, whose epimorphism is out of the free module
`𝒪_X^{⊕ σ.I}` — not out of `(L ^⊗ (-d)) ^⊕ t`, and with no relation to
`Stacks.AmpleCharacterization.twistHom` of the sections, which is what the mapping-out property
needs. Rather than match the two presentations, the epimorphism out of the sum of negative twists
is built first, by the untwisting
`Stacks.AmpleGlobalGeneration.exists_epi_biproduct_of_epi_free`, and the *sections* are then read
off its components by `Stacks.AmpleCharacterization.exists_twistHom_eq` — every morphism
`L ^⊗ (-d) ⟶ F` is `twistHom` of a section. The assembled map is then equal to the epimorphism
by `Stacks.Algebraization.negativeTwistSum_hom_ext`, so no comparison of `SheafOfModules.free`
with a biproduct of units, and no naturality of `twistHom` in the index, is needed.

**The reindexing to `Fin t`.** The untwisting produces a bilimit bicone indexed by the index type
`σ.I` of the generating family, which lives in the module universe, while
`Stacks.Algebraization.negativeTwistSum` is indexed by `Fin t`. The move is
`CategoryTheory.Limits.Bicone.whisker` along an equivalence `σ.I ≃ Fin t` from
`Finite.exists_equiv_fin` with `CategoryTheory.Limits.Bicone.whiskerIsBilimitIff` transporting the
bilimit property — as in `Stacks.AmpleGlobalGeneration`
`.exists_shortExact_biproduct_of_generatingSections` — and
`CategoryTheory.Limits.biproduct.uniqueUpToIso` then identifies `⨁` with the bicone's vertex.
Whiskering leaves `Bicone.pt` unchanged, so the epimorphism out of it is reused verbatim.

**Epimorphisms are passed explicitly.** `AlgebraicGeometry.Scheme.Modules` is a plain `def` for
`SheafOfModules _` agreeing with it only at default transparency, so an `Epi` arriving as a
hypothesis in one spelling is not found by instance search for the other; the hypotheses are
therefore handed to `CategoryTheory.epi_comp'` and `CategoryTheory.epi_of_epi` rather than left to
synthesis, which is the same discipline as
`Stacks.AmpleEventualGeneration.epi_sigma_map`.

## References

* [Stacks Project, Tag 0885](https://stacks.math.columbia.edu/tag/0885)
* [Stacks Project, Tag 0884](https://stacks.math.columbia.edu/tag/0884)
* [Stacks Project, Tag 087Y](https://stacks.math.columbia.edu/tag/087Y)
* [Stacks Project, Tag 01Q3](https://stacks.math.columbia.edu/tag/01Q3)
* [Stacks Project, Tag 01VK](https://stacks.math.columbia.edu/tag/01VK)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
  Opposite
open Stacks.Cohomology.FormalFunctions (baseIdealSheaf)
open scoped AlgebraicGeometry

universe u

namespace Stacks.Algebraization

attribute [local instance] CategoryTheory.Limits.HasFiniteBiproducts.of_hasFiniteProducts
  Stacks.SheafInternalHom.sheafifyMonoidal
  Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory
  Stacks.SectionRingGeometric.schemePreadditive
  Stacks.SectionRingGeometric.schemeTensorRightAdditive

/-! ### An epimorphism from a finite sum of negative twists -/

variable {X : Scheme.{u}}

section Sum

variable (L : X.Modules) [Stacks.Ample.IsInvertibleModule X L] (d : ℤ)

/-- **From finitely many global sections generating `F ⊗ L ^⊗ d`, an epimorphism
`(L ^⊗ (-d)) ^⊕ t ⟶ F`.**

This is `Stacks.AmpleGlobalGeneration.exists_epi_biproduct_of_epi_free` — the untwisting of the
free presentation, which is the implication (7) ⇒ (8) of [Stacks, Tag 01Q3] with the ampleness
stripped out — transported from the bilimit bicone it produces onto
`Stacks.Algebraization.negativeTwistSum`, the biproduct over `Fin t` that the completion functor
is applied to. The index type is moved by `CategoryTheory.Limits.Bicone.whisker` along an
equivalence `σ.I ≃ Fin t`, and `CategoryTheory.Limits.biproduct.uniqueUpToIso` identifies the
whiskered bicone's vertex with the biproduct. -/
public theorem exists_epi_negativeTwistSum_of_generatingSections (F : X.Modules)
    (σ : (F ⊗ Stacks.Ample.tensorPowModule X L d).GeneratingSections) (hσ : Finite σ.I) :
    ∃ (t : ℕ) (p : negativeTwistSum L d t ⟶ F), Epi p := by
  have := hσ
  have hπ : Epi (σ.π : Stacks.AmpleGlobalGeneration.freeModule X σ.I ⟶
    F ⊗ Stacks.Ample.tensorPowModule X L d) := σ.epi
  obtain ⟨b, hb, p, hp, -⟩ := Stacks.AmpleGlobalGeneration.exists_epi_biproduct_of_epi_free
    L d F (σ.π : Stacks.AmpleGlobalGeneration.freeModule X σ.I ⟶ _) hπ
  obtain ⟨t, ⟨e⟩⟩ := Finite.exists_equiv_fin σ.I
  have hcmp : Epi ((biproduct.uniqueUpToIso
        (fun _ : Fin t => Stacks.Ample.tensorPowModule X L (-d))
        ((b.whiskerIsBilimitIff e.symm).symm hb)).symm.hom ≫ p) :=
    epi_comp' inferInstance hp
  exact ⟨t, _, hcmp⟩

/-- **The same epimorphism, presented as the map assembled from `t` global sections of
`F ⊗ L ^⊗ d`.**

The mapping-out property of the completion of `(L ^⊗ (-d)) ^⊕ t` consumes sections, through
`Stacks.AmpleCharacterization.twistHom`, rather than morphisms out of the summands. Every morphism
`L ^⊗ (-d) ⟶ F` is `twistHom` of a section
(`Stacks.AmpleCharacterization.exists_twistHom_eq`), so the components of the epimorphism above
are read off as sections, and the map assembled from them is that epimorphism again by
`Stacks.Algebraization.negativeTwistSum_hom_ext`. -/
public theorem exists_sections_epi_negativeTwistSumDesc (F : X.Modules)
    (σ : (F ⊗ Stacks.Ample.tensorPowModule X L d).GeneratingSections) (hσ : Finite σ.I) :
    ∃ (t : ℕ) (s₀ : Fin t → Γ(F ⊗ Stacks.Ample.tensorPowModule X L d, ⊤)),
      Epi (negativeTwistSumDesc L d t fun j =>
        Stacks.AmpleCharacterization.twistHom L F d (s₀ j)) := by
  obtain ⟨t, p, hp⟩ := exists_epi_negativeTwistSum_of_generatingSections L d F σ hσ
  choose s₀ hs₀ using fun j : Fin t =>
    Stacks.AmpleCharacterization.exists_twistHom_eq L F d (negativeTwistSumι L d t j ≫ p)
  refine ⟨t, s₀, ?_⟩
  have hdesc : (negativeTwistSumDesc L d t fun j =>
      Stacks.AmpleCharacterization.twistHom L F d (s₀ j)) = p :=
    negativeTwistSum_hom_ext L d t _ _ fun j =>
      (negativeTwistSumι_desc L d t _ j).trans (hs₀ j)
  rw [hdesc]
  exact hp

end Sum

/-! ### The generation statement of Stacks 0885 -/

/-- **Every coherent adic system receives an epimorphism from the completion of a coherent
module** — the generation statement of [Stacks, Tag 0885], for a proper morphism to the spectrum
of a Noetherian ring and an invertible module ample relative to it.

The degree twisted by is `max d₀ n₀`, where `d₀` is the threshold of the lifting step of
`Stacks.Coherent.exists_compatible_sections_whiskerRight_tensorPowModule` — hence that of
[Stacks, Tag 0884] — and `n₀` is the threshold of clause (7) of [Stacks, Tag 01Q3] at the lowest
term `𝓕_0`, which is coherent and so quasi-coherent of finite type. Clause (7) generates
`𝓕_0 ⊗ L ^⊗ d` by `t` global sections; those are turned into an epimorphism
`(L ^⊗ (-d)) ^⊕ t ⟶ 𝓕_0` presented as the map assembled from `t` sections, the sections are lifted
to a family compatible along the whole system, and
`Stacks.Algebraization.descCompletionNegativeTwistSumOfSections` assembles the lifted family into
a morphism out of the completion of `(L ^⊗ (-d)) ^⊕ t`. Its component at the lowest level is the
map the generating family gave, hence an epimorphism, and [Stacks, Tag 087Y]
(`Stacks.Coherent.epi_iff_epi_app_zero`) promotes that to the whole system.

Completeness of `A` for `I` is not used, and is not assumed. -/
@[ega "III 5.2.5" "Surjection step"]
public theorem exists_epi_completionFunctor_of_isRelativelyAmple
    (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    (f : X ⟶ Spec (.of A)) [IsProper f] [AlgebraicGeometry.IsLocallyNoetherian X]
    (L : X.Modules) [Stacks.Ample.IsInvertibleModule X L]
    (hL : Stacks.RelativeAmple.IsRelativelyAmple f L)
    (𝓕 : Stacks.Coherent.CoherentAdicSystems (baseIdealSheaf A I f)) :
    ∃ (P : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf)
      (p : (completionFunctor X (baseIdealSheaf A I f)).obj P ⟶ 𝓕), Epi p := by
  have hamp : Stacks.Ample.IsAmple X L :=
    (Stacks.RelativeAmpleAffineBase.isRelativelyAmple_iff_isAmple f L).mp hL
  have _ : (𝓕.obj.obj (op 0)).IsCoherent := 𝓕.property.1 0
  obtain ⟨n₀, hn₀⟩ := Stacks.AmpleLocalGeneration.isEventuallyGloballyGenerated_of_isAmple L hamp
    (𝓕.obj.obj (op 0)) (isQuasicoherent_of_isCoherent (𝓕.obj.obj (op 0)))
    _root_.SheafOfModules.IsCoherent.isFiniteType
  obtain ⟨d₀, hd₀⟩ :=
    Stacks.Coherent.exists_compatible_sections_whiskerRight_tensorPowModule A I f L hL 𝓕
  obtain ⟨σ, hσ⟩ := hn₀ (max d₀ n₀) (le_max_right d₀ n₀)
  obtain ⟨t, s₀, hepi⟩ :=
    exists_sections_epi_negativeTwistSumDesc L (max d₀ n₀) (𝓕.obj.obj (op 0)) σ hσ
  obtain ⟨s, hs0, hs⟩ := hd₀ (max d₀ n₀) (le_max_left d₀ n₀) t s₀
  refine ⟨negativeTwistSumCoherent L (max d₀ n₀) t,
    descCompletionNegativeTwistSumOfSections L (max d₀ n₀) t (baseIdealSheaf A I f) 𝓕 s hs, ?_⟩
  refine (Stacks.Coherent.epi_iff_epi_app_zero _ _).mpr ?_
  have hfam : (negativeTwistSumDesc L (max d₀ n₀) t fun j =>
        Stacks.AmpleCharacterization.twistHom L (𝓕.obj.obj (op 0)) (max d₀ n₀) (s j 0)) =
      negativeTwistSumDesc L (max d₀ n₀) t fun j =>
        Stacks.AmpleCharacterization.twistHom L (𝓕.obj.obj (op 0)) (max d₀ n₀) (s₀ j) :=
    congrArg (negativeTwistSumDesc L (max d₀ n₀) t) (funext fun j =>
      congrArg (Stacks.AmpleCharacterization.twistHom L (𝓕.obj.obj (op 0)) (max d₀ n₀)) (hs0 j))
  have hzero : Epi (completionProjection X (baseIdealSheaf A I f)
      (negativeTwistSumCoherent L (max d₀ n₀) t) 0 ≫
        (descCompletionNegativeTwistSumOfSections L (max d₀ n₀) t (baseIdealSheaf A I f)
          𝓕 s hs).hom.app (op 0)) := by
    rw [completionProjection_descCompletionNegativeTwistSumOfSections, hfam]
    exact hepi
  exact epi_of_epi (completionProjection X (baseIdealSheaf A I f)
    (negativeTwistSumCoherent L (max d₀ n₀) t) 0) _

end Stacks.Algebraization

end
