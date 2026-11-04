module

public import StacksFrontier.AlgebraicGeometry.DerivedPushforward.IsoTransport
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.PushforwardCoherence.DepthDimensionCriterionZeroLocus
public import StacksFrontier.AlgebraicGeometry.Properties.ExtendFiniteType.FiniteModule
public import StacksCore.Tactic.StacksAttribute

/-!
# A coherent module on an open of an affine scheme comes from a finite module on the base

Let `T` be an affine locally Noetherian scheme, let `g : W ⟶ T` be an open immersion and let `ℱ`
be a coherent `𝒪_W`-module. Writing `A = Γ(T, ⊤)`, this file produces an ideal `I ⊆ A` and a
finite `A`-module `M` such that the higher direct images `R^p g_* ℱ` are coherent exactly when
the higher direct images of `M̃|_{Spec A ∖ V(I)}` along the inclusion of that open are.

## Main results

* `AlgebraicGeometry.isCoherent_rightDerived_iff_of_tilde_restrict_iso` — the coherence
  comparison across a given isomorphism `M̃|_W ≅ ℱ`.
* `AlgebraicGeometry.exists_ideal_eq_finiteModule_tilde_restrict_iso` — a coherent module on an
  open `W = Spec A ∖ V(I)` of `Spec A` is `M̃|_W` for a finite `A`-module `M`.
* `AlgebraicGeometry.exists_ideal_finiteModule_isCoherent_rightDerived_iff_opens` — at an
  arbitrary open of a spectrum.
* `AlgebraicGeometry.exists_ideal_finiteModule_isCoherent_rightDerived_iff_affine` — along an
  open immersion into an arbitrary affine locally Noetherian scheme.
* `Stacks.LocalCohomologySequence.exists_ideal_finiteModule_forall_lt_depth_add_height_iff`
  — the affine case of [Stacks, Tag 0BJY] for an arbitrary coherent module.

## References

* [Stacks Project, Tag 0BJY](https://stacks.math.columbia.edu/tag/0BJY)
* [Stacks Project, Tag 0BJR](https://stacks.math.columbia.edu/tag/0BJR)
* [Stacks Project, Tag 0BK0](https://stacks.math.columbia.edu/tag/0BK0)
* [Stacks Project, Tag 01Y6](https://stacks.math.columbia.edu/tag/01Y6)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open Stacks.AlgebraicGeometry.CoherentDevissage (isCoherent_of_iso)
open Stacks.AlgebraicGeometry.DerivedPushforward (isCoherent_rightDerived_transport_iff)
open Stacks.AlgebraicGeometry.FiniteDirectImageCoherent (isCoherent_pushforward_of_isFinite)

universe u

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry

/-! ### At an arbitrary open of a spectrum, keeping the isomorphism -/

/-- The ring of global sections of an affine locally Noetherian scheme is Noetherian. -/
private instance isNoetherianRing_globalSections_top {T : Scheme.{u}} [IsAffine T]
    [IsLocallyNoetherian T] : IsNoetherianRing Γ(T, (⊤ : T.Opens)) :=
  IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top T⟩

/-- **Coherence of the higher direct images is read across an isomorphism of the modules.** For
`e : M̃|_W ≅ ℱ` on an open `W` of `Spec A`, the higher direct images of the two modules along
the inclusion of `W` are coherent together. -/
public theorem isCoherent_rightDerived_iff_of_tilde_restrict_iso {A : CommRingCat.{u}}
    (W : (Spec A).Opens) (G : W.toScheme.Modules) (M : ModuleCat.{u} A)
    (e : (tilde M).restrict W.ι ≅ G) (p : ℕ) :
    (((Scheme.Modules.pushforward W.ι).rightDerived p).obj
        ((tilde M).restrict W.ι)).IsCoherent ↔
      (((Scheme.Modules.pushforward W.ι).rightDerived p).obj G).IsCoherent :=
  ⟨fun _ => isCoherent_of_iso (((Scheme.Modules.pushforward W.ι).rightDerived p).mapIso e.symm),
    fun _ => isCoherent_of_iso (((Scheme.Modules.pushforward W.ι).rightDerived p).mapIso e)⟩

/-- **A coherent module on an open `W` of `Spec A` is `M̃|_W` for a finite `A`-module `M`, and
`W` is the complement of a vanishing locus.** For a Noetherian ring `A`, an open `W` of `Spec A`
and a coherent module `ℱ` on `W`, there are an ideal `I` with `Spec A ∖ V(I) = W` and a finite
`A`-module `M` with `M̃|_W ≅ ℱ`. -/
public theorem exists_ideal_eq_finiteModule_tilde_restrict_iso {A : CommRingCat.{u}}
    [IsNoetherianRing A] (W : (Spec A).Opens) (G : W.toScheme.Modules) [G.IsCoherent] :
    ∃ I : Ideal A, zeroLocusCompl I = W ∧
      ∃ M : ModuleCat.{u} A, Module.Finite A M ∧
        Nonempty ((tilde M).restrict W.ι ≅ G) := by
  obtain ⟨I, hI⟩ := (PrimeSpectrum.isClosed_iff_zeroLocus_ideal ((W : Set (Spec A)))ᶜ).mp
    W.isOpen.isClosed_compl
  have hW : zeroLocusCompl I = W := Opens.ext <| by
    change (PrimeSpectrum.zeroLocus (I : Set (ToType A)))ᶜ = _
    rw [← hI]
    exact compl_compl _
  refine ⟨I, hW, ?_⟩
  subst hW
  exact exists_finiteModule_tilde_restrict_zeroLocusCompl I G

/-! ### At an arbitrary open of a spectrum -/

/-- **A coherent module on an open of `Spec A` is `M̃` restricted to the complement of a
vanishing locus, for a finite `A`-module `M`.** The open `W` is the complement of the vanishing
locus of an ideal `I`, and the higher direct images of the two modules along the inclusion of
that open are coherent together. -/
public theorem exists_ideal_finiteModule_isCoherent_rightDerived_iff_opens
    {A : CommRingCat.{u}} [IsNoetherianRing A] (W : (Spec A).Opens)
    (G : W.toScheme.Modules) [G.IsCoherent] :
    ∃ (I : Ideal A) (M : ModuleCat.{u} A), Module.Finite A M ∧
      ∀ p : ℕ,
        ((((Scheme.Modules.pushforward (zeroLocusCompl I).ι).rightDerived p).obj
            ((tilde M).restrict (zeroLocusCompl I).ι)).IsCoherent ↔
          (((Scheme.Modules.pushforward W.ι).rightDerived p).obj G).IsCoherent) := by
  obtain ⟨I, hW, M, hMfin, ⟨e⟩⟩ := exists_ideal_eq_finiteModule_tilde_restrict_iso W G
  subst hW
  exact ⟨I, M, hMfin, isCoherent_rightDerived_iff_of_tilde_restrict_iso _ G M e⟩

/-! ### Along an open immersion into an affine scheme -/

/-- **A coherent module on an open subscheme of an affine locally Noetherian scheme comes from a
finite module on the base.** For an open immersion `g : W ⟶ T` with `T` affine and locally
Noetherian and a coherent `𝒪_W`-module `ℱ`, there are an ideal `I ⊆ Γ(T, ⊤)` and a finite
`Γ(T, ⊤)`-module `M` whose higher direct images along the inclusion of `Spec Γ(T, ⊤) ∖ V(I)` are
coherent exactly when those of `ℱ` along `g` are. -/
public theorem exists_ideal_finiteModule_isCoherent_rightDerived_iff_affine
    {W T : Scheme.{u}} [IsAffine T] [IsLocallyNoetherian T] (g : W ⟶ T) [IsOpenImmersion g]
    (F : W.Modules) [F.IsCoherent] :
    ∃ (I : Ideal Γ(T, (⊤ : T.Opens))) (M : ModuleCat.{u} Γ(T, (⊤ : T.Opens))),
      Module.Finite Γ(T, (⊤ : T.Opens)) M ∧
      ∀ p : ℕ,
        ((((Scheme.Modules.pushforward (zeroLocusCompl I).ι).rightDerived p).obj
            ((tilde M).restrict (zeroLocusCompl I).ι)).IsCoherent ↔
          (((Scheme.Modules.pushforward g).rightDerived p).obj F).IsCoherent) := by
  have hGcoh : ((Scheme.Modules.pushforward
      (Scheme.Hom.isoOpensRange (g ≫ T.isoSpec.hom)).hom).obj F).IsCoherent :=
    isCoherent_pushforward_of_isFinite (Scheme.Hom.isoOpensRange (g ≫ T.isoSpec.hom)).hom F
  obtain ⟨I, M, hMfin, hiff⟩ := exists_ideal_finiteModule_isCoherent_rightDerived_iff_opens
    (Scheme.Hom.opensRange (g ≫ T.isoSpec.hom))
    ((Scheme.Modules.pushforward (Scheme.Hom.isoOpensRange (g ≫ T.isoSpec.hom)).hom).obj F)
  refine ⟨I, M, hMfin, fun p => (hiff p).trans ?_⟩
  exact (isCoherent_rightDerived_transport_iff g
    (Scheme.Hom.opensRange (g ≫ T.isoSpec.hom)).ι
    (Scheme.Hom.isoOpensRange (g ≫ T.isoSpec.hom)) T.isoSpec
    (Scheme.Hom.isoOpensRange_hom_ι (g ≫ T.isoSpec.hom)) p F).symm

end AlgebraicGeometry

namespace Stacks.LocalCohomologySequence

/-! ### The affine case of Tag 0BJY for an arbitrary coherent module -/

/-- **The affine case of [Stacks, Tag 0BJY] for an arbitrary coherent module.** Let `T` be an
affine locally Noetherian scheme with `A = Γ(T, ⊤)` universally catenary, let `g : W ⟶ T` be an
open immersion and let `ℱ` be a coherent `𝒪_W`-module. Then there are an ideal `I ⊆ A` and a
finite `A`-module `M` such that, granted Serre's condition `(Sₙ)` on the formal fibres of
`𝒪_{Spec A, q}` for every prime `q ⊇ I`, the higher direct images `R^p g_* ℱ` are coherent for
`0 ≤ p < n` exactly when `depth_{A_𝔭}(M_𝔭) + dim((A/𝔭)_𝔮) > n` for every pair of primes
`𝔭 ⊆ 𝔮` of `A` with `𝔭 ∉ V(I)`, `𝔮 ∈ V(I)` and `M_𝔭 ≠ 0`. -/
public theorem exists_ideal_finiteModule_forall_lt_depth_add_height_iff
    {W T : Scheme.{u}} [IsAffine T] [IsLocallyNoetherian T] (g : W ⟶ T) [IsOpenImmersion g]
    (F : W.Modules) [F.IsCoherent] (n : ℕ)
    (hA : Ring.IsUniversallyCatenary (ToType Γ(T, (⊤ : T.Opens)))) :
    ∃ (I : Ideal Γ(T, (⊤ : T.Opens))) (M : ModuleCat.{u} Γ(T, (⊤ : T.Opens))),
      Module.Finite Γ(T, (⊤ : T.Opens)) M ∧
      ((∀ q : PrimeSpectrum (ToType Γ(T, (⊤ : T.Opens))), I ≤ q.asIdeal →
          Stacks.LocalCohomology.FormalFibersHavePropertySk
            (Localization.AtPrime q.asIdeal) n) →
        ((∀ p q : PrimeSpectrum (ToType Γ(T, (⊤ : T.Opens))), ¬ I ≤ p.asIdeal →
            I ≤ q.asIdeal → p.asIdeal ≤ q.asIdeal →
            Nontrivial (LocalizedModule p.asIdeal.primeCompl M) →
            (n : ℕ∞) < Module.depth (Localization.AtPrime p.asIdeal)
                  (IsLocalRing.maximalIdeal (Localization.AtPrime p.asIdeal))
                  (LocalizedModule p.asIdeal.primeCompl M) +
                (q.asIdeal.map (Ideal.Quotient.mk p.asIdeal)).height) ↔
          ∀ p : ℕ, p < n →
            (((Scheme.Modules.pushforward g).rightDerived p).obj F).IsCoherent)) := by
  obtain ⟨I, M, hMfin, hiff⟩ :=
    AlgebraicGeometry.exists_ideal_finiteModule_isCoherent_rightDerived_iff_affine g F
  exact ⟨I, M, hMfin, fun hformal =>
    (forall_lt_depth_add_height_iff_forall_isCoherent_rightDerivedZeroLocus I M hA n
      hformal).trans (forall_congr' fun p => imp_congr_right fun _ => hiff p)⟩

end Stacks.LocalCohomologySequence

end
