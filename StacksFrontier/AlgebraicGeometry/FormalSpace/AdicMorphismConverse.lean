module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.AdicMorphismCharts
public import StacksFrontier.AlgebraicGeometry.FormalSpace.ColimitOfAlgebraicSpaces
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionFiniteType
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CountablePresentingRing
public import StacksFrontier.AlgebraicGeometry.FormalSpace.EtaleCompletionCover
public import StacksFrontier.AlgebraicGeometry.FormalSpace.EtaleCompletionRepresentable
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RepresentableOfAffineEtaleCover
public import StacksFrontier.AlgebraicGeometry.FormalSpace.SpectrumFullyFaithful
public import StacksFrontier.AlgebraicGeometry.FormalSpace.TautFormalSpectrumRepresentable
public import StacksFrontier.CategoryTheory.Sites.QuasiCompact.CoveringSetOfObjects
public import StacksFrontier.RingTheory.Rig.ClosedPoint
public import Mathlib.Tactic.TFAE

/-!
# Adic morphisms: the chart condition implies representability (Section 0AQ2)

Let `S` be a scheme contained in a big fppf site `B` and let `f : X ⟶ Y` be a morphism of
locally adic\* formal algebraic spaces over `S`. Formal Spaces, **Section 0AQ2** asserts that
the following are equivalent:

1. `f` is representable by algebraic spaces;
2. for every commutative square with `U`, `V` affine formal algebraic spaces and `U ⟶ X`,
   `V ⟶ Y` representable by algebraic spaces and étale, the morphism `U ⟶ V` corresponds to an
   adic map in `WAdm^{adic*}` (equivalently a taut one, by the footnote).

The implication (1) ⟹ (2) is
`AlgebraicGeometry.FormalSpace.isAdicOnEveryAffineEtaleDiagram_of_isAdicMorphism'`. This file
proves (2) ⟹ (1) and assembles the equivalence.

## Main results

* `AlgebraicGeometry.FormalSpace.exists_cover_pullback_of_isAdicOnEveryAffineEtaleDiagram`: over
  a pair of charts `U ⟶ X`, `V ⟶ Y` presented by rings of `WAdm^{adic*}`, the fibre product
  `V ×_Y U` is covered by affine formal algebraic spaces representable étale over `X` whose map
  to `Y` is representable by algebraic spaces.
* `AlgebraicGeometry.FormalSpace.isAdicMorphism_of_isAdicOnEveryAffineEtaleDiagram`: **Section
  0AQ2**, condition (2) implies condition (1).
* `AlgebraicGeometry.FormalSpace.isAdicMorphism_tfae`: **Section 0AQ2**, the equivalence.

## Implementation notes

The source deduces the equivalence from Stacks 0ANK. The route here is direct. Fix charts
`U = Spf A ⟶ X` and `V = Spf R ⟶ Y` of the given atlases, with `A` and `R` in `WAdm^{adic*}`.
The fibre product `V ×_Y U` is representable étale over `Spf A`, so it is covered by formal
spectra `W = Spf C^` of completions of étale `A`-algebras `C` (Stacks 0AN8 and 04D1), which are
again in `WAdm^{adic*}`. Each `W` sits in a chart square over `f` with upper horizontal map
`W ⟶ V`; that map is `Spf` of a continuous homomorphism `R ⟶ C^` (Stacks 0AN0), which is adic
by condition (2), hence taut (Stacks 0GBS), hence its formal spectrum is representable by
algebraic spaces (Stacks 0AN5). So every member of the resulting affine étale covering of `X`
maps representably to `Y`, and representability by algebraic spaces descends along such a
covering (Stacks 0AN4, the implication from (5) to (1)).

Composing the coverings of the fibre products `V_j ×_Y U_i` over all pairs of charts gives an
affine étale covering of `X`; joint surjectivity is checked one level at a time.

## References

* [Stacks Project, Tag 0AQ2](https://stacks.math.columbia.edu/tag/0AQ2)
* [Stacks Project, Tag 0AN0](https://stacks.math.columbia.edu/tag/0AN0)
* [Stacks Project, Tag 0AN4](https://stacks.math.columbia.edu/tag/0AN4)
* [Stacks Project, Tag 0AN5](https://stacks.math.columbia.edu/tag/0AN5)
* [Stacks Project, Tag 0AN8](https://stacks.math.columbia.edu/tag/0AN8)
* [Stacks Project, Tag 0ANK](https://stacks.math.columbia.edu/tag/0ANK)
* [Stacks Project, Tag 0GBS](https://stacks.math.columbia.edu/tag/0GBS)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.FormalSpace

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- A topological ring of `WAdm^{adic*}` in the sense of `TopologicalRing.IsAdicStar` is one in the
sense of `AlgebraicGeometry.FormalSpace.IsCountablyAdicStar`: its finitely generated ideal of
definition defines its topology, the topology being adic. -/
theorem isCountablyAdicStar_of_isAdicStar {R : Type u} [CommRing R] [TopologicalSpace R]
    [IsTopologicalRing R] [IsLinearTopology R R] (hR : TopologicalRing.IsAdicStar R) :
    IsCountablyAdicStar R := by
  obtain ⟨I, hI, hfg⟩ := hR.2
  obtain ⟨J, -, hJ⟩ := hR.1.1
  exact ⟨TopologicalRing.isCountablyWeaklyAdmissible_of_isAdicStar hR, I, hfg,
    (Rig.isIdealOfDefinition_iff_isAdic ⟨J, hJ⟩ I).mp hI⟩

/-- A family of jointly surjective families over the members of a jointly surjective family
composes to a jointly surjective family. -/
theorem isLocallySurjective_sigmaDesc_comp_sigma {Z : FppfSheaf B S hS} {J : Type (u + 1)}
    {P : J → FppfSheaf B S hS} (p : ∀ j, P j ⟶ Z)
    (hp : letI : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) :=
      Sheaf.instHasColimitsOfSize; Sheaf.IsLocallySurjective (Sigma.desc p))
    {K : J → Type (u + 1)} {R : (x : Σ j, K j) → FppfSheaf B S hS} (q : ∀ x, R x ⟶ P x.1)
    (hq : letI : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) :=
      Sheaf.instHasColimitsOfSize;
      ∀ j, Sheaf.IsLocallySurjective (Sigma.desc fun k : K j ↦ q ⟨j, k⟩)) :
    letI : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
    Sheaf.IsLocallySurjective (Sigma.desc fun x : Σ j, K j ↦ q x ≫ p x.1) := by
  let : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
  have h1 := Sheaf.isLocallySurjective_sigmaDesc_sigma q hq
  have hfac : (Sigma.desc fun x : Σ j, K j ↦ q x ≫ Sigma.ι P x.1) ≫ Sigma.desc p =
      Sigma.desc fun x : Σ j, K j ↦ q x ≫ p x.1 :=
    Sigma.hom_ext _ _ fun x ↦ by simp
  rw [← hfac]
  have := (Sheaf.isLocallySurjective_iff_epi _).1 h1
  have := (Sheaf.isLocallySurjective_iff_epi _).1 hp
  exact (Sheaf.isLocallySurjective_iff_epi _).2 (epi_comp _ _)

/-- **The charts over one pair of charts.** Let `u : U ⟶ X` and `v : V ⟶ Y` be representable étale
charts by formal spectra of rings of `WAdm^{adic*}`, and let `f : X ⟶ Y` satisfy the chart
condition of Section 0AQ2. Then the fibre product `V ×_Y U` is covered, jointly surjectively, by
affine formal algebraic spaces `W` whose composite map to `X` is representable étale and whose
composite map to `Y` is representable by algebraic spaces. -/
theorem exists_cover_pullback_of_isAdicOnEveryAffineEtaleDiagram {X Y U V : FppfSheaf B S hS}
    (f : X ⟶ Y) (hf : IsAdicOnEveryAffineEtaleDiagram B S hS f)
    (u : U ⟶ X) (hu : IsRepresentableEtale B S hS u)
    (v : V ⟶ Y) (hv : IsRepresentableEtale B S hS v)
    (hV : IsAffineFormalAlgebraicSpace B S hS V)
    {A : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A]
    (hA : IsCountablyAdicStar A) (D : QuotientSystem B S hS A) (eU : U ≅ formalSpectrum D)
    {R : Type u} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [IsLinearTopology R R]
    (hR : IsCountablyAdicStar R) (D' : QuotientSystem B S hS R) (eV : V ≅ formalSpectrum D') :
    letI : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
    ∃ (K : Type (u + 1)) (W : K → FppfSheaf B S hS) (w : ∀ k, W k ⟶ pullback v (u ≫ f)),
      (∀ k, IsAffineFormalAlgebraicSpace B S hS (W k)) ∧
      (∀ k, IsRepresentableEtale B S hS (w k ≫ pullback.snd v (u ≫ f) ≫ u)) ∧
      (∀ k, Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS
        ((w k ≫ pullback.snd v (u ≫ f) ≫ u) ≫ f).hom) ∧
      Sheaf.IsLocallySurjective (Sigma.desc w) := by
  let : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
  have hAw : TopologicalRing.IsWeaklyAdmissible A := hA.1.1
  have hRw : TopologicalRing.IsWeaklyAdmissible R := hR.1.1
  obtain ⟨I, hIfg, hIadic⟩ := hA.2
  have hD : D.HasLargeSite :=
    QuotientSystem.hasLargeSite_of_isCountablyGenerated B S hS D hAw hA.1.2
  have hD' : D'.HasLargeSite :=
    QuotientSystem.hasLargeSite_of_isCountablyGenerated B S hS D' hRw hR.1.2
  have hφ : IsRepresentableEtale B S hS (pullback.snd v (u ≫ f) ≫ eU.hom) :=
    IsRepresentableEtale.comp B S hS (isRepresentableEtale_pullback_snd B S hS v (u ≫ f) hv)
      (isRepresentableEtale_of_isIso B S hS eU.hom)
  obtain ⟨K, C, _, fk, hfk, Q, g, hg, w, hw, hsurj⟩ :=
    exists_completion_cover_of_isRepresentableEtale B S hS hAw hIfg hIadic D hD _ hφ
  have hft : ∀ k, let : Algebra A (C k) := (fk k).toAlgebra; Algebra.FiniteType A (C k) :=
    fun k ↦ by
      let : Algebra A (C k) := (fk k).toAlgebra
      have : Algebra.Etale A (C k) := hfk k
      infer_instance
  have hQ : ∀ k, (Q k).HasLargeSite := fun k ↦
    hasLargeSite_completionOver_of_finiteType B S hS (fk k) (hft k) hD (Q k)
  have hCw : ∀ k, TopologicalRing.IsWeaklyAdmissible (TopologicalRing.CompletionOver (fk k)) :=
    fun k ↦ TopologicalRing.completionOver_isWeaklyAdmissible (fk k) hAw
  have hsnd : ∀ k, w k ≫ pullback.snd v (u ≫ f) = formalSpectrumMap hAw (g k) ≫ eU.inv :=
    fun k ↦ by rw [← hw k]; simp
  have het : ∀ k, IsRepresentableEtale B S hS (w k ≫ pullback.snd v (u ≫ f) ≫ u) := fun k ↦ by
    rw [← Category.assoc, hsnd k, Category.assoc]
    exact IsRepresentableEtale.comp B S hS
      (isRepresentableEtale_formalSpectrumMap_of_etale B S hS hAw D hD (fk k) (hfk k) (Q k) (g k)
        (hg k))
      (IsRepresentableEtale.comp B S hS (isRepresentableEtale_of_isIso B S hS eU.inv) hu)
  refine ⟨K, fun k ↦ formalSpectrum (Q k), w, fun k ↦
    isAffineFormalAlgebraicSpace_formalSpectrum (hCw k) (Q k) (hQ k), het, fun k ↦ ?_, hsurj⟩
  -- the chart square over `f`
  set t : formalSpectrum (Q k) ⟶ V := w k ≫ pullback.fst v (u ≫ f) with ht
  have hsq : (w k ≫ pullback.snd v (u ≫ f) ≫ u) ≫ f = t ≫ v := by
    simp only [ht, Category.assoc]
    rw [← pullback.condition]
  obtain ⟨γ, hγ, -⟩ := existsUnique_continuousHom_formalSpectrumMap_eq hRw (hCw k) (t ≫ eV.hom)
  have htγ : t = (Iso.refl _).hom ≫ formalSpectrumMap hRw γ ≫ eV.inv := by
    rw [hγ]; simp
  have hadic : RingHom.IsAdic γ.toRingHom :=
    hf (formalSpectrum (Q k)) V _ v t
      (isAffineFormalAlgebraicSpace_formalSpectrum (hCw k) (Q k) (hQ k)) hV (het k) hv hsq
      R (TopologicalRing.CompletionOver (fk k)) hR (isCountablyAdicStar_completionOver hA (fk k))
      hRw D' (Q k)
      (Iso.refl _) eV γ htγ
  have hrep : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS
      (formalSpectrumMap hRw γ).hom :=
    isRepresentableByAlgebraicSpacesULift_formalSpectrumMap_of_isTaut B S hS hRw (hCw k) D' (Q k)
      (hQ k) γ (RingHom.isTaut_of_isAdic γ.toRingHom hadic)
  rw [hsq]
  have htrep : IsAdicMorphism B S hS t := by
    rw [htγ, Iso.refl_hom, Category.id_comp]
    exact IsAdicMorphism.comp B S hS _ _ hrep (isAdicMorphism_of_isIso B S hS eV.inv)
  exact IsAdicMorphism.comp B S hS t v htrep hv.1

/-- **Section 0AQ2, condition (2) implies condition (1).** Let `f : X ⟶ Y` be a morphism of
locally adic\* formal algebraic spaces over `S` such that for every commutative square with `U`,
`V` affine formal algebraic spaces and `U ⟶ X`, `V ⟶ Y` representable étale, the map `U ⟶ V`
corresponds to an adic map of `WAdm^{adic*}`. Then `f` is representable by algebraic spaces,
that is, adic in the sense of Definition 0AQ3. -/
theorem isAdicMorphism_of_isAdicOnEveryAffineEtaleDiagram {X Y : FppfSheaf B S hS} (f : X ⟶ Y)
    (hX : IsLocallyAdicStar B S hS X) (hY : IsLocallyAdicStar B S hS Y)
    (hf : IsAdicOnEveryAffineEtaleDiagram B S hS f) : IsAdicMorphism B S hS f := by
  classical
  let : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
  obtain ⟨hXf, I, U, a, hUaff, hUet, hUsurj, hUstar⟩ := hX
  obtain ⟨hYf, J, V, b, hVaff, hVet, hVsurj, hVstar⟩ := hY
  have hcharts : ∀ (i : I) (j : J), ∃ (K : Type (u + 1)) (W : K → FppfSheaf B S hS)
      (w : ∀ k, W k ⟶ pullback (b j) (a i ≫ f)),
      (∀ k, IsAffineFormalAlgebraicSpace B S hS (W k)) ∧
      (∀ k, IsRepresentableEtale B S hS (w k ≫ pullback.snd (b j) (a i ≫ f) ≫ a i)) ∧
      (∀ k, Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS
        ((w k ≫ pullback.snd (b j) (a i ≫ f) ≫ a i) ≫ f).hom) ∧
      Sheaf.IsLocallySurjective (Sigma.desc w) := by
    intro i j
    obtain ⟨-, A, _, _, _, _, hApres, hAadic, hAfg⟩ := hUstar i
    obtain ⟨-, R, _, _, _, _, hRpres, hRadic, hRfg⟩ := hVstar j
    exact exists_cover_pullback_of_isAdicOnEveryAffineEtaleDiagram B S hS f hf (a i) (hUet i)
      (b j) (hVet j) (hVaff j) (isCountablyAdicStar_of_isAdicStar ⟨hAadic, hAfg⟩)
      hApres.2.some.quotientSystem hApres.2.some.formalSpectrumIso
      (isCountablyAdicStar_of_isAdicStar ⟨hRadic, hRfg⟩)
      hRpres.2.some.quotientSystem hRpres.2.some.formalSpectrumIso
  choose K W w hWaff hWet hWrep hWsurj using hcharts
  refine isRepresentable_of_affineEtaleCover_of_isRepresentable_comp B S hS f hXf hYf
    (I := Σ i, Σ j, K i j) (fun x ↦ W x.1 x.2.1 x.2.2)
    (fun x ↦ w x.1 x.2.1 x.2.2 ≫ pullback.snd (b x.2.1) (a x.1 ≫ f) ≫ a x.1)
    ⟨fun x ↦ hWaff _ _ _, fun x ↦ hWet _ _ _, ?_⟩ fun x ↦ hWrep _ _ _
  -- joint surjectivity: two flattenings
  have hstage : ∀ i, Sheaf.IsLocallySurjective (Sigma.desc fun y : Σ j, K i j ↦
      w i y.1 y.2 ≫ pullback.snd (b y.1) (a i ≫ f)) := fun i ↦
    isLocallySurjective_sigmaDesc_comp_sigma B S hS (fun j ↦ pullback.snd (b j) (a i ≫ f))
      (Sheaf.isLocallySurjective_sigmaDesc_pullback_snd (a i ≫ f) b hVsurj)
      (fun y : Σ j, K i j ↦ w i y.1 y.2) (fun j ↦ hWsurj i j)
  have h := isLocallySurjective_sigmaDesc_comp_sigma B S hS a hUsurj
    (K := fun i ↦ Σ j, K i j) (R := fun x ↦ W x.1 x.2.1 x.2.2)
    (fun x ↦ w x.1 x.2.1 x.2.2 ≫ pullback.snd (b x.2.1) (a x.1 ≫ f)) hstage
  simpa only [Category.assoc] using h

/-- **Section 0AQ2.** Let `f : X ⟶ Y` be a morphism of locally adic\* formal algebraic spaces
over `S`. The following are equivalent:

1. `f` is representable by algebraic spaces, that is, `f` is an adic morphism in the sense of
   Definition 0AQ3;
2. for every commutative square
   ```
   U ⟶ V
   ↓     ↓
   X ⟶ Y
   ```
   with `U` and `V` affine formal algebraic spaces and `U ⟶ X`, `V ⟶ Y` representable by
   algebraic spaces and étale, the morphism `U ⟶ V` corresponds to an adic map in
   `WAdm^{adic*}`;
3. the same with "adic" replaced by "taut", which is the footnote of the section. -/
@[stacks 0AQ2 "the equivalence of conditions (1) and (2) of the section for a morphism of \
locally adic* formal algebraic spaces, together with the footnote reading (2) with taut maps"]
theorem isAdicMorphism_tfae {X Y : FppfSheaf B S hS} (f : X ⟶ Y)
    (hX : IsLocallyAdicStar B S hS X) (hY : IsLocallyAdicStar B S hS Y) :
    List.TFAE
      [ IsAdicMorphism B S hS f,
        IsAdicOnEveryAffineEtaleDiagram B S hS f,
        IsTautOnEveryAffineEtaleDiagramAdicStar B S hS f ] := by
  tfae_have 1 → 2 := isAdicOnEveryAffineEtaleDiagram_of_isAdicMorphism' B S hS f
  tfae_have 2 → 1 := isAdicMorphism_of_isAdicOnEveryAffineEtaleDiagram B S hS f hX hY
  tfae_have 2 ↔ 3 := isAdicOnEveryAffineEtaleDiagram_iff_isTautAdicStar B S hS f
  tfae_finish

end AlgebraicGeometry.FormalSpace

end
