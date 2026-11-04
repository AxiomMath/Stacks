module

public import StacksFrontier.AlgebraicGeometry.DeRham.SmoothSpectralSequenceOfStepSquares
public import StacksFrontier.AlgebraicGeometry.DeRham.SmoothGradedPieceStepSquaresProof
public import StacksFrontier.AlgebraicGeometry.DeRham.SmoothFirstPageFlat
public import StacksFrontier.AlgebraicGeometry.DeRham.SmoothFirstPageFlatIdentification
public import StacksFrontier.Topology.Sheaves.Cohomology.FilteredComplexSpectralSequence.PushforwardFirstDifferentialDerived

/-!
# The spectral sequence of a smooth morphism, with its first differential

Let `f : X ⟶ Y` be a quasi-compact, quasi-separated and smooth morphism of schemes over a base
`S`, with `g : Y ⟶ S` the structure morphism of the target. [Stacks, Tag 0FMM] produces a
spectral sequence with `E_1^{p, q} = H^q(Ω^p_{Y/S} ⊗^𝐋_{𝒪_Y} Rf_*Ω^•_{X/Y})`. This file names the
spectral sequence and its first-page isomorphisms, and describes its first differential, the
subject of [Stacks, Tag 0FMN].

## Main definitions

* `Stacks.DeRhamSmooth.deRhamSmoothResolution`: a chosen filtered K-injective resolution `J` of
  the filtered complex `Ω^•_{X/S}` of Section 0FMK.
* `Stacks.DeRhamSmooth.deRhamSmoothSpectralSequence`: the spectral sequence of 0FMM, starting at
  the first page: the spectral sequence of the filtered complex `f_*J`.
* `Stacks.DeRhamSmooth.higherDirectImageGradedPieceFirstPageIso`: the identification
  `R^{p + q}f_*gr^pΩ^•_{X/S} ≅ H^q(Ω^p_{Y/S} ⊗^𝐋 Rf_*Ω^•_{X/Y})` of Section 0FMK followed by the
  projection formula of Tag 0FML, as an isomorphism.
* `Stacks.DeRhamSmooth.deRhamSmoothGradedHomologyIso`:
  `H^{p + q}(f_*gr^pJ) ≅ H^q(Ω^p_{Y/S} ⊗^𝐋 Rf_*Ω^•_{X/Y})`.
* `Stacks.DeRhamSmooth.deRhamSmoothFirstPageIso`: `E_1^{p, q} ≅ deRhamFirstPage f g p q`.
* `Stacks.DeRhamSmooth.deRhamFirstPageDifferential`: the map
  `H^q(Ω^p ⊗^𝐋 Rf_*Ω^•_{X/Y}) ⟶ H^q(Ω^{p + 1} ⊗^𝐋 Rf_*Ω^•_{X/Y})`: the connecting morphism, in
  the cohomology of `f_*J`, of `0 ⟶ gr^{p + 1}J ⟶ F^pJ/F^{p + 2}J ⟶ gr^pJ ⟶ 0`, read through
  `deRhamSmoothGradedHomologyIso`.
* `Stacks.DeRhamSmooth.deRhamFirstPageFlatDifferential` and
  `Stacks.DeRhamSmooth.deRhamSmoothFirstPageFlatIso`: the first differential, and the first page,
  in the flat case, between the modules `Ω^p_{Y/S} ⊗_{𝒪_Y} ℋ^q_dR(X/Y)`, read through
  `higherDirectImageGradedPieceFlatIso`.

## Main results

* `Stacks.DeRhamSmooth.deRhamSmoothSpectralSequence_d`: **the first differential** of the
  spectral sequence of 0FMM is `deRhamFirstPageDifferential`; `deRhamSmoothSpectralSequence_d_flat`
  in the flat case.
* `Stacks.DeRhamSmooth.deRhamFirstPageDifferential_eq_derived`: `deRhamFirstPageDifferential` is
  `R^{p + q}f_*` of the connecting morphism `gr^p ⟶ gr^{p + 1}[1]` of the graded short exact
  sequence of `Ω^•_{X/S}` in the derived category, with no resolution.
* `Stacks.DeRhamSmooth.deRhamFirstPageDifferential_comp`,
  `Stacks.DeRhamSmooth.deRhamFirstPageFlatDifferential_comp`: `d_1 ∘ d_1 = 0`.
* `Stacks.DeRhamSmooth.deRhamSmoothSpectralSequence_isBounded`,
  `Stacks.DeRhamSmooth.deRhamSmoothSpectralSequence_abutsTo`: the spectral sequence is bounded and
  abuts to `R^{p + q}f_*Ω^•_{X/S}` (Tag 0FMM for this named spectral sequence).

## References

* [Stacks Project, Tag 0FMM](https://stacks.math.columbia.edu/tag/0FMM)
* [Stacks Project, Tag 0FMN](https://stacks.math.columbia.edu/tag/0FMN)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry
open RingedSpaceModuleAdjunction Stacks.Cohomology.FilteredComplex Stacks.DeRhamDirectImage

universe u

attribute [local instance 2000] HasDerivedCategory.standard
attribute [-instance] Stacks.Cohomology.SpectralLimit.hasSheafifyOpensMax


namespace Stacks.DeRhamSmooth

variable {X Y S : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S)

/-- **The first page of 0FMM, from the graded pieces**: for `p ≥ 0`, written `p = k`, the graded
piece `gr^kΩ^•_{X/S}` is `f^{-1}Ω^k_{Y/S}[-k] ⊗ Ω^•_{X/Y}` (Section 0FMK,
`gradedPieceIsoGradedTargetComplexOfStepSquares` at `stepSquares`), whose higher direct images
are the first page by the projection formula of Tag 0FML (`higherDirectImageGradedTargetIso`). -/
def higherDirectImageGradedPieceFirstPageIsoNat [QuasiCompact f] [QuasiSeparated f] [Smooth f]
    (k : ℕ) (q : ℤ) :
    higherDirectImage (derivedRelativePushforward f g)
        (gradedPiece (inverseImageBase (f ≫ g)) (k : ℤ) (deRhamSmoothFiltration f g))
        ((k : ℤ) + q) ≅
      deRhamFirstPage f g (k : ℤ) q :=
  (DerivedCategory.homologyFunctor _ ((k : ℤ) + q)).mapIso
      ((derivedRelativePushforward f g).mapIso (DerivedCategory.Q.mapIso
        (gradedPieceIsoGradedTargetComplexOfStepSquares f g k (stepSquares f g k).1
          (stepSquares f g k).2))) ≪≫
    higherDirectImageGradedTargetIso f g k q

/-- **`R^{p + q}f_*gr^pΩ^•_{X/S} ≅ H^q(Ω^p_{Y/S} ⊗^𝐋_{𝒪_Y} Rf_*Ω^•_{X/Y})`**, as an isomorphism:
`higherDirectImageGradedPieceFirstPageIsoNat` for `p ≥ 0`, and the isomorphism of two zero objects
for `p < 0`. -/
def higherDirectImageGradedPieceFirstPageIso [QuasiCompact f] [QuasiSeparated f] [Smooth f]
    (p q : ℤ) :
    higherDirectImage (derivedRelativePushforward f g)
        (gradedPiece (inverseImageBase (f ≫ g)) p (deRhamSmoothFiltration f g)) (p + q) ≅
      deRhamFirstPage f g p q :=
  if hp : p < 0 then
    (isZero_higherDirectImage_gradedPiece_of_neg f g p (p + q) hp).iso
      (isZero_deRhamFirstPage_of_neg f g p q hp)
  else
    eqToIso (by rw [Int.toNat_of_nonneg (not_lt.1 hp)]) ≪≫
      higherDirectImageGradedPieceFirstPageIsoNat f g p.toNat q ≪≫
      eqToIso (by rw [Int.toNat_of_nonneg (not_lt.1 hp)])

/-- Conjugating a morphism by two composites of isomorphisms, split after the first factor. -/
private lemma conj_trans {C : Type*} [Category* C] {P M N P' M' N' : C} (a : P ≅ M) (b : M ≅ N)
    (a' : P' ≅ M') (b' : M' ≅ N') (δ : M ⟶ M') :
    a.hom ≫ δ ≫ a'.inv = (a ≪≫ b).hom ≫ (b.inv ≫ δ ≫ b'.hom) ≫ (a' ≪≫ b').inv := by
  simp

/-- Two conjugated morphisms compose to zero if their conjugates do. -/
private lemma comp_eq_zero_of_conj {C : Type*} [Category* C] [Preadditive C] {A B D A' B' D' : C}
    (e : A' ≅ A) (e' : B' ≅ B) (e'' : D' ≅ D) (d : A ⟶ B) (d' : B ⟶ D)
    (h : (e.hom ≫ d ≫ e'.inv) ≫ (e'.hom ≫ d' ≫ e''.inv) = 0) : d ≫ d' = 0 := by
  have := congrArg (fun x ↦ e.inv ≫ x ≫ e''.hom) h
  simpa using this

/-- Conjugates of two morphisms composing to zero compose to zero. -/
private lemma conj_comp_eq_zero {C : Type*} [Category* C] [Preadditive C] {A B D A' B' D' : C}
    (e : A ≅ A') (e' : B ≅ B') (e'' : D ≅ D') (d : A ⟶ B) (d' : B ⟶ D) (h : d ≫ d' = 0) :
    (e.inv ≫ d ≫ e'.hom) ≫ (e'.inv ≫ d' ≫ e''.hom) = 0 := by
  simp [reassoc_of% h]

/-- Conjugating a morphism by two composites of three isomorphisms, given commuting squares
through the first two factors. -/
private lemma conj_trans_trans {C : Type*} [Category* C] {A M P N A' M' P' N' : C}
    (a : A ≅ M) (e : M ≅ P) (b : P ≅ N) (a' : A' ≅ M') (e' : M' ≅ P') (b' : P' ≅ N')
    (δ : A ⟶ A') (c : M ⟶ M') (c' : P ⟶ P') (hδ : δ ≫ a'.hom = a.hom ≫ c)
    (hc : c ≫ e'.hom = e.hom ≫ c') :
    (a ≪≫ e ≪≫ b).inv ≫ δ ≫ (a' ≪≫ e' ≪≫ b').hom = b.inv ≫ c' ≫ b'.hom := by
  simp only [Iso.trans_inv, Iso.trans_hom, Category.assoc, reassoc_of% hδ, reassoc_of% hc,
    Iso.inv_hom_id_assoc]

/-- **The chosen filtered K-injective resolution** of the filtered complex `Ω^•_{X/S}` of
Section 0FMK (`deRhamSmoothFiltration`), from [Stacks, Tag 0BKI]. -/
def deRhamSmoothResolution :
    FilteredKInjectiveResolution (inverseImageBase (f ≫ g)) (deRhamSmoothFiltration f g) :=
  FilteredKInjectiveResolution.chosen _ _

/-- **The spectral sequence of [Stacks, Tag 0FMM]**, starting at its first page: the spectral
sequence of the filtered complex `f_*J` for `J` the chosen filtered K-injective resolution of
`Ω^•_{X/S}` (`deRhamSmoothResolution`). -/
def deRhamSmoothSpectralSequence :
    CohomologicalSpectralSequence
      (SheafOfModules.{u} (structureSheafRing (inverseImageBase g))) 1 :=
  (pushforwardSpectralSequence (relativeBase f g) (deRhamSmoothResolution f g).obj).shiftStart
    (by omega)

/-- The derived pushforward `derivedRelativePushforward` is a right derived functor of the
pushforward along `relativeBase`, with unit `derivedRelativePushforwardUnit`. -/
instance isRightDerivedFunctor_derivedRelativePushforward :
    (derivedRelativePushforward f g).IsRightDerivedFunctor (derivedRelativePushforwardUnit f g)
      (HomotopyCategory.quasiIso
        (SheafOfModules.{u} (structureSheafRing (inverseImageBase (f ≫ g)))) (ComplexShape.up ℤ)) :=
  have := hasPointwiseRightDerivedFunctor_homotopyPushforward (relativeBase f g)
  inferInstance

/-- `H^n(f_*gr^pJ) ≅ H^q(Ω^p_{Y/S} ⊗^𝐋_{𝒪_Y} Rf_*Ω^•_{X/Y})` for `n = p + q`, `J` the chosen
resolution: the cohomology of `f_*` of the K-injective complex `gr^pJ` is `R^nf_*gr^pJ`, which is
`R^nf_*gr^pΩ^•_{X/S}` through the quasi-isomorphism `gr^pΩ^•_{X/S} ⟶ gr^pJ`, and that is the first
page by `higherDirectImageGradedPieceFirstPageIso`. -/
def deRhamSmoothGradedHomologyIso [QuasiCompact f] [QuasiSeparated f] [Smooth f] (p q n : ℤ)
    (hn : n = p + q) :
    ((pushforwardComplexFunctor (relativeBase f g)).obj
        ((FilteredObject.gr p).obj (deRhamSmoothResolution f g).obj)).homology n ≅
      deRhamFirstPage f g p q :=
  pushforwardGrHomologyIso (relativeBase f g) (deRhamSmoothResolution f g) p n ≪≫
    eqToIso (by subst hn; rfl) ≪≫ higherDirectImageGradedPieceFirstPageIso f g p q

/-- **The first page of [Stacks, Tag 0FMM]**: `E_1^{p, q} ≅ H^q(Ω^p_{Y/S} ⊗^𝐋_{𝒪_Y}
Rf_*Ω^•_{X/Y})`, as an isomorphism. -/
def deRhamSmoothFirstPageIso [QuasiCompact f] [QuasiSeparated f] [Smooth f] (p q : ℤ) :
    ((deRhamSmoothSpectralSequence f g).page 1).X (p, q) ≅ deRhamFirstPage f g p q :=
  pushforwardFirstPageIso (relativeBase f g) (deRhamSmoothResolution f g).obj
      (deRhamSmoothResolution f g).injective_step p q (p + q) rfl ≪≫
    deRhamSmoothGradedHomologyIso f g p q (p + q) rfl

/-- **The first differential of [Stacks, Tag 0FMM]**, as a map
`H^q(Ω^p_{Y/S} ⊗^𝐋 Rf_*Ω^•_{X/Y}) ⟶ H^q(Ω^{p + 1}_{Y/S} ⊗^𝐋 Rf_*Ω^•_{X/Y})`: the connecting
morphism, in the cohomology of `f_*` of the chosen resolution `J`, of
`0 ⟶ gr^{p + 1}J ⟶ F^pJ/F^{p + 2}J ⟶ gr^pJ ⟶ 0`, read through `deRhamSmoothGradedHomologyIso`. -/
def deRhamFirstPageDifferential [QuasiCompact f] [QuasiSeparated f] [Smooth f] (p q : ℤ) :
    deRhamFirstPage f g p q ⟶ deRhamFirstPage f g (p + 1) q :=
  (deRhamSmoothGradedHomologyIso f g p q (p + q) rfl).inv ≫
    (shortExact_pushforward_grShortComplex (relativeBase f g) (deRhamSmoothResolution f g).obj
      (deRhamSmoothResolution f g).injective_step p).δ (p + q) (p + 1 + q) (by simp; omega) ≫
    (deRhamSmoothGradedHomologyIso f g (p + 1) q (p + 1 + q) rfl).hom

/-- **The first differential of the spectral sequence of [Stacks, Tag 0FMM]** is
`deRhamFirstPageDifferential`, through the first-page isomorphisms `deRhamSmoothFirstPageIso`. -/
theorem deRhamSmoothSpectralSequence_d [QuasiCompact f] [QuasiSeparated f] [Smooth f] (p q : ℤ) :
    ((deRhamSmoothSpectralSequence f g).page 1).d (p, q) (p + 1, q) =
      (deRhamSmoothFirstPageIso f g p q).hom ≫ deRhamFirstPageDifferential f g p q ≫
        (deRhamSmoothFirstPageIso f g (p + 1) q).inv := by
  change ((pushforwardSpectralSequence (relativeBase f g) (deRhamSmoothResolution f g).obj).page 1
    (by omega)).d (p, q) (p + 1, q) = _
  rw [pushforwardSpectralSequence_d (relativeBase f g) (deRhamSmoothResolution f g).obj
    (deRhamSmoothResolution f g).injective_step p q (p + q) (p + 1 + q) rfl (by omega)]
  exact conj_trans _ _ _ _ _

/-- `d_1 ∘ d_1 = 0` for `deRhamFirstPageDifferential`. -/
@[reassoc (attr := simp)]
theorem deRhamFirstPageDifferential_comp [QuasiCompact f] [QuasiSeparated f] [Smooth f]
    (p q : ℤ) :
    deRhamFirstPageDifferential f g p q ≫ deRhamFirstPageDifferential f g (p + 1) q = 0 := by
  have h := ((deRhamSmoothSpectralSequence f g).page 1).d_comp_d (p, q) (p + 1, q) (p + 1 + 1, q)
  rw [deRhamSmoothSpectralSequence_d, deRhamSmoothSpectralSequence_d] at h
  exact comp_eq_zero_of_conj _ _ _ _ _ h


/-- An exhaustive filtration (`F^p = K` for `p ≤ 0`) has `R^nf_*F^p ⟶ R^nf_*K` invertible for
`p ≤ 0`. -/
private lemma higherDirectImageMap_isIso_of_exhaustive
    (K : CochainComplex.Filtered
      (SheafOfModules.{u} (structureSheafRing (inverseImageBase (f ≫ g)))))
    (hexh : ∀ p : ℤ, p ≤ 0 → IsIso (K.filtration.ι.app (op p))) (n : ℤ) :
    ∃ p₁ : ℤ, ∀ p : ℤ, p ≤ p₁ →
      IsIso (higherDirectImageMap (derivedRelativePushforward f g) (K.filtration.ι.app (op p)) n) :=
  ⟨0, fun p hp ↦ by
    have := hexh p hp
    exact Functor.map_isIso _ _⟩

/-- The convergence data of the spectral sequence of `f_*` of the chosen resolution: boundedness
of the first page in each total degree, and the abutment to `R^nf_*Ω^•_{X/S}`. -/
private theorem deRhamSmoothSpectralSequence_converges
    [QuasiCompact f] [QuasiSeparated f] [Smooth f] :
    _root_.IsBounded (deRhamSmoothSpectralSequence f g) ∧
      SpectralSequence.AbutsTo (deRhamSmoothSpectralSequence f g)
        (fun n => deRhamHigherDirectImage f g n) := by
  have hexhaust := higherDirectImageMap_isIso_of_exhaustive f g (deRhamSmoothFiltration f g)
    (deRhamSmoothFiltration_spec f g).2.2.2
  obtain ⟨hfin, F, hF, -, hbounds, hinf, hgriso⟩ := pushforward_converges (relativeBase f g)
    (derivedRelativePushforward f g) (derivedRelativePushforwardUnit f g)
    (deRhamSmoothResolution f g) (exists_higherDirectImage_deRhamSmoothFiltration_isZero f g)
    hexhaust
  exact ⟨hfin, SpectralSequence.AbutsTo.shiftStart ⟨hinf, F, hF, hbounds, hgriso⟩ (by omega)⟩

/-- **The spectral sequence of [Stacks, Tag 0FMM] is bounded**: in each total degree only
finitely many terms of its first page are nonzero. -/
theorem deRhamSmoothSpectralSequence_isBounded [QuasiCompact f] [QuasiSeparated f] [Smooth f] :
    _root_.IsBounded (deRhamSmoothSpectralSequence f g) :=
  (deRhamSmoothSpectralSequence_converges f g).1

/-- **The spectral sequence of [Stacks, Tag 0FMM] abuts to `R^{p + q}f_*Ω^•_{X/S}`.** -/
theorem deRhamSmoothSpectralSequence_abutsTo [QuasiCompact f] [QuasiSeparated f] [Smooth f] :
    SpectralSequence.AbutsTo (deRhamSmoothSpectralSequence f g)
      (fun n => deRhamHigherDirectImage f g n) :=
  (deRhamSmoothSpectralSequence_converges f g).2


/-- **The first differential of [Stacks, Tag 0FMM], in the derived category**:
`deRhamFirstPageDifferential` is `R^{p + q}f_*` of the connecting morphism `gr^pΩ^•_{X/S} ⟶
gr^{p + 1}Ω^•_{X/S}[1]` of the distinguished triangle of
`0 ⟶ gr^{p + 1}Ω^•_{X/S} ⟶ F^pΩ^•_{X/S}/F^{p + 2}Ω^•_{X/S} ⟶ gr^pΩ^•_{X/S} ⟶ 0`, read through
`higherDirectImageGradedPieceFirstPageIso`. -/
theorem deRhamFirstPageDifferential_eq_derived [QuasiCompact f] [QuasiSeparated f] [Smooth f]
    (p q : ℤ) :
    deRhamFirstPageDifferential f g p q =
      (higherDirectImageGradedPieceFirstPageIso f g p q).inv ≫
        higherDirectImageGrConnecting (relativeBase f g) (deRhamSmoothFiltration f g) p (p + q)
          (p + 1 + q) (by omega) ≫
        (higherDirectImageGradedPieceFirstPageIso f g (p + 1) q).hom := by
  have h := pushforward_grConnecting (relativeBase f g) (deRhamSmoothResolution f g) p (p + q)
    (p + 1 + q) (by omega)
  exact conj_trans_trans _ _ _ _ _ _ _ _ _ h
    ((Category.comp_id _).trans (Category.id_comp _).symm)



/-- **The first differential of [Stacks, Tag 0FMM], derived form, on the spectral sequence**:
through `E_1^{p, q} ≅ H^{p + q}(f_*gr^pJ) ≅ R^{p + q}f_*gr^pΩ^•_{X/S}`, the first differential is
`R^{p + q}f_*` of the connecting morphism of the graded triangle of `Ω^•_{X/S}`. -/
theorem deRhamSmoothSpectralSequence_d_derived [QuasiCompact f] [QuasiSeparated f] [Smooth f]
    (p q : ℤ) :
    ((deRhamSmoothSpectralSequence f g).page 1).d (p, q) (p + 1, q) =
      (pushforwardFirstPageIso (relativeBase f g) (deRhamSmoothResolution f g).obj
          (deRhamSmoothResolution f g).injective_step p q (p + q) rfl ≪≫
        pushforwardGrHomologyIso (relativeBase f g) (deRhamSmoothResolution f g) p (p + q)).hom ≫
        higherDirectImageGrConnecting (relativeBase f g) (deRhamSmoothFiltration f g) p (p + q)
          (p + 1 + q) (by omega) ≫
        (pushforwardFirstPageIso (relativeBase f g) (deRhamSmoothResolution f g).obj
          (deRhamSmoothResolution f g).injective_step (p + 1) q (p + 1 + q) rfl ≪≫
        pushforwardGrHomologyIso (relativeBase f g) (deRhamSmoothResolution f g) (p + 1)
          (p + 1 + q)).inv := by
  have hc : (pushforwardGrHomologyIso (relativeBase f g) (deRhamSmoothResolution f g) p
      (p + q)).inv ≫
      (shortExact_pushforward_grShortComplex (relativeBase f g) (deRhamSmoothResolution f g).obj
        (deRhamSmoothResolution f g).injective_step p).δ (p + q) (p + 1 + q) (by simp; omega) ≫
      (pushforwardGrHomologyIso (relativeBase f g) (deRhamSmoothResolution f g) (p + 1)
        (p + 1 + q)).hom =
      higherDirectImageGrConnecting (relativeBase f g) (deRhamSmoothFiltration f g) p (p + q)
        (p + 1 + q) (by omega) := by
    rw [pushforward_grConnecting (relativeBase f g) (deRhamSmoothResolution f g) p (p + q)
      (p + 1 + q) (by omega), Iso.inv_hom_id_assoc]
  change ((pushforwardSpectralSequence (relativeBase f g) (deRhamSmoothResolution f g).obj).page 1
    (by omega)).d (p, q) (p + 1, q) = _
  rw [pushforwardSpectralSequence_d (relativeBase f g) (deRhamSmoothResolution f g).obj
    (deRhamSmoothResolution f g).injective_step p q (p + q) (p + 1 + q) rfl (by omega), ← hc]
  exact conj_trans _ _ _ _ _

/-- **`d_1 ∘ d_1 = 0` for the derived connecting morphisms of the graded pieces of
`Ω^•_{X/S}`.** -/
theorem higherDirectImageGrConnecting_deRhamSmoothFiltration_comp
    [QuasiCompact f] [QuasiSeparated f] [Smooth f] (p q : ℤ) :
    higherDirectImageGrConnecting (relativeBase f g) (deRhamSmoothFiltration f g) p (p + q)
        (p + 1 + q) (by omega) ≫
      higherDirectImageGrConnecting (relativeBase f g) (deRhamSmoothFiltration f g) (p + 1)
        (p + 1 + q) (p + 1 + 1 + q) (by omega) = 0 := by
  have h := ((deRhamSmoothSpectralSequence f g).page 1).d_comp_d (p, q) (p + 1, q) (p + 1 + 1, q)
  rw [deRhamSmoothSpectralSequence_d_derived, deRhamSmoothSpectralSequence_d_derived] at h
  exact comp_eq_zero_of_conj _ _ _ _ _ h


/-! ### The flat case of [Stacks, Tag 0FMN] -/

/-- **The first differential in the flat case of [Stacks, Tag 0FMN]**: when the de Rham
cohomology sheaves `ℋ^q_dR(X/Y)` are flat `𝒪_Y`-modules, the map
`d_1^{p, q} : Ω^p_{Y/S} ⊗_{𝒪_Y} ℋ^q_dR(X/Y) ⟶ Ω^{p + 1}_{Y/S} ⊗_{𝒪_Y} ℋ^q_dR(X/Y)`: `R^{p + q}f_*`
of the connecting morphism of the graded triangle of `Ω^•_{X/S}`
(`higherDirectImageGrConnecting`), read through the identifications
`R^{p + q}f_*gr^pΩ^•_{X/S} ≅ Ω^p_{Y/S} ⊗_{𝒪_Y} ℋ^q_dR(X/Y)` of
`higherDirectImageGradedPieceFlatIso`. -/
def deRhamFirstPageFlatDifferential [QuasiCompact f] [QuasiSeparated f] [Smooth f]
    (hflat : ∀ q : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Y.sheaf)
      (deRhamCohomologySheaf f q)) (p q : ℤ) :
    deRhamFirstPageFlat f g p q ⟶ deRhamFirstPageFlat f g (p + 1) q :=
  (higherDirectImageGradedPieceFlatIso f g hflat p q).inv ≫
    higherDirectImageGrConnecting (relativeBase f g) (deRhamSmoothFiltration f g) p (p + q)
      (p + 1 + q) (by omega) ≫
    (higherDirectImageGradedPieceFlatIso f g hflat (p + 1) q).hom

/-- `d_1 ∘ d_1 = 0` for `deRhamFirstPageFlatDifferential`. -/
@[reassoc (attr := simp)]
theorem deRhamFirstPageFlatDifferential_comp [QuasiCompact f] [QuasiSeparated f] [Smooth f]
    (hflat : ∀ q : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Y.sheaf)
      (deRhamCohomologySheaf f q)) (p q : ℤ) :
    deRhamFirstPageFlatDifferential f g hflat p q ≫
      deRhamFirstPageFlatDifferential f g hflat (p + 1) q = 0 :=
  conj_comp_eq_zero (C := SheafOfModules.{u} (structureSheafRing (inverseImageBase g))) _ _ _ _ _
    (higherDirectImageGrConnecting_deRhamSmoothFiltration_comp f g p q)

/-- **The first page of [Stacks, Tag 0FMM] in the flat case of [Stacks, Tag 0FMN]**: when the
`ℋ^q_dR(X/Y)` are flat `𝒪_Y`-modules, `E_1^{p, q} ≅ Ω^p_{Y/S} ⊗_{𝒪_Y} ℋ^q_dR(X/Y)`:
`E_1^{p, q} ≅ H^{p + q}(f_*gr^pJ) ≅ R^{p + q}f_*gr^pΩ^•_{X/S}` followed by
`higherDirectImageGradedPieceFlatIso`. -/
def deRhamSmoothFirstPageFlatIso [QuasiCompact f] [QuasiSeparated f] [Smooth f]
    (hflat : ∀ q : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Y.sheaf)
      (deRhamCohomologySheaf f q)) (p q : ℤ) :
    ((deRhamSmoothSpectralSequence f g).page 1).X (p, q) ≅ deRhamFirstPageFlat f g p q :=
  (pushforwardFirstPageIso (relativeBase f g) (deRhamSmoothResolution f g).obj
      (deRhamSmoothResolution f g).injective_step p q (p + q) rfl ≪≫
    pushforwardGrHomologyIso (relativeBase f g) (deRhamSmoothResolution f g) p (p + q)) ≪≫
    higherDirectImageGradedPieceFlatIso f g hflat p q

/-- **The first differential of the spectral sequence of [Stacks, Tag 0FMM], flat case**: through
`E_1^{p, q} ≅ Ω^p_{Y/S} ⊗_{𝒪_Y} ℋ^q_dR(X/Y)` it is `deRhamFirstPageFlatDifferential`. -/
theorem deRhamSmoothSpectralSequence_d_flat [QuasiCompact f] [QuasiSeparated f] [Smooth f]
    (hflat : ∀ q : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Y.sheaf)
      (deRhamCohomologySheaf f q)) (p q : ℤ) :
    ((deRhamSmoothSpectralSequence f g).page 1).d (p, q) (p + 1, q) =
      (deRhamSmoothFirstPageFlatIso f g hflat p q).hom ≫
        deRhamFirstPageFlatDifferential f g hflat p q ≫
          (deRhamSmoothFirstPageFlatIso f g hflat (p + 1) q).inv :=
  (deRhamSmoothSpectralSequence_d_derived f g p q).trans (conj_trans _ _ _ _ _)

end Stacks.DeRhamSmooth
