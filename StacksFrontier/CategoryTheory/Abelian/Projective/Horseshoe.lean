module

public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.HomologySequenceLemmas
public import Mathlib.CategoryTheory.Abelian.LeftDerived
public import StacksFrontier.CategoryTheory.Abelian.Projective.ResolutionLift
import StacksCore.Tactic.EgaSgaAttribute

/-! # The horseshoe lemma and the long exact sequence of left derived functors

Let `C` be an abelian category with enough projectives and let `F : C ⥤ D` be an additive
functor into an abelian category. This file proves the **horseshoe lemma** (Weibel, Lemma 2.2.8):
a short exact sequence `S : 0 → S.X₁ → S.X₂ → S.X₃ → 0` lifts to a short exact sequence of
projective resolutions which is split in every degree. From it, the left derived functors
`Lₙ F` acquire a connecting morphism `Lₙ₊₁ F (S.X₃) ⟶ Lₙ F (S.X₁)`, a long exact sequence, and
the naturality of the connecting morphism in the short exact sequence.

## Main definitions

* `CategoryTheory.ShortComplex.Horseshoe`: the data produced by the horseshoe lemma.
* `CategoryTheory.ShortComplex.horseshoe`: the horseshoe lemma itself.
* `CategoryTheory.ShortComplex.Horseshoe.δ` and `CategoryTheory.Functor.leftDerivedδ`: the
  connecting morphism `Lₙ₊₁ F (S.X₃) ⟶ Lₙ F (S.X₁)`.
* `CategoryTheory.ProjectiveResolution.aug0`: the degree-zero augmentation of a projective
  resolution, with its codomain spelled as the resolved object.

## Main results

* `CategoryTheory.Functor.additive_leftDerived`: the left derived functors are additive.
* `CategoryTheory.Functor.leftDerived_exact`, `leftDerived_exact_δ₁`, `leftDerived_exact_δ₂`
  and `epi_leftDerivedZero_map_g`: the long exact sequence
  `⋯ → Lₙ₊₁ F (S.X₃) → Lₙ F (S.X₁) → Lₙ F (S.X₂) → Lₙ F (S.X₃) → ⋯ → L₀ F (S.X₃) → 0`.
* `CategoryTheory.Functor.leftDerivedδ_naturality`: the connecting morphism is natural in the
  short exact sequence.

## References

* [Stacks Project, Tag 010Q](https://stacks.math.columbia.edu/tag/010Q)
* [Stacks Project, Tag 08PG](https://stacks.math.columbia.edu/tag/08PG)
* Weibel, *An introduction to homological algebra*, Lemma 2.2.8 and Theorem 2.4.6.
-/

@[expose] public noncomputable section

open CategoryTheory Category Limits Preadditive

universe v u v₂ u₂

namespace CategoryTheory.ProjectiveResolution

variable {C : Type u} [Category.{v} C] [Abelian C] {Z : C}

/-- The degree-zero component of the augmentation of a projective resolution, with its
codomain spelled `Z` rather than `((ChainComplex.single₀ C).obj Z).X 0`. -/
def aug0 (P : ProjectiveResolution Z) : P.complex.X 0 ⟶ Z :=
  (ChainComplex.toSingle₀Equiv P.complex Z P.π).1

/-- The augmentation kills the image of the differential out of degree one. -/
@[reassoc (attr := simp)]
lemma d_comp_aug0 (P : ProjectiveResolution Z) : P.complex.d 1 0 ≫ aug0 P = 0 :=
  (ChainComplex.toSingle₀Equiv P.complex Z P.π).2

/-- The augmentation of a projective resolution is an epimorphism in degree zero. -/
lemma epi_aug0 (P : ProjectiveResolution Z) : Epi (aug0 P) :=
  inferInstanceAs (Epi (P.π.f 0))

/-- `P₁ → P₀ → Z` is exact, in the `aug0` spelling. -/
lemma exact_aug0 (P : ProjectiveResolution Z) :
    (ShortComplex.mk (P.complex.d 1 0) (aug0 P) (d_comp_aug0 P)).Exact :=
  P.exact₀

end CategoryTheory.ProjectiveResolution

namespace CategoryTheory.ShortComplex

variable {C : Type u} [Category.{v} C] [Abelian C]

section Helpers

open ProjectiveResolution

/-- Two morphisms into a complex concentrated in degree zero agree as soon as their
degree-zero components do. -/
lemma to_single₀_eq {T : ChainComplex C ℕ} {Y : C}
    (α β : T ⟶ (ChainComplex.single₀ C).obj Y) (h : α.f 0 = β.f 0) : α = β :=
  (ChainComplex.toSingle₀Equiv T Y).injective (Subtype.ext h)

/-- The degree-zero component of a morphism of resolutions covering `u`, in the `aug0`
spelling. -/
lemma π_comp_single₀_map_f_zero {X Y : C} (P : ProjectiveResolution X) (u : X ⟶ Y) :
    (P.π ≫ (ChainComplex.single₀ C).map u).f 0 = aug0 P ≫ u := by
  rw [HomologicalComplex.comp_f, ChainComplex.single₀_map_f_zero]
  rfl

/-- A null-homotopic chain map into a resolution vanishes on the augmentation. -/
lemma nullHomotopicMap_comp_π {X : C} {P : ChainComplex C ℕ} (Q : ProjectiveResolution X)
    (k : ∀ i j, P.X i ⟶ Q.complex.X j) :
    Homotopy.nullHomotopicMap k ≫ Q.π = 0 :=
  to_single₀_eq _ _ (by
    rw [HomologicalComplex.comp_f, ChainComplex.nullHomotopicMap_f_zero,
      HomologicalComplex.zero_f, Category.assoc, Q.complex_d_comp_π_f_zero, comp_zero])

/-- The relation in `ComplexShape.down ℕ` which carries the connecting morphism. -/
lemma down_rel_succ (n : ℕ) : (ComplexShape.down ℕ).Rel (n + 1) n := rfl

end Helpers

namespace HorseshoeAux

open ProjectiveResolution

/-- `d ∘ d = 0` for a lower-triangular differential `[[dᴬ, s], [0, dᶜ]]` on a biproduct:
on the diagonal it is `d ∘ d = 0` in each summand, off the diagonal it is the cocycle
identity `s₁ ≫ dᴬ = -(dᶜ ≫ s₀)`. -/
lemma dd_twisted {A₂ A₁ A₀ C₂ C₁ C₀ : C}
    (dA₁ : A₂ ⟶ A₁) (dA₀ : A₁ ⟶ A₀) (dC₁ : C₂ ⟶ C₁) (dC₀ : C₁ ⟶ C₀)
    (s₁ : C₂ ⟶ A₁) (s₀ : C₁ ⟶ A₀)
    (hA : dA₁ ≫ dA₀ = 0) (hC : dC₁ ≫ dC₀ = 0)
    (hcross : s₁ ≫ dA₀ = -(dC₁ ≫ s₀)) :
    biprod.desc (biprod.lift dA₁ 0) (biprod.lift s₁ dC₁) ≫
      biprod.desc (biprod.lift dA₀ 0) (biprod.lift s₀ dC₀) = 0 := by
  ext <;>
  simp only [biprod.inl_desc_assoc, biprod.inr_desc_assoc, biprod.lift_desc,
    Preadditive.add_comp, Category.assoc, biprod.lift_fst, biprod.lift_snd, comp_zero, add_zero,
    zero_comp, hA, hC]
  rw [add_eq_zero_iff_eq_neg, hcross]

/-- The short five lemma: a morphism of exact short complexes whose two outer components
are isomorphisms has isomorphic middle component. -/
lemma shortFive {S₁ S₂ : ShortComplex C}
    (h₁ : S₁.Exact) (h₂ : S₂.Exact) (hf₂ : Mono S₂.f) (hg₁ : Epi S₁.g)
    (φ : S₁ ⟶ S₂) (h1 : IsIso φ.τ₁) (h3 : IsIso φ.τ₃) : IsIso φ.τ₂ := by
  have := h1; have := h3
  have : Mono φ.τ₂ :=
    ShortComplex.mono_of_mono_of_mono_of_mono φ h₁ hf₂ inferInstance inferInstance
  have : Epi φ.τ₂ :=
    ShortComplex.epi_of_epi_of_epi_of_epi φ h₂ hg₁ inferInstance inferInstance
  exact isIso_of_mono_of_epi φ.τ₂

/-- An exact short complex whose outer terms are zero has zero middle term. -/
lemma isZero_X₂ {S : ShortComplex C} (hS : S.Exact) (h1 : IsZero S.X₁) (h3 : IsZero S.X₃) :
    IsZero S.X₂ := by
  have hmono : Mono S.g := hS.mono_g (h1.eq_zero_of_src _)
  rw [IsZero.iff_id_eq_zero, ← cancel_mono S.g]
  simp [h3.eq_zero_of_tgt S.g]

/-- The bottom of the homology long exact sequence of a short exact sequence of
`ℕ`-indexed chain complexes: the map induced in degree zero by the right-hand map is an
epimorphism. -/
lemma epi_homologyMap_g_zero {S : ShortComplex (ChainComplex C ℕ)} (hS : S.ShortExact) :
    Epi (HomologicalComplex.homologyMap S.g 0) := by
  have : Epi S.g := hS.epi_g
  have : Epi (HomologicalComplex.opcyclesMap S.g 0) := by
    have := HomologicalComplex.opcycles_right_exact S hS.exact (i := 0); infer_instance
  have i2 : IsIso (S.X₃.homologyι 0) := ChainComplex.isIso_homologyι₀ _
  have i1 : IsIso (S.X₂.homologyι 0) := ChainComplex.isIso_homologyι₀ _
  have key : HomologicalComplex.homologyMap S.g 0 ≫ S.X₃.homologyι 0
      = S.X₂.homologyι 0 ≫ HomologicalComplex.opcyclesMap S.g 0 :=
    HomologicalComplex.homologyι_naturality S.g 0
  have hc : Epi (HomologicalComplex.homologyMap S.g 0 ≫ S.X₃.homologyι 0) := by
    rw [key]; infer_instance
  exact (epi_comp_iff_of_isIso (HomologicalComplex.homologyMap S.g 0) (S.X₃.homologyι 0)).mp hc

variable {S : ShortComplex C} (PA : ProjectiveResolution S.X₁)
  (PC : ProjectiveResolution S.X₃)

/-- The readiness invariant of the horseshoe recursion: the obstruction to extending the
shear family one step vanishes. -/
def Ready : (n : ℕ) → (PC.complex.X (n + 1) ⟶ PA.complex.X n) → Prop
  | 0, sn => (PC.complex.d 2 1 ≫ sn) ≫ aug0 PA = 0
  | (m + 1), sn => (PC.complex.d (m + 3) (m + 2) ≫ sn) ≫ PA.complex.d (m + 1) m = 0

/-- One step of the horseshoe recursion: a lift of `-(dᶜₙ₊₁ ≫ sₙ)` through `dᴬₙ`, for a
ready `sₙ`. -/
def stepLift (n : ℕ) (sn : PC.complex.X (n + 1) ⟶ PA.complex.X n)
    (hsn : Ready PA PC n sn) :
    { t : PC.complex.X (n + 2) ⟶ PA.complex.X (n + 1) //
        t ≫ PA.complex.d (n + 1) n = -(PC.complex.d (n + 2) (n + 1) ≫ sn) } := by
  haveI : Projective (PC.complex.X (n + 2)) := PC.projective _
  cases n with
  | zero =>
    have hyp : (-(PC.complex.d 2 1 ≫ sn)) ≫ aug0 PA = 0 := by
      rw [neg_comp, show (PC.complex.d 2 1 ≫ sn) ≫ aug0 PA = 0 from hsn, neg_zero]
    exact ⟨(exact_aug0 PA).liftFromProjective _ hyp,
      (exact_aug0 PA).liftFromProjective_comp _ hyp⟩
  | succ m =>
    have hyp : (-(PC.complex.d (m + 3) (m + 2) ≫ sn)) ≫ PA.complex.d (m + 1) m = 0 := by
      rw [neg_comp,
        show (PC.complex.d (m + 3) (m + 2) ≫ sn) ≫ PA.complex.d (m + 1) m = 0 from hsn, neg_zero]
    exact ⟨(PA.exact_succ m).liftFromProjective _ hyp,
      (PA.exact_succ m).liftFromProjective_comp _ hyp⟩

variable (hS : S.ShortExact)

/-- A lift `σ : (PC)₀ ⟶ S.X₂` of the augmentation of `PC` along the epimorphism `S.g`. -/
def sigma : PC.complex.X 0 ⟶ S.X₂ :=
  haveI := hS.epi_g
  Projective.factorThru (X := S.X₃) (aug0 PC) S.g

/-- The defining property of `sigma`. -/
lemma sigma_comp : sigma PC hS ≫ S.g = aug0 PC := by
  have := hS.epi_g
  exact Projective.factorThru_comp (X := S.X₃) (aug0 PC) S.g

/-- The composite `dᶜ₁ ≫ σ` lands in the kernel of `S.g`. -/
lemma dc0_sigma_comp_g : (PC.complex.d 1 0 ≫ sigma PC hS) ≫ S.g = 0 := by
  rw [Category.assoc, sigma_comp, d_comp_aug0]

/-- The factorization `t : (PC)₁ ⟶ S.X₁` of `dᶜ₁ ≫ σ` through `S.f`. -/
def tbase : PC.complex.X 1 ⟶ S.X₁ :=
  hS.exact.liftFromProjective (PC.complex.d 1 0 ≫ sigma PC hS) (dc0_sigma_comp_g PC hS)

/-- The defining property of `tbase`. -/
lemma tbase_comp : tbase PC hS ≫ S.f = PC.complex.d 1 0 ≫ sigma PC hS :=
  hS.exact.liftFromProjective_comp _ _

/-- `tbase` is killed by the differential out of degree two. -/
lemma dc1_tbase : PC.complex.d 2 1 ≫ tbase PC hS = 0 := by
  have := hS.mono_f
  have hf : (PC.complex.d 2 1 ≫ tbase PC hS) ≫ S.f = 0 := by
    rw [Category.assoc, tbase_comp, ← Category.assoc, PC.complex.d_comp_d, zero_comp]
  exact (cancel_mono S.f).1 (by simpa using hf)

/-- The base of the shear family, `s₀ : (PC)₁ ⟶ (PA)₀`, lifting `-t` along the
augmentation of `PA`. -/
def sbase : PC.complex.X 1 ⟶ PA.complex.X 0 :=
  haveI := epi_aug0 PA
  Projective.factorThru (X := S.X₁) (-(tbase PC hS)) (aug0 PA)

/-- The defining property of `sbase`. -/
lemma sbase_comp : sbase PA PC hS ≫ aug0 PA = -(tbase PC hS) := by
  have := epi_aug0 PA
  exact Projective.factorThru_comp (X := S.X₁) (-(tbase PC hS)) (aug0 PA)

/-- `sbase` is ready. -/
lemma readyBase : Ready PA PC 0 (sbase PA PC hS) := by
  change (PC.complex.d 2 1 ≫ sbase PA PC hS) ≫ aug0 PA = 0
  rw [Category.assoc, sbase_comp, comp_neg, dc1_tbase, neg_zero]

/-- The shear family together with its readiness invariant, by recursion. -/
def sData : (n : ℕ) →
    { sn : PC.complex.X (n + 1) ⟶ PA.complex.X n // Ready PA PC n sn }
  | 0 => ⟨sbase PA PC hS, readyBase PA PC hS⟩
  | (n + 1) =>
    let prev := sData n
    let nxt := stepLift PA PC n prev.1 prev.2
    ⟨nxt.1, by
      change (PC.complex.d (n + 3) (n + 2) ≫ nxt.1) ≫ PA.complex.d (n + 1) n = 0
      rw [Category.assoc, nxt.2, comp_neg, ← Category.assoc, PC.complex.d_comp_d,
        zero_comp, neg_zero]⟩

/-- The shear family `sₙ : (PC)ₙ₊₁ ⟶ (PA)ₙ` of the horseshoe. -/
def shear (n : ℕ) : PC.complex.X (n + 1) ⟶ PA.complex.X n :=
  (sData PA PC hS n).1

/-- The cross-term identity satisfied by the shear family. -/
lemma shear_cross (n : ℕ) :
    shear PA PC hS (n + 1) ≫ PA.complex.d (n + 1) n
      = -(PC.complex.d (n + 2) (n + 1) ≫ shear PA PC hS n) :=
  (stepLift PA PC n (sData PA PC hS n).1 (sData PA PC hS n).2).2

/-- The shear family starts at `sbase`. -/
lemma shear_zero : shear PA PC hS 0 = sbase PA PC hS := rfl

/-- The twisted lower-triangular differential `[[dᴬ, sₙ], [0, dᶜ]]`. -/
def D (n : ℕ) :
    (PA.complex.X (n + 1) ⊞ PC.complex.X (n + 1)) ⟶ (PA.complex.X n ⊞ PC.complex.X n) :=
  biprod.desc (biprod.lift (PA.complex.d (n + 1) n) 0)
    (biprod.lift (shear PA PC hS n) (PC.complex.d (n + 1) n))

/-- The twisted differential squares to zero. -/
lemma D_comp_D (n : ℕ) : D PA PC hS (n + 1) ≫ D PA PC hS n = 0 :=
  dd_twisted _ _ _ _ _ _ (PA.complex.d_comp_d _ _ _) (PC.complex.d_comp_d _ _ _)
    (shear_cross PA PC hS n)

/-- The middle complex of the horseshoe: the degreewise biproduct of `PA` and `PC` with the
twisted differential. -/
abbrev Tcx : ChainComplex C ℕ :=
  ChainComplex.of (fun n => PA.complex.X n ⊞ PC.complex.X n) (D PA PC hS) (D_comp_D PA PC hS)

/-- The differential of the middle complex. -/
lemma Tcx_d (n : ℕ) : (Tcx PA PC hS).d (n + 1) n = D PA PC hS n :=
  ChainComplex.of_d (fun n => PA.complex.X n ⊞ PC.complex.X n) (D PA PC hS) n

/-- The middle complex is degreewise projective. -/
lemma Tcx_proj (n : ℕ) : Projective ((Tcx PA PC hS).X n) :=
  inferInstanceAs (Projective (PA.complex.X n ⊞ PC.complex.X n))

/-- The inclusion of `PA` into the middle complex, degreewise `biprod.inl`. -/
def iota : PA.complex ⟶ Tcx PA PC hS where
  f _ := biprod.inl
  comm' i j hij := by
    obtain rfl : j + 1 = i := hij
    rw [Tcx_d]
    simp only [D, biprod.inl_desc]
    refine biprod.hom_ext _ _ ?_ ?_ <;> simp

/-- The components of `iota`. -/
lemma iota_f (n : ℕ) : (iota PA PC hS).f n = biprod.inl := rfl

/-- The projection of the middle complex onto `PC`, degreewise `biprod.snd`. -/
def proj : Tcx PA PC hS ⟶ PC.complex where
  f _ := biprod.snd
  comm' i j hij := by
    obtain rfl : j + 1 = i := hij
    rw [Tcx_d]
    simp only [D]
    refine biprod.hom_ext' _ _ ?_ ?_ <;> simp

/-- The components of `proj`. -/
lemma proj_f (n : ℕ) : (proj PA PC hS).f n = biprod.snd := rfl

/-- The inclusion and the projection compose to zero. -/
lemma iota_comp_proj : iota PA PC hS ≫ proj PA PC hS = 0 := by
  refine HomologicalComplex.hom_ext _ _ fun n => ?_
  rw [HomologicalComplex.comp_f, iota_f, proj_f, HomologicalComplex.zero_f]
  exact biprod.inl_snd

/-- The degreewise splitting of the horseshoe sequence: the biproduct splitting. -/
def splitting (n : ℕ) :
    (ShortComplex.mk ((iota PA PC hS).f n) ((proj PA PC hS).f n)
      (by rw [← HomologicalComplex.comp_f, iota_comp_proj]; simp)).Splitting :=
  Splitting.ofHasBinaryBiproduct (PA.complex.X n) (PC.complex.X n)

/-- The degree-zero augmentation `(εᴬ ≫ S.f, σ)` of the middle complex. -/
def e0 : (Tcx PA PC hS).X 0 ⟶ S.X₂ :=
  biprod.desc (aug0 PA ≫ S.f) (sigma PC hS)

/-- The degree-zero augmentation is killed by the differential out of degree one. -/
lemma d_comp_e0 : (Tcx PA PC hS).d 1 0 ≫ e0 PA PC hS = 0 := by
  rw [Tcx_d]
  simp only [D, e0]
  refine biprod.hom_ext' _ _ ?_ ?_
  · simp only [biprod.inl_desc_assoc, biprod.lift_desc, comp_zero, zero_comp, add_zero]
    rw [← Category.assoc, d_comp_aug0, zero_comp]
  · simp only [biprod.inr_desc_assoc, biprod.lift_desc]
    rw [show shear PA PC hS 0 = sbase PA PC hS from rfl, ← Category.assoc, sbase_comp,
      neg_comp, tbase_comp]
    simp

/-- The augmentation of the middle complex. -/
def aug : Tcx PA PC hS ⟶ (ChainComplex.single₀ C).obj S.X₂ :=
  (ChainComplex.toSingle₀Equiv _ _).symm ⟨e0 PA PC hS, d_comp_e0 PA PC hS⟩

/-- The degree-zero component of the augmentation. -/
lemma aug_f0 : (aug PA PC hS).f 0 = e0 PA PC hS :=
  ChainComplex.toSingle₀Equiv_symm_apply_f_zero _ _

/-- The inclusion covers `S.f`. -/
lemma iota_comp_aug :
    iota PA PC hS ≫ aug PA PC hS = PA.π ≫ (ChainComplex.single₀ C).map S.f := by
  refine to_single₀_eq _ _ ?_
  rw [HomologicalComplex.comp_f, iota_f, aug_f0, π_comp_single₀_map_f_zero]
  exact biprod.inl_desc _ _

/-- The projection covers `S.g`. -/
lemma proj_comp_π :
    proj PA PC hS ≫ PC.π = aug PA PC hS ≫ (ChainComplex.single₀ C).map S.g := by
  refine to_single₀_eq _ _ ?_
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f, proj_f, aug_f0,
    ChainComplex.single₀_map_f_zero]
  change biprod.snd ≫ aug0 PC = e0 PA PC hS ≫ S.g
  simp only [e0]
  refine biprod.hom_ext' _ _ ?_ ?_
  · simp [S.zero]
  · simp [sigma_comp]

/-- The degreewise split short complex of complexes produced by the construction. -/
def ses : ShortComplex (ChainComplex C ℕ) :=
  ShortComplex.mk _ _ (iota_comp_proj PA PC hS)

/-- It is short exact. -/
lemma ses_shortExact : (ses PA PC hS).ShortExact :=
  HomologicalComplex.shortExact_of_degreewise_shortExact _
    fun n => (splitting PA PC hS n).shortExact

/-- The augmentation of the middle complex is a quasi-isomorphism, so the middle complex
resolves `S.X₂`. -/
lemma aug_quasiIso : _root_.QuasiIso (aug PA PC hS) := by
  have hSE₁ : (ses PA PC hS).ShortExact := ses_shortExact PA PC hS
  have hSE₂ : (S.map (ChainComplex.single₀ C)).ShortExact := hS.map_of_exact _
  rw [_root_.quasiIso_iff]
  intro i
  rw [quasiIsoAt_iff_isIso_homologyMap]
  match i with
  | 0 =>
    let φ : ses PA PC hS ⟶ S.map (ChainComplex.single₀ C) :=
      { τ₁ := PA.π, τ₂ := aug PA PC hS, τ₃ := PC.π
        comm₁₂ := (iota_comp_aug PA PC hS).symm
        comm₂₃ := (proj_comp_π PA PC hS).symm }
    set hf0 := HomologicalComplex.homologyFunctor C (ComplexShape.down ℕ) 0 with hhf0
    have hτ₂ : (hf0.mapShortComplex.map φ).τ₂
        = HomologicalComplex.homologyMap (aug PA PC hS) 0 := rfl
    rw [← hτ₂]
    have hzC : IsZero ((S.map (ChainComplex.single₀ C)).X₃.homology 1) :=
      HomologicalComplex.isZero_single_obj_homology (ComplexShape.down ℕ) 0 _ 1 (by norm_num)
    have hMonoF : Mono (hf0.mapShortComplex.obj (S.map (ChainComplex.single₀ C))).f :=
      (hSE₂.homology_exact₁ 1 0 (by simp)).mono_g (hzC.eq_zero_of_src _)
    have hτ : ∀ {Z : C} (P : ProjectiveResolution Z),
        IsIso (HomologicalComplex.homologyMap P.π 0) := fun P => by
      have := P.quasiIso; infer_instance
    exact shortFive (hSE₁.homology_exact₂ 0) (hSE₂.homology_exact₂ 0) hMonoF
      (epi_homologyMap_g_zero hSE₁) (hf0.mapShortComplex.map φ) (hτ PA) (hτ PC)
  | (n + 1) =>
    have hP : ∀ {Z : C} (P : ProjectiveResolution Z), IsZero (P.complex.homology (n + 1)) :=
      fun P => by
        rw [← HomologicalComplex.exactAt_iff_isZero_homology]; exact P.complex_exactAt_succ n
    have hT : IsZero ((Tcx PA PC hS).homology (n + 1)) :=
      isZero_X₂ (hSE₁.homology_exact₂ (n + 1)) (hP PA) (hP PC)
    have hSB : IsZero (((ChainComplex.single₀ C).obj S.X₂).homology (n + 1)) :=
      HomologicalComplex.isZero_single_obj_homology (ComplexShape.down ℕ) 0 S.X₂ (n + 1)
        (by norm_num)
    exact IsZero.isIso hT hSB _

/-- The middle projective resolution produced by the horseshoe. -/
def PB : ProjectiveResolution S.X₂ :=
  haveI := aug_quasiIso PA PC hS
  ProjectiveResolution.mk (Tcx PA PC hS) (Tcx_proj PA PC hS) (aug PA PC hS)

end HorseshoeAux

/-- A **horseshoe** for a short complex `S` in an abelian category: projective resolutions
of the three terms of `S`, assembled into a short complex of chain complexes which is split
in every degree and whose two maps cover `S.f` and `S.g` on the augmentations. -/
structure Horseshoe (S : ShortComplex C) where
  /-- a projective resolution of `S.X₁` -/
  PA : ProjectiveResolution S.X₁
  /-- a projective resolution of `S.X₂` -/
  PB : ProjectiveResolution S.X₂
  /-- a projective resolution of `S.X₃` -/
  PC : ProjectiveResolution S.X₃
  /-- the chain map covering `S.f` -/
  ι : PA.complex ⟶ PB.complex
  /-- the chain map covering `S.g` -/
  p : PB.complex ⟶ PC.complex
  /-- the two chain maps compose to zero -/
  w : ι ≫ p = 0
  /-- the sequence of complexes is split in every degree -/
  splitting : ∀ n, (ShortComplex.mk (ι.f n) (p.f n)
    (by rw [← HomologicalComplex.comp_f, w, HomologicalComplex.zero_f])).Splitting
  /-- `ι` covers `S.f` -/
  commι : ι ≫ PB.π = PA.π ≫ (ChainComplex.single₀ C).map S.f
  /-- `p` covers `S.g` -/
  commp : p ≫ PC.π = PB.π ≫ (ChainComplex.single₀ C).map S.g

/-- **The horseshoe lemma.**  A short exact sequence in an abelian category with enough
projectives lifts to a degreewise split short exact sequence of projective resolutions of
its three terms: the chosen resolutions `PA` of `S.X₁` and `PC` of `S.X₃`, and in the middle
`Tₙ := (PA)ₙ ⊞ (PC)ₙ` with a twisted lower-triangular differential `[[dᴬ, sₙ], [0, dᶜ]]`. -/
@[no_expose, ega "0 11.6.1" "special case"]
def horseshoe [EnoughProjectives C] {S : ShortComplex C} (hS : S.ShortExact) :
    Horseshoe S :=
  { PA := ProjectiveResolution.of S.X₁
    PB := HorseshoeAux.PB _ _ hS
    PC := ProjectiveResolution.of S.X₃
    ι := HorseshoeAux.iota _ _ hS
    p := HorseshoeAux.proj _ _ hS
    w := HorseshoeAux.iota_comp_proj _ _ hS
    splitting := HorseshoeAux.splitting _ _ hS
    commι := HorseshoeAux.iota_comp_aug _ _ hS
    commp := HorseshoeAux.proj_comp_π _ _ hS }

/-- The left derived functors of an additive functor are additive. -/
instance _root_.CategoryTheory.Functor.additive_leftDerived
    {D : Type u₂} [Category.{v₂} D] [Abelian D] [HasProjectiveResolutions C]
    (F : C ⥤ D) [F.Additive] (n : ℕ) : (F.leftDerived n).Additive where
  map_add {X Y} f g := by
    have hsum : (ProjectiveResolution.lift f (projectiveResolution X) (projectiveResolution Y)
          + ProjectiveResolution.lift g (projectiveResolution X) (projectiveResolution Y))
        ≫ (projectiveResolution Y).π
        = (projectiveResolution X).π ≫ (ChainComplex.single₀ C).map (f + g) := by
      rw [Preadditive.add_comp, ProjectiveResolution.lift_commutes,
        ProjectiveResolution.lift_commutes, Functor.map_add, Preadditive.comp_add]
    rw [Functor.leftDerived_map_eq F n f
        (P := projectiveResolution X) (Q := projectiveResolution Y) _
        (ProjectiveResolution.lift_commutes f _ _),
      Functor.leftDerived_map_eq F n g
        (P := projectiveResolution X) (Q := projectiveResolution Y) _
        (ProjectiveResolution.lift_commutes g _ _),
      Functor.leftDerived_map_eq F n (f + g) _ hsum]
    simp only [Functor.map_add, Functor.comp_map, Preadditive.comp_add, Preadditive.add_comp]

namespace Horseshoe

section Sequence

variable {S : ShortComplex C} (H : Horseshoe S)

/-- The degreewise split short exact sequence of complexes carried by a horseshoe. -/
def ses : ShortComplex (ChainComplex C ℕ) := ShortComplex.mk H.ι H.p H.w

/-- A horseshoe sequence is short exact, being split in every degree. -/
lemma ses_shortExact : H.ses.ShortExact :=
  HomologicalComplex.shortExact_of_degreewise_shortExact _
    fun n => (H.splitting n).shortExact

include H in
/-- The right-hand map of a horseshoe sequence is an epimorphism. -/
lemma epi_p : Epi H.p :=
  HomologicalComplex.epi_of_epi_f _ fun n => (H.splitting n).epi_g

include H in
/-- The two maps of a horseshoe sequence compose to zero in each degree. -/
lemma ι_comp_p_f (n : ℕ) : H.ι.f n ≫ H.p.f n = 0 := by
  rw [← HomologicalComplex.comp_f, H.w, HomologicalComplex.zero_f]

variable {D : Type u₂} [Category.{v₂} D] [Abelian D] (F : C ⥤ D) [F.Additive]

/-- The image of a horseshoe sequence under an additive functor. -/
def mapSes : ShortComplex (ChainComplex D ℕ) :=
  H.ses.map (F.mapHomologicalComplex (ComplexShape.down ℕ))

/-- An additive functor preserves the degreewise splitting, hence the short exactness. -/
lemma mapSes_shortExact : (H.mapSes F).ShortExact :=
  HomologicalComplex.shortExact_of_degreewise_shortExact _
    fun n => ((H.splitting n).map F).shortExact

end Sequence

section Derived

variable {S : ShortComplex C} (H : Horseshoe S) [HasProjectiveResolutions C]
  {D : Type u₂} [Category.{v₂} D] [Abelian D] (F : C ⥤ D) [F.Additive]

/-- `ProjectiveResolution.isoLeftDerivedObj` for `S.X₁`, spelled with `homology` rather than
`homologyFunctor`. -/
def isoPA (n : ℕ) :
    (F.leftDerived n).obj S.X₁ ≅ (H.mapSes F).X₁.homology n :=
  H.PA.isoLeftDerivedObj F n

/-- `ProjectiveResolution.isoLeftDerivedObj` for `S.X₂`, at the same spelling. -/
def isoPB (n : ℕ) :
    (F.leftDerived n).obj S.X₂ ≅ (H.mapSes F).X₂.homology n :=
  H.PB.isoLeftDerivedObj F n

/-- `ProjectiveResolution.isoLeftDerivedObj` for `S.X₃`, at the same spelling. -/
def isoPC (n : ℕ) :
    (F.leftDerived n).obj S.X₃ ≅ (H.mapSes F).X₃.homology n :=
  H.PC.isoLeftDerivedObj F n

/-- `Lₙ F` applied to `S.f` is computed by the horseshoe. -/
lemma map_f_eq (n : ℕ) :
    (F.leftDerived n).map S.f = (H.isoPA F n).hom ≫
      HomologicalComplex.homologyMap (H.mapSes F).f n ≫ (H.isoPB F n).inv :=
  Functor.leftDerived_map_eq F n S.f H.ι H.commι

/-- `Lₙ F` applied to `S.g` is computed by the horseshoe. -/
lemma map_g_eq (n : ℕ) :
    (F.leftDerived n).map S.g = (H.isoPB F n).hom ≫
      HomologicalComplex.homologyMap (H.mapSes F).g n ≫ (H.isoPC F n).inv :=
  Functor.leftDerived_map_eq F n S.g H.p H.commp

/-- The connecting morphism `Lₙ₊₁ F (S.X₃) ⟶ Lₙ F (S.X₁)` of a horseshoe: the connecting
morphism of the homology long exact sequence of the mapped horseshoe sequence, conjugated by
the comparison isomorphisms. -/
def δ (n : ℕ) :
    (F.leftDerived (n + 1)).obj S.X₃ ⟶ (F.leftDerived n).obj S.X₁ :=
  (H.isoPC F (n + 1)).hom ≫
    (H.mapSes_shortExact F).δ (n + 1) n (down_rel_succ n) ≫ (H.isoPA F n).inv

include H in
/-- Exactness of `Lₙ F (S.X₁) ⟶ Lₙ F (S.X₂) ⟶ Lₙ F (S.X₃)`. -/
lemma exact_map (n : ℕ) : (S.map (F.leftDerived n)).Exact := by
  refine ShortComplex.exact_of_iso ?_ ((H.mapSes_shortExact F).homology_exact₂ n)
  exact ShortComplex.isoMk (H.isoPA F n).symm (H.isoPB F n).symm (H.isoPC F n).symm
    (by simp [H.map_f_eq]) (by simp [H.map_g_eq])

/-- The map into a connecting morphism composes to zero. -/
lemma map_g_comp_δ (n : ℕ) : (F.leftDerived (n + 1)).map S.g ≫ H.δ F n = 0 := by
  have h := (H.mapSes_shortExact F).comp_δ (n + 1) n (down_rel_succ n)
  rw [H.map_g_eq, δ]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [reassoc_of% h]
  simp

/-- A connecting morphism followed by the next map composes to zero. -/
lemma δ_comp_map_f (n : ℕ) : H.δ F n ≫ (F.leftDerived n).map S.f = 0 := by
  have h := (H.mapSes_shortExact F).δ_comp (n + 1) n (down_rel_succ n)
  rw [H.map_f_eq, δ]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [reassoc_of% h]
  simp

/-- Exactness of `Lₙ₊₁ F (S.X₂) ⟶ Lₙ₊₁ F (S.X₃) ⟶ Lₙ F (S.X₁)`. -/
lemma exact_δ₁ (n : ℕ) : (ShortComplex.mk _ _ (H.map_g_comp_δ F n)).Exact := by
  refine ShortComplex.exact_of_iso ?_
    ((H.mapSes_shortExact F).homology_exact₃ (n + 1) n (down_rel_succ n))
  exact ShortComplex.isoMk (H.isoPB F (n + 1)).symm (H.isoPC F (n + 1)).symm
    (H.isoPA F n).symm (by simp [H.map_g_eq]) (by simp [δ])

/-- Exactness of `Lₙ₊₁ F (S.X₃) ⟶ Lₙ F (S.X₁) ⟶ Lₙ F (S.X₂)`. -/
lemma exact_δ₂ (n : ℕ) : (ShortComplex.mk _ _ (H.δ_comp_map_f F n)).Exact := by
  refine ShortComplex.exact_of_iso ?_
    ((H.mapSes_shortExact F).homology_exact₁ (n + 1) n (down_rel_succ n))
  exact ShortComplex.isoMk (H.isoPC F (n + 1)).symm (H.isoPA F n).symm
    (H.isoPB F n).symm (by simp [δ]) (by simp [H.map_f_eq])

include H in
/-- The degree-zero end of the long exact sequence: `L₀ F (S.g)` is an epimorphism. -/
lemma epi_map_g : Epi ((F.leftDerived 0).map S.g) := by
  have := HorseshoeAux.epi_homologyMap_g_zero (H.mapSes_shortExact F)
  rw [H.map_g_eq]
  infer_instance

end Derived

section Naturality

variable {S T : ShortComplex C} (H : Horseshoe S) (K : Horseshoe T) (φ : S ⟶ T)

/-- The lift of `φ.τ₁` to the first resolutions. -/
def mapτ₁ : H.PA.complex ⟶ K.PA.complex :=
  ProjectiveResolution.lift φ.τ₁ H.PA K.PA

/-- `mapτ₁` covers `φ.τ₁`. -/
lemma mapτ₁_comm :
    mapτ₁ H K φ ≫ K.PA.π = H.PA.π ≫ (ChainComplex.single₀ C).map φ.τ₁ :=
  ProjectiveResolution.lift_commutes _ _ _

/-- A lift of `φ.τ₂` to the middle resolutions. -/
def mapτ₂Aux : H.PB.complex ⟶ K.PB.complex :=
  ProjectiveResolution.lift φ.τ₂ H.PB K.PB

/-- `mapτ₂Aux` covers `φ.τ₂`. -/
lemma mapτ₂Aux_comm :
    mapτ₂Aux H K φ ≫ K.PB.π = H.PB.π ≫ (ChainComplex.single₀ C).map φ.τ₂ :=
  ProjectiveResolution.lift_commutes _ _ _

/-- A homotopy between the two composites `H.ι ≫ mapτ₂Aux` and `mapτ₁ ≫ K.ι`. -/
def ιHomotopy :
    _root_.Homotopy (H.ι ≫ mapτ₂Aux H K φ) (mapτ₁ H K φ ≫ K.ι) :=
  ProjectiveResolution.liftHomotopy' K.PB.π _ _ (by
    simp only [Category.assoc]
    rw [mapτ₂Aux_comm, reassoc_of% H.commι, ← Functor.map_comp, K.commι,
      reassoc_of% mapτ₁_comm, ← Functor.map_comp, φ.comm₁₂])

/-- The corrected lift of `φ.τ₂`: `mapτ₂Aux` minus the null-homotopic map built from
`ιHomotopy` and the retraction of the splitting of `H`. -/
def mapτ₂ : H.PB.complex ⟶ K.PB.complex :=
  mapτ₂Aux H K φ - Homotopy.nullHomotopicMap
    fun i j => (H.splitting i).r ≫ (ιHomotopy H K φ).hom i j

/-- The square against the inclusions commutes. -/
lemma ι_comp_mapτ₂ : H.ι ≫ mapτ₂ H K φ = mapτ₁ H K φ ≫ K.ι := by
  have hk : (fun i j => H.ι.f i ≫ (H.splitting i).r ≫ (ιHomotopy H K φ).hom i j)
      = (ιHomotopy H K φ).hom := by
    funext i j
    rw [← Category.assoc, (H.splitting i).f_r, Category.id_comp]
  rw [mapτ₂, Preadditive.comp_sub, Homotopy.comp_nullHomotopicMap, hk,
    ← Homotopy.sub_eq_nullHomotopicMap (ιHomotopy H K φ)]
  abel

/-- `mapτ₂` covers `φ.τ₂`. -/
lemma mapτ₂_comm :
    mapτ₂ H K φ ≫ K.PB.π = H.PB.π ≫ (ChainComplex.single₀ C).map φ.τ₂ := by
  rw [mapτ₂, Preadditive.sub_comp, nullHomotopicMap_comp_π, sub_zero, mapτ₂Aux_comm]

/-- The degreewise component of the induced map on the third resolutions, obtained from
`mapτ₂` through the section of the splitting of `H`. -/
def mapτ₃f (n : ℕ) : H.PC.complex.X n ⟶ K.PC.complex.X n :=
  (H.splitting n).s ≫ (mapτ₂ H K φ).f n ≫ K.p.f n

/-- The square against the projections commutes degreewise. -/
lemma p_comp_mapτ₃f (n : ℕ) :
    H.p.f n ≫ mapτ₃f H K φ n = (mapτ₂ H K φ).f n ≫ K.p.f n := by
  have hι : H.ι.f n ≫ (mapτ₂ H K φ).f n = (mapτ₁ H K φ).f n ≫ K.ι.f n := by
    rw [← HomologicalComplex.comp_f, ι_comp_mapτ₂, HomologicalComplex.comp_f]
  rw [mapτ₃f, ← Category.assoc, (H.splitting n).g_s, Preadditive.sub_comp, Category.id_comp,
    Category.assoc, reassoc_of% hι, ι_comp_p_f K n]
  simp

/-- The induced map on the third resolutions. -/
def mapτ₃ : H.PC.complex ⟶ K.PC.complex where
  f n := mapτ₃f H K φ n
  comm' i j hij := by
    have hepi : Epi (H.p.f i) := (H.splitting i).epi_g
    rw [← cancel_epi (H.p.f i), ← Category.assoc, p_comp_mapτ₃f, Category.assoc,
      K.p.comm, ← Category.assoc, (mapτ₂ H K φ).comm, Category.assoc,
      ← p_comp_mapτ₃f, ← Category.assoc, ← H.p.comm, Category.assoc]

/-- The square against the projections commutes. -/
lemma p_comp_mapτ₃ : H.p ≫ mapτ₃ H K φ = mapτ₂ H K φ ≫ K.p :=
  HomologicalComplex.hom_ext _ _ fun n => by
    rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f]
    exact p_comp_mapτ₃f H K φ n

/-- `mapτ₃` covers `φ.τ₃`. -/
lemma mapτ₃_comm :
    mapτ₃ H K φ ≫ K.PC.π = H.PC.π ≫ (ChainComplex.single₀ C).map φ.τ₃ := by
  have := epi_p H
  rw [← cancel_epi H.p, reassoc_of% p_comp_mapτ₃, K.commp, reassoc_of% mapτ₂_comm,
    ← Functor.map_comp, reassoc_of% H.commp, ← Functor.map_comp, φ.comm₂₃]

/-- A morphism of short complexes lifts to a morphism of horseshoe sequences, on the nose. -/
def mapSesHom : H.ses ⟶ K.ses where
  τ₁ := mapτ₁ H K φ
  τ₂ := mapτ₂ H K φ
  τ₃ := mapτ₃ H K φ
  comm₁₂ := (ι_comp_mapτ₂ H K φ).symm
  comm₂₃ := (p_comp_mapτ₃ H K φ).symm

variable {D : Type u₂} [Category.{v₂} D] [Abelian D] (F : C ⥤ D) [F.Additive]

/-- The image of `mapSesHom` under an additive functor. -/
def mapSesMap : H.mapSes F ⟶ K.mapSes F :=
  (F.mapHomologicalComplex (ComplexShape.down ℕ)).mapShortComplex.map (mapSesHom H K φ)

variable [HasProjectiveResolutions C]

/-- `Lₙ F` applied to `φ.τ₁` is computed by `mapτ₁`. -/
lemma map_τ₁_eq (n : ℕ) :
    (F.leftDerived n).map φ.τ₁ = (H.isoPA F n).hom ≫
      HomologicalComplex.homologyMap (mapSesMap H K φ F).τ₁ n ≫ (K.isoPA F n).inv :=
  Functor.leftDerived_map_eq F n φ.τ₁ (mapτ₁ H K φ) (mapτ₁_comm H K φ)

/-- `Lₙ F` applied to `φ.τ₃` is computed by `mapτ₃`. -/
lemma map_τ₃_eq (n : ℕ) :
    (F.leftDerived n).map φ.τ₃ = (H.isoPC F n).hom ≫
      HomologicalComplex.homologyMap (mapSesMap H K φ F).τ₃ n ≫ (K.isoPC F n).inv :=
  Functor.leftDerived_map_eq F n φ.τ₃ (mapτ₃ H K φ) (mapτ₃_comm H K φ)

/-- **Naturality of the connecting morphism.**  A morphism of short complexes carrying one
horseshoe to another commutes with the connecting morphisms. -/
lemma δ_naturality (n : ℕ) :
    (F.leftDerived (n + 1)).map φ.τ₃ ≫ K.δ F n
      = H.δ F n ≫ (F.leftDerived n).map φ.τ₁ := by
  have hnat := HomologicalComplex.HomologySequence.δ_naturality (mapSesMap H K φ F)
    (H.mapSes_shortExact F) (K.mapSes_shortExact F) (n + 1) n (down_rel_succ n)
  rw [map_τ₃_eq H K φ F (n + 1), map_τ₁_eq H K φ F n, δ, δ]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [reassoc_of% hnat]

end Naturality

end Horseshoe

end CategoryTheory.ShortComplex

namespace CategoryTheory.Functor

variable {C : Type u} [Category.{v} C] [Abelian C] [EnoughProjectives C]
  {D : Type u₂} [Category.{v₂} D] [Abelian D] (F : C ⥤ D) [F.Additive]

open ShortComplex

/-- **The connecting morphism of the left derived functors.**  For a short exact sequence
`S` in an abelian category with enough projectives and an additive functor `F`, this is the
morphism `Lₙ₊₁ F (S.X₃) ⟶ Lₙ F (S.X₁)` of the long exact sequence, read off the horseshoe
`horseshoe hS`. -/
def leftDerivedδ {S : ShortComplex C} (hS : S.ShortExact) (n : ℕ) :
    (F.leftDerived (n + 1)).obj S.X₃ ⟶ (F.leftDerived n).obj S.X₁ :=
  (horseshoe hS).δ F n

/-- Exactness of `Lₙ F (S.X₁) ⟶ Lₙ F (S.X₂) ⟶ Lₙ F (S.X₃)`. -/
lemma leftDerived_exact {S : ShortComplex C} (hS : S.ShortExact) (n : ℕ) :
    (S.map (F.leftDerived n)).Exact :=
  (horseshoe hS).exact_map F n

/-- The map into a connecting morphism composes to zero. -/
lemma leftDerived_map_g_comp_δ {S : ShortComplex C} (hS : S.ShortExact) (n : ℕ) :
    (F.leftDerived (n + 1)).map S.g ≫ F.leftDerivedδ hS n = 0 :=
  (horseshoe hS).map_g_comp_δ F n

/-- A connecting morphism followed by the next map composes to zero. -/
lemma leftDerivedδ_comp_map_f {S : ShortComplex C} (hS : S.ShortExact) (n : ℕ) :
    F.leftDerivedδ hS n ≫ (F.leftDerived n).map S.f = 0 :=
  (horseshoe hS).δ_comp_map_f F n

/-- Exactness of `Lₙ₊₁ F (S.X₂) ⟶ Lₙ₊₁ F (S.X₃) ⟶ Lₙ F (S.X₁)`. -/
lemma leftDerived_exact_δ₁ {S : ShortComplex C} (hS : S.ShortExact) (n : ℕ) :
    (ShortComplex.mk _ _ (F.leftDerived_map_g_comp_δ hS n)).Exact :=
  (horseshoe hS).exact_δ₁ F n

/-- Exactness of `Lₙ₊₁ F (S.X₃) ⟶ Lₙ F (S.X₁) ⟶ Lₙ F (S.X₂)`. -/
lemma leftDerived_exact_δ₂ {S : ShortComplex C} (hS : S.ShortExact) (n : ℕ) :
    (ShortComplex.mk _ _ (F.leftDerivedδ_comp_map_f hS n)).Exact :=
  (horseshoe hS).exact_δ₂ F n

/-- The degree-zero end of the long exact sequence: `L₀ F (S.g)` is an epimorphism. -/
lemma epi_leftDerivedZero_map_g {S : ShortComplex C} (hS : S.ShortExact) :
    Epi ((F.leftDerived 0).map S.g) :=
  (horseshoe hS).epi_map_g F

/-- **Naturality of the connecting morphism** in the short exact sequence. -/
lemma leftDerivedδ_naturality {S T : ShortComplex C} (hS : S.ShortExact) (hT : T.ShortExact)
    (φ : S ⟶ T) (n : ℕ) :
    (F.leftDerived (n + 1)).map φ.τ₃ ≫ F.leftDerivedδ hT n
      = F.leftDerivedδ hS n ≫ (F.leftDerived n).map φ.τ₁ :=
  Horseshoe.δ_naturality (horseshoe hS) (horseshoe hT) φ F n

end CategoryTheory.Functor

end
