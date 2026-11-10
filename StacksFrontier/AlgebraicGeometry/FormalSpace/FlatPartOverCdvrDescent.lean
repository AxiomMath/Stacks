module

public import Mathlib.CategoryTheory.Sites.Subsheaf
public import StacksFrontier.AlgebraicGeometry.FormalSpace.ClosedImmersionDescent
public import StacksFrontier.AlgebraicGeometry.FormalSpace.ColimitOfAlgebraicSpaces
public import StacksFrontier.AlgebraicGeometry.FormalSpace.EtaleCover
public import StacksFrontier.AlgebraicGeometry.FormalSpace.FibreProductFormalBase
public import StacksFrontier.AlgebraicGeometry.FormalSpace.FlatPartOverCdvr
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RigEtaleLocalCharacterization
public import StacksFrontier.AlgebraicGeometry.FormalSpace.SetTheoreticDescentRepresentable
public import StacksFrontier.AlgebraicGeometry.FormalSpace.SourceCoverImpliesEveryDiagramNoetherian
public import StacksFrontier.CategoryTheory.Sites.QuasiCompact.CoveringSetOfObjects
public import StacksFrontier.CategoryTheory.Sites.QuasiCompact.LocallySurjectiveTransfer
import all StacksFrontier.AlgebraicGeometry.FormalSpace.ClosedImmersionMcQuillan

/-!
# Gluing the flat parts over a complete discrete valuation ring

This file proves the three sheaf-theoretic steps of the proof of **Stacks 0GD8** that do not
involve the base ring: that the factorization of a morphism through a closed immersion descends
along an affine étale covering of its source, that closed subspaces of the members of an atlas
which are mutually compatible glue to a closed subspace, and that a locally Noetherian formal
algebraic space flat over the base is covered by Noetherian affine formal algebraic spaces flat
over the base which map to the members of a given atlas of the target.

## Main results

* `AlgebraicGeometry.FormalSpace.mono_of_isClosedImmersion`: a closed immersion of fppf sheaves
  is a monomorphism, which is the monomorphism property of Stacks 0AQB used in the source.
* `CategoryTheory.Sheaf.exists_comp_eq_of_isLocallySurjective_sigmaDesc`: a morphism of sheaves
  of sets factors through a monomorphism as soon as the members of a family surjecting onto its
  source do.
* `AlgebraicGeometry.FormalSpace.factorizationDescendsAlongAffineEtaleCover`: the descent of a
  factorization through a closed immersion along an affine étale covering.
* `AlgebraicGeometry.FormalSpace.isFlat_comp_of_isRepresentableEtale`: flatness over the base is
  inherited along a representable étale morphism, directly from Definition 0GCC.
* `AlgebraicGeometry.FormalSpace.flatPartsDescend`: the gluing step.
* `AlgebraicGeometry.FormalSpace.hasFlatAffineCoverOfFlat`: the covering of a test object.

## Implementation notes

The source glues the flat parts `X'ᵢ ⟶ Xᵢ` as the quotient of `∐ X'ᵢ` by the étale equivalence
relation `∐ X'ᵢ ×_X X'ⱼ`. Here the quotient is realized directly as the image sheaf of the map
`∐ X'ᵢ ⟶ X`, which is a subsheaf of `X`; the observation of the source that
`X'ᵢ ×_X Xⱼ ⟶ Xⱼ` factors through `X'ⱼ` is exactly what identifies the base change of that
subsheaf along `Xⱼ ⟶ X` with `X'ⱼ`. Being a closed immersion then descends from the members of
the atlas by the descent step of Stacks 0GHY
(`AlgebraicGeometry.FormalSpace.isClosedImmersion_of_locallySurjectiveFamily`), so neither
Spaces, Theorem 02WW nor Bootstrap, Lemma 046J is needed.

## References

* [Stacks Project, Tag 0AQB](https://stacks.math.columbia.edu/tag/0AQB)
* [Stacks Project, Tag 0GCC](https://stacks.math.columbia.edu/tag/0GCC)
* [Stacks Project, Tag 0GD8](https://stacks.math.columbia.edu/tag/0GD8)
* [Stacks Project, Tag 0GHY](https://stacks.math.columbia.edu/tag/0GHY)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace CategoryTheory.Sheaf

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

/-- **Factorizations through a monomorphism descend along a surjection of sheaves.** Let
`m : Z ⟶ Y` be a monomorphism of sheaves of sets and `b : Q ⟶ Y` a morphism. If a family
`wₖ : Wₖ ⟶ Q` induces a surjection of sheaves `∐ Wₖ ⟶ Q` and each `wₖ ≫ b` factors through `m`,
then `b` factors through `m`: the base change of `m` along `b` is a monomorphism through which
the surjection `∐ Wₖ ⟶ Q` factors, hence an isomorphism. -/
theorem exists_comp_eq_of_isLocallySurjective_sigmaDesc
    {Z Y Q : Sheaf J (Type max u v)} (m : Z ⟶ Y) [Mono m] (b : Q ⟶ Y) {K : Type*}
    {W : K → Sheaf J (Type max u v)} [HasCoproduct W]
    (wk : ∀ k, W k ⟶ Q) (hw : IsLocallySurjective (Limits.Sigma.desc wk))
    (h : ∀ k, ∃ r : W k ⟶ Z, r ≫ m = wk k ≫ b) : ∃ r : Q ⟶ Z, r ≫ m = b := by
  choose r hr using h
  have hfac : Limits.Sigma.desc wk =
      Limits.Sigma.desc (fun k ↦ pullback.lift (r k) (wk k) (hr k)) ≫ pullback.snd m b :=
    Limits.Sigma.hom_ext _ _ fun k ↦ by simp only [Limits.Sigma.ι_comp_desc,
      Limits.Sigma.ι_comp_desc_assoc, pullback.lift_snd]
  have : Epi (Limits.Sigma.desc wk) := (isLocallySurjective_iff_epi _).1 hw
  have : Epi (pullback.snd m b) := by
    rw [hfac] at this
    exact epi_of_epi (Limits.Sigma.desc fun k ↦ pullback.lift (r k) (wk k) (hr k)) _
  have : IsIso (pullback.snd m b) := isIso_of_mono_of_epi _
  exact ⟨inv (pullback.snd m b) ≫ pullback.fst m b, by simp [pullback.condition]⟩

end CategoryTheory.Sheaf

namespace AlgebraicGeometry.FormalSpace

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Closed immersions are monomorphisms, and factorizations through them descend -/

/-- **A closed immersion of fppf sheaves is a monomorphism**, being a closed immersion into its
target in the sense of the sheafified Yoneda embedding, whose base changes along represented
points are closed immersions of schemes, hence monomorphisms. This is the monomorphism property
of **Stacks 0AQB** for closed immersions, used in the proof of Stacks 0GD8. -/
theorem mono_of_isClosedImmersion {X Y : FppfSheaf B S hS} (f : X ⟶ Y)
    (hf : IsClosedImmersion B S hS f) : Mono f :=
  mono_of_isClosedImmersionInto f (isClosedImmersionInto_of_isClosedImmersion B S hS f hf)

/-- **The descent of a factorization through a closed immersion along an affine étale
covering.** If every member of an affine étale covering of `Y` maps to `X'` compatibly with
`q : Y ⟶ X`, then `q` itself factors through the closed immersion `ι : X' ⟶ X`, since `ι` is a
monomorphism and the covering is a surjection of sheaves. This is the last step of the proof of
Stacks 0GD8. -/
theorem factorizationDescendsAlongAffineEtaleCover :
    FactorizationDescendsAlongAffineEtaleCover B S hS := by
  intro X' X Y ι q hι J W w hW h
  let _ : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
  have := mono_of_isClosedImmersion B S hS ι hι
  exact Sheaf.exists_comp_eq_of_isLocallySurjective_sigmaDesc ι q w hW.2.2 h

/-! ### Flatness along representable étale morphisms -/

/-- **Flatness over the base is inherited along a representable étale morphism.** If
`f : X ⟶ Y` is flat in the sense of Definition 0GCC and `w : W ⟶ X` is representable by
algebraic spaces and étale, then `w ≫ f` is flat: an affine étale chart of `W` composed with `w`
is an affine étale chart of `X`, so every chart square of `w ≫ f` is one of `f`. -/
theorem isFlat_comp_of_isRepresentableEtale {W X Y : FppfSheaf B S hS} {w : W ⟶ X}
    {f : X ⟶ Y} (hw : IsRepresentableEtale B S hS w) (hf : IsFlat B S hS f) :
    IsFlat B S hS (w ≫ f) := by
  intro U V hU hV a b t ha hb hae hbe hsq
  have hcomp := IsRepresentableEtale.comp B S hS ⟨ha, hae⟩ hw
  exact hf U V hU hV (a ≫ w) b t hcomp.1 hb hcomp.2 hbe (by simpa using hsq)

/-- A Noetherian affine formal algebraic space is locally Noetherian, being its own one-member
atlas as in Definition 0AIM. -/
theorem isLocallyNoetherian_of_isAffine_of_isNoetherian {X : FppfSheaf B S hS}
    (hX : IsAffineFormalAlgebraicSpace B S hS X) (hXn : IsNoetherian B S hS X) :
    IsLocallyNoetherian B S hS X := by
  let : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
  refine ⟨isFormalAlgebraicSpace_of_isAffineFormalAlgebraicSpace B S hS hX,
    PUnit.{u + 2}, fun _ ↦ X, fun _ ↦ 𝟙 X, fun _ ↦ hX,
    fun _ ↦ isRepresentableEtale_id B S hS X, ?_, fun _ ↦ hXn⟩
  have : IsSplitEpi (Sigma.desc fun _ : PUnit.{u + 2} ↦ 𝟙 X) :=
    ⟨⟨Sigma.ι (fun _ : PUnit.{u + 2} ↦ X) PUnit.unit, by simp⟩⟩
  exact (Sheaf.isLocallySurjective_iff_epi _).2 inferInstance

/-- **A covering of the members of a covering is a covering.** If `{eᵢ : Eᵢ ⟶ Y}` induces a
surjection of sheaves and, for each `i`, so does `{wᵢₖ : Wᵢₖ ⟶ Eᵢ}`, then so does the family of
composites `{wᵢₖ ≫ eᵢ}`. -/
theorem isLocallySurjective_sigmaDesc_comp_sigmaDesc {Y : FppfSheaf B S hS} {I : Type (u + 1)}
    {E : I → FppfSheaf B S hS} (e : ∀ i, E i ⟶ Y) {K : I → Type (u + 1)}
    {W : ∀ i, K i → FppfSheaf B S hS} (wk : ∀ i k, W i k ⟶ E i)
    (he : letI : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) :=
        Sheaf.instHasColimitsOfSize
      Sheaf.IsLocallySurjective (Sigma.desc e))
    (hw : ∀ i, letI : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) :=
        Sheaf.instHasColimitsOfSize
      Sheaf.IsLocallySurjective (Sigma.desc (wk i))) :
    letI : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
    Sheaf.IsLocallySurjective (Sigma.desc fun s : Σ i, K i ↦ wk s.1 s.2 ≫ e s.1) := by
  let _ : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
  have hfac : (Sigma.desc fun s : Σ i, K i ↦ wk s.1 s.2 ≫ Sigma.ι E s.1) ≫ Sigma.desc e =
      Sigma.desc fun s : Σ i, K i ↦ wk s.1 s.2 ≫ e s.1 :=
    Sigma.hom_ext _ _ fun s ↦ by simp
  have h₁ := (Sheaf.isLocallySurjective_iff_epi _).1
    (Sheaf.isLocallySurjective_sigmaDesc_sigma (fun s : Σ i, K i ↦ wk s.1 s.2) hw)
  have h₂ := (Sheaf.isLocallySurjective_iff_epi _).1 he
  rw [Sheaf.isLocallySurjective_iff_epi, ← hfac]
  exact epi_comp _ _

/-- **Charts of a base change along a representable étale morphism.** Let `e : E ⟶ Y` be
representable étale and `g : G ⟶ Y` a morphism from a locally Noetherian formal algebraic space
such that `g ≫ c` is flat for some `c : Y ⟶ T`, and suppose the fibre product `E ×_Y G` is a
formal algebraic space. Then `E ×_Y G` has an affine étale covering by Noetherian affine formal
algebraic spaces, each representable étale over `G` and flat over `T` through `E`.

This is the observation of the proof of Stacks 0GD8 that the charts of `X'ᵢ ×_X Xⱼ` and of
`Xᵢ ×_X Y` are Noetherian and flat over the base: the projection of the fibre product to `G`
is representable étale, being a base change of `e`. -/
theorem exists_noetherian_flat_cover_pullback {G E Y T : FppfSheaf B S hS} (e : E ⟶ Y)
    (g : G ⟶ Y) (c : Y ⟶ T) (he : IsRepresentableEtale B S hS e)
    (hP : IsFormalAlgebraicSpace B S hS (pullback e g)) (hG : IsLocallyNoetherian B S hS G)
    (hflat : IsFlat B S hS (g ≫ c)) :
    ∃ (K : Type (u + 1)) (W : K → FppfSheaf B S hS) (wk : ∀ k, W k ⟶ pullback e g),
      IsAffineEtaleCover B S hS W wk ∧ (∀ k, IsNoetherian B S hS (W k)) ∧
        (∀ k, IsRepresentableEtale B S hS (wk k ≫ pullback.snd e g)) ∧
        ∀ k, IsFlat B S hS ((wk k ≫ pullback.fst e g) ≫ e ≫ c) := by
  let _ : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
  obtain ⟨-, K, W, wk, hWaff, hWet, hWsurj⟩ := hP
  have hsnd : ∀ k, IsRepresentableEtale B S hS (wk k ≫ pullback.snd e g) := fun k ↦
    IsRepresentableEtale.comp B S hS (hWet k) (isRepresentableEtale_pullback_snd B S hS e g he)
  refine ⟨K, W, wk, ⟨hWaff, hWet, hWsurj⟩, fun k ↦
    isNoetherian_of_isRepresentableEtale_of_isLocallyNoetherian B S hS hG _ (hWaff k) (hsnd k),
    hsnd, fun k ↦ ?_⟩
  rw [show (wk k ≫ pullback.fst e g) ≫ e ≫ c = (wk k ≫ pullback.snd e g) ≫ g ≫ c by
    simp only [Category.assoc, pullback.condition_assoc]]
  exact isFlat_comp_of_isRepresentableEtale B S hS (hsnd k) hflat

/-! ### The covering of a test object -/

variable {A : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  (D : QuotientSystem B S hS A)

omit [IsTopologicalRing A] in
/-- **The covering of a test object in the proof of Stacks 0GD8.** Let `X` be a formal algebraic
space over `S` with a morphism `p : X ⟶ Spf A`. A locally Noetherian formal algebraic space `Y`
flat over `A` and mapping to `X` admits an affine étale covering by Noetherian affine formal
algebraic spaces flat over `A` which map to the members of a given affine étale covering of `X`,
compatibly with `Y ⟶ X`.

The members are the charts of the fibre products `Xᵢ ×_X Y`, which are formal algebraic spaces
by Stacks 0AJ3; they are representable étale over `Y`, being charts of a base change of
`Xᵢ ⟶ X`, hence Noetherian and flat over `A`, and they cover `Y` because a surjection of sheaves
stays one after base change and after refinement by coverings. -/
theorem hasFlatAffineCoverOfFlat {X : FppfSheaf B S hS} (hX : IsFormalAlgebraicSpace B S hS X)
    (p : X ⟶ formalSpectrum D) : HasFlatAffineCoverOfFlat B S hS D p := by
  intro I U u hU Y q hY hqflat
  let _ : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
  have hP : ∀ i, IsFormalAlgebraicSpace B S hS (pullback (u i) q) := fun i ↦
    isFormalAlgebraicSpace_pullback_of_isFormalAlgebraicSpace B S hS (u i) q hX
      (isFormalAlgebraicSpace_of_isAffineFormalAlgebraicSpace B S hS (hU.1 i)) hY.1
  choose K W wk hWcov hWnoeth hWet hWflat using fun i ↦
    exists_noetherian_flat_cover_pullback B S hS (u i) q p (hU.2.1 i) (hP i) hY hqflat
  refine ⟨Σ i, K i, fun s ↦ W s.1 s.2, fun s ↦ wk s.1 s.2 ≫ pullback.snd (u s.1) q,
    fun s ↦ s.1, fun s ↦ wk s.1 s.2 ≫ pullback.fst (u s.1) q,
    ⟨fun s ↦ (hWcov s.1).1 s.2, fun s ↦ hWet s.1 s.2,
      isLocallySurjective_sigmaDesc_comp_sigmaDesc B S hS (fun i ↦ pullback.snd (u i) q) wk
        (Sheaf.isLocallySurjective_sigmaDesc_pullback_snd q u hU.2.2)
        (fun i ↦ (hWcov i).2.2)⟩,
    fun s ↦ hWnoeth s.1 s.2, fun s ↦ by simp [pullback.condition],
    fun s ↦ by simpa using hWflat s.1 s.2⟩

/-! ### The gluing step -/

/-- **The flat parts of two members of an atlas are compatible.** Let `uᵢ : Uᵢ ⟶ X` be
representable étale with `Uᵢ` affine, and let `zⱼ : Zⱼ ⟶ Uⱼ` be a map from a Noetherian affine
formal algebraic space with `Zⱼ ⟶ Uⱼ ⟶ X ⟶ T` flat. If a monomorphism `zᵢ : Zᵢ ⟶ Uᵢ` receives
every map into `Uᵢ` out of a Noetherian affine formal algebraic space flat over `T` through
`Uᵢ`, then the projection `Uᵢ ×_X Zⱼ ⟶ Uᵢ` factors through `zᵢ`.

This is the step `X'ᵢ ×_X Xⱼ ⟶ Xⱼ` factors through `X'ⱼ` of the proof of Stacks 0GD8, with the
roles of the two indices exchanged: the fibre product is covered by Noetherian affine charts
flat over `T`, each of which factors through `zᵢ`, and the factorizations descend. -/
theorem exists_comp_eq_pullback_fst_of_universal {X Ui Uj Zi Zj T : FppfSheaf B S hS}
    (hX : IsFormalAlgebraicSpace B S hS X) (c : X ⟶ T) (ui : Ui ⟶ X) (uj : Uj ⟶ X)
    (zi : Zi ⟶ Ui) (zj : Zj ⟶ Uj) (hUi : IsAffineFormalAlgebraicSpace B S hS Ui)
    (hui : IsRepresentableEtale B S hS ui) (hZj : IsAffineFormalAlgebraicSpace B S hS Zj)
    (hZjn : IsNoetherian B S hS Zj) [Mono zi] (hflat : IsFlat B S hS (zj ≫ uj ≫ c))
    (huniv : ∀ (W : FppfSheaf B S hS) (w : W ⟶ Ui), IsAffineFormalAlgebraicSpace B S hS W →
      IsNoetherian B S hS W → IsFlat B S hS (w ≫ ui ≫ c) → ∃ r : W ⟶ Zi, r ≫ zi = w) :
    ∃ r : pullback ui (zj ≫ uj) ⟶ Zi, r ≫ zi = pullback.fst ui (zj ≫ uj) := by
  let _ : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
  obtain ⟨K, W, wk, hWcov, hWnoeth, -, hWflat⟩ :=
    exists_noetherian_flat_cover_pullback B S hS ui (zj ≫ uj) c hui
      (isFormalAlgebraicSpace_pullback_of_isFormalAlgebraicSpace B S hS ui (zj ≫ uj) hX
        (isFormalAlgebraicSpace_of_isAffineFormalAlgebraicSpace B S hS hUi)
        (isFormalAlgebraicSpace_of_isAffineFormalAlgebraicSpace B S hS hZj))
      (isLocallyNoetherian_of_isAffine_of_isNoetherian B S hS hZj hZjn) (by simpa using hflat)
  exact Sheaf.exists_comp_eq_of_isLocallySurjective_sigmaDesc zi _ wk hWcov.2.2 fun k ↦
    huniv (W k) (wk k ≫ pullback.fst ui (zj ≫ uj)) (hWcov.1 k) (hWnoeth k)
      (by simpa using hWflat k)

variable {A : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  (D : QuotientSystem B S hS A)

omit [IsTopologicalRing A] in
/-- **The gluing step of Stacks 0GD8.** Let `X` be a formal algebraic space over `S` with a
morphism `p : X ⟶ Spf A`. Closed immersions `zᵢ : Zᵢ ⟶ Uᵢ` into the members of an affine étale
covering of `X`, with `Zᵢ` Noetherian affine and flat over `A`, each receiving every map into
`Uᵢ` from a Noetherian affine formal algebraic space flat over `A`, glue to a closed immersion
`ι : X' ⟶ X` of formal algebraic spaces for which the `Zᵢ` form an affine étale covering of `X'`
compatibly with the covering of `X`.

`X'` is the image sheaf of `∐ Zᵢ ⟶ X`. By the compatibility of the `Zᵢ`
(`AlgebraicGeometry.FormalSpace.exists_comp_eq_pullback_fst_of_universal`) the base change of
`X' ⟶ X` along `Uᵢ ⟶ X` is `Zᵢ ⟶ Uᵢ`, a closed immersion; being a closed immersion descends
along the covering by Stacks 0GHY, and the `Zᵢ ⟶ X'` are representable étale as base changes of
the `Uᵢ ⟶ X`, and jointly surjective by construction of the image. -/
theorem flatPartsDescend {X : FppfSheaf B S hS} (hX : IsFormalAlgebraicSpace B S hS X)
    (p : X ⟶ formalSpectrum D) : FlatPartsDescend B S hS D p := by
  intro I U u hU Z z hZaff hZnoeth hZclosed hZflat hZuniv
  let _ : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
  have hzmono : ∀ i, Mono (z i) := fun i ↦ mono_of_isClosedImmersion B S hS (z i) (hZclosed i)
  let f : ∐ Z ⟶ X := Sigma.desc fun i ↦ z i ≫ u i
  let ι : Sheaf.image f ⟶ X := Sheaf.imageι f
  let ζ : ∀ i, Z i ⟶ Sheaf.image f := fun i ↦ Sigma.ι Z i ≫ Sheaf.toImage f
  have hζι : ∀ i, ζ i ≫ ι = z i ≫ u i := fun i ↦ by simp [ζ, ι, f, Sheaf.toImage_ι]
  have hsurj : Sheaf.IsLocallySurjective (Sigma.desc ζ) := by
    rw [show Sigma.desc ζ = Sheaf.toImage f from Sigma.hom_ext _ _ fun i ↦ by simp [ζ],
      Sheaf.isLocallySurjective_iff_epi]
    infer_instance
  -- the base change of `ι` along `uᵢ` is `zᵢ`
  have hfac : ∀ i, ∃ c : pullback ι (u i) ⟶ Z i, c ≫ z i = pullback.snd ι (u i) := fun i ↦ by
    refine Sheaf.exists_comp_eq_of_isLocallySurjective_sigmaDesc (z i) _
      (fun j ↦ pullback.snd (ζ j) (pullback.fst ι (u i)))
      (Sheaf.isLocallySurjective_sigmaDesc_pullback_snd _ ζ hsurj) fun j ↦ ?_
    obtain ⟨c, hc⟩ := exists_comp_eq_pullback_fst_of_universal B S hS hX p (u i) (u j) (z i)
      (z j) (hU.1 i) (hU.2.1 i) (hZaff j) (hZnoeth j) (hZflat j) (hZuniv i)
    refine ⟨pullback.lift (pullback.snd (ζ j) (pullback.fst ι (u i)) ≫ pullback.snd ι (u i))
      (pullback.fst (ζ j) (pullback.fst ι (u i))) ?_ ≫ c, ?_⟩
    · rw [Category.assoc, ← pullback.condition, ← pullback.condition_assoc, hζι]
    · rw [Category.assoc, hc, pullback.lift_fst]
  choose c hc using hfac
  let e : ∀ i, Z i ≅ pullback ι (u i) := fun i ↦
    { hom := pullback.lift (ζ i) (z i) (hζι i)
      inv := c i
      hom_inv_id := by
        rw [← cancel_mono (z i), Category.assoc, hc, pullback.lift_snd, Category.id_comp]
      inv_hom_id := by
        apply pullback.hom_ext
        · rw [← cancel_mono ι]
          simp only [Category.assoc, Category.id_comp, pullback.lift_fst_assoc, hζι,
            reassoc_of% (hc i)]
          exact pullback.condition.symm
        · rw [Category.assoc, pullback.lift_snd, hc, Category.id_comp] }
  have hsnd : ∀ i, IsClosedImmersion B S hS (pullback.snd ι (u i)) := fun i ↦
    have : IsIso (e i).inv := Iso.isIso_inv (e i)
    isClosedImmersion_of_isPullback B S hS (fst := (e i).inv) (g := 𝟙 (U i))
      (IsPullback.of_horiz_isIso ⟨(hc i).trans (Category.comp_id _).symm⟩) (hZclosed i)
  have hιclosed : IsClosedImmersion B S hS ι :=
    isClosedImmersion_of_locallySurjectiveFamily B S hS I U u hU.2.2 hsnd
  have hζet : ∀ i, IsRepresentableEtale B S hS (ζ i) := fun i ↦ by
    have : IsIso (e i).hom := Iso.isIso_hom (e i)
    rw [show ζ i = (e i).hom ≫ pullback.fst ι (u i) from (pullback.lift_fst _ _ _).symm]
    exact (isRepresentableEtale_of_isIso B S hS _).comp B S hS
      (isRepresentableEtale_pullback_fst B S hS ι (u i) (hU.2.1 i))
  exact ⟨Sheaf.image f, ι, ζ, isFormalAlgebraicSpace_of_etaleCover B S hS _ Z ζ
    (fun i ↦ isFormalAlgebraicSpace_of_isAffineFormalAlgebraicSpace B S hS (hZaff i)) hζet hsurj
    (SetTheoreticDescent.satisfiesSetTheoreticCondition_of_representable_over B S hS ι
      hιclosed.1 hX.1), hιclosed, ⟨hZaff, hζet, hsurj⟩, hζι⟩

end AlgebraicGeometry.FormalSpace

end
