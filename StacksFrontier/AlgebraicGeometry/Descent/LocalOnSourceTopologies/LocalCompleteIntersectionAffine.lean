module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Conormal.ConormalSequenceExact
public import StacksFrontier.AlgebraicGeometry.Conormal.SequenceExact
public import StacksFrontier.AlgebraicGeometry.Descent.LocalOnSourceTopologies.LocalCompleteIntersection
public import StacksFrontier.AlgebraicGeometry.Descent.LocalOnTarget.RegularImmersionFpqc
public import StacksFrontier.AlgebraicGeometry.Descent.MorphismProperty.FaithfullyFlatRing
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BigSitesPushforward.ClosedImmersionCoverings
public import StacksFrontier.AlgebraicGeometry.Flatness.StalkIdealSheaf
public import StacksFrontier.AlgebraicGeometry.ModuleLimits.AffineHom
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.LocalCompleteIntersection.Affine
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.LocalCompleteIntersection.ImmersionIntoSmooth
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.LocalCompleteIntersection.Perfect
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.LocalCompleteIntersection.SmoothTarget
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.LocalCompleteIntersection.Syntomic
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.RegularImmersion.SmoothTargetPermanence
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.RegularImmersion.SplitConormalKoszulRegular
public import StacksFrontier.AlgebraicGeometry.Morphisms.Syntomic.Properties
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PseudoCoherent.LocalCompleteIntersection.ImmersionIntoSmooth
public import StacksFrontier.AlgebraicGeometry.Spaces.RegularImmersionComposition

/-!
# The syntomic source locality of the Koszul property

A morphism of affine schemes is a local complete intersection morphism as soon as its
precomposition with a surjective syntomic morphism of affine schemes is. This is the one
assertion the syntomic case of **Stacks 036H** still needed, so **Stacks 069P** is proved here:
the property of being a local complete intersection morphism is syntomic local on the source.

The *étale* case of Stacks 069P does not go through this file at all:
`AlgebraicGeometry.isLocalCompleteIntersectionMorphism_isLocalAtSource_etale` of
`StacksFrontier.AlgebraicGeometry.Descent.LocalOnSourceTopologies.LocalCompleteIntersectionEtale`
proves it unconditionally, because a cover by base changes along *smooth* morphisms makes
Stacks 069G apply directly and no conormal sequence is needed.

## Main results

* `AlgebraicGeometry.isKoszulRegularImmersion_of_flat_covers_image`: a closed immersion is
  Koszul-regular as soon as its base changes along a family of flat morphisms locally of finite
  presentation whose images cover the closed subscheme are.
* `AlgebraicGeometry.exists_koszulRegular_ambient_factorization`: the padding step, a
  Koszul-regular closed immersion of a scheme Koszul over the base into a relative affine space
  over a given affine target, through which the structure morphism factors.
* `AlgebraicGeometry.inf_map_eq_mul_ker_appTop_of_flat`: for a closed immersion `j : W ⟶ T`
  over a flat `q : W ⟶ P`, the ideal of `j` meets an ideal extended from `P` in the product of
  the two, which is the ideal-theoretic form of the splitting of the conormal sequence.
* `AlgebraicGeometry.stalkIdeal_eq_map_germ_top`: the stalk of the defining ideal sheaf of a
  closed immersion of affine schemes is the extension along the germ of the ideal on global
  sections.
* `AlgebraicGeometry.isKoszulRegularImmersion_of_flat_pullback`: part (3) of Stacks 068Z for the
  one shape of square the proof produces, with no conormal hypothesis left.
* `AlgebraicGeometry.exists_conormal_retraction_of_inf_le`: the module-theoretic retraction
  that the splitting of the conormal sequence of Stacks 062S amounts to.
* `AlgebraicGeometry.conormalRetraction_of_flat_pullback`: that retraction read as a morphism of
  sheaves of modules, by the affine computation of Stacks 01R3.
* `AlgebraicGeometry.splitConormalOfFlatPullback`: the conormal input of Stacks 062S that part
  (3) of Stacks 068Z asks for, for the one shape of square the proof of Stacks 069P produces.
* `AlgebraicGeometry.isLocalCompleteIntersectionMorphism_of_surjective_syntomic_of_isAffine`:
  the affine descent.
* `AlgebraicGeometry.isLocalAtSource_syntomic_isLocalCompleteIntersectionMorphism`:
  **Stacks 069P**.

## The conormal input, by two routes

Stacks applies part (3) of Stacks 068Z to a closed immersion `k : Z ⟶ W` obtained by flat base
change of a closed immersion `i : X ⟶ P`, followed by a closed immersion `j : W ⟶ T` over `P`,
and that lemma asks for the conormal sequence of Stacks 062S to be exact and locally split.
Everything that asks for is available for these squares, and both halves come from the same
place: `AlgebraicGeometry.inf_map_eq_mul_ker_appTop_of_flat` says that the two ideals of
`Γ(T, ⊤)` in sight — the one cutting out `W` and the one extended from the ideal of `X` — cut
out `Z` together and are transverse.

* `AlgebraicGeometry.splitConormalOfFlatPullback` is the full input. Exactness at the middle
  term and surjectivity on the right hold for any pair of immersions
  (`Stacks.Immersion.conormalSequence_exact`,
  `Stacks.Immersion.epi_conormalSequenceRightMap`); transversality retracts the left-hand map
  globally, by `AlgebraicGeometry.exists_cotangent_extension_of_inf_le` read through the affine
  computation of Stacks 01R3 part (2).
* `AlgebraicGeometry.isKoszulRegularImmersion_of_flat_pullback` draws part (3) of Stacks 068Z
  without that input, through the one consequence of it the proof of Stacks 068Z uses — the
  injectivity of the map of cotangent fibres `I_x / 𝔪_x I_x ⟶ J_x / 𝔪_x J_x`, which
  `Stacks.AlgebraicGeometry.isKoszulRegularImmersion_of_comp_of_mem_smul_stalkIdeal` takes
  instead, and which is the same transversality read on the stalk at `x`. It is this route the
  affine descent below uses, because it does not need `j` locally of finite presentation;
  `AlgebraicGeometry.isKoszulRegularImmersion_of_flat_pullback_of_splitConormal` is the other
  one.

## Implementation notes

Stacks takes the disjoint union of the members of the syntomic cover produced by Stacks 00T0 in
order to argue with a single ambient affine space. That is avoided here: Koszul-regularity of a
closed immersion is read off a family of flat base changes covering the image by Stacks 0694, so
each member of the cover can be treated separately and no coproduct is formed. The cover itself
is the syntomic case of Stacks 04E3, which is the geometric form of Stacks 00T0.

The ambient affine space of the padding step is produced from a finite polynomial presentation
of the ring map on global sections rather than from Stacks 04II, so that the immersion obtained
is closed and its composite with the projection is the given morphism on the nose.

## References

* [The Stacks Project, Lemma 35.26.4 (036H)](https://stacks.math.columbia.edu/tag/036H)
* [The Stacks Project, Lemma 10.136.18 (00T0)](https://stacks.math.columbia.edu/tag/00T0)
* [The Stacks Project, Lemma 29.26.10 (01UA)](https://stacks.math.columbia.edu/tag/01UA)
* [The Stacks Project, Lemma 29.32.5 (01R3)](https://stacks.math.columbia.edu/tag/01R3)
* [The Stacks Project, Lemma 35.14.1 (02KK)](https://stacks.math.columbia.edu/tag/02KK)
* [The Stacks Project, Lemma 31.21.5 (062S)](https://stacks.math.columbia.edu/tag/062S)
* [The Stacks Project, Lemma 31.22.8 (068Z)](https://stacks.math.columbia.edu/tag/068Z)
* [The Stacks Project, Lemma 35.23.34 (0694)](https://stacks.math.columbia.edu/tag/0694)
* [The Stacks Project, Lemma 31.23.12 (0693)](https://stacks.math.columbia.edu/tag/0693)
* [The Stacks Project, Lemma 37.62.20 (069P)](https://stacks.math.columbia.edu/tag/069P)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.AlgebraicGeometry.RegularIdealSheaf

universe u

namespace AlgebraicGeometry

/-! ### Stacks 069G without its hypothesis -/

/-- **Stacks 069G**, unconditionally: an immersion over `S` of an open of the source of a local
complete intersection morphism into a scheme smooth over `S` is Koszul-regular. -/
@[stacks 069G, sga "6 VIII 1.2"]
theorem isKoszulRegularImmersion_of_koszul {X S P : Scheme.{u}} (f : X ⟶ S) (π : P ⟶ S)
    [Smooth π] (U : X.Opens) (i : U.toScheme ⟶ P) [IsImmersion i]
    (hf : IsLocalCompleteIntersectionMorphism f) (hi : U.ι ≫ f = i ≫ π) :
    IsKoszulRegularImmersion i :=
  isKoszulRegularImmersion_of_isLocalCompleteIntersectionMorphism koszulRegularCompSmooth f π U i
    hf hi

/-- A Koszul morphism factored as an immersion followed by a smooth morphism has Koszul-regular
immersion part. This is Stacks 069G read at the whole source rather than at an open of it. -/
theorem isKoszulRegularImmersion_of_koszul_comp_smooth {Z W Y : Scheme.{u}} (k : Z ⟶ W)
    (π : W ⟶ Y) [IsImmersion k] [Smooth π]
    (hk : IsLocalCompleteIntersectionMorphism (k ≫ π)) : IsKoszulRegularImmersion k := by
  have htop : IsKoszulRegularImmersion ((⊤ : Z.Opens).ι ≫ k) :=
    isKoszulRegularImmersion_of_koszul (k ≫ π) π ⊤ ((⊤ : Z.Opens).ι ≫ k) hk
      (by simp only [Category.assoc])
  have h := Stacks.AlgebraicGeometry.isKoszulRegularImmersion_comp (Scheme.topIso Z).inv
    ((⊤ : Z.Opens).ι ≫ k)
    (isKoszulRegularImmersion_of_isOpenImmersion (Scheme.topIso Z).inv) htop
  simpa only [← Category.assoc, Scheme.toIso_inv_ι, Category.id_comp] using h

/-! ### Charts into a relative affine space -/

/-- A morphism of affine schemes locally of finite presentation is a closed immersion into a
finite-dimensional relative affine space over its target, followed by the projection. -/
@[sga "6 VIII 1.1" "more general"]
theorem exists_closedImmersion_affineSpace_of_lfp {T V : Scheme.{u}} (g : T ⟶ V) [IsAffine T]
    [IsAffine V] [LocallyOfFinitePresentation g] :
    ∃ n : ℕ, ∃ h : T ⟶ AffineSpace (ULift.{u} (Fin n)) V,
      IsClosedImmersion h ∧
        h ≫ (AffineSpace (ULift.{u} (Fin n)) V ↘ V) = g := by
  let φ := (g.appTop).hom
  let _ : Algebra (↑(Γ(V, ⊤))) (↑(Γ(T, ⊤))) := φ.toAlgebra
  have hfp : φ.FinitePresentation := Scheme.Hom.finitePresentation_appTop g
  have hft : RingHom.FiniteType φ := RingHom.FiniteType.of_finitePresentation hfp
  let _ : Algebra.FiniteType (↑(Γ(V, ⊤))) (↑(Γ(T, ⊤))) := hft
  obtain ⟨n, p, hp⟩ :=
    (Algebra.FiniteType.iff_quotient_mvPolynomial'').mp
      (inferInstance : Algebra.FiniteType (↑(Γ(V, ⊤))) (↑(Γ(T, ⊤))))
  let R := Γ(V, ⊤)
  let A := Γ(T, ⊤)
  let e : MvPolynomial (Fin n) R ≃ₐ[R] MvPolynomial (ULift.{u} (Fin n)) R :=
    MvPolynomial.renameEquiv _ (Equiv.ulift.{u, 0} (α := Fin n)).symm
  let p' : MvPolynomial (ULift.{u} (Fin n)) R →ₐ[R] A := p.comp e.symm.toAlgHom
  have hp' : Function.Surjective p' := by
    intro x
    obtain ⟨y, hy⟩ := hp x
    refine ⟨e y, ?_⟩
    change p (e.symm (e y)) = x
    rw [AlgEquiv.symm_apply_apply]
    exact hy
  let η : CommRingCat.of (MvPolynomial (ULift.{u} (Fin n)) R) ⟶ CommRingCat.of A :=
    CommRingCat.ofHom p'.toRingHom
  let h : T ⟶ AffineSpace (ULift.{u} (Fin n)) V :=
    T.isoSpec.hom ≫ Spec.map η ≫ (AffineSpace.SpecIso (ULift.{u} (Fin n)) R).inv ≫
      AffineSpace.map (ULift.{u} (Fin n)) V.isoSpec.inv
  let _ : IsClosedImmersion (Spec.map η) := IsClosedImmersion.spec_of_surjective η hp'
  let _ : IsIso (AffineSpace.map (ULift.{u} (Fin n)) V.isoSpec.inv) := by
    change IsIso ((AffineSpace.functor.obj (Opposite.op (ULift.{u} (Fin n)))).map V.isoSpec.inv)
    infer_instance
  have hh : IsClosedImmersion h := by
    dsimp only [h]
    infer_instance
  have hcoeff : CommRingCat.ofHom
      (MvPolynomial.C : R →+* MvPolynomial (ULift.{u} (Fin n)) R) ≫ η = CommRingCat.ofHom φ := by
    ext r
    exact p'.commutes r
  have hbase : h ≫ (AffineSpace (ULift.{u} (Fin n)) V ↘ V) = g := by
    dsimp only [h]
    calc
      T.isoSpec.hom ≫ Spec.map η ≫ (AffineSpace.SpecIso (ULift.{u} (Fin n)) R).inv ≫
          AffineSpace.map (ULift.{u} (Fin n)) V.isoSpec.inv ≫
            (AffineSpace (ULift.{u} (Fin n)) V ↘ V) =
        T.isoSpec.hom ≫ Spec.map η ≫ (AffineSpace.SpecIso (ULift.{u} (Fin n)) R).inv ≫
          (AffineSpace (ULift.{u} (Fin n)) (Spec R) ↘ Spec R) ≫ V.isoSpec.inv := by
            simp only [AffineSpace.map_over]
      _ = T.isoSpec.hom ≫ Spec.map η ≫
          ((AffineSpace.SpecIso (ULift.{u} (Fin n)) R).inv ≫
            (AffineSpace (ULift.{u} (Fin n)) (Spec R) ↘ Spec R)) ≫ V.isoSpec.inv := by
            simp only [Category.assoc]
      _ = T.isoSpec.hom ≫ Spec.map η ≫ Spec.map (CommRingCat.ofHom MvPolynomial.C) ≫
          V.isoSpec.inv := by rw [AffineSpace.SpecIso_inv_over]
      _ = T.isoSpec.hom ≫ Spec.map
          (CommRingCat.ofHom (MvPolynomial.C : R →+* MvPolynomial (ULift.{u} (Fin n)) R) ≫ η) ≫
          V.isoSpec.inv := by
            have hs := (Spec.map_comp
              (CommRingCat.ofHom
                (MvPolynomial.C : R →+* MvPolynomial (ULift.{u} (Fin n)) R)) η).symm
            simpa only [Category.assoc] using
              congrArg (fun k => T.isoSpec.hom ≫ k ≫ V.isoSpec.inv) hs
      _ = T.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom φ) ≫ V.isoSpec.inv := by rw [hcoeff]
      _ = g := by
            have hphi : CommRingCat.ofHom φ = g.appTop := by ext; rfl
            rw [hphi]
            change T.toSpecΓ ≫ Spec.map g.appTop ≫ V.isoSpec.inv = g
            calc
              _ = (g ≫ V.toSpecΓ) ≫ V.isoSpec.inv := by
                exact (congrArg (fun k => k ≫ V.isoSpec.inv)
                  (Scheme.toSpecΓ_naturality g)).symm
              _ = g := by simp [Scheme.isoSpec]
  exact ⟨n, h, hh, hbase⟩

/-- An open immersion of schemes is a local complete intersection morphism, being Koszul-regular
into its target. -/
private theorem koszul_of_isOpenImmersion' {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j] :
    IsLocalCompleteIntersectionMorphism j := by
  intro x
  refine ⟨AlgebraicGeometry.finiteTypeAt_of_locallyOfFiniteType j x, ⊤, by simp, X,
    (⊤ : X.Opens).ι, j,
    inferInstance, ?_, inferInstance, rfl⟩
  exact isKoszulRegularImmersion_of_isOpenImmersion (⊤ : X.Opens).ι

/-- **The padding step.** A Koszul morphism of affine schemes `q : W ⟶ P` whose composite with a
smooth `π : P ⟶ Y` makes `k ≫ q ≫ π` Koszul admits a closed immersion into a relative affine
space over `P` which is Koszul-regular, through which `q` factors, and for which `k` followed by
it is Koszul-regular as well. -/
@[sga "6 VIII 1.1" "more general"]
theorem exists_koszulRegular_ambient_factorization {Z W P Y : Scheme.{u}} [IsAffine W]
    [IsAffine P] (k : Z ⟶ W) [IsClosedImmersion k] (q : W ⟶ P) (π : P ⟶ Y) [Smooth π]
    (hq : IsLocalCompleteIntersectionMorphism q)
    (hk : IsLocalCompleteIntersectionMorphism (k ≫ q ≫ π)) :
    ∃ (m : ℕ) (j : W ⟶ AffineSpace (ULift.{u} (Fin m)) P) (_ : IsClosedImmersion j),
      j ≫ (AffineSpace (ULift.{u} (Fin m)) P ↘ P) = q ∧
      LocallyOfFinitePresentation j ∧
      IsKoszulRegularImmersion j ∧ IsKoszulRegularImmersion (k ≫ j) := by
  have : LocallyOfFinitePresentation q :=
    locallyOfFinitePresentation_of_isLocalCompleteIntersectionMorphism hq
  obtain ⟨m, j, hj, hbase⟩ := exists_closedImmersion_affineSpace_of_lfp q
  let _ : IsClosedImmersion j := hj
  have hρ : Smooth (AffineSpace (ULift.{u} (Fin m)) P ↘ P) := smooth_affineSpace_over _ _
  have hjq : IsLocalCompleteIntersectionMorphism
      (j ≫ (AffineSpace (ULift.{u} (Fin m)) P ↘ P)) := by rw [hbase]; exact hq
  have hjlci := isLocalCompleteIntersectionMorphism_of_comp_of_smooth j
    (AffineSpace (ULift.{u} (Fin m)) P ↘ P) hjq
  refine ⟨m, j, hj, hbase,
    locallyOfFinitePresentation_of_isLocalCompleteIntersectionMorphism hjlci,
    isKoszulRegularImmersion_of_koszul_comp_smooth j
      (AffineSpace (ULift.{u} (Fin m)) P ↘ P) hjq, ?_⟩
  apply isKoszulRegularImmersion_of_koszul_comp_smooth (k ≫ j)
    ((AffineSpace (ULift.{u} (Fin m)) P ↘ P) ≫ π)
  change IsLocalCompleteIntersectionMorphism
    (k ≫ j ≫ (AffineSpace (ULift.{u} (Fin m)) P ↘ P) ≫ π)
  rw [← Category.assoc j (AffineSpace (ULift.{u} (Fin m)) P ↘ P) π, hbase]
  exact hk

/-- A morphism of affine schemes locally of finite presentation which is a Koszul-regular closed
immersion into a relative affine space over its target is a local complete intersection
morphism. -/
theorem isLocalCompleteIntersectionMorphism_of_koszulRegular_affineImmersion
    {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y] (f : X ⟶ Y) (n : ℕ)
    (i : X ⟶ AffineSpace (ULift.{u} (Fin n)) Y) [IsClosedImmersion i]
    (hbase : i ≫ (AffineSpace (ULift.{u} (Fin n)) Y ↘ Y) = f)
    [LocallyOfFiniteType f] (hreg : IsKoszulRegularImmersion i) :
    IsLocalCompleteIntersectionMorphism f := by
  intro x
  have : Smooth (AffineSpace (ULift.{u} (Fin n)) Y ↘ Y) := smooth_affineSpace_over _ _
  have hreg' : IsKoszulRegularImmersion ((⊤ : X.Opens).ι ≫ i) :=
    Stacks.AlgebraicGeometry.isKoszulRegularImmersion_comp (⊤ : X.Opens).ι i
      (isKoszulRegularImmersion_of_isOpenImmersion (⊤ : X.Opens).ι) hreg
  refine ⟨AlgebraicGeometry.finiteTypeAt_of_locallyOfFiniteType f x, ⊤, by simp,
    AffineSpace (ULift.{u} (Fin n)) Y, (⊤ : X.Opens).ι ≫ i,
    (AffineSpace (ULift.{u} (Fin n)) Y ↘ Y), inferInstance, hreg', inferInstance, ?_⟩
  rw [Category.assoc, hbase]

/-! ### Reading Koszul-regularity off a flat cover of the image -/

/-- An immersion is Koszul-regular as soon as its base changes along the members of an fpqc
covering are quasi-compact Koszul-regular immersions. -/
private theorem isKoszulRegularImmersion_of_forall_pullbackSnd {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsImmersion f] {R : Presieve Y} (hR : R ∈ Scheme.fpqcPrecoverage Y)
    (h : ∀ {U : Scheme.{u}} {g : U ⟶ Y} [HasPullback f g], R g →
      (∃ hs : IsImmersion (pullback.snd f g), @IsKoszulRegularImmersion _ _ _ hs) ∧
        QuasiCompact (pullback.snd f g)) :
    IsKoszulRegularImmersion f :=
  (isLocalAtTarget_koszulRegularImmersion_inf_quasiCompact_fpqc.of_forall_pullbackSnd
    (f := f) hR fun hg => h hg).1.2

/-- **Stacks 0694 in the form the descent uses.** A closed immersion is Koszul-regular as soon
as, for a family of flat morphisms locally of finite presentation whose images cover the closed
subscheme, every base change of it along a member of the family is Koszul-regular. -/
theorem isKoszulRegularImmersion_of_flat_covers_image {Z X : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] {ι : Type u} (Y : ι → Scheme.{u}) (q : ∀ j, Y j ⟶ X)
    (hflat : ∀ j, Flat (q j)) (hlfp : ∀ j, LocallyOfFinitePresentation (q j))
    (hcover : ∀ z : Z, ∃ j, i.base z ∈ Set.range (q j).base)
    (hreg : ∀ j, IsKoszulRegularImmersion (pullback.snd i (q j))) :
    IsKoszulRegularImmersion i := by
  classical
  let U : X.Opens := ⟨(Set.range i.base)ᶜ, i.isClosedEmbedding.isClosed_range.isOpen_compl⟩
  let V : Option ι → Scheme.{u} := fun j => j.elim U.toScheme Y
  let p : ∀ j, V j ⟶ X := fun j => match j with
    | none => U.ι
    | some j => q j
  have hcov : Presieve.ofArrows V p ∈ Scheme.fppfPrecoverage X := by
    apply (Scheme.ofArrows_mem_precoverage_iff _).mpr
    constructor
    · intro x
      by_cases hx : x ∈ Set.range i.base
      · obtain ⟨z, rfl⟩ := hx
        obtain ⟨j, hj⟩ := hcover z
        exact ⟨some j, hj⟩
      · exact ⟨none, ⟨⟨x, hx⟩, rfl⟩⟩
    · intro j
      cases j with
      | none => exact ⟨inferInstanceAs (Flat U.ι),
          inferInstanceAs (LocallyOfFinitePresentation U.ι)⟩
      | some j => exact ⟨hflat j, hlfp j⟩
  refine isKoszulRegularImmersion_of_forall_pullbackSnd i
    (Scheme.fppfPrecoverage_le_fpqcPrecoverage _ hcov) ?_
  rintro _ _ _ ⟨j⟩
  cases j with
  | some j => exact ⟨⟨inferInstance, hreg j⟩, inferInstance⟩
  | none =>
    have : IsEmpty ↑(pullback i U.ι) := by
      apply Scheme.isEmpty_pullback
      rw [Set.disjoint_left]
      intro x hx hy
      obtain ⟨y, rfl⟩ := hy
      exact y.property hx
    exact ⟨⟨inferInstance, isKoszulRegularImmersion_of_isOpenImmersion (pullback.snd i U.ι)⟩,
      inferInstance⟩

/-! ### The ideal-theoretic content of the splitting of the conormal sequence -/

/-- **The intersection condition splits the conormal inclusion for a sum of ideals.** If two
ideals `I` and `J` of a ring meet inside `I * J + J ^ 2`, then the conormal module of `I ⊔ J`
retracts onto `J` modulo `I * J + J ^ 2`, compatibly with the inclusion of `J`. -/
theorem exists_conormal_retraction_of_inf_le {R : Type*} [CommRing R] (I J : Ideal R)
    (h : J ⊓ I ≤ I * J ⊔ J ^ 2) :
    ∃ r : (I ⊔ J).Cotangent →ₗ[R] (J ⧸ Submodule.comap J.subtype (I * J ⊔ J ^ 2)),
      ∀ x : J, r ((I ⊔ J).toCotangent
        (Submodule.inclusion (le_sup_right : J ≤ I ⊔ J) x)) = Submodule.Quotient.mk x := by
  let N := Submodule.comap J.subtype (I * J ⊔ J ^ 2)
  let a : I →ₗ[R] ↥(I ⊔ J) := Submodule.inclusion le_sup_left
  let b : J →ₗ[R] ↥(I ⊔ J) := Submodule.inclusion le_sup_right
  let σ := a.coprod b
  have hσ : Function.Surjective σ := by
    intro z
    obtain ⟨x, hx, y, hy, hxy⟩ := Submodule.mem_sup.mp z.property
    exact ⟨(⟨x, hx⟩, ⟨y, hy⟩), Subtype.ext hxy⟩
  let ρ : I × J →ₗ[R] J ⧸ N := N.mkQ.comp (LinearMap.snd R I J)
  have hker : LinearMap.ker σ ≤ LinearMap.ker ρ := by
    intro x hx
    change ρ x = 0
    apply (Submodule.Quotient.mk_eq_zero N).mpr
    apply h
    refine ⟨x.2.property, ?_⟩
    have he : (x.1 : R) + (x.2 : R) = 0 := congrArg Subtype.val hx
    have hy : (x.2 : R) = -(x.1 : R) := eq_neg_of_add_eq_zero_right he
    change (x.2 : R) ∈ I
    rw [hy]
    exact I.neg_mem x.1.property
  let s := (LinearMap.ker σ).liftQ ρ hker ∘ₗ
    (σ.quotKerEquivOfSurjective hσ).symm.toLinearMap
  have hs (x : I) (y : J) : s (a x + b y) = N.mkQ y := by
    change ((LinearMap.ker σ).liftQ ρ hker)
      ((σ.quotKerEquivOfSurjective hσ).symm (σ (x, y))) = _
    rw [LinearMap.quotKerEquivOfSurjective_symm_apply, Submodule.liftQ_apply]
    rfl
  have hsprod (x y : ↥(I ⊔ J)) : s (x * y) = 0 := by
    obtain ⟨xi, hxi, xj, hxj, hx⟩ := Submodule.mem_sup.mp x.property
    obtain ⟨yi, hyi, yj, hyj, hy⟩ := Submodule.mem_sup.mp y.property
    have hi : xi * yi + xi * yj + xj * yi ∈ I :=
      I.add_mem (I.add_mem (I.mul_mem_right _ hxi) (I.mul_mem_right _ hxi))
        (I.mul_mem_left _ hyi)
    have hj : xj * yj ∈ J := J.mul_mem_left _ hyj
    have he : x * y = a ⟨_, hi⟩ + b ⟨_, hj⟩ := by
      apply Subtype.ext
      change (x : R) * (y : R) = xi * yi + xi * yj + xj * yi + xj * yj
      rw [← hx, ← hy]
      ring
    rw [he, hs]
    apply (Submodule.Quotient.mk_eq_zero N).mpr
    change xj * yj ∈ I * J ⊔ J ^ 2
    exact (le_sup_right : J ^ 2 ≤ I * J ⊔ J ^ 2) (show xj * yj ∈ J ^ 2 by
      rw [pow_two]; exact Ideal.mul_mem_mul hxj hyj)
  refine ⟨Ideal.Cotangent.lift s hsprod, ?_⟩
  intro x
  rw [Ideal.Cotangent.lift_toCotangent]
  change s (b x) = N.mkQ x
  simpa only [map_zero, zero_add] using hs 0 x

/-- A linear map out of an ideal `J` kills the elements of `I * J` as soon as the scalars in `I`
act as zero on its target. -/
theorem linearMap_eq_zero_of_mem_ideal_mul {R M : Type*} [CommRing R] [AddCommGroup M]
    [Module R M] (I J : Ideal R) (u : J →ₗ[R] M) (hu : ∀ a ∈ I, ∀ m : M, a • m = 0) (x : J)
    (hx : (x : R) ∈ I * J) : u x = 0 := by
  rw [← Ideal.smul_eq_mul] at hx
  have h := Submodule.smul_induction_on (p := fun y : R => ∃ hy : y ∈ J, u ⟨y, hy⟩ = 0) hx
    (fun a ha b hb => ⟨J.mul_mem_left a hb, by
      change u (a • (⟨b, hb⟩ : J)) = 0
      rw [map_smul]
      exact hu a ha _⟩)
    (fun a b ha hb => by
      obtain ⟨haJ, ha0⟩ := ha
      obtain ⟨hbJ, hb0⟩ := hb
      refine ⟨J.add_mem haJ hbJ, ?_⟩
      change u ((⟨a, haJ⟩ : J) + ⟨b, hbJ⟩) = 0
      rw [map_add, ha0, hb0, add_zero])
  exact h.choose_spec

/-- **Extension of a map off `J` to the conormal module of `I ⊔ J`.** Under the intersection
condition, every linear map out of `J` whose target is killed by `I ⊔ J` extends to the conormal
module of `I ⊔ J` along the inclusion of `J`. -/
theorem exists_cotangent_extension_of_inf_le {R M : Type*} [CommRing R] [AddCommGroup M]
    [Module R M] (I J : Ideal R) (h : J ⊓ I ≤ I * J ⊔ J ^ 2) (u : J →ₗ[R] M)
    (hu : ∀ a ∈ I ⊔ J, ∀ m : M, a • m = 0) :
    ∃ v : (I ⊔ J).Cotangent →ₗ[R] M, ∀ x : J,
      v ((I ⊔ J).toCotangent (Submodule.inclusion le_sup_right x)) = u x := by
  obtain ⟨r, hr⟩ := exists_conormal_retraction_of_inf_le I J h
  let N := Submodule.comap J.subtype (I * J ⊔ J ^ 2)
  have hN : N ≤ LinearMap.ker u := by
    intro x hx
    change u x = 0
    apply linearMap_eq_zero_of_mem_ideal_mul (I ⊔ J) J u hu x
    rw [Ideal.sup_mul, ← pow_two]
    exact hx
  refine ⟨N.liftQ u hN ∘ₗ r, fun x => ?_⟩
  rw [LinearMap.comp_apply, hr, Submodule.liftQ_apply]

/-- **Flatness makes the kernel meet an extended ideal in their product.** For ring maps
`a : A →+* R` and a surjection `b : R →+* S` with `b ∘ a` flat, the kernel of `b` meets the
extension of an ideal `I` of `A` exactly in the product of the two. -/
theorem ideal_inf_map_eq_mul_of_flat {A R S : Type u} [CommRing A] [CommRing R] [CommRing S]
    (a : A →+* R) (b : R →+* S) (hb : Function.Surjective b) (hflat : (b.comp a).Flat)
    (I : Ideal A) : RingHom.ker b ⊓ I.map a = I.map a * RingHom.ker b := by
  let _ : Algebra A R := a.toAlgebra
  let _ : Algebra A S := (b.comp a).toAlgebra
  let _ : Module.Flat A S := hflat
  let f : R →ₐ[A] S := ⟨b, fun _ => rfl⟩
  have hker : LinearMap.ker f.toLinearMap = (RingHom.ker b).restrictScalars A := rfl
  change RingHom.ker b ⊓ I.map (algebraMap A R) = I.map (algebraMap A R) * RingHom.ker b
  apply Submodule.restrictScalars_injective A
  rw [← Ideal.smul_eq_mul, Ideal.smul_restrictScalars, ← hker,
    ← LinearMap.ker_inf_smul_top_eq_smul_of_flat I f.toLinearMap hb, hker,
    Ideal.smul_top_eq_map]
  rfl

/-- **A pushout of a surjective ring map carries its kernel to the new kernel.** -/
theorem ker_eq_map_of_isPushout {R S T U : CommRingCat.{u}} (f : R ⟶ S) (g : R ⟶ T) (a : S ⟶ U)
    (b : T ⟶ U) (hsq : IsPushout f g a b) (hf : Function.Surjective f) :
    RingHom.ker b.hom = (RingHom.ker f.hom).map g.hom := by
  let I := (RingHom.ker f.hom).map g.hom
  have hle : I ≤ RingHom.ker b.hom := by
    rw [Ideal.map_le_iff_le_comap]
    intro x hx
    change b.hom (g.hom x) = 0
    rw [← show a.hom (f.hom x) = b.hom (g.hom x) from congr($(hsq.w) x)]
    rw [show f.hom x = 0 from hx, map_zero]
  let q : T ⟶ CommRingCat.of ((T : Type u) ⧸ I) := CommRingCat.ofHom (Ideal.Quotient.mk I)
  have hkerle : RingHom.ker f.hom ≤
      RingHom.ker ((Ideal.Quotient.mk I).comp g.hom) := fun x hx =>
    RingHom.mem_ker.mpr (Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_map_of_mem g.hom hx))
  let c : S ⟶ CommRingCat.of ((T : Type u) ⧸ I) := CommRingCat.ofHom
    (f.hom.liftOfSurjective hf ⟨(Ideal.Quotient.mk I).comp g.hom, hkerle⟩)
  have hc : f ≫ c = g ≫ q := by
    ext x
    exact RingHom.liftOfSurjective_comp_apply f.hom hf
      ⟨(Ideal.Quotient.mk I).comp g.hom, hkerle⟩ x
  let d := hsq.desc c q hc
  have hd : b ≫ d = q := hsq.inr_desc _ _ _
  apply le_antisymm _ hle
  intro x hx
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  change q.hom x = 0
  rw [← hd]
  change d.hom (b.hom x) = 0
  rw [show b.hom x = 0 from hx, map_zero]

/-- **The two ideals of the ambient affine scheme are transverse.** Let `i : X ⟶ P` be a closed
immersion of affine schemes, let `q : W ⟶ P` be flat with `W` affine, let `k : Z ⟶ W` be the base
change of `i` along `q`, and let `j : W ⟶ T` be a closed immersion with `j ≫ ρ = q` for some
`ρ : T ⟶ P` with `T` affine. Writing `I` for the extension to `Γ(T, ⊤)` along `ρ` of the ideal of
`i` and `J` for the ideal of `j`, the ideal of `k ≫ j` is `I ⊔ J` and `J ⊓ I = I * J`.

This is the whole of the splitting of the conormal sequence of Stacks 062S for this square:
feeding `J ⊓ I ≤ I * J ⊔ J ^ 2` to `AlgebraicGeometry.exists_conormal_retraction_of_inf_le`
produces the retraction of its left-hand map on global sections. -/
theorem inf_map_eq_mul_ker_appTop_of_flat {Z W X P T : Scheme.{u}} [IsAffine P] [IsAffine W]
    [IsAffine T] (i : X ⟶ P) [IsClosedImmersion i] (k : Z ⟶ W) [IsClosedImmersion k]
    (s : Z ⟶ X) (q : W ⟶ P) [Flat q] (hsq : IsPullback k s q i) (j : W ⟶ T)
    [IsClosedImmersion j] (ρ : T ⟶ P) (hbase : j ≫ ρ = q) :
    RingHom.ker (k ≫ j).appTop.hom =
        (RingHom.ker i.appTop.hom).map ρ.appTop.hom ⊔ RingHom.ker j.appTop.hom ∧
      RingHom.ker j.appTop.hom ⊓ (RingHom.ker i.appTop.hom).map ρ.appTop.hom =
        (RingHom.ker i.appTop.hom).map ρ.appTop.hom * RingHom.ker j.appTop.hom := by
  have : IsAffine X := (IsClosedImmersion.isAffine_surjective_of_isAffine i).1
  set I₀ := RingHom.ker i.appTop.hom with hI₀
  set I := I₀.map ρ.appTop.hom with hI
  set J := RingHom.ker j.appTop.hom with hJ
  have hker : RingHom.ker (k ≫ j).appTop.hom = I ⊔ J := by
    have hk := ker_eq_map_of_isPushout i.appTop q.appTop s.appTop k.appTop
      (isPushout_appTop_of_isPullback hsq).flip
      (IsClosedImmersion.isAffine_surjective_of_isAffine i).2
    rw [Scheme.Hom.comp_appTop, CommRingCat.hom_comp, ← RingHom.comap_ker, hk]
    rw [← hbase, Scheme.Hom.comp_appTop, CommRingCat.hom_comp, ← Ideal.map_map]
    exact Ideal.comap_map_of_surjective j.appTop.hom
      (IsClosedImmersion.isAffine_surjective_of_isAffine j).2 I
  refine ⟨hker, ?_⟩
  have hf : (j.appTop.hom.comp ρ.appTop.hom).Flat := by
    have hh : (j ≫ ρ).appTop.hom.Flat := by rw [hbase]; exact q.flat_appTop
    simpa only [Scheme.Hom.comp_appTop, CommRingCat.hom_comp] using hh
  exact ideal_inf_map_eq_mul_of_flat ρ.appTop.hom j.appTop.hom
    (IsClosedImmersion.isAffine_surjective_of_isAffine j).2 hf I₀

/-! ### Koszul-regularity of a flat base change -/

/-- **Transversality splits the cotangent fibre.** If `I ≤ m` and the two ideals `I` and `J` meet
inside `I * J`, then an element of `J` lying in `m (I ⊔ J)` already lies in `m J`.

Written `a = b + c` with `b ∈ m I` and `c ∈ m J`, the element `b = a - c` lies in `J`, hence in
`J ⊓ I ≤ I * J ≤ m * J`. -/
theorem mem_smul_of_mem_smul_sup {R : Type*} [CommRing R] {m I J : Ideal R}
    (hI : I ≤ m) (hinf : J ⊓ I ≤ I * J) {a : R} (haJ : a ∈ J) (ha : a ∈ m • (I ⊔ J)) :
    a ∈ m • J := by
  rw [Ideal.smul_eq_mul, Ideal.mul_sup] at ha
  obtain ⟨b, hb, c, hc, habc⟩ := Submodule.mem_sup.mp ha
  have hcJ : c ∈ J := Ideal.mul_le_right hc
  have hbI : b ∈ I := Ideal.mul_le_right hb
  have hbJ : b ∈ J := by
    have hba : b = a - c := by rw [← habc, add_sub_cancel_right]
    rw [hba]
    exact J.sub_mem haJ hcJ
  have hb' : b ∈ m * J := Ideal.mul_mono hI le_rfl (hinf ⟨hbJ, hbI⟩)
  rw [Ideal.smul_eq_mul, ← habc]
  exact Ideal.add_mem _ hb' hc

/-- The germ at a point of an affine scheme is a flat ring map, being a localization of the ring
of global sections at the prime of that point. -/
private theorem flat_germ_top {X : Scheme.{u}} [IsAffine X] (x : X) :
    (X.presheaf.germ (⊤ : X.Opens) x trivial).hom.Flat := by
  have hU : IsAffineOpen (⊤ : X.Opens) := isAffineOpen_top X
  let _ : Algebra Γ(X, ⊤) (X.presheaf.stalk x) :=
    X.presheaf.algebra_section_stalk (U := (⊤ : X.Opens)) ⟨x, trivial⟩
  have : IsLocalization.AtPrime (X.presheaf.stalk x) (hU.primeIdealOf ⟨x, trivial⟩).asIdeal :=
    hU.isLocalization_stalk _
  have : Module.Flat Γ(X, ⊤) (X.presheaf.stalk x) :=
    IsLocalization.flat _ (hU.primeIdealOf ⟨x, trivial⟩).asIdeal.primeCompl
  exact this

/-- **The stalk of the defining ideal sheaf of a closed immersion of affine schemes.** It is the
extension along the germ of the ideal cut out on global sections, the stalk map being the
localization of the map on global sections at the prime of the point. -/
theorem stalkIdeal_eq_map_germ_top {A B : Scheme.{u}} [IsAffine A] [IsAffine B] (f : A ⟶ B)
    [IsClosedImmersion f] (a : A) {b : B} (hb : f a = b) :
    Stacks.RingedSpace.stalkIdeal (X := B.toLocallyRingedSpace) (definingIdealOfHom f) b =
      (RingHom.ker f.appTop.hom).map (B.presheaf.germ (⊤ : B.Opens) b trivial).hom := by
  subst hb
  have happ : f.appLE (⊤ : B.Opens) (⊤ : A.Opens) le_top = f.appTop := Scheme.Hom.appLE_eq_app f
  have hsurj : Function.Surjective (f.appLE (⊤ : B.Opens) (⊤ : A.Opens) le_top).hom := by
    rw [happ]
    exact (IsClosedImmersion.isAffine_surjective_of_isAffine f).2
  rw [stalkIdeal_definingIdealOfHom_eq_ker f a,
    Stacks.Flatness.ker_stalkMap_eq_map_germ f (isAffineOpen_top B) (isAffineOpen_top A)
      le_top trivial trivial hsurj, happ]

/-- **The conormal input of Stacks 068Z for the squares the proof of Stacks 069P produces,
discharged.** Let `i : X ⟶ P` be a closed immersion of affine schemes, let `k : Z ⟶ W` be its
base change along a flat `q : W ⟶ P` with `W` affine, and let `j : W ⟶ T` be a closed immersion
into an affine scheme over `P`, say `j ≫ ρ = q`. If `j` and `k ≫ j` are Koszul-regular
immersions, then so is `k`.

This is what Stacks obtains from part (3) of Stacks 068Z, whose conormal hypothesis — exactness
and local splitness of the conormal sequence of Stacks 062S — is used there only through
injectivity of the map of cotangent fibres of `j` and `k ≫ j` at a point. That injectivity is
available here directly: writing `I` for the ideal extended to `Γ(T, ⊤)` along `ρ` from the ideal
of `i` and `J` for the ideal of `j`, `AlgebraicGeometry.inf_map_eq_mul_ker_appTop_of_flat` says
that the ideal of `k ≫ j` is `I ⊔ J`, and the same flatness argument run on the stalk at the
point — the stalk map of `j` is a surjection whose composite with the germ of `ρ` is flat, being
the germ of `q` — says that the two extended ideals meet in their product there. The ideal
extended from `P` is contained in the maximal ideal because it is contained in the ideal of
`k ≫ j`, so `AlgebraicGeometry.mem_smul_of_mem_smul_sup` applies and
`Stacks.AlgebraicGeometry.isKoszulRegularImmersion_of_comp_of_mem_smul_stalkIdeal` concludes. -/
theorem isKoszulRegularImmersion_of_flat_pullback {Z W X P T : Scheme.{u}} [IsAffine P]
    [IsAffine W] [IsAffine T] (i : X ⟶ P) [IsClosedImmersion i] (k : Z ⟶ W)
    [IsClosedImmersion k] (s : Z ⟶ X) (q : W ⟶ P) [Flat q] (hsq : IsPullback k s q i)
    (j : W ⟶ T) [IsClosedImmersion j] (ρ : T ⟶ P) (hbase : j ≫ ρ = q)
    (hj : IsKoszulRegularImmersion j) (hkj : IsKoszulRegularImmersion (k ≫ j)) :
    IsKoszulRegularImmersion k := by
  obtain ⟨hker, -⟩ := inf_map_eq_mul_ker_appTop_of_flat i k s q hsq j ρ hbase
  have hZ : IsAffine Z := (IsClosedImmersion.isAffine_surjective_of_isAffine (k ≫ j)).1
  refine Stacks.AlgebraicGeometry.isKoszulRegularImmersion_of_comp_of_mem_smul_stalkIdeal k j
    (fun z a ha hsmul => ?_) hj hkj
  have hpt : (k ≫ j) z = j (k z) := rfl
  set γ := (T.presheaf.germ (⊤ : T.Opens) (j (k z)) trivial).hom with hγ
  have hJ : Stacks.RingedSpace.stalkIdeal (X := T.toLocallyRingedSpace)
      (definingIdealOfHom j) (j (k z)) = (RingHom.ker j.appTop.hom).map γ :=
    stalkIdeal_eq_map_germ_top j (k z) rfl
  have hK : Stacks.RingedSpace.stalkIdeal (X := T.toLocallyRingedSpace)
      (definingIdealOfHom (k ≫ j)) (j (k z))
      = ((RingHom.ker i.appTop.hom).map ρ.appTop.hom).map γ ⊔
        (RingHom.ker j.appTop.hom).map γ := by
    rw [stalkIdeal_eq_map_germ_top (k ≫ j) z hpt, hker, Ideal.map_sup]
  have hIm : ((RingHom.ker i.appTop.hom).map ρ.appTop.hom).map γ ≤
      IsLocalRing.maximalIdeal (T.presheaf.stalk (j (k z))) := by
    refine le_trans (le_trans le_sup_left hK.ge) (IsLocalRing.le_maximalIdeal ?_)
    exact hpt ▸ stalkIdeal_definingIdealOfHom_ne_top (k ≫ j) z
  have hsurjst : Function.Surjective (j.stalkMap (k z)).hom := j.stalkMap_surjective (k z)
  have hcomp : (j.stalkMap (k z)).hom.comp (γ.comp ρ.appTop.hom)
      = (W.presheaf.germ (⊤ : W.Opens) (k z) trivial).hom.comp q.appTop.hom := by
    ext g
    show (j.stalkMap (k z)).hom (γ (ρ.appTop.hom g)) = _
    rw [hγ, Scheme.Hom.germ_stalkMap_apply j (⊤ : T.Opens) (k z) trivial (ρ.appTop g)]
    show (W.presheaf.germ (j ⁻¹ᵁ (⊤ : T.Opens)) (k z) trivial).hom
      (j.appTop.hom (ρ.appTop.hom g)) = _
    rw [show j.appTop.hom (ρ.appTop.hom g) = q.appTop.hom g from by
      rw [← hbase, Scheme.Hom.comp_appTop, CommRingCat.hom_comp]; rfl]
    rfl
  have hflat : ((j.stalkMap (k z)).hom.comp (γ.comp ρ.appTop.hom)).Flat := by
    rw [hcomp]
    exact RingHom.Flat.comp q.flat_appTop (flat_germ_top (k z))
  have hinfst := ideal_inf_map_eq_mul_of_flat (γ.comp ρ.appTop.hom) (j.stalkMap (k z)).hom
    hsurjst hflat (RingHom.ker i.appTop.hom)
  rw [← Ideal.map_map, (stalkIdeal_definingIdealOfHom_eq_ker j (k z)).symm.trans hJ] at hinfst
  rw [hK] at hsmul
  rw [hJ] at ha ⊢
  exact mem_smul_of_mem_smul_sup hIm hinfst.le ha hsmul

/-! ### The conormal sequence of a flat base change -/

/-- Restriction of sections along an endomorphism of an open is the identity: the only morphism
of opens from an open to itself is the identity. -/
private theorem val_map_eq_self {Z : Scheme.{u}} (M : Z.Modules) {U : Z.Opens}
    (f : op U ⟶ op U) (x : M.val.obj (op U)) : (M.val.map f).hom x = x := by
  rw [show f = 𝟙 (op U) from Subsingleton.elim _ _, PresheafOfModules.map_id]
  rfl

/-- **A closed immersion into an affine scheme is presented by its global kernel**, in the shape
the affine computation of Stacks 01R3 part (2) asks for: the scheme-theoretic intersection of
the source with the whole of the target is the spectrum of the quotient by that kernel. -/
private theorem exists_affine_quotient_presentation
    {Z X : Scheme.{u}} [IsAffine X] (j : Z ⟶ X) [IsClosedImmersion j]
    (J : Ideal Γ(X, ⊤)) (hJ : J = RingHom.ker j.appTop.hom) :
    ∃ e : pullback j (⊤ : X.Opens).ι ≅ Spec (.of (Γ(X, ⊤) ⧸ J)),
      pullback.snd j (⊤ : X.Opens).ι ≫ (isAffineOpen_top X).isoSpec.hom =
        e.hom ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) := by
  subst hJ
  have : IsAffine Z := (IsClosedImmersion.isAffine_surjective_of_isAffine j).1
  let er := RingHom.quotientKerEquivOfSurjective
    (IsClosedImmersion.isAffine_surjective_of_isAffine j).2
  let e : Z ≅ Spec (.of (Γ(X, ⊤) ⧸ RingHom.ker j.appTop.hom)) :=
    Z.isoSpec ≪≫ Scheme.Spec.mapIso er.toCommRingCatIso.op
  have : IsIso (⊤ : X.Opens).ι := by
    change IsIso (Scheme.topIso X).hom
    infer_instance
  refine ⟨asIso (pullback.fst j (⊤ : X.Opens).ι) ≪≫ e, ?_⟩
  have ht : (isAffineOpen_top X).isoSpec.hom = (⊤ : X.Opens).ι ≫ X.isoSpec.hom := by
    apply (cancel_epi (isAffineOpen_top X).isoSpec.inv).mp
    simp only [Iso.inv_hom_id, ← Category.assoc, IsAffineOpen.isoSpec_inv_ι,
      IsAffineOpen.fromSpec_top]
  rw [ht, ← Category.assoc, ← pullback.condition]
  simp only [Iso.trans_hom, asIso_hom, Category.assoc]
  congr 1
  dsimp [e]
  rw [Category.assoc, ← Scheme.isoSpec_hom_naturality]
  congr 1
  rw [← Spec.map_comp]
  congr 1

/-- **The transversality of two ideals retracts the left-hand map of the conormal sequence.**
Let `k : Z ⟶ W` and `j : W ⟶ T` be closed immersions with `T` affine, let `I` and `J` be ideals
of `Γ(T, ⊤)` with `I ⊔ J` inside the ideal of `k ≫ j` and `J ⊓ I ≤ I * J ⊔ J ^ 2`, and let the
scheme-theoretic intersections of `W` and of `Z` with `T` be cut out by `J` and by `I ⊔ J`. Then
the canonical map `k^* 𝒞_{W/T} ⟶ 𝒞_{Z/T}` of Stacks 01R4 admits a retraction.

`AlgebraicGeometry.exists_cotangent_extension_of_inf_le` extends the composite
`J ⟶ J/J² ⟶ Γ(k^* 𝒞_{W/T}, ⊤)` to the conormal module of `I ⊔ J`, which by the affine
computation of Stacks 01R3 part (2) — `Stacks.Conormal.affineConormalIsoCotangent` — is the
module of global sections of `𝒞_{Z/T}`; that extension is `Γ(T, ⊤)`-linear, hence
`Γ(Z, ⊤)`-linear because `Γ(T, ⊤) ⟶ Γ(Z, ⊤)` is surjective, so
`Stacks.AlgebraicGeometry.ModuleLimits.exists_hom_app_top_eq` turns it into a morphism of sheaves
of modules. That morphism retracts the canonical map because
`Stacks.Immersion.isInducedConormalSheafMap_immersionConormalSheafMap` computes the canonical map
on the generators `J.toCotangent a`, and two morphisms out of a quasi-coherent sheaf on an affine
scheme agreeing on global sections are equal. -/
@[sga "6 VIII 1.3" "(iii)"]
private theorem conormal_retraction_of_ideal_intersection
    {Z W T : Scheme.{u}} [IsAffine T] (k : Z ⟶ W) (j : W ⟶ T)
    [IsClosedImmersion k] [IsClosedImmersion j]
    (I J : Ideal Γ(T, ⊤)) (hIJ : J ⊓ I ≤ I * J ⊔ J ^ 2)
    (hker : I ⊔ J ≤ RingHom.ker (k ≫ j).appTop.hom)
    (eJ : pullback j (⊤ : T.Opens).ι ≅ Spec (.of (Γ(T, ⊤) ⧸ J)))
    (heJ : pullback.snd j (⊤ : T.Opens).ι ≫ (isAffineOpen_top T).isoSpec.hom =
      eJ.hom ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)))
    (eK : pullback (k ≫ j) (⊤ : T.Opens).ι ≅ Spec (.of (Γ(T, ⊤) ⧸ (I ⊔ J))))
    (heK : pullback.snd (k ≫ j) (⊤ : T.Opens).ι ≫ (isAffineOpen_top T).isoSpec.hom =
      eK.hom ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ⊔ J)))) :
    ∃ r : (Stacks.Conormal.conormalSheaf (k ≫ j) : Z.Modules) ⟶
        (Scheme.Modules.pullback k).obj (Stacks.Conormal.conormalSheaf j),
      Stacks.AlgebraicGeometry.conormalSequenceLeftMap k j ≫ r = 𝟙 _ := by
  classical
  have : IsAffine W := (IsClosedImmersion.isAffine_surjective_of_isAffine j).1
  have : IsAffine Z := (IsClosedImmersion.isAffine_surjective_of_isAffine k).1
  let F : W.Modules := Stacks.Conormal.conormalSheaf j
  let A : Z.Modules := (Scheme.Modules.pullback k).obj F
  let B : Z.Modules := Stacks.Conormal.conormalSheaf (k ≫ j)
  let α : A ⟶ B := Stacks.AlgebraicGeometry.conormalSequenceLeftMap k j
  have _ : F.IsQuasicoherent :=
    inferInstanceAs (Stacks.Conormal.conormalSheaf j).IsQuasicoherent
  have _ : A.IsQuasicoherent :=
    AlgebraicGeometry.SheafOfModules.modulePullback_isQuasicoherent k.toLRSHom.toShHom F
  have _ : B.IsQuasicoherent :=
    inferInstanceAs (Stacks.Conormal.conormalSheaf (k ≫ j)).IsQuasicoherent
  let R := Γ(T, ⊤)
  let _ : Module R Γ(F, ⊤) := Module.compHom Γ(F, ⊤) j.appTop.hom
  let _ : Module R Γ(A, ⊤) := Module.compHom Γ(A, ⊤) (k ≫ j).appTop.hom
  let _ : Module R Γ(B, ⊤) := Module.compHom Γ(B, ⊤) (k ≫ j).appTop.hom
  let eF := Stacks.Conormal.affineConormalIsoCotangent j ⊤ (isAffineOpen_top T) J eJ heJ
  let eB := Stacks.Conormal.affineConormalIsoCotangent (k ≫ j) ⊤ (isAffineOpen_top T)
    (I ⊔ J) eK heK
  let adj := Scheme.Modules.pullbackPushforwardAdjunction k
  let η := adj.unit.app F
  let u0 : Γ(F, ⊤) →ₗ[R] Γ(A, ⊤) :=
    { toFun := η.app ⊤
      map_add' := map_add _
      map_smul' := by
        intro r x
        change η.app ⊤ (@SMul.smul Γ(W, ⊤) Γ(F, ⊤) _ (j.appTop r) x) =
          @SMul.smul Γ(Z, ⊤) Γ(A, ⊤) _ ((k ≫ j).appTop r) (η.app ⊤ x)
        have hh := Scheme.Modules.Hom.app_smul η (U := ⊤) (j.appTop r) x
        convert hh using 1 <;> rfl }
  let u1 : J →ₗ[R] Γ(A, ⊤) := u0 ∘ₗ eF.inv.hom ∘ₗ J.toCotangent
  obtain ⟨v, hv⟩ := exists_cotangent_extension_of_inf_le I J hIJ u1 (by
    intro a ha m
    change ((k ≫ j).appTop a) • m = 0
    rw [show (k ≫ j).appTop a = 0 from hker ha, zero_smul])
  let r0 : Γ(B, ⊤) →ₗ[R] Γ(A, ⊤) := v ∘ₗ eB.hom.hom
  let r1 : Γ(B, ⊤) →ₗ[Γ(Z, ⊤)] Γ(A, ⊤) :=
    { toFun := r0
      map_add' := map_add r0
      map_smul' := by
        intro c x
        obtain ⟨a, rfl⟩ := (IsClosedImmersion.isAffine_surjective_of_isAffine (k ≫ j)).2 c
        exact r0.map_smul a x }
  obtain ⟨r, hr⟩ := Stacks.AlgebraicGeometry.ModuleLimits.exists_hom_app_top_eq
    (F := B) (G := A) r1
  refine ⟨r, ?_⟩
  refine (adj.homEquiv F A).injective ?_
  show (adj.homEquiv F A) (α ≫ r) = (adj.homEquiv F A) (𝟙 A)
  have h2 : (adj.homEquiv F A) (𝟙 A) = adj.unit.app F := by
    rw [Adjunction.homEquiv_unit, CategoryTheory.Functor.map_id]
    exact Category.comp_id _
  rw [h2, Adjunction.homEquiv_unit, CategoryTheory.Functor.map_comp, ← Category.assoc]
  apply Stacks.AlgebraicGeometry.ModuleLimits.hom_ext_of_app_top
  intro x
  obtain ⟨a, ha⟩ := J.toCotangent_surjective (eF.hom x)
  have hx : eF.inv (J.toCotangent a) = x := by
    rw [ha]
    exact CategoryTheory.Iso.hom_inv_id_apply eF x
  rw [← hx, Scheme.Modules.Hom.comp_app]
  have hc := Stacks.Immersion.isInducedConormalSheafMap_immersionConormalSheafMap
    (k ≫ j) j k (𝟙 T) (by simp) ⊤ (isAffineOpen_top T) ⊤ (isAffineOpen_top T) (by simp)
    (I ⊔ J) J eK heK eJ heJ a (Submodule.inclusion le_sup_right a)
    (by
      rw [Scheme.Hom.appLE]
      have h1 : T.presheaf.map
          (homOfLE (show (⊤ : T.Opens) ≤ (𝟙 T) ⁻¹ᵁ ⊤ from by simp)).op =
          𝟙 (T.presheaf.obj (op (⊤ : T.Opens))) := by
        rw [show (homOfLE (show (⊤ : T.Opens) ≤ (𝟙 T) ⁻¹ᵁ ⊤ from by simp)).op =
          (𝟙 (op (⊤ : T.Opens))) from Subsingleton.elim _ _]
        exact T.presheaf.map_id _
      rw [h1]
      simp)
  rw [Adjunction.homEquiv_unit] at hc
  have hc' : (Scheme.Modules.Hom.app
          (adj.unit.app F ≫ (Scheme.Modules.pushforward k).map α) ⊤)
        (eF.inv (J.toCotangent a))
      = eB.inv ((I ⊔ J).toCotangent (Submodule.inclusion le_sup_right a)) :=
    (val_map_eq_self B _ _).symm.trans hc
  show (Scheme.Modules.Hom.app ((Scheme.Modules.pushforward k).map r) ⊤)
      ((Scheme.Modules.Hom.app (adj.unit.app F ≫ (Scheme.Modules.pushforward k).map α) ⊤)
        (eF.inv (J.toCotangent a))) =
    (Scheme.Modules.Hom.app (adj.unit.app F) ⊤) (eF.inv (J.toCotangent a))
  rw [hc']
  refine (hr _).trans ?_
  show v (eB.hom (eB.inv ((I ⊔ J).toCotangent (Submodule.inclusion le_sup_right a)))) = _
  rw [CategoryTheory.Iso.inv_hom_id_apply]
  exact hv a

/-- **The left-hand map of the conormal sequence of a flat base change is retracted.** For a
closed immersion `k : Z ⟶ W` of affine schemes obtained by flat base change of a closed immersion
`i : X ⟶ P` of affine schemes, and a closed immersion `j : W ⟶ T` into an affine scheme over `P`,
the canonical map `k^* 𝒞_{W/T} ⟶ 𝒞_{Z/T}` admits a retraction.

The two ideals of `Γ(T, ⊤)` are the one cutting out `W` and the one extended from the ideal of
`X`; `AlgebraicGeometry.inf_map_eq_mul_ker_appTop_of_flat` says they cut out `Z` together and
that they are transverse, and `AlgebraicGeometry.conormal_retraction_of_ideal_intersection` turns
that into the retraction. -/
theorem conormalRetraction_of_flat_pullback {Z W X P T : Scheme.{u}} [IsAffine P] [IsAffine W]
    [IsAffine T] (i : X ⟶ P) [IsClosedImmersion i] (k : Z ⟶ W) [IsClosedImmersion k]
    (s : Z ⟶ X) (q : W ⟶ P) [Flat q] (hsq : IsPullback k s q i)
    (j : W ⟶ T) [IsClosedImmersion j] (ρ : T ⟶ P) (hbase : j ≫ ρ = q) :
    ∃ r : (Stacks.Conormal.conormalSheaf (k ≫ j) : Z.Modules) ⟶
        (Scheme.Modules.pullback k).obj (Stacks.Conormal.conormalSheaf j),
      Stacks.AlgebraicGeometry.conormalSequenceLeftMap k j ≫ r = 𝟙 _ := by
  obtain ⟨hker, hinf⟩ := inf_map_eq_mul_ker_appTop_of_flat i k s q hsq j ρ hbase
  obtain ⟨eJ, heJ⟩ := exists_affine_quotient_presentation j (RingHom.ker j.appTop.hom) rfl
  obtain ⟨eK, heK⟩ := exists_affine_quotient_presentation (k ≫ j)
    ((RingHom.ker i.appTop.hom).map ρ.appTop.hom ⊔ RingHom.ker j.appTop.hom) hker.symm
  exact conormal_retraction_of_ideal_intersection k j _ _ (hinf.le.trans le_sup_left)
    hker.symm.le eJ heJ eK heK

/-! ### The conormal input, proved -/

/-- **The conormal input of Stacks 068Z for the squares the proof of Stacks 069P produces.** For
a closed immersion `k : Z ⟶ W` of affine schemes obtained by flat base change of a closed
immersion `i : X ⟶ P` of affine schemes, and a closed immersion `j : W ⟶ T` into an affine
scheme over `P`, the conormal sequence of Stacks 062S for `k` and `j` is exact and locally split.

This used to be carried as a hypothesis; `AlgebraicGeometry.splitConormalOfFlatPullback` proves
it. -/
def SplitConormalOfFlatPullback : Prop :=
  ∀ {Z W X P T : Scheme.{u}} [IsAffine P] [IsAffine W] [IsAffine T]
    (i : X ⟶ P) [IsClosedImmersion i] (k : Z ⟶ W) [IsClosedImmersion k]
    (s : Z ⟶ X) (q : W ⟶ P) [Flat q], IsPullback k s q i →
    ∀ (j : W ⟶ T) [IsClosedImmersion j] (ρ : T ⟶ P), j ≫ ρ = q →
      Stacks.AlgebraicGeometry.IsSplitExactConormalSequence k j

/-- **The conormal input of Stacks 068Z for the squares the proof of Stacks 069P produces, with
no hypothesis.** The composite of the two maps of the conormal sequence of Stacks 062S vanishes
by `Stacks.Immersion.conormalSequence_comp_zero`, the sequence is exact at its middle term by
`Stacks.Immersion.conormalSequence_exact` and surjective on the right by
`Stacks.Immersion.epi_conormalSequenceRightMap`, all three for an arbitrary pair of immersions;
and `AlgebraicGeometry.conormalRetraction_of_flat_pullback` retracts its left-hand map globally,
which makes the sequence short exact (a retracted map into an exact sequence with epimorphic
right-hand map splits it, `CategoryTheory.ShortComplex.Splitting.ofExactOfRetraction`) and gives
the `locallySplit` clause on the open `⊤`. -/
theorem splitConormalOfFlatPullback : SplitConormalOfFlatPullback.{u} := by
  intro Z W X P T _ _ _ i _ k _ s q _ hsq j _ ρ hbase
  obtain ⟨r, hr⟩ := conormalRetraction_of_flat_pullback i k s q hsq j ρ hbase
  have hepi : Epi (Stacks.Immersion.conormalSequenceShortComplex k j).g :=
    Stacks.Immersion.epi_conormalSequenceRightMap k j
  have hsplit : (Stacks.Immersion.conormalSequenceShortComplex k j).Splitting :=
    ShortComplex.Splitting.ofExactOfRetraction _
      (Stacks.Immersion.conormalSequence_exact k j) r hr hepi
  exact
    { comp_eq_zero := Stacks.Immersion.conormalSequence_comp_zero k j
      shortExact := hsplit.shortExact
      locallySplit := fun z =>
        ⟨⊤, trivial, (Scheme.Modules.restrictFunctor (⊤ : Z.Opens).ι).map r,
          ((Scheme.Modules.restrictFunctor (⊤ : Z.Opens).ι).map_comp _ r).symm.trans
            ((congrArg (Scheme.Modules.restrictFunctor (⊤ : Z.Opens).ι).map hr).trans
              (CategoryTheory.Functor.map_id _ _))⟩ }

/-- **Part (3) of Stacks 068Z for the squares the proof of Stacks 069P produces, by Stacks' own
route.** This is `AlgebraicGeometry.isKoszulRegularImmersion_of_flat_pullback` again, obtained
the way Stacks obtains it: from part (3) of Stacks 068Z fed with
`AlgebraicGeometry.splitConormalOfFlatPullback`. It needs `j` locally of finite presentation,
which the other proof does not. -/
theorem isKoszulRegularImmersion_of_flat_pullback_of_splitConormal {Z W X P T : Scheme.{u}}
    [IsAffine P] [IsAffine W] [IsAffine T] (i : X ⟶ P) [IsClosedImmersion i] (k : Z ⟶ W)
    [IsClosedImmersion k] (s : Z ⟶ X) (q : W ⟶ P) [Flat q] (hsq : IsPullback k s q i)
    (j : W ⟶ T) [IsClosedImmersion j] [LocallyOfFinitePresentation j] (ρ : T ⟶ P)
    (hbase : j ≫ ρ = q) (hj : IsKoszulRegularImmersion j)
    (hkj : IsKoszulRegularImmersion (k ≫ j)) :
    IsKoszulRegularImmersion k :=
  Stacks.AlgebraicGeometry.isKoszulRegularImmersion_of_comp_of_isSplitExactConormalSequence k j
    (splitConormalOfFlatPullback i k s q hsq j ρ hbase) hj hkj

/-! ### The affine descent -/

/-- **The affine case of Stacks 069P.** A morphism of affine schemes is a local complete
intersection morphism as soon as its precomposition with a surjective syntomic morphism of
affine schemes is.

`f` is of finite presentation by Stacks 02KK, so it is a closed immersion `i` into a relative
affine space over its target followed by the smooth projection, and it suffices to see that `i`
is Koszul-regular. The syntomic case of Stacks 04E3, which is the geometric form of
Stacks 00T0, covers the source of `g` by base changes along syntomic morphisms `q_a` to that
affine space, and by Stacks 0694 it is enough to see that each base change of `i` along `q_a` is
Koszul-regular. On an affine open of the member of the cover this is Stacks 068Z applied to the
Koszul-regular closed immersions of Stacks 069G into a further relative affine space produced by
`AlgebraicGeometry.exists_koszulRegular_ambient_factorization`, and the descent from the affine
space back to the member of the cover is
`AlgebraicGeometry.isKoszulRegularImmersion_of_flat_pullback`. -/
theorem isLocalCompleteIntersectionMorphism_of_surjective_syntomic_of_isAffine
    {X' X Y : Scheme.{u}} [IsAffine X'] [IsAffine X] [IsAffine Y]
    (g : X' ⟶ X) (f : X ⟶ Y) (hsurj : Surjective g) (hsyn : Syntomic g)
    (hlci : IsLocalCompleteIntersectionMorphism (g ≫ f)) :
    IsLocalCompleteIntersectionMorphism f := by
  have hcompFP : ((g ≫ f).appTop).hom.FinitePresentation := by
    have : LocallyOfFinitePresentation (g ≫ f) :=
      locallyOfFinitePresentation_of_isLocalCompleteIntersectionMorphism hlci
    exact Scheme.Hom.finitePresentation_appTop (g ≫ f)
  have hgFlat : Flat g := flat hsyn
  have hgFF : (g.appTop).hom.FaithfullyFlat :=
    (Flat.flat_and_surjective_iff_faithfullyFlat_of_isAffine g).mp ⟨hgFlat, hsurj⟩
  have hgFP : (g.appTop).hom.FinitePresentation := by
    have : LocallyOfFinitePresentation g := locallyOfFinitePresentation hsyn
    exact Scheme.Hom.finitePresentation_appTop g
  have hfFP : (f.appTop).hom.FinitePresentation :=
    RingHom.finitePresentation_of_comp_of_faithfullyFlat f.appTop.hom g.appTop.hom
      (by simpa only [Scheme.Hom.comp_appTop, CommRingCat.hom_comp] using hcompFP) hgFF hgFP
  have hlfpF : LocallyOfFinitePresentation f := by
    have hspec : LocallyOfFinitePresentation (Spec.map f.appTop) :=
      (LocallyOfFinitePresentation.SpecMap_iff f.appTop).mpr hfFP
    have : MorphismProperty.IsStableUnderComposition
      (@LocallyOfFinitePresentation : MorphismProperty Scheme.{u}) := inferInstance
    have : MorphismProperty.RespectsIso
        (@LocallyOfFinitePresentation : MorphismProperty Scheme.{u}) :=
      MorphismProperty.respectsIso_of_isStableUnderComposition (fun X Y f hf => by
        let _ : IsIso f := hf
        infer_instance)
    exact (MorphismProperty.arrow_mk_iso_iff
      (@LocallyOfFinitePresentation : MorphismProperty Scheme.{u})
      (arrowIsoSpecΓOfIsAffine f)).mpr hspec
  let _ : LocallyOfFinitePresentation f := hlfpF
  obtain ⟨n, i, hi, hbase⟩ := exists_closedImmersion_affineSpace_of_lfp f
  let _ : IsClosedImmersion i := hi
  set π : AffineSpace (ULift.{u} (Fin n)) Y ⟶ Y :=
    AffineSpace (ULift.{u} (Fin n)) Y ↘ Y with hπ
  have hπsm : Smooth π := smooth_affineSpace_over _ _
  have hreg : IsKoszulRegularImmersion i := by
    obtain ⟨J, W, q, t, hq, ht, hcover⟩ :=
      exists_syntomic_zariskiCover_baseChange_of_isClosedImmersion i g hsyn
    have hcov := (Scheme.ofArrows_mem_precoverage_iff _).mp hcover
    apply isKoszulRegularImmersion_of_flat_covers_image i W q (fun a => flat (hq a))
      (fun a => locallyOfFinitePresentation (hq a))
    · intro z
      obtain ⟨z', hz'⟩ := hsurj.surj z
      obtain ⟨a, w, hw⟩ := hcov.1 z'
      refine ⟨a, (pullback.fst (q a) i).base w, ?_⟩
      have htw : (pullback.snd (q a) i).base w = z := by
        rw [← ht a]
        change g.base ((t a).base w) = z
        rw [hw, hz']
      have hc := congrArg (fun k : pullback (q a) i ⟶ _ => k.base w)
        (pullback.condition (f := q a) (g := i))
      change (q a).base ((pullback.fst (q a) i).base w) =
        i.base ((pullback.snd (q a) i).base w) at hc
      exact hc.trans (congrArg i.base htw)
    · intro a
      let e := pullbackSymmetry i (q a)
      have hta : IsOpenImmersion (t a) := hcov.2 a
      let _ : IsOpenImmersion (t a) := hta
      have hqLci : IsLocalCompleteIntersectionMorphism (q a) :=
        isLocalCompleteIntersectionMorphism_of_syntomic (hq a)
      have hlocal : IsLocalCompleteIntersectionMorphism (e.hom ≫ t a ≫ g ≫ f) := by
        refine isLocalCompleteIntersectionMorphism_comp e.hom _
          (koszul_of_isOpenImmersion' e.hom) ?_
        exact isLocalCompleteIntersectionMorphism_comp (t a) (g ≫ f)
          (koszul_of_isOpenImmersion' (t a)) hlci
      have heq : e.hom ≫ t a ≫ g ≫ f = pullback.snd i (q a) ≫ q a ≫ π := by
        calc
          _ = e.hom ≫ (t a ≫ g) ≫ f := by simp only [Category.assoc]
          _ = e.hom ≫ pullback.snd (q a) i ≫ f := by rw [ht a]
          _ = pullback.fst i (q a) ≫ f := by simp [e]
          _ = pullback.fst i (q a) ≫ i ≫ π := by rw [hπ, hbase]
          _ = _ := by rw [pullback.condition_assoc]
      rw [heq] at hlocal
      refine isKoszulRegularImmersion_of_forall_pullbackSnd (pullback.snd i (q a))
        (Scheme.zariskiPrecoverage_le_fpqcPrecoverage _ (W a).affineCover.mem₀) ?_
      rintro _ _ _ ⟨b⟩
      let l := (W a).affineCover.f b
      let k := pullback.snd (pullback.snd i (q a)) l
      have hqflat : Flat (q a) := flat (hq a)
      let _ : Flat (q a) := hqflat
      have hq' : IsLocalCompleteIntersectionMorphism (l ≫ q a) :=
        isLocalCompleteIntersectionMorphism_comp l (q a) (koszul_of_isOpenImmersion' l) hqLci
      have hk : IsLocalCompleteIntersectionMorphism (k ≫ (l ≫ q a) ≫ π) := by
        have hh := isLocalCompleteIntersectionMorphism_comp
          (pullback.fst (pullback.snd i (q a)) l) (pullback.snd i (q a) ≫ q a ≫ π)
          (koszul_of_isOpenImmersion' _) hlocal
        simpa only [k, Category.assoc, pullback.condition_assoc] using hh
      obtain ⟨m, jW, hjW, hbaseW, hlfpW, hregW, hregkW⟩ :=
        exists_koszulRegular_ambient_factorization k (l ≫ q a) π hq' hk
      let _ : IsClosedImmersion jW := hjW
      let _ : LocallyOfFinitePresentation jW := hlfpW
      have hsq := (IsPullback.of_hasPullback (pullback.snd i (q a)) l).flip.paste_vert
        (IsPullback.of_hasPullback i (q a)).flip
      exact ⟨⟨inferInstance, isKoszulRegularImmersion_of_flat_pullback i k _ (l ≫ q a) hsq jW _
        hbaseW hregW hregkW⟩, inferInstance⟩
  exact isLocalCompleteIntersectionMorphism_of_koszulRegular_affineImmersion f n i hbase hreg

/-- **The retraction the `locallySplit` clause of Stacks 062S asks for, on global sections.** In
the situation of `AlgebraicGeometry.inf_map_eq_mul_ker_appTop_of_flat` the conormal module of
`k ≫ j` retracts onto the conormal module of `j`, compatibly with the inclusion of the ideal of
`j` into the ideal of `k ≫ j`.

This is the content of the `locallySplit` clause of
`Stacks.AlgebraicGeometry.IsSplitExactConormalSequence` for the squares that the proof of
Stacks 069P produces, read on global sections.
`AlgebraicGeometry.conormalRetraction_of_flat_pullback` is the same retraction read as a morphism
of sheaves of modules, which is what
`Stacks.AlgebraicGeometry.IsSplitExactConormalSequence.locallySplit` asks for. -/
theorem exists_cotangent_retraction_of_flat_pullback {Z W X P T : Scheme.{u}} [IsAffine P]
    [IsAffine W] [IsAffine T] (i : X ⟶ P) [IsClosedImmersion i] (k : Z ⟶ W)
    [IsClosedImmersion k] (s : Z ⟶ X) (q : W ⟶ P) [Flat q] (hsq : IsPullback k s q i)
    (j : W ⟶ T) [IsClosedImmersion j] (ρ : T ⟶ P) (hbase : j ≫ ρ = q) :
    RingHom.ker (k ≫ j).appTop.hom =
        (RingHom.ker i.appTop.hom).map ρ.appTop.hom ⊔ RingHom.ker j.appTop.hom ∧
      ∃ r : ((RingHom.ker i.appTop.hom).map ρ.appTop.hom ⊔
            RingHom.ker j.appTop.hom).Cotangent →ₗ[Γ(T, ⊤)]
          (RingHom.ker j.appTop.hom ⧸ Submodule.comap (RingHom.ker j.appTop.hom).subtype
            ((RingHom.ker i.appTop.hom).map ρ.appTop.hom * RingHom.ker j.appTop.hom ⊔
              RingHom.ker j.appTop.hom ^ 2)),
        ∀ x : RingHom.ker j.appTop.hom,
          r (((RingHom.ker i.appTop.hom).map ρ.appTop.hom ⊔
              RingHom.ker j.appTop.hom).toCotangent
            (Submodule.inclusion le_sup_right x)) = Submodule.Quotient.mk x := by
  obtain ⟨hker, hinf⟩ := inf_map_eq_mul_ker_appTop_of_flat i k s q hsq j ρ hbase
  exact ⟨hker, exists_conormal_retraction_of_inf_le
    ((RingHom.ker i.appTop.hom).map ρ.appTop.hom) (RingHom.ker j.appTop.hom)
    (hinf.le.trans le_sup_left)⟩

/-! ### Stacks 069P -/

/-- **Stacks 069P.** The property of being a local complete intersection morphism of schemes is
syntomic local on the source: a morphism is Koszul exactly when its composites with the members
of a syntomic covering of its source are.

All four inputs of the syntomic case of Stacks 036H are supplied: Zariski locality on the source
and on the target and preservation under precomposition with a syntomic morphism come from
`StacksFrontier.AlgebraicGeometry.Descent.LocalOnSourceTopologies.LocalCompleteIntersection`, and
the affine descent is
`AlgebraicGeometry.isLocalCompleteIntersectionMorphism_of_surjective_syntomic_of_isAffine`. -/
@[stacks 069P]
theorem isLocalAtSource_syntomic_isLocalCompleteIntersectionMorphism :
    MorphismProperty.IsLocalAtSource
      (@IsLocalCompleteIntersectionMorphism.{u} : MorphismProperty Scheme.{u})
      (Scheme.precoverage (@Syntomic.{u})) :=
  isLocalAtSource_syntomic_of_affine_descent
    (@IsLocalCompleteIntersectionMorphism.{u} : MorphismProperty Scheme.{u})
    fun g f hsurj hsyn hcomp =>
      isLocalCompleteIntersectionMorphism_of_surjective_syntomic_of_isAffine g f hsurj
        hsyn hcomp

end AlgebraicGeometry

end
