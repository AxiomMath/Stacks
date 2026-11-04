module

public import StacksFrontier.AlgebraicGeometry.Duality.BlowupBaseChange.ExceptionalFibre
public import StacksFrontier.AlgebraicGeometry.Duality.BlowupBaseChange.ExceptionalCartier
public import StacksFrontier.AlgebraicGeometry.Duality.BlowupBaseChange.ProjectiveLineTarget
public import StacksFrontier.AlgebraicGeometry.Duality.BlowupBaseChange.InvertiblePullback
public import StacksFrontier.AlgebraicGeometry.Duality.BlowupBaseChange.CartierTwistedInverseImage
public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImage.PerfectBaseChange
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.PerfectMorphism.RegularTarget
public import StacksFrontier.RingTheory.NodalChart.Regularity

/-!
# The base change map of the twisted inverse image fails without Tor independence

This is [Stacks, Example 0AAC]. Let `k` be a field, `Y = 𝐀²_k`, `f : X ⟶ Y` the blowup of `Y`
in the origin, `g : Y' = Spec k ⟶ Y` the origin, and `X' = X ×_Y Y' = E = 𝐏¹_k` the exceptional
divisor. Then `f` is perfect and proper and `g` is perfect, but the source `L(g')^* a(𝒪_Y)` and the
target `a'(Lg^* 𝒪_Y)` of the base change map (48.5.0.1) of [Stacks, Tag 0AA6] are not isomorphic,
so no map between them — in particular no base change map — is an isomorphism; and `f`, `g` are
not Tor independent.

## The proof

The source computes `a(𝒪_Y) = 𝒪_X(-1)`, an invertible module in degree `0`, and
`a'(𝒪_{Spec k}) = 𝒪_E(-2)[1]`, an invertible module in degree `-1`. The argument below reads
that difference off the standard t-structure.

* `f` factors as `X ⟶ 𝐏¹_Y ⟶ Y` through the closed immersion `ι`, whose image is an effective
  Cartier divisor `D` (`Stacks.Duality.BlowupBaseChange.isEffectiveCartierDivisor_ker_ι`), so
  `a ≅ p^× ⋙ i_D^× ⋙ ψ^×` with `ψ : X ≅ D` ([Stacks, Tag 0ATX]).
* `p^×(𝒪_Y) ≅ (𝒪(-2) ⊗ p^*𝒪_Y)[1]` ([Stacks, Tag 0A9W],
  `Stacks.Duality.ProjCoeff.twistedInverseImageIso`), and `i_D^×` of an invertible module placed
  in degree `-1` is an invertible module in degree `0` ([Stacks, Tag 0A9X] and
  [Stacks, Tag 0AA4],
  `Stacks.Duality.exists_isInvertibleModule_twistedInverseImage_subschemeι_iso_single`).
  Derived pullback of an invertible module in degree `0` lies in `D^{≥ 0}`, so the source of the
  base change map lies in `D^{≥ 0}`.
* The target is `p_k^×(𝒪_{Spec k})` for `p_k : 𝐏¹_k ⟶ Spec k`, which is not in `D^{≥ 0}`:
  the trace identifies maps out of `𝒪(-2)[1]`, an object of `D^{≤ -1}`, into it with the
  endomorphisms of `𝒪_{Spec k}`
  (`Stacks.Duality.not_isGE_twistedInverseImage_projToSpecCoeff_derivedStructureSheaf`).
* If `f` and `g` were Tor independent, the base change map would be an isomorphism by
  [Stacks, Tag 0BZG], `f` being perfect and proper and all schemes Noetherian.

## Main results

* `Stacks.Duality.BlowupBaseChange.not_nonempty_iso_twistedInverseImage_baseChange_obj`: the
  source and target of the base change map at `𝒪_Y` are not isomorphic.
* `Stacks.Duality.BlowupBaseChange.baseChange_example`: **[Stacks, Example 0AAC]**.

## References

* [Stacks Project, Tag 0AAC](https://stacks.math.columbia.edu/tag/0AAC)
* [Stacks Project, Tag 0AA6](https://stacks.math.columbia.edu/tag/0AA6)
* [Stacks Project, Tag 0BZG](https://stacks.math.columbia.edu/tag/0BZG)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Triangulated
open Stacks.AlgebraicGeometry.ProjPolyChart

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

namespace Stacks.Duality.BlowupBaseChange

variable (k : Type u) [Field k]

/-- The projective line `𝐏¹_k` is quasi-compact. -/
instance : CompactSpace (AlgebraicGeometry.Proj (polyGrading k 1)) :=
  have := Stacks.ProjectiveSpace.Cohomology.quasiCompact_projToSpecCoeff k 1
  QuasiCompact.compactSpace_of_compactSpace (projToSpecCoeff k 1)

/-- The projective line `𝐏¹_k` is quasi-separated. -/
instance : QuasiSeparatedSpace (AlgebraicGeometry.Proj (polyGrading k 1)) :=
  have := Stacks.ProjectiveSpace.Cohomology.quasiSeparated_projToSpecCoeff k 1
  quasiSeparatedSpace_of_quasiSeparated (projToSpecCoeff k 1)

/-- The projective line `𝐏¹_Y` over `Y = 𝐀²_k` is quasi-compact. -/
instance : CompactSpace (AlgebraicGeometry.Proj (polyGrading (A k) 1)) :=
  have := Stacks.ProjectiveSpace.Cohomology.quasiCompact_projToSpecCoeff (A k) 1
  QuasiCompact.compactSpace_of_compactSpace (projToSpecCoeff (A k) 1)

/-- The projective line `𝐏¹_Y` over `Y = 𝐀²_k` is quasi-separated. -/
instance : QuasiSeparatedSpace (AlgebraicGeometry.Proj (polyGrading (A k) 1)) :=
  have := Stacks.ProjectiveSpace.Cohomology.quasiSeparated_projToSpecCoeff (A k) 1
  quasiSeparatedSpace_of_quasiSeparated (projToSpecCoeff (A k) 1)

/-- The image `D ⊆ 𝐏¹_Y` of the closed immersion `ι k` is quasi-compact. -/
instance : CompactSpace (ι k).ker.subscheme :=
  QuasiCompact.compactSpace_of_compactSpace (ι k).ker.subschemeι

/-- The image `D ⊆ 𝐏¹_Y` of the closed immersion `ι k` is quasi-separated. -/
instance : QuasiSeparatedSpace (ι k).ker.subscheme :=
  quasiSeparatedSpace_of_quasiSeparated (ι k).ker.subschemeι

/-- Membership in `D^{≥ n}` is invariant under isomorphism. -/
theorem isGE_of_iso_of_isGE {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
    {X Y : DerivedCategory C} (e : X ≅ Y) (n : ℤ) (h : X.IsGE n) : Y.IsGE n := by
  have := h
  exact DerivedCategory.TStructure.t.isGE_of_iso e n

/-- The structure sheaf of `𝐀²_k`, in degree zero. -/
abbrev structureSheaf : quasiCoherentDerivedCategory (Spec (CommRingCat.of (A k))) :=
  DerivedPushforward.derivedStructureSheaf (Spec (CommRingCat.of (A k)))

/-- Membership in `D^{≥ n}` of the underlying object is invariant under isomorphism in the
quasi-coherent derived category. -/
private theorem isGE_obj_of_iso {S : Scheme} {X Y : quasiCoherentDerivedCategory S} (e : X ≅ Y)
    (n : ℤ) (h : X.obj.IsGE n) : Y.obj.IsGE n :=
  isGE_of_iso_of_isGE ((ObjectProperty.ι _).mapIso e) n h

/-- **The source of the base change map lies in `D^{≥ 0}`**: `L(g')^* a(𝒪_Y)` is the derived
pullback of an invertible module placed in degree zero. Indeed `f = ψ ≫ i_D ≫ p` with `ψ` an
isomorphism onto the effective Cartier divisor `D ⊆ 𝐏¹_Y`, so
`a(𝒪_Y) ≅ ψ^×(i_D^×(p^×𝒪_Y)) ≅ Lψ^*(i_D^×((𝒪(-2) ⊗ p^*𝒪_Y)[1]))`, and `i_D^×` carries an
invertible module in degree `-1` to an invertible module in degree `0`. -/
theorem isGE_source :
    ((twistedInverseImage (f k) (isQuasicoherent_homology_derivedPushforward_of_qcqs (f k)) ⋙
        quasiCoherentDerivedPullback' (g' k)).obj (structureSheaf k)).obj.IsGE 0 := by
  let D := (ι k).ker
  have : Stacks.Divisors.IsEffectiveCartierDivisor D := isEffectiveCartierDivisor_ker_ι k
  let ψ : blowup k ⟶ D.subscheme := (ι k).toImage
  have hfac : f k = ψ ≫ (D.subschemeι ≫ projToSpecCoeff (A k) 1) := by
    rw [f_eq_ι_comp, ← Category.assoc, Scheme.Hom.toImage_imageι]
  have : IsLocallyNoetherian (AlgebraicGeometry.Proj (polyGrading (A k) 1)) :=
    isLocallyNoetherian_proj_polyGrading (A k) 1
  let eCongr := twistedInverseImageCongr hfac
    (isQuasicoherent_homology_derivedPushforward_of_qcqs (f k))
    (isQuasicoherent_homology_derivedPushforward_of_qcqs
      (ψ ≫ (D.subschemeι ≫ projToSpecCoeff (A k) 1)))
  let e₁ := twistedInverseImageCompIsoOfQcqs ψ (D.subschemeι ≫ projToSpecCoeff (A k) 1)
  let e₂ := twistedInverseImageCompIsoOfQcqs D.subschemeι (projToSpecCoeff (A k) 1)
  let M := ModuleCat.of (A k) (A k)
  let eO : structureSheaf k ≅ ProjCoeff.Mqc (A k) M :=
    derivedStructureSheafIsoDerivedTilde (CommRingCat.of (A k))
  let eP : (twistedInverseImage (projToSpecCoeff (A k) 1)
      (isQuasicoherent_homology_derivedPushforward_of_qcqs _)).obj (structureSheaf k) ≅
        ProjCoeff.Gqc (A k) 1 M :=
    (twistedInverseImage (projToSpecCoeff (A k) 1)
      (isQuasicoherent_homology_derivedPushforward_of_qcqs _)).mapIso eO ≪≫
      ProjCoeff.twistedInverseImageIso (A k) 1 M
  let G := (ProjCoeff.T (A k) 1 (-((1 : ℕ) : ℤ) - 1)).obj M
  have : Stacks.Ample.IsInvertibleModule _ G := isInvertibleModule_geometricFactor (A k) 1 _
  obtain ⟨L, hL, ⟨eL⟩⟩ := exists_isInvertibleModule_twistedInverseImage_subschemeι_iso_single D G
    (ProjCoeff.Gqc (A k) 1 M) (Iso.refl _)
  have := hL
  let a_D := twistedInverseImage D.subschemeι
    (isQuasicoherent_homology_derivedPushforward_of_qcqs D.subschemeι)
  let K' := a_D.obj (ProjCoeff.Gqc (A k) 1 M)
  let eψ := twistedInverseImageIsoQuasiCoherentDerivedPullbackOfIsIso ψ
  let eTot : (twistedInverseImage (f k)
        (isQuasicoherent_homology_derivedPushforward_of_qcqs (f k))).obj
      (structureSheaf k) ≅ (quasiCoherentDerivedPullback' ψ).obj K' :=
    eCongr.app _ ≪≫ e₁.app _ ≪≫ (twistedInverseImage ψ _).mapIso (e₂.app _ ≪≫ a_D.mapIso eP) ≪≫
      eψ.app K'
  let e₃ : ((twistedInverseImage (f k) (isQuasicoherent_homology_derivedPushforward_of_qcqs (f k)) ⋙
        quasiCoherentDerivedPullback' (g' k)).obj (structureSheaf k)).obj ≅
      (derivedPullback (g' k ≫ ψ)).obj ((DerivedCategory.singleFunctor _ 0).obj L) :=
    (ObjectProperty.ι _).mapIso ((quasiCoherentDerivedPullback' (g' k)).mapIso eTot) ≪≫
      (derivedPullbackCompIso (g' k) ψ).app K'.obj ≪≫ (derivedPullback (g' k ≫ ψ)).mapIso eL
  exact isGE_of_iso_of_isGE e₃.symm 0
    (isGE_derivedPullback_singleFunctor_of_isInvertibleModule (g' k ≫ ψ) L)


/-- **The target of the base change map does not lie in `D^{≥ 0}`**: `a'(Lg^* 𝒪_Y)` is
`p_k^×(𝒪_{Spec k})` for `p_k : 𝐏¹_k ⟶ Spec k`, which is `𝒪(-2)[1]` and is not in `D^{≥ 0}`. -/
theorem not_isGE_target :
    ¬ ((quasiCoherentDerivedPullback' (g k) ⋙
        twistedInverseImage (projToSpecCoeff k 1)
          (isQuasicoherent_homology_derivedPushforward_of_qcqs (projToSpecCoeff k 1))).obj
          (structureSheaf k)).obj.IsGE 0 := by
  intro h
  obtain ⟨e⟩ := nonempty_quasiCoherentDerivedPullback_derivedStructureSheaf_iso (g k)
  exact not_isGE_twistedInverseImage_projToSpecCoeff_derivedStructureSheaf k 1 le_rfl
    (isGE_obj_of_iso ((twistedInverseImage (projToSpecCoeff k 1)
      (isQuasicoherent_homology_derivedPushforward_of_qcqs (projToSpecCoeff k 1))).mapIso e) 0 h)

/-- **The source and the target of the base change map (48.5.0.1) at `𝒪_Y` are not
isomorphic**, for the blowup `f : X ⟶ 𝐀²_k` of the origin and the origin `g : Spec k ⟶ 𝐀²_k`,
with `X' = 𝐏¹_k` the exceptional divisor: the source lies in `D^{≥ 0}` and the target does not. -/
theorem not_nonempty_iso_twistedInverseImage_baseChange_obj :
    ¬ Nonempty ((twistedInverseImage (f k)
        (isQuasicoherent_homology_derivedPushforward_of_qcqs (f k)) ⋙
          quasiCoherentDerivedPullback' (g' k)).obj (structureSheaf k) ≅
      (quasiCoherentDerivedPullback' (g k) ⋙
        twistedInverseImage (projToSpecCoeff k 1)
          (isQuasicoherent_homology_derivedPushforward_of_qcqs (projToSpecCoeff k 1))).obj
          (structureSheaf k)) := by
  rintro ⟨e⟩
  exact not_isGE_target k
    (isGE_obj_of_iso e 0 (isGE_source k))

/-- The blowup morphism is perfect: it is of finite type over the regular scheme `𝐀²_k`
([Stacks, Tag 068B]). -/
theorem perfect_f : Perfect (f k) :=
  perfect_of_isRegular (f k) (Stacks.isRegular_spec_of_isRegularRing (A k))

/-- The origin is a closed point of `𝐀²_k`. -/
instance : IsClosedImmersion (g k) :=
  IsClosedImmersion.spec_of_surjective _
    fun a => ⟨MvPolynomial.C a, MvPolynomial.constantCoeff_C _ a⟩

/-- The origin `Spec k ⟶ 𝐀²_k` is perfect: it is of finite type over the regular scheme `𝐀²_k`
([Stacks, Tag 068B]). -/
theorem perfect_g : Perfect (g k) :=
  perfect_of_isRegular (g k) (Stacks.isRegular_spec_of_isRegularRing (A k))

/-- **The blowup and the origin are not Tor independent.** Otherwise the base change map of
[Stacks, Tag 0AA6] would be an isomorphism by [Stacks, Tag 0BZG], `f` being perfect and proper
and all schemes Noetherian, contradicting
`Stacks.Duality.BlowupBaseChange.not_nonempty_iso_twistedInverseImage_baseChange_obj`. -/
theorem not_torIndependent : ¬ TorIndependent (f k) (g k) := by
  intro hTor
  have : IsNoetherian (blowup k) := isNoetherian_of_isProper (f k)
  have := perfect_f k
  have := isIso_torIndependentTwistedInverseImageBaseChange_app_of_perfect (isPullback k) hTor
    (structureSheaf k)
  exact not_nonempty_iso_twistedInverseImage_baseChange_obj k
    ⟨asIso ((torIndependentTwistedInverseImageBaseChange (isPullback k) hTor).app
      (structureSheaf k))⟩

/-- **[Stacks, Example 0AAC]: the base change map (48.5.0.1) is not an isomorphism for a
perfect proper `f` and a perfect `g`.** Let `k` be a field, `f : X ⟶ Y = 𝐀²_k` the blowup of
the origin, `g : Y' = Spec k ⟶ Y` the origin and `X' = E = 𝐏¹_k` the exceptional divisor, with
`g' : X' ⟶ X` its inclusion and `f' : X' ⟶ Y'` its structure morphism; let `a`, `a'` be the right
adjoints of `Rf_*`, `Rf'_*` on `D_QCoh` ([Stacks, Tag 0A9E]). Then `f` is proper and perfect, `g`
is perfect, the square is cartesian, `f` and `g` are not Tor independent, and no morphism
`L(g')^* a(𝒪_Y) ⟶ a'(Lg^* 𝒪_Y)` — in particular no base change map — is an isomorphism. -/
@[stacks 0AAC]
theorem baseChange_example :
    IsProper (f k) ∧ Perfect (f k) ∧ Perfect (g k) ∧
      IsPullback (g' k) (projToSpecCoeff k 1) (f k) (g k) ∧ ¬ TorIndependent (f k) (g k) ∧
      ∀ φ : (twistedInverseImage (f k)
          (isQuasicoherent_homology_derivedPushforward_of_qcqs (f k)) ⋙
            quasiCoherentDerivedPullback' (g' k)).obj (structureSheaf k) ⟶
        (quasiCoherentDerivedPullback' (g k) ⋙
          twistedInverseImage (projToSpecCoeff k 1)
            (isQuasicoherent_homology_derivedPushforward_of_qcqs (projToSpecCoeff k 1))).obj
            (structureSheaf k), ¬ IsIso φ :=
  ⟨inferInstance, perfect_f k, perfect_g k, isPullback k, not_torIndependent k,
    fun φ hφ => not_nonempty_iso_twistedInverseImage_baseChange_obj k ⟨@asIso _ _ _ _ φ hφ⟩⟩

end Stacks.Duality.BlowupBaseChange
