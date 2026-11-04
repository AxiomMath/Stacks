module

public import StacksFrontier.AlgebraicGeometry.Blowup.ExceptionalProjectiveBundle
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundle.FibreProjectiveSpace
public import StacksFrontier.AlgebraicGeometry.Conormal.SmoothRank

/-!
# The exceptional divisor of a blowup in a smooth centre of codimension two is a `𝐏¹`-family

Let `f : X ⟶ S` be smooth, let `ℐ` be a quasi-coherent ideal sheaf on `X` whose closed subscheme
`Z = V(ℐ)` is smooth over `S`, and suppose the conormal sheaf `ℐ/ℐ²` of `Z` is finite locally
free of rank `2` (the centre has codimension two). Let `b : X' ⟶ X` be the blowup of `X` in `ℐ`
(`AlgebraicGeometry.blowUp`, `AlgebraicGeometry.blowUpToBase`) and `p : E ⟶ Z` the morphism from
its exceptional divisor to the centre. By [Stacks, Tag 0FUT]
(`Stacks.AlgebraicGeometry.exceptionalDivisorIsoProjectiveBundle`) `p` is the projective bundle
`𝐏(ℐ/ℐ²) ⟶ Z` of a module locally free of rank two. This file reads off what that means for the
fibres:

* `p` is smooth, flat, proper and locally of finite presentation;
* for every field `K` and every `K`-point `z : Spec K ⟶ Z`, the fibre of `p` over `z` is the
  projective line `𝐏¹_K = Proj K[T₀, T₁]`, by a cartesian square;
* that fibre is also the fibre of the blowup `b` over `z ≫ (Z ⟶ X)`, by the cartesian square
  `E = X' ×_X Z`; in particular every fibre of `b` over a field-valued point of the centre is
  isomorphic over `K` to `𝐏¹_K`.

`X'` is smooth over `S` (`Stacks.AlgebraicGeometry.smooth_blowUpToBase_comp_of_idealSheafData`),
so a second blowup of `X'` in a smooth centre of codimension two falls under the same statements.

## Main definitions

* `Stacks.AlgebraicGeometry.exceptionalSubschemeMap`: the morphism `p : E ⟶ V(ℐ)`.

## Main results

* `Stacks.ProjectiveBundleFibre.exists_isPullback_projectiveBundle_of_field`: the fibre of the
  projective bundle of a module finite locally free of rank `n + 1` over any point
  `Spec K ⟶ X` with values in a field is `𝐏ⁿ_K`.
* `Stacks.AlgebraicGeometry.smooth_exceptionalSubschemeMap`,
  `Stacks.AlgebraicGeometry.isProper_exceptionalSubschemeMap`,
  `Stacks.AlgebraicGeometry.flat_exceptionalSubschemeMap`,
  `Stacks.AlgebraicGeometry.locallyOfFinitePresentation_exceptionalSubschemeMap`: `p` is smooth,
  proper, flat and locally of finite presentation.
* `Stacks.AlgebraicGeometry.exists_isPullback_exceptionalSubschemeMap_projectiveLine`: the fibre
  square `𝐏¹_K ⟶ E` over `z`, together with the fibre square `𝐏¹_K ⟶ X'` over `z ≫ (Z ⟶ X)`.
* `Stacks.AlgebraicGeometry.isPullback_blowUpToBase_comp_subschemeι_iff`: a square over `z` is a
  fibre of `p` exactly when, composed with `E ⟶ X'`, it is a fibre of `b` over `z ≫ (Z ⟶ X)`.
* `Stacks.AlgebraicGeometry.exists_iso_projectiveLine_of_isPullback_exceptionalSubschemeMap` and
  `Stacks.AlgebraicGeometry.exists_iso_projectiveLine_of_isPullback_blowUpToBase`: every fibre of
  `p` over `z`, and every fibre of `b` over `z ≫ (Z ⟶ X)`, is isomorphic over `K` to `𝐏¹_K`.

## Implementation notes

The fibre computation of `Stacks.ProjectiveBundleFibre.exists_isPullback_projectiveBundle` is
stated for the residue-field points `Spec κ(y) ⟶ X`; the argument only uses that the image of
the point lies in an open on which the module is free, which holds for any morphism from the
spectrum of a field, since that spectrum has one point. It is redone here for an arbitrary
field-valued point, so that a `k`-point of a `k`-scheme gives a fibre over `k` itself.

## References

* [Stacks Project, Tag 0FUT](https://stacks.math.columbia.edu/tag/0FUT)
* [Stacks Project, Tag 01OE](https://stacks.math.columbia.edu/tag/01OE)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.RelativeProj (projectiveBundle projectiveBundleToBase)
open Stacks.AlgebraicGeometry.ProjPolyChart (polyGrading projToSpecCoeff)

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

namespace Stacks.ProjectiveBundleFibre

variable {X : Scheme.{u}} (E : X.Modules) [E.IsQuasicoherent] (n : ℕ)
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E (n + 1)]
  (K : Type u) [Field K] (j : Spec (CommRingCat.of K) ⟶ X)

/-- **The fibre of a projective bundle over a field-valued point is projective space**: for `ℰ`
finite locally free of rank `n + 1` on `X`, a field `K` and a morphism `j : Spec K ⟶ X`, there is
a cartesian square `𝐏ⁿ_K ⟶ 𝐏(ℰ)` over `j`. -/
theorem exists_isPullback_projectiveBundle_of_field :
    ∃ φ : AlgebraicGeometry.Proj (polyGrading K n) ⟶ projectiveBundle X E,
      IsPullback φ (projToSpecCoeff K n) (projectiveBundleToBase X E) j := by
  have : Subsingleton (Spec (CommRingCat.of K)) :=
    inferInstanceAs (Subsingleton (PrimeSpectrum K))
  have : Nonempty (Spec (CommRingCat.of K)) := inferInstanceAs (Nonempty (PrimeSpectrum K))
  let x₀ : Spec (CommRingCat.of K) := Nonempty.some inferInstance
  obtain ⟨U, hxU, ⟨e⟩⟩ := Stacks.ProjectiveBundle.exists_restrict_free E (n + 1) (j x₀)
  have hj : Set.range j ⊆ U := by
    rintro _ ⟨x, rfl⟩
    rw [Subsingleton.elim x x₀]
    exact hxU
  obtain ⟨hF⟩ := nonempty_iso_pullback_of_restrict_free E _ U e j hj
  let F := SheafOfModules.free (R := (Spec (CommRingCat.of K)).ringCatSheaf)
    (ULift.{u} (Fin (n + 1)))
  have : F.IsQuasicoherent := Stacks.AlgebraicGeometry.AffineQcohEquivalence.isQuasicoherent_free _
  obtain ⟨θ, hθ, -⟩ := exists_iso_freeProjectiveBundle K n
  let ψ := θ ≪≫ Stacks.RelativeProj.bundlePresentationIso F
  let bc := Stacks.RelativeProj.projectiveBundleBaseChange j E F hF
  have hψ : ψ.hom ≫ projectiveBundleToBase _ F = projToSpecCoeff K n :=
    (Category.assoc _ _ _).trans ((congrArg (fun k => θ.hom ≫ k)
      (Stacks.RelativeProj.bundlePresentationIso_hom_comp_toBase F)).trans hθ)
  refine ⟨ψ.hom ≫ bc, ?_⟩
  refine (Stacks.RelativeProj.isPullback_projectiveBundleToBase_baseChange j E F hF).flip.of_iso
    ψ.symm (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ (by simp) (by simp)
  · simp [bc]
  · simp [← hψ]

/-- **Every fibre of a projective bundle over a field-valued point is isomorphic over `K` to
`𝐏ⁿ_K`**: any cartesian square over `j : Spec K ⟶ X` has a top-left corner isomorphic, over
`Spec K`, to `Proj K[T₀, …, Tₙ]`. -/
theorem exists_iso_projectiveSpace_of_isPullback {F : Scheme.{u}}
    {q : F ⟶ projectiveBundle X E} {g : F ⟶ Spec (CommRingCat.of K)}
    (h : IsPullback q g (projectiveBundleToBase X E) j) :
    ∃ e : F ≅ AlgebraicGeometry.Proj (polyGrading K n), e.hom ≫ projToSpecCoeff K n = g := by
  obtain ⟨φ, hφ⟩ := exists_isPullback_projectiveBundle_of_field E n K j
  exact ⟨h.isoIsPullback _ _ hφ, h.isoIsPullback_hom_snd _ _ hφ⟩

end Stacks.ProjectiveBundleFibre

namespace Stacks.AlgebraicGeometry

variable {S X : Scheme.{u}} (f : X ⟶ S) (ℐ : X.IdealSheafData)

/-- **The morphism `p : E ⟶ V(ℐ)` from the exceptional divisor of the blowup of `X` in `ℐ` to
the centre**, induced by the blowup morphism; it is the second leg of the cartesian square
`Stacks.AlgebraicGeometry.isPullback_exceptionalDivisor_toCentre`. -/
abbrev exceptionalSubschemeMap : exceptionalDivisor ℐ ⟶ ℐ.subscheme :=
  Scheme.IdealSheafData.subschemeMap (exceptionalIdeal ℐ) ℐ (blowUpToBase ℐ)
    (ℐ.le_map_comap (blowUpToBase ℐ))

/-- **A field-valued square over the centre is a fibre of `p : E ⟶ Z` exactly when, composed with
the inclusion `E ⟶ X'`, it is a fibre of the blowup `b : X' ⟶ X`** over the composite point
`Spec K ⟶ Z ⟶ X`. This is the pasting of cartesian squares along `E = X' ×_X Z`; commutativity of
the small square follows from that of the large one because `Z ⟶ X` is a monomorphism. -/
theorem isPullback_blowUpToBase_comp_subschemeι_iff {F T : Scheme.{u}} (z : T ⟶ ℐ.subscheme)
    (q : F ⟶ exceptionalDivisor ℐ) (g : F ⟶ T) :
    IsPullback (q ≫ (exceptionalIdeal ℐ).subschemeι) g (blowUpToBase ℐ) (z ≫ ℐ.subschemeι) ↔
      IsPullback q g (exceptionalSubschemeMap ℐ) z := by
  refine ⟨fun h => ?_, fun h => h.paste_horiz (isPullback_exceptionalDivisor_toCentre ℐ)⟩
  have e : q ≫ exceptionalSubschemeMap ℐ = g ≫ z := by
    rw [← cancel_mono ℐ.subschemeι, Category.assoc, Category.assoc,
      ← (isPullback_exceptionalDivisor_toCentre ℐ).w, ← Category.assoc, h.w]
  exact h.of_right e (isPullback_exceptionalDivisor_toCentre ℐ)

/-- **Every fibre of the blowup over a point of the centre lies in the exceptional divisor and is
a fibre of `p : E ⟶ Z`**: a cartesian square over `z ≫ (Z ⟶ X)` factors through `E ⟶ X'`, and the
factored square is cartesian over `z`. -/
theorem exists_isPullback_exceptionalSubschemeMap_of_isPullback_blowUpToBase
    {F T : Scheme.{u}} (z : T ⟶ ℐ.subscheme) {q' : F ⟶ blowUp ℐ} {g : F ⟶ T}
    (h : IsPullback q' g (blowUpToBase ℐ) (z ≫ ℐ.subschemeι)) :
    ∃ q : F ⟶ exceptionalDivisor ℐ, q ≫ (exceptionalIdeal ℐ).subschemeι = q' ∧
      IsPullback q g (exceptionalSubschemeMap ℐ) z := by
  let q := (isPullback_exceptionalDivisor_toCentre ℐ).lift q' (g ≫ z)
    (by simpa using h.w)
  have hq : q ≫ (exceptionalIdeal ℐ).subschemeι = q' :=
    (isPullback_exceptionalDivisor_toCentre ℐ).lift_fst _ _ _
  refine ⟨q, hq, (isPullback_blowUpToBase_comp_subschemeι_iff ℐ z q g).mp ?_⟩
  rwa [hq]

/-- **A smooth centre of codimension two has conormal sheaf of rank two.** If `X` is smooth of
relative dimension `e + 2` over `S` and `Z = V(ℐ)` is smooth of relative dimension `e`, then
`ℐ/ℐ²` is finite locally free of rank `2`: it is the kernel of `Ω_{X/S}|_Z ⟶ Ω_{Z/S}`
(`Stacks.Conormal.isFiniteLocallyFreeOfRank_conormalSheaf_of_smoothOfRelativeDimension`), read
as the degree-one piece of the conormal algebra through `Stacks.Conormal.conormalDegreeOneHom`. -/
theorem isFiniteLocallyFreeOfRank_two_conormalSheafDegreeOne (e : ℕ)
    [SmoothOfRelativeDimension (e + 2) f] [SmoothOfRelativeDimension e (ℐ.subschemeι ≫ f)] :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (Stacks.Conormal.conormalSheafDegreeOne ℐ.subschemeι) 2 := by
  have h := Stacks.Conormal.isFiniteLocallyFreeOfRank_conormalSheaf_of_smoothOfRelativeDimension
    ℐ.subschemeι f (e + 2) e
  rw [Nat.add_sub_cancel_left] at h
  exact AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso
    (@asIso _ _ _ _ (Stacks.Conormal.conormalDegreeOneHom ℐ.subschemeι)
      (Stacks.Conormal.conormalDegreeOneHom_isIso ℐ.subschemeι)) h

/-- The identification of `E` with `𝐏(ℐ/ℐ²)` of [Stacks, Tag 0FUT] is one over the centre,
stated for `exceptionalSubschemeMap`. -/
theorem exceptionalDivisorIsoProjectiveBundle_hom_comp_eq_exceptionalSubschemeMap [Smooth f]
    [Smooth (ℐ.subschemeι ≫ f)] :
    (exceptionalDivisorIsoProjectiveBundle f ℐ).hom ≫
        projectiveBundleToBase ℐ.subscheme
          (Stacks.Conormal.conormalSheafDegreeOne ℐ.subschemeι) =
      exceptionalSubschemeMap ℐ :=
  exceptionalDivisorIsoProjectiveBundle_hom_toCentre f ℐ

section RankTwo

variable [Smooth f] [Smooth (ℐ.subschemeι ≫ f)]
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
    (Stacks.Conormal.conormalSheafDegreeOne ℐ.subschemeι) 2]

include f

/-- **The exceptional divisor of a blowup in a smooth centre of codimension two is smooth over
the centre**: it is the projective bundle of a module finite locally free of rank two. -/
theorem smooth_exceptionalSubschemeMap : Smooth (exceptionalSubschemeMap ℐ) := by
  rw [← exceptionalDivisorIsoProjectiveBundle_hom_comp_eq_exceptionalSubschemeMap f ℐ]
  have := Stacks.ProjectiveBundleFibre.smooth_projectiveBundleToBase
    (Stacks.Conormal.conormalSheafDegreeOne ℐ.subschemeι) 1
  infer_instance

/-- **The exceptional divisor of a blowup in a smooth centre of codimension two is proper over
the centre**: it is the projective bundle of a module finite locally free of rank two. -/
theorem isProper_exceptionalSubschemeMap : IsProper (exceptionalSubschemeMap ℐ) := by
  rw [← exceptionalDivisorIsoProjectiveBundle_hom_comp_eq_exceptionalSubschemeMap f ℐ]
  have := Stacks.ProjectiveBundleFibre.isProper_projectiveBundleToBase_of_rank
    (Stacks.Conormal.conormalSheafDegreeOne ℐ.subschemeι) 1
  infer_instance

/-- **The exceptional divisor of a blowup in a smooth centre of codimension two is flat over the
centre.** -/
theorem flat_exceptionalSubschemeMap : Flat (exceptionalSubschemeMap ℐ) :=
  haveI := smooth_exceptionalSubschemeMap f ℐ
  inferInstance

/-- **The exceptional divisor of a blowup in a smooth centre of codimension two is locally of
finite presentation over the centre**; with `isProper_exceptionalSubschemeMap` (which includes
quasi-compactness and separatedness) it is of finite presentation. -/
theorem locallyOfFinitePresentation_exceptionalSubschemeMap :
    LocallyOfFinitePresentation (exceptionalSubschemeMap ℐ) :=
  haveI := smooth_exceptionalSubschemeMap f ℐ
  inferInstance

variable (K : Type u) [Field K] (z : Spec (CommRingCat.of K) ⟶ ℐ.subscheme)

/-- **The fibre of the exceptional divisor over a field-valued point of the centre is the
projective line, and it is the fibre of the blowup.** For a field `K` and `z : Spec K ⟶ Z` there
is `φ : 𝐏¹_K ⟶ E` exhibiting `𝐏¹_K = Proj K[T₀, T₁]` as the fibre of `p : E ⟶ Z` over `z`, and
`φ` followed by `E ⟶ X'` exhibits it as the fibre of the blowup `b : X' ⟶ X` over
`z ≫ (Z ⟶ X)`. -/
theorem exists_isPullback_exceptionalSubschemeMap_projectiveLine :
    ∃ φ : AlgebraicGeometry.Proj (polyGrading K 1) ⟶ exceptionalDivisor ℐ,
      IsPullback φ (projToSpecCoeff K 1) (exceptionalSubschemeMap ℐ) z ∧
        IsPullback (φ ≫ (exceptionalIdeal ℐ).subschemeι) (projToSpecCoeff K 1)
          (blowUpToBase ℐ) (z ≫ ℐ.subschemeι) := by
  obtain ⟨φ, hφ⟩ := Stacks.ProjectiveBundleFibre.exists_isPullback_projectiveBundle_of_field
    (Stacks.Conormal.conormalSheafDegreeOne ℐ.subschemeι) 1 K z
  let e := exceptionalDivisorIsoProjectiveBundle f ℐ
  have he : e.inv ≫ exceptionalSubschemeMap ℐ =
      projectiveBundleToBase ℐ.subscheme (Stacks.Conormal.conormalSheafDegreeOne ℐ.subschemeι) := by
    rw [Iso.inv_comp_eq]
    exact (exceptionalDivisorIsoProjectiveBundle_hom_comp_eq_exceptionalSubschemeMap f ℐ).symm
  have h : IsPullback (φ ≫ e.inv) (projToSpecCoeff K 1) (exceptionalSubschemeMap ℐ) z :=
    hφ.of_iso (Iso.refl _) e.symm (Iso.refl _) (Iso.refl _) (by simp) (by simp)
      (by simpa using he.symm) (by simp)
  exact ⟨φ ≫ e.inv, h, (isPullback_blowUpToBase_comp_subschemeι_iff ℐ z _ _).mpr h⟩

/-- **Every fibre of the exceptional divisor over a field-valued point of the centre is isomorphic
over `K` to `𝐏¹_K`.** -/
theorem exists_iso_projectiveLine_of_isPullback_exceptionalSubschemeMap {F : Scheme.{u}}
    {q : F ⟶ exceptionalDivisor ℐ} {g : F ⟶ Spec (CommRingCat.of K)}
    (h : IsPullback q g (exceptionalSubschemeMap ℐ) z) :
    ∃ e : F ≅ AlgebraicGeometry.Proj (polyGrading K 1), e.hom ≫ projToSpecCoeff K 1 = g := by
  obtain ⟨φ, hφ, -⟩ := exists_isPullback_exceptionalSubschemeMap_projectiveLine f ℐ K z
  exact ⟨h.isoIsPullback _ _ hφ, h.isoIsPullback_hom_snd _ _ hφ⟩

/-- **Every fibre of the blowup in a smooth centre of codimension two over a field-valued point of
the centre is isomorphic over `K` to `𝐏¹_K`**, and lies in the exceptional divisor. -/
theorem exists_iso_projectiveLine_of_isPullback_blowUpToBase {F : Scheme.{u}}
    {q' : F ⟶ blowUp ℐ} {g : F ⟶ Spec (CommRingCat.of K)}
    (h : IsPullback q' g (blowUpToBase ℐ) (z ≫ ℐ.subschemeι)) :
    (∃ q : F ⟶ exceptionalDivisor ℐ, q ≫ (exceptionalIdeal ℐ).subschemeι = q' ∧
        IsPullback q g (exceptionalSubschemeMap ℐ) z) ∧
      ∃ e : F ≅ AlgebraicGeometry.Proj (polyGrading K 1), e.hom ≫ projToSpecCoeff K 1 = g := by
  obtain ⟨q, hq, hpb⟩ := exists_isPullback_exceptionalSubschemeMap_of_isPullback_blowUpToBase ℐ z h
  exact ⟨⟨q, hq, hpb⟩,
    exists_iso_projectiveLine_of_isPullback_exceptionalSubschemeMap f ℐ K z hpb⟩

/-- **The exceptional divisor of a blowup in a smooth centre of codimension two is a flat proper
family of projective lines, and the blowup is again smooth.** Let `f : X ⟶ S` be smooth and let
`ℐ` be an ideal sheaf on `X` whose closed subscheme `Z` is smooth over `S` with conormal sheaf
finite locally free of rank two. Then the blowup `X'` of `X` in `ℐ` is smooth over `S`; the
morphism `p : E ⟶ Z` from the exceptional divisor is smooth, proper, flat and locally of finite
presentation; and for every field `K` and every `z : Spec K ⟶ Z` there is a cartesian square
exhibiting `𝐏¹_K` as the fibre of `p` over `z`, which composed with `E ⟶ X'` exhibits it as the
fibre of `b : X' ⟶ X` over `z ≫ (Z ⟶ X)`. -/
theorem smooth_blowUp_exceptionalSubschemeMap_projectiveLineFamily :
    Smooth (blowUpToBase ℐ ≫ f) ∧ Smooth (exceptionalSubschemeMap ℐ) ∧
      IsProper (exceptionalSubschemeMap ℐ) ∧ Flat (exceptionalSubschemeMap ℐ) ∧
      LocallyOfFinitePresentation (exceptionalSubschemeMap ℐ) ∧
      ∀ (K : Type u) [Field K] (z : Spec (CommRingCat.of K) ⟶ ℐ.subscheme),
        ∃ φ : AlgebraicGeometry.Proj (polyGrading K 1) ⟶ exceptionalDivisor ℐ,
          IsPullback φ (projToSpecCoeff K 1) (exceptionalSubschemeMap ℐ) z ∧
            IsPullback (φ ≫ (exceptionalIdeal ℐ).subschemeι) (projToSpecCoeff K 1)
              (blowUpToBase ℐ) (z ≫ ℐ.subschemeι) :=
  ⟨smooth_blowUpToBase_comp_of_idealSheafData f ℐ, smooth_exceptionalSubschemeMap f ℐ,
    isProper_exceptionalSubschemeMap f ℐ, flat_exceptionalSubschemeMap f ℐ,
    locallyOfFinitePresentation_exceptionalSubschemeMap f ℐ,
    fun K _ z => exists_isPullback_exceptionalSubschemeMap_projectiveLine f ℐ K z⟩

end RankTwo

end Stacks.AlgebraicGeometry

end
