module

public import StacksFrontier.Examples.Spaces.CurveFamilyNotScheme.Blowup.StrictTransform
public import StacksFrontier.AlgebraicGeometry.Curves.Models.SpecialFiberPrincipal
public import StacksFrontier.AlgebraicGeometry.Divisors.DivisorPicardClass
public import StacksFrontier.AlgebraicGeometry.Divisors.InvertibleSheafPullback
public import StacksFrontier.AlgebraicGeometry.Divisors.RegularSectionCorrespondence
public import StacksFrontier.AlgebraicGeometry.Divisors.ZeroSchemeCanonicalSection
public import StacksFrontier.AlgebraicGeometry.Divisors.ZeroSchemeProperties
public import StacksFrontier.AlgebraicGeometry.Divisors.ZeroSchemeRegular
public import StacksFrontier.AlgebraicGeometry.DivisorFlatPullback.Basic
public import StacksFrontier.AlgebraicGeometry.Modules.FreeSheafMatrix
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.EmbeddedResolution.AmbientCurveResolution
import all StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.EmbeddedResolution.CurveStrictTransform

/-!
# The strict transform meets the exceptional divisor in one rational point

In the setting of `StacksFrontier/Examples/Spaces/CurveFamilyNotScheme/Blowup/StrictTransform.lean`
(a regular Noetherian surface `Y`, the blowup `π : Z ⟶ Y` at a closed point `y` with
two-dimensional local ring, exceptional divisor `E`, and the strict transform `C` of an integral
regular curve `Y₀ = V(t)` with `t ∈ 𝔪_y \ 𝔪_y²`), this file proves the facts about `C ∩ E` and
the conormal sheaf of `C` that the construction of [Stacks, Tag 0D5E] uses:

* `C ∩ E` is a single closed point `p`, whose residue field is that of `y`;
* the exceptional divisor restricts to `C` as the reduced point `p`: `E|_C = 𝒪_C(-p)`;
* the conormal sheaf of `C` is `𝒪_C(p)`, and more generally the restriction of `𝒪_Z(-(n+1)C)` to
  `C` is `𝒪_C((n+1)p)`.

## The argument

The total transform `E + C = π⁻¹(Y₀)` is cut out by the single global function `π^* t`, so its
invertible sheaf is trivial; hence `𝒪_Z(-C) ≅ 𝒪_Z(E)` in the Picard group of `Z`. Restricting to
`C` and using `E|_C = p` gives `𝒪_Z(-C)|_C ≅ 𝒪_C(p)`. The identity `E|_C = p` is read off the
isomorphism `C ≅ Y₀` over `π`: the inverse image of the reduced point `y` on `Y₀` is the reduced
point `y` of `Y₀`.

## Main results

* `Stacks.Examples.CurveFamilyNotScheme.exists_strictTransform_inter_exceptional`: the point `p`
  and all of its properties, including the conormal isomorphisms.

## References

* [Stacks Project, Tag 0D5E](https://stacks.math.columbia.edu/tag/0D5E)
* [Stacks Project, Tag 0BI7](https://stacks.math.columbia.edu/tag/0BI7)
* [Stacks Project, Tag 0B3P](https://stacks.math.columbia.edu/tag/0B3P)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace IsLocalRing Opposite
open Stacks.Divisors (IsEffectiveCartierDivisor)

universe u

namespace Stacks.Examples.CurveFamilyNotScheme

variable {Y : Scheme.{u}} (y : Y) (hy : IsClosed ({y} : Set Y))

/-- The residue field map of a closed immersion is an isomorphism. -/
theorem isIso_residueFieldMap_of_isClosedImmersion {X W : Scheme.{u}} (g : W ⟶ X)
    [IsClosedImmersion g] (w : W) : IsIso (g.residueFieldMap w) := by
  refine (ConcreteCategory.isIso_iff_bijective _).mpr ⟨RingHom.injective _, fun z => ?_⟩
  obtain ⟨a, rfl⟩ := W.residue_surjective w z
  obtain ⟨b, rfl⟩ := g.stalkMap_surjective w a
  exact ⟨X.residue (g w) b, by
    rw [← ConcreteCategory.comp_apply, Scheme.residue_residueFieldMap,
      ConcreteCategory.comp_apply]⟩

section Surface

variable [IsNoetherian Y] (hreg : IsRegular Y) (hdim : topologicalKrullDim Y = 2)
  (hydim : ringKrullDim (Y.presheaf.stalk y) = 2) {Y₀ : Y.IdealSheafData}
  [IsIntegral Y₀.subscheme] (hY₀C : IsEffectiveCartierDivisor Y₀)
  (hY₀reg : IsRegular Y₀.subscheme) (hyY₀ : y ∈ (Y₀.support : Set Y))

include hreg hdim hydim hY₀C hY₀reg hyY₀

/-- **The strict transform of `Y₀` meets the exceptional divisor in a single rational point, at
which the exceptional divisor restricts to the reduced point, and the conormal sheaf of the
strict transform is the invertible sheaf of that point.**

Precisely, writing `C` for the strict transform, there is a closed point `p` of `C` such that
* `p` lies over `y`, and it is the only point of `C` over `y`;
* the residue field map `κ(y) ⟶ κ(p)` is an isomorphism;
* `E|_C` is the reduced point `p`;
* for every `n`, the restriction of `𝒪_Z(-(n+1)C)` to `C` is `𝒪_C((n+1)p)`; for `n = 0` this is
  the conormal sheaf of `C`. -/
theorem exists_strictTransform_inter_exceptional (t : Γ(Y, ⊤))
    (hY₀t : Y₀ = Scheme.IdealSheafData.ofIdealTop (Ideal.span {t}))
    (ht : Y.presheaf.Γgerm y t ∉ maximalIdeal (Y.presheaf.stalk y) ^ 2) :
    ∃ (p : (strictTransformIdeal y hy Y₀).subscheme) (hp : IsClosed ({p} : Set _)),
      pointBlowupToBase y hy ((strictTransformIdeal y hy Y₀).subschemeι p) = y ∧
      (∀ q : (strictTransformIdeal y hy Y₀).subscheme,
        pointBlowupToBase y hy ((strictTransformIdeal y hy Y₀).subschemeι q) = y → q = p) ∧
      IsIso (((strictTransformIdeal y hy Y₀).subschemeι ≫ pointBlowupToBase y hy).residueFieldMap
        p) ∧
      (exceptionalIdeal (pointIdeal y hy)).comap (strictTransformIdeal y hy Y₀).subschemeι =
        Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩ ∧
      ∀ n : ℕ, Nonempty ((Scheme.Modules.pullback (strictTransformIdeal y hy Y₀).subschemeι).obj
        (Stacks.Divisors.negativeTwist (strictTransformIdeal y hy Y₀ ^ (n + 1))) ≅
          Stacks.Divisors.modulesInvertibleSheaf
            (Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩ ^ (n + 1))) := by
  classical
  set π := pointBlowupToBase y hy with hπ
  set E := exceptionalIdeal (pointIdeal y hy) with hEdef
  set C := strictTransformIdeal y hy Y₀ with hCdef
  set ι := C.subschemeι with hιdef
  set φ := strictTransformToFibre y hy Y₀ with hφdef
  have hφiso : IsIso φ := isIso_strictTransformToFibre y hy hdim hydim hY₀C hY₀reg hyY₀
  have hcomm : φ ≫ Y₀.subschemeι = ι ≫ π := strictTransformToFibre_comp_subschemeι y hy Y₀
  obtain ⟨y₀, hy₀⟩ : y ∈ Set.range Y₀.subschemeι := by rwa [Y₀.range_subschemeι]
  have hy₀closed : IsClosed ({y₀} : Set Y₀.subscheme) := by
    have h : Y₀.subschemeι ⁻¹' {y} = {y₀} := by
      ext w
      simp only [Set.mem_preimage, Set.mem_singleton_iff]
      exact ⟨fun hw => Y₀.subschemeι.isClosedEmbedding.injective (hw.trans hy₀.symm),
        fun hw => hw ▸ hy₀⟩
    rw [← h]
    exact hy.preimage Y₀.subschemeι.continuous
  set p : C.subscheme := φ.homeomorph.symm y₀ with hpdef
  have hφp : φ p = y₀ := φ.homeomorph.apply_symm_apply y₀
  have hp : IsClosed ({p} : Set C.subscheme) := by
    have h : φ.homeomorph.symm '' {y₀} = {p} := Set.image_singleton
    rw [← h]
    exact φ.homeomorph.symm.isClosedMap _ hy₀closed
  -- The exceptional divisor restricts to `C` as the reduced point `p`.
  have hEι : E.comap ι = ((pointIdeal y hy).comap Y₀.subschemeι).comap φ := by
    change ((pointIdeal y hy).comap π).comap ι = _
    rw [← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp, hcomm]
  have h1 : (pointIdeal y hy).comap Y₀.subschemeι =
      Scheme.IdealSheafData.vanishingIdeal ⟨{y₀}, hy₀closed⟩ := by
    have hc : pointIdeal y hy = centerIdeal (Y₀.subschemeι y₀) (hy₀ ▸ hy) := by
      subst hy₀
      rfl
    rw [hc]
    exact comap_centerIdeal_of_isClosedImmersion Y₀.subschemeι y₀ hy₀closed _
  have h2 : (Scheme.IdealSheafData.vanishingIdeal ⟨{y₀}, hy₀closed⟩).comap φ =
      Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩ := by
    have hc : Scheme.IdealSheafData.vanishingIdeal ⟨{y₀}, hy₀closed⟩ =
        centerIdeal (φ p) (hφp ▸ hy₀closed) := by
      unfold centerIdeal
      congr 1
      refine Closeds.ext ?_
      change ({y₀} : Set Y₀.subscheme) = {φ p}
      rw [hφp]
    rw [hc]
    exact comap_centerIdeal_of_isClosedImmersion φ p hp _
  have hcomap : E.comap ι = Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩ := by
    rw [hEι, h1, h2]
  have hπι : ∀ q : C.subscheme, π (ι q) = Y₀.subschemeι (φ q) := fun q =>
    (congrArg (fun k => k q) hcomm).symm
  refine ⟨p, hp, ?_, ?_, ?_, hcomap, ?_⟩
  · rw [hπι, hφp, hy₀]
  · intro q hq
    have hq' : Y₀.subschemeι (φ q) = Y₀.subschemeι y₀ := (hπι q).symm.trans (hq.trans hy₀.symm)
    apply φ.homeomorph.injective
    change φ q = φ p
    rw [hφp]
    exact Y₀.subschemeι.isClosedEmbedding.injective hq'
  · rw [← hcomm, Scheme.residueFieldMap_comp]
    have h1 := isIso_residueFieldMap_of_isClosedImmersion Y₀.subschemeι (φ p)
    have : IsOpenImmersion φ := inferInstance
    have h2 : IsIso (φ.residueFieldMap p) := inferInstance
    exact @IsIso.comp_isIso _ _ _ _ _ _ _ h1 h2
  -- The Picard computation.
  have hE : IsEffectiveCartierDivisor E :=
    Stacks.Blowup.isEffectiveCartierDivisor_exceptionalIdeal _
  have hC : IsEffectiveCartierDivisor C :=
    isEffectiveCartierDivisor_strictTransformIdeal y hy hreg hdim hydim hY₀C hY₀reg hyY₀
  have hEC : E * C = Y₀.comap π :=
    exceptionalIdeal_mul_strictTransformIdeal y hy hreg hdim hydim hY₀C hY₀reg hyY₀ t hY₀t ht
  -- The total transform has trivial invertible sheaf.
  have hT0 : Stacks.Divisors.picardClass (E * C) = 0 := by
    set f : Γ(pointBlowup y hy, ⊤) := π.appTop.hom t with hf
    set s := Stacks.FreeSheafMatrix.unitSection f with hs
    let L : (pointBlowup y hy).Modules := SheafOfModules.unit (pointBlowup y hy).ringCatSheaf
    have hzero : zeroScheme (pointBlowup y hy) L (s.eval (op ⊤)) = E * C := by
      have hTeq : Y₀.comap π = Scheme.IdealSheafData.ofIdealTop (Ideal.span {f}) := by
        rw [hY₀t, Stacks.IdealSheaf.comap_ofIdealTop, Ideal.map_span, Set.image_singleton]
      rw [hEC, hTeq]
      refine Scheme.IdealSheafData.ext ?_
      funext V
      rw [Stacks.Divisors.ideal_ofIdealTop_span_singleton]
      refine zeroScheme_ideal_of_trivialization (pointBlowup y hy) L (s.eval (op ⊤)) V
        (LinearEquiv.refl _ _) _ ?_
      change (pointBlowup y hy).presheaf.map _ ((pointBlowup y hy).presheaf.map _ f) = _
      rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
      rfl
    have hregs : IsRegularSection (pointBlowup y hy).sheaf.obj
        (pointBlowup y hy).ringCatSheaf.property s :=
      (isEffectiveCartierDivisor_zeroScheme_iff_isRegularSection (pointBlowup y hy)
        (SheafOfModules.unit (pointBlowup y hy).ringCatSheaf) s).mp
        (hzero ▸ (inferInstance : IsEffectiveCartierDivisor (E * C)))
    obtain ⟨e, -, -⟩ := existsUnique_invertibleSheafIso_zeroScheme (pointBlowup y hy)
      (SheafOfModules.unit (pointBlowup y hy).ringCatSheaf) s hregs
    have e' : Stacks.Divisors.invertibleSheaf' (E * C) ≅
        _root_.SheafOfModules.unit (Stacks.SheafOfModules.TensorSheafification.structureSheaf
          (pointBlowup y hy).presheaf (Stacks.RingedSpace.structureIsSheaf
            (pointBlowup y hy).toRingedSpace)) := by
      rw [← hzero]
      exact e
    refine Eq.trans ?_ (Stacks.SheafOfModules.picardClass_zero (pointBlowup y hy).presheaf
      (Stacks.RingedSpace.structureIsSheaf (pointBlowup y hy).toRingedSpace))
    exact (Stacks.SheafOfModules.picardClass_eq_iff _ _ _ _ _ _).2 ⟨e'⟩
  -- `E|_C` is an effective Cartier divisor on `C`.
  have hEιC : IsEffectiveCartierDivisor (E.comap ι) := by
    rw [hEι]
    exact Stacks.Divisors.isPullbackDefined_of_flat φ _
      (comap_centerIdeal_isEffectiveCartierDivisor Y₀
        (topologicalKrullDim_fibre y hdim hydim hY₀C hY₀reg hyY₀) y hy y₀ hy₀
        (hY₀reg.isRegularLocalRing_stalk y₀))
  have hV : IsEffectiveCartierDivisor (Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩) :=
    hcomap ▸ hEιC
  have hpull : Stacks.Picard.schemePullbackClass ι (Stacks.Divisors.picardClass E) =
      Stacks.Divisors.picardClass (Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩) := by
    have : Stacks.Divisors.IsPullbackDefined ι E := hEιC
    have := hEιC
    refine (Stacks.Picard.pullbackClass_classOf ι.toLRSHom.toShHom
      (Stacks.Divisors.invertibleSheaf' E)
      (Stacks.Divisors.isInvertible_invertibleSheaf_picard E)).trans ?_
    refine Eq.trans ?_ (Stacks.Divisors.picardClass_congr hcomap)
    exact (Stacks.SheafOfModules.picardClass_eq_iff _ _ _ _ _
      (Stacks.Divisors.isInvertible_invertibleSheaf_picard (E.comap ι))).2
        ⟨Stacks.Divisors.invertibleSheafPullbackIso ι E⟩
  intro n
  have hneg : Stacks.Divisors.negativeTwistPicardClass (C ^ (n + 1)) =
      ((n + 1 : ℕ) : ℤ) • Stacks.Divisors.picardClass E := by
    rw [Stacks.Divisors.negativeTwistPicardClass_eq_neg, Stacks.Divisors.picardClass_pow]
    have h := Stacks.Divisors.picardClass_mul E C
    rw [hT0] at h
    have hc : Stacks.Divisors.picardClass C = -Stacks.Divisors.picardClass E := by
      rw [eq_neg_iff_add_eq_zero, add_comm]
      exact h.symm
    rw [hc, zsmul_neg, neg_neg]
  have hcomp : ∀ x : Stacks.Picard.ofScheme (pointBlowup y hy),
      Stacks.Picard.schemePullbackClass ι x = Stacks.Picard.schemePullbackClassHom ι x :=
    fun _ => rfl
  have key : Stacks.Picard.schemePullbackClass ι
      (Stacks.Divisors.negativeTwistPicardClass (C ^ (n + 1))) =
      Stacks.Divisors.picardClass (Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩ ^ (n + 1)) := by
    rw [hneg, hcomp, map_zsmul, ← hcomp, hpull, Stacks.Divisors.picardClass_pow]
  have hL := Stacks.Picard.pullbackClass_classOf ι.toLRSHom.toShHom
    (Stacks.Divisors.negativeTwist' (C ^ (n + 1)))
    (Stacks.Divisors.isInvertible_negativeTwist_picard (C ^ (n + 1)))
  obtain ⟨e⟩ := (Stacks.SheafOfModules.picardClass_eq_iff _ _ _ _ _ _).1 (hL.symm.trans key)
  exact ⟨e⟩

end Surface

end Stacks.Examples.CurveFamilyNotScheme

end
