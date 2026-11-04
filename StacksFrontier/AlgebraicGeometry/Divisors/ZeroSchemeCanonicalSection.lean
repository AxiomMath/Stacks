module

public import StacksFrontier.AlgebraicGeometry.Divisors.CanonicalSectionNonvanishing
public import StacksFrontier.AlgebraicGeometry.Divisors.ZeroSchemeExactSequence
public import StacksFrontier.AlgebraicGeometry.InvertibleTrivialization.Basic

/-!
# The zero scheme of the canonical section is the divisor

Let `X` be a scheme and `D ⊆ X` an effective Cartier divisor. Tag 01WX gives the invertible
sheaf `𝒪_X(D) = SheafHom(ℐ_D, 𝒪_X)` and its canonical global section `1_D`, the one
corresponding to the inclusion `ℐ_D ⟶ 𝒪_X`, and Tag 02OQ gives the zero scheme `Z(s)` of a
global section of an invertible module. This file identifies the two:

`Z(1_D) = D`.

That is the composite `D ↦ (𝒪_X(D), 1_D) ↦ Z(1_D)` of the two constructions
[Stacks, Tag 01X0](https://stacks.math.columbia.edu/tag/01X0) asserts are mutually inverse, and
with Tag 02OR (4) — `AlgebraicGeometry.isEffectiveCartierDivisor_zeroScheme_iff_isRegularSection`
— it gives clause (1) of that tag, that `1_D` is a regular section.

## Main definitions

* `Stacks.Divisors.idealInclusionValue`: the image in `𝒪_X` of a section of `ℐ_D`, with the
  codomain *declared* as `Γ(X, V)`.
* `Stacks.Divisors.evalPairing`: the evaluation pairing `𝒪_X(D)(V) × ℐ_D(V) → Γ(X, V)` on
  sections, with the codomain likewise declared as `Γ(X, V)`.
* `AlgebraicGeometry.IsShortExactUnitSequence`: the assertion of [Stacks, Tag 0C6K] with the
  closed subscheme as a separate argument.

## Main results

* `Stacks.Divisors.zeroScheme_canonicalSection'`: **`Z(1_D) = D`.**
* `Stacks.Divisors.isRegularSection_canonicalSections`: the canonical section of `𝒪_X(D)` is
  regular.
* `Stacks.Divisors.isShortExactUnitSequence_canonicalSections`: the sequence
  `0 ⟶ 𝒪_X ⟶ 𝒪_X(D) ⟶ i_* i^* 𝒪_X(D) ⟶ 0` of [Stacks, Tag 0C6K] **at `i = D.subschemeι`**,
  rather than at the zero scheme of the section.
* `Stacks.Divisors.mem_ideal_iff_exists_idealInclusionValue`: on an affine open, the ideal of
  `D` is exactly the image of `ℐ_D ⟶ 𝒪_X`.

## References

* [Stacks Project, Tag 01X0](https://stacks.math.columbia.edu/tag/01X0)
* [Stacks Project, Tag 01WX](https://stacks.math.columbia.edu/tag/01WX)
* [Stacks Project, Tag 02OQ](https://stacks.math.columbia.edu/tag/02OQ)
* [Stacks Project, Tag 02OR](https://stacks.math.columbia.edu/tag/02OR)
* [Stacks Project, Tag 0C6K](https://stacks.math.columbia.edu/tag/0C6K)
* [Stacks Project, Tag 0B8M](https://stacks.math.columbia.edu/tag/0B8M)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.SheafOfModules.TensorStalkRingedSpace (ringStalk)

universe u

namespace AlgebraicGeometry

variable {X : Scheme.{u}}

/-- **The assertion of [Stacks, Tag 0C6K] with the closed subscheme as a parameter.** For a
closed subscheme `I ⊆ X` with inclusion `i`, an `𝒪_X`-module `L` and a global section `s`, the
sequence `0 ⟶ 𝒪_X ⟶ L ⟶ i_* i^* L ⟶ 0` is short exact, with the first map multiplication by `s`
and the second the unit of the pullback–pushforward adjunction. -/
def IsShortExactUnitSequence (I : X.IdealSheafData) (L : X.Modules) (s : L.sections) : Prop :=
  let i := I.subschemeι
  let O : X.Modules := SheafOfModules.unit X.ringCatSheaf
  let f : O ⟶ L := L.unitHomEquiv.symm s
  let g : L ⟶ (Scheme.Modules.pushforward i).obj ((Scheme.Modules.pullback i).obj L) :=
    (Scheme.Modules.pullbackPushforwardAdjunction i).unit.app L
  ∃ h : f ≫ g = 0, (ShortComplex.mk f g h).ShortExact

/-- **[Stacks, Tag 0C6K], second assertion, as `IsShortExactUnitSequence`.** -/
theorem isShortExactUnitSequence_zeroScheme (L : X.Modules)
    [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L] (s : L.sections)
    (hs : IsRegularSection X.sheaf.obj X.ringCatSheaf.property s) :
    IsShortExactUnitSequence (zeroScheme X L (s.eval (op ⊤))) L s :=
  shortExact_zeroScheme_of_isRegularSection X L s hs

end AlgebraicGeometry

namespace Stacks.Divisors

variable {X : Scheme.{u}} (D : X.IdealSheafData)

/-- `𝒪_X(D)` read as an object of `X.Modules`. The two are the same object: `X.Modules` is
`SheafOfModules X.ringCatSheaf` and `X.ringCatSheaf` is `structureSheafRing X.toRingedSpace`. -/
noncomputable abbrev modulesInvertibleSheaf : X.Modules := invertibleSheaf D

/-- **The image in `𝒪_X` of a section of `ℐ_D`**, with the codomain declared as `Γ(X, V)`. -/
noncomputable abbrev idealInclusionValue (V : Opens X.carrier)
    (b : (negativeTwist D).val.obj (op V)) : Γ(X, V) :=
  ((idealInclusion D).val.app (op V)).hom b

/-- **The evaluation pairing `𝒪_X(D)(V) × ℐ_D(V) → Γ(X, V)` on sections.** This is
`Stacks.SheafOfModules.evalSection` with the codomain declared as `Γ(X, V)`. -/
noncomputable abbrev evalPairing (V : Opens X.carrier) (z : Γ(modulesInvertibleSheaf D, V))
    (b : (negativeTwist D).val.obj (op V)) : Γ(X, V) :=
  Stacks.SheafOfModules.evalSection X.presheaf (negativeTwist D).val
    (SheafOfModules.unit (structureSheafRing X.toRingedSpace)).val (op V) z b

/-- The pairing is `Γ(X, V)`-linear in the section of `𝒪_X(D)`. -/
theorem evalPairing_smul (V : Opens X.carrier) (c : Γ(X, V))
    (z : Γ(modulesInvertibleSheaf D, V)) (b : (negativeTwist D).val.obj (op V)) :
    evalPairing D V (c • z) b = c • evalPairing D V z b :=
  Stacks.SheafOfModules.evalSection_smul_left X.presheaf (negativeTwist D).val
    (SheafOfModules.unit (structureSheafRing X.toRingedSpace)).val (op V) c z b

/-- **The canonical section pairs with a section of `ℐ_D` to its image in `𝒪_X`.** This is
`Stacks.Divisors.evalSection_canonicalSections` with the declared codomain. -/
theorem evalPairing_canonicalSections (V : Opens X.carrier)
    (b : (negativeTwist D).val.obj (op V)) :
    evalPairing D V ((canonicalSections D).eval (op V)) b = idealInclusionValue D V b :=
  evalSection_canonicalSections D V b

/-- **On an affine open the ideal of `D` is exactly the image of `ℐ_D ⟶ 𝒪_X`.** -/
theorem mem_ideal_iff_exists_idealInclusionValue (V : X.affineOpens) (t : Γ(X, V.1)) :
    t ∈ D.ideal V ↔
      ∃ b : (negativeTwist D).val.obj (op V.1), idealInclusionValue D V.1 b = t := by
  rw [← D.ker_subschemeι_app V]
  refine ⟨fun ht => ⟨(kernelIdealSheafIso D).inv.val.app (op V.1) (mkKernelSection D t ht),
    (idealInclusion_val_app_kernelIdealSheafIso_inv D V.1 _).trans
      (kernelSection_mkKernelSection D t ht)⟩, ?_⟩
  rintro ⟨b, rfl⟩
  have h := kernelSection_mem D ((kernelIdealSheafIso D).hom.val.app (op V.1) b)
  rwa [kernelSection_kernelIdealSheafIso_hom] at h

/-- The canonical section, read as a global section of the sheaf, has value `1_D` over `⊤`. -/
theorem canonicalSections_eval_top :
    (canonicalSections D).eval (op (⊤ : Opens X.carrier)) = canonicalSection D :=
  Stacks.SheafOfModules.sectionsOfTop_eval_top (invertibleSheaf D) (canonicalSection D)

variable [hD : IsEffectiveCartierDivisor D]

/-- **The two ideals agree on an affine open carrying a trivializing pair.** If `w` is a section
of `𝒪_X(D)` and `v` a section of `ℐ_D` over an affine open `V` pairing to `1`, and `w`
trivializes `𝒪_X(D)` over `V`, then `ℐ_{Z(1_D)}(V) = ℐ_D(V)`, both being generated by the image
of `v` in `𝒪_X`. -/
theorem ideal_zeroScheme_canonicalSection_eq_of_evalPairing_eq_one (V : X.affineOpens)
    (w : Γ(modulesInvertibleSheaf D, V.1)) (v : (negativeTwist D).val.obj (op V.1))
    (hone : evalPairing D V.1 w v = 1)
    (hbij : Function.Bijective fun c : Γ(X, V.1) => c • w) :
    (zeroScheme X (modulesInvertibleSheaf D) (canonicalSection D)).ideal V = D.ideal V := by
  obtain ⟨r, hr⟩ := hbij.2 ((canonicalSections D).eval (op V.1))
  have hr' : r • w = (canonicalSections D).eval (op V.1) := hr
  have hpair : ∀ b, idealInclusionValue D V.1 b = r * evalPairing D V.1 w b := fun b => by
    rw [← evalPairing_canonicalSections, ← hr', evalPairing_smul, smul_eq_mul]
  have hzs : (zeroScheme X (modulesInvertibleSheaf D) (canonicalSection D)).ideal V
      = Ideal.span {r} := by
    let e := LinearEquiv.ofBijective
      (LinearMap.toSpanSingleton Γ(X, V.1) Γ(modulesInvertibleSheaf D, V.1) w) hbij
    exact zeroScheme_ideal_of_trivialization X (modulesInvertibleSheaf D) (canonicalSection D)
      V e.symm _ (by
        change e.symm ((canonicalSections D).eval (op V.1)) = r
        rw [← hr']; exact e.symm_apply_apply _)
  rw [hzs]
  refine le_antisymm (Ideal.span_le.mpr ?_) fun t ht => ?_
  · rintro t ht
    rcases Set.mem_singleton_iff.mp ht with rfl
    refine (mem_ideal_iff_exists_idealInclusionValue D V _).mpr ⟨v, ?_⟩
    rw [hpair, hone, mul_one]
  · obtain ⟨b, rfl⟩ := (mem_ideal_iff_exists_idealInclusionValue D V t).mp ht
    rw [hpair]
    exact Ideal.mul_mem_right _ _ (Ideal.subset_span rfl)

/-- **Every point has an affine neighbourhood on which `ℐ_{Z(1_D)}` and `ℐ_D` agree.** -/
theorem exists_affineOpen_ideal_zeroScheme_canonicalSection_eq (x : X) :
    ∃ V : X.affineOpens, x ∈ V.1 ∧
      (zeroScheme X (modulesInvertibleSheaf D) (canonicalSection D)).ideal V = D.ideal V := by
  have hlocal : ∀ z : X.toRingedSpace.carrier, IsLocalRing (ringStalk X.toRingedSpace z) :=
    fun z => X.isLocalRing z
  have hinv := stacksIsInvertible_negativeTwist D
  obtain ⟨W, hxW, w, v, hwv⟩ :=
    Stacks.SheafOfModules.exists_tensorPairing_eq_unitSection
      (Stacks.SheafOfModules.Scheme.evaluationIso X (negativeTwist D)) x
  obtain ⟨-, ⟨V, hV, rfl⟩, hxV, hVW⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hxW W.isOpen
  have hVW' : V ≤ W := hVW
  refine ⟨⟨V, hV⟩, hxV, ?_⟩
  refine ideal_zeroScheme_canonicalSection_eq_of_evalPairing_eq_one D ⟨V, hV⟩
    ((modulesInvertibleSheaf D).presheaf.map (homOfLE hVW').op w)
    ((negativeTwist D).val.map (homOfLE hVW').op v) ?_ ?_
  · refine (Stacks.SheafOfModules.tensorPairing_evaluationIso (negativeTwist D) V _ _).symm.trans
      ((Stacks.SheafOfModules.tensorPairing_res
        (Stacks.SheafOfModules.Scheme.evaluationIso X (negativeTwist D))
        (homOfLE hVW') w v).symm.trans ?_)
    rw [hwv]
    exact map_one ((structureSheafRing X.toRingedSpace).obj.map (homOfLE hVW').op).hom
  · exact Stacks.SheafOfModules.bijective_smul_of_tensorPairing_eq_unitSection _ W w v hwv V hVW'

/-- **`Z(1_D) = D`.** The zero scheme of the canonical section of `𝒪_X(D)` is `D` itself: the
composite `D ↦ (𝒪_X(D), 1_D) ↦ Z(1_D)` is the identity. -/
@[stacks 01X0 "zeroScheme_canonicalSection"]
theorem zeroScheme_canonicalSection' :
    zeroScheme X (modulesInvertibleSheaf D) (canonicalSection D) = D := by
  choose V hV hideal using exists_affineOpen_ideal_zeroScheme_canonicalSection_eq D
  exact Scheme.IdealSheafData.ext_of_iSup_eq_top V
    (top_le_iff.mp fun z _ => TopologicalSpace.Opens.mem_iSup.mpr ⟨z, hV z⟩) hideal

/-- `Z(1_D) = D`, with the section in the `PresheafOfModules.sections` form. -/
theorem zeroScheme_canonicalSections :
    zeroScheme X (modulesInvertibleSheaf D) ((canonicalSections D).eval (op ⊤)) = D := by
  rw [canonicalSections_eval_top, zeroScheme_canonicalSection' D]

/-- The canonical section `1_D` of `𝒪_X(D)` is a regular section, i.e. a nonzerodivisor
([Stacks, Tag 01WY]). -/
@[stacks 01X0 "canonical_section_regular"]
theorem isRegularSection_canonicalSections :
    IsRegularSection X.sheaf.obj X.ringCatSheaf.property (canonicalSections D) := by
  refine (isEffectiveCartierDivisor_zeroScheme_iff_isRegularSection X
    (modulesInvertibleSheaf D) (canonicalSections D)).mp ?_
  rwa [zeroScheme_canonicalSections D]

/-- **[Stacks, Tag 0C6K] at the divisor.** For an effective Cartier divisor `D ⊆ X` with
inclusion `i`, the sequence

`0 ⟶ 𝒪_X ⟶ 𝒪_X(D) ⟶ i_* i^* 𝒪_X(D) ⟶ 0`

is short exact, the first map being multiplication by the canonical section `1_D`. -/
theorem isShortExactUnitSequence_canonicalSections :
    IsShortExactUnitSequence D (modulesInvertibleSheaf D) (canonicalSections D) := by
  have key := isShortExactUnitSequence_zeroScheme (modulesInvertibleSheaf D) (canonicalSections D)
    (isRegularSection_canonicalSections D)
  rwa [zeroScheme_canonicalSections D] at key

end Stacks.Divisors

end
