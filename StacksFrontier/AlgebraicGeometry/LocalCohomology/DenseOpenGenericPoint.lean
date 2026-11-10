module

public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Stalk
public import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
public import Mathlib.RingTheory.AdicCompletion.LocalRing
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.PuncturedSpectrum
import StacksCore.Tactic.EgaSgaAttribute

/-!
# A nonempty open of an integral scheme, seen from a local ring

Let `X` be an integral scheme, `U` a nonempty open of `X` and `z` a point of `X` outside `U`.
This file compares the sections of the structure sheaf of `Spec 𝒪_{X,z}` over the preimage of
`U` with the sections over the *whole* punctured spectrum of `𝒪_{X,z}`, and transports the
punctured spectrum of a local ring along the completion map.

This is the step of [Stacks, Tag 0AWC] which the source calls "shrink/enlarge `U` to the
punctured spectrum". Two facts make it work and both need `X` to be integral:

* the generic point of `X` lies in every nonempty open and specializes to every point, so it is
  in the image of `Spec 𝒪_{X,z} ⟶ X`; hence the preimage of `U` in `Spec 𝒪_{X,z}` is a *nonempty*
  open, which avoids the closed point because `z ∉ U`;
* `𝒪_{X,z}` is a domain, so restriction between opens of `Spec 𝒪_{X,z}` along an inclusion with
  nonempty source is injective (`AlgebraicGeometry.map_injective_of_isIntegral`). Finiteness of
  the sections over the smaller open therefore *implies* finiteness over the larger one, over a
  Noetherian ring.

## Main definitions

* `Stacks.LocalCohomology.sectionsRestrict`: restriction of sections of `𝒪_{Spec R}` along an
  inclusion of opens, as an `R`-linear map.

## Main results

* `Stacks.LocalCohomology.genericPoint_mem_of_isOpen`: in a quasi-sober irreducible space the
  generic point lies in every nonempty open.
* `Stacks.LocalCohomology.nonempty_preimage_fromSpecStalk`: for `X` integral and `U` a nonempty
  open, the preimage of `U` along `Spec 𝒪_{X,z} ⟶ X` is nonempty — it contains a point over the
  generic point of `X`.
* `Stacks.LocalCohomology.preimage_fromSpecStalk_le_puncturedSpectrum`: if `z ∉ U` that preimage
  avoids the closed point, so it is contained in the punctured spectrum.
* `Stacks.LocalCohomology.module_finite_sections_of_le`: over a Noetherian domain `R`, finiteness
  of `Γ(Spec R, V')` for a nonempty `V' ≤ V` forces finiteness of `Γ(Spec R, V)`.
* `Stacks.LocalCohomology.module_finite_sections_puncturedSpectrum_of_preimage`: the three
  combined — the "enlarge `U` to the punctured spectrum" step of [Stacks, Tag 0AWC].
* `Stacks.LocalCohomology.preimage_puncturedSpectrum_of_map_maximalIdeal` and
  `Stacks.LocalCohomology.preimage_puncturedSpectrum_adicCompletion`: the punctured spectrum pulls
  back to the punctured spectrum along a homomorphism of local rings which maps the maximal ideal
  *onto* an ideal generating the maximal ideal, in particular along the completion map of a
  Noetherian local ring.

## References

* [Stacks Project, Tag 0AWC](https://stacks.math.columbia.edu/tag/0AWC)
* [Stacks Project, Tag 0E9I](https://stacks.math.columbia.edu/tag/0E9I)
* [Stacks Project, Tag 02KH](https://stacks.math.columbia.edu/tag/02KH)
* [Stacks Project, Tag 05AZ](https://stacks.math.columbia.edu/tag/05AZ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite

universe u

namespace Stacks.LocalCohomology

/-! ### The generic point and nonempty opens -/

/-- **The generic point lies in every nonempty open** of a quasi-sober irreducible space. -/
@[ega "0 2.1.2" "special case", ega "0 2.1.4" "partial"]
theorem genericPoint_mem_of_isOpen {α : Type*} [TopologicalSpace α] [QuasiSober α]
    [IrreducibleSpace α] {s : Set α} (hs : IsOpen s) (h : s.Nonempty) : genericPoint α ∈ s :=
  (genericPoint_specializes h.choose).mem_open hs h.choose_spec

/-- **A nonempty open of an integral scheme pulls back to a nonempty open of `Spec 𝒪_{X,z}`.** -/
theorem nonempty_preimage_fromSpecStalk {X : Scheme.{u}} [IsIntegral X] (z : X) (U : X.Opens)
    (hU : (U : Set X).Nonempty) :
    Nonempty (X.fromSpecStalk z ⁻¹ᵁ U) := by
  obtain ⟨w, hw⟩ : genericPoint (X : Type u) ∈ Set.range (X.fromSpecStalk z) := by
    rw [Scheme.range_fromSpecStalk]
    exact genericPoint_specializes z
  refine ⟨⟨w, ?_⟩⟩
  change X.fromSpecStalk z w ∈ U
  exact hw ▸ genericPoint_mem_of_isOpen U.isOpen hU

/-- **The preimage of an open missing `z` avoids the closed point**: if `z ∉ U`, then the
preimage of `U` in `Spec 𝒪_{X,z}` is contained in the punctured spectrum. -/
theorem preimage_fromSpecStalk_le_puncturedSpectrum {X : Scheme.{u}} (z : X) (U : X.Opens)
    (hz : z ∉ U) :
    X.fromSpecStalk z ⁻¹ᵁ U ≤ puncturedSpectrum (X.presheaf.stalk z) := by
  intro x hx
  change x ≠ IsLocalRing.closedPoint (ToType (X.presheaf.stalk z))
  intro hx0
  refine hz ?_
  have : X.fromSpecStalk z x ∈ U := hx
  rwa [hx0, Scheme.fromSpecStalk_closedPoint] at this

/-! ### Restriction of sections on an affine scheme -/

/-- **Restriction of sections of `𝒪_{Spec R}`, as an `R`-linear map.** For `V' ≤ V` opens of
`Spec R` this is `Γ(Spec R, V) ⟶ Γ(Spec R, V')`. -/
def sectionsRestrict (R : CommRingCat.{u}) {V V' : (Spec R).Opens} (h : V' ≤ V) :
    Γ(Spec R, V) →ₗ[R] Γ(Spec R, V') where
  toFun x := (Spec R).presheaf.map (homOfLE h).op x
  map_add' _ _ := map_add _ _ _
  map_smul' r x := by
    have halg : ∀ W : (Spec R).Opens, algebraMap (ToType R) Γ(Spec R, W) r =
        (Spec R).presheaf.map W.leTop.op ((Scheme.ΓSpecIso R).inv r) := fun _ => rfl
    have hcomp : V.leTop.op ≫ (homOfLE h).op = V'.leTop.op := Subsingleton.elim _ _
    have hkey := ConcreteCategory.congr_hom
      (((Spec R).presheaf.map_comp V.leTop.op (homOfLE h).op).symm.trans
        (congrArg (Spec R).presheaf.map hcomp)) ((Scheme.ΓSpecIso R).inv r)
    simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply] at hkey
    change (Spec R).presheaf.map (homOfLE h).op (r • x) =
      r • (Spec R).presheaf.map (homOfLE h).op x
    rw [Algebra.smul_def, Algebra.smul_def, map_mul, halg V, halg V', hkey]

/-- `Stacks.LocalCohomology.sectionsRestrict` is the restriction map of the structure presheaf. -/
@[simp]
theorem sectionsRestrict_apply (R : CommRingCat.{u}) {V V' : (Spec R).Opens} (h : V' ≤ V)
    (x : Γ(Spec R, V)) :
    sectionsRestrict R h x = (Spec R).presheaf.map (homOfLE h).op x := rfl

/-- **Finiteness of sections grows with the open, on an integral affine scheme.** Let `R` be a
Noetherian domain and `V' ≤ V` opens of `Spec R` with `V'` nonempty. If `Γ(Spec R, V')` is a
finite `R`-module then so is `Γ(Spec R, V)`. -/
theorem module_finite_sections_of_le (R : CommRingCat.{u}) [IsNoetherianRing R] [IsDomain R]
    {V V' : (Spec R).Opens} (h : V' ≤ V) [Nonempty V']
    (hfin : Module.Finite (ToType R) Γ(Spec R, V')) :
    Module.Finite (ToType R) Γ(Spec R, V) :=
  Module.Finite.of_injective (sectionsRestrict R h)
    (map_injective_of_isIntegral (Spec R) (homOfLE h))

/-- **The "enlarge `U` to the punctured spectrum" step of [Stacks, Tag 0AWC].**

Let `X` be an integral locally Noetherian scheme, `U` a nonempty open and `z ∈ X ∖ U`. If the
sections of `𝒪_{Spec 𝒪_{X,z}}` over the preimage of `U` are a finite `𝒪_{X,z}`-module, then so
are the sections over the whole punctured spectrum of `𝒪_{X,z}`. -/
theorem module_finite_sections_puncturedSpectrum_of_preimage {X : Scheme.{u}} [IsIntegral X]
    [IsLocallyNoetherian X] (z : X) (U : X.Opens) (hU : (U : Set X).Nonempty) (hz : z ∉ U)
    (hfin : Module.Finite (ToType (X.presheaf.stalk z))
      Γ(Spec (X.presheaf.stalk z), X.fromSpecStalk z ⁻¹ᵁ U)) :
    Module.Finite (ToType (X.presheaf.stalk z))
      Γ(Spec (X.presheaf.stalk z), puncturedSpectrum (X.presheaf.stalk z)) :=
  have : Nonempty (X.fromSpecStalk z ⁻¹ᵁ U) :=
    nonempty_preimage_fromSpecStalk z U hU
  module_finite_sections_of_le (X.presheaf.stalk z)
    (preimage_fromSpecStalk_le_puncturedSpectrum z U hz) hfin

/-! ### The punctured spectrum along the completion map -/

/-- **The punctured spectrum pulls back to the punctured spectrum along a homomorphism of local
rings whose target's maximal ideal is generated by the image of the source's.** -/
theorem preimage_puncturedSpectrum_of_map_maximalIdeal {R S : CommRingCat.{u}} [IsLocalRing R]
    [IsLocalRing S] (φ : R ⟶ S)
    (hφ : Ideal.map φ.hom (IsLocalRing.maximalIdeal (ToType R)) =
      IsLocalRing.maximalIdeal (ToType S)) :
    Spec.map φ ⁻¹ᵁ puncturedSpectrum R = puncturedSpectrum S := by
  have hloc : IsLocalHom φ.hom :=
    ((IsLocalRing.local_hom_TFAE φ.hom).out 3 1).mp (le_of_eq hφ)
  refine TopologicalSpace.Opens.ext (Set.ext fun x => ?_)
  change PrimeSpectrum.comap φ.hom x ≠ IsLocalRing.closedPoint (ToType R) ↔
    x ≠ IsLocalRing.closedPoint (ToType S)
  rw [not_iff_not]
  refine ⟨fun h => ?_, fun h => h ▸ IsLocalRing.comap_closedPoint φ.hom⟩
  have hx : IsLocalRing.maximalIdeal (ToType R) ≤ Ideal.comap φ.hom x.asIdeal :=
    le_of_eq (congrArg PrimeSpectrum.asIdeal h).symm
  have : IsLocalRing.maximalIdeal (ToType S) ≤ x.asIdeal :=
    hφ ▸ Ideal.map_le_iff_le_comap.mpr hx
  exact PrimeSpectrum.ext
    ((IsLocalRing.maximalIdeal.isMaximal (ToType S)).eq_of_le x.isPrime.ne_top this).symm

/-- **The punctured spectrum pulls back to the punctured spectrum along the completion map** of a
Noetherian local ring. -/
theorem preimage_puncturedSpectrum_adicCompletion (R : CommRingCat.{u}) [IsNoetherianRing R]
    [IsLocalRing R] :
    Spec.map (CommRingCat.ofHom (algebraMap (ToType R)
          (AdicCompletion (IsLocalRing.maximalIdeal (ToType R)) (ToType R)))) ⁻¹ᵁ
        puncturedSpectrum R =
      puncturedSpectrum (CommRingCat.of
        (AdicCompletion (IsLocalRing.maximalIdeal (ToType R)) (ToType R))) :=
  preimage_puncturedSpectrum_of_map_maximalIdeal _
    (AdicCompletion.maximalIdeal_eq_map_of_fg
      (IsNoetherian.noetherian (IsLocalRing.maximalIdeal (ToType R)))).symm

end Stacks.LocalCohomology

end
