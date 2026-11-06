module

public import Mathlib.CategoryTheory.Abelian.Pseudoelements
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.BitUniformityIII.AmbientShortExact
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.BitUniformityIII.BaseThreshold
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.BitUniformityIII.ThickeningVanishingAboveDegree

/-!
# The first map `𝒪_{Yₙ}(q+1) ⟶ 𝒪_{Y_{n+1}}(q)` of the first sequence of Tag 0GA7

Let `A` be a commutative ring, `I ⊆ A` an ideal and `X = Proj(⨁ₙ Iⁿ)` the blowup of `Spec(A)`
in `I`, with exceptional divisor `Y` and thickenings `Yₙ = nY`. The proof of
[Stacks, Tag 0GA7] uses the short exact sequence

  `0 → 𝒪_{Yₙ}(q+1) → 𝒪_{Y_{n+1}}(q) → 𝒪_Y(q) → 0`

on `X`. This file constructs its first map and proves its three properties, which are the last
four fields of `Stacks.LocalCohomology.UniformityIII.GeometricInput` — `divα`, `div_comp`,
`div_shortExact` and `div_sq_left` — and then **inhabits that structure** (`geometricInput`), so
everything proved from `GeometricInput` holds for a Noetherian base ring.

## What the map is

It is `𝒪_X(q+1) ⟶ 𝒪_X(q)` passed to the quotients. Precisely, the square

  `𝒪_X(q+1) → 𝒪_X(q)`
  `   ↓            ↓`
  `𝒪_{Yₙ}(q+1) → 𝒪_{Y_{n+1}}(q)`

is to be filled in, the vertical maps being the canonical surjections. Since
`𝒪_X(q+1) ⟶ 𝒪_{Yₙ}(q+1)` is an epimorphism, `CategoryTheory.Abelian.epiDesc` fills it in as
soon as the composite `𝒪_X(q+1) → 𝒪_X(q) → 𝒪_{Y_{n+1}}(q)` kills the kernel of the left
vertical map — and then the filling is unique, so `div_comp` and `div_sq_left` are both read off
the square by cancelling the epimorphism.

## The one containment, and why no comparison of ideal powers is needed

The kernel in question is `ℐⁿ·𝒪_X(q+1)`, and the containment to prove is

  `ambientTwistMap(ℐⁿ·𝒪_X(q+1)) ⊆ ℐⁿ⁺¹·𝒪_X(q)`,

the right-hand side being the kernel of `𝒪_X(q) ⟶ 𝒪_{Y_{n+1}}(q)`. No comparison between the
*tensor* power of `ℐ_Y` and the `AlgebraicGeometry.Scheme.IdealSheafData` power
`thickeningIdeal I n` is needed; two results do the work:

* `Stacks.LocalCohomology.UniformityIII.isIso_kernelLift_twistedThickeningIdealMap`, which holds
  for **every** `n` and `q`: `ℐ_{Yₙ} ⊗ 𝒪_X(q)` *is* the kernel of `𝒪_X(q) ⟶ 𝒪_{Yₙ}(q)`. So the
  containment need only be checked after precomposition with `twistedThickeningIdealMap`, whose
  source is a tensor product — and a morphism out of a sheafified tensor product is determined
  by its values on local pure tensors, `Stacks.SheafOfModules.OnSpace.tensor_hom_ext`.
* `Stacks.Blowup.exists_restrict_appTwistShift_eq_smul`: near any point the image of a section
  under `𝒪_X(q+1) ⟶ 𝒪_X(q)` is `b·`(a section), for some `b ∈ I` — the local half of
  [Stacks, Tag 02OS] part (3).

On a pure tensor `a ⊗ c` the composite is therefore the pure tensor of the image of `1` with
`a·b·`(a section), and `a·b` is killed by `𝒪_X ⟶ 𝒪_{Y_{n+1}}`: the ideal powers enter only
through `AlgebraicGeometry.Scheme.IdealSheafData.ideal_pow`, which says that on an affine open
the ideal of `thickeningIdeal I n` is literally the `n`-th power of the ideal of
`thickeningIdeal I 1`. That is the content of `app_thickeningProj_mul_eq_zero` below, and it is
a statement about ideals of a commutative ring, with no sheafified tensor product in it.

## Main definitions

* `Stacks.LocalCohomology.UniformityIII.divα`: **the map `𝒪_{Yₙ}(q+1) ⟶ 𝒪_{Y_{n+1}}(q)`**, the
  field `divα` of `GeometricInput`.
* `Stacks.LocalCohomology.UniformityIII.geometricInput`: **a witness for `GeometricInput`**, for a
  Noetherian base ring.

## Main results

* `Stacks.LocalCohomology.UniformityIII.app_thickeningProj_mul_eq_zero`: a product of a section
  killed by `𝒪_X ⟶ 𝒪_{Yₙ}` and one killed by `𝒪_X ⟶ 𝒪_{Yₘ}` is killed by
  `𝒪_X ⟶ 𝒪_{Y_{n+m}}`.
* `Stacks.LocalCohomology.UniformityIII.thickeningTwistProj_comp_divα`: the defining square.
* `Stacks.LocalCohomology.UniformityIII.divα_comp_thickeningTwistRestrict_eq_zero`: **the field
  `div_comp`**.
* `Stacks.LocalCohomology.UniformityIII.blowupΓMap_divα_thickeningSections`: **the field
  `div_sq_left`**.
* `Stacks.LocalCohomology.UniformityIII.exact_twistedDiv`: `ambientTwistMap I q` carries
  `ℐⁿ·𝒪_X(q+1)` *onto* `ℐⁿ⁺¹·𝒪_X(q)` — the surjectivity half of the ideal-power multiplication,
  and the only input the exactness of the first sequence needs beyond the defining square.
* `Stacks.LocalCohomology.UniformityIII.shortExact_divα`: **the field `div_shortExact`**, with no
  hypothesis `1 ≤ n`.
* `Stacks.LocalCohomology.UniformityIII.exists_threshold_forall_blowupCohomology`: all four
  clauses of [Stacks, Tag 0GA7] in one statement, for a Noetherian base ring and under no
  further hypothesis.

## References

* [Stacks Project, Tag 01CC](https://stacks.math.columbia.edu/tag/01CC)
* [Stacks Project, Tag 02OS](https://stacks.math.columbia.edu/tag/02OS)
* [Stacks Project, Tag 0GA6](https://stacks.math.columbia.edu/tag/0GA6)
* [Stacks Project, Tag 0GA7](https://stacks.math.columbia.edu/tag/0GA7)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite TopologicalSpace
open AlgebraicGeometry
open Stacks.SheafOfModules.OnSpace (tensorObjTmul tensor_hom_ext sheaf_comp_app_apply
  sheaf_comp3_app_apply_of whiskerRight_tmul leftUnitor_tmul
  tensorObjTmul_app_one_smul_eq_zero tensorObjTmul_eq_zero_of_locally)

universe u

namespace Stacks.LocalCohomology.UniformityIII

attribute [local instance] modulesMonoidal modulesMonoidal'

variable {A : Type u} [CommRing A] (I : Ideal A)

/-! ### The ideal of the `n`-th thickening on an affine open -/

/-- **The ideal cutting out the `n`-th thickening of the exceptional divisor on an affine open**:
the `n`-th power of the ideal generated by the pullback of `I`.

The thickening is a power of an `AlgebraicGeometry.Scheme.IdealSheafData`, and
`AlgebraicGeometry.Scheme.IdealSheafData.ideal_pow` says that taking the ideal on an affine open
commutes with that power on the nose, so this is
`Stacks.LocalCohomology.UniformityIII.ideal_thickeningIdeal_one_affineOpens` raised to the
`n`-th power. -/
theorem ideal_thickeningIdeal_affineOpens (n : ℕ) (V : (blowupScheme I).affineOpens) :
    (thickeningIdeal I n).ideal V = Ideal.map (pullbackCoeffLE I V.1).hom I ^ n := by
  have hpow : ∀ m : ℕ, (thickeningIdeal I m).ideal V =
      ((Scheme.IdealSheafData.ofIdealTop
        (Ideal.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom I)).comap
          (Stacks.Blowup.toSpec I)).ideal V ^ m := fun m =>
    congrFun (Scheme.IdealSheafData.ideal_pow
      ((Scheme.IdealSheafData.ofIdealTop
        (Ideal.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom I)).comap
          (Stacks.Blowup.toSpec I)) m) V
  have hone : Ideal.map (pullbackCoeffLE I V.1).hom I =
      ((Scheme.IdealSheafData.ofIdealTop
        (Ideal.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom I)).comap
          (Stacks.Blowup.toSpec I)).ideal V := by
    rw [← ideal_thickeningIdeal_one_affineOpens I V, hpow 1, pow_one]
  rw [hpow n, hone]

/-- **A section of `𝒪_X` over an affine open killed by `𝒪_X ⟶ 𝒪_{Yₙ}` lies in the `n`-th power
of the pullback of `I`.** This is `ideal_thickeningIdeal_affineOpens` read through
`AlgebraicGeometry.Scheme.IdealSheafData.ker_subschemeι_app`, whose statement is about
`AlgebraicGeometry.Scheme.IdealSheafData.subschemeι` on sections — the same map as
`Stacks.LocalCohomology.UniformityIII.thickeningProj` by definitional unfolding of
`SheafOfModules.unitToPushforwardObjUnit`. -/
theorem mem_pow_of_app_thickeningProj_eq_zero (n : ℕ) (V : (blowupScheme I).affineOpens)
    (c : Γ(blowupScheme I, V.1))
    (hc : (thickeningProj I n).val.app (op V.1) (unitSection I V.1 c) = 0) :
    c ∈ Ideal.map (pullbackCoeffLE I V.1).hom I ^ n := by
  rw [← ideal_thickeningIdeal_affineOpens I n V, ← Scheme.IdealSheafData.ker_subschemeι_app]
  exact hc

/-- The converse of `mem_pow_of_app_thickeningProj_eq_zero`: a section of `𝒪_X` over an affine
open lying in the `n`-th power of the pullback of `I` is killed by `𝒪_X ⟶ 𝒪_{Yₙ}`. -/
theorem app_thickeningProj_eq_zero_of_mem_pow (n : ℕ) (V : (blowupScheme I).affineOpens)
    (c : Γ(blowupScheme I, V.1))
    (hc : c ∈ Ideal.map (pullbackCoeffLE I V.1).hom I ^ n) :
    (thickeningProj I n).val.app (op V.1) (unitSection I V.1 c) = 0 := by
  have h : c ∈ RingHom.ker ((thickeningIdeal I n).subschemeι.app V.1).hom := by
    rw [Scheme.IdealSheafData.ker_subschemeι_app, ideal_thickeningIdeal_affineOpens I n V]
    exact hc
  exact h

/-- **Being killed by `𝒪_X ⟶ 𝒪_{Yₖ}` is inherited by restrictions.** Naturality of
`thickeningProj` and nothing else; it is the step that lets the affine case of the next lemma be
read on an arbitrary open. -/
theorem app_thickeningProj_map_eq_zero (k : ℕ) {U V : (blowupScheme I).Opens} (hVU : V ≤ U)
    (e : Γ(blowupScheme I, U))
    (he : (thickeningProj I k).val.app (op U) (unitSection I U e) = 0) :
    (thickeningProj I k).val.app (op V)
      (unitSection I V ((blowupScheme I).presheaf.map (homOfLE hVU).op e)) = 0 := by
  refine Eq.trans (congrArg (fun z => ((thickeningProj I k).val.app (op V)) z)
    (map_unitSection I hVU e).symm) ?_
  refine Eq.trans (PresheafOfModules.naturality_apply (thickeningProj I k).val
    (homOfLE hVU).op (unitSection I U e)) ?_
  rw [he]
  exact map_zero ((thickeningSheaf I k).val.map (homOfLE hVU).op).hom

/-- **The thickenings multiply, on an affine open**: a product of a section killed by
`𝒪_X ⟶ 𝒪_{Yₙ}` and a section killed by `𝒪_X ⟶ 𝒪_{Yₘ}` is killed by `𝒪_X ⟶ 𝒪_{Y_{n+m}}`.

On an affine open each kernel is a power of one ideal of `Γ(X, V)`, by
`mem_pow_of_app_thickeningProj_eq_zero`, so this is `Ideal.mul_mem_mul` and `pow_add`. -/
theorem app_thickeningProj_mul_eq_zero_affineOpens (n m : ℕ)
    (V : (blowupScheme I).affineOpens) (c d : Γ(blowupScheme I, V.1))
    (hc : (thickeningProj I n).val.app (op V.1) (unitSection I V.1 c) = 0)
    (hd : (thickeningProj I m).val.app (op V.1) (unitSection I V.1 d) = 0) :
    (thickeningProj I (n + m)).val.app (op V.1) (unitSection I V.1 (c * d)) = 0 := by
  refine app_thickeningProj_eq_zero_of_mem_pow I (n + m) V _ ?_
  rw [pow_add]
  exact Ideal.mul_mem_mul (mem_pow_of_app_thickeningProj_eq_zero I n V c hc)
    (mem_pow_of_app_thickeningProj_eq_zero I m V d hd)

/-- **The thickenings multiply.** The affine case
`app_thickeningProj_mul_eq_zero_affineOpens` spread over an arbitrary open: both hypotheses and
the conclusion restrict, the affine opens of a scheme form a basis, and the structure sheaf of
the thickening is a sheaf, so a section vanishing on a cover vanishes. -/
theorem app_thickeningProj_mul_eq_zero (n m : ℕ) (V : (blowupScheme I).Opens)
    (c d : Γ(blowupScheme I, V))
    (hc : (thickeningProj I n).val.app (op V) (unitSection I V c) = 0)
    (hd : (thickeningProj I m).val.app (op V) (unitSection I V d) = 0) :
    (thickeningProj I (n + m)).val.app (op V) (unitSection I V (c * d)) = 0 := by
  refine TopCat.Presheaf.IsSheaf.section_ext (F := (thickeningSheaf I (n + m)).val.presheaf)
    (thickeningSheaf I (n + m)).isSheaf ?_
  intro x hx
  obtain ⟨W, hWaff, hxW, hWV⟩ :=
    TopologicalSpace.Opens.isBasis_iff_nbhd.mp (blowupScheme I).isBasis_affineOpens hx
  refine ⟨W, hWV, hxW, ?_⟩
  refine Eq.trans (PresheafOfModules.naturality_apply (thickeningProj I (n + m)).val
    (homOfLE hWV).op (unitSection I V (c * d))).symm ?_
  refine Eq.trans ?_ (map_zero
    ((thickeningSheaf I (n + m)).val.presheaf.map (homOfLE hWV).op).hom).symm
  refine Eq.trans (congrArg (fun z => ((thickeningProj I (n + m)).val.app (op W)) z)
    ((map_unitSection I hWV (c * d)).trans
      (congrArg (unitSection I W) (map_mul _ c d)))) ?_
  exact app_thickeningProj_mul_eq_zero_affineOpens I n m ⟨W, hWaff⟩ _ _
    (app_thickeningProj_map_eq_zero I n hWV c hc)
    (app_thickeningProj_map_eq_zero I m hWV d hd)

/-! ### The pure-tensor computation -/

section Local

attribute [local instance] ProjectiveSpectrum.isPrime
attribute [local instance_reducible] ProjectiveSpectrum.top
attribute [local implicit_reducible] TopCat.Sheaf sheafCompose AlgebraicGeometry.Proj

open AlgebraicGeometry.ProjectiveSpectrum.Proj (structureSheaf)

/-- **The pure tensor of the first sequence vanishes where the right factor factors twice.** If
the restriction of a section of `𝒪_X(q)` to `V` is `r·s·c` for two scalars whose product is
killed by `𝒪_X ⟶ 𝒪_{Yₙ}`, then the pure tensor of the restricted image of `1` with that
restriction is zero: the product moves across the tensor onto the left factor, where it is the
image of itself.

This is `Stacks.LocalCohomology.UniformityIII.tensorObjTmul_app_one_eq_zero_of_restrict_eq_smul`
with the scalar presented as a product, which is the shape the two halves of the comparison
arrive in — one scalar from the ideal sheaf of the `n`-th thickening, the other from the local
factorisation of `𝒪_X(q+1) ⟶ 𝒪_X(q)`. The scalars are taken at the spelling
`X.ringCatSheaf.obj.obj (op V)` of the ring of sections, which is the one carrying both the ring
structure and the action on `(blowupTwist I q).val.obj (op V)`; the `Γ(X, V)` spelling carries
the ring structure but acts only on `Γ(M, V)`. The two actions agree by `rfl`. -/
theorem tensorObjTmul_app_one_eq_zero_of_restrict_eq_smul_smul (n q : ℕ)
    {U V : Opens (ProjectiveSpectrum.top (Stacks.Blowup.reesGrading I))} (hV : V ≤ U)
    (r s : (blowupScheme I).ringCatSheaf.obj.obj (op V))
    (hrs : (thickeningProj I n).val.app (op V) (r * s) = 0)
    (z : (blowupTwist I q).val.obj (op U)) (c : (blowupTwist I q).val.obj (op V))
    (hc : (((blowupTwist I q).val.map (homOfLE hV).op) z :
        (blowupTwist I q).val.obj (op V)) = r • (s • c)) :
    tensorObjTmul (blowupScheme I).toRingedSpace (thickeningSheaf I n) (blowupTwist I q) (op V)
        (((thickeningSheaf I n).val.map (homOfLE hV).op)
          (((thickeningProj I n).val.app (op U))
            (1 : (blowupScheme I).ringCatSheaf.obj.obj (op U))))
        (((blowupTwist I q).val.map (homOfLE hV).op) z) = 0 :=
  (congrArg₂ (tensorObjTmul (blowupScheme I).toRingedSpace (thickeningSheaf I n)
      (blowupTwist I q) (op V)) (map_app_thickeningProj_one I n hV)
      (hc.trans (mul_smul r s c).symm)).trans
    (tensorObjTmul_app_one_smul_eq_zero (blowupScheme I).toRingedSpace (blowupTwist I q)
      (thickeningProj I n) (op V) (r * s) c hrs)

/-- **Near every point the pure tensor of the first sequence vanishes.** The degree-one standard
opens `D₊(b⁽¹⁾)`, `b ∈ I`, cover the blowup, so at any point there is a `b ∈ I` with `b⁽¹⁾`
invertible there (`Stacks.Blowup.exists_reesDegOne_mem_primeCompl`); near that point the image of
a section of `𝒪_X(q+1)` is `b·` a section of `𝒪_X(q)`
(`Stacks.Blowup.exists_restrict_appTwistShift_eq_smul`). The extra scalar `r` is carried through
by linearity of the map and semilinearity of the restriction, so the section is `r·b·`something
there, and `r·b` is killed by `𝒪_X ⟶ 𝒪_{Y_{n+1}}` by `app_thickeningProj_mul_eq_zero`: `r` is
killed by `𝒪_X ⟶ 𝒪_{Yₙ}` and `b` by `𝒪_X ⟶ 𝒪_Y`. -/
theorem exists_tensorObjTmul_app_one_succ_eq_zero (n q : ℕ) (U : (blowupScheme I).Opens)
    (r : Γ(blowupScheme I, U))
    (hr : (thickeningProj I n).val.app (op U) (unitSection I U r) = 0)
    (c : Γ(blowupTwist I (q + 1), U))
    (x : blowupScheme I) (hx : x ∈ U) :
    ∃ (V : (blowupScheme I).Opens) (hV : V ≤ U), x ∈ V ∧
      tensorObjTmul (blowupScheme I).toRingedSpace (thickeningSheaf I (n + 1))
          (blowupTwist I q) (op V)
        (((thickeningSheaf I (n + 1)).val.map (homOfLE hV).op)
          (((thickeningProj I (n + 1)).val.app (op U))
            (1 : (blowupScheme I).ringCatSheaf.obj.obj (op U))))
        (((blowupTwist I q).val.map (homOfLE hV).op)
          ((ambientTwistMap I q).val.app (op U) (r • c))) = 0 := by
  obtain ⟨b, hb, hbx⟩ := Stacks.Blowup.exists_reesDegOne_mem_primeCompl I x
  obtain ⟨V, hV, hxV, c', hc'⟩ := Stacks.Blowup.exists_restrict_appTwistShift_eq_smul
    I (q : ℤ) U c x hx hb hbx
    (((SheafOfModules.unit (blowupScheme I).ringCatSheaf).val.map
        (homOfLE (le_top : U ≤ ⊤)).op)
      ((Stacks.Blowup.toSpec I).appTop.hom
        ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom b)))
    (fun y => val_appTop_toSpec I b y.1)
  refine ⟨V, hV, hxV, ?_⟩
  have hfac : ((blowupTwist I q).val.map (homOfLE hV).op)
        ((ambientTwistMap I q).val.app (op U) c) =
      ((structureSheaf (Stacks.Blowup.reesGrading I)).obj.map (homOfLE hV).op
        (((SheafOfModules.unit (blowupScheme I).ringCatSheaf).val.map
            (homOfLE (le_top : U ≤ ⊤)).op)
          ((Stacks.Blowup.toSpec I).appTop.hom
            ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom b)))) • c' :=
    Eq.trans (congrArg (fun w : (blowupTwist I q).val.obj (op U) =>
      (((blowupTwist I q).val.map (homOfLE hV).op) w :
        (blowupTwist I q).val.obj (op V)))
      ((Stacks.Blowup.appTwistShift_eq I (q : ℤ) (op U) c).symm)) hc'
  refine tensorObjTmul_app_one_eq_zero_of_restrict_eq_smul_smul I (n + 1) q hV
    ((blowupScheme I).ringCatSheaf.obj.map (homOfLE hV).op
      (r : (blowupScheme I).ringCatSheaf.obj.obj (op U)))
    ((structureSheaf (Stacks.Blowup.reesGrading I)).obj.map (homOfLE hV).op
      (((SheafOfModules.unit (blowupScheme I).ringCatSheaf).val.map
          (homOfLE (le_top : U ≤ ⊤)).op)
        ((Stacks.Blowup.toSpec I).appTop.hom
          ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom b))))
    (app_thickeningProj_mul_eq_zero I n 1 V _ _
      (app_thickeningProj_map_eq_zero I n hV r hr)
      (app_thickeningProj_one_map_restrict_eq_zero I hb hV))
    _ c' ?_
  refine Eq.trans (congrArg (fun w : (blowupTwist I q).val.obj (op U) =>
    (((blowupTwist I q).val.map (homOfLE hV).op) w :
      (blowupTwist I q).val.obj (op V)))
    (((ambientTwistMap I q).val.app (op U)).hom.map_smul
      (r : (blowupScheme I).ringCatSheaf.obj.obj (op U)) c)) ?_
  refine Eq.trans (PresheafOfModules.map_smul (blowupTwist I q).val (homOfLE hV).op
    (r : (blowupScheme I).ringCatSheaf.obj.obj (op U))
    ((ambientTwistMap I q).val.app (op U) c)) ?_
  exact congrArg _ hfac

end Local

/-! ### The containment, and the map -/

/-- The sections of `ℐ_{Yₙ}` are killed by `𝒪_X ⟶ 𝒪_{Yₙ}` after the inclusion into `𝒪_X`. -/
private theorem app_thickeningProj_app_thickeningIdealι_eq_zero (n : ℕ)
    (U : (Opens (blowupScheme I).carrier)ᵒᵖ) (a : (thickeningIdealSheaf I n).val.obj U) :
    (thickeningProj I n).val.app U ((thickeningIdealι I n).val.app U a) = 0 :=
  congrArg (fun ψ : thickeningIdealSheaf I n ⟶ thickeningSheaf I n => ψ.val.app U a)
    (kernel.condition (thickeningProj I n))

/-- A section of the kernel lifted from `M` goes to the same section of `N` as the original. -/
private theorem app_kernel_ι_app_kernelLift {M N P : (blowupScheme I).Modules} (f : N ⟶ P)
    (g : M ⟶ N) (w : g ≫ f = 0) (U : (Opens (blowupScheme I).carrier)ᵒᵖ) (s : M.val.obj U) :
    (kernel.ι f).val.app U ((kernel.lift f g w).val.app U s) = g.val.app U s :=
  congrArg (fun ψ : M ⟶ N => ψ.val.app U s) (kernel.lift_ι f g w)

/-- **The composite `𝒪_X(q+1) → 𝒪_X(q) → 𝒪_{Y_{n+1}}(q)` on a local section** is the pure tensor
of the image of `1` with the image of the section under `ambientTwistMap`. -/
theorem app_ambientTwistMap_comp_thickeningTwistProj (n q : ℕ)
    (U : (Opens (blowupScheme I).carrier)ᵒᵖ) (z : (blowupTwist I (q + 1)).val.obj U) :
    ((ambientTwistMap I q ≫ thickeningTwistProj I (n + 1) q).val.app U).hom z =
      tensorObjTmul (blowupScheme I).toRingedSpace (thickeningSheaf I (n + 1))
        (blowupTwist I q) U
        (((thickeningProj I (n + 1)).val.app U)
          (1 : (blowupScheme I).ringCatSheaf.obj.obj U))
        (((ambientTwistMap I q).val.app U) z) :=
  (sheaf_comp_app_apply (blowupScheme I).toRingedSpace (ambientTwistMap I q)
    (thickeningTwistProj I (n + 1) q) U z).trans
      (app_thickeningTwistProj I (n + 1) q U _)

/-- **The composite `ℐ_{Yₙ} ⊗ 𝒪_X(q+1) → 𝒪_X(q+1) → 𝒪_X(q) → 𝒪_{Y_{n+1}}(q)` is zero**, which
is the containment `ambientTwistMap(ℐⁿ·𝒪_X(q+1)) ⊆ ℐⁿ⁺¹·𝒪_X(q)`.

The source is a sheafified tensor product, so the morphism is determined by its values on local
pure tensors `a ⊗ c` (`Stacks.SheafOfModules.OnSpace.tensor_hom_ext`). On one of those the
composite is `a·c` pushed along `𝒪_X(q+1) → 𝒪_X(q) → 𝒪_{Y_{n+1}}(q)`
(`app_twistedThickeningIdealMap_tmul`), which `app_thickeningTwistProj` presents as the pure
tensor of the image of `1` with `ambientTwistMap(a·c)`; and
`exists_tensorObjTmul_app_one_succ_eq_zero` kills that pure tensor near every point, so the
sheaf axiom kills it. -/
theorem twistedThickeningIdealMap_comp_ambientTwistMap_comp_thickeningTwistProj_eq_zero
    (n q : ℕ) :
    twistedThickeningIdealMap I n (q + 1) ≫ ambientTwistMap I q ≫
        thickeningTwistProj I (n + 1) q = 0 := by
  refine tensor_hom_ext (blowupScheme I).toRingedSpace ?_
  intro U a c
  refine Eq.trans (sheaf_comp_app_apply (blowupScheme I).toRingedSpace
    (twistedThickeningIdealMap I n (q + 1))
    (ambientTwistMap I q ≫ thickeningTwistProj I (n + 1) q) U _) ?_
  refine Eq.trans (congrArg (fun w : (blowupTwist I (q + 1)).val.obj U =>
    ((ambientTwistMap I q ≫ thickeningTwistProj I (n + 1) q).val.app U).hom w)
    (app_twistedThickeningIdealMap_tmul I n (q + 1) U.unop a c)) ?_
  refine Eq.trans (app_ambientTwistMap_comp_thickeningTwistProj I n q U _) ?_
  refine Eq.trans (tensorObjTmul_eq_zero_of_locally (blowupScheme I).toRingedSpace
    (thickeningSheaf I (n + 1)) (blowupTwist I q) U.unop _ _ (fun x hx =>
      exists_tensorObjTmul_app_one_succ_eq_zero I n q U.unop
        (sectionOfUnit I U.unop ((thickeningIdealι I n).val.app U a))
        (app_thickeningProj_app_thickeningIdealι_eq_zero I n U a) c x hx)) ?_
  refine Eq.symm ?_
  show ((0 : (thickeningIdealSheaf I n ⊗ blowupTwist I (q + 1) :
      (blowupScheme I).Modules).val ⟶ (thickeningTwist I (n + 1) q).val).app U).hom _ = 0
  rfl

/-- **The kernel of `𝒪_X(q+1) ⟶ 𝒪_{Yₙ}(q+1)` is killed by the composite
`𝒪_X(q+1) → 𝒪_X(q) → 𝒪_{Y_{n+1}}(q)`.**

`Stacks.LocalCohomology.UniformityIII.isIso_kernelLift_twistedThickeningIdealMap` identifies that
kernel with `ℐ_{Yₙ} ⊗ 𝒪_X(q+1)` — it holds for every `n` and every `q` — so the canonical lift is
an epimorphism and the containment may be cancelled against it, leaving
`twistedThickeningIdealMap_comp_ambientTwistMap_comp_thickeningTwistProj_eq_zero`. -/
theorem kernel_ι_comp_ambientTwistMap_comp_thickeningTwistProj_eq_zero (n q : ℕ) :
    kernel.ι (thickeningTwistProj I n (q + 1)) ≫ ambientTwistMap I q ≫
        thickeningTwistProj I (n + 1) q = 0 := by
  have : IsIso (kernel.lift (thickeningTwistProj I n (q + 1))
      (twistedThickeningIdealMap I n (q + 1))
      (twistedThickeningIdealMap_comp_thickeningTwistProj_eq_zero I n (q + 1))) :=
    isIso_kernelLift_twistedThickeningIdealMap I n (q + 1)
  haveI := @IsIso.epi_of_iso _ _ _ _ _ this
  refine (cancel_epi (kernel.lift (thickeningTwistProj I n (q + 1))
    (twistedThickeningIdealMap I n (q + 1))
    (twistedThickeningIdealMap_comp_thickeningTwistProj_eq_zero I n (q + 1)))).mp ?_
  rw [comp_zero, ← Category.assoc, kernel.lift_ι]
  exact twistedThickeningIdealMap_comp_ambientTwistMap_comp_thickeningTwistProj_eq_zero I n q

/-- **The field `divα` of `Stacks.LocalCohomology.UniformityIII.GeometricInput`**: the first map
`𝒪_{Yₙ}(q+1) ⟶ 𝒪_{Y_{n+1}}(q)` of the first sequence of the proof of [Stacks, Tag 0GA7].

It is `ambientTwistMap I q` passed to the quotients: the canonical surjection
`𝒪_X(q+1) ⟶ 𝒪_{Yₙ}(q+1)` is an epimorphism, and the composite
`𝒪_X(q+1) → 𝒪_X(q) → 𝒪_{Y_{n+1}}(q)` kills its kernel by
`kernel_ι_comp_ambientTwistMap_comp_thickeningTwistProj_eq_zero`, so
`CategoryTheory.Abelian.epiDesc` produces the map. -/
def divα (n q : ℕ) : thickeningTwist I n (q + 1) ⟶ thickeningTwist I (n + 1) q :=
  Abelian.epiDesc (thickeningTwistProj I n (q + 1))
    (ambientTwistMap I q ≫ thickeningTwistProj I (n + 1) q)
    (kernel_ι_comp_ambientTwistMap_comp_thickeningTwistProj_eq_zero I n q)

/-- **The defining square of `divα`**: the square whose verticals are the canonical surjections
onto the thickenings and whose horizontals are `ambientTwistMap I q` and `divα I n q` commutes.
Every property of `divα` below is read off this by cancelling the epimorphism. -/
theorem thickeningTwistProj_comp_divα (n q : ℕ) :
    thickeningTwistProj I n (q + 1) ≫ divα I n q =
      ambientTwistMap I q ≫ thickeningTwistProj I (n + 1) q :=
  Abelian.comp_epiDesc (thickeningTwistProj I n (q + 1))
    (ambientTwistMap I q ≫ thickeningTwistProj I (n + 1) q)
    (kernel_ι_comp_ambientTwistMap_comp_thickeningTwistProj_eq_zero I n q)

/-- **The field `div_comp` of `Stacks.LocalCohomology.UniformityIII.GeometricInput`**: the first
sequence `0 → 𝒪_{Yₙ}(q+1) → 𝒪_{Y_{n+1}}(q) → 𝒪_Y(q) → 0` is a complex.

Precomposing with the epimorphism `𝒪_X(q+1) ⟶ 𝒪_{Yₙ}(q+1)` turns the assertion into
`𝒪_X(q+1) → 𝒪_X(q) → 𝒪_{Y_{n+1}}(q) → 𝒪_Y(q)` being zero, and the last two maps compose to the
canonical `𝒪_X(q) ⟶ 𝒪_Y(q)` by
`Stacks.LocalCohomology.UniformityIII.thickeningTwistProj_comp_thickeningTwistRestrict`, so this
is the complex condition of the *second* sequence,
`ambientTwistMap_comp_thickeningTwistProj_eq_zero`. -/
theorem divα_comp_thickeningTwistRestrict_eq_zero (n q : ℕ) :
    divα I n q ≫ thickeningTwistRestrict I (Nat.le_add_left 1 n) q = 0 := by
  refine (cancel_epi (thickeningTwistProj I n (q + 1))).mp ?_
  rw [comp_zero, ← Category.assoc, thickeningTwistProj_comp_divα, Category.assoc,
    thickeningTwistProj_comp_thickeningTwistRestrict,
    ambientTwistMap_comp_thickeningTwistProj_eq_zero]

/-- **The field `div_sq_left` of `Stacks.LocalCohomology.UniformityIII.GeometricInput`**: the
left-hand square of the diagram in the proof of [Stacks, Tag 0GA7] clause (2). The composite
`I^{q+1} → H⁰(X, 𝒪_{Yₙ}(q+1)) → H⁰(X, 𝒪_{Y_{n+1}}(q))` is the canonical map of `Iᑫ` along the
inclusion `I^{q+1} ⊆ Iᑫ`.

The defining square of `divα` reduces it to the same statement for the ambient sequence,
`Stacks.LocalCohomology.UniformityIII.blowupΓMap_ambientTwistMap_ambientSections`, since
`thickeningSections` is by definition `ambientSections` followed by the canonical surjection. -/
theorem blowupΓMap_divα_thickeningSections (n q : ℕ) (x : (I ^ (q + 1) : Ideal A)) :
    blowupΓMap I (divα I n q) (thickeningSections I n (q + 1) x) =
      thickeningSections I (n + 1) q
        ⟨(x : A), Ideal.pow_le_pow_right (Nat.le_succ q) x.2⟩ := by
  show blowupΓMap I (divα I n q)
    (blowupΓMap I (thickeningTwistProj I n (q + 1)) (ambientSections I (q + 1) x)) = _
  rw [← blowupΓMap_comp, thickeningTwistProj_comp_divα, blowupΓMap_comp,
    blowupΓMap_ambientTwistMap_ambientSections]
  rfl

/-! ### Sections of the kernel, and the generators of the image -/

/-- **A section killed by a morphism of sheaves of modules comes from its kernel.**

`CategoryTheory.SheafOfModules.evaluation` at an open preserves finite limits, so
`CategoryTheory.Limits.PreservesKernel.iso` identifies the sections of the kernel over that open
with the kernel of the map on sections, which `CategoryTheory.ModuleCat.kernelIsoKer` computes as
a submodule. This is `Stacks.ClosedImmersion.exists_idealSheaf_section_of_app_eq_zero` for an
arbitrary morphism, at the spelling `AlgebraicGeometry.Scheme.Modules` of the category. -/
theorem exists_app_kernel_ι_eq {M N : (blowupScheme I).Modules} (g : M ⟶ N)
    (V : (blowupScheme I).Opens) (a : M.val.obj (op V))
    (ha : (g.val.app (op V)) a = 0) :
    ∃ y : (kernel g).val.obj (op V), (kernel.ι g).val.app (op V) y = a := by
  have hmem : a ∈ LinearMap.ker
      ((_root_.SheafOfModules.evaluation.{u} (blowupScheme I).ringCatSheaf (op V)).map g).hom := ha
  refine ⟨(PreservesKernel.iso
    (_root_.SheafOfModules.evaluation.{u} (blowupScheme I).ringCatSheaf (op V)) g).inv
      ((ModuleCat.kernelIsoKer
        ((_root_.SheafOfModules.evaluation.{u} (blowupScheme I).ringCatSheaf (op V)).map g)).inv
          ⟨a, hmem⟩), ?_⟩
  refine (congr($(PreservesKernel.iso_inv_ι
    (_root_.SheafOfModules.evaluation.{u} (blowupScheme I).ringCatSheaf (op V)) g)
      ((ModuleCat.kernelIsoKer
        ((_root_.SheafOfModules.evaluation.{u} (blowupScheme I).ringCatSheaf (op V)).map g)).inv
          ⟨a, hmem⟩))).trans ?_
  exact congr($(ModuleCat.kernelIsoKer_inv_kernel_ι
    ((_root_.SheafOfModules.evaluation.{u} (blowupScheme I).ringCatSheaf (op V)).map g))
      (⟨a, hmem⟩ : LinearMap.ker
        ((_root_.SheafOfModules.evaluation.{u} (blowupScheme I).ringCatSheaf (op V)).map g).hom))

/-- **The composite `ℐ_{Yₙ} ⊗ 𝒪_X(q+1) → 𝒪_X(q+1) → 𝒪_X(q)` on sections over an open**, as an
additive map between the section groups at the spelling `Γ(M, V)`, which is where the scalar
action lives. The spelling is what makes summing scalar multiples possible; see
`Stacks.LocalCohomology.UniformityIII.ambientTwistMapSections`. -/
def twistedDivSections (n q : ℕ) (V : (blowupScheme I).Opens) :
    Γ((thickeningIdealSheaf I n ⊗ blowupTwist I (q + 1) : (blowupScheme I).Modules), V) →+
      Γ(blowupTwist I q, V) :=
  ((twistedThickeningIdealMap I n (q + 1) ≫ ambientTwistMap I q).val.app (op V)).hom.toAddMonoidHom

/-- **The generators of the image**: over an affine open, a section of `𝒪_X(q)` scaled by an
element of the `(n+1)`-st power of the pullback of `I` is in the image of
`ℐ_{Yₙ} ⊗ 𝒪_X(q+1) → 𝒪_X(q)`.

This is the surjectivity half of the ideal-power multiplication, and the only place in the file
where the *decomposition* `ℐⁿ⁺¹ = ℐⁿ · ℐ` is used rather than the containment. On an affine open
the two sides are honest ideals of `Γ(X, V)` and the decomposition is
`CategoryTheory.Submodule.mul_induction_on` after `pow_succ`. On a generator `u·v` with
`u ∈ Mⁿ` and `v ∈ M`: `v·c` is in the image of `𝒪_X(q+1) ⟶ 𝒪_X(q)`
(`exists_app_ambientTwistMap_eq_smul_of_mem_map`), say `v·c = ambientTwistMap(s')`; `u` lifts to
a section `y` of `ℐ_{Yₙ}` (`exists_app_kernel_ι_eq`, using
`app_thickeningProj_eq_zero_of_mem_pow`); and the pure tensor `y ⊗ s'` is carried to
`u·ambientTwistMap(s') = u·v·c`. -/
theorem exists_app_twistedDiv_eq_smul (n q : ℕ) (V : (blowupScheme I).affineOpens)
    (r : Γ(blowupScheme I, V.1))
    (hr : r ∈ Ideal.map (pullbackCoeffLE I V.1).hom I ^ (n + 1))
    (c : Γ(blowupTwist I q, V.1)) :
    ∃ s : Γ((thickeningIdealSheaf I n ⊗ blowupTwist I (q + 1) : (blowupScheme I).Modules), V.1),
      twistedDivSections I n q V.1 s = r • c := by
  rw [pow_succ] at hr
  refine Submodule.mul_induction_on hr ?_ ?_
  · intro u hu v hv
    obtain ⟨s', hs'⟩ := exists_app_ambientTwistMap_eq_smul_of_mem_map I q V.1 v hv c
    obtain ⟨y, hy⟩ := exists_app_kernel_ι_eq I (thickeningProj I n) V.1 (unitSection I V.1 u)
      (app_thickeningProj_eq_zero_of_mem_pow I n V u hu)
    refine ⟨tensorObjTmul (blowupScheme I).toRingedSpace (thickeningIdealSheaf I n)
      (blowupTwist I (q + 1)) (op V.1) y s', ?_⟩
    show ((ambientTwistMap I q).val.app (op V.1))
        (((twistedThickeningIdealMap I n (q + 1)).val.app (op V.1))
          (tensorObjTmul (blowupScheme I).toRingedSpace (thickeningIdealSheaf I n)
            (blowupTwist I (q + 1)) (op V.1) y s')) = (u * v) • c
    rw [app_twistedThickeningIdealMap_tmul I n (q + 1) V.1 y s',
      show sectionOfUnit I V.1 ((thickeningIdealι I n).val.app (op V.1) y) = u from hy]
    refine Eq.trans (((ambientTwistMap I q).val.app (op V.1)).hom.map_smul
      (u : (blowupScheme I).ringCatSheaf.obj.obj (op V.1)) s') ?_
    rw [hs']
    exact smul_smul u v c
  · intro r₁ r₂ h₁ h₂
    obtain ⟨s₁, hs₁⟩ := h₁
    obtain ⟨s₂, hs₂⟩ := h₂
    exact ⟨s₁ + s₂, by rw [map_add, hs₁, hs₂, add_smul]⟩

/-- The complex condition of the first sequence with the first map read as the composite
`ℐ_{Yₙ} ⊗ 𝒪_X(q+1) → 𝒪_X(q+1) → 𝒪_X(q)`; this is
`twistedThickeningIdealMap_comp_ambientTwistMap_comp_thickeningTwistProj_eq_zero` with the
bracketing the short complex below wants. -/
theorem twistedThickeningIdealMap_comp_ambientTwistMap_comp_eq_zero (n q : ℕ) :
    (twistedThickeningIdealMap I n (q + 1) ≫ ambientTwistMap I q) ≫
        thickeningTwistProj I (n + 1) q = 0 := by
  rw [Category.assoc]
  exact twistedThickeningIdealMap_comp_ambientTwistMap_comp_thickeningTwistProj_eq_zero I n q

/-! ### The image is the whole kernel -/

/-- **Every section of the kernel of `𝒪_X(q) ⟶ 𝒪_{Y_{n+1}}(q)` is locally in the image of
`ℐ_{Yₙ} ⊗ 𝒪_X(q+1) → 𝒪_X(q)`.**

The route is the one `Stacks.LocalCohomology.UniformityIII.exists_restrict_eq_app_ambientTwistMap`
takes at `n = 0`: the section is, near any point, the image of a section `z` of
`ℐ_{Y_{n+1}} ⊗ 𝒪_X(q)` (`isIso_kernelLift_twistedThickeningIdealMap`, which holds for every
index), that `z` is on a smaller open a finite sum of pure tensors `a ⊗ c`
(`Stacks.SheafOfModules.TensorUnit.exists_sieve_sum_toTensorSheafSection`), and the open may be
shrunk to an affine one because the covering sieve is closed under restriction. On an affine open
each `a` lies in the `(n+1)`-st power of `Ideal.map ψ_V I`, so each `a·c` — and so the sum — is in
the image, by `exists_app_twistedDiv_eq_smul`. -/
theorem exists_restrict_eq_app_twistedDiv (n q : ℕ) (U : (blowupScheme I).Opens)
    (t : (kernel (thickeningTwistProj I (n + 1) q)).val.obj (op U))
    (x : blowupScheme I) (hxU : x ∈ U) :
    ∃ (V : (blowupScheme I).Opens) (hVU : V ≤ U), x ∈ V ∧
      ∃ s : (thickeningIdealSheaf I n ⊗ blowupTwist I (q + 1) :
          (blowupScheme I).Modules).val.obj (op V),
        (twistedThickeningIdealMap I n (q + 1) ≫ ambientTwistMap I q).val.app (op V) s =
          (blowupTwist I q).val.map (homOfLE hVU).op
            ((kernel.ι (thickeningTwistProj I (n + 1) q)).val.app (op U) t) := by
  classical
  have : IsIso (kernel.lift (thickeningTwistProj I (n + 1) q)
      (twistedThickeningIdealMap I (n + 1) q)
      (twistedThickeningIdealMap_comp_thickeningTwistProj_eq_zero I (n + 1) q)) :=
    isIso_kernelLift_twistedThickeningIdealMap I (n + 1) q
  set z := (inv (kernel.lift (thickeningTwistProj I (n + 1) q)
    (twistedThickeningIdealMap I (n + 1) q)
    (twistedThickeningIdealMap_comp_thickeningTwistProj_eq_zero I (n + 1) q))).val.app (op U) t
    with hzdef
  have hz : (kernel.lift (thickeningTwistProj I (n + 1) q)
      (twistedThickeningIdealMap I (n + 1) q)
      (twistedThickeningIdealMap_comp_thickeningTwistProj_eq_zero I (n + 1) q)).val.app
        (op U) z = t :=
    congrArg
      (fun ψ : kernel (thickeningTwistProj I (n + 1) q) ⟶
          kernel (thickeningTwistProj I (n + 1) q) => ψ.val.app (op U) t)
      (IsIso.inv_hom_id (kernel.lift (thickeningTwistProj I (n + 1) q)
        (twistedThickeningIdealMap I (n + 1) q)
        (twistedThickeningIdealMap_comp_thickeningTwistProj_eq_zero I (n + 1) q)))
  obtain ⟨S, hSmem, hS⟩ := Stacks.SheafOfModules.TensorUnit.exists_sieve_sum_toTensorSheafSection
    (X := (blowupScheme I).toRingedSpace) (F := thickeningIdealSheaf I (n + 1))
    (blowupTwist I q) U z
  obtain ⟨W, k, hSk, hxW⟩ := (Opens.mem_grothendieckTopology _).mp hSmem x hxU
  obtain ⟨V, hVaff, hxV, hVW⟩ :=
    TopologicalSpace.Opens.isBasis_iff_nbhd.mp (blowupScheme I).isBasis_affineOpens hxW
  have hVU : V ≤ U := hVW.trans (leOfHom k)
  obtain ⟨m, a, b, hab⟩ := hS (homOfLE hVW ≫ k) (S.downward_closed hSk _)
  rw [show (homOfLE hVW ≫ k) = homOfLE hVU from by rw [← homOfLE_leOfHom k, homOfLE_comp]]
    at hab
  have hU' : (kernel.ι (thickeningTwistProj I (n + 1) q)).val.app (op U) t =
      (twistedThickeningIdealMap I (n + 1) q).val.app (op U) z := by
    refine Eq.trans (congrArg
      (fun y => (kernel.ι (thickeningTwistProj I (n + 1) q)).val.app (op U) y) hz.symm) ?_
    exact app_kernel_ι_app_kernelLift I _ _ _ _ z
  have hVsum : (blowupTwist I q).val.map (homOfLE hVU).op
      ((kernel.ι (thickeningTwistProj I (n + 1) q)).val.app (op U) t) =
      ∑ j : Fin m,
        sectionOfUnit I V ((thickeningIdealι I (n + 1)).val.app (op V) (a j)) • b j := by
    have hab' : (thickeningIdealSheaf I (n + 1) ⊗ blowupTwist I q :
          (blowupScheme I).Modules).val.map (homOfLE hVU).op z =
        ∑ j : Fin m, tensorObjTmul (blowupScheme I).toRingedSpace
          (thickeningIdealSheaf I (n + 1)) (blowupTwist I q) (op V) (a j) (b j) := hab
    rw [hU', ← PresheafOfModules.naturality_apply, hab', map_sum]
    exact Finset.sum_congr rfl fun j _ =>
      app_twistedThickeningIdealMap_tmul I (n + 1) q V (a j) (b j)
  refine ⟨V, hVU, hxV, ?_⟩
  obtain ⟨s, hs⟩ := exists_eq_sum_of_forall_mem_range (twistedDivSections I n q V)
    (Finset.univ : Finset (Fin m))
    (fun j => sectionOfUnit I V ((thickeningIdealι I (n + 1)).val.app (op V) (a j)) • b j)
    (fun j _ => exists_app_twistedDiv_eq_smul I n q ⟨V, hVaff⟩ _
      (mem_pow_of_app_thickeningProj_eq_zero I (n + 1) ⟨V, hVaff⟩ _
        (app_thickeningProj_app_thickeningIdealι_eq_zero I (n + 1) (op V) (a j))) (b j))
  exact ⟨s, hs.trans hVsum.symm⟩

/-- **The canonical lift `ℐ_{Yₙ} ⊗ 𝒪_X(q+1) ⟶ ker(𝒪_X(q) ⟶ 𝒪_{Y_{n+1}}(q))` is an
epimorphism.** -/
theorem epi_kernelLift_twistedDiv (n q : ℕ) :
    Epi (kernel.lift (thickeningTwistProj I (n + 1) q)
      (twistedThickeningIdealMap I n (q + 1) ≫ ambientTwistMap I q)
      (twistedThickeningIdealMap_comp_ambientTwistMap_comp_eq_zero I n q)) := by
  refine Stacks.SheafOfModules.StalkEpiMono.epi_of_exists_sections _ fun U t x hxU => ?_
  obtain ⟨V, hVU, hxV, s, hs⟩ := exists_restrict_eq_app_twistedDiv I n q U t x hxU
  refine ⟨V, hVU, hxV, s, Stacks.SheafOfModules.injective_app_kernel_ι
    (thickeningTwistProj I (n + 1) q) (op V) ?_⟩
  refine Eq.trans ?_ (PresheafOfModules.naturality_apply
    (kernel.ι (thickeningTwistProj I (n + 1) q)).val (homOfLE hVU).op t).symm
  exact (app_kernel_ι_app_kernelLift I _ _ _ _ s).trans hs

/-- **`ℐ_{Yₙ} ⊗ 𝒪_X(q+1) → 𝒪_X(q) → 𝒪_{Y_{n+1}}(q)` is exact at the middle**, i.e.
`ambientTwistMap I q` carries `ℐⁿ·𝒪_X(q+1)` *onto* `ℐⁿ⁺¹·𝒪_X(q)`.

This is the surjectivity half of the ideal-power multiplication, and the last input the first
sequence of Tag 0GA7 needs. The first map is a monomorphism — `mono_twistedThickeningIdealMap`
and the injectivity of `ambientTwistMap I q` — so its canonical lift to the kernel is one too,
and `epi_kernelLift_twistedDiv` makes that lift an epimorphism; an abelian category is balanced,
so the lift is an isomorphism and `shortExact_of_isIso_kernelLift` applies. -/
theorem exact_twistedDiv (n q : ℕ) :
    (ShortComplex.mk (twistedThickeningIdealMap I n (q + 1) ≫ ambientTwistMap I q)
      (thickeningTwistProj I (n + 1) q)
      (twistedThickeningIdealMap_comp_ambientTwistMap_comp_eq_zero I n q)).Exact := by
  have := mono_twistedThickeningIdealMap I n (q + 1)
  have := (shortExact_ambientTwistMap I q).mono_f
  have : Mono (twistedThickeningIdealMap I n (q + 1) ≫ ambientTwistMap I q) := mono_comp _ _
  have : Mono (kernel.lift (thickeningTwistProj I (n + 1) q)
      (twistedThickeningIdealMap I n (q + 1) ≫ ambientTwistMap I q)
      (twistedThickeningIdealMap_comp_ambientTwistMap_comp_eq_zero I n q)) :=
    mono_of_mono_fac (kernel.lift_ι _ _ _)
  have := epi_kernelLift_twistedDiv I n q
  exact (shortExact_of_isIso_kernelLift
    (twistedThickeningIdealMap I n (q + 1) ≫ ambientTwistMap I q)
    (thickeningTwistProj I (n + 1) q)
    (twistedThickeningIdealMap_comp_ambientTwistMap_comp_eq_zero I n q)
    (isIso_of_mono_of_epi _)).exact

/-! ### Short exactness of the first sequence -/

section ShortExact

open CategoryTheory.Abelian.Pseudoelement

attribute [local instance] CategoryTheory.Abelian.Pseudoelement.objectToSort
attribute [local instance] CategoryTheory.Abelian.Pseudoelement.homToFun

/-- **`𝒪_{Yₘ}(q) ⟶ 𝒪_{Yₙ}(q)` is an epimorphism** for `n ≤ m`, so the second map of the first
sequence of Tag 0GA7 is surjective. The composite `𝒪_X(q) ⟶ 𝒪_{Yₘ}(q) ⟶ 𝒪_{Yₙ}(q)` is the
canonical `𝒪_X(q) ⟶ 𝒪_{Yₙ}(q)`, which is an epimorphism by
`Stacks.LocalCohomology.UniformityIII.epi_thickeningTwistProj`, and a composite being an
epimorphism forces its second factor to be one. -/
theorem epi_thickeningTwistRestrict {n m : ℕ} (h : n ≤ m) (q : ℕ) :
    Epi (thickeningTwistRestrict I h q) := by
  have : Epi (thickeningTwistProj I m q ≫ thickeningTwistRestrict I h q) := by
    rw [thickeningTwistProj_comp_thickeningTwistRestrict]
    exact epi_thickeningTwistProj I n q
  exact epi_of_epi (thickeningTwistProj I m q) (thickeningTwistRestrict I h q)

/-- **The first sequence is exact at its middle term.**

This needs nothing about the first map beyond the square that defines it. A pseudoelement of
`𝒪_{Y_{n+1}}(q)` killed by the restriction to the exceptional divisor lifts to `𝒪_X(q)`, because
`𝒪_X(q) ⟶ 𝒪_{Y_{n+1}}(q)` is an epimorphism; the lift is killed by `𝒪_X(q) ⟶ 𝒪_Y(q)`, because
that map factors through the restriction
(`thickeningTwistProj_comp_thickeningTwistRestrict`); so by the exactness of the *second*
sequence (`Stacks.LocalCohomology.UniformityIII.shortExact_ambientTwistMap`, which holds for
every `q`) it comes from `𝒪_X(q+1)`; and its image in `𝒪_{Yₙ}(q+1)` is the preimage wanted, by
the defining square `thickeningTwistProj_comp_divα`. -/
theorem exact_divα (n q : ℕ) :
    (ShortComplex.mk (divα I n q) (thickeningTwistRestrict I (Nat.le_add_left 1 n) q)
      (divα_comp_thickeningTwistRestrict_eq_zero I n q)).Exact := by
  refine exact_of_pseudo_exact _ (fun b hb => ?_)
  obtain ⟨s, hs⟩ := pseudo_surjective_of_epi (thickeningTwistProj I (n + 1) q) b
  have h1 : (thickeningTwistProj I 1 q) s = 0 := by
    rw [← thickeningTwistProj_comp_thickeningTwistRestrict I (Nat.le_add_left 1 n) q,
      Abelian.Pseudoelement.comp_apply, hs]
    exact hb
  obtain ⟨t, ht⟩ := pseudo_exact_of_exact (shortExact_ambientTwistMap I q).exact s h1
  refine ⟨(thickeningTwistProj I n (q + 1)) t, ?_⟩
  rw [← Abelian.Pseudoelement.comp_apply, thickeningTwistProj_comp_divα,
    Abelian.Pseudoelement.comp_apply, ht, hs]

/-- **The first map of the first sequence is a monomorphism.**

A pseudoelement of `𝒪_{Yₙ}(q+1)` killed by `divα` lifts to `𝒪_X(q+1)`, and the lift's image in
`𝒪_X(q)` is killed by `𝒪_X(q) ⟶ 𝒪_{Y_{n+1}}(q)`; `exact_twistedDiv` makes that image come from
`ℐ_{Yₙ} ⊗ 𝒪_X(q+1)`, and `ambientTwistMap I q` is a monomorphism
(`Stacks.LocalCohomology.UniformityIII.shortExact_ambientTwistMap`), so the lift itself comes
from `ℐ_{Yₙ} ⊗ 𝒪_X(q+1)` — where `twistedThickeningIdealMap_comp_thickeningTwistProj_eq_zero`
kills it. -/
theorem mono_divα (n q : ℕ) : Mono (divα I n q) := by
  have hexact := exact_twistedDiv I n q
  have := (shortExact_ambientTwistMap I q).mono_f
  refine mono_of_zero_of_map_zero _ (fun a ha => ?_)
  obtain ⟨t, ht⟩ := pseudo_surjective_of_epi (thickeningTwistProj I n (q + 1)) a
  have h0 : (thickeningTwistProj I (n + 1) q) ((ambientTwistMap I q) t) = 0 := by
    rw [← Abelian.Pseudoelement.comp_apply, ← thickeningTwistProj_comp_divα,
      Abelian.Pseudoelement.comp_apply, ht, ha]
  obtain ⟨w, hw⟩ := pseudo_exact_of_exact hexact _ h0
  have ht' : (twistedThickeningIdealMap I n (q + 1)) w = t :=
    pseudo_injective_of_mono (ambientTwistMap I q)
      (by rw [← Abelian.Pseudoelement.comp_apply]; exact hw)
  rw [← ht, ← ht', ← Abelian.Pseudoelement.comp_apply,
    twistedThickeningIdealMap_comp_thickeningTwistProj_eq_zero, Abelian.Pseudoelement.zero_apply]

/-- **The field `div_shortExact` of `Stacks.LocalCohomology.UniformityIII.GeometricInput`**:
`0 → 𝒪_{Yₙ}(q+1) → 𝒪_{Y_{n+1}}(q) → 𝒪_Y(q) → 0` is short exact. No hypothesis `1 ≤ n` is
needed. -/
theorem shortExact_divα (n q : ℕ) :
    (ShortComplex.mk (divα I n q) (thickeningTwistRestrict I (Nat.le_add_left 1 n) q)
      (divα_comp_thickeningTwistRestrict_eq_zero I n q)).ShortExact where
  exact := exact_divα I n q
  mono_f := mono_divα I n q
  epi_g := epi_thickeningTwistRestrict I (Nat.le_add_left 1 n) q

end ShortExact

/-! ### The Situation of Tag 0GA6 is inhabited -/

/-- **A witness for `Stacks.LocalCohomology.UniformityIII.GeometricInput`**, for a Noetherian
base ring: the Situation of [Stacks, Tag 0GA6] on the blowup holds.

`Stacks.LocalCohomology.UniformityIII.exists_forall_subsingleton_blowupH_thickeningTwist`
gives `d` and the vanishing above it,
`Stacks.LocalCohomology.UniformityIII.exists_baseThreshold` gives `q₀` and its three defining
properties, `Stacks.LocalCohomology.UniformityIII.shortExact_ambientTwistMap` is the second
sequence, and the first map of the first sequence and its three properties are above. -/
def geometricInput [IsNoetherianRing A] : GeometricInput I where
  d := (exists_forall_subsingleton_blowupH_thickeningTwist I).choose
  q₀ := (exists_baseThreshold I).choose
  divα n q := divα I n q
  div_comp n q := divα_comp_thickeningTwistRestrict_eq_zero I n q
  div_shortExact n q _ := shortExact_divα I n q
  amb_shortExact q := shortExact_ambientTwistMap I q
  div_sq_left n q x := blowupΓMap_divα_thickeningSections I n q x
  base_vanishing i q hi _ hq := (exists_baseThreshold I).choose_spec.1 i q hi hq
  base_surjective q hq := (exists_baseThreshold I).choose_spec.2.1 q hq
  base_ker_le q hq x hx := (exists_baseThreshold I).choose_spec.2.2 q hq x hx
  base_vanishing_gt i q hi :=
    (exists_forall_subsingleton_blowupH_thickeningTwist I).choose_spec 1 i q hi

/-- **Tag 0GA7, clause (1), unconditionally** for a Noetherian base ring: for `n ≥ 1`, `i > 0`
and `q` at least the threshold of `geometricInput`, the cohomology `Hⁱ(X, 𝒪_{Yₙ}(q))` vanishes.
This is `Stacks.LocalCohomology.UniformityIII.subsingleton_thickeningH` at the witness. -/
theorem subsingleton_thickeningH_of_isNoetherian [IsNoetherianRing A] {n i q : ℕ} (hn : 1 ≤ n)
    (hi : 1 ≤ i) (hq : (geometricInput I).q₀ ≤ q) :
    Subsingleton (blowupH I i (thickeningTwist I n q)) :=
  subsingleton_thickeningH I (geometricInput I) hn hi hq

/-- **Tag 0GA7, clause (2), unconditionally** for a Noetherian base ring: the canonical map
`Iᑫ → H⁰(X, 𝒪_{Yₙ}(q))` is surjective with kernel `I^{q+n}`. This is
`Stacks.LocalCohomology.UniformityIII.thickeningSections_surjective_and_ker` at the witness. -/
theorem thickeningSections_surjective_and_ker_of_isNoetherian [IsNoetherianRing A] {n q : ℕ}
    (hn : 1 ≤ n) (hq : (geometricInput I).q₀ ≤ q) :
    Function.Surjective (thickeningSections I n q) ∧
      ∀ x : (I ^ q : Ideal A), thickeningSections I n q x = 0 ↔ (x : A) ∈ I ^ (q + n) :=
  thickeningSections_surjective_and_ker I (geometricInput I) hn hq

/-- **Tag 0GA7, clause (3), unconditionally** for a Noetherian base ring: `Hⁱ(X, 𝒪_X(q))`
vanishes for `i ≥ 1` and `q` at least the threshold. This is
`Stacks.LocalCohomology.UniformityIII.subsingleton_blowupH` at the witness. -/
theorem subsingleton_blowupH_of_isNoetherian [IsNoetherianRing A] {i q : ℕ} (hi : 1 ≤ i)
    (hq : (geometricInput I).q₀ ≤ q) : Subsingleton (blowupH I i (blowupTwist I q)) :=
  subsingleton_blowupH I (geometricInput I) hi hq

/-- **Tag 0GA7, clause (4), unconditionally** for a Noetherian base ring: the canonical map
`Iᑫ → H⁰(X, 𝒪_X(q))` is bijective for `q` at least the threshold. This is
`Stacks.LocalCohomology.UniformityIII.bijective_ambientSections` at the witness. -/
theorem bijective_ambientSections_of_isNoetherian [IsNoetherianRing A] {q : ℕ}
    (hq : (geometricInput I).q₀ ≤ q) : Function.Bijective (ambientSections I q) :=
  bijective_ambientSections I (geometricInput I) hq

/-- **All four clauses of [Stacks, Tag 0GA7] in one statement**, for a Noetherian base ring and
under no further hypothesis: there is a `q₀` such that for `q ≥ q₀`

1. `Hⁱ(X, 𝒪_{Yₙ}(q)) = 0` for `n ≥ 1` and `i ≥ 1`;
2. `H⁰(X, 𝒪_{Yₙ}(q)) = Iᑫ/I^{q+n}` for `n ≥ 1`, as surjectivity of the canonical map together
   with the computation of its kernel;
3. `Hⁱ(X, 𝒪_X(q)) = 0` for `i ≥ 1`; and
4. `H⁰(X, 𝒪_X(q)) = Iᑫ`.

As an existential this forgets which threshold works; the tag, which says that `q(S)` read off
the exceptional divisor works, is
`Stacks.LocalCohomology.UniformityIII.blowupHmod_of_qS_le`. -/
theorem exists_threshold_forall_blowupCohomology [IsNoetherianRing A] :
    ∃ q₀ : ℕ,
      (∀ n i q : ℕ, 1 ≤ n → 1 ≤ i → q₀ ≤ q →
        Subsingleton (blowupH I i (thickeningTwist I n q))) ∧
      (∀ n q : ℕ, 1 ≤ n → q₀ ≤ q →
        Function.Surjective (thickeningSections I n q) ∧
          ∀ x : (I ^ q : Ideal A), thickeningSections I n q x = 0 ↔ (x : A) ∈ I ^ (q + n)) ∧
      (∀ i q : ℕ, 1 ≤ i → q₀ ≤ q → Subsingleton (blowupH I i (blowupTwist I q))) ∧
      (∀ q : ℕ, q₀ ≤ q → Function.Bijective (ambientSections I q)) :=
  ⟨(geometricInput I).q₀,
    fun _ _ _ hn hi hq => subsingleton_thickeningH_of_isNoetherian I hn hi hq,
    fun _ _ hn hq => thickeningSections_surjective_and_ker_of_isNoetherian I hn hq,
    fun _ _ hi hq => subsingleton_blowupH_of_isNoetherian I hi hq,
    fun _ hq => bijective_ambientSections_of_isNoetherian I hq⟩

end Stacks.LocalCohomology.UniformityIII

end
