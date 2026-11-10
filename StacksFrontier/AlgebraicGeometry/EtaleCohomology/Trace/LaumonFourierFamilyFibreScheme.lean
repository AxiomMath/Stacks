module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LaumonFamilyFibreCohomology
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LaumonFourierLineFamily

/-!
# The fibres of Laumon's Fourier family over a rational point of the `t`-line

Let `V'` be an open of the `t`-line over `k'`, `U' = pr₂⁻¹(V')`, `v` a point of `V'` whose residue
field `κ(v)` is identified with `k'` by `ι : k' → κ(v)` (`κ(v) = k'`), lying over `t = c`, and
`Y` the fibre of `U' → V'` over `v`. Then `Y = X' ×_{k'} κ(v)` for `X' = 𝔸¹_{k'} = Spec k'[x]`
(`Stacks.EtaleCohomology.exists_laumonFourierFibre_fieldExtension`), and `Y → U' → 𝔸²` is
`Y → X'` followed by the section `t = c`, `Spec(φ_c)` for the evaluation
`φ_c : k'[x][t] → k'[x]`, `t ↦ c` (`Stacks.EtaleCohomology.laumonFourierEvalAlgHom`). The
evaluation carries the kernel `a xⁿ + x t` of the Fourier family to `a xⁿ + c x`, so the
Artin–Schreier characters of the family and of the fibre agree along `Y`
(`Stacks.EtaleCohomology.artinSchreierCharacter_laumonFourierFibre_eq`). These are the
geometric inputs of the identification of the fibres of the Fourier family
([Tag 03VH](https://stacks.math.columbia.edu/tag/03VH)).

## Main definitions

* `Stacks.EtaleCohomology.laumonFourierEvalAlgHom`: `φ_c : k'[x][t] → k'[x]`, `t ↦ c`.

## Main results

* `Stacks.EtaleCohomology.laumonFourierEvalAlgHom_laumonFourierKernel`.
* `Stacks.EtaleCohomology.exists_laumonFourierFibre_fieldExtension`.
* `Stacks.EtaleCohomology.artinSchreierCharacter_laumonFourierFibre_eq`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.SmallEtale
open Polynomial
open Stacks.Frobenius

universe u

namespace Stacks.EtaleCohomology

section Eval

variable {k' : Type u} [Field k']

/-- **The evaluation `φ_c : k'[x][t] → k'[x]`, `t ↦ c`**, as a homomorphism of `k'`-algebras. -/
public def laumonFourierEvalAlgHom (c : k') : Polynomial (Polynomial k') →ₐ[k'] Polynomial k' :=
  { eval₂RingHom (RingHom.id (Polynomial k')) (Polynomial.C c) with
    commutes' := fun r => by
      change eval₂ (RingHom.id (Polynomial k')) (Polynomial.C c) (Polynomial.C (Polynomial.C r)) =
        Polynomial.C r
      simp }

/-- `φ_c` is the identity on `k'[x]`. -/
public theorem laumonFourierEvalAlgHom_C (c : k') (q : Polynomial k') :
    laumonFourierEvalAlgHom c (Polynomial.C q) = q :=
  eval₂_C _ _

/-- `φ_c (t) = c`. -/
public theorem laumonFourierEvalAlgHom_X (c : k') :
    laumonFourierEvalAlgHom c Polynomial.X = Polynomial.C c :=
  eval₂_X _ _

/-- **`φ_c (a xⁿ + x t) = a xⁿ + c x`.** -/
public theorem laumonFourierEvalAlgHom_laumonFourierKernel (n : ℕ) (a c : k') :
    laumonFourierEvalAlgHom c (laumonFourierKernel k' n a) =
      Polynomial.C a * Polynomial.X ^ n + Polynomial.C c * Polynomial.X := by
  simp only [laumonFourierKernel, map_add, map_mul, laumonFourierEvalAlgHom_C,
    laumonFourierEvalAlgHom_X]
  ring

end Eval

section Fibre

variable {k' : Type u} [Field k'] {B : BigEtaleSite.{u}}
  {hL : schemeSizeBelow B.cutoff (Spec (.of (Polynomial k')))} {V' : B.Scheme}
  (jV' : V' ⟶ Stacks.ArtinSchreier.specObject (Polynomial k') B hL) (v : V'.1)

/-- **`φ_v = map ι ∘ φ_c`** when `t(v) = ι(c)`, `ι : k' → κ(v)`. -/
public theorem laumonFibreRingHom_eq_comp_laumonFourierEvalAlgHom (c : k')
    (hXc : laumonPointRingHom jV' v Polynomial.X = laumonPointRingHom jV' v (Polynomial.C c)) :
    laumonFibreRingHom jV' v =
      (mapRingHom ((laumonPointRingHom jV' v).comp Polynomial.C)).comp
        (laumonFourierEvalAlgHom c).toRingHom := by
  refine Polynomial.ringHom_ext (fun q => ?_) ?_
  · have h := RingHom.congr_fun (laumonFibreRingHom_comp_C jV' v) q
    simp only [RingHom.comp_apply] at h
    rw [h, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      laumonFourierEvalAlgHom_C]
  · rw [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, laumonFourierEvalAlgHom_X,
      coe_mapRingHom, Polynomial.map_C, RingHom.comp_apply, ← hXc]
    simp [laumonFibreRingHom]

variable {hS : schemeSizeBelow B.cutoff (Spec (.of (Polynomial (Polynomial k'))))} {U' : B.Scheme}
  (jU : U' ⟶ Stacks.ArtinSchreier.specObject (Polynomial (Polynomial k')) B hS) (g' : U' ⟶ V')

/-- **The fibre of the Fourier family over a point `v` with `κ(v) = k'` over `t = c` is
`X' ×_{k'} κ(v)`**, `X' = Spec k'[x]`: an isomorphism `α` onto the base change, over `κ(v)`, with
`Y → U' → 𝔸²` equal to `Y → X'` followed by the section `Spec(φ_c)` of `t = c`. -/
public theorem exists_laumonFourierFibre_fieldExtension [Finite (V'.1.residueField v)] (c : k')
    (hXc : laumonPointRingHom jV' v Polynomial.X = laumonPointRingHom jV' v (Polynomial.C c))
    (hX' : schemeSizeBelow B.cutoff (Spec (.of (Polynomial k'))))
    (hU : IsPullback (B.inclusion.map jU) (B.inclusion.map g')
      (B.inclusion.map (laumonFamilyProjection k' B hS hL)) (B.inclusion.map jV'))
    {Y : B.Scheme} (i : Y ⟶ U') (fY : Y.1 ⟶ Spec (.of (V'.1.residueField v)))
    (hY : IsPullback (B.inclusion.map i) fY (B.inclusion.map g') (V'.1.fromSpecResidueField v)) :
    letI := ((laumonPointRingHom jV' v).comp Polynomial.C).toAlgebra
    haveI : Module.Finite k' (V'.1.residueField v) := Module.Finite.of_finite
    ∃ α : Y ⟶ fieldExtensionScheme B (Stacks.ArtinSchreier.specObject (Polynomial k') B hX')
        (Spec.map (CommRingCat.ofHom (algebraMap k' (Polynomial k')))) (V'.1.residueField v),
      IsIso (B.inclusion.map α) ∧ ConnectedSpace Y.1 ∧
      B.inclusion.map α ≫ pullback.snd _ (specAlgebraMap k' (V'.1.residueField v)) = fY ∧
      B.inclusion.map i ≫ B.inclusion.map jU =
        (B.inclusion.map α ≫ pullback.fst _ (specAlgebraMap k' (V'.1.residueField v))) ≫
          Spec.map (CommRingCat.ofHom (laumonFourierEvalAlgHom c).toRingHom) := by
  let := ((laumonPointRingHom jV' v).comp Polynomial.C).toAlgebra
  have : Module.Finite k' (V'.1.residueField v) := Module.Finite.of_finite
  obtain ⟨β, hβC, hβφ⟩ := exists_laumonFamilyFibre_iso jV' v jU g' hU i fY hY
  have hP : IsPullback
      (Spec.map (CommRingCat.ofHom (mapRingHom (algebraMap k' (V'.1.residueField v)))))
      (Spec.map (CommRingCat.ofHom
        (Polynomial.C : V'.1.residueField v →+* Polynomial (V'.1.residueField v))))
      (Spec.map (CommRingCat.ofHom (algebraMap k' (Polynomial k'))))
      (specAlgebraMap k' (V'.1.residueField v)) :=
    (isPullback_SpecMap_of_isPushout _ _ _ _
      (isPushout_C_mapRingHom k' (V'.1.residueField v))).flip
  let α : Y ⟶ fieldExtensionScheme B (Stacks.ArtinSchreier.specObject (Polynomial k') B hX')
      (Spec.map (CommRingCat.ofHom (algebraMap k' (Polynomial k')))) (V'.1.residueField v) :=
    ObjectProperty.homMk (β.hom ≫ hP.isoPullback.hom)
  refine ⟨α, ?_, ?_, ?_, ?_⟩
  · change IsIso (β.hom ≫ hP.isoPullback.hom)
    infer_instance
  · have hc : ConnectedSpace (Spec (.of (Polynomial (V'.1.residueField v)))) := inferInstance
    exact @Function.Surjective.connectedSpace _ _ _ hc _ _ (Scheme.homeoOfIso β.symm).surjective
      (Scheme.homeoOfIso β.symm).continuous
  · change (β.hom ≫ hP.isoPullback.hom) ≫ _ = fY
    rw [Category.assoc, IsPullback.isoPullback_hom_snd, hβC]
  · change _ = ((β.hom ≫ hP.isoPullback.hom) ≫ _) ≫ _
    rw [Category.assoc, Category.assoc, IsPullback.isoPullback_hom_fst_assoc, ← Spec.map_comp,
      ← CommRingCat.ofHom_comp]
    refine hβφ.trans ?_
    congr 3
    exact laumonFibreRingHom_eq_comp_laumonFourierEvalAlgHom jV' v c hXc

end Fibre

end Stacks.EtaleCohomology

end
