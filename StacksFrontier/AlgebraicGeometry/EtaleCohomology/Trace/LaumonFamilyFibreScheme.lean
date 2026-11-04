module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LaumonOriginFibreScheme
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LaumonFamilyStalkPurity

/-!
# The fibres of Laumon's family over a point of an open of the `t`-line

For an open `jV' : V' ⟶ 𝔸¹_{k'}` of the `t`-line, its preimage `U'` in
`𝔸² = Spec k'[x][t]` under `pr₂` and a fibre `Y` of `U' → V'` over a point `v` of `V'`
([Tag 03VH](https://stacks.math.columbia.edu/tag/03VH)), the fibre `Y` is `𝔸¹_{κ(v)}`: there is an
isomorphism `β : Y ≅ Spec κ(v)[x]` over `κ(v)` under which `Y → U' → 𝔸²` is the spectrum of
`φ_v : k'[x][t] → κ(v)[x]`, `x ↦ x`, `t ↦ s = t(v)`
(`Stacks.EtaleCohomology.exists_laumonFamilyFibre_iso`).

## Main definitions

* `Stacks.EtaleCohomology.laumonFibreRingHom`: the ring map `φ_v`.

## Main results

* `Stacks.EtaleCohomology.fromSpecResidueField_comp_eq_specMap_Γevaluation`,
  `Stacks.EtaleCohomology.fromSpecResidueField_comp_map_laumonPointRingHom`.
* `Stacks.EtaleCohomology.laumonFibreRingHom_laumonKernel`: `φ_v(t (xⁿ⁰ + c x)) = s xⁿ⁰ + c s x`.
* `Stacks.EtaleCohomology.exists_laumonFamilyFibre_iso`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Polynomial

universe u

namespace Stacks.EtaleCohomology

/-- **A morphism to an affine scheme at a point**: `Spec κ(x) → X → Spec R` is the spectrum of
`R → Γ(X) → κ(x)`. -/
public theorem fromSpecResidueField_comp_eq_specMap_Γevaluation {X : Scheme.{u}} (x : X)
    {R : CommRingCat.{u}} (f : X ⟶ Spec R) :
    X.fromSpecResidueField x ≫ f =
      Spec.map ((Scheme.ΓSpecIso R).inv ≫ f.appTop ≫ X.Γevaluation x) := by
  calc _ = X.fromSpecResidueField x ≫ f ≫ (Spec R).toSpecΓ ≫
        Spec.map (Scheme.ΓSpecIso R).inv := by rw [toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]
    _ = (X.fromSpecResidueField x ≫ X.toSpecΓ) ≫ Spec.map f.appTop ≫
        Spec.map (Scheme.ΓSpecIso R).inv := by
        rw [← Category.assoc f, Scheme.toSpecΓ_naturality]
        simp only [Category.assoc]
    _ = _ := by
        rw [Scheme.fromSpecResidueField_toSpecΓ, Spec.map_comp, Spec.map_comp]
        simp only [Category.assoc]

variable {k' : Type u} [Field k'] {B : BigEtaleSite.{u}}
  {hL : schemeSizeBelow B.cutoff (Spec (.of (Polynomial k')))} {V' : B.Scheme}
  (jV' : V' ⟶ Stacks.ArtinSchreier.specObject (Polynomial k') B hL) (v : V'.1)

/-- **Evaluation at a point of an open of the `t`-line**: `Spec κ(v) → V' → Spec k'[t]` is the
spectrum of `k'[t] → κ(v)` (`Stacks.EtaleCohomology.laumonPointRingHom`). -/
public theorem fromSpecResidueField_comp_map_laumonPointRingHom :
    V'.1.fromSpecResidueField v ≫ B.inclusion.map jV' =
      Spec.map (CommRingCat.ofHom (laumonPointRingHom jV' v)) := by
  rw [fromSpecResidueField_comp_eq_specMap_Γevaluation]
  rfl

/-- **The ring map of the fibre over `v`**: `φ_v : k'[x][t] → κ(v)[x]`, the identity on `x` (the
inner variable) and `t ↦ s = t(v)` (the outer variable). -/
public def laumonFibreRingHom :
    Polynomial (Polynomial k') →+* Polynomial (V'.1.residueField v) :=
  eval₂RingHom (mapRingHom ((laumonPointRingHom jV' v).comp C))
    (C (laumonPointRingHom jV' v X))

/-- **`φ_v` on `k'[x]`**: its restriction along `C : k'[x] → k'[x][t]` maps the coefficients along
`k' → k'[t] → κ(v)`. -/
public theorem laumonFibreRingHom_comp_C :
    (laumonFibreRingHom jV' v).comp (C : Polynomial k' →+* Polynomial (Polynomial k')) =
      mapRingHom ((laumonPointRingHom jV' v).comp C) := by
  refine RingHom.ext fun a => ?_
  simp [laumonFibreRingHom]

/-- **`φ_v` on `k'[t]`**: its restriction along `k'[t] → k'[x][t]` is `k'[t] → κ(v)` followed by
the constants `κ(v) → κ(v)[x]`. -/
public theorem laumonFibreRingHom_comp_mapRingHom_C :
    (laumonFibreRingHom jV' v).comp (mapRingHom (C : k' →+* Polynomial k')) =
      (C : V'.1.residueField v →+* Polynomial (V'.1.residueField v)).comp
        (laumonPointRingHom jV' v) := by
  refine Polynomial.ringHom_ext (fun a => ?_) ?_
  · simp [laumonFibreRingHom]
  · simp [laumonFibreRingHom]

/-- **`φ_v(t (xⁿ⁰ + c x)) = s xⁿ⁰ + (c s) x`**, `s = t(v)`. -/
public theorem laumonFibreRingHom_laumonKernel (n₀ : ℕ) (c : k') :
    laumonFibreRingHom jV' v (laumonKernel k' n₀ c) =
      C (laumonPointRingHom jV' v Polynomial.X) *
          (Polynomial.X : Polynomial (V'.1.residueField v)) ^ n₀ +
        C (laumonPointRingHom jV' v (C c) * laumonPointRingHom jV' v Polynomial.X) * Polynomial.X :=
  laumonKernel_eval k' ((laumonPointRingHom jV' v).comp C) n₀ c _

variable {hS : schemeSizeBelow B.cutoff (Spec (.of (Polynomial (Polynomial k'))))} {U' : B.Scheme}
  (jU : U' ⟶ Stacks.ArtinSchreier.specObject (Polynomial (Polynomial k')) B hS) (g' : U' ⟶ V')

/-- **The fibre of Laumon's family over `v` is `𝔸¹_{κ(v)}`**: for `U' = pr₂⁻¹(V')` and a fibre
`Y` of `U' → V'` over `v`, there is an isomorphism `β : Y ≅ Spec κ(v)[x]` over `κ(v)` with
`Y → U' → 𝔸² = Spec(φ_v) ∘ β`. -/
public theorem exists_laumonFamilyFibre_iso
    (hU : IsPullback (B.inclusion.map jU) (B.inclusion.map g')
      (B.inclusion.map (laumonFamilyProjection k' B hS hL)) (B.inclusion.map jV'))
    {Y : B.Scheme} (i : Y ⟶ U') (fY : Y.1 ⟶ Spec (.of (V'.1.residueField v)))
    (hY : IsPullback (B.inclusion.map i) fY (B.inclusion.map g') (V'.1.fromSpecResidueField v)) :
    ∃ β : Y.1 ≅ Spec (.of (Polynomial (V'.1.residueField v))),
      β.hom ≫ Spec.map (CommRingCat.ofHom
        (C : V'.1.residueField v →+* Polynomial (V'.1.residueField v))) = fY ∧
      B.inclusion.map i ≫ B.inclusion.map jU =
        β.hom ≫ Spec.map (CommRingCat.ofHom (laumonFibreRingHom jV' v)) := by
  let iκ : Algebra k' (V'.1.residueField v) := ((laumonPointRingHom jV' v).comp C).toAlgebra
  have P := isPullback_SpecMap_of_isPushout _ _ _ _ (isPushout_C_mapRingHom_C k')
  have S1 := hY.paste_horiz hU
  have S2 := S1.paste_horiz P
  have hb : (V'.1.fromSpecResidueField v ≫ B.inclusion.map jV') ≫
      Spec.map (CommRingCat.ofHom (C : k' →+* Polynomial k')) =
      Spec.map (CommRingCat.ofHom (algebraMap k' (V'.1.residueField v))) := by
    rw [fromSpecResidueField_comp_map_laumonPointRingHom, ← Spec.map_comp]
    rfl
  rw [hb] at S2
  have Q := (isPullback_SpecMap_of_isPushout _ _ _ _
    (isPushout_C_mapRingHom k' (V'.1.residueField v))).flip
  let β := S2.isoIsPullback _ _ Q
  have hβ₁ : β.hom ≫ Spec.map (CommRingCat.ofHom (mapRingHom (algebraMap k' _))) =
      (B.inclusion.map i ≫ B.inclusion.map jU) ≫ laumonFamilyPr₁ k' :=
    S2.isoIsPullback_hom_fst _ _ Q
  have hβ₂ : β.hom ≫ Spec.map (CommRingCat.ofHom
      (C : V'.1.residueField v →+* Polynomial (V'.1.residueField v))) = fY :=
    S2.isoIsPullback_hom_snd _ _ Q
  refine ⟨β, hβ₂, P.hom_ext ?_ ?_⟩
  · rw [hβ₁.symm, Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
      laumonFibreRingHom_comp_C]
  · have hw := S1.w
    rw [Category.assoc] at hw
    have h1 := fromSpecResidueField_comp_map_laumonPointRingHom jV' v
    show (B.inclusion.map i ≫ B.inclusion.map jU) ≫
        B.inclusion.map (laumonFamilyProjection k' B hS hL) = _
    rw [Category.assoc, hw, h1, ← hβ₂, Category.assoc, ← Spec.map_comp, Category.assoc,
      ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
    congr 3
    exact (laumonFibreRingHom_comp_mapRingHom_C jV' v).symm

end Stacks.EtaleCohomology

end
