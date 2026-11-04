module

public import StacksFrontier.AlgebraicGeometry.PicardScheme.Jacobian.CohomologyClassDivisor
public import StacksFrontier.AlgebraicGeometry.Perfect.CohomologyAndBaseChangeBasis

/-!
# Linear combinations of a basis of sections, and their restrictions to fibres

Let `L₀` be a module on `X_{B₀}` with global sections `e₀, …, e_{n-1}` which, after every base
change to an affine scheme mapping into an open `V ⊆ B₀`, form a basis of the global sections
(`Stacks.RigidifiedPicard.IsSectionBasis`; this is what cohomology and base change provides). For
`v : T ⟶ B₀` and functions `cᵢ` on `T` the section `∑ cᵢ eᵢ` of the pullback of `L₀` to `X_T` is
`Stacks.RigidifiedPicard.abelSection`. Its pullback along any morphism lying over `T' ⟶ T` is
again a linear combination, and when the `cᵢ` have no common zero it vanishes identically on no
fibre of `X_T ⟶ T`.

## Main definitions

* `Stacks.RigidifiedPicard.abelSection`: `∑ cᵢ eᵢ`.
* `Stacks.RigidifiedPicard.IsSectionBasis`: the basis property after affine base change.

## Main results

* `Stacks.RigidifiedPicard.pullbackComp_app_pullbackGlobalSections_abelSection`: pullbacks.
* `Stacks.RigidifiedPicard.pullbackGlobalSections_fiberι_abelSection_ne_zero`: fibres.
* `Stacks.RigidifiedPicard.appTop_fromSpecResidueField_eq_zero_iff`: a function vanishes at a
  point exactly when its restriction to the residue field there is zero.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u

namespace Stacks.RigidifiedPicard

variable {X S : Scheme.{u}} (f : X ⟶ S) {B₀ : Over S} (L₀ : (bc f B₀).Modules) {n : ℕ}
  (e : Fin n → Γ(L₀, ⊤))

/-- **The section `∑ cᵢ eᵢ`** of the pullback of `L₀` to `X_T`, for `v : T ⟶ B₀` and functions
`c₀, …, c_{n-1}` on `T`. -/
noncomputable def abelSection {T : Over S} (v : T ⟶ B₀) (c : Fin n → Γ(T.left, ⊤)) :
    Γ((Scheme.Modules.pullback (bcMap f v)).obj L₀, ⊤) :=
  ∑ i, ((bcProj f T).appTop (c i) : Γ(bc f T, ⊤)) • pullbackGlobalSections (bcMap f v) L₀ (e i)

/-- **The sections `eᵢ` form a basis after every affine base change into `V`.** -/
def IsSectionBasis (V : B₀.left.Opens) : Prop :=
  ∀ {T' Y' : Scheme.{u}} [IsAffine T'] (h : T' ⟶ B₀.left), Set.range h ⊆ V →
    ∀ (p' : Y' ⟶ T') (g' : Y' ⟶ bc f B₀), IsPullback g' p' (bcProj f B₀) h →
      Function.Bijective (fun c : Fin n → Γ(T', ⊤) =>
        ∑ i, (p'.appTop (c i) : Γ(Y', ⊤)) • pullbackGlobalSections g' L₀ (e i))

/-- **Pulling back `∑ cᵢ eᵢ`.** Along `g' : Y' ⟶ X_T` lying over `h' : T' ⟶ T`, the pullback of
`∑ cᵢ eᵢ` is `∑ h'^*cᵢ · g'^*eᵢ`, read on the pullback along the composite. -/
theorem pullbackComp_app_pullbackGlobalSections_abelSection {T : Over S} (v : T ⟶ B₀)
    (c : Fin n → Γ(T.left, ⊤)) {Y' T' : Scheme.{u}} (g' : Y' ⟶ bc f T) (p' : Y' ⟶ T')
    (h' : T' ⟶ T.left) (w : g' ≫ bcProj f T = p' ≫ h') :
    ((Scheme.Modules.pullbackComp g' (bcMap f v)).hom.app L₀).app ⊤
        (pullbackGlobalSections g' _ (abelSection f L₀ e v c)) =
      ∑ i, (p'.appTop (h'.appTop (c i)) : Γ(Y', ⊤)) •
        pullbackGlobalSections (g' ≫ bcMap f v) L₀ (e i) := by
  rw [abelSection, map_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [AlgebraicGeometry.SectionsEqualizer.pullbackGlobalSections_smul,
    Scheme.Modules.Hom.app_smul, AlgebraicGeometry.SectionsEqualizer.pullbackGlobalSections_comp]
  congr 1
  show (g' ≫ bcProj f T).appTop (c i) = (p' ≫ h').appTop (c i)
  rw [w]

end Stacks.RigidifiedPicard

namespace Stacks.RigidifiedPicard

variable {X S : Scheme.{u}} (f : X ⟶ S) {B₀ : Over S} (L₀ : (bc f B₀).Modules) {n : ℕ}
  (e : Fin n → Γ(L₀, ⊤))

/-- A point lies in `basicOpen a` iff the preimage of `basicOpen a` in its residue field
spectrum is nonempty. -/
private theorem mem_basicOpen_iff_exists_mem_preimage {T : Scheme.{u}} (t : T) (a : Γ(T, ⊤)) :
    t ∈ T.basicOpen a ↔ ∃ x, x ∈ (T.fromSpecResidueField t) ⁻¹ᵁ T.basicOpen a := by
  have hpt : Nonempty (Spec (T.residueField t)) := by
    show Nonempty (PrimeSpectrum _); infer_instance
  obtain ⟨x⟩ := hpt
  refine ⟨fun ht => ⟨x, ?_⟩, fun ⟨x, hx⟩ => ?_⟩
  · show T.fromSpecResidueField t x ∈ T.basicOpen a
    rwa [Scheme.fromSpecResidueField_apply]
  · change T.fromSpecResidueField t x ∈ T.basicOpen a at hx
    rwa [Scheme.fromSpecResidueField_apply] at hx

/-- A function vanishing at a point vanishes after restriction to the residue field there. -/
theorem notMem_basicOpen_of_appTop_fromSpecResidueField_eq_zero {T : Scheme.{u}} (t : T)
    (a : Γ(T, ⊤)) (h : (T.fromSpecResidueField t).appTop a = 0) : t ∉ T.basicOpen a := by
  rw [mem_basicOpen_iff_exists_mem_preimage]
  rintro ⟨x, hx⟩
  rw [Scheme.preimage_basicOpen_top, h, Scheme.basicOpen_zero] at hx
  exact hx

/-- **`∑ cᵢ eᵢ` does not vanish identically on any fibre** when the `eᵢ` are a basis after base
change and the `cᵢ` have no common zero. -/
theorem pullbackGlobalSections_fiberι_abelSection_ne_zero {V : B₀.left.Opens}
    (hbasis : IsSectionBasis f L₀ e V) {T : Over S} (v : T ⟶ B₀)
    (hv : Set.range v.left ⊆ V) (c : Fin n → Γ(T.left, ⊤))
    (hc : ∀ t, ∃ i, t ∈ T.left.basicOpen (c i)) (t : T.left) :
    pullbackGlobalSections ((bcProj f T).fiberι t) _ (abelSection f L₀ e v c) ≠ 0 := by
  intro h0
  set ι := (bcProj f T).fiberι t
  set p' := (bcProj f T).fiberToSpecResidueField t
  set j := T.left.fromSpecResidueField t
  have hsq : IsPullback ι p' (bcProj f T) j := IsPullback.of_hasPullback _ _
  have hsq' : IsPullback (ι ≫ bcMap f v) p' (bcProj f B₀) (j ≫ v.left) :=
    hsq.paste_horiz (bcMap_isPullback_proj f v)
  have hrange : Set.range (j ≫ v.left) ⊆ V := by
    rintro _ ⟨x, rfl⟩
    exact hv ⟨_, rfl⟩
  have hinj := (hbasis (j ≫ v.left) hrange p' (ι ≫ bcMap f v) hsq').1
  have hsum := pullbackComp_app_pullbackGlobalSections_abelSection f L₀ e v c ι p' j hsq.w
  rw [h0, map_zero] at hsum
  have hc0 : (fun i => j.appTop (c i)) = 0 := by
    refine hinj (hsum.symm.trans ?_)
    simp
  obtain ⟨i, hi⟩ := hc t
  exact notMem_basicOpen_of_appTop_fromSpecResidueField_eq_zero t (c i) (congrFun hc0 i) hi

end Stacks.RigidifiedPicard

namespace Stacks.RigidifiedPicard

/-- A function restricts to zero on the residue field of a point exactly when it vanishes there. -/
theorem appTop_fromSpecResidueField_eq_zero_iff {T : Scheme.{u}} (t : T) (a : Γ(T, ⊤)) :
    (T.fromSpecResidueField t).appTop a = 0 ↔ t ∉ T.basicOpen a := by
  refine ⟨notMem_basicOpen_of_appTop_fromSpecResidueField_eq_zero t a, fun ht => ?_⟩
  by_contra h0
  apply ht
  have hfield : IsField Γ(Spec (T.residueField t), ⊤) :=
    (Scheme.ΓSpecIso (T.residueField t)).commRingCatIsoToRingEquiv.toMulEquiv.isField
      (Field.toIsField _)
  have hu : IsUnit ((T.fromSpecResidueField t).appTop a) := by
    obtain ⟨b, hb⟩ := hfield.mul_inv_cancel h0
    exact IsUnit.of_mul_eq_one _ hb
  rw [mem_basicOpen_iff_exists_mem_preimage]
  refine ⟨default, ?_⟩
  rw [Scheme.preimage_basicOpen_top, Scheme.basicOpen_of_isUnit _ hu]
  trivial

end Stacks.RigidifiedPicard

end
