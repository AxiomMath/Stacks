module

public import Mathlib.AlgebraicGeometry.Fiber
public import StacksFrontier.AlgebraicGeometry.Curves.GenusCurve.SeparableDegreeFibres

/-!
# The genus of a field-valued fibre of a family whose fibres all have genus `r`

Let `p : X ⟶ S` be proper, and assume that every scheme-theoretic fibre
`p.fiberToSpecResidueField s` has genus `r`. Then for every field `K` and every morphism
`Spec K ⟶ S`, the base change `X_K ⟶ Spec K` has genus `r` as well: if `t` is the point of
`Spec K`, the fibre of `X_K ⟶ Spec K` at `t` is both the base change of `X_K` along
`Spec κ(t) ⟶ Spec K` and the base change of the fibre of `p` at the image of `t` along
`Spec κ(t) ⟶ Spec κ(s)`, and the genus is invariant under extension of the ground field
(`AlgebraicGeometry.genus_eq_of_isPullback`).

## Main results

* `Stacks.AlgebraicGeometry.NodalFamilyCohomology.genus_eq_of_isPullback_of_forall_genus`:
  every field-valued base change of such a family has genus `r`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.AlgebraicGeometry.NodalFamilyCohomology

/-- **The genus of a field-valued base change of a family of genus `r`.** Let `p : X ⟶ S` be
proper with every fibre `p.fiberToSpecResidueField s` of genus `r`, and let `Y ⟶ Spec K` be the
base change of `p` along a morphism `Spec K ⟶ S` from the spectrum of a field. Then `Y ⟶ Spec K`
has genus `r`. -/
theorem genus_eq_of_isPullback_of_forall_genus {K : Type u} [Field K] {X Y S : Scheme.{u}}
    {g' : Y ⟶ X} {p' : Y ⟶ Spec (.of K)} {p : X ⟶ S} {g : Spec (.of K) ⟶ S}
    (h : IsPullback g' p' p g) [IsProper p] (r : ℕ)
    (hr : ∀ s : S, genus (p.fiberToSpecResidueField s) = r) : genus p' = r := by
  have : IsProper p' := MorphismProperty.of_isPullback h inferInstance
  obtain ⟨t⟩ : Nonempty (Spec (.of K)) := inferInstance
  have hps : IsProper (p.fiberToSpecResidueField (g t)) :=
    MorphismProperty.of_isPullback (IsPullback.of_hasPullback p _) inferInstance
  have h1 : genus (p'.fiberToSpecResidueField t) = genus (p.fiberToSpecResidueField (g t)) :=
    genus_eq_of_isPullback _ _ (g.residueFieldMap t).hom _ _ _
      (isPullback_fiberToSpecResidueField_of_isPullback h t)
  set φ := Spec.preimage ((Spec (.of K)).fromSpecResidueField t)
  have hφ : Spec.map (CommRingCat.ofHom φ.hom) = (Spec (.of K)).fromSpecResidueField t :=
    Spec.map_preimage _
  have h2 : genus (p'.fiberToSpecResidueField t) = genus p' :=
    genus_eq_of_isPullback K _ φ.hom (p'.fiberι t) _ p'
      (hφ ▸ IsPullback.of_hasPullback p' ((Spec (.of K)).fromSpecResidueField t))
  rw [← h2, h1, hr]

end Stacks.AlgebraicGeometry.NodalFamilyCohomology

end
