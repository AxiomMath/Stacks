module

public import StacksFrontier.AlgebraicGeometry.Quot.StableReduction.FamilyCriterion
public import StacksFrontier.AlgebraicGeometry.Quot.StableReduction.Glueing.RationalTailIso

/-!
# Transport of the stable fibre condition along isomorphisms of fibres

Let `ψ : V' ⟶ V` be an isomorphism of schemes lying over an isomorphism of fields
`Spec k' ≅ Spec k`. The fibre conditions defining a stable curve of genus `g` — global functions
equal to the ground field, genus `g ≥ 2`, no rational tail and no rational bridge — hold for `V`
over `k` as soon as they hold for `V'` over `k'`.

Consequently, if `X' ⟶ S'` is the base change of `X ⟶ S` along `j : S' ⟶ S` and `j` induces an
isomorphism of residue fields at `s'` (for instance, `j` is an open immersion), then the fibre of
`X ⟶ S` over `j s'` is a stable curve of genus `g` as soon as the fibre of `X' ⟶ S'` over `s'`
is.

## Main results

* `AlgebraicGeometry.isIso_ΓSpecIso_inv_comp_appTop_of_iso`,
  `AlgebraicGeometry.genus_eq_of_iso` and
  `AlgebraicGeometry.HasGenusTwoNoRationalTailNoRationalBridge.of_iso`: the three fibre
  conditions are invariant under isomorphisms over isomorphisms of fields.
* `AlgebraicGeometry.IsStableFibreOfGenus.of_isPullback`: transport of the fibre condition along
  a base change inducing an isomorphism of residue fields.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

variable {k k' : Type u} [Field k] [Field k'] (φ : CommRingCat.of k ⟶ CommRingCat.of k')
  [IsIso φ] {V V' : Scheme.{u}} (f : V ⟶ Spec (.of k)) (f' : V' ⟶ Spec (.of k'))
  (ψ : V' ⟶ V) [IsIso ψ]

/-- The condition that the global functions of a scheme over a field are the field is invariant
under an isomorphism of schemes lying over an isomorphism of fields. -/
theorem isIso_ΓSpecIso_inv_comp_appTop_of_iso (hw : ψ ≫ f = f' ≫ Spec.map φ)
    (h : IsIso ((Scheme.ΓSpecIso (.of k')).inv ≫ f'.appTop)) :
    IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop) := by
  have key : ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop) ≫ ψ.appTop =
      φ ≫ ((Scheme.ΓSpecIso (.of k')).inv ≫ f'.appTop) := by
    rw [Category.assoc, ← Scheme.Hom.comp_appTop, hw, Scheme.Hom.comp_appTop,
      ← Category.assoc, ← Category.assoc, Scheme.ΓSpecIso_inv_naturality]
  have : IsIso ψ.appTop := inferInstanceAs (IsIso (ψ.app ⊤))
  have : IsIso (((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop) ≫ ψ.appTop) := by
    rw [key]; infer_instance
  exact IsIso.of_isIso_comp_right _ ψ.appTop

/-- The square formed by an isomorphism of schemes over an isomorphism of fields is
cartesian. -/
theorem isPullback_of_iso (hw : ψ ≫ f = f' ≫ Spec.map φ) : IsPullback ψ f' f (Spec.map φ) :=
  IsPullback.of_horiz_isIso ⟨hw⟩

/-- A morphism isomorphic over an isomorphism of fields to `f'` is the composite of `inv ψ`,
`f'` and `Spec.map φ`. -/
private theorem eq_inv_comp_of_iso {C : Type*} [Category C] {A B D E : C} (a : A ⟶ B)
    [IsIso a] (b : B ⟶ D) (c : A ⟶ E) (d : E ⟶ D) (hw : a ≫ b = c ≫ d) : b = inv a ≫ c ≫ d := by
  rw [← hw, IsIso.inv_hom_id_assoc]

/-- The genus is invariant under an isomorphism of schemes lying over an isomorphism of
fields. -/
theorem genus_eq_of_iso (hw : ψ ≫ f = f' ≫ Spec.map φ) [IsProper f'] : genus f = genus f' := by
  have : IsProper f := by rw [eq_inv_comp_of_iso ψ f f' _ hw]; infer_instance
  exact (genus_eq_of_isPullback k k' φ.hom ψ f' f (isPullback_of_iso φ f f' ψ hw)).symm

/-- **The stable fibre condition is invariant under isomorphisms.** If `ψ : V' ⟶ V` is an
isomorphism of schemes lying over an isomorphism of fields `Spec k' ≅ Spec k` and `V'` over `k'`
has genus at least two and neither rational tails nor rational bridges, then so has `V` over
`k`. -/
theorem HasGenusTwoNoRationalTailNoRationalBridge.of_iso (hw : ψ ≫ f = f' ≫ Spec.map φ)
    (h : HasGenusTwoNoRationalTailNoRationalBridge k' f') :
    HasGenusTwoNoRationalTailNoRationalBridge k f := by
  obtain ⟨hg2, htail, hproper, hbridge⟩ := h
  have : IsProper f' := hproper
  have hf := eq_inv_comp_of_iso ψ f f' _ hw
  have : IsProper f := by rw [hf]; infer_instance
  refine ⟨?_, ?_, inferInstanceAs (IsProper f), ?_⟩
  · rwa [genus_eq_of_iso φ f f' ψ hw]
  · exact fun C hC ↦ htail _ ((isRationalTail_comp_isIso_iff f' φ _).mp
      (isRationalTail_map_of_isIso f (f' ≫ Spec.map φ) (inv ψ) hf.symm C hC))
  · exact fun C hC ↦ hbridge _ ((isRationalBridge_comp_iff f' φ _).mp
      (isRationalBridge_map_of_isIso f (f' ≫ Spec.map φ) (inv ψ) C hC))

/-- **Transport of the stable fibre condition along a base change.** Let `X' ⟶ S'` be the base
change of `p : X ⟶ S` along `j : S' ⟶ S`, and let `s' ∈ S'` be a point at which `j` induces an
isomorphism of residue fields. If the fibre of `X' ⟶ S'` over `s'` is a stable curve of genus
`g`, so is the fibre of `p` over `j s'`. -/
theorem IsStableFibreOfGenus.of_isPullback {g : ℕ} {X' X S' S : Scheme.{u}} {fst : X' ⟶ X}
    {p' : X' ⟶ S'} {p : X ⟶ S} {j : S' ⟶ S} (h : IsPullback fst p' p j) (s' : S')
    [IsIso (j.residueFieldMap s')] (hs : IsStableFibreOfGenus g p' s') :
    IsStableFibreOfGenus g p (j s') := by
  have hpb := isPullback_fiberToSpecResidueField_of_isPullback h s'
  have hφ : IsIso (j.residueFieldMap s') := ‹_›
  have hψ := hpb.isIso_fst_of_isIso
  obtain ⟨hΓ, hgt, hgen⟩ := hs
  have hpr : IsProper (p'.fiberToSpecResidueField s') := hgt.2.2.1
  exact ⟨@isIso_ΓSpecIso_inv_comp_appTop_of_iso _ _ _ _ (j.residueFieldMap s') hφ _ _ _ _ _ hψ
      hpb.w hΓ,
    @HasGenusTwoNoRationalTailNoRationalBridge.of_iso _ _ _ _ (j.residueFieldMap s') hφ _ _ _ _ _
      hψ hpb.w hgt,
    (@genus_eq_of_iso _ _ _ _ (j.residueFieldMap s') hφ _ _ _ _ _ hψ hpb.w hpr).trans hgen⟩

end AlgebraicGeometry

end
