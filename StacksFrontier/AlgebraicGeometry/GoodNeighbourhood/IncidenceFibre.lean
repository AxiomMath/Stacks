module

public import StacksFrontier.AlgebraicGeometry.GoodNeighbourhood.FlatTower
public import StacksFrontier.AlgebraicGeometry.Descent.EffectiveEpi.QuasicoherentSectionsEqualizer
public import Mathlib.AlgebraicGeometry.AffineSpace

/-!
# The incidence family `V(vⱼ - tⱼ w₀) ⊆ X̄ × 𝔸^c` and its fibre over the origin

Let `p : X ⟶ Spec k`, `L` an invertible module on `X` and `v₁, …, v_c, w₀` global sections. On
`P = X ×_k 𝔸^c_k`, with projections `pr₁`, `pr₂` and coordinates `t₁, …, t_c` of `𝔸^c_k`, the
sections `Gⱼ = pr₁^* vⱼ - tⱼ · pr₁^* w₀` of `pr₁^* L` cut out the incidence family of
SGA 4, Exposé XI, Proposition 3.3. Its fibre over the origin `0 ∈ 𝔸^c_k` is `X` itself, embedded
by `x ↦ (x, 0)`, and there `Gⱼ` restricts to `vⱼ`, since `tⱼ` vanishes at the origin. So the
partial intersections of the family restrict to the partial intersections `V(v₁, …, v_m)` of `X`.

The origin is a `k`-rational point, so `Spec k ⟶ 𝔸^c_k` is the inclusion of the residue field of
the origin up to an isomorphism `Spec k ≅ Spec κ(0)`; this presents `X` as the scheme-theoretic
fibre in the form the fibrewise criteria (`AlgebraicGeometry.GoodNeighbourhood.FlatTower`) use.

## Main definitions

* `AlgebraicGeometry.GoodNeighbourhood.incidenceSection`: the section `Gⱼ`.
* `AlgebraicGeometry.GoodNeighbourhood.originSection`: `x ↦ (x, 0)`, from `X` to `X ×_k 𝔸^c_k`.

## Main results

* `AlgebraicGeometry.GoodNeighbourhood.exists_iso_fromSpecResidueField_of_comp_eq_id`: a section
  of a scheme over `k` is the inclusion of the residue field of its point, up to isomorphism.
* `AlgebraicGeometry.GoodNeighbourhood.isPullback_originSection`.
* `AlgebraicGeometry.GoodNeighbourhood.comap_partialIdeal_incidenceSection_originSection`.

## References

* SGA 4, Tome 3, Exposé XI, Proposition 3.3.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.GoodNeighbourhood

attribute [local instance] Stacks.ChernCap42.isInvertible_sheafObj_modulePullback

/-- **A section over a field is the inclusion of the residue field of its point.** If
`o₀ : Spec k ⟶ T` is a section of `τ : T ⟶ Spec k`, then `o₀` is `Spec k ≅ Spec κ(s)` followed by
`Spec κ(s) ⟶ T` for the image point `s`: the embedding `κ(s) ⟶ k` defining `o₀` has the
residue map of `τ` as a right inverse. -/
theorem exists_iso_fromSpecResidueField_of_comp_eq_id (k : Type u) [Field k] {T : Scheme.{u}}
    (τ : T ⟶ Spec (.of k)) (o₀ : Spec (.of k) ⟶ T) (h : o₀ ≫ τ = 𝟙 _) :
    ∃ (s : T) (α : Spec (.of k) ≅ Spec (T.residueField s)),
      α.hom ≫ T.fromSpecResidueField s = o₀ := by
  set e := Scheme.SpecToEquivOfField k T o₀
  have ho : Spec.map e.2 ≫ T.fromSpecResidueField e.1 = o₀ :=
    (Scheme.SpecToEquivOfField k T).symm_apply_apply o₀
  let c : CommRingCat.of k ⟶ T.residueField e.1 := Spec.preimage (T.fromSpecResidueField e.1 ≫ τ)
  have hc : c ≫ e.2 = 𝟙 _ := by
    apply Spec.map_injective
    rw [Spec.map_comp, Spec.map_preimage, ← Category.assoc, ho, h, Spec.map_id]
  have hc' : e.2 ≫ c = 𝟙 _ := by
    ext a
    apply e.2.hom.injective
    simpa using congrArg (fun φ => φ.hom (e.2.hom a)) hc
  have : IsIso e.2 := ⟨⟨c, hc', hc⟩⟩
  exact ⟨e.1, asIso (Spec.map e.2), ho⟩

/-- **Changing the base of a smooth closed subscheme by an isomorphism.** -/
theorem SubschemeSmoothAt.comp_isIso {Y S S' : Scheme.{u}} (q : Y ⟶ S) (α : S ⟶ S') [IsIso α]
    {I : Y.IdealSheafData} {n : ℕ} {z : Y} (h : SubschemeSmoothAt q I n z) :
    SubschemeSmoothAt (q ≫ α) I n z := by
  obtain ⟨y, hy, U, hyU, hsm⟩ := h
  refine ⟨y, hy, U, hyU, ?_⟩
  simpa only [Category.assoc, add_zero] using
    (inferInstance : SmoothOfRelativeDimension (n + 0) ((U.ι ≫ I.subschemeι ≫ q) ≫ α))

variable {k : Type u} [Field k] {X : Scheme.{u}} (p : X ⟶ Spec (.of k)) (c : ℕ)

/-- The origin `0` of `𝔸^c_k`, as a `k`-point. -/
noncomputable abbrev origin : Spec (.of k) ⟶ 𝔸(ULift.{u} (Fin c); Spec (.of k)) :=
  AffineSpace.homOfVector (𝟙 _) 0

/-- **The fibre of `X ×_k 𝔸^c_k` over the origin**: `x ↦ (x, 0)`. -/
noncomputable def originSection :
    X ⟶ pullback p (𝔸(ULift.{u} (Fin c); Spec (.of k)) ↘ Spec (.of k)) :=
  pullback.lift (𝟙 X) (p ≫ origin c) (by simp)

/-- The first projection of `originSection p c` is the identity of `X`. -/
@[reassoc (attr := simp)]
theorem originSection_fst : originSection p c ≫ pullback.fst _ _ = 𝟙 X :=
  pullback.lift_fst _ _ _

/-- The second projection of `originSection p c` is `p` followed by the origin of `𝔸^c_k`. -/
@[reassoc (attr := simp)]
theorem originSection_snd : originSection p c ≫ pullback.snd _ _ = p ≫ origin c :=
  pullback.lift_snd _ _ _

/-- **`X` is the fibre of `X ×_k 𝔸^c_k ⟶ 𝔸^c_k` over the origin.** -/
theorem isPullback_originSection :
    IsPullback (originSection p c) p
      (pullback.snd p (𝔸(ULift.{u} (Fin c); Spec (.of k)) ↘ Spec (.of k))) (origin c) := by
  refine IsPullback.of_right (h₁₂ := pullback.fst _ _)
    (h₂₂ := 𝔸(ULift.{u} (Fin c); Spec (.of k)) ↘ Spec (.of k)) ?_ (originSection_snd p c)
    (IsPullback.of_hasPullback _ _)
  rw [originSection_fst, AffineSpace.homOfVector_over]
  exact IsPullback.of_horiz_isIso ⟨by simp⟩

variable {c} (L : X.Modules) [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]

/-- **The equations of the incidence family**: `Gⱼ = pr₁^* vⱼ - tⱼ · pr₁^* w₀` on
`X ×_k 𝔸^c_k`. -/
noncomputable def incidenceSection (v : Fin c → Γ(L, ⊤)) (w₀ : Γ(L, ⊤)) (j : Fin c) :
    Γ((Scheme.Modules.pullback
      (pullback.fst p (𝔸(ULift.{u} (Fin c); Spec (.of k)) ↘ Spec (.of k)))).obj L, ⊤) :=
  pullbackGlobalSections (pullback.fst _ _) L (v j) -
    (pullback.snd p (𝔸(ULift.{u} (Fin c); Spec (.of k)) ↘ Spec (.of k))).appTop
      (AffineSpace.coord (Spec (.of k)) (ULift.up j)) •
      pullbackGlobalSections (pullback.fst _ _) L w₀

/-- Pulling back an ideal sheaf along `pr₁` and restricting along `originSection` does nothing. -/
private theorem comap_comap_originSection (I : X.IdealSheafData) :
    (I.comap (pullback.fst p (𝔸(ULift.{u} (Fin c); Spec (.of k)) ↘ Spec (.of k)))).comap
      (originSection p c) = I := by
  rw [← Scheme.IdealSheafData.comap_comp, originSection_fst, Scheme.IdealSheafData.comap_id]

/-- **On the fibre over the origin the incidence equations are the `vⱼ`.** -/
theorem comap_zeroScheme_incidenceSection_originSection (v : Fin c → Γ(L, ⊤)) (w₀ : Γ(L, ⊤))
    (j : Fin c) :
    (zeroScheme _ _ (incidenceSection p L v w₀ j)).comap (originSection p c) =
      zeroScheme X L (v j) := by
  have hsec : pullbackGlobalSections (originSection p c) _ (incidenceSection p L v w₀ j) =
      pullbackGlobalSections (originSection p c) _
        (pullbackGlobalSections (pullback.fst _ _) L (v j)) := by
    have happ : (originSection p c).appTop
        ((pullback.snd p (𝔸(ULift.{u} (Fin c); Spec (.of k)) ↘ Spec (.of k))).appTop
          (AffineSpace.coord (Spec (.of k)) (ULift.up j))) = 0 := by
      simpa only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
        AffineSpace.homOfVector_appTop_coord, Pi.zero_apply, map_zero] using
        congrArg (fun φ : X ⟶ 𝔸(ULift.{u} (Fin c); Spec (.of k)) =>
          φ.appTop (AffineSpace.coord (Spec (.of k)) (ULift.up j))) (originSection_snd p c)
    rw [incidenceSection, map_sub, SectionsEqualizer.pullbackGlobalSections_smul, happ, zero_smul,
      sub_zero]
  rw [← Stacks.Divisors.zeroScheme_pullback, hsec, Stacks.Divisors.zeroScheme_pullback,
    Stacks.Divisors.zeroScheme_pullback]
  exact comap_comap_originSection p _

/-- **On the fibre over the origin the partial intersections of the incidence family are the
`V(v₁, …, v_m)`.** -/
theorem comap_partialIdeal_incidenceSection_originSection (v : Fin c → Γ(L, ⊤)) (w₀ : Γ(L, ⊤))
    (m : ℕ) :
    (partialIdeal _ (incidenceSection p L v w₀) m).comap (originSection p c) =
      partialIdeal L v m := by
  simp only [partialIdeal]
  rw [(Scheme.IdealSheafData.map_gc _).l_iSup]
  refine iSup_congr fun j => ?_
  rw [(Scheme.IdealSheafData.map_gc _).l_iSup]
  exact iSup_congr fun _ => comap_zeroScheme_incidenceSection_originSection p L v w₀ j

/-- **The pullback of `w₀` restricts to `w₀` on the fibre over the origin.** -/
theorem comap_zeroScheme_pullback_fst_originSection (w₀ : Γ(L, ⊤)) :
    (zeroScheme _ _ (pullbackGlobalSections
      (pullback.fst p (𝔸(ULift.{u} (Fin c); Spec (.of k)) ↘ Spec (.of k))) L w₀)).comap
        (originSection p c) =
      zeroScheme X L w₀ := by
  have h₃ : zeroScheme _ _ (pullbackGlobalSections
      (pullback.fst p (𝔸(ULift.{u} (Fin c); Spec (.of k)) ↘ Spec (.of k))) L w₀) =
      (zeroScheme X L w₀).comap (pullback.fst _ _) := Stacks.Divisors.zeroScheme_pullback _ _ _
  rw [h₃]
  exact comap_comap_originSection p _

end AlgebraicGeometry.GoodNeighbourhood

end
