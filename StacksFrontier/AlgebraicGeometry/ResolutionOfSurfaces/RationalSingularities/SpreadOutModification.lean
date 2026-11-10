module

public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalSingularities.LocalBirationalExtensions
public import StacksFrontier.AlgebraicGeometry.Pullback.StalkFromSpecStalk
public import StacksFrontier.AlgebraicGeometry.Morphisms.Birational.Stability
public import StacksFrontier.AlgebraicGeometry.Morphisms.Birational.GenericPoint
public import StacksFrontier.AlgebraicGeometry.Properties.Normal

/-!
# A spread-out modification of a local ring is a normal modification

Let `f : X ⟶ Spec(A)` be a modification with `X` normal, `x ∈ X` a closed point, and
`g : X' ⟶ X` a proper morphism which is an isomorphism over `X ∖ {x}` and whose base change
`Y ⟶ Spec 𝒪_{X, x}` along `Spec 𝒪_{X, x} ⟶ X` is a normal modification. Step 4 of the source's
proof of [Stacks, Tag 0BG0] says that then `X'` is normal and `g ≫ f` is a modification of
`Spec(A)`: the local rings of `X'` are those of `X` away from `x` and those of `Y` above `x`.

## Main results

* `AlgebraicGeometry.isNormal_and_isModification_of_isPullback_fromSpecStalk`: Step 4 of the
  proof of [Stacks, Tag 0BG0].

## Implementation notes

The hypotheses `AlgebraicGeometry.SpreadOutIsNormalModification` and
`AlgebraicGeometry.SpreadOutIsNormalModificationOverSpec` were meant to carry this step, but
they ask only that the base change `Y` be *normal*. That is not enough, and both are false as
stated: for `X = Spec(A)`, `f = 𝟙` and `X' = X ⊔ Spec κ(x)` mapping to `X` by the identity and
the closed point, `g` is proper, of finite presentation and an isomorphism over `X ∖ {x}`, and
`Y = Spec 𝒪_{X, x} ⊔ Spec κ(x)` is normal, but `X'` is not integral. The theorem below asks, as
the source does, that `Y ⟶ Spec 𝒪_{X, x}` be a modification. It also asks that `x` not be the
generic point of `X`, which holds for a closed point of a scheme of positive dimension.

## References

* [Stacks Project, Tag 0BG0](https://stacks.math.columbia.edu/tag/0BG0)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

open GlueingNearPoint

/-- Normality of a local ring transports backwards along an isomorphism of rings. -/
private theorem normal_of_iso {R S : CommRingCat.{u}} (e : R ≅ S) [IsDomain S]
    [IsIntegrallyClosed S] : ∃ _ : IsDomain R, IsIntegrallyClosed R := by
  let e' : S ≃+* R := e.symm.commRingCatIsoToRingEquiv
  have : IsDomain R := Function.Injective.isDomain e'.symm e'.symm.injective
  exact ⟨inferInstance, IsIntegrallyClosed.of_equiv e'⟩

/-- **Step 4 of [Stacks, Tag 0BG0].** Let `f : X ⟶ Spec(A)` be a modification with `X` normal,
`x ∈ X` a closed point other than the generic point, and `g : X' ⟶ X` a proper morphism which is
an isomorphism over `X ∖ {x}`. If the base change `p : Y ⟶ Spec 𝒪_{X, x}` of `g` along
`Spec 𝒪_{X, x} ⟶ X` is a modification with `Y` normal, then `X'` is normal and `g ≫ f` is a
modification of `Spec(A)`. -/
theorem isNormal_and_isModification_of_isPullback_fromSpecStalk
    {A : Type u} [CommRing A] [IsDomain A] {X : Scheme.{u}} [IsNormal X]
    (f : X ⟶ Spec (.of A)) (hf : IsModification f) (x : X) (hx : IsClosed ({x} : Set X))
    (hxη : letI := hf.source_isIntegral; x ≠ genericPoint X)
    {X' Y : Scheme.{u}} (g : X' ⟶ X) (p : Y ⟶ Spec (X.presheaf.stalk x)) (q : Y ⟶ X')
    (hsq : IsPullback q p g (X.fromSpecStalk x)) (hg : IsProper g)
    (hiso : IsIso ((Over.pullback (puncturedOpen hx).ι).obj (Over.mk g)).hom)
    (hY : IsNormal Y) (hp : IsModification p) :
    IsNormal X' ∧ IsModification (g ≫ f) := by
  have : IsIntegral X := hf.source_isIntegral
  have : IsIntegral Y := hp.source_isIntegral
  set U := puncturedOpen hx
  have hU : IsIso (g ∣_ U) := by
    have : IsIso (pullback.snd g U.ι) := hiso
    rw [morphismRestrict]
    infer_instance
  have : Flat (X.fromSpecStalk x) := flat_fromSpecStalk X x
  have : Flat q := MorphismProperty.IsStableUnderBaseChange.of_isPullback hsq.flip inferInstance
  have : IsPreimmersion q :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback hsq.flip inferInstance
  have hover : ∀ x' : X', g x' = x → ∃ w : Y, q w = x' ∧ IsIso (q.stalkMap w) := by
    intro x' hx'
    obtain ⟨w₀, hw₀, -⟩ := exists_point_pullback_fromSpecStalk_isIso_stalkMap g x x' hx'
    refine ⟨hsq.isoPullback.inv w₀, ?_, isIso_stalkMap_of_flat_isPreimmersion q _⟩
    rw [← Scheme.Hom.comp_apply, hsq.isoPullback_inv_fst]
    exact hw₀
  have haway : ∀ x' : X', g x' ≠ x → IsIso (g.stalkMap x') := by
    intro x' hx'
    have hmem : x' ∈ g ⁻¹ᵁ U := hx'
    have : IsIso ((g ∣_ U).stalkMap ⟨x', hmem⟩) :=
      ((isIso_iff_isIso_stalkMap (g ∣_ U)).mp hU).2 _
    exact (Arrow.isIso_iff_isIso_of_isIso (morphismRestrictStalkMap g U ⟨x', hmem⟩).hom).mp this
  have hX' : IsNormal X' := by
    rw [isNormal_iff_stalk_normal]
    intro x'
    by_cases hx' : g x' = x
    · obtain ⟨w, rfl, hw⟩ := hover x' hx'
      have := hY.stalk_normal w
      exact normal_of_iso (asIso (q.stalkMap w))
    · have := haway x' hx'
      have := IsNormal.stalk_normal (X := X) (g x')
      exact normal_of_iso (asIso (g.stalkMap x')).symm
  refine ⟨hX', ?_⟩
  set ξ := q (genericPoint Y)
  have hgξ : g ξ = genericPoint X := by
    have h1 : g ξ = X.fromSpecStalk x (p (genericPoint Y)) := by
      simp only [ξ, ← Scheme.Hom.comp_apply, hsq.w]
    rw [h1, IsBirational.genericPoint_eq p hp.isBirational, fromSpecStalk_genericPoint]
  have hξU : ξ ∈ g ⁻¹ᵁ U := by
    change g ξ ∈ ({x} : Set X)ᶜ
    rw [hgξ]
    exact fun h => hxη h.symm
  have hspec : ∀ x' : X', ξ ⤳ x' := by
    intro x'
    by_cases hx' : g x' = x
    · obtain ⟨w, rfl, -⟩ := hover x' hx'
      exact ((genericPoint_spec Y).specializes (Set.mem_univ w)).map q.continuous
    · have hmem : x' ∈ g ⁻¹ᵁ U := hx'
      let e := (g ∣_ U).homeomorph
      have h1 : ((g ∣_ U) ⟨ξ, hξU⟩).1 = genericPoint X :=
        (morphismRestrict_base_coe g U _).trans hgξ
      have h2 : ((g ∣_ U) ⟨x', hmem⟩).1 = g x' := morphismRestrict_base_coe g U _
      have hs : e ⟨ξ, hξU⟩ ⤳ e ⟨x', hmem⟩ := by
        refine (subtype_specializes_iff _ _).mpr ?_
        change ((g ∣_ U) ⟨ξ, hξU⟩).1 ⤳ ((g ∣_ U) ⟨x', hmem⟩).1
        rw [h1, h2]
        exact (genericPoint_spec X).specializes (Set.mem_univ _)
      exact (subtype_specializes_iff _ _).mp (e.isInducing.specializes_iff.mp hs)
  have hirr : IrreducibleSpace X' := by
    have hcl : closure ({ξ} : Set X') = Set.univ :=
      Set.eq_univ_of_forall fun x' => specializes_iff_mem_closure.mp (hspec x')
    have h := (isIrreducible_singleton (x := ξ)).closure
    rw [hcl] at h
    exact (irreducibleSpace_def X').mpr h
  have hint : IsIntegral X' := isIntegral_of_irreducibleSpace_of_isReduced X'
  have hgen : genericPoint X' = ξ :=
    (((genericPoint_spec X').specializes (Set.mem_univ ξ)).antisymm (hspec _)).eq
  have hgbir : IsBirational g := by
    refine isBirational_of_isIso_morphismRestrict g U hU ?_ ?_
    · intro x' hx'
      rw [genericPoints_eq_singleton, Set.mem_singleton_iff] at hx'
      rw [hx', hgen]
      exact hξU
    · intro y hy
      rw [genericPoints_eq_singleton, Set.mem_singleton_iff] at hy
      rw [hy]
      exact fun h => hxη h.symm
  exact ⟨hgbir.comp hf.isBirational, by have := hf.isProper; infer_instance, hint⟩

end AlgebraicGeometry

end
