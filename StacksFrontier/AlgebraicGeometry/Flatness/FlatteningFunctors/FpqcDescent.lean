module

public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import StacksFrontier.AlgebraicGeometry.Flatness.FlatteningFunctors.Injectivity

/-!
# The four conditions on a base-changed module homomorphism are fpqc local on the base

Let `u : F ⟶ G` be a homomorphism of quasi-coherent modules on a scheme `X` over `S`, and let
`T` be a scheme over `S`.  If `{T_i → T}` is an fpqc covering, then `u_T` is injective,
surjective, an isomorphism, or zero exactly when every `u_{T_i}` is.

Only one implication needs an argument.  The maps `X ×_S T_i → X ×_S T` are flat, and jointly
surjective because `{T_i → T}` is; so every point of `X ×_S T` is the image of a point of some
`X ×_S T_i`, and at such a point the stalk of `u_{T_i}` is the extension of scalars of the
stalk of `u_T` along a faithfully flat homomorphism.

## Main results

* `Stacks.Flatness.ModuleMapBaseChangeSituation.isInjectiveAfterBaseChange_iff_fpqcCover`,
  `isSurjectiveAfterBaseChange_iff_fpqcCover`, `isIsomorphismAfterBaseChange_iff_fpqcCover` and
  `isZeroAfterBaseChange_iff_fpqcCover`.

## Implementation notes

An fpqc covering of `T` is taken in the form of a
`CategoryTheory.Precoverage.ZeroHypercover` for `AlgebraicGeometry.Scheme.fpqcPrecoverage`;
its index type lives in an arbitrary universe, independent of the universe of the schemes.

## References

* [Stacks Project, Tag 05MJ](https://stacks.math.columbia.edu/tag/05MJ)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u w

namespace Stacks.Flatness.ModuleMapBaseChangeSituation

variable (D : ModuleMapBaseChangeSituation.{u}) {T T' : Over D.S}

/-- Injectivity of the base-changed homomorphism over `T'` is injectivity of the pullback along
the transition morphism of the base-changed homomorphism over `T`. -/
private theorem isInjectiveAfterBaseChange_iff_mono_pullback (g : T' ⟶ T) :
    D.IsInjectiveAfterBaseChange T' ↔
      Mono ((Scheme.Modules.pullback (D.baseChangeTransition g)).map (D.baseChangeMap T)) := by
  have hn := D.baseChangeMap_transition_naturality g
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · have hc : Mono ((D.baseChangeTransitionIso g).hom.app D.F ≫ D.baseChangeMap T') :=
      mono_comp _ _
    rw [hn] at hc
    exact (MorphismProperty.cancel_right_of_respectsIso
      (MorphismProperty.monomorphisms _) _ _).mp hc
  · have hc : Mono ((Scheme.Modules.pullback (D.baseChangeTransition g)).map
        (D.baseChangeMap T) ≫ (D.baseChangeTransitionIso g).hom.app D.G) := mono_comp _ _
    rw [← hn] at hc
    exact (MorphismProperty.cancel_left_of_respectsIso
      (MorphismProperty.monomorphisms _) _ _).mp hc

/-- Surjectivity of the base-changed homomorphism over `T'` is surjectivity of the pullback
along the transition morphism of the base-changed homomorphism over `T`. -/
private theorem isSurjectiveAfterBaseChange_iff_epi_pullback (g : T' ⟶ T) :
    D.IsSurjectiveAfterBaseChange T' ↔
      Epi ((Scheme.Modules.pullback (D.baseChangeTransition g)).map (D.baseChangeMap T)) := by
  have hn := D.baseChangeMap_transition_naturality g
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · have hc : Epi ((D.baseChangeTransitionIso g).hom.app D.F ≫ D.baseChangeMap T') :=
      epi_comp _ _
    rw [hn] at hc
    exact (MorphismProperty.cancel_right_of_respectsIso
      (MorphismProperty.epimorphisms _) _ _).mp hc
  · have hc : Epi ((Scheme.Modules.pullback (D.baseChangeTransition g)).map
        (D.baseChangeMap T) ≫ (D.baseChangeTransitionIso g).hom.app D.G) := epi_comp _ _
    rw [← hn] at hc
    exact (MorphismProperty.cancel_left_of_respectsIso
      (MorphismProperty.epimorphisms _) _ _).mp hc

/-- Vanishing of the base-changed homomorphism over `T'` is vanishing of the pullback along the
transition morphism of the base-changed homomorphism over `T`. -/
private theorem isZeroAfterBaseChange_iff_pullback_eq_zero (g : T' ⟶ T) :
    D.IsZeroAfterBaseChange T' ↔
      (Scheme.Modules.pullback (D.baseChangeTransition g)).map (D.baseChangeMap T) = 0 := by
  have hn := D.baseChangeMap_transition_naturality g
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · refine (cancel_mono ((D.baseChangeTransitionIso g).hom.app D.G)).1 ?_
    rw [← hn, h]
    simp
  · refine (cancel_epi ((D.baseChangeTransitionIso g).hom.app D.F)).1 ?_
    rw [hn, h]
    simp

/-- If the transition morphism `T' ⟶ T` is flat, a point of `X ×_S T` lifts to `X ×_S T'`
as soon as its image in `T` lifts to `T'`. -/
private theorem exists_baseChangeTransition_preimage (g : T' ⟶ T) (hg : Flat g.left)
    (z : D.baseChange T) (y₀ : T'.left)
    (hy₀ : g.left.base y₀ = (pullback.snd D.f T.hom).base z) :
    ∃ y, (D.baseChangeTransition g).base y = z :=
  Stacks.BaseChange.exists_transition_preimage D.f g hg z y₀ hy₀

/-- The three reflection statements for an fpqc covering, proved together because they share
the construction of a preimage of a point. -/
private theorem fpqcCover_reflection
    (T : Over D.S) (𝒰 : Precoverage.ZeroHypercover.{w} Scheme.fpqcPrecoverage T.left) :
    (D.IsInjectiveAfterBaseChange T ↔
      ∀ i, D.IsInjectiveAfterBaseChange (Over.mk (𝒰.f i ≫ T.hom))) ∧
    (D.IsSurjectiveAfterBaseChange T ↔
      ∀ i, D.IsSurjectiveAfterBaseChange (Over.mk (𝒰.f i ≫ T.hom))) ∧
    (D.IsZeroAfterBaseChange T ↔
      ∀ i, D.IsZeroAfterBaseChange (Over.mk (𝒰.f i ≫ T.hom))) := by
  have hdata := (Scheme.presieve₀_mem_precoverage_iff (P := @Flat) 𝒰.toPreZeroHypercover).mp
    (Scheme.propQCPrecoverage_le_precoverage (P := @Flat) T.left 𝒰.mem₀)
  have hflat : ∀ i, Flat (𝒰.f i) := hdata.2
  set localHom : ∀ i, Over.mk (𝒰.f i ≫ T.hom) ⟶ T := fun i ↦ Over.homMk (𝒰.f i) (by simp)
  have hlift : ∀ z : D.baseChange T, ∃ i, ∃ y : D.baseChange (Over.mk (𝒰.f i ≫ T.hom)),
      (D.baseChangeTransition (localHom i)).base y = z := by
    intro z
    obtain ⟨i, y₀, hy₀⟩ := hdata.1 ((pullback.snd D.f T.hom).base z)
    exact ⟨i, D.exists_baseChangeTransition_preimage (localHom i) (hflat i) z y₀ hy₀⟩
  refine ⟨⟨fun h i ↦ D.isInjectiveAfterBaseChange_of_flat_hom (localHom i) (hflat i) h, ?_⟩,
    ⟨fun h i ↦ D.isSurjectiveAfterBaseChange_of_hom (localHom i) h, ?_⟩,
    ⟨fun h i ↦ D.isZeroAfterBaseChange_of_hom (localHom i) h, ?_⟩⟩
  · intro h
    refine (SheafOfModules.mono_iff_injective_stalkMap (D.baseChangeMap T)).2 fun z ↦ ?_
    obtain ⟨i, y, hy⟩ := hlift z
    have hq : Flat (D.baseChangeTransition (localHom i)) :=
      D.baseChangeTransition_flat (localHom i) (hflat i)
    have hmono := (D.isInjectiveAfterBaseChange_iff_mono_pullback (localHom i)).mp (h i)
    have := (injective_stalkMap_modulePullback_iff (D.baseChangeTransition (localHom i))
      (D.baseChangeMap T) y).mp ((SheafOfModules.mono_iff_injective_stalkMap _).mp hmono y)
    rwa [hy] at this
  · intro h
    refine (SheafOfModules.epi_iff_surjective_stalkMap (D.baseChangeMap T)).2 fun z ↦ ?_
    obtain ⟨i, y, hy⟩ := hlift z
    have hq : Flat (D.baseChangeTransition (localHom i)) :=
      D.baseChangeTransition_flat (localHom i) (hflat i)
    have hepi := (D.isSurjectiveAfterBaseChange_iff_epi_pullback (localHom i)).mp (h i)
    have := (surjective_stalkMap_modulePullback_iff (D.baseChangeTransition (localHom i))
      (D.baseChangeMap T) y).mp ((SheafOfModules.epi_iff_surjective_stalkMap _).mp hepi y)
    rwa [hy] at this
  · intro h
    refine (SheafOfModules.eq_zero_iff_stalkMap_apply_eq_zero _ (D.baseChangeMap T)).2
      fun z m ↦ ?_
    obtain ⟨i, y, hy⟩ := hlift z
    have hq : Flat (D.baseChangeTransition (localHom i)) :=
      D.baseChangeTransition_flat (localHom i) (hflat i)
    have hzero := (D.isZeroAfterBaseChange_iff_pullback_eq_zero (localHom i)).mp (h i)
    have hst := (SheafOfModules.eq_zero_iff_stalkMap_apply_eq_zero _ _).mp hzero y
    have := (stalkMap_modulePullback_eq_zero_iff (D.baseChangeTransition (localHom i))
      (D.baseChangeMap T) y).mp hst
    rw [hy] at this
    exact this m

/-- Injectivity of the base-changed homomorphism is fpqc local on the base. -/
theorem isInjectiveAfterBaseChange_iff_fpqcCover (T : Over D.S)
    (𝒰 : Precoverage.ZeroHypercover.{w} Scheme.fpqcPrecoverage T.left) :
    D.IsInjectiveAfterBaseChange T ↔
      ∀ i, D.IsInjectiveAfterBaseChange (Over.mk (𝒰.f i ≫ T.hom)) :=
  (D.fpqcCover_reflection T 𝒰).1

/-- Surjectivity of the base-changed homomorphism is fpqc local on the base. -/
theorem isSurjectiveAfterBaseChange_iff_fpqcCover (T : Over D.S)
    (𝒰 : Precoverage.ZeroHypercover.{w} Scheme.fpqcPrecoverage T.left) :
    D.IsSurjectiveAfterBaseChange T ↔
      ∀ i, D.IsSurjectiveAfterBaseChange (Over.mk (𝒰.f i ≫ T.hom)) :=
  (D.fpqcCover_reflection T 𝒰).2.1

/-- Vanishing of the base-changed homomorphism is fpqc local on the base. -/
theorem isZeroAfterBaseChange_iff_fpqcCover (T : Over D.S)
    (𝒰 : Precoverage.ZeroHypercover.{w} Scheme.fpqcPrecoverage T.left) :
    D.IsZeroAfterBaseChange T ↔
      ∀ i, D.IsZeroAfterBaseChange (Over.mk (𝒰.f i ≫ T.hom)) :=
  (D.fpqcCover_reflection T 𝒰).2.2

/-- Being an isomorphism after base change is fpqc local on the base: it is the conjunction of
injectivity and surjectivity, each of which is. -/
theorem isIsomorphismAfterBaseChange_iff_fpqcCover (T : Over D.S)
    (𝒰 : Precoverage.ZeroHypercover.{w} Scheme.fpqcPrecoverage T.left) :
    D.IsIsomorphismAfterBaseChange T ↔
      ∀ i, D.IsIsomorphismAfterBaseChange (Over.mk (𝒰.f i ≫ T.hom)) := by
  show IsIso (D.baseChangeMap T) ↔ ∀ i, IsIso (D.baseChangeMap (Over.mk (𝒰.f i ≫ T.hom)))
  simp only [isIso_iff_mono_and_epi, forall_and]
  exact and_congr (D.isInjectiveAfterBaseChange_iff_fpqcCover T 𝒰)
    (D.isSurjectiveAfterBaseChange_iff_fpqcCover T 𝒰)

end Stacks.Flatness.ModuleMapBaseChangeSituation

end
