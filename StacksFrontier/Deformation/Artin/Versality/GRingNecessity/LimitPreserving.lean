module

public import Mathlib.AlgebraicGeometry.AffineTransitionLimit
public import StacksFrontier.Deformation.Artin.Approximation
public import StacksFrontier.Deformation.Artin.Versality.GRingNecessity.Functor

/-!
# The category of Stacks Example 98.12.8 is limit preserving on objects

Let `Λ` be a Noetherian ring, `𝔪 ⊂ Λ` a maximal ideal, `C` a finite type `Λ`-algebra, and
`𝒳 = 𝒮_F` the category fibred in sets of Stacks Example 98.12.8, whose objects over `T` are
the factorizations of `T → S = Spec Λ` through `S' = (S ∖ {𝔪}) ⨿ Spec C`. This file proves the
first claim of the Example: `𝒳 → (Sch/S)_{fppf}` is limit preserving on objects.

The morphism `S' → S` is locally of finite presentation: it is an open immersion on
`S ∖ {𝔪}`, and `C` is finitely presented over the Noetherian ring `Λ`. Hence a morphism over
`S` from the limit of a cofiltered system of affine `S`-schemes to `S'` factors through one
member of the system (Limits, Proposition 32.6.1), which is exactly the descent of objects of
`𝒳`; the comparison morphisms of `𝒳` exist and are unique because `F` has subsingleton values.

## Main results

* `Deformation.Artin.GRingNecessity.factorizationCategory_isLimitPreservingOnObjects`:
  **Stacks Example 98.12.8**, `𝒳` is limit preserving on objects, in the form used by the
  hypothesis of Stacks 07XH.

## Implementation notes

The statement is `BigFppfOver.IsLimitPreservingOnObjects.{u, u, u, u, u + 1}` for `𝒳` over the
base `baseFiberedCategory` with `structureMorphism`, exactly the hypothesis `hlimit` of the
formalization of Stacks 07XH (see
`Deformation.Artin.AlgebraizationConclusion`): cofiltered index categories `I : Type u` with
`Category.{u} I` and affine objects of the big fppf site of `S`.

## References

* [Stacks Project, Tag 07XI](https://stacks.math.columbia.edu/tag/07XI)
* [Stacks Project, Tag 07XH](https://stacks.math.columbia.edu/tag/07XH)
* [Stacks Project, Tag 06CU](https://stacks.math.columbia.edu/tag/06CU)
* [Stacks Project, Tag 01ZC](https://stacks.math.columbia.edu/tag/01ZC)
-/

@[expose] public noncomputable section

namespace Deformation.Artin.GRingNecessity

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u


variable {Λ : Type u} [CommRing Λ] (𝔪 : Ideal Λ) [𝔪.IsMaximal] (C : Type u) [CommRing C]
  [Algebra Λ C] (B : BigFppfSite.{u}) (hS : B.Contains (Spec (.of Λ)))

/-- The inclusion of the big affine fppf site of `Spec Λ` into its big fppf site. -/
abbrev affineIncl : BigAffineFppf B (Spec (.of Λ)) hS ⥤ BigFppfOver B (Spec (.of Λ)) hS :=
  BigAffineFppf.inclusion B (Spec (.of Λ)) hS

/-- A morphism is the composite of itself with identities. -/
theorem eq_id_comp_comp_id {𝒞 : Type*} [Category 𝒞] {X Y : 𝒞} (f : X ⟶ Y) :
    f = 𝟙 X ≫ f ≫ 𝟙 Y := by
  simp

/-- **Stacks Example 98.12.8: `𝒳` is limit preserving on objects.** -/
theorem factorizationCategory_isLimitPreservingOnObjects [IsNoetherianRing Λ]
    [Algebra.FiniteType Λ C] :
    BigFppfOver.IsLimitPreservingOnObjects.{u, u, u, u, u + 1} B (Spec (.of Λ)) hS
      (factorizationCategory 𝔪 C B hS)
      (Deformation.Artin.Approximation.baseFiberedCategory B (Spec (.of Λ)) hS)
      (Deformation.Artin.Approximation.structureMorphism B (Spec (.of Λ)) hS
        (factorizationCategory 𝔪 C B hS)) := by
  intro I _ _ D c hc i y x γ hγ
  have : LocallyOfFinitePresentation (puncturedCoprodMap 𝔪 C) :=
    locallyOfFinitePresentation_puncturedCoprodMap 𝔪 C
  obtain ⟨⟨xb, xf⟩, hx⟩ := x
  change xb = (affineIncl B hS).obj c.pt at hx
  subst hx
  obtain ⟨y, hy⟩ := y
  change y = (affineIncl B hS).obj (D.obj i) at hy
  subst hy
  let D' := D ⋙ BigAffineFppf.toScheme B (Spec (.of Λ)) hS
  let t : D' ⟶ (Functor.const I).obj (Spec (.of Λ)) :=
    { app := fun j => structureHom B hS ((affineIncl B hS).obj (D.obj j))
      naturality := fun j j' e => by
        simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.comp_id]
        exact structureHom_comp B hS ((affineIncl B hS).map (D.map e)) }
  have : ∀ (j : I), IsAffine (D'.obj j) := fun j => (D.obj j).property
  have : ∀ {j j' : I} (e : j ⟶ j'), IsAffineHom (D'.map e) := fun _ => inferInstance
  have : ∀ j : I, CompactSpace (D'.obj j) := fun _ => inferInstance
  have : ∀ j : I, QuasiSeparatedSpace (D'.obj j) := fun _ => inferInstance
  obtain ⟨g, hg⟩ : FactorsThroughPuncturedCoprod 𝔪 C
      (structureHom B hS ((affineIncl B hS).obj c.pt)) :=
    xf.as.2
  obtain ⟨i₀, g₀, -, hg₀⟩ := Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation D' t
    (puncturedCoprodMap 𝔪 C) ((BigAffineFppf.toScheme B (Spec (.of Λ)) hS).mapCone c) hc g (by
      ext j
      simp only [NatTrans.comp_app, Functor.const_map_app]
      rw [hg]
      exact structureHom_comp B hS ((affineIncl B hS).map (c.π.app j)))
  let i' := IsCofiltered.min i i₀
  let j : i' ⟶ i := IsCofiltered.minToLeft i i₀
  let k : i' ⟶ i₀ := IsCofiltered.minToRight i i₀
  have hfac : FactorsThroughPuncturedCoprod 𝔪 C
      (structureHom B hS ((affineIncl B hS).obj (D.obj i'))) :=
    ⟨D'.map k ≫ g₀, by
      rw [Category.assoc, hg₀]
      exact structureHom_comp B hS ((affineIncl B hS).map (D.map k))⟩
  have hp := (factorizationCategory 𝔪 C B hS).isFiberedInGroupoids
  have hb :=
    (Deformation.Artin.Approximation.baseFiberedCategory B (Spec (.of Λ)) hS).isFiberedInGroupoids
  let X : (factorizationCategory 𝔪 C B hS).val.obj := ⟨(affineIncl B hS).obj c.pt, xf⟩
  let X' : (factorizationCategory 𝔪 C B hS).val.obj :=
    mkObj 𝔪 C B hS ((affineIncl B hS).obj (D.obj i')) hfac
  refine ⟨i', j, ⟨X', rfl⟩, ⟨X, rfl⟩,
    homOfBase (X := X) (Y := X') ((affineIncl B hS).map (c.π.app i')),
    𝟙 _, (affineIncl B hS).map (D.map j), ?_, ?_, inferInstance, ?_, ?_⟩
  · have : (factorizationCategory 𝔪 C B hS).val.p.IsHomLift ((affineIncl B hS).map (c.π.app i'))
        (homOfBase (X := X) (Y := X') ((affineIncl B hS).map (c.π.app i'))) :=
      IsHomLift.of_fac' _ _ _ rfl rfl (eq_id_comp_comp_id ((affineIncl B hS).map (c.π.app i')))
    exact hp.isStronglyCartesian_homLift _ _
  · exact IsHomLift.of_fac' _ _ _ rfl rfl (eq_id_comp_comp_id (𝟙 ((affineIncl B hS).obj c.pt)))
  · have : (Deformation.Artin.Approximation.baseFiberedCategory B (Spec (.of Λ)) hS).val.p.IsHomLift
        ((affineIncl B hS).map (D.map j)) ((affineIncl B hS).map (D.map j)) :=
      IsHomLift.of_fac' _ _ _ rfl rfl (eq_id_comp_comp_id ((affineIncl B hS).map (D.map j)))
    exact @Functor.IsFiberedInGroupoids.isStronglyCartesian_homLift _ _ _ _ _ hb _ _ _ _
      ((affineIncl B hS).map (D.map j)) ((affineIncl B hS).map (D.map j)) this
  · have hγ' : γ = (affineIncl B hS).map (c.π.app i) :=
      (@IsHomLift.eq_of_isHomLift _ _ _ _
        (Deformation.Artin.Approximation.baseFiberedCategory B (Spec (.of Λ)) hS).val.p _ _
        ((affineIncl B hS).map (c.π.app i)) γ hγ.toIsHomLift).symm
    subst hγ'
    change (affineIncl B hS).map (c.π.app i') ≫ (affineIncl B hS).map (D.map j) =
      𝟙 ((affineIncl B hS).obj c.pt) ≫ (affineIncl B hS).map (c.π.app i)
    rw [Category.id_comp, ← Functor.map_comp, c.w j]

end Deformation.Artin.GRingNecessity

end
