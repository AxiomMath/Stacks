module

public import StacksFrontier.Algebra.Homology.RightDerivedDeltaOne
public import StacksFrontier.Algebra.Homology.RightDerivedDelta

/-!
# Surjectivity of the co-edge morphism in degree one

Let `P : A ⥤ B` and `Q : B ⥤ D` be additive left exact functors between abelian categories with
enough injectives, with `P` preserving injective objects. The five-term exact sequence of the
composite `Q ∘ P` continues the co-edge morphism `R¹(Q ∘ P) X ⟶ Q (R¹P X)` by a morphism to
`R²Q (P X)`. This file proves the consequence of that exactness which is used in practice: when
`R²Q (P X)` vanishes, the co-edge morphism in degree one is an epimorphism.

## Main results

* `Stacks.Cohomology.RightDerivedCoEdge.epi_map_homologyπ_one_of_isZero`: for an injective
  resolution `I` of `X`, `Q` applied to the projection `Z¹(P I) ⟶ H¹(P I)` is an epimorphism as
  soon as `R²Q (P X) = 0`.
* `Stacks.Cohomology.RightDerivedCoEdge.epi_secondEdge_app_one_of_isZero`: the co-edge
  morphism `R¹(Q ∘ P) X ⟶ Q (R¹P X)` is an epimorphism as soon as `R²Q (P X) = 0`.

## Implementation notes

Write `K = P I` and `a : P X ⟶ K⁰` for `P` applied to the augmentation. Left exactness of `P`
makes `0 ⟶ P X ⟶ K⁰ ⟶ K¹` exact, so `0 ⟶ coker a ⟶ Z¹ K ⟶ H¹ K ⟶ 0` is short exact
(`Stacks.Cohomology.RightDerivedDeltaOne.shortExact_cyclesOfCoaug`), and its long exact sequence
of right derived functors of `Q` gives `Q (Z¹ K) ⟶ Q (H¹ K) ⟶ R¹Q (coker a)`. The sequence
`0 ⟶ P X ⟶ K⁰ ⟶ coker a ⟶ 0` has injective middle term, so dimension shifting identifies
`R¹Q (coker a)` with `R²Q (P X)`. The co-edge morphism, on cycles, is `Q` applied to the
projection `Z¹ K ⟶ H¹ K` (`Stacks.Cohomology.RightDerivedCoEdge.secondEdge_app_eq`), so it is an
epimorphism when that is.

## References

* [Stacks Project, Tag 01F2](https://stacks.math.columbia.edu/tag/01F2)
* [Stacks Project, Tag 015N](https://stacks.math.columbia.edu/tag/015N)
-/

@[expose] public noncomputable section

open CategoryTheory Category Limits

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace Stacks.Cohomology.RightDerivedCoEdge

variable {A : Type u₁} [Category.{v₁} A] [Abelian A]
  {B : Type u₂} [Category.{v₂} B] [Abelian B]
  {D : Type u₃} [Category.{v₃} D] [Abelian D]
  [HasInjectiveResolutions A] [EnoughInjectives B]
  (P : A ⥤ B) [P.Additive] [P.PreservesInjectiveObjects] [PreservesFiniteLimits P]
  (Q : B ⥤ D) [Q.Additive] [PreservesFiniteLimits Q]

omit [HasInjectiveResolutions A] in
/-- **`Q` applied to the projection `Z¹(P I) ⟶ H¹(P I)` is an epimorphism when `R²Q (P X) = 0`.**
The kernel of the projection is `coker (P X ⟶ (P I)⁰)`, whose first right derived functor is
`R²Q (P X)` by dimension shifting along the injective `(P I)⁰`. -/
theorem epi_map_homologyπ_one_of_isZero {X : A} (I : InjectiveResolution X)
    (h : IsZero ((Q.rightDerived 2).obj (P.obj X))) :
    Epi (Q.map (((P.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex).homologyπ 1)) := by
  set K := (P.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex
  -- the sequence `0 ⟶ P X ⟶ K⁰ ⟶ coker a ⟶ 0`, with injective middle term
  let S₁ : ShortComplex B := ShortComplex.mk (mapAug P I) (cokernel.π (mapAug P I))
    (cokernel.condition (mapAug P I))
  have hS₁ : S₁.ShortExact :=
    { exact := ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel (mapAug P I))
      mono_f := inferInstanceAs (Mono (mapAug P I))
      epi_g := inferInstanceAs (Epi (cokernel.π (mapAug P I))) }
  have : Injective S₁.X₂ :=
    RightDerivedEdge.injective_mapHomologicalComplex_obj P I.cocomplex
      (fun n => inferInstance) 0
  have h₁ : IsZero ((Q.rightDerived 1).obj (cokernel (mapAug P I))) := by
    obtain ⟨e⟩ := RightDerivedDelta.nonempty_iso_rightDerived_of_injective hS₁ Q 0
    exact h.of_iso e
  -- the sequence `0 ⟶ coker a ⟶ Z¹ K ⟶ H¹ K ⟶ 0`
  have hS₂ := RightDerivedDeltaOne.shortExact_cyclesOfCoaug (mapAug P I) (mapAug_comp_d P I)
    (exact_mapAug P I)
  obtain ⟨δ, -, hδ⟩ := RightDerivedDelta.exists_delta_exact_composableArrows₅ hS₂ Q
  have : Epi ((Q.rightDerived 0).map (K.homologyπ 1)) := ((hδ 0).exact 1).epi_f (h₁.eq_of_tgt _ _)
  rw [← NatIso.naturality_1 Q.rightDerivedZeroIsoSelf (K.homologyπ 1)]
  infer_instance

/-- **The co-edge morphism `R¹(Q ∘ P) X ⟶ Q (R¹P X)` is an epimorphism when `R²Q (P X) = 0`.**
This is the exactness of the five-term sequence at `Q (R¹P X)`, in the form used to conclude
surjectivity. -/
theorem epi_secondEdge_app_one_of_isZero (X : A)
    (h : IsZero ((Q.rightDerived 2).obj (P.obj X))) :
    Epi ((secondEdge P Q 1).app X) := by
  have hπ := epi_map_homologyπ_one_of_isZero P Q (injectiveResolution X) h
  have he : Epi (Q.mapIso ((injectiveResolution X).isoRightDerivedObj P 1)).inv := inferInstance
  have := @epi_of_epi_fac _ _ _ _ _ _ _ _ (@epi_comp _ _ _ _ _ _ hπ _ he)
    (secondEdge_app_eq P Q 1 (injectiveResolution X))
  have := @epi_of_epi _ _ _ _ _ _ _ this
  exact @epi_of_epi _ _ _ _ _ _ _ this

end Stacks.Cohomology.RightDerivedCoEdge

end
