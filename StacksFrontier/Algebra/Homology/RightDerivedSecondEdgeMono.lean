module

public import StacksFrontier.Algebra.Homology.RightDerivedSecondEdgeEpi

/-!
# Injectivity of the co-edge morphism in degree one

Let `P : A ⥤ B` and `Q : B ⥤ D` be additive left exact functors between abelian categories with
enough injectives, with `P` preserving injective objects. The five-term exact sequence of the
composite `Q ∘ P` begins

`0 ⟶ R¹Q (P X) ⟶ R¹(Q ∘ P) X ⟶ Q (R¹P X)`.

This file proves the consequence of that exactness used in practice: when `R¹Q (P X)` vanishes,
the co-edge morphism `R¹(Q ∘ P) X ⟶ Q (R¹P X)` is a monomorphism. Together with
`Stacks.Cohomology.RightDerivedCoEdge.epi_secondEdge_app_one_of_isZero` it is an isomorphism
when `R¹Q (P X) = R²Q (P X) = 0`; for `P = j_*` and `Q = Γ(X, -)` this reads
`H¹(U, F) ≅ Γ(X, R¹j_* F)` when `H¹(X, j_* F) = H²(X, j_* F) = 0`.

## Main results

* `Stacks.Cohomology.RightDerivedCoEdge.mono_secondEdge_app_one_of_isZero`.
* `Stacks.Cohomology.RightDerivedCoEdge.isIso_secondEdge_app_one_of_isZero`.

## Implementation notes

Write `K = P I` for an injective resolution `I` of `X` and `a : P X ⟶ K⁰` for `P` applied to the
augmentation. The kernel of the comparison `H¹(Q K) ⟶ Q (H¹ K)` is the image of the class map
`Q (coker a) ⟶ H¹(Q K)` (`Stacks.Cohomology.RightDerivedDeltaOne.exact_coaugClass`). The class map
kills the image of `Q K⁰` (`Stacks.Cohomology.RightDerivedDeltaOne.map_π_comp_coaugClass`), and
`Q K⁰ ⟶ Q (coker a)` is onto when `R¹Q (P X) = 0`, by the long exact sequence of
`0 ⟶ P X ⟶ K⁰ ⟶ coker a ⟶ 0`. So the class map vanishes and the comparison is a monomorphism.

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

omit [HasInjectiveResolutions A] [P.PreservesInjectiveObjects] in
/-- **The comparison `H¹(Q (P I)) ⟶ Q (H¹(P I))` is a monomorphism when `R¹Q (P X) = 0`.** -/
theorem mono_homologyToMapHomology_one_of_isZero {X : A} (I : InjectiveResolution X)
    (h : IsZero ((Q.rightDerived 1).obj (P.obj X))) :
    Mono (homologyToMapHomology Q ((P.mapHomologicalComplex (ComplexShape.up ℕ)).obj
      I.cocomplex) 1) := by
  set K := (P.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex with hK
  have ha : mapAug P I ≫ K.d 0 1 = 0 := mapAug_comp_d P I
  have hex := exact_mapAug P I
  -- the sequence `0 ⟶ P X ⟶ K⁰ ⟶ coker a ⟶ 0`, with injective middle term
  let S₁ : ShortComplex B := ShortComplex.mk (mapAug P I) (cokernel.π (mapAug P I))
    (cokernel.condition (mapAug P I))
  have hS₁ : S₁.ShortExact :=
    { exact := ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel (mapAug P I))
      mono_f := inferInstanceAs (Mono (mapAug P I))
      epi_g := inferInstanceAs (Epi (cokernel.π (mapAug P I))) }
  -- `Q K⁰ ⟶ Q (coker a)` is an epimorphism
  obtain ⟨δ, -, hδ⟩ := RightDerivedDelta.exists_delta_exact_composableArrows₅ hS₁ Q
  have hexact := (hδ 0).exact 1
  have hepi₀ : Epi ((Q.rightDerived 0).map (cokernel.π (mapAug P I))) :=
    hexact.epi_f (h.eq_of_tgt _ _)
  have hnat := (Q.rightDerivedZeroIsoSelf).hom.naturality (cokernel.π (mapAug P I))
  have hfac : Q.map (cokernel.π (mapAug P I)) =
      (Q.rightDerivedZeroIsoSelf).inv.app (K.X 0) ≫
        (Q.rightDerived 0).map (cokernel.π (mapAug P I)) ≫
          (Q.rightDerivedZeroIsoSelf).hom.app (cokernel (mapAug P I)) := by
    rw [hnat, ← Category.assoc, ← NatTrans.comp_app, Iso.inv_hom_id, NatTrans.id_app,
      Category.id_comp]
  have hepi : Epi (Q.map (cokernel.π (mapAug P I))) := by
    rw [hfac]
    infer_instance
  -- the class map vanishes
  have hzero : RightDerivedDeltaOne.coaugClass Q (mapAug P I) ha = 0 := by
    rw [← cancel_epi (Q.map (cokernel.π (mapAug P I))), comp_zero]
    exact RightDerivedDeltaOne.map_π_comp_coaugClass Q (mapAug P I) ha
  exact (RightDerivedDeltaOne.exact_coaugClass Q (mapAug P I) ha hex).mono_g hzero

omit [P.PreservesInjectiveObjects] in
/-- **The co-edge morphism `R¹(Q ∘ P) X ⟶ Q (R¹P X)` is a monomorphism when `R¹Q (P X) = 0`.**
This is the exactness of the five-term sequence at `R¹(Q ∘ P) X`, in the form used to conclude
injectivity. -/
theorem mono_secondEdge_app_one_of_isZero (X : A)
    (h : IsZero ((Q.rightDerived 1).obj (P.obj X))) :
    Mono ((secondEdge P Q 1).app X) := by
  have hm := mono_homologyToMapHomology_one_of_isZero P Q (injectiveResolution X) h
  change Mono (secondEdgeApp P Q 1 X)
  rw [secondEdgeApp]
  have : Mono (homologyFunctorToMapHomology Q
      ((P.mapHomologicalComplex (ComplexShape.up ℕ)).obj (injectiveResolution X).cocomplex) 1) :=
    hm
  refine @mono_comp _ _ _ _ _ _ inferInstance _ (@mono_comp _ _ _ _ _ _ this _ ?_)
  exact inferInstanceAs (Mono (Q.mapIso
    ((injectiveResolution X).isoRightDerivedObj P 1).symm).hom)

/-- **The co-edge morphism `R¹(Q ∘ P) X ⟶ Q (R¹P X)` is an isomorphism when
`R¹Q (P X) = R²Q (P X) = 0`.** -/
theorem isIso_secondEdge_app_one_of_isZero (X : A)
    (h₁ : IsZero ((Q.rightDerived 1).obj (P.obj X)))
    (h₂ : IsZero ((Q.rightDerived 2).obj (P.obj X))) :
    IsIso ((secondEdge P Q 1).app X) :=
  have := mono_secondEdge_app_one_of_isZero P Q X h₁
  have := epi_secondEdge_app_one_of_isZero P Q X h₂
  isIso_of_mono_of_epi _

end Stacks.Cohomology.RightDerivedCoEdge

end
