module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CompactSupportFrobeniusRestrictScalars
public import StacksFrontier.CategoryTheory.FilteredDerived.Perfectness.DerivedFunctorTrace
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.ShortExactTrace
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleComplexes.EtaleModulesCtfCorner

/-!
# The trace of `π_X^*` and restriction of scalars

For a ring morphism `ρ : Λ →+* Λ'` along which restriction of scalars carries finite projective
`Λ'`-modules to finite projective `Λ`-modules (for instance the projection onto a factor of a
product ring), and a bounded below complex `K` of sheaves of `Λ'`-modules with `RΓ_c(X_k̄, K)`
perfect over `Λ'`, the complex `RΓ_c(X_k̄, res K)` is perfect over `Λ` and

`Tr_Λ(π_X^* | RΓ_c(X_k̄, res K)) = res♮(Tr_{Λ'}(π_X^* | RΓ_c(X_k̄, K)))`.

This is the compatibility of `RΓ_c` and of `π_X^*` with restriction of scalars, combined with the
functoriality of traces along exact functors. It reduces the trace formula of
[Stacks, Tag 03UG] for a finite ring to its primary factors.

## Main results

* `Stacks.EtaleCohomology.perfectDerivedTrace_canonicalCompactSupportFrobenius_restrictScalars`
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.FilteredDerived AlgebraicGeometry

universe u

namespace Stacks.DerivedFunctor

variable {A : Type*} {B : Type*} [Category A] [Category B] [Abelian A] [Abelian B]
  [HasDerivedCategory A] [HasDerivedCategory B] (T : A ⥤ B) [T.Additive]
  [PreservesFiniteLimits T] [PreservesFiniteColimits T]

/-- The transformation induced by the identity is the identity. -/
theorem mapDerivedNatTrans_id : mapDerivedNatTrans (𝟙 T) = 𝟙 _ := by
  refine Localization.natTrans_ext DerivedCategory.Q
    (HomologicalComplex.quasiIso A (ComplexShape.up ℤ)) fun K => ?_
  rw [← cancel_mono (T.mapDerivedCategoryFactors.hom.app K), mapDerivedNatTrans_factors_app]
  simp

/-- The bounded below transformation induced by the identity is the identity. -/
theorem mapDerivedCategoryPlusNatTrans_id_app (K : DerivedCategory.Plus A) :
    (mapDerivedCategoryPlusNatTrans (𝟙 T)).app K = 𝟙 _ := by
  ext
  change (mapDerivedNatTrans (𝟙 T)).app K.obj = 𝟙 _
  rw [mapDerivedNatTrans_id]
  rfl

end Stacks.DerivedFunctor

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard

variable {Λ Λ' : Type} [Ring Λ] [Ring Λ'] (ρ : Λ →+* Λ')
  {k : Type u} [Field k] [Fintype k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
  (j : CompactificationOf (Over.mk f)) (kbar : Type u) [Field kbar] [Algebra k kbar]
  (p q : ℕ) [Fact p.Prime] [CharP k p] (hcard : Fintype.card k = p ^ q)

/-- **Restriction of scalars from a corner `eΛ` (`e` a central idempotent) preserves finite
projective modules**: it is left adjoint to `M ↦ eM`, which is exact, and a finite `eΛ`-module is
finite over `Λ`, `Λ ⟶ eΛ` being surjective. -/
theorem preservesFiniteProjective_cornerRestrict {Λ : Type} [Ring Λ] {e : Λ}
    (he : IsIdempotentElem e) (hc : ∀ a : Λ, a * e = e * a) :
    PreservesFiniteProjective.{0, u + 1}
      (ModuleCat.restrictScalars.{u + 1} (cornerRingHom he hc)) := by
  refine fun P hPf hPp => ⟨?_, ?_⟩
  · obtain ⟨S, hS⟩ := hPf.fg_top
    let Q := (ModuleCat.restrictScalars.{u + 1} (cornerRingHom he hc)).obj P
    let S' : Set Q := (S : Set P)
    have key : ∀ y : P, y ∈ Submodule.span he.Corner (S : Set P) →
        (show Q from y) ∈ Submodule.span Λ S' := by
      intro y hy
      induction hy using Submodule.span_induction with
      | mem z hz => exact Submodule.subset_span hz
      | zero => exact Submodule.zero_mem _
      | add z w _ _ hz hw => exact Submodule.add_mem _ hz hw
      | smul c z _ hz =>
        obtain ⟨a, rfl⟩ := cornerRingHom_surjective he hc c
        exact Submodule.smul_mem _ a hz
    exact ⟨⟨S, eq_top_iff.2 fun x _ => key x (hS ▸ Submodule.mem_top)⟩⟩
  · have : Small.{u + 1} he.Corner := small_of_injective (f := fun s : he.Corner => s.1)
      Subtype.val_injective
    have := Functor.preservesEpimorphisms_of_adjunction (cornerAdj.{u + 1} he hc)
    exact (IsProjective.iff_projective _).2 ((cornerRestrictAdj.{u + 1} he hc).map_projective P
      ((IsProjective.iff_projective P).1 hPp))

/-- **Restriction of scalars and the trace of `π_X^*`.** -/
theorem perfectDerivedTrace_canonicalCompactSupportFrobenius_restrictScalars
    (hΦ : PreservesFiniteProjective.{0, u + 1} (ModuleCat.restrictScalars.{u + 1} ρ))
    (K : CochainComplex.Plus (EtaleModules.{u, 0} Λ' X))
    (hK : StacksDraft.Perfect.IsPerfect (DerivedCategory.Plus.ι.obj
      (compactSupportFrobeniusCohomology.{u, 0} Λ' f j kbar K))) :
    ∃ hK' : StacksDraft.Perfect.IsPerfect (DerivedCategory.Plus.ι.obj
        (compactSupportFrobeniusCohomology.{u, 0} Λ f j kbar
          ((etaleModuleRestrictScalars ρ X).mapCochainComplexPlus.obj K))),
      perfectDerivedTrace Λ ⟨_, hK'⟩ (DerivedCategory.Plus.ι.map
          (canonicalCompactSupportFrobenius.{u, 0} Λ f j kbar p q hcard
            ((etaleModuleRestrictScalars ρ X).mapCochainComplexPlus.obj K))) =
        functorTraceMap (ModuleCat.restrictScalars.{u + 1} ρ) (𝟙 _) hΦ
          (perfectDerivedTrace Λ' ⟨_, hK⟩ (DerivedCategory.Plus.ι.map
            (canonicalCompactSupportFrobenius.{u, 0} Λ' f j kbar p q hcard K))) := by
  let E := compactSupportFrobeniusCohomologyRestrictScalarsIso ρ f j kbar K
  have hres : StacksDraft.Perfect.IsPerfect (DerivedCategory.Plus.ι.obj
      ((ModuleCat.restrictScalars.{u + 1} ρ).mapDerivedCategoryPlus.obj
        (compactSupportFrobeniusCohomology.{u, 0} Λ' f j kbar K))) :=
    isPerfect_mapDerivedCategory_of_preservesFiniteProjective _ hΦ hK
  have hK' := StacksDraft.Perfect.isPerfect_of_iso (DerivedCategory.Plus.ι.mapIso E).symm hres
  refine ⟨hK', ?_⟩
  rw [← perfectDerivedTrace_mapDerivedCategoryPlus _ (𝟙 _) hΦ _ hK _ hres]
  refine (perfectDerivedTrace_congr Λ _ ⟨_, hK'⟩ (DerivedCategory.Plus.ι.mapIso E) _ _ ?_).symm
  rw [Stacks.DerivedFunctor.mapDerivedCategoryPlusNatTrans_id_app, Category.id_comp,
    Functor.mapIso_hom]
  exact (DerivedCategory.Plus.ι.map_comp _ _).symm.trans ((congrArg DerivedCategory.Plus.ι.map
    (restrictScalars_canonicalCompactSupportFrobenius ρ f j kbar p q hcard K)).trans
      (DerivedCategory.Plus.ι.map_comp _ _))

end Stacks.EtaleCohomology
