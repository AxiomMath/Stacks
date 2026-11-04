module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CompactSupportRestrictScalarsNatural
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CompactSupportRestrictScalarsTrace
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.ShortExactTrace
public import StacksFrontier.CategoryTheory.FilteredDerived.Perfectness.DerivedFunctorTrace

/-!
# The trace of `π_X^*` twisted by an endomorphism of restriction of scalars

Let `ρ : Λ →+* Λ'` be a ring map along which restriction of scalars preserves finite projective
modules, `θ` a natural endomorphism of restriction of scalars of modules along `ρ` (for instance
multiplication by a central element of `Λ'`) and `Θ` its sectionwise action on sheaves. For a
bounded below complex `K` of sheaves of `Λ'`-modules with `RΓ_c(X_k̄, K)` perfect over `Λ'`, the
complex `RΓ_c(X_k̄, K|_Λ)` is perfect over `Λ` and

`Tr_Λ(Θ_* ∘ π_X^* | RΓ_c(X_k̄, K|_Λ)) = θ♮(Tr_{Λ'}(π_X^* | RΓ_c(X_k̄, K)))`,

`θ♮ : Λ'^♮ → Λ^♮` being the map of `CategoryTheory.FilteredDerived.functorTraceMap`. For `θ`
multiplication by `c ∈ Λ'` and `Λ'` commutative, finite free over `Λ`, `θ♮(t) = Tr_{Λ'/Λ}(c t)`:
this is how the trace of `π_X^*` twisted by the action of a coefficient ring is read off the trace
over the coefficient ring.

The statements consume objects defined in the standard model `HasDerivedCategory.standard` of the
derived category (`perfectDerivedTrace`, `canonicalCompactSupportFrobenius`), which is therefore a
local instance here.

## Main results

* `perfectDerivedTrace_canonicalCompactSupportFrobenius_comp_restrictScalarsEndo`: the trace
  formula above.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.FilteredDerived AlgebraicGeometry

universe u

namespace Stacks.EtaleCohomology

section Standard

attribute [local instance] HasDerivedCategory.standard

variable {Λ Λ' : Type} [Ring Λ] [Ring Λ'] (ρ : Λ →+* Λ')
  (θ : ModuleCat.restrictScalars.{u + 1} ρ ⟶ ModuleCat.restrictScalars.{u + 1} ρ)
  {k : Type u} [Field k] [Fintype k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
  (j : CompactificationOf (Over.mk f)) (kbar : Type u) [Field kbar] [Algebra k kbar]
  (p q : ℕ) [Fact p.Prime] [CharP k p] (hcard : Fintype.card k = p ^ q)

/-- A chase through three commutative squares: if `θ` commutes with `r`, `E` carries `θ` to `Θ`
and `r` to `π`, then `E` carries `θ ≫ r` to `π ≫ Θ`. -/
theorem comp_eq_of_comm_squares' {D : Type*} [Category* D] {A B : D} (E : A ⟶ B)
    (θ r : A ⟶ A) (Θ π : B ⟶ B) (h₁ : θ ≫ r = r ≫ θ) (h₂ : θ ≫ E = E ≫ Θ)
    (h₃ : r ≫ E = E ≫ π) : (θ ≫ r) ≫ E = E ≫ π ≫ Θ := by
  rw [h₁, Category.assoc, h₂, reassoc_of% h₃]

/-- **The trace of `π_X^*` twisted by `Θ`, after restriction of scalars**:
`Tr_Λ(Θ_* ∘ π_X^* | RΓ_c(X_k̄, K|_Λ)) = θ♮(Tr_{Λ'}(π_X^* | RΓ_c(X_k̄, K)))`. -/
theorem perfectDerivedTrace_canonicalCompactSupportFrobenius_comp_restrictScalarsEndo
    (hΦ : PreservesFiniteProjective.{0, u + 1} (ModuleCat.restrictScalars.{u + 1} ρ))
    (K : CochainComplex.Plus (EtaleModules.{u, 0} Λ' X))
    (hK : StacksDraft.Perfect.IsPerfect (DerivedCategory.Plus.ι.obj
      (compactSupportFrobeniusCohomology.{u, 0} Λ' f j kbar K))) :
    ∃ hK' : StacksDraft.Perfect.IsPerfect (DerivedCategory.Plus.ι.obj
        (compactSupportFrobeniusCohomology.{u, 0} Λ f j kbar
          ((etaleModuleRestrictScalars ρ X).mapCochainComplexPlus.obj K))),
      perfectDerivedTrace Λ ⟨_, hK'⟩ (DerivedCategory.Plus.ι.map
          (canonicalCompactSupportFrobenius.{u, 0} Λ f j kbar p q hcard
            ((etaleModuleRestrictScalars ρ X).mapCochainComplexPlus.obj K) ≫
          (compactSupportFrobeniusFunctor.{u, 0} Λ f j kbar).map
            (etaleModuleRestrictScalarsComplexEndo ρ θ K))) =
        functorTraceMap (ModuleCat.restrictScalars.{u + 1} ρ) θ hΦ
          (perfectDerivedTrace Λ' ⟨_, hK⟩ (DerivedCategory.Plus.ι.map
            (canonicalCompactSupportFrobenius.{u, 0} Λ' f j kbar p q hcard K))) := by
  let E := compactSupportFrobeniusCohomologyRestrictScalarsIso ρ f j kbar K
  have hres : StacksDraft.Perfect.IsPerfect (DerivedCategory.Plus.ι.obj
      ((ModuleCat.restrictScalars.{u + 1} ρ).mapDerivedCategoryPlus.obj
        (compactSupportFrobeniusCohomology.{u, 0} Λ' f j kbar K))) :=
    isPerfect_mapDerivedCategory_of_preservesFiniteProjective _ hΦ hK
  have hY : StacksDraft.Perfect.IsPerfect (DerivedCategory.Plus.ι.obj
      (compactSupportFrobeniusCohomology.{u, 0} Λ f j kbar
        ((etaleModuleRestrictScalars ρ X).mapCochainComplexPlus.obj K))) :=
    StacksDraft.Perfect.isPerfect_of_iso (DerivedCategory.Plus.ι.mapIso E).symm hres
  refine ⟨hY, ?_⟩
  have hθπ := (Stacks.DerivedFunctor.mapDerivedCategoryPlusNatTrans θ).naturality
    (canonicalCompactSupportFrobenius.{u, 0} Λ' f j kbar p q hcard K)
  have hθ := compactSupportFrobeniusCohomologyRestrictScalarsIso_naturality ρ θ f j kbar K
  have hπ := restrictScalars_canonicalCompactSupportFrobenius ρ f j kbar p q hcard K
  have hconj : DerivedCategory.Plus.ι.map
        ((Stacks.DerivedFunctor.mapDerivedCategoryPlusNatTrans θ).app
            (compactSupportFrobeniusCohomology.{u, 0} Λ' f j kbar K) ≫
          (ModuleCat.restrictScalars.{u + 1} ρ).mapDerivedCategoryPlus.map
            (canonicalCompactSupportFrobenius.{u, 0} Λ' f j kbar p q hcard K)) ≫
        (DerivedCategory.Plus.ι.mapIso E).hom =
      (DerivedCategory.Plus.ι.mapIso E).hom ≫ DerivedCategory.Plus.ι.map
        (canonicalCompactSupportFrobenius.{u, 0} Λ f j kbar p q hcard
            ((etaleModuleRestrictScalars ρ X).mapCochainComplexPlus.obj K) ≫
          (compactSupportFrobeniusFunctor.{u, 0} Λ f j kbar).map
            (etaleModuleRestrictScalarsComplexEndo ρ θ K)) := by
    simp only [Functor.mapIso_hom, ← Functor.map_comp]
    exact congrArg _ (comp_eq_of_comm_squares' _ _ _ _ _ hθπ.symm hθ hπ)
  rw [← perfectDerivedTrace_mapDerivedCategoryPlus _ θ hΦ _ hK _ hres]
  exact (perfectDerivedTrace_congr _ _ ⟨_, hY⟩ (DerivedCategory.Plus.ι.mapIso E) _ _ hconj).symm

end Standard

end Stacks.EtaleCohomology

end
