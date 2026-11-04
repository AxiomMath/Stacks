module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BoundedSmallEtaleSiteComparison
public import StacksFrontier.Algebra.Homology.DerivedCategory.TriangleMorphismHomology
public import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedSquareCommShift

/-!
# Isomorphisms off the closed points are detected by hypercohomology

The last paragraph of the proof of [Stacks, Tag 0F1H] reads: *"Choose a distinguished triangle
`q⁻¹Rj_*𝓕 ⟶ Rh_*p⁻¹𝓕 ⟶ Q ⟶ (q⁻¹Rj_*𝓕)[1]`. Since `Q` is supported in closed points we see that
it suffices to prove `H^i(X ×_K Y, Q) = 0` for all `i`, see Lemma 0F1G. Thus it suffices to prove
that `q⁻¹Rj_*𝓕 ⟶ Rh_*p⁻¹𝓕` induces an isomorphism on cohomology."*

This file proves that step for an arbitrary morphism `φ : A ⟶ B` of the unbounded derived category
of abelian sheaves on the small étale site of a scheme `Z` of finite type over a separably closed
field: if `φ` induces isomorphisms on the stalks of all cohomology sheaves at the geometric points
lying over non-closed points of `Z`, then `φ` is an isomorphism exactly when it induces
isomorphisms on all hypercohomology groups `H^i(Z_étale, -)`.

## Main results

* `Stacks.EtaleCohomology.isZero_map_homology_obj₃` — for an exact functor `Φ` on the heart and a
  distinguished triangle `A ⟶ B ⟶ Q ⟶ A[1]`, `Φ(H^i(Q))` vanishes once `Φ(H^i(A) ⟶ H^i(B))` is
  surjective and `Φ(H^{i+1}(A) ⟶ H^{i+1}(B))` is injective.
* `Stacks.EtaleCohomology.isIso_iff_forall_isIso_hypercohomology_of_closedPointSupport` — the step
  of the source.

## Implementation notes

`Stacks.EtaleCohomology.smallEtaleDerivedGlobalSections`
(`StacksFrontier/AlgebraicGeometry/EtaleCohomology/DerivedEtale.lean:196`) is formed for the standard
model of the derived categories; that fixes the model here.

## References

* [Stacks Project, Tag 0F1H](https://stacks.math.columbia.edu/tag/0F1H)
* [Stacks Project, Tag 0F1G](https://stacks.math.columbia.edu/tag/0F1G)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Pretriangulated
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology

section Triangle

variable {C D : Type*} [Category* C] [Abelian C] [HasDerivedCategory C] [Category* D] [Abelian D]
  (Φ : C ⥤ D) [Φ.Additive] [Φ.PreservesHomology]

/-- **The third vertex of a triangle under an exact functor of the cohomology.** For an exact
functor `Φ` and a distinguished triangle `A ⟶ B ⟶ Q ⟶ A[1]` of `D(C)`, the object `Φ(H^i(Q))`
vanishes as soon as `Φ(H^i(A) ⟶ H^i(B))` is an epimorphism and `Φ(H^{i+1}(A) ⟶ H^{i+1}(B))` is a
monomorphism. -/
theorem isZero_map_homology_obj₃ {T : Triangle (DerivedCategory C)} (hT : T ∈ distTriang _)
    (n : ℤ) (h₁ : Epi (Φ.map ((DerivedCategory.homologyFunctor C n).map T.mor₁)))
    (h₂ : Mono (Φ.map ((DerivedCategory.homologyFunctor C (n + 1)).map T.mor₁))) :
    IsZero (Φ.obj ((DerivedCategory.homologyFunctor C n).obj T.obj₃)) := by
  have e₂ := ((DerivedCategory.homologyFunctor C 0).homologySequence_exact₂ T hT n).map Φ
  have e₃ := ((DerivedCategory.homologyFunctor C 0).homologySequence_exact₃ T hT n (n + 1)
    rfl).map Φ
  have e₁ := ((DerivedCategory.homologyFunctor C 0).homologySequence_exact₁ T hT n (n + 1)
    rfl).map Φ
  exact e₃.isZero_X₂ (e₂.epi_f_iff.1 h₁) (e₁.mono_g_iff.1 h₂)

end Triangle

-- `Stacks.EtaleCohomology.smallEtaleDerivedGlobalSections`
-- (`StacksFrontier/AlgebraicGeometry/EtaleCohomology/DerivedEtale.lean:196`) is formed for the
-- standard model of the derived categories.
attribute [local instance] HasDerivedCategory.standard
attribute [local instance] isGrothendieckAbelian_sheaf_smallEtale_objectUniverse

/-- **Isomorphisms off the closed points are detected by hypercohomology** (the step of the proof
of [Stacks, Tag 0F1H] that applies [Stacks, Tag 0F1G]). Let `K` be a separably closed field, `Z` a
scheme of finite type over `K` and `φ : A ⟶ B` a morphism of the unbounded derived category of
abelian sheaves on `Z_étale` which induces isomorphisms on the stalks of all cohomology sheaves at
the geometric points of `Z` lying over non-closed points. Then `φ` is an isomorphism if and only if
it induces isomorphisms `H^i(Z_étale, A) ⟶ H^i(Z_étale, B)` for all `i`. -/
theorem isIso_iff_forall_isIso_hypercohomology_of_closedPointSupport
    (K : Type u) [Field K] [IsSepClosed K] {Z : Scheme.{u}} (f : Z ⟶ Spec (.of K))
    [LocallyOfFiniteType f] [QuasiCompact f]
    {A B : DerivedCategory (Sheaf Z.smallEtaleTopology Ab.{u + 1})} (φ : A ⟶ B)
    (hφ : ∀ (p : GeometricPoint Z) (i : ℤ), ¬ IsClosed ({p.hom default} : Set Z) →
      IsIso ((Scheme.pointSmallEtale p.hom).sheafFiber.map
        ((DerivedCategory.homologyFunctor (Sheaf Z.smallEtaleTopology Ab.{u + 1}) i).map φ))) :
    IsIso φ ↔ ∀ i : ℤ, IsIso ((DerivedCategory.homologyFunctor Ab.{u + 1} i).map
      ((smallEtaleDerivedGlobalSections Z).map φ)) := by
  obtain ⟨Q, g, δ, hT⟩ := distinguished_cocone_triangle φ
  let T := Triangle.mk φ g δ
  let RΓ := smallEtaleDerivedGlobalSections Z
  have hRT : RΓ.mapTriangle.obj T ∈ distTriang _ := RΓ.map_distinguished _ hT
  rw [show IsIso φ ↔ IsIso T.mor₁ from Iff.rfl, ← Triangle.isZero₃_iff_isIso₁ T hT]
  show IsZero Q ↔ _
  rw [SmallEtale.isZero_iff_forall_isZero_hypercohomology_of_closedPointSupport Z K f Q
    (fun p i hp => isZero_map_homology_obj₃ _ hT i (@IsIso.epi_of_iso _ _ _ _ _ (hφ p i hp))
      (@IsIso.mono_of_iso _ _ _ _ _ (hφ p (i + 1) hp)))]
  constructor
  · intro h i
    have h₁ := DerivedCategory.epi_homologyFunctor_map_mor₁_of_isZero hRT i (h i)
    have h₂ := DerivedCategory.mono_homologyFunctor_map_mor₁_of_isZero hRT (i - 1) (h (i - 1))
    rw [sub_add_cancel] at h₂
    exact isIso_of_mono_of_epi ((DerivedCategory.homologyFunctor Ab.{u + 1} i).map
      (RΓ.mapTriangle.obj T).mor₁)
  · intro h i
    exact DerivedCategory.isZero_homologyFunctor_obj₃ hRT i
      (@IsIso.epi_of_iso _ _ _ _ _ (h i)) (@IsIso.mono_of_iso _ _ _ _ _ (h (i + 1)))

end Stacks.EtaleCohomology

end
