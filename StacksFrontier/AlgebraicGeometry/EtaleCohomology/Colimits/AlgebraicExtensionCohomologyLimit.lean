module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.FieldExtensionCohomologyLimit
public import Mathlib.FieldTheory.IntermediateField.Algebraic

/-!
# Cohomology classes dying after an algebraic field extension die over a finite subextension

Let `k'/k` be an algebraic field extension, `X` a quasi-compact quasi-separated scheme over `k`
and `G` an abelian sheaf on `X_étale`. A class of `H^q(X, G)` which vanishes on `X_{k'}` vanishes
on `X_E` for some finite subextension `E/k` of `k'/k`. This is the injectivity half of
[Stacks, Tag 03Q6] for the system of finite subextensions: by
`Stacks.EtaleCohomology.LimitExt.exists_fg_restriction_eq_zero` the class dies over a finitely
generated `k`-subalgebra `A` of `k'`, and in an algebraic extension such a subalgebra is a field
(Stacks 0BID) which is finite over `k`.

## Main results

* `Stacks.EtaleCohomology.LimitExt.exists_finiteDimensional_restriction_eq_zero`.

## References

* [Stacks Project, Tag 03Q6](https://stacks.math.columbia.edu/tag/03Q6)
* [Stacks Project, Tag 0BID](https://stacks.math.columbia.edu/tag/0BID)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.EtaleCohomology.LimitExt

attribute [local instance] isGrothendieckAbelian_sheaf_smallEtale_objectUniverse

/-- **Classes dying after an algebraic field extension die over a finite subextension**
(the injectivity half of Stacks 03Q6 for the finite subextensions of an algebraic extension).
Let `k'/k` be an algebraic field extension, `X` a quasi-compact quasi-separated scheme over `k`,
`G` an abelian sheaf on `X_étale` and `c ∈ H^q(X, G)`. If `c` restricts to zero on `X_{k'}`, then
it restricts to zero on `X ×_k Spec E` for some intermediate field `E` of `k'/k` finite over
`k`. -/
theorem exists_finiteDimensional_restriction_eq_zero (k k' : Type u) [Field k] [Field k']
    [Algebra k k'] [Algebra.IsAlgebraic k k'] {X : Scheme.{u}} [CompactSpace X]
    [QuasiSeparatedSpace X] (π : X ⟶ Spec (.of k))
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ) (c : Sheaf.H.{u + 1} G q)
    (hc : etaleCohomologyRestrictionMap.{u, 0, u + 1} (scalarExtensionFst k k' π) G q c = 0) :
    ∃ E : IntermediateField k k', FiniteDimensional k E ∧
      etaleCohomologyRestrictionMap.{u, 0, u + 1}
        (pullback.fst π (Spec.map (CommRingCat.ofHom (algebraMap k E)))) G q c = 0 := by
  obtain ⟨A, hA, hcA⟩ := exists_fg_restriction_eq_zero k k' π G q c hc
  let E : IntermediateField k k' := A.toIntermediateField' (Subalgebra.isField_of_algebraic A)
  let φ : E ≃ₐ[k] A :=
    Subalgebra.equivOfEq E.toSubalgebra A (toSubalgebra_toIntermediateField' _ _)
  have hfin : FiniteDimensional k E := by
    have : Algebra.FiniteType k A := (Subalgebra.fg_iff_finiteType A).1 hA
    have : Algebra.FiniteType k E := Algebra.FiniteType.equiv inferInstance φ.symm
    exact Algebra.IsIntegral.finite
  refine ⟨E, hfin, ?_⟩
  let ψ : Spec (.of A) ⟶ Spec (.of E) :=
    (Scheme.Spec.mapIso φ.toRingEquiv.toCommRingCatIso.op).hom
  have hψ : ψ ≫ Spec.map (CommRingCat.ofHom (algebraMap k E)) =
      Spec.map (CommRingCat.ofHom (algebraMap k A)) := by
    change Spec.map (CommRingCat.ofHom φ.toRingEquiv.toRingHom) ≫ _ = _
    rw [← Spec.map_comp]
    congr 1
  let ι : pullback π (Spec.map (CommRingCat.ofHom (algebraMap k A))) ⟶
      pullback π (Spec.map (CommRingCat.ofHom (algebraMap k E))) :=
    pullback.map _ _ _ _ (𝟙 X) ψ (𝟙 _) (by simp) (by simp [hψ])
  have : IsIso ι := by exact pullback.map_isIso _ _ _ _ _ _ _ _ _
  exact (restriction_eq_zero_of_comp_isIso ι _ _ (by simp [ι]) G q c).1 hcA

end Stacks.EtaleCohomology.LimitExt

end
