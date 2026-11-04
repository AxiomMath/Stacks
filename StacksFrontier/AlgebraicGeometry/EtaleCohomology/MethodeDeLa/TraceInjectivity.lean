module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.CohomologyPullbackMap
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.IntegralPushforwardExact

/-!
# The méthode de la trace

Let `f : X ⟶ Y` be an integral morphism of schemes and `G` an abelian sheaf on the small étale
site of `Y`. Suppose the unit `G ⟶ f_* f⁻¹ G` of the inverse-image/direct-image adjunction,
followed by some map `τ : f_* f⁻¹ G ⟶ G`, is an isomorphism. Then the pull back map
`Hⁿ(Y, G) ⟶ Hⁿ(X, f⁻¹ G)` on étale cohomology is injective.

For a finite étale `f` of constant degree `d`, `τ` is the trace and the composite is
multiplication by `d`; it is invertible as soon as multiplication by `d` is invertible on `G`, for
instance when `G` is `ℓ`-power torsion and `d` is prime to `ℓ`. This is the "méthode de la
trace" of [Stacks, Section 03SH].

The proof does not use the Leray spectral sequence. Since `f_*` is exact, it acts on `Ext`
groups, and applying it to the pull back of a class `x ∈ Extⁿ(ℤ, G)` and composing with the unit
`ℤ ⟶ f_* f⁻¹ ℤ = f_* ℤ` returns `x` followed by the unit `G ⟶ f_* f⁻¹ G`, by naturality of the
unit. Following this with `τ` gives `x` followed by an isomorphism.

## Main results

* `Stacks.EtaleCohomology.etaleCohomologyPushforward`: the action of `f_*` on étale cohomology,
  `Hⁿ(X, K) ⟶ Hⁿ(Y, f_* K)`, for an integral `f`.
* `Stacks.EtaleCohomology.etaleCohomologyPushforward_etaleCohomologyPullback`: pulling back and
  then pushing forward is composition with the unit.
* `Stacks.EtaleCohomology.injective_etaleCohomologyPullback_of_isIso`: the méthode de la trace.

## References

* [Stacks Project, Section 03SH](https://stacks.math.columbia.edu/tag/03SH)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIntegralHom f]

/-- For an integral morphism `f`, the direct image `f_*` on abelian étale sheaves preserves finite
colimits. -/
instance smallEtalePushforwardAb_preservesFiniteColimits_of_isIntegralHom :
    PreservesFiniteColimits (smallEtalePushforwardAb f) :=
  ((exactFunctor_iff _).mp (smallEtalePushforwardAb_exact_of_isIntegralHom f)).2

/-- For an integral morphism `f`, the direct image `f_*` on abelian étale sheaves preserves finite
limits. -/
instance smallEtalePushforwardAb_preservesFiniteLimits_of_isIntegralHom :
    PreservesFiniteLimits (smallEtalePushforwardAb f) :=
  ((exactFunctor_iff _).mp (smallEtalePushforwardAb_exact_of_isIntegralHom f)).1

/-- **Pushing forward étale cohomology classes along an integral morphism.** The direct image
`f_*` is exact, so it acts on `Ext` groups; composing with the unit `ℤ ⟶ f_* f⁻¹ ℤ ≅ f_* ℤ`
gives a map `Hⁿ(X, K) ⟶ Hⁿ(Y, f_* K)`. -/
def etaleCohomologyPushforward (K : Sheaf (smallEtaleTopology X) Ab.{u + 1}) (p : ℕ) :
    Sheaf.H.{u + 1} K p →+ Sheaf.H.{u + 1} ((smallEtalePushforwardAb f).obj K) p where
  toFun y := (Ext.mk₀ ((smallEtaleAdjunctionAb f).unit.app _ ≫ (smallEtalePushforwardAb f).map
      ((smallEtalePullbackAbConstantIso f).hom.app (AddCommGrpCat.of (ULift ℤ))))).comp
    (y.mapExactFunctor (smallEtalePushforwardAb f)) (zero_add p)
  map_zero' := by simp
  map_add' x y := by simp [Ext.comp_add]

/-- `etaleCohomologyPushforward f K p y` is the image of `y` under `f_*`, precomposed with the unit
`ℤ ⟶ f_* f⁻¹ ℤ ≅ f_* ℤ`. -/
lemma etaleCohomologyPushforward_apply (K : Sheaf (smallEtaleTopology X) Ab.{u + 1}) (p : ℕ)
    (y : Sheaf.H.{u + 1} K p) :
    etaleCohomologyPushforward f K p y =
      (Ext.mk₀ ((smallEtaleAdjunctionAb f).unit.app _ ≫ (smallEtalePushforwardAb f).map
        ((smallEtalePullbackAbConstantIso f).hom.app (AddCommGrpCat.of (ULift ℤ))))).comp
      (y.mapExactFunctor (smallEtalePushforwardAb f)) (zero_add p) := rfl

/-- **Pulling back and then pushing forward is composition with the unit** `G ⟶ f_* f⁻¹ G`. -/
theorem etaleCohomologyPushforward_etaleCohomologyPullback
    (G : Sheaf (smallEtaleTopology Y) Ab.{u + 1}) (p : ℕ) (x : Sheaf.H.{u + 1} G p) :
    etaleCohomologyPushforward f _ p (etaleCohomologyPullback f (𝟙 _) p x) =
      x.comp (Ext.mk₀ ((smallEtaleAdjunctionAb f).unit.app G)) (add_zero p) := by
  have hnat := Stacks.ExtFunctorial.mk₀_comp_mapExactFunctor (smallEtaleAdjunctionAb f).unit
    ((constantSheaf (smallEtaleTopology Y) Ab.{u + 1}).obj (AddCommGrpCat.of (ULift ℤ))) p x
  rw [Stacks.ExtFunctorial.mapExactFunctor_id] at hnat
  rw [etaleCohomologyPushforward_apply, etaleCohomologyPullback_apply, ← hnat,
    ← Stacks.ExtFunctorial.mapExactFunctor_comp_functor]
  simp only [Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀, Ext.comp_mk₀_id]
  rw [← Ext.comp_assoc_of_second_deg_zero, Ext.mk₀_comp_mk₀, Category.assoc,
    ← CategoryTheory.Functor.map_comp, Iso.hom_inv_id_app]
  congr 2

/-- **The méthode de la trace.** If the unit `G ⟶ f_* f⁻¹ G` followed by some `τ` is an
isomorphism, then pulling back `Hⁿ(Y, G) ⟶ Hⁿ(X, f⁻¹ G)` is injective. -/
theorem injective_etaleCohomologyPullback_of_isIso (G : Sheaf (smallEtaleTopology Y) Ab.{u + 1})
    (τ : (smallEtalePushforwardAb f).obj ((smallEtalePullbackAb f).obj G) ⟶ G)
    (hτ : IsIso ((smallEtaleAdjunctionAb f).unit.app G ≫ τ)) (p : ℕ) :
    Function.Injective (etaleCohomologyPullback f (𝟙 ((smallEtalePullbackAb f).obj G)) p) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  have h := congrArg (fun y ↦ (etaleCohomologyPushforward f _ p y).comp (Ext.mk₀ τ) (add_zero p))
    hx
  simp only [etaleCohomologyPushforward_etaleCohomologyPullback, map_zero, Ext.zero_comp,
    Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀] at h
  have h' := congrArg (fun y ↦ y.comp (Ext.mk₀ (inv ((smallEtaleAdjunctionAb f).unit.app G ≫ τ)))
    (add_zero p)) h
  simpa only [Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀, IsIso.hom_inv_id,
    Ext.comp_mk₀_id, Ext.zero_comp] using h'

end Stacks.EtaleCohomology

end
