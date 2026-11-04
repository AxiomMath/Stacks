module

public import StacksFrontier.AlgebraicGeometry.DeRham.HodgeWeil.Kunneth
public import StacksFrontier.AlgebraicGeometry.WeilDeRham.FieldBaseChange

/-!
# Hodge cohomology along an extension of the base field: the comparison map

Let `k ⟶ K` be an extension of fields and `X` a smooth projective scheme over `k`, with base change
`X_K = X ×_{Spec k} Spec K` and projection `pr : X_K ⟶ X`. Pullback along the cartesian square
`(pr, Spec K ⟶ Spec k)` (Section 50.5, Tag 0FM4) gives the base change map
`pr^* : H^q(X, Ω^p_{X/k}) ⟶ H^q(X_K, Ω^p_{X_K/K})`, which is semilinear along `k ⟶ K`, and
hence its `K`-linear extension `K ⊗_k H^q(X, Ω^p_{X/k}) ⟶ H^q(X_K, Ω^p_{X_K/K})`.

## Main definitions

* `Stacks.HodgeWeil.hodgeBaseChange`: the base change map `pr^*` on `H^q(X, Ω^p_{X/k})`.
* `Stacks.HodgeWeil.hodgeBaseChangeLinear`: its `K`-linear extension
  `K ⊗_k H^q(X, Ω^p_{X/k}) ⟶ H^q(X_K, Ω^p_{X_K/K})`, `c ⊗ x ↦ c · pr^* x`.

## Main results

* `Stacks.HodgeWeil.hodgeBaseRingHom_comp_hodgeScalarsOverField`: the ring map of the square is
  compatible with the scalars `k ⟶ K`.
* `Stacks.HodgeWeil.hodgeBaseChange_smul`: the base change map is semilinear along `k ⟶ K`.

## References

* [Stacks Project, Tag 0FWE](https://stacks.math.columbia.edu/tag/0FWE)
* [Stacks Project, Tag 0FVT](https://stacks.math.columbia.edu/tag/0FVT)
* [Stacks Project, Tag 0FM4](https://stacks.math.columbia.edu/tag/0FM4)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Opposite Stacks.WeilCohomology
open Stacks.WeilDeRham
open Stacks.WeilCohomology.SmoothProjectiveScheme hiding specStructure
open AlgebraicGeometry.SheafOfModules (hodgeCohomologyComponent)
open scoped TensorProduct

universe u

namespace Stacks.HodgeWeil

attribute [local instance] RestrictScalars.moduleOrig

variable {k : Type u} [Field k]

variable (K : Type u) [Field K] [Algebra k K] (X : (SmoothProjectiveScheme k).FullSubcategory)

/-- **The ring map of the base change square is compatible with the scalars**:
`k ⟶ Γ(X, p⁻¹𝒪_{Spec k}) ⟶ Γ(X_K, p_K⁻¹𝒪_{Spec K})` is `k ⟶ K ⟶ Γ(X_K, p_K⁻¹𝒪_{Spec K})`. -/
theorem hodgeBaseRingHom_comp_hodgeScalarsOverField :
    (hodgeBaseRingHom (fieldBaseChangeProj X) ((fieldBaseChange k K).obj X).obj.hom X.obj.hom
        (specStructure k K) (fieldBaseChangeProj_comp_hom X)).comp
        (hodgeScalarsOverField X.obj.hom) =
      (hodgeScalarsOverField ((fieldBaseChange k K).obj X).obj.hom).comp (algebraMap k K) := by
  ext c
  have h := congrArg (fun φ => φ (specScalars k c))
    (hodgeBaseRingHom_comp_inverseImageGlobalSections (fieldBaseChangeProj X)
      ((fieldBaseChange k K).obj X).obj.hom X.obj.hom (specStructure k K)
      (fieldBaseChangeProj_comp_hom X))
  have h2 := congrArg (fun φ => φ.hom c)
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap k K)))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h h2
  exact h.trans (congrArg _ h2.symm)

/-- **The base change map `pr^* : H^q(X, Ω^p_{X/k}) ⟶ H^q(X_K, Ω^p_{X_K/K})`**: pullback on Hodge
cohomology along the cartesian square `(pr, Spec K ⟶ Spec k)`. -/
abbrev hodgeBaseChange (p : ℕ) (q : ℤ) :
    hodgeCohomologyComponent (formsAlgebras X.obj.hom) p q →+
      hodgeCohomologyComponent (formsAlgebras ((fieldBaseChange k K).obj X).obj.hom) p q :=
  (hodgePullback (fieldBaseChangeProj X) ((fieldBaseChange k K).obj X).obj.hom X.obj.hom
    (specStructure k K) (fieldBaseChangeProj_comp_hom X) p q).toAddMonoidHom

/-- **The base change map is semilinear along `k ⟶ K`.** -/
theorem hodgeBaseChange_smul (p : ℕ) (q : ℤ) (c : k)
    (x : hodgeCohomologyComponent (formsAlgebras X.obj.hom) p q) :
    hodgeBaseChange K X p q (c • x) = algebraMap k K c • hodgeBaseChange K X p q x := by
  have h := (hodgePullback (fieldBaseChangeProj X) ((fieldBaseChange k K).obj X).obj.hom
    X.obj.hom (specStructure k K) (fieldBaseChangeProj_comp_hom X) p q).map_smulₛₗ
    (hodgeScalarsOverField X.obj.hom c) x
  rw [← RingHom.comp_apply, hodgeBaseRingHom_comp_hodgeScalarsOverField, RingHom.comp_apply] at h
  exact h

/-- The base change map as a `k`-linear map into `H^q(X_K, Ω^p_{X_K/K})` with scalars restricted
to `k`. -/
def hodgeBaseChangeRestrict (p : ℕ) (q : ℤ) :
    hodgeCohomologyComponent (formsAlgebras X.obj.hom) p q →ₗ[k]
      RestrictScalars k K
        (hodgeCohomologyComponent (formsAlgebras ((fieldBaseChange k K).obj X).obj.hom) p q) where
  toFun x := (RestrictScalars.addEquiv k K _).symm (hodgeBaseChange K X p q x)
  map_add' x y := by rw [map_add, map_add]
  map_smul' c x := by
    rw [hodgeBaseChange_smul, RingHom.id_apply, RestrictScalars.smul_def]
    rfl

/-- **The comparison map `K ⊗_k H^q(X, Ω^p_{X/k}) ⟶ H^q(X_K, Ω^p_{X_K/K})`**, `c ⊗ x ↦ c · pr^* x`,
the `K`-linear extension of the base change map. -/
def hodgeBaseChangeLinear (p : ℕ) (q : ℤ) :
    K ⊗[k] hodgeCohomologyComponent (formsAlgebras X.obj.hom) p q →ₗ[K]
      hodgeCohomologyComponent (formsAlgebras ((fieldBaseChange k K).obj X).obj.hom) p q where
  toFun t := RestrictScalars.addEquiv k K _ ((hodgeBaseChangeRestrict K X p q).liftBaseChange K t)
  map_add' s t := by rw [map_add, map_add]
  map_smul' c t := by
    rw [map_smul]
    rfl

/-- The comparison map sends `c ⊗ x` to `c` times the base change of `x`. -/
theorem hodgeBaseChangeLinear_tmul (p : ℕ) (q : ℤ) (c : K)
    (x : hodgeCohomologyComponent (formsAlgebras X.obj.hom) p q) :
    hodgeBaseChangeLinear K X p q (c ⊗ₜ x) = c • hodgeBaseChange K X p q x :=
  rfl

end Stacks.HodgeWeil

end
