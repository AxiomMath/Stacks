module

public import StacksFrontier.AlgebraicGeometry.Quot.ProjectiveQuot.UniversalPresentation

/-!
# The cokernel attached to a Grassmannian presentation

Let `m ≥ 0`, `N = freeRank n r m` and let `q : 𝒪_T^{⊕ N} ⟶ ℰ` be a finite locally free quotient
(a `T`-point of `G(k, N)`), with kernel `ℰ' ⊆ 𝒪_T^{⊕ N}`. Through the frame
`𝒪_T^{⊕ N} ≅ π_*(𝒪^{⊕ r}(m))` of `AlgebraicGeometry.ProjectiveQuot.pushforwardTwistFreeModuleIso`,
the inclusion of `ℰ'` corresponds by adjunction to a map
`u_m : π^* ℰ' ⟶ 𝒪^{⊕ r}(m)` of modules on `ℙⁿ_T`, and its cokernel `ℱ^{(m)} = coker(u_m)` is the
twisted module whose flattening cuts `Quot^P` out of the Grassmannian in the proof of Stacks 0DPA
(the map `Ψ` of that proof, twisted by `m`). For the universal quotient `q_G` this is the
universal family; for the presentation of `K ∈ Quot^P(T)` the image of `u_m` is `𝒦(m)`.

## Main definitions

* `AlgebraicGeometry.ProjectiveQuot.presentationTwistMap`: `u_m : π^* ker(q) ⟶ 𝒪^{⊕ r}(m)`.
* `AlgebraicGeometry.ProjectiveQuot.presentationCokernel`: `ℱ^{(m)} = coker(u_m)`, and
  `AlgebraicGeometry.ProjectiveQuot.presentationCokernelπ` its quotient map.

## Main results

* `AlgebraicGeometry.ProjectiveQuot.unit_comp_pushforward_map_presentationTwistMap`: `u_m` is
  adjoint to the inclusion of `ker(q)` followed by the frame.

## References

* [Stacks Project, Tag 0DPA](https://stacks.math.columbia.edu/tag/0DPA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.ProjectiveQuot

variable {n r : ℕ}

/-- **The map `u_m : π^* ker(q) ⟶ 𝒪^{⊕ r}(m)`** attached to a presentation
`q : 𝒪_T^{⊕ N} ⟶ ℰ`, `N = freeRank n r m`: the adjoint of
`ker(q) ⟶ 𝒪_T^{⊕ N} ≅ π_*(𝒪^{⊕ r}(m))`. -/
def presentationTwistMap (m : ℕ) {T : Scheme.{u}} {k : ℕ}
    (q : Grassmannian.QuotientPresentation T k (freeRank.{u} n r m)) :
    (Scheme.Modules.pullback (projectiveSpaceOver n T ↘ T)).obj (kernel q.map) ⟶
      twist (m : ℤ) (freeModule n r T) :=
  ((Scheme.Modules.pullbackPushforwardAdjunction (projectiveSpaceOver n T ↘ T)).homEquiv _ _).symm
    (kernel.ι q.map ≫ (pushforwardTwistFreeModuleIso (n := n) (r := r) T m).inv)

/-- **`ℱ^{(m)} = coker(u_m)`**, the twisted family attached to a presentation. -/
def presentationCokernel (m : ℕ) {T : Scheme.{u}} {k : ℕ}
    (q : Grassmannian.QuotientPresentation T k (freeRank.{u} n r m)) :
    (projectiveSpaceOver n T).Modules :=
  cokernel (presentationTwistMap m q)

/-- The quotient map `𝒪^{⊕ r}(m) ⟶ ℱ^{(m)}`. -/
def presentationCokernelπ (m : ℕ) {T : Scheme.{u}} {k : ℕ}
    (q : Grassmannian.QuotientPresentation T k (freeRank.{u} n r m)) :
    twist (m : ℤ) (freeModule n r T) ⟶ presentationCokernel m q :=
  cokernel.π (presentationTwistMap m q)

/-- The quotient map `𝒪^{⊕ r}(m) ⟶ ℱ^{(m)}` is an epimorphism. -/
instance (m : ℕ) {T : Scheme.{u}} {k : ℕ}
    (q : Grassmannian.QuotientPresentation T k (freeRank.{u} n r m)) :
    Epi (presentationCokernelπ m q) :=
  inferInstanceAs (Epi (cokernel.π (presentationTwistMap m q)))

/-- **`u_m` is adjoint to `ker(q) ⟶ 𝒪_T^{⊕ N} ≅ π_*(𝒪^{⊕ r}(m))`.** -/
theorem unit_comp_pushforward_map_presentationTwistMap (m : ℕ) {T : Scheme.{u}} {k : ℕ}
    (q : Grassmannian.QuotientPresentation T k (freeRank.{u} n r m)) :
    (Scheme.Modules.pullbackPushforwardAdjunction (projectiveSpaceOver n T ↘ T)).unit.app
        (kernel q.map) ≫
      (Scheme.Modules.pushforward (projectiveSpaceOver n T ↘ T)).map (presentationTwistMap m q) =
      kernel.ι q.map ≫ (pushforwardTwistFreeModuleIso (n := n) (r := r) T m).inv :=
  ((Scheme.Modules.pullbackPushforwardAdjunction (projectiveSpaceOver n T ↘ T)).homEquiv_unit
      _ _ _).symm.trans
    (((Scheme.Modules.pullbackPushforwardAdjunction (projectiveSpaceOver n T ↘ T)).homEquiv
      _ _).apply_symm_apply _)

end AlgebraicGeometry.ProjectiveQuot

end
