module

public import StacksFrontier.AlgebraicGeometry.Curves.LinearSystemScheme.ClosedPoints
public import StacksFrontier.AlgebraicGeometry.Curves.LinearSystemScheme.CanonicalBasis
public import StacksFrontier.AlgebraicGeometry.Variety.Projective.AvoidingLines
public import Mathlib.AlgebraicGeometry.AlgClosed.Basic
public import StacksCore.Tactic.StacksAttribute

/-!
# The complete linear system as a scheme ([Stacks, Tag 0CCT])

Let `X` be a smooth projective curve over an algebraically closed field `k` and `D ⊆ X` an
effective Cartier divisor of degree `d`, with complete linear system `|D|`
(`Stacks.Divisors.completeLinearSystem`). The fibre of the Abel map
`γ_d : Hilb^d_{X/k} → Pic^d_{X/k}` over the point of `𝒪_X(D)` is the functor
`Stacks.LinearSystemScheme.abelFibre` of degree-`d` families `Z ⊆ X_T` with `𝒪_{X_T}(Z)` locally
isomorphic to `pr_X^* 𝒪_X(D)`. This file states the two assertions of Tag 0CCT about it:

* it is represented by the projective space `𝐏(H⁰(X, 𝒪_X(D))^∨)` of [Stacks, Example 0FCY], and
  the closed points of that scheme are the members of `|D|`, which gives `|D|` its natural scheme
  structure;
* that scheme is isomorphic over `k` to `ℙ^m_k` with `m + 1 = h⁰(𝒪_X(D))`.

## Main results

* `Stacks.LinearSystemScheme.completeLinearSystem_eq_closedPoints_abelFibre`.
* `Stacks.LinearSystemScheme.completeLinearSystem_iso_projectiveSpace`.

## References

* [Stacks Project, Tag 0CCT](https://stacks.math.columbia.edu/tag/0CCT)
* [Stacks Project, Example 0FCY](https://stacks.math.columbia.edu/tag/0FCY)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Stacks.Hilbert

universe u

namespace Stacks.LinearSystemScheme

variable (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
  [IsAlgClosed k] [IsCurve k f] [IsProjectiveVariety k f] [Smooth f]
  (D : X.IdealSheafData) [Stacks.Divisors.IsEffectiveCartierDivisor D]

/-- The space of global sections `H⁰(X, 𝒪_X(D))` is finite-dimensional over `k`. -/
instance finiteDimensional_globalSections :
    FiniteDimensional k (cohomologyOverField k f (Stacks.Divisors.modulesInvertibleSheaf D) 0) :=
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : (Stacks.Divisors.modulesInvertibleSheaf D).IsCoherent :=
    Stacks.AlgebraicGeometry.CoherenceCriteria.isCoherent_of_isInvertible X _
  finiteDimensional_cohomologyOverField_of_isProper k f _ 0

/-- The dual `H⁰(X, 𝒪_X(D))^∨` of the space of global sections is nontrivial. -/
instance nontrivial_dual_globalSections :
    Nontrivial (Module.Dual k
      (cohomologyOverField k f (Stacks.Divisors.modulesInvertibleSheaf D) 0)) := by
  rw [← Module.finrank_pos_iff (R := k), Subspace.dual_finrank_eq]
  exact one_le_finrank_globalSections k f D

/-- The structure morphism `𝐏(H⁰(X, 𝒪_X(D))^∨) ⟶ Spec k` is locally of finite type. -/
instance locallyOfFiniteType_linearSystemScheme :
    LocallyOfFiniteType (projectiveSpaceOfModuleToSpec k (Module.Dual k
      (cohomologyOverField k f (Stacks.Divisors.modulesInvertibleSheaf D) 0))) :=
  have := AlgebraicGeometry.ProjectiveSpaceOfModule.isProper_projectiveSpaceOfModuleToSpec k
    (Module.Dual k (cohomologyOverField k f (Stacks.Divisors.modulesInvertibleSheaf D) 0))
  inferInstance

/-- `H⁰(X, 𝒪_X(D))^∨`. -/
abbrev dualSections : Type u :=
  Module.Dual k (cohomologyOverField k f (Stacks.Divisors.modulesInvertibleSheaf D) 0)

/-- `𝐏(H⁰(X, 𝒪_X(D))^∨)`, the representing scheme of the fibre of the Abel map. -/
abbrev linearSystemScheme : Scheme.{u} :=
  projectiveSpaceOfModule k (dualSections k f D)

omit [IsAlgClosed k] [IsCurve k f] [IsProjectiveVariety k f] [Smooth f]
  [Divisors.IsEffectiveCartierDivisor D] in
/-- The structure morphism of `linearSystemScheme k f D` over `Spec k` is
`projectiveSpaceOfModuleToSpec k (dualSections k f D)`. -/
lemma over_linearSystemScheme :
    linearSystemScheme k f D ↘ Spec (.of k) =
      projectiveSpaceOfModuleToSpec k (dualSections k f D) := rfl

omit [IsAlgClosed k] [IsCurve k f] [Smooth f] in
/-- For a nonzero `s ∈ H⁰(X, 𝒪_X(D))`, the evaluation functional at `s` on `H⁰(X, 𝒪_X(D))^∨` is
nonzero. -/
theorem eval_ne_zero
    {s : cohomologyOverField k f (Stacks.Divisors.modulesInvertibleSheaf D) 0} (hs : s ≠ 0) :
    Module.Dual.eval k _ s ≠ 0 :=
  fun h => hs ((Module.eval_apply_eq_zero_iff k s).mp h)

/-- The `k`-point of `𝐏(H⁰(X, 𝒪_X(D))^∨)` at the closed point cut out by evaluation at a nonzero
`s ∈ H⁰(X, 𝒪_X(D))`. -/
def sectionPoint {s : cohomologyOverField k f (Stacks.Divisors.modulesInvertibleSheaf D) 0}
    (hs : s ≠ 0) : fieldPoint k ⟶ (linearSystemScheme k f D).asOver (Spec (.of k)) :=
  Over.homMk (@pointOfClosedPoint _ _ _ _ (projectiveSpaceOfModuleToSpec k (dualSections k f D))
    (locallyOfFiniteType_linearSystemScheme k f D)
    (ProjectiveSpaceOfModule.linearFunctionalPoint k _ (Module.Dual.eval k _ s)
      (eval_ne_zero k f D hs))
    (ProjectiveSpaceOfModule.linearFunctionalPoint_isClosed k _ _ (eval_ne_zero k f D hs)))
    (@pointOfClosedPoint_comp _ _ _ _ _ (locallyOfFiniteType_linearSystemScheme k f D) _ _)

/-- **The canonical representability bijection.** The fibre of the Abel map over `𝒪_X(D)` is
represented by `𝐏(H⁰(X, 𝒪_X(D))^∨)` through the bijection that sends the closed point cut out by
evaluation at a nonzero `s ∈ H⁰(X, 𝒪_X(D))` to the family over `Spec k` whose image in `X` is
the zero scheme `Z(s)`. -/
theorem exists_abelFibre_equiv_projectiveSpace_canonical {d : ℕ}
    (hd : invertibleCurveDegree k f (topologicalKrullDim_le_one k f)
      (Stacks.Divisors.modulesInvertibleSheaf D) = d) :
    ∃ e : ∀ T : Over (Spec (.of k)),
        (T ⟶ (linearSystemScheme k f D).asOver (Spec (.of k))) ≃ abelFibre f D d T,
      (∀ (T T' : Over (Spec (.of k))) (h : T' ⟶ T)
          (g : T ⟶ (linearSystemScheme k f D).asOver (Spec (.of k))),
        (e T' (h ≫ g)).1.ideal = (e T g).1.ideal.comap (familyBaseChangeMap (curveOver f) h)) ∧
      ∀ (s : cohomologyOverField k f (Stacks.Divisors.modulesInvertibleSheaf D) 0) (hs : s ≠ 0),
        (e (fieldPoint k) (sectionPoint k f D hs)).1.ideal.comap
            (inv (pullback.fst f (𝟙 (Spec (.of k))))) =
          zeroScheme X (Stacks.Divisors.modulesInvertibleSheaf D)
            (sectionOf k f (Stacks.Divisors.modulesInvertibleSheaf D) s) := by
  set H0 := cohomologyOverField k f (Stacks.Divisors.modulesInvertibleSheaf D) 0
  obtain ⟨n, hn⟩ : ∃ n, Module.finrank k H0 = n + 1 :=
    ⟨Module.finrank k H0 - 1, (Nat.sub_add_cancel (one_le_finrank_globalSections k f D)).symm⟩
  let b := Module.finBasisOfFinrankEq k H0 hn
  let w := globalSectionsBasis k f (Stacks.Divisors.modulesInvertibleSheaf D) b
  let bV := b.dualBasis
  let φ := projectiveSpaceOfModuleOverIso k bV
  refine ⟨fun T => ((Iso.homCongr (Iso.refl T) φ).trans
    (familyEquiv k f D w (topologicalKrullDim_le_one k f) hd T)), fun T T' h g => ?_,
    fun s hs => ?_⟩
  · simp only [Equiv.trans_apply, Iso.homCongr_apply, Iso.refl_inv, Category.id_comp,
      Category.assoc]
    exact familyEquiv_naturality k f D w _ hd h (g ≫ φ.hom)
  · obtain ⟨j, hj⟩ : ∃ j, b.repr s j ≠ 0 := by
      by_contra! hcon
      exact hs (b.repr.injective (by ext j; simp [hcon j]))
    let c : Fin (n + 1) → Γ(Spec (.of k), ⊤) := fun i => (Scheme.ΓSpecIso (.of k)).inv (b.repr s i)
    have hc : Ideal.span (Set.range c) = ⊤ := Ideal.eq_top_of_isUnit_mem _
      (Ideal.subset_span ⟨j, rfl⟩) ((Ne.isUnit hj).map (Scheme.ΓSpecIso (.of k)).inv.hom)
    have hcφ : ∀ i, c i = (Scheme.ΓSpecIso (.of k)).inv (Module.Dual.eval k H0 s (bV i)) :=
      fun i => by simp only [c, bV, Module.Dual.eval_apply, Module.Basis.dualBasis_apply]
    have hg : sectionPoint k f D hs ≫ φ.hom = coordHom k (T := fieldPoint k) c hc := by
      ext1
      show _ ≫ (projectiveSpaceOfModuleIsoProjMvPolynomial bV).hom = coordMor (𝟙 _) c hc
      show pointOfClosedPoint _ _ _ ≫ _ = _
      rw [← coordMor_comp_inv_eq_pointOfClosedPoint k bV (Module.Dual.eval k H0 s)
        (eval_ne_zero k f D hs) c hc hcφ, Category.assoc, Iso.inv_hom_id, Category.comp_id]
    simp only [Equiv.trans_apply, Iso.homCongr_apply, Iso.refl_inv, Category.id_comp]
    show (familyOf k f _ w (sectionPoint k f D hs ≫ φ.hom)).comap _ = _
    rw [hg, familyOf_coordHom]
    show (coordDivisor k f _ w (𝟙 _) c).comap _ = _
    rw [comap_coordDivisor_point]
    congr 1
    rw [sectionOf_eq_sum k f _ b s]
    exact Finset.sum_congr rfl fun i _ => by rw [globalSectionsBasis_apply]

/-- Let `X` be a smooth projective curve over an algebraically
closed field `k` and `D ⊆ X` an effective Cartier divisor of degree `d`. The fibre of the Abel map
`γ_d : Hilb^d_{X/k} → Pic^d_{X/k}` over the point corresponding to `𝒪_X(D)` is represented by
the scheme `𝐏(H⁰(X, 𝒪_X(D))^∨)` — a natural bijection between its `T`-points and the `k`-morphisms
`T ⟶ 𝐏(H⁰(X, 𝒪_X(D))^∨)` — and the closed points of that scheme are exactly the effective Cartier
divisors linearly equivalent to `D`, a closed point corresponding to the image in `X` of the
family over `Spec k` it classifies. -/
theorem completeLinearSystem_eq_closedPoints_abelFibre {d : ℕ}
    (hd : invertibleCurveDegree k f (topologicalKrullDim_le_one k f)
      (Stacks.Divisors.modulesInvertibleSheaf D) = d) :
    ∃ e : ∀ T : Over (Spec (.of k)),
        (T ⟶ (linearSystemScheme k f D).asOver (Spec (.of k))) ≃ abelFibre f D d T,
      (∀ (T T' : Over (Spec (.of k))) (h : T' ⟶ T)
          (g : T ⟶ (linearSystemScheme k f D).asOver (Spec (.of k))),
        (e T' (h ≫ g)).1.ideal = (e T g).1.ideal.comap (familyBaseChangeMap (curveOver f) h)) ∧
      ∃ c : closedPoints (linearSystemScheme k f D) ≃ Stacks.Divisors.completeLinearSystem D,
        (∀ x : closedPoints (linearSystemScheme k f D),
          (c x : X.IdealSheafData) =
            (e (fieldPoint k) (Over.homMk (@pointOfClosedPoint _ _ _ _
              (projectiveSpaceOfModuleToSpec k (dualSections k f D))
              (locallyOfFiniteType_linearSystemScheme k f D) x.1 x.2)
              (@pointOfClosedPoint_comp _ _ _ _ _
                (locallyOfFiniteType_linearSystemScheme k f D) x.1 x.2))).1.ideal.comap
              (inv (pullback.fst f (𝟙 (Spec (.of k)))))) ∧
        ∀ (s : cohomologyOverField k f (Stacks.Divisors.modulesInvertibleSheaf D) 0)
          (hs : s ≠ 0),
          (c ⟨ProjectiveSpaceOfModule.linearFunctionalPoint k _ (Module.Dual.eval k _ s)
              (eval_ne_zero k f D hs),
            ProjectiveSpaceOfModule.linearFunctionalPoint_isClosed k _ _
              (eval_ne_zero k f D hs)⟩ : X.IdealSheafData) =
            zeroScheme X (Stacks.Divisors.modulesInvertibleSheaf D)
              (sectionOf k f (Stacks.Divisors.modulesInvertibleSheaf D) s) := by
  obtain ⟨e, he, hpin⟩ := exists_abelFibre_equiv_projectiveSpace_canonical k f D hd
  refine ⟨e, he, ?_⟩
  let sec : {p : Spec (.of k) ⟶ linearSystemScheme k f D //
      p ≫ projectiveSpaceOfModuleToSpec k (dualSections k f D) = 𝟙 _} ≃
      (fieldPoint k ⟶ (linearSystemScheme k f D).asOver (Spec (.of k))) :=
    { toFun := fun p => Over.homMk p.1 (by
        show p.1 ≫ linearSystemScheme k f D ↘ Spec (.of k) = 𝟙 _
        rw [over_linearSystemScheme]
        exact p.2)
      invFun := fun g => ⟨g.left, Over.w g⟩
      left_inv := fun p => rfl
      right_inv := fun g => by ext; rfl }
  refine ⟨(pointEquivClosedPoint (projectiveSpaceOfModuleToSpec k (dualSections k f D))).symm.trans
    (sec.trans ((e (fieldPoint k)).trans (abelFibreSpecEquiv k f D hd))), fun x => rfl,
    fun s hs => hpin s hs⟩

/-- Let `X` be a smooth projective curve over an algebraically closed field `k`, `D ⊆ X` an
effective Cartier divisor of degree `d`, and `m` the integer with `m + 1 = h⁰(𝒪_X(D))`. The scheme
`|D| = 𝐏(H⁰(X, 𝒪_X(D))^∨)` representing the fibre of the Abel map over the point of `𝒪_X(D)` is
isomorphic over `k` to `ℙ^m_k`; equivalently, that fibre is represented by `ℙ^m_k` — a natural
bijection between its `T`-points and the `k`-morphisms `T ⟶ ℙ^m_k`. Canonically, the fibre is
represented by `𝐏(H⁰(X, 𝒪_X(D))^∨)` itself, through the bijection sending the closed point cut out
by evaluation at a nonzero `s ∈ H⁰(X, 𝒪_X(D))` to the family whose image in `X` is the zero scheme
`Z(s)`. -/
@[stacks 0CCT "|D| is isomorphic to P^m_k with m + 1 = h^0(O_X(D)); canonically \
|D| = P(H^0(X, O_X(D))^dual)"]
theorem completeLinearSystem_iso_projectiveSpace {d m : ℕ}
    (hd : invertibleCurveDegree k f (topologicalKrullDim_le_one k f)
      (Stacks.Divisors.modulesInvertibleSheaf D) = d)
    (hm : Module.finrank k
      (cohomologyOverField k f (Stacks.Divisors.modulesInvertibleSheaf D) 0) = m + 1) :
    Nonempty ((linearSystemScheme k f D).asOver (Spec (.of k)) ≅
      (projectiveSpaceOverRing m (.of k)).asOver (Spec (.of k))) ∧
    (∃ e : ∀ T : Over (Spec (.of k)),
        (T ⟶ (projectiveSpaceOverRing m (.of k)).asOver (Spec (.of k))) ≃ abelFibre f D d T,
      ∀ (T T' : Over (Spec (.of k))) (h : T' ⟶ T)
          (g : T ⟶ (projectiveSpaceOverRing m (.of k)).asOver (Spec (.of k))),
        (e T' (h ≫ g)).1.ideal = (e T g).1.ideal.comap (familyBaseChangeMap (curveOver f) h)) ∧
    ∃ e : ∀ T : Over (Spec (.of k)),
        (T ⟶ (linearSystemScheme k f D).asOver (Spec (.of k))) ≃ abelFibre f D d T,
      (∀ (T T' : Over (Spec (.of k))) (h : T' ⟶ T)
          (g : T ⟶ (linearSystemScheme k f D).asOver (Spec (.of k))),
        (e T' (h ≫ g)).1.ideal = (e T g).1.ideal.comap (familyBaseChangeMap (curveOver f) h)) ∧
      ∀ (s : cohomologyOverField k f (Stacks.Divisors.modulesInvertibleSheaf D) 0) (hs : s ≠ 0),
        (e (fieldPoint k) (sectionPoint k f D hs)).1.ideal.comap
            (inv (pullback.fst f (𝟙 (Spec (.of k))))) =
          zeroScheme X (Stacks.Divisors.modulesInvertibleSheaf D)
            (sectionOf k f (Stacks.Divisors.modulesInvertibleSheaf D) s) := by
  have hV : Module.finrank k (dualSections k f D) = m + 1 := by
    rw [Subspace.dual_finrank_eq, hm]
  let φ := basisProjectiveSpaceOfModuleIso (Module.finBasisOfFinrankEq k _ hV)
  obtain ⟨e, he, hpin⟩ := exists_abelFibre_equiv_projectiveSpace_canonical k f D hd
  refine ⟨⟨φ⟩, ⟨fun T => (Iso.homCongr (Iso.refl T) φ.symm).trans (e T), fun T T' h g => ?_⟩,
    e, he, hpin⟩
  simp only [Equiv.trans_apply, Iso.homCongr_apply, Iso.refl_inv, Category.id_comp,
    Iso.symm_hom, Category.assoc]
  exact he T T' h (g ≫ φ.inv)

end Stacks.LinearSystemScheme

end
