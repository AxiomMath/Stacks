module

public import StacksFrontier.AlgebraicGeometry.Curves.LinearSystemScheme.UniversalFamily
public import StacksFrontier.AlgebraicGeometry.Curves.LinearSystemScheme.RegularSectionUnit
public import StacksFrontier.AlgebraicGeometry.Picard.TorsionSmoothProjectiveCurve.PicardFunctorPoints

/-!
# A morphism into `Proj k[T₀, …, Tₙ]` is determined by its family

For a smooth projective curve `X` over an algebraically closed field `k`, an invertible `L` and a
basis `w` of `Γ(X, L)`, two `k`-morphisms `g, g' : T ⟶ Q` with the same pullback of the universal
divisor are equal. Locally on `T` both are `[c₀ : … : cₙ]` and `[c'₀ : … : c'ₙ]` with
`Z(Σ cᵢ wᵢ) = Z(Σ c'ᵢ wᵢ)`; the two coordinate sections then differ by a unit of
`Γ(X_V, 𝒪) = Γ(V, 𝒪)`, and so do the coordinates.

## Main results

* `Stacks.LinearSystemScheme.isIso_appTop_pullback_snd`: `Γ(V, 𝒪) = Γ(X_V, 𝒪)`.
* `Stacks.LinearSystemScheme.eq_of_familyOf_eq`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite HomogeneousLocalization
open AlgebraicGeometry.Proj Stacks.AlgebraicGeometry.SectionsBaseChange Stacks.Hilbert

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

namespace Stacks.LinearSystemScheme

variable (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
  [IsAlgClosed k] [IsCurve k f] [IsProjectiveVariety k f] [Smooth f]

/-- **The only global functions on `X ×_k T` are those of `T`.** -/
theorem isIso_appTop_pullback_snd {T : Scheme.{u}} (g : T ⟶ Spec (.of k)) :
    IsIso (pullback.snd f g).appTop := by
  have : CompactSpace X := compactSpace_of_curve k f
  have : Nonempty X := inferInstance
  obtain ⟨σ, hσ⟩ := Stacks.PicardFunctor.exists_section_of_isAlgClosed k f
  have := isIso_c_baseChange_of_isCurve_of_section f σ hσ g
  exact (inferInstance : IsIso ((pullback.snd f g).toLRSHom.toHom.c.app (op ⊤)))

variable (L : X.Modules) [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
  {n : ℕ} (w : letI := baseModule f L ⊤; Module.Basis (Fin (n + 1)) Γ(Spec (.of k), ⊤) Γ(L, ⊤))

/-- **Over an affine base, unimodular coordinates with the same divisor define the same point.** -/
theorem coordMor_eq_of_coordDivisor_eq {V : Scheme.{u}} [IsAffine V] (h : V ⟶ Spec (.of k))
    (c c' : Fin (n + 1) → Γ(V, ⊤)) (hc : Ideal.span (Set.range c) = ⊤)
    (hc' : Ideal.span (Set.range c') = ⊤)
    (hZ : coordDivisor k f L w h c = coordDivisor k f L w h c') :
    coordMor h c hc = coordMor h c' hc' := by
  have := isQuasicoherent_of_curve k f L
  have := compactSpace_of_curve k f
  have := quasiSeparatedSpace_of_curve k f
  obtain ⟨u, hu, hs⟩ := exists_isUnit_smul_eq_of_zeroScheme_eq _ hZ
    (isEffectiveCartierDivisor_coordDivisor k f L w h c hc)
  have := isIso_appTop_pullback_snd k f h
  have hbij := ConcreteCategory.bijective_of_isIso (pullback.snd f h).appTop
  obtain ⟨a, rfl⟩ := hbij.2 u
  have ha : IsUnit a := by
    obtain ⟨b, hb⟩ := hbij.2 (↑hu.unit⁻¹ : Γ(pullback f h, ⊤))
    refine IsUnit.of_mul_eq_one b (hbij.1 ?_)
    rw [map_mul, map_one, hb]
    exact hu.mul_val_inv
  obtain rfl : c' = a • c :=
    (coordSection_bijective (IsPullback.of_hasPullback f h) L w).1 (by rwa [coordSection_smul])
  exact (coordMor_unit_mul h c hc ha.unit hc').symm

omit [IsAlgClosed k] in
/-- A `k`-morphism into `Q` from an open subscheme, landing in `D₊(Tᵢ)`, is `[c₀ : … : cₙ]` for its
chart coordinates. -/
theorem left_eq_coordMor {T : Over (Spec (.of k))} (g : T ⟶ projOver k (n := n)) (i : Fin (n + 1))
    (hg : g.left ⁻¹ᵁ basicOpen (coordGrading k n) (MvPolynomial.X i) = ⊤) :
    g.left = coordMor T.hom (chartCoords g.left i hg) (span_range_chartCoords _ _ _) :=
  eq_coordMor_chartCoords T.hom g.left (Over.w g) i hg

/-- **Injectivity on affine bases.** -/
theorem eq_of_familyOf_eq_of_isAffine {T : Over (Spec (.of k))} [IsAffine T.left]
    (g g' : T ⟶ projOver k (n := n)) (i l : Fin (n + 1))
    (hg : g.left ⁻¹ᵁ basicOpen (coordGrading k n) (MvPolynomial.X i) = ⊤)
    (hg' : g'.left ⁻¹ᵁ basicOpen (coordGrading k n) (MvPolynomial.X l) = ⊤)
    (h : familyOf k f L w g = familyOf k f L w g') : g.left = g'.left := by
  rw [left_eq_coordMor k g i hg, left_eq_coordMor k g' l hg']
  refine coordMor_eq_of_coordDivisor_eq k f L w T.hom _ _ _ _ ?_
  rw [← familyOf_of_chart k f L w g i hg, ← familyOf_of_chart k f L w g' l hg', h]

/-- **A morphism into `Q` is determined by its pullback of the universal divisor.** -/
theorem eq_of_familyOf_eq {T : Over (Spec (.of k))} (g g' : T ⟶ projOver k (n := n))
    (h : familyOf k f L w g = familyOf k f L w g') : g = g' := by
  have hloc : ∀ t : T.left, ∃ (V : T.left.Opens) (i l : Fin (n + 1)), IsAffineOpen V ∧ t ∈ V ∧
      V ≤ g.left ⁻¹ᵁ basicOpen (coordGrading k n) (MvPolynomial.X i) ∧
      V ≤ g'.left ⁻¹ᵁ basicOpen (coordGrading k n) (MvPolynomial.X l) := by
    intro t
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp
      ((iSup_preimage_basicOpen_X k g.left).ge (Set.mem_univ t))
    obtain ⟨l, hl⟩ := TopologicalSpace.Opens.mem_iSup.mp
      ((iSup_preimage_basicOpen_X k g'.left).ge (Set.mem_univ t))
    set W : T.left.Opens := g.left ⁻¹ᵁ basicOpen (coordGrading k n) (MvPolynomial.X i) ⊓
        g'.left ⁻¹ᵁ basicOpen (coordGrading k n) (MvPolynomial.X l)
    have htW : t ∈ (W : Set T.left) := ⟨hi, hl⟩
    obtain ⟨_, ⟨V, hV, rfl⟩, htV, hVle⟩ :=
      T.left.isBasis_affineOpens.exists_subset_of_mem_open htW W.isOpen
    exact ⟨V, i, l, hV, htV, fun x hx => (hVle hx).1, fun x hx => (hVle hx).2⟩
  choose V i l hV htV hVi hVl using hloc
  ext1
  refine (T.left.openCoverOfIsOpenCover V (eq_top_iff.mpr fun t _ =>
    TopologicalSpace.Opens.mem_iSup.mpr ⟨t, htV t⟩)).hom_ext _ _ fun t => ?_
  have : IsAffine (restrictOver (k := k) (T := T) (V t).ι).left := hV t
  have hpre : ∀ (W : T.left.Opens), V t ≤ W → (V t).ι ⁻¹ᵁ W = ⊤ := fun W hW =>
    eq_top_iff.mpr fun x _ => hW x.2
  exact eq_of_familyOf_eq_of_isAffine k f L w (T := restrictOver (V t).ι)
    (restrictHom (V t).ι ≫ g) (restrictHom (V t).ι ≫ g') (i t) (l t)
    (by rw [Over.comp_left, Scheme.Hom.comp_preimage]; exact hpre _ (hVi t))
    (by rw [Over.comp_left, Scheme.Hom.comp_preimage]; exact hpre _ (hVl t))
    (by rw [familyOf_comp, familyOf_comp, h])

end Stacks.LinearSystemScheme

end
